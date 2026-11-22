set shell := ["bash", "-euo", "pipefail", "-c"]

sub_manifests := "oracle/Cargo.toml integrations/Cargo.toml bench/Cargo.toml fuzz/Cargo.toml tools/gen-tables/Cargo.toml"
manifests := "Cargo.toml " + sub_manifests
test_features := "std,float-convert,serde,bytemuck,num-traits"
release_features := "std,float-convert"
msrv := `sed -n 's/^rust-version = "\(.*\)"$/\1/p' Cargo.toml`
min_coverage := "92"

[doc("List the recipes")]
default:
    @just --list --unsorted

[doc("Fast checks of every commit: formatting, root clippy, source rules, generated tables, spelling")]
[group("gates")]
check: fmt-check clippy rules tables typos

[doc("The local gate before a push, minutes: lint, tests, integrations, oracle, MSRV, feature combinations, cargo deny; not miri, coverage, i686, fuzzing, Kani, Lean")]
[group("gates")]
all: lint rules test test-release test-strict test-integrations oracle msrv hack deny

[doc("What the CI lint job runs: rustfmt and clippy on every manifest, rustdoc, spelling, generated tables")]
[group("lint")]
lint: fmt-check clippy-all doc typos tables

[doc("rustfmt --check on every manifest")]
[group("lint")]
fmt-check:
    for m in {{ manifests }}; do cargo fmt --check --manifest-path "$m"; done

[doc("rustfmt on every manifest")]
[group("lint")]
fmt:
    for m in {{ manifests }}; do cargo fmt --manifest-path "$m"; done

[doc("clippy -D warnings on the root crate: default features, every feature but strict-overflow (the tests it turns off), then all")]
[group("lint")]
clippy:
    cargo clippy --all-targets -- -D warnings
    cargo clippy --all-targets --features {{ test_features }} -- -D warnings
    cargo clippy --all-targets --all-features -- -D warnings

[doc("clippy of the root crate, then clippy -D warnings with all features on every other manifest")]
[group("lint")]
clippy-all: clippy
    for m in {{ sub_manifests }}; do cargo clippy --manifest-path "$m" --all-targets --all-features -- -D warnings; done

[doc("rustdoc with warnings as errors")]
[group("lint")]
doc:
    RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features

[doc("Spelling of code and docs")]
[group("lint")]
typos:
    typos

[doc("Project rules of tests/source_rules.rs: doc comments only, no platform code, unsafe only in src/pod.rs")]
[group("lint")]
rules:
    cargo test -q --test source_rules

[doc("Generated tables match tools/gen-tables")]
[group("lint")]
tables:
    cargo run -q --manifest-path tools/gen-tables/Cargo.toml -- --check

[doc("Tests of the root crate with every feature but strict-overflow")]
[group("test")]
test:
    cargo test --features {{ test_features }}

[doc("Tests in release, where the arithmetic is optimized")]
[group("test")]
test-release:
    cargo test --features {{ release_features }} --release

[doc("Doc tests of the root crate with every feature but strict-overflow")]
[group("test")]
doctest:
    cargo test --doc --features {{ test_features }}

[doc("Operators panic instead of saturating")]
[group("test")]
test-strict:
    cargo test --features strict-overflow --test strict

[doc("Tests of the optional features through their public traits, every feature combination")]
[group("test")]
test-integrations:
    cargo hack test --manifest-path integrations/Cargo.toml --feature-powerset

[doc("Exact rational oracle")]
[group("test")]
oracle:
    cargo test --manifest-path oracle/Cargo.toml --release

[doc("Build on the minimum supported Rust (rust-version of Cargo.toml) without features and with all; src has only positive cfg(feature) branches, so the two builds reach each of them")]
[group("test")]
msrv:
    cargo +{{ msrv }} build
    cargo +{{ msrv }} build --all-features

[doc("Check every feature combination, clippy every single feature")]
[group("test")]
hack:
    cargo hack check --feature-powerset --no-dev-deps
    cargo hack clippy --each-feature --all-targets -- -D warnings

[doc("Miri with strict provenance on the unsafe code of src/pod.rs")]
[group("test")]
miri toolchain="nightly":
    cd integrations && MIRIFLAGS=-Zmiri-strict-provenance cargo +{{ toolchain }} miri test --features bytemuck --test bytemuck

[doc("Line coverage of src by the root tests and the tests of integrations/ together, with the CI floor; cargo llvm-cov reports only the binaries of one workspace, so llvm-cov of llvm-tools merges them; the test binaries are found anywhere under the target directory, cargo versions place them differently")]
[group("test")]
cov min=min_coverage:
    cargo llvm-cov clean --workspace
    cargo llvm-cov --no-report --features {{ test_features }}
    CARGO_LLVM_COV_TARGET_DIR="$PWD/target/llvm-cov-target" cargo llvm-cov --no-report --manifest-path integrations/Cargo.toml --all-features --dep-coverage fulcrum
    tools="$(rustc --print sysroot)/lib/rustlib/$(rustc -vV | sed -n 's/^host: //p')/bin" && d=target/llvm-cov-target \
      && "$tools/llvm-profdata" merge -sparse "$d"/*.profraw -o "$d/merged.profdata" \
      && "$tools/llvm-cov" report -instr-profile="$d/merged.profdata" $(find "$d" -type f -perm -u+x -regextype posix-extended -regex '.*/[a-z0-9_]+-[0-9a-f]{16}' ! -name 'build_script_*' | sed 's/^/-object=/') \
        -ignore-filename-regex='/\.cargo/|/\.rustup/|/rustc/|/tests/|/integrations/|/target/' | tee "$d/report.txt" \
      && awk -v min={{ min }} '$1 == "TOTAL" { found = 1; if ($10 + 0 < min) { print "line coverage " $10 " is below " min "%"; exit 1 } } END { if (!found) exit 1 }' "$d/report.txt"

[doc("Mutation testing, hours; extra arguments go to cargo mutants, e.g. --jobs 4 --shard 0/8. The Kani harnesses (`src/proofs`, only under `cfg(kani)`) are not mutated. A build over 2 minutes (a mutant that loops in the const evaluation of `ff!`) is a timeout. A mutant that times out counts as caught: only exit code 3 (timeouts, nothing missed) passes")]
[group("test")]
mutants *args:
    cargo mutants --no-shuffle --timeout-multiplier 3 --build-timeout 120 --exclude src/proofs/mod.rs --exclude src/proofs/geometry.rs --features {{ test_features }} {{ args }} || test $? -eq 3

[doc("cargo deny: advisories, bans, licenses, sources of every manifest")]
[group("security")]
deny:
    for m in {{ manifests }}; do cargo deny --manifest-path "$m" --all-features check advisories bans licenses sources; done

[doc("Instruction counts under Callgrind; needs Valgrind and gungraun-runner of the same version as gungraun")]
[group("perf")]
perf *args:
    cd bench && cargo bench --bench instr -- {{ args }}

[doc("Vectorization of the loops of bench/src/loops.rs against the table of bench/src/bin/asm.rs, no software routine in the scalar mul and div, no branch in saturating_add; isa is sse2, avx2 or neon (neon needs the aarch64-unknown-linux-gnu target)")]
[group("perf")]
asm isa:
    cd bench && cargo run -q --release --bin asm -- {{ isa }}

[doc("Speed against fixed, libm and std floats, then the README section of bench/src/bin/report.rs on stdout; extra arguments go to criterion")]
[group("perf")]
bench *args:
    cd bench && cargo bench --bench ops -- {{ args }} && cargo run -q --release --bin report

[doc("Lean proofs of verify/lean with the prebuilt Mathlib, then leanchecker replays every module through the kernel, one at a time: given several at once it crashes")]
[group("verify")]
lean:
    cd verify/lean && lake exe cache get && lake build
    cd verify/lean && for f in $(find Fulcrum -name '*.lean'); do m="${f%.lean}"; lake env leanchecker "${m//\//.}"; done

[doc("Sources of Aeneas at the commit of verify/lean/lake-manifest.json and of Charon at its charon-pin, in target/aeneas")]
[group("verify")]
aeneas-src:
    rm -rf target/aeneas && mkdir -p target/aeneas
    git clone -q https://github.com/AeneasVerif/aeneas target/aeneas/aeneas
    git -C target/aeneas/aeneas checkout -q "$(jq -r '.packages[] | select(.name == "aeneas") | .rev' verify/lean/lake-manifest.json)"
    git clone -q https://github.com/AeneasVerif/charon target/aeneas/charon
    git -C target/aeneas/charon checkout -q "$(tail -1 target/aeneas/aeneas/charon-pin)"
    git -C target/aeneas/charon submodule update -q --init --recursive
    ln -s ../charon target/aeneas/aeneas/charon

[doc("Build Charon and Aeneas of aeneas-src; needs rustup and the opam packages of target/aeneas/aeneas/src/aeneas.opam and target/aeneas/charon/charon.opam")]
[group("verify")]
aeneas:
    cd target/aeneas/charon/charon && cargo build -q --release
    mkdir -p target/aeneas/charon/bin target/aeneas/aeneas/bin
    cp target/aeneas/charon/charon/target/release/charon target/aeneas/charon/charon/target/release/charon-driver target/aeneas/charon/bin/
    cd target/aeneas/aeneas/src && dune build
    cp target/aeneas/aeneas/src/_build/default/main.exe target/aeneas/aeneas/bin/aeneas

[doc("Extract src/kernel.rs to verify/lean/Fulcrum/Kernel with the Charon and Aeneas of `just aeneas`; the generated headers lose their regular comments, FunsExternal.lean is written by hand")]
[group("verify")]
extract:
    target/aeneas/charon/bin/charon cargo --preset=aeneas --start-from crate::kernel --dest-file target/extract/kernel.llbc
    rm -rf target/extract/lean
    target/aeneas/aeneas/bin/aeneas -backend lean -split-files -no-progress-bar -namespace fulcrum -subdir Fulcrum/Kernel -dest target/extract/lean target/extract/kernel.llbc
    for f in Types Funs; do grep -v '^-- \|^/- ' "target/extract/lean/Fulcrum/Kernel/$f.lean" > "verify/lean/Fulcrum/Kernel/$f.lean"; done
