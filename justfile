set shell := ["bash", "-euo", "pipefail", "-c"]

manifests := "Cargo.toml oracle/Cargo.toml integrations/Cargo.toml bench/Cargo.toml fuzz/Cargo.toml tools/gen-tables/Cargo.toml"
test_features := "std,float-convert,serde,bytemuck,num-traits"
release_features := "std,float-convert"
optional_features := "serde bytemuck num-traits"
msrv := "1.60"
min_coverage := "80"

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

[doc("clippy of the root crate, then clippy -D warnings with all features on every manifest")]
[group("lint")]
clippy-all: clippy
    for m in {{ manifests }}; do cargo clippy --manifest-path "$m" --all-targets --all-features -- -D warnings; done

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

[doc("Operators panic instead of saturating")]
[group("test")]
test-strict:
    cargo test --features strict-overflow --test strict

[doc("Tests of the optional features through their public traits")]
[group("test")]
test-integrations:
    cargo test --manifest-path integrations/Cargo.toml --all-features

[doc("Exact rational oracle")]
[group("test")]
oracle:
    cargo test --manifest-path oracle/Cargo.toml --release

[doc("Build on the minimum supported Rust with each optional feature")]
[group("test")]
msrv:
    cargo +{{ msrv }} build
    for f in {{ optional_features }}; do cargo +{{ msrv }} build --features "$f"; done
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

[doc("Line coverage of the root tests with the CI floor")]
[group("test")]
cov min=min_coverage:
    cargo llvm-cov --features {{ test_features }} --summary-only --fail-under-lines {{ min }}

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

[doc("Speed against fixed, libm and std floats on one pinned core")]
[group("perf")]
bench *args:
    bench/run.sh {{ args }}
