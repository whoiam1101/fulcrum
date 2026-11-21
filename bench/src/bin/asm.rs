//! Checks the assembly of `src/loops.rs` for one instruction set: which loops
//! vectorize, that the scalar `mul` and `div` call no software routine
//! (except the `u128` division of `FixedFloat64`), and that `saturating_add`
//! has no branch.
//!
//! Usage: `asm sse2|avx2|neon`. It builds the library of this crate with
//! `--emit asm` for x86-64 (the SSE2 baseline, or `x86-64-v3` with AVX2) or
//! for aarch64 (NEON) into `target/asm/<isa>`, in the release profile with one
//! codegen unit like the `bench` profile (whose fat LTO acts only at link
//! time), then compares every loop with [`VECTORIZED`] in both directions: a
//! loop that stops vectorizing fails, and so does one that starts, which is
//! the signal to update the table and the "Arrays" section of the API guides
//! that repeats it. Exits with status 1 on any difference.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

/// The loops of `src/loops.rs` and the instruction sets they vectorize on.
const VECTORIZED: [(&str, &[&str]); 18] = [
    ("add_8", &["sse2", "avx2", "neon"]),
    ("sub_8", &["sse2", "avx2", "neon"]),
    ("mul_8", &["sse2", "avx2", "neon"]),
    ("mul_int_8", &["sse2", "avx2", "neon"]),
    ("mul_add_8", &["sse2", "avx2", "neon"]),
    ("lerp_8", &["sse2", "avx2", "neon"]),
    ("add_16", &["sse2", "avx2", "neon"]),
    ("sub_16", &["sse2", "avx2", "neon"]),
    ("mul_16", &["sse2", "avx2", "neon"]),
    ("mul_int_16", &["sse2", "avx2", "neon"]),
    ("mul_add_16", &["sse2", "avx2", "neon"]),
    ("lerp_16", &["sse2", "avx2", "neon"]),
    ("add_32", &["sse2", "avx2", "neon"]),
    ("sub_32", &["sse2", "avx2", "neon"]),
    ("mul_32", &["avx2", "neon"]),
    ("mul_int_32", &["avx2"]),
    ("mul_add_32", &["avx2", "neon"]),
    ("lerp_32", &["avx2", "neon"]),
];

/// The software routines of 128-bit multiplication and division on the
/// 64-bit targets checked here.
const LIBCALLS: [&str; 5] = ["__multi3", "__divti3", "__udivti3", "__modti3", "__umodti3"];

/// Target triple and `RUSTFLAGS` of an instruction set.
fn target(isa: &str) -> Option<(&'static str, &'static str)> {
    match isa {
        "sse2" => Some(("x86_64-unknown-linux-gnu", "")),
        "avx2" => Some(("x86_64-unknown-linux-gnu", "-C target-cpu=x86-64-v3")),
        "neon" => Some(("aarch64-unknown-linux-gnu", "")),
        _ => None,
    }
}

/// Builds the library with `--emit asm` and returns the path of its `.s`
/// file. The library is cleaned first: cargo emits the assembly only when it
/// compiles the crate, not when the crate is fresh.
fn build(isa: &str, triple: &str, flags: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/asm")
        .join(isa);
    let cargo = env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let status = Command::new(&cargo)
        .args([
            "clean",
            "-q",
            "-p",
            "fulcrum-bench",
            "--release",
            "--target",
            triple,
        ])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .env("CARGO_TARGET_DIR", &dir)
        .status()
        .expect("cargo runs");
    assert!(status.success(), "cargo clean failed");
    let status = Command::new(&cargo)
        .args(["rustc", "-q", "--release", "--lib", "--target", triple])
        .args(["--", "--emit", "asm"])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .env("CARGO_TARGET_DIR", &dir)
        .env("RUSTFLAGS", flags)
        .env("CARGO_PROFILE_RELEASE_CODEGEN_UNITS", "1")
        .status()
        .expect("cargo runs");
    assert!(status.success(), "cargo rustc --emit asm failed");
    newest_asm(&dir).expect("the .s file of fulcrum_bench")
}

/// The newest `fulcrum_bench*.s` under `dir`, searched recursively: where
/// cargo puts it inside the target directory depends on its version.
fn newest_asm(dir: &Path) -> Option<PathBuf> {
    let mut best: Option<(std::time::SystemTime, PathBuf)> = None;
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in fs::read_dir(&d).into_iter().flatten().flatten() {
            let path = entry.path();
            let Ok(meta) = entry.metadata() else { continue };
            if meta.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|x| x == "s")
                && path
                    .file_name()
                    .is_some_and(|n| n.to_string_lossy().starts_with("fulcrum_bench"))
            {
                let Ok(time) = meta.modified() else { continue };
                if best.as_ref().is_none_or(|(t, _)| time > *t) {
                    best = Some((time, path));
                }
            }
        }
    }
    best.map(|(_, p)| p)
}

/// The name of a function of `loops` in a mangled symbol: the identifier
/// after the module `5loops`, prefixed with its length.
fn loop_name(symbol: &str) -> Option<String> {
    let rest = &symbol[symbol.find("5loops")? + 6..];
    let digits = rest.chars().take_while(char::is_ascii_digit).count();
    let len: usize = rest[..digits].parse().ok()?;
    rest.get(digits..digits + len).map(str::to_owned)
}

/// The instructions of every function of `loops`, by name.
fn functions(asm: &str) -> Vec<(String, Vec<String>)> {
    let mut out: Vec<(String, Vec<String>)> = Vec::new();
    let mut open = false;
    for line in asm.lines() {
        let t = line.trim();
        if let Some(symbol) = line
            .strip_suffix(':')
            .filter(|_| !line.starts_with(['.', ' ', '\t']))
        {
            open = false;
            if let Some(name) = loop_name(symbol) {
                out.push((name, Vec::new()));
                open = true;
            }
        } else if t.starts_with(".Lfunc_end") || t == ".cfi_endproc" {
            open = false;
        } else if open && !t.is_empty() && !t.starts_with('.') && !t.ends_with(':') {
            if let Some((_, body)) = out.last_mut() {
                body.push(t.to_owned());
            }
        }
    }
    out
}

/// Whether `s` names a NEON vector register with an arrangement, `v0.4s`.
fn neon_vector(s: &str) -> bool {
    s.split(|c: char| !(c.is_ascii_alphanumeric() || c == '.'))
        .any(|w| {
            let Some(rest) = w.strip_prefix('v') else {
                return false;
            };
            let Some((reg, arr)) = rest.split_once('.') else {
                return false;
            };
            !reg.is_empty()
                && reg.chars().all(|c| c.is_ascii_digit())
                && arr.len() >= 2
                && arr[..arr.len() - 1].chars().all(|c| c.is_ascii_digit())
                && arr.ends_with(['b', 'h', 's', 'd'])
        })
}

/// Whether an instruction is packed integer arithmetic on the vector
/// registers of `isa`: `p…` on `%xmm` for SSE2, `vp…` on `%ymm` for AVX2, any
/// instruction on an arranged register (`v0.4s`) for NEON. Moves of scalars
/// through `%xmm` do not count.
fn vector(isa: &str, ins: &str) -> bool {
    let op = ins.split_whitespace().next().unwrap_or("");
    match isa {
        "sse2" => op.starts_with('p') && ins.contains("%xmm"),
        "avx2" => op.starts_with("vp") && ins.contains("%ymm"),
        _ => neon_vector(ins),
    }
}

/// Whether an instruction is a branch: `j…` on x86-64, `b`, `b.…`, `cbz`,
/// `cbnz`, `tbz`, `tbnz` on aarch64.
fn branch(isa: &str, ins: &str) -> bool {
    let op = ins.split_whitespace().next().unwrap_or("");
    if isa == "neon" {
        op == "b" || op.starts_with("b.") || matches!(op, "cbz" | "cbnz" | "tbz" | "tbnz")
    } else {
        op.starts_with('j')
    }
}

/// The software routine of [`LIBCALLS`] an instruction names, if any.
fn libcall(ins: &str) -> Option<&'static str> {
    LIBCALLS.into_iter().find(|c| {
        ins.split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
            .any(|w| w == *c)
    })
}

fn main() {
    let isa = env::args().nth(1).unwrap_or_default();
    let Some((triple, flags)) = target(&isa) else {
        eprintln!("usage: asm sse2|avx2|neon");
        std::process::exit(2);
    };
    let path = build(&isa, triple, flags);
    let asm = fs::read_to_string(&path).expect("readable assembly");
    let funcs = functions(&asm);
    let scalars: Vec<(String, u32, &str)> = [8, 16, 32, 64]
        .into_iter()
        .flat_map(|w| {
            ["mul", "div", "saturating_add"].map(|op| (format!("scalar_{}_{}", op, w), w, op))
        })
        .collect();
    let missing: Vec<&str> = VECTORIZED
        .iter()
        .map(|(n, _)| *n)
        .chain(scalars.iter().map(|(n, _, _)| n.as_str()))
        .filter(|n| !funcs.iter().any(|(f, _)| f == n))
        .collect();
    if !missing.is_empty() {
        eprintln!("FAIL not in the assembly: {:?}", missing);
        std::process::exit(1);
    }
    let body = |name: &str| {
        &funcs
            .iter()
            .find(|(n, _)| n == name)
            .expect("checked above")
            .1
    };
    let mut failures = Vec::new();

    for (name, isas) in VECTORIZED {
        let expected = isas.contains(&isa.as_str());
        let actual = body(name).iter().any(|i| vector(&isa, i));
        let verdict = if actual { "vectorized" } else { "scalar" };
        println!("{:<26} {}", name, verdict);
        if expected != actual {
            failures.push(format!(
                "{}: {} on {}, the table says {}",
                name,
                verdict,
                isa,
                if expected { "vectorized" } else { "scalar" }
            ));
        }
    }

    for (name, width, op) in &scalars {
        let b = body(name);
        if *op == "saturating_add" {
            let branches = b.iter().filter(|i| branch(&isa, i)).count();
            println!("{:<26} branches {}", name, branches);
            if branches != 0 {
                failures.push(format!("{}: {} branches", name, branches));
            }
        } else {
            let calls: Vec<&str> = b.iter().filter_map(|i| libcall(i)).collect();
            let allowed = *op == "div" && *width == 64 && calls.iter().all(|c| *c == "__udivti3");
            println!("{:<26} libcalls {:?}", name, calls);
            if !calls.is_empty() && !allowed {
                failures.push(format!("{}: calls {:?}", name, calls));
            }
        }
    }

    if failures.is_empty() {
        println!("{}: as expected ({})", isa, path.display());
    } else {
        for f in &failures {
            eprintln!("FAIL {}", f);
        }
        std::process::exit(1);
    }
}
