//! Turns criterion results into the `## Benchmarks` section of the README.
//!
//! Usage: `report [--criterion DIR] [--readme FILE] [--out FILE]`.
//! Without `--readme` and `--out` the section is printed to stdout.
//!
//! A difference counts only when the 95% confidence intervals of the two
//! medians do not overlap and the medians differ by at least 5%; otherwise the
//! pair is reported as on par.

use serde_json::Value;
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

const HEADING: &str = "## Benchmarks";
const MIN_EFFECT: f64 = 1.05;

const CASES: [(&str, &str, &str); 5] = [
    ("throughput", "add", "`+`, throughput"),
    ("throughput", "mul", "`*`, throughput"),
    ("latency", "mul", "`*`, latency"),
    ("throughput", "div", "`/`, throughput"),
    ("latency", "div", "`/`, latency"),
];

const PAIRS: [(&str, &str); 3] = [
    ("FixedFloat16", "I8F8"),
    ("FixedFloat32", "I16F16"),
    ("FixedFloat64", "I32F32"),
];

const NATIVE: [(&str, &str); 2] = [("FixedFloat32", "f32"), ("FixedFloat64", "f64")];

/// Median time per operation and its 95% confidence interval, in ns.
#[derive(Clone, Copy)]
struct Est {
    ns: f64,
    lo: f64,
    hi: f64,
}

/// Outcome of comparing fulcrum against another implementation.
#[derive(Clone, Copy, PartialEq)]
enum Verdict {
    Faster(f64),
    Slower(f64),
    Even,
}

fn compare(ours: Est, theirs: Est) -> Verdict {
    let ratio = theirs.ns / ours.ns;
    let separated = ours.hi < theirs.lo || theirs.hi < ours.lo;
    if !separated || (ratio < MIN_EFFECT && ratio > 1.0 / MIN_EFFECT) {
        Verdict::Even
    } else if ratio > 1.0 {
        Verdict::Faster(ratio)
    } else {
        Verdict::Slower(1.0 / ratio)
    }
}

fn verdict_text(v: Verdict) -> String {
    match v {
        Verdict::Faster(r) => format!("{:.2}× faster", r),
        Verdict::Slower(r) => format!("{:.2}× slower", r),
        Verdict::Even => "on par".to_string(),
    }
}

fn load(dir: &Path, out: &mut BTreeMap<String, Est>) {
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if !path.is_dir() {
            continue;
        }
        let meta = path.join("new").join("benchmark.json");
        let est = path.join("new").join("estimates.json");
        if meta.is_file() && est.is_file() {
            if let Some((id, e)) = parse(&meta, &est) {
                out.insert(id, e);
            }
        } else {
            load(&path, out);
        }
    }
}

fn parse(meta: &Path, est: &Path) -> Option<(String, Est)> {
    let meta: Value = serde_json::from_str(&fs::read_to_string(meta).ok()?).ok()?;
    let est: Value = serde_json::from_str(&fs::read_to_string(est).ok()?).ok()?;
    let id = meta["full_id"].as_str()?.to_string();
    let n = meta["throughput"]["Elements"].as_f64().unwrap_or(1.0);
    let median = &est["median"];
    let ci = &median["confidence_interval"];
    Some((
        id,
        Est {
            ns: median["point_estimate"].as_f64()? / n,
            lo: ci["lower_bound"].as_f64()? / n,
            hi: ci["upper_bound"].as_f64()? / n,
        },
    ))
}

fn ns(v: f64) -> String {
    if v >= 10.0 {
        format!("{:.2}", v)
    } else {
        format!("{:.3}", v)
    }
}

fn run(cmd: &str, args: &[&str]) -> Option<String> {
    let out = Command::new(cmd).args(args).output().ok()?;
    let s = String::from_utf8(out.stdout).ok()?;
    let s = s.trim();
    if out.status.success() && !s.is_empty() {
        Some(s.to_string())
    } else {
        None
    }
}

fn cpu() -> String {
    fs::read_to_string("/proc/cpuinfo")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("model name"))
                .and_then(|l| l.split(':').nth(1))
                .map(|m| m.trim().to_string())
        })
        .unwrap_or_else(|| "unknown CPU".to_string())
}

fn today() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let z = (secs / 86_400) as i64 + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    format!("{:04}-{:02}-{:02}", y, m, d)
}

/// Results of one run, indexed by criterion's full benchmark id.
struct Report {
    data: BTreeMap<String, Est>,
}

impl Report {
    fn get(&self, mode: &str, op: &str, imp: &str, ty: &str) -> Option<Est> {
        self.data
            .get(&format!("{}/{}/{}/{}", mode, op, imp, ty))
            .copied()
    }

    fn vs_fixed(&self, mode: &str, op: &str, ours: &str, theirs: &str) -> Option<Verdict> {
        Some(compare(
            self.get(mode, op, "fulcrum", ours)?,
            self.get(mode, op, "fixed-sat", theirs)?,
        ))
    }

    fn vs_native(&self, mode: &str, op: &str, ours: &str, native: &str) -> Option<Verdict> {
        Some(compare(
            self.get(mode, op, "fulcrum", ours)?,
            self.get(mode, op, "native", native)?,
        ))
    }

    fn speed_table(&self, s: &mut String) {
        s.push('|');
        for (ours, theirs) in PAIRS {
            let _ = write!(s, " | `{}` | `fixed` {}", ours, theirs);
        }
        s.push_str(" | `f32` | `f64` |\n|---|");
        for _ in 0..PAIRS.len() * 2 + 2 {
            s.push_str("---:|");
        }
        s.push('\n');
        for (mode, op, label) in CASES {
            let _ = write!(s, "| {}", label);
            for (ours, theirs) in PAIRS {
                let a = self.get(mode, op, "fulcrum", ours);
                let b = self.get(mode, op, "fixed-sat", theirs);
                let v = match (a, b) {
                    (Some(a), Some(b)) => compare(a, b),
                    _ => Verdict::Even,
                };
                let cell = |e: Option<Est>, bold: bool| match e {
                    Some(e) if bold => format!("**{}**", ns(e.ns)),
                    Some(e) => ns(e.ns),
                    None => "—".to_string(),
                };
                let _ = write!(
                    s,
                    " | {} | {}",
                    cell(a, matches!(v, Verdict::Faster(_))),
                    cell(b, matches!(v, Verdict::Slower(_)))
                );
            }
            for native in ["f32", "f64"] {
                let e = self.get(mode, op, "native", native);
                let _ = write!(s, " | {}", e.map_or("—".to_string(), |e| ns(e.ns)));
            }
            s.push_str(" |\n");
        }
    }

    fn verdict_table(&self, s: &mut String) {
        s.push('|');
        for (ours, theirs) in PAIRS {
            let _ = write!(s, " | `{}` vs `{}`", ours, theirs);
        }
        for (ours, native) in NATIVE {
            let _ = write!(s, " | `{}` vs `{}`", ours, native);
        }
        s.push_str(" |\n|---|");
        for _ in 0..PAIRS.len() + NATIVE.len() {
            s.push_str("---|");
        }
        s.push('\n');
        for (mode, op, label) in CASES {
            let _ = write!(s, "| {}", label);
            for (ours, theirs) in PAIRS {
                let v = self.vs_fixed(mode, op, ours, theirs);
                let _ = write!(s, " | {}", v.map_or("—".to_string(), verdict_text));
            }
            for (ours, native) in NATIVE {
                let v = self.vs_native(mode, op, ours, native);
                let _ = write!(s, " | {}", v.map_or("—".to_string(), verdict_text));
            }
            s.push_str(" |\n");
        }
    }

    fn summary(&self, s: &mut String) {
        let mut all = Vec::new();
        for (mode, op, label) in CASES {
            for (ours, theirs) in PAIRS {
                if let Some(v) = self.vs_fixed(mode, op, ours, theirs) {
                    all.push((op, label, ours, theirs, v));
                }
            }
        }
        let faster = all
            .iter()
            .filter(|c| matches!(c.4, Verdict::Faster(_)))
            .count();
        let slower = all
            .iter()
            .filter(|c| matches!(c.4, Verdict::Slower(_)))
            .count();
        let _ = writeln!(
            s,
            "- **Against `fixed`** (same formats, saturating operators): fulcrum is faster in {} of {} cases, on par in {}, slower in {}.",
            faster,
            all.len(),
            all.len() - faster - slower,
            slower
        );

        for (op, name) in [("add", "`+`"), ("mul", "`*`"), ("div", "`/`")] {
            let cases: Vec<_> = all.iter().filter(|c| c.0 == op).collect();
            let ups: Vec<f64> = cases
                .iter()
                .filter_map(|c| match c.4 {
                    Verdict::Faster(r) => Some(r),
                    _ => None,
                })
                .collect();
            let downs: Vec<f64> = cases
                .iter()
                .filter_map(|c| match c.4 {
                    Verdict::Slower(r) => Some(r),
                    _ => None,
                })
                .collect();
            let even = cases.len() - ups.len() - downs.len();
            let mut parts = Vec::new();
            if !ups.is_empty() {
                parts.push(format!("faster in {} ({})", ups.len(), range(&ups)));
            }
            if even > 0 {
                parts.push(format!("on par in {}", even));
            }
            if !downs.is_empty() {
                parts.push(format!("slower in {} ({})", downs.len(), range(&downs)));
            }
            let _ = writeln!(
                s,
                "  - {}: out of {} cases, {}.",
                name,
                cases.len(),
                parts.join(", ")
            );
        }

        let best = all
            .iter()
            .filter_map(|c| match c.4 {
                Verdict::Faster(r) => Some((r, c)),
                _ => None,
            })
            .max_by(|a, b| a.0.total_cmp(&b.0));
        let worst = all
            .iter()
            .filter_map(|c| match c.4 {
                Verdict::Slower(r) => Some((r, c)),
                _ => None,
            })
            .max_by(|a, b| a.0.total_cmp(&b.0));
        if let Some((r, c)) = best {
            let _ = writeln!(
                s,
                "- **Biggest win:** {} of `{}`, {:.2}× faster than `fixed` {}.",
                c.1, c.2, r, c.3
            );
        }
        if let Some((r, c)) = worst {
            let _ = writeln!(
                s,
                "- **Biggest loss:** {} of `{}`, {:.2}× slower than `fixed` {}.",
                c.1, c.2, r, c.3
            );
        }

        for (ours, native) in NATIVE {
            let parts: Vec<String> = CASES
                .iter()
                .filter_map(|&(mode, op, label)| {
                    self.vs_native(mode, op, ours, native)
                        .map(|v| format!("{} {}", label, verdict_text(v)))
                })
                .collect();
            if !parts.is_empty() {
                let _ = writeln!(
                    s,
                    "- **Cost of determinism**, `{}` vs hardware `{}`: {}.",
                    ours,
                    native,
                    parts.join("; ")
                );
            }
        }
    }

    fn section(&self, env_line: &str) -> String {
        let mut s = String::new();
        let _ = writeln!(s, "{}\n", HEADING);
        let _ = writeln!(s, "{}\n", env_line);
        s.push_str(
            "Generated by `bench/src/bin/report.rs` from [`bench/benches/ops.rs`](bench/benches/ops.rs). \
             Operands in `[-2, 2)`, divisors in `±[0.5, 2)`. \
             *Throughput*: 4096 independent operations, the compiler may vectorize. \
             *Latency*: a dependent chain, each result feeds the next operation.\n\n",
        );
        s.push_str("### Summary\n\n");
        self.summary(&mut s);
        s.push_str("\n### Speed, ns per operation (median, lower is better)\n\n");
        s.push_str(
            "Bold marks the winner of each fulcrum / `fixed` pair, only where the difference is significant.\n\n",
        );
        self.speed_table(&mut s);
        s.push_str("\n### fulcrum compared with each competitor\n\n");
        self.verdict_table(&mut s);
        s.push_str(
            "\n### How to read this\n\n\
             - A difference is reported only when the 95% confidence intervals of the two medians do not overlap and the medians differ by at least 5%; everything else is *on par*. \
             Absolute numbers depend on the runner's CPU, ratios measured in the same run are what to compare.\n\
             - `fixed` is measured with `saturating_*`, the closest to fulcrum semantics. \
             fulcrum additionally rounds `*` and `/` to nearest, while `fixed` truncates: fulcrum does more work per operation and returns a more accurate result.\n\
             - `f32`/`f64` are the speed ceiling: hardware floats are fast, but their results may differ between platforms and compilers. \
             The gap shows the price of bit-identical results.\n\
             - Reproduce locally: `cd bench && cargo bench --bench ops && cargo run --release --bin report`.\n",
        );
        s
    }

    fn raw_table(&self) -> String {
        let mut s = String::from("| Benchmark | ns/op, median | 95% CI |\n|---|---:|---:|\n");
        for (id, e) in &self.data {
            let _ = writeln!(
                s,
                "| `{}` | {} | {} – {} |",
                id,
                ns(e.ns),
                ns(e.lo),
                ns(e.hi)
            );
        }
        s
    }
}

fn range(v: &[f64]) -> String {
    let lo = v.iter().copied().fold(f64::INFINITY, f64::min);
    let hi = v.iter().copied().fold(0.0, f64::max);
    if hi - lo < 0.005 {
        format!("{:.2}×", hi)
    } else {
        format!("{:.2}–{:.2}×", lo, hi)
    }
}

fn splice(readme: &str, section: &str) -> String {
    let lines: Vec<&str> = readme.lines().collect();
    let start = lines.iter().position(|l| l.trim_end() == HEADING);
    let (start, end) = match start {
        Some(i) => {
            let end = lines[i + 1..]
                .iter()
                .position(|l| l.starts_with("## "))
                .map_or(lines.len(), |j| i + 1 + j);
            (i, end)
        }
        None => {
            let at = lines
                .iter()
                .position(|l| l.trim_end() == "## Citation")
                .unwrap_or(lines.len());
            (at, at)
        }
    };
    let mut out = String::new();
    for l in &lines[..start] {
        out.push_str(l);
        out.push('\n');
    }
    out.push_str(section);
    if end < lines.len() {
        out.push('\n');
        for l in &lines[end..] {
            out.push_str(l);
            out.push('\n');
        }
    }
    out
}

fn main() {
    let mut criterion = PathBuf::from("target/criterion");
    let mut readme: Option<PathBuf> = None;
    let mut out: Option<PathBuf> = None;
    let mut args = env::args().skip(1);
    while let Some(a) = args.next() {
        let v = args.next().unwrap_or_else(|| {
            eprintln!("missing value for {}", a);
            std::process::exit(2)
        });
        match a.as_str() {
            "--criterion" => criterion = v.into(),
            "--readme" => readme = Some(v.into()),
            "--out" => out = Some(v.into()),
            _ => {
                eprintln!("usage: report [--criterion DIR] [--readme FILE] [--out FILE]");
                std::process::exit(2)
            }
        }
    }

    let mut data = BTreeMap::new();
    load(&criterion, &mut data);
    if data.is_empty() {
        eprintln!(
            "no criterion results in {}, run `cargo bench --bench ops` first",
            criterion.display()
        );
        std::process::exit(1);
    }
    let report = Report { data };

    let date = today();
    let commit = run("git", &["rev-parse", "--short", "HEAD"]).unwrap_or_else(|| "?".into());
    let rustc = run("rustc", &["-V"]).unwrap_or_else(|| "rustc ?".into());
    let machine = if env::var("GITHUB_ACTIONS").ok().as_deref() == Some("true") {
        "GitHub-hosted runner"
    } else {
        "local machine"
    };
    let env_line = format!(
        "Measured on {}, commit `{}`, {}: {}, {} {}, {}.",
        date,
        commit,
        machine,
        cpu(),
        env::consts::ARCH,
        env::consts::OS,
        rustc
    );
    let section = report.section(&env_line);

    if readme.is_none() && out.is_none() {
        print!("{}", section);
        return;
    }
    if let Some(path) = readme {
        let old = fs::read_to_string(&path).expect("read README");
        fs::write(&path, splice(&old, &section)).expect("write README");
    }
    if let Some(path) = out {
        let body = section
            .replacen(HEADING, &format!("# Benchmark results, {}", date), 1)
            .replace("\n### ", "\n## ")
            .replace("](bench/", "](../");
        let full = format!("{}\n## All cases\n\n{}", body, report.raw_table());
        fs::write(&path, full).expect("write results");
    }
}
