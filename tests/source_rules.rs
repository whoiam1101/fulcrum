//! Source rules of the repository, checked by every `cargo test` run, locally
//! and in CI:
//!
//! - only doc comments: `///` and `//!` in Rust, `/-- -/` and `/-! -/` in Lean,
//!   none at all in TOML, YAML and `.gitignore`;
//! - no platform-specific code and no floating point in `src`, except
//!   `src/float.rs` behind the `float-convert` feature.

use std::fs;
use std::path::{Path, PathBuf};

const SKIPPED_DIRS: &[&str] = &["target", ".git", ".lake", ".claude"];
const PLATFORM_TOKENS: &[&str] = &[
    "asm!",
    "target_arch",
    "target_pointer_width",
    "target_endian",
];
const FLOAT_WORDS: &[&str] = &["f32", "f64"];

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if path.is_dir() {
            if !SKIPPED_DIRS.contains(&name.as_str()) {
                collect(&path, &mut *out);
            }
        } else {
            out.push(path);
        }
    }
}

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn files() -> Vec<PathBuf> {
    let mut out = Vec::new();
    collect(&root(), &mut out);
    out.sort();
    out
}

fn after_space_or_start(chars: &[char], i: usize) -> bool {
    i == 0 || chars[i - 1].is_whitespace()
}

/// A Rust line with `//` that is not `///` or `//!`, or with a block comment opener.
fn rust_violation(line: &str) -> bool {
    let chars: Vec<char> = line.chars().collect();
    let opener = ['/', '*'];
    for i in 0..chars.len().saturating_sub(1) {
        if chars[i] == opener[0] && chars[i + 1] == opener[1] {
            return true;
        }
        if chars[i] == '/' && chars[i + 1] == '/' && after_space_or_start(&chars, i) {
            match chars.get(i + 2) {
                Some('/') | Some('!') => {}
                _ => return true,
            }
        }
    }
    false
}

/// A TOML, YAML or `.gitignore` line with `#` at its start or after whitespace.
fn config_violation(line: &str) -> bool {
    let chars: Vec<char> = line.chars().collect();
    (0..chars.len()).any(|i| chars[i] == '#' && after_space_or_start(&chars, i))
}

/// A Lean line with `--` at its start or after whitespace, or with `/-` that
/// does not open a doc comment.
fn lean_violation(line: &str) -> bool {
    let chars: Vec<char> = line.chars().collect();
    (0..chars.len().saturating_sub(1)).any(|i| {
        let dashes = chars[i] == '-' && chars[i + 1] == '-' && after_space_or_start(&chars, i);
        let block = chars[i] == '/'
            && chars[i + 1] == '-'
            && !matches!(chars.get(i + 2), Some('-') | Some('!') | None);
        dashes || block
    })
}

fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn has_word(line: &str, word: &str) -> bool {
    let mut start = 0;
    while let Some(pos) = line[start..].find(word) {
        let at = start + pos;
        let before = line[..at].chars().next_back();
        let after = line[at + word.len()..].chars().next();
        if !before.map_or(false, is_word_char) && !after.map_or(false, is_word_char) {
            return true;
        }
        start = at + word.len();
    }
    false
}

/// A `src` line with platform-specific code or a floating-point type.
fn platform_violation(line: &str) -> bool {
    PLATFORM_TOKENS.iter().any(|t| line.contains(t))
        || FLOAT_WORDS.iter().any(|w| has_word(line, w))
}

fn violations(rule: impl Fn(&Path) -> Option<fn(&str) -> bool>) -> Vec<String> {
    let root = root();
    let mut found = Vec::new();
    for path in files() {
        let check = match rule(&path) {
            Some(check) => check,
            None => continue,
        };
        let text = match fs::read_to_string(&path) {
            Ok(text) => text,
            Err(_) => continue,
        };
        for (n, line) in text.lines().enumerate() {
            if check(line) {
                let shown = path.strip_prefix(&root).unwrap_or(&path).display();
                found.push(format!("{}:{}: {}", shown, n + 1, line.trim()));
            }
        }
    }
    found
}

fn extension(path: &Path) -> &str {
    path.extension().and_then(|e| e.to_str()).unwrap_or("")
}

#[test]
fn only_doc_comments() {
    let lean = root().join("verify").join("lean");
    let found = violations(|path| {
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        match extension(path) {
            "rs" => Some(rust_violation as fn(&str) -> bool),
            "toml" | "yml" | "yaml" => Some(config_violation),
            "lean" if path.starts_with(&lean) => Some(lean_violation),
            _ if name == ".gitignore" => Some(config_violation),
            _ => None,
        }
    });
    assert!(
        found.is_empty(),
        "regular comments (only doc comments are allowed, see docs/ARCHITECTURE.md §0):\n{}",
        found.join("\n")
    );
}

#[test]
fn no_platform_code_in_src() {
    let src = root().join("src");
    let float = src.join("float.rs");
    let found = violations(|path| {
        if extension(path) == "rs" && path.starts_with(&src) && path != float {
            Some(platform_violation as fn(&str) -> bool)
        } else {
            None
        }
    });
    assert!(
        found.is_empty(),
        "platform-specific code or floating point in src (allowed only in src/float.rs):\n{}",
        found.join("\n")
    );
}

#[test]
fn rules_catch_what_they_forbid() {
    let slashes = "/".repeat(2);
    assert!(rust_violation(&format!("let x = 1; {} note", slashes)));
    assert!(rust_violation("// note"));
    assert!(rust_violation(&format!("{}{} block", '/', '*')));
    assert!(!rust_violation("/// doc"));
    assert!(!rust_violation("//! doc"));
    assert!(!rust_violation("let url = \"https://example.com\";"));
    assert!(config_violation("# note"));
    assert!(config_violation("key = 1 # note"));
    assert!(!config_violation("color = \"#fff\""));
    assert!(lean_violation("-- note"));
    assert!(lean_violation("/- note -/"));
    assert!(!lean_violation("/-- doc -/"));
    assert!(!lean_violation("/-! doc -/"));
    assert!(platform_violation("let x: f64 = 0.0;"));
    assert!(platform_violation("#[cfg(target_arch = \"x86_64\")]"));
    assert!(!platform_violation("let half64 = 1;"));
    assert!(!platform_violation("fn from_f64_bits() {}"));
}
