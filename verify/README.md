# verify

Formal verification (docs/ARCHITECTURE.md §6.1):

| Folder | Layer | Tool |
|---|---|---|
| `../src/proofs/` | 1 | Kani proof harnesses, run with `cargo kani` from the repository root |
| `lean/` | 2–3 | Lean 4 spec and proofs through Aeneas extraction (stage 8 of `ROADMAP.md`): `src/kernel.rs` equals the specification, and the error bounds of `src/trig.rs` and of its tables |
