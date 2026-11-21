# verify

Formal verification (docs/ARCHITECTURE.md §6.1):

| Folder | Layer | Tool |
|---|---|---|
| `../src/proofs/` | 1 | Kani proof harnesses, run with `cargo kani` from the repository root |
| `lean/` | 2–3 | Lean 4 spec and proofs through Aeneas extraction (stage 8 of `ROADMAP.md`): `src/kernel.rs` equals the specification, and the error bounds of `src/trig.rs` and of its tables |

`lean/` builds with `lake exe cache get && lake build`. The root `Fulcrum.lean` ends with `#check_axioms`: the build fails if any declaration of a `Fulcrum` module is an axiom or depends on anything beyond `propext`, `Classical.choice` and `Quot.sound`, so no `sorry`, `native_decide` or `bv_decide`. CI then runs `leanchecker` on every module of `lean/Fulcrum/` separately (given several at once, it crashes).
