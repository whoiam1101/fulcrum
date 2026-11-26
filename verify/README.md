# verify

Formal verification (docs/ARCHITECTURE.md §6.1):

| Folder | Tool | What it proves |
|---|---|---|
| `../src/proofs/` | Kani, `cargo kani` from the repository root | no panics and equality with the specification for the code outside the extracted modules |
| `lean/` | Lean 4 on the code extracted by Charon and Aeneas | layers L1–L5 of stage 8 of `ROADMAP.md`: `src/kernel.rs` equals the specification, `src/trig.rs` and `src/exp.rs` stay within their error bounds |

`just lean` builds `lean/` and then runs `leanchecker` on each module of `lean/Fulcrum/` in turn, since it crashes when given several at once.

`lean/Fulcrum/Kernel/Types.lean` and `Funs.lean` hold `src/kernel.rs`, `src/trig.rs`, `src/exp.rs` and their tables, extracted with `just aeneas-src aeneas extract`. CI extracts them again and fails if they differ from the code. `FunsExternal.lean` defines by hand the functions of `core` that Aeneas does not know.

The root `Fulcrum.lean` ends with `#check_axioms`. The build fails if a declaration of a `Fulcrum` module is an axiom or depends on anything beyond `propext`, `Classical.choice` and `Quot.sound`, which rules out `sorry`, `native_decide` and `bv_decide`.
