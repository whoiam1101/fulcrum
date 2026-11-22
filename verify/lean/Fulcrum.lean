import Fulcrum.Spec
import Fulcrum.Kernel.Funs
import Fulcrum.Round
import Fulcrum.Narrow
import Fulcrum.Mul
import Fulcrum.Lerp
import Fulcrum.Div
import Fulcrum.Rescale

/-!
# fulcrum

Every declaration of a `Fulcrum` module, this one included, depends on no axioms beyond the three
of Lean and Mathlib: `propext`, `Classical.choice` and `Quot.sound`. No
`sorry`, no `native_decide` or `bv_decide` (`Lean.ofReduceBool`), no axiom of
our own; `#check_axioms` below fails the build otherwise. CI then runs
`leanchecker` on every file of `Fulcrum/`, one at a time: it replays each
declaration through the kernel, so `debug.skipKernelTC` does not pass, and a
file not imported here has no `.olean` and fails it.
-/

open Lean Elab Command in
/-- Fails unless every declaration of a `Fulcrum` module uses only `propext`,
`Classical.choice` and `Quot.sound`, and at least one was checked. -/
elab "#check_axioms" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (decl, ci) in env.constants.toList do
    let module := match env.getModuleIdxFor? decl with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless (`Fulcrum).isPrefixOf module do continue
    if ci matches .axiomInfo _ then
      throwError "{decl} is an axiom"
    for a in ← collectAxioms decl do
      unless allowed.contains a do
        throwError "{decl} depends on {a}"
    checked := checked + 1
  if checked == 0 then
    throwError "no declarations checked"
  logInfo m!"{checked} declarations use only the standard axioms"

#check_axioms
