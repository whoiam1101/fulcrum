import Fulcrum.Spec
import Fulcrum.Kernel.Funs
import Fulcrum.Lemmas.Nat
import Fulcrum.Lemmas.Int
import Fulcrum.Lemmas.List
import Fulcrum.Lemmas.Scalar
import Fulcrum.Lemmas.Loop
import Fulcrum.Math.Range
import Fulcrum.Math.Round
import Fulcrum.Math.Div
import Fulcrum.Math.Newton
import Fulcrum.Math.Sqrt
import Fulcrum.Math.Rsqrt
import Fulcrum.Math.Series
import Fulcrum.Math.Const
import Fulcrum.Tables.Trig
import Fulcrum.Tables.Exp
import Fulcrum.Math.Fixed
import Fulcrum.Math.Quarter
import Fulcrum.Math.Cot
import Fulcrum.Math.Atan
import Fulcrum.Math.Log
import Fulcrum.Math.Exp
import Fulcrum.Math.Pow
import Fulcrum.L1.ShrRound
import Fulcrum.L1.RoundsUp
import Fulcrum.L2.Narrow
import Fulcrum.L2.Parts
import Fulcrum.L3.Mul
import Fulcrum.L3.Lerp
import Fulcrum.L3.Rescale
import Fulcrum.L3.Div.Magnitude
import Fulcrum.L3.Div.Signed
import Fulcrum.L3.Div.Total
import Fulcrum.L3.Sqrt.Table
import Fulcrum.L3.Sqrt.Common
import Fulcrum.L3.Sqrt.K8
import Fulcrum.L3.Sqrt.K16
import Fulcrum.L3.Sqrt.RsqrtTable
import Fulcrum.L3.Sqrt.K32
import Fulcrum.L3.Sqrt.K64
import Fulcrum.L4.SinQuarter
import Fulcrum.L4.Turns
import Fulcrum.L4.Radians
import Fulcrum.L4.Tan
import Fulcrum.L4.Atan
import Fulcrum.L4.Angle
import Fulcrum.L4.Vec
import Fulcrum.L4.Log
import Fulcrum.L4.Exp
import Fulcrum.L4.Pow

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
