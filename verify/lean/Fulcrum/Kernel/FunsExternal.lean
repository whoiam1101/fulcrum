module
public import Aeneas
public import Fulcrum.Kernel.Types
@[expose] public section
open Aeneas Aeneas.Std Result

/-!
# The functions of `core` that the kernel calls and Aeneas does not define

`unsigned_abs` of a signed integer is its two's complement absolute value
read as unsigned: the bits of `BitVec.abs`, so `MIN` maps to `2^(BITS-1)`.
-/

/-- `i8::unsigned_abs`. -/
def core.num.I8.unsigned_abs (x : Std.I8) : Result Std.U8 := ok ⟨x.bv.abs⟩

/-- `i16::unsigned_abs`. -/
def core.num.I16.unsigned_abs (x : Std.I16) : Result Std.U16 := ok ⟨x.bv.abs⟩

/-- `i32::unsigned_abs`. -/
def core.num.I32.unsigned_abs (x : Std.I32) : Result Std.U32 := ok ⟨x.bv.abs⟩

/-- `i64::unsigned_abs`. -/
def core.num.I64.unsigned_abs (x : Std.I64) : Result Std.U64 := ok ⟨x.bv.abs⟩
