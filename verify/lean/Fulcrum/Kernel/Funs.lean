module
public import Aeneas
public import Fulcrum.Kernel.Types
public import Fulcrum.Kernel.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

set_option maxHeartbeats 1000000

set_option maxRecDepth 2048

noncomputable section

namespace fulcrum

/-- [fulcrum::kernel::shr_round]:
    Source: 'src/kernel.rs', lines 39:0-47:1 -/
def kernel.shr_round (n : Std.I128) (s : Std.U32) : Result Std.I128 := do
  if s = 0#u32
  then ok n
  else
    if s >= 128#u32
    then ok 0#i128
    else
      let i ← n >>> s
      let i1 ← s - 1#u32
      let i2 ← n >>> i1
      let i3 ← lift (i2 &&& 1#i128)
      i + i3

/-- [fulcrum::kernel::magnitude_rounds_up]:
    Source: 'src/kernel.rs', lines 53:0-55:1 -/
def kernel.magnitude_rounds_up
  (negative : Bool) (half : Bool) (sticky : Bool) : Result Bool := do
  if half
  then if negative
       then ok sticky
       else ok true
  else ok false

/-- [fulcrum::kernel::rescale]:
    Source: 'src/kernel.rs', lines 61:0-71:1 -/
def kernel.rescale
  (raw : Std.I128) (src_frac : Std.U32) (dst_frac : Std.U32) :
  Result (Std.I128 × Bool)
  := do
  if src_frac >= dst_frac
  then
    let i ← src_frac - dst_frac
    let i1 ← kernel.shr_round raw i
    ok (i1, false)
  else
    let s ← dst_frac - src_frac
    let i ← lift (core.num.I128.wrapping_shl raw s)
    let i1 ← core.num.I128.MAX >>> s
    if raw > i1
    then ok (i, true)
    else let i2 ← core.num.I128.MIN >>> s
         ok (i, raw < i2)

/-- [fulcrum::kernel::rsqrt_start]: loop body 1:
    Source: 'src/kernel.rs', lines 701:8-708:9 -/
@[rust_loop_body]
def kernel.rsqrt_start_loop0_loop0.body
  (d : Std.U128) (lo : Std.U128) (hi : Std.U128) :
  Result (ControlFlow (Std.U128 × Std.U128) Std.U128)
  := do
  let i ← hi - lo
  if i > 1#u128
  then
    let i1 ← lo + hi
    let mid ← i1 / 2#u128
    let i2 ← mid * mid
    let i3 ← i2 * d
    let i4 ← 1#u128 <<< 71#i32
    if i3 <= i4
    then ok (cont (mid, hi))
    else ok (cont (lo, mid))
  else ok (done lo)

/-- [fulcrum::kernel::rsqrt_start]: loop 1:
    Source: 'src/kernel.rs', lines 701:8-708:9 -/
@[rust_loop]
def kernel.rsqrt_start_loop0_loop0
  (d : Std.U128) (lo : Std.U128) (hi : Std.U128) : Result Std.U128 := do
  loop
    (fun (lo1, hi1) => kernel.rsqrt_start_loop0_loop0.body d lo1 hi1)
    (lo, hi)

/-- [fulcrum::kernel::rsqrt_start]: loop body 0:
    Source: 'src/kernel.rs', lines 697:4-711:5 -/
@[rust_loop_body]
def kernel.rsqrt_start_loop0.body
  (table : Array Std.U32 192#usize) (t : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 192#usize) × Std.Usize) (Array Std.U32
    192#usize))
  := do
  if t < 256#usize
  then
    let i ← 2#usize * t
    let i1 ← i + 1#usize
    let d ← lift (UScalar.cast .U128 i1)
    let hi ← 1#u128 <<< 33#i32
    let lo ← kernel.rsqrt_start_loop0_loop0 d 0#u128 hi
    let i2 ← t - 64#usize
    let i3 ← lift (UScalar.cast .U32 lo)
    let a ← Array.update table i2 i3
    let t1 ← t + 1#usize
    ok (cont (a, t1))
  else ok (done table)

/-- [fulcrum::kernel::rsqrt_start]: loop 0:
    Source: 'src/kernel.rs', lines 697:4-711:5 -/
@[rust_loop]
def kernel.rsqrt_start_loop0
  (table : Array Std.U32 192#usize) (t : Std.Usize) :
  Result (Array Std.U32 192#usize)
  := do
  loop
    (fun (table1, t1) => kernel.rsqrt_start_loop0.body table1 t1)
    (table, t)

/-- [fulcrum::kernel::rsqrt_start]:
    Source: 'src/kernel.rs', lines 694:0-713:1 -/
def kernel.rsqrt_start : Result (Array Std.U32 192#usize) := do
  let table := Array.repeat 192#usize 0#u32
  kernel.rsqrt_start_loop0 table 64#usize

/-- [fulcrum::kernel::RSQRT_START]
    Source: 'src/kernel.rs', lines 692:0-692:46 -/
@[global_simps, irreducible]
def kernel.RSQRT_START : Result (Array Std.U32 192#usize) := kernel.rsqrt_start

/-- [fulcrum::kernel::k32::NEWTON_STEPS]
    Source: 'src/kernel.rs', lines 334:12-334:45; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
@[global_simps, irreducible] def kernel.k32.NEWTON_STEPS : Std.U32 := 0#u32

/-- [fulcrum::kernel::k32::isqrt]: loop body 0:
    Source: 'src/kernel.rs', lines 678:0-678:74 -/
@[rust_loop_body]
def kernel.k32.isqrt_loop0.body
  (n : Std.U64) (x : Std.U64) : Result (ControlFlow Std.U64 Std.U64) := do
  let i ← x + 1#u64
  let i1 ← i * i
  if i1 <= n
  then ok (cont i)
  else ok (done x)

/-- [fulcrum::kernel::k32::isqrt]: loop 0:
    Source: 'src/kernel.rs', lines 678:0-678:74 -/
@[rust_loop]
def kernel.k32.isqrt_loop0 (n : Std.U64) (x : Std.U64) : Result Std.U64 := do
  loop
    (fun x1 => kernel.k32.isqrt_loop0.body n x1)
    x

/-- [fulcrum::kernel::k32::isqrt]: loop body 1:
    Source: 'src/kernel.rs', lines 678:0-678:74 -/
@[rust_loop_body]
def kernel.k32.isqrt_loop1.body
  (n : Std.U64) (x : Std.U64) (i : Std.U32) :
  Result (ControlFlow (Std.U64 × Std.U32) Std.U64)
  := do
  if i < kernel.k32.NEWTON_STEPS
  then
    let i1 ← n / x
    let i2 ← x + i1
    let x1 ← i2 >>> 1#i32
    let i3 ← i + 1#u32
    ok (cont (x1, i3))
  else ok (done x)

/-- [fulcrum::kernel::k32::isqrt]: loop 1:
    Source: 'src/kernel.rs', lines 678:0-678:74 -/
@[rust_loop]
def kernel.k32.isqrt_loop1
  (n : Std.U64) (x : Std.U64) (i : Std.U32) : Result Std.U64 := do
  loop
    (fun (x1, i1) => kernel.k32.isqrt_loop1.body n x1 i1)
    (x, i)

/-- [fulcrum::kernel::k32::isqrt]: loop body 2:
    Source: 'src/kernel.rs', lines 678:0-678:74 -/
@[rust_loop_body]
def kernel.k32.isqrt_loop2.body
  (n : Std.U64) (x : Std.U64) : Result (ControlFlow Std.U64 Std.U64) := do
  let i ← x * x
  if i > n
  then let x1 ← x - 1#u64
       ok (cont x1)
  else ok (done x)

/-- [fulcrum::kernel::k32::isqrt]: loop 2:
    Source: 'src/kernel.rs', lines 678:0-678:74 -/
@[rust_loop]
def kernel.k32.isqrt_loop2 (n : Std.U64) (x : Std.U64) : Result Std.U64 := do
  loop
    (fun x1 => kernel.k32.isqrt_loop2.body n x1)
    x

/-- [fulcrum::kernel::k32::isqrt]: loop body 3:
    Source: 'src/kernel.rs', lines 678:0-678:74 -/
@[rust_loop_body]
def kernel.k32.isqrt_loop3.body
  (n : Std.U64) (x : Std.U64) (i : Std.U32) :
  Result (ControlFlow (Std.U64 × Std.U32) Std.U64)
  := do
  if i < kernel.k32.NEWTON_STEPS
  then
    let i1 ← n / x
    let i2 ← x + i1
    let x1 ← i2 >>> 1#i32
    let i3 ← i + 1#u32
    ok (cont (x1, i3))
  else ok (done x)

/-- [fulcrum::kernel::k32::isqrt]: loop 3:
    Source: 'src/kernel.rs', lines 678:0-678:74 -/
@[rust_loop]
def kernel.k32.isqrt_loop3
  (n : Std.U64) (x : Std.U64) (i : Std.U32) : Result Std.U64 := do
  loop
    (fun (x1, i1) => kernel.k32.isqrt_loop3.body n x1 i1)
    (x, i)

/-- [fulcrum::kernel::k32::isqrt]: loop body 4:
    Source: 'src/kernel.rs', lines 678:0-678:74 -/
@[rust_loop_body]
def kernel.k32.isqrt_loop4.body
  (n : Std.U64) (x : Std.U64) : Result (ControlFlow Std.U64 Std.U64) := do
  let i ← x * x
  if i > n
  then let x1 ← x - 1#u64
       ok (cont x1)
  else ok (done x)

/-- [fulcrum::kernel::k32::isqrt]: loop 4:
    Source: 'src/kernel.rs', lines 678:0-678:74 -/
@[rust_loop]
def kernel.k32.isqrt_loop4 (n : Std.U64) (x : Std.U64) : Result Std.U64 := do
  loop
    (fun x1 => kernel.k32.isqrt_loop4.body n x1)
    x

/-- [fulcrum::kernel::k32::isqrt]:
    Source: 'src/kernel.rs', lines 494:12-511:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.isqrt (n : Std.U64) : Result Std.U64 := do
  if n < 2#u64
  then ok n
  else
    let i ← lift (core.num.U64.leading_zeros n)
    let i1 ← lift (~~~ 1#u32)
    let z ← lift (i &&& i1)
    let m ← n <<< z
    let a ← m >>> 32#i32
    let a1 ← kernel.RSQRT_START
    let i2 ← m >>> 56#i32
    let i3 ← lift (UScalar.cast .Usize i2)
    let i4 ← i3 - 64#usize
    let i5 ← Array.index_usize a1 i4
    let y ← lift (UScalar.cast .U64 i5)
    let i6 ← 3#u64 <<< 62#i32
    let i7 ← y * y
    let i8 ← i7 >>> 32#i32
    let i9 ← a * i8
    let i10 ← i6 - i9
    let i11 ← i10 >>> 32#i32
    let i12 ← y * i11
    let y1 ← i12 >>> 31#i32
    let i13 ← a * y1
    let s ← i13 >>> 31#i32
    let i14 ← lift (core.num.U64.wrapping_mul s s)
    let i15 ← lift (core.num.U64.wrapping_sub m i14)
    let e ← lift (UScalar.hcast .I64 i15)
    let i16 ← lift (UScalar.hcast .I64 s)
    let i17 ← lift (UScalar.hcast .I128 y1)
    let i18 ← lift (IScalar.cast .I128 e)
    let i19 ← i17 * i18
    let i20 ← i19 >>> 64#i32
    let i21 ← lift (IScalar.cast .I64 i20)
    let i22 ← i16 + i21
    let s1 ← lift (IScalar.hcast .U64 i22)
    let i23 ← z / 2#u32
    let x ← s1 >>> i23
    let i24 ← x + 1#u64
    let i25 ← i24 * i24
    if i25 <= n
    then
      let x1 ← kernel.k32.isqrt_loop0 n i24
      let x2 ← kernel.k32.isqrt_loop1 n x1 0#u32
      let i26 ← x2 * x2
      if i26 > n
      then let x3 ← x2 - 1#u64
           kernel.k32.isqrt_loop2 n x3
      else ok x2
    else
      let x1 ← kernel.k32.isqrt_loop3 n x 0#u32
      let i26 ← x1 * x1
      if i26 > n
      then let x2 ← x1 - 1#u64
           kernel.k32.isqrt_loop4 n x2
      else ok x1

/-- [fulcrum::kernel::scale_narrow]: loop body 1:
    Source: 'src/kernel.rs', lines 305:12-307:13 -/
@[rust_loop_body]
def kernel.scale_narrow_loop0_loop0.body
  (k : Std.U64) (s : Std.U64) (four : Std.U128) (m : Std.U64) :
  Result (ControlFlow Std.U64 Std.U64)
  := do
  if m < k
  then
    let i ← 2#u64 * m
    let i1 ← i + 1#u64
    let i2 ← i + 1#u64
    let i3 ← i1 * i2
    let i4 ← lift (UScalar.cast .U128 i3)
    let i5 ← lift (UScalar.cast .U128 s)
    let i6 ← i4 * i5
    if i6 < four
    then let m1 ← m + 1#u64
         ok (cont m1)
    else ok (done m)
  else ok (done m)

/-- [fulcrum::kernel::scale_narrow]: loop 1:
    Source: 'src/kernel.rs', lines 305:12-307:13 -/
@[rust_loop]
def kernel.scale_narrow_loop0_loop0
  (k : Std.U64) (s : Std.U64) (four : Std.U128) (m : Std.U64) :
  Result Std.U64
  := do
  loop
    (fun m1 => kernel.scale_narrow_loop0_loop0.body k s four m1)
    m

/-- [fulcrum::kernel::scale_narrow]: loop body 2:
    Source: 'src/kernel.rs', lines 310:12-312:13 -/
@[rust_loop_body]
def kernel.scale_narrow_loop0_loop1.body
  (s : Std.U64) (four : Std.U128) (m : Std.U64) :
  Result (ControlFlow Std.U64 Std.U64)
  := do
  if m > 0#u64
  then
    let i ← 2#u64 * m
    let i1 ← i - 1#u64
    let i2 ← i - 1#u64
    let i3 ← i1 * i2
    let i4 ← lift (UScalar.cast .U128 i3)
    let i5 ← lift (UScalar.cast .U128 s)
    let i6 ← i4 * i5
    if i6 > four
    then let m1 ← m - 1#u64
         ok (cont m1)
    else ok (done m)
  else ok (done m)

/-- [fulcrum::kernel::scale_narrow]: loop 2:
    Source: 'src/kernel.rs', lines 310:12-312:13 -/
@[rust_loop]
def kernel.scale_narrow_loop0_loop1
  (s : Std.U64) (four : Std.U128) (m : Std.U64) : Result Std.U64 := do
  loop
    (fun m1 => kernel.scale_narrow_loop0_loop1.body s four m1)
    m

/-- [fulcrum::kernel::scale_narrow]: loop body 3:
    Source: 'src/kernel.rs', lines 310:12-312:13 -/
@[rust_loop_body]
def kernel.scale_narrow_loop0_loop2.body
  (s : Std.U64) (four : Std.U128) (m : Std.U64) :
  Result (ControlFlow Std.U64 Std.U64)
  := do
  if m > 0#u64
  then
    let i ← 2#u64 * m
    let i1 ← i - 1#u64
    let i2 ← i - 1#u64
    let i3 ← i1 * i2
    let i4 ← lift (UScalar.cast .U128 i3)
    let i5 ← lift (UScalar.cast .U128 s)
    let i6 ← i4 * i5
    if i6 > four
    then let m1 ← m - 1#u64
         ok (cont m1)
    else ok (done m)
  else ok (done m)

/-- [fulcrum::kernel::scale_narrow]: loop 3:
    Source: 'src/kernel.rs', lines 310:12-312:13 -/
@[rust_loop]
def kernel.scale_narrow_loop0_loop2
  (s : Std.U64) (four : Std.U128) (m : Std.U64) : Result Std.U64 := do
  loop
    (fun m1 => kernel.scale_narrow_loop0_loop2.body s four m1)
    m

/-- [fulcrum::kernel::scale_narrow]: loop body 0:
    Source: 'src/kernel.rs', lines 295:4-316:5 -/
@[rust_loop_body]
def kernel.scale_narrow_loop0.body
  (v : Array Std.I64 3#usize) (k : Std.U64) (s : Std.U64) (inv : Std.U64)
  (shift : Std.U32) (out : Array Std.I64 3#usize) (i : Std.Usize) :
  Result (ControlFlow ((Array Std.I64 3#usize) × Std.Usize) (Array Std.I64
    3#usize))
  := do
  if i < 3#usize
  then
    let x ← Array.index_usize v i
    let i1 ← core.num.I64.unsigned_abs x
    let p ← i1 * k
    let i2 ← lift (UScalar.cast .U128 p)
    let i3 ← lift (UScalar.cast .U128 p)
    let i4 ← i2 * i3
    let four ← 4#u128 * i4
    let i5 ← lift (UScalar.cast .U128 p)
    let i6 ← lift (UScalar.cast .U128 inv)
    let i7 ← i5 * i6
    let i8 ← shift - 1#u32
    let i9 ← 1#u128 <<< i8
    let i10 ← i7 + i9
    let i11 ← i10 >>> shift
    let m ← lift (UScalar.cast .U64 i11)
    let m1 ← if m > k
               then ok k
               else ok m
    if m1 < k
    then
      let i12 ← 2#u64 * m1
      let i13 ← i12 + 1#u64
      let i14 ← i12 + 1#u64
      let i15 ← i13 * i14
      let i16 ← lift (UScalar.cast .U128 i15)
      let i17 ← lift (UScalar.cast .U128 s)
      let i18 ← i16 * i17
      if i18 < four
      then
        let m2 ← m1 + 1#u64
        let m3 ← kernel.scale_narrow_loop0_loop0 k s four m2
        let i19 ←
          if x < 0#i64
          then do
               let i20 ← lift (UScalar.hcast .I64 m3)
               -. i20
          else ok (UScalar.hcast .I64 m3)
        let a ← Array.update out i i19
        let i20 ← i + 1#usize
        ok (cont (a, i20))
      else
        if m1 > 0#u64
        then
          let i19 ← i12 - 1#u64
          let i20 ← i12 - 1#u64
          let i21 ← i19 * i20
          let i22 ← lift (UScalar.cast .U128 i21)
          let i23 ← lift (UScalar.cast .U128 s)
          let i24 ← i22 * i23
          if i24 > four
          then
            let m2 ← m1 - 1#u64
            let m3 ← kernel.scale_narrow_loop0_loop1 s four m2
            let i25 ←
              if x < 0#i64
              then do
                   let i26 ← lift (UScalar.hcast .I64 m3)
                   -. i26
              else ok (UScalar.hcast .I64 m3)
            let a ← Array.update out i i25
            let i26 ← i + 1#usize
            ok (cont (a, i26))
          else
            let i25 ←
              if x < 0#i64
              then do
                   let i26 ← lift (UScalar.hcast .I64 m1)
                   -. i26
              else ok (UScalar.hcast .I64 m1)
            let a ← Array.update out i i25
            let i26 ← i + 1#usize
            ok (cont (a, i26))
        else
          let i19 ←
            if x < 0#i64
            then do
                 let i20 ← lift (UScalar.hcast .I64 m1)
                 -. i20
            else ok (UScalar.hcast .I64 m1)
          let a ← Array.update out i i19
          let i20 ← i + 1#usize
          ok (cont (a, i20))
    else
      if m1 > 0#u64
      then
        let i12 ← 2#u64 * m1
        let i13 ← i12 - 1#u64
        let i14 ← i12 - 1#u64
        let i15 ← i13 * i14
        let i16 ← lift (UScalar.cast .U128 i15)
        let i17 ← lift (UScalar.cast .U128 s)
        let i18 ← i16 * i17
        if i18 > four
        then
          let m2 ← m1 - 1#u64
          let m3 ← kernel.scale_narrow_loop0_loop2 s four m2
          let i19 ←
            if x < 0#i64
            then do
                 let i20 ← lift (UScalar.hcast .I64 m3)
                 -. i20
            else ok (UScalar.hcast .I64 m3)
          let a ← Array.update out i i19
          let i20 ← i + 1#usize
          ok (cont (a, i20))
        else
          let i19 ←
            if x < 0#i64
            then do
                 let i20 ← lift (UScalar.hcast .I64 m1)
                 -. i20
            else ok (UScalar.hcast .I64 m1)
          let a ← Array.update out i i19
          let i20 ← i + 1#usize
          ok (cont (a, i20))
      else
        let i12 ←
          if x < 0#i64
          then do
               let i13 ← lift (UScalar.hcast .I64 m1)
               -. i13
          else ok (UScalar.hcast .I64 m1)
        let a ← Array.update out i i12
        let i13 ← i + 1#usize
        ok (cont (a, i13))
  else ok (done out)

/-- [fulcrum::kernel::scale_narrow]: loop 0:
    Source: 'src/kernel.rs', lines 295:4-316:5 -/
@[rust_loop]
def kernel.scale_narrow_loop0
  (v : Array Std.I64 3#usize) (k : Std.U64) (s : Std.U64) (inv : Std.U64)
  (shift : Std.U32) (out : Array Std.I64 3#usize) (i : Std.Usize) :
  Result (Array Std.I64 3#usize)
  := do
  loop
    (fun (out1, i1) => kernel.scale_narrow_loop0.body v k s inv shift out1 i1)
    (out, i)

/-- [fulcrum::kernel::scale_narrow]:
    Source: 'src/kernel.rs', lines 289:0-318:1 -/
def kernel.scale_narrow
  (v : Array Std.I64 3#usize) (k : Std.U64) (s : Std.U64) :
  Result (Array Std.I64 3#usize)
  := do
  let i ← lift (core.num.U64.leading_zeros s)
  let i1 ← lift (core.num.U32.saturating_sub i 1#u32)
  let i2 ← lift (~~~ 1#u32)
  let z ← lift (i1 &&& i2)
  let i3 ← 1#u128 <<< 94#i32
  let i4 ← s <<< z
  let i5 ← kernel.k32.isqrt i4
  let i6 ← lift (UScalar.cast .U128 i5)
  let i7 ← i3 / i6
  let inv ← lift (UScalar.cast .U64 i7)
  let i8 ← z / 2#u32
  let shift ← 94#u32 - i8
  let out := Array.repeat 3#usize 0#i64
  kernel.scale_narrow_loop0 v k s inv shift out 0#usize

/-- [fulcrum::kernel::k8::fits]:
    Source: 'src/kernel.rs', lines 340:12-342:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.fits (w : Std.I16) : Result Bool := do
  let i ← lift (IScalar.cast .I16 core.num.I8.MIN)
  if w >= i
  then let i1 ← lift (IScalar.cast .I16 core.num.I8.MAX)
       ok (w <= i1)
  else ok false

/-- [fulcrum::kernel::k8::narrow]:
    Source: 'src/kernel.rs', lines 346:12-352:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.narrow (w : Std.I16) : Result (Option Std.I8) := do
  let b ← kernel.k8.fits w
  if b
  then let i ← lift (IScalar.cast .I8 w)
       ok (some i)
  else ok none

/-- [fulcrum::kernel::k8::saturate]:
    Source: 'src/kernel.rs', lines 356:12-364:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.saturate (w : Std.I16) : Result Std.I8 := do
  let i ← lift (IScalar.cast .I16 core.num.I8.MAX)
  if w > i
  then ok core.num.I8.MAX
  else
    let i1 ← lift (IScalar.cast .I16 core.num.I8.MIN)
    if w < i1
    then ok core.num.I8.MIN
    else ok (IScalar.cast .I8 w)

/-- [fulcrum::kernel::k8::wrap]:
    Source: 'src/kernel.rs', lines 368:12-370:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.wrap (w : Std.I16) : Result Std.I8 := do
  ok (IScalar.cast .I8 w)

/-- [fulcrum::kernel::k8::to_int]:
    Source: 'src/kernel.rs', lines 375:12-377:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.to_int (w : Std.I16) : Result Std.I8 := do
  let i ← w >>> 4#i32
  ok (IScalar.cast .I8 i)

/-- [fulcrum::kernel::k8::from_parts]:
    Source: 'src/kernel.rs', lines 381:12-383:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.from_parts (int : Std.I8) (frac : Std.U8) : Result Std.I16 := do
  let i ← lift (IScalar.cast .I16 int)
  let i1 ← i <<< 4#i32
  let i2 ← lift (UScalar.hcast .I16 frac)
  i1 + i2

/-- [fulcrum::kernel::k8::HALF]
    Source: 'src/kernel.rs', lines 336:12-336:46; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
@[global_simps, irreducible]
def kernel.k8.HALF : Result Std.I16 := do let i ← 4#i32 - 1#i32
                                          1#i16 <<< i

/-- [fulcrum::kernel::k8::round_frac]:
    Source: 'src/kernel.rs', lines 391:12-397:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.round_frac (p : Std.I16) : Result Std.I16 := do
  if core.num.I16.BITS = 128#u32
  then
    let i ← p >>> 4#i32
    let i1 ← 4#i32 - 1#i32
    let i2 ← p >>> i1
    let i3 ← lift (i2 &&& 1#i16)
    i + i3
  else let i ← kernel.k8.HALF
       let i1 ← p + i
       i1 >>> 4#i32

/-- [fulcrum::kernel::k8::mul]:
    Source: 'src/kernel.rs', lines 402:12-404:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.mul (a : Std.I8) (b : Std.I8) : Result Std.I16 := do
  let i ← lift (IScalar.cast .I16 a)
  let i1 ← lift (IScalar.cast .I16 b)
  let i2 ← i * i1
  kernel.k8.round_frac i2

/-- [fulcrum::kernel::k8::mul_add]:
    Source: 'src/kernel.rs', lines 412:12-414:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.mul_add
  (a : Std.I8) (b : Std.I8) (c : Std.I8) : Result Std.I16 := do
  let i ← kernel.k8.mul a b
  let i1 ← lift (IScalar.cast .I16 c)
  i + i1

/-- [fulcrum::kernel::k8::round_magnitude_div]:
    Source: 'src/kernel.rs', lines 421:12-429:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.round_magnitude_div
  (un : Std.U16) (ud : Std.U16) (negative : Bool) : Result Std.I16 := do
  let i ← un <<< 1#i32
  let i1 ← lift (UScalar.cast_fromBool .U16 negative)
  let i2 ← ud - i1
  let i3 ← i + i2
  let i4 ← ud <<< 1#i32
  let m ← i3 / i4
  let m1 ← lift (UScalar.hcast .I16 m)
  if negative
  then -. m1
  else ok m1

/-- [fulcrum::kernel::k8::mul_div]:
    Source: 'src/kernel.rs', lines 437:12-443:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.mul_div
  (a : Std.I8) (b : Std.I8) (c : Std.I8) : Result Std.I16 := do
  let i ← core.num.I8.unsigned_abs a
  let i1 ← lift (UScalar.cast .U16 i)
  let i2 ← core.num.I8.unsigned_abs b
  let i3 ← lift (UScalar.cast .U16 i2)
  let i4 ← i1 * i3
  let i5 ← core.num.I8.unsigned_abs c
  let i6 ← lift (UScalar.cast .U16 i5)
  kernel.k8.round_magnitude_div i4 i6 (((a < 0#i8) != (b < 0#i8)) != (c <
    0#i8))

/-- [fulcrum::kernel::k8::lerp]:
    Source: 'src/kernel.rs', lines 450:12-452:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.lerp
  (a : Std.I8) (b : Std.I8) (t : Std.I8) : Result Std.I16 := do
  let i ← lift (IScalar.cast .I16 a)
  let i1 ← lift (IScalar.cast .I16 b)
  let i2 ← lift (IScalar.cast .I16 a)
  let i3 ← i1 - i2
  let i4 ← lift (IScalar.cast .I16 t)
  let i5 ← i3 * i4
  let i6 ← kernel.k8.round_frac i5
  i + i6

/-- [fulcrum::kernel::k8::div]:
    Source: 'src/kernel.rs', lines 113:8-119:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.div (a : Std.I8) (b : Std.I8) : Result Std.I16 := do
  let i ← core.num.I8.unsigned_abs a
  let i1 ← lift (UScalar.cast .U16 i)
  let i2 ← i1 <<< 4#i32
  let i3 ← core.num.I8.unsigned_abs b
  let i4 ← lift (UScalar.cast .U16 i3)
  kernel.k8.round_magnitude_div i2 i4 ((a < 0#i8) != (b < 0#i8))

/-- [fulcrum::kernel::k8::div_int]:
    Source: 'src/kernel.rs', lines 123:8-129:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.div_int (a : Std.I8) (n : Std.I8) : Result Std.I16 := do
  let i ← core.num.I8.unsigned_abs a
  let i1 ← lift (UScalar.cast .U16 i)
  let i2 ← core.num.I8.unsigned_abs n
  let i3 ← lift (UScalar.cast .U16 i2)
  kernel.k8.round_magnitude_div i1 i3 ((a < 0#i8) != (n < 0#i8))

/-- [fulcrum::kernel::k8::div_total]:
    Source: 'src/kernel.rs', lines 461:12-469:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.div_total (a : Std.I8) (b : Std.I8) : Result Std.I16 := do
  if b = 0#i8
  then ok 0#i16
  else kernel.k8.div a b

/-- [fulcrum::kernel::sqrt_start]: loop body 1:
    Source: 'src/kernel.rs', lines 721:8-723:9 -/
@[rust_loop_body]
def kernel.sqrt_start_loop0_loop0.body
  (v : Std.U32) (s : Std.U32) : Result (ControlFlow Std.U32 Std.U32) := do
  let i ← s + 1#u32
  let i1 ← i * i
  if i1 <= v
  then ok (cont i)
  else ok (done s)

/-- [fulcrum::kernel::sqrt_start]: loop 1:
    Source: 'src/kernel.rs', lines 721:8-723:9 -/
@[rust_loop]
def kernel.sqrt_start_loop0_loop0
  (s : Std.U32) (v : Std.U32) : Result Std.U32 := do
  loop
    (fun s1 => kernel.sqrt_start_loop0_loop0.body v s1)
    s

/-- [fulcrum::kernel::sqrt_start]: loop body 0:
    Source: 'src/kernel.rs', lines 719:4-726:5 -/
@[rust_loop_body]
def kernel.sqrt_start_loop0.body
  (table : Array Std.U16 256#usize) (t : Std.Usize) (s : Std.U32) :
  Result (ControlFlow ((Array Std.U16 256#usize) × Std.Usize × Std.U32)
    (Array Std.U16 256#usize))
  := do
  if t < 256#usize
  then
    let i ← 2#usize * t
    let i1 ← i + 1#usize
    let i2 ← lift (UScalar.cast .U32 i1)
    let v ← i2 <<< 15#i32
    let s1 ← kernel.sqrt_start_loop0_loop0 s v
    let i3 ← lift (UScalar.cast .U16 s1)
    let a ← Array.update table t i3
    let t1 ← t + 1#usize
    ok (cont (a, t1, s1))
  else ok (done table)

/-- [fulcrum::kernel::sqrt_start]: loop 0:
    Source: 'src/kernel.rs', lines 719:4-726:5 -/
@[rust_loop]
def kernel.sqrt_start_loop0
  (table : Array Std.U16 256#usize) (t : Std.Usize) (s : Std.U32) :
  Result (Array Std.U16 256#usize)
  := do
  loop
    (fun (table1, t1, s1) => kernel.sqrt_start_loop0.body table1 t1 s1)
    (table, t, s)

/-- [fulcrum::kernel::sqrt_start]:
    Source: 'src/kernel.rs', lines 715:0-728:1 -/
def kernel.sqrt_start : Result (Array Std.U16 256#usize) := do
  let table := Array.repeat 256#usize 0#u16
  kernel.sqrt_start_loop0 table 0#usize 0#u32

/-- [fulcrum::kernel::SQRT_START]
    Source: 'src/kernel.rs', lines 686:0-686:44 -/
@[global_simps, irreducible]
def kernel.SQRT_START : Result (Array Std.U16 256#usize) := kernel.sqrt_start

/-- [fulcrum::kernel::k8::NEWTON_STEPS]
    Source: 'src/kernel.rs', lines 334:12-334:45; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
@[global_simps, irreducible] def kernel.k8.NEWTON_STEPS : Std.U32 := 1#u32

/-- [fulcrum::kernel::k8::isqrt]: loop body 0:
    Source: 'src/kernel.rs', lines 676:0-676:72 -/
@[rust_loop_body]
def kernel.k8.isqrt_loop0.body
  (n : Std.U16) (x : Std.U16) (i : Std.U32) :
  Result (ControlFlow (Std.U16 × Std.U32) Std.U16)
  := do
  if i < kernel.k8.NEWTON_STEPS
  then
    let i1 ← n / x
    let i2 ← x + i1
    let x1 ← i2 >>> 1#i32
    let i3 ← i + 1#u32
    ok (cont (x1, i3))
  else ok (done x)

/-- [fulcrum::kernel::k8::isqrt]: loop 0:
    Source: 'src/kernel.rs', lines 676:0-676:72 -/
@[rust_loop]
def kernel.k8.isqrt_loop0
  (n : Std.U16) (x : Std.U16) (i : Std.U32) : Result Std.U16 := do
  loop
    (fun (x1, i1) => kernel.k8.isqrt_loop0.body n x1 i1)
    (x, i)

/-- [fulcrum::kernel::k8::isqrt]: loop body 1:
    Source: 'src/kernel.rs', lines 676:0-676:72 -/
@[rust_loop_body]
def kernel.k8.isqrt_loop1.body
  (n : Std.U16) (x : Std.U16) : Result (ControlFlow Std.U16 Std.U16) := do
  let i ← x * x
  if i > n
  then let x1 ← x - 1#u16
       ok (cont x1)
  else ok (done x)

/-- [fulcrum::kernel::k8::isqrt]: loop 1:
    Source: 'src/kernel.rs', lines 676:0-676:72 -/
@[rust_loop]
def kernel.k8.isqrt_loop1 (n : Std.U16) (x : Std.U16) : Result Std.U16 := do
  loop
    (fun x1 => kernel.k8.isqrt_loop1.body n x1)
    x

/-- [fulcrum::kernel::k8::isqrt]:
    Source: 'src/kernel.rs', lines 494:12-511:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.isqrt (n : Std.U16) : Result Std.U16 := do
  if n < 2#u16
  then ok n
  else
    let i ← lift (core.num.U16.leading_zeros n)
    let bits ← core.num.U16.BITS - i
    let j ←
      if bits <= 8#u32
      then ok 0#u32
      else do
           let i1 ← bits - 7#u32
           i1 / 2#u32
    let a ← kernel.SQRT_START
    let i1 ← 2#u32 * j
    let i2 ← n >>> i1
    let i3 ← lift (UScalar.cast .Usize i2)
    let t ← Array.index_usize a i3
    let x ←
      if j >= 8#u32
      then do
           let i4 ← j - 8#u32
           t <<< i4
      else do
           let i4 ← 8#u32 - j
           t >>> i4
    let x1 ← kernel.k8.isqrt_loop0 n x 0#u32
    let i4 ← x1 * x1
    if i4 > n
    then let x2 ← x1 - 1#u16
         kernel.k8.isqrt_loop1 n x2
    else ok x1

/-- [fulcrum::kernel::k8::sqrt_round]:
    Source: 'src/kernel.rs', lines 517:12-520:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.sqrt_round (n : Std.U16) : Result Std.U16 := do
  let s ← kernel.k8.isqrt n
  let i ← s * s
  let i1 ← n - i
  let i2 ← lift (UScalar.cast_fromBool .U16 (i1 > s))
  s + i2

/-- [fulcrum::kernel::k8::sqrt]:
    Source: 'src/kernel.rs', lines 526:12-528:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.sqrt (a : Std.I8) : Result Std.I8 := do
  let i ← lift (IScalar.hcast .U16 a)
  let i1 ← i <<< 4#i32
  let i2 ← kernel.k8.sqrt_round i1
  ok (UScalar.hcast .I8 i2)

/-- [fulcrum::kernel::k8::rsqrt]:
    Source: 'src/kernel.rs', lines 538:12-543:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.rsqrt (a : Std.I8) : Result Std.I8 := do
  let ua ← lift (IScalar.hcast .U16 a)
  let i ← 3#i32 * 4#i32
  let i1 ← 1#u16 <<< i
  let i2 ← i1 / ua
  let s ← kernel.k8.isqrt i2
  let i3 ← 2#u16 * s
  let odd ← i3 + 1#u16
  let i4 ← odd * odd
  let i5 ← i4 * ua
  let i6 ← i + 2#i32
  let i7 ← 1#u16 <<< i6
  let i8 ← lift (UScalar.cast_fromBool .U16 (i5 < i7))
  let i9 ← s + i8
  ok (UScalar.hcast .I8 i9)

/-- [fulcrum::kernel::k8::hypot]:
    Source: 'src/kernel.rs', lines 549:12-553:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.hypot (a : Std.I8) (b : Std.I8) : Result Std.I16 := do
  let i ← core.num.I8.unsigned_abs a
  let ua ← lift (UScalar.cast .U16 i)
  let i1 ← core.num.I8.unsigned_abs b
  let ub ← lift (UScalar.cast .U16 i1)
  let i2 ← ua * ua
  let i3 ← ub * ub
  let i4 ← i2 + i3
  let i5 ← kernel.k8.sqrt_round i4
  ok (UScalar.hcast .I16 i5)

/-- [fulcrum::kernel::k8::det]:
    Source: 'src/kernel.rs', lines 562:12-564:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.det
  (a : Std.I8) (b : Std.I8) (c : Std.I8) (d : Std.I8) : Result Std.I16 := do
  let i ← lift (IScalar.cast .I16 a)
  let i1 ← lift (IScalar.cast .I16 d)
  let i2 ← i * i1
  let i3 ← lift (IScalar.cast .I16 b)
  let i4 ← lift (IScalar.cast .I16 c)
  let i5 ← i3 * i4
  let i6 ← i2 - i5
  kernel.k8.round_frac i6

/-- [fulcrum::kernel::k8::norm_sq]:
    Source: 'src/kernel.rs', lines 568:12-573:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.norm_sq
  (a : Std.I8) (b : Std.I8) (c : Std.I8) : Result Std.U128 := do
  let i ← core.num.I8.unsigned_abs a
  let ua ← lift (UScalar.cast .U128 i)
  let i1 ← core.num.I8.unsigned_abs b
  let ub ← lift (UScalar.cast .U128 i1)
  let i2 ← core.num.I8.unsigned_abs c
  let uc ← lift (UScalar.cast .U128 i2)
  let i3 ← ua * ua
  let i4 ← ub * ub
  let i5 ← i3 + i4
  let i6 ← uc * uc
  i5 + i6

/-- [fulcrum::kernel::k8::sq]:
    Source: 'src/kernel.rs', lines 577:12-580:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.sq (m : Std.I8) : Result Std.U128 := do
  let i ← core.num.I8.unsigned_abs m
  let um ← lift (UScalar.cast .U128 i)
  um * um

/-- [fulcrum::kernel::k8::scale_vec]:
    Source: 'src/kernel.rs', lines 217:8-224:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.scale_vec
  (a : Std.I8) (b : Std.I8) (c : Std.I8) (k : Std.I8) :
  Result (Array Std.I8 3#usize)
  := do
  let s ← kernel.k8.norm_sq a b c
  if s = 0#u128
  then ok (Array.make 3#usize [ a, b, c ])
  else
    let i ← lift (IScalar.cast .I64 a)
    let i1 ← lift (IScalar.cast .I64 b)
    let i2 ← lift (IScalar.cast .I64 c)
    let i3 ← lift (IScalar.hcast .U64 k)
    let i4 ← lift (UScalar.cast .U64 s)
    let r ← kernel.scale_narrow (Array.make 3#usize [ i, i1, i2 ]) i3 i4
    let i5 ← Array.index_usize r 0#usize
    let i6 ← lift (IScalar.cast .I8 i5)
    let i7 ← Array.index_usize r 1#usize
    let i8 ← lift (IScalar.cast .I8 i7)
    let i9 ← Array.index_usize r 2#usize
    let i10 ← lift (IScalar.cast .I8 i9)
    ok (Array.make 3#usize [ i6, i8, i10 ])

/-- [fulcrum::kernel::k8::cmp_length]:
    Source: 'src/kernel.rs', lines 587:12-597:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.cmp_length
  (a : Std.I8) (b : Std.I8) (c : Std.I8) (k : Std.I8) : Result Std.I8 := do
  let s ← kernel.k8.norm_sq a b c
  let k2 ← kernel.k8.sq k
  if s < k2
  then ok (-1)#i8
  else if s > k2
       then ok 1#i8
       else ok 0#i8

/-- [fulcrum::kernel::k8::hypot3]:
    Source: 'src/kernel.rs', lines 604:12-609:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.hypot3
  (a : Std.I8) (b : Std.I8) (c : Std.I8) : Result Std.I16 := do
  let i ← core.num.I8.unsigned_abs a
  let ua ← lift (UScalar.cast .U16 i)
  let i1 ← core.num.I8.unsigned_abs b
  let ub ← lift (UScalar.cast .U16 i1)
  let i2 ← core.num.I8.unsigned_abs c
  let uc ← lift (UScalar.cast .U16 i2)
  let i3 ← ua * ua
  let i4 ← ub * ub
  let i5 ← i3 + i4
  let i6 ← uc * uc
  let i7 ← i5 + i6
  let i8 ← kernel.k8.sqrt_round i7
  ok (UScalar.hcast .I16 i8)

/-- [fulcrum::kernel::k8::midpoint]:
    Source: 'src/kernel.rs', lines 613:12-615:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.midpoint (a : Std.I8) (b : Std.I8) : Result Std.I8 := do
  let i ← lift (a ||| b)
  let i1 ← lift (a ^^^ b)
  let i2 ← i1 >>> 1#i32
  i - i2

/-- [fulcrum::kernel::k8::shr]:
    Source: 'src/kernel.rs', lines 620:12-628:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.shr (a : Std.I8) (n : Std.U32) : Result Std.I8 := do
  if n = 0#u32
  then ok a
  else
    if n >= core.num.I8.BITS
    then ok 0#i8
    else
      let i ← a >>> n
      let i1 ← n - 1#u32
      let i2 ← a >>> i1
      let i3 ← lift (i2 &&& 1#i8)
      i + i3

/-- [fulcrum::kernel::k8::shl]:
    Source: 'src/kernel.rs', lines 633:12-640:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.shl (a : Std.I8) (n : Std.U32) : Result (Std.I8 × Bool) := do
  if n >= core.num.I8.BITS
  then ok (0#i8, a != 0#i8)
  else let r ← a <<< n
       let i ← r >>> n
       ok (r, i != a)

/-- [fulcrum::kernel::k8::ONE]
    Source: 'src/kernel.rs', lines 333:12-333:39; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
@[global_simps, irreducible]
def kernel.k8.ONE : Result Std.I16 := 1#i16 <<< 4#i32

/-- [fulcrum::kernel::k8::MASK]
    Source: 'src/kernel.rs', lines 335:12-335:40; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
@[global_simps, irreducible]
def kernel.k8.MASK : Result Std.I16 := do let i ← kernel.k8.ONE
                                          i - 1#i16

/-- [fulcrum::kernel::k8::ceil]:
    Source: 'src/kernel.rs', lines 644:12-646:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.ceil (a : Std.I8) : Result Std.I16 := do
  let i ← lift (IScalar.cast .I16 a)
  let i1 ← kernel.k8.MASK
  let i2 ← i + i1
  let i3 ← lift (~~~ i1)
  ok (i2 &&& i3)

/-- [fulcrum::kernel::k8::round_half_away]:
    Source: 'src/kernel.rs', lines 650:12-657:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.round_half_away (a : Std.I8) : Result Std.I16 := do
  let w ← lift (IScalar.cast .I16 a)
  if w >= 0#i16
  then
    let i ← kernel.k8.HALF
    let i1 ← w + i
    let i2 ← kernel.k8.MASK
    let i3 ← lift (~~~ i2)
    ok (i1 &&& i3)
  else
    let i ← kernel.k8.HALF
    let i1 ← i - w
    let i2 ← kernel.k8.MASK
    let i3 ← lift (~~~ i2)
    let i4 ← lift (i1 &&& i3)
    -. i4

/-- [fulcrum::kernel::k8::round_ties_even]:
    Source: 'src/kernel.rs', lines 661:12-671:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 676:0-676:72 -/
def kernel.k8.round_ties_even (a : Std.I8) : Result Std.I16 := do
  let w ← lift (IScalar.cast .I16 a)
  let i ← kernel.k8.MASK
  let i1 ← lift (~~~ i)
  let floor ← lift (w &&& i1)
  let frac ← lift (w &&& i)
  let i2 ← w >>> 4#i32
  let i3 ← lift (i2 &&& 1#i16)
  let i4 ← kernel.k8.HALF
  if frac > i4
  then let i5 ← kernel.k8.ONE
       floor + i5
  else
    if frac = i4
    then if i3 = 1#i16
         then let i5 ← kernel.k8.ONE
              floor + i5
         else ok floor
    else ok floor

/-- [fulcrum::kernel::k16::fits]:
    Source: 'src/kernel.rs', lines 340:12-342:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.fits (w : Std.I32) : Result Bool := do
  let i ← lift (IScalar.cast .I32 core.num.I16.MIN)
  if w >= i
  then let i1 ← lift (IScalar.cast .I32 core.num.I16.MAX)
       ok (w <= i1)
  else ok false

/-- [fulcrum::kernel::k16::narrow]:
    Source: 'src/kernel.rs', lines 346:12-352:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.narrow (w : Std.I32) : Result (Option Std.I16) := do
  let b ← kernel.k16.fits w
  if b
  then let i ← lift (IScalar.cast .I16 w)
       ok (some i)
  else ok none

/-- [fulcrum::kernel::k16::saturate]:
    Source: 'src/kernel.rs', lines 356:12-364:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.saturate (w : Std.I32) : Result Std.I16 := do
  let i ← lift (IScalar.cast .I32 core.num.I16.MAX)
  if w > i
  then ok core.num.I16.MAX
  else
    let i1 ← lift (IScalar.cast .I32 core.num.I16.MIN)
    if w < i1
    then ok core.num.I16.MIN
    else ok (IScalar.cast .I16 w)

/-- [fulcrum::kernel::k16::wrap]:
    Source: 'src/kernel.rs', lines 368:12-370:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.wrap (w : Std.I32) : Result Std.I16 := do
  ok (IScalar.cast .I16 w)

/-- [fulcrum::kernel::k16::to_int]:
    Source: 'src/kernel.rs', lines 375:12-377:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.to_int (w : Std.I32) : Result Std.I16 := do
  let i ← w >>> 8#i32
  ok (IScalar.cast .I16 i)

/-- [fulcrum::kernel::k16::from_parts]:
    Source: 'src/kernel.rs', lines 381:12-383:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.from_parts (int : Std.I8) (frac : Std.U8) : Result Std.I32 := do
  let i ← lift (IScalar.cast .I32 int)
  let i1 ← i <<< 8#i32
  let i2 ← lift (UScalar.hcast .I32 frac)
  i1 + i2

/-- [fulcrum::kernel::k16::HALF]
    Source: 'src/kernel.rs', lines 336:12-336:46; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
@[global_simps, irreducible]
def kernel.k16.HALF : Result Std.I32 := do let i ← 8#i32 - 1#i32
                                           1#i32 <<< i

/-- [fulcrum::kernel::k16::round_frac]:
    Source: 'src/kernel.rs', lines 391:12-397:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.round_frac (p : Std.I32) : Result Std.I32 := do
  if core.num.I32.BITS = 128#u32
  then
    let i ← p >>> 8#i32
    let i1 ← 8#i32 - 1#i32
    let i2 ← p >>> i1
    let i3 ← lift (i2 &&& 1#i32)
    i + i3
  else let i ← kernel.k16.HALF
       let i1 ← p + i
       i1 >>> 8#i32

/-- [fulcrum::kernel::k16::mul]:
    Source: 'src/kernel.rs', lines 402:12-404:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.mul (a : Std.I16) (b : Std.I16) : Result Std.I32 := do
  let i ← lift (IScalar.cast .I32 a)
  let i1 ← lift (IScalar.cast .I32 b)
  let i2 ← i * i1
  kernel.k16.round_frac i2

/-- [fulcrum::kernel::k16::mul_add]:
    Source: 'src/kernel.rs', lines 412:12-414:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.mul_add
  (a : Std.I16) (b : Std.I16) (c : Std.I16) : Result Std.I32 := do
  let i ← kernel.k16.mul a b
  let i1 ← lift (IScalar.cast .I32 c)
  i + i1

/-- [fulcrum::kernel::k16::round_magnitude_div]:
    Source: 'src/kernel.rs', lines 421:12-429:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.round_magnitude_div
  (un : Std.U32) (ud : Std.U32) (negative : Bool) : Result Std.I32 := do
  let i ← un <<< 1#i32
  let i1 ← lift (UScalar.cast_fromBool .U32 negative)
  let i2 ← ud - i1
  let i3 ← i + i2
  let i4 ← ud <<< 1#i32
  let m ← i3 / i4
  let m1 ← lift (UScalar.hcast .I32 m)
  if negative
  then -. m1
  else ok m1

/-- [fulcrum::kernel::k16::mul_div]:
    Source: 'src/kernel.rs', lines 437:12-443:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.mul_div
  (a : Std.I16) (b : Std.I16) (c : Std.I16) : Result Std.I32 := do
  let i ← core.num.I16.unsigned_abs a
  let i1 ← lift (UScalar.cast .U32 i)
  let i2 ← core.num.I16.unsigned_abs b
  let i3 ← lift (UScalar.cast .U32 i2)
  let i4 ← i1 * i3
  let i5 ← core.num.I16.unsigned_abs c
  let i6 ← lift (UScalar.cast .U32 i5)
  kernel.k16.round_magnitude_div i4 i6 (((a < 0#i16) != (b < 0#i16)) != (c <
    0#i16))

/-- [fulcrum::kernel::k16::lerp]:
    Source: 'src/kernel.rs', lines 450:12-452:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.lerp
  (a : Std.I16) (b : Std.I16) (t : Std.I16) : Result Std.I32 := do
  let i ← lift (IScalar.cast .I32 a)
  let i1 ← lift (IScalar.cast .I32 b)
  let i2 ← lift (IScalar.cast .I32 a)
  let i3 ← i1 - i2
  let i4 ← lift (IScalar.cast .I32 t)
  let i5 ← i3 * i4
  let i6 ← kernel.k16.round_frac i5
  i + i6

/-- [fulcrum::kernel::k16::round_div]:
    Source: 'src/kernel.rs', lines 91:8-96:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.round_div (n : Std.I32) (d : Std.I32) : Result Std.I32 := do
  let i ← core.num.I32.unsigned_abs d
  let ud ← lift (UScalar.hcast .I32 i)
  let sd ← lift (IScalar.cast_fromBool .I32 (d < 0#i32))
  let bias ← if n < 0#i32
               then do
                    let i1 ← 1#i32 - sd
                    i1 - ud
               else ud - sd
  let i1 ← n <<< 1#i32
  let i2 ← i1 + bias
  let i3 ← d <<< 1#i32
  i2 / i3

/-- [fulcrum::kernel::k16::div]:
    Source: 'src/kernel.rs', lines 100:8-102:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.div (a : Std.I16) (b : Std.I16) : Result Std.I32 := do
  let i ← lift (IScalar.cast .I32 a)
  let i1 ← i <<< 8#i32
  let i2 ← lift (IScalar.cast .I32 b)
  kernel.k16.round_div i1 i2

/-- [fulcrum::kernel::k16::div_int]:
    Source: 'src/kernel.rs', lines 106:8-108:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.div_int (a : Std.I16) (n : Std.I16) : Result Std.I32 := do
  let i ← lift (IScalar.cast .I32 a)
  let i1 ← lift (IScalar.cast .I32 n)
  kernel.k16.round_div i i1

/-- [fulcrum::kernel::k16::div_total]:
    Source: 'src/kernel.rs', lines 461:12-469:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.div_total (a : Std.I16) (b : Std.I16) : Result Std.I32 := do
  let i ← lift (IScalar.cast_fromBool .I16 (b = 0#i16))
  let i1 ← lift (b ||| i)
  kernel.k16.div a i1

/-- [fulcrum::kernel::k16::NEWTON_STEPS]
    Source: 'src/kernel.rs', lines 334:12-334:45; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
@[global_simps, irreducible] def kernel.k16.NEWTON_STEPS : Std.U32 := 1#u32

/-- [fulcrum::kernel::k16::isqrt]: loop body 0:
    Source: 'src/kernel.rs', lines 677:0-677:70 -/
@[rust_loop_body]
def kernel.k16.isqrt_loop0.body
  (n : Std.U32) (x : Std.U32) (i : Std.U32) :
  Result (ControlFlow (Std.U32 × Std.U32) Std.U32)
  := do
  if i < kernel.k16.NEWTON_STEPS
  then
    let i1 ← n / x
    let i2 ← x + i1
    let x1 ← i2 >>> 1#i32
    let i3 ← i + 1#u32
    ok (cont (x1, i3))
  else ok (done x)

/-- [fulcrum::kernel::k16::isqrt]: loop 0:
    Source: 'src/kernel.rs', lines 677:0-677:70 -/
@[rust_loop]
def kernel.k16.isqrt_loop0
  (n : Std.U32) (x : Std.U32) (i : Std.U32) : Result Std.U32 := do
  loop
    (fun (x1, i1) => kernel.k16.isqrt_loop0.body n x1 i1)
    (x, i)

/-- [fulcrum::kernel::k16::isqrt]: loop body 1:
    Source: 'src/kernel.rs', lines 677:0-677:70 -/
@[rust_loop_body]
def kernel.k16.isqrt_loop1.body
  (n : Std.U32) (x : Std.U32) : Result (ControlFlow Std.U32 Std.U32) := do
  let i ← x * x
  if i > n
  then let x1 ← x - 1#u32
       ok (cont x1)
  else ok (done x)

/-- [fulcrum::kernel::k16::isqrt]: loop 1:
    Source: 'src/kernel.rs', lines 677:0-677:70 -/
@[rust_loop]
def kernel.k16.isqrt_loop1 (n : Std.U32) (x : Std.U32) : Result Std.U32 := do
  loop
    (fun x1 => kernel.k16.isqrt_loop1.body n x1)
    x

/-- [fulcrum::kernel::k16::isqrt]:
    Source: 'src/kernel.rs', lines 494:12-511:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.isqrt (n : Std.U32) : Result Std.U32 := do
  if n < 2#u32
  then ok n
  else
    let i ← lift (core.num.U32.leading_zeros n)
    let bits ← core.num.U32.BITS - i
    let j ←
      if bits <= 8#u32
      then ok 0#u32
      else do
           let i1 ← bits - 7#u32
           i1 / 2#u32
    let a ← kernel.SQRT_START
    let i1 ← 2#u32 * j
    let i2 ← n >>> i1
    let i3 ← lift (UScalar.cast .Usize i2)
    let i4 ← Array.index_usize a i3
    let t ← lift (UScalar.cast .U32 i4)
    let x ←
      if j >= 8#u32
      then do
           let i5 ← j - 8#u32
           t <<< i5
      else do
           let i5 ← 8#u32 - j
           t >>> i5
    let x1 ← kernel.k16.isqrt_loop0 n x 0#u32
    let i5 ← x1 * x1
    if i5 > n
    then let x2 ← x1 - 1#u32
         kernel.k16.isqrt_loop1 n x2
    else ok x1

/-- [fulcrum::kernel::k16::sqrt_round]:
    Source: 'src/kernel.rs', lines 517:12-520:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.sqrt_round (n : Std.U32) : Result Std.U32 := do
  let s ← kernel.k16.isqrt n
  let i ← s * s
  let i1 ← n - i
  let i2 ← lift (UScalar.cast_fromBool .U32 (i1 > s))
  s + i2

/-- [fulcrum::kernel::k16::sqrt]:
    Source: 'src/kernel.rs', lines 526:12-528:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.sqrt (a : Std.I16) : Result Std.I16 := do
  let i ← lift (IScalar.hcast .U32 a)
  let i1 ← i <<< 8#i32
  let i2 ← kernel.k16.sqrt_round i1
  ok (UScalar.hcast .I16 i2)

/-- [fulcrum::kernel::k16::rsqrt]:
    Source: 'src/kernel.rs', lines 538:12-543:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.rsqrt (a : Std.I16) : Result Std.I16 := do
  let ua ← lift (IScalar.hcast .U32 a)
  let i ← 3#i32 * 8#i32
  let i1 ← 1#u32 <<< i
  let i2 ← i1 / ua
  let s ← kernel.k16.isqrt i2
  let i3 ← 2#u32 * s
  let odd ← i3 + 1#u32
  let i4 ← odd * odd
  let i5 ← i4 * ua
  let i6 ← i + 2#i32
  let i7 ← 1#u32 <<< i6
  let i8 ← lift (UScalar.cast_fromBool .U32 (i5 < i7))
  let i9 ← s + i8
  ok (UScalar.hcast .I16 i9)

/-- [fulcrum::kernel::k16::hypot]:
    Source: 'src/kernel.rs', lines 549:12-553:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.hypot (a : Std.I16) (b : Std.I16) : Result Std.I32 := do
  let i ← core.num.I16.unsigned_abs a
  let ua ← lift (UScalar.cast .U32 i)
  let i1 ← core.num.I16.unsigned_abs b
  let ub ← lift (UScalar.cast .U32 i1)
  let i2 ← ua * ua
  let i3 ← ub * ub
  let i4 ← i2 + i3
  let i5 ← kernel.k16.sqrt_round i4
  ok (UScalar.hcast .I32 i5)

/-- [fulcrum::kernel::k16::det]:
    Source: 'src/kernel.rs', lines 562:12-564:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.det
  (a : Std.I16) (b : Std.I16) (c : Std.I16) (d : Std.I16) :
  Result Std.I32
  := do
  let i ← lift (IScalar.cast .I32 a)
  let i1 ← lift (IScalar.cast .I32 d)
  let i2 ← i * i1
  let i3 ← lift (IScalar.cast .I32 b)
  let i4 ← lift (IScalar.cast .I32 c)
  let i5 ← i3 * i4
  let i6 ← i2 - i5
  kernel.k16.round_frac i6

/-- [fulcrum::kernel::k16::norm_sq]:
    Source: 'src/kernel.rs', lines 568:12-573:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.norm_sq
  (a : Std.I16) (b : Std.I16) (c : Std.I16) : Result Std.U128 := do
  let i ← core.num.I16.unsigned_abs a
  let ua ← lift (UScalar.cast .U128 i)
  let i1 ← core.num.I16.unsigned_abs b
  let ub ← lift (UScalar.cast .U128 i1)
  let i2 ← core.num.I16.unsigned_abs c
  let uc ← lift (UScalar.cast .U128 i2)
  let i3 ← ua * ua
  let i4 ← ub * ub
  let i5 ← i3 + i4
  let i6 ← uc * uc
  i5 + i6

/-- [fulcrum::kernel::k16::sq]:
    Source: 'src/kernel.rs', lines 577:12-580:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.sq (m : Std.I16) : Result Std.U128 := do
  let i ← core.num.I16.unsigned_abs m
  let um ← lift (UScalar.cast .U128 i)
  um * um

/-- [fulcrum::kernel::k16::scale_vec]:
    Source: 'src/kernel.rs', lines 217:8-224:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.scale_vec
  (a : Std.I16) (b : Std.I16) (c : Std.I16) (k : Std.I16) :
  Result (Array Std.I16 3#usize)
  := do
  let s ← kernel.k16.norm_sq a b c
  if s = 0#u128
  then ok (Array.make 3#usize [ a, b, c ])
  else
    let i ← lift (IScalar.cast .I64 a)
    let i1 ← lift (IScalar.cast .I64 b)
    let i2 ← lift (IScalar.cast .I64 c)
    let i3 ← lift (IScalar.hcast .U64 k)
    let i4 ← lift (UScalar.cast .U64 s)
    let r ← kernel.scale_narrow (Array.make 3#usize [ i, i1, i2 ]) i3 i4
    let i5 ← Array.index_usize r 0#usize
    let i6 ← lift (IScalar.cast .I16 i5)
    let i7 ← Array.index_usize r 1#usize
    let i8 ← lift (IScalar.cast .I16 i7)
    let i9 ← Array.index_usize r 2#usize
    let i10 ← lift (IScalar.cast .I16 i9)
    ok (Array.make 3#usize [ i6, i8, i10 ])

/-- [fulcrum::kernel::k16::cmp_length]:
    Source: 'src/kernel.rs', lines 587:12-597:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.cmp_length
  (a : Std.I16) (b : Std.I16) (c : Std.I16) (k : Std.I16) : Result Std.I8 := do
  let s ← kernel.k16.norm_sq a b c
  let k2 ← kernel.k16.sq k
  if s < k2
  then ok (-1)#i8
  else if s > k2
       then ok 1#i8
       else ok 0#i8

/-- [fulcrum::kernel::k16::hypot3]:
    Source: 'src/kernel.rs', lines 604:12-609:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.hypot3
  (a : Std.I16) (b : Std.I16) (c : Std.I16) : Result Std.I32 := do
  let i ← core.num.I16.unsigned_abs a
  let ua ← lift (UScalar.cast .U32 i)
  let i1 ← core.num.I16.unsigned_abs b
  let ub ← lift (UScalar.cast .U32 i1)
  let i2 ← core.num.I16.unsigned_abs c
  let uc ← lift (UScalar.cast .U32 i2)
  let i3 ← ua * ua
  let i4 ← ub * ub
  let i5 ← i3 + i4
  let i6 ← uc * uc
  let i7 ← i5 + i6
  let i8 ← kernel.k16.sqrt_round i7
  ok (UScalar.hcast .I32 i8)

/-- [fulcrum::kernel::k16::midpoint]:
    Source: 'src/kernel.rs', lines 613:12-615:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.midpoint (a : Std.I16) (b : Std.I16) : Result Std.I16 := do
  let i ← lift (a ||| b)
  let i1 ← lift (a ^^^ b)
  let i2 ← i1 >>> 1#i32
  i - i2

/-- [fulcrum::kernel::k16::shr]:
    Source: 'src/kernel.rs', lines 620:12-628:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.shr (a : Std.I16) (n : Std.U32) : Result Std.I16 := do
  if n = 0#u32
  then ok a
  else
    if n >= core.num.I16.BITS
    then ok 0#i16
    else
      let i ← a >>> n
      let i1 ← n - 1#u32
      let i2 ← a >>> i1
      let i3 ← lift (i2 &&& 1#i16)
      i + i3

/-- [fulcrum::kernel::k16::shl]:
    Source: 'src/kernel.rs', lines 633:12-640:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.shl (a : Std.I16) (n : Std.U32) : Result (Std.I16 × Bool) := do
  if n >= core.num.I16.BITS
  then ok (0#i16, a != 0#i16)
  else let r ← a <<< n
       let i ← r >>> n
       ok (r, i != a)

/-- [fulcrum::kernel::k16::ONE]
    Source: 'src/kernel.rs', lines 333:12-333:39; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
@[global_simps, irreducible]
def kernel.k16.ONE : Result Std.I32 := 1#i32 <<< 8#i32

/-- [fulcrum::kernel::k16::MASK]
    Source: 'src/kernel.rs', lines 335:12-335:40; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
@[global_simps, irreducible]
def kernel.k16.MASK : Result Std.I32 := do let i ← kernel.k16.ONE
                                           i - 1#i32

/-- [fulcrum::kernel::k16::ceil]:
    Source: 'src/kernel.rs', lines 644:12-646:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.ceil (a : Std.I16) : Result Std.I32 := do
  let i ← lift (IScalar.cast .I32 a)
  let i1 ← kernel.k16.MASK
  let i2 ← i + i1
  let i3 ← lift (~~~ i1)
  ok (i2 &&& i3)

/-- [fulcrum::kernel::k16::round_half_away]:
    Source: 'src/kernel.rs', lines 650:12-657:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.round_half_away (a : Std.I16) : Result Std.I32 := do
  let w ← lift (IScalar.cast .I32 a)
  if w >= 0#i32
  then
    let i ← kernel.k16.HALF
    let i1 ← w + i
    let i2 ← kernel.k16.MASK
    let i3 ← lift (~~~ i2)
    ok (i1 &&& i3)
  else
    let i ← kernel.k16.HALF
    let i1 ← i - w
    let i2 ← kernel.k16.MASK
    let i3 ← lift (~~~ i2)
    let i4 ← lift (i1 &&& i3)
    -. i4

/-- [fulcrum::kernel::k16::round_ties_even]:
    Source: 'src/kernel.rs', lines 661:12-671:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 677:0-677:70 -/
def kernel.k16.round_ties_even (a : Std.I16) : Result Std.I32 := do
  let w ← lift (IScalar.cast .I32 a)
  let i ← kernel.k16.MASK
  let i1 ← lift (~~~ i)
  let floor ← lift (w &&& i1)
  let frac ← lift (w &&& i)
  let i2 ← w >>> 8#i32
  let i3 ← lift (i2 &&& 1#i32)
  let i4 ← kernel.k16.HALF
  if frac > i4
  then let i5 ← kernel.k16.ONE
       floor + i5
  else
    if frac = i4
    then if i3 = 1#i32
         then let i5 ← kernel.k16.ONE
              floor + i5
         else ok floor
    else ok floor

/-- [fulcrum::kernel::k32::fits]:
    Source: 'src/kernel.rs', lines 340:12-342:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.fits (w : Std.I64) : Result Bool := do
  let i ← lift (IScalar.cast .I64 core.num.I32.MIN)
  if w >= i
  then let i1 ← lift (IScalar.cast .I64 core.num.I32.MAX)
       ok (w <= i1)
  else ok false

/-- [fulcrum::kernel::k32::narrow]:
    Source: 'src/kernel.rs', lines 346:12-352:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.narrow (w : Std.I64) : Result (Option Std.I32) := do
  let b ← kernel.k32.fits w
  if b
  then let i ← lift (IScalar.cast .I32 w)
       ok (some i)
  else ok none

/-- [fulcrum::kernel::k32::saturate]:
    Source: 'src/kernel.rs', lines 356:12-364:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.saturate (w : Std.I64) : Result Std.I32 := do
  let i ← lift (IScalar.cast .I64 core.num.I32.MAX)
  if w > i
  then ok core.num.I32.MAX
  else
    let i1 ← lift (IScalar.cast .I64 core.num.I32.MIN)
    if w < i1
    then ok core.num.I32.MIN
    else ok (IScalar.cast .I32 w)

/-- [fulcrum::kernel::k32::wrap]:
    Source: 'src/kernel.rs', lines 368:12-370:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.wrap (w : Std.I64) : Result Std.I32 := do
  ok (IScalar.cast .I32 w)

/-- [fulcrum::kernel::k32::to_int]:
    Source: 'src/kernel.rs', lines 375:12-377:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.to_int (w : Std.I64) : Result Std.I32 := do
  let i ← w >>> 16#i32
  ok (IScalar.cast .I32 i)

/-- [fulcrum::kernel::k32::from_parts]:
    Source: 'src/kernel.rs', lines 381:12-383:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.from_parts
  (int : Std.I16) (frac : Std.U16) : Result Std.I64 := do
  let i ← lift (IScalar.cast .I64 int)
  let i1 ← i <<< 16#i32
  let i2 ← lift (UScalar.hcast .I64 frac)
  i1 + i2

/-- [fulcrum::kernel::k32::HALF]
    Source: 'src/kernel.rs', lines 336:12-336:46; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
@[global_simps, irreducible]
def kernel.k32.HALF : Result Std.I64 := do let i ← 16#i32 - 1#i32
                                           1#i64 <<< i

/-- [fulcrum::kernel::k32::round_frac]:
    Source: 'src/kernel.rs', lines 391:12-397:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.round_frac (p : Std.I64) : Result Std.I64 := do
  if core.num.I64.BITS = 128#u32
  then
    let i ← p >>> 16#i32
    let i1 ← 16#i32 - 1#i32
    let i2 ← p >>> i1
    let i3 ← lift (i2 &&& 1#i64)
    i + i3
  else let i ← kernel.k32.HALF
       let i1 ← p + i
       i1 >>> 16#i32

/-- [fulcrum::kernel::k32::mul]:
    Source: 'src/kernel.rs', lines 402:12-404:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.mul (a : Std.I32) (b : Std.I32) : Result Std.I64 := do
  let i ← lift (IScalar.cast .I64 a)
  let i1 ← lift (IScalar.cast .I64 b)
  let i2 ← i * i1
  kernel.k32.round_frac i2

/-- [fulcrum::kernel::k32::mul_add]:
    Source: 'src/kernel.rs', lines 412:12-414:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.mul_add
  (a : Std.I32) (b : Std.I32) (c : Std.I32) : Result Std.I64 := do
  let i ← kernel.k32.mul a b
  let i1 ← lift (IScalar.cast .I64 c)
  i + i1

/-- [fulcrum::kernel::k32::round_magnitude_div]:
    Source: 'src/kernel.rs', lines 421:12-429:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.round_magnitude_div
  (un : Std.U64) (ud : Std.U64) (negative : Bool) : Result Std.I64 := do
  let i ← un <<< 1#i32
  let i1 ← lift (UScalar.cast_fromBool .U64 negative)
  let i2 ← ud - i1
  let i3 ← i + i2
  let i4 ← ud <<< 1#i32
  let m ← i3 / i4
  let m1 ← lift (UScalar.hcast .I64 m)
  if negative
  then -. m1
  else ok m1

/-- [fulcrum::kernel::k32::mul_div]:
    Source: 'src/kernel.rs', lines 437:12-443:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.mul_div
  (a : Std.I32) (b : Std.I32) (c : Std.I32) : Result Std.I64 := do
  let i ← core.num.I32.unsigned_abs a
  let i1 ← lift (UScalar.cast .U64 i)
  let i2 ← core.num.I32.unsigned_abs b
  let i3 ← lift (UScalar.cast .U64 i2)
  let i4 ← i1 * i3
  let i5 ← core.num.I32.unsigned_abs c
  let i6 ← lift (UScalar.cast .U64 i5)
  kernel.k32.round_magnitude_div i4 i6 (((a < 0#i32) != (b < 0#i32)) != (c <
    0#i32))

/-- [fulcrum::kernel::k32::lerp]:
    Source: 'src/kernel.rs', lines 450:12-452:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.lerp
  (a : Std.I32) (b : Std.I32) (t : Std.I32) : Result Std.I64 := do
  let i ← lift (IScalar.cast .I64 a)
  let i1 ← lift (IScalar.cast .I64 b)
  let i2 ← lift (IScalar.cast .I64 a)
  let i3 ← i1 - i2
  let i4 ← lift (IScalar.cast .I64 t)
  let i5 ← i3 * i4
  let i6 ← kernel.k32.round_frac i5
  i + i6

/-- [fulcrum::kernel::k32::round_div]:
    Source: 'src/kernel.rs', lines 91:8-96:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.round_div (n : Std.I64) (d : Std.I64) : Result Std.I64 := do
  let i ← core.num.I64.unsigned_abs d
  let ud ← lift (UScalar.hcast .I64 i)
  let sd ← lift (IScalar.cast_fromBool .I64 (d < 0#i64))
  let bias ← if n < 0#i64
               then do
                    let i1 ← 1#i64 - sd
                    i1 - ud
               else ud - sd
  let i1 ← n <<< 1#i32
  let i2 ← i1 + bias
  let i3 ← d <<< 1#i32
  i2 / i3

/-- [fulcrum::kernel::k32::div]:
    Source: 'src/kernel.rs', lines 100:8-102:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.div (a : Std.I32) (b : Std.I32) : Result Std.I64 := do
  let i ← lift (IScalar.cast .I64 a)
  let i1 ← i <<< 16#i32
  let i2 ← lift (IScalar.cast .I64 b)
  kernel.k32.round_div i1 i2

/-- [fulcrum::kernel::k32::div_int]:
    Source: 'src/kernel.rs', lines 106:8-108:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.div_int (a : Std.I32) (n : Std.I32) : Result Std.I64 := do
  let i ← lift (IScalar.cast .I64 a)
  let i1 ← lift (IScalar.cast .I64 n)
  kernel.k32.round_div i i1

/-- [fulcrum::kernel::k32::div_total]:
    Source: 'src/kernel.rs', lines 461:12-469:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.div_total (a : Std.I32) (b : Std.I32) : Result Std.I64 := do
  if b = 0#i32
  then ok 0#i64
  else kernel.k32.div a b

/-- [fulcrum::kernel::k32::sqrt_round]:
    Source: 'src/kernel.rs', lines 517:12-520:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.sqrt_round (n : Std.U64) : Result Std.U64 := do
  let s ← kernel.k32.isqrt n
  let i ← s * s
  let i1 ← n - i
  let i2 ← lift (UScalar.cast_fromBool .U64 (i1 > s))
  s + i2

/-- [fulcrum::kernel::k32::sqrt]:
    Source: 'src/kernel.rs', lines 526:12-528:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.sqrt (a : Std.I32) : Result Std.I32 := do
  let i ← lift (IScalar.hcast .U64 a)
  let i1 ← i <<< 16#i32
  let i2 ← kernel.k32.sqrt_round i1
  ok (UScalar.hcast .I32 i2)

/-- [fulcrum::kernel::k32::rsqrt]:
    Source: 'src/kernel.rs', lines 538:12-543:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.rsqrt (a : Std.I32) : Result Std.I32 := do
  let ua ← lift (IScalar.hcast .U64 a)
  let i ← 3#i32 * 16#i32
  let i1 ← 1#u64 <<< i
  let i2 ← i1 / ua
  let s ← kernel.k32.isqrt i2
  let i3 ← 2#u64 * s
  let odd ← i3 + 1#u64
  let i4 ← odd * odd
  let i5 ← i4 * ua
  let i6 ← i + 2#i32
  let i7 ← 1#u64 <<< i6
  let i8 ← lift (UScalar.cast_fromBool .U64 (i5 < i7))
  let i9 ← s + i8
  ok (UScalar.hcast .I32 i9)

/-- [fulcrum::kernel::k32::hypot]:
    Source: 'src/kernel.rs', lines 549:12-553:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.hypot (a : Std.I32) (b : Std.I32) : Result Std.I64 := do
  let i ← core.num.I32.unsigned_abs a
  let ua ← lift (UScalar.cast .U64 i)
  let i1 ← core.num.I32.unsigned_abs b
  let ub ← lift (UScalar.cast .U64 i1)
  let i2 ← ua * ua
  let i3 ← ub * ub
  let i4 ← i2 + i3
  let i5 ← kernel.k32.sqrt_round i4
  ok (UScalar.hcast .I64 i5)

/-- [fulcrum::kernel::k32::det]:
    Source: 'src/kernel.rs', lines 562:12-564:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.det
  (a : Std.I32) (b : Std.I32) (c : Std.I32) (d : Std.I32) :
  Result Std.I64
  := do
  let i ← lift (IScalar.cast .I64 a)
  let i1 ← lift (IScalar.cast .I64 d)
  let i2 ← i * i1
  let i3 ← lift (IScalar.cast .I64 b)
  let i4 ← lift (IScalar.cast .I64 c)
  let i5 ← i3 * i4
  let i6 ← i2 - i5
  kernel.k32.round_frac i6

/-- [fulcrum::kernel::k32::norm_sq]:
    Source: 'src/kernel.rs', lines 568:12-573:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.norm_sq
  (a : Std.I32) (b : Std.I32) (c : Std.I32) : Result Std.U128 := do
  let i ← core.num.I32.unsigned_abs a
  let ua ← lift (UScalar.cast .U128 i)
  let i1 ← core.num.I32.unsigned_abs b
  let ub ← lift (UScalar.cast .U128 i1)
  let i2 ← core.num.I32.unsigned_abs c
  let uc ← lift (UScalar.cast .U128 i2)
  let i3 ← ua * ua
  let i4 ← ub * ub
  let i5 ← i3 + i4
  let i6 ← uc * uc
  i5 + i6

/-- [fulcrum::kernel::k32::sq]:
    Source: 'src/kernel.rs', lines 577:12-580:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.sq (m : Std.I32) : Result Std.U128 := do
  let i ← core.num.I32.unsigned_abs m
  let um ← lift (UScalar.cast .U128 i)
  um * um

/-- [fulcrum::kernel::k32::scale_vec]:
    Source: 'src/kernel.rs', lines 217:8-224:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.scale_vec
  (a : Std.I32) (b : Std.I32) (c : Std.I32) (k : Std.I32) :
  Result (Array Std.I32 3#usize)
  := do
  let s ← kernel.k32.norm_sq a b c
  if s = 0#u128
  then ok (Array.make 3#usize [ a, b, c ])
  else
    let i ← lift (IScalar.cast .I64 a)
    let i1 ← lift (IScalar.cast .I64 b)
    let i2 ← lift (IScalar.cast .I64 c)
    let i3 ← lift (IScalar.hcast .U64 k)
    let i4 ← lift (UScalar.cast .U64 s)
    let r ← kernel.scale_narrow (Array.make 3#usize [ i, i1, i2 ]) i3 i4
    let i5 ← Array.index_usize r 0#usize
    let i6 ← lift (IScalar.cast .I32 i5)
    let i7 ← Array.index_usize r 1#usize
    let i8 ← lift (IScalar.cast .I32 i7)
    let i9 ← Array.index_usize r 2#usize
    let i10 ← lift (IScalar.cast .I32 i9)
    ok (Array.make 3#usize [ i6, i8, i10 ])

/-- [fulcrum::kernel::k32::cmp_length]:
    Source: 'src/kernel.rs', lines 587:12-597:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.cmp_length
  (a : Std.I32) (b : Std.I32) (c : Std.I32) (k : Std.I32) : Result Std.I8 := do
  let s ← kernel.k32.norm_sq a b c
  let k2 ← kernel.k32.sq k
  if s < k2
  then ok (-1)#i8
  else if s > k2
       then ok 1#i8
       else ok 0#i8

/-- [fulcrum::kernel::k32::hypot3]:
    Source: 'src/kernel.rs', lines 604:12-609:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.hypot3
  (a : Std.I32) (b : Std.I32) (c : Std.I32) : Result Std.I64 := do
  let i ← core.num.I32.unsigned_abs a
  let ua ← lift (UScalar.cast .U64 i)
  let i1 ← core.num.I32.unsigned_abs b
  let ub ← lift (UScalar.cast .U64 i1)
  let i2 ← core.num.I32.unsigned_abs c
  let uc ← lift (UScalar.cast .U64 i2)
  let i3 ← ua * ua
  let i4 ← ub * ub
  let i5 ← i3 + i4
  let i6 ← uc * uc
  let i7 ← i5 + i6
  let i8 ← kernel.k32.sqrt_round i7
  ok (UScalar.hcast .I64 i8)

/-- [fulcrum::kernel::k32::midpoint]:
    Source: 'src/kernel.rs', lines 613:12-615:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.midpoint (a : Std.I32) (b : Std.I32) : Result Std.I32 := do
  let i ← lift (a ||| b)
  let i1 ← lift (a ^^^ b)
  let i2 ← i1 >>> 1#i32
  i - i2

/-- [fulcrum::kernel::k32::shr]:
    Source: 'src/kernel.rs', lines 620:12-628:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.shr (a : Std.I32) (n : Std.U32) : Result Std.I32 := do
  if n = 0#u32
  then ok a
  else
    if n >= core.num.I32.BITS
    then ok 0#i32
    else
      let i ← a >>> n
      let i1 ← n - 1#u32
      let i2 ← a >>> i1
      let i3 ← lift (i2 &&& 1#i32)
      i + i3

/-- [fulcrum::kernel::k32::shl]:
    Source: 'src/kernel.rs', lines 633:12-640:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.shl (a : Std.I32) (n : Std.U32) : Result (Std.I32 × Bool) := do
  if n >= core.num.I32.BITS
  then ok (0#i32, a != 0#i32)
  else let r ← a <<< n
       let i ← r >>> n
       ok (r, i != a)

/-- [fulcrum::kernel::k32::ONE]
    Source: 'src/kernel.rs', lines 333:12-333:39; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
@[global_simps, irreducible]
def kernel.k32.ONE : Result Std.I64 := 1#i64 <<< 16#i32

/-- [fulcrum::kernel::k32::MASK]
    Source: 'src/kernel.rs', lines 335:12-335:40; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
@[global_simps, irreducible]
def kernel.k32.MASK : Result Std.I64 := do let i ← kernel.k32.ONE
                                           i - 1#i64

/-- [fulcrum::kernel::k32::ceil]:
    Source: 'src/kernel.rs', lines 644:12-646:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.ceil (a : Std.I32) : Result Std.I64 := do
  let i ← lift (IScalar.cast .I64 a)
  let i1 ← kernel.k32.MASK
  let i2 ← i + i1
  let i3 ← lift (~~~ i1)
  ok (i2 &&& i3)

/-- [fulcrum::kernel::k32::round_half_away]:
    Source: 'src/kernel.rs', lines 650:12-657:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.round_half_away (a : Std.I32) : Result Std.I64 := do
  let w ← lift (IScalar.cast .I64 a)
  if w >= 0#i64
  then
    let i ← kernel.k32.HALF
    let i1 ← w + i
    let i2 ← kernel.k32.MASK
    let i3 ← lift (~~~ i2)
    ok (i1 &&& i3)
  else
    let i ← kernel.k32.HALF
    let i1 ← i - w
    let i2 ← kernel.k32.MASK
    let i3 ← lift (~~~ i2)
    let i4 ← lift (i1 &&& i3)
    -. i4

/-- [fulcrum::kernel::k32::round_ties_even]:
    Source: 'src/kernel.rs', lines 661:12-671:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 678:0-678:74 -/
def kernel.k32.round_ties_even (a : Std.I32) : Result Std.I64 := do
  let w ← lift (IScalar.cast .I64 a)
  let i ← kernel.k32.MASK
  let i1 ← lift (~~~ i)
  let floor ← lift (w &&& i1)
  let frac ← lift (w &&& i)
  let i2 ← w >>> 16#i32
  let i3 ← lift (i2 &&& 1#i64)
  let i4 ← kernel.k32.HALF
  if frac > i4
  then let i5 ← kernel.k32.ONE
       floor + i5
  else
    if frac = i4
    then if i3 = 1#i64
         then let i5 ← kernel.k32.ONE
              floor + i5
         else ok floor
    else ok floor

/-- [fulcrum::kernel::k64::fits]:
    Source: 'src/kernel.rs', lines 340:12-342:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.fits (w : Std.I128) : Result Bool := do
  let i ← lift (IScalar.cast .I128 core.num.I64.MIN)
  if w >= i
  then let i1 ← lift (IScalar.cast .I128 core.num.I64.MAX)
       ok (w <= i1)
  else ok false

/-- [fulcrum::kernel::k64::narrow]:
    Source: 'src/kernel.rs', lines 346:12-352:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.narrow (w : Std.I128) : Result (Option Std.I64) := do
  let b ← kernel.k64.fits w
  if b
  then let i ← lift (IScalar.cast .I64 w)
       ok (some i)
  else ok none

/-- [fulcrum::kernel::k64::saturate]:
    Source: 'src/kernel.rs', lines 356:12-364:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.saturate (w : Std.I128) : Result Std.I64 := do
  let i ← lift (IScalar.cast .I128 core.num.I64.MAX)
  if w > i
  then ok core.num.I64.MAX
  else
    let i1 ← lift (IScalar.cast .I128 core.num.I64.MIN)
    if w < i1
    then ok core.num.I64.MIN
    else ok (IScalar.cast .I64 w)

/-- [fulcrum::kernel::k64::wrap]:
    Source: 'src/kernel.rs', lines 368:12-370:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.wrap (w : Std.I128) : Result Std.I64 := do
  ok (IScalar.cast .I64 w)

/-- [fulcrum::kernel::k64::to_int]:
    Source: 'src/kernel.rs', lines 375:12-377:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.to_int (w : Std.I128) : Result Std.I64 := do
  let i ← w >>> 32#i32
  ok (IScalar.cast .I64 i)

/-- [fulcrum::kernel::k64::from_parts]:
    Source: 'src/kernel.rs', lines 381:12-383:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.from_parts
  (int : Std.I32) (frac : Std.U32) : Result Std.I128 := do
  let i ← lift (IScalar.cast .I128 int)
  let i1 ← i <<< 32#i32
  let i2 ← lift (UScalar.hcast .I128 frac)
  i1 + i2

/-- [fulcrum::kernel::k64::HALF]
    Source: 'src/kernel.rs', lines 336:12-336:46; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
@[global_simps, irreducible]
def kernel.k64.HALF : Result Std.I128 := do
  let i ← 32#i32 - 1#i32
  1#i128 <<< i

/-- [fulcrum::kernel::k64::round_frac]:
    Source: 'src/kernel.rs', lines 391:12-397:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.round_frac (p : Std.I128) : Result Std.I128 := do
  if core.num.I128.BITS = 128#u32
  then
    let i ← p >>> 32#i32
    let i1 ← 32#i32 - 1#i32
    let i2 ← p >>> i1
    let i3 ← lift (i2 &&& 1#i128)
    i + i3
  else let i ← kernel.k64.HALF
       let i1 ← p + i
       i1 >>> 32#i32

/-- [fulcrum::kernel::k64::mul]:
    Source: 'src/kernel.rs', lines 402:12-404:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.mul (a : Std.I64) (b : Std.I64) : Result Std.I128 := do
  let i ← lift (IScalar.cast .I128 a)
  let i1 ← lift (IScalar.cast .I128 b)
  let i2 ← i * i1
  kernel.k64.round_frac i2

/-- [fulcrum::kernel::k64::mul_add]:
    Source: 'src/kernel.rs', lines 412:12-414:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.mul_add
  (a : Std.I64) (b : Std.I64) (c : Std.I64) : Result Std.I128 := do
  let i ← kernel.k64.mul a b
  let i1 ← lift (IScalar.cast .I128 c)
  i + i1

/-- [fulcrum::kernel::k64::round_magnitude_div]:
    Source: 'src/kernel.rs', lines 421:12-429:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.round_magnitude_div
  (un : Std.U128) (ud : Std.U128) (negative : Bool) : Result Std.I128 := do
  let i ← un <<< 1#i32
  let i1 ← lift (UScalar.cast_fromBool .U128 negative)
  let i2 ← ud - i1
  let i3 ← i + i2
  let i4 ← ud <<< 1#i32
  let m ← i3 / i4
  let m1 ← lift (UScalar.hcast .I128 m)
  if negative
  then -. m1
  else ok m1

/-- [fulcrum::kernel::k64::mul_div]:
    Source: 'src/kernel.rs', lines 437:12-443:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.mul_div
  (a : Std.I64) (b : Std.I64) (c : Std.I64) : Result Std.I128 := do
  let i ← core.num.I64.unsigned_abs a
  let i1 ← lift (UScalar.cast .U128 i)
  let i2 ← core.num.I64.unsigned_abs b
  let i3 ← lift (UScalar.cast .U128 i2)
  let i4 ← i1 * i3
  let i5 ← core.num.I64.unsigned_abs c
  let i6 ← lift (UScalar.cast .U128 i5)
  kernel.k64.round_magnitude_div i4 i6 (((a < 0#i64) != (b < 0#i64)) != (c <
    0#i64))

/-- [fulcrum::kernel::k64::lerp]:
    Source: 'src/kernel.rs', lines 450:12-452:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.lerp
  (a : Std.I64) (b : Std.I64) (t : Std.I64) : Result Std.I128 := do
  let i ← lift (IScalar.cast .I128 a)
  let i1 ← lift (IScalar.cast .I128 b)
  let i2 ← lift (IScalar.cast .I128 a)
  let i3 ← i1 - i2
  let i4 ← lift (IScalar.cast .I128 t)
  let i5 ← i3 * i4
  let i6 ← kernel.k64.round_frac i5
  i + i6

/-- [fulcrum::kernel::k64::div]:
    Source: 'src/kernel.rs', lines 113:8-119:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.div (a : Std.I64) (b : Std.I64) : Result Std.I128 := do
  let i ← core.num.I64.unsigned_abs a
  let i1 ← lift (UScalar.cast .U128 i)
  let i2 ← i1 <<< 32#i32
  let i3 ← core.num.I64.unsigned_abs b
  let i4 ← lift (UScalar.cast .U128 i3)
  kernel.k64.round_magnitude_div i2 i4 ((a < 0#i64) != (b < 0#i64))

/-- [fulcrum::kernel::k64::div_int]:
    Source: 'src/kernel.rs', lines 123:8-129:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.div_int (a : Std.I64) (n : Std.I64) : Result Std.I128 := do
  let i ← core.num.I64.unsigned_abs a
  let i1 ← lift (UScalar.cast .U128 i)
  let i2 ← core.num.I64.unsigned_abs n
  let i3 ← lift (UScalar.cast .U128 i2)
  kernel.k64.round_magnitude_div i1 i3 ((a < 0#i64) != (n < 0#i64))

/-- [fulcrum::kernel::k64::div_total]:
    Source: 'src/kernel.rs', lines 461:12-469:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.div_total (a : Std.I64) (b : Std.I64) : Result Std.I128 := do
  if b = 0#i64
  then ok 0#i128
  else kernel.k64.div a b

/-- [fulcrum::kernel::k64::NEWTON_STEPS]
    Source: 'src/kernel.rs', lines 334:12-334:45; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
@[global_simps, irreducible] def kernel.k64.NEWTON_STEPS : Std.U32 := 1#u32

/-- [fulcrum::kernel::k64::isqrt]: loop body 0:
    Source: 'src/kernel.rs', lines 679:0-679:75 -/
@[rust_loop_body]
def kernel.k64.isqrt_loop0.body
  (n : Std.U128) (x : Std.U128) (i : Std.U32) :
  Result (ControlFlow (Std.U128 × Std.U32) Std.U128)
  := do
  if i < kernel.k64.NEWTON_STEPS
  then
    let i1 ← n / x
    let i2 ← x + i1
    let x1 ← i2 >>> 1#i32
    let i3 ← i + 1#u32
    ok (cont (x1, i3))
  else ok (done x)

/-- [fulcrum::kernel::k64::isqrt]: loop 0:
    Source: 'src/kernel.rs', lines 679:0-679:75 -/
@[rust_loop]
def kernel.k64.isqrt_loop0
  (n : Std.U128) (x : Std.U128) (i : Std.U32) : Result Std.U128 := do
  loop
    (fun (x1, i1) => kernel.k64.isqrt_loop0.body n x1 i1)
    (x, i)

/-- [fulcrum::kernel::k64::isqrt]: loop body 1:
    Source: 'src/kernel.rs', lines 679:0-679:75 -/
@[rust_loop_body]
def kernel.k64.isqrt_loop1.body
  (n : Std.U128) (x : Std.U128) : Result (ControlFlow Std.U128 Std.U128) := do
  let i ← x * x
  if i > n
  then let x1 ← x - 1#u128
       ok (cont x1)
  else ok (done x)

/-- [fulcrum::kernel::k64::isqrt]: loop 1:
    Source: 'src/kernel.rs', lines 679:0-679:75 -/
@[rust_loop]
def kernel.k64.isqrt_loop1
  (n : Std.U128) (x : Std.U128) : Result Std.U128 := do
  loop
    (fun x1 => kernel.k64.isqrt_loop1.body n x1)
    x

/-- [fulcrum::kernel::k64::isqrt]:
    Source: 'src/kernel.rs', lines 494:12-511:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.isqrt (n : Std.U128) : Result Std.U128 := do
  if n < 2#u128
  then ok n
  else
    let i ← lift (core.num.U128.leading_zeros n)
    let bits ← core.num.U128.BITS - i
    let low ← core.num.U64.BITS - 1#u32
    if bits <= low
    then
      let i1 ← lift (UScalar.cast .U64 n)
      let i2 ← kernel.k32.isqrt i1
      ok (UScalar.cast .U128 i2)
    else
      let i1 ← bits - low
      let i2 ← i1 + 1#u32
      let j ← i2 / 2#u32
      let i3 ← 2#u32 * j
      let i4 ← n >>> i3
      let i5 ← lift (UScalar.cast .U64 i4)
      let i6 ← kernel.k32.isqrt i5
      let i7 ← lift (UScalar.cast .U128 i6)
      let i8 ← i7 + 1#u128
      let x ← i8 <<< j
      let x1 ← kernel.k64.isqrt_loop0 n x 0#u32
      let i9 ← x1 * x1
      if i9 > n
      then let x2 ← x1 - 1#u128
           kernel.k64.isqrt_loop1 n x2
      else ok x1

/-- [fulcrum::kernel::k64::sqrt_round]:
    Source: 'src/kernel.rs', lines 517:12-520:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.sqrt_round (n : Std.U128) : Result Std.U128 := do
  let s ← kernel.k64.isqrt n
  let i ← s * s
  let i1 ← n - i
  let i2 ← lift (UScalar.cast_fromBool .U128 (i1 > s))
  s + i2

/-- [fulcrum::kernel::k64::sqrt]:
    Source: 'src/kernel.rs', lines 526:12-528:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.sqrt (a : Std.I64) : Result Std.I64 := do
  let i ← lift (IScalar.hcast .U128 a)
  let i1 ← i <<< 32#i32
  let i2 ← kernel.k64.sqrt_round i1
  ok (UScalar.hcast .I64 i2)

/-- [fulcrum::kernel::k64::rsqrt]:
    Source: 'src/kernel.rs', lines 538:12-543:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.rsqrt (a : Std.I64) : Result Std.I64 := do
  let ua ← lift (IScalar.hcast .U128 a)
  let i ← 3#i32 * 32#i32
  let i1 ← 1#u128 <<< i
  let i2 ← i1 / ua
  let s ← kernel.k64.isqrt i2
  let i3 ← 2#u128 * s
  let odd ← i3 + 1#u128
  let i4 ← odd * odd
  let i5 ← i4 * ua
  let i6 ← i + 2#i32
  let i7 ← 1#u128 <<< i6
  let i8 ← lift (UScalar.cast_fromBool .U128 (i5 < i7))
  let i9 ← s + i8
  ok (UScalar.hcast .I64 i9)

/-- [fulcrum::kernel::k64::hypot]:
    Source: 'src/kernel.rs', lines 549:12-553:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.hypot (a : Std.I64) (b : Std.I64) : Result Std.I128 := do
  let i ← core.num.I64.unsigned_abs a
  let ua ← lift (UScalar.cast .U128 i)
  let i1 ← core.num.I64.unsigned_abs b
  let ub ← lift (UScalar.cast .U128 i1)
  let i2 ← ua * ua
  let i3 ← ub * ub
  let i4 ← i2 + i3
  let i5 ← kernel.k64.sqrt_round i4
  ok (UScalar.hcast .I128 i5)

/-- [fulcrum::kernel::k64::det]:
    Source: 'src/kernel.rs', lines 562:12-564:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.det
  (a : Std.I64) (b : Std.I64) (c : Std.I64) (d : Std.I64) :
  Result Std.I128
  := do
  let i ← lift (IScalar.cast .I128 a)
  let i1 ← lift (IScalar.cast .I128 d)
  let i2 ← i * i1
  let i3 ← lift (IScalar.cast .I128 b)
  let i4 ← lift (IScalar.cast .I128 c)
  let i5 ← i3 * i4
  let i6 ← i2 - i5
  kernel.k64.round_frac i6

/-- [fulcrum::kernel::k64::norm_sq]:
    Source: 'src/kernel.rs', lines 568:12-573:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.norm_sq
  (a : Std.I64) (b : Std.I64) (c : Std.I64) : Result Std.U128 := do
  let i ← core.num.I64.unsigned_abs a
  let ua ← lift (UScalar.cast .U128 i)
  let i1 ← core.num.I64.unsigned_abs b
  let ub ← lift (UScalar.cast .U128 i1)
  let i2 ← core.num.I64.unsigned_abs c
  let uc ← lift (UScalar.cast .U128 i2)
  let i3 ← ua * ua
  let i4 ← ub * ub
  let i5 ← i3 + i4
  let i6 ← uc * uc
  i5 + i6

/-- [fulcrum::kernel::k64::sq]:
    Source: 'src/kernel.rs', lines 577:12-580:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.sq (m : Std.I64) : Result Std.U128 := do
  let i ← core.num.I64.unsigned_abs m
  let um ← lift (UScalar.cast .U128 i)
  um * um

/-- [fulcrum::wide::div_rem_3by2]: loop body 0:
    Source: 'src/wide.rs', lines 129:4-132:5 -/
@[rust_loop_body]
def wide.div_rem_3by2_loop.body
  (v : Std.U64) (d1 : Std.U128) (d0 : Std.U128) (q : Std.U128) (r : Std.U128) :
  Result (ControlFlow (Std.U128 × Std.U128) Std.U128)
  := do
  let i ← r >>> 64#i32
  if i = 0#u128
  then
    let i1 ← q * d0
    let i2 ← r <<< 64#i32
    let i3 ← lift (UScalar.cast .U128 v)
    let i4 ← lift (i2 ||| i3)
    if i1 > i4
    then let q1 ← q - 1#u128
         let r1 ← r + d1
         ok (cont (q1, r1))
    else ok (done q)
  else ok (done q)

/-- [fulcrum::wide::div_rem_3by2]: loop 0:
    Source: 'src/wide.rs', lines 129:4-132:5 -/
@[rust_loop]
def wide.div_rem_3by2_loop
  (v : Std.U64) (d1 : Std.U128) (d0 : Std.U128) (q : Std.U128) (r : Std.U128) :
  Result Std.U128
  := do
  loop
    (fun (q1, r1) => wide.div_rem_3by2_loop.body v d1 d0 q1 r1)
    (q, r)

/-- [fulcrum::wide::div_rem_3by2]:
    Source: 'src/wide.rs', lines 120:0-135:1 -/
def wide.div_rem_3by2
  (u : Std.U128) (v : Std.U64) (d : Std.U128) :
  Result (Std.U128 × Std.U128)
  := do
  let d1 ← d >>> 64#i32
  let i ← lift (UScalar.cast .U64 d)
  let d0 ← lift (UScalar.cast .U128 i)
  let i1 ← u >>> 64#i32
  let q ←
    if i1 >= d1
    then ok (UScalar.cast .U128 core.num.U64.MAX)
    else u / d1
  let i2 ← q * d1
  let r ← u - i2
  let q1 ← wide.div_rem_3by2_loop v d1 d0 q r
  let i3 ← u <<< 64#i32
  let i4 ← lift (UScalar.cast .U128 v)
  let i5 ← lift (i3 ||| i4)
  let i6 ← lift (core.num.U128.wrapping_mul q1 d)
  let rem ← lift (core.num.U128.wrapping_sub i5 i6)
  ok (q1, rem)

/-- [fulcrum::wide::div_rem_u256]:
    Source: 'src/wide.rs', lines 142:0-156:1 -/
def wide.div_rem_u256
  (hi : Std.U128) (lo : Std.U128) (d : Std.U128) :
  Result (Std.U128 × Std.U128)
  := do
  if hi = 0#u128
  then let i ← lo / d
       let i1 ← lo % d
       ok (i, i1)
  else
    let s ← lift (core.num.U128.leading_zeros d)
    let d1 ← d <<< s
    let (hi1, lo1) ←
      if s = 0#u32
      then ok (hi, lo)
      else
        do
        let i ← hi <<< s
        let i1 ← 128#u32 - s
        let i2 ← lo >>> i1
        let i3 ← lift (i ||| i2)
        let i4 ← lo <<< s
        ok (i3, i4)
    let i ← lo1 >>> 64#i32
    let i1 ← lift (UScalar.cast .U64 i)
    let (q1, r) ← wide.div_rem_3by2 hi1 i1 d1
    let i2 ← lift (UScalar.cast .U64 lo1)
    let (q0, r1) ← wide.div_rem_3by2 r i2 d1
    let i3 ← q1 <<< 64#i32
    let i4 ← lift (i3 ||| q0)
    let i5 ← r1 >>> s
    ok (i4, i5)

/-- [fulcrum::wide::widening_mul_u128]:
    Source: 'src/wide.rs', lines 100:0-110:1 -/
def wide.widening_mul_u128
  (a : Std.U128) (b : Std.U128) : Result (Std.U128 × Std.U128) := do
  let a1 ← a >>> 64#i32
  let i ← lift (UScalar.cast .U64 a)
  let a0 ← lift (UScalar.cast .U128 i)
  let b1 ← b >>> 64#i32
  let i1 ← lift (UScalar.cast .U64 b)
  let b0 ← lift (UScalar.cast .U128 i1)
  let p00 ← a0 * b0
  let p01 ← a0 * b1
  let p10 ← a1 * b0
  let i2 ← p00 >>> 64#i32
  let i3 ← lift (UScalar.cast .U64 p01)
  let i4 ← lift (UScalar.cast .U128 i3)
  let i5 ← i2 + i4
  let i6 ← lift (UScalar.cast .U64 p10)
  let i7 ← lift (UScalar.cast .U128 i6)
  let mid ← i5 + i7
  let i8 ← lift (UScalar.cast .U64 p00)
  let i9 ← lift (UScalar.cast .U128 i8)
  let i10 ← mid <<< 64#i32
  let lo ← lift (i9 ||| i10)
  let i11 ← a1 * b1
  let i12 ← p01 >>> 64#i32
  let i13 ← i11 + i12
  let i14 ← p10 >>> 64#i32
  let i15 ← i13 + i14
  let i16 ← mid >>> 64#i32
  let hi ← i15 + i16
  ok (hi, lo)

/-- [fulcrum::kernel::k64::scale_to]:
    Source: 'src/kernel.rs', lines 242:8-256:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.scale_to
  (x : Std.I64) (k : Std.I64) (s : Std.U128) : Result Std.I64 := do
  let i ← core.num.I64.unsigned_abs x
  let ux ← lift (UScalar.cast .U128 i)
  let i1 ← core.num.I64.unsigned_abs k
  let k1 ← lift (UScalar.cast .U128 i1)
  let i2 ← ux * ux
  let i3 ← k1 * k1
  let (hi, lo) ← wide.widening_mul_u128 i2 i3
  let (q, r) ← wide.div_rem_u256 hi lo s
  let t ← kernel.k64.isqrt q
  let i4 ← lift (UScalar.hcast .I128 q)
  let i5 ← t * t
  let i6 ← i5 + t
  let i7 ← lift (UScalar.hcast .I128 i6)
  let d ← i4 - i7
  let up ←
    if d > 0#i128
    then ok true
    else if d = 0#i128
         then do
              let i8 ← s >>> 2#i32
              ok (r > i8)
         else ok false
  let i8 ← lift (UScalar.cast_fromBool .U128 up)
  let i9 ← t + i8
  let m ← lift (UScalar.hcast .I64 i9)
  if x < 0#i64
  then -. m
  else ok m

/-- [fulcrum::kernel::k64::scale_vec]:
    Source: 'src/kernel.rs', lines 261:8-267:9; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.scale_vec
  (a : Std.I64) (b : Std.I64) (c : Std.I64) (k : Std.I64) :
  Result (Array Std.I64 3#usize)
  := do
  let s ← kernel.k64.norm_sq a b c
  if s = 0#u128
  then ok (Array.make 3#usize [ a, b, c ])
  else
    let i ← kernel.k64.scale_to a k s
    let i1 ← kernel.k64.scale_to b k s
    let i2 ← kernel.k64.scale_to c k s
    ok (Array.make 3#usize [ i, i1, i2 ])

/-- [fulcrum::kernel::k64::cmp_length]:
    Source: 'src/kernel.rs', lines 587:12-597:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.cmp_length
  (a : Std.I64) (b : Std.I64) (c : Std.I64) (k : Std.I64) : Result Std.I8 := do
  let s ← kernel.k64.norm_sq a b c
  let k2 ← kernel.k64.sq k
  if s < k2
  then ok (-1)#i8
  else if s > k2
       then ok 1#i8
       else ok 0#i8

/-- [fulcrum::kernel::k64::hypot3]:
    Source: 'src/kernel.rs', lines 604:12-609:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.hypot3
  (a : Std.I64) (b : Std.I64) (c : Std.I64) : Result Std.I128 := do
  let i ← core.num.I64.unsigned_abs a
  let ua ← lift (UScalar.cast .U128 i)
  let i1 ← core.num.I64.unsigned_abs b
  let ub ← lift (UScalar.cast .U128 i1)
  let i2 ← core.num.I64.unsigned_abs c
  let uc ← lift (UScalar.cast .U128 i2)
  let i3 ← ua * ua
  let i4 ← ub * ub
  let i5 ← i3 + i4
  let i6 ← uc * uc
  let i7 ← i5 + i6
  let i8 ← kernel.k64.sqrt_round i7
  ok (UScalar.hcast .I128 i8)

/-- [fulcrum::kernel::k64::midpoint]:
    Source: 'src/kernel.rs', lines 613:12-615:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.midpoint (a : Std.I64) (b : Std.I64) : Result Std.I64 := do
  let i ← lift (a ||| b)
  let i1 ← lift (a ^^^ b)
  let i2 ← i1 >>> 1#i32
  i - i2

/-- [fulcrum::kernel::k64::shr]:
    Source: 'src/kernel.rs', lines 620:12-628:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.shr (a : Std.I64) (n : Std.U32) : Result Std.I64 := do
  if n = 0#u32
  then ok a
  else
    if n >= core.num.I64.BITS
    then ok 0#i64
    else
      let i ← a >>> n
      let i1 ← n - 1#u32
      let i2 ← a >>> i1
      let i3 ← lift (i2 &&& 1#i64)
      i + i3

/-- [fulcrum::kernel::k64::shl]:
    Source: 'src/kernel.rs', lines 633:12-640:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.shl (a : Std.I64) (n : Std.U32) : Result (Std.I64 × Bool) := do
  if n >= core.num.I64.BITS
  then ok (0#i64, a != 0#i64)
  else let r ← a <<< n
       let i ← r >>> n
       ok (r, i != a)

/-- [fulcrum::kernel::k64::ONE]
    Source: 'src/kernel.rs', lines 333:12-333:39; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
@[global_simps, irreducible]
def kernel.k64.ONE : Result Std.I128 := 1#i128 <<< 32#i32

/-- [fulcrum::kernel::k64::MASK]
    Source: 'src/kernel.rs', lines 335:12-335:40; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
@[global_simps, irreducible]
def kernel.k64.MASK : Result Std.I128 := do let i ← kernel.k64.ONE
                                            i - 1#i128

/-- [fulcrum::kernel::k64::ceil]:
    Source: 'src/kernel.rs', lines 644:12-646:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.ceil (a : Std.I64) : Result Std.I128 := do
  let i ← lift (IScalar.cast .I128 a)
  let i1 ← kernel.k64.MASK
  let i2 ← i + i1
  let i3 ← lift (~~~ i1)
  ok (i2 &&& i3)

/-- [fulcrum::kernel::k64::round_half_away]:
    Source: 'src/kernel.rs', lines 650:12-657:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.round_half_away (a : Std.I64) : Result Std.I128 := do
  let w ← lift (IScalar.cast .I128 a)
  if w >= 0#i128
  then
    let i ← kernel.k64.HALF
    let i1 ← w + i
    let i2 ← kernel.k64.MASK
    let i3 ← lift (~~~ i2)
    ok (i1 &&& i3)
  else
    let i ← kernel.k64.HALF
    let i1 ← i - w
    let i2 ← kernel.k64.MASK
    let i3 ← lift (~~~ i2)
    let i4 ← lift (i1 &&& i3)
    -. i4

/-- [fulcrum::kernel::k64::round_ties_even]:
    Source: 'src/kernel.rs', lines 661:12-671:13; this code is generated from a macro invocation at: 'src/kernel.rs', lines 679:0-679:75 -/
def kernel.k64.round_ties_even (a : Std.I64) : Result Std.I128 := do
  let w ← lift (IScalar.cast .I128 a)
  let i ← kernel.k64.MASK
  let i1 ← lift (~~~ i)
  let floor ← lift (w &&& i1)
  let frac ← lift (w &&& i)
  let i2 ← w >>> 32#i32
  let i3 ← lift (i2 &&& 1#i128)
  let i4 ← kernel.k64.HALF
  if frac > i4
  then let i5 ← kernel.k64.ONE
       floor + i5
  else
    if frac = i4
    then if i3 = 1#i128
         then let i5 ← kernel.k64.ONE
              floor + i5
         else ok floor
    else ok floor

end fulcrum
