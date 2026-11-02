module

public import Enclosure.Defs
public import Enclosure.BinarySplit.Defs

/-!
# `Native.Eval.Encl`: the computable part

The definitions `native_decide` evaluates, free of `Mathlib` so that they compile natively (the
`NativeEval` library is built with `precompileModules`). Their soundness theorems are in
`Native.Encl`.
-/
@[expose] public section

namespace Native

open Enclosure

/-- The fields of an enclosure `±cn/cd ± rn/rd`: the sign of the centre, its magnitude over `cd`,
and the radius `rn/rd`. -/
structure Encl where
  neg : Bool
  cn : Nat
  cd : Nat
  rn : Nat
  rd : Nat
  deriving Repr, DecidableEq

namespace Encl

/-- Both denominators are positive: the side condition every `Enclosure` lemma asks of an input. -/
def denomsPos (e : Encl) : Bool := Nat.ble (nat_lit 1) e.cd && Nat.ble (nat_lit 1) e.rd

/-- The exact rational `±cn/cd`, with radius `0`. -/
def const (neg : Bool) (cn cd : Nat) : Encl := ⟨neg, cn, cd, nat_lit 0, nat_lit 1⟩

/-- Negation: flip the sign of the centre. -/
def negate (e : Encl) : Encl := ⟨!e.neg, e.cn, e.cd, e.rn, e.rd⟩

/-- The signed centre numerator of `x + y` over `cdx·cdy`, as `(sign, magnitude)`. -/
def addCentre (x y : Encl) : Bool × Nat :=
  let p := ((numPos x.neg x.cn).mul y.cd).add ((numPos y.neg y.cn).mul x.cd)
  let m := ((numNeg x.neg x.cn).mul y.cd).add ((numNeg y.neg y.cn).mul x.cd)
  if Nat.ble m p then (false, p.sub m) else (true, m.sub p)

/-- `x + y`, exactly (`Real.IsNear.add`): centre over `cdx·cdy`, radius over `rdx·rdy`. -/
def add (x y : Encl) : Option Encl :=
  let c := addCentre x y
  if x.denomsPos && y.denomsPos &&
      Nat.beq (((numPos c.1 c.2).add ((numNeg x.neg x.cn).mul y.cd)).add
                ((numNeg y.neg y.cn).mul x.cd))
              (((numNeg c.1 c.2).add ((numPos x.neg x.cn).mul y.cd)).add
                ((numPos y.neg y.cn).mul x.cd)) then
    some ⟨c.1, c.2, x.cd.mul y.cd, (x.rn.mul y.rd).add (y.rn.mul x.rd), x.rd.mul y.rd⟩
  else none

/-- `x − y = x + (−y)`. -/
def sub (x y : Encl) : Option Encl := add x y.negate

/-- `x · y`, exactly (`Real.IsNear.mul`): the interval-product radius over `cdx·cdy·rdx·rdy`. -/
def mul (x y : Encl) : Option Encl :=
  if x.denomsPos && y.denomsPos then
    some ⟨Bool.xor x.neg y.neg, x.cn.mul y.cn, x.cd.mul y.cd,
      ((((x.cn.mul y.rn).mul y.cd).mul x.rd).add (((y.cn.mul x.rn).mul x.cd).mul y.rd)).add
        (((x.rn.mul y.rn).mul x.cd).mul y.cd),
      ((x.cd.mul y.cd).mul x.rd).mul y.rd⟩
  else none

/-- Round the centre's magnitude down onto the grid `1/Q` and inflate the radius (over `Q`) by the
drop, rounded up (`Real.IsNear.recentre'`). Keeps field sizes bounded under repeated arithmetic. -/
def recentre (e : Encl) (Q : Nat) : Option Encl :=
  let cn' := (e.cn.mul Q).div e.cd
  let num := (e.rn.mul (e.cd.mul Q)).add (((e.cn.mul Q).sub (cn'.mul e.cd)).mul e.rd)
  let den := e.rd.mul e.cd
  let rn' := (num.add (den.sub (nat_lit 1))).div den
  if recentreOk e.cn e.cd e.rn e.rd cn' Q rn' Q then some ⟨e.neg, cn', Q, rn', Q⟩ else none

/-- `x⁻¹` for a positive enclosure, with endpoints `a/Q ≤ 1/hi`, `1/lo ≤ b/Q`
(`Real.IsNear.inv_image`). `none` if the enclosure is not strictly positive. -/
def invPos (e : Encl) (Q : Nat) : Option Encl :=
  let lo := (e.cn.mul e.rd).sub (e.rn.mul e.cd)     -- lo·cd·rd
  let hi := (e.cn.mul e.rd).add (e.rn.mul e.cd)     -- hi·cd·rd
  let qcr := Q.mul (e.cd.mul e.rd)
  let a := qcr.div hi
  let b := (qcr.add (lo.sub (nat_lit 1))).div lo
  if !e.neg && e.denomsPos && Nat.ble (nat_lit 1) Q &&
      Nat.blt (e.rn.mul e.cd) (e.cn.mul e.rd) &&
      Nat.ble (a.mul hi) qcr && Nat.ble qcr (b.mul lo) then
    some ⟨false, a.add b, Nat.mul (nat_lit 2) Q, b.sub a, Nat.mul (nat_lit 2) Q⟩
  else none

/-- `x⁻¹` for an enclosure excluding `0`: `invPos` directly, or through `x⁻¹ = −(−x)⁻¹`. -/
def inv (e : Encl) (Q : Nat) : Option Encl :=
  if e.neg then (invPos e.negate Q).map negate else invPos e Q

/-- `√x` for a nonnegative enclosure, with endpoints on the grid `1/Q`: `a/Q ≤ √lo`, `√hi ≤ b/Q`
(`Real.IsNear.sqrt_image`). -/
def sqrt (e : Encl) (Q : Nat) : Option Encl :=
  let lo := (e.cn.mul e.rd).sub (e.rn.mul e.cd)     -- lo·cd·rd
  let hi := (e.cn.mul e.rd).add (e.rn.mul e.cd)     -- hi·cd·rd
  let cr := e.cd.mul e.rd
  let a := Nat.sqrt ((lo.mul (Q.pow 2)).div cr)
  let b := (Nat.sqrt (((hi.mul (Q.pow 2)).add (cr.sub (nat_lit 1))).div cr)).add (nat_lit 1)
  if !e.neg && e.denomsPos && Nat.ble (nat_lit 1) Q &&
      Nat.ble (e.rn.mul e.cd) (e.cn.mul e.rd) &&
      Nat.ble ((a.pow 2).mul cr) (lo.mul (Q.pow 2)) &&
      Nat.ble (hi.mul (Q.pow 2)) ((b.pow 2).mul cr) then
    some ⟨false, a.add b, Nat.mul (nat_lit 2) Q, b.sub a, Nat.mul (nat_lit 2) Q⟩
  else none

/-- The side conditions of `Real.IsNear.of_interval` (and `BSN.isNear_log_image`): positive
denominators, and the result interval `R` containing `[lo e₁, hi e₂]`, cleared of denominators. -/
def hullOk (e₁ e₂ R : Encl) : Bool :=
  Nat.ble 1 e₁.cd && Nat.ble 1 e₁.rd && Nat.ble 1 e₂.cd && Nat.ble 1 e₂.rd &&
  Nat.ble 1 R.cd && Nat.ble 1 R.rd &&
  Nat.ble ((((numPos R.neg R.cn).mul ((R.rd.mul e₁.cd).mul e₁.rd)).add
      ((numNeg e₁.neg e₁.cn).mul ((R.cd.mul R.rd).mul e₁.rd))).add
      (e₁.rn.mul ((R.cd.mul R.rd).mul e₁.cd)))
    ((((numPos e₁.neg e₁.cn).mul ((R.cd.mul R.rd).mul e₁.rd)).add
      ((numNeg R.neg R.cn).mul ((R.rd.mul e₁.cd).mul e₁.rd))).add
      (R.rn.mul ((R.cd.mul e₁.cd).mul e₁.rd))) &&
  Nat.ble ((((numPos e₂.neg e₂.cn).mul ((R.cd.mul R.rd).mul e₂.rd)).add
      ((numNeg R.neg R.cn).mul ((R.rd.mul e₂.cd).mul e₂.rd))).add
      (e₂.rn.mul ((R.cd.mul R.rd).mul e₂.cd)))
    ((((numPos R.neg R.cn).mul ((R.rd.mul e₂.cd).mul e₂.rd)).add
      ((numNeg e₂.neg e₂.cn).mul ((R.cd.mul R.rd).mul e₂.rd))).add
      (R.rn.mul ((R.cd.mul e₂.cd).mul e₂.rd)))

/-- `⌊n/d⌋` for a signed numerator. -/
def floorDiv (n : Int) (d : Nat) : Int := Int.fdiv n d

/-- An enclosure on the grid `1/Q` of the interval from `e₁`'s lower end to `e₂`'s upper end. -/
def hullFields (e₁ e₂ : Encl) (Q : Nat) : Encl :=
  let s₁ : Int := if e₁.neg then -(e₁.cn : Int) else e₁.cn
  let s₂ : Int := if e₂.neg then -(e₂.cn : Int) else e₂.cn
  -- `lo = (s₁·rd₁ − rn₁·cd₁)/(cd₁·rd₁)`, `hi = (s₂·rd₂ + rn₂·cd₂)/(cd₂·rd₂)`, scaled by `Q`
  let L := floorDiv ((s₁ * e₁.rd - e₁.rn * e₁.cd) * Q) (e₁.cd * e₁.rd)
  let H := -floorDiv (-((s₂ * e₂.rd + e₂.rn * e₂.cd) * Q)) (e₂.cd * e₂.rd)
  let m := floorDiv (L + H) 2
  let r := max (m - L) (H - m)
  ⟨decide (m < 0), m.natAbs, Q, r.toNat, Q⟩

/-- The hull of `e₁` and `e₂` on the grid `1/Q`, if it checks. -/
def hull (e₁ e₂ : Encl) (Q : Nat) : Option Encl :=
  let R := hullFields e₁ e₂ Q
  if hullOk e₁ e₂ R then some R else none

/-- `x + y`, recentred onto `1/Q`. -/
def addR (x y : Encl) (Q : Nat) : Option Encl := (add x y).bind (recentre · Q)

/-- `x − y`, recentred onto `1/Q`. -/
def subR (x y : Encl) (Q : Nat) : Option Encl := (sub x y).bind (recentre · Q)

/-- `x · y`, recentred onto `1/Q`. -/
def mulR (x y : Encl) (Q : Nat) : Option Encl := (mul x y).bind (recentre · Q)

end Encl

end Native
