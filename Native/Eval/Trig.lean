module

public import Enclosure.Defs
public import Enclosure.BinarySplit.Defs
public import Native.Eval.Const

/-!
# `Native.Eval.Trig`: the computable part

The definitions `native_decide` evaluates, free of `Mathlib` so that they compile natively (the
`NativeEval` library is built with `precompileModules`). Their soundness theorems are in
`Native.Trig`.
-/
@[expose] public section

namespace Native

open Enclosure BSN

/-- A power of two `≥ 2·D` (so that `(2D).ble Q`): the leaves' output denominator. -/
def dyadic (D : Nat) : Nat := 2 ^ (Nat.log2 (2 * D) + 1)

/-- The signed floor of `(A − B)/den`, as `(sign, magnitude)`: `⌊(A−B)/den⌋` when `B ≤ A`, else
`−⌈(B−A)/den⌉`. -/
def signedFloor (A B den : Nat) : Bool × Nat :=
  if B ≤ A then (false, (A - B) / den) else (true, (B - A + den - 1) / den)

/-- The least `M` (counting from `M`) at which the even/odd trig series' convergence and tail guards
hold, with the running tail products `L = u^k·2D`, `R = v^k·k!` (as `BSN.trigTermCountAux`), cut off
after `fuel` steps. The value needs no proof: the leaf lemma re-checks every guard. -/
def trigTermCount (u v : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, M, _, _, _ => M
  | fuel + 1, M, k, L, R =>
    if u.blt ((k + 1) * v) && (2 * u ^ 2).ble ((k + 1) ^ 2 * v ^ 2) && (2 * L).ble R then M
    else trigTermCount u v fuel (M + 1) (k + 4) (L * u ^ 4)
      (R * (v ^ 4 * ((k + 1) * (k + 2) * (k + 3) * (k + 4))))

/-- The side conditions of `BSN.cos_dyadic_bound`, other than the two `binarySplit` equations. -/
def cosRatOk (u v M Mm Q D Te Qe To Qo : Nat) (neg : Bool) (cn : Nat) : Bool :=
  u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v) &&
  (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)) &&
  Nat.ble 1 Qe && Nat.ble 1 Qo && Nat.ble 1 D && Nat.ble 1 v && Nat.ble 1 M &&
  (Mm.succ).beq M &&
  ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble (Qe.mul (cosEvenQ v Mm)) &&
  (((numPos neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
      ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)).ble
    ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
      ((numNeg neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))) &&
  ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
      ((numNeg neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))).blt
    ((((numPos neg cn).succ).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
      ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) &&
  (Nat.mul 2 D).ble Q

/-- `cos(u/v)` to `1/D`, centre on the grid `1/dyadic D`. `none` if `u/v` is too large for the
series' convergence guards. -/
def cosRat (u v D : Nat) : Option Encl :=
  let Q := dyadic D
  let M := max 1 (trigTermCount u v 10000 0 0 (2 * D) 1)
  let Mm := M - 1
  let ev := binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm
  let od := binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm
  let Ne := ev.2.1 + ev.1
  let No := u ^ 2 * (od.2.1 + od.1)
  let Do := 2 * v ^ 2 * od.2.1
  let c := signedFloor (Ne * Do * Q) (No * ev.2.1 * Q) (ev.2.1 * Do)
  if cosRatOk u v M Mm Q D ev.1 ev.2.1 od.1 od.2.1 c.1 c.2 then some ⟨c.1, c.2, Q, 1, D⟩
  else none

/-- The side conditions of `BSN.sin_dyadic_bound`, other than the two `binarySplit` equations. -/
def sinRatOk (u v M Mm Q D Te Qe To Qo : Nat) (neg : Bool) (cn : Nat) : Bool :=
  u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v) &&
  (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)) &&
  Nat.ble 1 Qe && Nat.ble 1 Qo && Nat.ble 1 D && Nat.ble 1 v && Nat.ble 1 M &&
  (Mm.succ).beq M &&
  ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
    ((v.mul Qe).mul (sinEvenQ v Mm)) &&
  (((numPos neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
      ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
    ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
      ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))) &&
  ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
      ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))).blt
    ((((numPos neg cn).succ).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
      ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) &&
  (Nat.mul 2 D).ble Q

/-- `sin(u/v)` to `1/D`, centre on the grid `1/dyadic D`. `none` if `u/v` is too large for the
series' convergence guards. -/
def sinRat (u v D : Nat) : Option Encl :=
  let Q := dyadic D
  let M := max 1 (trigTermCount u v 10000 0 1 (u * (2 * D)) v)
  let Mm := M - 1
  let ev := binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm
  let od := binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm
  let Ne := u * (ev.2.1 + ev.1)
  let De := v * ev.2.1
  let No := u ^ 3 * (od.2.1 + od.1)
  let Do := 6 * v ^ 3 * od.2.1
  let c := signedFloor (Ne * Do * Q) (No * De * Q) (De * Do)
  if sinRatOk u v M Mm Q D ev.1 ev.2.1 od.1 od.2.1 c.1 c.2 then some ⟨c.1, c.2, Q, 1, D⟩
  else none

/-- The `1`-Lipschitz image: an enclosure `e` of `f` at `X`'s centre becomes one of `f x`, its
radius inflated by `X`'s (`Real.IsNear.lipschitz_image`'s output fields). -/
def lipschitzImage (X e : Encl) : Option Encl :=
  if Nat.ble 1 X.rd && Nat.ble 1 e.rd then
    some ⟨e.neg, e.cn, e.cd, (e.rn.mul X.rd).add (X.rn.mul e.rd), e.rd.mul X.rd⟩
  else none

/-- `cos x` for `x` enclosed by `X` with a small centre: the leaf at the centre, widened by `X`'s
radius. `X`'s centre should already be on a coarse grid (see `recentre`). -/
def cosSmall (X : Encl) (D : Nat) : Option Encl :=
  (cosRat X.cn X.cd D).bind (lipschitzImage X)

/-- `sin x` for `x` enclosed by `X` with a small centre; see `cosSmall`. -/
def sinSmall (X : Encl) (D : Nat) : Option Encl :=
  (sinRat X.cn X.cd D).bind fun c => lipschitzImage X (if X.neg then c.negate else c)

/-- `cos(y + (4q + j)·π/2)` from enclosures of `cos y`/`sin y`, by the quadrant `j < 4`. -/
def quadCos (j : Nat) (Y : Encl) (D : Nat) : Option Encl :=
  match j with
  | 0 => cosSmall Y D
  | 1 => (sinSmall Y D).map Encl.negate
  | 2 => (cosSmall Y D).map Encl.negate
  | 3 => sinSmall Y D
  | _ => none

/-- `sin(y + (4q + j)·π/2)` from enclosures of `sin y`/`cos y`, by the quadrant `j < 4`. -/
def quadSin (j : Nat) (Y : Encl) (D : Nat) : Option Encl :=
  match j with
  | 0 => sinSmall Y D
  | 1 => cosSmall Y D
  | 2 => (sinSmall Y D).map Encl.negate
  | 3 => (cosSmall Y D).map Encl.negate
  | _ => none

/-- The nearest multiple `k` of `π/2` to `X`'s (nonnegative) centre `cn/cd`, from `piEncl`'s centre:
`⌊2·(cn/cd)/π + 1/2⌋`. Any `k` is sound; the nearest keeps the reduced argument small. -/
def nearestQuarterTurn (X : Encl) : Nat :=
  (4 * X.cn * piEncl.cd + X.cd * piEncl.cn) / (2 * X.cd * piEncl.cn)

/-- `x − (k/2)·π` for the nearest quarter turn `k`, recentred onto the grid `1/dyadic (4D)`. -/
def reduceQuarter (X : Encl) (k D : Nat) : Option Encl :=
  ((Encl.const false k 2).mul piEncl).bind fun K =>
    (X.sub K).bind fun Y => Y.recentre (dyadic (4 * D))

/-- `cos x` for `x` enclosed by `X` with a nonnegative centre, reduced by the nearest quarter
turn. -/
def cosNonneg (X : Encl) (D : Nat) : Option Encl :=
  let k := nearestQuarterTurn X
  (reduceQuarter X k D).bind fun Y => quadCos (k % 4) Y D

/-- `sin x` for `x` enclosed by `X` with a nonnegative centre, reduced by the nearest quarter
turn. -/
def sinNonneg (X : Encl) (D : Nat) : Option Encl :=
  let k := nearestQuarterTurn X
  (reduceQuarter X k D).bind fun Y => quadSin (k % 4) Y D

/-- `cos x` for `x` enclosed by `X`, to about `1/D` plus `X`'s radius. A negative centre goes
through `cos x = cos (−x)`. -/
def cos (X : Encl) (D : Nat) : Option Encl :=
  if X.neg then cosNonneg X.negate D else cosNonneg X D

/-- `sin x` for `x` enclosed by `X`, to about `1/D` plus `X`'s radius. A negative centre goes
through `sin x = −sin (−x)`. -/
def sin (X : Encl) (D : Nat) : Option Encl :=
  if X.neg then (sinNonneg X.negate D).map Encl.negate else sinNonneg X D

end Native
