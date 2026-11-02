module

public import Enclosure.Defs
public import Enclosure.BinarySplit.Defs
public import Native.Eval.Trig

/-!
# `Native.Eval.Arctan`: the computable part

The definitions `native_decide` evaluates, free of `Mathlib` so that they compile natively (the
`NativeEval` library is built with `precompileModules`). Their soundness theorems are in
`Native.Arctan`.
-/
@[expose] public section

namespace Native

open Enclosure BSN

/-- The least `M` (counting from `M`) with `u^(4M+1)·2D ≤ v^(4M+1)·(4M+1)`, with the running powers
`L = u^(4M+1)·2D` and `R = v^(4M+1)`, cut off after `fuel` steps. The value needs no proof:
`BSN.arctan_dyadic_bound` re-checks the tail guard. -/
def arctanTermCount (u v : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, M, _, _ => M
  | fuel + 1, M, L, R =>
    if L ≤ R * (4 * M + 1) then M else arctanTermCount u v fuel (M + 1) (L * u ^ 4) (R * v ^ 4)

/-- The side conditions of `BSN.arctan_dyadic_bound`, other than the two `binarySplit` equations. -/
def arctanRatOk (u v M Mm Q D Te Qe To Qo : Nat) (neg : Bool) (cn : Nat) : Bool :=
  u.blt v && Nat.ble 1 Qe && Nat.ble 1 Qo && Nat.ble 1 D && Nat.ble 1 v && Nat.ble 1 M &&
  (Mm.succ).beq M &&
  ((u.pow ((Nat.mul 4 M).succ)).mul (Nat.mul 2 D)).ble
    ((v.pow ((Nat.mul 4 M).succ)).mul ((Nat.mul 4 M).succ)) &&
  (((numPos neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
      ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
    ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
      ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))) &&
  ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
      ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))).blt
    ((((numPos neg cn).succ).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
      ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) &&
  (Nat.mul 2 D).ble Q

/-- `arctan(u/v)` to `1/D` for `u < v`, centre on the grid `1/dyadic D`. -/
def arctanRat (u v D : Nat) : Option Encl :=
  let Q := dyadic D
  let M := max 1 (arctanTermCount u v 10000 1 (u ^ 5 * (2 * D)) (v ^ 5))
  let Mm := M - 1
  let ev := binarySplit (arctanEvenP u) (arctanEvenQ v) 0 Mm
  let od := binarySplit (arctanOddP u) (arctanOddQ v) 0 Mm
  let Ne := u * (ev.2.1 + ev.1)
  let De := v * ev.2.1
  let No := u ^ 3 * (od.2.1 + od.1)
  let Do := 3 * v ^ 3 * od.2.1
  let c := signedFloor (Ne * Do * Q) (No * De * Q) (De * Do)
  if arctanRatOk u v M Mm Q D ev.1 ev.2.1 od.1 od.2.1 c.1 c.2 then some ⟨c.1, c.2, Q, 1, D⟩
  else none

end Native
