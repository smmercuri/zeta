module

public import Enclosure.Defs
public import Enclosure.BinarySplit.Defs
public import Native.Eval.RiemannSiegel

/-!
# `Native.Eval.Batch`: the computable part

The definitions `native_decide` evaluates, free of `Mathlib` so that they compile natively (the
`NativeEval` library is built with `precompileModules`). Their soundness theorems are in
`Native.Batch`.
-/
@[expose] public section

namespace Native

open Enclosure BSN

/-- The side conditions of `Real.IsNear.pos_val`/`neg_val` (the enclosure `Z` excludes `0`) and of
`norm_gt_of_isNear` (`Z`'s magnitude exceeds the upper end of `B`). -/
def endpointOk (Z B : Encl) : Bool :=
  Nat.ble 1 Z.cd && Nat.ble 1 Z.rd && Nat.ble 1 B.cd && Nat.ble 1 B.rd &&
  Nat.blt (Z.rn.mul Z.cd) (Z.cn.mul Z.rd) &&
  Nat.blt ((((numPos B.neg B.cn).mul (B.rd.mul (Z.cd.mul Z.rd))).add
      (B.rn.mul (B.cd.mul (Z.cd.mul Z.rd)))).add
      (Z.rn.mul (B.cd.mul (B.rd.mul Z.cd))))
    ((Z.cn.mul (B.cd.mul (B.rd.mul Z.rd))).add
      ((numNeg B.neg B.cn).mul (B.rd.mul (Z.cd.mul Z.rd))))

/-- The certified sign (`true` for negative) of a value enclosed by `z`, when its enclosure
excludes `0` and its magnitude exceeds the bound enclosed by `b`. -/
def certifiedSign (z b : Option Encl) : Option Bool :=
  z.bind fun Z => b.bind fun B => if endpointOk Z B then some Z.neg else none

/-- At `t = tn/td`: the certified sign of the linear-free approximant against an enclosure `B` of
the error bound at some `s ≤ t` (the bound is antitone, so one value serves a whole batch). -/
def endpointSign₀ (tab : TermTable) (tn td W : Nat) (B : Option Encl) : Option Bool :=
  certifiedSign (approx₀F tab tn td W) B

/-- At `t = tn/td`: the certified sign of the full approximant against its error bound. -/
def endpointSign₁ (tab : TermTable) (tn td W : Nat) : Option Bool :=
  certifiedSign (approx₁ tab tn td W) (errBound₁ tn td W)

/-- A bracket `[an/ad, bn/bd]`. -/
structure Row where
  an : Nat
  ad : Nat
  bn : Nat
  bd : Nat
  deriving Repr

/-- The checks of a bracket's certificates other than the endpoint values: positive
denominators, `a ≤ b`, and `32π ≤ a` (as `BSN.thirtyTwoPi_le_dec`). -/
def rowOk (r : Row) : Bool :=
  Nat.ble 1 r.ad && Nat.ble 1 r.bd && Nat.ble (r.an.mul r.bd) (r.bn.mul r.ad) &&
  Nat.ble (Nat.mul 504 r.ad) (Nat.mul 5 r.an)

/-- Two certified signs that differ. -/
def signsDiffer : Option Bool → Option Bool → Bool
  | some s₁, some s₂ => s₁ != s₂
  | _, _ => false

/-- The brackets between consecutive boundaries. -/
def rowsOf : List (Nat × Nat) → List Row
  | a :: b :: rest => ⟨a.1, a.2, b.1, b.2⟩ :: rowsOf (b :: rest)
  | _ => []

/-- The fallback check: the bracket's endpoint signs under the full approximant at precision `W₁`,
with its own table. -/
def fallbackOk (a b : Nat × Nat) (W₁ : Nat) : Bool :=
  signsDiffer (endpointSign₁ (termTable 0 W₁) a.1 a.2 W₁)
    (endpointSign₁ (termTable 0 W₁) b.1 b.2 W₁)

/-- Every bracket of the tiling checks, given the left boundary `a` and its linear-free sign `sa`
(already computed when it was the previous bracket's right boundary). Each bracket passes `rowOk`
and has differing linear-free signs, against the batch's error bound `B`, or else differing full
signs (`fallbackOk`). The right boundary's sign is computed once and passed on. -/
def tilingOk (tab : TermTable) (W W₁ : Nat) (B : Option Encl) :
    Nat × Nat → Option Bool → List (Nat × Nat) → Bool
  | _, _, [] => true
  | a, sa, b :: rest =>
    let sb := endpointSign₀ tab b.1 b.2 W B
    (rowOk ⟨a.1, a.2, b.1, b.2⟩ && (signsDiffer sa sb || fallbackOk a b W₁)) &&
    tilingOk tab W W₁ B b sb rest

/-- The whole batch, as the tiling with boundaries `bs`: `n` brackets from `an/ad` to `bn/bd`,
each certified. The linear-free values use precision `W`, one main-sum table up to the top
boundary's cutoff, and the error bound at the bottom boundary; the full-certificate fallback
recomputes at precision `W₁`. -/
def checkTiling (bs : List (Nat × Nat)) (W W₁ n an ad bn bd : Nat) : Bool :=
  match bs with
  | a :: b :: rest =>
    let tab := termTable (((b :: rest).getLast?.bind fun l => cutoff l.1 l.2).getD 0) W
    let B := errBound a.1 a.2 W
    Nat.ble 1 a.1 && Nat.ble 1 a.2 &&
      tilingOk tab W W₁ B a (endpointSign₀ tab a.1 a.2 W B) (b :: rest) &&
      (b :: rest).length == n && a == (an, ad) && (b :: rest).getLast? == some (bn, bd)
  | _ => false

end Native
