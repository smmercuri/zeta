/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Functions.Pi
public import Enclosure.BinarySplit.Tactic.Arctan
public import Enclosure.BinarySplit.Tactic.Engine

/-!
# `π` metaprograms: `pi_approx%`, `pi_near%`, and shared constants

The metaprogram side of `Functions.Pi`: `mkPiProof` (the two Machin arctan factors at
precision `1/(20E)`, combined by `pi_combine`), the `pi_approx%` value elaborator, the
`pi_near%` enclosure elaborator, and the reusable named `π` constants (15 dp and 50 dp, each
kernel-checked once) for range reduction.
-/
@[expose] public section


namespace BSN
open Enclosure

/-! ### Elaborator and tactic -/

open Lean Elab Term Meta in
/-- `(P, Q, proof)` with `proof : Real.IsNear Real.pi false P Q 1 E`, from Machin's formula
`P = 16·c₁ − 4·c₂` with the factors `arctan(1/5)`, `arctan(1/239)` as auxiliary lemmas. -/
meta def mkPiProof (E : ℕ) : MetaM (ℕ × ℕ × Expr) := do
  let D := 20 * E
  let (h₁, neg₁, c₁, Q) ← mkArctanPos 1 5 D
  let (h₂, neg₂, c₂, _) ← mkArctanPos 1 239 D
  if neg₁ || neg₂ then throwError "mkPiProof: unexpected negative arctan centre"
  -- `mkArctanPos 1 v D` concludes `Real.IsNear (Real.arctan (↑1/↑v)) false c Q 1 D`.
  let a₁ ← mkBoundAux (mkIsNearTy (mkRealFn ``Real.arctan (mkCastDivR 1 5)) false c₁ Q 1 D) h₁
  let a₂ ← mkBoundAux (mkIsNearTy (mkRealFn ``Real.arctan (mkCastDivR 1 239)) false c₂ Q 1 D) h₂
  let P := 16 * c₁ - 4 * c₂
  let app := mkAppN (mkConst ``pi_combine)
    #[natLitShared c₁, natLitShared c₂, natLitShared Q, natLitShared D, natLitShared E,
      natLitShared P,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, a₁, a₂]
  return (P, Q, app)

open Lean Elab Term Meta in
/-- The signed centre `(neg, cn, Q)` of the factor `arctan(1/v)` at precision `1/D`, without a
proof. -/
meta def mkArctanFactorVal (v D : ℕ) : MetaM (Bool × ℕ × ℕ) := do
  let (m, Q, _, _, _) ← arctanCore 1 v D
  return (decide (m < 0), m.natAbs, Q)

open Lean Elab Term Meta in
/-- `(P, Q)` with `P/Q ≈ π` to precision `1/E`, without a proof; memoized in `piValCache`. -/
meta def piVal (E : ℕ) : MetaM (ℕ × ℕ) := do
  if let some r := (← piValCache.get)[E]? then
    return r
  let D := 20 * E
  let (_, c₁, Q) ← mkArctanFactorVal 5 D
  let (_, c₂, _) ← mkArctanFactorVal 239 D
  let r := (16 * c₁ - 4 * c₂, Q)
  piValCache.modify (·.insert E r)
  return r

open Lean Elab Term Meta in
/-- `pi_approx% E : ℚ` is the dyadic rational `P/Q` approximating `Real.pi` to `1/E`, without a
proof (the enclosure is `pi_near%`). -/
elab "pi_approx% " En:num : term => do
  let (P, Q) ← piVal En.getNat
  mkNatDyadic P Q

open Lean Elab Term Meta in
/-- The dyadic numerator of `π ≈ P/Q` at precision `1/E`, as a literal. -/
elab "piNum% " En:num : term => do return natLitShared (← piVal En.getNat).1

open Lean Elab Term Meta in
/-- The dyadic denominator (`2^k`) of `π ≈ P/Q` at precision `1/E`, as a literal. -/
elab "piDen% " En:num : term => do return natLitShared (← piVal En.getNat).2

open Lean Elab Term Meta in
/-- `pi_near% E` : a proof of `Real.IsNear Real.pi false P Q 1 E` from `mkPiProof`. -/
elab "pi_near% " En:num : term => do
  let (_, _, pf) ← mkPiProof En.getNat
  return pf

/-! ### Reusable named `π` constants

Fixed-precision `IsNear` enclosures of `π`, each kernel-checked once and referenced in place of a
fresh Machin certificate. -/

/-- `π` to `1/10¹⁵` as an `IsNear` enclosure with literal dyadic fields. -/
theorem pi_near_15 :
    Real.IsNear Real.pi false (piNum% 1000000000000000) (piDen% 1000000000000000)
      (nat_lit 1) (nat_lit 1000000000000000) :=
  pi_near% 1000000000000000

/-- `π` to `1/10⁵⁰` as an `IsNear` enclosure with literal dyadic fields. -/
theorem pi_near_50 :
    Real.IsNear Real.pi
      false (piNum% 100000000000000000000000000000000000000000000000000)
      (piDen% 100000000000000000000000000000000000000000000000000)
      (nat_lit 1) (nat_lit 100000000000000000000000000000000000000000000000000) :=
  pi_near% 100000000000000000000000000000000000000000000000000

open Lean Elab Term Meta in
/-- `mkConstTier?` for `π` (tiers `pi_near_15`, `pi_near_50`). -/
meta def mkPiTier? (E : ℕ) (weaken : Bool := false) : MetaM (Option (ℕ × ℕ × ℕ × Expr)) :=
  mkConstTier? (mkConst ``Real.pi) ``pi_near_15 ``pi_near_50 piVal E weaken

end BSN
