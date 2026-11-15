/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Functions.Log2
public import Enclosure.BinarySplit.Tactic.Log
public import Enclosure.BinarySplit.Tactic.Engine

/-!
# High-precision `log 2` metaprograms and shared constants

The metaprogram side of `Functions.Log2`: the Machin factor builders, `mkLog2Proof`, the
`log2_approx%` value elaborator and `log2_near%` enclosure elaborator, the value-only `log2ValAt`,
and the reusable named `log 2` constants (15 dp and 50 dp, each kernel-checked once) in both the
whole-`ℚ` form and the split form the interval `log` reduction consumes.
-/
@[expose] public section


namespace BSN
open Enclosure

open Lean Elab Term Meta in
/-- `(p, ty, proof)` for the Machin factor `log((v+1)/(v-1))` at precision `1/D`, with
`proof : ty` and `ty = Real.IsNear (log (↑(v+1)/↑(v-1))) false p Q 1 D`, `Q = dyadicDenom D`. -/
private meta def mkLogFactor (v D : ℕ) : MetaM (ℕ × Expr × Expr) := do
  let (app, p, Q) ← mkLogPos 1 v D
  -- `mkLogPos 1 v D` concludes `Real.IsNear (Real.log (↑(v+1)/↑(v−1))) false p Q 1 D`.
  let ty := mkIsNearTy (mkRealFn ``Real.log (mkCastDivR (v + 1) (v - 1))) false p Q 1 D
  return (p, ty, app)

/-- `(Q, D)` for `log 2` to `1/E`: the per-factor precision `D = 15E` and the least power of two
`Q ≥ 2D`. -/
private meta def log2QD (E : ℕ) : ℕ × ℕ :=
  let D := 15 * E
  (2 ^ Nat.clog 2 (2 * D), D)

open Lean Elab Term Meta in
/-- `(P, Q, proof)` with `proof : Real.IsNear (Real.log 2) false P Q 1 E`, from the Machin
decomposition `P = 7p₁ + 5p₂ + 3p₃`. -/
meta def mkLog2Proof (E : ℕ) : MetaM (ℕ × ℕ × Expr) := do
  let (Q, D) := log2QD E
  let (p₁, t₁, h₁) ← mkLogFactor 31 D
  let (p₂, t₂, h₂) ← mkLogFactor 49 D
  let (p₃, t₃, h₃) ← mkLogFactor 161 D
  -- Lift each factor proof to its own auxiliary lemma so the combined term stays small and
  -- `maxSharing` stays cheap.
  let c₁ ← mkBoundAux t₁ h₁
  let c₂ ← mkBoundAux t₂ h₂
  let c₃ ← mkBoundAux t₃ h₃
  let P := 7 * p₁ + 5 * p₂ + 3 * p₃
  let app := mkAppN (mkConst ``log2_combine)
    #[natLitShared p₁, natLitShared p₂, natLitShared p₃, natLitShared Q, natLitShared D,
      natLitShared E, natLitShared P,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, c₁, c₂, c₃]
  return (P, Q, app)

open Lean Elab Term Meta in
/-- The dyadic numerator of the factor `log((v+1)/(v−1))` at precision `1/D`, without a proof. -/
private meta def mkLogFactorVal (v D : ℕ) : MetaM ℕ := do
  let (p, _, _, _) ← logCore 1 v D
  return p

open Lean Elab Term Meta in
/-- `(P, Q)` with `P/Q ≈ log 2` to precision `1/E`, without a proof. -/
meta def log2ValAt (E : ℕ) : MetaM (ℕ × ℕ) := do
  let (Q, D) := log2QD E
  let P := 7 * (← mkLogFactorVal 31 D) + 5 * (← mkLogFactorVal 49 D)
    + 3 * (← mkLogFactorVal 161 D)
  return (P, Q)

open Lean Elab Term Meta in
/-- `log2_approx% E : ℚ` is the dyadic rational `P/Q` approximating `log 2` to `1/E`, without a
proof (the enclosure is `log2_near%`). -/
elab "log2_approx% " En:num : term => do
  let (P, Q) ← log2ValAt En.getNat
  mkNatDyadic P Q

open Lean Elab Term Meta in
/-- The dyadic numerator of `log 2 ≈ P/Q` at precision `1/E`, as a literal. -/
elab "log2Num% " En:num : term => do return natLitShared (← log2ValAt En.getNat).1

open Lean Elab Term Meta in
/-- The dyadic denominator (`2^k`) of `log 2 ≈ P/Q` at precision `1/E`, as a literal. -/
elab "log2Den% " En:num : term => do return natLitShared (← log2ValAt En.getNat).2

open Lean Elab Term Meta in
/-- `log2_near% E` : a proof of `Real.IsNear (Real.log 2) false P Q 1 E` from `mkLog2Proof`. -/
elab "log2_near% " En:num : term => do
  let (_, _, pf) ← mkLog2Proof En.getNat
  return pf

/-! ### Reusable named `log 2` constants

Fixed-precision `IsNear` enclosures of `log 2`, each kernel-checked once and referenced in place of
a fresh Machin certificate. -/

/-- `log 2` to `1/10¹⁵` as an `IsNear` enclosure with literal dyadic fields. -/
theorem log2_near_15 :
    Real.IsNear (Real.log 2) false (log2Num% 1000000000000000) (log2Den% 1000000000000000)
      1 1000000000000000 :=
  log2_near% 1000000000000000

/-- `log 2` to `1/10⁵⁰` as an `IsNear` enclosure with literal dyadic fields. -/
theorem log2_near_50 :
    Real.IsNear (Real.log 2)
      false (log2Num% 100000000000000000000000000000000000000000000000000)
      (log2Den% 100000000000000000000000000000000000000000000000000)
      1 100000000000000000000000000000000000000000000000000 :=
  log2_near% 100000000000000000000000000000000000000000000000000

open Lean Elab Term Meta in
/-- `mkConstTier?` for `log 2` (tiers `log2_near_15`, `log2_near_50`). -/
meta def mkLog2Tier? (E : ℕ) (weaken : Bool := false) : MetaM (Option (ℕ × ℕ × ℕ × Expr)) :=
  mkConstTier? (mkRealFn ``Real.log mkRealTwo) ``log2_near_15 ``log2_near_50 log2ValAt E weaken

end BSN
