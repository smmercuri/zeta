/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Tactic.Enclosures
public meta import Enclosure.BinarySplit.Tactic.Enclosures

/-!
# ζ-term rectangle builders `n^s`

The complex-power building blocks for the zeta head sum: metaprograms that assemble a certified
rectangle enclosure of a Dirichlet-series term `n^(σ + i·t)`. They are specific to the zeta
certificates, so they live here rather than in the general `Enclosure` library.
-/
@[expose] public section


namespace BSN
open Enclosure
open Lean Meta

/-- `√↑n = √(↑n/↑1)`, relating the ratio-form sqrt certificate to the plain cast. -/
theorem sqrt_natCast_div_one (n : ℕ) :
    Real.sqrt (n : ℝ) = Real.sqrt ((n : ℝ) / ((nat_lit 1 : ℕ) : ℝ)) := by
  rw [show ((nat_lit 1 : ℕ) : ℝ) = 1 from Nat.cast_one, div_one]

/-- Enclosure of `√↑n`, with no constant `1` cast in the enclosed value. -/
meta def mkSqrtNatNear (n D : ℕ) : MetaM RNear := do
  let base ← mkSqrtNear n 1 D
  let he := mkApp (mkConst ``sqrt_natCast_div_one) (natLitShared n)
  ofEqNear (mkRealFn ``Real.sqrt (mkNatCastR n)) he base

/-- Rectangle enclosure of `n^(σ + i·τ)` (`n ≥ 1`) for a half-integer real part `σ = m2/2` and a
signed rational `τ = tnum/tden`: magnitude `√(n^m2)`, phase `cos/sin(|τ|·log n)` with the `sin`
component negated for `τ < 0`. Covers `n^(−s)`, `N^(1−s)`, `N^(−s)` and `N^(−s−(2k−1))`. -/
meta def mkCpowIntCNear (n : ℕ) (m2 tnum : ℤ) (tden D : ℕ) : MetaM CNear := do
  let magNear ← if m2 ≥ 0 then mkSqrtNear (n ^ m2.toNat) 1 D
                else mkInvImageNear (← mkSqrtNatNear (n ^ (-m2).toNat) D) D
  let logN ← mkLogNearOf n 1 D D
  let tlogN ← mulNear (← mkConstNear tnum.natAbs tden) logN
  let cosT ← mkCosImageNear tlogN D
  let sinT0 ← mkSinImageNear tlogN D
  let sinT ← if tnum < 0 then negNear sinT0 else pure sinT0
  let reN ← mulNear magNear cosT
  let imN ← mulNear magNear sinT
  return { re := reN, im := imN }

end BSN
