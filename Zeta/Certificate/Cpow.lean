module

public import Enclosure.BinarySplit.Tactic.Enclosures
public meta import Enclosure.BinarySplit.Tactic.Enclosures

/-!
# ζ-term rectangle builders `n^s`

The complex-power building blocks for the zeta head sum: metaprograms that assemble a certified
rectangle enclosure of a Dirichlet-series term `n^(σ + i·t)`. These are specific to the zeta
certificates, so they live here rather than in the general `Enclosure` library. They are built
on the library's real and complex enclosure combinators (`√`, `log`, `cos`/`sin` of an enclosure,
and `×`).
-/
@[expose] public section


namespace BSN
open Enclosure
open Lean Meta

/-- `√↑n = √(↑n/↑1)`: transports the ratio-form sqrt certificate onto the plain integer cast, so
the enclosed value carries no constant `1` cast. -/
theorem sqrt_natCast_div_one (n : ℕ) :
    Real.sqrt (n : ℝ) = Real.sqrt ((n : ℝ) / ((nat_lit 1 : ℕ) : ℝ)) := by
  rw [show ((nat_lit 1 : ℕ) : ℝ) = 1 from Nat.cast_one, div_one]

/-- Enclosure of `√↑n` (value `Real.sqrt ↑n`, carrying no constant cast): the ratio-form
`√(↑n/↑1)` certificate renamed onto `√↑n` through `sqrt_natCast_div_one`. -/
meta def mkSqrtNatNear (n D : ℕ) : MetaM RNear := do
  let base ← mkSqrtNear n 1 D
  let he := mkApp (mkConst ``sqrt_natCast_div_one) (natLitShared n)
  ofEqNear (mkRealFn ``Real.sqrt (mkNatCastR n)) he base

/-- Build a rectangle enclosure of `n^(σ + i·τ)` for a half-integer real part `σ = m2/2` and a
signed rational `τ = tnum/tden`: the magnitude is `n^σ = √(n^m2)` (the reciprocal under the
square root when `m2 < 0`), the phase runs through `cos/sin(|τ|·log n)` with the `sin` component
negated for `τ < 0` (`sin` is odd, `cos` even). The `log n` enclosure is `mkLogNearOf`, so any
`n ≥ 1` works (range-reduced as needed). Covers the zeta building blocks `n^(−s)`, `N^(1−s)`,
`N^(−s)`, `N^(−s−(2k−1))`. -/
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
