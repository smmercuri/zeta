/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannSiegel.Moment
public import Zeta.Zeros.HardyZ

/-!
# The Riemann–Siegel approximant: definitions

The objects a Riemann–Siegel *certificate* is stated in terms of, kept apart from the proofs
(`Zeta.RiemannSiegel.ZeroOrder`, `Correction`, `Linear`, `FirstOrder`) so that a certificate file
stays clear of `PrimeNumberTheoremAnd`'s rectangle-residue apparatus. The bound
`abs_hardyZRemainderRS_le` is attached where the certificates are consumed.

## Main definitions

- `Zeta.RiemannSiegel.mainSumOfPhase`: `2 ∑_{n ≤ ν} n^{-1/2} cos(θ − t log n)`.
- `Zeta.RiemannSiegel.correction`, `Zeta.RiemannSiegel.correctionLinear`: `Ψ(p)` and `C₁(p)`.
- `hardyZApproximantRS`, `hardyZErrorBoundRS` (and the linear-free `…RS₀` variants): the
  approximant a certificate evaluates and the closed-form bound its margins are checked against.
-/
@[expose] public section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/-- The Riemann–Siegel main sum at a prescribed phase `θ`,
`S(θ, t, ν) = 2 ∑_{n = 1}^{ν} n^{-1/2} cos (θ − t log n)`. -/
noncomputable def mainSumOfPhase (θ t : ℝ) (ν : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ν, Real.cos (θ - t * Real.log n) / Real.sqrt n

/-- The Riemann–Siegel correction function `Ψ(p) = 2 Re(e^{−iπ/8} M(p))`
(`riemann_siegel_first.tex`, `def:rsf_correction`). -/
noncomputable def correction (p : ℝ) : ℝ :=
  2 * (exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2)).re

/-- The first classical Riemann–Siegel coefficient `C₁(p) = −Ψ'''(p)/(96π²)`
(`riemann_siegel_first.tex`, `def:rsf_c1`), in its moment form. -/
noncomputable def correctionLinear (p : ℝ) : ℝ :=
  2 * (exp (-((π / 8 : ℝ) * I)) *
    (-(1 / 2) * modelMoment 1 (p : ℂ) (1 / 2) - 2 * π * I / 3 * modelMoment 3 (p : ℂ) (1 / 2))).re

end Zeta.RiemannSiegel

open Zeta.RiemannSiegel

/-- The first-order Riemann–Siegel approximant for Hardy's `Z`: the main sum at the order-`2`
Stirling phase and cutoff `ν = ⌊√T⌋`, corrected by `(-1)^ν T^{-1/4}(Ψ(p) + C₁(p)/√T)` at the
fractional part `p = √T - ν`. Unlike `hardyZApproximantEM`, it takes no parameters. -/
noncomputable abbrev hardyZApproximantRS (t : ℝ) : ℝ :=
  mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ⌊Real.sqrt (t / (2 * π))⌋₊
    - (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
        * (correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
          + correctionLinear (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
              / Real.sqrt (t / (2 * π)))

/-- The error term of the first-order Riemann–Siegel approximant, `Z(t) − Z̃^{RS}(t)`. It is
bounded by `abs_hardyZRemainderRS_le`. -/
noncomputable abbrev hardyZRemainderRS (t : ℝ) : ℝ := Zeta.hardyZ t - hardyZApproximantRS t

/-- **The first-order Riemann–Siegel error bound**, `25/4 · T^{-5/4} + T^{-15/4}/32` with
`T = t/2π`. -/
noncomputable abbrev hardyZErrorBoundRS (t : ℝ) : ℝ :=
  25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ) + 1 / 32 * (t / (2 * π)) ^ (-(15 / 4) : ℝ)

/-- The linear-free first-order Riemann–Siegel approximant: `hardyZApproximantRS` with
correction term `Ψ(p)` alone. Its error bound is `hardyZErrorBoundRS₀`. -/
noncomputable abbrev hardyZApproximantRS₀ (t : ℝ) : ℝ :=
  mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ⌊Real.sqrt (t / (2 * π))⌋₊
    - (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
        * correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)

/-- The error term of the linear-free approximant, `Z(t) − Z̃₀^{RS}(t)`. -/
noncomputable abbrev hardyZRemainderRS₀ (t : ℝ) : ℝ := Zeta.hardyZ t - hardyZApproximantRS₀ t

/-- The error bound for the linear-free approximant: `hardyZErrorBoundRS` plus the discarded
linear term's uniform size `(13/10)·T^{-3/4}`. -/
noncomputable abbrev hardyZErrorBoundRS₀ (t : ℝ) : ℝ :=
  hardyZErrorBoundRS t + 13 / 10 * (t / (2 * π)) ^ (-(3 / 4) : ℝ)
