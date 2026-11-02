/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.HalfPlane

/-!
# `Γ` and `ψ` on the right half-plane

Regularity of `Complex.Gamma` and `ψ = Complex.digamma = logDeriv Γ` on the open right half-plane
`{z : ℂ | 0 < z.re}`, in the half-plane forms mathlib does not provide.

## Main results

* `Complex.ne_neg_natCast_of_re_pos`: the pole-avoidance side condition;
* `Complex.differentiableAt_Gamma_of_re_pos`, `Complex.differentiableOn_Gamma_re_pos`,
  `Complex.analyticOnNhd_Gamma_re_pos`: regularity of `Γ` on `{0 < re}`;
* `Complex.differentiableOn_digamma_re_pos`, `Complex.differentiableAt_digamma`:
  regularity of `ψ` on `{0 < re}`;
* `Complex.isPreconnected_re_pos`: the half-plane itself.
-/
@[expose] public section


namespace Complex

/-- A complex number with positive real part is never a non-positive integer. -/
theorem ne_neg_natCast_of_re_pos {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -(m : ℂ) := by
  rintro rfl; exact absurd hz (by simp)

/-- **`Γ` is differentiable at every point of the right half-plane.** -/
theorem differentiableAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z :=
  Complex.differentiableAt_Gamma z (ne_neg_natCast_of_re_pos hz)

/-- The right half-plane is preconnected (indeed convex). -/
theorem isPreconnected_re_pos : IsPreconnected {z : ℂ | 0 < z.re} :=
  (convex_halfSpace_re_gt 0).isPreconnected

/-- `Complex.Gamma` is holomorphic on the right half-plane. -/
theorem differentiableOn_Gamma_re_pos : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} :=
  fun _ hz ↦ (differentiableAt_Gamma_of_re_pos hz).differentiableWithinAt

/-- `Complex.Gamma` is analytic on (a neighbourhood of each point of) the right half-plane. -/
theorem analyticOnNhd_Gamma_re_pos : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} :=
  differentiableOn_Gamma_re_pos.analyticOnNhd (isOpen_re_gt 0)

/-- `Complex.digamma = Γ'/Γ` is holomorphic on the right half-plane. -/
theorem differentiableOn_digamma_re_pos :
    DifferentiableOn ℂ Complex.digamma {z : ℂ | 0 < z.re} := by
  rw [Complex.digamma_def]
  exact (differentiableOn_Gamma_re_pos.deriv (isOpen_re_gt 0)).div differentiableOn_Gamma_re_pos
    fun _ hz ↦ Complex.Gamma_ne_zero_of_re_pos hz

/-- **Differentiability of the digamma function.** On the right half-plane `{Re > 0}`,
`ψ = Complex.digamma` is complex-differentiable. -/
theorem differentiableAt_digamma {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.digamma s :=
  (differentiableOn_digamma_re_pos.analyticOnNhd (isOpen_re_gt 0) s hs).differentiableAt

end Complex
