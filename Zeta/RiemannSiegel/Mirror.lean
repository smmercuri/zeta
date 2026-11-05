/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Zeta.RiemannSiegel.Deform

/-!
# The mirror Riemann–Siegel contour integral

Siegel's identity pairs the Riemann–Siegel contour integral `I(s, a)` of
`Zeta/RiemannSiegel/Integral.lean` with its reflection across the real axis,
`Ĩ(s, a) = conj (I(conj s, a))` (`riemann_siegel_zero.tex`, `def:rsz_mirror`). Taking the mirror by
conjugation rather than by a second contour is what keeps it free of a second branch of the power:
`Ĩ` needs no contour and no integral of its own, and inherits everything already proved about `I`.

The functional-equation factor `χ` that completes Siegel's identity is *not* Riemann–Siegel
mathematics and lives in `Zeta/Analysis/SpecialFunctions/GammaFactor.lean`.

## Main results

* `Zeta.RiemannSiegel.mirrorContourIntegral`, `Zeta.RiemannSiegel.mirrorHankelIntegral`: the
  mirrors of `Zeta.RiemannSiegel.contourIntegral` and `Zeta.RiemannSiegel.hankelIntegral`;
* `Zeta.RiemannSiegel.mirrorContourIntegral_one_sub_eq`:
  `Ĩ(1-s, ½) = -e^{-iπ(2-s)/4} cos(πs/2) Φ̃(1-s)` for `Re s > 1`;
* `Zeta.RiemannSiegel.mirrorHankelIntegral_eq_integral`: `Φ̃` as an honest integral,
  `Φ̃(s) = ∫_0^∞ ρ^{-s} e^{-πρ²} / sin (πρ e^{-iπ/4}) dρ`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- The **mirror Riemann–Siegel contour integral** `Ĩ(s, a) = conj (I(conj s, a))`. -/
noncomputable def mirrorContourIntegral (s : ℂ) (a : ℝ) : ℂ :=
  starRingEnd ℂ (contourIntegral (starRingEnd ℂ s) a)

/-- The **mirror Hankel ray integrand** `ρ ↦ ρ^{-s} e^{-πρ²} / sin (πρ e^{-iπ/4})`, the pointwise
conjugate of `Zeta.RiemannSiegel.hankelIntegrand`. -/
noncomputable def mirrorHankelIntegrand (s : ℂ) (ρ : ℝ) : ℂ :=
  (ρ : ℂ) ^ (-s) * exp (-(π * (ρ : ℂ) ^ 2)) / sin (π * ρ * exp (-((π / 4 : ℝ) * I)))

/-- The **mirror Hankel ray integral** `Φ̃(s) = conj (Φ(conj s))`. -/
noncomputable def mirrorHankelIntegral (s : ℂ) : ℂ :=
  starRingEnd ℂ (hankelIntegral (starRingEnd ℂ s))

/-- **The mirror Hankel ray integrand is the conjugate of the Hankel ray integrand.** -/
theorem mirrorHankelIntegrand_eq_conj (s : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    mirrorHankelIntegrand s ρ = starRingEnd ℂ (hankelIntegrand (starRingEnd ℂ s) ρ) := by
  have hcpow : ((ρ : ℂ)) ^ (-s) = starRingEnd ℂ ((ρ : ℂ) ^ (-(starRingEnd ℂ s))) := by
    simpa [Complex.conj_ofReal] using Complex.conj_cpow (ρ : ℂ) (-s)
      (by rw [Complex.arg_ofReal_of_nonneg hρ]; exact fun h ↦ Real.pi_ne_zero h.symm)
  have hexp : exp (-((π : ℂ) * (ρ : ℂ) ^ 2))
      = starRingEnd ℂ (exp (-((π : ℂ) * (ρ : ℂ) ^ 2))) := by
    rw [← Complex.exp_conj]; simp
  have hsin : sin ((π : ℂ) * ρ * exp (-((π / 4 : ℝ) * I)))
      = starRingEnd ℂ (sin ((π : ℂ) * ρ * exp ((π / 4 : ℝ) * I))) := by
    rw [← Complex.sin_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  rw [mirrorHankelIntegrand, hankelIntegrand, map_div₀, map_mul, ← hcpow, ← hexp, ← hsin]

/-- **Absolute convergence of the mirror Hankel ray integral** `Φ̃(s)`, for `Re s < 0`. -/
theorem integrableOn_mirrorHankelIntegrand {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (mirrorHankelIntegrand s) (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_hankelIntegrand (s := starRingEnd ℂ s) (by simpa using hs)
  have heq : ∀ ρ ∈ Set.Ioi (0 : ℝ),
      mirrorHankelIntegrand s ρ = starRingEnd ℂ (hankelIntegrand (starRingEnd ℂ s) ρ) :=
    fun ρ hρ ↦ mirrorHankelIntegrand_eq_conj s (le_of_lt hρ)
  refine Integrable.mono' h.norm ?_ ?_
  · refine (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ using (heq ρ hρ).symm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ using
      (heq ρ hρ ▸ (Complex.norm_conj _)).le

/-- **The mirror Hankel ray integral is an honest integral**,
`Φ̃(s) = ∫_0^∞ ρ^{-s} e^{-πρ²} / sin (πρ e^{-iπ/4}) dρ`
(`riemann_siegel_zero.tex`, `def:rsz_phi_mirror`). -/
theorem mirrorHankelIntegral_eq_integral (s : ℂ) :
    mirrorHankelIntegral s = ∫ ρ in Set.Ioi (0 : ℝ), mirrorHankelIntegrand s ρ := by
  rw [mirrorHankelIntegral, hankelIntegral, ← integral_conj]
  exact setIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦
    (mirrorHankelIntegrand_eq_conj s (le_of_lt hρ)).symm

/-- **The mirror contour integral in Hankel form**:
`Ĩ(1-s, ½) = -e^{-iπ(2-s)/4} cos (πs/2) Φ̃(1-s)` for `Re s > 1`
(`riemann_siegel_zero.tex`, `lem:rsz_mirror`). -/
theorem mirrorContourIntegral_one_sub_eq {s : ℂ} (hs : 1 < s.re) :
    mirrorContourIntegral (1 - s) (1 / 2)
      = -(exp (-((π / 4 : ℝ) * I * (2 - s))) * cos ((π : ℂ) * s / 2)) *
          mirrorHankelIntegral (1 - s) := by
  have hz : ((1 : ℂ) - (starRingEnd ℂ) s).re < 0 := by
    simp only [sub_re, one_re, conj_re]
    linarith
  have hexp : (starRingEnd ℂ) (exp ((π / 4 : ℝ) * I * (1 + ((1 : ℂ) - (starRingEnd ℂ) s))))
      = exp (-((π / 4 : ℝ) * I * (2 - s))) := by
    rw [← exp_conj]
    congr 1
    simp only [map_mul, map_add, map_one, map_sub, conj_conj, conj_I, conj_ofReal]
    ring
  have hsin : (starRingEnd ℂ) (sin ((π : ℂ) * ((1 : ℂ) - (starRingEnd ℂ) s) / 2))
      = cos ((π : ℂ) * s / 2) := by
    rw [← sin_conj, show (starRingEnd ℂ) ((π : ℂ) * ((1 : ℂ) - (starRingEnd ℂ) s) / 2)
        = (π : ℂ) / 2 - (π : ℂ) * s / 2 by
      simp only [map_div₀, map_mul, map_sub, map_one, conj_conj, conj_ofReal, map_ofNat]
      ring]
    exact sin_pi_div_two_sub _
  rw [mirrorContourIntegral, mirrorHankelIntegral, map_sub, map_one,
    contourIntegral_half_eq_neg_exp_mul_sin_mul_hankelIntegral hz, map_mul, map_neg, map_mul,
    hexp, hsin]

end Zeta.RiemannSiegel
