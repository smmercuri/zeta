/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Zeta.Analysis.SpecialFunctions.Gaussian
public import Zeta.RiemannSiegel.Integral

/-!
# The Riemann–Siegel contour integral is entire

The contour integral `I(s, a) = ∫_{L(a)} x^{-s} G(x) dx` of `Zeta/RiemannSiegel/Integral.lean` is
an entire function of `s` (`riemann_siegel_zero.tex`, `lem:rsz_entire`). This is differentiation
under the integral sign: the integrand is `e^{-s Log x} G(x)` in the branch
`Zeta.RiemannSiegel.slantLog`, so its `s`-derivative is `-Log x` times itself, and the Gaussian
majorant `Zeta.RiemannSiegel.norm_contourIntegrand_le_exp` (uniform for `s` in a box)
survives multiplication by `‖Log L(a)(w)‖ = O(|w|)`.

## Main results

* `Zeta.RiemannSiegel.hasDerivAt_contourIntegrand`: the `s`-derivative of the integrand;
* `Zeta.RiemannSiegel.differentiable_contourIntegral`,
  `Zeta.RiemannSiegel.differentiable_contourIntegral_of_le_half`: `s ↦ I(s, a)` is entire.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- The `s`-derivative of the Riemann–Siegel integrand. -/
theorem hasDerivAt_contourIntegrand {a : ℝ} (ha0 : 0 < a) (s : ℂ) (w : ℝ) :
    HasDerivAt (fun u ↦ contourIntegrand u a w)
      (-slantLog (line a w) * contourIntegrand s a w) s := by
  -- the branch cut is invisible to `slantCpow_eq_exp_mul_slantLog`, so this is `d/ds e^{-s Log x}`
  have hexp : ∀ u : ℂ, contourIntegrand u a w
      = exp (-u * slantLog (line a w)) * kernel (line a w) := fun u ↦ by
    rw [contourIntegrand, integrand, slantCpow_eq_exp_mul_slantLog (line_ne_zero ha0.ne' w)]
  simp only [hexp]
  exact (((hasDerivAt_neg' (𝕜 := ℂ) s).mul_const (slantLog (line a w))).cexp.mul_const
    (kernel (line a w))).congr_deriv (by ring)

/-- The Riemann–Siegel contour integral is an entire function of `s`
(`riemann_siegel_zero.tex`, `lem:rsz_entire`), along any contour whose kernel denominator is
bounded below. -/
theorem differentiable_contourIntegral {a c : ℝ} (ha0 : 0 < a) (hc : 0 < c)
    (hsin : ∀ w : ℝ, c ≤ ‖sin (π * line a w)‖) :
    Differentiable ℂ fun s ↦ contourIntegral s a := by
  have hsin0 : ∀ w : ℝ, sin (π * line a w) ≠ 0 := fun w ↦
    norm_pos_iff.1 (lt_of_lt_of_le hc (hsin w))
  intro s₀
  simp only [contourIntegral]
  -- the Gaussian majorant, uniform on the unit ball about `s₀` …
  obtain ⟨M, hMle⟩ : ∃ M : ℝ, ∀ s : ℂ, |s.re| ≤ |s₀.re| + 1 → |s.im| ≤ |s₀.im| + 1 →
      ∀ w : ℝ, ‖contourIntegrand s a w‖ ≤ M * Real.exp (-(π / 2) * w ^ 2) :=
    ⟨_, fun _ ↦ norm_contourIntegrand_le_exp ha0 hc hsin⟩
  -- … and the at most linear growth of the logarithmic factor the derivative contributes
  obtain ⟨N, hN0, hNle⟩ : ∃ N : ℝ, 0 < N ∧ ∀ w : ℝ, ‖slantLog (line a w)‖ ≤ N + 2 * |w| :=
    ⟨_, by positivity, norm_slantLog_line_le ha0⟩
  have hint : Integrable fun w : ℝ ↦ Real.exp (-(π / 2) * w ^ 2) * (M * N + 2 * M * |w|) := by
    simpa using integrable_exp_neg_mul_sq_mul_poly (by positivity) (M * N) (2 * M) 0 0
  have hbound : ∀ w : ℝ, ∀ s ∈ Metric.ball s₀ 1,
      ‖-slantLog (line a w) * contourIntegrand s a w‖
        ≤ Real.exp (-(π / 2) * w ^ 2) * (M * N + 2 * M * |w|) := by
    intro w s hs
    have hd : ‖s - s₀‖ ≤ 1 := by rw [Metric.mem_ball, Complex.dist_eq] at hs; exact hs.le
    have hre : |s.re| ≤ |s₀.re| + 1 := sub_le_iff_le_add'.1 <|
      ((abs_sub_abs_le_abs_sub s.re s₀.re).trans
        (by simpa using Complex.abs_re_le_norm (s - s₀))).trans hd
    have him : |s.im| ≤ |s₀.im| + 1 := sub_le_iff_le_add'.1 <|
      ((abs_sub_abs_le_abs_sub s.im s₀.im).trans
        (by simpa using Complex.abs_im_le_norm (s - s₀))).trans hd
    rw [norm_mul, norm_neg]
    calc ‖slantLog (line a w)‖ * ‖contourIntegrand s a w‖
        ≤ (N + 2 * |w|) * (M * Real.exp (-(π / 2) * w ^ 2)) :=
          mul_le_mul (hNle w) (hMle s hre him w) (norm_nonneg _) (by linarith [abs_nonneg w])
      _ = _ := by ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := s₀)
    (F := fun (s : ℂ) (w : ℝ) ↦ contourIntegrand s a w)
    (F' := fun (s : ℂ) (w : ℝ) ↦ -slantLog (line a w) * contourIntegrand s a w)
    (bound := fun w ↦ Real.exp (-(π / 2) * w ^ 2) * (M * N + 2 * M * |w|))
    (s := Metric.ball s₀ 1) (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun s ↦
      (continuous_contourIntegrand s ha0 hsin0).aestronglyMeasurable)
    (integrable_contourIntegrand s₀ ha0 hc hsin)
    (((continuous_slantLog_line ha0).neg.mul
      (continuous_contourIntegrand s₀ ha0 hsin0)).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)
    hint
    (Filter.Eventually.of_forall fun w s _ ↦
      hasDerivAt_contourIntegrand ha0 s w)).2.differentiableAt.const_mul (1 + I)

/-- The contour integral is entire along a contour crossing the real axis inside `(0, ½]`. -/
theorem differentiable_contourIntegral_of_le_half {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    Differentiable ℂ fun s ↦ contourIntegral s a :=
  differentiable_contourIntegral ha0 (c := min (1 / 2) (a / Real.sqrt 2))
    (lt_min (by norm_num) (by positivity))
    fun w ↦ (min_le_min le_rfl (norm_line_ge a w)).trans
      (norm_sin_pi_mul_line_ge_min ha0.le ha w)

end Zeta.RiemannSiegel
