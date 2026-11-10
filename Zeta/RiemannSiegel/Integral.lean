/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Zeta.RiemannSiegel.Kernel
public import Zeta.RiemannSiegel.Power

/-!
# The Riemann–Siegel contour integral

The Riemann–Siegel formula rests on the contour integral `I(s, a) = ∫_{L(a)} x^{-s} G(x) dx` of the
kernel `Zeta.RiemannSiegel.kernel` against the branch `Zeta.RiemannSiegel.slantCpow` of
`x ↦ x^{-s}`, taken along the slanted line `Zeta.RiemannSiegel.line` (`riemann_siegel.tex`,
`def:rs_integral`).

The integral converges absolutely for every `s`: the Gaussian factor `e^{iπx²}` of the kernel
contributes `e^{-2πw(a+w)}`, whose square-exponential decay beats both the polynomial factor
`‖x‖^{-Re s}` and the exponential factor `e^{slantArg x · Im s}` coming from the power (the latter
is bounded outright, since the argument along the contour stays below `3π/4` in modulus). The sharp
estimate on the critical line is in `Zeta/RiemannSiegel/Bound.lean`.

## Main results

* `Zeta.RiemannSiegel.integrand`: the integrand `x ↦ x^{-s} G(x)`;
* `Zeta.RiemannSiegel.contourIntegrand`, `Zeta.RiemannSiegel.norm_contourIntegrand`,
  `Zeta.RiemannSiegel.norm_contourIntegrand_eq_exp`: its restriction
  `w ↦ L(a)(w)^{-s} G(L(a)(w))` to the contour, and two forms of the modulus of that;
* `Zeta.RiemannSiegel.continuous_contourIntegrand`: continuity along a contour missing the
  integers;
* `Zeta.RiemannSiegel.norm_contourIntegrand_le_exp`: a Gaussian majorant, uniform for `s` in a box;
* `Zeta.RiemannSiegel.integrable_contourIntegrand`,
  `Zeta.RiemannSiegel.integrable_contourIntegrand_of_le_half`: absolute convergence;
* `Zeta.RiemannSiegel.norm_kernel_line_le`: a Gaussian bound `‖G(L(a)(w))‖ = O(e^{-πw²})` for the
  kernel alone;
* `Zeta.RiemannSiegel.slantIntegral`: the integral of an arbitrary integrand along `L(a)`;
* `Zeta.RiemannSiegel.contourIntegral`: the contour integral `I(s, a)`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Complex

/-- The modulus of a purely imaginary doubling: `‖2i z‖ = 2‖z‖`. -/
theorem norm_two_mul_I_mul (z : ℂ) : ‖2 * I * z‖ = 2 * ‖z‖ := by simp

/-- Pulling the norm inside a `(1 + i)`-scaled integral: `‖(1 + i) ∫ F‖ ≤ √2 ∫ ‖F‖`. -/
theorem norm_one_add_I_mul_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : α → ℂ) : ‖(1 + I) * ∫ w, F w ∂μ‖ ≤ Real.sqrt 2 * ∫ w, ‖F w‖ ∂μ := by
  rw [norm_mul, norm_one_add_I]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.sqrt_nonneg 2)

end Complex

namespace Zeta.RiemannSiegel

/-- The Riemann–Siegel integrand `x ↦ x^{-s} G(x)`, in which the power is taken in the branch
`Zeta.RiemannSiegel.slantCpow` adapted to the contour. -/
noncomputable def integrand (s x : ℂ) : ℂ :=
  slantCpow x (-s) * kernel x

/-- The integrand of the Riemann–Siegel contour integral, `w ↦ L(a)(w)^{-s} G(L(a)(w))`. -/
noncomputable def contourIntegrand (s : ℂ) (a w : ℝ) : ℂ :=
  integrand s (line a w)

/-- The modulus of the integrand, with the kernel's denominator `2i sin (πx)` split off. -/
theorem norm_contourIntegrand (s : ℂ) (a w : ℝ) :
    ‖contourIntegrand s a w‖
      = ‖slantCpow (line a w) (-s) * exp (π * I * line a w ^ 2)‖ /
        (2 * ‖sin (π * line a w)‖) := by
  rw [contourIntegrand, integrand, kernel_eq_div_two_mul_I_mul_sin, ← mul_div_assoc, norm_div,
    norm_two_mul_I_mul]

/-- The modulus of the integrand as an exponential, the logarithm of the modulus and the
argument of the power having been separated from the Gaussian and from the kernel's denominator. -/
theorem norm_contourIntegrand_eq_exp (s : ℂ) {a : ℝ} (ha0 : 0 < a) (w : ℝ) :
    ‖contourIntegrand s a w‖
      = Real.exp (Real.log ‖line a w‖ * (-s).re + slantArg (line a w) * s.im) *
        (Real.exp (-(2 * π * (a + w) * w)) / (2 * ‖sin (π * line a w)‖)) := by
  have hx0 : line a w ≠ 0 := line_ne_zero ha0.ne' w
  rw [norm_contourIntegrand, norm_mul, norm_slantCpow hx0, Complex.norm_exp_pi_mul_I_mul_sq,
    line_re, line_im, Real.rpow_def_of_pos (norm_pos_iff.2 hx0), Complex.neg_im, mul_neg,
    Real.exp_neg (slantArg (line a w) * s.im), div_inv_eq_mul,
    ← Real.exp_add (Real.log ‖line a w‖ * (-s).re) (slantArg (line a w) * s.im)]
  ring

/-- The integrand is continuous along a contour that misses the integers. -/
theorem continuous_contourIntegrand (s : ℂ) {a : ℝ} (ha0 : 0 < a)
    (hsin : ∀ w : ℝ, sin (π * line a w) ≠ 0) : Continuous (contourIntegrand s a) := by
  have hline := continuous_line a
  have hrot : Continuous fun w : ℝ ↦ exp ((π / 4 : ℝ) * I) * line a w := continuous_const.mul hline
  have hpow : Continuous fun w : ℝ ↦ (exp ((π / 4 : ℝ) * I) * line a w) ^ (-s) :=
    hrot.cpow continuous_const fun w ↦ mem_slitPlane_iff.2 <| Or.inl <| by
      rw [re_exp_pi_div_four_mul_I_mul_line]
      exact div_pos ha0 (Real.sqrt_pos.2 two_pos)
  have hker : Continuous fun w : ℝ ↦ kernel (line a w) := by
    simp only [kernel_eq_div_two_mul_I_mul_sin]
    exact Continuous.div (by fun_prop) (by fun_prop) fun w ↦ by simpa [I_ne_zero] using hsin w
  unfold contourIntegrand integrand slantCpow
  exact (continuous_const.mul hpow).mul hker

/-- A Gaussian majorant for the Riemann–Siegel integrand, along any contour whose kernel
denominator is bounded below by `c`. The bound is stated through upper bounds `σ, τ` for
`|Re s|, |Im s|`, so that it is uniform for `s` in a box. -/
theorem norm_contourIntegrand_le_exp {s : ℂ} {a c σ τ : ℝ} (ha0 : 0 < a) (hc : 0 < c)
    (hsin : ∀ w : ℝ, c ≤ ‖sin (π * line a w)‖) (hσ : |s.re| ≤ σ) (hτ : |s.im| ≤ τ) (w : ℝ) :
    ‖contourIntegrand s a w‖
      ≤ Real.exp (3 * π * τ / 4 + (|Real.log (a / Real.sqrt 2)| + a) * σ + 2 * σ ^ 2 / π +
          π * a ^ 2) / (2 * c) * Real.exp (-(π / 2) * w ^ 2) := by
  have hpi := Real.pi_pos
  set L : ℝ := |Real.log (a / Real.sqrt 2)|
  have hL0 : 0 ≤ L := abs_nonneg _
  have hσ0 : 0 ≤ σ := (abs_nonneg _).trans hσ
  have habs : |Real.log ‖line a w‖| ≤ L + a + 2 * |w| := abs_log_norm_line_le ha0 w
  -- bound the exponent, term by term
  have harg : slantArg (line a w) * s.im ≤ 3 * π * τ / 4 :=
    (slantArg_line_mul_im_le s ha0 w).trans (by gcongr)
  have hlog : Real.log ‖line a w‖ * (-s).re ≤ (L + a) * σ + 2 * σ ^ 2 / π + π / 2 * w ^ 2 := by
    have h1 : Real.log ‖line a w‖ * (-s).re ≤ |Real.log ‖line a w‖| * |s.re| := by
      simpa [abs_mul] using le_abs_self (Real.log ‖line a w‖ * (-s).re)
    have h2 : |Real.log ‖line a w‖| * |s.re| ≤ (L + a + 2 * |w|) * σ :=
      (mul_le_mul_of_nonneg_right habs (abs_nonneg _)).trans (by gcongr)
    -- `2A|w| ≤ (π/2)w² + 2A²/π` is `(π|w| - 2A)² ≥ 0` divided by `2π`
    have h3 : 2 * σ * |w| ≤ π / 2 * w ^ 2 + 2 * σ ^ 2 / π := by
      rw [← sq_abs w, ← sub_nonneg, show π / 2 * |w| ^ 2 + 2 * σ ^ 2 / π - 2 * σ * |w|
        = (π * |w| - 2 * σ) ^ 2 / (2 * π) by field_simp; ring]
      positivity
    nlinarith [h1, h2, h3]
  have hgauss : -(2 * π * (a + w) * w) ≤ π * a ^ 2 - π * w ^ 2 := by
    nlinarith [sq_nonneg (a + w)]
  rw [norm_contourIntegrand_eq_exp s ha0, ← mul_div_assoc, div_mul_eq_mul_div, ← Real.exp_add,
    ← Real.exp_add]
  gcongr Real.exp ?_ / ?_ <;> linarith [hsin w]

/-- Absolute convergence of the Riemann–Siegel contour integral, along any contour whose
kernel denominator is bounded below. -/
theorem integrable_contourIntegrand (s : ℂ) {a c : ℝ} (ha0 : 0 < a) (hc : 0 < c)
    (hsin : ∀ w : ℝ, c ≤ ‖sin (π * line a w)‖) : Integrable (contourIntegrand s a) := by
  have hsin0 : ∀ w : ℝ, sin (π * line a w) ≠ 0 := fun w ↦
    norm_pos_iff.1 (lt_of_lt_of_le hc (hsin w))
  exact Integrable.mono' ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < π / 2)).const_mul _)
    (continuous_contourIntegrand s ha0 hsin0).aestronglyMeasurable
    (.of_forall (norm_contourIntegrand_le_exp ha0 hc hsin le_rfl le_rfl))

/-- Absolute convergence along a contour crossing the real axis inside `(0, ½]`. -/
theorem integrable_contourIntegrand_of_le_half (s : ℂ) {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    Integrable (contourIntegrand s a) :=
  integrable_contourIntegrand s ha0 (c := min (1 / 2) (a / Real.sqrt 2))
    (lt_min (by norm_num) (by positivity))
    fun w ↦ (min_le_min le_rfl (norm_line_ge a w)).trans (norm_sin_pi_mul_line_ge_min ha0.le ha w)

/-- A Gaussian bound for the kernel along a contour crossing the real axis inside `(0, ½]`: the
kernel's Gaussian numerator decays like `e^{-πw²}` while its denominator stays bounded away from
zero. -/
theorem norm_kernel_line_le {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) (w : ℝ) :
    ‖kernel (line a w)‖
      ≤ Real.exp (π * a ^ 2) / (Real.sqrt 2 * a) * Real.exp (-(π * w ^ 2)) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt' one_pos).2 (by norm_num)
  -- on `(0, ½]` the crude bound `a/√2` is the smaller of the two, so the `min` disappears
  have hlow : a / Real.sqrt 2 ≤ ‖sin (π * line a w)‖ :=
    le_trans (le_min (by rw [div_le_iff₀ h2]; nlinarith) (norm_line_ge a w))
      (norm_sin_pi_mul_line_ge_min ha0.le ha w)
  rw [kernel_eq_div_two_mul_I_mul_sin, norm_div, Complex.norm_exp_pi_mul_I_mul_sq, line_re,
    line_im, Complex.norm_two_mul_I_mul,
    show Real.exp (π * a ^ 2) / (Real.sqrt 2 * a) * Real.exp (-(π * w ^ 2))
      = Real.exp (π * a ^ 2 + -(π * w ^ 2)) / (2 * (a / Real.sqrt 2)) by
      rw [Real.exp_add, show 2 * (a / Real.sqrt 2) = 2 / Real.sqrt 2 * a by ring, Real.div_sqrt]
      ring]
  gcongr
  nlinarith [sq_nonneg (a + w), Real.pi_pos]

/-- The integral along the slanted contour `L(a)`, `∫_{L(a)} f = (1 + i) ∫_ℝ f(L(a)(w)) dw`. -/
noncomputable def slantIntegral (f : ℂ → ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, f (line a w)

/-- The Riemann–Siegel contour integral `I(s, a) = ∫_{L(a)} x^{-s} G(x) dx`, parametrised by
the slanted contour `Zeta.RiemannSiegel.line`, whose constant velocity is `1 + i`. -/
noncomputable def contourIntegral (s : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, contourIntegrand s a w

theorem contourIntegral_eq_slantIntegral (s : ℂ) (a : ℝ) :
    contourIntegral s a = slantIntegral (integrand s) a :=
  rfl

end Zeta.RiemannSiegel
