/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Zeta.RiemannSiegel.Gaussian
public import Zeta.RiemannSiegel.Integral

/-!
# The Riemann–Siegel model integral

Replacing the true integrand of `Zeta.RiemannSiegel.contourIntegral` by its Gaussian model at the
saddle leaves the **model integral**

`M(p) = ∫_{L(1/2)} e^{2πi(v − p)²} / (e^{iπv} − e^{−iπv}) dv`

(`riemann_siegel_first.tex`, `def:rsf_model`), which carries the whole of the first-order
correction to the Riemann–Siegel formula. The contour is the half-integer line `L(1/2)`, so the
denominator is bounded below by `Zeta.RiemannSiegel.norm_sin_pi_mul_line_ge` exactly as in the
order-zero chapter, and no new lower bound is needed. The contour parameter is carried along
nonetheless, because the unit shift of `ModelShift.lean` deforms `L(1/2)` out to `L(3/2)`.

The point of this file is the **half shift** `modelIntegral_add_half`, one of the two functional
equations that pin `M` algebraically.

## Main results

* `Zeta.RiemannSiegel.modelFun`, `Zeta.RiemannSiegel.modelIntegrand`,
  `Zeta.RiemannSiegel.modelIntegral`: the model integrand as a function of the complex variable, its
  restriction to `L(a)`, and the model integral `M(p) = modelIntegral p (1/2)`;
* `Zeta.RiemannSiegel.modelFun_add_one`: translation by one reverses the sign;
* `Zeta.RiemannSiegel.integrable_modelIntegrand`: absolute convergence, for every complex `p`;
* `Zeta.RiemannSiegel.norm_exp_two_pi_mul_I_mul_line_sub_sq`,
  `Zeta.RiemannSiegel.norm_exp_two_pi_mul_I_mul_line_sub_sq'`: the modulus of the model Gaussian
  along `L(½)`, with the square completed, and as a Gaussian in the distance to the centre;
* `Zeta.RiemannSiegel.norm_modelIntegral_le`: `|M(p)| ≤ e^{π(1/2 − p)²}/2` for real `p`;
* `Zeta.RiemannSiegel.modelIntegral_add_half`:
  `M(p + 1/2) = i e^{2πip} M(p) − i e^{iπ/8} e^{iπp}/√2`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- The **Riemann–Siegel model integrand** `m_p(x) = e^{2πi(x − p)²} / (e^{iπx} − e^{−iπx})`, whose
denominator is that of the Riemann–Siegel kernel `Zeta.RiemannSiegel.kernel`. -/
noncomputable def modelFun (p x : ℂ) : ℂ :=
  exp (2 * π * I * (x - p) ^ 2) / (exp (π * I * x) - exp (-(π * I * x)))

/-- The **integrand of the Riemann–Siegel model integral** along the contour `L(a)`. -/
noncomputable def modelIntegrand (p : ℂ) (a w : ℝ) : ℂ :=
  modelFun p (line a w)

/-- The **Riemann–Siegel model integral** `M(p) = ∫_{L(1/2)} m_p(v) dv`, taken here along the
contour `L(a)`, whose constant velocity is `1 + i`. -/
noncomputable def modelIntegral (p : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, modelIntegrand p a w

theorem modelIntegral_eq_slantIntegral (p : ℂ) (a : ℝ) :
    modelIntegral p a = slantIntegral (modelFun p) a :=
  rfl

/-- The model integrand with its denominator written as a sine. -/
theorem modelFun_eq_div_two_mul_I_mul_sin (p x : ℂ) :
    modelFun p x = exp (2 * π * I * (x - p) ^ 2) / (2 * I * sin (π * x)) := by
  rw [modelFun, show ((π : ℂ) * I * x) = ((π : ℂ) * x) * I by ring, exp_mul_I_sub_exp_neg_mul_I]

/-- The model integrand as a Gaussian multiple of the Riemann–Siegel kernel. -/
theorem modelFun_eq_mul_kernel (p x : ℂ) :
    modelFun p x = exp (2 * π * I * (x - p) ^ 2 - π * I * x ^ 2) * kernel x := by
  rw [modelFun, kernel, ← mul_div_assoc, ← exp_add,
    show 2 * (π : ℂ) * I * (x - p) ^ 2 - π * I * x ^ 2 + π * I * x ^ 2
      = 2 * π * I * (x - p) ^ 2 by ring]

/-- Translating the model integrand by one reverses its sign and shifts `p` by one. -/
theorem modelFun_add_one (p x : ℂ) : modelFun p (x + 1) = -modelFun (p - 1) x := by
  have hden : exp ((π : ℂ) * I * (x + 1)) - exp (-((π : ℂ) * I * (x + 1)))
      = -(exp ((π : ℂ) * I * x) - exp (-((π : ℂ) * I * x))) := by
    rw [show ((π : ℂ) * I * (x + 1)) = π * I * x + π * I by ring, exp_add,
      show (-((π : ℂ) * I * x + π * I)) = -(π * I * x) + -(π * I) by ring, exp_add,
      exp_pi_mul_I, show exp (-((π : ℂ) * I)) = -1 by rw [exp_neg, exp_pi_mul_I]; norm_num]
    ring
  rw [modelFun, modelFun, hden, show (x + 1 - p) ^ 2 = (x - (p - 1)) ^ 2 by ring, div_neg]

/-- The model integrand is dominated by its Gaussian numerator, wherever the kernel denominator
is bounded below. -/
theorem norm_modelFun_le (p : ℂ) {x : ℂ} {c : ℝ} (hc : 0 < c) (hx : c ≤ ‖sin (π * x)‖) :
    ‖modelFun p x‖ ≤ ‖exp (2 * π * I * (x - p) ^ 2)‖ / (2 * c) := by
  rw [modelFun_eq_div_two_mul_I_mul_sin, norm_div, Complex.norm_two_mul_I_mul]
  gcongr

/-- The model integrand is dominated by its Gaussian numerator along a half-integer contour. -/
theorem norm_modelIntegrand_le (p : ℂ) {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) (w : ℝ) :
    ‖modelIntegrand p a w‖ ≤ ‖exp (2 * π * I * (line a w - p) ^ 2)‖ / Real.sqrt 2 := by
  rw [modelIntegrand, show Real.sqrt 2 = 2 * (Real.sqrt 2 / 2) by ring]
  exact norm_modelFun_le p (by positivity) (norm_sin_pi_mul_line_ge ha w)

/-- The model integrand is continuous along a half-integer contour. -/
theorem continuous_modelIntegrand (p : ℂ) {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) :
    Continuous (modelIntegrand p a) := by
  have hline := continuous_line a
  have h : modelIntegrand p a
      = fun w : ℝ ↦ exp (2 * π * I * (line a w - p) ^ 2) / (2 * I * sin (π * line a w)) :=
    funext fun w ↦ modelFun_eq_div_two_mul_I_mul_sin p (line a w)
  rw [h]
  exact Continuous.div (by fun_prop) (by fun_prop) fun w ↦ by
    simpa [I_ne_zero] using sin_pi_mul_line_ne_zero ha w

/-- Absolute convergence of the model integral, for every complex `p`. -/
theorem integrable_modelIntegrand (p : ℂ) {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) :
    Integrable (modelIntegrand p a) :=
  Integrable.mono' ((integrable_exp_two_pi_mul_I_mul_line_sub_sq a p).norm.div_const _)
    (continuous_modelIntegrand p ha).aestronglyMeasurable
    (.of_forall (norm_modelIntegrand_le p ha))

/-- The modulus of the model Gaussian along the half-integer contour, with the square
completed: a Gaussian in the contour parameter, of peak `e^{π(½ − p)²}` and centre
`−(½ − p)/2`. -/
theorem norm_exp_two_pi_mul_I_mul_line_sub_sq (p w : ℝ) :
    ‖exp (2 * π * I * (line (1 / 2) w - (p : ℂ)) ^ 2)‖
      = Real.exp (π * (1 / 2 - p) ^ 2) * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) := by
  rw [Complex.norm_exp_two_pi_mul_I_mul_sq, Complex.sub_re, Complex.sub_im, line_re, line_im,
    ofReal_re, ofReal_im,
    show -(4 * π * (1 / 2 + w - p) * (w - 0))
      = π * (1 / 2 - p) ^ 2 + -(4 * π) * (w + (1 / 2 - p) / 2) ^ 2 by ring, Real.exp_add]

/-- The modulus of the model Gaussian along the half-integer contour, as a Gaussian in the
distance to the centre (`riemann_siegel_first.tex`, `lem:rsf_kernel_gauss`). -/
theorem norm_exp_two_pi_mul_I_mul_line_sub_sq' (p w : ℝ) :
    ‖exp (2 * π * I * (line (1 / 2) w - (p : ℂ)) ^ 2)‖
      = Real.exp (2 * π * (1 / 2 - p) ^ 2) *
          Real.exp (-(2 * π) * ‖line (1 / 2) w - (p : ℂ)‖ ^ 2) := by
  rw [norm_exp_two_pi_mul_I_mul_line_sub_sq, norm_line_sub_ofReal_sq, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

/-- An explicit bound for the model integral at a real point. -/
theorem norm_modelIntegral_le (p : ℝ) :
    ‖modelIntegral p (1 / 2)‖ ≤ Real.exp (π * (1 / 2 - p) ^ 2) / 2 := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  have hgauss : ∫ w : ℝ, Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) = 1 / 2 := by
    rw [integral_add_right_eq_self (fun u : ℝ ↦ Real.exp (-(4 * π) * u ^ 2)) ((1 / 2 - p) / 2),
      integral_gaussian, show π / (4 * π) = (1 / 2 : ℝ) ^ 2 by
        rw [div_eq_iff (by positivity)]; ring, Real.sqrt_sq (by norm_num)]
  calc ‖modelIntegral (p : ℂ) (1 / 2)‖
      ≤ Real.sqrt 2 * ∫ w : ℝ, ‖modelIntegrand (p : ℂ) (1 / 2) w‖ :=
        norm_one_add_I_mul_integral_le _
    _ ≤ Real.sqrt 2 * ∫ w : ℝ,
          ‖exp (2 * π * I * (line (1 / 2) w - (p : ℂ)) ^ 2)‖ / Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left (integral_mono (integrable_modelIntegrand _ hhalf).norm
          ((integrable_exp_two_pi_mul_I_mul_line_sub_sq (1 / 2) (p : ℂ)).norm.div_const _)
          (norm_modelIntegrand_le _ hhalf)) hs2.le
    _ = Real.exp (π * (1 / 2 - p) ^ 2) / 2 := by
        simp only [norm_exp_two_pi_mul_I_mul_line_sub_sq p, mul_div_right_comm]
        rw [integral_const_mul, hgauss]
        field_simp

/-- The half shift for the model integral:
`M(p + 1/2) = i e^{2πip} M(p) − i e^{iπ/8} e^{iπp}/√2`, for every complex `p`. -/
theorem modelIntegral_add_half (p : ℂ) :
    modelIntegral (p + 1 / 2) (1 / 2)
      = I * exp (2 * π * I * p) * modelIntegral p (1 / 2)
        - I * exp ((π / 8 : ℝ) * I) * exp (π * I * p) / (Real.sqrt 2 : ℂ) := by
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  set C : ℂ := exp (-((π / 8 : ℝ) * I)) * exp (-((π : ℂ) * I * p)) with hC
  -- the auxiliary Gaussian, a pure Gaussian centred at `p + 1/4`
  have hgpt (w : ℝ) : C * exp (2 * π * I * (line (1 / 2) w - (p + 1 / 4)) ^ 2)
      = exp (2 * π * I * (line (1 / 2) w - p) ^ 2) * exp (-((π : ℂ) * I * line (1 / 2) w)) := by
    rw [hC, ← exp_add, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  have hCval : ((1 + I) * ∫ w : ℝ, C * exp (2 * π * I * (line (1 / 2) w - (p + 1 / 4)) ^ 2))
      = C * ((1 + I) / 2) := by
    rw [integral_const_mul, mul_left_comm, integral_exp_two_pi_mul_I_mul_line_sub_sq]
  -- the Gaussian quasi-period, followed by partial fractions
  have hsplit (w : ℝ) : modelIntegrand (p + 1 / 2) (1 / 2) w
      = I * exp (2 * π * I * p) * (modelIntegrand p (1 / 2) w -
        C * exp (2 * π * I * (line (1 / 2) w - (p + 1 / 4)) ^ 2)) := by
    have hne : exp ((π : ℂ) * I * line (1 / 2) w) ≠ exp (-((π : ℂ) * I * line (1 / 2) w)) := by
      rw [← sub_ne_zero,
        show ((π : ℂ) * I * line (1 / 2) w) = ((π : ℂ) * line (1 / 2) w) * I by ring,
        exp_mul_I_sub_exp_neg_mul_I]
      simpa [I_ne_zero] using sin_pi_mul_line_ne_zero hhalf w
    have hquasi : exp (2 * (π : ℂ) * I * (line (1 / 2) w - (p + 1 / 2)) ^ 2)
        = exp ((π : ℂ) / 2 * I) * exp (2 * π * I * p) *
            exp (2 * π * I * (line (1 / 2) w - p) ^ 2) *
            exp (-(2 * π * I * line (1 / 2) w)) := by
      rw [← exp_add, ← exp_add, ← exp_add]
      congr 1
      ring
    rw [modelIntegrand, modelIntegrand, modelFun, modelFun, hquasi, exp_pi_div_two_mul_I,
      mul_div_assoc, exp_neg_two_pi_mul_I_div_sub_eq hne, hgpt w]
    ring
  have hMain : modelIntegral (p + 1 / 2) (1 / 2)
      = I * exp (2 * π * I * p) * (modelIntegral p (1 / 2) - C * ((1 + I) / 2)) := by
    rw [← hCval]
    simp only [modelIntegral, hsplit]
    rw [integral_const_mul, integral_sub (integrable_modelIntegrand p hhalf)
      ((integrable_exp_two_pi_mul_I_mul_line_sub_sq (1 / 2) (p + 1 / 4)).const_mul _)]
    ring
  -- the two rotations `e^{2πip} e^{-iπp} = e^{iπp}` and `e^{-iπ/8} e^{iπ/4} = e^{iπ/8}`
  have hexp : exp (2 * (π : ℂ) * I * p) * exp (-((π / 8 : ℝ) * I)) * exp (-((π : ℂ) * I * p)) *
      exp ((π / 4 : ℝ) * I) = exp ((π / 8 : ℝ) * I) * exp ((π : ℂ) * I * p) := by
    simp only [← exp_add]
    congr 1
    push_cast
    ring
  rw [hMain, mul_sub, hC, ← exp_pi_div_four_mul_I_div_sqrt_two]
  linear_combination (-I / (Real.sqrt 2 : ℂ)) * hexp

end Zeta.RiemannSiegel
