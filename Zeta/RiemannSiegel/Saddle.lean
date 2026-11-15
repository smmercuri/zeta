/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Zeta.RiemannSiegel.Model

/-!
# The saddle-point reduction of the Riemann–Siegel integral

The Riemann–Siegel contour integral `I(s, a)` of `Zeta.RiemannSiegel.contourIntegral` is taken over
the line `L(a)` with `a = ν + 1/2`, `ν = ⌊√T⌋`, `T = t/2π`, which passes within `1/2` of the saddle
`√T` of the integrand. Writing `p = √T - ν` and `v = x - ν`, the substitution `x ↦ x - ν` carries
`L(a)` onto `L(1/2)`, the contour of the model integral `M(p)` of
`Zeta.RiemannSiegel.modelIntegral`, and the true integrand becomes the model integrand times
`e^Δ`, where

`Δ(x) = iπx² - s Log x + (log T)/4 + i(ϑ(t) + π/8) - 2πi(x - √T)²`

is the **saddle discrepancy** (`riemann_siegel_first.tex`, `def:rsf_discrepancy`). Since `Δ` is
*defined* as this difference of logarithms, the factorisation
`Zeta.RiemannSiegel.integrand_eq_modelFun_mul` is exact and unconditional; all the analytic content
of the chapter is then the single statement that `Δ` is small, which is what makes `√T` a saddle:
the terms of `Δ` linear in `x - √T` cancel, leaving
`Δ = -½ log (1 + u) - 2πiT (log (1 + u) - u + u²/2)` with `u = (x - √T)/√T`, hence
`|Δ| ≲ |x - √T|³/√T`.

## Main results

* `Zeta.RiemannSiegel.norm_modelIntegrand_le_exp_neg_mul_sq`: the Gaussian majorant for the model
  integrand along `L(½)`;
* `Zeta.RiemannSiegel.leadingTheta`: the leading Stirling phase `ϑ(t)`;
* `Zeta.RiemannSiegel.saddleDiscrepancy`, `Zeta.RiemannSiegel.saddleFactor`: the discrepancy `Δ` and
  the constant `(-1)^ν T^{-1/4} e^{-i(ϑ + π/8)}` accompanying it;
* `Zeta.RiemannSiegel.integrand_eq_modelFun_mul`: the exact factorisation of the integrand;
* `Zeta.RiemannSiegel.norm_modelIntegrand_mul_exp_saddleDiscrepancy`: the modulus of the
  renormalised integrand;
* `Zeta.RiemannSiegel.contourIntegral_eq_modelIntegrand_mul`,
  `Zeta.RiemannSiegel.contourIntegral_sub_mul_modelIntegral`: its integrated forms, the second
  isolating the error `I(s, a) - saddleFactor * M(p)`;
* `Zeta.RiemannSiegel.saddleDiscrepancy_eq_log_sub_logTaylor`,
  `Zeta.RiemannSiegel.saddleDiscrepancy_eq_tsum`: the two forms of the series expansion of `Δ`;
* `Zeta.RiemannSiegel.norm_saddleDiscrepancy_le`: the explicit bound
  `|Δ| ≤ (|y| + 4π|y|³/3)/√T` for `|y| ≤ √T/2`, `y = x - √T`;
* `Zeta.RiemannSiegel.saddleLinear`, `Zeta.RiemannSiegel.norm_saddleLinear_le`,
  `Zeta.RiemannSiegel.norm_saddleDiscrepancy_sub_linear_le`: the polynomial
  `P₁(y) = -y/2 - 2πiy³/3` carrying the `T^{-1/2}` term of `Δ`, its modulus
  `|P₁(y)| ≤ |y|/2 + 2π|y|³/3`, and the resulting `|Δ - P₁(y)/√T| ≤ (|y|²/2 + π|y|⁴)/T`;
* `Zeta.RiemannSiegel.norm_saddleDiscrepancy_le'`,
  `Zeta.RiemannSiegel.exp_norm_saddleDiscrepancy_mul_exp_le`: the bound `|Δ| ≤ ½ + 2π|y|²/3` and
  the exponent budget it buys, `e^{|Δ|}e^{-2π|y|²} ≤ e^{1/2}e^{-4π|y|²/3}`.

`saddleLinear` and `exp_norm_saddleDiscrepancy_mul_exp_le` are what the sharp first-order estimate
of `sec:rsf_sharp` runs on: it evaluates the `T^{-1/2}` term exactly, and integrates the
remainder against the narrowed Gaussian `e^{-4π|y|²/3}` that survives `e^{|Δ|}`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- **The Gaussian majorant for the model integrand along `L(½)`**: `|m_p| ≤ e^{π/4}e^{-4πξ²}/√2`
in the centred parameter `ξ = w + (½ - p)/2`, whenever the fractional part `p` lies within `½` of
the contour. -/
theorem norm_modelIntegrand_le_exp_neg_mul_sq {p : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2) (w : ℝ) :
    ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ Real.exp (π / 4) * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) / Real.sqrt 2 := by
  refine (norm_modelIntegrand_le (p : ℂ) (by norm_num : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2) w).trans ?_
  rw [norm_exp_two_pi_mul_I_mul_line_sub_sq p w,
    div_le_div_iff_of_pos_right (Real.sqrt_pos.2 two_pos)]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
    (by nlinarith [Real.pi_pos, sq_le_sq' (abs_le.1 hκ).1 (abs_le.1 hκ).2])) (Real.exp_nonneg _)

/-- The **leading Stirling phase** `ϑ(t) = (t/2) log (t/2π) - t/2 - π/8`, the leading term of the
Riemann–Siegel theta function `Real.riemannSiegelTheta`. -/
noncomputable def leadingTheta (t : ℝ) : ℝ :=
  t / 2 * Real.log (t / (2 * π)) - t / 2 - π / 8

/-- **The leading phase, shorn of its constant term**, `T = t/2π`. -/
theorem leadingTheta_add_pi_div_eight (t : ℝ) :
    leadingTheta t + π / 8 = π * (t / (2 * π)) * (Real.log (t / (2 * π)) - 1) := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  rw [leadingTheta]
  field_simp
  ring

/-- The **saddle discrepancy**
`Δ(x) = iπx² - s Log x + (log T)/4 + i(ϑ(t) + π/8) - 2πi(x - √T)²`,
the logarithm of the ratio of the Riemann–Siegel integrand `Zeta.RiemannSiegel.integrand` at
`s = ½ + it` to its Gaussian model at the saddle `√T`, `T = t/2π`. The logarithm is the branch
`Zeta.RiemannSiegel.slantLog` adapted to the contour. -/
noncomputable def saddleDiscrepancy (t : ℝ) (x : ℂ) : ℂ :=
  π * I * x ^ 2 - (1 / 2 + t * I) * slantLog x + (Real.log (t / (2 * π)) : ℂ) / 4
    + I * ((leadingTheta t : ℂ) + π / 8)
    - 2 * π * I * (x - (Real.sqrt (t / (2 * π)) : ℂ)) ^ 2

/-- The **saddle factor** `(-1)^ν T^{-1/4} e^{-i(ϑ(t) + π/8)}` with `T = t/2π`, the constant of
modulus `T^{-1/4}` relating the Riemann–Siegel integral to the model integral. -/
noncomputable def saddleFactor (t : ℝ) (ν : ℕ) : ℂ :=
  (-1) ^ ν * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ)
    * exp (-(I * ((leadingTheta t : ℂ) + π / 8)))

theorem saddleFactor_ne_zero {t : ℝ} (ht : 0 < t) (ν : ℕ) : saddleFactor t ν ≠ 0 := by
  have hT0 : 0 < t / (2 * π) := by positivity
  rw [saddleFactor]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) (exp_ne_zero _)
  exact_mod_cast (Real.rpow_pos_of_pos hT0 _).ne'

/-- **The modulus of the saddle factor**, `T = t/2π`. -/
theorem norm_saddleFactor {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    ‖saddleFactor t ν‖ = (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
  have hT0 : 0 < t / (2 * π) := by positivity
  rw [saddleFactor, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hT0 _)]
  simp

/-- **The exact factorisation of the Riemann–Siegel integrand**: with `T = t/2π`, `p = √T - ν` and
`v = x - ν`, the integrand at `s = ½ + it` is `e^Δ` times the model integrand at `v`. -/
theorem integrand_eq_modelFun_mul {t : ℝ} (ht : 0 < t) (ν : ℕ) {x : ℂ} (hx : x ≠ 0) :
    integrand (1 / 2 + t * I) x
      = saddleFactor t ν * modelFun ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (x - ν)
        * exp (saddleDiscrepancy t x) := by
  have hT0 : 0 < t / (2 * π) := by positivity
  have hinv : ((-1 : ℂ) ^ ν)⁻¹ = (-1) ^ ν := by rw [← inv_pow, inv_neg_one]
  have hdiv : ∀ E : ℂ, E / (2 * I * ((-1 : ℂ) ^ ν * Complex.sin (π * (x - ν))))
      = (-1) ^ ν * (E / (2 * I * Complex.sin (π * (x - ν)))) := fun E ↦ by
    rw [show (2 : ℂ) * I * ((-1 : ℂ) ^ ν * Complex.sin (π * (x - ν)))
        = (-1 : ℂ) ^ ν * (2 * I * Complex.sin (π * (x - ν))) by ring,
      div_mul_eq_div_div_swap, div_eq_mul_inv, hinv, mul_comm]
  -- the kernel's denominator is antiperiodic
  have hsin : Complex.sin (π * x) = (-1) ^ ν * Complex.sin (π * (x - ν)) := by
    rw [show ((π : ℂ) * x) = π * (x - ν) + ν * π by ring]
    exact Complex.sin_antiperiodic.add_nat_mul_eq ν
  have hrpow : (((t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
      = exp (-((Real.log (t / (2 * π)) : ℂ) / 4)) := by
    rw [Real.rpow_def_of_pos hT0, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  -- the numerators, where the whole content of the identity sits
  have hnum : exp (-(1 / 2 + (t : ℂ) * I) * slantLog x) * exp ((π : ℂ) * I * x ^ 2)
      = exp (-((Real.log (t / (2 * π)) : ℂ) / 4)) * exp (-(I * ((leadingTheta t : ℂ) + π / 8)))
        * exp (2 * π * I * (x - (Real.sqrt (t / (2 * π)) : ℂ)) ^ 2)
        * exp (saddleDiscrepancy t x) := by
    rw [← exp_add, ← exp_add, ← exp_add, ← exp_add, saddleDiscrepancy]
    congr 1
    ring
  rw [integrand, kernel_eq_div_two_mul_I_mul_sin, slantCpow_eq_exp_mul_slantLog hx,
    modelFun_eq_div_two_mul_I_mul_sin, hsin, saddleFactor, hrpow,
    show ((x - (ν : ℂ)) - ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ))
      = x - (Real.sqrt (t / (2 * π)) : ℂ) by push_cast; ring, hdiv]
  linear_combination ((-1 : ℂ) ^ ν / (2 * I * Complex.sin (π * (x - ν)))) * hnum

/-- **The contour of the model integral is the contour of the Riemann-Siegel integral translated
by `ν`**: recentring `L(ν + ½)` at `S` is recentring `L(½)` at `p = S - ν`. -/
theorem line_sub_ofReal_sub {ν : ℕ} {S p : ℝ} (hp : p = S - ν) (w : ℝ) :
    line ((ν : ℝ) + 1 / 2) w - (S : ℂ) = line (1 / 2) w - (p : ℂ) := by
  rw [hp, line, line]
  push_cast
  ring

/-- **The factorisation along the contour** `L(ν + ½)`, which the substitution `x ↦ x - ν` carries
onto the contour `L(½)` of the model integral. -/
theorem contourIntegrand_eq_modelIntegrand_mul {t : ℝ} (ht : 0 < t) (ν : ℕ) (w : ℝ) :
    contourIntegrand (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) w
      = saddleFactor t ν
        * (modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))) := by
  have hline : line ((ν : ℝ) + 1 / 2) w - (ν : ℂ) = line (1 / 2) w := by
    simpa using line_sub_ofReal_sub (S := (ν : ℝ)) (p := 0) (by ring) w
  have hx0 : line ((ν : ℝ) + 1 / 2) w ≠ 0 := line_ne_zero (by positivity) w
  rw [contourIntegrand, integrand_eq_modelFun_mul ht ν hx0, modelIntegrand, hline]
  ring

/-- **The renormalised integrand**: along `L(ν + ½)` the model integrand against `e^Δ` is the
Riemann–Siegel integrand divided by the modulus `T^{-1/4}` of the saddle factor. -/
theorem norm_modelIntegrand_mul_exp_saddleDiscrepancy {t : ℝ} (ht : 0 < t) (ν : ℕ) (w : ℝ) :
    ‖modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
        * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))‖
      = ‖contourIntegrand (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) w‖
          / (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
  have hR0 : (t / (2 * π)) ^ (-(1 / 4) : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [contourIntegrand_eq_modelIntegrand_mul ht ν w, norm_mul (saddleFactor t ν),
    norm_saddleFactor ht]
  field_simp

/-- **Absolute convergence of the perturbed model integral.** -/
theorem integrable_modelIntegrand_mul_exp_saddleDiscrepancy {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    Integrable fun w : ℝ ↦ modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
      * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) := by
  have hint : Integrable (contourIntegrand (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)) :=
    integrable_contourIntegrand _ (by positivity) (c := Real.sqrt 2 / 2) (by positivity)
      fun w ↦ norm_sin_pi_mul_line_ge (n := (ν : ℤ)) (by push_cast; ring) w
  refine (hint.const_mul (saddleFactor t ν)⁻¹).congr (.of_forall fun w ↦ ?_)
  change (saddleFactor t ν)⁻¹ * contourIntegrand (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) w = _
  rw [contourIntegrand_eq_modelIntegrand_mul ht ν w, ← mul_assoc,
    inv_mul_cancel₀ (saddleFactor_ne_zero ht ν), one_mul]

/-- **Absolute convergence of the perturbation of the model integral.** -/
theorem integrable_modelIntegrand_mul_exp_saddleDiscrepancy_sub_one {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    Integrable fun w : ℝ ↦ modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
      * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1) := by
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  exact (((integrable_modelIntegrand_mul_exp_saddleDiscrepancy ht ν).sub
    (integrable_modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ) hhalf)).congr
    (.of_forall fun w ↦ by simp only [Pi.sub_apply]; ring))

/-- **The Riemann–Siegel contour integral as a perturbation of the model integral**
(`riemann_siegel_first.tex`, `lem:rsf_factor`). -/
theorem contourIntegral_eq_modelIntegrand_mul {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
      = saddleFactor t ν
        * ((1 + I) * ∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
            * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))) := by
  rw [contourIntegral]
  simp only [contourIntegrand_eq_modelIntegrand_mul ht ν]
  rw [integral_const_mul]
  ring

/-- **The error committed by replacing the integrand by its model at the saddle**
(`riemann_siegel_first.tex`, `lem:rsf_factor`, last display). -/
theorem contourIntegral_sub_mul_modelIntegral {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
        - saddleFactor t ν * modelIntegral ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2)
      = saddleFactor t ν
        * ((1 + I) * ∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
            * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)) := by
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  have hsplit : (∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1))
      = (∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)))
        - ∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w := by
    simp only [mul_sub, mul_one]
    exact integral_sub (integrable_modelIntegrand_mul_exp_saddleDiscrepancy ht ν)
      (integrable_modelIntegrand _ hhalf)
  rw [contourIntegral_eq_modelIntegrand_mul ht ν, modelIntegral, hsplit]
  ring

/-- The second Taylor polynomial of `log (1 + ·)`. -/
private theorem logTaylor_two (z : ℂ) : Complex.logTaylor 2 z = z := by
  simp [Complex.logTaylor_succ, Complex.logTaylor_zero]

/-- The third Taylor polynomial of `log (1 + ·)`. -/
private theorem logTaylor_three (z : ℂ) : Complex.logTaylor 3 z = z - z ^ 2 / 2 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Complex.logTaylor_succ, Pi.add_apply, logTaylor_two]
  push_cast
  ring

/-- The fourth Taylor polynomial of `log (1 + ·)`. -/
private theorem logTaylor_four (z : ℂ) : Complex.logTaylor 4 z = z - z ^ 2 / 2 + z ^ 3 / 3 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, Complex.logTaylor_succ, Pi.add_apply, logTaylor_three]
  push_cast
  ring

/-- The tail of the logarithmic series past its `(n+1)`-st Taylor polynomial, on the disc of
radius `½`. -/
private theorem norm_log_sub_logTaylor_le_of_norm_le_half {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) (n : ℕ) :
    ‖Complex.log (1 + u) - Complex.logTaylor (n + 1) u‖ ≤ 2 * ‖u‖ ^ (n + 1) / (n + 1) := by
  have hu1 : ‖u‖ < 1 := hu.trans_lt (by norm_num)
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  refine (Complex.norm_log_sub_logTaylor_le n hu1).trans ?_
  calc ‖u‖ ^ (n + 1) * (1 - ‖u‖)⁻¹ / ((n : ℝ) + 1)
      ≤ ‖u‖ ^ (n + 1) * 2 / ((n : ℝ) + 1) := by gcongr
    _ = 2 * ‖u‖ ^ (n + 1) / ((n : ℝ) + 1) := by ring

/-- **The modulus of a saddle discrepancy in split form** `-A/2 - 2πiT·B`, the shape taken by `Δ`
and by `Δ - P₁(y)/√T` alike once the logarithm is expanded. -/
private theorem norm_neg_half_sub_two_pi_mul_I_mul_le {T α β : ℝ} (hT : 0 ≤ T) {A B : ℂ}
    (hA : ‖A‖ ≤ α) (hB : ‖B‖ ≤ β) :
    ‖-(1 / 2) * A - 2 * π * I * (T : ℂ) * B‖ ≤ 1 / 2 * α + 2 * π * T * β := by
  have hfac : ‖2 * (π : ℂ) * I * (T : ℂ)‖ = 2 * π * T := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, mul_one,
      Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hT]
  calc ‖-(1 / 2) * A - 2 * π * I * (T : ℂ) * B‖
      ≤ ‖-(1 / 2) * A‖ + ‖2 * (π : ℂ) * I * (T : ℂ) * B‖ := norm_sub_le _ _
    _ = 1 / 2 * ‖A‖ + 2 * π * T * ‖B‖ := by rw [norm_mul, norm_mul, hfac]; norm_num
    _ ≤ 1 / 2 * α + 2 * π * T * β :=
        add_le_add (by linarith)
          (mul_le_mul_of_nonneg_left hB (mul_nonneg (by positivity) hT))

/-- **The series form of the saddle discrepancy**, in the parametrisation `x = √T (1 + u)`. Here
`Complex.logTaylor 3 u = u - u²/2`, so the second factor is the tail `∑_{k ≥ 3}` of the logarithmic
series. -/
theorem saddleDiscrepancy_eq_log_sub_logTaylor {t : ℝ} (ht : 0 < t) {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    saddleDiscrepancy t ((Real.sqrt (t / (2 * π)) : ℂ) * (1 + u))
      = -(1 / 2) * Complex.log (1 + u)
        - 2 * π * I * ((t / (2 * π) : ℝ) : ℂ)
          * (Complex.log (1 + u) - Complex.logTaylor 3 u) := by
  have hT0 : 0 < t / (2 * π) := by positivity
  have hS : 0 < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  have hur : -(1 / 2 : ℝ) ≤ u.re := by
    linarith [neg_abs_le u.re, (Complex.abs_re_le_norm u).trans hu]
  have h1u : (1 : ℂ) + u ≠ 0 := fun h ↦ by
    rw [show u = -1 by linear_combination h] at hur
    norm_num at hur
  -- the point lies in the right half-plane, where the slanted branch is the principal one
  have hre : 0 < ((Real.sqrt (t / (2 * π)) : ℂ) * (1 + u)).re := by
    have h1 : (0 : ℝ) < (1 + u).re := by rw [Complex.add_re, Complex.one_re]; linarith
    rw [Complex.re_ofReal_mul]
    positivity
  have hlog : Complex.log ((Real.sqrt (t / (2 * π)) : ℂ) * (1 + u))
      = (Real.log (t / (2 * π)) : ℂ) / 2 + Complex.log (1 + u) := by
    rw [Complex.log_ofReal_mul hS h1u, Real.log_sqrt hT0.le]
    push_cast
    ring
  have hS2 : ((Real.sqrt (t / (2 * π)) : ℂ)) ^ 2 = ((t / (2 * π) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hT0.le]
  have ht2 : (t : ℂ) = 2 * π * ((t / (2 * π) : ℝ) : ℂ) := by push_cast; field_simp
  have hϑ : ((leadingTheta t : ℝ) : ℂ) + (π : ℂ) / 8
      = π * ((t / (2 * π) : ℝ) : ℂ) * ((Real.log (t / (2 * π)) : ℂ) - 1) := by
    rw [show ((leadingTheta t : ℝ) : ℂ) + (π : ℂ) / 8 = ((leadingTheta t + π / 8 : ℝ) : ℂ) by
      push_cast; ring, leadingTheta_add_pi_div_eight]
    push_cast
    ring
  rw [saddleDiscrepancy, slantLog_eq_log hre, hlog, hϑ, logTaylor_three, ht2, ← hS2]
  ring

/-- **The saddle discrepancy as the tail of the logarithmic series**
(`riemann_siegel_first.tex`, `lem:rsf_discrepancy_bound`). -/
theorem saddleDiscrepancy_eq_tsum {t : ℝ} (ht : 0 < t) {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    saddleDiscrepancy t ((Real.sqrt (t / (2 * π)) : ℂ) * (1 + u))
      = -(1 / 2) * Complex.log (1 + u)
        - 2 * π * I * ((t / (2 * π) : ℝ) : ℂ)
          * ∑' k : ℕ, (-1) ^ (k + 2) * u ^ (k + 3) / ((k : ℂ) + 3) := by
  have hu1 : ‖u‖ < 1 := hu.trans_lt (by norm_num)
  have hsum := Complex.hasSum_taylorSeries_log hu1
  have htail : Complex.log (1 + u) - Complex.logTaylor 3 u
      = ∑' k : ℕ, (-1) ^ (k + 2) * u ^ (k + 3) / ((k : ℂ) + 3) := by
    have h := hsum.summable.sum_add_tsum_nat_add 3
    rw [hsum.tsum_eq] at h
    rw [Complex.logTaylor, ← h, add_sub_cancel_left]
    refine tsum_congr fun k ↦ ?_
    rw [show k + 3 + 1 = (k + 2) + 2 by ring, pow_add]
    push_cast
    ring
  rw [saddleDiscrepancy_eq_log_sub_logTaylor ht hu, htail]

/-- **The explicit bound for the saddle discrepancy**
(`riemann_siegel_first.tex`, `lem:rsf_discrepancy_bound`): with `y = x - √T`,
`|Δ(x)| ≤ (|y| + 4π|y|³/3)/√T` whenever `|y| ≤ √T/2`. -/
theorem norm_saddleDiscrepancy_le {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ≤ Real.sqrt (t / (2 * π)) / 2) :
    ‖saddleDiscrepancy t x‖
      ≤ (‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖
          + 4 * π / 3 * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 3) / Real.sqrt (t / (2 * π)) := by
  have hT0 : 0 < t / (2 * π) := by positivity
  have hS : 0 < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set n : ℝ := ‖x - (S : ℂ)‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hSne : ((S : ℝ) : ℂ) ≠ 0 := by simpa using hS.ne'
  -- reparametrise by `u = y/√T`
  have hxu : x = (S : ℂ) * (1 + (x - (S : ℂ)) / (S : ℂ)) := by field_simp; ring
  have hunorm : ‖(x - (S : ℂ)) / (S : ℂ)‖ = n / S := by
    rw [norm_div, hn, Complex.norm_real, Real.norm_of_nonneg hS.le]
  have hu : ‖(x - (S : ℂ)) / (S : ℂ)‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_iff₀ hS]
    linarith [hx]
  have hTS : t / (2 * π) = S ^ 2 := (Real.sq_sqrt hT0.le).symm
  -- the two series bounds
  have hlog : ‖Complex.log (1 + (x - (S : ℂ)) / (S : ℂ))‖ ≤ 3 / 2 * (n / S) := by
    rw [← hunorm]
    exact Complex.norm_log_one_add_half_le_self hu
  have htail : ‖Complex.log (1 + (x - (S : ℂ)) / (S : ℂ))
      - Complex.logTaylor 3 ((x - (S : ℂ)) / (S : ℂ))‖ ≤ 2 / 3 * (n / S) ^ 3 := by
    have h := norm_log_sub_logTaylor_le_of_norm_le_half hu 2
    rw [hunorm] at h
    norm_num at h
    linarith
  have hΔ : saddleDiscrepancy t x
      = -(1 / 2) * Complex.log (1 + (x - (S : ℂ)) / (S : ℂ))
        - 2 * π * I * ((t / (2 * π) : ℝ) : ℂ)
          * (Complex.log (1 + (x - (S : ℂ)) / (S : ℂ))
            - Complex.logTaylor 3 ((x - (S : ℂ)) / (S : ℂ))) := by
    conv_lhs => rw [hxu]
    exact saddleDiscrepancy_eq_log_sub_logTaylor ht hu
  rw [hΔ]
  refine (norm_neg_half_sub_two_pi_mul_I_mul_le hT0.le hlog htail).trans ?_
  rw [show 1 / 2 * (3 / 2 * (n / S)) + 2 * π * (t / (2 * π)) * (2 / 3 * (n / S) ^ 3)
      = (3 / 4 * n + 4 * π / 3 * n ^ 3) / S by rw [hTS]; field_simp; ring]
  gcongr
  linarith

/-- The **linear part of the saddle discrepancy**, `P₁(y) = -y/2 - 2πiy³/3`
(`riemann_siegel_first.tex`, `lem:rsf_delta_split`). "Linear" refers to the order in
`ζ = T^{-1/2}`: `P₁(y)/√T` is the `ζ`-linear part of `Δ`, and `P₁` is a cubic in `y`. -/
noncomputable def saddleLinear (y : ℂ) : ℂ := -(y / 2) - 2 * π * I / 3 * y ^ 3

/-- **The linear part of the saddle discrepancy is a cubic in `|y|`.** -/
theorem norm_saddleLinear_le (y : ℂ) : ‖saddleLinear y‖ ≤ ‖y‖ / 2 + 2 * π / 3 * ‖y‖ ^ 3 := by
  rw [saddleLinear]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_neg, norm_div, norm_mul, norm_pow, norm_div, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  norm_num

/-- **The saddle discrepancy with its linear part split off**
(`riemann_siegel_first.tex`, `lem:rsf_delta_split`): with `y = x - √T` and `T = t/2π`,
`|Δ(x) - P₁(y)/√T| ≤ (|y|²/2 + π|y|⁴)/T` whenever `|y| ≤ √T/2`. -/
theorem norm_saddleDiscrepancy_sub_linear_le {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ≤ Real.sqrt (t / (2 * π)) / 2) :
    ‖saddleDiscrepancy t x
        - saddleLinear (x - (Real.sqrt (t / (2 * π)) : ℂ)) / (Real.sqrt (t / (2 * π)) : ℂ)‖
      ≤ (1 / 2 * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 2
          + π * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 4) / (t / (2 * π)) := by
  have hT0 : 0 < t / (2 * π) := by positivity
  have hS : 0 < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  set S : ℝ := Real.sqrt (t / (2 * π))
  set n : ℝ := ‖x - (S : ℂ)‖ with hn
  have hSne : ((S : ℝ) : ℂ) ≠ 0 := by simpa using hS.ne'
  have hS0 : S ≠ 0 := hS.ne'
  have hTS : t / (2 * π) = S ^ 2 := (Real.sq_sqrt hT0.le).symm
  have hTS' : ((t / (2 * π) : ℝ) : ℂ) = (S : ℂ) ^ 2 := by rw [hTS]; push_cast; ring
  -- reparametrise by `u = y/√T`
  set u : ℂ := (x - (S : ℂ)) / (S : ℂ) with hu_def
  have hunorm : ‖u‖ = n / S := by
    rw [hu_def, norm_div, hn, Complex.norm_real, Real.norm_of_nonneg hS.le]
  have hu : ‖u‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_iff₀ hS]
    linarith [hx]
  have hxS : x - (S : ℂ) = (S : ℂ) * u := by
    rw [hu_def]
    field_simp
  have hxu : x = (S : ℂ) * (1 + u) := by linear_combination hxS
  -- subtracting `P₁(y)/√T` promotes the second-order Taylor polynomial to the third-order one
  have hkey : saddleDiscrepancy t x - saddleLinear (x - (S : ℂ)) / (S : ℂ)
      = -(1 / 2) * (Complex.log (1 + u) - Complex.logTaylor 2 u)
        - 2 * π * I * ((t / (2 * π) : ℝ) : ℂ)
          * (Complex.log (1 + u) - Complex.logTaylor 4 u) := by
    have hΔ : saddleDiscrepancy t x
        = -(1 / 2) * Complex.log (1 + u) - 2 * π * I * ((t / (2 * π) : ℝ) : ℂ)
            * (Complex.log (1 + u) - Complex.logTaylor 3 u) := by
      conv_lhs => rw [hxu]
      exact saddleDiscrepancy_eq_log_sub_logTaylor ht hu
    rw [hΔ, logTaylor_two, logTaylor_three, logTaylor_four, saddleLinear, hxS, hTS']
    field_simp
    ring
  -- the two Taylor remainders
  have hlog2 : ‖Complex.log (1 + u) - Complex.logTaylor 2 u‖ ≤ ‖u‖ ^ 2 := by
    have h := norm_log_sub_logTaylor_le_of_norm_le_half hu 1
    norm_num at h
    linarith
  have hlog4 : ‖Complex.log (1 + u) - Complex.logTaylor 4 u‖ ≤ ‖u‖ ^ 4 / 2 := by
    have h := norm_log_sub_logTaylor_le_of_norm_le_half hu 3
    norm_num at h
    linarith
  rw [hkey]
  refine (norm_neg_half_sub_two_pi_mul_I_mul_le hT0.le hlog2 hlog4).trans_eq ?_
  rw [hunorm, hTS]
  field_simp

/-- **The saddle discrepancy is bounded by a quadratic** (`riemann_siegel_first.tex`,
`lem:rsf_delta_exp`): `|Δ(x)| ≤ ½ + 2π|y|²/3` for `y = x - √T` with `|y| ≤ √T/2`. -/
theorem norm_saddleDiscrepancy_le' {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ≤ Real.sqrt (t / (2 * π)) / 2) :
    ‖saddleDiscrepancy t x‖ ≤ 1 / 2 + 2 * π / 3 * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 2 := by
  have hT0 : 0 < t / (2 * π) := by positivity
  have hS : 0 < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  set S : ℝ := Real.sqrt (t / (2 * π))
  set n : ℝ := ‖x - (S : ℂ)‖
  have hcube : 0 ≤ π * (n ^ 2 * (S - 2 * n)) :=
    mul_nonneg Real.pi_pos.le (mul_nonneg (sq_nonneg n) (by linarith))
  refine (norm_saddleDiscrepancy_le ht hx).trans ?_
  rw [div_le_iff₀ hS]
  nlinarith [hcube]

/-- **The exponent budget at Taylor radius `½`** (`riemann_siegel_first.tex`, `lem:rsf_delta_exp`):
against the Gaussian `e^{-2π|y|²}`, the factor `e^{|Δ|}` costs a third of the exponent and a
constant `e^{1/2}`, for `y = x - √T` with `|y| ≤ √T/2`. -/
theorem exp_norm_saddleDiscrepancy_mul_exp_le {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ≤ Real.sqrt (t / (2 * π)) / 2) :
    Real.exp ‖saddleDiscrepancy t x‖
        * Real.exp (-(2 * π) * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 2)
      ≤ Real.exp (1 / 2)
          * Real.exp (-(4 * π / 3) * ‖x - (Real.sqrt (t / (2 * π)) : ℂ)‖ ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  linarith [norm_saddleDiscrepancy_le' ht hx]

end Zeta.RiemannSiegel
