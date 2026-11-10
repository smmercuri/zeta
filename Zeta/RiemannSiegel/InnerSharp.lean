/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Zeta.Analysis.Complex.Exponential
public import Zeta.Analysis.SpecialFunctions.Gaussian
public import Zeta.RiemannSiegel.Moment
public import Zeta.RiemannSiegel.Saddle

/-!
# The sharp inner saddle-point estimate

The crude inner estimate `Zeta.RiemannSiegel.norm_integral_inner_le` bounds `|e^Δ - 1|` by `2|Δ|`
and integrates in absolute value, discarding the cancellation that produces the next classical
Riemann–Siegel coefficient. This file subtracts the `T^{-1/2}`-linear part `P₁(y)/√T` of the
saddle discrepancy (`Zeta.RiemannSiegel.saddleLinear`) before estimating, and so bounds the
*second-order* remainder (`riemann_siegel_first.tex`, `lem:rsf_inner_sharp`).

Two features distinguish it from the crude chain. The splitting radius is
`Zeta.RiemannSiegel.sharpSplitRadius`, proportional to `√T`, chosen so
that `|y| ≤ √T/2` holds on the whole inner region and the Taylor radius `1/2` of
`Zeta.RiemannSiegel.norm_saddleDiscrepancy_le` is available with no further hypothesis. And the two
contributions are integrated against *different* Gaussians: the linear discrepancy against the
model Gaussian `e^{-4πξ²}`, and the exponential remainder against the widened `e^{-8πξ²/3}` left
over after `e^{|Δ|}` has eaten a third of the exponent.

## Main results

* `Zeta.RiemannSiegel.sharpSplitRadius`: the splitting radius `W = (√T - 1)/(2√2)`;
* `Zeta.RiemannSiegel.integrable_modelIntegrand_mul_saddleLinear_div`: absolute convergence of the
  linear term against the model integrand;
* `Zeta.RiemannSiegel.norm_integral_inner_sub_linear_le`
  (`riemann_siegel_first.tex`, `lem:rsf_inner_sharp`): over `|w| ≤ W`, the model integrand against
  `e^Δ - 1 - P₁(y)/√T` contributes at most `(299/100) T^{-1}`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- The splitting radius of the sharp saddle estimate `W = (√T - 1)/(2√2)`, `T = t/2π`
(`riemann_siegel_first.tex`, `sec:rsf_sharp`). -/
noncomputable def sharpSplitRadius (t : ℝ) : ℝ :=
  (Real.sqrt (t / (2 * π)) - 1) / (2 * Real.sqrt 2)

/-- An explicit upper bound for `√2`. -/
theorem sqrt_two_le : Real.sqrt 2 ≤ 1.41422 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)

/-- `x ↦ xᵏ e^{-bx²}` is antitone past the point where `b x² ≥ k`. -/
theorem pow_mul_exp_neg_mul_sq_le {b A₀ A : ℝ} {k : ℕ} (hb : 0 < b) (hA₀ : 0 < A₀)
    (hbA : (k : ℝ) ≤ b * A₀ ^ 2) (hA : A₀ ≤ A) :
    A ^ k * Real.exp (-b * A ^ 2) ≤ A₀ ^ k * Real.exp (-b * A₀ ^ 2) := by
  have hx : 0 ≤ b * (A ^ 2 - A₀ ^ 2) := mul_nonneg hb.le (by nlinarith)
  have hA₀' : A₀ ≠ 0 := hA₀.ne'
  -- `(A/A₀)ᵏ ≤ e^{b(A² - A₀²)}`, which is `1 + x/k ≤ e^{x/k}` raised to the `k`-th power
  have hexp : A ^ k ≤ A₀ ^ k * Real.exp (b * (A ^ 2 - A₀ ^ 2)) := by
    rw [← div_le_iff₀' (pow_pos hA₀ k), ← div_pow]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using Real.one_le_exp hx
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hlin : A / A₀ ≤ 1 + b * (A ^ 2 - A₀ ^ 2) / k := by
      rw [div_le_iff₀ hA₀, ← sub_nonneg,
        show (1 + b * (A ^ 2 - A₀ ^ 2) / (k : ℝ)) * A₀ - A
          = (b * A₀ * (A + A₀) - k) * (A - A₀) / (k : ℝ) by field_simp; ring]
      have hkA : (k : ℝ) ≤ b * A₀ * (A + A₀) := by
        nlinarith [mul_nonneg (mul_nonneg hb.le hA₀.le) (sub_nonneg.2 hA),
          mul_pos hb (pow_pos hA₀ 2)]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hk0.le
    have hd : 0 ≤ b * (A ^ 2 - A₀ ^ 2) / k := div_nonneg hx hk0.le
    calc (A / A₀) ^ k ≤ (1 + b * (A ^ 2 - A₀ ^ 2) / k) ^ k :=
          pow_le_pow_left₀ (div_nonneg (by linarith) hA₀.le) hlin k
      _ ≤ Real.exp (b * (A ^ 2 - A₀ ^ 2) / k) ^ k :=
          pow_le_pow_left₀ (by linarith)
            (by linarith [Real.add_one_le_exp (b * (A ^ 2 - A₀ ^ 2) / k)]) k
      _ = Real.exp (b * (A ^ 2 - A₀ ^ 2)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  calc A ^ k * Real.exp (-b * A ^ 2)
      ≤ A₀ ^ k * Real.exp (b * (A ^ 2 - A₀ ^ 2)) * Real.exp (-b * A ^ 2) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = A₀ ^ k * Real.exp (-b * A₀ ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- Absolute convergence of the linear term of the saddle discrepancy against the model
integrand: `P₁` is a cubic, so the integrand is a combination of the model moments of orders
one and three. -/
theorem integrable_modelIntegrand_mul_saddleLinear_div (p S : ℂ) :
    Integrable fun w : ℝ ↦ modelIntegrand p (1 / 2) w
      * (saddleLinear (line (1 / 2) w - p) / S) := by
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  refine (((integrable_modelMomentIntegrand 1 p hhalf).const_mul (-(1 / 2) / S)).add
    ((integrable_modelMomentIntegrand 3 p hhalf).const_mul
      (-(2 * (π : ℂ) * I / 3) / S))).congr (.of_forall fun w ↦ ?_)
  simp only [Pi.add_apply, modelMomentIntegrand, saddleLinear]
  ring

/-- Above the threshold `T ≥ 16` the saddle `√T` is at least `4`. -/
theorem four_le_sqrt {t : ℝ} (ht : 16 ≤ t / (2 * π)) : 4 ≤ Real.sqrt (t / (2 * π)) :=
  Real.le_sqrt_of_sq_le (by nlinarith)

/-- The fractional part of `√T` keeps the centre of the model Gaussian within `1/2` of the
contour. -/
private theorem sq_sub_le {p : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2) : (1 / 2 - p) ^ 2 ≤ 1 / 4 := by
  nlinarith [sq_le_sq' (abs_le.1 hκ).1 (abs_le.1 hκ).2]

/-- The distance to the saddle is dominated by the centred contour parameter on the unit
interval of fractional parts. -/
private theorem norm_line_sub_ofReal_sq_le_of_abs_le {p : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2) (w : ℝ) :
    ‖line (1 / 2) w - (p : ℂ)‖ ^ 2 ≤ 2 * (w + (1 / 2 - p) / 2) ^ 2 + 1 / 8 := by
  rw [norm_line_sub_ofReal_sq]
  linarith [sq_sub_le hκ]

/-- The even powers of the distance to the saddle, against the centred contour parameter. -/
private theorem pow_four_le {Y u : ℝ} (hQ : Y ^ 2 ≤ 2 * u ^ 2 + 1 / 8) :
    Y ^ 4 ≤ (2 * u ^ 2 + 1 / 8) ^ 2 :=
  (pow_le_pow_left₀ (sq_nonneg Y) hQ 2).trans_eq' (by ring)

/-- The quadratic weight of the linear discrepancy, as an even polynomial in the centred contour
parameter. -/
private theorem discrepancy_weight_le {Y u : ℝ} (hQ : Y ^ 2 ≤ 2 * u ^ 2 + 1 / 8) :
    1 / 2 * Y ^ 2 + π * Y ^ 4 ≤ 1 / 16 + π / 64 + (1 + π / 2) * u ^ 2 + 4 * π * u ^ 4 := by
  have h4 : π * Y ^ 4 ≤ 4 * π * u ^ 4 + π / 2 * u ^ 2 + π / 64 := by
    have h := mul_le_mul_of_nonneg_left (pow_four_le hQ) Real.pi_pos.le
    nlinarith [h]
  linarith

/-- The quadratic weight of the exponential remainder, as an even polynomial in the centred
contour parameter. -/
private theorem exp_remainder_weight_le {Y u : ℝ} (hQ : Y ^ 2 ≤ 2 * u ^ 2 + 1 / 8) :
    Y ^ 2 + 8 * π / 3 * Y ^ 4 + 16 * π ^ 2 / 9 * Y ^ 6
      ≤ 1 / 8 + π / 24 + π ^ 2 / 288 + (2 + 4 * π / 3 + π ^ 2 / 6) * u ^ 2
        + (32 * π / 3 + 8 * π ^ 2 / 3) * u ^ 4 + 128 * π ^ 2 / 9 * u ^ 6 := by
  have h6 : Y ^ 6 ≤ (2 * u ^ 2 + 1 / 8) ^ 3 :=
    (pow_le_pow_left₀ (sq_nonneg Y) hQ 3).trans_eq' (by ring)
  have e4 : 8 * π / 3 * Y ^ 4 ≤ 8 * π / 3 * (2 * u ^ 2 + 1 / 8) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_four_le hQ) (by positivity)
  have e6 : 16 * π ^ 2 / 9 * Y ^ 6 ≤ 16 * π ^ 2 / 9 * (2 * u ^ 2 + 1 / 8) ^ 3 :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  nlinarith [e4, e6, hQ]

/-- The pointwise majorant for the linear discrepancy on the inner region: the model integrand
against `Δ - P₁(y)/√T`, dominated by the model Gaussian times an even polynomial of degree four. -/
private theorem norm_modelIntegrand_mul_saddleDiscrepancy_sub_linear_le {t : ℝ} (ht : 0 < t)
    {ν : ℕ} {p S w : ℝ} (hS : S = Real.sqrt (t / (2 * π))) (hp : p = S - ν)
    (hκ : |1 / 2 - p| ≤ 1 / 2) (hu : ‖line (1 / 2) w - (p : ℂ)‖ ≤ S / 2) :
    ‖modelIntegrand (p : ℂ) (1 / 2) w
        * (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)
            - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖
      ≤ 11 / 5 / (Real.sqrt 2 * (t / (2 * π)))
          * (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2)
              * (1 / 16 + π / 64 + (1 + π / 2) * (w + (1 / 2 - p) / 2) ^ 2
                  + 4 * π * (w + (1 / 2 - p) / 2) ^ 4)) := by
  subst hS
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hT0 : (0 : ℝ) < t / (2 * π) := by positivity
  have hxy := line_sub_ofReal_sub hp w
  have hx : ‖line ((ν : ℝ) + 1 / 2) w - ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)‖
      ≤ Real.sqrt (t / (2 * π)) / 2 := by rw [hxy]; exact hu
  have hd := norm_saddleDiscrepancy_sub_linear_le ht hx
  rw [hxy] at hd
  -- the model integrand is dominated by its Gaussian numerator, of peak `e^{π/4}`
  have h8 := norm_modelIntegrand_le_exp_neg_mul_sq hκ w
  -- abbreviations for the distance to the saddle and for the second-order remainder
  set Y : ℝ := ‖line (1 / 2) w - (p : ℂ)‖ with hYdef
  set R : ℂ := saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)
    - saddleLinear (line (1 / 2) w - (p : ℂ)) / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ) with hRdef
  calc ‖modelIntegrand (p : ℂ) (1 / 2) w * R‖
      = ‖modelIntegrand (p : ℂ) (1 / 2) w‖ * ‖R‖ := norm_mul _ _
    _ ≤ Real.exp (π / 4) * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) / Real.sqrt 2
          * ((1 / 2 * Y ^ 2 + π * Y ^ 4) / (t / (2 * π))) :=
        mul_le_mul h8 hd (norm_nonneg _) (by positivity)
    _ ≤ 11 / 5 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) / Real.sqrt 2
          * ((1 / 16 + π / 64 + (1 + π / 2) * (w + (1 / 2 - p) / 2) ^ 2
              + 4 * π * (w + (1 / 2 - p) / 2) ^ 4) / (t / (2 * π))) :=
        mul_le_mul
          ((div_le_div_iff_of_pos_right hs2).2
            (mul_le_mul_of_nonneg_right Real.exp_pi_div_four_le (Real.exp_nonneg _)))
          ((div_le_div_iff_of_pos_right hT0).2
            (discrepancy_weight_le (norm_line_sub_ofReal_sq_le_of_abs_le hκ w)))
          (div_nonneg (by positivity) hT0.le) (by positivity)
    _ = _ := by field_simp

/-- The pointwise majorant for the exponential remainder on the inner region: the model
integrand against `e^Δ - 1 - Δ`, dominated by the widened Gaussian times an even polynomial of
degree six. -/
private theorem norm_modelIntegrand_mul_exp_sub_one_sub_self_le {t : ℝ} (ht : 0 < t)
    {ν : ℕ} {p S w : ℝ} (hS : S = Real.sqrt (t / (2 * π))) (hp : p = S - ν)
    (hκ : |1 / 2 - p| ≤ 1 / 2) (hu : ‖line (1 / 2) w - (p : ℂ)‖ ≤ S / 2) :
    ‖modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
            - saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))‖
      ≤ 47 / 10 / (2 * Real.sqrt 2 * (t / (2 * π)))
          * (Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2)
              * (1 / 8 + π / 24 + π ^ 2 / 288
                  + (2 + 4 * π / 3 + π ^ 2 / 6) * (w + (1 / 2 - p) / 2) ^ 2
                  + (32 * π / 3 + 8 * π ^ 2 / 3) * (w + (1 / 2 - p) / 2) ^ 4
                  + 128 * π ^ 2 / 9 * (w + (1 / 2 - p) / 2) ^ 6)) := by
  subst hS
  have hpi := Real.pi_pos
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  have hT0 : (0 : ℝ) < t / (2 * π) := by positivity
  have hTS : Real.sqrt (t / (2 * π)) ^ 2 = t / (2 * π) := Real.sq_sqrt hT0.le
  have hxy := line_sub_ofReal_sub hp w
  have hx : ‖line ((ν : ℝ) + 1 / 2) w - ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)‖
      ≤ Real.sqrt (t / (2 * π)) / 2 := by rw [hxy]; exact hu
  have hd1 := norm_saddleDiscrepancy_le ht hx
  have hd3 := exp_norm_saddleDiscrepancy_mul_exp_le ht hx
  rw [hxy] at hd1 hd3
  have hsq := sq_sub_le hκ
  -- the model integrand, as a Gaussian in the distance to the saddle
  have h8 : ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ Real.exp (2 * π * (1 / 2 - p) ^ 2)
        * Real.exp (-(2 * π) * ‖line (1 / 2) w - (p : ℂ)‖ ^ 2) / Real.sqrt 2 := by
    refine (norm_modelIntegrand_le (p : ℂ) hhalf w).trans ?_
    rw [norm_exp_two_pi_mul_I_mul_line_sub_sq' p w]
  -- the squared discrepancy, in the units of the second-order error
  have hΔsq : ‖saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)‖ ^ 2
      ≤ (‖line (1 / 2) w - (p : ℂ)‖ ^ 2 + 8 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 4
          + 16 * π ^ 2 / 9 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 6) / (t / (2 * π)) := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hd1 2
    rw [div_pow, hTS] at h
    refine h.trans_eq ?_
    congr 1
    ring
  -- the peak of the widened Gaussian, after the exponent budget has been spent
  have hEc : Real.exp (2 * π * (1 / 2 - p) ^ 2)
      * (Real.exp (1 / 2) * Real.exp (-(2 * π / 3) * (1 / 2 - p) ^ 2)) ≤ 47 / 10 := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact (Real.exp_le_exp.2 (by nlinarith)).trans Real.exp_half_add_pi_div_three_le
  have hsplit : Real.exp (-(4 * π / 3) * ‖line (1 / 2) w - (p : ℂ)‖ ^ 2)
      = Real.exp (-(2 * π / 3) * (1 / 2 - p) ^ 2)
        * Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2) := by
    rw [← Real.exp_add, norm_line_sub_ofReal_sq]
    congr 1
    ring
  -- abbreviations for the distance to the saddle and for the discrepancy itself
  set Y : ℝ := ‖line (1 / 2) w - (p : ℂ)‖ with hYdef
  set D : ℂ := saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w) with hDdef
  calc ‖modelIntegrand (p : ℂ) (1 / 2) w * (exp D - 1 - D)‖
      = ‖modelIntegrand (p : ℂ) (1 / 2) w‖ * ‖exp D - 1 - D‖ := norm_mul _ _
    _ ≤ Real.exp (2 * π * (1 / 2 - p) ^ 2) * Real.exp (-(2 * π) * Y ^ 2) / Real.sqrt 2
          * (‖D‖ ^ 2 / 2 * Real.exp ‖D‖) :=
        mul_le_mul h8 (Complex.norm_exp_sub_one_sub_id_le' _) (norm_nonneg _) (by positivity)
    _ = Real.exp (2 * π * (1 / 2 - p) ^ 2) / (2 * Real.sqrt 2) * ‖D‖ ^ 2
          * (Real.exp ‖D‖ * Real.exp (-(2 * π) * Y ^ 2)) := by ring
    _ ≤ Real.exp (2 * π * (1 / 2 - p) ^ 2) / (2 * Real.sqrt 2)
          * ((Y ^ 2 + 8 * π / 3 * Y ^ 4 + 16 * π ^ 2 / 9 * Y ^ 6) / (t / (2 * π)))
          * (Real.exp (1 / 2) * Real.exp (-(4 * π / 3) * Y ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hΔsq (by positivity)) hd3 (by positivity)
          (mul_nonneg (by positivity) (div_nonneg (by positivity) hT0.le))
    _ = Real.exp (2 * π * (1 / 2 - p) ^ 2)
          * (Real.exp (1 / 2) * Real.exp (-(2 * π / 3) * (1 / 2 - p) ^ 2)) / (2 * Real.sqrt 2)
          * ((Y ^ 2 + 8 * π / 3 * Y ^ 4 + 16 * π ^ 2 / 9 * Y ^ 6) / (t / (2 * π)))
          * Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2) := by
        rw [hsplit]
        ring
    _ ≤ 47 / 10 / (2 * Real.sqrt 2)
          * ((1 / 8 + π / 24 + π ^ 2 / 288
              + (2 + 4 * π / 3 + π ^ 2 / 6) * (w + (1 / 2 - p) / 2) ^ 2
              + (32 * π / 3 + 8 * π ^ 2 / 3) * (w + (1 / 2 - p) / 2) ^ 4
              + 128 * π ^ 2 / 9 * (w + (1 / 2 - p) / 2) ^ 6) / (t / (2 * π)))
          * Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul ?_ ?_ ?_ ?_) (Real.exp_nonneg _)
        · exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)).2 hEc
        · exact (div_le_div_iff_of_pos_right hT0).2
            (exp_remainder_weight_le (norm_line_sub_ofReal_sq_le_of_abs_le hκ w))
        · exact div_nonneg (by positivity) hT0.le
        · positivity
    _ = _ := by field_simp

/-- The numerical constant of the sharp inner estimate. -/
private theorem sharp_inner_constant_le :
    11 / 5 * (1 / 2 * (1 / 8 + π / 64 + 5 / (16 * π)))
      + 47 / 20 * ((π ^ 3 + 21 * π ^ 2 + 189 * π + 837) / (288 * π)) * Real.sqrt (3 / 8)
      ≤ 299 / 100 := by
  have hπ1 : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hπ2 : π < 3.1416 := Real.pi_lt_d4
  have hs : Real.sqrt (3 / 8) ≤ 0.6124 := by
    rw [show (0.6124 : ℝ) = Real.sqrt (0.6124 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hA : 11 / 5 * (1 / 2 * (1 / 8 + π / 64 + 5 / (16 * π))) ≤ 0.3010 := by
    have h1 : (5 : ℝ) / (16 * π) ≤ 5 / (16 * 3.1415) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hBR : (π ^ 3 + 21 * π ^ 2 + 189 * π + 837) / (288 * π) ≤ 1.845 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hprod : (π ^ 3 + 21 * π ^ 2 + 189 * π + 837) / (288 * π) * Real.sqrt (3 / 8)
      ≤ 1.845 * 0.6124 :=
    mul_le_mul hBR hs (Real.sqrt_nonneg _) (by norm_num)
  linarith

/-- The sharp inner saddle-point estimate (`riemann_siegel_first.tex`, `lem:rsf_inner_sharp`):
over the region `|w| ≤ W = (√T - 1)/(2√2)` about the saddle, the model integrand against the
second-order remainder `e^Δ - 1 - P₁(y)/√T` contributes at most `(299/100) T^{-1}`. -/
theorem norm_integral_inner_sub_linear_le {t : ℝ} (ht : 16 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖(1 + I) * ∫ w in Set.Icc (-sharpSplitRadius t) (sharpSplitRadius t),
        modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
              - saddleLinear (line (1 / 2) w - ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ))
                  / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ))‖
      ≤ 299 / 100 / (t / (2 * π)) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  -- abbreviations for the splitting radius, the saddle `√T` and the fractional part `p`
  set W : ℝ := sharpSplitRadius t with hWdef
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set p : ℝ := S - (ν : ℝ) with hpdef
  clear_value p S W
  have hS4 : 4 ≤ S := by rw [hSdef]; exact four_le_sqrt ht
  have hW : W = (S - 1) / (2 * Real.sqrt 2) := by rw [hWdef, hSdef, sharpSplitRadius]
  have hκ : |1 / 2 - p| ≤ 1 / 2 := by
    rw [abs_le, hpdef]
    constructor <;> linarith
  -- on the inner region the expansion parameter stays inside the Taylor radius `1/2`
  have hy : ∀ w ∈ Set.Icc (-W) W, ‖line (1 / 2) w - (p : ℂ)‖ ≤ S / 2 := fun w hw ↦ by
    have habs : |w| ≤ W := abs_le.2 ⟨hw.1, hw.2⟩
    rw [hW, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)] at habs
    exact (norm_line_sub_ofReal_le (1 / 2) w p).trans
      (by linarith [(abs_le.1 hκ).1, (abs_le.1 hκ).2])
  -- the Gaussian majorant: two Gaussians in the centred parameter, of different widths
  set maj : ℝ → ℝ := fun w ↦
    11 / 5 / (Real.sqrt 2 * (t / (2 * π))) *
      (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
        (1 / 16 + π / 64 + (1 + π / 2) * (w + (1 / 2 - p) / 2) ^ 2
          + 4 * π * (w + (1 / 2 - p) / 2) ^ 4))
    + 47 / 10 / (2 * Real.sqrt 2 * (t / (2 * π))) *
      (Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2) *
        (1 / 8 + π / 24 + π ^ 2 / 288
          + (2 + 4 * π / 3 + π ^ 2 / 6) * (w + (1 / 2 - p) / 2) ^ 2
          + (32 * π / 3 + 8 * π ^ 2 / 3) * (w + (1 / 2 - p) / 2) ^ 4
          + 128 * π ^ 2 / 9 * (w + (1 / 2 - p) / 2) ^ 6)) with hmajdef
  clear_value maj
  have hc1 : (0 : ℝ) < 11 / 5 / (Real.sqrt 2 * (t / (2 * π))) :=
    div_pos (by norm_num) (mul_pos hs2 hT0)
  have hc2 : (0 : ℝ) < 47 / 10 / (2 * Real.sqrt 2 * (t / (2 * π))) :=
    div_pos (by norm_num) (by positivity)
  have hmaj0 : ∀ w : ℝ, 0 ≤ maj w := fun w ↦ by
    rw [hmajdef]
    exact add_nonneg (mul_nonneg hc1.le (by positivity)) (mul_nonneg hc2.le (by positivity))
  have hint1 : Integrable fun w : ℝ ↦ 11 / 5 / (Real.sqrt 2 * (t / (2 * π))) *
      (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
        (1 / 16 + π / 64 + (1 + π / 2) * (w + (1 / 2 - p) / 2) ^ 2
          + 4 * π * (w + (1 / 2 - p) / 2) ^ 4)) :=
    ((integrable_exp_neg_mul_sq_mul_even_quartic (b := 4 * π) (by positivity) _ _
      _).comp_add_right _).const_mul _
  have hint2 : Integrable fun w : ℝ ↦ 47 / 10 / (2 * Real.sqrt 2 * (t / (2 * π))) *
      (Real.exp (-(8 * π / 3) * (w + (1 / 2 - p) / 2) ^ 2) *
        (1 / 8 + π / 24 + π ^ 2 / 288
          + (2 + 4 * π / 3 + π ^ 2 / 6) * (w + (1 / 2 - p) / 2) ^ 2
          + (32 * π / 3 + 8 * π ^ 2 / 3) * (w + (1 / 2 - p) / 2) ^ 4
          + 128 * π ^ 2 / 9 * (w + (1 / 2 - p) / 2) ^ 6)) :=
    ((integrable_exp_neg_mul_sq_mul_even_poly (b := 8 * π / 3) (by positivity) _ _ _
      _).comp_add_right _).const_mul _
  have hmajint : Integrable maj := by rw [hmajdef]; exact hint1.add hint2
  -- the value of the majorant integral, by the even moments of a Gaussian
  have hsqrt1 : Real.sqrt (π / (4 * π)) = 1 / 2 := by
    rw [show π / (4 * π) = (1 / 2 : ℝ) ^ 2 by rw [div_eq_iff (by positivity)]; ring,
      Real.sqrt_sq (by norm_num)]
  have hsqrt2 : Real.sqrt (π / (8 * π / 3)) = Real.sqrt (3 / 8) := by
    rw [show π / (8 * π / 3) = (3 : ℝ) / 8 by rw [div_eq_iff (by positivity)]; ring]
  have hmajval : ∫ w : ℝ, maj w
      = 11 / 5 / (Real.sqrt 2 * (t / (2 * π))) * (1 / 2 * (1 / 8 + π / 64 + 5 / (16 * π)))
        + 47 / 10 / (2 * Real.sqrt 2 * (t / (2 * π)))
          * ((π ^ 3 + 21 * π ^ 2 + 189 * π + 837) / (288 * π) * Real.sqrt (3 / 8)) := by
    rw [hmajdef, integral_add hint1 hint2, integral_const_mul, integral_const_mul,
      integral_exp_neg_mul_sq_mul_even_quartic_comp_add_right
        (by positivity : (0 : ℝ) < 4 * π),
      integral_exp_neg_mul_sq_mul_even_poly_comp_add_right
        (by positivity : (0 : ℝ) < 8 * π / 3), hsqrt1, hsqrt2]
    have hπ0 : π ≠ 0 := Real.pi_ne_zero
    have hs2' : Real.sqrt 2 ≠ 0 := hs2.ne'
    have hT0' : t / (2 * π) ≠ 0 := hT0.ne'
    field_simp
    ring
  -- integrability of the second-order remainder against the model integrand
  have hExp : Integrable fun w : ℝ ↦ modelIntegrand (p : ℂ) (1 / 2) w
      * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) := by
    have h := integrable_modelIntegrand_mul_exp_saddleDiscrepancy ht0 ν
    rwa [← hSdef, ← hpdef] at h
  have hLin := integrable_modelIntegrand_mul_saddleLinear_div (p : ℂ) (S : ℂ)
  have hFint : Integrable fun w : ℝ ↦ modelIntegrand (p : ℂ) (1 / 2) w
      * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
          - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ)) :=
    (((hExp.sub (integrable_modelIntegrand (p : ℂ) hhalf)).sub hLin)).congr
      (.of_forall fun w ↦ by simp only [Pi.sub_apply]; ring)
  -- the pointwise majorant on the inner region
  have key : ∀ w ∈ Set.Icc (-W) W, ‖modelIntegrand (p : ℂ) (1 / 2) w
      * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
          - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖ ≤ maj w := by
    intro w hw
    have hu := hy w hw
    rw [show modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
              - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))
        = modelIntegrand (p : ℂ) (1 / 2) w
            * (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)
                - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))
          + modelIntegrand (p : ℂ) (1 / 2) w
            * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
                - saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) by ring, hmajdef]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_modelIntegrand_mul_saddleDiscrepancy_sub_linear_le ht0 hSdef hpdef hκ hu)
      (norm_modelIntegrand_mul_exp_sub_one_sub_self_le ht0 hSdef hpdef hκ hu))
  calc ‖(1 + I) * ∫ w in Set.Icc (-W) W, modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
            - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖
      ≤ Real.sqrt 2 * ∫ w in Set.Icc (-W) W, ‖modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1
              - saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖ :=
        norm_one_add_I_mul_integral_le _
    _ ≤ Real.sqrt 2 * ∫ w in Set.Icc (-W) W, maj w :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on hFint.norm.integrableOn
          hmajint.integrableOn measurableSet_Icc key) hs2.le
    _ ≤ Real.sqrt 2 * ∫ w : ℝ, maj w :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hmajint (.of_forall hmaj0)) hs2.le
    _ = (11 / 5 * (1 / 2 * (1 / 8 + π / 64 + 5 / (16 * π)))
          + 47 / 20 * ((π ^ 3 + 21 * π ^ 2 + 189 * π + 837) / (288 * π)) * Real.sqrt (3 / 8))
            / (t / (2 * π)) := by
        rw [hmajval]
        field_simp
        ring
    _ ≤ 299 / 100 / (t / (2 * π)) := by
        gcongr
        exact sharp_inner_constant_le

end Zeta.RiemannSiegel
