/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Zeta.Analysis.SpecialFunctions.Gaussian
public import Zeta.RiemannSiegel.Integral
public import Zeta.RiemannSiegel.Phase

/-!
# The order-zero bound for the shifted Riemann–Siegel integral

On the critical line `s = 1/2 + it` the contour integral `Zeta.RiemannSiegel.contourIntegral` over
the far contour `L(a)` is *small*, of size `O(t^{-1/4})`, and it is this smallness that makes the
Riemann–Siegel formula an approximation (`riemann_siegel.tex`, `sec:rs_bound`).

The bound is `2^{5/4} a^{-1/2} e^{B²/4π}`, with `B = 2π|T - a²|/a`: along a half-integer contour the
integrand has modulus `‖x‖^{-1/2} e^{φ(w)} / (2|sin πx|)` with `‖x‖ ≥ a/√2` and `2|sin πx| ≥ √2`,
while the phase estimate `Zeta.RiemannSiegel.phase_le` dominates `e^{φ}` by the Gaussian
`e^{-πw² + B|w|}`, of integral at most `2 e^{B²/4π}`.

The crossing point `a` is taken at the half-integer `⌊√T⌋ + 1/2` nearest the saddle `√T` of the
integrand, `T = t/2π`. Crossing at the saddle itself would make `B = 0`, but there the lower bound
on `|sin πx|` degenerates; the resulting loss, a factor `e^{B²/4π} ≤ 37.12`, is exactly what the
first-order theory recovers as the classical correction term `Ψ(p)`.

## Main results

* `Zeta.RiemannSiegel.norm_contourIntegrand_le`: the Gaussian majorant for the integrand;
* `Zeta.RiemannSiegel.norm_contourIntegrand_le'`: its sharp form for `|w| ≥ 1`, which keeps both the
  phase and the full exponential decay of the kernel's denominator;
* `Zeta.RiemannSiegel.norm_contourIntegral_le`: `|I(1/2 + it, a)| ≤ 2^{5/4} a^{-1/2} e^{B²/4π}`;
* `Zeta.RiemannSiegel.norm_contourIntegral_le_ninetyFive`,
  `Zeta.RiemannSiegel.norm_contourIntegral_le_hundredFiftyOne`: the numerical forms
  `≤ 95 T^{-1/4}` and `≤ 151 t^{-1/4}`, valid for `t ≥ 32π`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- **The gap between `T` and `a²` at a crossing point `a` within `½` of the saddle `S = √T`.** -/
theorem abs_sub_sq_le {T S a : ℝ} (hTS : S ^ 2 = T) (h0 : 0 ≤ S + a) (h1 : S - 1 / 2 ≤ a)
    (h2 : a ≤ S + 1 / 2) : |T - a ^ 2| ≤ a + 1 / 4 := by
  rw [← hTS, show S ^ 2 - a ^ 2 = (S - a) * (S + a) by ring, abs_mul, abs_of_nonneg h0]
  calc |S - a| * (S + a) ≤ 1 / 2 * (S + a) := by
        gcongr
        exact abs_le.2 ⟨by linarith, by linarith⟩
    _ ≤ a + 1 / 4 := by linarith

/-- **The comparison `T ≤ c⁴a²` in the `rpow` exponents of the order-zero bound.** -/
theorem rpow_neg_half_le_mul_rpow_neg_quarter {T a c : ℝ} (ha : 0 < a) (hT : 0 < T) (hc : 0 < c)
    (h : T ≤ c ^ 4 * a ^ 2) : a ^ (-(1 / 2) : ℝ) ≤ c * T ^ (-(1 / 4) : ℝ) := by
  have key : T ^ (1 / 4 : ℝ) ≤ c * a ^ (1 / 2 : ℝ) :=
    (Real.rpow_le_rpow hT.le h (by norm_num)).trans_eq <| by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast c 4,
        ← Real.rpow_natCast a 2, ← Real.rpow_mul hc.le, ← Real.rpow_mul ha.le]
      norm_num
  rw [Real.rpow_neg ha.le, Real.rpow_neg hT.le, inv_eq_one_div, inv_eq_one_div, mul_one_div,
    div_le_div_iff₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hT _)]
  linarith

/-- **The triangle bound for a multiplicative perturbation `E - 1`.** -/
theorem norm_mul_sub_one_le (A E : ℂ) : ‖A * (E - 1)‖ ≤ ‖A * E‖ + ‖A‖ := by
  rw [mul_sub, mul_one]
  exact norm_sub_le _ _

/-- **The crossing point controls the contour**: `|x|^{-1/2} ≤ 2^{1/4} a^{-1/2}` along `L(a)`,
since `|x| ≥ a/√2`. -/
private theorem norm_line_rpow_neg_half_le {a : ℝ} (ha0 : 0 < a) (w : ℝ) :
    ‖line a w‖ ^ (-(1 / 2) : ℝ) ≤ 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hlb : (0 : ℝ) < a / Real.sqrt 2 := by positivity
  have hxlb : a / Real.sqrt 2 ≤ ‖line a w‖ := norm_line_ge a w
  rw [show 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) = (a / Real.sqrt 2) ^ (-(1 / 2) : ℝ) by
    rw [Real.div_rpow ha0.le hs2.le, Real.rpow_neg hs2.le,
      show Real.sqrt 2 ^ (1 / 2 : ℝ) = 2 ^ (1 / 4 : ℝ) by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num,
      div_inv_eq_mul]
    ring]
  exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num) (Set.mem_Ioi.2 hlb)
    (Set.mem_Ioi.2 (hlb.trans_le hxlb)) hxlb

/-- **The Gaussian majorant for the Riemann–Siegel integrand on the critical line.** -/
theorem norm_contourIntegrand_le {t a : ℝ} {n : ℤ} (ht : 0 ≤ t) (ha : a = n + 1 / 2) (ha0 : 0 < a)
    (hT : t / (2 * π) ≤ 2 * a ^ 2) (w : ℝ) :
    ‖contourIntegrand (1 / 2 + t * I) a w‖
      ≤ 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) / Real.sqrt 2 *
        Real.exp (-(π * w ^ 2) + 2 * π * |t / (2 * π) - a ^ 2| / a * |w|) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hsinlb : Real.sqrt 2 / 2 ≤ ‖sin ((π : ℂ) * line a w)‖ := norm_sin_pi_mul_line_ge ha w
  have hpow := norm_line_rpow_neg_half_le ha0 w
  have hph : Real.exp (phase t a w)
      ≤ Real.exp (-(π * w ^ 2) + 2 * π * |t / (2 * π) - a ^ 2| / a * |w|) :=
    Real.exp_le_exp.2 (phase_le ht ha0 hT w)
  rw [norm_contourIntegrand, norm_slantCpow_mul_exp_eq_phase ha0.ne' t w, div_mul_eq_mul_div]
  gcongr
  linarith

/-- **The sharp majorant for the integrand outside the unit interval**: beyond `|w| = 1` the
kernel's denominator contributes its full exponential decay `e^{π|w|}`, rather than the constant
`√2/2` of `Zeta.RiemannSiegel.norm_contourIntegrand_le`, and the phase is retained rather than
dominated by a Gaussian (`riemann_siegel_first.tex`, `lem:rsf_outer_sharp`). No hypothesis on `a`
beyond positivity is needed: away from the real axis the lower bound on `|sin (πx)|` is uniform. -/
theorem norm_contourIntegrand_le' {t a : ℝ} (ha0 : 0 < a) {w : ℝ} (hw : 1 ≤ |w|) :
    ‖contourIntegrand (1 / 2 + t * I) a w‖
      ≤ 100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ))
        * Real.exp (phase t a w - π * |w|) := by
  have hE : (0 : ℝ) < Real.exp (π * |w|) := Real.exp_pos _
  have hsin : 99 / 200 * Real.exp (π * |w|) ≤ ‖sin ((π : ℂ) * line a w)‖ :=
    mul_exp_le_norm_sin_pi_mul_line a hw
  have hpow := norm_line_rpow_neg_half_le ha0 w
  have hEp : (0 : ℝ) < Real.exp (phase t a w) := Real.exp_pos _
  have hsin2 : (0 : ℝ) < 2 * ‖sin ((π : ℂ) * line a w)‖ := by nlinarith
  have hK0 : (0 : ℝ) ≤ 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg ha0.le _)
  rw [norm_contourIntegrand, norm_slantCpow_mul_exp_eq_phase ha0.ne' t w, div_le_iff₀ hsin2,
    Real.exp_sub]
  calc ‖line a w‖ ^ (-(1 / 2) : ℝ) * Real.exp (phase t a w)
      ≤ 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) * Real.exp (phase t a w) :=
        mul_le_mul_of_nonneg_right hpow hEp.le
    _ = 100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ))
          * (Real.exp (phase t a w) / Real.exp (π * |w|)) * (99 / 100 * Real.exp (π * |w|)) := by
        field_simp
    _ ≤ 100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ))
          * (Real.exp (phase t a w) / Real.exp (π * |w|))
          * (2 * ‖sin ((π : ℂ) * line a w)‖) :=
        mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg (mul_nonneg (by norm_num) hK0) (by positivity))

/-- **The order-zero bound for the shifted Riemann–Siegel integral**, in which `B = 2π|T - a²|/a`
measures the distance, in units of the contour, from the crossing point `a` to the saddle `√T`. -/
theorem norm_contourIntegral_le {t a : ℝ} {n : ℤ} (ht : 0 ≤ t) (ha : a = n + 1 / 2) (ha0 : 0 < a)
    (hT : t / (2 * π) ≤ 2 * a ^ 2) :
    ‖contourIntegral (1 / 2 + t * I) a‖
      ≤ 2 ^ (5 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) *
        Real.exp ((2 * π * |t / (2 * π) - a ^ 2| / a) ^ 2 / (4 * π)) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  set B := 2 * π * |t / (2 * π) - a ^ 2| / a
  set K := 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) / Real.sqrt 2 with hKdef
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hint := integrable_contourIntegrand (1 / 2 + (t : ℂ) * I) ha0 (by positivity)
    (norm_sin_pi_mul_line_ge ha)
  have hbody : ∫ w : ℝ, ‖contourIntegrand (1 / 2 + t * I) a w‖
      ≤ K * (2 * Real.exp (B ^ 2 / (4 * π))) := by
    calc ∫ w : ℝ, ‖contourIntegrand (1 / 2 + t * I) a w‖
        ≤ ∫ w : ℝ, K * Real.exp (-(π * w ^ 2) + B * |w|) :=
          integral_mono hint.norm ((integrable_exp_neg_pi_mul_sq_add_mul_abs B).const_mul K)
            fun w ↦ norm_contourIntegrand_le ht ha ha0 hT w
      _ = K * ∫ w : ℝ, Real.exp (-(π * w ^ 2) + B * |w|) := integral_const_mul K _
      _ ≤ K * (2 * Real.exp (B ^ 2 / (4 * π))) :=
          mul_le_mul_of_nonneg_left (integral_exp_neg_pi_mul_sq_add_mul_abs_le B) hK0
  have hconst : Real.sqrt 2 * (K * 2) = 2 ^ (5 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) := by
    rw [hKdef, show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add two_pos, Real.rpow_one]
    field_simp
  calc ‖contourIntegral (1 / 2 + t * I) a‖
      ≤ Real.sqrt 2 * ∫ w : ℝ, ‖contourIntegrand (1 / 2 + t * I) a w‖ := by
        rw [contourIntegral]; exact norm_one_add_I_mul_integral_le _
    _ ≤ Real.sqrt 2 * (K * (2 * Real.exp (B ^ 2 / (4 * π)))) :=
        mul_le_mul_of_nonneg_left hbody hs2.le
    _ = 2 ^ (5 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) * Real.exp (B ^ 2 / (4 * π)) := by
        rw [← hconst]; ring

private theorem exp_three_point_six_le : Real.exp 3.60643 ≤ 37.12 := by
  have hexp4 : Real.exp 4 ≤ 54.5981501 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
    exact (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4).trans (by norm_num)
  have hq : (1.4710186 : ℝ) ≤ Real.exp 0.39357 := by
    linarith [Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.39357)]
  have hsplit : Real.exp 3.60643 * Real.exp 0.39357 = Real.exp 4 := by
    rw [← Real.exp_add]; norm_num
  linarith [mul_nonneg (Real.exp_pos (3.60643 : ℝ)).le (sub_nonneg.2 hq)]

private theorem two_rpow_five_div_four_le : (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 2.379 := by
  rw [show (2 : ℝ) ^ (5 / 4 : ℝ) = 2 * Real.sqrt (Real.sqrt 2) by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (5 / 4 : ℝ) = 1 + 1 / 2 * (1 / 2) by norm_num, Real.rpow_add two_pos, Real.rpow_one]]
  have hs : Real.sqrt (Real.sqrt 2) ≤ 1.1895 :=
    (Real.sqrt_le_left (by norm_num)).2 ((Real.sqrt_le_left (by norm_num)).2 (by norm_num))
  linarith

private theorem two_mul_pi_rpow_one_div_four_le : (2 * π : ℝ) ^ (1 / 4 : ℝ) ≤ 1.5833 := by
  rw [show (2 * π : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt (2 * π)) by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
    norm_num]
  exact (Real.sqrt_le_left (by norm_num)).2
    ((Real.sqrt_le_left (by norm_num)).2 (by nlinarith [Real.pi_lt_d6]))

/-- **The numerical form of the order-zero bound**, at the half-integer crossing point nearest the
saddle: `|I(1/2 + it, ⌊√T⌋ + 1/2)| ≤ 95 T^{-1/4}` for `t ≥ 32π`. -/
theorem norm_contourIntegral_le_ninetyFive {t a : ℝ} {n : ℤ} (ht : 32 * π ≤ t) (ha : a = n + 1 / 2)
    (hn : (n : ℝ) ≤ Real.sqrt (t / (2 * π))) (hn' : Real.sqrt (t / (2 * π)) < n + 1) :
    ‖contourIntegral (1 / 2 + t * I) a‖ ≤ 95 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
  have hpi := Real.pi_pos
  have ht0 : (0 : ℝ) ≤ t := by nlinarith
  have hT0 : (0 : ℝ) ≤ t / (2 * π) := by positivity
  have hT16 : (16 : ℝ) ≤ t / (2 * π) := by rw [le_div_iff₀ (by positivity)]; linarith
  set S := Real.sqrt (t / (2 * π)) with hSdef
  have hS0 : (0 : ℝ) ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = t / (2 * π) := Real.sq_sqrt hT0
  have hS4 : (4 : ℝ) ≤ S := by nlinarith
  have haS : S - 1 / 2 ≤ a := by rw [ha]; linarith
  have haS' : a ≤ S + 1 / 2 := by rw [ha]; linarith
  have ha0 : (0 : ℝ) < a := by linarith
  have ha35 : (7 : ℝ) / 2 ≤ a := by linarith
  have hTle : t / (2 * π) ≤ 2 * a ^ 2 := by nlinarith
  -- the crossing point is within `1/2` of the saddle, so `B ≤ 15π/7`
  have habs : |t / (2 * π) - a ^ 2| ≤ a + 1 / 4 := abs_sub_sq_le hSsq (by linarith) haS haS'
  have hB0 : (0 : ℝ) ≤ 2 * π * |t / (2 * π) - a ^ 2| / a := by positivity
  have hB : 2 * π * |t / (2 * π) - a ^ 2| / a ≤ 15 * π / 7 := by
    rw [div_le_iff₀ ha0]
    nlinarith [mul_le_mul_of_nonneg_left habs (by positivity : (0 : ℝ) ≤ 2 * π),
      mul_nonneg hpi.le (by linarith : (0 : ℝ) ≤ a - 7 / 2)]
  have hBsq : (2 * π * |t / (2 * π) - a ^ 2| / a) ^ 2 / (4 * π) ≤ 3.60643 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hB, hB0, Real.pi_lt_d6, mul_nonneg hpi.le
      (by linarith [Real.pi_lt_d6] : (0 : ℝ) ≤ 3.141593 - π)]
  -- the loss from crossing at a half-integer rather than at the saddle
  have hexp : Real.exp ((2 * π * |t / (2 * π) - a ^ 2| / a) ^ 2 / (4 * π)) ≤ 37.12 :=
    (Real.exp_le_exp.2 hBsq).trans exp_three_point_six_le
  -- `a^{-1/2} ≤ 1.07 T^{-1/4}`, since `a ≥ (7/8)√T`
  have hrpow : a ^ (-(1 / 2) : ℝ) ≤ 1.07 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) :=
    rpow_neg_half_le_mul_rpow_neg_quarter ha0 (by linarith) (by norm_num) (by nlinarith)
  refine (norm_contourIntegral_le ht0 ha ha0 hTle).trans ?_
  have hTpow : (0 : ℝ) ≤ (t / (2 * π)) ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg hT0 _
  calc 2 ^ (5 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) *
        Real.exp ((2 * π * |t / (2 * π) - a ^ 2| / a) ^ 2 / (4 * π))
      ≤ 2.379 * (1.07 * (t / (2 * π)) ^ (-(1 / 4) : ℝ)) * 37.12 :=
        mul_le_mul (mul_le_mul two_rpow_five_div_four_le hrpow (by positivity) (by norm_num)) hexp
          (Real.exp_pos _).le (by positivity)
    _ ≤ 95 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by linarith

/-- **The order-zero bound in terms of `t`** rather than of `T = t/2π`. -/
theorem norm_contourIntegral_le_hundredFiftyOne {t a : ℝ} {n : ℤ} (ht : 32 * π ≤ t)
    (ha : a = n + 1 / 2) (hn : (n : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hn' : Real.sqrt (t / (2 * π)) < n + 1) :
    ‖contourIntegral (1 / 2 + t * I) a‖ ≤ 151 * t ^ (-(1 / 4) : ℝ) := by
  have hpi := Real.pi_pos
  have ht0 : (0 : ℝ) < t := by nlinarith
  refine (norm_contourIntegral_le_ninetyFive ht ha hn hn').trans ?_
  have hsplit : (t / (2 * π)) ^ (-(1 / 4) : ℝ)
      = t ^ (-(1 / 4) : ℝ) * (2 * π) ^ (1 / 4 : ℝ) := by
    rw [Real.div_rpow ht0.le (by positivity), Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * π),
      div_inv_eq_mul]
  have h0 : (0 : ℝ) ≤ t ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg ht0.le _
  rw [hsplit]
  nlinarith [mul_nonneg h0 (sub_nonneg.2 two_mul_pi_rpow_one_div_four_le)]

end Zeta.RiemannSiegel
