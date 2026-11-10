/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Explicit bounds for the exponential

An unrestricted bound `‖z‖² e^{‖z‖}/2` for the quadratic Taylor remainder `exp z - 1 - z`, and two
numerical values of `exp`. Mathlib's `Complex.norm_exp_sub_one_sub_id_le` needs `‖z‖ ≤ 1`, and
`Complex.norm_exp_sub_sum_le_norm_mul_exp` loses the factor `1/2`, which the Riemann–Siegel saddle
estimate (`riemann_siegel_first.tex`, `lem:rsf_inner_sharp`) cannot afford.

## Main results

* `Real.exp_sub_one_sub_id_le`: `e^r - 1 - r ≤ (r²/2) e^r` for `r ≥ 0`;
* `Complex.norm_exp_sub_one_sub_id_le'`: `‖e^z - 1 - z‖ ≤ (‖z‖²/2) e^{‖z‖}`, for every `z`;
* `Real.exp_pi_div_four_le`, `Real.exp_half_add_pi_div_three_le`: `e^{π/4} ≤ 11/5` and
  `e^{1/2 + π/3} ≤ 47/10`.
-/
@[expose] public section


open scoped Nat Real

namespace Real

private theorem hasDerivAt_sq_div_two_sub_one_add_exp_neg_mul (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2 - 1 + exp (-y) * (1 + y)) (x - x * exp (-x)) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2) x x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  have h2 : HasDerivAt (fun y : ℝ ↦ exp (-y)) (-exp (-x)) x := by
    simpa using (hasDerivAt_neg x).exp
  have h3 : HasDerivAt (fun y : ℝ ↦ (1 : ℝ) + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  rw [show x - x * exp (-x) = x + (-exp (-x) * (1 + x) + exp (-x) * 1) by ring]
  exact (h1.sub_const 1).add (h2.mul h3)

/-- The quadratic Taylor remainder of the real exponential: `e^r - 1 - r ≤ (r²/2) e^r` for
`r ≥ 0`. -/
theorem exp_sub_one_sub_id_le {r : ℝ} (hr : 0 ≤ r) : exp r - 1 - r ≤ r ^ 2 / 2 * exp r := by
  have hd := hasDerivAt_sq_div_two_sub_one_add_exp_neg_mul
  have hmono : MonotoneOn (fun y : ℝ ↦ y ^ 2 / 2 - 1 + exp (-y) * (1 + y)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt) fun x hx ↦ ?_
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have hx0 : (0 : ℝ) < x := hx
    nlinarith [exp_le_one_iff.2 (neg_nonpos.2 hx0.le)]
  have hkey : 0 ≤ r ^ 2 / 2 - 1 + exp (-r) * (1 + r) := by
    simpa using hmono Set.self_mem_Ici hr hr
  have he : exp (-r) * exp r = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  have h2 : 0 ≤ (r ^ 2 / 2 - 1 + exp (-r) * (1 + r)) * exp r := mul_nonneg hkey (exp_pos r).le
  have h3 : (r ^ 2 / 2 - 1 + exp (-r) * (1 + r)) * exp r
      = r ^ 2 / 2 * exp r - exp r + (1 + r) := by linear_combination (1 + r) * he
  rw [h3] at h2
  linarith

/-- An explicit upper bound for `e^{π/4}`. -/
theorem exp_pi_div_four_le : exp (π / 4) ≤ 11 / 5 := by
  have h : π / 4 ≤ 0.7854 := by linarith [pi_lt_d4]
  refine (exp_le_exp.2 h).trans ?_
  refine (exp_bound' (by norm_num) (by norm_num) (n := 4) (by norm_num)).trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- An explicit upper bound for `e^{1/2 + π/3}`. -/
theorem exp_half_add_pi_div_three_le : exp (1 / 2 + π / 3) ≤ 47 / 10 := by
  -- `1/2 + π/3 ≤ 1.5472 = 4 · 0.3868`, and the quartic power keeps `exp_bound'` inside its
  -- radius of validity: `1.4723 ^ 4 = 4.6988 ≤ 4.7`
  have h : 1 / 2 + π / 3 ≤ (4 : ℕ) * 0.3868 := by push_cast; linarith [pi_lt_d4]
  have hb : exp 0.3868 ≤ 1.4723 := by
    refine (exp_bound' (by norm_num) (by norm_num) (n := 6) (by norm_num)).trans ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc exp (1 / 2 + π / 3) ≤ exp ((4 : ℕ) * 0.3868) := exp_le_exp.2 h
    _ = exp 0.3868 ^ 4 := exp_nat_mul _ 4
    _ ≤ 1.4723 ^ 4 := pow_le_pow_left₀ (exp_pos _).le hb 4
    _ ≤ 47 / 10 := by norm_num

end Real

namespace Complex

/-- The quadratic Taylor remainder of the complex exponential, for every `z`. -/
theorem norm_exp_sub_one_sub_id_le' (z : ℂ) : ‖exp z - 1 - z‖ ≤ ‖z‖ ^ 2 / 2 * Real.exp ‖z‖ := by
  have h := norm_exp_sub_sum_le_exp_norm_sub_sum z 2
  have hz : ∑ m ∈ Finset.range 2, z ^ m / (m ! : ℂ) = 1 + z := by
    simp [Finset.sum_range_succ]
  have hr : ∑ m ∈ Finset.range 2, ‖z‖ ^ m / (m ! : ℝ) = 1 + ‖z‖ := by
    simp [Finset.sum_range_succ]
  rw [hz, hr] at h
  rw [sub_sub]
  refine h.trans ?_
  linarith [Real.exp_sub_one_sub_id_le (norm_nonneg z)]

end Complex
