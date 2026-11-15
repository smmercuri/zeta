/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gamma.Growth
public import Zeta.RiemannXi
public import Zeta.ArgZeta.Basic
public import PrimeNumberTheoremAnd.ZetaBounds

/-!
# Order-one growth of the Riemann ξ-function

The order-one growth bound `‖ξ(s)‖ ≤ exp(C |s| log|s|)` for `|s| ≥ 2`, together with the
half-plane bound for `Γ` and the polynomial bound for `ζ` that feed it (`xi_order.tex`).

## Main results

* `norm_Gamma_le_strip_quarter_two` (`lem:xo_gamma_strip_bounded`).
* `norm_Gamma_le_exp_halfplane` (`lem:xo_gamma_halfplane`).
* `norm_riemannZeta_sub_head_le` (`lem:xo_zeta_em2`).
* `norm_riemannZeta_le_const_mul_of_half_le_re` (`lem:xo_zeta_poly`).
* `norm_riemannXi_le_exp` (`thm:xo_order` = `lem:lb_pf_order`).
-/
@[expose] public section


open Complex Filter Topology MeasureTheory Set


/-- Translating by `1` does not increase the modulus, on the half-plane `1/2 ≤ Re z`. -/
private lemma norm_sub_one_le_norm_of_half_le_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖z - 1‖ ≤ ‖z‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg z)
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith [hz]

/-- Strip bound for `Γ` on `[1/4, 2]` (`lem:xo_gamma_strip_bounded`). There is `C₀ > 0` with
`‖Γ(w)‖ ≤ C₀ (1 + ‖w‖^{3/2})` for every `w` with `1/4 ≤ Re w ≤ 2`. Stated for the whole strip,
slightly stronger than the blueprint's `|w| ≥ 1`. -/
theorem norm_Gamma_le_strip_quarter_two :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ w : ℂ, (1 : ℝ) / 4 ≤ w.re → w.re ≤ 2 →
      ‖Complex.Gamma w‖ ≤ C₀ * (1 + ‖w‖ ^ ((3 : ℝ) / 2)) := by
  obtain ⟨c₁, c₂, hc₁, hc₁₂, H⟩ :=
    norm_Gamma_vertical_le (a := 1 / 4) (b := 2) (by norm_num) (by norm_num)
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  -- compact rectangle bound for `|Im w| < 1`
  obtain ⟨M₀, hM₀⟩ :=
    ((isCompact_Icc (a := (1 / 4 : ℝ)) (b := 2)).reProdIm
        (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn
      fun w hw ↦ (differentiableAt_Gamma_of_re_pos (by
        rw [mem_reProdIm] at hw; linarith [hw.1.1])).continuousAt.continuousWithinAt
  refine ⟨max c₂ M₀, lt_of_lt_of_le hc₂ (le_max_left _ _), fun w hw1 hw2 ↦ ?_⟩
  have hnormnn : (0 : ℝ) ≤ ‖w‖ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (norm_nonneg _) _
  have hC₀ : (0 : ℝ) ≤ max c₂ M₀ := hc₂.le.trans (le_max_left _ _)
  by_cases himw : 1 ≤ |w.im|
  · -- vertical bound case
    have hexp : Real.exp (-(Real.pi / 2) * |w.im|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg w.im)])
    have hrpow : |w.im| ^ (w.re - 1 / 2) ≤ ‖w‖ ^ ((3 : ℝ) / 2) :=
      (Real.rpow_le_rpow_of_exponent_le himw (by linarith)).trans
        (Real.rpow_le_rpow (abs_nonneg _) (Complex.abs_im_le_norm w) (by norm_num))
    have hub := (H w.re hw1 hw2 w.im himw).2
    rw [Complex.re_add_im] at hub
    calc ‖Complex.Gamma w‖
        ≤ c₂ * |w.im| ^ (w.re - 1 / 2) * Real.exp (-(Real.pi / 2) * |w.im|) := hub
      _ ≤ c₂ * ‖w‖ ^ ((3 : ℝ) / 2) * 1 := by gcongr
      _ ≤ max c₂ M₀ * (1 + ‖w‖ ^ ((3 : ℝ) / 2)) := by
            nlinarith [mul_le_mul_of_nonneg_right (le_max_left c₂ M₀) hnormnn]
  · -- compact rectangle case
    have hwK := hM₀ w (by
      rw [mem_reProdIm]
      exact ⟨⟨hw1, hw2⟩, (abs_lt.mp (not_le.mp himw)).1.le, (abs_lt.mp (not_le.mp himw)).2.le⟩)
    nlinarith [le_max_right c₂ M₀]

/-- Half-plane upper bound for `Γ` (`lem:xo_gamma_halfplane`). There is `Cγ > 0` with
`‖Γ(z)‖ ≤ exp(Cγ (‖z‖ log‖z‖ + 1))` for every `z` with `1/4 ≤ Re z` and `‖z‖ ≥ 1`. -/
theorem norm_Gamma_le_exp_halfplane :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∀ z : ℂ, (1 : ℝ) / 4 ≤ z.re → 1 ≤ ‖z‖ →
      ‖Complex.Gamma z‖ ≤ Real.exp (Cγ * (‖z‖ * Real.log ‖z‖ + 1)) := by
  obtain ⟨C₀, hC₀, hstrip⟩ := norm_Gamma_le_strip_quarter_two
  -- descent on the number `n` of recurrence steps needed to reach the strip
  have aux : ∀ n : ℕ, ∀ z : ℂ, (1 : ℝ) / 4 ≤ z.re → z.re ≤ 2 + n → 1 ≤ ‖z‖ →
      ‖Complex.Gamma z‖ ≤ C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * ‖z‖ ^ n := by
    intro n
    induction n with
    | zero => exact fun z hz1 hz2 _ ↦ by simpa using hstrip z hz1 (by simpa using hz2)
    | succ n ih =>
        intro z hz1 hz2 hz3
        by_cases hcase : z.re ≤ 2 + n
        · exact (ih z hz1 hcase hz3).trans (by gcongr; exact Nat.le_succ n)
        · have hrebig : (2 : ℝ) < z.re :=
            lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg n)) (not_le.mp hcase)
          have hwre : (z - 1).re = z.re - 1 := by simp
          have hwne : z - 1 ≠ 0 := fun hh ↦ by rw [hh, Complex.zero_re] at hwre; linarith
          have hstep : Complex.Gamma z = (z - 1) * Complex.Gamma (z - 1) := by
            rw [← Complex.Gamma_add_one (z - 1) hwne]; congr 1; ring
          have hw_norm1 : (1 : ℝ) ≤ ‖z - 1‖ :=
            le_trans (by rw [hwre]; linarith)
              ((le_abs_self _).trans (abs_re_le_norm (z - 1)))
          have hih := ih (z - 1) (by rw [hwre]; linarith)
            (by rw [hwre]; push_cast at hz2 ⊢; linarith) hw_norm1
          have hnorm_le : ‖z - 1‖ ≤ ‖z‖ := norm_sub_one_le_norm_of_half_le_re (by linarith)
          rw [hstep, norm_mul, pow_succ]
          calc ‖z - 1‖ * ‖Complex.Gamma (z - 1)‖
              ≤ ‖z‖ * (C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * ‖z‖ ^ n) :=
                mul_le_mul hnorm_le (hih.trans (by gcongr)) (norm_nonneg _) (norm_nonneg _)
            _ = C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * (‖z‖ ^ n * ‖z‖) := by ring
  -- assembly: take `n = ⌊Re z⌋₊` recurrence steps, then exponentiate
  refine ⟨max (5 / 2) (Real.log (2 * C₀)),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun z hz1 hz3 ↦ ?_⟩
  set N := ‖z‖ with hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hz3
  have hL0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hz3
  have hNL : (0 : ℝ) ≤ N * Real.log N := mul_nonneg hN0.le hL0
  set n := ⌊z.re⌋₊ with hn
  have hn_le : (n : ℝ) ≤ N :=
    (Nat.floor_le (by linarith)).trans ((le_abs_self _).trans (abs_re_le_norm z))
  have hbase := aux n z hz1 (by linarith [Nat.lt_floor_add_one z.re]) hz3
  rw [← hN] at hbase
  have h1le : (1 : ℝ) ≤ N ^ ((3 : ℝ) / 2) := Real.one_le_rpow hz3 (by norm_num)
  have hpow : N ^ n ≤ Real.exp (N * Real.log N) := by
    rw [← Real.rpow_natCast N n, Real.rpow_def_of_pos hN0]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hn_le hL0])
  have hkey : C₀ * (1 + N ^ ((3 : ℝ) / 2)) * N ^ n
      ≤ Real.exp (Real.log (2 * C₀) + Real.log N * (3 / 2)) * Real.exp (N * Real.log N) := by
    rw [Real.exp_add, Real.exp_log (by positivity), ← Real.rpow_def_of_pos hN0]
    exact mul_le_mul (by nlinarith [mul_nonneg hC₀.le (sub_nonneg.mpr h1le)]) hpow
      (by positivity) (by positivity)
  refine (hbase.trans hkey).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hCγ1 : (5 : ℝ) / 2 ≤ max (5 / 2) (Real.log (2 * C₀)) := le_max_left _ _
  nlinarith [le_max_right (5 / 2 : ℝ) (Real.log (2 * C₀)), hNL,
    mul_nonneg (by linarith : (0 : ℝ) ≤ N - 1) hL0, mul_nonneg (sub_nonneg.mpr hCγ1) hNL]

/-- Remainder bound for the `N = 2` Euler–Maclaurin truncation of `ζ` (`lem:xo_zeta_em2`).
For `Re s ≥ 1/2`, the integral remainder of `riemannZeta0 2` satisfies
`‖s ∫₂^∞ (⌊x⌋ + 1/2 - x) x^{-(s+1)} dx‖ ≤ √2 ‖s‖`. -/
theorem norm_riemannZeta_sub_head_le {s : ℂ} (hs : (1 : ℝ) / 2 ≤ s.re) :
    ‖s * ∫ x in Set.Ioi (2 : ℝ), (↑⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ Real.sqrt 2 * ‖s‖ := by
  have hσpos : 0 < s.re := by linarith
  have key := ZetaBnd_aux1b 2 (by norm_num) (σ := s.re) (t := s.im) hσpos
  simp only [Nat.cast_ofNat, Complex.re_add_im] at key
  -- `2^{-σ}/σ ≤ 2^{-1/2}·2 = √2`
  have hb2 : (2 : ℝ) ^ (-s.re) / s.re ≤ Real.sqrt 2 := by
    calc (2 : ℝ) ^ (-s.re) / s.re = (2 : ℝ) ^ (-s.re) * (1 / s.re) := by ring
      _ ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) * 2 :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
            (by rw [div_le_iff₀ hσpos]; linarith) (by positivity)
            (Real.rpow_pos_of_pos (by norm_num) _).le
      _ = Real.sqrt 2 := by
          rw [mul_comm]; nth_rewrite 1 [← Real.rpow_one (2 : ℝ)]
          rw [← Real.rpow_add (by norm_num), Real.sqrt_eq_rpow]; congr 1; norm_num
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (key.trans hb2) (norm_nonneg s)

/-- Polynomial bound for `ζ` (`lem:xo_zeta_poly`). There is `Cζ > 0` with `‖ζ(s)‖ ≤ Cζ ‖s‖`
for every `s` with `Re s ≥ 1/2` and `‖s‖ ≥ 2`. -/
theorem norm_riemannZeta_le_const_mul_of_half_le_re :
    ∃ Cζ : ℝ, 0 < Cζ ∧ ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → 2 ≤ ‖s‖ → ‖riemannZeta s‖ ≤ Cζ * ‖s‖ := by
  refine ⟨5 + Real.sqrt 2, by positivity, fun s hs hsnorm ↦ ?_⟩
  have hσpos : 0 < s.re := by linarith
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs1 : s ≠ 1 := by rintro rfl; rw [norm_one] at hsnorm; norm_num at hsnorm
  by_cases hcase : 2 ≤ s.re
  · -- `Re s ≥ 2`: `‖ζ(s)‖ ≤ π²/6`
    have hb := norm_riemannZeta_sub_one_le_of_two_le_re hcase
    have h2 := norm_sub_norm_le (riemannZeta s) 1
    rw [norm_one] at h2
    nlinarith [Real.sqrt_nonneg 2, Real.pi_le_four, Real.pi_pos,
      mul_nonneg (Real.sqrt_nonneg 2) (by linarith : (0 : ℝ) ≤ ‖s‖)]
  · -- `1/2 ≤ Re s < 2`: the `N = 2` truncation, term by term
    have hs0 : s ≠ 0 := by rintro rfl; simp at hσpos
    have hexp : riemannZeta s
        = (∑ n ∈ Finset.range 3, 1 / ((n : ℂ)) ^ s)
          + (-(((2 : ℕ) : ℂ) ^ (1 - s))) / (1 - s)
          + (-(((2 : ℕ) : ℂ) ^ (-s))) / 2
          + s * ∫ x in Set.Ioi (2 : ℝ), (↑⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) :=
      (Zeta0EqZeta (N := 2) (by norm_num) hσpos hs1).symm
    have hA : ‖∑ n ∈ Finset.range 3, 1 / ((n : ℂ)) ^ s‖ ≤ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Nat.cast_zero, Nat.cast_one, Complex.zero_cpow hs0, Complex.one_cpow,
        div_zero, div_one, zero_add]
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_div, norm_one, norm_natCast_cpow_of_pos (by norm_num : 0 < 2)]
      have hden : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ s.re := by positivity
      linarith [(div_le_one hden).mpr (Real.one_le_rpow (by norm_num) (by linarith))]
    have hB : ‖(-(((2 : ℕ) : ℂ) ^ (1 - s))) / (1 - s)‖ ≤ Real.sqrt 2 := by
      rw [norm_div, norm_neg, norm_natCast_cpow_of_pos (by norm_num : 0 < 2), Complex.sub_re,
        Complex.one_re]
      have h1s : (1 : ℝ) ≤ ‖1 - s‖ := by
        rw [show (1 : ℂ) - s = -(s - 1) by ring, norm_neg]
        have hh := norm_sub_norm_le s 1
        rw [norm_one] at hh; linarith
      refine (div_le_self (Real.rpow_nonneg (by norm_num) _) h1s).trans ?_
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hC : ‖(-(((2 : ℕ) : ℂ) ^ (-s))) / 2‖ ≤ 1 / 2 := by
      rw [norm_div, norm_neg, norm_natCast_cpow_of_pos (by norm_num : 0 < 2), Complex.neg_re,
        show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      simpa using Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -s.re ≤ 0)
    rw [hexp]
    refine norm_add₄_le.trans ((add_le_add (add_le_add (add_le_add hA hB) hC)
      (norm_riemannZeta_sub_head_le hs)).trans ?_)
    linarith

/-- Order-one growth of `ξ` (`thm:xo_order` = `lem:lb_pf_order`). There is `C > 0` with
`‖ξ(s)‖ ≤ exp(C ‖s‖ log‖s‖)` for all `‖s‖ ≥ 2`; i.e. `ξ` has order `≤ 1`. -/
theorem norm_riemannXi_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ ‖s‖ →
      ‖riemannXi s‖ ≤ Real.exp (C * (‖s‖ * Real.log ‖s‖)) := by
  obtain ⟨Cγ, hCγ, hγ⟩ := norm_Gamma_le_exp_halfplane
  obtain ⟨Cζ, hCζ, hζ⟩ := norm_riemannZeta_le_const_mul_of_half_le_re
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₀ : ℝ := Cγ / 2 + 3 + (|Real.log Cζ| + Cγ) / (2 * Real.log 2) with hC₀def
  have hfrac : 0 ≤ (|Real.log Cζ| + Cγ) / (2 * Real.log 2) :=
    div_nonneg (add_nonneg (abs_nonneg _) hCγ.le) (by positivity)
  have hC0 : 0 < C₀ := by rw [hC₀def]; linarith [hfrac, hCγ]
  -- main bound on the right half-plane `Re s ≥ 1/2`
  have main : ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → 2 ≤ ‖s‖ →
      ‖riemannXi s‖ ≤ Real.exp (C₀ * (‖s‖ * Real.log ‖s‖)) := by
    intro s hs hsnorm
    have hσpos : 0 < s.re := by linarith
    have hN0 : 0 < ‖s‖ := by linarith
    have hL0 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
    have hs0 : s ≠ 0 := by rintro rfl; simp at hN0
    have hs1 : s ≠ 1 := by rintro rfl; rw [norm_one] at hsnorm; norm_num at hsnorm
    have hhalf : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    set P := ‖s‖ * Real.log ‖s‖ with hP
    have hP0 : 0 ≤ P := mul_nonneg hN0.le hL0
    have hPlow : 2 * Real.log 2 ≤ P := by
      rw [hP]
      nlinarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hsnorm, hl2, hL0,
        mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖ - 2) hL0]
    have hlogP : Real.log ‖s‖ ≤ P := by
      rw [hP]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖ - 1) hL0]
    -- the three factor bounds; the `Γ(s/2)` exponent is at most `P/2`
    have hpre : ‖(1 / 2 : ℂ) * (s * (s - 1))‖ ≤ ‖s‖ ^ 2 := by
      rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      nlinarith [mul_le_mul_of_nonneg_left (by simpa using norm_sub_le s 1) (norm_nonneg s),
        mul_nonneg (norm_nonneg s) (by linarith : (0 : ℝ) ≤ ‖s‖ - 1)]
    have hΓnorm : ‖Gammaℝ s‖ ≤ Real.exp (Cγ * (1 / 2 * P + 1)) := by
      rw [Gammaℝ_def, norm_mul]
      have hπ : ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
        refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
        rw [Complex.div_ofNat_re, Complex.neg_re]; linarith
      have hG : ‖s / 2‖ * Real.log ‖s / 2‖ ≤ 1 / 2 * P := by
        rw [hhalf, hP]
        have hlogle : Real.log (‖s‖ / 2) ≤ Real.log ‖s‖ :=
          Real.log_le_log (by linarith) (by linarith)
        nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ ‖s‖ / 2 by linarith),
          mul_le_mul_of_nonneg_left hlogle (by linarith : (0 : ℝ) ≤ ‖s‖ / 2)]
      refine (mul_le_mul hπ (hγ (s / 2) (by rw [Complex.div_ofNat_re]; linarith)
        (by rw [hhalf]; linarith)) (norm_nonneg _) (by norm_num)).trans ?_
      exact (one_mul _).trans_le
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hCγ.le))
    have hcombine : ‖riemannXi s‖ ≤ ‖s‖ ^ 2 * Real.exp (Cγ * (1 / 2 * P + 1)) * (Cζ * ‖s‖) := by
      rw [riemannXi_eq_prefactor_mul hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hσpos), norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hpre hΓnorm (norm_nonneg _) (by positivity))
        (hζ s hs hsnorm) (norm_nonneg _) (by positivity)
    -- rewrite the polynomial-times-exp bound as a single exponential, then compare exponents
    have hrw : ‖s‖ ^ 2 * Real.exp (Cγ * (1 / 2 * P + 1)) * (Cζ * ‖s‖)
        = Real.exp (Real.log Cζ + 3 * Real.log ‖s‖ + Cγ * (1 / 2 * P + 1)) := by
      have hcube : ‖s‖ ^ 3 = Real.exp (3 * Real.log ‖s‖) := by
        rw [← Real.rpow_natCast ‖s‖ 3, Real.rpow_def_of_pos hN0]; congr 1; push_cast; ring
      rw [Real.exp_add, Real.exp_add, Real.exp_log hCζ, ← hcube]; ring
    refine (hcombine.trans_eq hrw).trans (Real.exp_le_exp.mpr ?_)
    have hconst : Real.log Cζ + Cγ ≤ ((|Real.log Cζ| + Cγ) / (2 * Real.log 2)) * P :=
      calc Real.log Cζ + Cγ ≤ |Real.log Cζ| + Cγ := by linarith [le_abs_self (Real.log Cζ)]
        _ = ((|Real.log Cζ| + Cγ) / (2 * Real.log 2)) * (2 * Real.log 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hPlow hfrac
    rw [hC₀def]
    linarith [hconst, hlogP]
  -- assembly: reduce `Re s < 1/2` to `Re s ≥ 1/2` via `ξ(1-s) = ξ(s)`
  refine ⟨4 * C₀, by linarith [hC0], fun s hsnorm ↦ ?_⟩
  by_cases hcase : (1 : ℝ) / 2 ≤ s.re
  · refine (main s hcase hsnorm).trans (Real.exp_le_exp.mpr ?_)
    linarith [mul_nonneg hC0.le (mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖)
      (Real.log_nonneg (by linarith : (1 : ℝ) ≤ ‖s‖)))]
  · rw [not_le] at hcase
    have hre' : (1 : ℝ) / 2 ≤ (1 - s).re := by simp; linarith
    have hnorm_ge : ‖s‖ ≤ ‖1 - s‖ := by simpa using norm_sub_one_le_norm_of_half_le_re hre'
    have hnorm_le : ‖1 - s‖ ≤ 2 * ‖s‖ := by
      have := norm_sub_le (1 : ℂ) s; rw [norm_one] at this; linarith
    have hloga0 : 0 ≤ Real.log ‖1 - s‖ := Real.log_nonneg (by linarith)
    rw [← riemannXi_one_sub s]
    refine (main (1 - s) hre' (hsnorm.trans hnorm_ge)).trans (Real.exp_le_exp.mpr ?_)
    have hloga : Real.log ‖1 - s‖ ≤ 2 * Real.log ‖s‖ := by
      have h1 : Real.log ‖1 - s‖ ≤ Real.log (2 * ‖s‖) := Real.log_le_log (by linarith) hnorm_le
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hsnorm]
    have hala : ‖1 - s‖ * Real.log ‖1 - s‖ ≤ 4 * (‖s‖ * Real.log ‖s‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hnorm_le hloga0,
        mul_le_mul_of_nonneg_left hloga (by linarith [norm_nonneg s] : (0 : ℝ) ≤ 2 * ‖s‖)]
    linarith [mul_le_mul_of_nonneg_left hala hC0.le]
