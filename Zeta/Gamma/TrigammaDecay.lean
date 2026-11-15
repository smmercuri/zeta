/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gamma.Trigamma
public import Zeta.Gamma.DigammaStirling
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Basic.Complex.BigOperators

/-!
# Decay of the trigamma function along the shift

Decay of `ψ' = deriv Complex.digamma` along the integer shift, and the consequences for `Im ψ'`
and for `Re ψ` on the vertical line `¼ + iT/2` (`gram_averaging.tex`).

## Main results

* `Complex.norm_digamma_le`: `‖ψ(z)‖ ≤ log‖z‖ + (π + 3)` for `Re z > 0`, `‖z‖ ≥ 1`.
* `Complex.tendsto_deriv_digamma_add_nat`: `ψ'(s + n) → 0` as `n → ∞`, for `Re s > 0`.
* `Complex.im_deriv_digamma_nonpos`: `Im ψ'(s) ≤ 0` in the upper right quadrant.
* `Complex.monotoneOn_re_digamma_quarter_vertical`: `T ↦ Re ψ(¼ + iT/2)` is monotone on `[0, ∞)`.
-/
@[expose] public section


open Complex Filter
open scoped Topology Nat Real

namespace Complex
open Complex.Stirling

/-- **Logarithmic bound on the digamma function.** For `Re z > 0` and `‖z‖ ≥ 1`,
`‖ψ(z)‖ ≤ log‖z‖ + (π + 3)`. -/
theorem norm_digamma_le {z : ℂ} (hz : 0 < z.re) (h1 : 1 ≤ ‖z‖) :
    ‖Complex.digamma z‖ ≤ Real.log ‖z‖ + (Real.pi + 3) := by
  have hlogpos : 0 ≤ Real.log ‖z‖ := Real.log_nonneg h1
  -- principal term
  have hLog : ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im, abs_of_nonneg hlogpos]
    linarith [Complex.abs_arg_le_pi z]
  -- `(2z)⁻¹`
  have hinv : ‖(2 * z)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, Complex.norm_ofNat]
    exact inv_le_one_of_one_le₀ (by nlinarith [h1])
  -- the (single-term) Bernoulli sum
  have hsum : ‖∑ k ∈ Finset.Icc 1 1, (bernoulli (2 * k) : ℂ) / (2 * k) * z ^ (-(2 * k : ℤ))‖
      ≤ 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton, norm_mul]
    have hb : ‖(bernoulli (2 * 1) : ℂ) / (2 * (1 : ℕ))‖ ≤ 1 := by
      norm_num [bernoulli_two, Complex.norm_div]
    have hz2 : ‖z ^ (-(2 * (1 : ℕ) : ℤ))‖ ≤ 1 := by
      rw [norm_zpow]; exact zpow_le_one_of_nonpos₀ h1 (by norm_num)
    exact (mul_le_of_le_one_left (norm_nonneg _) hb).trans hz2
  -- remainder `R^ψ_3`
  have hrem : ‖digammaRemainderIoi z (2 * 1 + 1)‖ ≤ 1 := by
    have hb := norm_digammaRemainderIoi_le' z hz (2 * 1 + 1) (by norm_num)
    have hzp : ‖z‖ ^ (-(2 * 1 + 1 : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ h1 (by norm_num)
    have hcoef : ((2 * 1 + 1)! : ℝ) / (2 * Real.pi) ^ ((2 * 1 + 1) - 1) ≤ 1 := by
      rw [show (2 * 1 + 1 : ℕ) = 3 from rfl, show (3 - 1 : ℕ) = 2 from rfl,
        show (3 ! : ℝ) = 6 from by norm_num, div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    exact hb.trans ((mul_le_of_le_one_left (zpow_nonneg (norm_nonneg _) _) hcoef).trans hzp)
  -- assemble via the triangle inequality (shapes inferred from the goal)
  rw [digamma_eq_log_sub z hz 1]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans ?_
  linarith [hLog, hinv, hsum, hrem]

/-- A point within distance `r` of `c` has real part at least `Re c − r`. -/
private lemma re_sub_dist_le_re {c z : ℂ} {r : ℝ} (h : dist z c ≤ r) : c.re - r ≤ z.re := by
  have hab := Complex.abs_re_le_norm (c - z)
  rw [Complex.sub_re, show ‖c - z‖ = dist z c by rw [Complex.dist_eq, norm_sub_rev]] at hab
  linarith [(le_abs_self (c.re - z.re)).trans hab]

/-- **Decay of the trigamma function along the shift.** For fixed `s` with `Re s > 0`,
`ψ'(s + n) → 0` as `n → ∞`. -/
theorem tendsto_deriv_digamma_add_nat {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ ↦ deriv Complex.digamma (s + n)) atTop (𝓝 0) := by
  set L : ℝ := Real.pi + 3 with hL
  set K : ℝ := Real.log (2 * (‖s‖ + 1)) + L with hK
  -- the majorant `e n = (2 log n + 2K)/n → 0`
  have he : Tendsto (fun n : ℕ ↦ (2 * Real.log ↑n + 2 * K) / ↑n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ 2 * Real.log ↑n / ↑n) atTop (𝓝 0) := by
      have h0 := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop).const_mul 2
      simp only [Function.comp_def, id_eq, mul_zero] at h0
      exact h0.congr fun n ↦ by rw [mul_div_assoc]
    have h2 : Tendsto (fun n : ℕ ↦ 2 * K / ↑n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (2 * K)
    simpa [add_div] using h1.add h2
  refine squeeze_zero_norm' ?_ he
  -- `n` large enough that `↑n ≥ 1` and `Re(s+n) ≥ 2` (so the disc radius `R ≥ 1`)
  filter_upwards [eventually_ge_atTop (max 1 ⌈2 - s.re⌉₊)] with n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hnpos : 0 < (n : ℝ) := by linarith
  set c : ℂ := s + ↑n with hc
  have hcre : c.re = s.re + ↑n := by rw [hc, Complex.add_re, Complex.natCast_re]
  have hcre2 : 2 ≤ c.re := by
    rw [hcre]
    have hle : (⌈2 - s.re⌉₊ : ℝ) ≤ ↑n := by exact_mod_cast le_trans (le_max_right _ _) hn
    linarith [Nat.le_ceil (2 - s.re), hle]
  set R : ℝ := c.re / 2 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have hR1 : 1 ≤ R := by rw [hR]; linarith
  -- Cauchy estimate (points at distance `≤ R` from `c` have `Re ≥ Re c − R = R`)
  have hbound : ‖deriv Complex.digamma c‖ ≤ (Real.log (2 * (‖s‖ + ↑n)) + L) / R := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos
    · apply DifferentiableOn.diffContOnCl
      intro z hz
      have hzc : dist z c ≤ R :=
        Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hz)
      exact (differentiableAt_digamma (by linarith [re_sub_dist_le_re hzc])).differentiableWithinAt
    · intro z hz
      have hzc : dist z c = R := Metric.mem_sphere.mp hz
      have hzre : R ≤ z.re := by linarith [re_sub_dist_le_re hzc.le]
      have hznorm1 : 1 ≤ ‖z‖ := le_trans hR1 (hzre.trans (Complex.re_le_norm z))
      have hznorm : ‖z‖ ≤ 2 * (‖s‖ + ↑n) := by
        have hcn : ‖c‖ ≤ ‖s‖ + ↑n := by
          rw [hc]
          simpa [Complex.norm_natCast] using norm_add_le s (↑n : ℂ)
        have hzc' : ‖z - c‖ = R := by rw [← Complex.dist_eq]; exact hzc
        have hz1 : ‖z‖ ≤ ‖c‖ + R := hzc' ▸ norm_le_norm_add_norm_sub' z c
        have hRle : R ≤ ‖s‖ + ↑n := by
          rw [hR, hcre]; linarith [Complex.re_le_norm s, norm_nonneg s]
        linarith
      calc ‖Complex.digamma z‖ ≤ Real.log ‖z‖ + L := norm_digamma_le (by linarith [hzre]) hznorm1
        _ ≤ Real.log (2 * (‖s‖ + ↑n)) + L := by gcongr
  -- chain the Cauchy bound to `e n`
  refine hbound.trans ?_
  have hnum : Real.log (2 * (‖s‖ + ↑n)) + L ≤ Real.log ↑n + K := by
    have hmul : (2 : ℝ) * (‖s‖ + ↑n) ≤ 2 * (‖s‖ + 1) * ↑n := by nlinarith [norm_nonneg s, hn1]
    have hlog : Real.log (2 * (‖s‖ + ↑n)) ≤ Real.log (2 * (‖s‖ + 1)) + Real.log ↑n := by
      rw [← Real.log_mul (by positivity) (by linarith)]
      exact Real.log_le_log (by positivity) hmul
    rw [hK]; linarith
  have hnum0 : 0 ≤ Real.log (2 * (‖s‖ + ↑n)) + L := by
    have : 0 ≤ Real.log (2 * (‖s‖ + ↑n)) := Real.log_nonneg (by nlinarith [norm_nonneg s, hn1])
    rw [hL]; linarith [Real.pi_pos]
  rw [hR]
  calc (Real.log (2 * (‖s‖ + ↑n)) + L) / (c.re / 2)
      ≤ (Real.log (2 * (‖s‖ + ↑n)) + L) / (↑n / 2) :=
        div_le_div_of_nonneg_left hnum0 (by positivity) (by rw [hcre]; linarith)
    _ = (Real.log (2 * (‖s‖ + ↑n)) + L) * 2 / ↑n := by rw [div_div_eq_mul_div]
    _ ≤ (2 * Real.log ↑n + 2 * K) / ↑n := by gcongr; linarith [hnum]

/-- **Non-positivity of `Im ψ'` in the upper half-plane.** For `Re s > 0` and `0 ≤ Im s`,
`Im ψ'(s) ≤ 0`, where `ψ' = deriv Complex.digamma`. -/
theorem im_deriv_digamma_nonpos {s : ℂ} (hs : 0 < s.re) (him : 0 ≤ s.im) :
    (deriv Complex.digamma s).im ≤ 0 := by
  have htel : ∀ n : ℕ, deriv Complex.digamma s
      = deriv Complex.digamma (s + ↑n) + ∑ k ∈ Finset.range n, ((s + ↑k) ^ 2)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      have hsm : 0 < (s + ↑m).re := by
        simp only [Complex.add_re, Complex.natCast_re]
        linarith [Nat.cast_nonneg (α := ℝ) m]
      rw [show (s : ℂ) + ↑(m + 1) = (s + ↑m) + 1 by push_cast; ring, deriv_digamma_add_one hsm,
        Finset.sum_range_succ, ih]
      ring
  have hle : ∀ n : ℕ, (deriv Complex.digamma s).im ≤ (deriv Complex.digamma (s + ↑n)).im := by
    intro n
    rw [htel n, Complex.add_im, Complex.im_sum]
    have hsum : (∑ k ∈ Finset.range n, (((s + (k : ℂ)) ^ 2)⁻¹).im) ≤ 0 :=
      Finset.sum_nonpos fun k _ ↦ im_inv_sq_nonpos
        (by simp only [Complex.add_re, Complex.natCast_re];
            linarith [Nat.cast_nonneg (α := ℝ) k, hs.le])
        (by simp only [Complex.add_im, Complex.natCast_im, add_zero]; exact him)
    linarith
  have hlim : Tendsto (fun n : ℕ ↦ (deriv Complex.digamma (s + ↑n)).im) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Complex.continuous_im.tendsto 0).comp (tendsto_deriv_digamma_add_nat hs)
  exact ge_of_tendsto' hlim hle

/-- **Monotonicity of `Re ψ` on the vertical line `¼ + iT/2`.** The map `T ↦ Re ψ(¼ + iT/2)` is
monotone increasing on `[0, ∞)`. -/
theorem monotoneOn_re_digamma_quarter_vertical :
    MonotoneOn (fun T : ℝ ↦ (Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).re)
      (Set.Ici 0) := by
  have hre : ∀ T : ℝ, 0 < (1 / 4 + Complex.I * ((T : ℂ) / 2)).re := fun T ↦ by
    rw [show (1 / 4 + Complex.I * ((T : ℂ) / 2)).re = 1 / 4 by simp]; norm_num
  have hderiv : ∀ T : ℝ,
      HasDerivAt (fun t : ℝ ↦ (Complex.digamma (1 / 4 + Complex.I * ((t : ℂ) / 2))).re)
        (-(1 / 2) * (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).im) T := by
    intro T
    have haff : HasDerivAt (fun z : ℂ ↦ (1 / 4 : ℂ) + Complex.I * (z / 2)) (Complex.I * (1 / 2))
        (T : ℂ) := (((hasDerivAt_id (T : ℂ)).div_const 2).const_mul Complex.I).const_add (1 / 4)
    have hcomp := ((differentiableAt_digamma (hre T)).hasDerivAt.comp (T : ℂ) haff).comp_ofReal
    have hg := Complex.reCLM.hasFDerivAt.comp_hasDerivAt T hcomp
    simp only [Complex.reCLM_apply, Function.comp_apply] at hg
    rw [show (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2)) * (Complex.I * (1 / 2))).re
        = -(1 / 2) * (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).im by
      simp [Complex.mul_re]; ring] at hg
    exact hg
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr fun T ↦ (hderiv T).continuousAt).continuousOn
  · exact fun T _ ↦ (hderiv T).differentiableAt.differentiableWithinAt
  · intro T hT
    rw [interior_Ici] at hT
    rw [(hderiv T).deriv]
    have him : (deriv Complex.digamma (1 / 4 + Complex.I * ((T : ℂ) / 2))).im ≤ 0 := by
      refine im_deriv_digamma_nonpos (hre T) ?_
      have hval : (1 / 4 + Complex.I * ((T : ℂ) / 2)).im = T / 2 := by simp
      rw [hval]; linarith [Set.mem_Ioi.mp hT]
    linarith

end Complex
