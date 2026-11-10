/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Hadamard.XiOrder
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Log
public import Mathlib.Analysis.SpecialFunctions.Integrability.PosLog
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Summability of the zeros of the Riemann `ξ`-function

For every `ε > 0` the family `z ↦ (D z) ‖z‖^{-(1+ε)}` is summable, where
`D := MeromorphicOn.divisor riemannXi ⊤` packages the zeros of `ξ` with their multiplicities;
in particular `∑_ρ |ρ|^{-2} < ∞`, the hypothesis consumed by the canonical product
(`zero_summability.tex`).

## Main results

* `logCounting_riemannXi_le` (`lem:zs_jensen`).
* `riemannXiZeroCount` (`def:zs_count`).
* `riemannXiZeroCount_le` (`lem:zs_count_bound`).
* `summable_riemannXiDivisor_norm_rpow` (`lem:zs_summable_divisor`).
* `summable_one_div_riemannZeta_zero_rpow` (`thm:zs_main` = `lem:lb_pf_summable`).
* `summable_inv_norm_sq_riemannXiZeros` (`lem:zs_product`).
-/
@[expose] public section


open Complex Filter Topology MeasureTheory Set Function MeromorphicOn Metric
open scoped ENNReal NNReal


/-- `ξ` is meromorphic on all of `ℂ`. -/
private theorem meromorphic_riemannXi : Meromorphic riemannXi :=
  fun z ↦ (analyticOnNhd_riemannXi z (mem_univ z)).meromorphicAt

/-- Jensen bound on the integrated counting function (`lem:zs_jensen`). There is a constant
`C_N > 0` such that for all `R ≥ 2`, `N(R) = logCounting D R ≤ C_N R log R`. -/
theorem logCounting_riemannXi_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) R
        ≤ C * (R * Real.log R) := by
  obtain ⟨Cξ, hCξ, hξ⟩ := norm_riemannXi_le_exp
  refine ⟨Cξ + 1 / 2, by linarith, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  simp only [Set.top_eq_univ]
  rw [Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
      meromorphic_riemannXi hRpos.ne',
    (analyticOnNhd_riemannXi 0 (mem_univ 0)).meromorphicTrailingCoeffAt_of_ne_zero
      (by rw [riemannXi_zero]; norm_num),
    riemannXi_zero,
    show Real.log ‖(1 : ℂ) / 2‖ = -Real.log 2 from by
      rw [Complex.norm_div, norm_one, Complex.norm_ofNat, one_div, Real.log_inv]]
  have hca : Real.circleAverage (fun x ↦ Real.log ‖riemannXi x‖) 0 R ≤ Cξ * (R * Real.log R) := by
    refine Real.circleAverage_mono_on_of_le_circle
      (MeromorphicOn.circleIntegrable_log_norm (fun z _ ↦ meromorphic_riemannXi z)) fun x hx ↦ ?_
    rw [mem_sphere_iff_norm, sub_zero, abs_of_pos hRpos] at hx
    by_cases hzero : riemannXi x = 0
    · rw [hzero, norm_zero, Real.log_zero]
      exact mul_nonneg hCξ.le (mul_nonneg hRpos.le (Real.log_nonneg (by linarith)))
    · rw [Real.log_le_iff_le_exp (norm_pos_iff.mpr hzero), ← hx]
      exact hξ x (by rw [hx]; exact hR)
  -- `log 2 ≤ ½ R log R` since `log 2 ≤ log R` and `(R - 2) log R ≥ 0`
  have hl2R : Real.log 2 ≤ 1 / 2 * (R * Real.log R) := by
    linarith [Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hR,
      mul_nonneg (show (0 : ℝ) ≤ R - 2 by linarith)
        (Real.log_nonneg (show (1 : ℝ) ≤ R by linarith))]
  linarith

/-- The divisor of `ξ` is non-negative. -/
theorem divisor_riemannXi_nonneg : 0 ≤ MeromorphicOn.divisor riemannXi (⊤ : Set ℂ) :=
  analyticOnNhd_riemannXi.divisor_nonneg

/-- The multiplicity of `ξ` at `z`, cast to `ℝ`, is non-negative. -/
theorem divisor_riemannXi_cast_nonneg (z : ℂ) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) := by
  exact_mod_cast divisor_riemannXi_nonneg z

/-- `Int.toNat` loses nothing on the (non-negative) divisor of `ξ`. -/
theorem divisor_riemannXi_toNat_cast (z : ℂ) :
    (((MeromorphicOn.divisor riemannXi ⊤ z).toNat : ℕ) : ℝ)
      = ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg (divisor_riemannXi_nonneg z)

/-- The divisor of `ξ` vanishes at `0`. -/
theorem divisor_riemannXi_apply_zero : MeromorphicOn.divisor riemannXi (⊤ : Set ℂ) 0 = 0 := by
  have hanalytic : AnalyticAt ℂ riemannXi 0 := analyticOnNhd_riemannXi 0 (mem_univ 0)
  change MeromorphicOn.divisor riemannXi univ 0 = 0
  rw [MeromorphicOn.divisor_apply (fun z _ ↦ meromorphic_riemannXi z) (mem_univ 0),
    hanalytic.meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (Or.inr (by rw [riemannXi_zero]; norm_num))]
  rfl

/-- Zero-counting function (`def:zs_count`): the number of zeros of `ξ` in `|z| ≤ R`, counted
with multiplicity, as the finsum of the restricted divisor. -/
noncomputable def riemannXiZeroCount (R : ℝ) : ℝ :=
  ∑ᶠ z, ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z : ℤ) : ℝ)

/-- On the ball, the restricted divisor agrees value-wise with the global divisor of `ξ`. -/
theorem divisor_riemannXi_closedBall_eq (R : ℝ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    MeromorphicOn.divisor riemannXi (closedBall 0 R) z = MeromorphicOn.divisor riemannXi ⊤ z := by
  rw [MeromorphicOn.divisor_apply (fun w _ ↦ meromorphic_riemannXi w) hz]
  change _ = MeromorphicOn.divisor riemannXi univ z
  rw [MeromorphicOn.divisor_apply (fun w _ ↦ meromorphic_riemannXi w) (mem_univ z)]

/-- The `ℝ≥0∞`-valued sum of the multiplicities over the
closed ball equals `ENNReal.ofReal (n(R))`. -/
theorem tsum_toNat_divisor_closedBall (R : ℝ) :
    ∑' z : closedBall (0 : ℂ) R, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞)
      = ENNReal.ofReal (riemannXiZeroCount R) := by
  have hsupp : (Function.support
      fun w : ℂ ↦ ((MeromorphicOn.divisor riemannXi (closedBall 0 R) w : ℤ) : ℝ)).Finite :=
    ((MeromorphicOn.divisor riemannXi (closedBall 0 R)).finiteSupport
      (isCompact_closedBall 0 R)).subset fun z hz ↦ by simpa [Function.mem_support] using hz
  have hnn : ∀ w : ℂ, (0 : ℝ) ≤ ((MeromorphicOn.divisor riemannXi (closedBall 0 R) w : ℤ) : ℝ) :=
    fun w ↦ by exact_mod_cast (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg w
  rw [riemannXiZeroCount, ← tsum_eq_finsum (L := SummationFilter.unconditional ℂ) hsupp,
    ENNReal.ofReal_tsum_of_nonneg hnn (summable_of_hasFiniteSupport hsupp),
    tsum_subtype (closedBall (0 : ℂ) R)
      (fun w ↦ ((MeromorphicOn.divisor riemannXi ⊤ w).toNat : ℝ≥0∞))]
  refine tsum_congr fun w ↦ ?_
  by_cases hw : w ∈ closedBall (0 : ℂ) R
  · rw [Set.indicator_of_mem hw, divisor_riemannXi_closedBall_eq R hw,
      ← divisor_riemannXi_toNat_cast w, ENNReal.ofReal_natCast]
  · rw [Set.indicator_of_notMem hw,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw]
    simp

/-- Pointwise counting bound (`lem:zs_count_bound`). There is a constant `C_n > 0` with
`n(R) ≤ C_n R log R` for all `R ≥ 2`. -/
theorem riemannXiZeroCount_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → riemannXiZeroCount R ≤ C * (R * Real.log R) := by
  obtain ⟨CN, hCN, hN⟩ := logCounting_riemannXi_le
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * CN / Real.log 2, by positivity, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have h2Rabs : |2 * R| = 2 * R := abs_of_pos (by linarith)
  -- every term of the `logCounting` finsum at radius `2R` is non-negative (at `z = 0` the
  -- `log (2R‖z‖⁻¹)` factor itself vanishes, off `closedBall 0 (2R)` the divisor factor does)
  have hRHSnn : ∀ z : ℂ, 0 ≤ ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
      (MeromorphicOn.divisor riemannXi ⊤)) z : ℝ) * Real.log (2 * R * ‖z‖⁻¹) := fun z ↦ by
    by_cases hz2R : z ∈ closedBall (0 : ℂ) (2 * R)
    · rcases eq_or_ne z 0 with rfl | hz0
      · simp
      · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        have hznorm : ‖z‖ ≤ 2 * R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz2R
        rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ (by rwa [h2Rabs])]
        exact mul_nonneg (divisor_riemannXi_cast_nonneg z)
          (Real.log_nonneg (by rw [le_mul_inv_iff₀ hzpos]; linarith))
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (by rw [h2Rabs]; exact hz2R)]
      simp
  -- Step 1: `log 2 * n(R) ≤ logCounting D (2R)`.
  have hkey : Real.log 2 * riemannXiZeroCount R ≤
      Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) (2 * R) := by
    -- expand `logCounting` to its defining finsum; this reaches through the bundled-hom
    -- construction (`AddMonoidHom.coe_mk`/`ZeroHom.coe_mk`) as mathlib exposes no API lemma for it
    rw [show Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) (2 * R)
          = ∑ᶠ z, ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
              (MeromorphicOn.divisor riemannXi ⊤)) z : ℝ) * Real.log (2 * R * ‖z‖⁻¹)
            + ((MeromorphicOn.divisor riemannXi ⊤) 0 : ℝ) * Real.log (2 * R) from by
        simp only [Function.locallyFinsuppWithin.logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]]
    rw [divisor_riemannXi_apply_zero, Int.cast_zero, zero_mul, add_zero, riemannXiZeroCount,
      mul_finsum]
    refine finsum_le_finsum ?_ ?_ ?_
    · refine ((MeromorphicOn.divisor riemannXi (closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset (fun z hz ↦ ?_)
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Int.cast_eq_zero] at hz
      simpa [Function.mem_support] using hz.2
    · refine ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
        (MeromorphicOn.divisor riemannXi ⊤)).finiteSupport
          (isCompact_closedBall 0 |2 * R|)).subset (fun z hz ↦ ?_)
      simpa [Function.mem_support, Int.cast_eq_zero]
        using Function.support_mul_subset_left _ _ hz
    · intro z
      dsimp only
      by_cases hzR : z ∈ closedBall (0 : ℂ) R
      · -- on the ball: restricted divisor = `D z`, and `log(2R/‖z‖) ≥ log 2`
        rw [divisor_riemannXi_closedBall_eq R hzR]
        rcases eq_or_ne z 0 with rfl | hz0
        · rw [divisor_riemannXi_apply_zero]; simp
        · have hznorm : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzR
          have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
          rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ (by
            rw [h2Rabs]; simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]; linarith)]
          have hloglow : Real.log 2 ≤ Real.log (2 * R * ‖z‖⁻¹) :=
            Real.log_le_log (by norm_num) (by rw [le_mul_inv_iff₀ hzpos]; linarith)
          linarith [mul_le_mul_of_nonneg_left hloglow (divisor_riemannXi_cast_nonneg z)]
      · -- off the ball: restricted divisor is `0`, and the `2R`-term is non-negative
        rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzR, Int.cast_zero, mul_zero]
        exact hRHSnn z
  -- Step 2: combine with the Jensen bound at radius `2R`.
  have hlog2R : Real.log (2 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hRpos)]
    linarith [Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hR]
  have hstep : CN * (2 * R * Real.log (2 * R)) ≤ 4 * CN * (R * Real.log R) := by
    rw [show 4 * CN * (R * Real.log R) = CN * (2 * R * (2 * Real.log R)) by ring]
    gcongr
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  linarith [hkey.trans ((hN (2 * R) (by linarith)).trans hstep)]

/-- Every real `> 1` sits in a dyadic shell `[2^k, 2^{k+1})` for some `k : ℕ`. -/
private theorem exists_dyadic_shell {x : ℝ} (hx : 1 < x) :
    ∃ k : ℕ, (2 : ℝ) ^ k ≤ x ∧ x < 2 ^ (k + 1) := by
  obtain ⟨n, hn1, hn2⟩ :=
    exists_mem_Ico_zpow (by linarith : (0 : ℝ) < x) (by norm_num : (1 : ℝ) < 2)
  have hn0 : 0 ≤ n := by
    by_contra h
    rw [not_le] at h
    have h1 : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (0 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by lia)
    rw [zpow_zero] at h1; linarith
  exact ⟨n.toNat, by rw [← zpow_natCast, Int.toNat_of_nonneg hn0]; exact hn1,
    by rw [← zpow_natCast (2 : ℝ) (n.toNat + 1), Nat.cast_add, Nat.cast_one,
        Int.toNat_of_nonneg hn0]; exact hn2⟩

/-- Divisor-weighted summability (`lem:zs_summable_divisor`). For every real `p > 1` the family
`z ↦ (D z) ‖z‖^{-p}` is summable. -/
theorem summable_riemannXiDivisor_norm_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun z : ℂ ↦ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) * ‖z‖ ^ (-p)) := by
  obtain ⟨Cn, hCn, hn⟩ := riemannXiZeroCount_le
  set g : ℂ → ℝ := fun z ↦ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) * ‖z‖ ^ (-p) with hg
  have hgnn : ∀ z, 0 ≤ g z := fun z ↦ mul_nonneg (divisor_riemannXi_cast_nonneg z) (by positivity)
  -- reduce to finiteness of the `ℝ≥0∞`-valued sum
  rw [show g = fun z ↦ ((Real.toNNReal (g z) : ℝ≥0) : ℝ) from
      funext fun z ↦ (Real.coe_toNNReal _ (hgnn z)).symm,
    ← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  change (∑' z : ℂ, ENNReal.ofReal (g z)) ≠ ∞
  set s : ℝ := (2 : ℝ) ^ (-p) with hs
  set r : ℝ := 2 * s with hr
  have hreq : r = (2 : ℝ) ^ (1 - p) := by
    rw [hr, hs, sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  have hr0 : 0 < r := by rw [hreq]; positivity
  have hr1 : r < 1 := by
    rw [hreq]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  -- dyadic shells and the inner disc
  set A : ℕ → Set ℂ := fun k ↦ {z | (2 : ℝ) ^ k ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (k + 1)}
  have hcover : (univ : Set ℂ) ⊆ closedBall (0 : ℂ) 1 ∪ ⋃ k : ℕ, A k := fun z _ ↦ by
    by_cases h1 : ‖z‖ ≤ 1
    · exact Or.inl (by simpa [Metric.mem_closedBall, dist_eq_norm] using h1)
    · exact Or.inr (mem_iUnion.mpr (exists_dyadic_shell (not_le.mp h1)))
  -- per-shell summand bound `B`, summable since `r < 1`
  set B : ℕ → ℝ := fun k ↦ 2 * Cn * Real.log 2 * (((k : ℝ) + 1) * r ^ k) with hB
  have hBnn : ∀ k, 0 ≤ B k := fun k ↦ by rw [hB]; positivity
  have hBsum : Summable B := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0.le])
    rw [hB]
    exact (((h1.add (summable_geometric_of_lt_one hr0.le hr1)).congr
      fun k ↦ by rw [pow_one]; ring).mul_left _)
  -- each shell sum is dominated by `ofReal (B k)`: `‖z‖^{-p} ≤ s^k` there, and the shell holds at
  -- most `n(2^{k+1}) ≤ Cn 2^{k+1} (k+1) log 2` zeros
  have hshell : ∀ k : ℕ, ∑' z : A k, ENNReal.ofReal (g z) ≤ ENNReal.ofReal (B k) := fun k ↦ by
    have h2k1 : (2 : ℝ) ≤ 2 ^ (k + 1) := by
      simpa using pow_le_pow_right₀ one_le_two (Nat.le_add_left 1 k)
    have hskeq : ((2 : ℝ) ^ k) ^ (-p) = s ^ k := by
      rw [hs, ← Real.rpow_natCast ((2 : ℝ) ^ (-p)) k, ← Real.rpow_natCast (2 : ℝ) k,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    have hlognn : 0 ≤ Cn * (2 ^ (k + 1) * Real.log (2 ^ (k + 1))) :=
      mul_nonneg hCn.le (mul_nonneg (by positivity)
        (Real.log_nonneg (one_le_pow₀ (by norm_num))))
    calc ∑' z : A k, ENNReal.ofReal (g z)
        ≤ ∑' z : A k, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞)
            * ENNReal.ofReal (s ^ k) := by
          refine ENNReal.tsum_le_tsum fun z ↦ ?_
          rw [← ENNReal.ofReal_natCast, divisor_riemannXi_toNat_cast,
            ← ENNReal.ofReal_mul (divisor_riemannXi_cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          simp only [hg]
          exact mul_le_mul_of_nonneg_left
            (hskeq ▸ Real.rpow_le_rpow_of_nonpos (by positivity) z.2.1 (by linarith))
            (divisor_riemannXi_cast_nonneg _)
      _ = (∑' z : A k, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞))
            * ENNReal.ofReal (s ^ k) := ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal (riemannXiZeroCount (2 ^ (k + 1))) * ENNReal.ofReal (s ^ k) := by
          rw [← tsum_toNat_divisor_closedBall]
          gcongr
          exact ENNReal.tsum_mono_subtype
            (fun w ↦ ((MeromorphicOn.divisor riemannXi ⊤ w).toNat : ℝ≥0∞))
            fun z hz ↦ by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2.le
      _ ≤ ENNReal.ofReal (Cn * (2 ^ (k + 1) * Real.log (2 ^ (k + 1))))
            * ENNReal.ofReal (s ^ k) := by gcongr; exact hn _ h2k1
      _ = ENNReal.ofReal (B k) := by
          rw [← ENNReal.ofReal_mul hlognn]
          simp only [hB]
          congr 1
          rw [Real.log_pow, pow_succ, hr, mul_pow]
          push_cast; ring
  -- the inner disc carries only finitely many zeros
  have hinner : (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z)) ≠ ∞ := by
    refine (summable_of_hasFiniteSupport (Set.Finite.subset
      (((MeromorphicOn.divisor riemannXi (closedBall 0 1)).finiteSupport
        (isCompact_closedBall 0 1)).preimage Subtype.coe_injective.injOn)
      fun z hz ↦ ?_)).tsum_ofReal_ne_top
    rw [Set.mem_preimage, Function.mem_support, divisor_riemannXi_closedBall_eq 1 z.2]
    exact fun h0 ↦ hz (by simp only [hg]; rw [h0]; simp)
  have hBtop : (∑' k : ℕ, ENNReal.ofReal (B k)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hBnn hBsum]; exact ENNReal.ofReal_ne_top
  -- assemble: `ℂ = closedBall 0 1 ∪ ⋃ₖ Aₖ`
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hinner, hBtop⟩) ?_
  calc ∑' z : ℂ, ENNReal.ofReal (g z)
      = ∑' z : (univ : Set ℂ), ENNReal.ofReal (g z) := (tsum_univ _).symm
    _ ≤ ∑' z : (closedBall (0 : ℂ) 1 ∪ (⋃ k : ℕ, A k) : Set ℂ), ENNReal.ofReal (g z) :=
        ENNReal.tsum_mono_subtype (fun w ↦ ENNReal.ofReal (g w)) hcover
    _ ≤ (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z))
          + ∑' z : (⋃ k : ℕ, A k : Set ℂ), ENNReal.ofReal (g z) :=
        ENNReal.tsum_union_le (fun w ↦ ENNReal.ofReal (g w)) _ _
    _ ≤ (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z)) + ∑' k : ℕ, ENNReal.ofReal (B k) := by
        gcongr
        exact (ENNReal.tsum_iUnion_le_tsum (fun w ↦ ENNReal.ofReal (g w)) A).trans
          (ENNReal.tsum_le_tsum hshell)

/-- Summability of the zeros of `ξ` (`thm:zs_main` = `lem:lb_pf_summable`). For every `ε > 0`
the family `z ↦ (D z) ‖z‖^{-(1+ε)}` is summable; in particular `∑_ρ |ρ|^{-2} < ∞`. -/
theorem summable_one_div_riemannZeta_zero_rpow {ε : ℝ} (hε : 0 < ε) :
    Summable (fun z : ℂ ↦ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) * ‖z‖ ^ (-(1 + ε))) :=
  summable_riemannXiDivisor_norm_rpow (by linarith)

/-- The summability hypothesis of the canonical product (`lem:zs_product`). For the multiplicity
enumeration `ι := (z : supp D) × Fin (D z).toNat`, `ρ(z,j) := z`, the family `i ↦ ‖ρ(i)⁻¹‖²`
is summable. -/
theorem summable_inv_norm_sq_riemannXiZeros :
    Summable (fun i : (z : (MeromorphicOn.divisor riemannXi ⊤).support) ×
        Fin (MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat ↦ ‖((i.1 : ℂ))⁻¹‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun _ ↦ by positivity)]
  refine ⟨fun x ↦ (hasSum_fintype _).summable, ?_⟩
  refine ((summable_riemannXiDivisor_norm_rpow (show (1 : ℝ) < 2 by norm_num)).subtype
    (MeromorphicOn.divisor riemannXi ⊤).support).congr fun z ↦ ?_
  rw [tsum_fintype]
  simp only [Function.comp_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, divisor_riemannXi_toNat_cast]
  rw [norm_inv, inv_pow, ← Real.rpow_natCast ‖z.1‖ 2, ← Real.rpow_neg (norm_nonneg _)]
  norm_num

