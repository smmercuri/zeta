/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.ArgZeta.Basic
public import Zeta.ArgZeta.ShiftIdentity

/-!
# Lehman's explicit bound §4: the explicit tail witness

Explicit numerals for the tail constant `C_t` of `lem:ll_tail`
(`logNormZetaIntegral_tail_ge`), at the working abscissae `a = 103/100` and `a = 124/100`.

## Main results

* `logNormZetaIntegral_tail_ge_explicit`: `C_t ≤ 49` at `a = 103/100`.
* `logNormZetaIntegral_tail_ge_sharp` (`lem:le_tail_sharp`): `C_t ≤ 23/5` at `a = 103/100`.
* `logNormZetaIntegral_tail_ge_tight` (`lem:ls_Ct`): `C_t ≤ 5/2` at `a = 124/100`.
-/
@[expose] public section


open Complex Filter Topology Function Set

open scoped Real

section Tail
open MeasureTheory

/-- **Tail majorant** (`lem:le_tail_majorant`). The tight majorant
`N(σ) = 2^{-σ} + 2^{1-σ}/(σ-1)` for `ζ(σ) - 1 = ∑_n (n+2)^{-σ}`, `σ > 1`. -/
theorem tsum_one_div_nat_add_two_rpow_le_majorant {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ 2 ^ (-σ) + 2 ^ (1 - σ) / (σ - 1) := by
  have hneg : (-σ : ℝ) < -1 := by linarith
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 2) ^ σ) :=
    Real.summable_one_div_nat_add_two_rpow hσ
  rw [hsum.tsum_eq_zero_add]
  have h0 : 1 / (((0 : ℕ) : ℝ) + 2) ^ σ = (2 : ℝ) ^ (-σ) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div]
    norm_num
  -- the shifted tail is bounded by `∫_2^∞ x^{-σ} dx = 2^{1-σ}/(σ-1)`
  have htail : ∑' n : ℕ, 1 / (((n : ℕ) + 1 : ℝ) + 2) ^ σ ≤ 2 ^ (1 - σ) / (σ - 1) := by
    have h := Real.tsum_one_div_nat_add_rpow_le 2 (by norm_num) hσ
    norm_num at h
    refine le_trans (le_of_eq (tsum_congr fun n ↦ ?_)) h
    rw [show ((n : ℕ) + 1 : ℝ) + 2 = (n : ℝ) + 3 by ring, one_div]
  refine add_le_add (le_of_eq ?_) (le_trans (le_of_eq (tsum_congr fun n ↦ ?_)) htail)
  · exact h0
  · push_cast; ring_nf

/-- **Convexity chord for `2^{-u}`** (`lem:le_two_pow_chord`). -/
theorem Real.rpow_two_neg_le_one_sub_half {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (2 : ℝ) ^ (-u) ≤ 1 - u / 2 := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-Real.log 2))
    (by linarith : (0 : ℝ) ≤ 1 - u) hu0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    show Real.log 2 * -u = u * -Real.log 2 by ring]
  linarith [h]

/-- `2^{1-σ} = 2 · 2^{-σ}`. -/
private lemma two_rpow_one_sub (σ : ℝ) : (2 : ℝ) ^ (1 - σ) = 2 * 2 ^ (-σ) := by
  rw [show (1 - σ : ℝ) = 1 + -σ by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_one]

/-- The geometric piece `σ ↦ 2^{-σ}` is integrable on every right ray. -/
private lemma integrableOn_two_rpow_neg_Ioi (c : ℝ) :
    IntegrableOn (fun σ : ℝ ↦ (2 : ℝ) ^ (-σ)) (Set.Ioi c) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp : IntegrableOn (fun σ : ℝ ↦ Real.exp (-(Real.log 2 * σ))) (Set.Ioi c) :=
    Real.integrableOn_exp_neg_mul_Ioi hl2 c
  refine hexp.congr_fun (fun σ _ ↦ ?_) measurableSet_Ioi
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring_nf

/-- The geometric integral `∫_c^∞ 2^{-σ} dσ = 2^{-c}/log 2`. -/
private lemma integral_two_rpow_neg_Ioi (c : ℝ) :
    ∫ σ in Set.Ioi c, (2 : ℝ) ^ (-σ) = 2 ^ (-c) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcong : ∫ σ in Set.Ioi c, (2 : ℝ) ^ (-σ)
      = ∫ σ in Set.Ioi c, Real.exp (-Real.log 2 * σ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun σ _ ↦ ?_
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  rw [hcong, integral_exp_mul_Ioi (by linarith) c,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [div_eq_div_iff (ne_of_lt (by linarith : -Real.log 2 < 0)) (ne_of_gt hl2)]
  rw [show -Real.log 2 * c = Real.log 2 * -c by ring]
  ring

/-- The tail piece `σ ↦ 2^{1-σ}/(σ-1)` is integrable on `(c, ∞)` for `c > 1`. -/
private lemma integrableOn_tail_majorant_snd {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) / (σ - 1)) (Set.Ioi c) := by
  have hcont : ContinuousOn (fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) / (σ - 1)) (Set.Ioi c) := by
    have h2 : Continuous fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) :=
      (Real.continuous_const_rpow (by norm_num)).comp (continuous_const.sub continuous_id)
    exact h2.continuousOn.div ((continuous_id.sub continuous_const).continuousOn)
      (fun σ hσ ↦ ne_of_gt (by simp only [Set.mem_Ioi] at hσ; linarith))
  refine Integrable.mono' ((integrableOn_two_rpow_neg_Ioi c).const_mul (2 / (c - 1)))
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  simp only [Set.mem_Ioi] at hσ
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.rpow_nonneg (by norm_num) _) hσ1.le), two_rpow_one_sub,
    show 2 / (c - 1) * (2 : ℝ) ^ (-σ) = 2 * (2 : ℝ) ^ (-σ) / (c - 1) by ring]
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- The tight tail majorant is integrable on `(c, ∞)` for `c > 1`. -/
private lemma integrableOn_tail_majorant {c : ℝ} (hc : 1 < c) :
    IntegrableOn (fun σ : ℝ ↦ (2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1)) (Set.Ioi c) :=
  (integrableOn_two_rpow_neg_Ioi _).add (integrableOn_tail_majorant_snd hc)

/-- **Tail-integral core.** The integral of the tail majorant over `(a, ∞)`, for `1 < a ≤ 2`, in
a form whose only transcendental ingredient is `log((a-1)⁻¹)`. -/
private lemma integral_tail_majorant_le_core {a : ℝ} (ha : 1 < a) (ha2 : a ≤ 2) :
    ∫ σ in Set.Ioi a, ((2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1))
      ≤ 0.7214 + (Real.log (a - 1)⁻¹ + a / 2 - 1) + 0.7214 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [integral_add (integrableOn_two_rpow_neg_Ioi _) (integrableOn_tail_majorant_snd ha)]
  -- the geometric piece: `2^{-a}/log 2 ≤ 0.7214`
  have hp1 : ∫ σ in Set.Ioi a, (2 : ℝ) ^ (-σ) ≤ 0.7214 := by
    rw [integral_two_rpow_neg_Ioi, div_le_iff₀ hl2]
    have h2c : (2 : ℝ) ^ (-a) ≤ 1 / 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : (-a : ℝ) ≤ -1)
      rwa [Real.rpow_neg_one, ← one_div] at h
    linarith [Real.log_two_gt_d9]
  -- split the second piece at `σ = 2`
  have hsplit : ∫ σ in Set.Ioi a, (2 : ℝ) ^ (1 - σ) / (σ - 1)
      = (∫ σ in Set.Ioc a 2, (2 : ℝ) ^ (1 - σ) / (σ - 1))
        + ∫ σ in Set.Ioi (2 : ℝ), (2 : ℝ) ^ (1 - σ) / (σ - 1) := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_tail_majorant_snd ha).mono_set Set.Ioc_subset_Ioi_self)
      (integrableOn_tail_majorant_snd (by norm_num : (1 : ℝ) < 2)),
      Set.Ioc_union_Ioi_eq_Ioi ha2]
  -- the middle piece: chord bound, then FTC with antiderivative `log(σ-1) - σ/2`
  have hmid : ∫ σ in Set.Ioc a 2, (2 : ℝ) ^ (1 - σ) / (σ - 1)
      ≤ Real.log (a - 1)⁻¹ + a / 2 - 1 := by
    rw [← intervalIntegral.integral_of_le ha2]
    have hII : IntervalIntegrable (fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) / (σ - 1)) volume a 2 := by
      apply ContinuousOn.intervalIntegrable
      have h2 : Continuous fun σ : ℝ ↦ (2 : ℝ) ^ (1 - σ) :=
        (Real.continuous_const_rpow (by norm_num)).comp (continuous_const.sub continuous_id)
      refine h2.continuousOn.div ((continuous_id.sub continuous_const).continuousOn)
        fun σ hσ ↦ ne_of_gt ?_
      rw [Set.uIcc_of_le ha2, Set.mem_Icc] at hσ
      linarith [hσ.1]
    have hII' : IntervalIntegrable (fun σ : ℝ ↦ 1 / (σ - 1) - 1 / 2) volume a 2 := by
      apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.sub (ContinuousOn.div continuousOn_const
        ((continuous_id.sub continuous_const).continuousOn) fun σ hσ ↦ ne_of_gt ?_)
        continuousOn_const
      rw [Set.uIcc_of_le ha2, Set.mem_Icc] at hσ
      linarith [hσ.1]
    have hle : ∫ σ in a..2, (2 : ℝ) ^ (1 - σ) / (σ - 1) ≤ ∫ σ in a..2, (1 / (σ - 1) - 1 / 2) := by
      refine intervalIntegral.integral_mono_on ha2 hII hII' fun σ hσ ↦ ?_
      rw [Set.mem_Icc] at hσ
      have hσ1 : (0 : ℝ) < σ - 1 := by linarith [hσ.1]
      have hchord : (2 : ℝ) ^ (1 - σ) ≤ 1 - (σ - 1) / 2 := by
        have h := Real.rpow_two_neg_le_one_sub_half (u := σ - 1) (by linarith [hσ.1])
          (by linarith [hσ.2])
        rwa [show (-(σ - 1) : ℝ) = 1 - σ by ring] at h
      calc (2 : ℝ) ^ (1 - σ) / (σ - 1) ≤ (1 - (σ - 1) / 2) / (σ - 1) := by gcongr
        _ = 1 / (σ - 1) - 1 / 2 := by field_simp
    have hFTC : ∫ σ in a..2, (1 / (σ - 1) - 1 / 2) = Real.log (a - 1)⁻¹ + a / 2 - 1 := by
      have hderiv : ∀ σ ∈ Set.uIcc a 2,
          HasDerivAt (fun x : ℝ ↦ Real.log (x - 1) - x / 2) (1 / (σ - 1) - 1 / 2) σ := by
        intro σ hσ
        rw [Set.uIcc_of_le ha2, Set.mem_Icc] at hσ
        have hne : σ - 1 ≠ 0 := ne_of_gt (by linarith [hσ.1])
        have h1 : HasDerivAt (fun x : ℝ ↦ Real.log (x - 1)) (1 / (σ - 1)) σ := by
          simpa using ((hasDerivAt_id σ).sub_const 1).log hne
        exact h1.sub ((hasDerivAt_id σ).div_const 2)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hII',
        show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one, Real.log_inv]
      ring
    exact hle.trans_eq hFTC
  -- the far piece: `1/(σ-1) ≤ 1` and the geometric integral again
  have hp3 : ∫ σ in Set.Ioi (2 : ℝ), (2 : ℝ) ^ (1 - σ) / (σ - 1) ≤ 0.7214 := by
    have hmono : ∫ σ in Set.Ioi (2 : ℝ), (2 : ℝ) ^ (1 - σ) / (σ - 1)
        ≤ ∫ σ in Set.Ioi (2 : ℝ), 2 * (2 : ℝ) ^ (-σ) := by
      refine setIntegral_mono_on (integrableOn_tail_majorant_snd (by norm_num : (1 : ℝ) < 2))
        ((integrableOn_two_rpow_neg_Ioi 2).const_mul 2)
        measurableSet_Ioi fun σ hσ ↦ ?_
      simp only [Set.mem_Ioi] at hσ
      rw [two_rpow_one_sub]
      exact div_le_self (by positivity) (by linarith)
    rw [integral_const_mul, integral_two_rpow_neg_Ioi] at hmono
    have h22 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
      rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    rw [h22] at hmono
    refine hmono.trans ?_
    rw [show (2 : ℝ) * (1 / 4 / Real.log 2) = 1 / 2 / Real.log 2 by ring, div_le_iff₀ hl2]
    linarith [Real.log_two_gt_d9]
  rw [hsplit]
  linarith [hp1, hmid, hp3]

/-- `log(25/24 · 2^k) ≤ 1/24 + k·log 2`. -/
private lemma log_25_24_mul_two_pow_le (k : ℕ) :
    Real.log (25 / 24 * 2 ^ k) ≤ 1 / 24 + k * Real.log 2 := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 25 / 24 by norm_num)]

/-- **Explicit tail integral** (`lem:le_tail_int_bound`). The tail majorant integrates to
`≤ 23/5` over `(103/100, ∞)`. -/
theorem integral_tail_majorant_le :
    ∫ σ in Set.Ioi (103 / 100 : ℝ), ((2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1)) ≤ 23 / 5 := by
  have h := integral_tail_majorant_le_core (a := 103 / 100) (by norm_num) (by norm_num)
  rw [show ((103 / 100 : ℝ) - 1)⁻¹ = 100 / 3 by norm_num] at h
  have hlog : Real.log (100 / 3) ≤ 1 / 24 + 5 * Real.log 2 := by
    have h5 := log_25_24_mul_two_pow_le 5
    rw [show (25 / 24 * 2 ^ (5 : ℕ) : ℝ) = 100 / 3 by norm_num] at h5
    push_cast at h5; linarith
  linarith [h, hlog, Real.log_two_lt_d9]

/-- **Explicit tail witness** (`lem:le_tail_explicit`). The tail constant `C_t ≤ 49` at
`a = 103/100` (that is, `d = 53/100`). Superseded by `logNormZetaIntegral_tail_ge_sharp`. -/
theorem logNormZetaIntegral_tail_ge_explicit (t : ℝ) :
    (-49 ≤ ∫ σ in Set.Ioi (103 / 100 : ℝ),
        Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-49 ≤ ∫ σ in Set.Ioo (103 / 100 : ℝ) (156 / 100),
        Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨h1, h2⟩ :=
    logNormZetaIntegral_tail_ge_const (a := 103 / 100) (by norm_num) (156 / 100) t
  -- `C_t = (∑_n 1/(n+2)^{103/100})/log 2 ≤ 49`
  have hbound : (∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ (103 / 100 : ℝ)) / Real.log 2 ≤ 49 := by
    have hsum := Real.tsum_one_div_nat_add_two_rpow_le_inv_sub_one
      (show (1 : ℝ) < 103 / 100 by norm_num)
    rw [show (1 : ℝ) / (103 / 100 - 1) = 100 / 3 by norm_num] at hsum
    rw [div_le_iff₀ hl2]
    linarith [hsum, Real.log_two_gt_d9]
  exact ⟨by linarith, by linarith⟩

/-- **Tail-witness core.** Any bound `∫_a^∞ N ≤ B` on the tight majorant
`N σ = 2^{-σ} + 2^{1-σ}/(σ-1)` (`1 < a`) is a tail witness `C_t ≤ B`. -/
private lemma neg_le_logNormZetaIntegral_of_integral_majorant_le {a B : ℝ} (ha1 : 1 < a)
    (hIN : ∫ σ in Set.Ioi a, ((2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1)) ≤ B) (b t : ℝ) :
    (-B ≤ ∫ σ in Set.Ioi a, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-B ≤ ∫ σ in Set.Ioo a b, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) :=
  neg_le_logNormZetaIntegral_of_tsum_le ha1 (integrableOn_tail_majorant ha1)
    (fun _ hσ ↦ tsum_one_div_nat_add_two_rpow_le_majorant (lt_trans ha1 hσ)) hIN

/-- **Sharp tail witness** (`lem:le_tail_sharp`). The tail constant `C_t ≤ 23/5` at
`a = 103/100`. -/
theorem logNormZetaIntegral_tail_ge_sharp (t : ℝ) :
    (-(23 / 5) ≤ ∫ σ in Set.Ioi (103 / 100 : ℝ),
        Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-(23 / 5) ≤ ∫ σ in Set.Ioo (103 / 100 : ℝ) (156 / 100),
        Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) :=
  neg_le_logNormZetaIntegral_of_integral_majorant_le (a := 103 / 100) (by norm_num)
    integral_tail_majorant_le (156 / 100) t

/-- **Explicit tail integral at the deeper abscissa `a = 124/100`** (`= ½ + d`, `d = 74/100`).
The tail majorant integrates to `≤ 5/2` there. -/
theorem integral_tail_majorant_le_124 :
    ∫ σ in Set.Ioi (124 / 100 : ℝ), ((2 : ℝ) ^ (-σ) + 2 ^ (1 - σ) / (σ - 1)) ≤ 5 / 2 := by
  have h := integral_tail_majorant_le_core (a := 124 / 100) (by norm_num) (by norm_num)
  rw [show ((124 / 100 : ℝ) - 1)⁻¹ = 25 / 6 by norm_num] at h
  have hlog : Real.log (25 / 6) ≤ 1 / 24 + 2 * Real.log 2 := by
    have h2 := log_25_24_mul_two_pow_le 2
    rw [show (25 / 24 * 2 ^ (2 : ℕ) : ℝ) = 25 / 6 by norm_num] at h2
    push_cast at h2; linarith
  linarith [h, hlog, Real.log_two_lt_d9]

/-- **Tight tail witness at depth `d = 74/100`** (`lem:ls_Ct`). The tail constant `C_t ≤ 5/2` at
`a = ½ + d = 124/100`. -/
theorem logNormZetaIntegral_tail_ge_tight (t : ℝ) :
    (-(5 / 2) ≤ ∫ σ in Set.Ioi (124 / 100 : ℝ),
        Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-(5 / 2) ≤ ∫ σ in Set.Ioo (124 / 100 : ℝ) (198 / 100),
        Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) :=
  neg_le_logNormZetaIntegral_of_integral_majorant_le (a := 124 / 100) (by norm_num)
    integral_tail_majorant_le_124 (198 / 100) t

end Tail

