/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.ArgZeta.Basic
public import PrimeNumberTheoremAnd.ZetaBounds
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Upper bound on `I(t)`

The convexity-free upper bound `I(t) ≤ a₁ + b₁ log t` on the log-modulus line integral
`I(t) = ∫_{1/2}^∞ log|ζ(σ + it)| dσ`, together with the pointwise growth bounds for `ζ` that
drive it.

## Main results

* `Real.sum_range_rpow_neg_le` (`lem:lb_sum_rpow`): `∑_{n=0}^N n^{-σ} ≤ N^{1-σ}/(1-σ) + 1` for
  `0 < σ < 1`.
* `norm_riemannZeta_le_of_mem_strip` (`lem:lb_zeta_strip`),
  `exists_norm_riemannZeta_le_const_mul_log` (`lem:lb_zeta_near_one`): pointwise bounds on
  `|ζ(σ + it)|` in the strip and near `σ = 1`.
* `logNormZetaIntegral_le` (`lem:lb_I_upper`): the bound with `a₁` existential.
* `logNormZetaIntegral_le_nine`, `logNormZetaIntegral_le_five`: the explicit forms
  `I(t) ≤ 9 + (3/16) log t` and `I(t) ≤ 5 + (1/8) log t`, for `t ≥ 168π` off the zeros.
-/
@[expose] public section


open Complex Filter Topology MeasureTheory Set

/-- **Partial-sum bound for the Dirichlet series** (`lem:lb_sum_rpow`). For `0 < σ < 1` and
`N ≥ 1`, `∑_{n=0}^N n^{-σ} ≤ N^{1-σ}/(1-σ) + 1`. The `Finset.range (N+1)` phrasing (whose `n = 0`
term vanishes) interfaces directly with the `riemannZeta0` partial sum. -/
theorem Real.sum_range_rpow_neg_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (1 - σ) / (1 - σ) + 1 := by
  have h1mσ : 0 < 1 - σ := by linarith
  -- the sum/integral comparison via antitonicity of `x ↦ x^{-σ}` on `[1, N]`
  have hcmp := (Real.antitoneOn_rpow_neg_Icc (a := 1) (b := 1 + (↑(N - 1) : ℝ)) hσ0.le
    one_pos).sum_le_integral
  -- `1 + ↑(N-1) = ↑N`
  have hcast : (1 : ℝ) + (↑(N - 1) : ℝ) = (N : ℝ) := by
    rw [Nat.cast_sub hN]; push_cast; ring
  rw [hcast] at hcmp
  -- evaluate the integral
  have hint : ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ) = ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -σ)), Real.one_rpow,
      show -σ + 1 = 1 - σ by ring]
  rw [hint] at hcmp
  -- peel `n = 0` from the outer sum
  rw [Finset.sum_range_succ', Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hσ0.ne'), add_zero]
  -- the inner sum over `range N`: peel `n = 1`, reindex the rest to `range (N-1)`
  have inner : ∑ i ∈ Finset.range N, ((↑(i + 1) : ℝ)) ^ (-σ)
      = (∑ i ∈ Finset.range (N - 1), ((1 : ℝ) + ↑(i + 1)) ^ (-σ)) + 1 := by
    conv_lhs => rw [show N = (N - 1) + 1 by lia]
    rw [Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      congr 1; push_cast; ring
    · norm_num
  rw [inner]
  calc (∑ i ∈ Finset.range (N - 1), ((1 : ℝ) + ↑(i + 1)) ^ (-σ)) + 1
      ≤ ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) + 1 := by linarith [hcmp]
    _ ≤ (N : ℝ) ^ (1 - σ) / (1 - σ) + 1 := by gcongr; linarith

/-- The point `σ + it` avoids the pole `s = 1` of `ζ` whenever `t ≠ 0`. -/
private theorem add_mul_I_ne_one {σ t : ℝ} (ht : t ≠ 0) : (σ : ℂ) + (t : ℂ) * I ≠ 1 :=
  fun h ↦ ht (by simpa using congrArg Complex.im h)

/-- Positivity of `|t|` together with the floor comparisons `0 < ⌊|t|⌋₊` and `(⌊|t|⌋₊ : ℝ) ≤ |t|`,
for `3 < |t|`. -/
private theorem abs_floor_bundle {t : ℝ} (ht : 3 < |t|) :
    0 < |t| ∧ 0 < ⌊|t|⌋₊ ∧ (⌊|t|⌋₊ : ℝ) ≤ |t| :=
  have htpos : (0 : ℝ) < |t| := by linarith
  ⟨htpos, Nat.floor_pos.mpr (by linarith), Nat.floor_le htpos.le⟩

/-- **Term 1 of the Euler–Maclaurin bound for `ζ`**: the Dirichlet partial sum `∑_{n ≤ N} n^{-s}`
at `N = ⌊|t|⌋₊`, `s = σ + it`, has modulus `≤ |t|^{1-σ}/(1-σ) + |t|^{1-σ}`. -/
private theorem norm_sum_one_div_cpow_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), 1 / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ |t| ^ (1 - σ) / (1 - σ) + |t| ^ (1 - σ) := by
  have σpos : 0 < σ := by linarith [hσ.1]
  have h1mσ : 0 < 1 - σ := by linarith [hσ.2]
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  have hre : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
    rw [show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp]; exact σpos
  have hs_ne : (σ : ℂ) + (t : ℂ) * I ≠ 0 := fun h ↦ by rw [h] at hre; simp at hre
  have hsum_norm : ‖∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), 1 / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ ∑ n ∈ Finset.range (⌊|t|⌋₊ + 1), (n : ℝ) ^ (-σ) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ ↦ ?_))
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [Nat.cast_zero]
      rw [Complex.zero_cpow hs_ne, div_zero, norm_zero, Real.zero_rpow (neg_ne_zero.mpr σpos.ne')]
    · rw [norm_div, norm_one, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp, one_div, Real.rpow_neg (Nat.cast_nonneg n)]
  refine hsum_norm.trans ((Real.sum_range_rpow_neg_le σpos hσ.2 Npos).trans ?_)
  have hdiv : (⌊|t|⌋₊ : ℝ) ^ (1 - σ) / (1 - σ) ≤ |t| ^ (1 - σ) / (1 - σ) := by gcongr
  have h1L : (1 : ℝ) ≤ |t| ^ (1 - σ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ |t|) h1mσ.le
  linarith

/-- **Term 2 of the Euler–Maclaurin bound for `ζ`**: the boundary term `-N^{1-s}/(1-s)`
(`N = ⌊|t|⌋₊`, `s = σ + it`) has modulus `≤ 2|t|^{1-σ}`. -/
private theorem norm_neg_cpow_one_sub_div_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1)
    (ht : 3 < |t|) :
    ‖-(⌊|t|⌋₊ : ℂ) ^ (1 - ((σ : ℂ) + (t : ℂ) * I)) / (1 - ((σ : ℂ) + (t : ℂ) * I))‖
      ≤ |t| ^ (1 - σ) * 2 := by
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  rw [norm_div, norm_neg, norm_natCast_cpow_of_pos Npos,
    show ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I)).re = 1 - σ by simp]
  exact (UpperBnd_aux6 ht ⟨hσ.1, by linarith [hσ.2]⟩ (add_mul_I_ne_one (abs_pos.mp htpos))
    Npos N_le_t).1

/-- **Term 3 of the Euler–Maclaurin bound for `ζ`**: the boundary term `-N^{-s}/2`
(`N = ⌊|t|⌋₊`, `s = σ + it`) has modulus `≤ |t|^{1-σ}`. -/
private theorem norm_neg_cpow_neg_div_two_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1)
    (ht : 3 < |t|) :
    ‖-(⌊|t|⌋₊ : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) / 2‖ ≤ |t| ^ (1 - σ) := by
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  rw [norm_div, norm_neg, norm_natCast_cpow_of_pos Npos, RCLike.norm_ofNat,
    show (-((σ : ℂ) + (t : ℂ) * I)).re = -σ by simp]
  exact (UpperBnd_aux6 ht ⟨hσ.1, by linarith [hσ.2]⟩ (add_mul_I_ne_one (abs_pos.mp htpos))
    Npos N_le_t).2.1

/-- **Term 4 of the Euler–Maclaurin bound for `ζ`**: the tail integral
`s · ∫_N^∞ (⌊x⌋ + ½ - x) x^{-(s+1)} dx` (`N = ⌊|t|⌋₊`, `s = σ + it`) has modulus
`≤ 16|t|^{1-σ}`. -/
private theorem norm_riemannZeta0_tail_le {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖((σ : ℂ) + (t : ℂ) * I) * ∫ x in Ioi (⌊|t|⌋₊ : ℝ),
        (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) + 1)‖ ≤ 16 * |t| ^ (1 - σ) := by
  have σpos : 0 < σ := by linarith [hσ.1]
  have hσ2 : σ ≤ 2 := by linarith [hσ.2]
  obtain ⟨htpos, Npos, N_le_t⟩ := abs_floor_bundle ht
  have hpow : |t| * |t| ^ (-σ) = |t| ^ (1 - σ) := by
    rw [show (1 - σ : ℝ) = 1 + (-σ) by ring, Real.rpow_add htpos, Real.rpow_one]
  refine (ZetaBnd_aux1 ⌊|t|⌋₊ Npos ⟨σpos, hσ2⟩ (by linarith : (2 : ℝ) ≤ |t|)).trans ?_
  rw [mul_div_assoc]
  refine (mul_le_mul_of_nonneg_left
    (UpperBnd_aux6 ht ⟨hσ.1, hσ2⟩ (add_mul_I_ne_one (abs_pos.mp htpos)) Npos N_le_t).2.2
    (by positivity)).trans (le_of_eq ?_)
  rw [show |t| ^ (1 - σ) = |t| * |t| ^ (-σ) from hpow.symm]; ring

/-- **Convexity-free strip bound for `ζ`** (`lem:lb_zeta_strip`). For `1/2 < σ < 1` and `3 < |t|`,
`‖ζ(σ + it)‖ ≤ 11/(1-σ) · |t|^{1-σ}`. The constant `11` (rather than the blueprint's sharper `7`)
affects only the additive constant `a₁` of `lem:lb_I_upper`, never the coefficient `b₁`. -/
theorem norm_riemannZeta_le_of_mem_strip {σ t : ℝ} (hσ : σ ∈ Ioo (1 / 2 : ℝ) 1) (ht : 3 < |t|) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ 11 / (1 - σ) * |t| ^ (1 - σ) := by
  rw [mul_comm Complex.I (t : ℂ)]
  have h1mσ : 0 < 1 - σ := by linarith [hσ.2]
  have σpos : 0 < σ := by linarith [hσ.1]
  obtain ⟨htpos, Npos, -⟩ := abs_floor_bundle ht
  have hre : 0 < ((σ : ℂ) + (t : ℂ) * I).re := by
    rw [show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp]; exact σpos
  have hL : (0 : ℝ) < |t| ^ (1 - σ) := Real.rpow_pos_of_pos htpos _
  -- Assemble the four Euler–Maclaurin terms via the `riemannZeta0` representation.
  rw [← Zeta0EqZeta Npos hre (add_mul_I_ne_one (abs_pos.mp htpos))]
  refine le_trans (norm_add₄_le ..) ?_
  refine le_trans (add_le_add (add_le_add (add_le_add (norm_sum_one_div_cpow_le hσ ht)
    (norm_neg_cpow_one_sub_div_le hσ ht)) (norm_neg_cpow_neg_div_two_le hσ ht))
    (norm_riemannZeta0_tail_le hσ ht)) ?_
  have hscalar : 1 / (1 - σ) + 20 ≤ 11 / (1 - σ) := by
    rw [← sub_nonneg, show 11 / (1 - σ) - (1 / (1 - σ) + 20) = (20 * σ - 10) / (1 - σ) by
      field_simp; ring]
    exact div_nonneg (by linarith [hσ.1]) h1mσ.le
  calc |t| ^ (1 - σ) / (1 - σ) + |t| ^ (1 - σ) + |t| ^ (1 - σ) * 2 + |t| ^ (1 - σ)
        + 16 * |t| ^ (1 - σ)
      = (1 / (1 - σ) + 20) * |t| ^ (1 - σ) := by ring
    _ ≤ 11 / (1 - σ) * |t| ^ (1 - σ) := mul_le_mul_of_nonneg_right hscalar hL.le

/-- **Bound near `σ = 1`** (`lem:lb_zeta_near_one`). There is a constant `C > 0` with
`|ζ(σ + it)| ≤ C·log|t|` for all `σ ∈ [1,2]` and `|t| > 3`. -/
theorem exists_norm_riemannZeta_le_const_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, σ ∈ Icc (1 : ℝ) 2 → 3 < |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ C * Real.log |t| := by
  obtain ⟨A, hA, C, hC, hbound⟩ := ZetaUpperBnd
  refine ⟨C, hC, fun σ t hσ ht ↦ ?_⟩
  have hlogpos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hmem : σ ∈ Icc (1 - A / Real.log |t|) 2 := by
    refine ⟨?_, hσ.2⟩
    have hnn : 0 ≤ A / Real.log |t| := div_nonneg hA.1.le hlogpos.le
    linarith [hσ.1]
  have h := hbound σ t ht hmem
  rwa [mul_comm Complex.I (t : ℂ)]

/-- **Explicit form of the bound near `σ = 1`.** For `σ ∈ [1, 2]` and `|t| > 3`,
`|ζ(σ + it)| ≤ C₁·log|t|` with `C₁ = e^{1/2}·(5 + 8·2) = 21·e^{1/2}`. -/
theorem norm_riemannZeta_le_const_mul_log {σ t : ℝ} (hσ : σ ∈ Icc (1 : ℝ) 2) (ht : 3 < |t|) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ Real.exp (1 / 2) * (5 + 8 * 2) * Real.log |t| := by
  obtain ⟨σ_ge, σ_le⟩ := hσ
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have σ_ge' : 1 - (1 / 2) / Real.log |t| ≤ σ := by
    have : (0 : ℝ) ≤ (1 / 2) / Real.log |t| := by positivity
    linarith
  obtain ⟨Npos, _, _, _, σPos, neOne⟩ :=
    UpperBnd_aux (A := 1 / 2) ⟨by norm_num, by norm_num⟩ ht σ_ge'
  rw [mul_comm Complex.I (t : ℂ), ← Zeta0EqZeta Npos (by simp [σPos]) neOne]
  apply le_trans (by apply norm_add₄_le) ?_
  have h := ZetaUpperBnd' (A := 1 / 2) ⟨by norm_num, le_rfl⟩ ht ⟨σ_ge', σ_le⟩
  simpa using h

/-- `σ ↦ log(1 - σ)` is interval-integrable on `[1/2, 1]` (reflection of `log` about `σ = 1`). -/
private theorem intervalIntegrable_log_one_sub :
    IntervalIntegrable (fun σ : ℝ ↦ Real.log (1 - σ)) volume (1 / 2) 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := (1 / 2 : ℝ)) (b := 0)).comp_sub_left 1
  norm_num at h; exact h

/-- `σ ↦ log(σ - 1)` is interval-integrable on `[1, 2]` (shift of `log` by `1`). -/
private theorem intervalIntegrable_log_sub_one :
    IntervalIntegrable (fun σ : ℝ ↦ Real.log (σ - 1)) volume 1 2 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)).comp_sub_right 1
  norm_num at h; exact h

/-- The exact value of the strip-majorant integral over `[1/2, 1]`:
`∫_{1/2}^{1} (log 11 + (1-σ)L - log(1-σ)) dσ = ½log 11 + L/8 + (½log 2 + ½)`. The `L/8` term is
the sole source of the leading `⅛ log t` of `lem:lb_I_upper`. -/
private theorem integral_strip_majorant (L : ℝ) :
    ∫ σ in (1 / 2 : ℝ)..1, (Real.log 11 + (1 - σ) * L - Real.log (1 - σ))
      = 1 / 2 * Real.log 11 + L / 8 + (1 / 2 * Real.log 2 + 1 / 2) := by
  have ii_const : IntervalIntegrable (fun _ : ℝ ↦ Real.log 11) volume (1 / 2) 1 :=
    intervalIntegrable_const
  have ii_lin : IntervalIntegrable (fun σ : ℝ ↦ (1 - σ) * L) volume (1 / 2) 1 :=
    Continuous.intervalIntegrable (by fun_prop) (1 / 2) 1
  have ii_log := intervalIntegrable_log_one_sub
  have hlin : ∫ σ in (1 / 2 : ℝ)..1, (1 - σ) * L = L / 8 := by
    rw [intervalIntegral.integral_mul_const]
    have hone : ∫ σ in (1 / 2 : ℝ)..1, (1 - σ) = 1 / 8 := by
      rw [intervalIntegral.integral_comp_sub_left (fun x ↦ x) 1, integral_id]
      norm_num
    rw [hone]; ring
  have hlog : ∫ σ in (1 / 2 : ℝ)..1, Real.log (1 - σ) = -(1 / 2 * Real.log 2) - 1 / 2 := by
    rw [intervalIntegral.integral_comp_sub_left (fun x ↦ Real.log x) 1, integral_log]
    rw [show (1 : ℝ) - 1 = 0 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      Real.log_div one_ne_zero two_ne_zero, Real.log_one]
    simp
  rw [intervalIntegral.integral_sub (ii_const.add ii_lin) ii_log,
    intervalIntegral.integral_add ii_const ii_lin, intervalIntegral.integral_const, hlin, hlog]
  simp only [smul_eq_mul]
  ring

/-- **Elementary strip bound for `ζ` on `σ > 1`** (`lem:ls_upper_elem`). For real `σ > 1` and any
`t`, `‖ζ(σ + it)‖ ≤ σ/(σ - 1)`. This `t`-independent majorant is what lowers the `I(t)`
coefficient from `3/16` to `1/8` in `logNormZetaIntegral_le_five`. -/
theorem norm_riemannZeta_le_div_sub_one {σ t : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ σ / (σ - 1) := by
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  set s : ℂ := (σ : ℂ) + Complex.I * t with hs
  have hsre : s.re = σ := by simp [hs]
  have htail : ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
    have h := norm_riemannZeta_sub_one_le (s := s) (by rw [hsre]; exact hσ)
    rwa [hsre] at h
  have hsum := Real.tsum_one_div_nat_add_two_rpow_le_inv_sub_one hσ
  have hnorm := norm_le_insert (1 : ℂ) (riemannZeta s)
  rw [norm_one, norm_sub_rev] at hnorm
  refine (by linarith [htail, hsum] : ‖riemannZeta s‖ ≤ 1 + 1 / (σ - 1)).trans (le_of_eq ?_)
  rw [eq_div_iff hσ1.ne']; field_simp; ring

/-- The `[1, 2]` majorant integral of the elementary strip bound:
`∫_1^2 (log σ - log(σ - 1)) dσ = 2 log 2`. -/
private theorem integral_log_sub_log_sub_one :
    ∫ σ in (1 : ℝ)..2, (Real.log σ - Real.log (σ - 1)) = 2 * Real.log 2 := by
  have iiA : IntervalIntegrable (fun σ : ℝ ↦ Real.log σ) volume 1 2 :=
    intervalIntegral.intervalIntegrable_log'
  rw [intervalIntegral.integral_sub iiA intervalIntegrable_log_sub_one]
  have hA : ∫ σ in (1 : ℝ)..2, Real.log σ = 2 * Real.log 2 - 1 := by
    rw [integral_log, Real.log_one]; ring
  have hB : ∫ σ in (1 : ℝ)..2, Real.log (σ - 1) = -1 := by
    rw [intervalIntegral.integral_comp_sub_right (fun x ↦ Real.log x) 1]
    norm_num [integral_log, Real.log_one]
  rw [hA, hB]; ring

/-- Integrability of the `I(t)` integrand on any subset of the ray `(1/2, ∞)`, off the zeros of
`ζ`. -/
private theorem integrableOn_log_norm_riemannZeta_subset {t : ℝ} {S : Set ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (hS : S ⊆ Ioi (1 / 2 : ℝ)) :
    IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) S :=
  (integrableOn_log_norm_riemannZeta_Ioi ht hzero).mono_set hS

/-- **Four-way split of `I(t)`** over the ranges `(1/2, 1]`, `(1, 2]`, `(2, 4]`, `(4, ∞)`, for
`t ≠ 0` off the zeros of `ζ` on the ray `{σ + it : σ ≥ 1/2}`. -/
private theorem logNormZetaIntegral_eq_add {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t
      = (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        + ∫ σ in Ioi (4 : ℝ), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ := by
  have ig : ∀ {S : Set ℝ}, S ⊆ Ioi (1 / 2 : ℝ) →
      IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) S :=
    fun hS ↦ integrableOn_log_norm_riemannZeta_subset ht hzero hS
  have ig_a := ig (S := Ioc (1 / 2 : ℝ) 1) Ioc_subset_Ioi_self
  have ig_Ioi1 := ig (S := Ioi (1 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  have ig_Ioi2 := ig (S := Ioi (2 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  have ig_b := ig (S := Ioc (1 : ℝ) 2) (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_c := ig (S := Ioc (2 : ℝ) 4) (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_d := ig (S := Ioi (4 : ℝ)) (Ioi_subset_Ioi (by norm_num))
  rw [logNormZetaIntegral, ← Ioc_union_Ioi_eq_Ioi (show (1 / 2 : ℝ) ≤ 1 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_a ig_Ioi1,
    ← Ioc_union_Ioi_eq_Ioi (show (1 : ℝ) ≤ 2 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_b ig_Ioi2,
    ← Ioc_union_Ioi_eq_Ioi (show (2 : ℝ) ≤ 4 by norm_num),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ig_c ig_d]
  ring

/-- **Range `(1/2, 1]` bound.** For `3 < t` off the zeros of `ζ`,
`∫_{(1/2,1]} log‖ζ(σ + it)‖ dσ ≤ ½log11 + (log t)/8 + (½log2 + ½)`. This block is the source of
the leading `⅛ log t` of the upper bound on `I(t)`. -/
private theorem integral_log_norm_riemannZeta_Ioc_half_one_le {t : ℝ} (ht : 3 < t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 1 / 2 * Real.log 11 + Real.log t / 8 + (1 / 2 * Real.log 2 + 1 / 2) := by
  have htpos : 0 < t := by linarith
  have ht3 : 3 < |t| := by rwa [abs_of_pos htpos]
  have hpos : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
    fun σ hσ ↦ norm_pos_iff.mpr (hzero σ hσ)
  have ig_a := integrableOn_log_norm_riemannZeta_subset (S := Ioc (1 / 2 : ℝ) 1) htpos.ne' hzero
    Ioc_subset_Ioi_self
  have hmaj : IntegrableOn
      (fun σ : ℝ ↦ Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ))
      (Ioc (1 / 2 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact ((intervalIntegrable_const).add
      (Continuous.intervalIntegrable (by fun_prop) (1 / 2) 1)).sub intervalIntegrable_log_one_sub
  calc (∫ σ in Ioc (1 / 2 : ℝ) 1, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioc (1 / 2 : ℝ) 1, (Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ)) := by
        refine setIntegral_mono_on_ae ig_a hmaj measurableSet_Ioc ?_
        have hne1 : ∀ᵐ σ : ℝ, σ ≠ 1 := by rw [ae_iff]; simp
        filter_upwards [hne1] with σ hσ1 hσmem
        have hσIoo : σ ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hσmem.1, lt_of_le_of_ne hσmem.2 hσ1⟩
        have h1mσ : 0 < 1 - σ := by linarith [hσIoo.2]
        have hstrip := norm_riemannZeta_le_of_mem_strip hσIoo ht3
        rw [abs_of_pos htpos] at hstrip
        have hzpos := hpos σ (le_of_lt hσmem.1)
        have hlogexp : Real.log (11 / (1 - σ) * t ^ (1 - σ))
            = Real.log 11 - Real.log (1 - σ) + (1 - σ) * Real.log t := by
          rw [Real.log_mul (ne_of_gt (div_pos (by norm_num) h1mσ))
              (ne_of_gt (Real.rpow_pos_of_pos htpos _)),
            Real.log_div (by norm_num) (ne_of_gt h1mσ), Real.log_rpow htpos]
        calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
            ≤ Real.log (11 / (1 - σ) * t ^ (1 - σ)) := Real.log_le_log hzpos hstrip
          _ = Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ) := by rw [hlogexp]; ring
    _ = ∫ σ in (1 / 2 : ℝ)..1, (Real.log 11 + (1 - σ) * Real.log t - Real.log (1 - σ)) :=
        (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = 1 / 2 * Real.log 11 + Real.log t / 8 + (1 / 2 * Real.log 2 + 1 / 2) :=
        integral_strip_majorant _

/-- **Range `(2, 4]` bound.** For `t ≠ 0` off the zeros of `ζ`, the `t`-independent
`∫_{(2,4]} log‖ζ(σ + it)‖ dσ ≤ 2·log(π²/6)`. -/
private theorem integral_log_norm_riemannZeta_Ioc_two_four_le {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 2 * Real.log (Real.pi ^ 2 / 6) := by
  have hpos : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
    fun σ hσ ↦ norm_pos_iff.mpr (hzero σ hσ)
  have ig_c := integrableOn_log_norm_riemannZeta_subset (S := Ioc (2 : ℝ) 4) ht hzero
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have ig_m3 : IntegrableOn (fun _ : ℝ ↦ Real.log (Real.pi ^ 2 / 6)) (Ioc (2 : ℝ) 4) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    exact intervalIntegrable_const
  calc (∫ σ in Ioc (2 : ℝ) 4, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioc (2 : ℝ) 4, Real.log (Real.pi ^ 2 / 6) := by
        refine setIntegral_mono_on ig_c ig_m3 measurableSet_Ioc ?_
        intro σ hσmem
        have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
        have hb := norm_riemannZeta_sub_one_le_of_two_le_re
          (s := (σ : ℂ) + Complex.I * t) (by rw [hre]; linarith [hσmem.1])
        have hzle : ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ Real.pi ^ 2 / 6 := by
          have h := norm_sub_norm_le (riemannZeta ((σ : ℂ) + Complex.I * t)) 1
          rw [norm_one] at h
          linarith
        have hzpos := hpos σ (by linarith [hσmem.1])
        exact Real.log_le_log hzpos hzle
    _ = 2 * Real.log (Real.pi ^ 2 / 6) := by
        rw [← intervalIntegral.integral_of_le (by norm_num : (2 : ℝ) ≤ 4),
          intervalIntegral.integral_const]; norm_num

/-- **Range `(4, ∞)` bound.** For `t ≠ 0` off the zeros of `ζ`, `∫_{(4,∞)} log‖ζ(σ + it)‖ dσ` is
bounded by the convergent `∫_{(4,∞)} 8(π²/6 - 1)·exp(-(log 2)·σ) dσ`. -/
private theorem integral_log_norm_riemannZeta_Ioi_four_le {t : ℝ} (ht : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    (∫ σ in Ioi (4 : ℝ), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have ig_d := integrableOn_log_norm_riemannZeta_subset (S := Ioi (4 : ℝ)) ht hzero
    (Ioi_subset_Ioi (by norm_num))
  have ig_maj : IntegrableOn
      (fun σ : ℝ ↦ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))) (Ioi (4 : ℝ)) :=
    (Real.integrableOn_exp_neg_mul_Ioi hl2 4).const_mul _
  refine setIntegral_mono_on ig_d ig_maj measurableSet_Ioi ?_
  intro σ hσmem
  calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
      ≤ |Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖| := le_abs_self _
    _ ≤ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) :=
        abs_log_norm_riemannZeta_le_exp (le_of_lt hσmem)

/-- **Parametric upper bound on `I`, abstract middle block** (`lem:lb_I_upper`). Given any bound
`∫_{(1,2]} log‖ζ(σ + it)‖ dσ ≤ M₂ + β₂·log t` on the middle strip, the upper bound on `I(t)` has
leading coefficient `⅛ + β₂`. -/
theorem logNormZetaIntegral_le_of_middle {M₂ β₂ : ℝ} {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (hmid : (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        ≤ M₂ + β₂ * Real.log t) :
    logNormZetaIntegral t ≤
      (1 / 2 * Real.log 11 + (1 / 2 * Real.log 2 + 1 / 2) + M₂
        + (2 * Real.log (Real.pi ^ 2 / 6)
          + ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))))
        + (1 / 8 + β₂) * Real.log t := by
  have htpos : 0 < t := by nlinarith [Real.pi_pos]
  have ht3 : 3 < t := by nlinarith [Real.pi_gt_three]
  rw [logNormZetaIntegral_eq_add htpos.ne' hzero]
  linarith [integral_log_norm_riemannZeta_Ioc_half_one_le ht3 hzero, hmid,
    integral_log_norm_riemannZeta_Ioc_two_four_le htpos.ne' hzero,
    integral_log_norm_riemannZeta_Ioi_four_le htpos.ne' hzero]

/-- **Absorption of the `log log t` term.** For `1 < t`,
`log(log t) ≤ (1/16)·log t + (4log2 - 1)`. -/
private theorem log_log_le_div_sixteen_add {t : ℝ} (ht : 1 < t) :
    Real.log (Real.log t) ≤ 1 / 16 * Real.log t + (4 * Real.log 2 - 1) := by
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have h16 : Real.log (Real.log t / 16) ≤ Real.log t / 16 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hlogt) (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num,
    Real.log_pow] at h16
  push_cast at h16
  linarith

/-- **Parametric upper bound on `I` via the `hC₁`-route** (`lem:lb_I_upper`). From any bound
`‖ζ(σ + it)‖ ≤ C₁·log|t|` on `[1, 2]`, with leading coefficient `b₁ = ⅛ + 1/16 = 3/16`. -/
theorem logNormZetaIntegral_le_of_bound {C₁ : ℝ} (hC₁0 : 0 < C₁)
    (hC₁ : ∀ σ t : ℝ, σ ∈ Icc (1 : ℝ) 2 → 3 < |t| →
      ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ C₁ * Real.log |t|)
    {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t ≤
      (1 / 2 * Real.log 11 + (1 / 2 * Real.log 2 + 1 / 2) + (Real.log C₁ + (4 * Real.log 2 - 1))
        + (2 * Real.log (Real.pi ^ 2 / 6)
          + ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))))
        + 3 / 16 * Real.log t := by
  have htpos : 0 < t := by nlinarith [Real.pi_pos]
  have ht3 : 3 < |t| := by rw [abs_of_pos htpos]; nlinarith [Real.pi_gt_three]
  have htgt1 : 1 < t := by nlinarith [Real.pi_gt_three]
  have hlogt : 0 < Real.log t := Real.log_pos htgt1
  have hpos : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
    fun σ hσ ↦ norm_pos_iff.mpr (hzero σ hσ)
  have ig_b := integrableOn_log_norm_riemannZeta_subset (S := Ioc (1 : ℝ) 2) htpos.ne' hzero
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have hmid : (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ (Real.log C₁ + (4 * Real.log 2 - 1)) + 1 / 16 * Real.log t := by
    have ig_m2 : IntegrableOn (fun _ : ℝ ↦ Real.log C₁ + Real.log (Real.log t))
        (Ioc (1 : ℝ) 2) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      exact intervalIntegrable_const
    calc (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        ≤ ∫ σ in Ioc (1 : ℝ) 2, (Real.log C₁ + Real.log (Real.log t)) := by
          refine setIntegral_mono_on ig_b ig_m2 measurableSet_Ioc ?_
          intro σ hσmem
          have hb := hC₁ σ t ⟨le_of_lt hσmem.1, hσmem.2⟩ ht3
          rw [abs_of_pos htpos] at hb
          have hzpos := hpos σ (by linarith [hσmem.1])
          calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
              ≤ Real.log (C₁ * Real.log t) := Real.log_le_log hzpos hb
            _ = Real.log C₁ + Real.log (Real.log t) := Real.log_mul (ne_of_gt hC₁0) (ne_of_gt hlogt)
      _ = Real.log C₁ + Real.log (Real.log t) := by
          rw [← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
            intervalIntegral.integral_const]; norm_num
      _ ≤ (Real.log C₁ + (4 * Real.log 2 - 1)) + 1 / 16 * Real.log t := by
          linarith [log_log_le_div_sixteen_add htgt1]
  linarith [logNormZetaIntegral_le_of_middle ht hzero hmid]

/-- **Elementary upper bound on `I`** (`lem:ls_upper_elem`). The `t`-independent middle block of
the elementary strip bound leaves no `log log t` term, so the leading coefficient is
`b₁ = 1/8` rather than `3/16`. -/
theorem logNormZetaIntegral_le_elem {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t ≤
      (1 / 2 * Real.log 11 + (1 / 2 * Real.log 2 + 1 / 2) + 2 * Real.log 2
        + (2 * Real.log (Real.pi ^ 2 / 6)
          + ∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ))))
        + 1 / 8 * Real.log t := by
  have htpos : 0 < t := by nlinarith [Real.pi_pos]
  have ig_b := integrableOn_log_norm_riemannZeta_subset (S := Ioc (1 : ℝ) 2) htpos.ne' hzero
    (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have hmid : (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ≤ 2 * Real.log 2 + 0 * Real.log t := by
    have hmaj : IntegrableOn (fun σ : ℝ ↦ Real.log σ - Real.log (σ - 1)) (Ioc (1 : ℝ) 2) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      exact intervalIntegral.intervalIntegrable_log'.sub intervalIntegrable_log_sub_one
    calc (∫ σ in Ioc (1 : ℝ) 2, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
        ≤ ∫ σ in Ioc (1 : ℝ) 2, (Real.log σ - Real.log (σ - 1)) := by
          refine setIntegral_mono_on ig_b hmaj measurableSet_Ioc (fun σ hσmem ↦ ?_)
          have hσ1 : 1 < σ := hσmem.1
          have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
          have hzpos : 0 < ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ :=
            norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact hσ1.le))
          have hζle := norm_riemannZeta_le_div_sub_one (t := t) hσ1
          calc Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
              ≤ Real.log (σ / (σ - 1)) := Real.log_le_log hzpos hζle
            _ = Real.log σ - Real.log (σ - 1) := Real.log_div (by linarith) (by linarith)
      _ = ∫ σ in (1 : ℝ)..2, (Real.log σ - Real.log (σ - 1)) :=
          (intervalIntegral.integral_of_le (by norm_num)).symm
      _ = 2 * Real.log 2 := integral_log_sub_log_sub_one
      _ = 2 * Real.log 2 + 0 * Real.log t := by ring
  linarith [logNormZetaIntegral_le_of_middle ht hzero hmid]

/-- The evaluated exponential tail `∫_4^∞ 8(π²/6-1)e^{-(log 2)σ} dσ = (π²/6-1)/(2 log 2)`. -/
private theorem integral_exp_tail_eq :
    (∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)))
      = (Real.pi ^ 2 / 6 - 1) / (2 * Real.log 2) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have key : (∫ σ in Ioi (4 : ℝ), 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)))
      = 8 * (Real.pi ^ 2 / 6 - 1) * ∫ σ in Ioi (4 : ℝ), Real.exp ((-Real.log 2) * σ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun σ _ ↦ ?_)
    simp only [neg_mul]
  rw [key, integral_exp_mul_Ioi (by linarith : -Real.log 2 < 0) 4]
  have hexp : Real.exp ((-Real.log 2) * 4) = 1 / 16 := by
    rw [show (-Real.log 2) * 4 = -(4 * Real.log 2) by ring, Real.exp_neg,
      show (4 : ℝ) * Real.log 2 = Real.log (2 ^ 4) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
    norm_num
  rw [hexp]; field_simp; ring

/-- Crude numeric bound `π² < 9.8697`. -/
private theorem pi_sq_lt_d4 : Real.pi ^ 2 < 9.8697 := by
  nlinarith [Real.pi_lt_d6, Real.pi_pos]

/-- `log 11 ≤ 3 log 2 + 3/8`. -/
private theorem log_eleven_le : Real.log 11 ≤ 3 * Real.log 2 + 3 / 8 := by
  have he : Real.log 11 = Real.log (2 ^ 3) + Real.log (11 / 8) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]; norm_num
  rw [he, Real.log_pow]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 8 by norm_num)
  push_cast; linarith

/-- `log(π²/6) < 1/2`, i.e. `π²/6 < e^{1/2}`. -/
private theorem log_pi_sq_div_six_lt : Real.log (Real.pi ^ 2 / 6) < 1 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have hsq : (Real.pi ^ 2 / 6) ^ 2 < Real.exp (1 / 2) ^ 2 := by
    have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [pow_two, ← Real.exp_add]; norm_num
    rw [h1]; nlinarith [pi_sq_lt_d4, Real.exp_one_gt_d9]
  exact lt_of_pow_lt_pow_left₀ 2 (Real.exp_pos _).le hsq

/-- The evaluated exponential tail `(π²/6-1)/(2 log 2) < 1/2`. -/
private theorem exp_tail_lt_half : (Real.pi ^ 2 / 6 - 1) / (2 * Real.log 2) < 1 / 2 := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pi_sq_lt_d4, Real.log_two_gt_d9]

/-- **Explicit elementary upper bound on `I`**: `I(t) ≤ 5 + (1/8)·log t` for `t ≥ 168π` off the
zeros. The true additive constant of `logNormZetaIntegral_le_elem` is `≈ 4.89`. -/
theorem logNormZetaIntegral_le_five {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t ≤ 5 + 1 / 8 * Real.log t := by
  refine (logNormZetaIntegral_le_elem ht hzero).trans ?_
  rw [integral_exp_tail_eq]
  linarith [log_eleven_le, log_pi_sq_div_six_lt, exp_tail_lt_half, Real.log_two_lt_d9]

/-- **Upper bound on `I`** (`lem:lb_I_upper`), with the additive constant `a₁` existential. -/
theorem logNormZetaIntegral_le :
    ∃ a₁ : ℝ, ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      logNormZetaIntegral t ≤ a₁ + 3 / 16 * Real.log t := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_riemannZeta_le_const_mul_log
  exact ⟨_, fun t ht hzero ↦ logNormZetaIntegral_le_of_bound hC₁0 hC₁ ht hzero⟩

/-- **Explicit upper bound on `I`**: `I(t) ≤ 9 + (3/16)·log t` for all `t ≥ 168π` off the zeros.
At the pinned constant `C₁ = 21·e^{1/2}` the true additive constant is `≈ 8.83`. -/
theorem logNormZetaIntegral_le_nine {t : ℝ} (ht : 168 * Real.pi ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    logNormZetaIntegral t ≤ 9 + 3 / 16 * Real.log t := by
  refine (logNormZetaIntegral_le_of_bound (C₁ := Real.exp (1 / 2) * (5 + 8 * 2)) (by positivity)
    (fun σ t hσ ht ↦ norm_riemannZeta_le_const_mul_log hσ ht) ht hzero).trans ?_
  -- `log C₁ = 1/2 + log 21`
  have hlogC : Real.log (Real.exp (1 / 2) * (5 + 8 * 2)) = 1 / 2 + Real.log 21 := by
    rw [show (5 + 8 * 2 : ℝ) = 21 by norm_num,
      Real.log_mul (Real.exp_ne_zero _) (by norm_num), Real.log_exp]
  have h21 : Real.log 21 ≤ 4 * Real.log 2 + 5 / 16 := by
    have he : Real.log 21 = Real.log (2 ^ 4) + Real.log (21 / 16) := by
      rw [← Real.log_mul (by positivity) (by norm_num)]; norm_num
    rw [he, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 21 / 16 by norm_num)
    push_cast; linarith
  rw [integral_exp_tail_eq, hlogC]
  -- numeric: `a₁(21·e^{1/2}) ≤ 9`
  linarith [log_eleven_le, h21, log_pi_sq_div_six_lt, exp_tail_lt_half, Real.log_two_lt_d9]

