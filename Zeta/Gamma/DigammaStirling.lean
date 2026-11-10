/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gamma.Stirling
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Gauss's digamma limit and the vanishing Stirling constant

The Euler–Maclaurin/Stirling expansion of the digamma function, whose additive Stirling constant
vanishes. Establishing that uses the product structure of `Γ` through Euler/Gauss's limit
`GammaSeq s n → Γ s`.

## Main results

- `Complex.Stirling.tendstoLocallyUniformlyOn_gammaSeq`: on the open right half-plane
  `s ↦ Complex.GammaSeq s n` converges to `Γ` locally uniformly.
- `Complex.Stirling.tendsto_log_sub_sum_inv_add`: Gauss's digamma product limit
  `ψ(s) = lim_n (Log n - ∑_{j=0}^{n} (s + j)⁻¹)` for `Re s > 0`.
- `Complex.Stirling.tendsto_digamma_sub_log_atTop`: the leading constant vanishes,
  `ψ(s + N + 1) - Log(s + N) → 0` as `N → ∞`, for `Re s > 0`.
- `Complex.Stirling.digamma_eq_log_sub`: for `Re s > 0`,
  `ψ(s) = Log s - 1/(2s) - ∑_{k=1}^{M} B_{2k}/(2k) · s^{-2k} - R_{2M+1}(g_s; 0, ∞)`.
- `Complex.Stirling.norm_digamma_sub_log_le'`: the first-order consequence
  `‖ψ(s) - Log s + 1/(2s)‖ ≤ (1/12 + 3/(2π²a)) · ‖s‖^{-2}` for `Re s ≥ a > 0`.
-/
@[expose] public section


open MeasureTheory Filter Topology
open scoped Nat Real

namespace Complex.Stirling

/-- On the right half-plane, each shifted denominator `w + j` is nonzero. -/
private theorem add_natCast_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    w + (j : ℂ) ≠ 0 := by
  intro h
  have hre : 0 < (w + (j : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) j]
  rw [h] at hre; simp at hre

/-- `(s + N)⁻¹ → 0` as `N → ∞`. -/
theorem tendsto_inv_add_natCast_atTop {s : ℂ} :
    Tendsto (fun N : ℕ ↦ (s + (N : ℂ))⁻¹) atTop (𝓝 0) := by
  have hnorm_top : Tendsto (fun N : ℕ ↦ ‖s + (N : ℂ)‖) atTop atTop := by
    have hev : ∀ N : ℕ, s.re + (N : ℝ) ≤ ‖s + (N : ℂ)‖ := fun N ↦ by
      calc s.re + (N : ℝ) = (s + (N : ℂ)).re := by simp
        _ ≤ ‖s + (N : ℂ)‖ := Complex.re_le_norm _
    exact tendsto_atTop_mono hev
      (tendsto_atTop_add_const_left atTop s.re tendsto_natCast_atTop_atTop)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_inv, Pi.inv_def] using hnorm_top.inv_tendsto_atTop

/-- Term II of the vanishing Stirling constant: for `Re s > 0`, `Log N - Log(s + N) → 0` as
`N → ∞`. -/
private theorem tendsto_log_natCast_sub_log_add_atTop {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦ Complex.log (N : ℂ) - Complex.log (s + (N : ℂ))) atTop (𝓝 0) := by
  have hsdiv : Tendsto (fun N : ℕ ↦ s / (N : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_const_div_atTop_nhds_zero_nat ‖s‖).congr fun N ↦ ?_
    rw [norm_div, Complex.norm_natCast]
  have h1 : Tendsto (fun N : ℕ ↦ 1 + s / (N : ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hsdiv
  have hcont : ContinuousAt Complex.log 1 :=
    continuousAt_clog (Or.inl (by rw [Complex.one_re]; norm_num))
  have hlog : Tendsto (fun N : ℕ ↦ Complex.log (1 + s / (N : ℂ))) atTop (𝓝 0) := by
    have := (hcont.tendsto.comp h1)
    simpa [Function.comp_def, Complex.log_one] using this
  have hfact : ∀ᶠ N : ℕ in atTop,
      Complex.log (N : ℂ) - Complex.log (s + (N : ℂ)) = -Complex.log (1 + s / (N : ℂ)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    have hr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hsNne : s + (N : ℂ) ≠ 0 := add_natCast_ne_zero_of_re_pos hs N
    have hxne : 1 + s / (N : ℂ) ≠ 0 := by
      rw [show 1 + s / (N : ℂ) = (s + (N : ℂ)) / (N : ℂ) by field_simp; ring]
      exact div_ne_zero hsNne hNc
    have hsN : s + (N : ℂ) = ((N : ℝ) : ℂ) * (1 + s / (N : ℂ)) := by
      rw [Complex.ofReal_natCast]; field_simp; ring
    rw [hsN, Complex.log_ofReal_mul hr hxne, ← Complex.natCast_log]
    ring
  refine Tendsto.congr' (hfact.mono fun N h ↦ h.symm) ?_
  simpa using hlog.neg

/-- The interval-restricted Euler kernel `𝟙_{(0,n]}(x) · (1 - x/n)ⁿ` is nonnegative. -/
private theorem indicator_kernel_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ (Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x := by
  rw [Set.indicator_apply]
  split
  · rename_i hmem
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hmem.1 hmem.2
    have hx1 : x / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hmem.2
    exact pow_nonneg (by linarith) n
  · exact le_refl 0

/-- The interval-restricted Euler kernel `𝟙_{(0,n]}(x) · (1 - x/n)ⁿ` is bounded above by
`e^{-x}`. -/
private theorem indicator_kernel_le_exp (n : ℕ) (x : ℝ) :
    (Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x ≤ Real.exp (-x) := by
  rw [Set.indicator_apply]
  split
  · rename_i hmem; exact Real.one_sub_div_pow_le_exp_neg hmem.2
  · exact (Real.exp_pos _).le

/-- The `s`-free domination `|𝟙_{(0,n]}(x)·(1 - x/n)ⁿ - e^{-x}| ≤ e^{-x}`. -/
private theorem abs_indicator_sub_exp_le (n : ℕ) (x : ℝ) :
    |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
      ≤ Real.exp (-x) := by
  rw [abs_le]
  refine ⟨by linarith [indicator_kernel_nonneg n x], ?_⟩
  linarith [indicator_kernel_le_exp n x, Real.exp_pos (-x)]

/-- The `s`-free dominating integrand `e^{-x}(x^{a-1} + x^{b-1})` is integrable on `(0, ∞)` for
`a, b > 0`. -/
private theorem integrableOn_exp_mul_two_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1))) (Set.Ioi 0) :=
  ((Real.GammaIntegral_convergent ha).add (Real.GammaIntegral_convergent hb)).congr_fun
    (fun x _ ↦ by simp only [Pi.add_apply]; ring) measurableSet_Ioi

/-- For `x > 0` and `a ≤ c ≤ b`, the weight `x^{c-1}` is dominated by `x^{a-1} + x^{b-1}`. -/
private theorem rpow_sub_one_le_add {a b c x : ℝ} (hx : 0 < x) (hac : a ≤ c) (hcb : c ≤ b) :
    x ^ (c - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
  rcases le_total 1 x with hx1 | hx1
  · have h := Real.rpow_le_rpow_of_exponent_le hx1 (show c - 1 ≤ b - 1 by linarith)
    have := Real.rpow_nonneg hx.le (a - 1); linarith
  · have h := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show a - 1 ≤ c - 1 by linarith)
    have := Real.rpow_nonneg hx.le (b - 1); linarith

/-- The error integrand `|𝟙_{(0,n]}(x)·(1 - x/n)ⁿ - e^{-x}| · (x^{a-1} + x^{b-1})` is
a.e.-strongly measurable. -/
private theorem aestronglyMeasurable_abs_indicator_sub_exp_mul (a b : ℝ) (n : ℕ) :
    AEStronglyMeasurable (fun x : ℝ ↦
      |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
        * (x ^ (a - 1) + x ^ (b - 1))) (volume.restrict (Set.Ioi 0)) := by
  have hW : ContinuousOn (fun x : ℝ ↦ x ^ (a - 1) + x ^ (b - 1)) (Set.Ioi 0) :=
    (continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt hx)).add
      (continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt hx))
  have hker : Measurable fun x : ℝ ↦
      (Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x :=
    Measurable.indicator
      ((continuous_const.sub (continuous_id.div_const _)).pow n).measurable measurableSet_Ioc
  have hexp : Measurable fun x : ℝ ↦ Real.exp (-x) :=
    (Real.continuous_exp.comp continuous_neg).measurable
  have habs : Measurable fun x : ℝ ↦
      |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)| := by
    simp only [abs_eq_max_neg]
    exact (hker.sub hexp).max (hker.sub hexp).neg
  exact (habs.aestronglyMeasurable).mul (hW.aestronglyMeasurable measurableSet_Ioi)

/-- The error integrand `|𝟙_{(0,n]}(x)·(1 - x/n)ⁿ - e^{-x}| · (x^{a-1} + x^{b-1})` is integrable on
`(0, ∞)`. -/
private theorem integrableOn_abs_indicator_sub_exp_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    IntegrableOn (fun x : ℝ ↦
      |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
        * (x ^ (a - 1) + x ^ (b - 1))) (Set.Ioi 0) := by
  refine (integrableOn_exp_mul_two_rpow ha hb).mono'
    (aestronglyMeasurable_abs_indicator_sub_exp_mul a b n) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (abs_indicator_sub_exp_le n x) (by positivity)

/-- Dominated convergence for the `s`-free error: as `n → ∞` the total error weight
`∫₀^∞ |𝟙_{(0,n]}(x)·(1 - x/n)ⁿ - e^{-x}| (x^{a-1} + x^{b-1}) dx → 0`. -/
private theorem tendsto_integral_abs_indicator_sub_exp_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ ∫ x in Set.Ioi (0 : ℝ),
        |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
          * (x ^ (a - 1) + x ^ (b - 1))) atTop (𝓝 0) := by
  set F : ℕ → ℝ → ℝ := fun n x ↦
    |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
      * (x ^ (a - 1) + x ^ (b - 1)) with hFdef
  have h_bound : ∀ n, ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ‖F n x‖ ≤ Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)) := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [hFdef, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (abs_indicator_sub_exp_le n x) (by positivity)
  have h_lim : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun n ↦ F n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hconv : Tendsto (fun n : ℕ ↦
        (Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x) atTop
        (𝓝 (Real.exp (-x))) := by
      have key : Tendsto (fun n : ℕ ↦ (1 - x / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp (-x))) := by
        refine (Real.tendsto_one_add_div_pow_exp (-x)).congr fun n ↦ ?_
        rw [neg_div, ← sub_eq_add_neg]
      refine key.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
      have hmem : x ∈ Set.Ioc 0 (n : ℝ) := ⟨hx0, by rw [← Nat.ceil_le]; exact hn⟩
      exact (Set.indicator_of_mem hmem (fun y ↦ (1 - y / (n : ℝ)) ^ n)).symm
    have hz : Tendsto (fun n : ℕ ↦
        |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|)
        atTop (𝓝 0) := by simpa using (hconv.sub_const (Real.exp (-x))).abs
    rw [hFdef]; simpa using hz.mul_const (x ^ (a - 1) + x ^ (b - 1))
  have hmain := tendsto_integral_of_dominated_convergence (f := fun _ : ℝ ↦ (0 : ℝ))
    (fun x ↦ Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)))
    (fun n ↦ aestronglyMeasurable_abs_indicator_sub_exp_mul a b n)
    (integrableOn_exp_mul_two_rpow ha hb) h_bound h_lim
  simpa [hFdef] using hmain

/-- `GammaSeq` as an improper integral: for `0 < Re s` and `n ≠ 0`,
`GammaSeq s n = ∫_{(0,∞)} 𝟙_{(0,n]}(x)·(1 - x/n)ⁿ · x^{s-1}`. -/
private theorem GammaSeq_eq_setIntegral_indicator {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    Complex.GammaSeq s n = ∫ x in Set.Ioi (0 : ℝ),
      ↑((Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x) * (x : ℂ) ^ (s - 1) := by
  have hpoint : ∀ x : ℝ,
      ↑((Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x) * (x : ℂ) ^ (s - 1)
        = (Set.Ioc 0 (n : ℝ)).indicator
            (fun y ↦ (((1 - y / n) ^ n : ℝ) : ℂ) * (y : ℂ) ^ (s - 1)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioc 0 (n : ℝ)
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hs hn,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (n : ℝ)),
    setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ hpoint x,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self]

/-- The `GammaSeq` integrand `𝟙_{(0,n]}(x)·(1 - x/n)ⁿ · x^{s-1}` is integrable on `(0, ∞)` for
`0 < Re s`. -/
private theorem integrableOn_Ioi_indicator_kernel_mul_cpow {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (fun x : ℝ ↦
        ↑((Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x) * (x : ℂ) ^ (s - 1))
      (Set.Ioi (0 : ℝ)) := by
  refine (Real.GammaIntegral_convergent hs).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.measurable.comp
      (Measurable.indicator (by fun_prop) measurableSet_Ioc)).aestronglyMeasurable).mul
      (aestronglyMeasurable_ofReal_cpow_Ioi le_rfl (s - 1))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (indicator_kernel_nonneg n x)]
    exact mul_le_mul_of_nonneg_right (indicator_kernel_le_exp n x) (Real.rpow_nonneg hx0.le _)

/-- The `s`-free uniform bound: for `a ≤ Re s ≤ b` and `n ≥ 1`, `‖Γ(s) - GammaSeq(s, n)‖` is
bounded by the `s`-free total error weight. -/
private theorem norm_Gamma_sub_GammaSeq_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {s : ℂ} (hsa : a ≤ s.re) (hsb : s.re ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    ‖Complex.Gamma s - Complex.GammaSeq s n‖
      ≤ ∫ x in Set.Ioi (0 : ℝ),
          |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
            * (x ^ (a - 1) + x ^ (b - 1)) := by
  have hs : 0 < s.re := lt_of_lt_of_le ha hsa
  set g : ℝ → ℝ := fun x ↦ (Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x with hg
  have hΓint : IntegrableOn (fun x : ℝ ↦ (↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1))) (Set.Ioi 0) :=
    Complex.GammaIntegral_convergent hs
  have hΓ : Complex.Gamma s = ∫ x in Set.Ioi (0 : ℝ), ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) := by
    rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  have hGSint : IntegrableOn (fun x : ℝ ↦ ↑(g x) * (x : ℂ) ^ (s - 1)) (Set.Ioi 0) := by
    simpa only [hg] using integrableOn_Ioi_indicator_kernel_mul_cpow hs n
  have hGS : Complex.GammaSeq s n = ∫ x in Set.Ioi (0 : ℝ), ↑(g x) * (x : ℂ) ^ (s - 1) := by
    simpa only [hg] using GammaSeq_eq_setIntegral_indicator hs (by lia : n ≠ 0)
  rw [hΓ, hGS, ← integral_sub hΓint hGSint]
  calc ‖∫ x in Set.Ioi (0 : ℝ),
          (↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) - ↑(g x) * (x : ℂ) ^ (s - 1))‖
      ≤ ∫ x in Set.Ioi (0 : ℝ),
          ‖↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) - ↑(g x) * (x : ℂ) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Ioi (0 : ℝ), |g x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1)) := by
        refine setIntegral_mono_on (hΓint.sub hGSint).norm
          (integrableOn_abs_indicator_sub_exp_mul ha (lt_of_lt_of_le ha hab) n)
          measurableSet_Ioi fun x hx ↦ ?_
        have hx0 : (0 : ℝ) < x := hx
        rw [show (↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) - ↑(g x) * (x : ℂ) ^ (s - 1))
              = (↑(Real.exp (-x) - g x) : ℂ) * (x : ℂ) ^ (s - 1) by push_cast; ring,
          norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re,
          Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (rpow_sub_one_le_add hx0 hsa hsb) (abs_nonneg _)

/-- Locally uniform Euler/Gauss limit: on the open right half-plane `{Re s > 0}` the sequence
`s ↦ Complex.GammaSeq s n` converges to `Γ` locally uniformly. -/
theorem tendstoLocallyUniformlyOn_gammaSeq :
    TendstoLocallyUniformlyOn (fun (n : ℕ) (s : ℂ) ↦ Complex.GammaSeq s n) Complex.Gamma
      atTop {s : ℂ | 0 < s.re} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_re_gt 0)]
  intro K hKsub hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  obtain ⟨xa, hxaK, hxa⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  obtain ⟨xb, hxbK, hxb⟩ := hK.exists_isMaxOn hKne Complex.continuous_re.continuousOn
  have ha : 0 < xa.re := hKsub hxaK
  have hab : xa.re ≤ xb.re := isMinOn_iff.mp hxa xb hxbK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, (∫ x in Set.Ioi (0 : ℝ),
      |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
        * (x ^ (xa.re - 1) + x ^ (xb.re - 1))) < ε :=
    (tendsto_integral_abs_indicator_sub_exp_mul ha
      (lt_of_lt_of_le ha hab)).eventually (gt_mem_nhds hε)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  intro s hsK
  rw [Complex.dist_eq]
  calc ‖Complex.Gamma s - Complex.GammaSeq s n‖
      ≤ ∫ x in Set.Ioi (0 : ℝ),
          |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
            * (x ^ (xa.re - 1) + x ^ (xb.re - 1)) :=
        norm_Gamma_sub_GammaSeq_le ha hab (isMinOn_iff.mp hxa s hsK) (isMaxOn_iff.mp hxb s hsK) hn1
    _ < ε := hn

/-- Gauss's digamma product limit: for `Re s > 0`,
`ψ(s) = lim_n (Log n - ∑_{j=0}^{n} (s + j)⁻¹)`. -/
theorem tendsto_log_sub_sum_inv_add {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ ↦ Complex.log (n : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹)
      atTop (𝓝 (Complex.digamma s)) := by
  have hΩ : s ∈ {z : ℂ | 0 < z.re} := hs
  -- Each `GammaSeq · n` (for `n ≥ 1`) is holomorphic on the right half-plane.
  have hdiff : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (fun w ↦ Complex.GammaSeq w n)
      {z : ℂ | 0 < z.re} := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr (by lia)⟩
    have hnum : DifferentiableOn ℂ (fun w : ℂ ↦ (n : ℂ) ^ w * (n ! : ℂ)) {z : ℂ | 0 < z.re} :=
      ((differentiable_const_cpow_of_neZero (n : ℂ)).mul_const _).differentiableOn
    have hprod : DifferentiableOn ℂ (fun w : ℂ ↦ ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)))
        {z : ℂ | 0 < z.re} :=
      DifferentiableOn.fun_finsetProd fun j _ ↦ (differentiable_id.add_const _).differentiableOn
    have hden : ∀ w ∈ {z : ℂ | 0 < z.re},
        (∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) ≠ 0 := fun w hw ↦
      Finset.prod_ne_zero_iff.mpr fun j _ ↦ add_natCast_ne_zero_of_re_pos hw j
    simp only [Complex.GammaSeq]
    exact hnum.div hprod hden
  have hgne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hkey := Complex.logDeriv_tendsto (isOpen_re_gt 0) hΩ
    tendstoLocallyUniformlyOn_gammaSeq hdiff hgne
  rw [Complex.digamma_def]
  refine hkey.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr (by lia)⟩
  have hcpow_ne : (n : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (NeZero.ne _))
  have hfac_ne : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hAne : (n : ℂ) ^ s * (n ! : ℂ) ≠ 0 := mul_ne_zero hcpow_ne hfac_ne
  have hBne : (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ add_natCast_ne_zero_of_re_pos hs j
  have hdA : DifferentiableAt ℂ (fun w : ℂ ↦ (n : ℂ) ^ w * (n ! : ℂ)) s :=
    ((differentiable_const_cpow_of_neZero (n : ℂ)).mul_const _).differentiableAt
  have hdB : DifferentiableAt ℂ (fun w : ℂ ↦ ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) s :=
    DifferentiableAt.fun_finsetProd fun j _ ↦ (differentiable_id.add_const _).differentiableAt
  -- Logarithmic derivative of `n ^ w`: the constant `Log n`.
  have hlogcpow : logDeriv (fun w : ℂ ↦ (n : ℂ) ^ w) s = Complex.log (n : ℂ) := by
    rw [logDeriv_apply, Complex.deriv_const_cpow differentiableAt_fun_id (n : ℂ)]
    simp only [deriv_id'']
    rw [mul_one, mul_div_assoc, div_self hcpow_ne, mul_one]
  -- Logarithmic derivative of the product: `∑ (s + j)⁻¹`.
  have hlogprod : logDeriv (fun w : ℂ ↦ ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) s
      = ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹ := by
    rw [show (fun w : ℂ ↦ ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)))
        = ∏ j ∈ Finset.range (n + 1), (fun w : ℂ ↦ w + (j : ℂ)) from by
          funext w; rw [Finset.prod_apply],
      logDeriv_prod (fun j _ ↦ add_natCast_ne_zero_of_re_pos hs j)
      (fun j _ ↦ (differentiable_id.add_const _).differentiableAt)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hderiv1 : deriv (fun w : ℂ ↦ w + (j : ℂ)) s = 1 := by simp
    rw [logDeriv_apply, hderiv1, one_div]
  rw [show (fun w ↦ Complex.GammaSeq w n)
      = (fun w : ℂ ↦ (n : ℂ) ^ w * (n ! : ℂ)) /
          fun w : ℂ ↦ ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) from by
        funext w; rw [Pi.div_apply, Complex.GammaSeq],
    logDeriv_div s hAne hBne hdA hdB, logDeriv_mul_const s (n ! : ℂ) hfac_ne, hlogcpow, hlogprod]

/-- The additive Stirling constant vanishes: for `Re s > 0`,
`ψ(s + N + 1) - Log(s + N) → 0` as `N → ∞`. -/
theorem tendsto_digamma_sub_log_atTop {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦ Complex.digamma (s + (N : ℂ) + 1) - Complex.log (s + (N : ℂ)))
      atTop (𝓝 0) := by
  -- Term I: `ψ(s+N+1) - Log N = ψ(s) - (Log N - ∑_{j=0}^N (s+j)⁻¹) → ψ(s) - ψ(s) = 0`.
  have hI : Tendsto (fun N : ℕ ↦ Complex.digamma (s + (N : ℂ) + 1) - Complex.log (N : ℂ))
      atTop (𝓝 0) := by
    have hrw : ∀ N : ℕ, Complex.digamma (s + (N : ℂ) + 1) - Complex.log (N : ℂ)
        = Complex.digamma s
          - (Complex.log (N : ℂ) - ∑ j ∈ Finset.range (N + 1), (s + (j : ℂ))⁻¹) := by
      intro N
      rw [sum_inv_add_eq_digamma_sub s hs N]; ring
    have hlim := tendsto_const_nhds (x := Complex.digamma s) |>.sub (tendsto_log_sub_sum_inv_add hs)
    rw [sub_self] at hlim
    exact hlim.congr fun N ↦ (hrw N).symm
  -- Term II: `Log N - Log(s+N) = -Log(1 + s/N) → 0`.
  have hII : Tendsto (fun N : ℕ ↦ Complex.log (N : ℂ) - Complex.log (s + (N : ℂ)))
      atTop (𝓝 0) := tendsto_log_natCast_sub_log_add_atTop hs
  -- Combine.
  have := hI.add hII
  rw [add_zero] at this
  exact this.congr fun N ↦ by ring

/-- Euler–Maclaurin/Stirling expansion of the digamma function: for every `s` with `Re s > 0`
and every `M : ℕ`,
`ψ(s) = Log s - 1/(2s) - ∑_{k=1}^{M} B_{2k}/(2k) · s^{-2k} - R_{2M+1}(g_s; 0, ∞)`,
with `R_{2M+1}(g_s; 0, ∞) = digammaRemainderIoi s (2M+1)` bounded by
`norm_digammaRemainderIoi_le'`. -/
theorem digamma_eq_log_sub (s : ℂ) (hs : 0 < s.re) (M : ℕ) :
    Complex.digamma s = Complex.log s - (2 * s)⁻¹
      - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
      - digammaRemainderIoi s (2 * M + 1) := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  -- The vanishing pieces as `N → ∞`.
  have hL1 : Tendsto (fun N : ℕ ↦ Complex.digamma (s + (N : ℂ) + 1) - Complex.log (s + (N : ℂ)))
      atTop (𝓝 0) := tendsto_digamma_sub_log_atTop hs
  have hL2 : Tendsto (fun N : ℕ ↦ (s + (N : ℂ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_add_natCast_atTop
  have hL3 : ∀ k : ℕ, 1 ≤ k →
      Tendsto (fun N : ℕ ↦ (s + (N : ℂ)) ^ (-(2 * k : ℤ))) atTop (𝓝 0) := by
    intro k hk
    have h2k : (2 * k) ≠ 0 := by lia
    have hrw : ∀ N : ℕ, (s + (N : ℂ)) ^ (-(2 * k : ℤ)) = ((s + (N : ℂ))⁻¹) ^ (2 * k) := by
      intro N
      rw [show (-(2 * k : ℤ)) = -((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        inv_pow]
    have hpow := hL2.pow (2 * k)
    rw [zero_pow h2k] at hpow
    exact hpow.congr fun N ↦ (hrw N).symm
  have hL4 : Tendsto
      (fun N : ℕ ↦ eulerMaclaurinRemainder (2 * M + 1)
        (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) 0 (N : ℝ))
      atTop (𝓝 (digammaRemainderIoi s (2 * M + 1))) := by
    simp only [Complex.eulerMaclaurinRemainder_eq, digammaRemainderIoi]
    exact (intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_inv_add s hs (2 * M + 1) (by lia))
      tendsto_natCast_atTop_atTop).const_mul _
  have hSplus : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.Icc 1 M,
      (bernoulli (2 * k) : ℂ) / (2 * k) * (s + (N : ℂ)) ^ (-(2 * k : ℤ))) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.Icc 1 M) (fun k hk ↦ by
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      simpa only [mul_zero] using (hL3 k hk1).const_mul ((bernoulli (2 * k) : ℂ) / (2 * k)))
    simpa using h
  -- The rearranged Euler–Maclaurin identity, equal to `ψ(s)` for every `N`.
  set seq : ℕ → ℂ := fun N ↦
    (Complex.digamma (s + (N : ℂ) + 1) - Complex.log (s + (N : ℂ)))
      + Complex.log s
      - (s⁻¹ + (s + (N : ℂ))⁻¹) / 2
      + (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * (s + (N : ℂ)) ^ (-(2 * k : ℤ)))
      - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
      - eulerMaclaurinRemainder (2 * M + 1)
          (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) 0 (N : ℝ) with hseq
  have hconst : ∀ N : ℕ, Complex.digamma s = seq N := by
    intro N
    have h := sum_inv_add_eq s hs M N
    have hsplit : (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k)
          * ((s + (N : ℂ)) ^ (-(2 * k : ℤ)) - s ^ (-(2 * k : ℤ))))
        = (∑ k ∈ Finset.Icc 1 M,
            (bernoulli (2 * k) : ℂ) / (2 * k) * (s + (N : ℂ)) ^ (-(2 * k : ℤ)))
          - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ))) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hsplit] at h
    simp only [hseq]
    linear_combination -h
  have htend : Tendsto seq atTop (𝓝 (Complex.log s - (2 * s)⁻¹
      - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
      - digammaRemainderIoi s (2 * M + 1))) := by
    -- The combinator naturally lands on the limit with `0`s and `s⁻¹/2`; reconcile to `(2 * s)⁻¹`.
    have hcomb : Tendsto seq atTop (𝓝 (0 + Complex.log s - (s⁻¹ + 0) / 2 + 0
        - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
        - digammaRemainderIoi s (2 * M + 1))) := by
      rw [hseq]
      exact ((((hL1.add tendsto_const_nhds).sub
        ((tendsto_const_nhds.add hL2).div_const 2)).add hSplus).sub tendsto_const_nhds).sub hL4
    have hval : (0 + Complex.log s - (s⁻¹ + 0) / 2 + 0
          - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
          - digammaRemainderIoi s (2 * M + 1))
        = (Complex.log s - (2 * s)⁻¹
          - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
          - digammaRemainderIoi s (2 * M + 1)) := by
      field_simp
      ring
    rwa [hval] at hcomb
  exact tendsto_nhds_unique (tendsto_const_nhds.congr hconst) htend

/-- Explicit first-order digamma bound: for `a > 0` and `Re s ≥ a`,
`‖ψ(s) - Log s + (2s)⁻¹‖ ≤ (1/12 + 3/(2π²a)) · ‖s‖^(-2)`. -/
theorem norm_digamma_sub_log_le' {a : ℝ} (ha : 0 < a) (s : ℂ) (has : a ≤ s.re) :
    ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖
      ≤ (1 / 12 + 3 / (2 * π ^ 2 * a)) * ‖s‖ ^ (-(2 : ℤ)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hs : 0 < s.re := lt_of_lt_of_le ha has
  have hnpos : 0 < ‖s‖ := norm_pos_iff.mpr (Complex.ne_zero_of_re_pos hs)
  have han : a ≤ ‖s‖ := le_trans has (Complex.re_le_norm s)
  have hsum : (∑ k ∈ Finset.Icc 1 1, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
      = (bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ)) := by
    rw [Finset.Icc_self, Finset.sum_singleton]; norm_num
  have hexp := digamma_eq_log_sub s hs 1
  rw [hsum, show (2 * 1 + 1) = 3 from rfl] at hexp
  have hE : Complex.digamma s - Complex.log s + (2 * s)⁻¹
      = -((bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ))) - digammaRemainderIoi s 3 := by
    rw [hexp]; ring
  have hb2 : ‖(bernoulli 2 : ℂ) / 2‖ = 1 / 12 := by
    rw [bernoulli_two, norm_div, Complex.norm_ratCast]; norm_num
  have hR3 := norm_digammaRemainderIoi_le' s hs 3 (by norm_num)
  rw [show (3 ! : ℝ) = 6 from by norm_num [Nat.factorial], show (3 - 1) = 2 from rfl] at hR3
  have hsnorm3 : ‖s‖ ^ (-(3 : ℤ)) ≤ a⁻¹ * ‖s‖ ^ (-(2 : ℤ)) := by
    rw [show (-(3 : ℤ)) = -(2 : ℤ) + -(1 : ℤ) from by ring, zpow_add₀ hnpos.ne', zpow_neg_one,
      mul_comm (a⁻¹) (‖s‖ ^ (-(2 : ℤ)))]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ ha han) (zpow_nonneg (norm_nonneg _) _)
  calc ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖
      = ‖-((bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ))) - digammaRemainderIoi s 3‖ := by rw [hE]
    _ ≤ ‖-((bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ)))‖ + ‖digammaRemainderIoi s 3‖ :=
        norm_sub_le _ _
    _ = 1 / 12 * ‖s‖ ^ (-(2 : ℤ)) + ‖digammaRemainderIoi s 3‖ := by
        rw [norm_neg, norm_mul, norm_zpow, hb2]
    _ ≤ 1 / 12 * ‖s‖ ^ (-(2 : ℤ)) + 6 / (2 * π) ^ 2 * ‖s‖ ^ (-(3 : ℤ)) := by linarith [hR3]
    _ ≤ 1 / 12 * ‖s‖ ^ (-(2 : ℤ)) + 6 / (2 * π) ^ 2 * (a⁻¹ * ‖s‖ ^ (-(2 : ℤ))) := by
        linarith [mul_le_mul_of_nonneg_left hsnorm3 (by positivity : (0 : ℝ) ≤ 6 / (2 * π) ^ 2)]
    _ = (1 / 12 + 3 / (2 * π ^ 2 * a)) * ‖s‖ ^ (-(2 : ℤ)) := by
        have hane : a ≠ 0 := ha.ne'
        have hπne : π ≠ 0 := hπ.ne'
        field_simp
        ring

end Complex.Stirling
