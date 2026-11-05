/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gamma.Growth
public import Zeta.Gamma.LogGammaBranch
public import Zeta.Gamma.LogGammaStirling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Euler–Maclaurin/Stirling expansion of `log Γ`

The identity `Log Γ(w) = S_M(w) + ρ_M(w)` on the right half-plane, where `S_M = logGammaStirling`
is the Stirling approximant and `ρ_M = logGammaRemainderIoi` the improper `log Γ` remainder.

## Main results

- `Complex.Stirling.logGamma_eq_stirling_add_remainder`: `Log Γ(w) = S_M(w) + ρ_M(w)` for `M ≥ 1`,
  `Re w > 0`.
-/
@[expose] public section


open MeasureTheory Filter
open scoped Topology Nat Real

namespace Complex.Stirling

/-- The digamma remainder written as the difference between the truncated Stirling series of `ψ`
and `ψ` itself, on the right half-plane. -/
private theorem digammaRemainderIoi_eq {M : ℕ} {z : ℂ} (hz : 0 < z.re) :
    digammaRemainderIoi z (2 * M + 1)
      = (Complex.log z - (2 * z)⁻¹
          - ∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * z ^ (-(2 * k : ℤ)))
        - Complex.digamma z := by
  rw [digamma_eq_log_sub z hz M]; ring

/-- **Shared derivative.** On `{Re > 0}`, `g := logGamma - S_M` has derivative
`-R^ψ_{2M+1}`. -/
private theorem hasDerivAt_logGamma_sub_logGammaStirling {M : ℕ} {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun s ↦ logGamma s - logGammaStirling M s)
      (-(digammaRemainderIoi z (2 * M + 1))) z := by
  have h := (hasDerivAt_logGamma hz).sub (hasDerivAt_logGammaStirling (M := M) hz)
  rwa [show -(digammaRemainderIoi z (2 * M + 1))
      = Complex.digamma z - (Complex.log z - (2 * z)⁻¹
        - ∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * z ^ (-(2 * k : ℤ)))
      by rw [digamma_eq_log_sub z hz M]; ring]

/-- **Chain rule for `g` along a real-parametrised affine complex path.** If `ψ` is complex
differentiable at `↑t` with `Re (ψ ↑t) > 0`, then `t ↦ g (ψ ↑t)` has derivative `-R^ψ(ψ ↑t) · c`,
where `g := logGamma - S_M`. -/
private theorem hasDerivAt_logGamma_sub_logGammaStirling_comp {M : ℕ} {ψ : ℂ → ℂ}
    {c : ℂ} {t : ℝ} (hψ : HasDerivAt ψ c (t : ℂ)) (ht : 0 < (ψ (t : ℂ)).re) :
    HasDerivAt (fun s : ℝ ↦ logGamma (ψ (s : ℂ)) - logGammaStirling M (ψ (s : ℂ)))
      (-(digammaRemainderIoi (ψ (t : ℂ)) (2 * M + 1)) * c) t := by
  simpa [Function.comp_def] using
    ((hasDerivAt_logGamma_sub_logGammaStirling (M := M) ht).comp (t : ℂ) hψ).comp_ofReal

/-- Continuity of `τ ↦ R^ψ(f τ)` at any point where `Re (f τ) > 0`. -/
private theorem continuousAt_digammaRemainderIoi_comp {M : ℕ} {f : ℝ → ℂ} {t : ℝ}
    (hf : ContinuousAt f t) (ht : 0 < (f t).re) :
    ContinuousAt (fun s : ℝ ↦ digammaRemainderIoi (f s) (2 * M + 1)) t := by
  have hmem : {s : ℝ | 0 < (f s).re} ∈ nhds t :=
    hf.preimage_mem_nhds ((isOpen_re_gt 0).mem_nhds ht)
  have hslit : f t ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl ht)
  have hne : f t ≠ 0 := Complex.ne_zero_of_re_pos ht
  have c1 : ContinuousAt (fun s ↦ Complex.log (f s)) t := (continuousAt_clog hslit).comp hf
  have c2 : ContinuousAt (fun s ↦ (2 * f s)⁻¹) t :=
    (continuousAt_const.mul hf).inv₀ (by simp [hne])
  have c3 : ContinuousAt
      (fun s ↦ ∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * (f s) ^ (-(2 * k : ℤ)))
      t :=
    tendsto_finsetSum _ fun k _ ↦ (hf.zpow₀ (-(2 * (k : ℤ))) (Or.inl hne)).const_mul _
  have c4 : ContinuousAt (fun s ↦ Complex.digamma (f s)) t := (continuousAt_digamma ht).comp hf
  refine (((c1.sub c2).sub c3).sub c4).congr ?_
  filter_upwards [hmem] with s hs using (digammaRemainderIoi_eq hs).symm

/-- The pointwise remainder bound in terms of the real part:
`‖R^ψ(s)‖ ≤ C · (Re s)^{-(2M+1)}` for `Re s > 0`. -/
private theorem norm_digammaRemainderIoi_le_re {M : ℕ} (hM : 1 ≤ M) {s : ℂ} (hs : 0 < s.re) :
    ‖digammaRemainderIoi s (2 * M + 1)‖
      ≤ ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M) * s.re ^ (-(2 * M + 1 : ℝ)) := by
  have h1 := norm_digammaRemainderIoi_le' s hs (2 * M + 1) (by lia)
  have hge : s.re ≤ ‖s‖ := Complex.re_le_norm s
  have hzr : ‖s‖ ^ (-(2 * M + 1 : ℤ)) = ‖s‖ ^ (-(2 * M + 1 : ℝ)) := by
    rw [show (-(2 * M + 1 : ℝ)) = ((-(2 * M + 1 : ℤ) : ℤ) : ℝ) by push_cast; ring,
      Real.rpow_intCast]
  have hmono : ‖s‖ ^ (-(2 * M + 1 : ℝ)) ≤ s.re ^ (-(2 * M + 1 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hs hge (neg_nonpos.mpr (by positivity))
  have hCpos : (0 : ℝ) ≤ ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M) := by positivity
  calc ‖digammaRemainderIoi s (2 * M + 1)‖
      ≤ ((2 * M + 1)! : ℝ) / (2 * π) ^ ((2 * M + 1) - 1) * ‖s‖ ^ (-(2 * M + 1 : ℤ)) := h1
    _ = ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M) * ‖s‖ ^ (-(2 * M + 1 : ℝ)) := by
        rw [hzr, show (2 * M + 1) - 1 = 2 * M by lia]
    _ ≤ ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M) * s.re ^ (-(2 * M + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmono hCpos

/-- **Integrability along the ray.** `τ ↦ R^ψ(w+τ)` is integrable on `(0, ∞)`. -/
private theorem integrableOn_digammaRemainderIoi_shift {M : ℕ} (hM : 1 ≤ M) {w : ℂ}
    (hw : 0 < w.re) :
    IntegrableOn (fun τ : ℝ ↦ digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1)) (Set.Ioi 0) := by
  set C : ℝ := ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M)
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hre : ∀ {τ : ℝ}, 0 < τ → 0 < (w + (τ : ℂ)).re := fun {τ} hτ ↦ by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hmaj : IntegrableOn (fun τ : ℝ ↦ C * (τ + w.re) ^ (-(2 * M + 1 : ℝ))) (Set.Ioi 0) :=
    (integrableOn_add_rpow_Ioi_of_lt (show (-(2 * M + 1 : ℝ)) < -1 by linarith)
      (show -w.re < 0 by linarith)).const_mul C
  have hmeas : AEStronglyMeasurable
      (fun τ : ℝ ↦ digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))
      (volume.restrict (Set.Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro τ hτ
    exact (continuousAt_digammaRemainderIoi_comp
      (Complex.continuous_ofReal.const_add w).continuousAt (hre hτ)).continuousWithinAt
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  have hb := norm_digammaRemainderIoi_le_re hM (hre hτ)
  rwa [show (w + (τ : ℂ)).re = τ + w.re by
    simp only [Complex.add_re, Complex.ofReal_re]; ring] at hb

/-- **Horizontal fundamental theorem of calculus.** For `n : ℕ`,
`g(w) - g(w+n) = ∫_0^n R^ψ(w+τ) dτ`, where `g = logGamma - S_M`. -/
private theorem logGamma_sub_logGammaStirling_shift_eq_integral {M : ℕ} (hM : 1 ≤ M)
    {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    (logGamma w - logGammaStirling M w)
        - (logGamma (w + n) - logGammaStirling M (w + n))
      = ∫ τ in (0 : ℝ)..(n : ℝ), digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1) := by
  have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) (n : ℝ),
      HasDerivAt (fun t : ℝ ↦ logGamma (w + (t : ℂ)) - logGammaStirling M (w + (t : ℂ)))
        (-(digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))) τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) ≤ τ := by
      rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ (n : ℝ))] at hτ; exact hτ.1
    have hre : 0 < (w + (τ : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith
    simpa using
      hasDerivAt_logGamma_sub_logGammaStirling_comp ((hasDerivAt_id (τ : ℂ)).const_add w) hre
  have hint : IntervalIntegrable
      (fun τ : ℝ ↦ -(digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))) volume 0 (n : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    exact ((integrableOn_digammaRemainderIoi_shift hM hw).mono_set Set.Ioc_subset_Ioi_self).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at hFTC
  simp only [Complex.ofReal_natCast, Complex.ofReal_zero, add_zero] at hFTC
  linear_combination hFTC

/-- The Bernoulli tail of the Stirling series vanishes at `+∞`. -/
private theorem tendsto_bernoulli_tail {M : ℕ} :
    Tendsto (fun x : ℝ ↦ ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℝ) / (2 * k * (2 * k - 1)) * x ^ (1 - 2 * (k : ℤ))) atTop (𝓝 0) := by
  rw [show (0 : ℝ) = ∑ k ∈ Finset.Icc 1 M, (0 : ℝ) by simp]
  apply tendsto_finsetSum
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hlt : (1 - 2 * (k : ℤ)) < 0 := by lia
  simpa using (tendsto_zpow_atTop_zero hlt).const_mul
    ((bernoulli (2 * k) : ℝ) / (2 * k * (2 * k - 1)))

/-- The Stirling approximant at a positive real argument is a real number. -/
private theorem logGammaStirling_ofReal {M : ℕ} {x : ℝ} (hx : 0 < x) :
    logGammaStirling M (x : ℂ)
      = ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)
          + ∑ k ∈ Finset.Icc 1 M,
              (bernoulli (2 * k) : ℝ) / (2 * k * (2 * k - 1)) * x ^ (1 - 2 * (k : ℤ)) : ℂ) := by
  rw [logGammaStirling]
  push_cast [Complex.ofReal_log hx.le, Complex.ofReal_zpow]
  ring

/-- **Real-axis limit.** `g(x) → 0` as real `x → +∞`. -/
private theorem tendsto_g_ofReal_atTop {M : ℕ} :
    Tendsto (fun x : ℝ ↦ logGamma (x : ℂ) - logGammaStirling M (x : ℂ)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ ↦ Real.log (Real.Gamma x)
      - ((x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π))
      - ∑ k ∈ Finset.Icc 1 M,
          (bernoulli (2 * k) : ℝ) / (2 * k * (2 * k - 1)) * x ^ (1 - 2 * (k : ℤ)))
      atTop (𝓝 0) := by
    simpa [Real.Stirling.stirlingRef] using
      Real.Stirling.tendsto_log_Gamma_sub_stirlingRef_atTop.sub tendsto_bernoulli_tail
  refine (hreal.ofReal).congr' ?_ |>.mono_right (by simp)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [logGamma_ofReal hx, logGammaStirling_ofReal hx]
  push_cast
  ring

/-- **Vertical transfer.** `g(w+n) → 0` as `n → ∞`, where `g = logGamma - S_M`. -/
private theorem tendsto_g_shift_atTop {M : ℕ} (hM : 1 ≤ M) {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun n : ℕ ↦ logGamma (w + n) - logGammaStirling M (w + n)) atTop (𝓝 0) := by
  set C : ℝ := ((2 * M + 1)! : ℝ) / (2 * π) ^ (2 * M)
  have hbn : Tendsto (fun n : ℕ ↦ C * (w.re + (n : ℝ)) ^ (-(2 * M + 1 : ℤ)) * |w.im|)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ (w.re + (n : ℝ)) ^ (-(2 * M + 1 : ℤ))) atTop (𝓝 0) :=
      (tendsto_zpow_atTop_zero (show (-(2 * M + 1 : ℤ)) < 0 by lia)).comp
        (tendsto_atTop_add_const_left atTop w.re tendsto_natCast_atTop_atTop)
    simpa using (h1.const_mul C).mul_const |w.im|
  have hreal : Tendsto (fun n : ℕ ↦
      logGamma ((w.re + (n : ℝ) : ℝ) : ℂ) - logGammaStirling M ((w.re + (n : ℝ) : ℝ) : ℂ))
      atTop (𝓝 0) :=
    tendsto_g_ofReal_atTop.comp
      (tendsto_atTop_add_const_left atTop w.re tendsto_natCast_atTop_atTop)
  have htrans : Tendsto (fun n : ℕ ↦
      (logGamma (w + n) - logGammaStirling M (w + n))
        - (logGamma ((w.re + (n : ℝ) : ℝ) : ℂ)
          - logGammaStirling M ((w.re + (n : ℝ) : ℝ) : ℂ))) atTop (𝓝 0) := by
    refine squeeze_zero_norm ?_ hbn
    intro n
    set b : ℝ := w.re + (n : ℝ) with hb
    have hbpos : 0 < b := by rw [hb]; positivity
    have hre_eq : ∀ y : ℝ, ((b : ℂ) + (y : ℂ) * Complex.I).re = b := fun y ↦ by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    have hre : ∀ y : ℝ, 0 < ((b : ℂ) + (y : ℂ) * Complex.I).re := fun y ↦ by
      rw [hre_eq y]; exact hbpos
    have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) w.im,
        HasDerivAt (fun t : ℝ ↦ logGamma ((b : ℂ) + (t : ℂ) * Complex.I)
            - logGammaStirling M ((b : ℂ) + (t : ℂ) * Complex.I))
          (-(digammaRemainderIoi ((b : ℂ) + (y : ℂ) * Complex.I) (2 * M + 1)) * Complex.I) y := by
      intro y _
      have haff : HasDerivAt (fun z : ℂ ↦ (b : ℂ) + z * Complex.I) Complex.I (y : ℂ) := by
        simpa using ((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (b : ℂ)
      simpa using hasDerivAt_logGamma_sub_logGammaStirling_comp haff (hre y)
    have hcont : Continuous (fun y : ℝ ↦
        -(digammaRemainderIoi ((b : ℂ) + (y : ℂ) * Complex.I) (2 * M + 1)) * Complex.I) := by
      rw [continuous_iff_continuousAt]
      intro y
      exact ((continuousAt_digammaRemainderIoi_comp
        ((Complex.continuous_ofReal.mul continuous_const).const_add (b : ℂ)).continuousAt
        (hre y)).neg).mul continuousAt_const
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
    have hend1 : (b : ℂ) + (w.im : ℂ) * Complex.I = w + n := by
      rw [hb]; push_cast; linear_combination Complex.re_add_im w
    have hend0 : (b : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = ((w.re + (n : ℝ) : ℝ) : ℂ) := by
      rw [hb]; push_cast; ring
    rw [hend1, hend0] at hFTC
    rw [← hFTC, show |w.im| = |w.im - 0| by rw [sub_zero]]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y _
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg]
    have hbnd := norm_digammaRemainderIoi_le_re hM (hre y)
    have hbz : b ^ (-(2 * M + 1 : ℝ)) = b ^ (-(2 * M + 1 : ℤ)) := by
      rw [show (-(2 * M + 1 : ℝ)) = ((-(2 * M + 1 : ℤ) : ℤ) : ℝ) by push_cast; ring,
        Real.rpow_intCast]
    rw [hre_eq y, hbz] at hbnd
    exact hbnd
  simpa using htrans.add hreal

/-- **Euler–Maclaurin/Stirling expansion of `log Γ`.** For every `M ≥ 1` and every `w` with
`Re w > 0`, `Log Γ(w) = S_M(w) + ρ_M(w)`. -/
theorem logGamma_eq_stirling_add_remainder {M : ℕ} (hM : 1 ≤ M) {w : ℂ} (hw : 0 < w.re) :
    logGamma w = logGammaStirling M w + logGammaRemainderIoi M w := by
  have hconst : ∀ n : ℕ,
      logGamma w - logGammaStirling M w
        = (∫ τ in (0 : ℝ)..(n : ℝ), digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))
          + (logGamma (w + n) - logGammaStirling M (w + n)) := by
    intro n
    have h := logGamma_sub_logGammaStirling_shift_eq_integral hM hw n
    linear_combination h
  have htend1 : Tendsto
      (fun n : ℕ ↦ ∫ τ in (0 : ℝ)..(n : ℝ), digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))
      atTop (𝓝 (logGammaRemainderIoi M w)) := by
    have h := intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_digammaRemainderIoi_shift hM hw) tendsto_natCast_atTop_atTop
    rwa [logGammaRemainderIoi]
  have htend : Tendsto
      (fun n : ℕ ↦ (∫ τ in (0 : ℝ)..(n : ℝ), digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1))
          + (logGamma (w + n) - logGammaStirling M (w + n)))
      atTop (𝓝 (logGammaRemainderIoi M w + 0)) := htend1.add (tendsto_g_shift_atTop hM hw)
  have hlim : Tendsto (fun _ : ℕ ↦ logGamma w - logGammaStirling M w) atTop
      (𝓝 (logGammaRemainderIoi M w + 0)) := htend.congr fun n ↦ (hconst n).symm
  have hEq : logGamma w - logGammaStirling M w = logGammaRemainderIoi M w + 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  rw [add_zero] at hEq
  linear_combination hEq

end Complex.Stirling
