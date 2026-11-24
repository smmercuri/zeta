/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Euler's integral with a complex rate

Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi` evaluates `∫_0^∞ t^{a-1} e^{-rt} dt` as
`(1/r)^a Γ(a)` only for a *real* rate `r > 0`. This file extends it to a *complex* rate `b` with
`Re b > 0` (`riemann_siegel_zero.tex`, `lem:rsz_gamma_cplx`).

## Main results

* `Real.integrableOn_rpow_mul_exp_neg_mul_Ioi`: the real majorant `t^c e^{-δt}` is integrable;
* `Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi`: absolute convergence for `Re b > 0`;
* `Complex.integral_cpow_mul_exp_neg_mul_Ioi'`: `∫_0^∞ t^{a-1} e^{-bt} dt = (1/b)^a Γ(a)`, the
  strict generalisation of `Complex.integral_cpow_mul_exp_neg_mul_Ioi` to a complex rate;
* `Complex.integral_cpow_neg_mul_exp_neg_mul_Ioi`: the reindexed form
  `∫_0^∞ ρ^{-s} e^{-bρ} dρ = Γ(1-s) b^{s-1}`;
* `Real.integral_rpow_neg_mul_exp_neg_mul_Ioi`: its real counterpart
  `∫_0^∞ ρ^{-c} e^{-rρ} dρ = Γ(1-c) r^{c-1}`.
-/
@[expose] public section


open Filter MeasureTheory Set Topology

open scoped Real

namespace Real

/-- The real majorant of Euler's integrand, `t ↦ t^c e^{-δt}`, is integrable on `(0, ∞)` for
`c > -1` and `δ > 0`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {c δ : ℝ} (hc : -1 < c) (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ ↦ t ^ c * exp (-δ * t)) (Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_rpow hc one_pos hδ

end Real

namespace Complex

/-- Euler's integrand with a complex rate is absolutely integrable on `(0, ∞)` when the rate has
positive real part. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (a - 1) * exp (-(b * t))) (Ioi 0) := by
  refine (Real.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : (-1 : ℝ) < a.re - 1) hb).mono'
    (ContinuousOn.aestronglyMeasurable (ContinuousOn.mul (fun t ht ↦ ?_) (by fun_prop))
      measurableSet_Ioi) ?_
  · exact (continuousAt_ofReal_cpow_const t (a - 1) (Or.inr (mem_Ioi.1 ht).ne')).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (mem_Ioi.1 ht), norm_exp]
    simp [mul_re, neg_mul]

/-- **Euler's integral with a complex rate.** -/
theorem integral_cpow_mul_exp_neg_mul_Ioi' {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (a - 1) * exp (-(b * t)) = (1 / b) ^ a * Gamma a := by
  set F : ℂ → ℂ := fun z ↦ ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (a - 1) * exp (-(z * t)) with hF
  set G : ℂ → ℂ := fun z ↦ (1 / z) ^ a * Gamma a with hG
  have hUopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  -- differentiation under the integral sign, uniformly on a ball where `Re z ≥ (Re z₀)/2`
  have hFdiff : ∀ z ∈ {z : ℂ | 0 < z.re}, DifferentiableAt ℂ F z := by
    intro b₀ hb₀
    have hb₀' : 0 < b₀.re := hb₀
    have hδ : 0 < b₀.re / 2 := by positivity
    have hball : ∀ z ∈ Metric.ball b₀ (b₀.re / 2), b₀.re / 2 ≤ z.re := by
      intro z hz
      have h1 : |(z - b₀).re| ≤ ‖z - b₀‖ := abs_re_le_norm _
      have h2 : ‖z - b₀‖ < b₀.re / 2 := by simpa [dist_eq] using hz
      have h3 : |z.re - b₀.re| < b₀.re / 2 := by simpa [sub_re] using h1.trans_lt h2
      linarith [(abs_lt.1 h3).1]
    have hbound := Real.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith : (-1 : ℝ) < a.re) hδ
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure ℝ).restrict (Ioi 0))
      (F := fun (z : ℂ) (t : ℝ) ↦ (t : ℂ) ^ (a - 1) * exp (-(z * t)))
      (F' := fun (z : ℂ) (t : ℝ) ↦ -(t : ℂ) * ((t : ℂ) ^ (a - 1) * exp (-(z * t))))
      (x₀ := b₀) (bound := fun t : ℝ ↦ t ^ a.re * Real.exp (-(b₀.re / 2) * t))
      (Metric.ball_mem_nhds b₀ hδ)
      (eventually_of_mem (Metric.ball_mem_nhds b₀ hδ) fun z hz ↦
        MeasureTheory.Integrable.aestronglyMeasurable
          (integrableOn_cpow_mul_exp_neg_mul_Ioi ha (lt_of_lt_of_le hδ (hball z hz))))
      (integrableOn_cpow_mul_exp_neg_mul_Ioi ha hb₀')
      (continuous_ofReal.neg.aestronglyMeasurable.mul
        (integrableOn_cpow_mul_exp_neg_mul_Ioi ha hb₀').aestronglyMeasurable)
      ?_ hbound ?_
    · exact key.2.differentiableAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht0 : (0 : ℝ) < t := mem_Ioi.1 ht
      have h1 : t * t ^ (a.re - 1) = t ^ a.re := by
        rw [mul_comm, ← Real.rpow_add_one ht0.ne']
        congr 1
        ring
      have h2 : (-(z * (t : ℂ))).re = -(z.re * t) := by simp [mul_re]
      rw [norm_mul, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos ht0,
        norm_cpow_eq_rpow_re_of_pos ht0, norm_exp, h2, sub_re, one_re, ← mul_assoc, h1]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg ht0.le _)
      rw [neg_mul]
      exact neg_le_neg (mul_le_mul_of_nonneg_right (hball z hz) ht0.le)
    · filter_upwards with t z _
      have h0 : HasDerivAt (fun z : ℂ ↦ z * (t : ℂ)) ((t : ℂ)) z := by
        simpa using (hasDerivAt_id z).mul_const ((t : ℂ))
      exact ((h0.neg.cexp).const_mul ((t : ℂ) ^ (a - 1))).congr_deriv
        (by simp only [Pi.neg_apply]; ring)
  have hGdiff : ∀ z ∈ {z : ℂ | 0 < z.re}, DifferentiableAt ℂ G z := by
    intro b₀ hb₀
    have hb₀' : 0 < b₀.re := hb₀
    have hne : b₀ ≠ 0 := fun h ↦ by simp [h] at hb₀'
    have hslit : (1 / b₀) ∈ slitPlane := by
      refine mem_slitPlane_iff.2 (Or.inl ?_)
      rw [one_div, inv_re]
      exact div_pos hb₀' (normSq_pos.2 hne)
    exact ((differentiableAt_const 1 |>.div differentiableAt_id hne).cpow_const hslit).mul_const _
  have hFan : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz ↦ (hFdiff z hz).differentiableWithinAt) hUopen
  have hGan : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz ↦ (hGdiff z hz).differentiableWithinAt) hUopen
  -- the two sides already agree on the positive reals `1 + ε/2`, which accumulate at `1`
  have hone : (1 : ℂ) = ((1 : ℝ) : ℂ) := by norm_num
  have hagree : ∃ᶠ z in 𝓝[≠] (1 : ℂ), F z = G z := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [mem_nhdsWithin] at hs
    obtain ⟨u, huopen, h1u, hus⟩ := hs
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 huopen 1 h1u
    have hr : (0 : ℝ) < 1 + ε / 2 := by linarith
    refine ⟨((1 + ε / 2 : ℝ) : ℂ), hus ⟨hball ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, hone, dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs,
        show (1 + ε / 2 - 1 : ℝ) = ε / 2 by ring, abs_of_pos (by linarith)]
      linarith
    · simp only [mem_compl_iff, mem_singleton_iff, hone, ofReal_inj]
      intro hcon
      linarith
    · simp only [hF, hG]
      exact integral_cpow_mul_exp_neg_mul_Ioi ha hr
  exact hFan.eqOn_of_preconnected_of_frequently_eq hGan
    (convex_halfSpace_re_gt 0).isPreconnected (by simp) hagree hb

/-- **Euler's integral with a complex rate, reindexed**, with the principal branch of the power
(`riemann_siegel_zero.tex`, `lem:rsz_gamma_cplx`). -/
theorem integral_cpow_neg_mul_exp_neg_mul_Ioi {s b : ℂ} (hs : s.re < 1) (hb : 0 < b.re) :
    ∫ ρ : ℝ in Ioi 0, (ρ : ℂ) ^ (-s) * exp (-(b * ρ)) = Gamma (1 - s) * b ^ (s - 1) := by
  have ha : 0 < (1 - s).re := by simpa using hs
  have harg : b.arg ≠ π := fun h ↦ absurd (arg_eq_pi_iff.1 h).1 (not_lt.2 hb.le)
  have hpow : (1 / b) ^ (1 - s) = b ^ (s - 1) := by
    rw [one_div, inv_cpow _ _ harg, ← cpow_neg, neg_sub]
  calc ∫ ρ : ℝ in Ioi 0, (ρ : ℂ) ^ (-s) * exp (-(b * ρ))
      = (1 / b) ^ (1 - s) * Gamma (1 - s) := by
        simpa only [show (1 - s) - 1 = -s by ring] using integral_cpow_mul_exp_neg_mul_Ioi' ha hb
    _ = Gamma (1 - s) * b ^ (s - 1) := by rw [hpow]; ring

end Complex

namespace Real

/-- **Euler's integral in real form**, the real counterpart of
`Complex.integral_cpow_neg_mul_exp_neg_mul_Ioi`. -/
theorem integral_rpow_neg_mul_exp_neg_mul_Ioi {c r : ℝ} (hc : c < 1) (hr : 0 < r) :
    ∫ ρ in Ioi (0 : ℝ), ρ ^ (-c) * exp (-(r * ρ)) = Gamma (1 - c) * r ^ (c - 1) := by
  have hint : ∫ ρ in Ioi (0 : ℝ), (ρ : ℂ) ^ (-(c : ℂ)) * Complex.exp (-((r : ℂ) * ρ))
      = ((∫ ρ in Ioi (0 : ℝ), ρ ^ (-c) * exp (-(r * ρ)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ ?_
    have hρ0 : (0 : ℝ) < ρ := hρ
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hρ0.le, Complex.ofReal_exp]
    push_cast
    ring
  have h := Complex.integral_cpow_neg_mul_exp_neg_mul_Ioi (s := (c : ℂ)) (b := (r : ℂ))
    (by simpa using hc) (by simpa using hr)
  rw [hint, show (1 : ℂ) - (c : ℂ) = ((1 - c : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    show (c : ℂ) - 1 = ((c - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hr.le,
    ← Complex.ofReal_mul] at h
  exact_mod_cast h

end Real
