/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Zeta.Analysis.Complex.ArgumentPrinciple
public import Zeta.Theta
public import Zeta.ArgZeta.Basic
public import Zeta.ArgZeta.NewtonKernel

/-!
# Littlewood's reduction

Littlewood's reduction (`lem:lb_littlewood`) of the integral of `S(t)` to the log-modulus line
integral `I(t) = ∫_{1/2}^∞ log|ζ(σ+it)| dσ`, together with its building blocks. Throughout, the
logarithmic derivative `G = ζ'/ζ` is `logDeriv riemannZeta`.

## Main results

- `finite_riemannZeta_zeros_rectangle` (`lem:lb_finite_ordinates`): the zeros of `ζ` in a closed
  rectangle lying in the open upper half-plane are finite; `finite_re_riemannZeta_zeros_rectangle`
  and `finite_im_riemannZeta_zeros_rectangle` give the same for their abscissae and ordinates.
- `log_norm_riemannZeta_sub_eq_neg_im_integral` (`lem:lb_logNorm_diff`): along a zero-free
  vertical segment, `log|ζ(σ+it₂)| - log|ζ(σ+it₁)| = -Im ∫_{t₁}^{t₂} G(σ+it) dt`.
- `argVariation_riemannZeta_horizontal_eq_im_integral` (`lem:lb_horiz_argVar`): along a zero-free
  horizontal segment, the argument variation of `ζ` equals `Im ∫_{1/2}^{X} G(σ+it) dσ`.
- `integrableOn_logDeriv_riemannZeta_rectangle`,
  `integrableOn_im_logDeriv_riemannZeta_rectangle` (`lem:lb_logDeriv_integrable`): `G` is
  integrable on a rectangle in the open upper half-plane.
- `tendsto_argVariation_riemannZeta_horizontal_atTop` (`lem:lb_horiz_argVar_limit`): for `t > 0`
  with a zero-free ray, the horizontal argument variation from `1/2` to `X` tends to
  `-π · argZeta t` as `X → ∞`.
- `pi_mul_integral_argZeta_eq_sub` (`lem:lb_littlewood`): `π ∫_{t₁}^{t₂} S(t) dt = I(t₂) - I(t₁)`
  for `0 < t₁ < t₂` with zero-free rays, where `S = argZeta` and `I = logNormZetaIntegral`.
-/
@[expose] public section


open Complex MeasureTheory Metric Set Filter Topology

/-- `riemannZeta` is analytic on the open set `{s | s ≠ 1}`. -/
private theorem analyticOnNhd_riemannZeta_ne_one :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_ne

/-- The derivative `ζ'` is analytic on the open set `{s | s ≠ 1}`. -/
private theorem analyticOnNhd_deriv_riemannZeta_ne_one :
    AnalyticOnNhd ℂ (deriv riemannZeta) {s : ℂ | s ≠ 1} :=
  fun s hs ↦ (analyticOnNhd_riemannZeta_ne_one s hs).deriv

/-- `riemannZeta` is analytic on the open upper half-plane `{s | 0 < s.im}`. -/
private theorem analyticOnNhd_riemannZeta_upperHalfPlane :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | 0 < s.im} :=
  DifferentiableOn.analyticOnNhd (fun s hs ↦
    (differentiableAt_riemannZeta (by rintro rfl; simp at hs)).differentiableWithinAt)
    (isOpen_lt continuous_const continuous_im)

/-- The open upper half-plane is connected. -/
private theorem isConnected_upperHalfPlane : IsConnected {s : ℂ | 0 < s.im} :=
  (convex_halfSpace_im_gt 0).isConnected ⟨I, by simp⟩

/-- A closed rectangle with both corners in the open upper half-plane lies in the open upper
half-plane. -/
private theorem im_pos_of_mem_rectangle {z w s : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (hs : s ∈ Rectangle z w) : 0 < s.im := by
  simp only [Rectangle, mem_reProdIm, mem_uIcc] at hs
  rcases hs.2 with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith

/-- The row map `σ ↦ ζ(σ + it)` is continuous whenever `t ≠ 0`. -/
private theorem continuous_riemannZeta_horizontal {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
  analyticOnNhd_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
    (fun σ h ↦ ht (by simpa using congrArg Complex.im h))

/-- The column map `τ ↦ ζ(x + iτ)` is continuous whenever `x ≠ 1`. -/
private theorem continuous_riemannZeta_vertical {x : ℝ} (hx : x ≠ 1) :
    Continuous (fun τ : ℝ ↦ riemannZeta ((x : ℂ) + I * (τ : ℂ))) :=
  analyticOnNhd_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
    (fun τ h ↦ hx (by simpa using congrArg Complex.re h))

/-- A point `σ + it` on a horizontal line with `t ≠ 0` avoids the pole `s = 1`. -/
private theorem ofReal_add_I_mul_ne_one {σ t : ℝ} (ht : t ≠ 0) :
    (σ : ℂ) + I * (t : ℂ) ≠ 1 := fun h ↦ ht (by simpa using congrArg Complex.im h)

/-- **Finiteness of the zeros of `ζ` in a rectangle** (`lem:lb_finite_ordinates`). If the closed
rectangle `Rectangle z w` lies in the open upper half-plane (`0 < z.im` and `0 < w.im`), then the
set of zeros of `riemannZeta` in it is finite. -/
theorem finite_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Rectangle z w ∩ {ρ | riemannZeta ρ = 0}).Finite :=
  finite_rectangle_inter_setOf_eq_zero analyticOnNhd_riemannZeta_upperHalfPlane
    isConnected_upperHalfPlane (fun _ hρ ↦ im_pos_of_mem_rectangle hz hw hρ) (z₀ := 2 + I) (by simp)
    (riemannZeta_ne_zero_of_one_le_re (by simp))

/-- The abscissae of the zeros of `ζ` in a rectangle in the open upper half-plane form a finite
set (`lem:lb_finite_ordinates`). -/
theorem finite_re_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Complex.re '' (Rectangle z w ∩ {ρ | riemannZeta ρ = 0})).Finite :=
  (finite_riemannZeta_zeros_rectangle hz hw).image _

/-- The ordinates of the zeros of `ζ` in a rectangle in the open upper half-plane form a finite
set (`lem:lb_finite_ordinates`). -/
theorem finite_im_riemannZeta_zeros_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (Complex.im '' (Rectangle z w ∩ {ρ | riemannZeta ρ = 0})).Finite :=
  (finite_riemannZeta_zeros_rectangle hz hw).image _

/-- Membership of `σ + it` in a positively oriented closed rectangle: it suffices that each
coordinate lies in the corresponding coordinate interval of the corners. -/
private theorem ofReal_add_I_mul_mem_rectangle {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {σ t : ℝ} (hσ : σ ∈ Icc z.re w.re) (ht : t ∈ Icc z.im w.im) :
    ((σ : ℂ) + I * (t : ℂ)) ∈ Rectangle z w := by
  rw [Rectangle, mem_reProdIm, Set.uIcc_of_le hre, Set.uIcc_of_le him]
  exact ⟨by simpa using hσ, by simpa using ht⟩

/-- A point `σ + it` with `1/2 ≤ σ ≤ 1` and `t ∈ [t₁, t₂]` lies in the closed rectangle
`[1/2, 2] × [t₁, t₂]`, the box confining the zeros of `ζ` on the ray `σ ≥ 1/2`. -/
private theorem ofReal_add_I_mul_mem_rectangle_two {t₁ t₂ σ t : ℝ} (h12 : t₁ ≤ t₂)
    (hσ : (1 / 2 : ℝ) ≤ σ) (hσ1 : σ ≤ 1) (ht : t ∈ Set.Icc t₁ t₂) :
    ((σ : ℂ) + I * (t : ℂ)) ∈ Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ)) :=
  ofReal_add_I_mul_mem_rectangle (by norm_num) (by simpa using h12)
    (by simp only [mem_Icc]; norm_num; constructor <;> linarith) (by simpa using ht)

/-- A zero of `ζ` on the ray `σ + it` has abscissa `σ ≤ 1`. -/
private theorem re_le_one_of_riemannZeta_eq_zero {σ t : ℝ}
    (hz : riemannZeta ((σ : ℂ) + I * t) = 0) : σ ≤ 1 :=
  not_lt.mp fun h ↦ riemannZeta_ne_zero_of_one_le_re (by simpa using h.le) hz

/-- If `t ∈ [t₁, t₂]` is not the ordinate of any zero of `ζ` in the box `[1/2, 2] × [t₁, t₂]`,
then the whole ray `{σ + it : σ ≥ 1/2}` is zero-free. -/
private theorem riemannZeta_ray_ne_zero_of_not_mem_im_zeros {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) {t : ℝ}
    (ht : t ∈ Set.Icc t₁ t₂)
    (htbad : t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
      ∩ {ρ | riemannZeta ρ = 0})) :
    ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0 := fun σ hσ hzero ↦
  htbad ⟨(σ : ℂ) + I * (t : ℂ),
    ⟨ofReal_add_I_mul_mem_rectangle_two h12 hσ (re_le_one_of_riemannZeta_eq_zero hzero) ht,
      hzero⟩, by simp⟩

/-- `riemannZeta` is not eventually zero at any point of the open upper half-plane. -/
private theorem not_eventually_riemannZeta_eq_zero {x : ℂ} (hx : 0 < x.im) :
    ¬ ∀ᶠ z in 𝓝 x, riemannZeta z = 0 := fun hev ↦
  riemannZeta_ne_zero_of_one_le_re (s := 2 + I) (by simp)
    (analyticOnNhd_riemannZeta_upperHalfPlane.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isConnected_upperHalfPlane.isPreconnected hx hev (by simp))

/-- The function `s ↦ c / (s - ρ)` is integrable on the closed disk `closedBall ρ r`. -/
private theorem integrableOn_const_div_sub_closedBall (c ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℂ ↦ c / (s - ρ)) (closedBall ρ r) := by
  refine Integrable.mono' ((integrableOn_inv_norm_sub_closedBall ρ hr).const_mul ‖c‖)
    (measurable_const.div (measurable_id.sub measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s ↦ ?_)
  rw [norm_div, div_eq_mul_inv]

/-- **Local integrability of `ζ'/ζ`.** For `x` in the open upper half-plane, `logDeriv ζ` is
integrable on some closed disk around `x`. -/
private theorem exists_integrableOn_logDeriv_riemannZeta_closedBall {x : ℂ} (hx : 0 < x.im) :
    ∃ r > 0, IntegrableOn (logDeriv riemannZeta) (closedBall x r) := by
  have hax : AnalyticAt ℂ riemannZeta x :=
    analyticOnNhd_riemannZeta_ne_one x (by rintro rfl; simp at hx)
  by_cases hzero : riemannZeta x = 0
  · -- simple pole: residue decomposition `ζ'/ζ = n/(·-x) + logDeriv g`
    obtain ⟨n, g, -, -, -, hlogg, heq⟩ :=
      meromorphicOrderAt_eq_residue_logDeriv hax (not_eventually_riemannZeta_eq_zero hx)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      ((eventually_nhdsWithin_iff.mp heq).and hlogg.eventually_analyticAt)
    have hlt : ∀ {z : ℂ}, z ∈ closedBall x (ε / 2) → dist z x < ε := fun {z} hz ↦
      lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)
    refine ⟨ε / 2, half_pos hε, Integrable.congr
      ((integrableOn_const_div_sub_closedBall (n : ℂ) x (half_pos hε).le).add
        (ContinuousOn.integrableOn_compact (isCompact_closedBall x (ε / 2))
          fun _ hz ↦ (hball (hlt hz)).2.continuousAt.continuousWithinAt)) ?_⟩
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton x)),
      ae_restrict_mem measurableSet_closedBall] with z hzne hzmem
    exact ((hball (hlt hzmem)).1 hzne).symm
  · -- regular point: `ζ'/ζ` continuous on a small disk
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      (hax.eventually_analyticAt.and (hax.continuousAt.eventually_ne hzero))
    refine ⟨ε / 2, half_pos hε, ContinuousOn.integrableOn_compact
      (isCompact_closedBall x (ε / 2)) fun z hz ↦ ?_⟩
    obtain ⟨haz, hzne⟩ := hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith))
    exact (haz.deriv.div haz hzne).continuousAt.continuousWithinAt

/-- **Integrability of `ζ'/ζ` on a rectangle** (`lem:lb_logDeriv_integrable`). If the closed
rectangle `Rectangle z w` lies in the open upper half-plane, then `logDeriv ζ = ζ'/ζ` is integrable
on it, despite its poles at the zeros of `ζ`. -/
theorem integrableOn_logDeriv_riemannZeta_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (logDeriv riemannZeta) (Rectangle z w) := by
  refine LocallyIntegrableOn.integrableOn_isCompact ?_ (isCompact_uIcc.reProdIm isCompact_uIcc)
  intro x hx
  obtain ⟨r, hr, hint⟩ :=
    exists_integrableOn_logDeriv_riemannZeta_closedBall (im_pos_of_mem_rectangle hz hw hx)
  exact ⟨closedBall x r, nhdsWithin_le_nhds (closedBall_mem_nhds x hr), hint⟩

/-- **Integrability of `Im(ζ'/ζ)` on a rectangle** in the open upper half-plane
(`lem:lb_logDeriv_integrable`). This is the form fed to Fubini in Littlewood's reduction. -/
theorem integrableOn_im_logDeriv_riemannZeta_rectangle {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    IntegrableOn (fun s : ℂ ↦ (logDeriv riemannZeta s).im) (Rectangle z w) :=
  (integrableOn_logDeriv_riemannZeta_rectangle hz hw).im

/-- **Telescoping of `log|ζ|` along a vertical segment** (`lem:lb_logNorm_diff`). For
`0 < t₁ ≤ t₂` such that the vertical segment `{σ+it : t ∈ [t₁,t₂]}` is zero-free,
`log|ζ(σ+it₂)| - log|ζ(σ+it₁)| = -Im ∫_{t₁}^{t₂} (ζ'/ζ)(σ+it) dt`. -/
theorem log_norm_riemannZeta_sub_eq_neg_im_integral {σ t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂) (ht1 : 0 < t₁)
    (hne : ∀ t ∈ Icc t₁ t₂, riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖ - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖
      = -(∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hpathcont : Continuous (fun t : ℝ ↦ (σ : ℂ) + I * t) := by fun_prop
  have hmaps : MapsTo (fun t : ℝ ↦ (σ : ℂ) + I * t) (Icc t₁ t₂) {s : ℂ | s ≠ 1} :=
    fun t ht ↦ ofReal_add_I_mul_ne_one (ht1.trans_le ht.1).ne'
  have hderiv : ∀ t ∈ Ioo t₁ t₂,
      HasDerivAt (fun t : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))
        (deriv riemannZeta ((σ : ℂ) + I * t) * I) t := fun t ht ↦
    ((analyticOnNhd_riemannZeta_ne_one _
      (ofReal_add_I_mul_ne_one (ht1.trans_le ht.1.le).ne')).differentiableAt.hasDerivAt).comp t
      (by simpa using ((ofRealCLM.hasDerivAt (x := t)).const_mul I).const_add (σ : ℂ))
  have hφcont : ContinuousOn (fun t : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) (Icc t₁ t₂) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp hpathcont.continuousOn hmaps
  have heq : (fun t : ℝ ↦ deriv riemannZeta ((σ : ℂ) + I * t) * I / riemannZeta ((σ : ℂ) + I * t))
      = fun t : ℝ ↦ logDeriv riemannZeta ((σ : ℂ) + I * t) * I :=
    funext fun t ↦ by rw [logDeriv_apply, mul_div_right_comm]
  have h := re_integral_div_eq_log_norm_sub h12 hφcont hne hderiv
    (((analyticOnNhd_deriv_riemannZeta_ne_one.continuousOn.comp hpathcont.continuousOn hmaps).mul
      continuousOn_const).div hφcont hne)
  rw [heq, intervalIntegral.integral_mul_const, mul_I_re] at h
  linarith

/-- **Horizontal argument variation as an imaginary integral** (`lem:lb_horiz_argVar`). For
`a ≤ X` and `t ≠ 0` such that the horizontal segment `{σ+it : σ ∈ [a,X]}` is zero-free, the
argument variation of `ζ` along it equals `Im ∫_{a}^{X} (ζ'/ζ)(σ+it) dσ`. -/
theorem argVariation_riemannZeta_horizontal_eq_im_integral {a X t : ℝ} (hX : a ≤ X) (ht : t ≠ 0)
    (hne : ∀ σ ∈ Icc a X, riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    argVariation a X (fun σ ↦ riemannZeta ((σ : ℂ) + I * t))
      = (∫ σ in a..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  have hφcont : ContinuousOn (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) (Icc a X) :=
    (continuous_riemannZeta_horizontal ht).continuousOn
  have hdcont : Continuous (fun σ : ℝ ↦ deriv riemannZeta ((σ : ℂ) + I * t)) :=
    analyticOnNhd_deriv_riemannZeta_ne_one.continuousOn.comp_continuous (by fun_prop)
      (fun _ ↦ ofReal_add_I_mul_ne_one ht)
  have hderiv : ∀ σ ∈ Ioo a X,
      HasDerivAt (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))
        (deriv riemannZeta ((σ : ℂ) + I * t)) σ := fun σ _ ↦ by
    have h1 : HasDerivAt (fun σ : ℝ ↦ (σ : ℂ) + I * t) 1 σ := by
      simpa using (ofRealCLM.hasDerivAt (x := σ)).add_const (I * (t : ℂ))
    have hd := ((analyticOnNhd_riemannZeta_ne_one _
      (ofReal_add_I_mul_ne_one ht)).differentiableAt.hasDerivAt).comp σ h1
    rw [mul_one] at hd; exact hd
  rw [argVariation_eq_im_integral hX hφcont hne hderiv (hdcont.continuousOn.div hφcont hne)]
  simp only [logDeriv_apply]

/-- **Vanishing of the vertical argument variation at `+∞`** (`lem:lb_argVar_vertical`). For fixed
`t`, the argument variation of `ζ` along the vertical segment `X → X + it` tends to `0` as
`X → +∞`. -/
theorem tendsto_argVariation_riemannZeta_vertical_atTop {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun X : ℝ ↦ argVariation 0 t (fun τ : ℝ ↦ riemannZeta ((X : ℂ) + I * (τ : ℂ))))
      atTop (𝓝 0) := by
  have key : Tendsto (fun X : ℝ ↦ (riemannZeta ((X : ℂ) + I * (t : ℂ))).arg
      - (riemannZeta ((X : ℂ) + I * ((0 : ℝ) : ℂ))).arg) atTop (𝓝 0) := by
    simpa using (tendsto_arg_riemannZeta_atTop t).sub (tendsto_arg_riemannZeta_atTop 0)
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  rw [argVariation_eq_arg_sub_arg ht
    (continuous_riemannZeta_vertical (by linarith)).continuousOn
    (fun τ _ ↦ riemannZeta_mem_slitPlane_of_two_le_re (by simpa using hX))]

/-- For real `σ ≥ 2`, `ζ(σ)` is real and positive, so its principal argument is `0`. -/
private theorem arg_riemannZeta_ofReal_eq_zero {σ : ℝ} (hσ : 2 ≤ σ) :
    (riemannZeta (σ : ℂ)).arg = 0 := by
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ (σ : ℂ)
      = (((1 / ((n : ℝ) + 1) ^ σ : ℝ)) : ℂ) := fun n ↦ by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have him : (riemannZeta (σ : ℂ)).im = 0 := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using (by linarith : (1 : ℝ) < σ)),
      tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_im]
  have hsp := Complex.mem_slitPlane_iff.mp
    (riemannZeta_mem_slitPlane_of_two_le_re (s := (σ : ℂ)) (by simpa using hσ))
  exact Complex.arg_eq_zero_iff.mpr ⟨hsp.elim le_of_lt (absurd him), him⟩

/-- The affine reparametrisation `u ↦ a + u·(b - a)` maps `[0, 1]` into `[a, b]`, for `a ≤ b`. -/
private theorem mem_Icc_affine {a b u : ℝ} (hab : a ≤ b) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    a + u * (b - a) ∈ Set.Icc a b :=
  Set.uIcc_of_le hab ▸ add_mul_sub_mem_uIcc hu

/-- **Reparametrisation of a `ζ`-`lineSeg`.** If `lineSeg P Q u = g (a + u * (b - a))` (`a ≤ b`),
the `lineSeg`-parametrised argument variation of `ζ` along it is the interval-parametrised
variation of `ζ ∘ g` over `[a, b]`. -/
private theorem argVariation_riemannZeta_lineSeg_comp {a b : ℝ} (hab : a ≤ b) {P Q : ℂ}
    {g : ℝ → ℂ} (hg : ∀ u : ℝ, lineSeg P Q u = g (a + u * (b - a)))
    (hcont : ContinuousOn (fun x : ℝ ↦ riemannZeta (g x)) (Set.Icc a b))
    (hne : ∀ x ∈ Set.Icc a b, riemannZeta (g x) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg P Q u))
      = argVariation a b (fun x : ℝ ↦ riemannZeta (g x)) := by
  rw [show (fun u : ℝ ↦ riemannZeta (lineSeg P Q u))
      = fun u : ℝ ↦ (fun x : ℝ ↦ riemannZeta (g x)) (a + u * (b - a)) from
    funext fun u ↦ by rw [hg u]]
  exact argVariation_comp hab zero_le_one (by fun_prop) (fun u hu ↦ mem_Icc_affine hab hu)
    (by ring) (by ring) hcont hne

/-- **Reversal of a `ζ`-`lineSeg`.** Swapping the endpoints of an affine segment negates the
argument variation of `ζ` along it. -/
private theorem argVariation_riemannZeta_lineSeg_symm {z₀ z₁ : ℂ}
    (hcont : ContinuousOn (fun u : ℝ ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc (0 : ℝ) 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannZeta (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₁ z₀ u))
      = - argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) := by
  have hfun : (fun u : ℝ ↦ riemannZeta (lineSeg z₁ z₀ u))
      = (fun u : ℝ ↦ (fun v : ℝ ↦ riemannZeta (lineSeg z₀ z₁ v)) (0 + 1 - u)) := by
    funext u; simp only; congr 1; simp only [lineSeg]; push_cast; ring
  rw [hfun]
  exact argVariation_reverse zero_le_one hcont hne

/-- **Reversed horizontal `ζ`-segment.** The `lineSeg`-parametrised argument variation of `ζ`
along the reversed horizontal segment from `b + it` to `a + it` (`a ≤ b`, `t ≠ 0`, zero-free) is
`-argVariation a b (fun σ ↦ ζ(σ + it))`. -/
private theorem argVariation_riemannZeta_lineSeg_horizontal_rev {a b t : ℝ} (hab : a ≤ b)
    (ht : t ≠ 0) (hrowcont : Continuous fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
    (hne : ∀ σ ∈ Set.Icc a b, riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0) :
    argVariation 0 1
        (fun u ↦ riemannZeta (lineSeg ((b : ℂ) + I * (t : ℂ)) ((a : ℂ) + I * (t : ℂ)) u))
      = - argVariation a b (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
  have heq : ∀ u : ℝ, lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u
      = (((a + u * (b - a) : ℝ)) : ℂ) + I * (t : ℂ) := fun u ↦ by
    simp only [lineSeg]; push_cast; ring
  have hcont : ContinuousOn
      (fun u : ℝ ↦ riemannZeta (lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u))
      (Set.Icc 0 1) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp (continuous_lineSeg _ _).continuousOn
      (fun u _ ↦ by rw [heq u]; exact ofReal_add_I_mul_ne_one ht)
  have hne01 : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannZeta (lineSeg ((a : ℂ) + I * (t : ℂ)) ((b : ℂ) + I * (t : ℂ)) u) ≠ 0 := fun u hu ↦ by
    rw [heq u]; exact hne _ (mem_Icc_affine hab hu)
  rw [argVariation_riemannZeta_lineSeg_symm hcont hne01,
    argVariation_riemannZeta_lineSeg_comp (g := fun σ : ℝ ↦ (σ : ℂ) + I * (t : ℂ)) hab heq
      hrowcont.continuousOn hne]

/-- **`ζ`-argument variation along a `lineSeg` inside `Re s ≥ 2`**: the difference of the endpoint
arguments. -/
private theorem argVariation_riemannZeta_lineSeg_of_two_le_re {z₀ z₁ : ℂ}
    (h : ∀ u ∈ Set.Icc (0 : ℝ) 1, 2 ≤ (lineSeg z₀ z₁ u).re) :
    argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u))
      = (riemannZeta z₁).arg - (riemannZeta z₀).arg := by
  have hcont : ContinuousOn (fun u : ℝ ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc 0 1) :=
    analyticOnNhd_riemannZeta_ne_one.continuousOn.comp (continuous_lineSeg _ _).continuousOn
      fun u hu h1 ↦ by simpa [h1] using h u hu
  rw [argVariation_eq_arg_sub_arg zero_le_one hcont
    fun u hu ↦ riemannZeta_mem_slitPlane_of_two_le_re (h u hu), lineSeg_one, lineSeg_zero]

/-- **Limit of the horizontal argument variation** (`lem:lb_horiz_argVar_limit`). For `t > 0` with
the ray `{σ + it : σ ≥ 1/2}` zero-free, the horizontal argument variation of `ζ` from `1/2` to `X`
tends to `-π S(t) = -π · argZeta t` as `X → ∞`. -/
theorem tendsto_argVariation_riemannZeta_horizontal_atTop {t : ℝ} (ht : 0 < t)
    (hne : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0) :
    Tendsto (fun X : ℝ ↦ argVariation (1 / 2) X
        (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))))
      atTop (𝓝 (-(Real.pi * argZeta t))) := by
  -- `ζ(σ + it)` is continuous in `σ` (the row avoids `s = 1` since `t ≠ 0`).
  have hrowcont : Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
    continuous_riemannZeta_horizontal ht.ne'
  -- `π · argZeta t = argVariationContourL ζ t`.
  have hpi : Real.pi * argZeta t = argVariationContourL riemannZeta t := by
    rw [argZeta, ← mul_assoc, mul_one_div, div_self Real.pi_ne_zero, one_mul]
  -- The right (vertical) edge tends to `0`, so the whole contour value tends to `-π S(t)`.
  have hlim := (tendsto_argVariation_riemannZeta_vertical_atTop ht.le).sub_const
    (Real.pi * argZeta t)
  rw [zero_sub] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  -- The rectangle `[2, X] × [0, t]` has vanishing boundary argument variation.
  have hzero :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (2 : ℂ) (X : ℂ) u))
        + argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (X : ℂ) ((X : ℂ) + I * (t : ℂ)) u))
        + argVariation 0 1 (fun u ↦
            riemannZeta (lineSeg ((X : ℂ) + I * (t : ℂ)) ((2 : ℂ) + I * (t : ℂ)) u))
        + argVariation 0 1 (fun u ↦
            riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) (2 : ℂ) u)) = 0 := by
    have hsub : Rectangle (2 : ℂ) ((X : ℂ) + I * (t : ℂ)) ⊆ {s : ℂ | 1 < s.re} := fun ρ hρ ↦ by
      simp only [Rectangle, mem_reProdIm, mem_uIcc, show (2 : ℂ).re = 2 from by norm_num,
        show ((X : ℂ) + I * (t : ℂ)).re = X from by simp] at hρ
      rcases hρ.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact Set.mem_ofPred.mpr (by linarith)
    have hz0 := rectangleArgVariation_eq_zero_of_analyticOnNhd
      (fun s hs ↦ analyticOnNhd_riemannZeta_ne_one s (by rintro rfl; simp at hs))
      (fun _ hs ↦ riemannZeta_ne_zero_of_one_le_re hs.le) hsub
    rw [rectangleArgVariation] at hz0
    simpa [Complex.re_add_im, mul_comm] using hz0
  -- Bottom edge: on the real axis `[2, X]`, `ζ` is real-positive, so the variation is `0`.
  have hEb : argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (2 : ℂ) (X : ℂ) u)) = 0 := by
    rw [argVariation_riemannZeta_lineSeg_of_two_le_re (fun u hu ↦ by
        simp only [lineSeg_re, Complex.re_ofNat, Complex.ofReal_re]
        nlinarith [mul_nonneg hu.1 (by linarith : (0 : ℝ) ≤ X - 2)]),
      arg_riemannZeta_ofReal_eq_zero hX,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
      arg_riemannZeta_ofReal_eq_zero (le_refl 2), sub_self]
  -- Right edge: reparametrise to the vertical variation `argVariation 0 t (ζ(X + i·))`.
  have hEr0 :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg (X : ℂ) ((X : ℂ) + I * (t : ℂ)) u))
      = argVariation 0 t (fun τ : ℝ ↦ riemannZeta ((X : ℂ) + I * (τ : ℂ))) :=
    argVariation_riemannZeta_lineSeg_comp (g := fun τ : ℝ ↦ (X : ℂ) + I * (τ : ℂ)) ht.le
      (fun u ↦ by simp only [lineSeg]; push_cast; ring)
      (continuous_riemannZeta_vertical (by rintro rfl; norm_num at hX)).continuousOn
      (fun τ _ ↦ riemannZeta_ne_zero_of_one_le_re (by simpa using (by linarith : (1 : ℝ) ≤ X)))
  -- Top edge: reverse + reparametrise to `-argVariation 2 X (ζ(· + it))`.
  have hEt0 :
      argVariation 0 1
          (fun u ↦ riemannZeta (lineSeg ((X : ℂ) + I * (t : ℂ)) ((2 : ℂ) + I * (t : ℂ)) u))
      = - argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
    rw [show ((2 : ℂ) + I * (t : ℂ)) = (((2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num]
    exact argVariation_riemannZeta_lineSeg_horizontal_rev hX ht.ne' hrowcont
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  -- Left edge: both orientations stay on `Re s = 2`, so they are opposite endpoint differences.
  have hEl0 :
      argVariation 0 1 (fun u ↦ riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) (2 : ℂ) u))
      = - argVariation 0 1
          (fun u ↦ riemannZeta (lineSeg (2 : ℂ) ((2 : ℂ) + I * (t : ℂ)) u)) := by
    rw [argVariation_riemannZeta_lineSeg_of_two_le_re (fun u _ ↦ by norm_num [lineSeg_re]),
      argVariation_riemannZeta_lineSeg_of_two_le_re (fun u _ ↦ by norm_num [lineSeg_re]), neg_sub]
  -- `argVariation (1/2) X = argVariation (1/2) 2 + argVariation 2 X`.
  have hAsplit : argVariation (1 / 2) X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
      = argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ)))
        + argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) :=
    argVariation_trans (by norm_num) hX hrowcont.continuousOn
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  -- `VhorizL = -argVariation (1/2) 2`.
  have hAlow :
      argVariation 0 1
          (fun u ↦
            riemannZeta (lineSeg ((2 : ℂ) + I * (t : ℂ)) ((1 / 2 : ℂ) + I * (t : ℂ)) u))
      = - argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * (t : ℂ))) := by
    rw [show ((2 : ℂ) + I * (t : ℂ)) = (((2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num,
      show ((1 / 2 : ℂ) + I * (t : ℂ)) = (((1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) from by norm_num]
    exact argVariation_riemannZeta_lineSeg_horizontal_rev (by norm_num) ht.ne' hrowcont
      (fun σ hσ ↦ hne σ (by linarith [hσ.1]))
  -- Combine: substitute the four edge values, unfold `π · argZeta t` into the two contour legs
  -- (`Vvert + VhorizL`), and discharge the remaining linear identity.
  rw [hEb, hEr0, hEt0, hEl0] at hzero
  rw [hpi, argVariationContourL]
  linarith [hzero, hAsplit, hAlow]

/-- For `w` close to `1` (`‖w - 1‖ ≤ δ` with `δ < 1`), `|arg w| ≤ arcsin δ`: the disk
`‖w - 1‖ ≤ δ` is seen from the origin under a half-angle `arcsin δ`. -/
private theorem abs_arg_le_arcsin_of_norm_sub_one_le {w : ℂ} {δ : ℝ}
    (hw : ‖w - 1‖ ≤ δ) (hδ : δ < 1) : |w.arg| ≤ Real.arcsin δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hw
  have hre1 : |(w - 1).re| ≤ δ := (Complex.abs_re_le_norm _).trans hw
  rw [Complex.sub_re, Complex.one_re, abs_le] at hre1
  have hre : 0 < w.re := by linarith [hre1.1]
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr (by rintro rfl; simp at hre)
  -- the displacement bound, squared, and `‖w‖²`
  have e3 : (w.re - 1) ^ 2 + w.im ^ 2 ≤ δ ^ 2 := by
    have he : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]; ring
    linarith [pow_le_pow_left₀ (norm_nonneg _) hw 2, he]
  have e1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1d : (0 : ℝ) ≤ 1 - δ ^ 2 := by nlinarith [hδ0, hδ]
  -- `w.im² ≤ δ² ‖w‖²`, the perfect-square inequality `δ²‖w‖² - w.im² = (w.re-1+δ²)² + (1-δ²)·(…)`
  have habs : -(δ * ‖w‖) ≤ w.im ∧ w.im ≤ δ * ‖w‖ :=
    abs_le_of_sq_le_sq' (by
      rw [mul_pow, e1]
      nlinarith [e3, h1d, sq_nonneg (w.re - 1 + δ ^ 2), mul_nonneg h1d
        (by nlinarith [e3] : (0 : ℝ) ≤ δ ^ 2 - (w.re - 1) ^ 2 - w.im ^ 2)]) (by positivity)
  -- `0 < w.re` puts `arg w = arcsin (w.im / ‖w‖)`, and `arcsin` is monotone
  rw [Complex.arg_of_re_nonneg hre.le, abs_le, ← Real.arcsin_neg]
  exact ⟨Real.arcsin_le_arcsin (by rw [le_div_iff₀ hnorm]; linarith [habs.1]),
    Real.arcsin_le_arcsin (by rw [div_le_iff₀ hnorm]; linarith [habs.2])⟩

/-- `logDeriv ζ`, transported to `ℝ × ℝ` via `ℂ ≃ᵐ ℝ × ℝ`, is integrable on a product box
`[a, b] × [c, d]` lying in the open upper half-plane (`0 < c ≤ d`). -/
private theorem integrable_logDeriv_riemannZeta_box {a b c d : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hcd : c ≤ d) :
    Integrable (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ)))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))) := by
  have hfun : (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ))) ∘
      ⇑Complex.measurableEquivRealProd = logDeriv riemannZeta := funext fun z ↦ by
    simp only [Function.comp_apply, Complex.measurableEquivRealProd_apply]
    rw [mul_comm I (z.im : ℂ), Complex.re_add_im]
  have hset : Complex.measurableEquivRealProd ⁻¹' (Set.Icc a b ×ˢ Set.Icc c d)
      = Rectangle ((a : ℂ) + I * (c : ℂ)) ((b : ℂ) + I * (d : ℂ)) := by
    ext z
    simp [Rectangle, Complex.mem_reProdIm, Set.uIcc_of_le hab, Set.uIcc_of_le hcd,
      and_and_and_comm]
  rw [Measure.prod_restrict]
  change IntegrableOn (fun p : ℝ × ℝ ↦ logDeriv riemannZeta ((p.1 : ℂ) + I * (p.2 : ℂ)))
    (Set.Icc a b ×ˢ Set.Icc c d) volume
  rw [← Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
        Complex.measurableEquivRealProd.measurableEmbedding, hfun, hset]
  exact integrableOn_logDeriv_riemannZeta_rectangle (by simpa using hc)
    (by simpa using hc.trans_le hcd)

/-- **Domination of the horizontal argument variation** (`lem:lb_horiz_argVar_bdd`). For every
`X ≥ 2` and every nonzero `t` whose ray `{σ + it : σ ≥ 1/2}` is zero-free, the horizontal argument
variation of `ζ` is bounded by the `t`-dependent majorant
`g(t) = 2·arcsin(π²/6 - 1) + ∫_{1/2}^{2} ‖(ζ'/ζ)(σ+it)‖ dσ`. The `t`-dependence is essential: a
uniform constant bound is false near an ordinate. -/
theorem abs_argVariation_riemannZeta_horizontal_le {X t : ℝ} (hX : 2 ≤ X) (ht : t ≠ 0)
    (hne : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    |argVariation (1 / 2) X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  -- The row map `σ ↦ ζ(σ+it)` is continuous (the line `Im = t` avoids the pole `s = 1`).
  have hrowcont : Continuous (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t)) :=
    continuous_riemannZeta_horizontal ht
  -- Head `[1/2, 2]`: the imaginary part of `∫ ζ'/ζ`, bounded by its `L¹`-norm.
  have hhead : |argVariation (1 / 2) 2 (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
    rw [argVariation_riemannZeta_horizontal_eq_im_integral (by norm_num) ht
      (fun σ hσ ↦ hne σ hσ.1)]
    exact (Complex.abs_im_le_norm _).trans
      (intervalIntegral.norm_integral_le_integral_norm (by norm_num))
  -- Tail `[2, X]`: in `Re s ≥ 2`, `ζ` is in the slit plane and `|arg ζ| ≤ arcsin(π²/6 - 1)`.
  have htail : |argVariation 2 X (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + I * t))|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1) := by
    have hb : ∀ σ : ℝ, 2 ≤ σ →
        |(riemannZeta ((σ : ℂ) + I * t)).arg| ≤ Real.arcsin (Real.pi ^ 2 / 6 - 1) :=
      fun σ hσ ↦ abs_arg_le_arcsin_of_norm_sub_one_le
        (norm_riemannZeta_sub_one_le_of_two_le_re (by simpa using hσ))
        (by nlinarith [Real.pi_lt_d2, Real.pi_pos])
    rw [argVariation_eq_arg_sub_arg hX hrowcont.continuousOn (fun σ hσ ↦
      riemannZeta_mem_slitPlane_of_two_le_re (by simpa using hσ.1))]
    exact (abs_sub _ _).trans (by linarith [hb X (by linarith), hb 2 le_rfl])
  -- Split the variation at `σ = 2` and combine the two pieces.
  rw [argVariation_trans (by norm_num) hX hrowcont.continuousOn (fun σ hσ ↦ hne σ hσ.1)]
  exact (abs_add_le _ _).trans (by linarith [hhead, htail])

/-- **Integrability of the dominating function** (`lem:lb_horiz_argVar_bdd`). For `0 < t₁ ≤ t₂`
the majorant of `abs_argVariation_riemannZeta_horizontal_le` is integrable on `[t₁, t₂]`. -/
theorem integrableOn_argVariation_riemannZeta_horizontal_bound {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) :
    IntegrableOn (fun t : ℝ ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
      + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖) (Icc t₁ t₂) := by
  have hbox := integrable_logDeriv_riemannZeta_box (by norm_num : (1 / 2 : ℝ) ≤ 2) ht1 h12
  refine continuous_const.continuousOn.integrableOn_Icc.add
    ((hbox.swap.integral_norm_prod_left).congr (Filter.Eventually.of_forall fun t ↦ ?_))
  simp only [Function.comp_apply, Prod.swap_prod_mk,
    intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2),
    MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **The truncated row integral tends to `-π S(t)`.** For `t > 0` with a zero-free ray, the
imaginary part of `∫_{1/2}^{X} (ζ'/ζ)(σ+it) dσ` tends to `-π · argZeta t` as `X → ∞`. -/
private theorem tendsto_im_integral_logDeriv_row_atTop {t : ℝ} (ht : 0 < t)
    (hray : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    Tendsto (fun X : ℝ ↦ (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im)
      atTop (𝓝 (-(Real.pi * argZeta t))) := by
  refine (tendsto_argVariation_riemannZeta_horizontal_atTop ht hray).congr' ?_
  filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
  exact argVariation_riemannZeta_horizontal_eq_im_integral hX ht.ne' fun σ hσ ↦ hray σ hσ.1

/-- **The truncated row integral obeys the majorant** of
`abs_argVariation_riemannZeta_horizontal_le`. -/
private theorem abs_im_integral_logDeriv_row_le {X t : ℝ} (hX : 2 ≤ X) (ht : t ≠ 0)
    (hray : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    |(∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im|
      ≤ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ := by
  rw [← argVariation_riemannZeta_horizontal_eq_im_integral (by linarith) ht
    fun σ hσ ↦ hray σ hσ.1]
  exact abs_argVariation_riemannZeta_horizontal_le hX ht hray

/-- The partial integral `t ↦ ∫_{1/2}^{X} (ζ'/ζ)(σ+it) dσ` is integrable on `[t₁, t₂]`. -/
private theorem integrable_integral_logDeriv_riemannZeta_row {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    Integrable (fun t : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t))
      (volume.restrict (Set.Icc t₁ t₂)) := by
  have hbox := integrable_logDeriv_riemannZeta_box hX ht1 h12
  refine (hbox.swap.integral_prod_left).congr (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [Function.comp_apply, Prod.swap_prod_mk, intervalIntegral.integral_of_le hX,
    MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The partial integral `σ ↦ ∫_{t₁}^{t₂} (ζ'/ζ)(σ+it) dt` is integrable on `[1/2, X]`. -/
private theorem integrable_integral_logDeriv_riemannZeta_col {t₁ t₂ : ℝ} (ht1 : 0 < t₁)
    (h12 : t₁ ≤ t₂) {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    Integrable (fun σ : ℝ ↦ ∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t))
      (volume.restrict (Set.Icc (1 / 2 : ℝ) X)) := by
  have hbox := integrable_logDeriv_riemannZeta_box hX ht1 h12
  refine (hbox.integral_prod_left).congr (Filter.Eventually.of_forall fun σ ↦ ?_)
  simp only [intervalIntegral.integral_of_le h12, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- `Im` commutes with an interval integral over `[a, b]` (`a ≤ b`) of an integrable function. -/
private theorem intervalIntegral_im {a b : ℝ} (hab : a ≤ b) {F : ℝ → ℂ}
    (hF : Integrable F (volume.restrict (Icc a b))) :
    (∫ x in a..b, (F x).im) = (∫ x in a..b, F x).im := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_im (hF.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl))

/-- An iterated interval integral over `[a, b] × [c, d]` (`a ≤ b`, `c ≤ d`) as an iterated set
integral over the closed box. -/
private theorem intervalIntegral₂_eq_setIntegral₂ {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (F : ℝ → ℝ → ℂ) :
    (∫ x in a..b, ∫ y in c..d, F x y) = ∫ x in Icc a b, ∫ y in Icc c d, F x y := by
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact setIntegral_congr_fun measurableSet_Icc fun x _ ↦ by
    rw [intervalIntegral.integral_of_le hcd, ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **Littlewood's reduction, truncated form.** For `0 < t₁ ≤ t₂` and `1/2 ≤ X`, the truncated
difference `∫_{1/2}^{X} (log|ζ(σ+it₂)| - log|ζ(σ+it₁)|) dσ` equals
`-∫_{t₁}^{t₂} Im(∫_{1/2}^{X} (ζ'/ζ)(σ+it) dσ) dt`. -/
private theorem integral_log_norm_riemannZeta_sub_eq {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    (∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖))
      = -∫ t in t₁..t₂,
          (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
  -- Step 2 (telescope a.e. σ, off the finite set of zero abscissae in `[1/2, X] × [t₁, t₂]`):
  -- replace the integrand by `-Im ∫ G dt`.
  have hcongr : (∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖))
      = ∫ σ in (1 / 2 : ℝ)..X,
          -(∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t)).im := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr ((finite_re_riemannZeta_zeros_rectangle
      (z := (1 / 2 : ℂ) + I * (t₁ : ℂ)) (w := (X : ℂ) + I * (t₂ : ℂ)) (by simpa using ht1)
      (by simpa using ht1.trans_le h12)).measure_zero volume)] with σ hσ hσI
    rw [Set.uIoc_of_le hX] at hσI
    refine log_norm_riemannZeta_sub_eq_neg_im_integral h12 ht1 fun t ht hzero ↦
      hσ ⟨(σ : ℂ) + I * (t : ℂ), ⟨ofReal_add_I_mul_mem_rectangle (by simpa using hX)
        (by simpa using h12) (by simpa using (⟨hσI.1.le, hσI.2⟩ : σ ∈ Icc (1 / 2 : ℝ) X))
        (by simpa using ht), hzero⟩, by simp⟩
  -- Steps 2–3 (Fubini and pulling `Im` through the integrals).
  have hpullσ := intervalIntegral_im hX (integrable_integral_logDeriv_riemannZeta_col ht1 h12 hX)
  have hpullt := intervalIntegral_im h12 (integrable_integral_logDeriv_riemannZeta_row ht1 h12 hX)
  have hswap : (∫ σ in (1 / 2 : ℝ)..X, ∫ t in t₁..t₂, logDeriv riemannZeta ((σ : ℂ) + I * t))
      = ∫ t in t₁..t₂, ∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t) := by
    rw [intervalIntegral₂_eq_setIntegral₂ hX h12, intervalIntegral₂_eq_setIntegral₂ h12 hX]
    exact integral_integral_swap (integrable_logDeriv_riemannZeta_box hX ht1 h12)
  rw [hcongr, intervalIntegral.integral_neg]
  congr 1
  rw [hpullσ, hswap, ← hpullt]

/-- Almost every `t` fails to be the ordinate of a zero of `ζ` in the box `[1/2, 2] × [t₁, t₂]`. -/
private theorem ae_not_mem_im_riemannZeta_zeros {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (ht2 : 0 < t₂) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
        ∩ {ρ | riemannZeta ρ = 0}) :=
  compl_mem_ae_iff.mpr ((finite_im_riemannZeta_zeros_rectangle (by simpa using ht1)
    (by simpa using ht2)).measure_zero volume)

/-- For `t ∈ Ι t₁ t₂` (`0 < t₁ ≤ t₂`) that is not an ordinate of a zero in the box, `t` is
positive and the whole ray `{σ + it : σ ≥ 1/2}` is zero-free. -/
private theorem pos_and_ray_ne_zero_of_not_mem_im_zeros {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {t : ℝ} (htI : t ∈ Set.uIoc t₁ t₂)
    (htbad : t ∉ Complex.im '' (Rectangle ((1 / 2 : ℂ) + I * (t₁ : ℂ)) ((2 : ℂ) + I * (t₂ : ℂ))
      ∩ {ρ | riemannZeta ρ = 0})) :
    0 < t ∧ ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0 := by
  rw [Set.uIoc_of_le h12] at htI
  have htIcc : t ∈ Set.Icc t₁ t₂ := Set.Ioc_subset_Icc_self htI
  exact ⟨by linarith [htIcc.1], riemannZeta_ray_ne_zero_of_not_mem_im_zeros h12 htIcc htbad⟩

/-- The truncated row marginal `t ↦ Im ∫_{1/2}^{X} (ζ'/ζ)(σ+it) dσ` is a.e. strongly measurable
on `Ι t₁ t₂`. -/
private theorem aestronglyMeasurable_im_integral_row {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂)
    {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    AEStronglyMeasurable
      (fun t : ℝ ↦ (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im)
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) :=
  ((integrable_integral_logDeriv_riemannZeta_row ht1 h12 hX).im).aestronglyMeasurable.mono_measure
    (Measure.restrict_mono (Set.uIoc_of_le h12 ▸ Set.Ioc_subset_Icc_self) le_rfl)

/-- **Interval-integrability of `argZeta`** on `[t₁, t₂]` for `0 < t₁ ≤ t₂`. Unlike
`pi_mul_integral_argZeta_eq_sub`, this needs no zero-freeness at the endpoints. -/
theorem intervalIntegrable_argZeta {t₁ t₂ : ℝ} (ht1 : 0 < t₁) (h12 : t₁ ≤ t₂) :
    IntervalIntegrable argZeta volume t₁ t₂ := by
  have ht2 : 0 < t₂ := lt_of_lt_of_le ht1 h12
  have h0T := ae_not_mem_im_riemannZeta_zeros ht1 ht2
  set bound : ℝ → ℝ := fun t ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
      + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖
  set F : ℕ → ℝ → ℝ := fun n t ↦
    (∫ σ in (1 / 2 : ℝ)..((n : ℝ) + 1), logDeriv riemannZeta ((σ : ℂ) + I * t)).im
  have hFmeas : ∀ n, AEStronglyMeasurable (F n)
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) := fun n ↦
    aestronglyMeasurable_im_integral_row ht1 h12
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc t₁ t₂ →
      Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (-(Real.pi * argZeta t)))
        ∧ ‖-(Real.pi * argZeta t)‖ ≤ bound t := by
    filter_upwards [h0T] with t htbad htI
    obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12 htI htbad
    have htend : Tendsto (fun n : ℕ ↦ F n t) atTop (𝓝 (-(Real.pi * argZeta t))) :=
      (tendsto_im_integral_logDeriv_row_atTop htpos hray).comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    refine ⟨htend, le_of_tendsto htend.norm ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact abs_im_integral_logDeriv_row_le
      (by exact_mod_cast Nat.add_one_le_iff.mpr (by lia)) htpos.ne' hray
  have hmeas : AEStronglyMeasurable (fun t ↦ -(Real.pi * argZeta t))
      ((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop hFmeas ?_
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with t ht htI using (ht htI).1
  have hbound_int : IntegrableOn bound (Set.uIoc t₁ t₂) volume :=
    Set.uIoc_of_le h12 ▸ (integrableOn_argVariation_riemannZeta_horizontal_bound ht1
      h12).mono_set Set.Ioc_subset_Icc_self
  have hdom : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.uIoc t₁ t₂)),
      ‖-(Real.pi * argZeta t)‖ ≤ bound t := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae] with t ht htI using (ht htI).2
  have hfun : (fun t ↦ -(1 / Real.pi) * -(Real.pi * argZeta t)) = argZeta := funext fun t ↦ by
    rw [neg_mul_neg, ← mul_assoc, one_div_mul_cancel Real.pi_ne_zero, one_mul]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h12, ← Set.uIoc_of_le h12]
  exact hfun ▸ (Integrable.mono' hbound_int hmeas hdom).const_mul (-(1 / Real.pi))

/-- **The ordinates of zeros of `ζ` on the ray `σ ≥ 1/2` are locally finite.** For `0 < a ≤ b`,
only finitely many `t ∈ [a, b]` are the ordinate of a zero `σ + it` with `σ ≥ 1/2`; so the
zero-free ordinates are dense. -/
theorem finite_setOf_riemannZeta_zero_ray_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    {t : ℝ | (∃ σ : ℝ, (1 / 2 : ℝ) ≤ σ ∧ riemannZeta ((σ : ℂ) + I * t) = 0)
      ∧ t ∈ Set.Icc a b}.Finite := by
  have hb : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  refine Set.Finite.subset (finite_im_riemannZeta_zeros_rectangle
    (show (0 : ℝ) < ((1 / 2 : ℂ) + I * (a : ℂ)).im by simpa using ha)
    (show (0 : ℝ) < ((2 : ℂ) + I * (b : ℂ)).im by simpa using hb)) ?_
  rintro t ⟨⟨σ, hσ, hz⟩, htab⟩
  exact ⟨(σ : ℂ) + I * (t : ℂ), ⟨ofReal_add_I_mul_mem_rectangle_two hab hσ
    (re_le_one_of_riemannZeta_eq_zero hz) htab, hz⟩, by simp⟩

/-- **Littlewood's reduction** (`lem:lb_littlewood`). For `t₁ < t₂` with `0 < t₁`, neither an
ordinate of a zero of `ζ` on the ray `σ ≥ 1/2`, `π ∫_{t₁}^{t₂} S(t) dt = I(t₂) - I(t₁)`, where
`S = argZeta` and `I = logNormZetaIntegral`. -/
theorem pi_mul_integral_argZeta_eq_sub {t₁ t₂ : ℝ} (h12 : t₁ < t₂) (ht1 : 0 < t₁)
    (hne1 : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0)
    (hne2 : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) :
    Real.pi * ∫ t in t₁..t₂, argZeta t
      = logNormZetaIntegral t₂ - logNormZetaIntegral t₁ := by
  have h12' : t₁ ≤ t₂ := h12.le
  have ht2 : 0 < t₂ := lt_trans ht1 h12
  -- **Step 1: truncation limits.** `I(tⱼ) = lim_X ∫_{1/2}^X log|ζ(σ+itⱼ)|`, with each truncation
  -- interval-integrable; both are read off `integrableOn_log_norm_riemannZeta_Ioi`.
  have htr : ∀ t : ℝ, t ≠ 0 → (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      Tendsto (fun X : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X, Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖)
        atTop (𝓝 (logNormZetaIntegral t)) := fun t ht hne ↦ by
    simpa [logNormZetaIntegral] using intervalIntegral_tendsto_integral_Ioi (1 / 2)
      (integrableOn_log_norm_riemannZeta_Ioi ht hne) tendsto_id
  have hii : ∀ t : ℝ, t ≠ 0 → (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      ∀ X : ℝ, (1 / 2 : ℝ) ≤ X → IntervalIntegrable
        (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + I * t)‖) volume (1 / 2) X :=
    fun t ht hne X hX ↦ (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr
      ((integrableOn_log_norm_riemannZeta_Ioi ht hne).mono_set Set.Ioc_subset_Ioi_self)
  have hDtend : Tendsto (fun X : ℝ ↦ ∫ σ in (1 / 2 : ℝ)..X,
        (Real.log ‖riemannZeta ((σ : ℂ) + I * t₂)‖
          - Real.log ‖riemannZeta ((σ : ℂ) + I * t₁)‖)) atTop
      (𝓝 (logNormZetaIntegral t₂ - logNormZetaIntegral t₁)) := by
    refine ((htr t₂ ht2.ne' hne2).sub (htr t₁ ht1.ne' hne1)).congr' ?_
    filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
    rw [intervalIntegral.integral_sub (hii t₂ ht2.ne' hne2 X hX) (hii t₁ ht1.ne' hne1 X hX)]
  -- **Step 4 preparation: a.e. zero-free rays off the finite ordinate set.**
  have h0T := ae_not_mem_im_riemannZeta_zeros ht1 ht2
  -- **Step 4: dominated convergence.**
  have hDCT : Tendsto (fun X : ℝ ↦ ∫ t in t₁..t₂,
        (∫ σ in (1 / 2 : ℝ)..X, logDeriv riemannZeta ((σ : ℂ) + I * t)).im) atTop
      (𝓝 (∫ t in t₁..t₂, -(Real.pi * argZeta t))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun t ↦ 2 * Real.arcsin (Real.pi ^ 2 / 6 - 1)
        + ∫ σ in (1 / 2 : ℝ)..2, ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
      exact aestronglyMeasurable_im_integral_row ht1 h12' hX
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
      filter_upwards [h0T] with t htbad htI
      obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12' htI htbad
      rw [Real.norm_eq_abs]
      exact abs_im_integral_logDeriv_row_le hX htpos.ne' hray
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h12').mpr
        ((integrableOn_argVariation_riemannZeta_horizontal_bound ht1 h12').mono_set
          Set.Ioc_subset_Icc_self)
    · filter_upwards [h0T] with t htbad htI
      obtain ⟨htpos, hray⟩ := pos_and_ray_ne_zero_of_not_mem_im_zeros ht1 h12' htI htbad
      exact tendsto_im_integral_logDeriv_row_atTop htpos hray
  -- **Assemble.** The truncated difference equals `-∫ φ_X`; both limits coincide.
  have huniq : logNormZetaIntegral t₂ - logNormZetaIntegral t₁
      = -∫ t in t₁..t₂, -(Real.pi * argZeta t) :=
    tendsto_nhds_unique (hDtend.congr' (by
      filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with X hX
      exact integral_log_norm_riemannZeta_sub_eq ht1 h12' hX)) hDCT.neg
  rw [huniq, intervalIntegral.integral_neg, neg_neg, intervalIntegral.integral_const_mul]

