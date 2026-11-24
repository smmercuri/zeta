/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Zeros.HardyZ
public import Zeta.Gamma.TrigammaDecay
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Gram-point averaging lemma (Turing's method)

For the Riemann–Siegel theta function `θ = riemannSiegelTheta`, the normalised phase increment
`gramCoord l t = (θ(t) − θ(l))/π` averages to at most `1/2` over a Gram interval, and likewise
over a whole Gram block in its fractional form; also the calculus of `θ` the bound rests on (its
derivative, continuity, convexity, and strict monotonicity past `7`; blueprint
`gram_averaging.tex`).

## Main definitions

- `gramCoord`: the normalised phase increment `x(t, l) = (θ(t) − θ(l))/π`.
- `gramDomain`: the monotonicity domain `Ici 7` of `θ`.

## Main results

- `ConvexOn.integral_sub_left_le`: the convex chord bound
  `∫_a^b (f t − f a) dt ≤ (b−a)(f b − f a)/2`.
- `hasDerivAt_riemannSiegelTheta`: `θ'(T) = ½ Re ψ(¼ + iT/2) − ½ log π`, with `ψ` the digamma
  function.
- `continuousOn_riemannSiegelTheta`, `convexOn_riemannSiegelTheta`: continuity and convexity of
  `θ` on `[0, ∞)`.
- `integral_gramCoord_le`, `sum_integral_gramCoord_le`, `integral_fract_gramCoord_le`: the
  averaging bound over one Gram interval, over a Gram block, and in its fractional single-integral
  form.
- `strictMonoOn_riemannSiegelTheta_gramDomain`, `tendsto_riemannSiegelTheta_atTop`,
  `riemannSiegelTheta_seven_le`: `θ` is strictly increasing to `∞` on `[7, ∞)`, and
  `θ(7) ≤ n·π`.
-/
@[expose] public section


open MeasureTheory Filter
open scoped Topology Real

open Complex

/-- **Chord integral bound** for a convex continuous function on `[a, b]`. -/
theorem ConvexOn.integral_sub_left_le {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hfc : ContinuousOn f (Set.Icc a b)) :
    ∫ t in a..b, (f t - f a) ≤ (b - a) * (f b - f a) / 2 := by
  have hba : (0 : ℝ) < b - a := by linarith
  set k : ℝ := (f b - f a) / (b - a) with hk
  have hkval : k * (b - a) = f b - f a := div_mul_cancel₀ _ hba.ne'
  -- pointwise chord bound `f t − f a ≤ k (t − a)`, i.e. secant monotonicity from `a`
  have hchord : ∀ t ∈ Set.Icc a b, f t - f a ≤ k * (t - a) := fun t ht ↦ by
    rcases eq_or_lt_of_le ht.1 with h | hlt
    · simp [← h]
    · rcases eq_or_lt_of_le ht.2 with h2 | hlt2
      · rw [h2]; exact hkval.ge
      · exact (div_le_iff₀ (by linarith : (0 : ℝ) < t - a)).1 (hk ▸ hf.secant_mono_aux2
          (Set.left_mem_Icc.2 hab.le) (Set.right_mem_Icc.2 hab.le) hlt hlt2)
  -- integrate the chord bound and evaluate `∫_a^b k (t − a) dt = (b − a)(f b − f a)/2`
  have hmono := intervalIntegral.integral_mono_on hab.le
    ((hfc.intervalIntegrable_of_Icc (μ := volume) hab.le).sub intervalIntegrable_const)
    ((by fun_prop : Continuous fun t ↦ k * (t - a)).intervalIntegrable a b) hchord
  have heval : ∫ t in a..b, k * (t - a) = (b - a) * (f b - f a) / 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun t ↦ t) a, integral_id, ← hkval]
    ring
  rwa [heval] at hmono

/-- **First derivative of the Riemann–Siegel theta function**, with `ψ = Complex.digamma`. -/
theorem hasDerivAt_riemannSiegelTheta {T : ℝ} (hT : 0 < T) :
    HasDerivAt riemannSiegelTheta
      (1 / 2 * (Complex.digamma (1 / 4 + Complex.I * (T / 2))).re
        - 1 / 2 * Real.log Real.pi) T := by
  set w : ℂ := 1 / 4 + Complex.I * ((T : ℂ) / 2) with hw
  have hre : 0 < w.re := by rw [show w.re = 1 / 4 by rw [hw]; simp]; norm_num
  -- the branch value composed with the vertical line, then imaginary part, minus the linear term
  have hcurve := ((hasDerivAt_logGamma hre).comp (T : ℂ)
    ((((hasDerivAt_id (T : ℂ)).div_const 2).const_mul Complex.I).const_add (1 / 4))).comp_ofReal
  have hg := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt T hcurve).sub
    (((hasDerivAt_id T).div_const 2).mul_const (Real.log Real.pi))
  simp only [Complex.imCLM_apply, Function.comp_apply] at hg
  -- reconcile the derivative value: `Im (ψ w · (i/2)) = ½ Re (ψ w)`
  rw [show (Complex.digamma w * (Complex.I * (1 / 2))).im - 1 / 2 * Real.log Real.pi
      = 1 / 2 * (Complex.digamma w).re - 1 / 2 * Real.log Real.pi by
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      show ((1 : ℂ) / 2).re = 1 / 2 by simp, show ((1 : ℂ) / 2).im = 0 by simp]
    ring] at hg
  -- the branch expression agrees with `θ` on a neighbourhood of `T`
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hT] with s (hs : (0 : ℝ) < s)
  exact riemannSiegelTheta_eq_im_logGamma hs.le

/-- `θ = riemannSiegelTheta` is continuous on `[0, ∞)`. -/
theorem continuousOn_riemannSiegelTheta : ContinuousOn riemannSiegelTheta (Set.Ici 0) := by
  have hline : Continuous fun T : ℝ ↦ (1 / 4 : ℂ) + Complex.I * ((T : ℂ) / 2) :=
    ((Complex.continuous_ofReal.div_const 2).const_mul Complex.I).const_add (1 / 4)
  have hcurve : Continuous fun T : ℝ ↦ logGamma (1 / 4 + Complex.I * ((T : ℂ) / 2)) :=
    continuous_iff_continuousAt.2 fun T ↦ ContinuousAt.comp
      (f := fun T : ℝ ↦ (1 / 4 : ℂ) + Complex.I * ((T : ℂ) / 2))
      (hasDerivAt_logGamma (show 0 < (1 / 4 + Complex.I * ((T : ℂ) / 2)).re by
        rw [show (1 / 4 + Complex.I * ((T : ℂ) / 2)).re = 1 / 4 by simp]; norm_num)).continuousAt
      hline.continuousAt
  exact ((Complex.continuous_im.comp hcurve).sub
    ((continuous_id.div_const 2).mul continuous_const)).continuousOn.congr
      fun T hT ↦ riemannSiegelTheta_eq_im_logGamma hT

/-- **Convexity of the Riemann–Siegel theta function** on `[0, ∞)`. -/
theorem convexOn_riemannSiegelTheta : ConvexOn ℝ (Set.Ici 0) riemannSiegelTheta := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 0) continuousOn_riemannSiegelTheta
    (fun T hT ↦ ?_) (fun x hx y hy hxy ↦ ?_)
  · rw [interior_Ici] at hT
    exact (hasDerivAt_riemannSiegelTheta hT).differentiableAt.differentiableWithinAt
  · rw [interior_Ici] at hx hy
    rw [(hasDerivAt_riemannSiegelTheta hx).deriv, (hasDerivAt_riemannSiegelTheta hy).deriv]
    linarith [monotoneOn_re_digamma_quarter_vertical (Set.mem_Ici.2 (Set.mem_Ioi.mp hx).le)
      (Set.mem_Ici.2 (Set.mem_Ioi.mp hy).le) hxy]

/-- **Normalised phase increment** `x(t, l) = (θ(t) − θ(l))/π`, with base point `l` the first
argument and running variable `t` the second. -/
noncomputable def gramCoord (l t : ℝ) : ℝ := (riemannSiegelTheta t - riemannSiegelTheta l) / Real.pi

/-- **Gram-point averaging bound** over a Gram interval `[l, l+h] ⊆ [0, ∞)` (one on which `θ`
gains exactly `π`). -/
theorem integral_gramCoord_le {l h : ℝ} (hl : 0 ≤ l) (hh : 0 < h)
    (hgram : riemannSiegelTheta (l + h) - riemannSiegelTheta l = Real.pi) :
    ∫ t in l..l + h, gramCoord l t ≤ h / 2 := by
  have hsub : Set.Icc l (l + h) ⊆ Set.Ici 0 := fun x hx ↦ hl.trans hx.1
  have key : ∫ t in l..l + h, (riemannSiegelTheta t - riemannSiegelTheta l) ≤ h / 2 * Real.pi := by
    have h0 := ConvexOn.integral_sub_left_le (show l < l + h by linarith)
      (convexOn_riemannSiegelTheta.subset hsub (convex_Icc l (l + h)))
      (continuousOn_riemannSiegelTheta.mono hsub)
    rw [hgram] at h0
    exact h0.trans_eq (by ring)
  rw [show (∫ t in l..l + h, gramCoord l t)
        = (∫ t in l..l + h, (riemannSiegelTheta t - riemannSiegelTheta l)) / Real.pi by
      simp only [gramCoord, intervalIntegral.integral_div], div_le_iff₀ Real.pi_pos]
  linarith [key]

/-- Monotonicity of a block of points from the consecutive strict inequalities `p i < p (i+1)`. -/
private theorem le_of_stepwise_lt {k : ℕ} {p : ℕ → ℝ} (hmono : ∀ i < k, p i < p (i + 1)) :
    ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ k → p i ≤ p j := by
  intro i j hij
  induction hij with
  | refl => exact fun _ ↦ le_rfl
  | @step m _ ih => exact fun hmk ↦ (ih (by lia)).trans (hmono m (by lia)).le

/-- **Gram-block averaging bound**: over consecutive Gram intervals `[p i, p (i+1)] ⊆ [0, ∞)`, the
phase increments measured from the *left* endpoint of each interval sum to at most half the total
width. -/
theorem sum_integral_gramCoord_le {k : ℕ} {p : ℕ → ℝ} (hp0 : 0 ≤ p 0)
    (hmono : ∀ i < k, p i < p (i + 1))
    (hgram : ∀ i < k, riemannSiegelTheta (p (i + 1)) - riemannSiegelTheta (p i) = Real.pi) :
    ∑ i ∈ Finset.range k, ∫ t in p i..p (i + 1), gramCoord (p i) t ≤ (p k - p 0) / 2 := by
  -- each Gram interval contributes at most half its width; then telescope the widths
  refine (Finset.sum_le_sum (g := fun i ↦ (p (i + 1) - p i) / 2) fun i hi ↦ ?_).trans
    (le_of_eq (by rw [← Finset.sum_div, Finset.sum_range_sub]))
  have hi' : i < k := Finset.mem_range.1 hi
  have e : p i + (p (i + 1) - p i) = p (i + 1) := by ring
  have hkey := integral_gramCoord_le (l := p i) (h := p (i + 1) - p i)
    (hp0.trans (le_of_stepwise_lt hmono (Nat.zero_le i) hi'.le))
    (by linarith [hmono i hi']) (by rw [e]; exact hgram i hi')
  rwa [e] at hkey

/-- **Gram-block averaging bound, single-integral form**: over a Gram block `p 0 < ⋯ < p k` in
`[0, ∞)` on which `θ` is strictly increasing, the *fractional* phase increment measured from the
block's left endpoint averages to at most `1/2`. The caller supplies strict monotonicity, e.g. from
`strictMonoOn_riemannSiegelTheta_gramDomain`. -/
theorem integral_fract_gramCoord_le {k : ℕ} {p : ℕ → ℝ} (hp0 : 0 ≤ p 0)
    (hmono : ∀ i < k, p i < p (i + 1))
    (hsmono : StrictMonoOn riemannSiegelTheta (Set.Icc (p 0) (p k)))
    (hgram : ∀ i < k, riemannSiegelTheta (p (i + 1)) - riemannSiegelTheta (p i) = Real.pi) :
    ∫ t in p 0..p k, Int.fract (gramCoord (p 0) t) ≤ (p k - p 0) / 2 := by
  have hple := le_of_stepwise_lt hmono
  -- telescope `hgram`: `θ(p j) = θ(p 0) + j·π`
  have htel : ∀ j, j ≤ k →
      riemannSiegelTheta (p j) = riemannSiegelTheta (p 0) + (j : ℝ) * Real.pi := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ m ih =>
      intro hj
      push_cast
      rw [show riemannSiegelTheta (p (m + 1)) = riemannSiegelTheta (p m) + Real.pi from by
        linarith [hgram m (by lia)], ih (by lia)]
      ring
  -- pointwise: inside the `i`-th Gram interval the global fractional phase is the local phase
  have hpt : ∀ i, i < k → ∀ t, p i < t → t < p (i + 1) →
      Int.fract (gramCoord (p 0) t) = gramCoord (p i) t := by
    intro i hik t htl htr
    have hmemi : p i ∈ Set.Icc (p 0) (p k) :=
      ⟨hple (Nat.zero_le i) hik.le, hple hik.le le_rfl⟩
    have hmemi1 : p (i + 1) ∈ Set.Icc (p 0) (p k) :=
      ⟨hple (Nat.zero_le _) hik, hple hik le_rfl⟩
    have hmemt : t ∈ Set.Icc (p 0) (p k) :=
      ⟨(hmemi.1.trans_lt htl).le, (htr.trans_le hmemi1.2).le⟩
    have hlow := hsmono.monotoneOn hmemi hmemt htl.le
    have hhigh : riemannSiegelTheta t < riemannSiegelTheta (p (i + 1)) := hsmono hmemt hmemi1 htr
    have hgx : gramCoord (p 0) t = gramCoord (p i) t + (i : ℝ) := by
      simp only [gramCoord]; rw [htel i hik.le]; field_simp; ring
    have h0 : 0 ≤ gramCoord (p i) t := div_nonneg (by linarith) Real.pi_pos.le
    have h1 : gramCoord (p i) t < 1 := by
      simp only [gramCoord]; rw [div_lt_one Real.pi_pos]; linarith [hgram i hik]
    rw [hgx, Int.fract_add_natCast]
    exact Int.fract_eq_self.mpr ⟨h0, h1⟩
  -- the two integrands agree a.e. on each Gram interval (they differ only at the right endpoint)
  have hmain : ∀ i, i < k → ∀ᵐ t ∂volume,
      t ∈ Set.uIoc (p i) (p (i + 1)) → Int.fract (gramCoord (p 0) t) = gramCoord (p i) t := by
    intro i hik
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (p (i + 1)))] with t ht htmem
    rw [Set.uIoc_of_le (hmono i hik).le] at htmem
    exact hpt i hik t htmem.1 (lt_of_le_of_ne htmem.2 (by simpa using ht))
  -- `gramCoord (p i)` is continuous on the interval, so both integrands are interval-integrable
  have hcont : ∀ i, i < k → ContinuousOn (gramCoord (p i)) (Set.uIcc (p i) (p (i + 1))) := by
    intro i hik
    rw [Set.uIcc_of_le (hmono i hik).le]
    have hsub : Set.Icc (p i) (p (i + 1)) ⊆ Set.Ici 0 :=
      fun x hx ↦ Set.mem_Ici.mpr ((hp0.trans (hple (Nat.zero_le i) hik.le)).trans hx.1)
    unfold gramCoord
    exact ((continuousOn_riemannSiegelTheta.mono hsub).sub continuousOn_const).div_const _
  have hint : ∀ i, i < k →
      IntervalIntegrable (fun t ↦ Int.fract (gramCoord (p 0) t)) volume (p i) (p (i + 1)) :=
    fun i hik ↦ (intervalIntegrable_congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (hmain i hik))).mpr
        (hcont i hik).intervalIntegrable
  -- glue the blocks into one integral, rewrite to the local phase, and invoke the sum-wise bound
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint,
    Finset.sum_congr rfl (fun i hi ↦ intervalIntegral.integral_congr_ae
      (hmain i (Finset.mem_range.mp hi)))]
  exact sum_integral_gramCoord_le hp0 hmono hgram

open Set

/-- The monotonicity domain `[7, ∞)` of `θ` (whose last stationary point is `t₀ ≈ 6.29`). -/
abbrev gramDomain : Set ℝ := Ici 7

/-- **`θ'(7) > 0`**, in digamma form. -/
private theorem log_pi_lt_re_digamma_quarter_seven :
    Real.log Real.pi < (Complex.digamma (1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2))).re := by
  set s : ℂ := 1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2) with hs_def
  have hsre : s.re = 1 / 4 := by rw [hs_def]; simp
  have hsim : s.im = 7 / 2 := by rw [hs_def]; simp
  have hnormSq : Complex.normSq s = 197 / 16 := by
    rw [Complex.normSq_apply, hsre, hsim]; norm_num
  have hnorm_pos : 0 < ‖s‖ :=
    norm_pos_iff.mpr (Complex.ne_zero_of_re_pos (by rw [hsre]; norm_num))
  have hnorm_sq : ‖s‖ ^ 2 = 197 / 16 := by rw [Complex.sq_norm]; exact hnormSq
  have hnorm_lo : (3.5088 : ℝ) < ‖s‖ := by
    nlinarith [hnorm_sq, hnorm_pos, sq_nonneg (‖s‖ - 3.5088)]
  have hDbound : ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖
      ≤ (1 / 12 + 3 / (2 * π ^ 2 * (1 / 4))) * ‖s‖ ^ (-(2 : ℤ)) :=
    Complex.Stirling.norm_digamma_sub_log_le' (by norm_num) s (by rw [hsre])
  have hinv_re : ((2 * s)⁻¹).re = 2 / 197 := by
    rw [Complex.inv_re, Complex.normSq_mul, Complex.mul_re]
    simp only [hsre, hsim, hnormSq]
    norm_num
  -- `Re ψ(s) = log‖s‖ − Re (2s)⁻¹ + Re (error)`, and the error's real part is `≥ −‖error‖`
  have hdecomp : (Complex.digamma s).re = Real.log ‖s‖ - 2 / 197
      + (Complex.digamma s - Complex.log s + (2 * s)⁻¹).re := by
    rw [Complex.add_re, Complex.sub_re, Complex.log_re, hinv_re]; ring
  have hDre : -‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖
      ≤ (Complex.digamma s - Complex.log s + (2 * s)⁻¹).re :=
    (abs_le.1 (Complex.abs_re_le_norm _)).1
  have hπ2 : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d6, Real.pi_pos]
  have hDbound2 : ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖ ≤ 0.06 := by
    refine hDbound.trans ?_
    rw [show ‖s‖ ^ (-(2 : ℤ)) = 16 / 197 by
      rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hnorm_sq]; norm_num]
    have hv : 3 / (2 * π ^ 2 * (1 / 4)) < 0.6080 := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith [hπ2]
    nlinarith [hv]
  -- `log‖s‖ − log π ≥ 1 − π/‖s‖ > 1 − 0.8954`
  have hlogdiff : 1 - π / ‖s‖ ≤ Real.log ‖s‖ - Real.log π := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ‖s‖ / π by positivity)
    rwa [Real.log_div hnorm_pos.ne' Real.pi_pos.ne', inv_div] at h
  have hu : π / ‖s‖ < 0.8954 := by
    rw [div_lt_iff₀ hnorm_pos]; nlinarith [Real.pi_lt_d4, hnorm_lo]
  linarith [hdecomp, hDre, hDbound2, hlogdiff, hu]

/-- The derivative floor: on `(7, ∞)`, `θ'` is bounded below by its value
`½ (Re ψ(¼+i·7/2) − log π)` at the base point `7`. -/
private theorem le_deriv_riemannSiegelTheta {x : ℝ} (hx : 7 < x) :
    ((Complex.digamma (1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2))).re - Real.log π) / 2
      ≤ deriv riemannSiegelTheta x := by
  rw [(hasDerivAt_riemannSiegelTheta (by linarith : (0 : ℝ) < x)).deriv]
  have hmono := Complex.monotoneOn_re_digamma_quarter_vertical
    (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 7)) (Set.mem_Ici.mpr (by linarith : (0:ℝ) ≤ x)) hx.le
  simp only at hmono
  linarith

/-- **`θ` is strictly increasing on `gramDomain = [7, ∞)`.** -/
theorem strictMonoOn_riemannSiegelTheta_gramDomain :
    StrictMonoOn riemannSiegelTheta gramDomain := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 7)
    (continuousOn_riemannSiegelTheta.mono (Ici_subset_Ici.mpr (by norm_num))) fun x hx ↦ ?_
  rw [interior_Ici] at hx
  linarith [le_deriv_riemannSiegelTheta (Set.mem_Ioi.mp hx), log_pi_lt_re_digamma_quarter_seven]

/-- `θ` is continuous on `gramDomain = [7, ∞)`. -/
theorem continuousOn_riemannSiegelTheta_gramDomain : ContinuousOn riemannSiegelTheta gramDomain :=
  continuousOn_riemannSiegelTheta.mono (Ici_subset_Ici.mpr (by norm_num))

/-- `θ(t) → ∞` as `t → ∞`. -/
theorem tendsto_riemannSiegelTheta_atTop : atTop.Tendsto riemannSiegelTheta atTop := by
  set c := ((Complex.digamma (1 / 4 + Complex.I * (((7 : ℝ) : ℂ) / 2))).re - Real.log π) / 2
    with hc
  have hc_pos : 0 < c := by rw [hc]; linarith [log_pi_lt_re_digamma_quarter_seven]
  have hcont := continuousOn_riemannSiegelTheta.mono (Ici_subset_Ici.mpr (by norm_num : (0:ℝ) ≤ 7))
  have hdiff : DifferentiableOn ℝ riemannSiegelTheta (interior (Ici (7 : ℝ))) := by
    rw [interior_Ici]
    exact fun x hx ↦ (hasDerivAt_riemannSiegelTheta (by linarith [Set.mem_Ioi.mp hx] :
      (0 : ℝ) < x)).differentiableAt.differentiableWithinAt
  have hlin : ∀ x ∈ Ici (7 : ℝ), c * (x - 7) ≤ riemannSiegelTheta x - riemannSiegelTheta 7 :=
    fun x hx ↦ Convex.mul_sub_le_image_sub_of_le_deriv (convex_Ici 7) hcont hdiff
      (fun x hx ↦ hc ▸ le_deriv_riemannSiegelTheta (by rwa [interior_Ici] at hx))
      7 Set.self_mem_Ici x hx (Set.mem_Ici.mp hx)
  have hg : Tendsto (fun x : ℝ ↦ riemannSiegelTheta 7 + c * (x - 7)) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (Tendsto.const_mul_atTop hc_pos (tendsto_atTop_add_const_right atTop (-7) tendsto_id))
  refine tendsto_atTop_mono' atTop ?_ hg
  filter_upwards [eventually_ge_atTop (7 : ℝ)] with x hx
  linarith [hlin x (Set.mem_Ici.mpr hx)]

/-- **`θ(7) ≤ 0`.** -/
private theorem riemannSiegelTheta_seven_nonpos : riemannSiegelTheta 7 ≤ 0 := by
  have herr : riemannSiegelThetaStirlingErrorBound 1 0 = 12 / π ^ 2 := by
    simp only [riemannSiegelThetaStirlingErrorBound, Nat.cast_one, mul_one,
      Nat.cast_zero, add_zero]
    rw [show (Nat.factorial (2 * 1 + 1) : ℝ) = 6 by norm_num [Nat.factorial],
      show (2 * Real.pi) ^ (2 * 1) = 4 * π ^ 2 by ring,
      show ((1 / 4 : ℝ)) ^ (-2 : ℤ) = 16 by norm_num]
    have : (0 : ℝ) < π ^ 2 := by positivity
    field_simp
    ring
  have hθ := (abs_le.1 (abs_riemannSiegelTheta_sub_stirling_le (M := 1)
    (le_refl 1) (T := 7) (by norm_num : (0 : ℝ) ≤ 7))).2
  rw [herr] at hθ
  set w : ℂ := 1 / 4 + Complex.I * ((7 : ℝ) / 2) with hw_def
  have hwre : w.re = 1 / 4 := by rw [hw_def]; simp
  have hwim : w.im = 7 / 2 := by rw [hw_def]; simp
  have hnormSq : Complex.normSq w = 197 / 16 := by rw [Complex.normSq_apply, hwre, hwim]; norm_num
  have hnorm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr (Complex.ne_zero_of_re_pos (by rw [hwre]; norm_num))
  have hnorm_le4 : ‖w‖ ≤ 4 := by nlinarith [Complex.sq_norm w, hnormSq, norm_nonneg w]
  have hargnn : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.mpr (by rw [hwim]; norm_num)
  have hinvim : (w⁻¹).im ≤ 0 := by rw [Complex.inv_im, hwim, hnormSq]; norm_num
  have hlog_le : Real.log ‖w‖ ≤ Real.log 4 := Real.log_le_log hnorm_pos hnorm_le4
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  -- crude upper bound on the imaginary part of the order-1 Stirling polynomial at `w`
  have hIm : (Complex.Stirling.logGammaStirling 1 w).im ≤ 7 * Real.log 2 - 7 / 2 := by
    rw [Complex.Stirling.logGammaStirling]
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have hcoeff : (↑(bernoulli (2 * 1)) : ℂ) / (2 * (↑(1 : ℕ) : ℂ) * (2 * (↑(1 : ℕ) : ℂ) - 1))
        = ((1 / 12 : ℝ) : ℂ) := by
      rw [show (2 * 1 : ℕ) = 2 from rfl, bernoulli_two]; push_cast; norm_num
    have hval : ((w - 1 / 2) * Complex.log w - w + 1 / 2 * (↑(Real.log (2 * Real.pi)) : ℂ)
        + ((1 / 12 : ℝ) : ℂ) * w⁻¹).im
        = (w.re - 1 / 2) * Complex.arg w + w.im * Real.log ‖w‖ - w.im
          + (1 / 12) * (w⁻¹).im := by
      rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num]
      simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.sub_re,
        Complex.ofReal_im, Complex.ofReal_re, Complex.log_im, Complex.log_re]
      ring
    rw [show w ^ (1 - 2 * ((1 : ℕ) : ℤ)) = w⁻¹ by norm_num, hcoeff, hval, hwre, hwim]
    nlinarith [hargnn, hlog_le, hinvim, hlog4]
  have hπ2 : (9.84 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d6, Real.pi_pos]
  have hlogπ : 1 < Real.log π := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9, Real.pi_gt_d6])
  have h12 : 12 / π ^ 2 < 1.22 := by rw [div_lt_iff₀ (by positivity)]; nlinarith [hπ2]
  nlinarith [hθ, hIm, h12, hlogπ, Real.log_two_lt_d9]

/-- `θ(7) ≤ n·π` for every `n : ℕ`: the base point `7` lies below every gram point. -/
theorem riemannSiegelTheta_seven_le (n : ℕ) :
    riemannSiegelTheta 7 ≤ n * π :=
  le_trans riemannSiegelTheta_seven_nonpos (by positivity)

