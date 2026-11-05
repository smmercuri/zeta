/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannVonMangoldt.Halving
public import Zeta.RiemannVonMangoldt.ZeroCounting

/-!
# The exact Riemann–von Mangoldt formula

The exact formula `N(T) = θ(T)/π + 1 + S(T)`, for `T > 0` not the ordinate of a zero of `ζ`
(`thm:N_formula`).

## Main results

- `riemannXi_re_mem_Ioo_of_eq_zero`: every zero of `ξ` lies in the open critical strip
  `0 < Re s < 1`.
- `riemannZeta_eq_zero_of_riemannXi_eq_zero`: every zero of `ξ` is a zero of `ζ`.
- `riemannXi_ne_zero_of_im_eq_zero`: `ξ` has no real zeros.
- `riemannZeta.N_eq`, `riemannZeta.N_eq_of_forall_re_mem_Ico`: the formula, under the ordinate
  hypothesis and under its certifiable segment form.
-/
@[expose] public section


open Complex Set


/-- **Zeros of `ξ` lie in the open critical strip.** If `ξ s = 0` then `0 < Re s < 1`. -/
theorem riemannXi_re_mem_Ioo_of_eq_zero {s : ℂ} (hs : riemannXi s = 0) :
    s.re ∈ Set.Ioo (0 : ℝ) 1 := by
  -- `ξ ≠ 0` whenever `Re z ≥ 1`.
  have hge : ∀ z : ℂ, 1 ≤ z.re → riemannXi z ≠ 0 := by
    intro z hz hzero
    have hz0 : z ≠ 0 := by rintro rfl; rw [Complex.zero_re] at hz; norm_num at hz
    have hz1 : z ≠ 1 := by rintro rfl; rw [riemannXi_one] at hzero; norm_num at hzero
    have hΓ : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [riemannXi_eq_prefactor_mul hz0 hz1 hΓ] at hzero
    exact mul_ne_zero (prefactor_ne_zero_of hz0 hz1 hΓ)
      (riemannZeta_ne_zero_of_one_le_re hz) hzero
  refine ⟨?_, ?_⟩
  · by_contra h
    rw [not_lt] at h
    have h1 : 1 ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    exact hge (1 - s) h1 (by rw [riemannXi_one_sub]; exact hs)
  · by_contra h
    rw [not_lt] at h
    exact hge s h hs

/-- **Every zero of `ξ` is a zero of `ζ`.** -/
theorem riemannZeta_eq_zero_of_riemannXi_eq_zero {s : ℂ} (hs : riemannXi s = 0) :
    riemannZeta s = 0 :=
  have h := riemannXi_re_mem_Ioo_of_eq_zero hs
  (riemannXi_eq_zero_iff h.1 h.2).mp hs

/-- **`ξ` has no real zeros.** -/
theorem riemannXi_ne_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : riemannXi z ≠ 0 := by
  intro hξ
  obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
  have hz' : z = (↑z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [hz'] at hξ
  exact riemannXi_ofReal_ne_zero_of_mem_Icc ⟨by linarith, by linarith⟩ hξ

/-- **Contour factorisation of `ξ` on a segment.** On an affine segment `lineSeg z₀ z₁` that
stays in the right half-plane, avoids `1`, and where `ζ` is non-vanishing, the argument variation
of `ξ` splits as that of the polynomial factor, `Γ_ℝ`, and `ζ`. -/
private theorem argVariation_riemannXi_seg (z₀ z₁ : ℂ)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (lineSeg z₀ z₁ u).re)
    (hne1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 1)
    (hζ : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannZeta (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannXi (lineSeg z₀ z₁ u))
      = argVariation 0 1
          (fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
        + argVariation 0 1 (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u))
        + argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) := by
  have hsne : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 0 := by
    intro u hu heq; simpa [heq] using hre u hu
  -- continuity of the three factors on `[0, 1]`
  have hPcont : ContinuousOn
      (fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1))) (Set.Icc 0 1) :=
    (continuous_const.mul ((continuous_lineSeg z₀ z₁).mul
      ((continuous_lineSeg z₀ z₁).sub continuous_const))).continuousOn
  have hGcont : ContinuousOn (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u)) (Set.Icc 0 1) := by
    intro u hu
    exact ContinuousAt.comp_continuousWithinAt (g := Complex.Gammaℝ) (f := lineSeg z₀ z₁)
      (Complex.analyticAt_Gammaℝ (hre u hu)).continuousAt
      (continuous_lineSeg z₀ z₁).continuousWithinAt
  have hZcont : ContinuousOn (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc 0 1) := by
    intro u hu
    exact ContinuousAt.comp_continuousWithinAt (g := riemannZeta) (f := lineSeg z₀ z₁)
      (differentiableAt_riemannZeta (hne1 u hu)).continuousAt
      (continuous_lineSeg z₀ z₁).continuousWithinAt
  -- non-vanishing of the three factors on `[0, 1]`
  have hPne : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)) ≠ 0 := fun u hu ↦
    mul_ne_zero (one_div_ne_zero two_ne_zero)
      (mul_ne_zero (hsne u hu) (sub_ne_zero.mpr (hne1 u hu)))
  have hGne : ∀ u ∈ Set.Icc (0 : ℝ) 1, Complex.Gammaℝ (lineSeg z₀ z₁ u) ≠ 0 :=
    fun u hu ↦ Complex.Gammaℝ_ne_zero_of_re_pos (hre u hu)
  -- the factorisation, valid pointwise on `[0, 1]`
  have hEq : Set.EqOn (fun u ↦ riemannXi (lineSeg z₀ z₁ u))
      (((fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
        * (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u)))
        * (fun u ↦ riemannZeta (lineSeg z₀ z₁ u))) (Set.Icc 0 1) := by
    intro u hu
    change riemannXi (lineSeg z₀ z₁ u) = _
    rw [riemannXi_eq_prefactor_mul (hsne u hu) (hne1 u hu)
      (Complex.Gammaℝ_ne_zero_of_re_pos (hre u hu))]
    simp only [Pi.mul_apply]
  rw [argVariation_congr zero_le_one hEq,
    argVariation_mul zero_le_one (hPcont.mul hGcont)
      (fun u hu ↦ mul_ne_zero (hPne u hu) (hGne u hu)) hZcont hζ,
    argVariation_mul zero_le_one hPcont hPne hGcont hGne]

/-- The real and imaginary parts of the corners `-1` and `2 + iT` of the counting rectangle. -/
private theorem rectangle_corner_eq (T : ℝ) :
    (2 + I * (T : ℂ)).re = 2 ∧ (2 + I * (T : ℂ)).im = T
      ∧ (-1 : ℂ).re = -1 ∧ (-1 : ℂ).im = 0 :=
  ⟨by simp, by simp, by norm_num, by norm_num⟩

/-- **`ξ ≠ 0` on the boundary of the counting rectangle** with corners `-1` and `2 + iT`, for
`T > 0` not the ordinate of a zero of `ζ`. -/
private theorem riemannXi_ne_zero_of_mem_rectangleBorder {T : ℝ}
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) {ρ : ℂ}
    (hρ : ρ ∈ RectangleBorder (-1) (2 + I * (T : ℂ))) : riemannXi ρ ≠ 0 := by
  intro hξ
  obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
  obtain ⟨hwre, hwim, hm1re, hm1im⟩ := rectangle_corner_eq T
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
    hwre, hwim, hm1re, hm1im] at hρ
  rcases hρ with ((⟨_, him⟩ | ⟨hre, _⟩) | ⟨_, him⟩) | ⟨hre, _⟩
  · -- bottom edge: `Im ρ = 0`, so `ρ` is real and `ξ ρ ≠ 0`.
    exact riemannXi_ne_zero_of_im_eq_zero him hξ
  · -- left edge: `Re ρ = -1`, contradicting `0 < Re ρ`.
    rw [hre] at hr0; norm_num at hr0
  · -- top edge: `Im ρ = T`, so `ζ ρ = 0`, contradicting the hypothesis on `T`.
    exact hT' ρ him (riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)
  · -- right edge: `Re ρ = 2`, contradicting `Re ρ < 1`.
    rw [hre] at hr1; norm_num at hr1


/-- **The exact Riemann–von Mangoldt formula** (`thm:N_formula`). For `T > 0` not the ordinate of
a zero of `ζ`, `N(T) = θ(T)/π + 1 + S(T)`. -/
theorem riemannZeta.N_eq {T : ℝ} (hT : 0 < T)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) :
    riemannZeta.N T = riemannSiegelTheta T / Real.pi + 1 + argZeta T := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  -- corner data for the rectangle `[-1, 2] × [0, T]`
  obtain ⟨hwre, hwim, hm1re, hm1im⟩ := rectangle_corner_eq T
  have hle_re : (-1 : ℂ).re ≤ (2 + I * (T : ℂ)).re := by rw [hm1re, hwre]; norm_num
  have hle_im : (-1 : ℂ).im ≤ (2 + I * (T : ℂ)).im := by rw [hm1im, hwim]; exact hT.le
  -- the zeros of `ξ` in the rectangle are exactly the zeros of `N(T)`'s box
  have hRS : (Rectangle (-1) (2 + I * (T : ℂ)) ∩ {ρ : ℂ | riemannXi ρ = 0})
      = {z : ℂ | riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1
          ∧ z.im ∈ Set.Ioo (0 : ℝ) T} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hzR, hξ⟩
      obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
      rw [mem_Rect hle_re hle_im,
        hm1re, hm1im, hwre, hwim] at hzR
      obtain ⟨_, _, hzim0, hzimT⟩ := hzR
      exact ⟨hξ, ⟨hr0, hr1⟩,
        hzim0.lt_of_ne fun heq ↦ riemannXi_ne_zero_of_im_eq_zero heq.symm hξ,
        hzimT.lt_of_ne fun heq ↦ hT' z heq (riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)⟩
    · rintro ⟨hξ, ⟨hr0, hr1⟩, hi0, hiT⟩
      refine ⟨?_, hξ⟩
      rw [mem_Rect hle_re hle_im,
        hm1re, hm1im, hwre, hwim]
      exact ⟨by linarith, by linarith, hi0.le, hiT.le⟩
  -- finiteness of that zero set
  have hfin : (Rectangle (-1) (2 + I * (T : ℂ)) ∩ {ρ : ℂ | riemannXi ρ = 0}).Finite := by
    have hcompact : IsCompact (Rectangle (-1) (2 + I * (T : ℂ))) :=
      isCompact_uIcc.reProdIm isCompact_uIcc
    refine (riemannZeta.zeroes_on_Compact_finite' hcompact).subset ?_
    rintro z ⟨hzR, hξ⟩
    exact ⟨hzR, riemannZeta_eq_zero_of_riemannXi_eq_zero hξ⟩
  -- the argument principle on the rectangle
  have hap : (∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ))
      = 1 / (2 * Real.pi) * rectangleArgVariation riemannXi (-1) (2 + I * (T : ℂ)) := by
    refine rectangle_zero_count_eq_argVariation (z := (-1 : ℂ)) (w := 2 + I * (T : ℂ))
      (z₀ := (2 : ℂ)) analyticOnNhd_riemannXi
      isConnected_univ (Set.mem_univ _) ?_ (Set.subset_univ _) hle_re hle_im
      (fun ρ hρ ↦ riemannXi_ne_zero_of_mem_rectangleBorder hT' hρ) hfin
    have h2 := riemannXi_ofReal_ne_zero_of_mem_Icc (σ := 2) ⟨by norm_num, le_refl _⟩
    simpa using h2
  -- bridge the box tsum (from `N`) to the finite sum (from the argument principle)
  have hbridge : (∑' ρ : {z : ℂ // riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1
        ∧ z.im ∈ Set.Ioo (0 : ℝ) T},
      (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
      = ∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ) := by
    rw [← Finset.tsum_subtype' hfin.toFinset
        (fun ρ ↦ (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ)), hfin.coe_toFinset]
    exact (Equiv.setCongr hRS.symm).tsum_eq
      (fun ρ ↦ (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
  -- the halving identity
  have hhalf := argVariation_riemannXi_rectangle_eq_two_mul hT hT'
  -- the contour factorisation `Δ_{L_T} arg ξ = Δ poly + Δ Γ_ℝ + Δ ζ`
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have hc2re : (1 / 2 + I * (T : ℂ)).re = 1 / 2 := by simp
  have hc2im : (1 / 2 + I * (T : ℂ)).im = T := by simp
  have hcontour : argVariationContourL riemannXi T
      = argVariationContourL (fun s ↦ (1 / 2 : ℂ) * (s * (s - 1))) T
        + argVariationContourL Complex.Gammaℝ T + argVariationContourL riemannZeta T := by
    have hseg1 := argVariation_riemannXi_seg 2 (2 + I * (T : ℂ))
      (fun u _ ↦ by rw [lineSeg_re, h2re, hwre]; norm_num)
      (fun u _ heq ↦ by
        have := congrArg Complex.re heq
        rw [lineSeg_re, h2re, hwre, Complex.one_re] at this; norm_num at this)
      (fun u _ ↦ riemannZeta_ne_zero_of_one_le_re (by rw [lineSeg_re, h2re, hwre]; norm_num))
    have hseg2 := argVariation_riemannXi_seg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ))
      (fun u hu ↦ by rw [lineSeg_re, hwre, hc2re]; nlinarith [hu.1, hu.2])
      (fun u _ heq ↦ by
        have := congrArg Complex.im heq
        rw [lineSeg_im, hwim, hc2im, Complex.one_im] at this
        simp only [sub_self, mul_zero, add_zero] at this; exact hT.ne' this)
      (fun u _ ↦ hT' _ (by rw [lineSeg_im, hwim, hc2im]; ring))
    simp only [argVariationContourL]
    rw [hseg1, hseg2]; ring
  -- the three contour pieces
  rw [argVariation_poly_L hT, argVariation_GammaPi_L hT] at hcontour
  have hZval : argVariationContourL riemannZeta T = Real.pi * argZeta T := by
    rw [argZeta]; field_simp
  -- assemble
  rw [riemannZeta.N_eq_tsum_riemannXi_order, hbridge, hap, hhalf, hcontour, hZval]
  field_simp
  ring

/-- **The exact Riemann–von Mangoldt formula from a certifiable hypothesis.** As
`riemannZeta.N_eq`, but assuming only non-vanishing of `ζ` on the segment `Re ∈ [½, 1)` at height
`T` — the form a finite ball-arithmetic certificate produces. -/
theorem riemannZeta.N_eq_of_forall_re_mem_Ico {T : ℝ} (hT : 0 < T)
    (h : ∀ σ : ℝ, σ ∈ Set.Ico (1 / 2 : ℝ) 1 →
      riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    riemannZeta.N T = riemannSiegelTheta T / Real.pi + 1 + argZeta T :=
  riemannZeta.N_eq hT (riemannZeta_ne_zero_of_forall_re_mem_Ico hT h)
