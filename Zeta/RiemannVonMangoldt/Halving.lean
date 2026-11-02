/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannVonMangoldt.GammaFactor
public import Zeta.RiemannVonMangoldt.RealAxis

/-!
# Halving the boundary argument variation of `ξ`

For `T > 0` not the ordinate of a zero of `ζ`, the boundary argument variation of `ξ` around the
rectangle with corners `-1` and `2 + iT` is twice its variation along the contour
`L_T : 2 → 2 + iT → ½ + iT`.

## Main results

- `argVariation_conj`: conjugating the integrand negates the argument variation.
- `riemannXi_ne_zero_of_one_lt_re`, `riemannXi_ne_zero_of_zeta_ne_zero_of_im_ne_zero`: two
  non-vanishing criteria for `ξ`.
- `riemannXi_pos_of_mem_Icc`: `ξ > 0` on the real segment `[-1, 2]`.
- `argVariation_riemannXi_rectangle_eq_two_mul`: `Δ_{∂R} arg ξ = 2 Δ_{L_T} arg ξ`.
-/
@[expose] public section


open Complex Set


variable {a b : ℝ}

/-- **Conjugation negates the argument variation** of a continuous nowhere-zero `φ`. -/
theorem argVariation_conj (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a b (fun u => starRingEnd ℂ (φ u)) = - argVariation a b φ := by
  obtain ⟨g, hg, -⟩ :=
    exists_isContLog hab hφ h0 (Complex.exp_log (h0 a (Set.left_mem_Icc.mpr hab)))
  have hg' : IsContLog a b (fun u => starRingEnd ℂ (φ u)) (fun u => starRingEnd ℂ (g u)) := by
    refine ⟨Complex.continuous_conj.comp_continuousOn hg.1, fun u hu => ?_⟩
    change Complex.exp (starRingEnd ℂ (g u)) = starRingEnd ℂ (φ u)
    rw [Complex.exp_conj, hg.2 u hu]
  rw [argVariation_eq_of_isContLog hab hg', argVariation_eq_of_isContLog hab hg]
  simp only [Complex.conj_im]
  ring

/-! ### Non-vanishing and positivity of `ξ` -/

/-- `ξ(s) ≠ 0` for `Re s > 1`. -/
theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp only [Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by rintro rfl; simp only [Complex.one_re] at hs; linarith
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  rw [riemannXi_eq_prefactor_mul hs0 hs1 hΓ]
  exact mul_ne_zero (prefactor_ne_zero_of hs0 hs1 hΓ) hζ

/-- `ξ(s) ≠ 0` whenever `Im s ≠ 0` and `ζ(s) ≠ 0`. -/
theorem riemannXi_ne_zero_of_zeta_ne_zero_of_im_ne_zero {s : ℂ} (him : s.im ≠ 0)
    (hζ : riemannZeta s ≠ 0) : riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at him
  have hs1 : s ≠ 1 := by rintro rfl; simp at him
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_im_ne_zero him
  rw [riemannXi_eq_prefactor_mul hs0 hs1 hΓ]
  exact mul_ne_zero (prefactor_ne_zero_of hs0 hs1 hΓ) hζ

/-- `ξ` is real on the real axis: `(ξ σ).im = 0` for real `σ`. -/
private theorem riemannXi_ofReal_im_eq_zero (σ : ℝ) : (riemannXi (σ : ℂ)).im = 0 := by
  have hc := riemannXi_conj (σ : ℂ)
  rw [Complex.conj_ofReal] at hc
  have := congrArg Complex.im hc
  rw [Complex.conj_im] at this
  linarith

/-- **`ξ > 0` on the real segment `[-1, 2]`**, where it is also real. -/
theorem riemannXi_pos_of_mem_Icc {σ : ℝ} (hσ : σ ∈ Icc (-1 : ℝ) 2) :
    0 < (riemannXi (σ : ℂ)).re ∧ (riemannXi (σ : ℂ)).im = 0 := by
  refine ⟨?_, riemannXi_ofReal_im_eq_zero σ⟩
  by_contra hcon
  rw [not_lt] at hcon
  set g : ℝ → ℝ := fun x => (riemannXi (x : ℂ)).re with hg
  have hgcont : ContinuousOn g (Set.uIcc 0 σ) :=
    (Complex.continuous_re.comp
      (differentiable_riemannXi.continuous.comp Complex.continuous_ofReal)).continuousOn
  have hg0 : g 0 = 1 / 2 := by simp [hg, Complex.ofReal_zero, riemannXi_zero]
  have hmem : (0 : ℝ) ∈ Set.uIcc (g 0) (g σ) :=
    Set.mem_uIcc.mpr (Or.inr ⟨hcon, by rw [hg0]; norm_num⟩)
  obtain ⟨c, hc, hgc⟩ := intermediate_value_uIcc hgcont hmem
  have hsub : Set.uIcc 0 σ ⊆ Icc (-1 : ℝ) 2 :=
    Set.uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ hσ
  have hcIcc : c ∈ Icc (-1 : ℝ) 2 := hsub hc
  have hzero : riemannXi (c : ℂ) = 0 :=
    Complex.ext (by simpa [hg] using hgc) (riemannXi_ofReal_im_eq_zero c)
  exact riemannXi_ofReal_ne_zero_of_mem_Icc hcIcc hzero

/-! ### Argument variation along `lineSeg` edges -/

/-- `ξ ∘ lineSeg z₀ z₁` is continuous on `[0, 1]` (`ξ` is entire). -/
private theorem riemannXi_lineSeg_continuousOn (z₀ z₁ : ℂ) :
    ContinuousOn (fun u => riemannXi (lineSeg z₀ z₁ u)) (Set.Icc 0 1) :=
  (differentiable_riemannXi.continuous.comp (continuous_lineSeg z₀ z₁)).continuousOn

/-- `ξ ≠ 0` along a `lineSeg` edge whose abscissa is constantly `2` (`Re = 2 > 1`). -/
private theorem riemannXi_lineSeg_ne_zero_of_re_eq_two {z₀ z₁ : ℂ} (h0 : z₀.re = 2)
    (h1 : z₁.re = 2) : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ≠ 0 := by
  intro u _
  refine riemannXi_ne_zero_of_one_lt_re ?_
  rw [lineSeg_re, h0, h1]; norm_num

/-- `ξ ≠ 0` along a `lineSeg` edge at constant height `Im = T`, when `T > 0` is not an ordinate
of a zero of `ζ`. -/
private theorem riemannXi_lineSeg_ne_zero_of_im_eq_T {T : ℝ} (hT : T ≠ 0)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) {z₀ z₁ : ℂ} (h0 : z₀.im = T) (h1 : z₁.im = T) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ≠ 0 := by
  intro u _
  have him : (lineSeg z₀ z₁ u).im = T := by rw [lineSeg_im, h0, h1]; ring
  exact riemannXi_ne_zero_of_zeta_ne_zero_of_im_ne_zero (by rw [him]; exact hT) (hT' _ him)

/-- **Splitting a `lineSeg` edge at an interior parameter** `t ∈ [0, 1]`: the argument variation
over the segment is the sum of the variations over its two halves. -/
private theorem argVariation_lineSeg_split {f : ℂ → ℂ} (z₀ z₁ : ℂ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hcont : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc 0 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, f (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u => f (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u => f (lineSeg z₀ (lineSeg z₀ z₁ t) u))
        + argVariation 0 1 (fun u => f (lineSeg (lineSeg z₀ z₁ t) z₁ u)) := by
  have hmap1 : Set.MapsTo (fun v : ℝ => t * v) (Set.Icc 0 1) (Set.Icc 0 t) := by
    intro v hv; refine ⟨?_, ?_⟩ <;> nlinarith [hv.1, hv.2, ht0, ht1]
  have hmap2 : Set.MapsTo (fun v : ℝ => t + (1 - t) * v) (Set.Icc 0 1) (Set.Icc t 1) := by
    intro v hv; refine ⟨?_, ?_⟩ <;> nlinarith [hv.1, hv.2, ht0, ht1]
  have hcont1 : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc 0 t) :=
    hcont.mono (Set.Icc_subset_Icc le_rfl ht1)
  have hne1 : ∀ u ∈ Set.Icc (0 : ℝ) t, f (lineSeg z₀ z₁ u) ≠ 0 :=
    fun u hu => hne u ⟨hu.1, hu.2.trans ht1⟩
  have hcont2 : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc t 1) :=
    hcont.mono (Set.Icc_subset_Icc ht0 le_rfl)
  have hne2 : ∀ u ∈ Set.Icc t (1 : ℝ), f (lineSeg z₀ z₁ u) ≠ 0 :=
    fun u hu => hne u ⟨ht0.trans hu.1, hu.2⟩
  have e1 : (fun v : ℝ => f (lineSeg z₀ z₁ (t * v)))
      = (fun u => f (lineSeg z₀ (lineSeg z₀ z₁ t) u)) := by
    funext v; congr 1; simp only [lineSeg]; push_cast; ring
  have e2 : (fun v : ℝ => f (lineSeg z₀ z₁ (t + (1 - t) * v)))
      = (fun u => f (lineSeg (lineSeg z₀ z₁ t) z₁ u)) := by
    funext v; congr 1; simp only [lineSeg]; push_cast; ring
  have h1 : argVariation 0 t (fun u => f (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u => f (lineSeg z₀ (lineSeg z₀ z₁ t) u)) := by
    rw [← e1]
    exact (argVariation_comp ht0 zero_le_one (by fun_prop) hmap1
      (by show t * 0 = 0; ring) (by show t * 1 = t; ring) hcont1 hne1).symm
  have h2 : argVariation t 1 (fun u => f (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u => f (lineSeg (lineSeg z₀ z₁ t) z₁ u)) := by
    rw [← e2]
    exact (argVariation_comp ht1 zero_le_one (by fun_prop) hmap2
      (by show t + (1 - t) * 0 = t; ring) (by show t + (1 - t) * 1 = 1; ring) hcont2 hne2).symm
  rw [argVariation_trans ht0 ht1 hcont hne, h1, h2]

/-- **Reversing a `lineSeg` edge negates its argument variation.** -/
private theorem argVariation_lineSeg_swap {f : ℂ → ℂ} (z₀ z₁ : ℂ)
    (hcont : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc 0 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, f (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u => f (lineSeg z₁ z₀ u))
      = - argVariation 0 1 (fun u => f (lineSeg z₀ z₁ u)) := by
  rw [← argVariation_reverse zero_le_one hcont hne]
  congr 1; funext u
  show f (lineSeg z₁ z₀ u) = f (lineSeg z₀ z₁ (0 + 1 - u))
  congr 1
  simp only [lineSeg]; push_cast; ring

/-- The reflection `ρ(s) = 1 - conj s` sends `ξ` to its conjugate. -/
private theorem riemannXi_reflect (s : ℂ) :
    riemannXi (1 - starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  rw [riemannXi_one_sub, riemannXi_conj]

/-- **The reflection `ρ(s) = 1 - conj s` negates the argument variation of `ξ` along a `lineSeg`
edge**, carrying `z₀ → z₁` to `(1 - conj z₀) → (1 - conj z₁)`. -/
private theorem argVariation_lineSeg_reflect {z₀ z₁ : ℂ}
    (hcont : ContinuousOn (fun u => riemannXi (lineSeg z₀ z₁ u)) (Set.Icc 0 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1
        (fun u => riemannXi (lineSeg (1 - starRingEnd ℂ z₀) (1 - starRingEnd ℂ z₁) u))
      = - argVariation 0 1 (fun u => riemannXi (lineSeg z₀ z₁ u)) := by
  rw [← argVariation_conj zero_le_one hcont hne]
  congr 1; funext u
  show riemannXi (lineSeg (1 - starRingEnd ℂ z₀) (1 - starRingEnd ℂ z₁) u)
      = starRingEnd ℂ (riemannXi (lineSeg z₀ z₁ u))
  rw [← riemannXi_reflect]
  congr 1
  simp only [lineSeg, map_add, map_sub, map_mul, Complex.conj_ofReal]
  ring

/-- The argument variation of `ξ` along a `lineSeg` edge lying on the real segment `[-1, 2]`
vanishes. -/
private theorem argVariation_riemannXi_real_eq_zero {z₀ z₁ : ℂ}
    (hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∃ x ∈ Icc (-1 : ℝ) 2, lineSeg z₀ z₁ u = (x : ℂ)) :
    argVariation 0 1 (fun u => riemannXi (lineSeg z₀ z₁ u)) = 0 := by
  have hsp : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ∈ Complex.slitPlane := by
    intro u hu
    obtain ⟨x, hx, hxe⟩ := hpt u hu
    rw [hxe, Complex.mem_slitPlane_iff]; left
    exact (riemannXi_pos_of_mem_Icc hx).1
  have harg : ∀ {x : ℝ}, x ∈ Icc (-1 : ℝ) 2 → (riemannXi (x : ℂ)).arg = 0 := by
    intro x hx
    rw [Complex.arg_eq_zero_iff]
    exact ⟨(riemannXi_pos_of_mem_Icc hx).1.le, (riemannXi_pos_of_mem_Icc hx).2⟩
  obtain ⟨x0, hx0, hx0e⟩ := hpt 0 (by norm_num)
  obtain ⟨x1, hx1, hx1e⟩ := hpt 1 (by norm_num)
  rw [lineSeg_zero] at hx0e
  rw [lineSeg_one] at hx1e
  rw [argVariation_eq_arg_sub_arg zero_le_one (riemannXi_lineSeg_continuousOn z₀ z₁) hsp]
  simp only [lineSeg_one, lineSeg_zero]
  rw [hx0e, hx1e, harg hx0, harg hx1]
  ring

/-! ### The halving identity -/

/-- **Halving the contour.** For `T > 0` not the ordinate of a zero of `ζ`, the boundary argument
variation of `ξ` around the rectangle with corners `-1` and `2 + iT` is twice the variation along
`L_T : 2 → 2 + iT → ½ + iT`: `Δ_{∂R} arg ξ = 2 Δ_{L_T} arg ξ`. -/
theorem argVariation_riemannXi_rectangle_eq_two_mul {T : ℝ} (hT : 0 < T)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) :
    rectangleArgVariation riemannXi (-1) (2 + I * (T : ℂ))
      = 2 * argVariationContourL riemannXi T := by
  -- corner simplifications of the rectangle boundary
  have c0 : ((↑(-1 : ℂ).re : ℂ) + ↑(-1 : ℂ).im * I) = (-1 : ℂ) := Complex.re_add_im _
  have c1 : ((↑(2 + I * (T : ℂ)).re : ℂ) + ↑(-1 : ℂ).im * I) = 2 := by apply Complex.ext <;> simp
  have c2 : ((↑(2 + I * (T : ℂ)).re : ℂ) + ↑(2 + I * (T : ℂ)).im * I) = 2 + I * (T : ℂ) :=
    Complex.re_add_im _
  have c3 : ((↑(-1 : ℂ).re : ℂ) + ↑(2 + I * (T : ℂ)).im * I) = -1 + I * (T : ℂ) := by
    apply Complex.ext <;> simp
  -- non-vanishing of `ξ` along the relevant edges
  have hne_right : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg 2 (2 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_re_eq_two (by simp) (by simp)
  have hne_right' : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg (2 + I * (T : ℂ)) 2 u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_re_eq_two (by simp) (by simp)
  have hne_s2 : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannXi (lineSeg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_im_eq_T hT.ne' hT' (by simp) (by simp)
  have hne_s2' : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannXi (lineSeg (1 / 2 + I * (T : ℂ)) (2 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_im_eq_T hT.ne' hT' (by simp) (by simp)
  have hne_top : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannXi (lineSeg (2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_im_eq_T hT.ne' hT' (by simp) (by simp)
  have hne_bot : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg (-1) 2 u) ≠ 0 := by
    intro u hu
    have hpt : lineSeg (-1 : ℂ) 2 u = ((-1 + u * 3 : ℝ) : ℂ) := by
      simp only [lineSeg]; push_cast; ring
    rw [hpt]; intro h
    have hmem : (-1 + u * 3 : ℝ) ∈ Icc (-1 : ℝ) 2 := ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    have := (riemannXi_pos_of_mem_Icc hmem).1
    rw [h] at this; simp at this
  -- split the bottom and top edges at their midpoints `½` and `½ + iT`
  have hsplit_bot : argVariation 0 1 (fun u => riemannXi (lineSeg (-1) 2 u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg (-1) (1 / 2) u))
        + argVariation 0 1 (fun u => riemannXi (lineSeg (1 / 2) 2 u)) := by
    have h := argVariation_lineSeg_split (f := riemannXi) (-1) 2 (t := 1 / 2)
      (by norm_num) (by norm_num) (riemannXi_lineSeg_continuousOn _ _) hne_bot
    rw [show lineSeg (-1 : ℂ) 2 (1 / 2) = (1 / 2 : ℂ) from by
      simp only [lineSeg]; push_cast; ring] at h
    exact h
  have hsplit_top :
      argVariation 0 1 (fun u => riemannXi (lineSeg (2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ)) u))
        + argVariation 0 1
            (fun u => riemannXi (lineSeg (1 / 2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u)) := by
    have h := argVariation_lineSeg_split (f := riemannXi) (2 + I * (T : ℂ)) (-1 + I * (T : ℂ))
      (t := 1 / 2) (by norm_num) (by norm_num) (riemannXi_lineSeg_continuousOn _ _) hne_top
    rw [show lineSeg (2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) (1 / 2) = (1 / 2 + I * (T : ℂ)) from by
      simp only [lineSeg]; push_cast; ring] at h
    exact h
  -- the two real sub-segments contribute nothing
  have hbot1 : argVariation 0 1 (fun u => riemannXi (lineSeg (-1) (1 / 2) u)) = 0 :=
    argVariation_riemannXi_real_eq_zero fun u hu =>
      ⟨-1 + u * (3 / 2), ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩, by
        simp only [lineSeg]; push_cast; ring⟩
  have hbot2 : argVariation 0 1 (fun u => riemannXi (lineSeg (1 / 2) 2 u)) = 0 :=
    argVariation_riemannXi_real_eq_zero fun u hu =>
      ⟨1 / 2 + u * (3 / 2), ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩, by
        simp only [lineSeg]; push_cast; ring⟩
  -- the reflection identifies left with right and the two upper halves
  have hleft : argVariation 0 1 (fun u => riemannXi (lineSeg (-1 + I * (T : ℂ)) (-1) u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg 2 (2 + I * (T : ℂ)) u)) := by
    have hreflect := argVariation_lineSeg_reflect (z₀ := 2 + I * (T : ℂ)) (z₁ := 2)
      (riemannXi_lineSeg_continuousOn _ _) hne_right'
    have hswap := argVariation_lineSeg_swap (f := riemannXi) 2 (2 + I * (T : ℂ))
      (riemannXi_lineSeg_continuousOn _ _) hne_right
    rw [show (1 - starRingEnd ℂ (2 + I * (T : ℂ))) = -1 + I * (T : ℂ) from by
          simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring,
        show (1 - starRingEnd ℂ (2 : ℂ)) = (-1 : ℂ) from by
          simp only [map_ofNat]; norm_num] at hreflect
    rw [hreflect, hswap]; ring
  have hs2' :
      argVariation 0 1 (fun u => riemannXi (lineSeg (1 / 2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ)) u))
      := by
    have hreflect := argVariation_lineSeg_reflect (z₀ := 1 / 2 + I * (T : ℂ))
      (z₁ := 2 + I * (T : ℂ)) (riemannXi_lineSeg_continuousOn _ _) hne_s2'
    have hswap := argVariation_lineSeg_swap (f := riemannXi) (2 + I * (T : ℂ))
      (1 / 2 + I * (T : ℂ)) (riemannXi_lineSeg_continuousOn _ _) hne_s2
    rw [show (1 - starRingEnd ℂ (1 / 2 + I * (T : ℂ))) = 1 / 2 + I * (T : ℂ) from by
          simp only [map_add, map_mul, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal,
            map_ofNat]; ring,
        show (1 - starRingEnd ℂ (2 + I * (T : ℂ))) = -1 + I * (T : ℂ) from by
          simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat];
          ring] at hreflect
    rw [hreflect, hswap]; ring
  -- assemble
  rw [rectangleArgVariation, c0, c1, c2, c3]
  simp only [argVariationContourL]
  rw [hsplit_bot, hsplit_top, hbot1, hbot2, hleft, hs2']
  ring

