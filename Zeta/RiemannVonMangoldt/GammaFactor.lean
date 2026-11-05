/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gamma.HalfPlane
public import Zeta.Theta
public import Zeta.Analysis.Complex.ArgumentPrinciple
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# The argument of the `Γ` and `π` factors gives `θ`

Along the contour `L_T : 2 → 2 + iT → ½ + iT`, the archimedean factor
`Γ_ℝ(s) = π^{-s/2} Γ(s/2)` (`Complex.Gammaℝ`) is non-vanishing, and its argument variation is
the Riemann–Siegel theta function.

## Main results

- `argVariation_GammaPi_L`: `Δ_{L_T} arg Γ_ℝ = θ(T)`.
-/
@[expose] public section


open Complex Real

/-- An affine segment divides linearly: `lineSeg z₀ z₁ u / c = lineSeg (z₀/c) (z₁/c) u`. -/
private theorem lineSeg_div (z₀ z₁ c : ℂ) (u : ℝ) :
    lineSeg z₀ z₁ u / c = lineSeg (z₀ / c) (z₁ / c) u := by
  simp only [lineSeg]; ring

/-- Reversing the parameter swaps the endpoints of an affine segment:
`lineSeg z₀ z₁ (1 - u) = lineSeg z₁ z₀ u`. -/
private theorem lineSeg_one_sub (z₀ z₁ : ℂ) (u : ℝ) :
    lineSeg z₀ z₁ (1 - u) = lineSeg z₁ z₀ u := by
  simp only [lineSeg]; push_cast; ring

/-! ### The `π`-factor -/

/-- The argument variation of the `π`-factor `π^{-s/2}` over a single affine segment, the
difference of the imaginary parts of `(log π)(-s/2)` at the endpoints. -/
private theorem argVariation_cpow_pi_seg (z₀ z₁ : ℂ) :
    argVariation 0 1 (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
      = Real.log π * (-z₁.im / 2) - Real.log π * (-z₀.im / 2) := by
  have hπ : (↑π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hlog : IsContLog 0 1 (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
      (fun u ↦ (↑(Real.log π) : ℂ) * (-(lineSeg z₀ z₁ u) / 2)) :=
    ⟨(continuous_const.mul ((continuous_lineSeg z₀ z₁).neg.div_const 2)).continuousOn,
      fun u _ ↦ by
        simp only [Complex.cpow_def_of_ne_zero hπ, Complex.ofReal_log Real.pi_pos.le]⟩
  rw [argVariation_eq_of_isContLog zero_le_one hlog]
  simp only [lineSeg_zero, lineSeg_one, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.neg_im, Complex.div_ofNat_im, Complex.neg_re, Complex.div_ofNat_re]
  ring

/-- **The `π`-factor.** Along `L_T : 2 → 2 + iT → ½ + iT`,
`Δ_{L_T} arg(π^{-s/2}) = -(T/2) log π`. -/
private theorem argVariationContourL_cpow_pi {T : ℝ} :
    argVariationContourL (fun s ↦ (↑π : ℂ) ^ (-s / 2)) T = -(T / 2) * Real.log π := by
  simp only [argVariationContourL]
  rw [argVariation_cpow_pi_seg 2 (2 + I * ↑T),
    argVariation_cpow_pi_seg (2 + I * ↑T) (1 / 2 + I * ↑T)]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.im_ofNat, Complex.one_im, Complex.div_ofNat_im]
  ring

/-! ### The `Γ`-factor -/

/-- `Γ ∘ φ` is continuous on `[0, 1]` for any continuous path `φ` staying in the right
half-plane. -/
private theorem continuousOn_Gamma_comp {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (φ u).re) :
    ContinuousOn (fun u ↦ Complex.Gamma (φ u)) (Set.Icc 0 1) := fun u hu ↦
  (Complex.analyticOnNhd_Gamma_re_pos _ (hre u hu)).continuousAt.comp_continuousWithinAt
    hφ.continuousWithinAt

/-- The closed rectangle with corners `¼` and `1 + iT/2` lies in the right half-plane. -/
private theorem rectangle_subset_re_pos {T : ℝ} :
    Rectangle (1 / 4 : ℂ) (1 + I * ↑(T / 2)) ⊆ {z : ℂ | 0 < z.re} := fun p hp ↦ by
  rw [Rectangle, Complex.mem_reProdIm] at hp
  rw [show ((1 : ℂ) / 4).re = 1 / 4 by simp, show ((1 : ℂ) + I * ↑(T / 2)).re = 1 by simp,
    Set.uIcc_of_le (by norm_num)] at hp
  exact lt_of_lt_of_le (by norm_num) hp.1.1

/-- The boundary argument variation of `Γ` around the rectangle `[¼, 1] × [0, T/2]`, expanded
over its four oriented edges (bottom, right, top, left). -/
private theorem rectangleArgVariation_Gamma {T : ℝ} :
    rectangleArgVariation Complex.Gamma (1 / 4 : ℂ) (1 + I * ↑(T / 2))
    = argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4) 1 u))
    + argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg 1 (1 + I * ↑(T / 2)) u))
    + argVariation 0 1
        (fun u ↦ Complex.Gamma (lineSeg (1 + I * ↑(T / 2)) (1 / 4 + I * ↑(T / 2)) u))
    + argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 + I * ↑(T / 2)) (1 / 4) u)) := by
  have hbr : (↑((1 + I * ↑(T / 2) : ℂ)).re + ↑(1 / 4 : ℂ).im * I : ℂ) = 1 := by
    apply Complex.ext <;> simp
  have htl : (↑(1 / 4 : ℂ).re + ↑((1 + I * ↑(T / 2) : ℂ)).im * I : ℂ)
      = 1 / 4 + I * ↑(T / 2) := by
    apply Complex.ext <;> simp
  rw [rectangleArgVariation, Complex.re_add_im, Complex.re_add_im, hbr, htl]

/-- The argument variation of `Γ` over the bottom edge `¼ → 1` vanishes (`Γ > 0` there). -/
private theorem argVariation_Gamma_bottom :
    argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) 1 u)) = 0 := by
  have key : ∀ u : ℝ, Complex.Gamma (lineSeg (1 / 4 : ℂ) 1 u)
      = ↑(Real.Gamma (1 / 4 + u * (3 / 4))) := fun u ↦ by
    rw [show lineSeg (1 / 4 : ℂ) 1 u = ↑((1 / 4 + u * (3 / 4) : ℝ)) by
      simp only [lineSeg]; push_cast; ring, Complex.Gamma_ofReal]
  have hpos : ∀ u ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < 1 / 4 + u * (3 / 4) := fun u hu ↦ by
    nlinarith [hu.1]
  rw [argVariation_eq_arg_sub_arg zero_le_one
      (continuousOn_Gamma_comp (continuous_lineSeg _ _) fun u hu ↦ by
        rw [lineSeg_re, Complex.one_re, Complex.div_ofNat_re, Complex.one_re]
        nlinarith [hu.1])
      (fun u hu ↦ by
        rw [key u, Complex.mem_slitPlane_iff]
        exact Or.inl (by simpa using Real.Gamma_pos_of_pos (hpos u hu))),
    key, key, Complex.arg_ofReal_of_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le,
    Complex.arg_ofReal_of_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le]
  ring

/-- The vertical segment `Q : ¼ → ¼ + iT/2` has constant abscissa `¼`. -/
private theorem lineSeg_vseg_re {T : ℝ} (u : ℝ) :
    (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u).re = 1 / 4 := by
  rw [lineSeg_re]; simp

/-- `Γ` is continuous along the vertical segment `Q : ¼ → ¼ + iT/2` (abscissa `¼ > 0`). -/
private theorem continuousOn_Gamma_vseg {T : ℝ} :
    ContinuousOn (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u))
      (Set.Icc 0 1) :=
  continuousOn_Gamma_comp (continuous_lineSeg _ _) fun u _ ↦ by
    rw [lineSeg_vseg_re]; norm_num

/-- `Γ` is non-vanishing along the vertical segment `Q : ¼ → ¼ + iT/2` (abscissa `¼ > 0`). -/
private theorem Gamma_vseg_ne_zero {T : ℝ} :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u) ≠ 0 :=
  fun u _ ↦ Gamma_ne_zero_of_re_pos (by rw [lineSeg_vseg_re]; norm_num)

/-- The argument variation of `Γ` over the left edge `¼ + iT/2 → ¼` is the negative of the one
over the segment `Q : ¼ → ¼ + iT/2` defining `θ`. -/
private theorem argVariation_Gamma_left {T : ℝ} :
    argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 + I * ↑(T / 2)) (1 / 4 : ℂ) u))
      = -argVariation 0 1
          (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u)) := by
  rw [← argVariation_reverse zero_le_one continuousOn_Gamma_vseg Gamma_vseg_ne_zero]
  refine congrArg _ (funext fun u ↦ ?_)
  rw [show (0 : ℝ) + 1 - u = 1 - u by ring, lineSeg_one_sub]

/-- Reparametrising `Q : ¼ → ¼ + iT/2` from `[0, 1]` to `[0, T]` recovers the defining segment
of `θ`: `Δ_Q arg Γ = argVariation 0 T (u ↦ Γ(¼ + iu/2))`. -/
private theorem argVariation_Gamma_vseg_reparam {T : ℝ} (hT : 0 < T) :
    argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u))
      = argVariation 0 T (fun u ↦ Complex.Gamma (1 / 4 + I * (↑u / 2))) := by
  have hTc : (↑T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [← argVariation_comp zero_le_one hT.le ((continuous_id.div_const T).continuousOn)
    (fun v hv ↦ ⟨div_nonneg hv.1 hT.le, (div_le_one hT).mpr hv.2⟩) (by simp)
    (by simp [hT.ne']) continuousOn_Gamma_vseg Gamma_vseg_ne_zero]
  refine congrArg _ (funext fun v ↦ congrArg Complex.Gamma ?_)
  simp only [lineSeg, id_eq]
  push_cast
  field_simp
  ring

/-- **The `Γ`-factor.** Along `L_T : 2 → 2 + iT → ½ + iT`,
`Δ_{L_T} arg(Γ(s/2)) = argVariation 0 T (u ↦ Γ(¼ + iu/2))`, the defining segment of `θ`. -/
private theorem argVariationContourL_Gamma_half {T : ℝ} (hT : 0 < T) :
    argVariationContourL (fun s ↦ Complex.Gamma (s / 2)) T
      = argVariation 0 T (fun u ↦ Complex.Gamma (1 / 4 + I * (↑u / 2))) := by
  -- The rectangle boundary variation vanishes (Cauchy's theorem on `[¼,1] × [0,T/2]`).
  have hrect : rectangleArgVariation Complex.Gamma (1 / 4 : ℂ) (1 + I * ↑(T / 2)) = 0 :=
    rectangleArgVariation_eq_zero_of_analyticOnNhd Complex.analyticOnNhd_Gamma_re_pos
      (fun _ hx ↦ Gamma_ne_zero_of_re_pos hx) rectangle_subset_re_pos
  rw [rectangleArgVariation_Gamma, argVariation_Gamma_bottom, argVariation_Gamma_left,
    argVariation_Gamma_vseg_reparam hT] at hrect
  -- The two contour segments are the `s ↦ s/2` images of the right and top edges.
  have hseg1 : (fun u ↦ Complex.Gamma (lineSeg 2 (2 + I * ↑T) u / 2))
      = (fun u ↦ Complex.Gamma (lineSeg 1 (1 + I * ↑(T / 2)) u)) := by
    funext u; rw [lineSeg_div]; congr 2 <;> push_cast <;> ring
  have hseg2 : (fun u ↦ Complex.Gamma (lineSeg (2 + I * ↑T) (1 / 2 + I * ↑T) u / 2))
      = (fun u ↦ Complex.Gamma (lineSeg (1 + I * ↑(T / 2)) (1 / 4 + I * ↑(T / 2)) u)) := by
    funext u; rw [lineSeg_div]; congr 2 <;> push_cast <;> ring
  simp only [argVariationContourL]
  rw [hseg1, hseg2]
  linarith [hrect]

/-! ### The full archimedean factor -/

/-- The argument variation of `Γ_ℝ` along a single affine segment whose endpoints lie in the
right half-plane splits into the `π`-factor and the `Γ`-factor. -/
private theorem argVariation_Gammaℝ_seg (z₀ z₁ : ℂ) (h0 : 0 < z₀.re) (h1 : 0 < z₁.re) :
    argVariation 0 1 (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
        + argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg z₀ z₁ u / 2)) := by
  have hπ : (↑π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (lineSeg z₀ z₁ u / 2).re := fun u hu ↦ by
    rw [Complex.div_ofNat_re, lineSeg_re]
    rcases le_total z₀.re z₁.re with h | h
    · nlinarith [hu.1]
    · nlinarith [hu.2]
  have hfeq : (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u))
      = (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
        * (fun u ↦ Complex.Gamma (lineSeg z₀ z₁ u / 2)) :=
    funext fun u ↦ Complex.Gammaℝ_def _
  conv_lhs => rw [hfeq]
  exact argVariation_mul zero_le_one
    (((continuous_lineSeg z₀ z₁).neg.div_const 2).const_cpow (Or.inl hπ)).continuousOn
    (fun u _ ↦ by rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _)
    (continuousOn_Gamma_comp ((continuous_lineSeg z₀ z₁).div_const 2) hre)
    (fun u hu ↦ Gamma_ne_zero_of_re_pos (hre u hu))

/-- **The argument of the `Γ` and `π` factors is `θ`.** For `T > 0`,
`Δ_{L_T} arg Γ_ℝ = θ(T)` along `L_T : 2 → 2 + iT → ½ + iT`. -/
theorem argVariation_GammaPi_L {T : ℝ} (hT : 0 < T) :
    argVariationContourL Complex.Gammaℝ T = riemannSiegelTheta T := by
  -- Split `Γ_ℝ = π^{-s/2}·Γ(s/2)` on each of the two segments of `L_T`, then add up the
  -- `π`-factor and `Γ`-factor contour variations.
  have hpi := argVariationContourL_cpow_pi (T := T)
  have hga := argVariationContourL_Gamma_half hT
  simp only [argVariationContourL] at hpi hga ⊢
  rw [argVariation_Gammaℝ_seg 2 (2 + I * ↑T) (by norm_num) (by simp),
    argVariation_Gammaℝ_seg (2 + I * ↑T) (1 / 2 + I * ↑T) (by simp) (by norm_num),
    riemannSiegelTheta]
  linarith [hpi, hga]

