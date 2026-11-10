/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Zeta.Analysis.Complex.ArgVariation

/-!
# The Riemann–Siegel theta function, `S(T)`, and the polynomial argument

The analytic ingredients of the exact Riemann–von Mangoldt formula `N(T) = θ(T)/π + 1 + S(T)`,
built from the continuous argument variation `argVariation` of
`Zeta/Analysis/Complex/ArgVariation.lean` along the contour `L_T : 2 → 2 + iT → ½ + iT`.

## Main definitions

- `argVariationContourL`: the argument variation `Δ_{L_T} arg f` along `L_T`.
- `riemannSiegelTheta`: the Riemann–Siegel theta function `θ(T)`.
- `argZeta`: the function `S(T) = (1/π) Δ_{L_T} arg ζ`.

## Main results

- `argVariation_const`: the argument variation of a nonzero constant is `0`.
- `argVariation_poly_L`: along `L_T` the polynomial factor `½ s (s - 1)` has argument
  variation `π`.
-/
@[expose] public section


open Complex

namespace Complex

/-- For `z` in the upper half plane, `arg z + arg (-conj z) = π`. -/
theorem arg_add_arg_neg_conj {z : ℂ} (hz : 0 < z.im) :
    z.arg + (-(starRingEnd ℂ z)).arg = Real.pi := by
  have hpi : z.arg ≠ Real.pi := fun h ↦ hz.ne' (Complex.arg_eq_pi_iff.mp h).2
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hz), Complex.arg_conj,
    ite_eq_right hpi]
  ring

end Complex

variable {a b : ℝ}

/-- The argument variation of a nonzero constant is `0`. -/
theorem argVariation_const (hab : a ≤ b) {c : ℂ} (hc : c ≠ 0) :
    argVariation a b (fun _ ↦ c) = 0 := by
  rw [argVariation_eq_of_isContLog hab
    (g := fun _ ↦ Complex.log c) ⟨continuousOn_const, fun _ _ ↦ Complex.exp_log hc⟩]
  ring

/-- Argument variation along an affine segment that stays in the slit plane is the
difference of the principal arguments of the endpoints. -/
theorem argVariation_lineSeg {z₀ z₁ : ℂ}
    (h : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane) :
    argVariation 0 1 (lineSeg z₀ z₁) = z₁.arg - z₀.arg := by
  simpa using
    argVariation_eq_arg_sub_arg zero_le_one (continuous_lineSeg z₀ z₁).continuousOn h

/-- The argument variation `Δ_{L_T} arg f` of `f` along the contour `L_T : 2 → 2 + iT → ½ + iT`,
the sum of the variations over its two affine segments. -/
noncomputable def argVariationContourL (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  argVariation 0 1 (fun u ↦ f (lineSeg 2 (2 + Complex.I * T) u)) +
    argVariation 0 1 (fun u ↦ f (lineSeg (2 + Complex.I * T) (1 / 2 + Complex.I * T) u))

/-- The **Riemann–Siegel theta function**
`θ(T) = Δ_{γ_Γ} arg Γ − (T/2) log π`, where `γ_Γ(u) = ¼ + iu/2` is the vertical segment
from `¼` to `¼ + iT/2`, on which `Γ ≠ 0`. -/
noncomputable def riemannSiegelTheta (T : ℝ) : ℝ :=
  argVariation 0 T (fun u ↦ Complex.Gamma (1 / 4 + Complex.I * (u / 2))) -
    (T / 2) * Real.log Real.pi

/-- The function **`S(T) = (1/π) Δ_{L_T} arg ζ`**, the continuous variation of `arg ζ`
along `L_T : 2 → 2 + iT → ½ + iT`. -/
noncomputable def argZeta (T : ℝ) : ℝ := (1 / Real.pi) * argVariationContourL riemannZeta T

/-- The argument variation of the polynomial factor `½ s (s - 1)` over a single affine
segment that, together with its translate by `1`, stays in the slit plane. -/
theorem argVariation_poly_seg {z₀ z₁ : ℂ}
    (hs : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane)
    (hs1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg (z₀ - 1) (z₁ - 1) u ∈ Complex.slitPlane) :
    argVariation 0 1 (fun u ↦ (1 / 2) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
      = (z₁.arg - z₀.arg) + ((z₁ - 1).arg - (z₀ - 1).arg) := by
  have hc2 : (1 / 2 : ℂ) ≠ 0 := one_div_ne_zero two_ne_zero
  have hsub : (fun u ↦ lineSeg z₀ z₁ u - 1) = lineSeg (z₀ - 1) (z₁ - 1) :=
    lineSeg_sub_const z₀ z₁ 1
  have hcont : ContinuousOn (lineSeg z₀ z₁) (Set.Icc (0 : ℝ) 1) :=
    (continuous_lineSeg z₀ z₁).continuousOn
  have hcont1 : ContinuousOn (fun u ↦ lineSeg z₀ z₁ u - 1) (Set.Icc (0 : ℝ) 1) :=
    ((continuous_lineSeg z₀ z₁).sub continuous_const).continuousOn
  have h0 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 0 :=
    fun u hu ↦ Complex.slitPlane_ne_zero (hs u hu)
  have h1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u - 1 ≠ 0 := fun u hu ↦ by
    rw [congrFun hsub u]; exact Complex.slitPlane_ne_zero (hs1 u hu)
  change argVariation 0 1
    ((fun _ ↦ (1 / 2 : ℂ)) * (lineSeg z₀ z₁ * fun u ↦ lineSeg z₀ z₁ u - 1)) = _
  rw [argVariation_mul zero_le_one continuousOn_const (fun _ _ ↦ hc2) (hcont.mul hcont1)
        (fun u hu ↦ mul_ne_zero (h0 u hu) (h1 u hu)),
    argVariation_const zero_le_one hc2, zero_add,
    argVariation_mul zero_le_one hcont h0 hcont1 h1,
    argVariation_lineSeg hs, hsub, argVariation_lineSeg hs1]

/-- Argument of the polynomial factor: for `T > 0`, `Δ_{L_T} arg (½ s (s - 1)) = π`. -/
theorem argVariation_poly_L {T : ℝ} (hT : 0 < T) :
    argVariationContourL (fun s ↦ (1 / 2) * (s * (s - 1))) T = Real.pi := by
  -- slit-plane membership via a constant real part `> 0` …
  have memRe : ∀ {z₀ z₁ : ℂ} {r : ℝ}, 0 < r → z₀.re = r → z₁.re = r →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane :=
    fun hr h0 h1 u _ ↦ Complex.mem_slitPlane_iff.2 <| .inl <| by
      rw [lineSeg_re, h0, h1]; simpa using hr
  -- … or via a constant nonzero imaginary part
  have memIm : ∀ {z₀ z₁ : ℂ} {y : ℝ}, y ≠ 0 → z₀.im = y → z₁.im = y →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane :=
    fun hy h0 h1 u _ ↦ Complex.mem_slitPlane_iff.2 <| .inr <| by
      rw [lineSeg_im, h0, h1]; simpa using hy
  simp only [argVariationContourL]
  rw [argVariation_poly_seg (memRe (r := 2) two_pos (by norm_num) (by simp))
        (memRe (r := 1) one_pos (by norm_num) (by norm_num)),
      argVariation_poly_seg (memIm (y := T) hT.ne' (by simp) (by simp))
        (memIm (y := T) hT.ne' (by simp) (by simp))]
  -- evaluate the boundary arguments and telescope
  have hzsub : (1 / 2 + Complex.I * (T : ℂ)) - 1 =
      -(starRingEnd ℂ (1 / 2 + Complex.I * (T : ℂ))) := by
    norm_num [Complex.ext_iff]
  have hz_im : (0 : ℝ) < (1 / 2 + Complex.I * (T : ℂ)).im := by simpa using hT
  rw [hzsub, Complex.ofNat_arg, show (2 : ℂ) - 1 = 1 by norm_num, Complex.arg_one]
  linarith [arg_add_arg_neg_conj hz_im]

