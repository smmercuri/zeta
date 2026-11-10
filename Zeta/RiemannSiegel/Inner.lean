/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Zeta.Analysis.SpecialFunctions.Gaussian
public import Zeta.RiemannSiegel.Saddle

/-!
# The inner saddle-point estimate

The error committed by replacing the Riemann–Siegel integrand by its Gaussian model at the saddle is
`Zeta.RiemannSiegel.contourIntegral_sub_mul_modelIntegral`: the model integrand integrated against
`e^Δ - 1`, with `Δ` the saddle discrepancy `Zeta.RiemannSiegel.saddleDiscrepancy`. That integral is
estimated by splitting the contour at `|w| = W`, `W = T^{1/12}` the **splitting radius**
`Zeta.RiemannSiegel.splitRadius`; this file treats the inner region `|w| ≤ W`
(`riemann_siegel_first.tex`, `lem:rsf_inner`).

The exponent `1/12` enters only through `splitRadius_pow_six`, `√T = W^6`, in the parametrisation of
which every estimate on the inner region becomes a polynomial inequality in `W` alone.

## Main results

* `Zeta.RiemannSiegel.splitRadius`: the splitting radius `W = T^{1/12}`;
* `Zeta.RiemannSiegel.norm_integral_inner_le` (`riemann_siegel_first.tex`, `lem:rsf_inner`): the
  inner integral is at most `21 T^{-1/2}`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- The **splitting radius** `W = T^{1/12}`, `T = t/2π` (`riemann_siegel_first.tex`,
`sec:rsf_saddle`). -/
noncomputable def splitRadius (t : ℝ) : ℝ := (t / (2 * π)) ^ ((12 : ℝ)⁻¹)

theorem splitRadius_pos {t : ℝ} (ht : 0 < t) : 0 < splitRadius t :=
  Real.rpow_pos_of_pos (by positivity) _

theorem splitRadius_pow_twelve {t : ℝ} (ht : 0 < t) : splitRadius t ^ 12 = t / (2 * π) := by
  have hT : (0 : ℝ) < t / (2 * π) := by positivity
  rw [splitRadius, ← Real.rpow_natCast _ 12, ← Real.rpow_mul hT.le]
  norm_num

theorem splitRadius_pow_six {t : ℝ} (ht : 0 < t) :
    splitRadius t ^ 6 = Real.sqrt (t / (2 * π)) := by
  rw [← splitRadius_pow_twelve ht, show splitRadius t ^ 12 = (splitRadius t ^ 6) ^ 2 by ring,
    Real.sqrt_sq (pow_nonneg (splitRadius_pos ht).le 6)]

theorem le_splitRadius {t c : ℝ} (hc : 0 < c) (ht : c ^ 12 ≤ t / (2 * π)) :
    c ≤ splitRadius t := by
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp
    (lt_of_lt_of_le (by positivity) ht)
  refine le_of_pow_le_pow_left₀ (n := 12) (by norm_num) (splitRadius_pos ht0).le ?_
  rwa [splitRadius_pow_twelve ht0]

/-- Powers of `W` below the sixth, against the sixth. -/
private theorem mul_pow_le_pow_six {W : ℝ} (hW0 : 0 < W) (hW : (3.16 : ℝ) ≤ W) {j k : ℕ}
    (hjk : j + k = 6) : (3.16 : ℝ) ^ j * W ^ k ≤ W ^ 6 := by
  rw [show W ^ 6 = W ^ j * W ^ k by rw [← pow_add, hjk]]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hW j) (pow_nonneg hW0.le k)

/-- **The two pointwise hypotheses of the inner region**, in the parametrisation `√T = W^6` that
turns both into polynomial inequalities in `W` alone. -/
private theorem inner_pointwise_bounds {W : ℝ} (hW0 : 0 < W) (hW : (3.16 : ℝ) ≤ W) :
    1 / 2 + 1.415 * W ≤ W ^ 6 / 2
      ∧ 1 / 2 + 1.415 * W + 4 * π / 3 * (1 / 2 + 1.415 * W) ^ 3 ≤ W ^ 6 := by
  have h1 : (3.16 : ℝ) ^ 5 * W ^ 1 ≤ W ^ 6 := mul_pow_le_pow_six hW0 hW rfl
  have h2 : (3.16 : ℝ) ^ 4 * W ^ 2 ≤ W ^ 6 := mul_pow_le_pow_six hW0 hW rfl
  have h3 : (3.16 : ℝ) ^ 3 * W ^ 3 ≤ W ^ 6 := mul_pow_le_pow_six hW0 hW rfl
  have h4 : (3.16 : ℝ) ^ 6 * W ^ 0 ≤ W ^ 6 := mul_pow_le_pow_six hW0 hW rfl
  -- clearing `π` from the cubic term, so that both halves are rational in `W`
  have hc : 4 * π / 3 ≤ 4.1888 := by linarith [Real.pi_lt_d4]
  have hcube := mul_le_mul_of_nonneg_right hc (show (0 : ℝ) ≤ (1 / 2 + 1.415 * W) ^ 3 by positivity)
  norm_num at h1 h4
  exact ⟨by nlinarith, by nlinarith⟩

/-- **The numerical constant of the inner estimate.** -/
private theorem two_mul_exp_mul_moment_sum_le :
    2 * Real.exp (π / 4) * ((0.854 + 4 * π / 3 * 0.854 ^ 3) * Real.sqrt (π / (4 * π))
        + (1.415 + 3 * (4 * π / 3) * 0.854 ^ 2 * 1.415) / (4 * π)
        + 3 * (4 * π / 3) * 0.854 * 1.415 ^ 2 * (Real.sqrt (π / (4 * π)) / (2 * (4 * π)))
        + 4 * π / 3 * 1.415 ^ 3 / (4 * π) ^ 2) ≤ 21 := by
  have hπ1 : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hπ2 : π < 3.1416 := Real.pi_lt_d4
  have hsq : Real.sqrt (π / (4 * π)) = 1 / 2 := by
    rw [show π / (4 * π) = (1 / 2 : ℝ) ^ 2 by field_simp; ring]
    exact Real.sqrt_sq (by norm_num)
  have hform : (0.854 + 4 * π / 3 * 0.854 ^ 3) * Real.sqrt (π / (4 * π))
      + (1.415 + 3 * (4 * π / 3) * 0.854 ^ 2 * 1.415) / (4 * π)
      + 3 * (4 * π / 3) * 0.854 * 1.415 ^ 2 * (Real.sqrt (π / (4 * π)) / (2 * (4 * π)))
      + 4 * π / 3 * 1.415 ^ 3 / (4 * π) ^ 2
      = 0.854 / 2 + 2 * π / 3 * 0.854 ^ 3 + 1.415 / (4 * π) + 0.854 ^ 2 * 1.415
        + 0.854 * 1.415 ^ 2 / 4 + 1.415 ^ 3 / (12 * π) := by
    rw [hsq]
    field_simp
    ring
  rw [hform]
  have hbr0 : (0 : ℝ) ≤ 0.854 / 2 + 2 * π / 3 * 0.854 ^ 3 + 1.415 / (4 * π) + 0.854 ^ 2 * 1.415
      + 0.854 * 1.415 ^ 2 / 4 + 1.415 ^ 3 / (12 * π) := by positivity
  have hbr : 0.854 / 2 + 2 * π / 3 * 0.854 ^ 3 + 1.415 / (4 * π) + 0.854 ^ 2 * 1.415
      + 0.854 * 1.415 ^ 2 / 4 + 1.415 ^ 3 / (12 * π) ≤ 3.4 := by
    have h1 : (1.415 : ℝ) / (4 * π) ≤ 1.415 / (4 * 3.1415) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have h2 : (1.415 : ℝ) ^ 3 / (12 * π) ≤ 1.415 ^ 3 / (12 * 3.1415) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    nlinarith
  have hE : Real.exp (π / 4) ≤ 2.72 :=
    (Real.exp_le_exp.2 (by linarith : π / 4 ≤ 1)).trans (by linarith [Real.exp_one_lt_d9])
  have h := mul_le_mul hE hbr hbr0 (by norm_num : (0 : ℝ) ≤ 2.72)
  linarith

/-- The cube of a linear function of `|u|`, collected into a cubic in `|u|` of the shape that
`integral_exp_neg_mul_sq_mul_poly` integrates. -/
private theorem add_mul_abs_add_cube_eq (c A B u : ℝ) :
    A + B * |u| + c * (A + B * |u|) ^ 3
      = A + c * A ^ 3 + (B + 3 * c * A ^ 2 * B) * |u| + 3 * c * A * B ^ 2 * u ^ 2
        + c * B ^ 3 * |u| ^ 3 := by
  rw [← sq_abs u]
  ring

/-- **The pointwise estimate on the inner region**: the perturbed model integrand is a Gaussian
times the size of the saddle discrepancy. -/
private theorem norm_modelIntegrand_mul_exp_sub_one_le {t : ℝ} (ht : 0 < t) {ν : ℕ} {p S w : ℝ}
    (hS : S = Real.sqrt (t / (2 * π))) (hp : p = S - ν) (hκ : |1 / 2 - p| ≤ 1 / 2)
    (hu : ‖line (1 / 2) w - (p : ℂ)‖ ≤ S / 2)
    (hΔ : ‖line (1 / 2) w - (p : ℂ)‖ + 4 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 3 ≤ S) :
    ‖modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖
      ≤ 2 * Real.exp (π / 4) / (Real.sqrt 2 * S) *
        (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
          (‖line (1 / 2) w - (p : ℂ)‖
            + 4 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 3)) := by
  have hs2' : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
  have hS0 : 0 < S := by rw [hS]; exact Real.sqrt_pos.2 (by positivity)
  have hS0' : S ≠ 0 := hS0.ne'
  -- the contour of the model integral is the contour of `I(s, a)` translated by `ν`
  have hxy := line_sub_ofReal_sub hp w
  have hx : ‖line ((ν : ℝ) + 1 / 2) w - ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)‖
      ≤ Real.sqrt (t / (2 * π)) / 2 := by
    rw [← hS, hxy]
    exact hu
  have hd1 := norm_saddleDiscrepancy_le ht hx
  rw [← hS, hxy] at hd1
  -- abbreviations for the distance to the saddle and for the discrepancy itself
  set Y : ℝ := ‖line (1 / 2) w - (p : ℂ)‖ with hYdef
  set D : ℂ := saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w) with hDdef
  -- the discrepancy is at most one, so `e^Δ - 1` costs a factor two
  have hΔ1 : ‖D‖ ≤ 1 := hd1.trans ((div_le_one hS0).2 hΔ)
  have h7 : ‖exp D - 1‖ ≤ 2 * ((Y + 4 * π / 3 * Y ^ 3) / S) :=
    (Complex.norm_exp_sub_one_le hΔ1).trans (by linarith)
  -- the model integrand is dominated by its Gaussian numerator, of peak `e^{π/4}`
  have h8 := norm_modelIntegrand_le_exp_neg_mul_sq hκ w
  calc ‖modelIntegrand (p : ℂ) (1 / 2) w * (exp D - 1)‖
      = ‖modelIntegrand (p : ℂ) (1 / 2) w‖ * ‖exp D - 1‖ := norm_mul _ _
    _ ≤ Real.exp (π / 4) * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) / Real.sqrt 2
          * (2 * ((Y + 4 * π / 3 * Y ^ 3) / S)) :=
        mul_le_mul h8 h7 (norm_nonneg _) (by positivity)
    _ = 2 * Real.exp (π / 4) / (Real.sqrt 2 * S) *
          (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) * (Y + 4 * π / 3 * Y ^ 3)) := by
        field_simp

/-- **The inner saddle-point estimate** (`riemann_siegel_first.tex`, `lem:rsf_inner`): over the
region `|w| ≤ W = T^{1/12}` about the saddle, where the saddle discrepancy satisfies `|Δ| ≤ 1`, the
perturbation `e^Δ - 1` of the model integrand contributes at most `21 T^{-1/2}`. -/
theorem norm_integral_inner_le {t : ℝ} (ht : 10 ^ 6 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖(1 + I) * ∫ w in Set.Icc (-splitRadius t) (splitRadius t),
        modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖
      ≤ 21 / Real.sqrt (t / (2 * π)) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2' : Real.sqrt 2 ≠ 0 := hs2.ne'
  have hsqrt2 : Real.sqrt 2 ≤ 1.415 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  -- abbreviations for the splitting radius, the saddle `√T` and the fractional part `p`;
  -- their values are cleared, since every use goes through the equations below
  set W : ℝ := splitRadius t with hWdef
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set p : ℝ := S - (ν : ℝ) with hpdef
  clear_value p S W
  have hS0 : 0 < S := by rw [hSdef]; exact Real.sqrt_pos.2 hT0
  have hS0' : S ≠ 0 := hS0.ne'
  have hW0 : 0 < W := by rw [hWdef]; exact splitRadius_pos ht0
  have hW6 : W ^ 6 = S := by rw [hWdef, hSdef]; exact splitRadius_pow_six ht0
  have hW316 : (3.16 : ℝ) ≤ W := by
    rw [hWdef]
    exact le_splitRadius (by norm_num) (le_trans (by norm_num) ht)
  have hκ : |1 / 2 - p| ≤ 1 / 2 := by
    rw [abs_le, hpdef]
    constructor <;> linarith
  -- the two pointwise hypotheses of the inner region, as inequalities in `W`
  obtain ⟨hMS, hMΔ⟩ := inner_pointwise_bounds hW0 hW316
  rw [hW6] at hMS hMΔ
  have hy : ∀ w ∈ Set.Icc (-W) W, ‖line (1 / 2) w - (p : ℂ)‖ ≤ 1 / 2 + 1.415 * W := fun w hw ↦
    (norm_line_sub_ofReal_le (1 / 2) w p).trans (by
      nlinarith [abs_le.2 ⟨hw.1, hw.2⟩, hκ, abs_nonneg w,
        mul_le_mul_of_nonneg_right hsqrt2 (abs_nonneg w)])
  have hQ : ∀ w : ℝ, ‖line (1 / 2) w - (p : ℂ)‖ ≤ 0.854 + 1.415 * |w + (1 / 2 - p) / 2| :=
    fun w ↦ (norm_line_sub_ofReal_le' (1 / 2) w p).trans (by
      nlinarith [mul_le_mul_of_nonneg_right hsqrt2 (abs_nonneg (w + (1 / 2 - p) / 2)),
        mul_le_mul_of_nonneg_left hκ (Real.sqrt_nonneg 2), abs_nonneg (1 / 2 - p)])
  -- the Gaussian majorant: a cubic in `|w + (½ - p)/2|` against a Gaussian centred there
  set c₀ : ℝ := 0.854 + 4 * π / 3 * 0.854 ^ 3 with hc₀
  set c₁ : ℝ := 1.415 + 3 * (4 * π / 3) * 0.854 ^ 2 * 1.415 with hc₁
  set c₂ : ℝ := 3 * (4 * π / 3) * 0.854 * 1.415 ^ 2 with hc₂
  set c₃ : ℝ := 4 * π / 3 * 1.415 ^ 3 with hc₃
  set maj : ℝ → ℝ := fun w ↦ 2 * Real.exp (π / 4) / (Real.sqrt 2 * S) *
    (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
      (c₀ + c₁ * |w + (1 / 2 - p) / 2| + c₂ * (w + (1 / 2 - p) / 2) ^ 2
        + c₃ * |w + (1 / 2 - p) / 2| ^ 3)) with hmajdef
  clear_value maj c₃ c₂ c₁ c₀
  have hC0 : (0 : ℝ) ≤ 2 * Real.exp (π / 4) / (Real.sqrt 2 * S) :=
    div_nonneg (by positivity) (mul_nonneg hs2.le hS0.le)
  have hpoly0 : ∀ w : ℝ, (0 : ℝ) ≤ c₀ + c₁ * |w + (1 / 2 - p) / 2|
      + c₂ * (w + (1 / 2 - p) / 2) ^ 2 + c₃ * |w + (1 / 2 - p) / 2| ^ 3 := by
    intro w
    rw [hc₀, hc₁, hc₂, hc₃]
    positivity
  have hmaj0 : ∀ w : ℝ, 0 ≤ maj w := fun w ↦ by
    rw [hmajdef]
    exact mul_nonneg hC0 (mul_nonneg (Real.exp_nonneg _) (hpoly0 w))
  have hmajint : Integrable maj := by
    rw [hmajdef]
    exact ((integrable_exp_neg_mul_sq_mul_poly (b := 4 * π) (by positivity) c₀ c₁ c₂
      c₃).comp_add_right ((1 / 2 - p) / 2)).const_mul _
  -- the value of the majorant integral, by the absolute moments of a Gaussian
  set BR : ℝ := c₀ * Real.sqrt (π / (4 * π)) + c₁ / (4 * π)
    + c₂ * (Real.sqrt (π / (4 * π)) / (2 * (4 * π))) + c₃ / (4 * π) ^ 2 with hBR
  clear_value BR
  have hmajval : ∫ w : ℝ, maj w = 2 * Real.exp (π / 4) / (Real.sqrt 2 * S) * BR := by
    rw [hBR, hmajdef, integral_const_mul]
    congr 1
    rw [show (∫ w : ℝ, Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
          (c₀ + c₁ * |w + (1 / 2 - p) / 2| + c₂ * (w + (1 / 2 - p) / 2) ^ 2
            + c₃ * |w + (1 / 2 - p) / 2| ^ 3))
        = ∫ w : ℝ, (fun u : ℝ ↦ Real.exp (-(4 * π) * u ^ 2) *
          (c₀ + c₁ * |u| + c₂ * u ^ 2 + c₃ * |u| ^ 3)) (w + (1 / 2 - p) / 2) from rfl,
      integral_add_right_eq_self (fun u : ℝ ↦ Real.exp (-(4 * π) * u ^ 2) *
        (c₀ + c₁ * |u| + c₂ * u ^ 2 + c₃ * |u| ^ 3)) ((1 / 2 - p) / 2),
      integral_exp_neg_mul_sq_mul_poly (by positivity)]
  -- the numerical value of the resulting constant, `2e^{π/4} · 3.379 ≤ 21`
  have hnum : 2 * Real.exp (π / 4) * BR ≤ 21 := by
    rw [hBR, hc₀, hc₁, hc₂, hc₃]
    exact two_mul_exp_mul_moment_sum_le
  -- integrability of the perturbed model integrand
  have hFint : Integrable fun w : ℝ ↦ modelIntegrand (p : ℂ) (1 / 2) w
      * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1) := by
    have h1 := integrable_modelIntegrand_mul_exp_saddleDiscrepancy ht0 ν
    rw [← hSdef, ← hpdef] at h1
    have hsub : Integrable fun w : ℝ ↦ modelIntegrand (p : ℂ) (1 / 2) w
        * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))
          - modelIntegrand (p : ℂ) (1 / 2) w :=
      h1.sub (integrable_modelIntegrand (p : ℂ) hhalf)
    exact hsub.congr (.of_forall fun w ↦ by ring)
  -- the pointwise majorant on the inner region
  have key : ∀ w ∈ Set.Icc (-W) W, ‖modelIntegrand (p : ℂ) (1 / 2) w
      * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖ ≤ maj w := by
    intro w hw
    have hu : ‖line (1 / 2) w - (p : ℂ)‖ ≤ S / 2 := (hy w hw).trans hMS
    have hΔ : ‖line (1 / 2) w - (p : ℂ)‖
        + 4 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 3 ≤ S := by
      refine le_trans ?_ hMΔ
      gcongr <;> exact hy w hw
    refine (norm_modelIntegrand_mul_exp_sub_one_le ht0 hSdef hpdef hκ hu hΔ).trans ?_
    rw [hmajdef]
    refine mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)) hC0
    rw [hc₀, hc₁, hc₂, hc₃, ← add_mul_abs_add_cube_eq (4 * π / 3) 0.854 1.415]
    gcongr <;> exact hQ w
  calc ‖(1 + I) * ∫ w in Set.Icc (-W) W, modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖
      ≤ Real.sqrt 2 * ∫ w in Set.Icc (-W) W, ‖modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖ :=
        norm_one_add_I_mul_integral_le _
    _ ≤ Real.sqrt 2 * ∫ w in Set.Icc (-W) W, maj w :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on hFint.norm.integrableOn
          hmajint.integrableOn measurableSet_Icc key) hs2.le
    _ ≤ Real.sqrt 2 * ∫ w : ℝ, maj w :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hmajint (.of_forall hmaj0)) hs2.le
    _ = 2 * Real.exp (π / 4) * BR / S := by
        rw [hmajval]
        field_simp
    _ ≤ 21 / S := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hnum (inv_pos.2 hS0).le

end Zeta.RiemannSiegel
