/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Planar Newtonian-kernel integrability

The planar Newtonian kernel `s ↦ ‖s - ρ‖⁻¹` on a closed disk in `ℂ`, with respect to
two-dimensional Lebesgue measure.

## Main results

- `integrableOn_inv_norm_sub_closedBall` (`lem:lb_newton_kernel`): integrability on a closed disk.
- `integral_inv_norm_sub_closedBall`: the value of the integral is `2 π r`.
-/
@[expose] public section


open MeasureTheory Metric Real
open scoped ENNReal

/-- The lower Lebesgue integral of the Newtonian kernel `‖s‖⁻¹` over a disk of radius `r`
centred at the origin. -/
private theorem lintegral_ofReal_inv_norm_closedBall {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in closedBall (0 : ℂ) r, ENNReal.ofReal ‖s‖⁻¹ = ENNReal.ofReal (2 * π * r) := by
  rw [← lintegral_indicator measurableSet_closedBall,
    ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have heqon : Set.EqOn
      (fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 •
        (closedBall (0 : ℂ) r).indicator (fun w ↦ ENNReal.ofReal ‖w‖⁻¹)
          (Complex.polarCoord.symm p))
      ((Set.Ioc 0 r ×ˢ Set.Ioo (-π) π).indicator (fun _ ↦ 1))
      (Set.Ioi 0 ×ˢ Set.Ioo (-π) π) := by
    rintro ⟨x, y⟩ ⟨hx : (0 : ℝ) < x, hy₁, hy₂⟩
    have hnorm : ‖(Complex.polarCoord.symm (x, y) : ℂ)‖ = x := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hx]
    by_cases h : x ≤ r <;>
      simp [-Complex.polarCoord_symm_apply, mem_closedBall, dist_zero_right, hnorm, hx, hy₁, hy₂,
        h, ENNReal.mul_inv_cancel (by simp [hx] : ENNReal.ofReal x ≠ 0) ENNReal.ofReal_ne_top]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) heqon,
    setLIntegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo),
    Set.prod_inter_prod, Set.inter_eq_left.mpr Set.Ioc_subset_Ioi_self, Set.inter_self,
    setLIntegral_const, one_mul, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Ioc, Real.volume_Ioo, ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ r - 0)]
  congr 1
  ring

/-- The lower Lebesgue integral of `‖s - ρ‖⁻¹` over `closedBall ρ r`. -/
private theorem lintegral_ofReal_inv_norm_sub_closedBall (ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ s in closedBall ρ r, ENNReal.ofReal ‖s - ρ‖⁻¹ = ENNReal.ofReal (2 * π * r) := by
  rw [← lintegral_indicator measurableSet_closedBall, ← lintegral_add_right_eq_self _ ρ,
    ← lintegral_ofReal_inv_norm_closedBall hr, ← lintegral_indicator measurableSet_closedBall]
  refine lintegral_congr fun s ↦ ?_
  simp [Set.indicator, mem_closedBall, dist_eq_norm]

private theorem measurable_inv_norm_sub (ρ : ℂ) : Measurable (fun s : ℂ ↦ ‖s - ρ‖⁻¹) :=
  (continuous_norm.comp (continuous_id.sub continuous_const)).measurable.inv

/-- **Planar Newtonian-kernel integrability** (`lem:lb_newton_kernel`). The kernel
`s ↦ ‖s - ρ‖⁻¹` is integrable on a closed disk for two-dimensional Lebesgue measure. -/
theorem integrableOn_inv_norm_sub_closedBall (ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℂ ↦ ‖s - ρ‖⁻¹) (closedBall ρ r) := by
  refine ⟨(measurable_inv_norm_sub ρ).aestronglyMeasurable, ?_⟩
  simp_rw [hasFiniteIntegral_iff_norm, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    lintegral_ofReal_inv_norm_sub_closedBall ρ hr]
  exact ENNReal.ofReal_lt_top

/-- The integral of the planar Newtonian kernel `s ↦ ‖s - ρ‖⁻¹` over the closed disk
`closedBall ρ r` is `2 π r` (`lem:lb_newton_kernel`). -/
theorem integral_inv_norm_sub_closedBall (ρ : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∫ s in closedBall ρ r, ‖s - ρ‖⁻¹ = 2 * π * r := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun s ↦ inv_nonneg.mpr (norm_nonneg _))
    (measurable_inv_norm_sub ρ).aestronglyMeasurable,
    lintegral_ofReal_inv_norm_sub_closedBall ρ hr,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * π * r)]

