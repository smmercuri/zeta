/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Zeta.Analysis.SpecialFunctions.Gaussian
public import Zeta.RiemannSiegel.Hankel
public import Zeta.RiemannSiegel.Shift

/-!
# Deforming the Riemann–Siegel contour onto the diagonal

For `Re s < 0` the Riemann–Siegel integrand `x^{-s} G(x)` is absolutely integrable along the
contour `L(0)` through the origin even though the kernel `G` has a simple pole there, because the
power `x^{-s}` vanishes to order `-Re s > 0`. This file identifies the resulting integral `I(s, 0)`
with `I(s, ½)`, which combined with `Zeta/RiemannSiegel/Hankel.lean` is the Hankel-ray
representation of `I(s, ½)` (`riemann_siegel_zero.tex`, `lem:rsz_hankel`).

The deformation is carried out in two steps, and needs no indented contour.

*No integer is crossed.* For `0 < b ≤ a ≤ ½` the closed slanted strip between `L(b)` and `L(a)`
contains no integer, so the two contour integrals agree by the rotated-rectangle Cauchy argument of
`Zeta/RiemannSiegel/Shift.lean` with the residue replaced by zero.

*The crossing point may be sent to the origin.* Along `L(a)` the integrand is dominated, uniformly
in `a ∈ (0, ½]`, by an integrable function of the contour parameter alone, so `a → 0` may be taken
under the integral sign. The majorant must carry the singular factor `|w|^{-Re s - 1}`, integrable
precisely because `Re s < 0`; producing it is what the lower bound
`Zeta.RiemannSiegel.norm_sin_pi_mul_line_ge_min` — rather than the half-integer bound, which
degenerates as `a → 0` — is for.

## Main results

* `Zeta.RiemannSiegel.contourIntegral_eq_contourIntegral_of_le_half`: `I(s, a) = I(s, b)` for
  `0 < b ≤ a ≤ ½`;
* `Zeta.RiemannSiegel.norm_contourIntegrand_le_of_le_half`: the majorant, uniform in `a`;
* `Zeta.RiemannSiegel.contourIntegral_zero_eq_contourIntegral_half`: `I(s, 0) = I(s, ½)`;
* `Zeta.RiemannSiegel.contourIntegral_half_eq_neg_exp_mul_sin_mul_hankelIntegral`: the Hankel-ray
  representation `I(s, ½) = -e^{iπ(1+s)/4} sin (πs/2) Φ(s)`.
-/
@[expose] public section


open Complex Filter MeasureTheory Topology

open scoped Real

namespace Zeta.RiemannSiegel

/-! ### Moving between two contours that cross inside `(0, ½]` -/

/-- **The Riemann–Siegel contour integral is independent of the crossing point inside
`(0, ½]`.** -/
theorem contourIntegral_eq_contourIntegral_of_le_half (s : ℂ) {a b : ℝ} (hb0 : 0 < b)
    (hba : b ≤ a) (ha : a ≤ 1 / 2) : contourIntegral s a = contourIntegral s b := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have ha0 : 0 < a := hb0.trans_le hba
  have hβ0 : 0 < b / Real.sqrt 2 := div_pos hb0 hs2
  have hβα : b / Real.sqrt 2 ≤ a / Real.sqrt 2 := by gcongr
  -- the rotated rectangle contains no pole of the integrand
  have key : ∀ᶠ H : ℝ in atTop, RectangleIntegral (rotatedIntegrand s)
      (((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I)
      (((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I) = 0 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    set z : ℂ := ((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I with hzdef
    set w : ℂ := ((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I with hwdef
    have hzre : z.re = b / Real.sqrt 2 := by rw [hzdef]; simp
    have hwre : w.re = a / Real.sqrt 2 := by rw [hwdef]; simp
    have hzw2 : z.im ≤ w.im := by rw [hzdef, hwdef]; simpa using (by linarith : -H ≤ H)
    refine HolomorphicOn.vanishesOnRectangle (U := Rectangle z w) (fun ζ hζ ↦ ?_) subset_rfl
    obtain ⟨hr1, hr2, -, -⟩ := (mem_Rect (by rw [hzre, hwre]; exact hβα) hzw2 ζ).1 hζ
    rw [hzre] at hr1; rw [hwre] at hr2
    refine (differentiableAt_rotatedIntegrand s (hβ0.trans_le hr1) fun k hk ↦ ?_)
      |>.differentiableWithinAt
    -- the abscissa of a rotated integer misses `[b/√2, a/√2] ⊆ (0, 1/2]`
    have hkre : (k : ℝ) / Real.sqrt 2 = ζ.re := by
      rw [hk, ← Complex.ofReal_intCast, re_exp_pi_div_four_mul_I_mul_ofReal]
    have hk1 : b ≤ (k : ℝ) := (div_le_div_iff_of_pos_right hs2).1 (by rw [hkre]; exact hr1)
    have hk2 : (k : ℝ) ≤ a := (div_le_div_iff_of_pos_right hs2).1 (by rw [hkre]; exact hr2)
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by exact_mod_cast hb0.trans_le hk1 : (0 : ℤ) < k)
    linarith
  -- the truncated rectangle converges to the difference of the two contour integrals
  have hlim := tendsto_RectangleIntegral_rotatedIntegrand s hβ0 hβα
    (integrable_contourIntegrand_of_le_half s ha0 ha)
    (integrable_contourIntegrand_of_le_half s hb0 (hba.trans ha))
  exact sub_eq_zero.1 (tendsto_nhds_unique hlim
    (Tendsto.congr' (by filter_upwards [key] with H hH using hH.symm) tendsto_const_nhds))

/-! ### A majorant uniform in the crossing point -/

/-- **A majorant for the Riemann–Siegel integrand along `L(a)`, uniform over `0 < a ≤ ½`.** -/
theorem norm_contourIntegrand_le_of_le_half {s : ℂ} (hs : s.re ≤ 0) {a : ℝ} (ha0 : 0 < a)
    (ha : a ≤ 1 / 2) {w : ℝ} (hw : w ≠ 0) :
    ‖contourIntegrand s a w‖
      ≤ Real.exp (3 * π * |s.im| / 4 + (-s.re + 1) / 2 + 1) *
          ((1 + |w| ^ (-s.re - 1)) *
            Real.exp (-(π * w ^ 2) + (2 * (-s.re) + 2 + π) * |w|)) := by
  have hpi := Real.pi_pos
  set p : ℝ := -s.re with hp
  have hp0 : (0 : ℝ) ≤ p := by rw [hp]; linarith
  have hw0 : (0 : ℝ) < |w| := abs_pos.2 hw
  have hxpos : (0 : ℝ) < ‖line a w‖ := norm_pos_iff.2 (line_ne_zero ha0.ne' w)
  have hwx : |w| ≤ ‖line a w‖ := by simpa using Complex.abs_im_le_norm (line a w)
  have hxub : ‖line a w‖ ≤ 1 / 2 + 2 * |w| := (norm_line_le ha0.le w).trans (by linarith)
  have hZ0 : (0 : ℝ) ≤ |w| ^ (p - 1) := Real.rpow_nonneg (abs_nonneg w) _
  have hG0 : (0 : ℝ) < Real.exp (-(2 * π * w ^ 2) + π * |w|) := Real.exp_pos _
  -- the modulus of the integrand, factor by factor
  have hquot : Real.exp (-(2 * π * (a + w) * w)) / (2 * ‖sin (π * line a w)‖)
      ≤ (1 + 1 / (2 * ‖line a w‖)) * Real.exp (-(2 * π * w ^ 2) + π * |w|) := by
    have hnum : Real.exp (-(2 * π * (a + w) * w)) ≤ Real.exp (-(2 * π * w ^ 2) + π * |w|) :=
      Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right ha (abs_nonneg w),
        mul_le_mul_of_nonneg_left (neg_le_abs w) ha0.le])
    have hden : 1 / (2 * ‖sin (π * line a w)‖) ≤ 1 + 1 / (2 * ‖line a w‖) := by
      have hmin := norm_sin_pi_mul_line_ge_min ha0.le ha w
      have hinv : (0 : ℝ) ≤ 1 / (2 * ‖line a w‖) := by positivity
      rcases min_cases (1 / 2 : ℝ) ‖line a w‖ with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at hmin
      · linarith [one_div_le_one_div_of_le one_pos
          (by linarith : (1 : ℝ) ≤ 2 * ‖sin (π * line a w)‖)]
      · linarith [one_div_le_one_div_of_le (by linarith)
          (by linarith : 2 * ‖line a w‖ ≤ 2 * ‖sin (π * line a w)‖)]
    rw [div_eq_mul_one_div]
    exact (mul_le_mul hnum hden (by positivity) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hmodulus : ‖contourIntegrand s a w‖
      ≤ Real.exp (3 * π * |s.im| / 4) *
        ((‖line a w‖ ^ p + ‖line a w‖ ^ (p - 1) / 2) *
          Real.exp (-(2 * π * w ^ 2) + π * |w|)) := by
    have hrp : ‖line a w‖ ^ p * (1 + 1 / (2 * ‖line a w‖))
        = ‖line a w‖ ^ p + ‖line a w‖ ^ (p - 1) / 2 := by
      rw [Real.rpow_sub hxpos, Real.rpow_one]
      field_simp
    rw [norm_contourIntegrand_eq_exp s ha0, Real.exp_add, ← Real.rpow_def_of_pos hxpos,
      Complex.neg_re, ← hp]
    calc ‖line a w‖ ^ p * Real.exp (slantArg (line a w) * s.im) *
          (Real.exp (-(2 * π * (a + w) * w)) / (2 * ‖sin (π * line a w)‖))
        ≤ ‖line a w‖ ^ p * Real.exp (3 * π * |s.im| / 4) *
          ((1 + 1 / (2 * ‖line a w‖)) * Real.exp (-(2 * π * w ^ 2) + π * |w|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 (slantArg_line_mul_im_le s ha0 w)) (Real.rpow_nonneg hxpos.le _))
            hquot (by positivity) (by positivity)
      _ = _ := by rw [← hrp]; ring
  -- the two powers of the modulus, as exponentials in `|w|`
  have hE1 : (1 : ℝ) ≤ Real.exp ((p + 1) * (1 / 2 + 2 * |w|)) :=
    Real.one_le_exp (by nlinarith [abs_nonneg w])
  have hpow : ‖line a w‖ ^ p ≤ Real.exp ((p + 1) * (1 / 2 + 2 * |w|)) := by
    rw [Real.rpow_def_of_pos hxpos]
    exact Real.exp_le_exp.2 (by nlinarith [Real.log_le_sub_one_of_pos hxpos, abs_nonneg w])
  have hpowSub : ‖line a w‖ ^ (p - 1)
      ≤ |w| ^ (p - 1) + Real.exp ((p + 1) * (1 / 2 + 2 * |w|)) := by
    rcases le_or_gt 0 (p - 1) with hq | hq
    · have hpos : (0 : ℝ) < 1 / 2 + 2 * |w| := by positivity
      refine le_add_of_nonneg_of_le hZ0 ((Real.rpow_le_rpow hxpos.le hxub hq).trans ?_)
      rw [Real.rpow_def_of_pos hpos]
      exact Real.exp_le_exp.2 (by nlinarith [Real.log_le_sub_one_of_pos hpos, abs_nonneg w])
    · linarith [Real.rpow_le_rpow_of_nonpos hw0 hwx hq.le,
        (Real.exp_pos ((p + 1) * (1 / 2 + 2 * |w|))).le]
  -- both powers are absorbed by `3/2 (1 + |w|^{p-1})` times the exponential
  have hbracket : ‖line a w‖ ^ p + ‖line a w‖ ^ (p - 1) / 2
      ≤ (1 + |w| ^ (p - 1)) * (3 / 2 * Real.exp ((p + 1) * (1 / 2 + 2 * |w|))) := by
    nlinarith [hpow, hpowSub, mul_nonneg hZ0 (sub_nonneg.2 hE1)]
  -- the target Gaussian exceeds the one just produced by the factor `e^{1 + π w²} ≥ 3/2`
  have he : (3 : ℝ) / 2 ≤ Real.exp (1 + π * w ^ 2) := by
    linarith [Real.add_one_le_exp (1 + π * w ^ 2), mul_nonneg hpi.le (sq_nonneg w)]
  have hgauss : 3 / 2 * (Real.exp ((p + 1) * (1 / 2 + 2 * |w|)) *
        Real.exp (-(2 * π * w ^ 2) + π * |w|))
      ≤ Real.exp ((p + 1) / 2 + 1) * Real.exp (-(π * w ^ 2) + (2 * p + 2 + π) * |w|) :=
    (mul_le_mul_of_nonneg_right he (by positivity)).trans_eq
      (by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring)
  rw [show 3 * π * |s.im| / 4 + (p + 1) / 2 + 1 = 3 * π * |s.im| / 4 + ((p + 1) / 2 + 1) by ring,
    Real.exp_add, mul_assoc]
  refine hmodulus.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  calc (‖line a w‖ ^ p + ‖line a w‖ ^ (p - 1) / 2) * Real.exp (-(2 * π * w ^ 2) + π * |w|)
      ≤ (1 + |w| ^ (p - 1)) * (3 / 2 * (Real.exp ((p + 1) * (1 / 2 + 2 * |w|)) *
          Real.exp (-(2 * π * w ^ 2) + π * |w|))) := by
        nlinarith [mul_le_mul_of_nonneg_right hbracket hG0.le]
    _ ≤ (1 + |w| ^ (p - 1)) * (Real.exp ((p + 1) / 2 + 1) *
          Real.exp (-(π * w ^ 2) + (2 * p + 2 + π) * |w|)) :=
        mul_le_mul_of_nonneg_left hgauss (by positivity)
    _ = _ := by ring

/-! ### The contour through the origin -/

/-- **The Riemann–Siegel contour may be pushed onto the pole at the origin** for `Re s < 0`
(`riemann_siegel_zero.tex`, `lem:rsz_deform`). -/
theorem contourIntegral_zero_eq_contourIntegral_half {s : ℂ} (hs : s.re < 0) :
    contourIntegral s 0 = contourIntegral s (1 / 2) := by
  let α : ℕ → ℝ := fun n ↦ 1 / 2 * (1 / ((n : ℝ) + 1))
  have hα0 : ∀ n, 0 < α n := fun n ↦ by positivity
  have hαle : ∀ n, α n ≤ 1 / 2 := fun n ↦ by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; simp
    simpa [α] using mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hαtend : Tendsto α atTop (𝓝 0) := by
    simpa [α] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)
  have hne : ∀ᵐ w : ℝ, w ≠ 0 := by rw [ae_iff]; simp
  -- the majorant
  have hgint : Integrable fun w : ℝ ↦
      Real.exp (3 * π * |s.im| / 4 + (-s.re + 1) / 2 + 1) *
        ((1 + |w| ^ (-s.re - 1)) *
          Real.exp (-(π * w ^ 2) + (2 * (-s.re) + 2 + π) * |w|)) := by
    have h1 := integrable_exp_neg_pi_mul_sq_add_mul_abs (2 * (-s.re) + 2 + π)
    have h2 := integrable_rpow_abs_mul_exp_neg_pi_mul_sq_add_mul_abs
      (q := -s.re - 1) (by linarith) (2 * (-s.re) + 2 + π)
    refine ((h1.add h2).const_mul
      (Real.exp (3 * π * |s.im| / 4 + (-s.re + 1) / 2 + 1))).congr
      (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [Pi.add_apply]
    ring
  -- dominated convergence along the contours `L(α n)`
  have hlim : Tendsto (fun n : ℕ ↦ ∫ w : ℝ, contourIntegrand s (α n) w) atTop
      (𝓝 (∫ w : ℝ, contourIntegrand s 0 w)) := by
    refine tendsto_integral_of_dominated_convergence _
      (fun n ↦ (integrable_contourIntegrand_of_le_half s (hα0 n) (hαle n)).aestronglyMeasurable)
      hgint (fun n ↦ ?_) ?_
    · filter_upwards [hne] with w hw using
        norm_contourIntegrand_le_of_le_half hs.le (hα0 n) (hαle n) hw
    · filter_upwards [hne] with w hw
      have hslit : exp ((π / 4 : ℝ) * I) * line 0 w ∈ slitPlane := by
        refine mem_slitPlane_iff.2 (Or.inr ?_)
        rw [exp_pi_div_four_mul_I_mul_line]
        simpa using mul_ne_zero (Real.sqrt_pos.2 two_pos).ne' hw
      have hnotInt : ∀ k : ℤ, line 0 w ≠ (k : ℂ) := fun k hk ↦
        hw (by simpa [line_im] using congrArg Complex.im hk)
      have hcont : ContinuousAt (integrand s) (line 0 w) :=
        (differentiableAt_integrand s hslit hnotInt).continuousAt
      have hline : Tendsto (fun n : ℕ ↦ line (α n) w) atTop (𝓝 (line 0 w)) :=
        ((by unfold line; fun_prop : Continuous fun t : ℝ ↦ line t w).tendsto 0).comp hαtend
      exact hcont.tendsto.comp hline
  have h1 : Tendsto (fun n : ℕ ↦ contourIntegral s (α n)) atTop (𝓝 (contourIntegral s 0)) := by
    simpa only [contourIntegral] using hlim.const_mul _
  refine tendsto_nhds_unique h1 (Tendsto.congr' ?_ tendsto_const_nhds)
  filter_upwards with n using
    contourIntegral_eq_contourIntegral_of_le_half s (hα0 n) (hαle n) le_rfl

/-- **The Hankel-ray representation of the Riemann–Siegel contour integral**
(`riemann_siegel_zero.tex`, `lem:rsz_hankel`): for `Re s < 0`,
`I(s, ½) = -e^{iπ(1+s)/4} sin (πs/2) Φ(s)`. -/
theorem contourIntegral_half_eq_neg_exp_mul_sin_mul_hankelIntegral {s : ℂ} (hs : s.re < 0) :
    contourIntegral s (1 / 2)
      = -(exp ((π / 4 : ℝ) * I * (1 + s)) * sin ((π : ℂ) * s / 2)) * hankelIntegral s := by
  rw [← contourIntegral_zero_eq_contourIntegral_half hs]
  exact contourIntegral_zero_eq_neg_exp_mul_sin_mul_hankelIntegral hs

end Zeta.RiemannSiegel
