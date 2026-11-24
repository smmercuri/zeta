/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Gaussian majorants and the absolute moments of a Gaussian

Two gaps in Mathlib's Gaussian API, both needed by the Riemann–Siegel estimates: the majorant
`w ↦ exp (-πw² + b|w|)` (`riemann_siegel.tex`, `thm:rs_remainder_bound`), a Gaussian with two
peaks at `±b/2π`, so its integral is at most *twice* `exp (b²/4π)`; and the absolute moments
`∫ |w|^n e^{-bw²} dw` and their tails (`riemann_siegel_first.tex`, `lem:rsf_inner`).

## Main results

* `Real.exp_neg_pi_mul_sq_add_mul_abs_le`: the pointwise majorant by two translated Gaussians;
* `integrable_exp_neg_pi_mul_sq_add_mul_abs`: integrability;
* `integral_exp_neg_pi_mul_sq_add_mul_abs_le`: `∫ exp (-πw² + b|w|) dw ≤ 2 exp (b²/4π)`;
* `integrable_rpow_abs_mul_exp_neg_mul_sq`,
  `integrable_rpow_abs_mul_exp_neg_pi_mul_sq_add_mul_abs`: the same Gaussians still integrate
  against an integrable power singularity `|w|^q`, `q > -1`, at the origin;
* `integral_Ioi_pow_add_two_mul_exp_neg_mul_sq`: the recursion
  `∫_{w > 0} w^{n+2} e^{-bw²} = ((n+1)/2b) ∫_{w > 0} w^n e^{-bw²}`;
* `integral_abs_mul_exp_neg_mul_sq`, `integral_sq_mul_exp_neg_mul_sq`,
  `integral_abs_pow_three_mul_exp_neg_mul_sq`: `∫ |w| e^{-bw²} dw = 1/b`,
  `∫ w² e^{-bw²} dw = √(π/b)/2b` and `∫ |w|³ e^{-bw²} dw = 1/b²`;
* `integral_pow_four_mul_exp_neg_mul_sq`, `integral_pow_six_mul_exp_neg_mul_sq`:
  `∫ w⁴ e^{-bw²} dw = 3√(π/b)/4b²` and `∫ w⁶ e^{-bw²} dw = 15√(π/b)/8b³`;
* `integral_exp_neg_mul_sq_mul_poly`: a Gaussian against an arbitrary cubic in `|w|`;
* `integrable_exp_neg_mul_sq_mul_even_poly`, `integral_exp_neg_mul_sq_mul_even_poly`,
  `integral_exp_neg_mul_sq_mul_even_poly_comp_add_right`: a Gaussian against an arbitrary even
  polynomial of degree six, at the origin and translated;
* `integrable_exp_neg_mul_sq_mul_even_quartic`,
  `integral_exp_neg_mul_sq_mul_even_quartic_comp_add_right`: the same in degree four;
* `integrable_abs_pow_mul_exp_neg_mul_sq_add_mul_abs`,
  `integrable_pow_add_mul_abs_mul_exp_neg_mul_sq_add_mul_abs`: the Gaussian with a linear term in
  `|w|` integrates against a power of `|w|`, and against a power of an affine function of `|w|`;
* `integral_abs_pow_add_two_mul_exp_neg_mul_sq`: the recursion
  `∫ |w|^{n+2} e^{-bw²} = ((n+1)/2b) ∫ |w|^n e^{-bw²}` on the whole line;
* `integral_abs_pow_even_mul_exp_neg_mul_sq`,
  `integral_abs_pow_odd_mul_exp_neg_mul_sq`: the closed forms
  `∫ |w|^{2m} e^{-bw²} dw = ((2m)!/(4^m m!)) √(π/b)/b^m` and
  `∫ |w|^{2m+1} e^{-bw²} dw = m!/b^{m+1}`;
* `integral_Ioi_exp_neg_mul_sq_le`, `integral_compl_Icc_exp_neg_mul_sq_le`: the tails
  `∫_{w > c} e^{-bw²} dw ≤ e^{-bc²}/(2bc)` and `∫_{|w| > c} e^{-bw²} dw ≤ e^{-bc²}/(bc)`;
* `integral_Ioi_pow_three_mul_exp_neg_mul_sq`, `integral_compl_Icc_abs_mul_exp_neg_mul_sq`,
  `integral_compl_Icc_abs_pow_three_mul_exp_neg_mul_sq`,
  `integral_compl_Icc_sq_mul_exp_neg_mul_sq_le`: the higher tails
  `∫_{|w| > c} |w| e^{-bw²} dw = e^{-bc²}/b`, `∫_{|w| > c} |w|³ e^{-bw²} dw = e^{-bc²}(c²/b + 1/b²)`
  and `∫_{|w| > c} w² e^{-bw²} dw ≤ e^{-bc²}(c/b + 1/b²c)`;
* `integral_compl_Icc_exp_neg_mul_sq_mul_poly_le`,
  `integral_compl_Icc_exp_neg_mul_sq_mul_poly_comp_add_right_le`: the tail of a Gaussian against
  an arbitrary cubic in `|w|`, at the origin and translated;
* `integral_compl_Icc_exp_neg_mul_sq_comp_add_right_le`: the tail of a translated Gaussian alone,
  `∫_{|w| > W} e^{-b(w + d)²} dw ≤ e^{-bA²}/bA` at the surviving radius `A ≤ W - |d|`;
* `integral_compl_Icc_eq_two_mul_integral_Ioi`: the tail of an even function outside a symmetric
  interval is twice its tail on the half-line.
-/
@[expose] public section


open MeasureTheory Real

open scoped Nat

namespace Real

/-- A Gaussian carrying a linear term in `|w|` is dominated by the two Gaussians centred at its
peaks `±b/2π`. -/
theorem exp_neg_pi_mul_sq_add_mul_abs_le (b w : ℝ) :
    exp (-(π * w ^ 2) + b * |w|)
      ≤ exp (b ^ 2 / (4 * π)) *
        (exp (-π * (w - b / (2 * π)) ^ 2) + exp (-π * (w + b / (2 * π)) ^ 2)) := by
  have hpi : (π : ℝ) ≠ 0 := pi_ne_zero
  rcases abs_cases w with ⟨hw, -⟩ | ⟨hw, -⟩
  · have key : -(π * w ^ 2) + b * |w| = b ^ 2 / (4 * π) + -π * (w - b / (2 * π)) ^ 2 := by
      rw [hw]; field_simp; ring
    rw [key, exp_add]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (exp_pos _).le) (exp_pos _).le
  · have key : -(π * w ^ 2) + b * |w| = b ^ 2 / (4 * π) + -π * (w + b / (2 * π)) ^ 2 := by
      rw [hw]; field_simp; ring
    rw [key, exp_add]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (exp_pos _).le) (exp_pos _).le

end Real

private theorem integrable_exp_neg_pi_mul_sub_sq (c : ℝ) :
    Integrable fun w : ℝ ↦ exp (-π * (w - c) ^ 2) :=
  (integrable_exp_neg_mul_sq pi_pos).comp_sub_right c

private theorem integrable_exp_neg_pi_mul_add_sq (c : ℝ) :
    Integrable fun w : ℝ ↦ exp (-π * (w + c) ^ 2) := by
  simpa [sub_neg_eq_add] using integrable_exp_neg_pi_mul_sub_sq (-c)

private theorem integral_exp_neg_pi_mul_sub_sq (c : ℝ) :
    ∫ w : ℝ, exp (-π * (w - c) ^ 2) = 1 := by
  rw [show (∫ w : ℝ, exp (-π * (w - c) ^ 2))
      = ∫ w : ℝ, (fun u : ℝ ↦ exp (-π * u ^ 2)) (w - c) from rfl,
    integral_sub_right_eq_self (fun u : ℝ ↦ exp (-π * u ^ 2)) c, integral_gaussian,
    div_self pi_ne_zero, sqrt_one]

private theorem integral_exp_neg_pi_mul_add_sq (c : ℝ) :
    ∫ w : ℝ, exp (-π * (w + c) ^ 2) = 1 := by
  simpa [sub_neg_eq_add] using integral_exp_neg_pi_mul_sub_sq (-c)

private theorem integrable_majorant (b : ℝ) :
    Integrable fun w : ℝ ↦ exp (b ^ 2 / (4 * π)) *
      (exp (-π * (w - b / (2 * π)) ^ 2) + exp (-π * (w + b / (2 * π)) ^ 2)) :=
  ((integrable_exp_neg_pi_mul_sub_sq _).add (integrable_exp_neg_pi_mul_add_sq _)).const_mul _

/-- The Gaussian with a linear term in `|w|` is integrable. -/
theorem integrable_exp_neg_pi_mul_sq_add_mul_abs (b : ℝ) :
    Integrable fun w : ℝ ↦ exp (-(π * w ^ 2) + b * |w|) := by
  refine (integrable_majorant b).mono' (by fun_prop) (Filter.Eventually.of_forall fun w ↦ ?_)
  rw [norm_of_nonneg (exp_pos _).le]
  exact exp_neg_pi_mul_sq_add_mul_abs_le b w

/-- An explicit bound for the integral of a Gaussian with a linear term in `|w|`. -/
theorem integral_exp_neg_pi_mul_sq_add_mul_abs_le (b : ℝ) :
    ∫ w : ℝ, exp (-(π * w ^ 2) + b * |w|) ≤ 2 * exp (b ^ 2 / (4 * π)) := by
  calc ∫ w : ℝ, exp (-(π * w ^ 2) + b * |w|)
      ≤ ∫ w : ℝ, exp (b ^ 2 / (4 * π)) *
          (exp (-π * (w - b / (2 * π)) ^ 2) + exp (-π * (w + b / (2 * π)) ^ 2)) :=
        integral_mono (integrable_exp_neg_pi_mul_sq_add_mul_abs b) (integrable_majorant b)
          (exp_neg_pi_mul_sq_add_mul_abs_le b)
    _ = 2 * exp (b ^ 2 / (4 * π)) := by
        rw [integral_const_mul, integral_add (integrable_exp_neg_pi_mul_sub_sq _)
          (integrable_exp_neg_pi_mul_add_sq _), integral_exp_neg_pi_mul_sub_sq,
          integral_exp_neg_pi_mul_add_sq]
        ring

/-- A Gaussian integrates against a power singularity at the origin when that singularity is
itself integrable. -/
theorem integrable_rpow_abs_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {q : ℝ} (hq : -1 < q) :
    Integrable fun w : ℝ ↦ |w| ^ q * exp (-b * w ^ 2) := by
  have hIoi : IntegrableOn (fun w : ℝ ↦ |w| ^ q * exp (-b * w ^ 2)) (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq hb hq).congr_fun
      (fun x hx ↦ by rw [abs_of_pos hx]) measurableSet_Ioi
  have hIio : IntegrableOn (fun w : ℝ ↦ |w| ^ q * exp (-b * w ^ 2)) (Set.Iio 0) := by
    simpa using hIoi.comp_neg
  rw [← integrableOn_univ, ← Set.Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hIio, hIoi⟩

/-- The Gaussian with a linear term in `|w|` integrates against a power singularity at the
origin. -/
theorem integrable_rpow_abs_mul_exp_neg_pi_mul_sq_add_mul_abs {q : ℝ} (hq : -1 < q) (b : ℝ) :
    Integrable fun w : ℝ ↦ |w| ^ q * exp (-(π * w ^ 2) + b * |w|) := by
  have hmaj : Integrable fun w : ℝ ↦ exp (b ^ 2 / (2 * π)) * (|w| ^ q * exp (-(π / 2) * w ^ 2)) :=
    (integrable_rpow_abs_mul_exp_neg_mul_sq (by positivity) hq).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun w : ℝ ↦ |w| ^ q * exp (-(π * w ^ 2) + b * |w|)) volume := by
    have h1 := (integrable_rpow_abs_mul_exp_neg_mul_sq pi_pos hq).aestronglyMeasurable
    have h2 : Continuous fun w : ℝ ↦ exp (b * |w|) := by fun_prop
    refine (h1.mul h2.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [Pi.mul_apply]
    rw [mul_assoc, ← exp_add, show -π * w ^ 2 + b * |w| = -(π * w ^ 2) + b * |w| by ring]
  refine hmaj.mono' hmeas (Filter.Eventually.of_forall fun w ↦ ?_)
  -- `b|w| ≤ (π/2)w² + b²/2π`, by completing the square
  have hkey : -(π * w ^ 2) + b * |w| ≤ b ^ 2 / (2 * π) + -(π / 2) * w ^ 2 := by
    rw [← sub_nonneg, ← sq_abs w,
      show b ^ 2 / (2 * π) + -(π / 2) * |w| ^ 2 - (-(π * |w| ^ 2) + b * |w|)
        = (π * |w| - b) ^ 2 / (2 * π) by field_simp; ring]
    positivity
  rw [norm_of_nonneg (by positivity)]
  calc |w| ^ q * exp (-(π * w ^ 2) + b * |w|)
      ≤ |w| ^ q * exp (b ^ 2 / (2 * π) + -(π / 2) * w ^ 2) := by gcongr
    _ = exp (b ^ 2 / (2 * π)) * (|w| ^ q * exp (-(π / 2) * w ^ 2)) := by
        rw [exp_add]; ring

section Moments

variable {b : ℝ}

/-- A Gaussian integrates against any natural power on the half-line. -/
theorem integrableOn_pow_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    IntegrableOn (fun w : ℝ ↦ w ^ n * exp (-b * w ^ 2)) (Set.Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_sq hb
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))

/-- A Gaussian integrates against any natural power of `|·|`. -/
theorem integrable_abs_pow_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    Integrable fun w : ℝ ↦ |w| ^ n * exp (-b * w ^ 2) := by
  simpa using integrable_rpow_abs_mul_exp_neg_mul_sq hb
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))

/-- A Gaussian carrying a linear term in `|w|` integrates against any natural power of `|·|`. -/
theorem integrable_abs_pow_mul_exp_neg_mul_sq_add_mul_abs (hb : 0 < b) (c : ℝ) (n : ℕ) :
    Integrable fun w : ℝ ↦ |w| ^ n * exp (-b * w ^ 2 + c * |w|) := by
  have hmaj : Integrable fun w : ℝ ↦ exp (c ^ 2 / (2 * b)) * (|w| ^ n * exp (-(b / 2) * w ^ 2)) :=
    (integrable_abs_pow_mul_exp_neg_mul_sq (by positivity) n).const_mul _
  refine hmaj.mono' (by fun_prop) (.of_forall fun w ↦ ?_)
  -- `c|w| ≤ (b/2)w² + c²/2b`, by completing the square
  have hkey : -b * w ^ 2 + c * |w| ≤ c ^ 2 / (2 * b) + -(b / 2) * w ^ 2 := by
    rw [← sub_nonneg, ← sq_abs w,
      show c ^ 2 / (2 * b) + -(b / 2) * |w| ^ 2 - (-b * |w| ^ 2 + c * |w|)
        = (b * |w| - c) ^ 2 / (2 * b) by field_simp; ring]
    positivity
  rw [norm_of_nonneg (by positivity)]
  calc |w| ^ n * exp (-b * w ^ 2 + c * |w|)
      ≤ |w| ^ n * exp (c ^ 2 / (2 * b) + -(b / 2) * w ^ 2) := by gcongr
    _ = exp (c ^ 2 / (2 * b)) * (|w| ^ n * exp (-(b / 2) * w ^ 2)) := by rw [exp_add]; ring

/-- A Gaussian carrying a linear term in `|w|` integrates against any power of an affine
function of `|w|`. -/
theorem integrable_pow_add_mul_abs_mul_exp_neg_mul_sq_add_mul_abs (hb : 0 < b) {A β : ℝ}
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (c : ℝ) (n : ℕ) :
    Integrable fun w : ℝ ↦ (A + β * |w|) ^ n * exp (-b * w ^ 2 + c * |w|) := by
  have h0 : Integrable fun w : ℝ ↦ exp (-b * w ^ 2 + c * |w|) := by
    simpa using integrable_abs_pow_mul_exp_neg_mul_sq_add_mul_abs hb c 0
  have hn : Integrable fun w : ℝ ↦ |w| ^ n * exp (-b * w ^ 2 + c * |w|) :=
    integrable_abs_pow_mul_exp_neg_mul_sq_add_mul_abs hb c n
  have hmaj : Integrable fun w : ℝ ↦ 2 ^ (n - 1) * (A ^ n * exp (-b * w ^ 2 + c * |w|)
      + β ^ n * (|w| ^ n * exp (-b * w ^ 2 + c * |w|))) :=
    ((h0.const_mul (A ^ n)).add (hn.const_mul (β ^ n))).const_mul _
  refine hmaj.mono' (by fun_prop) (.of_forall fun w ↦ ?_)
  rw [norm_of_nonneg (by positivity)]
  calc (A + β * |w|) ^ n * exp (-b * w ^ 2 + c * |w|)
      ≤ 2 ^ (n - 1) * (A ^ n + (β * |w|) ^ n) * exp (-b * w ^ 2 + c * |w|) := by
        gcongr
        exact add_pow_le hA (by positivity) n
    _ = 2 ^ (n - 1) * (A ^ n * exp (-b * w ^ 2 + c * |w|)
          + β ^ n * (|w| ^ n * exp (-b * w ^ 2 + c * |w|))) := by rw [mul_pow]; ring

/-- A Gaussian beats any polynomial at infinity. -/
private theorem tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero (hb : 0 < b) (n : ℕ) :
    Filter.Tendsto (fun w : ℝ ↦ w ^ n * exp (-b * w ^ 2)) Filter.atTop (nhds 0) := by
  have hexp : Filter.Tendsto (fun x : ℝ ↦ exp (-(1 / 2) * x)) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun x : ℝ ↦ -(1 / 2) * x) Filter.atTop Filter.atBot :=
      Filter.tendsto_id.const_mul_atTop_of_neg (by norm_num)
    exact tendsto_exp_atBot.comp h
  refine ((rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb
    ((n : ℝ))).isBigO.trans_tendsto hexp).congr fun x ↦ ?_
  rw [rpow_natCast]

/-- The first moment of a Gaussian on a half-line. -/
theorem integral_Ioi_mul_exp_neg_mul_sq (hb : 0 < b) (c : ℝ) :
    ∫ w in Set.Ioi c, w * exp (-b * w ^ 2) = exp (-b * c ^ 2) / (2 * b) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hderiv : ∀ w : ℝ, HasDerivAt (fun w : ℝ ↦ -exp (-b * w ^ 2))
      (2 * b * (w * exp (-b * w ^ 2))) w := by
    intro w
    have h2 : HasDerivAt (fun w : ℝ ↦ exp (-b * w ^ 2))
        (exp (-b * w ^ 2) * (-b * (2 * w))) w := by
      simpa using ((hasDerivAt_pow 2 w).const_mul (-b)).exp
    rw [show 2 * b * (w * exp (-b * w ^ 2)) = -(exp (-b * w ^ 2) * (-b * (2 * w))) by ring]
    exact h2.neg
  have hlim : Filter.Tendsto (fun w : ℝ ↦ -exp (-b * w ^ 2)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb 0).neg
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (a := c)
    (Continuous.continuousWithinAt (by fun_prop)) (fun x _ ↦ hderiv x)
    ((integrable_mul_exp_neg_mul_sq hb).const_mul (2 * b)).integrableOn hlim
  rw [integral_const_mul, zero_sub, neg_neg] at key
  rw [eq_div_iff (by positivity : (2 : ℝ) * b ≠ 0)]
  linear_combination key

/-- The integration-by-parts recursion for the moments of a Gaussian on the half-line. -/
theorem integral_Ioi_pow_add_two_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    ∫ w in Set.Ioi (0 : ℝ), w ^ (n + 2) * exp (-b * w ^ 2)
      = ((n : ℝ) + 1) / (2 * b) * ∫ w in Set.Ioi (0 : ℝ), w ^ n * exp (-b * w ^ 2) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hderiv : ∀ w : ℝ, HasDerivAt (fun w : ℝ ↦ -(w ^ (n + 1) * exp (-b * w ^ 2)))
      (2 * b * (w ^ (n + 2) * exp (-b * w ^ 2))
        - ((n : ℝ) + 1) * (w ^ n * exp (-b * w ^ 2))) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℝ ↦ w ^ (n + 1)) (((n : ℝ) + 1) * w ^ n) w := by
      simpa using hasDerivAt_pow (n + 1) w
    have h2 : HasDerivAt (fun w : ℝ ↦ exp (-b * w ^ 2))
        (exp (-b * w ^ 2) * (-b * (2 * w))) w := by
      simpa using ((hasDerivAt_pow 2 w).const_mul (-b)).exp
    rw [show 2 * b * (w ^ (n + 2) * exp (-b * w ^ 2))
        - ((n : ℝ) + 1) * (w ^ n * exp (-b * w ^ 2))
        = -(((n : ℝ) + 1) * w ^ n * exp (-b * w ^ 2)
          + w ^ (n + 1) * (exp (-b * w ^ 2) * (-b * (2 * w)))) by ring]
    exact (h1.mul h2).neg
  have hint : IntegrableOn (fun w : ℝ ↦ 2 * b * (w ^ (n + 2) * exp (-b * w ^ 2))
      - ((n : ℝ) + 1) * (w ^ n * exp (-b * w ^ 2))) (Set.Ioi 0) :=
    ((integrableOn_pow_mul_exp_neg_mul_sq hb (n + 2)).const_mul _).sub
      ((integrableOn_pow_mul_exp_neg_mul_sq hb n).const_mul _)
  have hlim : Filter.Tendsto (fun w : ℝ ↦ -(w ^ (n + 1) * exp (-b * w ^ 2)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb (n + 1)).neg
  have key := integral_Ioi_of_hasDerivAt_of_tendsto
    (Continuous.continuousWithinAt (by fun_prop)) (fun x _ ↦ hderiv x) hint hlim
  rw [integral_sub ((integrableOn_pow_mul_exp_neg_mul_sq hb (n + 2)).const_mul _)
    ((integrableOn_pow_mul_exp_neg_mul_sq hb n).const_mul _), integral_const_mul,
    integral_const_mul] at key
  rw [show -((0 : ℝ) ^ (n + 1) * exp (-b * (0 : ℝ) ^ 2)) = 0 by simp, sub_zero] at key
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity : (2 : ℝ) * b ≠ 0)]
  linear_combination key

/-- The absolute moments of a Gaussian are twice its moments on the half-line. -/
private theorem integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul (n : ℕ) :
    ∫ w : ℝ, |w| ^ n * exp (-b * w ^ 2)
      = 2 * ∫ w in Set.Ioi (0 : ℝ), w ^ n * exp (-b * w ^ 2) := by
  have h := integral_comp_abs (f := fun u : ℝ ↦ u ^ n * exp (-b * u ^ 2))
  simp only [sq_abs] at h
  exact h

/-- The first absolute moment of a Gaussian. -/
theorem integral_abs_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, |w| * exp (-b * w ^ 2) = 1 / b := by
  have h := integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul (b := b) 1
  simp only [pow_one] at h
  rw [h, integral_Ioi_mul_exp_neg_mul_sq hb 0, show -b * (0 : ℝ) ^ 2 = 0 by ring, Real.exp_zero]
  field_simp

/-- The integration-by-parts recursion for the absolute moments of a Gaussian. -/
theorem integral_abs_pow_add_two_mul_exp_neg_mul_sq (hb : 0 < b) (n : ℕ) :
    ∫ w : ℝ, |w| ^ (n + 2) * exp (-b * w ^ 2)
      = ((n : ℝ) + 1) / (2 * b) * ∫ w : ℝ, |w| ^ n * exp (-b * w ^ 2) := by
  rw [integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul,
    integral_abs_pow_mul_exp_neg_mul_sq_eq_two_mul,
    integral_Ioi_pow_add_two_mul_exp_neg_mul_sq hb n]
  ring

/-- The even absolute moments of a Gaussian. -/
theorem integral_abs_pow_even_mul_exp_neg_mul_sq (hb : 0 < b) (m : ℕ) :
    ∫ w : ℝ, |w| ^ (2 * m) * exp (-b * w ^ 2)
      = (2 * m)! / (4 ^ m * m !) * (√(π / b) / b ^ m) := by
  induction m with
  | zero => simpa using integral_gaussian b
  | succ m ih =>
      have hb0 : b ≠ 0 := hb.ne'
      have hm : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
      have hfac : ((2 * m + 2)! : ℝ) = ((2 : ℝ) * m + 2) * (2 * m + 1) * (2 * m)! := by
        rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, integral_abs_pow_add_two_mul_exp_neg_mul_sq hb,
        ih, hfac, Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-- The odd absolute moments of a Gaussian. -/
theorem integral_abs_pow_odd_mul_exp_neg_mul_sq (hb : 0 < b) (m : ℕ) :
    ∫ w : ℝ, |w| ^ (2 * m + 1) * exp (-b * w ^ 2) = m ! / b ^ (m + 1) := by
  induction m with
  | zero => simpa using integral_abs_mul_exp_neg_mul_sq hb
  | succ m ih =>
      have hb0 : b ≠ 0 := hb.ne'
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring,
        integral_abs_pow_add_two_mul_exp_neg_mul_sq hb, ih, Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-- The second moment of a Gaussian. -/
theorem integral_sq_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, w ^ 2 * exp (-b * w ^ 2) = √(π / b) / (2 * b) := by
  have h := integral_abs_pow_even_mul_exp_neg_mul_sq hb 1
  simp only [show 2 * 1 = 2 from rfl, sq_abs, pow_one, Nat.factorial] at h
  rw [h]
  push_cast
  field_simp
  ring

private theorem even_four : Even 4 := ⟨2, rfl⟩

private theorem even_six : Even 6 := ⟨3, rfl⟩

/-- The fourth moment of a Gaussian. -/
theorem integral_pow_four_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, w ^ 4 * exp (-b * w ^ 2) = 3 * √(π / b) / (4 * b ^ 2) := by
  have h := integral_abs_pow_even_mul_exp_neg_mul_sq hb 2
  simp only [show 2 * 2 = 4 from rfl, even_four.pow_abs] at h
  rw [h, show ((4 : ℕ)! : ℝ) = 24 by norm_num [Nat.factorial],
    show ((2 : ℕ)! : ℝ) = 2 by norm_num [Nat.factorial]]
  field_simp
  ring

/-- The sixth moment of a Gaussian. -/
theorem integral_pow_six_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, w ^ 6 * exp (-b * w ^ 2) = 15 * √(π / b) / (8 * b ^ 3) := by
  have h := integral_abs_pow_even_mul_exp_neg_mul_sq hb 3
  simp only [show 2 * 3 = 6 from rfl, even_six.pow_abs] at h
  rw [h, show ((6 : ℕ)! : ℝ) = 720 by norm_num [Nat.factorial],
    show ((3 : ℕ)! : ℝ) = 6 by norm_num [Nat.factorial]]
  field_simp
  ring

/-- The third absolute moment of a Gaussian. -/
theorem integral_abs_pow_three_mul_exp_neg_mul_sq (hb : 0 < b) :
    ∫ w : ℝ, |w| ^ 3 * exp (-b * w ^ 2) = 1 / b ^ 2 := by
  simpa using integral_abs_pow_odd_mul_exp_neg_mul_sq hb 1

/-- The Gaussian tail on a half-line. -/
theorem integral_Ioi_exp_neg_mul_sq_le (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∫ w in Set.Ioi c, exp (-b * w ^ 2) ≤ exp (-b * c ^ 2) / (2 * b * c) := by
  have h1 : IntegrableOn (fun w : ℝ ↦ exp (-b * w ^ 2)) (Set.Ioi c) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have h2 : IntegrableOn (fun w : ℝ ↦ c⁻¹ * (w * exp (-b * w ^ 2))) (Set.Ioi c) :=
    ((integrable_mul_exp_neg_mul_sq hb).const_mul c⁻¹).integrableOn
  calc ∫ w in Set.Ioi c, exp (-b * w ^ 2)
      ≤ ∫ w in Set.Ioi c, c⁻¹ * (w * exp (-b * w ^ 2)) := by
        refine setIntegral_mono_on h1 h2 measurableSet_Ioi fun w hw ↦ ?_
        have hcw : (1 : ℝ) ≤ c⁻¹ * w := by
          rw [← div_eq_inv_mul]
          exact (one_le_div hc).2 (le_of_lt hw)
        calc exp (-b * w ^ 2) = 1 * exp (-b * w ^ 2) := (one_mul _).symm
          _ ≤ c⁻¹ * w * exp (-b * w ^ 2) :=
              mul_le_mul_of_nonneg_right hcw (exp_pos _).le
          _ = c⁻¹ * (w * exp (-b * w ^ 2)) := by ring
    _ = exp (-b * c ^ 2) / (2 * b * c) := by
        rw [integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq hb c]
        field_simp

/-- The third moment of a Gaussian on a half-line. -/
theorem integral_Ioi_pow_three_mul_exp_neg_mul_sq (hb : 0 < b) (c : ℝ) :
    ∫ w in Set.Ioi c, w ^ 3 * exp (-b * w ^ 2)
      = exp (-b * c ^ 2) * (c ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hderiv : ∀ w : ℝ, HasDerivAt
      (fun w : ℝ ↦ -((w ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) * exp (-b * w ^ 2)))
      (w ^ 3 * exp (-b * w ^ 2)) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℝ ↦ w ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) (2 * w / (2 * b)) w := by
      simpa using ((hasDerivAt_pow 2 w).div_const (2 * b)).add_const (1 / (2 * b ^ 2))
    have h2 : HasDerivAt (fun w : ℝ ↦ exp (-b * w ^ 2)) (exp (-b * w ^ 2) * (-b * (2 * w))) w := by
      simpa using ((hasDerivAt_pow 2 w).const_mul (-b)).exp
    refine (h1.mul h2).neg.congr_deriv ?_
    field_simp
    ring
  have hint : Integrable fun w : ℝ ↦ w ^ 3 * exp (-b * w ^ 2) := by
    refine (integrable_abs_pow_mul_exp_neg_mul_sq hb 3).mono' (by fun_prop)
      (.of_forall fun w ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (exp_pos _).le]
  have hlim : Filter.Tendsto
      (fun w : ℝ ↦ -((w ^ 2 / (2 * b) + 1 / (2 * b ^ 2)) * exp (-b * w ^ 2)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun w : ℝ ↦ exp (-b * w ^ 2)) Filter.atTop (nhds 0) := by
      simpa using tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb 0
    have h := ((tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero hb 2).const_mul
      (-(1 / (2 * b)))).add (h0.const_mul (-(1 / (2 * b ^ 2))))
    rw [show -(1 / (2 * b)) * (0 : ℝ) + -(1 / (2 * b ^ 2)) * 0 = 0 by ring] at h
    exact h.congr fun w ↦ by ring
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (a := c)
    (Continuous.continuousWithinAt (by fun_prop)) (fun x _ ↦ hderiv x) hint.integrableOn hlim
  rw [key, zero_sub, neg_neg]
  ring

/-- A point outside `Icc (-c) c` is at distance more than `c` from the origin. -/
private theorem lt_abs_of_mem_compl_Icc {c w : ℝ} (hw : w ∈ (Set.Icc (-c) c)ᶜ) : c < |w| := by
  rwa [Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le] at hw

/-- The integral of an even function outside a symmetric interval is twice its tail on the
half-line. -/
theorem integral_compl_Icc_eq_two_mul_integral_Ioi {f : ℝ → ℝ} (hf : Integrable f)
    (hfe : ∀ w : ℝ, f (-w) = f w) {c : ℝ} (hc : 0 ≤ c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, f w = 2 * ∫ w in Set.Ioi c, f w := by
  have hcompl : (Set.Icc (-c) c)ᶜ = Set.Iio (-c) ∪ Set.Ioi c := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      not_and_or, not_le]
  have hdisj : Disjoint (Set.Iio (-c)) (Set.Ioi c) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    have h1 : w < -c := hw
    have h2 : c < w := hw'
    linarith
  -- the left tail is the right tail reflected
  have hIio : ∫ w in Set.Iio (-c), f w = ∫ w in Set.Ioi c, f w := by
    have h := integral_comp_neg_Iic (-c) f
    rw [neg_neg] at h
    rw [← integral_Iic_eq_integral_Iio, ← h]
    exact setIntegral_congr_fun measurableSet_Iic fun w _ ↦ (hfe w).symm
  rw [hcompl, setIntegral_union hdisj measurableSet_Ioi hf.integrableOn hf.integrableOn, hIio]
  ring

/-- The Gaussian tail outside a symmetric interval. -/
theorem integral_compl_Icc_exp_neg_mul_sq_le (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, exp (-b * w ^ 2) ≤ exp (-b * c ^ 2) / (b * c) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hc0 : c ≠ 0 := hc.ne'
  rw [integral_compl_Icc_eq_two_mul_integral_Ioi (integrable_exp_neg_mul_sq hb)
    (fun w ↦ by rw [neg_sq]) hc.le]
  have heq : 2 * (exp (-b * c ^ 2) / (2 * b * c)) = exp (-b * c ^ 2) / (b * c) := by
    field_simp
  linarith [integral_Ioi_exp_neg_mul_sq_le hb hc]

/-- The tail of a Gaussian against `|w|`, outside a symmetric interval. -/
theorem integral_compl_Icc_abs_mul_exp_neg_mul_sq (hb : 0 < b) {c : ℝ} (hc : 0 ≤ c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, |w| * exp (-b * w ^ 2) = exp (-b * c ^ 2) / b := by
  have hb0 : b ≠ 0 := hb.ne'
  have hint : Integrable fun w : ℝ ↦ |w| * exp (-b * w ^ 2) := by
    simpa using integrable_abs_pow_mul_exp_neg_mul_sq hb 1
  have hIoi : ∫ w in Set.Ioi c, |w| * exp (-b * w ^ 2) = ∫ w in Set.Ioi c, w * exp (-b * w ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ by
      rw [abs_of_pos (lt_of_le_of_lt hc hw)]
  rw [integral_compl_Icc_eq_two_mul_integral_Ioi hint (fun w ↦ by rw [abs_neg, neg_sq]) hc, hIoi,
    integral_Ioi_mul_exp_neg_mul_sq hb c]
  field_simp

/-- The tail of a Gaussian against `|w|³`, outside a symmetric interval. -/
theorem integral_compl_Icc_abs_pow_three_mul_exp_neg_mul_sq (hb : 0 < b) {c : ℝ} (hc : 0 ≤ c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, |w| ^ 3 * exp (-b * w ^ 2)
      = exp (-b * c ^ 2) * (c ^ 2 / b + 1 / b ^ 2) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hint : Integrable fun w : ℝ ↦ |w| ^ 3 * exp (-b * w ^ 2) :=
    integrable_abs_pow_mul_exp_neg_mul_sq hb 3
  have hIoi : ∫ w in Set.Ioi c, |w| ^ 3 * exp (-b * w ^ 2)
      = ∫ w in Set.Ioi c, w ^ 3 * exp (-b * w ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ by
      rw [abs_of_pos (lt_of_le_of_lt hc hw)]
  rw [integral_compl_Icc_eq_two_mul_integral_Ioi hint (fun w ↦ by rw [abs_neg, neg_sq]) hc, hIoi,
    integral_Ioi_pow_three_mul_exp_neg_mul_sq hb c]
  ring

/-- **The tail of a Gaussian against `w²`, outside a symmetric interval.** -/
theorem integral_compl_Icc_sq_mul_exp_neg_mul_sq_le (hb : 0 < b) {c : ℝ} (hc : 0 < c) :
    ∫ w in (Set.Icc (-c) c)ᶜ, w ^ 2 * exp (-b * w ^ 2)
      ≤ exp (-b * c ^ 2) * (c / b + 1 / (b ^ 2 * c)) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have h2 : IntegrableOn (fun w : ℝ ↦ w ^ 2 * exp (-b * w ^ 2)) (Set.Icc (-c) c)ᶜ := by
    simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).integrableOn
  have h3 : IntegrableOn (fun w : ℝ ↦ c⁻¹ * (|w| ^ 3 * exp (-b * w ^ 2))) (Set.Icc (-c) c)ᶜ :=
    ((integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c⁻¹).integrableOn
  calc ∫ w in (Set.Icc (-c) c)ᶜ, w ^ 2 * exp (-b * w ^ 2)
      ≤ ∫ w in (Set.Icc (-c) c)ᶜ, c⁻¹ * (|w| ^ 3 * exp (-b * w ^ 2)) := by
        refine setIntegral_mono_on h2 h3 measurableSet_Icc.compl fun w hw ↦ ?_
        have hwc : c ≤ |w| := (lt_abs_of_mem_compl_Icc hw).le
        have hpow : w ^ 2 ≤ c⁻¹ * |w| ^ 3 := by
          rw [← sq_abs w, inv_mul_eq_div, le_div_iff₀ hc]
          nlinarith [abs_nonneg w]
        calc w ^ 2 * exp (-b * w ^ 2) ≤ c⁻¹ * |w| ^ 3 * exp (-b * w ^ 2) :=
              mul_le_mul_of_nonneg_right hpow (exp_pos _).le
          _ = c⁻¹ * (|w| ^ 3 * exp (-b * w ^ 2)) := by ring
    _ = c⁻¹ * (exp (-b * c ^ 2) * (c ^ 2 / b + 1 / b ^ 2)) := by
        rw [integral_const_mul, integral_compl_Icc_abs_pow_three_mul_exp_neg_mul_sq hb hc.le]
    _ = exp (-b * c ^ 2) * (c / b + 1 / (b ^ 2 * c)) := by
        field_simp

/-- The four monomials making up a cubic in `|w|` against a Gaussian. -/
private theorem exp_neg_mul_sq_mul_poly_eq (b c₀ c₁ c₂ c₃ : ℝ) :
    (fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3))
      = fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))
          + c₂ * (w ^ 2 * exp (-b * w ^ 2)) + c₃ * (|w| ^ 3 * exp (-b * w ^ 2)) := by
  funext w
  ring

/-- A Gaussian against a cubic in `|w|` is integrable. -/
theorem integrable_exp_neg_mul_sq_mul_poly (hb : 0 < b) (c₀ c₁ c₂ c₃ : ℝ) :
    Integrable fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3) := by
  rw [exp_neg_mul_sq_mul_poly_eq]
  refine (((((integrable_exp_neg_mul_sq hb).const_mul c₀).add ?_).add ?_).add ?_)
  · simpa using (integrable_abs_pow_mul_exp_neg_mul_sq hb 1).const_mul c₁
  · simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  · exact (integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c₃

/-- A Gaussian against a cubic in `|w|`, in terms of the first three absolute moments. -/
theorem integral_exp_neg_mul_sq_mul_poly (hb : 0 < b) (c₀ c₁ c₂ c₃ : ℝ) :
    ∫ w : ℝ, exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3)
      = c₀ * √(π / b) + c₁ / b + c₂ * (√(π / b) / (2 * b)) + c₃ / b ^ 2 := by
  have e0 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) :=
    (integrable_exp_neg_mul_sq hb).const_mul c₀
  have e1 : Integrable fun w : ℝ ↦ c₁ * (|w| * exp (-b * w ^ 2)) := by
    simpa using (integrable_abs_pow_mul_exp_neg_mul_sq hb 1).const_mul c₁
  have e2 : Integrable fun w : ℝ ↦ c₂ * (w ^ 2 * exp (-b * w ^ 2)) := by
    simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  have e3 : Integrable fun w : ℝ ↦ c₃ * (|w| ^ 3 * exp (-b * w ^ 2)) :=
    (integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c₃
  -- the partial sums are stated in `fun w ↦ …` form, since `Integrable.add` returns the `f + g`
  -- form, which `integral_add` will not match against the integrand below
  have e01 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2)) :=
    e0.add e1
  have e012 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))
      + c₂ * (w ^ 2 * exp (-b * w ^ 2)) := e01.add e2
  rw [exp_neg_mul_sq_mul_poly_eq, integral_add e012 e3, integral_add e01 e2, integral_add e0 e1,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_gaussian, integral_abs_mul_exp_neg_mul_sq hb, integral_sq_mul_exp_neg_mul_sq hb,
    integral_abs_pow_three_mul_exp_neg_mul_sq hb]
  ring

/-- **A Gaussian against a cubic in `|w|`, outside a symmetric interval.** -/
theorem integral_compl_Icc_exp_neg_mul_sq_mul_poly_le (hb : 0 < b) {A : ℝ} (hA : 0 < A)
    (hbA : 1 ≤ b * A ^ 2) {c₀ c₁ c₂ c₃ : ℝ} (h₀ : 0 ≤ c₀) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃) :
    ∫ w in (Set.Icc (-A) A)ᶜ, exp (-b * w ^ 2) * (c₀ + c₁ * |w| + c₂ * w ^ 2 + c₃ * |w| ^ 3)
      ≤ exp (-b * A ^ 2) / b * (c₀ / A + c₁ + 2 * c₂ * A + 2 * c₃ * A ^ 2) := by
  have hb0 : b ≠ 0 := hb.ne'
  have hA0 : A ≠ 0 := hA.ne'
  have hE : (0 : ℝ) < exp (-b * A ^ 2) := exp_pos _
  set s : Set ℝ := (Set.Icc (-A) A)ᶜ with hs
  have e0 : IntegrableOn (fun w : ℝ ↦ c₀ * exp (-b * w ^ 2)) s :=
    ((integrable_exp_neg_mul_sq hb).const_mul c₀).integrableOn
  have e1 : IntegrableOn (fun w : ℝ ↦ c₁ * (|w| * exp (-b * w ^ 2))) s := by
    simpa using ((integrable_abs_pow_mul_exp_neg_mul_sq hb 1).const_mul c₁).integrableOn
  have e2 : IntegrableOn (fun w : ℝ ↦ c₂ * (w ^ 2 * exp (-b * w ^ 2))) s := by
    simpa [sq_abs] using ((integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂).integrableOn
  have e3 : IntegrableOn (fun w : ℝ ↦ c₃ * (|w| ^ 3 * exp (-b * w ^ 2))) s :=
    ((integrable_abs_pow_mul_exp_neg_mul_sq hb 3).const_mul c₃).integrableOn
  -- the partial sums are stated in `fun w ↦ …` form, since `Integrable.add` returns the `f + g`
  -- form, which `integral_add`'s rewrite will not match against the integrand below
  have e01 : IntegrableOn (fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))) s :=
    e0.add e1
  have e012 : IntegrableOn (fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₁ * (|w| * exp (-b * w ^ 2))
      + c₂ * (w ^ 2 * exp (-b * w ^ 2))) s := e01.add e2
  -- each of the four monomials against its own tail
  have b0 : ∫ w in s, c₀ * exp (-b * w ^ 2) ≤ c₀ * (exp (-b * A ^ 2) / (b * A)) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_compl_Icc_exp_neg_mul_sq_le hb hA) h₀
  have b1 : ∫ w in s, c₁ * (|w| * exp (-b * w ^ 2)) = c₁ * (exp (-b * A ^ 2) / b) := by
    rw [integral_const_mul, integral_compl_Icc_abs_mul_exp_neg_mul_sq hb hA.le]
  have b2 : ∫ w in s, c₂ * (w ^ 2 * exp (-b * w ^ 2))
      ≤ c₂ * (exp (-b * A ^ 2) * (A / b + 1 / (b ^ 2 * A))) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_compl_Icc_sq_mul_exp_neg_mul_sq_le hb hA) h₂
  have b3 : ∫ w in s, c₃ * (|w| ^ 3 * exp (-b * w ^ 2))
      = c₃ * (exp (-b * A ^ 2) * (A ^ 2 / b + 1 / b ^ 2)) := by
    rw [integral_const_mul, integral_compl_Icc_abs_pow_three_mul_exp_neg_mul_sq hb hA.le]
  -- the two even moments lose a factor of two, and nothing more, once `1 ≤ bA²`
  have hd2 : 1 / (b ^ 2 * A) ≤ A / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    nlinarith
  have hd3 : 1 / b ^ 2 ≤ A ^ 2 / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    nlinarith
  have g2 : c₂ * (exp (-b * A ^ 2) * (A / b + 1 / (b ^ 2 * A)))
      ≤ c₂ * (exp (-b * A ^ 2) * (2 * A / b)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hE.le) h₂
    rw [show 2 * A / b = A / b + A / b by ring]
    linarith
  have g3 : c₃ * (exp (-b * A ^ 2) * (A ^ 2 / b + 1 / b ^ 2))
      ≤ c₃ * (exp (-b * A ^ 2) * (2 * A ^ 2 / b)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hE.le) h₃
    rw [show 2 * A ^ 2 / b = A ^ 2 / b + A ^ 2 / b by ring]
    linarith
  have hsum : c₀ * (exp (-b * A ^ 2) / (b * A)) + c₁ * (exp (-b * A ^ 2) / b)
      + c₂ * (exp (-b * A ^ 2) * (2 * A / b)) + c₃ * (exp (-b * A ^ 2) * (2 * A ^ 2 / b))
      = exp (-b * A ^ 2) / b * (c₀ / A + c₁ + 2 * c₂ * A + 2 * c₃ * A ^ 2) := by
    field_simp
  rw [exp_neg_mul_sq_mul_poly_eq, integral_add e012 e3, integral_add e01 e2, integral_add e0 e1]
  linarith

/-- Translating both the integrand and the region of integration, against a region that is at
least as large. -/
private theorem setIntegral_comp_add_right_le_of_nonneg {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ u : ℝ, 0 ≤ f u) {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) (d : ℝ)
    (hst : ∀ w ∈ s, w + d ∈ t) :
    ∫ w in s, f (w + d) ≤ ∫ u in t, f u := by
  have hR : ∫ w : ℝ, t.indicator f (w + d) = ∫ u : ℝ, t.indicator f u :=
    integral_add_right_eq_self (t.indicator f) d
  rw [← integral_indicator hs, ← integral_indicator ht, ← hR]
  refine integral_mono ((hf.comp_add_right d).indicator hs)
    ((hf.indicator ht).comp_add_right d) fun w ↦ ?_
  by_cases hw : w ∈ s
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hst w hw)]
  · rw [Set.indicator_of_notMem hw]
    exact Set.indicator_nonneg (fun u _ ↦ hf0 u) _

/-- **A Gaussian against a cubic in `|w|`, both centred at `-d`, outside a symmetric interval of
radius `W`**, measured at a radius `A ≤ W - |d|`. -/
theorem integral_compl_Icc_exp_neg_mul_sq_mul_poly_comp_add_right_le (hb : 0 < b) {W d A : ℝ}
    (hA : 0 < A) (hAW : A + |d| ≤ W) (hbA : 1 ≤ b * A ^ 2) {c₀ c₁ c₂ c₃ : ℝ} (h₀ : 0 ≤ c₀)
    (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃) :
    ∫ w in (Set.Icc (-W) W)ᶜ, exp (-b * (w + d) ^ 2) *
        (c₀ + c₁ * |w + d| + c₂ * (w + d) ^ 2 + c₃ * |w + d| ^ 3)
      ≤ exp (-b * A ^ 2) / b * (c₀ / A + c₁ + 2 * c₂ * A + 2 * c₃ * A ^ 2) := by
  refine le_trans (setIntegral_comp_add_right_le_of_nonneg
    (integrable_exp_neg_mul_sq_mul_poly hb c₀ c₁ c₂ c₃)
    (fun u ↦ by positivity) measurableSet_Icc.compl measurableSet_Icc.compl d fun w hw ↦ ?_)
    (integral_compl_Icc_exp_neg_mul_sq_mul_poly_le hb hA hbA h₀ h₂ h₃)
  have hwW : W < |w| := lt_abs_of_mem_compl_Icc hw
  have hshift : A < |w + d| := by
    have h := abs_sub_abs_le_abs_sub w (-d)
    rw [abs_neg, sub_neg_eq_add] at h
    linarith
  rw [Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le]
  exact hshift

/-- **A Gaussian centred at `-d`, outside a symmetric interval of radius `W`.** -/
theorem integral_compl_Icc_exp_neg_mul_sq_comp_add_right_le (hb : 0 < b) {W d A : ℝ} (hA : 0 < A)
    (hAW : A + |d| ≤ W) (hbA : 1 ≤ b * A ^ 2) :
    ∫ w in (Set.Icc (-W) W)ᶜ, exp (-b * (w + d) ^ 2) ≤ exp (-b * A ^ 2) / (b * A) := by
  have h := integral_compl_Icc_exp_neg_mul_sq_mul_poly_comp_add_right_le hb hA hAW hbA
    (c₀ := 1) (c₁ := 0) (c₂ := 0) (c₃ := 0) zero_le_one le_rfl le_rfl le_rfl
  simp only [mul_zero, zero_mul, add_zero, mul_one] at h
  calc ∫ w in (Set.Icc (-W) W)ᶜ, exp (-b * (w + d) ^ 2)
      ≤ exp (-b * A ^ 2) / b * (1 / A) := h
    _ = exp (-b * A ^ 2) / (b * A) := by ring

/-- The four monomials making up an even polynomial of degree six against a Gaussian. -/
private theorem exp_neg_mul_sq_mul_even_poly_eq (b c₀ c₂ c₄ c₆ : ℝ) :
    (fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4 + c₆ * w ^ 6))
      = fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₂ * (w ^ 2 * exp (-b * w ^ 2))
          + c₄ * (w ^ 4 * exp (-b * w ^ 2)) + c₆ * (w ^ 6 * exp (-b * w ^ 2)) := by
  funext w
  ring

/-- A Gaussian against an even polynomial of degree six is integrable. -/
theorem integrable_exp_neg_mul_sq_mul_even_poly (hb : 0 < b) (c₀ c₂ c₄ c₆ : ℝ) :
    Integrable fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4 + c₆ * w ^ 6) := by
  rw [exp_neg_mul_sq_mul_even_poly_eq]
  refine ((((integrable_exp_neg_mul_sq hb).const_mul c₀).add ?_).add ?_).add ?_
  · simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  · simpa [even_four.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 4).const_mul c₄
  · simpa [even_six.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 6).const_mul c₆

/-- A Gaussian against an even polynomial of degree six, in terms of its first four even
moments. -/
theorem integral_exp_neg_mul_sq_mul_even_poly (hb : 0 < b) (c₀ c₂ c₄ c₆ : ℝ) :
    ∫ w : ℝ, exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4 + c₆ * w ^ 6)
      = (c₀ + c₂ / (2 * b) + 3 * c₄ / (4 * b ^ 2) + 15 * c₆ / (8 * b ^ 3)) * √(π / b) := by
  have hb0 : b ≠ 0 := hb.ne'
  have e0 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) :=
    (integrable_exp_neg_mul_sq hb).const_mul c₀
  have e2 : Integrable fun w : ℝ ↦ c₂ * (w ^ 2 * exp (-b * w ^ 2)) := by
    simpa [sq_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 2).const_mul c₂
  have e4 : Integrable fun w : ℝ ↦ c₄ * (w ^ 4 * exp (-b * w ^ 2)) := by
    simpa [even_four.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 4).const_mul c₄
  have e6 : Integrable fun w : ℝ ↦ c₆ * (w ^ 6 * exp (-b * w ^ 2)) := by
    simpa [even_six.pow_abs] using (integrable_abs_pow_mul_exp_neg_mul_sq hb 6).const_mul c₆
  -- the partial sums are stated in `fun w ↦ …` form, since `Integrable.add` returns the `f + g`
  -- form, which `integral_add`'s rewrite will not match against the integrand below
  have e02 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₂ * (w ^ 2 * exp (-b * w ^ 2)) :=
    e0.add e2
  have e024 : Integrable fun w : ℝ ↦ c₀ * exp (-b * w ^ 2) + c₂ * (w ^ 2 * exp (-b * w ^ 2))
      + c₄ * (w ^ 4 * exp (-b * w ^ 2)) := e02.add e4
  rw [exp_neg_mul_sq_mul_even_poly_eq, integral_add e024 e6, integral_add e02 e4,
    integral_add e0 e2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_gaussian, integral_sq_mul_exp_neg_mul_sq hb,
    integral_pow_four_mul_exp_neg_mul_sq hb, integral_pow_six_mul_exp_neg_mul_sq hb]
  field_simp

/-- A Gaussian against an even polynomial of degree six, both centred at `-d`. -/
theorem integral_exp_neg_mul_sq_mul_even_poly_comp_add_right (hb : 0 < b) (c₀ c₂ c₄ c₆ d : ℝ) :
    ∫ w : ℝ, exp (-b * (w + d) ^ 2) *
        (c₀ + c₂ * (w + d) ^ 2 + c₄ * (w + d) ^ 4 + c₆ * (w + d) ^ 6)
      = (c₀ + c₂ / (2 * b) + 3 * c₄ / (4 * b ^ 2) + 15 * c₆ / (8 * b ^ 3)) * √(π / b) := by
  rw [show (∫ w : ℝ, exp (-b * (w + d) ^ 2) *
        (c₀ + c₂ * (w + d) ^ 2 + c₄ * (w + d) ^ 4 + c₆ * (w + d) ^ 6))
      = ∫ w : ℝ, (fun u : ℝ ↦ exp (-b * u ^ 2) *
        (c₀ + c₂ * u ^ 2 + c₄ * u ^ 4 + c₆ * u ^ 6)) (w + d) from rfl,
    integral_add_right_eq_self (fun u : ℝ ↦ exp (-b * u ^ 2) *
      (c₀ + c₂ * u ^ 2 + c₄ * u ^ 4 + c₆ * u ^ 6)) d,
    integral_exp_neg_mul_sq_mul_even_poly hb]

/-- A Gaussian against an even polynomial of degree four is integrable. -/
theorem integrable_exp_neg_mul_sq_mul_even_quartic (hb : 0 < b) (c₀ c₂ c₄ : ℝ) :
    Integrable fun w : ℝ ↦ exp (-b * w ^ 2) * (c₀ + c₂ * w ^ 2 + c₄ * w ^ 4) := by
  simpa using integrable_exp_neg_mul_sq_mul_even_poly hb c₀ c₂ c₄ 0

/-- A Gaussian against an even polynomial of degree four, both centred at `-d`. -/
theorem integral_exp_neg_mul_sq_mul_even_quartic_comp_add_right (hb : 0 < b) (c₀ c₂ c₄ d : ℝ) :
    ∫ w : ℝ, exp (-b * (w + d) ^ 2) * (c₀ + c₂ * (w + d) ^ 2 + c₄ * (w + d) ^ 4)
      = (c₀ + c₂ / (2 * b) + 3 * c₄ / (4 * b ^ 2)) * √(π / b) := by
  simpa using integral_exp_neg_mul_sq_mul_even_poly_comp_add_right hb c₀ c₂ c₄ 0 d

end Moments
