/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Zeta.Analysis.Complex.SinExp

/-!
# The slanted Riemann–Siegel contour

The Riemann–Siegel kernel `Zeta.RiemannSiegel.kernel` is integrated along the line of slope one
`L(a)(w) = (a + w) + i w` through a point `a` of the real axis (`riemann_siegel.tex`,
`sec:rs_contour`). Two features of that contour drive everything downstream.

*Rotation.* Multiplying by `e^{iπ/4}` turns `L(a)` into the vertical line `Re z = a/√2`. That
is what lets the contour-shift argument use axis-parallel rectangles, and what puts the
contour in a half-plane on which Mathlib's principal branch of `x ↦ x^{-s}` may be used after
rotation.

*Half-integer crossings.* When `a` is a half-integer the denominator `2 sin(πx)` of the kernel is
bounded below by `√2` all along `L(a)`, uniformly in `w`: near the real axis because `a + w` stays
within `¼` of a half-integer, and away from it because `sinh` grows.

The uniform bound `√2` is all the order-zero theory uses. The sharp first-order estimates use the
growth itself: away from the real axis the denominator is exponentially large, which makes the
outer tail negligible (`riemann_siegel.tex`, `lem:rs_sin_lower_sharp`). That bound holds for every
`a`, and is trivial at `w = 0`.

## Main results

* `Zeta.RiemannSiegel.line`: the contour `L(a)`;
* `Zeta.RiemannSiegel.line_ne_zero`: `L(a)` misses the origin for `a ≠ 0`;
* `Zeta.RiemannSiegel.line_zero`: `L(0)(w) = √2 w e^{iπ/4}`, the two Hankel rays;
* `Zeta.RiemannSiegel.continuous_line`: `L(a)` is continuous;
* `Zeta.RiemannSiegel.re_exp_pi_div_four_mul_I_mul_line`,
  `Zeta.RiemannSiegel.re_exp_pi_div_four_mul_I_mul_ofReal`: `Re (e^{iπ/4} L(a)(w)) = a/√2`;
* `Zeta.RiemannSiegel.norm_line_ge`, `Zeta.RiemannSiegel.norm_line_le`:
  `a/√2 ≤ |L(a)(w)| ≤ a + 2|w|`;
* `Zeta.RiemannSiegel.norm_line_sub_ofReal_le`: `|L(a)(w) − p| ≤ |a − p| + √2 |w|` for real `p`;
* `Zeta.RiemannSiegel.norm_line_sub_ofReal_sq`, `Zeta.RiemannSiegel.norm_line_sub_ofReal_le'`,
  `Zeta.RiemannSiegel.norm_line_sub_ofReal_ge`: the same distance in terms of the centred
  parameter `w + (a − p)/2`, exactly and as two-sided bounds;
* `Zeta.RiemannSiegel.sinh_le_norm_sin_pi_mul_line`,
  `Zeta.RiemannSiegel.abs_sin_le_norm_sin_pi_mul_line`: the two coordinatewise lower bounds
  `|sin (π L(a)(w))| ≥ sinh (π|w|)` and `≥ |sin (π (a + w))|`, for arbitrary `a`;
* `Zeta.RiemannSiegel.norm_sin_pi_mul_line_ge`, `Zeta.RiemannSiegel.sin_pi_mul_line_ne_zero`:
  `|sin (π L(a)(w))| ≥ √2/2`, and in particular `sin (π L(a)(w)) ≠ 0`, for `a` a half-integer;
* `Zeta.RiemannSiegel.norm_sin_pi_mul_line_ge_min`: `|sin (π L(a)(w))| ≥ min (½, |L(a)(w)|)` for
  `0 ≤ a ≤ ½`, a bound that survives the degeneration `a → 0`;
* `Zeta.RiemannSiegel.mul_exp_le_norm_sin_pi_mul_line`: the exponential lower bound
  `|sin (π L(a)(w))| ≥ (99/200) e^{π|w|}` for `|w| ≥ 1`, for arbitrary `a`.
-/
@[expose] public section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/-- The slanted Riemann–Siegel contour `L(a)(w) = (a + w) + i w`: the line of slope one
through `a`, traversed in the direction `1 + i`. -/
noncomputable def line (a w : ℝ) : ℂ := (a + w : ℝ) + (w : ℝ) * I

@[simp]
theorem line_re (a w : ℝ) : (line a w).re = a + w := by simp [line]

@[simp]
theorem line_im (a w : ℝ) : (line a w).im = w := by simp [line]

/-- The slanted contour misses the origin when `a ≠ 0`. -/
theorem line_ne_zero {a : ℝ} (ha : a ≠ 0) (w : ℝ) : line a w ≠ 0 := by
  simp only [ne_eq, Complex.ext_iff, line_re, line_im, Complex.zero_re, Complex.zero_im, not_and]
  exact fun h hw ↦ ha (by rw [hw] at h; linarith)

/-- Translating the slanted contour by one shifts its parameter by one. -/
theorem line_add_one (a w : ℝ) : line (a + 1) w = line a w + 1 := by
  rw [line, line]; push_cast; ring

@[fun_prop]
theorem continuous_line (a : ℝ) : Continuous (line a) := by
  unfold line; fun_prop

/-- Rotating the slanted contour by `e^{iπ/4}` gives a vertical line. -/
theorem exp_pi_div_four_mul_I_mul_line (a w : ℝ) :
    exp ((π / 4 : ℝ) * I) * line a w
      = (Real.sqrt 2 / 2 : ℝ) * ((a : ℂ) + ((a : ℂ) + 2 * w) * I) := by
  rw [exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four, line]
  push_cast
  linear_combination (Real.sqrt 2 : ℂ) * (w : ℂ) * (1 / 2) * Complex.I_sq

/-- The contour through the origin is the diagonal ray, `L(0)(w) = √2 w e^{iπ/4}`. -/
theorem line_zero (w : ℝ) : line 0 w = ((Real.sqrt 2 * w : ℝ) : ℂ) * exp ((π / 4 : ℝ) * I) := by
  refine mul_left_cancel₀ (exp_ne_zero (((π / 4 : ℝ) : ℂ) * I)) ?_
  rw [exp_pi_div_four_mul_I_mul_line, ← mul_assoc,
    mul_comm (exp (((π / 4 : ℝ) : ℂ) * I)) (((Real.sqrt 2 * w : ℝ) : ℂ)), mul_assoc,
    Complex.exp_pi_div_four_mul_I_mul_self]
  push_cast; ring

/-- The rotated contour is vertical, its abscissa independent of `w`. -/
theorem re_exp_pi_div_four_mul_I_mul_line (a w : ℝ) :
    (exp ((π / 4 : ℝ) * I) * line a w).re = a / Real.sqrt 2 := by
  rw [exp_pi_div_four_mul_I_mul_line, Complex.re_ofReal_mul,
    show ((a : ℂ) + ((a : ℂ) + 2 * w) * I).re = a by simp,
    eq_div_iff (by positivity : Real.sqrt 2 ≠ 0)]
  linear_combination (a / 2) * Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- The abscissa of a rotated real point. -/
theorem re_exp_pi_div_four_mul_I_mul_ofReal (r : ℝ) :
    (exp ((π / 4 : ℝ) * I) * (r : ℂ)).re = r / Real.sqrt 2 := by
  simpa [line] using re_exp_pi_div_four_mul_I_mul_line r 0

/-- The square of the modulus along the slanted contour. -/
theorem norm_line_sq (a w : ℝ) : ‖line a w‖ ^ 2 = (a ^ 2 + (a + 2 * w) ^ 2) / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, line_re, line_im]
  ring

/-- The slanted contour stays at distance at least `a/√2` from the origin. -/
theorem norm_line_ge (a w : ℝ) : a / Real.sqrt 2 ≤ ‖line a w‖ :=
  le_of_sq_le_sq (by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), norm_line_sq]
    nlinarith [sq_nonneg (a + 2 * w)]) (norm_nonneg _)

/-- The slanted contour stays at distance at most `a + 2|w|` from the origin. -/
theorem norm_line_le {a : ℝ} (ha0 : 0 ≤ a) (w : ℝ) : ‖line a w‖ ≤ a + 2 * |w| := by
  nlinarith [norm_line_sq a w, norm_nonneg (line a w), sq_abs w, le_abs_self w, abs_nonneg w,
    mul_nonneg ha0 (abs_nonneg w)]

/-- The logarithm of the modulus grows at most linearly along the slanted contour. -/
theorem abs_log_norm_line_le {a : ℝ} (ha0 : 0 < a) (w : ℝ) :
    |Real.log ‖line a w‖| ≤ |Real.log (a / Real.sqrt 2)| + a + 2 * |w| := by
  have hup : Real.log ‖line a w‖ ≤ a + 2 * |w| :=
    (Real.log_le_sub_one_of_pos (norm_pos_iff.2 (line_ne_zero ha0.ne' w))).trans
      (by linarith [norm_line_le ha0.le w])
  have hlow : Real.log (a / Real.sqrt 2) ≤ Real.log ‖line a w‖ :=
    Real.log_le_log (by positivity) (norm_line_ge a w)
  exact abs_le.2 ⟨by linarith [abs_nonneg w, neg_abs_le (Real.log (a / Real.sqrt 2))],
    by linarith [abs_nonneg (Real.log (a / Real.sqrt 2))]⟩

/-- The distance from a real point to the slanted contour grows at most linearly: the point
`L(a)(w)` lies within `√2 |w|` of the base point `a` of the contour. -/
theorem norm_line_sub_ofReal_le (a w p : ℝ) :
    ‖line a w - (p : ℂ)‖ ≤ |a - p| + Real.sqrt 2 * |w| := by
  rw [show line a w - (p : ℂ) = ((a - p : ℝ) : ℂ) + (w : ℂ) * (1 + I) by
    rw [line]; push_cast; ring]
  refine (norm_add_le _ _).trans_eq ?_
  rw [Complex.norm_real, norm_mul, Complex.norm_real, norm_one_add_I, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_comm]

/-- The square of the distance from a real point to the slanted contour, with the square
completed. -/
theorem norm_line_sub_ofReal_sq (a w p : ℝ) :
    ‖line a w - (p : ℂ)‖ ^ 2 = 2 * (w + (a - p) / 2) ^ 2 + (a - p) ^ 2 / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, line_re, line_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The distance from a real point to the slanted contour, in terms of the centred parameter
`w + (a − p)/2`. -/
theorem norm_line_sub_ofReal_le' (a w p : ℝ) :
    ‖line a w - (p : ℂ)‖ ≤ Real.sqrt 2 * (|w + (a - p) / 2| + |a - p| / 2) := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [norm_line_sub_ofReal_sq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [sq_abs (w + (a - p) / 2), sq_abs (a - p), abs_nonneg (w + (a - p) / 2),
    abs_nonneg (a - p)]

/-- The slanted contour stays at distance at least `|a − p|/√2` from a real point `p`. -/
theorem norm_line_sub_ofReal_ge (a w p : ℝ) :
    Real.sqrt 2 / 2 * |a - p| ≤ ‖line a w - (p : ℂ)‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [norm_line_sub_ofReal_sq, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [sq_abs (a - p), sq_nonneg (w + (a - p) / 2)]

/-- Exponential lower bound for the kernel denominator (`riemann_siegel.tex`,
`lem:rs_sin_lower_sharp`): along every line of slope one the denominator dominates
`sinh (π|w|)`. -/
theorem sinh_le_norm_sin_pi_mul_line (a w : ℝ) :
    Real.sinh (π * |w|) ≤ ‖sin (π * line a w)‖ := by
  simpa [Complex.mul_im, abs_mul, abs_of_pos Real.pi_pos] using
    Complex.sinh_abs_im_le_norm_sin ((π : ℂ) * line a w)

/-- The real sine at the abscissa is a lower bound for the kernel denominator. -/
theorem abs_sin_le_norm_sin_pi_mul_line (a w : ℝ) :
    |Real.sin (π * (a + w))| ≤ ‖sin (π * line a w)‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [sq_abs, Complex.norm_sin_sq,
    show ((π : ℂ) * line a w).re = π * (a + w) by simp [Complex.mul_re]]
  linarith [sq_nonneg (Real.sinh ((π : ℂ) * line a w).im)]

/-- Uniform lower bound for the kernel denominator along a half-integer contour, equivalently
`|e^{iπx} − e^{−iπx}| ≥ √2` along `L(a)`. -/
theorem norm_sin_pi_mul_line_ge {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) (w : ℝ) :
    Real.sqrt 2 / 2 ≤ ‖sin (π * line a w)‖ := by
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  rcases le_or_gt (1 / 4 : ℝ) |w| with hw | hw
  · -- far from the real axis: `π |w| ≥ 3/4` already exceeds `√2/2`
    refine le_trans ?_ ((Real.self_le_sinh_iff.2 (by positivity)).trans
      (sinh_le_norm_sin_pi_mul_line a w))
    nlinarith [Real.pi_gt_three]
  -- near the real axis: `a + w` lies within `¼` of the half-integer `a`
  refine le_trans ?_ (abs_sin_le_norm_sin_pi_mul_line a w)
  have hsin : Real.sin (π * (a + w)) = (-1 : ℝ) ^ n * Real.cos (π * w) := by
    rw [ha, show π * ((n : ℝ) + 1 / 2 + w) = π * w + π / 2 + n * π by ring,
      Real.sin_add_int_mul_pi, Real.sin_add_pi_div_two]
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos (π * w) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (π * w))
      (by linarith [Real.pi_pos] : π / 4 ≤ π)
      (by rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos])
    rwa [Real.cos_pi_div_four, Real.cos_abs] at h
  rw [hsin, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  exact hcos.trans (le_abs_self _)

/-- The kernel denominator is nonzero along a half-integer contour. -/
theorem sin_pi_mul_line_ne_zero {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) (w : ℝ) :
    sin (π * line a w) ≠ 0 :=
  norm_pos_iff.1 <| lt_of_lt_of_le (by positivity) (norm_sin_pi_mul_line_ge ha w)

/-- Lower bound for the kernel denominator along a contour crossing the real axis inside
`[0, ½]`. -/
theorem norm_sin_pi_mul_line_ge_min {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (w : ℝ) :
    min (1 / 2) ‖line a w‖ ≤ ‖sin (π * line a w)‖ := by
  have hpi3 := Real.pi_gt_three
  -- the real sine at the abscissa is one lower bound, `sinh` of the ordinate the other
  have hsin := abs_sin_le_norm_sin_pi_mul_line a w
  have hsinh : π * |w| ≤ ‖sin (π * line a w)‖ :=
    (Real.self_le_sinh_iff.2 (by positivity)).trans (sinh_le_norm_sin_pi_mul_line a w)
  rcases le_or_gt (1 / 4 : ℝ) |w| with hw | hw
  · -- far from the real axis the `sinh` bound alone exceeds `½`
    exact (min_le_left _ _).trans (by nlinarith)
  obtain ⟨hw1, hw2⟩ := abs_lt.1 hw
  rcases le_or_gt |a + w| (1 / 2 : ℝ) with hu | hu
  · -- near the origin: Jordan's inequality against `Re`, and `sinh` against `Im`
    have hj : 2 * |a + w| ≤ ‖sin (π * line a w)‖ := by
      have h := Real.mul_abs_le_abs_sin (x := π * (a + w))
        (by rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith)
      rw [abs_mul, abs_of_pos Real.pi_pos, ← mul_assoc, div_mul_cancel₀ _ Real.pi_ne_zero] at h
      exact h.trans hsin
    refine (min_le_right _ _).trans ((Complex.norm_le_abs_re_add_abs_im _).trans ?_)
    rw [line_re, line_im]
    nlinarith [abs_nonneg w, norm_nonneg (sin (π * line a w))]
  · -- just past the half-integer `½`, where the sine is still at least `½`
    refine (min_le_left _ _).trans (le_trans ?_ ((le_abs_self _).trans hsin))
    have hu' : 1 / 2 < a + w := by rcases abs_cases (a + w) with h | h <;> linarith [h.1]
    have ht : π * (a + w) - π / 2 < 1 := by
      nlinarith [Real.pi_lt_four, mul_lt_mul_of_pos_left
        (show a + w - 1 / 2 < 1 / 4 by linarith) Real.pi_pos]
    rw [← Real.cos_sub_pi_div_two]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := π * (a + w) - π / 2),
      mul_pos Real.pi_pos (show (0 : ℝ) < a + w - 1 / 2 by linarith)]

/-- A constant below the `n`-th power of `2.718` is below `e^x` as soon as `n ≤ x`. -/
theorem le_exp_of_le_pow {n : ℕ} {c x : ℝ} (hc : c ≤ 2.718 ^ n) (hx : (n : ℝ) ≤ x) :
    c ≤ Real.exp x :=
  hc.trans (((pow_le_pow_left₀ (by norm_num)
    (by linarith [Real.exp_one_gt_d9] : (2.718 : ℝ) ≤ Real.exp 1) n).trans_eq
      (Real.exp_one_pow n)).trans (Real.exp_le_exp.2 hx))

/-- The Gaussian factor at a threshold: a constant `c ≤ 2.718ⁿ` is swallowed by `e^{-x}` as
soon as `n ≤ x`. -/
theorem exp_neg_mul_le_one {n : ℕ} {c x : ℝ} (hc : c ≤ 2.718 ^ n) (hx : (n : ℝ) ≤ x) :
    Real.exp (-x) * c ≤ 1 := by
  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
  linarith [le_exp_of_le_pow hc hx]

/-- The kernel denominator is exponentially large away from the real axis
(`riemann_siegel.tex`, `lem:rs_sin_lower_sharp`). -/
theorem mul_exp_le_norm_sin_pi_mul_line (a : ℝ) {w : ℝ} (hw : 1 ≤ |w|) :
    99 / 200 * Real.exp (π * |w|) ≤ ‖sin (π * line a w)‖ := by
  refine le_trans ?_ (sinh_le_norm_sin_pi_mul_line a w)
  -- the constant `99/200` is `(1 - e^{-2π})/2`, so what has to be checked is `e^{2π|w|} ≥ 100`
  have h100 : (100 : ℝ) ≤ Real.exp (π * |w|) * Real.exp (π * |w|) := by
    rw [← Real.exp_add]
    exact le_exp_of_le_pow (n := 6) (by norm_num) (by push_cast; nlinarith [Real.pi_gt_three])
  rw [Real.sinh_eq, Real.exp_neg]
  nlinarith [Real.exp_pos (π * |w|), mul_inv_cancel₀ (Real.exp_ne_zero (π * |w|))]

end Zeta.RiemannSiegel
