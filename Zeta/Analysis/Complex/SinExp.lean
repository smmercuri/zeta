/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Elementary identities for the complex sine and exponential

Facts about `Complex.sin` and `Complex.exp` that are missing from Mathlib: the exponential form
`e^{iz} − e^{−iz} = 2i sin z`, the vanishing of `sin (π ·)` exactly on `ℤ`, and the moduli of
`sin`, `cos` and of the Gaussians `z ↦ exp (π i z²)` and `z ↦ exp (2π i z²)`.
They feed the Riemann–Siegel contour bounds (`riemann_siegel.tex`).

## Main results

* `Complex.exp_mul_I_sub_exp_neg_mul_I`: `e^{iz} − e^{−iz} = 2i sin z`;
* `Complex.exp_neg_two_pi_mul_I_div_sub_eq`: the partial-fraction split
  `e^{−2πiz}/(e^{iπz} − e^{−iπz}) = 1/(e^{iπz} − e^{−iπz}) − e^{−iπz}`;
* `Complex.norm_one_add_I`: `‖1 + i‖ = √2`;
* `Complex.exp_pi_div_four_mul_I`, `Complex.exp_pi_div_four_mul_I_mul_self`,
  `Complex.exp_neg_pi_div_four_mul_I_mul_self`, `Complex.I_mul_exp_neg_pi_div_four_mul_I`,
  `Complex.exp_pi_div_four_mul_I_div_sqrt_two`: the eighth root of unity `e^{iπ/4}` in cartesian
  form, the squares `e^{iπ/4}² = i` and `e^{-iπ/4}² = -i`, the quarter-turn
  `i e^{-iπ/4} = e^{iπ/4}`, and the quotient by `√2`;
* `Complex.exp_neg_pi_div_four_mul_I_mul_re`, `Complex.exp_neg_pi_div_four_mul_I_mul_im`: the
  cartesian coordinates of the rotation `z ↦ e^{-iπ/4} z`;
* `Complex.sin_pi_mul_ne_zero`: `sin (π z) ≠ 0` for `z` off `ℤ`;
* `Complex.norm_sin_sq`, `Complex.norm_cos_sq`: `‖sin z‖² = sin(Re z)² + sinh(Im z)²` and
  `‖cos z‖² = cos(Re z)² + sinh(Im z)²`;
* `Complex.sinh_abs_im_le_norm_sin`: `sinh |Im z| ≤ ‖sin z‖`;
* `Complex.norm_exp_pi_mul_I_mul_sq`, `Complex.norm_exp_two_pi_mul_I_mul_sq`:
  `‖exp (π i z²)‖ = exp (-2π · Re z · Im z)` and `‖exp (2π i z²)‖ = exp (-4π · Re z · Im z)`.
-/
@[expose] public section


open scoped Real

namespace Complex

/-- The exponential form of the sine: `e^{iz} − e^{−iz} = 2i sin z`. -/
theorem exp_mul_I_sub_exp_neg_mul_I (z : ℂ) : exp (z * I) - exp (-(z * I)) = 2 * I * sin z := by
  rw [show (-(z * I)) = (-z) * I by ring, exp_mul_I, exp_mul_I, cos_neg, sin_neg]
  ring

/-- **Partial fractions for the Riemann–Siegel kernel denominator.** -/
theorem exp_neg_two_pi_mul_I_div_sub_eq {z : ℂ} (hz : exp (π * I * z) ≠ exp (-(π * I * z))) :
    exp (-(2 * π * I * z)) / (exp (π * I * z) - exp (-(π * I * z)))
      = 1 / (exp (π * I * z) - exp (-(π * I * z))) - exp (-(π * I * z)) := by
  have hden : exp ((π : ℂ) * I * z) - exp (-(π * I * z)) ≠ 0 := sub_ne_zero_of_ne hz
  have key : exp (-(2 * (π : ℂ) * I * z))
      = 1 - exp (-((π : ℂ) * I * z)) * (exp ((π : ℂ) * I * z) - exp (-((π : ℂ) * I * z))) := by
    rw [mul_sub, ← exp_add, ← exp_add,
      show -((π : ℂ) * I * z) + (π : ℂ) * I * z = 0 by ring, exp_zero,
      show -((π : ℂ) * I * z) + -((π : ℂ) * I * z) = -(2 * (π : ℂ) * I * z) by ring]
    ring
  rw [key, sub_div, mul_div_assoc, div_self hden, mul_one]

/-- The eighth root of unity `e^{iπ/4}` in cartesian form. -/
theorem exp_pi_div_four_mul_I :
    exp ((π / 4 : ℝ) * I) = (Real.sqrt 2 / 2 : ℝ) + (Real.sqrt 2 / 2 : ℝ) * I := by
  rw [exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]

/-- The eighth root of unity `e^{-iπ/4}` in cartesian form. -/
theorem exp_neg_pi_div_four_mul_I :
    exp (-((π / 4 : ℝ) * I)) = (Real.sqrt 2 / 2 : ℝ) - (Real.sqrt 2 / 2 : ℝ) * I := by
  rw [show -(((π / 4 : ℝ) : ℂ) * I) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast
  ring

/-- The rotation by `π/4` and its inverse. -/
theorem exp_neg_pi_div_four_mul_I_mul_exp :
    exp (-((π / 4 : ℝ) * I)) * exp ((π / 4 : ℝ) * I) = 1 := by
  rw [← exp_add, neg_add_cancel, exp_zero]

/-- The rotation by `π/4`, followed by its inverse. -/
theorem exp_pi_div_four_mul_I_mul_exp_neg :
    exp ((π / 4 : ℝ) * I) * exp (-((π / 4 : ℝ) * I)) = 1 := by
  rw [mul_comm]
  exact exp_neg_pi_div_four_mul_I_mul_exp

/-- The rotation by `π/4`, applied twice. -/
theorem exp_pi_div_four_mul_I_mul_self :
    exp ((π / 4 : ℝ) * I) * exp ((π / 4 : ℝ) * I) = I := by
  rw [← exp_add, show ((π / 4 : ℝ) : ℂ) * I + ((π / 4 : ℝ) : ℂ) * I = (π : ℂ) / 2 * I by
    push_cast; ring, exp_pi_div_two_mul_I]

/-- The quarter-turn undoes half the rotation by `π/4`: `i e^{-iπ/4} = e^{iπ/4}`. -/
theorem I_mul_exp_neg_pi_div_four_mul_I :
    I * exp (-((π / 4 : ℝ) * I)) = exp ((π / 4 : ℝ) * I) := by
  linear_combination (-exp (-((π / 4 : ℝ) * I))) * exp_pi_div_four_mul_I_mul_self +
    exp ((π / 4 : ℝ) * I) * exp_pi_div_four_mul_I_mul_exp_neg

/-- The rotation by `-π/4`, applied twice: `e^{-iπ/4} e^{-iπ/4} = -i`. -/
theorem exp_neg_pi_div_four_mul_I_mul_self :
    exp (-((π / 4 : ℝ) * I)) * exp (-((π / 4 : ℝ) * I)) = -I := by
  rw [← exp_add, show -(((π / 4 : ℝ) : ℂ) * I) + -(((π / 4 : ℝ) : ℂ) * I) = -((π : ℂ) / 2 * I) by
    push_cast; ring, exp_neg, exp_pi_div_two_mul_I, inv_I]

/-- The modulus of `1 + i`. -/
theorem norm_one_add_I : ‖(1 + I : ℂ)‖ = Real.sqrt 2 := by
  rw [← Real.sqrt_sq (norm_nonneg ((1 : ℂ) + I)), Complex.sq_norm, Complex.normSq_apply]
  norm_num

/-- The real part of the rotation by `-π/4`. -/
theorem exp_neg_pi_div_four_mul_I_mul_re (z : ℂ) :
    (exp (-((π / 4 : ℝ) * I)) * z).re = Real.sqrt 2 / 2 * (z.re + z.im) := by
  rw [exp_neg_pi_div_four_mul_I]; simp [Complex.mul_re]; ring

/-- The imaginary part of the rotation by `-π/4`. -/
theorem exp_neg_pi_div_four_mul_I_mul_im (z : ℂ) :
    (exp (-((π / 4 : ℝ) * I)) * z).im = Real.sqrt 2 / 2 * (z.im - z.re) := by
  rw [exp_neg_pi_div_four_mul_I]; simp [Complex.mul_im]; ring

/-- The eighth root of unity `e^{iπ/4}` divided by `√2`. -/
theorem exp_pi_div_four_mul_I_div_sqrt_two :
    exp ((π / 4 : ℝ) * I) / (Real.sqrt 2 : ℂ) = (1 + I) / 2 := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
  rw [exp_pi_div_four_mul_I, div_eq_div_iff h2 two_ne_zero]
  push_cast
  ring

/-- `sin (π z)` does not vanish off the integers. -/
theorem sin_pi_mul_ne_zero {z : ℂ} (hz : ∀ n : ℤ, z ≠ n) : sin (π * z) ≠ 0 := by
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  exact sin_ne_zero_iff.2 fun k h ↦ hz k (mul_left_cancel₀ hpi (by rw [h]; ring))

/-- The modulus of the complex sine: `‖sin z‖² = sin(Re z)² + sinh(Im z)²`. -/
theorem norm_sin_sq (z : ℂ) : ‖sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have h : sin z = ((Real.sin z.re * Real.cosh z.im : ℝ) : ℂ)
      + ((Real.cos z.re * Real.sinh z.im : ℝ) : ℂ) * I := by
    rw [sin_eq]; push_cast; ring
  rw [h, Complex.sq_norm, normSq_add_mul_I, mul_pow, mul_pow, Real.cosh_sq]
  nlinarith [Real.sin_sq_add_cos_sq z.re]

/-- The complex sine is bounded below by `sinh` of the distance to the real axis. -/
theorem sinh_abs_im_le_norm_sin (z : ℂ) : Real.sinh |z.im| ≤ ‖sin z‖ := by
  have h0 : (0 : ℝ) ≤ Real.sinh |z.im| := by
    rw [Real.sinh_eq]
    have := Real.exp_le_exp.2 (neg_le_self (abs_nonneg z.im))
    linarith
  have hsq : Real.sinh |z.im| ^ 2 = Real.sinh z.im ^ 2 := by
    rcases abs_choice z.im with h | h
    · rw [h]
    · rw [h, Real.sinh_neg, neg_sq]
  nlinarith [norm_sin_sq z, sq_nonneg (Real.sin z.re), norm_nonneg (sin z)]

/-- **`sin (π z)` has modulus at least `1`** when `|Im z| ≥ √2/2`. -/
theorem one_le_norm_sin_pi_mul {z : ℂ} (hz : Real.sqrt 2 / 2 ≤ |z.im|) : 1 ≤ ‖sin (π * z)‖ := by
  have hpi := Real.pi_gt_three
  have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have him : |((π : ℂ) * z).im| = π * |z.im| := by
    rw [show ((π : ℂ) * z).im = π * z.im by simp [Complex.mul_im], abs_mul,
      abs_of_pos Real.pi_pos]
  have h1 : (1 : ℝ) ≤ |((π : ℂ) * z).im| := by
    rw [him]
    nlinarith [mul_le_mul_of_nonneg_left hz Real.pi_pos.le]
  exact (h1.trans (Real.self_le_sinh_iff.2 (abs_nonneg _))).trans (sinh_abs_im_le_norm_sin _)

/-- The modulus of the complex cosine: `‖cos z‖² = cos(Re z)² + sinh(Im z)²`. -/
theorem norm_cos_sq (z : ℂ) : ‖cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have h : cos z = ((Real.cos z.re * Real.cosh z.im : ℝ) : ℂ)
      + ((-(Real.sin z.re * Real.sinh z.im) : ℝ) : ℂ) * I := by
    rw [cos_eq]; push_cast; ring
  rw [h, Complex.sq_norm, normSq_add_mul_I, mul_pow, neg_pow, mul_pow, Real.cosh_sq]
  nlinarith [Real.sin_sq_add_cos_sq z.re]

/-- The modulus of the Gaussian `exp (π i z²)`. -/
theorem norm_exp_pi_mul_I_mul_sq (z : ℂ) :
    ‖exp (π * I * z ^ 2)‖ = Real.exp (-(2 * π * z.re * z.im)) := by
  rw [norm_exp]
  congr 1
  simp only [sq, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring

/-- The modulus of the rescaled Gaussian `exp (2π i z²)`. -/
theorem norm_exp_two_pi_mul_I_mul_sq (z : ℂ) :
    ‖exp (2 * π * I * z ^ 2)‖ = Real.exp (-(4 * π * z.re * z.im)) := by
  rw [norm_exp]
  congr 1
  simp only [sq, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
  ring

end Complex
