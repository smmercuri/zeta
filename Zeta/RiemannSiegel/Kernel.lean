/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecificLimits.Normed
public import Zeta.Analysis.Complex.SinExp

/-!
# The Riemann–Siegel kernel

The **Riemann–Siegel kernel** is
`G(x) = e^{iπx²} / (e^{iπx} − e^{−iπx}) = e^{iπx²} / (2i sin πx)`,
the integrand of the contour integral underlying the Riemann–Siegel formula (`riemann_siegel.tex`,
`sec:rs_kernel`). It is holomorphic off `ℤ` and has a simple pole at *every* integer with the
*same* residue `1/(2πi)`; that uniformity is what makes a contour shift across `1, …, ν` produce
the unweighted partial sum `∑_{n ≤ ν} n^{-s}`.

The quasi-periodicity `G(x + 1) − G(x) = e^{iπx(x+1)}` says the increment across one period is a
pure Gaussian.

## Main results

* `Zeta.RiemannSiegel.kernel`: the kernel `G`;
* `Zeta.RiemannSiegel.differentiableAt_kernel`: `G` is holomorphic off `ℤ`;
* `Zeta.RiemannSiegel.tendsto_sub_mul_kernel`: `G` has a simple pole of residue `1/(2πi)` at every
  integer;
* `Zeta.RiemannSiegel.kernel_neg`: `G` is odd;
* `Zeta.RiemannSiegel.kernel_eq_tsum_of_im_neg`, `Zeta.RiemannSiegel.kernel_eq_neg_tsum_of_im_pos`:
  the Gaussian expansions of `G` on the two open half-planes;
* `Zeta.RiemannSiegel.kernel_add_one`, `Zeta.RiemannSiegel.kernel_add_one_sub_kernel`: the
  quasi-periodicity of `G`.
-/
@[expose] public section


open Complex Filter Topology

open scoped Real

namespace Zeta.RiemannSiegel

/-- The **Riemann–Siegel kernel** `G(x) = e^{iπx²} / (e^{iπx} − e^{−iπx})`. -/
noncomputable def kernel (x : ℂ) : ℂ :=
  exp (π * I * x ^ 2) / (exp (π * I * x) - exp (-(π * I * x)))

/-- The Riemann–Siegel kernel in terms of the sine. -/
theorem kernel_eq_div_two_mul_I_mul_sin (x : ℂ) :
    kernel x = exp (π * I * x ^ 2) / (2 * I * sin (π * x)) := by
  rw [kernel, show ((π : ℂ) * I * x) = (π * x) * I by ring, exp_mul_I_sub_exp_neg_mul_I]

/-- **The Riemann–Siegel kernel is holomorphic off `ℤ`.** -/
theorem differentiableAt_kernel {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) : DifferentiableAt ℂ kernel x := by
  rw [funext kernel_eq_div_two_mul_I_mul_sin]
  exact DifferentiableAt.div (by fun_prop) (by fun_prop)
    (by simpa [I_ne_zero] using sin_pi_mul_ne_zero hx)

/-- **Quasi-periodicity of the Riemann–Siegel kernel.** -/
theorem kernel_add_one (x : ℂ) : kernel (x + 1) = exp (2 * π * I * x) * kernel x := by
  rw [kernel_eq_div_two_mul_I_mul_sin, kernel_eq_div_two_mul_I_mul_sin,
    show ((π : ℂ) * (x + 1)) = π * x + π by ring, sin_add_pi,
    show ((π : ℂ) * I * (x + 1) ^ 2) = 2 * π * I * x + π * I * x ^ 2 + π * I by ring,
    exp_add, exp_add, exp_pi_mul_I]
  ring

/-- **The increment of the Riemann–Siegel kernel across one period is a Gaussian.** -/
theorem kernel_add_one_sub_kernel {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) :
    kernel (x + 1) - kernel x = exp (π * I * x * (x + 1)) := by
  have hs : (2 : ℂ) * I * sin ((π : ℂ) * x) ≠ 0 := by
    simpa [I_ne_zero] using sin_pi_mul_ne_zero hx
  rw [kernel_add_one, kernel_eq_div_two_mul_I_mul_sin, ← sub_one_mul, ← mul_div_assoc,
    div_eq_iff hs, ← exp_mul_I_sub_exp_neg_mul_I, sub_mul, mul_sub, ← exp_add, ← exp_add,
    ← exp_add, show (2 * (π : ℂ) * I * x + π * I * x ^ 2) = π * I * x * (x + 1) + π * x * I by
      ring, show ((π : ℂ) * I * x * (x + 1) + -((π : ℂ) * x * I)) = π * I * x ^ 2 by ring, one_mul]

/-- **The Riemann–Siegel kernel is odd.** -/
theorem kernel_neg (x : ℂ) : kernel (-x) = -kernel x := by
  rw [kernel, kernel, neg_sq, show (π : ℂ) * I * -x = -((π : ℂ) * I * x) by ring, neg_neg,
    ← neg_sub, div_neg]

/-- **Gaussian expansion of the Riemann–Siegel kernel in the lower half-plane**, with every
coefficient the same constant `e^{-iπ/4}`. -/
theorem kernel_eq_tsum_of_im_neg {x : ℂ} (hx : x.im < 0) :
    kernel x
      = exp (-((π / 4 : ℝ) * I)) * ∑' k : ℕ, exp (π * I * (x - (2 * k + 1) / 2) ^ 2) := by
  have hq : ‖exp (-(2 * (π : ℂ) * I * x))‖ < 1 := by
    rw [Complex.norm_exp, show (-(2 * (π : ℂ) * I * x)).re = 2 * π * x.im by
      simp [Complex.mul_re, Complex.mul_im]]
    exact Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
  -- `(2k+1)² = 4k(k+1) + 1 ≡ 1 (mod 8)`, so `e^{-iπ/4}` cancels every coefficient
  have hterm (k : ℕ) : exp (-((π / 4 : ℝ) * I)) * exp ((π : ℂ) * I * (x - (2 * k + 1) / 2) ^ 2)
      = exp ((π : ℂ) * I * x ^ 2) * exp (-((π : ℂ) * I * x))
        * exp (-(2 * (π : ℂ) * I * x)) ^ k := by
    obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
    have hm' : (k : ℂ) * ((k : ℂ) + 1) = (m : ℂ) + (m : ℂ) := by exact_mod_cast hm
    rw [← Complex.exp_nat_mul, ← exp_add, ← exp_add, ← exp_add,
      show (-((π / 4 : ℝ) * I) + (π : ℂ) * I * (x - (2 * k + 1) / 2) ^ 2)
        = ((π : ℂ) * I * x ^ 2 + -((π : ℂ) * I * x) + k * -(2 * (π : ℂ) * I * x))
          + (m : ℂ) * (2 * π * I) from by push_cast; linear_combination ((π : ℂ) * I) * hm',
      exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [kernel, show exp ((π : ℂ) * I * x) - exp (-((π : ℂ) * I * x))
      = exp ((π : ℂ) * I * x) * (1 - exp (-(2 * (π : ℂ) * I * x))) from by
        rw [mul_sub, mul_one, ← exp_add]; ring_nf,
    ← tsum_mul_left, tsum_congr hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hq,
    Complex.exp_neg ((π : ℂ) * I * x), div_eq_mul_inv, mul_inv]
  ring

/-- **Gaussian expansion of the Riemann–Siegel kernel in the upper half-plane.** -/
theorem kernel_eq_neg_tsum_of_im_pos {x : ℂ} (hx : 0 < x.im) :
    kernel x
      = -(exp (-((π / 4 : ℝ) * I)) * ∑' k : ℕ, exp (π * I * (x + (2 * k + 1) / 2) ^ 2)) := by
  have h := kernel_eq_tsum_of_im_neg (x := -x) (by simpa using hx)
  rw [kernel_neg, tsum_congr fun k : ℕ ↦ congrArg Complex.exp (by ring :
    (π : ℂ) * I * (-x - (2 * (k : ℂ) + 1) / 2) ^ 2 = π * I * (x + (2 * k + 1) / 2) ^ 2)] at h
  linear_combination -h

/-- **Every integer is a simple pole of the Riemann–Siegel kernel, with residue `1/(2πi)`.** -/
theorem tendsto_sub_mul_kernel (n : ℤ) :
    Tendsto (fun x ↦ (x - n) * kernel x) (𝓝[≠] (n : ℂ)) (𝓝 (1 / (2 * π * I))) := by
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hsin : sin ((π : ℂ) * n) = 0 := sin_eq_zero_iff.2 ⟨n, by ring⟩
  -- the Gaussian factor at the pole is `cos (π n)`, since `n² ≡ n (mod 2)`
  have hgauss : exp ((π : ℂ) * I * (n : ℂ) ^ 2) = cos ((π : ℂ) * n) := by
    obtain ⟨m, hm⟩ : Even (n ^ 2 - n) :=
      (by ring : n * (n - 1) = n ^ 2 - n) ▸ Int.even_mul_pred_self n
    have hm' : ((n : ℂ)) ^ 2 - (n : ℂ) = (m : ℂ) + (m : ℂ) := by exact_mod_cast hm
    rw [show ((π : ℂ) * I * (n : ℂ) ^ 2) = ((π : ℂ) * n) * I + (m : ℂ) * (2 * π * I) from by
      linear_combination ((π : ℂ) * I) * hm', exp_add, exp_int_mul_two_pi_mul_I m, exp_mul_I, hsin]
    ring
  have hcos : cos ((π : ℂ) * n) ≠ 0 := hgauss ▸ exp_ne_zero ((π : ℂ) * I * (n : ℂ) ^ 2)
  -- the reciprocal slope of `z ↦ sin (π z)` at `n`, whose derivative `π cos (π n)` is nonzero
  have hinv : Tendsto (fun x : ℂ ↦ (x - n) / sin (π * x)) (𝓝[≠] (n : ℂ))
      (𝓝 (cos ((π : ℂ) * n) * π)⁻¹) := by
    have hderiv : HasDerivAt (fun z : ℂ ↦ sin (π * z)) (cos ((π : ℂ) * n) * π) (n : ℂ) := by
      simpa using (HasDerivAt.const_mul (π : ℂ) (hasDerivAt_id (n : ℂ))).csin
    refine ((hasDerivAt_iff_tendsto_slope.1 hderiv).inv₀ (mul_ne_zero hcos hpi)).congr fun x ↦ ?_
    simp only [slope_def_field, hsin, sub_zero, inv_div]
  rw [show (1 : ℂ) / (2 * π * I)
      = exp ((π : ℂ) * I * (n : ℂ) ^ 2) / (2 * I) * (cos ((π : ℂ) * n) * π)⁻¹ from by
    rw [hgauss]; field_simp]
  exact ((((by fun_prop : Continuous fun x : ℂ ↦ exp ((π : ℂ) * I * x ^ 2) / (2 * I)).tendsto
    (n : ℂ)).mono_left nhdsWithin_le_nhds).mul hinv).congr fun x ↦ by
      rw [kernel_eq_div_two_mul_I_mul_sin]; ring

end Zeta.RiemannSiegel
