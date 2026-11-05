/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannSiegel.Model
public import Zeta.RiemannSiegel.Shift

/-!
# The unit shift for the Riemann–Siegel model integral

The second of the two functional equations that pin the model integral `M(p)` of
`Zeta.RiemannSiegel.modelIntegral` algebraically is the **unit shift**

`M(p) + M(p + 1) = e^{2πip²}`

(`riemann_siegel_first.tex`, `lem:rsf_unit_shift`). It is the only contour deformation of the
first-order chapter: moving the contour from `L(1/2)` out to `L(3/2)` crosses the single pole
`v = 1` of the kernel denominator, and the translation `v ↦ v + 1` carries the far contour back onto
the near one at the cost of a sign and a unit shift in `p`
(`Zeta.RiemannSiegel.modelFun_add_one`).

The rectangle apparatus is not redone here: it is the general
`Zeta.RiemannSiegel.slantIntegral_sub_slantIntegral_of_pole` of `Shift.lean`, whose hypotheses are
supplied by the Gaussian bound on the horizontal sides and by the residue at the pole. Both are
easier than their order-zero analogues, because the model integrand carries no branch of a power:
it is holomorphic off `ℤ` outright, and its modulus is a bare Gaussian.

## Main results

* `Zeta.RiemannSiegel.rotatedModelFun`: the model integrand in the rotated coordinate of
  `Shift.lean`;
* `Zeta.RiemannSiegel.tendsto_sub_mul_rotatedModelFun`: its simple poles and their residues;
* `Zeta.RiemannSiegel.tendsto_HIntegral_rotatedModelFun`: the horizontal sides vanish;
* `Zeta.RiemannSiegel.modelIntegral_add_modelIntegral_add_one`: the unit shift.
-/
@[expose] public section


open Complex Filter MeasureTheory Topology

open scoped Real

namespace Zeta.RiemannSiegel

/-- The **model integrand in rotated coordinates**, `F(z) = e^{-iπ/4} m_p(e^{-iπ/4} z)`. -/
noncomputable def rotatedModelFun (p : ℂ) : ℂ → ℂ := rotatedFun (modelFun p)

/-- **The rotated model integrand, evaluated at a rotated point.** -/
theorem rotatedModelFun_exp_mul (p x : ℂ) :
    rotatedModelFun p (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * modelFun p x :=
  rotatedFun_exp_mul _ _

/-- **The model integrand is holomorphic off the integers.** -/
theorem differentiableAt_modelFun (p : ℂ) {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) :
    DifferentiableAt ℂ (modelFun p) x := by
  rw [funext (modelFun_eq_mul_kernel p)]
  exact (by fun_prop : DifferentiableAt ℂ
    (fun x : ℂ ↦ exp (2 * π * I * (x - p) ^ 2 - π * I * x ^ 2)) x).mul (differentiableAt_kernel hx)

/-- **The rotated model integrand is holomorphic off the rotated integers.** -/
theorem differentiableAt_rotatedModelFun (p : ℂ) {z : ℂ}
    (hz : ∀ k : ℤ, z ≠ exp ((π / 4 : ℝ) * I) * k) : DifferentiableAt ℂ (rotatedModelFun p) z :=
  differentiableAt_rotatedFun (differentiableAt_modelFun p fun k hcon ↦ hz k (by
    rw [← hcon, ← mul_assoc, exp_pi_div_four_mul_I_mul_exp_neg, one_mul]))

/-- **Every integer is a simple pole of the model integrand**, with residue
`e^{2πi(n − p)² − iπn²}/(2πi)`. -/
theorem tendsto_sub_mul_modelFun (p : ℂ) (n : ℤ) :
    Tendsto (fun x ↦ (x - n) * modelFun p x) (𝓝[≠] (n : ℂ))
      (𝓝 (exp (2 * π * I * ((n : ℂ) - p) ^ 2 - π * I * (n : ℂ) ^ 2) / (2 * π * I))) := by
  have hcont : Tendsto (fun x : ℂ ↦ exp (2 * π * I * (x - p) ^ 2 - π * I * x ^ 2))
      (𝓝[≠] (n : ℂ)) (𝓝 (exp (2 * π * I * ((n : ℂ) - p) ^ 2 - π * I * (n : ℂ) ^ 2))) :=
    ((by fun_prop : Continuous fun x : ℂ ↦
      exp (2 * π * I * (x - p) ^ 2 - π * I * x ^ 2)).tendsto _).mono_left nhdsWithin_le_nhds
  rw [div_eq_mul_one_div]
  refine Tendsto.congr (fun x ↦ ?_) (hcont.mul (tendsto_sub_mul_kernel n))
  rw [modelFun_eq_mul_kernel]
  ring

/-- **Every rotated integer is a simple pole of the rotated model integrand.** -/
theorem tendsto_sub_mul_rotatedModelFun (p : ℂ) (n : ℤ) :
    Tendsto (fun z ↦ (z - exp ((π / 4 : ℝ) * I) * n) * rotatedModelFun p z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * (n : ℂ)))
      (𝓝 (exp (2 * π * I * ((n : ℂ) - p) ^ 2 - π * I * (n : ℂ) ^ 2) / (2 * π * I))) :=
  tendsto_sub_mul_rotatedFun (tendsto_sub_mul_modelFun p n)

/-- **A Gaussian bound for the rotated model integrand** on a horizontal segment far from the
diagonal. -/
private theorem norm_rotatedModelFun_le (p : ℂ) {ξ y : ℝ} (h : 1 ≤ |y - ξ|) :
    ‖rotatedModelFun p ((ξ : ℂ) + (y : ℂ) * I)‖
      ≤ Real.exp (2 * π * ξ ^ 2 - 2 * π * y ^ 2
        + 2 * Real.sqrt 2 * π * (|ξ| + |y|) * (|p.re| + |p.im|) + 4 * π * |p.re| * |p.im|) := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set x : ℂ := exp (-((π / 4 : ℝ) * I)) * ((ξ : ℂ) + (y : ℂ) * I) with hxdef
  have hxre : x.re = Real.sqrt 2 / 2 * (ξ + y) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_re]; simp
  have hxim : x.im = Real.sqrt 2 / 2 * (y - ξ) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_im]; simp
  have hxim2 := le_abs_im_of_im_eq_mul (by positivity) hxim h
  have hnorm : ‖rotatedModelFun p ((ξ : ℂ) + (y : ℂ) * I)‖ = ‖modelFun p x‖ := by
    rw [rotatedModelFun, norm_rotatedFun, ← hxdef]
  -- the Gaussian numerator, the denominator being at least `2` in modulus
  have hbound : ‖modelFun p x‖ ≤ Real.exp (-(4 * π * (x.re - p.re) * (x.im - p.im))) := by
    refine (norm_modelFun_le p one_pos (Complex.one_le_norm_sin_pi_mul hxim2)).trans ?_
    rw [Complex.norm_exp_two_pi_mul_I_mul_sq, Complex.sub_re, Complex.sub_im]
    exact div_le_self (Real.exp_pos _).le (by norm_num)
  -- the exponent, in which the cross terms are the only inexact step
  have hid : -(4 * π * (Real.sqrt 2 / 2 * (ξ + y) - p.re) * (Real.sqrt 2 / 2 * (y - ξ) - p.im))
      = 2 * π * ξ ^ 2 - 2 * π * y ^ 2
        + 2 * Real.sqrt 2 * π * ((ξ + y) * p.im + (y - ξ) * p.re) - 4 * π * (p.re * p.im) := by
    linear_combination (-(π * (y ^ 2 - ξ ^ 2))) * hs2
  have hA : (ξ + y) * p.im + (y - ξ) * p.re ≤ (|ξ| + |y|) * (|p.re| + |p.im|) := by
    have h1 : (ξ + y) * p.im ≤ (|ξ| + |y|) * |p.im| :=
      (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact abs_add_le ξ y)
    have h2 : (y - ξ) * p.re ≤ (|ξ| + |y|) * |p.re| :=
      (le_abs_self _).trans (by
        rw [abs_mul]; gcongr; simpa [sub_eq_add_neg, add_comm] using abs_add_le y (-ξ))
    nlinarith [abs_nonneg p.re, abs_nonneg p.im, abs_nonneg ξ, abs_nonneg y]
  have hB : -(p.re * p.im) ≤ |p.re| * |p.im| := by
    rw [← abs_mul]
    exact neg_le_abs _
  rw [hnorm]
  refine hbound.trans (Real.exp_le_exp.2 ?_)
  rw [hxre, hxim, hid]
  nlinarith [mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 2 * π),
    mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 4 * π)]

/-- **The horizontal sides of the truncated rectangle vanish** for the rotated model integrand. -/
theorem tendsto_HIntegral_rotatedModelFun (p : ℂ) {β α : ℝ} (hβ : 0 ≤ β) (hβα : β ≤ α)
    {y : ℝ → ℝ} (hy : Tendsto (fun H ↦ |y H|) atTop atTop) :
    Tendsto (fun H ↦ HIntegral (rotatedModelFun p) β α (y H)) atTop (𝓝 0) := by
  have hK : (0 : ℝ) ≤ |p.re| + |p.im| := by positivity
  refine tendsto_HIntegral_of_norm_le
    (C₀ := 2 * π * α ^ 2 + 2 * Real.sqrt 2 * π * (α * (|p.re| + |p.im|)) + 4 * π * |p.re| * |p.im|)
    (C₁ := 2 * Real.sqrt 2 * π * (|p.re| + |p.im|)) (c := 2 * π) (T := α + 1) hβα (by positivity)
    (fun ξ u hξ1 hξ2 hu ↦ ?_) hy
  have hξ0 : 0 ≤ ξ := hβ.trans hξ1
  have h1 : 1 ≤ |u - ξ| := by
    linarith [abs_sub_abs_le_abs_sub u ξ, abs_of_nonneg hξ0]
  refine (norm_rotatedModelFun_le p h1).trans (Real.exp_le_exp.2 ?_)
  have hsq : ξ ^ 2 ≤ α ^ 2 := by nlinarith
  have hstep : 2 * Real.sqrt 2 * π * (ξ * (|p.re| + |p.im|))
      ≤ 2 * Real.sqrt 2 * π * (α * (|p.re| + |p.im|)) := by
    have h := mul_le_mul_of_nonneg_right hξ2 hK
    exact mul_le_mul_of_nonneg_left h (by positivity)
  rw [abs_of_nonneg hξ0]
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * π)]

/-- **The unit shift for the model integral** (`riemann_siegel_first.tex`, `lem:rsf_unit_shift`):
`M(p) + M(p + 1) = e^{2πip²}`. -/
theorem modelIntegral_add_modelIntegral_add_one (p : ℂ) :
    modelIntegral p (1 / 2) + modelIntegral (p + 1) (1 / 2) = exp (2 * π * I * p ^ 2) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hpi' : exp (-((π : ℂ) * I)) = -1 := by rw [exp_neg, exp_pi_mul_I]; norm_num
  -- moving the contour from `L(1/2)` to `L(3/2)` crosses the single pole `v = 1`
  have hcross : ∀ q : ℂ, modelIntegral q (3 / 2) - modelIntegral q (1 / 2)
      = -exp (2 * π * I * (1 - q) ^ 2) := by
    intro q
    have hβ : (0 : ℝ) ≤ (((1 : ℤ) : ℝ) - 1 / 2) / Real.sqrt 2 := by push_cast; positivity
    have hβα : (((1 : ℤ) : ℝ) - 1 / 2) / Real.sqrt 2 ≤ (((1 : ℤ) : ℝ) + 1 / 2) / Real.sqrt 2 := by
      rw [div_le_div_iff_of_pos_right hs2]; push_cast; linarith
    have hkey := slantIntegral_sub_slantIntegral_of_pole (f := modelFun q)
      (F := rotatedModelFun q) (n := 1) one_pos (rotatedModelFun_exp_mul q)
      (fun z _ hz ↦ differentiableAt_rotatedModelFun q hz)
      (tendsto_sub_mul_rotatedModelFun q 1)
      (tendsto_HIntegral_rotatedModelFun q hβ hβα (by simpa using tendsto_abs_atTop_atTop))
      (tendsto_HIntegral_rotatedModelFun q hβ hβα tendsto_abs_atTop_atTop)
      (integrable_modelIntegrand q (a := ((1 : ℤ) : ℝ) + 1 / 2) (n := 1) rfl)
      (integrable_modelIntegrand q (a := ((1 : ℤ) : ℝ) - 1 / 2) (n := 0) (by push_cast; ring))
    push_cast at hkey
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hkey
    rw [modelIntegral_eq_slantIntegral, modelIntegral_eq_slantIntegral, hkey,
      show 2 * (π : ℂ) * I * (1 - q) ^ 2 - π * I * 1 ^ 2
        = 2 * π * I * (1 - q) ^ 2 + -(π * I) by ring, exp_add, hpi']
    field_simp
  -- translating the contour by one reverses the sign and shifts `p`
  have htrans : ∀ q : ℂ, modelIntegral q (3 / 2) = -modelIntegral (q - 1) (1 / 2) := by
    intro q
    have hpt : ∀ w : ℝ, modelIntegrand q (3 / 2) w = -modelIntegrand (q - 1) (1 / 2) w := by
      intro w
      rw [modelIntegrand, modelIntegrand, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, line_add_one,
        modelFun_add_one]
    rw [modelIntegral, modelIntegral]
    simp only [hpt]
    rw [integral_neg]
    ring
  have h := hcross (p + 1)
  rw [htrans (p + 1), show p + 1 - 1 = p by ring] at h
  rw [show (2 : ℂ) * π * I * p ^ 2 = 2 * π * I * (1 - (p + 1)) ^ 2 by ring]
  linear_combination -h

end Zeta.RiemannSiegel
