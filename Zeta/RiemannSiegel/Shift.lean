/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import PrimeNumberTheoremAnd.ZetaBounds
public import Zeta.RiemannSiegel.Integral

/-!
# The Riemann–Siegel contour shift

Moving the slanted contour `Zeta.RiemannSiegel.line` from one half-integer crossing point to a
larger one sweeps across the integers in between, and each of them contributes its residue: the
difference of the two contour integrals is the partial sum `∑ n^{-s}` (`riemann_siegel.tex`,
`sec:rs_shift`).

The argument is carried out in the rotated coordinate `z = e^{iπ/4} x`, in which the slanted lines
become the *vertical* lines `Re z = a/√2` and the contour becomes an honest axis-parallel
rectangle; that is what lets it reuse `PrimeNumberTheoremAnd`'s rectangle residue calculus rather
than developing parallelogram contours. It suffices to cross one integer at a time, and three
inputs then feed the single-pole rectangle theorem `ResidueTheoremOnRectangleWithSimplePole'`:

* the integrand is holomorphic on the closed rectangle minus the pole — the branch
  `Zeta.RiemannSiegel.slantCpow` because the rectangle lies in the rotated right half-plane, and
  the kernel `Zeta.RiemannSiegel.kernel` because the only integer in a slanted strip of width one
  is the one being crossed;
* the pole is simple, with residue `n^{-s}/(2πi)`;
* the horizontal sides vanish as the truncation height `H` grows: there the Gaussian factor
  `e^{iπx²}` contributes `e^{-π(H² − ξ²)}`, while the power and the reciprocal of the kernel's
  denominator grow at most exponentially in `H`.

The vertical sides are affine reparametrisations of truncations of the contour integral, so they
converge to `I(s, a)` and `I(s, b)` by `Zeta.RiemannSiegel.integrable_contourIntegrand` and
dominated convergence.

The rectangle apparatus is developed for an arbitrary integrand
(`Zeta.RiemannSiegel.slantIntegral_sub_slantIntegral_of_pole`, and the three lemmas feeding it),
because the first-order chapter deforms the contour of the *model* integrand
`Zeta.RiemannSiegel.modelFun` across the same kind of strip; the Riemann–Siegel results below are
its corollaries. Two of those lemmas — `Zeta.RiemannSiegel.tendsto_HIntegral_of_norm_le` and
`Zeta.RiemannSiegel.tendsto_RectangleIntegral_of_tendsto` — mention no Riemann–Siegel object at all,
and live here only because `PrimeNumberTheoremAnd`'s `HIntegral` and `RectangleIntegral` are
declared in the root namespace of a package this project does not own.

## Main results

* `Zeta.RiemannSiegel.rotatedFun`: the rotation `f ↦ e^{-iπ/4} f(e^{-iπ/4} ·)`, together with its
  evaluation, modulus, holomorphy and residues;
* `Zeta.RiemannSiegel.rotatedIntegrand`: the integrand in the rotated coordinate;
* `Zeta.RiemannSiegel.tendsto_sub_mul_rotatedIntegrand`: its simple poles and their residues;
* `Zeta.RiemannSiegel.norm_integrand_le`: a Gaussian bound for the integrand off the real axis;
* `Zeta.RiemannSiegel.tendsto_HIntegral_rotatedIntegrand`,
  `Zeta.RiemannSiegel.tendsto_VIntegral_rotatedIntegrand`: the four sides of the rectangle in the
  limit `H → ∞`;
* `Zeta.RiemannSiegel.tendsto_RectangleIntegral_rotatedIntegrand`: the four together, converging to
  the difference of the two contour integrals;
* `Zeta.RiemannSiegel.slantIntegral_sub_slantIntegral_of_pole`: the one-step shift for an arbitrary
  integrand;
* `Zeta.RiemannSiegel.contourIntegral_sub_contourIntegral_eq_sum_cpow_neg`: the contour-shift
  identity `I(s, k + ½) − I(s, j + ½) = ∑_{j < n ≤ k} n^{-s}`;
* `Zeta.RiemannSiegel.sum_cpow_neg_eq_contourIntegral_sub_contourIntegral`: its corollary
  `∑_{n = 1}^{k} n^{-s} = I(s, k + ½) − I(s, ½)`.
-/
@[expose] public section


open Asymptotics Complex Filter MeasureTheory Topology

open scoped Real

namespace Zeta.RiemannSiegel

/-- The rotation by `-π/4` has modulus one. -/
theorem norm_exp_neg_pi_div_four_mul_I : ‖exp (-((π / 4 : ℝ) * I))‖ = 1 := by
  rw [show -(((π / 4 : ℝ) : ℂ) * I) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-! ### The rotation `z ↦ e^{-iπ/4} z` on integrands -/

/-- The **rotation of an integrand**, `F(z) = e^{-iπ/4} f(e^{-iπ/4} z)`: the change of variable
that straightens the slanted contour `Zeta.RiemannSiegel.line` into a vertical line. -/
noncomputable def rotatedFun (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  exp (-((π / 4 : ℝ) * I)) * f (exp (-((π / 4 : ℝ) * I)) * z)

/-- **A rotated integrand, evaluated at a rotated point.** -/
theorem rotatedFun_exp_mul (f : ℂ → ℂ) (x : ℂ) :
    rotatedFun f (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * f x := by
  rw [rotatedFun, ← mul_assoc, exp_neg_pi_div_four_mul_I_mul_exp, one_mul]

/-- **The modulus of a rotated integrand** is that of the integrand at the rotated point. -/
theorem norm_rotatedFun (f : ℂ → ℂ) (z : ℂ) :
    ‖rotatedFun f z‖ = ‖f (exp (-((π / 4 : ℝ) * I)) * z)‖ := by
  rw [rotatedFun, norm_mul, norm_exp_neg_pi_div_four_mul_I, one_mul]

/-- **A rotated integrand is holomorphic wherever the integrand is.** -/
theorem differentiableAt_rotatedFun {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (exp (-((π / 4 : ℝ) * I)) * z)) :
    DifferentiableAt ℂ (rotatedFun f) z :=
  (hf.comp z (by fun_prop)).const_mul _

/-- **The inverse rotation carries a punctured neighbourhood of a rotated point to a punctured
neighbourhood of the point.** -/
theorem tendsto_nhdsWithin_exp_neg_pi_div_four_mul_I (w : ℂ) :
    Tendsto (fun z : ℂ ↦ exp (-((π / 4 : ℝ) * I)) * z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * w)) (𝓝[≠] w) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h := ((by fun_prop : Continuous fun z : ℂ ↦ exp (-((π / 4 : ℝ) * I)) * z)).tendsto
      (exp ((π / 4 : ℝ) * I) * w)
    rw [← mul_assoc, exp_neg_pi_div_four_mul_I_mul_exp, one_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    exact fun hcon ↦
      hz (by rw [← hcon, ← mul_assoc, exp_pi_div_four_mul_I_mul_exp_neg, one_mul])

/-- **A rotated integrand inherits the simple poles of the integrand**, at the rotated points and
with the same residues. -/
theorem tendsto_sub_mul_rotatedFun {f : ℂ → ℂ} {n : ℤ} {R : ℂ}
    (h : Tendsto (fun x ↦ (x - n) * f x) (𝓝[≠] (n : ℂ)) (𝓝 R)) :
    Tendsto (fun z ↦ (z - exp ((π / 4 : ℝ) * I) * n) * rotatedFun f z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * (n : ℂ))) (𝓝 R) := by
  refine Tendsto.congr (fun z ↦ ?_)
    (h.comp (tendsto_nhdsWithin_exp_neg_pi_div_four_mul_I (n : ℂ)))
  simp only [Function.comp_apply, rotatedFun]
  linear_combination (f (exp (-((π / 4 : ℝ) * I)) * z) * (n : ℂ)) *
    exp_neg_pi_div_four_mul_I_mul_exp

/-! ### The Riemann–Siegel integrand in rotated coordinates -/

/-- The **Riemann–Siegel integrand in rotated coordinates**, `F(z) = e^{-iπ/4} f(e^{-iπ/4} z)` for
`f(x) = x^{-s} G(x)`. -/
noncomputable def rotatedIntegrand (s : ℂ) : ℂ → ℂ := rotatedFun (integrand s)

/-- **The rotated integrand, evaluated at a rotated point.** -/
theorem rotatedIntegrand_exp_mul (s x : ℂ) :
    rotatedIntegrand s (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * integrand s x :=
  rotatedFun_exp_mul _ _

/-- **The Riemann–Siegel integrand is holomorphic off the integers**, wherever the slanted branch
of the power is. -/
theorem differentiableAt_integrand (s : ℂ) {x : ℂ} (hx : exp ((π / 4 : ℝ) * I) * x ∈ slitPlane)
    (hn : ∀ n : ℤ, x ≠ n) : DifferentiableAt ℂ (integrand s) x :=
  (differentiableAt_slantCpow (-s) hx).mul (differentiableAt_kernel hn)

/-- **The rotated integrand is holomorphic off the rotated integers**, on the right half-plane. -/
theorem differentiableAt_rotatedIntegrand (s : ℂ) {z : ℂ} (hz : 0 < z.re)
    (hn : ∀ n : ℤ, z ≠ exp ((π / 4 : ℝ) * I) * n) :
    DifferentiableAt ℂ (rotatedIntegrand s) z := by
  have hzz : exp ((π / 4 : ℝ) * I) * (exp (-((π / 4 : ℝ) * I)) * z) = z := by
    rw [← mul_assoc, exp_pi_div_four_mul_I_mul_exp_neg, one_mul]
  exact differentiableAt_rotatedFun (differentiableAt_integrand s
    (mem_slitPlane_iff.2 (Or.inl (by rwa [hzz]))) fun n hcon ↦ hn n (by rw [← hzz, hcon]))

/-- **Every positive integer is a simple pole of the Riemann–Siegel integrand**, with residue
`n^{-s}/(2πi)`. -/
theorem tendsto_sub_mul_integrand (s : ℂ) {n : ℤ} (hn : 0 < n) :
    Tendsto (fun x ↦ (x - n) * integrand s x) (𝓝[≠] (n : ℂ))
      (𝓝 ((n : ℂ) ^ (-s) / (2 * π * I))) := by
  have hcast : ((n : ℤ) : ℂ) = (((n : ℝ)) : ℂ) := (Complex.ofReal_intCast n).symm
  have hrpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : exp ((π / 4 : ℝ) * I) * ((n : ℤ) : ℂ) ∈ slitPlane := by
    refine mem_slitPlane_iff.2 (Or.inl ?_)
    rw [hcast, re_exp_pi_div_four_mul_I_mul_ofReal]
    positivity
  rw [show ((n : ℂ) ^ (-s) : ℂ) = slantCpow ((n : ℤ) : ℂ) (-s) from by
    rw [hcast]; exact (slantCpow_ofReal hrpos (-s)).symm, div_eq_mul_one_div]
  refine Tendsto.congr (fun x ↦ ?_)
    ((((differentiableAt_slantCpow (-s) hre).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds).mul (tendsto_sub_mul_kernel n))
  rw [integrand]; ring

/-- **Every rotated positive integer is a simple pole of the rotated integrand**, with residue
`n^{-s}/(2πi)`. -/
theorem tendsto_sub_mul_rotatedIntegrand (s : ℂ) {n : ℤ} (hn : 0 < n) :
    Tendsto (fun z ↦ (z - exp ((π / 4 : ℝ) * I) * n) * rotatedIntegrand s z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * n)) (𝓝 ((n : ℂ) ^ (-s) / (2 * π * I))) :=
  tendsto_sub_mul_rotatedFun (tendsto_sub_mul_integrand s hn)

/-! ### The Gaussian bound on the horizontal sides -/

/-- **A Gaussian bound for the Riemann–Siegel integrand** away from the real axis. -/
theorem norm_integrand_le (s : ℂ) {x : ℂ} (hx : 0 < (exp ((π / 4 : ℝ) * I) * x).re)
    (h1 : 1 ≤ ‖x‖) (h2 : Real.sqrt 2 / 2 ≤ |x.im|) :
    ‖integrand s x‖ ≤ Real.exp (‖x‖ * |s.re| + 3 * π * |s.im| / 4 - 2 * π * x.re * x.im) := by
  have hxpos : (0 : ℝ) < ‖x‖ := by linarith
  have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
  -- the denominator is at least `1` in modulus, since `sinh` grows off the real axis
  have hsin : (1 : ℝ) ≤ ‖sin ((π : ℂ) * x)‖ := Complex.one_le_norm_sin_pi_mul h2
  -- the modulus of the integrand, factor by factor
  have hnorm : ‖integrand s x‖
      = Real.exp (Real.log ‖x‖ * (-s).re + slantArg x * s.im) *
        (Real.exp (-(2 * π * x.re * x.im)) / (2 * ‖sin (π * x)‖)) := by
    rw [integrand, norm_mul, norm_slantCpow hx0, kernel_eq_div_two_mul_I_mul_sin, norm_div,
      Complex.norm_exp_pi_mul_I_mul_sq,
      show ‖(2 : ℂ) * I * sin ((π : ℂ) * x)‖ = 2 * ‖sin ((π : ℂ) * x)‖ by simp,
      Real.rpow_def_of_pos hxpos, Complex.neg_im, mul_neg,
      Real.exp_neg (slantArg x * s.im), div_inv_eq_mul,
      ← Real.exp_add (Real.log ‖x‖ * (-s).re) (slantArg x * s.im)]
  -- the logarithmic factor
  have hlog : Real.log ‖x‖ * (-s).re ≤ ‖x‖ * |s.re| := by
    have hre : (-s).re ≤ |s.re| := by simpa using neg_le_abs s.re
    nlinarith [Real.log_nonneg h1, Real.log_le_self hxpos.le, abs_nonneg s.re]
  -- the argument factor
  have harg : slantArg x * s.im ≤ 3 * π * |s.im| / 4 := by
    have h := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hx))
    have hb : |slantArg x| ≤ 3 * π / 4 := by
      rw [slantArg, abs_le]; constructor <;> linarith
    nlinarith [le_abs_self (slantArg x * s.im), abs_mul (slantArg x) s.im, abs_nonneg s.im,
      abs_nonneg (slantArg x), mul_le_mul_of_nonneg_right hb (abs_nonneg s.im)]
  rw [hnorm]
  refine le_trans (mul_le_mul_of_nonneg_left (div_le_self (Real.exp_pos _).le (by linarith))
    (Real.exp_pos _).le) ?_
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

/-- A point whose imaginary part is `c` times a quantity of modulus at least one lies at distance
at least `c` from the real axis. -/
theorem le_abs_im_of_im_eq_mul {z : ℂ} {c d : ℝ} (hc : 0 ≤ c) (hz : z.im = c * d)
    (hd : 1 ≤ |d|) : c ≤ |z.im| := by
  rw [hz, abs_mul, abs_of_nonneg hc]
  exact le_mul_of_one_le_right hc hd

/-- **A Gaussian bound for the rotated integrand** on a horizontal segment far from the real
axis. -/
private theorem norm_rotatedIntegrand_le (s : ℂ) {ξ y : ℝ} (hξ : 0 < ξ) (h1 : 1 ≤ |y|)
    (h2 : 1 ≤ |y - ξ|) :
    ‖rotatedIntegrand s ((ξ : ℂ) + (y : ℂ) * I)‖
      ≤ Real.exp ((ξ + |y|) * |s.re| + 3 * π * |s.im| / 4 + π * ξ ^ 2 - π * |y| ^ 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2n : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  set x : ℂ := exp (-((π / 4 : ℝ) * I)) * ((ξ : ℂ) + (y : ℂ) * I) with hxdef
  have hxre : x.re = Real.sqrt 2 / 2 * (ξ + y) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_re]; simp
  have hxim : x.im = Real.sqrt 2 / 2 * (y - ξ) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_im]; simp
  have hrot : exp ((π / 4 : ℝ) * I) * x = (ξ : ℂ) + (y : ℂ) * I := by
    rw [hxdef, ← mul_assoc, exp_pi_div_four_mul_I_mul_exp_neg, one_mul]
  have hnx : ‖x‖ = ‖(ξ : ℂ) + (y : ℂ) * I‖ := by
    rw [hxdef, norm_mul, norm_exp_neg_pi_div_four_mul_I, one_mul]
  have hnx1 : 1 ≤ ‖x‖ := by
    refine h1.trans (hnx ▸ ?_)
    simpa using Complex.abs_im_le_norm ((ξ : ℂ) + (y : ℂ) * I)
  have hnx2 : ‖x‖ ≤ ξ + |y| := by
    rw [hnx]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [abs_of_pos hξ]
  have hxim2 := le_abs_im_of_im_eq_mul (by positivity) hxim h2
  have hbound := norm_integrand_le s (by rw [hrot]; simpa using hξ) hnx1 hxim2
  refine le_trans ?_ (hbound.trans (Real.exp_le_exp.2 ?_))
  · rw [rotatedIntegrand, norm_rotatedFun, ← hxdef]
  · have hprod : 2 * π * x.re * x.im = π * |y| ^ 2 - π * ξ ^ 2 := by
      rw [hxre, hxim, sq_abs]
      linear_combination (π * (y ^ 2 - ξ ^ 2) / 2) * hs2
    rw [hprod]
    nlinarith [abs_nonneg s.re]

/-- **A horizontal side of the truncated rectangle vanishes** as the truncation recedes, for any
integrand whose modulus is bounded by a Gaussian in the height. -/
theorem tendsto_HIntegral_of_norm_le {F : ℂ → ℂ} {β α c C₀ C₁ T : ℝ} (hβα : β ≤ α) (hc : 0 < c)
    (hb : ∀ ξ y : ℝ, β ≤ ξ → ξ ≤ α → T ≤ |y| →
      ‖F ((ξ : ℂ) + (y : ℂ) * I)‖ ≤ Real.exp (C₀ + C₁ * |y| - c * y ^ 2))
    {y : ℝ → ℝ} (hy : Tendsto (fun H ↦ |y H|) atTop atTop) :
    Tendsto (fun H ↦ HIntegral F β α (y H)) atTop (𝓝 0) := by
  -- the bound along a single horizontal side
  have hbound : ∀ H : ℝ, T ≤ |y H| →
      ‖HIntegral F β α (y H)‖ ≤ Real.exp (C₀ + C₁ * |y H| - c * |y H| ^ 2) * |α - β| := by
    intro H hH
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun ξ hξ ↦ ?_
    rw [Set.uIoc_of_le hβα, Set.mem_Ioc] at hξ
    rw [sq_abs]
    exact hb ξ (y H) hξ.1.le hξ.2 hH
  -- the bound tends to zero
  have hφ0 : Tendsto (fun u : ℝ ↦ Real.exp (C₀ + C₁ * u - c * u ^ 2) * |α - β|) atTop (𝓝 0) := by
    have hlin : Tendsto (fun u : ℝ ↦ C₁ - c * u) atTop atBot := by
      have h1 : Tendsto (fun u : ℝ ↦ c * u) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hc tendsto_id
      simpa [sub_eq_add_neg] using
        tendsto_atBot_add_const_left atTop C₁ (tendsto_neg_atTop_atBot.comp h1)
    have hquad : Tendsto (fun u : ℝ ↦ C₀ + C₁ * u - c * u ^ 2) atTop atBot := by
      refine Tendsto.congr (fun u ↦ ?_)
        (tendsto_atBot_add_const_left atTop C₀ (tendsto_id.atTop_mul_atBot₀ hlin))
      simp only [id_eq]; ring
    simpa using (Real.tendsto_exp_comp_nhds_zero.2 hquad).mul_const |α - β|
  refine squeeze_zero_norm' ?_ (hφ0.comp hy)
  filter_upwards [hy.eventually_ge_atTop T] with H hH using hbound H hH

/-- **The horizontal sides of the truncated rectangle vanish** as the truncation recedes. -/
theorem tendsto_HIntegral_rotatedIntegrand (s : ℂ) {β α : ℝ} (hβ : 0 < β) (hβα : β ≤ α)
    {y : ℝ → ℝ} (hy : Tendsto (fun H ↦ |y H|) atTop atTop) :
    Tendsto (fun H ↦ HIntegral (rotatedIntegrand s) β α (y H)) atTop (𝓝 0) := by
  refine tendsto_HIntegral_of_norm_le (C₀ := α * |s.re| + 3 * π * |s.im| / 4 + π * α ^ 2)
    (C₁ := |s.re|) (T := α + 1) hβα Real.pi_pos (fun ξ u hξ1 hξ2 hu ↦ ?_) hy
  have hξ0 : 0 < ξ := hβ.trans_le hξ1
  have h1 : 1 ≤ |u| := by linarith
  have h2 : 1 ≤ |u - ξ| := by
    linarith [abs_sub_abs_le_abs_sub u ξ, abs_of_nonneg hξ0.le]
  refine (norm_rotatedIntegrand_le s hξ0 h1 h2).trans (Real.exp_le_exp.2 ?_)
  have hsq : ξ ^ 2 ≤ α ^ 2 := by nlinarith
  rw [sq_abs]
  nlinarith [mul_le_mul_of_nonneg_right hξ2 (abs_nonneg s.re),
    mul_le_mul_of_nonneg_left hsq Real.pi_pos.le]

/-! ### The vertical sides -/

/-- `x / √2 = (√2/2) x`. -/
private theorem div_sqrt_two (x : ℝ) : x / Real.sqrt 2 = Real.sqrt 2 / 2 * x := by
  rw [div_eq_iff (Real.sqrt_pos.2 two_pos).ne']
  linear_combination (-(x / 2)) * Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- **A truncated vertical side of the rotated rectangle is a truncation of the slant integral**,
for any integrand that the rotation carries onto `f`. -/
theorem VIntegral_eq_intervalIntegral_line {F f : ℂ → ℂ}
    (hF : ∀ x : ℂ, F (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * f x) (a H : ℝ) :
    VIntegral F (a / Real.sqrt 2) (-H) H
      = (1 + I) * ∫ w in (-(H / Real.sqrt 2) - a / 2)..(H / Real.sqrt 2 - a / 2), f (line a w) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsqC : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by exact_mod_cast hsq
  have hend1 : Real.sqrt 2 * (-(H / Real.sqrt 2) - a / 2) + a / Real.sqrt 2 = -H := by
    rw [div_sqrt_two H, div_sqrt_two a]; linear_combination (-(H / 2)) * hsq
  have hend2 : Real.sqrt 2 * (H / Real.sqrt 2 - a / 2) + a / Real.sqrt 2 = H := by
    rw [div_sqrt_two H, div_sqrt_two a]; linear_combination (H / 2) * hsq
  have hpt : ∀ w : ℝ,
      F (((a / Real.sqrt 2 : ℝ) : ℂ) + ((Real.sqrt 2 * w + a / Real.sqrt 2 : ℝ) : ℂ) * I)
        = exp (-((π / 4 : ℝ) * I)) * f (line a w) := by
    intro w
    rw [show ((a / Real.sqrt 2 : ℝ) : ℂ) + ((Real.sqrt 2 * w + a / Real.sqrt 2 : ℝ) : ℂ) * I
        = exp ((π / 4 : ℝ) * I) * line a w from by
      rw [exp_pi_div_four_mul_I_mul_line, div_sqrt_two a]; push_cast; ring, hF]
  have hsub := intervalIntegral.smul_integral_comp_mul_add
    (a := -(H / Real.sqrt 2) - a / 2) (b := H / Real.sqrt 2 - a / 2)
    (fun y : ℝ ↦ F ((a / Real.sqrt 2 : ℝ) + (y : ℝ) * I))
    (Real.sqrt 2) (a / Real.sqrt 2)
  rw [hend1, hend2] at hsub
  rw [VIntegral, ← hsub]
  simp only [hpt, intervalIntegral.integral_const_mul, Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [exp_neg_pi_div_four_mul_I]
  push_cast
  linear_combination ((I + 1) / 2) * hsqC - (((Real.sqrt 2 : ℝ) : ℂ) ^ 2 / 2) * Complex.I_sq

/-- **A truncated vertical side of the rotated rectangle is a truncation of the contour
integral.** -/
theorem VIntegral_rotatedIntegrand (s : ℂ) (a H : ℝ) :
    VIntegral (rotatedIntegrand s) (a / Real.sqrt 2) (-H) H
      = (1 + I) * ∫ w in (-(H / Real.sqrt 2) - a / 2)..(H / Real.sqrt 2 - a / 2),
          contourIntegrand s a w :=
  VIntegral_eq_intervalIntegral_line (rotatedIntegrand_exp_mul s) a H

/-- **The truncated vertical side converges to the slant integral.** -/
theorem tendsto_VIntegral_nhds_slantIntegral {F f : ℂ → ℂ}
    (hF : ∀ x : ℂ, F (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * f x) {a : ℝ}
    (hint : Integrable fun w : ℝ ↦ f (line a w)) :
    Tendsto (fun H : ℝ ↦ VIntegral F (a / Real.sqrt 2) (-H) H) atTop (𝓝 (slantIntegral f a)) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hdiv : Tendsto (fun H : ℝ ↦ H / Real.sqrt 2) atTop atTop :=
    tendsto_id.atTop_div_const hs2
  simp only [VIntegral_eq_intervalIntegral_line hF, slantIntegral]
  refine Filter.Tendsto.const_mul _
    (MeasureTheory.intervalIntegral_tendsto_integral hint ?_ ?_)
  · simpa [sub_eq_add_neg] using
      tendsto_atBot_add_const_right atTop (-(a / 2)) (tendsto_neg_atTop_atBot.comp hdiv)
  · simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(a / 2)) hdiv

/-- **The truncated vertical side converges to the Riemann–Siegel contour integral.** -/
theorem tendsto_VIntegral_rotatedIntegrand (s : ℂ) {a : ℝ}
    (hint : Integrable (contourIntegrand s a)) :
    Tendsto (fun H : ℝ ↦ VIntegral (rotatedIntegrand s) (a / Real.sqrt 2) (-H) H) atTop
      (𝓝 (contourIntegral s a)) :=
  tendsto_VIntegral_nhds_slantIntegral (rotatedIntegrand_exp_mul s) hint

/-- **The truncated rectangle converges to the difference of its two vertical sides.** -/
theorem tendsto_RectangleIntegral_of_tendsto {F : ℂ → ℂ} {β α : ℝ} {A B : ℂ}
    (h1 : Tendsto (fun H : ℝ ↦ HIntegral F β α (-H)) atTop (𝓝 0))
    (h2 : Tendsto (fun H : ℝ ↦ HIntegral F β α H) atTop (𝓝 0))
    (h3 : Tendsto (fun H : ℝ ↦ VIntegral F α (-H) H) atTop (𝓝 A))
    (h4 : Tendsto (fun H : ℝ ↦ VIntegral F β (-H) H) atTop (𝓝 B)) :
    Tendsto (fun H : ℝ ↦ RectangleIntegral F ((β : ℂ) - (H : ℂ) * I) ((α : ℂ) + (H : ℂ) * I))
      atTop (𝓝 (A - B)) := by
  have h5 := ((h1.sub h2).add h3).sub h4
  simp only [sub_zero, zero_add] at h5
  refine Tendsto.congr (fun H ↦ ?_) h5
  simp [RectangleIntegral]

/-- **The truncated rectangle converges to the difference of the two contour integrals.** -/
theorem tendsto_RectangleIntegral_rotatedIntegrand (s : ℂ) {a b : ℝ} (hb0 : 0 < b / Real.sqrt 2)
    (hba : b / Real.sqrt 2 ≤ a / Real.sqrt 2) (hia : Integrable (contourIntegrand s a))
    (hib : Integrable (contourIntegrand s b)) :
    Tendsto (fun H : ℝ ↦ RectangleIntegral (rotatedIntegrand s)
      (((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I) (((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I))
      atTop (𝓝 (contourIntegral s a - contourIntegral s b)) :=
  tendsto_RectangleIntegral_of_tendsto
    (tendsto_HIntegral_rotatedIntegrand s hb0 hba (y := fun H : ℝ ↦ -H)
      (by simpa using tendsto_abs_atTop_atTop))
    (tendsto_HIntegral_rotatedIntegrand s hb0 hba (y := fun H : ℝ ↦ H) tendsto_abs_atTop_atTop)
    (tendsto_VIntegral_rotatedIntegrand s hia) (tendsto_VIntegral_rotatedIntegrand s hib)

/-! ### The contour-shift identity -/

/-- **The one-step contour shift**, for any integrand holomorphic off the integers whose horizontal
sides vanish: moving the contour from `L(n − ½)` out to `L(n + ½)` crosses the single integer `n`,
and the difference of the two slant integrals is `2πi` times the residue there. -/
theorem slantIntegral_sub_slantIntegral_of_pole {f F : ℂ → ℂ} {n : ℤ} {R : ℂ} (hn : 0 < n)
    (hF : ∀ x : ℂ, F (exp ((π / 4 : ℝ) * I) * x) = exp (-((π / 4 : ℝ) * I)) * f x)
    (hdiff : ∀ z : ℂ, 0 < z.re → (∀ k : ℤ, z ≠ exp ((π / 4 : ℝ) * I) * k) →
      DifferentiableAt ℂ F z)
    (hpole : Tendsto (fun z ↦ (z - exp ((π / 4 : ℝ) * I) * n) * F z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * (n : ℂ))) (𝓝 R))
    (hH1 : Tendsto (fun H : ℝ ↦ HIntegral F (((n : ℝ) - 1 / 2) / Real.sqrt 2)
      (((n : ℝ) + 1 / 2) / Real.sqrt 2) (-H)) atTop (𝓝 0))
    (hH2 : Tendsto (fun H : ℝ ↦ HIntegral F (((n : ℝ) - 1 / 2) / Real.sqrt 2)
      (((n : ℝ) + 1 / 2) / Real.sqrt 2) H) atTop (𝓝 0))
    (hia : Integrable fun w : ℝ ↦ f (line ((n : ℝ) + 1 / 2) w))
    (hib : Integrable fun w : ℝ ↦ f (line ((n : ℝ) - 1 / 2) w)) :
    slantIntegral f ((n : ℝ) + 1 / 2) - slantIntegral f ((n : ℝ) - 1 / 2) = 2 * π * I * R := by
  have hpiC : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlt2 : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : ((n : ℤ) : ℂ) = (((n : ℝ)) : ℂ) := (Complex.ofReal_intCast n).symm
  set b : ℝ := (n : ℝ) - 1 / 2 with hbdef
  set a : ℝ := (n : ℝ) + 1 / 2 with hadef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have hβ0 : 0 < b / Real.sqrt 2 := div_pos hb0 hs2
  have hβα : b / Real.sqrt 2 < a / Real.sqrt 2 := by
    rw [div_lt_div_iff_of_pos_right hs2, hbdef, hadef]; linarith
  set p : ℂ := exp ((π / 4 : ℝ) * I) * (n : ℂ) with hpdef
  have hpre : p.re = (n : ℝ) / Real.sqrt 2 := by
    rw [hpdef, hcast, re_exp_pi_div_four_mul_I_mul_ofReal]
  have hpim : p.im = (n : ℝ) / Real.sqrt 2 := by
    rw [hpdef, hcast, exp_pi_div_four_mul_I, div_sqrt_two]
    simp [Complex.mul_im]
  -- the only rotated integer whose abscissa lies in `[b/√2, a/√2]` is `p`
  have hstrip : ∀ k : ℤ, b / Real.sqrt 2 ≤ (exp ((π / 4 : ℝ) * I) * (k : ℂ)).re →
      (exp ((π / 4 : ℝ) * I) * (k : ℂ)).re ≤ a / Real.sqrt 2 → k = n := by
    intro k h1 h2
    rw [← Complex.ofReal_intCast k,
      re_exp_pi_div_four_mul_I_mul_ofReal, div_le_div_iff_of_pos_right hs2] at h1 h2
    rw [hbdef] at h1
    rw [hadef] at h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hk : ((k : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 h
      linarith
    · have hk : ((n : ℝ)) + 1 ≤ (k : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 h
      linarith
  -- the rectangle integral is the residue, for every large enough truncation height
  have key : ∀ᶠ H : ℝ in atTop,
      RectangleIntegral F (((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I)
          (((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I) = 2 * π * I * R := by
    filter_upwards [eventually_gt_atTop ((n : ℝ) / Real.sqrt 2)] with H hH
    set z : ℂ := ((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I with hzdef
    set w : ℂ := ((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I with hwdef
    have hzre : z.re = b / Real.sqrt 2 := by rw [hzdef]; simp
    have hzim : z.im = -H := by rw [hzdef]; simp
    have hwre : w.re = a / Real.sqrt 2 := by rw [hwdef]; simp
    have hwim : w.im = H := by rw [hwdef]; simp
    have hH0 : 0 < H := lt_trans (by positivity) hH
    have hzw1 : z.re ≤ w.re := by rw [hzre, hwre]; exact hβα.le
    have hzw2 : z.im ≤ w.im := by rw [hzim, hwim]; linarith
    have hnhds : Rectangle z w ∈ 𝓝 p := by
      have hHn : (0 : ℝ) < (n : ℝ) / Real.sqrt 2 := by positivity
      rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, hzre, hzim, hwre, hwim,
        Set.uIoo_of_le hβα.le, Set.uIoo_of_le (by linarith : (-H : ℝ) ≤ H),
        Set.mem_Ioo, Set.mem_Ioo, hpre, hpim]
      refine ⟨⟨?_, ?_⟩, by linarith, hH⟩
      · rw [div_lt_div_iff_of_pos_right hs2, hbdef]; linarith
      · rw [div_lt_div_iff_of_pos_right hs2, hadef]; linarith
    have hrect : HolomorphicOn F (Rectangle z w \ {p}) := by
      intro ζ hζ
      obtain ⟨hr1, hr2, -, -⟩ := (mem_Rect hzw1 hzw2 ζ).1 hζ.1
      rw [hzre] at hr1
      rw [hwre] at hr2
      refine (hdiff ζ (lt_of_lt_of_le hβ0 hr1) ?_).differentiableWithinAt
      intro k hk
      refine hζ.2 (Set.mem_singleton_iff.2 ?_)
      rw [hk, hstrip k (by rw [← hk]; exact hr1) (by rw [← hk]; exact hr2), ← hpdef]
    -- the simple pole at `p`
    have hballholo : HolomorphicOn F (Metric.ball p (1 / 2) \ {p}) := by
      intro ζ hζ
      have hd : ‖ζ - p‖ < 1 / 2 := by simpa [Complex.dist_eq] using Metric.mem_ball.1 hζ.1
      refine (hdiff ζ ?_ ?_).differentiableWithinAt
      · have h2 : p.re - ζ.re ≤ ‖ζ - p‖ := by
          linarith [neg_le_of_abs_le (Complex.abs_re_le_norm (ζ - p)), Complex.sub_re ζ p]
        have h4 : (1 : ℝ) / Real.sqrt 2 ≤ (n : ℝ) / Real.sqrt 2 := by gcongr
        have h5 : (1 : ℝ) / 2 < 1 / Real.sqrt 2 := by rw [lt_div_iff₀ hs2]; linarith
        rw [hpre] at h2
        linarith
      · intro k hk
        have hne : k ≠ n := fun h ↦ hζ.2 (Set.mem_singleton_iff.2 (by rw [hk, h, hpdef]))
        have h1 : (1 : ℝ) ≤ ‖(k : ℂ) - (n : ℂ)‖ := by
          rw [← Int.cast_sub k n, Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hne)
        have h2 : ‖ζ - p‖ = ‖(k : ℂ) - (n : ℂ)‖ := by
          rw [hk, hpdef, ← mul_sub, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
        linarith
    obtain ⟨V, hV, hbdd⟩ :=
      ResidueOfTendsTo (Metric.ball_mem_nhds p (by norm_num)) hballholo hpole
    obtain ⟨C, hC⟩ := hbdd
    have hnear : (F - fun t ↦ R / (t - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
      refine Asymptotics.isBigO_iff.2 ⟨C, ?_⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds hV, self_mem_nhdsWithin] with ζ h1 h2
      simpa [div_eq_mul_inv] using hC ⟨ζ, ⟨h1, h2⟩, rfl⟩
    have hres := ResidueTheoremOnRectangleWithSimplePole' hzw1 hzw2 hnhds hrect hnear
    rw [RectangleIntegral', smul_eq_mul] at hres
    field_simp at hres
    linear_combination hres
  -- the truncated rectangle converges to the difference of the two slant integrals
  have hlim := tendsto_RectangleIntegral_of_tendsto hH1 hH2
    (tendsto_VIntegral_nhds_slantIntegral hF hia) (tendsto_VIntegral_nhds_slantIntegral hF hib)
  have hconst : Tendsto (fun H : ℝ ↦ RectangleIntegral F
      (((b / Real.sqrt 2 : ℝ) : ℂ) - (H : ℂ) * I) (((a / Real.sqrt 2 : ℝ) : ℂ) + (H : ℂ) * I))
      atTop (𝓝 (2 * π * I * R)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [key] with H hH using hH.symm
  exact (tendsto_nhds_unique hconst hlim).symm

/-- **The one-step contour shift.** Crossing the integer `n` picks up its residue `n^{-s}`. -/
theorem contourIntegral_sub_contourIntegral_eq_cpow_neg (s : ℂ) {n : ℤ} (hn : 0 < n) :
    contourIntegral s ((n : ℝ) + 1 / 2) - contourIntegral s ((n : ℝ) - 1 / 2)
      = (n : ℂ) ^ (-s) := by
  have hpiC : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb0 : 0 < (n : ℝ) - 1 / 2 := by linarith
  have ha0 : 0 < (n : ℝ) + 1 / 2 := by linarith
  have hβ0 : 0 < ((n : ℝ) - 1 / 2) / Real.sqrt 2 := div_pos hb0 hs2
  have hβα : ((n : ℝ) - 1 / 2) / Real.sqrt 2 ≤ ((n : ℝ) + 1 / 2) / Real.sqrt 2 := by
    rw [div_le_div_iff_of_pos_right hs2]; linarith
  have hbhalf : (n : ℝ) - 1 / 2 = ((n - 1 : ℤ) : ℝ) + 1 / 2 := by push_cast; ring
  have hahalf : (n : ℝ) + 1 / 2 = ((n : ℤ) : ℝ) + 1 / 2 := rfl
  have hkey := slantIntegral_sub_slantIntegral_of_pole (f := integrand s) hn
    (rotatedIntegrand_exp_mul s) (fun z hz hk ↦ differentiableAt_rotatedIntegrand s hz hk)
    (tendsto_sub_mul_rotatedIntegrand s hn)
    (tendsto_HIntegral_rotatedIntegrand s hβ0 hβα (y := fun H : ℝ ↦ -H)
      (by simpa using tendsto_abs_atTop_atTop))
    (tendsto_HIntegral_rotatedIntegrand s hβ0 hβα (y := fun H : ℝ ↦ H) tendsto_abs_atTop_atTop)
    (integrable_contourIntegrand s ha0 (by positivity) (norm_sin_pi_mul_line_ge hahalf))
    (integrable_contourIntegrand s hb0 (by positivity) (norm_sin_pi_mul_line_ge hbhalf))
  rw [contourIntegral_eq_slantIntegral, contourIntegral_eq_slantIntegral, hkey]
  field_simp

/-- **The Riemann–Siegel contour-shift identity** (`riemann_siegel.tex`, `thm:rs_shift`): moving
the slanted contour from `j + ½` out to `k + ½` sweeps across the integers `j < n ≤ k`, and the
difference of the two contour integrals is the corresponding partial sum. -/
theorem contourIntegral_sub_contourIntegral_eq_sum_cpow_neg (s : ℂ) {j k : ℕ} (hjk : j ≤ k) :
    contourIntegral s ((k : ℝ) + 1 / 2) - contourIntegral s ((j : ℝ) + 1 / 2)
      = ∑ i ∈ Finset.Ioc j k, (i : ℂ) ^ (-s) := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hstep :=
      contourIntegral_sub_contourIntegral_eq_cpow_neg s (n := (k : ℤ) + 1) (by positivity)
    push_cast at hstep
    rw [show ((k : ℝ) + 1 - 1 / 2) = (k : ℝ) + 1 / 2 from by ring] at hstep
    rw [Finset.sum_Ioc_succ_top hk, ← ih]
    push_cast
    linear_combination hstep

/-- **Partial sums from the contour** (`riemann_siegel.tex`, `cor:rs_partial_sum`): the integral
over the far contour is the partial sum `∑_{n ≤ k} n^{-s}` plus the `k`-independent quantity
`I(s, ½)`. -/
theorem sum_cpow_neg_eq_contourIntegral_sub_contourIntegral (s : ℂ) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, (i : ℂ) ^ (-s)
      = contourIntegral s ((k : ℝ) + 1 / 2) - contourIntegral s (1 / 2) := by
  have h := contourIntegral_sub_contourIntegral_eq_sum_cpow_neg s (Nat.zero_le k)
  rw [Nat.cast_zero, zero_add] at h
  rw [show Finset.Icc 1 k = Finset.Ioc 0 k from Finset.Icc_succ_left_eq_Ioc _ _]
  exact h.symm

end Zeta.RiemannSiegel
