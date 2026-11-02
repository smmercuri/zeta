/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannSiegel.Gaussian
public import Zeta.RiemannSiegel.Shift

/-!
# Riemann's Mordell integral

Siegel's identity rests on one auxiliary function of a *complex* parameter `u`: the integral

`N(u, a) = ∫_{L(a)} e^{-2πiux} G(x) dx`

of the Riemann–Siegel kernel `Zeta.RiemannSiegel.kernel` against an exponential rather than
against a power, taken along the slanted contour `Zeta.RiemannSiegel.line`
(`riemann_siegel_zero.tex`, `sec:rsz_mordell`). This is the integral studied by Kronecker and
Mordell, at the parameter Riemann needed.

Unlike the contour integral `I(s, a)` of `Zeta/RiemannSiegel/Integral.lean` it can be evaluated in
closed form by elementary means, because the exponential — unlike the power — interacts with *both*
structural symmetries of `G`: the quasi-periodicity `G(x + 1) = e^{2πix} G(x)`, and the simple pole
at every integer. Each symmetry yields one of the two difference equations below.

The pole shift reuses the rectangle apparatus of `Zeta/RiemannSiegel/Shift.lean` unchanged, that
apparatus taking the integrand as a parameter; comparing `L(½)` with `L(3/2)` rather than with
`L(-½)` keeps the crossed pole at `n = 1 > 0`, inside its existing hypotheses.

## Main results

* `Zeta.RiemannSiegel.mordellIntegrand`, `Zeta.RiemannSiegel.mordellIntegral`: the integrand
  `x ↦ e^{-2πiux} G(x)` and the integral `N(u, a)` (`def:rsz_mordell`);
* `Zeta.RiemannSiegel.integrable_mordellIntegrand`: absolute convergence (`lem:rsz_mordell_conv`);
* `Zeta.RiemannSiegel.mordellIntegral_sub_mordellIntegral_add_one`: the Gaussian difference
  equation `N(u, a) - N(u + 1, a) = e^{iπ/4} e^{-iπ(u + ½)²}` (`lem:rsz_mordell_gauss`);
* `Zeta.RiemannSiegel.mordellIntegral_sub_exp_mul_mordellIntegral_add_one`: the pole difference
  equation `N(u) - e^{2πiu} N(u + 1) = 1` (`lem:rsz_mordell_pole`);
* `Zeta.RiemannSiegel.mordellIntegral_eq`: the closed form
  `N(u) = (e^{-iπu²} - e^{-iπu}) / (e^{iπu} - e^{-iπu})` (`thm:rsz_mordell`).
-/
@[expose] public section


open Complex Filter MeasureTheory Topology

open scoped Real

namespace Zeta.RiemannSiegel

/-- The **Mordell integrand** `x ↦ e^{-2πiux} G(x)`, the Riemann–Siegel kernel against an
exponential in place of a power. -/
noncomputable def mordellIntegrand (u x : ℂ) : ℂ :=
  exp (-(2 * π * I * u * x)) * kernel x

/-- **Riemann's Mordell integral** `N(u, a) = ∫_{L(a)} e^{-2πiux} G(x) dx`, taken along the slanted
contour `Zeta.RiemannSiegel.line`. -/
noncomputable def mordellIntegral (u : ℂ) (a : ℝ) : ℂ :=
  slantIntegral (mordellIntegrand u) a

/-- The **Mordell integrand in rotated coordinates**, `F(z) = e^{-iπ/4} f(e^{-iπ/4} z)` for
`f(x) = e^{-2πiux} G(x)`. -/
noncomputable def rotatedMordellIntegrand (u : ℂ) : ℂ → ℂ := rotatedFun (mordellIntegrand u)

/-- **The rotated Mordell integrand, evaluated at a rotated point.** -/
theorem rotatedMordellIntegrand_exp_mul (u x : ℂ) :
    rotatedMordellIntegrand u (exp ((π / 4 : ℝ) * I) * x)
      = exp (-((π / 4 : ℝ) * I)) * mordellIntegrand u x :=
  rotatedFun_exp_mul _ _

/-- **The Mordell integrand is holomorphic off the integers.** -/
theorem differentiableAt_mordellIntegrand (u : ℂ) {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) :
    DifferentiableAt ℂ (mordellIntegrand u) x := by
  unfold mordellIntegrand
  exact (by fun_prop : DifferentiableAt ℂ (fun x : ℂ ↦ exp (-(2 * π * I * u * x))) x).mul
    (differentiableAt_kernel hx)

/-- **The rotated Mordell integrand is holomorphic off the rotated integers.** -/
theorem differentiableAt_rotatedMordellIntegrand (u : ℂ) {z : ℂ}
    (hz : ∀ n : ℤ, z ≠ exp ((π / 4 : ℝ) * I) * n) :
    DifferentiableAt ℂ (rotatedMordellIntegrand u) z :=
  differentiableAt_rotatedFun (differentiableAt_mordellIntegrand u fun n hcon ↦ hz n (by
    rw [← hcon, ← mul_assoc, exp_pi_div_four_mul_I_mul_exp_neg, one_mul]))

/-- **Every integer is a simple pole of the Mordell integrand**, with residue
`e^{-2πiun}/(2πi)`. -/
theorem tendsto_sub_mul_mordellIntegrand (u : ℂ) (n : ℤ) :
    Tendsto (fun x ↦ (x - n) * mordellIntegrand u x) (𝓝[≠] (n : ℂ))
      (𝓝 (exp (-(2 * π * I * u * n)) / (2 * π * I))) := by
  rw [div_eq_mul_one_div]
  refine Tendsto.congr (fun x ↦ ?_)
    ((((by fun_prop : Continuous fun x : ℂ ↦ exp (-(2 * π * I * u * x))).tendsto
      (n : ℂ)).mono_left nhdsWithin_le_nhds).mul (tendsto_sub_mul_kernel n))
  rw [mordellIntegrand]; ring

/-- **Every rotated integer is a simple pole of the rotated Mordell integrand**, with residue
`e^{-2πiun}/(2πi)`. -/
theorem tendsto_sub_mul_rotatedMordellIntegrand (u : ℂ) (n : ℤ) :
    Tendsto (fun z ↦ (z - exp ((π / 4 : ℝ) * I) * n) * rotatedMordellIntegrand u z)
      (𝓝[≠] (exp ((π / 4 : ℝ) * I) * n)) (𝓝 (exp (-(2 * π * I * u * n)) / (2 * π * I))) :=
  tendsto_sub_mul_rotatedFun (tendsto_sub_mul_mordellIntegrand u n)

/-! ### The Gaussian bound on the horizontal sides -/

/-- **A Gaussian bound for the Mordell integrand** away from the real axis. -/
theorem norm_mordellIntegrand_le (u : ℂ) {x : ℂ} (hx : Real.sqrt 2 / 2 ≤ |x.im|) :
    ‖mordellIntegrand u x‖ ≤ Real.exp (2 * π * ‖u‖ * ‖x‖ - 2 * π * x.re * x.im) := by
  -- the denominator is at least `1` in modulus, since `sinh` grows off the real axis
  have hsin : (1 : ℝ) ≤ ‖sin ((π : ℂ) * x)‖ := Complex.one_le_norm_sin_pi_mul hx
  have hnorm : ‖mordellIntegrand u x‖
      = ‖exp (-(2 * π * I * u * x))‖ *
        (Real.exp (-(2 * π * x.re * x.im)) / (2 * ‖sin (π * x)‖)) := by
    rw [mordellIntegrand, norm_mul, kernel_eq_div_two_mul_I_mul_sin, norm_div,
      Complex.norm_exp_pi_mul_I_mul_sq,
      show ‖(2 : ℂ) * I * sin ((π : ℂ) * x)‖ = 2 * ‖sin ((π : ℂ) * x)‖ by simp]
  have hexp : ‖exp (-(2 * π * I * u * x))‖ ≤ Real.exp (2 * π * ‖u‖ * ‖x‖) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
    rw [norm_neg]
    simp [abs_of_pos Real.pi_pos, mul_assoc]
  rw [hnorm, show 2 * π * ‖u‖ * ‖x‖ - 2 * π * x.re * x.im
      = 2 * π * ‖u‖ * ‖x‖ + -(2 * π * x.re * x.im) by ring, Real.exp_add]
  exact mul_le_mul hexp (div_le_self (Real.exp_pos _).le (by linarith)) (by positivity)
    (Real.exp_pos _).le

/-- **A Gaussian bound for the rotated Mordell integrand** on a horizontal segment far from the
real axis. -/
private theorem norm_rotatedMordellIntegrand_le (u : ℂ) {ξ y : ℝ} (hξ : 0 ≤ ξ) (h2 : 1 ≤ |y - ξ|) :
    ‖rotatedMordellIntegrand u ((ξ : ℂ) + (y : ℂ) * I)‖
      ≤ Real.exp (2 * π * ‖u‖ * (ξ + |y|) + π * ξ ^ 2 - π * |y| ^ 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2n : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  set x : ℂ := exp (-((π / 4 : ℝ) * I)) * ((ξ : ℂ) + (y : ℂ) * I) with hxdef
  have hxre : x.re = Real.sqrt 2 / 2 * (ξ + y) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_re]; simp
  have hxim : x.im = Real.sqrt 2 / 2 * (y - ξ) := by
    rw [hxdef, exp_neg_pi_div_four_mul_I_mul_im]; simp
  have hnx : ‖x‖ = ‖(ξ : ℂ) + (y : ℂ) * I‖ := by
    rw [hxdef, norm_mul, norm_exp_neg_pi_div_four_mul_I, one_mul]
  have hnx2 : ‖x‖ ≤ ξ + |y| := by
    rw [hnx]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [abs_of_nonneg hξ]
  have hxim2 := le_abs_im_of_im_eq_mul (by positivity) hxim h2
  have hbound := norm_mordellIntegrand_le u hxim2
  refine le_trans ?_ (hbound.trans (Real.exp_le_exp.2 ?_))
  · rw [rotatedMordellIntegrand, norm_rotatedFun, ← hxdef]
  · have hprod : 2 * π * x.re * x.im = π * |y| ^ 2 - π * ξ ^ 2 := by
      rw [hxre, hxim, sq_abs]
      linear_combination (π * (y ^ 2 - ξ ^ 2) / 2) * hs2
    rw [hprod]
    have := mul_le_mul_of_nonneg_left hnx2 (by positivity : (0 : ℝ) ≤ 2 * π * ‖u‖)
    linarith

/-- **The horizontal sides of the truncated rectangle vanish** as the truncation recedes, for the
rotated Mordell integrand. -/
theorem tendsto_HIntegral_rotatedMordellIntegrand (u : ℂ) {β α : ℝ} (hβ : 0 < β) (hβα : β ≤ α)
    {y : ℝ → ℝ} (hy : Tendsto (fun H ↦ |y H|) atTop atTop) :
    Tendsto (fun H ↦ HIntegral (rotatedMordellIntegrand u) β α (y H)) atTop (𝓝 0) := by
  refine tendsto_HIntegral_of_norm_le (C₀ := 2 * π * ‖u‖ * α + π * α ^ 2) (C₁ := 2 * π * ‖u‖)
    (T := α + 1) hβα Real.pi_pos (fun ξ v hξ1 hξ2 hv ↦ ?_) hy
  have hξ0 : 0 < ξ := hβ.trans_le hξ1
  have h2 : 1 ≤ |v - ξ| := by
    linarith [abs_sub_abs_le_abs_sub v ξ, abs_of_nonneg hξ0.le]
  refine (norm_rotatedMordellIntegrand_le u hξ0.le h2).trans (Real.exp_le_exp.2 ?_)
  have hsq : ξ ^ 2 ≤ α ^ 2 := by nlinarith
  rw [sq_abs]
  nlinarith [mul_le_mul_of_nonneg_left hξ2 (by positivity : (0 : ℝ) ≤ 2 * π * ‖u‖),
    mul_le_mul_of_nonneg_left hsq Real.pi_pos.le]

/-! ### Convergence -/

/-- **The exponent of the Mordell integrand along the contour is a quadratic** in the contour
parameter, with leading coefficient the real number `-2π`. -/
private theorem neg_mul_line_add_mul_line_sq (u : ℂ) (a w : ℝ) :
    -(2 * π * I * u * line a w) + π * I * line a w ^ 2
      = (-2 * π : ℂ) * (w : ℂ) ^ 2 + 2 * π * I * (1 + I) * ((a : ℂ) - u) * (w : ℂ)
        + (π * I * (a : ℂ) ^ 2 - 2 * π * I * u * (a : ℂ)) := by
  simp only [line, Complex.ofReal_add]
  -- the velocity of `L(a)` is `1 + I`, whose square is `2I`; the coefficient below is the
  -- cofactor of `I² + 1` in the difference of the two sides
  linear_combination ((π : ℂ) * (w : ℂ) ^ 2 * (I + 2)) * Complex.I_sq

/-- **The Mordell integrand along the contour**, as a single Gaussian over the kernel's
denominator. -/
theorem mordellIntegrand_line (u : ℂ) (a w : ℝ) :
    mordellIntegrand u (line a w)
      = exp ((-2 * π : ℂ) * (w : ℂ) ^ 2 + 2 * π * I * (1 + I) * ((a : ℂ) - u) * (w : ℂ)
          + (π * I * (a : ℂ) ^ 2 - 2 * π * I * u * (a : ℂ))) / (2 * I * sin (π * line a w)) := by
  rw [mordellIntegrand, kernel_eq_div_two_mul_I_mul_sin, ← mul_div_assoc, ← Complex.exp_add,
    neg_mul_line_add_mul_line_sq u a w]

/-- **Absolute convergence of the Mordell integral** along any half-integer contour, of either
sign. -/
theorem integrable_mordellIntegrand {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) (u : ℂ) :
    Integrable fun w : ℝ ↦ mordellIntegrand u (line a w) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hb : (-2 * π : ℂ).re < 0 := by simpa using Real.pi_pos
  have hline := continuous_line a
  have hcont : Continuous fun w : ℝ ↦ mordellIntegrand u (line a w) := by
    have hker : Continuous fun w : ℝ ↦ kernel (line a w) := by
      simp only [kernel_eq_div_two_mul_I_mul_sin]
      exact Continuous.div (by fun_prop) (by fun_prop) fun w ↦ by
        simpa [I_ne_zero] using sin_pi_mul_line_ne_zero ha w
    simp only [mordellIntegrand]
    exact (((continuous_const.mul hline).neg).cexp).mul hker
  refine Integrable.mono' (((integrable_cexp_quadratic' hb
    (2 * π * I * (1 + I) * ((a : ℂ) - u))
    (π * I * (a : ℂ) ^ 2 - 2 * π * I * u * (a : ℂ))).norm).div_const (Real.sqrt 2))
    hcont.aestronglyMeasurable (.of_forall fun w ↦ ?_)
  rw [mordellIntegrand_line u a w, norm_div,
    show ‖(2 : ℂ) * I * sin ((π : ℂ) * line a w)‖ = 2 * ‖sin ((π : ℂ) * line a w)‖ by simp]
  gcongr
  linarith [norm_sin_pi_mul_line_ge ha w]

/-! ### The first difference equation: the Gaussian shift -/

/-- **The increment of the Mordell integrand in `u` is a Gaussian centred at `u + ½`**: the
exponential cancels the pole of the kernel exactly. -/
theorem mordellIntegrand_sub_mordellIntegrand_add_one (u : ℂ) {x : ℂ} (hx : ∀ n : ℤ, x ≠ n) :
    mordellIntegrand u x - mordellIntegrand (u + 1) x
      = exp (-(π * I * (u + 1 / 2) ^ 2)) * exp (π * I * (x - (u + 1 / 2)) ^ 2) := by
  have hs : sin ((π : ℂ) * x) ≠ 0 := Complex.sin_pi_mul_ne_zero hx
  have hden : (2 : ℂ) * I * sin (π * x) ≠ 0 := by simpa [I_ne_zero] using hs
  -- `1 - e^{-2πix}` factors through the kernel's denominator
  have hnum : (1 : ℂ) - exp (-(2 * π * I * x)) = exp (-(π * I * x)) * (2 * I * sin (π * x)) := by
    rw [show (2 : ℂ) * I * sin (π * x) = exp (π * I * x) - exp (-(π * I * x)) from by
        rw [show ((π : ℂ) * I * x) = ((π : ℂ) * x) * I by ring]
        exact (exp_mul_I_sub_exp_neg_mul_I _).symm,
      mul_sub, ← Complex.exp_add, ← Complex.exp_add,
      show -((π : ℂ) * I * x) + π * I * x = 0 by ring, Complex.exp_zero,
      show -((π : ℂ) * I * x) + -(π * I * x) = -(2 * π * I * x) by ring]
  have hL : mordellIntegrand u x - mordellIntegrand (u + 1) x
      = exp (-(2 * π * I * u * x)) * exp (π * I * x ^ 2) * (1 - exp (-(2 * π * I * x))) /
        (2 * I * sin (π * x)) := by
    rw [mordellIntegrand, mordellIntegrand, kernel_eq_div_two_mul_I_mul_sin,
      show -(2 * (π : ℂ) * I * (u + 1) * x) = -(2 * π * I * u * x) + -(2 * π * I * x) by ring,
      Complex.exp_add]
    field_simp
  rw [hL, hnum, ← mul_assoc, mul_div_assoc, div_self hden, mul_one, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- **The first difference equation for the Mordell integral: the Gaussian shift.** The difference
does not depend on the abscissa `a` of the contour (`lem:rsz_mordell_gauss`). -/
theorem mordellIntegral_sub_mordellIntegral_add_one {a : ℝ} {n : ℤ} (ha : a = n + 1 / 2) (u : ℂ) :
    mordellIntegral u a - mordellIntegral (u + 1) a
      = exp ((π / 4 : ℝ) * I) * exp (-(π * I * (u + 1 / 2) ^ 2)) := by
  have hpt : ∀ w : ℝ, mordellIntegrand u (line a w) - mordellIntegrand (u + 1) (line a w)
      = exp (-(π * I * (u + 1 / 2) ^ 2)) * exp (π * I * (line a w - (u + 1 / 2)) ^ 2) := fun w ↦
    mordellIntegrand_sub_mordellIntegrand_add_one u fun k hk ↦
      sin_pi_mul_line_ne_zero ha w (by rw [hk, mul_comm]; exact Complex.sin_int_mul_pi k)
  have hint : ∫ w : ℝ, (mordellIntegrand u (line a w) - mordellIntegrand (u + 1) (line a w))
      = exp (-(π * I * (u + 1 / 2) ^ 2)) *
        ∫ w : ℝ, exp (π * I * (line a w - (u + 1 / 2)) ^ 2) := by
    rw [MeasureTheory.integral_congr_ae (.of_forall hpt), MeasureTheory.integral_const_mul]
  rw [mordellIntegral, mordellIntegral, slantIntegral, slantIntegral, ← mul_sub,
    ← MeasureTheory.integral_sub (integrable_mordellIntegrand ha u)
      (integrable_mordellIntegrand ha (u + 1)), hint]
  linear_combination exp (-(π * I * (u + 1 / 2) ^ 2)) *
    integral_exp_pi_mul_I_mul_line_sub_sq a (u + 1 / 2)

/-! ### The second difference equation: the pole shift -/

/-- **Quasi-periodicity of the Mordell integrand**, inherited from that of the kernel. -/
theorem mordellIntegrand_add_one (u x : ℂ) :
    mordellIntegrand u (x + 1) = exp (-(2 * π * I * u)) * mordellIntegrand (u - 1) x := by
  rw [mordellIntegrand, mordellIntegrand, kernel_add_one,
    show exp (-(2 * (π : ℂ) * I * u * (x + 1))) * (exp (2 * π * I * x) * kernel x)
      = (exp (-(2 * (π : ℂ) * I * u * (x + 1))) * exp (2 * π * I * x)) * kernel x by ring,
    show exp (-(2 * (π : ℂ) * I * u)) * (exp (-(2 * π * I * (u - 1) * x)) * kernel x)
      = (exp (-(2 * (π : ℂ) * I * u)) * exp (-(2 * π * I * (u - 1) * x))) * kernel x by ring,
    ← Complex.exp_add, ← Complex.exp_add,
    show -(2 * (π : ℂ) * I * u * (x + 1)) + 2 * π * I * x
      = -(2 * (π : ℂ) * I * u) + -(2 * π * I * (u - 1) * x) by ring]

/-- **Translating the contour by one**, the Mordell integral of parameter `u`. -/
theorem mordellIntegral_add_one (u : ℂ) (a : ℝ) :
    mordellIntegral u (a + 1) = exp (-(2 * π * I * u)) * mordellIntegral (u - 1) a := by
  simp only [mordellIntegral, slantIntegral, line_add_one, mordellIntegrand_add_one]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **The second difference equation for the Mordell integral: the pole shift**
(`lem:rsz_mordell_pole`). -/
theorem mordellIntegral_sub_exp_mul_mordellIntegral_add_one (u : ℂ) :
    mordellIntegral u (1 / 2) - exp (2 * π * I * u) * mordellIntegral (u + 1) (1 / 2) = 1 := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  -- moving the contour from `L(½)` out to `L(3/2)` crosses the single pole `x = 1` of the kernel,
  -- whose residue there is `e^{-2πiu}/(2πi)`; this is that shift, at the parameter `v`
  have key : ∀ v : ℂ, exp (-(2 * π * I * v)) * mordellIntegral (v - 1) (1 / 2)
      - mordellIntegral v (1 / 2) = exp (-(2 * π * I * v)) := by
    intro v
    have hres : 2 * (π : ℂ) * I * (exp (-(2 * π * I * v * (1 : ℤ))) / (2 * π * I))
        = exp (-(2 * π * I * v)) := by
      -- `field_simp` needs `(π : ℂ) ≠ 0` from the context to clear the denominator
      have hpiC : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
      push_cast
      field_simp
    have hβ : (0 : ℝ) < (((1 : ℤ) : ℝ) - 1 / 2) / Real.sqrt 2 := by
      push_cast; positivity
    have hβα : (((1 : ℤ) : ℝ) - 1 / 2) / Real.sqrt 2 ≤ (((1 : ℤ) : ℝ) + 1 / 2) / Real.sqrt 2 := by
      rw [div_le_div_iff_of_pos_right hs2]; norm_num
    have hpole := slantIntegral_sub_slantIntegral_of_pole (f := mordellIntegrand v)
      (F := rotatedMordellIntegrand v) (n := 1)
      (R := exp (-(2 * π * I * v * (1 : ℤ))) / (2 * π * I)) one_pos
      (rotatedMordellIntegrand_exp_mul v)
      (fun z _ hz ↦ differentiableAt_rotatedMordellIntegrand v hz)
      (tendsto_sub_mul_rotatedMordellIntegrand v 1)
      (tendsto_HIntegral_rotatedMordellIntegrand v hβ hβα
        (by simpa using tendsto_abs_atTop_atTop))
      (tendsto_HIntegral_rotatedMordellIntegrand v hβ hβα tendsto_abs_atTop_atTop)
      (integrable_mordellIntegrand (n := 1) rfl v)
      (integrable_mordellIntegrand (n := 0) (by push_cast; ring) v)
    rw [hres] at hpole
    have h32 : (((1 : ℤ) : ℝ) + 1 / 2) = 1 / 2 + 1 := by push_cast; ring
    have h12 : (((1 : ℤ) : ℝ) - 1 / 2) = 1 / 2 := by push_cast; ring
    rw [h32, h12] at hpole
    rw [← mordellIntegral_add_one v (1 / 2)]
    simpa [mordellIntegral] using hpole
  have h := key (u + 1)
  rw [add_sub_cancel_right] at h
  have he : exp (-(2 * (π : ℂ) * I * (u + 1))) = exp (-(2 * π * I * u)) := by
    rw [show -(2 * (π : ℂ) * I * (u + 1)) = -(2 * π * I * u) + ((-1 : ℤ) : ℂ) * (2 * π * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [he] at h
  have hinv : exp (2 * (π : ℂ) * I * u) * exp (-(2 * π * I * u)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination exp (2 * (π : ℂ) * I * u) * h -
    (mordellIntegral u (1 / 2) - 1) * hinv

/-! ### The closed form -/

/-- **Closed form of the Mordell integral** (`thm:rsz_mordell`): for `u` off the integers,
`N(u) = (e^{-iπu²} - e^{-iπu}) / (e^{iπu} - e^{-iπu})`. -/
theorem mordellIntegral_eq {u : ℂ} (hu : ∀ n : ℤ, u ≠ n) :
    mordellIntegral u (1 / 2)
      = (exp (-(π * I * u ^ 2)) - exp (-(π * I * u))) /
        (exp (π * I * u) - exp (-(π * I * u))) := by
  have hden : exp ((π : ℂ) * I * u) - exp (-((π : ℂ) * I * u)) ≠ 0 := by
    rw [show ((π : ℂ) * I * u) = ((π : ℂ) * u) * I by ring, exp_mul_I_sub_exp_neg_mul_I]
    simpa [I_ne_zero] using Complex.sin_pi_mul_ne_zero hu
  -- the Gaussian factor of the first difference equation, in terms of the atoms of the answer
  have hR : exp ((π / 4 : ℝ) * I) * exp (-((π : ℂ) * I * (u + 1 / 2) ^ 2))
      = exp (-((π : ℂ) * I * u ^ 2)) * exp (-((π : ℂ) * I * u)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have hP : exp (2 * (π : ℂ) * I * u) = exp ((π : ℂ) * I * u) * exp ((π : ℂ) * I * u) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hinv : exp ((π : ℂ) * I * u) * exp (-((π : ℂ) * I * u)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hg := mordellIntegral_sub_mordellIntegral_add_one (a := 1 / 2) (n := 0) (by norm_num) u
  have hp := mordellIntegral_sub_exp_mul_mordellIntegral_add_one u
  rw [hR] at hg
  rw [hP] at hp
  have hB : mordellIntegral (u + 1) (1 / 2)
      = mordellIntegral u (1 / 2) - exp (-((π : ℂ) * I * u ^ 2)) * exp (-((π : ℂ) * I * u)) := by
    linear_combination -hg
  rw [hB] at hp
  rw [eq_div_iff hden]
  linear_combination (-exp (-((π : ℂ) * I * u))) * hp +
    (exp ((π : ℂ) * I * u) * exp (-((π : ℂ) * I * u ^ 2)) * exp (-((π : ℂ) * I * u))
      - exp ((π : ℂ) * I * u) * mordellIntegral u (1 / 2)
      + exp (-((π : ℂ) * I * u ^ 2))) * hinv

end Zeta.RiemannSiegel
