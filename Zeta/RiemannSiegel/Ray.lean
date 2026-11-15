/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Zeta.Analysis.SpecialFunctions.GammaIntegral
public import Zeta.RiemannSiegel.Mirror
public import Zeta.RiemannSiegel.Mordell

/-!
# The Mellin transform of the Mordell integral along the diagonal ray

Riemann's passage from the closed form of the Mordell integral `N(u)`
(`Zeta/RiemannSiegel/Mordell.lean`) to `ζ` multiplies that identity by `u^{-s}` and integrates `u`
over the ray `e^{-iπ/4}(0, ∞)` (`riemann_siegel_zero.tex`, `sec:rsz_mellin`). It is the step that
crosses the critical strip: the left-hand side produces the Riemann–Siegel contour integral
`I(1-s, ½)`, and the right-hand side produces `ζ(1-s)` together with the mirror Hankel integral
`Φ̃(s)`.

The ray is forced. It must lie in the lower half-plane for the geometric series to converge, and
`e^{-iπ/4}` is the unique direction for which the exponential rate is positive *uniformly along*
`L(a)`, because `Re (e^{iπ/4} x) = a/√2` is *constant* on `L(a)`
(`Zeta.RiemannSiegel.re_exp_pi_div_four_mul_I_mul_line`). That constancy is what makes the double
integral absolutely convergent, hence Fubini applicable. The contour in `x` stays fixed.

Two of the three terms are evaluated by one workhorse, `rayIntegral_exp_neg_two_pi_mul_I_mul`: the
ray integral of `u ↦ e^{-2πiuz}` is `(2π)^{s-1} e^{iπ(s-1)/2} Γ(1-s) z^{s-1}`, the last power taken
in the slanted branch `Zeta.RiemannSiegel.slantCpow`. Taking `z = n` gives the Dirichlet series of
`ζ`, and taking `z` on `L(½)` gives, after Fubini, the contour integral. The third, Gaussian, term
is a constant multiple of the mirror Hankel ray integral of
`Zeta/RiemannSiegel/Mirror.lean`.

## Main results

* `Zeta.RiemannSiegel.rayIntegral`: the operator `𝓡F(s) = ω ∫_0^∞ (ρω)^{-s} F(ρω) dρ`,
  `ω = e^{-iπ/4}`;
* `Zeta.RiemannSiegel.rayIntegral_exp_neg_two_pi_mul_I_mul`: its value on an exponential;
* `Zeta.RiemannSiegel.rayIntegral_inv_one_sub_exp`: the geometric term,
  `-(2π)^{s-1} e^{iπ(s-1)/2} Γ(1-s) ζ(1-s)` (`lem:rsz_ray_zeta`);
* `Zeta.RiemannSiegel.rayIntegral_mordellIntegral`: the contour term,
  `(2π)^{s-1} e^{iπ(s-1)/2} Γ(1-s) I(1-s, ½)` (`lem:rsz_ray_contour`);
* `Zeta.RiemannSiegel.rayIntegral_mirrorKernel`: the Gaussian term,
  `e^{iπ(s-1)/4} Φ̃(s) / (2i)` (`lem:rsz_ray_hankel`);
* `Zeta.RiemannSiegel.riemannZeta_add_contourIntegral_half_eq`: the Mellin form of Siegel's
  identity, `ζ(s) + I(s, ½) = (2π)^s e^{-iπ(2-s)/4} Φ̃(1-s) / (2 Γ(s))` for `Re s > 1`
  (`thm:rsz_mellin`).
-/
@[expose] public section


open Complex MeasureTheory Set

open scoped Real

namespace Zeta.RiemannSiegel

/-! ### The Mellin transform along the diagonal ray -/

/-- The diagonal ray integrand `ρ ↦ (ρω)^{-s} F(ρω)` with `ω = e^{-iπ/4}`, the power being the
principal branch (`arg (ρω) = -π/4`). -/
noncomputable def rayIntegrand (f : ℂ → ℂ) (s : ℂ) (ρ : ℝ) : ℂ :=
  ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ (-s) * f ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))

/-- The Mellin transform along the diagonal ray, `𝓡F(s) = ω ∫_0^∞ (ρω)^{-s} F(ρω) dρ` with
`ω = e^{-iπ/4}`. The `ω` in front is the velocity of the ray. -/
noncomputable def rayIntegral (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  exp (-((π / 4 : ℝ) * I)) * ∫ ρ in Ioi (0 : ℝ), rayIntegrand f s ρ

/-- The ray is the mirror of the outgoing Hankel ray, `ρω = conj (e^{iπ/4} ρ)`. -/
theorem conj_exp_pi_div_four_mul_I_mul_ofReal (ρ : ℝ) :
    starRingEnd ℂ (exp ((π / 4 : ℝ) * I) * (ρ : ℂ)) = (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_neg, mul_comm]

/-- The abscissa of a point of the ray. -/
theorem re_ofReal_mul_exp_neg_pi_div_four_mul_I (ρ : ℝ) :
    ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))).re = ρ / Real.sqrt 2 := by
  rw [← conj_exp_pi_div_four_mul_I_mul_ofReal, Complex.conj_re,
    re_exp_pi_div_four_mul_I_mul_ofReal]

/-- The ordinate of a point of the ray. -/
theorem im_ofReal_mul_exp_neg_pi_div_four_mul_I (ρ : ℝ) :
    ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))).im = -(ρ / Real.sqrt 2) := by
  rw [mul_comm, Complex.exp_neg_pi_div_four_mul_I_mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Real.sqrt_div_self']
  ring

/-- The ray misses the integers, away from the origin. -/
theorem ofReal_mul_exp_neg_pi_div_four_mul_I_ne_intCast {ρ : ℝ} (hρ : 0 < ρ) (n : ℤ) :
    (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) ≠ (n : ℂ) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  intro h
  have him := im_ofReal_mul_exp_neg_pi_div_four_mul_I ρ
  rw [h, Complex.intCast_im] at him
  have : 0 < ρ / Real.sqrt 2 := div_pos hρ h2
  linarith

/-- The ray lies in the slit plane, away from the origin. -/
theorem ofReal_mul_exp_neg_pi_div_four_mul_I_mem_slitPlane {ρ : ℝ} (hρ : 0 < ρ) :
    (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inl (by
    rw [re_ofReal_mul_exp_neg_pi_div_four_mul_I]
    exact div_pos hρ (Real.sqrt_pos.2 two_pos)))

/-- The ray integrand in polar form: the ray contributes the constant phase `e^{iπs/4}`. -/
theorem rayIntegrand_eq (f : ℂ → ℂ) (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    rayIntegrand f s ρ
      = (ρ : ℂ) ^ (-s) * exp ((π / 4 : ℝ) * I * s) * f ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) := by
  have hpi := Real.pi_pos
  have hcpow : ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ (-s)
      = (ρ : ℂ) ^ (-s) * exp ((π / 4 : ℝ) * I * s) := by
    rw [show -(((π / 4 : ℝ) : ℂ) * I) = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.ofReal_mul_exp_mul_I_cpow hρ (by linarith) (by linarith) (-s),
      show ((-(π / 4) : ℝ) : ℂ) * I * (-s) = ((π / 4 : ℝ) : ℂ) * I * s by push_cast; ring]
  rw [rayIntegrand, hcpow]

/-- The modulus of the ray integrand. -/
theorem norm_rayIntegrand (f : ℂ → ℂ) (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖rayIntegrand f s ρ‖
      = ρ ^ (-s.re) * Real.exp (-(π / 4 * s.im)) *
          ‖f ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))‖ := by
  rw [rayIntegrand_eq f s hρ, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hρ,
    Complex.norm_exp, Complex.neg_re,
    show (((π / 4 : ℝ) : ℂ) * I * s).re = -(π / 4 * s.im) by
      simp [Complex.mul_re, Complex.mul_im]]

/-- The ray integral depends only on the values on the ray. -/
theorem rayIntegral_congr {f g : ℂ → ℂ} {s : ℂ}
    (h : ∀ ρ : ℝ, 0 < ρ → f ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))
      = g ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))) :
    rayIntegral f s = rayIntegral g s := by
  rw [rayIntegral, rayIntegral]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ by
    rw [rayIntegrand, rayIntegrand, h ρ hρ]

/-- The ray integral is additive, given absolute convergence of both summands. -/
theorem rayIntegral_add {f g : ℂ → ℂ} {s : ℂ} (hf : IntegrableOn (rayIntegrand f s) (Ioi 0))
    (hg : IntegrableOn (rayIntegrand g s) (Ioi 0)) :
    rayIntegral (fun u ↦ f u + g u) s = rayIntegral f s + rayIntegral g s := by
  rw [rayIntegral, rayIntegral, rayIntegral, ← mul_add, ← integral_add hf hg]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun ρ _ ↦ by
    rw [rayIntegrand, rayIntegrand, rayIntegrand, mul_add]

/-! ### The Mellin transform of an exponential -/

/-- The ray integrand of an exponential, with the rate `2π e^{iπ/4} z` split off. -/
private theorem rayIntegrand_exp_eq (s z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    rayIntegrand (fun u ↦ exp (-(2 * π * I * u * z))) s ρ
      = exp ((π / 4 : ℝ) * I * s) *
          ((ρ : ℂ) ^ (-s) * exp (-(((2 * π : ℝ) : ℂ) * (exp ((π / 4 : ℝ) * I) * z) * ρ))) := by
  rw [rayIntegrand_eq _ s hρ,
    show -(2 * (π : ℂ) * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) * z)
      = -(((2 * π : ℝ) : ℂ) * (exp ((π / 4 : ℝ) * I) * z) * ρ) by
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
      linear_combination (-(2 * (π : ℂ) * (ρ : ℂ) * z)) *
        Complex.I_mul_exp_neg_pi_div_four_mul_I]
  ring

/-- The modulus of the ray integrand of an exponential. -/
private theorem norm_rayIntegrand_exp (s z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖rayIntegrand (fun u ↦ exp (-(2 * π * I * u * z))) s ρ‖
      = Real.exp (-(π / 4 * s.im)) *
          (ρ ^ (-s.re) * Real.exp (-(2 * π * (exp ((π / 4 : ℝ) * I) * z).re * ρ))) := by
  rw [rayIntegrand_exp_eq s z hρ, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
    Complex.norm_cpow_eq_rpow_re_of_pos hρ, Complex.neg_re,
    show (((π / 4 : ℝ) : ℂ) * I * s).re = -(π / 4 * s.im) by
      simp [Complex.mul_re, Complex.mul_im],
    show (-(((2 * π : ℝ) : ℂ) * (exp ((π / 4 : ℝ) * I) * z) * (ρ : ℂ))).re
      = -(2 * π * (exp ((π / 4 : ℝ) * I) * z).re * ρ) by
      rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.re_ofReal_mul]]

/-- The rate attached to the exponential has positive real part. -/
private theorem re_ofReal_two_pi_mul_pos {z : ℂ} (hz : 0 < (exp ((π / 4 : ℝ) * I) * z).re) :
    0 < (((2 * π : ℝ) : ℂ) * (exp ((π / 4 : ℝ) * I) * z)).re := by
  rw [Complex.re_ofReal_mul]
  exact mul_pos (by positivity) hz

/-- Absolute convergence of the ray integral of an exponential. -/
theorem integrableOn_rayIntegrand_exp_neg_two_pi_mul_I_mul {s z : ℂ} (hs : s.re < 1)
    (hz : 0 < (exp ((π / 4 : ℝ) * I) * z).re) :
    IntegrableOn (rayIntegrand (fun u ↦ exp (-(2 * π * I * u * z))) s) (Ioi 0) := by
  have ha : 0 < (1 - s).re := by simpa using hs
  have hb := re_ofReal_two_pi_mul_pos hz
  refine IntegrableOn.congr_fun ((Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi ha hb).const_mul
    (exp ((π / 4 : ℝ) * I * s))) (fun ρ hρ ↦ ?_) measurableSet_Ioi
  rw [rayIntegrand_exp_eq s z hρ, show (1 : ℂ) - s - 1 = -s by ring]

/-- The Mellin transform of an exponential along the ray: the power on the right is taken in
the slanted branch `Zeta.RiemannSiegel.slantCpow`. -/
theorem rayIntegral_exp_neg_two_pi_mul_I_mul {s z : ℂ} (hs : s.re < 1)
    (hz : 0 < (exp ((π / 4 : ℝ) * I) * z).re) :
    rayIntegral (fun u ↦ exp (-(2 * π * I * u * z))) s
      = ((2 * π : ℝ) : ℂ) ^ (s - 1) * exp ((π / 2 : ℝ) * I * (s - 1)) * Gamma (1 - s) *
          slantCpow z (s - 1) := by
  have hz0 : exp ((π / 4 : ℝ) * I) * z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hb := re_ofReal_two_pi_mul_pos hz
  have hint : ∫ ρ in Ioi (0 : ℝ), rayIntegrand (fun u ↦ exp (-(2 * π * I * u * z))) s ρ
      = exp ((π / 4 : ℝ) * I * s) *
          (Gamma (1 - s) * (((2 * π : ℝ) : ℂ) * (exp ((π / 4 : ℝ) * I) * z)) ^ (s - 1)) := by
    rw [← Complex.integral_cpow_neg_mul_exp_neg_mul_Ioi hs hb, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ rayIntegrand_exp_eq s z hρ
  have hph : exp (-((π / 4 : ℝ) * I)) * exp ((π / 4 : ℝ) * I * s)
      = exp ((π / 2 : ℝ) * I * (s - 1)) * exp (-((π / 4 : ℝ) * I * (s - 1))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [rayIntegral, hint, Complex.ofReal_mul_cpow (by positivity) hz0, slantCpow]
  linear_combination (Gamma (1 - s) * ((2 * π : ℝ) : ℂ) ^ (s - 1) *
    (exp ((π / 4 : ℝ) * I) * z) ^ (s - 1)) * hph

/-! ### The geometric term -/

/-- The geometric factor factors through the kernel's denominator along the ray. -/
private theorem one_sub_exp_two_pi_mul_I_mul_eq (u : ℂ) :
    1 - exp (2 * π * I * u) = -(exp (π * I * u) * (2 * I * sin (π * u))) := by
  rw [show (2 : ℂ) * I * sin ((π : ℂ) * u) = exp ((π : ℂ) * u * I) - exp (-((π : ℂ) * u * I)) from
    (Complex.exp_mul_I_sub_exp_neg_mul_I _).symm, mul_sub, ← Complex.exp_add, ← Complex.exp_add]
  rw [show (π : ℂ) * I * u + (π : ℂ) * u * I = 2 * π * I * u by ring,
    show (π : ℂ) * I * u + -((π : ℂ) * u * I) = 0 by ring, Complex.exp_zero]
  ring

/-- A lower bound for `1 - e^{2πiu}` along the ray. -/
private theorem le_norm_one_sub_exp_ray {ρ : ℝ} (hρ : 0 < ρ) :
    Real.sqrt 2 * π * ρ * Real.exp (π * ρ / Real.sqrt 2)
      ≤ ‖1 - exp (2 * π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))))‖ := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hpi := Real.pi_pos
  set u : ℂ := (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) with hu
  have him : ((π : ℂ) * u).im = -(π * ρ / Real.sqrt 2) := by
    rw [show (π : ℂ) * u = ((π : ℝ) : ℂ) * u by norm_cast, Complex.im_ofReal_mul, hu,
      im_ofReal_mul_exp_neg_pi_div_four_mul_I]
    ring
  have hexp : ‖exp ((π : ℂ) * I * u)‖ = Real.exp (π * ρ / Real.sqrt 2) := by
    rw [Complex.norm_exp, show ((π : ℂ) * I * u).re = -((π : ℂ) * u).im by
      simp [Complex.mul_re, Complex.mul_im], him, neg_neg]
  have hsin : π * ρ / Real.sqrt 2 ≤ ‖sin ((π : ℂ) * u)‖ := by
    refine le_trans (Real.self_le_sinh_iff.2 (by positivity)) ?_
    have h := Complex.sinh_abs_im_le_norm_sin ((π : ℂ) * u)
    rwa [him, abs_neg, abs_of_nonneg (by positivity)] at h
  have hval : 2 * (π * ρ / Real.sqrt 2) = Real.sqrt 2 * π * ρ := by
    rw [show 2 * (π * ρ / Real.sqrt 2) = 2 / Real.sqrt 2 * (π * ρ) by ring, Real.div_sqrt]; ring
  rw [one_sub_exp_two_pi_mul_I_mul_eq, norm_neg, norm_mul, hexp,
    show ‖(2 : ℂ) * I * sin ((π : ℂ) * u)‖ = 2 * ‖sin ((π : ℂ) * u)‖ by simp, ← hval]
  have := mul_le_mul_of_nonneg_left hsin (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [Real.exp_pos (π * ρ / Real.sqrt 2)]

/-- The ray integrand of the geometric factor is `O(ρ^{-Re s - 1} e^{-πρ/√2})`. -/
private theorem norm_rayIntegrand_inv_one_sub_exp_le (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖rayIntegrand (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s ρ‖
      ≤ Real.exp (-(π / 4 * s.im)) / (Real.sqrt 2 * π) *
          (ρ ^ (-s.re - 1) * Real.exp (-(π / Real.sqrt 2) * ρ)) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hpi := Real.pi_pos
  have hlb := le_norm_one_sub_exp_ray hρ
  rw [norm_rayIntegrand _ s hρ, norm_inv]
  calc ρ ^ (-s.re) * Real.exp (-(π / 4 * s.im)) *
        ‖1 - exp (2 * π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))))‖⁻¹
      ≤ ρ ^ (-s.re) * Real.exp (-(π / 4 * s.im)) *
        (Real.sqrt 2 * π * ρ * Real.exp (π * ρ / Real.sqrt 2))⁻¹ := by gcongr
    _ = Real.exp (-(π / 4 * s.im)) / (Real.sqrt 2 * π) *
        (ρ ^ (-s.re - 1) * Real.exp (-(π / Real.sqrt 2) * ρ)) := by
        rw [Real.rpow_sub hρ, Real.rpow_one, mul_inv, mul_inv,
          show -(π / Real.sqrt 2) * ρ = -(π * ρ / Real.sqrt 2) by ring,
          Real.exp_neg (π * ρ / Real.sqrt 2), div_eq_mul_inv, div_eq_mul_inv]
        ring

/-- Absolute convergence of the ray integral of the geometric factor, for `Re s < 0`. -/
theorem integrableOn_rayIntegrand_inv_one_sub_exp {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (rayIntegrand (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s) (Ioi 0) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hmaj : IntegrableOn (fun ρ : ℝ ↦ Real.exp (-(π / 4 * s.im)) / (Real.sqrt 2 * π) *
      (ρ ^ (-s.re - 1) * Real.exp (-(π / Real.sqrt 2) * ρ))) (Ioi 0) :=
    (Real.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)).const_mul _
  have hmeas : AEStronglyMeasurable
      (rayIntegrand (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s) (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (ContinuousOn.cpow (by fun_prop) continuousOn_const fun ρ hρ ↦ ?_)
      (ContinuousOn.inv₀ (by fun_prop) fun ρ hρ ↦ ?_)
    · exact ofReal_mul_exp_neg_pi_div_four_mul_I_mem_slitPlane hρ
    · have hρ0 : (0 : ℝ) < ρ := hρ
      exact norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (le_norm_one_sub_exp_ray hρ0))
  refine Integrable.mono' hmaj hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ using
    norm_rayIntegrand_inv_one_sub_exp_le s hρ

/-- The geometric expansion of the ray integrand. -/
private theorem tsum_rayIntegrand_exp (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∑' n : ℕ, rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ
      = -rayIntegrand (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s ρ := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  set x : ℂ := (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) with hxdef
  have hq : ‖exp (-(2 * (π : ℂ) * I * x))‖ < 1 := by
    rw [Complex.norm_exp,
      show (-(2 * (π : ℂ) * I * x)).re = 2 * π * x.im by simp [Complex.mul_re, Complex.mul_im],
      Real.exp_lt_one_iff, hxdef, im_ofReal_mul_exp_neg_pi_div_four_mul_I]
    nlinarith [Real.pi_pos, div_pos hρ h2]
  have hqne : exp (-(2 * (π : ℂ) * I * x)) ≠ 0 := Complex.exp_ne_zero _
  have hq0 : (1 : ℂ) - exp (-(2 * (π : ℂ) * I * x)) ≠ 0 :=
    sub_ne_zero_of_ne fun h ↦ by rw [← h] at hq; simp at hq
  have hterm : ∀ n : ℕ, rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ
      = x ^ (-s) * exp (-(2 * (π : ℂ) * I * x)) * exp (-(2 * (π : ℂ) * I * x)) ^ n := fun n ↦ by
    have h : exp (-(2 * (π : ℂ) * I * x)) * exp (-(2 * (π : ℂ) * I * x)) ^ n
        = exp (-(2 * (π : ℂ) * I * x * ((n : ℂ) + 1))) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    rw [rayIntegrand, ← hxdef, ← h, ← mul_assoc]
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hq, rayIntegrand, ← hxdef,
    show exp (2 * (π : ℂ) * I * x) = (exp (-(2 * (π : ℂ) * I * x)))⁻¹ by
      rw [← Complex.exp_neg]; ring_nf,
    show (1 : ℂ) - (exp (-(2 * (π : ℂ) * I * x)))⁻¹
      = -((1 - exp (-(2 * (π : ℂ) * I * x))) * (exp (-(2 * (π : ℂ) * I * x)))⁻¹) by
      field_simp; ring, inv_neg, mul_inv, inv_inv]
  ring

/-- The geometric term (`riemann_siegel_zero.tex`, `lem:rsz_ray_zeta`): for `Re s < 0`,
`𝓡(u ↦ 1/(1 - e^{2πiu}))(s) = -(2π)^{s-1} e^{iπ(s-1)/2} Γ(1-s) ζ(1-s)`. -/
theorem rayIntegral_inv_one_sub_exp {s : ℂ} (hs : s.re < 0) :
    rayIntegral (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s
      = -(((2 * π : ℝ) : ℂ) ^ (s - 1) * exp ((π / 2 : ℝ) * I * (s - 1)) * Gamma (1 - s) *
          riemannZeta (1 - s)) := by
  have hs1 : s.re < 1 := by linarith
  set C : ℂ := ((2 * π : ℝ) : ℂ) ^ (s - 1) * exp ((π / 2 : ℝ) * I * (s - 1)) * Gamma (1 - s)
    with hC
  -- the rotated rate at `z = n + 1` is positive
  have hzre : ∀ n : ℕ, 0 < (exp ((π / 4 : ℝ) * I) * ((n : ℂ) + 1)).re := fun n ↦ by
    rw [show ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring,
      re_exp_pi_div_four_mul_I_mul_ofReal]
    positivity
  -- each term of the series is a Dirichlet term
  have hval : ∀ n : ℕ, rayIntegral (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s
      = C * (((n : ℂ) + 1) ^ (s - 1)) := fun n ↦ by
    rw [rayIntegral_exp_neg_two_pi_mul_I_mul hs1 (hzre n),
      show ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring,
      slantCpow_ofReal (by positivity), hC]
  -- the sum of the Dirichlet terms is `ζ(1-s)`
  have h1 : 1 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hfe : ∀ n : ℕ, ((n : ℂ) + 1) ^ (s - 1) = 1 / ((n : ℂ) + 1) ^ (1 - s) := fun n ↦ by
    rw [one_div, ← Complex.cpow_neg, neg_sub]
  have hzeta : HasSum (fun n : ℕ ↦ ((n : ℂ) + 1) ^ (s - 1)) (riemannZeta (1 - s)) := by
    have hsum : Summable fun n : ℕ ↦ ((n : ℂ) + 1) ^ (s - 1) :=
      ((summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 h1)).congr fun n ↦ by
        rw [hfe]
        push_cast
        ring_nf
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1, ← tsum_congr hfe]
    exact hsum.hasSum
  -- term-by-term integration
  have hInt : ∀ n : ℕ, IntegrableOn
      (rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s) (Ioi 0) :=
    fun n ↦ integrableOn_rayIntegrand_exp_neg_two_pi_mul_I_mul hs1 (hzre n)
  have hnorm : ∀ (n : ℕ) (ρ : ℝ), 0 < ρ →
      ‖rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ‖
        = Real.exp (-(π / 4 * s.im)) *
            (ρ ^ (-s.re) * Real.exp (-(Real.sqrt 2 * π * ((n : ℝ) + 1) * ρ))) := fun n ρ hρ ↦ by
    rw [norm_rayIntegrand_exp s _ hρ,
      show ((n : ℂ) + 1) = ((((n : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring,
      re_exp_pi_div_four_mul_I_mul_ofReal,
      show 2 * π * (((n : ℝ) + 1) / Real.sqrt 2) * ρ
        = 2 / Real.sqrt 2 * (π * ((n : ℝ) + 1) * ρ) by ring, Real.div_sqrt]
    ring_nf
  have hSum : Summable fun n : ℕ ↦
      ∫ ρ in Ioi (0 : ℝ), ‖rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ‖ := by
    have hval2 : ∀ n : ℕ,
        (∫ ρ in Ioi (0 : ℝ),
          ‖rayIntegrand (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ‖)
          = Real.exp (-(π / 4 * s.im)) * (Real.Gamma (1 - s.re) *
              ((Real.sqrt 2 * π) ^ (s.re - 1) * ((n : ℝ) + 1) ^ (s.re - 1))) := fun n ↦ by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ ↦ hnorm n ρ hρ), integral_const_mul,
        Real.integral_rpow_neg_mul_exp_neg_mul_Ioi hs1 (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
    refine Summable.congr ?_ fun n ↦ (hval2 n).symm
    have hbase : Summable fun n : ℕ ↦ ((n : ℝ) + 1) ^ (s.re - 1) :=
      Summable.congr ((summable_nat_add_iff 1).2
        (Real.summable_nat_rpow.mpr (by linarith : s.re - 1 < -1))) fun n ↦ by push_cast; ring
    exact ((hbase.mul_left _).mul_left _).mul_left _
  have hleft : (exp (-((π / 4 : ℝ) * I)) *
      ∫ ρ in Ioi (0 : ℝ), ∑' n : ℕ, rayIntegrand
        (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s ρ)
      = -rayIntegral (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s := by
    rw [rayIntegral, ← mul_neg (exp (-((π / 4 : ℝ) * I))), ← integral_neg]
    exact congrArg _
      (setIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ tsum_rayIntegrand_exp s hρ)
  have hHS : HasSum (fun n : ℕ ↦ rayIntegral
      (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s)
      (-rayIntegral (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) s) := by
    have h := (hasSum_integral_of_summable_integral_norm
      (μ := volume.restrict (Ioi (0 : ℝ))) hInt hSum).mul_left (exp (-((π / 4 : ℝ) * I)))
    rwa [hleft] at h
  have hfin : HasSum (fun n : ℕ ↦ rayIntegral
      (fun u ↦ exp (-(2 * π * I * u * ((n : ℂ) + 1)))) s) (C * riemannZeta (1 - s)) := by
    simpa only [hval] using hzeta.mul_left C
  linear_combination -(hHS.unique hfin)

/-! ### The Gaussian term -/

/-- The ray integrand of the Gaussian factor is a constant multiple of the mirror Hankel ray
integrand. -/
private theorem rayIntegrand_mirrorKernel_eq (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    rayIntegrand (fun u ↦ exp (-(π * I * u ^ 2)) / (exp (π * I * u) - exp (-(π * I * u)))) s ρ
      = exp ((π / 4 : ℝ) * I * s) / (2 * I) * mirrorHankelIntegrand s ρ := by
  have hgauss : exp (-((π : ℂ) * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ 2))
      = exp (-((π : ℂ) * (ρ : ℂ) ^ 2)) := by
    congr 1
    linear_combination (-(π : ℂ) * I * (ρ : ℂ) ^ 2) * Complex.exp_neg_pi_div_four_mul_I_mul_self +
      ((π : ℂ) * (ρ : ℂ) ^ 2) * Complex.I_sq
  have hden : exp ((π : ℂ) * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))))
        - exp (-((π : ℂ) * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))))
      = 2 * I * sin ((π : ℂ) * (ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) := by
    rw [show (π : ℂ) * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))
        = (π : ℂ) * (ρ : ℂ) * exp (-((π / 4 : ℝ) * I)) * I by ring]
    exact Complex.exp_mul_I_sub_exp_neg_mul_I _
  rw [rayIntegrand_eq _ s hρ, hgauss, hden, mirrorHankelIntegrand]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- Absolute convergence of the ray integral of the Gaussian factor, for `Re s < 0`. -/
theorem integrableOn_rayIntegrand_mirrorKernel {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (rayIntegrand
      (fun u ↦ exp (-(π * I * u ^ 2)) / (exp (π * I * u) - exp (-(π * I * u)))) s) (Ioi 0) :=
  IntegrableOn.congr_fun ((integrableOn_mirrorHankelIntegrand hs).const_mul
    (exp ((π / 4 : ℝ) * I * s) / (2 * I)))
    (fun _ hρ ↦ (rayIntegrand_mirrorKernel_eq s hρ).symm) measurableSet_Ioi

/-- The Gaussian term (`riemann_siegel_zero.tex`, `lem:rsz_ray_hankel`):
`𝓡(u ↦ e^{-iπu²}/(e^{iπu} - e^{-iπu}))(s) = e^{iπ(s-1)/4} Φ̃(s) / (2i)`. -/
theorem rayIntegral_mirrorKernel (s : ℂ) :
    rayIntegral (fun u ↦ exp (-(π * I * u ^ 2)) / (exp (π * I * u) - exp (-(π * I * u)))) s
      = exp ((π / 4 : ℝ) * I * (s - 1)) / (2 * I) * mirrorHankelIntegral s := by
  have hph : exp ((π / 4 : ℝ) * I * (s - 1))
      = exp (-((π / 4 : ℝ) * I)) * exp ((π / 4 : ℝ) * I * s) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [rayIntegral, setIntegral_congr_fun measurableSet_Ioi
      (fun ρ hρ ↦ rayIntegrand_mirrorKernel_eq s hρ),
    -- off `Re s < 0` neither integral converges, and both sides are the junk value `0`
    integral_const_mul, ← mirrorHankelIntegral_eq_integral, hph]
  ring

/-! ### The contour term -/

/-- The double integrand of the contour term,
`(ρ, w) ↦ (ρω)^{-s} e^{-2πiρω L(½)(w)} G(L(½)(w))`. It is a `def` so that the Fubini hypothesis
`Integrable (Function.uncurry ·)` has a head symbol to unify against. -/
private noncomputable def contourRayIntegrand (s : ℂ) (ρ w : ℝ) : ℂ :=
  rayIntegrand (fun u ↦ exp (-(2 * π * I * u * line (1 / 2) w))) s ρ * kernel (line (1 / 2) w)

/-- The double integrand is dominated by a product of a function of `ρ` and one of `w`. -/
private theorem norm_contourRayIntegrand_le (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (w : ℝ) :
    ‖contourRayIntegrand s ρ w‖
      ≤ Real.exp (-(π / 4 * s.im)) * (ρ ^ (-s.re) * Real.exp (-(π / Real.sqrt 2) * ρ)) *
        (Real.exp (π / 4) * Real.sqrt 2 * Real.exp (-(π * w ^ 2))) := by
  have hconst : Real.exp (π / 4) / (Real.sqrt 2 * ((1 : ℝ) / 2))
      = Real.exp (π / 4) * Real.sqrt 2 := by
    rw [eq_comm, eq_div_iff (by positivity)]
    nlinarith [Real.exp_pos (π / 4), Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hk := norm_kernel_line_le (a := (1 : ℝ) / 2) (by norm_num) le_rfl w
  rw [show π * ((1 : ℝ) / 2) ^ 2 = π / 4 by ring, hconst] at hk
  rw [contourRayIntegrand, norm_mul, norm_rayIntegrand_exp s _ hρ,
    re_exp_pi_div_four_mul_I_mul_line,
    show -(2 * π * ((1 / 2 : ℝ) / Real.sqrt 2) * ρ) = -(π / Real.sqrt 2) * ρ by ring]
  exact mul_le_mul_of_nonneg_left hk
    (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.rpow_nonneg hρ.le _) (Real.exp_pos _).le))

/-- The double integrand is continuous on the open half-plane `{ρ > 0} × ℝ`. -/
private theorem continuousOn_uncurry_contourRayIntegrand (s : ℂ) :
    ContinuousOn (Function.uncurry (contourRayIntegrand s))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  have hlinew : Continuous (line (1 / 2)) := continuous_line (1 / 2)
  have hline : Continuous fun z : ℝ × ℝ ↦ line (1 / 2) z.2 := hlinew.comp continuous_snd
  have hpt : Continuous fun z : ℝ × ℝ ↦ ((z.1 : ℂ) * exp (-((π / 4 : ℝ) * I))) := by fun_prop
  have hker : Continuous fun w : ℝ ↦ kernel (line (1 / 2) w) := by
    simp only [kernel_eq_div_two_mul_I_mul_sin]
    exact Continuous.div (by fun_prop) (by fun_prop) fun w ↦ by
      simpa [Complex.I_ne_zero] using
        sin_pi_mul_line_ne_zero (a := (1 : ℝ) / 2) (n := 0) (by norm_num) w
  change ContinuousOn (fun z : ℝ × ℝ ↦ (((z.1 : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ (-s) *
      exp (-(2 * π * I * ((z.1 : ℂ) * exp (-((π / 4 : ℝ) * I))) * line (1 / 2) z.2)))
      * kernel (line (1 / 2) z.2)) _
  refine ContinuousOn.mul (ContinuousOn.mul
    (ContinuousOn.cpow hpt.continuousOn continuousOn_const fun z hz ↦ ?_)
    (Complex.continuous_exp.comp (((continuous_const.mul hpt).mul hline).neg)).continuousOn)
    (hker.comp continuous_snd).continuousOn
  exact ofReal_mul_exp_neg_pi_div_four_mul_I_mem_slitPlane hz.1

/-- The contour term (`riemann_siegel_zero.tex`, `lem:rsz_ray_contour`): for `Re s < 0`,
`𝓡(N)(s) = (2π)^{s-1} e^{iπ(s-1)/2} Γ(1-s) I(1-s, ½)`. -/
theorem rayIntegral_mordellIntegral {s : ℂ} (hs : s.re < 0) :
    rayIntegral (fun u ↦ mordellIntegral u (1 / 2)) s
      = ((2 * π : ℝ) : ℂ) ^ (s - 1) * exp ((π / 2 : ℝ) * I * (s - 1)) * Gamma (1 - s) *
          contourIntegral (1 - s) (1 / 2) := by
  have hpi := Real.pi_pos
  have hs1 : s.re < 1 := by linarith
  -- absolute convergence of the double integral
  have hfub : Integrable (Function.uncurry (contourRayIntegrand s))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hAint : IntegrableOn (fun ρ : ℝ ↦ Real.exp (-(π / 4 * s.im)) *
        (ρ ^ (-s.re) * Real.exp (-(π / Real.sqrt 2) * ρ))) (Ioi 0) :=
      (Real.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)).const_mul _
    have hBint : Integrable fun w : ℝ ↦
        Real.exp (π / 4) * Real.sqrt 2 * Real.exp (-(π * w ^ 2)) := by
      simpa [neg_mul] using
        (integrable_exp_neg_mul_sq hpi).const_mul (Real.exp (π / 4) * Real.sqrt 2)
    refine Integrable.mono' (hAint.mul_prod hBint) ?_ ?_
    · rw [Measure.restrict_prod_eq_prod_univ]
      exact (continuousOn_uncurry_contourRayIntegrand s).aestronglyMeasurable
        (measurableSet_Ioi.prod MeasurableSet.univ)
    · rw [Measure.restrict_prod_eq_prod_univ]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with z hz
      exact norm_contourRayIntegrand_le s hz.1 z.2
  -- the row integral is the Mordell integral, the constant power pulled inside
  have hrow : ∀ ρ : ℝ, rayIntegrand (fun u ↦ mordellIntegral u (1 / 2)) s ρ
      = (1 + I) * ∫ w : ℝ, contourRayIntegrand s ρ w := fun ρ ↦ by
    have heq : ∀ w : ℝ, contourRayIntegrand s ρ w
        = ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ (-s) *
            mordellIntegrand ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) (line (1 / 2) w) := fun w ↦ by
      rw [contourRayIntegrand, rayIntegrand, mordellIntegrand]
      ring
    rw [integral_congr_ae (.of_forall heq), integral_const_mul, rayIntegrand, mordellIntegral,
      slantIntegral]
    ring
  -- the column integral is the Riemann–Siegel integrand, by the workhorse
  have hcol : ∀ w : ℝ, exp (-((π / 4 : ℝ) * I)) * ∫ ρ in Ioi (0 : ℝ), contourRayIntegrand s ρ w
      = ((2 * π : ℝ) : ℂ) ^ (s - 1) * exp ((π / 2 : ℝ) * I * (s - 1)) * Gamma (1 - s) *
          contourIntegrand (1 - s) (1 / 2) w := fun w ↦ by
    have hzre : 0 < (exp ((π / 4 : ℝ) * I) * line (1 / 2) w).re := by
      rw [re_exp_pi_div_four_mul_I_mul_line]
      positivity
    rw [show (∫ ρ in Ioi (0 : ℝ), contourRayIntegrand s ρ w)
        = (∫ ρ in Ioi (0 : ℝ), rayIntegrand
            (fun u ↦ exp (-(2 * π * I * u * line (1 / 2) w))) s ρ) * kernel (line (1 / 2) w) from
      integral_mul_const _ _, ← mul_assoc, ← rayIntegral,
      rayIntegral_exp_neg_two_pi_mul_I_mul hs1 hzre, contourIntegrand, integrand,
      show -(1 - s) = s - 1 by ring]
    ring
  rw [rayIntegral, setIntegral_congr_fun measurableSet_Ioi (fun ρ _ ↦ hrow ρ),
    integral_const_mul, integral_integral_swap hfub,
    show exp (-((π / 4 : ℝ) * I)) *
        ((1 + I) * ∫ w : ℝ, ∫ ρ in Ioi (0 : ℝ), contourRayIntegrand s ρ w)
      = (1 + I) * (exp (-((π / 4 : ℝ) * I)) *
          ∫ w : ℝ, ∫ ρ in Ioi (0 : ℝ), contourRayIntegrand s ρ w) by ring,
    ← integral_const_mul, integral_congr_ae (.of_forall hcol), integral_const_mul,
    contourIntegral]
  ring

/-! ### The Mellin form of Siegel's identity -/

/-- The Mordell integral splits along the ray into a geometric part and a Gaussian part. -/
private theorem mordellIntegral_ray_eq {ρ : ℝ} (hρ : 0 < ρ) :
    mordellIntegral ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) (1 / 2)
      = (1 - exp (2 * π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))))⁻¹
        + exp (-(π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ 2)) /
            (exp (π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))))
              - exp (-(π * I * ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))))))  := by
  set u : ℂ := (ρ : ℂ) * exp (-((π / 4 : ℝ) * I))
  have hun : ∀ n : ℤ, u ≠ (n : ℂ) := ofReal_mul_exp_neg_pi_div_four_mul_I_ne_intCast hρ
  have hE : exp ((π : ℂ) * I * u) ≠ 0 := Complex.exp_ne_zero _
  have hsin : exp ((π : ℂ) * I * u) - exp (-((π : ℂ) * I * u)) = 2 * I * sin ((π : ℂ) * u) := by
    rw [show (π : ℂ) * I * u = (π : ℂ) * u * I by ring]
    exact Complex.exp_mul_I_sub_exp_neg_mul_I _
  have hD : exp ((π : ℂ) * I * u) - exp (-((π : ℂ) * I * u)) ≠ 0 := by
    rw [hsin]
    simpa [Complex.I_ne_zero] using Complex.sin_pi_mul_ne_zero hun
  have hone : (1 : ℂ) - exp (2 * (π : ℂ) * I * u)
      = -(exp ((π : ℂ) * I * u) * (exp ((π : ℂ) * I * u) - exp (-((π : ℂ) * I * u)))) := by
    rw [hsin, one_sub_exp_two_pi_mul_I_mul_eq]
  have hinv : exp ((π : ℂ) * I * u) * exp (-((π : ℂ) * I * u)) = 1 := by
    rw [← Complex.exp_add, show (π : ℂ) * I * u + -((π : ℂ) * I * u) = 0 by ring, Complex.exp_zero]
  rw [mordellIntegral_eq hun, hone]
  field_simp
  linear_combination -hinv

/-- The Mellin form of Siegel's identity (`riemann_siegel_zero.tex`, `thm:rsz_mellin`): for
`Re s > 1`, `ζ(s) + I(s, ½) = (2π)^s e^{-iπ(2-s)/4} Φ̃(1-s) / (2 Γ(s))`. -/
theorem riemannZeta_add_contourIntegral_half_eq {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s + contourIntegral s (1 / 2)
      = ((2 * π : ℝ) : ℂ) ^ s * exp (-((π / 4 : ℝ) * I * (2 - s))) / (2 * Gamma s) *
          mirrorHankelIntegral (1 - s) := by
  have ht : (1 - s).re < 0 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have h2π : ((2 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hΓ : Gamma s ≠ 0 := Complex.Gamma_ne_zero fun m h ↦ by
    rw [h] at hs
    simp only [Complex.neg_re, Complex.natCast_re] at hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hPQ : ((2 * π : ℝ) : ℂ) ^ ((1 - s) - 1) * ((2 * π : ℝ) : ℂ) ^ s = 1 := by
    rw [← Complex.cpow_add _ _ h2π, show (1 - s) - 1 + s = 0 by ring, Complex.cpow_zero]
  -- the raw identity at `1 - s`
  have hsplit : rayIntegral (fun u ↦ mordellIntegral u (1 / 2)) (1 - s)
      = rayIntegral (fun u ↦ (1 - exp (2 * π * I * u))⁻¹) (1 - s)
        + rayIntegral (fun u ↦ exp (-(π * I * u ^ 2)) /
            (exp (π * I * u) - exp (-(π * I * u)))) (1 - s) := by
    rw [← rayIntegral_add (integrableOn_rayIntegrand_inv_one_sub_exp ht)
      (integrableOn_rayIntegrand_mirrorKernel ht)]
    exact rayIntegral_congr fun ρ hρ ↦ mordellIntegral_ray_eq hρ
  rw [rayIntegral_mordellIntegral ht, rayIntegral_inv_one_sub_exp ht,
    rayIntegral_mirrorKernel (1 - s), show (1 : ℂ) - (1 - s) = s by ring] at hsplit
  -- the phase bookkeeping
  have hph : I * exp ((π / 2 : ℝ) * I * ((1 - s) - 1)) * exp (-((π / 4 : ℝ) * I * (2 - s)))
      = exp ((π / 4 : ℝ) * I * ((1 - s) - 1)) := by
    rw [mul_assoc, ← Complex.exp_add,
      show ((π / 2 : ℝ) : ℂ) * I * ((1 - s) - 1) + -(((π / 4 : ℝ) : ℂ) * I * (2 - s))
        = -((π : ℂ) / 2 * I) + ((π / 4 : ℝ) : ℂ) * I * ((1 - s) - 1) by push_cast; ring,
      Complex.exp_add, ← mul_assoc, Complex.exp_neg, Complex.exp_pi_div_two_mul_I,
      mul_inv_cancel₀ Complex.I_ne_zero, one_mul]
  have hfrac : exp ((π / 4 : ℝ) * I * ((1 - s) - 1)) / (2 * I)
      = exp ((π / 2 : ℝ) * I * ((1 - s) - 1)) * exp (-((π / 4 : ℝ) * I * (2 - s))) / 2 := by
    rw [← hph]
    field_simp
  have hPne : ((2 * π : ℝ) : ℂ) ^ ((1 - s) - 1) ≠ 0 := by simp [Complex.cpow_eq_zero_iff]
  -- name the four transcendental factors, so that `field_simp` cannot reassociate inside them
  set P : ℂ := ((2 * π : ℝ) : ℂ) ^ ((1 - s) - 1)
  set Q : ℂ := ((2 * π : ℝ) : ℂ) ^ s
  set E : ℂ := exp ((π / 2 : ℝ) * I * ((1 - s) - 1))
  set F : ℂ := exp (-((π / 4 : ℝ) * I * (2 - s)))
  -- divide by the nonvanishing prefactor `P E Γ(s)`
  refine mul_left_cancel₀ (a := P * E * Gamma s)
    (mul_ne_zero (mul_ne_zero hPne (Complex.exp_ne_zero _)) hΓ) ?_
  rw [mul_add, hsplit, hfrac]
  field_simp
  linear_combination (-(E * F * mirrorHankelIntegral (1 - s))) * hPQ

end Zeta.RiemannSiegel
