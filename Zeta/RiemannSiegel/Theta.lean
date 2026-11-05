/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Analysis.SpecialFunctions.Arctan
public import Zeta.RiemannSiegel.Saddle
public import Zeta.Zeros.HardyZ

/-!
# The leading Stirling form of the Riemann–Siegel theta function

The saddle-point reduction of `Zeta/RiemannSiegel/FirstOrder.lean` produces the *Stirling* phase
`ϑ(t) = (t/2) log (t/2π) - t/2 - π/8` (`Zeta.RiemannSiegel.leadingTheta`), whereas the exact
Riemann–Siegel formula produces the true `θ = riemannSiegelTheta`. This file quantifies the
difference (`riemann_siegel_first.tex`, `lem:rsf_theta`).

The error splits into two *independent* contributions at `w_t = ¼ + it/2`, and both must be
bounded, since the order-`2` Stirling polynomial itself contributes at orders `t^{-1}` and
`t^{-3}`:

* the elementary part `Im S_2(w_t) - (t/2) log π - ϑ(t)`, whose expansion begins `1/(48t)` —
  note that `Re w_t = ¼` also contributes at order `t^{-1}` (for instance
  `Im 1/(12 w_t) = -(t/2)/(12‖w_t‖²)` is *not* `-1/(6t)`), so every such contribution is
  collected before any estimate is made;
* the remainder `Im ρ_2(w_t)`, controlled by the `‖·‖`-form
  `Complex.Stirling.norm_logGammaRemainderIoi_le'`. The project's
  `riemannSiegelThetaStirlingErrorBound` records the weaker `(¼+N)^{-2M}` form, which uses only
  `Re w_t` and is therefore bounded in `t`.

Both halves hold for every `t > 0`, so the sharp estimate carries no threshold; the two forms that
do carry one (`t ≥ 32π` and `t ≥ 10³`) are deduced from it.

## Main results

* `Zeta.RiemannSiegel.abs_riemannSiegelTheta_sub_leading_sub_inv_le`
  (`riemann_siegel_first.tex`, `lem:rsf_theta_sharp`):
  `|θ(t) - ϑ(t) - 1/(48t)| ≤ 319/(2880t³) + 12/t⁴` for every `t > 0`, which is what pins the
  coefficient of `t^{-1}`;
* `Zeta.RiemannSiegel.abs_riemannSiegelTheta_sub_leading_le'`: `|θ(t) - ϑ(t)| ≤ 101/(4800t)` for
  `t ≥ 32π`, the threshold at which the sharp first-order formula applies it;
* `Zeta.RiemannSiegel.abs_riemannSiegelTheta_sub_leading_le`
  (`riemann_siegel_first.tex`, `lem:rsf_theta`): `|θ(t) - ϑ(t)| ≤ 1/(40t)` for `t ≥ 10³`.
-/
@[expose] public section


open Complex Complex.Stirling

open scoped Nat Real

namespace Zeta.RiemannSiegel

-- A `def` rather than an `abbrev` deliberately: the estimates below drive `simp only`, `norm_num`
-- and `positivity` at goals mentioning `w_t`, and they stay legible only while `w_t` is an atom.
/-- The **Stirling argument** `w_t = ¼ + i t/2` of the Riemann–Siegel theta function. -/
private noncomputable def thetaArg (t : ℝ) : ℂ := 1 / 4 + Complex.I * (t / 2)

private theorem thetaArg_re (t : ℝ) : (thetaArg t).re = 1 / 4 := by simp [thetaArg]

private theorem thetaArg_im (t : ℝ) : (thetaArg t).im = t / 2 := by simp [thetaArg]

private theorem normSq_thetaArg (t : ℝ) :
    Complex.normSq (thetaArg t) = 1 / 16 + t ^ 2 / 4 := by
  rw [Complex.normSq_apply, thetaArg_re, thetaArg_im]; ring

private theorem norm_thetaArg (t : ℝ) : ‖thetaArg t‖ = Real.sqrt (1 / 16 + t ^ 2 / 4) := by
  rw [← Real.sqrt_sq (norm_nonneg (thetaArg t)), Complex.sq_norm, normSq_thetaArg]

private theorem half_le_norm_thetaArg {t : ℝ} (ht : 0 ≤ t) : t / 2 ≤ ‖thetaArg t‖ := by
  have h := Complex.abs_im_le_norm (thetaArg t)
  rwa [thetaArg_im, abs_of_nonneg (by linarith)] at h

/-! ### The four elementary contributions

Each term of `Im S_2(w_t) - (t/2) log π - ϑ(t)` is pinned to its leading order with an `O(t^{-3})`
error. The leading terms `1/(16t)`, `1/(8t)`, `-1/(6t)` and `0` sum to `1/(48t)`. -/

/-- The logarithmic term, `(t/2)(log ‖w_t‖ - log (t/2)) = 1/(16t) + O(t^{-3})`. -/
private theorem abs_mul_log_norm_thetaArg_sub_le {t : ℝ} (ht : 0 < t) :
    |t / 2 * (Real.log ‖thetaArg t‖ - Real.log (t / 2)) - 1 / (16 * t)| ≤ 1 / (64 * t ^ 3) := by
  have htne : t ≠ 0 := ht.ne'
  set x : ℝ := 1 / (4 * t ^ 2) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  -- `‖w_t‖/(t/2) = √(1 + x)`, so the logarithmic difference is `(log (1 + x))/2`
  have hkey : Real.log ‖thetaArg t‖ - Real.log (t / 2) = Real.log (1 + x) / 2 := by
    have hq : (1 / 16 + t ^ 2 / 4) / ((t / 2) ^ 2) = 1 + x := by rw [hx]; field_simp; ring
    rw [norm_thetaArg, show t / 2 = Real.sqrt ((t / 2) ^ 2) from (Real.sqrt_sq (by linarith)).symm,
      Real.log_sqrt (by positivity), Real.log_sqrt (by positivity), ← sub_div,
      ← Real.log_div (by positivity) (pow_pos (by linarith : (0 : ℝ) < t / 2) 2).ne', hq]
  -- `x - x² ≤ log (1 + x) ≤ x`
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hup : Real.log (1 + x) ≤ x := by linarith [Real.log_le_sub_one_of_pos h1x]
  have hlow : x - x ^ 2 ≤ Real.log (1 + x) := by
    have hb : (1 + x)⁻¹ ≤ 1 - x + x ^ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ h1x]
      nlinarith [pow_nonneg hx0.le 3]
    linarith [Real.one_sub_inv_le_log_of_pos h1x]
  have hval1 : t / 4 * (x - x ^ 2) = 1 / (16 * t) - 1 / (64 * t ^ 3) := by
    rw [hx]; field_simp; ring
  have hval2 : t / 4 * x = 1 / (16 * t) := by rw [hx]; field_simp; ring
  rw [hkey, show t / 2 * (Real.log (1 + x) / 2) = t / 4 * Real.log (1 + x) by ring, abs_le]
  constructor <;>
    linarith [mul_le_mul_of_nonneg_left hlow (by linarith : (0 : ℝ) ≤ t / 4),
      mul_le_mul_of_nonneg_left hup (by linarith : (0 : ℝ) ≤ t / 4),
      (by positivity : (0 : ℝ) ≤ 1 / (64 * t ^ 3))]

/-- The argument term, `π/8 - (arg w_t)/4 = 1/(8t) + O(t^{-3})`. -/
private theorem abs_arg_thetaArg_sub_le {t : ℝ} (ht : 0 < t) :
    |π / 8 - Complex.arg (thetaArg t) / 4 - 1 / (8 * t)| ≤ 1 / (32 * t ^ 3) := by
  have htne : t ≠ 0 := ht.ne'
  have hy0 : (0 : ℝ) < (2 * t)⁻¹ := by positivity
  -- `arg w_t = arctan (2t) = π/2 - arctan (2t)⁻¹`, so the term is `(arctan (2t)⁻¹)/4`
  have harg : Complex.arg (thetaArg t) = Real.arctan (2 * t) := by
    rw [Complex.arg_eq_arctan (by rw [thetaArg_re]; norm_num), thetaArg_re, thetaArg_im]
    congr 1; ring
  have hG : π / 8 - Complex.arg (thetaArg t) / 4 = Real.arctan (2 * t)⁻¹ / 4 := by
    rw [harg, Real.arctan_inv_of_pos (by linarith : (0 : ℝ) < 2 * t)]; ring
  -- `y - y³ ≤ arctan y ≤ y` at `y = (2t)⁻¹`
  have hup : Real.arctan (2 * t)⁻¹ ≤ (2 * t)⁻¹ := Real.arctan_le_self hy0.le
  have hlow : (2 * t)⁻¹ - ((2 * t)⁻¹) ^ 3 ≤ Real.arctan (2 * t)⁻¹ := by
    refine le_trans ?_ (Real.div_one_add_sq_le_arctan hy0.le)
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_nonneg hy0.le 5]
  have hval1 : (2 * t)⁻¹ / 4 = 1 / (8 * t) := by field_simp; ring
  have hval2 : ((2 * t)⁻¹) ^ 3 / 4 = 1 / (32 * t ^ 3) := by field_simp; ring
  rw [hG, abs_le]
  constructor <;> linarith [(by positivity : (0 : ℝ) ≤ 1 / (32 * t ^ 3))]

/-- The first Bernoulli term, `Im (1/(12 w_t)) = -1/(6t) + O(t^{-3})`. The shift `Re w_t = ¼`
matters: the exact value is `-(t/2)/(12‖w_t‖²)`, not `-1/(6t)`. -/
private theorem abs_im_inv_thetaArg_sub_le {t : ℝ} (ht : 0 < t) :
    |(1 / 12 * (thetaArg t)⁻¹).im + 1 / (6 * t)| ≤ 1 / (24 * t ^ 3) := by
  have htne : t ≠ 0 := ht.ne'
  have him : (1 / 12 * (thetaArg t)⁻¹).im = -(t / 2) / (12 * (1 / 16 + t ^ 2 / 4)) := by
    rw [show (1 : ℂ) / 12 = ((1 / 12 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul,
      Complex.inv_im, normSq_thetaArg, thetaArg_im]
    field_simp
  rw [him, show -(t / 2) / (12 * (1 / 16 + t ^ 2 / 4)) + 1 / (6 * t)
      = 1 / (96 * t * (1 / 16 + t ^ 2 / 4)) from by field_simp; ring,
    abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [ht]

/-- The second Bernoulli term is already `O(t^{-3})`: `|Im (1/(360 w_t³))| ≤ 1/(45t³)`. -/
private theorem abs_im_inv_thetaArg_cube_le {t : ℝ} (ht : 0 < t) :
    |(1 / 360 * ((thetaArg t) ^ 3)⁻¹).im| ≤ 1 / (45 * t ^ 3) := by
  have htne : t ≠ 0 := ht.ne'
  have hn : t / 2 ≤ ‖thetaArg t‖ := half_le_norm_thetaArg ht.le
  calc |(1 / 360 * ((thetaArg t) ^ 3)⁻¹).im|
      ≤ ‖(1 / 360 * ((thetaArg t) ^ 3)⁻¹ : ℂ)‖ := Complex.abs_im_le_norm _
    _ = 1 / 360 / ‖thetaArg t‖ ^ 3 := by
        rw [norm_mul, norm_inv, norm_pow, show ‖(1 / 360 : ℂ)‖ = 1 / 360 by norm_num]
        ring
    _ ≤ 1 / 360 / (t / 2) ^ 3 :=
        div_le_div_of_nonneg_left (by norm_num) (pow_pos (by linarith) 3)
          (pow_le_pow_left₀ (by linarith) hn 3)
    _ = 1 / (45 * t ^ 3) := by field_simp; ring

/-! ### The elementary half of the theta estimate

The remainder half is `abs_riemannSiegelTheta_sub_approximant_two_le`, in `Zeta/Zeros/HardyZ.lean`.
-/

/-- **The elementary half** of the theta estimate (`riemann_siegel_first.tex`,
`lem:rsf_theta_sharp`, step (i)): the four centred errors of the order-`2` Stirling polynomial,
around the exact leading value `1/(16t) + 1/(8t) - 1/(6t) = 1/(48t)`. -/
private theorem abs_im_logGammaStirling_two_sub_leading_sub_inv_le {t : ℝ} (ht : 0 < t) :
    |(logGammaStirling 2 (thetaArg t)).im - t / 2 * Real.log π - leadingTheta t - 1 / (48 * t)|
      ≤ 319 / (2880 * t ^ 3) := by
  have htne : t ≠ 0 := ht.ne'
  -- expand the order-2 Stirling polynomial at `w_t`, leaving the two Bernoulli terms folded
  have h1 : ((thetaArg t - 1 / 2) * Complex.log (thetaArg t)).im
      = t / 2 * Real.log ‖thetaArg t‖ - Complex.arg (thetaArg t) / 4 := by
    rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.mul_im, Complex.log_re,
      Complex.log_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      thetaArg_re, thetaArg_im]
    ring
  have h2 : ((1 / 2 : ℂ) * ((Real.log (2 * π) : ℝ) : ℂ)).im = 0 := by simp
  have hexp : (logGammaStirling 2 (thetaArg t)).im
      = t / 2 * Real.log ‖thetaArg t‖ - Complex.arg (thetaArg t) / 4 - t / 2
        + (1 / 12 * (thetaArg t)⁻¹).im - (1 / 360 * ((thetaArg t) ^ 3)⁻¹).im := by
    rw [logGammaStirling_two]
    simp only [Complex.sub_im, Complex.add_im]
    rw [h1, h2, thetaArg_im]
    ring
  have hleading : leadingTheta t
      = t / 2 * Real.log (t / 2) - t / 2 * Real.log π - t / 2 - π / 8 := by
    rw [leadingTheta, show t / (2 * π) = t / 2 / π by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
    ring
  -- the leading terms `1/(16t) + 1/(8t) - 1/(6t) = 1/(48t)` are all that survives against `ϑ`
  have hid : (logGammaStirling 2 (thetaArg t)).im - t / 2 * Real.log π - leadingTheta t
        - 1 / (48 * t)
      = (t / 2 * (Real.log ‖thetaArg t‖ - Real.log (t / 2)) - 1 / (16 * t))
        + (π / 8 - Complex.arg (thetaArg t) / 4 - 1 / (8 * t))
        + ((1 / 12 * (thetaArg t)⁻¹).im + 1 / (6 * t))
        - (1 / 360 * ((thetaArg t) ^ 3)⁻¹).im := by
    rw [hexp, hleading]
    ring
  have hA := abs_le.1 (abs_mul_log_norm_thetaArg_sub_le ht)
  have hG := abs_le.1 (abs_arg_thetaArg_sub_le ht)
  have hC := abs_le.1 (abs_im_inv_thetaArg_sub_le ht)
  have hE := abs_le.1 (abs_im_inv_thetaArg_cube_le ht)
  have hsum : 1 / (64 * t ^ 3) + 1 / (32 * t ^ 3) + 1 / (24 * t ^ 3) + 1 / (45 * t ^ 3)
      = 319 / (2880 * t ^ 3) := by ring
  rw [hid, abs_le]
  constructor <;> linarith [hA.1, hA.2, hG.1, hG.2, hC.1, hC.2, hE.1, hE.2]

/-! ### The theta estimate, sharp and in its two thresholded forms -/

/-- **Leading term of the Stirling phase error** (`riemann_siegel_first.tex`,
`lem:rsf_theta_sharp`): the deviation of the Riemann–Siegel theta function from the leading
Stirling phase `ϑ = leadingTheta` has leading term `1/(48t)`. -/
theorem abs_riemannSiegelTheta_sub_leading_sub_inv_le {t : ℝ} (ht : 0 < t) :
    |riemannSiegelTheta t - leadingTheta t - 1 / (48 * t)|
      ≤ 319 / (2880 * t ^ 3) + 12 / t ^ 4 := by
  rw [show riemannSiegelTheta t - leadingTheta t - 1 / (48 * t)
      = (riemannSiegelTheta t - ((logGammaStirling 2 (thetaArg t)).im - t / 2 * Real.log π))
        + ((logGammaStirling 2 (thetaArg t)).im - t / 2 * Real.log π - leadingTheta t
            - 1 / (48 * t)) from by ring]
  refine (abs_add_le _ _).trans ?_
  -- step (ii), the Euler-Maclaurin remainder, in the `thetaArg` spelling of step (i)
  have hrem : |riemannSiegelTheta t
      - ((logGammaStirling 2 (thetaArg t)).im - t / 2 * Real.log π)| ≤ 12 / t ^ 4 := by
    simpa [riemannSiegelThetaApproximant, thetaArg] using
      abs_riemannSiegelTheta_sub_approximant_two_le ht
  linarith [hrem, abs_im_logGammaStirling_two_sub_leading_sub_inv_le ht]

/-- **Leading Stirling form of `θ` at the sharp first-order threshold** `t ≥ 32π`, in the form
`1.01/(48t)`. -/
theorem abs_riemannSiegelTheta_sub_leading_le' {t : ℝ} (ht : 32 * π ≤ t) :
    |riemannSiegelTheta t - leadingTheta t| ≤ 101 / (4800 * t) := by
  have h100 : (100 : ℝ) ≤ t := le_trans (by linarith [Real.pi_gt_d2]) ht
  have ht0 : (0 : ℝ) < t := by linarith
  have ht2 : (10000 : ℝ) ≤ t ^ 2 := by nlinarith
  have ht3 : (1000000 : ℝ) ≤ t ^ 3 := by nlinarith
  -- the two `O(t^{-3})` terms are each at most `1/(9600t)`, and `1/48 + 1/4800 = 101/4800`
  have h3 : (319 : ℝ) / (2880 * t ^ 3) ≤ 1 / (9600 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left ht2 (by positivity : (0 : ℝ) ≤ 2880 * t)]
  have h4 : (12 : ℝ) / t ^ 4 ≤ 1 / (9600 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left ht3 ht0.le]
  have hval : (1 : ℝ) / (48 * t) + (1 / (9600 * t) + 1 / (9600 * t)) = 101 / (4800 * t) := by
    ring
  have hsharp := abs_riemannSiegelTheta_sub_leading_sub_inv_le ht0
  rw [abs_le] at hsharp ⊢
  constructor <;> linarith [hsharp.1, hsharp.2, (by positivity : (0 : ℝ) < 1 / (48 * t))]

/-- **Leading Stirling form of `θ`** (`riemann_siegel_first.tex`, `lem:rsf_theta`): the
Riemann–Siegel theta function agrees with the leading Stirling phase `ϑ = leadingTheta` to within
`1/(40t)`. -/
theorem abs_riemannSiegelTheta_sub_leading_le {t : ℝ} (ht : 10 ^ 3 ≤ t) :
    |riemannSiegelTheta t - leadingTheta t| ≤ 1 / (40 * t) := by
  have ht0 : (0 : ℝ) < t := by linarith
  refine (abs_riemannSiegelTheta_sub_leading_le' (by linarith [Real.pi_lt_d2])).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

end Zeta.RiemannSiegel
