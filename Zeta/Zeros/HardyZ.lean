/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Analysis.SpecialFunctions.GammaFactor
public import Zeta.Theta
public import Zeta.RiemannXi
public import Zeta.Gamma.LogGammaBranch
public import Zeta.Gamma.LogGammaEM
public import Zeta.EulerMaclaurin.Continuation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Hardy's `Z` function and its Euler–Maclaurin error bound

Hardy's `Z(t) = Re(e^{iθ(t)} ζ(½+it))`, with `θ = riemannSiegelTheta`, is the real-valued
quantity whose sign changes locate the zeros of `ζ` on the critical line. This file records `Z`,
its Riemann–Siegel/Euler–Maclaurin approximant, and the resulting error bound, in which every
term is a function of `M`, `N`, `t` alone.

## Main definitions

- `Zeta.hardyZ`: Hardy's `Z(t) = Re(e^{iθ(t)} ζ(½+it))`.
- `riemannSiegelThetaApproximant`, `riemannSiegelThetaStirlingErrorBound`,
  `riemannSiegelThetaStirlingErrorBound'`: the shifted order-`M`, cutoff-`N` Stirling approximant
  of `θ` and its error bounds, in `Re w` and in `‖w‖` form.
- `thetaShift`: the height-independent Stirling shift `2M` used for `θ`, decoupled from the zeta
  cutoff `N`.
- `hardyZApproximantEM`, `hardyZRemainderEM`, `hardyZErrorBoundEM`: the approximant
  `Z̃_{M,N}(t) = Re(e^{i θ̃_{M,thetaShift M}(t)} ζ̃_{M,N}(t))`, its error `Z(t) − Z̃_{M,N}(t)`, and
  the bound on that error.

## Main results

- `riemannSiegelTheta_eq_im_logGamma`: the bridge `θ(T) = Im (log Γ (¼+iT/2)) − (T/2) log π`.
- `Complex.Gammaℝ_half_add_mul_I_eq_exp`, `Complex.chi_half_add_mul_I`: Deligne's archimedean
  factor on the critical line as an exponential, and the resulting `χ(½+it) = e^{-2iθ(t)}`.
- `continuousOn_hardyZ`, `hardyZ_eq_zero_iff_riemannZeta`: continuity of `Z` on `[0, ∞)`, and
  `Z(t) = 0 ↔ ζ(½+it) = 0`.
- `abs_riemannSiegelTheta_sub_stirling_le`, `abs_riemannSiegelTheta_sub_stirling_shift_le`,
  `abs_riemannSiegelTheta_sub_stirling_le'`, `abs_riemannSiegelTheta_sub_stirling_shift_le'`: the
  unshifted and shifted theta error bounds, each in `Re w` and in `‖w‖` form.
- `abs_riemannSiegelTheta_sub_approximant_two_le`: the order-`2` member of that family in closed
  form, `|θ(t) − θ̃_{2,0}(t)| ≤ 12 t^{-4}`.
- `norm_expImul_sub_expImul_le_abs`, `norm_expImul_sub_expImul_le`,
  `norm_expImul_sub_expImul_le'`: the unit-phase and phase-perturbation inequalities.
- `abs_hardyZ_sub_re_le`, `abs_hardyZ_sub_re_le'`: the `Z`-function error bound against arbitrary
  approximations of `θ(t)` and `ζ(½+it)`.
- `abs_hardyZRemainderEM_le`: `|Z(t) − Z̃_{M,N}(t)| ≤ hardyZErrorBoundEM M N t`.
-/
@[expose] public section


open Complex
open scoped Nat


/-- Hardy's `Z` function `Z(t) = Re(e^{iθ(t)} ζ(½+it))`, with `θ = riemannSiegelTheta`. -/
noncomputable def Zeta.hardyZ (t : ℝ) : ℝ :=
  (Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ)) * riemannZeta (1 / 2 + Complex.I * t)).re

/-- Continuity of the `log Γ` branch along the half-argument curve `u ↦ ¼ + i u/2`. -/
theorem continuous_logGamma_curve :
    Continuous fun u : ℝ ↦ logGamma (1 / 4 + Complex.I * ((u : ℂ) / 2)) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hre : (0 : ℝ) < (1 / 4 + Complex.I * ((u : ℂ) / 2)).re := by simp
  exact ContinuousAt.comp (f := fun u : ℝ => (1 / 4 : ℂ) + Complex.I * ((u : ℂ) / 2))
    (hasDerivAt_logGamma hre).continuousAt (by fun_prop)

/-- Theta via the holomorphic `log Γ` branch: for `T ≥ 0`,
`θ(T) = Im (log Γ (¼ + i T/2)) − (T/2) log π`, with `Complex.logGamma` the holomorphic branch on
the right half-plane normalised real on the positive axis. -/
theorem riemannSiegelTheta_eq_im_logGamma {T : ℝ} (hT : 0 ≤ T) :
    riemannSiegelTheta T
      = (logGamma (1 / 4 + Complex.I * (T / 2))).im - T / 2 * Real.log Real.pi := by
  have hre : ∀ u : ℝ, (0 : ℝ) < (1 / 4 + Complex.I * ((u : ℂ) / 2)).re := fun u => by simp
  have hcontlog : IsContLog 0 T (fun u => Complex.Gamma (1 / 4 + Complex.I * (u / 2)))
      (fun u ↦ logGamma (1 / 4 + Complex.I * (u / 2))) :=
    ⟨continuous_logGamma_curve.continuousOn, fun u _ ↦ cexp_logGamma (hre u)⟩
  rw [riemannSiegelTheta, argVariation_eq_of_isContLog hT hcontlog]
  have hg0 : (logGamma (1 / 4 + Complex.I * (((0 : ℝ) : ℂ) / 2))).im = 0 := by
    rw [show (1 : ℂ) / 4 + Complex.I * (((0 : ℝ) : ℂ) / 2) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring]
    exact logGamma_im_ofReal (by norm_num)
  simp only [hg0, sub_zero]

namespace Complex

/-- Deligne's real archimedean factor on the critical line, as an exponential:
`Γ_ℝ(½+it) = exp (log Γ(¼+it/2) − (¼+it/2) log π)`, the logarithm of `Γ` being the holomorphic
branch `Complex.logGamma`. -/
theorem Gammaℝ_half_add_mul_I_eq_exp (t : ℝ) :
    Gammaℝ (1 / 2 + I * t)
      = exp (logGamma (1 / 4 + I * ((t : ℂ) / 2))
          - (1 / 4 + I * ((t : ℂ) / 2)) * (Real.log Real.pi : ℂ)) := by
  have hwre : (0 : ℝ) < (1 / 4 + I * ((t : ℂ) / 2)).re := by simp
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsw2 : (1 / 2 + I * (t : ℂ)) / 2 = 1 / 4 + I * ((t : ℂ) / 2) := by ring
  have hΓw : Gamma ((1 / 2 + I * (t : ℂ)) / 2) = exp (logGamma (1 / 4 + I * ((t : ℂ) / 2))) := by
    rw [hsw2]
    exact (cexp_logGamma hwre).symm
  have hcpow : (Real.pi : ℂ) ^ (-(1 / 2 + I * (t : ℂ)) / 2)
      = exp (-(1 / 4 + I * ((t : ℂ) / 2)) * (Real.log Real.pi : ℂ)) := by
    rw [cpow_def_of_ne_zero hpi]
    congr 1
    rw [show log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) from (ofReal_log Real.pi_pos.le).symm,
      show (-(1 / 2 + I * (t : ℂ)) / 2 : ℂ) = -((1 / 2 + I * (t : ℂ)) / 2) from by ring, hsw2]
    ring
  rw [Gammaℝ_def, hcpow, hΓw, ← exp_add]
  congr 1
  ring

/-- The functional-equation factor on the critical line (`riemann_siegel_zero.tex`,
`lem:rsz_chi_theta`): `χ(½+it) = e^{-2iθ(t)}` for `t ≥ 0`. -/
theorem chi_half_add_mul_I {t : ℝ} (ht : 0 ≤ t) :
    chi (1 / 2 + I * t) = exp (-(2 * (riemannSiegelTheta t : ℂ)) * I) := by
  have hone_sub : (1 : ℂ) - (1 / 2 + I * (t : ℂ)) = starRingEnd ℂ (1 / 2 + I * (t : ℂ)) := by
    simp only [map_add, map_mul, conj_I, conj_ofReal, map_div₀, map_one, map_ofNat]
    ring
  have hLim : (logGamma (1 / 4 + I * ((t : ℂ) / 2))
      - (1 / 4 + I * ((t : ℂ) / 2)) * (Real.log Real.pi : ℂ)).im = riemannSiegelTheta t := by
    have himeq : ((1 / 4 + I * ((t : ℂ) / 2)) * (Real.log Real.pi : ℂ)).im
        = t / 2 * Real.log Real.pi := by
      rw [mul_im]; simp
    rw [sub_im, himeq]
    exact (riemannSiegelTheta_eq_im_logGamma ht).symm
  have hconjsub : ∀ z : ℂ, starRingEnd ℂ z - z = -(2 * (z.im : ℂ)) * I := fun z ↦ by
    apply Complex.ext
    · simp
    · simp
      ring
  rw [chi, hone_sub, Gammaℝ_conj, Gammaℝ_half_add_mul_I_eq_exp t, ← exp_conj, ← exp_sub,
    hconjsub, hLim]

end Complex

/-- Continuity of Hardy's `Z` on `[0, ∞)`. -/
theorem continuousOn_hardyZ : ContinuousOn Zeta.hardyZ (Set.Ici (0 : ℝ)) := by
  -- `θ` is continuous on `Ici 0` via the `log Γ` bridge.
  have hlog : Continuous fun t : ℝ =>
      (logGamma (1 / 4 + Complex.I * ((t : ℂ) / 2))).im - t / 2 * Real.log Real.pi :=
    (Complex.continuous_im.comp continuous_logGamma_curve).sub (by fun_prop)
  have hθ : ContinuousOn riemannSiegelTheta (Set.Ici 0) :=
    hlog.continuousOn.congr fun t ht => riemannSiegelTheta_eq_im_logGamma ht
  -- `ζ(½ + i·)` is continuous everywhere (the argument is never `1`).
  have hne : ∀ t : ℝ, (1 / 2 + Complex.I * (t : ℂ)) ≠ 1 := fun t h => by
    simpa using congrArg Complex.re h
  have hζ : Continuous fun t : ℝ => riemannZeta (1 / 2 + Complex.I * (t : ℂ)) :=
    continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (f := fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ))
        (differentiableAt_riemannZeta (hne t)).continuousAt (by fun_prop)
  -- Assemble `Z(t) = Re(e^{iθ(t)} · ζ(½ + it))`.
  have hmul : ContinuousOn
      (fun t : ℝ => Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ))
        * riemannZeta (1 / 2 + Complex.I * (t : ℂ))) (Set.Ici 0) :=
    (Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hθ).const_mul Complex.I)).mul hζ.continuousOn
  exact Complex.continuous_re.comp_continuousOn hmul

/-- Zeros of Hardy's `Z` are the critical-line zeros of `ζ`: for `t ≥ 0`,
`Z(t) = 0 ↔ ζ(½+it) = 0`. -/
theorem hardyZ_eq_zero_iff_riemannZeta {t : ℝ} (ht : 0 ≤ t) :
    Zeta.hardyZ t = 0 ↔ riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  set s : ℂ := 1 / 2 + Complex.I * (t : ℂ) with hs
  have hsre : s.re = 1 / 2 := by rw [hs]; simp
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; norm_num at hsre
  have hs1 : s ≠ 1 := fun h => by rw [h] at hsre; norm_num at hsre
  have hconjs : starRingEnd ℂ s = 1 - s := by
    rw [hs]; simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal,
      map_div₀, map_one, map_ofNat]; ring
  -- the half-argument point `w = s/2 = 1/4 + i t/2`
  set w : ℂ := 1 / 4 + Complex.I * ((t : ℂ) / 2) with hw
  have hwim : w.im = t / 2 := by rw [hw]; simp
  -- `Γ_ℝ(s) = exp L` with `L = logΓ(w) - w·log π`.
  set L : ℂ := logGamma w - w * (Real.log Real.pi : ℂ) with hL
  have hGammaℝ : Gammaℝ s = Complex.exp L := Complex.Gammaℝ_half_add_mul_I_eq_exp t
  have hLim : L.im = riemannSiegelTheta t := by
    have himeq : (w * (Real.log Real.pi : ℂ)).im = t / 2 * Real.log Real.pi := by
      rw [Complex.mul_im, hwim]; simp
    rw [hL, Complex.sub_im, himeq, hw]
    exact (riemannSiegelTheta_eq_im_logGamma ht).symm
  -- `exp L = exp(L.re) · e^{iθ}`.
  have hexpLre_ne : (Real.exp L.re : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hsplit : Gammaℝ s
      = (Real.exp L.re : ℂ) * Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ)) := by
    rw [hGammaℝ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im L]
    rw [hLim]; ring
  have hexpiθ : Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ))
      = Gammaℝ s / (Real.exp L.re : ℂ) := by
    rw [eq_div_iff hexpLre_ne, mul_comm]; exact hsplit.symm
  -- `Q = ½ s (s-1)` and `ξ(s)` are real (via conjugation).
  have hQconj : starRingEnd ℂ ((1 / 2 : ℂ) * (s * (s - 1))) = (1 / 2 : ℂ) * (s * (s - 1)) := by
    simp only [map_mul, map_sub, map_one, map_div₀, map_ofNat, hconjs]; ring
  have hξconj : starRingEnd ℂ (riemannXi s) = riemannXi s := by
    rw [← riemannXi_conj, hconjs, riemannXi_one_sub]
  -- `ξ(s) = Q · Γ_ℝ(s) · ζ(s)`, hence `Γ_ℝ(s)·ζ(s) = ξ(s)/Q` is real.
  have hΓℝ_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hQ_ne : (1 / 2 : ℂ) * (s * (s - 1)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
  have hξ : riemannXi s = 1 / 2 * (s * (s - 1)) * Gammaℝ s * riemannZeta s :=
    riemannXi_eq_prefactor_mul hs0 hs1 hΓℝ_ne
  have hR : Gammaℝ s * riemannZeta s = riemannXi s / ((1 / 2 : ℂ) * (s * (s - 1))) := by
    rw [eq_div_iff hQ_ne, hξ]; ring
  have hξ_re : riemannXi s = ((riemannXi s).re : ℂ) := (Complex.conj_eq_iff_re.mp hξconj).symm
  have hQ_re : (1 / 2 : ℂ) * (s * (s - 1)) = (((1 / 2 : ℂ) * (s * (s - 1))).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp hQconj).symm
  have hR_eq : Gammaℝ s * riemannZeta s
      = (((riemannXi s).re / ((1 / 2 : ℂ) * (s * (s - 1))).re : ℝ) : ℂ) := by
    rw [hR]; conv_lhs => rw [hξ_re, hQ_re]
    rw [← Complex.ofReal_div]
  -- `Z(t)` is the real number `ξ.re / Q.re / exp(L.re)`.
  have hZC : ((Zeta.hardyZ t : ℝ) : ℂ) = Gammaℝ s * riemannZeta s / (Real.exp L.re : ℂ) := by
    have hval : Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ)) * riemannZeta s
        = Gammaℝ s * riemannZeta s / (Real.exp L.re : ℂ) := by rw [hexpiθ]; ring
    rw [Zeta.hardyZ, show (1 / 2 + Complex.I * (t : ℂ)) = s from hs.symm, hval, hR_eq,
      ← Complex.ofReal_div, Complex.ofReal_re]
  -- Assemble the iff.
  rw [← Complex.ofReal_eq_zero, hZC, div_eq_zero_iff, mul_eq_zero]
  simp only [hΓℝ_ne, hexpLre_ne, or_false, false_or]

/-- Unit-phase difference bound: for real phases `α, β`, `‖e^{iα} - e^{iβ}‖ ≤ |α - β|`. -/
theorem norm_expImul_sub_expImul_le_abs (α β : ℝ) :
    ‖Complex.exp (Complex.I * (α : ℂ)) - Complex.exp (Complex.I * (β : ℂ))‖ ≤ |α - β| := by
  have hunit : ‖Complex.exp (Complex.I * (β : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I β
  have hfac : Complex.exp (Complex.I * (α : ℂ)) - Complex.exp (Complex.I * (β : ℂ))
      = Complex.exp (Complex.I * (β : ℂ)) * (Complex.exp (Complex.I * ((α - β : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [hfac, norm_mul, hunit, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := α - β)
  rwa [Real.norm_eq_abs] at this

/-- Phase perturbation: for real phases `α, β` and complex `z, w`,
`‖e^{iα}z - e^{iβ}w‖ ≤ |α-β|‖z‖ + ‖z-w‖`. -/
theorem norm_expImul_sub_expImul_le (α β : ℝ) (z w : ℂ) :
    ‖Complex.exp (Complex.I * (α : ℂ)) * z - Complex.exp (Complex.I * (β : ℂ)) * w‖
      ≤ |α - β| * ‖z‖ + ‖z - w‖ := by
  set a : ℂ := Complex.exp (Complex.I * (α : ℂ)) with ha
  set b : ℂ := Complex.exp (Complex.I * (β : ℂ)) with hb
  have hunit : ‖b‖ = 1 := by rw [hb, mul_comm]; exact Complex.norm_exp_ofReal_mul_I β
  have hphase : ‖a - b‖ ≤ |α - β| := norm_expImul_sub_expImul_le_abs α β
  -- split and apply the triangle inequality
  have hsplit : a * z - b * w = (a - b) * z + b * (z - w) := by ring
  calc ‖a * z - b * w‖
      = ‖(a - b) * z + b * (z - w)‖ := by rw [hsplit]
    _ ≤ ‖(a - b) * z‖ + ‖b * (z - w)‖ := norm_add_le _ _
    _ = ‖a - b‖ * ‖z‖ + ‖z - w‖ := by rw [norm_mul, norm_mul, hunit, one_mul]
    _ ≤ |α - β| * ‖z‖ + ‖z - w‖ := by gcongr

/-- Phase perturbation, approximant form: for real phases `α, β` and complex `z, w`,
`‖e^{iα}z - e^{iβ}w‖ ≤ |α-β|‖w‖ + ‖z-w‖`. The leading factor is the norm of `w`, in applications
the known approximant. -/
theorem norm_expImul_sub_expImul_le' (α β : ℝ) (z w : ℂ) :
    ‖Complex.exp (Complex.I * (α : ℂ)) * z - Complex.exp (Complex.I * (β : ℂ)) * w‖
      ≤ |α - β| * ‖w‖ + ‖z - w‖ := by
  have h := norm_expImul_sub_expImul_le β α w z
  rwa [norm_sub_rev (Complex.exp (Complex.I * (β : ℂ)) * w), abs_sub_comm β α,
    norm_sub_rev w z] at h

/-- The `Z`-function error bound: for any approximations `θ̃ ∈ ℝ`, `ζ̃ ∈ ℂ` of `θ(t)` and
`ζ(½+it)`,

`|Z(t) - Re(e^{iθ̃} ζ̃)| ≤ |θ(t) - θ̃| · ‖ζ(½+it)‖ + ‖ζ(½+it) - ζ̃‖`. -/
theorem abs_hardyZ_sub_re_le (t : ℝ) (θ' : ℝ) (ζ' : ℂ) :
    |Zeta.hardyZ t - (Complex.exp (Complex.I * (θ' : ℂ)) * ζ').re|
      ≤ |riemannSiegelTheta t - θ'| * ‖riemannZeta (1 / 2 + Complex.I * t)‖
        + ‖riemannZeta (1 / 2 + Complex.I * t) - ζ'‖ := by
  set ζv : ℂ := riemannZeta (1 / 2 + Complex.I * t) with hζv
  have hre : Zeta.hardyZ t - (Complex.exp (Complex.I * (θ' : ℂ)) * ζ').re
      = (Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ)) * ζv
          - Complex.exp (Complex.I * (θ' : ℂ)) * ζ').re := by
    rw [Zeta.hardyZ, hζv, Complex.sub_re]
  rw [hre]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  exact norm_expImul_sub_expImul_le (riemannSiegelTheta t) θ' ζv ζ'

/-- The `Z`-function error bound, approximant form: for any approximations `θ̃ ∈ ℝ`,
`ζ̃ ∈ ℂ` of `θ(t)` and `ζ(½+it)`,

`|Z(t) - Re(e^{iθ̃} ζ̃)| ≤ |θ(t) - θ̃| · ‖ζ̃‖ + ‖ζ(½+it) - ζ̃‖`.

The leading term uses the *computed* modulus `‖ζ̃‖`. -/
theorem abs_hardyZ_sub_re_le' (t : ℝ) (θ' : ℝ) (ζ' : ℂ) :
    |Zeta.hardyZ t - (Complex.exp (Complex.I * (θ' : ℂ)) * ζ').re|
      ≤ |riemannSiegelTheta t - θ'| * ‖ζ'‖
        + ‖riemannZeta (1 / 2 + Complex.I * t) - ζ'‖ := by
  set ζv : ℂ := riemannZeta (1 / 2 + Complex.I * t) with hζv
  have hre : Zeta.hardyZ t - (Complex.exp (Complex.I * (θ' : ℂ)) * ζ').re
      = (Complex.exp (Complex.I * (riemannSiegelTheta t : ℂ)) * ζv
          - Complex.exp (Complex.I * (θ' : ℂ)) * ζ').re := by
    rw [Zeta.hardyZ, hζv, Complex.sub_re]
  rw [hre]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  exact norm_expImul_sub_expImul_le' (riemannSiegelTheta t) θ' ζv ζ'

open Complex.Stirling

/-- The Riemann–Siegel theta Stirling error bound
`(2M+1)!/(2M(2π)^{2M}) · (¼+N)^{-2M}`, the right-hand side of
`abs_riemannSiegelTheta_sub_stirling_shift_le`. -/
noncomputable abbrev riemannSiegelThetaStirlingErrorBound (M N : ℕ) : ℝ :=
  ((2 * M + 1)! : ℝ) / (2 * M * (2 * Real.pi) ^ (2 * M)) * (1 / 4 + N : ℝ) ^ (-(2 * M : ℤ))

/-- The Riemann–Siegel theta Stirling error bound in `‖w‖` form
`(2M+1)! 2^{2M+1}/(2M(2π)^{2M}) · ((¼+N)² + t²/4)^{-M}`, the right-hand side of
`abs_riemannSiegelTheta_sub_stirling_shift_le'`. The base is `‖¼ + N + it/2‖²`, so the bound
decays in the height `t`. -/
noncomputable abbrev riemannSiegelThetaStirlingErrorBound' (M N : ℕ) (t : ℝ) : ℝ :=
  ((2 * M + 1)! : ℝ) * 2 ^ (2 * M + 1) / (2 * M * (2 * Real.pi) ^ (2 * M))
    * ((1 / 4 + N) ^ 2 + (t / 2) ^ 2 : ℝ) ^ (-(M : ℤ))

/-- The shifted Riemann–Siegel theta approximant: with `w_t = ¼ + i t/2`, the order-`M`,
cutoff-`N` Stirling approximant of `riemannSiegelTheta`:
`θ̃_{M,N}(t) = Im (S_M(w_t + N) − ∑_{j<N} Log (w_t + j)) − (t/2) log π`. -/
noncomputable abbrev riemannSiegelThetaApproximant (M N : ℕ) (t : ℝ) : ℝ :=
  ((logGammaStirling M (1 / 4 + Complex.I * (t / 2) + N)
        - ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * (t / 2) + j)).im
      - t / 2 * Real.log Real.pi : ℝ)

/-- The real part of the shifted Stirling argument `¼ + iT/2 + N`. -/
private theorem re_thetaArg_add_natCast (T : ℝ) (N : ℕ) :
    (1 / 4 + Complex.I * (T / 2) + (N : ℂ)).re = 1 / 4 + N := by
  simp

/-- The shifted Stirling argument `¼ + iT/2 + N` has positive real part. -/
private theorem re_thetaArg_add_natCast_pos (T : ℝ) (N : ℕ) :
    0 < (1 / 4 + Complex.I * (T / 2) + (N : ℂ)).re := by
  rw [re_thetaArg_add_natCast]; positivity

/-- The theta error is the imaginary part of the shifted `log Γ` Stirling remainder. -/
private theorem riemannSiegelTheta_sub_approximant_eq {M N : ℕ} (hM : 1 ≤ M) {T : ℝ}
    (hT : 0 ≤ T) :
    riemannSiegelTheta T - riemannSiegelThetaApproximant M N T
      = (logGammaRemainderIoi M (1 / 4 + Complex.I * (T / 2) + N)).im := by
  have hreT : (0 : ℝ) < (1 / 4 + Complex.I * (T / 2)).re := by simp
  rw [riemannSiegelTheta_eq_im_logGamma hT, logGamma_eq_sub_sum_log_add hreT N,
    logGamma_eq_stirling_add_remainder hM (re_thetaArg_add_natCast_pos T N)]
  simp only [riemannSiegelThetaApproximant, Complex.add_im, Complex.sub_im]
  ring

/-- Theta error, shifted: for `M ≥ 1`, `N : ℕ` and `T ≥ 0`,
`|θ(T) − θ̃_{M,N}(T)| ≤ (2M+1)!/(2M(2π)^{2M}) · (¼+N)^{-2M}`. The integer shift `N` makes the
Stirling argument's real part `¼ + N` as large as desired. -/
theorem abs_riemannSiegelTheta_sub_stirling_shift_le {M N : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    |riemannSiegelTheta T - riemannSiegelThetaApproximant M N T|
      ≤ riemannSiegelThetaStirlingErrorBound M N := by
  rw [riemannSiegelTheta_sub_approximant_eq hM hT]
  refine (Complex.abs_im_le_norm _).trans
    ((norm_logGammaRemainderIoi_le hM (re_thetaArg_add_natCast_pos T N)).trans_eq ?_)
  simp only [logGammaRemainderBound, riemannSiegelThetaStirlingErrorBound]
  rw [re_thetaArg_add_natCast]

/-- Theta error, shifted, in `‖w‖` form: for `M ≥ 1`, `N : ℕ` and `T ≥ 0`,
`|θ(T) − θ̃_{M,N}(T)| ≤ (2M+1)! 2^{2M+1}/(2M(2π)^{2M}) · ((¼+N)² + T²/4)^{-M}`, a bound that
decays in `T`. -/
theorem abs_riemannSiegelTheta_sub_stirling_shift_le' {M N : ℕ} (hM : 1 ≤ M) {T : ℝ}
    (hT : 0 ≤ T) :
    |riemannSiegelTheta T - riemannSiegelThetaApproximant M N T|
      ≤ riemannSiegelThetaStirlingErrorBound' M N T := by
  rw [riemannSiegelTheta_sub_approximant_eq hM hT]
  refine (Complex.abs_im_le_norm _).trans
    ((norm_logGammaRemainderIoi_le' hM (re_thetaArg_add_natCast_pos T N)).trans_eq ?_)
  have hsq : ‖(1 / 4 + Complex.I * (T / 2) + (N : ℂ))‖ ^ 2 = (1 / 4 + N) ^ 2 + (T / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, re_thetaArg_add_natCast]
    simp [sq]
  simp only [logGammaRemainderNormBound, riemannSiegelThetaStirlingErrorBound']
  rw [show (-(2 * M : ℤ)) = 2 * (-(M : ℤ)) by ring, zpow_mul, zpow_ofNat, hsq]

/-- Theta error, unshifted: for `M ≥ 1` and `T ≥ 0`, the order-`M` Stirling estimate
`θ̃_M(T) = Im S_M(¼ + iT/2) − (T/2) log π` satisfies
`|θ(T) − θ̃_M(T)| ≤ (2M+1)!/(2M(2π)^{2M}) · (¼)^{-2M}`. -/
theorem abs_riemannSiegelTheta_sub_stirling_le {M : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    |riemannSiegelTheta T
        - ((logGammaStirling M (1 / 4 + Complex.I * (T / 2))).im - T / 2 * Real.log Real.pi)|
      ≤ riemannSiegelThetaStirlingErrorBound M 0 := by
  simpa [riemannSiegelThetaApproximant] using
    abs_riemannSiegelTheta_sub_stirling_shift_le (N := 0) hM hT

/-- Theta error, unshifted, in `‖w_T‖` form: for `M ≥ 1` and `T ≥ 0`, the order-`M` Stirling
estimate `θ̃_M(T) = Im S_M(¼ + iT/2) − (T/2) log π` satisfies
`|θ(T) − θ̃_M(T)| ≤ (2M+1)! 2^{2M+1}/(2M(2π)^{2M}) · ‖¼ + iT/2‖^{-2M}`, a bound that decays in
`T`. -/
theorem abs_riemannSiegelTheta_sub_stirling_le' {M : ℕ} (hM : 1 ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    |riemannSiegelTheta T
        - ((logGammaStirling M (1 / 4 + Complex.I * (T / 2))).im - T / 2 * Real.log Real.pi)|
      ≤ logGammaRemainderNormBound M (1 / 4 + Complex.I * (T / 2)) := by
  have hre : (0 : ℝ) < (1 / 4 + Complex.I * ((T : ℂ) / 2)).re := by simp
  have hdiff : riemannSiegelTheta T
      - ((logGammaStirling M (1 / 4 + Complex.I * (T / 2))).im - T / 2 * Real.log Real.pi)
      = (logGammaRemainderIoi M (1 / 4 + Complex.I * (T / 2))).im := by
    rw [riemannSiegelTheta_eq_im_logGamma hT, logGamma_eq_stirling_add_remainder hM hre]
    simp only [Complex.add_im]
    ring
  rw [hdiff]
  exact (Complex.abs_im_le_norm _).trans (norm_logGammaRemainderIoi_le' hM hre)

/-- Theta error at order `2`, in closed form: `|θ(t) − θ̃_{2,0}(t)| ≤ 12 t^{-4}`. -/
theorem abs_riemannSiegelTheta_sub_approximant_two_le {t : ℝ} (ht : 0 < t) :
    |riemannSiegelTheta t - riemannSiegelThetaApproximant 2 0 t| ≤ 12 / t ^ 4 := by
  have him : (1 / 4 + Complex.I * ((t : ℂ) / 2)).im = t / 2 := by simp
  have hw : t / 2 ≤ ‖(1 / 4 + Complex.I * ((t : ℂ) / 2))‖ := by
    have h := Complex.abs_im_le_norm (1 / 4 + Complex.I * ((t : ℂ) / 2))
    rwa [him, abs_of_nonneg (by linarith)] at h
  have hpi : (1296 : ℝ) ≤ (2 * Real.pi) ^ 4 := by
    have h6 : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    calc (1296 : ℝ) = 6 ^ 4 := by norm_num
      _ ≤ (2 * Real.pi) ^ 4 := pow_le_pow_left₀ (by norm_num) h6 4
  have hz : ‖(1 / 4 + Complex.I * ((t : ℂ) / 2))‖ ^ (-(2 * ((2 : ℕ) : ℤ))) ≤ 16 / t ^ 4 := by
    rw [show (-(2 * ((2 : ℕ) : ℤ))) = -((4 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
    calc (‖(1 / 4 + Complex.I * ((t : ℂ) / 2))‖ ^ 4)⁻¹ ≤ ((t / 2) ^ 4)⁻¹ :=
          inv_anti₀ (pow_pos (by linarith) 4) (pow_le_pow_left₀ (by linarith) hw 4)
      _ = 16 / t ^ 4 := by field_simp; ring
  have hexpand : logGammaRemainderNormBound 2 (1 / 4 + Complex.I * ((t : ℂ) / 2))
      = 960 / (2 * Real.pi) ^ 4
        * ‖(1 / 4 + Complex.I * ((t : ℂ) / 2))‖ ^ (-(2 * ((2 : ℕ) : ℤ))) := by
    rw [logGammaRemainderNormBound]
    congr 1
    norm_num [Nat.factorial]
    ring
  have happrox : riemannSiegelThetaApproximant 2 0 t
      = (logGammaStirling 2 (1 / 4 + Complex.I * ((t : ℂ) / 2))).im
        - t / 2 * Real.log Real.pi := by
    simp [riemannSiegelThetaApproximant]
  rw [happrox]
  refine (abs_riemannSiegelTheta_sub_stirling_le' (M := 2) (by norm_num) ht.le).trans ?_
  rw [hexpand]
  calc 960 / (2 * Real.pi) ^ 4 * ‖(1 / 4 + Complex.I * ((t : ℂ) / 2))‖ ^ (-(2 * ((2 : ℕ) : ℤ)))
      ≤ 960 / (2 * Real.pi) ^ 4 * (16 / t ^ 4) := mul_le_mul_of_nonneg_left hz (by positivity)
    _ ≤ 960 / 1296 * (16 / t ^ 4) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi) (by positivity)
    -- the sharp constant here is `320/27 = 11.85…`; `12` is a deliberate rounding
    _ ≤ 12 / t ^ 4 := by
        rw [show (960 : ℝ) / 1296 * (16 / t ^ 4) = 320 / 27 / t ^ 4 from by ring]
        gcongr
        norm_num

/-- The theta Stirling shift: the number of `log Γ` recurrence steps applied before the order-`M`
expansion, moving the Stirling argument's real part from `¼` to `¼ + 2M`. The Stirling remainder
then scales like `(¼ + 2M)^{-2M}`, independent of the height and of the zeta cutoff `N`. -/
def thetaShift (M : ℕ) : ℕ := 2 * M

/-- The Riemann–Siegel/Euler–Maclaurin approximant for Hardy's `Z`,
`Z̃_{M,N}(t) = Re(e^{i θ̃_{M,thetaShift M}(t)} · ζ̃_{M,N}(t))`, built from the theta approximant
`riemannSiegelThetaApproximant M (thetaShift M) t` and the zeta approximant
`zetaApproximant (½ + it) M N`. The theta shift is independent of the zeta cutoff `N`, since the
theta error depends only on `M` and the shift. -/
noncomputable abbrev hardyZApproximantEM (M N : ℕ) (t : ℝ) : ℝ :=
  (Complex.exp (Complex.I * ((riemannSiegelThetaApproximant M (thetaShift M) t : ℝ) : ℂ))
      * zetaApproximant (1 / 2 + Complex.I * t) M N).re

/-- The error term of the approximant for Hardy's `Z`, `Z(t) − Z̃_{M,N}(t)`. It is bounded by
`abs_hardyZRemainderEM_le`. -/
noncomputable abbrev hardyZRemainderEM (M N : ℕ) (t : ℝ) : ℝ :=
  Zeta.hardyZ t - hardyZApproximantEM M N t

/-- Hardy's `Z` splits as its approximant plus its remainder. -/
theorem hardyZ_eq_approximantEM_add_remainderEM (M N : ℕ) (t : ℝ) :
    Zeta.hardyZ t = hardyZApproximantEM M N t + hardyZRemainderEM M N t := by
  rw [hardyZRemainderEM]; ring

/-- The parameterised Hardy `Z` error bound
`θ̃err_{M,N} · ‖ζ̃_{M,N}(t)‖ + ‖R^ζ_{M,N}(t)‖`, a function of `M`, `N`, `t` alone. -/
noncomputable abbrev hardyZErrorBoundEM (M N : ℕ) (t : ℝ) : ℝ :=
  riemannSiegelThetaStirlingErrorBound M (thetaShift M)
      * ‖zetaApproximant (1 / 2 + Complex.I * t) M N‖
    + ‖zetaRemainder (1 / 2 + Complex.I * t) M N‖

/-- The fully parameterised Hardy `Z` error bound: for `M ≥ 1`, `N ≥ 1` and `t ≥ 0`,
`|Z(t) − Z̃_{M,N}(t)| ≤ hardyZErrorBoundEM M N t`. Bounding its trailing `‖R^ζ‖` by
`norm_zetaRemainder_le` makes the whole error explicit. -/
theorem abs_hardyZRemainderEM_le {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    |hardyZRemainderEM M N t| ≤ hardyZErrorBoundEM M N t := by
  have hs1 : (1 / 2 + Complex.I * (t : ℂ)) ≠ 1 := fun h ↦ by
    simpa using congrArg Complex.re h
  have hsre : -(2 * M + 1 : ℝ) < (1 / 2 + Complex.I * (t : ℂ)).re := by
    rw [show (1 / 2 + Complex.I * (t : ℂ)).re = 1 / 2 by simp]
    have : (0 : ℝ) ≤ 2 * M + 1 := by positivity
    linarith
  have hzeta := riemannZeta_eq_approximant_add_remainder
    (1 / 2 + Complex.I * t) M N hN hsre hs1
  have hζdiff : riemannZeta (1 / 2 + Complex.I * t)
        - zetaApproximant (1 / 2 + Complex.I * t) M N
      = zetaRemainder (1 / 2 + Complex.I * t) M N := by
    rw [hzeta]; ring
  refine (abs_hardyZ_sub_re_le' t
      (riemannSiegelThetaApproximant M (thetaShift M) t)
      (zetaApproximant (1 / 2 + Complex.I * t) M N)).trans ?_
  rw [hardyZErrorBoundEM, hζdiff]
  gcongr
  exact abs_riemannSiegelTheta_sub_stirling_shift_le hM ht
