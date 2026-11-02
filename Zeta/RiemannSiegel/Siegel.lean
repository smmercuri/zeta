/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannSiegel.Entire
public import Zeta.RiemannSiegel.Ray
public import Zeta.Zeros.HardyZ

/-!
# Siegel's identity

`riemann_siegel_zero.tex`, `sec:rsz_siegel`. Siegel's identity
`ζ(s) = -I(s,½) - e^{-2iθ(t)} conj (I(s,½))` on the critical line is the one input of the
Riemann–Siegel tower that does not come from the contour apparatus of
`Zeta/RiemannSiegel/Shift.lean` and `Zeta/RiemannSiegel/Deform.lean`. This file proves it, in
three steps.

On `Re s > 1` the Mellin form of `Zeta/RiemannSiegel/Ray.lean` expresses `ζ(s) + I(s,½)` through
the mirror Hankel integral `Φ̃(1-s)`, and `Zeta/RiemannSiegel/Mirror.lean` expresses the mirror
contour integral `Ĩ(1-s,½)` through the same `Φ̃(1-s)`; the two are matched by the single
`Γ`-identity `χ(s) cos(πs/2) = (2π)^s/(2Γ(s))`. That is `prop:rsz_general_half`. Both contour
integrals being entire (`Zeta/RiemannSiegel/Entire.lean`) and `χ` being holomorphic off
`{1, 3, 5, …}`, the identity theorem carries the identity to all of `ℂ ∖ {1, 3, 5, …}`. On the
critical line `1-s = s̄`, so the mirror integral is the conjugate of `I(s,½)` and `χ` is the unit
`e^{-2iθ(t)}`.

## Main results

* `Zeta.RiemannSiegel.tendsto_contourIntegral_atTop_nhds_riemannZeta_add_contourIntegral_half`
  (`lem:rsz_limit`);
* `Zeta.RiemannSiegel.riemannZeta_add_contourIntegral_add_chi_mul_mirror_eq_zero_of_one_lt`
  (`prop:rsz_general_half`);
* `Zeta.RiemannSiegel.riemannZeta_add_contourIntegral_add_chi_mul_mirror_eq_zero`
  (`thm:rsz_general`);
* `Zeta.RiemannSiegel.riemannZeta_eq_neg_contourIntegral_sub` (`thm:rsz_siegel`).
-/
@[expose] public section


open Complex Filter

open scoped Real Topology

namespace Zeta.RiemannSiegel

/-- **The far-contour limit** `K(s) = lim_ν I(s, ν+½) = ζ(s) + I(s,½)`, for `Re s > 1`. -/
theorem tendsto_contourIntegral_atTop_nhds_riemannZeta_add_contourIntegral_half {s : ℂ}
    (hs : 1 < s.re) :
    Tendsto (fun ν : ℕ ↦ contourIntegral s ((ν : ℝ) + 1 / 2)) atTop
      (𝓝 (riemannZeta s + contourIntegral s (1 / 2))) := by
  have hsum : HasSum (fun n : ℕ ↦ 1 / (n : ℂ) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    exact (Complex.summable_one_div_nat_cpow.mpr hs).hasSum
  -- the `n = 0` term of the Dirichlet series vanishes, so `range (ν+1)` and `Icc 1 ν` agree
  have hcast : ∀ ν : ℕ, ∑ n ∈ Finset.range (ν + 1), 1 / (n : ℂ) ^ s
      = ∑ i ∈ Finset.Icc 1 ν, (i : ℂ) ^ (-s) := fun ν ↦ by
    rw [show Finset.range (ν + 1) = insert 0 (Finset.Icc 1 ν) from by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; lia,
      Finset.sum_insert (by simp)]
    simp [Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs), Complex.cpow_neg]
  refine ((hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).add_const
    (contourIntegral s (1 / 2))).congr fun ν ↦ ?_
  rw [Function.comp_apply, hcast ν, sum_cpow_neg_eq_contourIntegral_sub_contourIntegral s ν]
  ring

/-- **The mirror contour integral is entire** (`riemann_siegel_zero.tex`, `lem:rsz_entire`). -/
theorem differentiable_mirrorContourIntegral_one_sub {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    Differentiable ℂ fun s ↦ mirrorContourIntegral (1 - s) a := fun s ↦ by
  rw [show (fun s : ℂ ↦ mirrorContourIntegral (1 - s) a)
      = starRingEnd ℂ ∘ (fun u : ℂ ↦ contourIntegral (1 - u) a) ∘ starRingEnd ℂ from
    funext fun u ↦ by simp [mirrorContourIntegral]]
  exact differentiableAt_conj_conj_iff.2
    ((differentiable_contourIntegral_of_le_half ha0 ha _).fun_comp' _
      ((differentiableAt_const 1).sub differentiableAt_fun_id))

/-- **Siegel's identity on `Re s > 1`** (`riemann_siegel_zero.tex`, `prop:rsz_general_half`):
`ζ(s) + I(s,½) + χ(s) Ĩ(1-s,½) = 0`. -/
theorem riemannZeta_add_contourIntegral_add_chi_mul_mirror_eq_zero_of_one_lt {s : ℂ}
    (hs : 1 < s.re) (hodd : ∀ n : ℕ, s ≠ 2 * n + 1) :
    riemannZeta s + contourIntegral s (1 / 2)
      + Complex.chi s * mirrorContourIntegral (1 - s) (1 / 2) = 0 := by
  rw [riemannZeta_add_contourIntegral_half_eq hs, mirrorContourIntegral_one_sub_eq hs,
    show ((2 * π : ℝ) : ℂ) = 2 * (π : ℂ) by push_cast; ring]
  linear_combination (-(exp (-((π / 4 : ℝ) * I * (2 - s))) * mirrorHankelIntegral (1 - s))) *
    Complex.chi_mul_cos hodd

private theorem isClosed_range_two_mul_natCast_add_one :
    IsClosed (Set.range fun n : ℕ ↦ 2 * (n : ℂ) + 1) := by
  simpa [Set.range_comp, Function.comp_def] using
    (((Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).trans (Homeomorph.addRight 1)).isClosedMap.comp
      (Complex.isometry_ofReal.isClosedEmbedding.isClosedMap.comp
        Nat.isClosedEmbedding_coe_real.isClosedMap)).isClosed_range

/-- **Siegel's identity** (`riemann_siegel_zero.tex`, `thm:rsz_general`):
`ζ(s) + I(s,½) + χ(s) Ĩ(1-s,½) = 0` for every `s ∉ {1, 3, 5, …}`. -/
theorem riemannZeta_add_contourIntegral_add_chi_mul_mirror_eq_zero {s : ℂ}
    (hodd : ∀ n : ℕ, s ≠ 2 * n + 1) :
    riemannZeta s + contourIntegral s (1 / 2)
      + Complex.chi s * mirrorContourIntegral (1 - s) (1 / 2) = 0 := by
  set S : Set ℂ := Set.range fun n : ℕ ↦ 2 * (n : ℂ) + 1 with hS
  have hmem : ∀ z : ℂ, z ∈ Sᶜ ↔ ∀ n : ℕ, z ≠ 2 * n + 1 := fun z ↦ by simp [hS, eq_comm]
  set F : ℂ → ℂ := fun z ↦ riemannZeta z + contourIntegral z (1 / 2)
    + Complex.chi z * mirrorContourIntegral (1 - z) (1 / 2)
  -- `F` is holomorphic off the odd integers
  have hdiff : DifferentiableOn ℂ F Sᶜ := fun z hz ↦ by
    have hz' := (hmem z).1 hz
    exact (((differentiableAt_riemannZeta fun h ↦ hz' 0 (by rw [h]; norm_num)).add
      (differentiable_contourIntegral_of_le_half (by norm_num) le_rfl z)).add
      ((Complex.differentiableAt_chi hz').mul
        (differentiable_mirrorContourIntegral_one_sub (by norm_num) le_rfl z)))
      |>.differentiableWithinAt
  -- the complement of a countable set in `ℂ` is connected
  have hconn : IsPreconnected (Sᶜ : Set ℂ) :=
    ((Set.countable_range _).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have hz₀ : (2 + I : ℂ) ∈ (Sᶜ : Set ℂ) :=
    (hmem _).2 fun n h ↦ by simpa using congrArg Complex.im h
  -- `F` vanishes on the open set `{Re z > 1, Im z ≠ 0}`, a neighbourhood of `2 + I`
  have hev : F =ᶠ[𝓝 (2 + I : ℂ)] 0 := by
    have hU : IsOpen {z : ℂ | 1 < z.re ∧ z.im ≠ 0} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_ne.preimage continuous_im)
    filter_upwards [hU.mem_nhds (show 1 < (2 + I : ℂ).re ∧ (2 + I : ℂ).im ≠ 0 by norm_num)]
      with z hz
    exact riemannZeta_add_contourIntegral_add_chi_mul_mirror_eq_zero_of_one_lt hz.1
      fun n h ↦ hz.2 (by simpa using congrArg Complex.im h)
  exact (hdiff.analyticOnNhd isClosed_range_two_mul_natCast_add_one.isOpen_compl)
    |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀ hev ((hmem s).2 hodd)

/-- **Siegel's identity on the critical line** (`riemann_siegel_zero.tex`, `thm:rsz_siegel`):
for `t > 0` and `s = ½+it`, `ζ(s) = -I(s,½) - e^{-2iθ(t)} conj (I(s,½))`. -/
theorem riemannZeta_eq_neg_contourIntegral_sub {t : ℝ} (ht : 0 < t) :
    riemannZeta (1 / 2 + t * I)
      = -contourIntegral (1 / 2 + t * I) (1 / 2)
        - exp (-(2 * (riemannSiegelTheta t : ℂ)) * I) *
          (starRingEnd ℂ) (contourIntegral (1 / 2 + t * I) (1 / 2)) := by
  have hodd : ∀ n : ℕ, (1 / 2 + (t : ℂ) * I) ≠ 2 * n + 1 := fun n h ↦
    ht.ne' (by simpa using congrArg Complex.im h)
  have hmirror : mirrorContourIntegral (1 - (1 / 2 + (t : ℂ) * I)) (1 / 2)
      = starRingEnd ℂ (contourIntegral (1 / 2 + (t : ℂ) * I) (1 / 2)) := by
    rw [mirrorContourIntegral, show (1 : ℂ) - (1 / 2 + (t : ℂ) * I)
      = starRingEnd ℂ (1 / 2 + (t : ℂ) * I) by norm_num [Complex.ext_iff], Complex.conj_conj]
  have hchi : Complex.chi (1 / 2 + (t : ℂ) * I) = exp (-(2 * (riemannSiegelTheta t : ℂ)) * I) := by
    rw [mul_comm (t : ℂ) I]; exact Complex.chi_half_add_mul_I ht.le
  have h := riemannZeta_add_contourIntegral_add_chi_mul_mirror_eq_zero hodd
  rw [hmirror, hchi] at h
  linear_combination h

end Zeta.RiemannSiegel
