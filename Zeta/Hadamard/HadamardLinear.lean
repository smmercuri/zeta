/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Hadamard.HadamardFactorization

/-!
# The exponent of the Hadamard factorisation of `ξ` is affine

Writing `ξ = exp(h) · P` with `h` entire and `P` the canonical product of the zeros of `ξ`, the
exponent `h` is affine (`hadamard_factorization.tex`).

## Main result

* `exists_affine_log_riemannXi_div_canonicalProduct` (`lem:hf_h_linear`): there are `A, B : ℂ`
  with `h s = A + B * s` for all `s`.
-/
@[expose] public section


open Complex Filter Topology Set Metric


/-- **The exponent of the Hadamard factorisation is affine (`lem:hf_h_linear`).** If `ξ = exp(h)·P`
with `h` entire and `P` the canonical product, there are `A B : ℂ` with `h s = A + B·s` for all
`s`. -/
theorem exists_affine_log_riemannXi_div_canonicalProduct {h : ℂ → ℂ}
    (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    ∃ A B : ℂ, ∀ s, h s = A + B * s := by
  -- Growth of `Re h` on a good circle (`lem:hf_reH_growth`).
  obtain ⟨C, hCpos, hgrow⟩ := re_log_riemannXi_div_canonicalProduct_le hrep
  -- `h` is entire, hence analytic, hence so is `deriv h`.
  have hderivdiff : Differentiable ℂ (deriv h) := fun x ↦
    ((analyticOnNhd_univ_iff_differentiable.mpr hdiff).deriv x (mem_univ x)).differentiableAt
  -- **Claim A**: `‖h z‖ ≤ C₀·R^{3/2}` for `‖z‖ ≤ R/2`.
  set C₀ : ℝ := 2 * C + 3 * ‖h 0‖ + 2 with hC₀def
  have claimA : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖h z‖ ≤ C₀ * R ^ (3 / 2 : ℝ) := by
    intro R hR z hz
    obtain ⟨R', hR'mem, hR'⟩ := hgrow R hR
    have hR'pos : 0 < R' := by linarith [hR'mem.1]
    have hRpow1 : (1 : ℝ) ≤ R ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hCR : 0 ≤ C * R ^ (3 / 2 : ℝ) :=
      mul_nonneg hCpos.le (Real.rpow_nonneg (by linarith) _)
    -- Maximum-modulus principle: `Re h ≤ C·R^{3/2}` on the whole closed ball `|w| ≤ R'`.
    have hmax : ∀ w : ℂ, ‖w‖ ≤ R' → (h w).re ≤ C * R ^ (3 / 2 : ℝ) := by
      intro w hw
      have hfront : ∀ ζ ∈ frontier (ball (0 : ℂ) R'),
          ‖Complex.exp (h ζ)‖ ≤ Real.exp (C * R ^ (3 / 2 : ℝ)) := fun ζ hζ ↦ by
        rw [frontier_ball 0 hR'pos.ne'] at hζ
        rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (hR' ζ (by simpa using mem_sphere_iff_norm.mp hζ))
      have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        hdiff.cexp.diffContOnCl hfront
        (by rw [closure_ball 0 hR'pos.ne']; simpa [mem_closedBall, dist_eq_norm] using hw)
      rw [Complex.norm_exp] at hle
      exact Real.exp_le_exp.mp hle
    -- Borel–Carathéodory for `h - h 0` on `|s| ≤ R'`, evaluated at radius `R'/2 ≥ R/2 ≥ ‖z‖`.
    have hbc := borelCaratheodory_closedBall (f := fun s ↦ h s - h 0) (z := z) (r := R' / 2)
      (M := C * R ^ (3 / 2 : ℝ) + ‖h 0‖ + 1) hR'pos
      ((analyticOn_univ_iff_differentiable.mpr (hdiff.sub_const (h 0))).mono (subset_univ _))
      (by simp) (by linarith [norm_nonneg (h 0)])
      (fun ζ hζ ↦ by
        rw [mem_closedBall, dist_eq_norm, sub_zero] at hζ
        simp only [Complex.sub_re]
        linarith [hmax ζ hζ, (neg_le_abs (h 0).re).trans (abs_re_le_norm (h 0))])
      (by linarith) (by simp only [mem_closedBall, dist_eq_norm, sub_zero]; linarith [hR'mem.1])
    rw [show R' - R' / 2 = R' / 2 by ring, mul_div_assoc, div_self (half_pos hR'pos).ne',
      mul_one] at hbc
    rw [hC₀def]
    nlinarith [hbc, norm_sub_norm_le (h z) (h 0), norm_nonneg (h 0),
      mul_nonneg (norm_nonneg (h 0)) (sub_nonneg.mpr hRpow1)]
  -- **Claim B**: `iteratedDeriv 2 h c = 0` for all `c`, by Cauchy's estimate on `sphere c (R/4)`.
  have claimB : ∀ c : ℂ, iteratedDeriv 2 h c = 0 := by
    intro c
    have htend : Tendsto (fun R : ℝ ↦ 32 * C₀ * R ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (32 * C₀)
    refine norm_le_zero_iff.mp <| ge_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop (4 * ‖c‖ + 2)] with R hR
    have hR2 : 2 ≤ R := by linarith [norm_nonneg c]
    have hRpos : 0 < R := by linarith
    set ρ : ℝ := R / 2 - ‖c‖ with hρdef
    have hρ4 : R / 4 ≤ ρ := by rw [hρdef]; linarith
    have hρpos : 0 < ρ := by linarith
    -- `sphere c ρ ⊆ closedBall 0 (R/2)`, so the Claim-A bound applies on it.
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρpos
      hdiff.diffContOnCl (fun z hz ↦ claimA R hR2 z (by
        have hzc := norm_sub_norm_le z c
        rw [mem_sphere_iff_norm.mp hz, hρdef] at hzc
        linarith))
    rw [show ((Nat.factorial 2 : ℕ) : ℝ) = 2 from by norm_num [Nat.factorial]] at hcauchy
    -- Convert the Cauchy bound `2·(C₀ R^{3/2})/ρ²` into `32·C₀·R^{-1/2}`.
    have hpowid : R ^ (3 / 2 : ℝ) / R ^ 2 = R ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_natCast R 2, ← Real.rpow_sub hRpos]; norm_num
    calc ‖iteratedDeriv 2 h c‖ ≤ 2 * (C₀ * R ^ (3 / 2 : ℝ)) / ρ ^ 2 := hcauchy
      _ ≤ 2 * (C₀ * R ^ (3 / 2 : ℝ)) / (R ^ 2 / 16) := by
          gcongr; nlinarith [hρ4, hρpos]
      _ = 32 * C₀ * (R ^ (3 / 2 : ℝ) / R ^ 2) := by ring
      _ = 32 * C₀ * R ^ (-(1 / 2) : ℝ) := by rw [hpowid]
  -- From `deriv (deriv h) ≡ 0`, `deriv h` is constant and `h` is affine.
  have hderivconst : ∀ x : ℂ, deriv h x = deriv h 0 := fun x ↦
    is_const_of_deriv_eq_zero hderivdiff
      (fun y ↦ by simpa [iteratedDeriv_succ, iteratedDeriv_one] using claimB y) x 0
  refine ⟨h 0, deriv h 0, fun s ↦ ?_⟩
  have key : h s - deriv h 0 * s = h 0 := by
    simpa using is_const_of_deriv_eq_zero (f := fun y : ℂ ↦ h y - deriv h 0 * y)
      (hdiff.sub (differentiable_id.const_mul _))
      (fun x ↦ by
        have hd : HasDerivAt (fun y : ℂ ↦ h y - deriv h 0 * y) (deriv h x - deriv h 0) x :=
          (hdiff x).hasDerivAt.sub (by simpa using (hasDerivAt_id x).const_mul (deriv h 0))
        rw [hd.deriv, hderivconst x]; ring) s 0
  linear_combination key

