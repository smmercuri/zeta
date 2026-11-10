/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannSiegel.Bound
public import Zeta.RiemannSiegel.InnerSharp

/-!
# The sharp outer saddle-point estimate

Companion to `Zeta/RiemannSiegel/InnerSharp.lean`: the region `|w| > W` of the contour, at the
sharp splitting radius `W = Zeta.RiemannSiegel.sharpSplitRadius t = (√T - 1)/(2√2)`
(`riemann_siegel_first.tex`, `lem:rsf_outer_sharp`). As in the crude estimate
`Zeta.RiemannSiegel.norm_integral_outer_le`, `e^Δ` and `1` are bounded separately there. At the
sharp radius `|w| = W` is `O(1)`, so two of the crude bounds are replaced by sharp ones.

The kernel's denominator is bounded below by `(99/200) e^{π|w|}`
(`Zeta.RiemannSiegel.mul_exp_le_norm_sin_pi_mul_line`), as recorded in
`Zeta.RiemannSiegel.norm_contourIntegrand_le'`. The phase enters the bound: by
`Zeta.RiemannSiegel.phase_le'` the true tail decays like `e^{-23w²/4}` on the near side
`w ≥ -a/2` of the contour. On the far side `w ≤ -a/2`, where the contour is at distance
`a/2 ≥ 7/4` from the origin, the weaker `e^{-πw²}` of `Zeta.RiemannSiegel.phase_le_of_le_neg_half`
is used.

The uniformity in `T` is run in the radius, through the antitonicity of
`x ↦ x e^{-bx²}` past `bx² ≥ 1`: each of the three Gaussian tails reduces to a rational inequality
at the threshold `T = 16`, where `W = 1.06066…` and `A = W - 1/4 = 0.81066…`.

## Main results

* `Zeta.RiemannSiegel.norm_integral_outer_le'` (`riemann_siegel_first.tex`,
  `lem:rsf_outer_sharp`): over `|w| > W` the model integrand against `e^Δ - 1` contributes at most
  `T^{-1}/20`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- An explicit lower bound for `√2`. -/
private theorem le_sqrt_two : (1.41421 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)

/-- The sharp phase estimate against the kernel's exponential decay, on the near side
`w ≥ -a/2` of the contour and outside the splitting radius (`riemann_siegel_first.tex`,
`eq:rsf_outer_sharp_pointwise`, first line). -/
private theorem phase_sub_pi_mul_abs_le {t a W w : ℝ} (ht : 0 ≤ t) (ha : 7 / 2 ≤ a)
    (hD : |t / (2 * π) - a ^ 2| ≤ a + 1 / 4) (hT : t / (2 * π) ≤ 2 * a ^ 2)
    (hW : 106 / 100 ≤ W) (hWa : 2 * Real.sqrt 2 * W ≤ a) (hw : W ≤ |w|)
    (hw' : -(a / 2) ≤ w) :
    phase t a w - π * |w| ≤ -(23 / 4 * w ^ 2) := by
  have hπ : (3.1415 : ℝ) ≤ π := Real.pi_gt_d4.le
  have hs2 : (1.41421 : ℝ) ≤ Real.sqrt 2 := le_sqrt_two
  have ha0 : (0 : ℝ) < a := by linarith
  have hph := phase_le' ht ha0 hT hw'
  set r : ℝ := |w|
  have hr0 : (0 : ℝ) < r := by linarith
  have hrsq : r ^ 2 = w ^ 2 := sq_abs w
  set D : ℝ := |t / (2 * π) - a ^ 2|
  -- the two consequences of `|T - a²| ≤ a + 1/4`: `ε ≤ 15/49` and `B ≤ 15π/7`
  have hε : D / a ^ 2 ≤ 15 / 49 := by
    rw [div_le_iff₀ (pow_pos ha0 2)]
    nlinarith [mul_nonneg (sub_nonneg.2 ha) (by linarith : (0 : ℝ) ≤ 15 * a + 7 / 2)]
  have hB : 2 * π * D / a ≤ 15 * π / 7 := by
    rw [div_le_iff₀ ha0]
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.2 ha),
      mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 2 * π)]
  -- the contour factor `ar/(a + r)`, increasing in `r`
  have hWa' : 2.82842 * W ≤ a := by
    nlinarith [mul_nonneg (sub_nonneg.2 hs2) (by linarith : (0 : ℝ) ≤ W)]
  have hQ : 73 / 100 * W ≤ a * r / (a + r) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.2 hWa') (by linarith : (0 : ℝ) ≤ r - 73 / 100 * W),
      mul_nonneg (by linarith : (0 : ℝ) ≤ W) (sub_nonneg.2 hw), sq_nonneg W]
  set Q : ℝ := a * r / (a + r) with hQdef
  set B : ℝ := 2 * π * D / a
  set ε : ℝ := D / a ^ 2
  -- the pointwise inequality, divided by `r = |w| > 0`
  have hbracket : 0 ≤ (2 * π - 23 / 4) * r + (1 - ε) * (2 * π * Q) - (B - π) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * π - 23 / 4)
      (by linarith : (0 : ℝ) ≤ r - 106 / 100), Real.pi_pos,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε)
        (by nlinarith [Real.pi_pos] : (0 : ℝ) ≤ 2 * π * Q - 2 * π * (73 / 100 * (106 / 100)))]
  have hden : a + r ≠ 0 := ne_of_gt (by linarith)
  have hkey : (1 - ε) * (2 * π * a * w ^ 2 / (a + r)) = r * ((1 - ε) * (2 * π * Q)) := by
    rw [hQdef, ← hrsq]
    field_simp
  rw [hkey] at hph
  nlinarith [mul_nonneg hr0.le hbracket]

/-- The pointwise majorant for the true integrand outside the unit interval: the model
integrand against `e^Δ`, which is the Riemann–Siegel integrand along `L(ν + ½)` renormalised by the
saddle factor (`riemann_siegel_first.tex`, `lem:rsf_outer_sharp`, the true tail). -/
private theorem sqrt_two_mul_norm_modelIntegrand_mul_exp_saddleDiscrepancy_le {t : ℝ} (ht : 0 < t)
    {ν : ℕ} (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) (hS : 4 ≤ Real.sqrt (t / (2 * π)))
    {w : ℝ} (hw : 1 ≤ |w|) :
    Real.sqrt 2 * ‖modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
        * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))‖
      ≤ 19 / 10 * Real.exp (phase t ((ν : ℝ) + 1 / 2) w - π * |w|) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := div_pos ht (by positivity)
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set a : ℝ := (ν : ℝ) + 1 / 2 with hadef
  have ha0 : (0 : ℝ) < a := by rw [hadef]; positivity
  have haS : S ≤ a + 1 / 2 := by rw [hadef]; linarith
  have ha : (7 : ℝ) / 2 ≤ a := by rw [hadef]; linarith
  have hS0 : (0 : ℝ) ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = t / (2 * π) := Real.sq_sqrt hT0.le
  -- the constant `P = (100/99)√2 2^{1/4} (S/a)^{1/2} ≤ 19/10`, via `T ≤ 1.07⁴a²`
  have h2rpow : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 1.19 := by
    rw [show (2 : ℝ) ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt 2) by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num]
    exact (Real.sqrt_le_left (by norm_num)).2 ((Real.sqrt_le_left (by norm_num)).2 (by norm_num))
  have hconst : Real.sqrt 2 * (100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ)))
      ≤ 19 / 10 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
    have hcore : a ^ (-(1 / 2) : ℝ) ≤ 1.07 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) :=
      rpow_neg_half_le_mul_rpow_neg_quarter ha0 hT0 (by norm_num)
        (by nlinarith [mul_le_mul haS haS hS0 (by linarith : (0 : ℝ) ≤ a + 1 / 2)])
    calc Real.sqrt 2 * (100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ)))
        = Real.sqrt 2 * (100 / 99) * 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) := by ring
      _ ≤ 1.41422 * (100 / 99) * 1.19 * (1.07 * (t / (2 * π)) ^ (-(1 / 4) : ℝ)) :=
          mul_le_mul (mul_le_mul (by linarith) h2rpow (by positivity) (by norm_num)) hcore
            (Real.rpow_nonneg ha0.le _) (by norm_num)
      _ ≤ 19 / 10 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
          nlinarith [Real.rpow_nonneg hT0.le (-(1 / 4) : ℝ)]
  rw [norm_modelIntegrand_mul_exp_saddleDiscrepancy ht ν w, ← mul_div_assoc,
    div_le_iff₀ (Real.rpow_pos_of_pos hT0 _)]
  calc Real.sqrt 2 * ‖contourIntegrand (1 / 2 + t * I) a w‖
      ≤ Real.sqrt 2 * (100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ))
          * Real.exp (phase t a w - π * |w|)) := by
        gcongr
        exact norm_contourIntegrand_le' ha0 hw
    _ = Real.sqrt 2 * (100 / 99 * (2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ)))
          * Real.exp (phase t a w - π * |w|) := by ring
    _ ≤ 19 / 10 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) * Real.exp (phase t a w - π * |w|) :=
        mul_le_mul_of_nonneg_right hconst (Real.exp_nonneg _)
    _ = 19 / 10 * Real.exp (phase t a w - π * |w|) * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by ring

/-- The pointwise majorant for the model integrand, its Gaussian numerator centred at
`-(½ - p)/2` (`riemann_siegel_first.tex`, `lem:rsf_outer_sharp`, the model tail). -/
private theorem sqrt_two_mul_norm_modelIntegrand_le {p : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2) (w : ℝ) :
    Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ 11 / 5 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  calc Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ Real.sqrt 2 * (Real.exp (π / 4)
          * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) / Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left (norm_modelIntegrand_le_exp_neg_mul_sq hκ w) hs2.le
    _ = Real.exp (π / 4) * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) := by field_simp
    _ ≤ 11 / 5 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) :=
        mul_le_mul_of_nonneg_right Real.exp_pi_div_four_le (Real.exp_nonneg _)

/-- A Gaussian tail against an inverse square: `c₁e^{-bA²}/(bA) ≤ c₂/S²`, from the threshold
bound `Ae^{-bA²} ≤ m` and the comparison `S² ≤ kA²`. -/
private theorem mul_exp_div_le_div_sq {b A S k m c₁ c₂ : ℝ} (hA0 : 0 < A) (hS0 : 0 < S)
    (hc₁ : 0 ≤ c₁) (hk : 0 ≤ k) (hb : 0 < b) (hSsq : S ^ 2 ≤ k * A ^ 2)
    (hkey : A * Real.exp (-b * A ^ 2) ≤ m) (hnum : c₁ * (k * m) ≤ c₂ * b) :
    c₁ * (Real.exp (-b * A ^ 2) / (b * A)) ≤ c₂ / S ^ 2 := by
  have hE0 : (0 : ℝ) < Real.exp (-b * A ^ 2) := Real.exp_pos _
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (pow_pos hS0 2)]
  linarith [mul_le_mul_of_nonneg_left hSsq (mul_nonneg hc₁ hE0.le),
    mul_le_mul_of_nonneg_left hkey (mul_nonneg (mul_nonneg hc₁ hk) hA0.le),
    mul_le_mul_of_nonneg_right hnum hA0.le]

/-- The near-side Gaussian tail is at most `T^{-1}/25` (`riemann_siegel_first.tex`,
`lem:rsf_outer_sharp`, the first of the three numerical steps). -/
private theorem outer_true_constant_le {S W : ℝ} (hW : 106 / 100 ≤ W)
    (hSW : S = 2 * Real.sqrt 2 * W + 1) :
    19 / 10 * (Real.exp (-(23 / 4) * W ^ 2) / (23 / 4 * W)) ≤ 1 / 25 / S ^ 2 := by
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  have hW0 : (0 : ℝ) < W := by linarith
  have hS0 : (0 : ℝ) < S := by rw [hSW]; nlinarith [le_sqrt_two]
  have hSsq : S ^ 2 ≤ 14.229 * W ^ 2 := by
    have hSle : S ≤ 3.772 * W := by rw [hSW]; nlinarith
    nlinarith
  -- the Gaussian factor at the threshold beats the quadratic
  have hthr : Real.exp (-(23 / 4) * (106 / 100 : ℝ) ^ 2) * 403 ≤ 1 := by
    rw [show -(23 / 4) * (106 / 100 : ℝ) ^ 2 = -(23 / 4 * (106 / 100 : ℝ) ^ 2) by ring]
    exact exp_neg_mul_le_one (n := 6) (by norm_num) (by norm_num)
  have hkey : W * Real.exp (-(23 / 4) * W ^ 2) ≤ 1 / 130 := by
    have hmono := pow_mul_exp_neg_mul_sq_le (b := 23 / 4) (A₀ := 106 / 100) (A := W) (k := 1)
      (by norm_num) (by norm_num) (by norm_num) hW
    nlinarith [Real.exp_pos (-(23 / 4) * (106 / 100 : ℝ) ^ 2)]
  exact mul_exp_div_le_div_sq hW0 hS0 (by norm_num) (by norm_num) (by norm_num) hSsq hkey
    (by norm_num)

/-- The far-side Gaussian tail is at most `T^{-1}/200` (`riemann_siegel_first.tex`,
`lem:rsf_outer_sharp`, the second of the three numerical steps). -/
private theorem outer_far_constant_le {S a : ℝ} (ha : 7 / 2 ≤ a) (hS0 : 0 < S)
    (hSa : S ≤ a + 1 / 2) :
    19 / 10 * (Real.exp (-π * (a / 2) ^ 2) / (π * (a / 2))) ≤ 1 / 200 / S ^ 2 := by
  have hπ : (3.1415 : ℝ) ≤ π := Real.pi_gt_d4.le
  have hSsq : S ^ 2 ≤ 256 / 49 * (a / 2) ^ 2 := by nlinarith
  -- the Gaussian factor at the threshold `a = 7/2`
  have hthr : Real.exp (-π * (7 / 4 : ℝ) ^ 2) * 2900 ≤ 1 := by
    rw [show -π * (7 / 4 : ℝ) ^ 2 = -(π * (7 / 4 : ℝ) ^ 2) by ring]
    exact exp_neg_mul_le_one (n := 8) (by norm_num) (by push_cast; nlinarith)
  have hkey : a / 2 * Real.exp (-π * (a / 2) ^ 2) ≤ 7 / 11600 := by
    have hmono := pow_mul_exp_neg_mul_sq_le (b := π) (A₀ := 7 / 4) (A := a / 2) (k := 1)
      Real.pi_pos (by norm_num) (by push_cast; nlinarith) (by linarith)
    nlinarith [Real.exp_pos (-π * (7 / 4 : ℝ) ^ 2)]
  exact mul_exp_div_le_div_sq (by linarith) hS0 (by norm_num) (by norm_num) Real.pi_pos hSsq hkey
    (by linarith)

/-- The model Gaussian tail is at most `T^{-1}/200` (`riemann_siegel_first.tex`,
`lem:rsf_outer_sharp`, the third of the three numerical steps). -/
private theorem outer_model_constant_le {S A : ℝ} (hA : 81 / 100 ≤ A) (hS0 : 0 < S)
    (hSA : S ≤ 5 * A) :
    11 / 5 * (Real.exp (-(4 * π) * A ^ 2) / (4 * π * A)) ≤ 1 / 200 / S ^ 2 := by
  have hπ : (3.1415 : ℝ) ≤ π := Real.pi_gt_d4.le
  have hA0 : (0 : ℝ) < A := by linarith
  have hSsq : S ^ 2 ≤ 25 * A ^ 2 := by nlinarith
  have hthr : Real.exp (-(4 * π) * (81 / 100 : ℝ) ^ 2) * 2900 ≤ 1 := by
    rw [show -(4 * π) * (81 / 100 : ℝ) ^ 2 = -(4 * π * (81 / 100 : ℝ) ^ 2) by ring]
    exact exp_neg_mul_le_one (n := 8) (by norm_num) (by push_cast; nlinarith)
  have hkey : A * Real.exp (-(4 * π) * A ^ 2) ≤ 81 / 290000 := by
    have hmono := pow_mul_exp_neg_mul_sq_le (b := 4 * π) (A₀ := 81 / 100) (A := A) (k := 1)
      (by positivity) (by norm_num) (by push_cast; nlinarith) hA
    nlinarith [Real.exp_pos (-(4 * π) * (81 / 100 : ℝ) ^ 2)]
  exact mul_exp_div_le_div_sq hA0 hS0 (by norm_num) (by norm_num) (by positivity) hSsq hkey
    (by linarith)

/-- The true tail of the outer region on the near side of the contour `w ≥ -a/2`. -/
private theorem integral_true_near_le {t p a W S : ℝ} (ht : 0 ≤ t)
    (hGint : Integrable fun w : ℝ ↦ modelIntegrand (p : ℂ) (1 / 2) w
      * exp (saddleDiscrepancy t (line a w)))
    (hGpt : ∀ w : ℝ, 1 ≤ |w| → Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
      * exp (saddleDiscrepancy t (line a w))‖ ≤ 19 / 10 * Real.exp (phase t a w - π * |w|))
    (ha : 7 / 2 ≤ a) (hD : |t / (2 * π) - a ^ 2| ≤ a + 1 / 4) (hTa : t / (2 * π) ≤ 2 * a ^ 2)
    (hW : 106 / 100 ≤ W) (hWa : 2 * Real.sqrt 2 * W ≤ a) (hSW : S = 2 * Real.sqrt 2 * W + 1) :
    ∫ w in (Set.Icc (-W) W)ᶜ ∩ Set.Ici (-(a / 2)),
        Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
          * exp (saddleDiscrepancy t (line a w))‖ ≤ 1 / 25 / S ^ 2 := by
  have hTint : Integrable fun w : ℝ ↦ 19 / 10 * Real.exp (-(23 / 4) * w ^ 2) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 23 / 4)).const_mul _
  refine (setIntegral_mono_on (hGint.norm.const_mul _).integrableOn hTint.integrableOn
    (measurableSet_Icc.compl.inter measurableSet_Ici) fun w hw ↦ ?_).trans ?_
  · simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le,
      Set.mem_Ici] at hw
    refine (hGpt w (by linarith)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (by norm_num))
    exact (phase_sub_pi_mul_abs_le ht ha hD hTa hW hWa hw.1.le hw.2).trans_eq (by ring)
  · refine (setIntegral_mono_set hTint.integrableOn (.of_forall fun w ↦ by positivity)
      Set.inter_subset_left.eventuallyLE).trans ?_
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (integral_compl_Icc_exp_neg_mul_sq_le
      (by norm_num : (0 : ℝ) < 23 / 4) (by linarith : (0 : ℝ) < W))
      (by norm_num)).trans (outer_true_constant_le hW hSW)

/-- The true tail of the outer region on the far side of the contour `w ≤ -a/2`. -/
private theorem integral_true_far_le {t p a W S : ℝ}
    (hGint : Integrable fun w : ℝ ↦ modelIntegrand (p : ℂ) (1 / 2) w
      * exp (saddleDiscrepancy t (line a w)))
    (hGpt : ∀ w : ℝ, 1 ≤ |w| → Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
      * exp (saddleDiscrepancy t (line a w))‖ ≤ 19 / 10 * Real.exp (phase t a w - π * |w|))
    (ha : 7 / 2 ≤ a) (hTa' : 2 / π * a ^ 2 ≤ t / (2 * π)) (hS0 : 0 < S) (haS : S ≤ a + 1 / 2) :
    ∫ w in (Set.Icc (-W) W)ᶜ \ Set.Ici (-(a / 2)),
        Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
          * exp (saddleDiscrepancy t (line a w))‖ ≤ 1 / 200 / S ^ 2 := by
  have hFarint : Integrable fun w : ℝ ↦ 19 / 10 * Real.exp (-π * w ^ 2) :=
    (integrable_exp_neg_mul_sq Real.pi_pos).const_mul _
  have hlt : ∀ w ∈ (Set.Icc (-W) W)ᶜ \ Set.Ici (-(a / 2)), w < -(a / 2) := fun w hw ↦ by
    simpa only [Set.mem_Ici, not_le] using hw.2
  refine (setIntegral_mono_on (hGint.norm.const_mul _).integrableOn hFarint.integrableOn
    (measurableSet_Icc.compl.diff measurableSet_Ici) fun w hw ↦ ?_).trans ?_
  · have hwa : w ≤ -(a / 2) := (hlt w hw).le
    refine (hGpt w (by rw [abs_of_neg (by linarith)]; linarith)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
    have hph := phase_le_of_le_neg_half (by linarith : (0 : ℝ) < a) hTa' hwa
    have habs : (0 : ℝ) ≤ π * |w| := by positivity
    linarith
  · have hsub : (Set.Icc (-W) W)ᶜ \ Set.Ici (-(a / 2)) ⊆ (Set.Icc (-(a / 2)) (a / 2))ᶜ :=
      fun w hw ↦ by
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
        exact Or.inl (hlt w hw)
    refine (setIntegral_mono_set hFarint.integrableOn (.of_forall fun w ↦ by positivity)
      hsub.eventuallyLE).trans ?_
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (integral_compl_Icc_exp_neg_mul_sq_le Real.pi_pos
      (by linarith : (0 : ℝ) < a / 2)) (by norm_num)).trans (outer_far_constant_le ha hS0 haS)

/-- The tail of the model integrand alone over the outer region `|w| > W`. -/
private theorem integral_model_le {p W S : ℝ} (hHint : Integrable (modelIntegrand (p : ℂ) (1 / 2)))
    (hHpt : ∀ w : ℝ, Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ 11 / 5 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2))
    (hd : |(1 / 2 - p) / 2| ≤ 1 / 4) (hA : 81 / 100 ≤ W - 1 / 4) (hS0 : 0 < S)
    (hSA : S ≤ 5 * (W - 1 / 4)) :
    ∫ w in (Set.Icc (-W) W)ᶜ, Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ 1 / 200 / S ^ 2 := by
  have hπ : (3.1415 : ℝ) ≤ π := Real.pi_gt_d4.le
  have hbA : (1 : ℝ) ≤ 4 * π * (W - 1 / 4) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 81 / 100)
      hA 2) (by positivity : (0 : ℝ) ≤ 4 * π)
    linarith
  have hMint : Integrable fun w : ℝ ↦ 11 / 5 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) :=
    ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 4 * π)).comp_add_right
      ((1 / 2 - p) / 2)).const_mul _
  refine (setIntegral_mono_on (hHint.norm.const_mul _).integrableOn hMint.integrableOn
    measurableSet_Icc.compl fun w _ ↦ hHpt w).trans ?_
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (integral_compl_Icc_exp_neg_mul_sq_comp_add_right_le
    (by positivity : (0 : ℝ) < 4 * π) (by linarith : (0 : ℝ) < W - 1 / 4) (by linarith) hbA)
    (by norm_num)).trans (outer_model_constant_le hA hS0 hSA)

/-- The sharp outer saddle-point estimate (`riemann_siegel_first.tex`, `lem:rsf_outer_sharp`):
the contribution to the model integral of the region `|w| > W = (√T - 1)/(2√2)` is at most
`T^{-1}/20`. -/
theorem norm_integral_outer_le' {t : ℝ} (ht : 16 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖(1 + I) * ∫ w in (Set.Icc (-sharpSplitRadius t) (sharpSplitRadius t))ᶜ,
        modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖
      ≤ 1 / 20 / (t / (2 * π)) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  have hπ : (3.1415 : ℝ) ≤ π := Real.pi_gt_d4.le
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  have hS4 : 4 ≤ Real.sqrt (t / (2 * π)) := four_le_sqrt ht
  have hκ : |1 / 2 - (Real.sqrt (t / (2 * π)) - ν)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  -- the two pointwise majorants and the three integrability facts, before the abbreviations
  have hGpt := fun (w : ℝ) (hw : (1 : ℝ) ≤ |w|) ↦
    sqrt_two_mul_norm_modelIntegrand_mul_exp_saddleDiscrepancy_le ht0 hν' hS4 hw
  have hHpt := sqrt_two_mul_norm_modelIntegrand_le hκ
  have hGint := integrable_modelIntegrand_mul_exp_saddleDiscrepancy ht0 ν
  have hHint := integrable_modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ)
    (show (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 by norm_num)
  have hFint := integrable_modelIntegrand_mul_exp_saddleDiscrepancy_sub_one ht0 ν
  -- abbreviations: the saddle `√T`, the fractional part `p`, the crossing point `a`, the radii
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set p : ℝ := S - (ν : ℝ)
  set a : ℝ := (ν : ℝ) + 1 / 2 with hadef
  set W : ℝ := sharpSplitRadius t with hWdef
  have hTS : S ^ 2 = t / (2 * π) := Real.sq_sqrt hT0.le
  have hSW : S = 2 * Real.sqrt 2 * W + 1 := by
    rw [hWdef, hSdef, sharpSplitRadius]
    field_simp
    ring
  have hW106 : 106 / 100 ≤ W := by
    rw [hWdef, sharpSplitRadius, ← hSdef, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)]
    nlinarith
  have ha : (7 : ℝ) / 2 ≤ a := by rw [hadef]; linarith
  have haS : S ≤ a + 1 / 2 := by rw [hadef]; linarith
  have haS' : a ≤ S + 1 / 2 := by rw [hadef]; linarith
  clear_value S p a W
  have hS0 : (0 : ℝ) < S := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hD : |t / (2 * π) - a ^ 2| ≤ a + 1 / 4 :=
    abs_sub_sq_le hTS (by linarith) (by linarith) haS'
  have hTa : t / (2 * π) ≤ 2 * a ^ 2 := by rw [← hTS]; nlinarith
  have hTa' : 2 / π * a ^ 2 ≤ t / (2 * π) := by
    rw [← hTS, div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos]
    nlinarith [mul_nonneg (sub_nonneg.2 hπ) (sq_nonneg S)]
  have hWa : 2 * Real.sqrt 2 * W ≤ a := by linarith
  have hA81 : 81 / 100 ≤ W - 1 / 4 := by linarith
  have hSA : S ≤ 5 * (W - 1 / 4) := by
    nlinarith [mul_le_mul_of_nonneg_right hs2u hW0.le]
  have hd : |(1 / 2 - p) / 2| ≤ 1 / 4 := by
    rw [abs_div, abs_two]
    linarith [(abs_le.1 hκ).1, (abs_le.1 hκ).2]
  -- the three tails
  have hnear := integral_true_near_le ht0.le hGint hGpt ha hD hTa hW106 hWa hSW
  have hfar := integral_true_far_le (W := W) hGint hGpt ha hTa' hS0 haS
  have hmodel := integral_model_le hHint hHpt hd hA81 hS0 hSA
  -- the assembly
  have hGsplit := integral_inter_add_sdiff (s := (Set.Icc (-W) W)ᶜ)
    (t := Set.Ici (-(a / 2))) measurableSet_Ici
    ((hGint.norm.const_mul (Real.sqrt 2)).integrableOn (s := (Set.Icc (-W) W)ᶜ))
  calc ‖(1 + I) * ∫ w in (Set.Icc (-W) W)ᶜ, modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line a w)) - 1)‖
      ≤ Real.sqrt 2 * ∫ w in (Set.Icc (-W) W)ᶜ, ‖modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line a w)) - 1)‖ :=
        norm_one_add_I_mul_integral_le _
    _ = ∫ w in (Set.Icc (-W) W)ᶜ, Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line a w)) - 1)‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ w in (Set.Icc (-W) W)ᶜ, (Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
            * exp (saddleDiscrepancy t (line a w))‖
          + Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖) := by
        refine setIntegral_mono_on (hFint.norm.const_mul _).integrableOn
          ((hGint.norm.const_mul _).add (hHint.norm.const_mul _)).integrableOn
          measurableSet_Icc.compl fun w _ ↦ ?_
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_mul_sub_one_le _ _) hs2.le
    _ = (∫ w in (Set.Icc (-W) W)ᶜ, Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w
            * exp (saddleDiscrepancy t (line a w))‖)
          + ∫ w in (Set.Icc (-W) W)ᶜ, Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖ :=
        integral_add (hGint.norm.const_mul _).integrableOn (hHint.norm.const_mul _).integrableOn
    _ ≤ (1 / 25 / S ^ 2 + 1 / 200 / S ^ 2) + 1 / 200 / S ^ 2 := by
        rw [← hGsplit]
        exact add_le_add (add_le_add hnear hfar) hmodel
    _ = 1 / 20 / S ^ 2 := by ring
    _ = 1 / 20 / (t / (2 * π)) := by rw [hTS]

end Zeta.RiemannSiegel
