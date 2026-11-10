/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.ArgZeta.ShiftIdentity
public import Zeta.ArgZeta.Archimedean
public import Zeta.ArgZeta.Basic

/-!
# Lehman's lower bound on the Littlewood integral `I(t)`

The lower bound `-I(t) ≤ a₂ + (3/4)d² log t` on the log-modulus line integral
`I(t) = ∫_{1/2}^∞ log‖ζ(σ+it)‖ dσ` (`thm:ll_main`, `lem:lb_I_lower`).

## Main results

- `le_logNormZetaIntegral_of_le`: parametric core, with the pairing constant `c ≥ 2` free.
- `le_logNormZetaIntegral_of`: its `c = 5/2` case.
- `le_logNormZetaIntegral` (`thm:ll_main`): the bound with `a₂` existential.
-/
@[expose] public section


open Complex Filter Topology MeasureTheory Set

open scoped Real


/-- No enumerated zero of `ξ` lies at ordinate `t`, when `ζ` has no zero at ordinate `t` on the
ray `σ ≥ 1/2`. -/
private lemma riemannXiZeros_im_ne_of_forall_riemannZeta_ne {t : ℝ}
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0)
    (i : RiemannXiZerosIndex) : (riemannXiZeros i).im ≠ t := by
  intro hi
  -- no zero of `ξ` at ordinate `t` may have `Re ≥ 1/2`
  have key : ∀ ρ : ℂ, riemannXi ρ = 0 → ρ.im = t → (1 / 2 : ℝ) ≤ ρ.re → False :=
    fun ρ hξ hρ hge ↦ hzero ρ.re hge (by
      rw [show ((ρ.re : ℝ) : ℂ) + Complex.I * t = ρ from Complex.ext (by simp) (by simp [hρ])]
      exact riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)
  set ρ := riemannXiZeros i
  have hξ : riemannXi ρ = 0 := riemannXi_riemannXiZeros_eq_zero i
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with hge | hlt
  · exact key ρ hξ hi hge
  · -- otherwise the reflected zero `1 - conj ρ` has `Re = 1 - Re ρ > 1/2` and the same ordinate
    refine key (1 - starRingEnd ℂ ρ) (by rw [riemannXi_one_sub, riemannXi_conj, hξ, map_zero])
      (by simp [hi]) ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith

/-- The `ξ`-to-`ζ` log-modulus split along the line `σ + it`. The archimedean part is
`logNormGammaArchimedean t σ = log‖½ (σ+it)((σ+it)-1) Γ_ℝ(σ+it)‖`. -/
private lemma log_norm_riemannXi_eq {t σ : ℝ} (htne : t ≠ 0) (hσ : 0 < σ)
    (hζ : riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    Real.log ‖riemannXi ((σ : ℂ) + Complex.I * t)‖
      = logNormGammaArchimedean t σ + Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ := by
  have hz0 : (σ : ℂ) + Complex.I * t ≠ 0 := archLine_ne_zero htne σ
  have hz1 : (σ : ℂ) + Complex.I * t ≠ 1 := sub_ne_zero.mp (archLine_sub_one_ne_zero htne σ)
  have hΓ : Complex.Gammaℝ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hσ)
  rw [riemannXi_eq_prefactor_mul hz0 hz1 hΓ, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr (prefactor_ne_zero_of hz0 hz1 hΓ))
      (norm_ne_zero_iff.mpr hζ)]
  rfl

/-- Continuity of `σ ↦ log‖ζ(σ+it)‖` on `[1/2, ∞)`, away from the zeros excluded by hypothesis
(and the pole `s = 1`, which has ordinate `0 ≠ t`). -/
private lemma continuousOn_log_norm_riemannZeta_Ici {t : ℝ} (htne : t ≠ 0)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    ContinuousOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      (Set.Ici (1 / 2)) := by
  refine continuousOn_log_norm_riemannZeta (fun σ _ h ↦ ?_) hzero
  have him : ((σ : ℂ) + Complex.I * t).im = t := by simp
  rw [h] at him; simp only [Complex.one_im] at him; exact htne him.symm

/-- The width-`d` strip integral `∫_{Ioo s (s+d)} f` as an interval integral of the shifted
integrand over `[0, d]`. -/
private lemma intervalIntegral_zero_shift_eq_Ioo (f : ℝ → ℝ) {s d b : ℝ} (hd : 0 ≤ d)
    (hb : s + d = b) : (∫ x in (0 : ℝ)..d, f (x + s)) = ∫ σ in Set.Ioo s b, f σ := by
  have h := intervalIntegral.Ioo_eq_comp_add_right f (a := 0) (b := d) (s := s) hd
  rw [zero_add, show d + s = b from by rw [← hb]; ring] at h
  exact h.symm

/-- Parametric core of Lehman's lower bound on `I(t)`, parametric in the pairing constant
`c ≥ 2`. Given explicit constants for the shift (`hκ`), the archimedean strip difference
(`hCa`), the explicit formula (`hCψ`) and the tail (`hCt`), the additive constant of
`-I(t) ≤ a₂ + ((c-1)/2)d² log t` is `a₂ = c·d² Cψ + d² κ + 2 Ct + Ca`. -/
theorem le_logNormZetaIntegral_of_le {d κ Ca Cψ Ct : ℝ} (hd : 1 / 2 < d)
    (hκ : ∀ s : ℂ, (∀ i, s ≠ riemannXiZeros i) → (∀ i, s + d ≠ riemannXiZeros i) →
        ∑' i, (Real.log ‖s + ↑d - riemannXiZeros i‖ - Real.log ‖s - riemannXiZeros i‖)
          = Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖ - ↑d * κ)
    (hCa : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (d ^ 2 / 2) * Real.log t - Ca ≤
        (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
          ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ)
    (hCψ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      ∑' i, (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
        ≤ 1 / 2 * Real.log t + Cψ)
    (hCt : ∀ t : ℝ,
      (-Ct ≤ ∫ σ in Set.Ioi (1 / 2 + d), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) ∧
      (-Ct ≤ ∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d),
              Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖))
    {c : ℝ} (hc : 2 ≤ c) :
    ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤
        (c * d ^ 2 * Cψ + d ^ 2 * κ + 2 * Ct + Ca) + (c - 1) / 2 * d ^ 2 * Real.log t := by
  intro t ht hzero
  have hd0 : (0 : ℝ) < d := by linarith
  have htne : t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) ht)
  have ht_im : ∀ i, (riemannXiZeros i).im ≠ t :=
    riemannXiZeros_im_ne_of_forall_riemannZeta_ne hzero
  have hZc := continuousOn_log_norm_riemannZeta_Ici htne hzero
  have hg := integrableOn_log_norm_riemannZeta_Ioi htne hzero
  have hCa' := hCa t ht
  have hCt1 := (hCt t).1
  have hCt2 := (hCt t).2
  -- `Z` is the `ζ`-integrand, `A` the archimedean one; the whole assembly is linear in them
  set Z : ℝ → ℝ := fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ with hZdef
  set A : ℝ → ℝ := fun σ : ℝ ↦ logNormGammaArchimedean t σ with hAdef
  -- pointwise on `[0, d]`: the zero sum is the `ξ`-shift difference, split into `A` and `Z`
  have hsplit : Set.EqOn (fun x ↦ ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x)
      (fun x ↦ A (x + (1 / 2 + d)) + Z (x + (1 / 2 + d)) - (A (x + 1 / 2) + Z (x + 1 / 2))
        - d * κ) (Set.uIcc 0 d) := by
    intro x hx
    rw [Set.uIcc_of_le hd0.le, Set.mem_Icc] at hx
    have hne : ∀ y : ℂ, y.im = t → ∀ i, y ≠ riemannXiZeros i := fun y hy i h ↦ ht_im i (h ▸ hy)
    have key : ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x
        = Real.log ‖riemannXi ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ))‖
          - Real.log ‖riemannXi ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I)‖ - d * κ := by
      rw [← hκ _ (hne _ (by simp)) (hne _ (by simp))]
      exact tsum_congr fun i ↦ by rw [shiftLogIntegrand]
    simp only [hZdef, hAdef]
    rw [key,
      show (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)
          = (((x + (1 / 2 + d) : ℝ) : ℂ) + Complex.I * t) from by push_cast; ring,
      show (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I = (((x + 1 / 2 : ℝ) : ℂ) + Complex.I * t) from by
        push_cast; ring,
      log_norm_riemannXi_eq htne (by linarith [hx.1] : (0 : ℝ) < x + (1 / 2 + d))
        (hzero _ (by linarith [hx.1])),
      log_norm_riemannXi_eq htne (by linarith [hx.1] : (0 : ℝ) < x + 1 / 2)
        (hzero _ (by linarith [hx.1]))]
  -- interval integrabilities and the four strip substitutions, uniformly in the shift `s`
  have iA : ∀ s : ℝ, IntervalIntegrable (fun x ↦ A (x + s)) volume 0 d := fun s ↦
    ((continuous_logNormGammaArchimedean htne).comp (by fun_prop)).intervalIntegrable 0 d
  have iZ : ∀ s : ℝ, 1 / 2 ≤ s → IntervalIntegrable (fun x ↦ Z (x + s)) volume 0 d := fun s hs ↦ by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hd0.le]
    exact hZc.comp (by fun_prop) fun x hx ↦ by
      simp only [Set.mem_Icc] at hx; simp only [Set.mem_Ici]; linarith [hx.1]
  have eA1 := intervalIntegral_zero_shift_eq_Ioo A (s := 1 / 2) hd0.le rfl
  have eA2 := intervalIntegral_zero_shift_eq_Ioo A (s := 1 / 2 + d) (b := 1 / 2 + 2 * d) hd0.le
    (by ring)
  have eZ1 := intervalIntegral_zero_shift_eq_Ioo Z (s := 1 / 2) hd0.le rfl
  have eZ2 := intervalIntegral_zero_shift_eq_Ioo Z (s := 1 / 2 + d) (b := 1 / 2 + 2 * d) hd0.le
    (by ring)
  -- the integral of the zero sum, in terms of the four strip integrals
  have hIeq : (∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x)
      = ((∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), A σ)
            - ∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), A σ)
        + ((∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), Z σ)
            - ∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), Z σ) - d ^ 2 * κ := by
    have j1 := (iA (1 / 2)).add (iZ (1 / 2) le_rfl)
    have j2 := (iA (1 / 2 + d)).add (iZ (1 / 2 + d) (by linarith))
    rw [intervalIntegral.integral_congr hsplit,
      intervalIntegral.integral_sub (j2.sub j1) intervalIntegrable_const,
      intervalIntegral.integral_sub j2 j1,
      intervalIntegral.integral_add (iA (1 / 2 + d)) (iZ (1 / 2 + d) (by linarith)),
      intervalIntegral.integral_add (iA (1 / 2)) (iZ (1 / 2) le_rfl),
      intervalIntegral.integral_const, eA2, eZ2, eA1, eZ1]
    simp only [smul_eq_mul, sub_zero]
    ring
  -- the booker bound composed with the explicit-formula bound, read on the four strip integrals
  have hSb : ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      ≤ c / 2 * d ^ 2 * Real.log t + c * d ^ 2 * Cψ := by
    have h := (integral_tsum_log_norm_shift_le_of hd ht_im hc).trans
      (mul_le_mul_of_nonneg_left (hCψ t ht) (mul_nonneg (by linarith : (0 : ℝ) ≤ c) (sq_nonneg d)))
    linarith [h]
  rw [tsum_shiftLogIntegral_eq_intervalIntegral_tsum hd ht_im, hIeq] at hSb
  -- split `I(t)` at `1/2 + d` and assemble linearly
  have hIt : logNormZetaIntegral t
      = (∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), Z σ) + ∫ σ in Set.Ioi (1 / 2 + d), Z σ := by
    simp only [hZdef, logNormZetaIntegral]
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (1 / 2 : ℝ) ≤ 1 / 2 + d by linarith),
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hg.mono_set Set.Ioc_subset_Ioi_self) (hg.mono_set (Set.Ioi_subset_Ioi (by linarith))),
      integral_Ioc_eq_integral_Ioo]
  rw [hIt]
  nlinarith [hSb, hCa', hCt1, hCt2]

/-- The `c = 5/2` case of `le_logNormZetaIntegral_of_le`, where `(c-1)/2 = 3/4`. -/
theorem le_logNormZetaIntegral_of {d κ Ca Cψ Ct : ℝ} (hd : 1 / 2 < d)
    (hκ : ∀ s : ℂ, (∀ i, s ≠ riemannXiZeros i) → (∀ i, s + d ≠ riemannXiZeros i) →
        ∑' i, (Real.log ‖s + ↑d - riemannXiZeros i‖ - Real.log ‖s - riemannXiZeros i‖)
          = Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖ - ↑d * κ)
    (hCa : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (d ^ 2 / 2) * Real.log t - Ca ≤
        (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
          ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ)
    (hCψ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      ∑' i, (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
        ≤ 1 / 2 * Real.log t + Cψ)
    (hCt : ∀ t : ℝ,
      (-Ct ≤ ∫ σ in Set.Ioi (1 / 2 + d), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) ∧
      (-Ct ≤ ∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d),
              Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)) :
    ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤
        (5 / 2 * d ^ 2 * Cψ + d ^ 2 * κ + 2 * Ct + Ca) + 3 / 4 * d ^ 2 * Real.log t := by
  intro t ht hzero
  linarith [le_logNormZetaIntegral_of_le hd hκ hCa hCψ hCt (c := 5 / 2) (by norm_num) t ht hzero]

/-- Lehman's lower bound on `I(t)` (`thm:ll_main`, `lem:lb_I_lower`). For strip depth
`1/2 < d ≤ 2` there is a `t`-independent constant `a₂` with `-I(t) ≤ a₂ + (3/4)d² log t` at every
`t ≥ 168π` that is not an ordinate of a zero of `ζ` on the ray `{σ + it : σ ≥ 1/2}`. -/
theorem le_logNormZetaIntegral {d : ℝ} (hd : 1 / 2 < d) (hd' : d ≤ 2) :
    ∃ a₂ : ℝ, ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ a₂ + 3 / 4 * d ^ 2 * Real.log t := by
  obtain ⟨κ, hκ⟩ := exists_const_tsum_log_norm_riemannXiZeros_shift_eq
  obtain ⟨Ca, hCa⟩ := logNormGammaArchimedean_strip_diff_ge hd hd'
  obtain ⟨Cψ, hCψ⟩ := tsum_re_inv_riemannXiZeros_sub_le hd
  obtain ⟨Ct, hCt⟩ := logNormZetaIntegral_tail_ge hd
  exact ⟨5 / 2 * d ^ 2 * Cψ + d ^ 2 * κ + 2 * Ct + Ca,
    le_logNormZetaIntegral_of hd (fun s hs hsd ↦ hκ s d hs hsd) hCa hCψ hCt⟩

