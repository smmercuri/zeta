/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gamma.HalfPlane
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# A holomorphic branch of `log Γ` on the right half-plane

A holomorphic branch of `log Γ` on `{z : ℂ | 0 < z.re}`, which mathlib does not provide.

## Main definitions

* `Complex.logGamma`: the holomorphic branch of `log Γ` on `{z : ℂ | 0 < z.re}`, normalised so
  that `logGamma 1 = 0`.

## Main results

* `Complex.hasDerivAt_logGamma`: `(log Γ)' = digamma` on the right half-plane;
* `Complex.cexp_logGamma`: `exp (log Γ w) = Γ w`;
* `Complex.logGamma_ofReal`: on the positive real axis it agrees with `Real.log (Real.Gamma x)`;
* `Complex.logGamma_add_one`: the functional equation `log Γ (z+1) = Log z + log Γ z`;
* `Complex.logGamma_eq_sub_sum_log_add`: the exact integer shift.
-/
@[expose] public section


open Filter Topology Set
open scoped ComplexConjugate Real Nat

namespace Complex

/-- An (arbitrary) holomorphic primitive of `Complex.digamma` on the right half-plane. -/
noncomputable def logGammaAux : ℂ → ℂ :=
  Classical.choose (Convex.exists_forall_hasDerivWithinAt (convex_halfSpace_re_gt 0)
    differentiableOn_digamma_re_pos)

private lemma logGammaAux_hasDerivWithinAt {w : ℂ} (hw : 0 < w.re) :
    HasDerivWithinAt logGammaAux (Complex.digamma w) {z : ℂ | 0 < z.re} w :=
  Classical.choose_spec (Convex.exists_forall_hasDerivWithinAt (convex_halfSpace_re_gt 0)
    differentiableOn_digamma_re_pos) w hw

/-- The holomorphic branch of `log Γ` on the right half-plane `{z : ℂ | 0 < z.re}`, normalised so
that `logGamma 1 = 0`. -/
noncomputable def logGamma (w : ℂ) : ℂ := logGammaAux w - logGammaAux 1

/-- The branch is normalised: `log Γ 1 = 0`. -/
@[simp]
theorem logGamma_one : logGamma 1 = 0 := sub_self _

/-- The defining property of the branch: its derivative is the digamma function. -/
theorem hasDerivAt_logGamma {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt logGamma (Complex.digamma w) w :=
  ((logGammaAux_hasDerivWithinAt hw).hasDerivAt ((isOpen_re_gt 0).mem_nhds hw)).sub_const
    (logGammaAux 1)

/-- `exp (log Γ w) = Γ w` on the right half-plane. -/
theorem cexp_logGamma {w : ℂ} (hw : 0 < w.re) :
    Complex.exp (logGamma w) = Complex.Gamma w := by
  have hf : DifferentiableOn ℂ (fun z ↦ Complex.exp (logGamma z)) {z : ℂ | 0 < z.re} :=
    fun z hz ↦ ((hasDerivAt_logGamma hz).cexp).differentiableAt.differentiableWithinAt
  have hfn : ∀ z ∈ {z : ℂ | 0 < z.re}, Complex.exp (logGamma z) ≠ 0 :=
    fun z _ ↦ Complex.exp_ne_zero _
  have hlog : EqOn (logDeriv (fun z ↦ Complex.exp (logGamma z)))
      (logDeriv Complex.Gamma) {z : ℂ | 0 < z.re} := by
    intro z hz
    have hd : deriv (fun z ↦ Complex.exp (logGamma z)) z
        = Complex.exp (logGamma z) * Complex.digamma z :=
      ((hasDerivAt_logGamma hz).cexp).deriv
    rw [logDeriv_apply, logDeriv_apply, hd, mul_comm, mul_div_assoc,
      div_self (Complex.exp_ne_zero _), mul_one, Complex.digamma_def, logDeriv_apply]
  obtain ⟨c, -, hce⟩ := (logDeriv_eqOn_iff hf differentiableOn_Gamma_re_pos (isOpen_re_gt 0)
    isPreconnected_re_pos (fun _ hz ↦ Complex.Gamma_ne_zero_of_re_pos hz) hfn).mp hlog
  have hc1 : c = 1 := by
    simpa [logGamma_one, Complex.Gamma_one, Pi.smul_apply, smul_eq_mul]
      using (hce (by simp : (1 : ℂ) ∈ {z : ℂ | 0 < z.re})).symm
  simpa [Pi.smul_apply, smul_eq_mul, hc1] using hce (show w ∈ {z : ℂ | 0 < z.re} from hw)

/-- The digamma function commutes with complex conjugation, on all of `ℂ`. -/
theorem digamma_conj (s : ℂ) :
    Complex.digamma (conj s) = conj (Complex.digamma s) := by
  have hΓeq : (conj ∘ Complex.Gamma ∘ conj) = Complex.Gamma := by
    funext z; simp [Function.comp, Complex.Gamma_conj]
  have hderiv : deriv Complex.Gamma (conj s) = conj (deriv Complex.Gamma s) := by
    simpa using congrArg conj (congrFun (by rw [← deriv_conj_conj, hΓeq] :
      conj ∘ deriv Complex.Gamma ∘ conj = deriv Complex.Gamma) s)
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply, hderiv, Complex.Gamma_conj, map_div₀]

/-- On the positive real axis the branch is real-valued. -/
theorem logGamma_im_ofReal {x : ℝ} (hx : 0 < x) :
    (logGamma (x : ℂ)).im = 0 := by
  have hψderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ (logGamma (u : ℂ)).im) 0 t := by
    intro t ht
    have htre : 0 < ((t : ℂ)).re := by simpa using ht
    have hc : HasDerivAt (fun u : ℝ ↦ logGamma (u : ℂ)) (Complex.digamma (t : ℂ)) t :=
      (hasDerivAt_logGamma htre).comp_ofReal
    have him : HasDerivAt (fun u : ℝ ↦ Complex.imCLM (logGamma (u : ℂ)))
        (Complex.imCLM (Complex.digamma (t : ℂ))) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hc
    have hreal : (Complex.digamma (t : ℂ)).im = 0 :=
      Complex.conj_eq_iff_im.mp <| by
        simpa [Complex.conj_ofReal] using (digamma_conj (t : ℂ)).symm
    simpa only [Complex.imCLM_apply, hreal] using him
  simpa [Complex.ofReal_one] using isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun u hu ↦ (hψderiv u hu).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ (hψderiv u hu).deriv) hx (mem_Ioi.mpr one_pos)

/-- The branch agrees with the real `log Γ` on the positive real axis. -/
theorem logGamma_ofReal {x : ℝ} (hx : 0 < x) :
    logGamma (x : ℂ) = (Real.log (Real.Gamma x) : ℂ) := by
  have hre : Complex.exp (logGamma (x : ℂ)) = (Real.Gamma x : ℂ) := by
    rw [cexp_logGamma (by simpa using hx), Complex.Gamma_ofReal]
  have hreal : logGamma (x : ℂ) = ((logGamma (x : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [logGamma_im_ofReal hx]
  rw [hreal, ← Complex.ofReal_exp] at hre
  have hlog : (logGamma (x : ℂ)).re = Real.log (Real.Gamma x) := by
    rw [← Complex.ofReal_injective hre, Real.log_exp]
  rw [hreal, hlog]

/-- Functional equation of the branch: `log Γ (z + 1) = Log z + log Γ z` for `Re z > 0`, where
`Log` is the principal complex logarithm. -/
theorem logGamma_add_one {z : ℂ} (hz : 0 < z.re) :
    logGamma (z + 1) = Complex.log z + logGamma z := by
  set S : Set ℂ := {w : ℂ | 0 < w.re} with hS
  set k : ℂ → ℂ := fun v ↦ logGamma (v + 1) - Complex.log v - logGamma v with hk
  have hopen : IsOpen S := isOpen_re_gt 0
  have hpre : IsPreconnected S := isPreconnected_re_pos
  -- the difference `k` has vanishing derivative on the right half-plane
  have hderiv : ∀ w ∈ S, HasDerivAt k 0 w := by
    intro w hw
    have hw' : (0 : ℝ) < w.re := hw
    have hw1 : 0 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
    have hslit : w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hw')
    have hd1 : HasDerivAt (fun v : ℂ ↦ logGamma (v + 1)) (Complex.digamma (w + 1)) w := by
      have := (hasDerivAt_logGamma hw1).comp w ((hasDerivAt_id w).add_const 1)
      simpa [Function.comp_def] using this
    have hd2 : HasDerivAt Complex.log w⁻¹ w := Complex.hasDerivAt_log hslit
    have hd3 : HasDerivAt logGamma (Complex.digamma w) w := hasDerivAt_logGamma hw'
    have hval : Complex.digamma (w + 1) - w⁻¹ - Complex.digamma w = 0 := by
      rw [Complex.digamma_apply_add_one w (ne_neg_natCast_of_re_pos hw')]; ring
    have hkd := (hd1.sub hd2).sub hd3
    rwa [hval] at hkd
  have hfderiv : S.EqOn (fderiv ℂ k) 0 :=
    fun w hw ↦ by simpa using (hderiv w hw).hasFDerivAt.fderiv
  have hdiff : DifferentiableOn ℂ k S :=
    fun w hw ↦ (hderiv w hw).differentiableAt.differentiableWithinAt
  have h1mem : (1 : ℂ) ∈ S := by rw [hS]; simp
  have hzmem : z ∈ S := hz
  have hconst := hopen.is_const_of_fderiv_eq_zero hpre hdiff hfderiv hzmem h1mem
  have hk1 : k 1 = 0 := by
    simp only [hk, Complex.log_one, logGamma_one, sub_zero]
    rw [show (1 : ℂ) + 1 = ((2 : ℝ) : ℂ) by norm_num, logGamma_ofReal (by norm_num),
      Real.Gamma_two, Real.log_one, Complex.ofReal_zero]
  rw [hk1] at hconst
  simp only [hk] at hconst
  linear_combination hconst

/-- Exact integer shift of the branch. For `Re w > 0` and `N : ℕ`,
`log Γ w = log Γ (w + N) - ∑_{j=0}^{N-1} Log (w + j)`. -/
theorem logGamma_eq_sub_sum_log_add {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    logGamma w
      = logGamma (w + N) - ∑ j ∈ Finset.range N, Complex.log (w + j) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hwn : 0 < (w + (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hstep : logGamma (w + ((n + 1 : ℕ) : ℂ))
        = Complex.log (w + n) + logGamma (w + n) := by
      rw [show w + ((n + 1 : ℕ) : ℂ) = (w + (n : ℂ)) + 1 by push_cast; ring,
        logGamma_add_one hwn]
    rw [Finset.sum_range_succ, hstep, ih]
    ring

end Complex
