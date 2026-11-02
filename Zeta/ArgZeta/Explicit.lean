/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.ArgZeta.ShiftIdentity
public import Zeta.ArgZeta.MainBound
public import Zeta.ArgZeta.Dirichlet
public import Zeta.ArgZeta.ExplicitTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# De-existentialising the additive constant of Lehman's bound

The constant-free shift identity, the explicit archimedean witness, and the assembly of all the
explicit constants into concrete values of the additive constant `A` in Lehman's bound
(`cha:lehman_explicit`, `lehman_sharp.tex`). The Dirichlet/digamma constants and the tail witness
come from the siblings `Dirichlet` and `ExplicitTail`.

## Main results

- `tsum_log_norm_riemannXiZeros_shift_eq` (`lem:le_shift_no_kappa`): the shift identity without
  its constant `κ`.
- `logNormGammaArchimedean_strip_diff_ge_explicit` (`lem:le_arch_explicit`): the explicit
  archimedean witness.
- `norm_integral_argZeta_le_concrete` (`thm:le_concrete`), `norm_integral_argZeta_le_eighteen`
  (`thm:le_sharp`), `..._fifteen`, `..._twelve`, `..._six`, `..._eleven_halves`, `..._five`
  (`thm:ls_five`): Lehman's bound at successively sharper additive constants, `A ≤ 47` down to
  `A ≤ 5`.
- `norm_integral_argZeta_le_*_unconditional`: the same with the endpoint zero-freeness hypotheses
  removed.
-/
@[expose] public section


open Complex Filter Topology Function Set

open scoped Real

/-- `log π ≤ 2 log 2`, i.e. `log π ≤ log 4`, since `π < 4`. -/
private lemma log_pi_le_two_log_two : Real.log π ≤ 2 * Real.log 2 := by
  rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
  exact Real.log_le_log Real.pi_pos Real.pi_lt_four.le

/-- `log (2π) ≤ 3 log 2`. -/
private lemma log_two_pi_le_three_log_two : Real.log (2 * π) ≤ 3 * Real.log 2 := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne']; linarith [log_pi_le_two_log_two]

/-- The Hadamard constant `B` of `riemannXi_eq_hadamard_product` is `ξ'/ξ(0)`. -/
private lemma logDeriv_riemannXi_zero_eq {B : ℝ}
    (hB : ∀ s, riemannXi s =
      1 / 2 * Complex.exp (B * s) * riemannXiCanonicalProduct riemannXiZeros s) :
    logDeriv riemannXi 0 = (B : ℂ) := by
  -- Absorb the constant `½` into the exponent: `½ e^{Bs} = e^{log(1/2) + Bs}`.
  have hrep : ∀ s, riemannXi s = Complex.exp (Complex.log (1 / 2) + B * s) *
      riemannXiCanonicalProduct riemannXiZeros s := fun s ↦ by
    rw [hB s, Complex.exp_add, Complex.exp_log (by norm_num)]
  have hde : HasDerivAt (fun s : ℂ ↦ Complex.log (1 / 2) + (B : ℂ) * s) (B : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (B : ℂ)).const_add (Complex.log (1 / 2))
  rw [logDeriv_riemannXi_zero_eq_deriv (by fun_prop) hrep, hde.deriv]

/-- **De-existentialised shift identity** (`lem:le_shift_no_kappa`). The constant `κ` of
`exists_const_tsum_log_norm_riemannXiZeros_shift_eq` is `0`, so for every `s` and `s + d` not
zeros of `ξ`, `∑ᵢ [log‖s+d-ρᵢ‖ - log‖s-ρᵢ‖] = log‖ξ(s+d)‖ - log‖ξ(s)‖`. -/
theorem tsum_log_norm_riemannXiZeros_shift_eq {s : ℂ} {d : ℝ}
    (hs : ∀ i, s ≠ riemannXiZeros i) (hsd : ∀ i, s + d ≠ riemannXiZeros i) :
    ∑' i, (Real.log ‖s + ↑d - riemannXiZeros i‖ - Real.log ‖s - riemannXiZeros i‖)
      = Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖ := by
  obtain ⟨B, hB⟩ := riemannXi_eq_hadamard_product
  have hsum : Summable fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2 := summable_inv_norm_sq_riemannXiZeros
  have hresum : Summable fun i ↦ ((riemannXiZeros i)⁻¹).re := summable_re_inv_riemannXiZeros
  -- `κ = B + ∑ᵢ Re(1/ρᵢ) = 0`, since `B = Re(ξ'/ξ(0))`.
  have hκ0 : B + ∑' i, ((riemannXiZeros i)⁻¹).re = 0 := by
    have hBre : (logDeriv riemannXi 0).re = B := by
      rw [logDeriv_riemannXi_zero_eq hB, Complex.ofReal_re]
    have h := hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero
    rwa [hBre] at h
  set ρ := riemannXiZeros
  have hzne : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) → ∀ i, z / ρ i ≠ 1 := fun {z} hz i h ↦
    hz i ((div_eq_one_iff_eq (riemannXiZeros_ne_zero i)).mp h)
  have hsummSplit : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) →
      Summable (fun i ↦ Real.log ‖1 - z / ρ i‖ + (z / ρ i).re) := fun {z} hz ↦
    (summable_log_norm_weierstrassE1 ρ hsum z).congr
      (fun i ↦ log_norm_weierstrassE1 (hzne hz i))
  have hlogXi : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) →
      Real.log ‖riemannXi z‖
        = Real.log (1 / 2) + B * z.re + Real.log ‖riemannXiCanonicalProduct ρ z‖ := by
    intro z hz
    have hPne : riemannXiCanonicalProduct ρ z ≠ 0 :=
      riemannXiCanonicalProduct_ne_zero_of_forall_ne ρ hsum hz
    have h12 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
      rw [norm_div, norm_one, Complex.norm_ofNat]
    rw [hB z, norm_mul, norm_mul, Complex.norm_exp, h12,
      show ((B : ℂ) * z).re = B * z.re from by rw [Complex.re_ofReal_mul],
      Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hPne),
      Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hdiffXi : Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖
      = B * d + (Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖) := by
    rw [hlogXi hsd, hlogXi hs, Complex.add_re, Complex.ofReal_re]; ring
  have hterm : ∀ i,
      (Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re)
        = (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖) + d * ((ρ i)⁻¹).re := by
    intro i
    have hρ0 := riemannXiZeros_ne_zero i
    have elog : ∀ {w : ℂ}, w ≠ ρ i →
        Real.log ‖1 - w / ρ i‖ = Real.log ‖w - ρ i‖ - Real.log ‖ρ i‖ := by
      intro w hw
      have h1 : (1 : ℂ) - w / ρ i = (ρ i - w) / ρ i := by rw [sub_div, div_self hρ0]
      rw [h1, norm_div, Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦ hw h.symm))
        (norm_ne_zero_iff.mpr hρ0), norm_sub_rev]
    have hsubdiv : (s + ↑d) / ρ i - s / ρ i = (↑d : ℂ) * (ρ i)⁻¹ := by
      rw [div_sub_div_same, add_sub_cancel_left, div_eq_mul_inv]
    have ere : ((s + ↑d) / ρ i).re - (s / ρ i).re = d * ((ρ i)⁻¹).re := by
      rw [← Complex.sub_re, hsubdiv, Complex.re_ofReal_mul]
    rw [elog (hsd i), elog (hs i)]
    linear_combination ere
  have hD : Summable (fun i ↦ Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖) := by
    refine ((hsummSplit hsd).sub (hsummSplit hs)).sub (hresum.mul_left d) |>.congr fun i ↦ ?_
    rw [hterm i]; ring
  have hsplit : ∑' i, ((Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re))
      = ∑' i, (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖)
          + d * ∑' i, ((ρ i)⁻¹).re := by
    rw [funext (fun i ↦ hterm i), hD.tsum_add (hresum.mul_left d), tsum_mul_left]
  have hPsub : ∑' i, ((Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re))
      = Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖ := by
    rw [(hsummSplit hsd).tsum_sub (hsummSplit hs),
      ← log_norm_riemannXiCanonicalProduct_eq_tsum ρ hsum hsd,
      ← log_norm_riemannXiCanonicalProduct_eq_tsum ρ hsum hs]
  rw [hPsub] at hsplit
  have hfinal : ∑' i, (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖)
      = (Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖) - d * ∑' i, ((ρ i)⁻¹).re := by
    linear_combination -hsplit
  rw [hfinal, hdiffXi]
  linear_combination (-(d : ℝ)) * hκ0

/-- **Explicit bound on real `log Γ` over `[1/4, 4/5]`** (`lem:le_gamma_bounded`): for every
`σ ∈ [1/4, 4/5]`, `|log Γ(σ)| ≤ log 4`. This pins the sole non-explicit ingredient `M` of the
archimedean constant. -/
theorem abs_log_Gamma_le_log_four {σ : ℝ} (hσ : 1 / 4 ≤ σ) (hσ' : σ ≤ 4 / 5) :
    |Real.log (Real.Gamma σ)| ≤ Real.log 4 := by
  set g : ℝ → ℝ := Real.log ∘ Real.Gamma with hgdef
  have hconv : ConvexOn ℝ (Set.Ioi 0) g := Real.convexOn_log_Gamma
  have hg1 : g 1 = 0 := by rw [hgdef, Function.comp_apply, Real.Gamma_one, Real.log_one]
  have hg2 : g 2 = 0 := by rw [hgdef, Function.comp_apply, Real.Gamma_two, Real.log_one]
  have hg3 : g 3 = Real.log 2 := by
    have h3 : Real.Gamma 3 = 2 := by
      rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_two]
      norm_num
    rw [hgdef, Function.comp_apply, h3]
  have hσpos : (0 : ℝ) < σ := by linarith
  have hmemx : (σ + 1 : ℝ) ∈ Set.Ioi 0 := by simp only [Set.mem_Ioi]; linarith
  -- upper bound `g (σ+1) ≤ 0` via the chord on `[1, 2]` (triple `(1, σ+1, 2)`)
  have hup : g (σ + 1) ≤ 0 := by
    have h := hconv.slope_mono_adjacent (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) (show (1 : ℝ) < σ + 1 by linarith)
      (show σ + 1 < 2 by linarith)
    rw [hg1, hg2, sub_zero, zero_sub] at h
    have hd1 : (0 : ℝ) < σ + 1 - 1 := by linarith
    have hd2 : (0 : ℝ) < 2 - (σ + 1) := by linarith
    rw [div_le_div_iff₀ hd1 hd2] at h
    nlinarith [h]
  -- lower bound `-log 2 ≤ g (σ+1)` via secant monotonicity (triple `(σ+1, 2, 3)`)
  have hlo : -Real.log 2 ≤ g (σ + 1) := by
    have h := hconv.slope_mono_adjacent hmemx (show (3 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show σ + 1 < 2 by linarith) (show (2 : ℝ) < 3 by norm_num)
    rw [hg2, hg3, sub_zero, zero_sub] at h
    have hd2 : (0 : ℝ) < 2 - (σ + 1) := by linarith
    rw [show (3 : ℝ) - 2 = 1 by norm_num, div_one, div_le_iff₀ hd2] at h
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [h, hlog2, mul_nonneg hlog2 hσpos.le]
  -- transfer to `σ` via the recurrence `Γ(σ+1) = σ · Γ(σ)`
  have hΓpos : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos hσpos
  have hglog : Real.log (Real.Gamma σ) = g (σ + 1) - Real.log σ := by
    have hrec : g (σ + 1) = Real.log σ + Real.log (Real.Gamma σ) := by
      simp only [hgdef, Function.comp_apply]
      rw [Real.Gamma_add_one hσpos.ne', Real.log_mul hσpos.ne' hΓpos.ne']
    linarith
  have hlog24 : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have hlogσ_nonpos : Real.log σ ≤ 0 := Real.log_nonpos hσpos.le (by linarith)
  have hlogσ_ge : -Real.log 4 ≤ Real.log σ := by
    have h14 := Real.log_le_log (show (0 : ℝ) < 1 / 4 by norm_num) hσ
    rw [show (1 / 4 : ℝ) = 4⁻¹ by norm_num, Real.log_inv] at h14
    linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [hglog]; linarith
  · rw [hglog]; linarith

/-! ## §2 & §5: the explicit archimedean witness and the concrete additive constant

The explicit archimedean strip-difference constant `C_a ≤ 10` of `lem:le_arch_explicit`, and the
assembly of `a₁ ≤ 9`, `a₂ ≤ 136` into the concrete `A ≤ 47` of
`norm_integral_argZeta_le_concrete`. -/

section Assembly
open Complex.Stirling MeasureTheory

/-- The compact-interval bound `M = log 4` on `|log‖Γ(σ)‖|` over `[1/4, 4/5]`, in the shape
required by `Complex.log_norm_Gamma_remainder_le`. -/
private lemma abs_log_norm_Gamma_ofReal_le_log_four :
    ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (4 / 5), |Real.log ‖Complex.Gamma (σ : ℂ)‖| ≤ Real.log 4 := by
  intro σ hσ
  obtain ⟨hσ1, hσ2⟩ := hσ
  have hpos : 0 < Real.Gamma σ := Real.Gamma_pos_of_pos (by linarith)
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  exact abs_log_Gamma_le_log_four hσ1 hσ2

/-- The explicit digamma constant `C₀ = 1/π + 1/12` in the shape required by
`Complex.log_norm_Gamma_remainder_le`. -/
private lemma norm_digamma_sub_log_add_le_explicit {s : ℂ} (hs : (1 / 4 : ℝ) ≤ s.re) :
    ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖ ≤ (1 / π + 1 / 12) * ‖s‖ ^ (-(2 : ℤ)) := by
  have hspos : 0 < s.re := lt_of_lt_of_le (by norm_num) hs
  have key : Complex.digamma s - Complex.log s + (2 * s)⁻¹ = -digammaRemainderIoi s 1 := by
    have hde := digamma_eq_log_sub s hspos 0
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty,
      show (2 * 0 + 1 : ℕ) = 1 from rfl] at hde
    linear_combination hde
  rw [key, norm_neg]
  exact norm_digammaRemainderIoi_one_le hspos

/-- **Explicit archimedean witness** (`lem:le_arch_explicit`).  For `d = 53/100`, the strip
difference `A(½+d) - A(½)` is bounded below by `(d²/2) log t - C_a` with an explicit numeral
`C_a ≤ 10`, for all `t ≥ 168π`. -/
theorem logNormGammaArchimedean_strip_diff_ge_explicit :
    ∃ C : ℝ, C ≤ 10 ∧ ∀ t : ℝ, 168 * π ≤ t →
      (53 / 100 : ℝ) ^ 2 / 2 * Real.log t - C ≤
        (∫ σ in Set.Ioo (1 / 2 + 53 / 100) (1 / 2 + 2 * (53 / 100)), logNormGammaArchimedean t σ) -
          ∫ σ in Set.Ioo (1 / 2) (1 / 2 + 53 / 100), logNormGammaArchimedean t σ := by
  have hπpos : 0 < π := Real.pi_pos
  set K : ℝ := Real.log 4 + 4 / 5 + (4 / 5 / 2 + 1 / 4) *
      (|Real.log (1 / (4 / 5) ^ 2)| + |Real.log (1 + 1 / (1 / 4) ^ 2)|)
    + (1 / π + 1 / 12) * Real.pi / (2 * (1 / 4)) with hKdef
  -- the explicit Stirling constant is ≤ 7
  have hK7 : K ≤ 7 := by
    rw [hKdef]
    have hlast : (1 / π + 1 / 12) * Real.pi / (2 * (1 / 4)) = 2 + π / 6 := by
      rw [show (2 * (1 / 4) : ℝ) = 1 / 2 by norm_num, add_mul, one_div_mul_cancel hπpos.ne']
      ring
    have hA1 : |Real.log (1 / (4 / 5) ^ 2)| ≤ 9 / 16 := by
      rw [show (1 : ℝ) / (4 / 5) ^ 2 = 25 / 16 by norm_num,
        abs_of_nonneg (Real.log_nonneg (by norm_num))]
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 25 / 16 by norm_num)]
    have hA2 : |Real.log (1 + 1 / (1 / 4) ^ 2)| ≤ 4 * Real.log 2 + 1 / 16 := by
      rw [show (1 : ℝ) + 1 / (1 / 4) ^ 2 = 17 by norm_num,
        abs_of_nonneg (Real.log_nonneg (by norm_num)),
        show (17 : ℝ) = 16 * (17 / 16) by norm_num,
        Real.log_mul (by norm_num) (by norm_num),
        show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      push_cast
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 17 / 16 by norm_num)]
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [hlast, hlog4]
    nlinarith [hA1, hA2, Real.log_two_lt_d9, Real.pi_lt_d2]
  -- the two-sided Stirling bound along the archimedean line, with explicit `L₁ = -K, L₂ = K`
  have hM := abs_log_norm_Gamma_ofReal_le_log_four
  have hL : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 / 2 + 2 * (53 / 100) → ∀ t : ℝ, 2 ≤ t →
      -K + (σ / 2 - 1 / 2) * Real.log (t / 2) - Real.pi / 2 * (t / 2) ≤
        Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ ∧
      Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ ≤
        K + (σ / 2 - 1 / 2) * Real.log (t / 2) - Real.pi / 2 * (t / 2) := by
    intro σ hσ1 hσ2 t ht
    have hpt : ((σ : ℂ) + Complex.I * t) / 2
        = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hpt]
    have hb := log_norm_Gamma_remainder_le (a := 1 / 4) (b := 4 / 5) (M := Real.log 4)
      (C₀ := 1 / π + 1 / 12) (by norm_num) (by norm_num) hM (by positivity)
      (fun s hs ↦ norm_digamma_sub_log_add_le_explicit hs)
      (σ := σ / 2) (by linarith) (by linarith) (t := t / 2) (by linarith)
    rw [hKdef]
    obtain ⟨lo, hi⟩ := abs_le.mp hb
    constructor <;> linarith
  refine ⟨_, ?_, logNormGammaArchimedean_strip_diff_ge_of (d := 53 / 100) (L₁ := -K) (L₂ := K)
    (by norm_num) (by norm_num) hL⟩
  -- the explicit constant `C_a = (d²/2)(log2+logπ) + (d/2)log2 + 2dK ≤ 10`
  have hlogpi : Real.log π ≤ π - 1 := Real.log_le_sub_one_of_pos hπpos
  nlinarith [hK7, Real.log_two_lt_d9, Real.pi_lt_d2, hlogpi]

/-- Shared `d = 53/100`, `c = 5/2` lower-bound core with the band-based archimedean witness
(`C_a ≤ 10`), `C_ψ ≤ 39` and `κ = 0`: given a tail witness `Ct` and a numeral `a₂` dominating
`(5/2)d²·39 + 2 Ct + 10`, `-I(t) ≤ a₂ + (3/4)d²·log t`. -/
private lemma le_logNormZetaIntegral_53_of {Ct a₂ : ℝ}
    (hCt : ∀ t : ℝ,
      (-Ct ≤ ∫ σ in Set.Ioi (103 / 100 : ℝ),
              Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) ∧
      (-Ct ≤ ∫ σ in Set.Ioo (103 / 100 : ℝ) (156 / 100),
              Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖))
    (ha₂ : (5 : ℝ) / 2 * (53 / 100) ^ 2 * 39 + 2 * Ct + 10 ≤ a₂) :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ a₂ + 3 / 4 * (53 / 100) ^ 2 * Real.log t := by
  obtain ⟨Ca, hCa10, hCa⟩ := logNormGammaArchimedean_strip_diff_ge_explicit
  intro t ht hzero
  have hlt := le_logNormZetaIntegral_of (d := 53 / 100) (κ := 0) (Ca := Ca) (Cψ := 39) (Ct := Ct)
    (by norm_num)
    (fun s hs hsd ↦ by rw [tsum_log_norm_riemannXiZeros_shift_eq hs hsd]; ring)
    hCa
    (fun t ht ↦ tsum_re_inv_riemannXiZeros_sub_le_explicit t ht)
    (fun t ↦ by
      rw [show (1 / 2 + 53 / 100 : ℝ) = 103 / 100 by norm_num,
        show (1 / 2 + 2 * (53 / 100) : ℝ) = 156 / 100 by norm_num]
      exact hCt t)
    t ht hzero
  nlinarith [hlt, hCa10, ha₂]

/-- **Explicit lower bound on `I(t)`** (`lem:le_I_lower_explicit`). For `d = 53/100` and all
`t ≥ 168π` off the zeros of `ζ` on `{σ + it : σ ≥ ½}`, `-I(t) ≤ 136 + (3/4)d² log t`. -/
theorem le_logNormZetaIntegral_explicit :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ 136 + 3 / 4 * (53 / 100) ^ 2 * Real.log t :=
  le_logNormZetaIntegral_53_of logNormZetaIntegral_tail_ge_explicit (by norm_num)

/-- **Crude Lehman bound** (`thm:le_concrete`). For all reals `t₁ < t₂` with `168π < t₁`, neither
an ordinate of a zero of `ζ` on `{σ + it : σ ≥ ½}`,
`|∫_{t₁}^{t₂} S(t) dt| ≤ 47 + 0.128 log(t₂/2π)`. -/
theorem norm_integral_argZeta_le_concrete :
    ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 47 + 0.128 * Real.log (t₂ / (2 * π)) := by
  intro t₁ t₂ ht1 h12 hne1 hne2
  refine (norm_integral_argZeta_le_of_bounds
    (fun t ht hzero ↦ logNormZetaIntegral_le_nine ht hzero)
    (fun t ht hzero ↦ le_logNormZetaIntegral_explicit t ht hzero) t₁ t₂ ht1 h12 hne1 hne2).trans ?_
  have hπpos : 0 < π := Real.pi_pos
  -- `A = ((9 + 136) + coeff·log2π)/π ≤ 47`
  have hconst :
      (9 + 136 + (3 / 16 + 3 / 4 * (53 / 100) ^ 2) * Real.log (2 * π)) / π ≤ 47 := by
    rw [div_le_iff₀ hπpos]
    nlinarith [log_two_pi_le_three_log_two, Real.log_two_lt_d9, Real.pi_gt_d2]
  linarith [hconst]

/-- **Sharp lower bound on `I(t)`** (`lem:le_I_lower_sharp`): `-I(t) ≤ 233/5 + (3/4)d² log t` at
`d = 53/100`. Sharpens `le_logNormZetaIntegral_explicit` by the sharp tail `C_t ≤ 23/5`. -/
theorem le_logNormZetaIntegral_sharp :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ 233 / 5 + 3 / 4 * (53 / 100) ^ 2 * Real.log t :=
  le_logNormZetaIntegral_53_of logNormZetaIntegral_tail_ge_sharp (by norm_num)

/-- **Lower bound on `I(t)` at the sharpened pairing constant `c = 2`** (`lem:ls_rung_two`):
`-I(t) ≤ 206/5 + (3/4)d² log t` at `d = 53/100`. The genuine `log t` coefficient is the smaller
`(c-1)/2·d² = d²/2`; it is weakened here to the `3/4·d²` expected by the assembly core. -/
theorem le_logNormZetaIntegral_sharp_two :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ 206 / 5 + 3 / 4 * (53 / 100) ^ 2 * Real.log t := by
  obtain ⟨Ca, hCa10, hCa⟩ := logNormGammaArchimedean_strip_diff_ge_explicit
  intro t ht hzero
  have hlt := le_logNormZetaIntegral_of_le (d := 53 / 100) (κ := 0) (Ca := Ca) (Cψ := 39)
    (Ct := 23 / 5) (by norm_num)
    (fun s hs hsd ↦ by rw [tsum_log_norm_riemannXiZeros_shift_eq hs hsd]; ring)
    hCa
    (fun t ht ↦ tsum_re_inv_riemannXiZeros_sub_le_explicit t ht)
    (fun t ↦ by
      rw [show (1 / 2 + 53 / 100 : ℝ) = 103 / 100 by norm_num,
        show (1 / 2 + 2 * (53 / 100) : ℝ) = 156 / 100 by norm_num]
      exact logNormZetaIntegral_tail_ge_sharp t)
    (c := 2) (by norm_num) t ht hzero
  have hconst : (2 : ℝ) * (53 / 100) ^ 2 * 39 + (53 / 100) ^ 2 * 0 + 2 * (23 / 5) + Ca
      ≤ 206 / 5 := by nlinarith [hCa10]
  have hlogpos : (0 : ℝ) ≤ Real.log t :=
    Real.log_nonneg (by linarith [ht, Real.pi_gt_d2])
  nlinarith [hlt, hconst, hlogpos]

/-- **Lower bound on `I(t)` with the tight archimedean constant** (`lem:ls_Ca`):
`-I(t) ≤ 158/5 + (3/4)d² log t` at `d = 53/100`. Sharpens `le_logNormZetaIntegral_sharp_two` by
the digamma-level archimedean witness (`C_a ≤ 0.45` in place of the band-based `10`). -/
theorem le_logNormZetaIntegral_tight :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ 158 / 5 + 3 / 4 * (53 / 100) ^ 2 * Real.log t := by
  intro t ht hzero
  have hlt := le_logNormZetaIntegral_of_le (d := 53 / 100) (κ := 0)
    (Ca := (53 / 100) ^ 2 / 2 * (Real.log 2 + Real.log π) + (53 / 100) / 2 * Real.log 2
      + (53 / 100) ^ 2 / 10000)
    (Cψ := 39) (Ct := 23 / 5) (by norm_num)
    (fun s hs hsd ↦ by rw [tsum_log_norm_riemannXiZeros_shift_eq hs hsd]; ring)
    (logNormGammaArchimedean_strip_diff_ge_tight (by norm_num) (by norm_num))
    (fun t ht ↦ tsum_re_inv_riemannXiZeros_sub_le_explicit t ht)
    (fun t ↦ by
      rw [show (1 / 2 + 53 / 100 : ℝ) = 103 / 100 by norm_num,
        show (1 / 2 + 2 * (53 / 100) : ℝ) = 156 / 100 by norm_num]
      exact logNormZetaIntegral_tail_ge_sharp t)
    (c := 2) (by norm_num) t ht hzero
  have hlogsum : Real.log 2 + Real.log π ≤ 3 * Real.log 2 := by
    linarith [log_pi_le_two_log_two]
  have hconst : (2 : ℝ) * (53 / 100) ^ 2 * 39 + (53 / 100) ^ 2 * 0 + 2 * (23 / 5)
      + ((53 / 100) ^ 2 / 2 * (Real.log 2 + Real.log π) + (53 / 100) / 2 * Real.log 2
        + (53 / 100) ^ 2 / 10000) ≤ 158 / 5 := by
    have h1 : (53 / 100 : ℝ) ^ 2 / 2 * (Real.log 2 + Real.log π)
        ≤ (53 / 100) ^ 2 / 2 * (3 * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogsum (by positivity)
    nlinarith [h1, Real.log_two_lt_d9, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hlogpos : (0 : ℝ) ≤ Real.log t := Real.log_nonneg (by linarith [ht, Real.pi_gt_d2])
  nlinarith [hlt, hconst, hlogpos]

/-- Shared design-point-P1 core (`d = 74/100`, `c = 2`, tight archimedean and tail constants):
given a zero-sum witness `Cψ` and a numeral `a₂` dominating the assembled constant,
`-I(t) ≤ a₂ + (74/100)²/2·log t`. -/
private lemma le_logNormZetaIntegral_p1_of {Cψ a₂ : ℝ}
    (hCψ : ∀ t : ℝ, 168 * π ≤ t →
      ∑' i, (((1 / 2 : ℂ) + ((74 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
        ≤ 1 / 2 * Real.log t + Cψ)
    (ha₂ : (2 : ℝ) * (74 / 100) ^ 2 * Cψ + 2 * (5 / 2)
        + ((74 / 100) ^ 2 / 2 * (3 * Real.log 2) + (74 / 100) / 2 * Real.log 2
          + (74 / 100) ^ 2 / 10000) ≤ a₂) :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ a₂ + (74 / 100) ^ 2 / 2 * Real.log t := by
  intro t ht hzero
  have hlt := le_logNormZetaIntegral_of_le (d := 74 / 100) (κ := 0)
    (Ca := (74 / 100) ^ 2 / 2 * (Real.log 2 + Real.log π) + (74 / 100) / 2 * Real.log 2
      + (74 / 100) ^ 2 / 10000)
    (Cψ := Cψ) (Ct := 5 / 2) (by norm_num)
    (fun s hs hsd ↦ by rw [tsum_log_norm_riemannXiZeros_shift_eq hs hsd]; ring)
    (logNormGammaArchimedean_strip_diff_ge_tight (by norm_num) (by norm_num))
    hCψ
    (fun t ↦ by
      rw [show (1 / 2 + 74 / 100 : ℝ) = 124 / 100 by norm_num,
        show (1 / 2 + 2 * (74 / 100) : ℝ) = 198 / 100 by norm_num]
      exact logNormZetaIntegral_tail_ge_tight t)
    (c := 2) (by norm_num) t ht hzero
  have h1 : (74 / 100 : ℝ) ^ 2 / 2 * (Real.log 2 + Real.log π)
      ≤ (74 / 100) ^ 2 / 2 * (3 * Real.log 2) :=
    mul_le_mul_of_nonneg_left (by linarith [log_pi_le_two_log_two]) (by positivity)
  nlinarith [hlt, ha₂, h1]

/-- **Lower bound on `I(t)` at the deeper strip `d = 74/100`** (design point P1 of
`sec:ls_optim`): `-I(t) ≤ 57/5 + (74/100)²/2 · log t` for `t ≥ 168π` off the zeros. Unlike
`le_logNormZetaIntegral_sharp_two` and `_tight`, this keeps the genuine `log t` coefficient
`d²/2`; at `d = 74/100` the weakened `3/4·d²` would violate the shape constraint
`b₁ + b₂ ≤ 0.128π`. -/
theorem le_logNormZetaIntegral_eleven_halves :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ 57 / 5 + (74 / 100) ^ 2 / 2 * Real.log t :=
  le_logNormZetaIntegral_p1_of tsum_re_inv_riemannXiZeros_sub_le_tight
    (by nlinarith [Real.log_two_lt_d9, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])

/-- **Dirichlet-sharpened lower additive constant** (`thm:ls_five`, lower half):
`-I(t) ≤ 933/100 + (74/100)²/2 · log t`. Sharpens `le_logNormZetaIntegral_eleven_halves` by the
sharp zero-sum constant `C_ψ ≤ 319/100`. -/
theorem le_logNormZetaIntegral_five :
    ∀ t : ℝ, 168 * π ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ 933 / 100 + (74 / 100) ^ 2 / 2 * Real.log t :=
  le_logNormZetaIntegral_p1_of tsum_re_inv_riemannXiZeros_sub_le_tight_sharp
    (by nlinarith [Real.log_two_lt_d9, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])

/-- **Sharpened Lehman bound** (`thm:le_sharp`). For all reals `t₁ < t₂` with `168π < t₁`, neither
an ordinate of a zero of `ζ` on `{σ + it : σ ≥ ½}`,
`|∫_{t₁}^{t₂} S(t) dt| ≤ 18 + 0.128 log(t₂/2π)`. -/
theorem norm_integral_argZeta_le_eighteen :
    ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 18 + 0.128 * Real.log (t₂ / (2 * π)) := by
  intro t₁ t₂ ht1 h12 hne1 hne2
  refine (norm_integral_argZeta_le_of_bounds
    (fun t ht hzero ↦ logNormZetaIntegral_le_nine ht hzero)
    (fun t ht hzero ↦ le_logNormZetaIntegral_sharp t ht hzero) t₁ t₂ ht1 h12 hne1 hne2).trans ?_
  have hπpos : 0 < π := Real.pi_pos
  -- `A = ((9 + 233/5) + coeff·log 2π)/π ≤ 18`
  have hconst :
      (9 + 233 / 5 + (3 / 16 + 3 / 4 * (53 / 100) ^ 2) * Real.log (2 * π)) / π ≤ 18 := by
    rw [div_le_iff₀ hπpos]
    nlinarith [log_two_pi_le_three_log_two, Real.log_two_lt_d9, Real.pi_gt_d2]
  linarith [hconst]

/-- **Pairing-sharpened Lehman bound** (`thm:ls_conditional_weak` route at `c = 2`):
`|∫_{t₁}^{t₂} S(t) dt| ≤ 33/2 + 0.128 log(t₂/2π)`, for `t₁, t₂` as in
`norm_integral_argZeta_le_eighteen`. -/
theorem norm_integral_argZeta_le_sharp_two :
    ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 33 / 2 + 0.128 * Real.log (t₂ / (2 * π)) := by
  intro t₁ t₂ ht1 h12 hne1 hne2
  refine (norm_integral_argZeta_le_of_bounds
    (fun t ht hzero ↦ logNormZetaIntegral_le_nine ht hzero)
    (fun t ht hzero ↦ le_logNormZetaIntegral_sharp_two t ht hzero)
      t₁ t₂ ht1 h12 hne1 hne2).trans ?_
  have hπpos : 0 < π := Real.pi_pos
  -- `A = ((9 + 206/5) + coeff·log 2π)/π ≤ 33/2`
  have hconst :
      (9 + 206 / 5 + (3 / 16 + 3 / 4 * (53 / 100) ^ 2) * Real.log (2 * π)) / π ≤ 33 / 2 := by
    rw [div_le_iff₀ hπpos]
    nlinarith [log_two_pi_le_three_log_two, Real.log_two_lt_d9, Real.pi_gt_d2]
  linarith [hconst]

/-- The elementary upper bound `logNormZetaIntegral_le_five` (`a₁ ≤ 5`, `b₁ = 1/8`) with `b₁`
weakened up to the `3/16` expected by `norm_integral_argZeta_le_of_bounds`. -/
private lemma logNormZetaIntegral_le_five_weak (t : ℝ) (ht : 168 * π ≤ t)
    (hzero : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) :
    logNormZetaIntegral t ≤ 5 + 3 / 16 * Real.log t := by
  have hlog : (0 : ℝ) ≤ Real.log t := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  linarith [logNormZetaIntegral_le_five ht hzero]

/-- **Upper-and-pairing-sharpened Lehman bound** (levers U1 and rung R1):
`|∫_{t₁}^{t₂} S(t) dt| ≤ 15 + 0.128 log(t₂/2π)`, for `t₁, t₂` as in
`norm_integral_argZeta_le_eighteen`. -/
theorem norm_integral_argZeta_le_fifteen :
    ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 15 + 0.128 * Real.log (t₂ / (2 * π)) := by
  intro t₁ t₂ ht1 h12 hne1 hne2
  refine (norm_integral_argZeta_le_of_bounds logNormZetaIntegral_le_five_weak
    (fun t ht hzero ↦ le_logNormZetaIntegral_sharp_two t ht hzero)
      t₁ t₂ ht1 h12 hne1 hne2).trans ?_
  have hπpos : 0 < π := Real.pi_pos
  -- `A = ((5 + 206/5) + coeff·log 2π)/π ≤ 15`
  have hconst :
      (5 + 206 / 5 + (3 / 16 + 3 / 4 * (53 / 100) ^ 2) * Real.log (2 * π)) / π ≤ 15 := by
    rw [div_le_iff₀ hπpos]
    nlinarith [log_two_pi_le_three_log_two, Real.log_two_lt_d9, Real.pi_gt_d2]
  linarith [hconst]

/-- **Archimedean-sharpened Lehman bound** (`lem:ls_Ca` cashed in):
`|∫_{t₁}^{t₂} S(t) dt| ≤ 12 + 0.128 log(t₂/2π)`, for `t₁, t₂` as in
`norm_integral_argZeta_le_eighteen`. -/
theorem norm_integral_argZeta_le_twelve :
    ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 12 + 0.128 * Real.log (t₂ / (2 * π)) := by
  intro t₁ t₂ ht1 h12 hne1 hne2
  refine (norm_integral_argZeta_le_of_bounds logNormZetaIntegral_le_five_weak
    (fun t ht hzero ↦ le_logNormZetaIntegral_tight t ht hzero)
      t₁ t₂ ht1 h12 hne1 hne2).trans ?_
  have hπpos : 0 < π := Real.pi_pos
  have hconst :
      (5 + 158 / 5 + (3 / 16 + 3 / 4 * (53 / 100) ^ 2) * Real.log (2 * π)) / π ≤ 12 := by
    rw [div_le_iff₀ hπpos]
    nlinarith [log_two_pi_le_three_log_two, Real.log_two_lt_d9, Real.pi_gt_d2]
  linarith [hconst]

/-- **Tail-sharpened Lehman bound** (design point P1 at `d = 74/100`, sharpened tail):
`|∫_{t₁}^{t₂} S(t) dt| ≤ 11/2 + 0.128 log(t₂/2π)`, for `t₁, t₂` as in
`norm_integral_argZeta_le_eighteen`. This is the ceiling of the `N`-majorant tail. -/
theorem norm_integral_argZeta_le_eleven_halves :
    ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 11 / 2 + 0.128 * Real.log (t₂ / (2 * π)) := by
  intro t₁ t₂ ht1 h12 hne1 hne2
  refine (norm_integral_argZeta_le_of_bounds' (b₁ := 1 / 8) (b₂ := (74 / 100) ^ 2 / 2)
    (by norm_num) (by positivity) (by nlinarith [Real.pi_gt_d2])
    (fun t ht hzero ↦ logNormZetaIntegral_le_five ht hzero)
    (fun t ht hzero ↦ le_logNormZetaIntegral_eleven_halves t ht hzero)
      t₁ t₂ ht1 h12 hne1 hne2).trans ?_
  have hπpos : 0 < π := Real.pi_pos
  have hconst :
      (5 + 57 / 5 + (1 / 8 + (74 / 100) ^ 2 / 2) * Real.log (2 * π)) / π ≤ 11 / 2 := by
    rw [div_le_iff₀ hπpos]
    nlinarith [log_two_pi_le_three_log_two, Real.log_two_lt_d9, Real.pi_gt_d2]
  linarith [hconst]

/-- **Strip-depth-sharpened Lehman bound** (`rem:ls_p1_correction`):
`|∫_{t₁}^{t₂} S(t) dt| ≤ 6 + 0.128 log(t₂/2π)`. Superseded by the stronger
`norm_integral_argZeta_le_eleven_halves`. -/
theorem norm_integral_argZeta_le_six :
    ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 6 + 0.128 * Real.log (t₂ / (2 * π)) :=
  fun t₁ t₂ ht1 h12 hne1 hne2 ↦
    (norm_integral_argZeta_le_eleven_halves t₁ t₂ ht1 h12 hne1 hne2).trans (by linarith)

/-- **Dirichlet-sharpened Lehman bound** (`thm:ls_five`). For all reals `t₁ < t₂` with `168π < t₁`,
neither an ordinate of a zero of `ζ` on `{σ + it : σ ≥ ½}`,
`|∫_{t₁}^{t₂} S(t) dt| ≤ 5 + 0.128 log(t₂/2π)`. The true value is `≈ 4.79`. -/
theorem norm_integral_argZeta_le_five :
    ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 5 + 0.128 * Real.log (t₂ / (2 * π)) := by
  intro t₁ t₂ ht1 h12 hne1 hne2
  refine (norm_integral_argZeta_le_of_bounds' (b₁ := 1 / 8) (b₂ := (74 / 100) ^ 2 / 2)
    (by norm_num) (by positivity) (by nlinarith [Real.pi_gt_d2])
    (fun t ht hzero ↦ logNormZetaIntegral_le_five ht hzero)
    (fun t ht hzero ↦ le_logNormZetaIntegral_five t ht hzero)
      t₁ t₂ ht1 h12 hne1 hne2).trans ?_
  have hπpos : 0 < π := Real.pi_pos
  have hconst :
      (5 + 933 / 100 + (1 / 8 + (74 / 100) ^ 2 / 2) * Real.log (2 * π)) / π ≤ 5 := by
    rw [div_le_iff₀ hπpos]
    nlinarith [log_two_pi_le_three_log_two, Real.log_two_lt_d9, Real.pi_gt_d2]
  linarith [hconst]

end Assembly

/-! ## Removing the endpoint conditions

The bounds above require both endpoints `t₁, t₂` to be zero-free ordinates. The lemmas here remove
that hypothesis from each of them. -/

section Unconditional
open MeasureTheory

/-- Near any positive ordinate there is a zero-free ordinate: for `0 < c` and `0 < ε` some
`t ∈ (c, c+ε)` has `ζ(σ+it) ≠ 0` for all `σ ≥ 1/2`. -/
private lemma exists_zeroFree_Ioo {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ t : ℝ, t ∈ Set.Ioo c (c + ε) ∧
      ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0 := by
  have hcε : c < c + ε := by linarith
  have hfin := finite_setOf_riemannZeta_zero_ray_Icc hc hcε.le
  obtain ⟨t, htd⟩ := ((Set.Ioo_infinite hcε).sdiff hfin).nonempty
  rw [Set.mem_sdiff] at htd
  exact ⟨t, htd.1, fun σ hσ hz ↦ htd.2 ⟨⟨σ, hσ, hz⟩, Set.Ioo_subset_Icc_self htd.1⟩⟩

/-- **Parametric endpoint-removal core.** Any conditional bound
`|∫_{t₁}^{t₂} S| ≤ A + 0.128 log(t₂/2π)` at zero-free endpoints extends to all `t₁ < t₂` with
`168π < t₁`. -/
private lemma norm_integral_argZeta_le_unconditional_of {A : ℝ}
    (hbnd : ∀ t₁ t₂ : ℝ, 168 * π < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ A + 0.128 * Real.log (t₂ / (2 * π)))
    {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁) (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ A + 0.128 * Real.log (t₂ / (2 * π)) := by
  have hπ : 0 < π := Real.pi_pos
  have ht1pos : 0 < t₁ := lt_trans (by positivity) ht1
  have ht2pos : 0 < t₂ := lt_trans ht1pos h12
  have ht1gt1 : (1 : ℝ) < t₁ := by nlinarith [Real.pi_gt_three]
  set m : ℝ := min 1 (t₂ - t₁) with hm
  have hm0 : 0 < m := lt_min one_pos (by linarith)
  have hmlt : m ≤ t₂ - t₁ := min_le_right _ _
  set d : ℕ → ℝ := fun n ↦ min (1 / ((n : ℝ) + 1)) m with hd
  have hd0 : ∀ n, 0 < d n := fun n ↦ lt_min (by positivity) hm0
  have hdm : ∀ n, d n ≤ m := fun n ↦ min_le_right _ _
  have hdinv : ∀ n, d n ≤ 1 / ((n : ℝ) + 1) := fun n ↦ min_le_left _ _
  have hdtend : Tendsto d atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ (hd0 n).le) hdinv tendsto_one_div_add_atTop_nhds_zero_nat
  -- choose zero-free ordinates `a n ∈ (t₁, t₁+d n)`, `b n ∈ (t₂, t₂+d n)`
  choose a hamem hafree using fun n ↦ exists_zeroFree_Ioo ht1pos (hd0 n)
  choose b hbmem hbfree using fun n ↦ exists_zeroFree_Ioo ht2pos (hd0 n)
  have halt : ∀ n, t₁ < a n := fun n ↦ (hamem n).1
  have hault : ∀ n, a n < t₁ + d n := fun n ↦ (hamem n).2
  have hblt : ∀ n, t₂ < b n := fun n ↦ (hbmem n).1
  have hbult : ∀ n, b n < t₂ + d n := fun n ↦ (hbmem n).2
  have hab : ∀ n, a n < b n := fun n ↦ by
    have := hault n; have := hdm n; have := hblt n; linarith
  -- continuity of the primitive `x ↦ ∫_{t₁}^x argZeta` on `[t₁-1, t₂+1]`
  have hII : IntervalIntegrable argZeta volume (t₁ - 1) (t₂ + 1) :=
    intervalIntegrable_argZeta (by linarith) (by linarith)
  have hle : t₁ - 1 ≤ t₂ + 1 := by linarith
  have hcontOn : ContinuousOn (fun x ↦ ∫ s in t₁..x, argZeta s) (Set.Icc (t₁ - 1) (t₂ + 1)) := by
    have := intervalIntegral.continuousOn_primitive_interval' (a := t₁) hII
      (by rw [Set.uIcc_of_le hle]; exact ⟨by linarith, by linarith⟩)
    rwa [Set.uIcc_of_le hle] at this
  have hcatT1 : ContinuousAt (fun x ↦ ∫ s in t₁..x, argZeta s) t₁ :=
    hcontOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hcatT2 : ContinuousAt (fun x ↦ ∫ s in t₁..x, argZeta s) t₂ :=
    hcontOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  -- `a n → t₁`, `b n → t₂`
  have haup : Tendsto (fun n ↦ t₁ + d n) atTop (𝓝 t₁) := by
    simpa using tendsto_const_nhds.add hdtend
  have hbup : Tendsto (fun n ↦ t₂ + d n) atTop (𝓝 t₂) := by
    simpa using tendsto_const_nhds.add hdtend
  have hatend : Tendsto a atTop (𝓝 t₁) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds haup
      (fun n ↦ (halt n).le) (fun n ↦ (hault n).le)
  have hbtend : Tendsto b atTop (𝓝 t₂) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbup
      (fun n ↦ (hblt n).le) (fun n ↦ (hbult n).le)
  -- `∫_{aₙ}^{bₙ} argZeta → ∫_{t₁}^{t₂} argZeta`
  have hsplit : ∀ n, ∫ s in (a n)..(b n), argZeta s
      = (∫ s in t₁..(b n), argZeta s) - ∫ s in t₁..(a n), argZeta s := fun n ↦ by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_argZeta ht1pos (halt n).le)
      (intervalIntegrable_argZeta (lt_trans ht1pos (halt n)) (hab n).le)]
    ring
  have hIb : Tendsto (fun n ↦ ∫ s in t₁..(b n), argZeta s) atTop
      (𝓝 (∫ s in t₁..t₂, argZeta s)) := hcatT2.tendsto.comp hbtend
  have hIa : Tendsto (fun n ↦ ∫ s in t₁..(a n), argZeta s) atTop
      (𝓝 (∫ s in t₁..t₁, argZeta s)) := hcatT1.tendsto.comp hatend
  rw [intervalIntegral.integral_same] at hIa
  have hlhs : Tendsto (fun n ↦ ∫ s in (a n)..(b n), argZeta s) atTop
      (𝓝 (∫ s in t₁..t₂, argZeta s)) := by
    have hd := hIb.sub hIa
    rw [sub_zero] at hd
    exact hd.congr (fun n ↦ (hsplit n).symm)
  -- the right-hand side tends to `A + 0.128 log(t₂/2π)`
  have hrhs : Tendsto (fun n ↦ A + 0.128 * Real.log (b n / (2 * π))) atTop
      (𝓝 (A + 0.128 * Real.log (t₂ / (2 * π)))) := by
    have hlog : Tendsto (fun n ↦ Real.log (b n / (2 * π))) atTop
        (𝓝 (Real.log (t₂ / (2 * π)))) :=
      (Real.continuousAt_log (by positivity)).tendsto.comp (hbtend.div_const (2 * π))
    exact tendsto_const_nhds.add (hlog.const_mul 0.128)
  -- the conditional bound at the zero-free pair `(aₙ, bₙ)`
  have hbound : ∀ n, |∫ s in (a n)..(b n), argZeta s| ≤ A + 0.128 * Real.log (b n / (2 * π)) :=
    fun n ↦ hbnd (a n) (b n)
      (by have := halt n; linarith) (hab n) (hafree n) (hbfree n)
  exact le_of_tendsto_of_tendsto' hlhs.abs hrhs hbound

/-- **Crude Lehman bound, unconditional** (`thm:le_concrete_unconditional`). For all reals
`t₁ < t₂` with `168π < t₁`, `|∫_{t₁}^{t₂} S(t) dt| ≤ 47 + 0.128 log(t₂/2π)`, with no zero-freeness
hypothesis at the endpoints. -/
theorem norm_integral_argZeta_le_concrete_unconditional {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁)
    (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 47 + 0.128 * Real.log (t₂ / (2 * π)) :=
  norm_integral_argZeta_le_unconditional_of norm_integral_argZeta_le_concrete ht1 h12

/-- **Sharpened Lehman bound, unconditional** (`thm:le_sharp_unconditional`). For all reals
`t₁ < t₂` with `168π < t₁`, `|∫_{t₁}^{t₂} S(t) dt| ≤ 18 + 0.128 log(t₂/2π)`, with no zero-freeness
hypothesis at the endpoints. -/
theorem norm_integral_argZeta_le_eighteen_unconditional {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁)
    (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 18 + 0.128 * Real.log (t₂ / (2 * π)) :=
  norm_integral_argZeta_le_unconditional_of norm_integral_argZeta_le_eighteen ht1 h12

/-- **Pairing-sharpened Lehman bound, unconditional.** For all reals `t₁ < t₂` with `168π < t₁`,
`|∫_{t₁}^{t₂} S(t) dt| ≤ 33/2 + 0.128 log(t₂/2π)`, with no zero-freeness hypothesis at the
endpoints. -/
theorem norm_integral_argZeta_le_sharp_two_unconditional {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁)
    (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 33 / 2 + 0.128 * Real.log (t₂ / (2 * π)) :=
  norm_integral_argZeta_le_unconditional_of norm_integral_argZeta_le_sharp_two ht1 h12

/-- **Upper-and-pairing-sharpened Lehman bound, unconditional.** For all reals `t₁ < t₂` with
`168π < t₁`, `|∫_{t₁}^{t₂} S(t) dt| ≤ 15 + 0.128 log(t₂/2π)`, with no zero-freeness hypothesis at
the endpoints. -/
theorem norm_integral_argZeta_le_fifteen_unconditional {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁)
    (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 15 + 0.128 * Real.log (t₂ / (2 * π)) :=
  norm_integral_argZeta_le_unconditional_of norm_integral_argZeta_le_fifteen ht1 h12

/-- **Archimedean-sharpened Lehman bound, unconditional.** For all reals `t₁ < t₂` with
`168π < t₁`, `|∫_{t₁}^{t₂} S(t) dt| ≤ 12 + 0.128 log(t₂/2π)`, with no zero-freeness hypothesis at
the endpoints. -/
theorem norm_integral_argZeta_le_twelve_unconditional {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁)
    (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 12 + 0.128 * Real.log (t₂ / (2 * π)) :=
  norm_integral_argZeta_le_unconditional_of norm_integral_argZeta_le_twelve ht1 h12

/-- **Strip-depth-sharpened Lehman bound, unconditional.** For all reals `t₁ < t₂` with
`168π < t₁`, `|∫_{t₁}^{t₂} S(t) dt| ≤ 6 + 0.128 log(t₂/2π)`, with no zero-freeness hypothesis at
the endpoints. -/
theorem norm_integral_argZeta_le_six_unconditional {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁)
    (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 6 + 0.128 * Real.log (t₂ / (2 * π)) :=
  norm_integral_argZeta_le_unconditional_of norm_integral_argZeta_le_six ht1 h12

/-- **Tail-sharpened Lehman bound, unconditional.** For all reals `t₁ < t₂` with `168π < t₁`,
`|∫_{t₁}^{t₂} S(t) dt| ≤ 11/2 + 0.128 log(t₂/2π)`, with no zero-freeness hypothesis at the
endpoints. -/
theorem norm_integral_argZeta_le_eleven_halves_unconditional {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁)
    (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 11 / 2 + 0.128 * Real.log (t₂ / (2 * π)) :=
  norm_integral_argZeta_le_unconditional_of norm_integral_argZeta_le_eleven_halves ht1 h12

/-- **Dirichlet-sharpened Lehman bound, unconditional** (`thm:ls_five`). For all reals `t₁ < t₂`
with `168π < t₁`, `|∫_{t₁}^{t₂} S(t) dt| ≤ 5 + 0.128 log(t₂/2π)`, with no zero-freeness hypothesis
at the endpoints. This is the sharpest additive constant proved here. -/
theorem norm_integral_argZeta_le_five_unconditional {t₁ t₂ : ℝ} (ht1 : 168 * π < t₁)
    (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 5 + 0.128 * Real.log (t₂ / (2 * π)) :=
  norm_integral_argZeta_le_unconditional_of norm_integral_argZeta_le_five ht1 h12

end Unconditional

