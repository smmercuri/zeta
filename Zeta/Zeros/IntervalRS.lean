/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Zeros.Interval
public import Zeta.RiemannSiegel.FirstOrder

/-!
# Riemann–Siegel certified intervals contain zeros

The analytic content of a `ZIntervalRS.Certificate`: the two endpoint values it records exceed the
first-order Riemann–Siegel error bound, so the true `Z` shares their (opposite) signs and has a
zero strictly between them.

This is the Riemann–Siegel counterpart of `riemannZeta.exists_zero_of_zIntervalEM_certificate`,
kept apart from `Zeta/Zeros/Interval.lean` because it is the one place a certificate meets
`abs_hardyZRemainderRS_le` (which depends on `PrimeNumberTheoremAnd`). Certificate batches import
only `Interval`; the conversion here is applied where the batches are assembled.

## Main results

- `riemannZeta.exists_zero_of_zIntervalRS_certificate`: a certified Riemann–Siegel interval
  contains a `ζ`-zero on the critical line.
- `riemannZeta.exists_zero_of_zIntervalRS_certificate₀`: likewise for the linear-free certificate.
- `riemannZeta.exists_zero_of_zIntervalRS_certified`: either certificate.
-/
@[expose] public section


open Zeta.Certificates

/-- **Two approximate endpoint values of opposite sign, each within its own error of `Z`, bracket
a zero of `ζ`** on the critical line, strictly between the endpoints. -/
theorem riemannZeta.exists_zero_of_approx_sign_change {a b va vb : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hsign : va * vb < 0) (hL : |Zeta.hardyZ a - va| < |va|)
    (hR : |Zeta.hardyZ b - vb| < |vb|) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  -- The true `Z` matches the sign of its approximant at each endpoint.
  have hsL : 0 < Zeta.hardyZ a * va := mul_pos_of_abs_sub_lt hL
  have hsR : 0 < Zeta.hardyZ b * vb := mul_pos_of_abs_sub_lt hR
  -- Hence the true `Z` changes sign across the interval.
  have hprod : Zeta.hardyZ a * Zeta.hardyZ b < 0 := by
    nlinarith [mul_pos hsL hsR, hsign]
  -- Continuity + the intermediate value theorem produce a zero of `Z`.
  have hcont : ContinuousOn Zeta.hardyZ (Set.Icc a b) :=
    continuousOn_hardyZ.mono fun x hx ↦ ha.trans hx.1
  obtain ⟨t₀, ht₀mem, ht₀⟩ : ∃ t₀ ∈ Set.Icc a b, Zeta.hardyZ t₀ = 0 := by
    rcases mul_neg_iff.mp hprod with ⟨hlp, hrn⟩ | ⟨hln, hrp⟩
    · exact intermediate_value_Icc' hab hcont ⟨hrn.le, hlp.le⟩
    · exact intermediate_value_Icc hab hcont ⟨hln.le, hrp.le⟩
  -- The endpoints have nonzero `Z`, so the zero is strictly interior.
  have hlne : Zeta.hardyZ a ≠ 0 := left_ne_zero_of_mul hsL.ne'
  have hrne : Zeta.hardyZ b ≠ 0 := left_ne_zero_of_mul hsR.ne'
  have ht₀Ioo : t₀ ∈ Set.Ioo a b :=
    ⟨lt_of_le_of_ne ht₀mem.1 fun heq ↦ hlne (by rw [heq]; exact ht₀),
     lt_of_le_of_ne ht₀mem.2 fun heq ↦ hrne (by rw [← heq]; exact ht₀)⟩
  -- A zero of `Z` on the critical line is a zero of `ζ`.
  exact ⟨t₀, ht₀Ioo, (hardyZ_eq_zero_iff_riemannZeta (ha.trans ht₀Ioo.1.le)).mp ht₀⟩

/-- **A Riemann–Siegel certified interval contains a zero of `ζ`** on the critical line, strictly
between its endpoints. -/
theorem riemannZeta.exists_zero_of_zIntervalRS_certificate (I : ZIntervalRS) (h : I.Certificate) :
    ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1 / 2 + Complex.I * t) = 0 :=
  riemannZeta.exists_zero_of_approx_sign_change I.fst_le_snd h.fst_nonneg h.is_sign_change
    ((abs_hardyZRemainderRS_le h.sixteen_le_fst_div).trans_lt
      (by simpa [Real.norm_eq_abs] using h.fst_error))
    ((abs_hardyZRemainderRS_le h.sixteen_le_snd_div).trans_lt
      (by simpa [Real.norm_eq_abs] using h.snd_error))

/-- **A linear-free Riemann–Siegel certified interval contains a zero of `ζ`** on the critical
line, strictly between its endpoints. -/
theorem riemannZeta.exists_zero_of_zIntervalRS_certificate₀ (I : ZIntervalRS)
    (h : I.Certificate₀) :
    ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  have h16 {t : ℝ} (ht : 32 * Real.pi ≤ t) : 16 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  exact riemannZeta.exists_zero_of_approx_sign_change I.fst_le_snd h.fst_nonneg h.is_sign_change
    ((abs_hardyZRemainderRS₀_le (h16 h.le_fst)).trans_lt
      (by simpa [Real.norm_eq_abs] using h.fst_error))
    ((abs_hardyZRemainderRS₀_le (h16 h.le_snd)).trans_lt
      (by simpa [Real.norm_eq_abs] using h.snd_error))

/-- **Either Riemann–Siegel certificate yields a zero of `ζ`** in the interval. -/
theorem riemannZeta.exists_zero_of_zIntervalRS_certified (I : ZIntervalRS) (h : I.Certified) :
    ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1 / 2 + Complex.I * t) = 0 :=
  h.elim (riemannZeta.exists_zero_of_zIntervalRS_certificate I)
    (riemannZeta.exists_zero_of_zIntervalRS_certificate₀ I)
