/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Zeros.HardyZ
public import Mathlib.Data.Real.Sign
public import Mathlib.Order.Interval.Basic
public import Zeta.RiemannSiegel.Defs

/-!
# Certified zero intervals

A `ZIntervalEM` is a closed interval carrying the Euler–Maclaurin data used to estimate Hardy's
`Z` at its endpoints; a `ZIntervalEM.Certificate` records that the two computed endpoint values
have opposite signs and exceed their error bounds, which forces a genuine sign change of `Z`.

A `CertifiedZeroIntervals` bundles a separated list of plain intervals together with the *fact*
that each brackets a `ζ`-zero, rather than the certificate that established it. That is the seam
between the approximation method and the counting argument: everything below this structure —
`height`, `zeros`, and the `N` bound — is method-agnostic, and each method supplies its own smart
constructor discharging `has_zero` from its own certificates. `ZIntervalRS` needs no per-endpoint
data at all, the Riemann–Siegel cutoff being determined by the height alone.

## Main definitions

- `ZIntervalEM`, `ZIntervalEM.Certificate`: one bracketed zero and its Euler–Maclaurin
  certificate; `ZIntervalRS`, the Riemann–Siegel counterpart.
- `CertifiedZeroIntervals`, `CertifiedZeroIntervals.height`, `CertifiedZeroIntervals.zeros`: a
  separated list of certified intervals, the largest right endpoint, and the bracketed zeros.

## Main results

- `riemannZeta.exists_zero_of_zIntervalEM_certificate`: a certified Euler–Maclaurin interval
  contains a `ζ`-zero on the critical line.

Two results one might expect here live elsewhere, for import hygiene: this file is imported by
every certificate batch, so it mentions the Riemann–Siegel approximant only through its
*definition* (`Zeta.RiemannSiegel.Defs`) and never touches the zero-counting function.
- `riemannZeta.exists_zero_of_zIntervalRS_certificate`, the Riemann–Siegel counterpart of the
  theorem above, is in `Zeta/Zeros/IntervalRS.lean`: it needs the first-order bound
  `abs_hardyZRemainderRS_le`, whose proof chapter is phrased in `PrimeNumberTheoremAnd`'s
  rectangle apparatus.
- `riemannZeta.le_N_of_certifiedZeroIntervals`, `C.intervals.length ≤ N(C.height)`, is in
  `Zeta/Zeros/Count.lean` with the rest of the counting side.
-/
@[expose] public section


namespace Zeta.Certificates

/-- A closed nonempty interval along with the parameters needed to compute the Euler-Maclaurin
approximation of Hardy's Z-function at the endpoints. -/
structure ZIntervalEM extends NonemptyInterval ℝ where
  /-- The Euler–Maclaurin cutoff used to estimate the lower `Z` value. -/
  fstCutoff : ℕ
  /-- The Euler–Maclaurin cutoff used to estimate the upper `Z` value. -/
  sndCutoff : ℕ
  /-- The number of Bernoulli terms used to estimate the lower `Z` value. -/
  fstBernoulli : ℕ
  /-- The number of Bernoulli terms used to estimate the upper `Z` value. -/
  sndBernoulli : ℕ

/-- A closed nonempty interval used to compute the Riemann-Siegel approximation of Hardy's `Z`. -/
abbrev ZIntervalRS := NonemptyInterval ℝ

/-- The approximate value of the Hardy Z function at the left endpoint. -/
noncomputable abbrev ZIntervalEM.fstVal (I : ZIntervalEM) : ℝ :=
  hardyZApproximantEM I.fstBernoulli I.fstCutoff I.fst

/-- The approximate value of the Hardy Z function at the right endpoint. -/
noncomputable abbrev ZIntervalEM.sndVal (I : ZIntervalEM) : ℝ :=
  hardyZApproximantEM I.sndBernoulli I.sndCutoff I.snd

/-- The approximate value of the Hardy Z function at the left endpoint. -/
noncomputable abbrev ZIntervalRS.fstVal (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS I.fst

/-- The approximate value of the Hardy Z function at the right endpoint. -/
noncomputable abbrev ZIntervalRS.sndVal (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS I.snd

/-- The approximate value of the Hardy Z function at the left endpoint, without the first-order
correction `C₁`; see `ZIntervalRS.Certificate₀`. -/
noncomputable abbrev ZIntervalRS.fstVal₀ (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS₀ I.fst

/-- The approximate value of the Hardy Z function at the right endpoint, without the first-order
correction `C₁`; see `ZIntervalRS.Certificate₀`. -/
noncomputable abbrev ZIntervalRS.sndVal₀ (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS₀ I.snd

/-- A certificate that the interval `I` brackets a genuine zero of Hardy's `Z` function,
using Euler-Maclaurin approximation of the `Z`-function. This certifies that the interval
equivalently contains a zero of `ζ` on the critical line. -/
structure ZIntervalEM.Certificate (I : ZIntervalEM) where
  /-- Required for the Riemann-Siegel theta function error bound. -/
  fst_nonneg : 0 ≤ I.fst
  /-- Required for the log-Γ Stirling remainder error bound. -/
  fstBernoulli_pos : 0 < I.fstBernoulli
  /-- Required for the zeta Euler-Maclaurin error bound. -/
  fstCutoff_pos : 0 < I.fstCutoff
  /-- At least one Bernoulli term is used at the right endpoint; see `leftBernoulli_pos`. -/
  sndBernoulli_pos : 0 < I.sndBernoulli
  /-- The right Euler–Maclaurin cutoff is positive; see `leftCutoff_pos`. -/
  sndCutoff_pos : 0 < I.sndCutoff
  /-- The two computed endpoint values have opposite signs. -/
  is_sign_change : I.fstVal * I.sndVal < 0
  /-- The computed left value exceeds its error bound, so the true `Z` shares its sign. -/
  fst_error : ‖I.fstVal‖ > hardyZErrorBoundEM I.fstBernoulli I.fstCutoff I.fst
  /-- The computed right value exceeds its error bound, so the true `Z` shares its sign. -/
  snd_error : ‖I.sndVal‖ > hardyZErrorBoundEM I.sndBernoulli I.sndCutoff I.snd

/-- A certificate that the interval `I` brackets a genuine zero of Hardy's `Z` function,
using Riemann-Siegel approximation of the `Z`-function. This certifies that the interval
equivalently contains a zero of `ζ` on the critical line. -/
structure ZIntervalRS.Certificate (I : ZIntervalRS) where
  /-- Required for the first-order Riemann–Siegel error bound, which holds only for `t ≥ 32π`.
  The same bound at the right endpoint follows via `I.fst_le_snd`; see `le_snd`. -/
  le_fst : 32 * Real.pi ≤ I.fst
  /-- The two computed endpoint values have opposite signs. -/
  is_sign_change : I.fstVal * I.sndVal < 0
  /-- The computed left value exceeds its error bound, so the true `Z` shares its sign. -/
  fst_error : ‖I.fstVal‖ > hardyZErrorBoundRS I.fst
  /-- The computed right value exceeds its error bound, so the true `Z` shares its sign. -/
  snd_error : ‖I.sndVal‖ > hardyZErrorBoundRS I.snd

namespace ZIntervalRS.Certificate

variable {I : ZIntervalRS}

/-- The threshold `t ≥ 32π` also holds at the right endpoint. -/
theorem le_snd (h : I.Certificate) : 32 * Real.pi ≤ I.snd := h.le_fst.trans I.fst_le_snd

/-- The left endpoint is nonnegative, as `CertifiedZeroIntervals` requires. -/
theorem fst_nonneg (h : I.Certificate) : 0 ≤ I.fst :=
  le_trans (by positivity) h.le_fst

/-- The left endpoint clears the Riemann–Siegel threshold in the `T = t/2π` normalisation, the
form `abs_hardyZRemainderRS_le` takes it in. -/
theorem sixteen_le_fst_div (h : I.Certificate) : 16 ≤ I.fst / (2 * Real.pi) := by
  rw [le_div_iff₀ (by positivity)]
  linarith [h.le_fst]

/-- The right endpoint clears the Riemann–Siegel threshold in the `T = t/2π` normalisation. -/
theorem sixteen_le_snd_div (h : I.Certificate) : 16 ≤ I.snd / (2 * Real.pi) := by
  rw [le_div_iff₀ (by positivity)]
  linarith [h.le_snd]

end ZIntervalRS.Certificate

/-- A certificate as `ZIntervalRS.Certificate`, but against the linear-free approximant
`hardyZApproximantRS₀` and its larger error bound `hardyZErrorBoundRS₀`. It is cheaper to build,
since there is no `C₁` enclosure, and suffices wherever both endpoint values clear the extra
`13/10·T^{-3/4}`; close zero pairs still need the full `Certificate`. -/
structure ZIntervalRS.Certificate₀ (I : ZIntervalRS) where
  /-- Required for the first-order Riemann–Siegel error bound; see `Certificate.le_fst`. -/
  le_fst : 32 * Real.pi ≤ I.fst
  /-- The two computed endpoint values have opposite signs. -/
  is_sign_change : I.fstVal₀ * I.sndVal₀ < 0
  /-- The computed left value exceeds its error bound, so the true `Z` shares its sign. -/
  fst_error : ‖I.fstVal₀‖ > hardyZErrorBoundRS₀ I.fst
  /-- The computed right value exceeds its error bound, so the true `Z` shares its sign. -/
  snd_error : ‖I.sndVal₀‖ > hardyZErrorBoundRS₀ I.snd

namespace ZIntervalRS.Certificate₀

variable {I : ZIntervalRS}

/-- The threshold `t ≥ 32π` also holds at the right endpoint. -/
theorem le_snd (h : I.Certificate₀) : 32 * Real.pi ≤ I.snd := h.le_fst.trans I.fst_le_snd

/-- The left endpoint is nonnegative, as `CertifiedZeroIntervals` requires. -/
theorem fst_nonneg (h : I.Certificate₀) : 0 ≤ I.fst :=
  le_trans (by positivity) h.le_fst

end ZIntervalRS.Certificate₀

/-- What a Riemann–Siegel batch records per interval: either certificate. The metaprogram tries
the cheaper `Certificate₀` first and falls back to the full `Certificate`. -/
abbrev ZIntervalRS.Certified (I : ZIntervalRS) : Prop := I.Certificate ∨ I.Certificate₀

/-- A list of certified zero intervals, ordered and pairwise disjoint. -/
structure CertifiedZeroIntervals where
  intervals : List (NonemptyInterval ℝ)
  fst_nonneg : ∀ I ∈ intervals, 0 ≤ I.fst
  has_zero : ∀ I ∈ intervals, ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1/2 + Complex.I * t) = 0
  disj : intervals.IsChain fun I J ↦ I.snd ≤ J.fst


/-- The height of a certified list: the largest right endpoint (`0` if the list is empty). -/
@[simp]
noncomputable def CertifiedZeroIntervals.height (C : CertifiedZeroIntervals) : ℝ :=
  if h : C.intervals = [] then 0 else (C.intervals.maxOn (fun I ↦ I.snd) h).snd

/-- Every interval of a certified list ends below its height. -/
theorem CertifiedZeroIntervals.le_height (C : CertifiedZeroIntervals)
    {I : NonemptyInterval ℝ} (hI : I ∈ C.intervals) : I.snd ≤ C.height := by
  rw [CertifiedZeroIntervals.height, dif_neg (List.ne_nil_of_mem hI)]
  exact List.le_apply_maxOn_of_mem (f := fun I : NonemptyInterval ℝ ↦ I.snd) hI

/-- The intervals of a `CertifiedZeroIntervals` are pairwise separated: every earlier interval
ends at or before every later one begins. -/
theorem CertifiedZeroIntervals.pairwise (C : CertifiedZeroIntervals) :
    C.intervals.Pairwise (fun I J ↦ I.snd ≤ J.fst) :=
  have : Trans (fun I J : NonemptyInterval ℝ ↦ I.snd ≤ J.fst)
      (fun I J : NonemptyInterval ℝ ↦ I.snd ≤ J.fst)
      (fun I J : NonemptyInterval ℝ ↦ I.snd ≤ J.fst) :=
    ⟨fun {_ b _} hab hbc ↦ (hab.trans b.fst_le_snd).trans hbc⟩
  List.isChain_iff_pairwise.mp C.disj

end Zeta.Certificates

open Zeta.Certificates

/-- A real number within `|b|` of `b` shares `b`'s (necessarily nonzero) sign. -/
theorem Zeta.Certificates.mul_pos_of_abs_sub_lt {a b : ℝ} (h : |a - b| < |b|) :
    0 < a * b := by
  nlinarith [mul_self_lt_mul_self (abs_nonneg (a - b)) h, abs_mul_abs_self (a - b),
    abs_mul_abs_self b, sq_nonneg a]

/-- **A certified zero interval contains a zero of `ζ`** on the critical line, strictly between
its endpoints. -/
theorem riemannZeta.exists_zero_of_zIntervalEM_certificate (I : ZIntervalEM) (h : I.Certificate) :
    ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1 / 2 + Complex.I * t) = 0 := by
  have hlr : I.fst ≤ I.snd := I.fst_le_snd
  have hr0 : 0 ≤ I.snd := h.fst_nonneg.trans hlr
  -- The true `Z` matches the sign of its Euler–Maclaurin approximant at each endpoint.
  have hL : |hardyZ I.fst - I.fstVal| < |I.fstVal| :=
    (abs_hardyZRemainderEM_le h.fstBernoulli_pos h.fstCutoff_pos h.fst_nonneg).trans_lt
      (by simpa [Real.norm_eq_abs] using h.fst_error)
  have hR : |hardyZ I.snd - I.sndVal| < |I.sndVal| :=
    (abs_hardyZRemainderEM_le h.sndBernoulli_pos h.sndCutoff_pos hr0).trans_lt
      (by simpa [Real.norm_eq_abs] using h.snd_error)
  have hsL : 0 < hardyZ I.fst * I.fstVal := mul_pos_of_abs_sub_lt hL
  have hsR : 0 < hardyZ I.snd * I.sndVal := mul_pos_of_abs_sub_lt hR
  -- Hence the true `Z` changes sign across the interval.
  have hprod : hardyZ I.fst * hardyZ I.snd < 0 := by
    nlinarith [mul_pos hsL hsR, h.is_sign_change]
  -- Continuity + the intermediate value theorem produce a genuine zero of `Z`.
  have hcont : ContinuousOn hardyZ (Set.Icc I.fst I.snd) :=
    continuousOn_hardyZ.mono fun x hx ↦ h.fst_nonneg.trans hx.1
  obtain ⟨t₀, ht₀mem, ht₀⟩ : ∃ t₀ ∈ Set.Icc I.fst I.snd, hardyZ t₀ = 0 := by
    rcases mul_neg_iff.mp hprod with ⟨hlp, hrn⟩ | ⟨hln, hrp⟩
    · exact intermediate_value_Icc' hlr hcont ⟨hrn.le, hlp.le⟩
    · exact intermediate_value_Icc hlr hcont ⟨hln.le, hrp.le⟩
  -- The endpoints have nonzero `Z`, so the zero is strictly interior.
  have hlne : hardyZ I.fst ≠ 0 := left_ne_zero_of_mul hsL.ne'
  have hrne : hardyZ I.snd ≠ 0 := left_ne_zero_of_mul hsR.ne'
  have ht₀Ioo : t₀ ∈ Set.Ioo I.fst I.snd :=
    ⟨lt_of_le_of_ne ht₀mem.1 fun heq ↦ hlne (by rw [heq]; exact ht₀),
     lt_of_le_of_ne ht₀mem.2 fun heq ↦ hrne (by rw [← heq]; exact ht₀)⟩
  -- A zero of `Z` on the critical line is a zero of `ζ`.
  exact ⟨t₀, ht₀Ioo, (hardyZ_eq_zero_iff_riemannZeta (h.fst_nonneg.trans ht₀Ioo.1.le)).mp ht₀⟩

namespace Zeta.Certificates

open Complex Set

/-- The list of critical-line `ζ`-zeros bracketed by a certified list of intervals, one per
interval. -/
noncomputable def CertifiedZeroIntervals.zeros (C : CertifiedZeroIntervals) : List ℂ :=
  (C.intervals.pmap (fun I hI ↦ (C.has_zero I hI).choose) (by simp)).map
      fun t : ℝ ↦ 1/2 + I * t

/-- An empty certified list brackets no zeros. -/
theorem CertifiedZeroIntervals.zeros_empty (C : CertifiedZeroIntervals) (hC : C.intervals = []) :
    C.zeros = [] := by
  simp [CertifiedZeroIntervals.zeros, hC]

/-- The bracketed points are `ζ`-zeros of height in `(0, C.height)`. -/
theorem CertifiedZeroIntervals.zeros_spec (C : CertifiedZeroIntervals) :
    ∀ z ∈ C.zeros, z.im ∈ Ioo 0 C.height ∧ riemannZeta z = 0 := by
  intro z hz
  simp only [CertifiedZeroIntervals.zeros, List.mem_map] at hz
  rcases hz with ⟨I, hI, rfl⟩
  simp only [one_div, List.mem_pmap] at hI
  obtain ⟨a, ha, rfl⟩ := hI
  have := (C.has_zero a ha).choose_spec
  refine ⟨?_, by grind⟩
  convert Ioo_subset_Ioo (C.fst_nonneg _ ha) (le_height C ha) this.1
  simp

/-- One bracketed zero per interval. -/
theorem CertifiedZeroIntervals.zeros_length (C : CertifiedZeroIntervals) :
    C.zeros.length = C.intervals.length := by
  simp [CertifiedZeroIntervals.zeros, List.length_map, List.length_pmap]

/-- The bracketed zeros are distinct, the intervals being separated. -/
theorem CertifiedZeroIntervals.zeros_nodup (C : CertifiedZeroIntervals) :
    C.zeros.Nodup := by
  have hpair := C.pairwise
  -- The intervals are distinct: two equal intervals at positions `i < j` would give
  -- `I.right ≤ I.left`, but a certified interval brackets a zero in its open interior, so
  -- `I.left < I.right`. (Strictness of the chain is not available under the `≤` relation.)
  have hInod : C.intervals.Nodup := by
    rw [show C.intervals.Nodup = List.Pairwise (· ≠ ·) C.intervals from rfl,
      List.pairwise_iff_getElem]
    intro i j hi hj hlt heq
    have hsep := List.pairwise_iff_getElem.mp hpair i j hi hj hlt
    obtain ⟨t, ht, -⟩ := C.has_zero _ (List.getElem_mem hi)
    rw [← heq] at hsep
    exact absurd (ht.1.trans ht.2) (not_lt.mpr hsep)
  -- ...and any two distinct ones are comparable (each lies at or left of the other).
  have hcomp : ∀ I ∈ C.intervals, ∀ J ∈ C.intervals, I ≠ J →
      I.snd ≤ J.fst ∨ J.snd ≤ I.fst := by
    intro I hI J hJ hne
    have hpg := List.pairwise_iff_getElem.mp hpair
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hI
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hJ
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inl (hpg i j hi hj h)
    · subst h; exact absurd rfl hne
    · exact Or.inr (hpg j i hj hi h)
  -- The chosen zeros (before mapping into `ℂ`) are already distinct.
  have key : (C.intervals.pmap
      (fun I hI ↦ (C.has_zero I hI).choose) (by simp)).Nodup := by
    refine List.Nodup.pmap (fun I hI J hJ heq ↦ ?_) hInod
    by_contra hne
    have hsI := (C.has_zero I hI).choose_spec.1
    have hsJ := (C.has_zero J hJ).choose_spec.1
    rw [Set.mem_Ioo] at hsI hsJ
    rw [heq] at hsI
    rcases hcomp I hI J hJ hne with h | h
    · linarith [hsI.2, hsJ.1, h]
    · linarith [hsI.1, hsJ.2, h]
  rw [zeros]
  exact List.Nodup.map (f := fun t : ℝ ↦ 1 / 2 + Complex.I * t)
    (fun a b h ↦ by simpa using h) key

/-- The bracketed zeros lie on the critical line. -/
theorem CertifiedZeroIntervals.zeros_re (C : CertifiedZeroIntervals) {z : ℂ} (hz : z ∈ C.zeros) :
    z.re = 1 / 2 := by
  simp only [CertifiedZeroIntervals.zeros, List.mem_map] at hz
  rcases hz with ⟨I, hI, rfl⟩
  simp only [one_div, List.mem_pmap] at hI
  obtain ⟨a, ha, rfl⟩ := hI
  simp

/-- The bracketed zeros have height in `(0, C.height)`. -/
theorem CertifiedZeroIntervals.zeros_im (C : CertifiedZeroIntervals) {z : ℂ} (hz : z ∈ C.zeros) :
    z.im ∈ Ioo 0 C.height :=
  (C.zeros_spec z hz).1

/-- Upper bound on the certified height, from a bound on every interval's right endpoint. -/
theorem CertifiedZeroIntervals.height_le (C : CertifiedZeroIntervals) {r : ℝ} (h0 : 0 ≤ r)
    (hr : ∀ I ∈ C.intervals, I.snd ≤ r) : C.height ≤ r := by
  rw [CertifiedZeroIntervals.height]
  split
  · exact h0
  · exact hr _ List.maxOn_mem

/-- In a chain ordered by `I.snd ≤ J.fst`, every interval's right endpoint is `≤` the last
one's. -/
private theorem snd_le_getLast_isChain : ∀ {l : List (NonemptyInterval ℝ)} (hne : l ≠ [])
    (_ : l.IsChain (fun I J ↦ I.snd ≤ J.fst)) {I}, I ∈ l →
    I.snd ≤ (l.getLast hne).snd
  | [], hne, _, _, _ => absurd rfl hne
  | [_], _, _, _, hI => by rw [List.mem_singleton] at hI; subst hI; simp
  | _ :: b :: t, _, hc, _, hI => by
    rw [List.isChain_cons_cons] at hc
    rw [List.getLast_cons (List.cons_ne_nil b t)]
    rcases List.mem_cons.1 hI with rfl | hI'
    · exact hc.1.trans (b.fst_le_snd.trans
        (snd_le_getLast_isChain (List.cons_ne_nil b t) hc.2 List.mem_cons_self))
    · exact snd_le_getLast_isChain (List.cons_ne_nil b t) hc.2 hI'

/-- The certified height is the last interval's right endpoint, up to `≤`. -/
theorem CertifiedZeroIntervals.height_le_getLast (C : CertifiedZeroIntervals)
    (hne : C.intervals ≠ []) : C.height ≤ (C.intervals.getLast hne).snd := by
  refine C.height_le (le_trans (C.fst_nonneg _ (List.getLast_mem hne))
    (C.intervals.getLast hne).fst_le_snd) (fun I hI ↦ snd_le_getLast_isChain hne C.disj hI)

/-- The certified height is bounded by any `q` dominating the last interval's right endpoint.

The last interval is supplied through `getLast? = some I` with `I` **implicit**, mirroring
`separated_of_le`: a caller can pass `rfl` and let unification whnf the bundle and read the
boundary off it, so a batch built by a metaprogram — which names none of its intervals — needs
to expose no `getLast?` lemma of its own. -/
theorem CertifiedZeroIntervals.height_le_of_getLast? (C : CertifiedZeroIntervals)
    {I : NonemptyInterval ℝ} {q : ℝ} (h : C.intervals.getLast? = some I) (hq : I.snd ≤ q) :
    C.height ≤ q := by
  have hne : C.intervals ≠ [] := by
    intro he
    rw [he] at h
    simp at h
  refine (C.height_le_getLast hne).trans ?_
  rwa [show C.intervals.getLast hne = I from
    Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans h)]

end Zeta.Certificates
