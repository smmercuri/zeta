/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Zeros.IntervalRS
public import Enclosure.Sfrac

/-!
# Certificate-batch composition

`CertifiedZeroIntervals.append` concatenates two certified bundles given only the
`Separated` seam relation between the last interval of the first and the head interval of
the second. This is the primitive the sharded, auto-generated zero certificates fold
over: each batch's per-interval certificates and internal ordering are reused
verbatim, so the assembler only discharges the `O(#batches)` seam checks.

The generated assembler calls `CertifiedZeroIntervals.join`, which takes the batches as a
*flat list* plus two side conditions: every batch is nonempty, and consecutive batches are
`Separated`. Each seam is then
a standalone theorem built by `separated_of_le` (or `separated_of_lt`, for a gapped store) from
the batch's exposed `getLast?`/`head?` lemmas and one numeric comparison.

`append`, `Separated.append_right` and the `append_*` lemmas are the internal machinery of that
fold: `joinAux` appends one batch at a time and uses `Separated.append_right` to carry the
accumulator's seam invariant forward, since only the newest batch's last interval matters.

## Main definitions

- `Separated`: two bundles are ordered, i.e. the first's last interval ends at or before the
  second's first begins (`≤`, so shared endpoints are allowed).
- `CertifiedZeroIntervals.join`: concatenate a list of bundles, checking only adjacent seams.
- `CertifiedZeroIntervals.append`, `CertifiedZeroIntervals.ofCertified`: the binary primitive
  and the per-batch constructor.

## Main results

- `separated_of_le`, `separated_of_lt`: a seam from the endpoint lemmas plus `I.snd ≤ J.fst`
  (resp. `<`).
- `Separated.append_right`: a seam survives appending on the left.
- `BatchSpec`, `BatchSpec.bundle`: the statement a batch module exports (count and boundary
  endpoints) and the bundle recovered from it; `separated_of_endpoints` builds a seam from two
  batches' exported boundaries.
- `join_intervals`, `join_length`, `join_getLast?`: read a join's intervals, count and last
  interval without unfolding the fold.
-/
@[expose] public section


namespace Zeta.Certificates

/-- Two bundles are separated when the last interval of `C` ends at or before the first
interval of `D` begins. The relation is `≤`, so consecutive batches of a tiling may share an
endpoint. Vacuous if either bundle is empty. -/
def Separated (C D : CertifiedZeroIntervals) : Prop :=
  ∀ I ∈ C.intervals.getLast?, ∀ J ∈ D.intervals.head?, I.snd ≤ J.fst

/-- Build a seam from a bundle's exposed endpoint lemmas and one numeric comparison, so a
generated seam is a single term. -/
theorem separated_of_le {C D : CertifiedZeroIntervals} {I J : NonemptyInterval ℝ}
    (hC : C.intervals.getLast? = some I) (hD : D.intervals.head? = some J)
    (h : I.snd ≤ J.fst) : Separated C D := by
  intro I' hI' J' hJ'
  rw [hC, Option.mem_some_iff] at hI'
  rw [hD, Option.mem_some_iff] at hJ'
  subst hI'; subst hJ'; exact h

/-- `separated_of_le` specialised to a strict comparison, for a batch store whose consecutive
intervals are separated by a gap. -/
theorem separated_of_lt {C D : CertifiedZeroIntervals} {I J : NonemptyInterval ℝ}
    (hC : C.intervals.getLast? = some I) (hD : D.intervals.head? = some J)
    (h : I.snd < J.fst) : Separated C D :=
  separated_of_le hC hD h.le

/-- `separated_of_le` with the boundary read through `Option.map`: the form in which a batch
exports its endpoints (`BatchSpec`), so a seam between two batches is one numeric comparison
of literals. -/
theorem separated_of_endpoints {C D : CertifiedZeroIntervals} {b a : ℝ}
    (hC : C.intervals.getLast?.map (·.snd) = some b)
    (hD : D.intervals.head?.map (·.fst) = some a) (h : b ≤ a) : Separated C D := by
  intro I hI J hJ
  rw [Option.mem_def] at hI hJ
  rw [hI, Option.map_some] at hC
  rw [hJ, Option.map_some] at hD
  rw [Option.some.inj hC, Option.some.inj hD]; exact h

/-- `height_le_of_getLast?` with the boundary read through `Option.map`, as `BatchSpec`
exports it. -/
theorem CertifiedZeroIntervals.height_le_of_getLast?_snd (C : CertifiedZeroIntervals) {b q : ℝ}
    (h : C.intervals.getLast?.map (·.snd) = some b) (hq : b ≤ q) : C.height ≤ q := by
  obtain ⟨I, hI, hIb⟩ := Option.map_eq_some_iff.mp h
  exact C.height_le_of_getLast? hI (hIb ▸ hq)

/-- The statement a certificate batch exports: a certified bundle with `n` intervals exists
whose first interval starts at `an / ad` and whose last interval ends at `bn / bd` (the endpoints
as `Enclosure.sfrac` ratios, exactly as the certificate engine builds them from the store).

Only this statement crosses a batch's module boundary. The bundle itself (intervals, certificates,
disjointness chain) is the proof, and under the module system a theorem's proof stays in the
batch's private olean, so the size of each batch's import is independent of the height. The
assembler recovers the bundle through `BatchSpec.bundle`
(`Classical.choose`) and reads its count and boundaries off the three conjuncts. -/
abbrev BatchSpec (n an ad bn bd : ℕ) : Prop :=
  ∃ C : CertifiedZeroIntervals, C.intervals.length = n ∧
    C.intervals.head?.map (·.fst) = some (Enclosure.sfrac false an ad) ∧
    C.intervals.getLast?.map (·.snd) = some (Enclosure.sfrac false bn bd)

namespace BatchSpec

variable {n an ad bn bd : ℕ}

/-- The bundle a batch certifies. -/
noncomputable def bundle (h : BatchSpec n an ad bn bd) : CertifiedZeroIntervals := h.choose

@[simp] theorem bundle_length (h : BatchSpec n an ad bn bd) : h.bundle.intervals.length = n :=
  h.choose_spec.1

@[simp] theorem bundle_head? (h : BatchSpec n an ad bn bd) :
    h.bundle.intervals.head?.map (·.fst) = some (Enclosure.sfrac false an ad) :=
  h.choose_spec.2.1

@[simp] theorem bundle_getLast? (h : BatchSpec n an ad bn bd) :
    h.bundle.intervals.getLast?.map (·.snd) = some (Enclosure.sfrac false bn bd) :=
  h.choose_spec.2.2

theorem bundle_ne (h : BatchSpec n an ad bn bd) : h.bundle.intervals ≠ [] := by
  intro he
  have hh := h.bundle_head?
  rw [he] at hh
  simp at hh

end BatchSpec

/-- Concatenate two certified-zero-interval bundles, checking only the seam relation
between `C`'s last interval and `D`'s head interval. -/
def CertifiedZeroIntervals.append (C D : CertifiedZeroIntervals) (seam : Separated C D) :
    CertifiedZeroIntervals where
  intervals := C.intervals ++ D.intervals
  fst_nonneg := fun I hI ↦ (List.mem_append.1 hI).elim (C.fst_nonneg I) (D.fst_nonneg I)
  has_zero := fun I hI ↦ (List.mem_append.1 hI).elim (C.has_zero I) (D.has_zero I)
  disj := C.disj.append D.disj seam

@[simp] theorem CertifiedZeroIntervals.append_intervals (C D : CertifiedZeroIntervals)
    (seam : Separated C D) :
    (C.append D seam).intervals = C.intervals ++ D.intervals := rfl

/-- Build a certified bundle from a list of Euler–Maclaurin *certified* intervals (each interval
paired with its `Certificate`) plus the disjointness chain on the underlying intervals. This lets
a generated batch be a plain list of `⟨intervalᵢ, certᵢ⟩` pairs, with `fst_nonneg` and `has_zero`
derived once here for every batch.

This and `ofCertifiedRS` are the only method-aware definitions in the bundle API: they discharge
`has_zero` from their respective certificates, after which nothing downstream can tell which
approximation produced the intervals. In particular `join` may concatenate bundles of different
provenance, such as an Euler–Maclaurin batch at low heights with a Riemann–Siegel one above
`32π`. -/
def CertifiedZeroIntervals.ofCertifiedEM
    (l : List (Σ' I : ZIntervalEM, I.Certificate))
    (hdisj : (l.map (fun x ↦ x.1.toNonemptyInterval)).IsChain (fun I J ↦ I.snd ≤ J.fst)) :
    CertifiedZeroIntervals where
  intervals := l.map (fun x ↦ x.1.toNonemptyInterval)
  fst_nonneg := fun _ hI ↦ by
    obtain ⟨⟨_, c⟩, _, rfl⟩ := List.mem_map.1 hI; exact c.fst_nonneg
  has_zero := fun _ hI ↦ by
    obtain ⟨⟨I, c⟩, _, rfl⟩ := List.mem_map.1 hI
    exact riemannZeta.exists_zero_of_zIntervalEM_certificate I c
  disj := hdisj

/-- Build a certified bundle from a list of Riemann–Siegel certified intervals. The
Riemann–Siegel counterpart of `ofCertifiedEM`; see that declaration for why these two are the
only method-aware definitions here. A `ZIntervalRS` is a plain interval, so the bundle's
intervals are the list's first components. Each interval carries either certificate
(`ZIntervalRS.Certified`), so one batch can mix the linear-free and full approximants. -/
def CertifiedZeroIntervals.ofCertifiedRS
    (l : List (Σ' I : ZIntervalRS, I.Certified))
    (hdisj : (l.map PSigma.fst).IsChain (fun I J ↦ I.snd ≤ J.fst)) :
    CertifiedZeroIntervals where
  intervals := l.map PSigma.fst
  fst_nonneg := fun _ hI ↦ by
    obtain ⟨⟨_, c⟩, _, rfl⟩ := List.mem_map.1 hI
    exact c.elim (·.fst_nonneg) (·.fst_nonneg)
  has_zero := fun _ hI ↦ by
    obtain ⟨⟨I, c⟩, _, rfl⟩ := List.mem_map.1 hI
    exact riemannZeta.exists_zero_of_zIntervalRS_certified I c
  disj := hdisj

/-- The last interval of `C.append D` is the last interval of `D` (when `D` is nonempty),
so a left-fold's running seam only ever refers to the previous batch's last interval. -/
@[simp] theorem CertifiedZeroIntervals.append_getLast?
    (C D : CertifiedZeroIntervals) (seam : Separated C D) (hD : D.intervals ≠ []) :
    (C.append D seam).intervals.getLast? = D.intervals.getLast? :=
  List.getLast?_append_of_ne_nil _ hD

/-- A seam survives appending on the left: only the newest batch's last interval matters, so a
seam stated between two adjacent batches lifts to one against the whole accumulated fold.

Do not invoke this with dot notation: Lean's field notation matches the first argument whose
type head is `Separated`, including the implicit `seam`, so `h.append_right hne` binds `h` to
the wrong slot. Call it fully qualified. -/
theorem Separated.append_right {A C D : CertifiedZeroIntervals} {seam : Separated A C}
    (hne : C.intervals ≠ []) (h : Separated C D) : Separated (A.append C seam) D := by
  intro I hI J hJ
  rw [CertifiedZeroIntervals.append_getLast? _ _ _ hne] at hI
  exact h I hI J hJ

/-- The empty bundle. -/
def CertifiedZeroIntervals.empty : CertifiedZeroIntervals where
  intervals := []
  fst_nonneg := by simp
  has_zero := by simp
  disj := .nil

/-- Left-fold the bundles `l` onto the accumulator `acc`, given that `acc` is separated from
`l`'s head and that `l`'s own consecutive seams hold. Each step re-establishes the accumulator
invariant via `Separated.append_right`, so only the `O(#batches)` adjacent seams are checked. -/
def CertifiedZeroIntervals.joinAux (acc : CertifiedZeroIntervals) :
    (l : List CertifiedZeroIntervals) → (∀ C ∈ l, C.intervals ≠ []) →
      (∀ C ∈ l.head?, Separated acc C) → l.IsChain Separated → CertifiedZeroIntervals
  | [], _, _, _ => acc
  | C :: r, hne, hacc, h =>
      (acc.append C (hacc C rfl)).joinAux r
        (fun D hD ↦ hne D (List.mem_cons_of_mem _ hD))
        (fun D hD ↦ Separated.append_right (hne C (by simp)) (h.rel_head? hD))
        (List.isChain_cons.mp h).2

/-- Concatenate a whole list of certified bundles, checking only that consecutive entries
are `Separated`. The assembler names the batches once, in order, in a flat list. -/
def CertifiedZeroIntervals.join : (l : List CertifiedZeroIntervals) →
    (∀ C ∈ l, C.intervals ≠ []) → l.IsChain Separated → CertifiedZeroIntervals
  | [], _, _ => empty
  | C :: r, hne, h =>
      C.joinAux r (fun D hD ↦ hne D (List.mem_cons_of_mem _ hD))
        (fun _ hD ↦ h.rel_head? hD) (List.isChain_cons.mp h).2

theorem CertifiedZeroIntervals.joinAux_intervals (acc : CertifiedZeroIntervals)
    (l : List CertifiedZeroIntervals) (hne : ∀ C ∈ l, C.intervals ≠ [])
    (hacc : ∀ C ∈ l.head?, Separated acc C) (h : l.IsChain Separated) :
    (acc.joinAux l hne hacc h).intervals = acc.intervals ++ (l.map (·.intervals)).flatten := by
  induction l generalizing acc with
  | nil => simp [joinAux]
  | cons C r ih => rw [joinAux, ih]; simp

/-- The last interval of a join is the last interval of the last batch. -/
theorem CertifiedZeroIntervals.joinAux_getLast? (acc : CertifiedZeroIntervals)
    (l : List CertifiedZeroIntervals) (hne : ∀ C ∈ l, C.intervals ≠ [])
    (hacc : ∀ C ∈ l.head?, Separated acc C) (h : l.IsChain Separated) :
    (acc.joinAux l hne hacc h).intervals.getLast? =
      l.getLast?.elim acc.intervals.getLast? (·.intervals.getLast?) := by
  induction l generalizing acc with
  | nil => simp [joinAux]
  | cons C r ih =>
    rw [joinAux, ih]
    have hC : (acc.append C (hacc C rfl)).intervals.getLast? = C.intervals.getLast? :=
      CertifiedZeroIntervals.append_getLast? _ _ _ (hne C (by simp))
    match r with
    | [] => simpa using hC
    | D :: t =>
      rcases hlast : (D :: t).getLast? with _ | E
      · simp at hlast
      · simp [hlast]

/-- The intervals of a join are the batches' intervals, concatenated in order. -/
@[simp] theorem CertifiedZeroIntervals.join_intervals (l : List CertifiedZeroIntervals)
    (hne : ∀ C ∈ l, C.intervals ≠ []) (h : l.IsChain Separated) :
    (join l hne h).intervals = (l.map (·.intervals)).flatten := by
  cases l with
  | nil => simp [join, empty]
  | cons C r => simp [join, joinAux_intervals]

/-- A join's interval count is the sum of the batch sizes. -/
theorem CertifiedZeroIntervals.join_length (l : List CertifiedZeroIntervals)
    (hne : ∀ C ∈ l, C.intervals ≠ []) (h : l.IsChain Separated) :
    (join l hne h).intervals.length = (l.map (·.intervals.length)).sum := by
  simp [Function.comp_def]

/-- The bundle's last interval is the last batch's last interval, read off in `O(1)`. -/
@[simp] theorem CertifiedZeroIntervals.join_getLast? (l : List CertifiedZeroIntervals)
    (hne : ∀ C ∈ l, C.intervals ≠ []) (h : l.IsChain Separated) :
    (join l hne h).intervals.getLast? = l.getLast?.bind (·.intervals.getLast?) := by
  cases l with
  | nil => simp [join, empty]
  | cons C r =>
    rw [join, joinAux_getLast?]
    match r with
    | [] => simp
    | D :: t =>
      rcases hlast : (D :: t).getLast? with _ | E
      · simp at hlast
      · simp [hlast]

end Zeta.Certificates
