/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Enclosure.Sfrac
public import Enclosure.BinarySplit.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The binary-split engine over `ℕ`

The spec of `binarySplit` (defined in `Enclosure.BinarySplit.Defs`), which computes
`∑_{m≤i<n} ∏_{m≤j≤i} (p j / q j)` and the full product as numerator/denominator pairs over `ℕ`,
and the certificate equation lemmas (`binarySplit_of_le`/`_of_base*`/`_rec`), whose Boolean side
conditions (`Nat.beq`/`ble`/`blt`) are discharged by reflection. The signed rational `sfrac`
lives in `Enclosure.Sfrac` (opened below).

Following Bhavik Mehta's `Compute/LogSmallBig.lean`, the certificate lemmas carry the literal
result tuple, which the metaprogram (`Enclosure.BinarySplit.Tactic.Engine`) computes in `MetaM`, so
the kernel checks only `Nat.beq` equalities on numerals.
-/
@[expose] public section


namespace BSN
open Enclosure

/-! ### The binary-split engine

Each term is a running product `term_i = ∏_{m≤j≤i} (p j / q j)`, and `binarySplit` returns
`(T, Q, P)` with `∑ term_i = T/Q`, `∏ (p/q) = P/Q`, where `Q = ∏q` is the true common denominator
(no redundant factor). Combine: `T = Tl·Qr + Pl·Tr`, `Q = Ql·Qr`, `P = Pl·Pr`. -/

open Finset

/-- The `P`, `Q` components are products over the range. -/
theorem binarySplit_PQ {p q : ℕ → ℕ} {m n : ℕ} :
    (binarySplit p q m n).2.2 = ∏ j ∈ Ico m n, p j ∧
    (binarySplit p q m n).2.1 = ∏ j ∈ Ico m n, q j := by
  fun_induction binarySplit with
  | case1 m hlt => simp [Nat.Ico_succ_singleton]
  | case3 m n => simp_all
  | case2 m n hlt hne tl ql pl hL tr qr pr hR ihL ihR =>
    simp only [hL] at ihL; simp only [hR] at ihR
    have hmk : m ≤ (m + n) / 2 := by omega
    have hkn : (m + n) / 2 ≤ n := by omega
    refine ⟨?_, ?_⟩ <;>
      rw [← prod_Ico_consecutive _ hmk hkn] <;> simp [ihL.1, ihL.2, ihR.1, ihR.2]

theorem binarySplit_nonzero {p q : ℕ → ℕ} {m n : ℕ} (hq : ∀ i, q i ≠ 0) :
    (binarySplit p q m n).2.1 ≠ 0 := by
  fun_induction binarySplit <;> simp_all

/-- Spec: `T/Q` is the sum and `P/Q` is the product. -/
theorem binarySplit_spec {p q : ℕ → ℕ} {m n T Q P : ℕ} (hq : ∀ i, q i ≠ 0)
    (h : (T, Q, P) = binarySplit p q m n) :
    (∏ j ∈ Ico m n, ((p j : ℚ) / q j) = (P : ℚ) / Q) ∧
    (∑ i ∈ Ico m n, ∏ j ∈ Ico m (i + 1), ((p j : ℚ) / q j) = (T : ℚ) / Q) := by
  fun_induction binarySplit generalizing T Q P with
  | case1 m hlt =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hIco : Finset.Ico m (m + 1) = {m} := by
      ext x; rw [Finset.mem_Ico, Finset.mem_singleton]; omega
    simp [hIco]
  | case3 m n =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Ico_eq_empty (by omega : ¬ m < n)]
  | case2 m n hlt hne tl ql pl hL tr qr pr hR ihL ihR =>
    specialize ihL hL.symm; specialize ihR hR.symm
    have hmk : m ≤ (m + n) / 2 := by omega
    have hkn : (m + n) / 2 ≤ n := by omega
    obtain ⟨hPl, hSl⟩ := ihL
    obtain ⟨hPr, hSr⟩ := ihR
    obtain ⟨hPpl, hQl⟩ := (binarySplit_PQ (p := p) (q := q) (m := m) (n := (m + n) / 2))
    simp only [hL] at hPpl hQl
    obtain ⟨hPpr, hQr⟩ := (binarySplit_PQ (p := p) (q := q) (m := (m + n) / 2) (n := n))
    simp only [hR] at hPpr hQr
    have hqtl := binarySplit_nonzero (p := p) (m := m) (n := (m + n) / 2) hq
    simp only [hL] at hqtl
    have hqtr := binarySplit_nonzero (p := p) (m := (m + n) / 2) (n := n) hq
    simp only [hR] at hqtr
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hqlr : (ql : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqtl
    have hqrr : (qr : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqtr
    constructor
    · rw [← prod_Ico_consecutive _ hmk hkn, hPl, hPr]; push_cast; field_simp
    · rw [← sum_Ico_consecutive _ hmk hkn, hSl]
      have hsplit : ∑ i ∈ Ico ((m + n) / 2) n, ∏ j ∈ Ico m (i + 1), ((p j : ℚ) / q j)
          = ((pl : ℚ) / ql) * ∑ i ∈ Ico ((m + n) / 2) n, ∏ j ∈ Ico ((m + n) / 2) (i + 1),
              ((p j : ℚ) / q j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_Ico] at hi
        rw [← prod_Ico_consecutive _ hmk (by omega : (m + n) / 2 ≤ i + 1), hPl]
      rw [hsplit, hSr]
      push_cast
      field_simp

/-- A split from `0`: `Q ≠ 0`, and `T/Q` is the sum of the running products over `range n`. -/
theorem binarySplit_range_spec {p q : ℕ → ℕ} {n T Q P : ℕ} (hq : ∀ i, q i ≠ 0)
    (h : (T, Q, P) = binarySplit p q 0 n) :
    Q ≠ 0 ∧ ∑ i ∈ range n, ∏ j ∈ Ico 0 (i + 1), ((p j : ℚ) / q j) = (T : ℚ) / Q := by
  refine ⟨?_, by rw [range_eq_Ico]; exact (binarySplit_spec hq h).2⟩
  have hb := binarySplit_nonzero (p := p) (m := 0) (n := n) hq
  rw [← h] at hb
  simpa using hb

/-! ### Certificate equation lemmas (literal outputs tied by `beq`)

The Boolean side conditions use the primitive `Nat.add`/`Nat.mul`/..., so the kernel meets them
without unfolding `HAdd.hAdd → Add.add → Nat.add` per condition. -/

/-- Primitive-to-notation form of `Nat.div`, the companion of `Nat.add_eq`/`Nat.mul_eq`. -/
theorem Nat.div_eq' {a b : ℕ} : a.div b = a / b := rfl

theorem binarySplit_of_le {p q : ℕ → ℕ} {m n : ℕ} (h : n.ble m) :
    binarySplit p q m n = (0, 1, 1) := by
  rw [binarySplit]; simp only [Nat.ble_eq] at h; rw [dite_eq_right (by omega)]

/-- A leaf of the binary-splitting tree. Binders here and in the wider `binarySplit_of_base⟨w⟩` are
ordered least-changing first, so the olean shares identical application prefixes. -/
theorem binarySplit_of_base
    {m n : ℕ} (h2 : (m.succ).beq n) {q : ℕ → ℕ} {Q : ℕ} (hQ : Q.beq (q m)) {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq (p m)) {T : ℕ} (hT : T.beq (p m)) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  rw [binarySplit, dite_eq_left (by omega), dite_eq_left rfl]

theorem binarySplit_rec {p q : ℕ → ℕ}
    {m n k tl ql pl tr qr pr T Q P : ℕ}
    (h1 : (m.succ).blt n) (hk : k.beq ((m.add n).div 2))
    (hT : T.beq ((tl.mul qr).add (pl.mul tr))) (hQ : Q.beq (ql.mul qr))
    (hP : P.beq (pl.mul pr))
    (hl : binarySplit p q m k = (tl, ql, pl))
    (hr : binarySplit p q k n = (tr, qr, pr)) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.div_eq'] at h1 hk hT hQ hP
  subst hk hT hQ hP
  rw [binarySplit, dite_eq_left (by omega), dite_eq_right (by omega), hl, hr]

/-! Wider base cases: `_of_base2`/`3`/`4` each state a two- to four-leaf subtree (three, five or
seven nodes of the leaf/`_rec` shape) as one application, with the same midpoint splits and hence
the same literals, and single `Nat.beq` side conditions over the sequence values. -/

theorem binarySplit_of_base2
    {m n : ℕ} (h2 : (m.add 2).beq n) {q : ℕ → ℕ} {Q : ℕ} (hQ : Q.beq ((q m).mul (q (m.succ))))
    {P : ℕ} {p : ℕ → ℕ} (hP : P.beq ((p m).mul (p (m.succ)))) {T : ℕ}
    (hT : T.beq (((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 1) = (p m, q m, p m) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  have hr : binarySplit p q (m + 1) (m + 2) = (p (m + 1), q (m + 1), p (m + 1)) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base3
    {m n : ℕ} (h2 : (m.add 3).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq ((q m).mul ((q (m.succ)).mul (q (m.add 2))))) {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq ((p m).mul ((p (m.succ)).mul (p (m.add 2))))) {T : ℕ}
    (hT : T.beq (((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add
      ((p m).mul (((p (m.succ)).mul (q (m.add 2))).add
        ((p (m.succ)).mul (p (m.add 2))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 1) = (p m, q m, p m) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  have hr : binarySplit p q (m + 1) (m + 3) =
      (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2), q (m + 1) * q (m + 2),
        p (m + 1) * p (m + 2)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base4
    {m n : ℕ} (h2 : (m.add 4).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq (((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3))))) {P : ℕ}
    {p : ℕ → ℕ} (hP : P.beq (((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))))
    {T : ℕ}
    (hT : T.beq (((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul
        ((q (m.add 2)).mul (q (m.add 3)))).add
      (((p m).mul (p (m.succ))).mul
        (((p (m.add 2)).mul (q (m.add 3))).add ((p (m.add 2)).mul (p (m.add 3))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 2) =
      (p m * q (m + 1) + p m * p (m + 1), q m * q (m + 1), p m * p (m + 1)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 2) (m + 4) =
      (p (m + 2) * q (m + 3) + p (m + 2) * p (m + 3), q (m + 2) * q (m + 3),
        p (m + 2) * p (m + 3)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

/-! The rest of the ladder (widths 5-16, generated mechanically); `proveBS`
dispatches on `n - m` up to its cap. -/

theorem binarySplit_of_base5
    {m n : ℕ} (h2 : (m.add 5).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq (((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul ((q (m.add 3)).mul (q (m.add
        4))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq (((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add
        4))))))
    {T : ℕ}
    (hT : T.beq (((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add 2)).mul
        ((q (m.add 3)).mul (q (m.add 4))))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul
        ((q (m.add 3)).mul (q (m.add 4)))).add ((p (m.add 2)).mul (((p (m.add 3)).mul (q (m.add
        4))).add ((p (m.add 3)).mul (p (m.add 4))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 2) =
      (p m * q (m + 1) + p m * p (m + 1), q m * q (m + 1), p m * p (m + 1)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 2) (m + 5) =
      (p (m + 2) * (q (m + 3) * q (m + 4)) + p (m + 2) * (p (m + 3) * q (m + 4) + p (m + 3) * p (m
          + 4)), q (m + 2) * (q (m + 3) * q (m + 4)), p (m + 2) * (p (m + 3) * p (m + 4))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base6
    {m n : ℕ} (h2 : (m.add 6).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq (((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5))))))
    {T : ℕ}
    (hT : T.beq (((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 3) =
      (p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2)), q m
          * (q (m + 1) * q (m + 2)), p m * (p (m + 1) * p (m + 2))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 3) (m + 6) =
      (p (m + 3) * (q (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m
          + 5)), q (m + 3) * (q (m + 4) * q (m + 5)), p (m + 3) * (p (m + 4) * p (m + 5))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base7
    {m n : ℕ} (h2 : (m.add 7).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq (((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul (((q (m.add 3)).mul (q (m.add
        4))).mul ((q (m.add 5)).mul (q (m.add 6))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add
        4))).mul ((p (m.add 5)).mul (p (m.add 6))))))
    {T : ℕ}
    (hT : T.beq (((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul (((q (m.add 3)).mul (q
        (m.add 4))).mul ((q (m.add 5)).mul (q (m.add 6))))).add (((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((((p (m.add 3)).mul (q (m.add 4))).add ((p (m.add 3)).mul (p (m.add
        4)))).mul ((q (m.add 5)).mul (q (m.add 6)))).add (((p (m.add 3)).mul (p (m.add 4))).mul
        (((p (m.add 5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 3) =
      (p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2)), q m
          * (q (m + 1) * q (m + 2)), p m * (p (m + 1) * p (m + 2))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 3) (m + 7) =
      ((p (m + 3) * q (m + 4) + p (m + 3) * p (m + 4)) * (q (m + 5) * q (m + 6)) + p (m + 3) * p
          (m + 4) * (p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6)), q (m + 3) * q (m + 4) * (q (m
          + 5) * q (m + 6)), p (m + 3) * p (m + 4) * (p (m + 5) * p (m + 6))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base8
    {m n : ℕ} (h2 : (m.add 8).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q (m.add
        4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul (q (m.add 7))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add
        4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul (p (m.add 7))))))
    {T : ℕ}
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul (q (m.add 7))))).add ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul
        (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add
        5)))).mul ((q (m.add 6)).mul (q (m.add 7)))).add (((p (m.add 4)).mul (p (m.add 5))).mul
        (((p (m.add 6)).mul (q (m.add 7))).add ((p (m.add 6)).mul (p (m.add 7))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 4) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3)), q m * q (m + 1) * (q (m + 2) * q (m + 3)), p m
          * p (m + 1) * (p (m + 2) * p (m + 3))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 4) (m + 8) =
      ((p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5)) * (q (m + 6) * q (m + 7)) + p (m + 4) * p
          (m + 5) * (p (m + 6) * q (m + 7) + p (m + 6) * p (m + 7)), q (m + 4) * q (m + 5) * (q (m
          + 6) * q (m + 7)), p (m + 4) * p (m + 5) * (p (m + 6) * p (m + 7))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base9
    {m n : ℕ} (h2 : (m.add 9).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q (m.add
        4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add
        4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))))))
    {T : ℕ}
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))))).add ((((p m).mul (p (m.add
        1))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add
        ((p (m.add 4)).mul (p (m.add 5)))).mul ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add
        8))))).add (((p (m.add 4)).mul (p (m.add 5))).mul (((p (m.add 6)).mul ((q (m.add 7)).mul
        (q (m.add 8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p (m.add
        7)).mul (p (m.add 8))))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 4) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3)), q m * q (m + 1) * (q (m + 2) * q (m + 3)), p m
          * p (m + 1) * (p (m + 2) * p (m + 3))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 4) (m + 9) =
      ((p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5)) * (q (m + 6) * (q (m + 7) * q (m + 8))) + p
          (m + 4) * p (m + 5) * (p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q
          (m + 8) + p (m + 7) * p (m + 8))), q (m + 4) * q (m + 5) * (q (m + 6) * (q (m + 7) * q
          (m + 8))), p (m + 4) * p (m + 5) * (p (m + 6) * (p (m + 7) * p (m + 8)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base10
    {m n : ℕ} (h2 : (m.add 10).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul ((q (m.add 3)).mul (q (m.add
        4))))).mul (((q (m.add 5)).mul (q (m.add 6))).mul ((q (m.add 7)).mul ((q (m.add 8)).mul (q
        (m.add 9)))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add
        4))))).mul (((p (m.add 5)).mul (p (m.add 6))).mul ((p (m.add 7)).mul ((p (m.add 8)).mul (p
        (m.add 9)))))))
    {T : ℕ}
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4))))).add (((p m).mul (p (m.succ))).mul (((p (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4)))).add ((p (m.add 2)).mul (((p (m.add 3)).mul (q
        (m.add 4))).add ((p (m.add 3)).mul (p (m.add 4)))))))).mul (((q (m.add 5)).mul (q (m.add
        6))).mul ((q (m.add 7)).mul ((q (m.add 8)).mul (q (m.add 9)))))).add ((((p m).mul (p
        (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add 4))))).mul (((((p (m.add
        5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))).mul ((q (m.add 7)).mul ((q
        (m.add 8)).mul (q (m.add 9))))).add (((p (m.add 5)).mul (p (m.add 6))).mul (((p (m.add
        7)).mul ((q (m.add 8)).mul (q (m.add 9)))).add ((p (m.add 7)).mul (((p (m.add 8)).mul (q
        (m.add 9))).add ((p (m.add 8)).mul (p (m.add 9))))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 5) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * (q (m + 3) * q (m + 4))) + p m * p (m +
          1) * (p (m + 2) * (q (m + 3) * q (m + 4)) + p (m + 2) * (p (m + 3) * q (m + 4) + p (m +
          3) * p (m + 4))), q m * q (m + 1) * (q (m + 2) * (q (m + 3) * q (m + 4))), p m * p (m +
          1) * (p (m + 2) * (p (m + 3) * p (m + 4)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 5) (m + 10) =
      ((p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6)) * (q (m + 7) * (q (m + 8) * q (m + 9))) + p
          (m + 5) * p (m + 6) * (p (m + 7) * (q (m + 8) * q (m + 9)) + p (m + 7) * (p (m + 8) * q
          (m + 9) + p (m + 8) * p (m + 9))), q (m + 5) * q (m + 6) * (q (m + 7) * (q (m + 8) * q
          (m + 9))), p (m + 5) * p (m + 6) * (p (m + 7) * (p (m + 8) * p (m + 9)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base11
    {m n : ℕ} (h2 : (m.add 11).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul ((q (m.add 3)).mul (q (m.add
        4))))).mul (((q (m.add 5)).mul ((q (m.add 6)).mul (q (m.add 7)))).mul ((q (m.add 8)).mul
        ((q (m.add 9)).mul (q (m.add 10)))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add
        4))))).mul (((p (m.add 5)).mul ((p (m.add 6)).mul (p (m.add 7)))).mul ((p (m.add 8)).mul
        ((p (m.add 9)).mul (p (m.add 10)))))))
    {T : ℕ}
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4))))).add (((p m).mul (p (m.succ))).mul (((p (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4)))).add ((p (m.add 2)).mul (((p (m.add 3)).mul (q
        (m.add 4))).add ((p (m.add 3)).mul (p (m.add 4)))))))).mul (((q (m.add 5)).mul ((q (m.add
        6)).mul (q (m.add 7)))).mul ((q (m.add 8)).mul ((q (m.add 9)).mul (q (m.add 10)))))).add
        ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add 4))))).mul
        (((((p (m.add 5)).mul ((q (m.add 6)).mul (q (m.add 7)))).add ((p (m.add 5)).mul (((p
        (m.add 6)).mul (q (m.add 7))).add ((p (m.add 6)).mul (p (m.add 7)))))).mul ((q (m.add
        8)).mul ((q (m.add 9)).mul (q (m.add 10))))).add (((p (m.add 5)).mul ((p (m.add 6)).mul (p
        (m.add 7)))).mul (((p (m.add 8)).mul ((q (m.add 9)).mul (q (m.add 10)))).add ((p (m.add
        8)).mul (((p (m.add 9)).mul (q (m.add 10))).add ((p (m.add 9)).mul (p (m.add 10))))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 5) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * (q (m + 3) * q (m + 4))) + p m * p (m +
          1) * (p (m + 2) * (q (m + 3) * q (m + 4)) + p (m + 2) * (p (m + 3) * q (m + 4) + p (m +
          3) * p (m + 4))), q m * q (m + 1) * (q (m + 2) * (q (m + 3) * q (m + 4))), p m * p (m +
          1) * (p (m + 2) * (p (m + 3) * p (m + 4)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 5) (m + 11) =
      ((p (m + 5) * (q (m + 6) * q (m + 7)) + p (m + 5) * (p (m + 6) * q (m + 7) + p (m + 6) * p
          (m + 7))) * (q (m + 8) * (q (m + 9) * q (m + 10))) + p (m + 5) * (p (m + 6) * p (m + 7))
          * (p (m + 8) * (q (m + 9) * q (m + 10)) + p (m + 8) * (p (m + 9) * q (m + 10) + p (m +
          9) * p (m + 10))), q (m + 5) * (q (m + 6) * q (m + 7)) * (q (m + 8) * (q (m + 9) * q (m
          + 10))), p (m + 5) * (p (m + 6) * p (m + 7)) * (p (m + 8) * (p (m + 9) * p (m + 10))))
          :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base12
    {m n : ℕ} (h2 : (m.add 12).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))).mul (((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))).mul
        ((q (m.add 9)).mul ((q (m.add 10)).mul (q (m.add 11)))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5))))).mul (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        ((p (m.add 9)).mul ((p (m.add 10)).mul (p (m.add 11)))))))
    {T : ℕ}
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5)))))))).mul (((q (m.add 6)).mul
        ((q (m.add 7)).mul (q (m.add 8)))).mul ((q (m.add 9)).mul ((q (m.add 10)).mul (q (m.add
        11)))))).add ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p
        (m.add 4)).mul (p (m.add 5))))).mul (((((p (m.add 6)).mul ((q (m.add 7)).mul (q (m.add
        8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p (m.add 7)).mul (p
        (m.add 8)))))).mul ((q (m.add 9)).mul ((q (m.add 10)).mul (q (m.add 11))))).add (((p
        (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul (((p (m.add 9)).mul ((q (m.add
        10)).mul (q (m.add 11)))).add ((p (m.add 9)).mul (((p (m.add 10)).mul (q (m.add 11))).add
        ((p (m.add 10)).mul (p (m.add 11))))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 6) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * (q (m + 4) * q (m + 5))) + p m * (p (m + 1) * p (m + 2)) * (p (m + 3) * (q
          (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5))), q m
          * (q (m + 1) * q (m + 2)) * (q (m + 3) * (q (m + 4) * q (m + 5))), p m * (p (m + 1) * p
          (m + 2)) * (p (m + 3) * (p (m + 4) * p (m + 5)))) :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 6) (m + 12) =
      ((p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q (m + 8) + p (m + 7) * p
          (m + 8))) * (q (m + 9) * (q (m + 10) * q (m + 11))) + p (m + 6) * (p (m + 7) * p (m +
          8)) * (p (m + 9) * (q (m + 10) * q (m + 11)) + p (m + 9) * (p (m + 10) * q (m + 11) + p
          (m + 10) * p (m + 11))), q (m + 6) * (q (m + 7) * q (m + 8)) * (q (m + 9) * (q (m + 10)
          * q (m + 11))), p (m + 6) * (p (m + 7) * p (m + 8)) * (p (m + 9) * (p (m + 10) * p (m +
          11)))) :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base13
    {m n : ℕ} (h2 : (m.add 13).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))).mul (((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))).mul
        (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add 11)).mul (q (m.add 12)))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5))))).mul (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        (((p (m.add 9)).mul (p (m.add 10))).mul ((p (m.add 11)).mul (p (m.add 12)))))))
    {T : ℕ}
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5)))))))).mul (((q (m.add 6)).mul
        ((q (m.add 7)).mul (q (m.add 8)))).mul (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add
        11)).mul (q (m.add 12)))))).add ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p
        (m.add 3)).mul ((p (m.add 4)).mul (p (m.add 5))))).mul (((((p (m.add 6)).mul ((q (m.add
        7)).mul (q (m.add 8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p
        (m.add 7)).mul (p (m.add 8)))))).mul (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add
        11)).mul (q (m.add 12))))).add (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        (((((p (m.add 9)).mul (q (m.add 10))).add ((p (m.add 9)).mul (p (m.add 10)))).mul ((q
        (m.add 11)).mul (q (m.add 12)))).add (((p (m.add 9)).mul (p (m.add 10))).mul (((p (m.add
        11)).mul (q (m.add 12))).add ((p (m.add 11)).mul (p (m.add 12))))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 6) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * (q (m + 4) * q (m + 5))) + p m * (p (m + 1) * p (m + 2)) * (p (m + 3) * (q
          (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5))), q m
          * (q (m + 1) * q (m + 2)) * (q (m + 3) * (q (m + 4) * q (m + 5))), p m * (p (m + 1) * p
          (m + 2)) * (p (m + 3) * (p (m + 4) * p (m + 5)))) :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 6) (m + 13) =
      ((p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q (m + 8) + p (m + 7) * p
          (m + 8))) * (q (m + 9) * q (m + 10) * (q (m + 11) * q (m + 12))) + p (m + 6) * (p (m +
          7) * p (m + 8)) * ((p (m + 9) * q (m + 10) + p (m + 9) * p (m + 10)) * (q (m + 11) * q
          (m + 12)) + p (m + 9) * p (m + 10) * (p (m + 11) * q (m + 12) + p (m + 11) * p (m +
          12))), q (m + 6) * (q (m + 7) * q (m + 8)) * (q (m + 9) * q (m + 10) * (q (m + 11) * q
          (m + 12))), p (m + 6) * (p (m + 7) * p (m + 8)) * (p (m + 9) * p (m + 10) * (p (m + 11)
          * p (m + 12)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base14
    {m n : ℕ} (h2 : (m.add 14).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul (((q (m.add 3)).mul (q (m.add
        4))).mul ((q (m.add 5)).mul (q (m.add 6))))).mul (((q (m.add 7)).mul ((q (m.add 8)).mul (q
        (m.add 9)))).mul (((q (m.add 10)).mul (q (m.add 11))).mul ((q (m.add 12)).mul (q (m.add
        13)))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add
        4))).mul ((p (m.add 5)).mul (p (m.add 6))))).mul (((p (m.add 7)).mul ((p (m.add 8)).mul (p
        (m.add 9)))).mul (((p (m.add 10)).mul (p (m.add 11))).mul ((p (m.add 12)).mul (p (m.add
        13)))))))
    {T : ℕ}
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul (((q (m.add 3)).mul (q
        (m.add 4))).mul ((q (m.add 5)).mul (q (m.add 6))))).add (((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((((p (m.add 3)).mul (q (m.add 4))).add ((p (m.add 3)).mul (p (m.add
        4)))).mul ((q (m.add 5)).mul (q (m.add 6)))).add (((p (m.add 3)).mul (p (m.add 4))).mul
        (((p (m.add 5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))))))).mul (((q
        (m.add 7)).mul ((q (m.add 8)).mul (q (m.add 9)))).mul (((q (m.add 10)).mul (q (m.add
        11))).mul ((q (m.add 12)).mul (q (m.add 13)))))).add ((((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add 4))).mul ((p (m.add 5)).mul (p (m.add
        6))))).mul (((((p (m.add 7)).mul ((q (m.add 8)).mul (q (m.add 9)))).add ((p (m.add 7)).mul
        (((p (m.add 8)).mul (q (m.add 9))).add ((p (m.add 8)).mul (p (m.add 9)))))).mul (((q
        (m.add 10)).mul (q (m.add 11))).mul ((q (m.add 12)).mul (q (m.add 13))))).add (((p (m.add
        7)).mul ((p (m.add 8)).mul (p (m.add 9)))).mul (((((p (m.add 10)).mul (q (m.add 11))).add
        ((p (m.add 10)).mul (p (m.add 11)))).mul ((q (m.add 12)).mul (q (m.add 13)))).add (((p
        (m.add 10)).mul (p (m.add 11))).mul (((p (m.add 12)).mul (q (m.add 13))).add ((p (m.add
        12)).mul (p (m.add 13))))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 7) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))) + p m * (p (m + 1) * p (m + 2)) * ((p
          (m + 3) * q (m + 4) + p (m + 3) * p (m + 4)) * (q (m + 5) * q (m + 6)) + p (m + 3) * p
          (m + 4) * (p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6))), q m * (q (m + 1) * q (m +
          2)) * (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))), p m * (p (m + 1) * p (m + 2)) *
          (p (m + 3) * p (m + 4) * (p (m + 5) * p (m + 6)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 7) (m + 14) =
      ((p (m + 7) * (q (m + 8) * q (m + 9)) + p (m + 7) * (p (m + 8) * q (m + 9) + p (m + 8) * p
          (m + 9))) * (q (m + 10) * q (m + 11) * (q (m + 12) * q (m + 13))) + p (m + 7) * (p (m +
          8) * p (m + 9)) * ((p (m + 10) * q (m + 11) + p (m + 10) * p (m + 11)) * (q (m + 12) * q
          (m + 13)) + p (m + 10) * p (m + 11) * (p (m + 12) * q (m + 13) + p (m + 12) * p (m +
          13))), q (m + 7) * (q (m + 8) * q (m + 9)) * (q (m + 10) * q (m + 11) * (q (m + 12) * q
          (m + 13))), p (m + 7) * (p (m + 8) * p (m + 9)) * (p (m + 10) * p (m + 11) * (p (m + 12)
          * p (m + 13)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base15
    {m n : ℕ} (h2 : (m.add 15).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul (((q (m.add 3)).mul (q (m.add
        4))).mul ((q (m.add 5)).mul (q (m.add 6))))).mul ((((q (m.add 7)).mul (q (m.add 8))).mul
        ((q (m.add 9)).mul (q (m.add 10)))).mul (((q (m.add 11)).mul (q (m.add 12))).mul ((q
        (m.add 13)).mul (q (m.add 14)))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add
        4))).mul ((p (m.add 5)).mul (p (m.add 6))))).mul ((((p (m.add 7)).mul (p (m.add 8))).mul
        ((p (m.add 9)).mul (p (m.add 10)))).mul (((p (m.add 11)).mul (p (m.add 12))).mul ((p
        (m.add 13)).mul (p (m.add 14)))))))
    {T : ℕ}
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul (((q (m.add 3)).mul (q
        (m.add 4))).mul ((q (m.add 5)).mul (q (m.add 6))))).add (((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((((p (m.add 3)).mul (q (m.add 4))).add ((p (m.add 3)).mul (p (m.add
        4)))).mul ((q (m.add 5)).mul (q (m.add 6)))).add (((p (m.add 3)).mul (p (m.add 4))).mul
        (((p (m.add 5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))))))).mul ((((q
        (m.add 7)).mul (q (m.add 8))).mul ((q (m.add 9)).mul (q (m.add 10)))).mul (((q (m.add
        11)).mul (q (m.add 12))).mul ((q (m.add 13)).mul (q (m.add 14)))))).add ((((p m).mul ((p
        (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add 4))).mul ((p (m.add
        5)).mul (p (m.add 6))))).mul (((((((p (m.add 7)).mul (q (m.add 8))).add ((p (m.add 7)).mul
        (p (m.add 8)))).mul ((q (m.add 9)).mul (q (m.add 10)))).add (((p (m.add 7)).mul (p (m.add
        8))).mul (((p (m.add 9)).mul (q (m.add 10))).add ((p (m.add 9)).mul (p (m.add 10)))))).mul
        (((q (m.add 11)).mul (q (m.add 12))).mul ((q (m.add 13)).mul (q (m.add 14))))).add ((((p
        (m.add 7)).mul (p (m.add 8))).mul ((p (m.add 9)).mul (p (m.add 10)))).mul (((((p (m.add
        11)).mul (q (m.add 12))).add ((p (m.add 11)).mul (p (m.add 12)))).mul ((q (m.add 13)).mul
        (q (m.add 14)))).add (((p (m.add 11)).mul (p (m.add 12))).mul (((p (m.add 13)).mul (q
        (m.add 14))).add ((p (m.add 13)).mul (p (m.add 14))))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 7) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))) + p m * (p (m + 1) * p (m + 2)) * ((p
          (m + 3) * q (m + 4) + p (m + 3) * p (m + 4)) * (q (m + 5) * q (m + 6)) + p (m + 3) * p
          (m + 4) * (p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6))), q m * (q (m + 1) * q (m +
          2)) * (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))), p m * (p (m + 1) * p (m + 2)) *
          (p (m + 3) * p (m + 4) * (p (m + 5) * p (m + 6)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 7) (m + 15) =
      (((p (m + 7) * q (m + 8) + p (m + 7) * p (m + 8)) * (q (m + 9) * q (m + 10)) + p (m + 7) * p
          (m + 8) * (p (m + 9) * q (m + 10) + p (m + 9) * p (m + 10))) * (q (m + 11) * q (m + 12)
          * (q (m + 13) * q (m + 14))) + p (m + 7) * p (m + 8) * (p (m + 9) * p (m + 10)) * ((p (m
          + 11) * q (m + 12) + p (m + 11) * p (m + 12)) * (q (m + 13) * q (m + 14)) + p (m + 11) *
          p (m + 12) * (p (m + 13) * q (m + 14) + p (m + 13) * p (m + 14))), q (m + 7) * q (m + 8)
          * (q (m + 9) * q (m + 10)) * (q (m + 11) * q (m + 12) * (q (m + 13) * q (m + 14))), p (m
          + 7) * p (m + 8) * (p (m + 9) * p (m + 10)) * (p (m + 11) * p (m + 12) * (p (m + 13) * p
          (m + 14)))) :=
    binarySplit_of_base8 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base16
    {m n : ℕ} (h2 : (m.add 16).beq n) {q : ℕ → ℕ} {Q : ℕ}
    (hQ : Q.beq (((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q
        (m.add 4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul (q (m.add 7))))).mul ((((q (m.add
        8)).mul (q (m.add 9))).mul ((q (m.add 10)).mul (q (m.add 11)))).mul (((q (m.add 12)).mul
        (q (m.add 13))).mul ((q (m.add 14)).mul (q (m.add 15)))))))
    {P : ℕ} {p : ℕ → ℕ}
    (hP : P.beq (((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p
        (m.add 4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul (p (m.add 7))))).mul ((((p (m.add
        8)).mul (p (m.add 9))).mul ((p (m.add 10)).mul (p (m.add 11)))).mul (((p (m.add 12)).mul
        (p (m.add 13))).mul ((p (m.add 14)).mul (p (m.add 15)))))))
    {T : ℕ}
    (hT : T.beq (((((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul (q (m.add 7))))).add ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul
        (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add
        5)))).mul ((q (m.add 6)).mul (q (m.add 7)))).add (((p (m.add 4)).mul (p (m.add 5))).mul
        (((p (m.add 6)).mul (q (m.add 7))).add ((p (m.add 6)).mul (p (m.add 7)))))))).mul ((((q
        (m.add 8)).mul (q (m.add 9))).mul ((q (m.add 10)).mul (q (m.add 11)))).mul (((q (m.add
        12)).mul (q (m.add 13))).mul ((q (m.add 14)).mul (q (m.add 15)))))).add (((((p m).mul (p
        (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add 4)).mul (p (m.add
        5))).mul ((p (m.add 6)).mul (p (m.add 7))))).mul (((((((p (m.add 8)).mul (q (m.add
        9))).add ((p (m.add 8)).mul (p (m.add 9)))).mul ((q (m.add 10)).mul (q (m.add 11)))).add
        (((p (m.add 8)).mul (p (m.add 9))).mul (((p (m.add 10)).mul (q (m.add 11))).add ((p (m.add
        10)).mul (p (m.add 11)))))).mul (((q (m.add 12)).mul (q (m.add 13))).mul ((q (m.add
        14)).mul (q (m.add 15))))).add ((((p (m.add 8)).mul (p (m.add 9))).mul ((p (m.add 10)).mul
        (p (m.add 11)))).mul (((((p (m.add 12)).mul (q (m.add 13))).add ((p (m.add 12)).mul (p
        (m.add 13)))).mul ((q (m.add 14)).mul (q (m.add 15)))).add (((p (m.add 12)).mul (p (m.add
        13))).mul (((p (m.add 14)).mul (q (m.add 15))).add ((p (m.add 14)).mul (p (m.add
        15))))))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 8) =
      (((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3))) * (q (m + 4) * q (m + 5) * (q (m + 6) * q (m +
          7))) + p m * p (m + 1) * (p (m + 2) * p (m + 3)) * ((p (m + 4) * q (m + 5) + p (m + 4) *
          p (m + 5)) * (q (m + 6) * q (m + 7)) + p (m + 4) * p (m + 5) * (p (m + 6) * q (m + 7) +
          p (m + 6) * p (m + 7))), q m * q (m + 1) * (q (m + 2) * q (m + 3)) * (q (m + 4) * q (m +
          5) * (q (m + 6) * q (m + 7))), p m * p (m + 1) * (p (m + 2) * p (m + 3)) * (p (m + 4) *
          p (m + 5) * (p (m + 6) * p (m + 7)))) :=
    binarySplit_of_base8 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 8) (m + 16) =
      (((p (m + 8) * q (m + 9) + p (m + 8) * p (m + 9)) * (q (m + 10) * q (m + 11)) + p (m + 8) *
          p (m + 9) * (p (m + 10) * q (m + 11) + p (m + 10) * p (m + 11))) * (q (m + 12) * q (m +
          13) * (q (m + 14) * q (m + 15))) + p (m + 8) * p (m + 9) * (p (m + 10) * p (m + 11)) *
          ((p (m + 12) * q (m + 13) + p (m + 12) * p (m + 13)) * (q (m + 14) * q (m + 15)) + p (m
          + 12) * p (m + 13) * (p (m + 14) * q (m + 15) + p (m + 14) * p (m + 15))), q (m + 8) * q
          (m + 9) * (q (m + 10) * q (m + 11)) * (q (m + 12) * q (m + 13) * (q (m + 14) * q (m +
          15))), p (m + 8) * p (m + 9) * (p (m + 10) * p (m + 11)) * (p (m + 12) * p (m + 13) * (p
          (m + 14) * p (m + 15)))) :=
    binarySplit_of_base8 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

end BSN
