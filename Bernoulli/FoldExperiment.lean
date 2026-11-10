/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Bernoulli.TangentVerify

/-!
# Tangent numbers via a computable fold

The tangent-number emitter `Bernoulli.BernoulliValues` uses
(`fold_emit_tangent_numbers 99`). A computable step function `dstep` (one fused double-pass per
tangent number, over compressed rows) computes the Knuth table, one kernel reduction proves the
whole list of tangent numbers, and an `O(N)` peel-chain reads off each
`tangentNumberLit_k : tangentNumber k = Tₖ`. `foldLink` proves the fold correct against `knuth`,
so the emitted lemmas are axiom-clean. -/
@[expose] public section


open scoped Nat

namespace TangentNumbers

/-! ### Compressed rows

A Knuth-table row is a tangent polynomial's coefficient list, which vanishes on alternating
indices, so only the nonzero coefficients are stored; each Knuth step flips the parity of the
support. A `dstep` advances two parity flips at once in a single traversal (`combF`), reading one
tangent number in between. Each pass is a raw `List.rec` sliding window over curried `Nat`
arguments, spelled with `Nat.*` for the native fast path. `combP1`/`stepP1` only seed the first
row. -/

/-- Odd-support row → even-support row: `bᵢ = (2i-1)·aᵢ₋₁ + (2i+1)·aᵢ` (`a₋₁ = 0`, trailing
`(2i-1)·aₘ`).  Window carried as `(index i, prev = aᵢ₋₁)`. -/
noncomputable def combP1 : List Nat → Nat → Nat → List Nat :=
  List.rec (motive := fun _ => Nat → Nat → List Nat)
    (fun i prev => [Nat.mul (Nat.sub (Nat.mul 2 i) 1) prev])
    (fun c _ ih i prev =>
      Nat.add (Nat.mul (Nat.sub (Nat.mul 2 i) 1) prev) (Nat.mul (Nat.add (Nat.mul 2 i) 1) c)
        :: ih (Nat.add i 1) c)

noncomputable def stepP1 (a : List Nat) : List Nat := combP1 a 0 0

/-- The left coefficient of the fused double-step (two Knuth passes as one 3-term window)
`cⱼ = 2(2j-1)(j-1)·aⱼ₋₁ + 8j²·aⱼ + 2(2j+1)(j+1)·aⱼ₊₁`; `coM` and `coR` are the other two. -/
def coL (j : Nat) : Nat := Nat.mul 2 (Nat.mul (Nat.sub (Nat.mul 2 j) 1) (Nat.sub j 1))
def coM (j : Nat) : Nat := Nat.mul 8 (Nat.mul j j)
def coR (j : Nat) : Nat := Nat.mul 2 (Nat.mul (Nat.add (Nat.mul 2 j) 1) (Nat.add j 1))

/-- One parity-0 row to the next, fused.  Window carried as `(index j, aⱼ₋₁, aⱼ)`; the list supplies
`aⱼ₊₁`.  Seeded with `j = 0, aⱼ₋₁ = 0, aⱼ = a₀`; the two trailing entries close off `aⱼ₊₁ = 0`. -/
noncomputable def combF : List Nat → Nat → Nat → Nat → List Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → List Nat)
    (fun j p q => [Nat.add (Nat.mul (coL j) p) (Nat.mul (coM j) q), Nat.mul (coL (Nat.add j 1)) q])
    (fun nx _ ih j p q =>
      Nat.add (Nat.add (Nat.mul (coL j) p) (Nat.mul (coM j) q)) (Nat.mul (coR j) nx)
        :: ih (Nat.add j 1) q nx)

/-- One fused double-step on `(parity-0 row, accumulated tangents)`: the head `a₀` of the row is the
next tangent number, prepended to the accumulator, and seeds `combF`. -/
noncomputable def dstep : List Nat × List Nat → List Nat × List Nat :=
  fun t => List.rec (motive := fun _ => List Nat × List Nat) ([], t.2)
    (fun a0 rest _ => (combF rest 0 0 a0, a0 :: t.2)) t.1

/-- Apply `dstep` `n` times to `(current parity-0 row, accumulated tangents)`. -/
noncomputable def iterD (n : Nat) (s : List Nat × List Nat) : List Nat × List Nat :=
  Nat.rec (motive := fun _ => List Nat × List Nat) s (fun _ ih => dstep ih) n

/-- Reduces to `[T_N, T_{N-1}, …, T_1]` (reversed, from the prepend in `dstep`). -/
noncomputable def tangentListN (N : Nat) : List Nat := (iterD N (stepP1 [1], [])).2

/-! ### Correctness

`foldLink`: the fold computes the tangent numbers, proved against the Knuth table `knuth` of
`Bernoulli.TangentVerify` via the row invariant `rowInv`, the two-step recurrence
`knuth_two_step`/`combF_window`, and the accumulator invariant `accInv`. -/

/-- `s` even-index entries of Knuth row `m` from column `2j`; recursive so it peels from the
front. -/
noncomputable def erow (m j : ℕ) : ℕ → List ℕ
  | 0 => []
  | s + 1 => knuth m (2 * j) :: erow m (j + 1) s

/-- The fused coefficients encode two `knuth_succ` steps: `knuth (m+2) (2j)` as a 3-term
combination. -/
theorem knuth_two_step (m j : ℕ) :
    knuth (m + 2) (2 * j) =
      coL j * knuth m (2 * j - 2) + coM j * knuth m (2 * j) + coR j * knuth m (2 * j + 2) := by
  simp only [coL, coM, coR]
  cases j with
  | zero => grind [knuth_succ_zero, knuth_succ]
  | succ j =>
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by ring, knuth_succ,
        show 2 * j + 1 + 2 = (2 * j + 2) + 1 from by ring, knuth_succ,
        show 2 * j + 1 = 2 * j + 1 from rfl, knuth_succ]
    grind

theorem combF_nil (j p q : ℕ) : combF [] j p q = [coL j * p + coM j * q, coL (j + 1) * q] := rfl

theorem combF_cons (nx : ℕ) (rest : List ℕ) (j p q : ℕ) :
    combF (nx :: rest) j p q
        = (coL j * p + coM j * q + coR j * nx) :: combF rest (j + 1) q nx := rfl

/-- `combF` carries the even entries of Knuth row `m` (window at index `j`) to those of row `m+2`,
once the window has reached past the diagonal (`hb`). -/
theorem combF_window (m j s : ℕ) (hb : m + 1 < 2 * (j + s + 1)) :
    combF (erow m (j + 1) s) j (knuth m (2 * j - 2)) (knuth m (2 * j))
        = erow (m + 2) j (s + 2) := by
  induction s generalizing j with
  | zero =>
    rw [erow, combF_nil, erow, erow, erow]
    have h1 : knuth m (2 * j + 2) = 0 := knuth_eq_zero m _ (by omega)
    have h2 : knuth m (2 * j + 4) = 0 := knuth_eq_zero m _ (by omega)
    have ej : knuth m (2 * (j + 1)) = knuth m (2 * j + 2) := by rw [Nat.mul_add, Nat.mul_one]
    rw [knuth_two_step m j, h1, knuth_two_step m (j + 1),
        show 2 * (j + 1) - 2 = 2 * j from by omega, show 2 * (j + 1) + 2 = 2 * j + 4 from by omega,
        h2, ej, h1]
    simp
  | succ s ih =>
    rw [erow, combF_cons]
    have ej : knuth m (2 * (j + 1)) = knuth m (2 * j + 2) := by rw [Nat.mul_add, Nat.mul_one]
    have hhead : coL j * knuth m (2 * j - 2) + coM j * knuth m (2 * j)
        + coR j * knuth m (2 * (j + 1))
        = knuth (m + 2) (2 * j) := by rw [knuth_two_step m j, ej]
    have hrec := ih (j + 1) (by omega)
    rw [show 2 * (j + 1) - 2 = 2 * j from by omega] at hrec
    rw [hhead, hrec]
    conv_rhs => rw [erow]

/-- At `j = 0` the seed `p` is killed by `coL 0 = 0`. -/
theorem combF_p0 (rest : List ℕ) (p q : ℕ) : combF rest 0 p q = combF rest 0 0 q := by
  cases rest with
  | nil => simp [combF_nil, coL]
  | cons nx rest' => simp [combF_cons, coL]

/-- The window as the fold seeds it: `j = 0, p = 0`. -/
theorem combF_window0 (m s : ℕ) (hb : m + 1 < 2 * (s + 1)) :
    combF (erow m 1 s) 0 0 (knuth m 0) = erow (m + 2) 0 (s + 2) := by
  have := combF_window m 0 s (by omega)
  simpa using this.symm ▸ (combF_p0 (erow m 1 s) (knuth m (2 * 0 - 2)) (knuth m (2 * 0))).symm

/-- Row invariant: after `k` double-steps the parity-0 row is the even entries of Knuth row
`2k+1`. -/
theorem rowInv (k : ℕ) : (iterD k (stepP1 [1], [])).1 = erow (2 * k + 1) 0 (k + 2) := by
  induction k with
  | zero =>
    have k10 : knuth 1 (2 * 0) = 1 := by rw [Nat.mul_zero, knuth_succ_zero]; simp [knuth_zero]
    have k12 : knuth 1 (2 * 1) = 1 := by
      rw [show 2 * 1 = 1 + 1 from rfl, knuth_succ]; simp [knuth_zero]
    rw [erow, erow, erow, k10, k12]; rfl
  | succ k ih =>
    have hiter : iterD (k + 1) (stepP1 [1], []) = dstep (iterD k (stepP1 [1], [])) := rfl
    rw [hiter]
    rw [show (dstep (iterD k (stepP1 [1], []))).1
          = combF (erow (2 * k + 1) 1 (k + 1)) 0 0 (knuth (2 * k + 1) 0) from by
        rw [dstep]; rw [ih, erow]]
    rw [combF_window0 (2 * k + 1) (k + 1) (by omega)]
    congr 1

/-- The reference output: `[T_N, T_{N-1}, …, T_1]`. -/
noncomputable def tanList : ℕ → List ℕ
  | 0 => []
  | k + 1 => tangentNumber (k + 1) :: tanList k

theorem tangentNumber_zero : tangentNumber 0 = 0 := by
  rw [tangentNumber_eq_knuth]; simp [knuth_zero]

/-- Accumulator invariant: after `k` double-steps the accumulator is `[T_k, …, T_1]`. -/
theorem accInv (k : ℕ) : (iterD k (stepP1 [1], [])).2 = tanList k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hiter : iterD (k + 1) (stepP1 [1], []) = dstep (iterD k (stepP1 [1], [])) := rfl
    rw [hiter]
    rw [show (dstep (iterD k (stepP1 [1], []))).2
          = knuth (2 * k + 1) 0 :: (iterD k (stepP1 [1], [])).2
          from by rw [dstep, rowInv k, erow]]
    rw [ih, tanList, show knuth (2 * k + 1) 0 = tangentNumber (k + 1) from by
      rw [tangentNumber_eq_knuth]; congr 1]

theorem tangentListN_eq (N : ℕ) : tangentListN N = tanList N := accInv N

theorem tanList_drop_head (N p : ℕ) : ((tanList N).drop p).headD 0 = tangentNumber (N - p) := by
  induction p generalizing N with
  | zero => cases N with
    | zero => simp [tanList, tangentNumber_zero]
    | succ k => simp [tanList]
  | succ p ih => cases N with
    | zero => simp [tanList, tangentNumber_zero]
    | succ k => rw [tanList, List.drop_succ_cons, ih]; congr 1; omega

/-- The fold computes the tangent numbers: `tangentNumber (N-p)` is the head of `drop p`. -/
theorem foldLink (N p : ℕ) : tangentNumber (N - p) = ((tangentListN N).drop p).headD 0 := by
  rw [tangentListN_eq]; exact (tanList_drop_head N p).symm

theorem tangentList_eq_of (N : Nat) (lits : List Nat) (h : (tangentListN N == lits) = true) :
    tangentListN N = lits := eq_of_beq h

theorem tnfold_d0 (N : Nat) (lits : List Nat) (h : tangentListN N = lits) :
    (tangentListN N).drop 0 = lits := by rw [List.drop_zero]; exact h

theorem tnfold_val (N p x : Nat) (t : List Nat) (h : (tangentListN N).drop p = x :: t) :
    tangentNumber (N - p) = x := by rw [foldLink N p, h]; rfl

theorem tnfold_next (N p x : Nat) (t : List Nat) (h : (tangentListN N).drop p = x :: t) :
    (tangentListN N).drop (p + 1) = t := by rw [← List.tail_drop, h]; rfl

/-! `fold_emit_tangent_numbers N` adds `tangentNumberLit_k : tangentNumber k = Tₖ` (k = 1,…,N):
one fold reduction proves the whole list, then an `O(N)` peel-chain reads each entry off it. -/
open Lean Lean.Meta Lean.Elab Lean.Elab.Command in
elab "fold_emit_tangent_numbers " nStx:num : command => liftTermElabM do
  let N := nStx.getNat
  -- compute T_1..T_N natively, matching the Lean fold
  let mut cur : Array Nat := #[0, 1]
  let mut Ts : Array Nat := #[]
  for i in [0 : 2 * N] do
    if i % 2 == 1 then Ts := Ts.push cur[0]!
    let L := cur.size
    let mut nw : Array Nat := Array.mkEmpty (L + 1)
    for k in [0 : L + 1] do
      let a := if 1 ≤ k then (k - 1) * cur[k - 1]! else 0
      let b := if k + 1 < L then (k + 1) * cur[k + 1]! else 0
      nw := nw.push (a + b)
    cur := nw
  let natTy := Expr.const ``Nat []
  let listNat := mkApp (.const ``List [Level.zero]) natTy
  -- suffixes indexed by p: suf p = [R[p], …, R[N-1]] = [T_{N-p}, …, T_1], R[p] = Ts[N-1-p]
  let mut built : Array Expr := Array.mkEmpty (N + 1)
  built := built.push (mkApp (.const ``List.nil [Level.zero]) natTy)   -- p = N
  for pp in [0 : N] do
    let p := N - 1 - pp
    built :=
        built.push (mkApp3 (.const ``List.cons [Level.zero]) natTy (mkRawNatLit Ts[N - 1 - p]!)
          built.back!)
  let suf := fun (p : Nat) => built[N - p]!
  let tListN := mkApp (.const ``tangentListN []) (mkRawNatLit N)
  let dropTy := fun (p : Nat) => mkApp3 (.const ``Eq [Level.one]) listNat
    (mkAppN (.const ``List.drop [Level.zero]) #[natTy, mkRawNatLit p, tListN]) (suf p)
  -- one fold reduction: tangentListN N = suffixes 0
  let listEqTy := mkApp3 (.const ``Eq [Level.one]) listNat tListN (suf 0)
  let listEqPf := mkAppN (.const ``tangentList_eq_of []) #[mkRawNatLit N, suf 0, reflBoolTrue]
  addDecl (.thmDecl
    { name := `tangentListEq, levelParams := [], type := listEqTy, value := listEqPf })
  let d0Pf := mkAppN (.const ``tnfold_d0 []) #[mkRawNatLit N, suf 0, .const `tangentListEq []]
  addDecl (.thmDecl { name := `dropEq_0, levelParams := [], type := dropTy 0, value := d0Pf })
  -- peel: p = 0 .. N-1
  for p in [0 : N] do
    let k := N - p
    let x := mkRawNatLit Ts[N - 1 - p]!
    let t := suf (p + 1)
    let dp : Expr := .const (Name.mkSimple s!"dropEq_{p}") []
    let litNm := `TangentNumbers ++ Name.mkSimple s!"tangentNumberLit_{k}"
    let litTy :=
        mkApp3 (.const ``Eq [Level.one]) natTy (mkApp (.const ``tangentNumber []) (mkRawNatLit k)) x
    let litPf := mkAppN (.const ``tnfold_val []) #[mkRawNatLit N, mkRawNatLit p, x, t, dp]
    addDecl (.thmDecl { name := litNm, levelParams := [], type := litTy, value := litPf })
    if p + 1 < N then
      let nextPf := mkAppN (.const ``tnfold_next []) #[mkRawNatLit N, mkRawNatLit p, x, t, dp]
      addDecl (.thmDecl
        { name := Name.mkSimple s!"dropEq_{p + 1}", levelParams := [], type := dropTy (p + 1),
          value := nextPf })

end TangentNumbers
