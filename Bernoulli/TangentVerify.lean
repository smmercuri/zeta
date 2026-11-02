module

public import Bernoulli.TangentNumbers

/-!
# Certifying the tangent numbers into the environment

`emit_tangent_numbers N` adds `tangentNumberLit_k : tangentNumber k = Tₖ` for `k = 1, …, N` by
replaying the Knuth-Buckholtz A-table at the level of certificates.  The table lemmas it needs are
collected in the `TangentNumbers.Meta` namespace here; see `Bernoulli.TangentNumbers` for the
underlying definitions and theory.
-/
@[expose] public section


open scoped Nat

namespace TangentNumbers

noncomputable section
open Polynomial

/-! ## The Knuth-Buckholtz table

The coefficients `T_{n,k}` of the tangent polynomials, `knuth n k = (tangentPoly n).coeff k`, and
their recurrence.  These are used only to drive the verification tactic below. -/

/-- The Knuth-Buckholtz numbers `T_{n,k}`: the coefficient of `tanᵏ` in the `n`-th derivative,
`dⁿ/dxⁿ tan x = Σₖ T_{n,k} · tanᵏ x`. -/
def knuth (n k : ℕ) : ℕ := (tangentPoly n).coeff k

@[simp, grind =] theorem knuth_zero (k : ℕ) : knuth 0 k = if k = 1 then 1 else 0 := by
  grind [knuth, tangentPoly, coeff_X]

/-- The first column: `T_{n+1,0} = T_{n,1}` (the `k = 0` case of Knuth's recurrence (7),
where the `T_{n,-1}` term vanishes). -/
theorem knuth_succ_zero (n : ℕ) : knuth (n + 1) 0 = knuth n 1 := by
  rw [knuth, knuth, tangentPoly_succ, add_mul, one_mul, coeff_add, coeff_derivative]
  simp

/-- Knuth's recurrence (7), in the underflow-free form
`T_{n+1,k+1} = k·T_{n,k} + (k+2)·T_{n,k+2}`
(set `k ↦ k+1` in `T_{n+1,k} = (k-1)·T_{n,k-1} + (k+1)·T_{n,k+1}`). -/
theorem knuth_succ (n k : ℕ) :
    knuth (n + 1) (k + 1) = k * knuth n k + (k + 2) * knuth n (k + 2) := by
  simp only [knuth, tangentPoly_succ, add_mul, one_mul, coeff_add]
  grind [coeff_X_pow_mul', coeff_derivative]

/-- Above the main diagonal the table vanishes: `T_{n,k} = 0` for `k > n+1`
(`Pₙ` has degree `n+1`). -/
theorem knuth_eq_zero (n k : ℕ) (hk : n + 1 < k) : knuth n k = 0 := by
  induction n generalizing k with
  | zero => grind
  | succ => grind [knuth_succ, cases Nat]

/-- The top diagonal of Knuth's table holds the factorials, `T_{n,n+1} = n!`.  The table builder
seeds its first row with these (`T_{j-1,j} = (j-1)!`). -/
theorem knuth_self (n : ℕ) : knuth n (n + 1) = n ! := by
  induction n with
  | zero => grind [Nat.factorial_zero]
  | succ => grind [knuth_succ, Nat.factorial_succ, knuth_eq_zero]

/-- The tangent number `Tₙ` is the bottom entry `T_{2n-1,0}` of the table: both are the constant
term `P_{2n-1}(0)` of the tangent polynomial. -/
theorem tangentNumber_eq_knuth (n : ℕ) : tangentNumber n = knuth (2 * n - 1) 0 := by
  rw [tangentNumber, knuth, coeff_zero_eq_eval_zero]

end

/-! ## Certificate lemmas for `emit_tangent_numbers`

The combine steps (`knuth_step` … `tangentNumber_eq_of`) pin each table entry's indices and value to
literals, so the certificate chain the tactic builds stays a clean numeral.  They carry no
mathematical content of their own. -/

namespace Meta

open Polynomial

theorem knuth_zero_one : knuth (nat_lit 0) (nat_lit 1) = (nat_lit 1) := by simp

/-- The single combine step: one application of Knuth's recurrence with the two source entries
pinned to literals `a, b` and the combined value pre-reduced to a literal `c`, so the certificate
chain the emitter builds stays a clean numeral. -/
theorem knuth_step (N N' K K' K'' a b c : ℕ)
    (hN' : N.succ.beq N') (hK' : K.succ.beq K') (hK'' : K'.succ.beq K'')
    (h1 : knuth N K = a) (h2 : knuth N K'' = b) (hc : ((K.mul a).add (K''.mul b)).beq c) :
    knuth N' K' = c := by
  simp only [Nat.succ_eq_add_one, Nat.beq_eq, Nat.mul_eq, Nat.add_eq] at hN' hK' hK'' hc
  subst hN' hK' hK''
  grind [TangentNumbers.knuth_succ]

/-- The diagonal combine `T_{N+1,1} = 2·T_{N,2}`: `knuth_succ` with `K = 0`, where the `K·T_{N,0}`
term drops out.  The tactic uses this for the bottom entry of each column, so it needs no left
neighbour there (the `T_{N,0}` the general step would reference is multiplied by zero). -/
theorem knuth_step0 (N N' b c : ℕ) (hN' : N.succ.beq N')
    (h2 : knuth N (nat_lit 2) = b) (hc : (b.mul (nat_lit 2)).beq c) :
    knuth N' (nat_lit 1) = c := by
  simp only [Nat.succ_eq_add_one, Nat.beq_eq, Nat.mul_eq] at hN' hc
  subst hN'
  grind [TangentNumbers.knuth_succ]

/-- The diagonal one rung at a time: `T_{n+1,n+2} = (n+1)·T_{n,n+1}` (the off-diagonal term in
`knuth_succ` vanishes by `knuth_eq_zero`).  The verification tactic builds the factorial seed with
this, one multiplication per entry, instead of recomputing each `(j-1)!` from scratch. -/
theorem knuth_self_step (n n' n'' a c : ℕ) (hn' : n.succ.beq n') (hn'' : n'.succ.beq n'')
    (h : knuth n n' = a) (hc : (n'.mul a).beq c) :
    knuth n' n'' = c := by
  simp only [Nat.succ_eq_add_one, Nat.beq_eq, Nat.mul_eq] at hn' hn'' hc
  subst hn' hn''
  grind [TangentNumbers.knuth_succ, knuth_eq_zero]

/-- The tangent number read off the last working value of column `2k-1`.  From the diagonal entry
`knuth (2k-2) 1 = a`, one step of Knuth's first-column recurrence (`knuth (n+1) 0 = knuth n 1`) and
`tangentNumber_eq_knuth` give `tangentNumber k = a`.  Folding the column freeze and the read-off
together lets the verification tactic close the whole column with a single lemma application (each
is used exactly once). -/
theorem tangentNumber_eq_of (k n a : ℕ) (hn : n.succ.beq ((k.mul (nat_lit 2)).sub (nat_lit 1)))
    (h : knuth n (nat_lit 1) = a) :
    tangentNumber k = a := by
  simp only [Nat.succ_eq_add_one, Nat.mul_eq, Nat.sub_eq, Nat.beq_eq] at hn
  rw [tangentNumber_eq_knuth]
  grind [TangentNumbers.knuth_succ_zero]

end Meta

/-! ## Emitting the certified tangent numbers

`emit_tangent_numbers N` adds one lemma `tangentNumberLit_k : tangentNumber k = Tₖ` per
`k = 1, …, N`. It sweeps the Knuth A-table once, laying every interior cell down as an internal
auxiliary lemma `knuth n k = v` (via `mkAuxLemma`) proved from its two parents by name (so the
kernel never re-checks a shared subproof), then reads each column's frozen cell off with
`tangentNumber_eq_of`.  Downstream (Bernoulli numerators, exact values, regularity) cites
`tangentNumberLit_k`.  No giant proof term and no `native_decide`; every side condition is a
`reflBoolTrue`. -/
section
open Lean Lean.Meta Lean.Elab Lean.Elab.Command

elab "emit_tangent_numbers " nStx:num : command => liftTermElabM do
  let N := nStx.getNat
  let mkCell := fun (n k v : Nat) (pf : Expr) => do
    let stmt := mkApp3 (.const ``Eq [Level.one]) (.const ``Nat [])
      (mkAppN (.const ``TangentNumbers.knuth []) #[mkRawNatLit n, mkRawNatLit k]) (mkRawNatLit v)
    mkAuxLemma [] stmt pf
  let mut prev : Array (Nat × Name) := Array.replicate (N + 1) (0, .anonymous)
  let mut freeze : Array (Nat × Name) := Array.replicate (N + 1) (0, .anonymous)
  let b0 ← mkCell 0 1 1 (.const ``TangentNumbers.Meta.knuth_zero_one [])
  prev := prev.set! 1 (1, b0); freeze := freeze.set! 1 (1, b0)
  -- diagonal seed `knuth (j-1) j = (j-1)!`, one rung at a time
  for j in [2:N+1] do
    let (aVal, aN) := prev[j - 1]!
    let c := (j - 1) * aVal
    let nm ← mkCell (j - 1) j c (mkAppN (.const ``TangentNumbers.Meta.knuth_self_step [])
      #[mkRawNatLit (j - 2), mkRawNatLit (j - 1), mkRawNatLit j, mkRawNatLit aVal, mkRawNatLit c,
        reflBoolTrue, reflBoolTrue, .const aN [], reflBoolTrue])
    prev := prev.set! j (c, nm)
  -- rows `k = 2, …, N`; the first entry of each row is the frozen `knuth (2k-2) 1 = Tₖ`
  for k in [2:N+1] do
    let mut cur : Array (Nat × Name) := Array.replicate (N + 1) (0, .anonymous)
    for j in [k:N+1] do
      if j == k then
        let M := 2 * k - 3
        let (bVal, bN) := prev[k]!
        let c := 2 * bVal
        let nm ← mkCell (M + 1) 1 c (mkAppN (.const ``TangentNumbers.Meta.knuth_step0 [])
          #[mkRawNatLit M, mkRawNatLit (M + 1), mkRawNatLit bVal, mkRawNatLit c,
            reflBoolTrue, .const bN [], reflBoolTrue])
        cur := cur.set! j (c, nm); freeze := freeze.set! k (c, nm)
      else
        let N₀ := j + k - 3
        let K₀ := j - k
        let (aVal, aN) := cur[j-1]!
        let (bVal, bN) := prev[j]!
        let c := K₀ * aVal + (K₀ + 2) * bVal
        let nm ← mkCell (N₀ + 1) (K₀ + 1) c (mkAppN (.const ``TangentNumbers.Meta.knuth_step [])
          #[mkRawNatLit N₀, mkRawNatLit (N₀ + 1), mkRawNatLit K₀, mkRawNatLit (K₀ + 1),
            mkRawNatLit (K₀ + 2), mkRawNatLit aVal, mkRawNatLit bVal, mkRawNatLit c,
            reflBoolTrue, reflBoolTrue, reflBoolTrue, .const aN [], .const bN [], reflBoolTrue])
        cur := cur.set! j (c, nm)
    prev := cur
  -- read each column's frozen cell off as `tangentNumber k = Tₖ`
  for k in [1:N+1] do
    let (Tval, cN) := freeze[k]!
    let stmt := mkApp3 (.const ``Eq [Level.one]) (.const ``Nat [])
      (mkApp (.const ``TangentNumbers.tangentNumber []) (mkRawNatLit k)) (mkRawNatLit Tval)
    let pf := mkAppN (.const ``TangentNumbers.Meta.tangentNumber_eq_of [])
      #[mkRawNatLit k, mkRawNatLit (2 * k - 2), mkRawNatLit Tval, reflBoolTrue, .const cN []]
    addDecl (.thmDecl
      { name := `TangentNumbers ++ Name.mkSimple s!"tangentNumberLit_{k}", levelParams := [],
        type := stmt, value := pf })

end

end TangentNumbers
