import Bernoulli.BernoulliValues

/-!
# Kummer's criterion and the regular primes below 200

A prime `p` is regular iff it does not divide the numerator of any Bernoulli number `B_k` for
the even indices `k = 2, 4, …, p-3` (Kummer's criterion).  This file defines that criterion
(`KummerCriterion`) and `derive_regular_below 200` generates a `KummerCriterion p` proof for every
regular prime below 200 (the 38 of them).

The reduced numerators are prime-independent, emitted once as the `bernNumAbs_m` lemmas by
`Bernoulli.BernoulliValues`.  So a whole prime's regularity proof is, per Bernoulli number, one
divisibility check on the shared literal — no tangent table and no cross-multiplies re-checked per
prime.  It uses no `interval_cases` and no `native_decide`. -/

open scoped Nat

namespace TangentNumbers

theorem not_dvd_num_of_forall (P m n : ℕ) (habs : (bernoulli (2 * m + 2)).num.natAbs = n)
    (hn : ¬ P ∣ n) : ¬ (P : ℤ) ∣ (bernoulli (2 * m + 2)).num := by
  rw [← Int.natAbs_dvd_natAbs, habs]
  simpa using hn

/-! ## Kummer's criterion -/

/-- Kummer's criterion: a prime `p` satisfies it iff `p` divides no numerator of the Bernoulli
numbers `B_k` for even `k = 2, 4, …, p-3`. -/
def KummerCriterion (p : ℕ) : Prop :=
  ∀ k, 2 ≤ k → k ≤ p - 3 → Even k → ¬ (p : ℤ) ∣ (bernoulli k).num

/-! ## Ball skeleton: a `Nat`-recursion bounded-∀ certificate

A `Nat`-recursion chain that never builds an intermediate list, avoiding the per-index
`List.range.loop` reduction that dominates a `List.range N` + `Forall₂` sweep skeleton.  `KQ p m`
is the per-index predicate; the per-prime proof is
`kummerCriterion_of_ball p N hle (ball_k_succ … (ball_k_zero p))`, each index's fact built by name
from `bernNumAbs_m`. -/

/-- `¬ a ∣ b` from the boolean residue certificate `1 ≤ b % a`. -/
theorem not_dvd_of_mod (a b : ℕ) (h : Nat.ble 1 (b % a) = true) : ¬ a ∣ b := by
  rw [Nat.dvd_iff_mod_eq_zero]; simp only [Nat.ble_eq] at h; omega

/-- The per-index Kummer predicate. -/
def KQ (p m : ℕ) : Prop := ¬ (p : ℤ) ∣ (bernoulli (2 * m + 2)).num

theorem ball_k_zero (p : ℕ) : ∀ m, m < 0 → KQ p m := fun _ h => absurd h (Nat.not_lt_zero _)

theorem ball_k_succ (p N : ℕ) (hN : KQ p N) (h : ∀ m, m < N → KQ p m) :
    ∀ m, m < N + 1 → KQ p m := fun m hm => (Nat.lt_succ_iff_lt_or_eq.mp hm).elim (h m) (· ▸ hN)

theorem kummerCriterion_of_ball (p N : ℕ) (hle : p ≤ 2 * N + 3)
    (h : ∀ m, m < N → KQ p m) : KummerCriterion p := by
  intro k hk2 hkle hev
  obtain ⟨t, rfl⟩ := hev
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hh : KQ p m := h m (by omega)
  rw [KQ] at hh
  have hidx : (m + 1) + (m + 1) = 2 * m + 2 := by ring
  rwa [hidx]

/-- `KQ p m` from the numerator literal and its non-divisibility (`not_dvd_num_of_forall`). -/
theorem kq_of (p m n : ℕ) (habs : (bernoulli (2 * m + 2)).num.natAbs = n) (hn : ¬ p ∣ n) : KQ p m :=
  not_dvd_num_of_forall p m n habs hn

/-! ## Regular primes below 200

`derive_regular_below N` proves `KummerCriterion p` (regularity) for every regular prime `p < N`, as
a lemma `regular_p`.  Regularity is decided by the computation itself: it reads the reduced
numerators of `B_2, …, B_{p-3}` off the `bernNumAbs_m` lemmas (emitted by
`Bernoulli.BernoulliValues`) and emits a proof only when `p` divides none of them.  Irregular primes
(below 200: `37, 59, 67, 101, 103, 131, 149, 157`) are silently skipped.  Each proof is
`kummerCriterion_of_ball` over the ball chain, built as a raw `Expr` and `addDecl`ed — no
`elabCommand`, no `Syntax`, no `decide`; every side condition is a `reflBoolTrue`.
`native_decide`-free. -/
open Lean Lean.Meta Lean.Elab Lean.Elab.Command in
/-- Add `regular_p : KummerCriterion p` for every regular prime `p < N`. -/
elab "derive_regular_below " nStx:num : command => liftTermElabM do
  let bound := nStx.getNat
  let isPrime : Nat → Bool := fun n => Id.run do
    if n < 2 then return false
    let mut d := 2
    while d * d ≤ n do
      if n % d == 0 then return false
      d := d + 1
    return true
  let maxM := (bound - 3) / 2
  let mut nums : Array Nat := #[]
  for m in [0:maxM] do
    let some (_, _, nE) :=
        (← inferType (.const (`TangentNumbers ++ Name.mkSimple s!"bernNumAbs_{m}") [])).eq?
      | throwError "derive_regular_below: bernNumAbs_{m} is not an equality"
    let some nv := nE.rawNatLit?
      | throwError "derive_regular_below: |numerator| of B_{2 * m + 2} is not a literal"
    nums := nums.push nv
  let mut regulars : Array (Nat × Nat) := #[]
  for p in [2:bound] do
    if !isPrime p then continue
    let N := if 3 ≤ p then (p - 3) / 2 else 0
    let mut reg := true
    for m in [0:N] do
      if nums[m]! % p == 0 then reg := false
    if reg then regulars := regulars.push (p, N)
  for (p, N) in regulars do
    let PE := mkRawNatLit p
    let mut acc := mkAppN (.const ``TangentNumbers.ball_k_zero []) #[PE]
    for m in [0:N] do
      let lit := mkRawNatLit nums[m]!
      let bernAbs := Expr.const (`TangentNumbers ++ Name.mkSimple s!"bernNumAbs_{m}") []
      let elemNat := mkAppN (.const ``TangentNumbers.not_dvd_of_mod []) #[PE, lit, reflBoolTrue]
      let factM :=
          mkAppN (.const ``TangentNumbers.kq_of []) #[PE, mkRawNatLit m, lit, bernAbs, elemNat]
      acc := mkAppN (.const ``TangentNumbers.ball_k_succ []) #[PE, mkRawNatLit m, factM, acc]
    let hle :=
        mkAppN (.const ``Nat.le_of_ble_eq_true []) #[PE, mkRawNatLit (2 * N + 3), reflBoolTrue]
    let pf :=
        mkAppN (.const ``TangentNumbers.kummerCriterion_of_ball []) #[PE, mkRawNatLit N, hle, acc]
    let ty := mkApp (.const ``TangentNumbers.KummerCriterion []) PE
    let nm := `TangentNumbers ++ Name.mkSimple s!"regular_{p}"
    addDecl (.thmDecl { name := nm, levelParams := [], type := ty, value := pf })

/-! ## All regular primes below 200

The sweep reads `|num(B_{2m+2})| = n` by name off the environment lemma `bernNumAbs_m`
emitted by `Bernoulli.BernoulliValues`, so a per-prime read is an `O(1)` constant reference. -/

derive_regular_below 200

/-- Sanity check: the generated lemmas are present, well-typed, and axiom-clean. -/
example : KummerCriterion 2 := regular_2
example : KummerCriterion 5 := regular_5
example : KummerCriterion 163 := regular_163
example : KummerCriterion 199 := regular_199

#print axioms regular_163

end TangentNumbers
