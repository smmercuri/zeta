/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-!
# Binary-splitting definitions that need no `Mathlib`

`binarySplit` and the series coefficients the `*_dyadic_bound` lemmas are stated with. This file
imports no `Mathlib`, so compiled checkers (the `NativeCode` library) use exactly the same functions
the lemmas mention. Their specs live with the lemmas (`Enclosure.BinarySplit.Basic`,
`Enclosure.BinarySplit.Functions.*`).
-/
@[expose] public section

namespace BSN

/-- Minimal binary split. `(T, Q, P)` with `∑_{m≤i<n} ∏_{m≤j≤i}(p j/q j) = T/Q` and
`∏_{m≤j<n}(p j/q j) = P/Q`. -/
def binarySplit (p q : Nat → Nat) (m n : Nat) : Nat × Nat × Nat :=
  if _h : m < n then
    if _h2 : m + 1 = n then (p m, q m, p m)
    else
      let (tl, ql, pl) := binarySplit p q m ((m + n) / 2)
      let (tr, qr, pr) := binarySplit p q ((m + n) / 2) n
      (tl * qr + pl * tr, ql * qr, pl * pr)
  else (0, 1, 1)
termination_by n - m
decreasing_by all_goals omega

/-! ### Series coefficients -/

/-- Even-indexed cos sub-series `∑_j (u/v)^{4j}/(4j)!`: leading factor `1`,
ratio `u^4 / (v^4·(4k+1)(4k+2)(4k+3)(4k+4))`. -/
def cosEvenP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def cosEvenQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.succ (Nat.mul 4 k)) (Nat.add (Nat.mul 4 k) 2))
      (Nat.add (Nat.mul 4 k) 3)) (Nat.add (Nat.mul 4 k) 4))

/-- Odd-indexed cos sub-series `∑_j (u/v)^{4j+2}/(4j+2)!`: leading factor
`u^2/(2 v^2)`, ratio `u^4 / (v^4·(4k+3)(4k+4)(4k+5)(4k+6))`. -/
def cosOddP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def cosOddQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 3) (Nat.add (Nat.mul 4 k) 4))
      (Nat.add (Nat.mul 4 k) 5)) (Nat.add (Nat.mul 4 k) 6))

/-- Even-indexed sin sub-series `∑_j (u/v)^{4j+1}/(4j+1)!`: leading factor `u/v`,
ratio `u^4 / (v^4·(4k+2)(4k+3)(4k+4)(4k+5))`. -/
def sinEvenP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def sinEvenQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 2) (Nat.add (Nat.mul 4 k) 3))
      (Nat.add (Nat.mul 4 k) 4)) (Nat.add (Nat.mul 4 k) 5))

/-- Odd-indexed sin sub-series `∑_j (u/v)^{4j+3}/(4j+3)!`: leading factor
`u^3/(6 v^3)`, ratio `u^4 / (v^4·(4k+4)(4k+5)(4k+6)(4k+7))`. -/
def sinOddP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def sinOddQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 4) (Nat.add (Nat.mul 4 k) 5))
      (Nat.add (Nat.mul 4 k) 6)) (Nat.add (Nat.mul 4 k) 7))

/-- `artanh(u/v)`: leading factor `u/v`, ratio `u^2(2k+1) / (v^2(2k+3))`. -/
def artanhP (u : Nat) : Nat
    → Nat := fun k => Nat.mul (Nat.pow u (nat_lit 2)) (Nat.succ (Nat.mul (nat_lit 2) k))
def artanhQ (v : Nat) : Nat
    → Nat := fun k => Nat.mul (Nat.pow v (nat_lit 2)) (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 3))

/-- Even-indexed arctan sub-series `∑_j (u/v)^{4j+1}/(4j+1)`: leading factor `u/v`,
ratio `u^4·(4k+1) / (v^4·(4k+5))`. -/
def arctanEvenP (u : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow u 4) (Nat.succ (Nat.mul 4 k))
def arctanEvenQ (v : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow v 4) (Nat.add (Nat.mul 4 k) 5)

/-- Odd-indexed arctan sub-series `∑_j (u/v)^{4j+3}/(4j+3)`: leading factor `u^3/(3 v^3)`,
ratio `u^4·(4k+3) / (v^4·(4k+7))`. -/
def arctanOddP (u : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow u 4) (Nat.add (Nat.mul 4 k) 3)
def arctanOddQ (v : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow v 4) (Nat.add (Nat.mul 4 k) 7)

end BSN
