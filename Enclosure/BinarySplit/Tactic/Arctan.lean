/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Functions.Arctan
public import Enclosure.BinarySplit.Tactic.Engine
public import Enclosure.BinarySplit.Tactic.Recognizer
public meta import Enclosure.BinarySplit.Functions.Arctan
public meta import Enclosure.BinarySplit.Tactic.Engine

/-!
# `arctan` certificate builders

The metaprogram side of `Functions.Arctan`: term-count search and the even/odd certificate
builders (`mkArctanPos`).
-/
@[expose] public section


namespace BSN
open Enclosure

private meta partial def arctanTermCountAux (u v M L vk : ℕ) : ℕ :=
  if L.ble (vk * (4 * M + 1)) then M
  else arctanTermCountAux u v (M + 1) (L * u ^ 4) (vk * v ^ 4)

/-- Least `M ≥ 1` with `u^(4M+1)·2D ≤ v^(4M+1)·(4M+1)`. -/
private meta def arctanTermCount (u v D : ℕ) : ℕ :=
    arctanTermCountAux u v 1 (u ^ 5 * (2 * D)) (v ^ 5)

open Lean Elab Term Meta in
/-- `(m, Q, M, even, odd)` for `arctan (u/v)` (`u < v`) at precision `1/D`: the signed
floor-rounded numerator `m` over `Q = dyadicDenom D`, the term count, and the two binary-split
values. -/
meta def arctanCore (u v D : ℕ) : MetaM (Int × ℕ × ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) := do
  let Q := dyadicDenom D
  let M := arctanTermCount u v D
  let evenP : ℕ → ℕ := fun k => u ^ 4 * (4 * k + 1)
  let evenQ : ℕ → ℕ := fun k => v ^ 4 * (4 * k + 5)
  let oddP : ℕ → ℕ := fun k => u ^ 4 * (4 * k + 3)
  let oddQ : ℕ → ℕ := fun k => v ^ 4 * (4 * k + 7)
  let (Te, Qe, Pe) := evalFoldGen evenP evenQ 0 (M - 1)
  let (To, Qo, Po) := evalFoldGen oddP oddQ 0 (M - 1)
  let Ne : ℕ := u * (Qe + Te); let De : ℕ := v * Qe
  let No : ℕ := u ^ 3 * (Qo + To); let Do : ℕ := 3 * v ^ 3 * Qo
  let s : Int := (Ne : Int) * Do - (No : Int) * De
  let m : Int := Int.fdiv (s * (Q : Int)) ((De : Int) * Do)
  return (m, Q, M, (Te, Qe, Pe), (To, Qo, Po))

open Lean Elab Term Meta in
/-- `(proof, neg, cn, Q)` with `proof : Real.IsNear (arctan (↑u/↑v)) neg cn Q 1 D`, for
`u < v`. -/
meta def mkArctanPos (u v D : ℕ) : MetaM (Expr × Bool × ℕ × ℕ) :=
  mkEvenOddCertCore ``arctanEvenP ``arctanEvenQ ``arctanOddP ``arctanOddQ
    (arctanEvenP u) (arctanEvenQ v) (arctanOddP u) (arctanOddQ v) u v (arctanTermCount u v D) D
    (fun (Te, Qe, To, Qo) => (u * (Qe + Te), v * Qe, u ^ 3 * (Qo + To), 3 * v ^ 3 * Qo))
    ``arctan_dyadic_bound_f ``arctan_dyadic_bound_t 7

end BSN
