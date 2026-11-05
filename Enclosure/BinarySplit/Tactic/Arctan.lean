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

/-- Least `M ≥ 1` with `u^(4M+1)·2D ≤ v^(4M+1)·(4M+1)`; powers threaded incrementally
(like `expTermCount`), not recomputed per step. -/
private meta def arctanTermCount (u v D : ℕ) : ℕ :=
    arctanTermCountAux u v 1 (u ^ 5 * (2 * D)) (v ^ 5)

open Lean Elab Term Meta in
/-- Core for `arctan (u/v)` (`u<v`) at `1/D` via binary splitting. -/
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
/-- Build the arctan inner enclosure `Real.IsNear (arctan (↑u/↑v)) neg cn Q 1 D` (`u<v`); return
`(proof, neg, cn, Q)`. Shared by the Machin π combiner. A thin wrapper over
the shared `mkEvenOddCertCore` (even value `u(Qe+Te)/(v·Qe)`, odd `u³(Qo+To)/(3v³·Qo)`,
7 leading side conditions of the sign-specialized `arctan_dyadic_bound_f`/`_t`). -/
meta def mkArctanPos (u v D : ℕ) : MetaM (Expr × Bool × ℕ × ℕ) :=
  mkEvenOddCertCore ``arctanEvenP ``arctanEvenQ ``arctanOddP ``arctanOddQ
    (arctanEvenP u) (arctanEvenQ v) (arctanOddP u) (arctanOddQ v) u v (arctanTermCount u v D) D
    (fun (Te, Qe, To, Qo) => (u * (Qe + Te), v * Qe, u ^ 3 * (Qo + To), 3 * v ^ 3 * Qo))
    ``arctan_dyadic_bound_f ``arctan_dyadic_bound_t 7

end BSN
