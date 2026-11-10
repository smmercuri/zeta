module

public import Enclosure.BinarySplit.Functions.Cos
public import Enclosure.BinarySplit.Functions.CosPoly
public import Enclosure.BinarySplit.Tactic.Engine
public import Enclosure.BinarySplit.Tactic.Recognizer
public meta import Enclosure.BinarySplit.Tactic.Engine
public meta import Enclosure.BinarySplit.Functions.Cos
public meta import Enclosure.BinarySplit.Functions.CosPoly

/-!
# `cos` certificate builders

The metaprogram side of `Functions.Cos`: term-count search and the even/odd certificate
builders (`mkCosPos`).
-/
@[expose] public section


namespace BSN
open Enclosure

/-- Least `M` satisfying the cos tail guard at index `4M`. -/
private meta def cosTermCount (u v D : ℕ) : ℕ := trigTermCountAux u v 0 0 (2 * D) 1

open Lean Elab Term Meta in
/-- The cos enclosure `(proof, false, cn, Q)` through `cos_poly_bound` (the ten-term Taylor
polynomial with literal coefficients, needing no `binarySplit` certificate), or `none` when that
lemma's conditions fail at this argument and precision. The sign is `false` because the reduced
argument lies in `[0, π/2)`. -/
meta def mkCosPosPoly (u v D : ℕ) : MetaM (Option (Expr × Bool × ℕ × ℕ)) := do
  let Q := dyadicDenom D
  -- the lemma's own conditions, checked here so a failure returns `none`
  unless u < 21 * v do return none
  unless 2 * u ^ 2 ≤ 441 * v ^ 2 do return none
  unless 2 * u ^ 20 * (2 * D) ≤ v ^ 20 * 2432902008176640000 do return none
  unless 2 * D ≤ Q do return none
  unless 1 ≤ v && 1 ≤ D do return none
  -- the same two sums the lemma's conditions name, in the same coefficient order
  let P : ℕ := 6402373705728000 * v ^ 18 + 266765571072000 * (u ^ 4 * v ^ 14)
    + 158789030400 * (u ^ 8 * v ^ 10) + 13366080 * (u ^ 12 * v ^ 6) + 306 * (u ^ 16 * v ^ 2)
  let N : ℕ := 3201186852864000 * (u ^ 2 * v ^ 16) + 8892185702400 * (u ^ 6 * v ^ 12)
    + 1764322560 * (u ^ 10 * v ^ 8) + 73440 * (u ^ 14 * v ^ 4) + u ^ 18
  let Den : ℕ := v ^ 18 * 6402373705728000
  if P < N then return none
  let cn := (P - N) * Q / Den
  -- `cn` is the floor, so `hr1`/`hr2` hold; both are checked again before the term is emitted
  unless cn * Den + N * Q ≤ P * Q do return none
  unless P * Q < (cn + 1) * Den + N * Q do return none
  let lit := natLitShared
  return some (mkAppN (mkConst ``cos_poly_bound_packed)
    #[lit u, lit v, lit Q, lit D, lit cn, reflBoolTrue], false, cn, Q)

open Lean Elab Term Meta in
/-- `(proof, neg, cn, Q)` with `proof : Real.IsNear (cos (↑u/↑v)) neg cn Q 1 D`, from
`mkCosPosPoly` when it applies, else from `mkEvenOddCertCore`. -/
meta def mkCosPos (u v D : ℕ) : MetaM (Expr × Bool × ℕ × ℕ) := do
  if let some r ← mkCosPosPoly u v D then return r
  let M := cosTermCount u v D
  mkEvenOddCertCore ``cosEvenP ``cosEvenQ ``cosOddP ``cosOddQ
    (cosEvenP u) (cosEvenQ v) (cosOddP u) (cosOddQ v) u v M D
    (fun (Te, Qe, To, Qo) => (Qe + Te, Qe, u ^ 2 * (Qo + To), 2 * v ^ 2 * Qo))
    ``cos_dyadic_bound_f ``cos_dyadic_bound_t 8

end BSN
