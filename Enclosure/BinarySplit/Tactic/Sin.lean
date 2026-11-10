module

public import Enclosure.BinarySplit.Functions.Sin
public import Enclosure.BinarySplit.Functions.SinPoly
public meta import Enclosure.BinarySplit.Functions.SinPoly
public import Enclosure.BinarySplit.Reduce.Sin
public import Enclosure.BinarySplit.Tactic.Engine
public import Enclosure.BinarySplit.Tactic.Recognizer
public meta import Enclosure.BinarySplit.Tactic.Engine
public meta import Enclosure.BinarySplit.Functions.Sin

/-!
# `sin` certificate builders

The metaprogram side of `Functions.Sin`: term-count search and the even/odd certificate builders.
-/
@[expose] public section


namespace BSN
open Enclosure

/-- Least `M` satisfying the sin tail guard at index `4M+1`. -/
private meta def sinTermCount (u v D : ℕ) : ℕ := trigTermCountAux u v 0 1 (u * (2 * D)) v

open Lean Elab Term Meta in
/-- The sin enclosure through `sin_poly_bound`, or `none` when its conditions fail (the analogue
of `mkCosPosPoly`). -/
meta def mkSinPosPoly (u v D : ℕ) : MetaM (Option (Expr × Bool × ℕ × ℕ)) := do
  let Q := dyadicDenom D
  unless u < 22 * v do return none
  unless 2 * u ^ 2 ≤ 484 * v ^ 2 do return none
  unless 2 * u ^ 21 * (2 * D) ≤ v ^ 21 * 51090942171709440000 do return none
  unless 2 * D ≤ Q do return none
  unless 1 ≤ v && 1 ≤ D do return none
  let P : ℕ := 121645100408832000 * (u * v ^ 18) + 1013709170073600 * (u ^ 5 * v ^ 14)
    + 335221286400 * (u ^ 9 * v ^ 10) + 19535040 * (u ^ 13 * v ^ 6) + 342 * (u ^ 17 * v ^ 2)
  let N : ℕ := 20274183401472000 * (u ^ 3 * v ^ 16) + 24135932620800 * (u ^ 7 * v ^ 12)
    + 3047466240 * (u ^ 11 * v ^ 8) + 93024 * (u ^ 15 * v ^ 4) + u ^ 19
  let Den : ℕ := v ^ 19 * 121645100408832000
  if P < N then return none
  let cn := (P - N) * Q / Den
  unless cn * Den + N * Q ≤ P * Q do return none
  unless P * Q < (cn + 1) * Den + N * Q do return none
  let lit := natLitShared
  return some (mkAppN (mkConst ``sin_poly_bound_packed)
    #[lit u, lit v, lit Q, lit D, lit cn, reflBoolTrue], false, cn, Q)

open Lean Elab Term Meta in
/-- `(proof, neg, cn, Q)` with `proof : Real.IsNear (sin (↑u/↑v)) neg cn Q 1 D`, from
`mkSinPosPoly` when it applies, else from `mkEvenOddCertCore`. -/
meta def mkSinPos (u v D : ℕ) : MetaM (Expr × Bool × ℕ × ℕ) := do
  if let some r ← mkSinPosPoly u v D then return r
  -- `max 1` keeps `M ≥ 1` (needed for `sin_dyadic_bound`'s `hM`); only affects `u = 0`, where
  -- `sinTermCount` returns `0`. Every convergence/tail guard is monotone in `M`, so `M = 1` is
  -- safe.
  let M := max 1 (sinTermCount u v D)
  mkEvenOddCertCore ``sinEvenP ``sinEvenQ ``sinOddP ``sinOddQ
    (sinEvenP u) (sinEvenQ v) (sinOddP u) (sinOddQ v) u v M D
    (fun (Te, Qe, To, Qo) => (u * (Qe + Te), v * Qe, u ^ 3 * (Qo + To), 6 * v ^ 3 * Qo))
    ``sin_dyadic_bound_f ``sin_dyadic_bound_t 8

end BSN
