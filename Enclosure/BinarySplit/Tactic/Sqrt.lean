module

public import Enclosure.BinarySplit.Functions.Sqrt
public import Enclosure.BinarySplit.Tactic.Engine

/-!
# `√` enclosure metaprogram

The metaprogram side of `Functions.Sqrt`: `mkSqrtEncl` computes the dyadic enclosure
`[a/Q, b/Q]` of `√(N/M)` (`a = ⌊Q·√(N/M)⌋` via `Nat.sqrt`, `Q = 2ᵏ`) and assigns
`sqrt_enclosure`, with the squaring side conditions discharged by reflection.
-/
@[expose] public section


namespace BSN

/-! ### Metaprogram: compute the dyadic enclosure and emit the certificate -/

open Lean Elab Term Meta in
/-- Build the `IsNear` enclosure of `√(N/M)` (centre `(a+b)/(2Q)`, radius `(b−a)/(2Q)`, width
`≤ 1/(2D)`). The elaborator picks `Q = dyadicDenom D = 2ᵏ`, `a = ⌊√(N·Q²/M)⌋` (via `Nat.sqrt`),
`b = a+1`; the squaring side conditions are `reflBoolTrue`. Returns `(proof, a, b, Q)` for the
complex interval-arithmetic layer. -/
meta def mkSqrtEncl (N M D : ℕ) : MetaM (Expr × ℕ × ℕ × ℕ) := do
  let Q := dyadicDenom D
  let a := Nat.sqrt (N * Q ^ 2 / M)
  let b := a + 1
  let app := mkAppN (mkConst ``sqrt_enclosure)
    #[natLitShared N, natLitShared M, natLitShared a, natLitShared b, natLitShared Q,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  return (app, a, b, Q)

end BSN
