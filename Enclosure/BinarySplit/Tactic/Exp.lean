/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Functions.Exp
public import Enclosure.BinarySplit.Tactic.Engine
public import Enclosure.BinarySplit.Tactic.Recognizer
public meta import Enclosure.BinarySplit.Tactic.Engine
public meta import Enclosure.BinarySplit.Functions.Exp

/-!
# `exp` certificate builders

The metaprogram side of `Functions.Exp`: term-count search, the pure split evaluator, and the
certificate builders for `Real.exp` enclosures (`mkExpPos`, `mkExpCert`).
-/
@[expose] public section


namespace BSN
open Enclosure

/-- The least term count `N` (from the seed) for `exp (u/v)` at precision `1/D`, with
`L = u^N · 2D` and `R = v^N · N!` carried as running products, so each step is one big×small
multiply. -/
private meta partial def expTermCountAux (u v N L R : ℕ) : ℕ :=
  if L * ((N + 1) * v) ≤ R * ((N + 1) * v - u) then N
  else expTermCountAux u v (N + 1) (L * u) (R * (v * (N + 1)))

private meta def expTermCount (u v D : ℕ) : ℕ := expTermCountAux u v 0 (2 * D) 1

open Lean Elab Term Meta in
/-- `(p, Q, N, (T, Qd, P))` for `exp (u/v)` at precision `1/D`: the binary-split values over
`[0, N-1)` and the dyadic numerator `p = ⌊(Qd+T)·Q/Qd⌋` over `Q = dyadicDenom D`. -/
meta def expCore (u v D : ℕ) : MetaM (ℕ × ℕ × ℕ × (ℕ × ℕ × ℕ)) := do
  let Q := dyadicDenom D
  let N := expTermCount u v D
  let (T, Qd, P) := evalFoldGen (fun _ => u) (fun m => v * (m + 1)) 0 (N - 1)
  return ((Qd + T) * Q / Qd, Q, N, (T, Qd, P))

open Lean Elab Term Meta in
/-- `(proof, p, Q)` with `proof : Real.IsNear (exp (↑u/↑v)) false p Q 1 D`. -/
meta def mkExpPos (u v D : ℕ) : MetaM (Expr × ℕ × ℕ) := do
  let Q := dyadicDenom D
  let N := expTermCount u v D
  let pE := mkApp (mkConst ``expNatP) (natLitShared u)
  let qE := mkApp (mkConst ``expNatQ) (natLitShared v)
  let ((T, Qd, P), hsplit) ← proveBS (fun i => pure (expNatP u i)) (fun i => pure (expNatQ v i))
    pE qE (natLitShared 0) (natLitShared (N - 1)) 0 (N - 1)
  let p := (Qd + T) * Q / Qd
  let app := mkAppN (mkConst ``exp_dyadic_bound)
    #[natLitShared u, natLitShared v, natLitShared N, natLitShared (N - 1), natLitShared Qd,
      natLitShared D,
      natLitShared T, natLitShared P,
      natLitShared Q, natLitShared p, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue, hsplit, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  return (app, p, Q)

open Lean Elab Term Meta in
/-- `(proof, neg, cn, cd, rn, rd)` with `proof` an `IsNear` enclosure of radius `1/D` of
`Real.exp x`, for `x` a nonnegative integer `u` (`kind = 0`), a positive fraction `↑u/↑v`
(`kind = 1`), or a negative fraction `(-↑u)/↑v` (`kind = 2`). -/
meta def mkExpCert (u v D kind : ℕ) : MetaM (Expr × Bool × ℕ × ℕ × ℕ × ℕ) := do
  if kind == 2 then
    -- negative fraction: `exp(-u/v) = 1/exp(u/v)` via `exp_neg_bound`. The inner positive
    -- enclosure (`mkExpPos`) is computed at the doubled precision `1/D0`; the reciprocal is
    -- re-rounded to the dyadic `p'/Q'`. Result fields `(false, p', Q', 1, D)`.
    let D0 := 2 * D
    let Q' := dyadicDenom D
    let (pos, p, Q) ← mkExpPos u v D0
    let p' := Q' * Q / p
    let cert := mkAppN (mkConst ``exp_neg_bound)
      #[natLitShared u, natLitShared v, natLitShared Q, natLitShared D0, natLitShared Q',
        natLitShared D, natLitShared p,
        natLitShared p', reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, pos]
    return (cert, false, p', Q', 1, D)
  if kind == 0 then
    -- integer path: `mkExpPos` with `v = 1`, recast `↑u/↑1 → ↑u` by `exp_int_of_rat`. Fields
    -- `(false, p, Q, 1, D)`.
    let (pos, p, Q) ← mkExpPos u 1 D
    let cert := mkAppN (mkConst ``exp_int_of_rat)
      #[natLitShared u, toExpr false, natLitShared p, natLitShared Q, natLitShared 1,
        natLitShared D, pos]
    return (cert, false, p, Q, 1, D)
  else
    -- fraction path: `mkExpPos` (enclosed real `Real.exp (↑u/↑v)`), fields `(false, p, Q, 1, D)`.
    let (pos, p, Q) ← mkExpPos u v D
    return (pos, false, p, Q, 1, D)

end BSN
