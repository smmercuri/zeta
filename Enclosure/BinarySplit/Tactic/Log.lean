/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Functions.Log
public import Enclosure.BinarySplit.Reduce.Log
public import Enclosure.BinarySplit.Tactic.Engine
public import Enclosure.BinarySplit.Tactic.Recognizer
public meta import Enclosure.BinarySplit.Functions.Log
public meta import Enclosure.BinarySplit.Tactic.Engine

/-!
# `log` certificate builders

The metaprogram side of `Functions.Log`: term-count search, the pure split evaluator, and the
certificate builders (`mkLogPos`, `mkLogFracPos`).
-/
@[expose] public section


namespace BSN
open Enclosure

/-- The least `N` (from the seed) with `4·L ≤ vk`, carrying `L` and `vk` as running powers:
recomputing `u^(2N+1)` per step would make the search quadratic in `N`. -/
private meta partial def logTermCountAux (u v N L vk : ℕ) : ℕ :=
  if 4 * L ≤ vk then N
  else logTermCountAux u v (N + 1) (L * u ^ 2) (vk * v ^ 2)

/-- Least `N` with `4·u^(2N+1)·2D ≤ v^(2N+1)`: the artanh term count for `log((v+u)/(v−u))` at
precision `1/D`. -/
private meta def logTermCount (u v D : ℕ) : ℕ := logTermCountAux u v 0 (u * (2 * D)) v

open Lean Elab Term Meta in
/-- `(p, Q, N, (T, Qd, P))` for `log((v+u)/(v−u))` at precision `1/D`: the binary-split values
over `[0, N-1)` and the dyadic numerator `p = ⌊2u(Qd+T)·Q/(v·Qd)⌋` over `Q = dyadicDenom D`. -/
meta def logCore (u v D : ℕ) : MetaM (ℕ × ℕ × ℕ × (ℕ × ℕ × ℕ)) := do
  let Q := dyadicDenom D
  let N := logTermCount u v D
  let (T, Qd, P) :=
    evalFoldGen (fun m => u ^ 2 * (2 * m + 1)) (fun m => v ^ 2 * (2 * m + 3)) 0 (N - 1)
  return (2 * (u * (Qd + T)) * Q / (v * Qd), Q, N, (T, Qd, P))

open Lean Elab Term Meta in
/-- `(proof, p, Q)` with `proof : Real.IsNear (log (↑S/↑Dd)) false p Q 1 D` for the literals
`S = v+u`, `Dd = v−u`. -/
meta def mkLogPos (u v D : ℕ) : MetaM (Expr × ℕ × ℕ) := do
  let Q := dyadicDenom D
  -- `max 1` keeps `N ≥ 1` (needed for `log_dyadic_bound`'s `hN`); only affects the `u = 0` case
  -- (reduced argument an exact power of 2, `log 1 = 0`), where `logTermCount` returns `0`. Every
  -- convergence/tail guard is monotone in `N`, so `N = 1` is safe (value stays `0`).
  let N := max 1 (logTermCount u v D)
  let pE := mkApp (mkConst ``artanhP) (natLitShared u)
  let qE := mkApp (mkConst ``artanhQ) (natLitShared v)
  let ((T, Qd, P), hsplit) ← proveBS (fun i => pure (artanhP u i)) (fun i => pure (artanhQ v i))
    pE qE (natLitShared 0) (natLitShared (N - 1)) 0 (N - 1)
  let p := 2 * (u * (Qd + T)) * Q / (v * Qd)
  let app := mkAppN (mkConst ``log_dyadic_bound) #[natLitShared u, natLitShared v, natLitShared N,
    natLitShared (N - 1),
    natLitShared Qd, natLitShared Q, natLitShared D, natLitShared T, natLitShared P, natLitShared p,
    natLitShared (v + u), natLitShared (v - u), reflBoolTrue,
    reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
    reflBoolTrue, reflBoolTrue, hsplit, reflBoolTrue,
    reflBoolTrue, reflBoolTrue, reflBoolTrue]
  return (app, p, Q)

open Lean Elab Term Meta in
/-- `(proof, p, Q)` with `proof : Real.IsNear (log (↑a/↑b)) false p Q 1 D`, for `a ≥ b ≥ 1` in
the artanh convergence range (an error otherwise). -/
meta def mkLogFracPos (a b D : ℕ) : MetaM (Expr × ℕ × ℕ) := do
  let g := Nat.gcd (a - b) (a + b)
  let u := (a - b) / g
  let v := (a + b) / g
  unless 2 * u ^ 2 ≤ v ^ 2 do
    throwError "mkLogFracPos: the argument {a}/{b} is out of the direct artanh series range"
  let (raw, p, Q) ← mkLogPos u v D
  let proof := mkAppN (mkConst ``logfrac_isNear)
    #[natLitShared (v + u), natLitShared (v - u), natLitShared g, natLitShared a, natLitShared b,
      natLitShared p, natLitShared Q,
      natLitShared D, reflBoolTrue, reflBoolTrue, reflBoolTrue, raw]
  return (proof, p, Q)

end BSN
