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

/-- Artanh term count for `log((v+u)/(v−u))` at `1/D` (mirrors the private `logTermCount`). -/
private meta partial def logTermCountAux (u v N L vk : ℕ) : ℕ :=
  if 4 * L ≤ vk then N
  else logTermCountAux u v (N + 1) (L * u ^ 2) (vk * v ^ 2)

/-- Least `N` with `4·u^(2N+1)·2D ≤ v^(2N+1)`. The powers are threaded incrementally (like
`expTermCount`), not recomputed per step; a from-scratch `u^(2N+1)` each iteration would make
the search quadratic in `N`. -/
private meta def logTermCount (u v D : ℕ) : ℕ := logTermCountAux u v 0 (u * (2 * D)) v

open Lean Elab Term Meta in
/-- Core for `log((v+u)/(v−u))` at `1/D`: pick `Q = 2^k` and `N`, run the binary split over
`[0, N-1)`, and floor-round `2·u·(Qd+T)/(v·Qd)` to the dyadic numerator. -/
meta def logCore (u v D : ℕ) : MetaM (ℕ × ℕ × ℕ × (ℕ × ℕ × ℕ)) := do
  let Q := dyadicDenom D
  let N := logTermCount u v D
  let (T, Qd, P) :=
    evalFoldGen (fun m => u ^ 2 * (2 * m + 1)) (fun m => v ^ 2 * (2 * m + 3)) 0 (N - 1)
  return (2 * (u * (Qd + T)) * Q / (v * Qd), Q, N, (T, Qd, P))

open Lean Elab Term Meta in
/-- Build the positive inner enclosure `Real.IsNear (log (↑S/↑Dd)) false p Q 1 D` (with
`S = v+u`, `Dd = v−u` passed as literals) and return `(proof, p, Q)`: run `binarySplit` over
`[0, N−1)` on the artanh series, then assign `log_dyadic_bound`. -/
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
/-- Build the enclosure `Real.IsNear (log (↑a/↑b)) false p Q 1 D` for a rational `a/b ≥ 1`
(`a ≥ b ≥ 1`) in the artanh convergence range, and return `(proof, p, Q)`. The artanh split
runs on the gcd-reduced pair `u = (a−b)/g`, `v = (a+b)/g` (so canonical inputs stay small),
and the raw `log((v+u)/(v−u))` certificate is recast to `log(a/b)` by the weighted
`logfrac_isNear`. -/
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
