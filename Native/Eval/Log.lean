module

public import Enclosure.Defs
public import Enclosure.BinarySplit.Defs
public import Native.Eval.Const
public import Native.Eval.Trig

/-!
# `Native.Eval.Log`: the computable part

The definitions `native_decide` evaluates, free of `Mathlib` so that they compile natively (the
`NativeEval` library is built with `precompileModules`). Their soundness theorems are in
`Native.Log`.
-/
@[expose] public section

namespace Native

open Enclosure BSN

/-- The least `N` (counting from `N`) with `4·u^(2N+1)·2D ≤ v^(2N+1)`, with the running powers
`L = u^(2N+1)·2D` and `vk = v^(2N+1)`, cut off after `fuel` steps. The value needs no proof:
`BSN.log_dyadic_bound` re-checks the tail guard. -/
def logTermCount (u v : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, N, _, _ => N
  | fuel + 1, N, L, vk =>
    if 4 * L ≤ vk then N else logTermCount u v fuel (N + 1) (L * u ^ 2) (vk * v ^ 2)

/-- The side conditions of `BSN.log_dyadic_bound`, other than the `binarySplit` equation. -/
def logLeafOk (u v N Nm Qd Qdy D T p S Dd : Nat) : Bool :=
  u.blt v && (Nat.mul 2 (u.pow 2)).ble (v.pow 2) && Nat.ble 1 Qd && Nat.ble 1 D && Nat.ble 1 v &&
  Nat.ble 1 N && (Nm.succ).beq N && S.beq (v.add u) && Dd.beq (v.sub u) &&
  ((Nat.mul 4 (u.pow ((Nat.mul 2 N).succ))).mul (Nat.mul 2 D)).ble (v.pow ((Nat.mul 2 N).succ)) &&
  (p.mul (v.mul Qd)).ble ((Nat.mul 2 (u.mul (Qd.add T))).mul Qdy) &&
  ((Nat.mul 2 (u.mul (Qd.add T))).mul Qdy).blt ((p.succ).mul (v.mul Qd)) &&
  (Nat.mul 2 D).ble Qdy

/-- `log((v+u)/(v−u))` to `1/D`, for `2u² ≤ v²`. -/
def logLeaf (u v D : Nat) : Option Encl :=
  let Qdy := dyadic D
  let N := max 1 (logTermCount u v 10000 0 (u * (2 * D)) v)
  let Nm := N - 1
  let sp := binarySplit (artanhP u) (artanhQ v) 0 Nm
  let p := 2 * (u * (sp.2.1 + sp.1)) * Qdy / (v * sp.2.1)
  if logLeafOk u v N Nm sp.2.1 Qdy D sp.1 p (v + u) (v - u) then some ⟨false, p, Qdy, 1, D⟩
  else none

/-- `log(a/b)` for `a ≥ b ≥ 1`: reduce by `2ᵏ ≤ a/b < 2ᵏ⁺¹` to the leaf at `2a / (b·2ᵏ⁺¹)`
(`u = a − b·2ᵏ`, `v = a + b·2ᵏ`), plus `k·log 2`. -/
def logRat (a b D : Nat) : Option Encl :=
  let k := Nat.log2 (a / b)
  let u := a - b * 2 ^ k
  let v := a + b * 2 ^ k
  (logLeaf u v D).bind fun r =>
    if Nat.ble 1 a && Nat.ble 1 b && (v + u).beq (Nat.mul 2 a) &&
        (v - u).beq (Nat.mul b (Nat.pow 2 (Nat.succ k))) &&
        r.neg == false && r.rn == 1 && Nat.ble 1 r.rd && Nat.ble 1 log2Encl.rd &&
        Nat.ble 1 r.cd && Nat.ble 1 log2Encl.cd then
      some ⟨false, (r.cn.mul log2Encl.cd).add ((k.mul log2Encl.cn).mul r.cd),
        r.cd.mul log2Encl.cd, log2Encl.rd.add (k.mul r.rd), r.rd.mul log2Encl.rd⟩
    else none

/-- `log(a/b)` for any `a, b ≥ 1`: `logRat` when `a ≥ b`, else `−log(b/a)`. -/
def logRatSigned (a b D : Nat) : Option Encl :=
  if b ≤ a then logRat a b D else (logRat b a D).map Encl.negate

/-- `log n` for `n ≥ 1`. -/
def logNat (n D : Nat) : Option Encl := logRat n 1 D

/-- The side conditions of `BSN.isNear_log_image` that `Encl.hullOk` does not cover. -/
def logOk (X : Encl) (L1 K1 L2 K2 : Nat) : Bool :=
  !X.neg && Nat.ble 1 X.cd && Nat.ble 1 X.rd && Nat.ble 1 K1 && Nat.ble 1 K2 && Nat.ble 1 L1 &&
  Nat.blt (X.rn.mul X.cd) (X.cn.mul X.rd) &&
  Nat.beq (L1.mul (X.cd.mul X.rd)) (((X.cn.mul X.rd).sub (X.rn.mul X.cd)).mul K1) &&
  Nat.beq (L2.mul (X.cd.mul X.rd)) (((X.cn.mul X.rd).add (X.rn.mul X.cd)).mul K2)

/-- `log x` for `x` in a positive enclosure `X`, on the grid `1/dyadic D`: the hull of the logs of
`X`'s endpoints, each to `1/D`. -/
def log (X : Encl) (D : Nat) : Option Encl :=
  let K := X.cd.mul X.rd
  let L1 := (X.cn.mul X.rd).sub (X.rn.mul X.cd)
  let L2 := (X.cn.mul X.rd).add (X.rn.mul X.cd)
  (logRatSigned L1 K D).bind fun e₁ =>
    (logRatSigned L2 K D).bind fun e₂ =>
      if logOk X L1 K L2 K then Encl.hull e₁ e₂ (dyadic D) else none

end Native
