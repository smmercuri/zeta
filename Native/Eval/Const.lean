/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Enclosure.Defs
public import Enclosure.BinarySplit.Defs
public import Native.Eval.Encl

/-!
# `Native.Eval.Const`: the computable part

The definitions `native_decide` evaluates, free of `Mathlib` so that they compile natively (the
`NativeEval` library is built with `precompileModules`). Their soundness theorems are in
`Native.Const`.
-/
@[expose] public section

namespace Native

open Enclosure BSN

/-- `π` to `1/10⁵⁰`: the fields of `BSN.pi_near_50`. -/
def piEncl : Encl :=
  ⟨false, 18806549737669504701992162098148602382148218980016788,
    5986310706507378352962293074805895248510699696029696,
    nat_lit 1, nat_lit 100000000000000000000000000000000000000000000000000⟩

/-- `log 2` to `1/10⁵⁰`: the fields of `BSN.log2_near_50`. -/
def log2Encl : Encl :=
  ⟨false, 4149394388171403555371821489548486867298455139804967,
    5986310706507378352962293074805895248510699696029696,
    1, 100000000000000000000000000000000000000000000000000⟩

/-- A power of two `≥ 2·D` (so that `(2D).ble Q`): the leaves' output denominator. -/
def dyadic (D : Nat) : Nat := 2 ^ (Nat.log2 (2 * D) + 1)

/-- The signed floor of `(A − B)/den`, as `(sign, magnitude)`: `⌊(A−B)/den⌋` when `B ≤ A`, else
`−⌈(B−A)/den⌉`. -/
def signedFloor (A B den : Nat) : Bool × Nat :=
  if B ≤ A then (false, (A - B) / den) else (true, (B - A + den - 1) / den)

end Native
