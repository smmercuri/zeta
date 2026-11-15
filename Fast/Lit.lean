/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Lean

/-!
# Compiled helpers for the certificate builder

The builder's hottest helpers, stated over `Lean.Expr` and `Nat` alone so the module carries no
`Mathlib` import and its library can set `precompileModules`. `Enclosure.BinarySplit.Tactic`
re-exports these names, and callers use them from there.
-/
@[expose] public section

namespace BSN

open Lean

/-- The term `@Eq.refl Bool true`, a proof of any `(b : Bool) = true` the kernel reduces to
`true`. -/
meta def reflBoolTrue : Expr :=
  mkApp2 (.const ``Eq.refl [.succ .zero]) (.const ``Bool []) (.const ``Bool.true [])

/-- Cache key wrapping `ℕ`, hashed modulo the largest 64-bit prime. Core's `Hashable Nat` keeps only
the low 64 bits, so every `2^k` with `k ≥ 64` would hash to `0`. -/
structure NatLitKey where
  val : Nat

meta instance : BEq NatLitKey := ⟨fun a b => a.val == b.val⟩
meta instance : Hashable NatLitKey := ⟨fun a => UInt64.ofNat (a.val % 18446744073709551557)⟩

/-- Process-global interning cache for big `ℕ` literal `Expr`s (see `natLitShared`). A
`PersistentHashMap` because an interpreted `Std.HashMap` copies the whole table per insert. -/
meta initialize natLitCache : IO.Ref (Lean.PersistentHashMap NatLitKey Expr) ← IO.mkRef {}

private meta unsafe def natLitSharedImpl (n : Nat) : Expr :=
  if n < 9223372036854775808 then
    mkRawNatLit n
  else
    unsafeBaseIO do
      -- lock-free hit path (`get`, no `take`); a racing double-insert of the same value is
      -- benign: both objects are structurally identical, one wins the map
      match (← natLitCache.get).find? ⟨n⟩ with
      | some e => return e
      | none =>
        let e := mkRawNatLit n
        natLitCache.modify (·.insert ⟨n⟩ e)
        return e

/-- `mkRawNatLit` that returns one shared `Expr` object per big (`≥ 2^63`) value, so the compacted
olean, which deduplicates big `Nat` payloads only by pointer, stores each such numeral once.
Reads are lock-free; the insert is safe under parallel elaboration. -/
@[implemented_by natLitSharedImpl]
meta def natLitShared (n : Nat) : Expr := mkRawNatLit n

/-- `Nat.gcd n B` for a power of two `B`, computed as the lowest set bit of `n % B` (or `B` when
that is `0`). -/
meta def gcdPow2 (n B : Nat) : Nat :=
  let m := n % B
  if m == 0 then B else m - Nat.land m (m - 1)

/-- Target dyadic precision for `renorm`: centre/radius denominators are capped at
`2 ^ renormBits`, far above the certificate precision. -/
meta def renormBits : Nat := 1024

/-- The fields `(cn', cd', rn', rd')` obtained by flooring the centre `cn/cd` and ceiling the
radius `rn/rd` (plus the centre drop) onto the dyadic grid `·/B`, then `gcd`-reducing. -/
meta def roundFieldsAt (cn cd rn rd B : Nat) : Nat × Nat × Nat × Nat :=
  let cnF := (cn * B) / cd                  -- floor of cn/cd onto ·/B
  let cnErr := cn * B - cnF * cd            -- = (cn·B) mod cd, in [0, cd)
  let Nnum := rn * (cd * B) + cnErr * rd    -- numerator of rn/rd + δ over rd·cd·B
  let Dden := rd * (cd * B)
  let rnF := (Nnum * B + Dden - 1) / Dden   -- ceil of (rn/rd + δ) onto ·/B
  let gc := gcdPow2 cnF B
  let gr := gcdPow2 rnF B
  (cnF / gc, B / gc, rnF / gr, B / gr)

/-- The rounding arithmetic of `renorm`: `none` when both denominators already fit under the
scale-aware cap, else `roundFieldsAt` at that cap. -/
meta def renormFields? (cn cd rn rd : Nat) : Option (Nat × Nat × Nat × Nat) :=
  -- Scale-aware cap: about `renormBits` significant bits. For a value of magnitude `2^{-e}`
  -- the denominator cap is `2^{renormBits+e}`, so a value far below `2^{-renormBits}` retains
  -- its significant bits. Values of magnitude `≥ 1` use the plain `2^{renormBits}` cap.
  let e :=
    if cn != 0 then cd.log2 - cn.log2
    else if rn != 0 then rd.log2 - rn.log2
    else 0
  let B := 2 ^ (renormBits + min e 4096)
  if cd ≤ B && rd ≤ B then
    none
  else
    some (roundFieldsAt cn cd rn rd B)

end BSN
