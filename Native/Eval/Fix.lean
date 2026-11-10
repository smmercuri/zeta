/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Native.Eval.Encl
public import Enclosure.Defs
public import Enclosure.BinarySplit.Defs
public import Native.Eval.Const

/-!
# `Native.Eval.Fix`: fixed-point enclosures, the computable part

An `Fx` encloses a real number on a fixed grid `1/Q` (a power of two shared by a whole computation):
`x ∈ c/Q ± r/Q`. Addition, subtraction and integer scaling are exact numerator arithmetic;
multiplication is one product, a floor division by `Q` and a rounded-up radius. `cos` and `sin` are
Taylor polynomials evaluated in `Fx` plus the series' remainder bound, after reducing the argument
by the nearest multiple of `π/2`. The soundness theorems are in `Native.Fix`.
-/
@[expose] public section

namespace Native

/-- A fixed-point enclosure on the grid `1/Q`: `x ∈ c/Q ± r/Q`, with `|c| ≤ m·Q`. The magnitude
bound `m` is small, so multiplication bounds its radius with machine-word arithmetic on `m`. -/
structure Fx where
  c : Int
  r : Nat
  m : Nat
  deriving Repr

namespace Fx

/-- The exact zero. -/
def zero : Fx := ⟨0, 0, 0⟩

/-- The exact integer `k`. -/
def ofInt (Q : Nat) (k : Int) : Fx := ⟨k * Q, 0, k.natAbs⟩

/-- `x + y`. -/
def add (a b : Fx) : Fx := ⟨a.c + b.c, a.r + b.r, a.m + b.m⟩

/-- `−x`. -/
def neg (a : Fx) : Fx := ⟨-a.c, a.r, a.m⟩

/-- `x − y`. -/
def sub (a b : Fx) : Fx := ⟨a.c - b.c, a.r + b.r, a.m + b.m⟩

/-- `k·x` for an integer `k`. -/
def smul (k : Int) (a : Fx) : Fx := ⟨k * a.c, k.natAbs * a.r, k.natAbs * a.m⟩

/-- `x·y`: the floor of the exact centre `cₐc_b/Q`, and the interval-product radius with the
centres bounded by their magnitudes, plus the floor's rounding. -/
def mul (Q : Nat) (a b : Fx) : Fx :=
  ⟨a.c * b.c / (Q : Int), a.m * b.r + b.m * a.r + a.r * b.r / Q + 2, a.m * b.m⟩

/-- `x·y` as `mul`, but with the centres themselves in the radius rather than their magnitude
bounds: tighter when a factor is far below `1`, since `m ≥ 1` for any nonzero value. -/
def mulExact (Q : Nat) (a b : Fx) : Fx :=
  ⟨a.c * b.c / (Q : Int), (a.c.natAbs * b.r + b.c.natAbs * a.r + a.r * b.r) / Q + 2, a.m * b.m⟩

/-- `x/k` for a positive integer `k`. -/
def divNat (k : Nat) (a : Fx) : Fx := ⟨a.c / (k : Int), a.r / k + 2, a.m / k + 1⟩

/-- The same enclosure with its magnitude bound recomputed from the centre (the carried bound
drifts after cancellation or long sums). -/
def tighten (Q : Nat) (a : Fx) : Fx := ⟨a.c, a.r, a.c.natAbs / Q + 1⟩

/-- Widen the radius by `R`. -/
def addRad (a : Fx) (R : Nat) : Fx := ⟨a.c, a.r + R, a.m⟩

/-- An upper bound `B` on `|x|`, as `|x| ≤ B/Q`. -/
def absBound (a : Fx) : Nat := a.c.natAbs + a.r

/-- The rational `±a/b` (`b ≥ 1`). -/
def ofRat (neg : Bool) (a b Q : Nat) : Fx :=
  ⟨(if neg then -(a : Int) else a) * Q / (b : Int), 1, a / b + 1⟩

/-- An `Encl` (with positive denominators) on the grid `1/Q`. -/
def ofEncl (Q : Nat) (e : Encl) : Option Fx :=
  if Nat.ble 1 e.cd && Nat.ble 1 e.rd then
    some ⟨(if e.neg then -(e.cn : Int) else e.cn) * Q / (e.cd : Int), (e.rn * Q) / e.rd + 2,
      e.cn / e.cd + 1⟩
  else none

/-- The same enclosure as an `Encl` over `Q`. -/
def toEncl (Q : Nat) (a : Fx) : Encl := ⟨decide (a.c < 0), a.c.natAbs, Q, a.r, Q⟩

/-! ### Inverse and square root -/

/-- The enclosure of `y` from integer bounds `a ≤ Q·y ≤ b`: centre `⌊(a+b)/2⌋`, radius to `b`. -/
def ofBounds (Q a b : Nat) : Fx := ⟨((a + b) / 2 : Nat), b - (a + b) / 2, b / Q + 1⟩

/-- `1/x` for `x` enclosed by a strictly positive `X`: `Q/x` lies in
`[⌊Q²/(c+r)⌋, ⌈Q²/(c−r)⌉]`. -/
def invPos (Q : Nat) (X : Fx) : Option Fx :=
  if Nat.ble 1 Q && decide ((X.r : Int) < X.c) then
    some (ofBounds Q (Q * Q / (X.c.toNat + X.r))
      ((Q * Q + (X.c.toNat - X.r) - 1) / (X.c.toNat - X.r)))
  else none

/-- `1/x` for `x` enclosed by an `X` excluding `0`: `invPos`, through `x⁻¹ = −(−x)⁻¹` if
negative. -/
def inv (Q : Nat) (X : Fx) : Option Fx :=
  if X.c < 0 then (invPos Q (neg X)).map neg else invPos Q X

/-- `√x` for `x` enclosed by `X`: `Q·√x` lies in `[⌊√((c−r)Q)⌋, ⌊√((c+r)Q)⌋ + 1]` (the ends
clamped at `0`). -/
def sqrt (Q : Nat) (X : Fx) : Option Fx :=
  if Nat.ble 1 Q then
    some (ofBounds Q (Nat.sqrt ((X.c - X.r).toNat * Q)) (Nat.sqrt ((X.c + X.r).toNat * Q) + 1))
  else none

/-! ### Taylor polynomials -/

/-- The terms and partial sums of the `cos` series at `x`, given `X2` enclosing `x²`: after `k`
steps, the term `(−1)^k x^{2k}/(2k)!` and the sum of the terms before it. -/
def cosSeries (Q : Nat) (X2 : Fx) : Nat → Fx × Fx
  | 0 => (ofInt Q 1, zero)
  | k + 1 =>
    let ts := cosSeries Q X2 k
    (divNat ((2 * k + 1) * (2 * k + 2)) (neg (mul Q ts.1 X2)), add ts.2 ts.1)

/-- The terms and partial sums of the `sin` series at `x`, given `X` and `X2`: after `k` steps, the
term `(−1)^k x^{2k+1}/(2k+1)!` and the sum of the terms before it. -/
def sinSeries (Q : Nat) (X X2 : Fx) : Nat → Fx × Fx
  | 0 => (X, zero)
  | k + 1 =>
    let ts := sinSeries Q X X2 k
    (divNat ((2 * k + 2) * (2 * k + 3)) (neg (mul Q ts.1 X2)), add ts.2 ts.1)

/-- `m!` (Lean core has no factorial). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `⌈2Q/(D^m·m!)⌉`: on the grid, twice the series remainder bound `|x|^m/m!` for `|x| ≤ 1/D`. -/
@[inline] def remainder (Q D m : Nat) : Nat := (2 * Q + D ^ m * fact m - 1) / (D ^ m * fact m)

/-- The side conditions of `cosTaylor`/`sinTaylor`: `|x| ≤ 1/D` and at least one term. -/
@[inline] def taylorOk (Q D N : Nat) (X : Fx) : Bool :=
  Nat.ble 1 Q && Nat.ble 1 D && Nat.ble 1 N && Nat.ble (D * X.absBound) Q

/-- `cos x` for `x` enclosed by `X` with `|x| ≤ 1/D`: the Taylor polynomial of `N` terms evaluated
in `Fx`, plus the remainder bound. -/
@[inline] def cosTaylor (Q D N : Nat) (X : Fx) : Option Fx :=
  if taylorOk Q D N X then
    some (tighten Q (addRad (cosSeries Q (mul Q X X) N).2 (remainder Q D (2 * N))))
  else none

/-- `sin x` for `x` enclosed by `X` with `|x| ≤ 1/D`; see `cosTaylor`. -/
@[inline] def sinTaylor (Q D N : Nat) (X : Fx) : Option Fx :=
  if taylorOk Q D N X then
    some (tighten Q (addRad (sinSeries Q X (mul Q X X) N).2 (remainder Q D (2 * N + 1))))
  else none

/-- `(cos x, sin x)` by the two Taylor polynomials. -/
@[inline] def taylorPair (Q D N : Nat) (X : Fx) : Option (Fx × Fx) :=
  (cosTaylor Q D N X).bind fun C => (sinTaylor Q D N X).map fun S => (C, S)

/-- The rotation `(cos(a+b), sin(a+b))` from `(cos a, sin a)` and `(cos b, sin b)`. -/
def rotate (Q : Nat) (a b : Fx × Fx) : Fx × Fx :=
  (tighten Q (sub (mul Q a.1 b.1) (mul Q a.2 b.2)),
    tighten Q (add (mul Q a.2 b.1) (mul Q a.1 b.2)))

/-! ### Reduction by `k·π/2` -/

/-- The nearest multiple `k` of `π/2` to the centre of `X`, from an enclosure `H` of `π/2`, as an
integer. Any `k` is sound; the nearest keeps the reduced argument small. -/
def nearestQuarter (X H : Fx) : Int :=
  if H.c ≤ 0 then 0 else (2 * X.c + H.c) / (2 * H.c)

/-- `cos(y + j·π/2)` from enclosures `C`, `S` of `cos y`, `sin y`, by `j mod 4`. -/
def quadrantCos (j : Nat) (C S : Fx) : Fx :=
  match j % 4 with
  | 0 => C
  | 1 => neg S
  | 2 => neg C
  | _ => S

/-- `sin(y + j·π/2)` from enclosures `C`, `S` of `cos y`, `sin y`, by `j mod 4`. -/
def quadrantSin (j : Nat) (C S : Fx) : Fx :=
  match j % 4 with
  | 0 => S
  | 1 => C
  | 2 => neg S
  | _ => neg C

/-- `(cos x, sin x)` for any `x` enclosed by `X`, given an enclosure `H` of `π/2` and an evaluator
`g` for small arguments: reduce to `y = x − k·π/2` and apply `g` at `y`. -/
def reduce (Q : Nat) (H : Fx) (g : Fx → Option (Fx × Fx)) (X : Fx) : Option (Fx × Fx) :=
  reduceAt (nearestQuarter X H) (g (tighten Q (sub X (smul (nearestQuarter X H) H))))
where
  /-- With the quarter turns `k` fixed. -/
  reduceAt (k : Int) (o : Option (Fx × Fx)) : Option (Fx × Fx) :=
    o.map fun cs => (quadrantCos (k % 4).toNat cs.1 cs.2, quadrantSin (k % 4).toNat cs.1 cs.2)

/-- The number of series terms at `|x| ≤ 1`: enough for `2⁻¹⁰⁰`. -/
def taylorTerms : Nat := 14

/-- `(cos x, sin x)` for any `x`, by the Taylor polynomials after reduction. -/
def cosSin (Q : Nat) (H X : Fx) : Option (Fx × Fx) := reduce Q H (taylorPair Q 1 taylorTerms) X

/-! ### A table of `cos`/`sin` at multiples of `1/128` -/

/-- The table's step is `1/tableScale`. -/
def tableScale : Nat := 128

/-- The number of series terms at `|x| ≤ 1/128`: enough for `2⁻⁷⁰`. -/
def smallTerms : Nat := 4

/-- `(cos(j/128), sin(j/128))` for `j = 0, …, 102`, covering `[0, π/4]` with room for rounding;
`H` encloses `π/2`. -/
def trigTable (Q : Nat) (H : Fx) : Array (Option (Fx × Fx)) :=
  Array.ofFn (n := 103) fun j => cosSin Q H (ofRat false j.1 tableScale Q)

/-- `(cos(j/128), sin(j/128))` for any integer `j`, from the table: `cos` is even and `sin` odd. -/
def trigAt (tbl : Array (Option (Fx × Fx))) (j : Int) : Option (Fx × Fx) :=
  (tbl[j.natAbs]?.join).map fun cs => if j < 0 then (cs.1, neg cs.2) else cs

/-- The table index nearest to the centre of `Y`: `⌊128·c/Q + 1/2⌋`. -/
def tableIndex (Q : Nat) (Y : Fx) : Int := (2 * tableScale * Y.c + Q) / (2 * (Q : Int))

/-- `(cos y, sin y)` for small `y` enclosed by `Y`: split `y = j/128 + r` at the nearest `j`, take
`(cos, sin)(j/128)` from the table and the short series at `r`, and rotate. -/
def nearTable (Q : Nat) (tbl : Array (Option (Fx × Fx))) (Y : Fx) : Option (Fx × Fx) :=
  nearAt Q tbl (tableIndex Q Y) Y
where
  /-- With the table index `j` fixed. -/
  nearAt (Q : Nat) (tbl : Array (Option (Fx × Fx))) (j : Int) (Y : Fx) : Option (Fx × Fx) :=
    (trigAt tbl j).bind fun a =>
      (taylorPair Q tableScale smallTerms
        (tighten Q (sub Y (ofRat (decide (j < 0)) j.natAbs tableScale Q)))).map (rotate Q a)

/-- `(cos x, sin x)` for any `x` enclosed by `X`, with the table: reduce by quarter turns, then
`nearTable`. -/
def cosSinT (Q : Nat) (H : Fx) (tbl : Array (Option (Fx × Fx))) (X : Fx) : Option (Fx × Fx) :=
  reduce Q H (nearTable Q tbl) X

end Fx

end Native
