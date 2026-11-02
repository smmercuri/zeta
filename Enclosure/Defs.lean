module

/-!
# Enclosure definitions that need no `Mathlib`

The plain computable definitions the `Enclosure` certificate lemmas state their side conditions
with, kept free of `Mathlib` so that compiled checkers (the `NativeCode` library) can use exactly
the same functions the lemmas mention.

* `numPos`/`numNeg`: the natural parts of a signed numerator `±cn`;
* `recentreOk`: the side conditions of `Real.IsNear.recentre'`, as one Boolean.
-/
@[expose] public section

namespace Enclosure

/-- The positive part of the signed numerator `±cn`: `cn` if nonnegative, else `0`. -/
def numPos (neg : Bool) (cn : Nat) : Nat := if neg then 0 else cn

/-- The negative part of the signed numerator `±cn`: `cn` if negative, else `0`. -/
def numNeg (neg : Bool) (cn : Nat) : Nat := if neg then cn else 0

/-- The six side conditions of `Real.IsNear.recentre'`, as one Boolean. Each `a ≤ b` is carried as
`Nat.sub a b`, zero exactly when it holds, and the six are summed and compared against zero, so the
whole check stays on `Nat.sub`/`add`/`mul`/`beq`. -/
def recentreOk (cn cd rn rd cn' cd' rn' rd' : Nat) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cd)
    (Nat.add (Nat.sub (nat_lit 1) cd')
    (Nat.add (Nat.sub (nat_lit 1) rd)
    (Nat.add (Nat.sub (nat_lit 1) rd')
    (Nat.add (Nat.sub (cn'.mul cd) (cn.mul cd'))
             (Nat.sub (((rn.mul (cd.mul cd')).add (((cn.mul cd').sub (cn'.mul cd)).mul rd)).mul rd')
                      (rn'.mul (rd.mul (cd.mul cd')))))))))
    (nat_lit 0)

end Enclosure
