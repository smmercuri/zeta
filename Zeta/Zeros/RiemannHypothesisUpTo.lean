/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Zeros.RiemannHypothesisUpTo.Basic
public import Zeta.Zeros.CountCertificates

/-!
# The Riemann hypothesis up to the certified height

`riemannHypothesisUpTo` (`RiemannHypothesisUpTo.Basic`) instantiated at the generated certificate
`certifiedZeroCount`.
-/
@[expose] public section

/-- The Riemann hypothesis holds up to the head gram point of the generated certificate. -/
theorem riemannHypothesisUpTo_certifiedZeroCount :
    RiemannHypothesisUpTo (gramPoint certifiedZeroCount.minIdx) :=
  riemannHypothesisUpTo certifiedZeroCount
