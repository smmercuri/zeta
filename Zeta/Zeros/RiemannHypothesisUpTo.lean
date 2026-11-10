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

`riemannHypothesisUpTo` (`RiemannHypothesisUpTo.Basic`) and the simplicity of the zeros,
instantiated at the generated certificate `certifiedZeroCount`.
-/
@[expose] public section

/-- The Riemann hypothesis holds up to the head gram point of the generated certificate. -/
theorem riemannHypothesisUpTo_certifiedZeroCount :
    RiemannHypothesisUpTo (gramPoint certifiedZeroCount.minIdx) :=
  riemannHypothesisUpTo certifiedZeroCount

/-- Every zero below the head gram point of the generated certificate is simple. -/
theorem meromorphicOrderAt_eq_one_certifiedZeroCount {s : ℂ}
    (hs : s.im ∈ Set.Ioo 0 (gramPoint certifiedZeroCount.minIdx)) (hs_zero : riemannZeta s = 0) :
    meromorphicOrderAt riemannZeta s = 1 :=
  riemannZeta.meromorphicOrderAt_eq_one_upto certifiedZeroCount hs hs_zero
