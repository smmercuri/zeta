/-
Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Bhavik Mehta
-/
module

public import Zeta.Zeros.RiemannHypothesisUpTo.Basic
public import Native.CountCertificates

/-!
# Riemann hypothesis up to bounded heights, checked natively

`Zeta.riemannHypothesisUpTo_1000449` again, from `Native.certifiedZeroCount`: the same
statement and the same generic argument, with the Riemann–Siegel batches checked by compiled
evaluation (`native_decide`). `#print axioms` therefore lists, besides
`propext`, `Classical.choice` and `Quot.sound`, one `native_decide` axiom per native batch: the
result trusts the Lean compiler and runtime as well as the kernel.
-/

@[expose] public section

namespace Native

open Zeta.Certificates

/-- The Riemann Hypothesis holds up to height 1000449, with the Riemann–Siegel zero
certificates checked natively: every zero of `riemannZeta` with `|im| < 1000449`, other than
the trivial zeros and `s = 1`, has real part `1/2`. -/
theorem riemannHypothesisUpTo_1000449 : RiemannHypothesisUpTo 1000449 :=
  fun s h_zero h_nontrivial h_one h_im =>
    riemannHypothesisUpTo certifiedZeroCount s h_zero h_nontrivial h_one
      (h_im.trans_le ((show (1000449 : ℝ) ≤ Gram.gp1.fst by norm_num).trans
        (GramPoint.certificate_left_lt_gramPoint Gram.gp1_cert).le))

end Native

end
