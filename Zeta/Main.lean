/-
Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Bhavik Mehta
-/
module

public import Zeta.Zeros.RiemannHypothesisUpTo

/-!
# Riemann hypothesis up to bounded heights

-/

@[expose] public section

namespace Zeta

open Zeta.Certificates

/-- **The Riemann Hypothesis holds up to height 10011**: every zero of `riemannZeta` with
`|im| < 10011`, other than the trivial zeros and `s = 1`, has real part `1/2`. -/
theorem riemannHypothesisUpTo_10011 : RiemannHypothesisUpTo 10011 :=
  fun s h_zero h_nontrivial h_one h_im =>
    riemannHypothesisUpTo certifiedZeroCount s h_zero h_nontrivial h_one
      (h_im.trans_le ((show (10011 : ℝ) ≤ Gram.gp1.fst by norm_num).trans
        (GramPoint.certificate_left_lt_gramPoint Gram.gp1_cert).le))

end Zeta

end

/--
info: 'Zeta.riemannHypothesisUpTo_10011' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Zeta.riemannHypothesisUpTo_10011
