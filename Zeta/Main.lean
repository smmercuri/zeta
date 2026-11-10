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

/-- The Riemann Hypothesis holds up to height 1000449: every zero of `riemannZeta` with
`|im| < 1000449`, other than the trivial zeros and `s = 1`, has real part `1/2`. -/
theorem riemannHypothesisUpTo_1000449 : RiemannHypothesisUpTo 1000449 :=
  fun s h_zero h_nontrivial h_one h_im =>
    riemannHypothesisUpTo certifiedZeroCount s h_zero h_nontrivial h_one
      (h_im.trans_le ((show (1000449 : ℝ) ≤ Gram.gp1.fst by norm_num).trans
        (GramPoint.certificate_left_lt_gramPoint Gram.gp1_cert).le))

/-- Every zero up to height 1000449 is simple: every zero of `riemannZeta` with
`0 < im < 1000449` has order `1`. -/
theorem simpleZerosUpTo_1000449 : SimpleZerosUpTo 1000449 :=
  (simpleZerosUpTo certifiedZeroCount).mono
    ((show (1000449 : ℝ) ≤ Gram.gp1.fst by norm_num).trans
      (GramPoint.certificate_left_lt_gramPoint Gram.gp1_cert).le)

end Zeta

end

/--
info: 'Zeta.riemannHypothesisUpTo_1000449' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Zeta.riemannHypothesisUpTo_1000449

/--
info: 'Zeta.simpleZerosUpTo_1000449' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Zeta.simpleZerosUpTo_1000449
