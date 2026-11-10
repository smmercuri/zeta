/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Zeta.Main

/-!
# Comparator solution: the headline theorem

The challenge statement, discharged by the project's `Zeta.riemannHypothesisUpTo_100013`
(whose type `RiemannHypothesisUpTo 100013` unfolds to it). Comparator re-checks the whole
dependency tree, certificate batches included, so every batch's private olean must be full-size
(`proofs.sh restore`).
-/

namespace Comparator

theorem riemannHypothesisUpTo_100013 :
    ∀ s, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → |s.im| < 100013 →
      s.re = 1 / 2 :=
  Zeta.riemannHypothesisUpTo_100013

end Comparator
