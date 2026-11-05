/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Zeta.Main

/-!
# Comparator solution: the headline theorem

The challenge statement, discharged by the project's `Zeta.riemannHypothesisUpTo_10011`
(whose type `RiemannHypothesisUpTo 10011` unfolds to it). Comparator re-checks the whole
dependency tree, certificate batches included, so every batch's private olean must be full-size
(`proofs.sh restore`).
-/

namespace Comparator

theorem riemannHypothesisUpTo_10011 :
    ∀ s, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → |s.im| < 10011 →
      s.re = 1 / 2 :=
  Zeta.riemannHypothesisUpTo_10011

end Comparator
