/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import Zeta.Theta
import Zeta.Gram.ZeroCounting

/-!
# Main analytic theorems

This is the comparator challenge for the main theoretical ingredients of
Turing's method.
- `riemannZeta_N_eq` is the formula `N(T) = θ(T)/π + 1 + S(T)` whenever `T` is not the ordinate
   of a zero of `ζ(s)`.
- `norm_integral_argZeta_le` is the Lehman-style bound using a weaker `5` as the additive constant.
- `riemannZeta_N_le_of_gramPoints` is Turing's bound `N(gramPoint n) ≤ n + 1` from zeros in the
  `k + 1` Gram intervals above `gramPoint n`.
-/


namespace Comparator

/-- **The Riemann–von Mangoldt formula**: `N(T) = θ(T)/π + 1 + S(T)` for `T > 0` not the
ordinate of a zero of `ζ`. -/
theorem riemannZeta_N_eq {T : ℝ} (hT : 0 < T)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) :
    riemannZeta.N T = riemannSiegelTheta T / Real.pi + 1 + argZeta T :=
  sorry

/-- **Lehman's bound**, unconditional and with an explicit constant: for `168π < t₁ < t₂`,
`|∫_{t₁}^{t₂} S(t) dt| ≤ 5 + 0.128 log(t₂/2π)`. -/
theorem norm_integral_argZeta_le_five {t₁ t₂ : ℝ} (ht1 : 168 * Real.pi < t₁) (h12 : t₁ < t₂) :
    |∫ t in t₁..t₂, argZeta t| ≤ 5 + 0.128 * Real.log (t₂ / (2 * Real.pi)) :=
  sorry

/-- **Turing's bound at a Gram point**: if each of the `k + 1` Gram intervals above `gramPoint n`
contains a zero of `ζ` on the critical line, and the run is high and wide enough for Lehman's
bound, then `N(gramPoint n) ≤ n + 1`. -/
theorem riemannZeta_N_le_of_gramPoints (n k : ℕ) (hg : 168 * Real.pi < gramPoint n)
    (h : (5 + (0.128 : ℝ) * (gramPoint (n + k + 1) / (2 * Real.pi)).log) <
      (gramPoint (n + k + 1) - gramPoint n) / 2)
    (hc : ∀ j < k + 1, ∃ t ∈ Set.Ico (gramPoint (n + j)) (gramPoint (n + j + 1)),
      riemannZeta (1 / 2 + Complex.I * t) = 0) :
    riemannZeta.N (gramPoint n) ≤ n + 1 :=
  sorry

end Comparator
