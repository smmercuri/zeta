/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Zeros.Certificates.Basic

/-!
# Folding batch statements

`BatchSpec.append` concatenates two batches at the level of their exported statements: from
`BatchSpec n₁ a … b …` and `BatchSpec n₂ c … e …` and one cross-multiplied `Nat.ble` for the seam
`b ≤ c`, it concludes `BatchSpec (n₁ + n₂) a … e …`. The generated assembler folds the batches
through it one prefix theorem at a time, so each step is `O(1)` and states its count and boundary
as literals.

This lives apart from `Basic` because every batch module imports `Basic` (through the certificate
metaprogram), while only the assembler needs the fold.
-/
@[expose] public section

namespace Zeta.Certificates

/-- Append two batch statements. The seam is the exported boundary `bn/bd ≤ cn/cd`, as one
cross-multiplied `Nat.ble` on the literals. -/
theorem BatchSpec.append {n₁ an ad bn bd n₂ cn cd en ed : ℕ} (h₁ : BatchSpec n₁ an ad bn bd)
    (h₂ : BatchSpec n₂ cn cd en ed) (hbd : Nat.ble 1 bd = true) (hcd : Nat.ble 1 cd = true)
    (hseam : Nat.ble (bn.mul cd) (cn.mul bd) = true) : BatchSpec (n₁ + n₂) an ad en ed := by
  obtain ⟨C, hCl, hCh, hCt⟩ := h₁
  obtain ⟨D, hDl, hDh, hDt⟩ := h₂
  have hC : C.intervals ≠ [] := by intro he; rw [he] at hCh; simp at hCh
  have hD : D.intervals ≠ [] := by intro he; rw [he] at hDh; simp at hDh
  refine ⟨C.append D (separated_of_endpoints hCt hDh
    (Enclosure.dec_le_dec bn bd cn cd rfl rfl hbd hcd hseam)), ?_, ?_, ?_⟩
  · simp [hCl, hDl]
  · rw [CertifiedZeroIntervals.append_intervals, List.head?_append_of_ne_nil _ hC, hCh]
  · rw [CertifiedZeroIntervals.append_intervals, List.getLast?_append_of_ne_nil _ hD, hDt]

end Zeta.Certificates
