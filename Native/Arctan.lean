/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Native.Eval.Arctan
public import Native.Eval.Const
public import Native.Const
public import Enclosure.BinarySplit.Functions.Cos
public import Enclosure.BinarySplit.Functions.Sin
public import Enclosure.BinarySplit.Reduce.Sin
public import Enclosure.Defs
public import Enclosure.BinarySplit.Defs
public import Enclosure.BinarySplit.Functions.Arctan

/-!
# Native `arctan`

`arctanRat u v D`: `arctan(u/v)` to `1/D` for `u < v`, by binary splitting
(`BSN.arctan_dyadic_bound`).
-/
@[expose] public section

namespace Native

open Enclosure BSN

theorem arctanRat_encloses {u v D : ℕ} {e : Encl} (h : arctanRat u v D = some e) :
    e.Encloses (Real.arctan ((u : ℝ) / v)) := by
  simp only [arctanRat] at h
  split at h
  · rename_i hc
    simp only [arctanRatOk, Bool.and_eq_true, and_assoc] at hc
    obtain ⟨huv, hQe, hQo, hD, hv, hM, hMm, htail, hr1, hr2, hQ⟩ := hc
    cases h
    exact arctan_dyadic_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ huv hQe hQo hD hv hM hMm rfl rfl htail
      hr1 hr2 hQ
  · cases h

end Native
