/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Native.Eval.Log
public import Native.Const
public import Native.Eval.Const
public import Enclosure.BinarySplit.Functions.Cos
public import Enclosure.BinarySplit.Functions.Sin
public import Enclosure.BinarySplit.Reduce.Sin
public import Enclosure.Defs
public import Enclosure.BinarySplit.Defs
public import Enclosure.BinarySplit.Functions.Log
public import Enclosure.BinarySplit.Reduce.Log

/-!
# Native `log`

* `logLeaf u v D`: `log((v+u)/(v−u))` to `1/D` by the artanh series (`BSN.log_dyadic_bound`);
* `logRat a b D`: `log(a/b)` for `a ≥ b ≥ 1`, reducing by `2ᵏ` with `log 2`
  (`BSN.log_rat_reduce_isNear`); `logRatSigned` also takes `a < b`, through `log(a/b) = −log(b/a)`;
* `logNat n D`: `log n`;
* `log X D`: `log x` for a positive enclosure, between the logs of its endpoints
  (`BSN.isNear_log_image`).
-/
@[expose] public section

namespace Native

open Enclosure BSN

theorem logLeaf_encloses {u v D : ℕ} {e : Encl} (h : logLeaf u v D = some e) :
    e.Encloses (Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ))) := by
  simp only [logLeaf] at h
  split at h
  · rename_i hc
    simp only [logLeafOk, Bool.and_eq_true, and_assoc] at hc
    obtain ⟨huv, hg, hQd, hD, hv, hN, hNm, hS, hDd, htail, hr1, hr2, hQ⟩ := hc
    cases h
    exact log_dyadic_bound _ _ _ _ _ _ _ _ _ _ _ _ huv hg hQd hD hv hN hNm hS hDd rfl htail hr1
      hr2 hQ
  · cases h

theorem logRat_encloses {a b D : ℕ} {e : Encl} (h : logRat a b D = some e) :
    e.Encloses (Real.log ((a : ℝ) / b)) := by
  simp only [logRat, Option.bind_eq_some_iff] at h
  obtain ⟨r, hr, he⟩ := h
  split at he
  · rename_i hc
    simp only [Bool.and_eq_true, and_assoc, beq_iff_eq] at hc
    obtain ⟨ha, hb, hS, hDd, hneg, hrn, hD, hE, hQr, hQ2⟩ := hc
    cases he
    have hleaf := logLeaf_encloses hr
    obtain ⟨rneg, rcn, rcd, rrn, rrd⟩ := r
    simp only at hneg hrn hD hQr ⊢
    subst hneg hrn
    exact log_rat_reduce_isNear _ _ _ _ _ _ _ _ _ _ _ ha hb hS hDd hleaf log2Encl_encloses hD hE
      hQr hQ2
  · cases he

theorem logRatSigned_encloses {a b D : ℕ} {e : Encl} (h : logRatSigned a b D = some e) :
    e.Encloses (Real.log ((a : ℝ) / b)) := by
  simp only [logRatSigned] at h
  split at h
  · exact logRat_encloses h
  · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    have hlog : Real.log ((a : ℝ) / b) = -Real.log ((b : ℝ) / a) := by
      rw [← Real.log_inv, inv_div]
    rw [hlog]
    exact Encl.negate_encloses (logRat_encloses hc)

theorem logNat_encloses {n D : ℕ} {e : Encl} (h : logNat n D = some e) :
    e.Encloses (Real.log (n : ℝ)) := by
  simpa using logRat_encloses h

theorem log_encloses {X e : Encl} {D : ℕ} {x : ℝ} (hx : X.Encloses x) (h : log X D = some e) :
    e.Encloses (Real.log x) := by
  simp only [log, Option.bind_eq_some_iff] at h
  obtain ⟨e₁, h₁, e₂, h₂, he⟩ := h
  split at he
  · rename_i hc
    simp only [logOk, Bool.and_eq_true, and_assoc, Bool.not_eq_true'] at hc
    obtain ⟨hneg, hcd, hrd, hK1, hK2, hL1, hpos, hE1, hE2⟩ := hc
    simp only [Encl.hull] at he
    split at he
    · rename_i hh
      simp only [Encl.hullOk, Bool.and_eq_true, and_assoc] at hh
      obtain ⟨hd1, he1, hd2, he2, hcdR, hrdR, hL, hH⟩ := hh
      cases he
      obtain ⟨xneg, xcn, xcd, xrn, xrd⟩ := X
      simp only at hneg
      subst hneg
      have l1 := logRatSigned_encloses h₁
      have l2 := logRatSigned_encloses h₂
      rw [← sfrac_false_div] at l1 l2
      exact isNear_log_image hx hcd hrd hK1 hK2 hL1 hpos hE1 hE2 l1 l2 hd1 he1 hd2 he2 hcdR hrdR
        hL hH
    · cases he
  · cases he

end Native
