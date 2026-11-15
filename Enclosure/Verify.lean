/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.Core
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Real interval enclosures: the bound verifier and comparisons

The generic bound verifier `isNear_verify_le`, sign extraction (`pos_val`/`neg_val`), and the
certificate comparisons (`norm_gt_of_isNear`, `gt_of_isNear`).
-/
@[expose] public section


namespace Enclosure

/-! ### The generic bound verifier -/

/-- Generic bound verifier: `|X − q| ≤ eps` when an enclosure of `X` lies inside
`[q − eps, q + eps]` (`hlo`/`hhi`). -/
theorem isNear_verify_le (X q eps : ℝ) (cneg qneg : Bool) (cn cd rn rd qn qd en ed : ℕ)
    (hcert : Real.IsNear X cneg cn cd rn rd)
    (hq : q = sfrac qneg qn qd) (heps : eps = sfrac false en ed)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hqd : Nat.ble 1 qd) (hed : Nat.ble 1 ed)
    (hlo : Nat.ble ((((numPos qneg qn).mul ((ed.mul cd).mul rd)).add
              ((numNeg cneg cn).mul ((qd.mul ed).mul rd))).add
              (rn.mul ((cd.mul qd).mul ed)))
            ((((numPos cneg cn).mul ((qd.mul ed).mul rd)).add
              ((numNeg qneg qn).mul ((ed.mul cd).mul rd))).add
              (en.mul ((qd.mul cd).mul rd))))
    (hhi : Nat.ble ((((numPos cneg cn).mul ((qd.mul ed).mul rd)).add
              ((numNeg qneg qn).mul ((ed.mul cd).mul rd))).add
              (rn.mul ((cd.mul qd).mul ed)))
            ((((numPos qneg qn).mul ((ed.mul cd).mul rd)).add
              ((numNeg cneg cn).mul ((qd.mul ed).mul rd))).add
              (en.mul ((qd.mul cd).mul rd)))) :
    |X - q| ≤ eps := by
  subst hq heps
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hqdR : (0:ℝ) < qd := pos_real_of_ble hqd
  have hedR : (0:ℝ) < ed := pos_real_of_ble hed
  have heps : sfrac false en ed = (en : ℝ) / ed := by simp [sfrac]
  rw [Real.IsNear, abs_le] at hcert
  have hloR : sfrac qneg qn qd - (en : ℝ) / ed ≤ sfrac cneg cn cd - (rn : ℝ) / rd := by
    rw [sfrac_eq_parts qneg qn qd, sfrac_eq_parts cneg cn cd,
      div_sub_div _ _ hqdR.ne' hedR.ne', div_sub_div _ _ hcdR.ne' hrdR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos qneg qn * (ed * cd * rd) + numNeg cneg cn * (qd * ed * rd)
                + rn * (cd * qd * ed) : ℕ) : ℝ)
            ≤ ((numPos cneg cn * (qd * ed * rd) + numNeg qneg qn * (ed * cd * rd)
                + en * (qd * cd * rd) : ℕ) : ℝ) := by exact_mod_cast hlo
    push_cast at hc ⊢; nlinarith [hc]
  have hhiR : sfrac cneg cn cd + (rn : ℝ) / rd ≤ sfrac qneg qn qd + (en : ℝ) / ed := by
    rw [sfrac_eq_parts qneg qn qd, sfrac_eq_parts cneg cn cd,
      div_add_div _ _ hcdR.ne' hrdR.ne', div_add_div _ _ hqdR.ne' hedR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos cneg cn * (qd * ed * rd) + numNeg qneg qn * (ed * cd * rd)
                + rn * (cd * qd * ed) : ℕ) : ℝ)
            ≤ ((numPos qneg qn * (ed * cd * rd) + numNeg cneg cn * (qd * ed * rd)
                + en * (qd * cd * rd) : ℕ) : ℝ) := by exact_mod_cast hhi
    push_cast at hc ⊢; nlinarith [hc]
  rw [heps, abs_le]
  exact ⟨by linarith [hcert.1, hloR], by linarith [hcert.2, hhiR]⟩

/-- Fast verifier when the goal's `q` equals the enclosure centre as a rational (same sign,
`qn·cd = cn·qd`): only that and `rn·ed ≤ en·rd` are checked, avoiding `isNear_verify_le`'s
four-denominator products. The centre is compared by cross-multiplication because `q` may be a
gcd-reduced literal. -/
theorem isNear_verify_le_center (X q eps : ℝ) (neg : Bool) (cn cd rn rd qn qd en ed : ℕ)
    (hcert : Real.IsNear X neg cn cd rn rd)
    (hq : q = sfrac neg qn qd) (heps : eps = sfrac false en ed)
    (hcd : Nat.ble 1 cd) (hqd : Nat.ble 1 qd) (hrd : Nat.ble 1 rd) (hed : Nat.ble 1 ed)
    (hsame : (qn.mul cd).beq (cn.mul qd)) (hle : Nat.ble (rn.mul ed) (en.mul rd)) :
    |X - q| ≤ eps := by
  subst hq heps
  simp only [Nat.beq_eq, Nat.ble_eq, Nat.mul_eq] at hsame hle
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hqdR : (0:ℝ) < qd := pos_real_of_ble hqd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hedR : (0:ℝ) < ed := pos_real_of_ble hed
  have hqc : (qn : ℝ) / qd = (cn : ℝ) / cd := by
    rw [div_eq_div_iff hqdR.ne' hcdR.ne']; exact_mod_cast hsame
  have hqcenter : sfrac neg qn qd = sfrac neg cn cd := by unfold sfrac; rw [hqc]
  rw [hqcenter]
  have hcert' : |X - sfrac neg cn cd| ≤ (rn : ℝ) / rd := hcert
  refine hcert'.trans ?_
  rw [show sfrac false en ed = (en : ℝ) / ed from by simp [sfrac], div_le_div_iff₀ hrdR hedR]
  exact_mod_cast hle

/-! ### Sign and margin extraction (the certificate comparisons) -/

/-- A negatively-signed enclosure whose radius stays below its centre magnitude pins `x < 0`. -/
theorem Real.IsNear.neg_val {x : ℝ} {cn cd rn rd : ℕ}
    (h : Real.IsNear x true cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd)
    (hlt : Nat.blt (rn.mul cd) (cn.mul rd)) : x < 0 := by
  simp only [Nat.blt_eq, Nat.mul_eq] at hlt
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hu := h.upper
  rw [sfrac_true_div, neg_div] at hu
  have hcross : (rn : ℝ) * cd < (cn : ℝ) * rd := by exact_mod_cast hlt
  have hlt' : (rn : ℝ) / rd < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ hrdR hcdR]
    linarith
  linarith

/-- A positively-signed enclosure whose radius stays below its centre pins the sign: `0 < x`. -/
theorem Real.IsNear.pos_val {x : ℝ} {cn cd rn rd : ℕ}
    (h : Real.IsNear x false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd)
    (hlt : Nat.blt (rn.mul cd) (cn.mul rd)) : 0 < x := by
  simp only [Nat.blt_eq, Nat.mul_eq] at hlt
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hl := h.lower
  rw [sfrac_false_div] at hl
  have hcross : (rn : ℝ) * cd < (cn : ℝ) * rd := by exact_mod_cast hlt
  have hlt' : (rn : ℝ) / rd < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ hrdR hcdR]
    linarith
  linarith

/-- `‖x‖ > e`: the magnitude lower bound of `x`'s enclosure exceeds the upper bound of `e`'s. -/
theorem norm_gt_of_isNear {x e : ℝ} {nx ne' : Bool} {cnx cdx rnx rdx cne cde rne rde : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (he : Real.IsNear e ne' cne cde rne rde)
    (hcdx : Nat.ble 1 cdx) (hrdx : Nat.ble 1 rdx) (hcde : Nat.ble 1 cde) (hrde : Nat.ble 1 rde)
    (h : Nat.blt ((((numPos ne' cne).mul (rde.mul (cdx.mul rdx))).add
            (rne.mul (cde.mul (cdx.mul rdx)))).add
            (rnx.mul (cde.mul (rde.mul cdx))))
          ((cnx.mul (cde.mul (rde.mul rdx))).add
            ((numNeg ne' cne).mul (rde.mul (cdx.mul rdx))))) :
    ‖x‖ > e := by
  simp only [Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at h
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hcdeR : (0:ℝ) < cde := pos_real_of_ble hcde
  have hrdeR : (0:ℝ) < rde := pos_real_of_ble hrde
  -- |x| ≥ cnx/cdx − rnx/rdx
  have habs : (cnx : ℝ) / cdx - (rnx : ℝ) / rdx ≤ |x| := by
    have h1 : |sfrac nx cnx cdx| - |x - sfrac nx cnx cdx| ≤ |x| := by
      have := abs_sub_abs_le_abs_sub (sfrac nx cnx cdx) x
      have habs2 : |sfrac nx cnx cdx - x| = |x - sfrac nx cnx cdx| := abs_sub_comm _ _
      linarith [this, habs2 ▸ this]
    rw [abs_sfrac] at h1
    have h2 : |x - sfrac nx cnx cdx| ≤ (rnx : ℝ) / rdx := hx
    linarith
  -- e ≤ sfrac ne' cne cde + rne/rde
  have hup := he.upper
  -- cross-multiplied comparison
  have hcR : ((numPos ne' cne * (rde * (cdx * rdx)) + rne * (cde * (cdx * rdx))
        + rnx * (cde * (rde * cdx)) : ℕ) : ℝ)
      < ((cnx * (cde * (rde * rdx)) + numNeg ne' cne * (rde * (cdx * rdx)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcR
  have hkey : sfrac ne' cne cde + (rne : ℝ) / rde < (cnx : ℝ) / cdx - (rnx : ℝ) / rdx := by
    rw [sfrac_eq_parts]
    rw [div_add_div _ _ hcdeR.ne' hrdeR.ne', div_sub_div _ _ hcdxR.ne' hrdxR.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcR]
  rw [Real.norm_eq_abs, gt_iff_lt]
  linarith

/-- `x > e`: the lower bound of `x`'s enclosure exceeds the upper bound of `e`'s. -/
theorem gt_of_isNear {x e : ℝ} {nx ne' : Bool} {cnx cdx rnx rdx cne cde rne rde : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (he : Real.IsNear e ne' cne cde rne rde)
    (hcdx : Nat.ble 1 cdx) (hrdx : Nat.ble 1 rdx) (hcde : Nat.ble 1 cde) (hrde : Nat.ble 1 rde)
    (h : Nat.blt ((((numPos ne' cne).mul (rde.mul (cdx.mul rdx))).add
            (rne.mul (cde.mul (cdx.mul rdx)))).add
          (((numNeg nx cnx).mul (rdx.mul (cde.mul rde))).add
            (rnx.mul (cdx.mul (cde.mul rde)))))
          (((numPos nx cnx).mul (rdx.mul (cde.mul rde))).add
            ((numNeg ne' cne).mul (rde.mul (cdx.mul rdx))))) :
    x > e := by
  simp only [Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at h
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hcdeR : (0:ℝ) < cde := pos_real_of_ble hcde
  have hrdeR : (0:ℝ) < rde := pos_real_of_ble hrde
  have hlo : sfrac nx cnx cdx - (rnx : ℝ) / rdx ≤ x := by
    have h1 : |x - sfrac nx cnx cdx| ≤ (rnx : ℝ) / rdx := hx
    linarith [(abs_le.mp h1).1]
  have hup : e ≤ sfrac ne' cne cde + (rne : ℝ) / rde := he.upper
  have hcR : ((numPos ne' cne * (rde * (cdx * rdx)) + rne * (cde * (cdx * rdx))
        + (numNeg nx cnx * (rdx * (cde * rde)) + rnx * (cdx * (cde * rde))) : ℕ) : ℝ)
      < ((numPos nx cnx * (rdx * (cde * rde))
        + numNeg ne' cne * (rde * (cdx * rdx)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcR
  have hkey : sfrac ne' cne cde + (rne : ℝ) / rde < sfrac nx cnx cdx - (rnx : ℝ) / rdx := by
    rw [sfrac_eq_parts, sfrac_eq_parts,
      div_add_div _ _ hcdeR.ne' hrdeR.ne', div_sub_div _ _ hcdxR.ne' hrdxR.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcR]
  linarith

end Enclosure
