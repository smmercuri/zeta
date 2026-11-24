/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.Core

/-!
# Real interval enclosures: arithmetic combinators

Addition, negation, subtraction and multiplication of `Real.IsNear` enclosures, their
literal-output (`*Lit`) forms with the sign-specialized variants, and `recentre`.
-/
@[expose] public section


namespace Enclosure

/-! ### Addition of enclosures -/

/-- `x + y` is near `±cnR/(cdx·cdy)` with radius `(rnx·rdy + rny·rdx)/(rdx·rdy)`; the result
sign/magnitude is fixed by `hnum`. -/
theorem Real.IsNear.add {x y : ℝ} {nx ny nR : Bool} {cnx cdx rnx rdx cny cdy rny rdy cnR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg ny cny).mul cdx))
                    (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add
                          ((numPos ny cny).mul cdx))) :
    Real.IsNear (x + y) nR cnR (cdx.mul cdy) ((rnx.mul rdy).add (rny.mul rdx)) (rdx.mul rdy) := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hcdyR : (0:ℝ) < cdy := pos_real_of_ble hcdy
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hrdyR : (0:ℝ) < rdy := pos_real_of_ble hrdy
  have eR : (numPos nR cnR : ℝ) + (numNeg nx cnx : ℝ) * cdy + (numNeg ny cny : ℝ) * cdx
          = (numNeg nR cnR : ℝ) + (numPos nx cnx : ℝ) * cdy + (numPos ny cny : ℝ) * cdx := by
    have h' := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.add_eq, Nat.mul_eq] at h'
    exact_mod_cast h'
  have hc : sfrac nR cnR (cdx * cdy) = sfrac nx cnx cdx + sfrac ny cny cdy := by
    rw [sfrac_eq_parts nR cnR, sfrac_eq_parts nx cnx, sfrac_eq_parts ny cny,
      div_add_div _ _ (ne_of_gt hcdxR) (ne_of_gt hcdyR), Nat.cast_mul,
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (cdx : ℝ) * (cdy : ℝ) * eR
  have hrad : ((rnx * rdy + rny * rdx : ℕ) : ℝ) / ((rdx * rdy : ℕ) : ℝ)
            = (rnx : ℝ) / rdx + (rny : ℝ) / rdy := by
    rw [div_add_div _ _ (ne_of_gt hrdxR) (ne_of_gt hrdyR)]
    push_cast
    ring
  simp only [Real.IsNear] at hx hy ⊢
  rw [hc, hrad]
  calc |x + y - (sfrac nx cnx cdx + sfrac ny cny cdy)|
      = |(x - sfrac nx cnx cdx) + (y - sfrac ny cny cdy)| := by congr 1; ring
    _ ≤ |x - sfrac nx cnx cdx| + |y - sfrac ny cny cdy| := abs_add_le _ _
    _ ≤ (rnx : ℝ) / rdx + (rny : ℝ) / rdy := add_le_add hx hy

/-! ### Negation and subtraction -/

/-- Negation. `−x` is near the sign-flipped centre with the same magnitude and radius. -/
theorem Real.IsNear.neg {x : ℝ} {nx : Bool} {cnx cdx rnx rdx : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) : Real.IsNear (-x) (!nx) cnx cdx rnx rdx := by
  simp only [Real.IsNear, sfrac_not] at hx ⊢
  have : -x - -sfrac nx cnx cdx = -(x - sfrac nx cnx cdx) := by ring
  rwa [this, abs_neg]

/-- `x − y`: same shape as `add`, with `hnum` flipping `y`'s sign. -/
theorem Real.IsNear.sub {x y : ℝ} {nx ny nR : Bool} {cnx cdx rnx rdx cny cdy rny rdy cnR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq
        (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg (!ny) cny).mul cdx))
        (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add ((numPos (!ny) cny).mul cdx))) :
    Real.IsNear (x - y) nR cnR (cdx.mul cdy) ((rnx.mul rdy).add (rny.mul rdx)) (rdx.mul rdy) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg hcdx hcdy hrdx hrdy hnum

/-! ### Multiplication of enclosures -/

/-- The interval-multiplication error bound: `|xy − cx·cy| ≤ |cx|·ry + |cy|·rx + rx·ry`. -/
theorem abs_mul_sub {x y cx cy rx ry : ℝ} (hx : |x - cx| ≤ rx) (hy : |y - cy| ≤ ry) :
    |x * y - cx * cy| ≤ |cx| * ry + |cy| * rx + rx * ry := by
  have hrx : 0 ≤ rx := le_trans (abs_nonneg _) hx
  calc |x * y - cx * cy|
      = |cx * (y - cy) + cy * (x - cx) + (x - cx) * (y - cy)| := by congr 1; ring
    _ ≤ |cx * (y - cy) + cy * (x - cx)| + |(x - cx) * (y - cy)| := abs_add_le _ _
    _ ≤ (|cx * (y - cy)| + |cy * (x - cx)|) + |(x - cx) * (y - cy)| := by
        gcongr; exact abs_add_le _ _
    _ = |cx| * |y - cy| + |cy| * |x - cx| + |x - cx| * |y - cy| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |cx| * ry + |cy| * rx + rx * ry := by gcongr

/-- `x · y` is near `±(cnx·cny)/(cdx·cdy)` with the interval-product radius; the sign is `xor`. -/
theorem Real.IsNear.mul {x y : ℝ} {nx ny : Bool} {cnx cdx rnx rdx cny cdy rny rdy : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy) :
    Real.IsNear (x * y) (Bool.xor nx ny) (cnx.mul cny) (cdx.mul cdy)
      (((((cnx.mul rny).mul cdy).mul rdx).add (((cny.mul rnx).mul cdx).mul rdy)).add
        (((rnx.mul rny).mul cdx).mul cdy))
      (((cdx.mul cdy).mul rdx).mul rdy) := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hcdyR : (0:ℝ) < cdy := pos_real_of_ble hcdy
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hrdyR : (0:ℝ) < rdy := pos_real_of_ble hrdy
  have hcdxN : 0 < cdx := pos_of_ble hcdx
  have hcdyN : 0 < cdy := pos_of_ble hcdy
  have hrdxN : 0 < rdx := pos_of_ble hrdx
  have hrdyN : 0 < rdy := pos_of_ble hrdy
  have hrad : (cnx : ℝ) / cdx * ((rny : ℝ) / rdy) + (cny : ℝ) / cdy * ((rnx : ℝ) / rdx)
              + (rnx : ℝ) / rdx * ((rny : ℝ) / rdy)
            = ((cnx * rny * cdy * rdx + cny * rnx * cdx * rdy + rnx * rny * cdx * cdy : ℕ) : ℝ)
              / ((cdx * cdy * rdx * rdy : ℕ) : ℝ) := by
    rw [eq_div_iff (by positivity)]
    push_cast
    field_simp
  simp only [Real.IsNear] at hx hy ⊢
  rw [← sfrac_mul]
  refine le_trans (abs_mul_sub hx hy) ?_
  rw [abs_sfrac, abs_sfrac, hrad]

/-! ### Combinators with literal outputs

Each `*Lit` combinator states its result centre/radius as single numeral literals, tied to the
symbolic result by a `Nat.beq` (centre) and a `Nat.ble` (radius). -/

private theorem ble_one_mul {a b : ℕ} (ha : Nat.ble (nat_lit 1) a
      = true) (hb : Nat.ble (nat_lit 1) b = true) :
    Nat.ble (nat_lit 1) (a.mul b) = true := by
  rw [Nat.ble_eq] at ha hb ⊢
  have h := Nat.mul_le_mul ha hb
  omega

/-- Re-represent an enclosure's centre exactly (`cn/D = cn'/cd'`, cross-multiplied by `hc`) and
widen its radius (`Rn/Rd ≤ rn'/rd'`, by `hr`). -/
theorem Real.IsNear.reprLit {x : ℝ} {n : Bool} {cn D Rn Rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn D Rn Rd)
    (hD : Nat.ble (nat_lit 1) D) (hRd : Nat.ble (nat_lit 1) Rd) (hcd' : Nat.ble (nat_lit 1)
          cd') (hrd' : Nat.ble (nat_lit 1) rd')
    (hc : Nat.beq (cn.mul cd') (cn'.mul D))
    (hr : Nat.ble (Rn.mul rd') (rn'.mul Rd)) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [Nat.ble_eq, Nat.mul_eq] at hr
  have hDr : (0:ℝ) < D := pos_real_of_ble hD
  have hRdr : (0:ℝ) < Rd := pos_real_of_ble hRd
  have hcd'r : (0:ℝ) < cd' := pos_real_of_ble hcd'
  have hrd'r : (0:ℝ) < rd' := pos_real_of_ble hrd'
  have hceq : (cn : ℝ) / D = (cn' : ℝ) / cd' := by
    have hc' := Nat.eq_of_beq_eq_true hc
    simp only [Nat.mul_eq] at hc'
    rw [div_eq_div_iff hDr.ne' hcd'r.ne']; exact_mod_cast hc'
  have hsfrac : sfrac n cn D = sfrac n cn' cd' := by simp only [sfrac, hceq]
  have hrle : (Rn : ℝ) / Rd ≤ (rn' : ℝ) / rd' := by
    rw [div_le_div_iff₀ hRdr hrd'r]; exact_mod_cast hr
  simp only [Real.IsNear] at h ⊢
  rw [← hsfrac]
  exact le_trans h hrle

/-- `add` with literal outputs: centre `cnR'/cdR'` equal to the signed sum, radius `rnR'/rdR'`. -/
theorem Real.IsNear.addLit {x y : ℝ} {nx ny nR : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg ny cny).mul cdx))
                    (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add ((numPos ny cny).mul cdx)))
    (hcdR' : Nat.ble (nat_lit 1) cdR') (hrdR' : Nat.ble (nat_lit 1) rdR')
    (hc : Nat.beq (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)))
    (hr : Nat.ble (((rnx.mul rdy).add (rny.mul rdx)).mul rdR') (rnR'.mul (rdx.mul rdy))) :
    Real.IsNear (x + y) nR cnR' cdR' rnR' rdR' :=
  (hx.add hy hcdx hcdy hrdx hrdy hnum).reprLit
    (ble_one_mul hcdx hcdy) (ble_one_mul hrdx hrdy) hcdR' hrdR' hc hr

/-- Subtraction with literal outputs (the mirror of `addLit`; `hnum` flips `y`'s sign). -/
theorem Real.IsNear.subLit {x y : ℝ} {nx ny nR : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq
        (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg (!ny) cny).mul cdx))
        (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add ((numPos (!ny) cny).mul cdx)))
    (hcdR' : Nat.ble (nat_lit 1) cdR') (hrdR' : Nat.ble (nat_lit 1) rdR')
    (hc : Nat.beq (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)))
    (hr : Nat.ble (((rnx.mul rdy).add (rny.mul rdx)).mul rdR') (rnR'.mul (rdx.mul rdy))) :
    Real.IsNear (x - y) nR cnR' cdR' rnR' rdR' :=
  (hx.sub hy hcdx hcdy hrdx hrdy hnum).reprLit
    (ble_one_mul hcdx hcdy) (ble_one_mul hrdx hrdy) hcdR' hrdR' hc hr

/-! ### Sign-specialized `addLit`/`subLit` variants

One variant per input sign pair, baking the signs in so `hnum` is a plain `Nat.beq` on products. -/

private theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  simpa [Nat.beq_eq_true_eq] using h

/-- The eight sign-independent side conditions of the `addLit`/`subLit` sign variants as one
Boolean, packed as in `recentreOk` (each `a = b` as the pair of differences). -/
def addLitOk (cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cdx)
    (Nat.add (Nat.sub (nat_lit 1) cdy)
    (Nat.add (Nat.sub (nat_lit 1) rdx)
    (Nat.add (Nat.sub (nat_lit 1) rdy)
    (Nat.add (Nat.sub (nat_lit 1) cdR')
    (Nat.add (Nat.sub (nat_lit 1) rdR')
    (Nat.add (Nat.sub (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)))
    (Nat.add (Nat.sub (cnR'.mul (cdx.mul cdy)) (cnR.mul cdR'))
             (Nat.sub (((rnx.mul rdy).add (rny.mul rdx)).mul rdR')
                      (rnR'.mul (rdx.mul rdy)))))))))))
    (nat_lit 0)

/-- Unpack `addLitOk` into the eight conditions the sign variants take. -/
private theorem addLitOk_parts {cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' : ℕ}
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Nat.ble (nat_lit 1) cdx = true ∧ Nat.ble (nat_lit 1) cdy = true ∧
    Nat.ble (nat_lit 1) rdx = true ∧ Nat.ble (nat_lit 1) rdy = true ∧
    Nat.ble (nat_lit 1) cdR' = true ∧ Nat.ble (nat_lit 1) rdR' = true ∧
    Nat.beq (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)) = true ∧
    Nat.ble (((rnx.mul rdy).add (rny.mul rdx)).mul rdR') (rnR'.mul (rdx.mul rdy)) = true := by
  simp only [addLitOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z6, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z7, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z8, z9⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6),
    beq_of_eq (Nat.le_antisymm (Nat.le_of_sub_eq_zero z7) (Nat.le_of_sub_eq_zero z8)),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z9)⟩

/-- The eight side conditions of the `mulLit` sign variants as one Boolean, packed as in
`addLitOk`. -/
def mulLitOk (cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cdx)
    (Nat.add (Nat.sub (nat_lit 1) cdy)
    (Nat.add (Nat.sub (nat_lit 1) rdx)
    (Nat.add (Nat.sub (nat_lit 1) rdy)
    (Nat.add (Nat.sub (nat_lit 1) cdR)
    (Nat.add (Nat.sub (nat_lit 1) rdR)
    (Nat.add (Nat.sub ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)))
    (Nat.add (Nat.sub (cnR.mul (cdx.mul cdy)) ((cnx.mul cny).mul cdR))
             (Nat.sub ((((((cnx.mul rny).mul cdy).mul rdx).add
                         (((cny.mul rnx).mul cdx).mul rdy)).add
                         (((rnx.mul rny).mul cdx).mul cdy)).mul rdR)
                      (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy)))))))))))
    (nat_lit 0)

/-- Unpack `mulLitOk` into the eight conditions the sign variants take. -/
private theorem mulLitOk_parts {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Nat.ble (nat_lit 1) cdx = true ∧ Nat.ble (nat_lit 1) cdy = true ∧
    Nat.ble (nat_lit 1) rdx = true ∧ Nat.ble (nat_lit 1) rdy = true ∧
    Nat.ble (nat_lit 1) cdR = true ∧ Nat.ble (nat_lit 1) rdR = true ∧
    Nat.beq ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)) = true ∧
    Nat.ble ((((((cnx.mul rny).mul cdy).mul rdx).add (((cny.mul rnx).mul cdx).mul rdy)).add
      (((rnx.mul rny).mul cdx).mul cdy)).mul rdR) (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy))
      = true := by
  simp only [mulLitOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z6, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z7, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z8, z9⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6),
    beq_of_eq (Nat.le_antisymm (Nat.le_of_sub_eq_zero z7) (Nat.le_of_sub_eq_zero z8)),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z9)⟩

/-- `x ≥ 0, y ≥ 0` (result sign `+`): `cnR = cnx·cdy + cny·cdx`. -/
theorem Real.IsNear.addLit_ff {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr

/-- `x ≤ 0, y ≤ 0` (result sign `−`): `cnx·cdy + cny·cdx = cnR`. -/
theorem Real.IsNear.addLit_tt {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr

/-- `x ≥ 0, y ≤ 0`, result `+`: `cnR + cny·cdx = cnx·cdy`. -/
theorem Real.IsNear.addLit_ft_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cny.mul cdx)) (cnx.mul cdy))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/-- `x ≥ 0, y ≤ 0`, result `−`: `cny·cdx = cnR + cnx·cdy`. -/
theorem Real.IsNear.addLit_ft_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cny.mul cdx) (cnR.add (cnx.mul cdy)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/-- `x ≤ 0, y ≥ 0`, result `+`: `cnR + cnx·cdy = cny·cdx`. -/
theorem Real.IsNear.addLit_tf_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cnx.mul cdy)) (cny.mul cdx))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/-- `x ≤ 0, y ≥ 0`, result `−`: `cnx·cdy = cnR + cny·cdx`. -/
theorem Real.IsNear.addLit_tf_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cnx.mul cdy) (cnR.add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/-- `x ≥ 0, y ≥ 0`, difference `+`: `cnR + cny·cdx = cnx·cdy`. -/
theorem Real.IsNear.subLit_ff_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cny.mul cdx)) (cnx.mul cdy))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/-- `x ≥ 0, y ≥ 0`, difference `−`: `cny·cdx = cnR + cnx·cdy`. -/
theorem Real.IsNear.subLit_ff_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cny.mul cdx) (cnR.add (cnx.mul cdy)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/-- `x ≥ 0, y ≤ 0` (so `x − y = x + |y|`, result `+`): `cnR = cnx·cdy + cny·cdx`. -/
theorem Real.IsNear.subLit_ft {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr

/-- `x ≤ 0, y ≥ 0` (so `x − y = −(|x| + y)`, result `−`): `cnx·cdy + cny·cdx = cnR`. -/
theorem Real.IsNear.subLit_tf {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr

/-- `x ≤ 0, y ≤ 0`, difference `+` (`|y| ≥ |x|`): `cnR + cnx·cdy = cny·cdx`. -/
theorem Real.IsNear.subLit_tt_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cnx.mul cdy)) (cny.mul cdx))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/-- `x ≤ 0, y ≤ 0`, difference `−` (`|x| ≥ |y|`): `cnx·cdy = cnR + cny·cdx`. -/
theorem Real.IsNear.subLit_tt_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cnx.mul cdy) (cnR.add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/-- `mul` with literal outputs: centre `cnR/cdR` equal to the exact product (sign `xor`), radius
`rnR/rdR`. -/
theorem Real.IsNear.mulLit {x y : ℝ} {nx ny : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hcdR : Nat.ble (nat_lit 1) cdR) (hrdR : Nat.ble (nat_lit 1) rdR)
    (hc : Nat.beq ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)))
    (hr : Nat.ble (((((((cnx.mul rny).mul cdy).mul rdx).add
        (((cny.mul rnx).mul cdx).mul rdy)).add (((rnx.mul rny).mul cdx).mul cdy)).mul rdR))
      (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy))) :
    Real.IsNear (x * y) (Bool.xor nx ny) cnR cdR rnR rdR :=
  (hx.mul hy hcdx hcdy hrdx hrdy).reprLit (ble_one_mul hcdx hcdy)
    (ble_one_mul (ble_one_mul (ble_one_mul hcdx hcdy) hrdx) hrdy) hcdR hrdR hc hr

/-! ### Sign-specialized `mulLit` variants

Four variants (one per input sign pair) baking the result sign in as a literal. -/

/-- `x ≥ 0, y ≥ 0`: result sign `+`. -/
theorem Real.IsNear.mulLit_ff {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) false cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr

/-- `x ≥ 0, y ≤ 0`: result sign `−`. -/
theorem Real.IsNear.mulLit_ft {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) true cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr

/-- `x ≤ 0, y ≥ 0`: result sign `−`. -/
theorem Real.IsNear.mulLit_tf {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) true cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr

/-- `x ≤ 0, y ≤ 0`: result sign `+`. -/
theorem Real.IsNear.mulLit_tt {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) false cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr

/-- Round an enclosure's centre down to a coarser dyadic `cn'/cd' ≤ cn/cd` and inflate the radius by
the drop `δ = cn/cd − cn'/cd'`. -/
theorem Real.IsNear.recentre {x : ℝ} {n : Bool} {cn cd rn rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd)
    (hcd : Nat.ble (nat_lit 1) cd) (hcd' : Nat.ble (nat_lit 1) cd') (hrd : Nat.ble (nat_lit 1)
          rd) (hrd' : Nat.ble (nat_lit 1) rd')
    (hfloor : Nat.ble (cn'.mul cd) (cn.mul cd'))
    (hrad : Nat.ble (((rn.mul (cd.mul cd')).add (((cn.mul cd').sub (cn'.mul cd)).mul rd)).mul rd')
                    (rn'.mul (rd.mul (cd.mul cd')))) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hfloor hrad
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hcd'R : (0:ℝ) < cd' := pos_real_of_ble hcd'
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hrd'R : (0:ℝ) < rd' := pos_real_of_ble hrd'
  have hnn : (0:ℝ) ≤ (cn : ℝ) / cd - (cn' : ℝ) / cd' := by
    have : (cn' : ℝ) / cd' ≤ (cn : ℝ) / cd := by
      rw [div_le_div_iff₀ hcd'R hcdR]; exact_mod_cast hfloor
    linarith
  have hmagdiff : |sfrac n cn cd - sfrac n cn' cd'| = (cn : ℝ) / cd - (cn' : ℝ) / cd' := by
    have hsdiff : sfrac n cn cd - sfrac n cn' cd'
        = (if n then -1 else 1) * ((cn : ℝ) / cd - (cn' : ℝ) / cd') := by
      simp only [sfrac]; ring
    rw [hsdiff, abs_mul]; cases n <;> simp [abs_of_nonneg hnn]
  have hkey : (rn : ℝ) / rd + ((cn : ℝ) / cd - (cn' : ℝ) / cd') ≤ (rn' : ℝ) / rd' := by
    rw [div_sub_div _ _ (ne_of_gt hcdR) (ne_of_gt hcd'R),
      div_add_div _ _ (ne_of_gt hrdR) (by positivity), div_le_div_iff₀ (by positivity) hrd'R]
    have hcast : ((cn : ℝ) * cd' - cd * cn') = ((cn * cd' - cn' * cd : ℕ) : ℝ) := by
      rw [Nat.cast_sub hfloor]; push_cast; ring
    rw [hcast]
    have h2 : (((rn * (cd * cd') + (cn * cd' - cn' * cd) * rd) * rd' : ℕ) : ℝ)
            ≤ ((rn' * (rd * (cd * cd')) : ℕ) : ℝ) := by exact_mod_cast hrad
    push_cast at h2 ⊢
    nlinarith [h2]
  simp only [Real.IsNear] at h ⊢
  calc |x - sfrac n cn' cd'|
      ≤ |x - sfrac n cn cd| + |sfrac n cn cd - sfrac n cn' cd'| := abs_sub_le _ _ _
    _ ≤ (rn : ℝ) / rd + ((cn : ℝ) / cd - (cn' : ℝ) / cd') := by
      rw [hmagdiff]; exact add_le_add h le_rfl
    _ ≤ (rn' : ℝ) / rd' := hkey

/-- `Real.IsNear.recentre` with its six side conditions packed into `recentreOk`, so the kernel
instantiates one short application rather than six arithmetic trees. -/
theorem Real.IsNear.recentre' {x : ℝ} {n : Bool} {cn cd rn rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd)
    (hs : recentreOk cn cd rn rd cn' cd' rn' rd' = true) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [recentreOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, z6⟩ := Nat.add_eq_zero_iff.mp hs
  exact Real.IsNear.recentre h
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2))
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4))
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6))

end Enclosure
