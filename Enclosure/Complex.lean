module

public import Enclosure
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Complex rectangle enclosures: the `Complex.IsNear` predicate

A complex `z` is enclosed by a rectangle: independent `IsNear` enclosures of `z.re` and `z.im`. All
arithmetic on `ℂ` reduces to the real combinators applied componentwise.
-/
@[expose] public section


namespace Enclosure

/-- `z` lies in the rectangle whose real and imaginary sides are the two `IsNear` enclosures. -/
def Complex.IsNear (z : ℂ)
    (reNeg : Bool) (reCn reCd reRn reRd : ℕ)
    (imNeg : Bool) (imCn imCd imRn imRd : ℕ) : Prop :=
  Real.IsNear z.re reNeg reCn reCd reRn reRd ∧
  Real.IsNear z.im imNeg imCn imCd imRn imRd

/-- Real-part accessor. -/
theorem Complex.IsNear.re_isNear {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Real.IsNear z.re reNeg reCn reCd reRn reRd := h.1

/-- Imaginary-part accessor; see `Complex.IsNear.re_isNear`. -/
theorem Complex.IsNear.im_isNear {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Real.IsNear z.im imNeg imCn imCd imRn imRd := h.2

/-- Build a rectangle enclosure of the explicit complex number `⟨re, im⟩` from independent
enclosures of its real and imaginary parts. -/
theorem Complex.IsNear.mk {re im : ℝ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear re reNeg reCn reCd reRn reRd)
    (him : Real.IsNear im imNeg imCn imCd imRn imRd) :
    Complex.IsNear ⟨re, im⟩ reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := ⟨hre, him⟩

/-- Negation. `−z` flips the sign flag of each component; magnitudes and radii are unchanged. -/
theorem Complex.IsNear.neg {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Complex.IsNear (-z) (!reNeg) reCn reCd reRn reRd (!imNeg) imCn imCd imRn imRd := by
  obtain ⟨hre, him⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Complex.neg_re]; exact hre.neg
  · rw [Complex.neg_im]; exact him.neg

/-- Addition. From `IsNear` enclosures of the componentwise sums `z.re+w.re` and `z.im+w.im`,
conclude the rectangle enclosure of `z+w`. -/
theorem Complex.IsNear.add {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re + w.re) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.im + w.im) imN imCn imCd imRn imRd) :
    Complex.IsNear (z + w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.add_re]; exact hre
  · rw [Complex.add_im]; exact him

/-- Subtraction. From `IsNear` enclosures of the componentwise differences `z.re−w.re` and
`z.im−w.im`, conclude the rectangle enclosure of `z−w`. -/
theorem Complex.IsNear.sub {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re - w.re) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.im - w.im) imN imCn imCd imRn imRd) :
    Complex.IsNear (z - w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.sub_re]; exact hre
  · rw [Complex.sub_im]; exact him

/-- Multiplication. From `IsNear` enclosures of the two real combinations
`z.re·w.re − z.im·w.im` and `z.re·w.im + z.im·w.re`, conclude the rectangle enclosure of `z·w`. -/
theorem Complex.IsNear.mul {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re * w.re - z.im * w.im) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.re * w.im + z.im * w.re) imN imCn imCd imRn imRd) :
    Complex.IsNear (z * w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re]; exact hre
  · rw [Complex.mul_im]; exact him

/-! ### Paired-input combine lemmas

The `*LitP` variants consume the paired proofs `h1`/`h2` directly, carrying both components'
literal-output conditions in one application. Sign conditions use the raw `Bool.rec` forms
`numPosC`/`numNegC`. -/

/-- `numPos` in raw `Bool.rec` form (kernel fast path, no `cond`/`Bool.casesOn` wrappers): same
value. -/
def numPosC (neg : Bool) (cn : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) cn 0 neg

/-- `numNeg` in raw `Bool.rec` form; see `numPosC`. -/
def numNegC (neg : Bool) (cn : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) 0 cn neg

theorem numPosC_eq (neg : Bool) (cn : ℕ) : numPosC neg cn = numPos neg cn := by
  cases neg <;> rfl

theorem numNegC_eq (neg : Bool) (cn : ℕ) : numNegC neg cn = numNeg neg cn := by
  cases neg <;> rfl

/-- Paired addition with literal outputs: `Real.IsNear.addLit` on both components, concluded
through `Complex.IsNear.add`. Suffix `r`/`i` = real/imaginary component. -/
theorem Complex.IsNear.addLitP {z w : ℂ}
    {nxr : Bool} {cnxr cdxr rnxr rdxr : ℕ} {nxi : Bool} {cnxi cdxi rnxi rdxi : ℕ}
    {nyr : Bool} {cnyr cdyr rnyr rdyr : ℕ} {nyi : Bool} {cnyi cdyi rnyi rdyi : ℕ}
    {nRr : Bool} {cnRr cnRr' cdRr' rnRr' rdRr' : ℕ}
    {nRi : Bool} {cnRi cnRi' cdRi' rnRi' rdRi' : ℕ}
    (h1 : Complex.IsNear z nxr cnxr cdxr rnxr rdxr nxi cnxi cdxi rnxi rdxi)
    (h2 : Complex.IsNear w nyr cnyr cdyr rnyr rdyr nyi cnyi cdyi rnyi rdyi)
    (hcdxr : Nat.ble (nat_lit 1) cdxr) (hcdyr : Nat.ble (nat_lit 1) cdyr)
    (hrdxr : Nat.ble (nat_lit 1) rdxr) (hrdyr : Nat.ble (nat_lit 1) rdyr)
    (hnumr : Nat.beq
      (((numPosC nRr cnRr).add ((numNegC nxr cnxr).mul cdyr)).add
        ((numNegC nyr cnyr).mul cdxr))
      (((numNegC nRr cnRr).add ((numPosC nxr cnxr).mul cdyr)).add
        ((numPosC nyr cnyr).mul cdxr)))
    (hcdRr' : Nat.ble (nat_lit 1) cdRr') (hrdRr' : Nat.ble (nat_lit 1) rdRr')
    (hcr : Nat.beq (cnRr.mul cdRr') (cnRr'.mul (cdxr.mul cdyr)))
    (hrr : Nat.ble (((rnxr.mul rdyr).add (rnyr.mul rdxr)).mul rdRr')
      (rnRr'.mul (rdxr.mul rdyr)))
    (hcdxi : Nat.ble (nat_lit 1) cdxi) (hcdyi : Nat.ble (nat_lit 1) cdyi)
    (hrdxi : Nat.ble (nat_lit 1) rdxi) (hrdyi : Nat.ble (nat_lit 1) rdyi)
    (hnumi : Nat.beq
      (((numPosC nRi cnRi).add ((numNegC nxi cnxi).mul cdyi)).add
        ((numNegC nyi cnyi).mul cdxi))
      (((numNegC nRi cnRi).add ((numPosC nxi cnxi).mul cdyi)).add
        ((numPosC nyi cnyi).mul cdxi)))
    (hcdRi' : Nat.ble (nat_lit 1) cdRi') (hrdRi' : Nat.ble (nat_lit 1) rdRi')
    (hci : Nat.beq (cnRi.mul cdRi') (cnRi'.mul (cdxi.mul cdyi)))
    (hri : Nat.ble (((rnxi.mul rdyi).add (rnyi.mul rdxi)).mul rdRi')
      (rnRi'.mul (rdxi.mul rdyi))) :
    Complex.IsNear (z + w) nRr cnRr' cdRr' rnRr' rdRr' nRi cnRi' cdRi' rnRi' rdRi' := by
  simp only [numPosC_eq, numNegC_eq] at hnumr hnumi
  exact Complex.IsNear.add
    (Real.IsNear.addLit h1.1 h2.1 hcdxr hcdyr hrdxr hrdyr hnumr hcdRr' hrdRr' hcr hrr)
    (Real.IsNear.addLit h1.2 h2.2 hcdxi hcdyi hrdxi hrdyi hnumi hcdRi' hrdRi' hci hri)

/-- Paired subtraction with literal outputs; see `Complex.IsNear.addLitP`. -/
theorem Complex.IsNear.subLitP {z w : ℂ}
    {nxr : Bool} {cnxr cdxr rnxr rdxr : ℕ} {nxi : Bool} {cnxi cdxi rnxi rdxi : ℕ}
    {nyr : Bool} {cnyr cdyr rnyr rdyr : ℕ} {nyi : Bool} {cnyi cdyi rnyi rdyi : ℕ}
    {nRr : Bool} {cnRr cnRr' cdRr' rnRr' rdRr' : ℕ}
    {nRi : Bool} {cnRi cnRi' cdRi' rnRi' rdRi' : ℕ}
    (h1 : Complex.IsNear z nxr cnxr cdxr rnxr rdxr nxi cnxi cdxi rnxi rdxi)
    (h2 : Complex.IsNear w nyr cnyr cdyr rnyr rdyr nyi cnyi cdyi rnyi rdyi)
    (hcdxr : Nat.ble (nat_lit 1) cdxr) (hcdyr : Nat.ble (nat_lit 1) cdyr)
    (hrdxr : Nat.ble (nat_lit 1) rdxr) (hrdyr : Nat.ble (nat_lit 1) rdyr)
    (hnumr : Nat.beq
      (((numPosC nRr cnRr).add ((numNegC nxr cnxr).mul cdyr)).add
        ((numPosC nyr cnyr).mul cdxr))
      (((numNegC nRr cnRr).add ((numPosC nxr cnxr).mul cdyr)).add
        ((numNegC nyr cnyr).mul cdxr)))
    (hcdRr' : Nat.ble (nat_lit 1) cdRr') (hrdRr' : Nat.ble (nat_lit 1) rdRr')
    (hcr : Nat.beq (cnRr.mul cdRr') (cnRr'.mul (cdxr.mul cdyr)))
    (hrr : Nat.ble (((rnxr.mul rdyr).add (rnyr.mul rdxr)).mul rdRr')
      (rnRr'.mul (rdxr.mul rdyr)))
    (hcdxi : Nat.ble (nat_lit 1) cdxi) (hcdyi : Nat.ble (nat_lit 1) cdyi)
    (hrdxi : Nat.ble (nat_lit 1) rdxi) (hrdyi : Nat.ble (nat_lit 1) rdyi)
    (hnumi : Nat.beq
      (((numPosC nRi cnRi).add ((numNegC nxi cnxi).mul cdyi)).add
        ((numPosC nyi cnyi).mul cdxi))
      (((numNegC nRi cnRi).add ((numPosC nxi cnxi).mul cdyi)).add
        ((numNegC nyi cnyi).mul cdxi)))
    (hcdRi' : Nat.ble (nat_lit 1) cdRi') (hrdRi' : Nat.ble (nat_lit 1) rdRi')
    (hci : Nat.beq (cnRi.mul cdRi') (cnRi'.mul (cdxi.mul cdyi)))
    (hri : Nat.ble (((rnxi.mul rdyi).add (rnyi.mul rdxi)).mul rdRi')
      (rnRi'.mul (rdxi.mul rdyi))) :
    Complex.IsNear (z - w) nRr cnRr' cdRr' rnRr' rdRr' nRi cnRi' cdRi' rnRi' rdRi' := by
  simp only [numPosC_eq, numNegC_eq] at hnumr hnumi
  refine Complex.IsNear.sub
    (Real.IsNear.subLit h1.1 h2.1 hcdxr hcdyr hrdxr hrdyr ?_ hcdRr' hrdRr' hcr hrr)
    (Real.IsNear.subLit h1.2 h2.2 hcdxi hcdyi hrdxi hrdyi ?_ hcdRi' hrdRi' hci hri)
  · cases nyr <;> simpa [numPos, numNeg] using hnumr
  · cases nyi <;> simpa [numPos, numNeg] using hnumi

/-- Rectangle recentre: `Real.IsNear.recentre` on both components in one application. -/
theorem Complex.IsNear.recentre2 {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {rCn' rCd' rRn' rRd' iCn' iCd' iRn' iRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hrcd : Nat.ble (nat_lit 1) rCd) (hrcd' : Nat.ble (nat_lit 1) rCd') (hrrd : Nat.ble
          (nat_lit 1) rRd)
    (hrrd' : Nat.ble (nat_lit 1) rRd')
    (hrfloor : Nat.ble (rCn'.mul rCd) (rCn.mul rCd'))
    (hrrad : Nat.ble
      (((rRn.mul (rCd.mul rCd')).add (((rCn.mul rCd').sub (rCn'.mul rCd)).mul rRd)).mul rRd')
      (rRn'.mul (rRd.mul (rCd.mul rCd'))))
    (hicd : Nat.ble (nat_lit 1) iCd) (hicd' : Nat.ble (nat_lit 1) iCd') (hird : Nat.ble
          (nat_lit 1) iRd)
    (hird' : Nat.ble (nat_lit 1) iRd')
    (hifloor : Nat.ble (iCn'.mul iCd) (iCn.mul iCd'))
    (hirad : Nat.ble
      (((iRn.mul (iCd.mul iCd')).add (((iCn.mul iCd').sub (iCn'.mul iCd)).mul iRd)).mul iRd')
      (iRn'.mul (iRd.mul (iCd.mul iCd')))) :
    Complex.IsNear z rN rCn' rCd' rRn' rRd' iN iCn' iCd' iRn' iRd' :=
  ⟨h.1.recentre hrcd hrcd' hrrd hrrd' hrfloor hrrad,
   h.2.recentre hicd hicd' hird hird' hifloor hirad⟩

/-- One-sided rectangle recentre: round only the real component; imaginary passes through. -/
theorem Complex.IsNear.recentreRe {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {rCn' rCd' rRn' rRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hrcd : Nat.ble (nat_lit 1) rCd) (hrcd' : Nat.ble (nat_lit 1) rCd') (hrrd : Nat.ble
          (nat_lit 1) rRd)
    (hrrd' : Nat.ble (nat_lit 1) rRd')
    (hrfloor : Nat.ble (rCn'.mul rCd) (rCn.mul rCd'))
    (hrrad : Nat.ble
      (((rRn.mul (rCd.mul rCd')).add (((rCn.mul rCd').sub (rCn'.mul rCd)).mul rRd)).mul rRd')
      (rRn'.mul (rRd.mul (rCd.mul rCd')))) :
    Complex.IsNear z rN rCn' rCd' rRn' rRd' iN iCn iCd iRn iRd :=
  ⟨h.1.recentre hrcd hrcd' hrrd hrrd' hrfloor hrrad, h.2⟩

/-- One-sided rectangle recentre for the IMAGINARY component; see `recentreRe`. -/
theorem Complex.IsNear.recentreIm {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {iCn' iCd' iRn' iRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hicd : Nat.ble (nat_lit 1) iCd) (hicd' : Nat.ble (nat_lit 1) iCd') (hird : Nat.ble
          (nat_lit 1) iRd)
    (hird' : Nat.ble (nat_lit 1) iRd')
    (hifloor : Nat.ble (iCn'.mul iCd) (iCn.mul iCd'))
    (hirad : Nat.ble
      (((iRn.mul (iCd.mul iCd')).add (((iCn.mul iCd').sub (iCn'.mul iCd)).mul iRd)).mul iRd')
      (iRn'.mul (iRd.mul (iCd.mul iCd')))) :
    Complex.IsNear z rN rCn rCd rRn rRd iN iCn' iCd' iRn' iRd' :=
  ⟨h.1, h.2.recentre hicd hicd' hird hird' hifloor hirad⟩

/-- Rectangle enclosure of `z` from enclosures of `z.re`, `z.im`; the projection form of `mk`. -/
theorem Complex.IsNear.of_parts {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear z.re reNeg reCn reCd reRn reRd)
    (him : Real.IsNear z.im imNeg imCn imCd imRn imRd) :
    Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := ⟨hre, him⟩

/-- Transport a rectangle enclosure along an equality of the enclosed complex value. -/
theorem Complex.IsNear.of_eq {z w : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (he : z = w) (h : Complex.IsNear w reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := by
  rw [he]; exact h

/-- The real part of a complex inverse as a product: `(z⁻¹).re = z.re · (normSq z)⁻¹`. -/
theorem Complex.inv_re_eq_mul (z : ℂ) : (z⁻¹).re = z.re * (Complex.normSq z)⁻¹ := by
  rw [Complex.inv_re, div_eq_mul_inv]

/-- The imaginary part of a complex inverse as a product: `(z⁻¹).im = (−z.im) · (normSq z)⁻¹`. -/
theorem Complex.inv_im_eq_mul (z : ℂ) : (z⁻¹).im = -z.im * (Complex.normSq z)⁻¹ := by
  rw [Complex.inv_im, div_eq_mul_inv, neg_mul]

/-- `normSq z = z.re·z.re + z.im·z.im`, the form the real combinators assemble. -/
theorem Complex.normSq_eq_mul_add_mul (z : ℂ) :
    Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z

/-! ### Complex finite-sum splitting (the mirror of the real lemmas in `Sums.lean`) -/

/-- Split a complex `Finset.Ico` sum at a midpoint `m ∈ [a,b]`. -/
theorem sum_Ico_consec_complex (f : ℕ → ℂ) (a m b : ℕ)
    (hab : Nat.ble a m = true) (hmb : Nat.ble m b = true) :
    (∑ i ∈ Finset.Ico a b, f i) = (∑ i ∈ Finset.Ico a m, f i) + (∑ i ∈ Finset.Ico m b, f i) :=
  (Finset.sum_Ico_consecutive f (Nat.le_of_ble_eq_true hab) (Nat.le_of_ble_eq_true hmb)).symm

/-- A width-one complex `Finset.Ico` sum (`b = a+1`) is the single term `f a`. -/
theorem sum_Ico_width_one_complex (f : ℕ → ℂ) (a b : ℕ) (h : Nat.beq b (a.add 1) = true) :
    (∑ i ∈ Finset.Ico a b, f i) = f a := by
  have hb : b = a + 1 := Nat.eq_of_beq_eq_true h
  subst hb
  rw [Finset.sum_Ico_succ_top (Nat.le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]

/-- An empty complex `Finset.Ico` sum (`a = b`) is `0`. -/
theorem sum_Ico_empty_complex (f : ℕ → ℂ) (a b : ℕ) (h : Nat.beq a b = true) :
    (∑ i ∈ Finset.Ico a b, f i) = 0 := by
  have hb : a = b := Nat.eq_of_beq_eq_true h
  subst hb
  rw [Finset.Ico_self, Finset.sum_empty]

/-- A complex `Finset.range n` sum as a `Finset.Ico 0 n` sum. -/
theorem sum_range_eq_Ico_complex (f : ℕ → ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i) = (∑ i ∈ Finset.Ico 0 n, f i) := by
  rw [Finset.range_eq_Ico]

/-! ### The complex logarithm, componentwise

For `z = ⟨p/q, r/q⟩` in the right half-plane, the real part of `Complex.log z` is `½·log(normSq z)`
and the imaginary part is `arctan(r/p)`. -/

/-- In the right half-plane `z.arg = arctan(z.im/z.re)`, since `arg ∈ (−π/2, π/2)` there and
`arctan` inverts `tan`. (Mathlib has no direct `arg = arctan` statement.) -/
theorem Complex.arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  have h1 : -(Real.pi / 2) < z.arg := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz)
  have h2 : z.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [← Complex.tan_arg z, Real.arctan_tan h1 h2]

/-- Real part of `Complex.log ⟨p/q, r/q⟩` as `½·log(N/M)` with `N = p²+r²`, `M = q²`. -/
theorem clog_re_eq (p r q N M : ℕ) (hq : Nat.ble (nat_lit 1) q = true)
    (hN : Nat.beq N ((p.mul p).add (r.mul r)) = true) (hM : Nat.beq M (q.mul q) = true) :
    (Complex.log ⟨sfrac false p q, sfrac false r q⟩).re
      = sfrac false (nat_lit 1) (nat_lit 2) * Real.log (sfrac false N M) := by
  obtain rfl := Nat.eq_of_beq_eq_true hN
  obtain rfl := Nat.eq_of_beq_eq_true hM
  have hqR : (0 : ℝ) < q := pos_real_of_ble hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  have hnorm : Complex.normSq ⟨sfrac false p q, sfrac false r q⟩
      = sfrac false ((p.mul p).add (r.mul r)) (q.mul q) := by
    rw [Complex.normSq_mk]
    simp only [sfrac_false_div, Nat.mul_eq, Nat.add_eq]
    push_cast
    field_simp
  rw [Complex.log_re, Complex.norm_def, hnorm, sfrac_false_div, sfrac_false_div,
    Real.log_sqrt (by positivity)]
  push_cast
  ring

/-- Imaginary part of `Complex.log ⟨p/q, r/q⟩` (`p, q > 0`) as `arctan(r/p)` (the `q` cancels). -/
theorem clog_im_eq (p r q : ℕ) (hp : Nat.ble (nat_lit 1) p
      = true) (hq : Nat.ble (nat_lit 1) q = true) :
    (Complex.log ⟨sfrac false p q, sfrac false r q⟩).im = Real.arctan ((r : ℝ) / p) := by
  have hpR : (0 : ℝ) < p := pos_real_of_ble hp
  have hqR : (0 : ℝ) < q := pos_real_of_ble hq
  have hproj_re : (⟨sfrac false p q, sfrac false r q⟩ : ℂ).re = sfrac false p q := rfl
  have hproj_im : (⟨sfrac false p q, sfrac false r q⟩ : ℂ).im = sfrac false r q := rfl
  have hre : (0 : ℝ) < (⟨sfrac false p q, sfrac false r q⟩ : ℂ).re := by
    rw [hproj_re, sfrac_false_div]
    exact div_pos hpR hqR
  rw [Complex.log_im, Complex.arg_eq_arctan_of_re_pos hre, hproj_re, hproj_im,
    sfrac_false_div, sfrac_false_div, div_div_div_cancel_right₀ hqR.ne']

end Enclosure
