module

public import Enclosure.BinarySplit.Basic
public import Enclosure
public import Enclosure.BinarySplit.Taylor

/-!
# `cos` via an even/odd split on the ℕ binary-split engine

Like `sin`, `cos(u/v)`'s alternating Taylor sum splits into even- and odd-indexed parts,
recombined by a single subtraction:

`∑_{i<2M} (-1)^i x^{2i}/(2i)! = E_M − O_M`, where
`E_M = ∑_{j<M} x^{4j}/(4j)!` and `O_M = ∑_{j<M} x^{4j+2}/(4j+2)!`.
-/
@[expose] public section


namespace BSN
open Enclosure

open Finset

/-- `∏_{k<j} (4k+1)(4k+2)(4k+3)(4k+4) = (4j)!`. -/
theorem prod_cosEven_denom (j : ℕ) :
    ∏ k ∈ range j, ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)) = (4 * j).factorial := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : 4 * (n + 1) = (4 * n) + 4 := by ring
    rw [prod_range_succ, ih, e, factorial_add_four]

/-- `∏_{k<j} (4k+3)(4k+4)(4k+5)(4k+6) · 2 = (4j+2)!`. -/
theorem prod_cosOdd_denom (j : ℕ) :
    (∏ k ∈ range j, ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6))) * 2 =
      (4 * j + 2).factorial := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have e : 4 * (n + 1) + 2 = (4 * n + 2) + 4 := by ring
    rw [prod_range_succ, e, factorial_add_four, ← ih]
    ring

/-! ### Even/odd instantiations and their rational sums -/

/-- Even cos sub-series running product:
`∏_{0≤k≤i}(cosEvenP u/cosEvenQ v) = (u/v)^(4(i+1))/(4(i+1))!`. -/
theorem cosEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((cosEvenP u k : ℚ) / (cosEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1)).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [cosEvenP, cosEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1)).factorial := by
    have keyN : ∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4)))
        = v ^ (4 * (i + 1)) * (4 * (i + 1)).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
        prod_cosEven_denom]
    exact_mod_cast keyN
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1)).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]

/-- Even sub-series value: `(Qe+Te)/Qe` is the even sub-series partial sum (leading factor `1`). -/
theorem cosEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (cosEvenP u) (cosEvenQ v) 0 (M - 1)) :
    (((Q + T : ℕ) : ℚ) / Q)
      = ∑ j ∈ Finset.range M, (u : ℚ) ^ (4 * j) / ((v : ℚ) ^ (4 * j) * (4 * j).factorial) := by
  have hqne : ∀ i, cosEvenQ v i ≠ 0 := by
    intro i; simp only [cosEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => cosEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ', hspec]
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  push_cast
  field_simp
  ring

/-- Odd cos sub-series running product: `∏ = 2·u^(4(i+1)) / (v^(4(i+1))·(4(i+1)+2)!)`. -/
theorem cosOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((cosOddP u k : ℚ) / (cosOddQ v k))
      = 2 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [cosOddP, cosOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial / 2 := by
    have keyN : (∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)))) * 2
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_cosOdd_denom]
    have keyQ : (∏ k ∈ Finset.range (i + 1),
        ((v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6)) : ℕ) : ℚ)) * 2
        = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)]
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]

/-- Odd sub-series value: `u²·(Qo+To)/(2·v²·Qo)` is the odd sub-series partial sum. -/
theorem cosOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (cosOddP u) (cosOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 2 * (Q + T) / (2 * v ^ 2 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 2) / ((v : ℚ) ^ (4 * j + 2) * (4 * j + 2).factorial) := by
  have hqne : ∀ i, cosOddQ v i ≠ 0 := by
    intro i; simp only [cosOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := cosOddP u) (q := cosOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := cosOddP u) (q := cosOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => cosOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 2) / ((v : ℚ) ^ (4 * (i + 1) + 2) * (4 * (i + 1) + 2).factorial)
        = (u : ℚ) ^ 2 / (2 * v ^ 2) *
          (2 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 2).factorial)) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 2, pow_add (v : ℚ) (4 * (i + 1)) 2]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_two]
  push_cast
  field_simp
  ring

/-- Enclosure for `cos(u/v)` via binary splitting. `cos = E − O`; even value
`(Qe+Te)/Qe`, odd value `u²(Qo+To)/(2v²·Qo)`; signed centre `±cn/Q`. -/
theorem cos_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    -- the tail factor `v^(4M)·(4M)!` is expressed as `Qe · cosEvenQ v Mm` (`Qe` is the even split's
    -- own denominator `v^(4Mm)·(4Mm)!`, already balanced-verified), so the kernel never reduces
    -- `Nat.factorial (4M)`.
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : (((numPos neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)).ble
      ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  have hMpos0 : 1 ≤ M := Nat.le_of_ble_eq_true hM
  -- `Qe · cosEvenQ v (M-1) = v^(4M)·(4M)!`: the even split's denominator times its next leaf is the
  -- full product `∏_{k<M} cosEvenQ v k`, whose closed form is `v^(4M)·(4M)!`
  -- (`prod_cosEven_denom`).
  have hbridge : Qe * cosEvenQ v (M - 1) = v ^ (2 * (2 * M)) * (2 * (2 * M)).factorial := by
    have hQeprod : Qe = ∏ k ∈ Finset.range (M - 1), cosEvenQ v k := by
      have h := (binarySplit_PQ (p := cosEvenP u) (q := cosEvenQ v) (m := 0) (n := M - 1)).2
      rw [heven, ← Finset.range_eq_Ico] at h; exact h
    rw [hQeprod, ← Finset.prod_range_succ, show M - 1 + 1 = M from by omega]
    simp only [cosEvenQ, Nat.pow_eq, Nat.mul_eq, Nat.add_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
      prod_cosEven_denom, show 4 * M = 2 * (2 * M) from by ring]
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := cosEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := cosOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : ((Qe + Te : ℕ) : ℚ) / Qe - (u : ℚ) ^ 2 * (Qo + To) / (2 * v ^ 2 * Qo)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℚ) / v) ^ (2 * i) / (2 * i).factorial := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) = 4 * j := by ring
    have e2 : 2 * (2 * j + 1) = 4 * j + 2 := by ring
    rw [e1, e2, s1, s2, div_pow, div_pow]
    ring
  set m : ℤ := (mp : ℤ) - (mn : ℤ) with hm
  rw [Real.IsNear, Nat.cast_one]
  have hvform : sfrac neg cn Q = (m : ℝ) / Q := by
    rw [sfrac_eq_parts neg cn Q, ← hmp_def, ← hmn_def, hm]
    push_cast
    ring
  rw [hvform]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at hu hu2 htail hQ hr1 hr2
  push_cast at hcombine
  set Do := 2 * v ^ 2 * Qo with hDo_def
  set Ne := Qe + Te with hNe_def
  set No := u ^ 2 * (Qo + To) with hNo_def
  have hDoR : (Do : ℝ) = 2 * (v : ℝ) ^ 2 * Qo := by rw [hDo_def]; push_cast; ring
  have hr1z : m * ((Qe : ℤ) * Do) ≤ ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q := by
    have h : (mp : ℤ) * ((Qe : ℤ) * Do) + (No : ℤ) * Qe * Q
        ≤ (Ne : ℤ) * Do * Q + (mn : ℤ) * ((Qe : ℤ) * Do) := by exact_mod_cast hr1
    have e1 : m * ((Qe : ℤ) * Do) = (mp : ℤ) * ((Qe : ℤ) * Do) - (mn : ℤ) * ((Qe : ℤ) * Do) := by
      rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * Qe * Q := by ring
    rw [e1, e2]; linarith
  have hr2z : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q < (m + 1) * ((Qe : ℤ) * Do) := by
    have h : (Ne : ℤ) * Do * Q + (mn : ℤ) * ((Qe : ℤ) * Do)
        < (mp + 1) * ((Qe : ℤ) * Do) + (No : ℤ) * Qe * Q := by exact_mod_cast hr2
    have e1 : (m + 1) * ((Qe : ℤ) * Do)
        = (mp + 1) * ((Qe : ℤ) * Do) - (mn : ℤ) * ((Qe : ℤ) * Do) := by rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * Qe) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * Qe * Q := by ring
    rw [e1, e2]; linarith
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQe0 : (0 : ℝ) < Qe := pos_real_of_ble hQe
  have hDo0 : (0 : ℝ) < Do := by rw [hDoR]; positivity
  have hvalR : ((Ne : ℝ) / Qe - (No : ℝ) / Do)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℝ) / v) ^ (2 * i) / (2 * i).factorial := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDo_def, hNo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((2 * M : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hcos := cos_sub_sum_le ((u : ℝ) / v) (2 * M) hxnn hxlt
  rw [← hvalR] at hcos
  have hcos' : |Real.cos ((u : ℝ) / v) - ((Ne : ℝ) / Qe - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine hcos.trans ?_
    have hA2 : ((u : ℝ) / v) ^ (2 * (2 * M)) / (2 * (2 * M)).factorial * 2 ≤ 1 / (2 * D) := by
      rw [div_pow, div_div, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have e : (u : ℝ) ^ (2 * (2 * M)) * 2 * (2 * D)
          = 2 * (u : ℝ) ^ (2 * (2 * M)) * (2 * D) := by ring
      rw [e]
      have htR : 2 * (u : ℝ) ^ (2 * (2 * M)) * (2 * D) ≤ (Qe : ℝ) * (cosEvenQ v (M - 1) : ℝ) := by
        exact_mod_cast htail
      have hbR : (Qe : ℝ) * (cosEvenQ v (M - 1) : ℝ)
          = (v : ℝ) ^ (2 * (2 * M)) * ((2 * (2 * M)).factorial : ℝ) := by exact_mod_cast hbridge
      exact le_of_le_of_eq htR hbR
    refine le_trans ?_ hA2
    gcongr
    exact geo_factor_le _ _ (by positivity) (by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      exact_mod_cast hu2)
  have hr1' : (m : ℝ) * ((Qe : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * Qe) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * Qe) * Q < ((m : ℝ) + 1) * ((Qe : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.cos ((u : ℝ) / v)) (Ne : ℝ) (Qe : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hcos' hr1' hr2' hQe0 hDo0 hDr hQr hQ

/-! ### Sign-specialized rounding conditions (see `sin_dyadic_bound_f`) -/

/-- `cos_dyadic_bound` with the centre sign `false` (nonnegative value) baked in. -/
theorem cos_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : ((cn.mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)).ble
      (((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q)).blt
      (((cn.succ).mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo))).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) false cn Q 1 D := by
  refine cos_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega

/-- `cos_dyadic_bound` with the centre sign `true` (negative value) baked in. -/
theorem cos_dyadic_bound_t (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).succ).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).succ).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (cosEvenP u) (cosEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (cosOddP u) (cosOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow (Nat.mul 2 (Nat.mul 2 M)))).mul (Nat.mul 2 D)).ble
      (Qe.mul (cosEvenQ v Mm)))
    (hr1 : ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q).ble
      ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        (cn.mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))) = true)
    (hr2 : ((((Qe.add Te).mul ((Nat.mul 2 (v.pow 2)).mul Qo)).mul Q).add
        (cn.mul (Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)))).blt
      ((Qe.mul ((Nat.mul 2 (v.pow 2)).mul Qo)).add
        ((((u.pow 2).mul (Qo.add To)).mul Qe).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) true cn Q 1 D := by
  refine cos_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po true cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
      Nat.zero_mul, Nat.zero_add] at hr1 ⊢
    omega
  · have hp : numPos true cn = 0 := rfl
    have hn : numNeg true cn = cn := rfl
    simp only [hp, hn, Nat.blt_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.one_mul] at hr2 ⊢
    omega

/-- Negative fraction via `Real.cos_neg`: `cos` is even, so the enclosure is unchanged. -/
theorem cos_neg_of_bound (u v : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (h : Real.IsNear (Real.cos ((u : ℝ) / v)) neg cn cd rn rd) :
    Real.IsNear (Real.cos ((-(u : ℝ)) / v)) neg cn cd rn rd := by
  rw [Real.IsNear, neg_div, Real.cos_neg]; exact h

end BSN
