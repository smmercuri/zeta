module

public import Enclosure.BinarySplit.Basic
public import Enclosure
public import Enclosure.BinarySplit.Taylor

/-!
# `sin` via an even/odd split on the ℕ binary-split engine

`sin(u/v)`'s alternating Taylor sum splits into positive even- and odd-indexed parts,
recombined by a single subtraction:

`∑_{i<2M} (-1)^i x^{2i+1}/(2i+1)! = E_M − O_M`, where
`E_M = ∑_{j<M} x^{4j+1}/(4j+1)!` and `O_M = ∑_{j<M} x^{4j+3}/(4j+3)!`.
-/
@[expose] public section


namespace BSN
open Enclosure

open Finset

/-- `∏_{k<j} (4k+2)(4k+3)(4k+4)(4k+5) = (4j+1)!`. -/
theorem prod_even_denom (j : ℕ) :
    ∏ k ∈ range j, ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5))
        = (4 * j + 1).factorial := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : 4 * (n + 1) + 1 = (4 * n + 1) + 4 := by ring
    rw [prod_range_succ, ih, e, factorial_add_four]

/-- `∏_{k<j} (4k+4)(4k+5)(4k+6)(4k+7) · 3! = (4j+3)!`. -/
theorem prod_odd_denom (j : ℕ) :
    (∏ k ∈ range j, ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7))) * 6 =
      (4 * j + 3).factorial := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have e : 4 * (n + 1) + 3 = (4 * n + 3) + 4 := by ring
    rw [prod_range_succ, e, factorial_add_four, ← ih]
    ring

/-! ### Even/odd instantiations and their rational sums -/

/-- Even sub-series running product:
`∏_{0≤k≤i}(sinEvenP u/sinEvenQ v) = (u/v)^(4(i+1)) / (4(i+1)+1)!` (combined `u^…/v^…` form). -/
theorem sinEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((sinEvenP u k : ℚ) / (sinEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [sinEvenP, sinEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial := by
    have keyN : ∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5)))
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, prod_even_denom]
    exact_mod_cast keyN
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]

/-- Even sub-series value: `u·(Qe+Te)/(v·Qe)` is the even sub-series partial sum. -/
theorem sinEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (sinEvenP u) (sinEvenQ v) 0 (M - 1)) :
    ((u : ℚ) * (Q + T) / (v * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 1) / ((v : ℚ) ^ (4 * j + 1) * (4 * j + 1).factorial) := by
  have hqne : ∀ i, sinEvenQ v i ≠ 0 := by
    intro i; simp only [sinEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => sinEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 1) / ((v : ℚ) ^ (4 * (i + 1) + 1) * (4 * (i + 1) + 1).factorial)
        = (u : ℚ) / v *
          ((u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 1).factorial)) := by
    intro i _
    rw [pow_succ' (u : ℚ), pow_succ' (v : ℚ)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
  field_simp
  ring

/-- Odd sub-series running product:
`∏_{0≤k≤i}(sinOddP u/sinOddQ v) = 6·u^(4(i+1)) / (v^(4(i+1))·(4(i+1)+3)!)`. -/
theorem sinOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((sinOddP u k : ℚ) / (sinOddQ v k))
      = 6 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial) := by
  rw [← Finset.range_eq_Ico]
  simp only [sinOddP, sinOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hden : (∏ k ∈ Finset.range (i + 1),
      ((v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial / 6 := by
    have keyN : (∏ k ∈ Finset.range (i + 1),
        (v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)))) * 6
        = v ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_odd_denom]
    have keyQ : (∏ k ∈ Finset.range (i + 1),
        ((v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7)) : ℕ) : ℚ)) * 6
        = (v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (6 : ℚ) ≠ 0)]
  rw [hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hf : ((4 * (i + 1) + 3).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  push_cast
  rw [← pow_mul]

/-- Odd sub-series value: `u³·(Qo+To)/(6·v³·Qo)` is the odd sub-series partial sum. -/
theorem sinOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (sinOddP u) (sinOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 3 * (Q + T) / (6 * v ^ 3 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 3) / ((v : ℚ) ^ (4 * j + 3) * (4 * j + 3).factorial) := by
  have hqne : ∀ i, sinOddQ v i ≠ 0 := by
    intro i; simp only [sinOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := sinOddP u) (q := sinOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := sinOddP u) (q := sinOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => sinOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 3) / ((v : ℚ) ^ (4 * (i + 1) + 3) * (4 * (i + 1) + 3).factorial)
        = (u : ℚ) ^ 3 / (6 * v ^ 3) *
          (6 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * (4 * (i + 1) + 3).factorial)) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 3, pow_add (v : ℚ) (4 * (i + 1)) 3]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.factorial_succ, Nat.factorial_zero]
  push_cast
  field_simp
  ring

/-- Enclosure for `sin(u/v)` via binary splitting. `sin = E − O` from two `binarySplit`
certificates; even `u(Qe+Te)/(v·Qe)`, odd `u³(Qo+To)/(6v³·Qo)`; signed centre `±cn/Q`. -/
theorem sin_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : (((numPos neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  have hMpos0 : 1 ≤ M := Nat.le_of_ble_eq_true hM
  -- `v · Qe · sinEvenQ v (M-1) = v^(4M+1)·(4M+1)!`: the even split's denominator times its next
  -- leaf is `∏_{k<M} sinEvenQ v k = v^(4M)·(4M+1)!`, and the leading `u/v` factor contributes one
  -- more `v`.
  have hbridge : v * (Qe * sinEvenQ v (M - 1))
      = v ^ (2 * (2 * M) + 1) * (2 * (2 * M) + 1).factorial := by
    have hQeprod : Qe = ∏ k ∈ Finset.range (M - 1), sinEvenQ v k := by
      have h := (binarySplit_PQ (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1)).2
      rw [heven, ← Finset.range_eq_Ico] at h; exact h
    rw [hQeprod, ← Finset.prod_range_succ, show M - 1 + 1 = M from by omega]
    simp only [sinEvenQ, Nat.pow_eq, Nat.mul_eq, Nat.add_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, prod_even_denom,
      show 2 * (2 * M) + 1 = 4 * M + 1 from by ring, pow_succ]
    ring
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQeN : 0 < Qe := pos_of_ble hQe
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := sinEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := sinOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : (u : ℚ) * (Qe + Te) / (v * Qe) - (u : ℚ) ^ 3 * (Qo + To) / (6 * v ^ 3 * Qo)
      = ∑ i ∈ Finset.range (2 * M),
          (-1) ^ i * ((u : ℚ) / v) ^ (2 * i + 1) / (2 * i + 1).factorial := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) + 1 = 4 * j + 1 := by ring
    have e2 : 2 * (2 * j + 1) + 1 = 4 * j + 3 := by ring
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
  set De := v * Qe with hDe_def
  set Do := 6 * v ^ 3 * Qo with hDo_def
  set Ne := u * (Qe + Te) with hNe_def
  set No := u ^ 3 * (Qo + To) with hNo_def
  have hDeR : (De : ℝ) = (v : ℝ) * Qe := by rw [hDe_def]; push_cast; ring
  have hDoR : (Do : ℝ) = 6 * (v : ℝ) ^ 3 * Qo := by rw [hDo_def]; push_cast; ring
  have hr1z : m * ((De : ℤ) * Do) ≤ ((Ne : ℤ) * Do - (No : ℤ) * De) * Q := by
    have h : (mp : ℤ) * ((De : ℤ) * Do) + (No : ℤ) * De * Q
        ≤ (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do) := by exact_mod_cast hr1
    have e1 : m * ((De : ℤ) * Do) = (mp : ℤ) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by
      rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hr2z : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q < (m + 1) * ((De : ℤ) * Do) := by
    have h : (Ne : ℤ) * Do * Q + (mn : ℤ) * ((De : ℤ) * Do)
        < (mp + 1) * ((De : ℤ) * Do) + (No : ℤ) * De * Q := by exact_mod_cast hr2
    have e1 : (m + 1) * ((De : ℤ) * Do)
        = (mp + 1) * ((De : ℤ) * Do) - (mn : ℤ) * ((De : ℤ) * Do) := by rw [hm]; ring
    have e2 : ((Ne : ℤ) * Do - (No : ℤ) * De) * Q = (Ne : ℤ) * Do * Q - (No : ℤ) * De * Q := by ring
    rw [e1, e2]; linarith
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hDe0 : (0 : ℝ) < De := by rw [hDeR]; positivity
  have hDo0 : (0 : ℝ) < Do := by rw [hDoR]; positivity
  have hvalR : ((Ne : ℝ) / De - (No : ℝ) / Do)
      = ∑ i ∈ Finset.range (2 * M),
          (-1) ^ i * ((u : ℝ) / v) ^ (2 * i + 1) / (2 * i + 1).factorial := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDe_def, hNo_def, hDo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((2 * M : ℕ) : ℝ) + 2 := by
    rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hsin := sin_sub_sum_le ((u : ℝ) / v) (2 * M) hxnn hxlt
  rw [← hvalR] at hsin
  have hsin' : |Real.sin ((u : ℝ) / v) - ((Ne : ℝ) / De - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine hsin.trans ?_
    have hA2 : ((u : ℝ) / v) ^ (2 * (2 * M) + 1) / (2 * (2 * M) + 1).factorial * 2
        ≤ 1 / (2 * D) := by
      rw [div_pow, div_div, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have e : (u : ℝ) ^ (2 * (2 * M) + 1) * 2 * (2 * D)
          = 2 * (u : ℝ) ^ (2 * (2 * M) + 1) * (2 * D) := by ring
      rw [e]
      have htR : 2 * (u : ℝ) ^ (2 * (2 * M) + 1) * (2 * D)
          ≤ (v : ℝ) * (Qe : ℝ) * (sinEvenQ v (M - 1) : ℝ) := by exact_mod_cast htail
      have hbR : (v : ℝ) * (Qe : ℝ) * (sinEvenQ v (M - 1) : ℝ)
          = (v : ℝ) ^ (2 * (2 * M) + 1) * ((2 * (2 * M) + 1).factorial : ℝ) := by
        have hb : v * Qe * sinEvenQ v (M - 1)
            = v ^ (2 * (2 * M) + 1) * (2 * (2 * M) + 1).factorial := by
          rw [Nat.mul_assoc]; exact hbridge
        exact_mod_cast hb
      exact le_of_le_of_eq htR hbR
    refine le_trans ?_ hA2
    gcongr
    exact geo_factor_le _ _ (by positivity) (by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      exact_mod_cast hu2)
  have hr1' : (m : ℝ) * ((De : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * De) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * De) * Q < ((m : ℝ) + 1) * ((De : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.sin ((u : ℝ) / v)) (Ne : ℝ) (De : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hsin' hr1' hr2' hDe0 hDo0 hDr hQr hQ

/-! ### Sign-specialized rounding conditions

Variants of `sin_dyadic_bound` with the centre sign baked in as plain `ℕ` comparisons. -/

/-- `sin_dyadic_bound` with the centre sign `false` (nonnegative value) baked in. -/
theorem sin_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : ((cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      (((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q)).blt
      ((((cn.succ)).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) false cn Q 1 D := by
  refine sin_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega

/-- `sin_dyadic_bound` with the centre sign `true` (negative value) baked in. -/
theorem sin_dyadic_bound_t (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v) (hM :
          Nat.ble 1 M)
    (hMm : (Mm.succ).beq M)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (hr1 : (((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        (cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q).add
        (cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo)))).blt
      ((((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) true cn Q 1 D := by
  refine sin_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po true cn hu hu2 hQe hQo hD hv hM hMm
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

/-- Negative fraction via `Real.sin_neg`: the value negates, so the centre's sign flag flips. -/
theorem sin_neg_of_bound (u v : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (hpos : Real.IsNear (Real.sin ((u : ℝ) / v)) neg cn cd rn rd) :
    Real.IsNear (Real.sin ((-(u : ℝ)) / v)) (!neg) cn cd rn rd := by
  rw [Real.IsNear, sfrac_not, neg_div, Real.sin_neg]
  have he : -Real.sin ((u : ℝ) / v) - -sfrac neg cn cd
      = -(Real.sin ((u : ℝ) / v) - sfrac neg cn cd) := by ring
  rw [he, abs_neg]
  exact hpos

end BSN
