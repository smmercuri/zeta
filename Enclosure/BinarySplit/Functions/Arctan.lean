module

public import Enclosure.BinarySplit.Basic
public import Enclosure
public import Enclosure.BinarySplit.Taylor
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# `arctan` via an even/odd split on the ℕ binary-split engine

`arctan(x) = ∑_{k≥0} (-1)^k x^{2k+1}/(2k+1)` (the alternating `artanh`). As with `sin`, the
partial sum splits into positive even- and odd-indexed parts, recombined by a single subtraction:

`∑_{i<2M} (-1)^i x^{2i+1}/(2i+1) = E_M − O_M`, where
`E_M = ∑_{j<M} x^{4j+1}/(4j+1)` and `O_M = ∑_{j<M} x^{4j+3}/(4j+3)`.

The remainder is the alternating-series estimate `≤ x^{4M+1}/(4M+1)` for `0 ≤ x < 1`.
-/
@[expose] public section


namespace BSN
open Enclosure

open Finset

/-- `∏_{k<j} (4k+5) = (∏_{k<j} (4k+1)) · (4j+1)` (telescoping: `4k+5 = 4(k+1)+1`). -/
private theorem prod_arctanEven (j : ℕ) :
    ∏ k ∈ range j, (4 * k + 5) = (∏ k ∈ range j, (4 * k + 1)) * (4 * j + 1) := by
  induction j with
  | zero => simp
  | succ n ih => rw [prod_range_succ, ih, prod_range_succ]; ring

/-- `(∏_{k<j} (4k+7)) · 3 = (∏_{k<j} (4k+3)) · (4j+3)` (telescoping: `4k+7 = 4(k+1)+3`). -/
private theorem prod_arctanOdd (j : ℕ) :
    (∏ k ∈ range j, (4 * k + 7)) * 3 = (∏ k ∈ range j, (4 * k + 3)) * (4 * j + 3) := by
  induction j with
  | zero => rfl
  | succ n ih => rw [prod_range_succ, prod_range_succ, ← ih]; ring

/-! ### Even/odd instantiations and their rational sums -/

/-! ### Taylor remainder: the alternating-series estimate -/

/-- Alternating-series remainder for `arctan`. For `0 ≤ x < 1`, the `2M`-term partial sum is within
the first omitted term `x^{4M+1}/(4M+1)` of `arctan x`. -/
theorem arctan_sub_sum_le (x : ℝ) (M : ℕ) (hx : 0 ≤ x) (hx1 : x < 1) :
    |Real.arctan x - ∑ k ∈ range (2 * M), (-1) ^ k * x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)| ≤
      x ^ (4 * M + 1) / (4 * (M : ℝ) + 1) := by
  set f : ℕ → ℝ := fun n => x ^ (2 * n + 1) / (2 * (n : ℝ) + 1) with hf
  have hx2 : x ^ 2 < 1 := pow_lt_one₀ hx hx1 two_ne_zero
  have hanti : Antitone f := by
    intro a b hab
    simp only [hf]
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact div_le_div₀ (by positivity) (pow_le_pow_of_le_one hx hx1.le (by omega))
      (by positivity) (by linarith)
  have hsum : Summable f := by
    have hg : Summable (fun n : ℕ => x * (x ^ 2) ^ n) :=
      (summable_geometric_of_lt_one (sq_nonneg x) hx2).mul_left x
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hg
    simp only [hf]
    rw [show x * (x ^ 2) ^ n = x ^ (2 * n + 1) by rw [← pow_mul, ← pow_succ']]
    exact div_le_self (by positivity) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have harc : Real.arctan x = ∑' i, (-1) ^ i * f i := by
    rw [← (Real.hasSum_arctan (x := x)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hx]; exact hx1)).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [hf]
    rw [mul_div_assoc]
    push_cast
    ring
  have hbound := alternating_series_error_bound f hanti hsum (2 * M)
  rw [← harc] at hbound
  have hsumeq : (∑ i ∈ range (2 * M), (-1) ^ i * f i)
      = ∑ k ∈ range (2 * M), (-1) ^ k * x ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hf]
    rw [mul_div_assoc]
  have hfeq : f (2 * M) = x ^ (4 * M + 1) / (4 * (M : ℝ) + 1) := by
    simp only [hf]
    rw [show 2 * (2 * M) + 1 = 4 * M + 1 by ring]
    push_cast
    ring
  rw [hsumeq, hfeq] at hbound
  exact hbound

/-! ### Negative arguments (arctan is odd) -/

/-! ### Large arguments (the complementary angle)

An argument `u/v ≥ 1` is recast onto the in-range reciprocal by `arctan(u/v) = π/2 − arctan(v/u)`
(for `u > v`), with the diagonal `arctan(u/u) = π/4` exact. -/

/-- `arctan(u/v) = π/2 − arctan(v/u)` for positive `u`, `v`: the complementary-angle identity. -/
theorem arctan_recip (u v : ℕ) (hu : Nat.ble 1 u = true) (hv : Nat.ble 1 v = true) :
    Real.arctan ((u : ℝ) / v)
        = sfrac false (nat_lit 1) (nat_lit 2) * Real.pi - Real.arctan ((v : ℝ) / u) := by
  have huR : (0 : ℝ) < u := pos_real_of_ble hu
  have hvR : (0 : ℝ) < v := pos_real_of_ble hv
  have hinv : (u : ℝ) / v = ((v : ℝ) / u)⁻¹ := (inv_div _ _).symm
  rw [hinv, Real.arctan_inv_of_pos (div_pos hvR huR), sfrac_false_div]
  push_cast
  ring

/-- `arctan(u/u) = π/4`: the exact diagonal. -/
theorem arctan_diag (u v : ℕ) (hu : Nat.ble 1 u = true) (huv : Nat.beq u v = true) :
    Real.arctan ((u : ℝ) / v) = sfrac false (nat_lit 1) (nat_lit 4) * Real.pi := by
  obtain rfl := Nat.eq_of_beq_eq_true huv
  have huR : (0 : ℝ) < u := pos_real_of_ble hu
  rw [div_self huR.ne', Real.arctan_one, sfrac_false_div]
  push_cast
  ring

/-! ### The binary split for `arctan`. -/

/-- Even arctan sub-series running product: `∏ = (u/v)^(4(i+1)) / (4(i+1)+1)`. -/
theorem arctanEven_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((arctanEvenP u k : ℚ) / (arctanEvenQ v k))
      = (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 1 : ℕ) : ℚ)) := by
  rw [← Finset.range_eq_Ico]
  simp only [arctanEvenP, arctanEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib]
  have hnum : (∏ k ∈ Finset.range (i + 1), ((u ^ 4 * (4 * k + 1) : ℕ) : ℚ))
      = (u : ℚ) ^ (4 * (i + 1)) * ∏ k ∈ Finset.range (i + 1), ((4 * k + 1 : ℕ) : ℚ) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hden : (∏ k ∈ Finset.range (i + 1), ((v ^ 4 * (4 * k + 5) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), ((4 * k + 1 : ℕ) : ℚ))
        * (4 * (i + 1) + 1)) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
    congr 1
    exact_mod_cast prod_arctanEven (i + 1)
  rw [hnum, hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hp1 : (∏ k ∈ Finset.range (i + 1), ((4 * k + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp

/-- Even sub-series value: `u·(Qe+Te)/(v·Qe)` is the even arctan sub-series partial sum. -/
theorem arctanEven_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (arctanEvenP u) (arctanEvenQ v) 0 (M - 1)) :
    ((u : ℚ) * (Q + T) / (v * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 1) / ((v : ℚ) ^ (4 * j + 1) * ((4 * j + 1 : ℕ) : ℚ)) := by
  have hqne : ∀ i, arctanEvenQ v i ≠ 0 := by
    intro i; simp only [arctanEvenQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb :=
        binarySplit_nonzero (p := arctanEvenP u) (q := arctanEvenQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := arctanEvenP u) (q := arctanEvenQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => arctanEven_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 1) / ((v : ℚ) ^ (4 * (i + 1) + 1) * ((4 * (i + 1) + 1 : ℕ) : ℚ))
        = (u : ℚ) / v *
          ((u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 1 : ℕ) : ℚ))) := by
    intro i _
    rw [pow_succ' (u : ℚ), pow_succ' (v : ℚ)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.cast_one, mul_one]
  field_simp
  ring

/-- Odd arctan sub-series running product: `∏ = 3·u^(4(i+1)) / (v^(4(i+1))·(4(i+1)+3))`. -/
theorem arctanOdd_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ k ∈ Finset.Ico 0 (i + 1), ((arctanOddP u k : ℚ) / (arctanOddQ v k))
      = 3 * (u : ℚ) ^ (4 * (i + 1)) / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 3 : ℕ) : ℚ)) := by
  rw [← Finset.range_eq_Ico]
  simp only [arctanOddP, arctanOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  rw [Finset.prod_div_distrib]
  have hnum : (∏ k ∈ Finset.range (i + 1), ((u ^ 4 * (4 * k + 3) : ℕ) : ℚ))
      = (u : ℚ) ^ (4 * (i + 1)) * ∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hden : (∏ k ∈ Finset.range (i + 1), ((v ^ 4 * (4 * k + 7) : ℕ) : ℚ))
      = (v : ℚ) ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ))
        * (4 * (i + 1) + 3)) / 3 := by
    have keyN : (∏ k ∈ Finset.range (i + 1), (v ^ 4 * (4 * k + 7))) * 3
        = v ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), (4 * k + 3)) * (4 * (i + 1) + 3)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, mul_assoc,
        prod_arctanOdd]
    have keyQ : (∏ k ∈ Finset.range (i + 1), ((v ^ 4 * (4 * k + 7) : ℕ) : ℚ)) * 3
        = (v : ℚ) ^ (4 * (i + 1)) * ((∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ))
          * (4 * (i + 1) + 3)) := by exact_mod_cast keyN
    rwa [eq_div_iff (by norm_num : (3 : ℚ) ≠ 0)]
  rw [hnum, hden]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hp1 : (∏ k ∈ Finset.range (i + 1), ((4 * k + 3 : ℕ) : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp

/-- Odd sub-series value: `u³·(Qo+To)/(3·v³·Qo)` is the odd arctan sub-series partial sum. -/
theorem arctanOdd_value (u v M T Q P : ℕ) (hv : v ≠ 0) (hM : 1 ≤ M)
    (h : (T, Q, P) = binarySplit (arctanOddP u) (arctanOddQ v) 0 (M - 1)) :
    ((u : ℚ) ^ 3 * (Q + T) / (3 * v ^ 3 * Q))
      = ∑ j ∈ Finset.range M,
          (u : ℚ) ^ (4 * j + 3) / ((v : ℚ) ^ (4 * j + 3) * ((4 * j + 3 : ℕ) : ℚ)) := by
  have hqne : ∀ i, arctanOddQ v i ≠ 0 := by
    intro i; simp only [arctanOddQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 4 hv) (by positivity)
  have hQ0 : Q ≠ 0 := by
    have hb :=
        binarySplit_nonzero (p := arctanOddP u) (q := arctanOddQ v) (m := 0) (n := M - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec :=
      (binarySplit_spec (p := arctanOddP u) (q := arctanOddQ v) (m := 0) (n := M - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => arctanOdd_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : M = M - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (M - 1),
      (u : ℚ) ^ (4 * (i + 1) + 3) / ((v : ℚ) ^ (4 * (i + 1) + 3) * ((4 * (i + 1) + 3 : ℕ) : ℚ))
        = (u : ℚ) ^ 3 / (3 * v ^ 3) *
          (3 * (u : ℚ) ^ (4 * (i + 1))
                / ((v : ℚ) ^ (4 * (i + 1)) * ((4 * (i + 1) + 3 : ℕ) : ℚ))) := by
    intro i _
    rw [pow_add (u : ℚ) (4 * (i + 1)) 3, pow_add (v : ℚ) (4 * (i + 1)) 3]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add]
  push_cast
  field_simp
  ring

/-- Enclosure for `arctan(u/v)` (`u < v`) via binary splitting. `arctan = E − O`; even value
`u(Qe+Te)/(v·Qe)`, odd `u³(Qo+To)/(3v³·Qo)`; signed centre `±cn/Q`; alternating-series tail. -/
theorem arctan_dyadic_bound (u v M Mm Q D Te Qe Pe To Qo Po : ℕ) (neg : Bool) (cn : ℕ)
    (huv : u.blt v) (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hM : Nat.ble 1 M) (hMm : (Mm.succ).beq M)
    (heven : binarySplit (arctanEvenP u) (arctanEvenQ v) 0 Mm = (Te, Qe, Pe))
    (hodd : binarySplit (arctanOddP u) (arctanOddQ v) 0 Mm = (To, Qo, Po))
    (htail : ((u.pow ((Nat.mul 4 M).succ)).mul (Nat.mul 2 D)).ble
      ((v.pow ((Nat.mul 4 M).succ)).mul ((Nat.mul 4 M).succ)))
    (hr1 : (((numPos neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
        ((numNeg neg cn).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))).blt
      ((((numPos neg cn).succ).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.arctan ((u : ℝ) / v)) neg cn Q 1 D := by
  have hMm' : Mm = M - 1 := by
    have h : Mm + 1 = M := Nat.eq_of_beq_eq_true hMm
    omega
  subst hMm'
  set mp := numPos neg cn with hmp_def
  set mn := numNeg neg cn with hmn_def
  have hvN : 0 < v := pos_of_ble hv
  have hQeN : 0 < Qe := pos_of_ble hQe
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hDN : 0 < D := pos_of_ble hD
  have hvne : v ≠ 0 := hvN.ne'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  have hvalE := arctanEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := arctanOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : (u : ℚ) * (Qe + Te) / (v * Qe) - (u : ℚ) ^ 3 * (Qo + To) / (3 * v ^ 3 * Qo)
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℚ) / v) ^ (2 * i + 1) / (2 * (i : ℚ) + 1) := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) + 1 = 4 * j + 1 := by ring
    have e2 : 2 * (2 * j + 1) + 1 = 4 * j + 3 := by ring
    rw [e1, e2, s1, s2]
    push_cast
    rw [div_pow, div_pow]
    have d1 : (2 : ℚ) * (2 * (j : ℚ)) + 1 = 4 * (j : ℚ) + 1 := by ring
    have d2 : (2 : ℚ) * (2 * (j : ℚ) + 1) + 1 = 4 * (j : ℚ) + 3 := by ring
    rw [d1, d2]
    field_simp
    ring
  set m : ℤ := (mp : ℤ) - (mn : ℤ) with hm
  rw [Real.IsNear, Nat.cast_one]
  have hvform : sfrac neg cn Q = (m : ℝ) / Q := by
    rw [sfrac_eq_parts neg cn Q, ← hmp_def, ← hmn_def, hm]
    push_cast
    ring
  rw [hvform]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at huv htail hQ hr1 hr2
  set De := v * Qe with hDe_def
  set Do := 3 * v ^ 3 * Qo with hDo_def
  set Ne := u * (Qe + Te) with hNe_def
  set No := u ^ 3 * (Qo + To) with hNo_def
  have hDeR : (De : ℝ) = (v : ℝ) * Qe := by rw [hDe_def]; push_cast; ring
  have hDoR : (Do : ℝ) = 3 * (v : ℝ) ^ 3 * Qo := by rw [hDo_def]; push_cast; ring
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
      = ∑ i ∈ Finset.range (2 * M), (-1) ^ i * ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
    have hcast := congrArg (fun r : ℚ => (r : ℝ)) hcombine
    push_cast at hcast
    rw [hNe_def, hDe_def, hNo_def, hDo_def]
    push_cast
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 1 := by rw [div_lt_one hvr]; exact_mod_cast huv
  have harem := arctan_sub_sum_le ((u : ℝ) / v) M hxnn hxlt
  rw [← hvalR] at harem
  have hatail : |Real.arctan ((u : ℝ) / v) - ((Ne : ℝ) / De - (No : ℝ) / Do)| ≤ 1 / (2 * D) := by
    refine harem.trans ?_
    rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have e : (4 * (M : ℝ) + 1) = ((4 * M + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    exact_mod_cast htail
  have hr1' : (m : ℝ) * ((De : ℝ) * Do) ≤ ((Ne : ℝ) * Do - No * De) * Q := by exact_mod_cast hr1z
  have hr2' : ((Ne : ℝ) * Do - No * De) * Q < ((m : ℝ) + 1) * ((De : ℝ) * Do) := by
    exact_mod_cast hr2z
  exact sub_grid_round (Real.arctan ((u : ℝ) / v)) (Ne : ℝ) (De : ℝ) (No : ℝ) (Do : ℝ) m Q D
    hatail hr1' hr2' hDe0 hDo0 hDr hQr hQ

/-! ### Sign-specialized rounding conditions (see `sin_dyadic_bound_f`) -/

/-- `arctan_dyadic_bound` with the centre sign `false` (nonnegative value) baked in. -/
theorem arctan_dyadic_bound_f (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (huv : u.blt v) (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hM : Nat.ble 1 M) (hMm : (Mm.succ).beq M)
    (heven : binarySplit (arctanEvenP u) (arctanEvenQ v) 0 Mm = (Te, Qe, Pe))
    (hodd : binarySplit (arctanOddP u) (arctanOddQ v) 0 Mm = (To, Qo, Po))
    (htail : ((u.pow ((Nat.mul 4 M).succ)).mul (Nat.mul 2 D)).ble
      ((v.pow ((Nat.mul 4 M).succ)).mul ((Nat.mul 4 M).succ)))
    (hr1 : ((cn.mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      (((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q)).blt
      (((cn.succ).mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.arctan ((u : ℝ) / v)) false cn Q 1 D := by
  refine arctan_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn huv hQe hQo hD hv hM hMm
    heven hodd htail ?_ ?_ hQ
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.ble_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr1 ⊢
    omega
  · simp only [numPos, numNeg, if_neg Bool.false_ne_true, Nat.blt_eq, Nat.add_eq,
      Nat.mul_eq, Nat.pow_eq, Nat.zero_mul, Nat.add_zero] at hr2 ⊢
    omega

/-- `arctan_dyadic_bound` with the centre sign `true` (negative value) baked in. -/
theorem arctan_dyadic_bound_t (u v M Mm Q D Te Qe Pe To Qo Po cn : ℕ)
    (huv : u.blt v) (hQe : Nat.ble 1 Qe) (hQo : Nat.ble 1 Qo) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hM : Nat.ble 1 M) (hMm : (Mm.succ).beq M)
    (heven : binarySplit (arctanEvenP u) (arctanEvenQ v) 0 Mm = (Te, Qe, Pe))
    (hodd : binarySplit (arctanOddP u) (arctanOddQ v) 0 Mm = (To, Qo, Po))
    (htail : ((u.pow ((Nat.mul 4 M).succ)).mul (Nat.mul 2 D)).ble
      ((v.pow ((Nat.mul 4 M).succ)).mul ((Nat.mul 4 M).succ)))
    (hr1 : ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q).ble
      ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
        (cn.mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).mul Q).add
        (cn.mul ((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)))).blt
      (((v.mul Qe).mul ((Nat.mul 3 (v.pow 3)).mul Qo)).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.arctan ((u : ℝ) / v)) true cn Q 1 D := by
  refine arctan_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po true cn huv hQe hQo hD hv hM hMm
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

end BSN
