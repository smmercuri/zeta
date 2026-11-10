/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
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
  obtain ⟨hQ0, hspec⟩ := binarySplit_range_spec hqne h
  rw [Finset.sum_congr rfl (fun i _ ↦ sinEven_fold_term u v i hv)] at hspec
  have hNeq : M = M - 1 + 1 := by lia
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
  obtain ⟨hQ0, hspec⟩ := binarySplit_range_spec hqne h
  rw [Finset.sum_congr rfl (fun i _ ↦ sinOdd_fold_term u v i hv)] at hspec
  have hNeq : M = M - 1 + 1 := by lia
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
    lia
  subst hMm'
  have hMpos : 1 ≤ M := Nat.le_of_ble_eq_true hM
  -- `v · Qe · sinEvenQ v (M-1) = v^(4M+1)·(4M+1)!`: the even split's denominator times its next
  -- leaf is `∏_{k<M} sinEvenQ v k = v^(4M)·(4M+1)!`, and the leading `u/v` factor contributes one
  -- more `v`.
  have hbridge : v * (Qe * sinEvenQ v (M - 1))
      = v ^ (2 * (2 * M) + 1) * (2 * (2 * M) + 1).factorial := by
    have hQeprod : Qe = ∏ k ∈ Finset.range (M - 1), sinEvenQ v k := by
      have h := (binarySplit_PQ (p := sinEvenP u) (q := sinEvenQ v) (m := 0) (n := M - 1)).2
      rw [heven, ← Finset.range_eq_Ico] at h; exact h
    rw [hQeprod, ← Finset.prod_range_succ, show M - 1 + 1 = M from by lia]
    simp only [sinEvenQ, Nat.pow_eq, Nat.mul_eq, Nat.add_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul, prod_even_denom,
      show 2 * (2 * M) + 1 = 4 * M + 1 from by ring, pow_succ]
    ring
  have hvN : 0 < v := pos_of_ble hv
  have hQeN : 0 < Qe := pos_of_ble hQe
  have hQoN : 0 < Qo := pos_of_ble hQo
  have hvne : v ≠ 0 := hvN.ne'
  have hvalE := sinEven_value u v M Te Qe Pe hvne hMpos heven.symm
  have hvalO := sinOdd_value u v M To Qo Po hvne hMpos hodd.symm
  have hcombine : (u : ℚ) * (Qe + Te) / (v * Qe) - (u : ℚ) ^ 3 * (Qo + To) / (6 * v ^ 3 * Qo)
      = ∑ i ∈ Finset.range (2 * M),
          (-1) ^ i * ((u : ℚ) / v) ^ (2 * i + 1) / (2 * i + 1).factorial := by
    rw [hvalE, hvalO, sum_range_two_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have s1 : ((-1 : ℚ)) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
    have s2 : ((-1 : ℚ)) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e1 : 2 * (2 * j) + 1 = 4 * j + 1 := by ring
    have e2 : 2 * (2 * j + 1) + 1 = 4 * j + 3 := by ring
    rw [e1, e2, s1, s2, div_pow, div_pow]
    ring
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq] at hu hu2 htail
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hvalR : (((u * (Qe + Te) : ℕ) : ℝ) / ((v * Qe : ℕ) : ℝ)
        - ((u ^ 3 * (Qo + To) : ℕ) : ℝ) / ((6 * v ^ 3 * Qo : ℕ) : ℝ))
      = ∑ i ∈ Finset.range (2 * M),
          (-1) ^ i * ((u : ℝ) / v) ^ (2 * i + 1) / (2 * i + 1).factorial := by
    have hcast := congrArg (fun r : ℚ ↦ (r : ℝ)) hcombine
    push_cast at hcast ⊢
    convert hcast using 2
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((2 * M : ℕ) : ℝ) + 2 := by
    rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  have hsin := sin_sub_sum_le ((u : ℝ) / v) (2 * M) hxnn hxlt
  rw [← hvalR] at hsin
  refine isNear_of_sub_two_frac _ neg cn Q D _ _ _ _ (Nat.mul_pos hvN hQeN)
    (Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos hvN 3)) hQoN) hD hQ hr1 hr2 (hsin.trans ?_)
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

/-! ### Sign-specialized rounding conditions

Variants of `sin_dyadic_bound` with the centre sign baked in as plain `ℕ` comparisons. -/

/-- `sin_dyadic_bound` with the centre sign `false` (nonnegative value) baked in. -/
theorem sin_dyadic_bound_f
    (v : ℕ) (hv : Nat.ble 1 v) (Q D : ℕ) (hD : Nat.ble 1 D) (hQ : (Nat.mul 2 D).ble Q) (M : ℕ)
    (hM : Nat.ble 1 M) (Mm : ℕ) (hMm : (Mm.succ).beq M) (Qe : ℕ) (hQe : Nat.ble 1 Qe) (Qo : ℕ)
    (hQo : Nat.ble 1 Qo) (Te Pe To Po u : ℕ)
    (hu : u.blt (((Nat.mul 2 (Nat.mul 2 M)).add 2).mul v))
    (hu2 : (Nat.mul 2 (u.pow 2)).ble ((((Nat.mul 2 (Nat.mul 2 M)).add 2).pow 2).mul (v.pow 2)))
    (htail : ((Nat.mul 2 (u.pow ((Nat.mul 2 (Nat.mul 2 M)).succ))).mul (Nat.mul 2 D)).ble
      ((v.mul Qe).mul (sinEvenQ v Mm)))
    (cn : ℕ)
    (hr1 : ((cn.mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)).ble
      (((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q) = true)
    (hr2 : ((((u.mul (Qe.add Te)).mul ((Nat.mul 6 (v.pow 3)).mul Qo)).mul Q)).blt
      ((((cn.succ)).mul ((v.mul Qe).mul ((Nat.mul 6 (v.pow 3)).mul Qo))).add
        ((((u.pow 3).mul (Qo.add To)).mul (v.mul Qe)).mul Q)) = true)
    (heven : binarySplit (sinEvenP u) (sinEvenQ v) (nat_lit 0) Mm = (Te, Qe, Pe))
    (hodd : binarySplit (sinOddP u) (sinOddQ v) (nat_lit 0) Mm = (To, Qo, Po)) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) false cn Q 1 D :=
  sin_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po false cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail (roundLo_false hr1) (roundHi_false hr2) hQ

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
    Real.IsNear (Real.sin ((u : ℝ) / v)) true cn Q 1 D :=
  sin_dyadic_bound u v M Mm Q D Te Qe Pe To Qo Po true cn hu hu2 hQe hQo hD hv hM hMm
    heven hodd htail (roundLo_true hr1) (roundHi_true hr2) hQ

/-- An enclosure of `sin(u/v)` with its sign flag flipped encloses `sin(−u/v)`. -/
theorem sin_neg_of_bound (u v : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (hpos : Real.IsNear (Real.sin ((u : ℝ) / v)) neg cn cd rn rd) :
    Real.IsNear (Real.sin ((-(u : ℝ)) / v)) (!neg) cn cd rn rd := by
  rw [Real.IsNear, sfrac_not, neg_div, Real.sin_neg]
  have he : -Real.sin ((u : ℝ) / v) - -sfrac neg cn cd
      = -(Real.sin ((u : ℝ) / v) - sfrac neg cn cd) := by ring
  rw [he, abs_neg]
  exact hpos

end BSN
