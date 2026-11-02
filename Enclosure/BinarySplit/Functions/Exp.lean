module

public import Enclosure.BinarySplit.Basic
public import Enclosure
public import Enclosure.BinarySplit.Taylor

/-!
# `exp` on the ℕ binary-split engine

`exp(u/v) = ∑_i (u/v)^i/i!` is a positive series, computed as a single ℕ binary split
(`a = b = 1`, `p = u`, `q = v·(j+1)`). Negatives go through `exp(-x) = 1/exp(x)`; large
arguments through the halving identity `exp(u) = (exp(u/2ᵏ))^(2ᵏ)`.
-/
@[expose] public section


namespace BSN
open Enclosure

open Finset

/-- `exp(u/v)`: `p = u`, `q = v·(j+1)`, `a = b = 1`. -/
def expNatP (u : ℕ) : ℕ → ℕ := fun _ => u
def expNatQ (v : ℕ) : ℕ → ℕ := fun j => Nat.mul v (Nat.succ j)

/-- Range-reduced dyadic bound for `exp` of a large integer via halving: with `n = 2ᵏ` and
`exp(u) = (exp(u/n))ⁿ`, an inner bound `|exp(u/n) − p/Q| ≤ 1/D0` gives `|exp u − P/R| ≤ 1/D`
where `P/R = (p/Q)ⁿ`. -/
theorem exp_halving_dyadic_bound (u n p Q D0 D P R : ℕ)
    (hn : Nat.ble 1 n) (hQ : Nat.ble 1 Q) (hD0 : Nat.ble 1 D0) (hD : Nat.ble 1 D)
    (hP : P.beq (p.pow n)) (hR : R.beq (Q.pow n))
    (hprop : ((n.mul (((p.mul D0).add Q).pow (n.sub 1))).mul D).ble
      (((Q.mul D0).pow (n.sub 1)).mul D0))
    (hinner : Real.IsNear (Real.exp ((u : ℝ) / n)) false p Q 1 D0) :
    Real.IsNear (Real.exp (u : ℝ)) false P R 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hinner ⊢
  simp only [Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
    Nat.sub_eq] at hP hR hprop
  subst hP hR
  have hnN : 0 < n := pos_of_ble hn
  have hQN : 0 < Q := pos_of_ble hQ
  have hD0N : 0 < D0 := pos_of_ble hD0
  have hnR : (0 : ℝ) < n := pos_real_of_ble hn
  have hQR : (0 : ℝ) < Q := pos_real_of_ble hQ
  have hD0R : (0 : ℝ) < D0 := pos_real_of_ble hD0
  have hDR : (0 : ℝ) < D := pos_real_of_ble hD
  set a : ℝ := (p : ℝ) / Q with ha_def
  set b : ℝ := Real.exp ((u : ℝ) / n) with hb_def
  set ε : ℝ := 1 / (D0 : ℝ) with hε_def
  have ha0 : 0 ≤ a := by rw [ha_def]; positivity
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hε0 : 0 ≤ ε := by rw [hε_def]; positivity
  have hbM : b ≤ a + ε := by
    have := (abs_le.mp hinner).2; linarith
  -- `exp u = bⁿ`
  have hue : (u : ℝ) = (n : ℝ) * ((u : ℝ) / n) := by field_simp
  have hexp : Real.exp u = b ^ n := by rw [hb_def, ← Real.exp_nat_mul, ← hue]
  -- `P/R = aⁿ`
  have hPR : ((p ^ n : ℕ) : ℝ) / ((Q ^ n : ℕ) : ℝ) = a ^ n := by
    rw [Nat.cast_pow, Nat.cast_pow, ha_def, div_pow]
  rw [hexp, hPR]
  -- propagation: `n · (a+ε)^(n-1) · ε ≤ 1/D`
  have hMeq : a + ε = (((p * D0 + Q : ℕ) : ℝ)) / ((Q * D0 : ℕ) : ℝ) := by
    rw [ha_def, hε_def]; push_cast; field_simp
  have hpras : (n : ℝ) * (a + ε) ^ (n - 1) * ε ≤ 1 / D := by
    have key : (n : ℝ) * (a + ε) ^ (n - 1) * ε
        = ((n * (p * D0 + Q) ^ (n - 1) : ℕ) : ℝ) / (((Q * D0) ^ (n - 1) * D0 : ℕ) : ℝ) := by
      rw [hMeq, hε_def, div_pow]; push_cast; field_simp
    rw [key, div_le_div_iff₀ (by positivity) hDR, one_mul]
    exact_mod_cast hprop
  calc |b ^ n - a ^ n|
      ≤ (n : ℝ) * (a + ε) ^ (n - 1) * |b - a| :=
        abs_pow_sub_pow_le ha0 hb0 (by linarith) hbM
    _ ≤ (n : ℝ) * (a + ε) ^ (n - 1) * ε :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ 1 / D := hpras

/-- Reciprocal enclosure for `exp (-x)` (`x ≥ 0`) via `exp(-x) = 1/exp(x)`: from a positive inner
enclosure `hpos` of `exp x`, re-round the reciprocal to the dyadic `p'/Q'`. -/
theorem exp_neg_recip_bound (Q D0 Q' D p p' : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hp : Nat.ble 1 p) (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q')
    (hD : Nat.ble 1 D) (hD0 : Nat.ble 1 D0) (hQp : Q.ble p)
    (hr1 : (p'.mul p).ble (Q'.mul Q)) (hr2 : (Q'.mul Q).blt ((p'.succ).mul p))
    (hcomb : (D.mul (Q'.add D0)).ble (D0.mul Q'))
    (hpos : Real.IsNear (Real.exp x) false p Q 1 D0) :
    Real.IsNear (Real.exp (-x)) false p' Q' 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hpos ⊢
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hQp hr1 hr2 hcomb
  have hpR : (0 : ℝ) < p := pos_real_of_ble hp
  have hQR : (0 : ℝ) < Q := pos_real_of_ble hQ
  have hQ'R : (0 : ℝ) < Q' := pos_real_of_ble hQ'
  have hDR : (0 : ℝ) < D := pos_real_of_ble hD
  have hD0R : (0 : ℝ) < D0 := pos_real_of_ble hD0
  set a : ℝ := Real.exp x with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact Real.one_le_exp hx
  have ha0 : 0 < a := by linarith
  have hane : a ≠ 0 := ne_of_gt ha0
  set b : ℝ := (p : ℝ) / Q with hbdef
  have hb1 : 1 ≤ b := by rw [hbdef, le_div_iff₀ hQR, one_mul]; exact_mod_cast hQp
  have hb0 : 0 < b := by linarith
  have hbne : b ≠ 0 := ne_of_gt hb0
  have hexpneg : Real.exp (-x) = 1 / a := by rw [Real.exp_neg, one_div, ha]
  rw [hexpneg]
  have hab : |1 / a - 1 / b| ≤ 1 / D0 := by
    have heq : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
    rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < a * b),
      div_le_iff₀ (by positivity : (0 : ℝ) < a * b)]
    calc |b - a| = |a - b| := abs_sub_comm b a
      _ ≤ 1 / D0 := hpos
      _ ≤ 1 / D0 * (a * b) := le_mul_of_one_le_right (by positivity) (by nlinarith)
  have hterm2 : |1 / b - (p' : ℝ) / Q'| ≤ 1 / Q' := by
    have h1b : 1 / b = (Q : ℝ) / p := by rw [hbdef, one_div_div]
    rw [h1b]
    have e1 : (p' : ℝ) / Q' ≤ (Q : ℝ) / p := by
      rw [div_le_div_iff₀ hQ'R hpR, mul_comm (Q : ℝ)]; exact_mod_cast hr1
    have e2 : (Q : ℝ) / p < (p' : ℝ) / Q' + 1 / Q' := by
      rw [← add_div, div_lt_div_iff₀ hpR hQ'R, mul_comm (Q : ℝ)]; exact_mod_cast hr2
    rw [abs_of_nonneg (by linarith)]; linarith
  calc |1 / a - (p' : ℝ) / Q'|
      ≤ |1 / a - 1 / b| + |1 / b - (p' : ℝ) / Q'| := abs_sub_le _ _ _
    _ ≤ 1 / D0 + 1 / Q' := add_le_add hab hterm2
    _ ≤ 1 / D := by
        have hc : (D : ℝ) * (Q' + D0) ≤ D0 * Q' := by exact_mod_cast hcomb
        rw [div_add_div _ _ (ne_of_gt hD0R) (ne_of_gt hQ'R), one_mul, mul_one,
          div_le_div_iff₀ (by positivity) hDR, one_mul]
        nlinarith

/-- Enclosure for `exp` of a negative fraction `-u/v` (`v ≥ 1`): the fraction wrapper of
`exp_neg_recip_bound` with `x = u/v`. -/
theorem exp_neg_bound (u v Q D0 Q' D p p' : ℕ)
    (hp : Nat.ble 1 p) (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q')
    (hD : Nat.ble 1 D) (hD0 : Nat.ble 1 D0) (hQp : Q.ble p)
    (hr1 : (p'.mul p).ble (Q'.mul Q)) (hr2 : (Q'.mul Q).blt ((p'.succ).mul p))
    (hcomb : (D.mul (Q'.add D0)).ble (D0.mul Q'))
    (hpos : Real.IsNear (Real.exp ((u : ℝ) / v)) false p Q 1 D0) :
    Real.IsNear (Real.exp ((-(u : ℝ)) / v)) false p' Q' 1 D := by
  rw [neg_div]
  exact exp_neg_recip_bound Q D0 Q' D p p' ((u : ℝ) / v) (by positivity)
    hp hQ hQ' hD hD0 hQp hr1 hr2 hcomb hpos

/-- Each running product of the split is an exp Taylor term:
`∏_{0≤j≤i}(u/(v·(j+1))) = (u/v)^(i+1)/(i+1)!`. -/
theorem exp_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ j ∈ Finset.Ico 0 (i + 1), ((u : ℚ) / ((v * (j + 1) : ℕ) : ℚ))
      = ((u : ℚ) / v) ^ (i + 1) / ((i + 1).factorial : ℚ) := by
  rw [← Finset.range_eq_Ico]
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range]
  have hfac : ∏ j ∈ Finset.range (i + 1), ((j : ℚ) + 1) = ((i + 1).factorial : ℚ) := by
    rw [← Finset.prod_range_add_one_eq_factorial (i + 1)]; push_cast; ring
  rw [hfac, div_pow]
  have hvne : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hfne : ((i + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- The value of the split. With `(T,Q,P) = binarySplit (fun _ => u) (fun j => v·(j+1)) 0 (N-1)`,
the exp Taylor partial sum `∑_{i<N} (u/v)^i/i!` equals `(Q+T)/Q`. -/
theorem exp_value (u v N T Q P : ℕ) (hv : v ≠ 0) (hN : 1 ≤ N)
    (h : (T, Q, P) = binarySplit (fun _ => u) (fun j => v * (j + 1)) 0 (N - 1)) :
    (((Q + T : ℕ) : ℚ) / (Q : ℚ))
      = ∑ i ∈ Finset.range N, ((u : ℚ) / v) ^ i / (i.factorial : ℚ) := by
  have hqne : ∀ i, (fun j => v * (j + 1)) i ≠ 0 := by intro i; simp [hv]
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := fun _ => u) (q := fun j => v * (j + 1))
      (m := 0) (n := N - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := fun _ => u) (q := fun j => v * (j + 1))
    (m := 0) (n := N - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ => by simpa using exp_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  -- split off the i = 0 term of the range-N sum
  have hNeq : N = N - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  rw [hspec]
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  push_cast
  field_simp
  ring

open Real in
/-- Enclosure for `exp(u/v)` via binary splitting. The certificate is a `binarySplit` returning
`(T, Qd, P)` with Taylor-sum value `(Qd+T)/Qd`, rounded to the dyadic `p/Q`. -/
theorem exp_dyadic_bound (u v N Nm Qd D T P Q p : ℕ)
    (hu : u.blt ((N.succ).mul v)) (hQd : Nat.ble 1 Qd) (hD : Nat.ble 1 D) (hv : Nat.ble 1 v)
    (hN : Nat.ble 1 N) (hNm : (Nm.succ).beq N)
    (hsplit : binarySplit (expNatP u) (expNatQ v) 0 Nm = (T, Qd, P))
    -- the tail factor `v^N·N!` is expressed as `v·N·Qd` (`Qd = v^(N-1)·(N-1)!` is the split's
    -- own denominator, already balanced-verified), so the kernel never reduces `Nat.factorial N`.
    (htail : (((u.pow N).mul (N.succ)).mul v).mul (Nat.mul 2 D) |>.ble
      (((v.mul N).mul Qd).mul (((N.succ).mul v).sub u)))
    (hr1 : (p.mul Qd).ble ((Qd.add T).mul Q)) (hr2 : ((Qd.add T).mul Q).blt ((p.succ).mul Qd))
    (hQ : (Nat.mul 2 D).ble Q) :
    Real.IsNear (Real.exp ((u : ℝ) / v)) false p Q 1 D := by
  have hNm' : Nm = N - 1 := by
    have h : Nm + 1 = N := Nat.eq_of_beq_eq_true hNm
    omega
  subst hNm'
  -- `Qd = v^(N-1)·(N-1)!` from the split's product component, hence `v·N·Qd = v^N·N!`
  have hQdeq : Qd = v ^ (N - 1) * (N - 1).factorial := by
    have h := (binarySplit_PQ (p := expNatP u) (q := expNatQ v) (m := 0) (n := N - 1)).2
    rw [hsplit] at h
    have hQdraw : Qd = ∏ j ∈ Finset.Ico 0 (N - 1), expNatQ v j := h
    rw [hQdraw, ← Finset.range_eq_Ico]
    simp only [expNatQ, Nat.mul_eq, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    rw [Finset.prod_range_add_one_eq_factorial]
  have hbridge : v * N * Qd = v ^ N * N.factorial := by
    rw [hQdeq]
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by have := Nat.le_of_ble_eq_true hN; omega⟩
    simp only [Nat.add_sub_cancel]
    rw [pow_succ, Nat.factorial_succ]; ring
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
    Nat.sub_eq] at hu htail hr1 hr2 hQ
  rw [hbridge] at htail
  have hDN : 0 < D := pos_of_ble hD
  have hqs' : (0 : ℝ) < Qd := pos_real_of_ble hQd
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hvr : (0 : ℝ) < v := pos_real_of_ble hv
  have hvne : v ≠ 0 := (pos_of_ble hv).ne'
  have hvR : (v : ℝ) ≠ 0 := ne_of_gt hvr
  have hQ0 : 0 < Q := by omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hx0 : 0 ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < (N : ℝ) + 1 := by rw [div_lt_iff₀ hvr]; exact_mod_cast hu
  -- value link: the dyadic-free fraction (Qd+T)/Qd is the exp Taylor partial sum
  have hsum : ∑ k ∈ Finset.range N, ((u : ℝ) / v) ^ k / (k.factorial : ℝ)
      = ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) := by
    have hq := exp_value u v N T Qd P hvne (Nat.le_of_ble_eq_true hN) hsplit.symm
    have hr := congrArg (fun r : ℚ => (r : ℝ)) hq
    push_cast at hr ⊢
    rw [← hr]
  have hexp : |Real.exp ((u : ℝ) / v) - ((Qd + T : ℕ) : ℝ) / (Qd : ℝ)|
      ≤ ((u : ℝ) / v) ^ N / N.factorial * (((N : ℝ) + 1) / ((N : ℝ) + 1 - (u : ℝ) / v)) := by
    rw [← hsum, abs_of_nonneg (exp_sub_sum_nonneg _ N hx0)]
    exact exp_sub_sum_le _ N hx0 hxlt
  have htail' : ((u : ℝ) / v) ^ N / N.factorial * (((N : ℝ) + 1) / ((N : ℝ) + 1 - (u : ℝ) / v))
      ≤ 1 / (2 * D) := by
    have hpos : (0 : ℝ) < (N : ℝ) + 1 - (u : ℝ) / v := by linarith
    have hsubpos : 0 < (N + 1) * v - u := by
      have h := hu; simp only [Nat.succ_eq_add_one] at h; omega
    have hfacne : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos N).ne'
    have hvpowne : (v : ℝ) ^ N ≠ 0 := pow_ne_zero N hvR
    have hc1 : ((N : ℝ) + 1 - (u : ℝ) / v) = (((N + 1) * v - u : ℕ) : ℝ) / v := by
      rw [Nat.cast_sub hu.le]; push_cast; field_simp
    have key : ((u : ℝ) / v) ^ N / N.factorial * (((N : ℝ) + 1) / ((N : ℝ) + 1 - (u : ℝ) / v))
        = ((u : ℝ) ^ N * ((N : ℝ) + 1) * v) /
          ((v : ℝ) ^ N * N.factorial * (((N + 1) * v - u : ℕ) : ℝ)) := by
      rw [hc1, div_pow]
      field_simp
    have hden : (0 : ℝ) < (v : ℝ) ^ N * N.factorial * (((N + 1) * v - u : ℕ) : ℝ) :=
      mul_pos (mul_pos (pow_pos hvr N) (by exact_mod_cast Nat.factorial_pos N))
        (by exact_mod_cast hsubpos)
    rw [key, div_le_div_iff₀ hden (mul_pos two_pos hDr), one_mul]
    exact_mod_cast htail
  have e1 : (p : ℝ) / Q ≤ ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) := by
    rw [div_le_div_iff₀ hQr hqs']; exact_mod_cast hr1
  have e2 : ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) < (p : ℝ) / Q + 1 / Q := by
    rw [← add_div, div_lt_div_iff₀ hqs' hQr]; exact_mod_cast hr2
  have hround' : |((Qd + T : ℕ) : ℝ) / (Qd : ℝ) - (p : ℝ) / Q| ≤ 1 / (2 * D) := by
    rw [abs_of_nonneg (sub_nonneg.mpr e1)]
    calc ((Qd + T : ℕ) : ℝ) / (Qd : ℝ) - (p : ℝ) / Q
        ≤ 1 / Q := by linarith [e2]
      _ ≤ 1 / (2 * D) := by
          rw [div_le_div_iff₀ hQr (mul_pos two_pos hDr), one_mul, one_mul]; exact_mod_cast hQ
  calc |Real.exp ((u : ℝ) / v) - (p : ℝ) / Q|
      ≤ |Real.exp ((u : ℝ) / v) - ((Qd + T : ℕ) : ℝ) / (Qd : ℝ)|
          + |((Qd + T : ℕ) : ℝ) / (Qd : ℝ) - (p : ℝ) / Q| := abs_sub_le _ _ _
    _ ≤ 1 / (2 * D) + 1 / (2 * D) := add_le_add (hexp.trans htail') hround'
    _ = 1 / D := by rw [← add_div, one_add_one_eq_two, ← div_div, div_self two_ne_zero]

/-- Recast `exp (↑u/↑1)` as `exp ↑u` for the integer path (`↑u/↑1` is not defeq to `↑u`). -/
theorem exp_int_of_rat (u : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (h : Real.IsNear (Real.exp ((u : ℝ) / ((1 : ℕ) : ℝ))) neg cn cd rn rd) :
    Real.IsNear (Real.exp ((u : ℕ) : ℝ)) neg cn cd rn rd := by
  rwa [Nat.cast_one, div_one] at h

end BSN
