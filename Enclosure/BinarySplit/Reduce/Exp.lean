module

public import Enclosure
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Range-reduction lemmas for `exp` by `log 2`

`exp x = 2ᵏ·exp r` with `r = x − k·log 2` (`exp_scale`), the Lipschitz bound
`abs_exp_sub_exp_le_mul`, and the step lemma `exp_reduce_step`.
-/
@[expose] public section


namespace BSN
open Enclosure

/-! ### `exp` reduction by `log 2` -/

/-- If `M` bounds `exp` at both points (`exp r ≤ M`, `exp rc ≤ M`), then
`|exp r − exp rc| ≤ M·|r − rc|`. -/
theorem abs_exp_sub_exp_le_mul (r rc M : ℝ) (hr : Real.exp r ≤ M) (hrc : Real.exp rc ≤ M) :
    |Real.exp r - Real.exp rc| ≤ M * |r - rc| := by
  rcases le_total rc r with h | h
  · have hge : Real.exp rc ≤ Real.exp r := Real.exp_le_exp.mpr h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith : (0 : ℝ) ≤ r - rc)]
    have key : Real.exp r - Real.exp rc ≤ Real.exp r * (r - rc) := by
      have h1 := Real.add_one_le_exp (rc - r)
      have h2 : Real.exp r * (rc - r + 1) ≤ Real.exp r * Real.exp (rc - r) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos r))
      rw [← Real.exp_add] at h2
      have e : r + (rc - r) = rc := by ring
      rw [e] at h2
      nlinarith [Real.exp_pos r]
    calc Real.exp r - Real.exp rc ≤ Real.exp r * (r - rc) := key
      _ ≤ M * (r - rc) := mul_le_mul_of_nonneg_right hr (by linarith)
  · have hge : Real.exp r ≤ Real.exp rc := Real.exp_le_exp.mpr h
    rw [abs_sub_comm (Real.exp r) (Real.exp rc), abs_sub_comm r rc,
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith : (0 : ℝ) ≤ rc - r)]
    have key : Real.exp rc - Real.exp r ≤ Real.exp rc * (rc - r) := by
      have h1 := Real.add_one_le_exp (r - rc)
      have h2 : Real.exp rc * (r - rc + 1) ≤ Real.exp rc * Real.exp (r - rc) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos rc))
      rw [← Real.exp_add] at h2
      have e : rc + (r - rc) = r := by ring
      rw [e] at h2
      nlinarith [Real.exp_pos rc]
    calc Real.exp rc - Real.exp r ≤ Real.exp rc * (rc - r) := key
      _ ≤ M * (rc - r) := mul_le_mul_of_nonneg_right hrc (by linarith)

/-- `log 2` reduction core. From `exp x = 2ᵏ·exp r`, an `M`-Lipschitz bound between `r` and the
centre `rc`, `|r − rc| ≤ B`, and `|exp rc − val| ≤ inner`, conclude `|exp x − 2ᵏ·val| ≤ Dinv`
whenever `2ᵏ·(M·B + inner) ≤ Dinv`. -/
theorem exp_reduce_core (x r rc val M B inner Dinv : ℝ) (k : ℕ) (hM : 0 ≤ M)
    (hk : Real.exp x = (2 : ℝ) ^ k * Real.exp r)
    (hlip : |Real.exp r - Real.exp rc| ≤ M * |r - rc|)
    (hB : |r - rc| ≤ B)
    (hinner : |Real.exp rc - val| ≤ inner)
    (htot : (2 : ℝ) ^ k * (M * B + inner) ≤ Dinv) :
    |Real.exp x - (2 : ℝ) ^ k * val| ≤ Dinv := by
  have hpk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h1 : |Real.exp x - (2 : ℝ) ^ k * val| = (2 : ℝ) ^ k * |Real.exp r - val| := by
    rw [hk, ← mul_sub, abs_mul, abs_of_pos hpk]
  rw [h1]
  have h2 : |Real.exp r - val| ≤ M * B + inner :=
    calc |Real.exp r - val|
        ≤ |Real.exp r - Real.exp rc| + |Real.exp rc - val| := abs_sub_le _ _ _
      _ ≤ M * B + inner := add_le_add (hlip.trans (mul_le_mul_of_nonneg_left hB hM)) hinner
  calc (2 : ℝ) ^ k * |Real.exp r - val|
      ≤ (2 : ℝ) ^ k * (M * B + inner) := mul_le_mul_of_nonneg_left h2 (le_of_lt hpk)
    _ ≤ Dinv := htot

/-! ### Automated reduction: the scale identity, the centre identity, and the step lemma -/

/-- Scale identity `exp X = 2ᵏ·exp(X − k·log 2)`, from `exp(k·log 2) = (exp(log 2))ᵏ = 2ᵏ`. -/
theorem exp_scale (X k : ℕ) :
    Real.exp X = (2 : ℝ) ^ k * Real.exp ((X : ℝ) - k * Real.log 2) := by
  have h2 : Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← h2, ← Real.exp_add]
  congr 1
  ring

/-- The centre identity. With the `ℕ` link `X·LQ = u + k·Lp`, the rational `u/LQ` equals the
centre `X − k·(Lp/LQ)`. -/
theorem exp_reduce_arg_pos (X Lp LQ k u : ℕ)
    (hlink : (X.mul LQ).beq (u.add (k.mul Lp))) (hLQ : Nat.ble 1 LQ) :
    (u : ℝ) / (LQ : ℝ) = (X : ℝ) - (k : ℝ) * ((Lp : ℝ) / (LQ : ℝ)) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hlink
  have hLQr : (0 : ℝ) < LQ := pos_real_of_ble hLQ
  have key : (X : ℝ) * LQ = (u : ℝ) + k * Lp := by exact_mod_cast hlink
  field_simp
  linarith [key]

/-- The reduction step. From a `log 2` certificate `|log 2 − Lp/LQ| ≤ 1/E`, the centre link
`X·LQ = u + k·Lp` and the in-range certificate `|exp(u/LQ) − val| ≤ 1/Dp`, conclude
`|exp X − 2ᵏ·val| ≤ 1/D` (Lipschitz constant `M = 3`). -/
theorem exp_reduce_step (X k E Lp LQ Dp D u vp vQ Pf : ℕ)
    (hPf : Pf.beq ((Nat.pow 2 k).mul vp))
    (hL : Real.IsNear (Real.log 2) false Lp LQ 1 E)
    (hlink : (X.mul LQ).beq (u.add (k.mul Lp)))
    (hinner : Real.IsNear (Real.exp ((u : ℝ) / (LQ : ℝ))) false vp vQ 1 Dp)
    (hLQ : Nat.ble 1 LQ) (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (hle1 : ((u.mul E).add (k.mul LQ)).ble (LQ.mul E))
    (htot : (((Nat.pow 2 k).mul (((Nat.mul 3 k).mul Dp).add E)).mul D).ble (E.mul Dp)) :
    Real.IsNear (Real.exp ((X : ℕ) : ℝ)) false Pf vQ 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hL hinner ⊢
  have hLQbt := hLQ
  simp only [Nat.beq_eq, Nat.mul_eq, Nat.pow_eq] at hPf
  set val : ℝ := (vp : ℝ) / vQ with hvaldef
  have hPfval : (Pf : ℝ) / (vQ : ℝ) = (2 : ℝ) ^ k * val := by
    rw [hvaldef, hPf]; push_cast; ring
  rw [hPfval]
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq] at hle1 htot
  have hLQr : (0 : ℝ) < LQ := pos_real_of_ble hLQ
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  have hDpr : (0 : ℝ) < Dp := pos_real_of_ble hDp
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  set L : ℝ := (Lp : ℝ) / LQ with hLdef
  set rc : ℝ := (u : ℝ) / LQ with hrcdef
  set r : ℝ := (X : ℝ) - k * Real.log 2 with hrdef
  have hrc : rc = (X : ℝ) - k * L := by
    rw [hrcdef, hLdef]; exact exp_reduce_arg_pos X Lp LQ k u hlink hLQbt
  have hknn : (0 : ℝ) ≤ (k : ℝ) / E := by positivity
  -- displacement `|r − rc| ≤ k/E`
  have hB : |r - rc| ≤ (k : ℝ) / E := by
    have e : r - rc = -((k : ℝ) * (Real.log 2 - L)) := by rw [hrdef, hrc]; ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    calc (k : ℝ) * |Real.log 2 - L| ≤ (k : ℝ) * (1 / E) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = (k : ℝ) / E := by ring
  -- `rc + k/E ≤ 1`, hence `rc ≤ 1` and `r ≤ 1`
  have hrcB1 : rc + (k : ℝ) / E ≤ 1 := by
    rw [hrcdef, div_add_div _ _ (ne_of_gt hLQr) (ne_of_gt hEr), div_le_one (by positivity)]
    have hle1R : ((u * E + k * LQ : ℕ) : ℝ) ≤ ((LQ * E : ℕ) : ℝ) := by exact_mod_cast hle1
    push_cast at hle1R ⊢
    nlinarith [hle1R]
  have hrc1 : rc ≤ 1 := by linarith [hrcB1, hknn]
  have hr1 : r ≤ 1 := by
    have h1 : r - rc ≤ |r - rc| := le_abs_self _
    linarith [hB, hrcB1]
  have hexp3 : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  have hr3 : Real.exp r ≤ 3 := le_trans (Real.exp_le_exp.mpr hr1) hexp3
  have hrc3 : Real.exp rc ≤ 3 := le_trans (Real.exp_le_exp.mpr hrc1) hexp3
  have hlip := abs_exp_sub_exp_le_mul r rc 3 hr3 hrc3
  -- final precision combine
  have htotR : (2 : ℝ) ^ k * (3 * ((k : ℝ) / E) + 1 / Dp) ≤ 1 / D := by
    have hc : (2 : ℝ) ^ k * (3 * k * Dp + E) * D ≤ E * Dp := by exact_mod_cast htot
    have e : (2 : ℝ) ^ k * (3 * ((k : ℝ) / E) + 1 / Dp)
        = (2 : ℝ) ^ k * (3 * k * Dp + E) / (E * Dp) := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) hDr, one_mul]
    nlinarith [hc]
  exact exp_reduce_core X r rc val 3 ((k : ℝ) / E) (1 / Dp) (1 / D) k (by norm_num)
    (exp_scale X k) hlip hB hinner htotR

end BSN
