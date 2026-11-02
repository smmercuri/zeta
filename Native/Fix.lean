module

public import Native.Eval.Fix
public import Native.Trig
public import Enclosure.BinarySplit.Taylor

/-!
# Fixed-point enclosures

Soundness of `Native.Eval.Fix`: `Fx.Encloses Q a x` says `|x − c/Q| ≤ r/Q` and `|c| ≤ m·Q`, and
each operation's result encloses the real operation's result. The grid `1/Q` is shared, so
addition and subtraction are exact on numerators; multiplication and division round the centre
down and the radius up, which `intDiv_bounds` and `natDiv_bound` account for.
-/
@[expose] public section

namespace Native

open Enclosure BSN

namespace Fx

/-- `a` encloses `x` on the grid `1/Q`: `|x − c/Q| ≤ r/Q`, with the magnitude bound `|c| ≤ m·Q`. -/
def Encloses (Q : ℕ) (a : Fx) (x : ℝ) : Prop :=
  |x - (a.c : ℝ) / Q| ≤ (a.r : ℝ) / Q ∧ a.c.natAbs ≤ a.m * Q

/-! ### Rounding -/

/-- Integer division by a positive `Q` is the floor: `⌊A/Q⌋ ≤ A/Q < ⌊A/Q⌋ + 1`. -/
theorem intDiv_bounds (A : ℤ) {Q : ℕ} (hQ : 0 < Q) :
    ((A / (Q : ℤ) : ℤ) : ℝ) ≤ (A : ℝ) / Q ∧ (A : ℝ) / Q < ((A / (Q : ℤ) : ℤ) : ℝ) + 1 := by
  have hQZ : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h1 : A / (Q : ℤ) * Q ≤ A := Int.ediv_mul_le A hQZ.ne'
  have h2 : A < (A / (Q : ℤ) + 1) * Q := Int.lt_ediv_add_one_mul_self A hQZ
  constructor
  · rw [le_div_iff₀ hQR]; exact_mod_cast h1
  · rw [div_lt_iff₀ hQR]; exact_mod_cast h2

/-- Natural division by a positive `Q` loses less than one: `N/Q ≤ ⌊N/Q⌋ + 1`. -/
theorem natDiv_bound (N : ℕ) {Q : ℕ} (hQ : 0 < Q) : (N : ℝ) / Q ≤ ((N / Q : ℕ) : ℝ) + 1 := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h : N < (N / Q + 1) * Q := by
    have := Nat.div_add_mod N Q
    have := Nat.mod_lt N hQ
    nlinarith
  rw [div_le_iff₀ hQR]
  exact_mod_cast h.le

/-- Rounded-up natural division: `n ≤ ⌈n/d⌉·d`. -/
theorem le_ceilDiv_mul (n : ℕ) {d : ℕ} (hd : 0 < d) : n ≤ (n + d - 1) / d * d := by
  have := Nat.div_add_mod (n + d - 1) d
  have := Nat.mod_lt (n + d - 1) hd
  have := Nat.mul_comm ((n + d - 1) / d) d
  omega

/-- The rounding error of `A/Q ↦ ⌊A/Q⌋/Q` on the grid: at most `1/Q`. -/
theorem floor_grid_err (A : ℤ) {Q : ℕ} (hQ : 0 < Q) :
    |(A : ℝ) / Q / Q - ((A / (Q : ℤ) : ℤ) : ℝ) / Q| ≤ 1 / Q := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨h1, h2⟩ := intDiv_bounds A hQ
  rw [← sub_div, abs_div, abs_of_pos hQR, div_le_div_iff_of_pos_right hQR, abs_le]
  constructor <;> linarith

/-- Floor division keeps a magnitude bound: `|P| ≤ K·Q` gives `|⌊P/Q⌋| ≤ K`. -/
theorem natAbs_ediv_le (P : ℤ) {K Q : ℕ} (hQ : 0 < Q) (h : P.natAbs ≤ K * Q) :
    (P / (Q : ℤ)).natAbs ≤ K := by
  have h1 : -(K : ℤ) * Q ≤ P := by rw [Int.neg_mul]; omega
  have h2 : P ≤ (K : ℤ) * Q := by omega
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have e1 := Int.ediv_le_ediv hQ' h2
  have e2 := Int.ediv_le_ediv hQ' h1
  rw [Int.mul_ediv_cancel _ hQ'.ne'] at e1 e2
  omega

/-- `a ≤ (a/b + 1)·b`. -/
theorem le_div_add_one_mul (a : ℕ) {b : ℕ} (hb : 0 < b) : a ≤ (a / b + 1) * b := by
  have := Nat.lt_div_mul_add (a := a) hb
  rw [Nat.add_mul, one_mul]; omega

/-- The magnitude of `⌊±a·Q/b⌋`: at most `(a/b + 1)·Q`. -/
theorem natAbs_scaled_le (neg : Bool) (a : ℕ) {b : ℕ} (Q : ℕ) (hb : 0 < b) :
    ((if neg then -(a : ℤ) else a) * Q / (b : ℤ)).natAbs ≤ (a / b + 1) * Q := by
  refine natAbs_ediv_le _ hb ?_
  have h : ((if neg then -(a : ℤ) else a) * Q).natAbs = a * Q := by
    cases neg <;> simp [Int.natAbs_mul]
  rw [h, Nat.mul_right_comm]
  exact Nat.mul_le_mul_right _ (le_div_add_one_mul a hb)

/-! ### Exact operations -/

/-- The triangle inequality for two enclosure errors. -/
theorem abs_add_sub_le {x y cx cy rx ry : ℝ} (ha : |x - cx| ≤ rx) (hb : |y - cy| ≤ ry) :
    |x + y - (cx + cy)| ≤ rx + ry := by
  calc |x + y - (cx + cy)| = |(x - cx) + (y - cy)| := by ring_nf
    _ ≤ |x - cx| + |y - cy| := abs_add_le _ _
    _ ≤ _ := add_le_add ha hb

theorem zero_encloses {Q : ℕ} : zero.Encloses Q 0 := by simp [Encloses, zero]

theorem ofInt_encloses {Q : ℕ} (hQ : 0 < Q) (k : ℤ) : (ofInt Q k).Encloses Q k := by
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  exact ⟨by simp [ofInt, hQR], by simp [ofInt, Int.natAbs_mul]⟩

theorem add_encloses {Q : ℕ} {a b : Fx} {x y : ℝ} (ha : a.Encloses Q x) (hb : b.Encloses Q y) :
    (add a b).Encloses Q (x + y) := by
  refine ⟨?_, ?_⟩
  · simp only [add, Int.cast_add, Nat.cast_add, add_div]
    exact abs_add_sub_le ha.1 hb.1
  · have := Int.natAbs_add_le a.c b.c
    have := ha.2
    have := hb.2
    simp only [add, Nat.add_mul]
    omega

theorem neg_encloses {Q : ℕ} {a : Fx} {x : ℝ} (ha : a.Encloses Q x) :
    (neg a).Encloses Q (-x) := by
  refine ⟨?_, by simpa [neg] using ha.2⟩
  simp only [neg, Int.cast_neg, neg_div]
  rw [show -x - -((a.c : ℝ) / Q) = -(x - (a.c : ℝ) / Q) by ring, abs_neg]
  exact ha.1

theorem sub_encloses {Q : ℕ} {a b : Fx} {x y : ℝ} (ha : a.Encloses Q x) (hb : b.Encloses Q y) :
    (sub a b).Encloses Q (x - y) := by
  have h := add_encloses ha (neg_encloses hb)
  simp only [add, neg, ← sub_eq_add_neg] at h
  exact h

theorem smul_encloses {Q : ℕ} (k : ℤ) {a : Fx} {x : ℝ} (ha : a.Encloses Q x) :
    (smul k a).Encloses Q (k * x) := by
  refine ⟨?_, ?_⟩
  · simp only [smul, Int.cast_mul, Nat.cast_mul, Nat.cast_natAbs]
    rw [show (k : ℝ) * x - (k : ℝ) * (a.c : ℝ) / Q = k * (x - (a.c : ℝ) / Q) by ring, abs_mul,
      mul_div_assoc, Int.cast_abs]
    exact mul_le_mul_of_nonneg_left ha.1 (abs_nonneg _)
  · simp only [smul, Int.natAbs_mul, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ ha.2

theorem tighten_encloses {Q : ℕ} (hQ : 0 < Q) {a : Fx} {x : ℝ} (ha : a.Encloses Q x) :
    (tighten Q a).Encloses Q x := ⟨ha.1, le_div_add_one_mul _ hQ⟩

/-! ### Multiplication and division -/

/-- The rounded product's error, with the centres themselves in the radius: the bound `mul` and
`mulExact` both reduce to. -/
theorem abs_mul_sub_floor_le {Q : ℕ} (hQ : 0 < Q) {a b : Fx} {x y : ℝ} (ha : a.Encloses Q x)
    (hb : b.Encloses Q y) :
    |x * y - ((a.c * b.c / (Q : ℤ) : ℤ) : ℝ) / Q|
      ≤ (((a.c.natAbs : ℝ) * b.r + b.c.natAbs * a.r + a.r * b.r) / Q + 1) / Q := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  -- the exact product's error, `|xy − cₐc_b/Q²| ≤ N/Q²`
  have hprod := Enclosure.abs_mul_sub ha.1 hb.1
  have hNR : |(a.c : ℝ) / Q| * ((b.r : ℝ) / Q) + |(b.c : ℝ) / Q| * ((a.r : ℝ) / Q)
      + (a.r : ℝ) / Q * ((b.r : ℝ) / Q) =
        ((a.c.natAbs : ℝ) * b.r + b.c.natAbs * a.r + a.r * b.r) / Q / Q := by
    simp only [Nat.cast_natAbs, Int.cast_abs, abs_div, abs_of_pos hQR]
    field_simp
  rw [hNR] at hprod
  have hround := floor_grid_err (a.c * b.c) hQ
  have hcentre : (a.c : ℝ) / Q * ((b.c : ℝ) / Q) = ((a.c * b.c : ℤ) : ℝ) / Q / Q := by
    push_cast; field_simp
  rw [hcentre] at hprod
  calc |x * y - ((a.c * b.c / (Q : ℤ) : ℤ) : ℝ) / Q|
      ≤ |x * y - ((a.c * b.c : ℤ) : ℝ) / Q / Q|
        + |((a.c * b.c : ℤ) : ℝ) / Q / Q - ((a.c * b.c / (Q : ℤ) : ℤ) : ℝ) / Q| :=
        abs_sub_le _ _ _
    _ ≤ ((a.c.natAbs : ℝ) * b.r + b.c.natAbs * a.r + a.r * b.r) / Q / Q + 1 / Q :=
        add_le_add hprod hround
    _ = _ := (add_div _ _ _).symm

/-- The magnitude bound of a product: `|⌊cₐc_b/Q⌋| ≤ mₐm_b·Q`. -/
theorem natAbs_mul_ediv_le {Q : ℕ} (hQ : 0 < Q) {a b : Fx} {x y : ℝ} (ha : a.Encloses Q x)
    (hb : b.Encloses Q y) : (a.c * b.c / (Q : ℤ)).natAbs ≤ a.m * b.m * Q := by
  refine natAbs_ediv_le _ hQ ?_
  rw [Int.natAbs_mul]
  calc a.c.natAbs * b.c.natAbs ≤ (a.m * Q) * (b.m * Q) := Nat.mul_le_mul ha.2 hb.2
    _ = a.m * b.m * Q * Q := by ring

theorem mul_encloses {Q : ℕ} (hQ : 0 < Q) {a b : Fx} {x y : ℝ} (ha : a.Encloses Q x)
    (hb : b.Encloses Q y) : (mul Q a b).Encloses Q (x * y) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨?_, natAbs_mul_ediv_le hQ ha hb⟩
  refine (abs_mul_sub_floor_le hQ ha hb).trans (div_le_div_of_nonneg_right ?_ hQR.le)
  -- the centres bounded by their magnitudes
  have hca : (a.c.natAbs : ℝ) ≤ a.m * Q := by exact_mod_cast ha.2
  have hcb : (b.c.natAbs : ℝ) ≤ b.m * Q := by exact_mod_cast hb.2
  have h1 := mul_le_mul_of_nonneg_right hca (Nat.cast_nonneg (α := ℝ) b.r)
  have h2 := mul_le_mul_of_nonneg_right hcb (Nat.cast_nonneg (α := ℝ) a.r)
  have hrr := natDiv_bound (a.r * b.r) hQ
  push_cast at hrr
  rw [add_div, add_div]
  have e1 : (a.c.natAbs : ℝ) * b.r / Q ≤ a.m * b.r := by
    rw [div_le_iff₀ hQR]; linarith
  have e2 : (b.c.natAbs : ℝ) * a.r / Q ≤ b.m * a.r := by
    rw [div_le_iff₀ hQR]; linarith
  simp only [mul]
  push_cast
  linarith

theorem mulExact_encloses {Q : ℕ} (hQ : 0 < Q) {a b : Fx} {x y : ℝ} (ha : a.Encloses Q x)
    (hb : b.Encloses Q y) : (mulExact Q a b).Encloses Q (x * y) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨?_, natAbs_mul_ediv_le hQ ha hb⟩
  refine (abs_mul_sub_floor_le hQ ha hb).trans (div_le_div_of_nonneg_right ?_ hQR.le)
  have hN := natDiv_bound (a.c.natAbs * b.r + b.c.natAbs * a.r + a.r * b.r) hQ
  simp only [mulExact]
  push_cast at hN ⊢
  linarith

theorem divNat_encloses {Q k : ℕ} (hQ : 0 < Q) (hk : 0 < k) {a : Fx} {x : ℝ}
    (ha : a.Encloses Q x) : (divNat k a).Encloses Q (x / k) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · simp only [divNat]
    obtain ⟨h1, h2⟩ := intDiv_bounds a.c hk
    have hrk := natDiv_bound a.r hk
    -- `|x/k − c/(kQ)| ≤ r/(kQ)` and `|c/(kQ) − ⌊c/k⌋/Q| ≤ 1/Q`
    have e1 : |x / k - (a.c : ℝ) / k / Q| ≤ (a.r : ℝ) / k / Q := by
      rw [show x / k - (a.c : ℝ) / k / Q = (x - (a.c : ℝ) / Q) / k by field_simp, abs_div,
        abs_of_pos hkR, div_div, mul_comm (k : ℝ), ← div_div]
      exact div_le_div_of_nonneg_right ha.1 hkR.le
    have e2 : |(a.c : ℝ) / k / Q - ((a.c / (k : ℤ) : ℤ) : ℝ) / Q| ≤ 1 / Q := by
      rw [← sub_div, abs_div, abs_of_pos hQR, div_le_div_iff_of_pos_right hQR, abs_le]
      constructor <;> linarith
    have hrad : (a.r : ℝ) / k / Q + 1 / Q ≤ ((a.r / k + 2 : ℕ) : ℝ) / Q := by
      rw [← add_div, div_le_div_iff_of_pos_right hQR]
      push_cast; linarith
    calc |x / k - ((a.c / (k : ℤ) : ℤ) : ℝ) / Q|
        ≤ |x / k - (a.c : ℝ) / k / Q| + |(a.c : ℝ) / k / Q - ((a.c / (k : ℤ) : ℤ) : ℝ) / Q| :=
          abs_sub_le _ _ _
      _ ≤ _ := le_trans (add_le_add e1 e2) hrad
  · simp only [divNat]
    refine natAbs_ediv_le _ hk ?_
    calc a.c.natAbs ≤ a.m * Q := ha.2
      _ ≤ (a.m / k + 1) * k * Q := Nat.mul_le_mul_right _ (le_div_add_one_mul _ hk)
      _ = (a.m / k + 1) * Q * k := Nat.mul_right_comm _ _ _

/-- The bound `absBound`: `|x| ≤ B/Q`. -/
theorem abs_le_absBound {Q : ℕ} {a : Fx} {x : ℝ} (ha : a.Encloses Q x) :
    |x| ≤ (a.absBound : ℝ) / Q := by
  have ha := ha.1
  simp only [absBound, Nat.cast_add, Nat.cast_natAbs, Int.cast_abs, add_div]
  have := abs_sub_abs_le_abs_sub x ((a.c : ℝ) / Q)
  rw [abs_div, Nat.abs_cast] at this
  linarith

/-! ### Conversions -/

theorem ofRat_encloses {Q a b : ℕ} (hQ : 0 < Q) (hb : 0 < b) (neg : Bool) :
    (ofRat neg a b Q).Encloses Q (sfrac neg a b) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  refine ⟨?_, natAbs_scaled_le neg a Q hb⟩
  set s : ℤ := (if neg then -(a : ℤ) else a) with hs
  have hval : sfrac neg a b = ((s * Q : ℤ) : ℝ) / b / Q := by
    rw [hs]; cases neg <;> simp [sfrac] <;> field_simp
  simp only [ofRat, ← hs, Nat.cast_one]
  rw [hval]
  obtain ⟨h1, h2⟩ := intDiv_bounds (s * Q) hb
  rw [← sub_div, abs_div, abs_of_pos hQR, div_le_div_iff_of_pos_right hQR, abs_le]
  constructor <;> linarith

theorem ofEncl_encloses {Q : ℕ} (hQ : 0 < Q) {e : Encl} {f : Fx} {x : ℝ} (he : e.Encloses x)
    (h : ofEncl Q e = some f) : f.Encloses Q x := by
  simp only [ofEncl] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hcd, hrd⟩ := hc
    cases h
    have hcd' : 0 < e.cd := Nat.le_of_ble_eq_true hcd
    have hrd' : 0 < e.rd := Nat.le_of_ble_eq_true hrd
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hcdR : (0 : ℝ) < e.cd := by exact_mod_cast hcd'
    have hrdR : (0 : ℝ) < e.rd := by exact_mod_cast hrd'
    refine ⟨?_, natAbs_scaled_le e.neg e.cn Q hcd'⟩
    set s : ℤ := (if e.neg then -(e.cn : ℤ) else e.cn) with hs
    have hval : sfrac e.neg e.cn e.cd = ((s * Q : ℤ) : ℝ) / e.cd / Q := by
      rw [hs]; cases e.neg <;> simp [sfrac] <;> field_simp
    simp only [Encl.Encloses, Real.IsNear] at he
    obtain ⟨h1, h2⟩ := intDiv_bounds (s * Q) hcd'
    have hrn := natDiv_bound (e.rn * Q) hrd'
    have e2 : |((s * Q : ℤ) : ℝ) / e.cd / Q - ((s * Q / (e.cd : ℤ) : ℤ) : ℝ) / Q| ≤ 1 / Q := by
      rw [← sub_div, abs_div, abs_of_pos hQR, div_le_div_iff_of_pos_right hQR, abs_le]
      constructor <;> linarith
    have hrad : (e.rn : ℝ) / e.rd + 1 / Q ≤ ((e.rn * Q / e.rd + 2 : ℕ) : ℝ) / Q := by
      rw [show (e.rn : ℝ) / e.rd = ((e.rn * Q : ℕ) : ℝ) / e.rd / Q by push_cast; field_simp,
        ← add_div, div_le_div_iff_of_pos_right hQR]
      push_cast at hrn ⊢; linarith
    rw [hval] at he
    calc |x - ((s * Q / (e.cd : ℤ) : ℤ) : ℝ) / Q|
        ≤ |x - ((s * Q : ℤ) : ℝ) / e.cd / Q|
          + |((s * Q : ℤ) : ℝ) / e.cd / Q - ((s * Q / (e.cd : ℤ) : ℤ) : ℝ) / Q| :=
          abs_sub_le _ _ _
      _ ≤ _ := le_trans (add_le_add he e2) hrad
  · cases h

theorem toEncl_encloses {Q : ℕ} {a : Fx} {x : ℝ} (ha : a.Encloses Q x) :
    (toEncl Q a).Encloses x := by
  simp only [Encl.Encloses, Real.IsNear, toEncl]
  have hval : sfrac (decide (a.c < 0)) a.c.natAbs Q = (a.c : ℝ) / Q := by
    by_cases hc : a.c < 0
    · simp only [hc, decide_true, sfrac, if_true, Nat.cast_natAbs, Int.cast_abs]
      rw [abs_of_neg (by exact_mod_cast hc)]; ring
    · simp only [hc, decide_false, sfrac, Bool.false_eq_true, if_false, Nat.cast_natAbs,
        Int.cast_abs]
      rw [abs_of_nonneg (by exact_mod_cast not_lt.mp hc)]; ring
  rw [hval]; exact ha.1

/-! ### Inverse and square root -/

theorem ofBounds_encloses {Q a b : ℕ} (hQ : 0 < Q) {y : ℝ} (ha : (a : ℝ) ≤ Q * y)
    (hb : Q * y ≤ b) : (ofBounds Q a b).Encloses Q y := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hab : a ≤ b := by exact_mod_cast ha.trans hb
  have hM1 := Nat.div_mul_le_self (a + b) 2
  have hM2 := Nat.lt_div_mul_add (a := a + b) (by norm_num : 0 < 2)
  have hMb : (a + b) / 2 ≤ b := by omega
  refine ⟨?_, ?_⟩
  · simp only [ofBounds, Int.cast_natCast]
    rw [show y - (((a + b) / 2 : ℕ) : ℝ) / Q = (Q * y - ((a + b) / 2 : ℕ)) / Q by field_simp,
      abs_div, abs_of_pos hQR, div_le_div_iff_of_pos_right hQR, abs_le, Nat.cast_sub hMb]
    have h2 : (((a + b) / 2 : ℕ) : ℝ) * 2 ≤ a + b := by exact_mod_cast hM1
    constructor <;> linarith
  · simp only [ofBounds, Int.natAbs_natCast]
    exact hMb.trans (le_div_add_one_mul b hQ)

theorem invPos_encloses {Q : ℕ} {X Y : Fx} {x : ℝ} (hX : X.Encloses Q x)
    (h : invPos Q X = some Y) : Y.Encloses Q x⁻¹ := by
  unfold invPos at h
  by_cases hc : (Nat.ble 1 Q && decide ((X.r : ℤ) < X.c)) = true
  · rw [if_pos hc] at h
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hQ1, hrc⟩ := hc
    have hQ : 0 < Q := Nat.le_of_ble_eq_true hQ1
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hct : ((X.c.toNat : ℕ) : ℤ) = X.c := Int.toNat_of_nonneg (by omega)
    have hlo : X.r < X.c.toNat := by omega
    set lo := X.c.toNat - X.r with hlo_def
    set hi := X.c.toNat + X.r with hhi_def
    have hloR : (lo : ℝ) = X.c - X.r := by
      rw [hlo_def, Nat.cast_sub hlo.le]
      have : ((X.c.toNat : ℕ) : ℝ) = (X.c : ℝ) := by exact_mod_cast hct
      rw [this]
    have hhiR : (hi : ℝ) = X.c + X.r := by
      rw [hhi_def, Nat.cast_add]
      have : ((X.c.toNat : ℕ) : ℝ) = (X.c : ℝ) := by exact_mod_cast hct
      rw [this]
    have hlo0 : 0 < lo := by omega
    have hloR0 : (0 : ℝ) < lo := by exact_mod_cast hlo0
    have hhiR0 : (0 : ℝ) < hi := by exact_mod_cast (show 0 < hi by omega)
    -- `lo/Q ≤ x ≤ hi/Q`
    obtain ⟨hx1, hx2⟩ := abs_le.mp hX.1
    have hxlo : (lo : ℝ) ≤ Q * x := by
      rw [hloR]
      have : ((X.c : ℝ) - X.r) / Q ≤ x := by rw [sub_div]; linarith
      rwa [div_le_iff₀ hQR, mul_comm] at this
    have hxhi : Q * x ≤ (hi : ℝ) := by
      rw [hhiR]
      have : x ≤ ((X.c : ℝ) + X.r) / Q := by rw [add_div]; linarith
      rwa [le_div_iff₀ hQR, mul_comm] at this
    have hx0 : 0 < x := by
      have : 0 < (Q : ℝ) * x := lt_of_lt_of_le hloR0 hxlo
      exact pos_of_mul_pos_right this hQR.le
    refine ofBounds_encloses hQ ?_ ?_
    · -- `⌊Q²/hi⌋ ≤ Q²/hi ≤ Q/x`
      calc ((Q * Q / hi : ℕ) : ℝ) ≤ ((Q * Q : ℕ) : ℝ) / hi := Nat.cast_div_le
        _ ≤ Q * x⁻¹ := by
          rw [div_le_iff₀ hhiR0, Nat.cast_mul]
          have : (Q : ℝ) * (Q * x) ≤ Q * hi := mul_le_mul_of_nonneg_left hxhi hQR.le
          calc (Q : ℝ) * Q = Q * x⁻¹ * (Q * x) := by field_simp
            _ ≤ Q * x⁻¹ * hi :=
              mul_le_mul_of_nonneg_left hxhi (by positivity)
    · -- `Q/x ≤ Q²/lo ≤ ⌈Q²/lo⌉`
      have hceil := le_ceilDiv_mul (Q * Q) hlo0
      have hceilR : ((Q * Q : ℕ) : ℝ) ≤ (((Q * Q + lo - 1) / lo : ℕ) : ℝ) * lo := by
        exact_mod_cast hceil
      calc (Q : ℝ) * x⁻¹ ≤ ((Q * Q : ℕ) : ℝ) / lo := by
            rw [le_div_iff₀ hloR0, Nat.cast_mul]
            calc (Q : ℝ) * x⁻¹ * lo ≤ Q * x⁻¹ * (Q * x) :=
                  mul_le_mul_of_nonneg_left hxlo (by positivity)
              _ = Q * Q := by field_simp
        _ ≤ _ := by rw [div_le_iff₀ hloR0]; exact hceilR
  · rw [if_neg hc] at h
    cases h

theorem inv_encloses {Q : ℕ} {X Y : Fx} {x : ℝ} (hX : X.Encloses Q x)
    (h : inv Q X = some Y) : Y.Encloses Q x⁻¹ := by
  unfold inv at h
  split at h
  · obtain ⟨Z, hZ, rfl⟩ := Option.map_eq_some_iff.mp h
    have := neg_encloses (invPos_encloses (neg_encloses hX) hZ)
    rwa [inv_neg, neg_neg] at this
  · exact invPos_encloses hX h

theorem sqrt_encloses {Q : ℕ} {X Y : Fx} {x : ℝ} (hX : X.Encloses Q x)
    (h : sqrt Q X = some Y) : Y.Encloses Q (Real.sqrt x) := by
  unfold sqrt at h
  by_cases hQ1 : Nat.ble 1 Q = true
  · rw [if_pos hQ1] at h
    cases h
    have hQ : 0 < Q := Nat.le_of_ble_eq_true hQ1
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    obtain ⟨hx1, hx2⟩ := abs_le.mp hX.1
    have hQx : (Q : ℝ) * Real.sqrt x = Real.sqrt ((Q : ℝ) ^ 2 * x) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hQR.le]
    refine ofBounds_encloses hQ ?_ ?_
    · rw [hQx]
      set lo := (X.c - X.r).toNat
      have hsq := Nat.sqrt_le' (lo * Q)
      rcases Nat.eq_zero_or_pos lo with h0 | h0
      · rw [h0, zero_mul, Nat.sqrt_zero, Nat.cast_zero]; exact Real.sqrt_nonneg _
      · have hlo : ((lo : ℕ) : ℤ) = X.c - X.r := Int.toNat_of_nonneg (by omega)
        have hloR : (lo : ℝ) = X.c - X.r := by exact_mod_cast hlo
        have hxlo : (lo : ℝ) * Q ≤ (Q : ℝ) ^ 2 * x := by
          rw [hloR]
          have : ((X.c : ℝ) - X.r) / Q ≤ x := by rw [sub_div]; linarith
          rw [div_le_iff₀ hQR] at this
          nlinarith
        apply Real.le_sqrt_of_sq_le
        have : ((Nat.sqrt (lo * Q) : ℕ) : ℝ) ^ 2 ≤ ((lo * Q : ℕ) : ℝ) := by exact_mod_cast hsq
        push_cast at this
        linarith
    · rw [hQx]
      set hi := (X.c + X.r).toNat
      have hsq := Nat.lt_succ_sqrt' (hi * Q)
      have hsqR : ((hi * Q : ℕ) : ℝ) < ((Nat.sqrt (hi * Q) + 1 : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast hsq
      rcases le_or_gt x 0 with hx0 | hx0
      · rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith)]; positivity
      · have hhi : ((hi : ℕ) : ℤ) = X.c + X.r := by
          refine Int.toNat_of_nonneg ?_
          have : (0 : ℝ) ≤ (X.c : ℝ) + X.r := by
            have : x ≤ ((X.c : ℝ) + X.r) / Q := by rw [add_div]; linarith
            have : 0 < ((X.c : ℝ) + X.r) / Q := lt_of_lt_of_le hx0 this
            exact (div_pos_iff_of_pos_right hQR).mp this |>.le
          exact_mod_cast this
        have hhiR : (hi : ℝ) = X.c + X.r := by exact_mod_cast hhi
        have hxhi : (Q : ℝ) ^ 2 * x ≤ (hi : ℝ) * Q := by
          rw [hhiR]
          have : x ≤ ((X.c : ℝ) + X.r) / Q := by rw [add_div]; linarith
          rw [le_div_iff₀ hQR] at this
          nlinarith
        rw [Real.sqrt_le_left (by positivity)]
        push_cast at hsqR ⊢
        linarith
  · rw [if_neg hQ1] at h
    cases h

/-! ### Taylor polynomials -/

theorem fact_eq : ∀ n, fact n = Nat.factorial n
  | 0 => rfl
  | n + 1 => by simp [fact, fact_eq n, Nat.factorial_succ]

theorem cosSeries_encloses {Q : ℕ} (hQ : 0 < Q) {X2 : Fx} {x : ℝ}
    (hX2 : X2.Encloses Q (x * x)) : ∀ k,
    (cosSeries Q X2 k).1.Encloses Q ((-1) ^ k * x ^ (2 * k) / (2 * k).factorial) ∧
    (cosSeries Q X2 k).2.Encloses Q
      (∑ j ∈ Finset.range k, (-1) ^ j * x ^ (2 * j) / (2 * j).factorial)
  | 0 => ⟨by simp only [cosSeries]; simpa using ofInt_encloses hQ 1, by
      simpa [cosSeries] using zero_encloses⟩
  | k + 1 => by
    obtain ⟨ht, hs⟩ := cosSeries_encloses hQ hX2 k
    simp only [cosSeries]
    refine ⟨?_, ?_⟩
    · have h := divNat_encloses hQ (by positivity : 0 < (2 * k + 1) * (2 * k + 2))
        (neg_encloses (mul_encloses hQ ht hX2))
      have e : (-1 : ℝ) ^ (k + 1) * x ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ) =
          -((-1) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ) * (x * x)) /
            (((2 * k + 1) * (2 * k + 2) : ℕ) : ℝ) := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        field_simp
        ring
      rw [e]; exact h
    · rw [Finset.sum_range_succ]
      exact add_encloses hs ht

theorem sinSeries_encloses {Q : ℕ} (hQ : 0 < Q) {X X2 : Fx} {x : ℝ} (hX : X.Encloses Q x)
    (hX2 : X2.Encloses Q (x * x)) : ∀ k,
    (sinSeries Q X X2 k).1.Encloses Q ((-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1).factorial) ∧
    (sinSeries Q X X2 k).2.Encloses Q
      (∑ j ∈ Finset.range k, (-1) ^ j * x ^ (2 * j + 1) / (2 * j + 1).factorial)
  | 0 => ⟨by simp only [sinSeries]; simpa using hX, by simpa [sinSeries] using zero_encloses⟩
  | k + 1 => by
    obtain ⟨ht, hs⟩ := sinSeries_encloses hQ hX hX2 k
    simp only [sinSeries]
    refine ⟨?_, ?_⟩
    · have h := divNat_encloses hQ (by positivity : 0 < (2 * k + 2) * (2 * k + 3))
        (neg_encloses (mul_encloses hQ ht hX2))
      have e : (-1 : ℝ) ^ (k + 1) * x ^ (2 * (k + 1) + 1) / ((2 * (k + 1) + 1).factorial : ℝ) =
          -((-1) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) * (x * x)) /
            (((2 * k + 2) * (2 * k + 3) : ℕ) : ℝ) := by
        rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Nat.factorial_succ,
          Nat.factorial_succ]
        push_cast
        field_simp
        ring
      rw [e]; exact h
    · rw [Finset.sum_range_succ]
      exact add_encloses hs ht

/-- `|x| < m` from `2|x|² ≤ 2B² ≤ m²`. -/
theorem abs_lt_of_sq_bound {x B m : ℝ} (hm : 0 < m) (hx : |x| ≤ B) (hB : 2 * B ^ 2 ≤ m ^ 2) :
    |x| < m := by
  have h0 := abs_nonneg x
  nlinarith [sq_nonneg (|x| - m), sq_nonneg B]

/-- The factor `0 ≤ (1 − (y/m)²)⁻¹ ≤ 2` when `2y² ≤ m²`. -/
theorem inv_one_sub_bounds {y m : ℝ} (hm : 0 < m) (hym : 2 * y ^ 2 ≤ m ^ 2) :
    0 ≤ (1 - (y / m) ^ 2)⁻¹ ∧ (1 - (y / m) ^ 2)⁻¹ ≤ 2 := by
  have hsq : (y / m) ^ 2 ≤ 1 / 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    linarith
  refine ⟨inv_nonneg.mpr (by linarith), ?_⟩
  rw [inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- `y^m/m!·(1 − (y/(m+1))²)⁻¹ ≤ 2B^m/m!` for `0 ≤ y ≤ B`, `2B² ≤ (m+1)²`. -/
theorem taylor_rem_le {y B : ℝ} (m : ℕ) (hy : 0 ≤ y) (hyB : y ≤ B)
    (hB : 2 * B ^ 2 ≤ ((m : ℝ) + 1) ^ 2) :
    y ^ m / m.factorial * (1 - (y / ((m : ℝ) + 1)) ^ 2)⁻¹ ≤ 2 * B ^ m / m.factorial := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  obtain ⟨h0, h2⟩ := inv_one_sub_bounds (y := y) hm (by nlinarith [mul_self_le_mul_self hy hyB])
  have hf : (0 : ℝ) < m.factorial := by positivity
  calc y ^ m / m.factorial * (1 - (y / ((m : ℝ) + 1)) ^ 2)⁻¹
      ≤ B ^ m / m.factorial * 2 :=
        mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ hy hyB _) hf.le) h2 h0
          (div_nonneg (pow_nonneg (hy.trans hyB) _) hf.le)
    _ = 2 * B ^ m / m.factorial := by ring

/-- The `cos` Taylor bound in the form the grid uses: `|cos x − P_N(x)| ≤ 2B^{2N}/(2N)!` for
`|x| ≤ B`, `2B² ≤ (2N+1)²`. -/
theorem cos_taylor_bound {x B : ℝ} (N : ℕ) (hx : |x| ≤ B) (hB : 2 * B ^ 2 ≤ (2 * N + 1) ^ 2) :
    |Real.cos x - ∑ k ∈ Finset.range N, (-1) ^ k * x ^ (2 * k) / (2 * k).factorial| ≤
      2 * B ^ (2 * N) / (2 * N).factorial := by
  have hm : (0 : ℝ) < 2 * N + 1 := by positivity
  have h := cos_sub_sum_le |x| N (abs_nonneg x) (abs_lt_of_sq_bound hm hx hB)
  have heven : ∀ k, |x| ^ (2 * k) = x ^ (2 * k) := fun k ↦ Even.pow_abs ⟨k, by ring⟩ x
  simp only [heven, Real.cos_abs] at h
  refine h.trans ?_
  rw [← heven]
  have := taylor_rem_le (2 * N) (abs_nonneg x) hx (by push_cast; linarith)
  push_cast at this
  exact this

/-- The `sin` Taylor bound in the form the grid uses: `|sin x − P_N(x)| ≤ 2B^{2N+1}/(2N+1)!` for
`|x| ≤ B`, `2B² ≤ (2N+2)²`. -/
theorem sin_taylor_bound {x B : ℝ} (N : ℕ) (hx : |x| ≤ B) (hB : 2 * B ^ 2 ≤ (2 * N + 2) ^ 2) :
    |Real.sin x - ∑ k ∈ Finset.range N, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1).factorial| ≤
      2 * B ^ (2 * N + 1) / (2 * N + 1).factorial := by
  have hm : (0 : ℝ) < 2 * N + 2 := by positivity
  have hpos : ∀ y : ℝ, 0 ≤ y → |y| ≤ B →
      |Real.sin y - ∑ k ∈ Finset.range N, (-1) ^ k * y ^ (2 * k + 1) / (2 * k + 1).factorial| ≤
        2 * B ^ (2 * N + 1) / (2 * N + 1).factorial := by
    intro y hy hyB
    have hyB' : y ≤ B := by rwa [abs_of_nonneg hy] at hyB
    have hlt : y < 2 * N + 2 := by
      have := abs_lt_of_sq_bound hm hyB hB; rwa [abs_of_nonneg hy] at this
    refine (sin_sub_sum_le y N hy hlt).trans ?_
    have := taylor_rem_le (2 * N + 1) hy hyB' (by push_cast; linarith)
    push_cast at this
    rwa [show (2 * (N : ℝ) + 1 + 1) = 2 * N + 2 by ring] at this
  rcases le_or_gt 0 x with hx0 | hx0
  · exact hpos x hx0 hx
  · have h := hpos (-x) (by linarith) (by rwa [abs_neg])
    have hodd : ∀ k, (-x) ^ (2 * k + 1) = -x ^ (2 * k + 1) := fun k ↦ Odd.neg_pow ⟨k, rfl⟩ x
    simp only [hodd, Real.sin_neg, mul_neg, neg_div, Finset.sum_neg_distrib] at h
    rwa [show -Real.sin x - -∑ k ∈ Finset.range N, (-1) ^ k * x ^ (2 * k + 1) /
        (2 * k + 1).factorial = -(Real.sin x - ∑ k ∈ Finset.range N, (-1) ^ k *
        x ^ (2 * k + 1) / (2 * k + 1).factorial) by ring, abs_neg] at h

/-- The grid remainder: `2B^m/m! ≤ remainder Q D m / Q` for `0 ≤ B ≤ 1/D`. -/
theorem remainder_spec {Q D m : ℕ} {B : ℝ} (hQ : 0 < Q) (hD : 0 < D) (hB0 : 0 ≤ B)
    (hB : B ≤ 1 / D) : 2 * B ^ m / m.factorial ≤ (remainder Q D m : ℝ) / Q := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hK : 0 < D ^ m * fact m := by rw [fact_eq]; positivity
  have hceil : 2 * Q ≤ remainder Q D m * (D ^ m * fact m) := le_ceilDiv_mul (2 * Q) hK
  rw [fact_eq] at hceil
  have hfR : (0 : ℝ) < m.factorial := by positivity
  have hceilR : 2 * (Q : ℝ) ≤ (remainder Q D m : ℝ) * ((D : ℝ) ^ m * m.factorial) := by
    exact_mod_cast hceil
  calc 2 * B ^ m / m.factorial ≤ 2 * (1 / (D : ℝ)) ^ m / m.factorial := by
        gcongr
    _ = 2 / ((D : ℝ) ^ m * m.factorial) := by rw [one_div_pow, mul_one_div, div_div]
    _ ≤ (remainder Q D m : ℝ) / Q := by
        rw [div_le_div_iff₀ (by positivity) hQR]; linarith

/-- Combine a polynomial enclosure and the Taylor bound into an enclosure of the function. -/
theorem encloses_of_poly {Q : ℕ} {s : Fx} {f p E : ℝ} {R : ℕ} (hs : s.Encloses Q p)
    (hfp : |f - p| ≤ E) (hE : E ≤ (R : ℝ) / Q) : (addRad s R).Encloses Q f := by
  refine ⟨?_, hs.2⟩
  have hs := hs.1
  simp only [addRad, Nat.cast_add, add_div]
  calc |f - (s.c : ℝ) / Q| ≤ |f - p| + |p - (s.c : ℝ) / Q| := abs_sub_le _ _ _
    _ ≤ (R : ℝ) / Q + (s.r : ℝ) / Q := add_le_add (hfp.trans hE) hs
    _ = _ := by ring

/-- What `taylorOk` gives: a positive grid, and `|x| ≤ B ≤ 1/D` with `2B² ≤ (2N+1)²`. -/
theorem taylorOk_spec {Q D N : ℕ} {X : Fx} (hc : taylorOk Q D N X = true) :
    0 < Q ∧ 0 < D ∧ 0 ≤ (X.absBound : ℝ) / Q ∧ (X.absBound : ℝ) / Q ≤ 1 / D ∧
      2 * ((X.absBound : ℝ) / Q) ^ 2 ≤ (2 * N + 1) ^ 2 := by
  simp only [taylorOk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hQ1, hD1⟩, hN1⟩, hB⟩ := hc
  have hQ : 0 < Q := Nat.le_of_ble_eq_true hQ1
  have hD : 0 < D := Nat.le_of_ble_eq_true hD1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.le_of_ble_eq_true hN1
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hBQ : (D : ℝ) * X.absBound ≤ Q := by exact_mod_cast Nat.le_of_ble_eq_true hB
  have hBD : (X.absBound : ℝ) / Q ≤ 1 / D := by
    rw [div_le_div_iff₀ hQR (by positivity)]; linarith
  have hB1 : (X.absBound : ℝ) / Q ≤ 1 := hBD.trans (by rw [div_le_one (by positivity)]; exact hDR)
  have hB0 : 0 ≤ (X.absBound : ℝ) / Q := by positivity
  refine ⟨hQ, hD, hB0, hBD, ?_⟩
  have : ((X.absBound : ℝ) / Q) ^ 2 ≤ 1 := pow_le_one₀ hB0 hB1
  nlinarith

theorem cosTaylor_encloses {Q D N : ℕ} {X C : Fx} {x : ℝ} (hX : X.Encloses Q x)
    (h : cosTaylor Q D N X = some C) : C.Encloses Q (Real.cos x) := by
  unfold cosTaylor at h
  by_cases hc : taylorOk Q D N X = true
  · rw [if_pos hc] at h
    cases h
    obtain ⟨hQ, hD, hB0, hBD, hB⟩ := taylorOk_spec hc
    have hs := (cosSeries_encloses hQ (mul_encloses hQ hX hX) N).2
    exact tighten_encloses hQ (encloses_of_poly hs (cos_taylor_bound N (abs_le_absBound hX) hB)
      (remainder_spec hQ hD hB0 hBD))
  · rw [if_neg hc] at h
    cases h

theorem sinTaylor_encloses {Q D N : ℕ} {X S : Fx} {x : ℝ} (hX : X.Encloses Q x)
    (h : sinTaylor Q D N X = some S) : S.Encloses Q (Real.sin x) := by
  unfold sinTaylor at h
  by_cases hc : taylorOk Q D N X = true
  · rw [if_pos hc] at h
    cases h
    obtain ⟨hQ, hD, hB0, hBD, hB⟩ := taylorOk_spec hc
    have hB' : 2 * ((X.absBound : ℝ) / Q) ^ 2 ≤ (2 * N + 2) ^ 2 := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    have hs := (sinSeries_encloses hQ hX (mul_encloses hQ hX hX) N).2
    exact tighten_encloses hQ (encloses_of_poly hs (sin_taylor_bound N (abs_le_absBound hX) hB')
      (remainder_spec hQ hD hB0 hBD))
  · rw [if_neg hc] at h
    cases h

theorem taylorPair_encloses {Q D N : ℕ} {X : Fx} {x : ℝ} {cs : Fx × Fx} (hX : X.Encloses Q x)
    (h : taylorPair Q D N X = some cs) :
    cs.1.Encloses Q (Real.cos x) ∧ cs.2.Encloses Q (Real.sin x) := by
  simp only [taylorPair, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨C, hC, S, hS, rfl⟩ := h
  exact ⟨cosTaylor_encloses hX hC, sinTaylor_encloses hX hS⟩

theorem rotate_encloses {Q : ℕ} (hQ : 0 < Q) {a b : Fx × Fx} {α β : ℝ}
    (ha : a.1.Encloses Q (Real.cos α) ∧ a.2.Encloses Q (Real.sin α))
    (hb : b.1.Encloses Q (Real.cos β) ∧ b.2.Encloses Q (Real.sin β)) :
    (rotate Q a b).1.Encloses Q (Real.cos (α + β)) ∧
      (rotate Q a b).2.Encloses Q (Real.sin (α + β)) := by
  rw [Real.cos_add, Real.sin_add]
  exact ⟨tighten_encloses hQ
      (sub_encloses (mul_encloses hQ ha.1 hb.1) (mul_encloses hQ ha.2 hb.2)),
    tighten_encloses hQ (add_encloses (mul_encloses hQ ha.2 hb.1) (mul_encloses hQ ha.1 hb.2))⟩

/-! ### Reduction by `k·π/2` -/

theorem quadrantCos_encloses {Q : ℕ} {C S : Fx} {y : ℝ} (q : ℤ) {j : ℕ} (hj : j < 4)
    (hC : C.Encloses Q (Real.cos y)) (hS : S.Encloses Q (Real.sin y)) :
    (quadrantCos j C S).Encloses Q (Real.cos (y + (4 * (q : ℝ) + j) * (Real.pi / 2))) := by
  interval_cases j
  · simpa [quadrantCos, cos_quad0] using hC
  · simpa [quadrantCos, cos_quad1] using neg_encloses hS
  · have := cos_quad2 y q
    simp only [quadrantCos, Nat.cast_ofNat]
    rw [this]; exact neg_encloses hC
  · have := cos_quad3 y q
    simp only [quadrantCos, Nat.cast_ofNat]
    rw [this]; exact hS

theorem quadrantSin_encloses {Q : ℕ} {C S : Fx} {y : ℝ} (q : ℤ) {j : ℕ} (hj : j < 4)
    (hC : C.Encloses Q (Real.cos y)) (hS : S.Encloses Q (Real.sin y)) :
    (quadrantSin j C S).Encloses Q (Real.sin (y + (4 * (q : ℝ) + j) * (Real.pi / 2))) := by
  interval_cases j
  · simpa [quadrantSin, sin_quad0] using hS
  · simpa [quadrantSin, sin_quad1] using hC
  · have := sin_quad2 y q
    simp only [quadrantSin, Nat.cast_ofNat]
    rw [this]; exact neg_encloses hS
  · have := sin_quad3 y q
    simp only [quadrantSin, Nat.cast_ofNat]
    rw [this]; exact neg_encloses hC

/-- The reduction identity: `x = (x − k·π/2) + (4⌊k/4⌋ + (k mod 4))·π/2`. -/
theorem quarter_reduce_eq (x : ℝ) (k : ℤ) :
    x = (x - k * (Real.pi / 2)) +
      (4 * ((k / 4 : ℤ) : ℝ) + ((k % 4).toNat : ℕ)) * (Real.pi / 2) := by
  have hmod : ((k % 4).toNat : ℤ) = k % 4 := Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
  have hk : (4 * ((k / 4 : ℤ) : ℝ) + (((k % 4).toNat : ℕ) : ℝ)) = (k : ℝ) := by
    have h := Int.mul_ediv_add_emod k 4
    have h' : ((4 * (k / 4) + ((k % 4).toNat : ℤ) : ℤ) : ℝ) = (k : ℝ) := by rw [hmod, h]
    push_cast at h'
    exact h'
  rw [hk]; ring

theorem toNat_emod_four_lt (k : ℤ) : (k % 4).toNat < 4 := by
  have h1 := Int.emod_nonneg k (by norm_num : (4 : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 4)
  omega

/-- `reduce` is sound given a sound evaluator `g` for the reduced argument. -/
theorem reduce_encloses {Q : ℕ} (hQ : 0 < Q) {H X : Fx} {g : Fx → Option (Fx × Fx)} {x : ℝ}
    {cs : Fx × Fx} (hH : H.Encloses Q (Real.pi / 2))
    (hg : ∀ Y y cs, Y.Encloses Q y → g Y = some cs →
      cs.1.Encloses Q (Real.cos y) ∧ cs.2.Encloses Q (Real.sin y))
    (hX : X.Encloses Q x) (h : reduce Q H g X = some cs) :
    cs.1.Encloses Q (Real.cos x) ∧ cs.2.Encloses Q (Real.sin x) := by
  simp only [reduce, reduce.reduceAt, Option.map_eq_some_iff] at h
  obtain ⟨cs', hcs', rfl⟩ := h
  set k := nearestQuarter X H
  obtain ⟨eC, eS⟩ := hg _ _ cs' (tighten_encloses hQ (sub_encloses hX (smul_encloses k hH))) hcs'
  have hj := toNat_emod_four_lt k
  have hx := quarter_reduce_eq x k
  refine ⟨?_, ?_⟩
  · rw [hx]; exact quadrantCos_encloses (k / 4) hj eC eS
  · rw [hx]; exact quadrantSin_encloses (k / 4) hj eC eS

theorem cosSin_encloses {Q : ℕ} (hQ : 0 < Q) {H X : Fx} {x : ℝ} {cs : Fx × Fx}
    (hH : H.Encloses Q (Real.pi / 2)) (hX : X.Encloses Q x) (h : cosSin Q H X = some cs) :
    cs.1.Encloses Q (Real.cos x) ∧ cs.2.Encloses Q (Real.sin x) :=
  reduce_encloses hQ hH (fun _ _ _ hY h ↦ taylorPair_encloses hY h) hX h

/-! ### The table of `cos`/`sin` at multiples of `1/128` -/

theorem tableScale_pos : 0 < tableScale := by decide

/-- Every entry `i` of a table encloses `(cos(i/128), sin(i/128))`. -/
def TableValid (Q : ℕ) (tbl : Array (Option (Fx × Fx))) : Prop :=
  ∀ i (hi : i < tbl.size) cs, tbl[i] = some cs →
    cs.1.Encloses Q (Real.cos ((i : ℝ) / tableScale)) ∧
      cs.2.Encloses Q (Real.sin ((i : ℝ) / tableScale))

theorem trigTable_valid {Q : ℕ} (hQ : 0 < Q) {H : Fx} (hH : H.Encloses Q (Real.pi / 2)) :
    TableValid Q (trigTable Q H) := by
  intro i hi cs h
  simp only [trigTable, Array.getElem_ofFn] at h
  have hX := ofRat_encloses hQ tableScale_pos false (a := i)
  rw [sfrac_false_div] at hX
  exact cosSin_encloses hQ hH hX h

theorem join_getElem?_spec {arr : Array (Option (Fx × Fx))} {i : ℕ} {cs : Fx × Fx}
    (h : arr[i]?.join = some cs) : ∃ hi : i < arr.size, arr[i] = some cs := by
  obtain ⟨o, ho, hcs⟩ := Option.bind_eq_some_iff.mp (by simpa [Option.join] using h)
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ho
  exact ⟨hi, hcs⟩

/-- `±|j|/b` with the sign of `j` is `j/b`. -/
theorem sfrac_sign_natAbs (j : ℤ) (b : ℕ) : sfrac (decide (j < 0)) j.natAbs b = (j : ℝ) / b := by
  rw [sfrac, Nat.cast_natAbs, Int.cast_abs]
  by_cases hj : j < 0
  · rw [abs_of_neg (by exact_mod_cast hj)]; simp [hj, neg_div]
  · rw [abs_of_nonneg (by exact_mod_cast not_lt.mp hj)]; simp [hj]

theorem trigAt_spec {Q : ℕ} {tbl : Array (Option (Fx × Fx))} (hT : TableValid Q tbl) {j : ℤ}
    {cs : Fx × Fx} (h : trigAt tbl j = some cs) :
    cs.1.Encloses Q (Real.cos ((j : ℝ) / tableScale)) ∧
      cs.2.Encloses Q (Real.sin ((j : ℝ) / tableScale)) := by
  simp only [trigAt, Option.map_eq_some_iff] at h
  obtain ⟨cs', h1, rfl⟩ := h
  obtain ⟨hi, hv⟩ := join_getElem?_spec h1
  obtain ⟨eC, eS⟩ := hT _ hi cs' hv
  have habs : ((j.natAbs : ℕ) : ℝ) = |(j : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs] at eC eS
  by_cases hj : j < 0
  · have hjR : (j : ℝ) < 0 := by exact_mod_cast hj
    rw [abs_of_neg hjR, neg_div, Real.cos_neg] at eC
    rw [abs_of_neg hjR, neg_div, Real.sin_neg] at eS
    simp only [hj, if_true]
    exact ⟨eC, by simpa using neg_encloses eS⟩
  · have hjR : (0 : ℝ) ≤ j := by exact_mod_cast not_lt.mp hj
    rw [abs_of_nonneg hjR] at eC eS
    simp only [hj, if_false]
    exact ⟨eC, eS⟩

theorem nearTable_encloses {Q : ℕ} (hQ : 0 < Q) {tbl : Array (Option (Fx × Fx))}
    (hT : TableValid Q tbl) {Y : Fx} {y : ℝ} {cs : Fx × Fx} (hY : Y.Encloses Q y)
    (h : nearTable Q tbl Y = some cs) :
    cs.1.Encloses Q (Real.cos y) ∧ cs.2.Encloses Q (Real.sin y) := by
  simp only [nearTable, nearTable.nearAt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  set j := tableIndex Q Y
  have hJ := ofRat_encloses hQ tableScale_pos (decide (j < 0)) (a := j.natAbs)
  rw [sfrac_sign_natAbs] at hJ
  have hR := tighten_encloses hQ (sub_encloses hY hJ)
  have := rotate_encloses hQ (trigAt_spec hT ha) (taylorPair_encloses hR hb)
  rwa [add_sub_cancel] at this

theorem cosSinT_encloses {Q : ℕ} (hQ : 0 < Q) {H X : Fx} {tbl : Array (Option (Fx × Fx))}
    {x : ℝ} {cs : Fx × Fx} (hH : H.Encloses Q (Real.pi / 2)) (hT : TableValid Q tbl)
    (hX : X.Encloses Q x) (h : cosSinT Q H tbl X = some cs) :
    cs.1.Encloses Q (Real.cos x) ∧ cs.2.Encloses Q (Real.sin x) :=
  reduce_encloses hQ hH (fun _ _ _ hY h ↦ nearTable_encloses hQ hT hY h) hX h

end Fx

end Native
