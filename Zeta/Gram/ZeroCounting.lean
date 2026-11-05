/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.ArgZeta.Explicit
public import Zeta.Gram.Averaging
public import Zeta.Gram.Block
public import Zeta.RiemannVonMangoldt.Main
public import Mathlib.Topology.Order.IntermediateValue
public import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.Union

/-!
# Turing's method: counting zeros at a gram point

The gram points `gramPoint n` (the unique `t ≥ 7` with `θ(t) = n·π`), and Turing's upper bound
`N(gramPoint n) ≤ n + 1` on the zero-counting function, from a run of consecutive gram intervals
each containing a zero. The bound is the Gram-block averaging lemma of `Zeta/Gram/Averaging.lean`
against the Lehman bound on `∫ S`.

## Main definitions

- `gramPoint`: the `n`-th gram point.

## Main results

- `gramPoint_theta_eq`, `gramPoint_seven_le`, `strictMono_gramPoint`, `gramPoint_le_iff`,
  `lt_gramPoint_iff`, `gramPoint_lt_iff`: the defining property of the gram points, and their
  order theory.
- `riemannZeta.N_mono`, `riemannZeta.N_add_one_le_of_zero`: monotonicity of `N`, and the jump at
  a zero.
- `riemannZeta.N_le_of_gramPoints`: Turing's bound `N(gramPoint n) ≤ n + 1`.
- `riemannZeta.N_le_of_certifiedGramBlockSeq`: the same bound from a `CertifiedGramBlockSeq`.
- `riemannSiegelTheta_zero`, `riemannSiegelTheta_nonpos_of_mem_Icc`: `θ(0) = 0` and `θ ≤ 0` on
  `[0, 7]`.
-/
@[expose] public section


open Real Set Filter Zeta.Certificates Complex MeasureTheory

/-- Past `7`, where `θ` is strictly increasing to `∞`, the equation `θ(t) = n·π` has a unique
solution. -/
theorem existsUnique_gramPoint (n : ℕ) :
    ∃! x ∈ Ici (7 : ℝ), riemannSiegelTheta x = n * π := by
  have hi := isPreconnected_Ici.intermediate_value_Ici (a := 7) (by simp)
    (by simpa using ⟨7, by simp⟩) continuousOn_riemannSiegelTheta_gramDomain
    tendsto_riemannSiegelTheta_atTop
  have : n * π ∈ Ici (riemannSiegelTheta 7) := by grind [riemannSiegelTheta_seven_le n]
  obtain ⟨x, hx, hθx⟩ := hi this
  refine ⟨x, ⟨hx, hθx⟩, fun y ⟨hy, hθy⟩ ↦ ?_⟩
  have := strictMonoOn_riemannSiegelTheta_gramDomain hx hy
  have := strictMonoOn_riemannSiegelTheta_gramDomain hy hx
  grind

/-- **The `n`-th gram point**: the unique `t ≥ 7` with `θ(t) = n·π`. -/
noncomputable def gramPoint (n : ℕ) : ℝ := (existsUnique_gramPoint n).choose

/-- The defining property of the `n`-th gram point. -/
theorem gramPoint_theta_eq (n : ℕ) : riemannSiegelTheta (gramPoint n) = n * π :=
  (existsUnique_gramPoint n).choose_spec.1.2

/-- Gram points lie in the monotonicity domain `[7, ∞)`. -/
theorem gramPoint_seven_le (n : ℕ) : 7 ≤ gramPoint n :=
  (existsUnique_gramPoint n).choose_spec.1.1

/-- Gram points are positive. -/
theorem gramPoint_pos (n : ℕ) : 0 < gramPoint n := by
  linarith [gramPoint_seven_le n]

/-- The gram points increase strictly with their index. -/
theorem strictMono_gramPoint : StrictMono gramPoint := fun m n hmn ↦ by
  rw [← strictMonoOn_riemannSiegelTheta_gramDomain.lt_iff_lt
      (Set.mem_Ici.mpr (gramPoint_seven_le m))
      (Set.mem_Ici.mpr (gramPoint_seven_le n)), gramPoint_theta_eq, gramPoint_theta_eq]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hmn) pi_pos

/-- Past `7` — where `θ` is strictly monotone — the `n`-th gram point lies weakly left of `t`
exactly when `θ(t)` has reached `n·π`. -/
theorem gramPoint_le_iff {n : ℕ} {t : ℝ} (ht : 7 ≤ t) :
    gramPoint n ≤ t ↔ (n : ℝ) * π ≤ riemannSiegelTheta t := by
  rw [← gramPoint_theta_eq n]
  exact (strictMonoOn_riemannSiegelTheta_gramDomain.le_iff_le
    (mem_Ici.mpr (gramPoint_seven_le n)) (mem_Ici.mpr ht)).symm

/-- Past `7`, `t` lies strictly left of the `n`-th gram point exactly when `θ(t) < n·π`. -/
theorem lt_gramPoint_iff {n : ℕ} {t : ℝ} (ht : 7 ≤ t) :
    t < gramPoint n ↔ riemannSiegelTheta t < (n : ℝ) * π :=
  lt_iff_lt_of_le_iff_le (gramPoint_le_iff ht)

/-- Past `7`, the `n`-th gram point lies strictly left of `t` exactly when `θ(t)` has passed
`n·π`. -/
theorem gramPoint_lt_iff {n : ℕ} {t : ℝ} (ht : 7 ≤ t) :
    gramPoint n < t ↔ (n : ℝ) * π < riemannSiegelTheta t := by
  rw [← gramPoint_theta_eq n]
  exact (strictMonoOn_riemannSiegelTheta_gramDomain.lt_iff_lt
    (mem_Ici.mpr (gramPoint_seven_le n)) (mem_Ici.mpr ht)).symm

/-- The half of `lt_gramPoint_iff` that needs no lower bound on `t`: a point whose `θ`-value has
not yet reached `n·π` lies below the `n`-th gram point. -/
theorem lt_gramPoint_of_theta_lt {n : ℕ} {t : ℝ} (h : riemannSiegelTheta t < (n : ℝ) * π) :
    t < gramPoint n :=
  not_le.1 fun hcon ↦
    absurd ((gramPoint_le_iff ((gramPoint_seven_le n).trans hcon)).mp hcon) (not_le.mpr h)

/-- The `ζ`-zeros of height in `Ioo 0 T` form a finite type (from `PrimeNumberTheoremAnd`). -/
noncomputable instance {T : ℝ} : Fintype (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :=
  (Kadiri.zeroes_rect_univ_positive_height_finite T).fintype

/-- `N T` is the (finite) sum of the orders of the `ζ`-zeros of height in `Ioo 0 T`. -/
lemma riemannZeta.N_eq_sum (T : ℝ) :
    riemannZeta.N T = ∑ ρ ∈ (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).toFinset,
      (riemannZeta.order ρ : ℝ) := by
  rw [riemannZeta.N, riemannZeta.zeroes_sum, tsum_fintype, ← Finset.sum_set_coe]
  exact Finset.sum_congr rfl fun _ _ ↦ one_mul _

/-- `N` is integer-valued, being a finite sum of (integer) zero orders. -/
lemma riemannZeta.exists_intCast_N (T : ℝ) : ∃ m : ℤ, riemannZeta.N T = m :=
  ⟨∑ ρ ∈ (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).toFinset, riemannZeta.order ρ, by
    rw [riemannZeta.N_eq_sum]; push_cast; rfl⟩

/-- Zeros of positive height have positive, hence nonnegative, order. -/
private lemma riemannZeta.order_nonneg_of_mem_toFinset {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).toFinset) :
    (0 : ℝ) ≤ (riemannZeta.order ρ : ℝ) := by
  exact_mod_cast (Kadiri.riemannZeta_order_pos_positiveHeightZero
    ⟨ρ, Set.mem_toFinset.1 hρ⟩).le

/-- The fractional gram phase `t ↦ {gramCoord a t}` is interval-integrable on `[a, b]`, for
`a, b ≥ 0`. -/
theorem intervalIntegrable_gramCoord {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t ↦ Int.fract (gramCoord a t)) volume a b := by
  have hsub : Set.uIoc a b ⊆ Set.Ici (0 : ℝ) := fun x hx ↦ ((le_min ha hb).trans_lt hx.1).le
  have hcont : ContinuousOn (fun t ↦ gramCoord a t) (Set.uIoc a b) :=
    ((continuousOn_riemannSiegelTheta.mono hsub).sub continuousOn_const).div_const _
  rw [intervalIntegrable_iff]
  refine .of_bound measure_Ioc_lt_top (measurable_fract.comp_aemeasurable
    (hcont.aestronglyMeasurable measurableSet_uIoc).aemeasurable).aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

/-- The set of `ζ`-zeros with imaginary part in `Ioo 0 τ` grows monotonically in the height `τ`. -/
private theorem riemannZeta.zeroes_rect_Ioo_subset {τ t : ℝ} (h : τ ≤ t) :
    riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 τ) ⊆
      riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 t) :=
  fun _ hz ↦ ⟨hz.1, Set.Ioo_subset_Ioo_right h hz.2.1, hz.2.2⟩

/-- The zero-counting function is monotone in the height. -/
theorem riemannZeta.N_mono : Monotone riemannZeta.N := fun τ t hτt ↦ by
  rw [riemannZeta.N_eq_sum, riemannZeta.N_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun _ hz ↦ Set.mem_toFinset.2 (zeroes_rect_Ioo_subset hτt (Set.mem_toFinset.1 hz)))
    fun _ hρ _ ↦ riemannZeta.order_nonneg_of_mem_toFinset hρ

/-- A critical-line zero at height `τ` makes `N` jump: `N(τ) + 1 ≤ N(t)` for every `t > τ`. -/
theorem riemannZeta.N_add_one_le_of_zero {τ t : ℝ} (hτ : 0 < τ)
    (h_zero : riemannZeta (1 / 2 + I * τ) = 0) (ht : τ < t) :
    riemannZeta.N τ + 1 ≤ riemannZeta.N t := by
  have him : (1 / 2 + I * (τ : ℂ)).im = τ := by simp
  have hmem : (1 / 2 + I * (τ : ℂ)) ∈ riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 t) :=
    ⟨Set.mem_univ _, by rw [him]; exact ⟨hτ, ht⟩, h_zero⟩
  -- the new zero sits at height exactly `τ`, so it is missing from the shorter rectangle
  have hnot : (1 / 2 + I * (τ : ℂ)) ∉
      (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 τ)).toFinset := fun hc ↦
    absurd (him ▸ (Set.mem_toFinset.1 hc).2.1).2 (lt_irrefl τ)
  have key := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun ρ ↦ (riemannZeta.order ρ : ℝ))
    (Finset.insert_subset (Set.mem_toFinset.2 hmem) fun _ hz ↦
      Set.mem_toFinset.2 (zeroes_rect_Ioo_subset ht.le (Set.mem_toFinset.1 hz)))
    fun _ hρ _ ↦ riemannZeta.order_nonneg_of_mem_toFinset hρ
  rw [Finset.sum_insert hnot] at key
  have h1 : (1 : ℝ) ≤ (riemannZeta.order (1 / 2 + I * (τ : ℂ)) : ℝ) := by
    exact_mod_cast Kadiri.riemannZeta_one_le_order_positiveHeightZero ⟨_, hmem⟩
  rw [riemannZeta.N_eq_sum, riemannZeta.N_eq_sum]
  linarith

/-- **Turing's bound on the zero count at a gram point.** If each of the `k + 1` gram intervals
above `gramPoint n` contains a critical-line zero, and the run is high enough (`hg`) and wide
enough (`h`) for the Lehman bound, then `N(gramPoint n) ≤ n + 1`. -/
theorem riemannZeta.N_le_of_gramPoints (n k : ℕ) (hg : 168 * π < gramPoint n)
    (h : (5 + (0.128 : ℝ) * (gramPoint (n + k + 1) / (2 * π)).log) <
      (gramPoint (n + k + 1) - gramPoint n) / 2)
    (hc : ∀ j < k + 1, ∃ t ∈ Ico (gramPoint (n + j)) (gramPoint (n + j + 1)),
      riemannZeta (1 / 2 + I * t) = 0) :
    riemannZeta.N (gramPoint n) ≤ n + 1 := by
  have hlt : gramPoint n < gramPoint (n + k + 1) := strictMono_gramPoint (by lia)
  have hg_le := hlt.le
  -- On the `j`-th gram interval the gram phase `x(t)` has integer part exactly `j`.
  have hX {j : ℕ} {t : ℝ} (ht : t ∈ Ico (gramPoint (n + j)) (gramPoint (n + j + 1))) :
      ⌊gramCoord (gramPoint n) t⌋ = j := by
    have h7 : (7 : ℝ) ≤ t := (gramPoint_seven_le _).trans ht.1
    have h1 := (gramPoint_le_iff h7).mp ht.1
    have h2 := (lt_gramPoint_iff h7).mp ht.2
    push_cast at h1 h2
    rw [Int.floor_eq_iff]
    simp only [gramCoord, gramPoint_theta_eq, Int.cast_natCast]
    rw [le_div_iff₀ pi_pos, div_lt_iff₀ pi_pos]
    constructor <;> linarith
  have hN {j : ℕ} {t : ℝ} (hj : j < k + 1)
      (ht : t ∈ Ico (gramPoint (n + j)) (gramPoint (n + j + 1))) :
      j ≤ riemannZeta.N t - riemannZeta.N (gramPoint n) := by
    induction j generalizing t with
    | zero => simpa using sub_nonneg.2 (riemannZeta.N_mono ht.1)
    | succ j ih =>
      obtain ⟨τ, hτ, h_zero⟩ := hc j (by grind)
      specialize ih (t := τ) (by grind) (by simpa [add_assoc] using hτ)
      push_cast
      linarith [riemannZeta.N_add_one_le_of_zero (τ := τ) (t := t)
        (by grind [gramPoint_pos (n + j)]) h_zero (by grind)]
  -- The gram intervals cover the block, so `⌊x(t)⌋` never overcounts the zeros gained since `gᵢ`.
  have hΔ {t : ℝ} (ht : t ∈ Set.Ico (gramPoint n) (gramPoint (n + k + 1))) :
      ⌊gramCoord (gramPoint n) t⌋ ≤ riemannZeta.N t - riemannZeta.N (gramPoint n) := by
    have hcov := Ico_subset_biUnion_Ico (k + 1) (fun j ↦ gramPoint (n + j))
      (by simpa [add_assoc] using ht)
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, ← add_assoc] at hcov
    obtain ⟨j, hj, htj⟩ := hcov
    rw [hX htj]
    exact_mod_cast hN hj htj
  -- `q = N(gᵢ) - n - 1` is an integer, so it suffices to squeeze it below `1`.
  suffices hq1 : riemannZeta.N (gramPoint n) - n - 1 < 1 by
    obtain ⟨M, hM⟩ := riemannZeta.exists_intCast_N (gramPoint n)
    rw [hM] at hq1 ⊢
    exact_mod_cast Int.lt_add_one_iff.mp
      (by exact_mod_cast (by push_cast; linarith : (M : ℝ) < (((n : ℤ) + 1 : ℤ) : ℝ) + 1))
  set q : ℝ := riemannZeta.N (gramPoint n) - n - 1 with hq
  -- At every ordinate carrying no zero (all but finitely many), `N t = θ(t)/π + 1 + S(t)`, so `hΔ`
  -- becomes the pointwise bound `q - {x(t)} ≤ S(t)`.
  have hS : (fun t ↦ q - Int.fract (gramCoord (gramPoint n) t))
      ≤ᵐ[volume.restrict (Icc (gramPoint n) (gramPoint (n + k + 1)))] argZeta := by
    filter_upwards [(finite_setOf_riemannZeta_zero_ray_Icc (gramPoint_pos n)
        hg_le).countable.ae_notMem <| volume.restrict (Icc (gramPoint n) (gramPoint (n + k + 1))),
      ae_restrict_mem measurableSet_Icc, Measure.ae_ne _ (gramPoint (n + k + 1))] with t ht ht' h_ne
    push Not at ht
    have ht_good := mt ht (by simpa using ht')
    push Not at ht_good
    have hΔt := hΔ (Set.mem_Ico.mpr ⟨ht'.1, ht'.2.lt_of_ne h_ne⟩)
    rw [riemannZeta.N_eq_of_forall_re_mem_Ico (by grind [gramPoint_pos n])
      fun σ hσ ↦ ht_good σ (by simpa using hσ.1)] at hΔt
    have hgx : gramCoord (gramPoint n) t = riemannSiegelTheta t / π - n := by
      rw [gramCoord, gramPoint_theta_eq]; field_simp
    rw [hq, Int.fract]
    linarith
  -- Integrating: Turing's averaging bound `∫{x} ≤ L/2` and Lehman's `|∫S| ≤ 5 + 0.128·log(g/2π)`
  -- together with the wideness hypothesis `h` squeeze `L·q < L`.
  have hfract := integral_fract_gramCoord_le (k := k + 1) (p := fun i ↦ gramPoint (n + i))
    (by simpa using (gramPoint_pos n).le) (fun _ _ ↦ strictMono_gramPoint (by lia))
    (strictMonoOn_riemannSiegelTheta_gramDomain.mono fun _ _ ↦ by grind [gramPoint_seven_le])
    (fun _ _ ↦ by simp [gramPoint_theta_eq]; ring)
  have hleh := (abs_le.mp (norm_integral_argZeta_le_five_unconditional hg hlt)).2
  have hIx := intervalIntegrable_gramCoord (gramPoint_pos n).le (gramPoint_pos (n + k + 1)).le
  have hint := intervalIntegral.integral_mono_ae_restrict hg_le
    (.sub intervalIntegrable_const hIx) (intervalIntegrable_argZeta (gramPoint_pos n) hg_le) hS
  rw [intervalIntegral.integral_sub intervalIntegrable_const hIx] at hint
  simp only [intervalIntegral.integral_const, smul_eq_mul, add_zero, ← add_assoc] at hint hfract
  rw [← mul_lt_mul_iff_right₀ (sub_pos.mpr hlt)]
  linarith

/-! ### The `CertifiedGramBlockSeq` counting bound -/

/-- `θ(0) = 0`. -/
theorem riemannSiegelTheta_zero : riemannSiegelTheta 0 = 0 := by
  unfold riemannSiegelTheta argVariation
  simp only [zero_div, zero_mul, sub_zero]
  split <;> simp

/-- `θ ≤ 0` on `[0, 7]`. -/
theorem riemannSiegelTheta_nonpos_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 7) :
    riemannSiegelTheta x ≤ 0 := by
  obtain ⟨hx0, hx7⟩ := hx
  have hb : (0 : ℝ) ≤ x / 7 := by positivity
  have hconv := convexOn_riemannSiegelTheta.2 Set.self_mem_Ici
    (Set.mem_Ici.2 (by norm_num : (0 : ℝ) ≤ 7)) (by linarith : (0 : ℝ) ≤ 1 - x / 7) hb (by ring)
  rw [show (1 - x / 7) • (0 : ℝ) + (x / 7) • (7 : ℝ) = x by simp only [smul_eq_mul]; ring] at hconv
  simp only [riemannSiegelTheta_zero, smul_eq_mul, mul_zero, zero_add] at hconv
  nlinarith [(by simpa using riemannSiegelTheta_seven_le 0 : riemannSiegelTheta 7 ≤ 0)]

namespace Zeta.Certificates

/-- The gram point `gramPoint G.idx` lies strictly right of the certified left bracket. -/
theorem GramPoint.certificate_left_lt_gramPoint {G : GramPoint} (h : G.Certificate) :
    G.fst < gramPoint G.idx :=
  lt_gramPoint_of_theta_lt (G.certificate_theta_left_lt h)

/-- The gram point `gramPoint G.idx` lies strictly left of the certified right bracket. -/
theorem GramPoint.certificate_gramPoint_lt_right {G : GramPoint} (h : G.Certificate) :
    gramPoint G.idx < G.snd := by
  have hgt := G.certificate_theta_right_gt h
  have hpos : (0 : ℝ) < riemannSiegelTheta G.snd := lt_of_le_of_lt (by positivity) hgt
  refine (gramPoint_lt_iff (not_lt.mp fun hcon ↦ ?_)).mpr hgt
  linarith [riemannSiegelTheta_nonpos_of_mem_Icc ⟨h.snd_nonneg, hcon.le⟩]

/-- A certified gram block brackets a genuine zero of `ζ` on the critical line, located strictly
between the two gram points `gramPoint B.left.idx` and `gramPoint B.right.idx`. -/
theorem GramBlock.certificate_exists_zero {B : GramBlock} (h : B.Certificate) :
    ∃ t ∈ Set.Ico (gramPoint B.left.idx) (gramPoint B.right.idx),
      riemannZeta (1 / 2 + I * t) = 0 := by
  obtain ⟨z, hz_mem, hz_left, hz_right⟩ := h.contains_zero
  obtain ⟨t, ht_mem, ht_zero⟩ := h.has_zero z hz_mem
  refine ⟨t, ⟨?_, ?_⟩, ht_zero⟩
  · linarith [ht_mem.1, hz_left.1, B.left.certificate_gramPoint_lt_right h.left_certificate]
  · linarith [ht_mem.2, hz_right.2, B.right.certificate_left_lt_gramPoint h.right_certificate]

/-- The head block's left bracket lies below the gram point `gramPoint minIdx`. -/
theorem CertifiedGramBlockSeq.head_left_le_gramPoint (C : CertifiedGramBlockSeq) :
    (C.blocks.head C.non_empty).left.fst ≤ gramPoint C.minIdx :=
  (GramPoint.certificate_left_lt_gramPoint
    (C.cert _ (List.head_mem C.non_empty)).left_certificate).le

end Zeta.Certificates

/-- **The `CertifiedGramBlockSeq` version of `riemannZeta.N_le_of_gramPoints`**: a certified
sequence of gram blocks bounds the zero count at its head gram point,
`N(gramPoint S.minIdx) ≤ S.minIdx + 1`. No zero-freeness (ordinate) obligation is needed. -/
theorem riemannZeta.N_le_of_certifiedGramBlockSeq (S : CertifiedGramBlockSeq) :
    riemannZeta.N (gramPoint S.minIdx) ≤ S.minIdx + 1 := by
  have hLpos : 0 < S.blocks.length := List.length_pos_of_ne_nil S.non_empty
  have hlen1 : S.blocks.length - 1 < S.blocks.length := by lia
  set n := (S.blocks.head S.non_empty).left.idx with hn_def
  set k := S.blocks.length - 1 with hk_def
  have hcertHead : (S.blocks.head S.non_empty).Certificate := S.cert _ (List.head_mem S.non_empty)
  have hcertLast : (S.blocks.getLast S.non_empty).Certificate :=
    S.cert _ (List.getLast_mem S.non_empty)
  have hlast_lidx : (S.blocks.getLast S.non_empty).left.idx = n + k := by
    rw [List.getLast_eq_getElem S.non_empty,
      S.getElem_left_idx (S.blocks.length - 1) hlen1, ← hn_def]
  have hlast_ridx : (S.blocks.getLast S.non_empty).right.idx = n + k + 1 := by
    have := (S.blocks.getLast S.non_empty).seq
    lia
  -- The hypotheses of `riemannZeta.N_le_of_gramPoints`.
  have hg : 168 * π < gramPoint n := lt_of_lt_of_le S.high S.head_left_le_gramPoint
  have hc : ∀ j < k + 1, ∃ t ∈ Set.Ico (gramPoint (n + j)) (gramPoint (n + j + 1)),
      riemannZeta (1 / 2 + I * t) = 0 := fun j hj ↦ by
    have hjl : j < S.blocks.length := by lia
    have hlidx : (S.blocks[j]'hjl).left.idx = n + j := by
      rw [S.getElem_left_idx j hjl, ← hn_def]
    have hridx : (S.blocks[j]'hjl).right.idx = n + j + 1 := by
      have := (S.blocks[j]'hjl).seq; lia
    obtain ⟨t, ht_mem, ht_zero⟩ :=
      (S.blocks[j]'hjl).certificate_exists_zero (S.cert _ (List.getElem_mem hjl))
    exact ⟨t, by rwa [hlidx, hridx] at ht_mem, ht_zero⟩
  have h : (5 + (0.128 : ℝ) * (gramPoint (n + k + 1) / (2 * π)).log)
      < (gramPoint (n + k + 1) - gramPoint n) / 2 := by
    -- the certified brackets are strictly inside the gram span, so the span only grew
    have hB_last := hlast_ridx ▸ (S.blocks.getLast S.non_empty).right.certificate_left_lt_gramPoint
      hcertLast.right_certificate
    have hA_head := hn_def.symm ▸ (S.blocks.head S.non_empty).left.certificate_gramPoint_lt_right
      hcertHead.left_certificate
    have hlog : Real.log (gramPoint (n + k + 1) / (2 * π))
        ≤ Real.log ((S.blocks.getLast S.non_empty).right.snd / (2 * π)) := by
      refine Real.log_le_log (div_pos (gramPoint_pos _) (by positivity)) ?_
      gcongr
      exact (hlast_ridx ▸ (S.blocks.getLast S.non_empty).right.certificate_gramPoint_lt_right
        hcertLast.right_certificate).le
    linarith [S.wide]
  exact riemannZeta.N_le_of_gramPoints n k hg h hc
