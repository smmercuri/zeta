module

public import Native.Eval.Batch
public import Native.RiemannSiegel
public import Zeta.Zeros.IntervalRS
public import Zeta.Zeros.Certificates.Basic

/-!
# Native Riemann–Siegel batches

`checkTiling bs W W₁ n an ad bn bd` checks, by evaluation, that the brackets between consecutive
boundaries `bs` are each `ZIntervalRS.Certified` (the linear-free `Certificate₀`, against the error
bound at the batch's bottom boundary, which is valid throughout because the bound is antitone;
falling back to the full `Certificate`), and that the batch has `n` brackets running from `an/ad`
to `bn/bd`. `batchSpec_of_tiling` turns `true` into the `BatchSpec n an ad bn bd` a kernel-checked
batch exports, so the existing assembly applies unchanged; a batch file proves
`checkTiling … = true` by `native_decide`.
-/
@[expose] public section

namespace Native

open Enclosure BSN Zeta.Certificates

/-! ### One endpoint: certified sign and margin -/

theorem certifiedSign_spec {z b : Option Encl} {x y : ℝ} {s : Bool}
    (hz : ∀ Z, z = some Z → Z.Encloses x) (hb : ∀ B, b = some B → B.Encloses y)
    (h : certifiedSign z b = some s) : (if s then x < 0 else 0 < x) ∧ ‖x‖ > y := by
  simp only [certifiedSign, Option.bind_eq_some_iff] at h
  obtain ⟨Z, hZ, B, hB, he⟩ := h
  have eZ := hz Z hZ
  have eB := hb B hB
  by_cases hc : endpointOk Z B = true
  · rw [if_pos hc] at he
    cases he
    simp only [endpointOk, Bool.and_eq_true, and_assoc] at hc
    obtain ⟨hcdx, hrdx, hcde, hrde, hlt, hmargin⟩ := hc
    refine ⟨?_, norm_gt_of_isNear eZ eB hcdx hrdx hcde hrde hmargin⟩
    obtain ⟨zneg, zcn, zcd, zrn, zrd⟩ := Z
    cases zneg
    · exact Real.IsNear.pos_val eZ hcdx hrdx hlt
    · exact Real.IsNear.neg_val eZ hcdx hrdx hlt
  · rw [if_neg hc] at he
    cases he

/-- An enclosure of the error bound at some `0 < s₀ ≤ t` serves at `t`: the bound is antitone. -/
theorem endpointSign₀_spec {tab : TermTable} {tn td W : ℕ} {B : Option Encl} {s₀ : ℝ} {s : Bool}
    (htab : tab.Valid) (hB : ∀ B', B = some B' → B'.Encloses (hardyZErrorBoundRS₀ s₀))
    (hs₀ : 0 < s₀) (hle : s₀ ≤ sfrac false tn td) (h : endpointSign₀ tab tn td W B = some s) :
    (if s then hardyZApproximantRS₀ (sfrac false tn td) < 0
      else 0 < hardyZApproximantRS₀ (sfrac false tn td)) ∧
    ‖hardyZApproximantRS₀ (sfrac false tn td)‖ > hardyZErrorBoundRS₀ (sfrac false tn td) := by
  obtain ⟨hsign, hgt⟩ := certifiedSign_spec (fun _ hZ ↦ approx₀F_encloses htab hZ) hB h
  exact ⟨hsign, lt_of_le_of_lt (hardyZErrorBoundRS₀_anti hs₀ hle) hgt⟩

theorem endpointSign₁_spec {tab : TermTable} {tn td W : ℕ} {s : Bool} (htab : tab.Valid)
    (h : endpointSign₁ tab tn td W = some s) :
    (if s then hardyZApproximantRS (sfrac false tn td) < 0
      else 0 < hardyZApproximantRS (sfrac false tn td)) ∧
    ‖hardyZApproximantRS (sfrac false tn td)‖ > hardyZErrorBoundRS (sfrac false tn td) :=
  certifiedSign_spec (fun _ hZ ↦ approx₁_encloses htab hZ) (fun _ hB ↦ errBound₁_encloses hB) h

/-! ### One bracket -/

/-- The bracket as a `ZIntervalRS`. When its endpoints are out of order (which `rowOk` rules
out) it degenerates to its left endpoint, so that it is defined without a proof argument. -/
noncomputable def Row.ivl (r : Row) : ZIntervalRS :=
  if h : sfrac false r.an r.ad ≤ sfrac false r.bn r.bd then ⟨(sfrac false r.an r.ad,
    sfrac false r.bn r.bd), h⟩
  else ⟨(sfrac false r.an r.ad, sfrac false r.an r.ad), le_rfl⟩

theorem Row.ivl_fst (r : Row) : r.ivl.fst = sfrac false r.an r.ad := by
  unfold Row.ivl; split <;> rfl

theorem signsDiffer_spec {o₁ o₂ : Option Bool} (h : signsDiffer o₁ o₂ = true) :
    ∃ s₁ s₂, o₁ = some s₁ ∧ o₂ = some s₂ ∧ s₁ ≠ s₂ := by
  match o₁, o₂, h with
  | some s₁, some s₂, h => exact ⟨s₁, s₂, rfl, rfl, by simpa [signsDiffer] using h⟩

theorem Row.le_of_rowOk {r : Row} (h : rowOk r = true) :
    sfrac false r.an r.ad ≤ sfrac false r.bn r.bd := by
  simp only [rowOk, Bool.and_eq_true, and_assoc] at h
  obtain ⟨had, hbd, hab, -⟩ := h
  exact dec_le_dec _ _ _ _ rfl rfl had hbd hab

theorem Row.ivl_snd {r : Row} (h : rowOk r = true) : r.ivl.snd = sfrac false r.bn r.bd := by
  unfold Row.ivl
  rw [dif_pos (Row.le_of_rowOk h)]

/-- Opposite strict signs multiply to a negative number. -/
theorem mul_neg_of_signs {x y : ℝ} {s₁ s₂ : Bool} (hs : s₁ ≠ s₂)
    (h₁ : if s₁ then x < 0 else 0 < x) (h₂ : if s₂ then y < 0 else 0 < y) : x * y < 0 := by
  cases s₁ <;> cases s₂
  · exact absurd rfl hs
  · simp only [Bool.false_eq_true, if_false, if_true] at h₁ h₂
    exact mul_neg_of_pos_of_neg h₁ h₂
  · simp only [Bool.false_eq_true, if_false, if_true] at h₁ h₂
    exact mul_neg_of_neg_of_pos h₁ h₂
  · exact absurd rfl hs

/-- A bracket certifies a zero: it passes `rowOk`, and its endpoint signs differ under the
linear-free approximant against an error bound at `s₀ ≤` its left end, or under the full one. -/
theorem certified_of_row {tab : TermTable} {r : Row} {W W₁ : ℕ} {B : Option Encl} {s₀ : ℝ}
    (htab : tab.Valid) (hB : ∀ B', B = some B' → B'.Encloses (hardyZErrorBoundRS₀ s₀))
    (hs₀ : 0 < s₀) (hle : s₀ ≤ sfrac false r.an r.ad) (hrow : rowOk r = true)
    (hs : signsDiffer (endpointSign₀ tab r.an r.ad W B) (endpointSign₀ tab r.bn r.bd W B) = true ∨
      fallbackOk (r.an, r.ad) (r.bn, r.bd) W₁ = true) : r.ivl.Certified := by
  have hsnd := Row.ivl_snd hrow
  have hfst := Row.ivl_fst r
  have hab := Row.le_of_rowOk hrow
  simp only [rowOk, Bool.and_eq_true, and_assoc] at hrow
  obtain ⟨had, -, -, h32⟩ := hrow
  have hle32 : 32 * Real.pi ≤ r.ivl.fst := by
    rw [hfst]; exact thirtyTwoPi_le_dec r.an r.ad rfl had h32
  rcases hs with hs | hs
  · obtain ⟨s₁, s₂, h₁, h₂, hne⟩ := signsDiffer_spec hs
    obtain ⟨sign₁, err₁⟩ := endpointSign₀_spec htab hB hs₀ hle h₁
    obtain ⟨sign₂, err₂⟩ := endpointSign₀_spec htab hB hs₀ (hle.trans hab) h₂
    refine Or.inr ⟨hle32, ?_, ?_, ?_⟩
    · simp only [ZIntervalRS.fstVal₀, ZIntervalRS.sndVal₀, hfst, hsnd]
      exact mul_neg_of_signs hne sign₁ sign₂
    · simp only [ZIntervalRS.fstVal₀, hfst]; exact err₁
    · simp only [ZIntervalRS.sndVal₀, hsnd]; exact err₂
  · obtain ⟨s₁, s₂, h₁, h₂, hne⟩ := signsDiffer_spec hs
    obtain ⟨sign₁, err₁⟩ := endpointSign₁_spec (termTable_valid 0 W₁) h₁
    obtain ⟨sign₂, err₂⟩ := endpointSign₁_spec (termTable_valid 0 W₁) h₂
    refine Or.inl ⟨hle32, ?_, ?_, ?_⟩
    · simp only [ZIntervalRS.fstVal, ZIntervalRS.sndVal, hfst, hsnd]
      exact mul_neg_of_signs hne sign₁ sign₂
    · simp only [ZIntervalRS.fstVal, hfst]; exact err₁
    · simp only [ZIntervalRS.sndVal, hsnd]; exact err₂

/-! ### From certified brackets to a `BatchSpec` -/

/-- A list of brackets, each certified and ending at its stated right endpoint, ordered, with `n`
brackets from `an/ad` to `bn/bd`, gives the `BatchSpec`. -/
theorem batchSpec_of_rows (rows : List Row) (n an ad bn bd : ℕ)
    (hall : ∀ r ∈ rows, r.ivl.Certified ∧ r.ivl.snd = sfrac false r.bn r.bd)
    (hchain : (rows.map Row.ivl).IsChain (fun I J ↦ I.snd ≤ J.fst))
    (hlen : rows.length = n)
    (hhead : rows.head?.map (fun r => (r.an, r.ad)) = some (an, ad))
    (hlast : rows.getLast?.map (fun r => (r.bn, r.bd)) = some (bn, bd)) :
    BatchSpec n an ad bn bd := by
  refine ⟨⟨rows.map Row.ivl, ?_, ?_, hchain⟩, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hI
    exact (hall r hr).1.elim (·.fst_nonneg) (·.fst_nonneg)
  · intro I hI
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hI
    exact riemannZeta.exists_zero_of_zIntervalRS_certified _ (hall r hr).1
  · simpa using hlen
  · rw [List.head?_map, Option.map_map]
    obtain ⟨f, hf, hfe⟩ := Option.map_eq_some_iff.mp hhead
    simp only [Prod.mk.injEq] at hfe
    rw [hf]
    simp [Function.comp, Row.ivl_fst, hfe.1, hfe.2]
  · rw [List.getLast?_map, Option.map_map]
    obtain ⟨l, hl, hle⟩ := Option.map_eq_some_iff.mp hlast
    simp only [Prod.mk.injEq] at hle
    rw [hl]
    simp [Function.comp, (hall l (List.mem_of_getLast? hl)).2, hle.1, hle.2]

/-! ### A batch as a tiling

A batch from a widened store is a tiling: consecutive brackets share their boundary. Checking it
as a list of boundaries computes each boundary's value once and carries its sign to the next
bracket; the main-sum factors come from one table for the whole batch. -/

theorem tilingOk_rows {tab : TermTable} {W W₁ : ℕ} {B : Option Encl} {s₀ : ℝ}
    (htab : tab.Valid) (hB : ∀ B', B = some B' → B'.Encloses (hardyZErrorBoundRS₀ s₀))
    (hs₀ : 0 < s₀) :
    ∀ (a : ℕ × ℕ) (rest : List (ℕ × ℕ)), s₀ ≤ sfrac false a.1 a.2 →
      tilingOk tab W W₁ B a (endpointSign₀ tab a.1 a.2 W B) rest = true →
      (∀ r ∈ rowsOf (a :: rest), r.ivl.Certified ∧ r.ivl.snd = sfrac false r.bn r.bd) ∧
      ((rowsOf (a :: rest)).map Row.ivl).IsChain (fun I J ↦ I.snd ≤ J.fst)
  | _, [], _, _ => ⟨by simp [rowsOf], by simp [rowsOf]⟩
  | a, b :: rest, hle, h => by
    simp only [tilingOk, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨hrow, hs⟩, hrest⟩ := h
    have hab : s₀ ≤ sfrac false b.1 b.2 :=
      hle.trans (Row.le_of_rowOk (r := ⟨a.1, a.2, b.1, b.2⟩) hrow)
    obtain ⟨ihall, ihchain⟩ := tilingOk_rows htab hB hs₀ b rest hab hrest
    have hsnd := Row.ivl_snd hrow
    refine ⟨?_, ?_⟩
    · intro r hr
      simp only [rowsOf, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨certified_of_row htab hB hs₀ hle hrow hs, hsnd⟩
      · exact ihall r hr
    · cases rest with
      | nil => simp [rowsOf]
      | cons c rest' =>
        simp only [rowsOf, List.map_cons] at ihchain ⊢
        refine List.IsChain.cons_cons ?_ ihchain
        rw [hsnd, Row.ivl_fst]

theorem rowsOf_length : ∀ (a : ℕ × ℕ) (rest : List (ℕ × ℕ)),
    (rowsOf (a :: rest)).length = rest.length
  | _, [] => rfl
  | _, b :: rest => by simp [rowsOf, rowsOf_length b rest]

theorem rowsOf_head (a b : ℕ × ℕ) (rest : List (ℕ × ℕ)) :
    (rowsOf (a :: b :: rest)).head?.map (fun r => (r.an, r.ad)) = some a := by
  simp [rowsOf]

theorem rowsOf_getLast : ∀ (a b : ℕ × ℕ) (rest : List (ℕ × ℕ)),
    (rowsOf (a :: b :: rest)).getLast?.map (fun r => (r.bn, r.bd)) =
      (b :: rest).getLast?
  | _, _, [] => by simp [rowsOf]
  | a, b, c :: rest => by
    have ih := rowsOf_getLast b c rest
    simp only [rowsOf] at ih ⊢
    rw [List.getLast?_cons_cons, ih, List.getLast?_cons_cons]

theorem batchSpec_of_tiling (bs : List (ℕ × ℕ)) (W W₁ n an ad bn bd : ℕ)
    (h : checkTiling bs W W₁ n an ad bn bd = true) : BatchSpec n an ad bn bd := by
  match bs, h with
  | a :: b :: rest, h =>
    simp only [checkTiling, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨ha1, ha2, htil, hlen, ha, hlast⟩ := h
    have hs₀ : 0 < sfrac false a.1 a.2 := by
      rw [sfrac_false_div]
      have : (0 : ℝ) < a.1 := by exact_mod_cast Nat.le_of_ble_eq_true ha1
      have : (0 : ℝ) < a.2 := by exact_mod_cast Nat.le_of_ble_eq_true ha2
      positivity
    obtain ⟨hall, hchain⟩ := tilingOk_rows (termTable_valid _ _)
      (fun _ hB ↦ errBound_encloses hB) hs₀ a (b :: rest) le_rfl htil
    refine batchSpec_of_rows _ n an ad bn bd hall hchain ?_ ?_ ?_
    · rw [rowsOf_length]; exact hlen
    · rw [rowsOf_head, ha]
    · rw [rowsOf_getLast, hlast]

end Native
