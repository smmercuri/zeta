module

public import Native.Eval.RiemannSiegel
public import Native.Log
public import Native.Arctan
public import Native.Fix
public import Zeta.Certificate.HardyZDefs

/-!
# Native Riemann–Siegel endpoint values

At a rational endpoint `t = tn/td`, enclosures of the linear-free Riemann–Siegel approximant
`hardyZApproximantRS₀ t` and its error bound `hardyZErrorBoundRS₀ t`. Each piece is built along the
expression tree of the `BSN` lemma that names it (`floor_sqrt_eq_dec`, `t_div_two_pi_mk`,
`riemannSiegelThetaApproximant_two_zero_mk`, `correction_mk`, `hardyZApproximantRS₀_eq`,
`hardyZErrorBoundRS₀_mk`), so soundness is the operations' soundness followed by that lemma.

All arithmetic runs on one grid `1/dyadic W`, with every transcendental leaf to `1/W`.
-/
@[expose] public section

namespace Native

open Enclosure BSN

/-! ### The cutoff `ν = ⌊√(t/2π)⌋` -/

theorem cutoff_eq {tn td ν : ℕ} (h : cutoff tn td = some ν) :
    ⌊Real.sqrt (sfrac false tn td / (2 * Real.pi))⌋₊ = ν := by
  simp only [cutoff] at h
  split at h
  · rename_i hc
    simp only [cutoffOk, Bool.and_eq_true, and_assoc] at hc
    obtain ⟨htd, hlo, hhi⟩ := hc
    cases h
    exact floor_sqrt_eq_dec tn td _ rfl htd hlo hhi
  · cases h

/-! ### `T = t/2π` -/

theorem twoPi_encloses {e : Encl} (h : twoPi = some e) :
    e.Encloses (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi) :=
  Encl.mul_encloses (Encl.const_encloses false 2 1) piEncl_encloses h

theorem tDivTwoPi_encloses {tn td Q : ℕ} {e : Encl} (h : tDivTwoPi tn td Q = some e) :
    e.Encloses (sfrac false tn td / (2 * Real.pi)) := by
  simp only [tDivTwoPi, Option.bind_eq_some_iff] at h
  obtain ⟨P, hP, P', hP', he⟩ := h
  rw [t_div_two_pi_mk _ tn td rfl]
  exact Encl.mulR_encloses (Encl.const_encloses false tn td)
    (Encl.inv_encloses (twoPi_encloses hP) hP') he

/-! ### The phase `θ̃ = riemannSiegelThetaApproximant 2 0 t` -/

theorem thetaWith_encloses {tn td W Q : ℕ} {c : ThetaConsts} {logPi : Option Encl} {e : Encl}
    (hlogPi : ∀ e, logPi = some e → e.Encloses (Real.log Real.pi))
    (h : thetaWith tn td W Q c logPi = some e) :
    e.Encloses (riemannSiegelThetaApproximant 2 0 (sfrac false tn td)) := by
  unfold thetaWith at h
  by_cases hc : thetaOk tn td c = true
  · rw [if_pos hc] at h
    simp only [thetaOk, Bool.and_eq_true, and_assoc] at hc
    obtain ⟨htn, htd, hS, hQ, hV, hT4, hT2, hRn, hRd⟩ := hc
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨lSQ, hlSQ, a₁, ha₁, atn, hatn, hp, hhp, d, hd, a₂, ha₂, lp, hlp, a₃, ha₃, s₁, hs₁,
      s₂, hs₂, s₃, hs₃, he⟩ := h
    rw [riemannSiegelThetaApproximant_two_zero_mk _ tn td _ _ _ _ _ _ _ rfl htn htd hS hQ hV hT4
      hT2 hRn hRd]
    have elSQ := logRatSigned_encloses hlSQ
    rw [← sfrac_false_div] at elSQ
    have ea₁ := Encl.mulR_encloses (Encl.const_encloses false tn _) elSQ ha₁
    have ehp := Encl.mulR_encloses (Encl.const_encloses false 1 2) piEncl_encloses hhp
    have ed := Encl.subR_encloses ehp (arctanRat_encloses hatn) hd
    have ea₂ := Encl.mulR_encloses (Encl.const_encloses false 1 4) ed ha₂
    have ea₃ := Encl.mulR_encloses (Encl.const_encloses false tn _)
      (hlogPi lp hlp) ha₃
    have es₁ := Encl.subR_encloses ea₁ ea₂ hs₁
    have es₂ := Encl.subR_encloses es₁ (Encl.const_encloses false tn _) hs₂
    have es₃ := Encl.subR_encloses es₂ ea₃ hs₃
    exact Encl.addR_encloses es₃ (Encl.const_encloses true _ _) he
  · rw [if_neg hc] at h
    cases h

theorem theta_encloses {tn td W : ℕ} {logPi : Option Encl} {e : Encl}
    (hlogPi : ∀ e, logPi = some e → e.Encloses (Real.log Real.pi))
    (h : theta tn td W logPi = some e) :
    e.Encloses (riemannSiegelThetaApproximant 2 0 (sfrac false tn td)) :=
  thetaWith_encloses hlogPi h

/-! ### The main sum `∑_{n ≤ ν} cos(θ − t log n)/√n` -/

theorem invSqrtNat_encloses {n Q : ℕ} {e : Encl} (h : invSqrtNat n Q = some e) :
    e.Encloses (Real.sqrt n)⁻¹ := by
  obtain ⟨sq, hsq, he⟩ := Option.bind_eq_some_iff.mp h
  have esq := Encl.sqrt_encloses (Encl.const_encloses false n 1) hsq
  rw [sfrac_false_div, Nat.cast_one, div_one] at esq
  exact Encl.inv_encloses esq he

/-- Every entry of a table encloses what it should, on its grid. -/
structure TermTable.Valid (tab : TermTable) : Prop where
  Q : 0 < tab.Q
  H : ∀ H, tab.H = some H → H.Encloses tab.Q (Real.pi / 2)
  trig : Fx.TableValid tab.Q tab.trig
  tp : ∀ x, tab.tp = some x → x.Encloses tab.Q (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi)
  itp : ∀ x, tab.itp = some x →
    x.Encloses tab.Q (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi)⁻¹
  logPi : ∀ e, tab.logPi = some e → e.Encloses (Real.log Real.pi)
  logPiF : ∀ x, tab.logPiF = some x → x.Encloses tab.Q (Real.log Real.pi)
  lg : ∀ i (hi : i < tab.lg.size) L, tab.lg[i] = some L → L.Encloses tab.Q (Real.log i)
  isq : ∀ i (hi : i < tab.isq.size) L, tab.isq[i] = some L → L.Encloses tab.Q (Real.sqrt i)⁻¹

theorem dyadic_pos (W : ℕ) : 0 < dyadic W := by unfold dyadic; positivity

theorem halfPi_encloses {W : ℕ} {H : Fx}
    (h : (Fx.ofEncl (dyadic W) piEncl).map (Fx.divNat 2) = some H) :
    H.Encloses (dyadic W) (Real.pi / 2) := by
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp h
  have := Fx.divNat_encloses (dyadic_pos W) (by norm_num : 0 < 2)
    (Fx.ofEncl_encloses (dyadic_pos W) piEncl_encloses hP)
  simpa using this

theorem termTable_valid (N W : ℕ) : (termTable N W).Valid where
  Q := dyadic_pos W
  H _ hH := halfPi_encloses hH
  trig := by
    change Fx.TableValid (dyadic W) (match (Fx.ofEncl (dyadic W) piEncl).map (Fx.divNat 2) with
      | some H => Fx.trigTable (dyadic W) H
      | none => #[])
    split
    · rename_i H hH
      exact Fx.trigTable_valid (dyadic_pos W) (halfPi_encloses hH)
    · intro i hi; simp at hi
  tp x hx := by
    simp only [termTable] at hx
    obtain ⟨P, hP, hx⟩ := Option.bind_eq_some_iff.mp hx
    exact Fx.ofEncl_encloses (dyadic_pos W) (twoPi_encloses hP) hx
  itp x hx := by
    simp only [termTable] at hx
    obtain ⟨I, hI, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨P, hP, hI⟩ := Option.bind_eq_some_iff.mp hI
    exact Fx.ofEncl_encloses (dyadic_pos W) (Encl.inv_encloses (twoPi_encloses hP) hI) hx
  logPi e he := log_encloses piEncl_encloses he
  logPiF x hx := by
    simp only [termTable] at hx
    obtain ⟨e, he, hx⟩ := Option.bind_eq_some_iff.mp hx
    exact Fx.ofEncl_encloses (dyadic_pos W) (log_encloses piEncl_encloses he) hx
  lg i hi L hL := by
    simp only [termTable, Array.getElem_ofFn, Option.bind_eq_some_iff] at hL
    obtain ⟨e, he, hL⟩ := hL
    exact Fx.ofEncl_encloses (dyadic_pos W) (logNat_encloses he) hL
  isq i hi L hL := by
    simp only [termTable, Array.getElem_ofFn, Option.bind_eq_some_iff] at hL
    obtain ⟨e, he, hL⟩ := hL
    exact Fx.ofEncl_encloses (dyadic_pos W) (invSqrtNat_encloses he) hL

theorem cosSinE_encloses {tab : TermTable} {X C S : Encl} {x : ℝ} (htab : tab.Valid)
    (hX : X.Encloses x) (h : cosSinE tab X = some (C, S)) :
    C.Encloses (Real.cos x) ∧ S.Encloses (Real.sin x) := by
  simp only [cosSinE, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨H, hH, XF, hXF, cs, hcs, rfl, rfl⟩ := h
  obtain ⟨eC, eS⟩ := Fx.cosSinT_encloses htab.Q (htab.H H hH) htab.trig
    (Fx.ofEncl_encloses htab.Q hX hXF) hcs
  exact ⟨Fx.toEncl_encloses eC, Fx.toEncl_encloses eS⟩

theorem lgAt_encloses {tab : TermTable} {n W : ℕ} {L : Fx} (htab : tab.Valid)
    (h : lgAt tab n W = some L) : L.Encloses tab.Q (Real.log n) := by
  unfold lgAt at h
  split at h
  · rename_i o ho
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ho
    exact htab.lg n hi L h
  · obtain ⟨e, he, hL⟩ := Option.bind_eq_some_iff.mp h
    exact Fx.ofEncl_encloses htab.Q (logNat_encloses he) hL

theorem isqAt_encloses {tab : TermTable} {n : ℕ} {L : Fx} (htab : tab.Valid)
    (h : isqAt tab n = some L) : L.Encloses tab.Q (Real.sqrt n)⁻¹ := by
  unfold isqAt at h
  split at h
  · rename_i o ho
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ho
    exact htab.isq n hi L h
  · obtain ⟨e, he, hL⟩ := Option.bind_eq_some_iff.mp h
    exact Fx.ofEncl_encloses htab.Q (invSqrtNat_encloses he) hL

/-! ### The phase table -/

/-- A phase table is valid for `t` when entry `i` encloses `(cos(t log i), sin(t log i))`. -/
def AngValid (Q : ℕ) (t : ℝ) (arr : Array (Option (Fx × Fx))) : Prop :=
  ∀ i (hi : i < arr.size) cs, arr[i] = some cs →
    cs.1.Encloses Q (Real.cos (t * Real.log i)) ∧ cs.2.Encloses Q (Real.sin (t * Real.log i))

theorem angleEntry_spec {tab : TermTable} {H T : Fx} {W : ℕ} {arr : Array (Option (Fx × Fx))}
    {t : ℝ} (htab : tab.Valid) (hH : H.Encloses tab.Q (Real.pi / 2)) (hT : T.Encloses tab.Q t)
    (hv : AngValid tab.Q t arr) {cs : Fx × Fx} (h : angleEntry tab H T W arr = some cs) :
    cs.1.Encloses tab.Q (Real.cos (t * Real.log arr.size)) ∧
      cs.2.Encloses tab.Q (Real.sin (t * Real.log arr.size)) := by
  unfold angleEntry at h
  by_cases h1 : arr.size ≤ 1
  · rw [if_pos h1] at h
    cases h
    have hlog : Real.log (arr.size : ℝ) = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h0 | h0 <;> simp [h0]
    rw [hlog, mul_zero, Real.cos_zero, Real.sin_zero]
    exact ⟨by simpa using Fx.ofInt_encloses htab.Q 1, Fx.zero_encloses⟩
  · rw [if_neg h1] at h
    by_cases h2 : (smallFactor arr.size arr.size 2 < arr.size &&
        smallFactor arr.size arr.size 2 * (arr.size / smallFactor arr.size arr.size 2) ==
          arr.size) = true
    · rw [if_pos h2] at h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
      obtain ⟨-, hpm⟩ := h2
      obtain ⟨a, ha, b, hb, rfl⟩ := by
        simpa only [Option.bind_eq_some_iff, Option.map_eq_some_iff] using h
      obtain ⟨hpi, hpa⟩ := Fx.join_getElem?_spec ha
      obtain ⟨hmi, hmb⟩ := Fx.join_getElem?_spec hb
      set p := smallFactor arr.size arr.size 2
      set m := arr.size / p
      have hp : 0 < p := by
        rcases Nat.eq_zero_or_pos p with h0 | h0
        · rw [h0, zero_mul] at hpm; omega
        · exact h0
      have hm : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, mul_zero] at hpm; omega
        · exact h0
      have hrot := Fx.rotate_encloses htab.Q (hv p hpi a hpa) (hv m hmi b hmb)
      have hlog : t * Real.log (arr.size : ℝ) = t * Real.log p + t * Real.log m := by
        have e : (arr.size : ℝ) = (p : ℝ) * (m : ℝ) := by exact_mod_cast hpm.symm
        rw [e, Real.log_mul (by positivity) (by positivity), mul_add]
      rw [hlog]
      exact hrot
    · rw [if_neg h2] at h
      obtain ⟨L, hL, hcs⟩ := Option.bind_eq_some_iff.mp h
      exact Fx.cosSinT_encloses htab.Q hH htab.trig
        (Fx.mul_encloses htab.Q hT (lgAt_encloses htab hL)) hcs

theorem anglesAux_valid {tab : TermTable} {H T : Fx} {W : ℕ} {t : ℝ} (htab : tab.Valid)
    (hH : H.Encloses tab.Q (Real.pi / 2)) (hT : T.Encloses tab.Q t) :
    ∀ k arr, AngValid tab.Q t arr → AngValid tab.Q t (anglesAux tab H T W k arr)
  | 0, _, hv => hv
  | k + 1, arr, hv => by
    refine anglesAux_valid htab hH hT k _ ?_
    intro i hi cs hcs
    rw [Array.size_push] at hi
    rw [Array.getElem_push] at hcs
    split at hcs
    · rename_i hlt
      exact hv i hlt cs hcs
    · rename_i hge
      have hi' : i = arr.size := by omega
      subst hi'
      exact angleEntry_spec htab hH hT hv hcs

/-! ### The sum -/

theorem sumTerms_encloses {tab : TermTable} {A : Array (Option (Fx × Fx))} {t : ℝ}
    (htab : tab.Valid) (hA : AngValid tab.Q t A) :
    ∀ ν S, sumTerms tab A ν = some S →
      S.1.Encloses tab.Q (∑ n ∈ Finset.Icc 1 ν, Real.cos (t * Real.log n) * (Real.sqrt n)⁻¹) ∧
      S.2.Encloses tab.Q (∑ n ∈ Finset.Icc 1 ν, Real.sin (t * Real.log n) * (Real.sqrt n)⁻¹)
  | 0, S, h => by
    simp only [sumTerms, Option.some.injEq] at h
    subst h
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl, Finset.sum_empty, Finset.sum_empty]
    exact ⟨Fx.zero_encloses, Fx.zero_encloses⟩
  | k + 1, S, h => by
    simp only [sumTerms, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨S', hS', cs, hcs, isq, hisq, rfl⟩ := h
    obtain ⟨hi, hcs'⟩ := Fx.join_getElem?_spec hcs
    obtain ⟨eC, eS⟩ := hA (k + 1) hi cs hcs'
    obtain ⟨e1, e2⟩ := sumTerms_encloses htab hA k S' hS'
    have ei := isqAt_encloses htab hisq
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), Finset.sum_Icc_succ_top (by omega)]
    exact ⟨Fx.add_encloses e1 (Fx.mul_encloses htab.Q eC ei),
      Fx.add_encloses e2 (Fx.mul_encloses htab.Q eS ei)⟩

/-- The main sum split along `cos(θ − φ) = cos θ cos φ + sin θ sin φ`. -/
theorem sum_cos_sub_eq (θ t : ℝ) (ν : ℕ) :
    ∑ n ∈ Finset.Icc 1 ν, Real.cos (θ - t * Real.log n) / Real.sqrt n =
      Real.cos θ * ∑ n ∈ Finset.Icc 1 ν, Real.cos (t * Real.log n) * (Real.sqrt n)⁻¹ +
      Real.sin θ * ∑ n ∈ Finset.Icc 1 ν, Real.sin (t * Real.log n) * (Real.sqrt n)⁻¹ := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Real.cos_sub, div_eq_mul_inv]; ring

theorem mainSumF_encloses {θ : Fx} {tab : TermTable} {tn td W ν : ℕ} {θr : ℝ}
    (htab : tab.Valid) (hθ : θ.Encloses tab.Q θr) {S : Fx}
    (h : mainSumF θ tn td tab W ν = some S) :
    S.Encloses tab.Q (∑ n ∈ Finset.Icc 1 ν,
      Real.cos (θr - sfrac false tn td * Real.log n) / Real.sqrt n) := by
  unfold mainSumF at h
  by_cases htd : Nat.ble 1 td = true
  · rw [if_pos htd] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨H, hH, cs, hcs, S', hS', rfl⟩ := h
    have eH := htab.H H hH
    obtain ⟨ec, es⟩ := Fx.cosSinT_encloses htab.Q eH htab.trig hθ hcs
    have hT := Fx.ofRat_encloses htab.Q (Nat.le_of_ble_eq_true htd) false (a := tn)
    have hA := anglesAux_valid (W := W) htab eH hT (ν + 1) #[] (fun i hi ↦ absurd hi (by simp))
    obtain ⟨e1, e2⟩ := sumTerms_encloses htab hA ν S' hS'
    rw [sum_cos_sub_eq]
    exact Fx.add_encloses (Fx.mul_encloses htab.Q ec (Fx.tighten_encloses htab.Q e1))
      (Fx.mul_encloses htab.Q es (Fx.tighten_encloses htab.Q e2))
  · rw [if_neg htd] at h
    cases h

theorem mainSum_encloses {θE : Encl} {tab : TermTable} {tn td W ν : ℕ} {θ : ℝ}
    (htab : tab.Valid) (hθ : θE.Encloses θ) {e : Encl} (h : mainSum θE tn td tab W ν = some e) :
    e.Encloses (∑ n ∈ Finset.Icc 1 ν,
      Real.cos (θ - sfrac false tn td * Real.log n) / Real.sqrt n) := by
  simp only [mainSum, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨θF, hθF, S, hS, rfl⟩ := h
  exact Fx.toEncl_encloses (mainSumF_encloses htab (Fx.ofEncl_encloses htab.Q hθ hθF) hS)

/-! ### The correction `Ψ(p)` and its derivatives

Each along its `BSN` lemma (`correction_mk`, `deriv_correction_mk`,
`iteratedDeriv_two_correction_mk`, `iteratedDeriv_three_correction_mk`, `correctionLinear_mk`):
the reciprocal of `C = cos 2πp` times a combination of trig leaves and the derivatives already
built. Their common side condition `cos 2πp ≠ 0` holds at every certificate endpoint
(`BSN.cos_two_pi_p_ne_zero_mk`). -/

/-- What `CorrLeaves` encloses at `p`. -/
structure CorrLeaves.Encloses (L : CorrLeaves) (p : ℝ) : Prop where
  tp : L.tp.Encloses (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi)
  C : L.C.Encloses (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
  S : L.S.Encloses (Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
  iC : L.iC.Encloses (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
  cφ : L.cφ.Encloses (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
    * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))))
  sφ : L.sφ.Encloses (Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
    * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))))

theorem corrLeaves_encloses {tab : TermTable} {P : Encl} {Q : ℕ} {p : ℝ} {L : CorrLeaves}
    (htab : tab.Valid) (hP : P.Encloses p) (h : corrLeaves tab P Q = some L) : L.Encloses p := by
  simp only [corrLeaves, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨tp, htp, a, ha, CS, hCS, iC, hiC, pp, hpp, q₁, hq₁, q₂, hq₂, b, hb, cs, hcs, rfl⟩ := h
  have etp := twoPi_encloses htp
  have ea := Encl.mulR_encloses etp hP ha
  obtain ⟨eC, eS⟩ := cosSinE_encloses htab ea (show cosSinE tab a = some (CS.1, CS.2) from hCS)
  have eq₂ := Encl.subR_encloses (Encl.subR_encloses (Encl.mulR_encloses hP hP hpp) hP hq₁)
    (Encl.const_encloses false 1 16) hq₂
  have eb := Encl.mulR_encloses etp eq₂ hb
  obtain ⟨ec, es⟩ := cosSinE_encloses htab eb (show cosSinE tab b = some (cs.1, cs.2) from hcs)
  exact ⟨etp, eC, eS, Encl.inv_encloses eC hiC, ec, es⟩

theorem correction_encloses {L : CorrLeaves} {Q : ℕ} {p : ℝ} {e : Encl} (hL : L.Encloses p)
    (hC : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0)
    (h : correction L Q = some e) : e.Encloses (Zeta.RiemannSiegel.correction p) := by
  rw [correction_mk p hC]
  exact Encl.mulR_encloses hL.iC hL.cφ h

theorem corrA_encloses {L : CorrLeaves} {P : Encl} {Q : ℕ} {p : ℝ} {e : Encl}
    (hL : L.Encloses p) (hP : P.Encloses p) (h : corrA L P Q = some e) :
    e.Encloses (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
      * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1))) := by
  simp only [corrA, Option.bind_eq_some_iff] at h
  obtain ⟨p₂, hp₂, d, hd, he⟩ := h
  exact Encl.mulR_encloses hL.tp (Encl.subR_encloses (Encl.mulR_encloses
    (Encl.const_encloses false 2 1) hP hp₂) (Encl.const_encloses false 1 1) hd) he

/-- What `CorrAux` encloses at `p`. -/
structure CorrAux.Encloses (X : CorrAux) (p : ℝ) : Prop where
  A : X.A.Encloses (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
      * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
  Y : X.Y.Encloses (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
      * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
  pi2 : X.pi2.Encloses (Real.pi * Real.pi)
  pi3 : X.pi3.Encloses (Real.pi * Real.pi * Real.pi)
  Z₂ : X.Z₂.Encloses (sfrac false (nat_lit 4) (nat_lit 1) * (Real.pi * Real.pi)
      * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))

theorem corrAux_encloses {L : CorrLeaves} {P : Encl} {Q : ℕ} {p : ℝ} {X : CorrAux}
    (hL : L.Encloses p) (hP : P.Encloses p) (h : corrAux L P Q = some X) : X.Encloses p := by
  simp only [corrAux, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨A, hA, Y, hY, pi2, hpi2, pi3, hpi3, f, hf, Z₂, hZ₂, rfl⟩ := h
  have epi2 := Encl.mulR_encloses piEncl_encloses piEncl_encloses hpi2
  exact ⟨corrA_encloses hL hP hA, Encl.mulR_encloses hL.tp hL.S hY, epi2,
    Encl.mulR_encloses epi2 piEncl_encloses hpi3,
    Encl.mulR_encloses (Encl.mulR_encloses (Encl.const_encloses false 4 1) epi2 hf) hL.C hZ₂⟩

theorem deriv1_encloses {L : CorrLeaves} {X : CorrAux} {ψ e : Encl} {Q : ℕ} {p : ℝ}
    (hL : L.Encloses p) (hX : X.Encloses p) (hψ : ψ.Encloses (Zeta.RiemannSiegel.correction p))
    (hC : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0)
    (h : deriv1 L X ψ Q = some e) :
    e.Encloses (iteratedDeriv 1 Zeta.RiemannSiegel.correction p) := by
  simp only [deriv1, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, c, hc, he⟩ := h
  rw [deriv_correction_mk p hC]
  exact Encl.mulR_encloses hL.iC (Encl.subR_encloses
    (Encl.negate_encloses (Encl.mulR_encloses hX.A hL.sφ ha))
    (Encl.mulR_encloses (Encl.negate_encloses hX.Y) hψ hb) hc) he

theorem deriv2_encloses {L : CorrLeaves} {X : CorrAux} {ψ ψ₁ e : Encl} {Q : ℕ} {p : ℝ}
    (hL : L.Encloses p) (hX : X.Encloses p) (hψ : ψ.Encloses (Zeta.RiemannSiegel.correction p))
    (hψ₁ : ψ₁.Encloses (iteratedDeriv 1 Zeta.RiemannSiegel.correction p))
    (hC : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0)
    (h : deriv2 L X ψ ψ₁ Q = some e) :
    e.Encloses (iteratedDeriv 2 Zeta.RiemannSiegel.correction p) := by
  simp only [deriv2, Option.bind_eq_some_iff] at h
  obtain ⟨aa, haa, t₁, ht₁, fp, hfp, t₂, ht₂, ty, hty, t₃, ht₃, t₄, ht₄, s₁, hs₁, s₂, hs₂, s₃,
    hs₃, he⟩ := h
  rw [iteratedDeriv_two_correction_mk p hC]
  have et₁ := Encl.mulR_encloses (Encl.mulR_encloses hX.A hX.A haa) hL.cφ ht₁
  have et₂ := Encl.mulR_encloses (Encl.mulR_encloses (Encl.const_encloses false 4 1)
    piEncl_encloses hfp) hL.sφ ht₂
  have et₃ := Encl.mulR_encloses (Encl.mulR_encloses (Encl.const_encloses false 2 1)
    (Encl.negate_encloses hX.Y) hty) hψ₁ ht₃
  have et₄ := Encl.mulR_encloses (Encl.negate_encloses hX.Z₂) hψ ht₄
  exact Encl.mulR_encloses hL.iC (Encl.subR_encloses (Encl.subR_encloses
    (Encl.subR_encloses (Encl.negate_encloses et₁) et₂ hs₁) et₃ hs₂) et₄ hs₃) he

theorem deriv3_encloses {L : CorrLeaves} {X : CorrAux} {ψ ψ₁ ψ₂ e : Encl} {Q : ℕ} {p : ℝ}
    (hL : L.Encloses p) (hX : X.Encloses p) (hψ : ψ.Encloses (Zeta.RiemannSiegel.correction p))
    (hψ₁ : ψ₁.Encloses (iteratedDeriv 1 Zeta.RiemannSiegel.correction p))
    (hψ₂ : ψ₂.Encloses (iteratedDeriv 2 Zeta.RiemannSiegel.correction p))
    (hC : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0)
    (h : deriv3 L X ψ ψ₁ ψ₂ Q = some e) :
    e.Encloses (iteratedDeriv 3 Zeta.RiemannSiegel.correction p) := by
  simp only [deriv3, Option.bind_eq_some_iff] at h
  obtain ⟨aa, haa, aaa, haaa, t₁, ht₁, ta, hta, fp, hfp, tafp, htafp, t₂, ht₂, ty, hty, t₃, ht₃,
    tz, htz, t₄, ht₄, ep, hep, eps, heps, t₅, ht₅, s₁, hs₁, s₂, hs₂, s₃, hs₃, s₄, hs₄, he⟩ := h
  rw [iteratedDeriv_three_correction_mk p hC]
  have et₁ := Encl.mulR_encloses (Encl.mulR_encloses (Encl.mulR_encloses hX.A hX.A haa) hX.A haaa)
    hL.sφ ht₁
  have et₂ := Encl.mulR_encloses (Encl.mulR_encloses (Encl.mulR_encloses
    (Encl.const_encloses false 3 1) hX.A hta) (Encl.mulR_encloses (Encl.const_encloses false 4 1)
      piEncl_encloses hfp) htafp) hL.cφ ht₂
  have et₃ := Encl.mulR_encloses (Encl.mulR_encloses (Encl.const_encloses false 3 1)
    (Encl.negate_encloses hX.Y) hty) hψ₂ ht₃
  have et₄ := Encl.mulR_encloses (Encl.mulR_encloses (Encl.const_encloses false 3 1)
    (Encl.negate_encloses hX.Z₂) htz) hψ₁ ht₄
  have et₅ := Encl.mulR_encloses (Encl.mulR_encloses (Encl.mulR_encloses
    (Encl.const_encloses false 8 1) hX.pi3 hep) hL.S heps) hψ ht₅
  exact Encl.mulR_encloses hL.iC (Encl.subR_encloses (Encl.subR_encloses (Encl.subR_encloses
    (Encl.subR_encloses et₁ et₂ hs₁) et₃ hs₂) et₄ hs₃) et₅ hs₄) he

theorem correctionLinear_encloses {X : CorrAux} {ψ₃ e : Encl} {Q : ℕ} {p : ℝ}
    (hX : X.Encloses p) (hψ₃ : ψ₃.Encloses (iteratedDeriv 3 Zeta.RiemannSiegel.correction p))
    (h : correctionLinear X ψ₃ Q = some e) :
    e.Encloses (Zeta.RiemannSiegel.correctionLinear p) := by
  simp only [correctionLinear, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨n, hn, i, hi, m, hm, rfl⟩ := h
  rw [correctionLinear_mk p]
  exact Encl.negate_encloses (Encl.mulR_encloses hψ₃ (Encl.inv_encloses
    (Encl.mulR_encloses (Encl.const_encloses false 96 1) hX.pi2 hn) hi) hm)

theorem corrLinear_encloses {L : CorrLeaves} {P ψ e : Encl} {Q : ℕ} {p : ℝ}
    (hL : L.Encloses p) (hP : P.Encloses p) (hψ : ψ.Encloses (Zeta.RiemannSiegel.correction p))
    (hC : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0)
    (h : corrLinear L P ψ Q = some e) :
    e.Encloses (Zeta.RiemannSiegel.correctionLinear p) := by
  simp only [corrLinear, Option.bind_eq_some_iff] at h
  obtain ⟨X, hX, ψ₁, hψ₁, ψ₂, hψ₂, ψ₃, hψ₃, he⟩ := h
  have eX := corrAux_encloses hL hP hX
  have eψ₁ := deriv1_encloses hL eX hψ hC hψ₁
  have eψ₂ := deriv2_encloses hL eX hψ eψ₁ hC hψ₂
  exact correctionLinear_encloses eX (deriv3_encloses hL eX hψ eψ₁ eψ₂ hC hψ₃) he

/-! ### The approximants `hardyZApproximantRS₀ t` and `hardyZApproximantRS t` -/

/-- `(−1)^ν` as a signed fraction. -/
theorem neg_one_pow_eq_sfrac (ν : ℕ) :
    (-1 : ℝ) ^ ν = sfrac (ν % 2 == 1) (nat_lit 1) (nat_lit 1) := by
  rcases Nat.mod_two_eq_zero_or_one ν with h | h
  · rw [h]; exact neg_one_pow_even_mk ν (by simp [h])
  · rw [h]; exact neg_one_pow_odd_mk ν (by simp [h])

/-- What `ApproxParts` encloses at `t` with cutoff `ν`. -/
structure ApproxParts.Encloses (A : ApproxParts) (t : ℝ) (ν : ℕ) : Prop where
  S₂ : A.S₂.Encloses (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ν)
  sqT : A.sqT.Encloses (Real.sqrt (t / (2 * Real.pi)))
  sgnq : A.sgnq.Encloses ((-1) ^ ν * (t / (2 * Real.pi)) ^ (-(1 / 4) : ℝ))
  P : A.P.Encloses (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))
  L : A.L.Encloses (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))

theorem approxParts_encloses {tab : TermTable} {tn td W Q ν : ℕ} {A : ApproxParts}
    (htab : tab.Valid) (h : approxParts tab tn td W Q ν = some A) :
    A.Encloses (sfrac false tn td) ν := by
  simp only [approxParts, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨θE, hθE, S, hS, S₂, hS₂, T, hT, sqT, hsqT, q, hq, iq, hiq, sgnq, hsgnq, P, hP, L, hL,
    rfl⟩ := h
  have eT := tDivTwoPi_encloses hT
  have esqT := Encl.sqrt_encloses eT hsqT
  have eiq := Encl.inv_encloses (Encl.sqrt_encloses esqT hq) hiq
  have eS := mainSum_encloses htab (theta_encloses htab.logPi hθE) hS
  have eS₂ := Encl.mulR_encloses (Encl.const_encloses false 2 1) eS hS₂
  have h2 : sfrac false 2 1 = (2 : ℝ) := by norm_num [sfrac]
  rw [h2] at eS₂
  have esgnq := Encl.mulR_encloses (Encl.const_encloses _ 1 1) eiq hsgnq
  rw [← neg_one_pow_eq_sfrac, ← rpow_neg_quarter_mk _ (sfrac_div_two_pi_nonneg tn td)] at esgnq
  have eP := Encl.subR_encloses esqT (Encl.const_encloses false ν 1) hP
  exact ⟨eS₂, esqT, esgnq, eP, corrLeaves_encloses htab eP hL⟩

theorem cos_ne_zero_of_endpointPos {tn td ν : ℕ} (hpos : endpointPos tn td = true)
    (hν : ⌊Real.sqrt (sfrac false tn td / (2 * Real.pi))⌋₊ = ν) :
    Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
      * (Real.sqrt (sfrac false tn td / (2 * Real.pi)) - sfrac false ν (nat_lit 1))) ≠ 0 := by
  simp only [endpointPos, Bool.and_eq_true] at hpos
  exact cos_two_pi_p_ne_zero_mk _ tn td ν rfl hpos.1 hpos.2 hν

theorem approx₀Of_encloses {tn td ν Q : ℕ} {A : ApproxParts} {e : Encl}
    (hpos : endpointPos tn td = true)
    (hν : ⌊Real.sqrt (sfrac false tn td / (2 * Real.pi))⌋₊ = ν)
    (hA : A.Encloses (sfrac false tn td) ν) (h : approx₀Of A Q = some e) :
    e.Encloses (hardyZApproximantRS₀ (sfrac false tn td)) := by
  simp only [approx₀Of, Option.bind_eq_some_iff] at h
  obtain ⟨ψ, hψ, b, hb, he⟩ := h
  have eψ := correction_encloses hA.L (cos_ne_zero_of_endpointPos hpos hν) hψ
  rw [hardyZApproximantRS₀_eq _ ν hν]
  exact Encl.subR_encloses hA.S₂ (Encl.mulR_encloses hA.sgnq eψ hb) he

theorem approx₁Of_encloses {tn td ν Q : ℕ} {A : ApproxParts} {e : Encl}
    (hpos : endpointPos tn td = true)
    (hν : ⌊Real.sqrt (sfrac false tn td / (2 * Real.pi))⌋₊ = ν)
    (hA : A.Encloses (sfrac false tn td) ν) (h : approx₁Of A Q = some e) :
    e.Encloses (hardyZApproximantRS (sfrac false tn td)) := by
  simp only [approx₁Of, Option.bind_eq_some_iff] at h
  obtain ⟨ψ, hψ, c₁, hc₁, isq, hisq, c, hc, k, hk, b, hb, he⟩ := h
  have hC := cos_ne_zero_of_endpointPos hpos hν
  have eψ := correction_encloses hA.L hC hψ
  have ec₁ := corrLinear_encloses hA.L hA.P eψ hC hc₁
  have ec := Encl.mulR_encloses ec₁ (Encl.inv_encloses hA.sqT hisq) hc
  rw [hardyZApproximantRS_eq _ ν hν]
  exact Encl.subR_encloses hA.S₂ (Encl.mulR_encloses hA.sgnq (Encl.addR_encloses eψ ec hk) hb) he

theorem approxPartsAt_spec {tab : TermTable} {tn td W ν : ℕ} {A : ApproxParts}
    (htab : tab.Valid) (h : approxPartsAt tab tn td W = some (ν, A)) :
    endpointPos tn td = true ∧ ⌊Real.sqrt (sfrac false tn td / (2 * Real.pi))⌋₊ = ν ∧
      A.Encloses (sfrac false tn td) ν := by
  unfold approxPartsAt at h
  by_cases hpos : endpointPos tn td = true
  · rw [if_pos hpos] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨ν', hν, A', hA, rfl, rfl⟩ := h
    exact ⟨hpos, cutoff_eq hν, approxParts_encloses htab hA⟩
  · rw [if_neg hpos] at h
    cases h

theorem approx₀_encloses {tab : TermTable} {tn td W : ℕ} {e : Encl} (htab : tab.Valid)
    (h : approx₀ tab tn td W = some e) :
    e.Encloses (hardyZApproximantRS₀ (sfrac false tn td)) := by
  obtain ⟨⟨ν, A⟩, hA, he⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hpos, hν, eA⟩ := approxPartsAt_spec htab hA
  exact approx₀Of_encloses hpos hν eA he

theorem approx₁_encloses {tab : TermTable} {tn td W : ℕ} {e : Encl} (htab : tab.Valid)
    (h : approx₁ tab tn td W = some e) :
    e.Encloses (hardyZApproximantRS (sfrac false tn td)) := by
  obtain ⟨⟨ν, A⟩, hA, he⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hpos, hν, eA⟩ := approxPartsAt_spec htab hA
  exact approx₁Of_encloses hpos hν eA he

/-! ### The linear-free approximant in fixed point -/

theorem thetaF_encloses {tn td W Q : ℕ} {c : ThetaConsts} {H lp θ : Fx} (hQ : 0 < Q)
    (hH : H.Encloses Q (Real.pi / 2)) (hlp : lp.Encloses Q (Real.log Real.pi))
    (h : thetaF tn td W Q c H lp = some θ) :
    θ.Encloses Q (riemannSiegelThetaApproximant 2 0 (sfrac false tn td)) := by
  unfold thetaF at h
  by_cases hc : thetaFOk tn td c = true
  · rw [if_pos hc] at h
    simp only [thetaFOk, thetaOk, Bool.and_eq_true, and_assoc] at hc
    obtain ⟨htn, htd, hS, hQc, hV, hT4, hT2, hRn, hRd, hT4p, hT2p, hRdp⟩ := hc
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨lSQ, hlSQ, L, hL, atn, hatn, A, hA, rfl⟩ := h
    rw [riemannSiegelThetaApproximant_two_zero_mk _ tn td _ _ _ _ _ _ _ rfl htn htd hS hQc hV hT4
      hT2 hRn hRd]
    have elSQ := logRatSigned_encloses hlSQ
    rw [← sfrac_false_div] at elSQ
    have eL := Fx.ofEncl_encloses hQ elSQ hL
    have eA := Fx.ofEncl_encloses hQ (arctanRat_encloses hatn) hA
    have e1 := Fx.mul_encloses hQ (Fx.ofRat_encloses hQ (Nat.le_of_ble_eq_true hT4p) false
      (a := tn)) eL
    have e2 := Fx.divNat_encloses hQ (by norm_num : 0 < 4) (Fx.sub_encloses hH eA)
    have e3 := Fx.ofRat_encloses hQ (Nat.le_of_ble_eq_true hT2p) false (a := tn)
    have e4 := Fx.mul_encloses hQ e3 hlp
    have e5 := Fx.ofRat_encloses hQ (Nat.le_of_ble_eq_true hRdp) true (a := c.Rn)
    have hq : sfrac false 1 4 * (sfrac false 1 2 * Real.pi - Real.arctan ((td : ℝ) / (c.V : ℝ)))
        = (Real.pi / 2 - Real.arctan ((td : ℝ) / (c.V : ℝ))) / ((4 : ℕ) : ℝ) := by
      simp only [sfrac]; push_cast; ring
    rw [hq]
    exact Fx.add_encloses (Fx.sub_encloses (Fx.sub_encloses (Fx.sub_encloses e1 e2) e3) e4) e5
  · rw [if_neg hc] at h
    cases h

theorem corrF_encloses {tab : TermTable} {H TP P ψ : Fx} {p : ℝ} (htab : tab.Valid)
    (hH : H.Encloses tab.Q (Real.pi / 2))
    (hTP : TP.Encloses tab.Q (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi))
    (hP : P.Encloses tab.Q p)
    (hC : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0)
    (h : corrF tab H TP P = some ψ) : ψ.Encloses tab.Q (Zeta.RiemannSiegel.correction p) := by
  simp only [corrF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨CS, hCS, iC, hiC, cs, hcs, rfl⟩ := h
  rw [correction_mk p hC]
  have eCS := Fx.cosSinT_encloses htab.Q hH htab.trig (Fx.mul_encloses htab.Q hTP hP) hCS
  have eiC := Fx.inv_encloses eCS.1 hiC
  have eq := Fx.sub_encloses (Fx.sub_encloses (Fx.mul_encloses htab.Q hP hP) hP)
    (Fx.ofRat_encloses htab.Q (by norm_num : 0 < 16) false (a := 1))
  have ecs := Fx.cosSinT_encloses htab.Q hH htab.trig (Fx.mul_encloses htab.Q hTP eq) hcs
  exact Fx.mulExact_encloses htab.Q eiC ecs.1

theorem signPow_encloses {Q ν : ℕ} {X : Fx} {x : ℝ} (hX : X.Encloses Q x) :
    (signPow ν X).Encloses Q ((-1) ^ ν * x) := by
  unfold signPow
  rcases Nat.mod_two_eq_zero_or_one ν with h | h
  · have hp : (-1 : ℝ) ^ ν = 1 := Even.neg_one_pow (Nat.even_iff.mpr h)
    rw [if_neg (by simp [h]), hp, one_mul]; exact hX
  · have hp : (-1 : ℝ) ^ ν = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr h)
    rw [if_pos (by simp [h]), hp, neg_one_mul]; exact Fx.neg_encloses hX

theorem approx₀FWith_encloses {tab : TermTable} {tn td W ν : ℕ} {H TP ITP lp A : Fx}
    (htab : tab.Valid) (hH : H.Encloses tab.Q (Real.pi / 2))
    (hTP : TP.Encloses tab.Q (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi))
    (hITP : ITP.Encloses tab.Q (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi)⁻¹)
    (hlp : lp.Encloses tab.Q (Real.log Real.pi)) (hpos : endpointPos tn td = true)
    (hν : ⌊Real.sqrt (sfrac false tn td / (2 * Real.pi))⌋₊ = ν)
    (h : approx₀FWith tab tn td W ν H TP ITP lp = some A) :
    A.Encloses tab.Q (hardyZApproximantRS₀ (sfrac false tn td)) := by
  have hQ := htab.Q
  simp only [approx₀FWith, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨θ, hθ, S, hS, sqT, hsqT, q, hq, iq, hiq, ψ, hψ, rfl⟩ := h
  have hpos' := hpos
  simp only [endpointPos, Bool.and_eq_true] at hpos'
  have htd := Nat.le_of_ble_eq_true hpos'.2
  have eS := mainSumF_encloses htab (thetaF_encloses hQ hH hlp hθ) hS
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have eT := Fx.mul_encloses hQ (Fx.ofRat_encloses hQ htd false (a := tn)) hITP
  rw [h2, ← div_eq_mul_inv] at eT
  have esqT := Fx.sqrt_encloses eT hsqT
  have eiq := Fx.inv_encloses (Fx.sqrt_encloses esqT hq) hiq
  rw [← rpow_neg_quarter_mk _ (sfrac_div_two_pi_nonneg tn td)] at eiq
  have hνR : ((ν : ℤ) : ℝ) = sfrac false ν (nat_lit 1) := by simp [sfrac]
  have eP := Fx.sub_encloses esqT (Fx.ofInt_encloses hQ ν)
  rw [hνR] at eP
  have eψ := corrF_encloses htab hH hTP eP (cos_ne_zero_of_endpointPos hpos hν) hψ
  rw [hardyZApproximantRS₀_eq _ ν hν, Zeta.RiemannSiegel.mainSumOfPhase, two_mul]
  exact Fx.sub_encloses (Fx.add_encloses eS eS)
    (Fx.mul_encloses hQ (signPow_encloses eiq) eψ)

theorem approx₀F_encloses {tab : TermTable} {tn td W : ℕ} {e : Encl} (htab : tab.Valid)
    (h : approx₀F tab tn td W = some e) :
    e.Encloses (hardyZApproximantRS₀ (sfrac false tn td)) := by
  unfold approx₀F at h
  by_cases hpos : endpointPos tn td = true
  · rw [if_pos hpos] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ν, hν, H, hH, TP, hTP, ITP, hITP, lp, hlp, A, hA, rfl⟩ := h
    exact Fx.toEncl_encloses (approx₀FWith_encloses htab (htab.H H hH) (htab.tp TP hTP)
      (htab.itp ITP hITP) (htab.logPiF lp hlp) hpos (cutoff_eq hν) hA)
  · rw [if_neg hpos] at h
    cases h

/-! ### The error bound `hardyZErrorBoundRS₀ t` -/

theorem errBoundWith_encloses {tn td Q : ℕ} {e : Encl} (h : errBoundWith tn td Q = some e) :
    e.Encloses (hardyZErrorBoundRS₀ (sfrac false tn td)) := by
  unfold errBoundWith at h
  by_cases hc : (Nat.ble 1 tn && Nat.ble 1 td) = true
  · rw [if_pos hc] at h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨htn, htd⟩ := hc
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨T, hT, s, hs, q, hq, qT, hqT, i₁, hi₁, m₂, hm₂, m₃, hm₃, i₂, hi₂, r₂, hr₂, r₃, hr₃,
      i₃, hi₃, a₁, ha₁, a₂, ha₂, a₃, ha₃, s₁, hs₁, he⟩ := h
    have eT := tDivTwoPi_encloses hT
    have eq := Encl.sqrt_encloses (Encl.sqrt_encloses eT hs) hq
    have eqT := Encl.mulR_encloses eq eT hqT
    have em₃ := Encl.mulR_encloses (Encl.mulR_encloses eqT eqT hm₂) eqT hm₃
    have er₃ := Encl.mulR_encloses (Encl.mulR_encloses eq eq hr₂) eq hr₃
    have ea₁ := Encl.mulR_encloses (Encl.const_encloses false 25 4) (Encl.inv_encloses eqT hi₁) ha₁
    have ea₂ := Encl.mulR_encloses (Encl.const_encloses false 1 32) (Encl.inv_encloses em₃ hi₂) ha₂
    have ea₃ := Encl.mulR_encloses (Encl.const_encloses false 13 10) (Encl.inv_encloses er₃ hi₃)
      ha₃
    rw [hardyZErrorBoundRS₀_mk _ tn td rfl htn htd]
    exact Encl.addR_encloses (Encl.addR_encloses ea₁ ea₂ hs₁) ea₃ he
  · rw [if_neg hc] at h
    cases h

theorem errBound_encloses {tn td W : ℕ} {e : Encl} (h : errBound tn td W = some e) :
    e.Encloses (hardyZErrorBoundRS₀ (sfrac false tn td)) :=
  errBoundWith_encloses h

theorem errBound₁With_encloses {tn td Q : ℕ} {e : Encl} (h : errBound₁With tn td Q = some e) :
    e.Encloses (hardyZErrorBoundRS (sfrac false tn td)) := by
  unfold errBound₁With at h
  by_cases hc : (Nat.ble 1 tn && Nat.ble 1 td) = true
  · rw [if_pos hc] at h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨htn, htd⟩ := hc
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨T, hT, s, hs, q, hq, qT, hqT, i₁, hi₁, m₂, hm₂, m₃, hm₃, i₂, hi₂, a₁, ha₁, a₂, ha₂,
      he⟩ := h
    have eT := tDivTwoPi_encloses hT
    have eq := Encl.sqrt_encloses (Encl.sqrt_encloses eT hs) hq
    have eqT := Encl.mulR_encloses eq eT hqT
    have em₃ := Encl.mulR_encloses (Encl.mulR_encloses eqT eqT hm₂) eqT hm₃
    have ea₁ := Encl.mulR_encloses (Encl.const_encloses false 25 4) (Encl.inv_encloses eqT hi₁) ha₁
    have ea₂ := Encl.mulR_encloses (Encl.const_encloses false 1 32) (Encl.inv_encloses em₃ hi₂) ha₂
    rw [hardyZErrorBoundRS_mk _ tn td rfl htn htd]
    exact Encl.addR_encloses ea₁ ea₂ he
  · rw [if_neg hc] at h
    cases h

theorem errBound₁_encloses {tn td W : ℕ} {e : Encl} (h : errBound₁ tn td W = some e) :
    e.Encloses (hardyZErrorBoundRS (sfrac false tn td)) :=
  errBound₁With_encloses h

end Native
