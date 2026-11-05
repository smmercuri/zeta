module

public import Bernoulli.BernoulliValues
public import Enclosure.BinarySplit.Basic

/-!
# Bernoulli values in real `sfrac` form

Bridges `Bernoulli.BernoulliValues` to the form the zeta certificate tactics consume:
`(bernoulli (2*k) : ℝ) = sfrac neg p q` with literal `p`, `q`. `bern_real_tangent_pos`/`_neg`
certify one value from the tangent number `T_{m+1}`; `derive_bern_real N` materialises
`bern_real_1 … bern_real_N`.
-/
@[expose] public section


namespace BSN
open Enclosure

open TangentNumbers

/-- `B_{2m+2}` for even `m` (positive value) in real `sfrac` form: `p/q` validated against
`(2m+2)·T_{m+1} / (2^{2m+2}(2^{2m+2}−1))` by one cross-multiplication. -/
theorem bern_real_tangent_pos (m Tn p q : ℕ)
    (hT : tangentNumber (m + 1) = Tn)
    (hm : Nat.beq (m % 2) 0 = true)
    (hq : Nat.ble 1 q = true)
    (hcross : Nat.beq (p.mul ((Nat.pow 2 ((Nat.mul 2 m).add 2)).mul
          ((Nat.pow 2 ((Nat.mul 2 m).add 2)).sub 1)))
        (q.mul (((Nat.mul 2 m).add 2).mul Tn)) = true) :
    (bernoulli (2 * m + 2) : ℝ) = sfrac false p q := by
  have hme : Even m := Nat.even_iff.mpr (Nat.eq_of_beq_eq_true hm)
  have hq : 0 < q := pos_of_ble hq
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Nat.sub_eq] at hcross
  have h1 : (1 : ℕ) ≤ 2 ^ (2 * m + 2) := Nat.one_le_two_pow
  have hcQ : ((p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1)) : ℕ) : ℚ)
      = ((q * ((2 * m + 2) * Tn) : ℕ) : ℚ) := by
    exact_mod_cast Nat.eq_of_beq_eq_true hcross
  push_cast [Nat.cast_sub h1] at hcQ
  have hQ : bernoulli (2 * m + 2) = (p : ℚ) / (q : ℚ) := by
    rw [bernoulli_eq_tangent_intDiv m, hT, hme.neg_one_pow, one_mul,
      div_eq_div_iff (by exact_mod_cast intDenom_ne_zero m)
        (by exact_mod_cast hq.ne')]
    push_cast [Nat.cast_sub h1]
    linear_combination -hcQ
  rw [hQ]
  exact sfrac_ratCast_natDiv p q

/-- `B_{2m+2}` for odd `m` (where the value is negative) in real `sfrac` form; the mirror of
`bern_real_tangent_pos`. -/
theorem bern_real_tangent_neg (m Tn p q : ℕ)
    (hT : tangentNumber (m + 1) = Tn)
    (hm : Nat.beq (m % 2) 1 = true)
    (hq : Nat.ble 1 q = true)
    (hcross : Nat.beq (p.mul ((Nat.pow 2 ((Nat.mul 2 m).add 2)).mul
          ((Nat.pow 2 ((Nat.mul 2 m).add 2)).sub 1)))
        (q.mul (((Nat.mul 2 m).add 2).mul Tn)) = true) :
    (bernoulli (2 * m + 2) : ℝ) = sfrac true p q := by
  have hmo : Odd m := Nat.odd_iff.mpr (Nat.eq_of_beq_eq_true hm)
  have hq : 0 < q := pos_of_ble hq
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Nat.sub_eq] at hcross
  have h1 : (1 : ℕ) ≤ 2 ^ (2 * m + 2) := Nat.one_le_two_pow
  have hcQ : ((p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1)) : ℕ) : ℚ)
      = ((q * ((2 * m + 2) * Tn) : ℕ) : ℚ) := by
    exact_mod_cast Nat.eq_of_beq_eq_true hcross
  push_cast [Nat.cast_sub h1] at hcQ
  have hQ : bernoulli (2 * m + 2) = -((p : ℚ) / (q : ℚ)) := by
    rw [bernoulli_eq_tangent_intDiv m, hT, hmo.neg_one_pow, ← neg_div,
      div_eq_div_iff (by exact_mod_cast intDenom_ne_zero m)
        (by exact_mod_cast hq.ne')]
    push_cast [Nat.cast_sub h1]
    linear_combination hcQ
  rw [hQ, sfrac_true_div]
  push_cast
  ring

/-! ## The generator -/

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Command in
/-- `derive_bern_real N` adds `bern_real_1 … bern_real_N`, each
`bern_real_k : (bernoulli (2 * k) : ℝ) = sfrac neg p q` with `±p/q` the reduced value of `B_{2k}`.
`N ≤ 99` (the tangent table's range). -/
elab "derive_bern_real " nStx:num : command => do
  let N := nStx.getNat
  if 100 ≤ N then throwError "derive_bern_real: the shared tangent table covers k ≤ 99"
  liftTermElabM do
    let curNs ← getCurrNamespace
    for k in [1:N+1] do
      let m := k - 1
      -- `tangentNumber k = Tₖ`: read the value straight off the per-entry env lemma
      -- `tangentNumberLit_k` that `emit_tangent_numbers` provides
      let litName := `TangentNumbers ++ Name.mkSimple s!"tangentNumberLit_{k}"
      let some info := (← getEnv).find? litName
        | throwError "derive_bern_real: no `{litName}` (does `emit_tangent_numbers` cover k = {k}?)"
      let some (_, _, rhsT) := info.type.eq?
        | throwError "derive_bern_real: `{litName}` is not an equality"
      let some Tval ← getNatValue? rhsT
        | throwError "derive_bern_real: `{litName}` has a non-literal value"
      let A : ℕ := (2 * m + 2) * Tval
      let Dq : ℕ := 2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1)
      let g := Nat.gcd A Dq
      let p := A / g
      let q := Dq / g
      let neg := m % 2 == 1
      let hT : Expr := .const litName []
      let lemName : Name := if neg then ``bern_real_tangent_neg else ``bern_real_tangent_pos
      let proof := mkAppN (.const lemName [])
        #[mkRawNatLit m, mkRawNatLit Tval, mkRawNatLit p, mkRawNatLit q, hT,
          reflBoolTrue, reflBoolTrue, reflBoolTrue]
      let negStx := mkIdent (if neg then ``Bool.true else ``Bool.false)
      let stmt ← elabTermAndSynthesize
        (← `((bernoulli (2 * $(quote k)) : ℝ) = sfrac $negStx $(quote p) $(quote q)))
        (some (.sort .zero))
      let nm := curNs ++ Name.mkSimple ("bern_real_" ++ toString k)
      addDecl (.thmDecl { name := nm, levelParams := [], type := stmt, value := proof })

/-! ### The table: `bern_real_1 … bern_real_99` (`B_2 … B_198`) -/

derive_bern_real 99

example : (bernoulli (2 * 1) : ℝ) = sfrac false 1 6 := bern_real_1
example : (bernoulli (2 * 6) : ℝ) = sfrac true 691 2730 := bern_real_6

end BSN
