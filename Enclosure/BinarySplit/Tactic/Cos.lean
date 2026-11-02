module

public import Enclosure.BinarySplit.Functions.Cos
public import Enclosure.BinarySplit.Tactic.Engine
public import Enclosure.BinarySplit.Tactic.Recognizer
public meta import Enclosure.BinarySplit.Tactic.Engine
public meta import Enclosure.BinarySplit.Functions.Cos

/-!
# `cos` certificate builders

The metaprogram side of `Functions.Cos`: term-count search and the even/odd certificate
builders (`mkCosPos`).
-/
@[expose] public section


namespace BSN
open Enclosure

/-- Least `M` satisfying the cos tail guard at `k = 4M`: the shared `trigTermCountAux`
seeded at `k = 0`. -/
private meta def cosTermCount (u v D : ℕ) : ℕ := trigTermCountAux u v 0 0 (2 * D) 1

open Lean Elab Term Meta in
/-- Core for `cos (u/v)` at `1/D` via binary splitting. -/
meta def cosCore (u v D : ℕ) : MetaM (Int × ℕ × ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) := do
  let Q := dyadicDenom D
  let M := cosTermCount u v D
  let evenQ : ℕ → ℕ := fun k => v ^ 4 * ((4 * k + 1) * (4 * k + 2) * (4 * k + 3) * (4 * k + 4))
  let oddQ : ℕ → ℕ := fun k => v ^ 4 * ((4 * k + 3) * (4 * k + 4) * (4 * k + 5) * (4 * k + 6))
  let (Te, Qe, Pe) := evalFoldGen (fun _ => u ^ 4) evenQ 0 (M - 1)
  let (To, Qo, Po) := evalFoldGen (fun _ => u ^ 4) oddQ 0 (M - 1)
  let Ne : ℕ := Qe + Te; let No : ℕ := u ^ 2 * (Qo + To); let Do : ℕ := 2 * v ^ 2 * Qo
  let s : Int := (Ne : Int) * Do - (No : Int) * Qe
  let m : Int := Int.fdiv (s * (Q : Int)) ((Qe : Int) * Do)
  return (m, Q, M, (Te, Qe, Pe), (To, Qo, Po))

open Lean Elab Term Meta in
/-- Build the cos inner enclosure `Real.IsNear (cos (↑u/↑v)) neg cn Q 1 D`; return
`(proof, neg, cn, Q)` with the sign decided in `MetaM` from the signed rounding. A thin wrapper
over the shared `mkEvenOddCertCore` (even value `(Qe+Te)/Qe`, odd `u²(Qo+To)/(2v²·Qo)`,
8 leading side conditions of the sign-specialized `cos_dyadic_bound_f`/`_t`). -/
meta def mkCosPos (u v D : ℕ) : MetaM (Expr × Bool × ℕ × ℕ) := do
  let M := cosTermCount u v D
  mkEvenOddCertCore ``cosEvenP ``cosEvenQ ``cosOddP ``cosOddQ
    (cosEvenP u) (cosEvenQ v) (cosOddP u) (cosOddQ v) u v M D
    (fun (Te, Qe, To, Qo) => (Qe + Te, Qe, u ^ 2 * (Qo + To), 2 * v ^ 2 * Qo))
    ``cos_dyadic_bound_f ``cos_dyadic_bound_t 8

end BSN
