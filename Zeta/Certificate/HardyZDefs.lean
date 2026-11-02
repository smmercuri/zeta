module

public import Enclosure.BinarySplit.Basic
public import Enclosure.BinarySplit.Reduce.Sin
public import Enclosure.Complex
public import Zeta.Zeros.HardyZ
public import Zeta.Gram.Block
public import Zeta.EulerMaclaurin.ErrorBound
public import Zeta.RiemannSiegel.FirstOrder
public import Zeta.Analysis.Complex.Arg
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The Euler–Maclaurin Hardy `Z` approximants, and the identities the enclosures certify

Local statements of the four approximant definitions from the zero-certificate development
(`Zeta/EulerMaclaurin` + `Zeta/Zeros` on the main branch), kept verbatim so that a merge needs
only definitional bridges, together with the algebraic identities that connect them to the
shapes the enclosure builders assemble:

- the folding identity for the zeta approximant (`N^{-s-(2k-1)} = N^{-s}·(N^{2k-1})⁻¹` collapses
  the Bernoulli tail onto the single `N^{-s}` factor);
- the real-part expansion `Re(e^{iθ}·ζ) = cos θ·Re ζ − sin θ·Im ζ` behind the Hardy `Z` value.

Everything here is `∀`-quantified mathematics; the per-instance work (rectangles, radii, kernel
checks) lives in the metaprogram layer.
-/
@[expose] public section


open scoped Nat

namespace Enclosure

/-- Rectangle identity for `(n:ℂ)^s` (`n > 0`, `s = σ + i·t`):
`(↑n)^s = ⟨exp(σ·log n)·cos(t·log n), exp(σ·log n)·sin(t·log n)⟩`. -/
theorem natCast_cpow_eq (n : ℕ) (hn : 0 < n) (σ t : ℝ) :
    ((n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      ⟨Real.exp (σ * Real.log n) * Real.cos (t * Real.log n),
       Real.exp (σ * Real.log n) * Real.sin (t * Real.log n)⟩ := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (by positivity)]
  have hstd : ((Real.log n : ℝ) : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I)
            = ((Real.log n * σ : ℝ) : ℂ) + ((Real.log n * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [Complex.cpow_def_of_ne_zero hn0, hlog, hstd]
  apply Complex.ext
  · rw [Complex.exp_re]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      add_zero, mul_one]
    congr 1 <;> congr 1 <;> ring
  · rw [Complex.exp_im]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      add_zero, mul_one]
    congr 1 <;> congr 1 <;> ring

/-- `|(XP − XN)/Xd − (YP − YN)/Yd| ≤ δn/δd` for two signed fractions given by their natural parts,
as one Boolean check on numerals: both one-sided inequalities, cleared of denominators. Written in
`Nat.mul`/`Nat.add` so a kernel `reflBoolTrue` check never unfolds an arithmetic instance. -/
def natAbsSubLe (XP XN Xd YP YN Yd δn δd : ℕ) : Bool :=
  Nat.ble (((XP.mul Yd).add (YN.mul Xd)).mul δd)
      ((δn.mul (Xd.mul Yd)).add (((XN.mul Yd).add (YP.mul Xd)).mul δd)) &&
    Nat.ble (((YP.mul Xd).add (XN.mul Yd)).mul δd)
      ((δn.mul (Xd.mul Yd)).add (((YN.mul Xd).add (XP.mul Yd)).mul δd))

/-- The real inequality a `natAbsSubLe` check certifies. -/
theorem abs_sub_le_of_natAbsSubLe {XP XN Xd YP YN Yd δn δd : ℕ}
    (hXd : 0 < Xd) (hYd : 0 < Yd) (hδd : 0 < δd)
    (h : natAbsSubLe XP XN Xd YP YN Yd δn δd = true) :
    |((XP : ℝ) - XN) / Xd - ((YP : ℝ) - YN) / Yd| ≤ (δn : ℝ) / δd := by
  simp only [natAbsSubLe, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hX : (0 : ℝ) < Xd := by exact_mod_cast hXd
  have hY : (0 : ℝ) < Yd := by exact_mod_cast hYd
  have hδ : (0 : ℝ) < δd := by exact_mod_cast hδd
  have h1' : ((XP : ℝ) * Yd + YN * Xd) * δd ≤ δn * (Xd * Yd) + (XN * Yd + YP * Xd) * δd := by
    exact_mod_cast h1
  have h2' : ((YP : ℝ) * Xd + XN * Yd) * δd ≤ δn * (Xd * Yd) + (YN * Xd + XP * Yd) * δd := by
    exact_mod_cast h2
  have e : ((XP : ℝ) - XN) / Xd - ((YP : ℝ) - YN) / Yd
      = ((XP : ℝ) * Yd + YN * Xd - (XN * Yd + YP * Xd)) / (Xd * Yd) := by
    field_simp
    ring
  have hXY : (0 : ℝ) < Xd * Yd := mul_pos hX hY
  rw [e, abs_div, abs_of_pos hXY, div_le_div_iff₀ hXY hδ]
  rcases abs_cases ((XP : ℝ) * Yd + YN * Xd - (XN * Yd + YP * Xd)) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;> nlinarith

end Enclosure

namespace BSN
open Enclosure

open Complex

/-- The strengthened Hardy `Z` error bound: the theta Stirling error times the approximant
modulus, plus the *named* zeta remainder bound. On the main branch,
`norm_zetaRemainder_le` bounds `‖zetaRemainder‖` by `zetaRemainderBound`, so a value exceeding this
quantity exceeds `hardyZErrorBoundEM` as well; this is the quantity the enclosure layer bounds. -/
noncomputable abbrev hardyZErrorBoundStrong (M N : ℕ) (t : ℝ) : ℝ :=
  riemannSiegelThetaStirlingErrorBound M (thetaShift M)
      * ‖zetaApproximant (1 / 2 + Complex.I * t) M N‖
    + zetaRemainderBound (1 / 2 + Complex.I * t) M N

/-- The strengthened bound dominates the working bound: substitute `norm_zetaRemainder_le`
(`‖zetaRemainder‖ ≤ zetaRemainderBound`) into the sum. The `-(2M+1) < s.re` hypothesis is
trivial at `s.re = ½`; `1 ≤ N` is carried as a kernel-checked `Nat.ble` literal. -/
theorem hardyZErrorBoundEM_le_strong (M N : ℕ) (t : ℝ) (hN : Nat.ble 1 N = true) :
    hardyZErrorBoundEM M N t ≤ hardyZErrorBoundStrong M N t := by
  have hN' : 1 ≤ N := Nat.le_of_ble_eq_true hN
  have hs : -(2 * M + 1 : ℝ) < (1 / 2 + Complex.I * (t : ℂ)).re := by
    have hre : (1 / 2 + Complex.I * (t : ℂ)).re = 1 / 2 := by simp
    rw [hre]
    have : (0 : ℝ) ≤ 2 * M + 1 := by positivity
    linarith
  exact add_le_add le_rfl (norm_zetaRemainder_le _ M N hN' hs)

/-- Chain a bound comparison through a stronger bound, all arguments explicit (the
`hardy_error_ok_full` assembly step). -/
theorem gt_trans_le (x s b : ℝ) (hle : b ≤ s) (h : x > s) : x > b := lt_of_le_of_lt hle h

/-! ### The identities the builders certify against -/

/-- `Re(e^{iθ}·ζ) = cos θ·Re ζ − sin θ·Im ζ`: what the Hardy `Z` assembly (cos/sin images of the
theta enclosure against the zeta rectangle) is an enclosure of. -/
theorem re_exp_mul (θ : ℝ) (ζ : ℂ) :
    (Complex.exp (Complex.I * (θ : ℂ)) * ζ).re = Real.cos θ * ζ.re - Real.sin θ * ζ.im := by
  rw [mul_comm Complex.I, Complex.exp_mul_I, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
    Complex.sin_ofReal_im]

/-- The folding identity: every `N`-power in the boundary and Bernoulli terms is `N^{-s}` times
an exact quantity, so `ζ̃` is the head sum plus `N^{-s}` times a single (rational when `s` is
rational) multiplier. This is the shape `mkZetaApproxCNear` assembles. -/
theorem zetaApproximant_eq_folded (s : ℂ) (M N : ℕ) (hN : 0 < N) :
    zetaApproximant s M N
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2
            + ∑ k ∈ Finset.Icc 1 M,
                ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
                  * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h1s : (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0, Complex.cpow_one]
  have hks : ∀ k : ℕ, (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))
      = (N : ℂ) ^ (-s) * ((N : ℂ) ^ (2 * k - 1))⁻¹ := fun k => by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0]
    congr 1
    rw [Complex.cpow_neg, Complex.cpow_natCast]
  have hsum : (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
      = (N : ℂ) ^ (-s) * ∑ k ∈ Finset.Icc 1 M,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
            * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hks k]
    ring
  rw [zetaApproximant, h1s, hsum]
  ring

/-! ### Leaf values in rectangle form

Each exact complex leaf of the approximants (`s`, `s + n`, `w + j`, plain constants) equals an
explicit `⟨sfrac, sfrac⟩` pair, so a radius-zero constant rectangle names it through
`Complex.IsNear.of_eq`. The component numerators stay symbolic ℕ arithmetic (`(1+4j)·td` and
the like); at literal instantiations the kernel evaluates them against the constant's literal
fields. -/

/-- The critical-line point `s = ½ + i·t` in rectangle form, for a recognised rational `t`. -/
theorem s_crit_mk (t : ℝ) (tneg : Bool) (tn td : ℕ) (ht : t = sfrac tneg tn td) :
    (1 / 2 + Complex.I * (t : ℂ)) = ⟨sfrac false (nat_lit 1) (nat_lit 2), sfrac tneg tn td⟩ := by
  subst ht
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sfrac_false_div]

/-- The shifted critical-line point `s + n = (1+2n)/2 + i·t` in rectangle form. -/
theorem s_add_nat_mk (t : ℝ) (tneg : Bool) (tn td n : ℕ) (ht : t = sfrac tneg tn td) :
    (1 / 2 + Complex.I * (t : ℂ)) + (n : ℂ)
      = ⟨sfrac false (Nat.add 1 (Nat.mul 2 n)) (nat_lit 2), sfrac tneg tn td⟩ := by
  simp only [Nat.mul_eq, Nat.add_eq]
  subst ht
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sfrac_false_div]
  ring

/-- The shifted Stirling point `w + j = ¼ + i·t/2 + j = ((1+4j)·td)/(4·td) + i·(tn/(2·td))` in
rectangle form (`td > 0`). The component fractions share the denominators the `cLogNear` call
uses. -/
theorem w_shift_mk (t : ℝ) (tneg : Bool) (tn td j : ℕ) (ht : t = sfrac tneg tn td)
    (htd : Nat.ble 1 td = true) :
    1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)
      = ⟨sfrac false ((Nat.add 1 (Nat.mul 4 j)).mul td) (Nat.mul 4 td),
         sfrac tneg (Nat.mul 2 tn) (Nat.mul 4 td)⟩ := by
  simp only [Nat.mul_eq, Nat.add_eq]
  subst ht
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, sfrac_false_div]
    field_simp
  · cases tneg <;> simp [Complex.add_im, Complex.mul_im, sfrac] <;> field_simp <;> ring

/-- `(ascPochhammer ℂ 1).eval s = s`: the base of the named Pochhammer chain
(`ascPochhammer_succ_eval_c` supplies each further step). The index is a raw literal
(`nat_lit`), matching the raw index the step lemma leaves behind, so the chain's rename seams
stay syntactic. -/
theorem ascPochhammer_one_eval (s : ℂ) : (ascPochhammer ℂ (nat_lit 1)).eval s = s := by
  rw [ascPochhammer_one, Polynomial.eval_X]

/-- `ascPochhammer_succ_eval` specialized to `ℂ`, with the successor index a literal `b` tied
by `Nat.beq`. Stating the left side at the literal (rather than `n + 1`) keeps the renamed
value's index a raw numeral: the next step's `of_eq` then compares the two sides syntactically
instead of unfolding the numeral — which cascaded into the kernel walking the whole ℂ
`HMul`/`Complex.instMul` instance chain (measured 2 `Complex.re` + 2 `Complex.im` + 2
`HMul.hMul`/`Mul.mul` unfolds per Pochhammer step). -/
theorem ascPochhammer_succ_eval_c (n b : ℕ) (s : ℂ) (hb : Nat.beq b (n.add 1) = true) :
    (ascPochhammer ℂ b).eval s = (ascPochhammer ℂ n).eval s * (s + n) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact ascPochhammer_succ_eval n s

/-- `0 : ℂ` in rectangle form (the empty-sum base of a named complex sum). -/
theorem complex_zero_mk : (0 : ℂ)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  apply Complex.ext <;> simp [sfrac]

/-! ### Naming the zeta approximant

The folded form is assembled leaf-by-leaf: `n^{-s}` rectangles renamed through `cpow_neg_s_mk`
(whose right side is the exact expression the cpow builder produces), the two sums unfolded
term-at-a-time through the `*_base`/`*_succ` lemmas (which carry the summand lambdas, so the
metaprogram never constructs one), and the exact leaves (`N/(s-1)`, `1/2`, the Bernoulli
coefficients, the integer-power reciprocals) in rectangle form. -/

/-- `n^{-s}` at `s = ½ + i·t` in the exact rectangle shape the cpow builder assembles:
magnitude `√(1/n)`, `cos` of the positive phase `t·log(n/1)`, `sin` negated. -/
theorem cpow_neg_s_mk (t : ℝ) (tn td n : ℕ) (ht : t = sfrac false tn td)
    (hn : Nat.ble 1 n = true) :
    (n : ℂ) ^ (-(1 / 2 + Complex.I * (t : ℂ)))
      = ⟨(Real.sqrt (n : ℝ))⁻¹
            * Real.cos (sfrac false tn td * Real.log (sfrac false n (nat_lit 1))),
         (Real.sqrt (n : ℝ))⁻¹
            * -Real.sin (sfrac false tn td * Real.log (sfrac false n (nat_lit 1)))⟩ := by
  have hn' : 0 < n := pos_of_ble hn
  have hnR : (0 : ℝ) < n := pos_real_of_ble hn
  have hexp : -(1 / 2 + Complex.I * (t : ℂ))
      = ((-(1/2) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hexp, natCast_cpow_eq n hn' (-(1/2)) (-t)]
  have hmag : Real.exp (-(1 / 2 * Real.log n)) = (Real.sqrt (n : ℝ))⁻¹ := by
    have h1 : ((1 : ℝ) / (n : ℝ)) = Real.exp (-Real.log n) := by
      rw [one_div, Real.exp_neg, Real.exp_log hnR]
    have h2 : Real.exp (-(1 / 2 * Real.log n)) = Real.sqrt (1 / (n : ℝ)) := by
      rw [h1, ← Real.exp_half]
      congr 1
      ring
    rw [h2, one_div, Real.sqrt_inv]
  have hlogsfrac : Real.log (sfrac false n (nat_lit 1)) = Real.log n := by
    rw [sfrac_false_div]; simp
  subst ht
  apply Complex.ext <;>
    simp only [hlogsfrac, neg_mul, Real.cos_neg, Real.sin_neg, hmag]

/-- The empty head sum (`N = 1`), in rectangle form. -/
theorem head_sum_base (s : ℂ) :
    (∑ n ∈ Finset.Ico (1 : ℕ) 1, (n : ℂ) ^ (-s))
        = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [Finset.Ico_self, Finset.sum_empty]
  exact complex_zero_mk

/-- Peel the top term off the head sum: `∑_{Ico 1 (a+1)} = ∑_{Ico 1 a} + a^{-s}` (`1 ≤ a`). -/
theorem head_sum_succ (s : ℂ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true)
    (ha : Nat.ble 1 a = true) :
    (∑ n ∈ Finset.Ico 1 b, (n : ℂ) ^ (-s))
      = (∑ n ∈ Finset.Ico 1 a, (n : ℂ) ^ (-s)) + (a : ℂ) ^ (-s) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_Ico_succ_top (Nat.le_of_ble_eq_true ha) _

/-- The head partial sum as a NAMED value. The per-step certificate statements then carry the
5-node application `headSumC s N` instead of the elaborated `Finset.sum` tree (~100 nodes with
its instance chain, duplicated into both rectangle components), so the kernel walks the sum
expression once, at the final `head_sum_c_eq` rename, not once per peel step. -/
noncomputable def headSumC (s : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)

/-- `head_sum_base` over the named partial sum (raw-literal index, matching the peel steps). -/
theorem head_sum_c_base (s : ℂ) : headSumC s (nat_lit 1)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ :=
  head_sum_base s

/-- `head_sum_succ` over the named partial sum. -/
theorem head_sum_c_succ (s : ℂ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true)
    (ha : Nat.ble 1 a = true) : headSumC s b = headSumC s a + (a : ℂ) ^ (-s) :=
  head_sum_succ s a b hb ha

/-- The head sum at `N = 2` is exactly `1` (`1^{-s} = 1`), in rectangle form; lets the head
accumulation seed at `n = 2` and skip the wasted full `cpow` leaf for `n = 1`. -/
theorem head_sum_c_two (s : ℂ) :
    headSumC s (nat_lit 2)
      = ⟨sfrac false (nat_lit 1) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [head_sum_c_succ s (nat_lit 1) (nat_lit 2) (by rfl) (by rfl), head_sum_c_base, Nat.cast_one,
    Complex.one_cpow]
  apply Complex.ext <;> simp [sfrac]

/-- Rename the finished named head sum back onto its `Finset.sum` form (one definitional
unfold, applied once per rectangle). -/
theorem head_sum_c_eq (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) = headSumC s N := rfl

/-- The empty Bernoulli tail (`M = 0`), in rectangle form (raw-literal upper bound, matching
the `m`-side of the first peel step). -/
theorem bern_sum_base (s : ℂ) (N : ℕ) :
    (∑ k ∈ Finset.Icc (1 : ℕ) (nat_lit 0),
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹)
      = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  rw [hIcc, Finset.sum_empty]
  exact complex_zero_mk

/-- Peel the top term off the Bernoulli tail: `∑_{Icc 1 (m+1)} = ∑_{Icc 1 m} + F (m+1)`. The
peeled top term's Pochhammer/power exponent is the literal `e = 2b − 1` (tied by `Nat.beq`), so
the step statement matches the incrementally built Pochhammer and power leaves without the
kernel reducing `2b − 1` at every peel; the summation lambdas stay generic (under binders,
never kernel-reduced). -/
theorem bern_sum_succ (s : ℂ) (N m b e : ℕ) (hb : Nat.beq b (m.add 1) = true)
    (he : Nat.beq (e.add 1) (Nat.mul 2 b) = true) :
    (∑ k ∈ Finset.Icc 1 b,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹)
      = (∑ k ∈ Finset.Icc 1 m,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
            * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹)
        + ((bernoulli (2 * b) : ℝ) / ((2 * b)! : ℝ) : ℂ)
            * (ascPochhammer ℂ e).eval s * ((N : ℂ) ^ e)⁻¹ := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  have he' : e = 2 * (m + 1) - 1 := by
    have h : e + 1 = 2 * (m + 1) := Nat.eq_of_beq_eq_true he
    omega
  subst he'
  exact Finset.sum_Icc_succ_top (by omega) _

/-- `1/2 : ℂ` in rectangle form. -/
theorem half_c_mk : (1 / 2 : ℂ)
    = ⟨sfrac false (nat_lit 1) (nat_lit 2), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  apply Complex.ext
  · simp [sfrac]
  · simp [sfrac]

/-- `N/(s-1)` at `s = ½ + i·t` in rectangle form: both components negative for `t > 0`, over
the common denominator `td² + 4tn²`. -/
theorem N_div_s_sub_one_mk (t : ℝ) (tn td N : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true) :
    (N : ℂ) / ((1 / 2 + Complex.I * (t : ℂ)) - 1)
      = ⟨sfrac true ((Nat.mul 2 N).mul (td.mul td)) ((td.mul td).add (Nat.mul 4 (tn.mul tn))),
         sfrac true ((Nat.mul 4 N).mul (tn.mul td)) ((td.mul td).add (Nat.mul 4 (tn.mul tn)))⟩ := by
  simp only [Nat.mul_eq, Nat.add_eq]
  subst ht
  have h1 : (0 : ℝ) < tn := pos_real_of_ble htn
  have h2 : (0 : ℝ) < td := pos_real_of_ble htd
  have hw : ((1 / 2 + Complex.I * ((sfrac false tn td : ℝ) : ℂ)) - 1)
      = ⟨-(1/2), (tn : ℝ) / td⟩ := by
    apply Complex.ext
    · simp [sfrac_false_div]
      norm_num
    · simp [sfrac_false_div]
  rw [hw]
  have hns : Complex.normSq ⟨-(1/2), (tn : ℝ) / td⟩ = 1/4 + (tn : ℝ)^2 / (td : ℝ)^2 := by
    rw [Complex.normSq_mk]
    ring
  apply Complex.ext
  · rw [Complex.div_re, hns]
    simp [sfrac]
    field_simp
    ring
  · rw [Complex.div_im, hns]
    simp [sfrac]
    field_simp

/-- `((N:ℂ)^m)⁻¹` in rectangle form (`N > 0`), with the power `P = N^m` a literal field. -/
theorem natCast_pow_inv_mk (N m P : ℕ) (hP : Nat.pow N m = P)
    (_hN : Nat.ble 1 N = true) :
    ((N : ℂ) ^ m)⁻¹ = ⟨sfrac false (nat_lit 1) P, sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  obtain rfl := hP
  simp only [Nat.pow_eq]
  have h : ((N : ℂ) ^ m)⁻¹ = (((N ^ m : ℕ) : ℝ) : ℂ)⁻¹ := by push_cast; ring
  rw [h, ← Complex.ofReal_inv]
  apply Complex.ext
  · rw [Complex.ofReal_re, sfrac_false_div, Nat.cast_one, one_div]
  · rw [Complex.ofReal_im]
    simp [sfrac]

/-- Primitive factorial for kernel reduction: raw `Nat.rec` + `Nat.mul` (no equation-compiler
`Nat.factorial._f`/`.match_1` and no `HMul`), so the error-leaf `mkNatEvalAux` value checks stay on
the `reduce_nat` fast path. Related to `Nat.factorial` by `factNat_eq`, which is elaborator-side. -/
def factNat (n : ℕ) : ℕ := n.rec 1 (fun k acc => Nat.mul (Nat.succ k) acc)

theorem factNat_eq (n : ℕ) : factNat n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h : factNat (k + 1) = (k + 1) * factNat k := rfl
    rw [h, ih, Nat.factorial_succ]

/-- The Bernoulli coefficient `(bernoulli 2k)/(2k)!` as a real-cast rectangle, given the
Bernoulli value in `sfrac` form and the factorial as a literal. -/
theorem bern_coeff_mk (k bn bd F : ℕ) (bneg : Bool)
    (hB : (bernoulli (2 * k) : ℝ) = sfrac bneg bn bd)
    (hF : factNat (Nat.mul 2 k) = F) (hbd : Nat.ble 1 bd = true) :
    ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
      = ⟨sfrac bneg bn (bd.mul F), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  obtain rfl := hF
  simp only [factNat_eq, Nat.mul_eq]
  have hbdR : (0 : ℝ) < bd := pos_real_of_ble hbd
  have hFR : (0 : ℝ) < ((2 * k)! : ℝ) := by exact_mod_cast (2 * k).factorial_pos
  rw [← Complex.ofReal_div]
  apply Complex.ext
  · rw [Complex.ofReal_re, hB]
    simp only [sfrac]
    cases bneg <;> (simp; field_simp)
  · rw [Complex.ofReal_im]
    simp [sfrac]

/-- The folding identity with a kernel-friendly `Nat.ble` hypothesis. -/
theorem zetaApproximant_eq_folded' (s : ℂ) (M N : ℕ) (hN : Nat.ble 1 N = true) :
    zetaApproximant s M N
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2
            + ∑ k ∈ Finset.Icc 1 M,
                ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
                  * (ascPochhammer ℂ (2 * k - 1)).eval s * ((N : ℂ) ^ (2 * k - 1))⁻¹) :=
  zetaApproximant_eq_folded s M N (pos_of_ble hN)

/-! ### Naming the theta approximant

The Stirling value at `z = w + N`, the log sum over `w + j`, and the `(t/2)·log π` correction,
each in the shapes the builders assemble. The `w`-powers `z^{1−2k}` route through the named
inverse of the natural power. -/

/-- `w + 0 − ½` in rectangle form (`N = 0`, `td > 0`): the companion of `w_sub_half_mk`, which
needs `N ≥ 1` twice over — its hypothesis, and its real numerator `(4N − 1)`, which truncates to
`0` in `ℕ` at `N = 0` where the true value is `−1/4`. Here the sign flag carries that minus
instead. Needed because `hardyZApproximantRS` pins the phase at
`riemannSiegelThetaApproximant 2 0 t`. -/
theorem w_sub_half_zero_mk (t : ℝ) (tneg : Bool) (tn td : ℕ) (ht : t = sfrac tneg tn td)
    (htd : Nat.ble 1 td = true) :
    (1 / 4 + Complex.I * ((t : ℂ) / 2) + ((nat_lit 0 : ℕ) : ℂ)) - 1 / 2
      = ⟨sfrac true td (Nat.mul 4 td), sfrac tneg (Nat.mul 2 tn) (Nat.mul 4 td)⟩ := by
  rw [w_shift_mk t tneg tn td (nat_lit 0) ht htd]
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  apply Complex.ext
  · simp only [Nat.mul_eq, mul_zero, Nat.add_eq, add_zero, one_mul, sfrac_false_div, Nat.cast_mul,
      Nat.cast_ofNat, one_div, sub_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self',
      sfrac_true_div]
    all_goals (field_simp; try ring)
  · simp

/-- `w + N − ½` in rectangle form (`N ≥ 1`, `td > 0`). -/
theorem w_sub_half_mk (t : ℝ) (tneg : Bool) (tn td N : ℕ) (ht : t = sfrac tneg tn td)
    (htd : Nat.ble 1 td = true) (hN : Nat.ble 1 N = true) :
    (1 / 4 + Complex.I * ((t : ℂ) / 2) + (N : ℂ)) - 1 / 2
      = ⟨sfrac false (((Nat.mul 4 N).sub 1).mul td) (Nat.mul 4 td),
         sfrac tneg (Nat.mul 2 tn) (Nat.mul 4 td)⟩ := by
  have hN' : 0 < N := pos_of_ble hN
  rw [w_shift_mk t tneg tn td N ht htd]
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  apply Complex.ext
  · simp only [sfrac_false_div, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, one_div,
      sub_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self']
    rw [Nat.cast_sub (by omega : 1 ≤ 4 * N)]
    push_cast
    field_simp
    ring
  · simp

/-- The `log(2π)` argument in the shape the enclosure carries (`2` as the constant `sfrac`). -/
theorem log_two_pi_eq : Real.log (2 * Real.pi)
    = Real.log (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi) := by
  norm_num [sfrac]

/-- `t/2` in the constant's `sfrac` shape. -/
theorem t_half_eq (t : ℝ) (tneg : Bool) (tn td : ℕ) (ht : t = sfrac tneg tn td) :
    t / 2 = sfrac tneg tn (2 * td) := by
  subst ht
  cases tneg <;> simp [sfrac] <;> ring

/-- The Stirling coefficient `bernoulli(2k)/(2k(2k−1))` in rectangle form (`k ≥ 1`). -/
theorem stirling_coeff_mk (k bn bd : ℕ) (bneg : Bool)
    (hB : (bernoulli (2 * k) : ℝ) = sfrac bneg bn bd)
    (hk : Nat.ble 1 k = true) (hbd : Nat.ble 1 bd = true) :
    (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1))
      = ⟨sfrac bneg bn (bd.mul ((Nat.mul 2 k).mul ((Nat.mul 2 k).sub 1))),
         sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  simp only [Nat.mul_eq, Nat.sub_eq]
  have hk' : 0 < k := pos_of_ble hk
  have hbdR : (0 : ℝ) < bd := pos_real_of_ble hbd
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast Nat.le_of_ble_eq_true hk
  have hd : (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) = (((2 * k * (2 * k - 1) : ℕ) : ℝ) : ℂ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    ring
  have hn : (bernoulli (2 * k) : ℂ) = ((bernoulli (2 * k) : ℝ) : ℂ) := by
    push_cast
    ring
  have hdR : (0 : ℝ) < ((2 * k * (2 * k - 1) : ℕ) : ℝ) := by
    have h1 : 0 < 2 * k * (2 * k - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast h1
  rw [hn, hd, ← Complex.ofReal_div]
  apply Complex.ext
  · rw [Complex.ofReal_re, hB]
    simp only [sfrac]
    cases bneg <;> (simp; field_simp)
  · rw [Complex.ofReal_im]
    simp [sfrac]

/-- `w^(1−2k : ℤ)` as the inverse of the natural power (`k ≥ 1`), the exponent a literal `e`
tied by `Nat.beq`. With a symbolic `(2k).sub 1` exponent the `of_eq` rename against the
incrementally built power `w ^ (2k−1)` (a raw literal) made the kernel unfold `Inv.inv` down
through `Complex.instInv`/`Complex.inv` into `⇑normSq` (measured 2 `DFunLike.coe` + 2
`ZeroHom.toFun` unfolds per Stirling term); with the literal the comparison is syntactic. -/
theorem zpow_one_sub_two_mul (w : ℂ) (k e : ℕ) (hk : Nat.ble 1 k = true)
    (he : Nat.beq (e.add 1) (Nat.mul 2 k) = true) :
    w ^ (1 - 2 * (k : ℤ)) = (w ^ e)⁻¹ := by
  have hk' : 0 < k := pos_of_ble hk
  have he' : e = 2 * k - 1 := by
    have h := Nat.eq_of_beq_eq_true he
    simp only [Nat.add_eq, Nat.mul_eq] at h
    omega
  subst he'
  have h : (1 - 2 * (k : ℤ)) = -(((2 * k - 1 : ℕ) : ℤ)) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    ring
  rw [h, zpow_neg, zpow_natCast]

/-- `w^(m+1) = w^m · w`, with the exponent a literal. -/
theorem pow_succ_c (w : ℂ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    w ^ b = w ^ m * w := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact pow_succ w m

/-- `w^1 = w` (raw-literal exponent, matching the literal the `pow_succ_c` chain carries: an
`OfNat` exponent here made the first step's rename walk `HPow`/`Monoid.npow` into the ℂ
multiplication instance). -/
theorem pow_one_c (w : ℂ) : w ^ (nat_lit 1) = w := pow_one w

/-- The empty Stirling correction sum, in rectangle form (raw-literal upper bound). -/
theorem stirling_sum_base (w : ℂ) :
    (∑ k ∈ Finset.Icc (1 : ℕ) (nat_lit 0),
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)))
      = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  rw [hIcc, Finset.sum_empty]
  exact complex_zero_mk

/-- Peel the top term off the Stirling correction sum. -/
theorem stirling_sum_succ (w : ℂ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    (∑ k ∈ Finset.Icc (1 : ℕ) b,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)))
      = (∑ k ∈ Finset.Icc (1 : ℕ) m,
          (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)))
        + (bernoulli (2 * b) : ℂ) / (2 * (b : ℂ) * (2 * (b : ℂ) - 1)) * w ^ (1 - 2 * (b : ℤ)) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_Icc_succ_top (by omega) _

/-- The empty log sum, in rectangle form. -/
theorem log_sum_base (t : ℝ) :
    (∑ j ∈ Finset.range 0, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
      = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ := by
  rw [Finset.range_zero, Finset.sum_empty]
  exact complex_zero_mk

/-- Peel the top term off the log sum. -/
theorem log_sum_succ (t : ℝ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    (∑ j ∈ Finset.range b, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
      = (∑ j ∈ Finset.range m, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
        + Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (m : ℂ)) := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_range_succ _ m

/-- The theta log partial sum as a NAMED value (cf. `headSumC`): keeps the per-step and
checkpoint statements small. -/
noncomputable def logSumC (t : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ))

/-- `log_sum_base` over the named partial sum (raw-literal index, matching the peel steps). -/
theorem log_sum_c_base (t : ℝ) : logSumC t (nat_lit 0)
    = ⟨sfrac false (nat_lit 0) (nat_lit 1), sfrac false (nat_lit 0) (nat_lit 1)⟩ :=
  log_sum_base t

/-- `log_sum_succ` over the named partial sum. -/
theorem log_sum_c_succ (t : ℝ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    logSumC t b = logSumC t m + Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (m : ℂ)) :=
  log_sum_succ t m b hb

/-- Rename the finished named log sum back onto its `Finset.sum` form (one definitional
unfold, applied once). -/
theorem log_sum_c_eq (t : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * ((t : ℂ) / 2) + (j : ℂ)))
      = logSumC t N := rfl

/-- `logGammaStirling M w` unfolded to its definitional body, in the exact shape the Stirling
builder assembles. Citing this once lets the builder rename its assembled enclosure onto the
compact `logGammaStirling M (w + N)` through a proven equality, instead of a `rfl` transport that
forces the kernel to delta-expand the whole gamma series at every bracket point. -/
theorem logGammaStirling_unfold (M : ℕ) (w : ℂ) :
    Complex.Stirling.logGammaStirling M w
      = (w - 1 / 2) * Complex.log w - w + (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ)
        + ∑ k ∈ Finset.Icc 1 M,
            (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ)) :=
  rfl

/-- `riemannSiegelThetaApproximant M N t` unfolded to the shape `mkThetaNamed` assembles (the
Stirling value now compact via `logGammaStirling_unfold`, the log sum in its `Finset.sum` form),
so `mkThetaApproxNamed` renames onto the approximant through this proven equality rather than a
`rfl` transport. -/
theorem riemannSiegelThetaApproximant_named (M N : ℕ) (t : ℝ) :
    riemannSiegelThetaApproximant M N t
      = ((Complex.Stirling.logGammaStirling M (1 / 4 + Complex.I * (t / 2) + N)
            - ∑ j ∈ Finset.range N, Complex.log (1 / 4 + Complex.I * (t / 2) + j)).im
          - t / 2 * Real.log Real.pi) :=
  rfl

/-- **The order-2, shift-0 theta approximant in real closed form.** With `w = ¼ + it/2`,
`Im((w − ½)·Log w) = (t/4)·log(1/16 + t²/4) − ¼·arg w`, `arg w = π/2 − arctan(1/(2t))` for
`t > 0`, `Im(−w) = −t/2`, and the Bernoulli terms `w⁻¹/12 − (w³)⁻¹/360` have an exact rational
imaginary part. So no complex arithmetic is needed to enclose `θ̃`: one real log, one small
arctan, `log π`, and rationals. -/
theorem riemannSiegelThetaApproximant_two_zero {t : ℝ} (ht : 0 < t) :
    riemannSiegelThetaApproximant 2 0 t
      = t / 4 * Real.log (1 / 16 + t ^ 2 / 4) - 1 / 4 * (Real.pi / 2 - Real.arctan (1 / (2 * t)))
        - t / 2 - t / 2 * Real.log Real.pi
        - (t / 2) / (12 * (1 / 16 + t ^ 2 / 4))
        + (3 * (1 / 16) * (t / 2) - (t / 2) ^ 3) / (360 * (1 / 16 + t ^ 2 / 4) ^ 3) := by
  set w : ℂ := 1 / 4 + Complex.I * (t / 2) with hw
  have hre : w.re = 1 / 4 := by simp [hw]
  have him : w.im = t / 2 := by simp [hw]
  have hnsq : Complex.normSq w = 1 / 16 + t ^ 2 / 4 := by
    rw [Complex.normSq_apply, hre, him]; ring
  have hnsq_pos : 0 < 1 / 16 + t ^ 2 / 4 := by positivity
  have harg : Complex.arg w = Real.pi / 2 - Real.arctan (1 / (2 * t)) := by
    rw [Complex.arg_eq_arctan (by rw [hre]; norm_num), hre, him]
    have h2t : 0 < 2 * t := by positivity
    rw [show t / 2 / (1 / 4) = 2 * t by ring, one_div, Real.arctan_inv_of_pos h2t]
    ring
  have hlog : Real.log ‖w‖ = 1 / 2 * Real.log (1 / 16 + t ^ 2 / 4) := by
    rw [Complex.norm_def, hnsq, Real.log_sqrt hnsq_pos.le]; ring
  have hw3im : (w ^ 3).im = 3 * (1 / 16) * (t / 2) - (t / 2) ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_im, Complex.mul_re, hre, him]; ring
  have hw3nsq : Complex.normSq (w ^ 3) = (1 / 16 + t ^ 2 / 4) ^ 3 := by
    rw [map_pow, hnsq]
  simp only [riemannSiegelThetaApproximant, Nat.cast_zero, add_zero, Finset.range_zero,
    Finset.sum_empty, sub_zero, Complex.Stirling.logGammaStirling_two]
  rw [← hw]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.inv_im, Complex.log_re,
    Complex.log_im, Complex.sub_re, hre, him, harg, hlog, hw3im, hw3nsq, hnsq,
    Complex.ofReal_im, Complex.ofReal_re]
  norm_num
  field_simp
  ring

/-- `riemannSiegelThetaApproximant 2 0 t` at a rational `t = tn/td`, in the shape the builder
assembles: every constant a literal (checked against `tn`, `td` by `Nat.beq`), the two
transcendental pieces `log (S/Q) = log (1/16 + t²/4)` and `arctan (td/V) = arctan (1/(2t))`, the
sealed `log π`, and the exact rational tail `−Rn/Rd`. -/
theorem riemannSiegelThetaApproximant_two_zero_mk (t : ℝ) (tn td S Q V T4 T2 Rn Rd : ℕ)
    (ht : t = sfrac false tn td) (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true)
    (hS : Nat.beq S ((td.mul td).add ((Nat.mul 4 tn).mul tn)) = true)
    (hQ : Nat.beq Q ((Nat.mul 16 td).mul td) = true) (hV : Nat.beq V (Nat.mul 2 tn) = true)
    (hT4 : Nat.beq T4 (Nat.mul 4 td) = true) (hT2 : Nat.beq T2 (Nat.mul 2 td) = true)
    (hRn : Nat.beq (Rn.add ((Nat.mul 48 tn).mul (td.pow 5)))
      (((Nat.mul 30 tn).mul td).mul (S.pow 2) |>.add ((Nat.mul 64 (tn.pow 3)).mul (td.pow 3)))
      = true)
    (hRd : Nat.beq Rd (Nat.mul 45 (S.pow 3)) = true) :
    riemannSiegelThetaApproximant 2 0 t
      = sfrac false tn T4 * Real.log (sfrac false S Q)
        - sfrac false 1 4 * (sfrac false 1 2 * Real.pi - Real.arctan ((td : ℝ) / (V : ℝ)))
        - sfrac false tn T2 - sfrac false tn T2 * Real.log Real.pi + sfrac true Rn Rd := by
  simp only [Nat.beq_eq, Nat.mul_eq, Nat.add_eq, Nat.pow_eq] at hS hQ hV hT4 hT2 hRn hRd
  subst hS hQ hV hT4 hT2 hRd ht
  have hn : (0 : ℝ) < tn := pos_real_of_ble htn
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have hRn' : (Rn : ℝ) = 30 * tn * td * ((td : ℝ) * td + 4 * tn * tn) ^ 2
      + 64 * (tn : ℝ) ^ 3 * td ^ 3 - 48 * tn * (td : ℝ) ^ 5 := by
    have := congrArg (fun n : ℕ ↦ (n : ℝ)) hRn
    push_cast at this
    linarith
  rw [riemannSiegelThetaApproximant_two_zero (by rw [sfrac_false_div]; positivity)]
  simp only [sfrac, if_false, if_true, one_mul, neg_one_mul, Bool.false_eq_true]
  have hlog : (1 / 16 + ((tn : ℝ) / td) ^ 2 / 4)
      = (((td * td + 4 * tn * tn : ℕ) : ℝ) / ((16 * td * td : ℕ) : ℝ)) := by
    push_cast; field_simp; ring
  have hatan : 1 / (2 * ((tn : ℝ) / td)) = (td : ℝ) / ((2 * tn : ℕ) : ℝ) := by
    push_cast; field_simp
  rw [hlog, hatan, hRn']
  push_cast
  field_simp
  ring


/-! ### Naming the error bound

`riemannSiegelThetaStirlingErrorBound` restructured as an exact rational times the reciprocal
of the `(2π)`-power, the norms as square roots of componentwise products, and the
`zetaRemainderBound` prefactor's real denominator folded into an exact constant. -/

/-- The theta Stirling error bound as an exact rational times `((2π)^{2M})⁻¹`. -/
theorem theta_err_eq (M N A B : ℕ)
    (hA : Nat.mul (factNat (Nat.succ (Nat.mul 2 M))) (Nat.pow 4 (Nat.mul 2 M)) = A)
    (hB : Nat.mul (Nat.mul 2 M) (Nat.pow (Nat.succ (Nat.mul 4 N)) (Nat.mul 2 M)) = B)
    (hM : Nat.ble 1 M = true) :
    riemannSiegelThetaStirlingErrorBound M N
      = sfrac false A B * ((2 * Real.pi) ^ (Nat.mul 2 M))⁻¹ := by
  obtain rfl := hA
  obtain rfl := hB
  simp only [factNat_eq, Nat.succ_eq_add_one, Nat.mul_eq, Nat.pow_eq]
  have hM' : 0 < M := pos_of_ble hM
  have hMR : (0 : ℝ) < 2 * M := by
    have : (0 : ℕ) < 2 * M := by omega
    exact_mod_cast this
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ (2 * M) := by positivity
  have h4N : (0 : ℝ) < (4 * (N : ℝ) + 1) ^ (2 * M) := by positivity
  have hz : ((1 / 4 + N : ℝ)) ^ (-(2 * M : ℤ)) = ((1 / 4 + (N : ℝ)) ^ (2 * M))⁻¹ := by
    rw [show (-(2 * M : ℤ)) = -((2 * M : ℕ) : ℤ) from by push_cast; ring, zpow_neg,
      zpow_natCast]
  have hbase : (1 / 4 + (N : ℝ)) = (4 * (N : ℝ) + 1) / 4 := by ring
  rw [riemannSiegelThetaStirlingErrorBound, hz, hbase, div_pow, sfrac_false_div]
  push_cast
  field_simp

/-- The `‖w‖`-form theta Stirling error bound at the rational endpoint `t = tn/td` as an exact
rational times `((2π)^{2M})⁻¹`: the base is `(¼+N)² + t²/4 = ((4N+1)² td² + 4 tn²)/(16 td²)`. -/
theorem theta_err_eq' (t : ℝ) (tn td M N A B : ℕ) (ht : t = sfrac false tn td)
    (hA : Nat.mul (Nat.mul (factNat (Nat.succ (Nat.mul 2 M))) (Nat.pow 2 (Nat.succ (Nat.mul 2 M))))
      (Nat.pow (Nat.mul 16 (Nat.mul td td)) M) = A)
    (hB : Nat.mul (Nat.mul 2 M) (Nat.pow (Nat.add
      (Nat.mul (Nat.mul (Nat.succ (Nat.mul 4 N)) (Nat.succ (Nat.mul 4 N))) (Nat.mul td td))
      (Nat.mul 4 (Nat.mul tn tn))) M) = B)
    (hM : Nat.ble 1 M = true) (htd : Nat.ble 1 td = true) :
    riemannSiegelThetaStirlingErrorBound' M N t
      = sfrac false A B * ((2 * Real.pi) ^ (Nat.mul 2 M))⁻¹ := by
  obtain rfl := hA
  obtain rfl := hB
  subst ht
  simp only [factNat_eq, Nat.succ_eq_add_one, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have hMR : (0 : ℝ) < 2 * M := by linarith [pos_real_of_ble hM]
  have hz : ((1 / 4 + N : ℝ) ^ 2 + (sfrac false tn td / 2) ^ 2) ^ (-(M : ℤ))
      = ((((4 * N + 1) * (4 * N + 1) * (td * td) + 4 * (tn * tn) : ℝ) / (16 * (td * td)))
            ^ M)⁻¹ := by
    rw [zpow_neg, zpow_natCast, sfrac_false_div]
    congr 2
    field_simp
    ring
  rw [riemannSiegelThetaStirlingErrorBound', hz, div_pow, sfrac_false_div]
  push_cast
  field_simp

/-- `‖z‖` as the square root of the componentwise product sum. -/
theorem norm_eq_sqrt_mul_add (z : ℂ) : ‖z‖ = Real.sqrt (z.re * z.re + z.im * z.im) := by
  rw [Complex.norm_def, Complex.normSq_apply]

/-- `2π` with the constant in `sfrac` form (the base the power chain multiplies). -/
theorem two_pi_eq : (2 : ℝ) * Real.pi = sfrac false (nat_lit 2) (nat_lit 1) * Real.pi := by
  norm_num [sfrac]

/-- `↑n · π` with the constant in `sfrac` form (the Gram-point target `idx · π`). -/
theorem natCast_mul_pi_eq (n : ℕ) : (n : ℝ) * Real.pi = sfrac false n (nat_lit 1) * Real.pi := by
  norm_num [sfrac]

/-- `x^(m+1) = x^m · x` over `ℝ`, with the exponent a literal. -/
theorem pow_succ_r (x : ℝ) (m b : ℕ) (hb : Nat.beq b (m.add 1) = true) :
    x ^ b = x ^ m * x := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact pow_succ x m

/-- `x^1 = x` over `ℝ` (raw-literal exponent; see `pow_one_c`). -/
theorem pow_one_r (x : ℝ) : x ^ (nat_lit 1) = x := pow_one x

/-- The `zetaRemainderBound` prefactor shape: the real denominator `s.re + m` at the
critical-line point is the exact rational `(1+2m)/2`, so the division folds into a constant
multiplier. -/
theorem zrb_shape_eq (x c t : ℝ) (m : ℕ) :
    x / ((1 / 2 + Complex.I * (t : ℂ)).re + ((m : ℕ) : ℝ)) * c
      = x * sfrac false (nat_lit 2) (Nat.add 1 (Nat.mul 2 m)) * c := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hre : (1 / 2 + Complex.I * (t : ℂ)).re + ((m : ℕ) : ℝ) = ((1 + 2 * m : ℕ) : ℝ) / 2 := by
    simp
    ring
  rw [hre, sfrac_false_div]
  have h0 : ((1 + 2 * m : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℕ) < 1 + 2 * m := by omega
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  field_simp
  ring

/-- `n^{-s-m}` at `s = ½ + i·t` in the cpow builder's rectangle shape: magnitude
`(√P)⁻¹` (the power `n^{1+2m}` carried as a literal `P`), phase argument `sfrac false n 1`,
matching the built enclosure so the rename transports by reflexivity. -/
theorem cpow_neg_s_sub_mk (t : ℝ) (tn td n m P : ℕ) (ht : t = sfrac false tn td)
    (hn : Nat.ble 1 n = true) (hP : Nat.pow n (Nat.add 1 (Nat.mul 2 m)) = P) :
    (n : ℂ) ^ (-(1 / 2 + Complex.I * (t : ℂ)) - ((m : ℕ) : ℂ))
      = ⟨(Real.sqrt (P : ℝ))⁻¹
            * Real.cos (sfrac false tn td * Real.log (sfrac false n (nat_lit 1))),
         (Real.sqrt (P : ℝ))⁻¹
            * -Real.sin (sfrac false tn td * Real.log (sfrac false n (nat_lit 1)))⟩ := by
  obtain rfl := hP
  simp only [Nat.mul_eq, Nat.add_eq, Nat.pow_eq]
  have hn' : 0 < n := pos_of_ble hn
  have hnR : (0 : ℝ) < n := pos_real_of_ble hn
  have hexp : -(1 / 2 + Complex.I * (t : ℂ)) - ((m : ℕ) : ℂ)
      = ((-(1 / 2) - m : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, natCast_cpow_eq n hn' (-(1 / 2) - m) (-t)]
  have hmag : Real.exp ((-(1 / 2) - m) * Real.log n)
      = (Real.sqrt ((n ^ (1 + 2 * m) : ℕ) : ℝ))⁻¹ := by
    have h1 : (((nat_lit 1 : ℕ) : ℝ) / ((n ^ (1 + 2 * m) : ℕ) : ℝ))
        = Real.exp (-(((1 + 2 * m : ℕ) : ℝ) * Real.log n)) := by
      rw [Nat.cast_one, one_div, Real.exp_neg]
      congr 1
      rw [← Real.log_pow, Real.exp_log (by positivity), Nat.cast_pow]
    have h2 : Real.exp ((-(1 / 2) - m) * Real.log n)
        = Real.sqrt (((nat_lit 1 : ℕ) : ℝ) / ((n ^ (1 + 2 * m) : ℕ) : ℝ)) := by
      rw [h1, ← Real.exp_half]
      congr 1
      push_cast
      ring
    rw [h2, Nat.cast_one, one_div, Real.sqrt_inv]
  have hlogsfrac : Real.log (sfrac false n (nat_lit 1)) = Real.log n := by
    rw [sfrac_false_div]; simp
  subst ht
  apply Complex.ext <;>
    simp only [hlogsfrac, neg_mul, Real.cos_neg, Real.sin_neg, hmag]


/-! ### Naming the Riemann–Siegel main sum

The Riemann–Siegel main sum is real, so its peel apparatus is the `ℝ` analogue of `headSumC`:
`mainSumRS` names the partial sum, `main_sum_rs_base`/`main_sum_rs_succ` peel it a term at a
time at raw literal indices, `main_sum_rs_term_mk` puts the peeled summand in the shape the
builder assembles, and `main_sum_of_phase_eq` renames the finished value back onto
`mainSumOfPhase` (which is twice it).

The phase `θ` stays an opaque real throughout: unlike `t` it is not a rational, and the
metaprogram supplies its enclosure from the Stirling builder. Only `t` is destructured into
`sfrac tn td`. -/

/-- The main sum's summand at the index `n`, in the exact real shape the builder assembles:
reciprocal square root times a cosine of the named phase `θ` minus `t·log n`, with the same
magnitude and `log` conventions as `cpow_neg_s_mk`. -/
theorem main_sum_rs_term_mk (θ t : ℝ) (tn td n : ℕ) (ht : t = sfrac false tn td) :
    Real.cos (θ - t * Real.log n) / Real.sqrt n
      = (Real.sqrt (n : ℝ))⁻¹
          * Real.cos (θ - sfrac false tn td * Real.log (sfrac false n (nat_lit 1))) := by
  have hlogsfrac : Real.log (sfrac false n (nat_lit 1)) = Real.log n := by
    rw [sfrac_false_div]; simp
  subst ht
  rw [hlogsfrac, div_eq_inv_mul]

/-- The Riemann–Siegel main sum's partial sum as a NAMED value; `mainSumOfPhase` is twice it.
Carrying the 4-node application `mainSumRS θ t ν` through the peel steps keeps the elaborated
`Finset.sum` out of every intermediate certificate, exactly as `headSumC` does on the
Euler–Maclaurin side. -/
noncomputable def mainSumRS (θ t : ℝ) (ν : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ν, Real.cos (θ - t * Real.log n) / Real.sqrt n

/-- The empty main sum (`ν = 0`), as a signed fraction. -/
theorem main_sum_rs_base (θ t : ℝ) :
    mainSumRS θ t (nat_lit 0) = sfrac false (nat_lit 0) (nat_lit 1) := by
  have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  rw [mainSumRS, hIcc, Finset.sum_empty]
  simp [sfrac]

/-- Peel the top term off the main sum: `∑_{Icc 1 b} = ∑_{Icc 1 a} + f b` (`b = a + 1`). The
peeled index is the raw literal `b`, so the next step's `of_eq` compares the two sides
syntactically instead of reducing `a + 1`; see `ascPochhammer_succ_eval_c`. -/
theorem main_sum_rs_succ (θ t : ℝ) (a b : ℕ) (hb : Nat.beq b (a.add 1) = true) :
    mainSumRS θ t b
      = mainSumRS θ t a + Real.cos (θ - t * Real.log b) / Real.sqrt b := by
  obtain rfl := Nat.eq_of_beq_eq_true hb
  exact Finset.sum_Icc_succ_top (Nat.le_add_left 1 a) _

/-- The main sum at `ν = 1` is `cos θ` (`log 1 = 0`, `√1 = 1`): lets the accumulation seed at
`n = 2` and skip a wasted `log`/`sqrt` leaf, as `head_sum_c_two` does on the EM side. -/
theorem main_sum_rs_one (θ t : ℝ) : mainSumRS θ t (nat_lit 1) = Real.cos θ := by
  rw [main_sum_rs_succ θ t (nat_lit 0) (nat_lit 1) (by rfl), main_sum_rs_base]
  simp [sfrac]

/-- Rename the finished named main sum onto `mainSumOfPhase`, the form the approximant is stated
in. The doubling is stated as `x + x` rather than `2 * x`: no enclosure builder produces a bare
`2` numeral (`mkConstNear` yields `sfrac false 2 1`), so the builder doubles with `addNear` and
this is the shape that then matches syntactically. -/
theorem main_sum_of_phase_eq (θ t : ℝ) (ν : ℕ) :
    Zeta.RiemannSiegel.mainSumOfPhase θ t ν = mainSumRS θ t ν + mainSumRS θ t ν :=
  two_mul (mainSumRS θ t ν)

/-! ### One main-sum step as a single lemma

`mainSumRS_step` adds the term `b` to the named partial sum in one kernel step: every interval
operation between the input enclosures and the next partial sum, and the range reduction of the
phase by a multiple of `π/2`, is folded into its proof, and each use checks only a few short
numeral conditions (two `natAbsSubLe`, one radius `Nat.ble`, positivity), all over one shared
denominator. Kernel cost is proportional to the number of `Nat` operations in those conditions. -/

/-! The quadrant identities and signs `mainSumRS_step` takes: `cos (r + k·π/2) = ε·g r` for
`k mod 4 = 0, 1, 2, 3` with `(g, ε) = (cos, 1), (sin, −1), (cos, −1), (sin, 1)`. The signs are named
constants so the builder can cite them. -/

/-- The quadrant sign `+1`. -/
noncomputable def quadSignPos : ℝ := 1

/-- The quadrant sign `−1`. -/
noncomputable def quadSignNeg : ℝ := -1

theorem abs_quadSignPos : |quadSignPos| = 1 := by simp [quadSignPos]

theorem abs_quadSignNeg : |quadSignNeg| = 1 := by simp [quadSignNeg]

/-- An in-range centre kept as is, for the quadrants with `ε = 1`. -/
theorem sfrac_eq_quadSignPos_mul (n : Bool) (c q : ℕ) :
    sfrac n c q = quadSignPos * sfrac n c q := by
  simp [quadSignPos]

/-- An in-range centre with its sign flipped, for the quadrants with `ε = −1`. -/
theorem sfrac_not_eq_quadSignNeg_mul (n : Bool) (c q : ℕ) :
    sfrac (!n) c q = quadSignNeg * sfrac n c q := by
  rw [sfrac_not, quadSignNeg, neg_one_mul]

private theorem exists_eq_four_mul_add_of_mod (k j : ℕ) (hk : Nat.beq (k % 4) j = true) :
    ∃ q : ℕ, k = 4 * q + j :=
  ⟨k / 4, by have := Nat.eq_of_beq_eq_true hk; have := Nat.div_add_mod k 4; omega⟩

/-- `cos (r + k·π/2) = cos r` for `k ≡ 0 (mod 4)`. -/
theorem cos_quad_nat0 (k : ℕ) (hk : Nat.beq (k % 4) 0 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignPos * Real.cos r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 0 hk
  rw [quadSignPos, one_mul, ← cos_quad0 r q]; push_cast; ring_nf

/-- `cos (r + k·π/2) = −sin r` for `k ≡ 1 (mod 4)`. -/
theorem cos_quad_nat1 (k : ℕ) (hk : Nat.beq (k % 4) 1 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignNeg * Real.sin r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 1 hk
  rw [quadSignNeg, neg_one_mul, ← cos_quad1 r q]; push_cast; ring_nf

/-- `cos (r + k·π/2) = −cos r` for `k ≡ 2 (mod 4)`. -/
theorem cos_quad_nat2 (k : ℕ) (hk : Nat.beq (k % 4) 2 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignNeg * Real.cos r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 2 hk
  rw [quadSignNeg, neg_one_mul, ← cos_quad2 r q]; push_cast; ring_nf

/-- `cos (r + k·π/2) = sin r` for `k ≡ 3 (mod 4)`. -/
theorem cos_quad_nat3 (k : ℕ) (hk : Nat.beq (k % 4) 3 = true) (r : ℝ) :
    Real.cos (r + (k : ℝ) * (Real.pi / 2)) = quadSignPos * Real.sin r := by
  obtain ⟨q, rfl⟩ := exists_eq_four_mul_add_of_mod k 3 hk
  rw [quadSignPos, one_mul, ← cos_quad3 r q]; push_cast; ring_nf

/-- One main-sum term's enclosure, `|A·cos φ − (Ac/B)·(Cc/B)| ≤ rA/B + (Ac/B)·ρ`: the per-term
half of `mainSumRS_step`, shared by the single and the paired steps. -/
theorem mainSumTerm_bound (θ : ℝ) (g : ℝ → ℝ) (ε : ℝ) (b tn td k B DI M : ℕ)
    (nθ : Bool) (cθ rθ cL rL cA rA : ℕ) (nφ : Bool) (u Pc rπ : ℕ) (nI : Bool) (cI : ℕ) (nC : Bool)
    (hε : |ε| = 1) (hquad : ∀ r : ℝ, Real.cos (r + (k : ℝ) * (Real.pi / 2)) = ε * g r)
    (hsign : sfrac nC cI B = ε * sfrac nI cI B)
    (htd : td ≠ 0) (hB : B ≠ 0) (hM : M ≠ 0) (hDI' : (2 : ℝ) * DI = B)
    (hθ : Real.IsNear θ nθ cθ B rθ B)
    (hL : Real.IsNear (Real.log (sfrac false b (nat_lit 1))) false cL B rL B)
    (hA : Real.IsNear (Real.sqrt (b : ℝ))⁻¹ false cA B rA B)
    (hpi : Real.IsNear Real.pi false Pc M rπ M)
    (hI : Real.IsNear (g ((u : ℝ) / (B : ℝ))) nI cI B 1 DI)
    (hφ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL))
      (td.mul B) (numPosC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B)))
      (numNegC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true) :
    |(Real.sqrt (b : ℝ))⁻¹ * Real.cos (θ - sfrac false tn td * Real.log (sfrac false b 1))
        - sfrac false cA B * sfrac nC cI B|
      ≤ (rA : ℝ) / B + sfrac false cA B
          * (((rθ : ℝ) + 3) / B + sfrac false tn td * ((rL : ℝ) / B) + (k : ℝ) * rπ / (2 * M)) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hφ' := abs_sub_le_of_natAbsSubLe
    (Nat.pos_of_ne_zero (by simp [Nat.mul_eq, htd, hB]))
    (Nat.pos_of_ne_zero (by simp [Nat.mul_eq, hM, hB])) (Nat.pos_of_ne_zero hB) hφ
  simp only [Nat.mul_eq, Nat.add_eq, numPosC_eq, numNegC_eq] at hφ'
  have eφ : ((((numPos nθ (td * cθ) : ℕ) : ℝ)
      - ((numNeg nθ (td * cθ) + tn * cL : ℕ) : ℝ)) / ((td * B : ℕ) : ℝ))
      = sfrac nθ cθ B - sfrac false tn td * sfrac false cL B := by
    rw [sfrac_eq_parts, sfrac_false_div, sfrac_false_div]
    cases nθ <;> simp [numPos, numNeg] <;> field_simp
    all_goals ring
  set σ : ℝ := if nφ then -1 else 1 with hσdef
  set r : ℝ := (u : ℝ) / B
  set Pr : ℝ := sfrac false Pc M
  have eY : (((numPos nφ (2 * M * u + k * Pc * B) : ℕ) : ℝ)
      - ((numNeg nφ (2 * M * u + k * Pc * B) : ℕ) : ℝ)) / ((2 * M * B : ℕ) : ℝ)
      = σ * (r + (k : ℝ) * (Pr / 2)) := by
    rw [← sfrac_eq_parts, sfrac, show Pr = (Pc : ℝ) / M from sfrac_false_div Pc M, hσdef]
    simp only [r]
    push_cast
    field_simp
  rw [eφ, eY] at hφ'
  have hσ : |σ| = 1 := by rw [hσdef]; split <;> simp
  have hpi' : |Pr - Real.pi| ≤ (rπ : ℝ) / M := by
    have := hpi; rw [Real.IsNear, abs_sub_comm] at this; exact this
  set ψ : ℝ := σ * (r + (k : ℝ) * (Real.pi / 2))
  have hψ : |σ * (r + (k : ℝ) * (Pr / 2)) - ψ| ≤ (k : ℝ) * rπ / (2 * M) := by
    have e : σ * (r + (k : ℝ) * (Pr / 2)) - ψ = σ * ((k : ℝ) * ((Pr - Real.pi) / 2)) := by ring
    rw [e, abs_mul, hσ, one_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_div, abs_two]
    calc (k : ℝ) * (|Pr - Real.pi| / 2) ≤ (k : ℝ) * (((rπ : ℝ) / M) / 2) := by gcongr
      _ = (k : ℝ) * rπ / (2 * M) := by field_simp
  have hcosψ : Real.cos ψ = ε * g r := by
    have : Real.cos ψ = Real.cos (r + (k : ℝ) * (Real.pi / 2)) := by
      simp only [ψ, σ]; split
      · rw [neg_one_mul, Real.cos_neg]
      · rw [one_mul]
    rw [this, hquad]
  simp only [Real.IsNear] at hθ hL hA hI
  rw [Nat.cast_one] at hI
  have hT : 0 ≤ sfrac false tn td := by rw [sfrac_false_div]; positivity
  have hAc : 0 ≤ sfrac false cA B := by rw [sfrac_false_div]; positivity
  set L := Real.log (sfrac false b 1)
  set A := (Real.sqrt (b : ℝ))⁻¹
  set T := sfrac false tn td with hTdef
  have hphase : |θ - T * L - ψ|
      ≤ (rθ : ℝ) / B + T * ((rL : ℝ) / B) + 1 / (B : ℝ) + (k : ℝ) * rπ / (2 * M) := by
    have : θ - T * L - ψ = (θ - sfrac nθ cθ B) - T * (L - sfrac false cL B)
        + (sfrac nθ cθ B - T * sfrac false cL B - σ * (r + (k : ℝ) * (Pr / 2)))
        + (σ * (r + (k : ℝ) * (Pr / 2)) - ψ) := by ring
    rw [this]
    calc _ ≤ |θ - sfrac nθ cθ B| + |T * (L - sfrac false cL B)|
          + |sfrac nθ cθ B - T * sfrac false cL B - σ * (r + (k : ℝ) * (Pr / 2))|
          + |σ * (r + (k : ℝ) * (Pr / 2)) - ψ| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_sub _ _
      _ ≤ _ := by
            rw [abs_mul, abs_of_nonneg hT]
            gcongr
            simpa using hφ'
  -- `|cos φ − Cc| ≤ ρ` with `ρ = (rθ + 3)/B + T·rL/B + k·rπ/(2M)` (the cert's `1/DI = 2/B`)
  set ρ : ℝ := ((rθ : ℝ) + 3) / B + T * ((rL : ℝ) / B) + (k : ℝ) * rπ / (2 * M)
  have hcos : |Real.cos (θ - T * L) - sfrac nC cI B| ≤ ρ := by
    rw [hsign]
    calc _ ≤ |Real.cos (θ - T * L) - Real.cos ψ| + |Real.cos ψ - ε * sfrac nI cI B| :=
          abs_sub_le _ _ _
      _ ≤ ((rθ : ℝ) / B + T * ((rL : ℝ) / B) + 1 / (B : ℝ) + (k : ℝ) * rπ / (2 * M))
          + 1 / (DI : ℝ) := by
            gcongr
            · exact (Real.abs_cos_sub_cos_le _ _).trans hphase
            · rw [hcosψ, ← mul_sub, abs_mul, hε, one_mul]; exact hI
      _ = ρ := by
            have hDIr : (DI : ℝ) = B / 2 := by linarith
            rw [hDIr]; simp only [ρ]; field_simp; ring
  have hterm : |A * Real.cos (θ - T * L) - sfrac false cA B * sfrac nC cI B|
      ≤ (rA : ℝ) / B + sfrac false cA B * ρ := by
    have : A * Real.cos (θ - T * L) - sfrac false cA B * sfrac nC cI B
        = (A - sfrac false cA B) * Real.cos (θ - T * L)
          + sfrac false cA B * (Real.cos (θ - T * L) - sfrac nC cI B) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hAc]
    gcongr
    calc |A - sfrac false cA B| * |Real.cos (θ - T * L)| ≤ |A - sfrac false cA B| * 1 := by
          gcongr; exact Real.abs_cos_le_one _
      _ ≤ _ := by rw [mul_one]; exact hA
  exact hterm

/-- **One Riemann–Siegel main-sum step.** From enclosures of the named partial sum up to `a`, the
phase `θ`, `log b`, `(√b)⁻¹`, the `π` tier and the in-range certificate of `g (u/B)`, enclose the
named partial sum up to `b = a + 1`. Every enclosure shares the centre and radius denominator `B`
(`π` has its own `M`, since its error is multiplied by `k`), which keeps the numeral conditions
short: kernel cost follows their size. The range reduction is folded in: `φc ≈ ±(u/B + k·π/2)`, and
`cos (r + k·π/2) = ε·g r` (`hquad`, from `cos_quad_nat0..3`).

With `φ = θ − t·log b`, `φc = θc/B − (tn/td)·Lc/B` and `ψ = ±(u/B + k·π/2)`: `|φ − ψ| ≤ rθ/B +
t·rL/B + 1/B + k·rπ/(2M)`, and the certificate adds `1/DI = 2/B`; so `|cos φ − Cc/B| ≤ ρ = (rθ +
3)/B + t·rL/B + k·rπ/(2M)`. Then `|A·cos φ − Ac·Cc/B²| ≤ rA/B + (Ac/B)·ρ` since `|cos φ| ≤ 1`, plus
the sum's radius and the rounding `1/B` of the new centre. The numeral conditions: `hpos` and `hDI`
(denominators positive, `2·DI = B`), `hφ` (the phase centre within `1/B` of the reduced point),
`hR` (`|Sc/B + (Ac/B)·(Cc/B) − R/B| ≤ 1/B`) and `hrad` (the radius inequality cleared of
denominators). -/
theorem mainSumRS_step (θ t : ℝ) (g : ℝ → ℝ) (ε : ℝ) (a b tn td k B DI M : ℕ)
    (nθ : Bool) (cθ rθ cL rL cA rA : ℕ) (nS : Bool) (cS rS : ℕ) (nφ : Bool) (u Pc rπ : ℕ)
    (nI : Bool) (cI : ℕ) (nC nR : Bool) (cR rR : ℕ)
    (hε : |ε| = 1) (hquad : ∀ r : ℝ, Real.cos (r + (k : ℝ) * (Real.pi / 2)) = ε * g r)
    (hsign : sfrac nC cI B = ε * sfrac nI cI B)
    (ht : t = sfrac false tn td) (hb : Nat.beq b (a.add 1) = true)
    (hS : Real.IsNear (mainSumRS θ t a) nS cS B rS B)
    (hθ : Real.IsNear θ nθ cθ B rθ B)
    (hL : Real.IsNear (Real.log (sfrac false b (nat_lit 1))) false cL B rL B)
    (hA : Real.IsNear (Real.sqrt (b : ℝ))⁻¹ false cA B rA B)
    (hpi : Real.IsNear Real.pi false Pc M rπ M)
    (hI : Real.IsNear (g ((u : ℝ) / (B : ℝ))) nI cI B 1 DI)
    (hpos : Nat.ble (nat_lit 1) (((td.mul B).mul M).mul DI) = true)
    (hDI : Nat.beq (Nat.mul 2 DI) B = true)
    (hφ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL))
      (td.mul B) (numPosC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B)))
      (numNegC nφ (((Nat.mul 2 M).mul u).add ((k.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true)
    (hR : natAbsSubLe (((numPosC nS cS).mul B).add (cA.mul (numPosC nC cI)))
      (((numNegC nS cS).mul B).add (cA.mul (numNegC nC cI))) (B.mul B)
      (numPosC nR cR) (numNegC nR cR) B (nat_lit 1) B = true)
    (hrad : Nat.ble (((((rS.add rA).add 1).mul B).mul td).mul (Nat.mul 2 M) |>.add
        (cA.mul (((Nat.mul 2 M).mul ((td.mul (rθ.add 3)).add (tn.mul rL))).add
          ((k.mul rπ).mul (td.mul B)))))
      (((rR.mul B).mul td).mul (Nat.mul 2 M)) = true) :
    Real.IsNear (mainSumRS θ t b) nR cR B rR B := by
  rw [main_sum_rs_succ θ t a b hb, main_sum_rs_term_mk θ t tn td b ht]
  simp only [Nat.ble_eq, Nat.mul_eq] at hpos
  have hp : td ≠ 0 ∧ B ≠ 0 ∧ M ≠ 0 ∧ DI ≠ 0 := by
    simpa [Nat.one_le_iff_ne_zero, Nat.mul_ne_zero_iff, and_assoc] using hpos
  obtain ⟨htd, hB, hM, hDI0⟩ := hp
  have hDI' : (2 : ℝ) * DI = B := by
    have := Nat.eq_of_beq_eq_true hDI; simp only [Nat.mul_eq] at this; exact_mod_cast this
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have htdr : (0 : ℝ) < td := by exact_mod_cast Nat.pos_of_ne_zero htd
  have hterm := mainSumTerm_bound θ g ε b tn td k B DI M nθ cθ rθ cL rL cA rA nφ u Pc rπ nI cI nC
    hε hquad hsign htd hB hM hDI' hθ hL hA hpi hI hφ
  simp only [Real.IsNear] at hS ⊢
  set T := sfrac false tn td with hTdef
  set L := Real.log (sfrac false b 1)
  set A := (Real.sqrt (b : ℝ))⁻¹
  set ρ : ℝ := ((rθ : ℝ) + 3) / B + T * ((rL : ℝ) / B) + (k : ℝ) * rπ / (2 * M)
  have hR' := abs_sub_le_of_natAbsSubLe
    (Nat.pos_of_ne_zero (by simp [Nat.mul_eq, hB])) (Nat.pos_of_ne_zero hB)
    (Nat.pos_of_ne_zero hB) hR
  simp only [Nat.mul_eq, Nat.add_eq, numPosC_eq, numNegC_eq] at hR'
  have eR' : ((((numPos nS cS * B + cA * numPos nC cI : ℕ) : ℝ)
      - ((numNeg nS cS * B + cA * numNeg nC cI : ℕ) : ℝ)) / ((B * B : ℕ) : ℝ))
      = sfrac nS cS B + sfrac false cA B * sfrac nC cI B := by
    rw [sfrac_eq_parts nS, sfrac_eq_parts nC, sfrac_false_div]
    push_cast
    field_simp
    ring
  rw [eR', ← sfrac_eq_parts] at hR'
  have hsum : |mainSumRS θ t a + A * Real.cos (θ - T * L) - sfrac nR cR B|
      ≤ (rS : ℝ) / B + ((rA : ℝ) / B + sfrac false cA B * ρ) + 1 / B := by
    have : mainSumRS θ t a + A * Real.cos (θ - T * L) - sfrac nR cR B
        = (mainSumRS θ t a - sfrac nS cS B)
          + (A * Real.cos (θ - T * L) - sfrac false cA B * sfrac nC cI B)
          + (sfrac nS cS B + sfrac false cA B * sfrac nC cI B - sfrac nR cR B) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    gcongr
    · refine (abs_add_le _ _).trans ?_
      gcongr
    · simpa using hR'
  refine hsum.trans ?_
  simp only [Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at hrad
  have hrad' : (((rS + rA + 1) * B * td * (2 * M) + cA * (2 * M * (td * (rθ + 3) + tn * rL)
      + k * rπ * (td * B)) : ℕ) : ℝ) ≤ ((rR * B * td * (2 * M) : ℕ) : ℝ) := by exact_mod_cast hrad
  push_cast at hrad'
  have hden : (0 : ℝ) < (B : ℝ) * B * td * (2 * M) := by positivity
  have key : (rS : ℝ) / B + ((rA : ℝ) / B + sfrac false cA B * ρ) + 1 / B
      = (((rS : ℝ) + rA + 1) * B * td * (2 * M) + cA * (2 * M * (td * ((rθ : ℝ) + 3) + tn * rL)
          + k * rπ * (td * B))) / ((B : ℝ) * B * td * (2 * M)) := by
    simp only [ρ, hTdef, sfrac_false_div]
    field_simp
    ring
  have keyR : (rR : ℝ) / B = (rR : ℝ) * B * td * (2 * M) / ((B : ℝ) * B * td * (2 * M)) := by
    field_simp
  rw [key, keyR]
  exact div_le_div_of_nonneg_right hrad' hden.le

/-- `R/B ≤ X ≤ R/B + 1/B` for `X = (XP − XN)/B²` and `R = ±cR`, as one-sided `Nat.ble`s: the centre
was floored, so the error's sign is known and no two-sided cross-multiplication is needed. -/
def natFloorLe (XP XN : ℕ) (nR : Bool) (cR B : ℕ) : Bool :=
  Nat.ble (((numPosC nR cR).mul B).add XN) (XP.add ((numNegC nR cR).mul B)) &&
    Nat.ble (XP.add ((numNegC nR cR).mul B)) ((((numPosC nR cR).mul B).add XN).add B)

theorem abs_sub_le_of_natFloorLe {XP XN cR B : ℕ} {nR : Bool} (hB : 0 < B)
    (h : natFloorLe XP XN nR cR B = true) :
    |((XP : ℝ) - XN) / ((B * B : ℕ) : ℝ) - sfrac nR cR B| ≤ 1 / (B : ℝ) := by
  simp only [natFloorLe, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq, numPosC_eq,
    numNegC_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have h1' : ((numPos nR cR : ℝ) * B + XN) ≤ XP + (numNeg nR cR : ℝ) * B := by exact_mod_cast h1
  have h2' : ((XP : ℝ) + (numNeg nR cR : ℝ) * B) ≤ (numPos nR cR : ℝ) * B + XN + B := by
    exact_mod_cast h2
  rw [sfrac_eq_parts, abs_le]
  push_cast
  constructor
  · rw [show ((XP : ℝ) - XN) / (B * B) - (numPos nR cR - numNeg nR cR) / B
        = (XP - XN - (numPos nR cR - numNeg nR cR) * B) / (B * B) by field_simp]
    have : (0 : ℝ) ≤ (XP - XN - (numPos nR cR - numNeg nR cR) * B) / (B * B) := by
      apply div_nonneg _ (by positivity); linarith
    linarith [show (0 : ℝ) ≤ 1 / B by positivity]
  · rw [show ((XP : ℝ) - XN) / (B * B) - (numPos nR cR - numNeg nR cR) / B
        = (XP - XN - (numPos nR cR - numNeg nR cR) * B) / (B * B) by field_simp,
      div_le_div_iff₀ (by positivity) hBr]
    nlinarith

/-- **Two main-sum terms in one step.** As `mainSumRS_step`, but adding terms `b₁ = a + 1` and
`b₂ = a + 2` together: one floored centre (`hR`, one-sided) and one radius check (`hrad`) per
pair. The intermediate rounding is redundant, so this removes condition terms rather than moving
them. -/
theorem mainSumRS_step2 (θ t : ℝ) (g₁ g₂ : ℝ → ℝ) (ε₁ ε₂ : ℝ) (a b₁ b₂ tn td k₁ k₂ B DI M : ℕ)
    (nθ : Bool) (cθ rθ cL₁ rL₁ cA₁ rA₁ cL₂ rL₂ cA₂ rA₂ : ℕ) (nS : Bool) (cS rS : ℕ)
    (nφ₁ : Bool) (u₁ : ℕ) (nφ₂ : Bool) (u₂ Pc rπ : ℕ)
    (nI₁ : Bool) (cI₁ : ℕ) (nC₁ nI₂ : Bool) (cI₂ : ℕ) (nC₂ nR : Bool) (cR rR : ℕ)
    (hε₁ : |ε₁| = 1) (hquad₁ : ∀ r : ℝ, Real.cos (r + (k₁ : ℝ) * (Real.pi / 2)) = ε₁ * g₁ r)
    (hsign₁ : sfrac nC₁ cI₁ B = ε₁ * sfrac nI₁ cI₁ B)
    (hε₂ : |ε₂| = 1) (hquad₂ : ∀ r : ℝ, Real.cos (r + (k₂ : ℝ) * (Real.pi / 2)) = ε₂ * g₂ r)
    (hsign₂ : sfrac nC₂ cI₂ B = ε₂ * sfrac nI₂ cI₂ B)
    (ht : t = sfrac false tn td) (hb₁ : Nat.beq b₁ (a.add 1) = true)
    (hb₂ : Nat.beq b₂ (b₁.add 1) = true)
    (hS : Real.IsNear (mainSumRS θ t a) nS cS B rS B)
    (hθ : Real.IsNear θ nθ cθ B rθ B)
    (hL₁ : Real.IsNear (Real.log (sfrac false b₁ (nat_lit 1))) false cL₁ B rL₁ B)
    (hA₁ : Real.IsNear (Real.sqrt (b₁ : ℝ))⁻¹ false cA₁ B rA₁ B)
    (hL₂ : Real.IsNear (Real.log (sfrac false b₂ (nat_lit 1))) false cL₂ B rL₂ B)
    (hA₂ : Real.IsNear (Real.sqrt (b₂ : ℝ))⁻¹ false cA₂ B rA₂ B)
    (hpi : Real.IsNear Real.pi false Pc M rπ M)
    (hI₁ : Real.IsNear (g₁ ((u₁ : ℝ) / (B : ℝ))) nI₁ cI₁ B 1 DI)
    (hI₂ : Real.IsNear (g₂ ((u₂ : ℝ) / (B : ℝ))) nI₂ cI₂ B 1 DI)
    (hpos : Nat.ble (nat_lit 1) (((td.mul B).mul M).mul DI) = true)
    (hDI : Nat.beq (Nat.mul 2 DI) B = true)
    (hφ₁ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL₁))
      (td.mul B) (numPosC nφ₁ (((Nat.mul 2 M).mul u₁).add ((k₁.mul Pc).mul B)))
      (numNegC nφ₁ (((Nat.mul 2 M).mul u₁).add ((k₁.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true)
    (hφ₂ : natAbsSubLe (numPosC nθ (td.mul cθ)) ((numNegC nθ (td.mul cθ)).add (tn.mul cL₂))
      (td.mul B) (numPosC nφ₂ (((Nat.mul 2 M).mul u₂).add ((k₂.mul Pc).mul B)))
      (numNegC nφ₂ (((Nat.mul 2 M).mul u₂).add ((k₂.mul Pc).mul B))) ((Nat.mul 2 M).mul B)
      (nat_lit 1) B = true)
    (hR : natFloorLe ((((numPosC nS cS).mul B).add (cA₁.mul (numPosC nC₁ cI₁))).add
        (cA₂.mul (numPosC nC₂ cI₂)))
      ((((numNegC nS cS).mul B).add (cA₁.mul (numNegC nC₁ cI₁))).add (cA₂.mul (numNegC nC₂ cI₂)))
      nR cR B = true)
    (hrad : Nat.ble (((((((rS.add rA₁).add rA₂).add 1).mul B).mul td).mul (Nat.mul 2 M) |>.add
        (cA₁.mul (((Nat.mul 2 M).mul ((td.mul (rθ.add 3)).add (tn.mul rL₁))).add
          ((k₁.mul rπ).mul (td.mul B))))) |>.add
        (cA₂.mul (((Nat.mul 2 M).mul ((td.mul (rθ.add 3)).add (tn.mul rL₂))).add
          ((k₂.mul rπ).mul (td.mul B)))))
      (((rR.mul B).mul td).mul (Nat.mul 2 M)) = true) :
    Real.IsNear (mainSumRS θ t b₂) nR cR B rR B := by
  rw [main_sum_rs_succ θ t b₁ b₂ hb₂, main_sum_rs_succ θ t a b₁ hb₁,
    main_sum_rs_term_mk θ t tn td b₁ ht, main_sum_rs_term_mk θ t tn td b₂ ht]
  simp only [Nat.ble_eq, Nat.mul_eq] at hpos
  have hp : td ≠ 0 ∧ B ≠ 0 ∧ M ≠ 0 ∧ DI ≠ 0 := by
    simpa [Nat.one_le_iff_ne_zero, Nat.mul_ne_zero_iff, and_assoc] using hpos
  obtain ⟨htd, hB, hM, hDI0⟩ := hp
  have hDI' : (2 : ℝ) * DI = B := by
    have := Nat.eq_of_beq_eq_true hDI; simp only [Nat.mul_eq] at this; exact_mod_cast this
  have hBr : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hMr : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have htdr : (0 : ℝ) < td := by exact_mod_cast Nat.pos_of_ne_zero htd
  have hT₁ := mainSumTerm_bound θ g₁ ε₁ b₁ tn td k₁ B DI M nθ cθ rθ cL₁ rL₁ cA₁ rA₁ nφ₁ u₁ Pc rπ
    nI₁ cI₁ nC₁ hε₁ hquad₁ hsign₁ htd hB hM hDI' hθ hL₁ hA₁ hpi hI₁ hφ₁
  have hT₂ := mainSumTerm_bound θ g₂ ε₂ b₂ tn td k₂ B DI M nθ cθ rθ cL₂ rL₂ cA₂ rA₂ nφ₂ u₂ Pc rπ
    nI₂ cI₂ nC₂ hε₂ hquad₂ hsign₂ htd hB hM hDI' hθ hL₂ hA₂ hpi hI₂ hφ₂
  have hR' := abs_sub_le_of_natFloorLe (Nat.pos_of_ne_zero hB) hR
  simp only [Nat.mul_eq, Nat.add_eq, numPosC_eq, numNegC_eq] at hR'
  have eX : ((((numPos nS cS * B + cA₁ * numPos nC₁ cI₁ + cA₂ * numPos nC₂ cI₂ : ℕ) : ℝ)
      - ((numNeg nS cS * B + cA₁ * numNeg nC₁ cI₁ + cA₂ * numNeg nC₂ cI₂ : ℕ) : ℝ))
      / ((B * B : ℕ) : ℝ))
      = sfrac nS cS B + sfrac false cA₁ B * sfrac nC₁ cI₁ B
        + sfrac false cA₂ B * sfrac nC₂ cI₂ B := by
    rw [sfrac_eq_parts nS, sfrac_eq_parts nC₁, sfrac_eq_parts nC₂, sfrac_false_div,
      sfrac_false_div]
    push_cast
    field_simp
    ring
  rw [eX] at hR'
  simp only [Real.IsNear] at hS ⊢
  set T := sfrac false tn td with hTdef
  set X₁ := (Real.sqrt (b₁ : ℝ))⁻¹ * Real.cos (θ - T * Real.log (sfrac false b₁ 1))
  set X₂ := (Real.sqrt (b₂ : ℝ))⁻¹ * Real.cos (θ - T * Real.log (sfrac false b₂ 1))
  have hsum : |mainSumRS θ t a + X₁ + X₂ - sfrac nR cR B|
      ≤ (rS : ℝ) / B
        + ((rA₁ : ℝ) / B + sfrac false cA₁ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₁ : ℝ) / B) + (k₁ : ℝ) * rπ / (2 * M)))
        + ((rA₂ : ℝ) / B + sfrac false cA₂ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₂ : ℝ) / B) + (k₂ : ℝ) * rπ / (2 * M)))
        + 1 / B := by
    have : mainSumRS θ t a + X₁ + X₂ - sfrac nR cR B
        = (mainSumRS θ t a - sfrac nS cS B)
          + (X₁ - sfrac false cA₁ B * sfrac nC₁ cI₁ B)
          + (X₂ - sfrac false cA₂ B * sfrac nC₂ cI₂ B)
          + (sfrac nS cS B + sfrac false cA₁ B * sfrac nC₁ cI₁ B
              + sfrac false cA₂ B * sfrac nC₂ cI₂ B - sfrac nR cR B) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    gcongr
    · refine (abs_add_le _ _).trans ?_
      gcongr
      refine (abs_add_le _ _).trans ?_
      gcongr
  refine hsum.trans ?_
  simp only [Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at hrad
  have hrad' : (((rS + rA₁ + rA₂ + 1) * B * td * (2 * M)
      + cA₁ * (2 * M * (td * (rθ + 3) + tn * rL₁) + k₁ * rπ * (td * B))
      + cA₂ * (2 * M * (td * (rθ + 3) + tn * rL₂) + k₂ * rπ * (td * B)) : ℕ) : ℝ)
      ≤ ((rR * B * td * (2 * M) : ℕ) : ℝ) := by exact_mod_cast hrad
  push_cast at hrad'
  have hden : (0 : ℝ) < (B : ℝ) * B * td * (2 * M) := by positivity
  have key : (rS : ℝ) / B
        + ((rA₁ : ℝ) / B + sfrac false cA₁ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₁ : ℝ) / B) + (k₁ : ℝ) * rπ / (2 * M)))
        + ((rA₂ : ℝ) / B + sfrac false cA₂ B
            * (((rθ : ℝ) + 3) / B + T * ((rL₂ : ℝ) / B) + (k₂ : ℝ) * rπ / (2 * M)))
        + 1 / B
      = (((rS : ℝ) + rA₁ + rA₂ + 1) * B * td * (2 * M)
          + cA₁ * (2 * M * (td * ((rθ : ℝ) + 3) + tn * rL₁) + k₁ * rπ * (td * B))
          + cA₂ * (2 * M * (td * ((rθ : ℝ) + 3) + tn * rL₂) + k₂ * rπ * (td * B)))
        / ((B : ℝ) * B * td * (2 * M)) := by
    simp only [hTdef, sfrac_false_div]
    field_simp
    ring
  have keyR : (rR : ℝ) / B = (rR : ℝ) * B * td * (2 * M) / ((B : ℝ) * B * td * (2 * M)) := by
    field_simp
  rw [key, keyR]
  exact div_le_div_of_nonneg_right hrad' hden.le

/-! ### The Riemann–Siegel correction factor

Renames for the three non-sum pieces of `hardyZApproximantRS`'s correction term
`(-1)^ν · T^{-1/4} · (Ψ(p) + C₁(p)/√T)` at `T = t/2π`: the sign, the normalised height, and the
quarter-power. `Ψ = correction` and `C₁ = correctionLinear` are *not* covered — they are defined
through `modelIntegral`/`modelMoment` and have no elementary closed form for the enclosure engine
to build (`cos_mul_correction` characterises `Ψ` only implicitly, and degenerates at
`p = 1/4, 3/4`). -/

/-- `(-1)^n = 1` at an even literal exponent, in `sfrac` form. The sign of the Riemann–Siegel
correction is decided at build time from the parity of the cutoff, so no power is ever enclosed. -/
theorem neg_one_pow_even_mk (n : ℕ) (h : Nat.beq (n % 2) (nat_lit 0) = true) :
    (-1 : ℝ) ^ n = sfrac false (nat_lit 1) (nat_lit 1) := by
  rw [(Nat.even_iff.2 (Nat.eq_of_beq_eq_true h)).neg_one_pow]
  norm_num [sfrac]

/-- `(-1)^n = -1` at an odd literal exponent, in `sfrac` form; the companion of
`neg_one_pow_even_mk`. -/
theorem neg_one_pow_odd_mk (n : ℕ) (h : Nat.beq (n % 2) (nat_lit 1) = true) :
    (-1 : ℝ) ^ n = sfrac true (nat_lit 1) (nat_lit 1) := by
  rw [(Nat.odd_iff.2 (Nat.eq_of_beq_eq_true h)).neg_one_pow]
  norm_num [sfrac]

/-- The normalised height `T = t/2π` in the shape the builder assembles: the endpoint's `sfrac`
times the reciprocal of `2·π`, with `2π` in `log_two_pi_eq`'s convention (`mkConstNear 2 1`
against `mkPiNear`). -/
theorem t_div_two_pi_mk (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td) :
    t / (2 * Real.pi)
      = sfrac false tn td * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi)⁻¹ := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  subst ht
  rw [h2, div_eq_mul_inv]

/-- `0 ≤ t/2π` for a nonnegative rational endpoint: the side condition `rpow_neg_quarter_mk`
takes, in the surface form the endpoint carries. -/
theorem sfrac_div_two_pi_nonneg (tn td : ℕ) : 0 ≤ sfrac false tn td / (2 * Real.pi) := by
  rw [sfrac_false_div]
  positivity

/-- `x^{-1/4} = (√(√x))⁻¹`: the quarter-power the Riemann–Siegel correction carries, as two
square-root images and a reciprocal. The engine has no `rpow` builder, and this is the only
shape it can assemble. -/
theorem rpow_neg_quarter_mk (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(1 / 4) : ℝ) = (Real.sqrt (Real.sqrt x))⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx, Real.rpow_neg hx]
  norm_num

/-- **The Riemann–Siegel correction in the shape the builder assembles**: the classical quotient
`Ψ(p) = cos(2π(p² − p − 1/16)) / cos(2πp)`, with the reciprocal pulled to the front and every
rational constant in `sfrac` form. The side condition is discharged once and for all by
`cos_two_pi_fract_sqrt_ne_zero`: at a rational endpoint `p` is irrational, so it never lands on
`1/4` or `3/4` and the denominator never vanishes. -/
theorem correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
            * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  rw [h2] at h
  rw [h2, h16, eq_inv_mul_iff_mul_eq₀ h, Zeta.RiemannSiegel.cos_mul_correction p]
  ring_nf

/-- `cos(2πp) ≠ 0` at a certificate endpoint, in the surface form the correction builder produces:
`t = tn/td` a positive rational, the cutoff already identified with the literal `ν` (by
`floor_sqrt_eq_dec`), constants in `sfrac` form. Discharges `correction_mk`'s side condition; the
mathematics is `cos_two_pi_fract_sqrt_ne_zero`. -/
theorem cos_two_pi_p_ne_zero_mk (t : ℝ) (tn td ν : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true)
    (hν : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν) :
    Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
        * (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))) ≠ 0 := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have hν1 : sfrac false ν (nat_lit 1) = (ν : ℝ) := by norm_num [sfrac]
  have htnR : (0 : ℝ) < tn := pos_real_of_ble htn
  have htdR : (0 : ℝ) < td := pos_real_of_ble htd
  set q : ℚ := (tn : ℚ) / (td : ℚ) with hqdef
  have hq : 0 < q := by
    rw [hqdef]
    exact div_pos (by exact_mod_cast htnR) (by exact_mod_cast htdR)
  have hqt : ((q : ℚ) : ℝ) = t := by
    rw [ht, hqdef, sfrac_false_div]; push_cast; ring
  rw [h2, hν1, ← hν, ← hqt]
  exact Zeta.RiemannSiegel.cos_two_pi_fract_sqrt_ne_zero q hq

/-- **The `32π ≤ t` threshold** the first-order Riemann–Siegel bound needs
(`ZIntervalRS.Certificate.le_fst`), from one cross-multiplied `Nat.ble`: `π < 3.15`
(`Real.pi_lt_d2`) gives `32π < 100.8 = 504/5`. -/
theorem thirtyTwoPi_le_dec {t : ℝ} (tn td : ℕ) (ht : t = sfrac false tn td)
    (htd : Nat.ble 1 td = true)
    (h : Nat.ble (Nat.mul 504 td) (Nat.mul 5 tn) = true) : 32 * Real.pi ≤ t := by
  subst ht
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have h' : (504 : ℝ) * td ≤ 5 * tn := by
    simp only [Nat.mul_eq] at h; exact_mod_cast Nat.le_of_ble_eq_true h
  have hpi : Real.pi * td ≤ 3.15 * td := mul_le_mul_of_nonneg_right Real.pi_lt_d2.le hd.le
  rw [sfrac_false_div, le_div_iff₀ hd]
  linarith

/-- **The Riemann–Siegel cutoff at a rational endpoint**, `⌊√(t/2π)⌋₊ = ν`, from two
cross-multiplied ℕ side conditions. Squaring removes the square root, so the cutoff is decided by
`2πν² ≤ t < 2π(ν+1)²`, and `2π·10²⁰ ∈ (628318530717958647692, 628318530717958647694)` by
`Real.pi_gt_d20`/`pi_lt_d20`. -/
theorem floor_sqrt_eq_dec {t : ℝ} (tn td ν : ℕ) (ht : t = sfrac false tn td)
    (htd : Nat.ble 1 td = true)
    (hlo : Nat.ble (Nat.mul (Nat.mul 628318530717958647694 (Nat.mul ν ν)) td)
      (Nat.mul 100000000000000000000 tn) = true)
    (hhi : Nat.blt (Nat.mul 100000000000000000000 tn)
      (Nat.mul (Nat.mul 628318530717958647692 (Nat.mul (ν + 1) (ν + 1))) td) = true) :
    ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν := by
  subst ht
  have hd : (0 : ℝ) < td := pos_real_of_ble htd
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlo' : (628318530717958647694 : ℝ) * (ν * ν) * td ≤ 100000000000000000000 * tn := by
    simp only [Nat.mul_eq] at hlo; exact_mod_cast Nat.le_of_ble_eq_true hlo
  have hhi' : (100000000000000000000 : ℝ) * tn
      < 628318530717958647692 * ((ν + 1) * (ν + 1)) * td := by
    simp only [Nat.mul_eq, Nat.blt_eq] at hhi; exact_mod_cast hhi
  have hsq : (0 : ℝ) ≤ (ν : ℝ) * ν := by positivity
  have hsq' : (0 : ℝ) ≤ ((ν : ℝ) + 1) * ((ν : ℝ) + 1) := by positivity
  have hpiu : (2 * Real.pi) * ((ν : ℝ) * ν) ≤ 6.28318530717958647694 * ((ν : ℝ) * ν) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_d20]) hsq
  have hpil : (6.28318530717958647692 : ℝ) * (((ν : ℝ) + 1) * ((ν : ℝ) + 1))
      ≤ (2 * Real.pi) * (((ν : ℝ) + 1) * ((ν : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_d20]) hsq'
  rw [sfrac_false_div, Nat.floor_eq_iff (Real.sqrt_nonneg _)]
  refine ⟨?_, ?_⟩
  · rw [Real.le_sqrt (Nat.cast_nonneg ν) (by positivity), le_div_iff₀ h2pi, sq]
    rw [le_div_iff₀ hd] at *
    nlinarith [hlo', hpiu, hd]
  · rw [Real.sqrt_lt' (by positivity), div_lt_iff₀ h2pi, div_lt_iff₀ hd, sq]
    nlinarith [hhi', hpil, hd]

/-- `0 < t/2π` for a positive rational endpoint: the side condition the `rpow` renames of the
error bound take (they invert, so nonnegativity is not enough — cf.
`sfrac_div_two_pi_nonneg`). -/
theorem sfrac_div_two_pi_pos (tn td : ℕ) (htn : Nat.ble 1 tn = true)
    (htd : Nat.ble 1 td = true) : 0 < sfrac false tn td / (2 * Real.pi) := by
  have h1 : (0 : ℝ) < tn := pos_real_of_ble htn
  have h2 : (0 : ℝ) < td := pos_real_of_ble htd
  rw [sfrac_false_div]
  exact div_pos (div_pos h1 h2) (by positivity)

/-- `0 ≤ t/2π` at an endpoint in any surface form. The metaprogram applies this directly, so it
is parameterised by `t` and `ht` rather than stated about `sfrac false tn td`: `tE` is whatever the
row carries (a decimal literal, say), and only `htE` ties it to the `sfrac` form. -/
theorem t_div_two_pi_nonneg (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td) :
    0 ≤ t / (2 * Real.pi) := by
  subst ht; exact sfrac_div_two_pi_nonneg tn td

/-- `0 < t/2π` at an endpoint in any surface form; the strict companion of
`t_div_two_pi_nonneg`, for the reciprocals in the error bound. -/
theorem t_div_two_pi_pos (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true) : 0 < t / (2 * Real.pi) := by
  subst ht; exact sfrac_div_two_pi_pos tn td htn htd

/-- `√(√x) = x^{1/4}`: the bridge between the engine's two square-root images and the real
exponents the Riemann–Siegel error bound carries. -/
theorem sqrt_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

/-- `x^{-3/4} = (√√x · √√x · √√x)⁻¹`, the discarded linear term's factor in
`hardyZErrorBoundRS₀`. -/
theorem rpow_neg_three_quarter_mk (x : ℝ) (hx : 0 < x) :
    x ^ (-(3 / 4) : ℝ)
      = (Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x))⁻¹ := by
  rw [sqrt_sqrt_eq_rpow hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_neg hx.le]
  norm_num

/-- `x^{-5/4} = (√√x · x)⁻¹`, the leading term of `hardyZErrorBoundRS`. -/
theorem rpow_neg_five_quarter_mk (x : ℝ) (hx : 0 < x) :
    x ^ (-(5 / 4) : ℝ) = (Real.sqrt (Real.sqrt x) * x)⁻¹ := by
  rw [sqrt_sqrt_eq_rpow hx.le, ← Real.rpow_add_one hx.ne', ← Real.rpow_neg hx.le]
  norm_num

/-- `x^{-15/4} = ((√√x · x) · (√√x · x) · (√√x · x))⁻¹`, the tail term of
`hardyZErrorBoundRS`. -/
theorem rpow_neg_fifteen_quarter_mk (x : ℝ) (hx : 0 < x) :
    x ^ (-(15 / 4) : ℝ)
      = (Real.sqrt (Real.sqrt x) * x * (Real.sqrt (Real.sqrt x) * x)
          * (Real.sqrt (Real.sqrt x) * x))⁻¹ := by
  rw [sqrt_sqrt_eq_rpow hx.le, ← Real.rpow_add_one hx.ne', ← Real.rpow_add hx,
    ← Real.rpow_add hx, ← Real.rpow_neg hx.le]
  norm_num

/-- **The linear-free Riemann–Siegel approximant at a literal cutoff.** `hardyZApproximantRS₀`
mentions `⌊√(t/2π)⌋₊`, a real-number floor that no amount of unfolding turns into a numeral, so the
builder's literal `ν` is put in through this rename; `hν` comes from `floor_sqrt_eq_dec`. -/
theorem hardyZApproximantRS₀_eq (t : ℝ) (ν : ℕ)
    (hν : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν) :
    hardyZApproximantRS₀ t
      = Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ν
        - (-1) ^ ν * (t / (2 * Real.pi)) ^ (-(1 / 4) : ℝ)
            * Zeta.RiemannSiegel.correction
                (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1)) := by
  have hs : sfrac false ν (nat_lit 1) = (ν : ℝ) := by norm_num [sfrac]
  rw [hs]
  subst hν
  rfl

/-- **The linear-free Riemann–Siegel error bound in the shape the builder assembles**:
`25/4·T^{-5/4} + 1/32·T^{-15/4} + 13/10·T^{-3/4}` with every real exponent turned into products of
`q = √(√T)` and `T`, and every coefficient in `sfrac` form. One rename for the whole bound, as
`correction_mk` is for `Ψ` — the coefficients alone would defeat a `rfl`, since `sfrac false 25 4`
is `1 * (25/4)` and `one_mul` is a theorem, not definitional. -/
theorem hardyZErrorBoundRS₀_mk (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true) :
    hardyZErrorBoundRS₀ t
      = sfrac false (nat_lit 25) (nat_lit 4)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))⁻¹
        + sfrac false (nat_lit 1) (nat_lit 32)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))))⁻¹
        + sfrac false (nat_lit 13) (nat_lit 10)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi)))
              * Real.sqrt (Real.sqrt (t / (2 * Real.pi)))
              * Real.sqrt (Real.sqrt (t / (2 * Real.pi))))⁻¹ := by
  subst ht
  have hT : 0 < sfrac false tn td / (2 * Real.pi) := sfrac_div_two_pi_pos tn td htn htd
  have h25 : sfrac false (nat_lit 25) (nat_lit 4) = (25 / 4 : ℝ) := by norm_num [sfrac]
  have h32 : sfrac false (nat_lit 1) (nat_lit 32) = (1 / 32 : ℝ) := by norm_num [sfrac]
  have h13 : sfrac false (nat_lit 13) (nat_lit 10) = (13 / 10 : ℝ) := by norm_num [sfrac]
  rw [h25, h32, h13, ← rpow_neg_five_quarter_mk _ hT, ← rpow_neg_fifteen_quarter_mk _ hT,
    ← rpow_neg_three_quarter_mk _ hT]

/-- **The first-order Riemann–Siegel approximant at a literal cutoff** — the `hardyZApproximantRS₀`
counterpart for the full approximant, carrying `Ψ(p) + C₁(p)/√T`. `hν` comes from
`floor_sqrt_eq_dec`, and the cutoff is stated as `sfrac false ν 1` to match what the builder's
`p = √T − ν` actually is. -/
theorem hardyZApproximantRS_eq (t : ℝ) (ν : ℕ)
    (hν : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ = ν) :
    hardyZApproximantRS t
      = Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ν
        - (-1) ^ ν * (t / (2 * Real.pi)) ^ (-(1 / 4) : ℝ)
            * (Zeta.RiemannSiegel.correction
                  (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))
                + Zeta.RiemannSiegel.correctionLinear
                    (Real.sqrt (t / (2 * Real.pi)) - sfrac false ν (nat_lit 1))
                  * (Real.sqrt (t / (2 * Real.pi)))⁻¹) := by
  have hs : sfrac false ν (nat_lit 1) = (ν : ℝ) := by norm_num [sfrac]
  rw [hs]
  subst hν
  rfl

/-- **The first-order Riemann–Siegel error bound in the shape the builder assembles**:
`25/4·T^{-5/4} + 1/32·T^{-15/4}`, the two-term companion of `hardyZErrorBoundRS₀_mk` (no
discarded-`C₁` charge, since the full approximant carries it). -/
theorem hardyZErrorBoundRS_mk (t : ℝ) (tn td : ℕ) (ht : t = sfrac false tn td)
    (htn : Nat.ble 1 tn = true) (htd : Nat.ble 1 td = true) :
    hardyZErrorBoundRS t
      = sfrac false (nat_lit 25) (nat_lit 4)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))⁻¹
        + sfrac false (nat_lit 1) (nat_lit 32)
          * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi)))
              * (Real.sqrt (Real.sqrt (t / (2 * Real.pi))) * (t / (2 * Real.pi))))⁻¹ := by
  subst ht
  have hT : 0 < sfrac false tn td / (2 * Real.pi) := sfrac_div_two_pi_pos tn td htn htd
  have h25 : sfrac false (nat_lit 25) (nat_lit 4) = (25 / 4 : ℝ) := by norm_num [sfrac]
  have h32 : sfrac false (nat_lit 1) (nat_lit 32) = (1 / 32 : ℝ) := by norm_num [sfrac]
  rw [h25, h32, ← rpow_neg_five_quarter_mk _ hT, ← rpow_neg_fifteen_quarter_mk _ hT]

/-! ### One error bound per batch

Both error bounds are sums of negative powers of `T = t/2π`, so they decrease in `t`. A batch
encloses the bound once, at its lowest endpoint `s`, and moves it to every endpoint `t ≥ s` of the
batch through one cross-multiplied `Nat.ble`. -/

/-- `hardyZErrorBoundRS` is antitone on `t > 0`. -/
theorem hardyZErrorBoundRS_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    hardyZErrorBoundRS t ≤ hardyZErrorBoundRS s := by
  have hT : 0 < s / (2 * Real.pi) := div_pos hs (by positivity)
  have hle : s / (2 * Real.pi) ≤ t / (2 * Real.pi) := by gcongr
  have h5 := Real.rpow_le_rpow_of_nonpos hT hle (by norm_num : -(5 / 4 : ℝ) ≤ 0)
  have h15 := Real.rpow_le_rpow_of_nonpos hT hle (by norm_num : -(15 / 4 : ℝ) ≤ 0)
  simp only [hardyZErrorBoundRS]
  linarith

/-- `hardyZErrorBoundRS₀` is antitone on `t > 0`. -/
theorem hardyZErrorBoundRS₀_anti {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    hardyZErrorBoundRS₀ t ≤ hardyZErrorBoundRS₀ s := by
  have hT : 0 < s / (2 * Real.pi) := div_pos hs (by positivity)
  have hle : s / (2 * Real.pi) ≤ t / (2 * Real.pi) := by gcongr
  have h3 := Real.rpow_le_rpow_of_nonpos hT hle (by norm_num : -(3 / 4 : ℝ) ≤ 0)
  have h := hardyZErrorBoundRS_anti hs hst
  simp only [hardyZErrorBoundRS₀]
  linarith

/-- `‖x‖ > hardyZErrorBoundRS t` from the same inequality at a lower rational endpoint
`s = sn/sd ≤ t = tn/td`. -/
theorem norm_gt_hardyZErrorBoundRS_of_le (x s t : ℝ) (sn sd tn td : ℕ)
    (hs : s = sfrac false sn sd) (ht : t = sfrac false tn td) (hsn : Nat.ble 1 sn = true)
    (hsd : Nat.ble 1 sd = true) (htd : Nat.ble 1 td = true)
    (hst : Nat.ble (sn.mul td) (tn.mul sd) = true) (h : ‖x‖ > hardyZErrorBoundRS s) :
    ‖x‖ > hardyZErrorBoundRS t := by
  have hs0 : 0 < s := by
    rw [hs, sfrac_false_div]; exact div_pos (pos_real_of_ble hsn) (pos_real_of_ble hsd)
  exact lt_of_le_of_lt (hardyZErrorBoundRS_anti hs0 (dec_le_dec sn sd tn td hs ht hsd htd hst)) h

/-- `norm_gt_hardyZErrorBoundRS_of_le` for the linear-free bound. -/
theorem norm_gt_hardyZErrorBoundRS₀_of_le (x s t : ℝ) (sn sd tn td : ℕ)
    (hs : s = sfrac false sn sd) (ht : t = sfrac false tn td) (hsn : Nat.ble 1 sn = true)
    (hsd : Nat.ble 1 sd = true) (htd : Nat.ble 1 td = true)
    (hst : Nat.ble (sn.mul td) (tn.mul sd) = true) (h : ‖x‖ > hardyZErrorBoundRS₀ s) :
    ‖x‖ > hardyZErrorBoundRS₀ t := by
  have hs0 : 0 < s := by
    rw [hs, sfrac_false_div]; exact div_pos (pos_real_of_ble hsn) (pos_real_of_ble hsd)
  exact lt_of_le_of_lt (hardyZErrorBoundRS₀_anti hs0 (dec_le_dec sn sd tn td hs ht hsd htd hst)) h

/-! ### The `Ψ`-derivative chain in builder shape

`correction_mk`'s companions for `Ψ'`, `Ψ''`, `Ψ'''` and `C₁`, each the divided form of the
corresponding product identity in `Correction.lean`. Every one has the same shape: the reciprocal
of `C = cos 2πp` first, then a combination of the trig leaves and the *previously built* derivative
enclosures. The builder assembles them in this order, renaming after each. -/

/-- `Ψ' = C⁻¹·(R₁ − C'·Ψ)`. -/
theorem deriv_correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    iteratedDeriv 1 Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * (-(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                    * (sfrac false (nat_lit 2) (nat_lit 1) * p
                          - sfrac false (nat_lit 1) (nat_lit 1))
                * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))))
            - -(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * Zeta.RiemannSiegel.correction p) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  have h1 : sfrac false (nat_lit 1) (nat_lit 1) = (1 : ℝ) := by norm_num [sfrac]
  have hsq : p * p = p ^ 2 := by ring
  rw [h2] at h
  rw [h2, h16, h1, hsq, eq_inv_mul_iff_mul_eq₀ h]
  linear_combination Zeta.RiemannSiegel.cos_mul_iteratedDeriv_one p

/-- `Ψ'' = C⁻¹·(R₂ − 2C'·Ψ' − C''·Ψ)`. -/
theorem iteratedDeriv_two_correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    iteratedDeriv 2 Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * (-((sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
                * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
                * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16))))
            - sfrac false (nat_lit 4) (nat_lit 1) * Real.pi
                * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16)))
            - sfrac false (nat_lit 2) (nat_lit 1)
                * -(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * iteratedDeriv 1 Zeta.RiemannSiegel.correction p
            - -(sfrac false (nat_lit 4) (nat_lit 1) * (Real.pi * Real.pi)
                  * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * Zeta.RiemannSiegel.correction p) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h4 : sfrac false (nat_lit 4) (nat_lit 1) = (4 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  have h1 : sfrac false (nat_lit 1) (nat_lit 1) = (1 : ℝ) := by norm_num [sfrac]
  have hsq : p * p = p ^ 2 := by ring
  simp only [h2] at h
  simp only [h2, h4, h16, h1, hsq]
  rw [eq_inv_mul_iff_mul_eq₀ h]
  linear_combination Zeta.RiemannSiegel.cos_mul_iteratedDeriv_two p

/-- `Ψ''' = C⁻¹·(R₃ − 3C'·Ψ'' − 3C''·Ψ' − C'''·Ψ)`, with
`R₃ = sinφ·(φ')³ − 3·cosφ·φ'·φ''`, `φ'' = 4π`. -/
theorem iteratedDeriv_three_correction_mk (p : ℝ)
    (h : Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p) ≠ 0) :
    iteratedDeriv 3 Zeta.RiemannSiegel.correction p
      = (Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))⁻¹
        * ((sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
              * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
              * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
              * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16)))
            - sfrac false (nat_lit 3) (nat_lit 1)
                * (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * (sfrac false (nat_lit 2) (nat_lit 1) * p - sfrac false (nat_lit 1) (nat_lit 1)))
                * (sfrac false (nat_lit 4) (nat_lit 1) * Real.pi)
                    * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                      * (p * p - p - sfrac false (nat_lit 1) (nat_lit 16)))
            - sfrac false (nat_lit 3) (nat_lit 1)
                * -(sfrac false (nat_lit 2) (nat_lit 1) * Real.pi
                  * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * iteratedDeriv 2 Zeta.RiemannSiegel.correction p
            - sfrac false (nat_lit 3) (nat_lit 1)
                * -(sfrac false (nat_lit 4) (nat_lit 1) * (Real.pi * Real.pi)
                  * Real.cos (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p))
                * iteratedDeriv 1 Zeta.RiemannSiegel.correction p
            - sfrac false (nat_lit 8) (nat_lit 1) * (Real.pi * Real.pi * Real.pi)
                * Real.sin (sfrac false (nat_lit 2) (nat_lit 1) * Real.pi * p)
                * Zeta.RiemannSiegel.correction p) := by
  have h2 : sfrac false (nat_lit 2) (nat_lit 1) = (2 : ℝ) := by norm_num [sfrac]
  have h3 : sfrac false (nat_lit 3) (nat_lit 1) = (3 : ℝ) := by norm_num [sfrac]
  have h4 : sfrac false (nat_lit 4) (nat_lit 1) = (4 : ℝ) := by norm_num [sfrac]
  have h8 : sfrac false (nat_lit 8) (nat_lit 1) = (8 : ℝ) := by norm_num [sfrac]
  have h16 : sfrac false (nat_lit 1) (nat_lit 16) = (1 / 16 : ℝ) := by norm_num [sfrac]
  have h1 : sfrac false (nat_lit 1) (nat_lit 1) = (1 : ℝ) := by norm_num [sfrac]
  have hsq : p * p = p ^ 2 := by ring
  simp only [h2] at h
  simp only [h2, h3, h4, h8, h16, h1, hsq]
  rw [eq_inv_mul_iff_mul_eq₀ h]
  linear_combination Zeta.RiemannSiegel.cos_mul_iteratedDeriv_three p

/-- `C₁ = −Ψ'''·(96π²)⁻¹`, the reciprocal on the right as the builder assembles it. -/
theorem correctionLinear_mk (p : ℝ) :
    Zeta.RiemannSiegel.correctionLinear p
      = -(iteratedDeriv 3 Zeta.RiemannSiegel.correction p
          * (sfrac false (nat_lit 96) (nat_lit 1) * (Real.pi * Real.pi))⁻¹) := by
  have h96 : sfrac false (nat_lit 96) (nat_lit 1) = (96 : ℝ) := by norm_num [sfrac]
  rw [h96, Zeta.RiemannSiegel.correctionLinear_eq, div_eq_mul_inv]
  ring

/-- Reciprocal through a negation: `x⁻¹ = -((-x)⁻¹)`. `mkInvImageNear` inverts only enclosures
with a positive centre, so a negative one is inverted after negating and negated back — the
Riemann–Siegel `cos(2πp)` denominator is negative for every `p ∈ (1/4, 3/4)`, i.e. about half the
certificate endpoints. -/
theorem inv_eq_neg_inv_neg (x : ℝ) : x⁻¹ = -(-x)⁻¹ := by
  rw [inv_neg, neg_neg]

/-- Instance-free sign combination for the certificate: negative times positive. -/
theorem mul_neg_of_neg_pos_r (x y : ℝ) (hx : x < 0) (hy : 0 < y) : x * y < 0 :=
  mul_neg_of_neg_of_pos hx hy

/-- Instance-free sign combination for the certificate: positive times negative. -/
theorem mul_neg_of_pos_neg_r (x y : ℝ) (hx : 0 < x) (hy : y < 0) : x * y < 0 :=
  mul_neg_of_pos_of_neg hx hy

end BSN

