/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Zeta.Analysis.SpecialFunctions.Arctan
public import Zeta.RiemannSiegel.Power

/-!
# The Gaussian majorant for the Riemann–Siegel phase

Along the slanted contour `Zeta.RiemannSiegel.line a` the modulus of the Riemann–Siegel integrand
`x^{-1/2-it} e^{iπx²}` is `‖x‖^{-1/2} e^{φ(w)}`, where
`φ(w) = t · slantArg (L(a)(w)) - 2πw(a + w)` (`riemann_siegel.tex`, `sec:rs_bound`). This file
bounds `φ` by a Gaussian, `φ(w) ≤ -πw² + B|w|`, which makes the shifted contour integral small: the
constant `B = 2π|T - a²|/a` measures how far the crossing point `a` sits from the saddle `√T`, and
vanishes when the contour crosses exactly at the saddle.

Everything reduces to elementary inequalities for `arctan`, stated here for the normalised argument
`g(r) = arctan(1 + 2r) - π/4` of the contour point `L(a)(ra)`, which is independent of `a` — whence
the name `Zeta.RiemannSiegel.lineArg`.

That majorant discards a factor `4` in the Gaussian exponent, which is irrelevant when the region
of interest starts at `|w| ≍ T^{1/12}` and fatal when it starts at `|w| ≍ √T/(2√2)`, so the sharp
forms are recorded here as well (`riemann_siegel.tex`, `lem:rs_arctan_sharp` onwards). The gain
comes from never estimating `g` itself but only the *defect* `ψ(r) = r - g(r)`, in terms of which
`λ g - r - r² = ε g - r² - ψ` identically, with `ε = λ - 1`. The sharp phase bound splits at
`w = -a/2`, and is sharp to leading order on the half carrying the saddle: at `ε = 0` and `|w| ≪ a`
it reads `φ(w) ≤ -4πw² + O(w³/a)`, against the truth `φ(w) = -4πw² + O(w³/a)`. The linear term
`B|w|` is the same in both, and cannot be improved: it is the genuine displacement of the crossing
point from the saddle.

## Main results

* `Zeta.RiemannSiegel.lineArg_eq_arctan`: the Möbius form `g(r) = arctan(r/(1 + r))`;
* `Zeta.RiemannSiegel.strictMono_lineArg`: `g` is strictly increasing, with `g(0) = 0`;
* `Zeta.RiemannSiegel.lineArg_le`, `Zeta.RiemannSiegel.lineArg_le_self`: the quadratic majorant
  `g(r) ≤ r + r²/2`, and `g(r) ≤ r` for `r ≥ 0`;
* `Zeta.RiemannSiegel.lineArg_le_sub_div`: the sharp majorant `ψ(r) ≥ r²/(1 + |r|)`, `r ≥ -½`;
* `Zeta.RiemannSiegel.mul_lineArg_sub_le`: the perturbed majorant
  `λ g(r) - r - r² ≤ -r²/2 + |λ - 1| |r|` for `|λ - 1| ≤ 1`;
* `Zeta.RiemannSiegel.mul_lineArg_sub_le'`,
  `Zeta.RiemannSiegel.mul_lineArg_sub_le_of_le_neg_half`: the sharp perturbed majorants on the two
  ranges `r ≥ -½` and `r ≤ -½`;
* `Zeta.RiemannSiegel.phase`, `Zeta.RiemannSiegel.norm_slantCpow_mul_exp_eq_phase`: the exponent
  `φ` and the factorisation of the integrand's modulus through it;
* `Zeta.RiemannSiegel.phase_le`: the Gaussian majorant `φ(w) ≤ -πw² + B|w|`;
* `Zeta.RiemannSiegel.phase_le'`, `Zeta.RiemannSiegel.phase_le_of_le_neg_half`: the sharp Gaussian
  majorants `φ(w) ≤ -2πw² - (1 - |ε|) 2πaw²/(a + |w|) + B|w|` and `φ(w) ≤ -πw²`.
-/
@[expose] public section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/-- The **normalised argument along the slanted contour**, `g(r) = arctan(1 + 2r) - π/4`: the value
of `Zeta.RiemannSiegel.slantArg` at the contour point `L(a)(ra)`, which depends only on `r`. -/
noncomputable def lineArg (r : ℝ) : ℝ := Real.arctan (1 + 2 * r) - π / 4

@[simp]
theorem lineArg_zero : lineArg 0 = 0 := by simp [lineArg, Real.arctan_one]

private theorem lineArg_neg_half : lineArg (-(1 / 2)) = -(π / 4) := by norm_num [lineArg]

/-- **The normalised argument is strictly increasing.** -/
theorem strictMono_lineArg : StrictMono lineArg := fun _ _ h ↦ by
  simpa [lineArg] using Real.arctan_lt_arctan_iff.2 (by linarith)

theorem lineArg_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ lineArg r :=
  lineArg_zero ▸ strictMono_lineArg.monotone hr

theorem lineArg_nonpos {r : ℝ} (hr : r ≤ 0) : lineArg r ≤ 0 :=
  lineArg_zero ▸ strictMono_lineArg.monotone hr

/-- The derivative of the normalised argument. -/
theorem hasDerivAt_lineArg (r : ℝ) : HasDerivAt lineArg (2 / (1 + (1 + 2 * r) ^ 2)) r := by
  have h : HasDerivAt (fun y : ℝ ↦ 1 + 2 * y) 2 r := by
    simpa using ((hasDerivAt_id r).const_mul (2 : ℝ)).const_add (1 : ℝ)
  have h' := h.arctan.sub_const (π / 4)
  rw [show 1 / (1 + (1 + 2 * r) ^ 2) * 2 = 2 / (1 + (1 + 2 * r) ^ 2) by ring] at h'
  exact h'

/-- **The normalised argument as a single arctangent**, `g(r) = arctan(r/(1 + r))` on `(-1, ∞)`. -/
theorem lineArg_eq_arctan {r : ℝ} (hr : -1 < r) : lineArg r = Real.arctan (r / (1 + r)) := by
  have h := Real.arctan_add (x := 1 + 2 * r) (y := -1) (by linarith)
  rw [Real.arctan_neg, Real.arctan_one, show (1 + 2 * r + -1) / (1 - (1 + 2 * r) * -1)
      = r / (1 + r) by
    rw [show (1 : ℝ) - (1 + 2 * r) * -1 = 2 * (1 + r) by ring,
      show (1 : ℝ) + 2 * r + -1 = 2 * r by ring, mul_div_mul_left _ _ two_ne_zero]] at h
  rw [lineArg]
  linarith

/-- **The sharp majorant for the normalised argument on `[0, ∞)`**, `g(r) ≤ r/(1 + r)`: the
`r ≥ 0` half of `Zeta.RiemannSiegel.lineArg_le_sub_div`. -/
private theorem lineArg_le_div {r : ℝ} (hr : 0 ≤ r) : lineArg r ≤ r / (1 + r) := by
  rw [lineArg_eq_arctan (by linarith)]
  exact Real.arctan_le_self (by positivity)

/-- **The normalised argument is dominated by the identity on `[0, ∞)`.** -/
theorem lineArg_le_self {r : ℝ} (hr : 0 ≤ r) : lineArg r ≤ r :=
  (lineArg_le_div hr).trans <| by rw [div_le_iff₀ (by linarith)]; nlinarith

/-- **The sharp majorant for the normalised argument on `[-½, 0]`**: the `r ≤ 0` half of
`Zeta.RiemannSiegel.lineArg_le_sub_div`. -/
private theorem lineArg_le_div_one_sub {r : ℝ} (hr : -(1 / 2) ≤ r) (hr0 : r ≤ 0) :
    lineArg r ≤ (r - 2 * r ^ 2) / (1 - r) := by
  have hne : (1 : ℝ) - r ≠ 0 := ne_of_gt (by linarith)
  have hd : ∀ x : ℝ, x < 1 → HasDerivAt (fun y : ℝ ↦ 2 * y + 1 - 1 / (1 - y) - lineArg y)
      (2 - (0 * (1 - x) - 1 * (0 - 1)) / (1 - x) ^ 2 - 2 / (1 + (1 + 2 * x) ^ 2)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ ↦ 2 * y + 1) 2 x := by
      simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).add_const (1 : ℝ)
    exact (h1.sub ((hasDerivAt_const x (1 : ℝ)).div
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
      (sub_ne_zero_of_ne hx.ne'))).sub (hasDerivAt_lineArg x)
  have hanti : AntitoneOn (fun y : ℝ ↦ 2 * y + 1 - 1 / (1 - y) - lineArg y)
      (Set.Icc (-(1 / 2) : ℝ) 0) := by
    have hmem : ∀ x ∈ interior (Set.Icc (-(1 / 2) : ℝ) 0), -(1 / 2) < x ∧ x < 0 := fun x hx ↦ by
      rwa [interior_Icc, Set.mem_Ioo] at hx
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun x ↦ 2 - (0 * (1 - x) - 1 * (0 - 1)) / (1 - x) ^ 2 - 2 / (1 + (1 + 2 * x) ^ 2))
      (fun x hx ↦ (hd x (by linarith [(Set.mem_Icc.1 hx).2])).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hd x (by linarith [(hmem x hx).2])).hasDerivWithinAt) fun x hx ↦ ?_
    obtain ⟨hx1, hx2⟩ := hmem x hx
    have hden : (0 : ℝ) < 1 + (1 + 2 * x) ^ 2 := by positivity
    have hden' : (0 : ℝ) < (1 - x) ^ 2 := pow_pos (by linarith) 2
    rw [show (0 * (1 - x) - 1 * (0 - 1)) / (1 - x) ^ 2 = 1 / (1 - x) ^ 2 by ring]
    -- `1 + (1 + 2x)² + 2(1 - x)² - 2(1 - x)²(1 + (1 + 2x)²) = 2x²(5 + 4x - 4x²) ≥ 0` on `[-½, 0]`
    have hkey : (2 : ℝ) ≤ 1 / (1 - x) ^ 2 + 2 / (1 + (1 + 2 * x) ^ 2) := by
      rw [div_add_div _ _ hden'.ne' hden.ne', le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg x) (by nlinarith : (0 : ℝ) ≤ 5 + 4 * x - 4 * x ^ 2)]
    linarith
  have h := hanti (Set.mem_Icc.2 ⟨hr, hr0⟩) (Set.mem_Icc.2 ⟨by norm_num, le_rfl⟩) hr0
  norm_num [lineArg_zero] at h
  rw [show (r - 2 * r ^ 2) / (1 - r) = 2 * r + 1 - (1 - r)⁻¹ by field_simp; ring]
  linarith

/-- **The quadratic majorant for `arctan`**, `arctan(1 + 2r) ≤ π/4 + r + r²/2`. -/
theorem lineArg_le (r : ℝ) : lineArg r ≤ r + r ^ 2 / 2 := by
  rcases le_total 0 r with hr | hr
  · nlinarith [lineArg_le_self hr, sq_nonneg r]
  rcases le_total (-(1 / 2) : ℝ) r with hr' | hr'
  · refine (lineArg_le_div_one_sub hr' hr).trans ?_
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - r)]
    nlinarith [mul_nonneg (sq_nonneg r) (by linarith : (0 : ℝ) ≤ 3 - r)]
  · -- `g(r) ≤ g(-½) = -π/4 < -½ ≤ r + r²/2`
    have h : lineArg r ≤ -(π / 4) := lineArg_neg_half ▸ strictMono_lineArg.monotone hr'
    linarith [Real.pi_gt_three, sq_nonneg (r + 1)]

/-- **The sharp majorant for the normalised argument** (`riemann_siegel.tex`,
`lem:rs_arctan_sharp`): the defect `ψ(r) = r - g(r)` is at least `r²/(1 + |r|)` for `r ≥ -½`. The
threshold `-½` is not sharp; the bound holds down to `r = -1.082…`. -/
theorem lineArg_le_sub_div {r : ℝ} (hr : -(1 / 2) ≤ r) : lineArg r ≤ r - r ^ 2 / (1 + |r|) := by
  rcases le_total 0 r with h | h
  · have hne : (1 : ℝ) + r ≠ 0 := by positivity
    have heq : r - r ^ 2 / (1 + r) = r / (1 + r) := by field_simp; ring
    rw [abs_of_nonneg h, heq]
    exact lineArg_le_div h
  · have hne : (1 : ℝ) - r ≠ 0 := (show (0 : ℝ) < 1 - r by linarith).ne'
    have heq : r - r ^ 2 / (1 + -r) = (r - 2 * r ^ 2) / (1 - r) := by
      rw [show (1 : ℝ) + -r = 1 - r by ring]
      field_simp
      ring
    rw [abs_of_nonpos h, heq]
    exact lineArg_le_div_one_sub hr h

/-- **The cost of perturbing the normalised argument**, `c g(r) ≤ |c| (|r| + ψ(r))` in terms of
the defect `ψ(r) = r - g(r)`. -/
theorem mul_lineArg_le (c r : ℝ) : c * lineArg r ≤ |c| * (|r| + (r - lineArg r)) := by
  rcases le_total 0 r with h | h
  · rw [abs_of_nonneg h]
    nlinarith [lineArg_nonneg h, lineArg_le_self h, le_abs_self c, abs_nonneg c]
  · rw [abs_of_nonpos h]
    nlinarith [lineArg_nonpos h, neg_abs_le c, abs_nonneg c]

/-- **The perturbed majorant for the normalised argument.** -/
theorem mul_lineArg_sub_le {lam r : ℝ} (hone : |lam - 1| ≤ 1) :
    lam * lineArg r - r - r ^ 2 ≤ -(r ^ 2 / 2) + |lam - 1| * |r| := by
  -- The two terms must never be separated: `|g r| ≤ |r|` is FALSE (`g'` attains `2` at `r = -1/2`),
  -- and the true global bound `|g| ≤ 2|r|` would double `B` in `phase_le`, inflating the final
  -- estimate by a factor of about `10⁵`. For `r < 0` the loss is absorbed by the slack in
  -- `lineArg_le` instead.
  linarith [mul_lineArg_le (lam - 1) r, mul_nonneg (abs_nonneg (lam - 1)) (sq_nonneg r),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - |lam - 1|)
      (by linarith [lineArg_le r] : (0 : ℝ) ≤ r ^ 2 / 2 + (r - lineArg r))]

/-- **The sharp perturbed majorant for the normalised argument** (`riemann_siegel.tex`,
`lem:rs_arctan_perturbed_sharp`), on the range `r ≥ -½`. -/
theorem mul_lineArg_sub_le' {lam r : ℝ} (hone : |lam - 1| ≤ 1) (hr : -(1 / 2) ≤ r) :
    lam * lineArg r - r - r ^ 2
      ≤ -r ^ 2 - (1 - |lam - 1|) * (r ^ 2 / (1 + |r|)) + |lam - 1| * |r| := by
  linarith [mul_lineArg_le (lam - 1) r,
    mul_le_mul_of_nonneg_left
      (by linarith [lineArg_le_sub_div hr] : r ^ 2 / (1 + |r|) ≤ r - lineArg r)
      (by linarith : (0 : ℝ) ≤ 1 - |lam - 1|)]

/-- **The sharp perturbed majorant for the normalised argument** (`riemann_siegel.tex`,
`lem:rs_arctan_perturbed_sharp`), on the range `r ≤ -½`. -/
theorem mul_lineArg_sub_le_of_le_neg_half {lam r : ℝ} (hlam : 2 / π ≤ lam) (hr : r ≤ -(1 / 2)) :
    lam * lineArg r - r - r ^ 2 ≤ -(r ^ 2 / 2) := by
  have hg : lineArg r ≤ -(π / 4) := lineArg_neg_half ▸ strictMono_lineArg.monotone hr
  have hg0 : lineArg r ≤ 0 := by linarith [Real.pi_pos]
  -- multiplying `λ ≥ 2/π` by the negative number `g(r)`, then `g(r) ≤ -π/4`
  have h2 : 2 / π * lineArg r ≤ -(1 / 2) := by
    have h := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 2 / π)
    rwa [show 2 / π * -(π / 4) = -(1 / 2) by field_simp; norm_num] at h
  linarith [mul_le_mul_of_nonpos_right hlam hg0, sq_nonneg (r + 1)]

theorem slantArg_line_eq_lineArg {a : ℝ} (ha : 0 < a) (w : ℝ) :
    slantArg (line a w) = lineArg (w / a) := by
  rw [slantArg_line ha, lineArg, show (a + 2 * w) / a = 1 + 2 * (w / a) by field_simp]

/-- The **Riemann–Siegel phase**: the exponent controlling the modulus of the integrand
`x^{-1/2-it} e^{iπx²}` along the slanted contour `L(a)`. -/
noncomputable def phase (t a w : ℝ) : ℝ := t * slantArg (line a w) - 2 * π * w * (a + w)

/-- **The Riemann–Siegel phase exponentiates to the modulus of the integrand.** -/
theorem norm_slantCpow_mul_exp_eq_phase {a : ℝ} (ha : a ≠ 0) (t w : ℝ) :
    ‖slantCpow (line a w) (-(1 / 2 + (t : ℂ) * I)) * exp (π * I * line a w ^ 2)‖
      = ‖line a w‖ ^ (-(1 / 2) : ℝ) * Real.exp (phase t a w) := by
  rw [norm_mul, norm_slantCpow (line_ne_zero ha w), Complex.norm_exp_pi_mul_I_mul_sq,
    line_re, line_im, phase,
    show (-(1 / 2 + (t : ℂ) * I)).re = -(1 / 2) by simp,
    show (-(1 / 2 + (t : ℂ) * I)).im = -t by simp,
    show Real.exp (slantArg (line a w) * -t) = (Real.exp (t * slantArg (line a w)))⁻¹ by
      rw [← Real.exp_neg]; congr 1; ring,
    div_eq_mul_inv, inv_inv, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Rescaling by `2πa²` turns a majorant for `λ g(r) - r - r²` at `λ = T/a²`, `r = w/a` into one
for the phase. -/
private theorem phase_le_of_le {t a : ℝ} (ha : 0 < a) {w R : ℝ}
    (h : t / (2 * π) / a ^ 2 * lineArg (w / a) - w / a - (w / a) ^ 2 ≤ R) :
    phase t a w ≤ 2 * π * a ^ 2 * R := by
  have ha' : a ≠ 0 := ha.ne'
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * π * a ^ 2)
  rw [show 2 * π * a ^ 2 * (t / (2 * π) / a ^ 2 * lineArg (w / a) - w / a - (w / a) ^ 2)
      = t * lineArg (w / a) - 2 * π * w * (a + w) by field_simp; ring] at h2
  rwa [phase, slantArg_line_eq_lineArg ha]

/-- The perturbation `λ = T/a²` of the ideal value `1` is within range of the perturbed
majorants. -/
private theorem abs_div_sq_sub_one_le {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a)
    (hT : t / (2 * π) ≤ 2 * a ^ 2) : |t / (2 * π) / a ^ 2 - 1| ≤ 1 := by
  have ha₂ : (0 : ℝ) < a ^ 2 := by positivity
  have h0 : 0 ≤ t / (2 * π) / a ^ 2 := by positivity
  rw [abs_le]
  refine ⟨by linarith, ?_⟩
  rw [sub_le_iff_le_add, div_le_iff₀ ha₂]
  linarith

/-- The perturbation `λ = T/a²` measured against the saddle. -/
private theorem abs_div_sq_sub_one_eq {t a : ℝ} (ha : 0 < a) :
    |t / (2 * π) / a ^ 2 - 1| = |t / (2 * π) - a ^ 2| / a ^ 2 := by
  have ha' : a ≠ 0 := ha.ne'
  have ha₂ : (0 : ℝ) < a ^ 2 := by positivity
  rw [show t / (2 * π) / a ^ 2 - 1 = (t / (2 * π) - a ^ 2) / a ^ 2 by field_simp,
    abs_div, abs_of_pos ha₂]

/-- **The Gaussian majorant for the Riemann–Siegel phase**, with constant `B = 2π|T - a²|/a` for
`T = t/2π`: the distance from the crossing point `a` to the saddle `√T` of the integrand. -/
theorem phase_le {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (hT : t / (2 * π) ≤ 2 * a ^ 2) (w : ℝ) :
    phase t a w ≤ -(π * w ^ 2) + 2 * π * |t / (2 * π) - a ^ 2| / a * |w| := by
  have ha' : a ≠ 0 := ha.ne'
  refine (phase_le_of_le ha
    (mul_lineArg_sub_le (r := w / a) (abs_div_sq_sub_one_le ht ha hT))).trans_eq ?_
  rw [abs_div_sq_sub_one_eq ha, abs_div, abs_of_pos ha]
  field_simp

/-- **The sharp Gaussian majorant for the Riemann–Siegel phase** (`riemann_siegel.tex`,
`lem:rs_phase_sharp`), on the half `w ≥ -a/2` of the contour carrying the saddle. -/
theorem phase_le' {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (hT : t / (2 * π) ≤ 2 * a ^ 2)
    {w : ℝ} (hw : -(a / 2) ≤ w) :
    phase t a w
      ≤ -(2 * π * w ^ 2)
        - (1 - |t / (2 * π) - a ^ 2| / a ^ 2) * (2 * π * a * w ^ 2 / (a + |w|))
        + 2 * π * |t / (2 * π) - a ^ 2| / a * |w| := by
  have ha' : a ≠ 0 := ha.ne'
  have hr : -(1 / 2 : ℝ) ≤ w / a := by rw [le_div_iff₀ ha]; linarith
  refine (phase_le_of_le ha
    (mul_lineArg_sub_le' (r := w / a) (abs_div_sq_sub_one_le ht ha hT) hr)).trans_eq ?_
  rw [abs_div_sq_sub_one_eq ha, abs_div, abs_of_pos ha,
    show (1 : ℝ) + |w| / a = (a + |w|) / a by field_simp]
  field_simp

/-- **The sharp Gaussian majorant for the Riemann–Siegel phase** (`riemann_siegel.tex`,
`lem:rs_phase_sharp`) on the half `w ≤ -a/2` of the contour away from the saddle, where the
crossing point is passed and no linear term survives. -/
theorem phase_le_of_le_neg_half {t a : ℝ} (ha : 0 < a) (hT : 2 / π * a ^ 2 ≤ t / (2 * π))
    {w : ℝ} (hw : w ≤ -(a / 2)) :
    phase t a w ≤ -(π * w ^ 2) := by
  have ha' : a ≠ 0 := ha.ne'
  have hlam : 2 / π ≤ t / (2 * π) / a ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hT
  have hr : w / a ≤ -(1 / 2 : ℝ) := by rw [div_le_iff₀ ha]; linarith
  refine (phase_le_of_le ha
    (mul_lineArg_sub_le_of_le_neg_half (r := w / a) hlam hr)).trans_eq ?_
  field_simp

end Zeta.RiemannSiegel
