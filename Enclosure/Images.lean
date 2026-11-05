module

public import Enclosure.Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Sqrt

/-!
# Real interval enclosures: images under functions

Enclosure of `f x` from an enclosure of `x`: the Lipschitz image (`sin`, `cos`), the monotone
endpoint images (`sqrt`, `inv`), the two-sided sandwich `of_interval`, and the midpoint helper
`of_endpoints`.
-/
@[expose] public section


namespace Enclosure

/-! ### Function of an enclosure (Lipschitz image)

Enclose `x` about a rational centre `c`, certify `f` at `c`, and widen by the Lipschitz factor. -/

/-- Image of an enclosure under a 1-Lipschitz `f`: from `x` near `c` (radius `ρn/ρd`) and a
certificate of `f c` (centre `q`, radius `rsn/rsd`), `f x` is near `q` with radius `ρ + r`. -/
theorem Real.IsNear.lipschitz_image {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y|)
    {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (f c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (f x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) := by
  subst hc
  simp only [Nat.mul_eq, Nat.add_eq]
  have hρdR : (0:ℝ) < ρd := pos_real_of_ble hρd
  have hrsdR : (0:ℝ) < rsd := pos_real_of_ble hrsd
  have hρdN : 0 < ρd := pos_of_ble hρd
  have hrsdN : 0 < rsd := pos_of_ble hrsd
  simp only [Real.IsNear] at hx hsc ⊢
  have hrad : ((rsn * ρd + ρn * rsd : ℕ) : ℝ) / ((rsd * ρd : ℕ) : ℝ)
            = (ρn : ℝ) / ρd + (rsn : ℝ) / rsd := by
    rw [div_eq_iff (by positivity)]; push_cast; field_simp; ring
  rw [hrad]
  calc |f x - sfrac sn scn scd|
      ≤ |f x - f (sfrac nc cn cd)| + |f (sfrac nc cn cd) - sfrac sn scn scd| :=
        abs_sub_le _ _ _
    _ ≤ |x - sfrac nc cn cd| + (rsn : ℝ) / rsd := add_le_add (hf _ _) hsc
    _ ≤ (ρn : ℝ) / ρd + (rsn : ℝ) / rsd := by linarith [hx]

/-- `sin` of an enclosure: `lipschitz_image` at `Real.abs_sin_sub_sin_le`. -/
theorem Real.IsNear.sin_image {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (Real.sin c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (Real.sin x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) :=
  lipschitz_image (fun _ _ => Real.abs_sin_sub_sin_le _ _) hx hc hsc hρd hrsd

/-- `cos` of an enclosure: `lipschitz_image` at `Real.abs_cos_sub_cos_le`. -/
theorem Real.IsNear.cos_image {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (Real.cos c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (Real.cos x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) :=
  lipschitz_image (fun _ _ => Real.abs_cos_sub_cos_le _ _) hx hc hsc hρd hrsd

/-- Midpoint enclosure from rational endpoints: if `a/Q ≤ z ≤ b/Q` (`Q > 0`), then `z` is near the
midpoint `(a+b)/(2Q)` with radius `(b−a)/(2Q)`. Shared tail of `sqrt_image` and `inv_image`. -/
theorem Real.IsNear.of_endpoints {z : ℝ} {a b Q : ℕ} (hQ : Nat.ble 1 Q)
    (h1 : (a : ℝ) / Q ≤ z) (h2 : z ≤ (b : ℝ) / Q) :
    Real.IsNear z false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a) (Nat.mul (nat_lit 2) Q) := by
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hab : a ≤ b := by
    have hh : (a : ℝ) / Q ≤ (b : ℝ) / Q := le_trans h1 h2
    rw [div_le_div_iff₀ hQR hQR] at hh
    exact_mod_cast le_of_mul_le_mul_right hh hQR
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  have hc1 : ((a : ℝ) + b) / (2 * Q) - ((b : ℝ) - a) / (2 * Q) = (a : ℝ) / Q := by field_simp; ring
  have hc2 : ((a : ℝ) + b) / (2 * Q) + ((b : ℝ) - a) / (2 * Q) = (b : ℝ) / Q := by field_simp; ring
  rw [Real.IsNear, sfrac_false_div, abs_le]
  push_cast [hcast]
  exact ⟨by linarith [h1, hc1], by linarith [h2, hc2]⟩

/-- `√` of a nonnegative enclosure `S ∈ [lo, hi]`: with square-to-verify bounds `a/Q ≤ √lo` and
`√hi ≤ b/Q` on the rational endpoints, monotonicity gives `√S ∈ [a/Q, b/Q]`, returned as the
midpoint `(a+b)/(2Q) ± (b−a)/(2Q)`. -/
theorem Real.IsNear.sqrt_image {S : ℝ} {cn cd rn rd a b Q : ℕ}
    (hS : Real.IsNear S false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hQ : Nat.ble 1 Q)
    (hge : Nat.ble (rn.mul cd) (cn.mul rd))
    (hlo : Nat.ble ((a.pow 2).mul (cd.mul rd)) (((cn.mul rd).sub (rn.mul cd)).mul (Q.pow 2)))
    (hhi : Nat.ble (((cn.mul rd).add (rn.mul cd)).mul (Q.pow 2)) ((b.pow 2).mul (cd.mul rd))) :
    Real.IsNear (Real.sqrt S) false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a)
      (Nat.mul (nat_lit 2) Q) := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq] at hge hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hsub : ((cn * rd - rn * cd : ℕ) : ℝ) = (cn : ℝ) * rd - rn * cd := by
    rw [Nat.cast_sub hge]; push_cast; ring
  have hQ2 : (0:ℝ) < (Q : ℝ) ^ 2 := by positivity
  have hcr : (0:ℝ) < (cd : ℝ) * rd := by positivity
  have hlo' : ((a : ℝ) / Q) ^ 2 ≤ (cn : ℝ) / cd - (rn : ℝ) / rd := by
    rw [div_pow, div_sub_div _ _ (ne_of_gt hcdR) (ne_of_gt hrdR), div_le_div_iff₀ hQ2 hcr]
    have h : ((a ^ 2 * (cd * rd) : ℕ) : ℝ) ≤ (((cn * rd - rn * cd) * Q ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hlo
    push_cast [hsub] at h; nlinarith [h]
  have hhi' : (cn : ℝ) / cd + (rn : ℝ) / rd ≤ ((b : ℝ) / Q) ^ 2 := by
    rw [div_pow, div_add_div _ _ (ne_of_gt hcdR) (ne_of_gt hrdR), div_le_div_iff₀ hcr hQ2]
    have h : (((cn * rd + rn * cd) * Q ^ 2 : ℕ) : ℝ) ≤ ((b ^ 2 * (cd * rd) : ℕ) : ℝ) := by
      exact_mod_cast hhi
    push_cast at h; nlinarith [h]
  have hSlo : (cn : ℝ) / cd - (rn : ℝ) / rd ≤ S := by have h := hS.lower; rwa [sfrac_false_div] at h
  have hShi : S ≤ (cn : ℝ) / cd + (rn : ℝ) / rd := by have h := hS.upper; rwa [sfrac_false_div] at h
  have h1 : (a : ℝ) / Q ≤ Real.sqrt S := by
    calc (a : ℝ) / Q = Real.sqrt (((a : ℝ) / Q) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((cn : ℝ) / cd - (rn : ℝ) / rd) := Real.sqrt_le_sqrt hlo'
      _ ≤ Real.sqrt S := Real.sqrt_le_sqrt hSlo
  have h2 : Real.sqrt S ≤ (b : ℝ) / Q := by
    calc Real.sqrt S ≤ Real.sqrt ((cn : ℝ) / cd + (rn : ℝ) / rd) := Real.sqrt_le_sqrt hShi
      _ ≤ Real.sqrt (((b : ℝ) / Q) ^ 2) := Real.sqrt_le_sqrt hhi'
      _ = (b : ℝ) / Q := Real.sqrt_sq (by positivity)
  exact Real.IsNear.of_endpoints hQ h1 h2

/-- Enclosure of `y` from a two-sided sandwich `y1 ≤ y ≤ y2` (enclosures of `y1`, `y2`) plus literal
result fields whose interval contains `[y1.lo, y2.hi]` (`hL`/`hH`). -/
theorem Real.IsNear.of_interval {y y1 y2 : ℝ} {n1 n2 nR : Bool}
    {c1 d1 r1 e1 c2 d2 r2 e2 cnR cdR rnR rdR : ℕ}
    (h1 : Real.IsNear y1 n1 c1 d1 r1 e1) (h2 : Real.IsNear y2 n2 c2 d2 r2 e2)
    (hlo : y1 ≤ y) (hhi : y ≤ y2)
    (hd1 : Nat.ble 1 d1) (he1 : Nat.ble 1 e1) (hd2 : Nat.ble 1 d2) (he2 : Nat.ble 1 e2)
    (hcdR : Nat.ble 1 cdR) (hrdR : Nat.ble 1 rdR)
    (hL : Nat.ble ((((numPos nR cnR).mul ((rdR.mul d1).mul e1)).add
              ((numNeg n1 c1).mul ((cdR.mul rdR).mul e1))).add
              (r1.mul ((cdR.mul rdR).mul d1)))
            ((((numPos n1 c1).mul ((cdR.mul rdR).mul e1)).add
              ((numNeg nR cnR).mul ((rdR.mul d1).mul e1))).add
              (rnR.mul ((cdR.mul d1).mul e1))))
    (hH : Nat.ble ((((numPos n2 c2).mul ((cdR.mul rdR).mul e2)).add
              ((numNeg nR cnR).mul ((rdR.mul d2).mul e2))).add
              (r2.mul ((cdR.mul rdR).mul d2)))
            ((((numPos nR cnR).mul ((rdR.mul d2).mul e2)).add
              ((numNeg n2 c2).mul ((cdR.mul rdR).mul e2))).add
              (rnR.mul ((cdR.mul d2).mul e2)))) :
    Real.IsNear y nR cnR cdR rnR rdR := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hL hH
  have hd1R : (0:ℝ) < d1 := pos_real_of_ble hd1
  have he1R : (0:ℝ) < e1 := pos_real_of_ble he1
  have hd2R : (0:ℝ) < d2 := pos_real_of_ble hd2
  have he2R : (0:ℝ) < e2 := pos_real_of_ble he2
  have hcdRR : (0:ℝ) < cdR := pos_real_of_ble hcdR
  have hrdRR : (0:ℝ) < rdR := pos_real_of_ble hrdR
  have hloR : sfrac nR cnR cdR - (rnR : ℝ) / rdR ≤ sfrac n1 c1 d1 - (r1 : ℝ) / e1 := by
    rw [sfrac_eq_parts nR cnR cdR, sfrac_eq_parts n1 c1 d1,
      div_sub_div _ _ hcdRR.ne' hrdRR.ne', div_sub_div _ _ hd1R.ne' he1R.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos nR cnR * (rdR * d1 * e1) + numNeg n1 c1 * (cdR * rdR * e1)
                + r1 * (cdR * rdR * d1) : ℕ) : ℝ)
            ≤ ((numPos n1 c1 * (cdR * rdR * e1) + numNeg nR cnR * (rdR * d1 * e1)
                + rnR * (cdR * d1 * e1) : ℕ) : ℝ) := by exact_mod_cast hL
    push_cast at hc ⊢; nlinarith [hc]
  have hhiR : sfrac n2 c2 d2 + (r2 : ℝ) / e2 ≤ sfrac nR cnR cdR + (rnR : ℝ) / rdR := by
    rw [sfrac_eq_parts nR cnR cdR, sfrac_eq_parts n2 c2 d2,
      div_add_div _ _ hd2R.ne' he2R.ne', div_add_div _ _ hcdRR.ne' hrdRR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos n2 c2 * (cdR * rdR * e2) + numNeg nR cnR * (rdR * d2 * e2)
                + r2 * (cdR * rdR * d2) : ℕ) : ℝ)
            ≤ ((numPos nR cnR * (rdR * d2 * e2) + numNeg n2 c2 * (cdR * rdR * e2)
                + rnR * (cdR * d2 * e2) : ℕ) : ℝ) := by exact_mod_cast hH
    push_cast at hc ⊢; nlinarith [hc]
  exact Real.IsNear.mk' (le_trans hloR (le_trans h1.lower hlo))
    (le_trans hhi (le_trans h2.upper hhiR))

/-- Reciprocal of a strictly positive enclosure `x ∈ [lo, hi]` (`lo > 0`): with cross-multiplied
`Nat.ble` bounds `a/Q ≤ 1/hi` and `1/lo ≤ b/Q`, `x⁻¹ ∈ [a/Q, b/Q]`, returned in midpoint form. -/
theorem Real.IsNear.inv_image {x : ℝ} {cn cd rn rd a b Q : ℕ}
    (hx : Real.IsNear x false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hQ : Nat.ble 1 Q)
    (hpos : Nat.blt (rn.mul cd) (cn.mul rd))
    (hlo : Nat.ble (a.mul ((cn.mul rd).add (rn.mul cd))) (Q.mul (cd.mul rd)))
    (hhi : Nat.ble (Q.mul (cd.mul rd)) (b.mul ((cn.mul rd).sub (rn.mul cd)))) :
    Real.IsNear x⁻¹ false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a)
      (Nat.mul (nat_lit 2) Q) := by
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hpos hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hposn : rn * cd < cn * rd := hpos
  have hsub : ((cn * rd - rn * cd : ℕ) : ℝ) = (cn : ℝ) * rd - rn * cd := by
    rw [Nat.cast_sub hposn.le]; push_cast; ring
  have hloQ : (0:ℝ) < (cn : ℝ) / cd - (rn : ℝ) / rd := by
    rw [div_sub_div _ _ hcdR.ne' hrdR.ne', lt_div_iff₀ (by positivity)]
    have h := hposn
    have : ((rn * cd : ℕ) : ℝ) < ((cn * rd : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; nlinarith [this]
  have hSlo : (cn : ℝ) / cd - (rn : ℝ) / rd ≤ x := by
    have h := hx.lower; rwa [sfrac_false_div] at h
  have hShi : x ≤ (cn : ℝ) / cd + (rn : ℝ) / rd := by
    have h := hx.upper; rwa [sfrac_false_div] at h
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le hloQ hSlo
  have hdiffR : (0:ℝ) < (cn : ℝ) * rd - (cd : ℝ) * rn := by
    have h' : ((rn * cd : ℕ) : ℝ) < ((cn * rd : ℕ) : ℝ) := by exact_mod_cast hposn
    push_cast at h'; linarith
  have hsumR : (0:ℝ) < (cn : ℝ) * rd + (cd : ℝ) * rn := by
    have hcdrn : (0:ℝ) ≤ (cd : ℝ) * rn := by positivity
    linarith
  have h1 : (a : ℝ) / Q ≤ x⁻¹ := by
    have hstep : (a : ℝ) / Q ≤ ((cn : ℝ) / cd + (rn : ℝ) / rd)⁻¹ := by
      rw [div_add_div _ _ hcdR.ne' hrdR.ne', inv_div, div_le_div_iff₀ hQR hsumR]
      have h' : ((a * (cn * rd + rn * cd) : ℕ) : ℝ) ≤ ((Q * (cd * rd) : ℕ) : ℝ) := by
        exact_mod_cast hlo
      push_cast at h'; nlinarith [h']
    exact le_trans hstep (inv_anti₀ hx0 hShi)
  have h2 : x⁻¹ ≤ (b : ℝ) / Q := by
    have hstep : ((cn : ℝ) / cd - (rn : ℝ) / rd)⁻¹ ≤ (b : ℝ) / Q := by
      rw [div_sub_div _ _ hcdR.ne' hrdR.ne', inv_div, div_le_div_iff₀ hdiffR hQR]
      have h' : ((Q * (cd * rd) : ℕ) : ℝ) ≤ ((b * (cn * rd - rn * cd) : ℕ) : ℝ) := by
        exact_mod_cast hhi
      push_cast [hsub] at h'; nlinarith [h']
    exact le_trans (inv_anti₀ hloQ hSlo) hstep
  exact Real.IsNear.of_endpoints hQ h1 h2

end Enclosure
