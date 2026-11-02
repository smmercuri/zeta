module

public import Native.Eval.Encl
public import Enclosure.Arith
public import Enclosure.Images

/-!
# Native enclosures: fields and arithmetic

`Encl` packages the five fields of an `Enclosure.Real.IsNear` enclosure (`x ∈ ±cn/cd ± rn/rd`) as
data, so that enclosures can be *computed* by ordinary functions and evaluated natively. Each
operation computes candidate output fields, checks exactly the `Bool` side conditions of the
`Enclosure` lemma it mirrors, and returns `none` if any fails; its soundness theorem then applies
that lemma. Nothing here chooses numbers that need proofs: every choice is re-checked.

* `Encl.Encloses e x`: `e` encloses `x`;
* `negate`, `add`, `sub`, `mul`: exact field arithmetic (`Real.IsNear.add`/`mul`);
* `recentre e Q`: round the centre down to the grid `1/Q` and inflate the radius, keeping field
  sizes bounded (`Real.IsNear.recentre'`);
* `inv e Q`, `sqrt e Q`: reciprocal and square root, with endpoints on the grid `1/Q`
  (`Real.IsNear.inv_image`/`sqrt_image`).
-/
@[expose] public section

namespace Native

open Enclosure

namespace Encl

/-- `e` encloses `x`: `|x − ±cn/cd| ≤ rn/rd`. -/
def Encloses (e : Encl) (x : ℝ) : Prop := Real.IsNear x e.neg e.cn e.cd e.rn e.rd

theorem const_encloses (neg : Bool) (cn cd : ℕ) : (const neg cn cd).Encloses (sfrac neg cn cd) :=
  Real.IsNear.const neg cn cd

/-! ### Negation, addition, subtraction -/

theorem negate_encloses {e : Encl} {x : ℝ} (h : e.Encloses x) : e.negate.Encloses (-x) :=
  Real.IsNear.neg h

theorem add_encloses {ex ey e : Encl} {x y : ℝ} (hx : ex.Encloses x) (hy : ey.Encloses y)
    (h : add ex ey = some e) : e.Encloses (x + y) := by
  simp only [add] at h
  split at h
  · rename_i hc
    simp only [denomsPos, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hcdx, hrdx⟩, hcdy, hrdy⟩, hnum⟩ := hc
    cases h
    exact Real.IsNear.add hx hy hcdx hcdy hrdx hrdy hnum
  · cases h

theorem sub_encloses {ex ey e : Encl} {x y : ℝ} (hx : ex.Encloses x) (hy : ey.Encloses y)
    (h : sub ex ey = some e) : e.Encloses (x - y) := by
  rw [sub_eq_add_neg]
  exact add_encloses hx (negate_encloses hy) h

/-! ### Multiplication -/

theorem mul_encloses {ex ey e : Encl} {x y : ℝ} (hx : ex.Encloses x) (hy : ey.Encloses y)
    (h : mul ex ey = some e) : e.Encloses (x * y) := by
  simp only [mul] at h
  split at h
  · rename_i hc
    simp only [denomsPos, Bool.and_eq_true] at hc
    obtain ⟨⟨hcdx, hrdx⟩, hcdy, hrdy⟩ := hc
    cases h
    exact Real.IsNear.mul hx hy hcdx hcdy hrdx hrdy
  · cases h

/-! ### Recentring onto a grid -/

theorem recentre_encloses {e e' : Encl} {Q : ℕ} {x : ℝ} (hx : e.Encloses x)
    (h : recentre e Q = some e') : e'.Encloses x := by
  simp only [recentre] at h
  split at h
  · rename_i hc
    cases h
    exact Real.IsNear.recentre' hx hc
  · cases h

/-! ### Reciprocal and square root -/

theorem invPos_encloses {e e' : Encl} {Q : ℕ} {x : ℝ} (hx : e.Encloses x)
    (h : invPos e Q = some e') : e'.Encloses x⁻¹ := by
  obtain ⟨neg, cn, cd, rn, rd⟩ := e
  simp only [invPos] at h
  split at h
  · rename_i hc
    simp only [denomsPos, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨hneg, hcd, hrd⟩, hQ⟩, hpos⟩, hlo⟩, hhi⟩ := hc
    subst hneg
    cases h
    exact Real.IsNear.inv_image hx hcd hrd hQ hpos hlo hhi
  · cases h

theorem inv_encloses {e e' : Encl} {Q : ℕ} {x : ℝ} (hx : e.Encloses x)
    (h : inv e Q = some e') : e'.Encloses x⁻¹ := by
  simp only [inv] at h
  split at h
  · obtain ⟨e₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp h
    have := negate_encloses (invPos_encloses (negate_encloses hx) h₀)
    rwa [inv_neg, neg_neg] at this
  · exact invPos_encloses hx h

theorem sqrt_encloses {e e' : Encl} {Q : ℕ} {x : ℝ} (hx : e.Encloses x)
    (h : sqrt e Q = some e') : e'.Encloses (Real.sqrt x) := by
  obtain ⟨neg, cn, cd, rn, rd⟩ := e
  simp only [sqrt] at h
  split at h
  · rename_i hc
    simp only [denomsPos, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨⟨hneg, hcd, hrd⟩, hQ⟩, hge⟩, hlo⟩, hhi⟩ := hc
    subst hneg
    cases h
    exact Real.IsNear.sqrt_image hx hcd hrd hQ hge hlo hhi
  · cases h

/-! ### Hull of two enclosures -/

theorem hull_encloses {e₁ e₂ R : Encl} {Q : ℕ} {y y₁ y₂ : ℝ} (h₁ : e₁.Encloses y₁)
    (h₂ : e₂.Encloses y₂) (hlo : y₁ ≤ y) (hhi : y ≤ y₂) (h : hull e₁ e₂ Q = some R) :
    R.Encloses y := by
  simp only [hull] at h
  split at h
  · rename_i hc
    simp only [hullOk, Bool.and_eq_true, and_assoc] at hc
    obtain ⟨hd1, he1, hd2, he2, hcdR, hrdR, hL, hH⟩ := hc
    cases h
    exact Real.IsNear.of_interval h₁ h₂ hlo hhi hd1 he1 hd2 he2 hcdR hrdR hL hH
  · cases h

/-! ### Arithmetic recentred onto a grid

The working forms: each operation followed by `recentre` onto the grid `1/Q`, so that repeated
arithmetic keeps its fields bounded. -/

theorem addR_encloses {ex ey e : Encl} {Q : ℕ} {x y : ℝ} (hx : ex.Encloses x)
    (hy : ey.Encloses y) (h : addR ex ey Q = some e) : e.Encloses (x + y) := by
  obtain ⟨s, hs, he⟩ := Option.bind_eq_some_iff.mp h
  exact recentre_encloses (add_encloses hx hy hs) he

theorem subR_encloses {ex ey e : Encl} {Q : ℕ} {x y : ℝ} (hx : ex.Encloses x)
    (hy : ey.Encloses y) (h : subR ex ey Q = some e) : e.Encloses (x - y) := by
  obtain ⟨s, hs, he⟩ := Option.bind_eq_some_iff.mp h
  exact recentre_encloses (sub_encloses hx hy hs) he

theorem mulR_encloses {ex ey e : Encl} {Q : ℕ} {x y : ℝ} (hx : ex.Encloses x)
    (hy : ey.Encloses y) (h : mulR ex ey Q = some e) : e.Encloses (x * y) := by
  obtain ⟨s, hs, he⟩ := Option.bind_eq_some_iff.mp h
  exact recentre_encloses (mul_encloses hx hy hs) he

end Encl

end Native
