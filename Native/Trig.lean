module

public import Native.Eval.Trig
public import Native.Const
public import Enclosure.BinarySplit.Functions.Cos
public import Enclosure.BinarySplit.Functions.Sin
public import Enclosure.BinarySplit.Reduce.Sin

/-!
# Native `cos` and `sin`

* `cosRat u v D`, `sinRat u v D`: `cos(u/v)`, `sin(u/v)` to `1/D` for a small rational argument, by
  binary splitting (`BSN.cos_dyadic_bound`, `BSN.sin_dyadic_bound`);
* `cosSmall X D`, `sinSmall X D`: of an enclosure `X` with a small centre, by the leaf at the centre
  and the `1`-Lipschitz bound (`Real.IsNear.cos_image`, `sin_image`);
* `cos X D`, `sin X D`: of any enclosure, reducing by the nearest multiple `k·π/2` with `Encl`
  arithmetic and the quadrant identities (`BSN.cos_quad0..3`, `sin_quad0..3`).
-/
@[expose] public section

namespace Native

open Enclosure BSN

/-! ### Shared helpers -/

/-! ### `cos` and `sin` of a small rational -/

theorem cosRat_encloses {u v D : ℕ} {e : Encl} (h : cosRat u v D = some e) :
    e.Encloses (Real.cos ((u : ℝ) / v)) := by
  simp only [cosRat] at h
  split at h
  · rename_i hc
    simp only [cosRatOk, Bool.and_eq_true, and_assoc] at hc
    obtain ⟨hu, hu2, hQe, hQo, hD, hv, hM, hMm, htail, hr1, hr2, hQ⟩ := hc
    cases h
    exact cos_dyadic_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu hu2 hQe hQo hD hv hM hMm rfl rfl htail
      hr1 hr2 hQ
  · cases h

theorem sinRat_encloses {u v D : ℕ} {e : Encl} (h : sinRat u v D = some e) :
    e.Encloses (Real.sin ((u : ℝ) / v)) := by
  simp only [sinRat] at h
  split at h
  · rename_i hc
    simp only [sinRatOk, Bool.and_eq_true, and_assoc] at hc
    obtain ⟨hu, hu2, hQe, hQo, hD, hv, hM, hMm, htail, hr1, hr2, hQ⟩ := hc
    cases h
    exact sin_dyadic_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu hu2 hQe hQo hD hv hM hMm rfl rfl htail
      hr1 hr2 hQ
  · cases h

/-! ### `cos` and `sin` of an enclosure with a small centre -/

/-- A leaf at `cn/cd` gives one at the signed centre `±cn/cd`: `cos` is even. -/
theorem cos_sfrac_of_rat {neg : Bool} {cn cd : ℕ} {e : Encl}
    (h : e.Encloses (Real.cos ((cn : ℝ) / cd))) : e.Encloses (Real.cos (sfrac neg cn cd)) := by
  cases neg
  · rwa [sfrac_false_div]
  · rw [sfrac_true_div]; exact cos_neg_of_bound _ _ _ _ _ _ _ h

/-- A leaf at `cn/cd` gives one at the signed centre `±cn/cd`: `sin` is odd, so the sign follows
the centre's. -/
theorem sin_sfrac_of_rat {neg : Bool} {cn cd : ℕ} {e : Encl}
    (h : e.Encloses (Real.sin ((cn : ℝ) / cd))) :
    (if neg then e.negate else e).Encloses (Real.sin (sfrac neg cn cd)) := by
  cases neg
  · simpa [sfrac_false_div] using h
  · rw [sfrac_true_div]; exact sin_neg_of_bound _ _ _ _ _ _ _ h

theorem lipschitzImage_encloses {f : ℝ → ℝ} (hf : ∀ a b, |f a - f b| ≤ |a - b|) {X c e : Encl}
    {x : ℝ} (hx : X.Encloses x) (hc : c.Encloses (f (sfrac X.neg X.cn X.cd)))
    (h : lipschitzImage X c = some e) : e.Encloses (f x) := by
  simp only [lipschitzImage] at h
  split at h
  · rename_i hd
    simp only [Bool.and_eq_true] at hd
    cases h
    exact Real.IsNear.lipschitz_image hf hx rfl hc hd.1 hd.2
  · cases h

theorem cosSmall_encloses {X e : Encl} {D : ℕ} {x : ℝ} (hx : X.Encloses x)
    (h : cosSmall X D = some e) : e.Encloses (Real.cos x) := by
  simp only [cosSmall, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, he⟩ := h
  exact lipschitzImage_encloses (fun _ _ => Real.abs_cos_sub_cos_le _ _) hx
    (cos_sfrac_of_rat (cosRat_encloses hc)) he

theorem sinSmall_encloses {X e : Encl} {D : ℕ} {x : ℝ} (hx : X.Encloses x)
    (h : sinSmall X D = some e) : e.Encloses (Real.sin x) := by
  simp only [sinSmall, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, he⟩ := h
  exact lipschitzImage_encloses (fun _ _ => Real.abs_sin_sub_sin_le _ _) hx
    (sin_sfrac_of_rat (sinRat_encloses hc)) he

/-! ### Range reduction by `k·π/2` -/

/-- The reduction identity: `x = (x − (k/2)·π) + (4·⌊k/4⌋ + k mod 4)·(π/2)`. -/
theorem reduce_eq (x : ℝ) (k : ℕ) :
    x = (x - sfrac false k 2 * Real.pi)
      + (4 * (((k / 4 : ℕ) : ℤ) : ℝ) + ((k % 4 : ℕ) : ℝ)) * (Real.pi / 2) := by
  have hk : 4 * ((k / 4 : ℕ) : ℝ) + ((k % 4 : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast Nat.div_add_mod k 4
  rw [sfrac_false_div, Int.cast_natCast, hk]
  ring

theorem quadCos_encloses {j : ℕ} {Y e : Encl} {D : ℕ} {y : ℝ} (q : ℤ) (hy : Y.Encloses y)
    (h : quadCos j Y D = some e) :
    e.Encloses (Real.cos (y + (4 * (q : ℝ) + (j : ℝ)) * (Real.pi / 2))) := by
  match j, h with
  | 0, h =>
    simp only [quadCos] at h
    simpa [cos_quad0] using cosSmall_encloses hy h
  | 1, h =>
    simp only [quadCos, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, rfl⟩ := h
    simpa [cos_quad1] using Encl.negate_encloses (sinSmall_encloses hy hc)
  | 2, h =>
    simp only [quadCos, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, rfl⟩ := h
    have : (4 * (q : ℝ) + ((2 : ℕ) : ℝ)) = 4 * (q : ℝ) + 2 := by norm_num
    rw [this, cos_quad2]
    exact Encl.negate_encloses (cosSmall_encloses hy hc)
  | 3, h =>
    simp only [quadCos] at h
    have : (4 * (q : ℝ) + ((3 : ℕ) : ℝ)) = 4 * (q : ℝ) + 3 := by norm_num
    rw [this, cos_quad3]
    exact sinSmall_encloses hy h
  | _ + 4, h => simp [quadCos] at h

theorem quadSin_encloses {j : ℕ} {Y e : Encl} {D : ℕ} {y : ℝ} (q : ℤ) (hy : Y.Encloses y)
    (h : quadSin j Y D = some e) :
    e.Encloses (Real.sin (y + (4 * (q : ℝ) + (j : ℝ)) * (Real.pi / 2))) := by
  match j, h with
  | 0, h =>
    simp only [quadSin] at h
    simpa [sin_quad0] using sinSmall_encloses hy h
  | 1, h =>
    simp only [quadSin] at h
    simpa [sin_quad1] using cosSmall_encloses hy h
  | 2, h =>
    simp only [quadSin, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, rfl⟩ := h
    have : (4 * (q : ℝ) + ((2 : ℕ) : ℝ)) = 4 * (q : ℝ) + 2 := by norm_num
    rw [this, sin_quad2]
    exact Encl.negate_encloses (sinSmall_encloses hy hc)
  | 3, h =>
    simp only [quadSin, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, rfl⟩ := h
    have : (4 * (q : ℝ) + ((3 : ℕ) : ℝ)) = 4 * (q : ℝ) + 3 := by norm_num
    rw [this, sin_quad3]
    exact Encl.negate_encloses (cosSmall_encloses hy hc)
  | _ + 4, h => simp [quadSin] at h

theorem reduceQuarter_encloses {X Y : Encl} {k D : ℕ} {x : ℝ} (hx : X.Encloses x)
    (h : reduceQuarter X k D = some Y) : Y.Encloses (x - sfrac false k 2 * Real.pi) := by
  simp only [reduceQuarter, Option.bind_eq_some_iff] at h
  obtain ⟨K, hK, Y₀, hY₀, hY⟩ := h
  exact Encl.recentre_encloses
    (Encl.sub_encloses hx (Encl.mul_encloses (Encl.const_encloses false k 2) piEncl_encloses hK)
      hY₀) hY

theorem cosNonneg_encloses {X e : Encl} {D : ℕ} {x : ℝ} (hx : X.Encloses x)
    (h : cosNonneg X D = some e) : e.Encloses (Real.cos x) := by
  simp only [cosNonneg, Option.bind_eq_some_iff] at h
  obtain ⟨Y, hY, he⟩ := h
  have := quadCos_encloses (((nearestQuarterTurn X) / 4 : ℕ) : ℤ)
    (reduceQuarter_encloses hx hY) he
  rwa [← reduce_eq] at this

theorem sinNonneg_encloses {X e : Encl} {D : ℕ} {x : ℝ} (hx : X.Encloses x)
    (h : sinNonneg X D = some e) : e.Encloses (Real.sin x) := by
  simp only [sinNonneg, Option.bind_eq_some_iff] at h
  obtain ⟨Y, hY, he⟩ := h
  have := quadSin_encloses (((nearestQuarterTurn X) / 4 : ℕ) : ℤ)
    (reduceQuarter_encloses hx hY) he
  rwa [← reduce_eq] at this

/-! ### `cos` and `sin` of any enclosure -/

theorem cos_encloses {X e : Encl} {D : ℕ} {x : ℝ} (hx : X.Encloses x) (h : cos X D = some e) :
    e.Encloses (Real.cos x) := by
  simp only [cos] at h
  split at h
  · simpa using cosNonneg_encloses (Encl.negate_encloses hx) h
  · exact cosNonneg_encloses hx h

theorem sin_encloses {X e : Encl} {D : ℕ} {x : ℝ} (hx : X.Encloses x) (h : sin X D = some e) :
    e.Encloses (Real.sin x) := by
  simp only [sin] at h
  split at h
  · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    simpa using Encl.negate_encloses (sinNonneg_encloses (Encl.negate_encloses hx) hc)
  · exact sinNonneg_encloses hx h

end Native
