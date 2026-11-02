module

public import Enclosure
public import Mathlib.Analysis.Real.Sqrt

/-!
# Certified `IsNear` enclosure for `√(N/M)` by squaring (everything as `ℕ`)

A dyadic enclosure `[a/Q, b/Q]` of `√(N/M)` is certified by squaring: `a²·M ≤ N·Q²` and
`N·Q² ≤ b²·M` are pure-`ℕ` comparisons, turned into an `IsNear` via monotonicity of `√`.
-/
@[expose] public section


namespace BSN
open Enclosure

/-- Certified `IsNear` enclosure for `√(N/M)`, all data carried as `ℕ`. From the squaring
conditions `a²·M ≤ N·Q²` and `N·Q² ≤ b²·M`, conclude `√(N/M) ∈ [a/Q, b/Q]`: centre `(a+b)/(2Q)`,
radius `(b−a)/(2Q)`. -/
theorem sqrt_enclosure (N M a b Q : ℕ)
    (hM : Nat.ble 1 M) (hQ : Nat.ble 1 Q) (hab : Nat.ble a b)
    (hlo : ((a.pow 2).mul M).ble (N.mul (Q.pow 2)))
    (hhi : (N.mul (Q.pow 2)).ble ((b.pow 2).mul M)) :
    Real.IsNear (Real.sqrt ((N : ℝ) / M)) false (a.add b) (Nat.mul 2 Q) (b.sub
          a) (Nat.mul 2 Q) := by
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  simp only [Nat.ble_eq, Nat.mul_eq, Nat.pow_eq] at hab hlo hhi
  have hMr : (0 : ℝ) < M := pos_real_of_ble hM
  have hQr : (0 : ℝ) < Q := pos_real_of_ble hQ
  have hQ2 : (0 : ℝ) < (Q : ℝ) ^ 2 := pow_pos hQr 2
  have hlo' : ((a : ℝ) / Q) ^ 2 ≤ (N : ℝ) / M := by
    rw [div_pow, div_le_div_iff₀ hQ2 hMr]; exact_mod_cast hlo
  have hhi' : (N : ℝ) / M ≤ ((b : ℝ) / Q) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hMr hQ2]; exact_mod_cast hhi
  have h1 : (a : ℝ) / Q ≤ Real.sqrt ((N : ℝ) / M) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (a : ℝ) / Q)]
    exact Real.sqrt_le_sqrt hlo'
  have h2 : Real.sqrt ((N : ℝ) / M) ≤ (b : ℝ) / Q := by
    calc Real.sqrt ((N : ℝ) / M)
        ≤ Real.sqrt (((b : ℝ) / Q) ^ 2) := Real.sqrt_le_sqrt hhi'
      _ = (b : ℝ) / Q := Real.sqrt_sq (by positivity)
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab
  have hc1 : ((a : ℝ) + b) / (2 * Q) - ((b : ℝ) - a) / (2 * Q) = (a : ℝ) / Q := by field_simp; ring
  have hc2 : ((a : ℝ) + b) / (2 * Q) + ((b : ℝ) - a) / (2 * Q) = (b : ℝ) / Q := by field_simp; ring
  rw [Real.IsNear, sfrac_false_div, abs_le]
  push_cast [hcast]
  exact ⟨by linarith [h1, hc1], by linarith [h2, hc2]⟩

end BSN
