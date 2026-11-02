/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannXi
public import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
public import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting

/-!
# `N(T)` counts zeros of ξ in a box

The `PrimeNumberTheoremAnd` zero-counting function `riemannZeta.N`, in terms of the zeros of the
Riemann ξ function.

## Main results

- `riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero`: every zero of ζ with nonzero imaginary part
  lies in the open critical strip `0 < Re s < 1`.
- `riemannZeta.N_eq_tsum_riemannXi_order`: `N(T)` is the sum, over zeros `ρ` of ξ in the box
  `0 < Re ρ < 1`, `0 < Im ρ < T`, of the multiplicity `meromorphicOrderAt riemannXi ρ`.
- `riemannZeta_ne_zero_of_forall_re_mem_Ico`: non-vanishing of `ζ` on the whole line `Im s = T`
  reduces to non-vanishing on the segment `Re ∈ [½, 1)` at height `T`.
-/
@[expose] public section


open Complex

/-- **Zeros of ζ off the real axis lie in the open critical strip.** If `ζ s = 0` and
`s.im ≠ 0`, then `0 < Re s < 1`. -/
theorem riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero {s : ℂ}
    (hz : riemannZeta s = 0) (him : s.im ≠ 0) : s.re ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨not_le.mp fun h ↦ Kadiri.riemannZeta_ne_zero_of_re_nonpos_im_ne_zero h him hz,
    not_le.mp fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz⟩

/-- **`N(T)` counts the zeros of ξ in a box.** For every `T`, `riemannZeta.N T` is the sum, over
the zeros `ρ` of ξ with `0 < Re ρ < 1` and `0 < Im ρ < T`, of the multiplicity
`meromorphicOrderAt riemannXi ρ`. -/
theorem riemannZeta.N_eq_tsum_riemannXi_order (T : ℝ) :
    riemannZeta.N T =
      ∑' ρ : {z : ℂ // riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1 ∧ z.im ∈ Set.Ioo (0 : ℝ) T},
        (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ) := by
  -- the index set of `N` is exactly the box of ξ-zeros
  have hset : riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T) =
      {z : ℂ | riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1 ∧ z.im ∈ Set.Ioo (0 : ℝ) T} := by
    ext z
    constructor
    · rintro ⟨-, hzim, hzero⟩
      have hre := riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hzero hzim.1.ne'
      obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp hre
      exact ⟨(riemannXi_eq_zero_iff hre0 hre1).mpr hzero, hre, hzim⟩
    · rintro ⟨hxi, hre, hzim⟩
      obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp hre
      exact ⟨Set.mem_univ _, hzim, (riemannXi_eq_zero_iff hre0 hre1).mp hxi⟩
  calc riemannZeta.N T
      = ∑' ρ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)),
          (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ) := by
        simp only [riemannZeta.N, riemannZeta.zeroes_sum]
        refine tsum_congr fun ρ ↦ ?_
        obtain ⟨-, hzim, hzero⟩ := ρ.property
        obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp
          (riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hzero hzim.1.ne')
        simp only [one_mul, riemannZeta.order,
          meromorphicOrderAt_riemannXi_eq_riemannZeta hre0 hre1]
    _ = _ := (Equiv.setCongr hset).tsum_eq
        (fun ρ ↦ (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))

/-- A complex number at height `T` is `↑(its real part) + I·T`. -/
private theorem eq_ofReal_re_add_I_mul {T : ℝ} {z : ℂ} (hz : z.im = T) :
    z = (↑z.re : ℂ) + Complex.I * (T : ℂ) := by
  apply Complex.ext <;> simp [hz]

/-- **Reduction of the ordinate hypothesis to a compact segment.** For `T > 0`, non-vanishing of
`ζ` on the whole horizontal line `{s : Im s = T}` follows from non-vanishing on the half-open
real-part segment `Re ∈ [½, 1)` at height `T`. This is what makes the ordinate hypothesis of
`riemannZeta.N_eq` numerically certifiable. -/
theorem riemannZeta_ne_zero_of_forall_re_mem_Ico {T : ℝ} (hT : 0 < T)
    (h : ∀ σ : ℝ, σ ∈ Set.Ico (1 / 2 : ℝ) 1 →
      riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0 := by
  intro s hs hz0
  have him : s.im ≠ 0 := by rw [hs]; exact hT.ne'
  obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp (riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hz0 him)
  have hxi : riemannXi s = 0 := (riemannXi_eq_zero_iff hre0 hre1).mpr hz0
  rcases le_or_gt (1 / 2 : ℝ) s.re with hge | hlt
  · -- `Re s ∈ [½, 1)`: the zero already lies on the segment.
    apply h s.re ⟨hge, hre1⟩
    rw [← eq_ofReal_re_add_I_mul hs]; exact hz0
  · -- `Re s ∈ (0, ½)`: reflect to `w = 1 - conj s`, with `Re w ∈ (½, 1)` at the same height.
    set w : ℂ := 1 - starRingEnd ℂ s with hw
    have hxi_w : riemannXi w = 0 := by
      rw [hw, riemannXi_one_sub, riemannXi_conj, hxi, map_zero]
    have hw_re : w.re = 1 - s.re := by simp [hw]
    have hw_im : w.im = T := by rw [hw]; simp [hs]
    apply h w.re ⟨by rw [hw_re]; linarith, by rw [hw_re]; linarith⟩
    rw [← eq_ofReal_re_add_I_mul hw_im]
    exact (riemannXi_eq_zero_iff (by rw [hw_re]; linarith) (by rw [hw_re]; linarith)).mp hxi_w
