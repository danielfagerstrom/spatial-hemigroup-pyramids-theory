/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.StageLemma

/-!
# `prop:principle-after-decimation`: the pointwise principle fails after decimation

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:principle-after-decimation`. Review round 2,
batch C (open question (2) of the theory paper's § 7.2).

On `hℤ^d`, read in the indices `ℤ^d` as `stage_lemma_2` reads it, let `u := δ₀ + 2·1_{±eⱼ}` and
`f := u - τΔ_h u`, `Δ_h` the `(2d+1)`-point Laplacian (`gridLap`).

* **`κ * f = u`** (`kconv_resolvent_sub_gridLap`). Every probability kernel `κ` with the
  transform of `prop:stage-lemma`(2) solves `κ - τΔ_hκ = δ₀` (`resolvent_eqn_of_gridFourier`: it
  is the kernel of `stage_lemma_2`, by uniqueness of the Fourier coefficients,
  `kernel_eq_of_gridFourier_eq`).
  For summable `u`, `κ * (u - τΔ_h u) = κ * u - τ (Δ_hκ) * u = (κ - τΔ_hκ) * u = u`, `Δ_h` passing
  through a convolution with a summable kernel (`gridLap_kconv`).
* **`f(0) = 1 - 2dτ/h²`**: `Δ_h u(0) = h⁻² ∑ⱼ (2 - 2 + 2)`.
* **After decimation.** For an integer `q ≥ 2`, `±q eⱼ` is neither `0` nor an axis neighbour, so
  the decimated output `m ↦ u(qm)` vanishes at the axis neighbours of `0` and is `1` at `0`: the
  origin is a strict axis maximum, and `u(0) = 1 > f(0)` for `τ > 0`.
* **Before decimation** the origin is no axis maximum (`u(e₀) = 2 > 1`), and the pair obeys the
  principle on the fine grid, by `stage_lemma_2`.

**What it reaches.** Lean core.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter

variable {d : ℕ}

/-- **The output of `prop:principle-after-decimation`**: `u(0) = 1`, `u(±eⱼ) = 2`, `u = 0`
elsewhere, on `ℤ^d`. -/
noncomputable def decimationOutput (d : ℕ) (n : Zd d) : ℝ :=
  deltaZ n + (axisNbrs d).indicator (fun _ => (2 : ℝ)) n

/-- **The input of `prop:principle-after-decimation`**: `f := (I - τΔ_h)u`. -/
noncomputable def decimationInput (d : ℕ) (h τ : ℝ) (n : Zd d) : ℝ :=
  decimationOutput d n - τ * gridLap h (decimationOutput d) n

theorem zbasis_ne_zero (i : Fin d) : zbasis i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [zbasis] at this

theorem zero_not_mem_axisNbrs : (0 : Zd d) ∉ axisNbrs d := by
  rintro ⟨i, h | h⟩
  · exact zbasis_ne_zero i h.symm
  · exact zbasis_ne_zero i (neg_eq_zero.1 h.symm)

theorem neg_mem_axisNbrs {n : Zd d} (hn : n ∈ axisNbrs d) : -n ∈ axisNbrs d := by
  obtain ⟨i, h | h⟩ := hn
  · exact ⟨i, Or.inr (by rw [h])⟩
  · exact ⟨i, Or.inl (by rw [h, neg_neg])⟩

/-- For an integer `q ≥ 2`, `q eᵢ` is not an axis neighbour. -/
theorem smul_zbasis_not_mem_axisNbrs {q : ℕ} (hq : 2 ≤ q) (i : Fin d) :
    (q : ℤ) • zbasis i ∉ axisNbrs d := by
  rintro ⟨j, h | h⟩
  · have := congrFun h i
    simp only [Pi.smul_apply, zbasis, Pi.single_eq_same, smul_eq_mul, mul_one] at this
    rw [Pi.single_apply] at this
    split_ifs at this <;> omega
  · have := congrFun h i
    simp only [Pi.smul_apply, zbasis, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.neg_apply]
      at this
    rw [Pi.single_apply] at this
    split_ifs at this
    omega

theorem decimationOutput_zero : decimationOutput d 0 = 1 := by
  simp [decimationOutput, deltaZ, indicator_of_notMem zero_not_mem_axisNbrs]

theorem decimationOutput_of_mem {n : Zd d} (hn : n ∈ axisNbrs d) : decimationOutput d n = 2 := by
  have hn0 : n ≠ 0 := fun h => zero_not_mem_axisNbrs (h ▸ hn)
  simp [decimationOutput, deltaZ, hn0, indicator_of_mem hn]

theorem decimationOutput_of_ne {n : Zd d} (h0 : n ≠ 0) (hn : n ∉ axisNbrs d) :
    decimationOutput d n = 0 := by
  simp [decimationOutput, deltaZ, h0, indicator_of_notMem hn]

theorem axisNbrs_finite : (axisNbrs d).Finite := by
  have : axisNbrs d =
      (Set.range fun i : Fin d => zbasis i) ∪ Set.range fun i : Fin d => -zbasis i := by
    ext n
    simp only [axisNbrs, mem_setOf_eq, mem_union, mem_range]
    constructor
    · rintro ⟨i, h | h⟩
      · exact Or.inl ⟨i, h.symm⟩
      · exact Or.inr ⟨i, h.symm⟩
    · rintro (⟨i, h⟩ | ⟨i, h⟩)
      · exact ⟨i, Or.inl h.symm⟩
      · exact ⟨i, Or.inr h.symm⟩
  rw [this]
  exact (finite_range _).union (finite_range _)

theorem summable_decimationOutput : Summable (decimationOutput d) := by
  refine summable_deltaZ.add ?_
  refine summable_of_hasFiniteSupport (show Set.Finite _ from axisNbrs_finite.subset ?_)
  intro n hn
  by_contra h
  exact hn (indicator_of_notMem h _)

/-- **`f(0) = 1 - 2dτ/h²`.** -/
theorem decimationInput_zero (h τ : ℝ) :
    decimationInput d h τ 0 = 1 - 2 * d * τ / h ^ 2 := by
  have hp : ∀ i : Fin d, zbasis i ∈ axisNbrs d := fun i => ⟨i, Or.inl rfl⟩
  have hm : ∀ i : Fin d, -zbasis i ∈ axisNbrs d := fun i => ⟨i, Or.inr rfl⟩
  simp only [decimationInput, gridLap, zero_add, zero_sub, decimationOutput_zero,
    decimationOutput_of_mem (hp _), decimationOutput_of_mem (hm _)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The resolvent equation from the transform.** Every probability kernel with the transform of
`prop:stage-lemma`(2) solves `κ - τΔ_hκ = δ₀`. -/
theorem resolvent_eqn_of_gridFourier (hd : 1 ≤ d) {h τ : ℝ} (hh : 0 < h) (hτ : 0 ≤ τ)
    {κ : Zd d → ℝ} (hκ : IsProbKernel κ)
    (hκF : ∀ θ : Fin d → ℝ,
      gridFourier κ θ = (((1 + 4 * τ / h ^ 2 * ∑ j, Real.sin (θ j / 2) ^ 2)⁻¹ : ℝ) : ℂ)) :
    ∀ n, κ n - τ * gridLap h κ n = deltaZ n := by
  obtain ⟨κ₀, hκ₀, hF, heq⟩ : ∃ κ₀ : Zd d → ℝ, IsProbKernel κ₀ ∧
      (∀ θ : Fin d → ℝ,
        gridFourier κ₀ θ = (((1 + 4 * τ / h ^ 2 * ∑ j, Real.sin (θ j / 2) ^ 2)⁻¹ : ℝ) : ℂ)) ∧
      ∀ n, κ₀ n - τ * gridLap h κ₀ n = deltaZ n := by
    rcases hτ.eq_or_lt with h0 | hpos
    · subst h0
      refine ⟨deltaZ, isProbKernel_deltaZ, fun θ => ?_, fun n => by ring⟩
      rw [gridFourier_deltaZ]; simp
    · set t := Real.sqrt τ with ht
      have ht0 : 0 < t := Real.sqrt_pos.2 hpos
      have ht2 : t ^ 2 = τ := Real.sq_sqrt hτ
      refine ⟨discreteHelmholtz d h t, isProbKernel_discreteHelmholtz hd hh ht0, fun θ => ?_,
        fun n => ?_⟩
      · rw [gridFourier_discreteHelmholtz hd hh ht0, sq_mul_gridSymbol, ht2]
      · rw [← ht2]; exact discreteHelmholtz_eqn hd hh ht0 n
  have hκeq : κ = κ₀ := kernel_eq_of_gridFourier_eq hκ.2.1 hκ₀.2.1 fun θ => by rw [hκF, hF]
  subst hκeq
  exact heq

/-- **`κ * (u - τΔ_h u) = u`** for a summable `κ` with `κ - τΔ_hκ = δ₀` and a summable `u`. -/
theorem kconv_resolvent_sub_gridLap {κ u : Zd d → ℝ} (hκ : Summable κ) (hu : Summable u)
    {h τ : ℝ} (heq : ∀ n, κ n - τ * gridLap h κ n = deltaZ n) :
    kconv κ (fun n => u n - τ * gridLap h u n) = u := by
  obtain ⟨Cu, hCu⟩ := bounded_of_summable_Z hu
  obtain ⟨Cκ, hCκ⟩ := bounded_of_summable_Z hκ
  have hLu := summable_gridLap hu h
  have hLκ := summable_gridLap hκ h
  have hf : (fun n => u n - τ * gridLap h u n) = fun n => 1 * u n + (-τ) * gridLap h u n := by
    funext n; ring
  have hδ : (fun n => 1 * κ n + (-τ) * gridLap h κ n) = deltaZ := by
    funext n; rw [← heq n]; ring
  have hmove : ∀ n, kconv (gridLap h u) κ n = kconv u (gridLap h κ) n := fun n => by
    rw [kconv_comm, ← gridLap_kconv h hκ hCu n, kconv_comm, gridLap_kconv h hu hCκ n]
  rw [kconv_comm, hf, kconv_add_smul_left hu hLu hκ 1 (-τ)]
  funext n
  rw [hmove n]
  have := congrFun (kconv_add_smul_right hu hκ hLκ 1 (-τ)) n
  rw [← this, hδ, kconv_deltaZ_right]

/-- **`prop:principle-after-decimation`.** On `hℤ^d`, in the indices with `τ/h²`, let
`u := δ₀ + 2·1_{±eⱼ}` and `f := (I - τΔ_h)u`, `d ≥ 1`, `h > 0`, `τ ≥ 0`.
1. Every probability kernel `κ` with the transform of `prop:stage-lemma`(2) has `κ * f = u`.
2. `f(0) = 1 - 2dτ/h²`, so `f(0) < u(0) = 1` when `τ > 0`.
3. For every integer `q ≥ 2`, the origin is a strict maximum of the decimated output `m ↦ u(qm)`
   against the axis neighbours, and for `τ > 0` the decimated pair `(m ↦ u(qm), m ↦ f(qm))` breaks
   the principle's clause at maxima there.
4. Before decimation the origin is no axis maximum of `u`, and the pair `(u, f)` obeys the principle
   on the axis neighbours at every point. -/
theorem principle_after_decimation (hd : 1 ≤ d) {h τ : ℝ} (hh : 0 < h) (hτ : 0 ≤ τ) :
    (∀ κ : Zd d → ℝ, IsProbKernel κ →
      (∀ θ : Fin d → ℝ,
        gridFourier κ θ = (((1 + 4 * τ / h ^ 2 * ∑ j, Real.sin (θ j / 2) ^ 2)⁻¹ : ℝ) : ℂ)) →
      kconv κ (decimationInput d h τ) = decimationOutput d) ∧
    decimationOutput d 0 = 1 ∧ decimationInput d h τ 0 = 1 - 2 * d * τ / h ^ 2 ∧
    (0 < τ → decimationInput d h τ 0 < decimationOutput d 0) ∧
    (∀ q : ℕ, 2 ≤ q →
      (∀ y ∈ axisNbrs d,
        decimationOutput d ((q : ℤ) • y) < decimationOutput d ((q : ℤ) • (0 : Zd d))) ∧
      IsNMax (axisNbrs d) (fun m => decimationOutput d ((q : ℤ) • m)) 0 ∧
      (0 < τ → ¬ (IsNMax (axisNbrs d) (fun m => decimationOutput d ((q : ℤ) • m)) 0 →
        decimationOutput d ((q : ℤ) • (0 : Zd d)) ≤ decimationInput d h τ ((q : ℤ) • 0)))) ∧
    ¬ IsNMax (axisNbrs d) (decimationOutput d) 0 ∧
    (∀ x, (IsNMax (axisNbrs d) (decimationOutput d) x →
        decimationOutput d x ≤ decimationInput d h τ x) ∧
      (IsNMin (axisNbrs d) (decimationOutput d) x →
        decimationInput d h τ x ≤ decimationOutput d x)) := by
  have hconv : ∀ κ : Zd d → ℝ, IsProbKernel κ →
      (∀ θ : Fin d → ℝ,
        gridFourier κ θ = (((1 + 4 * τ / h ^ 2 * ∑ j, Real.sin (θ j / 2) ^ 2)⁻¹ : ℝ) : ℂ)) →
      kconv κ (decimationInput d h τ) = decimationOutput d := fun κ hκ hκF =>
    kconv_resolvent_sub_gridLap hκ.2.1 summable_decimationOutput
      (resolvent_eqn_of_gridFourier hd hh hτ hκ hκF)
  have hf0 := decimationInput_zero (d := d) h τ
  have hlt : 0 < τ → decimationInput d h τ 0 < decimationOutput d 0 := fun hpos => by
    rw [hf0, decimationOutput_zero]
    have : 0 < 2 * (d : ℝ) * τ / h ^ 2 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      positivity
    linarith
  -- the decimated output at the axis neighbours
  have hdec : ∀ q : ℕ, 2 ≤ q → ∀ y ∈ axisNbrs d, decimationOutput d ((q : ℤ) • y) = 0 := by
    intro q hq y hy
    obtain ⟨i, rfl | rfl⟩ := hy
    · refine decimationOutput_of_ne ?_ (smul_zbasis_not_mem_axisNbrs hq i)
      intro h0
      have := congrFun h0 i
      simp [zbasis] at this
      omega
    · rw [smul_neg]
      refine decimationOutput_of_ne ?_ fun hm => smul_zbasis_not_mem_axisNbrs hq i ?_
      · intro h0
        have := congrFun h0 i
        simp [zbasis] at this
        omega
      · simpa using neg_mem_axisNbrs hm
  refine ⟨hconv, decimationOutput_zero, hf0, hlt, fun q hq => ?_, ?_, ?_⟩
  · have hstrict : ∀ y ∈ axisNbrs d,
        decimationOutput d ((q : ℤ) • y) < decimationOutput d ((q : ℤ) • (0 : Zd d)) := by
      intro y hy
      rw [hdec q hq y hy, smul_zero, decimationOutput_zero]
      norm_num
    have hmax : IsNMax (axisNbrs d) (fun m => decimationOutput d ((q : ℤ) • m)) 0 := by
      intro y hy
      simp only [zero_add]
      exact (hstrict y hy).le
    refine ⟨hstrict, hmax, fun hpos hP => ?_⟩
    have := hP hmax
    rw [smul_zero] at this
    exact absurd this (not_le.2 (hlt hpos))
  · intro hmax
    have i : Fin d := ⟨0, by omega⟩
    have := hmax (zbasis i) ⟨i, Or.inl rfl⟩
    rw [zero_add, decimationOutput_of_mem ⟨i, Or.inl rfl⟩, decimationOutput_zero] at this
    norm_num at this
  · intro x
    obtain ⟨⟨κ, hκ, hκF⟩, hall⟩ := stage_lemma_2 hd hh hτ
    have hP := (hall κ hκ hκF).2
    have hb : ∃ C : ℝ, ∀ n, |decimationInput d h τ n| ≤ C :=
      bounded_of_summable_Z ((summable_decimationOutput.sub
        ((summable_gridLap summable_decimationOutput h).mul_left τ)))
    have := hP (decimationInput d h τ) hb x
    rw [hconv κ hκ hκF] at this
    exact this

end Pyramids
