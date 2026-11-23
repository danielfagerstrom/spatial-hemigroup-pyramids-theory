/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Pyramid
import Pyramids.Cited.A42
import Pyramids.Cited.A48
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# `lem:lattice-infinitely-divisible`: lattice-carried infinitely divisible laws in `ℝ^d`

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `lem:lattice-infinitely-divisible`, chapter 3.
Wave 2b: the declaration moved here from `PyramidsSkeleton.Ch03Pyramid`, its statement unchanged.

## The route

Not through `ℤ^d` and the matrix `M⁻¹`, as printed, but directly through the coordinates of a basis
of `Γ`. Let `b_1, …, b_d` be a basis of the lattice and `c_i` the coordinate functionals of the
basis of `ℝ^d` it is, so that `x ∈ Γ` iff every `c_i(x)` is an integer. Write `c_i(x) = ⟨v_i, x⟩`.

* A42 (`cited_A42`) at the `1 × d` matrix `v_iᵀ` gives the triplet of the image `(c_i)_*η`:
  Gaussian part `v_iᵀAv_i`, Lévy measure the image of `ν` off `0`. The image is carried by `ℤ`, so
  A48 (`cited_A48`) gives `v_iᵀAv_i = 0` and a Lévy measure carried by `ℤ`, finite by
  `isFiniteMeasure_levy_of_int` (`cited_A48_finite`).
* `A` is positive semidefinite, so `v_iᵀAv_i = 0` gives `Av_i = 0`; the `v_i` span `ℝ^d` (they are
  the rows of the inverse of the matrix of the basis), so `A = 0`.
* `ν{c_i(x) ∉ ℤ} = 0` for every `i`, so `ν` is carried by `Γ`, and by `Γ ∖ {0}` since `ν{0} = 0`.
* Every `x ≠ 0` has some `c_i(x) ≠ 0`, so `ν(ℝ^d ∖ {0}) ≤ ∑_i ν{c_i(x) ≠ 0} < ∞`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set

variable {d : ℕ}

/-- The coordinate `y₀` of `ℝ¹` is measurable, and the set of `y` with `y₀ ∉ ℤ` is measurable. -/
theorem measurableSet_notInt : MeasurableSet {y : Rd 1 | ¬ ∃ k : ℤ, y 0 = k} := by
  have h : {y : Rd 1 | ¬ ∃ k : ℤ, y 0 = k} =
      (fun y : Rd 1 => y 0) ⁻¹' (Set.range (Int.cast : ℤ → ℝ))ᶜ := by
    ext y
    simp [eq_comm]
  rw [h]
  exact (measurable_pi_apply (0 : Fin 1)).comp (PiLp.continuous_ofLp 2 _).measurable
    (Set.countable_range _).measurableSet.compl

/-- **`lem:lattice-infinitely-divisible`.** An infinitely divisible law with generating triplet
`(A, ν, β)` carried by a full-rank lattice `Γ` has `A = 0`, and `ν` is finite and carried by
`Γ ∖ {0}`. -/
theorem lattice_infinitely_divisible (η : Measure (Rd d)) [IsProbabilityMeasure η]
    (hη : IsInfinitelyDivisible η) (T : LevyTriplet d) (hT : HasTriplet η T)
    (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (hcarr : η (Γ : Set (Rd d))ᶜ = 0) :
    T.A = 0 ∧ IsFiniteMeasure T.ν ∧ T.ν ((Γ : Set (Rd d)) \ {0})ᶜ = 0 := by
  classical
  haveI := ZLattice.module_free ℝ Γ
  haveI := ZLattice.module_finite ℝ Γ
  set b := Module.Free.chooseBasis ℤ Γ with hb
  set B := Module.Basis.ofZLatticeBasis ℝ Γ b with hB
  -- membership in `Γ` through the coordinates
  have hmem : ∀ x : Rd d, x ∈ Γ ↔ ∀ i, ∃ k : ℤ, B.coord i x = k := by
    intro x
    have h1 : x ∈ Γ ↔ x ∈ Submodule.span ℤ (Set.range B) := by
      rw [hB, Module.Basis.ofZLatticeBasis_span]
    rw [h1, Module.Basis.mem_span_iff_repr_mem ℤ B x]
    refine forall_congr' fun i => ?_
    simp only [Set.mem_range, Module.Basis.coord_apply, eq_intCast, eq_comm]
  -- the `1 × d` matrices of the coordinates
  set U : _ → Matrix (Fin 1) (Fin d) ℝ := fun i _ j => B.coord i (EuclideanSpace.single j 1)
    with hU
  have hsumx : ∀ x : Rd d, ∑ j, x j • EuclideanSpace.single j (1 : ℝ) = x := by
    intro x
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
    simpa using h
  have hUx : ∀ i (x : Rd d), (Matrix.toEuclideanLin (U i) x) 0 = B.coord i x := by
    intro i x
    rw [Matrix.toLpLin_apply]
    simp only [Matrix.mulVec, dotProduct, hU]
    conv_rhs => rw [← hsumx x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hUzero : ∀ i (x : Rd d), Matrix.toEuclideanLin (U i) x = 0 ↔ B.coord i x = 0 := by
    intro i x
    rw [← hUx]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      ext j
      rw [Subsingleton.elim j 0, h]
      rfl
  -- what A42 and A48 give at each coordinate
  have hcoord : ∀ i, (U i * T.A * (U i).transpose) 0 0 = 0 ∧
      T.ν {x | ¬ ∃ k : ℤ, B.coord i x = k} = 0 ∧ T.ν {x | B.coord i x ≠ 0} ≠ ⊤ := by
    intro i
    set L := Matrix.toEuclideanLin (U i) with hL
    have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
    haveI : IsProbabilityMeasure (η.map L) := Measure.isProbabilityMeasure_map hLm.aemeasurable
    have hpre : L ⁻¹' {y : Rd 1 | ¬ ∃ k : ℤ, y 0 = k} = {x | ¬ ∃ k : ℤ, B.coord i x = k} := by
      ext x
      simp only [mem_preimage, mem_setOf_eq, hL, hUx]
    have hcarrU : (η.map L) {y : Rd 1 | ¬ ∃ k : ℤ, y 0 = k} = 0 := by
      rw [Measure.map_apply hLm measurableSet_notInt, hpre]
      refine measure_mono_null ?_ hcarr
      intro x hx hxΓ
      exact hx ((hmem x).1 hxΓ i)
    obtain ⟨hidU, -, T', hT', hA', hν', -⟩ := cited_A42 η hη T hT (U i)
    obtain ⟨hA0, hνZ, hfin⟩ := cited_A48_finite (η.map L) hidU T' hT' hcarrU
    refine ⟨by rw [← hA', hA0]; rfl, ?_, ?_⟩
    · have hsub : {y : Rd 1 | ¬ ∃ k : ℤ, y 0 = k} ∩ {0}ᶜ = {y : Rd 1 | ¬ ∃ k : ℤ, y 0 = k} := by
        refine inter_eq_left.2 fun y hy h0 => hy ⟨0, ?_⟩
        rw [mem_singleton_iff.1 h0]
        simp
      have h1 : (T.ν.map L) {y : Rd 1 | ¬ ∃ k : ℤ, y 0 = k} = 0 := by
        rw [hν', Measure.restrict_apply' (measurableSet_singleton 0).compl, hsub] at hνZ
        exact hνZ
      have h2 := Measure.le_map_apply (μ := T.ν) hLm.aemeasurable
        {y : Rd 1 | ¬ ∃ k : ℤ, y 0 = k}
      rw [h1, hpre] at h2
      exact nonpos_iff_eq_zero.1 h2
    · have h1 : (T.ν.map L) {0}ᶜ ≠ ⊤ := by
        have h2 := measure_ne_top T'.ν univ
        rwa [hν', Measure.restrict_apply_univ] at h2
      have hpre0 : L ⁻¹' {0}ᶜ = {x | B.coord i x ≠ 0} := by
        ext x
        simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, mem_setOf_eq, hL, hUzero]
      rw [← hpre0]
      exact ne_top_of_le_ne_top h1 (Measure.le_map_apply hLm.aemeasurable _)
  refine ⟨?_, ?_, ?_⟩
  · -- `A = 0`
    have hPSD := T.A_posSemidef
    set v : _ → Fin d → ℝ := fun i j => U i 0 j with hv
    have hAv : ∀ i, T.A.mulVec (v i) = 0 := by
      intro i
      refine (hPSD.dotProduct_mulVec_zero_iff (v i)).1 ?_
      have h := (hcoord i).1
      rw [← h]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, hv,
        Finset.mul_sum, Finset.sum_mul, star_trivial]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    -- the unit vectors are combinations of the `v i`
    have hsingle : ∀ k : Fin d, (Pi.single k 1 : Fin d → ℝ) = ∑ i, (B i) k • v i := by
      intro k
      funext m
      have h := congrArg (fun x : Rd d => x k) (B.sum_repr (EuclideanSpace.single m (1 : ℝ)))
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        PiLp.single_apply] at h
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, hv, hU, Pi.single_apply]
      rw [show (if m = k then (1 : ℝ) else 0) = if k = m then 1 else 0 from by
        by_cases hmk : m = k
        · simp [hmk]
        · simp [hmk, Ne.symm hmk]]
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Module.Basis.coord_apply, mul_comm]
    ext j k
    have h := congrFun (congrArg T.A.mulVec (hsingle k)) j
    rw [Matrix.mulVec_sum] at h
    simp only [Matrix.mulVec_smul, hAv, smul_zero, Finset.sum_const_zero] at h
    rw [Matrix.mulVec_single_one] at h
    simpa using h
  · -- `ν` is finite
    refine ⟨?_⟩
    have hcover : (univ : Set (Rd d)) ⊆ {0} ∪ ⋃ i, {x | B.coord i x ≠ 0} := by
      intro x _
      by_cases hx : x = 0
      · exact Or.inl hx
      · right
        by_contra hall
        simp only [mem_iUnion, mem_setOf_eq, not_exists, not_not] at hall
        exact hx (B.ext_elem fun i => by simpa [Module.Basis.coord_apply] using hall i)
    calc T.ν univ ≤ T.ν ({0} ∪ ⋃ i, {x | B.coord i x ≠ 0}) := measure_mono hcover
      _ ≤ T.ν {0} + ∑ i, T.ν {x | B.coord i x ≠ 0} :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
      _ < ⊤ := by
          rw [T.ν_zero, zero_add]
          exact ENNReal.sum_lt_top.2 fun i _ => lt_top_iff_ne_top.2 (hcoord i).2.2
  · -- `ν` is carried by `Γ ∖ {0}`
    have hcover : ((Γ : Set (Rd d)) \ {0})ᶜ ⊆ {0} ∪ ⋃ i, {x | ¬ ∃ k : ℤ, B.coord i x = k} := by
      intro x hx
      by_cases h0 : x = 0
      · exact Or.inl h0
      · right
        have hxΓ : x ∉ Γ := fun hxΓ => hx ⟨hxΓ, h0⟩
        rw [hmem] at hxΓ
        push Not at hxΓ
        obtain ⟨i, hi⟩ := hxΓ
        exact mem_iUnion.2 ⟨i, fun ⟨k, hk⟩ => hi k hk⟩
    refine measure_mono_null hcover (measure_union_null T.ν_zero ?_)
    exact measure_iUnion_null fun i => (hcoord i).2.1

end Pyramids
