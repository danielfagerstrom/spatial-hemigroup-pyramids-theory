/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Price.GridKnot
import AffineHemigroup.GLPlus
import AffineHemigroup.SimilarityGeneral
import AffineHemigroup.CharFunSubspace
import Mathlib.Analysis.Real.Cardinality

/-!
# `prop:grid-pyramid-not-isotropic`(2): no isotropy, and a finite symmetry group

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:grid-pyramid-not-isotropic`. Wave 3g:
`grid_pyramid_not_isotropic_2` moved here from `PyramidsSkeleton.Ch05Price`, its statement
unchanged.

## The route

* **A symmetry passes to the Lévy measure** (`levy_map_eq_of_push_eq`): A42 at `U = R` gives the
  triplet of `R_*μ`, whose Lévy measure is `R_*ν` (an orthogonal map fixes only `0`); uniqueness
  (A39(ii)) gives `R_*ν = ν`, so `R` maps an atom to an atom of the same mass.
* **No `SO(d)`-invariant kernel**: `ν_t ≠ 0` is carried by the countable `Γ_q` (clause (1)), so
  it has an atom `x ≠ 0`; `SO(d)` is transitive on the sphere through `x` for `d ≥ 2`
  (`exists_isometry_det_pos`), so every point of that sphere is an atom, hence lies in `Γ_q`; but
  the sphere is uncountable (it contains the radial projection of the line `e₀ + ℝe₁`).
* **The finite group**: the atoms of `ν_w` span (`w` is the compound Poisson law of `ν_w`; for
  `η` orthogonal to the span of the atoms `ŵ(η) = 1`, so `w` is carried by that span,
  `charFun_one_on_subspace`); take a basis `B` among them. By clause (1),
  `ν_t ≥ D_{q^{n-1}} ν_w`, so the `q^{n-1}b`, `b ∈ B`, are atoms of `ν_t`. A symmetry maps each to
  a point of the same norm and the same mass, of which there are finitely many (`ν_t` is finite
  off a ball); a linear map is determined by its values on a basis.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## Symmetries and Lévy measures -/

/-- An orthogonal map is injective. -/
theorem lin_injective_of_orth {R : Mat d} (hR : R ∈ orthSet d) : Function.Injective (lin R) := by
  intro x y h
  rw [← lin_transpose_lin_of_orth hR x, h, lin_transpose_lin_of_orth hR y]

/-- **A symmetry of an infinitely divisible law is a symmetry of its Lévy measure** (A42 at
`U = R`, A39(ii)). -/
theorem levy_map_eq_of_push_eq {m : Measure (Rd d)} [IsProbabilityMeasure m]
    (hid : IsInfinitelyDivisible m) {T : LevyTriplet d} (hT : HasTriplet m T) {R : Mat d}
    (hR : R ∈ orthSet d) (hpush : push R m = m) : T.ν.map (lin R) = T.ν := by
  have hmap : m.map (Matrix.toEuclideanLin R) = m := hpush
  obtain ⟨-, -, T', hT', -, hν', -⟩ := cited_A42 m hid T hT R
  rw [hmap] at hT'
  obtain ⟨-, hν, -⟩ := cited_A39_unique m hid _ _ hT hT'
  have h0 : (T.ν.map (Matrix.toEuclideanLin R)) {0} = 0 := by
    rw [Measure.map_apply (Matrix.toEuclideanLin R).continuous_of_finiteDimensional.measurable
      (measurableSet_singleton 0)]
    refine measure_mono_null (fun x hx => ?_) T.ν_zero
    have hx' : lin R x = lin R 0 := by rw [map_zero]; exact hx
    exact lin_injective_of_orth hR hx'
  have hrestr : (T.ν.map (Matrix.toEuclideanLin R)).restrict {0}ᶜ
      = T.ν.map (Matrix.toEuclideanLin R) := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    simpa using h0
  exact ((hν.trans hν').trans hrestr).symm

/-- **A symmetry maps an atom to an atom of the same mass.** -/
theorem atom_map_eq {ν : Measure (Rd d)} {R : Mat d} (hR : R ∈ orthSet d)
    (h : ν.map (lin R) = ν) (x : Rd d) : ν {lin R x} = ν {x} := by
  conv_lhs => rw [← h]
  rw [Measure.map_apply (lin R).continuous.measurable (measurableSet_singleton _)]
  congr 1
  ext y
  simp only [mem_preimage, mem_singleton_iff]
  exact ⟨fun hy => lin_injective_of_orth hR hy, fun hy => hy ▸ rfl⟩

/-- A nonzero measure carried by a countable set has an atom in it. -/
theorem exists_atom_of_countable {ν : Measure (Rd d)} (hν : ν ≠ 0) {S : Set (Rd d)}
    (hS : S.Countable) (hcarr : ν Sᶜ = 0) : ∃ x ∈ S, ν {x} ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hS0 : ν S = 0 := by
    rw [← Set.biUnion_of_singleton S]
    exact (measure_biUnion_null_iff hS).2 hcon
  apply hν
  rw [← Measure.measure_univ_eq_zero, ← union_compl_self S]
  exact measure_union_null hS0 hcarr

/-- An atom of a measure carried by `S` lies in `S`. -/
theorem atom_mem {ν : Measure (Rd d)} {S : Set (Rd d)} (hcarr : ν Sᶜ = 0) {x : Rd d}
    (hx : ν {x} ≠ 0) : x ∈ S := by
  by_contra hxS
  exact hx (measure_mono_null (singleton_subset_iff.2 hxS) hcarr)

/-! ## The sphere -/

/-- **A sphere of positive radius in `ℝ^d`, `d ≥ 2`, is uncountable.** -/
theorem not_countable_sphere (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) :
    ¬ {y : Rd d | ‖y‖ = r}.Countable := by
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set v : ℝ → Rd d := fun s => ebasis i0 + s • ebasis i1 with hv
  have hv0 : ∀ s, v s i0 = 1 := fun s => by simp [hv, ebasis, hi]
  have hv1 : ∀ s, v s i1 = s := fun s => by simp [hv, ebasis, hi.symm]
  have hvne : ∀ s, v s ≠ 0 := fun s h => by
    have := hv0 s
    rw [h] at this
    simp at this
  set f : ℝ → Rd d := fun s => (r / ‖v s‖) • v s with hf
  have hmaps : MapsTo f univ {y : Rd d | ‖y‖ = r} := fun s _ => by
    simp only [hf, mem_setOf_eq, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (div_pos hr (norm_pos_iff.2 (hvne s))),
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 (hvne s))]
  have hinj : InjOn f univ := fun s _ t _ hst => by
    have h0 := congrArg (fun y : Rd d => y i0) hst
    have h1 := congrArg (fun y : Rd d => y i1) hst
    simp only [hf, PiLp.smul_apply, smul_eq_mul, hv0, hv1, mul_one] at h0 h1
    rw [h0] at h1
    have hne : r / ‖v t‖ ≠ 0 := (div_pos hr (norm_pos_iff.2 (hvne t))).ne'
    exact mul_left_cancel₀ hne h1
  exact fun hc => Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hc)

/-- **`SO(d)` is transitive on spheres**, `d ≥ 2`, as matrices: `R ∈ O(d)`, `det R = 1`,
`Rx = y`. -/
theorem exists_SO_map (hd : 2 ≤ d) {x y : Rd d} (h : ‖y‖ = ‖x‖) :
    ∃ R ∈ orthSet d, R.det = 1 ∧ lin R x = y := by
  obtain ⟨e, he, hdet⟩ := exists_isometry_det_pos hd h
  refine ⟨isoMat e, isoMat_mem_orthSet e, ?_, by rw [lin_isoMat]; exact he⟩
  have hpos : 0 < (isoMat e).det := by
    rw [← det_lin, lin_isoMat]
    exact hdet
  have hsq : (isoMat e).det * (isoMat e).det = 1 := by
    have h1 := orth_mul_transpose (isoMat_mem_orthSet e)
    have h2 := congrArg Matrix.det h1
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
  nlinarith

/-! ## Finitely many atoms of a given mass -/

/-- On a set of finite measure, a measure has finitely many atoms of mass at least `p > 0`. -/
theorem finite_atoms {ν : Measure (Rd d)} {U : Set (Rd d)} (hU : ν U ≠ ⊤) {p : ℝ≥0∞}
    (hp : p ≠ 0) : {y | y ∈ U ∧ p ≤ ν {y}}.Finite := by
  by_contra hinf
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hp hU
  obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
  have hle : (N : ℝ≥0∞) * p ≤ ν U := by
    calc (N : ℝ≥0∞) * p = ∑ y ∈ F, p := by rw [Finset.sum_const, nsmul_eq_mul, hFcard]
      _ ≤ ∑ y ∈ F, ν {y} := Finset.sum_le_sum fun y hy => (hFsub hy).2
      _ = ν F := sum_measure_singleton
      _ ≤ ν U := measure_mono fun y hy => (hFsub hy).1
  exact absurd hle (not_le.2 hN)

/-! ## The atoms of the mask span -/

/-- **The atoms of `ν_w` span when the atoms of `w` do**: for `η` orthogonal to the span `V` of the
atoms of `ν_w`, `ŵ(η) = 1`, so `w` is carried by `V`. -/
theorem span_atoms_levy {w : Measure (Rd d)} [IsProbabilityMeasure w] {D : SymLevyData d}
    (hD : IsSymData w D) (hA : D.A = 0) {Γ : Set (Rd d)} (hΓ : Γ.Countable) (hcarr : D.ν Γᶜ = 0)
    (hspan : Submodule.span ℝ {x : Rd d | w {x} ≠ 0} = ⊤) :
    Submodule.span ℝ {x : Rd d | D.ν {x} ≠ 0} = ⊤ := by
  set V := Submodule.span ℝ {x : Rd d | D.ν {x} ≠ 0} with hV
  -- `ν_w` is carried by `V`
  have hνV : D.ν (V : Set (Rd d))ᶜ = 0 := by
    have hsub : (V : Set (Rd d))ᶜ ⊆ Γᶜ ∪ (Γ ∩ (V : Set (Rd d))ᶜ) := fun x hx => by
      by_cases hxΓ : x ∈ Γ
      · exact Or.inr ⟨hxΓ, hx⟩
      · exact Or.inl hxΓ
    refine measure_mono_null hsub (measure_union_null hcarr ?_)
    rw [← Set.biUnion_of_singleton (Γ ∩ (V : Set (Rd d))ᶜ)]
    refine (measure_biUnion_null_iff (hΓ.mono inter_subset_left)).2 fun x hx => ?_
    by_contra hne
    exact hx.2 (Submodule.subset_span hne)
  -- `ŵ = 1` on `Vᗮ`
  have hone : ∀ η ∈ Vᗮ, ‖η‖ < 1 → charFun w η = 1 := by
    intro η hη _
    rw [hD η]
    have hint : ∫ x, (1 - Real.cos ⟪η, x⟫) ∂D.ν = 0 := by
      refine integral_eq_zero_of_ae ?_
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun x hx => ?_) hνV
      intro hxV
      apply hx
      have h0 : ⟪η, x⟫ = 0 := Submodule.inner_left_of_mem_orthogonal hxV hη
      simp [h0]
    simp [SymLevyData.exponent, pairExponent, hA, quad_zero, hint]
  have hcw := (charFun_one_on_subspace w Vᗮ 1 one_pos hone).1
  rw [Submodule.orthogonal_orthogonal] at hcw
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 fun x hx => ?_
  exact atom_mem hcw hx

/-! ## `prop:grid-pyramid-not-isotropic`(2) -/

/-- **`prop:grid-pyramid-not-isotropic`(2), no isotropy.** If `d ≥ 2`, no kernel `μ_t`, `t > 0`,
is invariant under `SO(d)`; if `supp w` spans `ℝ^d`, the symmetry group of every `μ_t`, `t > 0`,
is finite. -/
theorem grid_pyramid_not_isotropic_2 (hd : 2 ≤ d) (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ]
    [IsZLattice ℝ Γ] {q : ℝ} (w : Measure (Rd d)) (hw : IsLatticeMask (Γ : Set (Rd d)) w)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : CarriesLatticeLadder q w μ) :
    (∀ t : ℝ, 0 < t → ¬ IsSORotationInvariant (μ 0 t)) ∧
      (Submodule.span ℝ {x : Rd d | w {x} ≠ 0} = ⊤ →
        ∀ t : ℝ, 0 < t → (symmetryGroup (μ 0 t)).Finite) := by
  haveI := hw.1
  have hd1 : 1 ≤ d := by omega
  have hq0 : 0 < q := by linarith [hμ.1]
  have hΓc := countable_lattice Γ
  obtain ⟨-, Dw, hDw, hA0, -, -, hcar⟩ := lattice_mask_data hd1 Γ hw hμ
  have hΓ0 : Dw.ν (Γ : Set (Rd d))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 sdiff_subset) hcar
  have h1 := grid_pyramid_not_isotropic_1 Γ w hw μ hμ
  refine ⟨fun t ht hrot => ?_, fun hspan t ht => ?_⟩
  · -- no `SO(d)`-invariant kernel
    haveI := hμ.prob le_rfl ht.le
    obtain ⟨hid, -, ν, ⟨⟨T, hT⟩, hall⟩, hne, hcarr⟩ := h1.2.2.2.2.1 t ht
    rw [← hall T hT] at hne hcarr
    obtain ⟨x, -, hx⟩ := exists_atom_of_countable hne h1.1 hcarr
    have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0]; exact T.ν_zero)
    refine not_countable_sphere hd (norm_pos_iff.2 hx0) (h1.1.mono fun y hy => ?_)
    obtain ⟨R, hR, hdet, hRx⟩ := exists_SO_map hd hy
    have hmap := levy_map_eq_of_push_eq hid hT hR (hrot R hR hdet)
    refine atom_mem hcarr ?_
    rw [← hRx, atom_map_eq hR hmap]
    exact hx
  · -- the finite symmetry group
    haveI := hμ.prob le_rfl ht.le
    obtain ⟨hid, T, hT, -, hlo, -⟩ := hμ.between hd1 hw.2.1 hDw hA0 ht
    set c : ℝ := q ^ (dgLevel q t - 1) with hc
    have hc0 : c ≠ 0 := zpow_ne_zero _ hq0.ne'
    have hspanν := span_atoms_levy hDw hA0 hΓc hΓ0 hspan
    obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent ℝ {x : Rd d | Dw.ν {x} ≠ 0}
    rw [hspanν] at hBspan
    haveI : Finite B := (LinearIndependent.setFinite hBli).to_subtype
    -- `c b` is an atom of `ν_t`
    have hatom : ∀ b ∈ B, T.ν {c • b} ≠ 0 := by
      intro b hb hzero
      have hle := Measure.le_iff'.1 ((map_le_knotNu q Dw.ν _).trans hlo) {c • b}
      rw [hzero, Measure.map_apply (measurable_const_smul _) (measurableSet_singleton _)] at hle
      have hpre : (fun x : Rd d => c • x) ⁻¹' {c • b} = {b} := by
        ext y
        simp only [mem_preimage, mem_singleton_iff]
        exact ⟨fun h => smul_right_injective _ hc0 h, fun h => h ▸ rfl⟩
      rw [hpre] at hle
      exact hBsub hb (nonpos_iff_eq_zero.1 hle)
    -- the admissible images of `c b`
    set A : B → Set (Rd d) := fun b =>
      {y | y ∈ {z : Rd d | ‖c • (b : Rd d)‖ / 2 < ‖z‖} ∧ T.ν {c • (b : Rd d)} ≤ T.ν {y}}
      with hA
    have hAfin : ∀ b : B, (A b).Finite := by
      intro b
      have hb0 : c • (b : Rd d) ≠ 0 := fun h0 => hatom b b.2 (by rw [h0]; exact T.ν_zero)
      exact finite_atoms (T.measure_norm_gt_ne_top (by positivity)) (hatom b b.2)
    refine Set.Finite.of_injOn (f := fun R : Mat d => fun b : B => lin R (c • (b : Rd d)))
      (t := Set.pi univ A) (fun R hR => ?_) (fun R hR R' hR' hRR => ?_) (Set.Finite.pi hAfin)
    · -- a symmetry maps `c b` into `A b`
      obtain ⟨hRo, hpush⟩ := hR
      have hmap := levy_map_eq_of_push_eq hid hT hRo hpush
      intro b _
      have hb0 : c • (b : Rd d) ≠ 0 := fun h0 => hatom b b.2 (by rw [h0]; exact T.ν_zero)
      refine ⟨?_, (atom_map_eq hRo hmap _).ge⟩
      simp only [mem_setOf_eq]
      rw [norm_lin_of_orth hRo]
      linarith [norm_pos_iff.2 hb0]
    · -- a linear map is determined on a basis
      apply lin_injective
      refine ContinuousLinearMap.coe_injective (LinearMap.ext_on hBspan fun b hb => ?_)
      have h := congrFun hRR ⟨b, hb⟩
      simp only [map_smul] at h
      exact smul_right_injective _ hc0 h

end Pyramids
