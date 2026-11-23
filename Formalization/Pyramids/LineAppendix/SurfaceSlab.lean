/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.QCinRepr

/-!
# `thm:surface-measure`: measures on the quadrant and their slabs

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:surface-measure`. Wave 3a. The measure-theoretic
tools of the node, none of which mentions a family:

* **Measures on `(0,∞)`.** One null on `(-∞,0]` and finite on every `(ε,∞)` is σ-finite
  (`sigmaFinite_of_Ioi`); two such that agree, finitely, on every `(0,t]` are equal
  (`measure_ext_of_Ioc_zero`).
* **Slabs.** `slab Λ s t = Λ((s,t] × ·)` evaluates as a product (`slab_apply`), is monotone in `t`
  (`slab_mono`), commutes with restriction (`slab_restrict`) and with the dilation `J_c`
  (`slab_map_scaleDiag`).
* **Uniqueness.** Two measures on the quadrant with the same slabs `Λ((0,t] × ·)`, finite on every
  `(0,t] × (ε,∞)`, are equal (`quadrant_measure_ext`): first on the products `S × A` with `A`
  bounded away from `0`, through their `y`-marginals, then by the π-system of the products
  `S × A` with `A ⊆ (-∞,0] ∪ (ε,∞)`.

The pair of a slab and the exponent (A.e2) are `SurfacePair.lean`'s.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair)
open scoped Topology ENNReal

/-! ## Measures on `(0,∞)` -/

/-- A measure null on `(-∞,0]` and finite on every `(ε,∞)` is σ-finite. -/
theorem sigmaFinite_of_Ioi {m : Measure ℝ} (h0 : m (Iic 0) = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → m (Ioi ε) ≠ ⊤) : SigmaFinite m := by
  refine ⟨⟨⟨fun n : ℕ => Iic 0 ∪ Ioi (1 / ((n : ℝ) + 1)), fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
  · refine lt_top_iff_ne_top.2 (ne_top_of_le_ne_top ?_ (measure_union_le _ _))
    rw [h0, zero_add]
    exact hfin _ (by positivity)
  · refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    rcases le_or_gt x 0 with hx | hx
    · exact ⟨0, Or.inl hx⟩
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, Or.inr hn⟩

/-- The Lévy measure of a pair is σ-finite. -/
theorem SymLevyPair_sigmaFinite (P : SymLevyPair) : SigmaFinite P.ν :=
  sigmaFinite_of_Ioi P.ν_folded fun _ hε => SymLevyPair_measure_Ioi_ne_top P hε

/-- For a measure null on `(-∞,0]`, `m(a,b] = m(max a 0, max b 0]`. -/
theorem measure_Ioc_eq_max {m : Measure ℝ} (h0 : m (Iic 0) = 0) (a b : ℝ) :
    m (Ioc a b) = m (Ioc (max a 0) (max b 0)) := by
  rw [← measure_inter_conull (t := Ioi 0) (by rwa [compl_Ioi])]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff]
  constructor
  · rintro ⟨⟨hax, hxb⟩, hx⟩
    exact ⟨⟨hax, hx⟩, hxb.trans (le_max_left _ _)⟩
  · rintro ⟨⟨hax, hx⟩, hxb⟩
    exact ⟨⟨hax, (le_max_iff.1 hxb).elim id fun h => absurd h (not_le.2 hx)⟩, hx⟩

/-- **Two measures on `(0,∞)` that agree, finitely, on every `(0,t]` are equal.** -/
theorem measure_ext_of_Ioc_zero {m m' : Measure ℝ} (h0 : m (Iic 0) = 0) (h0' : m' (Iic 0) = 0)
    (hfin : ∀ t : ℝ, 0 < t → m (Ioc 0 t) ≠ ⊤)
    (h : ∀ t : ℝ, 0 < t → m (Ioc 0 t) = m' (Ioc 0 t)) : m = m' := by
  have h' : ∀ t : ℝ, 0 ≤ t → m (Ioc 0 t) = m' (Ioc 0 t) := by
    intro t ht
    rcases ht.eq_or_lt with rfl | ht
    · simp
    · exact h t ht
  have hfin' : ∀ t : ℝ, 0 ≤ t → m (Ioc 0 t) ≠ ⊤ := by
    intro t ht
    rcases ht.eq_or_lt with rfl | ht
    · simp
    · exact hfin t ht
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → m (Ioc a b) = m' (Ioc a b) := by
    intro a b ha hab
    have e : ∀ μ : Measure ℝ, μ (Ioc 0 b) = μ (Ioc 0 a) + μ (Ioc a b) := fun μ => by
      rw [← measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
        Ioc_union_Ioc_eq_Ioc ha hab]
    have e1 := e m
    have e2 := e m'
    rw [h' b (ha.trans hab), h' a ha] at e1
    exact (ENNReal.add_right_inj (by rw [← h' a ha]; exact hfin' a ha)).1 (e1.symm.trans e2)
  refine Measure.ext_of_Ioc' m m' (fun a b _ => ?_) (fun a b hab => ?_)
  · rw [measure_Ioc_eq_max h0]
    refine ne_top_of_le_ne_top (hfin' _ (le_max_right b 0)) (measure_mono ?_)
    exact Ioc_subset_Ioc_left (le_max_right a 0)
  · rw [measure_Ioc_eq_max h0, measure_Ioc_eq_max h0']
    exact key _ _ (le_max_right a 0) (max_le_max hab.le le_rfl)

/-! ## Slabs -/

theorem measurable_scaleDiag (c : ℝ) : Measurable (scaleDiag c) :=
  (measurable_fst.const_mul c).prodMk (measurable_snd.const_mul c)

/-- `Λ((s,t] × A)`. -/
theorem slab_apply (Λ : Measure (ℝ × ℝ)) (s t : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    slab Λ s t A = Λ (Ioc s t ×ˢ A) := by
  rw [slab, Measure.map_apply measurable_snd hA, Measure.restrict_apply (measurable_snd hA)]
  congr 1
  ext p
  simp [and_comm]

theorem lintegral_slab (Λ : Measure (ℝ × ℝ)) (s t : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ v, f v ∂(slab Λ s t) = ∫⁻ p in Ioc s t ×ˢ univ, f p.2 ∂Λ := by
  rw [slab, lintegral_map hf measurable_snd]

/-- The slabs grow with `t`. -/
theorem slab_mono (Λ : Measure (ℝ × ℝ)) {s t t' : ℝ} (h : t ≤ t') : slab Λ s t ≤ slab Λ s t' :=
  Measure.map_mono (Measure.restrict_mono (prod_mono (Ioc_subset_Ioc_right h) le_rfl) le_rfl)
    measurable_snd

/-- A slab of a measure restricted to `(0,T] × ℝ`. -/
theorem slab_restrict (Λ : Measure (ℝ × ℝ)) (t T : ℝ) :
    slab (Λ.restrict (Ioc 0 T ×ˢ univ)) 0 t = slab Λ 0 (min t T) := by
  rw [slab, slab, Measure.restrict_restrict (measurableSet_Ioc.prod MeasurableSet.univ),
    prod_inter_prod, Ioc_inter_Ioc, inter_univ, max_self]

/-- `J_c^{-1}((s,t] × A) = (s/c, t/c] × c^{-1}A`. -/
theorem scaleDiag_preimage_prod {c : ℝ} (hc : 0 < c) (s t : ℝ) (A : Set ℝ) :
    scaleDiag c ⁻¹' (Ioc s t ×ˢ A) = Ioc (s / c) (t / c) ×ˢ ((fun v => c * v) ⁻¹' A) := by
  ext ⟨y, v⟩
  simp only [scaleDiag, mem_preimage, mem_prod, mem_Ioc]
  rw [div_lt_iff₀ hc, le_div_iff₀ hc, mul_comm y c]

/-- **The slabs of `J_c Λ`**: `(J_c Λ)((s,t] × ·) = T_c Λ((s/c,t/c] × ·)`. -/
theorem slab_map_scaleDiag {c : ℝ} (hc : 0 < c) (Λ : Measure (ℝ × ℝ)) (s t : ℝ) :
    slab (Λ.map (scaleDiag c)) s t = (slab Λ (s / c) (t / c)).map (fun v => c * v) := by
  ext A hA
  rw [slab_apply _ _ _ hA, Measure.map_apply (measurable_scaleDiag c) (measurableSet_Ioc.prod hA),
    Measure.map_apply (measurable_const_mul c) hA,
    slab_apply _ _ _ (measurable_const_mul c hA), scaleDiag_preimage_prod hc]

/-- `J_c` preserves the quadrant. -/
theorem scaleDiag_preimage_quadrant {c : ℝ} (hc : 0 < c) :
    scaleDiag c ⁻¹' quadrant = quadrant := by
  ext ⟨y, v⟩
  simp only [scaleDiag, quadrant, mem_preimage, mem_prod, mem_Ioi]
  rw [mul_pos_iff_of_pos_left hc, mul_pos_iff_of_pos_left hc]

/-- The slab of a measure on the quadrant is null on `(-∞,0]`. -/
theorem slab_Iic_zero {Λ : Measure (ℝ × ℝ)} (hc : Λ quadrantᶜ = 0) (s t : ℝ) :
    slab Λ s t (Iic 0) = 0 := by
  rw [slab_apply _ _ _ measurableSet_Iic]
  refine measure_mono_null (fun p hp => ?_) hc
  simp only [quadrant, mem_compl_iff, mem_prod, mem_Ioi, not_and_or, not_lt]
  exact Or.inr hp.2

/-- On the quadrant, `Λ((s,t] × ℝ)` restricts to `(s,t] × (0,∞)`. -/
theorem restrict_Ioc_univ {Λ : Measure (ℝ × ℝ)} (hc : Λ quadrantᶜ = 0) (s t : ℝ) :
    Λ.restrict (Ioc s t ×ˢ univ) = Λ.restrict (Ioc s t ×ˢ Ioi 0) := by
  refine Measure.restrict_congr_set (ae_eq_set.2 ⟨measure_mono_null (fun p hp => ?_) hc, ?_⟩)
  · simp only [Set.mem_sdiff, mem_prod, mem_univ, mem_Ioi, and_true, not_and, not_lt] at hp
    simp only [quadrant, mem_compl_iff, mem_prod, mem_Ioi, not_and_or, not_lt]
    exact Or.inr (hp.2 hp.1)
  · rw [sdiff_eq_empty.2 (prod_mono le_rfl (subset_univ _)), measure_empty]

/-! ## Uniqueness on the quadrant -/

/-- On the quadrant, `Λ(S × A) = Λ(S × (A ∩ (ε,∞)))` when `A ⊆ (-∞,0] ∪ (ε,∞)`. -/
theorem measure_prod_inter_Ioi {Λ : Measure (ℝ × ℝ)} (hc : Λ quadrantᶜ = 0) (S : Set ℝ)
    {A : Set ℝ} {ε : ℝ} (hε : 0 < ε) (hA : A ⊆ Iic 0 ∪ Ioi ε) :
    Λ (S ×ˢ A) = Λ (S ×ˢ (A ∩ Ioi ε)) := by
  rw [← measure_inter_conull (t := univ ×ˢ Ioi 0) (measure_mono_null (fun p hp => ?_) hc),
    prod_inter_prod, inter_univ]
  · congr 2
    ext x
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · rintro ⟨hx, hx0⟩
      refine ⟨hx, (hA hx).elim (fun h => absurd (mem_Iic.1 h) (not_le.2 hx0)) id⟩
    · rintro ⟨hx, hxε⟩
      exact ⟨hx, hε.trans hxε⟩
  · simp only [mem_compl_iff, mem_prod, mem_univ, mem_Ioi, true_and] at hp
    simp only [quadrant, mem_compl_iff, mem_prod, mem_Ioi, not_and_or]
    exact Or.inr hp

/-- **A measure on the quadrant is determined by its slabs** `Λ((0,t] × ·)`, when these are finite
on every `(ε,∞)`. -/
theorem quadrant_measure_ext {Λ Λ' : Measure (ℝ × ℝ)} (hc : Λ quadrantᶜ = 0)
    (hc' : Λ' quadrantᶜ = 0) (hfin : ∀ t : ℝ, 0 < t → ∀ ε : ℝ, 0 < ε → slab Λ 0 t (Ioi ε) ≠ ⊤)
    (h : ∀ t : ℝ, 0 < t → slab Λ 0 t = slab Λ' 0 t) : Λ = Λ' := by
  -- the products `S × A` with `A ⊆ (ε,∞)`, through the `y`-marginals
  have hprod : ∀ ε : ℝ, 0 < ε → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioi ε →
      ∀ S : Set ℝ, MeasurableSet S → Λ (S ×ˢ A) = Λ' (S ×ˢ A) := by
    intro ε hε A hA hAε S hS
    set mA : Measure (ℝ × ℝ) → Measure ℝ := fun μ => (μ.restrict (univ ×ˢ A)).map Prod.fst
      with hmA
    have happ : ∀ μ : Measure (ℝ × ℝ), ∀ S : Set ℝ, MeasurableSet S → mA μ S = μ (S ×ˢ A) := by
      intro μ S hS
      rw [hmA, Measure.map_apply measurable_fst hS,
        Measure.restrict_apply (measurable_fst hS)]
      congr 1
      ext p
      simp
    have hnull : ∀ μ : Measure (ℝ × ℝ), μ quadrantᶜ = 0 → mA μ (Iic 0) = 0 := by
      intro μ hμ
      rw [happ μ _ measurableSet_Iic]
      refine measure_mono_null (fun p hp => ?_) hμ
      simp only [quadrant, mem_compl_iff, mem_prod, mem_Ioi, not_and_or, not_lt]
      exact Or.inl hp.1
    have hext : mA Λ = mA Λ' := by
      refine measure_ext_of_Ioc_zero (hnull Λ hc) (hnull Λ' hc') (fun t ht => ?_) (fun t ht => ?_)
      · rw [happ Λ _ measurableSet_Ioc, ← slab_apply _ _ _ hA]
        exact ne_top_of_le_ne_top (hfin t ht ε hε) (measure_mono hAε)
      · rw [happ Λ _ measurableSet_Ioc, happ Λ' _ measurableSet_Ioc, ← slab_apply _ _ _ hA,
          ← slab_apply _ _ _ hA, h t ht]
    rw [← happ Λ S hS, ← happ Λ' S hS, hext]
  -- the π-system
  set C : Set (Set (ℝ × ℝ)) := {E | ∃ S A : Set ℝ, MeasurableSet S ∧ MeasurableSet A ∧
    (∃ ε : ℝ, 0 < ε ∧ A ⊆ Iic 0 ∪ Ioi ε) ∧ E = S ×ˢ A} with hC
  have hCeq : ∀ E ∈ C, Λ E = Λ' E := by
    rintro _ ⟨S, A, hS, hA, ⟨ε, hε, hAε⟩, rfl⟩
    rw [measure_prod_inter_Ioi hc S hε hAε, measure_prod_inter_Ioi hc' S hε hAε]
    exact hprod ε hε _ (hA.inter measurableSet_Ioi) inter_subset_right S hS
  have hpi : IsPiSystem C := by
    rintro _ ⟨S, A, hS, hA, ⟨ε, hε, hAε⟩, rfl⟩ _ ⟨S', A', hS', hA', -, rfl⟩ -
    exact ⟨S ∩ S', A ∩ A', hS.inter hS', hA.inter hA',
      ⟨ε, hε, inter_subset_left.trans hAε⟩, prod_inter_prod⟩
  have hgen : (inferInstance : MeasurableSpace (ℝ × ℝ)) = MeasurableSpace.generateFrom C := by
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
    · rw [← generateFrom_prod]
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨S, (hS : MeasurableSet S), A, (hA : MeasurableSet A), rfl⟩
      have hsplit : S ×ˢ A = S ×ˢ (A ∩ Iic 0) ∪ ⋃ n : ℕ, S ×ˢ (A ∩ Ioi (1 / ((n : ℝ) + 1))) := by
        rw [← prod_iUnion, ← prod_union, ← inter_iUnion, ← inter_union_distrib_left]
        congr 1
        refine (inter_eq_left.2 fun x _ => ?_).symm
        rcases le_or_gt x 0 with hx | hx
        · exact Or.inl hx
        · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
          exact Or.inr (mem_iUnion.2 ⟨n, hn⟩)
      change MeasurableSet[MeasurableSpace.generateFrom C] (S ×ˢ A)
      rw [hsplit]
      refine MeasurableSet.union (MeasurableSpace.measurableSet_generateFrom
        ⟨S, _, hS, hA.inter measurableSet_Iic, ⟨1, one_pos, fun x hx => Or.inl hx.2⟩, rfl⟩)
        (MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom
          ⟨S, _, hS, hA.inter measurableSet_Ioi, ⟨_, by positivity, fun x hx => Or.inr hx.2⟩,
            rfl⟩)
    · rintro _ ⟨S, A, hS, hA, -, rfl⟩
      exact hS.prod hA
  -- the cover
  set Bn : ℕ → Set (ℝ × ℝ) := fun n =>
    Ioc (-(n : ℝ)) n ×ˢ (Iic 0 ∪ Ioi (1 / ((n : ℝ) + 1))) with hBn
  refine Measure.ext_of_generateFrom_of_iUnion C Bn hgen hpi ?_ (fun n => ?_) (fun n => ?_) hCeq
  · refine eq_univ_of_forall fun ⟨y, v⟩ => mem_iUnion.2 ?_
    obtain ⟨N1, hN1⟩ := exists_nat_gt |y|
    rcases le_or_gt v 0 with hv | hv
    · refine ⟨N1, ⟨⟨?_, ?_⟩, Or.inl hv⟩⟩
      · linarith [neg_abs_le y]
      · linarith [le_abs_self y]
    · obtain ⟨N2, hN2⟩ := exists_nat_one_div_lt hv
      refine ⟨N1 + N2, ⟨⟨?_, ?_⟩, Or.inr ?_⟩⟩
      · push_cast
        linarith [neg_abs_le y, (Nat.cast_nonneg N2 : (0 : ℝ) ≤ N2)]
      · push_cast
        linarith [le_abs_self y, (Nat.cast_nonneg N2 : (0 : ℝ) ≤ N2)]
      · refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN2
        push_cast
        linarith [(Nat.cast_nonneg N1 : (0 : ℝ) ≤ N1)]
  · exact ⟨_, _, measurableSet_Ioc, measurableSet_Iic.union measurableSet_Ioi,
      ⟨_, by positivity, le_rfl⟩, rfl⟩
  · rw [hBn, measure_prod_inter_Ioi hc _ (by positivity) le_rfl,
      inter_eq_right.2 subset_union_right]
    refine ne_top_of_le_ne_top
      (hfin ((n : ℝ) + 1) (by positivity) (1 / ((n : ℝ) + 1)) (by positivity)) ?_
    rw [slab_apply _ _ _ measurableSet_Ioi]
    calc Λ (Ioc (-(n : ℝ)) n ×ˢ Ioi (1 / ((n : ℝ) + 1)))
        ≤ Λ (Iic 0 ×ˢ Ioi (1 / ((n : ℝ) + 1)) ∪ Ioc 0 ((n : ℝ) + 1) ×ˢ Ioi (1 / ((n : ℝ) + 1))) :=
          measure_mono fun p hp => by
            rcases le_or_gt p.1 0 with h0 | h0
            · exact Or.inl ⟨h0, hp.2⟩
            · exact Or.inr ⟨⟨h0, by linarith [hp.1.2]⟩, hp.2⟩
      _ ≤ Λ (Iic 0 ×ˢ Ioi (1 / ((n : ℝ) + 1))) +
          Λ (Ioc 0 ((n : ℝ) + 1) ×ˢ Ioi (1 / ((n : ℝ) + 1))) := measure_union_le _ _
      _ = Λ (Ioc 0 ((n : ℝ) + 1) ×ˢ Ioi (1 / ((n : ℝ) + 1))) := by
          rw [measure_mono_null (fun p hp => ?_) hc, zero_add]
          simp only [quadrant, mem_compl_iff, mem_prod, mem_Ioi, not_and_or, not_lt]
          exact Or.inl hp.1

end Pyramids
