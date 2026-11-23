/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.SurfaceFamily

/-!
# `thm:surface-measure`: from a pair `(Λ, ℬ)` to its family

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:surface-measure`. Wave 3a:
`surface_measure_pair`, `surface_measure_injective`, `surface_measure_exponent` and
`surface_measure_integrable_iff` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in name.
`surface_measure_exponent` no longer takes the hypothesis `1 < q`, and
`surface_measure_integrable_iff` no longer takes `Λ quadrantᶜ = 0`; their proofs do not use them
(2026-11-14, a strengthening).

## The route

* **The pair of a slab.** For a measure `Λ` on the quadrant with (i)'s integrability,
  `(ℬ((0,t]), Λ((0,t] × ·))` is a pair whose exponent is (A.e2) (`surfacePairOf_exponent`). Two
  scales `s < t` with the same exponent would give `ℬ((s,t]) = 0` and `Λ((s,t] × (0,∞)) = 0`
  (`lem:line-exponent-data`(1)), against (iv) (`surfaceExponent_ne`).
* **The path.** (A.e2) on `[1,q]` satisfies (1)–(4) of `thm:annulus-parametrization`
  (`isAnnulusPath_surfaceExponent`): (1) and (2) by the pairs, `lem:line-exponent-data`(3) and
  (iv); (3) by `J_*Λ = Λ` and (ii) (`surfaceExponent_cov`); (4) by dominated convergence, since by
  (iii) no vertical line carries mass of `Λ` and `ℬ` has no atom
  (`continuousAt_surfaceExponent`).
* **The family** is then `thm:annulus-parametrization`'s, and its exponents at every `t > 0` are
  (A.e2), by the same covariance; so its kernels have the data (A.e1).
* **Injectivity**: (A.e1) fixes the exponents, which fix the family (`qFamily_eq_of_lineExponent`).
* **"for some, equivalently every, `t`"**: the slabs grow with `t`, and
  `Λ((0,qt] × ·) = T_qΛ((0,t] × ·)` by the invariance, with
  `∫ (1 ∧ v²) d(T_qϖ) ≤ max(1,q²) ∫ (1 ∧ v²) dϖ`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair IsSymLevyExponent)
open scoped Topology ENNReal

/-! ## Continuity of an integral in its upper limit -/

/-- `t ↦ ∫_{g ≤ t} f dm` is continuous at `t₀` when `{g = t₀}` is `m`-null. -/
theorem continuousAt_integral_indicator_le {α : Type*} [MeasurableSpace α] {m : Measure α}
    {g : α → ℝ} (hg : Measurable g) {f : α → ℝ} (hf : Integrable f m) {t₀ : ℝ}
    (h0 : m (g ⁻¹' {t₀}) = 0) :
    ContinuousAt (fun t => ∫ x, (g ⁻¹' Iic t).indicator f x ∂m) t₀ := by
  refine continuousAt_of_dominated
    (Eventually.of_forall fun t => (hf.indicator (hg measurableSet_Iic)).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ fun x => norm_indicator_le_norm_self f x)
    hf.norm ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
  have hx' : g x ≠ t₀ := hx
  rcases hx'.lt_or_gt with h | h
  · refine (continuousAt_const (y := f x)).congr ?_
    filter_upwards [eventually_gt_nhds h] with t ht
    exact (indicator_of_mem (mem_preimage.2 (mem_Iic.2 ht.le)) f).symm
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [eventually_lt_nhds h] with t ht
    exact (indicator_of_notMem (fun hm : x ∈ g ⁻¹' Iic t => not_le.2 ht (mem_Iic.1 hm)) f).symm

/-! ## The pair of a slab -/

/-- The integral of `1 - cos ωv` against a Lévy measure is finite. -/
theorem SymLevyPair_lintegral_cos_ne_top (P : SymLevyPair) (ω : ℝ) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν ≠ ⊤ :=
  ne_top_of_le_ne_top (P.exponentL_ne_top ω) le_add_self

/-- **The pair `(ℬ((0,t]), Λ((0,t] × ·))`** of a measure on the quadrant. -/
noncomputable def surfacePairOf (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (t : ℝ)
    (hc : Λ quadrantᶜ = 0) (hint : ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(slab Λ 0 t) ≠ ⊤) :
    SymLevyPair where
  a := (B (Ioc 0 t)).toReal
  ν := slab Λ 0 t
  a_nonneg := ENNReal.toReal_nonneg
  ν_folded := slab_Iic_zero hc 0 t
  ν_integrable := hint

/-- **The exponent of the pair is (A.e2).** -/
theorem surfacePairOf_exponent {Λ : Measure (ℝ × ℝ)} (B : Measure ℝ) {t : ℝ}
    (hc : Λ quadrantᶜ = 0) (hint : ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(slab Λ 0 t) ≠ ⊤)
    (ω : ℝ) : (surfacePairOf Λ B t hc hint).exponent ω = surfaceExponent Λ B t ω := by
  have hL : ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂(slab Λ 0 t) ≠ ⊤ :=
    SymLevyPair_lintegral_cos_ne_top (surfacePairOf Λ B t hc hint) ω
  have hm : Measurable fun p : ℝ × ℝ => 1 - Real.cos (ω * p.2) := by fun_prop
  rw [SymLevyPair.exponent, SymLevyPair.exponentL]
  change (ENNReal.ofReal ((B (Ioc 0 t)).toReal * ω ^ 2) +
    ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂(slab Λ 0 t)).toReal = _
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hL,
    ENNReal.toReal_ofReal (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg ω)), surfaceExponent,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => sub_nonneg.2 (Real.cos_le_one _))
      hm.aestronglyMeasurable, ← restrict_Ioc_univ hc, lintegral_slab Λ 0 t (by fun_prop)]

theorem surfaceExponent_of_nonpos (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) {t : ℝ} (ht : t ≤ 0)
    (ω : ℝ) : surfaceExponent Λ B t ω = 0 := by
  simp [surfaceExponent, Ioc_eq_empty (not_lt.2 ht)]

/-- **(A.e2) is covariant under `J`**: `Ψ_{qt}(ω) = Ψ_t(qω)`. -/
theorem surfaceExponent_cov {q : ℝ} (hq0 : 0 < q) {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}
    (hinv : Λ.map (scaleDiag q) = Λ)
    (hB : ∀ t : ℝ, 0 < t → B (Ioc 0 (q * t)) = ENNReal.ofReal (q ^ 2) * B (Ioc 0 t)) {t : ℝ}
    (ht : 0 < t) (ω : ℝ) : surfaceExponent Λ B (q * t) ω = surfaceExponent Λ B t (q * ω) := by
  have hpre : scaleDiag q ⁻¹' (Ioc 0 (q * t) ×ˢ Ioi 0) = Ioc 0 t ×ˢ Ioi 0 := by
    rw [scaleDiag_preimage_prod hq0, zero_div, mul_div_cancel_left₀ t hq0.ne']
    congr 1
    ext v
    simp only [mem_preimage, mem_Ioi]
    exact mul_pos_iff_of_pos_left hq0
  unfold surfaceExponent
  rw [hB t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg q)]
  congr 1
  · ring
  · conv_lhs => rw [← hinv]
    rw [setIntegral_map (measurableSet_Ioc.prod measurableSet_Ioi) (by fun_prop)
      (measurable_scaleDiag q).aemeasurable, hpre]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [scaleDiag]
    ring_nf

/-- **(A.e2) is continuous in `t` at `t₀ > 0`** when `Λ({t₀} × (0,∞)) = 0 = ℬ{t₀}`. -/
theorem continuousAt_surfaceExponent {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}
    (hc : Λ quadrantᶜ = 0) (hint : IsLevyIntegrableSurface Λ)
    (hBfin : ∀ t : ℝ, 0 < t → B (Ioc 0 t) ≠ ⊤) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hline : Λ ({t₀} ×ˢ Ioi 0) = 0) (hB0 : B {t₀} = 0) (ω : ℝ) :
    ContinuousAt (fun t => surfaceExponent Λ B t ω) t₀ := by
  have hT : 0 < t₀ + 1 := by linarith
  set mB := B.restrict (Ioc 0 (t₀ + 1)) with hmB
  set mΛ := Λ.restrict (Ioc 0 (t₀ + 1) ×ˢ Ioi 0) with hmΛ
  haveI : IsFiniteMeasure mB := isFiniteMeasure_restrict.2 (hBfin _ hT)
  have hm : Measurable fun p : ℝ × ℝ => 1 - Real.cos (ω * p.2) := by fun_prop
  have hfint : Integrable (fun p : ℝ × ℝ => 1 - Real.cos (ω * p.2)) mΛ := by
    refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun p => sub_nonneg.2 (Real.cos_le_one _))).2 ?_⟩
    rw [hmΛ, ← restrict_Ioc_univ hc, ← lintegral_slab Λ 0 (t₀ + 1)
      (f := fun x => ENNReal.ofReal (1 - Real.cos (ω * x))) (by fun_prop)]
    exact lt_top_iff_ne_top.2
      (SymLevyPair_lintegral_cos_ne_top (surfacePairOf Λ B _ hc (hint _ hT)) ω)
  have hrep : ∀ t : ℝ, t ≤ t₀ + 1 → surfaceExponent Λ B t ω =
      (∫ y, ((fun y : ℝ => y) ⁻¹' Iic t).indicator (fun _ => (1 : ℝ)) y ∂mB) * ω ^ 2 +
        ∫ p, (Prod.fst ⁻¹' Iic t).indicator (fun p : ℝ × ℝ => 1 - Real.cos (ω * p.2)) p ∂mΛ := by
    intro t ht
    have e1 : Iic t ∩ Ioc 0 (t₀ + 1) = Ioc 0 t := by
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, h2.trans ht⟩
    have e2 : Prod.fst ⁻¹' Iic t ∩ (Ioc 0 (t₀ + 1) ×ˢ Ioi 0) = Ioc 0 t ×ˢ Ioi (0 : ℝ) := by
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_prod, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨h1, ⟨h2, -⟩, h3⟩
        exact ⟨⟨h2, h1⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h2, ⟨h1, h2.trans ht⟩, h3⟩
    rw [show (fun y : ℝ => y) ⁻¹' Iic t = Iic t from rfl, surfaceExponent,
      integral_indicator measurableSet_Iic,
      integral_indicator (measurable_fst measurableSet_Iic), hmB, hmΛ,
      Measure.restrict_restrict measurableSet_Iic,
      Measure.restrict_restrict (measurable_fst measurableSet_Iic), e1, e2, setIntegral_const,
      smul_eq_mul, mul_one, measureReal_def]
  have h1 : ContinuousAt (fun t => ∫ y, ((fun y : ℝ => y) ⁻¹' Iic t).indicator
      (fun _ => (1 : ℝ)) y ∂mB) t₀ :=
    continuousAt_integral_indicator_le measurable_id (integrable_const 1) (by
      rw [preimage_id, hmB, Measure.restrict_apply (measurableSet_singleton t₀)]
      exact measure_mono_null inter_subset_left hB0)
  have h2 : ContinuousAt (fun t => ∫ p, (Prod.fst ⁻¹' Iic t).indicator
      (fun p : ℝ × ℝ => 1 - Real.cos (ω * p.2)) p ∂mΛ) t₀ := by
    refine continuousAt_integral_indicator_le measurable_fst hfint ?_
    rw [hmΛ, Measure.restrict_apply (measurable_fst (measurableSet_singleton t₀))]
    refine measure_mono_null (fun p hp => ?_) hline
    exact ⟨hp.1, hp.2.2⟩
  refine ((h1.mul (continuousAt_const (y := ω ^ 2))).add h2).congr ?_
  filter_upwards [eventually_le_nhds (show t₀ < t₀ + 1 by linarith)] with t ht
  exact (hrep t ht).symm

/-! ## The path of a pair -/

section Pair

variable {q : ℝ} {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}

theorem slab_zero_zero (Λ : Measure (ℝ × ℝ)) : slab Λ 0 0 = 0 := by
  rw [slab, Ioc_self, empty_prod, Measure.restrict_empty, Measure.map_zero]

theorem IsSurfacePair.integrable_nonneg (h : IsSurfacePair q Λ B) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(slab Λ 0 t) ≠ ⊤ := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [slab_zero_zero, lintegral_zero_measure]
    exact ENNReal.zero_ne_top
  · exact h.integrable t ht

theorem IsSurfacePair.B_ne_top (h : IsSurfacePair q Λ B) {t : ℝ} (ht : 0 ≤ t) :
    B (Ioc 0 t) ≠ ⊤ := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [Ioc_self, measure_empty]
    exact ENNReal.zero_ne_top
  · exact h.gaussian.2.1 t ht

theorem IsSurfacePair.B_cov (hq0 : 0 < q) (h : IsSurfacePair q Λ B) {t : ℝ} :
    B (Ioc 0 (q * t)) = ENNReal.ofReal (q ^ 2) * B (Ioc 0 t) := by
  rw [← h.gaussian.2.2 _ measurableSet_Ioc Ioc_subset_Ioi_self, image_mul_left_Ioc hq0, mul_zero]

/-- **Two scales never have the same exponent**, by (iv). -/
theorem surfaceExponent_ne (h : IsSurfacePair q Λ B) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∃ ω : ℝ, surfaceExponent Λ B t ω - surfaceExponent Λ B s ω ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have ht : 0 ≤ t := hs.trans hst.le
  obtain ⟨ha, hν⟩ := line_levy_unique (surfacePairOf Λ B s h.carried (h.integrable_nonneg hs))
    (surfacePairOf Λ B t h.carried (h.integrable_nonneg ht)) fun ω => by
      rw [surfacePairOf_exponent, surfacePairOf_exponent]
      linarith [hcon ω]
  have hBs := h.B_ne_top hs
  have hB : B (Ioc s t) = 0 := by
    have e : B (Ioc 0 t) = B (Ioc 0 s) + B (Ioc s t) := by
      rw [← measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
        Ioc_union_Ioc_eq_Ioc hs hst.le]
    have e2 : B (Ioc 0 s) = B (Ioc 0 t) := (ENNReal.toReal_eq_toReal_iff' hBs (h.B_ne_top ht)).1 ha
    rw [← e2] at e
    exact (ENNReal.add_right_inj hBs).1 (e.symm.trans (add_zero _).symm)
  have hΛ : Λ (Ioc s t ×ˢ Ioi 0) = 0 := by
    have hU : Ioc s t ×ˢ Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc s t ×ˢ Ioi (1 / ((n : ℝ) + 1)) := by
      rw [← prod_iUnion]
      congr 1
      ext v
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hv
        exact exists_nat_one_div_lt hv
      · rintro ⟨n, hn⟩
        exact lt_trans (by positivity) hn
    rw [hU]
    refine measure_iUnion_null fun n => ?_
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have e : Λ (Ioc 0 t ×ˢ Ioi (1 / ((n : ℝ) + 1))) = Λ (Ioc 0 s ×ˢ Ioi (1 / ((n : ℝ) + 1))) +
        Λ (Ioc s t ×ˢ Ioi (1 / ((n : ℝ) + 1))) := by
      rw [← measure_union (Disjoint.set_prod_left (Ioc_disjoint_Ioc_of_le le_rfl) _ _)
        (measurableSet_Ioc.prod measurableSet_Ioi), ← union_prod, Ioc_union_Ioc_eq_Ioc hs hst.le]
    have e2 : Λ (Ioc 0 s ×ˢ Ioi (1 / ((n : ℝ) + 1))) = Λ (Ioc 0 t ×ˢ Ioi (1 / ((n : ℝ) + 1))) := by
      rw [← slab_apply _ _ _ measurableSet_Ioi, ← slab_apply _ _ _ measurableSet_Ioi]
      exact congrArg (fun m : Measure ℝ => m (Ioi (1 / ((n : ℝ) + 1)))) hν
    have hfin : Λ (Ioc 0 s ×ˢ Ioi (1 / ((n : ℝ) + 1))) ≠ ⊤ := by
      rw [← slab_apply _ _ _ measurableSet_Ioi]
      exact SymLevyPair_measure_Ioi_ne_top
        (surfacePairOf Λ B s h.carried (h.integrable_nonneg hs)) hε
    rw [← e2] at e
    exact (ENNReal.add_right_inj hfin).1 (e.symm.trans (add_zero _).symm)
  have hs' : 0 < max s (t / 2) := lt_max_of_lt_right (by linarith)
  have hnd := h.nondeg (max s (t / 2)) t hs' (max_lt hst (by linarith))
  rw [measure_mono_null (Set.prod_mono (Ioc_subset_Ioc_left (le_max_left _ _)) le_rfl) hΛ,
    measure_mono_null (Ioc_subset_Ioc_left (le_max_left _ _)) hB, add_zero] at hnd
  exact lt_irrefl _ hnd

/-- **(A.e2) on `[1,q]` is a path of `thm:annulus-parametrization`.** -/
theorem isAnnulusPath_surfaceExponent (hq : 1 < q) (h : IsSurfacePair q Λ B) :
    IsAnnulusPath q (surfaceExponent Λ B) := by
  have hq0 : 0 < q := by linarith
  have hpair : ∀ t : ℝ, ∀ ht : 0 ≤ t, HasExpData (surfaceExponent Λ B t)
      (surfacePairOf Λ B t h.carried (h.integrable_nonneg ht)) :=
    fun t ht ω => (surfacePairOf_exponent B h.carried _ ω).symm
  refine ⟨fun t ht => ⟨⟨_, hpair t (zero_le_one.trans ht.1)⟩, ?_⟩,
    fun t t' ht htt' _ => ⟨?_, surfaceExponent_ne h (zero_le_one.trans ht) htt'⟩,
    fun ω => ?_, fun ω t ht => ?_⟩
  · obtain ⟨ω, hω⟩ := surfaceExponent_ne h le_rfl (lt_of_lt_of_le one_pos ht.1)
    exact ⟨ω, by rwa [surfaceExponent_of_nonpos _ _ le_rfl, sub_zero] at hω⟩
  · have h0 : 0 ≤ t := zero_le_one.trans ht
    refine (line_exponent_data_3 _ _ _ _ (hpair t h0) (hpair t' (h0.trans htt'.le))).1.2
      ⟨?_, slab_mono Λ htt'.le⟩
    exact ENNReal.toReal_mono (h.B_ne_top (h0.trans htt'.le))
      (measure_mono (Ioc_subset_Ioc_right htt'.le))
  · have h1 := surfaceExponent_cov hq0 h.invariant (fun _ _ => h.B_cov hq0) one_pos ω
    rwa [mul_one] at h1
  · have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
    exact (continuousAt_surfaceExponent h.carried h.integrable (fun s hs => h.B_ne_top hs.le)
      ht0 (h.no_line t ht0).1 (h.no_line t ht0).2 ω).continuousWithinAt

end Pair

/-! ## `thm:surface-measure`, from a pair to a family -/

/-- **`thm:surface-measure`, from a pair to a family.** Every pair with (i)–(iv) gives a family by
(A.e1). -/
theorem surface_measure_pair {q : ℝ} (hq : 1 < q) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (h : IsSurfacePair q Λ B) : ∃ μ : ℝ → ℝ → Measure ℝ, IsQFamily q μ ∧ IsSurfaceDataOf μ Λ B := by
  have hq0 : 0 < q := by linarith
  obtain ⟨⟨μ, hμ⟩, hall⟩ := annulus_parametrization_surjective hq _
    (isAnnulusPath_surfaceExponent hq h)
  have hext := annulusExtend_eq_of_cov hq (surfaceExponent Λ B)
    (fun ω => surfaceExponent_of_nonpos _ _ le_rfl ω) fun t ht ω => by
      rcases ht.eq_or_lt with rfl | ht
      · rw [mul_zero, surfaceExponent_of_nonpos _ _ le_rfl, surfaceExponent_of_nonpos _ _ le_rfl]
      · exact surfaceExponent_cov hq0 h.invariant (fun _ _ => h.B_cov hq0) ht ω
  refine ⟨μ, (hall μ hμ).1, fun t ht =>
    ⟨surfacePairOf Λ B t h.carried (h.integrable t ht), fun ω => ?_, rfl,
      ENNReal.ofReal_toReal (h.gaussian.2.1 t ht)⟩⟩
  obtain ⟨-, hc⟩ := hμ 0 t le_rfl ht.le
  rw [hc ω, hext t ht.le, hext 0 le_rfl, surfaceExponent_of_nonpos _ _ le_rfl, sub_zero,
    surfacePairOf_exponent]

/-- **`thm:surface-measure`, the family is determined by its pair.** -/
theorem surface_measure_injective {q : ℝ} (hq : 1 < q) (μ μ' : ℝ → ℝ → Measure ℝ)
    (hμ : IsQFamily q μ) (hμ' : IsQFamily q μ') (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (h : IsSurfaceDataOf μ Λ B) (h' : IsSurfaceDataOf μ' Λ B) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t := by
  refine qFamily_eq_of_lineExponent hq hμ hμ' fun t ht ω => ?_
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
  obtain ⟨P, hP, hPν, hPa⟩ := h t ht0
  obtain ⟨P', hP', hP'ν, hP'a⟩ := h' t ht0
  rw [lineExponent_eq_of_folded hμ.1 ht0.le hP, lineExponent_eq_of_folded hμ'.1 ht0.le hP']
  have ha : P.a = P'.a :=
    (ENNReal.ofReal_eq_ofReal_iff P.a_nonneg P'.a_nonneg).1 (hPa.trans hP'a.symm)
  unfold SymLevyPair.exponent SymLevyPair.exponentL
  rw [ha, hPν, hP'ν]

/-- **`thm:surface-measure`, "equivalently" (A.e2).** For a pair with (i)–(iv), (A.e1) holds iff
`Ψ_t(ω) = a(t)ω² + ∫_{(0,t] × (0,∞)} (1 - cos ωv) Λ(dy, dv)` for every `t > 0`. The hypothesis
`1 < q` of the skeleton is not used. -/
theorem surface_measure_exponent {q : ℝ} (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsQFamily q μ) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (h : IsSurfacePair q Λ B) :
    IsSurfaceDataOf μ Λ B ↔
      ∀ t : ℝ, 0 < t → ∀ ω : ℝ, lineExponent μ t ω = surfaceExponent Λ B t ω := by
  constructor
  · intro hd t ht ω
    obtain ⟨P, hP, hPν, hPa⟩ := hd t ht
    rw [lineExponent_eq_of_folded hμ.1 ht.le hP,
      ← surfacePairOf_exponent B h.carried (h.integrable t ht)]
    have ha : P.a = (B (Ioc 0 t)).toReal := by rw [← hPa, ENNReal.toReal_ofReal P.a_nonneg]
    unfold SymLevyPair.exponent SymLevyPair.exponentL
    rw [ha, hPν]
    rfl
  · intro he t ht
    refine ⟨surfacePairOf Λ B t h.carried (h.integrable t ht), fun ω => ?_, rfl,
      ENNReal.ofReal_toReal (h.gaussian.2.1 t ht)⟩
    rw [charFun_kernel_eq_exp hμ.1 ht.le, he t ht ω, surfacePairOf_exponent]

/-- `∫ (1 ∧ v²) dΛ((0,qt] × ·) ≤ max(1,q²) ∫ (1 ∧ v²) dΛ((0,t] × ·)` for an invariant `Λ`. -/
theorem lintegral_slab_mul_le {q : ℝ} (hq0 : 0 < q) {Λ : Measure (ℝ × ℝ)}
    (hinv : Λ.map (scaleDiag q) = Λ) (t : ℝ) :
    ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(slab Λ 0 (q * t)) ≤
      ENNReal.ofReal (max 1 (q ^ 2)) * ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(slab Λ 0 t) := by
  have e : slab Λ 0 (q * t) = (slab Λ 0 t).map (fun v => q * v) := by
    conv_lhs => rw [← hinv]
    rw [slab_map_scaleDiag hq0, zero_div, mul_div_cancel_left₀ t hq0.ne']
  rw [e, lintegral_map (by fun_prop) (measurable_const_mul q),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun v => ?_
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left 1 (q ^ 2)))]
  exact ENNReal.ofReal_le_ofReal (ScaleSpace.min_one_sq_mul_le q v)

/-- **`thm:surface-measure`(i), "for some, equivalently every, `t > 0`".** The hypothesis
`Λ quadrantᶜ = 0` of the skeleton is not used. -/
theorem surface_measure_integrable_iff {q : ℝ} (hq : 1 < q) (Λ : Measure (ℝ × ℝ))
    (hinv : Λ.map (scaleDiag q) = Λ) :
    (∃ t : ℝ, 0 < t ∧ ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(slab Λ 0 t) ≠ ⊤) ↔
      IsLevyIntegrableSurface Λ := by
  have hq0 : 0 < q := by linarith
  refine ⟨fun ⟨t₀, ht₀, hfin⟩ t ht => ?_, fun h => ⟨1, one_pos, h 1 one_pos⟩⟩
  have hpow : ∀ n : ℕ,
      ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(slab Λ 0 (q ^ n * t₀)) ≠ ⊤ := by
    intro n
    induction n with
    | zero => simpa using hfin
    | succ n ih =>
      rw [pow_succ, mul_comm (q ^ n) q, mul_assoc]
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ih)
        (lintegral_slab_mul_le hq0 hinv _)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (t / t₀) hq
  exact ne_top_of_le_ne_top (hpow n)
    (lintegral_mono' (slab_mono Λ ((div_lt_iff₀ ht₀).1 hn).le) le_rfl)

end Pyramids
