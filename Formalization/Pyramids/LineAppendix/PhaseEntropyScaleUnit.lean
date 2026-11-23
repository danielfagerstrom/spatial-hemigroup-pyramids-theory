/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.LadderBound

/-!
# `prop:phase-entropy-scale-unit`: the phase entropy does not see the scale unit

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:phase-entropy-scale-unit`. New at pass 6
(2026-11-22): the claim the paragraph after `def:phase-entropy` made in prose, stated and proved.

## The route

* **The family.** Relabelling the scales by `t ↦ ct`, `c > 0`, gives the family
  `μ'_{s,t} = μ_{s/c,t/c}`; it is again `q^ℤ`-covariant with `S_q t = qt`
  (`isQFamily_scaleUnit`), since `q(s/c) = (qs)/c`.
* **Its pair** is `((y, v) ↦ (cy, v))_* Λ` and `(y ↦ cy)_* ℬ`: the slabs are
  `Λ'((0,t] × ·) = Λ((0,t/c] × ·)` (`slab_map_scaleUnitMap`), and (i)–(iv) carry over
  (`isSurfacePair_scaleUnit`, `isSurfaceDataOf_scaleUnit`).
* **Its cylinder measure** is the image of `σ` under `(θ, r) ↦ ([cθ], r/c)`
  (`cylMeasure_map_scaleUnitMap`). The map `(y, v) ↦ (cy, v)` is the diagonal dilation `J_c`
  after `(y, v) ↦ (y, v/c)`; the second commutes with the orbit points, so it maps `Λ_σ` to
  `Λ_{σ'}` with `σ'` the image of `σ` under `(θ, r) ↦ (θ, r/c)`, and the cylinder measure of a
  dilated mixture is the rotated cylinder measure (`cylMeasure_map_scaleDiag`).
* **Its phase entropy.** The fibres `π'_r := (rot_c)_* π_{cr}` disintegrate the image, whose
  `r`-marginal is `ρ̃` pushed forward by `r ↦ r/c` (`isPhaseDisintegration_scaleUnit`); the
  rotation does not change the relative entropy against `η` (`klDiv_rotatedFibre`), and the
  substitution `r ↦ r/c` does not change the integral (`phaseEntropy_scaleUnit`). Any other
  disintegration agrees with this one almost everywhere (`phaseDisintegration_ae_eq`).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter ProbabilityTheory InformationTheory
open scoped ENNReal

/-! ## The change of scale unit on the surface -/

/-- **`(y, v) ↦ (cy, v)`**: the change of the scale unit `t ↦ ct` moves the scales and keeps the
displacements. -/
def scaleUnitMap (c : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (c * x.1, x.2)

theorem measurable_scaleUnitMap (c : ℝ) : Measurable (scaleUnitMap c) := by
  unfold scaleUnitMap
  fun_prop

theorem preimage_mul_left_Ioc_div {c : ℝ} (hc : 0 < c) (s t : ℝ) :
    (fun y : ℝ => c * y) ⁻¹' Ioc s t = Ioc (s / c) (t / c) := by
  ext y
  simp only [mem_preimage, mem_Ioc]
  rw [div_lt_iff₀ hc, le_div_iff₀ hc, mul_comm y c]

theorem preimage_scaleUnitMap_prod (c : ℝ) (S A : Set ℝ) :
    scaleUnitMap c ⁻¹' (S ×ˢ A) = ((fun y : ℝ => c * y) ⁻¹' S) ×ˢ A := by
  ext x
  exact Iff.rfl

theorem map_scaleUnitMap_apply_prod (c : ℝ) (Λ : Measure (ℝ × ℝ)) {S A : Set ℝ}
    (hS : MeasurableSet S) (hA : MeasurableSet A) :
    Λ.map (scaleUnitMap c) (S ×ˢ A) = Λ (((fun y : ℝ => c * y) ⁻¹' S) ×ˢ A) := by
  rw [Measure.map_apply (measurable_scaleUnitMap c) (hS.prod hA), preimage_scaleUnitMap_prod]

/-- **The slabs after a change of scale unit**: `Λ'((s,t] × ·) = Λ((s/c,t/c] × ·)`. -/
theorem slab_map_scaleUnitMap {c : ℝ} (hc : 0 < c) (Λ : Measure (ℝ × ℝ)) (s t : ℝ) :
    slab (Λ.map (scaleUnitMap c)) s t = slab Λ (s / c) (t / c) := by
  rw [slab, slab, Measure.restrict_map (measurable_scaleUnitMap c)
      (measurableSet_Ioc.prod MeasurableSet.univ), preimage_scaleUnitMap_prod,
    preimage_mul_left_Ioc_div hc, Measure.map_map measurable_snd (measurable_scaleUnitMap c)]
  rfl

/-- **(i)–(iv) survive a change of scale unit.** -/
theorem isSurfacePair_scaleUnit {q c : ℝ} (hc : 0 < c) {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}
    (h : IsSurfacePair q Λ B) :
    IsSurfacePair q (Λ.map (scaleUnitMap c)) (B.map fun y => c * y) := by
  have hT := measurable_scaleUnitMap c
  have hm : Measurable fun y : ℝ => c * y := measurable_const_mul c
  have hE : MeasurableEmbedding fun y : ℝ => c * y := measurableEmbedding_mulLeft₀ hc.ne'
  have hquad : scaleUnitMap c ⁻¹' quadrant = quadrant := by
    ext x
    simp only [scaleUnitMap, quadrant, mem_preimage, mem_prod, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hc.le, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hc h1, h2⟩
  have hsing : ∀ y : ℝ, (fun x : ℝ => c * x) ⁻¹' {y} = {y / c} := by
    intro y
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    rw [eq_div_iff hc.ne', mul_comm]
  have hIic : (fun x : ℝ => c * x) ⁻¹' Iic 0 = Iic 0 := by
    ext x
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro hx <;> nlinarith
  refine
    { carried := ?_
      invariant := ?_
      integrable := ?_
      gaussian := ⟨?_, ?_, ?_⟩
      no_line := ?_
      nondeg := ?_ }
  · rw [Measure.map_apply hT measurableSet_quadrant.compl, preimage_compl, hquad]
    exact h.carried
  · have e : scaleDiag q ∘ scaleUnitMap c = scaleUnitMap c ∘ scaleDiag q := by
      funext x
      refine Prod.ext ?_ ?_ <;> simp only [Function.comp_apply, scaleDiag, scaleUnitMap]
      ring
    rw [Measure.map_map (measurable_scaleDiag q) hT, e,
      ← Measure.map_map hT (measurable_scaleDiag q), h.invariant]
  · intro t ht
    rw [slab_map_scaleUnitMap hc, zero_div]
    exact h.integrable _ (div_pos ht hc)
  · rw [Measure.map_apply hm measurableSet_Iic, hIic]
    exact h.gaussian.1
  · intro t ht
    rw [Measure.map_apply hm measurableSet_Ioc, preimage_mul_left_Ioc_div hc, zero_div]
    exact h.gaussian.2.1 _ (div_pos ht hc)
  · intro A hA hA0
    have hpre : (fun x : ℝ => c * x) ⁻¹' ((fun y => q * y) '' A) =
        (fun y => q * y) '' ((fun x : ℝ => c * x) ⁻¹' A) := by
      ext x
      simp only [mem_preimage, mem_image]
      constructor
      · rintro ⟨a, ha, e⟩
        refine ⟨a / c, ?_, ?_⟩
        · have e2 : c * (a / c) = a := by field_simp
          rw [e2]
          exact ha
        · rw [← mul_div_assoc, e, mul_div_cancel_left₀ _ hc.ne']
      · rintro ⟨b, hb, e⟩
        exact ⟨c * b, hb, by rw [← e]; ring⟩
    have hpos : (fun x : ℝ => c * x) ⁻¹' A ⊆ Ioi 0 := fun x hx =>
      pos_of_mul_pos_right (show 0 < c * x from hA0 hx) hc.le
    rw [hE.map_apply, hpre, h.gaussian.2.2 _ (hm hA) hpos, hE.map_apply]
  · intro y hy
    rw [map_scaleUnitMap_apply_prod c Λ (measurableSet_singleton y) measurableSet_Ioi, hsing,
      Measure.map_apply hm (measurableSet_singleton y), hsing]
    exact h.no_line _ (div_pos hy hc)
  · intro s t hs hst
    rw [map_scaleUnitMap_apply_prod c Λ measurableSet_Ioc measurableSet_Ioi,
      Measure.map_apply hm measurableSet_Ioc, preimage_mul_left_Ioc_div hc]
    exact h.nondeg _ _ (div_pos hs hc) ((div_lt_div_iff_of_pos_right hc).2 hst)

/-! ## The relabelled family -/

/-- **The relabelled family is again `q^ℤ`-covariant in the canonical discrete gauge.** -/
theorem isQFamily_scaleUnit {q c : ℝ} (hc : 0 < c) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsQFamily q μ) : IsQFamily q (fun s t => μ (s / c) (t / c)) := by
  obtain ⟨⟨hL, hND, hS⟩, hbij, hcov⟩ := hμ
  have hd : ∀ {s t : ℝ}, s ≤ t → s / c ≤ t / c := fun h => div_le_div_of_nonneg_right h hc.le
  have hn : ∀ {s : ℝ}, 0 ≤ s → 0 ≤ s / c := fun h => div_nonneg h hc.le
  refine ⟨⟨⟨fun s t hs hst => hL.isProbability _ _ (hn hs) (hd hst),
      fun t ht => hL.diag _ (hn ht),
      fun r s t hr hrs hst => hL.cascade _ _ _ (hn hr) (hd hrs) (hd hst), fun ω => ?_⟩,
    fun s t hs hst => hND _ _ (hn hs) ((div_lt_div_iff_of_pos_right hc).2 hst),
    fun s t hs hst => hS _ _ (hn hs) (hd hst)⟩, hbij, fun s t hs hst => ?_⟩
  · refine (hL.continuous ω).comp (f := fun p : ℝ × ℝ => (p.1 / c, p.2 / c)) (by fun_prop) ?_
    rintro p ⟨h1, h2⟩
    exact ⟨hn h1, hd h2⟩
  · have e := hcov (s / c) (t / c) (hn hs) (hd hst)
    simp only [mul_div_assoc]
    exact e

/-- **The pair of the relabelled family**: its kernels have the folded data of `(Λ', ℬ')`. -/
theorem isSurfaceDataOf_scaleUnit {c : ℝ} (hc : 0 < c) {μ : ℝ → ℝ → Measure ℝ}
    {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ} (h : IsSurfaceDataOf μ Λ B) :
    IsSurfaceDataOf (fun s t => μ (s / c) (t / c)) (Λ.map (scaleUnitMap c))
      (B.map fun y => c * y) := by
  intro t ht
  obtain ⟨P, h1, h2, h3⟩ := h (t / c) (div_pos ht hc)
  refine ⟨P, ?_, ?_, ?_⟩
  · show IsFoldedData (μ (0 / c) (t / c)) P
    rw [zero_div]
    exact h1
  · rw [slab_map_scaleUnitMap hc, zero_div, h2]
  · rw [Measure.map_apply (measurable_const_mul c) measurableSet_Ioc,
      preimage_mul_left_Ioc_div hc, zero_div, h3]

/-! ## The cylinder measure -/

/-- **`(θ, r) ↦ ([cθ], r/c)`**, the change of scale unit read on the cylinder. -/
noncomputable def scaleUnitCyl (q c : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (qRot q c x.1, c⁻¹ * x.2)

theorem measurable_scaleUnitCyl (q c : ℝ) : Measurable (scaleUnitCyl q c) :=
  ((measurable_qRot q c).comp measurable_fst).prodMk (measurable_snd.const_mul _)

/-- `(y, v) ↦ (y, av)` commutes with the orbit points, so it maps `Λ_σ` to the mixture of the
image of `σ`. -/
theorem orbitMixture_map_snd_mul (q : ℝ) (σ : Measure (ℝ × ℝ)) (a : ℝ) :
    (orbitMixture q σ).map (fun x : ℝ × ℝ => (x.1, a * x.2)) =
      orbitMixture q (σ.map fun x : ℝ × ℝ => (x.1, a * x.2)) := by
  have hD : Measurable fun x : ℝ × ℝ => (x.1, a * x.2) := by fun_prop
  ext s hs
  rw [Measure.map_apply hD hs, orbitMixture_apply q σ (hD hs), orbitMixture_apply q _ hs]
  refine tsum_congr fun n => ?_
  rw [Measure.map_apply hD (measurable_orbitPt q n hs)]
  have e : (fun x : ℝ × ℝ => (x.1, a * x.2)) ∘ orbitPt q n =
      orbitPt q n ∘ (fun x : ℝ × ℝ => (x.1, a * x.2)) := by
    funext x
    refine Prod.ext ?_ ?_ <;> simp only [Function.comp_apply, orbitPt]
    ring
  rw [← Set.preimage_comp, ← Set.preimage_comp, e]

/-- **The cylinder measure after a change of scale unit** is the image of `σ` under
`(θ, r) ↦ ([cθ], r/c)`. -/
theorem cylMeasure_map_scaleUnitMap {q c : ℝ} (hq : 1 < q) (hc : 0 < c) {Λ : Measure (ℝ × ℝ)}
    (hcar : Λ quadrantᶜ = 0) (hinv : Λ.map (scaleDiag q) = Λ) :
    cylMeasure q (Λ.map (scaleUnitMap c)) = (cylMeasure q Λ).map (scaleUnitCyl q c) := by
  obtain ⟨hσ, hmix⟩ := cylMeasure_spec hq hcar hinv
  have hD : Measurable fun x : ℝ × ℝ => (x.1, c⁻¹ * x.2) := by fun_prop
  have hT : scaleUnitMap c = scaleDiag c ∘ fun x : ℝ × ℝ => (x.1, c⁻¹ * x.2) := by
    funext x
    simp only [scaleUnitMap, scaleDiag, Function.comp_apply, Prod.mk.injEq, true_and]
    rw [mul_inv_cancel_left₀ hc.ne']
  have hσD : ((cylMeasure q Λ).map fun x : ℝ × ℝ => (x.1, c⁻¹ * x.2)) (cylinder q)ᶜ = 0 := by
    rw [Measure.map_apply hD (measurableSet_cylinder q).compl]
    refine measure_mono_null ?_ hσ
    intro x hx hxc
    exact hx ⟨hxc.1, mul_pos (inv_pos.2 hc) hxc.2⟩
  have hL : Λ.map (scaleUnitMap c) = ((orbitMixture q (cylMeasure q Λ)).map
      fun x : ℝ × ℝ => (x.1, c⁻¹ * x.2)).map (scaleDiag c) := by
    rw [hmix, Measure.map_map (measurable_scaleDiag c) hD, ← hT]
  rw [hL, orbitMixture_map_snd_mul, cylMeasure_map_scaleDiag hq hσD hc,
    Measure.map_map (measurable_rotPair q c) hD]
  rfl

/-! ## The disintegration and the phase entropy -/

/-- **The fibres after a change of scale unit**: `π'_r := (rot_c)_* π_{cr}`. -/
noncomputable def scaleUnitFibre (q c : ℝ) (π : ℝ → Measure ℝ) (r : ℝ) : Measure ℝ :=
  (π (c * r)).map (qRot q c)

theorem coe_mulLeft₀_inv {c : ℝ} (hc : 0 < c) :
    (MeasurableEquiv.mulLeft₀ c⁻¹ (inv_ne_zero hc.ne') : ℝ → ℝ) = fun r => c⁻¹ * r := by
  funext r
  rfl

/-- **The rotated and reattached fibres disintegrate the image**, whose `r`-marginal is `ρ̃`
pushed forward by `r ↦ r/c`. -/
theorem isPhaseDisintegration_scaleUnit {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    {σ : Measure (ℝ × ℝ)} (hσ : σ (cylinder q)ᶜ = 0) {π : ℝ → Measure ℝ}
    (hπ : IsPhaseDisintegration q σ π) :
    IsPhaseDisintegration q (σ.map (scaleUnitCyl q c)) (scaleUnitFibre q c π) ∧
      rMarginal q (σ.map (scaleUnitCyl q c)) = (rMarginal q σ).map fun r => c⁻¹ * r := by
  have hG := measurable_scaleUnitCyl q c
  have hGcyl : (σ.map (scaleUnitCyl q c)) (cylinder q)ᶜ = 0 := by
    rw [Measure.map_apply hG (measurableSet_cylinder q).compl]
    refine measure_mono_null ?_ hσ
    intro x hx hxc
    exact hx ⟨qRot_mem hq hc hxc.1, mul_pos (inv_pos.2 hc) hxc.2⟩
  have hmarg : rMarginal q (σ.map (scaleUnitCyl q c)) = (rMarginal q σ).map fun r => c⁻¹ * r := by
    rw [rMarginal_eq_map hGcyl, rMarginal_eq_map hσ, Measure.map_map measurable_snd hG,
      Measure.map_map (measurable_const_mul _) measurable_snd]
    rfl
  have he := coe_mulLeft₀_inv hc
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hmarg⟩
  · exact (Measure.measurable_map _ (measurable_qRot q c)).comp
      (hπ.measurable.comp (measurable_const_mul c))
  · intro r
    haveI := hπ.isProbability (c * r)
    exact Measure.isProbabilityMeasure_map (measurable_qRot q c).aemeasurable
  · intro r
    rw [scaleUnitFibre, Measure.map_apply (measurable_qRot q c) measurableSet_Ico.compl]
    exact measure_mono_null (fun θ hθ hθI => hθ (qRot_mem hq hc hθI)) (hπ.carried _)
  · intro E hE
    rw [hmarg, ← he, lintegral_map_equiv, Measure.map_apply hG hE, hπ.disintegrates _ (hG hE)]
    refine lintegral_congr fun r => ?_
    rw [he]
    dsimp only
    rw [scaleUnitFibre, mul_inv_cancel_left₀ hc.ne',
      Measure.map_apply (measurable_qRot q c) (measurable_prodMk_right hE)]
    rfl

/-- **The phase entropy of the image** with the rotated and reattached fibres is that of `σ`. -/
theorem phaseEntropy_scaleUnit {q c : ℝ} (hq : 1 < q) (hc : 0 < c) {σ : Measure (ℝ × ℝ)}
    (hσ : σ (cylinder q)ᶜ = 0) {π : ℝ → Measure ℝ} (hπ : IsPhaseDisintegration q σ π) :
    phaseEntropy q (σ.map (scaleUnitCyl q c)) (scaleUnitFibre q c π) = phaseEntropy q σ π := by
  obtain ⟨-, hmarg⟩ := isPhaseDisintegration_scaleUnit hq hc hσ hπ
  have he := coe_mulLeft₀_inv hc
  have hI : ∫⁻ r, klDiv (scaleUnitFibre q c π
      ((MeasurableEquiv.mulLeft₀ c⁻¹ (inv_ne_zero hc.ne')) r)) (haarPhase q) ∂(rMarginal q σ) =
      ∫⁻ r, klDiv (π r) (haarPhase q) ∂(rMarginal q σ) := by
    refine lintegral_congr fun r => ?_
    rw [he]
    dsimp only
    rw [scaleUnitFibre, mul_inv_cancel_left₀ hc.ne']
    haveI := hπ.isProbability r
    exact klDiv_rotatedFibre hq (hπ.carried r) hc
  rw [phaseEntropy, phaseEntropy, hmarg, ← he, lintegral_map_equiv, hI]

/-- Two disintegrations that agree almost everywhere give the same phase entropy. -/
theorem phaseEntropy_congr_ae {q : ℝ} {σ : Measure (ℝ × ℝ)} {π π' : ℝ → Measure ℝ}
    (h : ∀ᵐ r ∂(rMarginal q σ), π r = π' r) : phaseEntropy q σ π = phaseEntropy q σ π' := by
  rw [phaseEntropy, phaseEntropy, lintegral_congr_ae (h.mono fun r hr => by rw [hr])]

/-! ## The node -/

/-- **`prop:phase-entropy-scale-unit`.** Let `μ` be a `q^ℤ`-covariant family in the canonical
discrete gauge with the pair `(Λ, ℬ)`, and `c > 0`. The family relabelled by `t ↦ ct`,
`μ'_{s,t} = μ_{s/c,t/c}`, is again `q^ℤ`-covariant in the canonical discrete gauge; its pair is
`((y, v) ↦ (cy, v))_* Λ` and `(y ↦ cy)_* ℬ`; its cylinder measure is the image of `σ` under
`(θ, r) ↦ ([cθ], r/c)`; and for every disintegration of the two cylinder measures the phase
entropies agree. -/
theorem phase_entropy_scale_unit {q c : ℝ} (hq : 1 < q) (hc : 0 < c) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsQFamily q μ) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (hΛ : IsFamilyPair q μ Λ B) :
    IsQFamily q (fun s t => μ (s / c) (t / c)) ∧
      IsFamilyPair q (fun s t => μ (s / c) (t / c)) (Λ.map (scaleUnitMap c))
        (B.map fun y => c * y) ∧
      cylMeasure q (Λ.map (scaleUnitMap c)) = (cylMeasure q Λ).map (scaleUnitCyl q c) ∧
      ∀ π π' : ℝ → Measure ℝ, IsPhaseDisintegration q (cylMeasure q Λ) π →
        IsPhaseDisintegration q (cylMeasure q (Λ.map (scaleUnitMap c))) π' →
        phaseEntropy q (cylMeasure q (Λ.map (scaleUnitMap c))) π' =
          phaseEntropy q (cylMeasure q Λ) π := by
  have hpair := isSurfacePair_scaleUnit hc hΛ.1
  have hcyl := cylMeasure_map_scaleUnitMap hq hc hΛ.1.carried hΛ.1.invariant
  refine ⟨isQFamily_scaleUnit hc hμ, ⟨hpair, isSurfaceDataOf_scaleUnit hc hΛ.2⟩, hcyl,
    fun π π' hπ hπ' => ?_⟩
  obtain ⟨hσ', hmix'⟩ := cylMeasure_spec hq hpair.carried hpair.invariant
  have hint' : IsCylIntegrable (cylMeasure q (Λ.map (scaleUnitMap c))) := by
    refine (knot_atom_cascades_2_integrable hq _ hσ').1.1 ?_
    rw [hmix']
    exact hpair.integrable
  have hσ := (cylMeasure_spec hq hΛ.1.carried hΛ.1.invariant).1
  obtain ⟨hπs, -⟩ := isPhaseDisintegration_scaleUnit hq hc hσ hπ
  rw [← hcyl] at hπs
  rw [phaseEntropy_congr_ae (phaseDisintegration_ae_eq hσ' hint' hπ' hπs), hcyl]
  exact phaseEntropy_scaleUnit hq hc hσ hπ

end Pyramids
