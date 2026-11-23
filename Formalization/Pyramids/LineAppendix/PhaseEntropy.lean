/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.StrataCylinderJump
import Pyramids.LineAppendix.StrataCylinderParts
import Pyramids.LineAppendix.PhaseDisintegration
import Pyramids.LineAppendix.KnotLadder
import Pyramids.LineAppendix.StepField
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# `thm:phase-entropy-selection`(1)–(2): the sign of the phase entropy, and when it vanishes

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:phase-entropy-selection`. Wave 3d: the
declarations `phase_entropy_selection_1` and `phase_entropy_selection_2` moved here from
`PyramidsSkeleton.ChA1Line`, unchanged in name and conclusion; `phase_entropy_selection_2` no
longer takes the family `μ`, its hypothesis `IsQFamily q μ`, the measure `ℬ` or the hypothesis
`IsFamilyPair q μ Λ B`, which the proof does not read (a strengthening: it holds for the cylinder
measure of every measure `Λ`).

## The route

* **Measurability.** The phase entropy is a lower integral of `r ↦ KL(π_r ‖ η)`. For a measurable
  family of probability measures this map is measurable (`measurable_klDiv_kernel`): the relative
  entropy is `∫ klFun(dπ_r/dη) dη` where `π_r ≪ η` and `∞` elsewhere (Mathlib's
  `klDiv_eq_lintegral_klFun`), the density can be chosen jointly measurable (Mathlib's
  `Kernel.rnDeriv`), and the set where `π_r ≪ η` is measurable
  (`Kernel.measurableSet_absolutelyContinuous`).
* **(2).** `𝔈 ≤ 0` as the negative of a value in `[0,∞]`; `𝔈 = 0` iff the integrand vanishes
  almost everywhere, iff `π_r = η` almost everywhere (Gibbs, `klDiv_eq_zero_iff`).
* **`𝔈 = 0` iff `σ = η ⊗ ρ̃`** (`phaseEntropy_eq_zero_iff_prod`): one way the disintegration
  identity with `π_r = η` is the product formula; the other way the constant family `η` is a
  disintegration of `η ⊗ ρ̃`, and disintegrations agree almost everywhere
  (`phaseDisintegration_ae_eq`). With `prop:strata-cylinder-coordinates`(1) this is
  `phaseEntropy_eq_zero_iff_slab`: `𝔈 = 0` iff `ϖ_{λt} = T_λ ϖ_t` for all `λ, t > 0`.
* **(1).** A member with `Ψ_{λt} = Ψ_t(λ ·)` has `Ψ_t = Ψ_1(t ·)`, the exponents of the similarity
  member, and a family is determined by its exponents on `[1,q)` (`qFamily_eq_of_lineExponent`).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-! ## Measurability of the integrand -/

open Classical in
/-- `r ↦ KL(π_r ‖ η)` is measurable for a measurable family of probability measures on `ℝ`. -/
theorem measurable_klDiv_kernel {π : ℝ → Measure ℝ} (hπm : Measurable π)
    (hπp : ∀ r : ℝ, IsProbabilityMeasure (π r)) (η : Measure ℝ) [IsFiniteMeasure η] :
    Measurable fun r => klDiv (π r) η := by
  let K : Kernel ℝ ℝ := ⟨π, hπm⟩
  haveI : IsMarkovKernel K := ⟨hπp⟩
  let E : Kernel ℝ ℝ := Kernel.const ℝ η
  have hset : MeasurableSet {r | K r ≪ E r} := Kernel.measurableSet_absolutelyContinuous K E
  have hint : Measurable fun r => ∫⁻ x, ENNReal.ofReal (klFun (K.rnDeriv E r x).toReal) ∂η := by
    have hf : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (klFun (K.rnDeriv E p.1 p.2).toReal) :=
      (measurable_klFun.comp (Kernel.measurable_rnDeriv K E).ennreal_toReal).ennreal_ofReal
    exact hf.lintegral_prod_right'
  have heq : (fun r => klDiv (π r) η) = fun r => if K r ≪ E r then
      ∫⁻ x, ENNReal.ofReal (klFun (K.rnDeriv E r x).toReal) ∂η else ∞ := by
    funext r
    haveI := hπp r
    rw [klDiv_eq_lintegral_klFun]
    by_cases h : π r ≪ η
    · have h' : K r ≪ E r := h
      rw [if_pos h, if_pos h']
      refine lintegral_congr_ae ?_
      have hae := Kernel.rnDeriv_eq_rnDeriv_measure (κ := K) (η := E) (a := r)
      filter_upwards [hae] with x hx
      rw [hx]
      rfl
    · have h' : ¬ K r ≪ E r := h
      rw [if_neg h, if_neg h']
  rw [heq]
  exact Measurable.ite hset hint measurable_const

/-! ## (2) -/

/-- `𝔈 ≤ 0`. -/
theorem phaseEntropy_nonpos (q : ℝ) (σ : Measure (ℝ × ℝ)) (π : ℝ → Measure ℝ) :
    phaseEntropy q σ π ≤ 0 :=
  EReal.neg_le_zero.2 (EReal.coe_ennreal_nonneg _)

/-- `𝔈 = 0` iff `π_r = η` for `ρ̃`-almost every `r`. -/
theorem phaseEntropy_eq_zero_iff {q : ℝ} (hq : 1 < q) {σ : Measure (ℝ × ℝ)}
    {π : ℝ → Measure ℝ} (hπ : IsPhaseDisintegration q σ π) :
    phaseEntropy q σ π = 0 ↔ ∀ᵐ r ∂(rMarginal q σ), π r = haarPhase q := by
  haveI := isProbabilityMeasure_haarPhase hq
  rw [phaseEntropy, EReal.neg_eq_zero_iff, EReal.coe_ennreal_eq_zero,
    lintegral_eq_zero_iff (measurable_klDiv_kernel hπ.measurable hπ.isProbability _)]
  constructor
  · intro h
    filter_upwards [h] with r hr
    haveI := hπ.isProbability r
    exact klDiv_eq_zero_iff.1 hr
  · intro h
    filter_upwards [h] with r hr
    rw [hr, Pi.zero_apply]
    exact klDiv_self _

/-- **`thm:phase-entropy-selection`(2)**, for every family (in particular every member):
`𝔈 ≤ 0`, with equality iff `π_r = η` for `ρ̃`-almost every `r`. The family `μ`, its hypothesis
`IsQFamily q μ`, the measure `ℬ` and the hypothesis `IsFamilyPair q μ Λ B` of the skeleton are not
used and were dropped on 2026-11-14, a strengthening: the statement holds for the cylinder measure
of every measure `Λ` and every disintegration of it. -/
theorem phase_entropy_selection_2 {q : ℝ} (hq : 1 < q) (Λ : Measure (ℝ × ℝ))
    (π : ℝ → Measure ℝ) (hπ : IsPhaseDisintegration q (cylMeasure q Λ) π) :
    phaseEntropy q (cylMeasure q Λ) π ≤ 0 ∧
      (phaseEntropy q (cylMeasure q Λ) π = 0 ↔
        ∀ᵐ r ∂(rMarginal q (cylMeasure q Λ)), π r = haarPhase q) :=
  ⟨phaseEntropy_nonpos q _ π, phaseEntropy_eq_zero_iff hq hπ⟩

/-! ## `𝔈 = 0` iff the cylinder measure is a product with `η` -/

instance sFinite_haarPhase (q : ℝ) : SFinite (haarPhase q) := by
  rw [haarPhase]
  infer_instance

/-- The `r`-marginal of `η ⊗ ρ` is `ρ`. -/
theorem rMarginal_haarPhase_prod {q : ℝ} (hq : 1 < q) (ρ : Measure ℝ) [SFinite ρ] :
    rMarginal q ((haarPhase q).prod ρ) = ρ := by
  haveI := isProbabilityMeasure_haarPhase hq
  have hη : (haarPhase q).restrict (Ico 1 q) = haarPhase q := by
    rw [haarPhase_eq_restrict, Measure.restrict_restrict measurableSet_Ico, inter_self]
  rw [rMarginal, ← Measure.restrict_univ (μ := ρ), ← Measure.prod_restrict, hη,
    Measure.restrict_univ, Measure.map_snd_prod, measure_univ, one_smul]

/-- The constant family `η` disintegrates `η ⊗ ρ`. -/
theorem isPhaseDisintegration_haarPhase_prod {q : ℝ} (hq : 1 < q) (ρ : Measure ℝ) [SFinite ρ] :
    IsPhaseDisintegration q ((haarPhase q).prod ρ) (fun _ => haarPhase q) where
  measurable := measurable_const
  isProbability := fun _ => isProbabilityMeasure_haarPhase hq
  carried := fun _ => haarPhase_compl_Ico q
  disintegrates := fun E hE => by
    rw [rMarginal_haarPhase_prod hq, Measure.prod_apply_symm hE]

/-- A disintegration with `π_r = η` almost everywhere makes `σ = η ⊗ ρ̃`. -/
theorem eq_prod_of_ae_haarPhase {q : ℝ} {σ : Measure (ℝ × ℝ)} {π : ℝ → Measure ℝ}
    (hπ : IsPhaseDisintegration q σ π) [SFinite (rMarginal q σ)]
    (h : ∀ᵐ r ∂(rMarginal q σ), π r = haarPhase q) :
    σ = (haarPhase q).prod (rMarginal q σ) := by
  ext E hE
  rw [hπ.disintegrates E hE, Measure.prod_apply_symm hE]
  exact lintegral_congr_ae (h.mono fun r hr => by simp only [hr])

/-- For a measure on the cylinder with (A.e3), `𝔈 = 0` iff `σ = η ⊗ ρ̃` for some `ρ̃`. -/
theorem phaseEntropy_eq_zero_iff_prod {q : ℝ} (hq : 1 < q) {σ : Measure (ℝ × ℝ)}
    (hσ : σ (cylinder q)ᶜ = 0) (hint : IsCylIntegrable σ) {π : ℝ → Measure ℝ}
    (hπ : IsPhaseDisintegration q σ π) :
    phaseEntropy q σ π = 0 ↔
      ∃ ρ : Measure ℝ, SFinite ρ ∧ ρ (Iic 0) = 0 ∧ σ = (haarPhase q).prod ρ := by
  haveI := sFinite_rMarginal hσ hint
  rw [phaseEntropy_eq_zero_iff hq hπ]
  constructor
  · intro h
    exact ⟨rMarginal q σ, inferInstance, rMarginal_Iic hσ, eq_prod_of_ae_haarPhase hπ h⟩
  · rintro ⟨ρ, hρs, -, hρ⟩
    have hd := isPhaseDisintegration_haarPhase_prod hq ρ
    rw [← hρ] at hd
    exact phaseDisintegration_ae_eq hσ hint hπ hd

/-- For a pair with (i)–(iv), `𝔈 = 0` iff `ϖ_{λt} = T_λ ϖ_t` for all `λ, t > 0`
(`prop:strata-cylinder-coordinates`(1), the jump part). -/
theorem phaseEntropy_eq_zero_iff_slab {q : ℝ} (hq : 1 < q) {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}
    (h : IsSurfacePair q Λ B) {π : ℝ → Measure ℝ}
    (hπ : IsPhaseDisintegration q (cylMeasure q Λ) π) :
    phaseEntropy q (cylMeasure q Λ) π = 0 ↔
      ∀ lam t : ℝ, 0 < lam → 0 < t → slab Λ 0 (lam * t) = (slab Λ 0 t).map (fun v => lam * v) := by
  obtain ⟨hσ, hmix⟩ := cylMeasure_spec hq h.carried h.invariant
  have hint : IsCylIntegrable (cylMeasure q Λ) := by
    refine (knot_atom_cascades_2_integrable hq _ hσ).1.1 ?_
    rw [hmix]
    exact h.integrable
  rw [phaseEntropy_eq_zero_iff_prod hq hσ hint hπ, (strata_cylinder_1_jump hq Λ B h).1,
    (strata_cylinder_1_jump hq Λ B h).2]

/-- `ϖ_{λt} = T_λ ϖ_t` for all `λ, t > 0` iff `ϖ_t = T_t ϖ_1` for all `t > 0`. -/
theorem slab_cov_iff (Λ : Measure (ℝ × ℝ)) :
    (∀ lam t : ℝ, 0 < lam → 0 < t → slab Λ 0 (lam * t) = (slab Λ 0 t).map (fun v => lam * v)) ↔
      ∀ t : ℝ, 0 < t → slab Λ 0 t = (slab Λ 0 1).map (fun v => t * v) := by
  constructor
  · intro h t ht
    have e := h t 1 ht one_pos
    rwa [mul_one] at e
  · intro h lam t hlam ht
    rw [h _ (mul_pos hlam ht), h t ht, Measure.map_map (measurable_const_mul _)
      (measurable_const_mul _)]
    congr 1
    funext v
    simp only [Function.comp_apply]
    ring

/-- For the pair of a family, `Ψ_{λt} = Ψ_t(λ ·)` for all `λ, t > 0` iff (a) and (a') of
`prop:strata-cylinder-coordinates`(1). -/
theorem lineExponent_cov_iff {q : ℝ} {μ : ℝ → ℝ → Measure ℝ} (hμ : IsQFamily q μ)
    {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ} (hΛ : IsFamilyPair q μ Λ B) :
    (∀ lam t : ℝ, 0 < lam → 0 < t → ∀ ω : ℝ,
        lineExponent μ (lam * t) ω = lineExponent μ t (lam * ω)) ↔
      (∀ lam t : ℝ, 0 < lam → 0 < t → slab Λ 0 (lam * t) = (slab Λ 0 t).map (fun v => lam * v)) ∧
        ∀ lam t : ℝ, 0 < lam → 0 < t →
          (B (Ioc 0 (lam * t))).toReal = lam ^ 2 * (B (Ioc 0 t)).toReal := by
  have he := (surface_measure_exponent μ hμ Λ B hΛ.1).1 hΛ.2
  rw [← strata_cylinder_1_both Λ B hΛ.1]
  constructor
  · intro H lam t hlam ht ω
    rw [← he _ (mul_pos hlam ht), ← he t ht]
    exact H lam t hlam ht ω
  · intro H lam t hlam ht ω
    rw [he _ (mul_pos hlam ht), he t ht]
    exact H lam t hlam ht ω

/-! ## (1) -/

/-- **`thm:phase-entropy-selection`(1).** The similarity member `μ₀` has
`Ψ_{λt} = Ψ_t(λ ·)` for all `λ, t > 0`, and it is the only member that has. The hypothesis
`IsKnotExponent q Ψ1` of the skeleton is not used and was dropped on 2026-11-14, a
strengthening. -/
theorem phase_entropy_selection_1 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ)
    (μ₀ : ℝ → ℝ → Measure ℝ) (hμ₀ : μ₀ ∈ modulationOrbit q Ψ1)
    (hsim : ∀ t : ℝ, 0 < t → ∀ ω : ℝ, lineExponent μ₀ t ω = Ψ1 (t * ω)) :
    (∀ lam t : ℝ, 0 < lam → 0 < t → ∀ ω : ℝ,
        lineExponent μ₀ (lam * t) ω = lineExponent μ₀ t (lam * ω)) ∧
      ∀ μ ∈ modulationOrbit q Ψ1,
        (∀ lam t : ℝ, 0 < lam → 0 < t → ∀ ω : ℝ,
          lineExponent μ (lam * t) ω = lineExponent μ t (lam * ω)) →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ₀ s t := by
  refine ⟨fun lam t hlam ht ω => ?_, fun μ hμ hcov s t hs hst => ?_⟩
  · rw [hsim _ (mul_pos hlam ht), hsim t ht]
    congr 1
    ring
  · refine qFamily_eq_of_lineExponent hq hμ.1 hμ₀.1 (fun t' ht' ω => ?_) s t hs hst
    have ht0 : 0 < t' := lt_of_lt_of_le one_pos ht'.1
    have h1 := hcov t' 1 ht0 one_pos ω
    rw [mul_one, lineExponent_one_of_mem_orbit hμ] at h1
    rw [h1, hsim t' ht0]

end Pyramids
