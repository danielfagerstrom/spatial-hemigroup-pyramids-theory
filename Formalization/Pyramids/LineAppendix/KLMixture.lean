/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# Three facts about the relative entropy that `prop:phase-entropy-ladder-bound` reads

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:phase-entropy-ladder-bound`(1). General
measure theory, nothing of the article's: wave 3f.

* **Invariance under a measurable equivalence** (`klDiv_map_measurableEquiv`): the
  Radon–Nikodym derivative of the images is the image of the derivative (Mathlib's
  `MeasurableEmbedding.rnDeriv_map`).
* **The conditional relative entropy in integral form** (`klDiv_compProd_right`):
  `KL(μ ⊗ κ ‖ μ ⊗ η) = ∫ KL(κ_a ‖ η_a) μ(da)` for Markov kernels on countably generated spaces.
  Mathlib's chain rule `klDiv_compProd_eq_add` states the conditional term as
  `KL(μ ⊗ κ ‖ μ ⊗ η)` and leaves the integral form as a to-do; the derivative
  `d(μ ⊗ κ)/d(μ ⊗ η)` is the kernel derivative `(a, b) ↦ (dκ_a/dη_a)(b)` where `κ_a ≪ η_a`
  almost everywhere (`rnDeriv_compProd_right`).
* **The mixture identity** (`lintegral_klDiv_eq_add`): for a probability `ρ`, a Markov kernel `P`
  and its mixture `M = ∫ P_r ρ(dr)`,
  `∫ KL(P_r ‖ η) ρ(dr) = KL(M ‖ η) + ∫ KL(P_r ‖ M) ρ(dr)` in `[0,∞]`, with no finiteness
  hypothesis. Both sides are relative entropies of the joint law `Q = ρ ⊗ P` (the previous item);
  swapping the coordinates and disintegrating `Q` along its second marginal `M`, the chain rule
  splits off `KL(M ‖ η)`.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set ProbabilityTheory InformationTheory
open scoped ENNReal

/-! ## Invariance under a measurable equivalence -/

/-- **The relative entropy is invariant under a measurable equivalence.** -/
theorem klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  classical
  have hac : μ.map e ≪ ν.map e ↔ μ ≪ ν := by
    refine ⟨fun h => ?_, fun h => h.map e.measurable⟩
    have h2 := h.map e.symm.measurable
    rwa [MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map] at h2
  rw [klDiv_eq_lintegral_klFun, klDiv_eq_lintegral_klFun]
  by_cases h : μ ≪ ν
  · rw [if_pos (hac.2 h), if_pos h, lintegral_map_equiv]
    refine lintegral_congr_ae ?_
    filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
    rw [hx]
  · rw [if_neg (mt hac.1 h), if_neg h]

/-! ## The conditional relative entropy in integral form -/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]

/-- **The derivative of `μ ⊗ κ` against `μ ⊗ η`** is the kernel derivative, where `κ_a ≪ η_a` for
`μ`-almost every `a`. -/
theorem rnDeriv_compProd_right (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] (h : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p => Kernel.rnDeriv κ η p.1 p.2 := by
  have hk : μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (fun p => Kernel.rnDeriv κ η p.1 p.2) := by
    rw [← Measure.compProd_withDensity (Kernel.measurable_rnDeriv κ η)]
    refine Measure.compProd_congr ?_
    filter_upwards [h] with a ha
    exact (Kernel.withDensity_rnDeriv_eq ha).symm
  rw [hk]
  exact Measure.rnDeriv_withDensity _ (Kernel.measurable_rnDeriv κ η)

/-- **The conditional relative entropy in integral form**:
`KL(μ ⊗ κ ‖ μ ⊗ η) = ∫ KL(κ_a ‖ η_a) μ(da)`. -/
theorem klDiv_compProd_right (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β)
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  by_cases h : ∀ᵐ a ∂μ, κ a ≪ η a
  · have hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η := Measure.absolutelyContinuous_compProd_right_iff.2 h
    rw [klDiv_eq_lintegral_klFun_of_ac hac,
      lintegral_congr_ae (g := fun p => ENNReal.ofReal (klFun (Kernel.rnDeriv κ η p.1 p.2).toReal))
        (by filter_upwards [rnDeriv_compProd_right μ κ η h] with p hp; rw [hp]),
      Measure.lintegral_compProd]
    · refine lintegral_congr_ae ?_
      filter_upwards [h] with a ha
      rw [klDiv_eq_lintegral_klFun_of_ac ha]
      refine lintegral_congr_ae ?_
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with x hx
      rw [hx]
    · exact (measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal
  · have hnac : ¬ μ ⊗ₘ κ ≪ μ ⊗ₘ η := fun hac =>
      h (Measure.absolutelyContinuous_compProd_right_iff.1 hac)
    rw [klDiv_of_not_ac hnac]
    have hS : MeasurableSet {a | κ a ≪ η a} := Kernel.measurableSet_absolutelyContinuous κ η
    have hpos : μ {a | κ a ≪ η a}ᶜ ≠ 0 := by
      intro h0
      exact h (by rw [ae_iff]; exact h0)
    symm
    rw [eq_top_iff]
    calc (⊤ : ℝ≥0∞) = ∫⁻ _ in {a | κ a ≪ η a}ᶜ, ⊤ ∂μ := by
          rw [setLIntegral_const, ENNReal.top_mul hpos]
      _ ≤ ∫⁻ a in {a | κ a ≪ η a}ᶜ, klDiv (κ a) (η a) ∂μ :=
          setLIntegral_mono' hS.compl fun a ha => (klDiv_of_not_ac ha).ge
      _ ≤ ∫⁻ a, klDiv (κ a) (η a) ∂μ := setLIntegral_le_lintegral _ _

/-! ## The mixture identity -/

/-- **The mixture identity**: for a probability `ρ`, a Markov kernel `P` and the mixture
`M = P ∘ ρ`, `∫ KL(P_r ‖ η) ρ(dr) = KL(M ‖ η) + ∫ KL(P_r ‖ M) ρ(dr)`. -/
theorem lintegral_klDiv_eq_add (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (P : Kernel ℝ ℝ)
    [IsMarkovKernel P] (η : Measure ℝ) [IsProbabilityMeasure η] :
    ∫⁻ r, klDiv (P r) η ∂ρ = klDiv (P ∘ₘ ρ) η + ∫⁻ r, klDiv (P r) (P ∘ₘ ρ) ∂ρ := by
  set M := P ∘ₘ ρ with hMdef
  have hconst : ∀ ν : Measure ℝ, [IsProbabilityMeasure ν] →
      ∫⁻ r, klDiv (P r) ν ∂ρ = klDiv (ρ ⊗ₘ P) (ρ ⊗ₘ Kernel.const ℝ ν) := by
    intro ν _
    rw [klDiv_compProd_right]
    simp only [Kernel.const_apply]
  set e : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodComm with he
  have hecoe : (e : ℝ × ℝ → ℝ × ℝ) = Prod.swap := rfl
  have hswap : ∀ ν : Measure ℝ, [IsProbabilityMeasure ν] →
      (ρ ⊗ₘ Kernel.const ℝ ν).map e = ν ⊗ₘ Kernel.const ℝ ρ := by
    intro ν _
    rw [Measure.compProd_const, Measure.compProd_const, hecoe]
    exact Measure.prod_swap
  set Q := (ρ ⊗ₘ P).map e with hQdef
  have hQ : Q.fst = M := by
    rw [hQdef, hecoe, Measure.fst_map_swap, Measure.snd_compProd]
  have hQd : Q = M ⊗ₘ Q.condKernel := by
    have h := Q.disintegrate Q.condKernel
    rw [hQ] at h
    exact h.symm
  rw [hconst η, hconst M, ← klDiv_map_measurableEquiv e (ρ ⊗ₘ P),
    ← klDiv_map_measurableEquiv e (ρ ⊗ₘ P), hswap, hswap, ← hQdef, hQd,
    klDiv_compProd_eq_add]

end Pyramids
