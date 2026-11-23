/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.KnotOrbits
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# `lem:phase-disintegration-exists`: the phase disintegration exists and is unique

Blueprint: `blueprint/src/parts/A1-line.tex`, `lem:phase-disintegration-exists`. Wave 3c: the
declaration `phase_disintegration_exists` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in
name and conclusion; its hypothesis `IsQFamily q μ`, which the proof does not use, is dropped (a
strengthening).

## The route

* **The weight.** `g(r) := w(r) = r² ∧ (1 + log₊ r)` is positive on `(0,∞)` and nondecreasing on
  `[0,∞)` (`cylWeight_mono`). For `θ ∈ [1,q)` and `r > 0`, `w(r) ≤ w(rθ)`, so (A.e3) gives
  `∫ g dρ̃ < ∞` (`lintegral_cylWeight_rMarginal_ne_top`). This gives the finiteness of
  `ρ̃([r₀,∞))` at once, and makes `gρ̃` finite and `ρ̃ = (gρ̃)/g` s-finite.
* **Existence.** With `τ` the image of `σ` under `(θ, r) ↦ (r, θ)`, the finite measure `g(r)τ` is
  `(gρ̃) ⊗ κ` for Mathlib's conditional kernel `κ` (`Measure.condKernel`, on the standard Borel
  space `ℝ`); dividing by `g` gives `τ = ρ̃ ⊗ κ` (`withDensity_compProd_left`). `κ_r` is carried by
  `[1,q)` for `ρ̃`-a.e. `r`, and is replaced by `δ_1` on the remaining null set.
* **Uniqueness.** A disintegration `π` is a Markov kernel with `ρ̃ ⊗ π = τ`; two of them give
  `(gρ̃) ⊗ π = (gρ̃) ⊗ π'`, so `π = π'` `gρ̃`-a.e. (`Kernel.ae_eq_of_compProd_eq`), hence `ρ̃`-a.e.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal

/-! ## The weight -/

theorem continuous_cylWeight : Continuous cylWeight := by
  unfold cylWeight
  fun_prop

theorem measurable_cylWeight : Measurable cylWeight := continuous_cylWeight.measurable

/-- `w` is nondecreasing on `[0,∞)`. -/
theorem cylWeight_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : cylWeight x ≤ cylWeight y :=
  min_le_min (pow_le_pow_left₀ hx hxy 2) (add_le_add le_rfl (Real.posLog_le_posLog hx hxy))

/-- The weight on the `r`-line, `g(r) := w(r)` in `[0,∞]`. -/
noncomputable def rWeight (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal (cylWeight r)

theorem measurable_rWeight : Measurable rWeight :=
  ENNReal.measurable_ofReal.comp measurable_cylWeight

theorem rWeight_ne_top (r : ℝ) : rWeight r ≠ ⊤ := ENNReal.ofReal_ne_top

theorem rWeight_ne_zero {r : ℝ} (hr : 0 < r) : rWeight r ≠ 0 := by
  rw [rWeight, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact cylWeight_pos hr

/-! ## The `r`-marginal of a measure on the cylinder -/

section Marginal

variable {q : ℝ} {σ : Measure (ℝ × ℝ)}

theorem ae_mem_cylinder (hσ : σ (cylinder q)ᶜ = 0) : ∀ᵐ p ∂σ, p ∈ cylinder q := by
  rw [ae_iff]
  exact hσ

theorem rMarginal_eq_map (hσ : σ (cylinder q)ᶜ = 0) : rMarginal q σ = σ.map Prod.snd := by
  rw [rMarginal, Measure.restrict_eq_self_of_ae_mem]
  exact (ae_mem_cylinder hσ).mono fun p hp => ⟨hp.1, mem_univ _⟩

theorem rMarginal_Iic (hσ : σ (cylinder q)ᶜ = 0) : rMarginal q σ (Iic 0) = 0 := by
  rw [rMarginal_eq_map hσ, Measure.map_apply measurable_snd measurableSet_Iic]
  refine measure_mono_null (fun p hp => ?_) hσ
  intro hpc
  linarith [show (0 : ℝ) < p.2 from hpc.2, show p.2 ≤ 0 from hp]

theorem ae_rMarginal_pos (hσ : σ (cylinder q)ᶜ = 0) : ∀ᵐ r ∂(rMarginal q σ), 0 < r := by
  rw [ae_iff]
  have e : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext; simp
  rw [e]
  exact rMarginal_Iic hσ

theorem ae_rWeight_ne_zero (hσ : σ (cylinder q)ᶜ = 0) :
    ∀ᵐ r ∂(rMarginal q σ), rWeight r ≠ 0 :=
  (ae_rMarginal_pos hσ).mono fun _ hr => rWeight_ne_zero hr

/-- **`∫ g dρ̃ < ∞`** from (A.e3): `w(r) ≤ w(rθ)` on the cylinder. -/
theorem lintegral_rWeight_ne_top (hσ : σ (cylinder q)ᶜ = 0) (hint : IsCylIntegrable σ) :
    ∫⁻ r, rWeight r ∂(rMarginal q σ) ≠ ⊤ := by
  rw [rMarginal_eq_map hσ, lintegral_map measurable_rWeight measurable_snd]
  refine ne_top_of_le_ne_top hint (lintegral_mono_ae ((ae_mem_cylinder hσ).mono fun p hp => ?_))
  have h1 : 1 ≤ p.1 := hp.1.1
  have h2 : 0 < p.2 := hp.2
  refine ENNReal.ofReal_le_ofReal (cylWeight_mono h2.le ?_)
  nlinarith

theorem isFiniteMeasure_withDensity_rWeight (hσ : σ (cylinder q)ᶜ = 0)
    (hint : IsCylIntegrable σ) : IsFiniteMeasure ((rMarginal q σ).withDensity rWeight) :=
  isFiniteMeasure_withDensity (lintegral_rWeight_ne_top hσ hint)

/-- `ρ̃ = (gρ̃)/g`, so `ρ̃` is s-finite. -/
theorem sFinite_rMarginal (hσ : σ (cylinder q)ᶜ = 0) (hint : IsCylIntegrable σ) :
    SFinite (rMarginal q σ) := by
  have := isFiniteMeasure_withDensity_rWeight hσ hint
  rw [← withDensity_inv_same measurable_rWeight (ae_rWeight_ne_zero hσ)
    (Eventually.of_forall rWeight_ne_top)]
  infer_instance

/-- **`ρ̃([r₀,∞)) < ∞`** for `r₀ > 0`. -/
theorem rMarginal_Ici_ne_top (hσ : σ (cylinder q)ᶜ = 0) (hint : IsCylIntegrable σ) {r₀ : ℝ}
    (hr₀ : 0 < r₀) : rMarginal q σ (Ici r₀) ≠ ⊤ := by
  have hle : rWeight r₀ * rMarginal q σ (Ici r₀) ≤ ∫⁻ r, rWeight r ∂(rMarginal q σ) := by
    rw [← setLIntegral_const]
    refine (setLIntegral_mono measurable_rWeight fun r hr => ?_).trans
      (setLIntegral_le_lintegral _ _)
    exact ENNReal.ofReal_le_ofReal (cylWeight_mono hr₀.le hr)
  intro htop
  rw [htop, ENNReal.mul_top (rWeight_ne_zero hr₀)] at hle
  exact lintegral_rWeight_ne_top hσ hint (top_le_iff.1 hle)

end Marginal

/-! ## Products and densities -/

/-- `(gμ) ⊗ κ = (μ ⊗ κ)·(g ∘ fst)`. -/
theorem withDensity_compProd_left {μ : Measure ℝ} [SFinite μ] (κ : Kernel ℝ ℝ)
    [IsSFiniteKernel κ] {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity g) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity fun p => g p.1 := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs,
    lintegral_withDensity_eq_lintegral_mul _ hg (Kernel.measurable_kernel_prodMk_left hs),
    ← lintegral_indicator hs,
    Measure.lintegral_compProd (f := s.indicator fun p : ℝ × ℝ => g p.1)
      ((hg.comp measurable_fst).indicator hs)]
  congr 1
  funext a
  have e : (fun b => s.indicator (fun p : ℝ × ℝ => g p.1) (a, b)) =
      (Prod.mk a ⁻¹' s).indicator fun _ => g a := by
    funext b
    rfl
  rw [e, lintegral_indicator_const (measurable_prodMk_left hs), Pi.mul_apply]

/-- The image `τ` of `σ` under `(θ, r) ↦ (r, θ)` has the first marginal `ρ̃`. -/
theorem fst_map_swap {q : ℝ} {σ : Measure (ℝ × ℝ)} (hσ : σ (cylinder q)ᶜ = 0) :
    (σ.map Prod.swap).fst = rMarginal q σ := by
  rw [rMarginal_eq_map hσ, Measure.fst, Measure.map_map measurable_fst measurable_swap]
  rfl

theorem fst_withDensity_fst (τ : Measure (ℝ × ℝ)) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (τ.withDensity fun p => g p.1).fst = τ.fst.withDensity g := by
  ext A hA
  rw [Measure.fst_apply hA, withDensity_apply _ (measurable_fst hA), withDensity_apply _ hA,
    Measure.fst, setLIntegral_map hA hg measurable_fst]

/-- A disintegration in the sense of `IsPhaseDisintegration` is the statement `τ = ρ̃ ⊗ π`. -/
theorem map_swap_eq_compProd {q : ℝ} {σ : Measure (ℝ × ℝ)} [SFinite (rMarginal q σ)]
    (κ : Kernel ℝ ℝ) [IsSFiniteKernel κ]
    (h : ∀ E : Set (ℝ × ℝ), MeasurableSet E →
      σ E = ∫⁻ r, κ r ((fun θ => (θ, r)) ⁻¹' E) ∂(rMarginal q σ)) :
    σ.map Prod.swap = rMarginal q σ ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply measurable_swap hs, h _ (measurable_swap hs),
    Measure.compProd_apply hs]
  rfl

/-! ## `lem:phase-disintegration-exists` for a measure on the cylinder with (A.e3) -/

section General

variable {q : ℝ} {σ : Measure (ℝ × ℝ)}

/-- **Existence**, for every measure on the cylinder with (A.e3). -/
theorem exists_phaseDisintegration (hq : 1 < q) (hσ : σ (cylinder q)ᶜ = 0)
    (hint : IsCylIntegrable σ) : ∃ π : ℝ → Measure ℝ, IsPhaseDisintegration q σ π := by
  haveI := sFinite_rMarginal hσ hint
  haveI := isFiniteMeasure_withDensity_rWeight hσ hint
  set ρ := rMarginal q σ with hρ
  set τ := σ.map Prod.swap with hτ
  set τg := τ.withDensity fun p => rWeight p.1 with hτg
  have hτg_fst : τg.fst = ρ.withDensity rWeight := by
    rw [hτg, fst_withDensity_fst τ measurable_rWeight, hτ, fst_map_swap hσ]
  haveI : IsFiniteMeasure τg := by
    refine ⟨?_⟩
    rw [← Measure.fst_univ, hτg_fst]
    exact measure_lt_top _ _
  set κ := τg.condKernel
  -- `τ = ρ ⊗ κ`
  have hτg_eq : τg = (ρ ⊗ₘ κ).withDensity fun p => rWeight p.1 := by
    rw [← withDensity_compProd_left κ measurable_rWeight, ← hτg_fst]
    exact (τg.disintegrate κ).symm
  have hmw : Measurable fun p : ℝ × ℝ => rWeight p.1 := measurable_rWeight.comp measurable_fst
  have hnull : ∀ ν : Measure (ℝ × ℝ), ν.fst = ρ → ∀ᵐ p ∂ν, rWeight p.1 ≠ 0 := by
    intro ν hν
    have h0 := ae_rWeight_ne_zero hσ
    rw [← hρ, ← hν, Measure.fst] at h0
    exact ae_of_ae_map measurable_fst.aemeasurable h0
  have hτ_eq : τ = ρ ⊗ₘ κ := by
    have h1 : τ = τg.withDensity fun p => (rWeight p.1)⁻¹ :=
      (withDensity_inv_same hmw (hnull τ (by rw [hτ, fst_map_swap hσ]))
        (Eventually.of_forall fun p => rWeight_ne_top _)).symm
    rw [h1, hτg_eq, withDensity_inv_same hmw (hnull _ (Measure.fst_compProd ρ κ))
      (Eventually.of_forall fun p => rWeight_ne_top _)]
  -- `κ_r` is carried by `[1,q)` for `ρ`-a.e. `r`
  have hS : MeasurableSet {r : ℝ | κ r (Ico 1 q)ᶜ = 0} :=
    Kernel.measurable_coe κ measurableSet_Ico.compl (measurableSet_singleton 0)
  have hκae : ∀ᵐ r ∂ρ, κ r (Ico 1 q)ᶜ = 0 := by
    have h0 : ∫⁻ r, κ r (Ico 1 q)ᶜ ∂ρ = 0 := by
      have e := congrArg (fun ν : Measure (ℝ × ℝ) => ν (univ ×ˢ (Ico 1 q)ᶜ)) hτ_eq
      rw [Measure.compProd_apply (MeasurableSet.univ.prod measurableSet_Ico.compl)] at e
      have e2 : ∀ r : ℝ, Prod.mk r ⁻¹' (univ ×ˢ (Ico 1 q)ᶜ) = (Ico 1 q)ᶜ := by
        intro r; ext θ; simp
      simp_rw [e2] at e
      rw [← e, hτ, Measure.map_apply measurable_swap
        (MeasurableSet.univ.prod measurableSet_Ico.compl)]
      refine measure_mono_null (fun p hp => ?_) hσ
      intro hpc
      exact hp.2 hpc.1
    exact (lintegral_eq_zero_iff (Kernel.measurable_coe κ measurableSet_Ico.compl)).1 h0
  let π : Kernel ℝ ℝ := Kernel.piecewise hS κ (Kernel.const ℝ (Measure.dirac 1))
  have hπκ : ∀ᵐ r ∂ρ, π r = κ r :=
    hκae.mono fun r hr => by
      simp only [π, Kernel.piecewise_apply, mem_setOf_eq, hr, if_true]
  refine ⟨π, ⟨π.measurable, fun r => inferInstance, fun r => ?_, fun E hE => ?_⟩⟩
  · by_cases hr : κ r (Ico 1 q)ᶜ = 0
    · simp only [π, Kernel.piecewise_apply, mem_setOf_eq, hr, if_true]
    · simp only [π, Kernel.piecewise_apply, mem_setOf_eq, hr, if_false, Kernel.const_apply]
      rw [Measure.dirac_apply' _ measurableSet_Ico.compl, indicator_of_notMem]
      simp only [mem_compl_iff, mem_Ico, le_refl, true_and, not_not]
      exact hq
  · have e := congrArg (fun ν : Measure (ℝ × ℝ) => ν (Prod.swap ⁻¹' E)) hτ_eq
    rw [hτ, Measure.map_apply measurable_swap (measurable_swap hE),
      Measure.compProd_apply (measurable_swap hE)] at e
    have hpre : Prod.swap ⁻¹' (Prod.swap ⁻¹' E) = E := by
      ext p; simp
    rw [hpre] at e
    rw [e]
    refine lintegral_congr_ae (hπκ.mono fun r hr => ?_)
    simp only [hr]
    rfl

/-- **Uniqueness `ρ̃`-a.e.**, for every measure on the cylinder with (A.e3). -/
theorem phaseDisintegration_ae_eq (hσ : σ (cylinder q)ᶜ = 0) (hint : IsCylIntegrable σ)
    {π π' : ℝ → Measure ℝ} (hπ : IsPhaseDisintegration q σ π)
    (hπ' : IsPhaseDisintegration q σ π') : ∀ᵐ r ∂(rMarginal q σ), π r = π' r := by
  haveI := sFinite_rMarginal hσ hint
  haveI := isFiniteMeasure_withDensity_rWeight hσ hint
  let K : Kernel ℝ ℝ := ⟨π, hπ.measurable⟩
  let K' : Kernel ℝ ℝ := ⟨π', hπ'.measurable⟩
  haveI : IsMarkovKernel K := ⟨hπ.isProbability⟩
  haveI : IsMarkovKernel K' := ⟨hπ'.isProbability⟩
  have h1 := map_swap_eq_compProd K hπ.disintegrates
  have h2 := map_swap_eq_compProd K' hπ'.disintegrates
  have h : (rMarginal q σ).withDensity rWeight ⊗ₘ K =
      (rMarginal q σ).withDensity rWeight ⊗ₘ K' := by
    rw [withDensity_compProd_left K measurable_rWeight,
      withDensity_compProd_left K' measurable_rWeight, ← h1, ← h2]
  have hae : K =ᵐ[(rMarginal q σ).withDensity rWeight] K' := Kernel.ae_eq_of_compProd_eq h
  exact (withDensity_absolutelyContinuous' measurable_rWeight.aemeasurable
    (ae_rWeight_ne_zero hσ)).ae_le hae

end General

/-! ## The node -/

/-- **`lem:phase-disintegration-exists`**, the claims of `def:phase-entropy`. For the pair
`(Λ, ℬ)` of a `q^ℤ`-covariant family, with cylinder measure `σ` and `r`-marginal `ρ̃`:
`ρ̃([r₀,∞)) < ∞` for every `r₀ > 0`; a disintegration `σ(dθ, dr) = π_r(dθ) ρ̃(dr)` into
probability measures on `[1,q)` exists; and any two agree for `ρ̃`-almost every `r`.

The hypothesis `IsQFamily q μ` of the skeleton is not used and was dropped on 2026-11-14, a
strengthening: the proof reads only (i) of the pair (`Λ` on the quadrant, `J`-invariant, with the
integrability). -/
theorem phase_disintegration_exists {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure ℝ)
    (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (hΛ : IsFamilyPair q μ Λ B) :
    (∀ r₀ : ℝ, 0 < r₀ → rMarginal q (cylMeasure q Λ) (Ici r₀) ≠ ⊤) ∧
      (∃ π : ℝ → Measure ℝ, IsPhaseDisintegration q (cylMeasure q Λ) π) ∧
      ∀ π π' : ℝ → Measure ℝ, IsPhaseDisintegration q (cylMeasure q Λ) π →
        IsPhaseDisintegration q (cylMeasure q Λ) π' →
          ∀ᵐ r ∂(rMarginal q (cylMeasure q Λ)), π r = π' r := by
  have hP := hΛ.1
  obtain ⟨hσ, hmix⟩ := cylMeasure_spec hq hP.carried hP.invariant
  have hint : IsCylIntegrable (cylMeasure q Λ) := by
    have := (knot_atom_cascades_2_integrable hq (cylMeasure q Λ) hσ).1
    rw [hmix] at this
    exact this.1 hP.integrable
  exact ⟨fun r₀ hr₀ => rMarginal_Ici_ne_top hσ hint hr₀, exists_phaseDisintegration hq hσ hint,
    fun π π' hπ hπ' => phaseDisintegration_ae_eq hσ hint hπ hπ'⟩

end Pyramids
