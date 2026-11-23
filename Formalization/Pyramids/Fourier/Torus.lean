/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.DiscreteHelmholtz
import Pyramids.Defs.Jet
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.MetricSpace.ThickenedIndicator

/-!
# Fourier series on the phase cube `[-π, π]^d`

Phase 5, wave 3b. A library file: the bridge from the phase cube `phaseCube d` with Lebesgue
measure to Mathlib's torus `UnitAddTorus (Fin d)` and its Hilbert basis `mFourierBasis`. Every
statement a later file reads is about the cube, `gridCoeff` and `volume.restrict (phaseCube d)`;
the torus, with the measure space of Mathlib's `AddCircleMulti` (`instMeasureSpaceUnitAddCircle`,
a local instance here as there), appears only in the proofs and in the operator
`gridMultiplierCLM`.

## The bridge

* `phaseToTorus θ = θ/(2π) mod ℤ^d` and `torusToPhase`, its inverse on `(-π, π]^d`; Lebesgue
  measure on the cube maps to `(2π)^d` times Haar measure (`map_phaseToTorus`), and back
  (`map_torusToPhase`), so both maps are quasi-measure-preserving.
* `integral_torus_eq`, `memLp_comp_phaseToTorus`, `memLp_comp_torusToPhase`: integrals and `Lᵖ`
  membership transfer. `gridCoeff_comp_phaseToTorus`: the coefficients of a function on the torus
  are the `gridCoeff` of its pull-back, with no factor (the `(2π)^{-d}` of `gridCoeff` is the
  volume of the cube).

## What later files read

* Linearity and the elementary coefficients: `gridCoeff_congr_ae`, `gridCoeff_add`, `_sub`,
  `_const_mul`, `_neg`, `_finset_sum`; `gridCoeff_cexp_mul` (a character shifts the coefficients),
  `gridCoeff_cexp` and `gridCoeff_one` (the coefficients of a character), `gridCoeff_conj`,
  `gridCoeff_comp_neg` (reflection), with `setIntegral_comp_neg` and
  `measurePreserving_neg_restrict` on a symmetric set.
* **Uniqueness for integrable functions**: `ae_eq_zero_of_gridCoeff_eq_zero`,
  `ae_eq_of_gridCoeff_eq`, from `torus_ae_eq_zero_of_mFourierCoeff` on the torus. The characters
  are dense in `C(𝕋^d, ℂ)` (Mathlib's `span_mFourier_closure_eq_top`, Stone–Weierstrass), so an
  integrable function with no coefficient integrates every continuous function to `0`, and the
  functions `thickenedIndicator` tend boundedly to the indicator of a closed set.
* **Parseval**: `hasSum_gridCoeff_inner` (inner products), `hasSum_sq_gridCoeff` (norms),
  `memℓp_gridCoeff`. **Riesz–Fischer**: `exists_gridCoeff_eq`.
* **Products and multipliers**: `hasSum_gridCoeff_mul` (the coefficients of a product of two `L²`
  functions are the absolutely convergent convolution of theirs), `gridCoeff_tsum_mul`,
  `gridCoeff_tsum` and `gridCoeff_gridFourier_mul` (an absolutely summable series as a
  multiplier), `memLp_two_mul_of_bound`, `memLp_two_conj`, `integrable_of_memLp_two`.
* **The bounded operator of a bounded multiplier** `m` on `ℓ²(ℤ^d)`: `gridMultiplierCLM`, with
  `isGridMultiplier_gridMultiplierCLM` (it is the operator of `IsGridMultiplier`) and
  `gridMultiplierCLM_apply` (its value, read from any `L²` function with the given coefficients).
-/

set_option autoImplicit false

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace Pyramids

open MeasureTheory Set Filter Complex UnitAddTorus
open scoped ENNReal ComplexConjugate Topology

variable {d : ℕ}

/-! ## The two maps between the cube and the torus -/

/-- **The phase `ϑ` as a point of the torus** `ℝ^d/ℤ^d`: `ϑ ↦ ϑ/(2π) mod ℤ^d`. -/
noncomputable def phaseToTorus (θ : Fin d → ℝ) : UnitAddTorus (Fin d) :=
  fun i => ((θ i / (2 * Real.pi) : ℝ) : UnitAddCircle)

/-- **The representative in `(-π, π]^d`** of a point of the torus. -/
noncomputable def torusToPhase (x : UnitAddTorus (Fin d)) : Fin d → ℝ :=
  fun i => 2 * Real.pi * (AddCircle.equivIoc 1 (-1 / 2) (x i) : ℝ)

theorem measurable_phaseToTorus : Measurable (phaseToTorus (d := d)) :=
  measurable_pi_lambda _ fun i =>
    AddCircle.measurable_mk'.comp ((measurable_pi_apply i).div_const _)

theorem measurable_torusToPhase : Measurable (torusToPhase (d := d)) :=
  measurable_pi_lambda _ fun i =>
    ((measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 (-1 / 2)).measurable).comp
      (measurable_pi_apply i)).const_mul _

theorem phaseToTorus_torusToPhase (x : UnitAddTorus (Fin d)) :
    phaseToTorus (torusToPhase x) = x := by
  funext i
  simp only [phaseToTorus, torusToPhase]
  rw [mul_div_cancel_left₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  exact AddCircle.coe_equivIoc

/-- The half-open cube `(-π, π]^d`. -/
def phaseCubeIoc (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Ioc (-Real.pi) Real.pi

theorem torusToPhase_phaseToTorus {θ : Fin d → ℝ} (hθ : θ ∈ phaseCubeIoc d) :
    torusToPhase (phaseToTorus θ) = θ := by
  funext i
  have hi := hθ i (mem_univ i)
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmem : θ i / (2 * Real.pi) ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
    constructor
    · rw [lt_div_iff₀ hπ]; linarith [hi.1]
    · rw [div_le_iff₀ hπ]; linarith [hi.2]
  simp only [torusToPhase, phaseToTorus]
  rw [AddCircle.equivIoc_coe_of_mem hmem]
  field_simp

theorem phaseCubeIoc_ae_eq : phaseCubeIoc d =ᵐ[volume] phaseCube d := by
  have := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
    (f := fun _ => -Real.pi) (g := fun _ => Real.pi)
  rw [← Set.pi_univ_Icc] at this
  exact this

theorem ae_mem_phaseCubeIoc :
    ∀ᵐ θ ∂(volume.restrict (phaseCube d)), θ ∈ phaseCubeIoc d := by
  rw [← Measure.restrict_congr_set phaseCubeIoc_ae_eq]
  exact ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)

theorem ae_torusToPhase_phaseToTorus :
    ∀ᵐ θ ∂(volume.restrict (phaseCube d)), torusToPhase (phaseToTorus θ) = θ := by
  filter_upwards [ae_mem_phaseCubeIoc] with θ hθ using torusToPhase_phaseToTorus hθ

theorem measurableSet_phaseCube : MeasurableSet (phaseCube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

instance isFiniteMeasure_phaseCube : IsFiniteMeasure (volume.restrict (phaseCube d)) := by
  refine isFiniteMeasure_restrict.2 ?_
  exact ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top).ne

/-! ## The image of Lebesgue measure on the cube -/

/-- The volume of the torus factor, `(2π)^d`, as a scalar on measures. -/
noncomputable def torusScale (d : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi) ^ d)

theorem torusScale_ne_zero : torusScale d ≠ 0 := by
  unfold torusScale
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

theorem torusScale_ne_top : torusScale d ≠ ∞ := ENNReal.ofReal_ne_top

/-- **Lebesgue measure on `[-π, π]^d`, mapped to the torus, is `(2π)^d` times Haar measure.** -/
theorem map_phaseToTorus :
    Measure.map phaseToTorus (volume.restrict (phaseCube d)) =
      torusScale d • (volume : Measure (UnitAddTorus (Fin d))) := by
  ext E hE
  set proj : (Fin d → ℝ) → UnitAddTorus (Fin d) := fun x i => ((x i : ℝ) : UnitAddCircle)
    with hproj
  have hpm : Measurable proj :=
    measurable_pi_lambda _ fun i => AddCircle.measurable_mk'.comp (measurable_pi_apply i)
  set c₀ : ℝ := (2 * Real.pi)⁻¹ with hc₀
  have hc0 : c₀ ≠ 0 := by positivity
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  set B : Set (Fin d → ℝ) := Set.univ.pi fun _ => Icc (-1 / 2 : ℝ) (-1 / 2 + 1) with hB
  set S : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)} with hS
  have hSpi : S = Set.univ.pi fun _ => Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
    ext x; simp [hS]
  have hSB : S =ᵐ[volume] B := by
    rw [hSpi, hB]
    have := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
      (f := fun _ => (-1 / 2 : ℝ)) (g := fun _ => -1 / 2 + 1)
    rw [← Set.pi_univ_Icc] at this
    exact this
  have hpre : phaseToTorus ⁻¹' E ∩ phaseCube d = (c₀ • ·) ⁻¹' (proj ⁻¹' E ∩ B) := by
    ext θ
    simp only [mem_inter_iff, mem_preimage, phaseCube, hB, Set.mem_pi, mem_univ, true_implies,
      mem_Icc]
    have e1 : phaseToTorus θ = proj (c₀ • θ) := by
      funext i
      simp only [phaseToTorus, hproj, Pi.smul_apply, smul_eq_mul, hc₀]
      congr 1
      ring
    rw [e1]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, hc₀]
    rw [show (2 * Real.pi)⁻¹ * θ i = θ i / (2 * Real.pi) by ring, le_div_iff₀ hπ,
      div_le_iff₀ hπ]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [Measure.map_apply measurable_phaseToTorus hE, Measure.restrict_apply
    (measurable_phaseToTorus hE), hpre, Measure.addHaar_preimage_smul _ hc0, Measure.smul_apply,
    smul_eq_mul]
  have hT : (volume : Measure (UnitAddTorus (Fin d))) E = volume (proj ⁻¹' E ∩ S) := by
    have := lintegral_preimage (E.indicator (1 : UnitAddTorus (Fin d) → ℝ≥0∞))
      (fun _ : Fin d => (-1 / 2 : ℝ))
    rw [lintegral_indicator_one hE] at this
    rw [this]
    have h2 : (fun x : Fin d → ℝ => E.indicator (1 : UnitAddTorus (Fin d) → ℝ≥0∞)
        (fun i => ((x i : ℝ) : UnitAddCircle))) = (proj ⁻¹' E).indicator 1 := by
      funext x
      simp only [hproj, indicator, mem_preimage, Pi.one_apply]
      rfl
    rw [h2, lintegral_indicator_one (hpm hE), Measure.restrict_apply (hpm hE)]
  rw [hT, measure_congr ((ae_eq_refl (proj ⁻¹' E)).inter hSB)]
  congr 1
  rw [Module.finrank_fin_fun, hc₀, inv_pow, inv_inv, torusScale,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi) ^ d)]

/-- **Haar measure on the torus, mapped to the cube, is `(2π)^{-d}` times Lebesgue measure.** -/
theorem map_torusToPhase :
    Measure.map torusToPhase (volume : Measure (UnitAddTorus (Fin d))) =
      (torusScale d)⁻¹ • volume.restrict (phaseCube d) := by
  have h1 : Measure.map torusToPhase (Measure.map phaseToTorus (volume.restrict (phaseCube d))) =
      volume.restrict (phaseCube d) := by
    rw [Measure.map_map measurable_torusToPhase measurable_phaseToTorus,
      Measure.map_congr (f := torusToPhase ∘ phaseToTorus) (g := id)
        (ae_torusToPhase_phaseToTorus (d := d)), Measure.map_id]
  rw [map_phaseToTorus, Measure.map_smul] at h1
  rw [← h1, smul_smul, ENNReal.inv_mul_cancel torusScale_ne_zero torusScale_ne_top, one_smul]

theorem quasiMeasurePreserving_phaseToTorus :
    Measure.QuasiMeasurePreserving phaseToTorus (volume.restrict (phaseCube d))
      (volume : Measure (UnitAddTorus (Fin d))) :=
  ⟨measurable_phaseToTorus, by rw [map_phaseToTorus]; exact Measure.smul_absolutelyContinuous⟩

theorem quasiMeasurePreserving_torusToPhase :
    Measure.QuasiMeasurePreserving torusToPhase (volume : Measure (UnitAddTorus (Fin d)))
      (volume.restrict (phaseCube d)) :=
  ⟨measurable_torusToPhase, by rw [map_torusToPhase]; exact Measure.smul_absolutelyContinuous⟩

/-! ## Transfer of integrals, `Lᵖ` membership and coefficients -/

theorem memLp_comp_phaseToTorus {p : ℝ≥0∞} {G : UnitAddTorus (Fin d) → ℂ}
    (hG : MemLp G p volume) : MemLp (G ∘ phaseToTorus) p (volume.restrict (phaseCube d)) := by
  have h1 : MemLp G p (Measure.map phaseToTorus (volume.restrict (phaseCube d))) := by
    rw [map_phaseToTorus]; exact hG.smul_measure torusScale_ne_top
  exact (memLp_map_measure_iff h1.1 measurable_phaseToTorus.aemeasurable).1 h1

theorem memLp_comp_torusToPhase {p : ℝ≥0∞} {F : (Fin d → ℝ) → ℂ}
    (hF : MemLp F p (volume.restrict (phaseCube d))) : MemLp (F ∘ torusToPhase) p volume := by
  have h1 : MemLp F p (Measure.map torusToPhase (volume : Measure (UnitAddTorus (Fin d)))) := by
    rw [map_torusToPhase]; exact hF.smul_measure (ENNReal.inv_ne_top.2 torusScale_ne_zero)
  exact (memLp_map_measure_iff h1.1 measurable_torusToPhase.aemeasurable).1 h1

theorem torusScale_toReal : (torusScale d).toReal = (2 * Real.pi) ^ d := by
  unfold torusScale; rw [ENNReal.toReal_ofReal (by positivity)]

/-- **An integral over the torus is `(2π)^{-d}` times the integral over the cube.** -/
theorem integral_torus_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : UnitAddTorus (Fin d) → E} (hG : AEStronglyMeasurable G volume) :
    ∫ x, G x = (((2 * Real.pi) ^ d)⁻¹ : ℝ) • ∫ θ in phaseCube d, G (phaseToTorus θ) := by
  have h1 : AEStronglyMeasurable G (Measure.map phaseToTorus (volume.restrict (phaseCube d))) := by
    rw [map_phaseToTorus]; exact hG.smul_measure _
  rw [← integral_map measurable_phaseToTorus.aemeasurable h1, map_phaseToTorus,
    integral_smul_measure, smul_smul, torusScale_toReal,
    inv_mul_cancel₀ (by positivity), one_smul]

theorem mFourier_phaseToTorus (n : Zd d) (θ : Fin d → ℝ) :
    mFourier n (phaseToTorus θ) = cexp (((gphase θ n : ℝ) : ℂ) * I) := by
  simp only [mFourier, ContinuousMap.coe_mk, phaseToTorus, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [gphase]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp

/-- **The coefficients of a function on the torus are those of its pull-back to the cube.** -/
theorem gridCoeff_comp_phaseToTorus {G : UnitAddTorus (Fin d) → ℂ}
    (hG : AEStronglyMeasurable G volume) (n : Zd d) :
    gridCoeff (G ∘ phaseToTorus) n = mFourierCoeff G n := by
  rw [mFourierCoeff, integral_torus_eq ((mFourier (-n)).continuous.aestronglyMeasurable.smul hG)]
  simp only [gridCoeff, Function.comp_apply, smul_eq_mul, mFourier_phaseToTorus,
    Complex.real_smul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only
  rw [mul_comm]
  congr 2
  simp only [gphase, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  push_cast
  ring

/-- **The coefficients are insensitive to a null set.** -/
theorem gridCoeff_congr_ae {F G : (Fin d → ℝ) → ℂ}
    (h : F =ᵐ[volume.restrict (phaseCube d)] G) : gridCoeff F = gridCoeff G := by
  funext n
  unfold gridCoeff
  congr 1
  exact integral_congr_ae (h.mono fun θ hθ => by simp only [hθ])

theorem mFourierCoeff_comp_torusToPhase {F : (Fin d → ℝ) → ℂ}
    (hF : AEStronglyMeasurable F (volume.restrict (phaseCube d))) (n : Zd d) :
    mFourierCoeff (F ∘ torusToPhase) n = gridCoeff F n := by
  rw [← gridCoeff_comp_phaseToTorus
    (hF.comp_quasiMeasurePreserving quasiMeasurePreserving_torusToPhase)]
  exact congrFun (gridCoeff_congr_ae (ae_torusToPhase_phaseToTorus.mono fun θ hθ => by
    simp only [Function.comp_apply, hθ])) n

/-! ## Linearity of the coefficients -/

@[fun_prop]
theorem continuous_gphase (n : Zd d) : Continuous fun θ : Fin d → ℝ => gphase θ n := by
  unfold gphase
  fun_prop

theorem norm_cexp_neg_phase (n : Zd d) (θ : Fin d → ℝ) :
    ‖cexp (-(((∑ i, (n i : ℝ) * θ i : ℝ) : ℂ) * I))‖ = 1 := by
  rw [← neg_mul, ← Complex.ofReal_neg]
  exact Complex.norm_exp_ofReal_mul_I _

theorem integrable_gridCoeff_integrand {F : (Fin d → ℝ) → ℂ}
    (hF : Integrable F (volume.restrict (phaseCube d))) (n : Zd d) :
    Integrable (fun θ => F θ * cexp (-(((∑ i, (n i : ℝ) * θ i : ℝ) : ℂ) * I)))
      (volume.restrict (phaseCube d)) :=
  hF.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun θ => (norm_cexp_neg_phase n θ).le)

theorem gridCoeff_add {F G : (Fin d → ℝ) → ℂ} (hF : Integrable F (volume.restrict (phaseCube d)))
    (hG : Integrable G (volume.restrict (phaseCube d))) (n : Zd d) :
    gridCoeff (fun θ => F θ + G θ) n = gridCoeff F n + gridCoeff G n := by
  simp only [gridCoeff, add_mul]
  rw [integral_add (integrable_gridCoeff_integrand hF n) (integrable_gridCoeff_integrand hG n),
    mul_add]

theorem gridCoeff_sub {F G : (Fin d → ℝ) → ℂ} (hF : Integrable F (volume.restrict (phaseCube d)))
    (hG : Integrable G (volume.restrict (phaseCube d))) (n : Zd d) :
    gridCoeff (fun θ => F θ - G θ) n = gridCoeff F n - gridCoeff G n := by
  simp only [gridCoeff, sub_mul]
  rw [integral_sub (integrable_gridCoeff_integrand hF n) (integrable_gridCoeff_integrand hG n),
    mul_sub]

theorem gridCoeff_const_mul (c : ℂ) (F : (Fin d → ℝ) → ℂ) (n : Zd d) :
    gridCoeff (fun θ => c * F θ) n = c * gridCoeff F n := by
  simp only [gridCoeff, mul_assoc]
  rw [integral_const_mul]
  ring

theorem gridCoeff_neg (F : (Fin d → ℝ) → ℂ) (n : Zd d) :
    gridCoeff (fun θ => -F θ) n = -gridCoeff F n := by
  have := gridCoeff_const_mul (-1) F n
  simpa using this

theorem gridCoeff_finset_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin d → ℝ) → ℂ}
    (hF : ∀ j ∈ s, Integrable (F j) (volume.restrict (phaseCube d))) (n : Zd d) :
    gridCoeff (fun θ => ∑ j ∈ s, F j θ) n = ∑ j ∈ s, gridCoeff (F j) n := by
  simp only [gridCoeff, Finset.sum_mul]
  rw [integral_finsetSum s fun j hj => integrable_gridCoeff_integrand (hF j hj) n,
    Finset.mul_sum]

/-- **Multiplication by a character shifts the coefficients.** -/
theorem gridCoeff_cexp_mul (F : (Fin d → ℝ) → ℂ) (m n : Zd d) :
    gridCoeff (fun θ => cexp (((gphase θ m : ℝ) : ℂ) * I) * F θ) n = gridCoeff F (n - m) := by
  unfold gridCoeff
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only
  rw [mul_comm (cexp _) (F θ), mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [gphase, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  push_cast
  ring

/-- **The coefficients of a character**: `δ_{nm}`. -/
theorem gridCoeff_cexp (m n : Zd d) :
    gridCoeff (fun θ => cexp (((gphase θ m : ℝ) : ℂ) * I)) n = if n = m then 1 else 0 := by
  have h1 : (fun θ => cexp (((gphase θ m : ℝ) : ℂ) * I)) =
      (mFourier m : UnitAddTorus (Fin d) → ℂ) ∘ phaseToTorus := by
    funext θ; simp only [Function.comp_apply, mFourier_phaseToTorus]
  have h2 : mFourierBasis.repr (mFourierLp (d := Fin d) 2 m) = lp.single 2 m 1 := by
    have := HilbertBasis.repr_self (mFourierBasis (d := Fin d)) m
    rwa [coe_mFourierBasis] at this
  have h3 := mFourierBasis_repr (mFourierLp (d := Fin d) 2 m) n
  rw [h2, mFourierCoeff_toLp, lp.single_apply, Pi.single_apply] at h3
  rw [h1, gridCoeff_comp_phaseToTorus (mFourier m).continuous.aestronglyMeasurable, ← h3]

theorem gridCoeff_one (n : Zd d) :
    gridCoeff (fun _ => (1 : ℂ)) n = if n = 0 then 1 else 0 := by
  have := gridCoeff_cexp (0 : Zd d) n
  simpa [gphase] using this

/-- **Conjugation**: the coefficients of `F̄` are `n ↦ conj (F̂(-n))`. -/
theorem gridCoeff_conj (F : (Fin d → ℝ) → ℂ) (n : Zd d) :
    gridCoeff (fun θ => conj (F θ)) n = conj (gridCoeff F (-n)) := by
  unfold gridCoeff
  rw [map_mul, Complex.conj_ofReal, ← integral_conj]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, map_neg, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `ϑ ↦ -ϑ` preserves Lebesgue measure on a symmetric set. -/
theorem measurePreserving_neg_restrict {s : Set (Fin d → ℝ)} (hs : MeasurableSet s)
    (hneg : -s = s) :
    MeasurePreserving (fun θ => -θ) (volume.restrict s) (volume.restrict s) := by
  have := (Measure.measurePreserving_neg (volume : Measure (Fin d → ℝ))).restrict_preimage hs
  have e : (Neg.neg ⁻¹' s : Set (Fin d → ℝ)) = -s := rfl
  rw [e, hneg] at this
  exact this

/-- An integral over a symmetric set is invariant under `ϑ ↦ -ϑ`. -/
theorem setIntegral_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set (Fin d → ℝ)} (hs : MeasurableSet s) (hneg : -s = s) (g : (Fin d → ℝ) → E) :
    ∫ θ in s, g (-θ) = ∫ θ in s, g θ :=
  (measurePreserving_neg_restrict hs hneg).integral_comp
    (MeasurableEquiv.neg (Fin d → ℝ)).measurableEmbedding g

theorem neg_phaseCube : -phaseCube d = phaseCube d := by
  ext θ
  simp only [phaseCube, Set.mem_neg, Set.mem_pi, mem_univ, true_implies, Pi.neg_apply, mem_Icc]
  refine forall_congr' fun j => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Reflection**: the coefficients of `ϑ ↦ F(-ϑ)` are `n ↦ F̂(-n)`. -/
theorem gridCoeff_comp_neg (F : (Fin d → ℝ) → ℂ) (n : Zd d) :
    gridCoeff (fun θ => F (-θ)) n = gridCoeff F (-n) := by
  unfold gridCoeff
  congr 1
  rw [← setIntegral_comp_neg measurableSet_phaseCube neg_phaseCube
    (fun θ => F θ * cexp (-(((∑ i, ((-n) i : ℝ) * θ i : ℝ) : ℂ) * I)))]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [Pi.neg_apply, Int.cast_neg]
  congr 3
  push_cast
  simp

/-! ## Uniqueness: an integrable function is determined by its coefficients -/

/-- **On the torus, an integrable function with no Fourier coefficient vanishes a.e.** The
characters span a dense subspace of `C(𝕋^d, ℂ)` (Stone–Weierstrass), integration against an
integrable function is continuous in the sup norm, and the continuous functions
`thickenedIndicator` tend boundedly to the indicator of a closed set. -/
theorem torus_ae_eq_zero_of_mFourierCoeff {G : UnitAddTorus (Fin d) → ℂ}
    (hG : Integrable G volume) (h : ∀ n, mFourierCoeff G n = 0) : G =ᵐ[volume] 0 := by
  have hint : ∀ g : C(UnitAddTorus (Fin d), ℂ), Integrable (fun x => g x * G x) volume :=
    fun g => hG.bdd_mul (c := ‖g‖) g.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => g.norm_coe_le_norm x)
  let Φ : C(UnitAddTorus (Fin d), ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ x, g x * G x
      map_add' := fun g₁ g₂ => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint g₁) (hint g₂)
      map_smul' := fun c g => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hbound : ∀ g, ‖Φ g‖ ≤ (∫ x, ‖G x‖) * ‖g‖ := by
    intro g
    calc ‖Φ g‖ = ‖∫ x, g x * G x‖ := rfl
      _ ≤ ∫ x, ‖g x * G x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖g‖ * ‖G x‖ := by
          refine integral_mono (hint g).norm (hG.norm.const_mul _) fun x => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _)
      _ = (∫ x, ‖G x‖) * ‖g‖ := by rw [integral_const_mul, mul_comm]
  let Φc := Φ.mkContinuous _ hbound
  have hspan : Submodule.span ℂ (range (mFourier (d := Fin d))) ≤
      LinearMap.ker (Φc : C(UnitAddTorus (Fin d), ℂ) →ₗ[ℂ] ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    have := h (-n)
    rw [mFourierCoeff, neg_neg] at this
    simpa [Φc, Φ, smul_eq_mul] using this
  have hall : ∀ g : C(UnitAddTorus (Fin d), ℂ), ∫ x, g x * G x = 0 := by
    intro g
    have hcl := Submodule.topologicalClosure_minimal _ hspan Φc.isClosed_ker
    rw [span_mFourier_closure_eq_top] at hcl
    exact hcl (Submodule.mem_top (x := g))
  refine ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hG fun K hK => ?_
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hδ
  have hδpos : ∀ k, 0 < δ k := fun k => by positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set g : ℕ → C(UnitAddTorus (Fin d), ℂ) := fun k =>
    ⟨fun x => (((thickenedIndicator (hδpos k) K x : NNReal) : ℝ) : ℂ), by fun_prop⟩ with hg
  have hlim := tendsto_integral_of_dominated_convergence (fun x => ‖G x‖)
    (F := fun k x => g k x * G x) (f := fun x => K.indicator G x)
    (fun k => (hint (g k)).1) hG.norm
    (fun k => Eventually.of_forall fun x => by
      simp only [hg, ContinuousMap.coe_mk, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        NNReal.abs_eq]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (by exact_mod_cast thickenedIndicator_le_one (hδpos k) K x))
    (Eventually.of_forall fun x => by
      have h1 := tendsto_pi_nhds.1 (thickenedIndicator_tendsto_indicator_closure hδpos hδlim K) x
      rw [hK.closure_eq] at h1
      have h2 : Tendsto (fun k => (((thickenedIndicator (hδpos k) K x : NNReal) : ℝ) : ℂ))
          atTop (𝓝 (((K.indicator (fun _ => (1 : NNReal)) x : NNReal) : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.comp NNReal.continuous_coe).continuousAt.tendsto.comp h1
      have h3 := h2.mul_const (G x)
      have h4 : (((K.indicator (fun _ => (1 : NNReal)) x : NNReal) : ℝ) : ℂ) * G x =
          K.indicator G x := by
        by_cases hx : x ∈ K <;> simp [hx]
      rw [← h4]
      exact h3)
  simp only [hall, tendsto_const_nhds_iff] at hlim
  rw [← integral_indicator hK.measurableSet]
  exact hlim.symm

/-- **Uniqueness of the coefficients**: an integrable function on `[-π, π]^d` whose coefficients
all vanish vanishes almost everywhere. -/
theorem ae_eq_zero_of_gridCoeff_eq_zero {F : (Fin d → ℝ) → ℂ}
    (hF : Integrable F (volume.restrict (phaseCube d))) (h : ∀ n, gridCoeff F n = 0) :
    F =ᵐ[volume.restrict (phaseCube d)] 0 := by
  have hG : Integrable (F ∘ torusToPhase) volume :=
    memLp_one_iff_integrable.1 (memLp_comp_torusToPhase (memLp_one_iff_integrable.2 hF))
  have h0 := torus_ae_eq_zero_of_mFourierCoeff hG fun n => by
    rw [mFourierCoeff_comp_torusToPhase hF.1, h n]
  have h1 := quasiMeasurePreserving_phaseToTorus.ae_eq h0
  filter_upwards [h1, ae_torusToPhase_phaseToTorus] with θ h1 h2
  simpa [h2] using h1

/-- **Two integrable functions with the same coefficients agree almost everywhere.** -/
theorem ae_eq_of_gridCoeff_eq {F G : (Fin d → ℝ) → ℂ}
    (hF : Integrable F (volume.restrict (phaseCube d)))
    (hG : Integrable G (volume.restrict (phaseCube d))) (h : ∀ n, gridCoeff F n = gridCoeff G n) :
    F =ᵐ[volume.restrict (phaseCube d)] G := by
  have := ae_eq_zero_of_gridCoeff_eq_zero (hF.sub hG) fun n => by
    rw [show (F - G) = fun θ => F θ - G θ from rfl, gridCoeff_sub hF hG, h n, sub_self]
  filter_upwards [this] with θ hθ
  simpa [sub_eq_zero] using hθ

/-! ## Parseval's identity and its converse -/

theorem mFourierCoeff_toLp_comp_torusToPhase {F : (Fin d → ℝ) → ℂ}
    (hF : MemLp F 2 (volume.restrict (phaseCube d))) (n : Zd d) :
    mFourierCoeff ((memLp_comp_torusToPhase hF).toLp _) n = gridCoeff F n := by
  rw [← mFourierCoeff_comp_torusToPhase hF.1 n, mFourierCoeff, mFourierCoeff]
  exact integral_congr_ae ((memLp_comp_torusToPhase hF).coeFn_toLp.mono fun x hx => by
    simp only [hx])

/-- **Parseval's identity**, for inner products: for `F, G ∈ L²([-π, π]^d)`,
`∑ₙ conj (F̂(n)) Ĝ(n) = (2π)^{-d} ∫ conj F · G`. -/
theorem hasSum_gridCoeff_inner {F G : (Fin d → ℝ) → ℂ}
    (hF : MemLp F 2 (volume.restrict (phaseCube d)))
    (hG : MemLp G 2 (volume.restrict (phaseCube d))) :
    HasSum (fun n => conj (gridCoeff F n) * gridCoeff G n)
      ((((2 * Real.pi) ^ d)⁻¹ : ℝ) * ∫ θ in phaseCube d, conj (F θ) * G θ) := by
  have hF' := memLp_comp_torusToPhase hF
  have hG' := memLp_comp_torusToPhase hG
  have key := hasSum_prod_mFourierCoeff (hF'.toLp _) (hG'.toLp _)
  simp only [mFourierCoeff_toLp_comp_torusToPhase hF, mFourierCoeff_toLp_comp_torusToPhase hG]
    at key
  convert key using 1
  have h1 : ∫ t, conj ((hF'.toLp _ : UnitAddTorus (Fin d) → ℂ) t) *
      (hG'.toLp _ : UnitAddTorus (Fin d) → ℂ) t =
      ∫ t, conj ((F ∘ torusToPhase) t) * (G ∘ torusToPhase) t :=
    integral_congr_ae (by
      filter_upwards [hF'.coeFn_toLp, hG'.coeFn_toLp] with t h1 h2
      simp only [h1, h2])
  have hm : AEStronglyMeasurable (fun t => conj ((F ∘ torusToPhase) t) * (G ∘ torusToPhase) t)
      (volume : Measure (UnitAddTorus (Fin d))) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable hF'.1).mul hG'.1
  rw [h1, integral_torus_eq hm, Complex.real_smul]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_torusToPhase_phaseToTorus] with θ hθ
  simp only [Function.comp_apply, hθ]

/-- **Parseval's identity**: `∑ₙ |F̂(n)|² = (2π)^{-d} ∫ |F|²`. -/
theorem hasSum_sq_gridCoeff {F : (Fin d → ℝ) → ℂ}
    (hF : MemLp F 2 (volume.restrict (phaseCube d))) :
    HasSum (fun n => ‖gridCoeff F n‖ ^ 2)
      (((2 * Real.pi) ^ d)⁻¹ * ∫ θ in phaseCube d, ‖F θ‖ ^ 2) := by
  have h := hasSum_gridCoeff_inner hF hF
  simp_rw [Complex.conj_mul'] at h
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · funext n; push_cast; rfl
  · rw [show (fun θ => ((‖F θ‖ : ℂ)) ^ 2) = fun θ => ((‖F θ‖ ^ 2 : ℝ) : ℂ) from
      funext fun θ => by push_cast; rfl, integral_complex_ofReal]
    push_cast
    rfl

/-- The coefficients of an `L²` function are square-summable. -/
theorem memℓp_gridCoeff {F : (Fin d → ℝ) → ℂ}
    (hF : MemLp F 2 (volume.restrict (phaseCube d))) : Memℓp (gridCoeff F) 2 := by
  refine memℓp_gen ?_
  have := (hasSum_sq_gridCoeff hF).summable
  refine this.congr fun n => ?_
  all_goals norm_num

/-- **Riesz–Fischer**: every square-summable sequence is the coefficient sequence of an `L²`
function on `[-π, π]^d`. -/
theorem exists_gridCoeff_eq (w : Zd d → ℂ) (hw : Memℓp w 2) :
    ∃ F : (Fin d → ℝ) → ℂ, MemLp F 2 (volume.restrict (phaseCube d)) ∧
      ∀ n, gridCoeff F n = w n := by
  set g := (mFourierBasis (d := Fin d)).repr.symm ⟨w, hw⟩
  refine ⟨(g : UnitAddTorus (Fin d) → ℂ) ∘ phaseToTorus, memLp_comp_phaseToTorus (Lp.memLp g),
    fun n => ?_⟩
  rw [gridCoeff_comp_phaseToTorus (Lp.aestronglyMeasurable g), ← mFourierBasis_repr,
    LinearIsometryEquiv.apply_symm_apply]

/-! ## Products and multipliers -/

theorem integrable_of_memLp_two {F : (Fin d → ℝ) → ℂ}
    (hF : MemLp F 2 (volume.restrict (phaseCube d))) :
    Integrable F (volume.restrict (phaseCube d)) :=
  hF.integrable one_le_two

/-- A bounded measurable multiple of an `L²` function is in `L²`. -/
theorem memLp_two_mul_of_bound {m F : (Fin d → ℝ) → ℂ}
    (hm : AEStronglyMeasurable m (volume.restrict (phaseCube d))) {C : ℝ}
    (hC : ∀ θ, ‖m θ‖ ≤ C) (hF : MemLp F 2 (volume.restrict (phaseCube d))) :
    MemLp (fun θ => m θ * F θ) 2 (volume.restrict (phaseCube d)) :=
  hF.of_le_mul (c := C) (hm.mul hF.1) (Eventually.of_forall fun θ => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC θ) (norm_nonneg _))

theorem memLp_two_conj {F : (Fin d → ℝ) → ℂ} (hF : MemLp F 2 (volume.restrict (phaseCube d))) :
    MemLp (fun θ => conj (F θ)) 2 (volume.restrict (phaseCube d)) :=
  hF.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hF.1)
    (Eventually.of_forall fun θ => by simp)

/-- **The coefficients of a product of two `L²` functions** are the convolution of theirs:
`(FG)^(n) = ∑ₘ F̂(m) Ĝ(n - m)`, the series converging absolutely. -/
theorem hasSum_gridCoeff_mul {F G : (Fin d → ℝ) → ℂ}
    (hF : MemLp F 2 (volume.restrict (phaseCube d)))
    (hG : MemLp G 2 (volume.restrict (phaseCube d))) (n : Zd d) :
    HasSum (fun m => gridCoeff F m * gridCoeff G (n - m)) (gridCoeff (fun θ => F θ * G θ) n) := by
  set A : (Fin d → ℝ) → ℂ := fun θ => cexp (((gphase θ n : ℝ) : ℂ) * I) * conj (G θ) with hA
  have hAm : MemLp A 2 (volume.restrict (phaseCube d)) :=
    memLp_two_mul_of_bound (C := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (fun θ => (Complex.norm_exp_ofReal_mul_I _).le) (memLp_two_conj hG)
  have h := hasSum_gridCoeff_inner hAm hF
  have hcA : ∀ m, conj (gridCoeff A m) = gridCoeff G (n - m) := by
    intro m
    rw [hA, gridCoeff_cexp_mul, gridCoeff_conj, Complex.conj_conj, neg_sub]
  simp only [hcA] at h
  have hv : (((2 * Real.pi) ^ d)⁻¹ : ℝ) * ∫ θ in phaseCube d, conj (A θ) * F θ =
      gridCoeff (fun θ => F θ * G θ) n := by
    unfold gridCoeff
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hA, map_mul, Complex.conj_conj, ← Complex.exp_conj, Complex.conj_ofReal,
      Complex.conj_I, gphase]
    rw [show (((∑ i, (n i : ℝ) * θ i : ℝ) : ℂ) * -I) = -(((∑ i, (n i : ℝ) * θ i : ℝ) : ℂ) * I)
      by ring]
    ring
  rw [hv] at h
  exact h.congr_fun fun m => mul_comm _ _

/-- **A summable series times an integrable function**: if `∑|k(m)| < ∞`, the coefficients of
`(∑ₘ k(m) e^{i⟨m,ϑ⟩}) F` are the convolution `k * F̂`. -/
theorem gridCoeff_tsum_mul {k : Zd d → ℂ} (hk : Summable fun m => ‖k m‖)
    {F : (Fin d → ℝ) → ℂ} (hF : Integrable F (volume.restrict (phaseCube d))) (n : Zd d) :
    gridCoeff (fun θ => (∑' m, k m * cexp (((gphase θ m : ℝ) : ℂ) * I)) * F θ) n =
      ∑' m, k m * gridCoeff F (n - m) := by
  set E : Zd d → (Fin d → ℝ) → ℂ := fun m θ => cexp (((gphase θ m : ℝ) : ℂ) * I) with hE
  set e : (Fin d → ℝ) → ℂ := fun θ => cexp (-(((∑ i, (n i : ℝ) * θ i : ℝ) : ℂ) * I)) with he
  have hEn : ∀ m θ, ‖E m θ‖ = 1 := fun m θ => Complex.norm_exp_ofReal_mul_I _
  have hEc : ∀ m, Continuous (E m) := fun m => by simp only [hE]; fun_prop
  have hFe : Integrable (fun θ => F θ * e θ) (volume.restrict (phaseCube d)) :=
    integrable_gridCoeff_integrand hF n
  set g : Zd d → (Fin d → ℝ) → ℂ := fun m θ => k m * E m θ * (F θ * e θ) with hg
  have hgi : ∀ m, Integrable (g m) (volume.restrict (phaseCube d)) := fun m =>
    hFe.bdd_mul (c := ‖k m‖) ((continuous_const.mul (hEc m)).aestronglyMeasurable)
      (Eventually.of_forall fun θ => by rw [norm_mul, hEn, mul_one])
  have hgn : ∀ m, ∫ θ in phaseCube d, ‖g m θ‖ = ‖k m‖ * ∫ θ in phaseCube d, ‖F θ‖ := by
    intro m
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hg, he, norm_mul, hEn, norm_cexp_neg_phase, mul_one]
  have hsum : Summable fun m => ∫ θ in phaseCube d, ‖g m θ‖ := by
    simp only [hgn]
    exact hk.mul_right _
  have hpt : ∀ θ, (∑' m, k m * E m θ) * F θ * e θ = ∑' m, g m θ := by
    intro θ
    rw [mul_assoc, ← tsum_mul_right]
  have hI : gridCoeff (fun θ => (∑' m, k m * E m θ) * F θ) n =
      ((((2 * Real.pi) ^ d)⁻¹ : ℝ) : ℂ) * ∫ θ in phaseCube d, ∑' m, g m θ := by
    unfold gridCoeff
    congr 1
    exact integral_congr_ae (Eventually.of_forall hpt)
  rw [show (fun θ => (∑' m, k m * cexp (((gphase θ m : ℝ) : ℂ) * I)) * F θ) =
    fun θ => (∑' m, k m * E m θ) * F θ from rfl, hI]
  rw [← integral_tsum_of_summable_integral_norm hgi hsum, ← tsum_mul_left]
  congr 1
  funext m
  rw [← gridCoeff_cexp_mul F m n, ← gridCoeff_const_mul]
  unfold gridCoeff
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [hg, hE, he]
  ring

/-- The coefficients of an absolutely convergent series are its terms. -/
theorem gridCoeff_tsum {k : Zd d → ℂ} (hk : Summable fun m => ‖k m‖) (n : Zd d) :
    gridCoeff (fun θ => ∑' m, k m * cexp (((gphase θ m : ℝ) : ℂ) * I)) n = k n := by
  have h := gridCoeff_tsum_mul hk (F := fun _ => 1) (integrable_const _) n
  simp only [mul_one, gridCoeff_one, sub_eq_zero] at h
  rw [h, tsum_eq_single n fun m hm => by simp [Ne.symm hm]]
  simp

/-- **The series of a summable real kernel times an integrable function**: the coefficients of
`λ̂ F` are the convolution `λ * F̂`. -/
theorem gridCoeff_gridFourier_mul {lam : Zd d → ℝ} (hl : Summable lam)
    {F : (Fin d → ℝ) → ℂ} (hF : Integrable F (volume.restrict (phaseCube d))) (n : Zd d) :
    gridCoeff (fun θ => gridFourier lam θ * F θ) n = ∑' m, (lam m : ℂ) * gridCoeff F (n - m) := by
  have hk : Summable fun m => ‖(lam m : ℂ)‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using summable_abs_iff.2 hl
  exact gridCoeff_tsum_mul hk hF n

/-! ## The bounded operator defined by a bounded multiplier -/

/-- The multiplier `m`, read on the torus, as an element of `L^∞`. -/
noncomputable def torusMultiplierLp (m : (Fin d → ℝ) → ℂ)
    (hm : AEStronglyMeasurable m (volume.restrict (phaseCube d))) (C : ℝ) (hC : ∀ θ, ‖m θ‖ ≤ C) :
    Lp ℂ ∞ (volume : Measure (UnitAddTorus (Fin d))) :=
  (memLp_top_of_bound (hm.comp_quasiMeasurePreserving quasiMeasurePreserving_torusToPhase) C
    (Eventually.of_forall fun _ => hC _)).toLp _

/-- **The operator on `ℓ²(ℤ^d)` with a bounded multiplier `m`**: `w ↦ (m ŵ)^∨`, through the
Hilbert basis of `L²(𝕋^d)`. -/
noncomputable def gridMultiplierCLM (m : (Fin d → ℝ) → ℂ)
    (hm : AEStronglyMeasurable m (volume.restrict (phaseCube d))) (C : ℝ) (hC : ∀ θ, ‖m θ‖ ≤ C) :
    ell2C d →L[ℂ] ell2C d :=
  (mFourierBasis (d := Fin d)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.holderL volume ∞ 2 2 (ContinuousLinearMap.mul ℂ ℂ)
        (torusMultiplierLp m hm C hC)).comp
      (mFourierBasis (d := Fin d)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem gridMultiplierCLM_spec (m : (Fin d → ℝ) → ℂ)
    (hm : AEStronglyMeasurable m (volume.restrict (phaseCube d))) (C : ℝ) (hC : ∀ θ, ‖m θ‖ ≤ C)
    (w : ell2C d) :
    MemLp ((((mFourierBasis (d := Fin d)).repr.symm w : Lp ℂ 2 _) : UnitAddTorus (Fin d) → ℂ) ∘
        phaseToTorus) 2 (volume.restrict (phaseCube d)) ∧
    (∀ n, gridCoeff ((((mFourierBasis (d := Fin d)).repr.symm w : Lp ℂ 2 _) :
        UnitAddTorus (Fin d) → ℂ) ∘ phaseToTorus) n = w n) ∧
    ∀ n, gridMultiplierCLM m hm C hC w n = gridCoeff (fun θ => m θ *
        ((((mFourierBasis (d := Fin d)).repr.symm w : Lp ℂ 2 _) : UnitAddTorus (Fin d) → ℂ) ∘
          phaseToTorus) θ) n := by
  set g := (mFourierBasis (d := Fin d)).repr.symm w with hgdef
  refine ⟨memLp_comp_phaseToTorus (Lp.memLp g), fun n => ?_, fun n => ?_⟩
  · rw [gridCoeff_comp_phaseToTorus (Lp.aestronglyMeasurable g), ← mFourierBasis_repr, hgdef,
      LinearIsometryEquiv.apply_symm_apply]
  · set σ := torusMultiplierLp m hm C hC with hσ
    set H := ContinuousLinearMap.holder 2 (ContinuousLinearMap.mul ℂ ℂ) σ g with hH
    have hT : gridMultiplierCLM m hm C hC w = (mFourierBasis (d := Fin d)).repr H := by
      simp only [gridMultiplierCLM, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.holderL_apply_apply, hH, hgdef]
      rfl
    rw [hT, mFourierBasis_repr, ← gridCoeff_comp_phaseToTorus (Lp.aestronglyMeasurable H)]
    refine congrFun (gridCoeff_congr_ae ?_) n
    have h1 := quasiMeasurePreserving_phaseToTorus.ae_eq
      (ContinuousLinearMap.coeFn_holder (r := 2) (ContinuousLinearMap.mul ℂ ℂ) σ g)
    have h2 := quasiMeasurePreserving_phaseToTorus.ae_eq
      ((memLp_top_of_bound (hm.comp_quasiMeasurePreserving quasiMeasurePreserving_torusToPhase) C
        (Eventually.of_forall fun _ => hC _)).coeFn_toLp)
    filter_upwards [h1, h2, ae_torusToPhase_phaseToTorus] with θ h1 h2 h3
    simp only [Function.comp_apply, ContinuousLinearMap.mul_apply'] at h1 h2 ⊢
    rw [h1, hσ, torusMultiplierLp, h2, h3]

/-- **`gridMultiplierCLM` is the operator of the multiplier** in the relational reading. -/
theorem isGridMultiplier_gridMultiplierCLM (m : (Fin d → ℝ) → ℂ)
    (hm : AEStronglyMeasurable m (volume.restrict (phaseCube d))) (C : ℝ) (hC : ∀ θ, ‖m θ‖ ≤ C)
    (w : ell2C d) : IsGridMultiplier m ⇑w ⇑(gridMultiplierCLM m hm C hC w) := by
  obtain ⟨h1, h2, h3⟩ := gridMultiplierCLM_spec m hm C hC w
  exact ⟨_, h1, h2, fun n => (h3 n).symm⟩

/-- **The value of the operator** at `w`, read from any `L²` function with coefficients `w`. -/
theorem gridMultiplierCLM_apply (m : (Fin d → ℝ) → ℂ)
    (hm : AEStronglyMeasurable m (volume.restrict (phaseCube d))) (C : ℝ) (hC : ∀ θ, ‖m θ‖ ≤ C)
    (w : ell2C d) {F : (Fin d → ℝ) → ℂ} (hF : MemLp F 2 (volume.restrict (phaseCube d)))
    (hFw : ∀ n, gridCoeff F n = w n) (n : Zd d) :
    gridMultiplierCLM m hm C hC w n = gridCoeff (fun θ => m θ * F θ) n := by
  obtain ⟨h1, h2, h3⟩ := gridMultiplierCLM_spec m hm C hC w
  rw [h3]
  refine congrFun (gridCoeff_congr_ae ?_) n
  have := ae_eq_of_gridCoeff_eq (integrable_of_memLp_two h1) (integrable_of_memLp_two hF)
    fun n => by rw [h2, hFw]
  filter_upwards [this] with θ hθ
  rw [hθ]

end Pyramids
