/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.StrataCylinderParts
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.Floor

/-!
# `prop:strata-cylinder-coordinates`, part B: measures on the circle `[1,q)`

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:strata-cylinder-coordinates`. Wave 3c. The
circle `(0,∞)/q^ℤ` is read on its fundamental domain `[1,q)`, through `θ ↦ log_q θ mod 1` into
`ℝ/ℤ`. This file proves, once, the two facts about measures on it that the jump part's
(b) ⟹ (c) and clause (3) both read.

* **Fourier uniqueness** (`addCircle_measure_ext`): two finite measures on `ℝ/Tℤ` with the same
  Fourier coefficients are equal. The span of the characters is dense in `C(ℝ/Tℤ, ℂ)` (Mathlib's
  `span_fourier_closure_eq_top`), the integral against a finite measure is continuous in the sup
  norm, and a finite Borel measure on a metric space is determined by the integrals of the bounded
  continuous functions.
* **Transport to `[1,q)`.** `θ ↦ log_q θ mod 1` is injective on `[1,q)` with a measurable inverse
  `u ↦ q^u`, `u ∈ [0,1)`; so two measures carried by `[1,q)` with the same image are equal
  (`eq_of_map_phaseMap`), and the Fourier coefficients of the image are the coefficients
  `∫ e^{2πij log_q θ} ν(dθ)` (`phaseCoeff`) of the measure.
* **Rotations.** The rotation `θ ↦ [λθ]` multiplies the `j`-th coefficient by `e^{2πij log_q λ}`
  (`phaseCoeff_map_qRot`), so a measure invariant under every rotation has no coefficient
  `j ≠ 0` (`phaseCoeff_eq_zero_of_invariant`): take `λ = q^{1/(2j)}`, at which the factor is `-1`.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter
open scoped ENNReal NNReal

/-! ## Fourier uniqueness on `ℝ/Tℤ` -/

/-- The integral against a finite measure on `ℝ/Tℤ`, as a continuous linear functional on
`C(ℝ/Tℤ, ℂ)`. -/
noncomputable def circleIntegralCLM {T : ℝ} [Fact (0 < T)] (m : Measure (AddCircle T))
    [IsFiniteMeasure m] : C(AddCircle T, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 m ℂ)

theorem circleIntegralCLM_apply {T : ℝ} [Fact (0 < T)] (m : Measure (AddCircle T))
    [IsFiniteMeasure m] (f : C(AddCircle T, ℂ)) : circleIntegralCLM m f = ∫ x, f x ∂m := by
  rw [circleIntegralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq' ℂ,
    L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp m f)

/-- **Fourier uniqueness**: two finite measures on `ℝ/Tℤ` with the same Fourier coefficients are
equal. -/
theorem addCircle_measure_ext {T : ℝ} [Fact (0 < T)] {μ ν : Measure (AddCircle T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℤ, ∫ x, fourier n x ∂μ = ∫ x, fourier n x ∂ν) : μ = ν := by
  set Φ := circleIntegralCLM μ - circleIntegralCLM ν with hΦ
  have hspan : Submodule.span ℂ (range (@fourier T)) ≤
      LinearMap.ker (Φ : C(AddCircle T, ℂ) →ₗ[ℂ] ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΦ,
      sub_apply, circleIntegralCLM_apply, h n, sub_self]
  have hcl := Submodule.topologicalClosure_minimal _ hspan (Φ.isClosed_ker)
  rw [span_fourier_closure_eq_top] at hcl
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  let F : C(AddCircle T, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hF : F ∈ LinearMap.ker (Φ : C(AddCircle T, ℂ) →ₗ[ℂ] ℂ) := hcl Submodule.mem_top
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hΦ, sub_apply,
    circleIntegralCLM_apply, sub_eq_zero] at hF
  have e : ∀ m : Measure (AddCircle T), ∫ x, F x ∂m = ((∫ x, f x ∂m : ℝ) : ℂ) := fun m =>
    integral_complex_ofReal
  rw [e, e] at hF
  exact_mod_cast hF

/-! ## The phase `log_q θ mod 1` -/

/-- **The character `θ ↦ e^{2πij log_q θ}`** of the circle `(0,∞)/q^ℤ`. -/
noncomputable def phaseChar (q : ℝ) (j : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (Real.logb q θ : ℂ))

/-- **The Fourier coefficients** `∫ e^{2πij log_q θ} ν(dθ)` of a measure `ν` on `[1,q)`. -/
noncomputable def phaseCoeff (q : ℝ) (ν : Measure ℝ) (j : ℤ) : ℂ := ∫ θ, phaseChar q j θ ∂ν

/-- **`θ ↦ log_q θ mod 1`**, from `[1,q)` onto `ℝ/ℤ`. -/
noncomputable def phaseMap (q θ : ℝ) : AddCircle (1 : ℝ) := (Real.logb q θ : AddCircle (1 : ℝ))

theorem measurable_phaseMap (q : ℝ) : Measurable (phaseMap q) :=
  AddCircle.measurable_mk'.comp (Real.measurable_log.div_const _)

theorem measurable_phaseChar (q : ℝ) (j : ℤ) :
    Measurable (phaseChar q j) := by
  unfold phaseChar
  refine Complex.measurable_exp.comp (measurable_const.mul ?_)
  exact Complex.measurable_ofReal.comp (Real.measurable_log.div_const _)

theorem norm_phaseChar (q : ℝ) (j : ℤ) (θ : ℝ) : ‖phaseChar q j θ‖ = 1 := by
  rw [phaseChar, Complex.norm_exp]
  simp

theorem phaseChar_zero (q θ : ℝ) : phaseChar q 0 θ = 1 := by
  simp [phaseChar]

/-- The Fourier coefficients of the image on `ℝ/ℤ` are those of the measure. -/
theorem integral_fourier_map_phaseMap (q : ℝ) (ν : Measure ℝ) (n : ℤ) :
    ∫ x, fourier n x ∂(ν.map (phaseMap q)) = phaseCoeff q ν n := by
  rw [integral_map (measurable_phaseMap q).aemeasurable
    (fourier n).continuous.aestronglyMeasurable, phaseCoeff]
  refine integral_congr_ae (.of_forall fun θ => ?_)
  simp only [phaseMap, fourier_coe_apply, Complex.ofReal_one, div_one, phaseChar]

/-- `log_q θ ∈ [0,1)` for `θ ∈ [1,q)`. -/
theorem logb_mem_Ico {q : ℝ} (hq : 1 < q) {θ : ℝ} (hθ : θ ∈ Ico 1 q) :
    Real.logb q θ ∈ Ico (0 : ℝ) (0 + 1) := by
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
  rw [zero_add]
  refine ⟨Real.logb_nonneg hq hθ.1, ?_⟩
  rw [Real.logb_lt_iff_lt_rpow hq hθ0, Real.rpow_one]
  exact hθ.2

/-- **Two measures carried by `[1,q)` with the same image on `ℝ/ℤ` are equal**: `u ↦ q^u` on
`[0,1)` inverts `θ ↦ log_q θ mod 1` there. -/
theorem eq_of_map_phaseMap {q : ℝ} (hq : 1 < q) {ν ν' : Measure ℝ} (hν : ν (Ico 1 q)ᶜ = 0)
    (hν' : ν' (Ico 1 q)ᶜ = 0) (h : ν.map (phaseMap q) = ν'.map (phaseMap q)) : ν = ν' := by
  have hq0 : 0 < q := by linarith
  set ψ : AddCircle (1 : ℝ) → ℝ :=
    fun u => q ^ ((AddCircle.equivIco (1 : ℝ) 0 u : Ico (0 : ℝ) (0 + 1)) : ℝ) with hψ
  have hψm : Measurable ψ :=
    (measurable_const.pow (measurable_subtype_coe.comp
      (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable))
  have hinv : ∀ θ ∈ Ico 1 q, ψ (phaseMap q θ) = θ := by
    intro θ hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
    simp only [hψ, phaseMap, AddCircle.equivIco_coe_eq (logb_mem_Ico hq hθ)]
    exact Real.rpow_logb hq0 hq.ne' hθ0
  have key : ∀ m : Measure ℝ, m (Ico 1 q)ᶜ = 0 → (m.map (phaseMap q)).map ψ = m := by
    intro m hm
    rw [Measure.map_map hψm (measurable_phaseMap q)]
    conv_rhs => rw [← Measure.map_id (μ := m)]
    refine Measure.map_congr ?_
    rw [EventuallyEq, ae_iff]
    refine measure_mono_null (fun θ hθ hθI => hθ (hinv θ hθI)) hm
  rw [← key ν hν, ← key ν' hν', h]

/-! ## Rotations -/

theorem measurable_qClass (q : ℝ) : Measurable (qClass q) := by
  unfold qClass dgLevel
  refine Measurable.mul ?_ measurable_id
  exact (measurable_of_countable fun n : ℤ => q ^ (-n)).comp
    (Int.measurable_floor.comp (Real.measurable_log.div_const _))

theorem measurable_qRot (q lam : ℝ) : Measurable (qRot q lam) :=
  (measurable_qClass q).comp (measurable_const_mul lam)

/-- `log_q [y] = log_q y - ⌊log_q y⌋` for `y > 0`. -/
theorem logb_qClass {q : ℝ} (hq : 1 < q) {y : ℝ} (hy : 0 < y) :
    Real.logb q (qClass q y) = Real.logb q y - dgLevel q y := by
  have hq0 : 0 < q := by linarith
  have hl : Real.log q ≠ 0 := (Real.log_pos hq).ne'
  have e : Real.logb q (q ^ (-dgLevel q y)) = -(dgLevel q y : ℝ) := by
    rw [Real.logb, Real.log_zpow, Int.cast_neg, neg_mul, neg_div, mul_div_assoc, div_self hl,
      mul_one]
  rw [qClass, Real.logb_mul (zpow_pos hq0 _).ne' hy.ne', e]
  ring

/-- `e^{2πij log_q [λθ]} = e^{2πij log_q λ} e^{2πij log_q θ}` for `λ, θ > 0`. -/
theorem phaseChar_qRot {q : ℝ} (hq : 1 < q) (j : ℤ) {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ) :
    phaseChar q j (qRot q lam θ) = phaseChar q j lam * phaseChar q j θ := by
  have hlθ : 0 < lam * θ := mul_pos hlam hθ
  rw [qRot, phaseChar, phaseChar, phaseChar, ← Complex.exp_add, logb_qClass hq hlθ,
    Real.logb_mul hlam.ne' hθ.ne']
  have e : (2 * Real.pi * Complex.I * (j : ℂ) *
      (((Real.logb q lam + Real.logb q θ - (dgLevel q (lam * θ) : ℝ)) : ℝ) : ℂ)) =
      (2 * Real.pi * Complex.I * (j : ℂ) * (Real.logb q lam : ℂ) +
        2 * Real.pi * Complex.I * (j : ℂ) * (Real.logb q θ : ℂ)) +
        (-(j * dgLevel q (lam * θ)) : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **A rotation multiplies the coefficients by a character**: for `ν` carried by `(0,∞)`,
`(ν ∘ [λ ·]⁻¹)^_j = e^{2πij log_q λ} ν̂_j`. -/
theorem phaseCoeff_map_qRot {q : ℝ} (hq : 1 < q) {ν : Measure ℝ} (hν : ν (Iic 0) = 0) (j : ℤ)
    {lam : ℝ} (hlam : 0 < lam) :
    phaseCoeff q (ν.map (qRot q lam)) j = phaseChar q j lam * phaseCoeff q ν j := by
  rw [phaseCoeff, integral_map (measurable_qRot q lam).aemeasurable
    (measurable_phaseChar q j).aestronglyMeasurable, phaseCoeff, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_pos_of_Iic_zero hν] with θ hθ
  exact phaseChar_qRot hq j hlam hθ

/-- **A measure invariant under every rotation has no coefficient `j ≠ 0`.** -/
theorem phaseCoeff_eq_zero_of_invariant {q : ℝ} (hq : 1 < q) {ν : Measure ℝ}
    (hν : ν (Iic 0) = 0) (hinv : ∀ lam : ℝ, 0 < lam → ν.map (qRot q lam) = ν) {j : ℤ}
    (hj : j ≠ 0) : phaseCoeff q ν j = 0 := by
  have hq0 : 0 < q := by linarith
  set lam : ℝ := q ^ (1 / (2 * (j : ℝ))) with hlam
  have hl : 0 < lam := Real.rpow_pos_of_pos hq0 _
  have e := phaseCoeff_map_qRot hq hν j hl
  rw [hinv lam hl] at e
  have hchar : phaseChar q j lam = -1 := by
    have hj' : (j : ℝ) ≠ 0 := Int.cast_ne_zero.2 hj
    rw [phaseChar, hlam, Real.logb_rpow hq0 hq.ne']
    have : 2 * Real.pi * Complex.I * (j : ℂ) * (((1 / (2 * (j : ℝ))) : ℝ) : ℂ) =
        Real.pi * Complex.I := by
      have hjc : (j : ℂ) ≠ 0 := Int.cast_ne_zero.2 hj
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  rw [hchar] at e
  have : (2 : ℂ) * phaseCoeff q ν j = 0 := by linear_combination e
  simpa using this

end Pyramids
