/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.LineAxiomsKernels
import Pyramids.Pyramid.DiscreteCovarianceLevy

/-!
# `lem:discrete-covariance-line`: discrete covariance in Lévy coordinates, on the line

Blueprint: `blueprint/src/parts/02-line.tex`, `lem:discrete-covariance-line`. Wave 2e: the three
declarations moved here from `PyramidsSkeleton.Ch02Line`, their statements unchanged.

## The route

The printed one, read on the line's own folded data.

* **The line inside `ℝ¹`.** A family of laws on `ℝ` is carried to `ℝ¹` by `x ↦ xe₀`, where the
  next chapter's lemmas apply at `d = 1`, and back by `y ↦ y₀` (`isLawHemigroup_lineEmb`,
  `isSymmetricFamily_lineEmb`, `isCovariantAt_lineEmb`). So every step `μ_{s,t}` of a family with
  (I1) and (I2) on `ℝ` is infinitely divisible (`lem:family-structure`), and two `q`-covariant
  families agreeing on `[1, q)` agree (`lem:discrete-covariance-levy`).
* **(A8 at `q^ℤ`) and the exponents.** (A8) at `q` with `S_q t = qt` is `q`-covariance of the
  kernels (`lem:line-axioms-kernels`(3)), and covariance at `q` gives the bijections at every
  `qⁿ` (`line_axioms_kernels_qcov`). `q`-covariance at the pairs `(0, t)` is
  `Ψ_{qt}(ω) = Ψ_t(qω)`; conversely the transforms of the steps are `e^{-(Ψ_t - Ψ_s)}`, which the
  condition carries from `(s, t)` at `qω` to `(qs, qt)` at `ω`.
* **The exponents and the folded data.** `Ψ_t(q ·)` has the folded data `(q²a(t), T_qϖ_t)`
  (`lem:line-exponent-data`(2)), and a folded pair is determined by its exponent
  (`lem:line-exponent-data`(1)). No cited fact is used directly: A39 and A41 enter through
  `lem:family-structure`, `lem:line-exponent-data` and `lem:discrete-covariance-levy`.
* **"Then".** The residual is `T_{q⁻¹}μ_{t,qt}`. The data are nondecreasing in `t`:
  `Ψ_{qt} - Ψ_t` is the exponent of the symmetric infinitely divisible step `μ_{t,qt}`, so
  `lem:line-exponent-data`(3) gives `ϖ_t ≤ ϖ_{qt} = T_qϖ_t`.
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X CascadeCore IsScaleCovariant IsKernelFamily SymLevyPair IsSymLevyExponent
  mconvL1)
open scoped Topology ComplexOrder

/-! ## The line inside `ℝ¹` -/

/-- `y₀` of `x e₀` is `x`: the image of a law under `x ↦ xe₀`, read back by `y ↦ y₀`. -/
theorem map_lineProj_lineEmb (m : Measure ℝ) : (m.map lineEmbL).map lineProjL = m := by
  rw [Measure.map_map lineProjL.continuous.measurable lineEmbL.continuous.measurable]
  have h : (lineProjL ∘ lineEmbL : ℝ → ℝ) = id :=
    funext fun x => by simp [lineProjL_apply, lineEmbL_apply, lineEmb_apply_zero]
  rw [h, Measure.map_id]

/-- The image under `x ↦ xe₀` is injective on measures. -/
theorem map_lineEmb_injective {m m' : Measure ℝ} (h : m.map lineEmbL = m'.map lineEmbL) :
    m = m' := by
  rw [← map_lineProj_lineEmb m, h, map_lineProj_lineEmb]

/-- **(I1) and (I2) on `ℝ` carry to `ℝ¹`.** -/
theorem isLawHemigroup_lineEmb {μ : ℝ → ℝ → Measure ℝ} (hμ : IsLawHemigroup μ) :
    IsLawHemigroup (fun s t => (μ s t).map lineEmbL) := by
  refine ⟨fun s t hs hst => ?_, fun t ht => ?_, fun r s t hr hrs hst => ?_, fun ω => ?_⟩
  · haveI := hμ.isProbability s t hs hst
    exact Measure.isProbabilityMeasure_map lineEmbL.continuous.measurable.aemeasurable
  · rw [hμ.diag t ht, Measure.map_dirac' lineEmbL.continuous.measurable, map_zero]
  · haveI := hμ.isProbability s t (hr.trans hrs) hst
    haveI := hμ.isProbability r s hr hrs
    rw [hμ.cascade r s t hr hrs hst, Measure.map_conv_continuousLinearMap]
  · simp only [charFun_map_lineEmb]
    exact hμ.continuous (ω 0)

/-- **A symmetric family on `ℝ` is one on `ℝ¹`.** -/
theorem isSymmetricFamily_lineEmb {μ : ℝ → ℝ → Measure ℝ} (hμ : IsSymmetricFamily μ) :
    IsSymmetricFamily (fun s t => (μ s t).map lineEmbL) := by
  refine ⟨isLawHemigroup_lineEmb hμ.1, fun s t hs hst h0 => ?_, fun s t hs hst => ?_⟩
  · apply hμ.2.1 s t hs hst
    have h1 := congrArg (fun m : Measure (Rd 1) => m.map lineProjL) h0
    simp only [map_lineProj_lineEmb] at h1
    rw [h1, Measure.map_dirac' lineProjL.continuous.measurable, map_zero]
  · simp only
    rw [Measure.map_map measurable_neg lineEmbL.continuous.measurable]
    have e : ((fun x : Rd 1 => -x) ∘ lineEmbL) = lineEmbL ∘ fun x : ℝ => -x :=
      funext fun x => (map_neg lineEmbL x).symm
    rw [e, ← Measure.map_map lineEmbL.continuous.measurable measurable_neg, hμ.2.2 s t hs hst]

/-- **Covariance carries to `ℝ¹`.** -/
theorem isCovariantAt_lineEmb {μ : ℝ → ℝ → Measure ℝ} {lam : ℝ} {S : ℝ → ℝ}
    (h : IsCovariantAt μ lam S) : IsCovariantAt (fun s t => (μ s t).map lineEmbL) lam S := by
  refine ⟨h.1, fun s t hs hst => ?_⟩
  simp only
  rw [Measure.map_map (continuous_const_smul lam).measurable lineEmbL.continuous.measurable]
  have e : ((fun x : Rd 1 => lam • x) ∘ lineEmbL) = lineEmbL ∘ fun x : ℝ => lam • x :=
    funext fun x => (map_smul lineEmbL lam x).symm
  rw [e, ← Measure.map_map lineEmbL.continuous.measurable (continuous_const_smul lam).measurable,
    h.2 s t hs hst]

/-- **Every step of a family with (I1) and (I2) on `ℝ` is infinitely divisible**:
`lem:family-structure` at `d = 1`, through `ℝ¹`. -/
theorem isLawHemigroup_line_infinitelyDivisible {μ : ℝ → ℝ → Measure ℝ} (hμ : IsLawHemigroup μ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : IsInfinitelyDivisible (μ s t) := by
  have h1 : IsInfinitelyDivisible ((μ s t).map lineEmbL) :=
    isLawHemigroup_infinitelyDivisible le_rfl (isLawHemigroup_lineEmb hμ) s t hs hst
  have h2 := isInfinitelyDivisible_map_lineProj h1
  rwa [map_lineProj_lineEmb] at h2

/-- **The dilate of an infinitely divisible law on `ℝ`** is infinitely divisible. -/
theorem isInfinitelyDivisible_map_mul {m : Measure ℝ} (h : IsInfinitelyDivisible m) (c : ℝ) :
    IsInfinitelyDivisible (m.map fun x => c * x) := by
  have h1 := isInfinitelyDivisible_map_lineProj
    (isInfinitelyDivisible_map_smul (isInfinitelyDivisible_map_lineEmb h) c)
  have e : ((m.map lineEmbL).map fun y : Rd 1 => c • y).map lineProjL = m.map fun x => c * x := by
    rw [Measure.map_map (continuous_const_smul c).measurable lineEmbL.continuous.measurable,
      Measure.map_map lineProjL.continuous.measurable
        ((continuous_const_smul c).comp lineEmbL.continuous).measurable]
    congr 1
    funext x
    simp [lineProjL_apply, lineEmbL_apply, lineEmb_apply_zero]
  rwa [e] at h1

/-! ## Folded data along a family -/

/-- **The transform of a step from the folded data of the kernels**:
`μ̂_{s,t} = e^{-(Ψ_t - Ψ_s)}`, from (I1). -/
theorem charFun_step_of_folded {μ : ℝ → ℝ → Measure ℝ} (hμ : IsLawHemigroup μ)
    {P : ℝ → SymLevyPair} (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ω : ℝ) :
    charFun (μ s t) ω = ((Real.exp (-((P t).exponent ω - (P s).exponent ω)) : ℝ) : ℂ) := by
  have h := charFun_kernel_mul_gen hμ hs hst ω
  rw [hP t (hs.trans hst) ω, hP s hs ω] at h
  have hne : ((Real.exp (-(P s).exponent ω) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  rw [eq_div_of_mul_eq hne h.symm, ← Complex.ofReal_div, ← Real.exp_sub]
  congr 2
  ring

/-- **The zero pair**, with exponent `0`. -/
noncomputable def SymLevyPair_zero : SymLevyPair where
  a := 0
  ν := 0
  a_nonneg := le_rfl
  ν_folded := by simp [ScaleSpace.IsFolded]
  ν_integrable := by simp

theorem SymLevyPair_zero_exponent (ω : ℝ) : SymLevyPair_zero.exponent ω = 0 := by
  simp [SymLevyPair.exponent, SymLevyPair.exponentL, SymLevyPair_zero]

/-- **The folded data at scale `0` vanish**: `μ_{0,0} = δ₀`. -/
theorem foldedData_zero {μ : ℝ → ℝ → Measure ℝ} (hμ : IsLawHemigroup μ) {P : SymLevyPair}
    (hP : IsFoldedData (μ 0 0) P) : (∀ ω : ℝ, P.exponent ω = 0) ∧ P.a = 0 ∧ P.ν = 0 := by
  have hz : ∀ ω : ℝ, P.exponent ω = 0 := by
    intro ω
    have h := hP ω
    rw [hμ.diag 0 le_rfl, charFun_dirac] at h
    simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h
    have h2 : Real.exp (-P.exponent ω) = 1 := by exact_mod_cast h.symm
    have := Real.exp_eq_one_iff _ |>.1 h2
    linarith
  obtain ⟨ha, hν⟩ := line_exponent_data_1_unique (fun _ => 0) P SymLevyPair_zero
    (fun ω => (hz ω).symm) fun ω => (SymLevyPair_zero_exponent ω).symm
  exact ⟨hz, ha, hν⟩

/-- **The exponent condition and the data.** `Ψ_{qt}(ω) = Ψ_t(qω)` for all `ω` iff
`a(qt) = q²a(t)` and `ϖ_{qt} = T_qϖ_t`. -/
theorem exponent_dilate_iff (P P' : SymLevyPair) {q : ℝ} (hq : 0 < q) :
    (∀ ω : ℝ, P'.exponent ω = P.exponent (q * ω)) ↔
      P'.a = q ^ 2 * P.a ∧ P'.ν = P.ν.map (fun v => q * v) := by
  obtain ⟨Q, hQa, hQν, hQ⟩ := line_exponent_data_2 P.exponent P (fun _ => rfl) hq
  constructor
  · intro h
    obtain ⟨ha, hν⟩ := line_exponent_data_1_unique (fun ω => P.exponent (q * ω)) P' Q
      (fun ω => (h ω).symm) hQ
    exact ⟨ha.trans hQa, hν.trans hQν⟩
  · rintro ⟨ha, hν⟩ ω
    have h1 : P'.exponent ω = Q.exponent ω := by
      simp only [SymLevyPair.exponent, SymLevyPair.exponentL, ha, hν, hQa, hQν]
    rw [h1]
    exact (hQ ω).symm

/-- **Covariance at `q` with `S_q t = qt`, in the exponents.** -/
theorem covariantAt_iff_folded {μ : ℝ → ℝ → Measure ℝ} (hμ : IsSymmetricFamily μ)
    {P : ℝ → SymLevyPair} (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {q : ℝ}
    (hq : 0 < q) :
    IsCovariantAt μ q (fun t => q * t) ↔
      ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ, (P (q * t)).exponent ω = (P t).exponent (q * ω) := by
  constructor
  · intro hcov t ht ω
    have hk : (μ 0 t).map (fun x => q • x) = μ 0 (q * t) := cov_kernel hcov ht
    have h1 := congrArg (fun m => charFun m ω) hk
    simp only [smul_eq_mul] at h1
    rw [charFun_map_mul, hP t ht, hP (q * t) (by positivity)] at h1
    have h2 := Real.exp_injective (Complex.ofReal_injective h1)
    linarith
  · intro hE
    refine ⟨⟨fun t ht => mul_nonneg hq.le ht, fun u _ v _ huv => mul_lt_mul_of_pos_left huv hq,
      fun t ht => ⟨t / q, div_nonneg ht hq.le, mul_div_cancel₀ t hq.ne'⟩⟩, fun s t hs hst => ?_⟩
    have hqs : 0 ≤ q * s := by positivity
    have hqst : q * s ≤ q * t := mul_le_mul_of_nonneg_left hst hq.le
    haveI := hμ.1.isProbability s t hs hst
    haveI := hμ.1.isProbability (q * s) (q * t) hqs hqst
    haveI : IsProbabilityMeasure ((μ s t).map fun x => q • x) :=
      Measure.isProbabilityMeasure_map (continuous_const_smul q).measurable.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    change charFun ((μ s t).map fun x => q • x) ω = charFun (μ (q * s) (q * t)) ω
    rw [charFun_map_smul, charFun_step_of_folded hμ.1 hP hs hst,
      charFun_step_of_folded hμ.1 hP hqs hqst, smul_eq_mul, hE t (hs.trans hst), hE s hs]

/-- **The data are nondecreasing**: `ϖ_s ≤ ϖ_t` and `a(s) ≤ a(t)` for `s ≤ t`, since
`Ψ_t - Ψ_s` is the exponent of the symmetric infinitely divisible step `μ_{s,t}`. -/
theorem foldedData_mono {μ : ℝ → ℝ → Measure ℝ} (hμ : IsSymmetricFamily μ)
    {P : ℝ → SymLevyPair} (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : (P s).a ≤ (P t).a ∧ (P s).ν ≤ (P t).ν := by
  haveI := hμ.1.isProbability s t hs hst
  obtain ⟨R, hR⟩ := line_exponent_data_1_converse (μ s t) (hμ.2.2 s t hs hst)
    (isLawHemigroup_line_infinitelyDivisible hμ.1 hs hst)
  have hdiff : IsSymLevyExponent (fun ω => (P t).exponent ω - (P s).exponent ω) := by
    refine ⟨R, fun ω => ?_⟩
    have h1 := (charFun_step_of_folded hμ.1 hP hs hst ω).symm.trans (hR ω)
    have h2 := Real.exp_injective (Complex.ofReal_injective h1)
    linarith
  exact ((line_exponent_data_3 (P s).exponent (P t).exponent (P s) (P t) (fun _ => rfl)
    (fun _ => rfl)).1).1 hdiff

/-! ## `lem:discrete-covariance-line` -/

/-- Covariance at `q` through a bijection equal to `t ↦ qt` on `[0,∞)`. -/
theorem isCovariantAt_mul_of_eqOn {μ : ℝ → ℝ → Measure ℝ} {q : ℝ} (hq : 0 < q) {Sq : ℝ → ℝ}
    (h : IsCovariantAt μ q Sq) (hS : ∀ t : ℝ, 0 ≤ t → Sq t = q * t) :
    IsCovariantAt μ q (fun t => q * t) := by
  refine ⟨⟨fun t ht => mul_nonneg hq.le ht, fun u _ v _ huv => mul_lt_mul_of_pos_left huv hq,
    fun t ht => ⟨t / q, div_nonneg ht hq.le, mul_div_cancel₀ t hq.ne'⟩⟩, fun s t hs hst => ?_⟩
  rw [h.2 s t hs hst, hS s hs, hS t (hs.trans hst)]

/-- (A8) at `q^ℤ` in the canonical discrete gauge is `q`-covariance of the kernels with
`S_q t = qt`. -/
theorem scaleCovariant_canonical_iff (C : CascadeCore) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsKernelFamily C.Φ μ) {q : ℝ} (hq : 1 < q) :
    (∃ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (qPowers q) S ∧ IsCanonicalDiscreteGauge q S) ↔
      IsCovariantAt μ q (fun t => q * t) := by
  have hq0 : 0 < q := by linarith
  have hqc := line_axioms_kernels_qcov C μ hμ hq
  constructor
  · rintro ⟨S, hS, hcan⟩
    have h1 := hqc.1 S hS 1
    rw [zpow_one] at h1
    exact isCovariantAt_mul_of_eqOn hq0 h1 hcan
  · intro hcov
    obtain ⟨S, hSq, hS⟩ := hqc.2 _ hcov
    exact ⟨S, hS, fun t _ => by rw [hSq]⟩

/-- **`lem:discrete-covariance-line`, the equivalences.** With the folded data `P t` of the
kernels `μ_{0,t}`: (A8 at `q^ℤ`) with `S_q t = qt` holds iff `Ψ_{qt}(ω) = Ψ_t(qω)` for all
`t ≥ 0`, `ω`, iff `a(qt) = q² a(t)` and `ϖ_{qt} = T_q ϖ_t` for all `t > 0`. -/
theorem discrete_covariance_line (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsKernelFamily C.Φ μ) (P : ℝ → SymLevyPair)
    (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {q : ℝ} (hq : 1 < q) :
    ((∃ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (qPowers q) S ∧ IsCanonicalDiscreteGauge q S) ↔
        ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ, (P (q * t)).exponent ω = (P t).exponent (q * ω)) ∧
      ((∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ, (P (q * t)).exponent ω = (P t).exponent (q * ω)) ↔
        ∀ t : ℝ, 0 < t →
          (P (q * t)).a = q ^ 2 * (P t).a ∧ (P (q * t)).ν = (P t).ν.map (fun v => q * v)) := by
  have hq0 : 0 < q := by linarith
  have hfam := line_axioms_kernels_1_family C μ hμ
  refine ⟨(scaleCovariant_canonical_iff C hμ hq).trans (covariantAt_iff_folded hfam hP hq0),
    ⟨fun hE t ht => (exponent_dilate_iff (P t) (P (q * t)) hq0).1 (hE t ht.le),
    fun hD t ht ω => ?_⟩⟩
  rcases ht.eq_or_lt with h0 | h0
  · subst h0
    have hz := (foldedData_zero hfam.1 (hP 0 le_rfl)).1
    rw [mul_zero, hz, hz]
  · exact (exponent_dilate_iff (P t) (P (q * t)) hq0).2 (hD t h0) ω

/-- **`lem:discrete-covariance-line`, "then".** Under (A8 at `q^ℤ`) with `S_q t = qt`, every
kernel is semi-selfdecomposable with span `q`, `T_q μ_{0,t} = μ_{0,qt} = μ_{0,t} * μ_{t,qt}`, and
`T_q ϖ_t ≥ ϖ_t`, `q² a(t) ≥ a(t)`. -/
theorem discrete_covariance_line_semi (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsKernelFamily C.Φ μ) (P : ℝ → SymLevyPair)
    (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {q : ℝ} (hq : 1 < q)
    (S : ℝ → ℝ → ℝ) (hS : IsScaleCovariant C.Φ (qPowers q) S)
    (hcan : IsCanonicalDiscreteGauge q S) (t : ℝ) (ht : 0 ≤ t) :
    IsSemiSelfDecomposableWithSpan q (μ 0 t) ∧ (μ 0 t).map (fun x => q * x) = μ 0 (q * t) ∧
      μ 0 (q * t) = μ 0 t ∗ μ t (q * t) ∧ (P t).ν ≤ (P t).ν.map (fun v => q * v) ∧
      (P t).a ≤ q ^ 2 * (P t).a := by
  have hq0 : 0 < q := by linarith
  have hfam := line_axioms_kernels_1_family C μ hμ
  have hcov : IsCovariantAt μ q (fun t => q * t) :=
    (scaleCovariant_canonical_iff C hμ hq).1 ⟨S, hS, hcan⟩
  have hqt : t ≤ q * t := by nlinarith
  have hk : (μ 0 t).map (fun x => q * x) = μ 0 (q * t) := by
    simpa only [smul_eq_mul] using cov_kernel hcov ht
  haveI := hfam.1.isProbability t (q * t) ht hqt
  haveI := hfam.1.isProbability 0 t le_rfl ht
  have hcasc : μ 0 (q * t) = μ 0 t ∗ μ t (q * t) := by
    rw [hfam.1.cascade 0 t (q * t) le_rfl ht hqt, Measure.conv_comm]
  -- the residual `T_{q⁻¹} μ_{t,qt}`
  have hsemi : IsSemiSelfDecomposableWithSpan q (μ 0 t) := by
    refine ⟨hq, (μ t (q * t)).map (fun x => q⁻¹ * x),
      ⟨Measure.isProbabilityMeasure_map (measurable_const_mul _).aemeasurable, fun z => ?_⟩,
      isInfinitelyDivisible_map_mul (isLawHemigroup_line_infinitelyDivisible hfam.1 ht hqt) q⁻¹⟩
    rw [charFun_map_mul]
    have h1 := charFun_kernel_mul_gen hfam.1 ht hqt (q⁻¹ • z)
    rw [← hk, charFun_map_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hq0.ne', one_mul] at h1
    rw [h1, smul_eq_mul, mul_comm]
  -- the data
  have hE := ((covariantAt_iff_folded hfam hP hq0).1 hcov)
  have hν : (P (q * t)).ν = (P t).ν.map (fun v => q * v) :=
    ((exponent_dilate_iff (P t) (P (q * t)) hq0).1 (hE t ht)).2
  refine ⟨hsemi, hk, hcasc, ?_, ?_⟩
  · rw [← hν]
    exact (foldedData_mono hfam hP ht hqt).2
  · have ha := (P t).a_nonneg
    have hq2 : 1 ≤ q ^ 2 := by nlinarith
    nlinarith

/-- **`lem:discrete-covariance-line`, the fundamental annulus.** Two such families whose kernels
`μ_{0,t}` agree for `t ∈ [1, q)` have the same kernels and the same operators. -/
theorem discrete_covariance_line_annulus (C C' : CascadeCore) (μ μ' : ℝ → ℝ → Measure ℝ)
    (hμ : IsKernelFamily C.Φ μ) (hμ' : IsKernelFamily C'.Φ μ') {q : ℝ} (hq : 1 < q)
    (S S' : ℝ → ℝ → ℝ) (hS : IsScaleCovariant C.Φ (qPowers q) S)
    (hcan : IsCanonicalDiscreteGauge q S) (hS' : IsScaleCovariant C'.Φ (qPowers q) S')
    (hcan' : IsCanonicalDiscreteGauge q S') (heq : ∀ t ∈ Ico (1 : ℝ) q, μ 0 t = μ' 0 t) :
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → C.Φ s t = C'.Φ s t := by
  have hfam := line_axioms_kernels_1_family C μ hμ
  have hfam' := line_axioms_kernels_1_family C' μ' hμ'
  have hcov := (scaleCovariant_canonical_iff C hμ hq).1 ⟨S, hS, hcan⟩
  have hcov' := (scaleCovariant_canonical_iff C' hμ' hq).1 ⟨S', hS', hcan'⟩
  have hker : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t := by
    intro s t hs hst
    refine map_lineEmb_injective ?_
    exact discrete_covariance_levy_determined le_rfl _ _ (isSymmetricFamily_lineEmb hfam)
      (isSymmetricFamily_lineEmb hfam') hq (isCovariantAt_lineEmb hcov)
      (isCovariantAt_lineEmb hcov') (fun t ht => by simp only [heq t ht]) s t hs hst
  refine ⟨hker, fun s t hs hst => ?_⟩
  haveI := hμ.isProbability s t hs hst
  haveI := hμ'.isProbability s t hs hst
  rw [ScaleSpace.Phi_eq_mconvL1 (Fam := C.toPreCascadeCore) hμ hs hst,
    ScaleSpace.Phi_eq_mconvL1 (Fam := C'.toPreCascadeCore) hμ' hs hst]
  exact ScaleSpace.mconvL1_congr (hker s t hs hst)

end Pyramids
