/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.MaternLine
import Pyramids.Cited.A22
import Pyramids.Cited.A24
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# `thm:matern-pyramid-line-noncreation`: Pólya frequency on the line

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:matern-pyramid-line-noncreation`. Phase 5,
wave 3b. The statement is the skeleton's (`PyramidsSkeleton/ChA1Line.lean`), unchanged.

* **The kernels** `μ_t` are Pólya frequency kernels: A22's determinant clause
  (`cited_A22_polya`) at `F_q = ∑ᵢ log(1 + ω²/ϑᵢ²)`, `ϑᵢ = q^{i+1}/c`, `a = 0`, admissible by
  `thm:matern-pyramid-line`(1).
* **The octave step** `μ_{t,qt} = L_{ct}`: A22 at `F₁(ω) = log(1 + ω²)`, one atom `ϑ = 1`
  (admissible by `lem:laplace-atoms-admissible`(2)), for the family `r ↦ L_r` at the scale `ct`.
* **An increment** `μ_{s,t}`, `t/s ∉ q^ℤ`, is not a Pólya frequency density. With
  `N_r(p) := ∏ᵢ (1 - (r/ϑᵢ)² p²)`, entire (`differentiable_maternN`, a locally uniformly
  convergent product), `N_r(iω) = e^{F_q(rω)}` (`maternN_mul_I`), so
  `μ̂_{s,t}(ω) = N_s(iω)/N_t(iω)`. If `μ_{s,t}` had a Pólya frequency density `φ`, A24
  (`cited_A24`, admitted on the imaginary axis) would give an entire `ψ` with
  `L(iω)ψ(iω) = 1`, `L(iω) = μ̂_{s,t}(-ω)`; so `N_s ψ = N_t` on the imaginary axis, hence on `ℂ`
  by the identity theorem. At `p₀ = q/(cs)` the factor `i = 0` of `N_s` vanishes, so `N_t(p₀) = 0`,
  and a product of factors `1 + fᵢ` with `∑ ‖fᵢ‖ < ∞` vanishes only if a factor does
  (`tprod_one_add_ne_zero_of_summable`): `(t/s)² = q^{2i}` for some `i`, so `t/s ∈ q^ℤ`.

The strip of Karlin's Proposition 1.4 is not read: the identity theorem runs on `ℂ` from the
imaginary axis, the two sides being entire.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter Complex
open ScaleSpace (IsAdmissibleExponent laplaceLaw polyaE2)
open scoped Topology ENNReal

variable {q c : ℝ}

/-! ## Two facts about Pólya frequency densities and kernels -/

/-- The determinant of order `1`: a Pólya frequency function is nonnegative. -/
theorem IsPolyaFrequencyFn.nonneg {φ : ℝ → ℝ} (hφ : IsPolyaFrequencyFn φ) (x : ℝ) : 0 ≤ φ x := by
  have h := hφ 1 (fun _ => x) (fun _ => 0) (Subsingleton.strictMono _) (Subsingleton.strictMono _)
  simpa [Matrix.det_unique] using h

/-- The transform of a measure with a Pólya frequency density, at `-ω`, is the two-sided
Laplace transform of the density at `iω`. -/
theorem charFun_neg_of_polya {φ : ℝ → ℝ} (hφ : IsPolyaFrequencyDensity φ) (ω : ℝ) :
    charFun ((volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (φ x)) (-ω) =
      ∫ x : ℝ, Complex.exp (-((ω : ℂ) * I) * x) * (φ x : ℂ) := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) volume :=
    hφ.2.1.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [charFun_apply_real, integral_withDensity_eq_integral_toReal_smul₀ hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hφ.1.nonneg x), Complex.real_smul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-! ## The clauses on the kernels and the octave step -/

theorem isAdmissible_maternExponent (hq : 1 < q) (hc : 0 < c) :
    IsAdmissibleExponent (maternExponent q c) :=
  let ⟨P, _, _, hP⟩ := exists_maternProfile hq hc
  ⟨P, hP⟩

/-- `μ̂_{0,t}(ω) = e^{-F_q(tω)}`. -/
theorem charFun_matern_zero {μ : ℝ → ℝ → Measure ℝ} (hμ : IsMaternPyramid q c μ) {t : ℝ}
    (ht : 0 ≤ t) (ω : ℝ) :
    charFun (μ 0 t) ω = ((Real.exp (-maternExponent q c (t * ω)) : ℝ) : ℂ) := by
  rw [(hμ 0 t le_rfl ht).2 ω]
  simp only [zero_mul, maternExponent_zero, sub_zero, Real.norm_eq_abs, maternExponent_mul_abs]

/-- `F₁(ω) = log(1 + ω²)` in the form of A22: `a = 0`, one atom `ϑ = 1`. -/
theorem logOnePlusSq_form (ω : ℝ) :
    Real.log (1 + ω ^ 2) = 0 * ω ^ 2 + ∑' _ : Unit, Real.log (1 + ω ^ 2 / (1 : ℝ) ^ 2) := by
  simp

/-- `L̂_r(ω) = e^{-F₁(rω)}`. -/
theorem charFun_laplaceLaw_eq_exp {r : ℝ} (hr : 0 < r) (ω : ℝ) :
    charFun (laplaceLaw r) ω = ((Real.exp (-Real.log (1 + (r * ω) ^ 2)) : ℝ) : ℂ) := by
  rw [charFun_laplaceLaw_real hr, Real.exp_neg, Real.exp_log (by positivity), mul_pow]

/-- **The Laplace law is a Pólya frequency kernel**: A22 at `F₁`. -/
theorem isPolyaFrequencyKernel_laplaceLaw {r : ℝ} (hr : 0 < r) :
    IsPolyaFrequencyKernel (laplaceLaw r) := by
  have hadm := (laplace_atoms_admissible_2 (ι := Unit) le_rfl (fun _ => (1 : ℝ))
    (fun _ => one_pos) (Summable.of_finite) (fun ω => Real.log (1 + ω ^ 2))
    logOnePlusSq_form).2.2.2.1
  obtain ⟨P, -, -, hP⟩ := hadm
  refine cited_A22_polya (ι := Unit) (fun ω => Real.log (1 + ω ^ 2)) ⟨P, hP⟩
    ⟨1, by norm_num [Real.log_eq_zero]⟩ 0 le_rfl (fun _ => (1 : ℝ)) (fun _ => one_pos)
    Summable.of_finite
    logOnePlusSq_form (fun r => laplaceLaw r)
    (fun r hr => ScaleSpace.isProbabilityMeasure_laplaceLaw hr)
    (fun r hr ω => charFun_laplaceLaw_eq_exp hr ω) hr

/-! ## The entire functions `N_r` -/

/-- `N_r(p) = ∏ᵢ (1 - (r/ϑᵢ)² p²)`, `ϑᵢ = q^{i+1}/c`. -/
noncomputable def maternN (q c r : ℝ) (p : ℂ) : ℂ :=
  ∏' i : ℕ, (1 + -((r / maternTheta q c i : ℝ) : ℂ) ^ 2 * p ^ 2)

theorem summable_maternN_coeff (hq : 1 < q) (hc : 0 < c) (r : ℝ) :
    Summable fun i : ℕ => (r / maternTheta q c i) ^ 2 :=
  ((summable_maternTheta hq hc).mul_left (r ^ 2)).congr fun i => by rw [div_pow, div_eq_mul_inv]

theorem norm_maternN_term (r : ℝ) (p : ℂ) (i : ℕ) :
    ‖-((r / maternTheta q c i : ℝ) : ℂ) ^ 2 * p ^ 2‖ = (r / maternTheta q c i) ^ 2 * ‖p‖ ^ 2 := by
  rw [norm_mul, norm_neg, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **`N_r` is entire.** -/
theorem differentiable_maternN (hq : 1 < q) (hc : 0 < c) (r : ℝ) :
    Differentiable ℂ (maternN q c r) := by
  have hloc : HasProdLocallyUniformlyOn
      (fun (i : ℕ) (p : ℂ) => 1 + -((r / maternTheta q c i : ℝ) : ℂ) ^ 2 * p ^ 2)
      (maternN q c r) univ := by
    refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun K _ hK => ?_
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    refine ((summable_maternN_coeff hq hc r).mul_right (R ^ 2)).hasProdUniformlyOn_nat_one_add hK
      (Eventually.of_forall fun i p hp => ?_) (fun _ => by fun_prop)
    rw [norm_maternN_term]
    gcongr
    exact hR p hp
  have hd : DifferentiableOn ℂ (maternN q c r) univ :=
    TendstoLocallyUniformlyOn.differentiableOn (φ := atTop) hloc
      (Eventually.of_forall fun s => by fun_prop) isOpen_univ
  exact differentiableOn_univ.1 hd

/-- **`N_r(iω) = e^{F_q(rω)}`.** -/
theorem maternN_mul_I (hq : 1 < q) (hc : 0 < c) (r ω : ℝ) :
    maternN q c r ((ω : ℂ) * I) = ((Real.exp (maternExponent q c (r * ω)) : ℝ) : ℂ) := by
  have h := (maternExponent_hasSum hq hc (r * ω)).rexp
  have hpos : ∀ i : ℕ, 0 < 1 + c ^ 2 * (r * ω) ^ 2 / q ^ (2 * (i + 1)) := fun i => by
    have : 0 < q := by linarith
    positivity
  have h2 : HasProd (fun i : ℕ => 1 + c ^ 2 * (r * ω) ^ 2 / q ^ (2 * (i + 1)))
      (Real.exp (maternExponent q c (r * ω))) := by
    convert h using 1
    funext i
    simp only [Function.comp_apply, Real.exp_log (hpos i)]
  have h3 := h2.map Complex.ofRealHom Complex.continuous_ofReal
  unfold maternN
  refine HasProd.tprod_eq ?_
  convert h3 using 1
  swap
  · rfl
  funext i
  simp only [Function.comp_apply, Complex.ofRealHom_eq_coe]
  rw [maternTerm_eq hq hc]
  push_cast
  have hθ : (maternTheta q c i : ℂ) ≠ 0 := by exact_mod_cast (maternTheta_pos hq hc i).ne'
  field_simp
  rw [I_sq]
  ring

/-- **The factor `i = 0` of `N_s` vanishes at `q/(cs)`.** -/
theorem maternN_zero_at (hq : 1 < q) (hc : 0 < c) {s : ℝ} (hs : 0 < s) :
    maternN q c s ((q / (c * s) : ℝ) : ℂ) = 0 := by
  refine tprod_of_exists_eq_zero ⟨0, ?_⟩
  have hq0 : 0 < q := by linarith
  have e : s / maternTheta q c 0 * (q / (c * s)) = 1 := by
    rw [maternTheta, zero_add, pow_one]
    field_simp
  have e2 : ((s / maternTheta q c 0 : ℝ) : ℂ) ^ 2 * ((q / (c * s) : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← mul_pow, ← Complex.ofReal_mul, e]
    simp
  rw [neg_mul, e2]
  ring

/-- **`N_t(q/(cs)) = 0` only if `t/s ∈ q^ℤ`.** -/
theorem mem_qPowers_of_maternN_eq_zero (hq : 1 < q) (hc : 0 < c) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (h0 : maternN q c t ((q / (c * s) : ℝ) : ℂ) = 0) : t / s ∈ qPowers q := by
  have hq0 : 0 < q := by linarith
  by_contra hnot
  refine tprod_one_add_ne_zero_of_summable (f := fun i : ℕ =>
    -((t / maternTheta q c i : ℝ) : ℂ) ^ 2 * ((q / (c * s) : ℝ) : ℂ) ^ 2) (fun i hi => ?_) ?_ h0
  · -- a vanishing factor: `(t/s)² = q^{2i}`
    have hval : (t / maternTheta q c i) ^ 2 * (q / (c * s)) ^ 2 = 1 := by
      have h1 : ((((t / maternTheta q c i) ^ 2 * (q / (c * s)) ^ 2 : ℝ)) : ℂ) = 1 := by
        rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
        linear_combination -hi
      exact_mod_cast h1
    have hts : t / s = q ^ i := by
      have hx : (t / maternTheta q c i * (q / (c * s))) = t / s / q ^ i := by
        rw [maternTheta]
        field_simp
        ring
      have hpos : 0 < t / s / q ^ i := by positivity
      have hsq : (t / s / q ^ i) ^ 2 = 1 := by rw [← hx, mul_pow]; exact hval
      have h1 : t / s / q ^ i = 1 := by nlinarith
      exact (div_eq_one_iff_eq (pow_pos hq0 i).ne').1 h1
    exact hnot ⟨i, by rw [hts]; exact zpow_natCast q i⟩
  · refine ((summable_maternN_coeff hq hc t).mul_right (‖((q / (c * s) : ℝ) : ℂ)‖ ^ 2)).congr
      fun i => ?_
    exact (norm_maternN_term t _ i).symm

/-! ## The increments -/

/-- **`μ̂_{s,t}(-ω) N_t(iω) = N_s(iω)`.** -/
theorem charFun_matern_increment {μ : ℝ → ℝ → Measure ℝ} (hq : 1 < q) (hc : 0 < c)
    (hμ : IsMaternPyramid q c μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ω : ℝ) :
    charFun (μ s t) (-ω) * maternN q c t ((ω : ℂ) * I) = maternN q c s ((ω : ℂ) * I) := by
  rw [(hμ s t hs hst).2 (-ω), maternN_mul_I hq hc, maternN_mul_I hq hc]
  simp only [Real.norm_eq_abs, maternExponent_mul_abs, mul_neg, maternExponent_neg]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- **An increment `μ_{s,t}` with `t/s ∉ q^ℤ` is not a Pólya frequency kernel.** -/
theorem matern_increment_not_polya {μ : ℝ → ℝ → Measure ℝ} (hq : 1 < q) (hc : 0 < c)
    (hμ : IsMaternPyramid q c μ) {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hnot : t / s ∉ qPowers q) : ¬ IsPolyaFrequencyKernel (μ s t) := by
  rintro ⟨φ, hφ, hμφ⟩
  obtain ⟨γ, δ, a, -, -, -, hψd, -, hL⟩ := cited_A24 φ hφ
  -- on the imaginary axis, `N_s ψ = N_t`
  have haxis : ∀ ω : ℝ, maternN q c s ((ω : ℂ) * I) * polyaE2 γ δ a ((ω : ℂ) * I) =
      maternN q c t ((ω : ℂ) * I) := by
    intro ω
    have h1 := charFun_matern_increment hq hc hμ hs.le hst.le ω
    rw [hμφ, charFun_neg_of_polya hφ] at h1
    rw [← h1, mul_comm _ (maternN q c t _), mul_assoc, hL ω, mul_one]
  -- hence on `ℂ`
  have hent : EqOn (fun p => maternN q c s p * polyaE2 γ δ a p) (maternN q c t) univ := by
    have hf : AnalyticOnNhd ℂ (fun p => maternN q c s p * polyaE2 γ δ a p) univ :=
      fun z _ => ((differentiable_maternN hq hc s).mul hψd).analyticAt z
    have hg : AnalyticOnNhd ℂ (maternN q c t) univ :=
      fun z _ => (differentiable_maternN hq hc t).analyticAt z
    refine hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ (mem_univ 0) ?_
    have htend : Tendsto (fun ω : ℝ => (ω : ℂ) * I) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun ω : ℝ => (ω : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
          (Complex.continuous_ofReal.mul continuous_const).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ω hω
        simpa using hω
    exact htend.frequently (Frequently.of_forall fun ω => haxis ω)
  have h0 := hent (mem_univ ((q / (c * s) : ℝ) : ℂ))
  simp only [maternN_zero_at hq hc hs, zero_mul] at h0
  exact hnot (mem_qPowers_of_maternN_eq_zero hq hc hs (hs.trans hst) h0.symm)

/-- **`thm:matern-pyramid-line-noncreation`.** In the Matérn pyramid every kernel `μ_t`, `t > 0`,
and every octave step `μ_{t,qt} = L_{ct}` is a Pólya frequency density; an increment `μ_{s,t}`,
`0 < s < t`, `t/s ∉ q^ℤ`, is not. -/
theorem matern_pyramid_line_noncreation {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure ℝ) (hμ : IsMaternPyramid q c μ) :
    (∀ t : ℝ, 0 < t → IsPolyaFrequencyKernel (μ 0 t)) ∧
      (∀ t : ℝ, 0 < t → IsPolyaFrequencyKernel (μ t (q * t))) ∧
      ∀ s t : ℝ, 0 < s → s < t → t / s ∉ qPowers q → ¬ IsPolyaFrequencyKernel (μ s t) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun s t hs hst hnot => ?_⟩
  · exact cited_A22_polya (maternExponent q c) (isAdmissible_maternExponent hq hc)
      (exists_maternExponent_ne hq hc) 0 le_rfl (maternTheta q c) (maternTheta_pos hq hc)
      (summable_maternTheta hq hc) (maternExponent_eq_atoms hq hc) (fun t => μ 0 t)
      (fun t ht => (hμ 0 t le_rfl ht.le).1) (fun t ht ω => charFun_matern_zero hμ ht.le ω) ht
  · rw [matern_octave_step hq hc hμ ht]
    exact isPolyaFrequencyKernel_laplaceLaw (mul_pos hc ht)
  · exact matern_increment_not_polya hq hc hμ hs hst hnot

end Pyramids
