/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.SurfaceStieltjes
import Pyramids.LineAppendix.StepField

/-!
# `thm:surface-measure`: from a family to its pair `(Λ, ℬ)`

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:surface-measure`. Wave 3a:
`surface_measure_family` and `surface_measure_unique` moved here from `PyramidsSkeleton.ChA1Line`,
unchanged in name; `surface_measure_unique` no longer takes the hypotheses `1 < q` and
`IsQFamily q μ`, which its proof does not use (2026-11-14, a strengthening).

## The route

Let the kernels have the folded data `(a(t), ϖ_t)`, `t ≥ 0` (`exists_folded`).

* **Steps.** For `s ≤ t`, `Ψ_t - Ψ_s` is the exponent of `μ_{s,t}`, so `a(s) ≤ a(t)`, `ϖ_s ≤ ϖ_t`,
  and the difference has data `Q` (`foldedData_step`, by `lem:line-exponent-data`(3)). Covariance
  gives `(a(qt), ϖ_{qt}) = (q²a(t), T_qϖ_t)` (`foldedData_cov`).
* **The averaging bound.** `1 ∧ x² ≤ 3(1 - cos x) + ∫_0^2 (1 - cos ωx) dω`, so by Tonelli
  `∫ (1 ∧ v²) dQ ≤ G(t) - G(s)` with `G(t) := 3Ψ_t(1) + ∫_0^2 Ψ_t` (`step_weight_le`), and
  `a(t) - a(s) ≤ Ψ_t(1) - Ψ_s(1)`. `G` and `t ↦ Ψ_t(1)` are continuous by (I2) and dominated
  convergence. Hence `t ↦ ϖ_t(A)` is continuous for `A` bounded away from `0`, and `a` is
  continuous.
* **`Λ`** is `exists_slab_of_monotone` applied to `t ↦ ϖ_{max(t,0)}`; **`ℬ`** is the Stieltjes
  measure of `t ↦ a(max(t,0))`. (i) is `quadrant_measure_ext` and the covariance of the data, (ii)
  the one-variable uniqueness `measure_ext_of_Ioc_zero`, (iii) the continuity of `ϖ_t(A)` and of
  `a`, and (iv) (ND): if both masses vanish, the step `μ_{s,t}` has the data `(0, 0)` and is `δ₀`.
* **Uniqueness** is `quadrant_measure_ext` and `measure_ext_of_Ioc_zero`, the slabs and the masses
  `ℬ((0,t])` being fixed by the folded data of `μ_t`, which are unique (`line_levy_unique`).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair IsSymLevyExponent)
open scoped Topology ENNReal

/-! ## The averaging bound -/

/-- `1 ∧ x² ≤ 3(1 - cos x) + ∫_0^2 (1 - cos ωx) dω`. -/
theorem min_one_sq_le_avg (x : ℝ) :
    ENNReal.ofReal (min 1 (x ^ 2)) ≤ 3 * ENNReal.ofReal (1 - Real.cos x) +
      ∫⁻ ω in Ioc (0 : ℝ) 2, ENNReal.ofReal (1 - Real.cos (ω * x)) := by
  rcases le_or_gt |x| 1 with hx | hx
  · refine le_add_right ?_
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (sq_le_three_mul_one_sub_cos hx))
  · refine le_add_left ?_
    calc ENNReal.ofReal (min 1 (x ^ 2)) ≤ 1 := ENNReal.ofReal_le_one.2 (min_le_left _ _)
      _ ≤ _ := one_le_lintegral_one_sub_cos hx.le

/-- **The averaging bound** for a pair: `∫ (1 ∧ v²) dϖ ≤ 3ψ(1) + ∫_0^2 ψ`. -/
theorem lintegral_min_one_sq_le (Q : SymLevyPair) :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂Q.ν ≤
      3 * Q.exponentL 1 + ∫⁻ ω in Ioc (0 : ℝ) 2, Q.exponentL ω := by
  haveI := SymLevyPair_sigmaFinite Q
  have hle : ∀ ω : ℝ, ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂Q.ν ≤ Q.exponentL ω :=
    fun ω => le_add_self
  have hgm : Measurable (Function.uncurry fun (x ω : ℝ) =>
      ENNReal.ofReal (1 - Real.cos (ω * x))) := by
    unfold Function.uncurry
    fun_prop
  calc ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂Q.ν
      ≤ ∫⁻ x, (3 * ENNReal.ofReal (1 - Real.cos x) +
          ∫⁻ ω in Ioc (0 : ℝ) 2, ENNReal.ofReal (1 - Real.cos (ω * x))) ∂Q.ν :=
        lintegral_mono fun x => min_one_sq_le_avg x
    _ = 3 * ∫⁻ x, ENNReal.ofReal (1 - Real.cos x) ∂Q.ν +
          ∫⁻ ω in Ioc (0 : ℝ) 2, ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂Q.ν := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
          lintegral_lintegral_swap hgm.aemeasurable]
    _ ≤ _ := add_le_add (by gcongr; simpa using hle 1)
        (setLIntegral_mono' measurableSet_Ioc fun ω _ => hle ω)

/-- `ε₀ ϖ(A) ≤ ∫ (1 ∧ v²) dϖ` for `A ⊆ (ε,∞)`, `ε₀ = 1 ∧ ε²`. -/
theorem measure_le_of_weight (m : Measure ℝ) {ε : ℝ} (hε : 0 < ε) {A : Set ℝ}
    (hAε : A ⊆ Ioi ε) :
    ENNReal.ofReal (min 1 (ε ^ 2)) * m A ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂m := by
  rw [← setLIntegral_const]
  refine (setLIntegral_mono (by fun_prop) fun x hx => ?_).trans (setLIntegral_le_lintegral _ _)
  exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (pow_le_pow_left₀ hε.le (hAε hx).le 2))

/-- The Gaussian coefficient is at most the exponent at `1`. -/
theorem SymLevyPair_a_le_exponent_one (Q : SymLevyPair) : Q.a ≤ Q.exponent 1 := by
  have h : ENNReal.ofReal (Q.a * 1 ^ 2) ≤ Q.exponentL 1 := le_self_add
  have h2 := ENNReal.toReal_mono (Q.exponentL_ne_top 1) h
  rwa [one_pow, mul_one, ENNReal.toReal_ofReal Q.a_nonneg] at h2

/-- A function whose increments are dominated by those of a continuous one is continuous. -/
theorem continuousOn_of_dist_le {f g : ℝ → ℝ} {s : Set ℝ} (hg : ContinuousOn g s)
    (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ dist (g x) (g y)) : ContinuousOn f s := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 (hg x hx) ε hε
  exact ⟨δ, hδ, fun y hy hxy => (h y hy x hx).trans_lt (hδ' hy hxy)⟩

/-! ## The data along a family -/

section Family

variable {q : ℝ} {μ : ℝ → ℝ → Measure ℝ}

/-- `t ↦ Ψ_t(ω)` is continuous on `[0,∞)`, by (I2). -/
theorem lineExponent_continuousOn (hμ : IsSymmetricFamily μ) (ω : ℝ) :
    ContinuousOn (fun t => lineExponent μ t ω) (Ici 0) := by
  have hK := kernelOrder_line hμ
  have hc : ContinuousOn (fun t => charFun (μ 0 t) ω) (Ici 0) :=
    (hμ.1.continuous ω).comp (continuous_const.prodMk continuous_id).continuousOn (by
      intro t ht
      exact ⟨le_rfl, ht⟩)
  exact ((Complex.continuous_re.comp_continuousOn hc).log fun t ht => (hK.re_pos ht ω).ne').neg

theorem lineExponent_nonneg (hμ : IsSymmetricFamily μ) {t : ℝ} (ht : 0 ≤ t) (ω : ℝ) :
    0 ≤ lineExponent μ t ω := by
  have h := lineExponent_mono hμ le_rfl ht ω
  rwa [lineExponent_zero hμ] at h

theorem integrableOn_lineExponent (hμ : IsSymmetricFamily μ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (lineExponent μ t) (Ioc 0 2) :=
  ((lineExponent_continuous hμ ht).integrableOn_Icc).mono_set Ioc_subset_Icc_self

/-- **`G(t) := 3Ψ_t(1) + ∫_0^2 Ψ_t`**, the averaged exponent. -/
noncomputable def avgExponent (μ : ℝ → ℝ → Measure ℝ) (t : ℝ) : ℝ :=
  3 * lineExponent μ t 1 + ∫ ω in Ioc (0 : ℝ) 2, lineExponent μ t ω

theorem avgExponent_continuousOn (hμ : IsSymmetricFamily μ) :
    ContinuousOn (avgExponent μ) (Ici 0) := by
  have hT : ∀ T : ℝ, ContinuousOn (avgExponent μ) (Icc 0 T) := by
    intro T
    refine (continuousOn_const.mul ((lineExponent_continuousOn hμ 1).mono
      Icc_subset_Ici_self)).add ?_
    refine MeasureTheory.continuousOn_of_dominated (bound := lineExponent μ (max T 0))
      (fun t ht => ?_) (fun t ht => ?_) (integrableOn_lineExponent hμ (le_max_right _ _)) ?_
    · exact (lineExponent_continuous hμ ht.1).aestronglyMeasurable
    · refine ae_of_all _ fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (lineExponent_nonneg hμ ht.1 ω)]
      exact lineExponent_mono hμ ht.1 (ht.2.trans (le_max_left _ _)) ω
    · exact ae_of_all _ fun ω => (lineExponent_continuousOn hμ ω).mono Icc_subset_Ici_self
  intro x hx
  refine (hT (x + 1) x ⟨hx, by linarith⟩).mono_of_mem_nhdsWithin ?_
  rw [← Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

/-- The exponent of a step is in `ND_s`. -/
theorem isSymLevyExponent_step (hμ : IsSymmetricFamily μ) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : IsSymLevyExponent (fun ω => lineExponent μ t ω - lineExponent μ s ω) := by
  obtain ⟨P, hP⟩ := exists_folded hμ
  haveI := hμ.1.isProbability s t hs hst
  obtain ⟨R, hR⟩ := line_exponent_data_1_converse (μ s t) (hμ.2.2 s t hs hst)
    (isLawHemigroup_line_infinitelyDivisible hμ.1 hs hst)
  refine ⟨R, fun ω => ?_⟩
  have h1 : charFun (μ s t) ω =
      ((Real.exp (-(lineExponent μ t ω - lineExponent μ s ω)) : ℝ) : ℂ) := by
    rw [lineExponent_eq_of_folded hμ (hs.trans hst) (hP t (hs.trans hst)),
      lineExponent_eq_of_folded hμ hs (hP s hs)]
    exact charFun_step_of_folded hμ.1 hP hs hst ω
  have h2 := Real.exp_injective (Complex.ofReal_injective (h1.symm.trans (hR ω)))
  linarith

/-- **The data of a step**: `a(s) ≤ a(t)`, `ϖ_s ≤ ϖ_t`, and the difference has data `Q`. -/
theorem foldedData_step (hμ : IsSymmetricFamily μ) {P : ℝ → SymLevyPair}
    (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (P s).a ≤ (P t).a ∧ (P s).ν ≤ (P t).ν ∧ ∃ Q : SymLevyPair, Q.a = (P t).a - (P s).a ∧
      Q.ν + (P s).ν = (P t).ν ∧
        ∀ ω : ℝ, Q.exponent ω = lineExponent μ t ω - lineExponent μ s ω := by
  have ht := hs.trans hst
  have h3 := line_exponent_data_3 _ _ _ _ (fun ω => lineExponent_eq_of_folded hμ hs (hP s hs) ω)
    (fun ω => lineExponent_eq_of_folded hμ ht (hP t ht) ω)
  obtain ⟨ha, hν⟩ := h3.1.1 (isSymLevyExponent_step hμ hs hst)
  obtain ⟨Q, hQa, hQν, hQ⟩ := h3.2 ha hν
  exact ⟨ha, hν, Q, hQa, hQν, fun ω => (hQ ω).symm⟩

/-- **Covariance of the data**: `(a(qt), ϖ_{qt}) = (q²a(t), T_qϖ_t)`. -/
theorem foldedData_cov (hμ : IsQFamily q μ) (hq0 : 0 < q) {P : ℝ → SymLevyPair}
    (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {t : ℝ} (ht : 0 ≤ t) :
    (P (q * t)).a = q ^ 2 * (P t).a ∧ (P (q * t)).ν = (P t).ν.map (fun v => q * v) := by
  obtain ⟨Q, hQa, hQν, hQ⟩ := line_exponent_data_2 (lineExponent μ t) (P t)
    (fun ω => lineExponent_eq_of_folded hμ.1 ht (hP t ht) ω) hq0
  have hqt : 0 ≤ q * t := mul_nonneg hq0.le ht
  obtain ⟨ha, hν⟩ := line_exponent_data_1_unique (lineExponent μ (q * t)) (P (q * t)) Q
    (fun ω => lineExponent_eq_of_folded hμ.1 hqt (hP _ hqt) ω)
    (fun ω => by rw [lineExponent_cov hμ ht ω]; exact hQ ω)
  exact ⟨ha.trans hQa, hν.trans hQν⟩

/-- **The averaging bound for a step**: `∫ (1 ∧ v²) dQ ≤ G(t) - G(s)`. -/
theorem step_weight_le (hμ : IsSymmetricFamily μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {Q : SymLevyPair} (hQ : ∀ ω : ℝ, Q.exponent ω = lineExponent μ t ω - lineExponent μ s ω) :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂Q.ν ≤
      ENNReal.ofReal (avgExponent μ t - avgExponent μ s) := by
  have ht := hs.trans hst
  refine (lintegral_min_one_sq_le Q).trans (le_of_eq ?_)
  simp_rw [← SymLevyPair_ofReal_exponent, hQ]
  have hint : IntegrableOn (fun ω => lineExponent μ t ω - lineExponent μ s ω) (Ioc 0 2) :=
    (integrableOn_lineExponent hμ ht).sub (integrableOn_lineExponent hμ hs)
  have hnn : ∀ ω : ℝ, 0 ≤ lineExponent μ t ω - lineExponent μ s ω :=
    fun ω => sub_nonneg.2 (lineExponent_mono hμ hs hst ω)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn),
    show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (hnn 1)) (integral_nonneg hnn),
    integral_sub (integrableOn_lineExponent hμ ht) (integrableOn_lineExponent hμ hs)]
  unfold avgExponent
  ring_nf

/-- **The bound on a step, setwise**:
`ϖ_t(A) ≤ ϖ_s(A) + (1 ∧ ε²)⁻¹ (G(t) - G(s))` for `A ⊆ (ε,∞)`. -/
theorem foldedData_measure_le (hμ : IsSymmetricFamily μ) {P : ℝ → SymLevyPair}
    (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {ε : ℝ} (hε : 0 < ε) {A : Set ℝ} (hAε : A ⊆ Ioi ε) :
    (P t).ν A ≤ (P s).ν A +
      (ENNReal.ofReal (min 1 (ε ^ 2)))⁻¹ * ENNReal.ofReal (avgExponent μ t - avgExponent μ s) := by
  obtain ⟨-, -, Q, -, hQν, hQ⟩ := foldedData_step hμ hP hs hst
  have hc0 : ENNReal.ofReal (min 1 (ε ^ 2)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_min one_pos (by positivity)
  rw [← hQν, Measure.add_apply, add_comm]
  refine add_le_add_right ?_ _
  rw [← ENNReal.mul_le_iff_le_inv hc0 ENNReal.ofReal_ne_top]
  exact (measure_le_of_weight Q.ν hε hAε).trans (step_weight_le hμ hs hst hQ)

/-- **Right-continuity of `t ↦ ϖ_{max(t,0)}(A)`** for `A ⊆ (ε,∞)`. -/
theorem tendsto_foldedData_right (hμ : IsSymmetricFamily μ) {P : ℝ → SymLevyPair}
    (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {ε : ℝ} (hε : 0 < ε) {A : Set ℝ}
    (hAε : A ⊆ Ioi ε) (t : ℝ) :
    Tendsto (fun r => (P (max r 0)).ν A) (𝓝[>] t) (𝓝 ((P (max t 0)).ν A)) := by
  rcases lt_or_ge t 0 with ht | ht
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with r hr
    rw [max_eq_right ht.le, max_eq_right (le_of_lt hr)]
  · have hc : (ENNReal.ofReal (min 1 (ε ^ 2)))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact lt_min one_pos (by positivity))
    have hG : Tendsto (avgExponent μ) (𝓝[>] t) (𝓝 (avgExponent μ t)) :=
      ((avgExponent_continuousOn hμ) t ht).mono_left
        (nhdsWithin_mono _ fun r hr => ht.trans (le_of_lt hr))
    have hup : Tendsto (fun r => (P (max t 0)).ν A + (ENNReal.ofReal (min 1 (ε ^ 2)))⁻¹ *
        ENNReal.ofReal (avgExponent μ r - avgExponent μ t)) (𝓝[>] t)
        (𝓝 ((P (max t 0)).ν A)) := by
      have h1 := ENNReal.tendsto_ofReal (hG.sub_const (avgExponent μ t))
      simpa using tendsto_const_nhds.add (ENNReal.Tendsto.const_mul h1 (Or.inr hc))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      rw [max_eq_left ht, max_eq_left (ht.trans (le_of_lt hr))]
      exact Measure.le_iff'.1 (foldedData_step hμ hP ht (le_of_lt hr)).2.1 A
    · filter_upwards [self_mem_nhdsWithin] with r hr
      rw [max_eq_left ht, max_eq_left (ht.trans (le_of_lt hr))]
      exact foldedData_measure_le hμ hP ht (le_of_lt hr) hε hAε

/-- `c (G(y) - G(s)) → 0` as `s ↑ y`, for `y > 0`. -/
theorem tendsto_avgExponent_left (hμ : IsSymmetricFamily μ) {y : ℝ} (hy : 0 < y) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) :
    Tendsto (fun s => c * ENNReal.ofReal (avgExponent μ y - avgExponent μ s)) (𝓝[<] y)
      (𝓝 0) := by
  have hG : Tendsto (avgExponent μ) (𝓝[<] y) (𝓝 (avgExponent μ y)) :=
    ((avgExponent_continuousOn hμ).continuousAt (Ici_mem_nhds hy)).tendsto.mono_left
      nhdsWithin_le_nhds
  have h1 := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := avgExponent μ y)).sub hG)
  simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hc)

end Family

/-! ## `thm:surface-measure`, from a family to a pair -/

/-- **`thm:surface-measure`, from a family to a pair.** Every family has a pair `(Λ, ℬ)` with
(i)–(iv) and (A.e1). -/
theorem surface_measure_family {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsQFamily q μ) : ∃ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ), IsFamilyPair q μ Λ B := by
  have hq0 : 0 < q := by linarith
  have hsf := hμ.1
  obtain ⟨P, hP⟩ := exists_folded hsf
  obtain ⟨-, hP0a, hP0ν⟩ := foldedData_zero hsf.1 (hP 0 le_rfl)
  -- `Λ`
  obtain ⟨Λ, hΛc, hΛs⟩ := exists_slab_of_monotone (ϖ := fun t => (P (max t 0)).ν)
    (fun s t h => (foldedData_step hsf hP (le_max_right s 0) (max_le_max h le_rfl)).2.1)
    (fun t ht => by simp only [max_eq_right ht, hP0ν])
    (fun t => (P _).ν_folded) (fun t ε hε => SymLevyPair_measure_Ioi_ne_top _ hε)
    (fun t ε hε A _ hAε => tendsto_foldedData_right hsf hP hε hAε t)
  have hΛP : ∀ t : ℝ, 0 < t → slab Λ 0 t = (P t).ν := fun t ht => by
    rw [hΛs t ht]
    simp only [max_eq_left ht.le]
  -- `ℬ`
  have hacont : ContinuousOn (fun t => (P t).a) (Ici 0) := by
    have key : ∀ x y : ℝ, 0 ≤ x → x ≤ y →
        dist (P x).a (P y).a ≤ dist (lineExponent μ x 1) (lineExponent μ y 1) := by
      intro x y hx hxy
      obtain ⟨ha, -, Q, hQa, -, hQ⟩ := foldedData_step hsf hP hx hxy
      rw [Real.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 ha),
        abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (lineExponent_mono hsf hx hxy 1)), ← hQa,
        ← hQ 1]
      exact SymLevyPair_a_le_exponent_one Q
    refine continuousOn_of_dist_le (lineExponent_continuousOn hsf 1) fun x hx y hy => ?_
    rcases le_total x y with hxy | hxy
    · exact key x y hx hxy
    · rw [dist_comm, dist_comm (lineExponent μ x 1)]
      exact key y x hy hxy
  have hacont' : Continuous fun t => (P (max t 0)).a :=
    hacont.comp_continuous (continuous_id.max continuous_const) fun t => le_max_right t 0
  have hamono : Monotone fun t => (P (max t 0)).a := fun s t h =>
    (foldedData_step hsf hP (le_max_right s 0) (max_le_max h le_rfl)).1
  set F : StieltjesFunction ℝ :=
    ⟨fun t => (P (max t 0)).a, hamono, fun x => hacont'.continuousWithinAt⟩ with hF
  set B := F.measure with hB
  have hBIoc : ∀ s t : ℝ, B (Ioc s t) = ENNReal.ofReal ((P (max t 0)).a - (P (max s 0)).a) :=
    fun s t => F.measure_Ioc s t
  have hBt : ∀ t : ℝ, 0 ≤ t → B (Ioc 0 t) = ENNReal.ofReal (P t).a := by
    intro t ht
    rw [hBIoc, max_eq_left ht, max_self, hP0a, sub_zero]
  have hB0 : B (Iic 0) = 0 := by
    have hbot : Tendsto F atBot (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_le_atBot 0] with t ht
      change 0 = (P (max t 0)).a
      rw [max_eq_right ht, hP0a]
    rw [hB, F.measure_Iic hbot 0]
    change ENNReal.ofReal ((P (max 0 0)).a - 0) = 0
    rw [max_self, hP0a, sub_zero, ENNReal.ofReal_zero]
  have hBy : ∀ y : ℝ, B {y} = 0 := by
    intro y
    have hlim : Function.leftLim F y = F y := leftLim_eq_of_tendsto (nhdsLT_neBot y).ne
      (hacont'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    rw [hB, F.measure_singleton, hlim, sub_self, ENNReal.ofReal_zero]
  have hm : Measurable fun y : ℝ => y / q := measurable_id.div_const q
  have hpreIoc : ∀ t : ℝ, (fun y : ℝ => y / q) ⁻¹' Ioc 0 t = Ioc 0 (q * t) := by
    intro t
    ext y
    simp only [mem_preimage, mem_Ioc]
    rw [div_pos_iff_of_pos_right hq0, div_le_iff₀ hq0, mul_comm t q]
  have hmapB : B.map (fun y => y / q) = ENNReal.ofReal (q ^ 2) • B := by
    have hpre0 : (fun y : ℝ => y / q) ⁻¹' Iic 0 = Iic 0 := by
      ext y
      simp only [mem_preimage, mem_Iic]
      rw [div_le_iff₀ hq0, zero_mul]
    refine measure_ext_of_Ioc_zero ?_ ?_ (fun t ht => ?_) (fun t ht => ?_)
    · rw [Measure.map_apply hm measurableSet_Iic, hpre0, hB0]
    · rw [Measure.smul_apply, hB0, smul_zero]
    · rw [Measure.map_apply hm measurableSet_Ioc, hpreIoc, hBt _ (by positivity)]
      exact ENNReal.ofReal_ne_top
    · rw [Measure.map_apply hm measurableSet_Ioc, hpreIoc, hBt _ (by positivity),
        (foldedData_cov hμ hq0 hP ht.le).1, ENNReal.ofReal_mul (sq_nonneg q), Measure.smul_apply,
        smul_eq_mul, hBt t ht.le]
  have hBscale : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioi 0 →
      B ((fun y => q * y) '' A) = ENNReal.ofReal (q ^ 2) * B A := by
    intro A hA _
    have himg : (fun y => q * y) '' A = (fun y : ℝ => y / q) ⁻¹' A := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [mem_preimage]
        rwa [mul_div_cancel_left₀ x hq0.ne']
      · intro hy
        exact ⟨y / q, hy, by field_simp⟩
    rw [himg, ← Measure.map_apply hm hA, hmapB, Measure.smul_apply, smul_eq_mul]
  -- (i): the invariance
  have hqm : MeasurableSet quadrantᶜ := (measurableSet_Ioi.prod measurableSet_Ioi).compl
  have hsl : ∀ t : ℝ, 0 < t → slab (Λ.map (scaleDiag q)) 0 t = slab Λ 0 t := by
    intro t ht
    have htq : 0 < t / q := div_pos ht hq0
    have e : q * (t / q) = t := by field_simp
    rw [slab_map_scaleDiag hq0, zero_div, hΛP _ htq, hΛP t ht,
      ← (foldedData_cov hμ hq0 hP htq.le).2, e]
  have hinv : Λ.map (scaleDiag q) = Λ := by
    refine quadrant_measure_ext ?_ hΛc (fun t ht ε hε => ?_) hsl
    · rw [Measure.map_apply (measurable_scaleDiag q) hqm, preimage_compl,
        scaleDiag_preimage_quadrant hq0, hΛc]
    · rw [hsl t ht, hΛP t ht]
      exact SymLevyPair_measure_Ioi_ne_top _ hε
  -- the slabs between two scales
  have hsplit : ∀ s t : ℝ, 0 < s → s ≤ t → ∀ A : Set ℝ, MeasurableSet A →
      (P t).ν A = (P s).ν A + Λ (Ioc s t ×ˢ A) := by
    intro s t hs hst A hA
    rw [← hΛP t (hs.trans_le hst), ← hΛP s hs, slab_apply _ _ _ hA, slab_apply _ _ _ hA,
      ← measure_union (Disjoint.set_prod_left (Ioc_disjoint_Ioc_of_le le_rfl) _ _)
        (measurableSet_Ioc.prod hA), ← union_prod, Ioc_union_Ioc_eq_Ioc hs.le hst]
  have hΛIoc : ∀ s t : ℝ, 0 < s → s ≤ t → ∀ ε : ℝ, 0 < ε → ∀ A : Set ℝ, MeasurableSet A →
      A ⊆ Ioi ε → Λ (Ioc s t ×ˢ A) ≤ (ENNReal.ofReal (min 1 (ε ^ 2)))⁻¹ *
        ENNReal.ofReal (avgExponent μ t - avgExponent μ s) := by
    intro s t hs hst ε hε A hA hAε
    have hfin : (P s).ν A ≠ ⊤ :=
      ne_top_of_le_ne_top (SymLevyPair_measure_Ioi_ne_top _ hε) (measure_mono hAε)
    rw [← ENNReal.add_le_add_iff_left hfin, ← hsplit s t hs hst A hA]
    exact foldedData_measure_le hsf hP hs.le hst hε hAε
  -- (iii)
  have hline : ∀ y : ℝ, 0 < y → Λ ({y} ×ˢ Ioi 0) = 0 := by
    intro y hy
    have hU : ({y} : Set ℝ) ×ˢ Ioi (0 : ℝ) = ⋃ n : ℕ, {y} ×ˢ Ioi (1 / ((n : ℝ) + 1)) := by
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
    have hc : (ENNReal.ofReal (min 1 ((1 / ((n : ℝ) + 1)) ^ 2)))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.2 (by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        exact lt_min one_pos (by positivity))
    refine nonpos_iff_eq_zero.1 (ge_of_tendsto (tendsto_avgExponent_left hsf hy hc) ?_)
    filter_upwards [Ioo_mem_nhdsLT hy] with s hs'
    exact (measure_mono (Set.prod_mono (singleton_subset_iff.2 (mem_Ioc.2 ⟨hs'.2, le_rfl⟩))
      le_rfl)).trans
      (hΛIoc s y hs'.1 hs'.2.le _ hε _ measurableSet_Ioi le_rfl)
  -- (iv)
  have hnd : ∀ s t : ℝ, 0 < s → s < t → 0 < Λ (Ioc s t ×ˢ Ioi 0) + B (Ioc s t) := by
    intro s t hs hst
    rw [pos_iff_ne_zero]
    intro h0
    obtain ⟨hΛ0, hB0'⟩ := add_eq_zero.1 h0
    obtain ⟨ha, -, Q, hQa, hQν, hQ⟩ := foldedData_step hsf hP hs.le hst.le
    have hQa0 : Q.a = 0 := by
      rw [hBIoc, max_eq_left (hs.le.trans hst.le), max_eq_left hs.le,
        ENNReal.ofReal_eq_zero] at hB0'
      linarith
    have hQν0 : Q.ν = 0 := by
      refine measure_ext_of_Ioi Q.ν_folded (by simp) fun ε hε A hA hAε => ?_
      have h1 := hsplit s t hs hst.le A hA
      rw [measure_mono_null (Set.prod_mono le_rfl (hAε.trans (Ioi_subset_Ioi hε.le))) hΛ0,
        add_zero, ← hQν, Measure.add_apply] at h1
      have hfin : (P s).ν A ≠ ⊤ :=
        ne_top_of_le_ne_top (SymLevyPair_measure_Ioi_ne_top _ hε) (measure_mono hAε)
      have h2 : (P s).ν A + Q.ν A = (P s).ν A + 0 := by
        rw [add_zero, add_comm]
        exact h1
      rw [Measure.coe_zero, Pi.zero_apply]
      exact (ENNReal.add_right_inj hfin).1 h2
    haveI := hsf.1.isProbability s t hs.le hst.le
    have hstep : ∀ ω : ℝ, charFun (μ s t) ω = ((Real.exp (-(Q.exponent ω)) : ℝ) : ℂ) := by
      intro ω
      rw [hQ ω, lineExponent_eq_of_folded hsf (hs.le.trans hst.le) (hP t (hs.le.trans hst.le)),
        lineExponent_eq_of_folded hsf hs.le (hP s hs.le)]
      exact charFun_step_of_folded hsf.1 hP hs.le hst.le ω
    obtain ⟨ω, hω⟩ := exists_ne_zero_of_ne_dirac hstep (hsf.2.1 s t hs.le hst)
    apply hω
    simp [SymLevyPair.exponent, SymLevyPair.exponentL, hQa0, hQν0]
  refine ⟨Λ, B, ⟨hΛc, hinv, fun t ht => ?_, ⟨hB0, fun t ht => ?_, hBscale⟩,
    fun y hy => ⟨hline y hy, hBy y⟩, hnd⟩,
    fun t ht => ⟨P t, hP t ht.le, (hΛP t ht).symm, (hBt t ht.le).symm⟩⟩
  · rw [hΛP t ht]
    exact (P t).ν_integrable
  · rw [hBt t ht.le]
    exact ENNReal.ofReal_ne_top

/-- **`thm:surface-measure`, the pair is unique**: any measures on `(0,∞)²` and `(0,∞)` giving the
family by (A.e1) are its pair. The hypotheses `1 < q` and `IsQFamily q μ` of the skeleton are not
used: the slabs and the masses `ℬ((0,t])` are fixed by the transform of `μ_t` alone. -/
theorem surface_measure_unique {q : ℝ} (μ : ℝ → ℝ → Measure ℝ) (Λ : Measure (ℝ × ℝ))
    (B : Measure ℝ) (h : IsFamilyPair q μ Λ B) (Λ' : Measure (ℝ × ℝ)) (B' : Measure ℝ)
    (hΛ' : Λ' quadrantᶜ = 0) (hB' : B' (Iic 0) = 0) (h' : IsSurfaceDataOf μ Λ' B') :
    Λ' = Λ ∧ B' = B := by
  have hdata : ∀ t : ℝ, 0 < t → slab Λ' 0 t = slab Λ 0 t ∧ B' (Ioc 0 t) = B (Ioc 0 t) ∧
      B' (Ioc 0 t) ≠ ⊤ ∧ ∀ ε : ℝ, 0 < ε → slab Λ' 0 t (Ioi ε) ≠ ⊤ := by
    intro t ht
    obtain ⟨P, hP, hPν, hPa⟩ := h.2 t ht
    obtain ⟨P', hP', hP'ν, hP'a⟩ := h' t ht
    have he : ∀ ω : ℝ, P'.exponent ω = P.exponent ω := fun ω => by
      have h2 := Real.exp_injective (Complex.ofReal_injective ((hP' ω).symm.trans (hP ω)))
      linarith
    obtain ⟨ha, hν⟩ := line_levy_unique P' P he
    refine ⟨by rw [← hP'ν, ← hPν, hν], by rw [← hP'a, ← hPa, ha], ?_, fun ε hε => ?_⟩
    · rw [← hP'a]
      exact ENNReal.ofReal_ne_top
    · rw [← hP'ν]
      exact SymLevyPair_measure_Ioi_ne_top _ hε
  exact ⟨quadrant_measure_ext hΛ' h.1.carried (fun t ht ε hε => (hdata t ht).2.2.2 ε hε)
    (fun t ht => (hdata t ht).1), measure_ext_of_Ioc_zero hB' h.1.gaussian.1
      (fun t ht => (hdata t ht).2.2.1) (fun t ht => (hdata t ht).2.1)⟩

end Pyramids
