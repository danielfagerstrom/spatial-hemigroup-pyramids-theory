/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.DiscreteCovarianceLine
import Pyramids.Pyramid.Synthesis
import Pyramids.Defs.LineAppendix

/-!
# `thm:annulus-parametrization`: one octave of exponents parametrizes the family

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:annulus-parametrization`. Wave 2e: the four
declarations moved here from `PyramidsSkeleton.ChA1Line`, their statements unchanged except that
`annulus_parametrization_map` drops the unused hypothesis `1 < q`, a strengthening.

## The route

The printed one, with the families read through their kernels (`IsQFamily`).

* **The map.** Each kernel `μ_t` and each step `μ_{t,t'}` is a symmetric infinitely divisible law
  (`lem:family-structure` at `d = 1`, through `ℝ¹`), so its exponent lies in `ND_s`
  (`lem:line-exponent-data`(1)); it is not identically zero because the law is not `δ₀` (ND).
  `Ψ_{t'} - Ψ_t` is the exponent of `μ_{t,t'}` by (I1). The gluing is covariance at the pair
  `(0, 1)`, and the continuity is (I2) with `μ̂_t > 0`.
* **Recovery and injectivity.** Covariance gives `Ψ_{qⁿu}(ω) = Ψ_u(qⁿω)` for `n ∈ ℤ`, so the
  extended path is `Ψ_t` at every `t ≥ 0`, and `μ̂_{s,t} = e^{-(Ψ_t - Ψ_s)}` by (I1). Two families
  with one path have one extended path, hence the same transforms.
* **Surjectivity** is `lem:synthesis` at `d = 1`. Each `Ψ_t ∈ ND_s` has folded data
  `(a(t), ϖ_t)`; in `ℝ¹` they are the data `(a(t), ϖ_t^s)`, `ϖ_t^s` the symmetric lift of `ϖ_t`,
  with the exponent `Ψ_t(z₀)`. The hypotheses of the synthesis lemma follow:
  `lem:line-exponent-data`(3) orders the data for `t < t'`, and the lift is monotone;
  `lem:line-exponent-data`(2) and the uniqueness of folded data (`lem:line-exponent-data`(1)) turn
  the gluing into `(a(q), ϖ_q) = (q²a(1), T_qϖ_1)`, and the lift commutes with the dilation. The
  laws on `ℝ¹` are read back on `ℝ` by `y ↦ y₀`, and the extended exponents of the synthesis are
  the extended path. No cited fact is used directly: A39 and A41 enter through
  `lem:family-structure`, `lem:line-exponent-data` and `lem:synthesis`.
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair IsSymLevyExponent)
open scoped Topology ComplexOrder

/-! ## The line inside `ℝ¹`, read back -/

theorem lineEmb_proj (y : Rd 1) : lineEmb (y 0) = y := by
  ext i
  rw [Subsingleton.elim i 0, lineEmb_apply_zero]

theorem map_lineEmb_lineProj (m : Measure (Rd 1)) : (m.map lineProjL).map lineEmbL = m := by
  rw [Measure.map_map lineEmbL.continuous.measurable lineProjL.continuous.measurable]
  have h : (lineEmbL ∘ lineProjL : Rd 1 → Rd 1) = id :=
    funext fun y => by simp [lineProjL_apply, lineEmbL_apply, lineEmb_proj]
  rw [h, Measure.map_id]

/-- **A symmetric family on `ℝ¹` is one on `ℝ`.** -/
theorem isSymmetricFamily_lineProj {ν : ℝ → ℝ → Measure (Rd 1)} (hν : IsSymmetricFamily ν) :
    IsSymmetricFamily (fun s t => (ν s t).map lineProjL) := by
  refine ⟨⟨fun s t hs hst => ?_, fun t ht => ?_, fun r s t hr hrs hst => ?_, fun ω => ?_⟩,
    fun s t hs hst h0 => ?_, fun s t hs hst => ?_⟩
  · haveI := hν.1.isProbability s t hs hst
    exact Measure.isProbabilityMeasure_map lineProjL.continuous.measurable.aemeasurable
  · rw [hν.1.diag t ht, Measure.map_dirac' lineProjL.continuous.measurable, map_zero]
  · haveI := hν.1.isProbability s t (hr.trans hrs) hst
    haveI := hν.1.isProbability r s hr hrs
    rw [hν.1.cascade r s t hr hrs hst, Measure.map_conv_continuousLinearMap]
  · simp only [charFun_map_lineProj]
    exact (hν.1.continuous (lineEmb ω))
  · apply hν.2.1 s t hs hst
    have h1 := congrArg (fun m : Measure ℝ => m.map lineEmbL) h0
    simp only [map_lineEmb_lineProj] at h1
    rw [h1, Measure.map_dirac' lineEmbL.continuous.measurable, map_zero]
  · rw [Measure.map_map measurable_neg lineProjL.continuous.measurable]
    have e : ((fun x : ℝ => -x) ∘ lineProjL) = lineProjL ∘ fun x : Rd 1 => -x :=
      funext fun x => (map_neg lineProjL x).symm
    rw [e, ← Measure.map_map lineProjL.continuous.measurable measurable_neg, hν.2.2 s t hs hst]

/-- **Covariance carries back from `ℝ¹`.** -/
theorem isCovariantAt_lineProj {ν : ℝ → ℝ → Measure (Rd 1)} {lam : ℝ} {S : ℝ → ℝ}
    (h : IsCovariantAt ν lam S) : IsCovariantAt (fun s t => (ν s t).map lineProjL) lam S := by
  refine ⟨h.1, fun s t hs hst => ?_⟩
  simp only
  rw [Measure.map_map (continuous_const_smul lam).measurable lineProjL.continuous.measurable]
  have e : ((fun x : ℝ => lam • x) ∘ lineProjL) = lineProjL ∘ fun x : Rd 1 => lam • x :=
    funext fun x => (map_smul lineProjL lam x).symm
  rw [e, ← Measure.map_map lineProjL.continuous.measurable (continuous_const_smul lam).measurable,
    h.2 s t hs hst]

/-! ## The data in `ℝ¹` of a folded pair -/

/-- **The data in `ℝ¹` of a folded pair** `(a, ϖ)`: the Gaussian datum `a` and the symmetric lift
`ϖ_s = ½(e_*ϖ + (-e)_*ϖ)` of `ϖ` (the affine export's `symLift`). -/
noncomputable def SymLevyPair_toData (P : SymLevyPair) : SymLevyData 1 where
  A := P.a • (1 : Mat 1)
  ν := symLift P.ν
  A_posSemidef := Matrix.PosSemidef.one.smul P.a_nonneg
  ν_zero := (symLevyTriplet P).ν_zero
  ν_integrable := (symLevyTriplet P).ν_integrable
  ν_symm := by
    have h := symLift_map_neg P.ν
    rwa [coe_neg_isometry] at h

theorem SymLevyPair_toData_triplet (P : SymLevyPair) :
    (SymLevyPair_toData P).triplet = symLevyTriplet P := by
  refine LevyTriplet.ext' ?_ rfl rfl
  change (2 : ℝ) • (P.a • (1 : Mat 1)) = (2 * P.a) • (1 : Mat 1)
  rw [smul_smul]

/-- The exponent of the data is the pair's: `Ψ(z) = aω² + ∫(1 - cos ωv) ϖ(dv)` at `ω = z₀`. -/
theorem SymLevyPair_toData_exponent (P : SymLevyPair) (z : Rd 1) :
    (SymLevyPair_toData P).exponent z = P.exponent (z 0) := by
  have h := (SymLevyPair_toData P).lkExponent_triplet z
  rw [SymLevyPair_toData_triplet, lkExponent_symLevyTriplet] at h
  exact_mod_cast (neg_inj.1 h).symm

theorem symLift_mono {ν ν' : Measure ℝ} (h : ν ≤ ν') : symLift ν ≤ symLift ν' := by
  rw [Measure.le_iff]
  intro s hs
  simp only [symLift, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.map_apply continuous_lineEmb.measurable hs, Measure.map_apply measurable_lineEmb_neg hs]
  gcongr

/-- The lift commutes with dilation. -/
theorem symLift_map_mul (ν : Measure ℝ) (c : ℝ) :
    symLift (ν.map fun x => c * x) = (symLift ν).map fun y => c • y := by
  have hc : Measurable fun x : ℝ => c * x := measurable_const_mul c
  have hs : Measurable fun y : Rd 1 => c • y := (continuous_const_smul c).measurable
  rw [symLift, symLift, Measure.map_smul, Measure.map_add _ _ hs,
    Measure.map_map continuous_lineEmb.measurable hc, Measure.map_map measurable_lineEmb_neg hc,
    Measure.map_map hs continuous_lineEmb.measurable, Measure.map_map hs measurable_lineEmb_neg]
  congr 3 <;> funext x <;> simp [lineEmb, smul_smul]

/-! ## The exponents of a family -/

section Family

variable {q : ℝ} {μ : ℝ → ℝ → Measure ℝ}

/-- `μ̂_t = e^{-Ψ_t}`, the transform being real and positive. -/
theorem charFun_kernel_eq_exp (hμ : IsSymmetricFamily μ) {t : ℝ} (ht : 0 ≤ t) (ω : ℝ) :
    charFun (μ 0 t) ω = ((Real.exp (-lineExponent μ t ω) : ℝ) : ℂ) := by
  have hK := kernelOrder_line hμ
  rw [lineExponent, neg_neg, Real.exp_log (hK.re_pos ht ω)]
  exact hK.charFun_eq_re ht ω

/-- `Ψ_0 = 0`. -/
theorem lineExponent_zero (hμ : IsSymmetricFamily μ) (ω : ℝ) : lineExponent μ 0 ω = 0 := by
  simp [lineExponent, hμ.1.diag 0 le_rfl, charFun_dirac]

/-- **The kernels have folded data.** -/
theorem exists_folded (hμ : IsSymmetricFamily μ) :
    ∃ P : ℝ → SymLevyPair, ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t) := by
  have h : ∀ t : ℝ, ∃ P : SymLevyPair, 0 ≤ t → IsFoldedData (μ 0 t) P := by
    intro t
    by_cases ht : 0 ≤ t
    · haveI := hμ.1.isProbability 0 t le_rfl ht
      obtain ⟨P, hP⟩ := line_exponent_data_1_converse (μ 0 t) (hμ.2.2 0 t le_rfl ht)
        (isLawHemigroup_line_infinitelyDivisible hμ.1 le_rfl ht)
      exact ⟨P, fun _ => hP⟩
    · exact ⟨SymLevyPair_zero, fun h => absurd h ht⟩
  choose P hP using h
  exact ⟨P, hP⟩

theorem lineExponent_eq_of_folded (hμ : IsSymmetricFamily μ) {t : ℝ} (ht : 0 ≤ t)
    {P : SymLevyPair} (hP : IsFoldedData (μ 0 t) P) (ω : ℝ) :
    lineExponent μ t ω = P.exponent ω := by
  have h := (charFun_kernel_eq_exp hμ ht ω).symm.trans (hP ω)
  have h2 := Real.exp_injective (Complex.ofReal_injective h)
  linarith

/-- Covariance at the pairs `(0, t)`: `Ψ_{qt}(ω) = Ψ_t(qω)`. -/
theorem lineExponent_cov (hμ : IsQFamily q μ) {t : ℝ} (ht : 0 ≤ t) (ω : ℝ) :
    lineExponent μ (q * t) ω = lineExponent μ t (q * ω) := by
  have hk : (μ 0 t).map (fun x => q • x) = μ 0 (q * t) := cov_kernel hμ.2 ht
  simp only [smul_eq_mul] at hk
  unfold lineExponent
  rw [← hk, charFun_map_mul]

/-- A law with transform `e^{-f}` and not `δ₀` has `f ≢ 0`. -/
theorem exists_ne_zero_of_ne_dirac {m : Measure ℝ} [IsProbabilityMeasure m] {f : ℝ → ℝ}
    (hf : ∀ ω : ℝ, charFun m ω = ((Real.exp (-f ω) : ℝ) : ℂ)) (hm : m ≠ Measure.dirac 0) :
    ∃ ω : ℝ, f ω ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hm (Measure.ext_of_charFun (funext fun ω => ?_))
  rw [hf ω, hcon ω, charFun_dirac]
  simp

end Family

/-- **The extension by covariance.** If `Ψ_0 = 0` and `Ψ_{qt}(ω) = Ψ_t(qω)` for `t ≥ 0`, then
`Ψ_{qⁿu}(ω) = Ψ_u(qⁿω)` for `n ∈ ℤ`, and the path's extension is `Ψ` itself on `[0,∞)`. -/
theorem annulusExtend_eq_of_cov {q : ℝ} (hq : 1 < q) (Ψ : ℝ → ℝ → ℝ)
    (h0 : ∀ ω : ℝ, Ψ 0 ω = 0)
    (hE : ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ, Ψ (q * t) ω = Ψ t (q * ω)) :
    ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ, annulusExtend q Ψ t ω = Ψ t ω := by
  have hq0 : 0 < q := by linarith
  have hnat : ∀ k : ℕ, ∀ u : ℝ, 0 ≤ u → ∀ ω : ℝ, Ψ (q ^ k * u) ω = Ψ u (q ^ k * ω) := by
    intro k
    induction k with
    | zero => intro u _ ω; simp
    | succ k ih =>
      intro u hu ω
      rw [show q ^ (k + 1) * u = q * (q ^ k * u) by ring, hE _ (by positivity), ih u hu,
        show q ^ k * (q * ω) = q ^ (k + 1) * ω by ring]
  have hint : ∀ n : ℤ, ∀ u : ℝ, 0 ≤ u → ∀ ω : ℝ, Ψ (q ^ n * u) ω = Ψ u (q ^ n * ω) := by
    intro n u hu ω
    rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
    · simpa only [zpow_natCast] using hnat k u hu ω
    · have hk : 0 < q ^ k := pow_pos hq0 k
      rw [zpow_neg, zpow_natCast]
      have h := hnat k ((q ^ k)⁻¹ * u) (by positivity) ((q ^ k)⁻¹ * ω)
      rw [mul_inv_cancel_left₀ hk.ne', mul_inv_cancel_left₀ hk.ne'] at h
      exact h.symm
  intro t ht ω
  rcases ht.eq_or_lt with h | h
  · subst h
    rw [annulusExtend, if_pos le_rfl, h0]
  · rw [annulusExtend, if_neg (not_le.2 h)]
    have hu : 0 ≤ q ^ (-dgLevel q t) * t := by positivity
    have e : q ^ dgLevel q t * (q ^ (-dgLevel q t) * t) = t := by
      rw [← mul_assoc, ← zpow_add₀ hq0.ne', add_neg_cancel, zpow_zero, one_mul]
    rw [← hint (dgLevel q t) _ hu ω, e]

/-! ## `thm:annulus-parametrization` -/

/-- **`thm:annulus-parametrization`, the map.** The exponents of a family, on `[1,q]`, satisfy
(1)–(4). -/
theorem annulus_parametrization_map {q : ℝ} (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsQFamily q μ) : IsAnnulusPath q (lineExponent μ) := by
  have hK := kernelOrder_line hμ.1
  obtain ⟨P, hP⟩ := exists_folded hμ.1
  have hLP : ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ, lineExponent μ t ω = (P t).exponent ω :=
    fun t ht ω => lineExponent_eq_of_folded hμ.1 ht (hP t ht) ω
  -- the exponent of a step
  have hstep : ∀ t t' : ℝ, 0 ≤ t → t ≤ t' → ∀ ω : ℝ, charFun (μ t t') ω =
      ((Real.exp (-(lineExponent μ t' ω - lineExponent μ t ω)) : ℝ) : ℂ) := by
    intro t t' ht htt' ω
    rw [hLP t' (ht.trans htt'), hLP t ht]
    exact charFun_step_of_folded hμ.1.1 hP ht htt' ω
  refine ⟨fun t ht => ⟨⟨P t, hLP t (by linarith [ht.1])⟩, ?_⟩,
    fun t t' ht htt' ht'q => ⟨?_, ?_⟩, fun ω => ?_, fun ω => ?_⟩
  · -- `Ψ_t ≢ 0`
    have ht0 : 0 < t := by linarith [ht.1]
    haveI := hμ.1.1.isProbability 0 t le_rfl ht0.le
    exact exists_ne_zero_of_ne_dirac (charFun_kernel_eq_exp hμ.1 ht0.le) (hμ.1.2.1 0 t le_rfl ht0)
  · -- `Ψ_{t'} - Ψ_t ∈ ND_s`: the exponent of the step
    have h0 : 0 ≤ t := by linarith
    haveI := hμ.1.1.isProbability t t' h0 htt'.le
    obtain ⟨R, hR⟩ := line_exponent_data_1_converse (μ t t') (hμ.1.2.2 t t' h0 htt'.le)
      (isLawHemigroup_line_infinitelyDivisible hμ.1.1 h0 htt'.le)
    refine ⟨R, fun ω => ?_⟩
    have h1 := (hstep t t' h0 htt'.le ω).symm.trans (hR ω)
    have h2 := Real.exp_injective (Complex.ofReal_injective h1)
    linarith
  · -- `Ψ_{t'} - Ψ_t ≢ 0`, by (ND)
    have h0 : 0 ≤ t := by linarith
    haveI := hμ.1.1.isProbability t t' h0 htt'.le
    exact exists_ne_zero_of_ne_dirac (hstep t t' h0 htt'.le) (hμ.1.2.1 t t' h0 htt')
  · -- gluing
    have h := lineExponent_cov hμ zero_le_one ω
    rwa [mul_one] at h
  · -- continuity, from (I2) and `μ̂_t > 0`
    have hc : ContinuousOn (fun t => charFun (μ 0 t) ω) (Ici 0) :=
      (hμ.1.1.continuous ω).comp (continuous_const.prodMk continuous_id).continuousOn
        fun t ht => ⟨le_rfl, ht⟩
    have hre : ContinuousOn (fun t => (charFun (μ 0 t) ω).re) (Icc 1 q) :=
      (Complex.continuous_re.comp_continuousOn hc).mono fun t ht => zero_le_one.trans ht.1
    exact (hre.log fun t ht => (hK.re_pos (zero_le_one.trans ht.1) ω).ne').neg

/-- **`thm:annulus-parametrization`, the recovery.** A family is recovered from its path by
`Ψ_{qⁿt} := Ψ_t(qⁿ ·)`, `t ∈ [1,q)`, `Ψ_0 := 0` and `μ̂_{s,t} = e^{-(Ψ_t - Ψ_s)}`. -/
theorem annulus_parametrization_recover {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsQFamily q μ) : IsExponentLaws (annulusExtend q (lineExponent μ)) μ := by
  obtain ⟨P, hP⟩ := exists_folded hμ.1
  have hext := annulusExtend_eq_of_cov hq (lineExponent μ) (lineExponent_zero hμ.1)
    fun t ht ω => lineExponent_cov hμ ht ω
  intro s t hs hst
  refine ⟨hμ.1.1.isProbability s t hs hst, fun ω => ?_⟩
  rw [hext t (hs.trans hst), hext s hs,
    lineExponent_eq_of_folded hμ.1 (hs.trans hst) (hP t (hs.trans hst)),
    lineExponent_eq_of_folded hμ.1 hs (hP s hs)]
  exact charFun_step_of_folded hμ.1.1 hP hs hst ω

/-- **`thm:annulus-parametrization`, injectivity.** Two families with the same exponents on
`[1,q]` have the same laws. -/
theorem annulus_parametrization_injective {q : ℝ} (hq : 1 < q) (μ μ' : ℝ → ℝ → Measure ℝ)
    (hμ : IsQFamily q μ) (hμ' : IsQFamily q μ')
    (heq : ∀ t ∈ Icc 1 q, ∀ ω : ℝ, lineExponent μ t ω = lineExponent μ' t ω) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t := by
  have h1 := annulus_parametrization_recover hq μ hμ
  have h2 := annulus_parametrization_recover hq μ' hμ'
  have hext : annulusExtend q (lineExponent μ) = annulusExtend q (lineExponent μ') := by
    funext t ω
    unfold annulusExtend
    split_ifs with ht
    · rfl
    · rw [heq _ (Ico_subset_Icc_self (octave_mem hq (not_le.1 ht)))]
  intro s t hs hst
  obtain ⟨hp, hc⟩ := h1 s t hs hst
  obtain ⟨hp', hc'⟩ := h2 s t hs hst
  exact Measure.ext_of_charFun (funext fun ω => by rw [hc, hc', hext])

/-- **`thm:annulus-parametrization`, surjectivity.** For a path with (1)–(4), laws with
`μ̂_{s,t} = e^{-(Ψ_t - Ψ_s)}` for the extended `Ψ` exist, and any such laws form a family whose
path is the given one. -/
theorem annulus_parametrization_surjective {q : ℝ} (hq : 1 < q) (Ψ : ℝ → ℝ → ℝ)
    (hΨ : IsAnnulusPath q Ψ) :
    (∃ μ : ℝ → ℝ → Measure ℝ, IsExponentLaws (annulusExtend q Ψ) μ) ∧
      ∀ μ : ℝ → ℝ → Measure ℝ, IsExponentLaws (annulusExtend q Ψ) μ →
        IsQFamily q μ ∧ ∀ t ∈ Icc 1 q, ∀ ω : ℝ, lineExponent μ t ω = Ψ t ω := by
  have hq0 : 0 < q := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  -- the folded data of the path, and their data in `ℝ¹`
  have hex : ∀ t : ℝ, ∃ P : SymLevyPair, t ∈ Icc 1 q → HasExpData (Ψ t) P := by
    intro t
    by_cases ht : t ∈ Icc 1 q
    · obtain ⟨P, hP⟩ := (hΨ.nd t ht).1
      exact ⟨P, fun _ => hP⟩
    · exact ⟨SymLevyPair_zero, fun h => absurd h ht⟩
  choose P hP using hex
  set D : ℝ → SymLevyData 1 := fun t => SymLevyPair_toData (P t) with hDdef
  have hD : ∀ t ∈ Icc 1 q, ∀ z : Rd 1, (D t).exponent z = Ψ t (z 0) := fun t ht z => by
    rw [hDdef, SymLevyPair_toData_exponent, hP t ht]
  have h1q : (1 : ℝ) ∈ Icc 1 q := ⟨le_rfl, hq.le⟩
  have hqq : q ∈ Icc 1 q := ⟨hq.le, le_rfl⟩
  -- the hypotheses of `lem:synthesis`
  have hsyn : IsSynthesisData q D := by
    refine ⟨fun ω => (hΨ.continuous (ω 0)).congr fun t ht => hD t ht ω,
      fun s t hs hst ht => ?_, ?_⟩
    · have hsI : s ∈ Icc 1 q := ⟨hs, by linarith⟩
      have htI : t ∈ Icc 1 q := ⟨by linarith, ht⟩
      obtain ⟨hR, ω0, hω0⟩ := hΨ.increments s t hs hst ht
      obtain ⟨ha, hν⟩ :=
        (line_exponent_data_3 (Ψ s) (Ψ t) (P s) (P t) (hP s hsI) (hP t htI)).1.1 hR
      refine ⟨?_, symLift_mono hν, fun heq => hω0 ?_⟩
      · change ((P t).a • (1 : Mat 1) - (P s).a • (1 : Mat 1)).PosSemidef
        rw [← sub_smul]
        exact Matrix.PosSemidef.one.smul (sub_nonneg.2 ha)
      · obtain ⟨hAe, hνe⟩ := Prod.mk.inj heq
        have he : (D s).exponent (lineEmb ω0) = (D t).exponent (lineEmb ω0) := by
          unfold SymLevyData.exponent
          rw [hAe, hνe]
        rw [hD t htI, hD s hsI, lineEmb_apply_zero] at he
        linarith
    · obtain ⟨Q, hQa, hQν, hQ⟩ := line_exponent_data_2 (Ψ 1) (P 1) (hP 1 h1q) hq0
      obtain ⟨ha, hν⟩ := line_exponent_data_1_unique (fun ω => Ψ 1 (q * ω)) (P q) Q
        (fun ω => by simp only; rw [← hΨ.glue ω]; exact hP q hqq ω) hQ
      refine ⟨?_, ?_⟩
      · change (P q).a • (1 : Mat 1) = q ^ 2 • ((P 1).a • (1 : Mat 1))
        rw [ha, hQa, smul_smul]
      · change symLift (P q).ν = (symLift (P 1).ν).map fun x => q • x
        rw [hν, hQν, symLift_map_mul]
  obtain ⟨-, ⟨μ1, hμ1⟩, hfam⟩ := synthesis hq D hsyn
  -- the extended exponents of the synthesis are the extended path
  have hlink : ∀ (t : ℝ) (z : Rd 1), octaveExponent q D t z = annulusExtend q Ψ t (z 0) := by
    intro t z
    rcases le_or_gt t 0 with ht | ht
    · rw [← octaveData_exponent hq, octaveData_of_nonpos q D ht, SymLevyData.zero_exponent,
        annulusExtend, if_pos ht]
    · rw [← octaveData_exponent hq, octaveData, dif_pos ⟨ht, hqne⟩, SymLevyData.dilate_exponent,
        hD _ (Ico_subset_Icc_self (octave_mem hq ht)), annulusExtend, if_neg (not_le.2 ht)]
      congr 1
  refine ⟨⟨fun s t => (μ1 s t).map lineProjL, fun s t hs hst => ?_⟩, fun μ hμ => ?_⟩
  · obtain ⟨hp, hc⟩ := hμ1 s t hs hst
    haveI := hp
    refine ⟨Measure.isProbabilityMeasure_map lineProjL.continuous.aemeasurable, fun ω => ?_⟩
    rw [charFun_map_lineProj, hc, hlink, hlink, lineEmb_apply_zero]
  -- any laws with these transforms
  set μ1' : ℝ → ℝ → Measure (Rd 1) := fun s t => (μ s t).map lineEmbL with hμ1'
  have hlaws : IsExponentLaws (octaveExponent q D) μ1' := by
    intro s t hs hst
    obtain ⟨hp, hc⟩ := hμ s t hs hst
    haveI := hp
    refine ⟨Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable, fun z => ?_⟩
    rw [hμ1', charFun_map_lineEmb, hc, hlink, hlink]
  obtain ⟨hsf, hcov⟩ := hfam μ1' hlaws
  have hsfμ : IsSymmetricFamily μ := by
    have h := isSymmetricFamily_lineProj hsf
    simpa only [hμ1', map_lineProj_lineEmb] using h
  have hcovμ : IsCovariantAt μ q (fun t => q * t) := by
    have h := isCovariantAt_lineProj hcov
    simpa only [hμ1', map_lineProj_lineEmb] using h
  refine ⟨⟨hsfμ, hcovμ⟩, fun t ht ω => ?_⟩
  have ht0 : 0 ≤ t := zero_le_one.trans ht.1
  obtain ⟨-, hc⟩ := hμ 0 t le_rfl ht0
  have hval : annulusExtend q Ψ t ω = Ψ t ω := by
    have htpos : ¬ t ≤ 0 := not_le.2 (lt_of_lt_of_le one_pos ht.1)
    rcases ht.2.lt_or_eq with hlt | heq
    · have hlev : dgLevel q t = 0 := dgLevel_eq hq (by simpa using ht.1) (by simpa using hlt)
      rw [annulusExtend, if_neg htpos, hlev]
      simp
    · rw [heq] at htpos ⊢
      have hlev : dgLevel q q = 1 := dgLevel_eq hq (by simp) (by
        rw [show (1 : ℤ) + 1 = 2 by norm_num, zpow_two]
        nlinarith)
      rw [annulusExtend, if_neg htpos, hlev, zpow_neg_one, inv_mul_cancel₀ hqne, zpow_one,
        ← hΨ.glue]
  have h0 : annulusExtend q Ψ 0 ω = 0 := by rw [annulusExtend, if_pos le_rfl]
  rw [lineExponent, hc ω, Complex.ofReal_re, Real.log_exp, h0, sub_zero, neg_neg, hval]

end Pyramids
