/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.AnnulusPhase
import Pyramids.LineAppendix.SurfaceFamily
import Pyramids.Cited.A9

/-!
# `thm:lattice-line`: the three strata on the line

Blueprint: `blueprint/src/parts/02-line.tex`, `thm:lattice-line`. Wave 3d: the five declarations
moved here from `PyramidsSkeleton.Ch02Line`, their statements unchanged.

## The route

* **(1).** The kernels are a symmetric family (`lem:line-axioms-kernels`(1)); the data are
  nondecreasing and the step `μ_{s,t}` has the data `(a(t) - a(s), ϖ_t - ϖ_s)` by
  `lem:line-exponent-data`(3), since `Ψ_t - Ψ_s` is the exponent of the symmetric infinitely
  divisible step; the continuity is that of `t ↦ -log μ̂_{0,t}(ω)`.
* **(1), the converse, directly on `ℝ`.** For `0 ≤ s ≤ t` the difference `Ψ_t - Ψ_s` lies in
  `ND_s` (`lem:line-exponent-data`(3)), so it is `-log μ̂` of a symmetric law `μ_{s,t}`
  (`lem:line-exponent-data`(1)). (I1) and (I2) are identities of transforms, (ND) is the
  uniqueness of the folded pair (`thm:cited-A9`) against the distinctness of the pairs, and
  `lem:line-axioms-kernels`(2) gives the operators. The print's route through
  `thm:lattice-strata`(1) at `d = 1` would need the folded data carried to `ℝ¹` and back; the
  construction on the line is shorter.
* **(2).** `lem:discrete-covariance-line`, and its "then" iterated over `n ∈ ℤ`.
* **(3).** "Only if": `thm:cited-A4` on the operators (`exists_profile_of_fullCov`) gives
  `Ψ_t = F(χ(t) ·)`; with `ψ := χ⁻¹`, `Ψ_{ψ(t)} = F(t ·)`, whose folded pair is
  `(αt², k(·/t) v⁻¹dv)` (`dilatePair`), and `thm:cited-A9` identifies it with the data.
  "If": the relabelled operators are covariant with `S'_λ t = λt` (`lattice_line_3_then`), so the
  original ones are with `S_λ := ψ ∘ (λ ·) ∘ χ`.
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X CascadeCore IsScaleCovariant IsKernelFamily IsSymmetric SymLevyPair
  IsSymLevyExponent SDProfile profileMeasure)
open scoped Topology ENNReal

/-! ## The dilated pair of a profile -/

/-- **The folded pair of `F(c ·)`**, `F` the admissible exponent of `(α, k)` and `c > 0`:
`(αc², k(·/c) v⁻¹dv)`. -/
noncomputable def dilatePair (D : SDProfile) {c : ℝ} (hc : 0 < c) : SymLevyPair where
  a := D.a * c ^ 2
  ν := profileMeasure fun u => D.k (u / c)
  a_nonneg := mul_nonneg D.a_nonneg (sq_nonneg c)
  ν_folded := ScaleSpace.isFolded_profileMeasure _
  ν_integrable := ScaleSpace.lintegral_min_profileMeasure_comp_div_ne_top D.k_antitone D.k_nonneg
    ((ScaleSpace.profile_integrability D.k_nonneg
      (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi D.k_antitone)).mpr
        ⟨D.integrable_near_zero, D.integrable_at_top⟩) hc

theorem dilatePair_exponent (D : SDProfile) {c : ℝ} (hc : 0 < c) (ω : ℝ) :
    (dilatePair D hc).exponent ω = D.exponent (c * ω) := by
  have hkc0 : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ D.k (x / c) := fun x hx =>
    D.k_nonneg _ (mem_Ioi.mpr (div_pos hx hc))
  have hkcm : AEMeasurable (fun u : ℝ => D.k (u / c)) (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi
      (ScaleSpace.antitoneOn_comp_div D.k_antitone hc)
  rw [SymLevyPair.exponent, SDProfile.exponent, SymLevyPair.exponentL,
    SDProfile.exponentL_eq_add_jump]
  change (ENNReal.ofReal (D.a * c ^ 2 * ω ^ 2) +
      ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂(profileMeasure fun u => D.k (u / c))).toReal = _
  rw [ScaleSpace.lintegral_one_sub_cos_profileMeasure hkc0 hkcm ω,
    ScaleSpace.profileJumpL_comp_div D.k hc ω, show D.a * c ^ 2 * ω ^ 2 = D.a * (c * ω) ^ 2 by ring]

/-! ## (1) -/

/-- **`thm:lattice-line`(1), no covariance.** `a(t)` and `ϖ_t` are nondecreasing; every step
`μ_{s,t}` is a symmetric infinitely divisible law with the folded data
`(a(t) - a(s), ϖ_t - ϖ_s)`; `t ↦ Ψ_t(ω)` is continuous. -/
theorem lattice_line_1 (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ) (hμ : IsKernelFamily C.Φ μ)
    (P : ℝ → SymLevyPair) (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) :
    MonotoneOn (fun t => (P t).a) (Ici 0) ∧ MonotoneOn (fun t => (P t).ν) (Ici 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsSymmetric (μ s t) ∧ IsInfinitelyDivisible (μ s t) ∧
        ∃ Q : SymLevyPair, Q.a = (P t).a - (P s).a ∧ Q.ν + (P s).ν = (P t).ν ∧
          IsFoldedData (μ s t) Q) ∧
      ∀ ω : ℝ, ContinuousOn (fun t => (P t).exponent ω) (Ici 0) := by
  have hfam := line_axioms_kernels_1_family C μ hμ
  refine ⟨fun s hs t _ hst => (foldedData_mono hfam hP hs hst).1,
    fun s hs t _ hst => (foldedData_mono hfam hP hs hst).2, fun s t hs hst => ?_, fun ω => ?_⟩
  · obtain ⟨ha, hν⟩ := foldedData_mono hfam hP hs hst
    obtain ⟨Q, hQa, hQν, hQ⟩ := (line_exponent_data_3 (P s).exponent (P t).exponent (P s) (P t)
      (fun _ => rfl) (fun _ => rfl)).2 ha hν
    refine ⟨hfam.2.2 s t hs hst, isLawHemigroup_line_infinitelyDivisible hfam.1 hs hst,
      Q, hQa, hQν, fun ω => ?_⟩
    rw [charFun_step_of_folded hfam.1 hP hs hst ω,
      show (P t).exponent ω - (P s).exponent ω = Q.exponent ω from hQ ω]
  · exact (lineExponent_continuousOn hfam ω).congr fun t ht =>
      (lineExponent_eq_of_folded hfam ht (hP t ht) ω).symm

/-- **`thm:lattice-line`(1), the converse.** Folded pairs `(a(t), ϖ_t)`, `t ≥ 0`, with
`(a(0), ϖ_0) = (0, 0)`, nondecreasing and distinct at distinct scales, with `t ↦ Ψ_t(ω)`
continuous, are the folded data of the kernels of a family with (A1)–(A7) and (ND). -/
theorem lattice_line_1_converse (P : ℝ → SymLevyPair) (h0a : (P 0).a = 0) (h0ν : (P 0).ν = 0)
    (hmono : ∀ s t : ℝ, 0 ≤ s → s < t →
      (P s).a ≤ (P t).a ∧ (P s).ν ≤ (P t).ν ∧ ((P s).a, (P s).ν) ≠ ((P t).a, (P t).ν))
    (hcont : ∀ ω : ℝ, ContinuousOn (fun t => (P t).exponent ω) (Ici 0)) :
    ∃ (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ), IsKernelFamily C.Φ μ ∧
      ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t) := by
  classical
  have hle : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (P s).a ≤ (P t).a ∧ (P s).ν ≤ (P t).ν := by
    intro s t hs hst
    rcases hst.eq_or_lt with h | h
    · subst h
      exact ⟨le_rfl, le_rfl⟩
    · exact ⟨(hmono s t hs h).1, (hmono s t hs h).2.1⟩
  -- the laws with the transforms `e^{-(Ψ_t - Ψ_s)}`
  have hex : ∀ s t : ℝ, ∃ m : Measure ℝ, 0 ≤ s → s ≤ t →
      IsProbabilityMeasure m ∧ IsSymmetric m ∧
        ∀ ω : ℝ, charFun m ω = ((Real.exp (-((P t).exponent ω - (P s).exponent ω)) : ℝ) : ℂ) := by
    intro s t
    by_cases h : 0 ≤ s ∧ s ≤ t
    · have hψ : IsSymLevyExponent (fun ω => (P t).exponent ω - (P s).exponent ω) :=
        ((line_exponent_data_3 (P s).exponent (P t).exponent (P s) (P t) (fun _ => rfl)
          (fun _ => rfl)).1).2 (hle s t h.1 h.2)
      obtain ⟨m, ⟨hm1, hm2, -, hm4⟩, -⟩ := line_exponent_data_1 _ hψ
      exact ⟨m, fun _ _ => ⟨hm1, hm2, hm4⟩⟩
    · exact ⟨0, fun hs hst => absurd ⟨hs, hst⟩ h⟩
  choose μ hμ using hex
  have hexp0 : ∀ ω, (P 0).exponent ω = 0 := fun ω => by
    simp [SymLevyPair.exponent, SymLevyPair.exponentL, h0a, h0ν]
  have hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t) :=
    fun s t hs hst => (hμ s t hs hst).1
  have hfam : IsSymmetricFamily μ := by
    refine ⟨⟨hprob, fun t ht => ?_, fun r s t hr hrs hst => ?_, fun ω => ?_⟩,
      fun s t hs hst h => ?_, fun s t hs hst => (hμ s t hs hst).2.1⟩
    · -- `μ_{t,t} = δ₀`
      haveI := hprob t t ht le_rfl
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      rw [(hμ t t ht le_rfl).2.2 ω, charFun_dirac]
      simp
    · -- `μ_{r,t} = μ_{s,t} ∗ μ_{r,s}`
      haveI := hprob r t hr (hrs.trans hst)
      haveI := hprob s t (hr.trans hrs) hst
      haveI := hprob r s hr hrs
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      rw [charFun_conv, (hμ r t hr (hrs.trans hst)).2.2 ω, (hμ s t (hr.trans hrs) hst).2.2 ω,
        (hμ r s hr hrs).2.2 ω, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3
      ring
    · -- continuity of the transforms
      have h1 : ContinuousOn (fun p : ℝ × ℝ => (P p.2).exponent ω)
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
        (hcont ω).comp continuous_snd.continuousOn fun p hp => mem_Ici.2 (hp.1.trans hp.2)
      have h2 : ContinuousOn (fun p : ℝ × ℝ => (P p.1).exponent ω)
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
        (hcont ω).comp continuous_fst.continuousOn fun p hp => mem_Ici.2 hp.1
      refine ContinuousOn.congr (f := fun p : ℝ × ℝ =>
        ((Real.exp (-((P p.2).exponent ω - (P p.1).exponent ω)) : ℝ) : ℂ)) ?_
        fun p hp => (hμ p.1 p.2 hp.1 hp.2).2.2 ω
      exact Complex.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn (h1.sub h2).neg)
    · -- (ND): equal exponents give equal pairs (`thm:cited-A9`)
      have heq : ∀ ω, (P s).exponent ω = (P t).exponent ω := by
        intro ω
        have h1 := (hμ s t hs hst.le).2.2 ω
        rw [h, charFun_dirac] at h1
        simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
        have h2 : Real.exp (-((P t).exponent ω - (P s).exponent ω)) = 1 := by
          exact_mod_cast h1.symm
        have := (Real.exp_eq_one_iff _).1 h2
        linarith
      obtain ⟨ha, hν⟩ := cited_A9 (P s) (P t) heq
      exact (hmono s t hs hst).2.2 (by rw [ha, hν])
  obtain ⟨C, hC⟩ := line_axioms_kernels_2_family μ hfam
  refine ⟨C, μ, hC, fun t ht ω => ?_⟩
  rw [(hμ 0 t le_rfl ht).2.2 ω, hexp0, sub_zero]

/-! ## (2) -/

/-- **`thm:lattice-line`(2), discrete covariance.** (A8 at `q^ℤ`) with `S_q t = qt` iff
`a(qt) = q² a(t)` and `ϖ_{qt} = T_q ϖ_t` for `t > 0`; then every kernel is semi-selfdecomposable
with span `q`, and the kernel at `q^n t` is the `T_{q^n}`-image of the kernel at `t`. -/
theorem lattice_line_2 (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ) (hμ : IsKernelFamily C.Φ μ)
    (P : ℝ → SymLevyPair) (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {q : ℝ}
    (hq : 1 < q) :
    ((∃ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (qPowers q) S ∧ IsCanonicalDiscreteGauge q S) ↔
        ∀ t : ℝ, 0 < t →
          (P (q * t)).a = q ^ 2 * (P t).a ∧ (P (q * t)).ν = (P t).ν.map (fun v => q * v)) ∧
      ((∃ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (qPowers q) S ∧ IsCanonicalDiscreteGauge q S) →
        (∀ t : ℝ, 0 ≤ t → IsSemiSelfDecomposableWithSpan q (μ 0 t)) ∧
          ∀ (n : ℤ) (t : ℝ), 0 ≤ t → (μ 0 t).map (fun x => q ^ n * x) = μ 0 (q ^ n * t)) := by
  have hq0 : 0 < q := by linarith
  have hdcl := discrete_covariance_line C μ hμ P hP hq
  refine ⟨hdcl.1.trans hdcl.2, fun ⟨S, hS, hcan⟩ => ⟨fun t ht =>
    (discrete_covariance_line_semi C μ hμ P hP hq S hS hcan t ht).1, ?_⟩⟩
  have hk : ∀ t : ℝ, 0 ≤ t → (μ 0 t).map (fun x => q * x) = μ 0 (q * t) := fun t ht =>
    (discrete_covariance_line_semi C μ hμ P hP hq S hS hcan t ht).2.1
  have hmeas : ∀ c : ℝ, Measurable fun x : ℝ => c * x := fun c => measurable_const_mul c
  -- the natural powers, by iteration
  have hnat : ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      (μ 0 t).map (fun x => q ^ n * x) = μ 0 (q ^ n * t) := by
    intro n
    induction n with
    | zero =>
      intro t _
      simp only [pow_zero, one_mul]
      exact Measure.map_id
    | succ n ih =>
      intro t ht
      have hcomp : (fun x : ℝ => q ^ (n + 1) * x) = (fun x => q * x) ∘ fun x => q ^ n * x :=
        funext fun x => by simp only [Function.comp_apply, pow_succ]; ring
      rw [hcomp, ← Measure.map_map (hmeas q) (hmeas _), ih t ht, hk _ (by positivity),
        pow_succ, mul_comm (q ^ n) q, mul_assoc]
  intro n t ht
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa only [zpow_natCast] using hnat m t ht
  · -- the negative powers, from the positive ones
    have hm0 : (q ^ m)⁻¹ * t ≥ 0 := by positivity
    have h1 := hnat m _ hm0
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0.ne'), one_mul] at h1
    rw [zpow_neg, zpow_natCast, ← h1, Measure.map_map (hmeas _) (hmeas _)]
    have hid : ((fun x : ℝ => (q ^ m)⁻¹ * x) ∘ fun x => q ^ m * x) = id :=
      funext fun x => by
        simp only [Function.comp_apply, id, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ hq0.ne'), one_mul]
    rw [hid, Measure.map_id]

/-! ## (3) -/

/-- **`thm:lattice-line`(3), "then".** For such `ψ` and `(α, k)`: `Ψ'_t(ω) = F(tω)` with `F` the
admissible exponent of `(α, k)`, and the relabelled family satisfies (A8) with `S'_λ t = λt`. -/
theorem lattice_line_3_then (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsKernelFamily C.Φ μ) (P : ℝ → SymLevyPair)
    (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) (ψ : ℝ → ℝ) (D : SDProfile)
    (hψ : IsGauge ψ)
    (hdata : ∀ t : ℝ, 0 < t →
      (P (ψ t)).a = D.a * t ^ 2 ∧ (P (ψ t)).ν = profileMeasure (fun v => D.k (v / t))) :
    (∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ, (P (ψ t)).exponent ω = D.exponent (t * ω)) ∧
      IsScaleCovariant (fun s t => C.Φ (ψ s) (ψ t)) (Ioi 0) (fun lam t => lam * t) := by
  have hfam := line_axioms_kernels_1_family C μ hμ
  have hψb := (isGauge_iff_isIncreasingBijection ψ).1 hψ
  have hψ0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ ψ t := fun t ht => hψb.mapsTo ht
  have hψmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ψ s ≤ ψ t := fun s t hs hst =>
    hψb.strictMonoOn.monotoneOn hs (mem_Ici.2 (hs.trans hst)) hst
  have hexp : ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ, (P (ψ t)).exponent ω = D.exponent (t * ω) := by
    intro t ht ω
    rcases ht.eq_or_lt with h0 | h0
    · subst h0
      rw [hψ.1, (foldedData_zero hfam.1 (hP 0 le_rfl)).1 ω, zero_mul, profile_exponent_zero]
    · obtain ⟨ha, hν⟩ := hdata t h0
      rw [← dilatePair_exponent D h0 ω]
      simp only [SymLevyPair.exponent, SymLevyPair.exponentL, ha, hν]
      rfl
  refine ⟨hexp, ?_⟩
  -- the relabelled kernels
  have hker : IsKernelFamily (fun s t => C.Φ (ψ s) (ψ t)) (fun s t => μ (ψ s) (ψ t)) :=
    ⟨fun s t hs hst => hμ.isProbability _ _ (hψ0 s hs) (hψmono s t hs hst),
      fun s t hs hst f => hμ.conv _ _ (hψ0 s hs) (hψmono s t hs hst) f⟩
  have hmulb : ∀ lam : ℝ, 0 < lam → IsIncreasingBijection (fun t => lam * t) := fun lam hlam =>
    ⟨fun t ht => mul_nonneg hlam.le ht, fun u _ v _ huv => mul_lt_mul_of_pos_left huv hlam,
      fun t ht => ⟨t / lam, div_nonneg ht hlam.le, mul_div_cancel₀ t hlam.ne'⟩⟩
  refine ⟨fun lam hlam _ => (hmulb lam hlam).mapsTo,
    fun lam hlam _ => (hmulb lam hlam).strictMonoOn, fun lam hlam _ => (hmulb lam hlam).surjOn,
    fun lam hlam _ => ?_⟩
  refine (line_axioms_kernels_3 _ _ hker hlam (fun t => lam * t) (hmulb lam hlam)).2 ?_
  intro s t hs hst
  have hls : 0 ≤ lam * s := mul_nonneg hlam.le hs
  have hlst : lam * s ≤ lam * t := mul_le_mul_of_nonneg_left hst hlam.le
  haveI := hμ.isProbability _ _ (hψ0 s hs) (hψmono s t hs hst)
  haveI := hμ.isProbability _ _ (hψ0 _ hls) (hψmono _ _ hls hlst)
  haveI : IsProbabilityMeasure ((μ (ψ s) (ψ t)).map fun x => lam * x) :=
    Measure.isProbabilityMeasure_map (measurable_const_mul lam).aemeasurable
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_map_mul, charFun_step_of_folded hfam.1 hP (hψ0 s hs) (hψmono s t hs hst),
    charFun_step_of_folded hfam.1 hP (hψ0 _ hls) (hψmono _ _ hls hlst),
    hexp t (hs.trans hst), hexp s hs, hexp _ (hls.trans hlst), hexp _ hls,
    show t * (lam * ω) = lam * t * ω by ring, show s * (lam * ω) = lam * s * ω by ring]

/-- **`thm:lattice-line`(3), full covariance, the equivalence.** (A8) holds iff for some gauge
`ψ = χ⁻¹` the relabelled kernels `μ_{0,ψ(t)}` have the folded data `a'(t) = αt²` and
`ϖ'_t(dv) = k(v/t) v⁻¹ dv` for all `t > 0`, `(α, k)` admissible data (an `SDProfile`). -/
theorem lattice_line_3 (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ) (hμ : IsKernelFamily C.Φ μ)
    (P : ℝ → SymLevyPair) (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) :
    (∃ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (Ioi 0) S) ↔
      ∃ (ψ : ℝ → ℝ) (D : SDProfile), IsGauge ψ ∧ ∀ t : ℝ, 0 < t →
        (P (ψ t)).a = D.a * t ^ 2 ∧ (P (ψ t)).ν = profileMeasure (fun v => D.k (v / t)) := by
  have hfam := line_axioms_kernels_1_family C μ hμ
  constructor
  · -- only if: `thm:cited-A4`, then `thm:cited-A9`
    rintro ⟨S, hS⟩
    have hbij : ∀ lam : ℝ, 0 < lam → IsIncreasingBijection (S lam) := fun lam hlam =>
      ⟨hS.S_mapsTo lam hlam hlam, hS.S_strictMonoOn lam hlam hlam, hS.S_surjOn lam hlam hlam⟩
    have hfull : ∀ lam : ℝ, 0 < lam → ∃ S' : ℝ → ℝ, IsCovariantAt μ lam S' := fun lam hlam =>
      ⟨S lam, (isCovariantAt_iff_map_mul μ lam (S lam)).2 ⟨hbij lam hlam,
        (line_axioms_kernels_3 C.Φ μ hμ hlam (S lam) (hbij lam hlam)).1
          (hS.scale lam hlam hlam)⟩⟩
    obtain ⟨χ, D, hχ, -, hF⟩ := exists_profile_of_fullCov hfam hfull
    obtain ⟨ψ, hψ, -, hχψ⟩ := isGauge_inverse hχ
    have hψb := (isGauge_iff_isIncreasingBijection ψ).1 hψ
    refine ⟨ψ, D, hψ, fun t ht => ?_⟩
    have hψt : 0 ≤ ψ t := hψb.mapsTo (mem_Ici.2 ht.le)
    have hexp : ∀ ω, (P (ψ t)).exponent ω = (dilatePair D ht).exponent ω := fun ω => by
      rw [dilatePair_exponent, ← lineExponent_eq_of_folded hfam hψt (hP _ hψt) ω, hF _ hψt ω,
        hχψ t ht.le]
    exact cited_A9 _ _ hexp
  · -- if: the relabelled operators are covariant with `λt`
    rintro ⟨ψ, D, hψ, hdata⟩
    have hthen := (lattice_line_3_then C μ hμ P hP ψ D hψ hdata).2
    obtain ⟨χ, hχ, hχψ, hψχ⟩ := isGauge_inverse hψ
    have hψb := (isGauge_iff_isIncreasingBijection ψ).1 hψ
    have hχb := (isGauge_iff_isIncreasingBijection χ).1 hχ
    have hχ0 : ∀ u : ℝ, 0 ≤ u → 0 ≤ χ u := fun u hu => hχb.mapsTo hu
    refine ⟨fun lam u => ψ (lam * χ u), ⟨?_, ?_, ?_, ?_⟩⟩
    · intro lam hlam _ u hu
      exact hψb.mapsTo (mem_Ici.2 (mul_nonneg hlam.le (hχ0 u hu)))
    · intro lam hlam _ u hu v hv huv
      exact hψb.strictMonoOn (mem_Ici.2 (mul_nonneg hlam.le (hχ0 u hu)))
        (mem_Ici.2 (mul_nonneg hlam.le (hχ0 v hv)))
        (mul_lt_mul_of_pos_left (hχb.strictMonoOn hu hv huv) hlam)
    · intro lam hlam _ v hv
      have hv' : 0 ≤ χ v / lam := div_nonneg (hχ0 v hv) hlam.le
      refine ⟨ψ (χ v / lam), hψb.mapsTo (mem_Ici.2 hv'), ?_⟩
      change ψ (lam * χ (ψ (χ v / lam))) = v
      rw [hχψ _ hv', mul_div_cancel₀ _ hlam.ne', hψχ v hv]
    · intro lam hlam hmem u v hu huv
      have hχuv : χ u ≤ χ v :=
        hχb.strictMonoOn.monotoneOn (mem_Ici.2 hu) (mem_Ici.2 (hu.trans huv)) huv
      have h := hthen.scale lam hlam hmem (χ u) (χ v) (hχ0 u hu) hχuv
      rwa [hψχ u hu, hψχ v (hu.trans huv)] at h

end Pyramids
