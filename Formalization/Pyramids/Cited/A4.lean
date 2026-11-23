/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.MainConstruction
import ScaleSpaceCore.MainAnalysis
import Pyramids.LineAppendix.LineExponentData

/-!
# Ledger A4: the classification on the line (V-line Thm. 7.3, p. 37)

Interface node `thm:cited-A4` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A4 of
`blueprint/AXIOMS.md`, cited from the line paper (V-line v0.1), Theorem 7.3, printed p. 37.

A4 is not admitted, and **needs no axiom of its own**: its three clauses are proved here from
A39, which the author admitted on 2026-11-13. Wave 3d, 2026-11-14: the three declarations moved here
from `PyramidsSkeleton.Ch02CitedFacts`, unchanged in statement and name.

* **Analysis ("only if").** The shared core's `main_analysis_exists`, whose one hypothesis
  `SymLevyUnique` is the affine module's `line_levy_unique` (A39(ii)–(iii), this article's
  `cited_A9`).
* **Uniqueness.** The shared core's `main_uniqueness` (Lean core), after the kernels of one
  operator family are identified (`mconvL1_injective`).
* **Construction, and "if".** The shared core's `main_construction` takes `LineLawInterfaces`,
  which bundles Bochner's theorem, not admitted here. It spends that hypothesis at one step only,
  the passage from a symmetric Lévy exponent to a law with that exponent. This article has that
  step from A39(iii) (`line_exponent_data_1`), so the construction is replayed with it: the
  kernel lemmas of `ScaleSpace.ConstructionData` are restated for any kernels with the transforms
  of the gauge and the profile (`IsGaugeKernels`), and the gauge lemmas and
  `expo_isSymLevyExponent` of the core, which take no interface, are used as they stand. For the
  "if", the given kernels are such kernels, and the family is built on the given operators.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X CascadeFamily CascadeCore PreCascadeCore CascadeData ConstructionData
  IsKernelFamily IsScaleCovariant IsPositive IsNondegenerate SDProfile IsSymmetric fourierCos
  mconvL1 IsSymLevyExponent)
open scoped ENNReal

/-! ## Kernels with the transforms of a gauge and a profile -/

/-- **Kernels with the transforms of `(χ, F)`**: probability measures, symmetric, with
`κ̂_{s,t}(ω) = exp(-(F(χ(t)ω) - F(χ(s)ω)))` for `0 ≤ s ≤ t`. -/
structure IsGaugeKernels (D : ConstructionData) (κ : ℝ → ℝ → Measure ℝ) : Prop where
  prob : ∀ s t, IsProbabilityMeasure (κ s t)
  sym : ∀ s t, IsSymmetric (κ s t)
  charFun_eq : ∀ s t, 0 ≤ s → s ≤ t → ∀ ω : ℝ,
    charFun (κ s t) ω = ((Real.exp (-(D.expo s t ω)) : ℝ) : ℂ)

/-- A law whose transform is `e^{-ψ}`, `ψ ∈ ND_s`, is symmetric. -/
theorem isSymmetric_of_charFun {m : Measure ℝ} [IsProbabilityMeasure m] {ψ : ℝ → ℝ}
    (hψ : IsSymLevyExponent ψ) (h : ∀ ω : ℝ, charFun m ω = ((Real.exp (-ψ ω) : ℝ) : ℂ)) :
    IsSymmetric m := by
  obtain ⟨ν, ⟨hp, hs, -, hc⟩, -⟩ := line_exponent_data_1 ψ hψ
  haveI := hp
  have e : m = ν := Measure.ext_of_charFun (funext fun ω => by rw [h, hc])
  rw [e]
  exact hs

namespace IsGaugeKernels

variable {D : ConstructionData} {κ : ℝ → ℝ → Measure ℝ} (h : IsGaugeKernels D κ)
include h

theorem fourierCos_eq {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ω : ℝ) :
    fourierCos (κ s t) ω = Real.exp (-(D.expo s t ω)) := by
  haveI := h.prob s t
  rw [ScaleSpace.fourierCos_eq_charFun_re, h.charFun_eq s t hs hst ω, Complex.ofReal_re]

/-- **(A6), the diagonal.** -/
theorem self {t : ℝ} (ht : 0 ≤ t) : κ t t = Measure.dirac 0 := by
  haveI := h.prob t t
  refine Measure.ext_of_charFun ?_
  funext ω
  rw [h.charFun_eq t t ht le_rfl, charFun_dirac, D.expo_self]
  simp

/-- **(A6), the cascade law.** -/
theorem conv {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) :
    (κ r s) ∗ (κ s t) = κ r t := by
  haveI := h.prob r s
  haveI := h.prob s t
  haveI := h.prob r t
  haveI : IsFiniteMeasure ((κ r s) ∗ (κ s t)) := by rw [Measure.conv]; infer_instance
  refine Measure.ext_of_charFun ?_
  funext ω
  rw [charFun_conv, h.charFun_eq r s hr hrs, h.charFun_eq s t (hr.trans hrs) hst,
    h.charFun_eq r t hr (hrs.trans hst), ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  rw [← D.expo_add (r := r) (s := s) (t := t) ω]
  ring

/-- **(A7)'s hypothesis.** -/
theorem cos_continuousOn (ω : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => fourierCos (κ p.1 p.2) ω)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
  have hFcont : Continuous D.P.exponent := D.P.continuous_exponent
  have h1 : ContinuousOn (fun p : ℝ × ℝ => D.χ p.1) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
    D.chi_continuousOn.comp continuousOn_fst fun _ hp => hp.1
  have h2 : ContinuousOn (fun p : ℝ × ℝ => D.χ p.2) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
    D.chi_continuousOn.comp continuousOn_snd fun _ hp => hp.1.trans hp.2
  have hg : ContinuousOn
      (fun p : ℝ × ℝ => Real.exp (-(D.P.exponent (D.χ p.2 * ω) - D.P.exponent (D.χ p.1 * ω))))
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
    refine Real.continuous_exp.comp_continuousOn (ContinuousOn.neg (ContinuousOn.sub ?_ ?_))
    · exact hFcont.comp_continuousOn (h2.mul continuousOn_const)
    · exact hFcont.comp_continuousOn (h1.mul continuousOn_const)
  refine hg.congr fun p hp => ?_
  rw [h.fourierCos_eq hp.1 hp.2]
  rfl

/-- **(ND) at the kernel.** -/
theorem ne_dirac (hne : ∃ ω : ℝ, D.P.exponent ω ≠ 0) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    κ s t ≠ Measure.dirac 0 := by
  intro hdir
  obtain ⟨ω₀, hω₀⟩ := hne
  have hFcont : Continuous D.P.exponent := D.P.continuous_exponent
  have ht : 0 < D.χ t := D.chi_pos (lt_of_le_of_lt hs hst)
  have hzero : ∀ ω : ℝ, D.P.exponent (D.χ t * ω) = D.P.exponent (D.χ s * ω) := by
    intro ω
    have h1 : fourierCos (κ s t) ω = 1 := by rw [hdir]; simp
    rw [h.fourierCos_eq hs hst.le] at h1
    have h2 : -(D.expo s t ω) = 0 := by
      have h3 := congrArg Real.log h1
      rwa [Real.log_exp, Real.log_one] at h3
    have : D.expo s t ω = 0 := by linarith
    simpa [ConstructionData.expo, sub_eq_zero] using this
  rcases eq_or_lt_of_le hs with h0 | hspos
  · apply hω₀
    have := hzero (ω₀ / D.χ t)
    rwa [← h0, D.chi_zero, zero_mul, D.P.exponent_zero, mul_div_cancel₀ _ ht.ne'] at this
  · have hcs : 0 < D.χ s := D.chi_pos hspos
    set c : ℝ := D.χ s / D.χ t with hc
    have hcpos : 0 < c := div_pos hcs ht
    have hcne : c ≠ 1 := by
      have : D.χ s < D.χ t := D.chi_mono hs (hs.trans hst.le) hst
      intro hce
      rw [hc, div_eq_one_iff_eq ht.ne'] at hce
      exact absurd hce this.ne
    have hinv : ∀ ω : ℝ, D.P.exponent ω = D.P.exponent (c * ω) := by
      intro ω
      have := hzero (ω / D.χ t)
      rw [mul_div_cancel₀ _ ht.ne'] at this
      rw [this, hc]
      congr 1
      field_simp
    exact hω₀ (ScaleSpace.dilation_invariance D.P.exponent hFcont.continuousAt D.P.exponent_zero c
      hcpos hcne hinv ω₀)

/-- **(A8) at the kernel**, with the gauge action `S_λ t = χ⁻¹(λχ(t))`. -/
theorem map_const_mul {lam s t : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s) (hst : s ≤ t) :
    (κ s t).map (fun x => lam * x) = κ (D.gaugeAction lam s) (D.gaugeAction lam t) := by
  have hSs : 0 ≤ D.gaugeAction lam s := D.gaugeAction_nonneg hlam hs
  have hSst : D.gaugeAction lam s ≤ D.gaugeAction lam t := by
    rcases eq_or_lt_of_le hst with h' | h'
    · rw [h']
    · exact le_of_lt (D.gaugeAction_strictMonoOn hlam hs (hs.trans hst) h')
  haveI := h.prob s t
  haveI := h.prob (D.gaugeAction lam s) (D.gaugeAction lam t)
  haveI : IsProbabilityMeasure ((κ s t).map fun x => lam * x) :=
    Measure.isProbabilityMeasure_map (measurable_const_mul lam).aemeasurable
  refine Measure.ext_of_charFun ?_
  funext ω
  rw [ScaleSpace.charFun_map_const_mul, h.charFun_eq s t hs hst, h.charFun_eq _ _ hSs hSst]
  congr 2
  simp only [ConstructionData.expo, D.chi_gaugeAction hlam hs,
    D.chi_gaugeAction hlam (hs.trans hst)]
  ring_nf

/-- The kernels as a `CascadeData`. -/
noncomputable def cascadeData : CascadeData where
  κ := κ
  prob := h.prob
  sym := h.sym
  self _ ht := h.self ht
  conv _ _ _ hr hrs hst := h.conv hr hrs hst
  cos_continuousOn := h.cos_continuousOn

theorem cascadeData_κ : h.cascadeData.κ = κ := rfl

end IsGaugeKernels

/-- Kernels with the transforms of `(χ, F)` exist, from A39(iii) (`line_exponent_data_1`). -/
theorem exists_isGaugeKernels (D : ConstructionData) : ∃ κ : ℝ → ℝ → Measure ℝ,
    IsGaugeKernels D κ := by
  classical
  have hex : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∃ m : Measure ℝ, IsProbabilityMeasure m ∧
      IsSymmetric m ∧ ∀ ω : ℝ, charFun m ω = ((Real.exp (-(D.expo s t ω)) : ℝ) : ℂ) := by
    intro s t hs hst
    obtain ⟨m, ⟨hp, hsym, -, hc⟩, -⟩ := line_exponent_data_1 _ (D.expo_isSymLevyExponent hs hst)
    exact ⟨m, hp, hsym, hc⟩
  let κ : ℝ → ℝ → Measure ℝ := fun s t =>
    if h : 0 ≤ s ∧ s ≤ t then (hex s t h.1 h.2).choose else Measure.dirac 0
  refine ⟨κ, ⟨fun s t => ?_, fun s t => ?_, fun s t hs hst ω => ?_⟩⟩
  · simp only [κ]
    split_ifs with h
    · exact (hex s t h.1 h.2).choose_spec.1
    · infer_instance
  · simp only [κ]
    split_ifs with h
    · exact (hex s t h.1 h.2).choose_spec.2.1
    · rw [IsSymmetric, Measure.map_dirac' measurable_neg, neg_zero]
  · simp only [κ, dif_pos (show 0 ≤ s ∧ s ≤ t from ⟨hs, hst⟩)]
    exact (hex s t hs hst).choose_spec.2.2 ω

/-- The construction data of a gauge and a profile. -/
def constructionDataOf (χ : ℝ → ℝ) (P : SDProfile) (hχ : IsGauge χ) : ConstructionData :=
  ⟨P, χ, hχ.1, hχ.2.1, hχ.2.2⟩

/-- A cascade family on given kernels with the transforms of `(χ, F)`, `F ≢ 0`. -/
noncomputable def IsGaugeKernels.cascadeFamily {D : ConstructionData} {κ : ℝ → ℝ → Measure ℝ}
    (h : IsGaugeKernels D κ) (hne : ∃ ω : ℝ, D.P.exponent ω ≠ 0) : CascadeFamily where
  toCascadeCore := h.cascadeData.cascadeCore fun _ _ hs hst => h.ne_dirac hne hs hst
  S := D.gaugeAction
  covariant := h.cascadeData.isScaleCovariant D.gaugeAction
    (fun _ hlam _ ht => D.gaugeAction_nonneg hlam ht)
    (fun _ hlam => D.gaugeAction_strictMonoOn hlam)
    (fun _ hlam => D.gaugeAction_surjOn hlam)
    (fun _ hlam _ _ hs hst => h.map_const_mul hlam hs hst)

/-! ## The node -/

/-- Two elements of `L¹` with a.e. equal representatives are equal; so an operator represented by
the kernel `m` is convolution by `m`. -/
theorem eq_mconvL1_of_kernel {Φ : ℝ → ℝ → (X →L[ℝ] X)} {μ : ℝ → ℝ → Measure ℝ}
    (hker : IsKernelFamily Φ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    haveI := hker.isProbability s t hs hst
    Φ s t = mconvL1 (μ s t) := by
  haveI := hker.isProbability s t hs hst
  refine ContinuousLinearMap.ext fun f => ?_
  refine Lp.ext ?_
  exact (hker.conv s t hs hst f).trans (ScaleSpace.coeFn_mconvL1 (μ s t) f).symm

/-- **`thm:cited-A4`, the uniqueness of the normalized pair.** A theorem: the kernels of one
operator family agree (`mconvL1_injective`), and the shared core's `main_uniqueness` (Lean core)
compares the two representations. -/
theorem cited_A4_unique (Φ : ℝ → ℝ → (X →L[ℝ] X)) (χ₁ χ₂ : ℝ → ℝ) (P₁ P₂ : SDProfile)
    (μ₁ μ₂ : ℝ → ℝ → Measure ℝ) (hχ₁ : IsGauge χ₁) (hχ₂ : IsGauge χ₂) (h1₁ : χ₁ 1 = 1)
    (h1₂ : χ₂ 1 = 1) (hne : ∃ ω : ℝ, P₁.exponent ω ≠ 0)
    (hker₁ : IsKernelFamily Φ μ₁) (hker₂ : IsKernelFamily Φ μ₂)
    (hrep₁ : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      charFun (μ₁ s t) ω =
        ((Real.exp (-(P₁.exponent (χ₁ t * ω) - P₁.exponent (χ₁ s * ω))) : ℝ) : ℂ))
    (hrep₂ : ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
      charFun (μ₂ s t) ω =
        ((Real.exp (-(P₂.exponent (χ₂ t * ω) - P₂.exponent (χ₂ s * ω))) : ℝ) : ℂ)) :
    (∀ t : ℝ, 0 ≤ t → χ₁ t = χ₂ t) ∧ ∀ ω : ℝ, P₁.exponent ω = P₂.exponent ω := by
  have heq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ₁ s t = μ₂ s t := by
    intro s t hs hst
    haveI := hker₁.isProbability s t hs hst
    haveI := hker₂.isProbability s t hs hst
    refine ScaleSpace.mconvL1_injective ?_
    rw [← eq_mconvL1_of_kernel hker₁ hs hst, ← eq_mconvL1_of_kernel hker₂ hs hst]
  refine ScaleSpace.main_uniqueness μ₁ χ₁ χ₂ P₁ P₂ h1₁ h1₂ hχ₁.1 hχ₂.1 hχ₁.2.1 hχ₂.2.1 hne
    (fun s t ω hs hst => ?_) (fun s t ω hs hst => ?_)
  · haveI := hker₁.isProbability s t hs hst
    rw [ScaleSpace.fourierCos_eq_charFun_re, hrep₁ s t ω hs hst, Complex.ofReal_re]
  · haveI := hker₁.isProbability s t hs hst
    rw [heq s t hs hst]
    haveI := hker₂.isProbability s t hs hst
    rw [ScaleSpace.fourierCos_eq_charFun_re, hrep₂ s t ω hs hst, Complex.ofReal_re]

/-- **`thm:cited-A4`, the construction.** For every gauge `χ` and every admissible `F ≢ 0` there
are probability measures `μ_{s,t}` with `μ̂_{s,t}(ω) = exp(-[F(χ(t)ω) - F(χ(s)ω)])`, and the
operators `f ↦ μ_{s,t} * f` form a family with (A1)–(A8) and (ND). A theorem from A39(iii), through
`line_exponent_data_1`. -/
theorem cited_A4_exists (χ : ℝ → ℝ) (P : SDProfile) (hχ : IsGauge χ)
    (hne : ∃ ω : ℝ, P.exponent ω ≠ 0) :
    ∃ (Fam : CascadeFamily) (μ : ℝ → ℝ → Measure ℝ), IsKernelFamily Fam.Φ μ ∧
      ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
        charFun (μ s t) ω =
          ((Real.exp (-(P.exponent (χ t * ω) - P.exponent (χ s * ω))) : ℝ) : ℂ) := by
  set D := constructionDataOf χ P hχ
  obtain ⟨κ, hκ⟩ := exists_isGaugeKernels D
  exact ⟨hκ.cascadeFamily hne, κ, hκ.cascadeData.isKernelFamily,
    fun s t ω hs hst => hκ.charFun_eq s t hs hst ω⟩

/-- **`thm:cited-A4`, the equivalence.** `Φ` satisfies (A1)–(A8) and (ND) iff there are a gauge
`χ`, an admissible `F ≢ 0` and kernels `μ_{s,t}` with `Φ_{s,t} f = μ_{s,t} * f` and
`μ̂_{s,t}(ω) = exp(-[F(χ(t)ω) - F(χ(s)ω)])`. A theorem: the "only if" is the shared core's
`main_analysis_exists` on `line_levy_unique` (A39(ii)–(iii)); the "if" builds the family on the
given operators from the given kernels, which have the transforms of `(χ, F)`. -/
theorem cited_A4 (Φ : ℝ → ℝ → (X →L[ℝ] X)) :
    (∃ Fam : CascadeFamily, Fam.Φ = Φ) ↔
      ∃ (χ : ℝ → ℝ) (P : SDProfile) (μ : ℝ → ℝ → Measure ℝ),
        IsGauge χ ∧ (∃ ω : ℝ, P.exponent ω ≠ 0) ∧ IsKernelFamily Φ μ ∧
          ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
            charFun (μ s t) ω =
              ((Real.exp (-(P.exponent (χ t * ω) - P.exponent (χ s * ω))) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨Fam, rfl⟩
    obtain ⟨μ, χ, P, hker, h0, hmono, hsurj, -, hne, hsym, hcos⟩ :=
      ScaleSpace.main_analysis_exists line_levy_unique Fam.toCascadeCore Fam.S Fam.covariant
    refine ⟨χ, P, μ, ⟨h0, hmono, hsurj⟩, hne, hker, fun s t ω hs hst => ?_⟩
    haveI := hker.isProbability s t hs hst
    rw [ScaleSpace.charFun_eq_fourierCos_of_symmetric (hsym s t hs hst), hcos s t ω hs hst]
  · rintro ⟨χ, P, μ, hχ, hne, hker, hchar⟩
    classical
    set D := constructionDataOf χ P hχ
    -- the given kernels, totalised by `δ₀`, have the transforms of `(χ, F)`
    let κ : ℝ → ℝ → Measure ℝ := fun s t => if 0 ≤ s ∧ s ≤ t then μ s t else Measure.dirac 0
    have hκμ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → κ s t = μ s t := fun s t hs hst => by
      simp only [κ, if_pos (And.intro hs hst)]
    have hprob : ∀ s t, IsProbabilityMeasure (κ s t) := fun s t => by
      by_cases hst : 0 ≤ s ∧ s ≤ t
      · rw [hκμ s t hst.1 hst.2]
        exact hker.isProbability s t hst.1 hst.2
      · simp only [κ, if_neg hst]
        infer_instance
    have hcf : ∀ s t, 0 ≤ s → s ≤ t → ∀ ω : ℝ,
        charFun (κ s t) ω = ((Real.exp (-(D.expo s t ω)) : ℝ) : ℂ) := fun s t hs hst ω => by
      rw [hκμ s t hs hst, hchar s t ω hs hst]
      rfl
    have hκ : IsGaugeKernels D κ := by
      refine ⟨hprob, fun s t => ?_, hcf⟩
      by_cases hst : 0 ≤ s ∧ s ≤ t
      · haveI := hprob s t
        exact isSymmetric_of_charFun (D.expo_isSymLevyExponent hst.1 hst.2) (hcf s t hst.1 hst.2)
      · simp only [κ, if_neg hst]
        rw [IsSymmetric, Measure.map_dirac' measurable_neg, neg_zero]
    -- on the index set the given operators are the family's
    set Fam₀ := hκ.cascadeFamily hne
    have hΦ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → Φ s t = Fam₀.Φ s t := fun s t hs hst => by
      haveI := hprob s t
      have hk : IsKernelFamily Φ κ :=
        ⟨fun s t _ _ => hprob s t, fun s t hs hst f => by
          rw [hκμ s t hs hst]
          exact hker.conv s t hs hst f⟩
      rw [eq_mconvL1_of_kernel hk hs hst]
      rfl
    have hS : ∀ lam : ℝ, 0 < lam → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        0 ≤ Fam₀.S lam s ∧ Fam₀.S lam s ≤ Fam₀.S lam t := fun lam hlam s t hs hst => by
      refine ⟨D.gaugeAction_nonneg hlam hs, ?_⟩
      rcases eq_or_lt_of_le hst with h' | h'
      · rw [h']
      · exact le_of_lt (D.gaugeAction_strictMonoOn hlam hs (hs.trans hst) h')
    let pre : PreCascadeCore :=
      { Φ := Φ
        translation := fun s t hs hst a f => by
          rw [hΦ s t hs hst]
          exact Fam₀.translation s t hs hst a f
        reflection := fun s t hs hst f => by
          rw [hΦ s t hs hst]
          exact Fam₀.reflection s t hs hst f
        unit_mass := fun s t hs hst f hf => by
          rw [hΦ s t hs hst]
          exact Fam₀.unit_mass s t hs hst f hf
        diag := fun t ht => by
          rw [hΦ t t ht le_rfl]
          exact Fam₀.diag t ht
        cascade := fun r s t hr hrs hst => by
          rw [hΦ s t (hr.trans hrs) hst, hΦ r s hr hrs, hΦ r t hr (hrs.trans hst)]
          exact Fam₀.cascade r s t hr hrs hst
        continuous := fun f => (Fam₀.continuous f).congr fun p hp => by
          simp only
          rw [hΦ p.1 p.2 hp.1 hp.2] }
    refine ⟨{ toPreCascadeCore := pre
              positive := fun s t hs hst f hf => by
                change ScaleSpace.IsNonneg (Φ s t f)
                rw [hΦ s t hs hst]
                exact Fam₀.positive s t hs hst f hf
              nondegenerate := fun s t hs hst => by
                change Φ s t ≠ _
                rw [hΦ s t hs hst.le]
                exact Fam₀.nondegenerate s t hs hst
              S := Fam₀.S
              covariant :=
                { S_mapsTo := Fam₀.covariant.S_mapsTo
                  S_strictMonoOn := Fam₀.covariant.S_strictMonoOn
                  S_surjOn := Fam₀.covariant.S_surjOn
                  scale := fun lam hlam hG s t hs hst => by
                    change (ScaleSpace.dilL1 hlam).comp (Φ s t) =
                      (Φ (Fam₀.S lam s) (Fam₀.S lam t)).comp (ScaleSpace.dilL1 hlam)
                    rw [hΦ s t hs hst, hΦ _ _ (hS lam hlam s t hs hst).1
                      (hS lam hlam s t hs hst).2]
                    exact Fam₀.covariant.scale lam hlam hG s t hs hst } }, rfl⟩

end Pyramids
