/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.PaperVI
import AffineHemigroup.MaternKernel
import AffineHemigroup.GaussMixture
import AffineHemigroup.MaternNegativeMass
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# The transform of a finite measure, and test functions

Helper facts that `Matern/MaternDensity.lean` and `Matern/MaternSobolev.lean` (`thm:matern-pyramid`,
the theory paper) read. They stood in files of the computation paper's chapter on the jet:
`MaternNotKernel.lean` (`mChar`, `continuous_mChar`, `integral_mChar_smul_mul`), `MaternRiesz.lean`
(`IsTestFn.toSchwartz`, `toSchwartz_apply`, `IsTestFn.fderiv_apply`, `fderiv_fderiv_apply`,
`IsWeakPartial.isWeakPartial2`) and `MaternHessian.lean` (`IsTestFn.differentiable`,
`continuous_fderiv_apply`, `hasCompactSupport_fderiv_apply`, `comp_add_right`), and `norm_ebasis`. Moved here verbatim
at the split (`adr/0007`; article-kit `PROCESS.md` § 5, a helper lemma goes in a file of the first
paper that needs it), names unchanged.
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set Filter Complex
open scoped Topology RealInnerProductSpace ENNReal NNReal FourierTransform SchwartzMap

variable {d : ℕ}

/-- **`μ̌(ξ) := ∫ e^{-2πi⟨y,ξ⟩} μ(dy)`**. -/
noncomputable def mChar (μ : Measure (Rd d)) (ξ : Rd d) : ℂ :=
  ∫ y, Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * I) ∂μ

theorem continuous_mChar (μ : Measure (Rd d)) [IsFiniteMeasure μ] : Continuous (mChar μ) := by
  refine continuous_of_dominated (bound := fun _ => 1) (fun ξ => ?_) (fun ξ => ?_)
    (integrable_const _) (Eventually.of_forall fun y => by fun_prop)
  · exact (by fun_prop : Continuous fun y : Rd d =>
      Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * I)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by rw [Complex.norm_exp_ofReal_mul_I]

/-- `∫ μ̌(λξ) Φ(ξ) dξ = ∫ (𝓕Φ)(λy) μ(dy)`, by Fubini. -/
theorem integral_mChar_smul_mul (μ : Measure (Rd d)) [IsFiniteMeasure μ] (Φ : 𝓢(Rd d, ℂ))
    (r : ℝ) : ∫ ξ, mChar μ (r • ξ) * Φ ξ = ∫ y, 𝓕 Φ (r • y) ∂μ := by
  have hF : Integrable (fun p : Rd d × Rd d =>
      Complex.exp (↑(-2 * Real.pi * ⟪p.2, r • p.1⟫) * I) * Φ p.1)
      ((volume : Measure (Rd d)).prod μ) := by
    refine (Φ.integrable.comp_fst μ).norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (by fun_prop : Continuous fun p : Rd d × Rd d =>
        Complex.exp (↑(-2 * Real.pi * ⟪p.2, r • p.1⟫) * I) * Φ p.1).aestronglyMeasurable
    · simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_rfl
  calc ∫ ξ, mChar μ (r • ξ) * Φ ξ
      = ∫ ξ, ∫ y, Complex.exp (↑(-2 * Real.pi * ⟪y, r • ξ⟫) * I) * Φ ξ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only [mChar]
        rw [integral_mul_const]
    _ = ∫ y, ∫ ξ, Complex.exp (↑(-2 * Real.pi * ⟪y, r • ξ⟫) * I) * Φ ξ ∂volume ∂μ :=
        integral_integral_swap (f := fun (ξ y : Rd d) =>
          Complex.exp (↑(-2 * Real.pi * ⟪y, r • ξ⟫) * I) * Φ ξ) hF
    _ = ∫ y, 𝓕 Φ (r • y) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        rw [SchwartzMap.fourier_coe, Real.fourier_eq']
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only [smul_eq_mul]
        rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm y ξ]

/-- A test function as a Schwartz function. -/
noncomputable def IsTestFn.toSchwartz {φ : Rd d → ℂ} (hφ : IsTestFn φ) : 𝓢(Rd d, ℂ) :=
  hφ.2.toSchwartzMap hφ.1

@[simp]
theorem IsTestFn.toSchwartz_apply {φ : Rd d → ℂ} (hφ : IsTestFn φ) (x : Rd d) :
    hφ.toSchwartz x = φ x := rfl

/-! ## Test functions (from `MaternHessian.lean` and `MaternRiesz.lean`) -/

theorem IsTestFn.differentiable {φ : Rd d → ℂ} (hφ : IsTestFn φ) : Differentiable ℝ φ :=
  hφ.1.differentiable (by simp)

theorem IsTestFn.continuous_fderiv_apply {φ : Rd d → ℂ} (hφ : IsTestFn φ) (v : Rd d) :
    Continuous fun x => fderiv ℝ φ x v :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem IsTestFn.hasCompactSupport_fderiv_apply {φ : Rd d → ℂ} (hφ : IsTestFn φ) (v : Rd d) :
    HasCompactSupport fun x => fderiv ℝ φ x v :=
  hφ.2.fderiv_apply (𝕜 := ℝ) v

/-- A translate of a test function is a test function. -/
theorem IsTestFn.comp_add_right {φ : Rd d → ℂ} (hφ : IsTestFn φ) (y : Rd d) :
    IsTestFn fun z => φ (z + y) :=
  ⟨hφ.1.comp (contDiff_id.add contDiff_const), hφ.2.comp_homeomorph (Homeomorph.addRight y)⟩

/-- `x ↦ ∂ⱼφ(x)` is a test function when `φ` is. -/
theorem IsTestFn.fderiv_apply {φ : Rd d → ℂ} (hφ : IsTestFn φ) (v : Rd d) :
    IsTestFn fun y => fderiv ℝ φ y v :=
  ⟨(contDiff_infty_iff_fderiv.1 hφ.1).2.clm_apply contDiff_const,
    hφ.hasCompactSupport_fderiv_apply v⟩

/-- `∂ᵢ(∂ⱼφ) = ∂ᵢ∂ⱼφ`, the second derivative read in the standard basis. -/
theorem IsTestFn.fderiv_fderiv_apply {φ : Rd d → ℂ} (hφ : IsTestFn φ) (i j : Fin d) (x : Rd d) :
    fderiv ℝ (fun y => fderiv ℝ φ y (ebasis j)) x (ebasis i) =
      iteratedFDeriv ℝ 2 φ x ![ebasis i, ebasis j] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((contDiff_infty_iff_fderiv.1 hφ.1).2.differentiable (by simp)) x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- **Two first weak derivatives give a second**: `∂ᵢu = w₁` and `∂ⱼw₁ = w` weakly give
`∂ᵢ∂ⱼu = w`. -/
theorem IsWeakPartial.isWeakPartial2 {u w₁ w : Rd d → ℂ} {i j : Fin d}
    (h1 : IsWeakPartial i u w₁) (h2 : IsWeakPartial j w₁ w) : IsWeakPartial2 i j u w := by
  intro φ hφ
  have h := h1 _ (hφ.fderiv_apply (ebasis j))
  simp only [hφ.fderiv_fderiv_apply] at h
  rw [h, h2 φ hφ, neg_neg]

/-- (From `MaternNotKernel.lean`, at the split.) -/
theorem norm_ebasis (k : Fin d) : ‖ebasis k‖ = 1 := by
  simp [ebasis]

end Pyramids
