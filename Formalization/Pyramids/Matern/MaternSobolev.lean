/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.BesselProfile
import Pyramids.Matern.MaternChar

/-!
# `W^{2,1}` and the octave step: the bound `‖(L_r - I)g‖₁ ≤ r² ∑ⱼ ‖∂ⱼ²g‖₁`

Blueprint: `blueprint/src/parts/04-matern.tex`, `thm:matern-pyramid`(4). Phase 5, wave 3b. The
facts about `W^{2,1}` that clause (4) reads, with no Fourier transform of a weak derivative.

* **Weak derivatives pass through a finite measure** (`IsWeakPartial.mconvE`,
  `IsWeakPartial2.mconvE`): Fubini moves `μ` onto the test function, `∫ (μ * g) ψ =
  ∫∫ g(z) ψ(z + y) dz μ(dy)` (`integral_mconvE_mul`), and a translate of a test function is a test
  function, with the translated derivatives.
* **Schwartz functions are in `W^{2,1}`** (`isW21_schwartz`): their derivatives are weak
  derivatives, by Mathlib's integration by parts for Schwartz functions, and are Schwartz again.
* **The bound** (`maternStep_sub_ae`, `eLpNorm_maternStep_sub_le`). For `g ∈ W^{2,1}` with weak
  second derivatives `vⱼ = ∂ⱼ²g`, `L_r * g - g = r² ∑ⱼ L_r * vⱼ` almost everywhere: tested against
  a real smooth compactly supported `φ`, the Green identity `lem:bessel-profile`(1)
  (`bessel_profile_1_green`) gives `∫ (L_r * g)(φ - r²Δφ) = ∫ gφ`, and the weak derivatives give
  `∫ (L_r * g) ∂ⱼ²φ = ∫ (L_r * vⱼ) φ`. So `‖(L_r - I)g‖₁ ≤ r² ∑ⱼ ‖vⱼ‖₁`. The printed proof reads the
  same identity on the transform; the Green identity makes the transform of a weak derivative
  unnecessary.

**What it reaches.** Lean core.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter Laplacian SchwartzMap
open ScaleSpace (mconvE)
open scoped Topology ENNReal SchwartzMap RealInnerProductSpace LineDeriv

variable {d : ℕ}

/-! ## Moving a finite measure onto the test function -/

/-- **`∫ (μ * g) ψ = ∫∫ g(z) ψ(z + y) dz μ(dy)`** for `g ∈ L¹`, `μ` finite and `ψ` bounded and
continuous. -/
theorem integral_mconvE_mul (μ : Measure (Rd d)) [IsFiniteMeasure μ] {g : Rd d → ℝ}
    (hg : Integrable g) {ψ : Rd d → ℂ} (hψ : Continuous ψ) {C : ℝ} (hC : ∀ x, ‖ψ x‖ ≤ C) :
    ∫ x, ((mconvE μ g x : ℝ) : ℂ) * ψ x = ∫ y, ∫ z, (g z : ℂ) * ψ (z + y) ∂volume ∂μ := by
  have h1 := ScaleSpace.integrable_uncurry_subE μ hg.1 hg
  have hI1 : Integrable (Function.uncurry fun x y : Rd d => (g (x - y) : ℂ) * ψ x)
      (volume.prod μ) :=
    h1.ofReal.mul_bdd (hψ.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => hC p.1)
  calc ∫ x, ((mconvE μ g x : ℝ) : ℂ) * ψ x
      = ∫ x, ∫ y, (g (x - y) : ℂ) * ψ x ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [ScaleSpace.mconvE_apply]
        rw [integral_mul_const, integral_complex_ofReal]
    _ = ∫ y, ∫ x, (g (x - y) : ℂ) * ψ x ∂volume ∂μ := integral_integral_swap hI1
    _ = ∫ y, ∫ z, (g z : ℂ) * ψ (z + y) ∂volume ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        have := integral_sub_right_eq_self (μ := (volume : Measure (Rd d)))
          (fun x => (g x : ℂ) * ψ (x + y)) y
        simp only [sub_add_cancel] at this
        exact this

/-- A test function is bounded. -/
theorem IsTestFn.exists_bound {φ : Rd d → ℂ} (hφ : IsTestFn φ) : ∃ C, ∀ x, ‖φ x‖ ≤ C :=
  hφ.differentiable.continuous.bounded_above_of_compact_support hφ.2

/-- `x ↦ ∂ᵢ∂ⱼφ(x)` is a test function when `φ` is. -/
theorem IsTestFn.iteratedFDeriv_two {φ : Rd d → ℂ} (hφ : IsTestFn φ) (i j : Fin d) :
    IsTestFn fun x => iteratedFDeriv ℝ 2 φ x ![ebasis i, ebasis j] := by
  have h := (hφ.fderiv_apply (ebasis j)).fderiv_apply (ebasis i)
  simpa only [hφ.fderiv_fderiv_apply] using h

/-- **A weak derivative passes through a finite measure**: `∂ₖg = v` weakly, with `g, v ∈ L¹`,
gives `∂ₖ(μ * g) = μ * v`. -/
theorem IsWeakPartial.mconv (μ : Measure (Rd d)) [IsFiniteMeasure μ] {g v : Rd d → ℝ}
    (hg : Integrable g) (hv : Integrable v) {k : Fin d}
    (h : IsWeakPartial k (fun x => (g x : ℂ)) (fun x => (v x : ℂ))) :
    IsWeakPartial k (fun x => (mconvE μ g x : ℂ)) (fun x => (mconvE μ v x : ℂ)) := by
  intro φ hφ
  obtain ⟨C, hC⟩ := hφ.exists_bound
  obtain ⟨C', hC'⟩ := (hφ.fderiv_apply (ebasis k)).exists_bound
  rw [integral_mconvE_mul μ hg (hφ.continuous_fderiv_apply (ebasis k)) hC',
    integral_mconvE_mul μ hv hφ.differentiable.continuous hC, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h' := h _ (hφ.comp_add_right y)
  simp only [fderiv_comp_add_right] at h'
  exact h'

/-- **A weak second derivative passes through a finite measure.** -/
theorem IsWeakPartial2.mconv (μ : Measure (Rd d)) [IsFiniteMeasure μ] {g v : Rd d → ℝ}
    (hg : Integrable g) (hv : Integrable v) {i j : Fin d}
    (h : IsWeakPartial2 i j (fun x => (g x : ℂ)) (fun x => (v x : ℂ))) :
    IsWeakPartial2 i j (fun x => (mconvE μ g x : ℂ)) (fun x => (mconvE μ v x : ℂ)) := by
  intro φ hφ
  obtain ⟨C, hC⟩ := hφ.exists_bound
  have h2 := hφ.iteratedFDeriv_two i j
  obtain ⟨C', hC'⟩ := h2.exists_bound
  rw [integral_mconvE_mul μ hg h2.differentiable.continuous hC',
    integral_mconvE_mul μ hv hφ.differentiable.continuous hC]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have h' := h _ (hφ.comp_add_right y)
  simp only [iteratedFDeriv_comp_add_right] at h'
  exact h'

/-- **`W^{2,1}` is preserved by a finite measure.** -/
theorem IsW21.mconv (μ : Measure (Rd d)) [IsFiniteMeasure μ] {g : Rd d → ℝ} (hg : IsW21 g) :
    IsW21 (mconvE μ g) := by
  obtain ⟨hgi, h1, h2⟩ := hg
  refine ⟨ScaleSpace.integrable_mconvE μ hgi.1 hgi, fun k => ?_, fun i j => ?_⟩
  · obtain ⟨v, hv, hw⟩ := h1 k
    exact ⟨mconvE μ v, ScaleSpace.integrable_mconvE μ hv.1 hv, hw.mconv μ hgi hv⟩
  · obtain ⟨v, hv, hw⟩ := h2 i j
    exact ⟨mconvE μ v, ScaleSpace.integrable_mconvE μ hv.1 hv, hw.mconv μ hgi hv⟩

/-! ## Schwartz functions are in `W^{2,1}` -/

/-- A real Schwartz function, read as a complex one. -/
noncomputable def schwartzC (f : 𝓢(Rd d, ℝ)) : 𝓢(Rd d, ℂ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM f

theorem schwartzC_apply (f : 𝓢(Rd d, ℝ)) (x : Rd d) : schwartzC f x = (f x : ℂ) := rfl

theorem lineDerivOp_schwartzC (f : 𝓢(Rd d, ℝ)) (m x : Rd d) :
    ∂_{m} (schwartzC f) x = ((∂_{m} f x : ℝ) : ℂ) := by
  rw [lineDerivOp_apply_eq_fderiv, lineDerivOp_apply_eq_fderiv]
  have h : HasFDerivAt (fun y => (f y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (f.differentiableAt.hasFDerivAt)
  change fderiv ℝ (fun y => (f y : ℂ)) x m = _
  rw [h.fderiv]
  rfl

/-- **The derivative of a Schwartz function is its weak derivative.** -/
theorem isWeakPartial_schwartz (f : 𝓢(Rd d, ℝ)) (k : Fin d) :
    IsWeakPartial k (fun x => (f x : ℂ)) (fun x => ((∂_{ebasis k} f) x : ℂ)) := by
  intro φ hφ
  let Φ : 𝓢(Rd d, ℂ) := hφ.2.toSchwartzMap hφ.1
  have h := integral_mul_lineDerivOp_right_eq_neg_left (μ := (volume : Measure (Rd d)))
    (schwartzC f) Φ (ebasis k)
  simp only [lineDerivOp_schwartzC] at h
  simp only [schwartzC_apply, lineDerivOp_apply_eq_fderiv] at h
  exact h

/-- **A real Schwartz function is in `W^{2,1}`.** -/
theorem isW21_schwartz (f : 𝓢(Rd d, ℝ)) : IsW21 (f : Rd d → ℝ) := by
  refine ⟨f.integrable, fun k => ⟨((∂_{ebasis k} f : 𝓢(Rd d, ℝ)) : Rd d → ℝ),
    (∂_{ebasis k} f : 𝓢(Rd d, ℝ)).integrable, isWeakPartial_schwartz f k⟩,
    fun i j => ⟨((∂_{ebasis j} (∂_{ebasis i} f : 𝓢(Rd d, ℝ)) : 𝓢(Rd d, ℝ)) : Rd d → ℝ),
    (∂_{ebasis j} (∂_{ebasis i} f : 𝓢(Rd d, ℝ)) : 𝓢(Rd d, ℝ)).integrable, ?_⟩⟩
  exact (isWeakPartial_schwartz f i).isWeakPartial2 (isWeakPartial_schwartz _ j)

/-! ## The bound for the octave step -/

/-- The Laplacian in the standard basis. -/
theorem laplacian_eq_sum_ebasis (φ : Rd d → ℝ) (x : Rd d) :
    Δ φ x = ∑ j, iteratedFDeriv ℝ 2 φ x ![ebasis j, ebasis j] := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [EuclideanSpace.basisFun_apply, ebasis]

/-- The second derivatives of `φ` read as a complex function. -/
theorem iteratedFDeriv_two_ofReal {φ : Rd d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x m₁ m₂ : Rd d) :
    iteratedFDeriv ℝ 2 (fun y => (φ y : ℂ)) x ![m₁, m₂] =
      ((iteratedFDeriv ℝ 2 φ x ![m₁, m₂] : ℝ) : ℂ) := by
  have h2 : ContDiffAt ℝ 2 φ x := (hφ.contDiffAt (x := x)).of_le (by
    exact WithTop.coe_le_coe.2 le_top)
  have h := Complex.ofRealCLM.iteratedFDeriv_comp_left h2 (i := 2) le_rfl
  change iteratedFDeriv ℝ 2 (Complex.ofRealCLM ∘ φ) x ![m₁, m₂] = _
  rw [h]
  rfl

/-- **`L_r * g - g = r² ∑ⱼ L_r * ∂ⱼ²g`** almost everywhere, for `g ∈ L¹` with weak second
derivatives `vⱼ = ∂ⱼ²g ∈ L¹`. -/
theorem maternStep_sub_ae (r : ℝ) {g : Rd d → ℝ} (hg : Integrable g) (v : Fin d → Rd d → ℝ)
    (hv : ∀ j, Integrable (v j))
    (hw : ∀ j, IsWeakPartial2 j j (fun x => (g x : ℂ)) (fun x => (v j x : ℂ))) :
    (fun x => mconvE (maternStep d r) g x - g x) =ᵐ[volume]
      fun x => r ^ 2 * ∑ j, mconvE (maternStep d r) (v j) x := by
  haveI := (charFun_maternStep (d := d) r 0).1
  have hLg := ScaleSpace.integrable_mconvE (maternStep d r) hg.1 hg
  have hLv : ∀ j, Integrable (mconvE (maternStep d r) (v j)) := fun j =>
    ScaleSpace.integrable_mconvE (maternStep d r) (hv j).1 (hv j)
  have hW : Integrable fun x =>
      mconvE (maternStep d r) g x - g x - r ^ 2 * ∑ j, mconvE (maternStep d r) (v j) x :=
    (hLg.sub hg).sub ((integrable_finsetSum _ fun j _ => hLv j).const_mul _)
  have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hW.locallyIntegrable
    fun φ hφ hφc => by
      have hφ' : ContDiff ℝ (⊤ : ℕ∞) φ := hφ
      have hT : IsTestFn fun x => (φ x : ℂ) :=
        ⟨Complex.ofRealCLM.contDiff.comp hφ', hφc.comp_left Complex.ofReal_zero⟩
      have hφcont : Continuous φ := hφ'.continuous
      obtain ⟨C, hC⟩ := hφcont.bounded_above_of_compact_support hφc
      -- the second derivatives of `φ`, bounded and continuous
      have hD : ∀ j, Continuous (fun x => iteratedFDeriv ℝ 2 φ x ![ebasis j, ebasis j]) ∧
          ∃ C', ∀ x, ‖iteratedFDeriv ℝ 2 φ x ![ebasis j, ebasis j]‖ ≤ C' := by
        intro j
        have h2 := hT.iteratedFDeriv_two j j
        obtain ⟨C', hC'⟩ := h2.exists_bound
        have hc := Complex.continuous_re.comp h2.differentiable.continuous
        simp only [Function.comp_def, iteratedFDeriv_two_ofReal hφ', Complex.ofReal_re] at hc
        refine ⟨hc, C', fun x => ?_⟩
        have := hC' x
        rwa [iteratedFDeriv_two_ofReal hφ', Complex.norm_real] at this
      -- the weak derivatives through `(maternStep d r)`, read on real functions
      have hj : ∀ j,
          ∫ x, mconvE (maternStep d r) g x * iteratedFDeriv ℝ 2 φ x ![ebasis j, ebasis j] =
          ∫ x, mconvE (maternStep d r) (v j) x * φ x := by
        intro j
        have h := (hw j).mconv (maternStep d r) hg (hv j) _ hT
        simp only [iteratedFDeriv_two_ofReal hφ'] at h
        have h' : ((∫ x, mconvE (maternStep d r) g x *
            iteratedFDeriv ℝ 2 φ x ![ebasis j, ebasis j] : ℝ) : ℂ) =
            ((∫ x, mconvE (maternStep d r) (v j) x * φ x : ℝ) : ℂ) := by
          rw [← integral_complex_ofReal, ← integral_complex_ofReal]
          push_cast
          exact h
        exact_mod_cast h'
      have hiD : ∀ j, Integrable fun x => mconvE (maternStep d r) g x *
          iteratedFDeriv ℝ 2 φ x ![ebasis j, ebasis j] := fun j =>
        hLg.mul_bdd (hD j).1.aestronglyMeasurable
          (Eventually.of_forall fun x => (hD j).2.choose_spec x)
      have hiLv : ∀ j, Integrable fun x => mconvE (maternStep d r) (v j) x * φ x := fun j =>
        (hLv j).mul_bdd hφcont.aestronglyMeasurable (Eventually.of_forall hC)
      have hΔ : ∫ x, mconvE (maternStep d r) g x * Δ φ x =
          ∑ j, ∫ x, mconvE (maternStep d r) (v j) x * φ x := by
        simp_rw [laplacian_eq_sum_ebasis φ, Finset.mul_sum]
        rw [integral_finsetSum _ fun j _ => hiD j]
        exact Finset.sum_congr rfl fun j _ => hj j
      have hgreen := bessel_profile_1_green (d := d) (r := r) g hg φ hφ' hφc
      have hiLg : Integrable fun x => mconvE (maternStep d r) g x * φ x :=
        hLg.mul_bdd hφcont.aestronglyMeasurable (Eventually.of_forall hC)
      have hiLΔ : Integrable fun x => mconvE (maternStep d r) g x * Δ φ x := by
        simp_rw [laplacian_eq_sum_ebasis φ, Finset.mul_sum]
        exact integrable_finsetSum _ fun j _ => hiD j
      have hig : Integrable fun x => g x * φ x :=
        hg.mul_bdd hφcont.aestronglyMeasurable (Eventually.of_forall hC)
      have hsplit : ∫ x, mconvE (maternStep d r) g x * (φ x - r ^ 2 * Δ φ x) =
          (∫ x, mconvE (maternStep d r) g x * φ x) -
            r ^ 2 * ∫ x, mconvE (maternStep d r) g x * Δ φ x := by
        have h := integral_sub hiLg (hiLΔ.const_mul (r ^ 2))
        rw [integral_const_mul] at h
        refine Eq.trans ?_ h
        congr 1
        funext x
        ring
      have hfun : (fun x => φ x •
          (mconvE (maternStep d r) g x - g x - r ^ 2 * ∑ j, mconvE (maternStep d r) (v j) x)) =
          fun x => (mconvE (maternStep d r) g x * φ x - g x * φ x) -
            r ^ 2 * ∑ j, mconvE (maternStep d r) (v j) x * φ x := by
        funext x
        rw [smul_eq_mul, ← Finset.sum_mul]
        ring
      have hA : Integrable fun x => mconvE (maternStep d r) g x * φ x - g x * φ x := hiLg.sub hig
      have hB : Integrable fun x => r ^ 2 * ∑ j, mconvE (maternStep d r) (v j) x * φ x :=
        (integrable_finsetSum _ fun j _ => hiLv j).const_mul _
      have e1 := integral_sub hA hB
      have e2 := integral_sub hiLg hig
      have e3 := integral_const_mul (μ := (volume : Measure (Rd d))) (r ^ 2)
        (fun x => ∑ j, mconvE (maternStep d r) (v j) x * φ x)
      have e4 := integral_finsetSum (μ := (volume : Measure (Rd d))) Finset.univ
        (fun j _ => hiLv j)
      rw [hfun]
      rw [hΔ] at hsplit
      rw [e4] at e3
      linarith [hsplit, hgreen, e1, e2, e3]
  filter_upwards [h0] with x hx
  linarith

/-- **`‖(L_r - I)g‖₁ ≤ r² K`** for `g ∈ W^{2,1}`, with `K = ∑ⱼ ‖∂ⱼ²g‖₁ < ∞` independent of `r`. -/
theorem eLpNorm_maternStep_sub_le {g : Rd d → ℝ} (hg : IsW21 g) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ r : ℝ,
      eLpNorm (fun x => mconvE (maternStep d r) g x - g x) 1 volume ≤
        ENNReal.ofReal (r ^ 2) * K := by
  choose v hv hw using fun j => hg.2.2 j j
  refine ⟨∑ j, eLpNorm (v j) 1 volume,
    ENNReal.sum_lt_top.2 fun j _ => (memLp_one_iff_integrable.2 (hv j)).2, fun r => ?_⟩
  haveI := (charFun_maternStep (d := d) r 0).1
  rw [eLpNorm_congr_ae (maternStep_sub_ae r hg.1 v hv hw)]
  have hfun : (fun x => r ^ 2 * ∑ j, mconvE (maternStep d r) (v j) x) =
      r ^ 2 • ∑ j, mconvE (maternStep d r) (v j) := by
    funext x
    simp [Finset.sum_apply]
  rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal (sq_nonneg r)]
  gcongr
  refine (eLpNorm_sum_le (fun j _ => ?_) le_rfl).trans (Finset.sum_le_sum fun j _ => ?_)
  · exact (ScaleSpace.integrable_mconvE _ (hv j).1 (hv j)).1
  · rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
    refine (ScaleSpace.lintegral_enorm_mconv_leE _ (hv j).1).trans ?_
    rw [measure_univ, one_mul]

end Pyramids
