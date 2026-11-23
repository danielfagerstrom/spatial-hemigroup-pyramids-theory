/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.MaternPyramid
import Pyramids.LineAppendix.MaternNonCreation
import Pyramids.LineAppendix.LadderNonCreation
import AffineHemigroup.RadialMarginal

/-!
# `thm:matern-pyramid`(3): the projections

Blueprint: `blueprint/src/parts/04-matern.tex`, `thm:matern-pyramid`. Phase 5, wave 3b. The three
declarations of clause (3) moved here from `PyramidsSkeleton.Ch04Matern` with their conclusions
unchanged. Binders their proofs do not read are dropped (2026-11-15, a strengthening):
`matern_pyramid_3_marginal` takes no `1 ≤ d`, `1 < q`, `0 < c` (a unit vector already gives
`d ≥ 1`); `_3_polya` and `_3_counts` take no `1 ≤ d`.

* **The marginal family** has the transforms `r ↦ μ̂_{s,t}(re)` (`charFun_marginal`), and
  `‖re‖ = |r|`: it is the Matérn pyramid on the line.
* **The projection of a record** (`isProjectionDensity_mconvE`): for a probability measure `μ` on
  `ℝ^d`, `f ∈ L¹` and a projection `p` of `f` along `e`, the function `(π_*μ) * p` is a projection
  of `μ * f`. Both sides of the defining identity, tested on `A`, are
  `∫ μ(dy) ∫ 1_A(⟨e, z + y⟩) f(z) dz`: on `ℝ^d` by Fubini and a translation, on the line by
  `integral_mul_mconv`, a translation, the projection identity at `A - w` and the image measure.
* **The Pólya frequency density** of `π_*μ_t` is `thm:matern-pyramid-line-noncreation`(1) for the
  marginal family; the convolution with it is the convolution with the measure, the density being
  nonnegative (a Pólya frequency function is, at order one).
* **The counts.** From scale zero, A23 (`cited_A23`) for the line's exponent `F_q`, `a = 0`,
  `θᵢ = q^{i+1}/c`, and the laws `π_*μ_t`; from rung to rung,
  `prop:ladder-non-creation-line`(2) (`ladder_non_creation_line`) with the multiplicities of
  `ladder_non_creation_line_matern`, and the laws `π_*μ_s`, `π_*μ_{s,qs}`.

**What it reaches.** The marginal family prints Lean core; the Pólya density prints
`cited_A22_polya` and `cited_A24` (the line's theorem is one declaration); the counts print
A22's two names (through A23) and `levy_khintchine_converse`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (mconvE mconv)
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ} {q c : ℝ}

/-- **`thm:matern-pyramid`(3), the marginal family.** Along a unit vector `e`, the marginal laws
`⟨e,·⟩_* μ_{s,t}` are the Matérn pyramid on the line. -/
theorem matern_pyramid_3_marginal {q c : ℝ}
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ) (e : Rd d) (he : ‖e‖ = 1) :
    IsMaternPyramid q c fun s t => marginal e (μ s t) := by
  intro s t hs hst
  haveI := (hμ s t hs hst).1
  refine ⟨inferInstance, fun ω => ?_⟩
  rw [charFun_marginal, charFun_maternPyramid hμ hs hst, norm_smul, he, mul_one]

/-! ## The projection of a record -/


/-- `1_A(σ + w) g(σ)` is the indicator of the translate `A - w`. -/
theorem indicator_translate_mul (A : Set ℝ) (w : ℝ) (g : ℝ → ℝ) :
    (fun σ => A.indicator 1 (σ + w) * g σ) = ((fun σ => σ + w) ⁻¹' A).indicator g := by
  funext σ
  by_cases hσ : σ + w ∈ A
  · simp [indicator_of_mem hσ, indicator_of_mem (show σ ∈ (fun σ => σ + w) ⁻¹' A from hσ)]
  · simp [indicator_of_notMem hσ, indicator_of_notMem (show σ ∉ (fun σ => σ + w) ⁻¹' A from hσ)]

/-- The projection identity tested on a translate:
`∫ 1_A(σ + w) p(σ) dσ = ∫ 1_A(⟨e,z⟩ + w) f(z) dz`. -/
theorem integral_indicator_translate_of_proj {e : Rd d} {f : Rd d → ℝ} {p : ℝ → ℝ}
    (hp : IsProjectionDensity e f p) {A : Set ℝ} (hA : MeasurableSet A) (w : ℝ) :
    ∫ σ, A.indicator 1 (σ + w) * p σ = ∫ z, A.indicator 1 (⟪e, z⟫ + w) * f z := by
  have hAw : MeasurableSet ((fun σ => σ + w) ⁻¹' A) := measurable_add_const w hA
  have h3 : (fun z : Rd d => A.indicator 1 (⟪e, z⟫ + w) * f z) =
      ((fun z : Rd d => ⟪e, z⟫) ⁻¹' ((fun σ => σ + w) ⁻¹' A)).indicator f := by
    funext z
    by_cases hz : ⟪e, z⟫ + w ∈ A
    · simp [indicator_of_mem hz, indicator_of_mem
        (show z ∈ (fun z : Rd d => ⟪e, z⟫) ⁻¹' ((fun σ => σ + w) ⁻¹' A) from hz)]
    · simp [indicator_of_notMem hz, indicator_of_notMem
        (show z ∉ (fun z : Rd d => ⟪e, z⟫) ⁻¹' ((fun σ => σ + w) ⁻¹' A) from hz)]
  rw [indicator_translate_mul, h3, integral_indicator hAw,
    integral_indicator ((continuous_inner_left e).measurable hAw)]
  exact hp.2 _ hAw

/-- **The projection of `μ * f`** is `(π_*μ) * p` for every projection `p` of `f`. -/
theorem isProjectionDensity_mconvE (μ : Measure (Rd d)) [IsProbabilityMeasure μ] {e : Rd d}
    {f : Rd d → ℝ} (hf : Integrable f) {p : ℝ → ℝ} (hp : IsProjectionDensity e f p) :
    IsProjectionDensity e (mconvE μ f) (mconv (marginal e μ) p) := by
  have hpi := hp.1
  refine ⟨ScaleSpace.integrable_mconv _ hpi.1 hpi, fun A hA => ?_⟩
  have hgm : Measurable (A.indicator (1 : ℝ → ℝ)) := measurable_const.indicator hA
  have hgb : ∀ t, |A.indicator (1 : ℝ → ℝ) t| ≤ 1 := fun t => by
    by_cases ht : t ∈ A <;> simp [ht]
  have hπ : Measurable fun x : Rd d => ⟪e, x⟫ := (continuous_inner_left e).measurable
  -- the line side
  have hmeas : AEStronglyMeasurable (fun w => ∫ σ, A.indicator 1 (σ + w) * p σ)
      (marginal e μ) := by
    have hs : StronglyMeasurable fun w => ∫ σ, A.indicator 1 (σ + w) * hpi.1.mk p σ := by
      refine StronglyMeasurable.integral_prod_right'
        (f := fun x : ℝ × ℝ => A.indicator 1 (x.2 + x.1) * hpi.1.mk p x.2) ?_
      exact ((hgm.comp (measurable_snd.add measurable_fst)).mul
        (hpi.1.stronglyMeasurable_mk.measurable.comp measurable_snd)).stronglyMeasurable
    refine hs.aestronglyMeasurable.congr (Eventually.of_forall fun w => ?_)
    exact integral_congr_ae (hpi.1.ae_eq_mk.mono fun σ hσ => by simp only [hσ])
  have hL : ∫ σ in A, mconv (marginal e μ) p σ =
      ∫ y, (∫ z, A.indicator 1 (⟪e, z⟫ + ⟪e, y⟫) * f z) ∂μ := by
    rw [← integral_indicator hA]
    have e1 : A.indicator (mconv (marginal e μ) p) =
        fun t => A.indicator 1 t * mconv (marginal e μ) p t := by
      funext t; by_cases ht : t ∈ A <;> simp [ht]
    have e2 : ∀ w, ∫ t, A.indicator 1 t * p (t - w) = ∫ σ, A.indicator 1 (σ + w) * p σ :=
      fun w => by
        rw [← integral_add_right_eq_self (fun t => A.indicator 1 t * p (t - w)) w]
        simp only [add_sub_cancel_right]
    rw [e1, ScaleSpace.integral_mul_mconv _ hpi.1 hpi hgm hgb]
    simp_rw [e2]
    rw [marginal, integral_map hπ.aemeasurable (by rw [← marginal]; exact hmeas)]
    simp_rw [integral_indicator_translate_of_proj hp hA]
  -- the side of `ℝ^d`
  have hR : ∫ x in (fun x : Rd d => ⟪e, x⟫) ⁻¹' A, mconvE μ f x =
      ∫ y, (∫ z, A.indicator 1 (⟪e, z⟫ + ⟪e, y⟫) * f z) ∂μ := by
    rw [← integral_indicator (hπ hA)]
    have e1 : ((fun x : Rd d => ⟪e, x⟫) ⁻¹' A).indicator (mconvE μ f) =
        fun x => ∫ y, A.indicator 1 ⟪e, x⟫ * f (x - y) ∂μ := by
      funext x
      rw [integral_const_mul]
      by_cases hx : ⟪e, x⟫ ∈ A
      · simp [indicator_of_mem hx, indicator_of_mem (show x ∈ (fun x : Rd d => ⟪e, x⟫) ⁻¹' A
          from hx), ScaleSpace.mconvE_apply]
      · simp [indicator_of_notMem hx, indicator_of_notMem
          (show x ∉ (fun x : Rd d => ⟪e, x⟫) ⁻¹' A from hx)]
    have hFi : Integrable (fun p : Rd d × Rd d => A.indicator 1 ⟪e, p.1⟫ * f (p.1 - p.2))
        (volume.prod μ) := by
      have hdom := (ScaleSpace.integrable_uncurry_subE μ hf.1 hf).norm
      refine hdom.mono' (((hgm.comp (hπ.comp measurable_fst)).aestronglyMeasurable).mul
        (ScaleSpace.integrable_uncurry_subE μ hf.1 hf).1) (Eventually.of_forall fun x => ?_)
      rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans le_rfl
      rw [Real.norm_eq_abs]; exact hgb _
    rw [e1, integral_integral_swap hFi]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [← integral_add_right_eq_self (fun x : Rd d => A.indicator 1 ⟪e, x⟫ * f (x - y)) y]
    simp only [add_sub_cancel_right, inner_add_right]
  rw [hL, hR]

/-- The convolution with the measure `φ dx` is `lineConv φ`, for `φ ≥ 0`. -/
theorem mconv_withDensity_eq_lineConv {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) (hφm : AEMeasurable φ)
    (p : ℝ → ℝ) : mconv ((volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (φ x)) p =
      lineConv φ p := by
  funext x
  rw [ScaleSpace.mconv_apply, lineConv,
    integral_withDensity_eq_integral_toReal_smul₀ hφm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hφ y)]

/-- **`thm:matern-pyramid`(3), the projected record.** For `f ∈ L¹(ℝ^d)` and `t > 0`, the
projection of the record `μ_t * f` along `e` is the projection of `f` convolved with a Pólya
frequency density, the density of `⟨e,·⟩_* μ_t`. -/
theorem matern_pyramid_3_polya {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ) (e : Rd d) (he : ‖e‖ = 1)
    (f : Rd d → ℝ) (hf : Integrable f) {t : ℝ} (ht : 0 < t) :
    ∃ φ : ℝ → ℝ, IsPolyaFrequencyDensity φ ∧
      marginal e (μ 0 t) = (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (φ x)) ∧
      ∀ p : ℝ → ℝ, IsProjectionDensity e f p →
        IsProjectionDensity e (mconvE (μ 0 t) f) (lineConv φ p) := by
  obtain ⟨φ, hφ, hm⟩ := (matern_pyramid_line_noncreation hq hc _
    (matern_pyramid_3_marginal μ hμ e he)).1 t ht
  refine ⟨φ, hφ, hm, fun p hp => ?_⟩
  haveI := (hμ 0 t le_rfl ht.le).1
  have h := isProjectionDensity_mconvE (μ 0 t) hf hp
  rwa [hm, mconv_withDensity_eq_lineConv hφ.1.nonneg hφ.2.1.1.aemeasurable] at h


/-- **`thm:matern-pyramid`(3), the counts.** Let `g` be a version of the projection of `f` that is
the primitive of an integrable `g'`. The version `(⟨e,·⟩_* μ_t) * g` of the projected record crosses
each level, and changes monotonicity, no more often than `g` (`t > 0`), and no more often at the
scale `qs` than at the scale `s` (`s > 0`); sign changes in the essential sense. -/
theorem matern_pyramid_3_counts {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ) (e : Rd d) (he : ‖e‖ = 1)
    (f : Rd d → ℝ) (hf : Integrable f) (g g' : ℝ → ℝ) (hg : IsProjectionDensity e f g)
    (hg' : Integrable g') (hprim : ∃ C : ℝ, ∀ x, g x = C + ∫ y in (0 : ℝ)..x, g' y) :
    (∀ t : ℝ, 0 < t →
      IsProjectionDensity e (mconvE (μ 0 t) f) (mconv (marginal e (μ 0 t)) g) ∧
        (∀ α : ℝ, essSignChanges (fun x => mconv (marginal e (μ 0 t)) g x - α) ≤
          essSignChanges (fun x => g x - α)) ∧
        essSignChanges (deriv (mconv (marginal e (μ 0 t)) g)) ≤ essSignChanges g') ∧
      ∀ s : ℝ, 0 < s →
        (∀ α : ℝ, essSignChanges (fun x => mconv (marginal e (μ 0 (q * s))) g x - α) ≤
          essSignChanges (fun x => mconv (marginal e (μ 0 s)) g x - α)) ∧
        essSignChanges (deriv (mconv (marginal e (μ 0 (q * s))) g)) ≤
          essSignChanges (deriv (mconv (marginal e (μ 0 s)) g)) := by
  have hm := matern_pyramid_3_marginal μ hμ e he
  have hμ1 : ∀ s : ℝ, 0 < s → IsProbabilityMeasure (marginal e (μ 0 s)) ∧
      ∀ ω : ℝ, charFun (marginal e (μ 0 s)) ω =
        ((Real.exp (-maternExponent q c (s * ω)) : ℝ) : ℂ) :=
    fun s hs => ⟨(hm 0 s le_rfl hs.le).1, charFun_matern_zero hm hs.le⟩
  refine ⟨fun t ht => ?_, fun s hs => ?_⟩
  · haveI := (hμ 0 t le_rfl ht.le).1
    refine ⟨isProjectionDensity_mconvE (μ 0 t) hf hg, ?_⟩
    exact cited_A23 (maternExponent q c) (isAdmissible_maternExponent hq hc) 0 le_rfl
      (maternTheta q c) (maternTheta_pos hq hc) (summable_maternTheta hq hc)
      (maternExponent_eq_atoms hq hc) (fun t => marginal e (μ 0 t)) (fun t ht => (hμ1 t ht).1)
      (fun t ht => (hμ1 t ht).2) g g' hg' hprim ht
  · obtain ⟨hF, hmult⟩ := ladder_non_creation_line_matern hq hc
    have hq0 : 0 < q := by linarith
    have hstep : ∀ s : ℝ, 0 < s → IsProbabilityMeasure (marginal e (μ s (q * s))) ∧
        ∀ ω : ℝ, charFun (marginal e (μ s (q * s))) ω =
          ((Real.exp (-(maternExponent q c (q * s * ω) - maternExponent q c (s * ω))) : ℝ) :
            ℂ) := by
      intro s hs
      have hle : s ≤ q * s := le_mul_of_one_le_left hs.le hq.le
      refine ⟨(hm s (q * s) hs.le hle).1, fun ω => ?_⟩
      rw [charFun_maternPyramid hm hs.le hle, Real.norm_eq_abs, maternExponent_mul_abs,
        maternExponent_mul_abs]
    have h := ladder_non_creation_line hq le_rfl (fun i : ℕ => q ^ (i + 1) / c)
      (fun i => div_pos (pow_pos hq0 _) hc)
      (by simpa [maternTheta] using summable_maternTheta hq hc) (maternExponent q c)
      (fun ω => by rw [hF ω, zero_mul, zero_add]) (exists_maternExponent_ne hq hc)
      (fun ϑ hϑ => by rw [hmult ϑ hϑ]; exact le_self_add)
    exact (h.2.2 (fun s => marginal e (μ 0 s)) (fun s => marginal e (μ s (q * s))) hμ1
      hstep).2.2 g g' hg' hprim s hs

end Pyramids
