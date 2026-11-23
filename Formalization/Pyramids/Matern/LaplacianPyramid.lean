/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.MaternDensity
import Pyramids.Matern.MaternSobolev

/-!
# `prop:laplacian-pyramid`: the level difference is a Laplacian

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:laplacian-pyramid`. Phase 5, wave 3b (on the
VM). `laplacian_pyramid` moved here from `PyramidsSkeleton.Ch04Matern`, its statement unchanged.

* **The records are smooth.** For `t > 0` the kernel `μ_t` has a `C^∞` density `p` with every
  derivative bounded (`matern_pyramid_1_family`), so `u(t, x) = ∫ f(z) p(x - z) dz`
  (`mconvE_withDensity_eq`). Differentiation under the integral sign, twice, with the bounds
  `|f(z)| sup‖Dᵏp‖` (`hasFDerivAt_densConv`), makes the record `C²` with
  `D²u(t, x) = ∫ f(z) D²p(x - z) dz`, continuous and bounded (`record_props`).
* **The first equality.** `μ_{qt} = μ_t ∗ L_{ct}` on the transforms, so `u(qt) = L_{ct} u(t)`
  almost everywhere (`mconvE_conv`), and everywhere, both sides being continuous.
* **The second.** Two integrations by parts per coordinate give `∫ u Δφ = ∫ (Δu) φ` for a `C²`
  function `u` and a smooth compactly supported `φ` (`integral_mul_laplacian`). With the Green
  identity of `lem:bessel-profile`(1) (`bessel_profile_1_green`), the continuous function
  `u(qt) - c²t²Δu(qt) - u(t)` integrates to `0` against every such `φ`, so it vanishes.

**What it reaches.** Lean core and the five names of A34's realization (`levy_khintchine_exists`,
`_unique`, `_converse`, `sato_polar_criterion`, `selfDecomposable_infinitelyDivisible`), through
`matern_pyramid_1_family`; nothing of its own.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter Laplacian
open ScaleSpace (mconvE)
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## Convolution of an integrable function with a bounded continuous kernel -/

section DensConv

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `(f ⋆ K)(x) := ∫ f(z) K(x - z) dz`. -/
noncomputable def densConv (K : Rd d → V) (f : Rd d → ℝ) (x : Rd d) : V :=
  ∫ z, f z • K (x - z)

theorem integrable_densConv_integrand {K : Rd d → V} (hK : Continuous K) {A : ℝ}
    (hA : ∀ y, ‖K y‖ ≤ A) {f : Rd d → ℝ} (hf : Integrable f) (x : Rd d) :
    Integrable fun z => f z • K (x - z) := by
  refine (hf.norm.const_mul A).mono' (hf.1.smul (hK.comp (continuous_const.sub
    continuous_id)).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _)

theorem continuous_densConv {K : Rd d → V} (hK : Continuous K) {A : ℝ}
    (hA : ∀ y, ‖K y‖ ≤ A) {f : Rd d → ℝ} (hf : Integrable f) : Continuous (densConv K f) := by
  refine continuous_of_dominated (bound := fun z => A * ‖f z‖)
    (fun x => (integrable_densConv_integrand hK hA hf x).1)
    (fun x => Eventually.of_forall fun z => ?_) (hf.norm.const_mul A)
    (Eventually.of_forall fun z => (hK.comp (continuous_id.sub continuous_const)).const_smul _)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _)

theorem norm_densConv_le {K : Rd d → V} {A : ℝ} (hA : ∀ y, ‖K y‖ ≤ A) {f : Rd d → ℝ}
    (hf : Integrable f) (x : Rd d) : ‖densConv K f x‖ ≤ ∫ z, A * ‖f z‖ := by
  refine norm_integral_le_of_norm_le (hf.norm.const_mul A) (Eventually.of_forall fun z => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _)

/-- **Differentiation under the integral sign**: for `K` differentiable with `K` and `DK`
continuous and bounded, `D(f ⋆ K) = f ⋆ DK`. -/
theorem hasFDerivAt_densConv {K : Rd d → V} (hK : Continuous K) {A : ℝ} (hA : ∀ y, ‖K y‖ ≤ A)
    (hKd : Differentiable ℝ K) (hK' : Continuous (fderiv ℝ K)) {B : ℝ}
    (hB : ∀ y, ‖fderiv ℝ K y‖ ≤ B) {f : Rd d → ℝ} (hf : Integrable f) (x : Rd d) :
    HasFDerivAt (densConv K f) (densConv (fderiv ℝ K) f x) x := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun x z => f z • fderiv ℝ K (x - z))
    (bound := fun z => B * ‖f z‖) univ_mem
    (Eventually.of_forall fun y => (integrable_densConv_integrand hK hA hf y).1)
    (integrable_densConv_integrand hK hA hf x)
    (integrable_densConv_integrand hK' hB hf x).1
    (Eventually.of_forall fun z y _ => ?_) (hf.norm.const_mul B)
    (Eventually.of_forall fun z y _ => ?_)
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  · have h := ((hKd (y - z)).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const z)).const_smul (f z)
    simp only [ContinuousLinearMap.comp_id] at h
    exact h

theorem fderiv_densConv {K : Rd d → V} (hK : Continuous K) {A : ℝ} (hA : ∀ y, ‖K y‖ ≤ A)
    (hKd : Differentiable ℝ K) (hK' : Continuous (fderiv ℝ K)) {B : ℝ}
    (hB : ∀ y, ‖fderiv ℝ K y‖ ≤ B) {f : Rd d → ℝ} (hf : Integrable f) :
    fderiv ℝ (densConv K f) = densConv (fderiv ℝ K) f :=
  funext fun x => (hasFDerivAt_densConv hK hA hKd hK' hB hf x).fderiv

end DensConv

/-! ## The record of a kernel with a smooth density -/

/-- A record against `p dx` is `f ⋆ p`. -/
theorem mconvE_withDensity_eq {p : Rd d → ℝ} (hp : Continuous p) (hp0 : ∀ x, 0 ≤ p x)
    (f : Rd d → ℝ) (x : Rd d) :
    mconvE (volume.withDensity fun y => ENNReal.ofReal (p y)) f x = densConv p f x := by
  rw [ScaleSpace.mconvE_apply, integral_withDensity_eq_integral_toReal_smul
    hp.measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hp0 _), smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun y => p y * f (x - y)) volume x, densConv]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [sub_sub_cancel, smul_eq_mul]
  ring

/-- **The record is `C²` with bounded derivatives.** For `p` smooth with every derivative bounded
and `f ∈ L¹`, `f ⋆ p` is continuous, bounded and `C²`, and its second derivative is
`f ⋆ D²p`, continuous and bounded. -/
theorem record_props {p : Rd d → ℝ} (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hpb : ∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n p x‖ ≤ C) {f : Rd d → ℝ}
    (hf : Integrable f) :
    Continuous (densConv p f) ∧ (∃ C : ℝ, ∀ x, |densConv p f x| ≤ C) ∧
      ContDiff ℝ 2 (densConv p f) ∧ Continuous (fderiv ℝ (fderiv ℝ (densConv p f))) ∧
      ∃ C : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ (densConv p f)) x‖ ≤ C := by
  obtain ⟨A, hA⟩ := hpb 0
  obtain ⟨B, hB⟩ := hpb 1
  obtain ⟨B2, hB2⟩ := hpb 2
  have hA' : ∀ y, ‖p y‖ ≤ A := fun y => by simpa using hA y
  have hB' : ∀ y, ‖fderiv ℝ p y‖ ≤ B := fun y => by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ p), norm_iteratedFDeriv_fderiv]
    exact hB y
  have hB2' : ∀ y, ‖fderiv ℝ (fderiv ℝ p) y‖ ≤ B2 := fun y => by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ (fderiv ℝ p)),
      norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
    exact hB2 y
  have hp1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ p) := (contDiff_infty_iff_fderiv.1 hp).2
  have hp2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ p)) := (contDiff_infty_iff_fderiv.1 hp1).2
  have hd0 := fderiv_densConv hp.continuous hA' (hp.differentiable (by simp))
    hp1.continuous hB' hf
  have hd1 := fderiv_densConv hp1.continuous hB' (hp1.differentiable (by simp))
    hp2.continuous hB2' hf
  have hdiff0 : Differentiable ℝ (densConv p f) := fun x =>
    (hasFDerivAt_densConv hp.continuous hA' (hp.differentiable (by simp)) hp1.continuous hB'
      hf x).differentiableAt
  have hdiff1 : Differentiable ℝ (densConv (fderiv ℝ p) f) := fun x =>
    (hasFDerivAt_densConv hp1.continuous hB' (hp1.differentiable (by simp)) hp2.continuous hB2'
      hf x).differentiableAt
  have hc2 : Continuous (densConv (fderiv ℝ (fderiv ℝ p)) f) :=
    continuous_densConv hp2.continuous hB2' hf
  have hI : ∀ C : ℝ, ∫ z, C * ‖f z‖ = C * ∫ z, ‖f z‖ := fun C => integral_const_mul _ _
  refine ⟨continuous_densConv hp.continuous hA' hf, ⟨A * ∫ z, ‖f z‖, fun x => ?_⟩, ?_, ?_,
    ⟨B2 * ∫ z, ‖f z‖, fun x => ?_⟩⟩
  · rw [← Real.norm_eq_abs, ← hI]
    exact norm_densConv_le hA' hf x
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_fderiv]
    refine ⟨hdiff0, by simp, ?_⟩
    rw [hd0, contDiff_one_iff_fderiv, hd1]
    exact ⟨hdiff1, hc2⟩
  · rw [hd0, hd1]
    exact hc2
  · rw [hd0, hd1, ← hI]
    exact norm_densConv_le hB2' hf x

/-! ## Integration by parts against a test function -/

/-- `∂_e(∂_e g) = D²g(e, e)`. -/
theorem fderiv_fderiv_apply_eq {g : Rd d → ℝ} (hg : ContDiff ℝ 2 g) (e x : Rd d) :
    fderiv ℝ (fun y => fderiv ℝ g y e) x e = iteratedFDeriv ℝ 2 g x ![e, e] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem integrable_mul_of_compact {a b : Rd d → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hbc : HasCompactSupport b) : Integrable fun x => a x * b x :=
  (ha.mul hb).integrable_of_hasCompactSupport hbc.mul_left

/-- **`∫ u ∂_e²φ = ∫ (∂_e²u) φ`** for `u` of class `C²` and `φ` smooth with compact support. -/
theorem integral_mul_second {u φ : Rd d → ℝ} (hu : ContDiff ℝ 2 u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (e : Rd d) :
    ∫ x, u x * iteratedFDeriv ℝ 2 φ x ![e, e] = ∫ x, iteratedFDeriv ℝ 2 u x ![e, e] * φ x := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact WithTop.coe_le_coe.2 le_top)
  set φ1 : Rd d → ℝ := fun y => fderiv ℝ φ y e
  set u1 : Rd d → ℝ := fun y => fderiv ℝ u y e
  have hφ1 : ContDiff ℝ 1 φ1 := ((contDiff_infty_iff_fderiv.1 hφ).2.clm_apply contDiff_const).of_le
    (by exact WithTop.coe_le_coe.2 le_top)
  have hu1 : ContDiff ℝ 1 u1 := (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hφ1c : HasCompactSupport φ1 := hφc.fderiv_apply (𝕜 := ℝ) e
  have hφ11c : HasCompactSupport fun y => fderiv ℝ φ1 y e := hφ1c.fderiv_apply (𝕜 := ℝ) e
  have hcφ1' : Continuous fun y => fderiv ℝ φ1 y e :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcu1' : Continuous fun y => fderiv ℝ u1 y e :=
    (hu1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have step1 : ∫ x, u x * fderiv ℝ φ1 x e = -∫ x, u1 x * φ1 x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (integrable_mul_of_compact hu1.continuous hφ1.continuous hφ1c)
      (integrable_mul_of_compact hu.continuous hcφ1' hφ11c)
      (integrable_mul_of_compact hu.continuous hφ1.continuous hφ1c)
      (fun x _ => (hu.differentiable (by norm_num)) x)
      (fun x _ => (hφ1.differentiable one_ne_zero) x)
  have step2 : ∫ x, u1 x * φ1 x = -∫ x, fderiv ℝ u1 x e * φ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (integrable_mul_of_compact hcu1' hφ.continuous hφc)
      (integrable_mul_of_compact hu1.continuous hφ1.continuous hφ1c)
      (integrable_mul_of_compact hu1.continuous hφ.continuous hφc)
      (fun x _ => (hu1.differentiable one_ne_zero) x)
      (fun x _ => (hφ.differentiable (by simp)) x)
  have e1 : ∀ x, iteratedFDeriv ℝ 2 φ x ![e, e] = fderiv ℝ φ1 x e := fun x =>
    (fderiv_fderiv_apply_eq hφ2 e x).symm
  have e2 : ∀ x, iteratedFDeriv ℝ 2 u x ![e, e] = fderiv ℝ u1 x e := fun x =>
    (fderiv_fderiv_apply_eq hu e x).symm
  simp_rw [e1, e2]
  rw [step1, step2, neg_neg]

/-- **`∫ u Δφ = ∫ (Δu) φ`** for `u` of class `C²` and `φ` smooth with compact support. -/
theorem integral_mul_laplacian {u φ : Rd d → ℝ} (hu : ContDiff ℝ 2 u)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, u x * Δ φ x = ∫ x, Δ u x * φ x := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact WithTop.coe_le_coe.2 le_top)
  have hc2 : ∀ {g : Rd d → ℝ}, ContDiff ℝ 2 g → ∀ e : Rd d,
      Continuous fun x => iteratedFDeriv ℝ 2 g x ![e, e] := by
    intro g hg e
    have h1 : ContDiff ℝ 1 fun y => fderiv ℝ g y e :=
      (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    rw [show (fun x => iteratedFDeriv ℝ 2 g x ![e, e]) =
        fun x => fderiv ℝ (fun y => fderiv ℝ g y e) x e from
      funext fun x => (fderiv_fderiv_apply_eq hg e x).symm]
    exact (h1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsupp : ∀ e : Rd d, HasCompactSupport fun x => iteratedFDeriv ℝ 2 φ x ![e, e] := by
    intro e
    rw [show (fun x => iteratedFDeriv ℝ 2 φ x ![e, e]) =
        fun x => fderiv ℝ (fun y => fderiv ℝ φ y e) x e from
      funext fun x => (fderiv_fderiv_apply_eq hφ2 e x).symm]
    exact (hφc.fderiv_apply (𝕜 := ℝ) e).fderiv_apply (𝕜 := ℝ) e
  have hL : ∀ x, u x * Δ φ x = ∑ j, u x * iteratedFDeriv ℝ 2 φ x ![ebasis j, ebasis j] :=
    fun x => by rw [laplacian_eq_sum_ebasis, Finset.mul_sum]
  have hR : ∀ x, Δ u x * φ x = ∑ j, iteratedFDeriv ℝ 2 u x ![ebasis j, ebasis j] * φ x :=
    fun x => by rw [laplacian_eq_sum_ebasis, Finset.sum_mul]
  rw [integral_congr_ae (Eventually.of_forall hL), integral_congr_ae (Eventually.of_forall hR),
    integral_finsetSum _ fun j _ => integrable_mul_of_compact hu.continuous
      (hc2 hφ2 (ebasis j)) (hsupp (ebasis j)),
    integral_finsetSum _ fun j _ => integrable_mul_of_compact (hc2 hu (ebasis j)) hφ.continuous
      hφc]
  exact Finset.sum_congr rfl fun j _ => integral_mul_second hu hφ hφc (ebasis j)

/-- The Laplacian of a function whose second derivative is continuous and bounded. -/
theorem laplacian_props {u : Rd d → ℝ} (hc : Continuous (fderiv ℝ (fderiv ℝ u)))
    {C : ℝ} (hC : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C) :
    Continuous (Δ u) ∧ ∃ C' : ℝ, ∀ x, |Δ u x| ≤ C' := by
  have hΔ : Δ u = fun x => ∑ j, fderiv ℝ (fderiv ℝ u) x (ebasis j) (ebasis j) := by
    funext x
    rw [laplacian_eq_sum_ebasis]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hΔ]
  refine ⟨continuous_finsetSum _ fun j _ =>
    (hc.clm_apply continuous_const).clm_apply continuous_const, ∑ _j : Fin d, C, fun x => ?_⟩
  rw [← Real.norm_eq_abs]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  calc ‖fderiv ℝ (fderiv ℝ u) x (ebasis j) (ebasis j)‖
      ≤ ‖fderiv ℝ (fderiv ℝ u) x (ebasis j)‖ * ‖ebasis j‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ u) x‖ * ‖ebasis j‖ * ‖ebasis j‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ C := by rw [norm_ebasis, mul_one, mul_one]; exact hC x

/-! ## The proposition -/

/-- **`prop:laplacian-pyramid`.** For `f ∈ L¹(ℝ^d)`, `u(t,·) = μ_t * f` and `t > 0`: the records at
`t` and `qt` are continuous and bounded, the one at `qt` is `C²` with a continuous bounded
Laplacian, and at every point `u(t) - u(qt) = (I - L_{ct}) u(t) = -c²t² Δ u(qt)`. -/
theorem laplacian_pyramid (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ) (f : Rd d → ℝ) (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) :
    Continuous (mconvE (μ 0 t) f) ∧ (∃ C : ℝ, ∀ x, |mconvE (μ 0 t) f x| ≤ C) ∧
      ContDiff ℝ 2 (mconvE (μ 0 (q * t)) f) ∧ (∃ C : ℝ, ∀ x, |mconvE (μ 0 (q * t)) f x| ≤ C) ∧
      Continuous (Δ (mconvE (μ 0 (q * t)) f)) ∧
      (∃ C : ℝ, ∀ x, |Δ (mconvE (μ 0 (q * t)) f) x| ≤ C) ∧
      (∀ x, mconvE (μ 0 t) f x - mconvE (μ 0 (q * t)) f x =
        mconvE (μ 0 t) f x - mconvE (maternStep d (c * t)) (mconvE (μ 0 t) f) x) ∧
      ∀ x, mconvE (μ 0 t) f x - mconvE (maternStep d (c * t)) (mconvE (μ 0 t) f) x =
        -(c ^ 2 * t ^ 2) * Δ (mconvE (μ 0 (q * t)) f) x := by
  have hqt : 0 < q * t := mul_pos (by linarith) ht
  obtain ⟨-, -, hstep, hdens⟩ := matern_pyramid_1_family hd hq hc μ hμ
  -- the two records as `f ⋆ p`
  have hrec : ∀ s : ℝ, 0 < s → ∃ p : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧
      (∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n p x‖ ≤ C) ∧
      mconvE (μ 0 s) f = densConv p f := by
    intro s hs
    obtain ⟨p, hp, hp0, hpb, hμs⟩ := hdens s hs
    exact ⟨p, hp, hpb, funext fun x => by rw [hμs, mconvE_withDensity_eq hp.continuous hp0]⟩
  obtain ⟨p, hp, hpb, hu⟩ := hrec t ht
  obtain ⟨P, hP, hPb, hU⟩ := hrec (q * t) hqt
  obtain ⟨hgc, ⟨Cg, hCg⟩, -, -, -⟩ := record_props hp hpb hf
  obtain ⟨hUc, hUb, hU2, hD2c, ⟨C2, hC2⟩⟩ := record_props hP hPb hf
  rw [← hu] at hgc hCg
  rw [← hU] at hUc hUb hU2 hD2c hC2
  obtain ⟨hΔc, hΔb⟩ := laplacian_props hD2c hC2
  set g := mconvE (μ 0 t) f with hg
  set U := mconvE (μ 0 (q * t)) f with hUdef
  set L := maternStep d (c * t) with hL
  haveI := (hμ 0 t le_rfl ht.le).1
  haveI := (hμ 0 (q * t) le_rfl hqt.le).1
  haveI hLp : IsProbabilityMeasure L := (charFun_maternStep (d := d) (c * t) 0).1
  have hgi : Integrable g := ScaleSpace.integrable_mconvE (μ 0 t) hf.1 hf
  -- the first equality: `U = L * g` everywhere
  have hconv : μ 0 (q * t) = μ 0 t ∗ L := by
    have hle : t ≤ q * t := le_mul_of_one_le_left ht.le hq.le
    haveI := (hμ t (q * t) ht.le hle).1
    rw [hL, ← hstep t ht]
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_conv, (hμ 0 (q * t) le_rfl hqt.le).2 ω, (hμ 0 t le_rfl ht.le).2 ω,
      (hμ t (q * t) ht.le hle).2 ω, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hLgc : Continuous (mconvE L g) := by
    refine continuous_of_dominated (bound := fun _ => Cg) (fun x => ?_)
      (fun x => Eventually.of_forall fun y => ?_) (integrable_const Cg)
      (Eventually.of_forall fun y => hgc.comp (continuous_id.sub continuous_const))
    · exact (hgc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact hCg _
  have hUL : ∀ x, U x = mconvE L g x := by
    have hae := ScaleSpace.mconvE_conv (μ 0 t) L hf.1 hf
    rw [← hconv] at hae
    have := (Continuous.ae_eq_iff_eq volume hLgc hUc).1 hae
    exact fun x => (congrFun this x).symm
  refine ⟨hgc, ⟨Cg, hCg⟩, hU2, hUb, hΔc, hΔb, fun x => by rw [hUL x], ?_⟩
  -- the second equality: `U - (ct)²ΔU - g` vanishes as a distribution, and is continuous
  set r := c * t with hr
  have hWc : Continuous fun x => U x - r ^ 2 * Δ U x - g x :=
    (hUc.sub (continuous_const.mul hΔc)).sub hgc
  have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hWc.locallyIntegrable
    fun φ hφ hφc => by
      have hφ' : ContDiff ℝ (⊤ : ℕ∞) φ := hφ
      have hφ2 : ContDiff ℝ 2 φ := hφ'.of_le (by exact WithTop.coe_le_coe.2 le_top)
      have hΔφc : Continuous (Δ φ) := by
        rw [funext (laplacian_eq_sum_ebasis φ)]
        exact continuous_finsetSum _ fun j _ =>
          (continuous_eval_const _).comp (hφ2.continuous_iteratedFDeriv le_rfl)
      have hΔφs : HasCompactSupport (Δ φ) := by
        refine (hφc.iteratedFDeriv (𝕜 := ℝ) 2).mono fun x hx => ?_
        rw [Function.mem_support] at hx ⊢
        contrapose! hx
        rw [laplacian_eq_sum_ebasis φ x, hx]
        simp
      have hgreen := bessel_profile_1_green (d := d) (r := r) g hgi φ hφ' hφc
      rw [← funext hUL] at hgreen
      have hibp := integral_mul_laplacian hU2 hφ' hφc
      have i1 := integrable_mul_of_compact hUc hφ'.continuous hφc
      have i2 := integrable_mul_of_compact hUc hΔφc hΔφs
      have i3 := integrable_mul_of_compact hΔc hφ'.continuous hφc
      have i4 := integrable_mul_of_compact hgc hφ'.continuous hφc
      have hsplit : ∫ x, U x * (φ x - r ^ 2 * Δ φ x) =
          (∫ x, U x * φ x) - r ^ 2 * ∫ x, U x * Δ φ x := by
        rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul _)]
        congr 1
        funext x
        ring
      have hfun : (fun x => φ x • (U x - r ^ 2 * Δ U x - g x)) =
          fun x => (U x * φ x - r ^ 2 * (Δ U x * φ x)) - g x * φ x := by
        funext x
        rw [smul_eq_mul]
        ring
      have e1 : ∫ x, (U x * φ x - r ^ 2 * (Δ U x * φ x)) - g x * φ x =
          (∫ x, U x * φ x - r ^ 2 * (Δ U x * φ x)) - ∫ x, g x * φ x :=
        integral_sub (i1.sub (i3.const_mul _)) i4
      have e2 : ∫ x, U x * φ x - r ^ 2 * (Δ U x * φ x) =
          (∫ x, U x * φ x) - ∫ x, r ^ 2 * (Δ U x * φ x) :=
        integral_sub i1 (i3.const_mul _)
      have e3 : ∫ x, r ^ 2 * (Δ U x * φ x) = r ^ 2 * ∫ x, Δ U x * φ x := integral_const_mul _ _
      rw [hfun, e1, e2, e3, ← hibp]
      linarith [hsplit, hgreen]
  have hW := (Continuous.ae_eq_iff_eq volume hWc continuous_const).1 h0
  intro x
  have hx := congrFun hW x
  rw [← hUL x]
  have : r ^ 2 = c ^ 2 * t ^ 2 := by rw [hr]; ring
  rw [this] at hx
  linarith

end Pyramids
