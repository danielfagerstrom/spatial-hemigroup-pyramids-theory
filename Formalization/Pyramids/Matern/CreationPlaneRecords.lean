/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.CreationPlaneGauss
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# `prop:creation-plane`(2): every witness is a record

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:creation-plane`. Phase 5, wave 3b (on the
VM). `creation_plane_2` moved here from `PyramidsSkeleton.Ch04Matern`, its conclusion unchanged; it
no longer takes `2 ≤ d`, which its proof does not read (2026-11-15, a strengthening).

* **Plancherel for an integrable square-integrable transform.** For `φ ∈ L¹ ∩ L²` the integral
  `G(z) = ∫ e^{2πi⟨ξ,z⟩} φ(ξ) dξ` is in `L²`: the `L²` element `𝓕⁻ φ` has the tempered
  distribution `𝓕⁻ T_φ` (`Lp.fourierInv_toTemperedDistribution_eq`), which by Fubini is the
  distribution of `G`; so `G = 𝓕⁻ φ` almost everywhere (`ae_eq_of_integral_contDiff_smul_eq`).
* **The transform of the witness.** `h_{a,δ} = N(0, τI) * g₀` with `g₀` integrable
  (`exists_gauss_record`, `τ = min(1, δ²)/2`), so `𝓕h(ξ) = e^{-2π²τ|ξ|²} 𝓕g₀(ξ)` by Fubini, and
  `|𝓕h(ξ)| ≤ ‖g₀‖₁ e^{-2π²τ|ξ|²}`: no transform of the anisotropic ridge is computed.
* **The deconvolution.** `φ := 𝓕h / η̂(-2π·)` is continuous, and integrable and bounded by
  `|φ(ξ)| ≤ C e^{-π²τ|ξ|²}`, from `1/η̂(ω) ≤ C_ε e^{ε|ω|²}` at `ε = τ/4`. Then
  `g := Re ∫ e^{2πi⟨ξ,·⟩} φ(ξ) dξ` is continuous and bounded, in `L²` by the first point, and
  `η * g = Re 𝓕⁻(η̂(-2π·) φ) = Re 𝓕⁻ 𝓕h = h` (`mconvE_re_fourierInvInt`, Fourier inversion). No
  realness argument is needed: the real part is taken.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter FourierTransform SchwartzMap
open ScaleSpace (mconvE)
open scoped Topology RealInnerProductSpace ComplexOrder

variable {d : ℕ}

/-! ## Plancherel for an integrable, square-integrable transform -/

/-- The inverse transform written as an integral, `∫ e^{2πi⟨ξ,z⟩} φ(ξ) dξ`. -/
noncomputable def invInt (φ : Rd d → ℂ) (z : Rd d) : ℂ :=
  ∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) * Complex.I) * φ ξ

theorem continuous_invInt {φ : Rd d → ℂ} (hφ : Integrable φ) : Continuous (invInt φ) := by
  refine continuous_of_dominated (bound := fun ξ => ‖φ ξ‖)
    (fun z => (Continuous.aestronglyMeasurable (by fun_prop)).mul hφ.1)
    (fun z => Eventually.of_forall fun ξ => ?_) hφ.norm (Eventually.of_forall fun ξ => ?_)
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  · fun_prop

theorem norm_invInt_le {φ : Rd d → ℂ} (z : Rd d) : ‖invInt φ z‖ ≤ ∫ ξ, ‖φ ξ‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext ξ
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **Fubini against a Schwartz function**: `∫ (𝓕⁻ f) φ = ∫ f · invInt φ`. -/
theorem integral_fourierInv_mul {φ : Rd d → ℂ} (hφ : Integrable φ) (f : 𝓢(Rd d, ℂ)) :
    ∫ ξ, (𝓕⁻ f) ξ * φ ξ = ∫ z, f z * invInt φ z := by
  have hint : Integrable (Function.uncurry fun (z ξ : Rd d) =>
      Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) * Complex.I) * (f z * φ ξ)) (volume.prod volume) := by
    refine (f.integrable.mul_prod hφ).norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul
        (f.integrable.mul_prod hφ).1
    · simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  have hL : ∀ ξ, (𝓕⁻ f) ξ * φ ξ =
      ∫ z, Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) * Complex.I) * (f z * φ ξ) := by
    intro ξ
    rw [fourierInv_coe, Real.fourierInv_eq', ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul, real_inner_comm z ξ]
    ring
  have hR : ∀ z, f z * invInt φ z =
      ∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) * Complex.I) * (f z * φ ξ) := by
    intro z
    rw [invInt, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    ring
  simp_rw [hL, hR]
  exact (integral_integral_swap hint).symm

/-- **Plancherel**, in the form needed: for `φ ∈ L¹ ∩ L²`, `invInt φ ∈ L²`. -/
theorem memLp_two_invInt {φ : Rd d → ℂ} (hφ : Integrable φ) (hφ2 : MemLp φ 2) :
    MemLp (invInt φ) 2 := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Lp ℂ 2 (volume : Measure (Rd d)), Φ = hφ2.toLp φ := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G' : Lp ℂ 2 (volume : Measure (Rd d)), G' = 𝓕⁻ Φ := ⟨_, rfl⟩
  have hcont := continuous_invInt hφ
  have key : ∀ f : 𝓢(Rd d, ℂ), ∫ z, f z • G' z = ∫ z, f z * invInt φ z := by
    intro f
    calc ∫ z, f z • G' z = Lp.toTemperedDistribution G' f :=
          (Lp.toTemperedDistribution_apply G' f).symm
      _ = 𝓕⁻ (Lp.toTemperedDistribution Φ) f := by
          rw [hG', Lp.fourierInv_toTemperedDistribution_eq]
      _ = Lp.toTemperedDistribution Φ (𝓕⁻ f) := TemperedDistribution.fourierInv_apply _ _
      _ = ∫ ξ, (𝓕⁻ f) ξ • Φ ξ := Lp.toTemperedDistribution_apply Φ _
      _ = ∫ ξ, (𝓕⁻ f) ξ * φ ξ := by
          refine integral_congr_ae ?_
          filter_upwards [hΦ ▸ hφ2.coeFn_toLp] with ξ hξ
          rw [smul_eq_mul, hξ]
      _ = _ := integral_fourierInv_mul hφ f
  have hae : (G' : Rd d → ℂ) =ᵐ[volume] invInt φ := by
    refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp G').locallyIntegrable (by norm_num))
      hcont.locallyIntegrable fun g g_smooth g_cpt => ?_
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.ofRealCLM ∘ g) := by fun_prop
    have := key (hg₁.toSchwartzMap hg₂)
    simp only [HasCompactSupport.toSchwartzMap_toFun, Function.comp_apply,
      Complex.ofRealCLM_apply] at this
    simpa only [Complex.real_smul, smul_eq_mul] using this
  exact (Lp.memLp G').ae_eq hae

/-! ## The transform of a record -/

theorem continuous_fourier_of_integrable {f : Rd d → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) := by
  have h : (𝓕 f) = fun w => ∫ v, Complex.exp (↑(-2 * Real.pi * ⟪v, w⟫) * Complex.I) * f v :=
    funext fun w => by rw [Real.fourier_eq']; simp only [smul_eq_mul]
  rw [h]
  refine continuous_of_dominated (bound := fun v => ‖f v‖)
    (fun w => (Continuous.aestronglyMeasurable (by fun_prop)).mul hf.1)
    (fun w => Eventually.of_forall fun v => ?_) hf.norm (Eventually.of_forall fun v => ?_)
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  · fun_prop

theorem norm_fourier_le_integral {f : Rd d → ℂ} (w : Rd d) : ‖𝓕 f w‖ ≤ ∫ v, ‖f v‖ := by
  rw [Real.fourier_eq']
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext v
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `(x, y) ↦ g(x - y)` is integrable on `volume × μ`. -/
theorem integrable_prod_comp_sub (μ : Measure (Rd d)) [IsFiniteMeasure μ] {g : Rd d → ℂ}
    (hg : Integrable g) (hgc : Continuous g) :
    Integrable (fun p : Rd d × Rd d => g (p.1 - p.2)) (volume.prod μ) := by
  rw [integrable_prod_iff' (Continuous.aestronglyMeasurable (by fun_prop))]
  refine ⟨Eventually.of_forall fun y => hg.comp_sub_right y, ?_⟩
  have : (fun y => ∫ x, ‖g (x - y)‖) = fun _ => ∫ x, ‖g x‖ :=
    funext fun y => integral_sub_right_eq_self (fun x => ‖g x‖) y
  simp only
  rw [this]
  exact integrable_const _

/-- A record of an integrable continuous function is integrable. -/
theorem integrable_mconvE (μ : Measure (Rd d)) [IsFiniteMeasure μ] {g : Rd d → ℝ}
    (hg : Integrable g) (hgc : Continuous g) :
    Integrable fun x => (mconvE μ g x : ℂ) := by
  have h := (integrable_prod_comp_sub μ hg.ofReal (by fun_prop)).integral_prod_left
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [ScaleSpace.mconvE_apply]
  exact integral_complex_ofReal

/-- **The transform of a record**: `𝓕(μ * g)(ξ) = μ̂(-2πξ) 𝓕g(ξ)`. -/
theorem fourier_mconvE (μ : Measure (Rd d)) [IsFiniteMeasure μ] {g : Rd d → ℝ}
    (hg : Integrable g) (hgc : Continuous g) (ξ : Rd d) :
    𝓕 (fun x => (mconvE μ g x : ℂ)) ξ =
      charFun μ (-(2 * Real.pi) • ξ) * 𝓕 (fun x => (g x : ℂ)) ξ := by
  have hG := integrable_prod_comp_sub μ hg.ofReal (by fun_prop)
  have hint : Integrable (Function.uncurry fun (x y : Rd d) =>
      Complex.exp (↑(-2 * Real.pi * ⟪x, ξ⟫) * Complex.I) * (g (x - y) : ℂ)) (volume.prod μ) := by
    refine hG.norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul hG.1)
      (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact le_rfl
  have h1 : ∀ x, Complex.exp (↑(-2 * Real.pi * ⟪x, ξ⟫) * Complex.I) • (mconvE μ g x : ℂ) =
      ∫ y, Complex.exp (↑(-2 * Real.pi * ⟪x, ξ⟫) * Complex.I) * (g (x - y) : ℂ) ∂μ := by
    intro x
    rw [ScaleSpace.mconvE_apply, smul_eq_mul, ← integral_complex_ofReal, ← integral_const_mul]
  have h2 : ∀ y, ∫ x, Complex.exp (↑(-2 * Real.pi * ⟪x, ξ⟫) * Complex.I) * (g (x - y) : ℂ) =
      Complex.exp (↑⟪y, -(2 * Real.pi) • ξ⟫ * Complex.I) * 𝓕 (fun x => (g x : ℂ)) ξ := by
    intro y
    rw [← integral_add_right_eq_self _ y, Real.fourier_eq', ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [add_sub_cancel_right, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [inner_add_left, real_inner_smul_right]
    push_cast
    ring
  rw [Real.fourier_eq']
  simp_rw [h1]
  rw [integral_integral_swap hint]
  simp_rw [h2]
  rw [integral_mul_const, charFun_apply]

/-- `E_v` is integrable: it lies under `e^{-|z|²/(2M)}`, `M ≥ max vᵢ`. -/
theorem integrable_gEv {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) : Integrable (gEv v) := by
  set M : ℝ := 1 + ∑ i, v i with hMdef
  have hS : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun j _ => (hv j).le
  have hM : ∀ i, v i ≤ M := fun i => by
    have := Finset.single_le_sum (fun j _ => (hv j).le) (Finset.mem_univ i)
    linarith
  have hM0 : 0 < M := by linarith
  refine (integrable_exp_neg_mul_sq_norm_Rd (d := d) (c := 1 / (2 * M)) (by positivity)).mono'
    (continuous_gEv v).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (gEv_pos v z), gEv, Real.exp_le_exp,
    EuclideanSpace.real_norm_sq_eq, neg_mul, neg_le_neg_iff, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [div_mul_eq_mul_div, one_mul]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by have := hv i; positivity)
    (by linarith [hM i])

/-! ## The statement -/

/-- **`prop:creation-plane`(2), records.** If `η̂ > 0` and `1/η̂(ω) ≤ C_ε e^{ε|ω|²}` for every
`ε > 0`, every `h_{a,δ}` is `η * g` with `g` real, bounded, continuous and in `L²`. -/
theorem creation_plane_2 [NeZero d] (η : Measure (Rd d)) [IsProbabilityMeasure η]
    (hpos : ∀ ω, 0 < charFun η ω)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ ω : Rd d,
      ((charFun η ω).re)⁻¹ ≤ Cε * Real.exp (ε * ‖ω‖ ^ 2))
    {a δ : ℝ} (ha : 1 < a) (hδ : 0 < δ) :
    ∃ g : Rd d → ℝ, Continuous g ∧ (∃ C : ℝ, ∀ x, |g x| ≤ C) ∧ MemLp g 2 volume ∧
      ∀ x, mconvE η g x = creationWitness d a δ x := by
  -- the witness is a Gaussian record
  have hm : 0 < min 1 (δ ^ 2) := lt_min one_pos (by positivity)
  set τ : ℝ := min 1 (δ ^ 2) / 2 with hτdef
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ < 1 := by have := min_le_left 1 (δ ^ 2); linarith
  have hτδ : τ < δ ^ 2 := by have := min_le_right 1 (δ ^ 2); linarith
  obtain ⟨w0, w2, v0, v2, -, -, hv0p, hv2p, hrec⟩ :=
    exists_gauss_record (d := d) ha hδ hτ0 hτ1 hτδ
  obtain ⟨g0, hg0⟩ : ∃ g0 : Rd d → ℝ, g0 = fun z => w0 * gConst v0 * gEv v0 (z - a • ebasis 0) +
      w0 * gConst v0 * gEv v0 (z + a • ebasis 0) + w2 * gConst v2 * gEv v2 z := ⟨_, rfl⟩
  have hg0c : Continuous g0 := by
    rw [hg0]; have := continuous_gEv v0; have := continuous_gEv v2; fun_prop
  have hg0i : Integrable g0 := by
    rw [hg0]
    exact ((((integrable_gEv hv0p).comp_sub_right _).const_mul _).add
      (((integrable_gEv hv0p).comp_add_right _).const_mul _)).add
      ((integrable_gEv hv2p).const_mul _)
  -- the witness and its transform
  obtain ⟨H, hHdef⟩ : ∃ H : Rd d → ℂ, H = fun x => (creationWitness d a δ x : ℂ) := ⟨_, rfl⟩
  have hH : H = fun x => (mconvE (gaussVar d τ) g0 x : ℂ) := by
    rw [hHdef]; funext x; rw [hg0, hrec x]
  have hHc : Continuous H := by
    rw [hHdef]
    have : ∀ i : Fin d, Continuous fun z : Rd d => z i :=
      fun i => (EuclideanSpace.proj i).continuous
    unfold creationWitness
    fun_prop
  have hHi : Integrable H := by rw [hH]; exact integrable_mconvE _ hg0i hg0c
  set N : ℝ := ∫ x, ‖(g0 x : ℂ)‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  have hFb : ∀ ξ, ‖𝓕 H ξ‖ ≤ N * Real.exp (-(2 * Real.pi ^ 2 * τ) * ‖ξ‖ ^ 2) := by
    intro ξ
    rw [hH, fourier_mconvE _ hg0i hg0c, charFun_gaussVar hτ0.le, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
    refine mul_le_mul (norm_fourier_le_integral ξ) (le_of_eq ?_) (Real.exp_pos _).le hN0
    congr 1
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos Real.two_pi_pos]
    ring
  have hFi : Integrable (𝓕 H) :=
    ((integrable_exp_neg_mul_sq_norm_Rd (d := d) (by positivity :
      (0 : ℝ) < 2 * Real.pi ^ 2 * τ)).const_mul N).mono'
      (continuous_fourier_of_integrable hHi).aestronglyMeasurable (Eventually.of_forall hFb)
  -- the deconvolution
  set E : Rd d → ℂ := fun ξ => charFun η (-(2 * Real.pi) • ξ) with hEdef
  have hEc : Continuous E := continuous_charFun.comp (continuous_const_smul _)
  have hEre : ∀ ξ, E ξ = ((E ξ).re : ℂ) := fun ξ =>
    Complex.ext (by simp) (by
      rw [Complex.ofReal_im]
      exact (Complex.pos_iff.1 (hpos (-(2 * Real.pi) • ξ))).2.symm)
  have hEpos : ∀ ξ, 0 < (E ξ).re := fun ξ => (Complex.pos_iff.1 (hpos _)).1
  have hE0 : ∀ ξ, E ξ ≠ 0 := fun ξ h => by
    have := hEpos ξ
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  obtain ⟨C, hC⟩ := hgrowth (τ / 4) (by positivity)
  obtain ⟨φ, hφdef⟩ : ∃ φ : Rd d → ℂ, φ = fun ξ => 𝓕 H ξ / E ξ := ⟨_, rfl⟩
  have hφc : Continuous φ := by
    rw [hφdef]; exact (continuous_fourier_of_integrable hHi).div hEc hE0
  have hφb : ∀ ξ, ‖φ ξ‖ ≤ N * C * Real.exp (-(Real.pi ^ 2 * τ) * ‖ξ‖ ^ 2) := by
    intro ξ
    have hCξ := hC (-(2 * Real.pi) • ξ)
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos Real.two_pi_pos] at hCξ
    rw [hφdef, norm_div, hEre ξ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hEpos ξ),
      div_eq_mul_inv]
    calc ‖𝓕 H ξ‖ * (E ξ).re⁻¹
        ≤ (N * Real.exp (-(2 * Real.pi ^ 2 * τ) * ‖ξ‖ ^ 2)) *
          (C * Real.exp (τ / 4 * (2 * Real.pi * ‖ξ‖) ^ 2)) :=
          mul_le_mul (hFb ξ) hCξ (inv_pos.2 (hEpos ξ)).le (by positivity)
      _ = N * C * Real.exp (-(Real.pi ^ 2 * τ) * ‖ξ‖ ^ 2) := by
          rw [mul_mul_mul_comm, ← Real.exp_add]
          congr 2
          ring
  have hNC : 0 ≤ N * C := by
    have := (norm_nonneg (φ 0)).trans (hφb 0)
    simpa using this
  have hφi : Integrable φ :=
    ((integrable_exp_neg_mul_sq_norm_Rd (d := d) (by positivity :
      (0 : ℝ) < Real.pi ^ 2 * τ)).const_mul (N * C)).mono' hφc.aestronglyMeasurable
      (Eventually.of_forall hφb)
  have hφ2 : MemLp φ 2 := by
    rw [memLp_two_iff_integrable_sq_norm hφc.aestronglyMeasurable]
    refine ((integrable_exp_neg_mul_sq_norm_Rd (d := d) (by positivity :
      (0 : ℝ) < Real.pi ^ 2 * τ)).const_mul ((N * C) * (N * C))).mono'
      (hφc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    have h1 := hφb ξ
    have h2 : Real.exp (-(Real.pi ^ 2 * τ) * ‖ξ‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ Real.pi ^ 2 * τ * ‖ξ‖ ^ 2 := by positivity
      linarith
    have h3 : ‖φ ξ‖ ≤ N * C := h1.trans (mul_le_of_le_one_right hNC h2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq, mul_assoc]
    exact mul_le_mul h3 h1 (norm_nonneg _) hNC
  -- the input
  refine ⟨fun z => (invInt φ z).re, Complex.continuous_re.comp (continuous_invInt hφi),
    ⟨∫ ξ, ‖φ ξ‖, fun x => (Complex.abs_re_le_norm _).trans (norm_invInt_le x)⟩,
    (memLp_two_invInt hφi hφ2).re, fun x => ?_⟩
  change mconvE η (fun z => (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) * Complex.I) * φ ξ).re) x = _
  rw [mconvE_re_fourierInvInt η hφi x]
  have hEφ : ∀ ξ, charFun η (-(2 * Real.pi) • ξ) * φ ξ = 𝓕 H ξ := fun ξ => by
    rw [hφdef]; exact mul_div_cancel₀ _ (hE0 ξ)
  simp_rw [hEφ]
  have hinv := congrFun (Continuous.fourierInv_fourier_eq hHc hHi hFi) x
  rw [Real.fourierInv_eq'] at hinv
  simp only [smul_eq_mul] at hinv
  rw [hinv, hHdef, Complex.ofReal_re]

end Pyramids
