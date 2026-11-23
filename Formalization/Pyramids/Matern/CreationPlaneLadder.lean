/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.CreationPlaneRecords
import Pyramids.Matern.ExpSchwartz
import Pyramids.Matern.FrameMatern
import Pyramids.Matern.MaternPyramid
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# `prop:creation-plane`(3): the Matérn and frame Matérn ladders

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:creation-plane`. Phase 5, wave 3b (on the
VM). `creation_plane_3` and `creation_plane_3_frame` moved here from `PyramidsSkeleton.Ch04Matern`,
their statements unchanged.

* **A Schwartz input.** If `η̂(-2πξ) = e^{-Ψ₀(ξ)}` with `Ψ₀` tempered and `Ψ₀ ≤ ε|ξ|² + A_ε` for
  every `ε > 0`, every `h_{a,δ}` is `η * g` with `g` a real Schwartz function: with
  `h = N(0, τI) * g₀` (`exists_gauss_record`), `g₀` a sum of three Gaussians, each a Schwartz
  function (`exists_schwartz_exp`), `φ := e^{Ψ₀ - 2π²τ|ξ|²} 𝓕g₀` is a Schwartz function (the
  multiplier has temperate growth, `hasTemperateGrowth_exp_comp`), and `g := Re 𝓕⁻φ`. Then
  `η * g = Re 𝓕⁻(η̂(-2π·) φ) = Re 𝓕⁻ 𝓕h = h`.
* **The exponents.** `F_q(s|2πξ|)` is the series `logSeries` at `b = c²s²(2π)²`, of temperate growth
  and below `ε|ξ|² + A_ε` (`ExpSchwartz.lean`); the frame's is a sum of such series along the axes.
* **The steps.** For laws given by their exponent, `μ_{0,t} = μ_{0,s} ∗ μ_{s,t}` (the transforms).
  The Matérn step `μ_{s,qs}` is `L_{cs}` (`lem:bessel-profile`(1)); the frame step is the product of
  `d` copies of the line's `L_{cs}`, absolutely continuous as a product of absolutely continuous
  laws. Clause (1) applies to either.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter FourierTransform SchwartzMap
open ScaleSpace (mconvE)
open scoped Topology RealInnerProductSpace ComplexOrder ContDiff

variable {d : ℕ}

/-! ## Gaussians as Schwartz functions -/

theorem hasTemperateGrowth_proj (i : Fin d) : Function.HasTemperateGrowth fun z : Rd d => z i :=
  (EuclideanSpace.proj i : Rd d →L[ℝ] ℝ).hasTemperateGrowth

/-- `E_v` is a Schwartz function. -/
theorem exists_schwartz_gEv {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) :
    ∃ f : 𝓢(Rd d, ℝ), ∀ z, f z = gEv v z := by
  set M : ℝ := 1 + ∑ i, v i with hMdef
  have hS : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun j _ => (hv j).le
  have hM : ∀ i, v i ≤ M := fun i => by
    have := Finset.single_le_sum (fun j _ => (hv j).le) (Finset.mem_univ i)
    linarith
  have hM0 : 0 < M := by linarith
  have hT : Function.HasTemperateGrowth fun z : Rd d => ∑ i, (-(2 * v i)⁻¹) * z i ^ 2 := by
    have := hasTemperateGrowth_proj (d := d)
    fun_prop
  obtain ⟨f, hf⟩ := exists_schwartz_exp hT (A := 0) (κ := 1 / (2 * M)) (by positivity) fun z => by
    rw [zero_sub, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hv i
    have h1 : z i ^ 2 / (2 * M) ≤ z i ^ 2 / (2 * v i) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hM i])
    rw [neg_mul, neg_le_neg_iff, ← div_eq_inv_mul, one_div_mul_eq_div]
    exact h1
  refine ⟨f, fun z => ?_⟩
  rw [hf, gEv]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_mul, ← div_eq_inv_mul]

/-! ## A Schwartz input for the witness -/

/-- **Every `h_{a,δ}` is `η * g` with `g` a real Schwartz function**, when
`η̂(-2πξ) = e^{-Ψ₀(ξ)}` with `Ψ₀` tempered and `Ψ₀ ≤ ε|ξ|² + A_ε` for every `ε > 0`. -/
theorem exists_schwartz_record [NeZero d] (η : Measure (Rd d)) [IsProbabilityMeasure η]
    {Ψ₀ : Rd d → ℝ} (hΨ : Function.HasTemperateGrowth Ψ₀)
    (hgrow : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ ξ, Ψ₀ ξ ≤ ε * ‖ξ‖ ^ 2 + A)
    (hη : ∀ ξ, charFun η (-(2 * Real.pi) • ξ) = ((Real.exp (-Ψ₀ ξ) : ℝ) : ℂ))
    {a δ : ℝ} (ha : 1 < a) (hδ : 0 < δ) :
    ∃ g : 𝓢(Rd d, ℝ), ∀ x, mconvE η g x = creationWitness d a δ x := by
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
  -- `g₀` is a Schwartz function
  obtain ⟨E0, hE0⟩ := exists_schwartz_gEv hv0p
  obtain ⟨E2, hE2⟩ := exists_schwartz_gEv hv2p
  set G0 : 𝓢(Rd d, ℝ) := (w0 * gConst v0) • compSubConstCLM ℝ (a • ebasis 0) E0 +
    (w0 * gConst v0) • compSubConstCLM ℝ (-(a • ebasis 0)) E0 + (w2 * gConst v2) • E2 with hG0
  have hG0g : ∀ z, G0 z = g0 z := fun z => by
    simp only [hG0, hg0, _root_.add_apply, _root_.smul_apply, compSubConstCLM_apply,
      hE0, hE2, smul_eq_mul, sub_neg_eq_add]
  set G0c : 𝓢(Rd d, ℂ) := postcompCLM (𝕜 := ℝ) Complex.ofRealCLM G0 with hG0c
  have hG0cg : ∀ z, G0c z = (g0 z : ℂ) := fun z => by
    simp [hG0c, hG0g]
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
  have hFH : ∀ ξ, 𝓕 H ξ = (Real.exp (-(2 * Real.pi ^ 2 * τ) * ‖ξ‖ ^ 2) : ℂ) * 𝓕 G0c ξ := by
    intro ξ
    rw [hH, fourier_mconvE _ hg0i hg0c, charFun_gaussVar hτ0.le, SchwartzMap.fourier_coe]
    congr 2
    · congr 1
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos Real.two_pi_pos]
      ring
    · rw [show (fun x => (g0 x : ℂ)) = ⇑G0c from funext fun z => (hG0cg z).symm]
  have hFHi : Integrable (𝓕 H) := by
    have : 𝓕 H = fun ξ => (Real.exp (-(2 * Real.pi ^ 2 * τ) * ‖ξ‖ ^ 2) : ℂ) * 𝓕 G0c ξ :=
      funext hFH
    rw [this]
    refine (𝓕 G0c).integrable.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun ξ => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have : 0 ≤ 2 * Real.pi ^ 2 * τ * ‖ξ‖ ^ 2 := by positivity
    linarith
  -- the multiplier `e^{Ψ₀ - 2π²τ|ξ|²}`
  set κ : ℝ := 2 * Real.pi ^ 2 * τ with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨A, hA⟩ := hgrow κ hκ0
  have hT : Function.HasTemperateGrowth fun ξ : Rd d => Ψ₀ ξ - κ * ‖ξ‖ ^ 2 := by
    have := Function.hasTemperateGrowth_norm_sq (Rd d)
    fun_prop
  have hmT := hasTemperateGrowth_exp_comp hT (A := A) fun ξ => by linarith [hA ξ]
  have hmC : Function.HasTemperateGrowth fun ξ : Rd d =>
      ((Real.exp (Ψ₀ ξ - κ * ‖ξ‖ ^ 2) : ℝ) : ℂ) :=
    Function.Complex.hasTemperateGrowth_ofReal.comp hmT
  set Φ : 𝓢(Rd d, ℂ) := smulLeftCLM ℂ (fun ξ : Rd d => ((Real.exp (Ψ₀ ξ - κ * ‖ξ‖ ^ 2) : ℝ) : ℂ))
    (𝓕 G0c) with hΦ
  have hΦapp : ∀ ξ, Φ ξ = ((Real.exp (Ψ₀ ξ - κ * ‖ξ‖ ^ 2) : ℝ) : ℂ) * 𝓕 G0c ξ := fun ξ => by
    rw [hΦ, smulLeftCLM_apply_apply hmC, smul_eq_mul]
  have hηΦ : ∀ ξ, charFun η (-(2 * Real.pi) • ξ) * Φ ξ = 𝓕 H ξ := fun ξ => by
    rw [hη, hΦapp, hFH, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  -- the input
  set g : 𝓢(Rd d, ℝ) := postcompCLM (𝕜 := ℝ) Complex.reCLM (𝓕⁻ Φ) with hg
  refine ⟨g, fun x => ?_⟩
  have hgapp : (g : Rd d → ℝ) =
      fun z => (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) * Complex.I) * Φ ξ).re := by
    funext z
    simp only [hg, postcompCLM_apply, Complex.reCLM_apply,
      SchwartzMap.fourierInv_coe, Real.fourierInv_eq', smul_eq_mul]
  rw [hgapp, mconvE_re_fourierInvInt η Φ.integrable x]
  simp_rw [hηΦ]
  have hinv := congrFun (Continuous.fourierInv_fourier_eq hHc hHi hFHi) x
  rw [Real.fourierInv_eq'] at hinv
  simp only [smul_eq_mul] at hinv
  rw [hinv, hHdef, Complex.ofReal_re]

/-! ## Laws given by their exponents -/

/-- `μ_{r,t} = μ_{r,s} ∗ μ_{s,t}`: the transforms multiply. -/
theorem exponentLaws_conv {Ψ : ℝ → Rd d → ℝ} {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : IsExponentLaws Ψ μ) {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) :
    μ r t = μ r s ∗ μ s t := by
  haveI := (hμ r t hr (hrs.trans hst)).1
  haveI := (hμ r s hr hrs).1
  haveI := (hμ s t (hr.trans hrs) hst).1
  refine Measure.ext_of_charFun (funext fun w => ?_)
  rw [charFun_conv, (hμ r t hr (hrs.trans hst)).2, (hμ r s hr hrs).2,
    (hμ s t (hr.trans hrs) hst).2, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- **The ladder from one step.** If the step `μ_{s,t}` is absolutely continuous, and
`μ̂_{0,s}(-2πξ) = e^{-Ψ₀(ξ)}` with `Ψ₀` as in `exists_schwartz_record`, some real Schwartz `g`
has a record `μ_{0,s} * g` with one local maximum and `μ_{0,t} * g = μ_{s,t} * (μ_{0,s} * g)` with two. -/
theorem ladder_of_step [NeZero d] (hd : 2 ≤ d) {Ψ : ℝ → Rd d → ℝ} {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : IsExponentLaws Ψ μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hac : μ s t ≪ volume)
    {Ψ₀ : Rd d → ℝ} (hΨ : Function.HasTemperateGrowth Ψ₀)
    (hgrow : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ ξ, Ψ₀ ξ ≤ ε * ‖ξ‖ ^ 2 + A)
    (hη : ∀ ξ, charFun (μ 0 s) (-(2 * Real.pi) • ξ) = ((Real.exp (-Ψ₀ ξ) : ℝ) : ℂ)) :
    ∃ g : 𝓢(Rd d, ℝ), (∃! x, IsLocalMax (mconvE (μ 0 s) g) x) ∧
      (∃ x y, x ≠ y ∧ IsLocalMax (mconvE (μ 0 t) g) x ∧ IsLocalMax (mconvE (μ 0 t) g) y) ∧
      mconvE (μ 0 t) g = mconvE (μ s t) (mconvE (μ 0 s) g) ∧
      ∃ C : ℝ, IsConnected {x | C < mconvE (μ 0 s) g x} ∧
        ¬ IsPreconnected {x | C < mconvE (μ 0 t) g x} := by
  haveI := (hμ s t hs hst).1
  haveI := (hμ 0 s le_rfl hs).1
  obtain ⟨a, δ, ha, hδ, h1, h2, C, hC1, hC2⟩ := creation_plane_1 hd (μ s t) hac
  obtain ⟨g, hg⟩ := exists_schwartz_record (μ 0 s) hΨ hgrow hη ha hδ
  have hrec : mconvE (μ 0 s) g = creationWitness d a δ := funext hg
  have hstep : mconvE (μ 0 t) g = mconvE (μ s t) (mconvE (μ 0 s) g) := by
    funext x
    obtain ⟨B, hB⟩ : ∃ B, ∀ z, |g z| ≤ B :=
      ⟨SchwartzMap.seminorm ℝ 0 0 g, fun z => by
        simpa using SchwartzMap.norm_le_seminorm ℝ g z⟩
    rw [exponentLaws_conv hμ le_rfl hs hst]
    exact mconvE_conv_of_bdd _ _ g.continuous hB x
  refine ⟨g, ?_, ?_, hstep, C, ?_, ?_⟩
  · rw [hrec]; exact h1
  · rw [hstep, hrec]; exact h2
  · rw [hrec]; exact hC1
  · rw [hstep, hrec]; exact hC2

/-! ## The Matérn exponent -/

theorem maternExponent_eq_logSeries {q c s : ℝ} (ξ : Rd d) :
    maternExponent q c (s * (2 * Real.pi * ‖ξ‖)) =
      logSeries q (c ^ 2 * s ^ 2 * (2 * Real.pi) ^ 2) ξ := by
  unfold maternExponent logSeries lsCoeff
  refine tsum_congr fun i => ?_
  congr 2
  rw [div_mul_eq_mul_div]
  ring

theorem maternExponent_abs_eq_logSeries {q c s : ℝ} (y : ℝ) :
    maternExponent q c (s * |(-(2 * Real.pi)) * y|) =
      logSeries q (c ^ 2 * s ^ 2 * (2 * Real.pi) ^ 2) y := by
  unfold maternExponent logSeries lsCoeff
  refine tsum_congr fun i => ?_
  congr 2
  rw [div_mul_eq_mul_div, mul_pow, sq_abs, Real.norm_eq_abs, sq_abs]
  ring

/-! ## The frame step -/

/-- The line's step `L_r` on `ℝ`: the image of `L_r` on `ℝ¹`. -/
noncomputable def lineStep (r : ℝ) : Measure ℝ := (maternStep 1 r).map fun x : Rd 1 => x 0

theorem measurable_coord0 : Measurable fun x : Rd 1 => x 0 :=
  (EuclideanSpace.proj (0 : Fin 1) : Rd 1 →L[ℝ] ℝ).continuous.measurable

theorem lineStep_isProbabilityMeasure {r : ℝ} (hr : 0 < r) : IsProbabilityMeasure (lineStep r) := by
  haveI := (bessel_profile_1 (d := 1) le_rfl hr).1
  exact Measure.isProbabilityMeasure_map measurable_coord0.aemeasurable

theorem charFun_lineStep {r : ℝ} (hr : 0 < r) (y : ℝ) :
    charFun (lineStep r) y = (((1 + r ^ 2 * y ^ 2)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨-, hcf, -⟩ := bessel_profile_1 (d := 1) le_rfl hr
  rw [lineStep, charFun_apply, integral_map measurable_coord0.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  have hin : ∀ x : Rd 1, ⟪x 0, y⟫ = ⟪x, EuclideanSpace.single 0 y⟫ := fun x => by
    rw [EuclideanSpace.inner_single_right]
    simp
  simp_rw [hin, ← charFun_apply, hcf, PiLp.norm_single, Real.norm_eq_abs, sq_abs]

theorem lineStep_ac {r : ℝ} (hr : 0 < r) : lineStep r ≪ volume := by
  obtain ⟨-, -, hden, -⟩ := bessel_profile_1 (d := 1) le_rfl hr
  have hpres : MeasurePreserving (fun x : Rd 1 => x 0) volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))
  rw [lineStep, hden, ← hpres.map_eq]
  exact (withDensity_absolutelyContinuous _ _).map measurable_coord0

/-- A product of absolutely continuous laws is absolutely continuous. -/
theorem pi_absolutelyContinuous :
    ∀ (n : ℕ) (μ ν : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
      (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν
  | 0, μ, ν, _, _, _ => by rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | n + 1, μ, ν, _, _, h => by
    rw [← (MeasurePreserving.symm _ (measurePreserving_piFinSuccAbove μ 0)).map_eq,
      ← (MeasurePreserving.symm _ (measurePreserving_piFinSuccAbove ν 0)).map_eq]
    exact ((h 0).prod (pi_absolutelyContinuous n _ _ fun j => h _)).map
      (MeasurableEquiv.measurable _)

/-- **The frame step**: `d` independent coordinates of law `L_r` on the line. -/
noncomputable def frameStep (d : ℕ) (r : ℝ) : Measure (Rd d) :=
  (Measure.pi fun _ : Fin d => lineStep r).map (WithLp.toLp 2)

theorem frameStep_isProbabilityMeasure {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (frameStep d r) := by
  haveI := lineStep_isProbabilityMeasure hr
  unfold frameStep
  rw [← MeasurableEquiv.coe_toLp]
  exact Measure.isProbabilityMeasure_map (MeasurableEquiv.toLp 2 _).measurable.aemeasurable

theorem charFun_frameStep {r : ℝ} (hr : 0 < r) (w : Rd d) :
    charFun (frameStep d r) w = ((∏ j, (1 + r ^ 2 * w j ^ 2)⁻¹ : ℝ) : ℂ) := by
  haveI := lineStep_isProbabilityMeasure hr
  rw [frameStep, charFun_pi]
  simp_rw [charFun_lineStep hr]
  push_cast
  rfl

theorem frameStep_ac {r : ℝ} (hr : 0 < r) : frameStep d r ≪ volume := by
  haveI := lineStep_isProbabilityMeasure hr
  rw [frameStep, ← (PiLp.volume_preserving_toLp (Fin d)).map_eq]
  rw [← MeasurableEquiv.coe_toLp]
  exact (pi_absolutelyContinuous d _ _ fun _ => lineStep_ac hr).map
    (MeasurableEquiv.toLp 2 _).measurable

/-- The octave step of a frame Matérn pyramid is the frame step. -/
theorem frame_step_eq {q c : ℝ} (hq : 1 < q) (hc : 0 < c) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : IsFrameMaternPyramid q c μ) {s : ℝ} (hs : 0 < s) :
    μ s (q * s) = frameStep d (c * s) := by
  have hle : s ≤ q * s := le_mul_of_one_le_left hs.le hq.le
  haveI := (hμ s (q * s) hs.le hle).1
  haveI := frameStep_isProbabilityMeasure (d := d) (mul_pos hc hs)
  refine Measure.ext_of_charFun (funext fun w => ?_)
  rw [(hμ s (q * s) hs.le hle).2, charFun_frameStep (mul_pos hc hs)]
  congr 1
  have hj : ∀ j, maternExponent q c (q * s * |w j|) - maternExponent q c (s * |w j|) =
      Real.log (1 + (c * s) ^ 2 * w j ^ 2) := by
    intro j
    rw [mul_assoc, maternExponent_mul_q hq hc, mul_pow, sq_abs]
    ring_nf
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_neg_distrib,
    Real.exp_sum, Finset.prod_congr rfl fun j _ => ?_]
  rw [Real.exp_neg, Real.exp_log (by positivity)]

/-! ## The statements -/

/-- **`prop:creation-plane`(3), the Matérn ladder.** For every `s > 0` a real Schwartz `g` has a
record `μ_s * g` with exactly one local maximum and the next record
`μ_{qs} * g = L_{cs} * (μ_s * g)` with at least two; for some level `C`, `μ_s * g - C` has one
positive region and `μ_{qs} * g - C` at least two. -/
theorem creation_plane_3 [NeZero d] (hd : 2 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ) {s : ℝ} (hs : 0 < s) :
    ∃ g : 𝓢(Rd d, ℝ), (∃! x, IsLocalMax (mconvE (μ 0 s) g) x) ∧
      (∃ x y, x ≠ y ∧ IsLocalMax (mconvE (μ 0 (q * s)) g) x ∧
        IsLocalMax (mconvE (μ 0 (q * s)) g) y) ∧
      mconvE (μ 0 (q * s)) g = mconvE (maternStep d (c * s)) (mconvE (μ 0 s) g) ∧
      ∃ C : ℝ, IsConnected {x | C < mconvE (μ 0 s) g x} ∧
        ¬ IsPreconnected {x | C < mconvE (μ 0 (q * s)) g x} := by
  have hd1 : 1 ≤ d := by omega
  have hle : s ≤ q * s := le_mul_of_one_le_left hs.le hq.le
  have hstep := matern_octave_step_d hd1 hq hc hμ hs
  obtain ⟨-, -, hden, -⟩ := bessel_profile_1 hd1 (mul_pos hc hs)
  have hb : 0 ≤ c ^ 2 * s ^ 2 * (2 * Real.pi) ^ 2 := by positivity
  have h := ladder_of_step hd hμ hs.le hle
    (by rw [hstep, hden]; exact withDensity_absolutelyContinuous _ _)
    (hasTemperateGrowth_logSeries hq hb) (fun ε hε => logSeries_le hq hb hε)
    (fun ξ => by rw [charFun_maternPyramid_neg hμ hs.le, maternExponent_eq_logSeries])
  rwa [hstep] at h

/-- **`prop:creation-plane`(3), the frame Matérn ladder.** The same for the frame Matérn pyramid. -/
theorem creation_plane_3_frame [NeZero d] (hd : 2 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsFrameMaternPyramid q c μ) {s : ℝ} (hs : 0 < s) :
    ∃ g : 𝓢(Rd d, ℝ), (∃! x, IsLocalMax (mconvE (μ 0 s) g) x) ∧
      (∃ x y, x ≠ y ∧ IsLocalMax (mconvE (μ 0 (q * s)) g) x ∧
        IsLocalMax (mconvE (μ 0 (q * s)) g) y) ∧
      ∃ C : ℝ, IsConnected {x | C < mconvE (μ 0 s) g x} ∧
        ¬ IsPreconnected {x | C < mconvE (μ 0 (q * s)) g x} := by
  have hle : s ≤ q * s := le_mul_of_one_le_left hs.le hq.le
  have hstep := frame_step_eq hq hc hμ hs
  have hb : 0 ≤ c ^ 2 * s ^ 2 * (2 * Real.pi) ^ 2 := by positivity
  set b := c ^ 2 * s ^ 2 * (2 * Real.pi) ^ 2 with hbdef
  have hT : Function.HasTemperateGrowth fun ξ : Rd d => ∑ j, logSeries q b (ξ j) :=
    Function.HasTemperateGrowth.sum fun j _ =>
      (hasTemperateGrowth_logSeries hq hb).comp (hasTemperateGrowth_proj j)
  have hgrow : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ,
      ∀ ξ : Rd d, ∑ j, logSeries q b (ξ j) ≤ ε * ‖ξ‖ ^ 2 + A := by
    intro ε hε
    obtain ⟨A, hA⟩ := logSeries_le (F := ℝ) hq hb hε
    refine ⟨d * A, fun ξ => ?_⟩
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    calc ∑ j, logSeries q b (ξ j) ≤ ∑ j : Fin d, (ε * ξ j ^ 2 + A) :=
          Finset.sum_le_sum fun j _ => by
            have := hA (ξ j); rwa [Real.norm_eq_abs, sq_abs] at this
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  obtain ⟨g, h1, h2, -, hC⟩ := ladder_of_step hd hμ hs.le hle
    (by rw [hstep]; exact frameStep_ac (mul_pos hc hs))
    hT hgrow
    (fun ξ => by
      rw [(hμ 0 s le_rfl hs.le).2]
      congr 3
      simp only [zero_mul, maternExponent_zero, Finset.sum_const_zero, sub_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← maternExponent_abs_eq_logSeries]
      rfl)
  exact ⟨g, h1, h2, hC⟩

end Pyramids
