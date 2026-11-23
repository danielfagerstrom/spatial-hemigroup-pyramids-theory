/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Matern
import AffineHemigroup.MaternLaw
import AffineHemigroup.MaternKernel
import AffineHemigroup.PositiveTransform
import AffineHemigroup.Subordination
import ScaleSpaceCore.L1OperatorsSpace
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# `lem:bessel-profile`: the octave step and its profile

Blueprint: `blueprint/src/parts/04-matern.tex`, `lem:bessel-profile`. Phase 5, wave 1c.

* **(1), the law.** `L_r` is `gammaGaussLaw d 1` dilated by `r`. The affine export gives its
  transform (`gammaGaussLaw_transform`) and its density `G` (`maternLaw_eq_withDensity`), and
  `map_smul_withDensity` carries the density through the dilation. `G` agrees with the lower
  integral `maternGreenE` off the origin, where its integrand is integrable
  (`integrableOn_maternLap`), and it is smooth there (`contDiffOn_maternGreen`).
* **(1), the Green's function.** The test function is read as a complex Schwartz function `φ`.
  Mathlib's `laplacian_eq_fourierMultiplierCLM` writes `φ - r²Δφ` as the inverse transform of
  `(1 + 4π²r²|ξ|²)𝓕φ`. Integrating that inverse transform against `L_r` (Fubini) multiplies its
  integrand by `L̂_r(2πξ) = (1 + 4π²r²|ξ|²)⁻¹`, so `∫ (φ - r²Δφ)(z + y) L_r(dy) = φ(z)`
  (`helmholtz_fourier_key`). Fubini twice moves `L_r` from `g` to the test function
  (`helmholtz_green`).
* **(2).** Frullani's integral (the affine export's `lintegral_frullani`) gives
  `log(1 + βu) = ∫₀^∞ (1 - e^{-su}) e^{-s/β} ds/s`; the Gaussian `g_{2s}` has
  `∫ (1 - cos⟨ω,x⟩) g_{2s} = 1 - e^{-s|ω|²}` (`lintegral_one_sub_cos_heat`); Tonelli exchanges the
  integrals; and the substitution `s = |x|²/(4v)` turns `∫₀^∞ g_{2s}(x) e^{-s/β} ds/s` into
  `b_d(|x|/√β)/(|S^{d-1}||x|^d)` (`polar_density_eq_lintegral`).
* **(3).** Dominated convergence with the bound `v^{d/2-1}e^{-v}`, the strict monotonicity of the
  integrand in `y`, and `v/2 + y²/(4v) ≥ y/2`. For the closed forms: the substitution `v = w²`,
  then `w ↦ η/w` and `σ = w - η/w` (`J₁ = J₂`, `J₁ + J₂ = √π`), and one integration by parts
  against `w e^{-w² - η²/w²}` for `b_3`.
-/

namespace Pyramids

open AffineHemigroup MeasureTheory Set Filter SchwartzMap FourierTransform Laplacian
open scoped Topology ENNReal SchwartzMap RealInnerProductSpace

variable {d : ℕ}


theorem helmholtz_fourier_key {r : ℝ} (L : Measure (Rd d)) [IsFiniteMeasure L]
    (hL : ∀ ξ, charFun L ξ = (((1 + r ^ 2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) (φ : 𝓢(Rd d, ℂ)) (z : Rd d) :
    ∫ y, (φ (z + y) - ((r ^ 2 : ℝ) : ℂ) * Δ (φ : Rd d → ℂ) (z + y)) ∂L = φ z := by
  have hn : (fun ξ : Rd d => ‖ξ‖ ^ 2).HasTemperateGrowth := by fun_prop
  set F : 𝓢(Rd d, ℂ) := 𝓕 φ with hF
  set S : 𝓢(Rd d, ℂ) := smulLeftCLM ℂ (fun ξ : Rd d => ‖ξ‖ ^ 2) F with hS
  set c : ℝ := r ^ 2 * (2 * Real.pi) ^ 2 with hc
  set H : 𝓢(Rd d, ℂ) := F + c • S with hH
  have hΔ : Δ φ = -(2 * Real.pi) ^ 2 • 𝓕⁻ S := by
    rw [laplacian_eq_fourierMultiplierCLM, fourierMultiplierCLM_apply]
  have hrep : ∀ x, φ x - ((r ^ 2 : ℝ) : ℂ) * Δ (φ : Rd d → ℂ) x = 𝓕⁻ (H : Rd d → ℂ) x := by
    intro x
    rw [← laplacian_apply, ← fourierInv_coe, hH, FourierTransform.fourierInv_add,
      FourierTransform.fourierInv_smul, hF, FourierPair.fourierInv_fourier_eq, hΔ]
    simp only [add_apply, smul_apply, hc]
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hHapply : ∀ ξ, H ξ = ((1 + c * ‖ξ‖ ^ 2 : ℝ) : ℂ) * F ξ := by
    intro ξ
    simp only [hH, add_apply, smul_apply, hS,
      smulLeftCLM_apply_apply hn]
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  simp_rw [hrep, Real.fourierInv_eq']
  have hint : Integrable (Function.uncurry fun (y : Rd d) (v : Rd d) =>
      Complex.exp (↑(2 * Real.pi * ⟪v, z + y⟫) * Complex.I) • H v) (L.prod volume) := by
    refine Integrable.mono' ((H.integrable (μ := volume)).norm.comp_snd L) ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by
        have := H.continuous
        fun_prop))
    · exact Eventually.of_forall fun p => by
        simp only [Function.uncurry, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  rw [integral_integral_swap hint]
  have hinner : ∀ v : Rd d, ∫ y, Complex.exp (↑(2 * Real.pi * ⟪v, z + y⟫) * Complex.I) • H v ∂L =
      Complex.exp (↑(2 * Real.pi * ⟪v, z⟫) * Complex.I) • F v := by
    intro v
    rw [integral_smul_const]
    have h1 : ∫ y, Complex.exp (↑(2 * Real.pi * ⟪v, z + y⟫) * Complex.I) ∂L =
        Complex.exp (↑(2 * Real.pi * ⟪v, z⟫) * Complex.I) * charFun L ((2 * Real.pi) • v) := by
      rw [charFun_apply, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      rw [← Complex.exp_add]
      congr 1
      rw [inner_add_right, real_inner_smul_right, real_inner_comm v y]
      push_cast
      ring
    rw [h1, hL, hHapply, smul_eq_mul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_pos Real.two_pi_pos]
    have hpos : (0 : ℝ) < 1 + r ^ 2 * (2 * Real.pi * ‖v‖) ^ 2 := by positivity
    have hc' : (1 + c * ‖v‖ ^ 2 : ℝ) = 1 + r ^ 2 * (2 * Real.pi * ‖v‖) ^ 2 := by rw [hc]; ring
    rw [hc', mul_assoc, ← mul_assoc ((_ : ℝ) : ℂ), ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne',
      Complex.ofReal_one, one_mul]
  simp_rw [hinner]
  rw [← Real.fourierInv_eq', hF, ← fourierInv_coe, FourierPair.fourierInv_fourier_eq]


/-- The real test function `φ`, read as a complex Schwartz function. -/
noncomputable def realTestSchwartz {φ : Rd d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) : 𝓢(Rd d, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => (φ x : ℂ))
    (hφc.comp_left Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp hφ)

theorem realTestSchwartz_apply {φ : Rd d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (x : Rd d) : realTestSchwartz hφ hφc x = (φ x : ℂ) := rfl

theorem laplacian_realTestSchwartz {φ : Rd d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (x : Rd d) :
    Δ (realTestSchwartz hφ hφc : Rd d → ℂ) x = (Δ φ x : ℂ) := by
  have h2 : ContDiffAt ℝ 2 φ x := (hφ.contDiffAt (x := x)).of_le (by
    exact WithTop.coe_le_coe.2 le_top)
  exact h2.laplacian_CLM_comp_left (l := Complex.ofRealCLM)

/-- **The fundamental identity of `I - r²Δ`** against `L` with `L̂ = (1 + r²|ω|²)⁻¹`, for a real
smooth compactly supported `φ`: `∫ (φ - r²Δφ)(z + y) L(dy) = φ(z)`. -/
theorem helmholtz_key_real {r : ℝ} (L : Measure (Rd d)) [IsFiniteMeasure L]
    (hL : ∀ ξ, charFun L ξ = (((1 + r ^ 2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) {φ : Rd d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (z : Rd d) :
    ∫ y, (φ (z + y) - r ^ 2 * Δ φ (z + y)) ∂L = φ z := by
  have h := helmholtz_fourier_key L hL (realTestSchwartz hφ hφc) z
  simp_rw [laplacian_realTestSchwartz, realTestSchwartz_apply] at h
  have h' : ∫ y, ((φ (z + y) - r ^ 2 * Δ φ (z + y) : ℝ) : ℂ) ∂L = (φ z : ℂ) := by
    rw [← h]
    congr 1
    funext y
    push_cast
    ring
  rw [integral_complex_ofReal] at h'
  exact_mod_cast h'

/-- `φ - r²Δφ` is bounded, being a Schwartz function. -/
theorem bdd_helmholtz_test {r : ℝ} {φ : Rd d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    Continuous (fun x => φ x - r ^ 2 * Δ φ x) ∧ ∃ C, ∀ x, ‖φ x - r ^ 2 * Δ φ x‖ ≤ C := by
  set Ψ : 𝓢(Rd d, ℂ) :=
    realTestSchwartz hφ hφc - ((r ^ 2 : ℝ) : ℂ) • Δ (realTestSchwartz hφ hφc) with hΨ
  have hΨx : ∀ x, Ψ x = ((φ x - r ^ 2 * Δ φ x : ℝ) : ℂ) := by
    intro x
    rw [hΨ, sub_apply, smul_apply, laplacian_apply, laplacian_realTestSchwartz,
      realTestSchwartz_apply]
    push_cast
    rw [smul_eq_mul]
  have hfun : (fun x => φ x - r ^ 2 * Δ φ x) = fun x => (Ψ x).re := by
    funext x
    rw [hΨx, Complex.ofReal_re]
  refine ⟨by rw [hfun]; exact Complex.continuous_re.comp Ψ.continuous, ?_⟩
  obtain ⟨C, -, hC⟩ := Ψ.decay 0 0
  refine ⟨C, fun x => ?_⟩
  have := hC x
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at this
  rw [hΨx, Complex.norm_real] at this
  exact this


/-- **The distributional identity for `L`**: `∫ (L * g)(φ - r²Δφ) = ∫ g φ`. -/
theorem helmholtz_green {r : ℝ} (L : Measure (Rd d)) [IsFiniteMeasure L]
    (hL : ∀ ξ, charFun L ξ = (((1 + r ^ 2 * ‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ)) (g : Rd d → ℝ)
    (hg : Integrable g) (φ : Rd d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, ScaleSpace.mconvE L g x * (φ x - r ^ 2 * Δ φ x) = ∫ x, g x * φ x := by
  obtain ⟨hψc, C, hC⟩ := bdd_helmholtz_test (r := r) hφ hφc
  set ψ := fun x => φ x - r ^ 2 * Δ φ x with hψ
  have h1 := ScaleSpace.integrable_uncurry_subE L hg.1 hg
  have hI1 : Integrable (Function.uncurry fun x y : Rd d => g (x - y) * ψ x) (volume.prod L) :=
    h1.mul_bdd (hψc.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => hC p.1)
  have hI2 : Integrable (Function.uncurry fun y x : Rd d => g x * ψ (x + y)) (L.prod volume) :=
    (hg.comp_snd L).mul_bdd (hψc.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable
      (Eventually.of_forall fun p => hC _)
  calc ∫ x, ScaleSpace.mconvE L g x * ψ x
      = ∫ x, ∫ y, g (x - y) * ψ x ∂L := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [ScaleSpace.mconvE_apply]
        rw [integral_mul_const]
    _ = ∫ y, ∫ x, g (x - y) * ψ x ∂volume ∂L := integral_integral_swap hI1
    _ = ∫ y, ∫ x, g x * ψ (x + y) ∂volume ∂L := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        have := integral_sub_right_eq_self (μ := (volume : Measure (Rd d)))
          (fun x => g x * ψ (x + y)) y
        simp only [sub_add_cancel] at this
        exact this
    _ = ∫ x, ∫ y, g x * ψ (x + y) ∂L := integral_integral_swap hI2
    _ = ∫ x, g x * φ x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [integral_const_mul]
        congr 1
        have := helmholtz_key_real L hL hφ hφc x
        exact this



theorem charFun_maternStep (r : ℝ) (ω : Rd d) :
    IsProbabilityMeasure (maternStep d r) ∧
      charFun (maternStep d r) ω = (((1 + r ^ 2 * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨hp, hc⟩ := gammaGaussLaw_transform (d := d) 1 one_pos
  refine ⟨Measure.isProbabilityMeasure_map (measurable_const_smul r).aemeasurable, ?_⟩
  rw [maternStep, charFun_map_smul, hc, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.rpow_neg_one]

theorem integrand_maternGreen_eq (x : Rd d) (s : ℝ) :
    Real.exp (-s) * (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / (4 * s)) =
      Real.exp (-s) * ((4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / (4 * s))) := by
  ring

theorem integrableOn_maternGreen_integrand {x : Rd d} (hx : x ≠ 0) :
    IntegrableOn (fun s : ℝ => Real.exp (-s) * (4 * Real.pi * s) ^ (-(d : ℝ) / 2) *
      Real.exp (-(‖x‖ ^ 2) / (4 * s))) (Ioi 0) := by
  have hc : 0 < ‖x‖ ^ 2 := by positivity
  have h : IntegrableOn (fun s : ℝ => (4 * Real.pi) ^ (-(d : ℝ) / 2) *
      (Real.exp (-s) * s ^ (-(d : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / (4 * s)))) (Ioi 0) :=
    (integrableOn_maternLap (-(d : ℝ) / 2) hc).const_mul _
  refine IntegrableOn.congr_fun h (fun s (hs : 0 < s) => ?_) measurableSet_Ioi
  rw [Real.mul_rpow (by positivity) hs.le]
  ring

theorem maternGreenE_eq_ofReal {x : Rd d} (hx : x ≠ 0) :
    maternGreenE d x = ENNReal.ofReal (maternGreen d x) := by
  rw [maternGreenE, maternGreen, ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [integrand_maternGreen_eq]
  · refine (integrableOn_maternGreen_integrand hx).congr_fun (fun s _ => ?_) measurableSet_Ioi
    exact integrand_maternGreen_eq x s
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s (hs : 0 < s) => ?_)
    positivity

theorem maternGreenE_pos (x : Rd d) : 0 < maternGreenE d x := by
  rw [maternGreenE, lintegral_pos_iff_support (by fun_prop)]
  have : Function.support (fun s : ℝ => ENNReal.ofReal (Real.exp (-s) *
      (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / (4 * s)))) ∩ Ioi 0 = Ioi 0 := by
    refine inter_eq_right.2 fun s (hs : 0 < s) => ?_
    rw [Function.mem_support, ENNReal.ofReal_ne_zero_iff]
    positivity
  rw [Measure.restrict_apply' measurableSet_Ioi, this, Real.volume_Ioi]
  simp


theorem map_smul_withDensity {r : ℝ} (hr : 0 < r) {f : Rd d → ℝ≥0∞} (hf : Measurable f) :
    (volume.withDensity f).map (fun x => r • x) =
      volume.withDensity (fun x => ENNReal.ofReal (r ^ (-(d : ℝ))) * f (r⁻¹ • x)) := by
  have hsm : Measurable fun x : Rd d => r • x := measurable_const_smul r
  have hpos : (0 : ℝ) < r ^ d := pow_pos hr d
  have hrp : r ^ (-(d : ℝ)) = (r ^ d)⁻¹ := by rw [Real.rpow_neg hr.le, Real.rpow_natCast]
  rw [hrp]
  ext s hs
  rw [Measure.map_apply hsm hs, withDensity_apply _ (hsm hs), withDensity_apply _ hs]
  set G : Rd d → ℝ≥0∞ := s.indicator fun x => ENNReal.ofReal (r ^ d)⁻¹ * f (r⁻¹ • x) with hG
  have hGm : Measurable G := (measurable_const.mul (hf.comp (measurable_const_smul _))).indicator hs
  have hmap := Measure.map_addHaar_smul (volume : Measure (Rd d)) hr.ne'
  rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.2 hpos)] at hmap
  have h1 : ∫⁻ x, G x ∂(Measure.map (fun x : Rd d => r • x) volume) =
      ∫⁻ y, G (r • y) := lintegral_map hGm hsm
  rw [hmap, lintegral_smul_measure] at h1
  have hGr : ∀ y, G (r • y) =
      ENNReal.ofReal (r ^ d)⁻¹ * ((fun x : Rd d => r • x) ⁻¹' s).indicator f y := by
    intro y
    by_cases hy : r • y ∈ s
    · have hy' : y ∈ (fun x : Rd d => r • x) ⁻¹' s := hy
      rw [hG, Set.indicator_of_mem hy, Set.indicator_of_mem hy', smul_smul,
        inv_mul_cancel₀ hr.ne', one_smul]
    · have hy' : y ∉ (fun x : Rd d => r • x) ⁻¹' s := hy
      rw [hG, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy', mul_zero]
  simp_rw [hGr] at h1
  rw [lintegral_const_mul _ (hf.indicator (hsm hs))] at h1
  rw [← lintegral_indicator (hsm hs), ← lintegral_indicator hs]
  change _ = ∫⁻ x, G x
  have h0 : ENNReal.ofReal (r ^ d)⁻¹ ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  exact ((ENNReal.mul_right_inj h0 ENNReal.ofReal_ne_top).1 h1).symm


/-! ## The statements of `lem:bessel-profile` -/

/-- **`lem:bessel-profile`(1), the law.** `L_r` is a probability measure with
`L̂_r(ω) = (1 + r²|ω|²)⁻¹` and the density `r^{-d} G(x/r)`; `G` is positive, finite off the
origin, and continuous on `ℝ^d ∖ {0}`. -/
theorem bessel_profile_1 (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (maternStep d r) ∧
      (∀ ω : Rd d, charFun (maternStep d r) ω = (((1 + r ^ 2 * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ)) ∧
      maternStep d r = volume.withDensity (maternDensityE d r) ∧
      (∀ x : Rd d, 0 < maternGreenE d x) ∧ (∀ x : Rd d, x ≠ 0 → maternGreenE d x ≠ ⊤) ∧
      ContinuousOn (fun x : Rd d => (maternGreenE d x).toReal) {0}ᶜ := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  refine ⟨(charFun_maternStep r 0).1, fun ω => (charFun_maternStep r ω).2, ?_, maternGreenE_pos,
    fun x hx => by rw [maternGreenE_eq_ofReal hx]; exact ENNReal.ofReal_ne_top, ?_⟩
  · obtain ⟨hp, hc⟩ := gammaGaussLaw_transform (d := d) 1 one_pos
    have hG := maternLaw_eq_withDensity (d := d) ⟨hp, hc⟩
    rw [maternStep, hG, map_smul_withDensity hr measurable_maternGreen.ennreal_ofReal]
    refine withDensity_congr_ae ?_
    have hnull : (volume : Measure (Rd d)) {0} = 0 := measure_singleton 0
    filter_upwards [compl_mem_ae_iff.2 hnull] with x hx
    have hx0 : r⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero hr.ne') hx
    rw [maternDensityE, maternGreenE_eq_ofReal hx0]
  · refine (contDiffOn_maternGreen (d := d)).continuousOn.congr fun x hx => ?_
    rw [maternGreenE_eq_ofReal hx, ENNReal.toReal_ofReal (maternGreen_nonneg x)]



/-- The integrand `v^{d/2-1} e^{-v - y²/(4v)}` of `b_d`. -/
theorem besselProfile_integrand_le {s y v : ℝ} (hv : 0 < v) :
    ‖v ^ (s - 1) * Real.exp (-v - y ^ 2 / (4 * v))‖ ≤ Real.exp (-v) * v ^ (s - 1) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
  have : 0 ≤ y ^ 2 / (4 * v) := by positivity
  linarith

theorem integrableOn_besselProfile {s : ℝ} (hs : 0 < s) (y : ℝ) :
    IntegrableOn (fun v : ℝ => v ^ (s - 1) * Real.exp (-v - y ^ 2 / (4 * v))) (Ioi 0) := by
  refine Integrable.mono' (Real.GammaIntegral_convergent hs) ?_ ?_
  · exact (by fun_prop : Measurable fun v : ℝ =>
      v ^ (s - 1) * Real.exp (-v - y ^ 2 / (4 * v))).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv =>
      besselProfile_integrand_le hv)


theorem besselProfile_zero (hd : 1 ≤ d) : besselProfile d 0 = 2 := by
  have hs : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [besselProfile]
  have h : ∫ v in Ioi (0 : ℝ), v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - (0 : ℝ) ^ 2 / (4 * v)) =
      Real.Gamma ((d : ℝ) / 2) := by
    rw [Real.Gamma_eq_integral hs]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero]
    ring
  rw [h, div_mul_cancel₀ _ (Real.Gamma_pos_of_pos hs).ne']

theorem continuous_besselProfile (hd : 1 ≤ d) : Continuous (besselProfile d) := by
  have hs : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine Continuous.mul continuous_const ?_
  refine continuous_of_dominated (bound := fun v => Real.exp (-v) * v ^ ((d : ℝ) / 2 - 1)) ?_ ?_
    (Real.GammaIntegral_convergent hs) ?_
  · exact fun y => (by fun_prop : Measurable fun v : ℝ =>
      v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - y ^ 2 / (4 * v))).aestronglyMeasurable
  · exact fun y => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv =>
      besselProfile_integrand_le hv)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : 0 < v) => ?_)
    have : (4 * v) ≠ 0 := by positivity
    fun_prop (disch := assumption)

theorem besselProfile_strictAntiOn (hd : 1 ≤ d) : StrictAntiOn (besselProfile d) (Ici 0) := by
  have hs : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  intro y hy y' hy' hyy'
  simp only [mem_Ici] at hy hy'
  rw [besselProfile, besselProfile]
  refine mul_lt_mul_of_pos_left ?_ (div_pos two_pos (Real.Gamma_pos_of_pos hs))
  rw [← sub_pos, ← integral_sub (integrableOn_besselProfile hs y)
    (integrableOn_besselProfile hs y')]
  have hpos : ∀ v ∈ Ioi (0 : ℝ), 0 < v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - y ^ 2 / (4 * v)) -
      v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - y' ^ 2 / (4 * v)) := by
    intro v (hv : 0 < v)
    rw [← mul_sub]
    refine mul_pos (by positivity) (sub_pos.2 (Real.exp_lt_exp.2 ?_))
    have : y ^ 2 < y' ^ 2 := by nlinarith
    have h4 : 0 < 4 * v := by positivity
    have : y ^ 2 / (4 * v) < y' ^ 2 / (4 * v) := div_lt_div_of_pos_right this h4
    linarith
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun v : ℝ => v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - y ^ 2 / (4 * v)) -
        v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - y' ^ 2 / (4 * v))) ∩ Ioi 0 = Ioi 0 :=
      inter_eq_right.2 fun v hv => (hpos v hv).ne'
    rw [this, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => (hpos v hv).le)
  · exact (integrableOn_besselProfile hs y).sub (integrableOn_besselProfile hs y')

theorem besselProfile_le (hd : 1 ≤ d) (y : ℝ) :
    besselProfile d y ≤ (2 : ℝ) ^ (1 + (d : ℝ) / 2) * Real.exp (-y / 2) := by
  have hs : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hΓ := Real.Gamma_pos_of_pos hs
  have hint2 : IntegrableOn (fun v : ℝ => Real.exp (-y / 2) *
      (v ^ ((d : ℝ) / 2 - 1) * Real.exp (-((1 / 2) * v)))) (Ioi 0) := by
    refine Integrable.const_mul ?_ _
    have h2 := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (d : ℝ) / 2 - 1)
      (by linarith) le_rfl (b := 1 / 2) (by norm_num))
    simp only [Real.rpow_one, neg_mul] at h2
    exact h2
  have hle : ∫ v in Ioi (0 : ℝ), v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - y ^ 2 / (4 * v)) ≤
      ∫ v in Ioi (0 : ℝ),
        Real.exp (-y / 2) * (v ^ ((d : ℝ) / 2 - 1) * Real.exp (-((1 / 2) * v))) := by
    refine setIntegral_mono_on (integrableOn_besselProfile hs y) hint2 measurableSet_Ioi
      fun v (hv : 0 < v) => ?_
    rw [mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have h4 : 0 < 4 * v := by positivity
    rw [show -v - y ^ 2 / (4 * v) = -(4 * v ^ 2 + y ^ 2) / (4 * v) by field_simp; ring,
      show -y / 2 + -(1 / 2 * v) = -(2 * y * v + 2 * v ^ 2) / (4 * v) by field_simp; ring]
    rw [div_le_div_iff_of_pos_right h4]
    nlinarith [sq_nonneg (v - y)]
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by norm_num)] at hle
  rw [besselProfile]
  calc 2 / Real.Gamma ((d : ℝ) / 2) *
        ∫ v in Ioi (0 : ℝ), v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - y ^ 2 / (4 * v))
      ≤ 2 / Real.Gamma ((d : ℝ) / 2) *
        (Real.exp (-y / 2) * ((1 / (1 / 2)) ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (2 : ℝ) ^ (1 + (d : ℝ) / 2) * Real.exp (-y / 2) := by
        rw [Real.rpow_add two_pos, Real.rpow_one]
        norm_num
        field_simp



/-- `w ↦ w - η/w` maps `(0,∞)` onto `ℝ`. -/
theorem image_sub_div_Ioi {η : ℝ} (hη : 0 < η) : (fun w : ℝ => w - η / w) '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun t => ?_
  set q := Real.sqrt (t ^ 2 + 4 * η) with hq
  have hs : q ^ 2 = t ^ 2 + 4 * η := Real.sq_sqrt (by positivity)
  have h1 : Real.sqrt (t ^ 2) < q := Real.sqrt_lt_sqrt (sq_nonneg t) (by linarith)
  rw [Real.sqrt_sq_eq_abs] at h1
  have hpos : 0 < (t + q) / 2 := by linarith [neg_le_abs t]
  refine ⟨(t + q) / 2, hpos, ?_⟩
  have hw : (t + q) / 2 ≠ 0 := hpos.ne'
  have key : (t + q) / 2 * ((t + q) / 2) - t * ((t + q) / 2) - η = 0 := by nlinarith [hs]
  change (t + q) / 2 - η / ((t + q) / 2) = t
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', eq_div_iff hw]
  linarith

theorem image_const_div_Ioi {η : ℝ} (hη : 0 < η) : (fun w : ℝ => η / w) '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩; exact div_pos hη hw
  · intro hu; exact ⟨η / u, div_pos hη hu, by simp only; field_simp⟩

theorem image_sq_Ioi : (fun w : ℝ => w ^ 2) '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩; exact pow_pos (mem_Ioi.1 hw) 2
  · intro hu; exact ⟨Real.sqrt u, Real.sqrt_pos.2 hu, Real.sq_sqrt (le_of_lt hu)⟩

/-- `J₁ = J₂`: the substitution `w ↦ η/w`. -/
theorem integral_J_swap {η : ℝ} (hη : 0 < η) :
    ∫ w in Ioi 0, Real.exp (-(w - η / w) ^ 2) =
      ∫ w in Ioi 0, η / w ^ 2 * Real.exp (-(w - η / w) ^ 2) := by
  have hder : ∀ w ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun w : ℝ => η / w) (-η / w ^ 2) (Ioi 0) w :=
    fun w (hw : 0 < w) => by
      have := (hasDerivAt_inv hw.ne').const_mul η
      have h2 : (fun w : ℝ => η / w) = fun y => η * y⁻¹ := funext fun y => div_eq_mul_inv _ _
      rw [h2, show -η / w ^ 2 = η * -(w ^ 2)⁻¹ by ring]
      exact this.hasDerivWithinAt
  have hinj : InjOn (fun w : ℝ => η / w) (Ioi 0) := fun a (ha : 0 < a) b (hb : 0 < b) h => by
    simp only at h
    field_simp at h
    nlinarith [h]
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj
    (fun u => Real.exp (-(u - η / u) ^ 2))
  rw [image_const_div_Ioi hη] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) => ?_
  simp only [smul_eq_mul]
  have hneg : -η / w ^ 2 < 0 := by
    have : 0 < η / w ^ 2 := by positivity
    rw [neg_div]; linarith
  rw [abs_of_neg hneg, neg_div, neg_neg]
  congr 2
  field_simp
  ring


/-- `J₁ + J₂ = √π`: the substitution `σ = w - η/w`, and the integrability of both. -/
theorem integral_J_sum {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun w : ℝ => Real.exp (-(w - η / w) ^ 2)) (Ioi 0) ∧
      IntegrableOn (fun w : ℝ => η / w ^ 2 * Real.exp (-(w - η / w) ^ 2)) (Ioi 0) ∧
      (∫ w in Ioi 0, Real.exp (-(w - η / w) ^ 2)) +
        (∫ w in Ioi 0, η / w ^ 2 * Real.exp (-(w - η / w) ^ 2)) = Real.sqrt Real.pi := by
  have hder : ∀ w ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun w : ℝ => w - η / w) (1 + η / w ^ 2) (Ioi 0) w :=
    fun w (hw : 0 < w) => by
      have := (hasDerivAt_id w).sub ((hasDerivAt_inv hw.ne').const_mul η)
      have h2 : (fun w : ℝ => w - η / w) = fun y => id y - η * y⁻¹ :=
        funext fun y => by rw [div_eq_mul_inv]; rfl
      rw [h2, show 1 + η / w ^ 2 = 1 - η * -(w ^ 2)⁻¹ by ring]
      exact this.hasDerivWithinAt
  have hmono : StrictMonoOn (fun w : ℝ => w - η / w) (Ioi 0) := by
    intro a (ha : 0 < a) b (hb : 0 < b) hab
    simp only
    have : η / b < η / a := div_lt_div_of_pos_left hη ha hab
    linarith
  have hg : Integrable (fun u : ℝ => Real.exp (-u ^ 2)) := by
    have := integrable_exp_neg_mul_sq (b := 1) one_pos
    simpa using this
  have hI := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder
    hmono.injOn (fun u : ℝ => Real.exp (-u ^ 2))).1
      (by rw [image_sub_div_Ioi hη]; exact hg.integrableOn)
  have hEq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hmono.injOn
    (fun u : ℝ => Real.exp (-u ^ 2))
  rw [image_sub_div_Ioi hη, Measure.restrict_univ] at hEq
  have habs : ∀ w ∈ Ioi (0 : ℝ), |1 + η / w ^ 2| • Real.exp (-(w - η / w) ^ 2) =
      Real.exp (-(w - η / w) ^ 2) + η / w ^ 2 * Real.exp (-(w - η / w) ^ 2) := by
    intro w (hw : 0 < w)
    rw [abs_of_pos (by positivity), smul_eq_mul]
    ring
  have hI' : IntegrableOn (fun w : ℝ => Real.exp (-(w - η / w) ^ 2) +
      η / w ^ 2 * Real.exp (-(w - η / w) ^ 2)) (Ioi 0) :=
    IntegrableOn.congr_fun hI habs measurableSet_Ioi
  have hJ1 : IntegrableOn (fun w : ℝ => Real.exp (-(w - η / w) ^ 2)) (Ioi 0) := by
    refine Integrable.mono' hI' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun w (hw : 0 < w) => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : 0 ≤ η / w ^ 2 * Real.exp (-(w - η / w) ^ 2) := by positivity
    linarith
  have hJ2 : IntegrableOn (fun w : ℝ => η / w ^ 2 * Real.exp (-(w - η / w) ^ 2)) (Ioi 0) := by
    have := hI'.sub hJ1
    refine this.congr_fun (fun w _ => ?_) measurableSet_Ioi
    simp
  refine ⟨hJ1, hJ2, ?_⟩
  rw [← integral_add hJ1 hJ2, ← setIntegral_congr_fun measurableSet_Ioi habs, ← hEq]
  have := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at this
  exact this

theorem integral_J_eq {η : ℝ} (hη : 0 < η) :
    ∫ w in Ioi 0, Real.exp (-(w - η / w) ^ 2) = Real.sqrt Real.pi / 2 ∧
      ∫ w in Ioi 0, η / w ^ 2 * Real.exp (-(w - η / w) ^ 2) = Real.sqrt Real.pi / 2 := by
  obtain ⟨-, -, h⟩ := integral_J_sum hη
  have h2 := integral_J_swap hη
  constructor <;> linarith


theorem exp_sq_split {η w : ℝ} (hw : 0 < w) :
    Real.exp (-w ^ 2 - η ^ 2 / w ^ 2) = Real.exp (-(2 * η)) * Real.exp (-(w - η / w) ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

/-- `A = ∫ e^{-w² - η²/w²} = e^{-2η}√π/2` and `η∫ w⁻² e^{-w² - η²/w²} = e^{-2η}√π/2`, with
the integrability of both integrands. -/
theorem integral_AB {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun w : ℝ => Real.exp (-w ^ 2 - η ^ 2 / w ^ 2)) (Ioi 0) ∧
      IntegrableOn (fun w : ℝ => η / w ^ 2 * Real.exp (-w ^ 2 - η ^ 2 / w ^ 2)) (Ioi 0) ∧
      ∫ w in Ioi 0, Real.exp (-w ^ 2 - η ^ 2 / w ^ 2) =
        Real.exp (-(2 * η)) * (Real.sqrt Real.pi / 2) ∧
      ∫ w in Ioi 0, η / w ^ 2 * Real.exp (-w ^ 2 - η ^ 2 / w ^ 2) =
        Real.exp (-(2 * η)) * (Real.sqrt Real.pi / 2) := by
  obtain ⟨h1, h2, -⟩ := integral_J_sum hη
  obtain ⟨e1, e2⟩ := integral_J_eq hη
  have c1 : EqOn (fun w : ℝ => Real.exp (-w ^ 2 - η ^ 2 / w ^ 2))
      (fun w => Real.exp (-(2 * η)) * Real.exp (-(w - η / w) ^ 2)) (Ioi 0) :=
    fun w hw => exp_sq_split hw
  have c2 : EqOn (fun w : ℝ => η / w ^ 2 * Real.exp (-w ^ 2 - η ^ 2 / w ^ 2))
      (fun w => Real.exp (-(2 * η)) * (η / w ^ 2 * Real.exp (-(w - η / w) ^ 2))) (Ioi 0) :=
    fun w hw => by simp only; rw [exp_sq_split hw]; ring
  refine ⟨IntegrableOn.congr_fun (h1.const_mul (Real.exp (-(2 * η)))) c1.symm measurableSet_Ioi,
    IntegrableOn.congr_fun (h2.const_mul (Real.exp (-(2 * η)))) c2.symm measurableSet_Ioi, ?_, ?_⟩
  · rw [setIntegral_congr_fun measurableSet_Ioi c1, integral_const_mul, e1]
  · rw [setIntegral_congr_fun measurableSet_Ioi c2, integral_const_mul, e2]


/-- `∫ w² e^{-w² - η²/w²} = e^{-2η}(√π/2)(1/2 + η)`, by parts against `w e^{-w² - η²/w²}`. -/
theorem integral_C {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun w : ℝ => w ^ 2 * Real.exp (-w ^ 2 - η ^ 2 / w ^ 2)) (Ioi 0) ∧
      ∫ w in Ioi 0, w ^ 2 * Real.exp (-w ^ 2 - η ^ 2 / w ^ 2) =
        Real.exp (-(2 * η)) * (Real.sqrt Real.pi / 2) * (1 / 2 + η) := by
  obtain ⟨iA, iB, eA, eB⟩ := integral_AB hη
  set E : ℝ → ℝ := fun w => Real.exp (-w ^ 2 - η ^ 2 / w ^ 2) with hE
  have hE1 : ∀ w, 0 ≤ w → E w ≤ Real.exp (-w ^ 2) := fun w _ => by
    simp only [hE]
    have : 0 ≤ η ^ 2 / w ^ 2 := by positivity
    exact Real.exp_le_exp.2 (by linarith)
  -- integrability of `w² E`
  have iC : IntegrableOn (fun w : ℝ => w ^ 2 * E w) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := 2) (by norm_num)
    refine Integrable.mono' h (by simp only [hE]; fun_prop) ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun w (hw : 0 < w) => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hE]; positivity), Real.rpow_two, neg_one_mul]
    exact mul_le_mul_of_nonneg_left (hE1 w hw.le) (by positivity)
  refine ⟨iC, ?_⟩
  -- the boundary function `F(w) = w E(w)` and its derivative
  set F : ℝ → ℝ := fun w => w * E w with hF
  set F' : ℝ → ℝ := fun w => E w - 2 * (w ^ 2 * E w) + 2 * η * (η / w ^ 2 * E w) with hF'
  have hderiv : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt F (F' w) w := by
    intro w (hw : 0 < w)
    have hw0 : w ≠ 0 := hw.ne'
    have hin : HasDerivAt (fun w : ℝ => -w ^ 2 - η ^ 2 / w ^ 2)
        (-(2 * w) + 2 * η ^ 2 / w ^ 3) w := by
      have h3 := (hasDerivAt_pow 2 w).neg.sub
        ((hasDerivAt_const w (η ^ 2)).div (hasDerivAt_pow 2 w) (pow_ne_zero 2 hw0))
      refine h3.congr_deriv ?_
      field_simp
      ring
    have h := (hasDerivAt_id w).mul hin.exp
    refine h.congr_deriv ?_
    simp only [hF', hE, id]
    field_simp
    ring
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    have hF0 : F 0 = 0 := by simp [hF]
    rw [ContinuousWithinAt, hF0]
    refine squeeze_zero_norm' ?_ (tendsto_nhdsWithin_of_tendsto_nhds
      (continuous_id.tendsto' 0 0 rfl))
    filter_upwards [self_mem_nhdsWithin] with w (hw : 0 ≤ w)
    simp only [hF, hE, norm_mul, Real.norm_eq_abs, abs_of_nonneg hw, id]
    rw [abs_of_pos (Real.exp_pos _)]
    have := hE1 w hw
    have h1 : Real.exp (-w ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    simp only [hE] at this
    nlinarith
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with w hw
    have hEpos : 0 < E w := by simp only [hE]; exact Real.exp_pos _
    change ‖w * E w‖ ≤ w ^ 1 * Real.exp (-w)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ w),
      abs_of_pos hEpos, pow_one]
    refine mul_le_mul_of_nonneg_left ((hE1 w (by linarith)).trans (Real.exp_le_exp.2 ?_))
      (by linarith)
    nlinarith
  have iF' : IntegrableOn F' (Ioi 0) := (iA.sub (iC.const_mul 2)).add (iB.const_mul (2 * η))
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv iF' hlim
  have hF0 : F 0 = 0 := by simp [hF]
  rw [hF0, sub_zero] at hibp
  have i1 : IntegrableOn (fun w => E w - 2 * (w ^ 2 * E w)) (Ioi 0) := iA.sub (iC.const_mul 2)
  have i2 : IntegrableOn (fun w => 2 * η * (η / w ^ 2 * E w)) (Ioi 0) := iB.const_mul (2 * η)
  have hs1 := integral_add i1 i2
  have hs2 := integral_sub iA (iC.const_mul 2)
  have hs3 : ∫ w in Ioi 0, 2 * (w ^ 2 * E w) = 2 * ∫ w in Ioi 0, w ^ 2 * E w :=
    integral_const_mul _ _
  have hs4 : ∫ w in Ioi 0, 2 * η * (η / w ^ 2 * E w) = 2 * η * ∫ w in Ioi 0, η / w ^ 2 * E w :=
    integral_const_mul _ _
  have hF'eq : F' = fun w => (E w - 2 * (w ^ 2 * E w)) + 2 * η * (η / w ^ 2 * E w) := rfl
  rw [hF'eq, hs1, hs2, hs3, hs4] at hibp
  have eA' : ∫ w in Ioi 0, E w = Real.exp (-(2 * η)) * (Real.sqrt Real.pi / 2) := eA
  have eB' : ∫ w in Ioi 0, η / w ^ 2 * E w = Real.exp (-(2 * η)) * (Real.sqrt Real.pi / 2) := eB
  rw [eA', eB'] at hibp
  change ∫ w in Ioi 0, w ^ 2 * E w = _
  linarith


/-- The substitution `v = w²` on `(0,∞)`. -/
theorem integral_Ioi_comp_sq (g : ℝ → ℝ) :
    ∫ v in Ioi 0, g v = ∫ w in Ioi 0, 2 * w * g (w ^ 2) := by
  have hder : ∀ w ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun w : ℝ => w ^ 2) (2 * w) (Ioi 0) w :=
    fun w _ => by simpa using (hasDerivAt_pow 2 w).hasDerivWithinAt
  have hinj : InjOn (fun w : ℝ => w ^ 2) (Ioi 0) := fun a (ha : 0 < a) b (hb : 0 < b) h => by
    simp only at h
    nlinarith [h]
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj g
  rw [image_sq_Ioi] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 0 < w) => ?_
  rw [smul_eq_mul, abs_of_pos (by positivity)]

theorem besselProfile_one_pos {y : ℝ} (hy : 0 < y) : besselProfile 1 y = 2 * Real.exp (-y) := by
  have hη : 0 < y / 2 := by positivity
  obtain ⟨-, -, eA, -⟩ := integral_AB hη
  rw [besselProfile, integral_Ioi_comp_sq]
  have hc : ∀ w ∈ Ioi (0 : ℝ), 2 * w * ((w ^ 2) ^ (((1 : ℕ) : ℝ) / 2 - 1) *
      Real.exp (-w ^ 2 - y ^ 2 / (4 * w ^ 2))) =
      2 * Real.exp (-w ^ 2 - (y / 2) ^ 2 / w ^ 2) := by
    intro w (hw : 0 < w)
    rw [sq_rpow_eq hw.le, show (2 : ℝ) * (((1 : ℕ) : ℝ) / 2 - 1) = -1 by norm_num,
      Real.rpow_neg_one,
      show y ^ 2 / (4 * w ^ 2) = (y / 2) ^ 2 / w ^ 2 by ring]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hc, integral_const_mul, eA,
    show ((1 : ℕ) : ℝ) / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp

theorem besselProfile_three_pos {y : ℝ} (hy : 0 < y) :
    besselProfile 3 y = 2 * (1 + y) * Real.exp (-y) := by
  have hη : 0 < y / 2 := by positivity
  obtain ⟨-, eC⟩ := integral_C hη
  rw [besselProfile, integral_Ioi_comp_sq]
  have hc : ∀ w ∈ Ioi (0 : ℝ), 2 * w * ((w ^ 2) ^ (((3 : ℕ) : ℝ) / 2 - 1) *
      Real.exp (-w ^ 2 - y ^ 2 / (4 * w ^ 2))) =
      2 * (w ^ 2 * Real.exp (-w ^ 2 - (y / 2) ^ 2 / w ^ 2)) := by
    intro w (hw : 0 < w)
    rw [sq_rpow_eq hw.le, show (2 : ℝ) * (((3 : ℕ) : ℝ) / 2 - 1) = 1 by norm_num, Real.rpow_one,
      show y ^ 2 / (4 * w ^ 2) = (y / 2) ^ 2 / w ^ 2 by ring]
    ring
  have hΓ : Real.Gamma (((3 : ℕ) : ℝ) / 2) = Real.sqrt Real.pi / 2 := by
    rw [show ((3 : ℕ) : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hc, integral_const_mul, eC, hΓ]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp



/-- `∫ (1 - cos⟨ω,x⟩) g_{2s}(x) dx = 1 - e^{-s|ω|²}`, in `[0,∞]`: the affine export's
`lintegral_one_sub_cos_heat`, with the integrand split as a product. -/
theorem lintegral_one_sub_cos_heatKernel {s : ℝ} (hs : 0 < s) (ω : Rd d) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) * ENNReal.ofReal (heatKernel d (2 * s) x) =
      ENNReal.ofReal (1 - Real.exp (-(s * ‖ω‖ ^ 2))) := by
  rw [← lintegral_one_sub_cos_heat hs ω]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul (sub_nonneg.2 (Real.cos_le_one _))]
  congr 2
  unfold heatKernel
  ring_nf

/-- Frullani's integral in the form `∫₀^∞ (1 - e^{-su}) e^{-s/β} ds/s = log(1 + βu)`. -/
theorem lintegral_frullani_log {β u : ℝ} (hβ : 0 < β) (hu : 0 ≤ u) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s / β) / s) *
        ENNReal.ofReal (1 - Real.exp (-(s * u))) = ENNReal.ofReal (Real.log (1 + β * u)) := by
  rcases hu.eq_or_lt with rfl | hu
  · simp
  have hab : 1 / β < u + 1 / β := by linarith
  have h := lintegral_frullani (by positivity : 0 < 1 / β) hab
  rw [show (u + 1 / β) / (1 / β) = 1 + β * u by field_simp; ring] at h
  rw [← h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show -((u + 1 / β) * s) = -(s * u) + -(1 / β * s) by ring, Real.exp_add]
  rw [show -(1 / β * s) = -s / β by ring]
  field_simp


/-- The integrand after `s = ρ²/(4v)`. -/
theorem heat_subst_eq {β ρ v : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hv : 0 < v) (x : Rd d)
    (hx : ‖x‖ = ρ) :
    (ρ ^ 2 / 4 / v ^ 2) * (Real.exp (-(ρ ^ 2 / 4 / v) / β) / (ρ ^ 2 / 4 / v) *
      heatKernel d (2 * (ρ ^ 2 / 4 / v)) x) =
      (Real.pi * ρ ^ 2) ^ (-(d : ℝ) / 2) *
        (v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - (ρ / Real.sqrt β) ^ 2 / (4 * v))) := by
  have hpi := Real.pi_pos
  rw [heatKernel, hx, show 2 * Real.pi * (2 * (ρ ^ 2 / 4 / v)) = (Real.pi * ρ ^ 2) / v by
    field_simp; ring, Real.div_rpow (by positivity) hv.le, Real.rpow_sub_one hv.ne',
    show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hv.le,
    show -ρ ^ 2 / (2 * (2 * (ρ ^ 2 / 4 / v))) = -v by field_simp; ring,
    div_pow, Real.sq_sqrt hβ.le]
  have h1 : Real.exp (-(ρ ^ 2 / 4 / v) / β) * Real.exp (-v) =
      Real.exp (-v - ρ ^ 2 / β / (4 * v)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [← h1]
  have : 0 < v ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hv _
  field_simp


/-- **The polar density of `log(1 + β|ω|²)` as a mixture of heat kernels**: for `x ≠ 0`,
`b_d(|x|/√β)/(|S^{d-1}||x|^d) = ∫₀^∞ g_{2s}(x) e^{-s/β} ds/s`. -/
theorem polar_density_eq_lintegral (hd : 1 ≤ d) {β : ℝ} (hβ : 0 < β) {x : Rd d} (hx : x ≠ 0) :
    ENNReal.ofReal (besselProfile d (‖x‖ / Real.sqrt β) / (sphereArea d * ‖x‖ ^ d)) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s / β) / s) *
        ENNReal.ofReal (heatKernel d (2 * s) x) := by
  set ρ := ‖x‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.2 hx
  have hds : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set c := ρ ^ 2 / 4 with hc
  have hcpos : 0 < c := by positivity
  set g : ℝ → ℝ := fun s => Real.exp (-s / β) / s * heatKernel d (2 * s) x with hg
  have hder : ∀ v ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun v : ℝ => c / v) (-c / v ^ 2) (Ioi 0) v :=
    fun v (hv : 0 < v) => by
      have := (hasDerivAt_inv hv.ne').const_mul c
      have h2 : (fun w : ℝ => c / w) = fun y => c * y⁻¹ := funext fun y => div_eq_mul_inv _ _
      rw [h2, show -c / v ^ 2 = c * -(v ^ 2)⁻¹ by ring]
      exact this.hasDerivWithinAt
  have hinj : InjOn (fun v : ℝ => c / v) (Ioi 0) := fun a (ha : 0 < a) b (hb : 0 < b) h => by
    simp only at h
    field_simp at h
    nlinarith [h]
  have hsub : ∀ v ∈ Ioi (0 : ℝ), |-c / v ^ 2| • g (c / v) =
      (Real.pi * ρ ^ 2) ^ (-(d : ℝ) / 2) *
        (v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - (ρ / Real.sqrt β) ^ 2 / (4 * v))) := by
    intro v (hv : 0 < v)
    have hneg : -c / v ^ 2 < 0 := by
      have : 0 < c / v ^ 2 := by positivity
      rw [neg_div]; linarith
    rw [abs_of_neg hneg, neg_div, neg_neg, smul_eq_mul, hg, hc]
    exact heat_subst_eq hβ hρ hv x rfl
  have hI := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder hinj g).2
    (IntegrableOn.congr_fun ((integrableOn_besselProfile hds (ρ / Real.sqrt β)).const_mul _)
      (fun v hv => (hsub v hv).symm) measurableSet_Ioi)
  rw [image_const_div_Ioi hcpos] at hI
  have hE := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj g
  rw [image_const_div_Ioi hcpos, setIntegral_congr_fun measurableSet_Ioi hsub,
    integral_const_mul] at hE
  have hnn : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ g s := fun s (hs : 0 < s) => by
    simp only [hg]
    exact mul_nonneg (by positivity) (heatKernel_nonneg (by positivity) x)
  have hlin : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s / β) / s) *
      ENNReal.ofReal (heatKernel d (2 * s) x) = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (g s) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
    rw [hg, ENNReal.ofReal_mul (by positivity)]
  rw [hlin, ← ofReal_integral_eq_lintegral_ofReal hI
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn)), hE]
  congr 1
  rw [besselProfile, sphereArea]
  generalize (∫ v in Ioi (0 : ℝ), v ^ ((d : ℝ) / 2 - 1) *
    Real.exp (-v - (ρ / Real.sqrt β) ^ 2 / (4 * v))) = I
  have hΓ := Real.Gamma_pos_of_pos hds
  have hpi := Real.pi_pos
  rw [Real.mul_rpow hpi.le (by positivity), show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg hpi.le, Real.rpow_neg (by positivity), ← Real.rpow_natCast_mul hρ.le,
    show ((2 : ℕ) : ℝ) * ((d : ℝ) / 2) = (d : ℕ) by push_cast; ring, Real.rpow_natCast]
  have : 0 < Real.pi ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hpi _
  field_simp


theorem bessel_profile_2_of_continuous (hd : 1 ≤ d) (hcont : Continuous (besselProfile d)) {β : ℝ}
    (hβ : 0 < β) (ω : Rd d) :
    ENNReal.ofReal (Real.log (1 + β * ‖ω‖ ^ 2)) =
      ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫)
        ∂(polarLevyMeasure d fun ρ => besselProfile d (ρ / Real.sqrt β)) := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  set A : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-s / β) / s) with hA
  set H : Rd d → ℝ → ℝ≥0∞ := fun x s => ENNReal.ofReal (heatKernel d (2 * s) x) with hH
  set C : Rd d → ℝ≥0∞ := fun x => ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) with hC
  have hdm : Measurable fun x : Rd d => ({0}ᶜ : Set (Rd d)).indicator (fun x =>
      ENNReal.ofReal (besselProfile d (‖x‖ / Real.sqrt β) / (sphereArea d * ‖x‖ ^ d))) x := by
    refine Measurable.indicator ?_ (measurableSet_singleton 0).compl
    exact ((hcont.measurable.comp (by fun_prop)).div (by fun_prop)).ennreal_ofReal
  rw [polarLevyMeasure, lintegral_withDensity_eq_lintegral_mul _ hdm (by fun_prop)]
  have hae : (fun x : Rd d => (({0}ᶜ : Set (Rd d)).indicator (fun x =>
      ENNReal.ofReal (besselProfile d (‖x‖ / Real.sqrt β) / (sphereArea d * ‖x‖ ^ d))) *
        C) x) =ᵐ[volume] fun x => ∫⁻ s in Ioi (0 : ℝ), A s * H x s * C x := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Rd d))] with x hx
    rw [Pi.mul_apply, Set.indicator_of_mem hx, polar_density_eq_lintegral hd hβ
      (by simpa using hx), lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_congr_ae hae, lintegral_lintegral_swap (by
    simp only [hA, hH, hC, heatKernel]
    fun_prop)]
  have hin : ∀ s ∈ Ioi (0 : ℝ), ∫⁻ x, A s * H x s * C x =
      A s * ENNReal.ofReal (1 - Real.exp (-(s * ‖ω‖ ^ 2))) := by
    intro s (hs : 0 < s)
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_one_sub_cos_heatKernel hs ω]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [mul_comm]
  rw [setLIntegral_congr_fun measurableSet_Ioi hin, lintegral_frullani_log hβ (sq_nonneg _)]


/-- **`lem:bessel-profile`(1), the Green's function.** For `g ∈ L¹(ℝ^d)`,
`(I - r²Δ)(L_r * g) = g` in the sense of distributions: tested against every smooth compactly
supported `φ`. -/
theorem bessel_profile_1_green {r : ℝ} (g : Rd d → ℝ)
    (hg : Integrable g) (φ : Rd d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, ScaleSpace.mconvE (maternStep d r) g x * (φ x - r ^ 2 * Δ φ x) = ∫ x, g x * φ x := by
  haveI := (charFun_maternStep (d := d) r 0).1
  exact helmholtz_green (maternStep d r) (fun ξ => (charFun_maternStep r ξ).2) g hg φ hφ hφc

/-- **`lem:bessel-profile`(2).** For `β > 0`,
`log(1 + β|ω|²) = ∫ (1 - cos⟨ω,x⟩) b_d(|x|/√β) (|S^{d-1}| |x|^d)⁻¹ dx`, in `[0,∞]`. -/
theorem bessel_profile_2 (hd : 1 ≤ d) {β : ℝ} (hβ : 0 < β) (ω : Rd d) :
    ENNReal.ofReal (Real.log (1 + β * ‖ω‖ ^ 2)) =
      ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫)
        ∂(polarLevyMeasure d fun ρ => besselProfile d (ρ / Real.sqrt β)) :=
  bessel_profile_2_of_continuous hd (continuous_besselProfile hd) hβ ω

/-- **`lem:bessel-profile`(3), the profile.** `b_d(0) = 2`; `b_d` is continuous and strictly
decreasing on `[0,∞)`, with `b_d(y) ≤ C_d e^{-y/2}`, `C_d = 2^{1+d/2}`. -/
theorem bessel_profile_3 (hd : 1 ≤ d) :
    besselProfile d 0 = 2 ∧ ContinuousOn (besselProfile d) (Ici 0) ∧
      StrictAntiOn (besselProfile d) (Ici 0) ∧
      ∀ y : ℝ, 0 ≤ y → besselProfile d y ≤ (2 : ℝ) ^ (1 + (d : ℝ) / 2) * Real.exp (-y / 2) :=
  ⟨besselProfile_zero hd, (continuous_besselProfile hd).continuousOn,
    besselProfile_strictAntiOn hd, fun y _ => besselProfile_le hd y⟩

/-- **`lem:bessel-profile`(3), the closed forms.** `b_1(y) = 2e^{-y}` and `b_3(y) = 2(1+y)e^{-y}`,
`y ≥ 0`. -/
theorem bessel_profile_3_closed :
    (∀ y : ℝ, 0 ≤ y → besselProfile 1 y = 2 * Real.exp (-y)) ∧
      ∀ y : ℝ, 0 ≤ y → besselProfile 3 y = 2 * (1 + y) * Real.exp (-y) := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rcases hy.eq_or_lt with rfl | hy
    · rw [besselProfile_zero le_rfl]; simp
    · exact besselProfile_one_pos hy
  · rcases hy.eq_or_lt with rfl | hy
    · rw [besselProfile_zero (by norm_num)]; simp
    · exact besselProfile_three_pos hy

end Pyramids
