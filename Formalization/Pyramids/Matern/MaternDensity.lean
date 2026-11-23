/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.MaternPyramid
import Pyramids.Matern.MaternChar
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# `thm:matern-pyramid`(1): the family, and the smooth density of the kernels

Blueprint: `blueprint/src/parts/04-matern.tex`, `thm:matern-pyramid`. Phase 5, wave 3b.
`matern_pyramid_1_family` moved here from `PyramidsSkeleton.Ch04Matern`, its statement unchanged.

* **The family.** A34's realization at `χ = id` has the same laws as any Matérn pyramid, and its
  clauses (I1)–(I3), (ND) transfer (`isIsotropicFamily_of_eq`); covariance and the octave step are
  read on the transforms (`MaternPyramid`).
* **A density from integrable moments of the transform** (`density_of_radial_charFun`), proved here
  from Fourier analysis on Schwartz functions, with no cited fact. For `μ̂(ω) = e^{-G(|ω|)}` with
  `|ω|ⁿe^{-G(|ω|)}` integrable for every `n`, put `ψ(ξ) := μ̂(2πξ)` (`μ`'s transform in Mathlib's
  normalisation, `mChar`) and `p := 𝓕ψ`.
  - `p` is real (`ψ` is real and even), `C^∞`, and its derivatives are bounded by the moments of
    `ψ` (`iteratedFDeriv_fourier`).
  - `∫ Φ p = ∫ Φ dμ` for every Schwartz `Φ`: `∫ Φ dμ = ∫ ψ 𝓕⁻Φ` by Fubini
    (`integral_mChar_smul_mul`) and Schwartz inversion, `ψ` even turns `𝓕⁻` into `𝓕`, and `𝓕` is
    self-adjoint.
  - `p ≥ 0`: a negative value would make `∫ Φ p < 0` for a bump `Φ ≥ 0` around it.
  - `∫ p ≤ 1`, testing on bumps equal to `1` on balls, and monotone convergence.
  - `μ = p dx`: both are finite, and their transforms agree: characters cut off by those bumps are
    Schwartz functions, and dominated convergence passes to the limit on both sides.
* **The moments of the Matérn kernel.** Keeping `N` terms of the series,
  `e^{-F_q(t|ω|)} ≤ (1 + b|ω|²)^{-N}` with `b = min(1, c²t²q^{-2N})`, and Mathlib's
  `integrable_rpow_neg_one_add_norm_sq` for `2N > n + d`.

**What it reaches.** The density prints Lean core; the family prints A35's names and A34's (none of
its own), through the realization.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter Complex
open scoped Topology ENNReal RealInnerProductSpace SchwartzMap FourierTransform

variable {d : ℕ}

/-! ## A density from integrable moments of a radial transform -/

/-- `ψ(ξ) := e^{-G(2π|ξ|)}`, the transform in Mathlib's normalisation. -/
noncomputable def radPsi (G : ℝ → ℝ) (ξ : Rd d) : ℂ := ((Real.exp (-G (2 * Real.pi * ‖ξ‖)) : ℝ) : ℂ)

theorem norm_radPsi (G : ℝ → ℝ) (ξ : Rd d) :
    ‖radPsi G ξ‖ = Real.exp (-G (2 * Real.pi * ‖ξ‖)) := by
  rw [radPsi, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem radPsi_neg (G : ℝ → ℝ) (ξ : Rd d) : radPsi G (-ξ) = radPsi G ξ := by
  simp [radPsi]

theorem mChar_eq_radPsi (μ : Measure (Rd d)) {G : ℝ → ℝ}
    (hcf : ∀ ω, charFun μ ω = ((Real.exp (-G ‖ω‖) : ℝ) : ℂ)) (ξ : Rd d) :
    mChar μ ξ = radPsi G ξ := by
  have hn : ‖((-(2 * Real.pi) : ℝ) • ξ)‖ = 2 * Real.pi * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos Real.two_pi_pos]
  rw [mChar, radPsi, ← hn, ← hcf, charFun_apply]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [real_inner_smul_right]
  congr 2
  push_cast
  ring

theorem integrable_moment_radPsi {G : ℝ → ℝ}
    (hmom : ∀ n : ℕ, Integrable fun ω : Rd d => ‖ω‖ ^ n * Real.exp (-G ‖ω‖)) (n : ℕ) :
    Integrable fun ξ : Rd d => ‖ξ‖ ^ n * ‖radPsi G ξ‖ := by
  have h := ((hmom n).comp_smul (Real.two_pi_pos.ne' : (2 * Real.pi) ≠ 0)).const_mul
    (((2 * Real.pi) ^ n)⁻¹)
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only [norm_radPsi, norm_smul, Real.norm_eq_abs, abs_of_pos Real.two_pi_pos, mul_pow]
  field_simp

theorem continuous_radPsi (μ : Measure (Rd d)) [IsFiniteMeasure μ] {G : ℝ → ℝ}
    (hcf : ∀ ω, charFun μ ω = ((Real.exp (-G ‖ω‖) : ℝ) : ℂ)) : Continuous (radPsi (d := d) G) := by
  have h : radPsi (d := d) G = mChar μ := funext fun ξ => (mChar_eq_radPsi μ hcf ξ).symm
  rw [h]
  exact continuous_mChar μ

theorem integrable_radPsi (μ : Measure (Rd d)) [IsFiniteMeasure μ] {G : ℝ → ℝ}
    (hcf : ∀ ω, charFun μ ω = ((Real.exp (-G ‖ω‖) : ℝ) : ℂ))
    (hmom : ∀ n : ℕ, Integrable fun ω : Rd d => ‖ω‖ ^ n * Real.exp (-G ‖ω‖)) :
    Integrable (radPsi (d := d) G) := by
  have h := integrable_moment_radPsi hmom 0
  simp only [pow_zero, one_mul] at h
  exact (integrable_norm_iff (continuous_radPsi μ hcf).aestronglyMeasurable).1 h


section Density

variable {G : ℝ → ℝ}

/-- `𝓕ψ` is real: `ψ` is real and even. -/
theorem fourier_radPsi_re (x : Rd d) :
    (((𝓕 (radPsi (d := d) G) x).re : ℝ) : ℂ) = 𝓕 (radPsi (d := d) G) x := by
  rw [← Complex.conj_eq_iff_re, Real.fourier_eq', ← integral_conj,
    ← integral_neg_eq_self (fun v : Rd d => Complex.exp (↑(-2 * Real.pi * ⟪v, x⟫) * I) •
      radPsi G v)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, map_mul, radPsi_neg, inner_neg_left]
  rw [radPsi, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [Complex.conj_ofReal, map_ofNat]

/-- **The test identity**: `∫ Φ · 𝓕ψ = ∫ Φ dμ` for every Schwartz `Φ`. -/
theorem integral_schwartz_mul_fourier_radPsi (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hcf : ∀ ω, charFun μ ω = ((Real.exp (-G ‖ω‖) : ℝ) : ℂ))
    (hmom : ∀ n : ℕ, Integrable fun ω : Rd d => ‖ω‖ ^ n * Real.exp (-G ‖ω‖))
    (Φ : 𝓢(Rd d, ℂ)) :
    ∫ x, Φ x * 𝓕 (radPsi (d := d) G) x = ∫ x, Φ x ∂μ := by
  have h1 := integral_mChar_smul_mul μ (𝓕⁻ Φ) 1
  simp only [one_smul, FourierTransform.fourier_fourierInv_eq] at h1
  rw [← h1]
  have hψ := integrable_radPsi μ hcf hmom
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (Rd d))
    Real.continuous_fourierChar continuous_inner hψ (Φ.integrable (μ := volume))
  simp only [smul_eq_mul] at hflip
  have hflip' : ∫ ξ, 𝓕 (radPsi (d := d) G) ξ * Φ ξ =
      ∫ ξ, radPsi (d := d) G ξ * 𝓕 (Φ : Rd d → ℂ) ξ := by
    simpa using! hflip
  have e2 : ∫ ξ, mChar μ ξ * (𝓕⁻ Φ) ξ = ∫ ξ, radPsi (d := d) G ξ * 𝓕 (Φ : Rd d → ℂ) ξ := by
    rw [← integral_neg_eq_self (fun ξ => radPsi (d := d) G ξ * 𝓕 (Φ : Rd d → ℂ) ξ)]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [mChar_eq_radPsi μ hcf, radPsi_neg, SchwartzMap.fourierInv_coe,
      Real.fourierInv_eq_fourier_neg]
  rw [e2, ← hflip']
  simp_rw [mul_comm (Φ _)]


/-- A test function, as a Schwartz function, from a real smooth compactly supported one times a
character. -/
theorem isTestFn_ofReal_mul {φ : Rd d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (ω : Rd d) : IsTestFn fun x => (φ x : ℂ) * Complex.exp (⟪x, ω⟫ * I) := by
  refine ⟨(ofRealCLM.contDiff.comp hφ).mul ?_, ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x : Rd d => ⟪x, ω⟫ := contDiff_id.inner ℝ contDiff_const
    exact Complex.contDiff_exp.comp ((ofRealCLM.contDiff.comp h1).mul contDiff_const)
  · exact (hφc.comp_left Complex.ofReal_zero).mul_right

/-- **A density from integrable moments of a radial transform.** -/
theorem density_of_radial_charFun (μ : Measure (Rd d)) [IsProbabilityMeasure μ] {G : ℝ → ℝ}
    (hcf : ∀ ω, charFun μ ω = ((Real.exp (-G ‖ω‖) : ℝ) : ℂ))
    (hmom : ∀ n : ℕ, Integrable fun ω : Rd d => ‖ω‖ ^ n * Real.exp (-G ‖ω‖)) :
    ∃ p : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ (∀ x, 0 ≤ p x) ∧
      (∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n p x‖ ≤ C) ∧
      μ = volume.withDensity fun x => ENNReal.ofReal (p x) := by
  set ψ := radPsi (d := d) G with hψdef
  have hmomψ : ∀ n : ℕ, n ≤ (⊤ : ℕ∞) → Integrable fun v : Rd d => ‖v‖ ^ n * ‖ψ v‖ :=
    fun n _ => integrable_moment_radPsi hmom n
  have hF : ContDiff ℝ (⊤ : ℕ∞) (𝓕 ψ) := Real.contDiff_fourier hmomψ
  set p : Rd d → ℝ := fun x => (𝓕 ψ x).re with hpdef
  have hpC : ∀ x, ((p x : ℝ) : ℂ) = 𝓕 ψ x := fun x => fourier_radPsi_re x
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := reCLM.contDiff.comp hF
  have hpc : Continuous p := hp.continuous
  -- the test identity, real form
  have htest : ∀ φ : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, φ x * p x = ∫ x, φ x ∂μ := by
    intro φ hφ hφc
    have hT : IsTestFn fun x => (φ x : ℂ) :=
      ⟨ofRealCLM.contDiff.comp hφ, hφc.comp_left Complex.ofReal_zero⟩
    have h := integral_schwartz_mul_fourier_radPsi μ hcf hmom hT.toSchwartz
    simp only [IsTestFn.toSchwartz_apply] at h
    rw [← hψdef] at h
    simp only [← hpC] at h
    rw [← Complex.ofReal_inj, ← integral_complex_ofReal, ← integral_complex_ofReal]
    push_cast
    exact h
  -- nonnegativity
  have hp0 : ∀ x, 0 ≤ p x := by
    intro x0
    by_contra hneg
    push Not at hneg
    have hopen : IsOpen {x | p x < 0} := isOpen_lt hpc continuous_const
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen x0 hneg
    let b : ContDiffBump x0 := ⟨δ / 2, δ, by positivity, by linarith⟩
    have hsupp : ∀ x, b x ≠ 0 → p x < 0 := fun x hx => by
      have : x ∈ Function.support b := hx
      rw [b.support_eq] at this
      exact hball this
    have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume)
      (f := fun x => -(b x * p x)) (x := x0) (b.continuous.mul hpc).neg
      (b.hasCompactSupport.mul_right.neg) (fun x => by
        by_cases hx : b x = 0
        · simp [hx]
        · have := hsupp x hx
          have := b.nonneg (x := x)
          simp only [Pi.zero_apply]
          nlinarith)
      (by
        rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))]
        simp only [one_mul, neg_ne_zero]
        exact hneg.ne)
    rw [integral_neg, htest b b.contDiff b.hasCompactSupport] at hpos
    have := integral_nonneg (μ := μ) (f := fun x => b x) fun x => b.nonneg
    linarith
  -- the mass: bumps equal to `1` on the balls of radius `n + 1`
  let bn : ℕ → ContDiffBump (0 : Rd d) := fun n =>
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  have hbn1 : ∀ x : Rd d, ∀ᶠ n in atTop, bn n x = 1 := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    refine (bn n).one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖x‖ ≤ (n : ℝ) + 1
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hbnp : ∀ n, Integrable fun x => bn n x * p x := fun n =>
    ((bn n).continuous.mul hpc).integrable_of_hasCompactSupport (bn n).hasCompactSupport.mul_right
  have hmass : ∫⁻ x, ENNReal.ofReal (p x) ≤ 1 := by
    have hlim : ∀ x, Tendsto (fun n => ENNReal.ofReal (bn n x * p x)) atTop
        (𝓝 (ENNReal.ofReal (p x))) := fun x =>
      tendsto_const_nhds.congr' ((hbn1 x).mono fun n hn => by simp only [hn, one_mul])
    calc ∫⁻ x, ENNReal.ofReal (p x)
        = ∫⁻ x, liminf (fun n => ENNReal.ofReal (bn n x * p x)) atTop := by
          refine lintegral_congr fun x => (hlim x).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (bn n x * p x)) atTop :=
          lintegral_liminf_le fun n => ((bn n).continuous.mul hpc).measurable.ennreal_ofReal
      _ ≤ 1 := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hbnp n)
            (Eventually.of_forall fun x => mul_nonneg (bn n).nonneg (hp0 x)),
            htest _ (bn n).contDiff (bn n).hasCompactSupport]
          refine ENNReal.ofReal_le_one.2 ?_
          calc ∫ x, bn n x ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ :=
                integral_mono_of_nonneg (Eventually.of_forall fun _ => (bn n).nonneg)
                  (integrable_const 1) (Eventually.of_forall fun _ => (bn n).le_one)
            _ = 1 := by simp
  have hpi : Integrable p := by
    refine ⟨hpc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hp0)]
    exact hmass.trans_lt ENNReal.one_lt_top
  -- the measure `p dx`, and its transform
  set ν := volume.withDensity fun x => ENNReal.ofReal (p x) with hν
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hmass.trans_lt ENNReal.one_lt_top
  have hcfν : ∀ ω, charFun ν ω = ∫ x, Complex.exp (⟪x, ω⟫ * I) * (p x : ℂ) := by
    intro ω
    rw [charFun_apply, hν, integral_withDensity_eq_integral_toReal_smul
      hpc.measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hp0 x), Complex.real_smul]
    ring
  refine ⟨p, hp, hp0, fun n => ?_, ?_⟩
  · -- bounded derivatives
    refine ⟨‖(reCLM : ℂ →L[ℝ] ℝ)‖ *
      ∫ v, ‖VectorFourier.fourierPowSMulRight (innerSL ℝ (E := Rd d)) ψ v n‖, fun x => ?_⟩
    have h1 := (reCLM : ℂ →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left (x := x) (n := n)
      hF.contDiffAt (by exact_mod_cast le_top)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [Real.iteratedFDeriv_fourier hmomψ (continuous_radPsi μ hcf).aestronglyMeasurable
      (by exact_mod_cast le_top)]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  · -- the transforms agree
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [hcfν]
    have hT : ∀ n, IsTestFn fun x => ((bn n x : ℝ) : ℂ) * Complex.exp (⟪x, ω⟫ * I) := fun n =>
      isTestFn_ofReal_mul (bn n).contDiff (bn n).hasCompactSupport ω
    have hid : ∀ n, ∫ x, ((bn n x : ℝ) : ℂ) * Complex.exp (⟪x, ω⟫ * I) * (p x : ℂ) =
        ∫ x, ((bn n x : ℝ) : ℂ) * Complex.exp (⟪x, ω⟫ * I) ∂μ := fun n => by
      have h := integral_schwartz_mul_fourier_radPsi μ hcf hmom (hT n).toSchwartz
      simp only [IsTestFn.toSchwartz_apply] at h
      rw [← hψdef] at h
      simp only [← hpC] at h
      exact h
    have hnorm : ∀ n x, ‖((bn n x : ℝ) : ℂ) * Complex.exp (⟪x, ω⟫ * I)‖ ≤ 1 := fun n x => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (bn n).nonneg]
      exact (bn n).le_one
    have hpt : ∀ x, Tendsto (fun n => ((bn n x : ℝ) : ℂ) * Complex.exp (⟪x, ω⟫ * I)) atTop
        (𝓝 (Complex.exp (⟪x, ω⟫ * I))) := fun x =>
      tendsto_const_nhds.congr' ((hbn1 x).mono fun n hn => by simp only [hn]; simp)
    have hmeasT : ∀ n, AEStronglyMeasurable
        (fun x => ((bn n x : ℝ) : ℂ) * Complex.exp (⟪x, ω⟫ * I)) μ := fun n =>
      (hT n).1.continuous.aestronglyMeasurable
    have hL : Tendsto (fun n => ∫ x, ((bn n x : ℝ) : ℂ) * Complex.exp (⟪x, ω⟫ * I) * (p x : ℂ))
        atTop (𝓝 (∫ x, Complex.exp (⟪x, ω⟫ * I) * (p x : ℂ))) := by
      refine tendsto_integral_of_dominated_convergence (fun x => ‖p x‖)
        (fun n => (((hT n).1.continuous.mul (continuous_ofReal.comp hpc))).aestronglyMeasurable)
        hpi.norm (fun n => Eventually.of_forall fun x => ?_)
        (Eventually.of_forall fun x => ((hpt x).mul tendsto_const_nhds))
      rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _) (hnorm n x)
    have hR : Tendsto (fun n => ∫ x, ((bn n x : ℝ) : ℂ) * Complex.exp (⟪x, ω⟫ * I) ∂μ)
        atTop (𝓝 (∫ x, Complex.exp (⟪x, ω⟫ * I) ∂μ)) :=
      tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hmeasT (integrable_const 1)
        (fun n => Eventually.of_forall fun x => hnorm n x) (Eventually.of_forall hpt)
    rw [charFun_apply]
    exact tendsto_nhds_unique hR (Tendsto.congr hid hL)

end Density


/-! ## The moments of the Matérn kernel -/

variable {q c : ℝ}

/-- `F_q` is continuous. -/
theorem continuous_maternExponent (hq : 1 < q) (hc : 0 < c) : Continuous (maternExponent q c) := by
  obtain ⟨P, -, -, hP⟩ := exists_maternProfile hq hc
  rw [show maternExponent q c = P.exponent from funext hP]
  exact P.continuous_exponent

/-- Keeping `N` terms: `F_q(s) ≥ N log(1 + bs²/t²)` with `b ≤ c²t²q^{-2N}`. -/
theorem maternExponent_ge_log (hq : 1 < q) (hc : 0 < c) {t : ℝ} (N : ℕ) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : b ≤ c ^ 2 * t ^ 2 / q ^ (2 * N)) (r : ℝ) :
    N * Real.log (1 + b * r ^ 2) ≤ maternExponent q c (t * r) := by
  have hq0 : 0 < q := by linarith
  have hterm : ∀ i ∈ Finset.range N, Real.log (1 + b * r ^ 2) ≤
      Real.log (1 + c ^ 2 * (t * r) ^ 2 / q ^ (2 * (i + 1))) := by
    intro i hi
    have hi' : i + 1 ≤ N := Finset.mem_range.1 hi
    refine Real.log_le_log (by positivity) ?_
    have hpow : q ^ (2 * (i + 1)) ≤ q ^ (2 * N) := pow_le_pow_right₀ hq.le (by omega)
    have h1 : c ^ 2 * t ^ 2 / q ^ (2 * N) ≤ c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    have h2 : b * r ^ 2 ≤ c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) * r ^ 2 :=
      mul_le_mul_of_nonneg_right (hb.trans h1) (sq_nonneg r)
    have e : c ^ 2 * (t * r) ^ 2 / q ^ (2 * (i + 1)) =
        c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) * r ^ 2 := by
      ring
    rw [e]
    linarith
  calc (N : ℝ) * Real.log (1 + b * r ^ 2) = ∑ _i ∈ Finset.range N, Real.log (1 + b * r ^ 2) := by
        simp
    _ ≤ ∑ i ∈ Finset.range N, Real.log (1 + c ^ 2 * (t * r) ^ 2 / q ^ (2 * (i + 1))) :=
        Finset.sum_le_sum hterm
    _ ≤ maternExponent q c (t * r) :=
        (summable_maternExponent hq hc (t * r)).sum_le_tsum _
          fun i _ => Real.log_nonneg (le_add_of_nonneg_right (by positivity))

/-- **The moments of the transform of the kernel**: `|ω|ⁿe^{-F_q(t|ω|)}` is integrable. -/
theorem integrable_moment_matern (hq : 1 < q) (hc : 0 < c) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable fun ω : Rd d => ‖ω‖ ^ n * Real.exp (-maternExponent q c (t * ‖ω‖)) := by
  set N : ℕ := n + d + 1 with hN
  have hq0 : 0 < q := by linarith
  set b : ℝ := min 1 (c ^ 2 * t ^ 2 / q ^ (2 * N)) with hbdef
  have hb0 : 0 < b := lt_min one_pos (by positivity)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hdom : Integrable fun ω : Rd d =>
      (b ^ (N : ℝ))⁻¹ * (1 + ‖ω‖ ^ 2) ^ (-(((2 * N - n : ℕ) : ℝ)) / 2) := by
    refine (integrable_rpow_neg_one_add_norm_sq ?_).const_mul _
    rw [finrank_euclideanSpace_fin]
    have : d < 2 * N - n := by omega
    exact_mod_cast this
  have hcont := continuous_maternExponent hq hc
  refine hdom.mono' (by fun_prop) (Eventually.of_forall fun ω => ?_)
  -- the pointwise bound
  set r := ‖ω‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg ω
  have h1 : 0 < 1 + r ^ 2 := by positivity
  have h2 : 0 < 1 + b * r ^ 2 := by positivity
  have hF := maternExponent_ge_log hq hc (t := t) N hb0.le (min_le_right _ _) r
  have hexp : Real.exp (-maternExponent q c (t * r)) ≤ (1 + b * r ^ 2) ^ (-(N : ℝ)) := by
    rw [Real.rpow_def_of_pos h2]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hge : b * (1 + r ^ 2) ≤ 1 + b * r ^ 2 := by nlinarith
  have hpow : (1 + b * r ^ 2) ^ (-(N : ℝ)) ≤ (b ^ (N : ℝ))⁻¹ * (1 + r ^ 2) ^ (-(N : ℝ)) := by
    calc (1 + b * r ^ 2) ^ (-(N : ℝ)) ≤ (b * (1 + r ^ 2)) ^ (-(N : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hge (by simp)
      _ = (b ^ (N : ℝ))⁻¹ * (1 + r ^ 2) ^ (-(N : ℝ)) := by
          rw [Real.mul_rpow hb0.le h1.le, Real.rpow_neg hb0.le]
  have hrn : r ^ n ≤ (1 + r ^ 2) ^ ((n : ℝ) / 2) := by
    calc r ^ n = (r ^ 2) ^ ((n : ℝ) / 2) := by
          rw [← Real.rpow_two, ← Real.rpow_mul hr0, show (2 : ℝ) * ((n : ℝ) / 2) = n by ring,
            Real.rpow_natCast]
      _ ≤ (1 + r ^ 2) ^ ((n : ℝ) / 2) :=
          Real.rpow_le_rpow (sq_nonneg r) (by linarith) (by positivity)
  rw [Real.norm_of_nonneg (by positivity)]
  calc r ^ n * Real.exp (-maternExponent q c (t * r))
      ≤ (1 + r ^ 2) ^ ((n : ℝ) / 2) * ((b ^ (N : ℝ))⁻¹ * (1 + r ^ 2) ^ (-(N : ℝ))) :=
        mul_le_mul hrn (hexp.trans hpow) (Real.exp_pos _).le (by positivity)
    _ = (b ^ (N : ℝ))⁻¹ * (1 + r ^ 2) ^ (-(((2 * N - n : ℕ) : ℝ)) / 2) := by
        rw [mul_left_comm, ← Real.rpow_add h1]
        congr 2
        push_cast [Nat.cast_sub (show n ≤ 2 * N by omega)]
        ring


/-! ## Clause (1), the family -/

/-- **`thm:matern-pyramid`(1), the family.** Any laws with those transforms form an isotropic family
with `S_λ t = λt` for every `λ > 0`; the octave step is `μ_{t,qt} = L_{ct}`; and for `t > 0` the
kernel `μ_t` has a nonnegative `C^∞` density with every derivative bounded. -/
theorem matern_pyramid_1_family (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ) :
    IsIsotropicFamily μ ∧ (∀ lam : ℝ, 0 < lam → IsCovariantAt μ lam fun t => lam * t) ∧
      (∀ t : ℝ, 0 < t → μ t (q * t) = maternStep d (c * t)) ∧
      ∀ t : ℝ, 0 < t → ∃ p : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) p ∧ (∀ x, 0 ≤ p x) ∧
        (∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n p x‖ ≤ C) ∧
        μ 0 t = volume.withDensity fun x => ENNReal.ofReal (p x) := by
  obtain ⟨ν, hprob, ⟨S, hS⟩, hcf⟩ := cited_A34 hd (fun t => t) (maternExponent q c)
    isGauge_idFun (matern_pyramid_1_admissible hd hq hc).1 (exists_maternExponent_ne_nonneg hq hc)
  have heq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = ν s t := fun s t hs hst => by
    haveI := (hμ s t hs hst).1
    haveI := hprob s t hs hst
    exact Measure.ext_of_charFun (funext fun ω => by
      rw [charFun_maternPyramid hμ hs hst, hcf s t hs hst])
  refine ⟨isIsotropicFamily_of_eq hS heq, fun lam hlam => isCovariantAt_matern hμ hlam,
    fun t ht => matern_octave_step_d hd hq hc hμ ht, fun t ht => ?_⟩
  haveI := (hμ 0 t le_rfl ht.le).1
  refine density_of_radial_charFun (μ 0 t) (G := fun r => maternExponent q c (t * r))
    (fun ω => ?_) (integrable_moment_matern hq hc ht)
  rw [charFun_maternPyramid hμ le_rfl ht.le, zero_mul, maternExponent_zero, sub_zero]

end Pyramids
