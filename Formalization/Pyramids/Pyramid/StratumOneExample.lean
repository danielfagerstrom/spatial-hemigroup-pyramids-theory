/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.StratumTwoExample
import Pyramids.Pyramid.LatticeStrata
import Pyramids.Pyramid.DiscreteCovarianceLevy
import Pyramids.Pyramid.WhatDoesNotLiftChain
import Pyramids.Cited.A44
import AffineHemigroup.OriginLowerBound
import AffineHemigroup.MaternLaw

/-!
# `prop:stratum-one-example`: an isotropic family in stratum 1

Blueprint: `blueprint/src/parts/03-pyramid.tex`. Moved from `PyramidsSkeleton.Ch03Pyramid` in wave
3d, unchanged in statement and name.

The data `(0, tσ_h)` (`sphereData`) have the exponent `t(1 - Ω_d(h|ω|))`, after the rotation of
`ω` to `|ω|e₀` (`integral_cos_sphereLaw`). `thm:lattice-strata`(1) makes any laws with these
exponents an isotropic family; the kernel is the Poisson mixture of the convolution powers of
`σ_h` (`charFun_poissonWalk`). No kernel `μ_t`, `t > 0`, is semi-selfdecomposable: its Lévy
measure `tσ_h` gives the sphere of radius `h` the mass `t`, which `D_b(tσ_h) = tσ_{bh}` does not,
against `thm:cited-A44`. Covariance under some `λ ≠ 1` would give, through
`lem:family-dilations`(2)–(3) and `lem:discrete-covariance-levy`, a semi-selfdecomposable kernel.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (convPow)
open scoped ENNReal RealInnerProductSpace Topology Nat

variable {d : ℕ}

/-! ## The law on one sphere -/

theorem one_le_of_neZero [NeZero d] : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)

/-- `σ_r` is symmetric. -/
theorem sphereLaw_map_neg (r : ℝ) : (sphereLaw d r).map (fun x => -x) = sphereLaw d r := by
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  have h := sphereLaw_preimage_isometry (LinearIsometryEquiv.neg ℝ (E := Rd d)) r hs
  rwa [coe_neg_isometry] at h

/-- `σ_r` is invariant under `O(d)`. -/
theorem sphereLaw_rotationInvariant (r : ℝ) : IsRotationInvariant (sphereLaw d r) := by
  intro Q hQ
  ext s hs
  rw [push, Measure.map_apply (lin Q).continuous.measurable hs]
  exact sphereLaw_preimage_isometry (orthIsometry hQ) r hs

/-- `σ_r` puts no mass at `0`, for `r ≠ 0`. -/
theorem sphereLaw_zero (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) : sphereLaw d r {0} = 0 := by
  have h := sphereLaw_sphere hd hr 0
  rw [if_neg hr.ne'] at h
  have hset : ({0} : Set (Rd d)) = {x : Rd d | ‖x‖ = 0} := by
    ext x; simp
  rw [hset, h]

/-- **The rotation to the first axis**: `∫ cos⟨x, ω⟩ σ_h(dx) = Ω_d(h|ω|)`. -/
theorem integral_cos_sphereLaw [NeZero d] (h : ℝ) (ω : Rd d) :
    ∫ x, Real.cos ⟪x, ω⟫ ∂sphereLaw d h = sphereOmega d (h * ‖ω‖) := by
  obtain ⟨R, hR⟩ := exists_isometry_norm_smul ω
  set e0 : Rd d := ebasis (0 : Fin d) with he0
  set g : Rd d → ℝ := fun v => Real.cos ⟪h • v, ‖ω‖ • e0⟫ with hg
  have hgc : Continuous g := by fun_prop
  have hinner : ∀ u : Rd d, ⟪h • u, ω⟫ = ⟪h • R.symm u, ‖ω‖ • e0⟫ := by
    intro u
    symm
    rw [← LinearIsometryEquiv.inner_map_map R, LinearIsometryEquiv.map_smul,
      LinearIsometryEquiv.apply_symm_apply, hR]
  have hlhs : ∫ x, Real.cos ⟪x, ω⟫ ∂sphereLaw d h = ∫ u, g u ∂normSphere d := by
    rw [sphereLaw, integral_map (continuous_const_smul h).aemeasurable
      (by fun_prop : Continuous fun x : Rd d => Real.cos ⟪x, ω⟫).aestronglyMeasurable]
    have h1 : ∀ u : Rd d, Real.cos ⟪h • u, ω⟫ = g (R.symm u) := fun u => by
      rw [hinner u]
    simp_rw [h1]
    rw [← integral_map R.symm.continuous.aemeasurable hgc.aestronglyMeasurable,
      normSphere_map_isometry]
  have hrhs : sphereOmega d (h * ‖ω‖) = ∫ u, g u ∂normSphere d := by
    rw [sphereOmega, sphereLaw, integral_map (continuous_const_smul (1 : ℝ)).aemeasurable
      (by fun_prop : Continuous fun η : Rd d => Real.cos (h * ‖ω‖ * η 0)).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [hg, he0, ebasis, one_smul, inner_smul_left, inner_smul_right,
      EuclideanSpace.inner_single_right, conj_trivial, one_mul]
    ring_nf
  rw [hlhs, hrhs]

/-- The transform of `σ_h` is `Ω_d(h|ω|)`. -/
theorem charFun_sphereLaw [NeZero d] (h : ℝ) (ω : Rd d) :
    charFun (sphereLaw d h) ω = ((sphereOmega d (h * ‖ω‖) : ℝ) : ℂ) := by
  haveI := isProbabilityMeasure_normSphere (d := d) one_le_of_neZero
  haveI : IsProbabilityMeasure (sphereLaw d h) :=
    Measure.isProbabilityMeasure_map (continuous_const_smul h).aemeasurable
  rw [charFun_of_symm _ (sphereLaw_map_neg h), integral_cos_sphereLaw]

/-! ## The data -/

/-- **The data `(0, tσ_h)`** of `prop:stratum-one-example`. -/
noncomputable def sphereData [NeZero d] {h : ℝ} (hh : 0 < h) (t : ℝ) : SymLevyData d where
  A := 0
  ν := ENNReal.ofReal t • sphereLaw d h
  A_posSemidef := Matrix.PosSemidef.zero
  ν_zero := by rw [Measure.smul_apply, sphereLaw_zero one_le_of_neZero hh, smul_zero]
  ν_integrable := by
    have hg : Measurable fun r : ℝ => ENNReal.ofReal (min (r ^ 2) 1) := by fun_prop
    rw [lintegral_smul_measure, lintegral_sphereLaw_radial one_le_of_neZero h hg]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  ν_symm := by rw [Measure.map_smul, sphereLaw_map_neg]

theorem sphereData_exponent [NeZero d] {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : 0 ≤ t) (ω : Rd d) :
    (sphereData hh t).exponent ω = t * (1 - sphereOmega d (h * ‖ω‖)) := by
  haveI := isProbabilityMeasure_normSphere (d := d) one_le_of_neZero
  haveI : IsProbabilityMeasure (sphereLaw d h) :=
    Measure.isProbabilityMeasure_map (continuous_const_smul h).aemeasurable
  have hint : Integrable (fun x : Rd d => Real.cos ⟪ω, x⟫) (sphereLaw d h) :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  simp only [SymLevyData.exponent, pairExponent, sphereData, quad_zero, zero_add,
    integral_smul_measure, ENNReal.toReal_ofReal ht, smul_eq_mul]
  rw [integral_sub (integrable_const 1) hint, integral_const, probReal_univ, one_smul]
  have hcomm : ∀ x : Rd d, ⟪ω, x⟫ = ⟪x, ω⟫ := fun x => real_inner_comm x ω
  simp_rw [hcomm]
  rw [integral_cos_sphereLaw]

/-- **`prop:stratum-one-example`, the data.** `(0, tσ_h)` are symmetric Lévy data with the
exponent `t(1 - Ω_d(h|ω|))`. -/
theorem stratum_one_example_data [NeZero d] {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : 0 ≤ t) :
    ∃ E : SymLevyData d, E.A = 0 ∧ E.ν = ENNReal.ofReal t • sphereLaw d h ∧
      ∀ ω : Rd d, E.exponent ω = t * (1 - sphereOmega d (h * ‖ω‖)) :=
  ⟨sphereData hh t, rfl, rfl, sphereData_exponent hh ht⟩

/-! ## The Poisson random walk -/

/-- **The law of a random walk with steps `σ_h`, after a Poisson number of steps with mean `t`**:
`∑_k e^{-t}t^k/k! · σ_h^{*k}`. -/
noncomputable def poissonWalk (d : ℕ) (h t : ℝ) : Measure (Rd d) :=
  Measure.sum fun k : ℕ =>
    ENNReal.ofReal (Real.exp (-t) * t ^ k / (k.factorial : ℝ)) • convPow (sphereLaw d h) k

theorem poissonWalk_univ [NeZero d] (h : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    poissonWalk d h t univ = 1 := by
  haveI := isProbabilityMeasure_normSphere (d := d) one_le_of_neZero
  haveI : IsProbabilityMeasure (sphereLaw d h) :=
    Measure.isProbabilityMeasure_map (continuous_const_smul h).aemeasurable
  rw [poissonWalk, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, convPow_univ, measure_univ, one_pow, smul_eq_mul, mul_one]
  have hterm : ∀ k : ℕ, ENNReal.ofReal (Real.exp (-t) * t ^ k / (k.factorial : ℝ)) =
      ENNReal.ofReal (Real.exp (-t) / (k ! : ℝ)) * ENNReal.ofReal t ^ k := fun k => by
    rw [← ENNReal.ofReal_pow ht, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [hterm]
  rw [tsum_poisson_mul_pow t ht, ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]

theorem isProbabilityMeasure_poissonWalk [NeZero d] (h : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityMeasure (poissonWalk d h t) := ⟨poissonWalk_univ h ht⟩

/-- **The transform of the walk**: `e^{-t} exp(t σ̂_h(ω)) = e^{-t(1 - Ω_d(h|ω|))}`. -/
theorem charFun_poissonWalk [NeZero d] (h : ℝ) {t : ℝ} (ht : 0 ≤ t) (ω : Rd d) :
    charFun (poissonWalk d h t) ω =
      ((Real.exp (-(t * (1 - sphereOmega d (h * ‖ω‖)))) : ℝ) : ℂ) := by
  haveI := isProbabilityMeasure_normSphere (d := d) one_le_of_neZero
  haveI : IsProbabilityMeasure (sphereLaw d h) :=
    Measure.isProbabilityMeasure_map (continuous_const_smul h).aemeasurable
  haveI := isProbabilityMeasure_poissonWalk (d := d) h ht
  have hint : Integrable (fun x : Rd d => Complex.exp (⟪x, ω⟫ * Complex.I)) (poissonWalk d h t) :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  set c : ℂ := charFun (sphereLaw d h) ω with hc
  rw [charFun_apply, poissonWalk, integral_sum_measure hint]
  have hterm : ∀ k : ℕ, ∫ x, Complex.exp (⟪x, ω⟫ * Complex.I) ∂(ENNReal.ofReal
      (Real.exp (-t) * t ^ k / (k.factorial : ℝ)) • convPow (sphereLaw d h) k)
      = ((Real.exp (-t) : ℝ) : ℂ) * (((t : ℂ) * c) ^ k / (k ! : ℂ)) := by
    intro k
    rw [integral_smul_measure, ← charFun_apply, charFun_convPow,
      ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    push_cast
    ring
  simp_rw [hterm]
  have hexp : ∑' k : ℕ, ((t : ℂ) * c) ^ k / (k ! : ℂ) = Complex.exp ((t : ℂ) * c) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  rw [tsum_mul_left, hexp, hc,
    charFun_sphereLaw, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    ← Real.exp_add]
  congr 2
  ring

/-! ## `prop:stratum-one-example` -/

/-- **`prop:stratum-one-example`.** Laws with `Ψ_t(ω) = t(1 - Ω_d(h|ω|))` exist, and any such laws
form an isotropic family whose kernel `μ_t` is the law of a random walk with steps `σ_h` after a
Poisson number of steps with mean `t`; no `μ_t`, `t > 0`, is semi-selfdecomposable, and the family
is `λ`-covariant for no `λ ≠ 1`. -/
theorem stratum_one_example [NeZero d] {h : ℝ} (hh : 0 < h) :
    (∃ μ : ℝ → ℝ → Measure (Rd d),
        IsExponentLaws (fun t ω => t * (1 - sphereOmega d (h * ‖ω‖))) μ) ∧
      ∀ μ : ℝ → ℝ → Measure (Rd d),
        IsExponentLaws (fun t ω => t * (1 - sphereOmega d (h * ‖ω‖))) μ →
          IsIsotropicFamily μ ∧
          (∀ t : ℝ, 0 ≤ t → μ 0 t = Measure.sum fun k : ℕ =>
            ENNReal.ofReal (Real.exp (-t) * t ^ k / (k.factorial : ℝ)) •
              convPow (sphereLaw d h) k) ∧
          (∀ t : ℝ, 0 < t → ¬ IsSemiSelfDecomposable (μ 0 t)) ∧
          ∀ lam : ℝ, 0 < lam → lam ≠ 1 → ¬ IsLamCovariant μ lam := by
  have hd : 1 ≤ d := one_le_of_neZero
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  haveI : IsProbabilityMeasure (sphereLaw d h) :=
    Measure.isProbabilityMeasure_map (continuous_const_smul h).aemeasurable
  set Ψ : ℝ → Rd d → ℝ := fun t ω => t * (1 - sphereOmega d (h * ‖ω‖)) with hΨ
  set D : ℝ → SymLevyData d := fun t => sphereData hh t with hD
  -- the two readings of the laws agree, `s, t ≥ 0` being the only labels read
  have hiff : ∀ μ : ℝ → ℝ → Measure (Rd d),
      IsExponentLaws Ψ μ ↔ IsExponentLaws (fun t ω => (D t).exponent ω) μ := by
    intro μ
    refine ⟨fun hμ s t hs hst => ?_, fun hμ s t hs hst => ?_⟩
    · obtain ⟨hp, hc⟩ := hμ s t hs hst
      exact ⟨hp, fun ω => by
        rw [hc ω]
        simp only [hD, hΨ, sphereData_exponent hh (hs.trans hst), sphereData_exponent hh hs]⟩
    · obtain ⟨hp, hc⟩ := hμ s t hs hst
      exact ⟨hp, fun ω => by
        rw [hc ω]
        simp only [hD, hΨ, sphereData_exponent hh (hs.trans hst), sphereData_exponent hh hs]⟩
  -- the hypotheses of `thm:lattice-strata`(1)
  have hsph : sphereLaw d h univ = 1 := measure_univ
  obtain ⟨hex, hfam⟩ := lattice_strata_1_converse hd D (fun _ => 0)
    (fun t _ => by simp [hD, sphereData])
    (fun t _ Q hQ => by
      change push Q (ENNReal.ofReal t • sphereLaw d h) = ENNReal.ofReal t • sphereLaw d h
      rw [push, Measure.map_smul]
      exact congrArg _ (sphereLaw_rotationInvariant h Q hQ))
    (fun s t hs hst => by
      refine ⟨le_rfl, ?_, fun heq => ?_⟩
      · change ENNReal.ofReal s • sphereLaw d h ≤ ENNReal.ofReal t • sphereLaw d h
        rw [Measure.le_iff]
        intro A _
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
      · have hν := congrArg (fun m : Measure (Rd d) => m univ) (congrArg Prod.snd heq)
        change (ENNReal.ofReal s • sphereLaw d h) univ = (ENNReal.ofReal t • sphereLaw d h) univ
          at hν
        simp only [Measure.smul_apply, hsph, smul_eq_mul, mul_one] at hν
        have := (ENNReal.ofReal_eq_ofReal_iff hs (hs.trans hst.le)).1 hν
        linarith)
    (fun ω => by
      have hc : Continuous fun t : ℝ => t * (1 - sphereOmega d (h * ‖ω‖)) := by fun_prop
      exact hc.continuousOn.congr fun t ht => sphereData_exponent hh ht ω)
  refine ⟨hex.imp fun μ hμ => (hiff μ).2 hμ, fun μ hμ => ?_⟩
  have hiso := hfam μ ((hiff μ).1 hμ)
  have hsym := isotropicFamily_isSymmetricFamily μ hiso
  -- the kernel `μ_t` has the data `(0, tσ_h)`
  have hdata : ∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t) := fun t ht ω => by
    rw [(hμ 0 t le_rfl ht).2 ω, hD, sphereData_exponent hh ht]
    simp [hΨ]
  -- no kernel is semi-selfdecomposable (`thm:cited-A44`)
  have hnotsemi : ∀ t : ℝ, 0 < t → ¬ IsSemiSelfDecomposable (μ 0 t) := by
    rintro t ht ⟨b, hb⟩
    haveI := hsym.1.isProbability 0 t le_rfl ht.le
    have hid := (family_structure_id hd μ hsym 0 t le_rfl ht.le).1
    have hle := (cited_A44 hb.1 (μ 0 t) hid _ (SymLevyData.hasTriplet (hdata t ht.le))).1 hb
    change ENNReal.ofReal t • sphereLaw d h ≤ (ENNReal.ofReal t • sphereLaw d h).map
      (fun x => b • x) at hle
    have hb0 : 0 < b := by linarith [hb.1]
    have hpre : (fun x : Rd d => b • x) ⁻¹' {x : Rd d | ‖x‖ = h} = {x : Rd d | ‖x‖ = h / b} := by
      ext x
      simp only [mem_preimage, mem_setOf_eq, norm_smul, Real.norm_of_nonneg hb0.le]
      rw [eq_div_iff hb0.ne', mul_comm]
    have hne : h ≠ h / b := by
      intro heq
      rw [eq_div_iff hb0.ne'] at heq
      nlinarith [hb.1]
    have h1 := Measure.le_iff'.1 hle {x : Rd d | ‖x‖ = h}
    rw [Measure.map_apply (continuous_const_smul b).measurable (measurableSet_sphere h), hpre]
      at h1
    have hl : (ENNReal.ofReal t • sphereLaw d h) {x : Rd d | ‖x‖ = h} = ENNReal.ofReal t := by
      rw [Measure.smul_apply, sphereLaw_sphere hd hh, if_pos rfl, smul_eq_mul, mul_one]
    have hr : (ENNReal.ofReal t • sphereLaw d h) {x : Rd d | ‖x‖ = h / b} = 0 := by
      rw [Measure.smul_apply, sphereLaw_sphere hd hh, if_neg hne, smul_eq_mul, mul_zero]
    rw [hl, hr, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
    linarith
  refine ⟨hiso, fun t ht => ?_, hnotsemi, fun lam hlam hne hcov => ?_⟩
  · -- the Poisson random walk
    haveI := hsym.1.isProbability 0 t le_rfl ht
    haveI := isProbabilityMeasure_poissonWalk (d := d) h ht
    change μ 0 t = poissonWalk d h t
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [hdata t ht ω, charFun_poissonWalk h ht, hD, sphereData_exponent hh ht]
  · -- `λ`-covariance for some `λ ≠ 1` gives a ratio `q > 1` (`lem:family-dilations`(2))
    obtain ⟨q, hq, S, hS⟩ : ∃ q : ℝ, 1 < q ∧ IsLamCovariant μ q := by
      rcases (family_dilations_2 hd μ hsym).2 with h1 | ⟨q, hq, hG⟩ | hG
      · have hmem : lam ∈ covariantDilations μ := ⟨hlam, hcov⟩
        rw [h1] at hmem
        exact absurd hmem hne
      · have hmem : q ∈ covariantDilations μ := by
          rw [hG]; exact ⟨1, zpow_one q⟩
        exact ⟨q, hq, hmem.2⟩
      · have hmem : (2 : ℝ) ∈ covariantDilations μ := by
          rw [hG]; norm_num
        exact ⟨2, by norm_num, hmem.2⟩
    -- the relabelled family has `S_q t = qt` (`lem:family-dilations`(3))
    obtain ⟨χ, hχ, -, hχS⟩ := family_dilations_3_exists hd μ hsym hq S hS
    obtain ⟨ψ, hψ, hψχ, hχψ⟩ := incBij_inverse ((isGauge_iff_isIncreasingBijection χ).1 hχ)
    obtain ⟨hsym', hcov'⟩ := family_dilations_3_relabel μ hsym hq S hS χ ψ hχ hχS hψχ hχψ
    -- its kernels are semi-selfdecomposable (`lem:discrete-covariance-levy`), and they are kernels
    -- of the family
    have hsemi := discrete_covariance_levy_semi hd (relabel μ ψ) hsym' hq hcov' 1 zero_le_one
    have hrel : relabel μ ψ 0 1 = μ 0 (ψ 1) := by
      simp only [relabel, incBij_zero hψ]
    rw [hrel] at hsemi
    exact hnotsemi (ψ 1) (incBij_pos hψ one_pos) ⟨q, hsemi⟩

end Pyramids
