/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.StratumOneExample
import Pyramids.Line.DiscreteCovarianceLine

/-!
# `prop:lindeberg-stratum-one`: Lindeberg's discrete scale space lies in the first stratum

Blueprint: `blueprint/src/parts/02-line.tex`, `prop:lindeberg-stratum-one`. Wave 3d: the three
declarations moved here from `PyramidsSkeleton.Ch02Line`, their statements unchanged.

## The route

* **(1).** The transform of the law on `hℤ` with the masses `e^{-u}I_{|n|}(u)` is read from the
  generating function `∑_{n ∈ ℤ} I_{|n|}(u) e^{inθ} = e^{u cos θ}` (`hasSum_besselI_exp`): the
  product of the two exponential series `e^{(u/2)e^{iθ}}` and `e^{(u/2)e^{-iθ}}`, regrouped by
  `n = a - b` along the bijection `(n, j) ↦ (j + n⁺, j + n⁻)` of `ℤ × ℕ` onto `ℕ × ℕ`. At `θ = 0`
  it gives the total mass `1`. The folded data `(0, uδ_h)` have the exponent `u(1 - cos hω)`.
* **(2).** The transforms give (I1), (I2), (ND) and the symmetry, and `lem:line-axioms-kernels`(2)
  the operators.
* **(3).** On `ℝ¹`, the image of `μ_{0,t}` has the transform of the data `(0, tσ_h)` of
  `prop:stratum-one-example` at `d = 1`, where `σ_h = ½(δ_{he₀} + δ_{-he₀})`; `thm:cited-A44`
  excludes every span, since `T_b(tσ_h)` misses the sphere of radius `h`. A span on `ℝ` gives one
  on `ℝ¹` (`isSemiSelfDecomposableWithSpan_map_lineEmb`). (A8 at `q^ℤ`) would make the kernels
  `q`-covariant (`lem:line-axioms-kernels`(3)), and after the relabelling of
  `lem:family-dilations`(3) a kernel would be semi-selfdecomposable with span `q`
  (`lem:discrete-covariance-levy`), which the first sentence excludes.
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X IsScaleCovariant IsKernelFamily SymLevyPair)
open scoped ENNReal Nat

/-! ## The generating function of `I_n` -/

/-- `I_m(u) = ∑_j (u/2)^{2j+m}/(j!(j+m)!)`. -/
theorem besselI_natCast_eq (m : ℕ) (u : ℝ) :
    besselI (m : ℝ) u =
      ∑' j : ℕ, (u / 2) ^ (2 * j + m) / ((j ! : ℝ) * ((j + m) ! : ℝ)) := by
  rw [besselI, Real.rpow_natCast, ← tsum_mul_left]
  congr 1
  funext j
  have hG : Real.Gamma ((m : ℝ) + j + 1) = ((j + m) ! : ℝ) := by
    rw [show (m : ℝ) + j + 1 = ((j + m : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  rw [hG, show (u ^ 2 / 4) ^ j = (u / 2) ^ (2 * j) by rw [pow_mul]; congr 1; ring, pow_add]
  ring

theorem besselI_natCast_nonneg (m : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ besselI (m : ℝ) u := by
  rw [besselI_natCast_eq]
  exact tsum_nonneg fun j => by positivity

/-- The bijection `(n, j) ↦ (j + n⁺, j + n⁻)` of `ℤ × ℕ` onto `ℕ × ℕ`. -/
def diagEquiv : ℤ × ℕ ≃ ℕ × ℕ where
  toFun p := (p.2 + p.1.toNat, p.2 + (-p.1).toNat)
  invFun p := ((p.1 : ℤ) - p.2, min p.1 p.2)
  left_inv p := by
    obtain ⟨n, j⟩ := p
    simp only [Prod.mk.injEq]
    constructor <;> omega
  right_inv p := by
    obtain ⟨a, b⟩ := p
    simp only [Prod.mk.injEq]
    constructor <;> omega

/-- **The generating function**: `∑_{n ∈ ℤ} I_{|n|}(u) e^{inθ} = e^{u cos θ}`. -/
theorem hasSum_besselI_exp (u θ : ℝ) :
    HasSum (fun n : ℤ => ((besselI (n.natAbs : ℝ) u : ℝ) : ℂ) * Complex.exp (n * θ * Complex.I))
      ((Real.exp (u * Real.cos θ) : ℝ) : ℂ) := by
  set x : ℂ := ((u / 2 : ℝ) : ℂ) with hx
  set F : ℕ → ℂ := fun a => (x * Complex.exp (θ * Complex.I)) ^ a / (a ! : ℂ) with hF
  set G : ℕ → ℂ := fun b => (x * Complex.exp (-θ * Complex.I)) ^ b / (b ! : ℂ) with hG
  have hnorm : ∀ (c : ℝ) (a : ℕ),
      ‖(x * Complex.exp (c * Complex.I)) ^ a / (a ! : ℂ)‖ = |u / 2| ^ a / (a ! : ℝ) := by
    intro c a
    rw [norm_div, norm_pow, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, hx,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
  have hFs : Summable fun a => ‖F a‖ := by
    simp_rw [hF, hnorm θ]
    exact Real.summable_pow_div_factorial _
  have hGs : Summable fun b => ‖G b‖ := by
    simp_rw [hG, show ∀ b : ℕ, (x * Complex.exp (-↑θ * Complex.I)) ^ b / (b ! : ℂ) =
      (x * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)) ^ b / (b ! : ℂ) from
        fun b => by push_cast; rfl,
      hnorm (-θ)]
    exact Real.summable_pow_div_factorial _
  -- the double series and its sum
  have hexp : ∀ w : ℂ, ∑' a : ℕ, w ^ a / (a ! : ℂ) = Complex.exp w := fun w => by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  have hprod : HasSum (fun p : ℕ × ℕ => F p.1 * G p.2) ((Real.exp (u * Real.cos θ) : ℝ) : ℂ) := by
    have h1 := (summable_mul_of_summable_norm hFs hGs).hasSum
    rw [← tsum_mul_tsum_of_summable_norm hFs hGs, hF, hG] at h1
    simp only at h1
    rw [hexp, hexp, ← Complex.exp_add] at h1
    have hval : Complex.exp (x * Complex.exp (θ * Complex.I) + x * Complex.exp (-θ * Complex.I)) =
        ((Real.exp (u * Real.cos θ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      rw [← mul_add, hx, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
      push_cast
      ring_nf
    rw [hval] at h1
    exact h1
  -- regrouped by `n = a - b`
  have hcomp := (diagEquiv.hasSum_iff).2 hprod
  have hterm : ∀ (n : ℤ) (j : ℕ), ((fun p : ℕ × ℕ => F p.1 * G p.2) ∘ diagEquiv) (n, j) =
      (((u / 2) ^ (2 * j + n.natAbs) / ((j ! : ℝ) * ((j + n.natAbs) ! : ℝ)) : ℝ) : ℂ) *
        Complex.exp (n * θ * Complex.I) := by
    intro n j
    simp only [Function.comp_apply, diagEquiv, Equiv.coe_fn_mk, hF, hG]
    rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    rcases le_or_gt 0 n with hn | hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      have h1 : (-(m : ℤ)).toNat = 0 := by omega
      simp only [Int.toNat_natCast, h1, add_zero, Int.natAbs_natCast]
      rw [hx]
      push_cast
      have hexp' : Complex.exp (((j : ℂ) + m) * (θ * Complex.I)) *
          Complex.exp ((j : ℂ) * (-θ * Complex.I)) = Complex.exp ((m : ℂ) * θ * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [← hexp']
      ring
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
      subst hm
      have h1 : (-(m : ℤ)).toNat = 0 := by omega
      simp only [h1, neg_neg, Int.toNat_natCast, add_zero, Int.natAbs_neg, Int.natAbs_natCast]
      rw [hx]
      push_cast
      have hexp' : Complex.exp ((j : ℂ) * (θ * Complex.I)) *
          Complex.exp (((j : ℂ) + m) * (-θ * Complex.I)) =
            Complex.exp (-(m : ℂ) * θ * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [← hexp']
      ring
  refine hcomp.prod_fiberwise fun n => ?_
  have hs := hcomp.summable.prod_factor n
  have hval : ∑' j : ℕ, ((fun p : ℕ × ℕ => F p.1 * G p.2) ∘ diagEquiv) (n, j) =
      ((besselI (n.natAbs : ℝ) u : ℝ) : ℂ) * Complex.exp (n * θ * Complex.I) := by
    simp_rw [hterm]
    rw [tsum_mul_right, besselI_natCast_eq, Complex.ofReal_tsum]
  rw [← hval]
  exact hs.hasSum

/-! ## (1) -/

/-- The masses `e^{-u}I_{|n|}(u)` sum to `1`. -/
theorem hasSum_lindebergMass (u : ℝ) :
    HasSum (fun n : ℤ => Real.exp (-u) * besselI (n.natAbs : ℝ) u) 1 := by
  have h := hasSum_besselI_exp u 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, Real.cos_zero]
    at h
  have h' := (Complex.hasSum_ofReal.1 h).mul_left (Real.exp (-u))
  rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h'

/-- **`prop:lindeberg-stratum-one`(1).** Lindeberg's kernel after the time `u ≥ 0` is a
probability law with transform `e^{-u(1 - cos hω)}`, compound Poisson with folded data
`(0, u δ_h)`. -/
theorem lindeberg_stratum_one_1 {h : ℝ} (hh : 0 < h) {u : ℝ} (hu : 0 ≤ u) :
    IsProbabilityMeasure (lindebergKernel h u) ∧
      (∀ ω : ℝ, charFun (lindebergKernel h u) ω =
        ((Real.exp (-(u * (1 - Real.cos (h * ω)))) : ℝ) : ℂ)) ∧
      ∃ Q : SymLevyPair, Q.a = 0 ∧ Q.ν = ENNReal.ofReal u • Measure.dirac h ∧
        IsFoldedData (lindebergKernel h u) Q := by
  set w : ℤ → ℝ := fun n => Real.exp (-u) * besselI (n.natAbs : ℝ) u with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => mul_nonneg (Real.exp_pos _).le (besselI_natCast_nonneg _ hu)
  have hsum : HasSum w 1 := hasSum_lindebergMass u
  have hprob : IsProbabilityMeasure (lindebergKernel h u) := by
    constructor
    rw [lindebergKernel, gridLaw, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hw0 hsum.summable, hsum.tsum_eq, ENNReal.ofReal_one]
  have hchar : ∀ ω : ℝ, charFun (lindebergKernel h u) ω =
      ((Real.exp (-(u * (1 - Real.cos (h * ω)))) : ℝ) : ℂ) := by
    intro ω
    have hint : Integrable (fun x : ℝ => Complex.exp (ω * x * Complex.I)) (lindebergKernel h u) :=
      Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
        (ae_of_all _ fun x => by rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I])
    rw [charFun_apply_real, lindebergKernel, gridLaw]
    rw [lindebergKernel, gridLaw] at hint
    rw [integral_sum_measure hint]
    have hterm : ∀ n : ℤ, ∫ x, Complex.exp (ω * x * Complex.I) ∂(ENNReal.ofReal
        (Real.exp (-u) * besselI (n.natAbs : ℝ) u) • Measure.dirac (h * n)) =
          ((Real.exp (-u) : ℝ) : ℂ) *
            (((besselI (n.natAbs : ℝ) u : ℝ) : ℂ) *
              Complex.exp (n * ((h * ω : ℝ) : ℂ) * Complex.I)) := by
      intro n
      rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal
        (mul_nonneg (Real.exp_pos _).le (besselI_natCast_nonneg _ hu)), Complex.real_smul]
      push_cast
      ring_nf
    simp_rw [hterm]
    rw [((hasSum_besselI_exp u (h * ω)).mul_left _).tsum_eq, ← Complex.ofReal_mul,
      ← Real.exp_add]
    congr 2
    ring
  refine ⟨hprob, hchar, ?_⟩
  -- the folded data `(0, uδ_h)`
  have hnot : h ∉ Iic (0 : ℝ) := by simpa using hh
  let Q : SymLevyPair :=
    { a := 0
      ν := ENNReal.ofReal u • Measure.dirac h
      a_nonneg := le_rfl
      ν_folded := by
        rw [ScaleSpace.IsFolded, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iic,
          indicator_of_notMem hnot, smul_zero]
      ν_integrable := by
        rw [lintegral_smul_measure, lintegral_dirac]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top }
  refine ⟨Q, rfl, rfl, fun ω => ?_⟩
  have hQ : Q.exponent ω = u * (1 - Real.cos (h * ω)) := by
    simp only [SymLevyPair.exponent, SymLevyPair.exponentL, Q, zero_mul, ENNReal.ofReal_zero,
      zero_add]
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, ← ENNReal.ofReal_mul hu,
      ENNReal.toReal_ofReal (mul_nonneg hu (sub_nonneg.2 (Real.cos_le_one _))), mul_comm ω h]
  rw [hchar ω, hQ]

/-! ## (2) -/

/-- **The kernels form a symmetric family.** -/
theorem lindeberg_isSymmetricFamily {h : ℝ} (hh : 0 < h) :
    IsSymmetricFamily (fun s t => lindebergKernel h (t - s)) := by
  have hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (lindebergKernel h (t - s)) :=
    fun s t _ hst => (lindeberg_stratum_one_1 hh (sub_nonneg.2 hst)).1
  have hchar : ∀ s t : ℝ, s ≤ t → ∀ ω : ℝ, charFun (lindebergKernel h (t - s)) ω =
      ((Real.exp (-((t - s) * (1 - Real.cos (h * ω)))) : ℝ) : ℂ) :=
    fun s t hst => (lindeberg_stratum_one_1 hh (sub_nonneg.2 hst)).2.1
  refine ⟨⟨hprob, fun t ht => ?_, fun r s t hr hrs hst => ?_, fun ω => ?_⟩,
    fun s t hs hst hdir => ?_, fun s t hs hst => ?_⟩
  · haveI := hprob t t ht le_rfl
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [hchar t t le_rfl ω, charFun_dirac]
    simp
  · haveI := hprob r t hr (hrs.trans hst)
    haveI := hprob s t (hr.trans hrs) hst
    haveI := hprob r s hr hrs
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_conv, hchar r t (hrs.trans hst) ω, hchar s t hst ω, hchar r s hrs ω,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  · have hc : Continuous fun p : ℝ × ℝ =>
        ((Real.exp (-((p.2 - p.1) * (1 - Real.cos (h * ω)))) : ℝ) : ℂ) := by fun_prop
    exact hc.continuousOn.congr fun p hp => hchar p.1 p.2 hp.2 ω
  · -- (ND): the transform at `ω = π/h` is `e^{-2(t - s)} ≠ 1`
    have h1 := hchar s t hst.le (Real.pi / h)
    simp only at hdir
    rw [hdir, charFun_dirac, mul_div_cancel₀ _ hh.ne', Real.cos_pi] at h1
    simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
    have h2 : Real.exp (-((t - s) * (1 - -1))) = 1 := by exact_mod_cast h1.symm
    have := (Real.exp_eq_one_iff _).1 h2
    linarith
  · haveI := hprob s t hs hst
    haveI : IsProbabilityMeasure ((lindebergKernel h (t - s)).map fun x => -x) :=
      Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_map_neg_real, hchar s t hst, hchar s t hst, mul_neg, Real.cos_neg]

/-- **`prop:lindeberg-stratum-one`(2).** The convolution operators satisfy (A1)–(A7) and (ND). -/
theorem lindeberg_stratum_one_2 {h : ℝ} (hh : 0 < h) :
    ∃ C : ScaleSpace.CascadeCore, IsKernelFamily C.Φ (fun s t => lindebergKernel h (t - s)) :=
  line_axioms_kernels_2_family _ (lindeberg_isSymmetricFamily hh)

/-! ## (3) -/

/-- **A span on `ℝ` is one on `ℝ¹`.** -/
theorem isSemiSelfDecomposableWithSpan_map_lineEmb {b : ℝ} {m : Measure ℝ}
    (h : IsSemiSelfDecomposableWithSpan b m) :
    IsSemiSelfDecomposableWithSpan b (m.map lineEmbL) := by
  obtain ⟨hb, ρ, ⟨hρ, hres⟩, hid⟩ := h
  refine ⟨hb, ρ.map lineEmbL, ⟨Measure.isProbabilityMeasure_map
    lineEmbL.continuous.measurable.aemeasurable, fun z => ?_⟩,
    isInfinitelyDivisible_map_lineEmb hid⟩
  rw [charFun_map_lineEmb, charFun_map_lineEmb, charFun_map_lineEmb, hres (z 0)]
  rfl

/-- `Ω_1(r) = cos r`: the unit sphere of `ℝ¹` is `{±e₀}`. -/
theorem sphereOmega_one (r : ℝ) : sphereOmega 1 r = Real.cos r := by
  haveI := isProbabilityMeasure_normSphere (d := 1) le_rfl
  haveI : IsProbabilityMeasure (sphereLaw 1 1) :=
    Measure.isProbabilityMeasure_map (continuous_const_smul (1 : ℝ)).aemeasurable
  have hsph : sphereLaw 1 1 {x : Rd 1 | ‖x‖ = 1} = 1 := by
    rw [sphereLaw_sphere le_rfl one_pos, if_pos rfl]
  have hmeas : MeasurableSet {x : Rd 1 | ‖x‖ = 1} := measurableSet_sphere 1
  have hae : ∀ᵐ η ∂(sphereLaw 1 1), Real.cos (r * η 0) = Real.cos r := by
    rw [ae_iff]
    refine measure_mono_null (t := {x : Rd 1 | ‖x‖ = 1}ᶜ) (fun η hη => ?_) ?_
    · intro h1
      apply hη
      have habs : |η 0| = 1 := by
        rw [← h1, ← Real.sqrt_sq (norm_nonneg η), norm_sq_rd1, Real.sqrt_sq_eq_abs]
      rcases abs_choice (η 0) with h2 | h2
      · rw [← h2, habs, mul_one]
      · rw [show η 0 = -1 by linarith, mul_neg_one, Real.cos_neg]
    · rw [measure_compl hmeas (measure_ne_top _ _), hsph, measure_univ, tsub_self]
  rw [sphereOmega, integral_congr_ae hae, integral_const, probReal_univ, one_smul]

/-- **No span on `ℝ¹`** (`thm:cited-A44`): the image of `μ_{0,t}`, `t > 0`, has the data
`(0, tσ_h)`, and `T_b(tσ_h)` misses the sphere of radius `h` that `tσ_h` charges. -/
theorem lindeberg_not_semi_lineEmb {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : 0 < t) (b : ℝ) :
    ¬ IsSemiSelfDecomposableWithSpan b ((lindebergKernel h t).map lineEmbL) := by
  intro hb
  have hfam := lindeberg_isSymmetricFamily hh
  haveI := (lindeberg_stratum_one_1 hh ht.le).1
  haveI : IsProbabilityMeasure ((lindebergKernel h t).map lineEmbL) :=
    Measure.isProbabilityMeasure_map lineEmbL.continuous.measurable.aemeasurable
  have hid : IsInfinitelyDivisible ((lindebergKernel h t).map lineEmbL) := by
    have h1 := isLawHemigroup_line_infinitelyDivisible hfam.1 le_rfl ht.le
    simp only [sub_zero] at h1
    exact isInfinitelyDivisible_map_lineEmb h1
  have hdata : IsSymData ((lindebergKernel h t).map lineEmbL) (sphereData hh t) := by
    intro z
    rw [charFun_map_lineEmb, (lindeberg_stratum_one_1 hh ht.le).2.1, sphereData_exponent hh ht.le,
      sphereOmega_one]
    have hnz : ‖z‖ = |z 0| := by
      rw [← Real.sqrt_sq (norm_nonneg z), norm_sq_rd1, Real.sqrt_sq_eq_abs]
    rw [hnz, ← abs_of_pos hh, ← abs_mul, Real.cos_abs, abs_of_pos hh]
  have hle := (cited_A44 hb.1 _ hid _ (SymLevyData.hasTriplet hdata)).1 hb
  change ENNReal.ofReal t • sphereLaw 1 h ≤ (ENNReal.ofReal t • sphereLaw 1 h).map
    (fun x => b • x) at hle
  have hb0 : 0 < b := by linarith [hb.1]
  have hpre : (fun x : Rd 1 => b • x) ⁻¹' {x : Rd 1 | ‖x‖ = h} = {x : Rd 1 | ‖x‖ = h / b} := by
    ext x
    simp only [mem_preimage, mem_setOf_eq, norm_smul, Real.norm_of_nonneg hb0.le]
    rw [eq_div_iff hb0.ne', mul_comm]
  have hne : h ≠ h / b := by
    intro heq
    rw [eq_div_iff hb0.ne'] at heq
    nlinarith [hb.1]
  have h1 := Measure.le_iff'.1 hle {x : Rd 1 | ‖x‖ = h}
  rw [Measure.map_apply (continuous_const_smul b).measurable (measurableSet_sphere h), hpre] at h1
  have hl : (ENNReal.ofReal t • sphereLaw 1 h) {x : Rd 1 | ‖x‖ = h} = ENNReal.ofReal t := by
    rw [Measure.smul_apply, sphereLaw_sphere le_rfl hh, if_pos rfl, smul_eq_mul, mul_one]
  have hr : (ENNReal.ofReal t • sphereLaw 1 h) {x : Rd 1 | ‖x‖ = h / b} = 0 := by
    rw [Measure.smul_apply, sphereLaw_sphere le_rfl hh, if_neg hne, smul_eq_mul, mul_zero]
  rw [hl, hr, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
  linarith

/-- **`prop:lindeberg-stratum-one`(3).** For no `q > 1` and `t > 0` is `μ_{0,t}`
semi-selfdecomposable with span `q`, and for no `q > 1` does the family satisfy (A8 at `q^ℤ`). -/
theorem lindeberg_stratum_one_3 {h : ℝ} (hh : 0 < h) {q : ℝ} (hq : 1 < q) :
    (∀ t : ℝ, 0 < t → ¬ IsSemiSelfDecomposableWithSpan q (lindebergKernel h t)) ∧
      ∀ (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ),
        IsKernelFamily Φ (fun s t => lindebergKernel h (t - s)) →
          ¬ IsScaleCovariant Φ (qPowers q) S := by
  refine ⟨fun t ht hs => lindeberg_not_semi_lineEmb hh ht q
    (isSemiSelfDecomposableWithSpan_map_lineEmb hs), fun Φ S hker hcov => ?_⟩
  have hq0 : 0 < q := by linarith
  have hmem : q ∈ qPowers q := ⟨1, zpow_one q⟩
  have hb : IsIncreasingBijection (S q) :=
    ⟨hcov.S_mapsTo q hq0 hmem, hcov.S_strictMonoOn q hq0 hmem, hcov.S_surjOn q hq0 hmem⟩
  have hfam := lindeberg_isSymmetricFamily hh
  -- the kernels are `q`-covariant (`lem:line-axioms-kernels`(3)), also on `ℝ¹`
  have hcovL : IsCovariantAt (fun s t => lindebergKernel h (t - s)) q (S q) :=
    (isCovariantAt_iff_map_mul _ q (S q)).2 ⟨hb,
      (line_axioms_kernels_3 Φ _ hker hq0 (S q) hb).1 (hcov.scale q hq0 hmem)⟩
  have hsym1 := isSymmetricFamily_lineEmb hfam
  have hcov1 := isCovariantAt_lineEmb hcovL
  -- the relabelling of `lem:family-dilations`(3), then `lem:discrete-covariance-levy`
  obtain ⟨χ, hχ, -, hχS⟩ := family_dilations_3_exists le_rfl _ hsym1 hq (S q) hcov1
  obtain ⟨ψ, hψ, hψχ, hχψ⟩ := incBij_inverse ((isGauge_iff_isIncreasingBijection χ).1 hχ)
  obtain ⟨hsym', hcov'⟩ := family_dilations_3_relabel _ hsym1 hq (S q) hcov1 χ ψ hχ hχS hψχ hχψ
  have hsemi := discrete_covariance_levy_semi le_rfl _ hsym' hq hcov' 1 zero_le_one
  simp only [relabel, incBij_zero hψ, sub_zero] at hsemi
  exact lindeberg_not_semi_lineEmb hh (incBij_pos hψ one_pos) q hsemi

end Pyramids
