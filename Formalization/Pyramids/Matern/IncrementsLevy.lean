/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.IncrementsBernstein
import Pyramids.Pyramid.FamilyStructure
import Pyramids.LineAppendix.MaternLine
import AffineHemigroup.StageAtom

/-!
# `prop:matern-increments`(2)–(3): the laws and their Lévy measures

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:matern-increments`. Phase 5, wave 3b. The
five declarations of clauses (2) and (3) other than the Thorin clause and the sum moved here from
`PyramidsSkeleton.Ch04Matern`. Their conclusions are unchanged; `_2` takes no `1 ≤ d`,
`_2_levy_exists` no `1 ≤ d`, `0 < γ`, `γ < β`, and `_3_levy_exists` none of its hypotheses, which
their proofs do not read (2026-11-15, a strengthening).

* **The measure `2∫_a^b L_r dr/r`** (`incLevy`) is the image of `(2/r) dr` on `(a,b]` times the law
  of `√(2X) Z` under `(r, x) ↦ rx`; its value on a Borel set is the setwise integral of the node
  (`incLevy_apply`), and its integrals are iterated (`lintegral_incLevy`). It is symmetric (each
  `L_r` has an even transform), it does not charge `0` in `d ≥ 1` (each `L_r` has a density), its
  mass is `2 log(b/a)`, its second moment is at most `2b²` times that of `L_1`, finite as that of
  `√(2X) Z` (Gaussian second moment and the mean of `X`), and
  `∫(1 - cos⟨ω,x⟩) = log(1 + b²|ω|²) - log(1 + a²|ω|²)`: `∫(1 - cos) dL_r` is
  `r²|ω|²/(1 + r²|ω|²)` from the transform of `L_r`, and the `r`-integral is the fundamental
  theorem of calculus.
* **Clause (2).** The mixture has the transform `(1 + γ|ω|²)/(1 + β|ω|²)`; with
  `ν = 2∫_{√γ}^{√β} L_r dr/r`, the compound Poisson law of `ν` has the transform
  `exp(-∫(1 - cos) dν)` (the affine export's `charFun_cpLaw_of_symm`), the same, and `(0, ν, 0)` is
  a generating triplet (`lkExponent_of_symm_general`).
* **Clause (3).** `ν_{s,t} = ∑ᵢ 2∫_{csq^{-i}}^{ctq^{-i}} L_r dr/r` (`incLevySum`), with
  `∫(1 - cos) dν_{s,t} = F_q(t|ω|) - F_q(s|ω|)` by Tonelli's theorem. `(0, ν_{s,t}, 0)` is a
  generating triplet of `μ_{s,t}`, and `μ_{s,t}` is infinitely divisible because the law of A39(iii)
  with that triplet has its transform (`isInfinitelyDivisible_of_hasTriplet`).

**What it reaches.** Clause (3)'s infinite divisibility reads A39(iii)
(`levy_khintchine_converse`); everything else prints Lean core.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## Transforms and symmetry -/

/-- The real part of a transform is the integral of the cosine. -/
theorem re_charFun (L : Measure (Rd d)) [IsFiniteMeasure L] (ω : Rd d) :
    (charFun L ω).re = ∫ x, Real.cos ⟪x, ω⟫ ∂L := by
  have hint : Integrable (fun x : Rd d => Complex.exp (⟪x, ω⟫ * Complex.I)) L :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply, ← RCLike.re_to_complex, ← integral_re hint]
  congr 1
  funext x
  simp [Complex.exp_ofReal_mul_I_re]

/-- A probability measure with an even transform is symmetric. -/
theorem map_neg_eq_of_charFun_even (L : Measure (Rd d)) [IsProbabilityMeasure L]
    (h : ∀ ω, charFun L (-ω) = charFun L ω) : L.map (fun x => -x) = L := by
  have hneg : (fun x : Rd d => -x) = (LinearIsometryEquiv.neg ℝ : Rd d ≃ₗᵢ[ℝ] Rd d) := by
    rw [LinearIsometryEquiv.coe_neg]
  haveI : IsProbabilityMeasure (L.map (fun x => -x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [hneg, charFun_map_isometry]
  simpa using h ω

theorem maternStep_map_neg (r : ℝ) : (maternStep d r).map (fun x => -x) = maternStep d r := by
  haveI := (charFun_maternStep (d := d) r 0).1
  refine map_neg_eq_of_charFun_even _ fun ω => ?_
  rw [(charFun_maternStep r (-ω)).2, (charFun_maternStep r ω).2, norm_neg]

theorem maternStep_singleton_zero (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) :
    maternStep d r {0} = 0 := by
  haveI : Nontrivial (Rd d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  rw [(bessel_profile_1 hd hr).2.2.1, withDensity_apply _ (measurableSet_singleton 0)]
  exact setLIntegral_measure_zero _ _ (measure_singleton 0)

/-- `∫(1 - cos⟨ω,x⟩) L_r(dx) = r²|ω|²/(1 + r²|ω|²)`. -/
theorem lintegral_one_sub_cos_maternStep (r : ℝ) (ω : Rd d) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) ∂(maternStep d r) =
      ENNReal.ofReal (r ^ 2 * ‖ω‖ ^ 2 / (1 + r ^ 2 * ‖ω‖ ^ 2)) := by
  obtain ⟨hp, hc⟩ := charFun_maternStep (d := d) r ω
  haveI := hp
  have hcos : Integrable (fun x : Rd d => Real.cos ⟪x, ω⟫) (maternStep d r) :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hcomm : ∀ x : Rd d, ⟪ω, x⟫ = ⟪x, ω⟫ := fun x => real_inner_comm x ω
  simp_rw [hcomm]
  have hint : Integrable (fun x : Rd d => 1 - Real.cos ⟪x, ω⟫) (maternStep d r) :=
    (integrable_const 1).sub hcos
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => by simp only [Pi.zero_apply]; linarith [Real.cos_le_one ⟪x, ω⟫])]
  congr 1
  have hre := re_charFun (maternStep d r) ω
  rw [hc, Complex.ofReal_re] at hre
  rw [integral_sub (integrable_const 1) hcos, ← hre]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  have : 0 < 1 + r ^ 2 * ‖ω‖ ^ 2 := by positivity
  field_simp
  ring

/-- If `∫(1 - cos) dν` is `v` as a lower integral, it is `v` as a Bochner integral. -/
theorem integral_one_sub_cos_of_lintegral (ν : Measure (Rd d)) (ω : Rd d) {v : ℝ} (hv : 0 ≤ v)
    (h : ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) ∂ν = ENNReal.ofReal v) :
    ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂ν = v := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by
    simp only [Pi.zero_apply]; linarith [Real.cos_le_one ⟪ω, x⟫]) (by fun_prop), h,
    ENNReal.toReal_ofReal hv]

/-! ## The measure `2∫_a^b L_r dr/r` -/

instance isProbabilityMeasure_gammaGaussLaw_one : IsProbabilityMeasure (gammaGaussLaw d 1) := by
  haveI := isProbabilityMeasure_gammaMeasure (a := 1) (r := 1) one_pos one_pos
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- **`2∫_a^b L_r dr/r`**: the image of `(2/r) dr` on `(a,b]` times the law of `√(2X) Z` under
`(r, x) ↦ rx`. -/
noncomputable def incLevy (d : ℕ) (a b : ℝ) : Measure (Rd d) :=
  (((volume.restrict (Ioc a b)).withDensity fun r => ENNReal.ofReal (2 / r)).prod
    (gammaGaussLaw d 1)).map fun p => p.1 • p.2

theorem lintegral_incLevy (a b : ℝ) {g : Rd d → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(incLevy d a b) =
      ∫⁻ r in Ioc a b, ENNReal.ofReal (2 / r) * ∫⁻ x, g x ∂(maternStep d r) := by
  have hm : Measurable fun p : ℝ × Rd d => p.1 • p.2 := by fun_prop
  have hmeas : Measurable fun r : ℝ => ∫⁻ y, g (r • y) ∂(gammaGaussLaw d 1) :=
    Measurable.lintegral_prod_right' (f := fun p : ℝ × Rd d => g (p.1 • p.2)) (hg.comp hm)
  rw [incLevy, lintegral_map hg hm, lintegral_prod (fun p : ℝ × Rd d => g (p.1 • p.2))
    (hg.comp hm).aemeasurable]
  refine (lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hmeas).trans ?_
  refine lintegral_congr fun r => ?_
  simp only [Pi.mul_apply]
  congr 1
  rw [maternStep, lintegral_map hg (measurable_const_smul r)]

theorem incLevy_apply (a b : ℝ) {A : Set (Rd d)} (hA : MeasurableSet A) :
    incLevy d a b A = ∫⁻ r in Ioc a b, ENNReal.ofReal (2 / r) * maternStep d r A := by
  have h := lintegral_incLevy (d := d) a b (g := A.indicator 1) (measurable_one.indicator hA)
  simp only [lintegral_indicator_one hA] at h
  exact h

theorem incLevy_map_neg (a b : ℝ) : (incLevy d a b).map (fun x => -x) = incLevy d a b := by
  ext A hA
  rw [Measure.map_apply measurable_neg hA, incLevy_apply a b (measurable_neg hA),
    incLevy_apply a b hA]
  refine lintegral_congr fun r => ?_
  rw [← Measure.map_apply measurable_neg hA, maternStep_map_neg]

theorem incLevy_singleton_zero (hd : 1 ≤ d) {a b : ℝ} (ha : 0 ≤ a) : incLevy d a b {0} = 0 := by
  rw [incLevy_apply a b (measurableSet_singleton 0)]
  refine (setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_).trans lintegral_zero
  rw [maternStep_singleton_zero hd (lt_of_le_of_lt ha hr.1), mul_zero]

/-- The mass of `2∫_a^b L_r dr/r` is `2 log(b/a)`. -/
theorem incLevy_univ {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    incLevy d a b univ = ENNReal.ofReal (2 * Real.log (b / a)) := by
  rw [incLevy_apply a b MeasurableSet.univ]
  have h1 : ∀ r, (maternStep d r) univ = 1 := fun r =>
    (charFun_maternStep (d := d) r 0).1.measure_univ
  simp_rw [h1, mul_one]
  have hpos : ∀ r ∈ Icc a b, 0 < r := fun r hr => ha.trans_le hr.1
  have hint : IntegrableOn (fun r : ℝ => 2 / r) (Ioc a b) :=
    (ContinuousOn.integrableOn_Icc (continuousOn_const.div continuousOn_id
      fun r hr => (hpos r hr).ne')).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioc).2
    (Eventually.of_forall fun r hr => (div_pos two_pos (ha.trans hr.1)).le))]
  congr 1
  rw [← intervalIntegral.integral_of_le hab]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha (ha.trans_le hab),
    div_eq_mul_inv]

/-- `∫(1 - cos⟨ω,x⟩) 2∫_a^b L_r(dx) dr/r = log(1 + b²|ω|²) - log(1 + a²|ω|²)`. -/
theorem lintegral_one_sub_cos_incLevy {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ω : Rd d) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) ∂(incLevy d a b) =
      ENNReal.ofReal (Real.log (1 + b ^ 2 * ‖ω‖ ^ 2) - Real.log (1 + a ^ 2 * ‖ω‖ ^ 2)) := by
  rw [lintegral_incLevy a b (by fun_prop)]
  simp_rw [lintegral_one_sub_cos_maternStep]
  set u := ‖ω‖ ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have hpt : ∀ r ∈ Ioc a b, ENNReal.ofReal (2 / r) * ENNReal.ofReal (r ^ 2 * u / (1 + r ^ 2 * u)) =
      ENNReal.ofReal (2 * r * u / (1 + r ^ 2 * u)) := by
    intro r hr
    have hr0 : 0 < r := lt_of_le_of_lt ha hr.1
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : 0 < 1 + r ^ 2 * u := by positivity
    field_simp
  have hcont : Continuous fun r : ℝ => 2 * r * u / (1 + r ^ 2 * u) :=
    (by fun_prop : Continuous fun r : ℝ => 2 * r * u).div (by fun_prop) fun r => by positivity
  rw [setLIntegral_congr_fun measurableSet_Ioc hpt, ← ofReal_integral_eq_lintegral_ofReal
    (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun r hr => by
        have : 0 < r := lt_of_le_of_lt ha hr.1
        positivity))]
  congr 1
  rw [← intervalIntegral.integral_of_le hab]
  have hderiv : ∀ r ∈ uIcc a b, HasDerivAt (fun r => Real.log (1 + r ^ 2 * u))
      (2 * r * u / (1 + r ^ 2 * u)) r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2 * u) (2 * r * u) r := by
      have := ((hasDerivAt_pow 2 r).mul_const u).const_add 1
      refine this.congr_deriv ?_
      push_cast
      ring
    exact (h1.log (by positivity)).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]

/-! ## Second moments -/

/-- `∫ |x|² d(law of √(2X)Z) < ∞`: `2E[X] E|Z|²`. -/
theorem lintegral_sq_gammaGaussLaw_ne_top :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(gammaGaussLaw d 1) ≠ ⊤ := by
  have hm : Measurable fun p : ℝ × Rd d => Real.sqrt (2 * p.1) • p.2 := by fun_prop
  rw [gammaGaussLaw, lintegral_map (by fun_prop) hm]
  have hpt : ∀ p : ℝ × Rd d, ENNReal.ofReal (‖Real.sqrt (2 * p.1) • p.2‖ ^ 2) =
      ENNReal.ofReal (2 * p.1) * ENNReal.ofReal (‖p.2‖ ^ 2) := by
    intro p
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rcases le_total 0 p.1 with h | h
    · rw [Real.sq_sqrt (by linarith), ENNReal.ofReal_mul (by linarith)]
    · rw [Real.sqrt_eq_zero'.2 (by linarith), ENNReal.ofReal_of_nonpos (by linarith)]
      simp [h]
  simp_rw [hpt]
  rw [lintegral_prod_mul (f := fun v : ℝ => ENNReal.ofReal (2 * v))
    (g := fun z : Rd d => ENNReal.ofReal (‖z‖ ^ 2)) (by fun_prop) (by fun_prop)]
  refine ENNReal.mul_ne_top ?_ ?_
  · -- `∫ 2v Γ(1,1)(dv) = 2`
    rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (gammaPDF 1 1) from (measurable_gammaPDFReal 1 1).ennreal_ofReal)
      (by fun_prop : Measurable fun v : ℝ => ENNReal.ofReal (2 * v))]
    have hpt' : ∀ v : ℝ, (gammaPDF 1 1 * fun v => ENNReal.ofReal (2 * v)) v =
        (Ioi 0).indicator (fun v => ENNReal.ofReal (2 * (v * Real.exp (-(1 * v))))) v := by
      intro v
      simp only [Pi.mul_apply, gammaPDF, gammaPDFReal, indicator, mem_Ioi]
      by_cases hv : 0 < v
      · rw [if_pos hv.le, if_pos hv, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp
        ring
      · rw [if_neg hv]
        rw [ENNReal.ofReal_of_nonpos (show 2 * v ≤ 0 by linarith [not_lt.1 hv]), mul_zero]
    simp_rw [hpt']
    rw [lintegral_indicator measurableSet_Ioi, lintegral_mul_exp_neg one_pos 2 zero_le_two]
    exact ENNReal.ofReal_ne_top
  · have h := (IsGaussian.memLp_two_id (μ := stdGaussian (Rd d)))
    have hi : Integrable (fun x : Rd d => ‖x‖ ^ 2) (stdGaussian (Rd d)) := by
      have := MemLp.integrable_norm_pow (p := 2) (by simpa using h) two_ne_zero
      simpa using this
    exact hi.lintegral_lt_top.ne

/-- The second moment of `L_r` is `r²` times that of `L_1`. -/
theorem lintegral_sq_maternStep (r : ℝ) :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(maternStep d r) =
      ENNReal.ofReal (r ^ 2) * ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(gammaGaussLaw d 1) := by
  rw [maternStep, lintegral_map (by fun_prop) (measurable_const_smul r), ← lintegral_const_mul _
    (by fun_prop)]
  refine lintegral_congr fun x => ?_
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (sq_nonneg r)]

/-- The second moment of `2∫_a^b L_r dr/r` is at most `2b²` times that of `L_1`. -/
theorem lintegral_sq_incLevy_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(incLevy d a b) ≤
      ENNReal.ofReal (2 * b ^ 2) * ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(gammaGaussLaw d 1) := by
  set K := ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(gammaGaussLaw d 1)
  rw [lintegral_incLevy a b (by fun_prop)]
  simp_rw [lintegral_sq_maternStep]
  calc ∫⁻ r in Ioc a b, ENNReal.ofReal (2 / r) * (ENNReal.ofReal (r ^ 2) * K)
      ≤ ∫⁻ _ in Ioc a b, ENNReal.ofReal (2 * b) * K := by
        refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
        have hr0 : 0 < r := lt_of_le_of_lt ha hr.1
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) K
        rw [show 2 / r * r ^ 2 = 2 * r by field_simp]
        linarith [hr.2]
    _ = ENNReal.ofReal (2 * b) * K * ENNReal.ofReal (b - a) := by
        rw [setLIntegral_const, Real.volume_Ioc]
    _ ≤ ENNReal.ofReal (2 * b ^ 2) * K := by
        rw [mul_right_comm, ← ENNReal.ofReal_mul (by linarith)]
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) K
        nlinarith

/-! ## Clause (2) -/

theorem charFun_maternIncLaw {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) (ω : Rd d) :
    charFun (maternIncLaw d β γ) ω = ((Real.exp (-maternIncExponent β γ (‖ω‖ ^ 2)) : ℝ) : ℂ) := by
  have hβ : 0 < β := hγ.trans hγβ
  have hr : γ / β < 1 := (div_lt_one hβ).2 hγβ
  haveI := (charFun_maternStep (d := d) (Real.sqrt β) 0).1
  have hint : ∀ L : Measure (Rd d), IsFiniteMeasure L →
      Integrable (fun x : Rd d => Complex.exp (⟪x, ω⟫ * Complex.I)) L := fun L _ =>
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply, maternIncLaw, integral_add_measure ((hint _ inferInstance).smul_measure
    ENNReal.ofReal_ne_top) ((hint _ inferInstance).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, ← charFun_apply,
    (charFun_maternStep _ ω).2, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by linarith), Real.sq_sqrt hβ.le]
  have hu : 0 ≤ ‖ω‖ ^ 2 := by positivity
  have hval : Real.exp (-maternIncExponent β γ (‖ω‖ ^ 2)) =
      γ / β + (1 - γ / β) * (1 + β * ‖ω‖ ^ 2)⁻¹ := by
    rw [maternIncExponent, Real.exp_neg, Real.exp_log (div_pos (by positivity) (by positivity))]
    field_simp
    ring
  rw [hval]
  simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.real_smul,
    mul_one]
  push_cast
  ring

theorem isProbabilityMeasure_maternIncLaw {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) :
    IsProbabilityMeasure (maternIncLaw d β γ) := by
  have hβ : 0 < β := hγ.trans hγβ
  have hr : γ / β < 1 := (div_lt_one hβ).2 hγβ
  haveI := (charFun_maternStep (d := d) (Real.sqrt β) 0).1
  constructor
  rw [maternIncLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
    measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add (by positivity) (by linarith)]
  simp

/-- **`prop:matern-increments`(2), the mixture.** `(γ/β) δ₀ + (1 - γ/β) L_{√β}` is a probability
measure with the transform `e^{-f_{β,γ}(|ω|²)}`, and it is the only one. It no longer takes
`1 ≤ d`, which its proof does not read (2026-11-15, a strengthening). -/
theorem matern_increments_2 {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) :
    IsProbabilityMeasure (maternIncLaw d β γ) ∧
      (∀ ω : Rd d, charFun (maternIncLaw d β γ) ω =
        ((Real.exp (-maternIncExponent β γ (‖ω‖ ^ 2)) : ℝ) : ℂ)) ∧
      ∀ ρ : Measure (Rd d), IsProbabilityMeasure ρ →
        (∀ ω : Rd d, charFun ρ ω = ((Real.exp (-maternIncExponent β γ (‖ω‖ ^ 2)) : ℝ) : ℂ)) →
          ρ = maternIncLaw d β γ := by
  haveI := isProbabilityMeasure_maternIncLaw (d := d) hγ hγβ
  refine ⟨inferInstance, charFun_maternIncLaw hγ hγβ, fun ρ hρ hc => ?_⟩
  exact Measure.ext_of_charFun (funext fun ω => by rw [hc, charFun_maternIncLaw hγ hγβ])

/-- **`prop:matern-increments`(2), the Lévy measure exists**: `ν = 2∫_{√γ}^{√β} L_r dr/r`
setwise. It no longer takes `1 ≤ d`, `0 < γ`, `γ < β`, which its proof does not read (2026-11-15, a
strengthening). -/
theorem matern_increments_2_levy_exists (β γ : ℝ) :
    ∃ ν : Measure (Rd d), ∀ A : Set (Rd d), MeasurableSet A →
      ν A = ∫⁻ r in Ioc (Real.sqrt γ) (Real.sqrt β), ENNReal.ofReal (2 / r) * maternStep d r A :=
  ⟨incLevy d (Real.sqrt γ) (Real.sqrt β), fun _ hA => incLevy_apply _ _ hA⟩

/-- The triplet `(0, ν, 0)` of a symmetric Lévy measure `ν` with finite second moment. -/
noncomputable def symTriplet (ν : Measure (Rd d)) (h0 : ν {0} = 0)
    (h2 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂ν ≠ ⊤) : LevyTriplet d where
  A := 0
  ν := ν
  γ := 0
  A_posSemidef := Matrix.PosSemidef.zero
  ν_zero := h0
  ν_integrable := ne_top_of_le_ne_top h2 (lintegral_mono fun _ =>
    ENNReal.ofReal_le_ofReal (min_le_left _ _))

/-- A law whose transform is `exp(-∫(1 - cos) dν)`, `ν` symmetric, has the triplet `(0, ν, 0)`. -/
theorem hasTriplet_symTriplet (μ : Measure (Rd d)) (ν : Measure (Rd d)) (h0 : ν {0} = 0)
    (h2 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂ν ≠ ⊤) (hsym : ν.map (fun x => -x) = ν)
    (hμ : ∀ z, charFun μ z = ((Real.exp (-∫ x, (1 - Real.cos ⟪z, x⟫) ∂ν) : ℝ) : ℂ)) :
    HasTriplet μ (symTriplet ν h0 h2) := fun z => by
  rw [hμ z, lkExponent_of_symm_general (symTriplet ν h0 h2) rfl hsym z, Complex.ofReal_exp]
  simp [symTriplet, quad_zero]

theorem maternIncExponent_eq_log_sub {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) (ω : Rd d) :
    Real.log (1 + Real.sqrt β ^ 2 * ‖ω‖ ^ 2) - Real.log (1 + Real.sqrt γ ^ 2 * ‖ω‖ ^ 2) =
      maternIncExponent β γ (‖ω‖ ^ 2) := by
  rw [Real.sq_sqrt (hγ.trans hγβ).le, Real.sq_sqrt hγ.le,
    maternIncExponent_eq (hγ.trans hγβ) hγ (by positivity)]

/-- **`prop:matern-increments`(2), compound Poisson.** With `ν = 2∫_{√γ}^{√β} L_r dr/r`: `ν` has
total mass `log(β/γ)`, the law is the compound Poisson law of `ν`, and `ν` is its Lévy measure. -/
theorem matern_increments_2_poisson (hd : 1 ≤ d) {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β)
    (ν : Measure (Rd d))
    (hν : ∀ A : Set (Rd d), MeasurableSet A →
      ν A = ∫⁻ r in Ioc (Real.sqrt γ) (Real.sqrt β), ENNReal.ofReal (2 / r) * maternStep d r A) :
    ν univ = ENNReal.ofReal (Real.log (β / γ)) ∧ maternIncLaw d β γ = compoundPoissonLaw ν ∧
      ∃ T : LevyTriplet d, HasTriplet (maternIncLaw d β γ) T ∧ T.ν = ν := by
  have hβ : 0 < β := hγ.trans hγβ
  have hsγ : 0 < Real.sqrt γ := Real.sqrt_pos.2 hγ
  have hle : Real.sqrt γ ≤ Real.sqrt β := Real.sqrt_le_sqrt hγβ.le
  have hνeq : ν = incLevy d (Real.sqrt γ) (Real.sqrt β) :=
    Measure.ext fun A hA => (hν A hA).trans (incLevy_apply _ _ hA).symm
  subst hνeq
  have huniv := incLevy_univ (d := d) hsγ hle
  have hmass : 2 * Real.log (Real.sqrt β / Real.sqrt γ) = Real.log (β / γ) := by
    rw [← Real.log_rpow (div_pos (Real.sqrt_pos.2 hβ) hsγ), Real.div_rpow (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)]
    norm_num [Real.sq_sqrt hβ.le, Real.sq_sqrt hγ.le]
  rw [hmass] at huniv
  haveI : IsFiniteMeasure (incLevy d (Real.sqrt γ) (Real.sqrt β)) :=
    ⟨by rw [huniv]; exact ENNReal.ofReal_lt_top⟩
  have hsym := incLevy_map_neg (d := d) (Real.sqrt γ) (Real.sqrt β)
  have hcos : ∀ z : Rd d, ∫ x, (1 - Real.cos ⟪z, x⟫) ∂(incLevy d (Real.sqrt γ) (Real.sqrt β)) =
      maternIncExponent β γ (‖z‖ ^ 2) := fun z => by
    rw [← maternIncExponent_eq_log_sub hγ hγβ z]
    refine integral_one_sub_cos_of_lintegral _ z ?_ (lintegral_one_sub_cos_incLevy hsγ.le hle z)
    rw [Real.sq_sqrt hβ.le, Real.sq_sqrt hγ.le]
    exact sub_nonneg.2 (Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ‖z‖]))
  have h2 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(incLevy d (Real.sqrt γ) (Real.sqrt β)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top lintegral_sq_gammaGaussLaw_ne_top)
      (lintegral_sq_incLevy_le hsγ.le hle)
  haveI := isProbabilityMeasure_maternIncLaw (d := d) hγ hγβ
  refine ⟨huniv, ?_, symTriplet _ (incLevy_singleton_zero hd hsγ.le) h2,
    hasTriplet_symTriplet _ _ _ h2 hsym fun z => by rw [hcos, charFun_maternIncLaw hγ hγβ], rfl⟩
  have hsym' : (incLevy d (Real.sqrt γ) (Real.sqrt β)).map
      (LinearIsometryEquiv.neg ℝ (E := Rd d)) = incLevy d (Real.sqrt γ) (Real.sqrt β) := by
    rw [LinearIsometryEquiv.coe_neg]
    exact hsym
  change maternIncLaw d β γ = cpLaw _
  exact Measure.ext_of_charFun (funext fun z => by
    rw [charFun_maternIncLaw hγ hγβ, charFun_cpLaw_of_symm _ hsym', hcos])

/-! ## Clause (3) -/

/-- **`ν_{s,t} = ∑_{i ≥ 1} 2∫_{csq^{-i}}^{ctq^{-i}} L_r dr/r`**. -/
noncomputable def incLevySum (d : ℕ) (q c s t : ℝ) : Measure (Rd d) :=
  Measure.sum fun i : ℕ => incLevy d (c * s / q ^ (i + 1)) (c * t / q ^ (i + 1))

theorem incLevySum_apply (q c s t : ℝ) {A : Set (Rd d)} (hA : MeasurableSet A) :
    incLevySum d q c s t A = ∑' i : ℕ, ∫⁻ r in Ioc (c * s / q ^ (i + 1)) (c * t / q ^ (i + 1)),
      ENNReal.ofReal (2 / r) * maternStep d r A := by
  rw [incLevySum, Measure.sum_apply _ hA]
  exact tsum_congr fun i => incLevy_apply _ _ hA

/-- **`prop:matern-increments`(3), the Lévy measure exists**:
`ν_{s,t} = ∑_{i ≥ 1} 2∫_{csq^{-i}}^{ctq^{-i}} L_r dr/r` setwise. It no longer takes `1 ≤ d`,
`1 < q`, `0 < c`, `0 < s`, `s < t`, which its proof does not read (2026-11-15, a strengthening). -/
theorem matern_increments_3_levy_exists (q c s t : ℝ) :
    ∃ ν : Measure (Rd d), ∀ A : Set (Rd d), MeasurableSet A →
      ν A = ∑' i : ℕ, ∫⁻ r in Ioc (c * s / q ^ (i + 1)) (c * t / q ^ (i + 1)),
        ENNReal.ofReal (2 / r) * maternStep d r A :=
  ⟨incLevySum d q c s t, fun _ hA => incLevySum_apply q c s t hA⟩

theorem incLevySum_singleton_zero (hd : 1 ≤ d) {q c s t : ℝ} (hq : 0 < q) (hc : 0 ≤ c)
    (hs : 0 ≤ s) : incLevySum d q c s t {0} = 0 := by
  rw [incLevySum, Measure.sum_apply _ (measurableSet_singleton 0)]
  exact ENNReal.tsum_eq_zero.2 fun i => incLevy_singleton_zero hd (by positivity)

theorem incLevySum_map_neg (q c s t : ℝ) :
    (incLevySum d q c s t).map (fun x => -x) = incLevySum d q c s t := by
  ext A hA
  rw [Measure.map_apply measurable_neg hA, incLevySum, Measure.sum_apply _ (measurable_neg hA),
    Measure.sum_apply _ hA]
  refine tsum_congr fun i => ?_
  rw [← Measure.map_apply measurable_neg hA, incLevy_map_neg]

theorem incLevy_bounds {q c s t : ℝ} (hq : 0 < q) (hc : 0 ≤ c) (hs : 0 ≤ s) (hst : s ≤ t)
    (i : ℕ) : 0 ≤ c * s / q ^ (i + 1) ∧ c * s / q ^ (i + 1) ≤ c * t / q ^ (i + 1) :=
  ⟨by positivity, div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hst hc) (by positivity)⟩

/-- `ν_{s,t}` has a finite second moment. -/
theorem lintegral_sq_incLevySum_ne_top {q c s t : ℝ} (hq : 1 < q) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hst : s ≤ t) : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(incLevySum d q c s t) ≠ ⊤ := by
  have hq0 : 0 < q := by linarith
  set K := ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(gammaGaussLaw d 1)
  have h0 : (0 : ℝ) ≤ (q ^ 2)⁻¹ := by positivity
  have h1 : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have hsum : Summable fun i : ℕ => 2 * (c * t) ^ 2 * (q ^ 2)⁻¹ * ((q ^ 2)⁻¹) ^ i :=
    (summable_geometric_of_lt_one h0 h1).mul_left _
  have hb : ∀ i : ℕ, ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(incLevy d (c * s / q ^ (i + 1))
      (c * t / q ^ (i + 1))) ≤
        ENNReal.ofReal (2 * (c * t) ^ 2 * (q ^ 2)⁻¹ * ((q ^ 2)⁻¹) ^ i) * K := by
    intro i
    obtain ⟨ha, hab⟩ := incLevy_bounds hq0 hc hs hst i
    refine (lintegral_sq_incLevy_le ha hab).trans (le_of_eq ?_)
    have hq2 : (q ^ (i + 1)) ^ 2 = q ^ 2 * (q ^ 2) ^ i := by ring
    congr 2
    rw [div_pow, hq2, inv_pow]
    field_simp
  rw [incLevySum, lintegral_sum_measure]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top lintegral_sq_gammaGaussLaw_ne_top

/-- `∫(1 - cos⟨ω,x⟩) ν_{s,t}(dx) = F_q(t|ω|) - F_q(s|ω|)`, by Tonelli's theorem. -/
theorem integral_one_sub_cos_incLevySum {q c s t : ℝ} (hq : 1 < q) (hc : 0 < c) (hs : 0 ≤ s)
    (hst : s ≤ t) (ω : Rd d) :
    ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂(incLevySum d q c s t) =
      maternExponent q c (t * ‖ω‖) - maternExponent q c (s * ‖ω‖) := by
  have hq0 : 0 < q := by linarith
  set A : ℝ → ℕ → ℝ := fun r i => Real.log (1 + c ^ 2 * (r * ‖ω‖) ^ 2 / q ^ (2 * (i + 1)))
    with hA
  have hterm : ∀ (r : ℝ) (i : ℕ), Real.log (1 + (c * r / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2) = A r i := by
    intro r i
    simp only [hA]
    congr 2
    rw [pow_mul]
    field_simp
    ring
  have hS : ∀ r, Summable (A r) := fun r => summable_maternExponent hq hc (r * ‖ω‖)
  have hnn : ∀ i, 0 ≤ A t i - A s i := fun i => by
    simp only [hA]
    refine sub_nonneg.2 (Real.log_le_log (by positivity) ?_)
    have : (s * ‖ω‖) ^ 2 ≤ (t * ‖ω‖) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hst (norm_nonneg ω)
      exact pow_le_pow_left₀ (by positivity) this 2
    have : c ^ 2 * (s * ‖ω‖) ^ 2 / q ^ (2 * (i + 1)) ≤ c ^ 2 * (t * ‖ω‖) ^ 2 / q ^ (2 * (i + 1)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity)) (by positivity)
    linarith
  have heq : maternExponent q c (t * ‖ω‖) - maternExponent q c (s * ‖ω‖) =
      ∑' i, (A t i - A s i) := by
    rw [(hS t).tsum_sub (hS s)]
    rfl
  rw [heq]
  refine integral_one_sub_cos_of_lintegral _ ω (tsum_nonneg hnn) ?_
  rw [incLevySum, lintegral_sum_measure, ENNReal.ofReal_tsum_of_nonneg hnn ((hS t).sub (hS s))]
  refine tsum_congr fun i => ?_
  obtain ⟨ha, hab⟩ := incLevy_bounds hq0 hc.le hs hst i
  rw [lintegral_one_sub_cos_incLevy ha hab ω, hterm, hterm]

/-- **`prop:matern-increments`(3), infinite divisibility.** Every step `μ_{s,t}`, `0 < s < t`, of
the Matérn pyramid is infinitely divisible with Lévy measure `ν_{s,t}`. -/
theorem matern_increments_3 (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) (ν : Measure (Rd d))
    (hν : ∀ A : Set (Rd d), MeasurableSet A →
      ν A = ∑' i : ℕ, ∫⁻ r in Ioc (c * s / q ^ (i + 1)) (c * t / q ^ (i + 1)),
        ENNReal.ofReal (2 / r) * maternStep d r A) :
    IsInfinitelyDivisible (μ s t) ∧ ∃ T : LevyTriplet d, HasTriplet (μ s t) T ∧ T.ν = ν := by
  have hνeq : ν = incLevySum d q c s t :=
    Measure.ext fun A hA => (hν A hA).trans (incLevySum_apply q c s t hA).symm
  subst hνeq
  obtain ⟨hprob, hchar⟩ := hμ s t hs.le hst.le
  haveI := hprob
  have h2 := lintegral_sq_incLevySum_ne_top (d := d) hq hc.le hs.le hst.le
  have hT := hasTriplet_symTriplet (μ s t) _
    (incLevySum_singleton_zero hd (by linarith) hc.le hs.le) h2 (incLevySum_map_neg q c s t)
    fun z => by rw [hchar z, integral_one_sub_cos_incLevySum hq hc hs.le hst.le z]
  exact ⟨isInfinitelyDivisible_of_hasTriplet hT, _, hT, rfl⟩

end Pyramids
