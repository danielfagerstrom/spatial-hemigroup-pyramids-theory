/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.BesselProfile
import Pyramids.LineAppendix.MaternLine
import Pyramids.Cited.A31
import Pyramids.Cited.A34
import Pyramids.Cited.A35

/-!
# `thm:matern-pyramid`(1)–(2): admissibility, the family, uniqueness

Blueprint: `blueprint/src/parts/04-matern.tex`, `thm:matern-pyramid`. Phase 5, wave 3b. The
declarations moved here from `PyramidsSkeleton.Ch04Matern` with their statements unchanged.

* **Origin data from a bound.** A profile `k ≥ 0`, nonincreasing on `(0,∞)`, with `k(r) ≤ M/r`
  satisfies both integrability conditions of an origin datum: `k(r)r ≤ M` on `(0,1)` and
  `k(r)/r ≤ M/r²` on `(1,∞)` (`originDatumOfLe`). The bound comes from `b_d(y) ≤ C_de^{-y/2}` and
  `e^{-x} ≤ 1/x`: `b_d(y) ≤ 2C_d/y` (`besselProfile_le_div`). So the two integrability estimates
  of the printed proof are replaced by one elementary bound, summed over the octaves.
* **The polar measure of a series** is the series of the polar measures, tested on any measurable
  function (`lintegral_polarLevyMeasure_tsum`): the densities add pointwise (`ofReal` of a
  nonnegative summable series) and `lintegral_tsum` exchanges.
* **(1), admissibility.** `lem:bessel-profile`(2) at `β = c²q^{-2(i+1)}`, `√β = c/q^{i+1}`, summed:
  `F_q(|ξ|)` is the exponent of the datum `(0, k_d)`; A35 (`cited_A35_classA`) gives `F_q ∈ 𝒜_d`.
* **(1), the family.** A34 (`cited_A34`) at `χ = id`, and `F_q ≢ 0`.
* **(2).** The functional equation iterates to `F̃(r) - F_q(r) = F̃(q^{-n}r) - F_q(q^{-n}r) → 0`
  (`matern_pyramid_line_2_direct`, the line's). For the family, A31 gives `(χ, F)`; the knot
  `n = 0` gives `F(χ(1)r) = F_q(r)`, so the gauge `χ/χ(1)` and `F_q` represent `μ'`, and the knots
  force `χ(q^n)/χ(1) = q^n`, `F_q` being strictly increasing on `[0,∞)`.

**What it reaches.** Admissibility prints A35's names (the affine export's `sato_polar_criterion`
and `selfDecomposable_infinitelyDivisible`, with A39's); the existence adds nothing of A34's own
(Lean core); the uniqueness of the family prints A31's.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## Elementary bounds -/

/-- `e^{-x} ≤ 1/x` for `x > 0`. -/
theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, one_div]
  refine inv_anti₀ hx ?_
  linarith [Real.add_one_le_exp x]

/-- `b_d ≥ 0`. -/
theorem besselProfile_nonneg (hd : 1 ≤ d) (y : ℝ) : 0 ≤ besselProfile d y := by
  have hs : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine mul_nonneg (div_nonneg zero_le_two (Real.Gamma_pos_of_pos hs).le) ?_
  refine setIntegral_nonneg measurableSet_Ioi fun v hv => ?_
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt hv) _) (Real.exp_pos _).le

/-- `b_d(y) ≤ 2C_d/y` for `y > 0`, `C_d = 2^{1+d/2}`. -/
theorem besselProfile_le_div (hd : 1 ≤ d) {y : ℝ} (hy : 0 < y) :
    besselProfile d y ≤ 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) / y := by
  have h1 := besselProfile_le hd y
  have h2 : Real.exp (-y / 2) ≤ 1 / (y / 2) := by
    rw [neg_div]; exact exp_neg_le_inv (by positivity)
  have hC : (0 : ℝ) < (2 : ℝ) ^ (1 + (d : ℝ) / 2) := by positivity
  calc besselProfile d y ≤ (2 : ℝ) ^ (1 + (d : ℝ) / 2) * (1 / (y / 2)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hC.le)
    _ = 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) / y := by field_simp

/-! ## Origin data from a bound -/

/-- **An origin datum from a bound**: a profile `k ≥ 0`, nonincreasing on `(0,∞)`, with
`k(r) ≤ M/r` there. -/
noncomputable def originDatumOfLe (k : ℝ → ℝ) (hk0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r)
    (hanti : AntitoneOn k (Ioi 0)) (M : ℝ) (hM : ∀ r : ℝ, 0 < r → k r ≤ M / r) :
    OriginDatum d where
  a := 0
  k := k
  a_nonneg := le_rfl
  k_nonneg := hk0
  k_antitone := hanti
  integrable_near_zero := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal M) ?_ ?_
    · rw [setLIntegral_const, Real.volume_Ioo]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · refine setLIntegral_mono measurable_const fun r hr => ENNReal.ofReal_le_ofReal ?_
      have h := hM r hr.1
      rwa [le_div_iff₀ hr.1] at h
  integrable_at_top := by
    have hI : IntegrableOn (fun r : ℝ => M * r ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul M
    refine ne_top_of_le_ne_top hI.lintegral_lt_top.ne ?_
    refine setLIntegral_mono' measurableSet_Ioi fun r hr => ENNReal.ofReal_le_ofReal ?_
    have hr0 : (0 : ℝ) < r := one_pos.trans hr
    have h := hM r hr0
    have e : M * r ^ (-2 : ℝ) = M / r / r := by
      rw [Real.rpow_neg hr0.le, Real.rpow_two]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h hr0.le

theorem originDatumOfLe_a (k : ℝ → ℝ) (hk0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r)
    (hanti : AntitoneOn k (Ioi 0)) (M : ℝ) (hM : ∀ r : ℝ, 0 < r → k r ≤ M / r) :
    (originDatumOfLe (d := d) k hk0 hanti M hM).a = 0 := rfl

theorem originDatumOfLe_k (k : ℝ → ℝ) (hk0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ k r)
    (hanti : AntitoneOn k (Ioi 0)) (M : ℝ) (hM : ∀ r : ℝ, 0 < r → k r ≤ M / r) :
    (originDatumOfLe (d := d) k hk0 hanti M hM).k = k := rfl

/-- The exponent of a datum without Gaussian part is the lower integral against the polar
measure of its profile. -/
theorem exponentL_of_a_zero (D : OriginDatum d) (ha : D.a = 0) (ξ : Rd d) :
    D.exponentL ξ = ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫) ∂polarLevyMeasure d D.k := by
  rw [OriginDatum.exponentL, ha, zero_mul, zero_div, ENNReal.ofReal_zero, zero_add]
  rfl

/-- **The polar measure of a series of profiles**, tested on a measurable function, is the series
of the tests. -/
theorem lintegral_polarLevyMeasure_tsum (k : ℕ → ℝ → ℝ) (hk0 : ∀ i r, 0 < r → 0 ≤ k i r)
    (hs : ∀ r, 0 < r → Summable fun i => k i r) (hm : ∀ i, Measurable (k i))
    (G : Rd d → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂polarLevyMeasure d (fun r => ∑' i, k i r) =
      ∑' i, ∫⁻ x, G x ∂polarLevyMeasure d (k i) := by
  set dens : (ℝ → ℝ) → Rd d → ℝ≥0∞ := fun k x =>
    ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x with hdens
  have hn : Measurable fun x : Rd d => ‖x‖ := measurable_norm
  have hmeas : ∀ i, Measurable (dens (k i)) := fun i => by
    refine Measurable.indicator ?_ (measurableSet_singleton 0).compl
    exact (((hm i).comp hn).div (measurable_const.mul (hn.pow_const d))).ennreal_ofReal
  have hsum : dens (fun r => ∑' i, k i r) = fun x => ∑' i, dens (k i) x := by
    funext x
    by_cases hx : x = 0
    · simp [hdens, hx]
    · have hx' : x ∈ ({0}ᶜ : Set (Rd d)) := hx
      have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
      simp only [hdens, indicator_of_mem hx']
      rw [← tsum_div_const, ENNReal.ofReal_tsum_of_nonneg]
      · intro i
        have hA : 0 ≤ sphereArea d :=
          div_nonneg (by positivity) (Real.Gamma_nonneg_of_nonneg (by positivity))
        exact div_nonneg (hk0 i _ hr) (by positivity)
      · exact (hs _ hr).div_const _
  have hpolar : ∀ k, polarLevyMeasure d k = volume.withDensity (dens k) := fun k => rfl
  have hi : ∀ i, ∫⁻ x, G x ∂polarLevyMeasure d (k i) = ∫⁻ x, dens (k i) x * G x := fun i => by
    rw [hpolar, lintegral_withDensity_eq_lintegral_mul _ (hmeas _) hG]
    rfl
  rw [hpolar, hsum, lintegral_withDensity_eq_lintegral_mul _ (Measurable.tsum hmeas) hG]
  simp_rw [hi]
  rw [← lintegral_tsum fun i => ((hmeas i).mul hG).aemeasurable]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, ENNReal.tsum_mul_right]

/-! ## Clause (1), admissibility -/

variable {q c : ℝ}

theorem sqrt_matern_beta (hq : 1 < q) (hc : 0 < c) (i : ℕ) :
    Real.sqrt (c ^ 2 / q ^ (2 * (i + 1))) = c / q ^ (i + 1) := by
  have hq0 : 0 < q := by linarith
  rw [show q ^ (2 * (i + 1)) = (q ^ (i + 1)) ^ 2 by ring, ← div_pow,
    Real.sqrt_sq (by positivity)]

/-- The `i`-th octave profile, `b_d(rq^{i+1}/c)`. -/
theorem maternProfile_term_le (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) {r : ℝ} (hr : 0 < r)
    (i : ℕ) :
    besselProfile d (r * q ^ (i + 1) / c) ≤
      2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / r * (1 / q) ^ (i + 1) := by
  have hq0 : 0 < q := by linarith
  have h := besselProfile_le_div hd (y := r * q ^ (i + 1) / c) (by positivity)
  refine h.trans (le_of_eq ?_)
  rw [div_pow, one_pow]
  field_simp

theorem summable_maternProfile (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) {r : ℝ} (hr : 0 < r) :
    Summable fun i : ℕ => besselProfile d (r * q ^ (i + 1) / c) := by
  have hq0 : 0 < q := by linarith
  have hg : Summable fun i : ℕ => 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / r * (1 / q) ^ (i + 1) :=
    ((summable_geometric_of_lt_one (by positivity)
      ((div_lt_one hq0).2 hq)).comp_injective (add_left_injective 1)).mul_left _
  exact hg.of_nonneg_of_le (fun i => besselProfile_nonneg hd _)
    (maternProfile_term_le hd hq hc hr)

theorem maternPolarProfile_le (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) {r : ℝ} (hr : 0 < r) :
    maternPolarProfile q c d r ≤ 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / (q - 1) / r := by
  have hq0 : 0 < q := by linarith
  have hq1 : (1 / q) < 1 := (div_lt_one hq0).2 hq
  have hg : HasSum (fun i : ℕ => 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / r * (1 / q) ^ (i + 1))
      (2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / r * ((1 / q) / (1 - 1 / q))) := by
    refine HasSum.mul_left _ ?_
    have h := (hasSum_geometric_of_lt_one (by positivity) hq1).mul_left (1 / q)
    convert h using 1
    · funext i; ring
    · field_simp
  refine (Summable.tsum_le_tsum (maternProfile_term_le hd hq hc hr)
    (summable_maternProfile hd hq hc hr) hg.summable).trans (le_of_eq ?_)
  rw [hg.tsum_eq]
  have : q - 1 ≠ 0 := by linarith
  field_simp

theorem maternPolarProfile_nonneg (hd : 1 ≤ d) (q c r : ℝ) : 0 ≤ maternPolarProfile q c d r :=
  tsum_nonneg fun _ => besselProfile_nonneg hd _

theorem maternPolarProfile_antitoneOn (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) :
    AntitoneOn (maternPolarProfile q c d) (Ioi 0) := by
  intro r hr s hs hrs
  have hq0 : 0 < q := by linarith
  refine Summable.tsum_le_tsum (fun i => ?_) (summable_maternProfile hd hq hc hs)
    (summable_maternProfile hd hq hc hr)
  have h1 : 0 ≤ r * q ^ (i + 1) / c := by have := hr.out.le; positivity
  have h2 : 0 ≤ s * q ^ (i + 1) / c := by have := hs.out.le; positivity
  have hle : r * q ^ (i + 1) / c ≤ s * q ^ (i + 1) / c := by gcongr
  exact (besselProfile_strictAntiOn hd).antitoneOn h1 h2 hle

/-- **The datum `(0, k_d)` of `F_q`.** -/
noncomputable def maternDatum (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) : OriginDatum d :=
  originDatumOfLe (maternPolarProfile q c d) (fun r _ => maternPolarProfile_nonneg hd q c r)
    (maternPolarProfile_antitoneOn hd hq hc) _ fun _ hr => maternPolarProfile_le hd hq hc hr

theorem maternDatum_exponentL (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) (ξ : Rd d) :
    (maternDatum hd hq hc).exponentL ξ = ENNReal.ofReal (maternExponent q c ‖ξ‖) := by
  have hq0 : 0 < q := by linarith
  rw [exponentL_of_a_zero _ rfl]
  change ∫⁻ x, _ ∂polarLevyMeasure d (fun r => ∑' i : ℕ, besselProfile d (r * q ^ (i + 1) / c)) = _
  rw [lintegral_polarLevyMeasure_tsum (fun i r => besselProfile d (r * q ^ (i + 1) / c))
      (fun i r _ => besselProfile_nonneg hd _) (fun r hr => summable_maternProfile hd hq hc hr)
      (fun i => (continuous_besselProfile hd).measurable.comp
        ((measurable_id.mul_const _).div_const _))
      _ (by fun_prop),
    maternExponent, ENNReal.ofReal_tsum_of_nonneg
      (fun i => Real.log_nonneg (le_add_of_nonneg_right (by positivity)))
      (summable_maternExponent hq hc _)]
  refine tsum_congr fun i => ?_
  have hβ : 0 < c ^ 2 / q ^ (2 * (i + 1)) := by positivity
  have h := bessel_profile_2 hd hβ ξ
  rw [sqrt_matern_beta hq hc i] at h
  have e1 : (fun ρ : ℝ => besselProfile d (ρ / (c / q ^ (i + 1)))) =
      fun ρ => besselProfile d (ρ * q ^ (i + 1) / c) := by
    funext ρ; congr 1; field_simp
  rw [e1] at h
  rw [← h]
  congr 2
  ring

theorem maternDatum_exponent (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) (ξ : Rd d) :
    maternExponent q c ‖ξ‖ = (maternDatum hd hq hc).exponent ξ := by
  rw [OriginDatum.exponent, maternDatum_exponentL,
    ENNReal.toReal_ofReal (maternExponent_nonneg hq hc _)]

/-- **`thm:matern-pyramid`(1), admissibility.** `F_q ∈ 𝒜_d`, the exponent of the origin datum with
Gaussian coefficient `0` and the polar profile `k_d(r) = ∑_{i ≥ 1} b_d(rq^i/c)` (a convergent
series; nonincreasing, as an `OriginDatum` profile is). -/
theorem matern_pyramid_1_admissible (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    classA d (maternExponent q c) ∧
      (∀ r : ℝ, 0 < r → Summable fun i : ℕ => besselProfile d (r * q ^ (i + 1) / c)) ∧
      ∃ D : OriginDatum d, D.a = 0 ∧ (∀ r : ℝ, 0 < r → D.k r = maternPolarProfile q c d r) ∧
        ∀ ξ : Rd d, maternExponent q c ‖ξ‖ = D.exponent ξ :=
  ⟨(cited_A35_classA hd _ fun r _ => maternExponent_nonneg hq hc r).2
      ⟨maternDatum hd hq hc, maternDatum_exponent hd hq hc⟩,
    fun _ hr => summable_maternProfile hd hq hc hr,
    maternDatum hd hq hc, rfl, fun _ _ => rfl, maternDatum_exponent hd hq hc⟩


/-! ## Clause (1), the family -/

/-- `F_q ≢ 0` on `[0,∞)`. -/
theorem exists_maternExponent_ne_nonneg (hq : 1 < q) (hc : 0 < c) :
    ∃ r : ℝ, 0 ≤ r ∧ maternExponent q c r ≠ 0 := by
  obtain ⟨ω, hω⟩ := exists_maternExponent_ne hq hc
  exact ⟨|ω|, abs_nonneg ω, by rwa [maternExponent_abs]⟩

/-- **`thm:matern-pyramid`(1), the family exists**: laws with the transforms
`exp(-(F_q(t|ω|) - F_q(s|ω|)))`, `0 ≤ s ≤ t`. -/
theorem matern_pyramid_1_exists (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    ∃ μ : ℝ → ℝ → Measure (Rd d), IsMaternPyramid q c μ := by
  obtain ⟨μ, hprob, -, hcf⟩ := cited_A34 hd (fun t => t) (maternExponent q c) isGauge_idFun
    (matern_pyramid_1_admissible hd hq hc).1 (exists_maternExponent_ne_nonneg hq hc)
  exact ⟨μ, fun s t hs hst => ⟨hprob s t hs hst, hcf s t hs hst⟩⟩

/-- The transform of a Matérn pyramid, in its displayed form. -/
theorem charFun_maternPyramid {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] {μ : ℝ → ℝ → Measure E} (hμ : IsMaternPyramid q c μ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ω : E) :
    charFun (μ s t) ω =
      ((Real.exp (-(maternExponent q c (t * ‖ω‖) - maternExponent q c (s * ‖ω‖))) : ℝ) : ℂ) :=
  (hμ s t hs hst).2 ω

/-- Two families with the same laws on `0 ≤ s ≤ t`: an isotropic cascade family transfers its
clauses (I1)–(I3) and (ND). -/
theorem isIsotropicFamily_of_eq {μ ν : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (hν : IsIsotropicCascadeFamily ν S) (h : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = ν s t) :
    IsIsotropicFamily μ := by
  refine ⟨⟨⟨fun s t hs hst => h s t hs hst ▸ hν.isProbability s t hs hst,
    fun t ht => (h t t ht le_rfl).trans (hν.diag t ht),
    fun r s t hr hrs hst => by
      rw [h r t hr (hrs.trans hst), h s t (hr.trans hrs) hst, h r s hr hrs]
      exact hν.cascade r s t hr hrs hst,
    fun ω => (hν.continuous ω).congr fun p hp => by
      simp only
      rw [h p.1 p.2 hp.1 hp.2]⟩,
    fun s t hs hst => by rw [h s t hs hst.le]; exact hν.nondegenerate s t hs hst⟩,
    fun s t hs hst Q hQ => by rw [h s t hs hst]; exact hν.rotation Q hQ s t hs hst⟩

/-- `t ↦ λt` is an increasing bijection of `[0,∞)` for `λ > 0`. -/
theorem isIncreasingBijection_mul {lam : ℝ} (hlam : 0 < lam) :
    IsIncreasingBijection (fun t => lam * t) :=
  ⟨fun _ ht => mul_nonneg hlam.le ht, fun _ _ _ _ huv => mul_lt_mul_of_pos_left huv hlam,
    fun t ht => ⟨t / lam, div_nonneg ht hlam.le, mul_div_cancel₀ t hlam.ne'⟩⟩

/-- A Matérn pyramid is `λ`-covariant with `S_λ t = λt`. -/
theorem isCovariantAt_matern {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]
    {μ : ℝ → ℝ → Measure E} (hμ : IsMaternPyramid q c μ) {lam : ℝ} (hlam : 0 < lam) :
    IsCovariantAt μ lam fun t => lam * t := by
  refine ⟨isIncreasingBijection_mul hlam, fun s t hs hst => ?_⟩
  have hls : 0 ≤ lam * s := mul_nonneg hlam.le hs
  have hlst : lam * s ≤ lam * t := mul_le_mul_of_nonneg_left hst hlam.le
  haveI := (hμ s t hs hst).1
  haveI := (hμ _ _ hls hlst).1
  haveI : IsProbabilityMeasure ((μ s t).map fun x => lam • x) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_map_smul, charFun_maternPyramid hμ hs hst, charFun_maternPyramid hμ hls hlst,
    norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  ring_nf

/-- **The octave step** of a Matérn pyramid in `ℝ^d` is `L_{ct}`. -/
theorem matern_octave_step_d (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c)
    {μ : ℝ → ℝ → Measure (Rd d)} (hμ : IsMaternPyramid q c μ) {t : ℝ} (ht : 0 < t) :
    μ t (q * t) = maternStep d (c * t) := by
  have hle : t ≤ q * t := le_mul_of_one_le_left ht.le hq.le
  haveI := (hμ t (q * t) ht.le hle).1
  haveI := (bessel_profile_1 hd (mul_pos hc ht)).1
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  have hp : 0 < 1 + c ^ 2 * (t * ‖ω‖) ^ 2 := by positivity
  rw [charFun_maternPyramid hμ ht.le hle, (bessel_profile_1 hd (mul_pos hc ht)).2.1 ω, mul_assoc,
    maternExponent_mul_q hq hc, add_sub_cancel_right, Real.exp_neg, Real.exp_log hp]
  congr 2
  ring

/-! ## Clause (2) -/

/-- **`thm:matern-pyramid`(2), the functional equation.** A continuous `F̃` on `[0,∞)` with
`F̃(0) = 0` and `F̃(qr) - F̃(r) = log(1 + c²r²)` is `F_q` on `[0,∞)`. -/
theorem matern_pyramid_2_equation {q c : ℝ} (hq : 1 < q) (hc : 0 < c) (F : ℝ → ℝ)
    (hcont : ContinuousOn F (Ici 0)) (h0 : F 0 = 0)
    (heq : ∀ r : ℝ, 0 ≤ r → F (q * r) - F r = Real.log (1 + c ^ 2 * r ^ 2)) :
    ∀ r : ℝ, 0 ≤ r → F r = maternExponent q c r := by
  intro r hr
  rcases hr.eq_or_lt with rfl | hr
  · rw [h0, maternExponent_zero]
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have h := (hcont 0 self_mem_Ici).tendsto
    rw [h0] at h
    exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  exact matern_pyramid_line_2_direct hq hc F (fun ω hω => heq ω hω.le) hlim r hr

/-- `F_q` is strictly increasing on `[0,∞)`. -/
theorem maternExponent_strictMonoOn (hq : 1 < q) (hc : 0 < c) :
    StrictMonoOn (maternExponent q c) (Ici 0) := by
  intro r hr s hs hrs
  have hq0 : 0 < q := by linarith
  refine Summable.tsum_lt_tsum (i := 0) (fun i => ?_) ?_ (summable_maternExponent hq hc r)
    (summable_maternExponent hq hc s)
  · refine Real.log_le_log (by positivity) ?_
    have : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr hrs.le 2
    gcongr
  · refine Real.log_lt_log (by positivity) ?_
    have : r ^ 2 < s ^ 2 := pow_lt_pow_left₀ hrs hr two_ne_zero
    gcongr

/-- A unit vector of `ℝ^d`, `d ≥ 1`. -/
theorem exists_unit_Rd (hd : 1 ≤ d) : ∃ e : Rd d, ‖e‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, hd⟩ 1, by simp⟩

/-- **`thm:matern-pyramid`(2), the family.** An isotropic fully covariant family whose knot
kernels `μ'_{0,q^n}`, `n ∈ ℤ`, have the transforms `exp(-F_q(q^n|ω|))` is the Matérn pyramid read
in a gauge `χ` with `χ(q^n) = q^n`. -/
theorem matern_pyramid_2_family (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ) (μ' : ℝ → ℝ → Measure (Rd d))
    (hμ' : ∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily μ' S)
    (hknots : ∀ (n : ℤ) (ω : Rd d),
      charFun (μ' 0 (q ^ n)) ω = ((Real.exp (-maternExponent q c (q ^ n * ‖ω‖)) : ℝ) : ℂ)) :
    ∃ χ : ℝ → ℝ, IsGauge χ ∧ (∀ n : ℤ, χ (q ^ n) = q ^ n) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (χ s) (χ t) := by
  obtain ⟨S, hS⟩ := hμ'
  have hprob := hS.isProbability
  obtain ⟨χ, F, hχ, hF, -, hrep⟩ := (cited_A31 hd μ' hprob).1 ⟨S, hS⟩
  have hF0 : F 0 = 0 := classA_zero hF
  obtain ⟨e, he⟩ := exists_unit_Rd hd
  have ha : 0 < χ 1 := by
    have h := hχ.2.1 self_mem_Ici (show (1 : ℝ) ∈ Ici 0 from mem_Ici.2 zero_le_one) zero_lt_one
    rwa [hχ.1] at h
  set a := χ 1 with ha_def
  -- the knot `n = 0`: `F(ar) = F_q(r)`
  have hFa : ∀ r : ℝ, 0 ≤ r → F (a * r) = maternExponent q c r := by
    intro r hr
    have h1 := hknots 0 (r • e)
    rw [zpow_zero, one_mul, hrep 0 1 le_rfl zero_le_one, hχ.1, zero_mul, hF0, sub_zero,
      norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hr] at h1
    have h2 := Complex.ofReal_injective h1
    have h3 := Real.exp_injective h2
    linarith
  set χ' : ℝ → ℝ := fun t => χ t / a with hχ'
  have hχ'0 : ∀ t, 0 ≤ t → 0 ≤ χ' t := fun t ht => by
    have h := hχ.2.1.monotoneOn self_mem_Ici (show t ∈ Ici 0 from ht) ht
    rw [hχ.1] at h
    exact div_nonneg h ha.le
  have hgauge : IsGauge χ' := by
    refine ⟨by simp [hχ', hχ.1], fun u hu v hv huv => div_lt_div_of_pos_right
      (hχ.2.1 hu hv huv) ha, fun y hy => ?_⟩
    obtain ⟨x, hx, hxy⟩ := hχ.2.2 (show a * y ∈ Ici 0 from mul_nonneg ha.le hy)
    exact ⟨x, hx, by simp only [hχ']; rw [hxy]; field_simp⟩
  have hrep' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d, charFun (μ' s t) ξ =
      ((Real.exp (-(maternExponent q c (χ' t * ‖ξ‖) - maternExponent q c (χ' s * ‖ξ‖))) : ℝ) :
        ℂ) := by
    intro s t hs hst ξ
    rw [hrep s t hs hst ξ, ← hFa _ (mul_nonneg (hχ'0 t (hs.trans hst)) (norm_nonneg ξ)),
      ← hFa _ (mul_nonneg (hχ'0 s hs) (norm_nonneg ξ))]
    simp only [hχ']
    congr 4 <;> field_simp
  have hmono : MonotoneOn χ' (Ici 0) := hgauge.2.1.monotoneOn
  have hχ'0' : χ' 0 = 0 := hgauge.1
  refine ⟨χ', hgauge, fun n => ?_, fun s t hs hst => ?_⟩
  · have hqn : 0 < q ^ n := zpow_pos (by linarith) n
    have h1 := hknots n e
    rw [hrep' 0 (q ^ n) le_rfl hqn.le, hχ'0', zero_mul, maternExponent_zero, sub_zero, he,
      mul_one, mul_one] at h1
    have h2 := Real.exp_injective (Complex.ofReal_injective h1)
    have h3 : maternExponent q c (χ' (q ^ n)) = maternExponent q c (q ^ n) := by linarith
    exact (maternExponent_strictMonoOn hq hc).injOn (hχ'0 _ hqn.le) hqn.le h3
  · have hs' := hχ'0 s hs
    have hst' : χ' s ≤ χ' t := hmono hs (hs.trans hst) hst
    haveI := hprob s t hs hst
    haveI := (hμ _ _ hs' hst').1
    refine Measure.ext_of_charFun (funext fun ξ => ?_)
    rw [hrep' s t hs hst ξ, charFun_maternPyramid hμ hs' hst']

end Pyramids
