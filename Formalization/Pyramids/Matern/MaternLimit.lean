/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.MaternProjections
import Pyramids.LineAppendix.MaternLineLimit

/-!
# `thm:matern-pyramid`(5): the limit `q ↓ 1`

Blueprint: `blueprint/src/parts/04-matern.tex`, `thm:matern-pyramid`. Phase 5, wave 3b. The five
declarations of clause (5) moved here from `PyramidsSkeleton.Ch04Matern` with their conclusions
unchanged. `matern_pyramid_5_weak` no longer takes `1 ≤ d` and `0 ≤ t`, which its proof does not
read (2026-11-15, a strengthening).

* **The limit** is the line's (`tendstoLocallyUniformly_maternExponent`), a statement in `r` alone,
  with `F_∞ = -½ Li₂(-c²·²)` (`maternLineLimit_eq_dilog`).
* **`Λ ∈ 𝒜_d`.** The profile `k(r) = ∫₀^∞ b_d(re^u/c) du` is nonnegative, nonincreasing and
  `≤ 2C_dc/r` (`b_d(y) ≤ 2C_d/y`), so it is an origin datum (`originDatumOfLe`). Its polar
  measure is the integral over `u` of the polar measures of `b_d(·e^u/c)`
  (`lintegral_polarLevyMeasure_integral`, Tonelli), and `lem:bessel-profile`(2) at
  `β = c²e^{-2u}` gives the exponent
  `∫₀^∞ log(1 + c²e^{-2u}|ξ|²) du = F_∞(|ξ|) = Λ(|ξ|)`; A35 gives `Λ ∈ 𝒜_d`.
* **The multiples.** `(0, ℓk_d)` is an origin datum with the exponent `ℓF_q`; the laws are the
  images of the law of `𝒜_d` under `x ↦ tx`.
* **Weak convergence.** Mathlib's Lévy continuity theorem along every sequence `q_n ↓ 1`, as on the
  line.
* **The kernels.** `F_q → ∞` off the origin is the line's (`tendsto_exp_neg_maternExponent`). A weak
  limit of the kernels in `ℝ^d` would give one of their marginals along a unit vector, which are the
  kernels of the line's Matérn pyramids (`matern_pyramid_3_marginal`), against
  `thm:matern-pyramid-line`(4).

**What it reaches.** The limit prints Lean core; `Λ ∈ 𝒜_d` and the multiples print A35's names; the
weak convergence prints Lean core; the kernels print `levy_khintchine_converse` (through the line's
clause (4)).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace BoundedContinuousFunction

variable {d : ℕ} {q c : ℝ}

/-- **`thm:matern-pyramid`(5), the limit.** `ℓ F_q → Λ = -½ Li₂(-c²·²)` locally uniformly as
`q ↓ 1`, `ℓ = log q`. -/
theorem matern_pyramid_5_limit {c : ℝ} (hc : 0 < c) :
    TendstoLocallyUniformly (fun q r => Real.log q * maternExponent q c r)
      (maternLimitExponent c) (𝓝[>] 1) := by
  have h : maternLineLimit c = maternLimitExponent c := funext (maternLineLimit_eq_dilog c)
  rw [← h]
  exact tendstoLocallyUniformly_maternExponent hc

/-! ## `Λ ∈ 𝒜_d` -/

/-- **The polar measure of an integral of profiles**, tested on a measurable function, is the
integral of the tests. -/
theorem lintegral_polarLevyMeasure_integral (k : ℝ → ℝ → ℝ)
    (hk0 : ∀ u r, 0 < r → 0 ≤ k u r) (hint : ∀ r, 0 < r → IntegrableOn (fun u => k u r) (Ioi 0))
    (hm : Measurable (Function.uncurry k)) (G : Rd d → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂polarLevyMeasure d (fun r => ∫ u in Ioi 0, k u r) =
      ∫⁻ u in Ioi 0, ∫⁻ x, G x ∂polarLevyMeasure d (k u) := by
  set dens : (ℝ → ℝ) → Rd d → ℝ≥0∞ := fun k x =>
    ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x with hdens
  have hn : Measurable fun x : Rd d => ‖x‖ := measurable_norm
  have hA : 0 ≤ sphereArea d :=
    div_nonneg (by positivity) (Real.Gamma_nonneg_of_nonneg (by positivity))
  have hjoint : Measurable (Function.uncurry fun (u : ℝ) (x : Rd d) => dens (k u) x) := by
    refine Measurable.indicator ?_ ((measurableSet_singleton 0).compl.preimage measurable_snd)
    exact ((hm.comp (measurable_fst.prodMk (hn.comp measurable_snd))).div
      (measurable_const.mul ((hn.comp measurable_snd).pow_const d))).ennreal_ofReal
  have hsum : dens (fun r => ∫ u in Ioi 0, k u r) = fun x => ∫⁻ u in Ioi 0, dens (k u) x := by
    funext x
    by_cases hx : x = 0
    · simp [hdens, hx]
    · have hx' : x ∈ ({0}ᶜ : Set (Rd d)) := hx
      have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
      simp only [hdens, indicator_of_mem hx']
      rw [← integral_div, ofReal_integral_eq_lintegral_ofReal ((hint _ hr).div_const _)
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u _ =>
          div_nonneg (hk0 u _ hr) (by positivity)))]
  have hpolar : ∀ k, polarLevyMeasure d k = volume.withDensity (dens k) := fun k => rfl
  have hmeas : Measurable (dens fun r => ∫ u in Ioi 0, k u r) := by
    rw [hsum]; exact hjoint.lintegral_prod_left'
  have hi : ∀ u, ∫⁻ x, G x ∂polarLevyMeasure d (k u) = ∫⁻ x, dens (k u) x * G x := fun u => by
    have hu : Measurable (dens (k u)) := hjoint.comp measurable_prodMk_left
    rw [hpolar, lintegral_withDensity_eq_lintegral_mul _ hu hG]
    rfl
  rw [hpolar, lintegral_withDensity_eq_lintegral_mul _ hmeas hG, hsum]
  simp_rw [hi]
  rw [lintegral_lintegral_swap (by exact (hjoint.mul (hG.comp measurable_snd)).aemeasurable)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  exact (lintegral_mul_const _ (by exact hjoint.comp measurable_prodMk_right)).symm

/-- The profile of `Λ`, `k(r) = ∫₀^∞ b_d(re^u/c) du`. -/
noncomputable def limitPolarProfile (c : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), besselProfile d (r * Real.exp u / c)

theorem limitProfile_term_le (hd : 1 ≤ d) (hc : 0 < c) {r : ℝ} (hr : 0 < r) (u : ℝ) :
    besselProfile d (r * Real.exp u / c) ≤
      2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / r * Real.exp (-u) := by
  have h := besselProfile_le_div hd (y := r * Real.exp u / c) (by positivity)
  refine h.trans (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

theorem integrableOn_limitProfile (hd : 1 ≤ d) (hc : 0 < c) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun u => besselProfile d (r * Real.exp u / c)) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul
    (2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / r)) ?_ (Eventually.of_forall fun u => ?_)
  · exact ((continuous_besselProfile hd).comp (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (besselProfile_nonneg hd _)]
    exact limitProfile_term_le hd hc hr u

theorem limitPolarProfile_le (hd : 1 ≤ d) (hc : 0 < c) {r : ℝ} (hr : 0 < r) :
    limitPolarProfile c d r ≤ 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / r := by
  have h := setIntegral_mono_on (integrableOn_limitProfile hd hc hr)
    ((integrableOn_exp_neg_Ioi 0).const_mul (2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / r))
    measurableSet_Ioi fun u _ => limitProfile_term_le hd hc hr u
  rwa [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one] at h

theorem limitPolarProfile_nonneg (hd : 1 ≤ d) (c r : ℝ) : 0 ≤ limitPolarProfile c d r :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => besselProfile_nonneg hd _

theorem limitPolarProfile_antitoneOn (hd : 1 ≤ d) (hc : 0 < c) :
    AntitoneOn (limitPolarProfile c d) (Ioi 0) := by
  intro r hr s hs hrs
  refine setIntegral_mono_on (integrableOn_limitProfile hd hc hs)
    (integrableOn_limitProfile hd hc hr) measurableSet_Ioi fun u _ => ?_
  have h1 : 0 ≤ r * Real.exp u / c := by have := hr.out.le; positivity
  have h2 : 0 ≤ s * Real.exp u / c := by have := hs.out.le; positivity
  have hle : r * Real.exp u / c ≤ s * Real.exp u / c := by gcongr
  exact (besselProfile_strictAntiOn hd).antitoneOn h1 h2 hle

/-- **The datum `(0, k)` of `Λ`.** -/
noncomputable def limitDatum (hd : 1 ≤ d) (hc : 0 < c) : OriginDatum d :=
  originDatumOfLe (limitPolarProfile c d) (fun r _ => limitPolarProfile_nonneg hd c r)
    (limitPolarProfile_antitoneOn hd hc) _ fun _ hr => limitPolarProfile_le hd hc hr

theorem maternLimitExponent_nonneg (c r : ℝ) : 0 ≤ maternLimitExponent c r := by
  rw [← maternLineLimit_eq_dilog]
  exact setIntegral_nonneg measurableSet_Ioi fun u _ =>
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))

theorem limitDatum_exponent (hd : 1 ≤ d) (hc : 0 < c) (ξ : Rd d) :
    maternLimitExponent c ‖ξ‖ = (limitDatum hd hc).exponent ξ := by
  rw [OriginDatum.exponent, exponentL_of_a_zero _ rfl]
  change _ = (∫⁻ x, _ ∂polarLevyMeasure d
    (fun r => ∫ u in Ioi (0 : ℝ), besselProfile d (r * Real.exp u / c))).toReal
  rw [lintegral_polarLevyMeasure_integral (fun u r => besselProfile d (r * Real.exp u / c))
    (fun u r _ => besselProfile_nonneg hd _) (fun r hr => integrableOn_limitProfile hd hc hr)
    ((continuous_besselProfile hd).measurable.comp (by fun_prop)) _ (by fun_prop)]
  have hterm : ∀ u, ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ξ, x⟫)
      ∂polarLevyMeasure d (fun r => besselProfile d (r * Real.exp u / c)) =
      ENNReal.ofReal (Real.log (1 + c ^ 2 * ‖ξ‖ ^ 2 * Real.exp (-2 * u))) := by
    intro u
    have hβ : 0 < c ^ 2 * Real.exp (-2 * u) := by positivity
    have h := bessel_profile_2 hd hβ ξ
    have hs : Real.sqrt (c ^ 2 * Real.exp (-2 * u)) = c * Real.exp (-u) := by
      rw [show c ^ 2 * Real.exp (-2 * u) = (c * Real.exp (-u)) ^ 2 by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf, Real.sqrt_sq (by positivity)]
    rw [hs] at h
    have e1 : (fun ρ : ℝ => besselProfile d (ρ / (c * Real.exp (-u)))) =
        fun ρ => besselProfile d (ρ * Real.exp u / c) := by
      funext ρ; congr 1; rw [Real.exp_neg]; field_simp
    rw [e1] at h
    rw [← h]
    congr 2
    ring
  simp_rw [hterm]
  rw [← ofReal_integral_eq_lintegral_ofReal, ENNReal.toReal_ofReal, ← maternLineLimit_eq_dilog,
    maternLineLimit]
  · exact setIntegral_nonneg measurableSet_Ioi fun u _ =>
      Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  · have h := integrableOn_limitIntegrand (A := c ^ 2 * ‖ξ‖ ^ 2) (by positivity)
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [limitIntegrand]
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u _ =>
      Real.log_nonneg (le_add_of_nonneg_right (by positivity)))

/-- **`thm:matern-pyramid`(5), the limit is admissible**: `Λ ∈ 𝒜_d`, the exponent of an origin
datum with the polar profile `∫₀^∞ b_d(re^u/c) du`. -/
theorem matern_pyramid_5_classA (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) :
    classA d (maternLimitExponent c) ∧ ∃ D : OriginDatum d,
      (∀ r : ℝ, 0 < r → D.k r = ∫ u in Ioi (0 : ℝ), besselProfile d (r * Real.exp u / c)) ∧
        ∀ ξ : Rd d, maternLimitExponent c ‖ξ‖ = D.exponent ξ :=
  ⟨(cited_A35_classA hd _ fun r _ => maternLimitExponent_nonneg c r).2
      ⟨limitDatum hd hc, limitDatum_exponent hd hc⟩,
    limitDatum hd hc, fun _ _ => rfl, limitDatum_exponent hd hc⟩

/-! ## The multiples -/

/-- The datum `(0, ℓk_d)` of `ℓF_q`. -/
noncomputable def maternDatumSmul (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) : OriginDatum d :=
  originDatumOfLe (fun r => Real.log q * maternPolarProfile q c d r)
    (fun r _ => mul_nonneg (Real.log_nonneg hq.le) (maternPolarProfile_nonneg hd q c r))
    (fun r hr s hs hrs => mul_le_mul_of_nonneg_left
      (maternPolarProfile_antitoneOn hd hq hc hr hs hrs) (Real.log_nonneg hq.le))
    (Real.log q * (2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / (q - 1)))
    fun r hr => by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (maternPolarProfile_le hd hq hc hr) (Real.log_nonneg hq.le)

theorem maternDatumSmul_exponent (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) (ξ : Rd d) :
    Real.log q * maternExponent q c ‖ξ‖ = (maternDatumSmul hd hq hc).exponent ξ := by
  have hℓ : 0 ≤ Real.log q := Real.log_nonneg hq.le
  have hscale : polarLevyMeasure d (fun r => Real.log q * maternPolarProfile q c d r) =
      ENNReal.ofReal (Real.log q) • polarLevyMeasure d (maternPolarProfile q c d) := by
    rw [polarLevyMeasure, polarLevyMeasure,
      ← withDensity_smul' (ENNReal.ofReal (Real.log q)) _ ENNReal.ofReal_ne_top]
    congr 1
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · have hx' : x ∈ ({0}ᶜ : Set (Rd d)) := hx
      simp only [Pi.smul_apply, smul_eq_mul, indicator_of_mem hx']
      rw [← ENNReal.ofReal_mul hℓ, mul_div_assoc]
  rw [OriginDatum.exponent, exponentL_of_a_zero _ rfl]
  change _ = (∫⁻ x, _ ∂polarLevyMeasure d
    (fun r => Real.log q * maternPolarProfile q c d r)).toReal
  have h2 := maternDatum_exponentL hd hq hc ξ
  rw [exponentL_of_a_zero _ rfl] at h2
  change ∫⁻ x, _ ∂polarLevyMeasure d (maternPolarProfile q c d) = _ at h2
  rw [hscale, lintegral_smul_measure, h2, smul_eq_mul, ← ENNReal.ofReal_mul hℓ,
    ENNReal.toReal_ofReal (mul_nonneg hℓ (maternExponent_nonneg hq hc _))]

/-- **`thm:matern-pyramid`(5), the multiples.** `ℓ F_q ∈ 𝒜_d`, and the laws with exponent
`ℓ F_q(t|·|)` exist. -/
theorem matern_pyramid_5_multiples (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    classA d (fun r => Real.log q * maternExponent q c r) ∧
      ∀ t : ℝ, 0 ≤ t → ∃ ν : Measure (Rd d), IsProbabilityMeasure ν ∧ ∀ ω : Rd d,
        charFun ν ω = ((Real.exp (-(Real.log q * maternExponent q c (t * ‖ω‖))) : ℝ) : ℂ) := by
  have hA : classA d (fun r => Real.log q * maternExponent q c r) :=
    (cited_A35_classA hd _ fun r _ =>
      mul_nonneg (Real.log_nonneg hq.le) (maternExponent_nonneg hq hc r)).2
      ⟨maternDatumSmul hd hq hc, maternDatumSmul_exponent hd hq hc⟩
  refine ⟨hA, fun t ht => ?_⟩
  obtain ⟨μ, hμ, -, hcf⟩ := hA.2
  haveI := hμ
  refine ⟨μ.map fun x => t • x, Measure.isProbabilityMeasure_map (by fun_prop), fun ω => ?_⟩
  rw [charFun_map_smul, hcf, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

/-! ## Weak convergence, and the kernels -/

/-- **`thm:matern-pyramid`(5), weak convergence.** At every scale `t`, laws with exponent
`ℓ F_q(t|·|)` converge weakly, as `q ↓ 1`, to the law with exponent `Λ(t|·|)`. -/
theorem matern_pyramid_5_weak {c : ℝ} (hc : 0 < c) {t : ℝ}
    (ν : ℝ → Measure (Rd d))
    (hν : ∀ q : ℝ, 1 < q → IsProbabilityMeasure (ν q) ∧ ∀ ω : Rd d,
      charFun (ν q) ω = ((Real.exp (-(Real.log q * maternExponent q c (t * ‖ω‖))) : ℝ) : ℂ))
    (ν₀ : Measure (Rd d)) [IsProbabilityMeasure ν₀]
    (hν₀ : ∀ ω : Rd d, charFun ν₀ ω = ((Real.exp (-maternLimitExponent c (t * ‖ω‖)) : ℝ) : ℂ)) :
    ∀ φ : Rd d →ᵇ ℝ, Tendsto (fun q => ∫ x, φ x ∂(ν q)) (𝓝[>] 1) (𝓝 (∫ x, φ x ∂ν₀)) := by
  intro φ
  rw [tendsto_iff_seq_tendsto]
  intro x hx
  have hev : ∀ᶠ n in atTop, 1 < x n := hx self_mem_nhdsWithin
  classical
  let μs : ℕ → ProbabilityMeasure (Rd d) := fun n =>
    if h : 1 < x n then ⟨ν (x n), (hν _ h).1⟩ else ⟨ν₀, inferInstance⟩
  let μ₀ : ProbabilityMeasure (Rd d) := ⟨ν₀, inferInstance⟩
  have hμs : ∀ n, 1 < x n → (μs n : Measure (Rd d)) = ν (x n) := fun n hn => by
    simp only [μs, dif_pos hn]
    rfl
  have hcf : ∀ ω : Rd d, Tendsto (fun n => charFun (μs n : Measure (Rd d)) ω) atTop
      (𝓝 (charFun (μ₀ : Measure (Rd d)) ω)) := by
    intro ω
    have hlim := (Complex.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp
      ((tendsto_maternExponent_at hc (t * ‖ω‖)).comp hx).neg)
    rw [show (μ₀ : Measure (Rd d)) = ν₀ from rfl, hν₀ ω, ← maternLineLimit_eq_dilog]
    refine hlim.congr' ?_
    filter_upwards [hev] with n hn
    rw [hμs n hn, (hν _ hn).2 ω]
    rfl
  have hw := ProbabilityMeasure.tendsto_of_tendsto_charFun hcf
  have hφ := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hw φ
  refine hφ.congr' ?_
  filter_upwards [hev] with n hn
  simp only [Function.comp_apply]
  rw [hμs n hn]

/-- **`thm:matern-pyramid`(5), the limit law exists** (fidelity review, R24). For `d ≥ 1`, `c > 0`
and every scale `t`, the law `ν₀` with the exponent `Λ(t|·|)` exists, and every choice of laws `ν_q`
with the exponents `ℓF_q(t|·|)`, `q > 1` (which exist, `matern_pyramid_5_multiples`), converges
weakly to it as `q ↓ 1`. -/
theorem matern_pyramid_5_limit_exists (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∃ ν₀ : Measure (Rd d), IsProbabilityMeasure ν₀ ∧
      (∀ ω : Rd d, charFun ν₀ ω = ((Real.exp (-maternLimitExponent c (t * ‖ω‖)) : ℝ) : ℂ)) ∧
      ∀ ν : ℝ → Measure (Rd d), (∀ q : ℝ, 1 < q → IsProbabilityMeasure (ν q) ∧ ∀ ω : Rd d,
        charFun (ν q) ω = ((Real.exp (-(Real.log q * maternExponent q c (t * ‖ω‖))) : ℝ) : ℂ)) →
        ∀ φ : Rd d →ᵇ ℝ, Tendsto (fun q => ∫ x, φ x ∂(ν q)) (𝓝[>] 1) (𝓝 (∫ x, φ x ∂ν₀)) := by
  obtain ⟨-, μ₀, hμ₀, -, hcf₀⟩ := (matern_pyramid_5_classA hd hc).1
  haveI := hμ₀
  have h2 : ∀ x : ℝ, maternLimitExponent c (|t| * x) = maternLimitExponent c (t * x) := by
    intro x; simp only [maternLimitExponent, mul_pow, sq_abs]
  have hcf : ∀ ω : Rd d, charFun (μ₀.map fun x => t • x) ω =
      ((Real.exp (-maternLimitExponent c (t * ‖ω‖)) : ℝ) : ℂ) := fun ω => by
    rw [charFun_map_smul, hcf₀, norm_smul, Real.norm_eq_abs, h2]
  haveI : IsProbabilityMeasure (μ₀.map fun x => t • x) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact ⟨_, inferInstance, hcf, fun ν hν => matern_pyramid_5_weak hc ν hν _ hcf⟩

/-- **`thm:matern-pyramid`(5), the kernels do not converge.** For `t > 0`,
`μ̂_t(ω) = e^{-F_q(t|ω|)} → 0` at `ω ≠ 0` since `F_q → ∞`, and the kernels `μ_t` of the Matérn
pyramids have no weak limit as `q ↓ 1`. -/
theorem matern_pyramid_5_kernels (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    (∀ ω : Rd d, ω ≠ 0 →
      Tendsto (fun q => Real.exp (-maternExponent q c (t * ‖ω‖))) (𝓝[>] 1) (𝓝 0)) ∧
      (∀ r : ℝ, 0 < r → Tendsto (fun q => maternExponent q c r) (𝓝[>] 1) atTop) ∧
      ∀ μ : ℝ → ℝ → ℝ → Measure (Rd d), (∀ q : ℝ, 1 < q → IsMaternPyramid q c (μ q)) →
        ¬ ∃ ν : Measure (Rd d), IsProbabilityMeasure ν ∧ ∀ φ : Rd d →ᵇ ℝ,
          Tendsto (fun q => ∫ x, φ x ∂(μ q 0 t)) (𝓝[>] 1) (𝓝 (∫ x, φ x ∂ν)) := by
  refine ⟨fun ω hω => tendsto_exp_neg_maternExponent hc
    (mul_ne_zero ht.ne' (norm_ne_zero_iff.2 hω)), fun r hr => ?_, fun μ hμ => ?_⟩
  · have h := tendsto_exp_neg_maternExponent hc (c := c) hr.ne'
    have h2 : Tendsto (fun q => -maternExponent q c r) (𝓝[>] 1) atBot :=
      Real.tendsto_exp_comp_nhds_zero.1 h
    exact tendsto_neg_atBot_iff.1 h2
  · rintro ⟨ν, hν, hconv⟩
    obtain ⟨e, he⟩ := exists_unit_Rd hd
    have hπ : Continuous fun x : Rd d => ⟪e, x⟫ := continuous_inner_left e
    have hline := (matern_pyramid_line_4_laws hc ht).2.2.2
      (fun q s t => marginal e (μ q s t))
      (fun q hq => matern_pyramid_3_marginal (μ q) (hμ q hq) e he)
    refine hline ⟨marginal e ν, inferInstance, fun φ => ?_⟩
    have h := hconv (φ.compContinuous ⟨fun x => ⟪e, x⟫, hπ⟩)
    simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] at h
    have e1 : ∀ m : Measure (Rd d), ∫ x, φ x ∂(marginal e m) = ∫ x, φ ⟪e, x⟫ ∂m := fun m => by
      rw [marginal, integral_map hπ.aemeasurable φ.continuous.aestronglyMeasurable]
    simp only [e1]
    exact h

end Pyramids
