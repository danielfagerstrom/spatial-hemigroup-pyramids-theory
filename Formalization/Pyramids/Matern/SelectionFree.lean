/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.SelectionStage
import Pyramids.Pyramid.LadderClassA

/-!
# `thm:selection-stratum-two`(1): the stages between the rungs are free

Blueprint: `blueprint/src/parts/04-matern.tex`, `thm:selection-stratum-two`. Phase 5, wave 3b (on
the VM).

* **The data of `L_{√τ}`.** `ν` has the polar profile `b_d(·/√τ)`, nonincreasing with
  `b_d(y) ≤ 2C_d/y`, so it is an origin datum's Lévy measure (`originDatumOfLe`), and its exponent
  is `log(1 + τ|ω|²)` (`lem:bessel-profile`(2)). Its logarithmic moment is finite:
  `log₊ r · b_d(r/√τ)/r ≤ C_d e^{-r/(2√τ)}`.
* **The split.** `ν_a`, `ν_b` are the radial measures of the profile cut at `r = 1`; they add up to
  `ν`, are carried by `{|x| ≤ 1}` and `{|x| > 1}`, are nonzero (`b_d > 0`), and are invariant under
  every isometry, as is `ν*` (`ladderNuStar_radial`).
* **The two families** are the uniform and the split coupling of `prop:ladder-knot-kernel`(2),
  with their isotropy (`ladder_knot_kernel_2_split_rot`), which carry A39 through
  `SymLevyData.eq_of_exponent`. Rescaled by `t`, `(μ_{s/t,u/t})`, they have the ladder through
  `t`; a relabelling `g` of the rescaled families is the relabelling `u ↦ g(tu)/t` of the given
  ones.
  They differ, since the identity is in `𝒢_q`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The profile `b_d(·/√τ)` -/

/-- `b_d > 0` on `[0,∞)`. -/
theorem besselProfile_pos (hd : 1 ≤ d) {y : ℝ} (hy : 0 ≤ y) : 0 < besselProfile d y :=
  lt_of_le_of_lt (besselProfile_nonneg hd (y + 1))
    ((bessel_profile_3 hd).2.2.1 (mem_Ici.2 hy) (mem_Ici.2 (by linarith)) (by linarith))

theorem stepProfile_antitoneOn (hd : 1 ≤ d) (τ : ℝ) :
    AntitoneOn (fun r => besselProfile d (r / Real.sqrt τ)) (Ioi 0) := fun _ hr _ hs hrs =>
  (bessel_profile_3 hd).2.2.1.antitoneOn (mem_Ici.2 (div_nonneg (le_of_lt hr) (Real.sqrt_nonneg _)))
    (mem_Ici.2 (div_nonneg (le_of_lt hs) (Real.sqrt_nonneg _)))
    (div_le_div_of_nonneg_right hrs (Real.sqrt_nonneg τ))

theorem stepProfile_le (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) {r : ℝ} (hr : 0 < r) :
    besselProfile d (r / Real.sqrt τ) ≤ 2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * Real.sqrt τ / r := by
  have h := besselProfile_le_div hd (div_pos hr (Real.sqrt_pos.2 hτ))
  rwa [div_div_eq_mul_div] at h

/-- **The origin datum of `L_{√τ}`**: no Gaussian part, the profile `b_d(·/√τ)`. -/
noncomputable def stepDatum (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) : OriginDatum d :=
  originDatumOfLe (fun r => besselProfile d (r / Real.sqrt τ))
    (fun _ _ => besselProfile_nonneg hd _) (stepProfile_antitoneOn hd τ) _
    fun _ hr => stepProfile_le hd hτ hr

/-- **The data of `L_{√τ}`.** -/
noncomputable def stepData (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) : SymLevyData d :=
  originSymData hd (stepDatum hd hτ)

/-- The radial profile of `L_{√τ}`'s Lévy measure, in `[0,∞]`. -/
noncomputable def stepKappa (d : ℕ) (τ : ℝ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (besselProfile d (r / Real.sqrt τ))

theorem measurable_stepKappa (hd : 1 ≤ d) (τ : ℝ) : Measurable (stepKappa d τ) :=
  ENNReal.measurable_ofReal.comp ((continuous_besselProfile hd).measurable.comp
    (measurable_id.div_const _))

theorem stepData_ν (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    (stepData hd hτ).ν = radialMeasure d (stepKappa d τ) := by
  rw [show (stepData hd hτ).ν = polarLevyMeasure d (fun r => besselProfile d (r / Real.sqrt τ))
    from rfl, polarLevyMeasure_eq_radial hd]
  rfl

theorem stepData_A (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    (stepData hd hτ).A = ((stepDatum hd hτ).a / 2) • (1 : Mat d) := rfl

theorem stepData_exponent (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) (ω : Rd d) :
    (stepData hd hτ).exponent ω = Real.log (1 + τ * ‖ω‖ ^ 2) := by
  rw [stepData, originSymData_exponent, OriginDatum.exponent,
    exponentL_of_a_zero (stepDatum hd hτ) rfl,
    show (stepDatum hd hτ).k = fun r => besselProfile d (r / Real.sqrt τ) from rfl,
    ← bessel_profile_2 hd hτ ω, ENNReal.toReal_ofReal (Real.log_nonneg (by
      have : 0 ≤ τ * ‖ω‖ ^ 2 := by positivity
      linarith))]

theorem isSymData_step (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    IsSymData (maternStep d (Real.sqrt τ)) (stepData hd hτ) := fun ω => by
  rw [(charFun_maternStep _ ω).2, stepData_exponent, Real.sq_sqrt hτ.le,
    inv_one_add_eq_exp (by positivity)]

/-! ## Radial measures in polar coordinates -/

/-- `∫ G(|x|) dν = ∫₀^∞ G(r) κ(r) dr/r` for the radial measure of `κ`. -/
theorem lintegral_radialMeasure (hd : 1 ≤ d) {κ : ℝ → ℝ≥0∞} (hκ : Measurable κ) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ x, G ‖x‖ ∂radialMeasure d κ = ∫⁻ r in Ioi 0, κ r * ENNReal.ofReal r⁻¹ * G r := by
  rw [← lintegral_map hG measurable_norm, radialMeasure_map_norm hd hκ,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hG]
  rfl

/-- The logarithmic moment of `L_{√τ}`'s Lévy measure is finite. -/
theorem lintegral_posLog_step (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(stepData hd hτ).ν < ⊤ := by
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  set C : ℝ := (2 : ℝ) ^ (1 + (d : ℝ) / 2) with hC
  set b : ℝ := 1 / (2 * Real.sqrt τ) with hb
  have hb0 : 0 < b := by positivity
  rw [stepData_ν, lintegral_radialMeasure hd (measurable_stepKappa hd τ)
    (G := fun r => ENNReal.ofReal (Real.posLog r)) (by fun_prop)]
  have hI : IntegrableOn (fun r : ℝ => C * Real.exp (-b * r)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hb0).const_mul C
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun r hr => ?_)
    (hI.lintegral_lt_top)
  have hr0 : 0 < r := hr
  have hk0 := besselProfile_nonneg hd (r / Real.sqrt τ)
  have hlog : Real.posLog r ≤ r := by
    rw [Real.posLog, max_le_iff]
    exact ⟨hr0.le, (Real.log_le_sub_one_of_pos hr0).trans (by linarith)⟩
  have hlog0 : 0 ≤ Real.posLog r := Real.posLog_nonneg
  rw [stepKappa, ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : besselProfile d (r / Real.sqrt τ) * r⁻¹ * Real.posLog r ≤
      besselProfile d (r / Real.sqrt τ) := by
    have : r⁻¹ * Real.posLog r ≤ 1 := by
      rw [inv_mul_le_iff₀ hr0]; linarith
    calc _ = besselProfile d (r / Real.sqrt τ) * (r⁻¹ * Real.posLog r) := by ring
      _ ≤ besselProfile d (r / Real.sqrt τ) * 1 := mul_le_mul_of_nonneg_left this hk0
      _ = _ := mul_one _
  refine h1.trans ((besselProfile_le hd _).trans (le_of_eq ?_))
  rw [hb]
  congr 2
  field_simp

/-! ## The split at `|x| = 1` -/

theorem radialMeasure_add {κ₁ κ₂ : ℝ → ℝ≥0∞} (hκ₁ : Measurable κ₁) :
    radialMeasure d κ₁ + radialMeasure d κ₂ = radialMeasure d (κ₁ + κ₂) := by
  unfold radialMeasure
  rw [← withDensity_add_left (measurable_radialDensity hκ₁)]
  congr 1
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · have hx' : x ∈ ({0}ᶜ : Set (Rd d)) := hx
    simp only [Pi.add_apply, indicator_of_mem hx', add_mul]

/-- The radial measure of `1_S κ` is carried by `{|x| ∈ S}`. -/
theorem radialMeasure_indicator_compl {S : Set ℝ} (hS : MeasurableSet S) (κ : ℝ → ℝ≥0∞) :
    radialMeasure d (S.indicator κ) ((fun x : Rd d => ‖x‖) ⁻¹' S)ᶜ = 0 := by
  have hm : MeasurableSet ((fun x : Rd d => ‖x‖) ⁻¹' S)ᶜ := (measurable_norm hS).compl
  rw [radialMeasure, withDensity_apply _ hm, ← lintegral_indicator hm]
  refine (lintegral_congr fun x => ?_).trans lintegral_zero
  by_cases hx : x ∈ ((fun x : Rd d => ‖x‖) ⁻¹' S)ᶜ
  · rw [indicator_of_mem hx]
    have hxS : ‖x‖ ∉ S := hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hx0' : x ∈ ({0}ᶜ : Set (Rd d)) := hx0
      rw [indicator_of_mem hx0', indicator_of_notMem hxS, zero_mul]
  · rw [indicator_of_notMem hx]

/-- A radial measure with `κ(r)/r ≥ c > 0` on an interval is nonzero. -/
theorem radialMeasure_ne_zero (hd : 1 ≤ d) {κ : ℝ → ℝ≥0∞} (hκ : Measurable κ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {c : ℝ≥0∞} (hc : c ≠ 0)
    (hlow : ∀ r ∈ Ioo a b, c ≤ κ r * ENNReal.ofReal r⁻¹) : radialMeasure d κ ≠ 0 := by
  intro h0
  have h := lintegral_radialMeasure hd hκ (G := fun _ => 1) measurable_const
  rw [h0, lintegral_zero_measure] at h
  have h2 : c * volume (Ioo a b) ≤ ∫⁻ r in Ioi 0, κ r * ENNReal.ofReal r⁻¹ * 1 := by
    rw [← setLIntegral_const]
    refine le_trans ?_ (lintegral_mono_set (s := Ioo a b)
      (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le)))
    refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
    rw [mul_one]
    exact hlow r hr
  rw [← h, nonpos_iff_eq_zero, mul_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hc h2
  · linarith

/-! ## The two families with the ladder of `L_{√τ}` -/

/-- **The rescaled family** `(μ_{s/t, u/t})`. -/
noncomputable def rescaleFamily (μ : ℝ → ℝ → Measure (Rd d)) (t : ℝ) : ℝ → ℝ → Measure (Rd d) :=
  fun s u => μ (s / t) (u / t)

theorem isIsotropicFamily_rescale {μ : ℝ → ℝ → Measure (Rd d)} (hμ : IsIsotropicFamily μ)
    {t : ℝ} (ht : 0 < t) : IsIsotropicFamily (rescaleFamily μ t) := by
  have hdiv : ∀ s u : ℝ, 0 ≤ s → s ≤ u → 0 ≤ s / t ∧ s / t ≤ u / t := fun s u hs hsu =>
    ⟨div_nonneg hs ht.le, div_le_div_of_nonneg_right hsu ht.le⟩
  refine ⟨⟨⟨fun s u hs hsu => hμ.1.1.isProbability _ _ (hdiv s u hs hsu).1 (hdiv s u hs hsu).2,
    fun u hu => hμ.1.1.diag _ (div_nonneg hu ht.le),
    fun r s u hr hrs hsu => hμ.1.1.cascade _ _ _ (div_nonneg hr ht.le)
      (div_le_div_of_nonneg_right hrs ht.le) (div_le_div_of_nonneg_right hsu ht.le),
    fun ω => ?_⟩, fun s u hs hsu => hμ.1.2 _ _ (div_nonneg hs ht.le)
      (div_lt_div_of_pos_right hsu ht)⟩,
    fun s u hs hsu => hμ.2 _ _ (hdiv s u hs hsu).1 (hdiv s u hs hsu).2⟩
  refine (hμ.1.1.continuous ω).comp ((continuous_fst.div_const t).prodMk
    (continuous_snd.div_const t)).continuousOn fun p hp => hdiv p.1 p.2 hp.1 hp.2

theorem isCovariantAt_rescale {μ : ℝ → ℝ → Measure (Rd d)} {q : ℝ}
    (hcov : IsCovariantAt μ q fun u => q * u) (t : ℝ) (ht : 0 < t) :
    IsCovariantAt (rescaleFamily μ t) q fun u => q * u := by
  refine ⟨hcov.1, fun s u hs hsu => ?_⟩
  simp only [rescaleFamily]
  rw [hcov.2 _ _ (div_nonneg hs ht.le) (div_le_div_of_nonneg_right hsu ht.le), mul_div_assoc,
    mul_div_assoc]

/-- A relabelling of rescaled families is one of the families. -/
theorem relabel_of_rescale {q : ℝ} {μ μ' : ℝ → ℝ → Measure (Rd d)} {t : ℝ} (ht : 0 < t)
    {g : ℝ → ℝ} (hg : IsInGaugeGroup q g)
    (hrel : ∀ s u : ℝ, 0 ≤ s → s ≤ u →
      rescaleFamily μ' t s u = rescaleFamily μ t (extendByZero g s) (extendByZero g u)) :
    ∃ g' : ℝ → ℝ, IsInGaugeGroup q g' ∧
      ∀ s u : ℝ, 0 ≤ s → s ≤ u → μ' s u = μ (extendByZero g' s) (extendByZero g' u) := by
  set g' : ℝ → ℝ := fun u => g (t * u) / t with hg'
  have hext : ∀ s : ℝ, extendByZero g (t * s) / t = extendByZero g' s := fun s => by
    by_cases hs : s = 0
    · simp [extendByZero, hs]
    · rw [extendByZero, if_neg (mul_ne_zero ht.ne' hs), extendByZero, if_neg hs]
  refine ⟨g', ⟨fun u hu v hv huv => ?_, fun u hu => ?_, fun y hy => ?_, ?_, fun u hu => ?_⟩,
    fun s u hs hsu => ?_⟩
  · exact div_lt_div_of_pos_right (hg.strictMonoOn (mul_pos ht hu) (mul_pos ht hv)
      (mul_lt_mul_of_pos_left huv ht)) ht
  · exact div_pos (hg.mapsTo (mem_Ioi.2 (mul_pos ht hu))) ht
  · obtain ⟨s, hs, hgs⟩ := hg.surjOn (mem_Ioi.2 (mul_pos ht hy))
    refine ⟨s / t, div_pos hs ht, ?_⟩
    simp only [hg']
    rw [mul_div_cancel₀ _ ht.ne', hgs, mul_div_cancel_left₀ _ ht.ne']
  · exact (hg.continuousOn.comp (continuous_const.mul continuous_id).continuousOn
      fun u hu => mem_Ioi.2 (mul_pos ht hu)).div_const t
  · simp only [hg']
    rw [mul_left_comm, hg.equivariant _ (mul_pos ht hu), mul_div_assoc]
  · have h := hrel (t * s) (t * u) (mul_nonneg ht.le hs) (mul_le_mul_of_nonneg_left hsu ht.le)
    simp only [rescaleFamily, mul_div_cancel_left₀ _ ht.ne', hext] at h
    exact h

theorem extendByZero_id (s : ℝ) : extendByZero id s = s := by
  by_cases hs : s = 0 <;> simp [extendByZero, hs]

theorem isInGaugeGroup_id (q : ℝ) : IsInGaugeGroup q id :=
  ⟨strictMonoOn_id, fun _ h => h, fun y hy => ⟨y, hy, rfl⟩, continuousOn_id, fun _ _ => rfl⟩

/-- **`thm:selection-stratum-two`(1), the freedom.** The isotropic `q`-covariant families in the
canonical discrete gauge with the ladder `(L_{√τ q^k})_k` through `t` are not unique, and two of
them are not relabellings of each other by any element of `𝒢_q`. -/
theorem selection_stratum_two_1_free (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) {t τ : ℝ} (ht : 0 < t)
    (hτ : 0 < τ) :
    ∃ μ₁ μ₂ : ℝ → ℝ → Measure (Rd d),
      (IsIsotropicFamily μ₁ ∧ IsCovariantAt μ₁ q (fun u => q * u) ∧
        ∀ k : ℤ, μ₁ (q ^ k * t) (q ^ (k + 1) * t) = maternStep d (Real.sqrt τ * q ^ k)) ∧
      (IsIsotropicFamily μ₂ ∧ IsCovariantAt μ₂ q (fun u => q * u) ∧
        ∀ k : ℤ, μ₂ (q ^ k * t) (q ^ (k + 1) * t) = maternStep d (Real.sqrt τ * q ^ k)) ∧
      (∃ s u : ℝ, 0 ≤ s ∧ s ≤ u ∧ μ₁ s u ≠ μ₂ s u) ∧
      ¬ ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧ ∀ s u : ℝ, 0 ≤ s → s ≤ u →
        μ₁ s u = μ₂ (extendByZero g s) (extendByZero g u) := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  set ρ := maternStep d (Real.sqrt τ) with hρ
  haveI : IsProbabilityMeasure ρ := (charFun_maternStep (d := d) (Real.sqrt τ) 0).1
  set D := stepData hd hτ with hD
  set κ := stepKappa d τ with hκ
  have hκm : Measurable κ := measurable_stepKappa hd τ
  set νa := radialMeasure d ((Iic (1 : ℝ)).indicator κ) with hνa
  set νb := radialMeasure d ((Iic (1 : ℝ))ᶜ.indicator κ) with hνb
  have hsum : D.ν = νa + νb := by
    rw [hD, stepData_ν, hνa, hνb, radialMeasure_add (hκm.indicator measurableSet_Iic),
      indicator_self_add_compl]
  -- lower bounds of the profile
  have hκlow : ∀ {r y : ℝ}, 0 < r → r ≤ y →
      ENNReal.ofReal (besselProfile d (y / Real.sqrt τ)) ≤ κ r :=
    fun {r y} hr hry => ENNReal.ofReal_le_ofReal (stepProfile_antitoneOn hd τ (mem_Ioi.2 hr)
      (mem_Ioi.2 (hr.trans_le hry)) hry)
  have hpos : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal (besselProfile d (y / Real.sqrt τ)) ≠ 0 :=
    fun y hy => (ENNReal.ofReal_pos.2 (besselProfile_pos hd (div_nonneg hy hs0.le))).ne'
  have hna : νa ≠ 0 := by
    refine radialMeasure_ne_zero hd (hκm.indicator measurableSet_Iic)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) (hpos 1 zero_le_one) fun r hr => ?_
    have hr0 : 0 < r := by linarith [hr.1]
    rw [indicator_of_mem (mem_Iic.2 hr.2.le)]
    calc ENNReal.ofReal (besselProfile d (1 / Real.sqrt τ)) ≤ κ r * 1 := by
          rw [mul_one]; exact hκlow hr0 hr.2.le
      _ ≤ κ r * ENNReal.ofReal r⁻¹ := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_inv₀ hr0 |>.2 hr.2.le)
  have hnb : νb ≠ 0 := by
    refine radialMeasure_ne_zero hd (hκm.indicator measurableSet_Iic.compl) one_pos
      (by norm_num : (1 : ℝ) < 2) (c := ENNReal.ofReal (besselProfile d (2 / Real.sqrt τ)) *
        ENNReal.ofReal (1 / 2)) (mul_ne_zero (hpos 2 zero_le_two) (by norm_num)) fun r hr => ?_
    have hr0 : 0 < r := by linarith [hr.1]
    rw [indicator_of_mem (show r ∈ (Iic (1 : ℝ))ᶜ from
      fun h => absurd (mem_Iic.1 h) (not_le.2 hr.1))]
    gcongr
    · exact hκlow hr0 hr.2.le
    · rw [one_div]
      exact (inv_le_inv₀ (by norm_num) hr0).2 hr.2.le
  have hR : ∀ R : Rd d ≃ₗᵢ[ℝ] Rd d, (ladderNuStar q D.ν).map R = ladderNuStar q D.ν ∧
      νa.map R = νa ∧ νb.map R = νb := fun R => by
    refine ⟨?_, radialMeasure_map_isometry _ R, radialMeasure_map_isometry _ R⟩
    rw [hD, stepData_ν, ladderNuStar_radial hd hq hκm, radialMeasure_map_isometry]
  have hneg : ∀ ν : Measure (Rd d), ν.map (LinearIsometryEquiv.neg ℝ (E := Rd d)) = ν →
      ν.map (fun x => -x) = ν := fun ν h => by rwa [coe_neg_isometry] at h
  obtain ⟨μU, μS, hladU, hladS, hnot, hiso⟩ := ladder_knot_kernel_2_split_rot hd hq ρ D
    (isSymData_step hd hτ) (lintegral_posLog_step hd hτ) νa νb hsum hna hnb
    (hneg _ (hR _).2.1) (hneg _ (hR _).2.2) _ _ (measurable_norm measurableSet_Iic.compl)
    (disjoint_compl_right.preimage _ |>.mono_right (by simp))
    (radialMeasure_indicator_compl measurableSet_Iic κ)
    (radialMeasure_indicator_compl measurableSet_Iic.compl κ)
  obtain ⟨hisoU, hisoS⟩ := hiso ⟨_, stepData_A hd hτ⟩ hR
  -- the two families, rescaled by `t`
  have hfam : ∀ μ : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ → IsRotationInvariantLaws μ →
      IsIsotropicFamily (rescaleFamily μ t) ∧ IsCovariantAt (rescaleFamily μ t) q (fun u => q * u) ∧
        ∀ k : ℤ, rescaleFamily μ t (q ^ k * t) (q ^ (k + 1) * t) =
          maternStep d (Real.sqrt τ * q ^ k) := by
    intro μ hlad hrot
    refine ⟨isIsotropicFamily_rescale ⟨⟨hlad.1.1, hlad.1.2.1⟩, hrot⟩ ht,
      isCovariantAt_rescale hlad.2.1 t ht, fun k => ?_⟩
    have h := step_zpow_of_cov hq hlad.2.1 k 1 q zero_le_one hq.le
    rw [mul_one, ← zpow_add_one₀ hq0.ne'] at h
    simp only [rescaleFamily, mul_div_cancel_right₀ _ ht.ne']
    rw [h, hlad.2.2, hρ, maternStep_map_smul, mul_comm]
  have hnot' : ¬ ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧ ∀ s u : ℝ, 0 ≤ s → s ≤ u →
      rescaleFamily μS t s u =
        rescaleFamily μU t (extendByZero g s) (extendByZero g u) := by
    rintro ⟨g, hg, hrel⟩
    exact hnot (relabel_of_rescale ht hg hrel)
  refine ⟨rescaleFamily μS t, rescaleFamily μU t, hfam μS hladS hisoS, hfam μU hladU hisoU,
    ?_, hnot'⟩
  by_contra hall
  push Not at hall
  exact hnot' ⟨id, isInGaugeGroup_id q, fun s u hs hsu => by
    rw [extendByZero_id, extendByZero_id]; exact hall s u hs hsu⟩

end Pyramids
