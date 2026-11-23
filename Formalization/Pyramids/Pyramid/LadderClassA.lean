/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.LadderStratum
import Pyramids.Cited.A35

/-!
# `prop:ladder-knot-kernel`(4)(b): when `F ∈ 𝒜_d`

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:ladder-knot-kernel`. Wave 3a:
`ladder_knot_kernel_4b_classA` moved here from `PyramidsSkeleton.Ch03Pyramid`, unchanged in name.
Its proof does not use the hypotheses `ϱ ≠ δ₀`, the rotation invariance of `ϱ` (the polar form of
`ν_ϱ` gives it), `k ≥ 0` and that `ϱ` is a probability measure, which were dropped (2026-11-14, a
strengthening).

## The route

* **Radial measures.** `κ(|x|)(|S^{d-1}| |x|^d)^{-1} dx` with a profile `κ` in `[0,∞]`
  (`radialMeasure`). Its image under `x ↦ cx` has the profile `κ(·/c)` (`map_smul_radialMeasure`),
  so `ν* = ∑_m D_{q^{-m-1}} ν_ϱ` has the profile `k* = ∑_m k(q^{m+1} ·)`
  (`ladderNuStar_radial`). Its image under `x ↦ |x|` is `κ(r) dr/r` (`radialMeasure_map_norm`,
  polar coordinates), so the profile is determined up to a null set (`radialMeasure_ae_eq`),
  and a profile changed on a null set gives the same measure (`radialMeasure_congr`).
* **`F` is the knot exponent.** By the uniqueness in the equation, `F(r) = Ψ*(re)`, and `Ψ*` is
  radial, `D*` having the data `(cI, ν*)` with `ν*` rotation invariant. So `F(|·|) = Ψ*`.
* **(⇒)** By A35, `F(|·|)` is the exponent of an origin datum `(a_0, k_d)`. The uniqueness of the
  data (A39) gives `ν_d = ν*`, so `k* = k_d` almost everywhere, and `k_d` is nonincreasing.
* **(⇐)** For `k* = k̃` a.e. with `k̃` nonincreasing: `∫ (1 ∧ r²) k̃(r) dr/r = ∫ (1 ∧ |x|²) dν* < ∞`
  makes `k̃` finite on `(0,∞)` (a nonincreasing profile infinite at `r₀` is infinite on `(0,r₀)`)
  and gives the integrability conditions. So `(a/(q² - 1), k̃)` is an origin datum with the Lévy
  measure `ν*`; its exponent is `Ψ* = F(|·|)`, and A35 gives `F ∈ 𝒜_d`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## Radial measures -/

/-- **The radial measure** `κ(|x|) (|S^{d-1}| |x|^d)^{-1} dx` on `ℝ^d ∖ {0}`, `κ` in `[0,∞]`. -/
noncomputable def radialMeasure (d : ℕ) (κ : ℝ → ℝ≥0∞) : Measure (Rd d) :=
  volume.withDensity fun x => ({0}ᶜ : Set (Rd d)).indicator
    (fun x => κ ‖x‖ * ENNReal.ofReal (sphereArea d * ‖x‖ ^ d)⁻¹) x

theorem measurable_radialDensity {κ : ℝ → ℝ≥0∞} (hκ : Measurable κ) :
    Measurable fun x : Rd d => ({0}ᶜ : Set (Rd d)).indicator
      (fun x => κ ‖x‖ * ENNReal.ofReal (sphereArea d * ‖x‖ ^ d)⁻¹) x :=
  ((hκ.comp measurable_norm).mul (by fun_prop)).indicator (measurableSet_singleton 0).compl

theorem polarLevyMeasure_eq_radial (hd : 1 ≤ d) (k : ℝ → ℝ) :
    polarLevyMeasure d k = radialMeasure d (fun r => ENNReal.ofReal (k r)) := by
  have hS := (sphereArea_eq_toSphere (d := d) hd).2
  unfold polarLevyMeasure radialMeasure
  congr 1
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · have hx' : x ∈ ({0}ᶜ : Set (Rd d)) := hx
    rw [indicator_of_mem hx', indicator_of_mem hx', div_eq_mul_inv,
      ENNReal.ofReal_mul' (inv_nonneg.2 (by positivity))]

theorem originDatum_levyMeasure_eq_radial (hd : 1 ≤ d) (D : OriginDatum d) :
    D.levyMeasure = radialMeasure d (fun r => ENNReal.ofReal ((Ioi (0 : ℝ)).indicator D.k r)) := by
  rw [show D.levyMeasure = polarLevyMeasure d D.k from rfl, polarLevyMeasure_eq_radial hd]
  unfold radialMeasure
  congr 1
  funext x
  by_cases hx : x = 0
  · simp [hx]
  · have hx' : x ∈ ({0}ᶜ : Set (Rd d)) := hx
    rw [indicator_of_mem hx', indicator_of_mem hx']
    beta_reduce
    rw [indicator_of_mem (show ‖x‖ ∈ Ioi (0 : ℝ) from norm_pos_iff.2 hx)]

/-- **A density invariant under an isometry** gives an invariant measure. -/
theorem withDensity_map_isometry {f : Rd d → ℝ≥0∞} (Q : Rd d ≃ₗᵢ[ℝ] Rd d)
    (hf : ∀ x, f (Q x) = f x) : ((volume : Measure (Rd d)).withDensity f).map Q =
      (volume : Measure (Rd d)).withDensity f := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply Q.continuous.measurable hB,
    withDensity_apply _ (Q.continuous.measurable hB),
    withDensity_apply _ hB, ← lintegral_indicator (Q.continuous.measurable hB),
    ← lintegral_indicator hB]
  have h := (Q.measurePreserving).lintegral_comp_emb Q.toHomeomorph.measurableEmbedding
    (B.indicator f)
  rw [← h]
  refine lintegral_congr fun x => ?_
  by_cases hx : Q x ∈ B
  · rw [indicator_of_mem (show x ∈ Q ⁻¹' B from hx), indicator_of_mem hx]
    exact (hf x).symm
  · rw [indicator_of_notMem (show x ∉ Q ⁻¹' B from hx), indicator_of_notMem hx]

theorem radialMeasure_map_isometry (κ : ℝ → ℝ≥0∞) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) :
    (radialMeasure d κ).map Q = radialMeasure d κ := by
  unfold radialMeasure
  refine withDensity_map_isometry Q fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  · have h1 : Q x ∈ ({0}ᶜ : Set (Rd d)) := by simpa using hx
    have h2 : x ∈ ({0}ᶜ : Set (Rd d)) := hx
    rw [indicator_of_mem h1, indicator_of_mem h2, LinearIsometryEquiv.norm_map]

/-- **The dilate** of a radial measure: `D_c` turns the profile `κ` into `κ(·/c)`. -/
theorem map_smul_radialMeasure (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) {κ : ℝ → ℝ≥0∞}
    (hκ : Measurable κ) :
    (radialMeasure d κ).map (fun x => c • x) = radialMeasure d (fun r => κ (r / c)) := by
  have hS := (sphereArea_eq_toSphere (d := d) hd).2
  have hκ' : Measurable fun r => κ (r / c) := hκ.comp (measurable_id.div_const c)
  refine Measure.ext fun B hB => ?_
  have hpre : MeasurableSet ((fun x : Rd d => c • x) ⁻¹' B) := measurable_const_smul c hB
  rw [Measure.map_apply (measurable_const_smul c) hB, radialMeasure, radialMeasure,
    withDensity_apply _ hpre, withDensity_apply _ hB, ← lintegral_indicator hpre,
    ← lintegral_indicator hB]
  set dens : Rd d → ℝ≥0∞ := fun x => ({0}ᶜ : Set (Rd d)).indicator
    (fun x => κ ‖x‖ * ENNReal.ofReal (sphereArea d * ‖x‖ ^ d)⁻¹) x with hdens
  set G : Rd d → ℝ≥0∞ := B.indicator fun y => dens (c⁻¹ • y) with hG
  have hGm : Measurable G :=
    ((measurable_radialDensity hκ).comp (measurable_const_smul c⁻¹)).indicator hB
  have h1 : ∀ x, ((fun x : Rd d => c • x) ⁻¹' B).indicator dens x = G (c • x) := by
    intro x
    have hcx : c⁻¹ • c • x = x := by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    by_cases hx : c • x ∈ B
    · rw [indicator_of_mem (show x ∈ (fun x : Rd d => c • x) ⁻¹' B from hx), hG,
        indicator_of_mem hx, hcx]
    · rw [indicator_of_notMem (show x ∉ (fun x : Rd d => c • x) ⁻¹' B from hx), hG,
        indicator_of_notMem hx]
  refine (lintegral_congr h1).trans ?_
  rw [← lintegral_map hGm (measurable_const_smul c), Measure.map_addHaar_smul volume hc.ne',
    lintegral_smul_measure, finrank_Rd, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ B
  · rw [hG, indicator_of_mem hy, indicator_of_mem hy]
    by_cases hy0 : y = 0
    · simp [hdens, hy0]
    · have hy0' : y ∈ ({0}ᶜ : Set (Rd d)) := hy0
      have hcy : c⁻¹ • y ∈ ({0}ᶜ : Set (Rd d)) := by
        simp [hy0, hc.ne']
      have hn : ‖c⁻¹ • y‖ = ‖y‖ / c := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le), inv_mul_eq_div]
      have hy1 : 0 < ‖y‖ := norm_pos_iff.2 hy0
      rw [hdens]
      beta_reduce
      rw [indicator_of_mem hcy, indicator_of_mem hy0', hn, mul_left_comm,
        ← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 2
      rw [abs_of_pos (inv_pos.2 (pow_pos hc d)), div_pow]
      field_simp
  · rw [hG, indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]

/-- **The profile of `ν*`**: for a radial `ν`, `ν*` has the profile `k* = ∑_m κ(q^{m+1} ·)`. -/
theorem ladderNuStar_radial (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) {κ : ℝ → ℝ≥0∞}
    (hκ : Measurable κ) :
    ladderNuStar q (radialMeasure d κ) =
      radialMeasure d (fun r => ∑' m : ℕ, κ (q ^ (m + 1) * r)) := by
  have hq0 : 0 < q := by linarith
  have hmap : ∀ m : ℕ, (radialMeasure d κ).map (fun x => (q ^ (-((m : ℤ) + 1))) • x) =
      radialMeasure d (fun r => κ (q ^ (m + 1) * r)) := by
    intro m
    rw [map_smul_radialMeasure hd (zpow_pos hq0 _) hκ, zpow_neg_succ]
    congr 1
    funext r
    rw [div_inv_eq_mul, mul_comm]
  rw [ladderNuStar]
  simp_rw [hmap]
  unfold radialMeasure
  beta_reduce
  rw [← withDensity_tsum (f := fun (m : ℕ) (x : Rd d) => ({0}ᶜ : Set (Rd d)).indicator
    (fun x => κ (q ^ (m + 1) * ‖x‖) * ENNReal.ofReal (sphereArea d * ‖x‖ ^ d)⁻¹) x)
    fun m => measurable_radialDensity (hκ.comp (measurable_const_mul (q ^ (m + 1))))]
  congr 1
  funext x
  rw [ENNReal.tsum_apply]
  by_cases hx : x = 0
  · simp [hx]
  · have hx' : x ∈ ({0}ᶜ : Set (Rd d)) := hx
    simp only [indicator_of_mem hx']
    rw [ENNReal.tsum_mul_right]

/-- **Polar coordinates**: the image of a radial measure under `x ↦ |x|` is `κ(r) dr/r`. -/
theorem radialMeasure_map_norm (hd : 1 ≤ d) {κ : ℝ → ℝ≥0∞} (hκ : Measurable κ) :
    (radialMeasure d κ).map (fun x => ‖x‖) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun r => κ r * ENNReal.ofReal r⁻¹ := by
  obtain ⟨hσ, hS⟩ := sphereArea_eq_toSphere (d := d) hd
  refine Measure.ext fun E hE => ?_
  have hpre : MeasurableSet ((fun x : Rd d => ‖x‖) ⁻¹' E) := measurable_norm hE
  rw [Measure.map_apply measurable_norm hE, radialMeasure, withDensity_apply _ hpre,
    ← lintegral_indicator hpre, withDensity_apply _ hE, Measure.restrict_restrict hE,
    lintegral_polar hd _ ((measurable_radialDensity hκ).indicator hpre)]
  have hinner : ∀ η : Metric.sphere (0 : Rd d) 1, ∫⁻ r in Ioi (0 : ℝ),
      ((fun x : Rd d => ‖x‖) ⁻¹' E).indicator (fun x => ({0}ᶜ : Set (Rd d)).indicator
        (fun x => κ ‖x‖ * ENNReal.ofReal (sphereArea d * ‖x‖ ^ d)⁻¹) x) (r • (η : Rd d)) *
          ENNReal.ofReal (r ^ (d - 1)) =
      ENNReal.ofReal (sphereArea d)⁻¹ * ∫⁻ r in E ∩ Ioi 0, κ r * ENNReal.ofReal r⁻¹ := by
    intro η
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator (hE.inter measurableSet_Ioi), ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun r => ?_
    by_cases hr : r ∈ Ioi (0 : ℝ)
    · have hr0 : 0 < r := hr
      have hn : ‖r • (η : Rd d)‖ = r := by
        rw [norm_smul, norm_eq_of_mem_sphere η, mul_one, Real.norm_of_nonneg hr0.le]
      have hne : r • (η : Rd d) ∈ ({0}ᶜ : Set (Rd d)) := by
        intro h0
        have : ‖r • (η : Rd d)‖ = 0 := by rw [mem_singleton_iff.1 h0, norm_zero]
        rw [hn] at this
        exact hr0.ne' this
      rw [indicator_of_mem hr]
      by_cases hrE : r ∈ E
      · rw [indicator_of_mem (show r • (η : Rd d) ∈ (fun x : Rd d => ‖x‖) ⁻¹' E by
            simp only [mem_preimage, hn]; exact hrE),
          indicator_of_mem (show r ∈ E ∩ Ioi 0 from ⟨hrE, hr⟩), indicator_of_mem hne, hn,
          mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (by positivity)), mul_left_comm,
          ← ENNReal.ofReal_mul (inv_nonneg.2 hS.le)]
        congr 2
        obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]
        field_simp
      · rw [indicator_of_notMem (show r • (η : Rd d) ∉ (fun x : Rd d => ‖x‖) ⁻¹' E by
            simp only [mem_preimage, hn]; exact hrE),
          indicator_of_notMem (fun h => hrE h.1), zero_mul]
    · rw [indicator_of_notMem hr, indicator_of_notMem (fun h => hr h.2)]
  simp_rw [hinner]
  rw [lintegral_const, ← hσ, mul_comm, ← mul_assoc, ← ENNReal.ofReal_mul hS.le,
    mul_inv_cancel₀ hS.ne', ENNReal.ofReal_one, one_mul]

/-- The radial measure determines its profile up to a null set. -/
theorem radialMeasure_ae_eq (hd : 1 ≤ d) {κ κ' : ℝ → ℝ≥0∞} (hκ : Measurable κ)
    (hκ' : Measurable κ') (h : radialMeasure d κ = radialMeasure d κ') :
    κ =ᵐ[volume.restrict (Ioi (0 : ℝ))] κ' := by
  have h2 := congrArg (fun m : Measure (Rd d) => m.map fun x => ‖x‖) h
  simp only [radialMeasure_map_norm hd hκ, radialMeasure_map_norm hd hκ'] at h2
  have h3 := (withDensity_eq_iff_of_sigmaFinite (by fun_prop) (by fun_prop)).1 h2
  filter_upwards [h3, ae_restrict_mem measurableSet_Ioi] with r hr hr0
  have hr0' : 0 < r := hr0
  exact (ENNReal.mul_left_inj (by simpa using hr0') ENNReal.ofReal_ne_top).1 hr

/-- A profile changed on a null set gives the same radial measure. -/
theorem radialMeasure_congr (hd : 1 ≤ d) {κ κ' : ℝ → ℝ≥0∞}
    (h : κ =ᵐ[volume.restrict (Ioi (0 : ℝ))] κ') : radialMeasure d κ = radialMeasure d κ' := by
  have hN : volume ({r | κ r ≠ κ' r} ∩ Ioi 0) = 0 := by
    have h' : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), κ r = κ' r := h
    rw [ae_iff, Measure.restrict_apply' measurableSet_Ioi] at h'
    exact h'
  obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null hN
  -- the preimage of `T` under the norm is null
  have hpre : volume ((fun x : Rd d => ‖x‖) ⁻¹' T) = 0 := by
    have hm : MeasurableSet ((fun x : Rd d => ‖x‖) ⁻¹' T) := measurable_norm hTm
    rw [← lintegral_indicator_one hm, lintegral_polar hd _ (measurable_one.indicator hm)]
    refine (lintegral_congr fun η => ?_).trans lintegral_zero
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    have hT : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∉ T :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hT0)
    filter_upwards [hT, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    have hn : ‖r • (η : Rd d)‖ = r := by
      rw [norm_smul, norm_eq_of_mem_sphere η, mul_one, Real.norm_of_nonneg (le_of_lt hr0)]
    rw [indicator_of_notMem (show r • (η : Rd d) ∉ (fun x : Rd d => ‖x‖) ⁻¹' T by
      simp only [mem_preimage, hn]; exact hr), zero_mul]
  unfold radialMeasure
  refine withDensity_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hpre] with x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hx0' : x ∈ ({0}ᶜ : Set (Rd d)) := hx0
    rw [indicator_of_mem hx0', indicator_of_mem hx0']
    have hκx : κ ‖x‖ = κ' ‖x‖ := by
      by_contra hne
      exact hx (hTsub ⟨hne, norm_pos_iff.2 hx0⟩)
    rw [hκx]

/-! ## Origin data as symmetric data -/

/-- **The symmetric data `(a/2 · I, ν_d)`** of an origin datum. -/
noncomputable def originSymData (hd : 1 ≤ d) (D : OriginDatum d) : SymLevyData d where
  A := (D.a / 2) • (1 : Mat d)
  ν := D.levyMeasure
  A_posSemidef := Matrix.PosSemidef.one.smul (by have := D.a_nonneg; positivity)
  ν_zero := D.levyMeasure_zero
  ν_integrable := D.lintegral_min_levyMeasure_ne_top hd
  ν_symm := by
    have h := D.levyMeasure_map_isometry (LinearIsometryEquiv.neg ℝ)
    rwa [coe_neg_isometry] at h

theorem originSymData_exponent (hd : 1 ≤ d) (D : OriginDatum d) (ξ : Rd d) :
    (originSymData hd D).exponent ξ = D.exponent ξ := by
  have hint : Integrable (fun x : Rd d => 1 - Real.cos ⟪ξ, x⟫) D.levyMeasure :=
    (originSymData hd D).integrable_one_sub_cos ξ
  have hnn : 0 ≤ ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂D.levyMeasure :=
    integral_nonneg fun x => sub_nonneg.2 (Real.cos_le_one _)
  have ha := D.a_nonneg
  rw [OriginDatum.exponent, OriginDatum.exponentL,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => sub_nonneg.2
      (Real.cos_le_one _)), ← ENNReal.ofReal_add (by positivity) hnn,
    ENNReal.toReal_ofReal (by positivity)]
  change quad ((D.a / 2) • (1 : Mat d)) ξ + ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂D.levyMeasure = _
  rw [quad_smul, quad_one]
  ring

/-! ## `prop:ladder-knot-kernel`(4)(b), the class -/

/-- **`prop:ladder-knot-kernel`(4)(b), the class.** For `F` the solution of the equation:
`F ∈ 𝒜_d` iff `k*(r) = ∑_{m ≥ 1} k_ϱ(q^m r)` agrees for almost every `r > 0` with a nonincreasing
function. -/
theorem ladder_knot_kernel_4b_classA (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    {a : ℝ} (ha : 0 ≤ a) (k : ℝ → ℝ) (hkm : Measurable k)
    (hlevy : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂polarLevyMeasure d k ≠ ⊤)
    (htrans : ∀ ω : Rd d, charFun ρ ω = ((Real.exp (-(a / 2 * ‖ω‖ ^ 2 +
      ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂polarLevyMeasure d k)) : ℝ) : ℂ))
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂polarLevyMeasure d k < ⊤)
    (e : Rd d) (he : ‖e‖ = 1) (F : ℝ → ℝ) (hFc : ContinuousOn F (Ici 0)) (hF0 : F 0 = 0)
    (hFeq : ∀ r : ℝ, 0 ≤ r → F (q * r) - F r = radialExponent ρ e r) :
    classA d F ↔ ∃ kt : ℝ → ℝ≥0∞, AntitoneOn kt (Ioi 0) ∧
      knotProfile q k =ᵐ[volume.restrict (Ioi (0 : ℝ))] kt := by
  have hq0 : 0 < q := by linarith
  have hq21 : 0 < q ^ 2 - 1 := by nlinarith
  set Dρ : SymLevyData d := polarData ha k hlevy with hDρ
  have hD : IsSymData ρ Dρ := isSymData_polar ha k hlevy htrans
  set Dst := ladderStarData hq Dρ hmom with hDst
  have hκm : Measurable fun r => ENNReal.ofReal (k r) := hkm.ennreal_ofReal
  have hpm : Measurable (knotProfile q k) := by
    have h : knotProfile q k = fun r =>
        ⨆ s : Finset ℕ, ∑ m ∈ s, ENNReal.ofReal (k (q ^ (m + 1) * r)) := by
      funext r
      exact ENNReal.tsum_eq_iSup_sum
    rw [h]
    exact .iSup fun s => s.measurable_fun_sum fun m _ =>
      (hkm.comp (measurable_const_mul _)).ennreal_ofReal
  -- `ν* = ν_{k*}`
  have hνst : Dst.ν = radialMeasure d (knotProfile q k) := by
    change ladderNuStar q (polarLevyMeasure d k) = _
    rw [polarLevyMeasure_eq_radial hd, ladderNuStar_radial hd hq hκm]
    rfl
  -- `Ψ*` is radial
  have hstA : Dst.A = ((q ^ 2 - 1)⁻¹ * (a / 2)) • (1 : Mat d) := by
    change (q ^ 2 - 1)⁻¹ • ((a / 2) • (1 : Mat d)) = _
    rw [smul_smul]
  have hrad : ∀ ξ : Rd d, Dst.exponent ξ = Dst.exponent (‖ξ‖ • e) := by
    intro ξ
    have hn : ‖‖ξ‖ • e‖ = ‖ξ‖ := by rw [norm_smul, he, mul_one, norm_norm]
    set R := Submodule.reflection (ℝ ∙ (‖ξ‖ • e - ξ) : Submodule ℝ (Rd d))ᗮ with hR
    have hRξ : R (‖ξ‖ • e) = ξ := Submodule.reflection_sub hn
    conv_lhs => rw [← hRξ]
    exact Dst.exponent_isometry hstA R (by rw [hνst]; exact radialMeasure_map_isometry _ R) _
  -- `F(r) = Ψ*(re)`
  have hnn : ∀ r : ℝ, 0 ≤ radialExponent ρ e r := fun r => by
    rw [radialExponent_eq hD]
    exact Dρ.exponent_nonneg _
  have hG : ∀ r : ℝ, (fun r : ℝ => Dst.exponent (r • e)) (q * r) -
      (fun r : ℝ => Dst.exponent (r • e)) r = radialExponent ρ e r := by
    intro r
    simp only
    rw [mul_smul, ladderStarData_exponent_smul hq Dρ hmom, radialExponent_eq hD]
    ring
  have hF : ∀ r : ℝ, 0 ≤ r → F r = Dst.exponent (r • e) := fun r hr =>
    (hasSum_step_Ici hq hFc hF0 hFeq (fun r _ => hnn r) hr).unique
      (hasSum_step_Ici hq (Dst.continuous_exponent.comp (continuous_id.smul
        continuous_const)).continuousOn (by simp [SymLevyData.exponent_zero])
        (fun r _ => hG r) (fun r _ => hnn r) hr)
  have hFξ : ∀ ξ : Rd d, F ‖ξ‖ = Dst.exponent ξ := fun ξ => by
    rw [hF _ (norm_nonneg ξ), ← hrad]
  have hFnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r := fun r hr => by
    rw [hF r hr]
    exact Dst.exponent_nonneg _
  rw [cited_A35_classA hd F hFnn]
  constructor
  · -- (⇒)
    rintro ⟨D, hDF⟩
    have hdata := (SymLevyData.eq_of_exponent (E := originSymData hd D) (E' := Dst) fun ξ => by
      rw [originSymData_exponent hd D, ← hDF, hFξ]).2
    change D.levyMeasure = Dst.ν at hdata
    rw [hνst, originDatum_levyMeasure_eq_radial hd D] at hdata
    have hkD : Measurable fun r => ENNReal.ofReal ((Ioi (0 : ℝ)).indicator D.k r) :=
      (measurable_indicator_Ioi_of_antitoneOn D.k_antitone).ennreal_ofReal
    refine ⟨fun r => ENNReal.ofReal (D.k r), fun r hr s hs hrs =>
      ENNReal.ofReal_le_ofReal (D.k_antitone hr hs hrs), ?_⟩
    filter_upwards [(radialMeasure_ae_eq hd hkD hpm hdata).symm,
      ae_restrict_mem measurableSet_Ioi] with r hr hr0
    rw [hr, indicator_of_mem hr0]
  · -- (⇐)
    rintro ⟨kt, hanti, hkt⟩
    have hνkt : Dst.ν = radialMeasure d kt := hνst.trans (radialMeasure_congr hd hkt)
    -- the integrability against `dr/r`
    have hint : ∫⁻ r in Ioi (0 : ℝ), kt r * ENNReal.ofReal r⁻¹ * ENNReal.ofReal (min (r ^ 2) 1)
        ≠ ⊤ := by
      have h1 := Dst.ν_integrable
      have h2 : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂radialMeasure d (knotProfile q k) =
          ∫⁻ r, ENNReal.ofReal (min (r ^ 2) 1) ∂((radialMeasure d (knotProfile q k)).map
            fun x => ‖x‖) :=
        (lintegral_map (f := fun r : ℝ => ENNReal.ofReal (min (r ^ 2) 1)) (by fun_prop)
          measurable_norm).symm
      rw [hνst, h2, radialMeasure_map_norm hd hpm,
        lintegral_withDensity_eq_lintegral_mul _ (hpm.mul (by fun_prop)) (by fun_prop)] at h1
      refine ne_top_of_le_ne_top h1 (le_of_eq (lintegral_congr_ae ?_))
      filter_upwards [hkt] with r hr
      simp only [Pi.mul_apply]
      rw [hr]
    -- `k̃` is finite on `(0,∞)`
    have hfin : ∀ r : ℝ, 0 < r → kt r ≠ ⊤ := by
      intro r0 hr0 htop
      apply hint
      set r1 := min r0 1 with hr1
      have hr1pos : 0 < r1 := lt_min hr0 one_pos
      have hpos : ∀ r ∈ Ioo (0 : ℝ) r1,
          kt r * ENNReal.ofReal r⁻¹ * ENNReal.ofReal (min (r ^ 2) 1) = ⊤ := by
        intro r hr
        have hkr : kt r = ⊤ := by
          have h3 := hanti (mem_Ioi.2 hr.1) (mem_Ioi.2 hr0) (hr.2.le.trans (min_le_left _ _))
          rw [htop] at h3
          exact top_le_iff.1 h3
        rw [hkr, ENNReal.top_mul (ENNReal.ofReal_pos.2 (inv_pos.2 hr.1)).ne',
          ENNReal.top_mul (ENNReal.ofReal_pos.2 (lt_min (pow_pos hr.1 2) one_pos)).ne']
      have heq : ∫⁻ r in Ioo (0 : ℝ) r1,
          kt r * ENNReal.ofReal r⁻¹ * ENNReal.ofReal (min (r ^ 2) 1) = ⊤ := by
        rw [setLIntegral_congr_fun measurableSet_Ioo hpos, setLIntegral_const, Real.volume_Ioo,
          ENNReal.top_mul (ENNReal.ofReal_pos.2 (by linarith)).ne']
      exact eq_top_iff.2 (heq ▸ lintegral_mono_set Ioo_subset_Ioi_self)
    -- the origin datum
    set kr : ℝ → ℝ := fun r => (kt r).toReal with hkr
    have hkr_ofReal : ∀ r : ℝ, 0 < r → ENNReal.ofReal (kr r) = kt r := fun r hr =>
      ENNReal.ofReal_toReal (hfin r hr)
    have hnear : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (kr r * r) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hint ?_
      calc ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (kr r * r)
          = ∫⁻ r in Ioo (0 : ℝ) 1,
              kt r * ENNReal.ofReal r⁻¹ * ENNReal.ofReal (min (r ^ 2) 1) := by
            refine setLIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
            have hr0 : 0 < r := hr.1
            rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, hkr_ofReal r hr0,
              min_eq_left (by nlinarith [hr.1, hr.2]), mul_assoc,
              ← ENNReal.ofReal_mul (inv_nonneg.2 hr0.le)]
            congr 2
            field_simp
        _ ≤ _ := lintegral_mono_set Ioo_subset_Ioi_self
    have hfar : ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (kr r / r) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hint ?_
      calc ∫⁻ r in Ioi (1 : ℝ), ENNReal.ofReal (kr r / r)
          = ∫⁻ r in Ioi (1 : ℝ),
              kt r * ENNReal.ofReal r⁻¹ * ENNReal.ofReal (min (r ^ 2) 1) := by
            refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 1 < r) => ?_
            have hr0 : 0 < r := by linarith
            rw [div_eq_mul_inv, ENNReal.ofReal_mul ENNReal.toReal_nonneg, hkr_ofReal r hr0,
              min_eq_right (by nlinarith), ENNReal.ofReal_one, mul_one]
        _ ≤ _ := lintegral_mono_set (Ioi_subset_Ioi zero_le_one)
    set D' : OriginDatum d := ⟨a / (q ^ 2 - 1), kr, by positivity,
      fun r _ => ENNReal.toReal_nonneg, fun r hr s hs hrs =>
        ENNReal.toReal_mono (hfin r hr) (hanti hr hs hrs), hnear, hfar⟩ with hD'
    refine ⟨D', fun ξ => ?_⟩
    have hν' : D'.levyMeasure = Dst.ν := by
      rw [hνkt, originDatum_levyMeasure_eq_radial hd D']
      unfold radialMeasure
      congr 1
      funext x
      by_cases hx : x = 0
      · simp [hx]
      · have hx' : x ∈ ({0}ᶜ : Set (Rd d)) := hx
        have hx0 : ‖x‖ ∈ Ioi (0 : ℝ) := norm_pos_iff.2 hx
        rw [indicator_of_mem hx', indicator_of_mem hx']
        beta_reduce
        rw [indicator_of_mem hx0]
        change ENNReal.ofReal (kr ‖x‖) * _ = _
        rw [hkr_ofReal _ hx0]
    rw [hFξ, ← originSymData_exponent hd D']
    simp only [SymLevyData.exponent, pairExponent]
    congr 1
    · change quad ((q ^ 2 - 1)⁻¹ • ((a / 2) • (1 : Mat d))) ξ =
        quad ((a / (q ^ 2 - 1) / 2) • (1 : Mat d)) ξ
      rw [smul_smul]
      congr 2
      field_simp
    · change ∫ x, _ ∂Dst.ν = ∫ x, _ ∂D'.levyMeasure
      rw [hν']

end Pyramids
