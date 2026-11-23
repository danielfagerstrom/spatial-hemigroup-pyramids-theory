/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.LadderBound
import Pyramids.LineAppendix.PhaseEntropySelection
import Pyramids.LineAppendix.HaarSmearing
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# `thm:phase-entropy-modulated-selection`: the tools

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:phase-entropy-modulated-selection`. Wave 3f:
the lemmas the node's assembly (`Pyramids.LineAppendix.ModulatedSelection`) reads. Nothing here
is a node's declaration.

* **The measure `ρ̃_k`** (`exists_kRho`): for `k ≥ 0` nonincreasing on `(0,∞)` with `k(∞) = 0`
  (`tendsto_profile_atTop`, from `∫ (1 ∧ x²) k(x) dx/x < ∞`), a σ-finite measure on `(0,∞)` with
  `ρ̃_k([x,∞)) = ℓ k(x)` off a countable set of `x`. It is the image under `exp` of the Stieltjes
  measure of the right-continuous version of `u ↦ -ℓ k(e^u)`.
* **Densities** carried through maps (`map_withDensity_comp`), slabs (`slab_withDensity_snd`),
  orbit mixtures (`orbitMixture_withDensity`) and dilations (`map_mul_withDensity_Ioi`).
* **The modulated cylinder measure** `σ_ρ(dθ, dr) = p([rθ]) η(dθ) ρ(dr)` (`modCyl`), its
  disintegration by `π_r = (p ∘ rot_r) η` (`modFibre`), whose rotated fibres are `p η`
  (`rotatedFibre_modFibre`), and the converse: a cylinder measure whose rotated fibres are `p η`
  almost everywhere is `σ_ρ̃` (`eq_modCyl_of_rotatedFibre`). Its image under `(θ, r) ↦ rθ` is
  `p([v])` times the Haar smearing of `ρ` (`map_modCyl`).
* **The data of the knot exponent** (`knot_data`): with no Gaussian part, `Ψ_1` has the data
  `(0, ϖ_1)` with `T_q ϖ_1 = μ + ϖ_1`, and then `ϖ_1 = ∑_{m ≥ 1} T_{q^{-m}} μ`
  (`eq_knotLevyMeasure_of_map`, chapter 3's uniqueness read through the symmetric lift).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair)
open scoped ENNReal NNReal Topology

/-! ## The profile vanishes at infinity -/

/-- **`k(∞) = 0`** for `k ≥ 0` nonincreasing on `(0,∞)` with `∫ (1 ∧ x²) k(x) dx/x < ∞`. -/
theorem tendsto_profile_atTop {k : ℝ → ℝ} (hk0 : ∀ x : ℝ, 0 < x → 0 ≤ k x)
    (hkanti : AntitoneOn k (Ioi 0))
    (hkint : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * k x / x) ≠ ⊤) :
    Tendsto k atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra H
  push Not at H
  have hge : ∀ x : ℝ, 0 < x → ε ≤ k x := by
    intro x hx
    obtain ⟨n, hn, hkn⟩ := H x
    have hn0 : 0 < n := lt_of_lt_of_le hx hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hk0 n hn0)] at hkn
    exact hkn.trans (hkanti hx hn0 hn)
  apply hkint
  refine ENNReal.eq_top_of_forall_nnreal_le fun C => ?_
  set r : ℝ := Real.exp (C / ε + 1) with hr
  have hr1 : 1 < r := by rw [hr]; exact Real.one_lt_exp_iff.2 (by positivity)
  have hr0 : 0 < r := by linarith
  have hlow : ENNReal.ofReal ε * ENNReal.ofReal (1 / 2 + Real.log r) ≤
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * k x / x) := by
    have h := lintegral_min_one_sq_div hr0
    rw [if_neg (not_le.2 hr1)] at h
    rw [← h, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (lintegral_mono_set Ioc_subset_Ioi_self).trans' (setLIntegral_mono'
      measurableSet_Ioc fun x hx => ?_)
    rw [← ENNReal.ofReal_mul hε.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx0 : 0 < x := hx.1
    have hm : 0 ≤ min 1 (x ^ 2) / x := div_nonneg (le_min zero_le_one (sq_nonneg x)) hx0.le
    calc ε * (min 1 (x ^ 2) / x) ≤ k x * (min 1 (x ^ 2) / x) :=
          mul_le_mul_of_nonneg_right (hge x hx0) hm
      _ = min 1 (x ^ 2) * k x / x := by ring
  refine le_trans ?_ hlow
  rw [← ENNReal.ofReal_mul hε.le, hr, Real.log_exp, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (C : ℝ) = ε * (C / ε) := by field_simp
  nlinarith [NNReal.coe_nonneg C]

/-! ## The measure `ρ̃_k` -/

/-- **The measure `ρ̃_k`**: for `k` nonincreasing on `(0,∞)` with `k(∞) = 0`, a s-finite measure on
`(0,∞)`, finite on every `[x,∞)`, with `ρ̃_k([x,∞)) = ℓ k(x)` for all `x > 0` off a countable
set. -/
theorem exists_kRho {q : ℝ} (hq : 1 < q) {k : ℝ → ℝ} (hkanti : AntitoneOn k (Ioi 0))
    (hklim : Tendsto k atTop (𝓝 0)) :
    ∃ ρ : Measure ℝ, SFinite ρ ∧ ρ (Iic 0) = 0 ∧ (∀ x : ℝ, 0 < x → ρ (Ici x) ≠ ⊤) ∧
      ∃ C : Set ℝ, C.Countable ∧ ∀ x : ℝ, 0 < x → x ∉ C →
        ρ (Ici x) = ENNReal.ofReal (Real.log q * k x) := by
  have hl : 0 < Real.log q := Real.log_pos hq
  set G : ℝ → ℝ := fun u => -(Real.log q * k (Real.exp u)) with hG
  have hGm : Monotone G := by
    intro u u' huu'
    simp only [hG, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left (hkanti (Real.exp_pos u) (Real.exp_pos u')
      (Real.exp_le_exp.2 huu')) hl.le
  set F : StieltjesFunction ℝ := hGm.stieltjesFunction with hF
  have hGlim : Tendsto G atTop (𝓝 0) := by
    have h := ((hklim.comp Real.tendsto_exp_atTop).const_mul (Real.log q)).neg
    simpa [hG, Function.comp_def] using h
  have hFlim : Tendsto F atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hGlim
      (hGlim.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)) (fun u => ?_) (fun u => ?_)
    · exact hGm.le_rightLim le_rfl
    · exact hGm.rightLim_le (by simp)
  have hpre : ∀ x : ℝ, 0 < x → Real.exp ⁻¹' Ici x = Ici (Real.log x) := by
    intro x hx
    ext u
    simp only [mem_preimage, mem_Ici]
    rw [Real.log_le_iff_le_exp hx]
  have hIci : ∀ x : ℝ, 0 < x →
      F.measure.map Real.exp (Ici x) = ENNReal.ofReal (0 - Function.leftLim F (Real.log x)) := by
    intro x hx
    rw [Measure.map_apply Real.measurable_exp measurableSet_Ici, hpre x hx, F.measure_Ici hFlim]
  refine ⟨F.measure.map Real.exp, inferInstance, ?_, fun x hx => ?_, ?_⟩
  · rw [Measure.map_apply Real.measurable_exp measurableSet_Iic]
    have : Real.exp ⁻¹' Iic 0 = ∅ := by
      ext u
      simp [(Real.exp_pos u).not_ge]
    rw [this, measure_empty]
  · rw [hIci x hx]
    exact ENNReal.ofReal_ne_top
  · refine ⟨Real.exp '' ({u | Function.leftLim F u ≠ F u} ∪ {u | ¬ ContinuousAt G u}),
      (F.countable_leftLim_ne.union hGm.countable_not_continuousAt).image _,
      fun x hx hxC => ?_⟩
    have hnot : Real.log x ∉ {u | Function.leftLim F u ≠ F u} ∪ {u | ¬ ContinuousAt G u} := by
      intro h
      exact hxC ⟨_, h, Real.exp_log hx⟩
    simp only [mem_union, mem_setOf_eq, not_or, not_not] at hnot
    rw [hIci x hx, hnot.1]
    have hc : Function.rightLim G (Real.log x) = G (Real.log x) :=
      (hGm.continuousWithinAt_Ioi_iff_rightLim_eq).1 hnot.2.continuousWithinAt
    change ENNReal.ofReal (0 - Function.rightLim G (Real.log x)) = _
    rw [hc, hG]
    simp only [Real.exp_log hx, zero_sub, neg_neg]

/-! ## Densities -/

/-- **A density composed with a map is pushed forward with it**:
`T_*((g ∘ T) μ) = g (T_* μ)`. -/
theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {T : α → β} (hT : Measurable T) {g : β → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity (g ∘ T)).map T = (μ.map T).withDensity g := by
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hT]
  rfl

/-- The slabs of `g(v) Λ(dy, dv)` are `g` times those of `Λ`. -/
theorem slab_withDensity_snd (Λ : Measure (ℝ × ℝ)) {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    (s t : ℝ) : slab (Λ.withDensity fun x => g x.2) s t = (slab Λ s t).withDensity g := by
  rw [slab, slab, restrict_withDensity (measurableSet_Ioc.prod MeasurableSet.univ)]
  exact map_withDensity_comp _ measurable_snd hg

/-- **The orbits of `g(rθ) σ`**: if `g(rθqⁿ) = g(rθ)`, the mixture is `g(v) Λ_σ(dy, dv)`. -/
theorem orbitMixture_withDensity (q : ℝ) (σ : Measure (ℝ × ℝ)) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) (hinv : ∀ᵐ x ∂σ, ∀ n : ℤ, g (x.2 * x.1 * q ^ n) = g (x.2 * x.1)) :
    orbitMixture q (σ.withDensity fun x => g (x.2 * x.1)) =
      (orbitMixture q σ).withDensity fun x => g x.2 := by
  ext s hs
  rw [orbitMixture_apply q _ hs, withDensity_apply _ hs, orbitMixture_eq_sum,
    Measure.restrict_sum _ hs, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [withDensity_apply _ (measurable_orbitPt q n hs),
    Measure.restrict_map (measurable_orbitPt q n) hs,
    lintegral_map (f := fun a : ℝ × ℝ => g a.2) (hg.comp measurable_snd)
      (measurable_orbitPt q n)]
  refine setLIntegral_congr_fun_ae (measurable_orbitPt q n hs) ?_
  filter_upwards [hinv] with x hx _
  exact (hx n).symm

/-- **The dilation of a density on `(0,∞)`**: `(v ↦ cv)_*(f dv) = c⁻¹ f(u/c) du`. -/
theorem map_mul_withDensity_Ioi {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ((volume.restrict (Ioi 0)).withDensity f).map (fun v => c * v) =
      (volume.restrict (Ioi 0)).withDensity fun u => ENNReal.ofReal c⁻¹ * f (c⁻¹ * u) := by
  have hT : Measurable fun v : ℝ => c * v := measurable_const_mul c
  have e : f = (fun u => f (c⁻¹ * u)) ∘ fun v => c * v := by
    funext v
    simp [inv_mul_cancel_left₀ hc.ne']
  have hmap : (volume.restrict (Ioi (0 : ℝ))).map (fun v => c * v) =
      ENNReal.ofReal c⁻¹ • volume.restrict (Ioi 0) := by
    ext s hs
    have hpre : (fun v : ℝ => c * v) ⁻¹' s ∩ Ioi 0 = (fun v : ℝ => c * v) ⁻¹' (s ∩ Ioi 0) := by
      ext v
      simp only [mem_inter_iff, mem_preimage, mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, mul_pos hc h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, pos_of_mul_pos_right h2 hc.le⟩
    rw [Measure.map_apply hT hs, Measure.restrict_apply (hT hs), hpre,
      Real.volume_preimage_mul_left hc.ne', Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hs, abs_of_pos (inv_pos.2 hc)]
  have e' : (volume.restrict (Ioi (0 : ℝ))).withDensity f =
      (volume.restrict (Ioi 0)).withDensity ((fun u => f (c⁻¹ * u)) ∘ fun v => c * v) :=
    congrArg _ e
  rw [e', map_withDensity_comp _ hT (g := fun u => f (c⁻¹ * u))
      (hf.comp (measurable_const_mul _)), hmap,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  rfl

/-! ## `[·]` and the lifted density -/

/-- `[qⁿy] = [y]` for `y > 0`. -/
theorem qClass_zpow_mul {q : ℝ} (hq : 1 < q) {y : ℝ} (hy : 0 < y) (n : ℤ) :
    qClass q (q ^ n * y) = qClass q y := by
  have hq0 : 0 < q := by linarith
  have hm : qClass q y ∈ Ico 1 q := octave_mem hq hy
  have e : q ^ n * y = q ^ (n + dgLevel q y) * qClass q y := by
    rw [qClass, ← mul_assoc, ← zpow_add₀ hq0.ne']
    congr 1
    ring_nf
  rw [e]
  exact qClass_eq_of_mem hq hm _

/-- **`p̄(v) = p([v])`**, as a density. -/
noncomputable def liftDensity (q : ℝ) (p : ℝ → ℝ) (v : ℝ) : ℝ≥0∞ := ENNReal.ofReal (p (qClass q v))

theorem measurable_liftDensity (q : ℝ) {p : ℝ → ℝ} (hpm : Measurable p) :
    Measurable (liftDensity q p) :=
  (hpm.comp (measurable_qClass q)).ennreal_ofReal

theorem liftDensity_zpow_mul {q : ℝ} (hq : 1 < q) (p : ℝ → ℝ) {y : ℝ} (hy : 0 < y) (n : ℤ) :
    liftDensity q p (y * q ^ n) = liftDensity q p y := by
  rw [liftDensity, liftDensity, mul_comm, qClass_zpow_mul hq hy]

/-- `ofReal(p([v]) X/v) = p̄(v) ofReal(X/v)` for `X ≥ 0`, `v > 0`. -/
theorem ofReal_lift_mul (q : ℝ) (p : ℝ → ℝ) {v X : ℝ} (hv : 0 < v) (hX : 0 ≤ X) :
    ENNReal.ofReal (p (qClass q v) * X / v) = liftDensity q p v * ENNReal.ofReal (X / v) := by
  rw [mul_div_assoc, ENNReal.ofReal_mul' (div_nonneg hX hv.le)]
  rfl

/-- **`p̄ > 0` for `dy/(ℓy)`-almost every `y`** when `p > 0` `η`-almost everywhere. -/
theorem ae_logHaar_liftDensity_pos {q : ℝ} (hq : 1 < q) {p : ℝ → ℝ} (hpm : Measurable p)
    (hppos : ∀ᵐ θ ∂(haarPhase q), 0 < p θ) : ∀ᵐ v ∂(logHaar q), 0 < p (qClass q v) := by
  set S : Set ℝ := {v | p (qClass q v) ≤ 0} with hS
  have hSm : MeasurableSet S := measurableSet_le (hpm.comp (measurable_qClass q)) measurable_const
  rw [ae_iff]
  simp only [not_lt]
  change logHaar q S = 0
  rw [← lintegral_indicator_one hSm,
    ← lintegral_haarPhase_tsum_zpow hq (measurable_one.indicator hSm)]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hppos, ae_haarPhase_mem q] with θ hθ hθm
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  have e : qClass q (θ * q ^ n) = θ := by rw [mul_comm]; exact qClass_eq_of_mem hq hθm n
  rw [indicator_of_notMem]
  simp only [hS, mem_setOf_eq, e, not_le]
  exact hθ

/-- **`p ∘ rot_r > 0` `η`-almost everywhere**, for `r > 0`. -/
theorem ae_haarPhase_lift_pos {q : ℝ} (hq : 1 < q) {p : ℝ → ℝ}
    (hppos : ∀ᵐ θ ∂(haarPhase q), 0 < p θ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ θ ∂(haarPhase q), 0 < p (qClass q (r * θ)) := by
  have h : ∀ᵐ θ ∂((haarPhase q).map (qRot q r)), 0 < p θ := by
    rw [map_qRot_haarPhase hq hr]
    exact hppos
  exact ae_of_ae_map (measurable_qRot q r).aemeasurable h

/-! ## The modulated cylinder measure -/

/-- **`σ_ρ(dθ, dr) = p([rθ]) η(dθ) ρ(dr)`**. -/
noncomputable def modCyl (q : ℝ) (p : ℝ → ℝ) (ρ : Measure ℝ) : Measure (ℝ × ℝ) :=
  ((haarPhase q).prod ρ).withDensity fun x => liftDensity q p (x.2 * x.1)

open Classical in
/-- **`π_r = (p ∘ rot_r) η`** for `r > 0`, and `η` otherwise. -/
noncomputable def modFibre (q : ℝ) (p : ℝ → ℝ) (r : ℝ) : Measure ℝ :=
  if 0 < r then (haarPhase q).withDensity (fun θ => liftDensity q p (r * θ)) else haarPhase q

theorem measurable_liftDensity_mul (q : ℝ) {p : ℝ → ℝ} (hpm : Measurable p) :
    Measurable fun x : ℝ × ℝ => liftDensity q p (x.2 * x.1) :=
  (measurable_liftDensity q hpm).comp (measurable_snd.mul measurable_fst)

/-- **The rotated fibres of `π` are `p η`**: `(rot_r)_*((p ∘ rot_r) η) = p η`, `r > 0`. -/
theorem rotatedFibre_modFibre {q : ℝ} (hq : 1 < q) {p : ℝ → ℝ} (hpm : Measurable p) {r : ℝ}
    (hr : 0 < r) :
    rotatedFibre q (modFibre q p) r = (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ) := by
  rw [rotatedFibre, modFibre, if_pos hr]
  have e : (fun θ => liftDensity q p (r * θ)) = (fun θ => ENNReal.ofReal (p θ)) ∘ qRot q r := rfl
  rw [e, map_withDensity_comp _ (measurable_qRot q r) hpm.ennreal_ofReal, map_qRot_haarPhase hq hr]

theorem modFibre_compl (q : ℝ) (p : ℝ → ℝ) (r : ℝ) : modFibre q p r (Ico 1 q)ᶜ = 0 := by
  unfold modFibre
  split_ifs
  · exact withDensity_absolutelyContinuous _ _ (haarPhase_compl_Ico q)
  · exact haarPhase_compl_Ico q

theorem isProbabilityMeasure_modFibre {q : ℝ} (hq : 1 < q) {p : ℝ → ℝ} (hpm : Measurable p)
    (hp1 : IsProbabilityMeasure ((haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)))
    (r : ℝ) : IsProbabilityMeasure (modFibre q p r) := by
  by_cases hr : 0 < r
  · have h := congrArg (fun μ : Measure ℝ => μ univ) (rotatedFibre_modFibre hq hpm hr)
    simp only [rotatedFibre, Measure.map_apply (measurable_qRot q r) MeasurableSet.univ,
      preimage_univ] at h
    exact ⟨h.trans measure_univ⟩
  · rw [modFibre, if_neg hr]
    exact isProbabilityMeasure_haarPhase hq

theorem measurable_modFibre (q : ℝ) {p : ℝ → ℝ} (hpm : Measurable p) :
    Measurable (modFibre q p) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have h1 : Measurable fun r => ∫⁻ θ, liftDensity q p (r * θ) ∂((haarPhase q).restrict s) :=
    ((measurable_liftDensity q hpm).comp
      (measurable_fst.mul measurable_snd)).lintegral_prod_right'
  have e : (fun r => modFibre q p r s) = fun r => if 0 < r then
      ∫⁻ θ, liftDensity q p (r * θ) ∂((haarPhase q).restrict s) else haarPhase q s := by
    funext r
    unfold modFibre
    split_ifs
    · rw [withDensity_apply _ hs]
    · rfl
  rw [e]
  exact Measurable.ite measurableSet_Ioi h1 measurable_const

/-- **The disintegration formula** `σ_ρ(E) = ∫ π_r(E_r) ρ(dr)`. -/
theorem modCyl_apply {q : ℝ} {p : ℝ → ℝ} (hpm : Measurable p) (ρ : Measure ℝ) [SFinite ρ]
    (hρ0 : ρ (Iic 0) = 0) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    modCyl q p ρ E = ∫⁻ r, modFibre q p r ((fun θ => (θ, r)) ⁻¹' E) ∂ρ := by
  rw [modCyl, withDensity_apply _ hE, ← lintegral_indicator hE,
    lintegral_prod_symm _ ((measurable_liftDensity_mul q hpm).indicator hE).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_of_Iic_zero hρ0] with r hr
  rw [modFibre, if_pos hr, withDensity_apply _ (measurable_prodMk_right hE),
    ← lintegral_indicator (measurable_prodMk_right hE)]
  rfl

/-- The `r`-marginal of `σ_ρ` is `ρ`. -/
theorem rMarginal_modCyl {q : ℝ} (hq : 1 < q) {p : ℝ → ℝ} (hpm : Measurable p)
    (hp1 : IsProbabilityMeasure ((haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)))
    (ρ : Measure ℝ) [SFinite ρ] (hρ0 : ρ (Iic 0) = 0) : rMarginal q (modCyl q p ρ) = ρ := by
  ext A hA
  rw [rMarginal, Measure.map_apply measurable_snd hA,
    Measure.restrict_apply (measurable_snd hA)]
  have e : Prod.snd ⁻¹' A ∩ Ico 1 q ×ˢ univ = Ico 1 q ×ˢ A := by
    ext x
    simp [and_comm]
  rw [e, modCyl_apply hpm ρ hρ0 (measurableSet_Ico.prod hA), ← lintegral_indicator_one hA]
  refine lintegral_congr fun r => ?_
  haveI := isProbabilityMeasure_modFibre hq hpm hp1 r
  by_cases hr : r ∈ A
  · have e2 : (fun θ => (θ, r)) ⁻¹' (Ico 1 q ×ˢ A) = Ico 1 q := by
      ext θ
      simp [hr]
    rw [e2, indicator_of_mem hr, Pi.one_apply,
      (prob_compl_eq_zero_iff measurableSet_Ico).1 (modFibre_compl q p r)]
  · have e2 : (fun θ => (θ, r)) ⁻¹' (Ico 1 q ×ˢ A) = ∅ := by
      ext θ
      simp [hr]
    rw [e2, indicator_of_notMem hr, measure_empty]

/-- **`π` disintegrates `σ_ρ`.** -/
theorem isPhaseDisintegration_modCyl {q : ℝ} (hq : 1 < q) {p : ℝ → ℝ} (hpm : Measurable p)
    (hp1 : IsProbabilityMeasure ((haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)))
    (ρ : Measure ℝ) [SFinite ρ] (hρ0 : ρ (Iic 0) = 0) :
    IsPhaseDisintegration q (modCyl q p ρ) (modFibre q p) where
  measurable := measurable_modFibre q hpm
  isProbability := isProbabilityMeasure_modFibre hq hpm hp1
  carried := modFibre_compl q p
  disintegrates := fun E hE => by
    rw [rMarginal_modCyl hq hpm hp1 ρ hρ0, modCyl_apply hpm ρ hρ0 hE]

/-- **The image of `σ_ρ` under `(θ, r) ↦ rθ`** is `p([v])` times the Haar smearing of `ρ`. -/
theorem map_modCyl (q : ℝ) {p : ℝ → ℝ} (hpm : Measurable p) (ρ : Measure ℝ) :
    (modCyl q p ρ).map (fun x => x.2 * x.1) =
      (((haarPhase q).prod ρ).map fun x => x.2 * x.1).withDensity (liftDensity q p) :=
  map_withDensity_comp (g := liftDensity q p) (T := fun x : ℝ × ℝ => x.2 * x.1) _
    (measurable_snd.mul measurable_fst) (measurable_liftDensity q hpm)

/-- **A cylinder measure whose rotated fibres are `p η` is `σ_ρ̃`.** -/
theorem eq_modCyl_of_rotatedFibre {q : ℝ} (hq : 1 < q) {p : ℝ → ℝ} (hpm : Measurable p)
    {σ : Measure (ℝ × ℝ)} {π : ℝ → Measure ℝ} (hπ : IsPhaseDisintegration q σ π)
    [SFinite (rMarginal q σ)] (hρ0 : rMarginal q σ (Iic 0) = 0)
    (h : ∀ᵐ r ∂(rMarginal q σ),
      rotatedFibre q π r = (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)) :
    σ = modCyl q p (rMarginal q σ) := by
  have hfib : ∀ᵐ r ∂(rMarginal q σ), π r = modFibre q p r := by
    filter_upwards [h, ae_pos_of_Iic_zero hρ0] with r hr hr0
    have hr' : 0 < r⁻¹ := inv_pos.2 hr0
    have h1 : π r = (rotatedFibre q π r).map (qRot q r⁻¹) := by
      rw [rotatedFibre, Measure.map_map (measurable_qRot q r⁻¹) (measurable_qRot q r)]
      conv_lhs => rw [← Measure.map_id (μ := π r)]
      refine Measure.map_congr ?_
      have hae : ∀ᵐ θ ∂(π r), θ ∈ Ico 1 q := by
        rw [ae_iff]
        exact hπ.carried r
      filter_upwards [hae] with θ hθ
      exact (qRot_inv_qRot hq hr0 hθ).symm
    have h2 : ((haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)).map (qRot q r⁻¹) =
        (haarPhase q).withDensity (fun θ => liftDensity q p (r * θ)) := by
      have e : (haarPhase q).withDensity (fun θ => ENNReal.ofReal (p θ)) =
          (haarPhase q).withDensity ((fun θ => liftDensity q p (r * θ)) ∘ qRot q r⁻¹) := by
        refine withDensity_congr_ae ?_
        filter_upwards [ae_haarPhase_mem q] with θ hθ
        have h3 := qRot_inv_qRot hq hr' hθ
        rw [inv_inv] at h3
        change ENNReal.ofReal (p θ) = ENNReal.ofReal (p (qRot q r (qRot q r⁻¹ θ)))
        rw [h3]
      rw [e, map_withDensity_comp (g := fun θ => liftDensity q p (r * θ)) _
        (measurable_qRot q r⁻¹) ((measurable_liftDensity q hpm).comp (measurable_const_mul r)),
        map_qRot_haarPhase hq hr']
    rw [h1, hr, h2, modFibre, if_pos hr0]
  ext E hE
  rw [hπ.disintegrates E hE, modCyl_apply hpm _ hρ0 hE]
  exact lintegral_congr_ae (hfib.mono fun r hr => by simp only [hr])

/-- `η ⊗ ρ` is carried by the cylinder when `ρ` is carried by `(0,∞)`. -/
theorem prod_cylinder_compl (q : ℝ) {ρ : Measure ℝ} [SFinite ρ] (hρ0 : ρ (Iic 0) = 0) :
    ((haarPhase q).prod ρ) (cylinder q)ᶜ = 0 := by
  have hsub : (cylinder q)ᶜ ⊆ (Ico 1 q)ᶜ ×ˢ univ ∪ univ ×ˢ (Ioi 0)ᶜ := by
    intro x hx
    simp only [cylinder, mem_compl_iff, mem_prod, not_and_or] at hx
    rcases hx with hx | hx
    · exact Or.inl ⟨hx, mem_univ _⟩
    · exact Or.inr ⟨mem_univ _, hx⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, haarPhase_compl_Ico, zero_mul]
  · rw [Measure.prod_prod, compl_Ioi, hρ0, mul_zero]

theorem modCyl_cylinder_compl (q : ℝ) (p : ℝ → ℝ) {ρ : Measure ℝ} [SFinite ρ]
    (hρ0 : ρ (Iic 0) = 0) :
    modCyl q p ρ (cylinder q)ᶜ = 0 :=
  withDensity_absolutelyContinuous _ _ (prod_cylinder_compl q hρ0)

/-- **`η ⊗ ρ ≪ σ_ρ`** when `p > 0` `η`-almost everywhere. -/
theorem prod_ac_modCyl {q : ℝ} (hq : 1 < q) {p : ℝ → ℝ} (hpm : Measurable p)
    (hppos : ∀ᵐ θ ∂(haarPhase q), 0 < p θ) (ρ : Measure ℝ) [SFinite ρ] (hρ0 : ρ (Iic 0) = 0) :
    (haarPhase q).prod ρ ≪ modCyl q p ρ := by
  refine withDensity_absolutelyContinuous' (measurable_liftDensity_mul q hpm).aemeasurable ?_
  rw [ae_iff]
  have hS : MeasurableSet {x : ℝ × ℝ | ¬ liftDensity q p (x.2 * x.1) ≠ 0} :=
    ((measurable_liftDensity_mul q hpm) (measurableSet_singleton 0)).compl.compl
  rw [Measure.prod_apply_symm hS]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [ae_pos_of_Iic_zero hρ0] with r hr
  have h := ae_haarPhase_lift_pos hq hppos hr
  rw [ae_iff] at h
  refine measure_mono_null (fun θ hθ => ?_) h
  simp only [mem_preimage, mem_setOf_eq, not_not, liftDensity, ENNReal.ofReal_eq_zero] at hθ ⊢
  exact not_lt.2 hθ

/-! ## The data of the knot exponent -/

/-- **`Ψ_1` has the data `(0, ϖ_1)` with `T_q ϖ_1 = μ + ϖ_1`** on a ladder with no Gaussian part. -/
theorem knot_data {q : ℝ} (hq : 1 < q) {Ψ1 : ℝ → ℝ} (hΨ1 : IsKnotExponent q Ψ1)
    (hnoG : HasNoGaussianStep q Ψ1) {m : Measure ℝ} (hm : IsStepMeasure q Ψ1 m)
    {P1 : SymLevyPair} (hP1 : HasExpData Ψ1 P1) :
    P1.a = 0 ∧ P1.ν.map (fun v => q * v) = m + P1.ν := by
  have hq0 : 0 < q := by linarith
  obtain ⟨Q2, hQ2a, hQ2ν, hQ2⟩ := line_exponent_data_2 Ψ1 P1 hP1 hq0
  have h3 := line_exponent_data_3 Ψ1 (fun ω => Ψ1 (q * ω)) P1 Q2 hP1 hQ2
  obtain ⟨ha, hν⟩ := h3.1.1 hΨ1.2.1
  obtain ⟨Q, hQa, hQν, hQ⟩ := h3.2 ha hν
  have hQ' : HasExpData (knotStep q Ψ1) Q := hQ
  obtain ⟨P, hP, hPm⟩ := hm
  obtain ⟨P', hP', hP'a⟩ := hnoG
  have hQP := line_exponent_data_1_unique _ Q P hQ' hP
  have hQP' := line_exponent_data_1_unique _ Q P' hQ' hP'
  refine ⟨?_, ?_⟩
  · have h0 : Q.a = 0 := hQP'.1.trans hP'a
    rw [hQa, hQ2a] at h0
    have h1 : (q ^ 2 - 1) * P1.a = 0 := by linarith
    have hq2 : q ^ 2 - 1 ≠ 0 := by nlinarith
    exact (mul_eq_zero.1 h1).resolve_left hq2
  · rw [← hQ2ν, ← hQν, hQP.2, hPm]

/-- `symLift ν (s) = ½(ν(e⁻¹ s) + ν((e ∘ neg)⁻¹ s))`. -/
theorem symLift_apply' (ν : Measure ℝ) {s : Set (Rd 1)} (hs : MeasurableSet s) :
    symLift ν s = (2 : ℝ≥0∞)⁻¹ * (ν (lineEmb ⁻¹' s) + ν ((fun x => lineEmb (-x)) ⁻¹' s)) := by
  rw [symLift, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply continuous_lineEmb.measurable hs, Measure.map_apply measurable_lineEmb_neg hs,
    smul_eq_mul]

/-- **`ϖ_1 = ∑_{m ≥ 1} T_{q^{-m}} μ`** for a pair `(a, ϖ_1)` with `T_q ϖ_1 = μ + ϖ_1`
(chapter 3's `eq_ladderNuStar_of_map`, read through the symmetric lift). -/
theorem eq_knotLevyMeasure_of_map {q : ℝ} (hq : 1 < q) (P : SymLevyPair) {m : Measure ℝ}
    (hmf : ScaleSpace.IsFolded m) (h : P.ν.map (fun v => q * v) = m + P.ν) :
    P.ν = knotLevyMeasure q m := by
  have hq0 : 0 < q := by linarith
  have hfold : P.ν (Iic 0) = 0 := P.ν_folded
  refine eq_of_symLift_eq P.ν_folded (knotLevyMeasure_folded hq0 hmf) ?_
  rw [← ladderNuStar_symLift]
  refine eq_ladderNuStar_of_map hq ?_ (fun ε hε => ?_) ?_
  · rw [symLift_apply' _ (measurableSet_singleton 0)]
    have h1 : P.ν (lineEmb ⁻¹' {0}) = 0 := by
      refine measure_mono_null (fun x hx => ?_) hfold
      have h0 : ‖lineEmb x‖ = 0 := by
        rw [mem_preimage, mem_singleton_iff] at hx
        rw [hx, norm_zero]
      rw [norm_lineEmb, abs_eq_zero] at h0
      exact h0.le
    have h2 : P.ν ((fun x => lineEmb (-x)) ⁻¹' {0}) = 0 := by
      refine measure_mono_null (fun x hx => ?_) hfold
      have h0 : ‖lineEmb (-x)‖ = 0 := by
        rw [mem_preimage, mem_singleton_iff] at hx
        rw [hx, norm_zero]
      rw [norm_lineEmb, abs_eq_zero, neg_eq_zero] at h0
      exact h0.le
    rw [h1, h2, add_zero, mul_zero]
  · have hT : P.ν (Iic 0 ∪ Ioi ε) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨by rw [hfold]; exact ENNReal.zero_ne_top,
        SymLevyPair_measure_Ioi_ne_top P hε⟩) (measure_union_le _ _)
    rw [symLift_apply' _ (measurableSet_lt measurable_const measurable_norm)]
    refine ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)
    · refine ne_top_of_le_ne_top hT (measure_mono fun x hx => ?_)
      simp only [mem_preimage, mem_setOf_eq, norm_lineEmb] at hx
      rcases le_or_gt x 0 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by rwa [abs_of_pos h0] at hx)
    · refine ne_top_of_le_ne_top hT (measure_mono fun x hx => ?_)
      simp only [mem_preimage, mem_setOf_eq, norm_lineEmb, abs_neg] at hx
      rcases le_or_gt x 0 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by rwa [abs_of_pos h0] at hx)
  · rw [← symLift_map_mul, h, symLift_add]

end Pyramids

