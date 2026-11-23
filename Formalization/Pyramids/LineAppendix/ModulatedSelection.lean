/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.ModulatedCandidate

/-!
# `thm:phase-entropy-modulated-selection`: selection with a log-periodic factor

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:phase-entropy-modulated-selection`. Wave 3f:
the declaration `phase_entropy_modulated_selection` moved here from `PyramidsSkeleton.ChA1Line`,
unchanged in name and conclusion. The tools are `Pyramids.LineAppendix.ModulatedCandidate`.

## The route

* **The candidate.** `Λ* := Λ_σ` for `σ = p([rθ]) η(dθ) ρ̃_k(dr)`. The density `p([v])` is
  invariant under `v ↦ qⁿv`, so `Λ* = p([v]) Λ_{η ⊗ ρ̃_k}` and its slabs are
  `p([v]) ℓ⁻¹ρ̃_k([v/t,∞)) dv/v = p([v]) k(v/t) dv/v` (`slab_orbitMixture_modCyl`).
* **The knot measure.** At `t = 1` the slab is `∑_{m ≥ 1} T_{q^{-m}} μ`, the densities
  telescoping because `k(∞) = 0` (`knotLevyMeasure_modulated`); with no Gaussian part `Ψ_1` has
  the data `(0, ϖ_1)` with `T_q ϖ_1 = μ + ϖ_1`, so `ϖ_1` is that sum (`knot_data`,
  `eq_knotLevyMeasure_of_map`). So the slab at `1` is a Lévy measure, which gives (i) at every
  `t`, and the family of `(Λ*, 0)` has the knot exponent `Ψ_1`.
* **(iv).** For `s < t` one orbit index `n` and one interval `I ⊆ [1,q)` have `θqⁿ ∈ (s,t]` for
  `θ ∈ I`; `η ⊗ ρ̃_k ≪ σ` (`p > 0` a.e.), `η(I) > 0` and `ρ̃_k ≠ 0`, since `ρ̃_k = 0` would make
  `μ = 0` (`orbitMixture_Ioc_pos`).
* **Its entropy.** `σ` is disintegrated by `π_r = (p ∘ rot_r) η`, whose rotated fibres are
  `p η = μ̄°`, so equality holds in `prop:phase-entropy-ladder-bound`(1).
* **Uniqueness.** At equality the rotated fibres of a member are `μ̄°` almost everywhere, so its
  cylinder measure is `σ_ρ̃` (`eq_modCyl_of_rotatedFibre`), and `μ = p([v])` times the Haar smearing
  of `ρ̃`. Two such members have the same smearing, hence the same `ρ̃`
  (`haar_smearing_injective`) and the same `Λ` (`modulated_unique`); `ℬ = 0` since the ladder
  has no Gaussian part. Conversely `ℬ = 0` with the candidate's slabs gives `Λ = Λ*`
  (`quadrant_measure_ext`), whose disintegrations agree almost everywhere.
* **The value.** `KL(p η ‖ η) = ∫ log p d(p η)`, and the fold carries `∫ log p dμ°` to
  `∫ log p([v]) μ(dv)` (`modulated_value`).
* **No similarity member.** A similarity member has `𝔈 = 0`, so the bound forces
  `KL(μ̄° ‖ η) = 0`, `μ̄° = η` and `p = 1` almost everywhere (`modulated_no_similarity`); the
  print's telescoping of the similarity step is not needed.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter ProbabilityTheory InformationTheory
open ScaleSpace (SymLevyPair profileMeasure)
open scoped ENNReal NNReal Topology

/-! ## The candidate's slabs -/

theorem withDensity_Ioi_congr {f g : ℝ → ℝ≥0∞} (h : ∀ v : ℝ, 0 < v → f v = g v) :
    (volume.restrict (Ioi (0 : ℝ))).withDensity f =
      (volume.restrict (Ioi (0 : ℝ))).withDensity g := by
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact h v hv

/-- **The slabs of `Λ_{σ_ρ}`**: `p([v]) k(v/t) dv/v`, for `ρ([x,∞)) = ℓ k(x)` off a countable
set. -/
theorem slab_orbitMixture_modCyl {q : ℝ} (hq : 1 < q) {p : ℝ → ℝ} (hpm : Measurable p)
    {k : ℝ → ℝ} (hk0 : ∀ x : ℝ, 0 < x → 0 ≤ k x) (ρ : Measure ℝ) [SFinite ρ]
    (hρ0 : ρ (Iic 0) = 0) (hfin : ∀ x : ℝ, 0 < x → ρ (Ici x) ≠ ⊤) {C : Set ℝ}
    (hC : C.Countable)
    (hρk : ∀ x : ℝ, 0 < x → x ∉ C → ρ (Ici x) = ENNReal.ofReal (Real.log q * k x)) {t : ℝ}
    (ht : 0 < t) :
    slab (orbitMixture q (modCyl q p ρ)) 0 t = (volume.restrict (Ioi 0)).withDensity
      fun v => ENNReal.ofReal (p (qClass q v) * k (v / t) / v) := by
  have hl : 0 < Real.log q := Real.log_pos hq
  have hinv : ∀ᵐ x ∂((haarPhase q).prod ρ), ∀ n : ℤ,
      liftDensity q p (x.2 * x.1 * q ^ n) = liftDensity q p (x.2 * x.1) := by
    have hc : ∀ᵐ x ∂((haarPhase q).prod ρ), x ∈ cylinder q := by
      rw [ae_iff]
      exact prod_cylinder_compl q hρ0
    filter_upwards [hc] with x hx n
    exact liftDensity_zpow_mul hq p (mul_pos hx.2 (lt_of_lt_of_le one_pos hx.1.1)) n
  have hanti : Antitone fun v => ρ (Ici (v / t)) :=
    fun a b hab => measure_mono (Ici_subset_Ici.2 (div_le_div_of_nonneg_right hab ht.le))
  have hdm : Measurable fun v => ENNReal.ofReal ((ρ (Ici (v / t))).toReal / Real.log q / v) :=
    ((hanti.measurable.ennreal_toReal.div_const _).div measurable_id).ennreal_ofReal
  rw [modCyl, orbitMixture_withDensity q _ (measurable_liftDensity q hpm) hinv,
    slab_withDensity_snd _ (measurable_liftDensity q hpm), orbitMixture_haarPhase_prod hq ρ,
    slab_logHaar_prod hq hρ0 hfin ht, profileMeasure,
    ← withDensity_mul _ hdm (measurable_liftDensity q hpm)]
  have hnull : volume ((fun x => t * x) '' C) = 0 := (hC.image _).measure_zero _
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull)] with v hv hvC
  have hv0 : (0 : ℝ) < v := hv
  have hvt0 : 0 < v / t := div_pos hv0 ht
  have hvt : v / t ∉ C := fun h => hvC ⟨v / t, h, by field_simp⟩
  rw [Pi.mul_apply, hρk _ hvt0 hvt,
    ENNReal.toReal_ofReal (mul_nonneg hl.le (hk0 _ hvt0)), mul_div_cancel_left₀ _ hl.ne',
    ofReal_lift_mul q p hv0 (hk0 _ hvt0), mul_comm]

/-- **The knot measure of the candidate telescopes**: `∑_{m ≥ 1} T_{q^{-m}} μ = p([v]) k(v) dv/v`
for `μ = p([v])(k(v/q) - k(v)) dv/v`. -/
theorem knotLevyMeasure_modulated {q : ℝ} (hq : 1 < q) {p : ℝ → ℝ} (hpm : Measurable p)
    {k : ℝ → ℝ} (hkm : Measurable k) (hk0 : ∀ x : ℝ, 0 < x → 0 ≤ k x)
    (hkanti : AntitoneOn k (Ioi 0)) (hklim : Tendsto k atTop (𝓝 0)) :
    knotLevyMeasure q ((volume.restrict (Ioi 0)).withDensity
        fun v => ENNReal.ofReal (p (qClass q v) * (k (v / q) - k v) / v)) =
      (volume.restrict (Ioi 0)).withDensity
        fun v => ENNReal.ofReal (p (qClass q v) * k (v / 1) / v) := by
  have hq0 : 0 < q := by linarith
  have hf : Measurable fun v => ENNReal.ofReal (p (qClass q v) * (k (v / q) - k v) / v) := by
    refine (((hpm.comp (measurable_qClass q)).mul ((hkm.comp (measurable_id.div_const q)).sub
      hkm)).div measurable_id).ennreal_ofReal
  set g : ℕ → ℝ → ℝ≥0∞ := fun j u =>
    ENNReal.ofReal (p (qClass q u) * (k (q ^ j * u) - k (q ^ (j + 1) * u)) / u) with hg
  have hgm : ∀ j, Measurable (g j) := fun j =>
    (((hpm.comp (measurable_qClass q)).mul ((hkm.comp (measurable_const_mul _)).sub
      (hkm.comp (measurable_const_mul _)))).div measurable_id).ennreal_ofReal
  have hterm : ∀ j : ℕ, ((volume.restrict (Ioi 0)).withDensity
      fun v => ENNReal.ofReal (p (qClass q v) * (k (v / q) - k v) / v)).map
        (fun v => q ^ (-((j : ℤ) + 1)) * v) = (volume.restrict (Ioi 0)).withDensity (g j) := by
    intro j
    have hc : 0 < q ^ (-((j : ℤ) + 1)) := zpow_pos hq0 _
    rw [map_mul_withDensity_Ioi hc hf]
    refine withDensity_Ioi_congr fun u hu => ?_
    have e : (q ^ (-((j : ℤ) + 1)))⁻¹ = q ^ (j + 1) := by
      rw [zpow_neg, inv_inv]
      norm_cast
    have hqj : 0 < q ^ (j + 1) := pow_pos hq0 _
    rw [e, ← ENNReal.ofReal_mul hqj.le]
    have hp : p (qClass q (q ^ (j + 1) * u)) = p (qClass q u) := by
      have h := qClass_zpow_mul hq hu ((j + 1 : ℕ) : ℤ)
      rw [zpow_natCast] at h
      rw [h]
    have e2 : q ^ (j + 1) * u / q = q ^ j * u := by
      rw [pow_succ]
      field_simp
    rw [hg, hp, e2]
    congr 1
    field_simp
  rw [knotLevyMeasure]
  simp_rw [hterm]
  rw [← withDensity_tsum hgm]
  refine withDensity_Ioi_congr fun u hu => ?_
  rw [div_one, ENNReal.tsum_apply]
  change ∑' j : ℕ, ENNReal.ofReal (p (qClass q u) * (k (q ^ j * u) - k (q ^ (j + 1) * u)) / u) =
    ENNReal.ofReal (p (qClass q u) * k u / u)
  have hmono : ∀ j : ℕ, k (q ^ (j + 1) * u) ≤ k (q ^ j * u) := fun j =>
    hkanti (mul_pos (pow_pos hq0 _) hu) (mul_pos (pow_pos hq0 _) hu)
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq.le (Nat.le_succ j)) hu.le)
  rcases le_or_gt (p (qClass q u)) 0 with hp | hp
  · have h0 : ∀ j : ℕ,
        ENNReal.ofReal (p (qClass q u) * (k (q ^ j * u) - k (q ^ (j + 1) * u)) / u) = 0 :=
      fun j => ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hp (sub_nonneg.2 (hmono j))) hu.le)
    simp only [h0, tsum_zero]
    exact (ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hp (hk0 u hu)) hu.le)).symm
  · set b : ℕ → ℝ := fun j => k (q ^ j * u) with hb
    have hblim : Tendsto b atTop (𝓝 0) :=
      hklim.comp ((tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const hu)
    have hnn : ∀ j : ℕ, 0 ≤ p (qClass q u) * (b j - b (j + 1)) / u := fun j =>
      div_nonneg (mul_nonneg hp.le (sub_nonneg.2 (hmono j))) hu.le
    have hsum : HasSum (fun j => p (qClass q u) * (b j - b (j + 1)) / u)
        (p (qClass q u) * k u / u) := by
      rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
      have e : ∀ N : ℕ, ∑ j ∈ Finset.range N, p (qClass q u) * (b j - b (j + 1)) / u =
          p (qClass q u) * (b 0 - b N) / u := by
        intro N
        rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_range_sub']
      simp_rw [e]
      have hb0 : b 0 = k u := by simp [hb]
      have h := ((tendsto_const_nhds (x := b 0)).sub hblim).const_mul (p (qClass q u))
      have h2 := h.div_const u
      rw [sub_zero, hb0] at h2
      rw [hb0]
      exact h2
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]

/-! ## (iv) for the candidate -/

/-- **`Λ_σ((s,t] × (0,∞)) > 0`** when `η ⊗ ρ ≪ σ` and `ρ((0,∞)) ≠ 0`. -/
theorem orbitMixture_Ioc_pos {q : ℝ} (hq : 1 < q) {σ : Measure (ℝ × ℝ)} {ρ : Measure ℝ}
    [SFinite ρ] (hac : (haarPhase q).prod ρ ≪ σ) (hρ : ρ (Ioi 0) ≠ 0) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) : 0 < orbitMixture q σ (Ioc s t ×ˢ Ioi 0) := by
  have hq0 : 0 < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos hq
  set u : ℝ := (s + t) / 2 with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  have hsu : s < u := by rw [hu]; linarith
  have hut : u < t := by rw [hu]; linarith
  set n : ℤ := dgLevel q u with hn
  have hqn : 0 < q ^ n := zpow_pos hq0 n
  set θ₀ : ℝ := q ^ (-n) * u with hθ₀
  have hθ₀m : θ₀ ∈ Ico 1 q := octave_mem hq hu0
  set b : ℝ := min q (q ^ (-n) * t) with hb
  have hθb : θ₀ < b := lt_min hθ₀m.2 (mul_lt_mul_of_pos_left hut (zpow_pos hq0 _))
  have hinv : ∀ x : ℝ, q ^ (-n) * x * q ^ n = x := by
    intro x
    rw [mul_comm, ← mul_assoc, ← zpow_add₀ hq0.ne', add_neg_cancel, zpow_zero, one_mul]
  have hsub : Ioo θ₀ b ×ˢ Ioi 0 ⊆ orbitPt q n ⁻¹' (Ioc s t ×ˢ Ioi 0) := by
    rintro ⟨θ, r⟩ ⟨⟨hθ1, hθ2⟩, hr⟩
    have hr0 : (0 : ℝ) < r := hr
    have hθ0 : 0 < θ := lt_trans (lt_of_lt_of_le one_pos hθ₀m.1) hθ1
    change (s < θ * q ^ n ∧ θ * q ^ n ≤ t) ∧ 0 < r * θ * q ^ n
    refine ⟨⟨?_, ?_⟩, by positivity⟩
    · have h1 : θ₀ * q ^ n < θ * q ^ n := mul_lt_mul_of_pos_right hθ1 hqn
      rw [hθ₀, hinv] at h1
      linarith
    · have h1 : θ * q ^ n < q ^ (-n) * t * q ^ n :=
        mul_lt_mul_of_pos_right (lt_of_lt_of_le hθ2 (min_le_right _ _)) hqn
      rw [hinv] at h1
      exact h1.le
  have hηI : haarPhase q (Ioo θ₀ b) ≠ 0 := by
    have hac' : volume.restrict (Ico 1 q) ≪ haarPhase q := by
      refine withDensity_absolutelyContinuous' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ico] with θ hθ
      exact (ENNReal.ofReal_pos.2 (one_div_pos.2
        (mul_pos hl (lt_of_lt_of_le one_pos hθ.1)))).ne'
    intro h0
    have h := hac' h0
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.2 (show Ioo θ₀ b ⊆ Ico 1 q from fun x hx =>
        ⟨hθ₀m.1.trans hx.1.le, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩),
      Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h
    linarith
  rw [pos_iff_ne_zero, orbitMixture_apply q σ (measurableSet_Ioc.prod measurableSet_Ioi)]
  intro h0
  have h3 : σ (Ioo θ₀ b ×ˢ Ioi 0) = 0 := measure_mono_null hsub (ENNReal.tsum_eq_zero.1 h0 n)
  have h4 := hac h3
  rw [Measure.prod_prod] at h4
  rcases mul_eq_zero.1 h4 with h | h
  · exact hηI h
  · exact hρ h

/-! ## Uniqueness -/

/-- **A member at equality**: its cylinder measure is `σ_ρ̃` and `μ = p([v])` times the Haar
smearing of `ρ̃`. -/
theorem member_eq_smear {q : ℝ} (hq : 1 < q) {Ψ1 : ℝ → ℝ} {m : Measure ℝ}
    (hm : IsStepMeasure q Ψ1 m) {p : ℝ → ℝ} (hpm : Measurable p) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : μ ∈ modulationOrbit q Ψ1) {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}
    (hΛ : IsFamilyPair q μ Λ B) {π : ℝ → Measure ℝ}
    (hπ : IsPhaseDisintegration q (cylMeasure q Λ) π)
    (h : ∀ᵐ r ∂(rMarginal q (cylMeasure q Λ)),
      rotatedFibre q π r = (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)) :
    SFinite (rMarginal q (cylMeasure q Λ)) ∧ rMarginal q (cylMeasure q Λ) (Iic 0) = 0 ∧
      (∀ x : ℝ, 0 < x → rMarginal q (cylMeasure q Λ) (Ici x) ≠ ⊤) ∧
      cylMeasure q Λ = modCyl q p (rMarginal q (cylMeasure q Λ)) ∧
      m = (((haarPhase q).prod (rMarginal q (cylMeasure q Λ))).map
        fun x => x.2 * x.1).withDensity (liftDensity q p) := by
  obtain ⟨hσ, -⟩ := cylMeasure_spec hq hΛ.1.carried hΛ.1.invariant
  have hρ0 := rMarginal_Iic hσ
  have hfin := (phase_disintegration_exists hq μ Λ B hΛ).1
  haveI : SigmaFinite (rMarginal q (cylMeasure q Λ)) := sigmaFinite_of_Ioi hρ0
    fun ε hε => ne_top_of_le_ne_top (hfin ε hε) (measure_mono Ioi_subset_Ici_self)
  have hσeq := eq_modCyl_of_rotatedFibre hq hpm hπ hρ0 h
  refine ⟨inferInstance, hρ0, hfin, hσeq, ?_⟩
  rw [← map_modCyl q hpm, ← hσeq]
  ext A hA
  rw [← knot_exponent_ladder_3 hq Ψ1 m hm μ hμ Λ B hΛ, slab_one_q_eq_cylMeasure hq hΛ.1 hA,
    Measure.map_apply (measurable_snd.mul measurable_fst) hA]
  rfl

/-- **Two members at equality have the same `Λ`.** -/
theorem modulated_unique {q : ℝ} (hq : 1 < q) {Ψ1 : ℝ → ℝ} {m : Measure ℝ}
    (hm : IsStepMeasure q Ψ1 m) {p : ℝ → ℝ} (hpm : Measurable p)
    (hppos : ∀ᵐ θ ∂(haarPhase q), 0 < p θ) {μ₁ μ₂ : ℝ → ℝ → Measure ℝ}
    (hμ₁ : μ₁ ∈ modulationOrbit q Ψ1) (hμ₂ : μ₂ ∈ modulationOrbit q Ψ1)
    {Λ₁ Λ₂ : Measure (ℝ × ℝ)} {B₁ B₂ : Measure ℝ} (hΛ₁ : IsFamilyPair q μ₁ Λ₁ B₁)
    (hΛ₂ : IsFamilyPair q μ₂ Λ₂ B₂) {π₁ π₂ : ℝ → Measure ℝ}
    (hπ₁ : IsPhaseDisintegration q (cylMeasure q Λ₁) π₁)
    (hπ₂ : IsPhaseDisintegration q (cylMeasure q Λ₂) π₂)
    (h₁ : ∀ᵐ r ∂(rMarginal q (cylMeasure q Λ₁)),
      rotatedFibre q π₁ r = (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ))
    (h₂ : ∀ᵐ r ∂(rMarginal q (cylMeasure q Λ₂)),
      rotatedFibre q π₂ r = (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)) :
    Λ₁ = Λ₂ := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hs₁, h0₁, hf₁, hσ₁, hm₁⟩ := member_eq_smear hq hm hpm hμ₁ hΛ₁ hπ₁ h₁
  obtain ⟨hs₂, h0₂, hf₂, hσ₂, hm₂⟩ := member_eq_smear hq hm hpm hμ₂ hΛ₂ hπ₂ h₂
  -- the smearing is `m / p([v])`
  have hsm : ∀ ρ : Measure ℝ, SFinite ρ → ρ (Iic 0) = 0 →
      m = (((haarPhase q).prod ρ).map fun x => x.2 * x.1).withDensity (liftDensity q p) →
      ((haarPhase q).prod ρ).map (fun x => x.2 * x.1) =
        m.withDensity fun v => (liftDensity q p v)⁻¹ := by
    intro ρ _ hρ0 hmρ
    have hac : ((haarPhase q).prod ρ).map (fun x => x.2 * x.1) ≪ logHaar q := by
      refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
      rw [map_haarPhase_prod_mul_apply hq0 ρ hρ0 hA]
      exact setLIntegral_measure_zero _ _ hA0
    rw [hmρ, withDensity_inv_same (measurable_liftDensity q hpm)
      (hac.ae_le ((ae_logHaar_liftDensity_pos hq hpm hppos).mono fun v hv =>
        (ENNReal.ofReal_pos.2 hv).ne'))
      (ae_of_all _ fun v => ENNReal.ofReal_ne_top)]
  have heq := (hsm _ hs₁ h0₁ hm₁).trans (hsm _ hs₂ h0₂ hm₂).symm
  have hρ := haar_smearing_injective hq _ _ h0₁ h0₂ hf₁ hf₂ heq
  rw [← (cylMeasure_spec hq hΛ₁.1.carried hΛ₁.1.invariant).2,
    ← (cylMeasure_spec hq hΛ₂.1.carried hΛ₂.1.invariant).2, hσ₁, hσ₂, hρ]

/-- On a ladder with no Gaussian part every member has `ℬ = 0`. -/
theorem gauss_eq_zero_measure {q : ℝ} (hq : 1 < q) {Ψ1 : ℝ → ℝ}
    (hnoG : HasNoGaussianStep q Ψ1) {μ : ℝ → ℝ → Measure ℝ} (hμ : μ ∈ modulationOrbit q Ψ1)
    {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ} (hΛ : IsFamilyPair q μ Λ B) : B = 0 := by
  have hBt := gauss_eq_zero_of_noGaussianStep hq hnoG hμ hΛ
  have hpos : B (Ioi 0) = 0 := by
    refine measure_mono_null (fun x hx => ?_)
      (measure_iUnion_null fun n : ℕ => hBt ((n : ℝ) + 1) (by positivity))
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact mem_iUnion.2 ⟨n, hx, by linarith⟩
  refine Measure.measure_univ_eq_zero.1 (measure_mono_null (fun x _ => ?_)
    (measure_union_null hΛ.1.gaussian.1 hpos))
  rcases le_or_gt x 0 with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ## The value -/

/-- **`|μ| KL(μ̄° ‖ η) = ∫ log p([v]) μ(dv)`** for `μ̄° = p η`, `p > 0`. -/
theorem modulated_value {q : ℝ} (hq : 1 < q) {m : Measure ℝ} (hm0 : m univ ≠ 0)
    (hmfin : m univ ≠ ⊤) {p : ℝ → ℝ} (hpm : Measurable p)
    (hp : foldedStepNorm q m = (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ))
    (hppos : ∀ᵐ θ ∂(haarPhase q), 0 < p θ) :
    (m univ * klDiv (foldedStepNorm q m) (haarPhase q)).toReal =
      ∫ v, Real.log (p (qClass q v)) ∂m := by
  haveI := isProbabilityMeasure_haarPhase hq
  have hmuniv : foldMeasure q m univ = m univ := by
    rw [foldMeasure, Measure.map_apply (measurable_qClass q) MeasurableSet.univ, preimage_univ]
  have hprob : foldedStepNorm q m univ = haarPhase q univ := by
    rw [foldedStepNorm, Measure.smul_apply, hmuniv, smul_eq_mul,
      ENNReal.inv_mul_cancel hm0 hmfin, measure_univ]
  haveI : IsProbabilityMeasure (foldedStepNorm q m) := ⟨hprob.trans measure_univ⟩
  have hac : foldedStepNorm q m ≪ haarPhase q := by
    rw [hp]
    exact withDensity_absolutelyContinuous _ _
  have hllr : llr (foldedStepNorm q m) (haarPhase q) =ᵐ[foldedStepNorm q m]
      fun θ => Real.log (p θ) := by
    have h1 : (foldedStepNorm q m).rnDeriv (haarPhase q) =ᵐ[haarPhase q]
        fun θ => ENNReal.ofReal (p θ) := by
      rw [hp]
      exact Measure.rnDeriv_withDensity _ hpm.ennreal_ofReal
    filter_upwards [hac.ae_le h1, hac.ae_le hppos] with θ h1θ h2θ
    simp only [llr, h1θ, ENNReal.toReal_ofReal h2θ.le]
  have hmr : (m univ).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hm0, hmfin⟩
  rw [ENNReal.toReal_mul, toReal_klDiv_of_measure_eq hac hprob, integral_congr_ae hllr,
    foldedStepNorm, integral_smul_measure, foldMeasure,
    integral_map (f := fun x => Real.log (p x)) (measurable_qClass q).aemeasurable
      (Real.measurable_log.comp hpm).aestronglyMeasurable,
    ENNReal.toReal_inv, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hmr, one_mul]

/-! ## No similarity member -/

/-- **If `p` is not almost everywhere constant, the ladder has no similarity member.** -/
theorem modulated_no_similarity {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ) {m : Measure ℝ}
    (hm : IsStepMeasure q Ψ1 m) (hm0 : m univ ≠ 0) (hmfin : m univ ≠ ⊤) {p : ℝ → ℝ}
    (hpm : Measurable p)
    (hp : foldedStepNorm q m = (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ))
    (hnc : ¬ ∃ c : ℝ, ∀ᵐ θ ∂(haarPhase q), p θ = c) :
    ¬ ∃ μ ∈ modulationOrbit q Ψ1, ∀ t : ℝ, 0 < t → ∀ ω : ℝ,
      lineExponent μ t ω = Ψ1 (t * ω) := by
  rintro ⟨μ, hμ, hsim⟩
  haveI := isProbabilityMeasure_haarPhase hq
  obtain ⟨Λ, B, hΛ⟩ := surface_measure_family hq μ hμ.1
  obtain ⟨-, ⟨π, hπ⟩, -⟩ := phase_disintegration_exists hq μ Λ B hΛ
  have hcov := (lineExponent_cov_iff hμ.1 hΛ).1 (phase_entropy_selection_1 hq Ψ1 μ hμ hsim).1
  have h0 : phaseEntropy q (cylMeasure q Λ) π = 0 :=
    (phaseEntropy_eq_zero_iff_slab hq hΛ.1 hπ).2 hcov.1
  have hb := (ladder_bound_1 hq Ψ1 m hm hmfin μ hμ Λ B hΛ π hπ).2.2.1
  rw [h0] at hb
  have hx : m univ * klDiv (foldedStepNorm q m) (haarPhase q) = 0 := by
    have h1 := EReal.le_neg.1 hb
    rw [neg_zero, ← EReal.coe_ennreal_zero, EReal.coe_ennreal_le_coe_ennreal_iff] at h1
    exact le_antisymm h1 bot_le
  have hKL0 : klDiv (foldedStepNorm q m) (haarPhase q) = 0 := (mul_eq_zero.1 hx).resolve_left hm0
  have hmuniv : foldMeasure q m univ = m univ := by
    rw [foldMeasure, Measure.map_apply (measurable_qClass q) MeasurableSet.univ, preimage_univ]
  haveI : IsProbabilityMeasure (foldedStepNorm q m) :=
    ⟨by rw [foldedStepNorm, Measure.smul_apply, hmuniv, smul_eq_mul,
      ENNReal.inv_mul_cancel hm0 hmfin]⟩
  have heq := klDiv_eq_zero_iff.1 hKL0
  rw [hp] at heq
  have hae : (fun θ => ENNReal.ofReal (p θ)) =ᵐ[haarPhase q] fun _ => 1 := by
    rw [← withDensity_eq_iff_of_sigmaFinite hpm.ennreal_ofReal.aemeasurable aemeasurable_const]
    rw [heq]
    exact withDensity_one.symm
  exact hnc ⟨1, hae.mono fun θ hθ => ENNReal.ofReal_eq_one.1 hθ⟩

/-! ## The node -/

/-- **`thm:phase-entropy-modulated-selection`.** For a knot exponent whose ladder has no Gaussian
part, with step measure `μ`, `0 < |μ| < ∞`, (1) `μ̄° = p η` with `p > 0` `η`-a.e. and
`KL(μ̄° ‖ η) < ∞`, and (2) `μ(dv) = p([v])(k(v/q) - k(v)) dv/v` for a nonincreasing `k ≥ 0` with
`∫ (1 ∧ x²) k(x) dx/x < ∞`: the family with `a ≡ 0` and `ϖ*_t(dv) = p([v]) k(v/t) dv/v` is a
member at which `𝔈 = -|μ| KL(μ̄° ‖ η)`; every member has `𝔈` at most this, with equality exactly
at that family, so it is the one maximizer; the maximum is `-∫ log p([v]) μ(dv)`; and if `p` is
not a.e. constant the ladder has no similarity member. -/
theorem phase_entropy_modulated_selection {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ)
    (hΨ1 : IsKnotExponent q Ψ1) (hnoG : HasNoGaussianStep q Ψ1) (m : Measure ℝ)
    (hm : IsStepMeasure q Ψ1 m) (hm0 : m univ ≠ 0) (hmfin : m univ ≠ ⊤) (p : ℝ → ℝ)
    (hpm : Measurable p)
    (hp : foldedStepNorm q m = (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ))
    (hppos : ∀ᵐ θ ∂(haarPhase q), 0 < p θ)
    (hKL : InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q) ≠ ⊤) (k : ℝ → ℝ)
    (hk0 : ∀ x : ℝ, 0 < x → 0 ≤ k x) (hkanti : AntitoneOn k (Ioi 0))
    (hkint : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * k x / x) ≠ ⊤)
    (hmk : m = (volume.restrict (Ioi 0)).withDensity
      fun v => ENNReal.ofReal (p (qClass q v) * (k (v / q) - k v) / v)) :
    (∃ μs ∈ modulationOrbit q Ψ1, ∃ (Λ : Measure (ℝ × ℝ)) (π : ℝ → Measure ℝ),
        IsFamilyPair q μs Λ 0 ∧
        (∀ t : ℝ, 0 < t → slab Λ 0 t = (volume.restrict (Ioi 0)).withDensity
          fun v => ENNReal.ofReal (p (qClass q v) * k (v / t) / v)) ∧
        IsPhaseDisintegration q (cylMeasure q Λ) π ∧
        phaseEntropy q (cylMeasure q Λ) π =
          -(((m univ * InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q)) : ℝ≥0∞) :
            EReal)) ∧
      (∀ μ ∈ modulationOrbit q Ψ1, ∀ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (π : ℝ → Measure ℝ),
        IsFamilyPair q μ Λ B → IsPhaseDisintegration q (cylMeasure q Λ) π →
          phaseEntropy q (cylMeasure q Λ) π ≤
            -(((m univ * InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q)) : ℝ≥0∞) :
              EReal) ∧
          (phaseEntropy q (cylMeasure q Λ) π =
              -(((m univ * InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q)) : ℝ≥0∞) :
                EReal) ↔
            B = 0 ∧ ∀ t : ℝ, 0 < t → slab Λ 0 t = (volume.restrict (Ioi 0)).withDensity
              fun v => ENNReal.ofReal (p (qClass q v) * k (v / t) / v))) ∧
      (m univ * InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q)).toReal =
        ∫ v, Real.log (p (qClass q v)) ∂m ∧
      ((¬ ∃ c : ℝ, ∀ᵐ θ ∂(haarPhase q), p θ = c) →
        ¬ ∃ μ ∈ modulationOrbit q Ψ1, ∀ t : ℝ, 0 < t → ∀ ω : ℝ,
          lineExponent μ t ω = Ψ1 (t * ω)) := by
  have hq0 : 0 < q := by linarith
  haveI := isProbabilityMeasure_haarPhase hq
  have hmuniv : foldMeasure q m univ = m univ := by
    rw [foldMeasure, Measure.map_apply (measurable_qClass q) MeasurableSet.univ, preimage_univ]
  have hp1 : IsProbabilityMeasure ((haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)) := by
    rw [← hp]
    exact ⟨by rw [foldedStepNorm, Measure.smul_apply, hmuniv, smul_eq_mul,
      ENNReal.inv_mul_cancel hm0 hmfin]⟩
  have hklim := tendsto_profile_atTop hk0 hkanti hkint
  -- a measurable version of `k`
  set kt : ℝ → ℝ := fun x => k (Real.exp (Real.log x)) with hkt
  have hkt_eq : ∀ x : ℝ, 0 < x → kt x = k x := fun x hx => by
    simp only [hkt, Real.exp_log hx]
  have hktm : Measurable kt := by
    have ha : Antitone fun u => k (Real.exp u) := fun u u' h =>
      hkanti (Real.exp_pos u) (Real.exp_pos u') (Real.exp_le_exp.2 h)
    exact ha.measurable.comp Real.measurable_log
  have hkt0 : ∀ x : ℝ, 0 < x → 0 ≤ kt x := fun x hx => by
    rw [hkt_eq x hx]
    exact hk0 x hx
  have hktanti : AntitoneOn kt (Ioi 0) := fun x hx y hy hxy => by
    rw [hkt_eq x hx, hkt_eq y hy]
    exact hkanti hx hy hxy
  have hktlim : Tendsto kt atTop (𝓝 0) :=
    hklim.congr' ((eventually_gt_atTop 0).mono fun x hx => (hkt_eq x hx).symm)
  have hmk' : m = (volume.restrict (Ioi 0)).withDensity
      fun v => ENNReal.ofReal (p (qClass q v) * (kt (v / q) - kt v) / v) := by
    rw [hmk]
    exact withDensity_Ioi_congr fun v hv => by rw [hkt_eq v hv, hkt_eq _ (div_pos hv hq0)]
  -- the measure `ρ̃_k` and the candidate
  obtain ⟨ρk, hρs, hρ0, hρfin, C, hC, hρk⟩ := exists_kRho hq hkanti hklim
  set σs := modCyl q p ρk with hσs
  set Λs := orbitMixture q σs with hΛs
  obtain ⟨hΛc, hΛinv, hΛcyl⟩ := orbitMixture_spec hq (modCyl_cylinder_compl q p hρ0)
  have hslab : ∀ t : ℝ, 0 < t → slab Λs 0 t = (volume.restrict (Ioi 0)).withDensity
      fun v => ENNReal.ofReal (p (qClass q v) * k (v / t) / v) :=
    fun t ht => slab_orbitMixture_modCyl hq hpm hk0 ρk hρ0 hρfin hC hρk ht
  -- the knot measure is `ϖ_1`
  obtain ⟨P1, hP1⟩ := hΨ1.1
  obtain ⟨hP1a, hP1map⟩ := knot_data hq hΨ1 hnoG hm hP1
  have hmfold : ScaleSpace.IsFolded m := by
    obtain ⟨P, -, hPm⟩ := hm
    rw [← hPm]
    exact P.ν_folded
  have hslab1 : slab Λs 0 1 = P1.ν := by
    rw [eq_knotLevyMeasure_of_map hq P1 hmfold hP1map, hslab 1 one_pos, hmk',
      knotLevyMeasure_modulated hq hpm hktm hkt0 hktanti hktlim]
    exact withDensity_Ioi_congr fun v hv => by rw [hkt_eq _ (div_pos hv one_pos)]
  have hint : IsLevyIntegrableSurface Λs :=
    (surface_measure_integrable_iff hq Λs hΛinv).1
      ⟨1, one_pos, by rw [hslab1]; exact P1.ν_integrable⟩
  -- `ρ̃_k ≠ 0`, since `μ ≠ 0`
  have hρne : ρk (Ioi 0) ≠ 0 := by
    intro h0
    have hρz : ρk = 0 := by
      refine Measure.measure_univ_eq_zero.1 (measure_mono_null (fun x _ => ?_)
        (measure_union_null hρ0 h0))
      rcases le_or_gt x 0 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hΛz : Λs = 0 := by
      have hw : ((0 : Measure (ℝ × ℝ)).withDensity fun x => liftDensity q p (x.2 * x.1)) = 0 := by
        ext s hs
        rw [withDensity_apply _ hs]
        simp
      rw [hΛs, hσs, hρz, modCyl, Measure.prod_zero, hw, orbitMixture_zero]
    have hle : m ≤ (volume.restrict (Ioi 0)).withDensity
        fun v => ENNReal.ofReal (p (qClass q v) * k (v / q) / v) := by
      rw [hmk]
      refine withDensity_mono ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv0 : (0 : ℝ) < v := hv
      have hvq : 0 < v / q := div_pos hv0 hq0
      have hk : k v ≤ k (v / q) := hkanti hvq hv0 (div_le_self hv0.le hq.le)
      rw [ofReal_lift_mul q p hv0 (sub_nonneg.2 hk), ofReal_lift_mul q p hv0 (hk0 _ hvq)]
      gcongr
      linarith [hk0 v hv0]
    rw [← hslab q hq0, hΛz] at hle
    have hz : slab (0 : Measure (ℝ × ℝ)) 0 q = 0 := by simp [slab]
    rw [hz] at hle
    apply hm0
    rw [le_antisymm hle (Measure.zero_le _)]
    rfl
  -- `(Λ*, 0)` is a pair with (i)–(iv)
  have hσac : (haarPhase q).prod ρk ≪ σs := prod_ac_modCyl hq hpm hppos ρk hρ0
  have hnl : ∀ y : ℝ, 0 < y → Λs ({y} ×ˢ Ioi 0) = 0 := by
    refine (knot_atom_cascades_2_integrable hq σs (modCyl_cylinder_compl q p hρ0)).2.2
      fun θ => ?_
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.prod_prod, haarPhase_ac_volume q (Real.volume_singleton (a := θ)), zero_mul]
  have hpair : IsSurfacePair q Λs 0 :=
    { carried := hΛc
      invariant := hΛinv
      integrable := hint
      gaussian := ⟨by simp, fun t _ => by simp, fun A _ _ => by simp⟩
      no_line := fun y hy => ⟨hnl y hy, by simp⟩
      nondeg := fun s t hs hst => by
        rw [Measure.coe_zero, Pi.zero_apply, add_zero]
        exact orbitMixture_Ioc_pos hq hσac hρne hs hst }
  -- the family of `(Λ*, 0)` is a member
  obtain ⟨μs, hμsQ, hμsD⟩ := surface_measure_pair hq Λs 0 hpair
  have hμs : μs ∈ modulationOrbit q Ψ1 := by
    refine ⟨hμsQ, fun ω => ?_⟩
    have hei := (surface_measure_exponent μs hμsQ Λs 0 hpair).1 hμsD
    have ha : (surfacePairOf Λs 0 1 hpair.carried (hpair.integrable 1 one_pos)).a = P1.a := by
      simp [surfacePairOf, hP1a]
    rw [charFun_kernel_eq_exp hμsQ.1 zero_le_one, hei 1 one_pos,
      ← surfacePairOf_exponent 0 hpair.carried (hpair.integrable 1 one_pos),
      symLevyPair_exponent_congr (Q := P1) ha hslab1, ← hP1 ω]
  have hFP : IsFamilyPair q μs Λs 0 := ⟨hpair, hμsD⟩
  -- its disintegration and its entropy
  have hπs : IsPhaseDisintegration q (cylMeasure q Λs) (modFibre q p) := by
    rw [hΛcyl]
    exact isPhaseDisintegration_modCyl hq hpm hp1 ρk hρ0
  have hfibs : ∀ᵐ r ∂(rMarginal q (cylMeasure q Λs)),
      rotatedFibre q (modFibre q p) r = foldedStepNorm q m := by
    rw [hΛcyl, rMarginal_modCyl hq hpm hp1 ρk hρ0]
    filter_upwards [ae_pos_of_Iic_zero hρ0] with r hr
    rw [rotatedFibre_modFibre hq hpm hr, hp]
  have hEs := ((ladder_bound_1 hq Ψ1 m hm hmfin μs hμs Λs 0 hFP (modFibre q p) hπs).2.2.2.2
    hKL).2 hfibs
  refine ⟨⟨μs, hμs, Λs, modFibre q p, hFP, hslab, hπs, hEs⟩, fun μ hμ Λ B π hΛ hπ => ?_,
    modulated_value hq hm0 hmfin hpm hp hppos, modulated_no_similarity hq Ψ1 hm hm0 hmfin hpm hp⟩
  have hlb := ladder_bound_1 hq Ψ1 m hm hmfin μ hμ Λ B hΛ π hπ
  refine ⟨hlb.2.2.1, ⟨fun hE => ?_, fun ⟨_, hsl⟩ => ?_⟩⟩
  · -- uniqueness
    have hfib := (hlb.2.2.2.2 hKL).1 hE
    rw [hp] at hfib hfibs
    have hΛeq := modulated_unique hq hm hpm hppos hμ hμs hΛ hFP hπ hπs hfib hfibs
    exact ⟨gauss_eq_zero_measure hq hnoG hμ hΛ, fun t ht => by rw [hΛeq]; exact hslab t ht⟩
  · -- the candidate's slabs give `Λ = Λ*`
    have hΛeq : Λ = Λs := quadrant_measure_ext hΛ.1.carried hΛc
      (fun t ht ε hε => SymLevyPair_measure_Ioi_ne_top
        (surfacePairOf Λ B t hΛ.1.carried (hΛ.1.integrable t ht)) hε)
      fun t ht => (hsl t ht).trans (hslab t ht).symm
    rw [hΛeq] at hπ hlb ⊢
    have hae := (phase_disintegration_exists hq μs Λs 0 hFP).2.2 π (modFibre q p) hπ hπs
    refine (hlb.2.2.2.2 hKL).2 ?_
    filter_upwards [hae, hfibs] with r hr hr'
    rw [rotatedFibre, hr]
    exact hr'

/-! ## The converse: attainment of the bound gives (2) (review round 3, supp.S3) -/

/-- **Attainment gives (2).** Under (1), if a member attains the bound, the step measure is
`p([v])(k(v/q) - k(v)) dv/v` with `k(x) := ℓ⁻¹ρ̃((x,∞))`, `ρ̃` the `r`-marginal of that member's
cylinder measure; `k ≥ 0` is nonincreasing, and `∫ (1 ∧ x²) k(x) dx/x < ∞` by (A.e3) for the
member. The proof reads neither `p > 0`, nor the absence of a Gaussian part, nor `|μ| > 0`. -/
theorem phase_entropy_modulated_selection_converse {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ)
    (m : Measure ℝ) (hm : IsStepMeasure q Ψ1 m) (hmfin : m univ ≠ ⊤) (p : ℝ → ℝ)
    (hpm : Measurable p)
    (hp : foldedStepNorm q m = (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ))
    (hKL : InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q) ≠ ⊤)
    {μ : ℝ → ℝ → Measure ℝ} (hμ : μ ∈ modulationOrbit q Ψ1) {Λ : Measure (ℝ × ℝ)}
    {B : Measure ℝ} (hΛ : IsFamilyPair q μ Λ B) {π : ℝ → Measure ℝ}
    (hπ : IsPhaseDisintegration q (cylMeasure q Λ) π)
    (hE : phaseEntropy q (cylMeasure q Λ) π =
      -(((m univ * InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q)) : ℝ≥0∞) :
        EReal)) :
    ∃ k : ℝ → ℝ, (∀ x : ℝ, 0 < x → 0 ≤ k x) ∧ AntitoneOn k (Ioi 0) ∧
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * k x / x) ≠ ⊤ ∧
      m = (volume.restrict (Ioi 0)).withDensity
        fun v => ENNReal.ofReal (p (qClass q v) * (k (v / q) - k v) / v) := by
  have hq0 : 0 < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos hq
  have hlb := ladder_bound_1 hq Ψ1 m hm hmfin μ hμ Λ B hΛ π hπ
  have hfib := (hlb.2.2.2.2 hKL).1 hE
  rw [hp] at hfib
  obtain ⟨hs, h0, hfin, -, hmρ⟩ := member_eq_smear hq hm hpm hμ hΛ hπ hfib
  set ρ := rMarginal q (cylMeasure q Λ) with hρ
  haveI := hs
  set k : ℝ → ℝ := fun x => (ρ (Ioi x)).toReal / Real.log q with hk
  have hIoi : ∀ x : ℝ, 0 < x → ρ (Ioi x) ≠ ⊤ := fun x hx =>
    ne_top_of_le_ne_top (hfin x hx) (measure_mono Ioi_subset_Ici_self)
  have hk0 : ∀ x : ℝ, 0 < x → 0 ≤ k x := fun x _ => div_nonneg ENNReal.toReal_nonneg hl.le
  have hkanti : AntitoneOn k (Ioi 0) := by
    intro x hx y hy hxy
    exact div_le_div_of_nonneg_right
      (ENNReal.toReal_mono (hIoi x hx) (measure_mono (Ioi_subset_Ioi hxy))) hl.le
  -- the integrability, from (A.e3) for the member
  have hkint : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * k x / x) ≠ ⊤ := by
    obtain ⟨hσ, hmix⟩ := cylMeasure_spec hq hΛ.1.carried hΛ.1.invariant
    have hint : IsCylIntegrable (cylMeasure q Λ) := by
      have := (knot_atom_cascades_2_integrable hq (cylMeasure q Λ) hσ).1
      rw [hmix] at this
      exact this.1 hΛ.1.integrable
    have hprod : IsCylIntegrable ((haarPhase q).prod ρ) :=
      (isCylIntegrable_prod_iff hq ρ h0).2 (lintegral_rWeight_ne_top hσ hint)
    refine ne_top_of_le_ne_top ((strata_cylinder_1_integrability hq ρ h0).2.1 hprod) ?_
    refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hkx : ENNReal.ofReal (k x) = ρ (Ioi x) / ENNReal.ofReal (Real.log q) := by
      rw [hk, ENNReal.ofReal_div_of_pos hl, ENNReal.ofReal_toReal (hIoi x hx0)]
    rw [show min 1 (x ^ 2) * k x / x = min 1 (x ^ 2) / x * k x by ring,
      ENNReal.ofReal_mul (div_nonneg (le_min zero_le_one (sq_nonneg x)) hx0.le), hkx]
    exact mul_le_mul_of_nonneg_left
      (ENNReal.div_le_div_right (measure_mono Ioi_subset_Ici_self) _) zero_le
  refine ⟨k, hk0, hkanti, hkint, ?_⟩
  -- the smearing has the density `ρ̃((v/q, v])` against `dv/(ℓv)`
  have hsm : ((haarPhase q).prod ρ).map (fun x => x.2 * x.1) =
      (logHaar q).withDensity fun v => ρ (Ioc (v / q) v) := by
    ext A hA
    rw [map_haarPhase_prod_mul_apply hq0 ρ h0 hA, withDensity_apply _ hA]
  have hf12 : Measurable ((fun y : ℝ => ENNReal.ofReal (1 / (Real.log q * y))) *
      fun v => ρ (Ioc (v / q) v)) :=
    (measurable_logHaar_density q).mul (measurable_measure_Ioc_div q ρ)
  rw [hmρ, hsm, logHaar, ← withDensity_mul _ (measurable_logHaar_density q)
    (measurable_measure_Ioc_div q ρ), ← withDensity_mul _ hf12 (measurable_liftDensity q hpm)]
  refine withDensity_Ioi_congr fun v hv => ?_
  have hvq : 0 < v / q := div_pos hv hq0
  have hle : v / q ≤ v := div_le_self hv.le hq.le
  have hsplit : ρ (Ioi (v / q)) = ρ (Ioc (v / q) v) + ρ (Ioi v) := by
    have hdisj : Disjoint (Ioc (v / q) v) (Ioi v) :=
      disjoint_left.2 fun x hx hx' => not_lt.2 hx.2 hx'
    rw [← Ioc_union_Ioi_eq_Ioi hle, measure_union hdisj measurableSet_Ioi]
  have hIoc : ρ (Ioc (v / q) v) ≠ ⊤ :=
    ne_top_of_le_ne_top (hIoi _ hvq) (measure_mono Ioc_subset_Ioi_self)
  have hdiff : k (v / q) - k v = (ρ (Ioc (v / q) v)).toReal / Real.log q := by
    simp only [hk]
    rw [hsplit, ENNReal.toReal_add hIoc (hIoi v hv)]
    ring
  simp only [Pi.mul_apply, liftDensity]
  rw [hdiff, show p (qClass q v) * ((ρ (Ioc (v / q) v)).toReal / Real.log q) / v =
      p (qClass q v) * (1 / (Real.log q * v) * (ρ (Ioc (v / q) v)).toReal) by ring,
    ENNReal.ofReal_mul' (mul_nonneg (one_div_pos.2 (mul_pos hl hv)).le ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (one_div_pos.2 (mul_pos hl hv)).le, ENNReal.ofReal_toReal hIoc]
  ring

/-- **`thm:phase-entropy-modulated-selection`, the equivalence.** Under the theorem's standing
hypotheses and (1), the bound `-|μ| KL(μ̄° ‖ η)` is attained by some member if and only if (2)
holds for some nonincreasing `k ≥ 0` with `∫ (1 ∧ x²) k(x) dx/x < ∞`. -/
theorem phase_entropy_modulated_selection_iff {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ)
    (hΨ1 : IsKnotExponent q Ψ1) (hnoG : HasNoGaussianStep q Ψ1) (m : Measure ℝ)
    (hm : IsStepMeasure q Ψ1 m) (hm0 : m univ ≠ 0) (hmfin : m univ ≠ ⊤) (p : ℝ → ℝ)
    (hpm : Measurable p)
    (hp : foldedStepNorm q m = (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ))
    (hppos : ∀ᵐ θ ∂(haarPhase q), 0 < p θ)
    (hKL : InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q) ≠ ⊤) :
    (∃ μ ∈ modulationOrbit q Ψ1, ∃ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
        (π : ℝ → Measure ℝ), IsFamilyPair q μ Λ B ∧ IsPhaseDisintegration q (cylMeasure q Λ) π ∧
        phaseEntropy q (cylMeasure q Λ) π =
          -(((m univ * InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q)) : ℝ≥0∞) :
            EReal)) ↔
      ∃ k : ℝ → ℝ, (∀ x : ℝ, 0 < x → 0 ≤ k x) ∧ AntitoneOn k (Ioi 0) ∧
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * k x / x) ≠ ⊤ ∧
        m = (volume.restrict (Ioi 0)).withDensity
          fun v => ENNReal.ofReal (p (qClass q v) * (k (v / q) - k v) / v) := by
  constructor
  · rintro ⟨μ, hμ, Λ, B, π, hΛ, hπ, hE⟩
    exact phase_entropy_modulated_selection_converse hq Ψ1 m hm hmfin p hpm hp hKL hμ hΛ hπ hE
  · rintro ⟨k, hk0, hkanti, hkint, hmk⟩
    obtain ⟨⟨μs, hμs, Λ, π, hFP, -, hπs, hEs⟩, -⟩ := phase_entropy_modulated_selection hq Ψ1
      hΨ1 hnoG m hm hm0 hmfin p hpm hp hppos hKL k hk0 hkanti hkint hmk
    exact ⟨μs, hμs, Λ, 0, π, hFP, hπs, hEs⟩

end Pyramids
