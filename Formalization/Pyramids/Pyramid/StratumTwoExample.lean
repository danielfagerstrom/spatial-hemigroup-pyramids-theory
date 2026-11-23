/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.Synthesis
import Pyramids.Pyramid.FamilyDilations
import Pyramids.Pyramid.NoLatticeKernel
import Pyramids.Cited.A45
import AffineHemigroup.SimilarityLine

/-!
# `prop:stratum-two-example`: an isotropic family strictly in stratum 2

Blueprint: `blueprint/src/parts/03-pyramid.tex`. Moved from `PyramidsSkeleton.Ch03Pyramid` in wave
2f, unchanged in statement and name.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology Matrix

variable {d : ℕ}

/-! ## Laws on spheres -/

theorem sphereLaw_apply (r : ℝ) {B : Set (Rd d)} (hB : MeasurableSet B) :
    sphereLaw d r B = normSphere d ((fun x => r • x) ⁻¹' B) :=
  Measure.map_apply (continuous_const_smul r).measurable hB

theorem measurableSet_sphere (ρ : ℝ) : MeasurableSet {x : Rd d | ‖x‖ = ρ} :=
  measurableSet_eq_fun continuous_norm.measurable measurable_const

/-- `σ_r` gives the sphere of radius `ρ` the mass `1` if `ρ = r`, and `0` otherwise. -/
theorem sphereLaw_sphere (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    sphereLaw d r {x : Rd d | ‖x‖ = ρ} = if r = ρ then 1 else 0 := by
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  rw [sphereLaw_apply r (measurableSet_sphere ρ)]
  have hsub : ∀ u : Rd d, ‖u‖ = 1 → (‖r • u‖ = ρ ↔ r = ρ) := by
    intro u hu
    rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le]
  have hnull : normSphere d {u : Rd d | ‖u‖ ≠ 1} = 0 := by
    have := ae_normSphere_norm (d := d)
    rwa [ae_iff] at this
  split_ifs with h
  · have hm : MeasurableSet ((fun x => r • x) ⁻¹' {x : Rd d | ‖x‖ = ρ}) :=
      (continuous_const_smul r).measurable (measurableSet_sphere ρ)
    rw [← prob_compl_eq_zero_iff hm]
    refine measure_mono_null (fun u hu => ?_) hnull
    intro hu1
    exact hu ((hsub u hu1).2 h)
  · refine measure_mono_null (fun u hu => ?_) hnull
    intro hu1
    exact h ((hsub u hu1).1 hu)

/-- The radii `hqⁱ` are distinct. -/
theorem radius_injective {q h : ℝ} (hq : 1 < q) (hh : 0 < h) {i j : ℤ}
    (hij : h * q ^ i = h * q ^ j) : i = j := by
  have h1 : q ^ i = q ^ j := mul_left_cancel₀ hh.ne' hij
  exact zpow_right_injective₀ (by linarith) hq.ne' h1

theorem sphereTrain_sphere (hd : 1 ≤ d) {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ) (θ : ℝ)
    (i : ℤ) : sphereTrain d q h w θ {x : Rd d | ‖x‖ = h * q ^ i} =
      ENNReal.ofReal (dgWeight w θ i) := by
  rw [sphereTrain, Measure.sum_apply _ (measurableSet_sphere _)]
  have hpos : ∀ j : ℤ, 0 < h * q ^ j := fun j => mul_pos hh (zpow_pos (by linarith) j)
  simp only [Measure.smul_apply, smul_eq_mul, sphereLaw_sphere hd (hpos _)]
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    rw [if_neg (fun hji => hj (radius_injective hq hh hji)), mul_zero]

/-- `σ_r` is invariant under every linear isometry. -/
theorem sphereLaw_preimage_isometry (e : Rd d ≃ₗᵢ[ℝ] Rd d) (r : ℝ) {s : Set (Rd d)}
    (hs : MeasurableSet s) : sphereLaw d r (e ⁻¹' s) = sphereLaw d r s := by
  have hm : MeasurableSet ((fun x => r • x) ⁻¹' s) := (continuous_const_smul r).measurable hs
  rw [sphereLaw_apply r (e.continuous.measurable hs), sphereLaw_apply r hs]
  have hpre : (fun x : Rd d => r • x) ⁻¹' (e ⁻¹' s) = e ⁻¹' ((fun x => r • x) ⁻¹' s) := by
    ext u
    simp only [mem_preimage, map_smul]
  rw [hpre, ← Measure.map_apply e.continuous.measurable hm, normSphere_map_isometry]

theorem sphereTrain_map_isometry (e : Rd d ≃ₗᵢ[ℝ] Rd d) (q h : ℝ) (w : ℤ → ℝ) (θ : ℝ) :
    (sphereTrain d q h w θ).map e = sphereTrain d q h w θ := by
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs, sphereTrain,
    Measure.sum_apply _ (e.continuous.measurable hs), Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul, sphereLaw_preimage_isometry e _ hs]

theorem sphereTrain_zero_mass {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ) (θ : ℝ) :
    sphereTrain d q h w θ {0} = 0 := by
  have hnull : normSphere d {u : Rd d | ‖u‖ ≠ 1} = 0 := by
    have := ae_normSphere_norm (d := d)
    rwa [ae_iff] at this
  rw [sphereTrain, Measure.sum_apply _ (measurableSet_singleton 0)]
  refine ENNReal.tsum_eq_zero.2 fun i => ?_
  have hr : h * q ^ i ≠ 0 := (mul_pos hh (zpow_pos (by linarith) i)).ne'
  rw [Measure.smul_apply, sphereLaw_apply _ (measurableSet_singleton 0),
    measure_mono_null (fun u hu => ?_) hnull, smul_zero]
  intro hu1
  have h0 : (h * q ^ i) • u = 0 := hu
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact hr h1
  · rw [h1, norm_zero] at hu1
    exact zero_ne_one hu1

theorem lintegral_sphereLaw_radial (hd : 1 ≤ d) (r : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g ‖x‖ ∂sphereLaw d r = g |r| := by
  haveI := isProbabilityMeasure_normSphere (d := d) hd
  rw [sphereLaw, lintegral_map (f := fun x : Rd d => g ‖x‖) (hg.comp continuous_norm.measurable)
    (continuous_const_smul r).measurable]
  rw [lintegral_congr_ae (g := fun _ => g |r|) ?_, lintegral_const, measure_univ, mul_one]
  filter_upwards [ae_normSphere_norm] with u hu
  simp [norm_smul, hu]

theorem lintegral_sphereTrain (q h : ℝ) (w : ℤ → ℝ) (θ : ℝ) (f : Rd d → ℝ≥0∞) :
    ∫⁻ x, f x ∂sphereTrain d q h w θ =
      ∑' i, ENNReal.ofReal (dgWeight w θ i) * ∫⁻ x, f x ∂sphereLaw d (h * q ^ i) := by
  rw [sphereTrain, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

/-! ## The weights -/

theorem dgWeight_nonneg {w : ℤ → ℝ} (hw0 : ∀ i, 0 ≤ w i) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (i : ℤ) : 0 ≤ dgWeight w θ i := by
  unfold dgWeight
  have := hw0 i
  have := hw0 (i - 1)
  have := hθ.1
  have := hθ.2
  positivity

theorem dgWeight_le {w : ℤ → ℝ} (hwanti : Antitone w) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (i : ℤ) : dgWeight w θ i ≤ w (i - 1) := by
  unfold dgWeight
  have h1 : w i ≤ w (i - 1) := hwanti (by omega)
  nlinarith [hθ.1, hθ.2]

theorem dgWeight_mono {w : ℤ → ℝ} (hwanti : Antitone w) {θ θ' : ℝ} (hθθ' : θ ≤ θ') (i : ℤ) :
    dgWeight w θ i ≤ dgWeight w θ' i := by
  unfold dgWeight
  have h1 : w i ≤ w (i - 1) := hwanti (by omega)
  nlinarith

theorem logb_mem_Icc {q t : ℝ} (hq : 1 < q) (ht : t ∈ Icc (1 : ℝ) q) :
    Real.logb q t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨Real.logb_nonneg hq ht.1, ?_⟩
  calc Real.logb q t ≤ Real.logb q q := Real.logb_le_logb_of_le hq (by linarith [ht.1]) ht.2
    _ = 1 := Real.logb_self_eq_one hq

/-- The Lévy integrability of the train: `∑ᵢ w_{i-1} (1 ∧ h²q^{2i}) < ∞`. -/
theorem train_summable {q h : ℝ} (hq : 1 < q) (w : ℤ → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hneg : Summable fun i : {i : ℤ // i < 0} => w i * q ^ (2 * (i : ℤ)))
    (hpos : Summable fun i : {i : ℤ // 0 ≤ i} => w i) :
    Summable fun i : ℤ => w (i - 1) * min ((h * q ^ i) ^ 2) 1 := by
  have hq0 : 0 < q := by linarith
  set f : ℤ → ℝ := fun j => if 0 ≤ j then w j else (h * q) ^ 2 * (w j * q ^ (2 * j)) with hf
  have hfs : Summable f := by
    rw [← summable_subtype_and_compl (s := {j : ℤ | 0 ≤ j})]
    constructor
    · change Summable fun x : {i : ℤ // 0 ≤ i} => f x
      exact hpos.congr fun j => by simp [hf, j.2]
    · let e : {i : ℤ // i < 0} ≃ ↥({j : ℤ | 0 ≤ j}ᶜ) :=
        Equiv.subtypeEquivRight (fun x => by simp)
      refine e.summable_iff.1 ((hneg.mul_left ((h * q) ^ 2)).congr fun j => ?_)
      have hj : ¬ 0 ≤ (j : ℤ) := not_le.2 j.2
      simp [e, hf, hj]
  have hshift : Summable fun j : ℤ => w j * min ((h * q ^ (j + 1)) ^ 2) 1 := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hw0 j) (le_min (sq_nonneg _) zero_le_one))
      (fun j => ?_) hfs
    by_cases hj : 0 ≤ j
    · simp only [hf, if_pos hj]
      exact mul_le_of_le_one_right (hw0 j) (min_le_right _ _)
    · simp only [hf, if_neg hj]
      have he : (h * q ^ (j + 1)) ^ 2 = (h * q) ^ 2 * q ^ (2 * j) := by
        rw [zpow_add_one₀ hq0.ne' j, show (2 : ℤ) * j = j + j by ring, zpow_add₀ hq0.ne' j j]
        ring
      calc w j * min ((h * q ^ (j + 1)) ^ 2) 1 ≤ w j * (h * q ^ (j + 1)) ^ 2 :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (hw0 j)
        _ = (h * q) ^ 2 * (w j * q ^ (2 * j)) := by rw [he]; ring
  refine (Equiv.addRight (1 : ℤ)).summable_iff.1 (hshift.congr fun j => ?_)
  simp

/-! ## The train is a symmetric, rotation-invariant Lévy measure -/

section Train

variable {q h : ℝ} (hq : 1 < q) (hh : 0 < h) {w : ℤ → ℝ} (hw0 : ∀ i, 0 ≤ w i)
  (hwanti : Antitone w)
  (hneg : Summable fun i : {i : ℤ // i < 0} => w i * q ^ (2 * (i : ℤ)))
  (hpos : Summable fun i : {i : ℤ // 0 ≤ i} => w i)
include hq hh hw0 hwanti hneg hpos

omit hh in
theorem sphereTrain_levy (hd : 1 ≤ d) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂sphereTrain d q h w θ ≠ ⊤ := by
  have hg : Measurable fun r : ℝ => ENNReal.ofReal (min (r ^ 2) 1) := by fun_prop
  rw [lintegral_sphereTrain]
  have hterm : ∀ i : ℤ, ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂sphereLaw d (h * q ^ i) =
      ENNReal.ofReal (min ((h * q ^ i) ^ 2) 1) := fun i => by
    have := lintegral_sphereLaw_radial hd (h * q ^ i) hg
    simp only [sq_abs] at this
    exact this
  simp_rw [hterm]
  have hS := train_summable (h := h) hq w hw0 hneg hpos
  have hnn : ∀ i : ℤ, 0 ≤ w (i - 1) * min ((h * q ^ i) ^ 2) 1 :=
    fun i => mul_nonneg (hw0 _) (le_min (sq_nonneg _) zero_le_one)
  refine ne_top_of_le_ne_top
    (ENNReal.ofReal_ne_top (r := ∑' i, w (i - 1) * min ((h * q ^ i) ^ 2) 1))
    ?_
  rw [ENNReal.ofReal_tsum_of_nonneg hnn hS]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← ENNReal.ofReal_mul (dgWeight_nonneg hw0 hθ i)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (dgWeight_le hwanti hθ i)
    (le_min (sq_nonneg _) zero_le_one))

theorem exists_trainData (hd : 1 ≤ d) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ∃ E : SymLevyData d, E.A = 0 ∧ E.ν = sphereTrain d q h w θ :=
  ⟨⟨0, sphereTrain d q h w θ, Matrix.PosSemidef.zero, sphereTrain_zero_mass hq hh w θ,
    sphereTrain_levy hq hw0 hwanti hneg hpos hd hθ,
    by rw [← coe_neg_isometry]; exact sphereTrain_map_isometry _ q h w θ⟩, rfl, rfl⟩

/-- The integral of `1 - cos⟨ω, ·⟩` against the train is affine in the phase. -/
theorem integral_sphereTrain (hd : 1 ≤ d) (ω : Rd d) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂sphereTrain d q h w θ =
      (1 - θ) * ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂sphereTrain d q h w 0 +
        θ * ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂sphereTrain d q h w 1 := by
  have hnn : ∀ x : Rd d, 0 ≤ 1 - Real.cos ⟪ω, x⟫ := fun x => by linarith [Real.cos_le_one ⟪ω, x⟫]
  have hm : AEStronglyMeasurable (fun x : Rd d => 1 - Real.cos ⟪ω, x⟫) (sphereTrain d q h w θ) :=
    (by fun_prop : Continuous fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).aestronglyMeasurable
  have hfin : ∀ θ' ∈ Icc (0 : ℝ) 1,
      ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) ∂sphereTrain d q h w θ' ≠ ⊤ := by
    intro θ' hθ'
    obtain ⟨E, -, hEν⟩ := exists_trainData hq hh hw0 hwanti hneg hpos hd hθ'
    have hI := E.triplet.integrable_one_sub_cos ω
    change Integrable _ E.ν at hI
    rw [hEν] at hI
    exact hI.lintegral_lt_top.ne
  set L : ℝ → ℝ≥0∞ := fun θ' => ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) ∂sphereTrain d q h w θ'
    with hL
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hsplit : L θ = ENNReal.ofReal (1 - θ) * L 0 + ENNReal.ofReal θ * L 1 := by
    simp only [hL, lintegral_sphereTrain]
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun i => ?_
    have hw1 : dgWeight w θ i = (1 - θ) * w i + θ * w (i - 1) := rfl
    have hd0 : dgWeight w 0 i = w i := by simp [dgWeight]
    have hd1 : dgWeight w 1 i = w (i - 1) := by simp [dgWeight]
    rw [hw1, hd0, hd1, ENNReal.ofReal_add (mul_nonneg (by linarith [hθ.2]) (hw0 i))
      (mul_nonneg hθ.1 (hw0 _)), ENNReal.ofReal_mul (by linarith [hθ.2]),
      ENNReal.ofReal_mul hθ.1]
    ring
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hm,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn)
      (by fun_prop : Continuous fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn)
      (by fun_prop : Continuous fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).aestronglyMeasurable]
  change (L θ).toReal = (1 - θ) * (L 0).toReal + θ * (L 1).toReal
  rw [hsplit, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin 0 h0))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin 1 h1)), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [hθ.2]), ENNReal.toReal_ofReal hθ.1]

end Train

/-- The train is monotone in the phase. -/
theorem sphereTrain_mono {q h : ℝ} {w : ℤ → ℝ} (hwanti : Antitone w) {θ θ' : ℝ} (hθθ' : θ ≤ θ') :
    sphereTrain d q h w θ ≤ sphereTrain d q h w θ' := by
  rw [Measure.le_iff]
  intro s hs
  rw [sphereTrain, sphereTrain, Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  refine ENNReal.tsum_le_tsum fun i => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  exact dgWeight_mono hwanti hθθ' i

/-- At phase `1` the train is the dilate by `q` of the train at phase `0`. -/
theorem sphereTrain_one {q h : ℝ} (hq : 1 < q) (w : ℤ → ℝ) :
    sphereTrain d q h w 1 = (sphereTrain d q h w 0).map (fun x => q • x) := by
  have hq0 : 0 < q := by linarith
  ext s hs
  have hm : MeasurableSet ((fun x : Rd d => q • x) ⁻¹' s) :=
    (continuous_const_smul q).measurable hs
  rw [Measure.map_apply (continuous_const_smul q).measurable hs, sphereTrain, sphereTrain,
    Measure.sum_apply _ hs, Measure.sum_apply _ hm]
  simp only [Measure.smul_apply, smul_eq_mul]
  conv_lhs => rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  refine tsum_congr fun i => ?_
  simp only [Equiv.coe_addRight]
  congr 1
  · simp [dgWeight]
  · rw [sphereLaw_apply _ hs, sphereLaw_apply _ hm]
    congr 1
    ext u
    simp only [mem_preimage, smul_smul]
    rw [zpow_add_one₀ hq0.ne']
    ring_nf


/-! ## `prop:stratum-two-example` -/

/-- Data with `A = 0` and the train as Lévy measure have an exponent invariant under `O(d)`. -/
theorem trainData_exponent_orth {q h : ℝ} {w : ℤ → ℝ} {θ : ℝ} {E : SymLevyData d} (hA : E.A = 0)
    (hν : E.ν = sphereTrain d q h w θ) {Q : Mat d} (hQ : Q ∈ orthSet d) (ω : Rd d) :
    E.exponent (lin Qᵀ ω) = E.exponent ω := by
  simp only [SymLevyData.exponent, pairExponent, hA, quad_zero, zero_add, hν]
  have hinner : ∀ x : Rd d, ⟪lin Qᵀ ω, x⟫ = ⟪ω, lin Q x⟫ := fun x => by
    rw [inner_lin_left, Matrix.transpose_transpose]
  simp_rw [hinner]
  have hmap : (sphereTrain d q h w θ).map (lin Q) = sphereTrain d q h w θ :=
    sphereTrain_map_isometry (orthIsometry hQ) q h w θ
  rw [← integral_map (lin Q).continuous.aemeasurable
    (by fun_prop : Continuous fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).aestronglyMeasurable, hmap]

/-- **`prop:stratum-two-example`, the hypotheses of `lem:synthesis`.** Data with `A_t = 0` and
`ν_t = ∑_i [(1 - θ) w_i + θ w_{i-1}] σ_{hq^i}` at `t = q^θ ∈ [1, q]` exist, and any such data meet
the hypotheses of `lem:synthesis`. -/
theorem stratum_two_example_data (hd : 1 ≤ d) {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : Antitone w) (hwne : ∃ i, w i ≠ 0)
    (hneg : Summable fun i : {i : ℤ // i < 0} => w i * q ^ (2 * (i : ℤ)))
    (hpos : Summable fun i : {i : ℤ // 0 ≤ i} => w i) :
    (∃ D : ℝ → SymLevyData d, ∀ t ∈ Icc (1 : ℝ) q,
        (D t).A = 0 ∧ (D t).ν = sphereTrain d q h w (Real.logb q t)) ∧
      ∀ D : ℝ → SymLevyData d, (∀ t ∈ Icc (1 : ℝ) q,
        (D t).A = 0 ∧ (D t).ν = sphereTrain d q h w (Real.logb q t)) → IsSynthesisData q D := by
  refine ⟨?_, fun D hD => ?_⟩
  · have hex : ∀ t : ℝ, ∃ E : SymLevyData d, t ∈ Icc (1 : ℝ) q →
        E.A = 0 ∧ E.ν = sphereTrain d q h w (Real.logb q t) := by
      intro t
      by_cases ht : t ∈ Icc (1 : ℝ) q
      · obtain ⟨E, hE⟩ := exists_trainData hq hh hw0 hwanti hneg hpos hd (logb_mem_Icc hq ht)
        exact ⟨E, fun _ => hE⟩
      · exact ⟨SymLevyData.zero, fun h' => absurd h' ht⟩
    choose D hD using hex
    exact ⟨D, hD⟩
  -- a strict step of the weights
  obtain ⟨i₀, hi₀⟩ : ∃ i, w i < w (i - 1) := by
    by_contra hcon
    push Not at hcon
    have hconst : ∀ i : ℤ, w i = w 0 := by
      have hstep : ∀ i : ℤ, w (i - 1) = w i := fun i =>
        le_antisymm (hcon i) (hwanti (by omega))
      intro i
      induction i using Int.induction_on with
      | zero => rfl
      | succ n ih => rw [← ih, ← hstep ((n : ℤ) + 1), add_sub_cancel_right]
      | pred n ih => rw [← ih, hstep (-(n : ℤ))]
    obtain ⟨i, hi⟩ := hwne
    haveI : Infinite {i : ℤ // 0 ≤ i} := Infinite.of_injective
      (fun n : ℕ => (⟨n, Int.natCast_nonneg n⟩ : {i : ℤ // 0 ≤ i}))
      (fun a b hab => by simpa using hab)
    have hz : w 0 = 0 := by
      have h' : Summable fun _ : {i : ℤ // 0 ≤ i} => w 0 := hpos.congr fun j => hconst j
      exact (summable_const_iff (w 0)).1 h'
    exact hi (by rw [hconst i, hz])
  have hq0 : 0 < q := by linarith
  have hspec := fun t (ht : t ∈ Icc (1 : ℝ) q) => hD t ht
  have hexp : ∀ t ∈ Icc (1 : ℝ) q, ∀ ω : Rd d,
      (D t).exponent ω = ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂sphereTrain d q h w (Real.logb q t) := by
    intro t ht ω
    simp only [SymLevyData.exponent, pairExponent, (hspec t ht).1, (hspec t ht).2, quad_zero,
      zero_add]
  refine ⟨fun ω => ?_, fun s t hs hst htq => ?_, ?_⟩
  · -- continuity: affine in `log_q t`
    have hcont : ContinuousOn (fun t => (1 - Real.logb q t) *
        ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂sphereTrain d q h w 0 +
        Real.logb q t * ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂sphereTrain d q h w 1) (Icc 1 q) := by
      have hl : ContinuousOn (Real.logb q) (Icc 1 q) :=
        Real.continuousOn_logb.mono fun t ht => by
          simp only [mem_compl_iff, mem_singleton_iff]
          linarith [ht.1]
      exact ((continuousOn_const.sub hl).mul continuousOn_const).add (hl.mul continuousOn_const)
    refine hcont.congr fun t ht => ?_
    rw [hexp t ht ω, integral_sphereTrain hq hh hw0 hwanti hneg hpos hd ω (logb_mem_Icc hq ht)]
  · have hsI : s ∈ Icc (1 : ℝ) q := ⟨hs, (hst.trans_le htq).le⟩
    have htI : t ∈ Icc (1 : ℝ) q := ⟨hs.trans hst.le, htq⟩
    have hlog : Real.logb q s < Real.logb q t := Real.logb_lt_logb hq (by linarith) hst
    refine ⟨?_, ?_, ?_⟩
    · rw [(hspec t htI).1, (hspec s hsI).1, sub_self]
      exact Matrix.PosSemidef.zero
    · rw [(hspec t htI).2, (hspec s hsI).2]
      exact sphereTrain_mono hwanti hlog.le
    · intro heq
      have hν : (D s).ν = (D t).ν := congrArg Prod.snd heq
      rw [(hspec t htI).2, (hspec s hsI).2] at hν
      have h1 := congrArg (fun m => m {x : Rd d | ‖x‖ = h * q ^ i₀}) hν
      simp only [sphereTrain_sphere hd hq hh] at h1
      have hlt : dgWeight w (Real.logb q s) i₀ < dgWeight w (Real.logb q t) i₀ := by
        unfold dgWeight
        nlinarith
      have h2 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (dgWeight_nonneg hw0 (logb_mem_Icc hq hsI) i₀)).2 hlt
      rw [h1] at h2
      exact lt_irrefl _ h2
  · have h1I : (1 : ℝ) ∈ Icc (1 : ℝ) q := ⟨le_rfl, hq.le⟩
    have hqI : q ∈ Icc (1 : ℝ) q := ⟨hq.le, le_rfl⟩
    refine ⟨?_, ?_⟩
    · rw [(hspec q hqI).1, (hspec 1 h1I).1, smul_zero]
    · rw [(hspec q hqI).2, (hspec 1 h1I).2, Real.logb_self_eq_one hq, Real.logb_one]
      exact sphereTrain_one hq w

/-- **`prop:stratum-two-example`, the family.** The family of `lem:synthesis` on these data is an
isotropic `q`-covariant family with `S_q t = qt`; it is not `λ`-covariant for every `λ > 0`; and
its kernels `μ_t`, `t > 0`, are carried by no discrete subgroup of `ℝ^d`. -/
theorem stratum_two_example (hd : 1 ≤ d) {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : Antitone w) (hwne : ∃ i, w i ≠ 0)
    (hneg : Summable fun i : {i : ℤ // i < 0} => w i * q ^ (2 * (i : ℤ)))
    (hpos : Summable fun i : {i : ℤ // 0 ≤ i} => w i) (D : ℝ → SymLevyData d)
    (hDspec : ∀ t ∈ Icc (1 : ℝ) q,
      (D t).A = 0 ∧ (D t).ν = sphereTrain d q h w (Real.logb q t)) :
    (∃ μ : ℝ → ℝ → Measure (Rd d), IsExponentLaws (octaveExponent q D) μ) ∧
      ∀ μ : ℝ → ℝ → Measure (Rd d), IsExponentLaws (octaveExponent q D) μ →
        IsIsotropicFamily μ ∧ IsCovariantAt μ q (fun t => q * t) ∧ ¬ IsFullyCovariantLaws μ ∧
          ∀ t : ℝ, 0 < t → ∀ Γ : AddSubgroup (Rd d), DiscreteTopology Γ →
            μ 0 t (Γ : Set (Rd d))ᶜ ≠ 0 := by
  have hq0 : 0 < q := by linarith
  have hsyn : IsSynthesisData q D :=
    (stratum_two_example_data hd hq hh w hw0 hwanti hwne hneg hpos).2 D hDspec
  obtain ⟨-, hex, hfam⟩ := synthesis hq D hsyn
  refine ⟨hex, fun μ hμ => ?_⟩
  obtain ⟨hsym, hcov⟩ := hfam μ hμ
  -- the exponents are invariant under `O(d)`
  have hrotΨ : ∀ (t : ℝ) {Q : Mat d}, Q ∈ orthSet d → ∀ ω : Rd d,
      octaveExponent q D t (lin Qᵀ ω) = octaveExponent q D t ω := by
    intro t Q hQ ω
    rw [← octaveData_exponent hq, ← octaveData_exponent hq]
    rcases le_or_gt t 0 with ht | ht
    · rw [octaveData_of_nonpos q D ht, SymLevyData.zero_exponent, SymLevyData.zero_exponent]
    · rw [octaveData, dif_pos ⟨ht, hq0.ne'⟩, SymLevyData.dilate_exponent,
        SymLevyData.dilate_exponent, ← ContinuousLinearMap.map_smul]
      have hu := Ico_subset_Icc_self (octave_mem hq ht)
      exact trainData_exponent_orth (hDspec _ hu).1 (hDspec _ hu).2 hQ _
  refine ⟨⟨⟨hsym.1, hsym.2.1⟩, fun s t hs hst Q hQ => ?_⟩, hcov, ?_, fun t ht Γ hΓ => ?_⟩
  · -- (I3)
    obtain ⟨hp, hc⟩ := hμ s t hs hst
    haveI := hp
    haveI : IsProbabilityMeasure (push Q (μ s t)) :=
      Measure.isProbabilityMeasure_map (lin Q).continuous.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [push, charFun_map_lin, hc, hc, hrotΨ t hQ, hrotΨ s hQ]
  · -- not fully covariant: the kernel at `1` would be self-decomposable
    intro hfull
    haveI := hsym.1.isProbability 0 1 le_rfl zero_le_one
    have hsd : IsSelfDecomposableSato (μ 0 1) := by
      intro b hb
      obtain ⟨S, hS⟩ := hfull b (by linarith)
      obtain ⟨-, hlt⟩ := family_dilations_1 hd μ hsym S S hS hS
      obtain ⟨u, hu0, hSu⟩ := hS.1.surjOn (show (1 : ℝ) ∈ Ici (0 : ℝ) from mem_Ici.2 zero_le_one)
      have hu0' : (0 : ℝ) ≤ u := hu0
      have hS0 : S 0 = 0 := incBij_zero hS.1
      have hupos : 0 < u := by
        rcases hu0'.eq_or_lt with h0 | h0
        · rw [← h0, hS0] at hSu
          exact absurd hSu zero_ne_one
        · exact h0
      have hu1 : u < 1 := by
        have := hlt hb u hupos
        rwa [hSu] at this
      refine ⟨μ u 1, hsym.1.isProbability u 1 hu0' hu1.le, fun z => ?_⟩
      have hcasc := hsym.1.cascade 0 u 1 le_rfl hu0' hu1.le
      have hmap : (μ 0 u).map (fun x => b • x) = μ 0 1 := by
        have := hS.2 0 u le_rfl hu0'
        rwa [hS0, hSu] at this
      have hbz : b • b⁻¹ • z = z := by
        rw [smul_smul, mul_inv_cancel₀ (by linarith), one_smul]
      haveI := hsym.1.isProbability u 1 hu0' hu1.le
      haveI := hsym.1.isProbability 0 u le_rfl hu0'
      conv_lhs => rw [hcasc]
      rw [charFun_conv, ← hmap, charFun_map_smul, hbz, mul_comm]
    -- the data of `μ 0 1`
    have h1I : (1 : ℝ) ∈ Icc (1 : ℝ) q := ⟨le_rfl, hq.le⟩
    have hdata : IsSymData (μ 0 1) (octaveData q D 1) := fun ω => by
      rw [(hμ 0 1 le_rfl zero_le_one).2 ω, octaveExponent_zero_left, sub_zero,
        octaveData_exponent hq]
    have hν1 : (octaveData q D 1).ν = sphereTrain d q h w 0 := by
      have h1 : octaveData q D 1 = octaveData q D (q ^ (0 : ℤ) * 1) := by simp
      rw [h1, octaveData_at hq hsyn 0 h1I]
      change (D 1).ν.map (fun x => q ^ (0 : ℤ) • x) = _
      simp only [zpow_zero, one_smul, Measure.map_id', (hDspec 1 h1I).2, Real.logb_one]
    have hid := (family_structure_id hd μ hsym 0 1 le_rfl zero_le_one).1
    obtain ⟨lam, k, -, -, -, -, hpolar⟩ :=
      (cited_A45 (μ 0 1) hid _ (SymLevyData.hasTriplet hdata)).1 hsd
    obtain ⟨i, hi⟩ := hwne
    have hwi : 0 < w i := lt_of_le_of_ne (hw0 i) (Ne.symm hi)
    set B : Set (Rd d) := {x : Rd d | ‖x‖ = h * q ^ i} with hB
    have hBm : MeasurableSet B := measurableSet_sphere _
    have hlhs := hpolar B hBm
    change (octaveData q D 1).ν B = _ at hlhs
    rw [hν1, show sphereTrain d q h w 0 B = ENNReal.ofReal (dgWeight w 0 i) from
      sphereTrain_sphere hd hq hh w 0 i] at hlhs
    have hzero : ∀ ξ : Metric.sphere (0 : Rd d) 1, (∫⁻ r in Ioi (0 : ℝ),
        B.indicator 1 (r • (ξ : Rd d)) * ENNReal.ofReal (k ξ r / r)) = 0 := by
      intro ξ
      have hξ : ‖(ξ : Rd d)‖ = 1 := mem_sphere_zero_iff_norm.1 ξ.2
      have hne : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ≠ h * q ^ i :=
        ae_restrict_of_ae (Set.Countable.ae_notMem (Set.countable_singleton _) volume)
      have hpos' : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ∈ Ioi (0 : ℝ) :=
        ae_restrict_mem measurableSet_Ioi
      rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) ?_, lintegral_zero]
      filter_upwards [hne, hpos'] with r hr hr0
      have hnot : r • (ξ : Rd d) ∉ B := by
        intro hmem
        have hn : ‖r • (ξ : Rd d)‖ = h * q ^ i := hmem
        rw [norm_smul, hξ, mul_one, Real.norm_of_nonneg (le_of_lt hr0)] at hn
        exact hr hn
      simp [Set.indicator_of_notMem hnot]
    have hR : (∫⁻ ξ, (∫⁻ r in Ioi (0 : ℝ),
        B.indicator 1 (r • (ξ : Rd d)) * ENNReal.ofReal (k ξ r / r)) ∂lam) = 0 := by
      simp only [hzero, lintegral_zero]
    rw [hR] at hlhs
    have hdw : dgWeight w 0 i = w i := by simp [dgWeight]
    rw [hdw] at hlhs
    exact (ENNReal.ofReal_pos.2 hwi).ne' hlhs
  · haveI := hΓ
    exact no_lattice_kernel hd μ hsym hq ⟨_, hcov⟩ ht Γ

end Pyramids
