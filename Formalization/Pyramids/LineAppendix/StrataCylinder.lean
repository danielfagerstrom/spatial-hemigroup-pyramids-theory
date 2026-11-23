/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.KnotCascades
import Pyramids.LineAppendix.PhaseDisintegration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# `prop:strata-cylinder-coordinates`, part A: the Haar measures, (2), the integrability

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:strata-cylinder-coordinates`. Wave 3c: the
declarations `strata_cylinder_2` and `strata_cylinder_1_integrability` moved here from
`PyramidsSkeleton.ChA1Line`, unchanged in statement. The node's other declarations are in
`StrataCylinderParts.lean` (the Gaussian part, both parts, "then") and in the skeleton (the
jump part's equivalences and (3)).

## The route

* **The Haar measures.** `dy/(ℓy)` on `(0,∞)` is invariant under every dilation
  (`lintegral_logHaar_comp_mul`), and `η` is its restriction to `[1,q)`
  (`haarPhase_eq_restrict`), a probability measure (`isProbabilityMeasure_haarPhase`).
* **Unfolding the orbits.** For a measurable `G ≥ 0` on `ℝ`,
  `∫_{[1,q)} ∑ₙ G(θqⁿ) η(dθ) = ∫ G(y) dy/(ℓy)` (`lintegral_haarPhase_tsum_zpow`): the dilation by
  `qⁿ` carries `[1,q)` onto `[qⁿ, qⁿ⁺¹)`, these intervals partition `(0,∞)`, and `dy/(ℓy)` does not
  see the dilation. This is the substitution `u = θqⁿ` of the proof of record, and it is the step
  the jump part's "then" clause reads as well.
* **(2).** With `G(u) = 𝟙_{u ≤ t}(1 - cos ωru)` the unfolding gives
  `ℓ⁻¹∫₀ᵗ (1 - cos ωru) du/u`, which is `ℓ⁻¹Cin(ωrt)` by the shared core's
  `intervalIntegral_dilate_cinIntegrand`.
* **The integrability.** For `θ ∈ [1,q)` and `r ≥ 0`, `w(r) ≤ w(rθ) ≤ max(q², 1 + ℓ) w(r)`
  (`cylWeight_mono`, `cylWeight_mul_le`), and `η` has mass `1`; so (A.e3) for `η ⊗ ρ̃` is
  `∫ w dρ̃ < ∞`. By Tonelli, `∫ (1 ∧ x²) ρ̃([x,∞)) dx/x = ∫ g dρ̃` with
  `g(r) = ∫₀ʳ (1 ∧ x²) dx/x = (r ∧ 1)²/2 + log(r ∨ 1)`, and `w/2 ≤ g ≤ w` on `(0,∞)`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (cin)
open scoped ENNReal NNReal

/-! ## Dilations of Lebesgue measure and of `dy/(ℓy)` -/

/-- `∫⁻ f(cy) dy = c⁻¹ ∫⁻ f` for `c > 0`. -/
theorem lintegral_comp_const_mul {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ≥0∞) :
    ∫⁻ y, f (c * y) = ENNReal.ofReal c⁻¹ * ∫⁻ u, f u := by
  set e := (Homeomorph.mulLeft₀ c hc.ne').toMeasurableEquiv with he
  have h1 : ∫⁻ y, f (c * y) = ∫⁻ y, f (e y) := rfl
  have hmap : Measure.map e (volume : Measure ℝ) = ENNReal.ofReal |c⁻¹| • volume :=
    Real.map_volume_mul_left hc.ne'
  rw [h1, ← lintegral_map_equiv f e, hmap, lintegral_smul_measure, abs_of_pos (inv_pos.2 hc),
    smul_eq_mul]

/-- `∫⁻ G d(dy/(ℓy)) = ∫⁻_{(0,∞)} G(y)/(ℓy) dy`. -/
theorem lintegral_logHaar (q : ℝ) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y, G y ∂(logHaar q) = ∫⁻ y in Ioi 0, ENNReal.ofReal (1 / (Real.log q * y)) * G y := by
  rw [logHaar, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hG]
  rfl

/-- **`dy/(ℓy)` is invariant under every dilation**: `∫ G(cy) dy/(ℓy) = ∫ G(y) dy/(ℓy)`. -/
theorem lintegral_logHaar_comp_mul (q : ℝ) {c : ℝ} (hc : 0 < c) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) : ∫⁻ y, G (c * y) ∂(logHaar q) = ∫⁻ y, G y ∂(logHaar q) := by
  rw [lintegral_logHaar q
      (show Measurable fun y => G (c * y) from hG.comp (measurable_const_mul c)),
    lintegral_logHaar q hG,
    ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  set F : ℝ → ℝ≥0∞ := (Ioi (0 : ℝ)).indicator
    (fun u => ENNReal.ofReal (1 / (Real.log q * u)) * G u) with hF
  have e : ∀ y : ℝ, (Ioi (0 : ℝ)).indicator
      (fun y => ENNReal.ofReal (1 / (Real.log q * y)) * G (c * y)) y =
        ENNReal.ofReal c * F (c * y) := by
    intro y
    rw [hF]
    by_cases hy : 0 < y
    · have hcy : 0 < c * y := mul_pos hc hy
      rw [indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy),
        indicator_of_mem (show c * y ∈ Ioi (0 : ℝ) from hcy), ← mul_assoc,
        ← ENNReal.ofReal_mul hc.le]
      congr 2
      field_simp
    · have hcy : ¬ 0 < c * y := fun h => hy (pos_of_mul_pos_right h hc.le)
      rw [indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy),
        indicator_of_notMem (show c * y ∉ Ioi (0 : ℝ) from hcy), mul_zero]
  simp_rw [e]
  rw [lintegral_comp_const_mul hc (fun u => ENNReal.ofReal c * F u),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity),
    inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

theorem measurable_logHaar_density (q : ℝ) :
    Measurable fun y : ℝ => ENNReal.ofReal (1 / (Real.log q * y)) := by fun_prop

/-- `η` is `dy/(ℓy)` restricted to `[1,q)`. -/
theorem haarPhase_eq_restrict {q : ℝ} : haarPhase q = (logHaar q).restrict (Ico 1 q) := by
  rw [logHaar, restrict_withDensity measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
    (inter_eq_left (s := Ico 1 q) (t := Ioi (0 : ℝ))).2
      (fun y hy => show (0 : ℝ) < y from lt_of_lt_of_le one_pos hy.1), haarPhase]

/-- `dy/(ℓy)` is null on `(-∞,0]`. -/
theorem logHaar_Iic (q : ℝ) : logHaar q (Iic 0) = 0 := by
  have h : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
    exact id
  rw [logHaar, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    h, Measure.restrict_empty, lintegral_zero_measure]

/-- **`η` is a probability measure**: `∫₁^q dθ/(ℓθ) = 1`. -/
theorem isProbabilityMeasure_haarPhase {q : ℝ} (hq : 1 < q) :
    IsProbabilityMeasure (haarPhase q) := by
  have hl : 0 < Real.log q := Real.log_pos hq
  constructor
  have hint : IntegrableOn (fun θ : ℝ => 1 / (Real.log q * θ)) (Icc 1 q) := by
    refine ContinuousOn.integrableOn_Icc (fun θ hθ => ?_)
    have : (Real.log q * θ) ≠ 0 := (mul_pos hl (lt_of_lt_of_le one_pos hθ.1)).ne'
    exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id) this).continuousWithinAt
  rw [haarPhase, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    setLIntegral_congr Ico_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal
      (hint.mono_set Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall fun θ hθ =>
        (one_div_pos.2 (mul_pos hl (lt_trans one_pos hθ.1))).le)),
    ← intervalIntegral.integral_of_le hq.le]
  simp_rw [one_div, mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (by linarith), div_one,
    inv_mul_cancel₀ hl.ne', ENNReal.ofReal_one]

instance {q : ℝ} : SFinite (logHaar q) := by rw [logHaar]; infer_instance

instance {q : ℝ} : SFinite (haarPhase q) := by rw [haarPhase]; infer_instance

/-! ## Unfolding the orbits -/

/-- **`∫_{[1,q)} ∑ₙ G(θqⁿ) η(dθ) = ∫ G(y) dy/(ℓy)`** for every measurable `G ≥ 0`: the
substitution `u = θqⁿ` on each `[qⁿ, qⁿ⁺¹)`, glued over `n ∈ ℤ`. -/
theorem lintegral_haarPhase_tsum_zpow {q : ℝ} (hq : 1 < q) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ θ, ∑' n : ℤ, G (θ * q ^ n) ∂(haarPhase q) = ∫⁻ y, G y ∂(logHaar q) := by
  have hq0 : 0 < q := by linarith
  rw [lintegral_tsum fun (n : ℤ) =>
    (show Measurable fun θ => G (θ * q ^ n) from hG.comp (measurable_mul_const _)).aemeasurable]
  have hterm : ∀ n : ℤ, ∫⁻ θ, G (θ * q ^ n) ∂(haarPhase q) =
      ∫⁻ y in Ico (q ^ n) (q ^ (n + 1)), G y ∂(logHaar q) := by
    intro n
    have hqn : 0 < q ^ n := zpow_pos hq0 n
    rw [haarPhase_eq_restrict, ← lintegral_indicator measurableSet_Ico,
      ← lintegral_indicator measurableSet_Ico]
    have e : ∀ θ : ℝ, (Ico 1 q).indicator (fun θ => G (θ * q ^ n)) θ =
        (Ico (q ^ n) (q ^ (n + 1))).indicator G (q ^ n * θ) := by
      intro θ
      have hiff : θ ∈ Ico 1 q ↔ q ^ n * θ ∈ Ico (q ^ n) (q ^ (n + 1)) := by
        rw [zpow_add_one₀ hq0.ne', mem_Ico, mem_Ico]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨le_mul_of_one_le_right hqn.le h1, mul_lt_mul_of_pos_left h2 hqn⟩
        · rintro ⟨h1, h2⟩
          exact ⟨le_of_mul_le_mul_left (by rwa [mul_one]) hqn, lt_of_mul_lt_mul_left h2 hqn.le⟩
      by_cases h : θ ∈ Ico 1 q
      · rw [indicator_of_mem h, indicator_of_mem (hiff.1 h), mul_comm]
      · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hiff.2 h'))]
    simp_rw [e]
    exact lintegral_logHaar_comp_mul q hqn (hG.indicator measurableSet_Ico)
  simp_rw [hterm]
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℤ => Ico (q ^ n) (q ^ (n + 1))) := by
    intro m n hmn
    refine Set.disjoint_left.2 fun y hm hn => hmn ?_
    rcases lt_trichotomy m n with h | h | h
    · exfalso
      have := zpow_le_zpow_right₀ hq.le (show m + 1 ≤ n by omega)
      linarith [hm.2, hn.1]
    · exact h
    · exfalso
      have := zpow_le_zpow_right₀ hq.le (show n + 1 ≤ m by omega)
      linarith [hm.1, hn.2]
  rw [← lintegral_iUnion (fun n => measurableSet_Ico) hdisj]
  have hU : (⋃ n : ℤ, Ico (q ^ n) (q ^ (n + 1))) = Ioi 0 := by
    ext y
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_of_lt_of_le (zpow_pos hq0 n) hn.1
    · intro hy
      exact exists_mem_Ico_zpow hy hq
  rw [hU, Measure.restrict_eq_self_of_ae_mem]
  rw [ae_iff]
  convert logHaar_Iic q using 2
  ext y
  simp

/-- `η`-almost every phase lies in `[1,q)`. -/
theorem ae_haarPhase_mem (q : ℝ) : ∀ᵐ θ ∂(haarPhase q), θ ∈ Ico 1 q := by
  rw [haarPhase_eq_restrict]
  exact ae_restrict_mem measurableSet_Ico

/-! ## (2), circle averaging -/

theorem knotAtomCascade_nonneg (q θ r t ω : ℝ) : 0 ≤ knotAtomCascade q θ r t ω :=
  tsum_nonneg fun n => by split_ifs <;> linarith [Real.cos_le_one (ω * (r * θ * q ^ n))]

/-- The orbit sum of the cascade: `Ψ^{(θ,r)}_t(ω) = ∑ₙ G(θqⁿ)` with
`G(u) = 𝟙_{u ≤ t}(1 - cos ωru)`, for `θ ∈ [1,q)`. -/
theorem ofReal_knotAtomCascade {q : ℝ} (hq : 1 < q) {θ r : ℝ} (hθr : (θ, r) ∈ cylinder q)
    (t ω : ℝ) :
    ENNReal.ofReal (knotAtomCascade q θ r t ω) = ∑' n : ℤ,
      (fun u : ℝ => if u ≤ t then ENNReal.ofReal (1 - Real.cos (ω * (r * u))) else 0)
        (θ * q ^ n) := by
  have hnn : ∀ n : ℤ, 0 ≤ (if θ * q ^ n ≤ t then 1 - Real.cos (ω * (r * θ * q ^ n)) else 0) :=
    fun n => by split_ifs <;> linarith [Real.cos_le_one (ω * (r * θ * q ^ n))]
  rw [knotAtomCascade, ENNReal.ofReal_tsum_of_nonneg hnn (knot_summable hq hθr t ω)]
  refine tsum_congr fun n => ?_
  by_cases h : θ * q ^ n ≤ t
  · simp only [if_pos h, mul_assoc]
  · simp only [if_neg h, ENNReal.ofReal_zero]

/-- **`prop:strata-cylinder-coordinates`(2), circle averaging (A.e5).** The circle average of a
knot-atom cascade is a Cin ray: `∫_{[1,q)} Ψ^{(θ,r)}_t(ω) η(dθ) = ℓ⁻¹ Cin(ωrt)`. -/
theorem strata_cylinder_2 {q : ℝ} (hq : 1 < q) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (ω : ℝ) :
    ∫ θ, knotAtomCascade q θ r t ω ∂(haarPhase q) = cin (ω * r * t) / Real.log q := by
  have hl : 0 < Real.log q := Real.log_pos hq
  set G : ℝ → ℝ≥0∞ := fun u => if u ≤ t then ENNReal.ofReal (1 - Real.cos (ω * (r * u))) else 0
    with hG
  have hGm : Measurable G := Measurable.ite measurableSet_Iic (by fun_prop) measurable_const
  have hK : ∀ᵐ θ ∂(haarPhase q),
      ENNReal.ofReal (knotAtomCascade q θ r t ω) = ∑' n : ℤ, G (θ * q ^ n) := by
    filter_upwards [ae_haarPhase_mem q] with θ hθ
    exact ofReal_knotAtomCascade hq ⟨hθ, hr⟩ t ω
  have hmeas : AEStronglyMeasurable (fun θ => knotAtomCascade q θ r t ω) (haarPhase q) := by
    have hm : Measurable fun θ => ∑' n : ℤ, G (θ * q ^ n) :=
      Measurable.tsum fun n => hGm.comp (measurable_mul_const _)
    refine hm.ennreal_toReal.aestronglyMeasurable.congr ?_
    filter_upwards [hK] with θ hθ
    rw [← hθ, ENNReal.toReal_ofReal (knotAtomCascade_nonneg q θ r t ω)]
  -- the integral against `dy/(ℓy)`
  have hint : IntegrableOn (fun y => (1 - Real.cos (ω * r * y)) / y / Real.log q) (Ioc 0 t) := by
    have := (ScaleSpace.intervalIntegrable_dilate_cinIntegrand (ω * r) ht.le).div_const
      (Real.log q)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).1 this
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 t)]
      fun y => (1 - Real.cos (ω * r * y)) / y / Real.log q :=
    (ae_restrict_iff' measurableSet_Ioc).2 (.of_forall fun y hy =>
      div_nonneg (div_nonneg (sub_nonneg.2 (Real.cos_le_one _)) hy.1.le) hl.le)
  have e : ∀ y : ℝ, (Ioi (0 : ℝ)).indicator
      (fun y => ENNReal.ofReal (1 / (Real.log q * y)) * G y) y =
        (Ioc 0 t).indicator
          (fun y => ENNReal.ofReal ((1 - Real.cos (ω * r * y)) / y / Real.log q)) y := by
    intro y
    by_cases hy : 0 < y
    · rw [indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy), hG]
      by_cases hyt : y ≤ t
      · simp only [if_pos hyt]
        rw [indicator_of_mem (show y ∈ Ioc 0 t from ⟨hy, hyt⟩),
          ← ENNReal.ofReal_mul (one_div_pos.2 (mul_pos hl hy)).le, ← mul_assoc ω r y]
        congr 1
        field_simp
      · simp only [if_neg hyt, mul_zero]
        rw [indicator_of_notMem (fun h => hyt h.2)]
    · rw [indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy),
        indicator_of_notMem (fun h => hy h.1)]
  have hlin : ∫⁻ y, G y ∂(logHaar q) = ENNReal.ofReal (cin (ω * r * t) / Real.log q) := by
    rw [lintegral_logHaar q hGm, ← lintegral_indicator measurableSet_Ioi]
    simp_rw [e]
    rw [lintegral_indicator measurableSet_Ioc, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
      ← intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_div,
      ScaleSpace.intervalIntegral_dilate_cinIntegrand]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun θ => knotAtomCascade_nonneg q θ r t ω)
      hmeas, lintegral_congr_ae hK, lintegral_haarPhase_tsum_zpow hq hGm, hlin,
    ENNReal.toReal_ofReal (div_nonneg (ScaleSpace.cin_nonneg' _) hl.le)]

/-! ## (1), the integrability -/

/-- A measure null on `(-∞,0]` is carried by `(0,∞)`. -/
theorem ae_pos_of_Iic_zero {ρ : Measure ℝ} (h : ρ (Iic 0) = 0) : ∀ᵐ r ∂ρ, 0 < r := by
  rw [ae_iff]
  convert h using 2
  ext r
  simp

/-- **`w(rθ) ≤ max(q², 1 + ℓ) w(r)`** for `θ ∈ [1,q)`. -/
theorem cylWeight_mul_le {q : ℝ} (hq : 1 < q) {θ r : ℝ} (hθ : θ ∈ Ico 1 q) :
    cylWeight (r * θ) ≤ max (q ^ 2) (1 + Real.log q) * cylWeight r := by
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
  have h1 : cylWeight (r * θ) ≤ q ^ 2 * r ^ 2 := by
    refine (min_le_left _ _).trans ?_
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hθ0.le hθ.2.le 2) (sq_nonneg r)
  have h2 : cylWeight (r * θ) ≤ (1 + Real.log q) * (1 + Real.posLog r) := by
    refine (min_le_right _ _).trans ?_
    have hpl : Real.posLog θ ≤ Real.log q := by
      rw [Real.posLog_eq_log (by rw [abs_of_pos hθ0]; exact hθ.1)]
      exact Real.log_le_log hθ0 hθ.2.le
    have hm := Real.posLog_mul (x := r) (y := θ)
    have hl : 0 ≤ Real.log q := (Real.log_pos hq).le
    nlinarith [Real.posLog_nonneg (x := r)]
  have hw : cylWeight r = min (r ^ 2) (1 + Real.posLog r) := rfl
  rw [hw]
  rcases le_total (r ^ 2) (1 + Real.posLog r) with h | h
  · rw [min_eq_left h]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg r))
  · rw [min_eq_right h]
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (add_nonneg zero_le_one Real.posLog_nonneg))

/-- **The fibre integral of the weight**: `w(r) ≤ ∫ w(rθ) η(dθ) ≤ max(q², 1 + ℓ) w(r)`. -/
theorem lintegral_haarPhase_cylWeight {q : ℝ} (hq : 1 < q) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (cylWeight r) ≤ ∫⁻ θ, ENNReal.ofReal (cylWeight (r * θ)) ∂(haarPhase q) ∧
      ∫⁻ θ, ENNReal.ofReal (cylWeight (r * θ)) ∂(haarPhase q) ≤
        ENNReal.ofReal (max (q ^ 2) (1 + Real.log q)) * ENNReal.ofReal (cylWeight r) := by
  haveI := isProbabilityMeasure_haarPhase hq
  constructor
  · calc ENNReal.ofReal (cylWeight r) = ∫⁻ _, ENNReal.ofReal (cylWeight r) ∂(haarPhase q) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_haarPhase_mem q] with θ hθ
          exact ENNReal.ofReal_le_ofReal (cylWeight_mono hr (le_mul_of_one_le_right hr hθ.1))
  · calc ∫⁻ θ, ENNReal.ofReal (cylWeight (r * θ)) ∂(haarPhase q)
        ≤ ∫⁻ _, ENNReal.ofReal (max (q ^ 2) (1 + Real.log q)) * ENNReal.ofReal (cylWeight r)
            ∂(haarPhase q) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_haarPhase_mem q] with θ hθ
          rw [← ENNReal.ofReal_mul (le_trans (sq_nonneg q) (le_max_left _ _))]
          exact ENNReal.ofReal_le_ofReal (cylWeight_mul_le hq hθ)
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- (A.e3) for `η ⊗ ρ̃` is `∫ w dρ̃ < ∞`. -/
theorem isCylIntegrable_prod_iff {q : ℝ} (hq : 1 < q) (ρ : Measure ℝ) [SFinite ρ]
    (hρ0 : ρ (Iic 0) = 0) :
    IsCylIntegrable ((haarPhase q).prod ρ) ↔ ∫⁻ r, ENNReal.ofReal (cylWeight r) ∂ρ ≠ ⊤ := by
  have hm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (cylWeight (p.2 * p.1)) :=
    (measurable_cylWeight.comp (measurable_snd.mul measurable_fst)).ennreal_ofReal
  rw [IsCylIntegrable, lintegral_prod_symm _ hm.aemeasurable]
  have hlow : ∫⁻ r, ENNReal.ofReal (cylWeight r) ∂ρ ≤
      ∫⁻ r, ∫⁻ θ, ENNReal.ofReal (cylWeight (r * θ)) ∂(haarPhase q) ∂ρ := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_pos_of_Iic_zero hρ0] with r hr
    exact (lintegral_haarPhase_cylWeight hq hr.le).1
  have hup : ∫⁻ r, ∫⁻ θ, ENNReal.ofReal (cylWeight (r * θ)) ∂(haarPhase q) ∂ρ ≤
      ENNReal.ofReal (max (q ^ 2) (1 + Real.log q)) * ∫⁻ r, ENNReal.ofReal (cylWeight r) ∂ρ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_pos_of_Iic_zero hρ0] with r hr
    exact (lintegral_haarPhase_cylWeight hq hr.le).2
  exact ⟨fun h => ne_top_of_le_ne_top h hlow,
    fun h => ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h) hup⟩

/-- **`g(r) = ∫₀ʳ (1 ∧ x²) dx/x`**: `r²/2` for `r ≤ 1`, `1/2 + log r` for `r > 1`. -/
theorem lintegral_min_one_sq_div {r : ℝ} (hr : 0 < r) :
    ∫⁻ x in Ioc 0 r, ENNReal.ofReal (min 1 (x ^ 2) / x) =
      ENNReal.ofReal (if r ≤ 1 then r ^ 2 / 2 else 1 / 2 + Real.log r) := by
  have hsmall : ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∫⁻ x in Ioc 0 s, ENNReal.ofReal (min 1 (x ^ 2) / x) = ENNReal.ofReal (s ^ 2 / 2) := by
    intro s hs hs1
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun x => ENNReal.ofReal x)
      (fun x hx => by
        rw [min_eq_right (by nlinarith [hx.1, hx.2] : x ^ 2 ≤ 1), sq,
          mul_div_cancel_right₀ _ hx.1.ne'])]
    have hI : IntegrableOn (fun x : ℝ => x) (Ioc 0 s) :=
      (continuous_id.integrableOn_Icc (a := 0) (b := s)).mono_set Ioc_subset_Icc_self
    have e : ENNReal.ofReal (∫ x in Ioc 0 s, x) = ∫⁻ x in Ioc 0 s, ENNReal.ofReal x :=
      ofReal_integral_eq_lintegral_ofReal hI
        ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall fun x hx => hx.1.le))
    rw [← e, ← intervalIntegral.integral_of_le hs.le, integral_id]
    congr 1
    ring
  split_ifs with h1
  · exact hsmall r hr h1
  · have h1' : 1 < r := lt_of_not_ge h1
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one h1'.le,
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl), hsmall 1 one_pos le_rfl,
      setLIntegral_congr_fun measurableSet_Ioc (g := fun x => ENNReal.ofReal x⁻¹)
        (fun x hx => by
          rw [min_eq_left (by nlinarith [hx.1, hx.2] : (1 : ℝ) ≤ x ^ 2), one_div])]
    have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Icc 1 r) :=
      continuousOn_inv₀.mono fun x hx => (lt_of_lt_of_le one_pos hx.1).ne'
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall fun x hx =>
        (inv_pos.2 (lt_trans one_pos hx.1)).le)),
      ← intervalIntegral.integral_of_le h1'.le, integral_inv_of_pos one_pos (by linarith), div_one,
      ← ENNReal.ofReal_add (by norm_num) (Real.log_nonneg h1'.le)]
    norm_num

/-- **`w/2 ≤ g ≤ w`** on `(0,∞)`. -/
theorem cylWeight_le_two_mul_g {r : ℝ} (hr : 0 < r) :
    cylWeight r ≤ 2 * (if r ≤ 1 then r ^ 2 / 2 else 1 / 2 + Real.log r) ∧
      (if r ≤ 1 then r ^ 2 / 2 else 1 / 2 + Real.log r) ≤ cylWeight r := by
  have hw : cylWeight r = min (r ^ 2) (1 + Real.posLog r) := rfl
  rw [hw]
  split_ifs with h1
  · have hp : Real.posLog r = 0 := by
      rw [Real.posLog_eq_zero_iff, abs_of_pos hr]
      exact h1
    rw [hp, add_zero, min_eq_left (by nlinarith)]
    constructor <;> nlinarith [sq_nonneg r]
  · have h1' : 1 < r := lt_of_not_ge h1
    have hp : Real.posLog r = Real.log r :=
      Real.posLog_eq_log (by rw [abs_of_pos hr]; exact h1'.le)
    have hlog0 : 0 ≤ Real.log r := Real.log_nonneg h1'.le
    have hlog1 : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr
    rw [hp]
    constructor
    · exact (min_le_right _ _).trans (by linarith)
    · exact le_min (by nlinarith) (by linarith)

/-- **`prop:strata-cylinder-coordinates`(1), the integrability.** For a measure `ρ̃` on `(0,∞)`,
(A.e3) for `η ⊗ ρ̃` is equivalent to `∫ (r² ∧ (1 + log₊ r)) ρ̃(dr) < ∞` and to
`∫ (1 ∧ x²) k(x) dx/x < ∞`, `k(x) = ℓ⁻¹ ρ̃([x,∞))` (read in `[0,∞]`). Typed for every s-finite
`ρ̃`: the node's `ρ̃` is σ-finite, and `η ⊗ ρ̃` is the product measure (Tonelli) only for s-finite
`ρ̃`. -/
theorem strata_cylinder_1_integrability {q : ℝ} (hq : 1 < q) (ρ : Measure ℝ) [SFinite ρ]
    (hρ0 : ρ (Iic 0) = 0) :
    (IsCylIntegrable ((haarPhase q).prod ρ) ↔ ∫⁻ r, ENNReal.ofReal (cylWeight r) ∂ρ ≠ ⊤) ∧
      (IsCylIntegrable ((haarPhase q).prod ρ) ↔
        ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) / x) *
          (ρ (Ici x) / ENNReal.ofReal (Real.log q)) ≠ ⊤) := by
  have hl : 0 < Real.log q := Real.log_pos hq
  refine ⟨isCylIntegrable_prod_iff hq ρ hρ0, (isCylIntegrable_prod_iff hq ρ hρ0).trans ?_⟩
  set c : ℝ≥0∞ := (ENNReal.ofReal (Real.log q))⁻¹ with hc
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hct : c ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hl).ne'
  set h : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (min 1 (x ^ 2) / x) with hh
  have hhm : Measurable h := by fun_prop
  -- pull out `ℓ⁻¹`
  have e1 : ∫⁻ x in Ioi (0 : ℝ), h x * (ρ (Ici x) / ENNReal.ofReal (Real.log q)) =
      (∫⁻ x in Ioi (0 : ℝ), h x * ρ (Ici x)) * c := by
    simp_rw [div_eq_mul_inv, ← mul_assoc]
    rw [lintegral_mul_const' _ _ hct]
  -- Tonelli
  set F : ℝ → ℝ → ℝ≥0∞ := fun x r => if x ≤ r then h x else 0 with hF
  have hFm : Measurable (Function.uncurry F) :=
    Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      (hhm.comp measurable_fst) measurable_const
  have e2 : ∫⁻ x in Ioi (0 : ℝ), h x * ρ (Ici x) =
      ∫⁻ r, (∫⁻ x in Ioi (0 : ℝ), F x r) ∂ρ := by
    rw [← lintegral_lintegral_swap hFm.aemeasurable]
    refine lintegral_congr fun x => ?_
    rw [← lintegral_indicator_const measurableSet_Ici]
    refine lintegral_congr fun r => ?_
    simp only [hF, indicator_apply, mem_Ici]
  have e3 : ∀ r : ℝ, 0 < r → ∫⁻ x in Ioi (0 : ℝ), F x r =
      ENNReal.ofReal (if r ≤ 1 then r ^ 2 / 2 else 1 / 2 + Real.log r) := by
    intro r hr
    rw [← lintegral_min_one_sq_div hr, ← lintegral_indicator measurableSet_Ioi,
      ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun x => ?_
    simp only [hF, indicator_apply, mem_Ioi, mem_Ioc]
    by_cases hx : 0 < x <;> by_cases hxr : x ≤ r <;> simp [hx, hxr, hh]
  have hlow : ∫⁻ r, (∫⁻ x in Ioi (0 : ℝ), F x r) ∂ρ ≤ ∫⁻ r, ENNReal.ofReal (cylWeight r) ∂ρ := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_pos_of_Iic_zero hρ0] with r hr
    rw [e3 r hr]
    exact ENNReal.ofReal_le_ofReal (cylWeight_le_two_mul_g hr).2
  have hup : ∫⁻ r, ENNReal.ofReal (cylWeight r) ∂ρ ≤
      2 * ∫⁻ r, (∫⁻ x in Ioi (0 : ℝ), F x r) ∂ρ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_pos_of_Iic_zero hρ0] with r hr
    rw [e3 r hr, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
    exact ENNReal.ofReal_le_ofReal (cylWeight_le_two_mul_g hr).1
  change _ ↔ ∫⁻ x in Ioi (0 : ℝ), h x * (ρ (Ici x) / ENNReal.ofReal (Real.log q)) ≠ ⊤
  rw [e1, e2]
  constructor
  · intro h'
    exact ENNReal.mul_ne_top (ne_top_of_le_ne_top h' hlow) hct
  · intro h'
    have hne : (∫⁻ r, (∫⁻ x in Ioi (0 : ℝ), F x r) ∂ρ) ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.top_mul hc0] at h'
      exact h' rfl
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hne) hup

end Pyramids
