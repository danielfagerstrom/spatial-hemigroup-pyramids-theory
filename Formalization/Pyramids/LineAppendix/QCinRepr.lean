/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.LineExponentData

/-!
# `prop:strata-cylinder-coordinates-q-cin`(1): the cone `𝒦_q` and its representation

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:strata-cylinder-coordinates-q-cin`. Wave 3a:
`qcin_1_cone` and `qcin_1_repr` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in statement
and name. The extreme rays are `QCinRays.lean`.

## The route

* **The spread.** For a measure `κ` on `(0,∞)`, `∑_{i ≥ 0} T_{q^{-i}} κ` is `qSpread q κ`. Against a
  measurable `f ≥ 0` it integrates as `∫ ∑_i f(τq^{-i}) κ(dτ)` (`lintegral_qSpread`), so
  `∫ E^{(q)}_τ(ω) κ(dτ) = ∫ (1 - cos ωv) (qSpread q κ)(dv)` (`lintegral_qCinRay_eq`). It satisfies
  `qSpread κ = κ + T_{q^{-1}} qSpread κ` (`qSpread_eq_add_map`) and `qSpread κ ≤ T_q qSpread κ`
  (`qSpread_le_map`). The `q`-Cin atoms are the spread of `δ_τ`.
* **Existence.** For `ψ ∈ 𝒦_q` with data `(a, ϖ)`, `T_{q^{-1}}ϖ ≤ ϖ`, and `κ` is the difference
  `ϖ - T_{q^{-1}}ϖ` (`SymLevyPair_exists_sub`). Iterating, `ϖ(A) = ∑_{i<n} κ(q^iA) + ϖ(q^nA)`, and
  the last term tends to `0` for `A ⊆ (ε,∞)`, `ϖ` being finite there. Two measures null on
  `(-∞,0]` that agree on the sets bounded away from `0` are equal (`measure_ext_of_Ioi`).
* **Uniqueness.** A representation `(a', κ')` gives the pair `(a', qSpread κ')` once the spread is
  a Lévy measure. That is proved by averaging `1 - cos ωv` over `ω ∈ (0,2]`
  (`levy_integrable_of_cos_le`), which needs Tonelli, hence `κ'` σ-finite: it is, as
  `E^{(q)}_τ(1) > 0` for `τ > 0` and `∫ E^{(q)}_τ(1) κ'(dτ) ≤ ψ(1) < ∞`. Then
  `lem:line-exponent-data`(1) gives `a' = a` and `qSpread κ' = ϖ`, and `κ'` is recovered from
  `qSpread κ' = κ' + T_{q^{-1}} qSpread κ'`, the second term finite on every `(ε,∞)`.

The proof of record reaches the same representation through the octave components of `ϖ`; the
difference `ϖ - T_{q^{-1}}ϖ` is the measure it builds, `κ^{(q)}`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair IsSymLevyExponent)
open scoped Topology ENNReal NNReal

/-! ## Pairs -/

/-- The exponent of a pair is nonnegative. -/
theorem SymLevyPair_exponent_nonneg (P : SymLevyPair) (ω : ℝ) : 0 ≤ P.exponent ω :=
  ENNReal.toReal_nonneg

theorem SymLevyPair_ofReal_exponent (P : SymLevyPair) (ω : ℝ) :
    ENNReal.ofReal (P.exponent ω) = P.exponentL ω :=
  ENNReal.ofReal_toReal (P.exponentL_ne_top ω)

/-- An element of `ND_s` is nonnegative. -/
theorem isSymLevyExponent_nonneg {ψ : ℝ → ℝ} (hψ : IsSymLevyExponent ψ) (ω : ℝ) : 0 ≤ ψ ω := by
  obtain ⟨P, hP⟩ := hψ
  rw [hP ω]
  exact SymLevyPair_exponent_nonneg P ω

/-- **`c(a, ϖ)`** for `c ≥ 0`. -/
noncomputable def SymLevyPair_smul (c : ℝ) (hc : 0 ≤ c) (P : SymLevyPair) : SymLevyPair where
  a := c * P.a
  ν := ENNReal.ofReal c • P.ν
  a_nonneg := mul_nonneg hc P.a_nonneg
  ν_folded := by
    rw [ScaleSpace.IsFolded, Measure.smul_apply, P.ν_folded, smul_zero]
  ν_integrable := by
    rw [lintegral_smul_measure, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top P.ν_integrable

theorem SymLevyPair_smul_exponent (c : ℝ) (hc : 0 ≤ c) (P : SymLevyPair) (ω : ℝ) :
    (SymLevyPair_smul c hc P).exponent ω = c * P.exponent ω := by
  have h : (SymLevyPair_smul c hc P).exponentL ω = ENNReal.ofReal c * P.exponentL ω := by
    simp only [SymLevyPair.exponentL, SymLevyPair_smul, lintegral_smul_measure, smul_eq_mul]
    rw [mul_add, ← ENNReal.ofReal_mul hc, ← mul_assoc]
  simp only [SymLevyPair.exponent, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- **The pair `(1, 0)`**, the data of `ω²`. -/
noncomputable def sqPair : SymLevyPair where
  a := 1
  ν := 0
  a_nonneg := zero_le_one
  ν_folded := by simp [ScaleSpace.IsFolded]
  ν_integrable := by simp

theorem sqPair_exponent (ω : ℝ) : sqPair.exponent ω = ω ^ 2 := by
  simp [SymLevyPair.exponent, SymLevyPair.exponentL, sqPair, sq_nonneg]

/-! ## Measures on `(0,∞)` -/

/-- Two measures null on `(-∞,0]` that agree on the measurable sets bounded away from `0` are
equal. -/
theorem measure_ext_of_Ioi {m m' : Measure ℝ} (h0 : m (Iic 0) = 0) (h0' : m' (Iic 0) = 0)
    (h : ∀ ε : ℝ, 0 < ε → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioi ε → m A = m' A) : m = m' := by
  ext A hA
  have hsplit : ∀ μ : Measure ℝ, μ (Iic 0) = 0 → μ A = μ (A ∩ Ioi 0) := by
    intro μ hμ
    rw [← measure_inter_add_sdiff A (measurableSet_Ioi (a := (0 : ℝ)))]
    have : μ (A \ Ioi 0) = 0 :=
      measure_mono_null (show A \ Ioi 0 ⊆ Iic 0 from fun x hx => mem_Iic.2 (not_lt.1 hx.2)) hμ
    rw [this, add_zero]
  rw [hsplit m h0, hsplit m' h0']
  have hU : A ∩ Ioi 0 = ⋃ n : ℕ, A ∩ Ioi (1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_iUnion]
    constructor
    · rintro ⟨hx, hx0⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx0
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, hn⟩
      exact ⟨hx, lt_trans (by positivity) hn⟩
  have hmono : Monotone fun n : ℕ => A ∩ Ioi (1 / ((n : ℝ) + 1)) := by
    intro n k hnk
    refine inter_subset_inter_right _ (Ioi_subset_Ioi ?_)
    have : (n : ℝ) ≤ k := Nat.cast_le.2 hnk
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [hU, hmono.measure_iUnion, hmono.measure_iUnion]
  exact iSup_congr fun n => h _ (by positivity) _ (hA.inter measurableSet_Ioi) inter_subset_right

/-! ## The spread `∑_{i ≥ 0} T_{q^{-i}} κ` -/

/-- **`∑_{i ≥ 0} T_{q^{-i}} κ`**: the measure `κ` spread over the scales `τq^{-i}`, `i ≥ 0`. -/
noncomputable def qSpread (q : ℝ) (κ : Measure ℝ) : Measure ℝ :=
  Measure.sum fun i : ℕ => κ.map fun x => x / q ^ i

theorem measurable_div_pow (q : ℝ) (i : ℕ) : Measurable fun x : ℝ => x / q ^ i := by fun_prop

theorem qSpread_apply (q : ℝ) (κ : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    qSpread q κ A = ∑' i : ℕ, κ ((fun x => x / q ^ i) ⁻¹' A) := by
  rw [qSpread, Measure.sum_apply _ hA]
  exact tsum_congr fun i => Measure.map_apply (measurable_div_pow q i) hA

theorem lintegral_qSpread (q : ℝ) (κ : Measure ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(qSpread q κ) = ∫⁻ τ, ∑' i : ℕ, f (τ / q ^ i) ∂κ := by
  rw [qSpread, lintegral_sum_measure]
  refine (tsum_congr fun i => lintegral_map hf (measurable_div_pow q i)).trans ?_
  exact (lintegral_tsum fun i => (hf.comp (measurable_div_pow q i)).aemeasurable).symm

/-- The `q`-Cin atoms are the spread of `δ_τ`. -/
theorem qSpread_dirac (q τ : ℝ) : qSpread q (Measure.dirac τ) = qCinAtoms q τ := by
  simp only [qSpread, qCinAtoms, Measure.map_dirac]

theorem qSpread_Iic {q : ℝ} (hq : 0 < q) {κ : Measure ℝ} (hκ : κ (Iic 0) = 0) :
    qSpread q κ (Iic 0) = 0 := by
  rw [qSpread_apply q κ measurableSet_Iic]
  refine ENNReal.tsum_eq_zero.2 fun i => ?_
  have : (fun x : ℝ => x / q ^ i) ⁻¹' Iic 0 = Iic 0 := by
    ext x
    simp only [mem_preimage, mem_Iic]
    rw [div_le_iff₀ (pow_pos hq i), zero_mul]
  rw [this, hκ]

theorem qSpread_mono (q : ℝ) {κ κ' : Measure ℝ} (h : κ ≤ κ') : qSpread q κ ≤ qSpread q κ' := by
  rw [Measure.le_iff]
  intro A hA
  rw [qSpread_apply q κ hA, qSpread_apply q κ' hA]
  exact ENNReal.tsum_le_tsum fun i => Measure.le_iff'.1 h _

theorem qSpread_add (q : ℝ) (κ κ' : Measure ℝ) :
    qSpread q (κ + κ') = qSpread q κ + qSpread q κ' := by
  ext A hA
  rw [Measure.add_apply, qSpread_apply q _ hA, qSpread_apply q _ hA, qSpread_apply q _ hA,
    ← ENNReal.tsum_add]
  exact tsum_congr fun i => Measure.add_apply _ _ _

theorem qSpread_smul (q : ℝ) (c : ℝ≥0∞) (κ : Measure ℝ) :
    qSpread q (c • κ) = c • qSpread q κ := by
  ext A hA
  rw [Measure.smul_apply, qSpread_apply q _ hA, qSpread_apply q _ hA, smul_eq_mul,
    ← ENNReal.tsum_mul_left]
  exact tsum_congr fun i => by rw [Measure.smul_apply, smul_eq_mul]

theorem div_pow_succ_eq {q : ℝ} (hq : q ≠ 0) (x : ℝ) (i : ℕ) :
    q * (x / q ^ (i + 1)) = x / q ^ i := by
  rw [pow_succ]
  field_simp

theorem inv_mul_div_pow_eq {q : ℝ} (hq : q ≠ 0) (x : ℝ) (i : ℕ) :
    q⁻¹ * x / q ^ i = x / q ^ (i + 1) := by
  rw [pow_succ]
  field_simp

/-- **`qSpread κ ≤ T_q qSpread κ`.** -/
theorem qSpread_le_map {q : ℝ} (hq : 0 < q) (κ : Measure ℝ) :
    qSpread q κ ≤ (qSpread q κ).map fun v => q * v := by
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.map_apply (measurable_const_mul q) hA, qSpread_apply q κ hA,
    qSpread_apply q κ (measurable_const_mul q hA)]
  calc ∑' i : ℕ, κ ((fun x => x / q ^ i) ⁻¹' A)
      = ∑' i : ℕ, κ ((fun x => x / q ^ (i + 1)) ⁻¹' ((fun v => q * v) ⁻¹' A)) := by
        refine tsum_congr fun i => congrArg κ ?_
        ext x
        simp only [mem_preimage]
        rw [div_pow_succ_eq hq.ne' x i]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective 1)
        (fun j => κ ((fun x => x / q ^ j) ⁻¹' ((fun v => q * v) ⁻¹' A)))

/-- **`qSpread κ = κ + T_{q^{-1}} qSpread κ`.** -/
theorem qSpread_eq_add_map {q : ℝ} (hq : 0 < q) (κ : Measure ℝ) :
    qSpread q κ = κ + (qSpread q κ).map fun v => q⁻¹ * v := by
  ext A hA
  rw [Measure.add_apply, Measure.map_apply (measurable_const_mul _) hA, qSpread_apply q κ hA,
    qSpread_apply q κ (measurable_const_mul _ hA), tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · simp
  · refine tsum_congr fun i => congrArg κ ?_
    ext x
    simp only [mem_preimage]
    rw [← div_pow_succ_eq hq.ne' x i, ← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul]

/-! ## The `q`-Cin ray as a series -/

theorem qCinRay_summable {q : ℝ} (hq : 1 < q) (τ ω : ℝ) :
    Summable fun i : ℕ => 1 - Real.cos (ω * (τ / q ^ i)) := by
  have hq0 : q ≠ 0 := (by linarith : (0 : ℝ) < q).ne'
  have hr : 0 ≤ (q ^ 2)⁻¹ := by positivity
  have hr1 : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
  refine Summable.of_nonneg_of_le (fun i => sub_nonneg.2 (Real.cos_le_one _)) (fun i => ?_)
    ((summable_geometric_of_lt_one hr hr1).mul_left ((ω * τ) ^ 2 / 2))
  have h := Real.one_sub_sq_div_two_le_cos (x := ω * (τ / q ^ i))
  have : (ω * (τ / q ^ i)) ^ 2 = (ω * τ) ^ 2 * ((q ^ 2)⁻¹) ^ i := by
    rw [inv_pow, ← pow_mul, mul_comm 2 i, pow_mul]
    field_simp
  rw [this] at h
  linarith

theorem qCinRay_nonneg (q τ ω : ℝ) : 0 ≤ qCinRay q τ ω :=
  tsum_nonneg fun _ => sub_nonneg.2 (Real.cos_le_one _)

theorem ofReal_qCinRay {q : ℝ} (hq : 1 < q) (τ ω : ℝ) :
    ENNReal.ofReal (qCinRay q τ ω) = ∑' i : ℕ, ENNReal.ofReal (1 - Real.cos (ω * (τ / q ^ i))) :=
  ENNReal.ofReal_tsum_of_nonneg (fun _ => sub_nonneg.2 (Real.cos_le_one _))
    (qCinRay_summable hq τ ω)

/-- `E^{(q)}_τ(ω) > 0` for `τ, ω ≠ 0`: its terms with `|ωτq^{-i}| < 2π` are positive. -/
theorem qCinRay_pos {q : ℝ} (hq : 1 < q) {τ ω : ℝ} (hτ : τ ≠ 0) (hω : ω ≠ 0) :
    0 < qCinRay q τ ω := by
  have hq0 : 0 < q := by linarith
  obtain ⟨i, hi⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop
    (|ω * τ| / (2 * Real.pi))).exists
  have hqi : 0 < q ^ i := pow_pos hq0 i
  set x := ω * (τ / q ^ i) with hx
  have hx0 : x ≠ 0 := by
    rw [hx]
    exact mul_ne_zero hω (div_ne_zero hτ hqi.ne')
  have hxabs : |x| < 2 * Real.pi := by
    have h1 : |x| = |ω * τ| / q ^ i := by
      rw [hx, ← mul_div_assoc, abs_div, abs_of_pos hqi]
    rw [h1, div_lt_iff₀ hqi]
    rw [div_lt_iff₀ (by positivity)] at hi
    linarith
  have hcos : Real.cos x < 1 := by
    refine lt_of_le_of_ne (Real.cos_le_one x) fun h => hx0 ?_
    exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [neg_abs_le x]) (lt_of_le_of_lt
      (le_abs_self x) hxabs)).1 h
  exact (qCinRay_summable hq τ ω).tsum_pos (fun j => sub_nonneg.2 (Real.cos_le_one _)) i
    (by rw [← hx]; linarith)

/-- `∫ E^{(q)}_τ(ω) κ(dτ) = ∫ (1 - cos ωv) (qSpread q κ)(dv)`. -/
theorem lintegral_qCinRay_eq {q : ℝ} (hq : 1 < q) (κ : Measure ℝ) (ω : ℝ) :
    ∫⁻ τ, ENNReal.ofReal (qCinRay q τ ω) ∂κ =
      ∫⁻ v, ENNReal.ofReal (1 - Real.cos (ω * v)) ∂(qSpread q κ) := by
  rw [lintegral_qSpread q κ (by fun_prop)]
  exact lintegral_congr fun τ => ofReal_qCinRay hq τ ω

/-- A measure `κ` on `(0,∞)` with `∫ E^{(q)}_τ(1) κ(dτ) < ∞` is σ-finite. -/
theorem sigmaFinite_of_qCinRay {q : ℝ} (hq : 1 < q) {κ : Measure ℝ} (hκ : κ (Iic 0) = 0)
    (hfin : ∫⁻ τ, ENNReal.ofReal (qCinRay q τ 1) ∂κ ≠ ⊤) : SigmaFinite κ := by
  set G : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (qCinRay q τ 1) with hG
  have hGm : Measurable G := by
    have : G = fun τ => ∑' i : ℕ, ENNReal.ofReal (1 - Real.cos (1 * (τ / q ^ i))) :=
      funext fun τ => ofReal_qCinRay hq τ 1
    rw [this]
    exact Measurable.tsum fun i => by fun_prop
  refine Measure.sigmaFinite_of_countable
    (S := insert (Iic 0) (range fun n : ℕ => {τ | ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ G τ}))
    ((countable_range _).insert _) ?_ ?_
  · rintro s (rfl | ⟨n, rfl⟩)
    · rw [hκ]
      exact ENNReal.zero_lt_top
    · have h := mul_meas_ge_le_lintegral₀ (μ := κ) hGm.aemeasurable
        (ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      have hpos : ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity
      exact ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hfin h) hpos
  · refine eq_univ_of_forall fun τ => ?_
    rcases le_or_gt τ 0 with hτ | hτ
    · exact ⟨Iic 0, mem_insert _ _, hτ⟩
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (qCinRay_pos hq hτ.ne' one_ne_zero)
      exact ⟨_, mem_insert_of_mem _ ⟨n, rfl⟩, ENNReal.ofReal_le_ofReal hn.le⟩

/-! ## Lévy integrability from the exponent -/

/-- `x² ≤ 3(1 - cos x)` for `|x| ≤ 1`. -/
theorem sq_le_three_mul_one_sub_cos {x : ℝ} (hx : |x| ≤ 1) : x ^ 2 ≤ 3 * (1 - Real.cos x) := by
  have h := (abs_le.1 (Real.cos_bound hx)).2
  have hx2 : x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg x]
  have h4 : |x| ^ 4 ≤ x ^ 2 := by
    have : |x| ^ 4 = x ^ 2 * x ^ 2 := by
      rw [← sq_abs x]
      ring
    rw [this]
    exact mul_le_of_le_one_left (sq_nonneg x) hx2
  nlinarith [sq_nonneg x]

/-- `1 - cos ωx ≤ 2(1 ∧ x²)` for `|ω| ≤ 2`. -/
theorem one_sub_cos_le_two_min {ω x : ℝ} (hω : |ω| ≤ 2) :
    1 - Real.cos (ω * x) ≤ 2 * min 1 (x ^ 2) := by
  rcases le_total (x ^ 2) 1 with hx | hx
  · rw [min_eq_right hx]
    have h := Real.one_sub_sq_div_two_le_cos (x := ω * x)
    have hω2 : ω ^ 2 ≤ 4 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg ω]
    have : (ω * x) ^ 2 = ω ^ 2 * x ^ 2 := by ring
    nlinarith [sq_nonneg x]
  · rw [min_eq_left hx]
    linarith [Real.neg_one_le_cos (ω * x)]

/-- `∫_0^2 (1 - cos ωx) dω = 2 - sin(2x)/x ≥ 1` for `|x| ≥ 1`. -/
theorem one_le_lintegral_one_sub_cos {x : ℝ} (hx : 1 ≤ |x|) :
    1 ≤ ∫⁻ ω in Ioc (0 : ℝ) 2, ENNReal.ofReal (1 - Real.cos (ω * x)) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hx
    linarith
  have hc : Continuous fun ω : ℝ => 1 - Real.cos (ω * x) := by fun_prop
  have hint : ∫ ω in (0 : ℝ)..2, (1 - Real.cos (ω * x)) = 2 - x⁻¹ * Real.sin (2 * x) := by
    have hcos : Continuous fun ω : ℝ => Real.cos (ω * x) := by fun_prop
    rw [intervalIntegral.integral_sub (f := fun _ => (1 : ℝ)) (g := fun ω => Real.cos (ω * x))
      intervalIntegrable_const (hcos.intervalIntegrable _ _),
      intervalIntegral.integral_comp_mul_right (fun y => Real.cos y) hx0, integral_cos]
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.intervalIntegrable 0 2).1
    (ae_of_all _ fun ω => sub_nonneg.2 (Real.cos_le_one _)),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2), hint, ENNReal.one_le_ofReal]
  have h1 : x⁻¹ * Real.sin (2 * x) ≤ 1 := by
    calc x⁻¹ * Real.sin (2 * x) ≤ |x⁻¹ * Real.sin (2 * x)| := le_abs_self _
      _ = |x|⁻¹ * |Real.sin (2 * x)| := by rw [abs_mul, abs_inv]
      _ ≤ 1 * 1 := mul_le_mul (inv_le_one_of_one_le₀ hx) (Real.abs_sin_le_one _)
          (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  linarith

/-- **Lévy integrability from the exponent.** If an s-finite measure `m` has
`∫ (1 - cos ωx) m(dx) ≤ ψ(ω)` for every `ω`, with `ψ` the exponent of a pair, then
`∫ (1 ∧ x²) m(dx) < ∞`: on `|x| ≤ 1` by `x² ≤ 3(1 - cos x)`, on `|x| ≥ 1` by averaging over
`ω ∈ (0,2]` (Tonelli). -/
theorem levy_integrable_of_cos_le (m : Measure ℝ) [SFinite m] (P : SymLevyPair)
    (h : ∀ ω : ℝ, ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂m ≤ P.exponentL ω) :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂m ≠ ⊤ := by
  set g : ℝ → ℝ → ℝ≥0∞ := fun x ω => ENNReal.ofReal (1 - Real.cos (ω * x)) with hg
  have hgm : Measurable (Function.uncurry g) := by
    simp only [hg]
    fun_prop
  have hg1 : Measurable fun x => g x 1 := by
    simp only [hg]
    fun_prop
  -- the pointwise bound
  have hpt : ∀ x : ℝ, ENNReal.ofReal (min 1 (x ^ 2)) ≤
      3 * g x 1 + ∫⁻ ω in Ioc (0 : ℝ) 2, g x ω := by
    intro x
    rcases le_or_gt |x| 1 with hx | hx
    · refine le_add_right ?_
      simp only [hg, one_mul]
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (sq_le_three_mul_one_sub_cos hx))
    · refine le_add_left ?_
      calc ENNReal.ofReal (min 1 (x ^ 2)) ≤ 1 := ENNReal.ofReal_le_one.2 (min_le_left _ _)
        _ ≤ _ := one_le_lintegral_one_sub_cos hx.le
  -- the exponent is bounded on `(0, 2]`
  set C : ℝ≥0∞ := ENNReal.ofReal (4 * P.a) + 2 * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν
    with hC
  have hCt : C ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (by norm_num) P.ν_integrable⟩
  have hexp : ∀ ω ∈ Ioc (0 : ℝ) 2, P.exponentL ω ≤ C := by
    intro ω hω
    have hωa : |ω| ≤ 2 := by rw [abs_of_pos hω.1]; exact hω.2
    rw [SymLevyPair.exponentL, hC]
    refine add_le_add (ENNReal.ofReal_le_ofReal ?_) ?_
    · have : ω ^ 2 ≤ 4 := by nlinarith [hω.1, hω.2]
      nlinarith [P.a_nonneg]
    · rw [← lintegral_const_mul' 2 _ (by norm_num)]
      refine lintegral_mono fun x => ?_
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (one_sub_cos_le_two_min hωa)
  have hbound : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂m ≤
      3 * P.exponentL 1 + ∫⁻ _ in Ioc (0 : ℝ) 2, C := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_add_left (hg1.const_mul 3), lintegral_const_mul 3 hg1,
      lintegral_lintegral_swap hgm.aemeasurable]
    have h1 : ∫⁻ x, g x 1 ∂m ≤ P.exponentL 1 := by simpa [hg] using h 1
    refine add_le_add (by gcongr) ?_
    exact setLIntegral_mono' measurableSet_Ioc fun ω hω => (h ω).trans (hexp ω hω)
  refine ne_top_of_le_ne_top ?_ hbound
  rw [setLIntegral_const, Real.volume_Ioc]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) (P.exponentL_ne_top 1),
    ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top⟩

/-! ## The representation -/

/-- A representation gives the data `(a, qSpread κ)`, when the spread is a Lévy measure. -/
theorem hasExpData_of_qCinRepr {q : ℝ} (hq : 1 < q) {ψ : ℝ → ℝ} {a : ℝ} {κ : Measure ℝ}
    (h : IsQCinRepr q ψ a κ) (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(qSpread q κ) ≠ ⊤) :
    ∃ P : SymLevyPair, P.a = a ∧ P.ν = qSpread q κ ∧ HasExpData ψ P := by
  refine ⟨⟨a, qSpread q κ, h.1, qSpread_Iic (by linarith) h.2.1, hint⟩, rfl, rfl, fun ω => ?_⟩
  rw [SymLevyPair.exponent, SymLevyPair.exponentL]
  simp only
  rw [← lintegral_qCinRay_eq hq, ← h.2.2 ω, ENNReal.toReal_ofReal (hψ0 ω)]

/-- The spread of a representation of an element of `ND_s` is a Lévy measure. -/
theorem qSpread_levy_of_qCinRepr {q : ℝ} (hq : 1 < q) {ψ : ℝ → ℝ} (hψ : IsSymLevyExponent ψ)
    {a : ℝ} {κ : Measure ℝ} (h : IsQCinRepr q ψ a κ) :
    ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(qSpread q κ) ≠ ⊤ := by
  obtain ⟨P, hP⟩ := hψ
  have hle : ∀ ω : ℝ, ∫⁻ τ, ENNReal.ofReal (qCinRay q τ ω) ∂κ ≤ ENNReal.ofReal (ψ ω) := by
    intro ω
    rw [h.2.2 ω]
    exact le_add_self
  haveI : SigmaFinite κ :=
    sigmaFinite_of_qCinRay hq h.2.1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle 1))
  haveI : SFinite (qSpread q κ) := by
    unfold qSpread
    infer_instance
  refine levy_integrable_of_cos_le _ P fun ω => ?_
  rw [← lintegral_qCinRay_eq hq, ← SymLevyPair_ofReal_exponent, ← hP ω]
  exact hle ω

/-- **The spread determines the measure**: `qSpread κ = qSpread κ'` with the spread a Lévy measure
and `κ, κ'` null on `(-∞,0]` gives `κ = κ'`. -/
theorem qSpread_injective {q : ℝ} (hq : 1 < q) {κ κ' : Measure ℝ} (hκ : κ (Iic 0) = 0)
    (hκ' : κ' (Iic 0) = 0) (P : SymLevyPair) (hP : P.ν = qSpread q κ)
    (h : qSpread q κ = qSpread q κ') : κ = κ' := by
  have hq0 : 0 < q := by linarith
  refine measure_ext_of_Ioi hκ hκ' fun ε hε A hA hAε => ?_
  have e1 := congrArg (fun m : Measure ℝ => m A) (qSpread_eq_add_map hq0 κ)
  have e2 := congrArg (fun m : Measure ℝ => m A) (qSpread_eq_add_map hq0 κ')
  simp only [Measure.add_apply] at e1 e2
  rw [← h] at e2
  have hfin : ((qSpread q κ).map fun v => q⁻¹ * v) A ≠ ⊤ := by
    rw [Measure.map_apply (measurable_const_mul _) hA, ← hP]
    refine ne_top_of_le_ne_top (SymLevyPair_measure_Ioi_ne_top P (mul_pos hq0 hε))
      (measure_mono fun x hx => ?_)
    have h1 : ε < q⁻¹ * x := hAε hx
    rw [mem_Ioi]
    rw [inv_mul_eq_div, lt_div_iff₀ hq0] at h1
    linarith
  exact (ENNReal.add_left_inj hfin).1 (e1.symm.trans e2)

/-- **Uniqueness of the representation**, for any `ψ ∈ ND_s`. -/
theorem qCinRepr_unique {q : ℝ} (hq : 1 < q) {ψ : ℝ → ℝ} (hψ : IsSymLevyExponent ψ) {a a' : ℝ}
    {κ κ' : Measure ℝ} (h : IsQCinRepr q ψ a κ) (h' : IsQCinRepr q ψ a' κ') :
    a = a' ∧ κ = κ' := by
  obtain ⟨P, hPa, hPν, hP⟩ := hasExpData_of_qCinRepr hq h (isSymLevyExponent_nonneg hψ)
    (qSpread_levy_of_qCinRepr hq hψ h)
  obtain ⟨P', hP'a, hP'ν, hP'⟩ := hasExpData_of_qCinRepr hq h' (isSymLevyExponent_nonneg hψ)
    (qSpread_levy_of_qCinRepr hq hψ h')
  obtain ⟨ha, hν⟩ := line_exponent_data_1_unique ψ P P' hP hP'
  refine ⟨hPa ▸ hP'a ▸ ha, qSpread_injective hq h.2.1 h'.2.1 P hPν ?_⟩
  rw [← hPν, ← hP'ν, hν]

/-- **Existence of the representation**: for `ψ ∈ 𝒦_q` with data `(a, ϖ)`, the measure
`κ = ϖ - T_{q^{-1}}ϖ` represents `ψ`, and its spread is `ϖ`. -/
theorem qCinRepr_exists {q : ℝ} (hq : 1 < q) {ψ : ℝ → ℝ} (P : SymLevyPair) (hP : HasExpData ψ P)
    (hK : P.ν ≤ P.ν.map fun v => q * v) :
    ∃ κ : Measure ℝ, IsQCinRepr q ψ P.a κ ∧ qSpread q κ = P.ν := by
  have hq0 : 0 < q := by linarith
  obtain ⟨Q, -, hQν, -⟩ := line_exponent_data_2 ψ P hP (inv_pos.2 hq0)
  have hle : Q.ν ≤ P.ν := by
    rw [hQν, Measure.le_iff]
    intro A hA
    rw [Measure.map_apply (measurable_const_mul _) hA]
    refine (Measure.le_iff'.1 hK _).trans_eq ?_
    rw [Measure.map_apply (measurable_const_mul _) (measurable_const_mul _ hA)]
    congr 1
    ext x
    simp [inv_mul_cancel_left₀ hq0.ne']
  obtain ⟨κ, hκ⟩ := SymLevyPair_exists_sub Q P hle
  have hκle : κ ≤ P.ν := hκ ▸ Measure.le_add_right le_rfl
  have hκ0 : κ (Iic 0) = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hκle (Iic 0)).trans P.ν_folded.le)
  have key : qSpread q κ = P.ν := by
    refine measure_ext_of_Ioi (qSpread_Iic hq0 hκ0) P.ν_folded fun ε hε A hA hAε => ?_
    set B : ℕ → Set ℝ := fun i => (fun x => x / q ^ i) ⁻¹' A with hB
    have hBm : ∀ i, MeasurableSet (B i) := fun i => measurable_div_pow q i hA
    have hstep : ∀ i, P.ν (B i) = κ (B i) + P.ν (B (i + 1)) := by
      intro i
      have e := congrArg (fun m : Measure ℝ => m (B i)) hκ
      simp only [Measure.add_apply] at e
      rw [← e, hQν, Measure.map_apply (measurable_const_mul _) (hBm i)]
      congr 2
      ext x
      simp only [hB, mem_preimage]
      rw [inv_mul_div_pow_eq hq0.ne' x i]
    have hsum : ∀ n : ℕ, P.ν A = (∑ i ∈ Finset.range n, κ (B i)) + P.ν (B n) := by
      intro n
      induction n with
      | zero => simp [hB]
      | succ n ih => rw [ih, hstep n, Finset.sum_range_succ, add_assoc]
    -- the tail tends to `0`
    have hsub : ∀ n : ℕ, B n ⊆ Ioi (ε * q ^ n) := by
      intro n x hx
      have h1 : ε < x / q ^ n := hAε hx
      rw [lt_div_iff₀ (pow_pos hq0 n)] at h1
      exact h1
    have hanti : Antitone fun n : ℕ => Ioi (ε * q ^ n) := by
      intro n k hnk
      exact Ioi_subset_Ioi (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq.le hnk) hε.le)
    have hinter : (⋂ n : ℕ, Ioi (ε * q ^ n)) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop
        (x / ε)).exists
      have h1 : ε * q ^ n < x := mem_iInter.1 hx n
      rw [div_lt_iff₀ hε] at hn
      linarith
    have htail : Tendsto (fun n => P.ν (B n)) atTop (𝓝 0) := by
      have h := tendsto_measure_iInter_atTop (μ := P.ν)
        (fun n => (measurableSet_Ioi (a := ε * q ^ n)).nullMeasurableSet) hanti
        ⟨0, by simpa using SymLevyPair_measure_Ioi_ne_top P hε⟩
      rw [hinter, measure_empty] at h
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
        (fun _ => by simp) fun n => measure_mono (hsub n)
    have hlim : Tendsto (fun n => (∑ i ∈ Finset.range n, κ (B i)) + P.ν (B n)) atTop
        (𝓝 ((∑' i, κ (B i)) + 0)) :=
      (ENNReal.tendsto_nat_tsum _).add htail
    have hconst : Tendsto (fun n => (∑ i ∈ Finset.range n, κ (B i)) + P.ν (B n)) atTop
        (𝓝 (P.ν A)) := by
      simp only [← hsum]
      exact tendsto_const_nhds
    rw [qSpread_apply q κ hA, tendsto_nhds_unique hconst hlim, add_zero]
  refine ⟨κ, ⟨P.a_nonneg, hκ0, fun ω => ?_⟩, key⟩
  rw [hP ω, SymLevyPair_ofReal_exponent, SymLevyPair.exponentL, lintegral_qCinRay_eq hq, key]

/-! ## `prop:strata-cylinder-coordinates-q-cin`(1) -/

/-- **The pair of `E^{(q)}_τ`**: `(0, ∑_{i ≥ 0} δ_{τq^{-i}})`. -/
noncomputable def qCinPair {q τ : ℝ} (hq : 1 < q) (hτ : 0 < τ) : SymLevyPair where
  a := 0
  ν := qCinAtoms q τ
  a_nonneg := le_rfl
  ν_folded := by
    rw [ScaleSpace.IsFolded, ← qSpread_dirac]
    refine qSpread_Iic (by linarith) ?_
    rw [Measure.dirac_apply' _ measurableSet_Iic,
      indicator_of_notMem (show τ ∉ Iic (0 : ℝ) from not_le.2 hτ)]
  ν_integrable := by
    have hq0 : q ≠ 0 := (by linarith : (0 : ℝ) < q).ne'
    have hr : 0 ≤ (q ^ 2)⁻¹ := by positivity
    have hr1 : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
    have hs := (summable_geometric_of_lt_one hr hr1).mul_left (τ ^ 2)
    rw [qCinAtoms, lintegral_sum_measure]
    simp only [lintegral_dirac]
    refine ne_top_of_le_ne_top (b := ∑' i : ℕ, ENNReal.ofReal (τ ^ 2 * ((q ^ 2)⁻¹) ^ i)) ?_ ?_
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hs]
      exact ENNReal.ofReal_ne_top
    · refine ENNReal.tsum_le_tsum fun i =>
        ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans_eq ?_)
      rw [inv_pow, ← pow_mul, mul_comm 2 i, pow_mul]
      field_simp

theorem qCinPair_exponent {q τ : ℝ} (hq : 1 < q) (hτ : 0 < τ) (ω : ℝ) :
    (qCinPair hq hτ).exponent ω = qCinRay q τ ω := by
  rw [SymLevyPair.exponent, SymLevyPair.exponentL]
  simp only [qCinPair, zero_mul, ENNReal.ofReal_zero, zero_add]
  rw [← qSpread_dirac, ← lintegral_qCinRay_eq hq, lintegral_dirac,
    ENNReal.toReal_ofReal (qCinRay_nonneg q τ ω)]

/-- **`prop:strata-cylinder-coordinates-q-cin`(1), the cone.** `𝒦_q` is a convex cone containing
`ω²` and every `E^{(q)}_τ`, the exponent with data `(0, ∑_{i ≥ 0} δ_{τq^{-i}})`. -/
theorem qcin_1_cone {q : ℝ} (hq : 1 < q) :
    (∀ ψ ψ' : ℝ → ℝ, IsInKq q ψ → IsInKq q ψ' → IsInKq q (ψ + ψ')) ∧
      (∀ (ψ : ℝ → ℝ) (c : ℝ), 0 ≤ c → IsInKq q ψ → IsInKq q (c • ψ)) ∧
      IsInKq q (fun ω => ω ^ 2) ∧
      ∀ τ : ℝ, 0 < τ → IsInKq q (qCinRay q τ) ∧
        ∃ P : SymLevyPair, P.a = 0 ∧ P.ν = qCinAtoms q τ ∧ HasExpData (qCinRay q τ) P := by
  have hq0 : 0 < q := by linarith
  have hmeas : Measurable fun v : ℝ => q * v := measurable_const_mul q
  refine ⟨?_, ?_, ?_, fun τ hτ => ?_⟩
  · rintro ψ ψ' ⟨P, hP, hK⟩ ⟨P', hP', hK'⟩
    refine ⟨SymLevyPair_add P P', fun ω => ?_, ?_⟩
    · rw [SymLevyPair_add_exponent, Pi.add_apply, hP ω, hP' ω]
    · change P.ν + P'.ν ≤ (P.ν + P'.ν).map fun v => q * v
      rw [Measure.map_add _ _ hmeas]
      exact add_le_add hK hK'
  · rintro ψ c hc ⟨P, hP, hK⟩
    refine ⟨SymLevyPair_smul c hc P, fun ω => ?_, ?_⟩
    · rw [SymLevyPair_smul_exponent, Pi.smul_apply, smul_eq_mul, hP ω]
    · change ENNReal.ofReal c • P.ν ≤ (ENNReal.ofReal c • P.ν).map fun v => q * v
      rw [Measure.map_smul, Measure.le_iff']
      intro s
      rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      have h1 := Measure.le_iff'.1 hK s
      gcongr
  · refine ⟨sqPair, fun ω => (sqPair_exponent ω).symm, ?_⟩
    change (0 : Measure ℝ) ≤ _
    exact Measure.zero_le _
  · refine ⟨⟨qCinPair hq hτ, fun ω => (qCinPair_exponent hq hτ ω).symm, ?_⟩,
      qCinPair hq hτ, rfl, rfl, fun ω => (qCinPair_exponent hq hτ ω).symm⟩
    change qCinAtoms q τ ≤ (qCinAtoms q τ).map fun v => q * v
    rw [← qSpread_dirac]
    exact qSpread_le_map hq0 _

/-- **`prop:strata-cylinder-coordinates-q-cin`(1), the representation.** Every `ψ ∈ 𝒦_q` is
uniquely `aω² + ∫ E^{(q)}_τ(ω) κ^{(q)}(dτ)`. -/
theorem qcin_1_repr {q : ℝ} (hq : 1 < q) (ψ : ℝ → ℝ) (hψ : IsInKq q ψ) :
    (∃ (a : ℝ) (κ : Measure ℝ), IsQCinRepr q ψ a κ) ∧
      ∀ (a a' : ℝ) (κ κ' : Measure ℝ), IsQCinRepr q ψ a κ → IsQCinRepr q ψ a' κ' →
        a = a' ∧ κ = κ' := by
  obtain ⟨P, hP, hK⟩ := hψ
  obtain ⟨κ, hκ, -⟩ := qCinRepr_exists hq P hP hK
  exact ⟨⟨P.a, κ, hκ⟩, fun a a' κ κ' h h' => qCinRepr_unique hq ⟨P, hP⟩ h h'⟩

end Pyramids
