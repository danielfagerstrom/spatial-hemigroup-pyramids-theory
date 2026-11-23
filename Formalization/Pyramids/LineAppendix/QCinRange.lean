/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.QCinRays
import Pyramids.LineAppendix.StrataCylinder
import Pyramids.Pyramid.LadderNuStar

/-!
# `prop:strata-cylinder-coordinates-q-cin`(1): the range of the representation

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:strata-cylinder-coordinates-q-cin`. Review
round 3, batch C (supp.R3): the pairs `(a, κ)` that represent an element of `𝒦_q` are those with
`a ≥ 0`, `κ` carried by `(0,∞)` and `∫ (τ² ∧ (1 + log₊ τ)) κ(dτ) < ∞`.

## The route

A pair represents an element of `𝒦_q` iff the spread `∑_{i ≥ 0} T_{q^{-i}} κ` is a Lévy measure
(`qSpread_levy_of_qCinRepr`, `qCinFun_spec`). Against `1 ∧ v²` the spread integrates
`∑_{i ≥ 0} (1 ∧ (τq^{-i})²) = (1 ∧ τ²) + b(τ)`, with `b` the bracket of `prop:ladder-knot-kernel`
(`ladderBracket`), and the bracket's two bounds (`ladderBracket_le`, `posLog_le_ladderBracket`)
put this sum between `(1 + ℓ)⁻¹ w(τ)` and `(1 + q²/(q² - 1) + ℓ⁻¹) w(τ)` for `τ > 0`, where
`w(τ) = τ² ∧ (1 + log₊ τ)` (`cylWeight`).
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair IsSymLevyExponent)
open scoped ENNReal

/-- **The spread's sum** `∑_{i ≥ 0} (1 ∧ (τq^{-i})²) = (1 ∧ τ²) + b(τ)`. -/
theorem qSpread_sum_eq {q : ℝ} (hq : 1 < q) (τ : ℝ) :
    Summable (fun i : ℕ => min 1 ((τ / q ^ i) ^ 2)) ∧
      ∑' i : ℕ, min 1 ((τ / q ^ i) ^ 2) = min 1 (τ ^ 2) + ladderBracket q τ := by
  have hs : Summable (fun m : ℕ => min 1 ((τ / q ^ (m + 1)) ^ 2)) :=
    (ladderBracket_summable hq τ).congr fun m => min_comm _ _
  have hs' : Summable (fun i : ℕ => min 1 ((τ / q ^ i) ^ 2)) :=
    (summable_nat_add_iff (f := fun i : ℕ => min 1 ((τ / q ^ i) ^ 2)) 1).1 hs
  refine ⟨hs', ?_⟩
  rw [← hs'.sum_add_tsum_nat_add 1, Finset.sum_range_one, ladderBracket]
  simp only [pow_zero, div_one]
  congr 1
  exact tsum_congr fun m => min_comm _ _

/-- **The lower bound** `w(τ) ≤ (1 + ℓ)((1 ∧ τ²) + b(τ))`, `τ > 0`. -/
theorem cylWeight_le_qSpread_sum {q : ℝ} (hq : 1 < q) {τ : ℝ} (hτ : 0 < τ) :
    cylWeight τ ≤ (1 + Real.log q) * (min 1 (τ ^ 2) + ladderBracket q τ) := by
  have hl : 0 < Real.log q := Real.log_pos hq
  have hb := ladderBracket_nonneg q τ
  rcases le_or_gt τ 1 with h1 | h1
  · have hm : min 1 (τ ^ 2) = τ ^ 2 := min_eq_right (by nlinarith)
    have hw : cylWeight τ ≤ τ ^ 2 := min_le_left _ _
    rw [hm]
    nlinarith [mul_nonneg hl.le (sq_nonneg τ), mul_nonneg hl.le hb]
  · have hm : min 1 (τ ^ 2) = 1 := min_eq_left (by nlinarith)
    have hw : cylWeight τ ≤ 1 + Real.posLog τ := min_le_right _ _
    have hp := posLog_le_ladderBracket hq h1
    rw [hm]
    nlinarith [mul_nonneg hl.le hb]

/-- **The upper bound** `(1 ∧ τ²) + b(τ) ≤ (1 + q²/(q² - 1) + ℓ⁻¹) w(τ)`, `τ > 0`. -/
theorem qSpread_sum_le_cylWeight {q : ℝ} (hq : 1 < q) {τ : ℝ} (hτ : 0 < τ) :
    min 1 (τ ^ 2) + ladderBracket q τ ≤
      (1 + q ^ 2 / (q ^ 2 - 1) + 1 / Real.log q) * cylWeight τ := by
  have hl : 0 < Real.log q := Real.log_pos hq
  have hc : 0 < q ^ 2 / (q ^ 2 - 1) := div_pos (by positivity) (by nlinarith)
  have hu : 0 < 1 / Real.log q := one_div_pos.2 hl
  have hb := ladderBracket_le hq hτ.le
  have e : Real.posLog τ / Real.log q = Real.posLog τ * (1 / Real.log q) := by ring
  rw [e] at hb
  rcases le_or_gt τ 1 with h1 | h1
  · have hp : Real.posLog τ = 0 := by
      rw [Real.posLog_eq_zero_iff, abs_of_pos hτ]
      exact h1
    have hm : min 1 (τ ^ 2) = τ ^ 2 := min_eq_right (by nlinarith)
    have hm' : min (τ ^ 2) 1 = τ ^ 2 := min_eq_left (by nlinarith)
    have hw : cylWeight τ = τ ^ 2 := by
      rw [cylWeight, hp, add_zero]
      exact min_eq_left (by nlinarith)
    rw [hp, hm', zero_mul, zero_add] at hb
    rw [hm, hw]
    nlinarith [mul_nonneg hu.le (sq_nonneg τ)]
  · have hm : min 1 (τ ^ 2) = 1 := min_eq_left (by nlinarith)
    have hm' : min (τ ^ 2) 1 = 1 := min_eq_right (by nlinarith)
    have hp0 : 0 ≤ Real.posLog τ := Real.posLog_nonneg
    have hpl : Real.posLog τ = Real.log τ :=
      Real.posLog_eq_log (by rw [abs_of_pos hτ]; exact h1.le)
    have hlog : Real.log τ ≤ τ - 1 := Real.log_le_sub_one_of_pos hτ
    have hw : cylWeight τ = 1 + Real.posLog τ := by
      rw [cylWeight]
      exact min_eq_right (by rw [hpl]; nlinarith)
    rw [hm'] at hb
    rw [hm, hw]
    nlinarith [mul_nonneg hp0 hc.le, mul_nonneg hp0 hu.le]

/-- **`prop:strata-cylinder-coordinates-q-cin`(1), the range.** A pair `(a, κ)`, `a ≥ 0`, `κ`
carried by `(0,∞)`, represents an element of `𝒦_q` if and only if
`∫ (τ² ∧ (1 + log₊ τ)) κ(dτ) < ∞`. -/
theorem qcin_1_range {q : ℝ} (hq : 1 < q) {a : ℝ} (ha : 0 ≤ a) {κ : Measure ℝ}
    (hκ : κ (Iic 0) = 0) :
    (∃ ψ : ℝ → ℝ, IsInKq q ψ ∧ IsQCinRepr q ψ a κ) ↔
      ∫⁻ τ, ENNReal.ofReal (cylWeight τ) ∂κ ≠ ⊤ := by
  have hl : 0 < Real.log q := Real.log_pos hq
  -- the spread's integral
  have hmeas : Measurable fun v : ℝ => ENNReal.ofReal (min 1 (v ^ 2)) :=
    (measurable_const.min (measurable_id.pow_const 2)).ennreal_ofReal
  have hsp : ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(qSpread q κ) =
      ∫⁻ τ, ENNReal.ofReal (min 1 (τ ^ 2) + ladderBracket q τ) ∂κ := by
    rw [lintegral_qSpread q κ hmeas]
    refine lintegral_congr fun τ => ?_
    obtain ⟨hs, he⟩ := qSpread_sum_eq hq τ
    rw [← he, ENNReal.ofReal_tsum_of_nonneg (fun i => le_min zero_le_one (sq_nonneg _)) hs]
  have hC1 : 0 ≤ 1 + Real.log q := by linarith
  have hC2 : 0 ≤ 1 + q ^ 2 / (q ^ 2 - 1) + 1 / Real.log q := by
    have h1 : 0 < q ^ 2 / (q ^ 2 - 1) := div_pos (by positivity) (by nlinarith)
    have h2 : 0 < 1 / Real.log q := one_div_pos.2 hl
    linarith
  have hlow : ∫⁻ τ, ENNReal.ofReal (cylWeight τ) ∂κ ≤
      ENNReal.ofReal (1 + Real.log q) *
        ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(qSpread q κ) := by
    rw [hsp, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_pos_of_Iic_zero hκ] with τ hτ
    rw [← ENNReal.ofReal_mul hC1]
    exact ENNReal.ofReal_le_ofReal (cylWeight_le_qSpread_sum hq hτ)
  have hup : ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(qSpread q κ) ≤
      ENNReal.ofReal (1 + q ^ 2 / (q ^ 2 - 1) + 1 / Real.log q) *
        ∫⁻ τ, ENNReal.ofReal (cylWeight τ) ∂κ := by
    rw [hsp, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_pos_of_Iic_zero hκ] with τ hτ
    rw [← ENNReal.ofReal_mul hC2]
    exact ENNReal.ofReal_le_ofReal (qSpread_sum_le_cylWeight hq hτ)
  constructor
  · rintro ⟨ψ, hK, hR⟩
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (qSpread_levy_of_qCinRepr hq (isInKq_symLevy hK) hR)) hlow
  · intro h
    exact ⟨_, qCinFun_spec hq ha hκ (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h) hup)⟩

end Pyramids
