/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.StratumOneExample

/-!
# `thm:lattice-strata-strict`: the strata are distinct

Blueprint: `blueprint/src/parts/03-pyramid.tex`. Moved from `PyramidsSkeleton.Ch03Pyramid` in wave
3d, unchanged in statement and name.

A fully covariant family is `q`-covariant by definition. The family of `prop:stratum-one-example`
(at `h = 1`) is isotropic and `q`-covariant for no `q ≠ 1`; the family of
`prop:stratum-two-example`, with the weights `w_i = 1` for `i < 0` and `0` otherwise, is isotropic,
`q`-covariant with `S t = q t`, and not fully covariant.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter

variable {d : ℕ}

/-- The weights `1` below `0` and `0` from `0` on. -/
noncomputable def lowerStepWeights (i : ℤ) : ℝ := if i < 0 then 1 else 0

/-- `∑_{i < 0} q^{2i}` converges for `q > 1`. -/
theorem summable_lowerStepWeights {q : ℝ} (hq : 1 < q) :
    Summable fun i : {i : ℤ // i < 0} => lowerStepWeights i * q ^ (2 * (i : ℤ)) := by
  have hq0 : 0 < q := by linarith
  set r : ℝ := (q ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
  have hg : Summable fun i : ℤ => r ^ i.natAbs := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨by simpa using summable_geometric_of_lt_one hr0 hr1,
      by simpa using summable_geometric_of_lt_one hr0 hr1⟩
  refine (hg.subtype {i : ℤ | i < 0}).congr fun i => ?_
  obtain ⟨i, hi⟩ := i
  have hi : i < 0 := hi
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨i.natAbs, by omega⟩
  simp only [Function.comp_apply, lowerStepWeights, if_pos hi, one_mul, Int.natAbs_neg,
    Int.natAbs_natCast, hr]
  rw [mul_neg, zpow_neg, zpow_mul, zpow_natCast, inv_pow]
  norm_cast

/-- **`thm:lattice-strata-strict`, the inclusion.** A fully covariant isotropic family is
`q`-covariant. -/
theorem lattice_strata_strict_imp {q : ℝ} (hq : 1 < q)
    (μ : ℝ → ℝ → Measure (Rd d)) (hfull : IsFullyCovariantLaws μ) :
    IsLamCovariant μ q :=
  hfull q (by linarith)

/-- **`thm:lattice-strata-strict`, both inclusions are strict.** Some isotropic family is not
`q`-covariant, and some `q`-covariant isotropic family is not fully covariant. -/
theorem lattice_strata_strict (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    (∃ μ : ℝ → ℝ → Measure (Rd d), IsIsotropicFamily μ ∧ ¬ IsLamCovariant μ q) ∧
      ∃ μ : ℝ → ℝ → Measure (Rd d), IsIsotropicFamily μ ∧ IsLamCovariant μ q ∧
        ¬ IsFullyCovariantLaws μ := by
  haveI : NeZero d := ⟨by omega⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨μ, hμ⟩, hall⟩ := stratum_one_example (d := d) one_pos
    obtain ⟨hiso, -, -, hnot⟩ := hall μ hμ
    exact ⟨μ, hiso, hnot q (by linarith) hq.ne'⟩
  · have hw0 : ∀ i, 0 ≤ lowerStepWeights i := fun i => by
      unfold lowerStepWeights; split_ifs <;> norm_num
    have hanti : Antitone lowerStepWeights := fun i j hij => by
      unfold lowerStepWeights
      split_ifs with hj hi hi <;> first | omega | norm_num
    have hne : ∃ i, lowerStepWeights i ≠ 0 := ⟨-1, by simp [lowerStepWeights]⟩
    have hpos : Summable fun i : {i : ℤ // 0 ≤ i} => lowerStepWeights i := by
      refine (summable_zero : Summable fun _ : {i : ℤ // 0 ≤ i} => (0 : ℝ)).congr fun i => ?_
      simp [lowerStepWeights, not_lt.2 i.2]
    have hneg := summable_lowerStepWeights hq
    obtain ⟨D, hD⟩ := (stratum_two_example_data hd hq one_pos lowerStepWeights hw0 hanti hne
      hneg hpos).1
    obtain ⟨⟨μ, hμ⟩, hall⟩ := stratum_two_example hd hq one_pos lowerStepWeights hw0 hanti hne
      hneg hpos D hD
    obtain ⟨hiso, hcov, hnot, -⟩ := hall μ hμ
    exact ⟨μ, hiso, ⟨_, hcov⟩, hnot⟩

/-- **`thm:lattice-strata-strict`, the strictness in the canonical gauge** (fidelity review, R58).
The draft's stratum (2) is `q`-covariance with `S_q t = qt`: some isotropic family is not
`q`-covariant with any `S` (so not with `S_q t = qt`), and some isotropic family `q`-covariant with
`S_q t = qt` is not fully covariant. -/
theorem lattice_strata_strict_canonical (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    (∃ μ : ℝ → ℝ → Measure (Rd d), IsIsotropicFamily μ ∧ ¬ IsLamCovariant μ q ∧
        ¬ IsCovariantAt μ q (fun t => q * t)) ∧
      ∃ μ : ℝ → ℝ → Measure (Rd d), IsIsotropicFamily μ ∧ IsCovariantAt μ q (fun t => q * t) ∧
        ¬ IsFullyCovariantLaws μ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨μ, hiso, hnot⟩ := (lattice_strata_strict hd hq).1
    exact ⟨μ, hiso, hnot, fun h => hnot ⟨_, h⟩⟩
  · have hw0 : ∀ i, 0 ≤ lowerStepWeights i := fun i => by
      unfold lowerStepWeights; split_ifs <;> norm_num
    have hanti : Antitone lowerStepWeights := fun i j hij => by
      unfold lowerStepWeights
      split_ifs with hj hi hi <;> first | omega | norm_num
    have hne : ∃ i, lowerStepWeights i ≠ 0 := ⟨-1, by simp [lowerStepWeights]⟩
    have hpos : Summable fun i : {i : ℤ // 0 ≤ i} => lowerStepWeights i := by
      refine (summable_zero : Summable fun _ : {i : ℤ // 0 ≤ i} => (0 : ℝ)).congr fun i => ?_
      simp [lowerStepWeights, not_lt.2 i.2]
    have hneg := summable_lowerStepWeights hq
    obtain ⟨D, hD⟩ := (stratum_two_example_data hd hq one_pos lowerStepWeights hw0 hanti hne
      hneg hpos).1
    obtain ⟨⟨μ, hμ⟩, hall⟩ := stratum_two_example hd hq one_pos lowerStepWeights hw0 hanti hne
      hneg hpos D hD
    obtain ⟨hiso, hcov, hnot, -⟩ := hall μ hμ
    exact ⟨μ, hiso, hcov, hnot⟩

end Pyramids
