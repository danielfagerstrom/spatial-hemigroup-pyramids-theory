/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Divisibility

/-!
# Ledger A48: infinitely divisible laws carried by `ℤ` (Sato, Cor. 24.6, p. 149)

**This file widens the trust base of the article: it declares one axiom**, admitted by the author on
2026-11-13. Ledger entry A48 of `blueprint/AXIOMS.md`, with its page transcription in
`blueprint/AXIOMS-verbatim.md`; interface node `thm:cited-A48`
(`blueprint/src/parts/02-cited-facts.tex`); listed in `blueprint/trust-boundary.txt`.

Source: Sato, *Lévy Processes and Infinitely Divisible Distributions*, Corollary 24.6 (Support in
`ℤ`), printed p. 149, its "only if". The axiom `cited_A48` admits what the corollary states, less
its drift clause: `A = 0` and a Lévy measure carried by `ℤ`, on `ℝ = ℝ¹ = Rd 1`, "the support is
contained in `ℤ`" read as "the complement of `ℤ` is null" (the skeleton's finding 9). Not carried:
the converse, the drift clause, any form on `ℝ^d`.

**The finiteness of `ν` is proved, not admitted** (review round 3, batch C, 2026-11-23; until then
the axiom carried it from the proof printed on the same page): `ν` is carried by `ℤ ∖ {0}`, where
`min(|x|², 1) = 1`, so `ν(ℝ) ≤ ∫ min(|x|², 1) dν < ∞` (`isFiniteMeasure_levy_of_int`).
`cited_A48_finite` is the former statement, for its users.

Not derived from the affine export: its ledger has no statement on supports.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory
open scoped ENNReal

/-- **`thm:cited-A48`, ledger A48** (Sato, Cor. 24.6, p. 149, the "only if" less the drift clause).
On `ℝ = ℝ¹`: an infinitely divisible law carried by `ℤ` has `A = 0` and a Lévy measure carried by
`ℤ`. Admitted by the author on 2026-11-13. -/
axiom cited_A48 (μ : Measure (Rd 1)) [IsProbabilityMeasure μ] (hμ : IsInfinitelyDivisible μ)
    (T : LevyTriplet 1) (hT : HasTriplet μ T)
    (hsupp : μ {x | ¬ ∃ k : ℤ, x 0 = k} = 0) :
    T.A = 0 ∧ T.ν {x | ¬ ∃ k : ℤ, x 0 = k} = 0

/-- **A Lévy measure on `ℝ` carried by `ℤ` is finite**: it is carried by `ℤ ∖ {0}` (`ν{0} = 0`),
where `|x| ≥ 1` and so `min(|x|², 1) = 1`, and `∫ min(|x|², 1) dν < ∞` by (8.2). -/
theorem isFiniteMeasure_levy_of_int (T : LevyTriplet 1)
    (hνZ : T.ν {x | ¬ ∃ k : ℤ, x 0 = k} = 0) : IsFiniteMeasure T.ν := by
  have h0 : ∀ᵐ x ∂T.ν, x ≠ 0 := by
    rw [ae_iff]
    simpa using T.ν_zero
  have hZ : ∀ᵐ x ∂T.ν, ∃ k : ℤ, x 0 = (k : ℝ) := by
    rw [ae_iff]
    exact hνZ
  have hae : ∀ᵐ x ∂T.ν, (1 : ℝ≥0∞) ≤ ENNReal.ofReal (min (‖x‖ ^ 2) 1) := by
    filter_upwards [h0, hZ] with x hx hk
    obtain ⟨k, hk⟩ := hk
    have hn : ‖x‖ = |(k : ℝ)| := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _),
        Real.norm_eq_abs, hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hx
      rw [← norm_eq_zero, hn]
      simp
    have h1 : (1 : ℝ) ≤ ‖x‖ := by
      rw [hn]
      exact_mod_cast Int.one_le_abs hk0
    rw [min_eq_right (by nlinarith), ENNReal.ofReal_one]
  refine ⟨lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr T.ν_integrable)⟩
  calc T.ν Set.univ = ∫⁻ _, 1 ∂T.ν := lintegral_one.symm
    _ ≤ _ := lintegral_mono_ae hae

/-- **`thm:cited-A48` with the finiteness of `ν`**: the former statement of the axiom, now the axiom
`cited_A48` and `isFiniteMeasure_levy_of_int`. -/
theorem cited_A48_finite (μ : Measure (Rd 1)) [IsProbabilityMeasure μ]
    (hμ : IsInfinitelyDivisible μ) (T : LevyTriplet 1) (hT : HasTriplet μ T)
    (hsupp : μ {x | ¬ ∃ k : ℤ, x 0 = k} = 0) :
    T.A = 0 ∧ T.ν {x | ¬ ∃ k : ℤ, x 0 = k} = 0 ∧ IsFiniteMeasure T.ν := by
  obtain ⟨hA, hν⟩ := cited_A48 μ hμ T hT hsupp
  exact ⟨hA, hν, isFiniteMeasure_levy_of_int T hν⟩

end Pyramids
