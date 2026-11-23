/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Interfaces

/-!
# Ledger A45: the polar form of a self-decomposable law (Sato, Thm. 15.10, p. 95)

Interface node `thm:cited-A45` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A45 of
`blueprint/AXIOMS.md`, cited from Sato, *Lévy Processes and Infinitely Divisible Distributions*,
Theorem 15.10, printed p. 95, formula (15.8).

The author admitted A45 on 2026-11-14. **This file declares no axiom.** The statement, as the
skeleton typed it, is word for word the affine export's axiom
`AffineHemigroup.sato_polar_criterion` (its ledger A2, the same theorem of Sato at the same page),
in the same vocabulary. The declaration below is that axiom, so `#print axioms` names the affine
axiom, which `blueprint/trust-boundary.txt` lists by its own name, grounded in this article's
entry A45.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set

variable {d : ℕ}

/-- **`thm:cited-A45`** (Sato, Thm. 15.10, p. 95). An infinitely divisible `μ` with triplet
`(A, ν, γ)` is self-decomposable if and only if `ν(B) = ∫_S λ(dξ) ∫₀^∞ 1_B(rξ) k_ξ(r) dr/r` for
every Borel `B`, with `λ` finite on the unit sphere `S` and `k_ξ(r) ≥ 0`, measurable in `ξ`,
nonincreasing in `r > 0`. The affine export's axiom `AffineHemigroup.sato_polar_criterion`. -/
theorem cited_A45 (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (hμ : IsInfinitelyDivisible μ)
    (T : LevyTriplet d) (hT : HasTriplet μ T) :
    IsSelfDecomposableSato μ ↔
      ∃ (lam : Measure (Metric.sphere (0 : Rd d) 1)) (k : Metric.sphere (0 : Rd d) 1 → ℝ → ℝ),
        IsFiniteMeasure lam ∧ (∀ ξ, ∀ r : ℝ, 0 < r → 0 ≤ k ξ r) ∧
        (∀ r : ℝ, 0 < r → Measurable fun ξ => k ξ r) ∧ (∀ ξ, AntitoneOn (k ξ) (Ioi 0)) ∧
        ∀ B : Set (Rd d), MeasurableSet B →
          T.ν B = ∫⁻ ξ, (∫⁻ r in Ioi (0 : ℝ),
            B.indicator 1 (r • (ξ : Rd d)) * ENNReal.ofReal (k ξ r / r)) ∂lam :=
  sato_polar_criterion μ hμ T hT

end Pyramids
