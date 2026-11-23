/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Interfaces

/-!
# Ledger A39: the Lévy–Khintchine representation (Sato, Thm. 8.1, pp. 37–38)

Interface node `thm:cited-A39` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A39 of
`blueprint/AXIOMS.md`, cited from Sato, *Lévy Processes and Infinitely Divisible Distributions*,
Theorem 8.1(i)–(iii), printed pp. 37–38, with Definition 8.2 on p. 38.

The author admitted A39 on 2026-11-13. **This file declares no axiom.** The three clauses, at the
statements the skeleton typed and the phase-4 review checked against the page, are the affine
export's axioms `AffineHemigroup.levy_khintchine_exists`, `levy_khintchine_unique` and
`levy_khintchine_converse` (its ledger A3, the same theorem of Sato, transcribed there from the same
pages), word for word in the same vocabulary (`IsInfinitelyDivisible`, `LevyTriplet`, `HasTriplet`
of `AffineHemigroup.Defs.Divisibility`). Each declaration below is that axiom, so `#print axioms`
names the affine axiom, which `blueprint/trust-boundary.txt` lists by its own name, grounded in this
article's entry A39.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory

variable {d : ℕ}

/-- **`thm:cited-A39`(i)** (Sato, Thm. 8.1(i), p. 37). An infinitely divisible law on `ℝ^d` has
a generating triplet: `μ̂ = exp` of (8.1), with `(A, ν, γ)` meeting (8.2) (`LevyTriplet`,
`HasTriplet`). The affine export's axiom `AffineHemigroup.levy_khintchine_exists`. -/
theorem cited_A39_exists (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsInfinitelyDivisible μ) : ∃ T : LevyTriplet d, HasTriplet μ T :=
  levy_khintchine_exists μ hμ

/-- **`thm:cited-A39`(ii)** (Sato, Thm. 8.1(ii), p. 38). The triplet is unique. The affine
export's axiom `AffineHemigroup.levy_khintchine_unique`. -/
theorem cited_A39_unique (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsInfinitelyDivisible μ) (T T' : LevyTriplet d) (hT : HasTriplet μ T)
    (hT' : HasTriplet μ T') : T.A = T'.A ∧ T.ν = T'.ν ∧ T.γ = T'.γ :=
  levy_khintchine_unique μ hμ T T' hT hT'

/-- **`thm:cited-A39`(iii)** (Sato, Thm. 8.1(iii), p. 38). Every triplet is the triplet of an
infinitely divisible law. The affine export's axiom `AffineHemigroup.levy_khintchine_converse`. -/
theorem cited_A39_converse (T : LevyTriplet d) :
    ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsInfinitelyDivisible μ ∧ HasTriplet μ T :=
  levy_khintchine_converse T

end Pyramids
