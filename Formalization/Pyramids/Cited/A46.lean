/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.Divisibility

/-!
# Ledger A46: unbounded support (Sato, Cor. 24.4, p. 149)

**This file widens the trust base of the article: it declares one axiom**, admitted by the author on
2026-11-13. Ledger entry A46 of `blueprint/AXIOMS.md`, with its page transcription in
`blueprint/AXIOMS-verbatim.md`; interface node `thm:cited-A46`
(`blueprint/src/parts/02-cited-facts.tex`); listed in `blueprint/trust-boundary.txt`.

Source: Sato, *Lévy Processes and Infinitely Divisible Distributions*, Corollary 24.4, printed
p. 149, where a point mass is called a `δ`-distribution (the entry's verdict MATCH). The statement
is the skeleton's, unchanged: "the support of `μ` is unbounded" is read through measure, as positive
mass outside every ball (the skeleton's finding 9).

Not derived from the affine export: its ledger has no statement on supports.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory

variable {d : ℕ}

/-- **`thm:cited-A46`, ledger A46** (Sato, Cor. 24.4, p. 149). An infinitely divisible law that is
not a point mass gives positive mass to the outside of every ball. Admitted by the author on
2026-11-13. -/
axiom cited_A46 (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (hμ : IsInfinitelyDivisible μ)
    (hδ : ∀ x : Rd d, μ ≠ Measure.dirac x) (R : ℝ) : μ {x | R < ‖x‖} ≠ 0

end Pyramids
