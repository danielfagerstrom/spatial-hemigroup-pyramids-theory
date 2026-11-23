/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Cited

/-!
# Ledger A49: the `g`-moment theorem (Sato, Thm. 25.3, p. 159)

**This file widens the trust base of the article: it declares one axiom**, admitted by the author on
2026-11-14. Ledger entry A49 of `blueprint/AXIOMS.md`, with its page transcription in
`blueprint/AXIOMS-verbatim.md`; interface node `thm:cited-A49`
(`blueprint/src/parts/02-cited-facts.tex`); listed in `blueprint/trust-boundary.txt`.

Source: Sato, *Lévy Processes and Infinitely Divisible Distributions*, Theorem 25.3, printed
p. 159, with Definitions 25.1–25.2 on the same page, printed for a Lévy process and read for its law
at time 1 (the page: finiteness of the `g`-moment "is not a time dependent distributional
property"). The statement is the skeleton's, unchanged: `g` submultiplicative
(`IsSubmultiplicative`,
Def. 25.2), locally bounded and measurable. Both directions are spent (`prop:ladder-knot-kernel`(2)
and `prop:exact-masks`(1) state the two moments as equivalent).

Not derived: neither the affine export nor the shared core states the theorem, and Sato's proof
splits the law into a compound Poisson part and a part with bounded jumps and bounds the moments of
each, which is far beyond a short step.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory

variable {d : ℕ}

/-- **`thm:cited-A49`, ledger A49** (Sato, Thm. 25.3, p. 159). For a submultiplicative, locally
bounded, measurable `g` and an infinitely divisible `μ` with Lévy measure `ν`: `∫ g dμ < ∞` if and
only if `∫_{|x| > 1} g dν < ∞`. Admitted by the author on 2026-11-14. -/
axiom cited_A49 (g : Rd d → ℝ) (hg : IsSubmultiplicative g)
    (hgb : ∀ K : Set (Rd d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, |g x| ≤ C) (hgm : Measurable g)
    (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (hμ : IsInfinitelyDivisible μ)
    (T : LevyTriplet d) (hT : HasTriplet μ T) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≠ ⊤ ↔
      (∫⁻ x in {x : Rd d | 1 < ‖x‖}, ENNReal.ofReal (g x) ∂T.ν) ≠ ⊤

end Pyramids
