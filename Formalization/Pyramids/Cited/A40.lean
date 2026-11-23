/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Interfaces

/-!
# Ledger A40: the transform of an infinitely divisible law has no zero (Sato, Lemma 7.5, p. 32)

Interface node `thm:cited-A40` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A40 of
`blueprint/AXIOMS.md`, cited from Sato, *Lévy Processes and Infinitely Divisible Distributions*,
Lemma 7.5, printed p. 32.

The author admitted A40 on 2026-11-13. **This file declares no axiom.** The statement follows in
two lines from clause (i) of the Lévy–Khintchine representation, which the affine export admits as
`AffineHemigroup.levy_khintchine_exists` (its ledger A3; this article's A39): the transform is the
complex exponential of the triplet's exponent, and the exponential has no zero. So `#print axioms`
names `levy_khintchine_exists` and nothing of A40's own. In Sato's book Lemma 7.5 precedes, and is
used in, the proof of Theorem 8.1; here the order is reversed, which is sound because Theorem 8.1(i)
is taken as given, not proved from Lemma 7.5.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory

variable {d : ℕ}

/-- **`thm:cited-A40`** (Sato, Lemma 7.5, p. 32). The transform of an infinitely divisible law on
`ℝ^d` has no zero. Proved from `cited_A39`(i), `AffineHemigroup.levy_khintchine_exists`. -/
theorem cited_A40 (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (hμ : IsInfinitelyDivisible μ)
    (z : Rd d) : charFun μ z ≠ 0 := by
  obtain ⟨T, hT⟩ := levy_khintchine_exists μ hμ
  rw [hT z]
  exact Complex.exp_ne_zero _

end Pyramids
