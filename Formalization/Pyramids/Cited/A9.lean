/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.LineLevyUnique

/-!
# Ledger A9: the folded Lévy–Khintchine pair is unique (V-line Prop. 2.3(3), p. 9)

Interface node `thm:cited-A9` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A9 of
`blueprint/AXIOMS.md`, cited from the line paper (V-line v0.1), Proposition 2.3(3), printed p. 9,
whose sources note names Sato, Thm. 8.1, pp. 37–38 (this article's A39).

A9 is not admitted, and **needs no axiom of its own**: its statement is the shared core's hypothesis
`ScaleSpace.SymLevyUnique`, which the affine module discharges at `d = 1` from Sato's Thm. 8.1 as
`AffineHemigroup.line_levy_unique` (its `prop:line-levy-unique`): the converse clause (iii) gives a
law with the first pair's triplet, and the uniqueness clause (ii) identifies the two triplets. Both
clauses are this article's A39, admitted on 2026-11-13. So `#print axioms` names
`levy_khintchine_unique` and `levy_khintchine_converse` and nothing of A9's own. Wave 3d,
2026-11-14: the declaration moved here from `PyramidsSkeleton.Ch02CitedFacts`, unchanged in
statement and name.
-/

namespace Pyramids

open ScaleSpace (SymLevyPair)

/-- **`thm:cited-A9`.** Two pairs `(a, ν)`, `(a', ν')` (`a, a' ≥ 0`, `ν, ν'` on `(0,∞)` with
`∫ (1 ∧ x²) dν < ∞`: the shared core's `SymLevyPair`) with the same function
`aω² + ∫ (1 - cos ωx) ν(dx)` are equal. A theorem from A39(ii)–(iii), through the affine module's
`line_levy_unique`. -/
theorem cited_A9 (P Q : SymLevyPair) (h : ∀ ω : ℝ, P.exponent ω = Q.exponent ω) :
    P.a = Q.a ∧ P.ν = Q.ν :=
  AffineHemigroup.line_levy_unique P Q h

end Pyramids
