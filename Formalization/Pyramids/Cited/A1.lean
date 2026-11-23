/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import ScaleSpaceCore.Representation
import ScaleSpaceCore.Transport

/-!
# Ledger A1: each operator is a convolution (V-line, Lemma 4.1)

Interface node `thm:cited-A1` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A1 of
`blueprint/AXIOMS.md`, cited from the line paper, Lemma 4.1.

On 2026-11-14 the author regraded the node `[T]`. **This file declares no axiom.** The shared core
ScaleSpaceCore proves the lemma with no axiom, and the three declarations below are its
statements, moved out of `PyramidsSkeleton.Ch02CitedFacts` unchanged in name and statement:

* `cited_A1_repr` is `ScaleSpace.representation_existsUnique`;
* `cited_A1_symm` writes the operator as `mconvL1 μ` (both sides are `μ * f` almost everywhere)
  and applies `ScaleSpace.isSymmetric_of_reflL1`;
* `cited_A1_converse` collects the core's lemmas on `mconvL1`: `coeFn_mconvL1`,
  `mconvL1_transL1`, `mconvL1_reflL1`, `isNonneg_mconvL1` and `integral_mconvL1`.

So `#print axioms` prints Lean core for each. In `cited_A1_symm` the hypotheses (A2), (A4) and
(A5) are not read, as the representation is given; they were dropped from its statement on
2026-11-14 (wave 2e), a strengthening. The node's printed statement keeps the source's letter.
-/

namespace Pyramids

open MeasureTheory
open ScaleSpace (X transL1 reflL1 IsPositive IsNonneg mconv mconvL1 IsSymmetric)

/-- **`thm:cited-A1`, existence and uniqueness.** Under (A1) (the type), (A2), (A4) and (A5), for
each pair `0 ≤ s ≤ t` there is a unique probability measure `μ_{s,t}` with `Φ_{s,t} f = μ_{s,t} * f`
for every `f ∈ L¹(ℝ)`, read in `L¹` (a.e. on representatives). The shared core proves this,
`ScaleSpace.representation_existsUnique`. -/
theorem cited_A1_repr (Φ : ℝ → ℝ → (X →L[ℝ] X))
    (htrans : ∀ s t, 0 ≤ s → s ≤ t → ∀ a f, Φ s t (transL1 a f) = transL1 a (Φ s t f))
    (hpos : IsPositive Φ)
    (hmass : ∀ s t, 0 ≤ s → s ≤ t → ∀ f, IsNonneg f →
      ∫ x, ((Φ s t f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ f : X, ((Φ s t f : X) : ℝ → ℝ) =ᵐ[volume] mconv μ (f : ℝ → ℝ) :=
  ScaleSpace.representation_existsUnique Φ htrans hpos hmass hs hst

/-- **`thm:cited-A1`, the symmetry under (A3).** The representing measure is symmetric. -/
theorem cited_A1_symm (Φ : ℝ → ℝ → (X →L[ℝ] X))
    (hrefl : ∀ s t, 0 ≤ s → s ≤ t → ∀ f, Φ s t (reflL1 f) = reflL1 (Φ s t f))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ f : X, ((Φ s t f : X) : ℝ → ℝ) =ᵐ[volume] mconv μ (f : ℝ → ℝ)) :
    IsSymmetric μ := by
  have hL : Φ s t = mconvL1 μ :=
    ContinuousLinearMap.ext fun f => Lp.ext ((hμ f).trans (ScaleSpace.coeFn_mconvL1 μ f).symm)
  exact ScaleSpace.isSymmetric_of_reflL1 hL (hrefl s t hs hst)

/-- **`thm:cited-A1`, the converse.** Every symmetric probability measure on `ℝ` defines, by
convolution, an operator with (A1)–(A5): `mconvL1 μ` is the bounded operator `f ↦ μ * f`. -/
theorem cited_A1_converse (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : IsSymmetric μ) :
    (∀ f : X, ((mconvL1 μ f : X) : ℝ → ℝ) =ᵐ[volume] mconv μ (f : ℝ → ℝ)) ∧
      (∀ a f, mconvL1 μ (transL1 a f) = transL1 a (mconvL1 μ f)) ∧
      (∀ f, mconvL1 μ (reflL1 f) = reflL1 (mconvL1 μ f)) ∧
      (∀ f, IsNonneg f → IsNonneg (mconvL1 μ f)) ∧
      ∀ f, IsNonneg f → ∫ x, ((mconvL1 μ f : X) : ℝ → ℝ) x = ∫ x, (f : ℝ → ℝ) x :=
  ⟨ScaleSpace.coeFn_mconvL1 μ, ScaleSpace.mconvL1_transL1, ScaleSpace.mconvL1_reflL1 hμ,
    ScaleSpace.isNonneg_mconvL1, fun f _ => ScaleSpace.integral_mconvL1 f⟩

end Pyramids
