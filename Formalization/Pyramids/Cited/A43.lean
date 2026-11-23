/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Cited
import Pyramids.Cited.A40

/-!
# Ledger A43: self-decomposable and semi-selfdecomposable laws are infinitely divisible
(Sato, Prop. 15.5, p. 93)

**This file widens the trust base of the article: it declares two axioms**, admitted by the author
on 2026-11-14. Ledger entry A43 of `blueprint/AXIOMS.md`, with its page transcription in
`blueprint/AXIOMS-verbatim.md`; interface node `thm:cited-A43`
(`blueprint/src/parts/02-cited-facts.tex`); listed in `blueprint/trust-boundary.txt`.

Source: Sato, *Lévy Processes and Infinitely Divisible Distributions*, Proposition 15.5, printed
p. 93: *"If `μ` is selfdecomposable, then `μ` is infinitely divisible and, for any `b > 1`, `ρ_b` in
(15.1) is uniquely determined and infinitely divisible. If `μ` is semi-selfdecomposable, then `μ` is
infinitely divisible and `ρ_b` is uniquely determined."* With the sentence after it: *"for any
`b > 1`, any selfdecomposable distribution is semi-selfdecomposable with `b` as a span."*

The proposition has five assertions. Only two are admitted here, each at the page's letter:

* "`μ` self-decomposable ⇒ `μ` infinitely divisible" is the affine export's axiom
  `AffineHemigroup.selfDecomposable_infinitelyDivisible` (its ledger A4, the same sentence of the
  same page), used by its own name and not declared again;
* "`ρ_b` is infinitely divisible" for a self-decomposable `μ` is the axiom
  `cited_A43_residual_infinitelyDivisible` (Sato's proof: Khintchine's theorem and the proof of his
  Thm. 15.3);
* "`μ` semi-selfdecomposable ⇒ `μ` infinitely divisible" is the axiom
  `cited_A43_semi_infinitelyDivisible` (Sato's proof: the closure of the class under weak limits,
  his Lemma 7.8);
* both uniqueness clauses are **proved**, by the page's own one-line argument: an infinitely
  divisible transform has no zero (`cited_A40`), so `ρ̂_b = μ̂ / μ̂(b⁻¹ ·)`, and the transform
  determines the law;
* the last sentence is **proved** from the first clause.

The skeleton's three declarations `cited_A43_sd`, `cited_A43_semi`, `cited_A43_span` are theorems
here, unchanged in statement and name. Neither admitted step is derived: each is a limit theorem
(a null array or a weak limit of infinitely divisible laws) whose proof from Khintchine's theorem
(A41, admitted) needs tail bounds from transforms and a construction of the array, several hundred
lines each.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory

variable {d : ℕ}

/-- **Ledger A43, the residual of a self-decomposable law** (Sato, Prop. 15.5, p. 93): if `μ` is
self-decomposable, then for every `b > 1` the residual `ρ_b` of (15.1) is infinitely divisible.
Stated for every residual, which is the same as for "the" residual, since the residual is unique
(`isSDResidual_unique`). Admitted by the author on 2026-11-14. -/
axiom cited_A43_residual_infinitelyDivisible (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsSelfDecomposableSato μ) {b : ℝ} (hb : 1 < b) (ρ : Measure (Rd d))
    (hρ : IsSDResidual b μ ρ) : IsInfinitelyDivisible ρ

/-- **Ledger A43, a semi-selfdecomposable law** (Sato, Prop. 15.5, p. 93): if `μ` is
semi-selfdecomposable, then `μ` is infinitely divisible. Admitted by the author on 2026-11-14. -/
axiom cited_A43_semi_infinitelyDivisible (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsSemiSelfDecomposable μ) : IsInfinitelyDivisible μ

/-- The residual of an infinitely divisible law at `b` is unique: the transform of `μ` has no zero
(`cited_A40`), so `ρ̂(z) = μ̂(z) / μ̂(b⁻¹z)`, and the transform determines the law. Sato's own
argument, p. 93. -/
theorem isSDResidual_unique (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsInfinitelyDivisible μ) {b : ℝ} {ρ ρ' : Measure (Rd d)} (hρ : IsSDResidual b μ ρ)
    (hρ' : IsSDResidual b μ ρ') : ρ = ρ' := by
  obtain ⟨hp, h⟩ := hρ
  obtain ⟨hp', h'⟩ := hρ'
  haveI := hp; haveI := hp'
  refine Measure.ext_of_charFun (funext fun z => ?_)
  have hne := cited_A40 μ hμ (b⁻¹ • z)
  have := (h z).symm.trans (h' z)
  exact mul_left_cancel₀ hne this

/-- **`thm:cited-A43`, the self-decomposable case**: `μ` is infinitely divisible and, for every
`b > 1`, the residual is unique and infinitely divisible. The infinite divisibility of `μ` is the
affine export's axiom `selfDecomposable_infinitelyDivisible`; that of the residual is
`cited_A43_residual_infinitelyDivisible`; the uniqueness is `isSDResidual_unique`. -/
theorem cited_A43_sd (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsSelfDecomposableSato μ) :
    IsInfinitelyDivisible μ ∧ ∀ b : ℝ, 1 < b →
      (∃! ρ : Measure (Rd d), IsSDResidual b μ ρ) ∧
        ∀ ρ : Measure (Rd d), IsSDResidual b μ ρ → IsInfinitelyDivisible ρ := by
  have hID := selfDecomposable_infinitelyDivisible μ hμ
  refine ⟨hID, fun b hb => ⟨?_, fun ρ hρ => cited_A43_residual_infinitelyDivisible μ hμ hb ρ hρ⟩⟩
  obtain ⟨ρ, hp, hρ⟩ := hμ b hb
  exact ⟨ρ, ⟨hp, hρ⟩, fun ρ' hρ' => isSDResidual_unique μ hID hρ' ⟨hp, hρ⟩⟩

/-- **`thm:cited-A43`, the semi-selfdecomposable case**: `μ` is infinitely divisible and the
residual at a span is unique (among probability measures). The infinite divisibility is
`cited_A43_semi_infinitelyDivisible`; the uniqueness is `isSDResidual_unique`. -/
theorem cited_A43_semi (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsSemiSelfDecomposable μ) :
    IsInfinitelyDivisible μ ∧ ∀ (b : ℝ) (ρ ρ' : Measure (Rd d)),
      IsSemiSelfDecomposableWithSpan b μ → IsSDResidual b μ ρ → IsSDResidual b μ ρ' → ρ = ρ' := by
  have hID := cited_A43_semi_infinitelyDivisible μ hμ
  exact ⟨hID, fun b ρ ρ' _ hρ hρ' => isSDResidual_unique μ hID hρ hρ'⟩

/-- **`thm:cited-A43`, the last sentence**: a self-decomposable law is semi-selfdecomposable with
every `b > 1` as a span. From the residual's existence (the definition) and its infinite
divisibility (`cited_A43_residual_infinitelyDivisible`). -/
theorem cited_A43_span (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsSelfDecomposableSato μ) {b : ℝ} (hb : 1 < b) :
    IsSemiSelfDecomposableWithSpan b μ := by
  obtain ⟨ρ, hp, hρ⟩ := hμ b hb
  exact ⟨hb, ρ, ⟨hp, hρ⟩, cited_A43_residual_infinitelyDivisible μ hμ hb ρ ⟨hp, hρ⟩⟩

end Pyramids
