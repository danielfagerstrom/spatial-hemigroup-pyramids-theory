/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Cited
import ScaleSpaceCore.SDProfile
import ScaleSpaceCore.L1Operators

/-!
# Ledger A22: the Pólya frequency members (V-selection v0.1, Prop. 4.5(1), p. 35, the "if")

**This file widens the trust base of the article: it declares two axioms**, admitted by the
author on 2026-11-15 (`adr/0005-a22-and-a24-admitted.md`). Ledger entry A22 of
`blueprint/AXIOMS.md`, with its page transcription in `blueprint/AXIOMS-verbatim.md`; interface
node `thm:cited-A22` (`blueprint/src/parts/02-cited-facts.tex`); both names are listed in
`blueprint/trust-boundary.txt`.

Source: V-selection v0.1 (`fagerstrom2026selection`), Proposition 4.5(1), printed p. 35, the "if"
half of its equivalence (the entry's verdict NARROWER-OK). The page's hypothesis is "an
admissible family" with exponent `F(ω) = aω² + ∑ᵢ log(1 + ω²/θᵢ²)`, `θᵢ > 0`, `∑ θᵢ⁻² < ∞`; both
axioms keep "admissible", and both take `F ≢ 0`, the presupposition of "an admissible family"
(the skeleton review, m1; the interface node states it). Not carried: the "only if"; the page's
list of members and non-members; the admissibility of the exponents the spenders apply it to,
which they prove.

**The two clauses.**

* `cited_A22_polya`: the kernels `μ_t`, `μ̂_t = e^{-F(t·)}`, are Pólya frequency kernels
  (`IsPolyaFrequencyKernel`: a density whose translation kernel is totally positive of every
  order). The skeleton's statement, unchanged.
* `cited_A22_variation`: `S⁻(μ_t * g) ≤ S⁻(g)` for every `t > 0` and every integrable or bounded
  (measurable) `g`, `S⁻` the sign changes in the essential sense (`essSignChanges`). The
  skeleton's statement **with `F ≢ 0` added**: the skeleton typed it without, a statement true at
  `F ≡ 0` too (the kernel is `δ₀`), but the page's range is an admissible family, so the axiom is
  admitted at the page's range and narrower than the skeleton's type. The case `F ≡ 0`, which the
  page does not cover, is proved where it is needed (`Pyramids.Cited.A23`).

The kernels are quantified over by specification: any probability measures with the stated
transforms (the skeleton's finding 1); the transform determines the law, so nothing is lost.

Not derived from the admitted entries: the pricing (`records/pyramids/PRICE-unadmitted-entries.md`,
A22) found a proof at about 3400–5000 lines of total positivity library that Mathlib lacks, and
the author admitted the entry instead.
-/

namespace Pyramids

open MeasureTheory
open ScaleSpace (IsAdmissibleExponent mconv)

/-- **`thm:cited-A22`, variation diminution, ledger A22** (V-selection v0.1, Prop. 4.5(1), p. 35,
the "if"). For an admissible `F ≢ 0` of the form `F(ω) = aω² + ∑ᵢ log(1 + ω²/θᵢ²)` (`a ≥ 0`,
countably many `θᵢ > 0`, `∑ θᵢ⁻² < ∞`) and kernels `μ̂_t = e^{-F(t ·)}`: `S⁻(μ_t * g) ≤ S⁻(g)`
for every `t > 0` and every integrable or bounded (measurable) `g`. Admitted by the author on
2026-11-15. -/
axiom cited_A22_variation {ι : Type*} [Countable ι] (F : ℝ → ℝ) (hF : IsAdmissibleExponent F)
    (hFne : ∃ ω : ℝ, F ω ≠ 0)
    (a : ℝ) (ha : 0 ≤ a) (θ : ι → ℝ) (hθ : ∀ i, 0 < θ i) (hsum : Summable fun i => (θ i ^ 2)⁻¹)
    (hform : ∀ ω : ℝ, F ω = a * ω ^ 2 + ∑' i, Real.log (1 + ω ^ 2 / θ i ^ 2))
    (μ : ℝ → Measure ℝ) (hμ : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hμF : ∀ t : ℝ, 0 < t → ∀ ω : ℝ, charFun (μ t) ω = ((Real.exp (-F (t * ω)) : ℝ) : ℂ))
    {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ)
    (hg : Integrable g ∨ (AEStronglyMeasurable g volume ∧ ∃ C : ℝ, ∀ x, |g x| ≤ C)) :
    essSignChanges (mconv (μ t) g) ≤ essSignChanges g

/-- **`thm:cited-A22`, the kernels are Pólya frequency kernels, ledger A22** (V-selection v0.1,
Prop. 4.5(1), p. 35, the "if"), for an admissible `F ≢ 0` of the form above. Admitted by the
author on 2026-11-15, at the skeleton's statement. -/
axiom cited_A22_polya {ι : Type*} [Countable ι] (F : ℝ → ℝ) (hF : IsAdmissibleExponent F)
    (hFne : ∃ ω : ℝ, F ω ≠ 0)
    (a : ℝ) (ha : 0 ≤ a) (θ : ι → ℝ) (hθ : ∀ i, 0 < θ i) (hsum : Summable fun i => (θ i ^ 2)⁻¹)
    (hform : ∀ ω : ℝ, F ω = a * ω ^ 2 + ∑' i, Real.log (1 + ω ^ 2 / θ i ^ 2))
    (μ : ℝ → Measure ℝ) (hμ : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hμF : ∀ t : ℝ, 0 < t → ∀ ω : ℝ, charFun (μ t) ω = ((Real.exp (-F (t * ω)) : ℝ) : ℂ))
    {t : ℝ} (ht : 0 < t) :
    IsPolyaFrequencyKernel (μ t)

end Pyramids
