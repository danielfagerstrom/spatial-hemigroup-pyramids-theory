/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.IsotropicClassification

/-!
# Ledger A31: the classification in `ℝ^d` (iso v0.1, Thm. 3.6, p. 13)

Interface node `thm:cited-A31` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A31 of
`blueprint/AXIOMS.md`, cited from the isotropic paper (iso v0.1), Theorem 3.6, printed p. 13.

The author admitted A31 on 2026-11-14. **This file declares no axiom.** The affine export, which
this development requires, proves the theorem: `AffineHemigroup.isotropic_classification` (the
equivalence) rests on the export's Lévy–Khintchine axioms `levy_khintchine_unique` and
`levy_khintchine_converse` (this article's A39, already admitted), and
`AffineHemigroup.isotropic_classification_unique` on Lean core alone. The export's uniqueness is the
page's wider form, against any real `F'` with `F'(0) = 0`; the statement here asks `F' ∈ 𝒜_d`, which
gives `F'(0) = 0` (`classA_zero`).
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory

variable {d : ℕ}

/-- **`thm:cited-A31`, the equivalence.** A family of probability measures on `ℝ^d` is an
isotropic cascade family if and only if it has the form `exp(-[F(χ(t)|ω|) - F(χ(s)|ω|)])` for a
gauge `χ` and an `F ∈ 𝒜_d` (`classA`), `F ≢ 0` on `[0,∞)`. The affine export's theorem
`AffineHemigroup.isotropic_classification`. -/
theorem cited_A31 (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) :
    (∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily μ S) ↔
      ∃ (χ : ℝ → ℝ) (F : ℝ → ℝ), IsGauge χ ∧ classA d F ∧ (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
          charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) :=
  isotropic_classification hd μ hprob

/-- **`thm:cited-A31`, the uniqueness.** A second pair `(χ', F')`, `χ'` a gauge and `F' ∈ 𝒜_d`,
with the same display is `(cχ, F(c⁻¹ ·))` for some `c > 0`, and `c = 1` when `χ(1) = χ'(1) = 1`.
The affine export's `AffineHemigroup.isotropic_classification_unique`, with `F'(0) = 0` from
`F' ∈ 𝒜_d`. Lean core. -/
theorem cited_A31_unique (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) (χ F : ℝ → ℝ)
    (hχ : IsGauge χ) (hF : classA d F) (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0)
    (hrep : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ))
    (χ' F' : ℝ → ℝ) (hχ' : IsGauge χ') (hF' : classA d F')
    (hrep' : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
      charFun (μ s t) ξ = ((Real.exp (-(F' (χ' t * ‖ξ‖) - F' (χ' s * ‖ξ‖))) : ℝ) : ℂ)) :
    ∃ c : ℝ, 0 < c ∧ (∀ t : ℝ, 0 ≤ t → χ' t = c * χ t) ∧
      (∀ r : ℝ, 0 ≤ r → F' r = F (c⁻¹ * r)) ∧ (χ 1 = 1 → χ' 1 = 1 → c = 1) :=
  isotropic_classification_unique hd μ hprob χ F hχ hF hFne hrep χ' F' hχ' (classA_zero hF') hrep'

end Pyramids
