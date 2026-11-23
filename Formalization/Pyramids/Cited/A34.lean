/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.IsotropicClassification

/-!
# Ledger A34: every pair is realized (iso v0.1, Lem. 3.8, p. 14)

Interface node `thm:cited-A34` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A34 of
`blueprint/AXIOMS.md`, cited from the isotropic paper (iso v0.1), Lemma 3.8, printed p. 14.

The author admitted A34 on 2026-11-14. **This file declares no axiom, and the declaration rests on
none**: the affine export proves the lemma, `AffineHemigroup.isotropic_realisation`, from Lean core
alone (the residuals of `F`'s law, dilated by the gauge).
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory

variable {d : ℕ}

/-- **`thm:cited-A34`.** For a gauge `χ` and `F ∈ 𝒜_d`, `F ≢ 0`, there is an isotropic cascade
family with the display. The affine export's `AffineHemigroup.isotropic_realisation`; Lean core. -/
theorem cited_A34 (hd : 1 ≤ d) (χ F : ℝ → ℝ) (hχ : IsGauge χ) (hF : classA d F)
    (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) :
    ∃ μ : ℝ → ℝ → Measure (Rd d),
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)) ∧
      (∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily μ S) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ξ : Rd d,
        charFun (μ s t) ξ = ((Real.exp (-(F (χ t * ‖ξ‖) - F (χ s * ‖ξ‖))) : ℝ) : ℂ) :=
  isotropic_realisation hd χ F hχ hF hFne

end Pyramids
