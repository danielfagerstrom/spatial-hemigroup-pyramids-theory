/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.PolarClassification

/-!
# Ledger A35: the polar form of `𝒜_d` (iso v0.1, Prop. 3.11(1)–(2), pp. 15–16)

Interface node `thm:cited-A35` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A35 of
`blueprint/AXIOMS.md`, cited from the isotropic paper (iso v0.1), Proposition 3.11(1)–(2), printed
pp. 15–16.

The author admitted A35 on 2026-11-14. **This file declares no axiom.** The affine export proves
both clauses: `AffineHemigroup.polar_reading`, `polar_reading_unique`, `polar_reading_admissible`
and `classA_iff_originDatum`, at the statements typed here. They rest on the export's axioms
`levy_khintchine_exists`, `_unique`, `_converse` (this article's A39), `sato_polar_criterion`
(Sato Thm. 15.10, this article's A45) and `selfDecomposable_infinitelyDivisible` (Sato Prop. 15.5,
first clause, this article's A43), all admitted here; `#print axioms` names those and nothing of
A35's own.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set
open ScaleSpace (SDProfile IsSelfDecomposable)

variable {d : ℕ}

/-- **`thm:cited-A35`(1), the reading.** For `F ≥ 0` on `[0,∞)`: `ξ ↦ F(|ξ|)` is the exponent of a
self-decomposable law on `ℝ^d` if and only if it is the exponent `F_d` of an isotropic origin
datum. The affine export's `AffineHemigroup.polar_reading`. -/
theorem cited_A35_reading (hd : 1 ≤ d) (F : ℝ → ℝ) (hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r) :
    (∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsSelfDecomposable μ ∧
        ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ)) ↔
      ∃ D : OriginDatum d, ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ :=
  polar_reading hd F hF

/-- **`thm:cited-A35`(1), the uniqueness of the datum**: `a` is unique and `k_d` is unique up to
a Lebesgue-null set of `(0,∞)`. The affine export's `AffineHemigroup.polar_reading_unique`. -/
theorem cited_A35_unique (hd : 1 ≤ d) (F : ℝ → ℝ) (hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r)
    (D D' : OriginDatum d) (hD : ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ)
    (hD' : ∀ ξ : Rd d, F ‖ξ‖ = D'.exponent ξ) :
    D.a = D'.a ∧ D.k =ᵐ[volume.restrict (Ioi (0 : ℝ))] D'.k :=
  polar_reading_unique hd F hF D D' hD hD'

/-- **`thm:cited-A35`(2), the class.** If (1) holds, `F` has a datum `(a', k₁)` in dimension `1`,
and for it `F` is admissible on `[0,∞)` with Gaussian coefficient `a'/2` and profile `k₁`. The
affine export's `AffineHemigroup.polar_reading_admissible`. -/
theorem cited_A35_admissible (hd : 1 ≤ d) (F : ℝ → ℝ) (hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r)
    (h : ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsSelfDecomposable μ ∧
      ∀ ξ : Rd d, charFun μ ξ = ((Real.exp (-F ‖ξ‖) : ℝ) : ℂ)) :
    (∃ D₁ : OriginDatum 1, ∀ ξ : Rd 1, F ‖ξ‖ = D₁.exponent ξ) ∧
      ∀ D₁ : OriginDatum 1, (∀ ξ : Rd 1, F ‖ξ‖ = D₁.exponent ξ) →
        ∃ P : SDProfile, P.a = D₁.a / 2 ∧ (∀ x ∈ Ioi (0 : ℝ), P.k x = D₁.k x) ∧
          ∀ r : ℝ, 0 ≤ r → F r = P.exponent r :=
  polar_reading_admissible hd F hF h

/-- **`thm:cited-A35`(2), "so `𝒜_d` is …".** `F ∈ 𝒜_d` if and only if `F(|·|)` is the exponent of
an isotropic origin datum in dimension `d`. The affine export's
`AffineHemigroup.classA_iff_originDatum`. -/
theorem cited_A35_classA (hd : 1 ≤ d) (F : ℝ → ℝ) (hF : ∀ r : ℝ, 0 ≤ r → 0 ≤ F r) :
    classA d F ↔ ∃ D : OriginDatum d, ∀ ξ : Rd d, F ‖ξ‖ = D.exponent ξ :=
  classA_iff_originDatum hd F hF

end Pyramids
