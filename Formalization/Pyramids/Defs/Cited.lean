/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.PaperVI
import AffineHemigroup.Defs.Origin
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The vocabulary of chapter 2's opening: what is cited

Blueprint: `blueprint/src/parts/02-cited-facts.tex`. Definitions only: nothing in this file
claims anything, and every identity the chapter's nodes state about these objects is a skeleton
statement (`PyramidsSkeleton.Ch02CitedFacts`).

## What the shared libraries already supply, and is not repeated here

* `def:cascade-measurement-family` is the shared core's `ScaleSpace.CascadeFamily` (home
  `line:def:cascade-family`).
* `def:isotropic-cascade-family` is the affine export's `AffineHemigroup.IsIsotropicCascadeFamily`
  (with `∃ S`, (I4) asserting that an action exists).
* `def:isotropic-origin-data` is the affine export's `AffineHemigroup.OriginDatum`, with
  `OriginDatum.levyMeasure`, `OriginDatum.exponent`, `IsLawOf` and `sphereArea`.
* `def:self-decomposable`, its first sentence, is `ScaleSpace.IsSelfDecomposable` (the measure
  form, `c = b⁻¹`) and, at Sato's letter, `AffineHemigroup.IsSelfDecomposableSato`; the two are
  the same class for a finite measure (`AffineHemigroup.isSelfDecomposable_iff_sato`).
* Infinite divisibility, generating triplets and `HasTriplet` are the affine export's
  `IsInfinitelyDivisible`, `LevyTriplet`, `HasTriplet` (Sato Def. 7.1, Thm. 8.1).

## What is defined here

* the semi-selfdecomposable laws of `def:self-decomposable`, with the residual and the span;
* complete monotonicity, Bernstein, complete Bernstein and Thorin–Bernstein functions
  (`def:complete-bernstein`, `def:thorin-bernstein`, and the section lead before them);
* the vocabulary that the interface nodes introduce inside their statements: the lag sections
  of `thm:cited-A19`, the rational transforms of `thm:cited-A20`, the sign changes and Pólya
  frequency densities of `thm:cited-A22`–`thm:cited-A24`, submultiplicativity (`thm:cited-A49`),
  negative definiteness (`thm:cited-A57`) and the modified Bessel function `I_ν` (which the
  grid law of `Defs/Line.lean` reads).

## Readings fixed here

* **A Bernstein function** is read on `(0,∞)` from a function `ℝ → ℝ`: nonnegative there,
  differentiable there, with completely monotone derivative. **Completely monotone** is smooth on
  `(0,∞)` with `(-1)ⁿ f⁽ⁿ⁾ ≥ 0` there, the derivatives taken within `(0,∞)`.
* **"Its Lévy measure has a density `m`"** (Defs. 6.1 and 8.1 of Schilling–Song–Vondraček) is
  read as: `f` has a representation (3.2) whose measure is `m(t) dt`. Since the triplet of (3.2) is
  determined by `f` (SSV Thm. 3.2, p. 21, cited in the section lead), this is the same as saying
  that *the* Lévy measure of `f` has that density.
* **Sign changes in the essential sense.** `pointSignChanges g` is the supremum, over finite
  increasing point sequences, of the sign changes of the values with the zeros deleted;
  `essSignChanges g` is its infimum over the functions equal to `g` almost everywhere. This equals
  the supremum over the point sequences avoiding a null set (a version that is `0` on the null set
  adds no sign change), and it makes the count of an a.e.-defined function, such as a
  convolution of an integrable function, independent of the version.
* **A Pólya frequency density** is a probability density `φ` whose kernel `φ(x - y)` is totally
  positive of every order (Karlin, Ch. 7).
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set
open scoped ENNReal ComplexOrder

/-! ## Semi-selfdecomposable laws (`def:self-decomposable`) -/

section SemiSD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- **`ρ` is a residual of `μ` at `b`** (Sato, Def. 15.1, (15.1)): a probability measure with
`μ̂(z) = μ̂(b⁻¹z) ρ̂(z)` for every `z`. Self-decomposability at Sato's letter
(`AffineHemigroup.IsSelfDecomposableSato`) asks one for every `b > 1`. -/
def IsSDResidual (b : ℝ) (μ ρ : Measure E) : Prop :=
  IsProbabilityMeasure ρ ∧ ∀ z : E, charFun μ z = charFun μ (b⁻¹ • z) * charFun ρ z

/-- **`μ` is semi-selfdecomposable with span `b`** (`def:self-decomposable`; Sato, Def. 15.1):
`b > 1` and some infinitely divisible residual at `b`. -/
def IsSemiSelfDecomposableWithSpan (b : ℝ) (μ : Measure E) : Prop :=
  1 < b ∧ ∃ ρ : Measure E, IsSDResidual b μ ρ ∧ IsInfinitelyDivisible ρ

/-- **`μ` is semi-selfdecomposable** (`def:self-decomposable`; Sato, Def. 15.1): it has some
span. -/
def IsSemiSelfDecomposable (μ : Measure E) : Prop :=
  ∃ b : ℝ, IsSemiSelfDecomposableWithSpan b μ

end SemiSD

/-! ## Bernstein functions (`def:complete-bernstein`, `def:thorin-bernstein`) -/

/-- **Complete monotonicity on `(0,∞)`**: `f` is smooth on `(0,∞)` and `(-1)ⁿ f⁽ⁿ⁾ ≥ 0` there,
for every `n ≥ 0`. -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0) ∧
    ∀ (n : ℕ) (x : ℝ), 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDerivWithin n f (Ioi 0) x

/-- **A Bernstein function** (the lead of § 2.2.2): `f ≥ 0` on `(0,∞)`, differentiable there, with
completely monotone derivative. -/
def IsBernsteinFunction (f : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, 0 < x → 0 ≤ f x) ∧ DifferentiableOn ℝ f (Ioi 0) ∧
    IsCompletelyMonotone (derivWithin f (Ioi 0))

/-- **A complete Bernstein function** (`def:complete-bernstein`; SSV Def. 6.1, (6.1)): a Bernstein
function with a representation (3.2) whose Lévy measure has a completely monotone density `m`,
`f(λ) = a + bλ + ∫_{(0,∞)} (1 - e^{-λt}) m(t) dt`, `a, b ≥ 0`, `∫ (1 ∧ t) m(t) dt < ∞`. -/
def IsCompleteBernstein (f : ℝ → ℝ) : Prop :=
  IsBernsteinFunction f ∧
    ∃ (a b : ℝ) (m : ℝ → ℝ), 0 ≤ a ∧ 0 ≤ b ∧ IsCompletelyMonotone m ∧
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (min 1 t * m t)) ≠ ⊤ ∧
      ∀ x : ℝ, 0 < x → f x = a + b * x + ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-(x * t))) * m t

/-- **A Thorin–Bernstein function** (`def:thorin-bernstein`; SSV Def. 8.1, (8.1)): a Bernstein
function with a representation (3.2) whose Lévy measure has a density `m` with `t ↦ t m(t)`
completely monotone, `a, b ≥ 0` and `∫ (1 ∧ t) m(t) dt < ∞`. -/
def IsThorinBernstein (f : ℝ → ℝ) : Prop :=
  IsBernsteinFunction f ∧
    ∃ (a b : ℝ) (m : ℝ → ℝ), 0 ≤ a ∧ 0 ≤ b ∧ IsCompletelyMonotone (fun t => t * m t) ∧
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (min 1 t * m t)) ≠ ⊤ ∧
      ∀ x : ℝ, 0 < x → f x = a + b * x + ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-(x * t))) * m t

/-! ## The Matérn family on the line and its lag sections (`thm:cited-A19`) -/

/-- **The kernels of the Matérn family of integer index `γ` on the line, in the canonical gauge**
(`thm:cited-A19`), by specification: probability measures `μ_{s,t}`, `0 ≤ s ≤ t`, with the cascade
`μ_{r,t} = μ_{s,t} ∗ μ_{r,s}` and the kernels from scale zero `μ̂_{0,t}(ω) = (1 + t²ω²)^{-γ}`. The
transform determines the law, and the cascade with the nonvanishing `μ̂_{0,s}` determines the
increments, so every such family is the Matérn family's. -/
structure IsMaternLineKernels (γ : ℕ) (μ : ℝ → ℝ → Measure ℝ) : Prop where
  isProbability : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)
  cascade : ∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t → μ r t = μ s t ∗ μ r s
  transform : ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ,
    charFun (μ 0 t) ω = ((((1 + t ^ 2 * ω ^ 2) ^ γ)⁻¹ : ℝ) : ℂ)

/-- **The causal first-order section** `r δ₀ + (1 - r) Exp₊(t)` of `thm:cited-A19`, with
`Exp₊(t)` the density `t⁻¹ e^{-x/t}` on `(0,∞)` (`expPlus`). -/
noncomputable def lagForward (r t : ℝ) : Measure ℝ :=
  ENNReal.ofReal r • Measure.dirac 0 +
    ENNReal.ofReal (1 - r) • (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (expPlus t x)

/-- **The anticausal first-order section** `r δ₀ + (1 - r) Exp₋(t)`, its mirror image. -/
noncomputable def lagBackward (r t : ℝ) : Measure ℝ :=
  ENNReal.ofReal r • Measure.dirac 0 +
    ENNReal.ofReal (1 - r) • (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (expMinus t x)

/-! ## Rational transforms (`thm:cited-A20`) -/

/-- **`R` is a symmetric rational function that is the transform of an infinitely divisible law
on `ℝ`, with folded Lévy profile `k_R`** (`thm:cited-A20`). `R` is a quotient of real polynomials
with no real zero of the denominator, even, the transform of an infinitely divisible probability
measure, and `-log R` is a symmetric Lévy exponent whose folded Lévy measure is `k_R(x) dx/x` on
`(0,∞)` (a pair of the shared core's `SymLevyPair`, Gaussian coefficient left free). -/
structure IsRationalLevyTransform (R kR : ℝ → ℝ) : Prop where
  rational : ∃ p q : Polynomial ℝ, ∀ ω : ℝ, q.eval ω ≠ 0 ∧ R ω = p.eval ω / q.eval ω
  even : ∀ ω : ℝ, R (-ω) = R ω
  isTransform : ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧ IsInfinitelyDivisible ρ ∧
    ∀ ω : ℝ, charFun ρ ω = (R ω : ℂ)
  kR_nonneg : ∀ x : ℝ, 0 < x → 0 ≤ kR x
  profile : ∃ P : ScaleSpace.SymLevyPair, P.ν = ScaleSpace.profileMeasure kR ∧
    ∀ ω : ℝ, R ω = Real.exp (-P.exponent ω)

/-! ## Sign changes and Pólya frequency densities (`thm:cited-A22`–`thm:cited-A24`) -/

open Classical in
/-- **The number of sign changes of a finite sequence**, the zeros deleted. -/
noncomputable def seqSignChanges (l : List ℝ) : ℕ :=
  let l' := l.filter fun x => x ≠ 0
  ((l'.zip l'.tail).filter fun p => p.1 * p.2 < 0).length

/-- **The sign changes of a function**, pointwise: the supremum over finite increasing point
sequences of the sign changes of its values. -/
noncomputable def pointSignChanges (g : ℝ → ℝ) : ℕ∞ :=
  ⨆ (n : ℕ) (x : Fin n → ℝ) (_ : StrictMono x),
    ((seqSignChanges (List.ofFn fun i => g (x i)) : ℕ) : ℕ∞)

/-- **`S⁻(g)`, the sign changes of `g` in the essential sense**: the least pointwise count among
the functions equal to `g` almost everywhere. -/
noncomputable def essSignChanges (g : ℝ → ℝ) : ℕ∞ :=
  ⨅ (g' : ℝ → ℝ) (_ : g' =ᵐ[volume] g), pointSignChanges g'

/-- **A Pólya frequency function** (Karlin, Ch. 7): the kernel `φ(x - y)` is totally positive of
every order, `det [φ(xᵢ - yⱼ)] ≥ 0` for all `x₁ < ⋯ < xₙ`, `y₁ < ⋯ < yₙ`. -/
def IsPolyaFrequencyFn (φ : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℝ), StrictMono x → StrictMono y →
    0 ≤ (Matrix.of fun i j => φ (x i - y j)).det

/-- **A Pólya frequency density**: a probability density that is a Pólya frequency function. -/
def IsPolyaFrequencyDensity (φ : ℝ → ℝ) : Prop :=
  IsPolyaFrequencyFn φ ∧ Integrable φ ∧ ∫ x, φ x = 1

/-- **A Pólya frequency kernel**: a measure with a Pólya frequency density. -/
def IsPolyaFrequencyKernel (μ : Measure ℝ) : Prop :=
  ∃ φ : ℝ → ℝ, IsPolyaFrequencyDensity φ ∧
    μ = (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (φ x)

/-! ## Submultiplicativity (`thm:cited-A49`) and negative definiteness (`thm:cited-A57`) -/

section Normed

variable {E : Type*} [NormedAddCommGroup E]

/-- **A submultiplicative function** (`thm:cited-A49`; Sato, Def. 25.2, (25.1)): nonnegative, and
`g(x + y) ≤ a g(x) g(y)` for all `x, y` and some constant `a > 0`. -/
def IsSubmultiplicative (g : E → ℝ) : Prop :=
  (∀ x : E, 0 ≤ g x) ∧ ∃ a : ℝ, 0 < a ∧ ∀ x y : E, g (x + y) ≤ a * g x * g y

/-- **A real negative definite function** (`thm:cited-A57`; SSV Def. 4.3 with (4.8), read for a
real function): even (hermitian, the function being real), and
`∑_{j,k} (ψ(ξⱼ) + ψ(ξₖ) - ψ(ξⱼ - ξₖ)) cⱼ c̄ₖ ≥ 0` in `ℂ` for all finite families. -/
def IsRealNegDef (ψ : E → ℝ) : Prop :=
  (∀ ξ : E, ψ (-ξ) = ψ ξ) ∧
    ∀ (n : ℕ) (ξ : Fin n → E) (c : Fin n → ℂ),
      0 ≤ ∑ j, ∑ k, ((ψ (ξ j) + ψ (ξ k) - ψ (ξ j - ξ k) : ℝ) : ℂ) * c j * starRingEnd ℂ (c k)

end Normed

/-! ## The modified Bessel function `I_ν` (the grid law, `Defs/Line.lean`) -/

/-- **`I_ν(z)`, the modified Bessel function of the first kind**, at real `z > 0`, by its series
(DLMF 10.25.2): `(z/2)^ν ∑_k (z²/4)^k / (k! Γ(ν + k + 1))`. Mathlib's `Real.Gamma` is `0` at the
poles, so the quotient is `0` there, as `1/Γ` is. `K_ν` is the shared core's
`ScaleSpace.besselK`, by DLMF 10.32.9. -/
noncomputable def besselI (ν z : ℝ) : ℝ :=
  (z / 2) ^ ν * ∑' k : ℕ, (z ^ 2 / 4) ^ k / (k.factorial * Real.Gamma (ν + k + 1))

end Pyramids
