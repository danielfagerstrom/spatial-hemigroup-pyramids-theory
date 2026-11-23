/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.PaperVI
import Pyramids.Defs.Pyramid
import Pyramids.LineAppendix.LineExponentData
import Pyramids.Pyramid.FamilyStructure
import Pyramids.Cited.A1
import Pyramids.Cited.A22
import Pyramids.Cited.A23
import Pyramids.Cited.A24
import Pyramids.Cited.A31
import Pyramids.Cited.A34
import Pyramids.Cited.A35
import Pyramids.Cited.A39
import Pyramids.Cited.A4
import Pyramids.Cited.A40
import Pyramids.Cited.A41
import Pyramids.Cited.A42
import Pyramids.Cited.A43
import Pyramids.Cited.A44
import Pyramids.Cited.A45
import Pyramids.Cited.A46
import Pyramids.Cited.A48
import Pyramids.Cited.A49
import Pyramids.Cited.A50
import Pyramids.Cited.A51
import Pyramids.Cited.A9
import Pyramids.Defs.Cited
import ScaleSpaceCore.Representation
import ScaleSpaceCore.MainAnalysis
import ScaleSpaceCore.CinRays
import ScaleSpaceCore.StudentTransform
import ScaleSpaceCore.PolyaFrequencyClass
import ScaleSpaceCore.L1OperatorsSpace
import AffineHemigroup.Defs.Operators
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Pyramids.Defs.LineAppendix

/-!
# The target types of chapter 2's opening: the 28 interface nodes

(27 until review round 3, batch C, which added `thm:cited-A15`, decision D3.)

Blueprint: `blueprint/src/parts/02-cited-facts.tex`. **This file carries `sorry`s and is not part
of the proved library `Pyramids`.** Each `thm:cited-A<N>` is typed here as a theorem at the
page's letter and as the node states it as used, one declaration per clause where the node has
several. They are **not** axioms: admitting an interface is the author's decision (phase 5). The
definition nodes of the part are the shared declarations named in `Pyramids.Defs.Cited` and the
definitions made there.

## The interfaces admitted, and moved out (wave 2a)

On 2026-11-13 the author admitted seven entries: A39, A40, A41, A42, A46, A48, A51. Their
declarations moved, unchanged in statement and name, into the proved library, one file per entry,
`Pyramids.Cited.A<N>`, and are deleted here:

* `cited_A39_exists`, `cited_A39_unique`, `cited_A39_converse` are proved there as the affine
  export's axioms `levy_khintchine_exists`, `_unique`, `_converse` (its ledger A3);
* `cited_A40` is proved there from `levy_khintchine_exists`;
* `cited_A41` is proved there from the affine export's axiom `khintchine_null_array` (its ledger
  A6), with the law of an independent sum and a point mass put in front of each row;
* `cited_A51_integral` is proved there from the definition of `besselK` (DLMF 10.32.9) and the
  shared core's substitution, with no axiom;
* `cited_A42`, `cited_A46` and `cited_A48` are declared there as axioms and listed in
  `blueprint/trust-boundary.txt`; the node's former clause (2), `cited_A51_evaluations`, was
  dropped, as nothing read it. In review round 3 (batch C, 2026-11-23) `cited_A42` became a
  theorem, Lean core, and left the trust boundary, and `cited_A48` lost its finiteness clause,
  which `cited_A48_finite` proves.

## A1, regraded and moved out (2026-11-14)

On 2026-11-14 the author regraded `thm:cited-A1` `[T]`. Its three declarations, `cited_A1_repr`,
`cited_A1_symm` and `cited_A1_converse`, moved unchanged in statement and name into
`Pyramids.Cited.A1`, where they are proved from the shared core with no axiom, and are deleted
here. `cited_A1_symm` reads neither (A2), (A4) nor (A5); the three hypotheses were dropped from
its Lean statement on 2026-11-14 (wave 2e), a strengthening, while the node's printed statement
keeps the source's letter.

## The interfaces admitted on 2026-11-14, and moved out (wave 2f)

On 2026-11-14 the author admitted seven more entries: A31, A34, A35, A43, A45, A49, A50. Their
declarations moved, unchanged in statement and name, into `Pyramids.Cited.A<N>`, and are deleted
here:

* `cited_A31`, `cited_A31_unique`, `cited_A34` and the four `cited_A35_*` are proved there as the
  affine export's theorems (`isotropic_classification`, `_unique`, `isotropic_realisation`,
  `polar_reading`, `_unique`, `_admissible`, `classA_iff_originDatum`), which rest on the export's
  axioms for A39, A43 (first clause) and A45, or on none;
* `cited_A45` is the affine export's axiom `sato_polar_criterion` (its ledger A2);
* `cited_A43_sd`, `cited_A43_semi` and `cited_A43_span` are proved there from the export's axiom
  `selfDecomposable_infinitelyDivisible` (its ledger A4) and two new axioms,
  `cited_A43_residual_infinitelyDivisible` and `cited_A43_semi_infinitelyDivisible`; both uniqueness
  clauses are proved;
* `cited_A49` is declared there as an axiom;
* `cited_A50` is proved there, Lean core.

The other twelve entries stay here, typed with `sorry`, not admitted.

## A9 and A4, proved from A39 and moved out (wave 3d)

On 2026-11-14 (wave 3d) `cited_A9` moved, unchanged in statement and name, into
`Pyramids.Cited.A9`, where it is the affine module's `line_levy_unique`, proved from A39(ii)–(iii);
and `cited_A4`, `cited_A4_exists`, `cited_A4_unique` moved, unchanged in statement and name, into
`Pyramids.Cited.A4`, where they are proved from A39(ii)–(iii) (the shared core's analysis and
uniqueness, and its construction replayed with `line_exponent_data_1` in place of Bochner's
theorem). Neither entry is admitted; neither needs an axiom of its own. Then `cited_A44` moved,
unchanged in statement and name, into `Pyramids.Cited.A44`, where it is proved from A39 and A42
(Sato's own argument: the triplet of the image under `x ↦ b⁻¹x`, and the triplets of a
convolution add); it is not admitted and needs no axiom of its own. The other nine entries stay
here.

## A22 and A24, admitted and moved out (wave 3b)

On 2026-11-15 the author admitted A22 and A24 (`adr/0005-a22-and-a24-admitted.md`). Their
declarations moved into `Pyramids.Cited.A22` and `Pyramids.Cited.A24` as axioms, and are deleted
here. Both were admitted narrower than they were typed here, each to its citation's range:

* `cited_A22_polya`, unchanged in name and statement;
* `cited_A22_variation`, unchanged in name and conclusion, with the hypothesis `F ≢ 0` added
  (`hFne`): the page's range is an admissible family (finding 4), and the case `F ≡ 0` is proved
  where it is needed;
* `cited_A24`, unchanged in name and in its class (`γ ≥ 0`, `∑ aⱼ² < ∞`, `γ + ∑ aⱼ² > 0`, `ψ`
  entire, `ψ(0) = 1`), with the identity `L ψ = 1` stated on the imaginary axis `s = ωi` only and
  the strip and its absolute convergence dropped: both spenders read the identity only there
  (`records/pyramids/PRICE-unadmitted-entries.md`, A24).

A23 is not admitted: `cited_A23` moved, unchanged in name and statement, into `Pyramids.Cited.A23`,
where it is proved from `cited_A22_variation` (the page's own derivation, p. 39). The other seven
entries stay here.

## What writing it down found

1. **Laws by specification.** "The kernels of the similarity family of `F`" (`thm:cited-A13`,
   `thm:cited-A22`, `thm:cited-A23`) are any probability measures `μ t`, `t > 0`, with
   `μ̂_t(ω) = e^{-F(tω)}`; "the Matérn family" (`thm:cited-A19`) is any family meeting
   `IsMaternLineKernels`. The transform determines the law, so nothing is lost, and no family is
   constructed. Existence is a separate statement where a node claims it: `cited_A4_exists`
   (`thm:cited-A4`'s construction sentence, now `Pyramids.Cited.A4`) and `thm:cited-A34`. The
   equivalence `cited_A4` is
   about a *given* operator family, so its "if" alone does not say that the laws exist; the
   skeleton review (M1) found the construction untyped, and the node now prints it, as the
   theorem's "if" read for the measures its display names by their transforms (the page's text
   after the theorem calls it the "construction" clause).
2. **"The function `F` of `thm:cited-A20`"** is quantified over: every statement after the
   uniqueness clause `cited_A20_unique` takes any continuous `F` with `F(0) = 0` solving the
   equation, which the `∃!` makes the same as "the" `F`.
3. **`thm:cited-A20`, "admissible exactly when this `k` is nonincreasing"** is typed as "when `k`
   has a nonincreasing version": the profile `k_R` is a density, fixed only up to a null set, and
   with a modified `k_R` the pointwise reading is false (the page's own proof says "the
   monotonicity is monotonicity of a representative"). The sum `k = ∑_{m≥1} k_R(q^m ·)` is taken in
   `[0,∞]`, so it has no junk value where it diverges. "In particular whenever `k_R` is" is typed
   pointwise. The node now prints the version reading (skeleton review, m2).
4. **`thm:cited-A22`, "Pólya frequency kernels".** A Pólya frequency density is a probability
   density (Karlin), so `δ₀`, the kernel of `F ≡ 0`, is not one. The form of the node allows
   `F ≡ 0` (`a = 0`, no `θ_i`), whose "similarity family" does not exist (`thm:cited-A4` asks
   `F ≢ 0`). So the Pólya frequency clause `cited_A22_polya` takes `F ≢ 0`, the presupposition of
   "the similarity family of `F`", and the variation-diminishing clause `cited_A22_variation`,
   true for `δ₀` too, does not. The node now states `F ≢ 0` (skeleton review, m1), so
   `cited_A22_variation` is stronger than the node by that hypothesis, and true.
5. **Sign changes in the essential sense** (`essSignChanges`) are the least pointwise count over
   the a.e.-versions; a convolution of an integrable `g` is defined a.e. only, and the count does
   not see the null set where the Bochner integral takes its junk value. `∂ₓ u(t,·)` in
   `thm:cited-A23` is `deriv`, whose junk value `0` sits on the null set where `u(t,·)`, an
   absolutely continuous function, is not differentiable, and zeros are deleted before counting.
6. **The realization of `thm:cited-A19`** is typed for every integrable input `y`: the state
   equation `w' = (y - w)/t_{k+1}` in its integral form `w(b) - w(a) = ∫_a^b (y - w)/t_{k+1}`, the
   reading of a differential equation with an `L¹` forcing, which for a continuous `y` gives the
   pointwise one; "the solution in `L¹`" is the conjunction: `w` is integrable, tends to `0` at
   `-∞`, and is the only integrable solution.
7. **`thm:cited-A51` at real `z > 0` only.** Mathlib has no complex Bessel functions. `K_ν` is
   the shared core's `ScaleSpace.besselK`, defined by DLMF 10.32.9 at real `z > 0`, and `I_ν` is
   `besselI`, defined by its series DLMF 10.25.2. The node's clause (1) is narrowed to real
   `z > 0` (skeleton review, M2), the range of its one spender, `lem:bessel-k`; the page's complex
   sector `|ph z| < π/4` is in the node's annotation only.
8. **Random variables at the letter** (`thm:cited-A41`): the null array is a family of measurable
   maps on one probability space, independent within each row (`iIndepFun`), with the law of
   `S_n - b_n` converging against every bounded continuous function. The rows may be empty; the
   statement is then still true (a row sum of `0`), so no narrowing is needed.
9. **Supports** are read through measure: "the support of `μ` is unbounded" (`thm:cited-A46`) is
   `μ{|x| > R} ≠ 0` for every `R`, and "contained in `ℤ`" (`thm:cited-A48`) is "the complement of
   `ℤ` is null", equivalent because `ℤ` is closed and the support is the complement of the largest
   open null set. `ℝ` in `thm:cited-A48` is `ℝ¹ = Rd 1`, the space `LevyTriplet 1` lives on.
10. **Gauges** are the affine export's `IsGauge`, `χ(0) = 0` with `χ` strictly increasing and
   onto `[0,∞)`, which says "increasing bijection of `[0,∞)`" (`isGauge_iff_isIncreasingBijection`).
11. **`thm:cited-A4` over continuous operators.** "A family of linear operators on `L¹(ℝ)`
   satisfies (A1)–(A8) and (ND)" is typed for `Φ s t : X →L[ℝ] X`: (A1) is the type, and both sides
   of the equivalence are false for an unbounded `Φ` (the right side's operators are convolutions).
12. **"Unique up to `(χ, F) ↦ (cχ, F(c⁻¹·))`"** (`thm:cited-A31`) is typed as: every second pair
   (a gauge and an `F' ∈ 𝒜_d`) is in the orbit, `F'` read on `[0,∞)` as `𝒜_d` reads it.
13. **"Imposes no restriction on `A` and `γ`"** (`thm:cited-A44`, `thm:cited-A45`) is the form of
   the equivalence itself, whose right side reads `ν` only; it is not a separate declaration.
14. **`thm:cited-A57`, the value at `0`.** The node writes `f(|ω|²)` at `ω = 0` for `f` on
   `(0,∞)`; the page reads `f(0)` as the limit (the mass `e^{-tf(0)}` of its (13.21)), so the
   statement takes `f(0) = 0` beside `f(0+) = 0`. The node now states the convention (skeleton
   review, m6).
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set Filter
open ScaleSpace (X transL1 reflL1 IsPositive IsNonneg mconv mconvL1 IsKernelFamily SDProfile
  IsSymmetric SymLevyPair mconvE mconvL1E besselK cinSDProfile laplaceLaw IsAdmissibleExponent
  polyaE2 IsSelfDecomposable convPow CascadeFamily)
open scoped Topology ENNReal SchwartzMap BoundedContinuousFunction ComplexOrder NNReal

variable {d : ℕ}

/-! ## `thm:cited-A9` — moved to `Pyramids.Cited.A9` (wave 3d) -/

/-! ## `thm:cited-A4` — moved to `Pyramids.Cited.A4` (wave 3d) -/

/-! ## `thm:cited-A30` [A, A30] — operators and kernels in dimension `d` (iso Lem. 3.3(1)–(2)) -/

/-- **`thm:cited-A30`(1), the representation.** A bounded linear `Φ` on `L¹(ℝ^d)` commuting with
translations, positive and mass-preserving on nonnegative functions (`IsSingleOperator`) is
convolution by a unique probability measure. The affine export proves it,
`AffineHemigroup.operators_to_kernels_repr`. -/
theorem cited_A30_repr (hd : 1 ≤ d) (Φ : L1 d →L[ℝ] L1 d) (hΦ : IsSingleOperator Φ) :
    ∃! μ : Measure (Rd d), IsProbabilityMeasure μ ∧
      ∀ f : L1 d, ((Φ f : L1 d) : Rd d → ℝ) =ᵐ[volume] mconvE μ (f : Rd d → ℝ) := by
  sorry

/-- **`thm:cited-A30`(1), the converse.** For every probability measure `μ` on `ℝ^d`, `f ↦ μ * f`
(`mconvL1E μ`) has the four properties. The affine export proves the four,
`AffineHemigroup.operators_to_kernels_converse`. -/
theorem cited_A30_converse (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ] :
    (∀ f : L1 d, ((mconvL1E μ f : L1 d) : Rd d → ℝ) =ᵐ[volume] mconvE μ (f : Rd d → ℝ)) ∧
      IsSingleOperator (mconvL1E μ) := by
  sorry

/-- **`thm:cited-A30`(2), the continuity.** `μ̂_n → μ̂` pointwise if and only if `μ_n * f → μ * f`
in `L¹(ℝ^d)` for every `f`. -/
theorem cited_A30_continuity (hd : 1 ≤ d) (μn : ℕ → Measure (Rd d))
    [∀ n, IsProbabilityMeasure (μn n)] (μ : Measure (Rd d)) [IsProbabilityMeasure μ] :
    (∀ ξ : Rd d, Tendsto (fun n => charFun (μn n) ξ) atTop (𝓝 (charFun μ ξ))) ↔
      ∀ f : L1 d, Tendsto (fun n => mconvL1E (μn n) f) atTop (𝓝 (mconvL1E μ f)) := by
  sorry

/-! ## `thm:cited-A31`, `thm:cited-A34`, `thm:cited-A35` — moved to `Pyramids.Cited.A31`,
`A34`, `A35` (wave 2f) -/

/-! ## `thm:cited-A13` [A, A13] — the generator of a Cin ray (V-cone Prop. 6.4(5)) -/

/-- **`thm:cited-A13`.** For the Cin ray of step `τ` (data `(0, 1_{(0,τ)})`, the shared core's
`cinSDProfile τ`), kernels `μ_t` with `μ̂_t(ω) = e^{-F(tω)}` and a Schwartz `f`, the scale space
`u(t,x) = (μ_t * f)(x)` has, at every `t > 0` and every `x`,
`∂_t u(t,x) = t⁻¹ (½(u(t, x - tτ) + u(t, x + tτ)) - u(t,x))`. -/
theorem cited_A13 {τ : ℝ} (hτ : 0 < τ) (μ : ℝ → Measure ℝ)
    (hμ : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hμF : ∀ t : ℝ, 0 < t → ∀ ω : ℝ,
      charFun (μ t) ω = ((Real.exp (-(cinSDProfile τ).exponent (t * ω)) : ℝ) : ℂ))
    (f : 𝓢(ℝ, ℝ)) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => mconv (μ s) f x)
      (t⁻¹ * ((mconv (μ t) f (x - t * τ) + mconv (μ t) f (x + t * τ)) / 2 - mconv (μ t) f x))
      t := by
  sorry

/-! ## `thm:cited-A15` [A, A15] — the Choquet structure of the admissible cone (V-cone Prop. 3.3)

Added in review round 3, batch C (decision D3), stated for the reader. The superposition map
`(a, ϖ) ↦ F`, `F(ω) = a ω² + ∫ Cin(τω) ϖ(dτ)`, typed in four declarations: into the cone, injective,
onto with the inverse `k(x) = ϖ((x,∞))`, and the extreme rays. A measure on `(0,∞)` is a measure
on `ℝ` with no mass on `(-∞, 0]`; the shared core's `cin` is the entire cosine integral, even on
`ℝ`. -/

/-- The domain of `thm:cited-A15`: `a ≥ 0`, `ϖ` a measure on `(0,∞)` with
`∫ τ² ∧ (1 + log₊ τ) ϖ(dτ) < ∞`. -/
def IsChoquetPair (a : ℝ) (ϖ : Measure ℝ) : Prop :=
  0 ≤ a ∧ ϖ (Iic 0) = 0 ∧
    ∫⁻ τ, ENNReal.ofReal (min (τ ^ 2) (1 + Real.posLog τ)) ∂ϖ ≠ ⊤

/-- The superposition `a ω² + ∫ Cin(τω) ϖ(dτ)` of `thm:cited-A15`. -/
noncomputable def choquetExponent (a : ℝ) (ϖ : Measure ℝ) (ω : ℝ) : ℝ :=
  a * ω ^ 2 + ∫ τ, ScaleSpace.cin (τ * ω) ∂ϖ

/-- **`thm:cited-A15`, into the cone.** The superposition of a pair of the domain is admissible. -/
theorem cited_A15_admissible {a : ℝ} {ϖ : Measure ℝ} (h : IsChoquetPair a ϖ) :
    IsAdmissibleExponent (choquetExponent a ϖ) := by
  sorry

/-- **`thm:cited-A15`, injective.** Two pairs of the domain with the same superposition are
equal. -/
theorem cited_A15_injective {a₁ a₂ : ℝ} {ϖ₁ ϖ₂ : Measure ℝ} (h₁ : IsChoquetPair a₁ ϖ₁)
    (h₂ : IsChoquetPair a₂ ϖ₂) (h : choquetExponent a₁ ϖ₁ = choquetExponent a₂ ϖ₂) :
    a₁ = a₂ ∧ ϖ₁ = ϖ₂ := by
  sorry

/-- **`thm:cited-A15`, onto, with the inverse.** The exponent of the data `(a, k)` is the
superposition of `(a, ϖ)` with `ϖ((x,∞)) = k(x)` for almost every `x > 0`: `ϖ = -dk`, `k` being
fixed by the exponent only up to a null set. -/
theorem cited_A15_inverse (P : SDProfile) :
    ∃ ϖ : Measure ℝ, IsChoquetPair P.a ϖ ∧
      (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ϖ (Ioi x) = ENNReal.ofReal (P.k x)) ∧
      ∀ ω : ℝ, P.exponent ω = choquetExponent P.a ϖ ω := by
  sorry

/-- **`thm:cited-A15`, the extreme rays.** The extreme rays of the cone of admissible exponents are
the Gaussian ray `ω ↦ ω²` and the Cin rays `ω ↦ Cin(τω)`, `τ > 0`. -/
theorem cited_A15_extreme (ψ : ℝ → ℝ) :
    IsExtremeRayIn {F : ℝ → ℝ | IsAdmissibleExponent F} ψ ↔
      ∃ c : ℝ≥0, c ≠ 0 ∧ (ψ = c • (fun ω : ℝ => ω ^ 2) ∨
        ∃ τ : ℝ, 0 < τ ∧ ψ = c • fun ω : ℝ => ScaleSpace.cin (τ * ω)) := by
  sorry

/-! ## `thm:cited-A19` [A, A19] — the Matérn cascade by first-order sections (V-cone Prop. 7.2) -/

/-- **`thm:cited-A19`, the increment.** For adjacent knots `0 < t_k < t_{k+1}`,
`μ̂_{t_k,t_{k+1}}(ω) = ((1 + t_k²ω²)/(1 + t_{k+1}²ω²))^γ`. -/
theorem cited_A19_transform {γ : ℕ} (hγ : 1 ≤ γ) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsMaternLineKernels γ μ) {tk tk1 : ℝ} (h0 : 0 < tk) (h1 : tk < tk1) (ω : ℝ) :
    charFun (μ tk tk1) ω =
      ((((1 + tk ^ 2 * ω ^ 2) / (1 + tk1 ^ 2 * ω ^ 2)) ^ γ : ℝ) : ℂ) := by
  sorry

/-- **`thm:cited-A19`, the cascade of sections.** The increment is `γ` causal sections
`r δ₀ + (1 - r) Exp₊(t_{k+1})` convolved with `γ` anticausal ones, `r = t_k/t_{k+1}`. -/
theorem cited_A19_sections {γ : ℕ} (hγ : 1 ≤ γ) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsMaternLineKernels γ μ) {tk tk1 : ℝ} (h0 : 0 < tk) (h1 : tk < tk1) :
    μ tk tk1 = convPow (lagForward (tk / tk1) tk1) γ ∗ convPow (lagBackward (tk / tk1) tk1) γ := by
  sorry

/-- **`thm:cited-A19`, the realization of a causal section**, for an integrable input `y`: the
state `w = Exp₊(t_{k+1}) * y` is integrable, solves `w' = (y - w)/t_{k+1}` (integral form), tends
to `0` at `-∞` and is the only integrable solution, and the output `r y + (1 - r) w` is the
section's convolution with `y`. -/
theorem cited_A19_forward {tk tk1 : ℝ} (h0 : 0 < tk) (h1 : tk < tk1) (y : ℝ → ℝ)
    (hy : Integrable y) :
    Integrable (fun x => ∫ z, expPlus tk1 z * y (x - z)) ∧
      (∀ a b : ℝ, (∫ z, expPlus tk1 z * y (b - z)) - ∫ z, expPlus tk1 z * y (a - z) =
        ∫ x in a..b, (y x - ∫ z, expPlus tk1 z * y (x - z)) / tk1) ∧
      Tendsto (fun x => ∫ z, expPlus tk1 z * y (x - z)) atBot (𝓝 0) ∧
      (∀ w : ℝ → ℝ, Integrable w → (∀ a b : ℝ, w b - w a = ∫ x in a..b, (y x - w x) / tk1) →
        w = fun x => ∫ z, expPlus tk1 z * y (x - z)) ∧
      ∀ x : ℝ, ∫ z, y (x - z) ∂(lagForward (tk / tk1) tk1) =
        tk / tk1 * y x + (1 - tk / tk1) * ∫ z, expPlus tk1 z * y (x - z) := by
  sorry

/-- **`thm:cited-A19`, the realization of an anticausal section**, its mirror image run backward:
`w = Exp₋(t_{k+1}) * y` solves `w' = (w - y)/t_{k+1}`, tends to `0` at `+∞`, and is the only
integrable solution. -/
theorem cited_A19_backward {tk tk1 : ℝ} (h0 : 0 < tk) (h1 : tk < tk1) (y : ℝ → ℝ)
    (hy : Integrable y) :
    Integrable (fun x => ∫ z, expMinus tk1 z * y (x - z)) ∧
      (∀ a b : ℝ, (∫ z, expMinus tk1 z * y (b - z)) - ∫ z, expMinus tk1 z * y (a - z) =
        ∫ x in a..b, ((∫ z, expMinus tk1 z * y (x - z)) - y x) / tk1) ∧
      Tendsto (fun x => ∫ z, expMinus tk1 z * y (x - z)) atTop (𝓝 0) ∧
      (∀ w : ℝ → ℝ, Integrable w → (∀ a b : ℝ, w b - w a = ∫ x in a..b, (w x - y x) / tk1) →
        w = fun x => ∫ z, expMinus tk1 z * y (x - z)) ∧
      ∀ x : ℝ, ∫ z, y (x - z) ∂(lagBackward (tk / tk1) tk1) =
        tk / tk1 * y x + (1 - tk / tk1) * ∫ z, expMinus tk1 z * y (x - z) := by
  sorry

/-- **`thm:cited-A19`, `γ = 1`**: the increment is the four-term mixture
`r²δ₀ + r(1 - r)(Exp₊ + Exp₋) + (1 - r)² Lap_{t_{k+1}}`. -/
theorem cited_A19_gamma_one {μ : ℝ → ℝ → Measure ℝ} (hμ : IsMaternLineKernels 1 μ)
    {tk tk1 : ℝ} (h0 : 0 < tk) (h1 : tk < tk1) :
    μ tk tk1 =
      ENNReal.ofReal ((tk / tk1) ^ 2) • Measure.dirac 0 +
        ENNReal.ofReal (tk / tk1 * (1 - tk / tk1)) •
          ((volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (expPlus tk1 x)) +
            (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (expMinus tk1 x))) +
        ENNReal.ofReal ((1 - tk / tk1) ^ 2) • laplaceLaw tk1 := by
  sorry

/-! ## `thm:cited-A20` [A, A20] — rational increments and the pyramid (V-cone Prop. 7.5(2)) -/

/-- **`thm:cited-A20`, existence and uniqueness**: exactly one continuous `F` with `F(0) = 0` and
`F(qω) - F(ω) = -log R(ω)`. -/
theorem cited_A20_unique {R kR : ℝ → ℝ} (hR : IsRationalLevyTransform R kR) {q : ℝ}
    (hq : 1 < q) :
    ∃! F : ℝ → ℝ, Continuous F ∧ F 0 = 0 ∧ ∀ ω : ℝ, F (q * ω) - F ω = -Real.log (R ω) := by
  sorry

/-- **`thm:cited-A20`, the product**: `e^{-F(ω)} = ∏_{m≥1} R(q^{-m}ω)`, the product converging
unconditionally. -/
theorem cited_A20_product {R kR : ℝ → ℝ} (hR : IsRationalLevyTransform R kR) {q : ℝ}
    (hq : 1 < q) (F : ℝ → ℝ) (hFc : Continuous F) (hF0 : F 0 = 0)
    (hF : ∀ ω : ℝ, F (q * ω) - F ω = -Real.log (R ω)) (ω : ℝ) :
    HasProd (fun m : ℕ => R (ω / q ^ (m + 1))) (Real.exp (-F ω)) := by
  sorry

/-- **`thm:cited-A20`, the folded profile**: `F(ω) = ∫₀^∞ (1 - cos ωx) k(x) dx/x` with
`k(x) = ∑_{m≥1} k_R(q^m x)`, the sum in `[0,∞]`. -/
theorem cited_A20_profile {R kR : ℝ → ℝ} (hR : IsRationalLevyTransform R kR) {q : ℝ}
    (hq : 1 < q) (F : ℝ → ℝ) (hFc : Continuous F) (hF0 : F 0 = 0)
    (hF : ∀ ω : ℝ, F (q * ω) - F ω = -Real.log (R ω)) (ω : ℝ) :
    0 ≤ F ω ∧ ENNReal.ofReal (F ω) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) / x) *
        ∑' m : ℕ, ENNReal.ofReal (kR (q ^ (m + 1) * x)) := by
  sorry

/-- **`thm:cited-A20`, admissibility**: `F` is admissible exactly when `k` has a nonincreasing
version on `(0,∞)`. -/
theorem cited_A20_admissible {R kR : ℝ → ℝ} (hR : IsRationalLevyTransform R kR) {q : ℝ}
    (hq : 1 < q) (F : ℝ → ℝ) (hFc : Continuous F) (hF0 : F 0 = 0)
    (hF : ∀ ω : ℝ, F (q * ω) - F ω = -Real.log (R ω)) :
    IsAdmissibleExponent F ↔
      ∃ k : ℝ → ℝ, (∀ x ∈ Ioi (0 : ℝ), 0 ≤ k x) ∧ AntitoneOn k (Ioi (0 : ℝ)) ∧
        ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
          ENNReal.ofReal (k x) = ∑' m : ℕ, ENNReal.ofReal (kR (q ^ (m + 1) * x)) := by
  sorry

/-- **`thm:cited-A20`, "in particular whenever `k_R` is"**: a nonincreasing `k_R` makes `F`
admissible. -/
theorem cited_A20_admissible_of_antitone {R kR : ℝ → ℝ} (hR : IsRationalLevyTransform R kR)
    {q : ℝ} (hq : 1 < q) (F : ℝ → ℝ) (hFc : Continuous F) (hF0 : F 0 = 0)
    (hF : ∀ ω : ℝ, F (q * ω) - F ω = -Real.log (R ω)) (hk : AntitoneOn kR (Ioi (0 : ℝ))) :
    IsAdmissibleExponent F := by
  sorry

/-! ## `thm:cited-A22` — admitted on 2026-11-15 and moved to `Pyramids.Cited.A22` (wave 3b) -/

/-! ## `thm:cited-A23` — proved from A22 and moved to `Pyramids.Cited.A23` (wave 3b) -/

/-! ## `thm:cited-A24` — admitted on 2026-11-15 and moved to `Pyramids.Cited.A24` (wave 3b) -/

/-! ## `thm:cited-A39`–`thm:cited-A42` — moved to `Pyramids.Cited.A39`–`A42` (wave 2a) -/

/-! ## `thm:cited-A43` — moved to `Pyramids.Cited.A43` (wave 2f) -/

/-! ## `thm:cited-A44` — moved to `Pyramids.Cited.A44` (wave 3d), proved from A39 and A42 -/

/-! ## `thm:cited-A45` — moved to `Pyramids.Cited.A45` (wave 2f) -/

/-! ## `thm:cited-A46`, `thm:cited-A48` — moved to `Pyramids.Cited.A46`, `A48` (wave 2a) -/

/-! ## `thm:cited-A49`, `thm:cited-A50` — moved to `Pyramids.Cited.A49`, `A50` (wave 2f) -/

/-! ## `thm:cited-A51` — moved to `Pyramids.Cited.A51` (wave 2a) -/

/-! ## `thm:cited-A55` [A, A55] — Bernstein's theorem (SSV, Thm. 1.4) -/

/-- **`thm:cited-A55`.** A completely monotone `f` is `∫_{[0,∞)} e^{-λt} μ(dt)` for a measure `μ`
carried by `[0,∞)`, at every `λ > 0`; the identity in `[0,∞]`, `f` being nonnegative. -/
theorem cited_A55 (f : ℝ → ℝ) (hf : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ, μ (Iio 0) = 0 ∧ ∀ x : ℝ, 0 < x →
      ENNReal.ofReal (f x) = ∫⁻ t, ENNReal.ofReal (Real.exp (-(x * t))) ∂μ := by
  sorry

/-! ## `thm:cited-A57` [A, A57] — a Bernstein function of `|ω|²` (SSV, Thm. 13.14) -/

/-- **`thm:cited-A57`.** For a Bernstein function with `f(0+) = 0` (and `f(0) := f(0+)`, the
book's convention): in every dimension `d ≥ 1`, `ω ↦ f(|ω|²)` is continuous and negative definite,
and `e^{-f(|ω|²)}` is the transform of an infinitely divisible probability measure. -/
theorem cited_A57 (f : ℝ → ℝ) (hf : IsBernsteinFunction f) (hf0 : Tendsto f (𝓝[>] 0) (𝓝 0))
    (hf00 : f 0 = 0) (d : ℕ) (hd : 1 ≤ d) :
    Continuous (fun ω : Rd d => f (‖ω‖ ^ 2)) ∧ IsRealNegDef (fun ω : Rd d => f (‖ω‖ ^ 2)) ∧
      ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ IsInfinitelyDivisible μ ∧
        ∀ ω : Rd d, charFun μ ω = ((Real.exp (-f (‖ω‖ ^ 2)) : ℝ) : ℂ) := by
  sorry

end Pyramids
