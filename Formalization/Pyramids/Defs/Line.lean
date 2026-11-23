/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Cited
import Pyramids.SubsamplingLine
import ScaleSpaceCore.Family
import ScaleSpaceCore.SDProfile
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The vocabulary of chapter 2's theory on the line

Blueprint: `blueprint/src/parts/02-line.tex`. Definitions only: nothing in this file claims
anything, and every identity the part's nodes state about these objects is a skeleton statement
(`PyramidsSkeleton.Ch02Line`).

## What the shared libraries already supply, and is not repeated here

* The operator axioms (A1)–(A7) and (ND) are the shared core's `ScaleSpace.CascadeCore`
  (`PreCascadeCore` with `IsPositive` and `IsNondegenerate`), and (A8) at a set `G` of dilations
  is `ScaleSpace.IsScaleCovariant Φ G S`, which the shared core states for an arbitrary `G` so that
  a discrete module can take `G = q^ℤ`. The full family is `ScaleSpace.CascadeFamily`.
* The kernels of an operator family are `ScaleSpace.IsKernelFamily Φ μ` (a hypothesis, not a
  construction); symmetry of a law on `ℝ` is `ScaleSpace.IsSymmetric`; `T_c μ` is
  `μ.map (fun x => c * x)`, the form of `ScaleSpace.map_mul_kernel_of_covariant`.
* A folded pair `(a, ϖ)` with `a ≥ 0`, `ϖ` on `(0,∞)` and `∫ (1 ∧ v²) dϖ < ∞` is the shared
  core's `ScaleSpace.SymLevyPair`, with its exponent `aω² + ∫ (1 - cos ωv) ϖ(dv)`; the admissible
  data `(α, k)` of (2.0) are `ScaleSpace.SDProfile`.
* Gauges are the affine export's `AffineHemigroup.IsGauge`; increasing bijections of `[0,∞)` are
  `AffineHemigroup.IsIncreasingBijection`; infinite divisibility is
  `AffineHemigroup.IsInfinitelyDivisible`; finite convolutions of measures are
  `AffineHemigroup.convList`.
* Semi-selfdecomposability with a span is `Pyramids.IsSemiSelfDecomposableWithSpan`
  (`Defs/Cited.lean`), which is stated over any real inner product space and so reads on `ℝ`.
* The sampled Laplace kernel of `prop:recursion-helmholtz`, its Fourier series and the Laplace
  density are `Pyramids.sampledLaplace`, `Pyramids.lineFourierSeries` (`Defs/PaperVI.lean`) and
  `ScaleSpace.laplaceDensity`; the line convolution of functions is `Pyramids.lineConv`; `I_ν` is
  `Pyramids.besselI` (`Defs/Cited.lean`).

## What is defined here

* **The clauses of `def:family-dimension-d`** (chapter 3), stated over any real inner product
  space `E`: this part's statements read them at `E = ℝ`, the line's own space, and chapter 3 can
  read them at `E = Rd d`. They are not tagged from this part; `def:family-dimension-d` is chapter
  3's node.
* `def:q-covariant-line`: `qPowers`, `IsQCovariantLine`, `IsCanonicalDiscreteGauge`,
  `IsFullyCovariantLine`.
* `def:semi-selfdecomposable-line`: `IsFoldedData` (the span clause is `Defs/Cited.lean`'s).
* `lem:closed-subgroups`: `IsClosedPosSubgroup`, `closedPosSubgroupGen`.
* `def:grid-pyramid-line`: `IsGridMask`, `gridLadderStep`, `CarriesGridLadder`,
  `IsExactGridPyramid`, `IsExactGridPyramidThird`.
* The objects the statements introduce: laws on `hℤ` (`gridLaw`), Lindeberg's kernels, the
  discrete-Gaussian data, the folded Lévy measure of a mask, the sampled Laplace family with its
  one-sided factors and increments, the pyramid computation and the aliased mass.

## Readings fixed here

* **The folded data of a law** (`def:semi-selfdecomposable-line`) is read by its exponent:
  `IsFoldedData μ P` says `μ̂(ω) = exp(-(aω² + ∫ (1 - cos ωv) ϖ(dv)))`. The node defines the pair
  as the Gaussian coefficient and the fold of the Lévy measure; a symmetric infinitely divisible
  law has exactly this exponent with that pair (Sato Thm. 8.1(i)), and a pair with the same
  exponent is the same pair (`thm:cited-A9`, the uniqueness of the folded pair). So the predicate
  determines the pair, and "the folded data of `μ` are `(a, ϖ)`" is `IsFoldedData μ ⟨a, ϖ, …⟩`.
* **A law on `hℤ`** given by its point masses `λ(n)` at `hn` is `gridLaw h λ`, the sum of the
  point masses; "carried by a lattice `ξℤ`" is "the complement of `ξℤ` is null".
* **"`q^ℤ`-covariant"** asserts that some bijections exist: it is `∃ S, IsQCovariantLine q Φ S`,
  the bijections carried as data, as the shared core's `CascadeFamily` carries its `S`.
* **The closed subgroups of `((0,∞), ×)`** are read on subsets of `ℝ`: a subset of `(0,∞)`
  containing `1`, closed under products and inverses, and closed in the topology of `(0,∞)` (not
  of `ℝ`: `q^ℤ` accumulates at `0`).
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set
open ScaleSpace (X CascadeCore CascadeFamily IsScaleCovariant IsKernelFamily SymLevyPair
  laplaceDensity)
open scoped ENNReal

/-! ## The clauses of `def:family-dimension-d`, over any space -/

section Families

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- **(I1) and (I2) for a family of probability measures** (`def:family-dimension-d`): each
`μ s t`, `0 ≤ s ≤ t`, is a probability measure; `μ t t = δ₀` and `μ r t = μ s t ∗ μ r s` for
`r ≤ s ≤ t`; and `(s, t) ↦ μ̂_{s,t}(ω)` is continuous on `{0 ≤ s ≤ t}` for each `ω`. -/
structure IsLawHemigroup (μ : ℝ → ℝ → Measure E) : Prop where
  isProbability : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t)
  diag : ∀ t : ℝ, 0 ≤ t → μ t t = Measure.dirac 0
  cascade : ∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t → μ r t = μ s t ∗ μ r s
  continuous : ∀ ω : E,
    ContinuousOn (fun p : ℝ × ℝ => charFun (μ p.1 p.2) ω) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}

/-- **(ND) for a family of laws**: `μ s t ≠ δ₀` whenever `s < t`. -/
def IsNondegenerateLaws (μ : ℝ → ℝ → Measure E) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s < t → μ s t ≠ Measure.dirac 0

/-- **Every law of the family is symmetric**: invariant under `x ↦ -x`. On `ℝ` each clause is
`ScaleSpace.IsSymmetric (μ s t)`. -/
def IsSymmetricLaws (μ : ℝ → ℝ → Measure E) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t → (μ s t).map (fun x => -x) = μ s t

/-- **A symmetric family in dimension `d`** (`def:family-dimension-d`), on the space `E`: (I1),
(I2), (ND), and every law symmetric. -/
def IsSymmetricFamily (μ : ℝ → ℝ → Measure E) : Prop :=
  IsLawHemigroup μ ∧ IsNondegenerateLaws μ ∧ IsSymmetricLaws μ

/-- **`λ`-covariance of a family of laws with the bijection `S`** (`def:family-dimension-d`):
`S` is an increasing bijection of `[0,∞)` and `D_λ μ_{s,t} = μ_{S s, S t}` for all `s ≤ t`. The
family is `λ`-covariant when some `S` does this. -/
def IsCovariantAt (μ : ℝ → ℝ → Measure E) (lam : ℝ) (S : ℝ → ℝ) : Prop :=
  IsIncreasingBijection S ∧
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → (μ s t).map (fun x => lam • x) = μ (S s) (S t)

end Families

/-! ## Families covariant under one ratio (`def:q-covariant-line`) -/

/-- **The dilations `q^ℤ`**, as a subset of `ℝ`. -/
def qPowers (q : ℝ) : Set ℝ := Set.range fun n : ℤ => q ^ n

/-- **`Φ` is `q^ℤ`-covariant, with the bijections `S`** (`def:q-covariant-line`): `q > 1`, `Φ`
satisfies (A1)–(A7) and (ND) (it is the operator family of a `CascadeCore`), and (A8) asked at
the dilations in `q^ℤ` (`IsScaleCovariant Φ (qPowers q) S`). "`q^ℤ`-covariant" is
`∃ S, IsQCovariantLine q Φ S`. -/
structure IsQCovariantLine (q : ℝ) (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ) : Prop where
  one_lt : 1 < q
  core : ∃ C : CascadeCore, C.Φ = Φ
  covariant : IsScaleCovariant Φ (qPowers q) S

/-- **The canonical discrete gauge** (`def:q-covariant-line`): `S_q t = qt` for all `t ≥ 0`. -/
def IsCanonicalDiscreteGauge (q : ℝ) (S : ℝ → ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → S q t = q * t

/-- **`Φ` is fully covariant** (`def:q-covariant-line`): it satisfies (A1)–(A8) and (ND), the
operator family of a `ScaleSpace.CascadeFamily`. -/
def IsFullyCovariantLine (Φ : ℝ → ℝ → (X →L[ℝ] X)) : Prop :=
  ∃ Fam : CascadeFamily, Fam.Φ = Φ

/-! ## Folded data (`def:semi-selfdecomposable-line`) -/

/-- **`P = (a, ϖ)` is the folded data of the law `μ`** (`def:semi-selfdecomposable-line`):
`μ̂(ω) = exp(-(aω² + ∫_{(0,∞)} (1 - cos ωv) ϖ(dv)))` for every `ω`. The pair is determined by
`μ` (`thm:cited-A9`). -/
def IsFoldedData (μ : Measure ℝ) (P : SymLevyPair) : Prop :=
  ∀ ω : ℝ, charFun μ ω = ((Real.exp (-P.exponent ω) : ℝ) : ℂ)

/-! ## Closed subgroups of `(0,∞)` (`lem:closed-subgroups`) -/

/-- **`H` is a closed subgroup of `((0,∞), ×)`**: `H ⊆ (0,∞)`, `1 ∈ H`, closed under products
and inverses, and closed in the topology of `(0,∞)`. -/
def IsClosedPosSubgroup (H : Set ℝ) : Prop :=
  H ⊆ Ioi 0 ∧ (1 : ℝ) ∈ H ∧ (∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) ∧ (∀ x ∈ H, x⁻¹ ∈ H) ∧
    IsClosed ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' H)

/-- **The closed subgroup of `(0,∞)` generated by `Λ`**: the intersection of the closed
subgroups containing `Λ`. -/
def closedPosSubgroupGen (Λ : Set ℝ) : Set ℝ :=
  ⋂₀ {H : Set ℝ | IsClosedPosSubgroup H ∧ Λ ⊆ H}

/-! ## Laws on a grid -/

/-- **The law on `hℤ` with the point masses `λ(n)` at `hn`**. -/
noncomputable def gridLaw (h : ℝ) (lam : ℤ → ℝ) : Measure ℝ :=
  Measure.sum fun n : ℤ => ENNReal.ofReal (lam n) • Measure.dirac (h * n)

/-- **Lindeberg's kernel** of `prop:lindeberg-stratum-one` after the time `u = t - s`: the law on
`hℤ` with mass `e^{-u} I_n(u)` at `hn`, `I_n` the modified Bessel function of the first kind
(`besselI`, whose series at `ν = |n|` is the node's `∑_j (u/2)^{2j+|n|}/(j!(j+|n|)!)`). -/
noncomputable def lindebergKernel (h u : ℝ) : Measure ℝ :=
  gridLaw h fun n => Real.exp (-u) * besselI (n.natAbs : ℝ) u

/-! ## The discrete-Gaussian pyramid (`prop:discrete-gaussian-pyramid`) -/

/-- **The interpolated weights** `w_i(η) := (1 - η) w_i + η w_{i-1}`. -/
def dgWeight (w : ℤ → ℝ) (η : ℝ) (i : ℤ) : ℝ := (1 - η) * w i + η * w (i - 1)

/-- **The octave index** `n` of `t = q^{n+η}`, `n ∈ ℤ`, `η ∈ [0,1)`. -/
noncomputable def dgLevel (q t : ℝ) : ℤ := ⌊Real.logb q t⌋

/-- **The phase** `η` of `t = q^{n+η}`. -/
noncomputable def dgPhase (q t : ℝ) : ℝ := Real.logb q t - ⌊Real.logb q t⌋

/-- **`ϖ_t := ∑_i w_i(η) δ_{hq^{i+n}}`** for `t = q^{n+η} > 0`, and `ϖ_0 := 0`. -/
noncomputable def dgLevyMeasure (q h : ℝ) (w : ℤ → ℝ) (t : ℝ) : Measure ℝ :=
  if t ≤ 0 then 0 else
    Measure.sum fun i : ℤ =>
      ENNReal.ofReal (dgWeight w (dgPhase q t) i) • Measure.dirac (h * q ^ (i + dgLevel q t))

/-- **`Ψ_t(ω) := ∑_i w_i(η)(1 - cos(hq^{i+n}ω))`** for `t = q^{n+η} > 0`, and `Ψ_0 := 0`. -/
noncomputable def dgExponent (q h : ℝ) (w : ℤ → ℝ) (t ω : ℝ) : ℝ :=
  if t ≤ 0 then 0 else
    ∑' i : ℤ, dgWeight w (dgPhase q t) i * (1 - Real.cos (h * q ^ (i + dgLevel q t) * ω))

/-- **The laws `μ_{s,t}` of the discrete-Gaussian pyramid, by specification**: probability
measures with `μ̂_{s,t} = e^{-(Ψ_t - Ψ_s)}` for `0 ≤ s ≤ t`. The transform determines the law, so
every such family is the node's. -/
def IsDGKernels (q h : ℝ) (w : ℤ → ℝ) (μ : ℝ → ℝ → Measure ℝ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t) ∧
    ∀ ω : ℝ, charFun (μ s t) ω =
      ((Real.exp (-(dgExponent q h w t ω - dgExponent q h w s ω)) : ℝ) : ℂ)

/-! ## Grid pyramids (`def:grid-pyramid-line`) -/

/-- **A mask on `hℤ`** (`def:grid-pyramid-line`): a symmetric probability law `w ≠ δ₀` carried by
`hℤ`. -/
def IsGridMask (h : ℝ) (w : Measure ℝ) : Prop :=
  IsProbabilityMeasure w ∧ ScaleSpace.IsSymmetric w ∧ w ≠ Measure.dirac 0 ∧
    w {x : ℝ | ¬∃ n : ℤ, x = h * n} = 0

/-- **The `n`-th step of the grid pyramid of `(w, q)`**, `T_{q^n} w`. -/
noncomputable def gridLadderStep (q : ℝ) (w : Measure ℝ) (n : ℤ) : Measure ℝ :=
  w.map fun x => q ^ n * x

/-- **`(Φ, S, μ)` carries the grid pyramid of `(w, q)`**: a `q^ℤ`-covariant family in the
canonical discrete gauge whose kernels have the steps `μ_{q^n, q^{n+1}} = T_{q^n} w`. -/
def CarriesGridLadder (q : ℝ) (w : Measure ℝ) (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ)
    (μ : ℝ → ℝ → Measure ℝ) : Prop :=
  IsQCovariantLine q Φ S ∧ IsCanonicalDiscreteGauge q S ∧ IsKernelFamily Φ μ ∧
    ∀ n : ℤ, μ (q ^ n) (q ^ (n + 1)) = gridLadderStep q w n

/-- **The grid pyramid of `(w, q)` is exact** (`def:grid-pyramid-line`): some `q^ℤ`-covariant
family in the canonical discrete gauge has its steps, through its kernels. -/
def IsExactGridPyramid (q : ℝ) (w : Measure ℝ) : Prop :=
  ∃ (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ) (μ : ℝ → ℝ → Measure ℝ),
    CarriesGridLadder q w Φ S μ

/-- **The grid pyramid of `(w, q)` is exact in the third stratum** (`def:grid-pyramid-line`):
some such family is fully covariant. -/
def IsExactGridPyramidThird (q : ℝ) (w : Measure ℝ) : Prop :=
  ∃ (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ) (μ : ℝ → ℝ → Measure ℝ),
    CarriesGridLadder q w Φ S μ ∧ IsFullyCovariantLine Φ

/-- **`ϖ` is the folded Lévy measure of the compound Poisson law `w`**
(`prop:grid-pyramids-infinitely-divisible`(1)): a finite measure on `(0,∞)` with
`ŵ(ω) = exp(-∫ (1 - cos ωv) ϖ(dv))`. -/
def IsMaskLevyMeasure (w ϖ : Measure ℝ) : Prop :=
  IsFiniteMeasure ϖ ∧ ScaleSpace.IsFolded ϖ ∧
    ∀ ω : ℝ, charFun w ω = ((Real.exp (-∫ v, (1 - Real.cos (ω * v)) ∂ϖ) : ℝ) : ℂ)

/-- **`ϖ_1 := ∑_{m ≥ 1} T_{q^{-m}} ϖ`**, the folded Lévy measure of the knot kernel of a grid
pyramid whose mask has the folded Lévy measure `ϖ` (`eq:grid-pyramid-knot-kernel`). -/
noncomputable def knotLevyMeasure (q : ℝ) (ϖ : Measure ℝ) : Measure ℝ :=
  Measure.sum fun m : ℕ => ϖ.map fun v => q ^ (-((m : ℤ) + 1)) * v

/-- **The partial product** `∏_{m=1}^{M} ŵ(q^{-m}ω)` of `eq:grid-pyramid-knot-kernel`. -/
noncomputable def ladderPartialProduct (q : ℝ) (w : Measure ℝ) (M : ℕ) (ω : ℝ) : ℂ :=
  ∏ m ∈ Finset.range M, charFun w (q ^ (-((m : ℤ) + 1)) * ω)

/-- **The partial convolution** `T_{q^{-1}}w * ⋯ * T_{q^{-M}}w`, whose transform is the partial
product. -/
noncomputable def ladderPartialConv (q : ℝ) (w : Measure ℝ) (M : ℕ) : Measure ℝ :=
  convList ((List.range M).map fun m => w.map fun x => q ^ (-((m : ℤ) + 1)) * x)

/-! The geometric kernel `(1-a)/(1+a) a^{|n|}` on `ℤ` is the proved library's
`Pyramids.geomKernel` (`Pyramids.SubsamplingLine`): the sampled Laplace mask `λ^L_a` of
`prop:grid-pyramids-infinitely-divisible`(4) is `gridLaw h (geomKernel a)`, and the sampled Laplace
kernel `λ_t` of `prop:sampled-laplace-exact` is `geomKernel a_t`. -/

/-- **The binomial mask** `[1, 4, 6, 4, 1]/16` on `ℤ`, centred at `0`. -/
noncomputable def binomialMask5 (n : ℤ) : ℝ :=
  if |n| ≤ 2 then ((Nat.choose 4 (n + 2).toNat : ℕ) : ℝ) / 16 else 0

/-! ## The sampled Laplace family (`prop:sampled-laplace-exact`) -/

/-- **`δ₀` on `ℤ`**. -/
def zdelta (n : ℤ) : ℝ := if n = 0 then 1 else 0

/-- **Convolution on `ℤ`**, `(f * g)(n) := ∑ₘ f(m) g(n - m)`. -/
noncomputable def zconv (f g : ℤ → ℝ) (n : ℤ) : ℝ := ∑' m : ℤ, f m * g (n - m)

/-- **The convolution power** `f^{*k}` on `ℤ`, with `f^{*0} = δ₀`. -/
noncomputable def zconvPow (f : ℤ → ℝ) : ℕ → ℤ → ℝ
  | 0 => zdelta
  | k + 1 => zconv (zconvPow f k) f

/-- **`a_t := e^{-h/t}`** for `t > 0`, and `a_0 := 0`. -/
noncomputable def slRatio (h t : ℝ) : ℝ := if 0 < t then Real.exp (-h / t) else 0

/-- **`λ_t(n) := (1-a_t)/(1+a_t) a_t^{|n|}`**, the Laplace kernel of range `t` sampled on `hℤ`
and renormalized; `λ_0 = δ₀`, since `a_0 = 0`. For `t > 0` it is `sampledLaplace h t`. -/
noncomputable def slKernel (h t : ℝ) : ℤ → ℝ := geomKernel (slRatio h t)

/-- **`e⁺(n) := (1-a)aⁿ` for `n ≥ 0`, `0` for `n < 0`**, the one-sided geometric law. -/
noncomputable def oneSidedGeom (a : ℝ) (n : ℤ) : ℝ := if 0 ≤ n then (1 - a) * a ^ n.toNat else 0

/-- **`p := a_s(1-a_t)/(a_t(1-a_s))`**, the weight of `δ₀` in each factor of the step. -/
noncomputable def slMix (h s t : ℝ) : ℝ :=
  slRatio h s * (1 - slRatio h t) / (slRatio h t * (1 - slRatio h s))

/-- **The forward factor** `pδ₀ + (1-p)e⁺_t` of the step from `s` to `t`. -/
noncomputable def slForward (h s t : ℝ) (n : ℤ) : ℝ :=
  slMix h s t * zdelta n + (1 - slMix h s t) * oneSidedGeom (slRatio h t) n

/-- **The backward factor** `pδ₀ + (1-p)e⁻_t`, `e⁻_t(n) := e⁺_t(-n)`. -/
noncomputable def slBackward (h s t : ℝ) (n : ℤ) : ℝ := slForward h s t (-n)

/-- **The step `λ_{s,t}`** := `(pδ₀ + (1-p)e⁺_t) * (pδ₀ + (1-p)e⁻_t)`, and `λ_{t,t} := δ₀`. -/
noncomputable def slIncrement (h s t : ℝ) : ℤ → ℝ :=
  if s = t then zdelta else zconv (slForward h s t) (slBackward h s t)

/-- **A bounded sequence** on `ℤ`. -/
def IsBoundedSeq (v : ℤ → ℝ) : Prop := ∃ C : ℝ, ∀ n : ℤ, |v n| ≤ C

/-- **The forward recursion** `v(n) = a v(n-1) + (1 - a + pa) y(n) - pa y(n-1)` of
`prop:sampled-laplace-exact`(1), one state. -/
def IsForwardRecursion (a p : ℝ) (y v : ℤ → ℝ) : Prop :=
  ∀ n : ℤ, v n = a * v (n - 1) + (1 - a + p * a) * y n - p * a * y (n - 1)

/-- **The same recursion run backward**, `v(n) = a v(n+1) + (1 - a + pa) y(n) - pa y(n+1)`. -/
def IsBackwardRecursion (a p : ℝ) (y v : ℤ → ℝ) : Prop :=
  ∀ n : ℤ, v n = a * v (n + 1) + (1 - a + p * a) * y n - p * a * y (n + 1)

/-- **The pyramid computation** `u_{k+1}(m) := (g * u_k)(qm)` from `u_0 = δ₀`. -/
noncomputable def pyramidLevels (g : ℤ → ℝ) (q : ℕ) : ℕ → ℤ → ℝ
  | 0 => zdelta
  | k + 1 => fun m => zconv g (pyramidLevels g q k) (q * m)

/-- **The density of `L_{r_0} * ⋯ * L_{r_n}`**, `n + 1` Laplace densities convolved. -/
noncomputable def laplaceChainDensity (r : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => laplaceDensity (r 0)
  | n + 1 => lineConv (laplaceChainDensity r n) (laplaceDensity (r (n + 1)))

/-- **The sampled factor** `L_{ctq^k}` sampled on `q^k hℤ` and read on the fine grid `hℤ`: its
value at `hi` when `q^k` divides `i`, and `0` otherwise. -/
noncomputable def sampledLaplaceFactor (h c t : ℝ) (q k : ℕ) (i : ℤ) : ℝ :=
  if ((q : ℤ) ^ k ∣ i) then laplaceDensity (c * t * (q : ℝ) ^ k) (i * h) else 0

/-- **The aliased mass** `α_t(ω) := ∑_{n ≠ 0} (1 + t²(ω + 2πn/h)²)⁻¹`. -/
noncomputable def aliasedMass (h t ω : ℝ) : ℝ :=
  ∑' n : ℤ, if n = 0 then 0 else (1 + t ^ 2 * (ω + 2 * Real.pi * n / h) ^ 2)⁻¹

end Pyramids
