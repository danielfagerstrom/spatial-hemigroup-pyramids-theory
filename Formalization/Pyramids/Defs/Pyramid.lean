/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Line
import AffineHemigroup.Defs.SmallerGroups
import AffineHemigroup.Defs.Origin
import ScaleSpaceCore.ConvPow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The vocabulary of chapter 3: a pyramid in `ℝ^d`

Blueprint: `blueprint/src/parts/03-pyramid.tex`. Definitions only: nothing in this file claims
anything, and every identity the chapter's nodes state about these objects is a skeleton statement
(`PyramidsSkeleton.Ch03Pyramid`).

## What is already defined, and is not repeated here

* **The clauses of `def:family-dimension-d`** are `Pyramids.Defs.Line`'s, stated there over any
  real inner product space `E` and read here at `E = Rd d`: (I1) and (I2) with the probability
  property are `IsLawHemigroup`, (ND) is `IsNondegenerateLaws`, symmetry is `IsSymmetricLaws`, a
  symmetric family is `IsSymmetricFamily`, and `λ`-covariance with the bijection `S` is
  `IsCovariantAt μ λ S` (`S` an increasing bijection of `[0,∞)`, `D_λ μ_{s,t} = μ_{S s, S t}`,
  `D_λ` the image under `x ↦ λx`). The kernel `μ_t := μ_{0,t}` is `μ 0 t`.
* **`def:semi-selfdecomposable`** is `Pyramids.IsSemiSelfDecomposableWithSpan` with the residual
  `Pyramids.IsSDResidual` (`Defs/Cited.lean`), stated over any real inner product space.
* `ℝ^d`, matrices and their action, `O(d)` (`orthSet`), rotation invariance of a measure
  (`IsRotationInvariant`), the marginal `π_*μ` (`marginal`), infinite divisibility, Sato's triplets
  (`LevyTriplet`, `HasTriplet`), the class `𝒜_d` (`classA`), gauges (`IsGauge`) and the normalised
  surface measure `σ̄` on `S^{d-1}` (`normSphere`, Mathlib's `volume.toSphere` carried to `ℝ^d`
  and divided by its mass) are the affine export's; `|S^{d-1}|` is its `sphereArea`.
* The octave index `n = ⌊log_q t⌋` is `Pyramids.dgLevel` and the interpolated weights
  `(1 - θ) w_i + θ w_{i-1}` are `Pyramids.dgWeight` (`Defs/Line.lean`); `qPowers q` is the set
  `q^ℤ`, the knots. The line's partial products `ladderPartialProduct` are read on `ℝ`.

## What is defined here

* the rest of `def:family-dimension-d`: a family (`IsFamily`), (I3) (`IsRotationInvariantLaws`),
  isotropic families (`IsIsotropicFamily`), `λ`-covariance as a property (`IsLamCovariant`), and the
  set `G` of `lem:family-dilations` (`covariantDilations`);
* the gauge group `𝒢_q` (`IsInGaugeGroup`, with the extension `g(0) := 0`, `extendByZero`) and
  relabelling (`relabel`);
* `def:knots-and-ladder`: `knotKernel`, `ladder` (the knots are `qPowers q`), and the ladder of a
  step (`dilLadder`);
* the symmetric Lévy data `(A, ν)` of `lem:family-structure` and their exponent (`SymLevyData`,
  `pairExponent`, `IsSymData`); laws by their exponents (`IsExponentLaws`);
* the hypotheses and the extension of `lem:synthesis` (`IsSynthesisData`, `octaveA`, `octaveNu`,
  `octaveExponent`);
* the sphere laws of the examples (`sphereLaw`, `sphereOmega`, `sphereTrain`, `betaLaw`), the
  folded marginal Lévy measure (`foldedMarginal`) and the classes `𝒜^{(q)}_n` (`classAq`);
* the ladder objects of `prop:ladder-knot-kernel` (`ladderNuStar`, `ladderProd`, `ladderConv`,
  `HasLadder`, `polarLevyMeasure`, `radialExponent`, `knotSeries`, `knotProfile`), the Lévy
  measure of `prop:ladder-not-every-frequency` (`notEveryNu`), and the equivalent weights and
  tensor powers of `prop:equivalent-weights` (`equivWeight`, `tensorPow`, `uniformInterval`).

## Readings fixed here

* **The data `(A, ν)` are this paper's**: `A` is half of Sato's Gaussian covariance matrix and
  enters the exponent as `⟨ω, Aω⟩` (`quad A ω`). `SymLevyData` asks `A` positive semidefinite
  (Mathlib's `PosSemidef`, which includes symmetry), `ν{0} = 0`, `∫ (|x|² ∧ 1) dν < ∞` and `ν`
  symmetric; under these the integrand `1 - cos⟨ω,x⟩` of the exponent is `ν`-integrable, so the
  Bochner integral in `pairExponent` is the integral, never a junk value.
* **"`μ` has the data `(A, ν)`"** is read by the exponent, as chapter 2's `IsFoldedData`:
  `IsSymData μ D` says `μ̂ = e^{-Ψ}` with `Ψ` the exponent of `D`. By the uniqueness of the triplet
  (`thm:cited-A39`) the data are determined by `μ`.
* **The laws with transform `e^{-(Ψ_t - Ψ_s)}`** are quantified over by specification
  (`IsExponentLaws Ψ μ`); the transform determines the law, so nothing is lost.
* **`η_1`**, the first coordinate of `η ∈ ℝ^d`, is `η 0`, which needs `[NeZero d]`: the definitions
  that read it (`sphereOmega`, `betaLaw`) carry that instance, which is the chapter's `d ≥ 1`.
* **The uniform probability `σ_r` on the sphere of radius `r`** is `sphereLaw d r`, the image of
  `σ̄ = normSphere d` under `x ↦ rx`.
* **`𝒢_q`** is a predicate on functions `ℝ → ℝ` read on `(0,∞)`; a relabelling by `g ∈ 𝒢_q` reads
  `g` extended by `g(0) := 0` (`extendByZero`), as the node extends it.
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set
open ScaleSpace (convPow)
open scoped ENNReal RealInnerProductSpace

/-! ## Families in dimension `d` (`def:family-dimension-d`) -/

section Families

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- **A family** (`def:family-dimension-d`): probability measures `μ s t`, `0 ≤ s ≤ t`, with (I1),
(I2) and (ND). Read at `E = Rd d` it is a family in dimension `d`. -/
def IsFamily (μ : ℝ → ℝ → Measure E) : Prop :=
  IsLawHemigroup μ ∧ IsNondegenerateLaws μ

/-- **The family is `λ`-covariant** (`def:family-dimension-d`): some increasing bijection `S_λ`
of `[0,∞)` has `D_λ μ_{s,t} = μ_{S_λ s, S_λ t}` for all `s ≤ t`. -/
def IsLamCovariant (μ : ℝ → ℝ → Measure E) (lam : ℝ) : Prop :=
  ∃ S : ℝ → ℝ, IsCovariantAt μ lam S

/-- **The set `G` of `lem:family-dilations`**: the `λ > 0` for which the family is
`λ`-covariant. -/
def covariantDilations (μ : ℝ → ℝ → Measure E) : Set ℝ :=
  {lam | 0 < lam ∧ IsLamCovariant μ lam}

/-- **The family is `λ`-covariant for every `λ > 0`** (fully covariant). -/
def IsFullyCovariantLaws (μ : ℝ → ℝ → Measure E) : Prop :=
  ∀ lam : ℝ, 0 < lam → IsLamCovariant μ lam

/-- **The relabelled family** `(μ_{ψ s, ψ t})`; the node's relabelling by `χ` is this with
`ψ = χ⁻¹`. -/
def relabel (μ : ℝ → ℝ → Measure E) (ψ : ℝ → ℝ) : ℝ → ℝ → Measure E :=
  fun s t => μ (ψ s) (ψ t)

/-- **The laws with transform `e^{-(Ψ_t - Ψ_s)}`, by specification**: for `0 ≤ s ≤ t`, `μ s t` is
a probability measure with `μ̂_{s,t}(ω) = exp(-(Ψ_t(ω) - Ψ_s(ω)))`. -/
def IsExponentLaws (Ψ : ℝ → E → ℝ) (μ : ℝ → ℝ → Measure E) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t) ∧
    ∀ ω : E, charFun (μ s t) ω = ((Real.exp (-(Ψ t ω - Ψ s ω)) : ℝ) : ℂ)

/-! ### Knots, knot kernels and the ladder (`def:knots-and-ladder`) -/

/-- **The knot kernel** `μ_{q^n}` (`def:knots-and-ladder`); the knots are `qPowers q`. -/
noncomputable def knotKernel (μ : ℝ → ℝ → Measure E) (q : ℝ) (n : ℤ) : Measure E := μ 0 (q ^ n)

/-- **The ladder** `(μ_{q^n, q^{n+1}})_{n ∈ ℤ}`, the octave steps (`def:knots-and-ladder`). -/
noncomputable def ladder (μ : ℝ → ℝ → Measure E) (q : ℝ) (n : ℤ) : Measure E :=
  μ (q ^ n) (q ^ (n + 1))

/-- **The ladder of a step** `ϱ`: `(D_{q^n} ϱ)_{n ∈ ℤ}`. -/
noncomputable def dilLadder (q : ℝ) (ρ : Measure E) (n : ℤ) : Measure E :=
  ρ.map fun x => (q ^ n) • x

/-! ### The objects of `prop:ladder-knot-kernel` -/

/-- **`ν* := ∑_{m ≥ 1} D_{q^{-m}} ν`** (`prop:ladder-knot-kernel`(1)). -/
noncomputable def ladderNuStar (q : ℝ) (ν : Measure E) : Measure E :=
  Measure.sum fun m : ℕ => ν.map fun x => (q ^ (-((m : ℤ) + 1))) • x

/-- **The partial product** `∏_{m=1}^{M} ϱ̂(q^{-m}ω)` (`prop:ladder-knot-kernel`(1)). -/
noncomputable def ladderProd (q : ℝ) (ρ : Measure E) (M : ℕ) (ω : E) : ℂ :=
  ∏ m ∈ Finset.range M, charFun ρ ((q ^ (-((m : ℤ) + 1))) • ω)

/-- **The partial convolution** `D_{q^{-1}}ϱ * ⋯ * D_{q^{-M}}ϱ`, whose transform is the partial
product. -/
noncomputable def ladderConv (q : ℝ) (ρ : Measure E) (M : ℕ) : Measure E :=
  convList ((List.range M).map fun m => ρ.map fun x => (q ^ (-((m : ℤ) + 1))) • x)

/-- **`μ` is a symmetric `q`-covariant family with `S_q t = qt` and the step `μ_{1,q} = ϱ`**, a
family with the ladder of `ϱ` (`prop:ladder-knot-kernel`(2)). -/
def HasLadder (q : ℝ) (ρ : Measure E) (μ : ℝ → ℝ → Measure E) : Prop :=
  IsSymmetricFamily μ ∧ IsCovariantAt μ q (fun t => q * t) ∧ μ 1 q = ρ

/-- **The equivalent weight** `W_n := w * D_q w * ⋯ * D_{q^{n-1}} w`
(`prop:equivalent-weights`), with `W_0 = δ₀`. -/
noncomputable def equivWeight (q : ℝ) (w : Measure E) (n : ℕ) : Measure E :=
  convList ((List.range n).map fun k => w.map fun x => (q ^ k) • x)

end Families

/-! ## The gauge group `𝒢_q` (`lem:family-dilations`(3)) -/

/-- **`g ∈ 𝒢_q`**: an increasing homeomorphism of `(0,∞)` with `g(qt) = q g(t)` for `t > 0`, read
on `(0,∞)`. -/
structure IsInGaugeGroup (q : ℝ) (g : ℝ → ℝ) : Prop where
  strictMonoOn : StrictMonoOn g (Ioi 0)
  mapsTo : MapsTo g (Ioi 0) (Ioi 0)
  surjOn : SurjOn g (Ioi 0) (Ioi 0)
  continuousOn : ContinuousOn g (Ioi 0)
  equivariant : ∀ t : ℝ, 0 < t → g (q * t) = q * g t

/-- **The extension of `g` to `[0,∞)` by `g(0) := 0`**. -/
noncomputable def extendByZero (g : ℝ → ℝ) : ℝ → ℝ := fun t => if t = 0 then 0 else g t

variable {d : ℕ}

/-! ## Isotropy (`def:family-dimension-d`, (I3)) -/

/-- **(I3)**: `Q_* μ_{s,t} = μ_{s,t}` for every `Q ∈ O(d)` and every pair `0 ≤ s ≤ t`. -/
def IsRotationInvariantLaws (μ : ℝ → ℝ → Measure (Rd d)) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsRotationInvariant (μ s t)

/-- **An isotropic family in dimension `d`** (`def:family-dimension-d`): a family with (I3). -/
def IsIsotropicFamily (μ : ℝ → ℝ → Measure (Rd d)) : Prop :=
  IsFamily μ ∧ IsRotationInvariantLaws μ

/-! ## Symmetric Lévy data (`lem:family-structure`) -/

/-- **The exponent of a pair** `(A, ν)`: `⟨ω, Aω⟩ + ∫ (1 - cos⟨ω,x⟩) ν(dx)`. -/
noncomputable def pairExponent (A : Mat d) (ν : Measure (Rd d)) (ω : Rd d) : ℝ :=
  quad A ω + ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂ν

/-- **Symmetric Lévy data** `(A, ν)` on `ℝ^d` (`lem:family-structure`): `A` positive semidefinite
(this paper's `A`, half of Sato's covariance matrix), `ν` a symmetric Lévy measure. -/
structure SymLevyData (d : ℕ) where
  /-- The Gaussian datum, entering as `⟨ω, Aω⟩`. -/
  A : Mat d
  /-- The Lévy measure. -/
  ν : Measure (Rd d)
  A_posSemidef : A.PosSemidef
  ν_zero : ν {0} = 0
  ν_integrable : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν ≠ ⊤
  ν_symm : ν.map (fun x => -x) = ν

/-- **The exponent of the data**, `Ψ(ω) = ⟨ω, Aω⟩ + ∫ (1 - cos⟨ω,x⟩) ν(dx)`. -/
noncomputable def SymLevyData.exponent (D : SymLevyData d) (ω : Rd d) : ℝ :=
  pairExponent D.A D.ν ω

/-- **`μ` has the data `D`**: `μ̂(ω) = e^{-Ψ(ω)}` with `Ψ` the exponent of `D`. -/
def IsSymData (μ : Measure (Rd d)) (D : SymLevyData d) : Prop :=
  ∀ ω : Rd d, charFun μ ω = ((Real.exp (-D.exponent ω) : ℝ) : ℂ)

/-! ## Synthesis from one octave (`lem:synthesis`) -/

/-- **The hypotheses of `lem:synthesis`** on data `D t`, read for `t ∈ [1, q]`: `t ↦ Ψ_t(ω)` is
continuous on `[1,q]`; for `1 ≤ s < t' ≤ q` the difference of the data is positive semidefinite,
a positive measure, and not zero; and `(A_q, ν_q) = (q²A_1, D_q ν_1)`. -/
structure IsSynthesisData (q : ℝ) (D : ℝ → SymLevyData d) : Prop where
  continuous : ∀ ω : Rd d, ContinuousOn (fun t => (D t).exponent ω) (Icc 1 q)
  increments : ∀ s t : ℝ, 1 ≤ s → s < t → t ≤ q →
    ((D t).A - (D s).A).PosSemidef ∧ (D s).ν ≤ (D t).ν ∧ ((D s).A, (D s).ν) ≠ ((D t).A, (D t).ν)
  glue : (D q).A = q ^ 2 • (D 1).A ∧ (D q).ν = (D 1).ν.map (fun x => q • x)

/-- **The Gaussian datum extended by (`eq:discrete-covariance-levy`)**: `A_{q^n t} := q^{2n} A_t`
for `t ∈ [1, q)`, `n ∈ ℤ`, and `0` at `t ≤ 0`. -/
noncomputable def octaveA (q : ℝ) (D : ℝ → SymLevyData d) (t : ℝ) : Mat d :=
  if t ≤ 0 then 0 else (q ^ (2 * dgLevel q t)) • (D (q ^ (-dgLevel q t) * t)).A

/-- **The Lévy measure extended by (`eq:discrete-covariance-levy`)**: `ν_{q^n t} := D_{q^n} ν_t`
for `t ∈ [1, q)`, `n ∈ ℤ`, and `0` at `t ≤ 0`. -/
noncomputable def octaveNu (q : ℝ) (D : ℝ → SymLevyData d) (t : ℝ) : Measure (Rd d) :=
  if t ≤ 0 then 0 else (D (q ^ (-dgLevel q t) * t)).ν.map fun x => (q ^ dgLevel q t) • x

/-- **The exponent of the extended data**, with `Ψ_0 = 0`. -/
noncomputable def octaveExponent (q : ℝ) (D : ℝ → SymLevyData d) (t : ℝ) (ω : Rd d) : ℝ :=
  pairExponent (octaveA q D t) (octaveNu q D t) ω

/-! ## Laws on spheres (`prop:stratum-one-example`, `prop:stratum-two-example`) -/

/-- **`σ_r`, the uniform probability on the sphere of radius `r` about `0`**. -/
noncomputable def sphereLaw (d : ℕ) (r : ℝ) : Measure (Rd d) :=
  (normSphere d).map fun x => r • x

/-- **`Ω_d(r) := ∫ cos(r η₁) σ_1(dη)`**, the normalised transform of `σ_1`. -/
noncomputable def sphereOmega (d : ℕ) [NeZero d] (r : ℝ) : ℝ :=
  ∫ η, Real.cos (r * η 0) ∂(sphereLaw d 1)

/-- **`∑_{i ∈ ℤ} [(1 - θ) w_i + θ w_{i-1}] σ_{hq^i}`**, the Lévy measure of
`prop:stratum-two-example` at `t = q^θ`. -/
noncomputable def sphereTrain (d : ℕ) (q h : ℝ) (w : ℤ → ℝ) (θ : ℝ) : Measure (Rd d) :=
  Measure.sum fun i : ℤ => ENNReal.ofReal (dgWeight w θ i) • sphereLaw d (h * q ^ i)

/-! ## The reduction to the line (`prop:what-does-not-lift`, `prop:what-does-not-lift-chain`) -/

/-- **`β_d`, the law of `|η₁|`** for `η` uniform on `S^{d-1}`. -/
noncomputable def betaLaw (d : ℕ) [NeZero d] : Measure ℝ :=
  (sphereLaw d 1).map fun η => |η 0|

/-- **The folded Lévy measure of the marginal along `e`**: the image of `ν` under
`x ↦ |⟨e, x⟩|`, restricted to `(0,∞)`. -/
noncomputable def foldedMarginal (e : Rd d) (ν : Measure (Rd d)) : Measure ℝ :=
  (ν.map fun x => |⟪e, x⟫|).restrict (Ioi 0)

/-- **`𝒜^{(q)}_n`** (`prop:what-does-not-lift-chain`): the `F : [0,∞) → [0,∞)` (functions on `ℝ`
read on `[0,∞)`) for which `ω ↦ F(|ω|)` on `ℝ^n` is the exponent of a semi-selfdecomposable law
with span `q`. -/
def classAq (q : ℝ) (n : ℕ) (F : ℝ → ℝ) : Prop :=
  (∀ r : ℝ, 0 ≤ r → 0 ≤ F r) ∧
    ∃ μ : Measure (Rd n), IsProbabilityMeasure μ ∧ IsSemiSelfDecomposableWithSpan q μ ∧
      ∀ ω : Rd n, charFun μ ω = ((Real.exp (-F ‖ω‖) : ℝ) : ℂ)

/-! ## Rotation-invariant steps with a polar profile (`prop:ladder-knot-kernel`(4)(b)) -/

/-- **The measure `k(|x|) (|S^{d-1}| |x|^d)^{-1} dx` on `ℝ^d ∖ {0}`**, for any profile `k` (the
affine export's `OriginDatum.levyMeasure` without the monotonicity of the profile). -/
noncomputable def polarLevyMeasure (d : ℕ) (k : ℝ → ℝ) : Measure (Rd d) :=
  volume.withDensity fun x =>
    ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x

/-- **`ψ_ϱ(r) := -log ϱ̂(re)`**, `r ≥ 0`, along the vector `e`. -/
noncomputable def radialExponent (ρ : Measure (Rd d)) (e : Rd d) (r : ℝ) : ℝ :=
  -Real.log (charFun ρ (r • e)).re

/-- **`∑_{m ≥ 1} ψ(q^{-m} r)`**, as a real series (`tsum`; its summability is a claim). -/
noncomputable def knotSeries (q : ℝ) (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑' m : ℕ, ψ (q ^ (-((m : ℤ) + 1)) * r)

/-- **`k*(r) := ∑_{m ≥ 1} k(q^m r)`**, in `[0,∞]`. -/
noncomputable def knotProfile (q : ℝ) (k : ℝ → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∑' m : ℕ, ENNReal.ofReal (k (q ^ (m + 1) * r))

/-! ## The example at one frequency (`prop:ladder-not-every-frequency`) -/

/-- **`ν_ϱ := ∑_{j ≥ 1} j^{-2} · ½(δ_{2^j} + δ_{-2^j})`** on `ℝ¹ = Rd 1`. -/
noncomputable def notEveryNu : Measure (Rd 1) :=
  Measure.sum fun j : ℕ => ENNReal.ofReal ((((j : ℝ) + 1) ^ 2)⁻¹ / 2) •
    (Measure.dirac (((2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1)) +
      Measure.dirac ((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1)))

/-! ## Equivalent weights (`prop:equivalent-weights`) -/

/-- **The uniform law on `[-h/2, h/2]`**. -/
noncomputable def uniformInterval (h : ℝ) : Measure ℝ :=
  ENNReal.ofReal h⁻¹ • volume.restrict (Icc (-(h / 2)) (h / 2))

/-- **The tensor power** `μ^{⊗d}` of a law on `ℝ`, a law on `ℝ^d`. -/
noncomputable def tensorPow (d : ℕ) (μ : Measure ℝ) : Measure (Rd d) :=
  (Measure.pi fun _ : Fin d => μ).map (WithLp.toLp 2)

end Pyramids
