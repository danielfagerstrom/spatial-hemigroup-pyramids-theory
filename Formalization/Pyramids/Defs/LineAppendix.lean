/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Pyramid
import Pyramids.Defs.Matern
import ScaleSpaceCore.Exponent
import ScaleSpaceCore.Cin
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# The vocabulary of appendix A: the discrete stratum on the line

Blueprint: `blueprint/src/parts/A1-line.tex`. Definitions only: nothing in this file claims
anything, and every identity the appendix's nodes state about these objects is a skeleton
statement (`PyramidsSkeleton.ChA1Line`).

## What is already defined, and is not repeated here

* **Families.** A symmetric family on the line with (I1), (I2), (ND) is `IsSymmetricFamily`, and
  `λ`-covariance with the bijection `S` is `IsCovariantAt` (`Defs/Line.lean`, over any real inner
  product space, read here on `ℝ`). Laws by their exponents are `IsExponentLaws`, the gauge group
  `𝒢_q` is `IsInGaugeGroup` with `extendByZero`, the relabelled family is `relabel`, the
  equivalent weights are `equivWeight`, the uniform law on `[-h/2, h/2]` is `uniformInterval`
  (`Defs/Pyramid.lean`).
* **Exponents.** The class `ND_s` of the appendix (`aω² + ∫ (1 - cos ωv) ϖ(dv)`, `a ≥ 0`,
  `∫ (1 ∧ v²) dϖ < ∞`) is the shared core's `ScaleSpace.IsSymLevyExponent`, and its data `(a, ϖ)`
  are a `ScaleSpace.SymLevyPair`; the admissible exponents of (2.0) are
  `ScaleSpace.IsAdmissibleExponent`, with the data `ScaleSpace.SDProfile`. The folded data of a law
  are `IsFoldedData` (`Defs/Line.lean`). `Cin` is the shared core's `ScaleSpace.cin`.
* **The Matérn objects.** `F_q` is `maternExponent q c` (even in its argument, so read on `ℝ`),
  the Matérn pyramid is `IsMaternPyramid q c` read at `E = ℝ`, `Li₂` is `dilog` and
  `-½ Li₂(-c²r²)` is `maternLimitExponent` (`Defs/Matern.lean`); the Laplace law `L_r` is the
  shared core's `ScaleSpace.laplaceLaw r`, the one-sided densities are `expPlus`, `expMinus`.
* **Grid objects.** The masks and grid pyramids of `def:grid-pyramid-line` (`IsGridMask`,
  `CarriesGridLadder`), laws on `hℤ` (`gridLaw`), the binomial mask (`binomialMask5`), convolution
  on `ℤ` (`zconv`), the discrete-Gaussian data (`IsDGKernels`) are chapter 2's; the octave index
  `⌊log_q t⌋` is `dgLevel`. Pólya frequency kernels (`IsPolyaFrequencyKernel`), sign changes of a
  finite sequence (`seqSignChanges`) and of a function in the essential sense (`essSignChanges`),
  complete monotonicity (`IsCompletelyMonotone`) are `Defs/Cited.lean`'s.
* **The relative entropy** is Mathlib's `InformationTheory.klDiv`, valued in `[0,∞]`. For
  probability measures it is the node's `KL`: `∞` unless `π ≪ η`; otherwise `∫ log(dπ/dη) dπ`,
  which Mathlib sets to `∞` when the log-likelihood ratio is not integrable, and the node's integral
  is `+∞` exactly then, since the negative part of `p log p` is bounded by `1/e`.

## What is defined here

* § A.1: the families of the appendix read through their kernels (`IsQFamily`), the exponent
  `Ψ_t` (`lineExponent`), the data of an exponent (`HasExpData`), the lifts of circle
  homeomorphisms (`logConj`, `IsCircleLift`), the paths of the annulus (`IsAnnulusPath`,
  `annulusExtend`) and the two coordinates of the octave phase (`octavePsi`, `octaveXi`).
* § A.2: the diagonal dilation `J_c` (`scaleDiag`), the slab measures `Λ((s,t] × ·)` (`slab`), the
  pairs `(Λ, ℬ)` (`IsSurfacePair`, with `IsSurfaceGaussian`, `IsLevyIntegrableSurface`), the
  exponent (A.e2) (`surfaceExponent`), the pair of a family (`IsSurfaceDataOf`, `IsFamilyPair`);
  the class `[y]` (`qClass`), the cylinder, its chart of the orbit space and its measure
  (`cylinder`, `cylinderChart`, `cylMeasure`), the orbits
  `Λ^{(θ,r)}` and their mixtures (`knotAtomOrbit`, `orbitMixture`), the weight of (A.e3)
  (`cylWeight`, `IsCylIntegrable`), the Gaussian spread `ℬ = ∑ q^{2n} β(q^{-n}·)` (`gaussSpread`),
  the knot-atom cascade (`knotAtomCascade`), the knot Gaussians (`knotGaussian`), extreme rays
  (`IsExtremeRayIn`) and the two cones (`surfaceCone`, `gaussianCone`); the Haar measure `η` and
  `dy/(ℓy)` (`haarPhase`, `logHaar`), the modulation spectrum (`modulationCoeff`,
  `modulationSpectrum`); the cone `𝒦_q` and the `q`-Cin rays (`IsInKq`, `qCinRay`, `qCinAtoms`,
  `IsQCinRepr`).
* `def:modulation-orbit`: `knotStep`, `IsKnotExponent`, `IsKnotLadder`, `IsStepMeasure`,
  `HasNoGaussianStep`, `modulationOrbit`.
* § A.3, `def:phase-entropy`: the `r`-marginal (`rMarginal`), the disintegration
  (`IsPhaseDisintegration`), the phase entropy (`phaseEntropy`); the fold and the rotation
  (`foldMeasure`, `qRot`), the normalized fold `μ̄°` and the rotated fibres `P_r`
  (`foldedStepNorm`, `rotatedFibre`).
* § A.4–A.5: "a step of no family" (`IsStepOfNoFamily`), the multiplicities (`atomMult`), the
  generator symbol of the Matérn pyramid on the line
  (`maternLineGen`), its limit exponent in the integral form (`maternLineLimit`), sign changes of a
  sequence on `ℤ` (`zSignChanges`, `zDiff`), the random-walk laws `exp[c δ²_v]` (`symStep`,
  `randomWalkLaw`) and the truncated `q`-Cin cascade (`qCinTruncation`).

## Readings fixed here

* **The families of the appendix are read through their kernels**, as the appendix itself says
  (its § A.1, by `lem:line-axioms-kernels`): a `q^ℤ`-covariant family in the canonical discrete
  gauge is `IsQFamily q μ`, a symmetric family on `ℝ` with `S_q t = qt`. Two families are the same
  when their laws agree on `0 ≤ s ≤ t`; by `lem:line-axioms-kernels` the operators are then the
  same as well.
* **`Ψ_t := -log μ̂_t`** is `lineExponent μ t`, with `μ̂_t` real and positive for these families
  (`lem:family-structure`), so the logarithm takes no junk value.
* **Measures on `(0,∞)` and `(0,∞)²`** are measures on `ℝ` and `ℝ × ℝ` that are null off the open
  half-line or quadrant (`B (Iic 0) = 0`, `Λ quadrantᶜ = 0`), as the shared core carries its folded
  Lévy measures. `Λ((s,t] × ·)` is the image of `Λ` restricted to `(s,t] × ℝ` under the second
  projection.
* **Measures on the cylinder `[1,q) × (0,∞)`** are measures on `ℝ × ℝ`, the first coordinate
  `θ`, the second `r`; on the circle `[1,q)` they are measures on `ℝ` null off `[1,q)`.
* **The disintegration** of `def:phase-entropy` is a measurable family `π` of probability
  measures on `[1,q)`, one for every `r` (a family that is one for `ρ̃`-a.e. `r` is changed on a
  null set without changing anything the appendix reads), with `σ(E) = ∫ π_r(E_r) ρ̃(dr)`. The
  phase entropy, a value in `[-∞, 0]`, is an `EReal`.
* **The mixture `Λ_σ = ∫ Λ^{(θ,r)} σ(dθ, dr)`** is `σ.bind`, whose kernel `(θ, r) ↦ Λ^{(θ,r)}` is
  measurable (a countable sum of point masses at measurable points), so the bind is the integral.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set
open ScaleSpace (SymLevyPair IsSymLevyExponent convPow)
open scoped ENNReal NNReal

/-! ## § A.1: families, exponents, data -/

/-- **A `q^ℤ`-covariant family in the canonical discrete gauge, read through its kernels**: a
symmetric family on `ℝ` (laws `μ s t`, (I1), (I2), (ND), symmetric) that is `q`-covariant with
`S_q t = qt`. -/
def IsQFamily (q : ℝ) (μ : ℝ → ℝ → Measure ℝ) : Prop :=
  IsSymmetricFamily μ ∧ IsCovariantAt μ q (fun t => q * t)

/-- **`Ψ_t := -log μ̂_t`**, the exponent of the kernel `μ_t = μ_{0,t}`. -/
noncomputable def lineExponent (μ : ℝ → ℝ → Measure ℝ) (t ω : ℝ) : ℝ :=
  -Real.log (charFun (μ 0 t) ω).re

/-- **`(a, ϖ)` are the data of `ψ`**: `ψ(ω) = aω² + ∫ (1 - cos ωv) ϖ(dv)` for every `ω`. -/
def HasExpData (ψ : ℝ → ℝ) (P : SymLevyPair) : Prop := ∀ ω : ℝ, ψ ω = P.exponent ω

/-- **`g̃(u) := log g(e^u)`**, the map of `lem:gauge-group`(2). -/
noncomputable def logConj (g : ℝ → ℝ) (u : ℝ) : ℝ := Real.log (g (Real.exp u))

/-- **An increasing homeomorphism `G` of `ℝ` with `G(u + ℓ) = G(u) + ℓ`**, a lift of an
orientation-preserving homeomorphism of the circle `ℝ/ℓℤ`. -/
def IsCircleLift (ℓ : ℝ) (G : ℝ → ℝ) : Prop :=
  StrictMono G ∧ Continuous G ∧ Function.Surjective G ∧ ∀ u : ℝ, G (u + ℓ) = G u + ℓ

/-- **The conditions (1)–(4) of `thm:annulus-parametrization`** on a path `(Ψ_t)_{t ∈ [1,q]}`. -/
structure IsAnnulusPath (q : ℝ) (Ψ : ℝ → ℝ → ℝ) : Prop where
  /-- (1) `Ψ_t ∈ ND_s` and `Ψ_t ≢ 0`. -/
  nd : ∀ t ∈ Icc 1 q, IsSymLevyExponent (Ψ t) ∧ ∃ ω : ℝ, Ψ t ω ≠ 0
  /-- (2) `Ψ_{t'} - Ψ_t ∈ ND_s` and `≢ 0` for `1 ≤ t < t' ≤ q`. -/
  increments : ∀ t t' : ℝ, 1 ≤ t → t < t' → t' ≤ q →
    IsSymLevyExponent (fun ω => Ψ t' ω - Ψ t ω) ∧ ∃ ω : ℝ, Ψ t' ω - Ψ t ω ≠ 0
  /-- (3) gluing, `Ψ_q = Ψ_1(q ·)`. -/
  glue : ∀ ω : ℝ, Ψ q ω = Ψ 1 (q * ω)
  /-- (4) `t ↦ Ψ_t(ω)` is continuous on `[1,q]`. -/
  continuous : ∀ ω : ℝ, ContinuousOn (fun t => Ψ t ω) (Icc 1 q)

/-- **The family's exponents recovered from the path**: `Ψ_{q^n t} := Ψ_t(q^n ·)` for
`t ∈ [1,q)`, `n ∈ ℤ`, and `Ψ_0 := 0` (read at every `t ≤ 0`). -/
noncomputable def annulusExtend (q : ℝ) (Ψ : ℝ → ℝ → ℝ) (t ω : ℝ) : ℝ :=
  if t ≤ 0 then 0 else Ψ (q ^ (-dgLevel q t) * t) (q ^ dgLevel q t * ω)

/-- **`ψ(u, v) := Ψ_{e^u}(e^v)`** (`thm:annulus-parametrization-phase`). -/
noncomputable def octavePsi (Ψ : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ := Ψ (Real.exp u) (Real.exp v)

/-- **`Ξ(w; ξ) := ψ(ξ, w - ξ)`** (`thm:annulus-parametrization-phase`). -/
noncomputable def octaveXi (Ψ : ℝ → ℝ → ℝ) (w ξ : ℝ) : ℝ := octavePsi Ψ ξ (w - ξ)

/-! ## § A.2: the surface measure -/

/-- **`J_c(y, v) := (cy, cv)`**; the diagonal dilation `J` of `thm:surface-measure` is `J_q`. -/
def scaleDiag (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (c * p.1, c * p.2)

/-- **The open quadrant `(0,∞)²`**. -/
def quadrant : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0

/-- **`Λ((s,t] × ·)`**, the measure `A ↦ Λ((s,t] × A)` on `ℝ`. -/
noncomputable def slab (Λ : Measure (ℝ × ℝ)) (s t : ℝ) : Measure ℝ :=
  (Λ.restrict (Ioc s t ×ˢ univ)).map Prod.snd

/-- **The integrability of `thm:surface-measure`(i)**, at every `t > 0`:
`∫ (1 ∧ v²) Λ((0,t] × dv) < ∞`. -/
def IsLevyIntegrableSurface (Λ : Measure (ℝ × ℝ)) : Prop :=
  ∀ t : ℝ, 0 < t → ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(slab Λ 0 t) ≠ ⊤

/-- **Condition (ii) of `thm:surface-measure`** on a measure `ℬ` on `(0,∞)`: `ℬ((0,t]) < ∞` for
`t > 0`, and `ℬ(qA) = q² ℬ(A)` for Borel `A ⊆ (0,∞)`. -/
def IsSurfaceGaussian (q : ℝ) (B : Measure ℝ) : Prop :=
  B (Iic 0) = 0 ∧ (∀ t : ℝ, 0 < t → B (Ioc 0 t) ≠ ⊤) ∧
    ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioi 0 →
      B ((fun y => q * y) '' A) = ENNReal.ofReal (q ^ 2) * B A

/-- **The pairs `(Λ, ℬ)` of `thm:surface-measure`**: conditions (i)–(iv). -/
structure IsSurfacePair (q : ℝ) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) : Prop where
  /-- `Λ` is a measure on `(0,∞)²`. -/
  carried : Λ quadrantᶜ = 0
  /-- (i) `J_* Λ = Λ`. -/
  invariant : Λ.map (scaleDiag q) = Λ
  /-- (i) the integrability, at every `t > 0`. -/
  integrable : IsLevyIntegrableSurface Λ
  /-- (ii). -/
  gaussian : IsSurfaceGaussian q B
  /-- (iii) no mass on a vertical line, no atom of `ℬ`. -/
  no_line : ∀ y : ℝ, 0 < y → Λ ({y} ×ˢ Ioi 0) = 0 ∧ B {y} = 0
  /-- (iv) nondegeneracy. -/
  nondeg : ∀ s t : ℝ, 0 < s → s < t → 0 < Λ (Ioc s t ×ˢ Ioi 0) + B (Ioc s t)

/-- **The exponent (A.e2)** of a pair:
`Ψ_t(ω) = a(t)ω² + ∫_{(0,t] × (0,∞)} (1 - cos ωv) Λ(dy, dv)`, `a(t) = ℬ((0,t])`. -/
noncomputable def surfaceExponent (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (t ω : ℝ) : ℝ :=
  (B (Ioc 0 t)).toReal * ω ^ 2 + ∫ p in Ioc 0 t ×ˢ Ioi 0, (1 - Real.cos (ω * p.2)) ∂Λ

/-- **(A.e1) for the family `μ`**: for every `t > 0` the kernel `μ_t` has the folded data
`(a(t), ϖ_t)` with `ϖ_t = Λ((0,t] × ·)` and `a(t) = ℬ((0,t])`. -/
def IsSurfaceDataOf (μ : ℝ → ℝ → Measure ℝ) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∃ P : SymLevyPair, IsFoldedData (μ 0 t) P ∧ P.ν = slab Λ 0 t ∧
    ENNReal.ofReal P.a = B (Ioc 0 t)

/-- **`(Λ, ℬ)` is the pair of the family `μ`** (`thm:surface-measure`): a pair with (i)–(iv)
that gives the family by (A.e1). -/
def IsFamilyPair (q : ℝ) (μ : ℝ → ℝ → Measure ℝ) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) : Prop :=
  IsSurfacePair q Λ B ∧ IsSurfaceDataOf μ Λ B

/-! ## § A.2: the cylinder and the knot-atom cascades -/

/-- **`[y] ∈ [1,q)`, the representative of `y > 0` modulo `q^ℤ`**: `q^{-n} y`, `n = ⌊log_q y⌋`. -/
noncomputable def qClass (q y : ℝ) : ℝ := q ^ (-dgLevel q y) * y

/-- **The cylinder `𝒞 = [1,q)_θ × (0,∞)_r`**. -/
def cylinder (q : ℝ) : Set (ℝ × ℝ) := Ico 1 q ×ˢ Ioi 0

/-- **The invariant map `(y, v) ↦ (log y mod ℓ, v/y)`** of `thm:knot-atom-cascades`(1), into
`(ℝ/ℓℤ) × ℝ`, read on `(0,∞)²`. -/
noncomputable def cylinderChart (q : ℝ) (p : ℝ × ℝ) : AddCircle (Real.log q) × ℝ :=
  ((Real.log p.1 : AddCircle (Real.log q)), p.2 / p.1)

/-- **`σ`, the cylinder measure of `Λ`**: the image of `Λ` restricted to `[1,q) × (0,∞)` under
`(y, v) ↦ (y, v/y)`. -/
noncomputable def cylMeasure (q : ℝ) (Λ : Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  (Λ.restrict (cylinder q)).map fun p => (p.1, p.2 / p.1)

/-- **`Λ^{(θ,r)} := ∑_{n ∈ ℤ} δ_{(θq^n, rθq^n)}`**, one orbit of `J`. -/
noncomputable def knotAtomOrbit (q θ r : ℝ) : Measure (ℝ × ℝ) :=
  Measure.sum fun n : ℤ => Measure.dirac (θ * q ^ n, r * θ * q ^ n)

/-- **`Λ_σ := ∫_𝒞 Λ^{(θ,r)} σ(dθ, dr)`**. -/
noncomputable def orbitMixture (q : ℝ) (σ : Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  σ.bind fun p => knotAtomOrbit q p.1 p.2

/-- **The weight of (A.e3)**, `x² ∧ (1 + log₊ x)`. -/
noncomputable def cylWeight (x : ℝ) : ℝ := min (x ^ 2) (1 + Real.posLog x)

/-- **(A.e3)**: `∫_𝒞 [(rθ)² ∧ (1 + log₊(rθ))] σ(dθ, dr) < ∞`. -/
def IsCylIntegrable (σ : Measure (ℝ × ℝ)) : Prop :=
  ∫⁻ p, ENNReal.ofReal (cylWeight (p.2 * p.1)) ∂σ ≠ ⊤

/-- **`ℬ(A) = ∑_n q^{2n} β(q^{-n}A ∩ [1,q))`**, for `β` a measure on `[1,q)`: the sum of the
images of `β` under `y ↦ q^n y`, weighted by `q^{2n}`. -/
noncomputable def gaussSpread (q : ℝ) (β : Measure ℝ) : Measure ℝ :=
  Measure.sum fun n : ℤ => ENNReal.ofReal (q ^ (2 * n)) • β.map fun y => q ^ n * y

/-- **The knot-atom cascade (A.e4)**,
`Ψ^{(θ,r)}_t(ω) = ∑_{n : θq^n ≤ t} (1 - cos(ω rθq^n))`, a real series. -/
noncomputable def knotAtomCascade (q θ r t ω : ℝ) : ℝ :=
  ∑' n : ℤ, if θ * q ^ n ≤ t then 1 - Real.cos (ω * (r * θ * q ^ n)) else 0

/-- **`ℬ^{(θ)} := ∑_n (θq^n)² δ_{θq^n}`**, the knot Gaussian of phase `θ`. -/
noncomputable def knotGaussian (q θ : ℝ) : Measure ℝ :=
  Measure.sum fun n : ℤ => ENNReal.ofReal ((θ * q ^ n) ^ 2) • Measure.dirac (θ * q ^ n)

/-- **`x` spans an extreme ray of the cone `C`**: `x ∈ C`, `x ≠ 0`, and every summand `y` of a
decomposition `x = y + z` in `C` is a nonnegative multiple of `x`. -/
def IsExtremeRayIn {M : Type*} [AddCommMonoid M] [SMul ℝ≥0 M] (C : Set M) (x : M) : Prop :=
  x ∈ C ∧ x ≠ 0 ∧ ∀ y ∈ C, ∀ z ∈ C, y + z = x → ∃ c : ℝ≥0, y = c • x

/-- **The cone of `thm:knot-atom-cascades`(3)**: the `J`-invariant measures `Λ` on `(0,∞)²` whose
cylinder measure satisfies (A.e3). -/
def surfaceCone (q : ℝ) : Set (Measure (ℝ × ℝ)) :=
  {Λ | Λ quadrantᶜ = 0 ∧ Λ.map (scaleDiag q) = Λ ∧ IsCylIntegrable (cylMeasure q Λ)}

/-- **The cone of the `ℬ`** with condition (ii). -/
def gaussianCone (q : ℝ) : Set (Measure ℝ) := {B | IsSurfaceGaussian q B}

/-- **`η(dθ) := dθ/(ℓθ)` on `[1,q)`**, the Haar probability measure of the circle
`(0,∞)/q^ℤ`. -/
noncomputable def haarPhase (q : ℝ) : Measure ℝ :=
  (volume.restrict (Ico 1 q)).withDensity fun θ => ENNReal.ofReal (1 / (Real.log q * θ))

/-- **`dy/(ℓy)` on `(0,∞)`**. -/
noncomputable def logHaar (q : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun y => ENNReal.ofReal (1 / (Real.log q * y))

/-- **`σ̂_j(A) := ∫_{[1,q) × A} e^{2πij log_q θ} σ(dθ, dr)`**
(`prop:strata-cylinder-coordinates`(3)). -/
noncomputable def modulationCoeff (q : ℝ) (σ : Measure (ℝ × ℝ)) (j : ℤ) (A : Set ℝ) : ℂ :=
  ∫ p in Ico 1 q ×ˢ A,
    Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (Real.logb q p.1 : ℂ)) ∂σ

/-- **The modulation spectrum**: the `j ≠ 0` with `σ̂_j ≠ 0`, that is `σ̂_j(A) ≠ 0` for some compact
`A ⊂ (0,∞)`. -/
def modulationSpectrum (q : ℝ) (σ : Measure (ℝ × ℝ)) : Set ℤ :=
  {j | j ≠ 0 ∧ ∃ A : Set ℝ, IsCompact A ∧ A ⊆ Ioi 0 ∧ modulationCoeff q σ j A ≠ 0}

/-! ## § A.2: the `q`-Cin rays -/

/-- **`ψ ∈ 𝒦_q`**: `ψ ∈ ND_s` with data `(a, ϖ)` such that `T_q ϖ ≥ ϖ`. -/
def IsInKq (q : ℝ) (ψ : ℝ → ℝ) : Prop :=
  ∃ P : SymLevyPair, HasExpData ψ P ∧ P.ν ≤ P.ν.map fun v => q * v

/-- **The `q`-Cin ray of cutoff `τ`**, `E^{(q)}_τ(ω) := ∑_{i ≥ 0} (1 - cos(ωτq^{-i}))`. -/
noncomputable def qCinRay (q τ ω : ℝ) : ℝ := ∑' i : ℕ, (1 - Real.cos (ω * (τ / q ^ i)))

/-- **`∑_{i ≥ 0} δ_{τq^{-i}}`**, the folded Lévy measure of `E^{(q)}_τ`. -/
noncomputable def qCinAtoms (q τ : ℝ) : Measure ℝ :=
  Measure.sum fun i : ℕ => Measure.dirac (τ / q ^ i)

/-- **`ψ(ω) = aω² + ∫ E^{(q)}_τ(ω) κ(dτ)`**, with `a ≥ 0` and `κ` a positive measure on
`(0,∞)`; the identity read in `[0,∞]`, so that the integral is never a junk value. -/
def IsQCinRepr (q : ℝ) (ψ : ℝ → ℝ) (a : ℝ) (κ : Measure ℝ) : Prop :=
  0 ≤ a ∧ κ (Iic 0) = 0 ∧ ∀ ω : ℝ,
    ENNReal.ofReal (ψ ω) = ENNReal.ofReal (a * ω ^ 2) + ∫⁻ τ, ENNReal.ofReal (qCinRay q τ ω) ∂κ

/-! ## `def:modulation-orbit` -/

/-- **The step `φ := Ψ_1(q ·) - Ψ_1`** of a knot exponent. -/
noncomputable def knotStep (q : ℝ) (Ψ1 : ℝ → ℝ) (ω : ℝ) : ℝ := Ψ1 (q * ω) - Ψ1 ω

/-- **A knot exponent** (`def:modulation-orbit`): `Ψ_1 ∈ ND_s` whose step lies in `ND_s` and is
not identically zero. -/
def IsKnotExponent (q : ℝ) (Ψ1 : ℝ → ℝ) : Prop :=
  IsSymLevyExponent Ψ1 ∧ IsSymLevyExponent (knotStep q Ψ1) ∧ ∃ ω : ℝ, knotStep q Ψ1 ω ≠ 0

/-- **`L` is the ladder of `Ψ_1`** (`def:modulation-orbit`), by specification: `L n` is the law
with the exponent `φ(q^n ·)`, `n ∈ ℤ`. -/
def IsKnotLadder (q : ℝ) (Ψ1 : ℝ → ℝ) (L : ℤ → Measure ℝ) : Prop :=
  ∀ n : ℤ, IsProbabilityMeasure (L n) ∧
    ∀ ω : ℝ, charFun (L n) ω = ((Real.exp (-knotStep q Ψ1 (q ^ n * ω)) : ℝ) : ℂ)

/-- **`m` is the step measure of the ladder of `Ψ_1`** (`def:modulation-orbit`): the folded Lévy
measure of the step `φ`. -/
def IsStepMeasure (q : ℝ) (Ψ1 : ℝ → ℝ) (m : Measure ℝ) : Prop :=
  ∃ P : SymLevyPair, HasExpData (knotStep q Ψ1) P ∧ P.ν = m

/-- **The ladder has no Gaussian part** (`def:modulation-orbit`): the Gaussian coefficient of `φ`
is `0`. -/
def HasNoGaussianStep (q : ℝ) (Ψ1 : ℝ → ℝ) : Prop :=
  ∃ P : SymLevyPair, HasExpData (knotStep q Ψ1) P ∧ P.a = 0

/-- **The modulation orbit of the ladder of `Ψ_1`** (`def:modulation-orbit`): the `q^ℤ`-covariant
families in the canonical discrete gauge whose knot kernel `μ_1` has the exponent `Ψ_1`. -/
def modulationOrbit (q : ℝ) (Ψ1 : ℝ → ℝ) : Set (ℝ → ℝ → Measure ℝ) :=
  {μ | IsQFamily q μ ∧ ∀ ω : ℝ, charFun (μ 0 1) ω = ((Real.exp (-Ψ1 ω) : ℝ) : ℂ)}

/-! ## § A.3: the phase entropy (`def:phase-entropy`) -/

/-- **`ρ̃(A) := σ([1,q) × A)`**, the `r`-marginal of a cylinder measure. -/
noncomputable def rMarginal (q : ℝ) (σ : Measure (ℝ × ℝ)) : Measure ℝ :=
  (σ.restrict (Ico 1 q ×ˢ univ)).map Prod.snd

/-- **`σ(dθ, dr) = π_r(dθ) ρ̃(dr)`** (`def:phase-entropy`): `π` is a measurable family of
probability measures on `[1,q)` with `σ(E) = ∫ π_r({θ : (θ, r) ∈ E}) ρ̃(dr)` for Borel `E`. -/
structure IsPhaseDisintegration (q : ℝ) (σ : Measure (ℝ × ℝ)) (π : ℝ → Measure ℝ) : Prop where
  measurable : Measurable π
  isProbability : ∀ r : ℝ, IsProbabilityMeasure (π r)
  carried : ∀ r : ℝ, π r (Ico 1 q)ᶜ = 0
  disintegrates : ∀ E : Set (ℝ × ℝ), MeasurableSet E →
    σ E = ∫⁻ r, π r ((fun θ => (θ, r)) ⁻¹' E) ∂(rMarginal q σ)

/-- **The phase entropy** `𝔈 := -∫ KL(π_r ‖ η) ρ̃(dr) ∈ [-∞, 0]` (`def:phase-entropy`), of the
cylinder measure `σ` with the disintegration `π`. -/
noncomputable def phaseEntropy (q : ℝ) (σ : Measure (ℝ × ℝ)) (π : ℝ → Measure ℝ) : EReal :=
  -(((∫⁻ r, InformationTheory.klDiv (π r) (haarPhase q) ∂(rMarginal q σ)) : ℝ≥0∞) : EReal)

/-- **`ν°`, the fold of `ν` onto the circle of phases**: its image under `v ↦ [v]`. -/
noncomputable def foldMeasure (q : ℝ) (ν : Measure ℝ) : Measure ℝ := ν.map (qClass q)

/-- **`rot_r[θ] := [rθ]`**, the rotation of the circle by `r`. -/
noncomputable def qRot (q r θ : ℝ) : ℝ := qClass q (r * θ)

/-- **`μ̄° := μ°/|μ|`**, the folded step normalized to a probability measure, `|μ| = μ((0,∞))`. -/
noncomputable def foldedStepNorm (q : ℝ) (m : Measure ℝ) : Measure ℝ :=
  (m univ)⁻¹ • foldMeasure q m

/-- **`P_r := (rot_r)_* π_r`**, the rotated fibre (`prop:phase-entropy-ladder-bound`(1)). -/
noncomputable def rotatedFibre (q : ℝ) (π : ℝ → Measure ℝ) (r : ℝ) : Measure ℝ :=
  (π r).map (qRot q r)

/-! ## § A.4: the classical generating kernels -/

/-- **`w` is a step of no family** (`prop:classical-kernels-no-exact-cascade`): `w` is not
infinitely divisible, and it is no kernel `μ_{s,t}` (in particular no `μ_{0,t}`) of any family of
operators satisfying (A1)–(A7), covariant or not. -/
def IsStepOfNoFamily (w : Measure ℝ) : Prop :=
  ¬ IsInfinitelyDivisible w ∧
    ∀ (Fam : ScaleSpace.PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ), ScaleSpace.IsPositive Fam.Φ →
      ScaleSpace.IsKernelFamily Fam.Φ μ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t ≠ w

/-! ## § A.4: Laplace atoms, the Matérn pyramid on the line, sequences -/

/-- **`mult(ϑ)`**, the number of `i` with `ϑ_i = ϑ`, in `ℕ∞`. -/
noncomputable def atomMult {ι : Type*} (θ : ι → ℝ) (ϑ : ℝ) : ℕ∞ := ENat.card {i // θ i = ϑ}

/-- **`h_t(ω) := (2/t) ∑_{i ≥ 1} (L̂_{ctq^{-i}}(ω) - 1)`**, `L̂_r(ω) = (1 + r²ω²)⁻¹`
(`thm:matern-pyramid-line`(3)). -/
noncomputable def maternLineGen (q c t ω : ℝ) : ℝ :=
  2 / t * ∑' i : ℕ, ((1 + (c * t / q ^ (i + 1)) ^ 2 * ω ^ 2)⁻¹ - 1)

/-- **`F_∞(ω) := ∫₀^∞ log(1 + c²ω²e^{-2u}) du`** (`thm:matern-pyramid-line`(4)). -/
noncomputable def maternLineLimit (c ω : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.log (1 + c ^ 2 * ω ^ 2 * Real.exp (-2 * u))

/-- **`S⁻(x)`, the number of sign changes of a real sequence on `ℤ`**, zeros deleted: the
supremum over finite increasing index sequences. -/
noncomputable def zSignChanges (x : ℤ → ℝ) : ℕ∞ :=
  ⨆ (n : ℕ) (k : Fin n → ℤ) (_ : StrictMono k),
    ((seqSignChanges (List.ofFn fun i => x (k i)) : ℕ) : ℕ∞)

/-- **`Δx(k) := x(k+1) - x(k)`**. -/
def zDiff (x : ℤ → ℝ) (k : ℤ) : ℝ := x (k + 1) - x k

/-! ## § A.5: random walks -/

/-- **`½(δ_v + δ_{-v})`**, the step law of the symmetric walk with steps `±v`. -/
noncomputable def symStep (v : ℝ) : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac v + Measure.dirac (-v))

/-- **`exp[c δ²_v] := e^{-c} ∑_{n ≥ 0} (cⁿ/n!) (½(δ_v + δ_{-v}))^{*n}`** (A.e9). -/
noncomputable def randomWalkLaw (c v : ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (Real.exp (-c) * c ^ n / (n.factorial : ℝ)) • convPow (symStep v) n

/-- **`K_N := exp[ℓδ²_τ] * exp[ℓδ²_{τq^{-1}}] * ⋯ * exp[ℓδ²_{τq^{-N}}]`**
(`prop:extreme-rays-random-walks`(2)). -/
noncomputable def qCinTruncation (q τ : ℝ) (N : ℕ) : Measure ℝ :=
  convList ((List.range (N + 1)).map fun i => randomWalkLaw (Real.log q) (τ / q ^ i))

end Pyramids
