/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Matern
import Pyramids.Defs.Helmholtz
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# The vocabulary of chapter 5, first part: the price of the plane

Blueprint: `blueprint/src/parts/05-price.tex` (§§ 5.1–5.3). Definitions only: nothing in this file
claims anything, and every identity the part's nodes state about these objects is a skeleton
statement (`PyramidsSkeleton.Ch05Price`).

## What is already defined, and is not repeated here

* Families of laws over any real inner product space `E`: (I1)–(I2) with the probability property
  (`IsLawHemigroup`, whose continuity clause is the continuity of `(s,t) ↦ μ̂_{s,t}(ω)`), and
  `λ`-covariance with a bijection (`IsCovariantAt`) (`Defs/Line.lean`).
* The ladder of a step, `(D_{q^n} w)_{n ∈ ℤ}` (`dilLadder`), the knot kernels `μ_{q^n}`
  (`knotKernel`), the partial products and partial convolutions of the knot kernel (`ladderProd`,
  `ladderConv`), `ν* = ∑_{m ≥ 1} D_{q^{-m}} ν` (`ladderNuStar`), the equivalent weights
  `w * D_q w * ⋯ * D_{q^{n-1}} w` (`equivWeight`), the tensor power of a law on the line
  (`tensorPow`) and the uniform law on `[-h/2, h/2]` (`uniformInterval`) (`Defs/Pyramid.lean`).
* The grid `ℤ^d` and its kernels (`Zd`, `IsProbKernel`, `kconv`, `kpow`, `deltaZ`, `zbasis`,
  `gridFourier`), `Δ_h` (`gridLap`), the random walk step (`rwStep`), the five-point resolvent
  (`discreteHelmholtz`), the discrete Helmholtz family (`helmKernel`) and its exact subsample
  (`IsExactSubsample`) (`Defs/PaperVI.lean`); the nine-point Laplacian, step and resolvent
  (`Defs/Helmholtz.lean`).
* Laws on `hℤ` (`gridLaw`), the binomial mask (`binomialMask5`), the sampled Laplace mask
  `λ^L_a = geomKernel a` (`Defs/Line.lean`, `Pyramids.SubsamplingLine`), and the line's grid
  pyramids (`IsGridMask`, `IsExactGridPyramid`) (`Defs/Line.lean`).
* The principle on a neighbourhood (`HasGridImplicitEulerPrinciple`, `IsNMax`), the axis
  neighbours (`axisNbrs`), laws on `hℤ^d` (`zdLaw`), compound Poisson laws on `ℝ^d`
  (`compoundPoissonLaw`) and the decimated records (`decimRecord`) (`Defs/Matern.lean`).
* The affine export's `Rd`, `Mat`, `lin`, `push`, `orthSet`, `ebasis`, `LevyTriplet`, `HasTriplet`,
  `IsInfinitelyDivisible`; the shared core's `convPow`.

## What is defined here

* `def:grid-family`: the resolvent of a stencil (`IsStencilResolvent`), the family of a stencil
  (`stencilFamily`), the powers of a mask (`maskPowers`);
* `def:exact-senses`: sense (i) (`IsExactLawArray`, `IsExactSampleArray`, with `latticePt`),
  sense (ii) (`IsExactSubsampleIn`), sense (iii) (`IsExactLatticePyramid`);
* `def:exact-grid-pyramid`: masks (`IsLatticeMask`), the carrying family (`CarriesLatticeLadder`),
  exactness (`IsExactLatticePyramid`), rotation invariance under `SO(d)`
  (`IsSORotationInvariant`), isotropy (`IsIsotropicCarrier`);
* the objects the statements introduce: `hℤ^d` as a set (`gridSet`), `Γ_q` (`qLatticeUnion`), the
  Lévy measure and the Gaussian part of a law (`HasLevyMeasure`, `HasNoGaussianPart`), the symmetry
  group (`symmetryGroup`), the signed permutations (`signedPermSet`), the coordinate axes
  (`axesSet`), the frame Lévy measure (`frameKnotLevy`), the uniform coupling (`uniformCouplingNu`),
  the resolvent mask and its Lévy measure (`resolventMask`, `resolventLevy`), the step of a stencil
  (`stencilStep`), tensor and axis kernels on `ℤ^d` (`tensorIdx`, `axisPassIdx`), and the lattice
  read through a basis (`latticeIdxPt`, `latticeIdxKernel`, `latticeApply`).

## Readings fixed here

* **Grid families are sets of kernels on `ℤ^d`**, the indices of the lattice, as chapter 4 reads
  kernels on `hℤ^d` (its finding 15). Item (1) of `def:grid-family` on `hℤ^d` is
  `stencilFamily (gridLap h)`, on `hℤ²` with the nine-point Laplacian
  `stencilFamily (ninePointLap h)`; the resolvents are taken **by specification**, the summable
  solutions of `(1 - t²L)κ = δ₀`, as the node defines them (they are unique, and equal to
  `discreteHelmholtz` and `ninePointHelmholtz`: `prop:discrete-helmholtz`(1),
  `prop:nine-point-family`(1)). Item (2) is `maskPowers w`. In the indices of the coarse grid
  `qΓ` the dilated mask `D_q w` is the same array `w`, so the family of item (2) on `qΓ` is again
  `maskPowers w`; the family of item (1) on `qhℤ^d` is `stencilFamily (gridLap (q h))`.
* **Sense (ii)** (`IsExactSubsampleIn F' q λ`) reads the subsample in the coarse grid's indices,
  `m ↦ λ(qm)`, and its renormalizing constant as the real series `C = ∑ₘ λ(qm)`. It asks `C > 0`,
  so a non-summable subsample (whose `tsum` is the junk `0`) is never exact. `F'` is the family on
  `qΓ` the node names. The machine-checked `IsExactSubsample` (`prop:helmholtz-subsampling`) is
  this sense for the five-point family, with the member written `helmKernel` and the constant
  existential.
* **Sense (i)** is read in exact arithmetic: "equal up to rounding" is equality. For a lattice law
  it is `IsExactLawArray`; for a continuum kernel with density `p` it is equality with the
  renormalized samples `p(hn)/∑ₘ p(hm)` (`IsExactSampleArray`), the sum asked positive.
* **An exact grid pyramid** is read on any real inner product space `E`, so that the line's
  `def:grid-pyramid-line` can be compared with it at `E = ℝ` (`prop:line-and-arrays`(1)). Its (a)
  and (b) are `IsLawHemigroup`: (b), weak continuity on `{0 ≤ s ≤ t}`, is the continuity of
  `(s,t) ↦ μ̂_{s,t}(ω)` at each `ω`, which is the same for probability laws on `ℝ^d` by Lévy's
  continuity theorem (the reading of chapters 2 and 3). (c) is `IsCovariantAt μ q (q ·)`, which
  also asks that `t ↦ qt` be an increasing bijection of `[0,∞)` (true for `q > 0`). `q > 1` is
  part of the definition, as in the node. The conditions do not mention `Γ`, so exactness is a
  property of `(w, q)`; the mask condition is `IsLatticeMask`, on a set `Γ` (a full-rank lattice is
  a `Submodule ℤ (Rd d)` with `DiscreteTopology` and `IsZLattice ℝ`, coerced to a set; `hℤ^d` is
  `gridSet d h`).
* **Rotation invariance** in `def:exact-grid-pyramid` is under `SO(d)`, as the node says
  (`IsSORotationInvariant`); the affine export's `IsRotationInvariant` is under `O(d)`.
* **The Lévy measure and the Gaussian part of a law** are read through Sato's generating triplets
  (`HasTriplet`): `HasLevyMeasure μ ν` says that `μ` has a triplet and that every triplet of `μ`
  has Lévy measure `ν` (`thm:cited-A39` makes the triplet unique, so this is "the Lévy measure of
  `μ` is `ν`"); `HasNoGaussianPart μ` likewise with `A = 0`. Neither is vacuous: both ask a
  triplet to exist.
* **The support of a law carried by a lattice** is its set of atoms (a lattice is closed and
  discrete), so "`supp w` spans `ℝ^d`" is read `span_ℝ {x | w{x} ≠ 0} = ℝ^d` in the statements.
* **Records** (`def:level-records`) are `decimRecord`, in the index coordinates of each level: a
  basis `b` of `Γ` identifies `Γ` with `ℤ^d` and `q^kΓ` with `ℤ^d` through `q^k b`; in the indices
  of level `j` the dilated mask `D_{q^j} w` is the array `w`, and the restriction to `q^{j+1}Γ` is
  `m ↦ (w * f_j)(qm)`. For `Γ = hℤ^d` the basis is `h e_i` (chapter 4's reading). A law `μ` on
  `ℝ^d` applied to an array on `Γ` and read at an index is `latticeApply b μ f m`,
  `∑_k μ{b k} f(m - k)`, which is `(μ * f)(b m)` when `μ` is carried by `Γ`.
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set
open ScaleSpace (convPow)
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## Grid families (`def:grid-family`) -/

/-- **`κ` is a summable solution of `(1 - t²L)κ = δ₀`** for an operator `L` on kernels of `ℤ^d`
(`def:grid-family`(1); `L = Δ_h` is `gridLap h`, `L = Δ_9` is `ninePointLap h`). -/
def IsStencilResolvent (L : (Zd d → ℝ) → Zd d → ℝ) (t : ℝ) (κ : Zd d → ℝ) : Prop :=
  Summable κ ∧ ∀ n, κ n - t ^ 2 * L κ n = deltaZ n

/-- **The grid family of a stencil** (`def:grid-family`(1)): the convolution powers `κ_t^{*γ}`,
`t > 0`, `γ ≥ 1` an integer, of the resolvents `κ_t` of `L`. -/
def stencilFamily (L : (Zd d → ℝ) → Zd d → ℝ) : Set (Zd d → ℝ) :=
  {lam | ∃ t : ℝ, 0 < t ∧ ∃ γ : ℕ, 1 ≤ γ ∧ ∃ κ : Zd d → ℝ, IsStencilResolvent L t κ ∧
    lam = kpow κ γ}

/-- **The grid family of a mask** `w` (`def:grid-family`(2)): its convolution powers `w^{*n}`,
`n ≥ 1`. -/
def maskPowers (w : Zd d → ℝ) : Set (Zd d → ℝ) := {lam | ∃ n : ℕ, 1 ≤ n ∧ lam = kpow w n}

/-! ## The senses of *exact* (`def:exact-senses`) -/

/-- **The point `hn` of `hℤ^d`**, `n ∈ ℤ^d`. -/
noncomputable def latticePt (h : ℝ) (n : Zd d) : Rd d := h • WithLp.toLp 2 fun i => (n i : ℝ)

/-- **`hℤ^d`**, as a set of points of `ℝ^d`. -/
def gridSet (d : ℕ) (h : ℝ) : Set (Rd d) := {x | ∃ n : Zd d, x = latticePt h n}

/-- **Sense (i), a lattice law** (`def:exact-senses`(i)): the computed array `A` equals the law
`κ` it stands for (in exact arithmetic). -/
def IsExactLawArray {ι : Type*} (A κ : ι → ℝ) : Prop := ∀ n, A n = κ n

/-- **Sense (i), a continuum kernel** (`def:exact-senses`(i)): the computed array `A` on `hℤ^d`
equals the renormalized samples `p(hn)/∑ₘ p(hm)` of the kernel with density `p`. -/
def IsExactSampleArray (h : ℝ) (p : Rd d → ℝ) (A : Zd d → ℝ) : Prop :=
  Summable (fun m : Zd d => p (latticePt h m)) ∧ 0 < ∑' m : Zd d, p (latticePt h m) ∧
    ∀ n, A n = p (latticePt h n) / ∑' m : Zd d, p (latticePt h m)

/-- **Sense (ii)** (`def:exact-senses`(ii)): for an integer `q ≥ 2`, the subsample
`m ↦ λ(qm)` of `λ`, renormalized by the mass it keeps `C = ∑ₘ λ(qm) > 0`, is a member of the
family `F'` on the coarse grid `qΓ` (read in its indices). -/
def IsExactSubsampleIn (F' : Set (Zd d → ℝ)) (q : ℕ) (lam : Zd d → ℝ) : Prop :=
  2 ≤ q ∧ 0 < ∑' m : Zd d, lam ((q : ℤ) • m) ∧
    (fun m => (∑' m' : Zd d, lam ((q : ℤ) • m'))⁻¹ * lam ((q : ℤ) • m)) ∈ F'

/-! ## The exact grid pyramid (`def:exact-grid-pyramid`) -/

/-- **A mask on `Γ`** (`def:exact-grid-pyramid`): a symmetric probability law `w ≠ δ₀` carried by
`Γ`. -/
def IsLatticeMask (Γ : Set (Rd d)) (w : Measure (Rd d)) : Prop :=
  IsProbabilityMeasure w ∧ w.map (fun x => -x) = w ∧ w ≠ Measure.dirac 0 ∧ w Γᶜ = 0

section Families

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- **`μ` carries the grid pyramid of `(w, q)`** (`def:exact-grid-pyramid`): `q > 1`; the
`μ s t`, `0 ≤ s ≤ t`, are probability laws with (a) and (b) (`IsLawHemigroup`); (c)
`μ_{qs,qt} = D_q μ_{s,t}`; and (d) `μ_{1,q} = w`. -/
def CarriesLatticeLadder (q : ℝ) (w : Measure E) (μ : ℝ → ℝ → Measure E) : Prop :=
  1 < q ∧ IsLawHemigroup μ ∧ IsCovariantAt μ q (fun t => q * t) ∧ μ 1 q = w

/-- **The grid pyramid of `(w, q)` is exact** (`def:exact-grid-pyramid`; sense (iii) of
`def:exact-senses`): some family carries it. -/
def IsExactLatticePyramid (q : ℝ) (w : Measure E) : Prop :=
  ∃ μ : ℝ → ℝ → Measure E, CarriesLatticeLadder q w μ

end Families

/-- **Rotation invariance under `SO(d)`**: `D_R μ = μ` for every `R ∈ SO(d)`. -/
def IsSORotationInvariant (μ : Measure (Rd d)) : Prop :=
  ∀ R ∈ orthSet d, R.det = 1 → push R μ = μ

/-- **The pyramid carried by `μ` is isotropic** (`def:exact-grid-pyramid`): some kernel `μ_t`,
`t > 0`, is rotation invariant. -/
def IsIsotropicCarrier (μ : ℝ → ℝ → Measure (Rd d)) : Prop :=
  ∃ t : ℝ, 0 < t ∧ IsSORotationInvariant (μ 0 t)

/-! ## The objects of `prop:grid-pyramid-not-isotropic` -/

/-- **`Γ_q := ⋃_{k ∈ ℤ} q^k Γ`**. -/
def qLatticeUnion (q : ℝ) (Γ : Set (Rd d)) : Set (Rd d) := ⋃ k : ℤ, (fun x => (q ^ k) • x) '' Γ

/-- **The Lévy measure of `μ` is `ν`**: `μ` has a generating triplet, and every generating
triplet of `μ` has Lévy measure `ν`. -/
def HasLevyMeasure (μ ν : Measure (Rd d)) : Prop :=
  (∃ T : LevyTriplet d, HasTriplet μ T) ∧ ∀ T : LevyTriplet d, HasTriplet μ T → T.ν = ν

/-- **`μ` has no Gaussian part**: `μ` has a generating triplet, and every generating triplet of
`μ` has `A = 0`. -/
def HasNoGaussianPart (μ : Measure (Rd d)) : Prop :=
  (∃ T : LevyTriplet d, HasTriplet μ T) ∧ ∀ T : LevyTriplet d, HasTriplet μ T → T.A = 0

/-- **The symmetry group** `{R ∈ O(d) : D_R μ = μ}` of a law. -/
def symmetryGroup (μ : Measure (Rd d)) : Set (Mat d) := {R | R ∈ orthSet d ∧ push R μ = μ}

/-- **The hyperoctahedral group**: the signed permutations of the axes, `R e_j = s_j e_{σ(j)}`
with `s_j = ±1`. -/
def signedPermSet (d : ℕ) : Set (Mat d) :=
  {R | ∃ σ : Equiv.Perm (Fin d), ∃ s : Fin d → ℝ, (∀ j, s j = 1 ∨ s j = -1) ∧
    R = Matrix.of fun i j => if i = σ j then s j else 0}

/-- **The coordinate axes** `⋃ᵢ ℝ eᵢ`. -/
def axesSet (d : ℕ) : Set (Rd d) := {x | ∃ i : Fin d, ∃ c : ℝ, x = c • ebasis i}

/-- **`ν_1 = ∑_{i ≤ d} ∑_{m ≥ 1} ∑_{n ≠ 0} (a^{|n|}/|n|) δ_{nhq^{-m}eᵢ}`** (`eq:frame-levy`). -/
noncomputable def frameKnotLevy (d : ℕ) (q h a : ℝ) : Measure (Rd d) :=
  Measure.sum fun i : Fin d => Measure.sum fun m : ℕ => Measure.sum fun n : ℤ =>
    if n = 0 then 0 else
      ENNReal.ofReal (a ^ n.natAbs / n.natAbs) •
        Measure.dirac (((n : ℝ) * h * q ^ (-((m : ℤ) + 1))) • ebasis i)

/-! ## The uniform coupling (`prop:exact-masks`(2)) -/

/-- **The Lévy measures of the uniform coupling**: `ν_t := ν* + (log_q t) ν` for `t ∈ [1, q)`,
`ν_{q^n t} := D_{q^n} ν_t`, and `0` at `t ≤ 0`; `n = ⌊log_q t⌋` (`dgLevel`). -/
noncomputable def uniformCouplingNu (q : ℝ) (ν : Measure (Rd d)) (t : ℝ) : Measure (Rd d) :=
  if t ≤ 0 then 0 else
    (ladderNuStar q ν + ENNReal.ofReal (Real.logb q (q ^ (-dgLevel q t) * t)) • ν).map
      fun x => (q ^ dgLevel q t) • x

/-! ## Resolvent masks (`prop:resolvent-masks-exact`) -/

/-- **`w := (1-p) ∑_{k ≥ 0} p^k σ^{*k}`** (`eq:resolvent-mask`). -/
noncomputable def resolventMask (p : ℝ) (σ : Measure (Rd d)) : Measure (Rd d) :=
  Measure.sum fun k : ℕ => ENNReal.ofReal ((1 - p) * p ^ k) • convPow σ k

/-- **`ν_w`, the restriction of `∑_{k ≥ 1} (p^k/k) σ^{*k}` to `ℝ^d ∖ {0}`**
(`prop:resolvent-masks-exact`(1)). -/
noncomputable def resolventLevy (p : ℝ) (σ : Measure (Rd d)) : Measure (Rd d) :=
  (Measure.sum fun k : ℕ =>
    ENNReal.ofReal (p ^ (k + 1) / ((k : ℝ) + 1)) • convPow σ (k + 1)).restrict {0}ᶜ

/-- **`σ := (2C)⁻¹ ∑_{y ∈ 𝒩} c_y (δ_y + δ_{-y})`**, `C = ∑_{y ∈ 𝒩} c_y`
(`prop:resolvent-masks-exact`(4)). -/
noncomputable def stencilStep (N : Finset (Rd d)) (c : Rd d → ℝ) : Measure (Rd d) :=
  ENNReal.ofReal (2 * ∑ y ∈ N, c y)⁻¹ •
    ∑ y ∈ N, ENNReal.ofReal (c y) • (Measure.dirac y + Measure.dirac (-y))

/-! ## Kernels on `ℤ^d` built from kernels on `ℤ` -/

/-- **The tensor kernel** `(k^{⊗d})(n) := ∏ᵢ k(nᵢ)` on `ℤ^d`. -/
def tensorIdx (k : ℤ → ℝ) : Zd d → ℝ := fun n => ∏ i, k (n i)

/-- **The kernel `k` carried by the axis `ℤ eᵢ`**: `k(nᵢ)` when `n` lies on the axis, `0`
otherwise. -/
noncomputable def axisPassIdx (k : ℤ → ℝ) (i : Fin d) : Zd d → ℝ := fun n => by
  classical exact if ∀ j, j ≠ i → n j = 0 then k (n i) else 0

/-! ## A lattice read through a basis (`prop:line-and-arrays`(2)) -/

/-- **The point `∑ᵢ kᵢ bᵢ` of `Γ`**, for a basis `b` of `Γ` and `k ∈ ℤ^d`. -/
noncomputable def latticeIdxPt {Γ : Submodule ℤ (Rd d)} (b : Module.Basis (Fin d) ℤ Γ)
    (k : Zd d) : Rd d :=
  ((b.equivFun.symm k : Γ) : Rd d)

/-- **The array of a law on `Γ`** in the indices of `b`: `k ↦ w{b k}`. -/
noncomputable def latticeIdxKernel {Γ : Submodule ℤ (Rd d)} (b : Module.Basis (Fin d) ℤ Γ)
    (w : Measure (Rd d)) : Zd d → ℝ :=
  fun k => (w {latticeIdxPt b k}).toReal

/-- **A law applied to an array on `Γ`**, read at the index `m`: `∑_k μ{b k} f(m - k)`, which is
`(μ * f)(b m)` when `μ` is carried by `Γ`. -/
noncomputable def latticeApply {Γ : Submodule ℤ (Rd d)} (b : Module.Basis (Fin d) ℤ Γ)
    (μ : Measure (Rd d)) (f : Zd d → ℝ) (m : Zd d) : ℝ :=
  ∑' k : Zd d, (μ {latticeIdxPt b k}).toReal * f (m - k)

end Pyramids
