/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Pyramid
import AffineHemigroup.Defs.Origin
import AffineHemigroup.Defs.Orbits
import ScaleSpaceCore.L1OperatorsSpace
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# The vocabulary of chapter 4: the Matérn pyramid

Blueprint: `blueprint/src/parts/04-matern.tex`. Definitions only: nothing in this file claims
anything, and every identity the chapter's nodes state about these objects is a skeleton statement
(`PyramidsSkeleton.Ch04Matern`).

## What is already defined, and is not repeated here

* The families of chapter 3: `IsIsotropicFamily`, `IsSymmetricFamily`, `IsCovariantAt`,
  `IsFullyCovariantLaws`, laws by their exponents (`IsExponentLaws`), the gauge group `𝒢_q`
  (`IsInGaugeGroup`, `extendByZero`) and the polar Lévy measure of a profile (`polarLevyMeasure`)
  (`Defs/Pyramid.lean`).
* Complete monotonicity, Bernstein, complete Bernstein and Thorin–Bernstein functions, Pólya
  frequency densities and sign changes in the essential sense (`Defs/Cited.lean`).
* The affine export's `Rd`, `Mat`, `quad`, `ebasis`, `marginal`, `OriginDatum`, `classA`,
  `IsIsotropicCascadeFamily`, `IsGauge`, `IsInfinitelyDivisible`, `LevyTriplet`, `HasTriplet`,
  `IsRotationInvariant`, `sphereArea`, the Gaussian `gaussVar d u = N(0, uI)` and the transform with
  the blueprint's convention `fourierPlus`; the shared core's `besselK` (`K_ν`, DLMF 10.32.9),
  `mconvE` (`(μ * f)(x) = ∫ f(x - y) μ(dy)` on `ℝ^d`) and `convPow`.
* The grid of `Defs/PaperVI.lean`: kernels on `ℤ^d` (`Zd`, `IsProbKernel`, `kconv`, `deltaZ`,
  `zbasis`, `gridFourier`), the weak derivatives `IsWeakPartial`, `IsWeakPartial2`, the Gaussian
  density `gaussDensityCov`, and `lineConv` on the line.

## What is defined here

* `def:matern-pyramid-data`: the octave step `L_r` (`maternStep`), the exponent `F_q`
  (`maternExponent`) and the profile `b_d` (`besselProfile`);
* `def:implicit-euler-principle`: the principle on `ℝ^d` (`HasImplicitEulerPrinciple`),
  `𝒩`-maxima and `𝒩`-minima (`IsNMax`, `IsNMin`) and the principle on `𝒩`
  (`HasGridImplicitEulerPrinciple`);
* the objects the statements introduce: the integral `G` and the density of `L_r`
  (`maternGreenE`, `maternDensityE`), the polar profile `k_d` (`maternPolarProfile`), the Matérn
  pyramid and its frame twin by specification (`IsMaternPyramid`, `IsFrameMaternPyramid`), the
  projection of a function (`IsProjectionDensity`), `W^{2,1}` (`IsW21`), the generator and its
  symbol (`maternGenerator`, `maternGenSymbol`), the dilogarithm and the limit exponent (`dilog`,
  `maternLimitExponent`), `P_d` and `E_1` (`besselTail`, `expIntegralE1`), the increment exponent
  `f_{β,γ}` and its law (`maternIncExponent`, `maternIncLaw`), compound Poisson laws on `ℝ^d`
  (`compoundPoissonLaw`), the witness `h_{a,δ}` (`creationWitness`), the axis neighbours
  (`axisNbrs`), laws on `hℤ^d` (`zdLaw`) and the decimated records (`decimRecord`).

## Readings fixed here

* **`L_r` is the law of `r√(2X) Z`, as the node prints it**: the shared `gammaGaussLaw d 1` (the
  law of `√(2V) Z`, `V` Gamma of shape `1` and scale `1`, that is standard exponential, and `Z`
  standard normal, independent: a product measure and its image under a continuous map) dilated
  by `r`. The node's first description, the mixture `∫₀^∞ e^{-s} N(0, 2sr²I) ds`, is the same
  measure by the definition of a mixture. The law is not written as a `Measure.bind` into
  `gaussVar d`: `bind` is `0` when the kernel is not measurable, which nothing in the library
  supplies for `u ↦ N(0, uI)`, so that form would carry an unproved obligation in every statement
  about `L_r` (skeleton review 03-04, F5). The image of a product measure under a measurable map
  carries none.
* **`F_q` is a real series** (`tsum`). "The series converges" is a claim inside the definition
  node and is not typed here (a definition carries no lemma); every statement that reads `F_q`
  through a summed form asks its summability where a junk value could enter.
* **`G` takes values in `(0,∞]`**, as the node says: it is a lower Lebesgue integral, `∞` at the
  origin when `d ≥ 2`, never a Bochner junk value. The density of `L_r` is `r^{-d} G(x/r)` in
  `[0,∞]`.
* **Records and the generator** are pointwise: `H_t g (x) = (2/t) ∑ᵢ ((L_{r_i} * g)(x) - g(x))`,
  a pointwise `tsum`. Where the node reads the series in `L¹` the statements ask its absolute
  convergence in `L¹` (`eLpNorm … 1`), which makes the pointwise sum the `L¹` sum almost
  everywhere; `eLpNorm` has no junk value.
* **Kernels on `hℤ^d` are indexed by `ℤ^d`**, as `def:neighbourhood-principle` reads them: a
  neighbourhood `𝒩 ⊂ hℤ^d ∖ {0}` is a set of indices, and an `𝒩`-maximum of `u` is
  `u(x + y) ≤ u(x)` for every `y ∈ 𝒩`. Every notion here is invariant under `n ↦ hn`.
* **The principle is the condition alone.** `HasImplicitEulerPrinciple μ` is the clause on outputs;
  the node defines it for a symmetric probability measure, and every statement carries that
  hypothesis beside it where it reads the principle as a hypothesis. A negative statement
  (`¬ HasImplicitEulerPrinciple μ`) so says that the clause fails, not that `μ` is not symmetric.
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set
open ScaleSpace (mconvE convPow)
open scoped ENNReal RealInnerProductSpace SchwartzMap

variable {d : ℕ}

/-! ## The octave step and the Matérn exponent (`def:matern-pyramid-data`) -/

/-- **`L_r := ∫₀^∞ e^{-s} N(0, 2sr²I) ds`** (`def:matern-pyramid-data`), the Matérn law of index
`1` at range `r`, read as the node's second description, the law of `r√(2X) Z`: the shared
`gammaGaussLaw d 1` (the law of `√(2X) Z`) dilated by `r`. -/
noncomputable def maternStep (d : ℕ) (r : ℝ) : Measure (Rd d) :=
  (gammaGaussLaw d 1).map fun x => r • x

/-- **`F_q(r) := ∑_{i ≥ 1} log(1 + c² q^{-2i} r²)`** (`def:matern-pyramid-data`), a real series. -/
noncomputable def maternExponent (q c r : ℝ) : ℝ :=
  ∑' i : ℕ, Real.log (1 + c ^ 2 * r ^ 2 / q ^ (2 * (i + 1)))

/-- **`b_d(y) := (2/Γ(d/2)) ∫₀^∞ v^{d/2-1} e^{-v - y²/(4v)} dv`** (`def:matern-pyramid-data`). -/
noncomputable def besselProfile (d : ℕ) (y : ℝ) : ℝ :=
  2 / Real.Gamma ((d : ℝ) / 2) *
    ∫ v in Ioi (0 : ℝ), v ^ ((d : ℝ) / 2 - 1) * Real.exp (-v - y ^ 2 / (4 * v))

/-! ## The density of `L_r` and the polar profile (`lem:bessel-profile`, `thm:matern-pyramid`) -/

/-- **`G(x) := ∫₀^∞ e^{-s} (4πs)^{-d/2} e^{-|x|²/(4s)} ds ∈ (0,∞]`** (`lem:bessel-profile`(1)),
a lower Lebesgue integral. -/
noncomputable def maternGreenE (d : ℕ) (x : Rd d) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0 : ℝ),
    ENNReal.ofReal (Real.exp (-s) * (4 * Real.pi * s) ^ (-(d : ℝ) / 2) *
      Real.exp (-(‖x‖ ^ 2) / (4 * s)))

/-- **The density `r^{-d} G(x/r)` of `L_r`**, in `[0,∞]`. -/
noncomputable def maternDensityE (d : ℕ) (r : ℝ) (x : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (r ^ (-(d : ℝ))) * maternGreenE d (r⁻¹ • x)

/-- **`k_d(r) := ∑_{i ≥ 1} b_d(r q^i / c)`** (`thm:matern-pyramid`(1)), a real series. -/
noncomputable def maternPolarProfile (q c : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  ∑' i : ℕ, besselProfile d (r * q ^ (i + 1) / c)

/-! ## The Matérn pyramid and its frame twin, by specification -/

section Families

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- **The Matérn pyramid with the constants `q`, `c`** (`thm:matern-pyramid`(1)), by
specification: probability measures `μ_{s,t}`, `0 ≤ s ≤ t`, with
`μ̂_{s,t}(ω) = exp(-(F_q(t|ω|) - F_q(s|ω|)))`. On `E = ℝ` it is the Matérn pyramid on the line of
`thm:matern-pyramid-line`, whose exponent `F_q` is even. -/
def IsMaternPyramid (q c : ℝ) (μ : ℝ → ℝ → Measure E) : Prop :=
  IsExponentLaws (fun t ω => maternExponent q c (t * ‖ω‖)) μ

end Families

/-- **The frame Matérn pyramid** (`prop:creation-plane`(3), `thm:selection-stratum-two`(4)), by
specification: the laws with transforms `∏_j exp(-(F_q(t|ω_j|) - F_q(s|ω_j|)))`, the product of
the line's Matérn pyramids along the axes. -/
def IsFrameMaternPyramid (q c : ℝ) (μ : ℝ → ℝ → Measure (Rd d)) : Prop :=
  IsExponentLaws (fun t ω => ∑ j, maternExponent q c (t * |ω j|)) μ

/-! ## Projections, Sobolev functions, the generator -/

/-- **`p` is the projection of `g` along `e`** (`thm:matern-pyramid`(3)): the density of the image
of `g(x) dx` under `x ↦ ⟨e, x⟩`, that is `p` integrable with `∫_A p = ∫_{⟨e,x⟩ ∈ A} g` for every
Borel `A`. Determined by `g` up to a null set. -/
def IsProjectionDensity (e : Rd d) (g : Rd d → ℝ) (p : ℝ → ℝ) : Prop :=
  Integrable p ∧ ∀ A : Set ℝ, MeasurableSet A →
    ∫ σ in A, p σ = ∫ x in (fun x : Rd d => ⟪e, x⟫) ⁻¹' A, g x

/-- **`g ∈ W^{2,1}(ℝ^d)`**: `g` integrable with every weak derivative of order at most `2`
integrable (the weak derivatives tested against complex test functions, `IsWeakPartial`). -/
def IsW21 (g : Rd d → ℝ) : Prop :=
  Integrable g ∧
    (∀ k, ∃ v : Rd d → ℝ, Integrable v ∧
      IsWeakPartial k (fun x => (g x : ℂ)) (fun x => (v x : ℂ))) ∧
    ∀ i j, ∃ v : Rd d → ℝ, Integrable v ∧
      IsWeakPartial2 i j (fun x => (g x : ℂ)) (fun x => (v x : ℂ))

/-- **`H_t g := (2/t) ∑_{i ≥ 1} (L_{ctq^{-i}} * g - g)`** (`thm:matern-pyramid`(4)), pointwise. -/
noncomputable def maternGenerator (d : ℕ) (q c t : ℝ) (g : Rd d → ℝ) (x : Rd d) : ℝ :=
  2 / t * ∑' i : ℕ, (mconvE (maternStep d (c * t / q ^ (i + 1))) g x - g x)

/-- **The symbol `σ_t(ω) := -(2/t) ∑_{i ≥ 1} β_i|ω|²/(1 + β_i|ω|²)`, `β_i := c² q^{-2i} t²`**
(`prop:matern-generator-octave`(1)). -/
noncomputable def maternGenSymbol (q c t : ℝ) (ω : Rd d) : ℝ :=
  -(2 / t) * ∑' i : ℕ,
    c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) * ‖ω‖ ^ 2 / (1 + c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) * ‖ω‖ ^ 2)

/-! ## The limit `q ↓ 1` (`thm:matern-pyramid`(5), `prop:thorin-in-dimension-d`(2)) -/

/-- **The dilogarithm** `Li₂(x) := -∫₀^x log(1 - u) du/u` (DLMF 25.12.2), read at real `x ≤ 1`. -/
noncomputable def dilog (x : ℝ) : ℝ := -∫ u in (0 : ℝ)..x, Real.log (1 - u) / u

/-- **`Λ(r) := -½ Li₂(-c²r²)`** (`thm:matern-pyramid`(5)). -/
noncomputable def maternLimitExponent (c r : ℝ) : ℝ := -(1 / 2) * dilog (-(c ^ 2 * r ^ 2))

/-- **`P_d(y) := ∫_y^∞ b_d(v) dv/v`** (`prop:thorin-in-dimension-d`(2)). -/
noncomputable def besselTail (d : ℕ) (y : ℝ) : ℝ := ∫ v in Ioi y, besselProfile d v / v

/-- **The exponential integral** `E_1(y) := ∫_y^∞ e^{-v} dv/v`. -/
noncomputable def expIntegralE1 (y : ℝ) : ℝ := ∫ v in Ioi y, Real.exp (-v) / v

/-! ## The increments (`prop:matern-increments`) -/

/-- **`f_{β,γ}(u) := log((1 + βu)/(1 + γu))`**. -/
noncomputable def maternIncExponent (β γ u : ℝ) : ℝ := Real.log ((1 + β * u) / (1 + γ * u))

/-- **The mixture `(γ/β) δ₀ + (1 - γ/β) L_{√β}`** (`prop:matern-increments`(2)). -/
noncomputable def maternIncLaw (d : ℕ) (β γ : ℝ) : Measure (Rd d) :=
  ENNReal.ofReal (γ / β) • Measure.dirac 0 + ENNReal.ofReal (1 - γ / β) • maternStep d (Real.sqrt β)

/-- **The compound Poisson law** `e^{-ν(ℝ^d)} ∑_{n ≥ 0} ν^{*n}/n!` of a finite measure `ν` on
`ℝ^d` (Sato, Def. 4.1). -/
noncomputable def compoundPoissonLaw (ν : Measure (Rd d)) : Measure (Rd d) :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (Real.exp (-(ν univ).toReal) / (n.factorial : ℝ)) • convPow ν n

/-! ## Creation (`prop:creation-plane`, `prop:creation-grid`) -/

/-- **`h_{a,δ}(x) := e^{-|x - ae₁|²/2} + e^{-|x + ae₁|²/2} + 8a² e^{-x₁²/(8a²)} e^{-|x'|²/(2δ²)}`**,
`x = (x₁, x')`, `x₁` the coordinate `0`, `|x'|² = |x|² - x₁²` (`prop:creation-plane`). -/
noncomputable def creationWitness (d : ℕ) [NeZero d] (a δ : ℝ) (x : Rd d) : ℝ :=
  Real.exp (-‖x - a • ebasis 0‖ ^ 2 / 2) + Real.exp (-‖x + a • ebasis 0‖ ^ 2 / 2) +
    8 * a ^ 2 * Real.exp (-(x 0) ^ 2 / (8 * a ^ 2)) *
      Real.exp (-(‖x‖ ^ 2 - (x 0) ^ 2) / (2 * δ ^ 2))

/-- **The law on `hℤ^d` with the point masses `w(n)` at `hn`**, a measure on `ℝ^d`. -/
noncomputable def zdLaw (d : ℕ) (h : ℝ) (w : Zd d → ℝ) : Measure (Rd d) :=
  Measure.sum fun n : Zd d =>
    ENNReal.ofReal (w n) • Measure.dirac (h • WithLp.toLp 2 fun i => (n i : ℝ))

/-- **The decimated records** of `prop:creation-grid`(3), in the index coordinates of each level:
`f_0 = f` and `f_{j+1}(m) := (w * f_j)(qm)`, the smoothing by `D_{q^j} w` on `q^j hℤ^d` read on
`q^{j+1} hℤ^d`. -/
noncomputable def decimRecord (w : Zd d → ℝ) (q : ℕ) (f : Zd d → ℝ) : ℕ → Zd d → ℝ
  | 0 => f
  | j + 1 => fun m => kconv w (decimRecord w q f j) ((q : ℤ) • m)

/-! ## The implicit-Euler maximum principle (`def:implicit-euler-principle`) -/

/-- **The implicit-Euler maximum principle** (`def:implicit-euler-principle`), for a (symmetric
probability) measure `μ` on `ℝ^d`: for every real Schwartz `f`, the output `u = μ * f` has
`u(x) ≤ f(x)` at every local maximum `x` of `u` and `u(x) ≥ f(x)` at every local minimum. -/
def HasImplicitEulerPrinciple (μ : Measure (Rd d)) : Prop :=
  ∀ (f : 𝓢(Rd d, ℝ)) (x : Rd d),
    (IsLocalMax (mconvE μ f) x → mconvE μ f x ≤ f x) ∧
      (IsLocalMin (mconvE μ f) x → f x ≤ mconvE μ f x)

/-- **`x` is an `𝒩`-maximum of `u`** (`def:implicit-euler-principle`): `u(x) ≥ u(x + y)` for every
`y ∈ 𝒩`. -/
def IsNMax (N : Set (Zd d)) (u : Zd d → ℝ) (x : Zd d) : Prop := ∀ y ∈ N, u (x + y) ≤ u x

/-- **`x` is an `𝒩`-minimum of `u`**: an `𝒩`-maximum of `-u`. -/
def IsNMin (N : Set (Zd d)) (u : Zd d → ℝ) (x : Zd d) : Prop := IsNMax N (fun n => -u n) x

/-- **The principle on `𝒩`** (`def:implicit-euler-principle`), for a kernel `κ` on `hℤ^d` indexed
by `ℤ^d`: for every bounded real `f`, the output `u = κ * f` has `u(x) ≤ f(x)` at every
`𝒩`-maximum and `u(x) ≥ f(x)` at every `𝒩`-minimum. The node reads it for a symmetric
probability `κ`; read for a real kernel of mass one it is the signed principle of
`def:neighbourhood-principle`. -/
def HasGridImplicitEulerPrinciple (N : Set (Zd d)) (κ : Zd d → ℝ) : Prop :=
  ∀ f : Zd d → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) → ∀ x : Zd d,
    (IsNMax N (kconv κ f) x → kconv κ f x ≤ f x) ∧ (IsNMin N (kconv κ f) x → f x ≤ kconv κ f x)

/-- **The `2d` axis neighbours** `{±e_j}` of `ℤ^d`. -/
def axisNbrs (d : ℕ) : Set (Zd d) := {n | ∃ i : Fin d, n = zbasis i ∨ n = -zbasis i}

end Pyramids
