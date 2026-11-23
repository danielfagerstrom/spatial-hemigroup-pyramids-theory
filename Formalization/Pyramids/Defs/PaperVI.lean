/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Defs.SmallerGroups
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import ScaleSpaceCore.LaplaceLaw

/-!
# The notation of chapters 6–7, moving to Paper VI: implementation and the jet

Blueprint: `blueprint/src/parts/06-helmholtz.tex`, `07-computation.tex` and `08-jet.tex`
(Q-0281, dispatch 5). These objects are introduced inside the statements of the nine nodes that
move to Paper VI; they are named here so that the
nodes that read them share one type. Every definition is vocabulary: nothing in this file claims
anything, and every identity a node displays about them (a transform, a factorization, that a series
sums to a probability) is a skeleton statement of that node.

## Readings fixed here

* **The transform on the line** is the blueprint's `f̂(ω) = ∫ e^{iωx} f(x) dx` (`fourierLine`), on
  functions; on measures it is Mathlib's `charFun`, which has the same convention.
* **Kernels on the grid `ℤ^d`** are functions `Zd d = (Fin d → ℤ) → ℝ`. "A probability measure on
  `ℤ^d`" is a kernel that is nonnegative, summable and of sum `1` (`IsProbKernel`): on a countable
  set a measure is its point masses. Convolution is `kconv`, the power `kpow`, the transform the
  Fourier series `∑ₙ λ(n) e^{i⟨n,ϑ⟩}` (`gridFourier`). Operators on the grid (`Δ_h`, the shift `S`)
  are maps of all sequences; "on `ℓ¹(ℤ)`" is the summable ones.
* **The `L²` transform with the blueprint's convention.** Mathlib's `𝓕` on `L²(ℝ^d)` is the
  extension of `∫ e^{-2πi⟨x,ξ⟩} f(x) dx`, so the blueprint's `f̂(ω)` is `𝓕 f (-ω/2π)`; an operator
  with multiplier `m` in the blueprint's convention (`v̂ = m f̂`) is
  `𝓕 v (ξ) = m(-2πξ) 𝓕 f (ξ)` a.e. (`IsL2Multiplier`), stated relationally so that no `L²`
  element is constructed here. `L²(ℝ^d)` is the complex space; the nodes' identities are linear, so
  the real ones are their restrictions.
* **Weak derivatives** are against complex test functions, smooth with compact support:
  `IsWeakPartial k u v` is `∫ u ∂ₖφ = -∫ v φ`, `IsWeakPartial2 i j u v` is `∫ u ∂ᵢ∂ⱼφ = ∫ v φ`;
  **`H²(ℝ^d)`** is the classical Sobolev space, `u ∈ L²` with every weak derivative of order at most
  `2` in `L²` (`IsH2`), which for `p = 2` and integer order is Mathlib's Bessel-potential space.
* **A finite complex Borel measure** `κ` is written `κ₀ - κ₁ + i(κ₂ - κ₃)` with four finite
  measures (the Jordan decompositions of its real and imaginary parts; Mathlib has no convolution of
  complex measures), and `κ * f` is `cmConv`.
* **The jet** of a `C²` function `u` on `ℝ^d` is its gradient `∇u` (Mathlib's `gradient`) and its
  Hessian matrix `hessMat u x`, the second derivative read in the standard basis.
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set Complex
open ScaleSpace (convPow laplaceDensity)
open scoped ENNReal RealInnerProductSpace FourierTransform

variable {d : ℕ}

/-! ## The line (`prop:recursion-helmholtz`(1)) -/

/-! **`ℓ_t(x) := (2t)⁻¹ e^{-|x|/t}`**, the Laplace density, is the shared library's
`ScaleSpace.laplaceDensity` (`ScaleSpaceCore.LaplaceLaw`, v0.4.0, Q-0364), opened above. It is
written `(2 * t)⁻¹ * Real.exp (-(|x| / t))` there and was `(2 * t)⁻¹ * Real.exp (-|x| / t)` here:
the same function (`neg_div`). -/

/-- **`e⁺_t(x) := t⁻¹ e^{-x/t} 1_{x > 0}`**, the one-sided exponential density. -/
noncomputable def expPlus (t x : ℝ) : ℝ := if 0 < x then t⁻¹ * Real.exp (-x / t) else 0

/-- **`e⁻_t(x) := e⁺_t(-x)`**. -/
noncomputable def expMinus (t x : ℝ) : ℝ := expPlus t (-x)

/-- **`f̂(ω) := ∫ e^{iωx} f(x) dx`** on the line (the blueprint's convention). -/
noncomputable def fourierLine (f : ℝ → ℝ) (ω : ℝ) : ℂ :=
  ∫ x, exp (((ω * x : ℝ) : ℂ) * I) * (f x : ℂ)

/-- **`(f * g)(x) := ∫ f(y) g(x - y) dy`** on the line. -/
noncomputable def lineConv (f g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, f y * g (x - y)

/-- **The mixture `(s²/t²) δ₀ + (1 - s²/t²) ℓ_t(x) dx`** (`prop:recursion-helmholtz`(1)), a
probability measure for `0 ≤ s ≤ t`, `t > 0`. -/
noncomputable def maternLineMix (s t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (s ^ 2 / t ^ 2) • Measure.dirac 0 +
    ENNReal.ofReal (1 - s ^ 2 / t ^ 2) •
      (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (laplaceDensity t x)

/-- **The Matérn increment of index `γ` from `s` to `t` on the line**
(`prop:recursion-helmholtz`(1), `prop:separable-frame`(1)): the `γ`-fold convolution power of
`maternLineMix s t`, which at `s = 0` is `ℓ_t^{*γ}`, and `δ₀` at `s = t`. -/
noncomputable def maternLineInc (γ : ℕ) (s t : ℝ) : Measure ℝ :=
  if s = t then Measure.dirac 0 else convPow (maternLineMix s t) γ

/-! ## The grid `hℤ` (`prop:recursion-helmholtz`(2)) -/

/-- **`λ_t(n) := (1-a)/(1+a) a^{|n|}`, `a := e^{-h/t}`**, the Laplace kernel sampled on `hℤ` and
renormalized to unit mass. -/
noncomputable def sampledLaplace (h t : ℝ) (n : ℤ) : ℝ :=
  (1 - Real.exp (-h / t)) / (1 + Real.exp (-h / t)) * Real.exp (-h / t) ^ n.natAbs

/-- **The Fourier series** `λ̂(ϑ) := ∑ₙ λ(n) e^{inϑ}` of a kernel on `ℤ`. -/
noncomputable def lineFourierSeries (lam : ℤ → ℝ) (θ : ℝ) : ℂ :=
  ∑' n : ℤ, (lam n : ℂ) * exp (((n * θ : ℝ) : ℂ) * I)

/-- **`D_h(ϑ) := h⁻²(2 - 2 cos ϑ)`**, the symbol of `-Δ_h` on `hℤ`. -/
noncomputable def lineGridSymbol (h θ : ℝ) : ℝ := (h ^ 2)⁻¹ * (2 - 2 * Real.cos θ)

/-- **`Δ_h u(n) := h⁻²(u(n+1) - 2u(n) + u(n-1))`**, the three-point Laplacian on `hℤ`. -/
noncomputable def lineGridLap (h : ℝ) (u : ℤ → ℝ) (n : ℤ) : ℝ :=
  (h ^ 2)⁻¹ * (u (n + 1) - 2 * u n + u (n - 1))

/-- **The renormalized range** `t_h := h/(2 sinh(h/2t))`. -/
noncomputable def helmRange (h t : ℝ) : ℝ := h / (2 * Real.sinh (h / (2 * t)))

/-- **The shift** `(Su)(n) := u(n-1)` on sequences. -/
def shiftZ (u : ℤ → ℝ) (n : ℤ) : ℝ := u (n - 1)

/-- **The inverse shift** `(S⁻¹u)(n) := u(n+1)`. -/
def shiftZInv (u : ℤ → ℝ) (n : ℤ) : ℝ := u (n + 1)

/-! ## The grid `hℤ^d` (`prop:discrete-helmholtz`, `prop:helmholtz-subsampling`) -/

/-- **`ℤ^d`**, the index set of the grid. -/
abbrev Zd (d : ℕ) := Fin d → ℤ

/-- **The unit vector** `e_i` of `ℤ^d`. -/
def zbasis (i : Fin d) : Zd d := Pi.single i 1

/-- **`δ₀`** on `ℤ^d`, as a kernel. -/
def deltaZ (n : Zd d) : ℝ := if n = 0 then 1 else 0

/-- **A probability measure on `ℤ^d`**, as a kernel: nonnegative, summable, of sum `1`. -/
def IsProbKernel (lam : Zd d → ℝ) : Prop :=
  (∀ n, 0 ≤ lam n) ∧ Summable lam ∧ ∑' n, lam n = 1

/-- **Convolution of kernels** on `ℤ^d`, `(λ * μ)(n) := ∑ₘ λ(m) μ(n - m)`. -/
noncomputable def kconv (lam mu : Zd d → ℝ) (n : Zd d) : ℝ := ∑' m, lam m * mu (n - m)

/-- **The convolution power** `λ^{*k}`, with `λ^{*0} = δ₀`. -/
noncomputable def kpow (lam : Zd d → ℝ) : ℕ → Zd d → ℝ
  | 0 => deltaZ
  | k + 1 => kconv (kpow lam k) lam

/-- **The Fourier series** `λ̂(ϑ) := ∑ₙ λ(n) e^{i⟨n,ϑ⟩}` of a kernel on `ℤ^d`. -/
noncomputable def gridFourier (lam : Zd d → ℝ) (θ : Fin d → ℝ) : ℂ :=
  ∑' n : Zd d, (lam n : ℂ) * exp (((∑ i, (n i : ℝ) * θ i : ℝ) : ℂ) * I)

/-- **`D_h(ϑ) := h⁻² ∑ᵢ (2 - 2 cos ϑᵢ)`**, the symbol of `-Δ_h` on `hℤ^d`. -/
noncomputable def gridSymbol (h : ℝ) (θ : Fin d → ℝ) : ℝ :=
  (h ^ 2)⁻¹ * ∑ i, (2 - 2 * Real.cos (θ i))

/-- **The `(2d+1)`-point Laplacian** `Δ_h u(n) := h⁻² ∑ᵢ (u(n+eᵢ) - 2u(n) + u(n-eᵢ))` on `hℤ^d`. -/
noncomputable def gridLap (h : ℝ) (u : Zd d → ℝ) (n : Zd d) : ℝ :=
  (h ^ 2)⁻¹ * ∑ i, (u (n + zbasis i) - 2 * u n + u (n - zbasis i))

/-- **The simple random walk step** `σ`: mass `1/2d` at each `±eᵢ`. -/
noncomputable def rwStep (n : Zd d) : ℝ :=
  ∑ i, ((if n = zbasis i then (1 : ℝ) else 0) + (if n = -zbasis i then 1 else 0)) / (2 * d)

/-- **`κ_t := (1-p) ∑_{k ≥ 0} p^k σ^{*k}`**, `c := t²/h²`, `p := 2dc/(1+2dc)`
(`prop:discrete-helmholtz`). -/
noncomputable def discreteHelmholtz (d : ℕ) (h t : ℝ) (n : Zd d) : ℝ :=
  let c := t ^ 2 / h ^ 2
  let p := 2 * d * c / (1 + 2 * d * c)
  (1 - p) * ∑' k : ℕ, p ^ k * kpow (rwStep (d := d)) k n

/-- **The discrete Helmholtz family** `λ^{(h,γ)}_t := κ_t^{*γ}` on `hℤ^d`
(`prop:discrete-helmholtz`(2), `prop:helmholtz-subsampling`). -/
noncomputable def helmKernel (d : ℕ) (h t : ℝ) (γ : ℕ) : Zd d → ℝ :=
  kpow (discreteHelmholtz d h t) γ

/-- **The increment** `λ_{s,t}`: the `γ`-fold power of `(s²/t²) δ₀ + (1 - s²/t²) κ_t`
(`prop:discrete-helmholtz`(2)). -/
noncomputable def helmIncrement (d : ℕ) (h : ℝ) (γ : ℕ) (s t : ℝ) : Zd d → ℝ :=
  kpow (fun n => s ^ 2 / t ^ 2 * deltaZ n + (1 - s ^ 2 / t ^ 2) * discreteHelmholtz d h t n) γ

/-- **The member of index `γ` and range `t` of the family on `hℤ`**, a kernel on `ℤ`
(`prop:helmholtz-subsampling`(1), (4)). -/
noncomputable def lineHelmKernel (h t : ℝ) (γ : ℕ) (n : ℤ) : ℝ := helmKernel 1 h t γ fun _ => n

/-- **The subsample of `λ^{(h,γ)}_t` by `q` is exact** (`prop:helmholtz-subsampling`): the kernel
`m ↦ λ^{(h,γ)}_t(qm)` equals `C λ^{(qh,γ')}_{t'}` for some `C > 0`, `t' > 0` and integer
`γ' ≥ 1`. -/
def IsExactSubsample (d : ℕ) (h : ℝ) (q : ℕ) (t : ℝ) (γ : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ t' : ℝ, 0 < t' ∧ ∃ γ' : ℕ, 1 ≤ γ' ∧
    ∀ m : Zd d, helmKernel d h t γ ((q : ℤ) • m) = C * helmKernel d (q * h) t' γ' m

/-! ## Frames (`prop:separable-frame`) -/

/-- **`D_A f := |det A|⁻¹ f(A⁻¹ ·)`** on functions on `ℝ^d`. -/
noncomputable def dilFun (A : Mat d) (f : Rd d → ℝ) (x : Rd d) : ℝ :=
  |A.det|⁻¹ * f (lin A⁻¹ x)

/-- **The convolution along the `i`-th axis** with a law `ν` on `ℝ`,
`g ↦ ∫ g(x - y eᵢ) ν(dy)`. -/
noncomputable def axisConv (i : Fin d) (ν : Measure ℝ) (g : Rd d → ℝ) (x : Rd d) : ℝ :=
  ∫ y, g (x - y • ebasis i) ∂ν

/-- **The composition of the `d` axis convolutions**, the `i`-th with `νᵢ` along the `i`-th axis. -/
noncomputable def axisConvAll (ν : Fin d → Measure ℝ) (g : Rd d → ℝ) : Rd d → ℝ :=
  (List.finRange d).foldr (fun i f => axisConv i (ν i) f) g

/-! ## The jet (`lem:affine-jet`) -/

/-- **The Hessian matrix** `∇²u(x)`, the second derivative read in the standard basis. -/
noncomputable def hessMat (u : Rd d → ℝ) (x : Rd d) : Mat d :=
  Matrix.of fun i j => iteratedFDeriv ℝ 2 u x ![ebasis i, ebasis j]

/-- **The centred Gaussian density of covariance `Σ ∈ PD(d)`**,
`g_Σ(z) = (2π)^{-d/2} (det Σ)^{-1/2} exp(-½⟨z, Σ⁻¹z⟩)`. -/
noncomputable def gaussDensityCov (S : Mat d) (z : Rd d) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2) * Real.exp (-(quad S⁻¹ z) / 2)

/-- **`(g * f)(x) := ∫ g(x - y) f(y) dy`** on `ℝ^d`. -/
noncomputable def fconv (g f : Rd d → ℝ) (x : Rd d) : ℝ := ∫ y, g (x - y) * f y

/-- **`(G * f)(x) := ∫ G(x - y) f(y) dy`** for a real kernel `G` and a complex `f`
(`prop:matern-hessian`'s `u := G_t * f`). -/
noncomputable def gconvC (G : Rd d → ℝ) (f : Rd d → ℂ) (x : Rd d) : ℂ :=
  ∫ y, (G (x - y) : ℂ) * f y

/-! ## `L²` multipliers and weak derivatives (`prop:matern-hessian`) -/

/-- **`L²(ℝ^d)`**, complex. -/
noncomputable abbrev L2C (d : ℕ) := Lp ℂ 2 (volume : Measure (Rd d))

/-- **`v` is the image of `f` under the multiplier `m`** in the blueprint's convention,
`v̂ = m f̂`: `𝓕 v (ξ) = m(-2πξ) 𝓕 f (ξ)` almost everywhere, with Mathlib's `L²` transform. -/
def IsL2Multiplier (m : Rd d → ℂ) (f v : L2C d) : Prop :=
  ((𝓕 v : L2C d) : Rd d → ℂ) =ᵐ[volume]
    fun ξ => m (-(2 * Real.pi) • ξ) * ((𝓕 f : L2C d) : Rd d → ℂ) ξ

/-- **The multiplier of `R_iR_j`**, `-ωᵢωⱼ/|ω|²`. -/
noncomputable def rieszSymbol (i j : Fin d) (ω : Rd d) : ℂ := ((-(ω i * ω j) / ‖ω‖ ^ 2 : ℝ) : ℂ)

/-- **A test function**: complex-valued, smooth, with compact support. -/
def IsTestFn (φ : Rd d → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

/-- **`v` is the weak derivative `∂ₖu`**: `∫ u ∂ₖφ = -∫ v φ` for every test function `φ`. -/
def IsWeakPartial (k : Fin d) (u v : Rd d → ℂ) : Prop :=
  ∀ φ : Rd d → ℂ, IsTestFn φ →
    ∫ x, u x * fderiv ℝ φ x (ebasis k) = -∫ x, v x * φ x

/-- **`v` is the weak derivative `∂ᵢ∂ⱼu`**: `∫ u ∂ᵢ∂ⱼφ = ∫ v φ` for every test function `φ`. -/
def IsWeakPartial2 (i j : Fin d) (u v : Rd d → ℂ) : Prop :=
  ∀ φ : Rd d → ℂ, IsTestFn φ →
    ∫ x, u x * iteratedFDeriv ℝ 2 φ x ![ebasis i, ebasis j] = ∫ x, v x * φ x

/-- **`u ∈ H²(ℝ^d)`**: `u ∈ L²` with every weak derivative of order at most `2` in `L²`. -/
def IsH2 (u : Rd d → ℂ) : Prop :=
  MemLp u 2 volume ∧ (∀ k, ∃ v, MemLp v 2 volume ∧ IsWeakPartial k u v) ∧
    ∀ i j, ∃ v, MemLp v 2 volume ∧ IsWeakPartial2 i j u v

/-- **`κ * f` for the finite complex measure `κ := κ₀ - κ₁ + i(κ₂ - κ₃)`**,
`(κ * f)(x) := ∫ f(x - y) κ(dy)`. -/
noncomputable def cmConv (κ : Fin 4 → Measure (Rd d)) (f : Rd d → ℂ) (x : Rd d) : ℂ :=
  (∫ y, f (x - y) ∂κ 0) - (∫ y, f (x - y) ∂κ 1) +
    I * ((∫ y, f (x - y) ∂κ 2) - ∫ y, f (x - y) ∂κ 3)

end Pyramids
