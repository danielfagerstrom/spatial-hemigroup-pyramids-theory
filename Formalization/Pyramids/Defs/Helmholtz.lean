/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Matern

/-!
# The vocabulary of chapter 5's stencils (§§ 5.4–5.6)

Blueprint: `blueprint/src/parts/06-helmholtz.tex`. Definitions only: nothing in this file claims
anything, and every identity the part's nodes state about these objects is a skeleton statement
(`PyramidsSkeleton.Ch05Helmholtz`). The file was opened by the typing of `05-price.tex`, whose
nodes read the nine-point Laplacian, step and resolvent; the typing of `06-helmholtz.tex`
continues it.

## What is already defined, and is not repeated here

* The grid `ℤ^d` and its kernels (`Zd`, `IsProbKernel`, `kconv`, `kpow`, `deltaZ`, `zbasis`,
  `gridFourier`), the `(2d+1)`-point Laplacian `Δ_h` (`gridLap`), its symbol (`gridSymbol`), the
  simple random walk step (`rwStep`), the five-point resolvent `κ_t` (`discreteHelmholtz`) and its
  family and increments (`helmKernel`, `helmIncrement`) are `Defs/PaperVI.lean`'s.
* `𝒩`-maxima and `𝒩`-minima (`IsNMax`, `IsNMin`), the principle on `𝒩`
  (`HasGridImplicitEulerPrinciple`) and the `2d` axis neighbours `{±e_j}` (`axisNbrs`) are
  `Defs/Matern.lean`'s.

## What is defined here

* `def:nine-point-laplacian`: `g` (`gcos`), `D_5` (`fivePointSymbol`), `Δ_9` (`ninePointLap`),
  `D_9` (`ninePointSymbol`) and `Φ_9` (`ninePointPhase`);
* `def:nine-point-stencil`: the box `{-1,0,1}²` (`nineBox`), a nine-point stencil
  (`nineStencilOp`), its symbol (`nineStencilSymbol`), consistency (`IsConsistentStencil`) and
  invariance under the signed permutations (`IsSignedPermInvariantStencil`);
* `def:neighbourhood-principle`: the domain of the signed principle, real symmetric summable
  kernels of mass one (`IsSignedKernel`), and the eight neighbours `𝒩_8` (`nbrs8`, with the four
  diagonal ones `diagNbrs`); `𝒩_4` is `axisNbrs 2`, and the condition is chapter 4's
  `HasGridImplicitEulerPrinciple`;
* the objects the statements introduce: the nine-point step, `p`, resolvent, family and
  increments (`ninePointStep`, `ninePointP`, `ninePointHelmholtz`, `ninePointFamily`,
  `ninePointIncrement`), `P_6` (`sexticP6`), `D_×` and `D_β` (`crossSymbol`, `betaSymbol`), the
  witness of `prop:grid-implicit-euler-principle-nine-axis` (`nineAxisWitness`), and the full
  Mehrstellen scheme: `B` (`mehrstellenB`, its kernel `mehrstellenBKernel`), the kernel of
  `B - t²Δ_9` (`mehrstellenMatrix`), `α_0` and `P` (`mehrstellenAlpha0`, `mehrstellenP`), the
  Neumann series of the inverse (`mehrstellenInverse`), `κ^M_t` (`mehrstellenKernelNu`,
  `mehrstellenKernel`), `D^*` and `Φ^*` (`mehrstellenSymbol`, `mehrstellenPhase`), the Fourier
  coefficients `c_n` (`mehrstellenCoeff`), and the family `Λ^M` (`mehrstellenFamily`,
  `mehrstellenIncrement`).

## Readings fixed here

* **Kernels and operators on `hℤ²` are indexed by `ℤ²`**, as in `Defs/PaperVI.lean`; `h` enters
  only through the factor `h⁻²` of an operator and the parameter `ν_h = t²/h²`. `e₁, e₂` are
  `zbasis 0`, `zbasis 1`; a frequency `ω ∈ ℝ²` is a function `Fin 2 → ℝ`, as the phase of
  `gridFourier` is, and `|ω|² = ω₁² + ω₂²`.
* **`D_9` and `Φ_9` by their formulas.** `def:nine-point-laplacian` defines `h²D_9` by the cosine
  formula and `Φ_9(θ) := h²D_9(θ/h)`; here both are the formulas, `ninePointSymbol` with the factor
  `h⁻²`. The two sentences of the node that are claims, "its symbol is `-D_9`" and "`Φ_9` does not
  depend on `h`", are not typed (a definition carries no lemma about itself).
* **The symbol of a nine-point stencil is the eigenvalue it names**: `L` maps
  `n ↦ e^{ih⟨n,ω⟩}` to `h⁻² ∑_m c_m e^{ih⟨m,ω⟩}` times itself, so `D_L(ω)` is
  `-h⁻² ∑_m c_m e^{ih⟨m,ω⟩}`, a complex number (real when the weights are symmetric). Weights
  "that do not depend on `h`" are one function `c : ℤ² → ℝ` for every `h`; only its values on the
  box are read. Consistency, "`D_L(ω) = |ω|² + O(h²)` as `h → 0` at every fixed `ω`", is
  `IsBigO` along `h → 0⁺` (`𝓝[>] 0`), `h > 0` being a mesh. A signed permutation is, as the node
  says, an additive bijection of `ℤ²` that maps `{±e₁, ±e₂}` onto itself.
* **The signed principle is the condition alone**, as chapter 4 reads the principle: the condition
  of `def:neighbourhood-principle` is `HasGridImplicitEulerPrinciple`, which is defined for any
  real kernel; the domain the node names (real, symmetric, summable, mass one) is `IsSignedKernel`,
  carried by the statements that need it. For a symmetric probability the two principles are the
  one predicate, as the node says.
* **The full Mehrstellen kernel** `κ^M_t := (B - t²Δ_9)⁻¹B` is `mehrstellenInverse ν * B`, the
  inverse being the Neumann series `α_0⁻¹ ∑ P^{*k}` of `lem:mehrstellen-splitting`. It is
  parametrized by `ν = ν_h = t²/h²` (`mehrstellenKernelNu`), and `mehrstellenKernel h t` reads it
  at `ν_h`. That the series is the (unique) summable inverse of the kernel of `B - t²Δ_9`, and
  that `B` and `B - t²Δ_9` are the convolutions with `mehrstellenBKernel` and
  `mehrstellenMatrix`, are statements (`lem:mehrstellen-splitting`,
  `prop:full-mehrstellen`(1)), so the definition is the node's object once they hold.
* **The Fourier coefficients** `c_n` of `Φ^*` are `(2π)⁻² ∫_{[-π,π]²} Φ^*(θ) e^{-i⟨n,θ⟩} dθ`,
  complex numbers; `Φ^*` is defined on all of `ℝ²` (its denominator is at least `1/3`).
-/

namespace Pyramids

open MeasureTheory Set Asymptotics
open scoped Topology

/-! ## The five-point and nine-point symbols (`def:nine-point-laplacian`) -/

/-- **`g(x) := 2 - 2 cos x`** (the notation of § 5.4). -/
noncomputable def gcos (x : ℝ) : ℝ := 2 - 2 * Real.cos x

/-- **The five-point symbol** `D_5(ω) := D_h(hω) = h⁻²(g(x) + g(y))`, `x = hω₁`, `y = hω₂`
(`def:nine-point-laplacian`): the symbol `gridSymbol` of `prop:discrete-helmholtz` at `d = 2`, read
at the phase `hω`. -/
noncomputable def fivePointSymbol (h : ℝ) (ω : Fin 2 → ℝ) : ℝ := gridSymbol h (h • ω)

/-- **The nine-point Laplacian on `hℤ²`** (`def:nine-point-laplacian`):
`Δ_9 u(n) := (6h²)⁻¹ (4 ∑_{±eᵢ} u(n ± eᵢ) + ∑_{±e₁±e₂} u(n ± e₁ ± e₂) - 20 u(n))`. -/
noncomputable def ninePointLap (h : ℝ) (u : Zd 2 → ℝ) (n : Zd 2) : ℝ :=
  (6 * h ^ 2)⁻¹ *
    (4 * ∑ i : Fin 2, (u (n + zbasis i) + u (n - zbasis i)) +
      (u (n + zbasis 0 + zbasis 1) + u (n + zbasis 0 - zbasis 1) +
        u (n - zbasis 0 + zbasis 1) + u (n - zbasis 0 - zbasis 1)) - 20 * u n)

/-- **The nine-point symbol** `D_9` (`def:nine-point-laplacian`):
`h²D_9(ω) := 10/3 - 4/3 (cos x + cos y) - 2/3 cos x cos y`, `x = hω₁`, `y = hω₂`. -/
noncomputable def ninePointSymbol (h : ℝ) (ω : Fin 2 → ℝ) : ℝ :=
  (h ^ 2)⁻¹ * (10 / 3 - 4 / 3 * (Real.cos (h * ω 0) + Real.cos (h * ω 1)) -
    2 / 3 * (Real.cos (h * ω 0) * Real.cos (h * ω 1)))

/-- **`Φ_9(θ) := h²D_9(θ/h)`**, the nine-point symbol as a function of the phase
(`def:nine-point-laplacian`): `10/3 - 4/3 (cos θ₁ + cos θ₂) - 2/3 cos θ₁ cos θ₂`. -/
noncomputable def ninePointPhase (θ : Fin 2 → ℝ) : ℝ :=
  10 / 3 - 4 / 3 * (Real.cos (θ 0) + Real.cos (θ 1)) - 2 / 3 * (Real.cos (θ 0) * Real.cos (θ 1))

/-! ## The nine-point family (`prop:nine-point-family`) -/

/-- **The nine-point step `σ_9`** (`prop:nine-point-family`): mass `1/5` at each `±eᵢ` and
`1/20` at each `±e₁ ± e₂`. -/
noncomputable def ninePointStep (n : Zd 2) : ℝ :=
  ∑ i : Fin 2, ((if n = zbasis i then (1 : ℝ) / 5 else 0) + (if n = -zbasis i then 1 / 5 else 0)) +
    ((if n = zbasis 0 + zbasis 1 then (1 : ℝ) / 20 else 0) +
      (if n = zbasis 0 - zbasis 1 then 1 / 20 else 0) +
      (if n = -zbasis 0 + zbasis 1 then 1 / 20 else 0) +
      (if n = -zbasis 0 - zbasis 1 then 1 / 20 else 0))

/-- **The nine-point resolvent `κ^9_t := (1-p) ∑_{k ≥ 0} p^k σ_9^{*k}`**, `ν_h := t²/h²`,
`p := (10/3)ν_h/(1 + (10/3)ν_h)` (`prop:nine-point-family`). -/
noncomputable def ninePointHelmholtz (h t : ℝ) (n : Zd 2) : ℝ :=
  let c := t ^ 2 / h ^ 2
  let p := 10 / 3 * c / (1 + 10 / 3 * c)
  (1 - p) * ∑' k : ℕ, p ^ k * kpow ninePointStep k n

/-- **`p := (10/3)ν_h/(1 + (10/3)ν_h)`**, `ν_h := t²/h²` (`prop:nine-point-family`), the `p` of
`ninePointHelmholtz`. -/
noncomputable def ninePointP (h t : ℝ) : ℝ :=
  10 / 3 * (t ^ 2 / h ^ 2) / (1 + 10 / 3 * (t ^ 2 / h ^ 2))

/-- **The nine-point family** `Λ^9_t := (κ^9_t)^{*γ}` (`prop:nine-point-family`(2)). -/
noncomputable def ninePointFamily (h t : ℝ) (γ : ℕ) : Zd 2 → ℝ := kpow (ninePointHelmholtz h t) γ

/-- **The increment** `Λ^9_{s,t}`: the `γ`-fold power of `(s²/t²) δ₀ + (1 - s²/t²) κ^9_t`
(`prop:nine-point-family`(2)). -/
noncomputable def ninePointIncrement (h : ℝ) (γ : ℕ) (s t : ℝ) : Zd 2 → ℝ :=
  kpow (fun n => s ^ 2 / t ^ 2 * deltaZ n + (1 - s ^ 2 / t ^ 2) * ninePointHelmholtz h t n) γ

/-! ## Rotation covariance (`prop:nine-point-family-rotation`, `prop:nine-point-family-unique`) -/

/-- **`P_6(ω) := ω₁⁶ + 5ω₁⁴ω₂² + 5ω₁²ω₂⁴ + ω₂⁶`** (`prop:nine-point-family-rotation`). -/
def sexticP6 (ω : Fin 2 → ℝ) : ℝ :=
  ω 0 ^ 6 + 5 * ω 0 ^ 4 * ω 1 ^ 2 + 5 * ω 0 ^ 2 * ω 1 ^ 4 + ω 1 ^ 6

/-- **`D_×`**, `h²D_×(ω) := 2 - 2 cos x cos y`, `x = hω₁`, `y = hω₂`
(`prop:nine-point-family-unique`). -/
noncomputable def crossSymbol (h : ℝ) (ω : Fin 2 → ℝ) : ℝ :=
  (h ^ 2)⁻¹ * (2 - 2 * (Real.cos (h * ω 0) * Real.cos (h * ω 1)))

/-- **`D_β := (1-β)D_5 + βD_×`** (`prop:nine-point-family-unique`). -/
noncomputable def betaSymbol (β h : ℝ) (ω : Fin 2 → ℝ) : ℝ :=
  (1 - β) * fivePointSymbol h ω + β * crossSymbol h ω

/-! ## Nine-point stencils (`def:nine-point-stencil`) -/

/-- **The `3 × 3` neighbourhood `{-1, 0, 1}²`** of the origin of `ℤ²`. -/
def nineBox : Finset (Zd 2) := Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ)

/-- **A nine-point stencil** on `hℤ²` with the real weights `c` (`def:nine-point-stencil`):
`Lu(n) := h⁻² ∑_{m ∈ {-1,0,1}²} c_m u(n + m)`. -/
noncomputable def nineStencilOp (h : ℝ) (c : Zd 2 → ℝ) (u : Zd 2 → ℝ) (n : Zd 2) : ℝ :=
  (h ^ 2)⁻¹ * ∑ m ∈ nineBox, c m * u (n + m)

/-- **The symbol `D_L` of a nine-point stencil** (`def:nine-point-stencil`): `L` maps
`n ↦ e^{ih⟨n,ω⟩}` to `-D_L(ω)` times itself, so `D_L(ω) = -h⁻² ∑_m c_m e^{ih⟨m,ω⟩}`. -/
noncomputable def nineStencilSymbol (h : ℝ) (c : Zd 2 → ℝ) (ω : Fin 2 → ℝ) : ℂ :=
  -((((h ^ 2)⁻¹ : ℝ) : ℂ) * ∑ m ∈ nineBox,
    (c m : ℂ) * Complex.exp (((h * ∑ i, (m i : ℝ) * ω i : ℝ) : ℂ) * Complex.I))

/-- **The stencil is consistent with `Δ`** (`def:nine-point-stencil`):
`D_L(ω) = |ω|² + O(h²)` as `h → 0`, at every fixed `ω`. -/
def IsConsistentStencil (c : Zd 2 → ℝ) : Prop :=
  ∀ ω : Fin 2 → ℝ,
    (fun h : ℝ => nineStencilSymbol h c ω - ((ω 0 ^ 2 + ω 1 ^ 2 : ℝ) : ℂ)) =O[𝓝[>] 0]
      fun h : ℝ => h ^ 2

/-- **The stencil is invariant under the signed permutations** (`def:nine-point-stencil`):
`c_{𝔰m} = c_m` for every `m ∈ {-1,0,1}²` and every additive bijection `𝔰` of `ℤ²` that permutes
`{±e₁, ±e₂}`. -/
def IsSignedPermInvariantStencil (c : Zd 2 → ℝ) : Prop :=
  ∀ s : Zd 2 ≃+ Zd 2, s '' axisNbrs 2 = axisNbrs 2 → ∀ m ∈ nineBox, c (s m) = c m

/-! ## The signed principle (`def:neighbourhood-principle`) -/

variable {d : ℕ}

/-- **A real symmetric summable kernel of mass one** on `ℤ^d` (`def:neighbourhood-principle`), not
necessarily positive: the kernels the signed principle is defined for. -/
def IsSignedKernel (κ : Zd d → ℝ) : Prop :=
  (∀ n, κ (-n) = κ n) ∧ Summable κ ∧ ∑' n, κ n = 1

/-- **The four diagonal neighbours** `{±e₁ ± e₂}` of `ℤ²`. -/
def diagNbrs : Set (Zd 2) :=
  {zbasis 0 + zbasis 1, zbasis 0 - zbasis 1, -zbasis 0 + zbasis 1, -zbasis 0 - zbasis 1}

/-- **`𝒩_8 := 𝒩_4 ∪ {±e₁ ± e₂}`**, the eight neighbours (`def:neighbourhood-principle`);
`𝒩_4 = {±e₁, ±e₂}` is `axisNbrs 2`. -/
def nbrs8 : Set (Zd 2) := axisNbrs 2 ∪ diagNbrs

/-- **The witness of `prop:grid-implicit-euler-principle-nine-axis`**: `u(±eᵢ) = -ε`,
`u(±e₁ ± e₂) = 1`, `u = 0` elsewhere (in particular `u(0) = 0`). -/
noncomputable def nineAxisWitness (ε : ℝ) (n : Zd 2) : ℝ :=
  -ε * (axisNbrs 2).indicator (fun _ => (1 : ℝ)) n + diagNbrs.indicator (fun _ => (1 : ℝ)) n

/-! ## The full Mehrstellen scheme (`lem:mehrstellen-splitting`, `prop:full-mehrstellen`) -/

/-- **The indicator of the axis neighbours** `{±e₁, ±e₂}`. -/
noncomputable def axisInd (n : Zd 2) : ℝ := (axisNbrs 2).indicator (fun _ => (1 : ℝ)) n

/-- **The indicator of the diagonal neighbours** `{±e₁ ± e₂}`. -/
noncomputable def diagInd (n : Zd 2) : ℝ := diagNbrs.indicator (fun _ => (1 : ℝ)) n

/-- **`B := 1 + (h²/12)Δ_h`** on `hℤ²`, as an operator (`prop:full-mehrstellen`,
`lem:mehrstellen-splitting`), `Δ_h` the five-point Laplacian. -/
noncomputable def mehrstellenB (h : ℝ) (u : Zd 2 → ℝ) (n : Zd 2) : ℝ :=
  u n + h ^ 2 / 12 * gridLap h u n

/-- **The kernel `(2/3)δ₀ + (1/12)∑_{±eᵢ} δ_{±eᵢ}`** (`prop:full-mehrstellen`), the kernel of
`B`. -/
noncomputable def mehrstellenBKernel (n : Zd 2) : ℝ := 2 / 3 * deltaZ n + 1 / 12 * axisInd n

/-- **The kernel with the weights of `prop:full-mehrstellen`(1)** at `ν = ν_h`:
`2/3 + (10/3)ν` at `0`, `1/12 - (2/3)ν` at each `±eᵢ`, `-(1/6)ν` at each `±e₁ ± e₂`. -/
noncomputable def mehrstellenMatrix (ν : ℝ) (n : Zd 2) : ℝ :=
  (2 / 3 + 10 / 3 * ν) * deltaZ n + (1 / 12 - 2 / 3 * ν) * axisInd n - 1 / 6 * ν * diagInd n

/-- **`α_0 := 2/3 + (10/3)ν_h`** (`lem:mehrstellen-splitting`). -/
noncomputable def mehrstellenAlpha0 (ν : ℝ) : ℝ := 2 / 3 + 10 / 3 * ν

/-- **The kernel `P`** of `lem:mehrstellen-splitting`: `((2/3)ν_h - 1/12)/α_0` at each `±eᵢ`,
`(1/6)ν_h/α_0` at each `±e₁ ± e₂`, `0` elsewhere. -/
noncomputable def mehrstellenP (ν : ℝ) (n : Zd 2) : ℝ :=
  (2 / 3 * ν - 1 / 12) / mehrstellenAlpha0 ν * axisInd n +
    1 / 6 * ν / mehrstellenAlpha0 ν * diagInd n

/-- **The Neumann series `α_0⁻¹ ∑_{k ≥ 0} P^{*k}`** (`lem:mehrstellen-splitting`). -/
noncomputable def mehrstellenInverse (ν : ℝ) (n : Zd 2) : ℝ :=
  (mehrstellenAlpha0 ν)⁻¹ * ∑' k : ℕ, kpow (mehrstellenP ν) k n

/-- **The full Mehrstellen kernel at `ν_h = ν`**, `(B - t²Δ_9)⁻¹B` with the inverse
`mehrstellenInverse ν` (`prop:full-mehrstellen`(1), `prop:positivity-threshold-onset`). -/
noncomputable def mehrstellenKernelNu (ν : ℝ) : Zd 2 → ℝ :=
  kconv (mehrstellenInverse ν) mehrstellenBKernel

/-- **`κ^M_t := (B - t²Δ_9)⁻¹B`** on `hℤ²` (`prop:full-mehrstellen`(1)), read at `ν_h = t²/h²`. -/
noncomputable def mehrstellenKernel (h t : ℝ) : Zd 2 → ℝ := mehrstellenKernelNu (t ^ 2 / h ^ 2)

/-- **`D^* := D_9/(1 - (h²/12)D_5)`** (`prop:full-mehrstellen`). -/
noncomputable def mehrstellenSymbol (h : ℝ) (ω : Fin 2 → ℝ) : ℝ :=
  ninePointSymbol h ω / (1 - h ^ 2 / 12 * fivePointSymbol h ω)

/-- **`Φ^*(θ) := Φ_9(θ)/(1 - (g(θ₁) + g(θ₂))/12)`**, `D^*` as a function of the phase
(`prop:full-mehrstellen`(3)). -/
noncomputable def mehrstellenPhase (θ : Fin 2 → ℝ) : ℝ :=
  ninePointPhase θ / (1 - (gcos (θ 0) + gcos (θ 1)) / 12)

/-- **The Fourier coefficient** `c_n := (2π)⁻² ∫_{[-π,π]²} Φ^*(θ) e^{-i⟨n,θ⟩} dθ`
(`prop:full-mehrstellen`(3)). -/
noncomputable def mehrstellenCoeff (n : Zd 2) : ℂ :=
  (((4 * Real.pi ^ 2)⁻¹ : ℝ) : ℂ) *
    ∫ θ in Set.univ.pi (fun _ : Fin 2 => Set.Icc (-Real.pi) Real.pi),
      (mehrstellenPhase θ : ℂ) * Complex.exp (-(((∑ i, (n i : ℝ) * θ i : ℝ) : ℂ) * Complex.I))

/-- **The Mehrstellen family** `Λ^M_t := (κ^M_t)^{*γ}` (`prop:full-mehrstellen-cascade`). -/
noncomputable def mehrstellenFamily (h t : ℝ) (γ : ℕ) : Zd 2 → ℝ := kpow (mehrstellenKernel h t) γ

/-- **The increment** `Λ^M_{s,t}`: the `γ`-fold power of `(s²/t²) δ₀ + (1 - s²/t²) κ^M_t`
(`prop:full-mehrstellen-cascade`). -/
noncomputable def mehrstellenIncrement (h : ℝ) (γ : ℕ) (s t : ℝ) : Zd 2 → ℝ :=
  kpow (fun n => s ^ 2 / t ^ 2 * deltaZ n + (1 - s ^ 2 / t ^ 2) * mehrstellenKernel h t n) γ

end Pyramids
