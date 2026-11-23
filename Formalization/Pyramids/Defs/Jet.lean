/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Helmholtz
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# The vocabulary of chapter 7's grid section (§ 7.3)

Blueprint: `blueprint/src/parts/08-jet.tex`, `prop:grid-jet`. Definitions only: nothing in this
file claims anything, and every identity the node states about these objects is a skeleton
statement (`PyramidsSkeleton.Ch07Jet`). The chapter has no definition node; these are the objects
the statement of `prop:grid-jet` introduces.

## What is already defined, and is not repeated here

* The grid `ℤ^d` and its kernels (`Zd`, `zbasis`, `deltaZ`, `kconv`, `gridFourier`), the
  `(2d+1)`-point Laplacian `Δ_h` (`gridLap`), its symbol `D_h` (`gridSymbol`) and the resolvent
  `κ_t` (`discreteHelmholtz`) are `Defs/PaperVI.lean`'s; `g(x) = 2 - 2 cos x` is `gcos`
  (`Defs/Helmholtz.lean`).
* The Matérn half of the chapter (`cor:hessian-from-level-difference`) reads only
  `Defs/PaperVI.lean`'s `L²` vocabulary (`L2C`, `gconvC`, `IsL2Multiplier`, `rieszSymbol`,
  `IsWeakPartial`, `IsWeakPartial2`, `IsH2`) and the affine export's `fourierPlus`; it needs
  nothing new.

## Readings fixed here

* **The transform on `ℓ²(ℤ^d)`.** The node's transform of a kernel is
  `ŝ(ϑ) = ∑ₙ s(n) e^{i⟨n,ϑ⟩}` (`gridFourier`), and its inverse the coefficient
  `(2π)^{-d} ∫_{[-π,π]^d} F(ϑ) e^{-i⟨n,ϑ⟩} dϑ` (`gridCoeff`). An operator "defined by its
  multiplier `m`" is read relationally (`IsGridMultiplier m w v`): there is an `F ∈ L²([-π,π]^d)`
  whose coefficients are `w` (so `F = ŵ` by Riesz–Fischer) and the coefficients of `mF` are `v`.
  No `ℓ²` element and no `L²` transform is constructed here; for a bounded `m` and `w ∈ ℓ²` the
  relation determines `v`. Sequences are complex; a real sequence enters through its coercion.
  Where the node names a bounded operator on `ℓ²(ℤ^d)` (clause (4)), its domain is Mathlib's
  complex Hilbert space `lp (fun _ => ℂ) 2` (`ell2C`).
* **`δ_i²`** (`secondDiff`) is defined over any `RCLike` field, so that it acts on the real
  sequences of clauses (1)–(2) and on complex `ℓ²` (the operator of clause (4)) alike; its kernel
  `h⁻²(δ_{e_i} - 2δ_0 + δ_{-e_i})` is `secondDiffKernel`.
* **The multiplier of `P_i`** is `D_{h,i}/D_h` (`diagHessSymbol`), with Lean's `x/0 = 0` at the
  zeros of `D_h`; the statements read it only off the origin of `[-π,π]^d`, where `D_h ≠ 0` (a
  conjunct of the statement), and the multiplier relation does not see a null set.
* **`S_i(ϑ) = 2i h⁻¹ sin(ϑ_i/2)` for `ϑ_i ∈ (-π,π]`, extended `2π`-periodically**
  (`halfSampleSymbol`): the periodic extension is `toIocMod` into `(-π, π]`. Its kernel, the
  inverse coefficients, is `halfSampleKernel`.
* **The delay `τ_a` read through band-limited interpolation** (`bandDelay`): the Whittaker–Shannon
  interpolant of the sequence along axis `i` read at `n_i - a`, that is
  `(τ_a u)(n) = ∑_{m ∈ ℤ} sinc(π(m - a)) u(n - m e_i)`, with `sinc x = sin x / x`
  (Mathlib's `Real.sinc`). At an integer `a` it is the plain delay `u(n - a e_i)`.
* **"Carried by the `i`-th axis"** (`IsAxisCarried`): every point where the kernel does not vanish
  is `m e_i` for an integer `m`.
-/

namespace Pyramids

open MeasureTheory Set Complex

variable {d : ℕ}

/-- **`ℓ²(ℤ^d)`**, complex. -/
noncomputable abbrev ell2C (d : ℕ) := lp (fun _ : Zd d => ℂ) 2

/-- **The phase cube `[-π, π]^d`.** -/
def phaseCube (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Icc (-Real.pi) Real.pi

/-- **The inverse Fourier coefficient** `(2π)^{-d} ∫_{[-π,π]^d} F(ϑ) e^{-i⟨n,ϑ⟩} dϑ` of a function
on the phase cube, at `n ∈ ℤ^d`. -/
noncomputable def gridCoeff (F : (Fin d → ℝ) → ℂ) (n : Zd d) : ℂ :=
  (((2 * Real.pi) ^ d)⁻¹ : ℝ) *
    ∫ θ in phaseCube d, F θ * exp (-(((∑ i, (n i : ℝ) * θ i : ℝ) : ℂ) * I))

/-- **`v` is the image of `w` under the multiplier `m`** on `ℓ²(ℤ^d)`: `w` is the coefficient
sequence of some `F ∈ L²([-π,π]^d)` (so `F = ŵ`), and `v` is that of `mF`. -/
def IsGridMultiplier (m : (Fin d → ℝ) → ℂ) (w v : Zd d → ℂ) : Prop :=
  ∃ F : (Fin d → ℝ) → ℂ, MemLp F 2 (volume.restrict (phaseCube d)) ∧
    (∀ n, gridCoeff F n = w n) ∧ ∀ n, gridCoeff (fun θ => m θ * F θ) n = v n

/-- **`D_{h,i}(ϑ) := h⁻² g(ϑ_i)`**, the symbol of `-δ_i²`. -/
noncomputable def axisSymbol (h : ℝ) (i : Fin d) (θ : Fin d → ℝ) : ℝ := (h ^ 2)⁻¹ * gcos (θ i)

/-- **`δ_i²u(n) := h⁻²(u(n + e_i) - 2u(n) + u(n - e_i))`**, the second difference along axis `i`. -/
noncomputable def secondDiff {𝕜 : Type*} [RCLike 𝕜] (h : ℝ) (i : Fin d) (u : Zd d → 𝕜)
    (n : Zd d) : 𝕜 :=
  ((h ^ 2)⁻¹ : ℝ) • (u (n + zbasis i) - 2 * u n + u (n - zbasis i))

/-- **The kernel of `δ_i²`**, `h⁻²(δ_{e_i} - 2δ_0 + δ_{-e_i})`. -/
noncomputable def secondDiffKernel (h : ℝ) (i : Fin d) (n : Zd d) : ℝ :=
  (h ^ 2)⁻¹ * ((if n = zbasis i then 1 else 0) - 2 * deltaZ n + (if n = -zbasis i then 1 else 0))

/-- **The multiplier `D_{h,i}/D_h` of `P_i`** (read off the zeros of `D_h`). -/
noncomputable def diagHessSymbol (h : ℝ) (i : Fin d) (θ : Fin d → ℝ) : ℝ :=
  axisSymbol h i θ / gridSymbol h θ

/-- **`S_i(ϑ) := 2i h⁻¹ sin(ϑ_i/2)` for `ϑ_i ∈ (-π, π]`, extended `2π`-periodically.** -/
noncomputable def halfSampleSymbol (h : ℝ) (i : Fin d) (θ : Fin d → ℝ) : ℂ :=
  2 * I * ((h⁻¹ * Real.sin (toIocMod Real.two_pi_pos (-Real.pi) (θ i) / 2) : ℝ) : ℂ)

/-- **The kernel of `S_i`**, the inverse Fourier coefficients of its multiplier. -/
noncomputable def halfSampleKernel (h : ℝ) (i : Fin d) : Zd d → ℂ :=
  gridCoeff (halfSampleSymbol h i)

/-- **The delay `τ_a u(n) := u(n - a e_i)` read through band-limited interpolation**:
`∑_{m ∈ ℤ} sinc(π(m - a)) u(n - m e_i)`. -/
noncomputable def bandDelay {𝕜 : Type*} [RCLike 𝕜] (i : Fin d) (a : ℝ) (u : Zd d → 𝕜)
    (n : Zd d) : 𝕜 :=
  ∑' m : ℤ, ((Real.sinc (Real.pi * (m - a)) : ℝ) : 𝕜) * u (n - m • zbasis i)

/-- **A kernel carried by the `i`-th axis**: it vanishes off `{m e_i : m ∈ ℤ}`. -/
def IsAxisCarried {R : Type*} [Zero R] (i : Fin d) (s : Zd d → R) : Prop :=
  ∀ n, s n ≠ 0 → ∃ m : ℤ, n = m • zbasis i

end Pyramids
