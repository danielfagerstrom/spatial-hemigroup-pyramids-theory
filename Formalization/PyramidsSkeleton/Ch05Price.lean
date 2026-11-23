/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.MatrixLadder
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# The target types of chapter 5, first part: the price of the plane

Blueprint: `blueprint/src/parts/05-price.tex` (§§ 5.1–5.3). **This file carries `sorry`s and is
not part of the proved library `Pyramids`.** Every `\notready` statement node of the part is typed
here, one declaration per clause or group of clauses; the four definition nodes are
`Pyramids.Defs.Price`'s (with `decimRecord` from `Pyramids.Defs.Matern`, `dilLadder` and
`knotKernel` from `Pyramids.Defs.Pyramid`).

Moved to the proved library in wave 3g: the four declarations of
`prop:grid-pyramid-not-isotropic` (`grid_pyramid_not_isotropic_union`, `_1`, `_2`, `_3`), to
`Pyramids.Price.GridKnot`, `Pyramids.Price.NotIsotropic` and `Pyramids.Price.FrameMatern`,
unchanged in name and conclusion, except that `grid_pyramid_not_isotropic_union` no longer takes
`2 ≤ q` and `0 < h`, which its proof does not read: dropped on 2026-11-15, a strengthening.
The three declarations of `prop:exact-masks` (`exact_masks_1`, `_1_poisson`, `_2`) moved to
`Pyramids.Price.ExactMasks`, unchanged in name, binders and conclusion. On 2026-11-15, by the
author's decision (a strengthening), `exact_masks_1` no longer takes the lattice `Γ`: its binder
`hw : IsLatticeMask Γ w` was replaced by the three hypotheses its proof reads.
The two declarations of `prop:binomial-knot-relation` (`binomial_knot_relation`, `_tensor`)
moved to `Pyramids.Price.BinomialKnot`, unchanged in name, binders and conclusion.
Moved in wave 3h: the two declarations of `prop:grid-frame-step-not-selected`
(`grid_frame_step_not_selected_1`, `_2`), to `Pyramids.Price.FrameStep`, unchanged in name and
conclusion, except that `_1` no longer takes `hN`, `hNsymm`, `h0` and `_2` no longer takes `hd`,
`hN`, `hNsymm`, `h0`, which their proofs do not read: dropped on 2026-11-15, a strengthening.
The six declarations of `prop:resolvent-masks-exact` (`resolvent_masks_exact_1`, `_2`, `_3`,
`_4_five`, `_4_nine`, `_4_general`) moved to `Pyramids.Price.ResolventMask` and
`Pyramids.Price.ResolventInstances`, unchanged in name and conclusion, except that `_1` no
longer takes `hfin` and `_3` no longer takes `hfin`, `hq` and the hypothesis `RΓ = Γ` of its last
clause, which their proofs do not read: dropped on 2026-11-15, a strengthening.

Moved in wave 3b: the two declarations of `prop:line-and-arrays` (`line_and_arrays_1`, `_2`), to
`Pyramids.Price.LineArrays`, unchanged in name and conclusion, except that `_2` no longer takes
`2 ≤ q`, which its proof does not read: dropped on 2026-11-15, a strengthening. Clause (1) is
proved through `CarriesGridLadder.family`, `exact_masks_1` and `grid_pyramids_id_2`, not through
A30.
Moved in wave 3b, on the VM: `records_creation` (`lem:records-creation`), to
`Pyramids.Price.RecordsCreation`, unchanged in name and conclusion, except that it takes `1 ≤ q`
for `2 ≤ q` and no longer takes `hpos`, `hN`, `hNsymm`, `h0`, which its proof does not read:
dropped on 2026-11-15, a strengthening.
Moved in wave 3b, on the VM: the five declarations of `prop:creation-grid-masks`
(`zdLaw_tensorIdx_eq_tensorPow`, `creation_grid_masks_1`, `_2`, `_3_resolvent`, `_3_frame`), to
`Pyramids.Price.CreationGridMasks`, unchanged in name and conclusion, except that `_1` and `_2`
take `1 ≤ d` for `2 ≤ d`, and `_3_resolvent` and `_3_frame` take `1 ≤ q` for `2 ≤ q` and no
longer take `hN`, `hNsymm`, `h0`, which their proofs do not read: dropped on 2026-11-15, a
strengthening.
Moved in wave 3b, on the VM: the two declarations of `prop:binomial-records`
(`binomial_records_1`, `_2`), to `Pyramids.Price.BinomialRecords`, unchanged in name and
conclusion, except that `_1` no longer takes `2 ≤ d` and `_2` no longer takes `hN`, `hNsymm`,
`h0`, which their proofs do not read: dropped on 2026-11-15, a strengthening.

## What writing it down found

1. **Exactness does not see the lattice.** Conditions (a)–(d) of `def:exact-grid-pyramid` do not
   mention `Γ`, so `IsExactLatticePyramid q w` is a property of `(w, q)`, and the mask condition
   (`IsLatticeMask Γ w`: symmetric probability `≠ δ₀` carried by `Γ`) is a separate hypothesis.
   The definition is stated over any real inner product space, so that `prop:line-and-arrays`(1)
   compares it with the line's operator definition at `E = ℝ` without transporting measures.
2. **(b) on transforms.** Weak continuity of `(s,t) ↦ μ_{s,t}` is typed as continuity of
   `(s,t) ↦ μ̂_{s,t}(ω)` for each `ω` (`IsLawHemigroup`), equivalent for probability laws on `ℝ^d`
   by Lévy's continuity theorem, the reading of chapters 2 and 3. Weak limits of laws (the product
   formula (`eq:knot-product`), the B-spline limit) are typed as pointwise convergence of the
   transforms of the partial convolutions to the transform of the limit, the same by that theorem.
3. **"The Lévy measure" through triplets.** `HasLevyMeasure μ ν` (a triplet exists and every
   triplet has Lévy measure `ν`) and `HasNoGaussianPart μ` read "the Lévy measure of `μ`" and "no
   Gaussian part"; `thm:cited-A39` makes the triplet unique, so nothing is lost. "Compound Poisson
   with Lévy measure `ν`" is `w = compoundPoissonLaw ν` together with `HasLevyMeasure w ν` (chapter
   4's finding 12). "The Lévy measure `ν_w` of the mask" in a later clause is quantified over:
   every `ν` with `HasLevyMeasure w ν`.
4. **Rotation invariance under `SO(d)`, symmetry groups in `O(d)`.** The definition says `SO(d)`
   (`IsSORotationInvariant`); "the group `{R ∈ O(d) : D_R μ_t = μ_t}`" is `symmetryGroup`.
   "`supp w` spans `ℝ^d`" is `span_ℝ {x | w{x} ≠ 0} = ⊤`: a law carried by a lattice has its atoms
   as support. "`RΓ = Γ`" is `lin R '' Γ = Γ`.
5. **The hyperoctahedral group** is `signedPermSet d`, the matrices with `R e_j = ±e_{σ(j)}`;
   "the symmetry group of every knot kernel is the hyperoctahedral group" is the set equality
   `symmetryGroup (μ_{q^n}) = signedPermSet d` for every `n ∈ ℤ` and every family carrying the
   frame ladder (the knot kernel is determined by the mask, clause (1)).
6. **Infinite products as limits of partial products.** `∏_i ∏_{m ≥ 1}` of the frame knot kernel
   is the limit of `∏_{m < M} ∏_i` (finite products commute); `∏_{m ≥ 1} ŵ(q^{-m}ω)^γ` likewise.
7. **The grid in its indices** (chapter 4's finding 15). `prop:grid-frame-step-not-selected`,
   `lem:records-creation`, `prop:creation-grid-masks`, `prop:binomial-records` read kernels on
   `hℤ^d` as arrays on `ℤ^d`: the frame mask is `tensorIdx (geomKernel a)`, the axis pass along
   `eᵢ` is `axisPassIdx (geomKernel a) i`, the binomial tensor mask is `tensorIdx binomialMask5`,
   neighbourhoods are sets of indices, and on the grid `q^k hℤ^d`, in its own indices, a
   `q^k𝒩`-maximum is an `𝒩`-maximum and the smoothing by `D_{q^k} w` is `kconv w`. `h` then plays
   no role and is not a parameter; infinite divisibility is that of `zdLaw d h w`, where it is.
   The nodes on a general `Γ` (`prop:grid-pyramid-not-isotropic`, `prop:exact-masks`,
   `prop:resolvent-masks-exact`) are typed on laws on `ℝ^d`, and the frame mask is there
   `tensorPow d (gridLaw h (geomKernel a))`, the same law: `zdLaw_tensorIdx_eq_tensorPow` states
   it (skeleton review 05, item 3), for every nonnegative summable `k`.
8. **`prop:line-and-arrays`(2) on any full-rank lattice** through a basis `b` of `Γ`: the input is
   an array `f` on `ℤ^d` (the indices of `b`), the algorithm is `decimRecord` of the array
   `k ↦ w{b k}`, and "`(D_{q^{n-1}}w * ⋯ * w * f)` restricted to `q^nΓ`" is
   `latticeApply b (equivWeight q w n) f (q^n m)`. The exact clause also states
   `μ_{1,q^n} = equivWeight q w n`, which the proof gives and which makes the law the record
   applies a law carried by `Γ`; "exact in sense (i)" is `IsExactLawArray`.
9. **`prop:resolvent-masks-exact`(4), "is (`eq:resolvent-mask`) with σ and p"** is the measure
   identity `zdLaw … = resolventMask p σ`, together with: `σ` is a mask on the lattice with finite
   support and `0 < p < 1`, so that clauses (1)–(3) apply. The general sentence drops "`𝒩 ⊂ Γ`"
   (the identity holds for any finite symmetric `𝒩 ⊂ ℝ^d ∖ {0}`), which is stronger, and asks only
   that `w` be a probability with the displayed transform (`1/ŵ = …` is `ŵ = (…)⁻¹`, the bracket
   being `≥ 1`).
10. **What is not typed.** In `def:exact-senses`, the sentences "the difference between those
   samples and the continuum kernels is aliasing", "`C` is below `1` whenever `λ` charges a point
   off the coarse grid" and "the subsample is the impulse response of smoothing by `λ` and keeping
   every `q`-th value" are claims inside a definition node (the precedent of chapters 3 and 4):
   the first is `prop:sampled-laplace-exact`(3), the other two are one-line skeleton statements if
   the author wants them. In `def:level-records`, "every record is bounded by `sup|f|`" and "the
   convolution reads `f_j` only on `q^jΓ`" likewise. In `def:exact-grid-pyramid`, "the mask is
   positive" is built into `Measure` (nonnegative weights). In `prop:creation-grid-masks`(1), "So
   Proposition `creation-grid`(1)–(2) applies to each of them" is the application of that node to
   the hypotheses the clause proves. In `prop:line-and-arrays`(1), "this equivalence is what
   identifies them" describes the equivalence.
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set Filter
open ScaleSpace (X convPow)
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace SchwartzMap Real

variable {d : ℕ}

/-! ## `prop:creation-grid-masks` — moved to `Pyramids.Price.CreationGridMasks` (wave 3b) -/

/-! ## `prop:binomial-records` — moved to `Pyramids.Price.BinomialRecords` (wave 3b) -/

/-! ## `prop:line-and-arrays` — moved to `Pyramids.Price.LineArrays` (wave 3b) -/

/-! ## `prop:expanding-grid-pyramid-not-isotropic` (review round 2, batch C, decision D1)

The statement of `grid_pyramid_not_isotropic_2`'s first conjunct with the scalar dilation `D_q`
replaced by an invertible matrix `M` (`CarriesMatrixLadder`, `Pyramids.Defs.MatrixLadder`).
Since 2026-11-23 (review round 3, batch C, s6-7.S2, a strengthening) `M` is invertible, where it
was expanding, and the declaration is renamed from `expanding_grid_pyramid_not_isotropic`; the
label keeps its old name. Not attempted. The printed proof needs: the infinite divisibility of
every law of the family (`lem:steps-infinitely-divisible`); `μ_{q^{n-1},q^n} = M^{n-1}_* w` from
(c_M) and (d), for every integer `n`; the triplet of a linear image (A42 at `U = M^{n-1}`) and the
additivity of triplets, for `ν_t ≥ M^{n-1}_* ν_w`; an atom of `ν_w` off `0`
(`lem:lattice-infinitely-divisible`); and the rotation step of `grid_pyramid_not_isotropic_2`,
with an atom of finite mass in place of the countable carrier. -/

/-- **`prop:expanding-grid-pyramid-not-isotropic`.** In `d ≥ 2`, if a family carries the grid
pyramid of a mask `w` on a full-rank lattice `Γ` with an invertible dilation `M`, no kernel
`μ_t`, `t > 0`, is invariant under `SO(d)`. Neither `MΓ ⊆ Γ` nor `M = qR` is assumed. -/
theorem matrix_grid_pyramid_not_isotropic (hd : 2 ≤ d) (Γ : Submodule ℤ (Rd d))
    [DiscreteTopology Γ] [IsZLattice ℝ Γ] {q : ℝ} {M : Mat d} (w : Measure (Rd d))
    (hw : IsLatticeMask (Γ : Set (Rd d)) w) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : CarriesMatrixLadder q M w μ) :
    ∀ t : ℝ, 0 < t → ¬ IsSORotationInvariant (μ 0 t) := by
  sorry

/-! ## `prop:grid-pyramid-singular-kernels`(3) (review round 3, batch C, s4-5.R2)

Clauses (1) and (2) are proved, `grid_pyramid_singular_kernels_1` and `_2` in
`Pyramids.Price.SingularKernels`. Clause (3) is proved in print only. Its printed proof needs: the
independent variables `X_m` with laws `D_{q^{-m}} w` on a product space; the convergence in
probability of their partial sums, from the weak convergence of the partial convolutions
(`eq:knot-product`) and the tightness of a weakly convergent sequence; Kolmogorov's zero-one
argument for an event that agrees almost surely with an event of `σ(X_{M+1}, X_{M+2}, …)` for every
`M`; and, between the knots, the compound Poisson form of a step with no Gaussian part and a finite
Lévy measure (A39). -/

/-- **`prop:grid-pyramid-singular-kernels`(3).** For an integer ratio `q` and an exact grid pyramid
on `hℤ^d`, every kernel `μ_t`, `t > 0`, of a carrying family is singular with respect to Lebesgue
measure. -/
theorem grid_pyramid_singular_kernels_3 {q : ℕ} {h : ℝ} (hh : 0 < h) {w : Measure (Rd d)}
    (hw : IsLatticeMask (gridSet d h) w) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder (q : ℝ) w μ) {t : ℝ} (ht : 0 < t) : μ 0 t ⟂ₘ volume := by
  sorry

/-! ## `prop:band-limited-refinable-mask` (review round 3, batch C, decision D2)

A density `p` on `ℝ^d` sampled on `hℤ^d`: `w := ∑_{n ∈ ℤ^d} h^d p(hn) δ_{hn}`. The node is proved
in print only; its Lean needs Poisson summation on `ℤ^d`, which Mathlib states on `ℝ` only. The
law `P := p(x) dx` is `volume.withDensity`, and the refinable law `μ`, printed as the law of
`∑_{m ≥ 1} q^{-m} Y_m`, is typed through its transform, the limit of the partial products
`∏_{m ≤ M} P̂(q^{-m} ω)`, which determines it. -/

/-- **The sampled mask** `∑_{n ∈ ℤ^d} h^d p(hn) δ_{hn}` of `prop:band-limited-refinable-mask`. -/
noncomputable def sampledMask (h : ℝ) (p : Rd d → ℝ) : Measure (Rd d) :=
  Measure.sum fun n : Zd d =>
    ENNReal.ofReal (h ^ d * p (latticePt h n)) • Measure.dirac (latticePt h n)

/-- **The law with density `p`.** -/
noncomputable def densityLaw (p : Rd d → ℝ) : Measure (Rd d) :=
  volume.withDensity fun x => ENNReal.ofReal (p x)

/-- **The hypotheses on the density** of `prop:band-limited-refinable-mask`: a rotation-invariant
probability density of the Schwartz class whose transform vanishes for `|ω| ≥ r`. -/
def IsBandLimitedDensity (r : ℝ) (p : 𝓢(Rd d, ℝ)) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∫ x, p x = 1 ∧ (∀ x y : Rd d, ‖x‖ = ‖y‖ → p x = p y) ∧
    ∀ ω : Rd d, r ≤ ‖ω‖ → charFun (densityLaw (p : Rd d → ℝ)) ω = 0

/-- **`prop:band-limited-refinable-mask`, such densities exist**: for every `r > 0`. -/
theorem band_limited_density_exists {r : ℝ} (hr : 0 < r) :
    ∃ p : 𝓢(Rd d, ℝ), IsBandLimitedDensity r p := by
  sorry

/-- **`prop:band-limited-refinable-mask`(1), the mask.** `w` is a mask on `hℤ^d`, its transform is
the periodization `∑_k φ(ω - 2πk/h)` of `φ = P̂`, equal to `φ` on `|ω| < 2π/h - r`; it has no
exponential moment, so its support is infinite, and it is not infinitely divisible. -/
theorem band_limited_refinable_mask_1 (hd : 1 ≤ d) {q h r : ℝ} (hq : 1 < q) (hh : 0 < h)
    (hr : 0 < r) (hrq : r ≤ 2 * π / ((q + 1) * h)) {p : 𝓢(Rd d, ℝ)}
    (hp : IsBandLimitedDensity r p) :
    IsLatticeMask (gridSet d h) (sampledMask h p) ∧
      (∀ ω : Rd d, HasSum (fun k : Zd d => charFun (densityLaw (p : Rd d → ℝ))
        (ω - latticePt (2 * π / h) k)) (charFun (sampledMask h p) ω)) ∧
      (∀ ω : Rd d, ‖ω‖ < 2 * π / h - r →
        charFun (sampledMask h p) ω = charFun (densityLaw (p : Rd d → ℝ)) ω) ∧
      (¬ ∃ c : ℝ, 0 < c ∧ Integrable (fun x : Rd d => Real.exp (c * ‖x‖)) (sampledMask h p)) ∧
      (¬ ∃ S : Set (Rd d), S.Finite ∧ sampledMask h p Sᶜ = 0) ∧
      ¬ IsInfinitelyDivisible (sampledMask h p) := by
  sorry

/-- **`prop:band-limited-refinable-mask`(2), the refinable law.** The law `μ` whose transform is
`∏_{m ≥ 1} φ(q^{-m} ω)` is a rotation-invariant probability law with a smooth density, it satisfies
the knot relation `D_q μ = μ * w`, and the partial products of the mask (`eq:knot-product`) converge
to its transform. -/
theorem band_limited_refinable_mask_2 (hd : 1 ≤ d) {q h r : ℝ} (hq : 1 < q) (hh : 0 < h)
    (hr : 0 < r) (hrq : r ≤ 2 * π / ((q + 1) * h)) {p : 𝓢(Rd d, ℝ)}
    (hp : IsBandLimitedDensity r p) :
    ∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧
      (∀ ω : Rd d, Tendsto (fun M => ladderProd q (densityLaw (p : Rd d → ℝ)) M ω) atTop
        (𝓝 (charFun μ ω))) ∧
      IsSORotationInvariant μ ∧
      (∃ f : Rd d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ x, 0 ≤ f x) ∧ μ = densityLaw f) ∧
      μ.map (fun x => q • x) = μ ∗ sampledMask h p ∧
      ∀ ω : Rd d, Tendsto (fun M => ladderProd q (sampledMask h p) M ω) atTop
        (𝓝 (charFun μ ω)) := by
  sorry

/-- **`prop:band-limited-refinable-mask`(3), the pyramid.** The grid pyramid of `(w, q)` is not
exact, and a family with (a), (c), (d) of `def:exact-grid-pyramid` but not (b) carries it with every
kernel rotation invariant: its kernels are constant on `[q^{n-1}, q^n)` and jump at every knot. -/
theorem band_limited_refinable_mask_3 (hd : 1 ≤ d) {q h r : ℝ} (hq : 1 < q) (hh : 0 < h)
    (hr : 0 < r) (hrq : r ≤ 2 * π / ((q + 1) * h)) {p : 𝓢(Rd d, ℝ)}
    (hp : IsBandLimitedDensity r p) :
    ¬ IsExactLatticePyramid q (sampledMask h p) ∧
      ∃ fam : ℝ → ℝ → Measure (Rd d),
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (fam s t)) ∧
        (∀ t : ℝ, 0 ≤ t → fam t t = Measure.dirac 0) ∧
        (∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t → fam r t = fam s t ∗ fam r s) ∧
        IsCovariantAt fam q (fun t => q * t) ∧
        fam 1 q = sampledMask h p ∧
        (∀ t : ℝ, 0 < t → IsSORotationInvariant (fam 0 t)) ∧
        ∀ n : ℤ, (∀ t ∈ Ico (q ^ (n - 1)) (q ^ n), fam 0 t = fam 0 (q ^ (n - 1))) ∧
          fam 0 (q ^ n) ≠ fam 0 (q ^ (n - 1)) := by
  sorry

end Pyramids
