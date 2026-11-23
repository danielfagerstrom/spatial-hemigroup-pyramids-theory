/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Price.FrameMatern
import Pyramids.LineAppendix.ClassicalKernels
import Pyramids.LineAppendix.ClassicalWeights

/-!
# `prop:binomial-knot-relation`: the binomial mask satisfies the knot relation

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:binomial-knot-relation`. Wave 3g:
`binomial_knot_relation` and `binomial_knot_relation_tensor` moved here from
`PyramidsSkeleton.Ch05Price`, unchanged in name, binders and conclusion.

## The route

* **The line** is `prop:equivalent-weights`(2) (`equivalent_weights_2`): `β̂(ω) = cos⁴(hω/2)`,
  Viète's product, the transform `sinc(hω/2)` of the uniform law, and `D_2 μ_1 = μ_1 * β`. The
  partial convolutions have the partial products as transforms (`charFun_ladderPartialConv`).
* **Bounded support, not infinitely divisible.** The cubic B-spline is carried by `[-2h, 2h]`
  and `prop:classical-kernels-no-exact-cascade` makes it, and `β`, not infinitely divisible
  (`prop:no-bounded-step`, A46). A family carrying the ladder of `(β, 2)` would make the mask
  `μ_{1,2}` infinitely divisible (`lem:family-structure`, A41).
* **The tensor powers.** Transforms factor over the axes (`tensorPow_charFun`), so the partial
  products are the products over the axes of those of the line, and the limit is a finite product
  of limits. A tensor power of a law carried by `[-r, r]` is carried by the ball of radius
  `√d r`, and it is no point mass when the factor's transform vanishes somewhere (`d ≥ 1`), so
  `prop:no-bounded-step` applies to `μ_1^{⊗d}` and to `β^{⊗d}` directly, with no marginal.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (convPow)
open scoped Topology ENNReal

variable {d : ℕ}

/-! ## Tensor powers -/

/-- **A tensor power of a law carried by `[-r, r]` is carried by the ball of radius `√(d r²)`.** -/
theorem tensorPow_norm_gt_null {ν : Measure ℝ} [SigmaFinite ν] {r : ℝ}
    (hν : ν {x | r < |x|} = 0) :
    tensorPow d ν {x | Real.sqrt (d * r ^ 2) < ‖x‖} = 0 := by
  rw [tensorPow, Measure.map_apply (PiLp.continuous_toLp 2 _).measurable
    (measurableSet_lt measurable_const measurable_norm)]
  refine measure_mono_null (fun y hy => ?_)
    (measure_iUnion_null fun i : Fin d =>
      Measure.pi_eval_preimage_null (fun _ : Fin d => ν) (i := i) hν)
  simp only [mem_preimage, mem_setOf_eq] at hy
  simp only [mem_iUnion, mem_preimage, mem_setOf_eq]
  by_contra hall
  push Not at hall
  refine (not_lt.2 ?_) hy
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(WithLp.toLp 2 y : Rd d) i‖ ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs, PiLp.toLp_apply]
        exact pow_le_pow_left₀ (abs_nonneg _) (hall i) 2
    _ = d * r ^ 2 := by simp

/-- **A tensor power is no point mass** when `d ≥ 1` and the factor's transform vanishes
somewhere. -/
theorem tensorPow_ne_dirac (hd : 1 ≤ d) {ν : Measure ℝ} [IsProbabilityMeasure ν] {t : ℝ}
    (ht : charFun ν t = 0) (x : Rd d) : tensorPow d ν ≠ Measure.dirac x := by
  intro hx
  set i0 : Fin d := ⟨0, hd⟩
  have h1 := (tensorPow_charFun (d := d) (m := ν)).2 (EuclideanSpace.single i0 t)
  rw [Finset.prod_eq_zero (Finset.mem_univ i0) (by rw [PiLp.single_apply,
    if_pos rfl, ht]), hx, charFun_dirac] at h1
  exact Complex.exp_ne_zero _ h1

/-! ## The binomial mask and the cubic B-spline -/

/-- `β̂(π/h) = cos⁴(π/2) = 0`. -/
theorem charFun_gridLaw_binomial_pi {h : ℝ} (hh : 0 < h) :
    charFun (gridLaw h binomialMask5) (Real.pi / h) = 0 := by
  rw [charFun_gridLaw_binomial, show h * (Real.pi / h) / 2 = Real.pi / 2 by field_simp,
    Real.cos_pi_div_two]
  simp

/-- The cubic B-spline is a probability law with transform `sinc(hω/2)⁴`. -/
theorem charFun_bspline4 {h : ℝ} (hh : 0 < h) :
    IsProbabilityMeasure (convPow (uniformInterval h) 4) ∧
      ∀ ω : ℝ, charFun (convPow (uniformInterval h) 4) ω =
        ((Real.sinc (h * ω / 2) ^ 4 : ℝ) : ℂ) := by
  haveI := isProbabilityMeasure_uniformInterval hh
  refine ⟨ScaleSpace.isProbabilityMeasure_convPow_real (uniformInterval h) 4, fun ω => ?_⟩
  rw [charFun_convPow_real, charFun_uniformInterval hh, Complex.ofReal_pow]

/-- `sinc(hω/2)⁴` vanishes at `ω = 2π/h`. -/
theorem charFun_bspline4_zero {h : ℝ} (hh : 0 < h) :
    charFun (convPow (uniformInterval h) 4) (2 * Real.pi / h) = 0 := by
  rw [(charFun_bspline4 hh).2, show h * (2 * Real.pi / h) / 2 = Real.pi by field_simp,
    Real.sinc_of_ne_zero Real.pi_ne_zero, Real.sin_pi, zero_div]
  simp

/-- The partial products of the line, in the two spellings. -/
theorem ladderProd_line (q : ℝ) (w : Measure ℝ) (M : ℕ) (ω : ℝ) :
    ladderProd q w M ω = ladderPartialProduct q w M ω := rfl

/-- The partial convolutions of the line, in the two spellings. -/
theorem ladderConv_line (q : ℝ) (w : Measure ℝ) (M : ℕ) :
    ladderConv q w M = ladderPartialConv q w M := rfl

/-! ## `prop:binomial-knot-relation` -/

/-- **`prop:binomial-knot-relation`, the line.** For the binomial mask `β` on `hℤ` and `q = 2`:
`β̂(2^{-m}ω) = cos⁴(2^{-m-1}hω)` for `m ≥ 1`; the product (`eq:knot-product`) converges to
`(sin(hω/2)/(hω/2))⁴`, the transform of the cubic B-spline `μ_1` (the fourfold convolution of the
uniform law on `[-h/2, h/2]`), to which the partial convolutions converge; `D_2 μ_1 = μ_1 * β`;
`μ_1` has bounded support and is not infinitely divisible; and the grid pyramid of `(β, 2)` is not
exact. -/
theorem binomial_knot_relation {h : ℝ} (hh : 0 < h) :
    (∀ (m : ℕ) (ω : ℝ), charFun (gridLaw h binomialMask5) ((2 : ℝ) ^ (-((m : ℤ) + 1)) * ω) =
      ((Real.cos ((2 : ℝ) ^ (-((m : ℤ) + 2)) * h * ω) ^ 4 : ℝ) : ℂ)) ∧
      (∀ ω : ℝ, Tendsto (fun M => ladderProd 2 (gridLaw h binomialMask5) M ω) atTop
        (𝓝 ((Real.sinc (h * ω / 2) ^ 4 : ℝ) : ℂ))) ∧
      (∀ ω : ℝ, charFun (convPow (uniformInterval h) 4) ω = ((Real.sinc (h * ω / 2) ^ 4 : ℝ) : ℂ)) ∧
      (∀ ω : ℝ, Tendsto (fun M => charFun (ladderConv 2 (gridLaw h binomialMask5) M) ω) atTop
        (𝓝 (charFun (convPow (uniformInterval h) 4) ω))) ∧
      (convPow (uniformInterval h) 4).map (fun x => 2 * x) =
        convPow (uniformInterval h) 4 ∗ gridLaw h binomialMask5 ∧
      (∃ R : ℝ, convPow (uniformInterval h) 4 {x | R < |x|} = 0) ∧
      ¬ IsInfinitelyDivisible (convPow (uniformInterval h) 4) ∧
      ¬ IsExactLatticePyramid (2 : ℝ) (gridLaw h binomialMask5) := by
  haveI := isProbabilityMeasure_gridLaw_binomial h
  obtain ⟨hPU, hU⟩ := charFun_bspline4 hh
  obtain ⟨hlim, -, hall⟩ := equivalent_weights_2 hh
  obtain ⟨-, hrel, -⟩ := hall _ hPU hU
  refine ⟨fun m ω => ?_, fun ω => hlim ω, hU, fun ω => ?_, hrel,
    ⟨_, convPow_uniformInterval_abs_gt_null hh 4⟩,
    (classical_kernels_no_exact_cascade_masks hh).2.1 4 (by norm_num) |>.1, ?_⟩
  · rw [charFun_gridLaw_binomial]
    congr 3
    rw [show -((m : ℤ) + 1) = -((m : ℤ) + 2) + 1 by ring, zpow_add₀ two_ne_zero, zpow_one]
    ring
  · simp_rw [ladderConv_line, (charFun_ladderPartialConv 2 _ _).2 ω, hU]
    exact hlim ω
  · rintro ⟨μ, -, hfam, -, hw⟩
    have hid := isLawHemigroup_line_infinitelyDivisible hfam zero_le_one one_le_two
    rw [hw] at hid
    exact (classical_kernels_no_exact_cascade_masks hh).1.1 hid

/-- **`prop:binomial-knot-relation`, the tensor powers.** On `hℤ^d`, `d ≥ 1`: the product for
`β^{⊗d}` converges to the transform of `μ_1^{⊗d}`, to which the partial convolutions converge;
`D_2 μ_1^{⊗d} = μ_1^{⊗d} * β^{⊗d}`; `μ_1^{⊗d}` has bounded support and is not infinitely
divisible; and the grid pyramid of `(β^{⊗d}, 2)` is not exact. -/
theorem binomial_knot_relation_tensor (hd : 1 ≤ d) {h : ℝ} (hh : 0 < h) :
    (∀ ω : Rd d, Tendsto (fun M => ladderProd 2 (tensorPow d (gridLaw h binomialMask5)) M ω)
      atTop (𝓝 (charFun (tensorPow d (convPow (uniformInterval h) 4)) ω))) ∧
      (∀ ω : Rd d, Tendsto
        (fun M => charFun (ladderConv 2 (tensorPow d (gridLaw h binomialMask5)) M) ω) atTop
        (𝓝 (charFun (tensorPow d (convPow (uniformInterval h) 4)) ω))) ∧
      (tensorPow d (convPow (uniformInterval h) 4)).map (fun x => (2 : ℝ) • x) =
        tensorPow d (convPow (uniformInterval h) 4) ∗ tensorPow d (gridLaw h binomialMask5) ∧
      (∃ R : ℝ, tensorPow d (convPow (uniformInterval h) 4) {x | R < ‖x‖} = 0) ∧
      ¬ IsInfinitelyDivisible (tensorPow d (convPow (uniformInterval h) 4)) ∧
      ¬ IsExactLatticePyramid (2 : ℝ) (tensorPow d (gridLaw h binomialMask5)) := by
  haveI := isProbabilityMeasure_gridLaw_binomial h
  obtain ⟨hPU, hU⟩ := charFun_bspline4 hh
  obtain ⟨hlim, -, hall⟩ := equivalent_weights_2 hh
  obtain ⟨-, -, hrelT⟩ := hall _ hPU hU
  haveI := (tensorPow_charFun (d := d) (m := gridLaw h binomialMask5)).1
  haveI := (tensorPow_charFun (d := d) (m := convPow (uniformInterval h) 4)).1
  -- the partial products factor over the axes
  have hprod : ∀ (M : ℕ) (ω : Rd d), ladderProd 2 (tensorPow d (gridLaw h binomialMask5)) M ω =
      ∏ i, ladderProd 2 (gridLaw h binomialMask5) M (ω i) := by
    intro M ω
    rw [ladderProd, Finset.prod_congr rfl fun m _ => tensorPow_charFun.2 _, Finset.prod_comm]
    rfl
  have hlimT : ∀ ω : Rd d, Tendsto
      (fun M => ladderProd 2 (tensorPow d (gridLaw h binomialMask5)) M ω) atTop
      (𝓝 (charFun (tensorPow d (convPow (uniformInterval h) 4)) ω)) := by
    intro ω
    simp_rw [hprod, tensorPow_charFun.2 ω, hU]
    exact tendsto_finsetProd _ fun i _ => hlim (ω i)
  have hbddU : ∃ R : ℝ, tensorPow d (convPow (uniformInterval h) 4) {x | R < ‖x‖} = 0 :=
    ⟨_, tensorPow_norm_gt_null (convPow_uniformInterval_abs_gt_null hh 4)⟩
  refine ⟨hlimT, fun ω => ?_, hrelT d, hbddU,
    (no_bounded_step _ hbddU (tensorPow_ne_dirac hd (charFun_bspline4_zero hh))).1, ?_⟩
  · simp_rw [(ladderConv_charFun 2 _ _).2 ω]
    exact hlimT ω
  · rintro ⟨μ, -, hfam, -, hw⟩
    have hid := isLawHemigroup_infinitelyDivisible hd hfam 1 2 zero_le_one one_le_two
    rw [hw] at hid
    exact (no_bounded_step _ ⟨_, tensorPow_norm_gt_null (gridLaw_binomial_abs_gt_null hh)⟩
      (tensorPow_ne_dirac hd (charFun_gridLaw_binomial_pi hh))).1 hid

end Pyramids
