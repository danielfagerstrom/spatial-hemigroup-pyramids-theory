/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.ClassicalKernels

/-!
# `prop:classical-pyramids-approximate`(1) and (5): supports and transforms

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:classical-pyramids-approximate`. Wave 3a:
`classical_pyramids_approximate_1` and `_5` moved here from `PyramidsSkeleton.ChA1Line`, unchanged
in statement and name.

## The route

The printed one. `W_n` is the convolution of the list of the dilates `T_{2^k}w`, `k < n`; the
support of a convolution lies in the sum of the supports (`conv_abs_gt_null`), and its transform is
the product of the transforms (`convList_charFun_real`). The binomial mask is carried by
`[-2h, 2h]` and has the transform `cos⁴(hω/2)` (`charFun_gridLaw_binomial`). The B-spline kernel
is a convolution power of the uniform law, whose transform is `sinc(hω/2)`.

The lemmas on lists of laws are indexed by a list of natural numbers, so that they apply to the
equivalent weights, `convList ((List.range n).map f)`, without reassociating a convolution.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (convPow)
open scoped Topology

/-! ## Lists of laws on the line -/

/-- The convolution of a list of probability measures on the line is a probability measure, and its
transform is the product of the transforms. -/
theorem convList_charFun_real (l : List (Measure ℝ)) (h : ∀ μ ∈ l, IsProbabilityMeasure μ) :
    IsProbabilityMeasure (convList l) ∧
      ∀ ω : ℝ, charFun (convList l) ω = (l.map fun μ => charFun μ ω).prod := by
  induction l with
  | nil =>
    refine ⟨by rw [convList]; infer_instance, fun ω => ?_⟩
    rw [convList, charFun_dirac]
    simp
  | cons μ l ih =>
    obtain ⟨hl, hlc⟩ := ih fun ν hν => h ν (List.mem_cons_of_mem _ hν)
    haveI := hl
    haveI := h μ List.mem_cons_self
    refine ⟨by rw [convList]; infer_instance, fun ω => ?_⟩
    rw [convList, List.map_cons, List.prod_cons, charFun_conv, hlc]

/-- The convolution of the laws `f k`, `k ∈ L`, is a probability measure. -/
theorem isProbabilityMeasure_convList_map (L : List ℕ) (f : ℕ → Measure ℝ)
    (hf : ∀ k, IsProbabilityMeasure (f k)) : IsProbabilityMeasure (convList (L.map f)) :=
  (convList_charFun_real _ fun _ hμ => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hμ
    exact hf k).1

/-- **The support of a convolution of a list**: if `f k` is carried by `[-R k, R k]` for `k ∈ L`,
the convolution of the `f k` is carried by `[-∑R k, ∑R k]`. -/
theorem convList_map_abs_gt_null (L : List ℕ) (f : ℕ → Measure ℝ)
    (hf : ∀ k, IsProbabilityMeasure (f k)) (R : ℕ → ℝ)
    (hR : ∀ k ∈ L, f k {x | R k < |x|} = 0) :
    convList (L.map f) {x | (L.map R).sum < |x|} = 0 := by
  induction L with
  | nil =>
    rw [List.map_nil, List.map_nil, List.sum_nil, convList,
      Measure.dirac_apply' _ (measurableSet_lt measurable_const continuous_abs.measurable)]
    simp
  | cons a L ih =>
    haveI := isProbabilityMeasure_convList_map L f hf
    haveI := hf a
    rw [List.map_cons, List.map_cons, List.sum_cons, convList]
    exact conv_abs_gt_null (hR a List.mem_cons_self)
      (ih fun k hk => hR k (List.mem_cons_of_mem _ hk))

/-- A sum over `List.range n` is the sum over `Finset.range n`. -/
theorem list_sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

/-- The complement of `[-R, R]` is `{x : R < |x|}`. -/
theorem compl_Icc_neg_eq (R : ℝ) : (Icc (-R) R)ᶜ = {x : ℝ | R < |x|} := by
  ext x
  simp only [mem_compl_iff, mem_Icc, mem_setOf_eq, ← abs_le, not_le]

/-- A dilate `T_c μ`, `c > 0`, of a law carried by `[-R, R]` is carried by `[-cR, cR]`. -/
theorem map_mul_abs_gt_null {μ : Measure ℝ} {c R : ℝ} (hc : 0 < c) (h : μ {x | R < |x|} = 0) :
    (μ.map fun x => c • x) {x | c * R < |x|} = 0 := by
  rw [Measure.map_apply (measurable_const_smul c)
    (measurableSet_lt measurable_const continuous_abs.measurable)]
  convert h using 2
  ext x
  simp only [mem_preimage, mem_setOf_eq, smul_eq_mul, abs_mul, abs_of_pos hc]
  exact mul_lt_mul_iff_right₀ hc

/-! ## The equivalent weights on the line -/

/-- `W_n` is a probability measure with `Ŵ_n(ω) = ∏_{k<n} ŵ(q^kω)`, on the line. -/
theorem equivWeight_charFun_real (q : ℝ) (w : Measure ℝ) [IsProbabilityMeasure w] (n : ℕ) :
    IsProbabilityMeasure (equivWeight q w n) ∧ ∀ ω : ℝ,
      charFun (equivWeight q w n) ω = ∏ k ∈ Finset.range n, charFun w (q ^ k * ω) := by
  have hl : ∀ μ ∈ (List.range n).map (fun k => w.map fun x => (q ^ k) • x),
      IsProbabilityMeasure μ := by
    intro μ hμ
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hμ
    exact Measure.isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
  obtain ⟨hp, hc⟩ := convList_charFun_real _ hl
  refine ⟨hp, fun ω => ?_⟩
  rw [equivWeight, hc, List.map_map, list_prod_map_range]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Function.comp_apply]
  exact charFun_map_smul _ _

/-- The binomial mask on `hℤ`, `h > 0`, is carried by `[-2h, 2h]`. -/
theorem gridLaw_binomial_abs_gt_null {h : ℝ} (hh : 0 < h) :
    gridLaw h binomialMask5 {x | 2 * h < |x|} = 0 := by
  have hm : MeasurableSet {x : ℝ | 2 * h < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [gridLaw_binomial_eq, Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hm, smul_eq_mul]
  rw [indicator_of_notMem, mul_zero]
  simp only [mem_setOf_eq, not_lt, abs_mul, abs_of_pos hh]
  have hn' := Finset.mem_Icc.1 hn
  have : |(n : ℝ)| ≤ 2 := by
    rw [abs_le]
    constructor
    · exact_mod_cast hn'.1
    · exact_mod_cast hn'.2
  nlinarith

/-- `W_n` of the binomial mask is carried by `[-2(2ⁿ - 1)h, 2(2ⁿ - 1)h]`. -/
theorem equivWeight_binomial_abs_gt_null {h : ℝ} (hh : 0 < h) (n : ℕ) :
    equivWeight 2 (gridLaw h binomialMask5) n {x | 2 * (2 ^ n - 1) * h < |x|} = 0 := by
  haveI := isProbabilityMeasure_gridLaw_binomial h
  have hf : ∀ k, IsProbabilityMeasure ((gridLaw h binomialMask5).map fun x => ((2 : ℝ) ^ k) • x) :=
    fun k => Measure.isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
  have h1 := convList_map_abs_gt_null (List.range n) _ hf (fun k => (2 : ℝ) ^ k * (2 * h))
    fun k _ => map_mul_abs_gt_null (by positivity) (gridLaw_binomial_abs_gt_null hh)
  have hsum : ((List.range n).map fun k => (2 : ℝ) ^ k * (2 * h)).sum = 2 * (2 ^ n - 1) * h := by
    rw [list_sum_map_range]
    clear h1
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [hsum] at h1
  exact h1

/-! ## `prop:classical-pyramids-approximate`(1) -/

/-- **`prop:classical-pyramids-approximate`(1).** `W_n` is carried by
`[-2(2ⁿ - 1)h, 2(2ⁿ - 1)h]`, and `Ŵ_n(ω) = ∏_{j<n} cos⁴(2^{j-1}hω)` vanishes at `π/h`. -/
theorem classical_pyramids_approximate_1 {h : ℝ} (hh : 0 < h) {n : ℕ} (hn : 1 ≤ n) :
    equivWeight 2 (gridLaw h binomialMask5) n
        (Icc (-(2 * (2 ^ n - 1) * h)) (2 * (2 ^ n - 1) * h))ᶜ = 0 ∧
      (∀ ω : ℝ, charFun (equivWeight 2 (gridLaw h binomialMask5) n) ω =
        ((∏ j ∈ Finset.range n, Real.cos (2 ^ j / 2 * h * ω) ^ 4 : ℝ) : ℂ)) ∧
      charFun (equivWeight 2 (gridLaw h binomialMask5) n) (Real.pi / h) = 0 := by
  haveI := isProbabilityMeasure_gridLaw_binomial h
  have hc : ∀ ω : ℝ, charFun (equivWeight 2 (gridLaw h binomialMask5) n) ω =
      ((∏ j ∈ Finset.range n, Real.cos (2 ^ j / 2 * h * ω) ^ 4 : ℝ) : ℂ) := by
    intro ω
    rw [(equivWeight_charFun_real 2 _ n).2, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [charFun_gridLaw_binomial]
    congr 4
    ring
  refine ⟨by rw [compl_Icc_neg_eq]; exact equivWeight_binomial_abs_gt_null hh n, hc, ?_⟩
  rw [hc, Finset.prod_eq_zero (i := 0) (Finset.mem_range.2 (by omega))]
  · simp
  · rw [pow_zero, show 1 / 2 * h * (Real.pi / h) = Real.pi / 2 by field_simp, Real.cos_pi_div_two]
    simp

/-! ## `prop:classical-pyramids-approximate`(5) -/

/-- **`prop:classical-pyramids-approximate`(5).** The B-spline kernel of order `m ≥ 1` and spacing
`h` has bounded support and the transform `(sin(hω/2)/(hω/2))^m`, which vanishes on
`(2π/h)ℤ ∖ {0}`. -/
theorem classical_pyramids_approximate_5 {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 1 ≤ m) :
    convPow (uniformInterval h) m (Icc (-(m * h / 2)) (m * h / 2))ᶜ = 0 ∧
      (∀ ω : ℝ, charFun (convPow (uniformInterval h) m) ω =
        (((Real.sinc (h * ω / 2)) ^ m : ℝ) : ℂ)) ∧
      ∀ k : ℤ, k ≠ 0 → charFun (convPow (uniformInterval h) m) (2 * Real.pi * k / h) = 0 := by
  haveI := isProbabilityMeasure_uniformInterval hh
  have hc : ∀ ω : ℝ, charFun (convPow (uniformInterval h) m) ω =
      (((Real.sinc (h * ω / 2)) ^ m : ℝ) : ℂ) := fun ω => by
    rw [charFun_convPow_real, charFun_uniformInterval hh, Complex.ofReal_pow]
  refine ⟨?_, hc, fun k hk => ?_⟩
  · rw [compl_Icc_neg_eq, mul_div_assoc]
    exact convPow_uniformInterval_abs_gt_null hh m
  · have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.2 hk
    rw [hc, show h * (2 * Real.pi * k / h) / 2 = k * Real.pi by field_simp,
      Real.sinc_of_ne_zero (mul_ne_zero hk' Real.pi_ne_zero), Real.sin_int_mul_pi, zero_div,
      zero_pow (by omega), Complex.ofReal_zero]

end Pyramids
