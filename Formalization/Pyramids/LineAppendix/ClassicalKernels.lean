/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.DiscreteCovarianceLine
import Pyramids.Pyramid.NoBoundedStep
import Pyramids.Pyramid.EquivalentWeights
import Pyramids.Defs.LineAppendix

/-!
# `prop:classical-kernels-no-exact-cascade`: the classical generating kernels are steps of no family

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:classical-kernels-no-exact-cascade`. Wave 2e:
the three declarations moved here from `PyramidsSkeleton.ChA1Line`, their statements unchanged.

## The route

The printed one.

* **The general statement.** `w` is carried to `ℝ¹` by `x ↦ xe₀`, where it keeps bounded support
  and is no point mass, so `prop:no-bounded-step` at `d = 1` says it is not infinitely divisible,
  and infinite divisibility would carry over. The kernels of a family with (A1)–(A7) satisfy (I1)
  and (I2) (`lem:line-axioms-kernels`(1)), and so do their images in `ℝ¹`; by the second clause of
  `prop:no-bounded-step` none of these is the image of `w`. No cited fact is used directly: A46
  and A41 enter through `prop:no-bounded-step`.
* **The masks.** A finite mask that is a probability measure has bounded support. The binomial
  mask and the B-spline kernels of every order `m ≥ 1` are no point masses because their transforms
  vanish somewhere (`cos⁴(hω/2)` at `ω = π/h`, `sinc(hω/2)^m` at `ω = 2π/h`), while that of a
  point mass has modulus `1`. The support of the `m`-fold convolution of the uniform law on
  `[-h/2, h/2]` lies in `[-mh/2, mh/2]`.
* **Burt's family** (fidelity review R50, 2026-11-16). Burt's normalization and equal contribution
  give `b = 1/4`, so the mask carries mass at both `±h`, which no point mass does.
* **The pyramid.** Its step at `n = 0` is `μ_{1,q} = w` itself.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set
open ScaleSpace (PreCascadeCore IsPositive IsKernelFamily convPow)

/-! ## Laws of bounded support -/

/-- A law whose transform vanishes somewhere is no point mass. -/
theorem ne_dirac_of_charFun_eq_zero {w : Measure ℝ} {ω : ℝ} (h : charFun w ω = 0) (x : ℝ) :
    w ≠ Measure.dirac x := by
  rintro rfl
  rw [charFun_dirac] at h
  exact Complex.exp_ne_zero _ h

/-- **The support of a convolution**: if `μ` is carried by `[-R₁, R₁]` and `ν` by `[-R₂, R₂]`, then
`μ * ν` is carried by `[-(R₁ + R₂), R₁ + R₂]`. -/
theorem conv_abs_gt_null {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {R₁ R₂ : ℝ}
    (h₁ : μ {x | R₁ < |x|} = 0) (h₂ : ν {x | R₂ < |x|} = 0) :
    (μ ∗ ν) {x | R₁ + R₂ < |x|} = 0 := by
  have hm : ∀ R : ℝ, MeasurableSet {x : ℝ | R < |x|} := fun R =>
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [Measure.conv, Measure.map_apply measurable_add (hm _)]
  have hsub : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' {x | R₁ + R₂ < |x|} ⊆
      {x | R₁ < |x|} ×ˢ univ ∪ univ ×ˢ {x | R₂ < |x|} := by
    intro p hp
    simp only [mem_preimage, mem_setOf_eq] at hp
    by_contra hcon
    simp only [mem_union, mem_prod, mem_setOf_eq, mem_univ, and_true, true_and, not_or,
      not_lt] at hcon
    have := abs_add_le p.1 p.2
    linarith [hcon.1, hcon.2]
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, h₁, zero_mul]
  · rw [Measure.prod_prod, h₂, mul_zero]

/-- The uniform law on `[-h/2, h/2]` is carried by it. -/
theorem uniformInterval_abs_gt_null (h : ℝ) : uniformInterval h {x | h / 2 < |x|} = 0 := by
  rw [uniformInterval, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_lt measurable_const continuous_abs.measurable)]
  have he : {x : ℝ | h / 2 < |x|} ∩ Icc (-(h / 2)) (h / 2) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, mem_Icc, mem_empty_iff_false, iff_false, not_and]
    intro hx h1 h2
    have := abs_le.2 ⟨h1, h2⟩
    linarith
  rw [he, measure_empty, smul_zero]

/-- The B-spline kernel of order `m` is carried by `[-mh/2, mh/2]`. -/
theorem convPow_uniformInterval_abs_gt_null {h : ℝ} (hh : 0 < h) (m : ℕ) :
    convPow (uniformInterval h) m {x | m * (h / 2) < |x|} = 0 := by
  haveI := isProbabilityMeasure_uniformInterval hh
  induction m with
  | zero =>
    rw [convPow, Measure.dirac_apply' _ (measurableSet_lt measurable_const
      continuous_abs.measurable)]
    simp
  | succ m ih =>
    haveI := ScaleSpace.isFiniteMeasure_convPow (uniformInterval h) m
    rw [convPow, show ((m + 1 : ℕ) : ℝ) * (h / 2) = m * (h / 2) + h / 2 by push_cast; ring]
    exact conv_abs_gt_null ih (uniformInterval_abs_gt_null h)

/-- A finite mask with nonnegative weights summing to `1` is a probability measure of bounded
support. -/
theorem gridLaw_finite_facts (h : ℝ) {lam : ℤ → ℝ} (hfin : {n | lam n ≠ 0}.Finite)
    (hnn : ∀ n, 0 ≤ lam n) (hsum : ∑' n, lam n = 1) :
    IsProbabilityMeasure (gridLaw h lam) ∧ ∃ R : ℝ, gridLaw h lam {x | R < |x|} = 0 := by
  have hm : ∀ R : ℝ, MeasurableSet {x : ℝ | R < |x|} := fun R =>
    measurableSet_lt measurable_const continuous_abs.measurable
  refine ⟨⟨?_⟩, ?_⟩
  · rw [gridLaw, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn (summable_of_hasFiniteSupport hfin), hsum,
      ENNReal.ofReal_one]
  · set F := hfin.toFinset
    refine ⟨∑ n ∈ F, |h * n|, ?_⟩
    rw [gridLaw, Measure.sum_apply _ (hm _)]
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    by_cases hn : lam n = 0
    · simp [hn]
    · have hnF : n ∈ F := hfin.mem_toFinset.2 hn
      have hle : |h * n| ≤ ∑ n ∈ F, |h * n| :=
        Finset.single_le_sum (f := fun n : ℤ => |h * (n : ℝ)|) (fun _ _ => abs_nonneg _) hnF
      rw [Measure.smul_apply, Measure.dirac_apply' _ (hm _), smul_eq_mul]
      rw [indicator_of_notMem (by simp only [mem_setOf_eq, not_lt]; exact hle), mul_zero]

/-! ## `prop:classical-kernels-no-exact-cascade` -/

/-- **`prop:classical-kernels-no-exact-cascade`, the general statement.** A probability measure of
bounded support, not a point mass, is not infinitely divisible and is no `μ_{0,t}` or `μ_{s,t}` of
any family satisfying (A1)–(A7). -/
theorem classical_kernels_no_exact_cascade (w : Measure ℝ) [IsProbabilityMeasure w]
    (hbdd : ∃ R : ℝ, w {x | R < |x|} = 0) (hnp : ∀ x : ℝ, w ≠ Measure.dirac x) :
    IsStepOfNoFamily w := by
  -- `w` carried to `ℝ¹` keeps bounded support and is no point mass
  haveI : IsProbabilityMeasure (w.map lineEmbL) :=
    Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable
  obtain ⟨R, hR⟩ := hbdd
  have hbdd' : ∃ R : ℝ, (w.map lineEmbL) {x | R < ‖x‖} = 0 := by
    refine ⟨R, ?_⟩
    rw [Measure.map_apply lineEmbL.continuous.measurable
      (measurableSet_lt measurable_const continuous_norm.measurable)]
    convert hR using 2
    ext x
    simp only [mem_preimage, mem_setOf_eq, lineEmbL_apply]
    have hn : ‖lineEmb x‖ = |x| := by
      rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_rd1, lineEmb_apply_zero, Real.sqrt_sq_eq_abs]
    rw [hn]
  have hnp' : ∀ y : Rd 1, w.map lineEmbL ≠ Measure.dirac y := by
    intro y hy
    apply hnp (y 0)
    have h1 := congrArg (fun m : Measure (Rd 1) => m.map lineProjL) hy
    simp only [map_lineProj_lineEmb] at h1
    rw [h1, Measure.map_dirac' lineProjL.continuous.measurable, lineProjL_apply]
  -- `prop:no-bounded-step` at `d = 1`
  obtain ⟨hnid, hstep⟩ := no_bounded_step (d := 1) (w.map lineEmbL) hbdd' hnp'
  refine ⟨fun hid => hnid (isInfinitelyDivisible_map_lineEmb hid),
    fun Fam μ hpos hμ s t hs hst heq => ?_⟩
  obtain ⟨-, hhemi, -⟩ := line_axioms_kernels_1 Fam μ hμ
  exact hstep _ (isLawHemigroup_lineEmb hhemi) s t hs hst (by simp only [heq])

/-- **`prop:classical-kernels-no-exact-cascade`, the masks listed.** The binomial mask, the
B-spline kernels of every order `m ≥ 1`, and every finite mask on `hℤ` that is a probability
measure and not a point mass. -/
theorem classical_kernels_no_exact_cascade_masks {h : ℝ} (hh : 0 < h) :
    IsStepOfNoFamily (gridLaw h binomialMask5) ∧
      (∀ m : ℕ, 1 ≤ m → IsStepOfNoFamily (convPow (uniformInterval h) m)) ∧
      ∀ lam : ℤ → ℝ, {n | lam n ≠ 0}.Finite → (∀ n, 0 ≤ lam n) → ∑' n, lam n = 1 →
        (∀ x : ℝ, gridLaw h lam ≠ Measure.dirac x) → IsStepOfNoFamily (gridLaw h lam) := by
  -- the finite masks
  have hfinite : ∀ lam : ℤ → ℝ, {n | lam n ≠ 0}.Finite → (∀ n, 0 ≤ lam n) → ∑' n, lam n = 1 →
      (∀ x : ℝ, gridLaw h lam ≠ Measure.dirac x) → IsStepOfNoFamily (gridLaw h lam) := by
    intro lam hfin hnn hsum hnp
    obtain ⟨hprob, hbdd⟩ := gridLaw_finite_facts h hfin hnn hsum
    exact classical_kernels_no_exact_cascade _ hbdd hnp
  refine ⟨?_, fun m hm => ?_, hfinite⟩
  · -- the binomial mask: `ŵ(π/h) = cos⁴(π/2) = 0`
    have hfin : {n : ℤ | binomialMask5 n ≠ 0}.Finite :=
      (Finset.Icc (-2 : ℤ) 2).finite_toSet.subset fun n hn => by
        by_contra hcon
        exact hn (binomialMask5_eq_zero hcon)
    have hnn : ∀ n, 0 ≤ binomialMask5 n := fun n => by
      rw [binomialMask5]
      split_ifs <;> positivity
    have hsum : ∑' n, binomialMask5 n = 1 := by
      haveI := isProbabilityMeasure_gridLaw_binomial h
      have h1 := measure_univ (μ := gridLaw h binomialMask5)
      rw [gridLaw, Measure.sum_apply _ MeasurableSet.univ] at h1
      simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at h1
      rw [← ENNReal.ofReal_tsum_of_nonneg hnn (summable_of_hasFiniteSupport hfin)] at h1
      rw [← ENNReal.ofReal_eq_one.1 h1]
    refine hfinite _ hfin hnn hsum fun x => ne_dirac_of_charFun_eq_zero (ω := Real.pi / h) ?_ x
    rw [charFun_gridLaw_binomial, show h * (Real.pi / h) / 2 = Real.pi / 2 by field_simp,
      Real.cos_pi_div_two]
    simp
  · -- the B-spline kernels: `sinc(hω/2)^m` vanishes at `ω = 2π/h`
    haveI := isProbabilityMeasure_uniformInterval hh
    haveI := ScaleSpace.isProbabilityMeasure_convPow_real (uniformInterval h) m
    refine classical_kernels_no_exact_cascade _ ⟨_, convPow_uniformInterval_abs_gt_null hh m⟩
      fun x => ne_dirac_of_charFun_eq_zero (ω := 2 * Real.pi / h) ?_ x
    rw [charFun_convPow_real, charFun_uniformInterval hh,
      show h * (2 * Real.pi / h) / 2 = Real.pi by field_simp,
      Real.sinc_of_ne_zero Real.pi_ne_zero, Real.sin_pi, zero_div, Complex.ofReal_zero,
      zero_pow (by omega)]

/-- **The five-tap mask `(c, b, a, b, c)`** on `ℤ`: `a` at `0`, `b` at `±1`, `c` at `±2`, zero
elsewhere. -/
noncomputable def fiveTapMask (a b c : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then a else if n = 1 ∨ n = -1 then b else if n = 2 ∨ n = -2 then c else 0

theorem fiveTapMask_eq_zero {a b c : ℝ} {n : ℤ} (hn : n ∉ Finset.Icc (-2 : ℤ) 2) :
    fiveTapMask a b c n = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  unfold fiveTapMask
  split_ifs <;> first | rfl | omega

/-- **`prop:classical-kernels-no-exact-cascade`, Burt's family.** A five-tap mask `(c, b, a, b, c)`
on `hℤ` with Burt's normalization `a + 2b + 2c = 1` and equal contribution at the ratio `2`,
`a + 2c = 2b` [Burt 1981, pp. 23–24], and `a, c ≥ 0`, is a step of no family. The two constraints
give `b = 1/4`, so the mask is a probability measure with mass at `±h`, and no point mass. Burt's
unimodality is not used. -/
theorem classical_kernels_no_exact_cascade_burt {h : ℝ} (hh : 0 < h) {a b c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hC1 : a + 2 * b + 2 * c = 1) (hC4 : a + 2 * c = 2 * b) :
    IsStepOfNoFamily (gridLaw h (fiveTapMask a b c)) := by
  have hb' : b = 1 / 4 := by linarith
  have hfin : {n : ℤ | fiveTapMask a b c n ≠ 0}.Finite :=
    (Finset.Icc (-2 : ℤ) 2).finite_toSet.subset fun n hn => by
      by_contra hcon
      exact hn (fiveTapMask_eq_zero hcon)
  have hnn : ∀ n, 0 ≤ fiveTapMask a b c n := fun n => by
    unfold fiveTapMask
    split_ifs <;> linarith
  have hsum : ∑' n, fiveTapMask a b c n = 1 := by
    rw [tsum_eq_sum (s := Finset.Icc (-2 : ℤ) 2) fun n hn => fiveTapMask_eq_zero hn]
    rw [show Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} by decide]
    simp [fiveTapMask]
    linarith
  refine (classical_kernels_no_exact_cascade_masks hh).2.2 _ hfin hnn hsum fun x hx => ?_
  -- the mass at `h * n` is at least the weight at `n`; a point mass carries both `±h`
  have key : ∀ n : ℤ, ENNReal.ofReal (fiveTapMask a b c n) ≤
      gridLaw h (fiveTapMask a b c) {h * n} := by
    intro n
    rw [gridLaw, Measure.sum_apply _ (measurableSet_singleton _)]
    refine le_trans ?_ (ENNReal.le_tsum n)
    simp
  have h1 := key 1
  have h2 := key (-1)
  rw [hx] at h1 h2
  simp only [fiveTapMask, hb'] at h1 h2
  norm_num at h1 h2
  have hq : ¬ ENNReal.ofReal (1 / 4 : ℝ) ≤ 0 := by
    rw [not_le, ENNReal.ofReal_pos]
    norm_num
  have hx1 : x = h := by
    by_contra hne
    rw [Pi.single_apply, if_neg hne] at h1
    exact hq h1
  have hx2 : x = -h := by
    by_contra hne
    rw [Pi.single_apply, if_neg hne] at h2
    exact hq h2
  linarith

/-- **`prop:classical-kernels-no-exact-cascade`, the pyramids.** For such `w` and every `q > 1`, no
family satisfying (A1)–(A7) has the octave steps `μ_{qⁿ,qⁿ⁺¹} = T_{qⁿ} w`. -/
theorem classical_kernels_no_exact_cascade_pyramid (w : Measure ℝ) [IsProbabilityMeasure w]
    (hbdd : ∃ R : ℝ, w {x | R < |x|} = 0) (hnp : ∀ x : ℝ, w ≠ Measure.dirac x) {q : ℝ}
    (hq : 1 < q) :
    ¬ ∃ (Fam : PreCascadeCore) (μ : ℝ → ℝ → Measure ℝ), IsPositive Fam.Φ ∧
      IsKernelFamily Fam.Φ μ ∧ ∀ n : ℤ, μ (q ^ n) (q ^ (n + 1)) = gridLadderStep q w n := by
  rintro ⟨Fam, μ, hpos, hμ, hsteps⟩
  have h0 := hsteps 0
  simp only [zpow_zero, zero_add, zpow_one, gridLadderStep, one_mul, Measure.map_id'] at h0
  exact (classical_kernels_no_exact_cascade w hbdd hnp).2 Fam μ hpos hμ 1 q zero_le_one hq.le h0

end Pyramids
