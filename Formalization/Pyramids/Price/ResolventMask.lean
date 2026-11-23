/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Price.ExactMasks
import Pyramids.Price.FrameMatern
import Pyramids.Pyramid.WhatDoesNotLiftChain

/-!
# `prop:resolvent-masks-exact`(1)–(3): the resolvent masks are exact

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:resolvent-masks-exact`. Wave 3h:
`resolvent_masks_exact_1`, `_2` and `_3` moved here from `PyramidsSkeleton.Ch05Price`, unchanged
in name and conclusion. Dropped on 2026-11-15, a strengthening: `_1` no longer takes `hfin` (the
finite support of `σ` is read only by the logarithmic moment of (2)), and `_3` no longer takes the
hypothesis `RΓ = Γ` of its last clause (the status line of the node already says that the proof
does not read it).

## The route

* **The transform** of the countable mixture `w = ∑ (1-p)p^k σ^{*k}` is the series of the
  transforms (`integral_sum_measure`), a geometric series in `pσ̂` (`charFun_resolventMask`).
* **The logarithm series.** `σ` is symmetric, so `σ̂ = z` is real, `|z| ≤ 1`, and
  `∑_{k ≥ 1} (p^k/k)(1 - z^k) = log(1 - pz) - log(1 - p)` is two real logarithm series
  (`Real.hasSum_pow_div_log_of_abs_lt_one`); no complex logarithm is needed. The integral of
  `1 - cos⟨ω,·⟩` against `ν_w` is that series: the restriction to `{0}ᶜ` drops a zero of the
  integrand, the sum of measures is a series of integrals, and `∫(1 - cos) dσ^{*k} = 1 - z^k`.
  So `w` has the symmetric data `(0, ν_w)`, which gives infinite divisibility and the Lévy
  measure (A39 through `lem:family-structure` and `prop:grid-pyramid-not-isotropic`), and `w` is
  the compound Poisson law of `ν_w` by the uniqueness of the transform.
* **(2).** `w^{*γ}` has the data `(0, γν_w)`; `log₊|x + y| ≤ log₊|x| + log₊|y| + log 2` gives
  `∫ log₊ dσ^{*k} ≤ k(L + log 2)`, `L := ∫ log₊ dσ`, so `∫ log₊|x| ν_w(dx) ≤ (L + log 2) ∑ p^k < ∞`
  (since 2026-11-23 under a logarithmic moment of `σ`, where finite support was assumed, and the
  ball of radius `kR` carried `σ^{*k}`); and `w^{*γ} ≠ δ₀` because its transform is
  `((1-p)/(1-pz))^γ < 1` where `σ̂ = z < 1`. Exactness is `prop:ladder-knot-kernel`(2) through
  `prop:exact-masks`'s `exact_of_symData_moment`; the knot kernel is the product formula.
* **(3).** `w^{*γ}` is a mask on `Γ` whose atoms contain those of `σ`
  (`(μ ∗ ν){x + y} ≥ μ{x}ν{y}`), so `prop:grid-pyramid-not-isotropic`(2) applies; a symmetry
  `R` of `σ` fixes `σ̂`, hence `ŵ`, every partial product, the knot kernel and its dilates.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (convPow)
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace Matrix

variable {d : ℕ}

/-! ## Convolution powers on `ℝ^d` -/

instance isProbabilityMeasure_convPow_Rd (σ : Measure (Rd d)) [IsProbabilityMeasure σ]
    (n : ℕ) : IsProbabilityMeasure (convPow σ n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac 0); infer_instance
  | succ n ih => haveI := ih; change IsProbabilityMeasure (convPow σ n ∗ σ); infer_instance

/-- A convolution power of a symmetric law is symmetric. -/
theorem convPow_map_neg (σ : Measure (Rd d)) [IsFiniteMeasure σ]
    (hs : σ.map (fun x => -x) = σ) (n : ℕ) :
    (convPow σ n).map (fun x => -x) = convPow σ n := by
  have hL : (⇑(-ContinuousLinearMap.id ℝ (Rd d)) : Rd d → Rd d) = fun x => -x := by
    funext x
    simp
  have h := convPow_map_clm (-ContinuousLinearMap.id ℝ (Rd d)) σ n
  rw [hL, hs] at h
  exact h.symm

/-- **A convolution is carried by `A + B`**, for measurable targets. -/
theorem conv_compl_null_Rd {A B C : Set (Rd d)} (hC : MeasurableSet C)
    (hadd : ∀ x ∈ A, ∀ y ∈ B, x + y ∈ C) {μ ν : Measure (Rd d)} [SFinite μ] [SFinite ν]
    (hμ : μ Aᶜ = 0) (hν : ν Bᶜ = 0) : (μ ∗ ν) Cᶜ = 0 := by
  rw [Measure.conv, Measure.map_apply measurable_add hC.compl]
  refine measure_mono_null (t := (Aᶜ ×ˢ univ) ∪ (univ ×ˢ Bᶜ)) (fun p hp => ?_)
    (measure_union_null ?_ ?_)
  · by_contra hc
    simp only [mem_union, mem_prod, mem_compl_iff, mem_univ, and_true, true_and, not_or,
      not_not] at hc
    exact hp (hadd _ hc.1 _ hc.2)
  · rw [Measure.prod_prod, hμ, zero_mul]
  · rw [Measure.prod_prod, hν, mul_zero]

/-- A convolution power of a law carried by an additively closed measurable set containing `0`
is carried by it. -/
theorem convPow_compl_null {S : Set (Rd d)} (hS : MeasurableSet S) (h0 : (0 : Rd d) ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (σ : Measure (Rd d)) [IsFiniteMeasure σ]
    (hσ : σ Sᶜ = 0) (n : ℕ) : convPow σ n Sᶜ = 0 := by
  induction n with
  | zero =>
    change Measure.dirac 0 Sᶜ = 0
    rw [Measure.dirac_apply' _ hS.compl,
      indicator_of_notMem (show (0 : Rd d) ∉ Sᶜ from fun h => h h0)]
  | succ n ih =>
    haveI := ScaleSpace.isFiniteMeasure_convPow_Rd σ n
    exact conv_compl_null_Rd hS hadd ih hσ

/-- **`σ^{*n}` is carried by the ball of radius `nR`** when `σ` is carried by that of radius `R`. -/
theorem convPow_ball_null {R : ℝ} (σ : Measure (Rd d)) [IsFiniteMeasure σ]
    (hσ : σ (Metric.closedBall 0 R)ᶜ = 0) (n : ℕ) :
    convPow σ n (Metric.closedBall 0 (n * R))ᶜ = 0 := by
  induction n with
  | zero =>
    change Measure.dirac 0 _ = 0
    rw [Measure.dirac_apply' _ Metric.isClosed_closedBall.measurableSet.compl,
      indicator_of_notMem (show (0 : Rd d) ∉ (Metric.closedBall 0 ((0 : ℕ) * R))ᶜ from
        fun h => h (by simp))]
  | succ n ih =>
    haveI := ScaleSpace.isFiniteMeasure_convPow_Rd σ n
    refine conv_compl_null_Rd Metric.isClosed_closedBall.measurableSet (fun x hx y hy => ?_) ih
      hσ
    rw [mem_closedBall_zero_iff] at hx hy ⊢
    calc ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
      _ ≤ n * R + R := add_le_add hx hy
      _ = ((n + 1 : ℕ) : ℝ) * R := by push_cast; ring

/-- **`(μ ∗ ν){x + y} ≥ μ{x} ν{y}`.** -/
theorem conv_singleton_ge (μ ν : Measure (Rd d)) [SFinite μ] [SFinite ν] (x y : Rd d) :
    μ {x} * ν {y} ≤ (μ ∗ ν) {x + y} := by
  rw [Measure.conv, Measure.map_apply measurable_add (measurableSet_singleton _),
    ← Measure.prod_prod]
  exact measure_mono fun p hp => by
    simp only [mem_prod, mem_singleton_iff] at hp
    simp [hp.1, hp.2]

/-! ## The resolvent mask: probability and transform -/

section Resolvent

variable {σ : Measure (Rd d)} {p : ℝ}

theorem resolventMask_apply (p : ℝ) (σ : Measure (Rd d)) {s : Set (Rd d)} (hs : MeasurableSet s) :
    resolventMask p σ s = ∑' k, ENNReal.ofReal ((1 - p) * p ^ k) * convPow σ k s := by
  rw [resolventMask, Measure.sum_apply _ hs]
  rfl

theorem isProbabilityMeasure_resolventMask [IsProbabilityMeasure σ] (hp0 : 0 ≤ p) (hp1 : p < 1) :
    IsProbabilityMeasure (resolventMask p σ) := by
  constructor
  rw [resolventMask_apply p σ MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by linarith) (pow_nonneg hp0 k))
    ((summable_geometric_of_lt_one hp0 hp1).mul_left _), tsum_mul_left,
    tsum_geometric_of_lt_one hp0 hp1, mul_inv_cancel₀ (by linarith), ENNReal.ofReal_one]

/-- **The transform of the mixture**: `ŵ = (1-p)/(1 - pσ̂)`. -/
theorem charFun_resolventMask [IsProbabilityMeasure σ] (hp0 : 0 ≤ p) (hp1 : p < 1)
    (ω : Rd d) :
    charFun (resolventMask p σ) ω = ((1 - p : ℝ) : ℂ) / (1 - (p : ℂ) * charFun σ ω) := by
  haveI := isProbabilityMeasure_resolventMask (σ := σ) hp0 hp1
  have hint : Integrable (fun x : Rd d => Complex.exp (↑⟪x, ω⟫ * Complex.I))
      (resolventMask p σ) :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply, resolventMask, integral_sum_measure hint]
  have hz : ‖(p : ℂ) * charFun σ ω‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp0]
    calc p * ‖charFun σ ω‖ ≤ p * 1 := mul_le_mul_of_nonneg_left (norm_charFun_le_one ω) hp0
      _ < 1 := by linarith
  have e : ∀ k : ℕ, ∫ x, Complex.exp (↑⟪x, ω⟫ * Complex.I)
      ∂(ENNReal.ofReal ((1 - p) * p ^ k) • convPow σ k) =
      ((1 - p : ℝ) : ℂ) * ((p : ℂ) * charFun σ ω) ^ k := fun k => by
    have h1p : 0 ≤ 1 - p := by linarith
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), ← charFun_apply,
      charFun_convPow, Complex.real_smul]
    push_cast
    ring
  simp_rw [e]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hz, div_eq_mul_inv]

/-! ## The Lévy measure -/

/-- **`∑_{k ≥ 1} (p^k/k) σ^{*k}`**, before the restriction to `{0}ᶜ`. -/
noncomputable def resolventSeries (p : ℝ) (σ : Measure (Rd d)) : Measure (Rd d) :=
  Measure.sum fun k : ℕ => ENNReal.ofReal (p ^ (k + 1) / ((k : ℝ) + 1)) • convPow σ (k + 1)

theorem resolventLevy_eq (p : ℝ) (σ : Measure (Rd d)) :
    resolventLevy p σ = (resolventSeries p σ).restrict {0}ᶜ := rfl

theorem resolventSeries_apply (p : ℝ) (σ : Measure (Rd d)) {s : Set (Rd d)}
    (hs : MeasurableSet s) : resolventSeries p σ s =
      ∑' k : ℕ, ENNReal.ofReal (p ^ (k + 1) / ((k : ℝ) + 1)) * convPow σ (k + 1) s := by
  rw [resolventSeries, Measure.sum_apply _ hs]
  rfl

/-- `∑_{k ≥ 1} p^k/k = log(1/(1-p))`. -/
theorem hasSum_resolvent_mass (hp0 : 0 ≤ p) (hp1 : p < 1) :
    HasSum (fun k : ℕ => p ^ (k + 1) / ((k : ℝ) + 1)) (Real.log (1 / (1 - p))) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := p) (by rw [abs_of_nonneg hp0]; exact hp1)
  rwa [one_div, Real.log_inv]

theorem resolventSeries_univ [IsProbabilityMeasure σ] (hp0 : 0 ≤ p) (hp1 : p < 1) :
    resolventSeries p σ univ = ENNReal.ofReal (Real.log (1 / (1 - p))) := by
  rw [resolventSeries_apply p σ MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
    (hasSum_resolvent_mass hp0 hp1).summable, (hasSum_resolvent_mass hp0 hp1).tsum_eq]

theorem isFiniteMeasure_resolventSeries [IsProbabilityMeasure σ] (hp0 : 0 ≤ p) (hp1 : p < 1) :
    IsFiniteMeasure (resolventSeries p σ) :=
  ⟨by rw [resolventSeries_univ hp0 hp1]; exact ENNReal.ofReal_lt_top⟩

theorem isFiniteMeasure_resolventLevy [IsProbabilityMeasure σ] (hp0 : 0 ≤ p) (hp1 : p < 1) :
    IsFiniteMeasure (resolventLevy p σ) := by
  haveI := isFiniteMeasure_resolventSeries (σ := σ) hp0 hp1
  rw [resolventLevy_eq]
  infer_instance

theorem resolventLevy_univ_le [IsProbabilityMeasure σ] (hp0 : 0 ≤ p) (hp1 : p < 1) :
    resolventLevy p σ univ ≤ ENNReal.ofReal (Real.log (1 / (1 - p))) := by
  rw [resolventLevy_eq, Measure.restrict_apply_univ, ← resolventSeries_univ (σ := σ) hp0 hp1]
  exact measure_mono (subset_univ _)

theorem resolventLevy_zero (p : ℝ) (σ : Measure (Rd d)) : resolventLevy p σ {0} = 0 := by
  rw [resolventLevy_eq, Measure.restrict_apply (measurableSet_singleton 0)]
  simp

theorem resolventLevy_symm [IsFiniteMeasure σ] (hs : σ.map (fun x => -x) = σ) :
    (resolventLevy p σ).map (fun x => -x) = resolventLevy p σ := by
  have hpre : (fun x : Rd d => -x) ⁻¹' ({0}ᶜ : Set (Rd d)) = {0}ᶜ := by
    ext x
    simp
  have hser : (resolventSeries p σ).map (fun x => -x) = resolventSeries p σ := by
    rw [resolventSeries, Measure.map_sum measurable_neg.aemeasurable]
    congr 1
    funext k
    rw [Measure.map_smul, convPow_map_neg σ hs]
  rw [resolventLevy_eq]
  nth_rewrite 1 [← hpre]
  rw [← Measure.restrict_map measurable_neg (measurableSet_singleton 0).compl, hser]

/-- **`ν_w` is carried by `Γ ∖ {0}`.** -/
theorem resolventLevy_carrier [IsFiniteMeasure σ] {S : Set (Rd d)} (hS : MeasurableSet S)
    (h0 : (0 : Rd d) ∈ S) (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (hσ : σ Sᶜ = 0) :
    resolventLevy p σ (S \ {0})ᶜ = 0 := by
  rw [resolventLevy_eq, Measure.restrict_apply (hS.diff (measurableSet_singleton 0)).compl]
  refine measure_mono_null (t := Sᶜ) (fun x hx => ?_) ?_
  · exact fun hxS => hx.1 ⟨hxS, hx.2⟩
  · rw [resolventSeries_apply p σ hS.compl]
    simp [convPow_compl_null hS h0 hadd σ hσ]

/-! ## The logarithm series -/

/-- `∫(1 - cos⟨ω,·⟩) dσ^{*n} = 1 - z^n` for symmetric `σ` with `σ̂(ω) = z`. -/
theorem integral_one_sub_cos_convPow [IsProbabilityMeasure σ] (hs : σ.map (fun x => -x) = σ)
    (n : ℕ) (ω : Rd d) {z : ℝ} (hz : charFun σ ω = (z : ℂ)) :
    ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂(convPow σ n) = 1 - z ^ n := by
  have h1 := charFun_of_symm (convPow σ n) (convPow_map_neg σ hs n) ω
  rw [charFun_convPow, hz, ← Complex.ofReal_pow] at h1
  have h2 : z ^ n = ∫ x, Real.cos ⟪x, ω⟫ ∂(convPow σ n) := Complex.ofReal_injective h1
  have hint : Integrable (fun x : Rd d => Real.cos ⟪x, ω⟫) (convPow σ n) :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hc : ∀ x : Rd d, ⟪ω, x⟫ = ⟪x, ω⟫ := fun x => real_inner_comm x ω
  simp_rw [hc]
  rw [integral_sub (integrable_const 1) hint, h2]
  simp

/-- **The integral against `ν_w`** is the series `∑_{k ≥ 1} (p^k/k)(1 - z^k)`. -/
theorem integral_resolventLevy [IsProbabilityMeasure σ] (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hs : σ.map (fun x => -x) = σ) (ω : Rd d) {z : ℝ} (hz : charFun σ ω = (z : ℂ)) :
    ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂(resolventLevy p σ) =
      ∑' k : ℕ, p ^ (k + 1) / ((k : ℝ) + 1) * (1 - z ^ (k + 1)) := by
  haveI := isFiniteMeasure_resolventSeries (σ := σ) hp0 hp1
  rw [resolventLevy_eq, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    simp only [mem_compl_iff, mem_singleton_iff, not_not] at hx
    simp [hx]]
  have hint : Integrable (fun x : Rd d => 1 - Real.cos ⟪ω, x⟫) (resolventSeries p σ) :=
    Integrable.of_bound (by fun_prop) 2 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [Real.cos_le_one ⟪ω, x⟫, Real.neg_one_le_cos ⟪ω, x⟫])
  rw [resolventSeries] at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr fun k => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    integral_one_sub_cos_convPow hs (k + 1) ω hz, smul_eq_mul]

/-- **The logarithm series**: `∑_{k ≥ 1} (p^k/k)(1 - z^k) = log(1 - pz) - log(1 - p)`. -/
theorem hasSum_resolvent_log (hp0 : 0 ≤ p) (hp1 : p < 1) {z : ℝ} (hz : |z| ≤ 1) :
    HasSum (fun k : ℕ => p ^ (k + 1) / ((k : ℝ) + 1) * (1 - z ^ (k + 1)))
      (Real.log (1 - p * z) - Real.log (1 - p)) := by
  have h1 := Real.hasSum_pow_div_log_of_abs_lt_one (x := p) (by rw [abs_of_nonneg hp0]; exact hp1)
  have hpz : |p * z| < 1 := by
    rw [abs_mul, abs_of_nonneg hp0]
    calc p * |z| ≤ p * 1 := mul_le_mul_of_nonneg_left hz hp0
      _ < 1 := by linarith
  have h3 := (Real.hasSum_pow_div_log_of_abs_lt_one hpz).neg.add h1
  rw [neg_neg, ← sub_eq_add_neg] at h3
  have e : (fun k : ℕ => p ^ (k + 1) / ((k : ℝ) + 1) * (1 - z ^ (k + 1))) =
      fun k : ℕ => -((p * z) ^ (k + 1) / ((k : ℝ) + 1)) + p ^ (k + 1) / ((k : ℝ) + 1) := by
    funext k
    rw [mul_pow]
    ring
  rw [e]
  exact h3

/-- A symmetric law has a real transform of modulus at most `1`. -/
theorem charFun_real_of_symm [IsProbabilityMeasure σ] (hs : σ.map (fun x => -x) = σ)
    (ω : Rd d) : ∃ z : ℝ, charFun σ ω = (z : ℂ) ∧ |z| ≤ 1 := by
  refine ⟨_, charFun_of_symm σ hs ω, ?_⟩
  have h := norm_charFun_le_one (μ := σ) ω
  rwa [charFun_of_symm σ hs ω, Complex.norm_real, Real.norm_eq_abs] at h

/-- **The data of the resolvent mask**: `(0, ν_w)`. -/
theorem exists_resolventData [IsProbabilityMeasure σ] (hs : σ.map (fun x => -x) = σ)
    (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃ D : SymLevyData d, D.A = 0 ∧ D.ν = resolventLevy p σ ∧ IsSymData (resolventMask p σ) D := by
  haveI := isFiniteMeasure_resolventLevy (σ := σ) hp0 hp1
  refine ⟨⟨0, resolventLevy p σ, Matrix.PosSemidef.zero, resolventLevy_zero p σ, ?_,
    resolventLevy_symm hs⟩, rfl, rfl, fun ω => ?_⟩
  · refine ne_top_of_le_ne_top (measure_ne_top (resolventLevy p σ) univ) ?_
    calc ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂resolventLevy p σ
        ≤ ∫⁻ _, 1 ∂resolventLevy p σ :=
          lintegral_mono fun x => ENNReal.ofReal_le_one.2 (min_le_right _ _)
      _ = resolventLevy p σ univ := lintegral_one
  · obtain ⟨z, hz, hz1⟩ := charFun_real_of_symm hs ω
    have hpz : 0 < 1 - p * z := by
      have : p * z ≤ p * |z| := mul_le_mul_of_nonneg_left (le_abs_self z) hp0
      nlinarith
    simp only [SymLevyData.exponent, pairExponent, quad_zero, zero_add]
    rw [charFun_resolventMask hp0 hp1, integral_resolventLevy hp0 hp1 hs ω hz,
      (hasSum_resolvent_log hp0 hp1 hz1).tsum_eq, neg_sub, Real.exp_sub,
      Real.exp_log (by linarith), Real.exp_log hpz, hz]
    push_cast
    rfl

/-! ## `prop:resolvent-masks-exact`(1) -/

/-- **`prop:resolvent-masks-exact`(1).** For a mask `σ` and `0 < p < 1`,
`w = (1-p) ∑ p^k σ^{*k}` is a probability with `ŵ = (1-p)/(1 - pσ̂)`; it is infinitely divisible,
the compound Poisson law of `ν_w`, the restriction of `∑_{k ≥ 1} (p^k/k) σ^{*k}` to `ℝ^d ∖ {0}`,
which is carried by `Γ ∖ {0}` and has mass at most `log(1/(1-p))`. The node reads it for `σ` of
finite support; the proof does not read it (dropped on 2026-11-15, a strengthening). -/
theorem resolvent_masks_exact_1 (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (σ : Measure (Rd d)) (hσ : IsLatticeMask (Γ : Set (Rd d)) σ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) :
    IsProbabilityMeasure (resolventMask p σ) ∧
      (∀ ω : Rd d, charFun (resolventMask p σ) ω =
        ((1 - p : ℝ) : ℂ) / (1 - (p : ℂ) * charFun σ ω)) ∧
      IsInfinitelyDivisible (resolventMask p σ) ∧
      HasLevyMeasure (resolventMask p σ) (resolventLevy p σ) ∧
      resolventMask p σ = compoundPoissonLaw (resolventLevy p σ) ∧
      resolventLevy p σ ((Γ : Set (Rd d)) \ {0})ᶜ = 0 ∧
      resolventLevy p σ univ ≤ ENNReal.ofReal (Real.log (1 / (1 - p))) := by
  obtain ⟨hprob, hs, -, hcarr⟩ := hσ
  haveI := hprob
  haveI := isProbabilityMeasure_resolventMask (σ := σ) hp0.le hp1
  haveI := isFiniteMeasure_resolventLevy (σ := σ) hp0.le hp1
  obtain ⟨D, hA, hν, hD⟩ := exists_resolventData (σ := σ) hs hp0.le hp1
  have hT := SymLevyData.hasTriplet hD
  have hΓ : MeasurableSet (Γ : Set (Rd d)) := (countable_lattice Γ).measurableSet
  refine ⟨inferInstance, charFun_resolventMask hp0.le hp1, isInfinitelyDivisible_of_hasTriplet hT,
    hν ▸ (hasLevyMeasure_of_symData hD).1, ?_,
    resolventLevy_carrier hΓ Γ.zero_mem (fun x hx y hy => Γ.add_mem hx hy) hcarr,
    resolventLevy_univ_le hp0.le hp1⟩
  change resolventMask p σ = cpLaw (resolventLevy p σ)
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_cpLaw_symm _ (resolventLevy_symm hs), hD ω, ← hν]
  simp [SymLevyData.exponent, pairExponent, hA, quad_zero]


/-! ## Symmetry, carrier and atoms of the mask -/

theorem resolventMask_map_neg [IsProbabilityMeasure σ] (hs : σ.map (fun x => -x) = σ) :
    (resolventMask p σ).map (fun x => -x) = resolventMask p σ := by
  rw [resolventMask, Measure.map_sum measurable_neg.aemeasurable]
  congr 1
  funext k
  rw [Measure.map_smul, convPow_map_neg σ hs]

theorem resolventMask_compl_null [IsFiniteMeasure σ] {S : Set (Rd d)} (hS : MeasurableSet S)
    (h0 : (0 : Rd d) ∈ S) (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (hσ : σ Sᶜ = 0) :
    resolventMask p σ Sᶜ = 0 := by
  rw [resolventMask_apply p σ hS.compl]
  simp [convPow_compl_null hS h0 hadd σ hσ]

theorem resolventMask_singleton_zero_ge (p : ℝ) (σ : Measure (Rd d)) :
    ENNReal.ofReal (1 - p) ≤ resolventMask p σ {0} := by
  rw [resolventMask_apply p σ (measurableSet_singleton 0)]
  calc ENNReal.ofReal (1 - p) = ENNReal.ofReal ((1 - p) * p ^ 0) * convPow σ 0 {0} := by
        change _ = _ * Measure.dirac 0 {0}
        simp
    _ ≤ _ := ENNReal.le_tsum (f := fun k => ENNReal.ofReal ((1 - p) * p ^ k) * convPow σ k {0}) 0

theorem resolventMask_singleton_ge (p : ℝ) (σ : Measure (Rd d)) [SFinite σ] (x : Rd d) :
    ENNReal.ofReal ((1 - p) * p) * σ {x} ≤ resolventMask p σ {x} := by
  rw [resolventMask_apply p σ (measurableSet_singleton x)]
  calc ENNReal.ofReal ((1 - p) * p) * σ {x} =
        ENNReal.ofReal ((1 - p) * p ^ 1) * convPow σ 1 {x} := by
        change _ = _ * (Measure.dirac 0 ∗ σ) {x}
        rw [Measure.dirac_zero_conv, pow_one]
    _ ≤ _ := ENNReal.le_tsum (f := fun k => ENNReal.ofReal ((1 - p) * p ^ k) * convPow σ k {x}) 1

theorem convPow_singleton_zero_ge (m : Measure (Rd d)) [IsFiniteMeasure m] (k : ℕ) :
    m {0} ^ k ≤ convPow m k {0} := by
  induction k with
  | zero =>
    rw [pow_zero]
    change 1 ≤ Measure.dirac (0 : Rd d) {0}
    simp
  | succ k ih =>
    haveI := ScaleSpace.isFiniteMeasure_convPow_Rd m k
    calc m {0} ^ (k + 1) = m {0} ^ k * m {0} := pow_succ _ _
      _ ≤ convPow m k {0} * m {0} := mul_le_mul_left ih _
      _ ≤ (convPow m k ∗ m) {0 + 0} := conv_singleton_ge _ _ 0 0
      _ = convPow m (k + 1) {0} := by rw [add_zero]; rfl

theorem convPow_singleton_ge (m : Measure (Rd d)) [IsFiniteMeasure m] (k : ℕ) (x : Rd d) :
    m {0} ^ k * m {x} ≤ convPow m (k + 1) {x} := by
  haveI := ScaleSpace.isFiniteMeasure_convPow_Rd m k
  calc m {0} ^ k * m {x} ≤ convPow m k {0} * m {x} :=
        mul_le_mul_left (convPow_singleton_zero_ge m k) _
    _ ≤ (convPow m k ∗ m) {0 + x} := conv_singleton_ge _ _ 0 x
    _ = convPow m (k + 1) {x} := by rw [zero_add]; rfl

/-- **Every atom of `σ` is an atom of `w^{*γ}`**, `γ ≥ 1`. -/
theorem convPow_resolventMask_atom [IsProbabilityMeasure σ] (hp0 : 0 < p) (hp1 : p < 1)
    {γ : ℕ} (hγ : 1 ≤ γ) {x : Rd d} (hx : σ {x} ≠ 0) :
    convPow (resolventMask p σ) γ {x} ≠ 0 := by
  haveI := isProbabilityMeasure_resolventMask (σ := σ) hp0.le hp1
  obtain ⟨k, rfl⟩ : ∃ k, γ = k + 1 := ⟨γ - 1, by omega⟩
  have h1p : 0 < 1 - p := by linarith
  refine ne_of_gt (lt_of_lt_of_le ?_ (convPow_singleton_ge _ k x))
  refine ENNReal.mul_pos (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 h1p)
    (resolventMask_singleton_zero_ge p σ)))) (ne_of_gt (lt_of_lt_of_le ?_
      (resolventMask_singleton_ge p σ x)))
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (mul_pos h1p hp0)).ne' hx |>.bot_lt

/-- **`w^{*γ} ≠ δ₀`**: its transform is `((1-p)/(1-pz))^γ < 1` where `σ̂ = z < 1`. -/
theorem convPow_resolventMask_ne_dirac [IsProbabilityMeasure σ]
    (hs : σ.map (fun x => -x) = σ) (hne : σ ≠ Measure.dirac 0) (hp0 : 0 < p) (hp1 : p < 1)
    {γ : ℕ} (hγ : 1 ≤ γ) : convPow (resolventMask p σ) γ ≠ Measure.dirac 0 := by
  haveI := isProbabilityMeasure_resolventMask (σ := σ) hp0.le hp1
  intro h
  obtain ⟨ω, hω⟩ : ∃ ω, charFun σ ω ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hne (eq_dirac_of_charFun_one hc)
  obtain ⟨z, hz, hz1⟩ := charFun_real_of_symm hs ω
  have hzlt : z < 1 := lt_of_le_of_ne (le_of_abs_le hz1) fun h1 => hω (by rw [hz, h1]; simp)
  have h1 := congrArg (fun m => charFun m ω) h
  rw [charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    charFun_convPow, charFun_resolventMask hp0.le hp1, hz] at h1
  have hpz : p * z < p := by nlinarith
  set r : ℝ := (1 - p) / (1 - p * z) with hr
  have hr0 : 0 < r := div_pos (by linarith) (by linarith)
  have hr1 : r < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hc : ((1 - p : ℝ) : ℂ) / (1 - (p : ℂ) * (z : ℂ)) = ((r : ℝ) : ℂ) := by
    rw [hr]
    push_cast
    rfl
  rw [hc, ← Complex.ofReal_pow] at h1
  have h2 : r ^ γ = 1 := by exact_mod_cast h1
  exact absurd h2 (pow_lt_one₀ hr0.le hr1 (by omega)).ne

/-! ## The data and the moment of `w^{*γ}` -/

/-- **`w^{*γ}` has the data `γ D`.** -/
theorem isSymData_convPow {m : Measure (Rd d)} [IsProbabilityMeasure m] {D : SymLevyData d}
    (hD : IsSymData m D) (γ : ℕ) :
    IsSymData (convPow m γ) (SymLevyData.zero.addSmul D γ) := fun ω => by
  rw [charFun_convPow, hD ω, SymLevyData.addSmul_exponent, SymLevyData.zero_exponent, zero_add,
    max_eq_left (Nat.cast_nonneg γ), ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2
  ring

/-- `log₊ r ≤ r` for `r ≥ 0`. -/
theorem posLog_le_self {r : ℝ} (hr : 0 ≤ r) : Real.posLog r ≤ r :=
  max_le hr (Real.log_le_self hr)

/-- **The logarithmic moment of `ν_w`** when `σ` is carried by a ball: `σ^{*k}` is carried by the
ball of radius `kR`, so the moment is at most `∑ p^k R`. -/
theorem lintegral_posLog_resolventLevy [IsProbabilityMeasure σ] (hp0 : 0 ≤ p) (hp1 : p < 1)
    {R : ℝ} (hR : 0 ≤ R) (hσR : σ (Metric.closedBall 0 R)ᶜ = 0) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(resolventLevy p σ) < ⊤ := by
  have hle : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(convPow σ n) ≤
      ENNReal.ofReal (n * R) := by
    intro n
    calc ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(convPow σ n)
        ≤ ∫⁻ _, ENNReal.ofReal (n * R) ∂(convPow σ n) := by
          refine lintegral_mono_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 (convPow_ball_null σ hσR n)] with x hx
          have hx' : ‖x‖ ≤ n * R := by
            rw [mem_compl_iff, not_not, mem_closedBall_zero_iff] at hx
            exact hx
          exact ENNReal.ofReal_le_ofReal ((posLog_le_self (norm_nonneg x)).trans hx')
      _ = ENNReal.ofReal (n * R) := by rw [lintegral_const, measure_univ, mul_one]
  have hsum : Summable fun k : ℕ => R * p ^ (k + 1) :=
    ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hp0 hp1)).mul_left R
  calc ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(resolventLevy p σ)
      ≤ ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(resolventSeries p σ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∑' k : ℕ, ENNReal.ofReal (p ^ (k + 1) / ((k : ℝ) + 1)) *
          ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(convPow σ (k + 1)) := by
        rw [resolventSeries, lintegral_sum_measure]
        simp_rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (p ^ (k + 1) / ((k : ℝ) + 1)) *
          ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * R) :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul_right (hle (k + 1)) _
    _ = ∑' k : ℕ, ENNReal.ofReal (R * p ^ (k + 1)) := by
        refine tsum_congr fun k => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        field_simp
    _ = ENNReal.ofReal (∑' k : ℕ, R * p ^ (k + 1)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- A law carried by a finite set is carried by a ball. -/
theorem exists_ball_of_finset {σ : Measure (Rd d)} (hfin : ∃ S : Finset (Rd d), σ (↑S)ᶜ = 0) :
    ∃ R : ℝ, 0 ≤ R ∧ σ (Metric.closedBall 0 R)ᶜ = 0 := by
  obtain ⟨S, hS⟩ := hfin
  refine ⟨∑ s ∈ S, ‖s‖, Finset.sum_nonneg fun s _ => norm_nonneg s,
    measure_mono_null (compl_subset_compl.2 fun s hs => ?_) hS⟩
  rw [mem_closedBall_zero_iff]
  exact Finset.single_le_sum (f := fun s => ‖s‖) (fun s _ => norm_nonneg s) hs

/-! ## The logarithmic moment of `ν_w` under a logarithmic moment of `σ`

Review round 3, s6-7.S6 (2026-11-23, a strengthening): (2) needs only `∫ log₊|x| σ(dx) < ∞`.
`log₊|x + y| ≤ log₊|x| + log₊|y| + log 2` (`Real.posLog_norm_add_le`) gives
`∫ log₊ dσ^{*n} ≤ n (L + log 2)`, so `∫ log₊ dν_w ≤ (L + log 2) ∑ p^k < ∞`. -/

/-- **The moment of a convolution**: `∫ log₊|x| d(μ ∗ σ) ≤ ∫ log₊ dμ + ∫ log₊ dσ + log 2` for
probability laws. -/
theorem lintegral_posLog_conv_le (μ σ : Measure (Rd d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure σ] :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(μ ∗ σ) ≤
      ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂μ + ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂σ +
        ENNReal.ofReal (Real.log 2) := by
  have hf : Measurable fun x : Rd d => ENNReal.ofReal (Real.posLog ‖x‖) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  rw [Measure.conv, lintegral_map hf measurable_add]
  calc ∫⁻ z, ENNReal.ofReal (Real.posLog ‖z.1 + z.2‖) ∂(μ.prod σ)
      ≤ ∫⁻ z, (ENNReal.ofReal (Real.posLog ‖z.1‖) + ENNReal.ofReal (Real.posLog ‖z.2‖)) +
          ENNReal.ofReal (Real.log 2) ∂(μ.prod σ) := by
        refine lintegral_mono fun z => ?_
        rw [← ENNReal.ofReal_add Real.posLog_nonneg Real.posLog_nonneg,
          ← ENNReal.ofReal_add (add_nonneg Real.posLog_nonneg Real.posLog_nonneg) hl2]
        exact ENNReal.ofReal_le_ofReal (Real.posLog_norm_add_le z.1 z.2)
    _ = ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂μ + ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂σ +
          ENNReal.ofReal (Real.log 2) := by
        have h1 : ∫⁻ z, ENNReal.ofReal (Real.posLog ‖z.1‖) ∂(μ.prod σ) =
            ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂μ := by
          rw [← lintegral_map hf measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
        have h2 : ∫⁻ z, ENNReal.ofReal (Real.posLog ‖z.2‖) ∂(μ.prod σ) =
            ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂σ := by
          rw [← lintegral_map hf measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
        rw [lintegral_add_right _ measurable_const,
          lintegral_add_left (f := fun z : Rd d × Rd d => ENNReal.ofReal (Real.posLog ‖z.1‖))
            (hf.comp measurable_fst), h1, h2, lintegral_const, measure_univ, mul_one]

/-- **`∫ log₊ dσ^{*n} ≤ n (∫ log₊ dσ + log 2)`.** -/
theorem lintegral_posLog_convPow_le (σ : Measure (Rd d)) [IsProbabilityMeasure σ] (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(convPow σ n) ≤
      n * (∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂σ + ENNReal.ofReal (Real.log 2)) := by
  induction n with
  | zero =>
    change ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(Measure.dirac 0) ≤ _
    simp [lintegral_dirac]
  | succ n ih =>
    change ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(convPow σ n ∗ σ) ≤ _
    refine (lintegral_posLog_conv_le (convPow σ n) σ).trans ?_
    rw [add_assoc, Nat.cast_succ, add_mul, one_mul]
    exact add_le_add_left ih _

/-- **The logarithmic moment of `ν_w`** under a logarithmic moment of `σ`:
`∫ log₊ dν_w ≤ (∫ log₊ dσ + log 2) ∑_{k ≥ 1} p^k < ∞`. -/
theorem lintegral_posLog_resolventLevy_of_moment [IsProbabilityMeasure σ] (hp0 : 0 ≤ p)
    (hp1 : p < 1) (hlog : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂σ < ⊤) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(resolventLevy p σ) < ⊤ := by
  set L := ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂σ + ENNReal.ofReal (Real.log 2) with hL
  have hLt : L < ⊤ := ENNReal.add_lt_top.2 ⟨hlog, ENNReal.ofReal_lt_top⟩
  have hsum : Summable fun k : ℕ => p ^ (k + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hp0 hp1)
  calc ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(resolventLevy p σ)
      ≤ ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(resolventSeries p σ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∑' k : ℕ, ENNReal.ofReal (p ^ (k + 1) / ((k : ℝ) + 1)) *
          ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(convPow σ (k + 1)) := by
        rw [resolventSeries, lintegral_sum_measure]
        simp_rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (p ^ (k + 1) / ((k : ℝ) + 1)) * (((k + 1 : ℕ) : ℝ≥0∞) * L) :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul_right (lintegral_posLog_convPow_le σ (k + 1)) _
    _ = ∑' k : ℕ, ENNReal.ofReal (p ^ (k + 1)) * L := by
        refine tsum_congr fun k => ?_
        rw [← mul_assoc]
        congr 1
        rw [show ((k + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((k : ℝ) + 1) by
          rw [← ENNReal.ofReal_natCast]; push_cast; rfl, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ = ENNReal.ofReal (∑' k : ℕ, p ^ (k + 1)) * L := by
        rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hLt

/-- **A law carried by a finite set has a logarithmic moment.** -/
theorem lintegral_posLog_lt_top_of_finset {σ : Measure (Rd d)} [IsFiniteMeasure σ]
    (hfin : ∃ S : Finset (Rd d), σ (↑S)ᶜ = 0) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂σ < ⊤ := by
  obtain ⟨R, -, hR⟩ := exists_ball_of_finset hfin
  calc ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂σ ≤ ∫⁻ _, ENNReal.ofReal (Real.posLog R) ∂σ := by
        refine lintegral_mono_ae ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hR] with x hx
        rw [mem_compl_iff, not_not, mem_closedBall_zero_iff] at hx
        exact ENNReal.ofReal_le_ofReal (Real.posLog_le_posLog (norm_nonneg x) hx)
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top σ univ)

/-! ## `prop:resolvent-masks-exact`(2) -/

/-- **`prop:resolvent-masks-exact`(2).** For every `q > 1` and integer `γ ≥ 1` the grid pyramid of
`(w^{*γ}, q)` is exact, and every carrying family has `μ̂_1 = ∏_{m ≥ 1} ŵ(q^{-m}·)^γ`.
Strengthened on 2026-11-23 (review round 3, s6-7.S6): `σ` needs a logarithmic moment, where it
was required to have finite support (`lintegral_posLog_lt_top_of_finset` recovers that case). -/
theorem resolvent_masks_exact_2 (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (σ : Measure (Rd d)) (hσ : IsLatticeMask (Γ : Set (Rd d)) σ)
    (hlog : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂σ < ⊤) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {q : ℝ} (hq : 1 < q) {γ : ℕ} (hγ : 1 ≤ γ) :
    IsExactLatticePyramid q (convPow (resolventMask p σ) γ) ∧
      ∀ μ : ℝ → ℝ → Measure (Rd d), CarriesLatticeLadder q (convPow (resolventMask p σ) γ) μ →
        ∀ ω : Rd d, Tendsto (fun M : ℕ => ∏ m ∈ Finset.range M,
            charFun (resolventMask p σ) ((q ^ (-((m : ℤ) + 1))) • ω) ^ γ)
          atTop (𝓝 (charFun (μ 0 1) ω)) := by
  obtain ⟨hprob, hs, hne, -⟩ := hσ
  haveI := hprob
  haveI := isProbabilityMeasure_resolventMask (σ := σ) hp0.le hp1
  have hd := one_le_of_ne_dirac hne
  refine ⟨?_, fun μ hμ ω => (hμ.product hd ω).1.congr fun M => by
    simp only [ladderProd, charFun_convPow]⟩
  obtain ⟨D, -, hν, hD⟩ := exists_resolventData (σ := σ) hs hp0.le hp1
  refine exact_of_symData_moment hd hq (convPow_resolventMask_ne_dirac hs hne hp0 hp1 hγ)
    (isSymData_convPow hD γ) ?_
  simp only [SymLevyData.addSmul, SymLevyData.zero, zero_add]
  rw [lintegral_smul_measure, hν]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lintegral_posLog_resolventLevy_of_moment hp0.le hp1 hlog)

/-! ## `prop:resolvent-masks-exact`(3) -/

/-- **`prop:resolvent-masks-exact`(3).** If `d ≥ 2` and `supp σ` spans `ℝ^d`, no kernel `μ_t`,
`t > 0`, of a family carrying the ladder of `(w^{*γ}, q)` is invariant under `SO(d)`; at every
knot the symmetry group is finite and contains every `R ∈ O(d)` with `R_*σ = σ`. The node reads it
for `σ` of finite support, `q > 1` and `R` with `RΓ = Γ`; the proof reads none of the three (`q > 1`
is part of carrying the ladder; dropped on 2026-11-15, a strengthening). -/
theorem resolvent_masks_exact_3 (hd : 2 ≤ d) (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ]
    [IsZLattice ℝ Γ] (σ : Measure (Rd d)) (hσ : IsLatticeMask (Γ : Set (Rd d)) σ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hspan : Submodule.span ℝ {x : Rd d | σ {x} ≠ 0} = ⊤) {q : ℝ} {γ : ℕ}
    (hγ : 1 ≤ γ) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : CarriesLatticeLadder q (convPow (resolventMask p σ) γ) μ) :
    (∀ t : ℝ, 0 < t → ¬ IsSORotationInvariant (μ 0 t)) ∧
      ∀ n : ℤ, (symmetryGroup (μ 0 (q ^ n))).Finite ∧
        ∀ R ∈ orthSet d, push R σ = σ → R ∈ symmetryGroup (μ 0 (q ^ n)) := by
  obtain ⟨hprob, hs, hne, hcarr⟩ := hσ
  haveI := hprob
  haveI := isProbabilityMeasure_resolventMask (σ := σ) hp0.le hp1
  have hΓ : MeasurableSet (Γ : Set (Rd d)) := (countable_lattice Γ).measurableSet
  have hadd : ∀ x ∈ (Γ : Set (Rd d)), ∀ y ∈ (Γ : Set (Rd d)), x + y ∈ (Γ : Set (Rd d)) :=
    fun x hx y hy => Γ.add_mem hx hy
  have hmask : IsLatticeMask (Γ : Set (Rd d)) (convPow (resolventMask p σ) γ) :=
    ⟨inferInstance, convPow_map_neg _ (resolventMask_map_neg hs) γ,
      convPow_resolventMask_ne_dirac hs hne hp0 hp1 hγ,
      convPow_compl_null hΓ Γ.zero_mem hadd _ (resolventMask_compl_null hΓ Γ.zero_mem hadd hcarr) γ⟩
  have hspan' : Submodule.span ℝ {x : Rd d | convPow (resolventMask p σ) γ {x} ≠ 0} = ⊤ :=
    top_le_iff.1 (hspan ▸ Submodule.span_mono fun x hx =>
      convPow_resolventMask_atom hp0 hp1 hγ hx)
  obtain ⟨h1, h2⟩ := grid_pyramid_not_isotropic_2 hd Γ _ hmask μ hμ
  have hq0 : 0 < q := by linarith [hμ.1]
  refine ⟨h1, fun n => ⟨h2 hspan' _ (zpow_pos hq0 n), fun R hR hRσ => ⟨hR, ?_⟩⟩⟩
  haveI := hμ.prob le_rfl zero_le_one
  haveI := hμ.prob le_rfl (zpow_pos hq0 n).le
  have hcn : ∀ ξ, charFun (μ 0 (q ^ n)) ξ = charFun (μ 0 1) ((q ^ n) • ξ) := fun ξ => by
    rw [hμ.zpow n, charFun_map_smul]
  rw [push_eq_iff_charFun, invariant_dilate_iff (zpow_ne_zero n hq0.ne') hcn R]
  have hσR := (push_eq_iff_charFun R).1 hRσ
  have hwR : ∀ ω, charFun (convPow (resolventMask p σ) γ) (lin Rᵀ ω) =
      charFun (convPow (resolventMask p σ) γ) ω := fun ω => by
    rw [charFun_convPow, charFun_convPow, charFun_resolventMask hp0.le hp1,
      charFun_resolventMask hp0.le hp1, hσR]
  have hd1 : 1 ≤ d := by omega
  intro ω
  have hP : ∀ M, ladderProd q (convPow (resolventMask p σ) γ) M (lin Rᵀ ω) =
      ladderProd q (convPow (resolventMask p σ) γ) M ω := fun M => by
    unfold ladderProd
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [← map_smul, hwR]
  have h3 := (hμ.product hd1 (lin Rᵀ ω)).1
  simp_rw [hP] at h3
  exact tendsto_nhds_unique h3 (hμ.product hd1 ω).1

end Resolvent

end Pyramids
