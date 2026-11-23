/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.ClassicalMoments
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# `prop:classical-pyramids-approximate`(3): the rescaled weights tend to the cubic B-spline

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:classical-pyramids-approximate`. Wave 3a:
`classical_pyramids_approximate_3` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in
statement and name.

## The route

The printed one. The transform of `T_{2^{-n}}W_n` at `ω` is `∏_{m=1}^{n} cos⁴(2^{-m}hω/2)`
(`charFun_equivWeight_binomial_rescaled`, the product of clause (1) read backwards), which tends to
`sinc(hω/2)⁴` by Viète's product (`tendsto_prod_cos`, `prop:equivalent-weights`(2)). That is the
transform of the cubic B-spline, and Lévy's continuity theorem (Mathlib's
`ProbabilityMeasure.tendsto_of_tendsto_charFun`) gives the weak convergence. The excess kurtosis is
`bspline4_excess_kurtosis`.

"Not Gaussian": weak limits are unique, so a Gaussian limit would be the cubic B-spline. Its
transform vanishes at `ω = 2π/h`, while a Gaussian transform `exp(imω - vω²/2)` vanishes nowhere.
This holds for every variance `v ≥ 0`, the point mass `v = 0` included.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (convPow)
open scoped Topology NNReal BoundedContinuousFunction

/-- **The transform of the rescaled weight**:
`(T_{2^{-n}}W_n)^(ω) = ∏_{m<n} cos⁴(hω/2 / 2^{m+1})`. -/
theorem charFun_equivWeight_binomial_rescaled (h : ℝ) (n : ℕ) (ω : ℝ) :
    charFun ((equivWeight 2 (gridLaw h binomialMask5) n).map fun x => x / 2 ^ n) ω =
      ((∏ m ∈ Finset.range n, Real.cos (h * ω / 2 / 2 ^ (m + 1)) ^ 4 : ℝ) : ℂ) := by
  haveI := isProbabilityMeasure_gridLaw_binomial h
  have hf : (fun x : ℝ => x / 2 ^ n) = fun x => (2 ^ n)⁻¹ * x := funext fun x => by
    rw [div_eq_inv_mul]
  rw [hf, charFun_map_mul, (equivWeight_charFun_real 2 _ n).2, Complex.ofReal_prod,
    ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [charFun_gridLaw_binomial, Complex.ofReal_pow]
  have hm' := Finset.mem_range.1 hm
  have hpow : (2 : ℝ) ^ n = 2 ^ (n - 1 - m) * 2 ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp
  rw [Complex.ofReal_pow]

/-- The transforms of the rescaled weights tend to `sinc(hω/2)⁴`. -/
theorem tendsto_charFun_equivWeight_binomial_rescaled (h ω : ℝ) :
    Tendsto (fun n : ℕ =>
        charFun ((equivWeight 2 (gridLaw h binomialMask5) n).map fun x => x / 2 ^ n) ω) atTop
      (𝓝 (((Real.sinc (h * ω / 2)) ^ 4 : ℝ) : ℂ)) := by
  simp_rw [charFun_equivWeight_binomial_rescaled, Finset.prod_pow]
  exact (Complex.continuous_ofReal.tendsto _).comp ((tendsto_prod_cos _).pow 4)

/-- **`T_{2^{-n}}W_n` converges weakly to the cubic B-spline.** -/
theorem tendsto_integral_equivWeight_binomial_rescaled {h : ℝ} (hh : 0 < h) (φ : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ =>
        ∫ x, φ x ∂((equivWeight 2 (gridLaw h binomialMask5) n).map fun x => x / 2 ^ n)) atTop
      (𝓝 (∫ x, φ x ∂(convPow (uniformInterval h) 4))) := by
  haveI := isProbabilityMeasure_gridLaw_binomial h
  haveI := isProbabilityMeasure_uniformInterval hh
  haveI := ScaleSpace.isProbabilityMeasure_convPow_real (uniformInterval h) 4
  have hP : ∀ n : ℕ, IsProbabilityMeasure
      ((equivWeight 2 (gridLaw h binomialMask5) n).map fun x => x / 2 ^ n) := fun n => by
    haveI := (equivWeight_charFun_real 2 (gridLaw h binomialMask5) n).1
    exact Measure.isProbabilityMeasure_map (measurable_div_const _).aemeasurable
  let μs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨_, hP n⟩
  let μ₀ : ProbabilityMeasure ℝ := ⟨convPow (uniformInterval h) 4, inferInstance⟩
  have hlim : Tendsto μs atTop (𝓝 μ₀) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun ω => ?_
    change Tendsto (fun n : ℕ =>
        charFun ((equivWeight 2 (gridLaw h binomialMask5) n).map fun x => x / 2 ^ n) ω) atTop
      (𝓝 (charFun (convPow (uniformInterval h) 4) ω))
    rw [charFun_convPow_real, charFun_uniformInterval hh, ← Complex.ofReal_pow]
    exact tendsto_charFun_equivWeight_binomial_rescaled h ω
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim φ

/-- A law whose integrals of all bounded continuous functions are those of a law with a vanishing
transform has that transform too: no Gaussian law is a weak limit of laws converging weakly to a
law whose transform vanishes somewhere. -/
theorem gaussianReal_ne_of_charFun_eq_zero {ν : Measure ℝ} [IsFiniteMeasure ν] {ω : ℝ}
    (hν : charFun ν ω = 0) (m : ℝ) (v : ℝ≥0) : ProbabilityTheory.gaussianReal m v ≠ ν := by
  intro heq
  rw [← heq, ProbabilityTheory.charFun_gaussianReal] at hν
  exact Complex.exp_ne_zero _ hν

/-! ## `prop:classical-pyramids-approximate`(3) -/

/-- **`prop:classical-pyramids-approximate`(3).** `T_{2^{-n}} W_n` converges weakly to the cubic
B-spline (transform `(sin(hω/2)/(hω/2))⁴`, excess kurtosis `-3/10`), and not to any Gaussian
law. -/
theorem classical_pyramids_approximate_3 {h : ℝ} (hh : 0 < h) :
    (∀ φ : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ =>
        ∫ x, φ x ∂((equivWeight 2 (gridLaw h binomialMask5) n).map fun x => x / 2 ^ n)) atTop
        (𝓝 (∫ x, φ x ∂(convPow (uniformInterval h) 4)))) ∧
      (∀ ω : ℝ, charFun (convPow (uniformInterval h) 4) ω =
        (((Real.sinc (h * ω / 2)) ^ 4 : ℝ) : ℂ)) ∧
      (∫ x, x ^ 4 ∂(convPow (uniformInterval h) 4) -
          3 * (∫ x, x ^ 2 ∂(convPow (uniformInterval h) 4)) ^ 2) /
          (∫ x, x ^ 2 ∂(convPow (uniformInterval h) 4)) ^ 2 = -(3 / 10) ∧
      ∀ (m : ℝ) (v : ℝ≥0), ¬ ∀ φ : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ =>
        ∫ x, φ x ∂((equivWeight 2 (gridLaw h binomialMask5) n).map fun x => x / 2 ^ n)) atTop
        (𝓝 (∫ x, φ x ∂(ProbabilityTheory.gaussianReal m v))) := by
  haveI := isProbabilityMeasure_uniformInterval hh
  haveI := ScaleSpace.isProbabilityMeasure_convPow_real (uniformInterval h) 4
  obtain ⟨-, hc, -⟩ := classical_pyramids_approximate_5 hh (m := 4) (by norm_num)
  refine ⟨tendsto_integral_equivWeight_binomial_rescaled hh, hc, bspline4_excess_kurtosis hh,
    fun m v hG => ?_⟩
  -- weak limits are unique: the Gaussian law would be the cubic B-spline
  have heq : ProbabilityTheory.gaussianReal m v = convPow (uniformInterval h) 4 :=
    ext_of_forall_integral_eq_of_IsFiniteMeasure fun φ =>
      tendsto_nhds_unique (hG φ) (tendsto_integral_equivWeight_binomial_rescaled hh φ)
  -- whose transform vanishes at `2π/h`
  have h0 := (classical_pyramids_approximate_5 hh (m := 4) (by norm_num)).2.2 1 one_ne_zero
  exact gaussianReal_ne_of_charFun_eq_zero h0 m v heq

end Pyramids
