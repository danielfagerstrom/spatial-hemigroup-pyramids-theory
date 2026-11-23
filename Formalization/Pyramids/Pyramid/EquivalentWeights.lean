/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Pyramid
import Pyramids.RecursionHelmholtz
import AffineHemigroup.CharFunSubspace
import AffineHemigroup.RationalSymbols
import AffineHemigroup.FrameFamilies

/-!
# `prop:equivalent-weights`: equivalent weights and the knot relation

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:equivalent-weights`. Phase 5, wave 1c.

(1) `W_n = w * D_q W_{n-1}`, so `W_n = D_q W_{n-1}` gives `ŵ · P = P` with
`P(ω) = ∏_{k=1}^{n-1} ŵ(q^k ω)`, continuous with `P(0) = 1`. So `ŵ = 1` on a ball about `0`, and
the affine export's `charFun_one_on_subspace` (at `H = ℝ^d`) makes `w = δ₀`. Neither the symmetry
of `w` nor `q > 1` is used.

(2) The binomial mask has `ŵ(ω) = cos⁴(hω/2)`, computed from its five point masses. Induction on
`sinc(2t) = sinc(t) cos(t)` gives `sinc x = sinc(x/2^M) ∏_{m<M} cos(x/2^{m+1})`, and
`sinc(x/2^M) → 1` gives Viète's product. The uniform law on `[-h/2, h/2]` has transform
`sinc(hω/2)`, so its fourfold convolution is a law `μ_1` with the transform of the node, and the
uniqueness of the transform makes it the only one. `D_2 μ_1 = μ_1 * w` is `sinc(2t)⁴ =
sinc(t)⁴ cos⁴(t)` at `t = hω/2`; on `hℤ^d` the transforms are products over the coordinates.
-/

namespace Pyramids

open AffineHemigroup MeasureTheory Set Filter
open scoped Topology ENNReal

variable {d : ℕ}

/-- A product over `List.range n` is the product over `Finset.range n`. -/
theorem list_prod_map_range {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih,
      Finset.prod_range_succ]; simp

/-- `W_n` is a probability measure with `Ŵ_n(ω) = ∏_{k<n} ŵ(q^k ω)`. -/
theorem equivWeight_charFun (q : ℝ) (w : Measure (Rd d)) [IsProbabilityMeasure w] (n : ℕ) :
    IsProbabilityMeasure (equivWeight q w n) ∧ ∀ ω : Rd d,
      charFun (equivWeight q w n) ω = ∏ k ∈ Finset.range n, charFun w ((q ^ k) • ω) := by
  have hl : ∀ μ ∈ (List.range n).map (fun k => w.map fun x => (q ^ k) • x),
      IsProbabilityMeasure μ := by
    intro μ hμ
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hμ
    exact Measure.isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
  obtain ⟨hp, hc⟩ := convList_charFun _ hl
  refine ⟨hp, fun ω => ?_⟩
  rw [equivWeight, hc, List.map_map, list_prod_map_range]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Function.comp_apply]
  exact charFun_map_smul _ _

/-- A probability measure whose transform is `1` near the origin is `δ₀`. -/
theorem eq_dirac_of_charFun_eq_one_near (w : Measure (Rd d)) [IsProbabilityMeasure w] {η : ℝ}
    (hη : 0 < η) (h1 : ∀ ω : Rd d, ‖ω‖ < η → charFun w ω = 1) : w = Measure.dirac 0 := by
  have h := (charFun_one_on_subspace w ⊤ η hη fun ω _ hω => h1 ω hω).2
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  have := h 0 ω Submodule.mem_top
  rw [zero_add] at this
  rw [this, charFun_dirac, charFun_zero]
  simp

/-- **`prop:equivalent-weights`(1).** For a law `w ≠ δ₀` and any real `q`,
`W_n ≠ D_q W_{n-1}` for `n ≥ 1`. Widened with the author's approval (wave 1c): the statement
typed at phase 4 also assumed `w` symmetric, `q > 1` and `n ≥ 2`, which the proof never used. The
blueprint states it for `q > 0`, where `D_q` is defined. -/
theorem equivalent_weights_1 (w : Measure (Rd d)) [IsProbabilityMeasure w]
    (hne : w ≠ Measure.dirac 0) (q : ℝ) {n : ℕ}
    (hn : 1 ≤ n) : equivWeight q w n ≠ (equivWeight q w (n - 1)).map (fun x => q • x) := by
  intro heq
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at heq
  obtain ⟨-, hn1⟩ := equivWeight_charFun q w (m + 1)
  obtain ⟨-, hm⟩ := equivWeight_charFun q w m
  -- the common factor `P(ω) = ∏_{k<m} ŵ(q^{k+1}ω)`
  set P : Rd d → ℂ := fun ω => ∏ k ∈ Finset.range m, charFun w ((q ^ (k + 1)) • ω) with hP
  have hrel : ∀ ω, charFun w ω * P ω = P ω := by
    intro ω
    have h : charFun (equivWeight q w (m + 1)) ω =
        charFun ((equivWeight q w m).map fun x => q • x) ω := by rw [heq]
    rw [charFun_map_smul, hn1, hm, Finset.prod_range_succ', pow_zero, one_smul] at h
    rw [mul_comm, h]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [smul_smul, pow_succ]
  have hPc : Continuous P := by
    refine continuous_finsetProd _ fun k _ => ?_
    exact continuous_charFun.comp (continuous_const_smul _)
  have hP0 : P 0 = 1 := by
    simp only [hP, smul_zero, charFun_zero, probReal_univ, Complex.ofReal_one,
      Finset.prod_const_one]
  have hev : ∀ᶠ ω in 𝓝 (0 : Rd d), P ω ≠ 0 := by
    have := hPc.continuousAt (x := 0)
    rw [ContinuousAt, hP0] at this
    exact this.eventually_ne one_ne_zero
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  apply hne
  refine eq_dirac_of_charFun_eq_one_near w hη fun ω hω => ?_
  have hPω : P ω ≠ 0 := hball (by simpa [dist_zero_right] using hω)
  have := hrel ω
  have h2 : (charFun w ω - 1) * P ω = 0 := by rw [sub_mul, this, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hPω


/-- The binomial mask vanishes off `{-2, …, 2}`. -/
theorem binomialMask5_eq_zero {n : ℤ} (hn : n ∉ Finset.Icc (-2 : ℤ) 2) : binomialMask5 n = 0 := by
  rw [binomialMask5, if_neg]
  rw [Finset.mem_Icc] at hn
  rw [abs_le]
  omega

/-- The binomial mask as a finite sum of point masses. -/
theorem gridLaw_binomial_eq (h : ℝ) :
    gridLaw h binomialMask5 = ∑ n ∈ Finset.Icc (-2 : ℤ) 2,
      ENNReal.ofReal (binomialMask5 n) • Measure.dirac (h * n) := by
  ext s hs
  rw [gridLaw, Measure.sum_apply _ hs, Measure.coe_finsetSum, Finset.sum_apply]
  refine tsum_eq_sum fun n hn => ?_
  rw [binomialMask5_eq_zero hn]
  simp

/-- The five values `[1, 4, 6, 4, 1]/16`. -/
theorem binomialMask5_vals : binomialMask5 (-2) = 1 / 16 ∧ binomialMask5 (-1) = 4 / 16 ∧
    binomialMask5 0 = 6 / 16 ∧ binomialMask5 1 = 4 / 16 ∧ binomialMask5 2 = 1 / 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [binomialMask5, Nat.choose]

/-- The binomial mask is a probability measure. -/
theorem isProbabilityMeasure_gridLaw_binomial (h : ℝ) :
    IsProbabilityMeasure (gridLaw h binomialMask5) := by
  constructor
  rw [gridLaw_binomial_eq]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  obtain ⟨h1, h2, h3, h4, h5⟩ := binomialMask5_vals
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by
    by_cases hn : n ∈ Finset.Icc (-2 : ℤ) 2
    · rw [binomialMask5]; split_ifs <;> positivity
    · rw [binomialMask5_eq_zero hn])]
  rw [show Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} by decide]
  simp [h1, h2, h3, h4, h5]
  norm_num


/-- `e^{2kyi} = (e^{yi})^{2k}`. -/
theorem exp_two_mul_eq (y : ℝ) (k : ℕ) :
    Complex.exp (((2 * k * y : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((y : ℂ) * Complex.I) ^ (2 * k) := by
  rw [← Complex.exp_nat_mul]; push_cast; ring_nf

/-- **`ŵ(ω) = cos⁴(hω/2)`** for the binomial mask on `hℤ`. -/
theorem charFun_gridLaw_binomial (h ω : ℝ) :
    charFun (gridLaw h binomialMask5) ω = (((Real.cos (h * ω / 2)) ^ 4 : ℝ) : ℂ) := by
  rw [gridLaw_binomial_eq, charFun_apply]
  rw [integral_finsetSum_measure (fun n _ => ?_)]
  swap
  · refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    exact integrable_dirac enorm_lt_top
  simp only [integral_smul_measure, integral_dirac]
  obtain ⟨h1, h2, h3, h4, h5⟩ := binomialMask5_vals
  rw [show Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have hexp : ∀ k : ℤ, Complex.exp (↑(inner ℝ (h * ↑k) ω) * Complex.I) =
      Complex.exp ((h * ω / 2 : ℝ) * Complex.I) ^ (2 * k) := by
    intro k
    rw [← Complex.exp_int_mul]
    congr 1
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  simp only [h1, h2, h3, h4, h5, hexp]
  set z := Complex.exp ((h * ω / 2 : ℝ) * Complex.I) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hcos : ((Real.cos (h * ω / 2) : ℝ) : ℂ) = (z + z⁻¹) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos, hz, ← Complex.exp_neg, neg_mul]
  rw [Complex.ofReal_pow, hcos]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 16),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 / 16),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6 / 16), Complex.real_smul]
  push_cast
  simp only [zpow_neg, zpow_ofNat]
  field_simp
  ring


/-- `sinc(2t) = sinc(t) cos(t)`. -/
theorem sinc_two_mul (t : ℝ) : Real.sinc (2 * t) = Real.sinc t * Real.cos t := by
  by_cases ht : t = 0
  · simp [ht]
  rw [Real.sinc_of_ne_zero ht, Real.sinc_of_ne_zero (mul_ne_zero two_ne_zero ht), Real.sin_two_mul]
  field_simp

/-- `sinc x = sinc(x/2^M) ∏_{m<M} cos(x/2^{m+1})`. -/
theorem sinc_eq_prod_cos (x : ℝ) (M : ℕ) :
    Real.sinc x = Real.sinc (x / 2 ^ M) * ∏ m ∈ Finset.range M, Real.cos (x / 2 ^ (m + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [ih, Finset.prod_range_succ, ← mul_assoc, mul_comm _ (Real.cos _), ← mul_assoc]
    congr 1
    rw [mul_comm, ← sinc_two_mul]
    congr 1
    rw [pow_succ]
    field_simp

/-- **Viète's product**: `∏_{m ≥ 1} cos(x/2^m) = sinc x`. -/
theorem tendsto_prod_cos (x : ℝ) :
    Tendsto (fun M : ℕ => ∏ m ∈ Finset.range M, Real.cos (x / 2 ^ (m + 1))) atTop
      (𝓝 (Real.sinc x)) := by
  have hs : Tendsto (fun M : ℕ => Real.sinc (x / 2 ^ M)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun M : ℕ => x / 2 ^ M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul x |>.congr fun M => by
          rw [one_div, inv_pow, div_eq_mul_inv]
    have := (Real.continuous_sinc.tendsto 0).comp h0
    rwa [Real.sinc_zero] at this
  have hev : ∀ᶠ M : ℕ in atTop, Real.sinc x / Real.sinc (x / 2 ^ M) =
      ∏ m ∈ Finset.range M, Real.cos (x / 2 ^ (m + 1)) := by
    filter_upwards [hs.eventually_ne one_ne_zero] with M hM
    rw [sinc_eq_prod_cos x M, mul_div_cancel_left₀ _ hM]
  have h1 := (tendsto_const_nhds (x := Real.sinc x)).div hs one_ne_zero
  rw [div_one] at h1
  exact h1.congr' hev


/-- The uniform law on `[-h/2, h/2]` is a probability measure. -/
theorem isProbabilityMeasure_uniformInterval {h : ℝ} (hh : 0 < h) :
    IsProbabilityMeasure (uniformInterval h) := by
  constructor
  rw [uniformInterval, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc,
    smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 hh.le)]
  rw [show h / 2 - -(h / 2) = h by ring, inv_mul_cancel₀ hh.ne', ENNReal.ofReal_one]

/-- The transform of the uniform law on `[-h/2, h/2]` is `sinc(hω/2)`. -/
theorem charFun_uniformInterval {h : ℝ} (hh : 0 < h) (ω : ℝ) :
    charFun (uniformInterval h) ω = ((Real.sinc (h * ω / 2) : ℝ) : ℂ) := by
  rw [charFun_apply, uniformInterval, integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), ENNReal.toReal_ofReal (inv_nonneg.2 hh.le)]
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hω : ω = 0
  · subst hω
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const]
    rw [Complex.real_smul, Complex.real_smul, zero_div, Real.sinc_zero]
    have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh.ne'
    push_cast
    field_simp
    ring
  have hc : (ω : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hω) Complex.I_ne_zero
  have hfun : (fun x : ℝ => Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I)) =
      fun x : ℝ => Complex.exp (((ω : ℂ) * Complex.I) * x) := by
    funext x; push_cast; ring_nf
  rw [hfun, integral_exp_mul_complex hc]
  have hne : h * ω / 2 ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hne, Complex.real_smul]
  push_cast
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh.ne'
  have hω0 : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hω
  rw [Complex.sin, show ↑ω * Complex.I * (↑h / 2) = (↑h * ↑ω / 2) * Complex.I by ring,
    show ↑ω * Complex.I * -(↑h / 2) = -(↑h * ↑ω / 2) * Complex.I by ring]
  field_simp
  rw [show Complex.I ^ 2 = -1 from Complex.I_sq]
  ring


/-- **`prop:equivalent-weights`(2).** For the binomial mask `w` on `hℤ` and `q = 2`: the partial
products of `∏_{m ≥ 1} ŵ(2^{-m}ω)` tend to `(sin(hω/2)/(hω/2))⁴`; a law `μ_1` with this transform
exists; every such law is the cubic B-spline (the fourfold convolution of the uniform law on
`[-h/2, h/2]`) and has `D_2 μ_1 = μ_1 * w`; and its tensor powers satisfy the same on `hℤ^d`. -/
theorem equivalent_weights_2 {h : ℝ} (hh : 0 < h) :
    (∀ ω : ℝ, Tendsto (fun M => ladderPartialProduct 2 (gridLaw h binomialMask5) M ω) atTop
        (𝓝 (((Real.sinc (h * ω / 2)) ^ 4 : ℝ) : ℂ))) ∧
      (∃ μ1 : Measure ℝ, IsProbabilityMeasure μ1 ∧
        ∀ ω : ℝ, charFun μ1 ω = (((Real.sinc (h * ω / 2)) ^ 4 : ℝ) : ℂ)) ∧
      ∀ μ1 : Measure ℝ, IsProbabilityMeasure μ1 →
        (∀ ω : ℝ, charFun μ1 ω = (((Real.sinc (h * ω / 2)) ^ 4 : ℝ) : ℂ)) →
          μ1 = ScaleSpace.convPow (uniformInterval h) 4 ∧
          μ1.map (fun x => 2 * x) = μ1 ∗ gridLaw h binomialMask5 ∧
          ∀ n : ℕ, (tensorPow n μ1).map (fun x => (2 : ℝ) • x) =
            tensorPow n μ1 ∗ tensorPow n (gridLaw h binomialMask5) := by
  haveI := isProbabilityMeasure_gridLaw_binomial h
  haveI := isProbabilityMeasure_uniformInterval hh
  haveI := ScaleSpace.isProbabilityMeasure_convPow_real (uniformInterval h) 4
  have hU : ∀ ω : ℝ, charFun (ScaleSpace.convPow (uniformInterval h) 4) ω =
      (((Real.sinc (h * ω / 2)) ^ 4 : ℝ) : ℂ) := fun ω => by
    rw [charFun_convPow_real, charFun_uniformInterval hh, Complex.ofReal_pow]
  -- the relation on the line: `μ̂₁(2ω) = μ̂₁(ω) ŵ(ω)`
  have hrel : ∀ ω : ℝ, (((Real.sinc (h * (2 * ω) / 2)) ^ 4 : ℝ) : ℂ) =
      (((Real.sinc (h * ω / 2)) ^ 4 : ℝ) : ℂ) * charFun (gridLaw h binomialMask5) ω := by
    intro ω
    rw [charFun_gridLaw_binomial, ← Complex.ofReal_mul, show h * (2 * ω) / 2 = 2 * (h * ω / 2) by
      ring, sinc_two_mul, mul_pow]
  refine ⟨fun ω => ?_, ⟨_, inferInstance, hU⟩, fun μ1 hμ1 hc => ?_⟩
  · have hprod : ∀ M : ℕ, ladderPartialProduct 2 (gridLaw h binomialMask5) M ω =
        (((∏ m ∈ Finset.range M, Real.cos (h * ω / 2 / 2 ^ (m + 1))) ^ 4 : ℝ) : ℂ) := by
      intro M
      rw [ladderPartialProduct, ← Finset.prod_pow, Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [charFun_gridLaw_binomial]
      congr 3
      rw [zpow_neg, show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      field_simp
    simp_rw [hprod]
    exact (Complex.continuous_ofReal.tendsto _).comp ((tendsto_prod_cos _).pow 4)
  · have hμ1eq : μ1 = ScaleSpace.convPow (uniformInterval h) 4 :=
      Measure.ext_of_charFun (funext fun ω => by rw [hc, hU])
    have hline : μ1.map (fun x => 2 * x) = μ1 ∗ gridLaw h binomialMask5 := by
      haveI : IsProbabilityMeasure (μ1.map fun x => 2 * x) :=
        Measure.isProbabilityMeasure_map (measurable_const_mul 2).aemeasurable
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      rw [charFun_map_mul, charFun_conv, hc, hc, hrel]
    refine ⟨hμ1eq, hline, fun n => ?_⟩
    have hP : ∀ ν : Measure ℝ, IsProbabilityMeasure ν → IsProbabilityMeasure (tensorPow n ν) :=
      fun ν hν => isProbabilityMeasure_prodLaw (fun _ => ν) fun _ => hν
    haveI := hP μ1 hμ1
    haveI := hP _ (isProbabilityMeasure_gridLaw_binomial h)
    haveI : IsProbabilityMeasure ((tensorPow n μ1).map fun x => (2 : ℝ) • x) :=
      Measure.isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
    have hT : ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∀ ω : Rd n,
        charFun (tensorPow n ν) ω = ∏ i, charFun ν (ω i) :=
      fun ν hν ω => charFun_prodLaw (fun _ => ν) (fun _ => hν) ω
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_map_smul, charFun_conv, hT μ1 hμ1, hT μ1 hμ1,
      hT _ (isProbabilityMeasure_gridLaw_binomial h), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [PiLp.smul_apply, smul_eq_mul, hc, hc, hrel]

end Pyramids
