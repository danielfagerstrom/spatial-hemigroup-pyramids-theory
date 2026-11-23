/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.ClassicalWeights

/-!
# `prop:classical-pyramids-approximate`(2): the moments of the equivalent weights

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:classical-pyramids-approximate`. Wave 3a:
`classical_pyramids_approximate_2` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in
statement and name.

## The route

The printed one, read on measures rather than on random variables. For laws of bounded support,
`∫x^n d(μ * ν) = ∑_m C(n,m) ∫x^m dμ ∫x^{n-m} dν` (`integral_pow_conv`, the binomial formula and
Fubini). For centred laws this makes the variance and the fourth cumulant
`κ₄ = ∫x⁴ - 3(∫x²)²` additive under convolution (`IsCentredBdd.conv`), hence over a list
(`IsCentredBdd.convList_map`) and over a convolution power (`IsCentredBdd.convPow_moments`). A
dilate by `c` multiplies them by `c²` and `c⁴`. The binomial mask has variance `h²` and
`κ₄ = -h⁴/2`; the uniform law on `[-h/2, h/2]` has variance `h²/12` and `κ₄ = -h⁴/120`. The
rest is the algebra of the geometric sums, with `16ⁿ - 1 = (4ⁿ - 1)(4ⁿ + 1)`.

The excess kurtosis of the cubic B-spline, a conjunct of clause (3), is proved here too
(`bspline4_excess_kurtosis`).
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (convPow)

/-! ## Moments of laws of bounded support -/

/-- On a finite measure carried by `[-R, R]` every power `x^k` is integrable. -/
theorem integrable_pow_of_abs_gt_null {μ : Measure ℝ} [IsFiniteMeasure μ] {R : ℝ}
    (h : μ {x | R < |x|} = 0) (k : ℕ) : Integrable (fun x => x ^ k) μ := by
  refine Integrable.of_bound (continuous_pow k).aestronglyMeasurable (|R| ^ k) ?_
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h
  simp only [mem_setOf_eq, not_le, norm_pow, Real.norm_eq_abs] at hx ⊢
  by_contra hcon
  exact absurd hx (not_lt.2 (pow_le_pow_left₀ (abs_nonneg x)
    ((not_lt.1 hcon).trans (le_abs_self R)) k))

/-- **The moments of a convolution**: for finite measures of bounded support,
`∫x^n d(μ * ν) = ∑_{m ≤ n} ∫x^m dμ ∫x^{n-m} dν C(n,m)`. -/
theorem integral_pow_conv {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {R₁ R₂ : ℝ}
    (h₁ : μ {x | R₁ < |x|} = 0) (h₂ : ν {x | R₂ < |x|} = 0) (n : ℕ) :
    ∫ x, x ^ n ∂(μ ∗ ν) = ∑ m ∈ Finset.range (n + 1),
      (∫ x, x ^ m ∂μ) * (∫ x, x ^ (n - m) ∂ν) * (n.choose m : ℝ) := by
  rw [Measure.conv, integral_map measurable_add.aemeasurable
    (continuous_pow n).aestronglyMeasurable]
  simp_rw [add_pow]
  rw [integral_finsetSum _ fun m _ => ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_mul_const, integral_prod_mul (fun x : ℝ => x ^ m) (fun y : ℝ => y ^ (n - m))]
  · exact ((integrable_pow_of_abs_gt_null h₁ m).mul_prod
      (integrable_pow_of_abs_gt_null h₂ (n - m))).mul_const _

/-- The moments of a dilate: `∫x^k d(T_c μ) = c^k ∫x^k dμ`. -/
theorem integral_pow_map_smul (μ : Measure ℝ) (c : ℝ) (k : ℕ) :
    ∫ x, x ^ k ∂(μ.map fun x => c • x) = c ^ k * ∫ x, x ^ k ∂μ := by
  rw [integral_map (measurable_const_smul c).aemeasurable (continuous_pow k).aestronglyMeasurable]
  simp only [smul_eq_mul, mul_pow]
  exact integral_const_mul _ _

/-- **A centred law of bounded support**: a probability measure on the line, carried by a bounded
interval, with mean `0`. -/
structure IsCentredBdd (μ : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure μ
  bdd : ∃ R : ℝ, μ {x | R < |x|} = 0
  mean : ∫ x, x ∂μ = 0

/-- **The fourth cumulant of a centred law**, `κ₄ = ∫x⁴ - 3(∫x²)²`. -/
noncomputable def cum4 (μ : Measure ℝ) : ℝ := ∫ x, x ^ 4 ∂μ - 3 * (∫ x, x ^ 2 ∂μ) ^ 2

/-- **Variance and fourth cumulant are additive under convolution**, for centred laws of bounded
support. -/
theorem IsCentredBdd.conv {μ ν : Measure ℝ} (hμ : IsCentredBdd μ) (hν : IsCentredBdd ν) :
    IsCentredBdd (μ ∗ ν) ∧ ∫ x, x ^ 2 ∂(μ ∗ ν) = ∫ x, x ^ 2 ∂μ + ∫ x, x ^ 2 ∂ν ∧
      cum4 (μ ∗ ν) = cum4 μ + cum4 ν := by
  haveI := hμ.prob
  haveI := hν.prob
  obtain ⟨R₁, h₁⟩ := hμ.bdd
  obtain ⟨R₂, h₂⟩ := hν.bdd
  have hm := integral_pow_conv h₁ h₂
  have h0 : ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ → ∫ x, x ^ 0 ∂ρ = 1 := fun ρ _ => by
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
  have h1 : ∀ ρ : Measure ℝ, ∫ x, x ∂ρ = 0 → ∫ x, x ^ 1 ∂ρ = 0 := fun ρ hρ => by
    simp only [pow_one, hρ]
  have e1 := hm 1
  have e2 := hm 2
  have e4 := hm 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0 μ inferInstance,
    h0 ν inferInstance, h1 μ hμ.mean, h1 ν hν.mean] at e1 e2 e4
  norm_num at e1 e2 e4
  have hc42 : ((Nat.choose 4 2 : ℕ) : ℝ) = 6 := by norm_num [Nat.choose]
  rw [hc42] at e4
  refine ⟨⟨inferInstance, ⟨R₁ + R₂, conv_abs_gt_null h₁ h₂⟩, ?_⟩, ?_, ?_⟩
  · simpa only [pow_one] using e1
  · rw [e2]
    ring
  · rw [cum4, cum4, cum4, e2, e4]
    ring

/-- `δ₀` is centred, with variance and fourth cumulant `0`. -/
theorem isCentredBdd_dirac_zero :
    IsCentredBdd (Measure.dirac (0 : ℝ)) ∧ ∫ x, x ^ 2 ∂(Measure.dirac (0 : ℝ)) = 0 ∧
      cum4 (Measure.dirac (0 : ℝ)) = 0 := by
  refine ⟨⟨inferInstance, ⟨0, ?_⟩, by simp⟩, by simp, by simp [cum4]⟩
  rw [Measure.dirac_apply' _ (measurableSet_lt measurable_const continuous_abs.measurable)]
  simp

/-- Variance and fourth cumulant of the convolution of a list of centred laws. -/
theorem IsCentredBdd.convList_map (L : List ℕ) (f : ℕ → Measure ℝ)
    (hf : ∀ k ∈ L, IsCentredBdd (f k)) :
    IsCentredBdd (convList (L.map f)) ∧
      ∫ x, x ^ 2 ∂(convList (L.map f)) = (L.map fun k => ∫ x, x ^ 2 ∂(f k)).sum ∧
      cum4 (convList (L.map f)) = (L.map fun k => cum4 (f k)).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil, convList]
    exact isCentredBdd_dirac_zero
  | cons a L ih =>
    obtain ⟨hc, h2, h4⟩ := ih fun k hk => hf k (List.mem_cons_of_mem _ hk)
    obtain ⟨hc', h2', h4'⟩ := (hf a List.mem_cons_self).conv hc
    simp only [List.map_cons, List.sum_cons, convList]
    exact ⟨hc', by rw [h2', h2], by rw [h4', h4]⟩

/-- Variance and fourth cumulant of a convolution power of a centred law. -/
theorem IsCentredBdd.convPow_moments {μ : Measure ℝ} (hμ : IsCentredBdd μ) (n : ℕ) :
    IsCentredBdd (convPow μ n) ∧ ∫ x, x ^ 2 ∂(convPow μ n) = n * ∫ x, x ^ 2 ∂μ ∧
      cum4 (convPow μ n) = n * cum4 μ := by
  induction n with
  | zero =>
    rw [ScaleSpace.convPow, Nat.cast_zero, zero_mul, zero_mul]
    exact isCentredBdd_dirac_zero
  | succ n ih =>
    obtain ⟨hc, h2, h4⟩ := ih
    obtain ⟨hc', h2', h4'⟩ := hc.conv hμ
    rw [ScaleSpace.convPow]
    refine ⟨hc', by rw [h2', h2]; push_cast; ring, by rw [h4', h4]; push_cast; ring⟩

/-- A dilate `T_c μ`, `c > 0`, of a centred law is centred, with variance `c²∫x²dμ` and fourth
cumulant `c⁴κ₄(μ)`. -/
theorem IsCentredBdd.map_smul {μ : Measure ℝ} (hμ : IsCentredBdd μ) {c : ℝ} (hc : 0 < c) :
    IsCentredBdd (μ.map fun x => c • x) ∧
      ∫ x, x ^ 2 ∂(μ.map fun x => c • x) = c ^ 2 * ∫ x, x ^ 2 ∂μ ∧
      cum4 (μ.map fun x => c • x) = c ^ 4 * cum4 μ := by
  haveI := hμ.prob
  obtain ⟨R, hR⟩ := hμ.bdd
  refine ⟨⟨Measure.isProbabilityMeasure_map (measurable_const_smul c).aemeasurable,
    ⟨c * R, map_mul_abs_gt_null hc hR⟩, ?_⟩, integral_pow_map_smul μ c 2, ?_⟩
  · have := integral_pow_map_smul μ c 1
    simp only [pow_one] at this
    rw [this, hμ.mean, mul_zero]
  · rw [cum4, cum4, integral_pow_map_smul, integral_pow_map_smul]
    ring

/-! ## The binomial mask and the uniform law -/

/-- An integral against the binomial mask on `hℤ`:
`∫f dw = (f(-2h) + 4f(-h) + 6f(0) + 4f(h) + f(2h))/16`. -/
theorem integral_gridLaw_binomial (h : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(gridLaw h binomialMask5) =
      (f (-(2 * h)) + 4 * f (-h) + 6 * f 0 + 4 * f h + f (2 * h)) / 16 := by
  rw [gridLaw_binomial_eq, integral_finsetSum_measure (fun n _ => ?_)]
  swap
  · exact Integrable.smul_measure (integrable_dirac enorm_lt_top) ENNReal.ofReal_ne_top
  simp only [integral_smul_measure, integral_dirac]
  obtain ⟨h1, h2, h3, h4, h5⟩ := binomialMask5_vals
  rw [show Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [h1, h2, h3, h4, h5]
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by norm_num)]
  push_cast
  simp only [smul_eq_mul, mul_neg, mul_one, mul_zero]
  ring_nf

/-- The binomial mask on `hℤ`, `h > 0`, is centred, with variance `h²` and `κ₄ = -h⁴/2`. -/
theorem isCentredBdd_gridLaw_binomial {h : ℝ} (hh : 0 < h) :
    IsCentredBdd (gridLaw h binomialMask5) ∧ ∫ x, x ^ 2 ∂(gridLaw h binomialMask5) = h ^ 2 ∧
      cum4 (gridLaw h binomialMask5) = -(h ^ 4 / 2) := by
  have h2 : ∫ x, x ^ 2 ∂(gridLaw h binomialMask5) = h ^ 2 := by
    rw [integral_gridLaw_binomial]; ring
  refine ⟨⟨isProbabilityMeasure_gridLaw_binomial h, ⟨_, gridLaw_binomial_abs_gt_null hh⟩, ?_⟩,
    h2, ?_⟩
  · rw [integral_gridLaw_binomial]; ring
  · rw [cum4, h2, integral_gridLaw_binomial]; ring

/-- The moments of the uniform law on `[-h/2, h/2]`. -/
theorem integral_pow_uniformInterval {h : ℝ} (hh : 0 < h) (k : ℕ) :
    ∫ x, x ^ k ∂(uniformInterval h) =
      h⁻¹ * (((h / 2) ^ (k + 1) - (-(h / 2)) ^ (k + 1)) / (k + 1)) := by
  rw [uniformInterval, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hh.le),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), integral_pow,
    smul_eq_mul]

/-- The uniform law on `[-h/2, h/2]` is centred, with variance `h²/12` and `κ₄ = -h⁴/120`. -/
theorem isCentredBdd_uniformInterval {h : ℝ} (hh : 0 < h) :
    IsCentredBdd (uniformInterval h) ∧ ∫ x, x ^ 2 ∂(uniformInterval h) = h ^ 2 / 12 ∧
      cum4 (uniformInterval h) = -(h ^ 4 / 120) := by
  have h2 : ∫ x, x ^ 2 ∂(uniformInterval h) = h ^ 2 / 12 := by
    rw [integral_pow_uniformInterval hh]
    field_simp
    ring
  refine ⟨⟨isProbabilityMeasure_uniformInterval hh, ⟨_, uniformInterval_abs_gt_null h⟩, ?_⟩,
    h2, ?_⟩
  · have := integral_pow_uniformInterval hh 1
    simp only [pow_one] at this
    rw [this]
    ring
  · rw [cum4, h2, integral_pow_uniformInterval hh]
    field_simp
    ring

/-! ## `prop:classical-pyramids-approximate`(2) -/

/-- The equivalent weights of the binomial mask are centred, with variance `(4ⁿ - 1)h²/3` and
fourth cumulant `-h⁴(16ⁿ - 1)/30`. -/
theorem equivWeight_binomial_moments {h : ℝ} (hh : 0 < h) (n : ℕ) :
    IsCentredBdd (equivWeight 2 (gridLaw h binomialMask5) n) ∧
      ∫ x, x ^ 2 ∂(equivWeight 2 (gridLaw h binomialMask5) n) = (4 ^ n - 1) * h ^ 2 / 3 ∧
      cum4 (equivWeight 2 (gridLaw h binomialMask5) n) = -(h ^ 4 * (16 ^ n - 1) / 30) := by
  obtain ⟨hw, hw2, hw4⟩ := isCentredBdd_gridLaw_binomial hh
  have hk : ∀ k : ℕ, IsCentredBdd ((gridLaw h binomialMask5).map fun x => ((2 : ℝ) ^ k) • x) ∧
      ∫ x, x ^ 2 ∂((gridLaw h binomialMask5).map fun x => ((2 : ℝ) ^ k) • x) = 4 ^ k * h ^ 2 ∧
      cum4 ((gridLaw h binomialMask5).map fun x => ((2 : ℝ) ^ k) • x) =
        16 ^ k * -(h ^ 4 / 2) := by
    intro k
    obtain ⟨hc, h2, h4⟩ := hw.map_smul (c := (2 : ℝ) ^ k) (by positivity)
    refine ⟨hc, ?_, ?_⟩
    · rw [h2, hw2, ← pow_mul, mul_comm k 2, pow_mul]
      norm_num
    · rw [h4, hw4, ← pow_mul, mul_comm k 4, pow_mul]
      norm_num
  obtain ⟨hc, h2, h4⟩ := IsCentredBdd.convList_map (List.range n) _ fun k _ => (hk k).1
  refine ⟨hc, ?_, ?_⟩
  · rw [equivWeight, h2, list_sum_map_range]
    clear hc h2 h4
    simp only [(hk _).2.1]
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  · rw [equivWeight, h4, list_sum_map_range]
    clear hc h2 h4
    simp only [(hk _).2.2]
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- **`prop:classical-pyramids-approximate`(2).** `W_n` (centred) has variance `(4ⁿ - 1)h²/3` and
excess kurtosis `-(3/10)(4ⁿ + 1)/(4ⁿ - 1)`, which is less than `-3/10`. -/
theorem classical_pyramids_approximate_2 {h : ℝ} (hh : 0 < h) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x, x ∂(equivWeight 2 (gridLaw h binomialMask5) n) = 0 ∧
      ∫ x, x ^ 2 ∂(equivWeight 2 (gridLaw h binomialMask5) n) = (4 ^ n - 1) * h ^ 2 / 3 ∧
      (∫ x, x ^ 4 ∂(equivWeight 2 (gridLaw h binomialMask5) n) -
          3 * (∫ x, x ^ 2 ∂(equivWeight 2 (gridLaw h binomialMask5) n)) ^ 2) /
          (∫ x, x ^ 2 ∂(equivWeight 2 (gridLaw h binomialMask5) n)) ^ 2 =
        -(3 / 10) * ((4 ^ n + 1) / (4 ^ n - 1)) ∧
      -(3 / 10) * ((4 ^ n + 1) / (4 ^ n - 1)) < -(3 / 10 : ℝ) := by
  obtain ⟨hc, h2, h4⟩ := equivWeight_binomial_moments hh n
  have h4n : (4 : ℝ) ≤ 4 ^ n := by
    calc (4 : ℝ) = 4 ^ 1 := (pow_one 4).symm
      _ ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h16 : (16 : ℝ) ^ n = (4 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hne : (4 : ℝ) ^ n - 1 ≠ 0 := by linarith
  have hh0 : h ≠ 0 := hh.ne'
  refine ⟨hc.mean, h2, ?_, ?_⟩
  · change cum4 _ / _ = _
    rw [h4, h2, h16]
    field_simp
    ring
  · have hlt : 1 < ((4 : ℝ) ^ n + 1) / (4 ^ n - 1) := by
      rw [one_lt_div (by linarith)]
      linarith
    linarith

/-- **The excess kurtosis of the cubic B-spline** is `-3/10`. -/
theorem bspline4_excess_kurtosis {h : ℝ} (hh : 0 < h) :
    (∫ x, x ^ 4 ∂(convPow (uniformInterval h) 4) -
        3 * (∫ x, x ^ 2 ∂(convPow (uniformInterval h) 4)) ^ 2) /
        (∫ x, x ^ 2 ∂(convPow (uniformInterval h) 4)) ^ 2 = -(3 / 10) := by
  obtain ⟨hu, hu2, hu4⟩ := isCentredBdd_uniformInterval hh
  obtain ⟨-, h2, h4⟩ := hu.convPow_moments 4
  change cum4 _ / _ = _
  rw [h4, h2, hu2, hu4]
  have hh0 : h ≠ 0 := hh.ne'
  field_simp
  ring

end Pyramids
