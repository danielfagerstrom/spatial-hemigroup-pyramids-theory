/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.GridPyramids
import Pyramids.RecursionHelmholtz
import Pyramids.Pyramid.EquivalentWeights

/-!
# `prop:grid-pyramids-infinitely-divisible`(4): the sampled Laplace mask and the binomial mask

Blueprint: `blueprint/src/parts/02-line.tex`, `prop:grid-pyramids-infinitely-divisible`. Wave 3e:
`grid_pyramids_id_4` and `grid_pyramids_id_4_binomial` moved here from `PyramidsSkeleton.Ch02Line`,
their statements unchanged.

## The route

* **The transform** of `λ^L_a` is `(1-a)²/(1 - 2a cos hω + a²)` (`prop:recursion-helmholtz`(2) at
  the spacing `1` and the range `t = -1/log a`, read at `ϑ = hω`).
* **The logarithm series.** With `z = ae^{iϑ}`, `log(1 - 2a cos ϑ + a²) = 2 Re log(1 - z)` and
  `-log(1 - z) = ∑_{k ≥ 1} z^k/k`; at `ϑ = 0` the same series gives `log(1 - a)`. So
  `log[(1 - 2a cos ϑ + a²)/(1-a)²] = ∑_{k ≥ 1} (2a^k/k)(1 - cos kϑ)`, and the mask has the folded
  Lévy measure `ϖ = ∑_{k ≥ 1} (2a^k/k) δ_{kh}`, finite: it is compound Poisson and infinitely
  divisible (clause (1)'s converse).
* **The moments**: `|hn|^p a^{|n|} ≤ h^p |n|^K a^{|n|}`, `K = ⌈p⌉`, summable; `log₊ x ≤ x` gives the
  logarithmic moment, so clause (2) applies, and its knot kernel is the display through
  `1 - 2a cos ϑ + a² = (1-a)² + 2a(1 - cos ϑ)`. Clause (3) gives the stratum.
* **The binomial mask** is symmetric (its transform `cos⁴(hω/2)` is even), not `δ₀` (the transform
  vanishes at `π/h`), and carried by `[-2h, 2h]`; clause (1) and the bounded-support clause apply.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X IsSymmetric)
open scoped Topology ENNReal ComplexOrder

/-! ## Laws on a grid -/

/-- A law on `hℤ` is carried by `hℤ`. -/
theorem gridLaw_apply_not_mulInt (h : ℝ) (lam : ℤ → ℝ) :
    gridLaw h lam {x : ℝ | ¬∃ n : ℤ, x = h * n} = 0 := by
  rw [gridLaw, Measure.sum_apply _ (measurableSet_not_mulInt h), ENNReal.tsum_eq_zero]
  intro n
  rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_not_mulInt h),
    indicator_of_notMem (not_not.2 ⟨n, rfl⟩), smul_zero]

theorem isProbabilityMeasure_gridLaw {h : ℝ} {lam : ℤ → ℝ} (h0 : ∀ n, 0 ≤ lam n)
    (hs : HasSum lam 1) : IsProbabilityMeasure (gridLaw h lam) := by
  constructor
  rw [gridLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg h0 hs.summable, hs.tsum_eq, ENNReal.ofReal_one]

/-- **The transform of a law on `hℤ`** is the Fourier series of its point masses at `ϑ = hω`. -/
theorem charFun_gridLaw {h : ℝ} {lam : ℤ → ℝ} (h0 : ∀ n, 0 ≤ lam n) (hs : HasSum lam 1)
    (ω : ℝ) : charFun (gridLaw h lam) ω = lineFourierSeries lam (h * ω) := by
  haveI := isProbabilityMeasure_gridLaw (h := h) h0 hs
  have hint : Integrable (fun x : ℝ => Complex.exp (ω * x * Complex.I)) (gridLaw h lam) :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply_real]
  rw [gridLaw] at hint ⊢
  rw [integral_sum_measure hint, lineFourierSeries]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (h0 n), Complex.real_smul]
  push_cast
  ring_nf

/-! ## The sampled Laplace mask -/

section Geometric

variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
include ha0 ha1

theorem geomKernel_nonneg (n : ℤ) : 0 ≤ geomKernel a n :=
  mul_nonneg (div_nonneg (by linarith) (by linarith)) (pow_nonneg ha0.le _)

theorem hasSum_geomKernel : HasSum (geomKernel a) 1 := by
  have hg := hasSum_geometric_of_lt_one ha0.le ha1
  have h1 : HasSum (fun n : ℕ => geomKernel a n) ((1 - a) / (1 + a) * (1 - a)⁻¹) := by
    refine (hg.mul_left ((1 - a) / (1 + a))).congr_fun fun n => ?_
    simp [geomKernel]
  have h2 : HasSum (fun n : ℕ => geomKernel a (-((n : ℤ) + 1)))
      ((1 - a) / (1 + a) * (a * (1 - a)⁻¹)) := by
    refine ((hg.mul_left a).mul_left ((1 - a) / (1 + a))).congr_fun fun n => ?_
    have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    simp only [geomKernel, hn, pow_succ]
    ring
  have h3 := HasSum.of_nat_of_neg_add_one (f := geomKernel a) h1 h2
  have hne1 : 1 - a ≠ 0 := by linarith
  have hne2 : 1 + a ≠ 0 := by linarith
  convert h3 using 1
  field_simp

theorem isProbabilityMeasure_geomMask (h : ℝ) : IsProbabilityMeasure (gridLaw h (geomKernel a)) :=
  isProbabilityMeasure_gridLaw (geomKernel_nonneg ha0 ha1) (hasSum_geomKernel ha0 ha1)

/-- **The transform of `λ^L_a`** (`prop:recursion-helmholtz`(2)). -/
theorem charFun_geomMask (h ω : ℝ) :
    charFun (gridLaw h (geomKernel a)) ω =
      (((1 - a) ^ 2 / (1 - 2 * a * Real.cos (h * ω) + a ^ 2) : ℝ) : ℂ) := by
  rw [charFun_gridLaw (geomKernel_nonneg ha0 ha1) (hasSum_geomKernel ha0 ha1)]
  have hlog : Real.log a < 0 := Real.log_neg ha0 ha1
  set t : ℝ := -1 / Real.log a with ht
  have htpos : 0 < t := div_pos_of_neg_of_neg (by norm_num) hlog
  have hexp : Real.exp (-1 / t) = a := by
    have e : -1 / t = Real.log a := by
      rw [ht]
      field_simp
    rw [e, Real.exp_log ha0]
  have hk : sampledLaplace 1 t = geomKernel a := by
    funext n
    simp only [sampledLaplace, geomKernel, hexp]
  rw [← hk, (recursion_grid_transform one_pos htpos (h * ω)).1, hexp]

/-- The denominator `1 - 2a cos ϑ + a² ≥ (1-a)² > 0`. -/
theorem geom_denom_pos (θ : ℝ) : 0 < 1 - 2 * a * Real.cos θ + a ^ 2 := by
  nlinarith [Real.cos_le_one θ]

/-- **The logarithm series**:
`∑_{k ≥ 1} (2a^k/k)(1 - cos kϑ) = log[(1 - 2a cos ϑ + a²)/(1-a)²]`. -/
theorem hasSum_geom_log (θ : ℝ) :
    HasSum (fun k : ℕ => 2 * a ^ (k + 1) / (k + 1) * (1 - Real.cos ((k + 1) * θ)))
      (Real.log ((1 - 2 * a * Real.cos θ + a ^ 2) / (1 - a) ^ 2)) := by
  set z : ℂ := (a : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hz
  have hzn : ‖z‖ < 1 := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha0]
    exact ha1
  -- the real parts of `z^k/k`, shifted to start at `k = 1`
  have h1 := (hasSum_nat_add_iff' 1).2 (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hzn))
  have hre : ∀ k : ℕ, ((z ^ (k + 1) / ((k : ℂ) + 1)).re) =
      a ^ (k + 1) * Real.cos ((k + 1) * θ) / (k + 1) := by
    intro k
    have e : z ^ (k + 1) = ((a ^ (k + 1) : ℝ) : ℂ) *
        Complex.exp ((((k + 1) * θ : ℝ) : ℂ) * Complex.I) := by
      rw [hz, mul_pow, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    rw [e, show ((k : ℂ) + 1) = (((k + 1 : ℝ)) : ℂ) by push_cast; ring,
      Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
    Complex.zero_re, sub_zero, Nat.cast_add, Nat.cast_one] at h1
  have h1' : HasSum (fun k : ℕ => a ^ (k + 1) * Real.cos ((k + 1) * θ) / (k + 1))
      (-Real.log ‖1 - z‖) := by
    have e1 : (-Complex.log (1 - z)).re = -Real.log ‖1 - z‖ := by
      rw [Complex.neg_re, Complex.log_re]
    rw [← e1]
    exact h1.congr_fun fun k => (hre k).symm
  have h0 := Real.hasSum_pow_div_log_of_abs_lt_one (x := a) (by rw [abs_of_pos ha0]; exact ha1)
  have h2 := (h0.mul_left 2).sub (h1'.mul_left 2)
  have hnorm : ‖1 - z‖ ^ 2 = 1 - 2 * a * Real.cos θ + a ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [hz, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have ha : 0 < 1 - a := by linarith
  have e2 : (fun k : ℕ => 2 * a ^ (k + 1) / (k + 1) * (1 - Real.cos ((k + 1) * θ))) =
      fun k : ℕ => 2 * (a ^ (k + 1) / (k + 1)) -
        2 * (a ^ (k + 1) * Real.cos ((k + 1) * θ) / (k + 1)) := by
    funext k
    ring
  have e3 : Real.log ((1 - 2 * a * Real.cos θ + a ^ 2) / (1 - a) ^ 2) =
      2 * -Real.log (1 - a) - 2 * -Real.log ‖1 - z‖ := by
    rw [Real.log_div (geom_denom_pos ha0 ha1 θ).ne' (pow_pos ha 2).ne', ← hnorm, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  rw [e2, e3]
  exact h2

/-- **The transform as an exponential**: `λ̂^L_a(ω) = exp(-∑_{k ≥ 1}(2a^k/k)(1 - cos khω))`. -/
theorem geom_symbol_eq_exp (θ : ℝ) :
    (1 - a) ^ 2 / (1 - 2 * a * Real.cos θ + a ^ 2) =
      Real.exp (-∑' k : ℕ, 2 * a ^ (k + 1) / (k + 1) * (1 - Real.cos ((k + 1) * θ))) := by
  have ha : 0 < 1 - a := by linarith
  rw [(hasSum_geom_log ha0 ha1 θ).tsum_eq, Real.exp_neg,
    Real.exp_log (div_pos (geom_denom_pos ha0 ha1 θ) (by positivity)), inv_div]

/-- **The folded Lévy measure of `λ^L_a`**: `ϖ = ∑_{k ≥ 1} (2a^k/k) δ_{kh}`. -/
noncomputable def geomLevyMeasure (a h : ℝ) : Measure ℝ :=
  Measure.sum fun k : ℕ => ENNReal.ofReal (2 * a ^ (k + 1) / (k + 1)) • Measure.dirac (h * (k + 1))

omit ha0 ha1 in
theorem geomLevyMeasure_univ (h : ℝ) :
    geomLevyMeasure a h univ = ∑' k : ℕ, ENNReal.ofReal (2 * a ^ (k + 1) / (k + 1)) := by
  rw [geomLevyMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp

theorem summable_geomLevy : Summable fun k : ℕ => 2 * a ^ (k + 1) / (k + 1) := by
  have h0 := Real.hasSum_pow_div_log_of_abs_lt_one (x := a) (by rw [abs_of_pos ha0]; exact ha1)
  exact (h0.mul_left 2).summable.congr fun k => by ring

theorem isMaskLevyMeasure_geom {h : ℝ} (hh : 0 < h) :
    IsMaskLevyMeasure (gridLaw h (geomKernel a)) (geomLevyMeasure a h) := by
  have hnn : ∀ k : ℕ, 0 ≤ 2 * a ^ (k + 1) / (k + 1) := fun k => by positivity
  haveI hfin : IsFiniteMeasure (geomLevyMeasure a h) := ⟨by
    rw [geomLevyMeasure_univ, ← ENNReal.ofReal_tsum_of_nonneg hnn (summable_geomLevy ha0 ha1)]
    exact ENNReal.ofReal_lt_top⟩
  refine ⟨hfin, ?_, fun ω => ?_⟩
  · rw [ScaleSpace.IsFolded, geomLevyMeasure, Measure.sum_apply _ measurableSet_Iic,
      ENNReal.tsum_eq_zero]
    intro k
    rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iic,
      indicator_of_notMem (by simp only [mem_Iic, not_le]; positivity), smul_zero]
  · have hint : Integrable (fun v => 1 - Real.cos (ω * v)) (geomLevyMeasure a h) :=
      integrable_one_sub_cos_of_finite _ ω
    rw [charFun_geomMask ha0 ha1, geom_symbol_eq_exp ha0 ha1]
    rw [geomLevyMeasure] at hint ⊢
    rw [integral_sum_measure hint]
    congr 3
    refine tsum_congr fun k => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hnn k), smul_eq_mul]
    ring_nf

omit ha1 in
theorem geomLevyMeasure_ne_zero (h : ℝ) : geomLevyMeasure a h ≠ 0 := by
  intro h0
  have h1 := Measure.le_iff'.1 (Measure.le_sum (fun k : ℕ =>
    ENNReal.ofReal (2 * a ^ (k + 1) / (k + 1)) • Measure.dirac (h * (k + 1))) 0) univ
  rw [← geomLevyMeasure, h0] at h1
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Measure.coe_zero,
    Pi.zero_apply, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
  have : 0 < 2 * a ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) := by positivity
  linarith

/-- **The moments of `λ^L_a`** are finite. -/
theorem lintegral_rpow_geomMask {h : ℝ} (hh : 0 < h) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂(gridLaw h (geomKernel a)) < ⊤ := by
  set K : ℕ := ⌈p⌉₊ with hK
  have hpK : p ≤ K := Nat.le_ceil p
  set g : ℤ → ℝ := fun n => (1 - a) / (1 + a) * h ^ p * ((n.natAbs : ℝ) ^ K * a ^ n.natAbs)
    with hg
  have hgs : Summable g := by
    have hs : Summable fun n : ℕ => (n : ℝ) ^ K * a ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one K
        (by rw [Real.norm_eq_abs, abs_of_pos ha0]; exact ha1)
    refine Summable.mul_left _ (Summable.of_nat_of_neg ?_ ?_)
    · simpa using hs
    · simpa using hs
  set f : ℤ → ℝ := fun n => geomKernel a n * |h * n| ^ p with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg (geomKernel_nonneg ha0 ha1 n) (by positivity)
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    have habs : |(n : ℝ)| = (n.natAbs : ℝ) := ((Nat.cast_natAbs n).trans Int.cast_abs).symm
    have hrp : (n.natAbs : ℝ) ^ p ≤ (n.natAbs : ℝ) ^ K := by
      rcases Nat.eq_zero_or_pos n.natAbs with h0 | h0
      · rw [h0, Nat.cast_zero, Real.zero_rpow hp.ne']
        positivity
      · have h1 : (1 : ℝ) ≤ n.natAbs := by exact_mod_cast h0
        calc (n.natAbs : ℝ) ^ p ≤ (n.natAbs : ℝ) ^ (K : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1 hpK
          _ = (n.natAbs : ℝ) ^ K := Real.rpow_natCast _ _
    simp only [hf, hg, geomKernel]
    rw [abs_mul, abs_of_pos hh, Real.mul_rpow hh.le (abs_nonneg _), habs]
    have hc : 0 ≤ (1 - a) / (1 + a) := div_nonneg (by linarith) (by linarith)
    have hp' : 0 ≤ h ^ p := by positivity
    have ha' : 0 ≤ a ^ n.natAbs := pow_nonneg ha0.le _
    calc (1 - a) / (1 + a) * a ^ n.natAbs * (h ^ p * (n.natAbs : ℝ) ^ p)
        = (1 - a) / (1 + a) * h ^ p * ((n.natAbs : ℝ) ^ p * a ^ n.natAbs) := by ring
      _ ≤ (1 - a) / (1 + a) * h ^ p * ((n.natAbs : ℝ) ^ K * a ^ n.natAbs) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrp ha')
            (mul_nonneg hc hp')
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hfg hgs
  rw [gridLaw, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have e : ∀ n : ℤ, ENNReal.ofReal (geomKernel a n) * ENNReal.ofReal (|h * n| ^ p) =
      ENNReal.ofReal (f n) := fun n =>
    (ENNReal.ofReal_mul (geomKernel_nonneg ha0 ha1 n)).symm
  simp_rw [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfs]
  exact ENNReal.ofReal_lt_top

omit ha0 in
/-- `1 - 2a cos ϑ + a² = (1-a)²(1 + 2ς(1 - cos ϑ))`, `ς = a/(1-a)²`. -/
theorem geom_symbol_eq_inv (θ : ℝ) :
    (1 - a) ^ 2 / (1 - 2 * a * Real.cos θ + a ^ 2) =
      (1 + 2 * (a / (1 - a) ^ 2) * (1 - Real.cos θ))⁻¹ := by
  have hne : (1 - a) ^ 2 ≠ 0 := by
    have : 1 - a ≠ 0 := by linarith
    positivity
  have e : 1 + 2 * (a / (1 - a) ^ 2) * (1 - Real.cos θ) =
      (1 - 2 * a * Real.cos θ + a ^ 2) / (1 - a) ^ 2 := by
    rw [eq_div_iff hne]
    calc (1 + 2 * (a / (1 - a) ^ 2) * (1 - Real.cos θ)) * (1 - a) ^ 2
        = (1 - a) ^ 2 + 2 * (1 - Real.cos θ) * (a / (1 - a) ^ 2 * (1 - a) ^ 2) := by ring
      _ = _ := by rw [div_mul_cancel₀ a hne]; ring
  rw [e, inv_div]

end Geometric

/-! ## `prop:grid-pyramids-infinitely-divisible`(4) -/

/-- **`prop:grid-pyramids-infinitely-divisible`(4), the sampled Laplace mask.** `λ^L_a` is a mask,
infinitely divisible with all moments finite; its grid pyramid is exact for every `q > 1`, every
family carrying it has the knot kernel (`eq:geometric-pyramid-knot-kernel`), and it is not exact
in the third stratum. -/
theorem grid_pyramids_id_4 {h : ℝ} (hh : 0 < h) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    IsGridMask h (gridLaw h (geomKernel a)) ∧ IsInfinitelyDivisible (gridLaw h (geomKernel a)) ∧
      (∀ p : ℝ, 0 < p → ∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂(gridLaw h (geomKernel a)) < ⊤) ∧
      ∀ q : ℝ, 1 < q → IsExactGridPyramid q (gridLaw h (geomKernel a)) ∧
        (∀ (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ) (μ : ℝ → ℝ → Measure ℝ),
          CarriesGridLadder q (gridLaw h (geomKernel a)) Φ S μ → ∀ ω : ℝ,
            Tendsto (fun M : ℕ => ∏ m ∈ Finset.range M,
                ((((1 + 2 * (a / (1 - a) ^ 2) *
                  (1 - Real.cos (q ^ (-((m : ℤ) + 1)) * h * ω)))⁻¹ : ℝ)) : ℂ))
              atTop (𝓝 (charFun (μ 0 1) ω))) ∧
        ¬ IsExactGridPyramidThird q (gridLaw h (geomKernel a)) := by
  haveI := isProbabilityMeasure_geomMask ha0 ha1 h
  have hmask := isMaskLevyMeasure_geom ha0 ha1 hh
  have hgrid : IsGridMask h (gridLaw h (geomKernel a)) :=
    ⟨inferInstance, hmask.isSymmetric,
      fun h0 => geomLevyMeasure_ne_zero ha0 h (hmask.eq_zero_iff.2 h0),
      gridLaw_apply_not_mulInt h _⟩
  have hid := hmask.isInfinitelyDivisible
  have hmom := fun p (hp : (0 : ℝ) < p) => lintegral_rpow_geomMask ha0 ha1 hh hp
  refine ⟨hgrid, hid, hmom, fun q hq => ⟨?_, fun Φ S μ hc ω => ?_,
    (grid_pyramids_id_3 hq hh _ hgrid).1⟩⟩
  · refine (grid_pyramids_id_2 hq hh _ hgrid).2.2 ⟨hid, lt_of_le_of_lt ?_ (hmom 1 one_pos)⟩
    refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_one, Real.posLog, max_le_iff]
    exact ⟨abs_nonneg x, Real.log_le_self (abs_nonneg x)⟩
  · obtain ⟨hsym, -, -⟩ := hc.family
    obtain ⟨P, hP⟩ := exists_folded hsym
    have hk := ((grid_pyramids_id_2_knot hq _ hgrid _ hmask Φ S μ hc (P 1)
      (hP 1 zero_le_one)).2.2 ω).1
    refine hk.congr fun M => Finset.prod_congr rfl fun m _ => ?_
    rw [charFun_geomMask ha0 ha1, geom_symbol_eq_inv ha1,
      show h * (q ^ (-((m : ℤ) + 1)) * ω) = q ^ (-((m : ℤ) + 1)) * h * ω by ring]

/-- **`prop:grid-pyramids-infinitely-divisible`(4), the binomial mask.** `[1,4,6,4,1]/16` on `hℤ`
is not infinitely divisible and has no exact grid pyramid. -/
theorem grid_pyramids_id_4_binomial {h : ℝ} (hh : 0 < h) :
    ¬ IsInfinitelyDivisible (gridLaw h binomialMask5) ∧
      ∀ q : ℝ, 1 < q → ¬ IsExactGridPyramid q (gridLaw h binomialMask5) := by
  haveI := isProbabilityMeasure_gridLaw_binomial h
  have hsym : IsSymmetric (gridLaw h binomialMask5) := by
    haveI : IsProbabilityMeasure ((gridLaw h binomialMask5).map fun x => -x) :=
      Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
    change (gridLaw h binomialMask5).map (fun x => -x) = gridLaw h binomialMask5
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_map_neg_real, charFun_gridLaw_binomial, charFun_gridLaw_binomial, mul_neg,
      neg_div, Real.cos_neg]
  have hne : gridLaw h binomialMask5 ≠ Measure.dirac 0 := by
    intro h0
    have h1 := charFun_gridLaw_binomial h (Real.pi / h)
    rw [h0, charFun_dirac, show h * (Real.pi / h) / 2 = Real.pi / 2 by field_simp,
      Real.cos_pi_div_two] at h1
    simp at h1
  have hgrid : IsGridMask h (gridLaw h binomialMask5) :=
    ⟨inferInstance, hsym, hne, gridLaw_apply_not_mulInt h _⟩
  have hbdd : ∃ R : ℝ, gridLaw h binomialMask5 {x : ℝ | R < |x|} = 0 := by
    refine ⟨2 * h, ?_⟩
    rw [gridLaw_binomial_eq, Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Measure.smul_apply, Measure.dirac_apply, indicator_of_notMem, smul_zero]
    simp only [mem_setOf_eq, not_lt]
    rw [Finset.mem_Icc] at hn
    have h1 : |(n : ℝ)| ≤ 2 := by
      rw [abs_le]
      constructor <;> exact_mod_cast (by omega : _)
    rw [abs_mul, abs_of_pos hh]
    nlinarith [abs_nonneg (n : ℝ)]
  exact ⟨(grid_pyramids_id_1 hh _ hgrid).2.2 hbdd,
    fun q hq => grid_pyramids_id_4_bounded hq hh _ hgrid hbdd⟩

end Pyramids
