/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.GeometricMask

/-!
# Kernels on `ℤ`: convolution, Fourier series, uniqueness

Blueprint: `blueprint/src/parts/02-line.tex`, `prop:sampled-laplace-exact` (wave 3f). The library
`prop:sampled-laplace-exact` reads: summable kernels on `ℤ` (`zconv`, `zdelta`, `zconvPow` of
`Pyramids.Defs.Line`) form a commutative and associative convolution algebra with unit `δ₀`; the
Fourier series `lineFourierSeries` of a convolution is the product of the Fourier series; and a
summable kernel is determined by its Fourier series, through the coefficient formula
`integral_coeff_of_hasSum` of `prop:positivity-threshold`. The proofs follow those of the kernels
on `ℤ^d` (`Pyramids.DiscreteHelmholtz`). The geometric kernels `geomKernel a` and `oneSidedGeom a`
have the transfers `(1-a)²/(1 - 2a cos ϑ + a²)` and `(1-a)/(1 - ae^{iϑ})`, also at `a = 0`.
-/

namespace Pyramids

open MeasureTheory Set Filter Complex
open scoped Topology Real

/-- `∫_{-π}^{π} e^{ikx} dx = 2π[k = 0]`. -/
theorem integral_Icc_exp_int (k : ℤ) :
    ∫ x in Set.Icc (-Real.pi) Real.pi, Complex.exp (((k * x : ℝ) : ℂ) * I) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  split_ifs with hk
  · subst hk
    simp only [Int.cast_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
      intervalIntegral.integral_const, Complex.real_smul]
    push_cast; ring
  · have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
    have e : ∀ x : ℝ, Complex.exp (((k * x : ℝ) : ℂ) * I) = Complex.exp ((k : ℂ) * I * x) :=
      fun x => by push_cast; ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have hper : Complex.exp ((k : ℂ) * I * (Real.pi : ℝ)) =
        Complex.exp ((k : ℂ) * I * ((-Real.pi : ℝ) : ℂ)) := by
      have := Complex.exp_int_mul_two_pi_mul_I k
      rw [show (k : ℂ) * I * (Real.pi : ℝ) = (k : ℂ) * I * ((-Real.pi : ℝ) : ℂ) +
        k * (2 * Real.pi * I) by push_cast; ring, Complex.exp_add, this, mul_one]
    rw [hper, sub_self, zero_div]

/-! ## Two facts on Fourier coefficients and geometric sums (moved from
`Helmholtz/PositivityThreshold.lean` at the split, `adr/0007`) -/

/-- **The coefficients of an absolutely convergent Fourier series**: if
`F(x) = ∑ₙ aₙ e^{inx}` with `∑ |aₙ| < ∞`, then `∫_{-π}^{π} F(x) e^{-ikx} dx = 2π a_k`. -/
theorem integral_coeff_of_hasSum {a : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) {F : ℝ → ℂ}
    (hF : ∀ x : ℝ, HasSum (fun n : ℤ => a n * Complex.exp (((n * x : ℝ) : ℂ) * I)) (F x))
    (k : ℤ) :
    ∫ x in Icc (-π) π, F x * Complex.exp (-(((k * x : ℝ) : ℂ) * I)) =
      ((2 * π : ℝ) : ℂ) * a k := by
  set G : ℤ → ℝ → ℂ := fun n x => a n * Complex.exp (((((n - k : ℤ) : ℝ) * x : ℝ) : ℂ) * I)
    with hG
  have hint : ∀ x : ℝ, F x * Complex.exp (-(((k * x : ℝ) : ℂ) * I)) = ∑' n, G n x := by
    intro x
    rw [← (hF x).tsum_eq, ← tsum_mul_right]
    congr 1
    funext n
    simp only [hG]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hcont : ∀ n, Continuous (G n) := fun n => by
    simp only [hG]
    fun_prop
  have hGint : ∀ n, Integrable (G n) (volume.restrict (Icc (-π) π)) := fun n =>
    (hcont n).continuousOn.integrableOn_compact isCompact_Icc
  have hnorm : ∀ n x, ‖G n x‖ = ‖a n‖ := fun n x => by
    simp only [hG]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsum : Summable fun n => ∫ x in Icc (-π) π, ‖G n x‖ := by
    simp_rw [hnorm, integral_const]
    exact ha.const_smul _
  have hGn : ∀ n, ∫ x in Icc (-π) π, G n x =
      a n * (if n - k = 0 then ((2 * π : ℝ) : ℂ) else 0) := by
    intro n
    simp only [hG]
    rw [integral_const_mul, integral_Icc_exp_int]
  simp_rw [hint]
  rw [← integral_tsum_of_summable_integral_norm hGint hsum]
  simp_rw [hGn]
  rw [tsum_eq_single k (fun n hn => by simp [sub_eq_zero, hn])]
  simp only [sub_self, ite_true]
  ring

/-- `∑_{n ∈ ℤ} |z|^{|n|} < ∞` for `|z| < 1`. -/
theorem summable_pow_natAbs {z : ℝ} (hz : |z| < 1) :
    Summable fun n : ℤ => |z| ^ n.natAbs := by
  have hg : Summable fun n : ℕ => |z| ^ n := summable_geometric_of_lt_one (abs_nonneg z) hz
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using hg
  · simpa using hg


/-! ## Convolution on `ℤ` -/

section Conv

variable {f g k : ℤ → ℝ}

theorem summable_zdelta : Summable zdelta :=
  (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable.congr fun n => by simp [zdelta]

theorem tsum_zdelta : ∑' n, zdelta n = 1 := by
  rw [show zdelta = fun n => if n = 0 then (1 : ℝ) else 0 from rfl, tsum_ite_eq]

theorem summable_zconv_pair (hf : Summable f) (hg : Summable g) :
    Summable fun p : ℤ × ℤ => f p.1 * g (p.2 - p.1) := by
  have h := summable_mul_of_summable_norm hf.norm hg.norm
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1, p.2 + p.1)
      invFun := fun p => (p.1, p.2 - p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  rw [← e.summable_iff]
  refine h.congr fun p => ?_
  simp [e]

theorem summable_zconv_term (hf : Summable f) (hg : Summable g) (n : ℤ) :
    Summable fun m => f m * g (n - m) :=
  (summable_zconv_pair hf hg).prod_symm.prod_factor n

theorem summable_zconv (hf : Summable f) (hg : Summable g) : Summable (zconv f g) :=
  (summable_zconv_pair hf hg).prod_symm.prod

theorem tsum_zconv (hf : Summable f) (hg : Summable g) :
    ∑' n, zconv f g n = (∑' n, f n) * ∑' n, g n := by
  have h := summable_zconv_pair hf hg
  unfold zconv
  rw [h.tsum_comm (f := fun m n => f m * g (n - m)), ← tsum_mul_right]
  congr 1
  funext m
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.subRight m).tsum_eq g

theorem zconv_nonneg (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℤ) : 0 ≤ zconv f g n :=
  tsum_nonneg fun m => mul_nonneg (hf m) (hg _)

theorem zconv_comm (f g : ℤ → ℝ) : zconv f g = zconv g f := by
  funext n
  unfold zconv
  rw [← (Equiv.subLeft n).tsum_eq]
  congr 1
  funext m
  simp [mul_comm]

theorem zconv_zdelta_left (g : ℤ → ℝ) : zconv zdelta g = g := by
  funext n
  unfold zconv zdelta
  simp only [ite_mul, one_mul, zero_mul]
  rw [tsum_ite_eq, sub_zero]

theorem zconv_zdelta_right (f : ℤ → ℝ) : zconv f zdelta = f := by
  rw [zconv_comm, zconv_zdelta_left]

theorem zconv_assoc (hf : Summable f) (hg : Summable g) (hk : Summable k) :
    zconv (zconv f g) k = zconv f (zconv g k) := by
  funext n
  unfold zconv
  have hF : Summable fun p : ℤ × ℤ => f p.1 * g (p.2 - p.1) * k (n - p.2) := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ j, ‖k j‖ ≤ C :=
      ⟨∑' j, ‖k j‖, fun j => hk.norm.le_tsum j fun _ _ => norm_nonneg _⟩
    refine Summable.of_norm_bounded ((summable_zconv_pair hf hg).norm.mul_right C) fun p => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have e1 : ∀ m, (∑' j, f j * g (m - j)) * k (n - m) = ∑' j, f j * g (m - j) * k (n - m) :=
    fun m => tsum_mul_right.symm
  simp_rw [e1]
  rw [hF.tsum_comm (f := fun j m => f j * g (m - j) * k (n - m))]
  congr 1
  funext j
  rw [← tsum_mul_left, ← (Equiv.addRight j).tsum_eq]
  congr 1
  funext i
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [show n - (i + j) = n - j - i by abel]
  ring

/-- The convolution of two symmetric kernels is symmetric. -/
theorem zconv_symm (hf : ∀ n, f (-n) = f n) (hg : ∀ n, g (-n) = g n) (n : ℤ) :
    zconv f g (-n) = zconv f g n := by
  unfold zconv
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext m
  simp only [Equiv.neg_apply]
  rw [hf, show -n - -m = -(n - m) by ring, hg]

theorem summable_zconvPow (hf : Summable f) : ∀ j : ℕ, Summable (zconvPow f j)
  | 0 => summable_zdelta
  | j + 1 => summable_zconv (summable_zconvPow hf j) hf

theorem zconvPow_nonneg (hf : ∀ n, 0 ≤ f n) : ∀ (j : ℕ) (n : ℤ), 0 ≤ zconvPow f j n
  | 0, n => by unfold zconvPow zdelta; split_ifs <;> norm_num
  | j + 1, n => zconv_nonneg (zconvPow_nonneg hf j) hf n

theorem zconvPow_symm (hf : ∀ n, f (-n) = f n) : ∀ (j : ℕ) (n : ℤ),
    zconvPow f j (-n) = zconvPow f j n
  | 0, n => by unfold zconvPow zdelta; simp
  | j + 1, n => zconv_symm (zconvPow_symm hf j) hf n

theorem tsum_zconvPow (hf : Summable f) (h1 : ∑' n, f n = 1) :
    ∀ j : ℕ, ∑' n, zconvPow f j n = 1
  | 0 => tsum_zdelta
  | j + 1 => by
    rw [zconvPow, tsum_zconv (summable_zconvPow hf j) hf, tsum_zconvPow hf h1 j, h1, one_mul]

/-- Convolution with a summable kernel is linear in the other argument. -/
theorem zconv_add_smul_left {f f' : ℤ → ℝ} (hf : Summable f) (hf' : Summable f')
    (hg : Summable g) (a b : ℝ) :
    zconv (fun n => a * f n + b * f' n) g = fun n => a * zconv f g n + b * zconv f' g n := by
  funext n
  unfold zconv
  rw [← tsum_mul_left, ← tsum_mul_left, ← ((summable_zconv_term hf hg n).mul_left a).tsum_add
    ((summable_zconv_term hf' hg n).mul_left b)]
  congr 1
  funext m
  ring

end Conv

/-! ## Fourier series on `ℤ` -/

section Fourier

variable {f g : ℤ → ℝ}

theorem summable_lineFourier_term (hf : Summable f) (θ : ℝ) :
    Summable fun n : ℤ => (f n : ℂ) * cexp (((n * θ : ℝ) : ℂ) * I) :=
  Summable.of_norm (hf.norm.congr fun n => by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real])

/-- **The Fourier series of a convolution is the product.** -/
theorem lineFourierSeries_zconv (hf : Summable f) (hg : Summable g) (θ : ℝ) :
    lineFourierSeries (zconv f g) θ = lineFourierSeries f θ * lineFourierSeries g θ := by
  unfold lineFourierSeries
  set e : ℤ → ℂ := fun n => cexp (((n * θ : ℝ) : ℂ) * I) with he
  have hemul : ∀ m j, e (m + j) = e m * e j := fun m j => by
    simp only [he]; push_cast; rw [← Complex.exp_add]; ring_nf
  have hF : Summable fun p : ℤ × ℤ => (f p.1 : ℂ) * (g (p.2 - p.1) : ℂ) * e p.2 := by
    refine Summable.of_norm ((summable_zconv_pair hf hg).norm.congr fun p => ?_)
    simp only [he, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have e1 : ∀ n, ((zconv f g n : ℝ) : ℂ) * e n = ∑' m, (f m : ℂ) * (g (n - m) : ℂ) * e n := by
    intro n
    rw [zconv, Complex.ofReal_tsum, ← tsum_mul_right]
    congr 1
    funext m
    push_cast
    ring
  change ∑' n, ((zconv f g n : ℝ) : ℂ) * e n = (∑' n, (f n : ℂ) * e n) * ∑' n, (g n : ℂ) * e n
  simp_rw [e1]
  rw [hF.tsum_comm (f := fun m n => (f m : ℂ) * (g (n - m) : ℂ) * e n), ← tsum_mul_right]
  congr 1
  funext m
  rw [← tsum_mul_left, ← (Equiv.addRight m).tsum_eq]
  congr 1
  funext j
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [hemul]
  ring

theorem lineFourierSeries_zdelta (θ : ℝ) : lineFourierSeries zdelta θ = 1 := by
  unfold lineFourierSeries
  have : ∀ n : ℤ, ((zdelta n : ℝ) : ℂ) * cexp (((n * θ : ℝ) : ℂ) * I) =
      if n = 0 then 1 else 0 := by
    intro n
    unfold zdelta
    split_ifs with h
    · subst h; simp
    · simp
  simp_rw [this]
  rw [tsum_ite_eq]

theorem lineFourierSeries_zconvPow (hf : Summable f) (θ : ℝ) :
    ∀ j : ℕ, lineFourierSeries (zconvPow f j) θ = lineFourierSeries f θ ^ j
  | 0 => lineFourierSeries_zdelta θ
  | j + 1 => by
    rw [zconvPow, lineFourierSeries_zconv (summable_zconvPow hf j) hf,
      lineFourierSeries_zconvPow hf θ j, pow_succ]

/-- The Fourier series is linear. -/
theorem lineFourierSeries_add_smul (hf : Summable f) (hg : Summable g) (a b : ℝ) (θ : ℝ) :
    lineFourierSeries (fun n => a * f n + b * g n) θ =
      (a : ℂ) * lineFourierSeries f θ + (b : ℂ) * lineFourierSeries g θ := by
  unfold lineFourierSeries
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_lineFourier_term hf θ).mul_left (a : ℂ)).tsum_add
      ((summable_lineFourier_term hg θ).mul_left (b : ℂ))]
  congr 1
  funext n
  push_cast
  ring

/-- The reflected kernel has the reflected Fourier series. -/
theorem lineFourierSeries_reflect (f : ℤ → ℝ) (θ : ℝ) :
    lineFourierSeries (fun n => f (-n)) θ = lineFourierSeries f (-θ) := by
  unfold lineFourierSeries
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext n
  simp only [Equiv.neg_apply, neg_neg]
  congr 3
  push_cast
  ring

/-- **A summable kernel on `ℤ` is determined by its Fourier series**: the coefficient formula
`integral_coeff_of_hasSum` recovers `f k` as `(2π)⁻¹ ∫ f̂(ϑ)e^{-ikϑ} dϑ`. -/
theorem eq_of_lineFourierSeries_eq (hf : Summable f) (hg : Summable g)
    (h : ∀ θ, lineFourierSeries f θ = lineFourierSeries g θ) : f = g := by
  funext k
  have hc : ∀ (u : ℤ → ℝ), Summable u →
      ∫ x in Icc (-π) π, lineFourierSeries u x * cexp (-(((k * x : ℝ) : ℂ) * I)) =
        ((2 * π : ℝ) : ℂ) * (u k : ℂ) := fun u hu =>
    integral_coeff_of_hasSum (a := fun n => (u n : ℂ))
      (hu.norm.congr fun n => by rw [Complex.norm_real]) (fun x =>
        (summable_lineFourier_term hu x).hasSum) k
  have e := (hc f hf).symm.trans ((congrArg (fun F : ℝ → ℂ =>
    ∫ x in Icc (-π) π, F x * cexp (-(((k * x : ℝ) : ℂ) * I))) (funext h)).trans (hc g hg))
  have h2 : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  exact_mod_cast mul_left_cancel₀ h2 e

/-- **The power of a convolution** is the convolution of the powers. -/
theorem zconvPow_zconv (hf : Summable f) (hg : Summable g) (j : ℕ) :
    zconvPow (zconv f g) j = zconv (zconvPow f j) (zconvPow g j) := by
  refine eq_of_lineFourierSeries_eq (summable_zconvPow (summable_zconv hf hg) j)
    (summable_zconv (summable_zconvPow hf j) (summable_zconvPow hg j)) fun θ => ?_
  rw [lineFourierSeries_zconvPow (summable_zconv hf hg), lineFourierSeries_zconv hf hg,
    lineFourierSeries_zconv (summable_zconvPow hf j) (summable_zconvPow hg j),
    lineFourierSeries_zconvPow hf, lineFourierSeries_zconvPow hg, mul_pow]

end Fourier

/-! ## The geometric kernels -/

section Geometric

variable {a : ℝ}

theorem summable_pow_natAbs_of_nonneg (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable fun n : ℤ => a ^ n.natAbs := by
  have := summable_pow_natAbs (z := a) (by rwa [abs_of_nonneg ha0])
  simpa [abs_of_nonneg ha0] using this

theorem geomKernel_zero : geomKernel 0 = zdelta := by
  funext n
  unfold geomKernel zdelta
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn]

theorem summable_geomKernel (ha0 : 0 ≤ a) (ha1 : a < 1) : Summable (geomKernel a) :=
  (summable_pow_natAbs_of_nonneg ha0 ha1).mul_left _

theorem geomKernel_nonneg' (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℤ) : 0 ≤ geomKernel a n :=
  mul_nonneg (div_nonneg (by linarith) (by linarith)) (pow_nonneg ha0 _)

theorem tsum_geomKernel (ha0 : 0 ≤ a) (ha1 : a < 1) : ∑' n, geomKernel a n = 1 := by
  rcases ha0.lt_or_eq with ha0 | rfl
  · exact (hasSum_geomKernel ha0 ha1).tsum_eq
  · rw [geomKernel_zero, tsum_zdelta]

theorem geomKernel_symm (n : ℤ) : geomKernel a (-n) = geomKernel a n := by
  simp [geomKernel]

/-- **The transfer of the geometric kernel**, `(1-a)²/(1 - 2a cos ϑ + a²)`, for `0 ≤ a < 1`. -/
theorem lineFourierSeries_geomKernel (ha0 : 0 ≤ a) (ha1 : a < 1) (θ : ℝ) :
    lineFourierSeries (geomKernel a) θ =
      (((1 - a) ^ 2 / (1 - 2 * a * Real.cos θ + a ^ 2) : ℝ) : ℂ) := by
  rcases ha0.lt_or_eq with ha0 | rfl
  · have h := (charFun_gridLaw (h := 1) (geomKernel_nonneg ha0 ha1) (hasSum_geomKernel ha0 ha1)
      θ).symm.trans (charFun_geomMask ha0 ha1 1 θ)
    simpa only [one_mul] using h
  · rw [geomKernel_zero, lineFourierSeries_zdelta]
    simp

/-- `(1 - ae^{iϑ})(1 - ae^{-iϑ}) = 1 - 2a cos ϑ + a²`, and neither factor vanishes for
`0 ≤ a < 1`. -/
theorem geom_factor_prod (θ : ℝ) :
    (1 - (a : ℂ) * cexp ((θ : ℂ) * I)) * (1 - (a : ℂ) * cexp (-((θ : ℂ) * I))) =
      ((1 - 2 * a * Real.cos θ + a ^ 2 : ℝ) : ℂ) := by
  have hzw : cexp ((θ : ℂ) * I) * cexp (-((θ : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hcos : cexp ((θ : ℂ) * I) + cexp (-((θ : ℂ) * I)) = 2 * Complex.cos (θ : ℂ) := by
    rw [Complex.two_cos, neg_mul]
  push_cast
  linear_combination (a : ℂ) ^ 2 * hzw - (a : ℂ) * hcos

theorem geom_factor_ne_zero (ha0 : 0 ≤ a) (ha1 : a < 1) (θ : ℝ) :
    (1 - (a : ℂ) * cexp ((θ : ℂ) * I)) ≠ 0 := by
  intro h0
  have h1 : (a : ℂ) * cexp ((θ : ℂ) * I) = 1 := by linear_combination (-1 : ℂ) * h0
  have : ‖(a : ℂ) * cexp ((θ : ℂ) * I)‖ = 1 := by rw [h1]; simp
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ha0] at this
  linarith

theorem geom_factor_ne_zero' (ha0 : 0 ≤ a) (ha1 : a < 1) (θ : ℝ) :
    (1 - (a : ℂ) * cexp (-((θ : ℂ) * I))) ≠ 0 := by
  have := geom_factor_ne_zero ha0 ha1 (-θ)
  simpa [neg_mul] using this

theorem geom_denom_pos' (ha0 : 0 ≤ a) (ha1 : a < 1) (θ : ℝ) :
    0 < 1 - 2 * a * Real.cos θ + a ^ 2 := by
  nlinarith [Real.cos_le_one θ]

theorem summable_oneSidedGeom (ha0 : 0 ≤ a) (ha1 : a < 1) : Summable (oneSidedGeom a) := by
  refine Summable.of_norm_bounded ((summable_pow_natAbs_of_nonneg ha0 ha1).mul_left (1 - a))
    fun n => ?_
  unfold oneSidedGeom
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (pow_nonneg ha0 _))]
    rw [show n.toNat = n.natAbs by omega]
  · simp only [norm_zero]
    exact mul_nonneg (by linarith) (pow_nonneg ha0 _)

theorem oneSidedGeom_nonneg (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℤ) : 0 ≤ oneSidedGeom a n := by
  unfold oneSidedGeom
  split_ifs
  · exact mul_nonneg (by linarith) (pow_nonneg ha0 _)
  · exact le_rfl

theorem hasSum_oneSidedGeom (ha0 : 0 ≤ a) (ha1 : a < 1) : HasSum (oneSidedGeom a) 1 := by
  have hg := hasSum_geometric_of_lt_one ha0 ha1
  have h1 : HasSum (fun n : ℕ => oneSidedGeom a n) ((1 - a) * (1 - a)⁻¹) :=
    (hg.mul_left (1 - a)).congr_fun fun n => by simp [oneSidedGeom]
  have h2 : HasSum (fun n : ℕ => oneSidedGeom a (-((n : ℤ) + 1))) 0 :=
    hasSum_zero.congr_fun fun n => by
      simp only [oneSidedGeom]
      rw [if_neg (by omega)]
  have h3 := HasSum.of_nat_of_neg_add_one h1 h2
  rwa [add_zero, mul_inv_cancel₀ (by linarith)] at h3

/-- **The transfer of the one-sided geometric law**, `(1-a)/(1 - ae^{iϑ})`. -/
theorem lineFourierSeries_oneSidedGeom (ha0 : 0 ≤ a) (ha1 : a < 1) (θ : ℝ) :
    lineFourierSeries (oneSidedGeom a) θ =
      ((1 - a : ℝ) : ℂ) / (1 - (a : ℂ) * cexp ((θ : ℂ) * I)) := by
  have hz : ‖(a : ℂ) * cexp ((θ : ℂ) * I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ha0]
    exact ha1
  have h1 : HasSum (fun n : ℕ => ((oneSidedGeom a n : ℝ) : ℂ) * cexp (((n * θ : ℝ) : ℂ) * I))
      (((1 - a : ℝ) : ℂ) * (1 - (a : ℂ) * cexp ((θ : ℂ) * I))⁻¹) := by
    refine ((hasSum_geometric_of_norm_lt_one hz).mul_left ((1 - a : ℝ) : ℂ)).congr_fun
      fun n => ?_
    have e1 : oneSidedGeom a (n : ℤ) = (1 - a) * a ^ n := by
      simp only [oneSidedGeom, Nat.cast_nonneg, if_true, Int.toNat_natCast]
    have e2 : cexp ((((n : ℝ) * θ : ℝ) : ℂ) * I) = cexp ((θ : ℂ) * I) ^ n := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e1, e2, mul_pow, Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]
  have h2 : HasSum (fun n : ℕ =>
      ((oneSidedGeom a (-((n : ℤ) + 1)) : ℝ) : ℂ) * cexp ((((-((n : ℤ) + 1) : ℤ) * θ : ℝ) : ℂ) * I))
      0 :=
    hasSum_zero.congr_fun fun n => by
      have e : oneSidedGeom a (-((n : ℤ) + 1)) = 0 := by
        simp only [oneSidedGeom]
        rw [if_neg (by omega)]
      rw [e, Complex.ofReal_zero, zero_mul]
  have h3 := HasSum.of_nat_of_neg_add_one
    (f := fun n : ℤ => ((oneSidedGeom a n : ℝ) : ℂ) * cexp (((n * θ : ℝ) : ℂ) * I)) h1 h2
  rw [lineFourierSeries, h3.tsum_eq, add_zero, div_eq_mul_inv]

end Geometric

end Pyramids
