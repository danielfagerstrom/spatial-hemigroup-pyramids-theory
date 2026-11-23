/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.ZConv
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.NumberTheory.ZetaValues

/-!
# `prop:sampled-laplace-exact`: the kernel, its transfer, the periodization, (1) and (3)

Blueprint: `blueprint/src/parts/02-line.tex`, `prop:sampled-laplace-exact`. Wave 3f: the
declarations `sampled_laplace_exact_sample`, `_transfer`, `_periodization`, `_1_factor`,
`_1_hemigroup`, `_1_recursion`, `_1_powers` and `_3` moved here from `PyramidsSkeleton.Ch02Line`,
their statements unchanged.

* **The transfer** is the geometric kernel's (`lineFourierSeries_geomKernel`), also at `a_0 = 0`.
* **The periodization** is Poisson's summation formula (Mathlib's
  `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`) for `f(v) = h ℓ_t(hv) e^{iωhv}`: its
  samples sum to `C_t λ̂_t(hω)`, and its Fourier transform at `ξ` is `ℓ̂_t(ω - 2πξ/h)` (the
  substitution `y = hv` in `fourierLine_laplace`). Both decay like `|x|⁻²`.
* **(3)** is the periodization at `ω` and at `0`, `λ̂_t(0) = 1`, and `∑_{n ≠ 0} n⁻² = π²/3`
  (Mathlib's `hasSum_zeta_two`).
* **(1)**: the two factors are `(1-a_t)(1-a_s z)/((1-a_s)(1-a_t z))`, `z = e^{±iϑ}`; summable
  kernels on `ℤ` are determined by their transfers (`eq_of_lineFourierSeries_eq`), which gives
  `λ_{0,t} = λ_t`, the composition rule and the powers; the transfer at `ϑ = π`,
  `((1-a)/(1+a))²`, separates `λ_{s,t}` from `δ₀`; `a_t = expNegInvGlue (t/h)` is continuous in
  `t`. The recursion is the
  identity `F(m) = (1 - a + pa)δ₀(m) - paδ₀(m-1) + aF(m-1)` of the forward factor, and two bounded
  solutions differ by a bounded solution of `e(n) = ae(n-1)`, which vanishes (`geom_homog_zero`).
-/

namespace Pyramids

open MeasureTheory Set Filter Complex Asymptotics
open ScaleSpace (laplaceDensity)
open scoped Topology Real FourierTransform

/-! ## The ratio `a_t` -/

section Ratio

variable {h : ℝ}

theorem slRatio_nonneg (h t : ℝ) : 0 ≤ slRatio h t := by
  unfold slRatio; split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem slRatio_of_pos {t : ℝ} (ht : 0 < t) : slRatio h t = Real.exp (-h / t) := by
  rw [slRatio, if_pos ht]

theorem slRatio_zero (h : ℝ) : slRatio h 0 = 0 := by rw [slRatio, if_neg (lt_irrefl 0)]

theorem slRatio_pos {t : ℝ} (ht : 0 < t) : 0 < slRatio h t := by
  rw [slRatio_of_pos ht]; exact Real.exp_pos _

theorem slRatio_lt_one (hh : 0 < h) (t : ℝ) : slRatio h t < 1 := by
  unfold slRatio; split_ifs with ht
  · exact gridA_lt_one hh ht
  · exact one_pos

theorem slRatio_lt (hh : 0 < h) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    slRatio h s < slRatio h t := by
  have ht : 0 < t := hs.trans_lt hst
  rcases hs.lt_or_eq with hs | rfl
  · rw [slRatio_of_pos hs, slRatio_of_pos ht]
    refine Real.exp_lt_exp.2 ?_
    rw [div_lt_div_iff₀ hs ht]
    nlinarith
  · rw [slRatio_zero]; exact slRatio_pos ht

theorem continuous_slRatio (hh : 0 < h) : Continuous (slRatio h) := by
  have e : slRatio h = fun t => expNegInvGlue (t / h) := by
    funext t
    unfold slRatio expNegInvGlue
    by_cases ht : 0 < t
    · rw [if_pos ht, if_neg (not_le.2 (div_pos ht hh)), inv_div, neg_div]
    · rw [if_neg ht, if_pos (div_nonpos_of_nonpos_of_nonneg (not_lt.1 ht) hh.le)]
  rw [e]
  exact (expNegInvGlue.contDiff (n := 0)).continuous.comp (continuous_id.div_const h)

end Ratio

/-! ## The kernel and its transfer -/

/-- `e^{-|nc|/x} = (e^{-c/x})^{|n|}` for `c ≥ 0`. -/
theorem exp_neg_abs_int_mul {c : ℝ} (hc : 0 ≤ c) (x : ℝ) (n : ℤ) :
    Real.exp (-(|n * c| / x)) = Real.exp (-c / x) ^ n.natAbs := by
  rw [← Real.exp_nat_mul, abs_mul, abs_of_nonneg hc, Nat.cast_natAbs, Int.cast_abs]
  congr 1
  ring

/-- **`prop:sampled-laplace-exact`, the kernel.** For `t > 0`, `λ_t` is the Laplace kernel of
range `t` sampled on `hℤ` and renormalized (it is `prop:recursion-helmholtz`'s `sampledLaplace`);
`λ_0 = δ₀`. -/
theorem sampled_laplace_exact_sample {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : 0 < t) :
    (∃ κ : ℝ, 0 < κ ∧ ∀ n : ℤ, slKernel h t n = κ * laplaceDensity t (n * h)) ∧
      slKernel h t = sampledLaplace h t ∧ slKernel h 0 = zdelta := by
  set a := Real.exp (-h / t) with ha
  have ha1 : a < 1 := gridA_lt_one hh ht
  refine ⟨⟨2 * t * ((1 - a) / (1 + a)), by
    have : 0 < 1 - a := by linarith
    have : 0 < 1 + a := by linarith [Real.exp_pos (-h / t)]
    positivity, fun n => ?_⟩, ?_, ?_⟩
  · rw [slKernel, slRatio_of_pos ht, ScaleSpace.laplaceDensity, exp_neg_abs_int_mul hh.le,
      geomKernel, ← ha]
    field_simp
  · funext n
    rw [slKernel, slRatio_of_pos ht, geomKernel, sampledLaplace]
  · rw [slKernel, slRatio_zero, geomKernel_zero]

/-- **`prop:sampled-laplace-exact`, the transfer (`eq:sampled-laplace-transfer`).** -/
theorem sampled_laplace_exact_transfer {h : ℝ} (hh : 0 < h) {t : ℝ} (θ : ℝ) :
    lineFourierSeries (slKernel h t) θ =
        (((1 - slRatio h t) ^ 2 / (1 - 2 * slRatio h t * Real.cos θ + slRatio h t ^ 2) : ℝ) : ℂ) ∧
      lineFourierSeries (slKernel h t) θ =
        ((1 - slRatio h t : ℝ) : ℂ) ^ 2 /
          ((1 - (slRatio h t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            (1 - (slRatio h t : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)))) := by
  have h1 := lineFourierSeries_geomKernel (slRatio_nonneg h t) (slRatio_lt_one hh t) θ
  refine ⟨h1, ?_⟩
  rw [slKernel, h1, geom_factor_prod]
  push_cast
  ring

/-- `λ̂_t(ϑ)` as a real number, `(1-a_t)²/(1 - 2a_t cos ϑ + a_t²) > 0`. -/
noncomputable def slTransfer (h t θ : ℝ) : ℝ :=
  (1 - slRatio h t) ^ 2 / (1 - 2 * slRatio h t * Real.cos θ + slRatio h t ^ 2)

theorem slTransfer_pos {h : ℝ} (hh : 0 < h) (t θ : ℝ) : 0 < slTransfer h t θ := by
  have h1 := slRatio_lt_one hh t
  have : 0 < 1 - slRatio h t := by linarith
  exact div_pos (by positivity) (geom_denom_pos' (slRatio_nonneg h t) h1 θ)

theorem lineFourierSeries_slKernel {h : ℝ} (hh : 0 < h) (t θ : ℝ) :
    lineFourierSeries (slKernel h t) θ = (slTransfer h t θ : ℂ) :=
  lineFourierSeries_geomKernel (slRatio_nonneg h t) (slRatio_lt_one hh t) θ

theorem continuous_slTransfer {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    Continuous fun t => slTransfer h t θ := by
  have hc := continuous_slRatio hh
  refine Continuous.div (by fun_prop) (by fun_prop) fun t => ?_
  exact (geom_denom_pos' (slRatio_nonneg h t) (slRatio_lt_one hh t) θ).ne'

theorem slTransfer_zero {h : ℝ} (hh : 0 < h) (t : ℝ) : slTransfer h t 0 = 1 := by
  unfold slTransfer
  rw [Real.cos_zero]
  have : 1 - 2 * slRatio h t * 1 + slRatio h t ^ 2 = (1 - slRatio h t) ^ 2 := by ring
  have h1 : (1 - slRatio h t) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [slRatio_lt_one hh t])
  rw [this, div_self h1]

/-! ## The periodization -/

section Periodization

variable {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
include hh ht

/-- **The Lorentzian decays like `|ξ|⁻²`.** -/
theorem lorentz_isBigO (ω : ℝ) :
    (fun ξ : ℝ => (1 + t ^ 2 * (ω + 2 * π * ξ / h) ^ 2)⁻¹) =O[cocompact ℝ]
      fun ξ : ℝ => |ξ| ^ (-2 : ℝ) := by
  refine IsBigO.of_bound (h ^ 2 / (t ^ 2 * π ^ 2)) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (h * |ω| / π + 1)] with ξ hξ
  rw [Real.norm_eq_abs] at hξ
  have hω : 0 ≤ h * |ω| / π := by positivity
  have hξ0 : 0 < |ξ| := by linarith
  have hr : |ξ| ^ (-2 : ℝ) = (ξ ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg _), show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast,
      sq_abs]
  have hX : 0 ≤ (ω + 2 * π * ξ / h) ^ 2 := sq_nonneg _
  have hξ2 : 0 < ξ ^ 2 := by rw [← sq_abs]; positivity
  rw [hr, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
    abs_of_pos (inv_pos.2 hξ2)]
  have hb : π * |ξ| / h ≤ |ω + 2 * π * ξ / h| := by
    have h1 : |2 * π * ξ / h| = 2 * π * |ξ| / h := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_of_pos hh]
    have h2 : |2 * π * ξ / h| - |ω| ≤ |ω + 2 * π * ξ / h| := by
      have := abs_sub_abs_le_abs_sub (2 * π * ξ / h) (-ω)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      exact this
    have h3 : |ω| ≤ π * |ξ| / h := by
      rw [le_div_iff₀ hh]
      have := mul_le_mul_of_nonneg_left hξ Real.pi_pos.le
      have e : π * (h * |ω| / π + 1) = h * |ω| + π := by field_simp
      nlinarith [abs_nonneg ω, Real.pi_pos]
    rw [h1] at h2
    have e : 2 * π * |ξ| / h = π * |ξ| / h + π * |ξ| / h := by ring
    linarith
  have hsq : (π * |ξ| / h) ^ 2 ≤ (ω + 2 * π * ξ / h) ^ 2 := by
    rw [← sq_abs (ω + _)]
    exact pow_le_pow_left₀ (by positivity) hb 2
  calc (1 + t ^ 2 * (ω + 2 * π * ξ / h) ^ 2)⁻¹ ≤ (t ^ 2 * (π * |ξ| / h) ^ 2)⁻¹ := by
        refine inv_anti₀ (by positivity) ?_
        nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg t)]
    _ = h ^ 2 / (t ^ 2 * π ^ 2) * (ξ ^ 2)⁻¹ := by
        rw [div_pow, mul_pow, sq_abs]
        field_simp

theorem summable_lorentz (ω : ℝ) :
    Summable fun n : ℤ => (1 + t ^ 2 * (ω + 2 * π * n / h) ^ 2)⁻¹ :=
  summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((lorentz_isBigO hh ht ω).comp_tendsto Int.tendsto_coe_cofinite)

/-- The function `f(v) = h e^{iωhv} ℓ_t(hv)` whose samples and transform the periodization
compares. -/
noncomputable def periodFun (h t ω : ℝ) (v : ℝ) : ℂ :=
  (h : ℂ) * (cexp (((ω * (h * v) : ℝ) : ℂ) * I) * (laplaceDensity t (h * v) : ℂ))

omit hh ht in
theorem continuous_periodFun (ω : ℝ) : Continuous (periodFun h t ω) := by
  unfold periodFun
  have := ScaleSpace.continuous_laplaceDensity t
  fun_prop

theorem periodFun_isBigO (ω : ℝ) :
    periodFun h t ω =O[cocompact ℝ] fun v : ℝ => |v| ^ (-2 : ℝ) := by
  refine IsBigO.of_bound (t / h) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop 1] with v hv
  rw [Real.norm_eq_abs] at hv
  have hv0 : 0 < |v| := by linarith
  have hr : |v| ^ (-2 : ℝ) = (v ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg _), show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast,
      sq_abs]
  have hv2 : 0 < v ^ 2 := by rw [← sq_abs]; positivity
  rw [hr, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hv2)]
  unfold periodFun
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hh,
    abs_of_nonneg (ScaleSpace.laplaceDensity_nonneg ht _), ScaleSpace.laplaceDensity]
  -- `e^{-y} ≤ 2/y²` at `y = h|v|/t`
  set y := |h * v| / t with hy
  have hy0 : 0 < y := by rw [hy, abs_mul, abs_of_pos hh]; positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy0.le
  have hexp : Real.exp (-y) ≤ 2 / y ^ 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    nlinarith
  have hyv : y ^ 2 = h ^ 2 * v ^ 2 / t ^ 2 := by
    rw [hy, div_pow, sq_abs, mul_pow]
  calc h * ((2 * t)⁻¹ * Real.exp (-y)) ≤ h * ((2 * t)⁻¹ * (2 / y ^ 2)) := by
        gcongr
    _ = t / h * (v ^ 2)⁻¹ := by
        rw [hyv]
        field_simp

/-- **The Fourier transform of `f`** is the shifted Lorentzian `ℓ̂_t(ω - 2πξ/h)`. -/
theorem fourier_periodFun (ω ξ : ℝ) :
    𝓕 (periodFun h t ω) ξ = (((1 + t ^ 2 * (-ω + 2 * π * ξ / h) ^ 2)⁻¹ : ℝ) : ℂ) := by
  set ω' := ω - 2 * π * ξ / h with hω'
  set G : ℝ → ℂ := fun y => cexp (((ω' * y : ℝ) : ℂ) * I) * (laplaceDensity t y : ℂ) with hG
  have hpt : ∀ v : ℝ, 𝐞 (-(v * ξ)) • periodFun h t ω v = (h : ℂ) * G (h * v) := by
    intro v
    have e : cexp (((2 * π * -(v * ξ) : ℝ) : ℂ) * I) * cexp (((ω * (h * v) : ℝ) : ℂ) * I) =
        cexp (((ω' * (h * v) : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hω']
      have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      push_cast
      field_simp
      ring
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, periodFun, hG]
    simp only
    rw [← e]
    ring
  rw [Real.fourier_real_eq]
  simp_rw [hpt]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun y => G y) h, abs_inv,
    abs_of_pos hh, Complex.real_smul, ← mul_assoc]
  have e : (h : ℂ) * ((h⁻¹ : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_inv]; exact mul_inv_cancel₀ (by exact_mod_cast hh.ne')
  rw [e, one_mul]
  have hF := fourierLine_laplace ht ω'
  rw [fourierLine] at hF
  rw [hF, hω']
  congr 2
  ring

end Periodization

/-- **`prop:sampled-laplace-exact`, the periodization.** At `ϑ = hω` the transfer is
`C_t⁻¹ ∑_n (1 + t²(ω + 2πn/h)²)⁻¹`, `C_t = (h/2t)(1 + a_t)/(1 - a_t)`, the series converging. -/
theorem sampled_laplace_exact_periodization {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : 0 < t) (ω : ℝ) :
    (Summable fun n : ℤ => (1 + t ^ 2 * (ω + 2 * Real.pi * n / h) ^ 2)⁻¹) ∧
      lineFourierSeries (slKernel h t) (h * ω) =
        ((((h / (2 * t)) * ((1 + slRatio h t) / (1 - slRatio h t)))⁻¹ *
          ∑' n : ℤ, (1 + t ^ 2 * (ω + 2 * Real.pi * n / h) ^ 2)⁻¹ : ℝ) : ℂ) := by
  refine ⟨summable_lorentz hh ht ω, ?_⟩
  set a := slRatio h t with ha
  have ha0 : 0 < a := slRatio_pos ht
  have ha1 : a < 1 := slRatio_lt_one hh t
  set C : ℝ := (h / (2 * t)) * ((1 + a) / (1 - a)) with hC
  have hC0 : C ≠ 0 := by
    have : 0 < 1 - a := by linarith
    rw [hC]; positivity
  -- Poisson's formula at `x = 0`
  have hFf : Summable fun n : ℤ => 𝓕 (periodFun h t ω) n := by
    simp_rw [fourier_periodFun hh ht]
    exact Complex.summable_ofReal.2 (summable_lorentz hh ht (-ω))
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (continuous_periodFun ω)
    one_lt_two (periodFun_isBigO hh ht ω) hFf 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hP
  -- the samples
  have hL : ∑' n : ℤ, periodFun h t ω n = (C : ℂ) * lineFourierSeries (slKernel h t) (h * ω) := by
    rw [lineFourierSeries, ← tsum_mul_left]
    congr 1
    funext n
    rw [periodFun, slKernel, geomKernel, ← ha, ScaleSpace.laplaceDensity,
      show h * (n : ℝ) = n * h by ring, exp_neg_abs_int_mul hh.le, ← slRatio_of_pos ht, ← ha]
    have h1 : (1 : ℂ) - a ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) - a ≠ 0)
    have h2 : (1 : ℂ) + a ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) + a ≠ 0)
    have h3 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [show ((ω * (n * h) : ℝ) : ℂ) = ((n * (h * ω) : ℝ) : ℂ) by push_cast; ring, hC]
    push_cast
    field_simp
  -- the transforms
  have hR : ∑' n : ℤ, 𝓕 (periodFun h t ω) n =
      ((∑' n : ℤ, (1 + t ^ 2 * (ω + 2 * π * n / h) ^ 2)⁻¹ : ℝ) : ℂ) := by
    simp_rw [fourier_periodFun hh ht]
    rw [← Complex.ofReal_tsum, ← (Equiv.neg ℤ).tsum_eq]
    congr 2
    funext n
    simp only [Equiv.neg_apply, Int.cast_neg]
    ring
  rw [hL, hR] at hP
  rw [Complex.ofReal_mul, ← hP, Complex.ofReal_inv, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hC0), one_mul]


/-! ## (3): aliasing -/

/-- `∑_{n ∈ ℤ} 1/n² = π²/3`, the term at `n = 0` being `1/0 = 0`. -/
theorem hasSum_int_one_div_sq : HasSum (fun n : ℤ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 3) := by
  have h1 : HasSum (fun n : ℕ => 1 / (((n : ℤ) : ℝ)) ^ 2) (π ^ 2 / 6) :=
    hasSum_zeta_two.congr_fun fun n => by rw [Int.cast_natCast]
  have h2 : HasSum (fun n : ℕ => 1 / (((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    rw [Finset.sum_range_one, Nat.cast_zero, zero_pow two_ne_zero, div_zero, sub_zero] at this
    refine this.congr_fun fun n => ?_
    push_cast
    ring
  have h3 := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => 1 / (n : ℝ) ^ 2) h1 h2
  rwa [show π ^ 2 / 6 + π ^ 2 / 6 = π ^ 2 / 3 by ring] at h3

/-- For `n ≠ 0`, `(1 + t²(2πn/h)²)⁻¹ < (h²/(4π²t²)) n⁻²`. -/
theorem alias_term_lt {h t : ℝ} (hh : 0 < h) (ht : 0 < t) {n : ℤ} (hn : n ≠ 0) :
    (1 + t ^ 2 * (0 + 2 * π * n / h) ^ 2)⁻¹ < h ^ 2 / (4 * π ^ 2 * t ^ 2) * (1 / (n : ℝ) ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := by positivity
  have hX : 0 < t ^ 2 * (0 + 2 * π * n / h) ^ 2 := by
    rw [zero_add]
    have : 2 * π * (n : ℝ) / h ≠ 0 :=
      div_ne_zero (mul_ne_zero (by positivity) hn') hh.ne'
    exact mul_pos (by positivity) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 this)))
  have e : h ^ 2 / (4 * π ^ 2 * t ^ 2) * (1 / (n : ℝ) ^ 2) =
      (t ^ 2 * (0 + 2 * π * n / h) ^ 2)⁻¹ := by
    have := Real.pi_pos
    field_simp
    ring
  rw [e]
  exact inv_strictAnti₀ hX (by linarith)

/-- **`prop:sampled-laplace-exact`(3), aliasing.** The aliased mass converges,
`λ̂_t(hω) = ((1 + t²ω²)⁻¹ + α_t(ω))/(1 + α_t(0))`, and `0 < α_t(0) < h²/(12t²)`. -/
theorem sampled_laplace_exact_3 {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : 0 < t) (ω : ℝ) :
    (Summable fun n : ℤ =>
      if n = 0 then (0 : ℝ) else (1 + t ^ 2 * (ω + 2 * Real.pi * n / h) ^ 2)⁻¹) ∧
      lineFourierSeries (slKernel h t) (h * ω) =
        ((((1 + t ^ 2 * ω ^ 2)⁻¹ + aliasedMass h t ω) / (1 + aliasedMass h t 0) : ℝ) : ℂ) ∧
      0 < aliasedMass h t 0 ∧ aliasedMass h t 0 < h ^ 2 / (12 * t ^ 2) := by
  have hS : ∀ ω' : ℝ, Summable fun n : ℤ =>
      if n = 0 then (0 : ℝ) else (1 + t ^ 2 * (ω' + 2 * π * n / h) ^ 2)⁻¹ := fun ω' =>
    (summable_lorentz hh ht ω').of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      fun n => by split_ifs <;> [positivity; exact le_rfl]
  set P : ℝ → ℝ := fun ω' => ∑' n : ℤ, (1 + t ^ 2 * (ω' + 2 * π * n / h) ^ 2)⁻¹ with hPdef
  have hP : ∀ ω', P ω' = (1 + t ^ 2 * ω' ^ 2)⁻¹ + aliasedMass h t ω' := by
    intro ω'
    change (∑' n : ℤ, (1 + t ^ 2 * (ω' + 2 * π * n / h) ^ 2)⁻¹) = _
    rw [(summable_lorentz hh ht ω').tsum_eq_add_tsum_ite 0, aliasedMass]
    simp
  set C : ℝ := (h / (2 * t)) * ((1 + slRatio h t) / (1 - slRatio h t)) with hC
  have h0 := (sampled_laplace_exact_periodization hh ht 0).2
  rw [mul_zero, lineFourierSeries_slKernel hh, slTransfer_zero hh] at h0
  have hC1 : C⁻¹ * P 0 = 1 := by exact_mod_cast h0.symm
  have hP0 : P 0 ≠ 0 := by
    intro h1; rw [h1, mul_zero] at hC1; exact zero_ne_one hC1
  have hα0 : 0 < aliasedMass h t 0 := by
    refine (hS 0).tsum_pos (fun n => by split_ifs <;> positivity) 1 ?_
    rw [if_neg one_ne_zero]
    positivity
  refine ⟨hS ω, ?_, hα0, ?_⟩
  · have hP0' : 1 + aliasedMass h t 0 = P 0 := by rw [hP 0]; simp
    rw [(sampled_laplace_exact_periodization hh ht ω).2, ← hP, hP0']
    change ((C⁻¹ * P ω : ℝ) : ℂ) = ((P ω / P 0 : ℝ) : ℂ)
    congr 1
    have : C⁻¹ = (P 0)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left hC1
    rw [this, div_eq_inv_mul]
  · have hb := hasSum_int_one_div_sq.mul_left (h ^ 2 / (4 * π ^ 2 * t ^ 2))
    have hlt : aliasedMass h t 0 < ∑' n : ℤ, h ^ 2 / (4 * π ^ 2 * t ^ 2) * (1 / (n : ℝ) ^ 2) := by
      refine (hS 0).tsum_lt_tsum (i := 1) (fun n => ?_) ?_ hb.summable
      · split_ifs with hn
        · subst hn; simp
        · exact (alias_term_lt hh ht hn).le
      · rw [if_neg one_ne_zero]
        exact alias_term_lt hh ht one_ne_zero
    rw [hb.tsum_eq] at hlt
    have e : h ^ 2 / (4 * π ^ 2 * t ^ 2) * (π ^ 2 / 3) = h ^ 2 / (12 * t ^ 2) := by
      have := Real.pi_pos
      field_simp
      ring
    rwa [e] at hlt

/-! ## (1): the factorization -/

section Factor

variable {h : ℝ} (hh : 0 < h)
include hh

theorem slMix_mem {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    0 ≤ slMix h s t ∧ slMix h s t < 1 := by
  have ht := hs.trans_lt hst
  have hb0 := slRatio_nonneg h s
  have hb1 := slRatio_lt_one hh s
  have ha0 := slRatio_pos (h := h) ht
  have ha1 := slRatio_lt_one hh t
  have hab := slRatio_lt hh hs hst
  unfold slMix
  constructor
  · exact div_nonneg (mul_nonneg hb0 (by linarith)) (mul_nonneg ha0.le (by linarith))
  · rw [div_lt_one (mul_pos ha0 (by linarith))]
    nlinarith

omit hh in
theorem slForward_eq (s t : ℝ) :
    slForward h s t = fun n => slMix h s t * zdelta n +
      (1 - slMix h s t) * oneSidedGeom (slRatio h t) n := rfl

theorem summable_slForward (s t : ℝ) : Summable (slForward h s t) := by
  rw [slForward_eq]
  exact (summable_zdelta.mul_left _).add
    ((summable_oneSidedGeom (slRatio_nonneg h t) (slRatio_lt_one hh t)).mul_left _)

theorem summable_slBackward (s t : ℝ) : Summable (slBackward h s t) :=
  (Equiv.neg ℤ).summable_iff.2 (summable_slForward hh s t)

theorem tsum_slForward (s t : ℝ) : ∑' n, slForward h s t n = 1 := by
  rw [slForward_eq, (summable_zdelta.mul_left _).tsum_add
    ((summable_oneSidedGeom (slRatio_nonneg h t) (slRatio_lt_one hh t)).mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_zdelta,
    (hasSum_oneSidedGeom (slRatio_nonneg h t) (slRatio_lt_one hh t)).tsum_eq]
  ring

theorem tsum_slBackward (s t : ℝ) : ∑' n, slBackward h s t n = 1 := by
  rw [← tsum_slForward hh s t]
  exact (Equiv.neg ℤ).tsum_eq (slForward h s t)

theorem slForward_nonneg {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (n : ℤ) :
    0 ≤ slForward h s t n := by
  have hp := slMix_mem hh hs hst
  rw [slForward_eq]
  refine add_nonneg (mul_nonneg hp.1 ?_) (mul_nonneg (by linarith)
    (oneSidedGeom_nonneg (slRatio_nonneg h t) (slRatio_lt_one hh t) n))
  unfold zdelta; split_ifs <;> norm_num

/-- The transfer of the forward factor, `p + (1-p)(1-a_t)/(1 - a_te^{iϑ})`. -/
theorem lineFourierSeries_slForward (s t θ : ℝ) :
    lineFourierSeries (slForward h s t) θ =
      ((slMix h s t : ℝ) : ℂ) + ((1 - slMix h s t : ℝ) : ℂ) * ((1 - slRatio h t : ℝ) : ℂ) /
        (1 - (slRatio h t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  rw [slForward_eq, lineFourierSeries_add_smul summable_zdelta
    (summable_oneSidedGeom (slRatio_nonneg h t) (slRatio_lt_one hh t)),
    lineFourierSeries_zdelta,
    lineFourierSeries_oneSidedGeom (slRatio_nonneg h t) (slRatio_lt_one hh t), mul_one,
    mul_div_assoc]

theorem lineFourierSeries_slBackward (s t θ : ℝ) :
    lineFourierSeries (slBackward h s t) θ =
      ((slMix h s t : ℝ) : ℂ) + ((1 - slMix h s t : ℝ) : ℂ) * ((1 - slRatio h t : ℝ) : ℂ) /
        (1 - (slRatio h t : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I))) := by
  have e : slBackward h s t = fun n => slForward h s t (-n) := rfl
  rw [e, lineFourierSeries_reflect, lineFourierSeries_slForward hh, Complex.ofReal_neg, neg_mul]

/-- One factor: `p + (1-p)(1-a)/(1 - az) = (1-a)(1 - bz)/((1-b)(1 - az))`. -/
theorem slFactor_eq {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) {z : ℂ}
    (hz : 1 - (slRatio h t : ℂ) * z ≠ 0) :
    ((slMix h s t : ℝ) : ℂ) + ((1 - slMix h s t : ℝ) : ℂ) * ((1 - slRatio h t : ℝ) : ℂ) /
        (1 - (slRatio h t : ℂ) * z) =
      ((1 - slRatio h t : ℝ) : ℂ) * (1 - (slRatio h s : ℂ) * z) /
        (((1 - slRatio h s : ℝ) : ℂ) * (1 - (slRatio h t : ℂ) * z)) := by
  have ht := hs.trans_lt hst
  have ha0 : (slRatio h t : ℂ) ≠ 0 := by exact_mod_cast (slRatio_pos (h := h) ht).ne'
  have hb1 : (1 : ℂ) - slRatio h s ≠ 0 := by
    exact_mod_cast (by linarith [slRatio_lt_one hh s] : (1 : ℝ) - slRatio h s ≠ 0)
  unfold slMix
  push_cast
  field_simp
  ring

theorem slKernel_ratio_eq {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (θ : ℝ) :
    lineFourierSeries (slKernel h t) θ / lineFourierSeries (slKernel h s) θ =
      (((slMix h s t : ℝ) : ℂ) + ((1 - slMix h s t : ℝ) : ℂ) * ((1 - slRatio h t : ℝ) : ℂ) /
          (1 - (slRatio h t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
        (((slMix h s t : ℝ) : ℂ) + ((1 - slMix h s t : ℝ) : ℂ) * ((1 - slRatio h t : ℝ) : ℂ) /
          (1 - (slRatio h t : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)))) := by
  have hz := geom_factor_ne_zero (slRatio_nonneg h t) (slRatio_lt_one hh t) θ
  have hw := geom_factor_ne_zero' (slRatio_nonneg h t) (slRatio_lt_one hh t) θ
  have hz' := geom_factor_ne_zero (slRatio_nonneg h s) (slRatio_lt_one hh s) θ
  have hw' := geom_factor_ne_zero' (slRatio_nonneg h s) (slRatio_lt_one hh s) θ
  have ha1 : (1 : ℂ) - slRatio h t ≠ 0 := by
    exact_mod_cast (by linarith [slRatio_lt_one hh t] : (1 : ℝ) - slRatio h t ≠ 0)
  have hb1 : (1 : ℂ) - slRatio h s ≠ 0 := by
    exact_mod_cast (by linarith [slRatio_lt_one hh s] : (1 : ℝ) - slRatio h s ≠ 0)
  rw [(sampled_laplace_exact_transfer hh θ).2, (sampled_laplace_exact_transfer hh θ).2,
    slFactor_eq hh hs hst hz, slFactor_eq hh hs hst hw]
  push_cast
  field_simp

/-- **`prop:sampled-laplace-exact`(1), the factorization (`eq:sampled-laplace-increment`).** For
`0 ≤ s < t`, `p ∈ [0,1)`, `λ̂_t/λ̂_s` is the product of the two factors, and it is the transfer of
`λ_{s,t}`. -/
theorem sampled_laplace_exact_1_factor {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    0 ≤ slMix h s t ∧ slMix h s t < 1 ∧ ∀ θ : ℝ,
      lineFourierSeries (slKernel h t) θ / lineFourierSeries (slKernel h s) θ =
          (((slMix h s t : ℝ) : ℂ) + ((1 - slMix h s t : ℝ) : ℂ) * ((1 - slRatio h t : ℝ) : ℂ) /
              (1 - (slRatio h t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) *
            (((slMix h s t : ℝ) : ℂ) + ((1 - slMix h s t : ℝ) : ℂ) * ((1 - slRatio h t : ℝ) : ℂ) /
              (1 - (slRatio h t : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)))) ∧
        lineFourierSeries (slIncrement h s t) θ =
          lineFourierSeries (slKernel h t) θ / lineFourierSeries (slKernel h s) θ := by
  refine ⟨(slMix_mem hh hs hst).1, (slMix_mem hh hs hst).2, fun θ => ⟨slKernel_ratio_eq hh hs hst θ,
    ?_⟩⟩
  rw [slKernel_ratio_eq hh hs hst θ, slIncrement, if_neg hst.ne,
    lineFourierSeries_zconv (summable_slForward hh s t) (summable_slBackward hh s t),
    lineFourierSeries_slForward hh, lineFourierSeries_slBackward hh]

end Factor

/-! ## (1): the exact hemigroup on the grid -/

section Hemigroup

variable {h : ℝ} (hh : 0 < h)
include hh

theorem summable_slIncrement (s t : ℝ) : Summable (slIncrement h s t) := by
  unfold slIncrement
  split_ifs
  · exact summable_zdelta
  · exact summable_zconv (summable_slForward hh s t) (summable_slBackward hh s t)

/-- **The transfer of the step**, `λ̂_{s,t} = λ̂_t/λ̂_s` for `0 ≤ s ≤ t`. -/
theorem lineFourierSeries_slIncrement {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (θ : ℝ) :
    lineFourierSeries (slIncrement h s t) θ =
      ((slTransfer h t θ / slTransfer h s θ : ℝ) : ℂ) := by
  rcases hst.lt_or_eq with hst | rfl
  · rw [(sampled_laplace_exact_1_factor hh hs hst).2.2 θ |>.2, lineFourierSeries_slKernel hh,
      lineFourierSeries_slKernel hh, Complex.ofReal_div]
  · rw [slIncrement, if_pos rfl, lineFourierSeries_zdelta, div_self (slTransfer_pos hh s θ).ne',
      Complex.ofReal_one]

omit hh in
theorem zconv_reflect_symm (f : ℤ → ℝ) (n : ℤ) :
    zconv f (fun m => f (-m)) (-n) = zconv f (fun m => f (-m)) n := by
  unfold zconv
  rw [← (Equiv.addRight n).tsum_eq (fun m => f m * f (-(n - m)))]
  congr 1
  funext m
  simp only [Equiv.coe_addRight]
  rw [show -(-n - m) = n + m by ring, show -(n - (m + n)) = m by ring, add_comm n m, mul_comm]

omit hh in
theorem slTransfer_pi (t : ℝ) :
    slTransfer h t π = ((1 - slRatio h t) / (1 + slRatio h t)) ^ 2 := by
  unfold slTransfer
  rw [Real.cos_pi, div_pow]
  congr 1
  ring

/-- **`prop:sampled-laplace-exact`(1), the exact hemigroup on the grid.** The kernels
`λ_{s,t}` are nonnegative, symmetric, of unit mass, `λ_{0,t} = λ_t`,
`λ_{r,t} = λ_{s,t} * λ_{r,s}`, `λ̂_{s,t}(ϑ)` is continuous in `(s, t)`, and `λ_{s,t} ≠ δ₀` for
`s < t`. -/
theorem sampled_laplace_exact_1_hemigroup :
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → (∀ n, 0 ≤ slIncrement h s t n) ∧
      (∀ n, slIncrement h s t (-n) = slIncrement h s t n) ∧ Summable (slIncrement h s t) ∧
      ∑' n, slIncrement h s t n = 1) ∧
      (∀ t : ℝ, 0 ≤ t → slIncrement h 0 t = slKernel h t) ∧
      (∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t →
        slIncrement h r t = zconv (slIncrement h s t) (slIncrement h r s)) ∧
      (∀ θ : ℝ, ContinuousOn (fun p : ℝ × ℝ => lineFourierSeries (slIncrement h p.1 p.2) θ)
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}) ∧
      ∀ s t : ℝ, 0 ≤ s → s < t → slIncrement h s t ≠ zdelta := by
  refine ⟨fun s t hs hst => ?_, fun t ht => ?_, fun r s t hr hrs hst => ?_, fun θ => ?_,
    fun s t hs hst => ?_⟩
  · rcases hst.lt_or_eq with hst | rfl
    · rw [slIncrement, if_neg hst.ne]
      refine ⟨zconv_nonneg (slForward_nonneg hh hs hst) (fun n => slForward_nonneg hh hs hst _),
        zconv_reflect_symm _, summable_zconv (summable_slForward hh s t)
          (summable_slBackward hh s t), ?_⟩
      rw [tsum_zconv (summable_slForward hh s t) (summable_slBackward hh s t),
        tsum_slForward hh, tsum_slBackward hh, one_mul]
    · rw [slIncrement, if_pos rfl]
      refine ⟨fun n => by unfold zdelta; split_ifs <;> norm_num, fun n => by simp [zdelta],
        summable_zdelta, tsum_zdelta⟩
  · refine eq_of_lineFourierSeries_eq (summable_slIncrement hh 0 t)
      (summable_geomKernel (slRatio_nonneg h t) (slRatio_lt_one hh t)) fun θ => ?_
    rw [lineFourierSeries_slIncrement hh le_rfl ht, lineFourierSeries_slKernel hh]
    have : slTransfer h 0 θ = 1 := by
      unfold slTransfer; rw [slRatio_zero]; norm_num
    rw [this, div_one]
  · refine eq_of_lineFourierSeries_eq (summable_slIncrement hh r t)
      (summable_zconv (summable_slIncrement hh s t) (summable_slIncrement hh r s)) fun θ => ?_
    rw [lineFourierSeries_zconv (summable_slIncrement hh s t) (summable_slIncrement hh r s),
      lineFourierSeries_slIncrement hh hr (hrs.trans hst),
      lineFourierSeries_slIncrement hh (hr.trans hrs) hst, lineFourierSeries_slIncrement hh hr hrs,
      ← Complex.ofReal_mul]
    congr 1
    have := (slTransfer_pos hh s θ).ne'
    field_simp
  · have hc : Continuous fun p : ℝ × ℝ => ((slTransfer h p.2 θ / slTransfer h p.1 θ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (((continuous_slTransfer hh θ).comp continuous_snd).div
        ((continuous_slTransfer hh θ).comp continuous_fst) fun p => (slTransfer_pos hh _ θ).ne')
    exact hc.continuousOn.congr fun p hp => lineFourierSeries_slIncrement hh hp.1 hp.2 θ
  · intro he
    have h1 := lineFourierSeries_slIncrement hh hs hst.le π
    rw [he, lineFourierSeries_zdelta] at h1
    have h2 : slTransfer h t π / slTransfer h s π = 1 := by exact_mod_cast h1.symm
    have ha := slRatio_lt hh hs hst
    have hb0 := slRatio_nonneg h s
    have ha1 := slRatio_lt_one hh t
    have hlt : slTransfer h t π < slTransfer h s π := by
      rw [slTransfer_pi, slTransfer_pi]
      refine pow_lt_pow_left₀ ?_ (div_nonneg (by linarith) (by linarith)) two_ne_zero
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    rw [div_eq_one_iff_eq (slTransfer_pos hh s π).ne'] at h2
    linarith

end Hemigroup

/-! ## (1): the recursions -/

section Recursion

/-- A summable kernel convolved with a bounded sequence: the terms are summable. -/
theorem summable_zconv_term_bdd {K y : ℤ → ℝ} (hK : Summable K) (hy : IsBoundedSeq y) (n : ℤ) :
    Summable fun m => K m * y (n - m) := by
  obtain ⟨C, hC⟩ := hy
  refine Summable.of_norm_bounded (hK.norm.mul_right C) fun m => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)

theorem isBoundedSeq_zconv {K y : ℤ → ℝ} (hK : Summable K) (hy : IsBoundedSeq y) :
    IsBoundedSeq (zconv K y) := by
  obtain ⟨C, hC⟩ := hy
  refine ⟨(∑' m, |K m|) * C, fun n => ?_⟩
  have hs := summable_zconv_term_bdd hK ⟨C, hC⟩ n
  calc |zconv K y n| = ‖∑' m, K m * y (n - m)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' m, ‖K m * y (n - m)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' m, |K m| * C := by
        refine hs.norm.tsum_le_tsum (fun m => ?_) (hK.abs.mul_right C)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
    _ = (∑' m, |K m|) * C := tsum_mul_right

/-- **A one-state recursion for a kernel gives one for its convolution**: if
`K(m) = c δ₀(m) - d δ₀(m - σ) + a K(m - σ)`, then `K * y` satisfies
`v(n) = c y(n) - d y(n - σ) + a v(n - σ)`. -/
theorem zconv_recursion {K y : ℤ → ℝ} (hK : Summable K) (hy : IsBoundedSeq y) {c d a : ℝ}
    (σ : ℤ) (hrec : ∀ m, K m = c * zdelta m - d * zdelta (m - σ) + a * K (m - σ)) (n : ℤ) :
    zconv K y n = c * y n - d * y (n - σ) + a * zconv K y (n - σ) := by
  have hsh : ∀ f : ℤ → ℝ, ∑' m, f (m - σ) * y (n - m) = zconv f y (n - σ) := fun f => by
    unfold zconv
    rw [← (Equiv.addRight σ).tsum_eq]
    congr 1
    funext m
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    congr 2
    ring
  have hshS : ∀ f : ℤ → ℝ, Summable f → Summable fun m => f (m - σ) * y (n - m) := fun f hf =>
    summable_zconv_term_bdd ((Equiv.subRight σ).summable_iff.2 hf) hy n
  have h1 := summable_zconv_term_bdd summable_zdelta hy n
  have h2 := hshS zdelta summable_zdelta
  have h3 := hshS K hK
  have e : zconv K y n = c * ∑' m, zdelta m * y (n - m) - d * ∑' m, zdelta (m - σ) * y (n - m) +
      a * ∑' m, K (m - σ) * y (n - m) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
      ← (h1.mul_left c).tsum_sub (h2.mul_left d), ← ((h1.mul_left c).sub (h2.mul_left d)).tsum_add
        (h3.mul_left a), zconv]
    congr 1
    funext m
    rw [hrec m]
    ring
  rw [e, hsh, hsh, show (∑' m, zdelta m * y (n - m)) = zconv zdelta y n from rfl,
    zconv_zdelta_left]

theorem oneSidedGeom_rec (a : ℝ) (m : ℤ) :
    oneSidedGeom a m = (1 - a) * zdelta m + a * oneSidedGeom a (m - 1) := by
  unfold oneSidedGeom zdelta
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring
  · simp
  · rw [if_pos hm.le, if_neg hm.ne', if_pos (by omega)]
    rw [show m.toNat = (m - 1).toNat + 1 by omega, pow_succ]
    ring

variable {h : ℝ} (hh : 0 < h)
include hh

omit hh in
theorem slForward_rec (s t : ℝ) (m : ℤ) :
    slForward h s t m = (1 - slRatio h t + slMix h s t * slRatio h t) * zdelta m -
      slMix h s t * slRatio h t * zdelta (m - 1) + slRatio h t * slForward h s t (m - 1) := by
  simp only [slForward]
  rw [oneSidedGeom_rec (slRatio h t) m]
  ring

omit hh in
theorem slBackward_rec (s t : ℝ) (m : ℤ) :
    slBackward h s t m = (1 - slRatio h t + slMix h s t * slRatio h t) * zdelta m -
      slMix h s t * slRatio h t * zdelta (m - -1) + slRatio h t * slBackward h s t (m - -1) := by
  have e : ∀ k, slBackward h s t k = slForward h s t (-k) := fun k => rfl
  have hz : ∀ k, zdelta (-k) = zdelta k := fun k => by simp [zdelta]
  rw [e, e, slForward_rec, show -m - 1 = -(m - -1) by ring, hz, hz]

/-- **`prop:sampled-laplace-exact`(1), the recursions.** Convolution with `pδ₀ + (1-p)e⁺_t` maps a
bounded `y` to the unique bounded solution of the forward recursion, and convolution with
`pδ₀ + (1-p)e⁻_t` to the unique bounded solution of the same recursion run backward. -/
theorem sampled_laplace_exact_1_recursion {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (y : ℤ → ℝ) (hy : IsBoundedSeq y) :
    (IsBoundedSeq (zconv (slForward h s t) y) ∧
      IsForwardRecursion (slRatio h t) (slMix h s t) y (zconv (slForward h s t) y) ∧
      ∀ v : ℤ → ℝ, IsBoundedSeq v → IsForwardRecursion (slRatio h t) (slMix h s t) y v →
        v = zconv (slForward h s t) y) ∧
      (IsBoundedSeq (zconv (slBackward h s t) y) ∧
      IsBackwardRecursion (slRatio h t) (slMix h s t) y (zconv (slBackward h s t) y) ∧
      ∀ v : ℤ → ℝ, IsBoundedSeq v → IsBackwardRecursion (slRatio h t) (slMix h s t) y v →
        v = zconv (slBackward h s t) y) := by
  have ht := hs.trans_lt hst
  have ha0 := slRatio_pos (h := h) ht
  have ha1 := slRatio_lt_one hh t
  set a := slRatio h t with ha
  set p := slMix h s t with hp
  have hF := summable_slForward hh s t
  have hB := summable_slBackward hh s t
  have hfw : IsForwardRecursion a p y (zconv (slForward h s t) y) := fun n => by
    rw [zconv_recursion hF hy 1 (slForward_rec s t) n]
    ring
  have hbw : IsBackwardRecursion a p y (zconv (slBackward h s t) y) := fun n => by
    rw [zconv_recursion hB hy (-1) (slBackward_rec s t) n, sub_neg_eq_add]
    ring
  have hdiff : ∀ u w : ℤ → ℝ, IsBoundedSeq u → IsBoundedSeq w →
      ∃ C, ∀ n, |(fun n => u n - w n) n| ≤ C := by
    rintro u w ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C + D, fun n => (abs_sub _ _).trans (add_le_add (hC n) (hD n))⟩
  refine ⟨⟨isBoundedSeq_zconv hF hy, hfw, fun v hv hvr => ?_⟩,
    ⟨isBoundedSeq_zconv hB hy, hbw, fun v hv hvr => ?_⟩⟩
  · have hz := geom_homog_zero ha0 ha1 1 (hdiff v _ hv (isBoundedSeq_zconv hF hy)) fun n => by
      rw [hvr n, hfw n]
      ring
    funext n
    have := congrFun hz n
    simp only [Pi.zero_apply] at this
    linarith
  · have hz := geom_homog_zero ha0 ha1 (-1) (hdiff v _ hv (isBoundedSeq_zconv hB hy)) fun n => by
      rw [sub_neg_eq_add, hvr n, hbw n]
      ring
    funext n
    have := congrFun hz n
    simp only [Pi.zero_apply] at this
    linarith

end Recursion

/-! ## (1): the powers -/

/-- **`prop:sampled-laplace-exact`(1), the powers.** For an integer `γ ≥ 1` the powers
`λ^{*γ}_{s,t}` form a cascade family of the same kind, with `γ` forward and `γ` backward factors
per increment. -/
theorem sampled_laplace_exact_1_powers {h : ℝ} (hh : 0 < h) {γ : ℕ} (hγ : 1 ≤ γ) :
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → (∀ n, 0 ≤ zconvPow (slIncrement h s t) γ n) ∧
      (∀ n, zconvPow (slIncrement h s t) γ (-n) = zconvPow (slIncrement h s t) γ n) ∧
      Summable (zconvPow (slIncrement h s t) γ) ∧ ∑' n, zconvPow (slIncrement h s t) γ n = 1) ∧
      (∀ t : ℝ, 0 ≤ t → zconvPow (slIncrement h 0 t) γ = zconvPow (slKernel h t) γ) ∧
      (∀ r s t : ℝ, 0 ≤ r → r ≤ s → s ≤ t → zconvPow (slIncrement h r t) γ =
        zconv (zconvPow (slIncrement h s t) γ) (zconvPow (slIncrement h r s) γ)) ∧
      (∀ θ : ℝ, ContinuousOn
        (fun p : ℝ × ℝ => lineFourierSeries (zconvPow (slIncrement h p.1 p.2) γ) θ)
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2}) ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → zconvPow (slIncrement h s t) γ ≠ zdelta) ∧
      ∀ s t : ℝ, 0 ≤ s → s < t → zconvPow (slIncrement h s t) γ =
        zconv (zconvPow (slForward h s t) γ) (zconvPow (slBackward h s t) γ) := by
  obtain ⟨hA, h0, hcomp, hcont, hne⟩ := sampled_laplace_exact_1_hemigroup hh
  refine ⟨fun s t hs hst => ?_, fun t ht => by rw [h0 t ht], fun r s t hr hrs hst => ?_,
    fun θ => ?_, fun s t hs hst => ?_, fun s t hs hst => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hA s t hs hst
    exact ⟨zconvPow_nonneg h1 γ, zconvPow_symm h2 γ, summable_zconvPow h3 γ,
      tsum_zconvPow h3 h4 γ⟩
  · rw [hcomp r s t hr hrs hst, zconvPow_zconv (summable_slIncrement hh s t)
      (summable_slIncrement hh r s)]
  · have hc : Continuous fun p : ℝ × ℝ =>
        ((slTransfer h p.2 θ / slTransfer h p.1 θ : ℝ) : ℂ) ^ γ :=
      (Complex.continuous_ofReal.comp (((continuous_slTransfer hh θ).comp continuous_snd).div
        ((continuous_slTransfer hh θ).comp continuous_fst)
          fun p => (slTransfer_pos hh _ θ).ne')).pow γ
    refine hc.continuousOn.congr fun p hp => ?_
    rw [lineFourierSeries_zconvPow (summable_slIncrement hh _ _),
      lineFourierSeries_slIncrement hh hp.1 hp.2 θ]
  · intro he
    have h1 := lineFourierSeries_zconvPow (summable_slIncrement hh s t) π γ
    rw [he, lineFourierSeries_zdelta, lineFourierSeries_slIncrement hh hs hst.le π] at h1
    have h2 : (slTransfer h t π / slTransfer h s π) ^ γ = 1 := by exact_mod_cast h1.symm
    have ha := slRatio_lt hh hs hst
    have hb0 := slRatio_nonneg h s
    have ha1 := slRatio_lt_one hh t
    have hlt : slTransfer h t π < slTransfer h s π := by
      rw [slTransfer_pi, slTransfer_pi]
      refine pow_lt_pow_left₀ ?_ (div_nonneg (by linarith) (by linarith)) two_ne_zero
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hq0 : 0 ≤ slTransfer h t π / slTransfer h s π :=
      (div_pos (slTransfer_pos hh t π) (slTransfer_pos hh s π)).le
    have hq1 : slTransfer h t π / slTransfer h s π < 1 :=
      (div_lt_one (slTransfer_pos hh s π)).2 hlt
    have := pow_lt_one₀ hq0 hq1 (by omega : γ ≠ 0)
    linarith
  · rw [slIncrement, if_neg hst.ne, zconvPow_zconv (summable_slForward hh s t)
      (summable_slBackward hh s t)]

end Pyramids
