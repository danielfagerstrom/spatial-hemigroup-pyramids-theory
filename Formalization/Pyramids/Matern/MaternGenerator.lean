/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.MaternSobolev
import Pyramids.Matern.MaternDensity
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# `thm:matern-pyramid`(4): the generator

Blueprint: `blueprint/src/parts/04-matern.tex`, `thm:matern-pyramid`. Phase 5, wave 3b.
`matern_pyramid_4_series` and `matern_pyramid_4` moved here from `PyramidsSkeleton.Ch04Matern`,
their conclusions unchanged; `matern_pyramid_4` no longer takes `1 ≤ d`, which its proof does not
read (2026-11-15, a strengthening). The series still reads it: the test frequency lies on an axis.

* **The series** (`matern_pyramid_4_series`). Each `L_r - I` has `L¹` norm at most `2`. On
  `W^{2,1}`, `‖(L_r - I)g‖₁ ≤ r²K` with `K = ∑ⱼ ‖∂ⱼ²g‖₁` (`eLpNorm_maternStep_sub_le`, from the
  Green identity), and `∑ᵢ r_i² < ∞` for `r_i = ctq^{-i}`.
* **The sum is not bounded.** Tested against the character `e^{i⟨x,ω⟩}`, the series is read term by
  term (`integral_tsum`, its absolute convergence in `L¹`), and `∫ (L_r * g) e^{i⟨·,ω⟩} =
  L̂_r(ω) ∫ g e^{i⟨·,ω⟩}` by Fubini (`integral_mconvE_mul_char`). So
  `|∫ (H_t g) e^{i⟨·,ω⟩}| = (2/t) ∑ᵢ (1 - L̂_{r_i}(ω)) |∫ g e^{i⟨·,ω⟩}|`. At `|ω| = q^N/(ct)` the
  first `N` terms are at least `1/2`, and for a normed bump `g` supported in the ball of radius
  `1/(2|ω|)` the last factor is at least `1/2` while `‖g‖₁ = 1`; so `‖H_t g‖₁ ≥ N/(2t)`. The printed
  proof used a modulated Gaussian; the bump needs only `|e^{iθ} - 1| ≤ |θ|`.
* **The generator** (`matern_pyramid_4`). For a real Schwartz `f`, with `F = 𝓕f` in Mathlib's
  normalisation, `(μ_τ * f)(x) = Re ∫ e^{2πi⟨ξ,x⟩} e^{-F_q(2πτ|ξ|)} F(ξ) dξ` for `τ ≥ 0`
  (Schwartz inversion and Fubini, `integral_fourierInvInt_sub`). The derivative in `τ` is taken
  under the integral sign. The line's `matern_pyramid_line_3` already gives
  `∂_τ e^{-F_q(τs)} = h_τ(s) e^{-F_q(τs)}` with the line's symbol
  `h_τ = (2/τ) ∑ᵢ ((1 + r_i²s²)⁻¹ - 1)`
  (`maternLineGen`), and `|h_τ(s)| ≤ 2τs² ∑ᵢ c²q^{-2(i+1)}` (`abs_maternLineGen_le`), so the
  derivative is dominated by `C|ξ|²|F(ξ)|` for `τ` near `t`. The same computation gives
  `(L_r * (μ_t * f))(x) - (μ_t * f)(x)` as the integral of `((1 + r²s²)⁻¹ - 1)` times the same
  integrand; these terms are summable in `L¹(dξ)` (`|(1 + r²s²)⁻¹ - 1| ≤ r²s²`), and `2/t` times
  their sum is `h_t(s)`. So `∂_t(μ_t * f) = H_t(μ_t * f)` at every point, not only almost
  everywhere. The record is in `W^{2,1}` since `f` is and a finite measure preserves `W^{2,1}`.

**What it reaches.** Lean core.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter SchwartzMap FourierTransform
open ScaleSpace (mconvE)
open scoped Topology ENNReal SchwartzMap RealInnerProductSpace FourierTransform

variable {d : ℕ}

/-! ## The ranges `r_i = ctq^{-i}` -/

/-- `∑ᵢ a/q^{i+1}` converges for `q > 1`. -/
theorem summable_div_pow_succ {q : ℝ} (hq : 1 < q) (a : ℝ) :
    Summable fun i : ℕ => a / q ^ (i + 1) := by
  have hq0 : 0 < q := by linarith
  have hg : Summable fun i : ℕ => (q⁻¹) ^ i :=
    summable_geometric_of_lt_one (inv_nonneg.2 hq0.le) (inv_lt_one_of_one_lt₀ hq)
  refine (hg.mul_left (a / q)).congr fun i => ?_
  rw [inv_pow, pow_succ]
  field_simp

/-- `∑ᵢ (ctq^{-i})² < ∞`. -/
theorem summable_sq_range {q : ℝ} (hq : 1 < q) (c t : ℝ) :
    Summable fun i : ℕ => (c * t / q ^ (i + 1)) ^ 2 := by
  have hq2 : 1 < q ^ 2 := one_lt_pow₀ hq two_ne_zero
  refine (summable_div_pow_succ hq2 ((c * t) ^ 2)).congr fun i => ?_
  rw [div_pow, ← pow_mul, ← pow_mul, mul_comm 2 (i + 1)]

/-! ## Clause (4): the series -/

/-- **`‖(L_r - I)g‖₁ ≤ 2‖g‖₁`.** -/
theorem maternStep_sub_bounded (r : ℝ) {g : Rd d → ℝ} (hg : Integrable g) :
    Integrable (fun x => mconvE (maternStep d r) g x - g x) ∧
      eLpNorm (fun x => mconvE (maternStep d r) g x - g x) 1 volume ≤ 2 * eLpNorm g 1 volume := by
  haveI := (charFun_maternStep (d := d) r 0).1
  have hLg := ScaleSpace.integrable_mconvE (maternStep d r) hg.1 hg
  refine ⟨hLg.sub hg, ?_⟩
  have h1 : eLpNorm (mconvE (maternStep d r) g) 1 volume ≤ eLpNorm g 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
    refine (ScaleSpace.lintegral_enorm_mconv_leE _ hg.1).trans ?_
    rw [measure_univ, one_mul]
  calc eLpNorm (fun x => mconvE (maternStep d r) g x - g x) 1 volume
      = eLpNorm (mconvE (maternStep d r) g - g) 1 volume := rfl
    _ ≤ eLpNorm (mconvE (maternStep d r) g) 1 volume + eLpNorm g 1 volume :=
        eLpNorm_sub_le hLg.1 hg.1 le_rfl
    _ ≤ eLpNorm g 1 volume + eLpNorm g 1 volume := by gcongr
    _ = 2 * eLpNorm g 1 volume := by rw [two_mul]

/-- **The series converges absolutely in `L¹` on `W^{2,1}`.** -/
theorem maternGenerator_summable {q c t : ℝ} (hq : 1 < q) {g : Rd d → ℝ} (hg : IsW21 g) :
    ∑' i : ℕ, eLpNorm (fun x => mconvE (maternStep d (c * t / q ^ (i + 1))) g x - g x) 1
      volume < ⊤ := by
  obtain ⟨K, hK, hbd⟩ := eLpNorm_maternStep_sub_le hg
  calc ∑' i : ℕ, eLpNorm (fun x => mconvE (maternStep d (c * t / q ^ (i + 1))) g x - g x) 1 volume
      ≤ ∑' i : ℕ, ENNReal.ofReal ((c * t / q ^ (i + 1)) ^ 2) * K :=
        ENNReal.tsum_le_tsum fun i => hbd _
    _ = ENNReal.ofReal (∑' i : ℕ, (c * t / q ^ (i + 1)) ^ 2) * K := by
        rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _)
          (summable_sq_range hq c t)]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK

/-! ## Clause (4): the sum is not bounded -/

/-- **`∫ (μ * g) e^{i⟨·,ω⟩} = μ̂(ω) ∫ g e^{i⟨·,ω⟩}`.** -/
theorem integral_mconvE_mul_char (μ : Measure (Rd d)) [IsFiniteMeasure μ] {g : Rd d → ℝ}
    (hg : Integrable g) (ω : Rd d) :
    ∫ x, ((mconvE μ g x : ℝ) : ℂ) * Complex.exp (↑⟪x, ω⟫ * Complex.I) =
      charFun μ ω * ∫ x, (g x : ℂ) * Complex.exp (↑⟪x, ω⟫ * Complex.I) := by
  rw [integral_mconvE_mul μ hg (by fun_prop) (C := 1)
    (fun x => by rw [Complex.norm_exp_ofReal_mul_I]), charFun_apply, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- `‖(a : ℂ)‖ₑ = ‖a‖ₑ`. -/
theorem enorm_complex_ofReal (a : ℝ) : ‖(a : ℂ)‖ₑ = ‖a‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

/-- `‖∫ h e^{i⟨·,ω⟩}‖ₑ ≤ ‖h‖₁`. -/
theorem enorm_integral_char_le (h : Rd d → ℝ) (ω : Rd d) :
    ‖∫ x, (h x : ℂ) * Complex.exp (↑⟪x, ω⟫ * Complex.I)‖ₑ ≤ eLpNorm h 1 volume := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  rw [eLpNorm_one_eq_lintegral_enorm]
  refine lintegral_congr fun x => ?_
  rw [enorm_mul, enorm_complex_ofReal, ← ofReal_norm (Complex.exp _),
    Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one, mul_one]

/-- **The sum tested against a character**: `∫ (H_t g) e^{i⟨·,ω⟩} =
(2/t) ∑ᵢ (L̂_{r_i}(ω) - 1) ∫ g e^{i⟨·,ω⟩}` on `W^{2,1}`. -/
theorem integral_maternGenerator_char {q c t : ℝ} (hq : 1 < q) {g : Rd d → ℝ} (hg : IsW21 g)
    (ω : Rd d) :
    ∫ x, (maternGenerator d q c t g x : ℂ) * Complex.exp (↑⟪x, ω⟫ * Complex.I) =
      ((2 / t : ℝ) : ℂ) * (∑' i : ℕ,
        ((((1 + (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ) - 1)) *
        ∫ x, (g x : ℂ) * Complex.exp (↑⟪x, ω⟫ * Complex.I) := by
  set e : Rd d → ℂ := fun x => Complex.exp (↑⟪x, ω⟫ * Complex.I) with he
  have hec : Continuous e := by fun_prop
  have hen : ∀ x, ‖e x‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I _
  set f : ℕ → Rd d → ℝ := fun i x => mconvE (maternStep d (c * t / q ^ (i + 1))) g x - g x
    with hf
  have hfi : ∀ i, Integrable (f i) := fun i => (maternStep_sub_bounded _ hg.1).1
  have hFi : ∀ i, Integrable fun x => (f i x : ℂ) * e x := fun i =>
    (hfi i).ofReal.mul_bdd hec.aestronglyMeasurable (Eventually.of_forall fun x => (hen x).le)
  have hsum : ∑' i, ∫⁻ x, ‖(f i x : ℂ) * e x‖ₑ ≠ ⊤ := by
    have h := maternGenerator_summable (c := c) (t := t) hq hg
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h)
    refine tsum_congr fun i => ?_
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr fun x => ?_
    rw [enorm_mul, enorm_complex_ofReal, ← ofReal_norm (e x), hen, ENNReal.ofReal_one,
      mul_one]
  have hterm : ∀ i, ∫ x, (f i x : ℂ) * e x =
      ((((1 + (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ) - 1) * ∫ x, (g x : ℂ) * e x := by
    intro i
    haveI := (charFun_maternStep (d := d) (c * t / q ^ (i + 1)) 0).1
    have hg1 : Integrable fun x => (g x : ℂ) * e x :=
      hg.1.ofReal.mul_bdd hec.aestronglyMeasurable (Eventually.of_forall fun x => (hen x).le)
    have hL1 : Integrable fun x => (mconvE (maternStep d (c * t / q ^ (i + 1))) g x : ℂ) * e x :=
      (ScaleSpace.integrable_mconvE _ hg.1.1 hg.1).ofReal.mul_bdd hec.aestronglyMeasurable
        (Eventually.of_forall fun x => (hen x).le)
    have hfun : (fun x => (f i x : ℂ) * e x) = fun x =>
        (mconvE (maternStep d (c * t / q ^ (i + 1))) g x : ℂ) * e x - (g x : ℂ) * e x := by
      funext x
      simp only [hf]
      push_cast
      ring
    rw [hfun, integral_sub hL1 hg1, integral_mconvE_mul_char _ hg.1 ω,
      (charFun_maternStep _ ω).2]
    ring
  have hfun : (fun x => (maternGenerator d q c t g x : ℂ) * e x) =
      fun x => ((2 / t : ℝ) : ℂ) * ∑' i, (f i x : ℂ) * e x := by
    funext x
    simp only [maternGenerator, hf]
    rw [Complex.ofReal_mul, Complex.ofReal_tsum, tsum_mul_right]
    ring
  rw [hfun, integral_const_mul, integral_tsum (fun i => (hFi i).1) hsum]
  simp_rw [hterm]
  rw [tsum_mul_right]
  ring

/-- **The sum is not bounded in the `L¹` norm on `W^{2,1}`.** -/
theorem maternGenerator_unbounded (hd : 1 ≤ d) {q c t : ℝ} (hq : 1 < q) (hc : 0 < c)
    (ht : 0 < t) :
    ¬ ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ g : Rd d → ℝ, IsW21 g →
      eLpNorm (maternGenerator d q c t g) 1 volume ≤ B * eLpNorm g 1 volume := by
  rintro ⟨B, hB, hbound⟩
  have hq0 : 0 < q := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * t * B.toReal)
  set ρ : ℝ := q ^ N / (c * t) with hρ_def
  have hρ : 0 < ρ := by positivity
  set ω : Rd d := ρ • ebasis (⟨0, hd⟩ : Fin d) with hω_def
  have hω : ‖ω‖ = ρ := by rw [hω_def, norm_smul, norm_ebasis, mul_one, Real.norm_of_nonneg hρ.le]
  set ε : ℝ := 1 / (2 * ρ) with hε_def
  have hε : 0 < ε := by positivity
  let φ : ContDiffBump (0 : Rd d) := ⟨ε / 2, ε, by positivity, by linarith⟩
  set g : Rd d → ℝ := φ.normed volume with hg_def
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := φ.contDiff_normed
  have hgc : HasCompactSupport g := φ.hasCompactSupport_normed
  have hW : IsW21 g := isW21_schwartz (hgc.toSchwartzMap hgs)
  have hgi : Integrable g := hW.1
  have hg0 : ∀ x, 0 ≤ g x := φ.nonneg_normed
  have hgint : ∫ x, g x = 1 := φ.integral_normed
  have hg1 : eLpNorm g 1 volume = 1 := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hgi]
    simp_rw [Real.norm_of_nonneg (hg0 _)]
    rw [hgint, ENNReal.ofReal_one]
  set e : Rd d → ℂ := fun x => Complex.exp (↑⟪x, ω⟫ * Complex.I) with he
  -- the bump against the character
  have hΛg : 1 / 2 ≤ ‖∫ x, (g x : ℂ) * e x‖ := by
    have hsub : (∫ x, (g x : ℂ) * e x) - 1 = ∫ x, (g x : ℂ) * (e x - 1) := by
      have h1 : Integrable fun x => (g x : ℂ) * e x :=
        hgi.ofReal.mul_bdd (by fun_prop) (Eventually.of_forall fun x =>
          (Complex.norm_exp_ofReal_mul_I _).le)
      have h2 : ∫ x, (g x : ℂ) = 1 := by rw [integral_complex_ofReal, hgint, Complex.ofReal_one]
      calc (∫ x, (g x : ℂ) * e x) - 1 = (∫ x, (g x : ℂ) * e x) - ∫ x, (g x : ℂ) := by rw [h2]
        _ = ∫ x, ((g x : ℂ) * e x - (g x : ℂ)) := (integral_sub h1 hgi.ofReal).symm
        _ = ∫ x, (g x : ℂ) * (e x - 1) := by
          congr 1
          funext x
          ring
    have hle : ‖(∫ x, (g x : ℂ) * e x) - 1‖ ≤ 1 / 2 := by
      rw [hsub]
      refine (norm_integral_le_of_norm_le (hgi.mul_const (1 / 2))
        (Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg0 x)]
        rcases eq_or_lt_of_le (hg0 x) with h0 | hpos
        · rw [← h0, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ (hg0 x)
          have hx : x ∈ Metric.ball (0 : Rd d) ε := by
            have : x ∈ Function.support g := hpos.ne'
            rwa [hg_def, φ.support_normed_eq] at this
          have hxn : ‖x‖ < ε := by simpa using hx
          calc ‖e x - 1‖ = ‖Complex.exp (Complex.I * ↑⟪x, ω⟫) - 1‖ := by rw [he, mul_comm]
            _ ≤ ‖⟪x, ω⟫‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
            _ ≤ ‖x‖ * ‖ω‖ := norm_inner_le_norm x ω
            _ ≤ ε * ρ := by rw [hω]; exact mul_le_mul_of_nonneg_right hxn.le hρ.le
            _ = 1 / 2 := by rw [hε_def]; field_simp
      · rw [integral_mul_const, hgint, one_mul]
    have h3 := norm_sub_norm_le (1 : ℂ) (∫ x, (g x : ℂ) * e x)
    have h4 : ‖(1 : ℂ) - ∫ x, (g x : ℂ) * e x‖ = ‖(∫ x, (g x : ℂ) * e x) - 1‖ := norm_sub_rev _ _
    rw [norm_one] at h3
    linarith
  have hΛg' : 1 / 2 ≤ ‖∫ x, (g x : ℂ) * Complex.exp (↑⟪x, ω⟫ * Complex.I)‖ := hΛg
  have hΛH := integral_maternGenerator_char (c := c) (t := t) hq hW ω
  set m : ℕ → ℝ := fun i => (1 + (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2)⁻¹ with hm
  have hmy : ∀ i, 1 - m i = (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2 /
      (1 + (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2) := by
    intro i
    have hpos : 0 < 1 + (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2 := by positivity
    simp only [hm]
    field_simp
    ring
  have hm1 : ∀ i, 0 ≤ 1 - m i ∧ 1 - m i ≤ (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2 := by
    intro i
    rw [hmy]
    have hy : 0 ≤ (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2 := by positivity
    exact ⟨by positivity, div_le_self hy (by linarith)⟩
  have hsm : Summable fun i => 1 - m i :=
    Summable.of_nonneg_of_le (fun i => (hm1 i).1) (fun i => (hm1 i).2)
      ((summable_sq_range hq c t).mul_right _)
  have hhalf : ∀ i < N, 1 / 2 ≤ 1 - m i := by
    intro i hi
    have hr : c * t / q ^ (i + 1) * ρ = q ^ N / q ^ (i + 1) := by
      rw [hρ_def]
      field_simp
    have hge : 1 ≤ q ^ N / q ^ (i + 1) := by
      rw [one_le_div (by positivity)]
      exact pow_le_pow_right₀ hq.le (by omega)
    have hy : (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2 = (q ^ N / q ^ (i + 1)) ^ 2 := by
      rw [← hr, hω]
      ring
    have hy1 : 1 ≤ (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2 := by
      rw [hy]
      nlinarith
    rw [hmy, le_div_iff₀ (by linarith)]
    linarith
  have hS : (N : ℝ) / 2 ≤ ∑' i, (1 - m i) := by
    calc (N : ℝ) / 2 = ∑ i ∈ Finset.range N, (1 / 2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ ≤ ∑ i ∈ Finset.range N, (1 - m i) :=
          Finset.sum_le_sum fun i hi => hhalf i (Finset.mem_range.1 hi)
      _ ≤ ∑' i, (1 - m i) := hsm.sum_le_tsum _ fun i _ => (hm1 i).1
  have hnormS : ‖∑' i, ((m i : ℂ) - 1)‖ = ∑' i, (1 - m i) := by
    have h : ∑' i, ((m i : ℂ) - 1) = ((-(∑' i, (1 - m i)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.ofReal_tsum, ← tsum_neg]
      congr 1
      funext i
      push_cast
      ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (tsum_nonneg fun i => (hm1 i).1)]
  have hlow : (N : ℝ) / (2 * t) ≤
      ‖∫ x, (maternGenerator d q c t g x : ℂ) * Complex.exp (↑⟪x, ω⟫ * Complex.I)‖ := by
    rw [hΛH, norm_mul, norm_mul, hnormS, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc (N : ℝ) / (2 * t) = 2 / t * ((N : ℝ) / 2) * (1 / 2) := by
          field_simp
      _ ≤ 2 / t * (∑' i, (1 - m i)) *
          ‖∫ x, (g x : ℂ) * Complex.exp (↑⟪x, ω⟫ * Complex.I)‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hS (by positivity)) hΛg' (by norm_num)
            (mul_nonneg (by positivity) (tsum_nonneg fun i => (hm1 i).1))
  have hup : ‖∫ x, (maternGenerator d q c t g x : ℂ) * Complex.exp (↑⟪x, ω⟫ * Complex.I)‖ₑ ≤ B :=
    (enorm_integral_char_le _ ω).trans ((hbound g hW).trans (by rw [hg1, mul_one]))
  have h1 : ENNReal.ofReal ((N : ℝ) / (2 * t)) ≤ B :=
    (ENNReal.ofReal_le_ofReal hlow).trans (by rw [ofReal_norm]; exact hup)
  have hBr : (N : ℝ) / (2 * t) ≤ B.toReal := (ENNReal.ofReal_le_iff_le_toReal hB.ne).1 h1
  rw [div_le_iff₀ (by positivity)] at hBr
  linarith

/-- **`thm:matern-pyramid`(4), the series.** Each term `L_{ctq^{-i}} - I` is bounded on `L¹`, with
norm at most `2`; on `W^{2,1}` the series converges absolutely in `L¹`; and its sum
`H_t = (2/t) ∑ (L_{ctq^{-i}} - I)` is not bounded in the `L¹` norm on `W^{2,1}`. -/
theorem matern_pyramid_4_series (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c) {t : ℝ}
    (ht : 0 < t) :
    (∀ (i : ℕ) (g : Rd d → ℝ), Integrable g →
      Integrable (fun x => mconvE (maternStep d (c * t / q ^ (i + 1))) g x - g x) ∧
        eLpNorm (fun x => mconvE (maternStep d (c * t / q ^ (i + 1))) g x - g x) 1 volume ≤
          2 * eLpNorm g 1 volume) ∧
      (∀ g : Rd d → ℝ, IsW21 g →
        ∑' i : ℕ, eLpNorm (fun x => mconvE (maternStep d (c * t / q ^ (i + 1))) g x - g x) 1
          volume < ⊤) ∧
      ¬ ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ g : Rd d → ℝ, IsW21 g →
        eLpNorm (maternGenerator d q c t g) 1 volume ≤ B * eLpNorm g 1 volume :=
  ⟨fun _ _ hg => maternStep_sub_bounded _ hg, fun _ hg => maternGenerator_summable hq hg,
    maternGenerator_unbounded hd hq hc ht⟩

/-! ## Clause (4): the generator, on the transform -/

/-- **The inverse transform against a finite measure**: for `ψ` integrable,
`∫ (𝓕⁻ψ)(x - y) μ(dy) = 𝓕⁻(μ̂(-2π·) ψ)(x)`, with the inverse transform written out. -/
theorem integral_fourierInvInt_sub (μ : Measure (Rd d)) [IsFiniteMeasure μ] {ψ : Rd d → ℂ}
    (hψ : Integrable ψ) (x : Rd d) :
    Integrable (fun y => ∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, x - y⟫) * Complex.I) * ψ ξ) μ ∧
      ∫ y, (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, x - y⟫) * Complex.I) * ψ ξ) ∂μ =
        ∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
          (charFun μ (-(2 * Real.pi) • ξ) * ψ ξ) := by
  have hint : Integrable (Function.uncurry fun (y ξ : Rd d) =>
      Complex.exp (↑(2 * Real.pi * ⟪ξ, x - y⟫) * Complex.I) * ψ ξ) (μ.prod volume) := by
    refine Integrable.mono' (hψ.norm.comp_snd μ) ?_ (Eventually.of_forall fun p => ?_)
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul (hψ.comp_snd μ).1
    · simp only [Function.uncurry, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  have hR : ∀ y : Rd d, Complex.exp (↑(2 * Real.pi * ⟪ξ, x - y⟫) * Complex.I) * ψ ξ =
      Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
        (Complex.exp (↑⟪y, -(2 * Real.pi) • ξ⟫ * Complex.I) * ψ ξ) := by
    intro y
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [inner_sub_right, real_inner_smul_right, real_inner_comm y ξ]
    push_cast
    ring
  simp only
  simp_rw [hR]
  rw [integral_const_mul, integral_mul_const, charFun_apply]

/-- **A record through the transform**: `μ * Re 𝓕⁻ψ = Re 𝓕⁻(μ̂(-2π·) ψ)`, pointwise. -/
theorem mconvE_re_fourierInvInt (μ : Measure (Rd d)) [IsFiniteMeasure μ] {ψ : Rd d → ℂ}
    (hψ : Integrable ψ) (x : Rd d) :
    mconvE μ (fun z => (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) * Complex.I) * ψ ξ).re) x =
      (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
          (charFun μ (-(2 * Real.pi) • ξ) * ψ ξ)).re := by
  obtain ⟨hi, he⟩ := integral_fourierInvInt_sub μ hψ x
  rw [ScaleSpace.mconvE_apply, ← he]
  exact integral_re hi

/-- The transform of `μ_τ` at `-2πξ`. -/
theorem charFun_maternPyramid_neg {q c : ℝ} {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : IsMaternPyramid q c μ) {τ : ℝ} (hτ : 0 ≤ τ) (ξ : Rd d) :
    charFun (μ 0 τ) (-(2 * Real.pi) • ξ) =
      ((Real.exp (-maternExponent q c (τ * (2 * Real.pi * ‖ξ‖))) : ℝ) : ℂ) := by
  rw [(hμ 0 τ le_rfl hτ).2]
  simp only [zero_mul, maternExponent_zero, sub_zero, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos Real.two_pi_pos]

/-- The transform of `L_r` at `-2πξ`. -/
theorem charFun_maternStep_neg (r : ℝ) (ξ : Rd d) :
    charFun (maternStep d r) (-(2 * Real.pi) • ξ) =
      (((1 + r ^ 2 * (2 * Real.pi * ‖ξ‖) ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [(charFun_maternStep r _).2, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos Real.two_pi_pos]

/-- **Schwartz inversion**, written out. -/
theorem schwartz_inversion (f : 𝓢(Rd d, ℝ)) (z : Rd d) :
    f z = (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) * Complex.I) *
      (𝓕 (schwartzC f)) ξ).re := by
  have hinv : (𝓕⁻ (𝓕 (schwartzC f)) : 𝓢(Rd d, ℂ)) = schwartzC f :=
    FourierPair.fourierInv_fourier_eq _
  have h : (f z : ℂ) = ∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) * Complex.I) *
      (𝓕 (schwartzC f)) ξ := by
    calc (f z : ℂ) = schwartzC f z := rfl
      _ = (𝓕⁻ (𝓕 (schwartzC f)) : 𝓢(Rd d, ℂ)) z := by rw [hinv]
      _ = 𝓕⁻ (⇑(𝓕 (schwartzC f) : 𝓢(Rd d, ℂ))) z := by rw [fourierInv_coe]
      _ = _ := by
        rw [Real.fourierInv_eq']
        simp only [smul_eq_mul]
  rw [← h, Complex.ofReal_re]

/-! ## Clause (4): the generator -/

/-- `|h_τ(s)| ≤ 2τs² A`, `A = ∑ᵢ c²q^{-2(i+1)}`, for the line's symbol `h_τ` (`maternLineGen`). -/
theorem abs_maternLineGen_le {q c : ℝ} (hq : 1 < q) {τ : ℝ} (hτ : 0 < τ) (s : ℝ) :
    |maternLineGen q c τ s| ≤ 2 * τ * s ^ 2 * ∑' i : ℕ, c ^ 2 / q ^ (2 * (i + 1)) := by
  rw [maternLineGen, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / τ)]
  have hsum := summable_maternLineGen hq c τ s
  have hb : ∀ i : ℕ, ‖(1 + (c * τ / q ^ (i + 1)) ^ 2 * s ^ 2)⁻¹ - 1‖ ≤
      τ ^ 2 * s ^ 2 * (c ^ 2 / q ^ (2 * (i + 1))) := by
    intro i
    rw [Real.norm_eq_abs]
    refine (inv_one_add_sub_one (by positivity)).2.2.trans (le_of_eq ?_)
    rw [genArg_eq]
    ring
  have hs2 : Summable fun i : ℕ => τ ^ 2 * s ^ 2 * (c ^ 2 / q ^ (2 * (i + 1))) :=
    (summable_genTerm hq (c ^ 2)).mul_left _
  have h1 : |∑' i : ℕ, ((1 + (c * τ / q ^ (i + 1)) ^ 2 * s ^ 2)⁻¹ - 1)| ≤
      ∑' i : ℕ, τ ^ 2 * s ^ 2 * (c ^ 2 / q ^ (2 * (i + 1))) := by
    rw [← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hsum.norm).trans (hsum.norm.tsum_le_tsum hb hs2)
  calc 2 / τ * |∑' i : ℕ, ((1 + (c * τ / q ^ (i + 1)) ^ 2 * s ^ 2)⁻¹ - 1)|
      ≤ 2 / τ * ∑' i : ℕ, τ ^ 2 * s ^ 2 * (c ^ 2 / q ^ (2 * (i + 1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * τ * s ^ 2 * ∑' i : ℕ, c ^ 2 / q ^ (2 * (i + 1)) := by
        rw [tsum_mul_left]
        field_simp

/-- A bounded measurable factor against a character keeps an integrand integrable. -/
theorem integrable_char_mul {ψ : Rd d → ℂ} (hψ : Integrable ψ) {b : Rd d → ℂ}
    (hb : AEStronglyMeasurable b) {C : ℝ} (hC : ∀ ξ, ‖b ξ‖ ≤ C) (x : Rd d) :
    Integrable fun ξ => Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) * (b ξ * ψ ξ) := by
  refine Integrable.mono' (hψ.norm.const_mul C) ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul (hb.mul hψ.1)
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC ξ) (norm_nonneg _)

/-- **`thm:matern-pyramid`(4), the generator.** For `f ∈ 𝓢(ℝ^d)` and `t > 0`: `μ_t * f ∈ W^{2,1}`,
`t ↦ (μ_t * f)(x)` is differentiable at `t` for every `x`, and `∂_t(μ_t * f) = H_t(μ_t * f)` almost
everywhere. -/
theorem matern_pyramid_4 {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ) (f : 𝓢(Rd d, ℝ)) {t : ℝ}
    (ht : 0 < t) :
    IsW21 (mconvE (μ 0 t) f) ∧ (∀ x, DifferentiableAt ℝ (fun τ => mconvE (μ 0 τ) f x) t) ∧
      (fun x => deriv (fun τ => mconvE (μ 0 τ) f x) t) =ᵐ[volume]
        maternGenerator d q c t (mconvE (μ 0 t) f) := by
  haveI := (hμ 0 t le_rfl ht.le).1
  set F : 𝓢(Rd d, ℂ) := 𝓕 (schwartzC f) with hF
  have hFc : Continuous F := F.continuous
  have hFi : Integrable F := F.integrable
  set s : Rd d → ℝ := fun ξ => 2 * Real.pi * ‖ξ‖ with hs
  set E : ℝ → Rd d → ℝ := fun τ ξ => Real.exp (-maternExponent q c (τ * s ξ)) with hE
  have hEc : ∀ τ, Continuous (E τ) := fun τ => by
    have := continuous_maternExponent hq hc
    simp only [hE, hs]
    fun_prop
  have hE1 : ∀ τ ξ, ‖((E τ ξ : ℝ) : ℂ)‖ ≤ 1 := fun τ ξ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff,
      neg_nonpos]
    exact maternExponent_nonneg hq hc _
  set e : Rd d → Rd d → ℂ := fun x ξ => Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I)
    with he
  have hψ : ∀ τ, Integrable fun ξ => ((E τ ξ : ℝ) : ℂ) * F ξ := fun τ =>
    Integrable.mono' hFi.norm ((Continuous.aestronglyMeasurable (by
      have := hEc τ
      fun_prop)).mul hFi.1) (Eventually.of_forall fun ξ => by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hE1 τ ξ)))
  -- the record through the transform
  have hrec : ∀ τ, 0 ≤ τ → ∀ x, mconvE (μ 0 τ) f x =
      (∫ ξ, e x ξ * (((E τ ξ : ℝ) : ℂ) * F ξ)).re := by
    intro τ hτ x
    haveI := (hμ 0 τ le_rfl hτ).1
    have h1 : (⇑f : Rd d → ℝ) = fun z => (∫ ξ, e z ξ * F ξ).re := funext (schwartz_inversion f)
    rw [h1, mconvE_re_fourierInvInt _ hFi x]
    simp_rw [charFun_maternPyramid_neg hμ hτ]
    rfl
  -- the derivative, under the integral sign
  set A : ℝ := ∑' i : ℕ, c ^ 2 / q ^ (2 * (i + 1)) with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun i => by positivity
  have hderiv : ∀ x, HasDerivAt (fun τ => mconvE (μ 0 τ) f x)
      (∫ ξ, e x ξ * (((maternLineGen q c t (s ξ) * E t ξ : ℝ) : ℂ) * F ξ)).re t := by
    intro x
    have hgm : Measurable fun ξ => maternLineGen q c t (s ξ) := by
      simp only [maternLineGen, hs]
      refine Measurable.const_mul (Measurable.tsum fun i => ?_) _
      fun_prop
    have hdiff : ∀ ξ, ∀ τ ∈ Ioo (t / 2) (2 * t), HasDerivAt
        (fun τ => e x ξ * (((E τ ξ : ℝ) : ℂ) * F ξ))
        (e x ξ * (((maternLineGen q c τ (s ξ) * E τ ξ : ℝ) : ℂ) * F ξ)) τ := by
      intro ξ τ hτ
      have hτ0 : 0 < τ := by linarith [hτ.1]
      have h := ((matern_pyramid_line_3 hq hc).1 τ hτ0 (s ξ)).2
      exact (h.ofReal_comp.mul_const (F ξ)).const_mul (e x ξ)
    have hbound : ∀ ξ, ∀ τ ∈ Ioo (t / 2) (2 * t),
        ‖e x ξ * (((maternLineGen q c τ (s ξ) * E τ ξ : ℝ) : ℂ) * F ξ)‖ ≤
          4 * t * A * (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖F ξ‖) := by
      intro ξ τ hτ
      have hτ0 : 0 < τ := by linarith [hτ.1]
      rw [norm_mul, he, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, Complex.ofReal_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := abs_maternLineGen_le (c := c) hq hτ0 (s ξ)
      have h2 := hE1 τ ξ
      have hs2 : s ξ ^ 2 = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by rw [hs]; ring
      have h3 : |maternLineGen q c τ (s ξ)| ≤ 4 * t * A * (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
        refine h1.trans ?_
        rw [hs2, ← hA]
        have : τ ≤ 2 * t := hτ.2.le
        have hp : 0 ≤ (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * A := by positivity
        nlinarith
      calc |maternLineGen q c τ (s ξ)| * ‖((E τ ξ : ℝ) : ℂ)‖ * ‖F ξ‖
          ≤ (4 * t * A * (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) * 1 * ‖F ξ‖ := by gcongr
        _ = 4 * t * A * (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖F ξ‖) := by ring
    have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure (Rd d))) (x₀ := t)
      (F := fun τ ξ => e x ξ * (((E τ ξ : ℝ) : ℂ) * F ξ))
      (F' := fun τ ξ => e x ξ * (((maternLineGen q c τ (s ξ) * E τ ξ : ℝ) : ℂ) * F ξ))
      (bound := fun ξ => 4 * t * A * (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖F ξ‖))
      (Ioo_mem_nhds (by linarith) (by linarith))
      (Eventually.of_forall fun τ => (integrable_char_mul (hψ τ) aestronglyMeasurable_const
        (C := 1) (fun _ => by rw [norm_one]) x).1.congr (Eventually.of_forall fun ξ => by
          simp only [one_mul, he]))
      ((integrable_char_mul (hψ t) aestronglyMeasurable_const
        (C := 1) (fun _ => by rw [norm_one]) x).congr (Eventually.of_forall fun ξ => by
          simp only [one_mul, he]))
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        (((Complex.measurable_ofReal.comp (hgm.mul (hEc t).measurable)).aestronglyMeasurable).mul
          hFi.1))
      (Eventually.of_forall hbound)
      ((F.integrable_pow_mul volume 2).const_mul _)
      (Eventually.of_forall hdiff)
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hint.2
    have hev : (fun τ => mconvE (μ 0 τ) f x) =ᶠ[𝓝 t]
        fun τ => (∫ ξ, e x ξ * (((E τ ξ : ℝ) : ℂ) * F ξ)).re := by
      filter_upwards [Ioi_mem_nhds ht] with τ hτ
      exact hrec τ (le_of_lt hτ) x
    exact (hre.congr_of_eventuallyEq hev).congr_deriv rfl
  -- the generator, through the transform
  have hgen : ∀ x, maternGenerator d q c t (mconvE (μ 0 t) f) x =
      (∫ ξ, e x ξ * (((maternLineGen q c t (s ξ) * E t ξ : ℝ) : ℂ) * F ξ)).re := by
    intro x
    set ψ : Rd d → ℂ := fun ξ => ((E t ξ : ℝ) : ℂ) * F ξ with hψdef
    set m : ℕ → Rd d → ℝ := fun i ξ => (1 + (c * t / q ^ (i + 1)) ^ 2 * s ξ ^ 2)⁻¹ with hm
    have hmc : ∀ i, Continuous (m i) := fun i => by
      simp only [hm, hs]
      refine Continuous.inv₀ (by fun_prop) fun ξ => by positivity
    have hm1 : ∀ i ξ, |m i ξ - 1| ≤ (c * t / q ^ (i + 1)) ^ 2 * s ξ ^ 2 := fun i ξ =>
      (inv_one_add_sub_one (by positivity)).2.2
    have hm1' : ∀ i ξ, ‖((m i ξ : ℂ) - 1)‖ ≤ 1 := fun i ξ => by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_le]
      obtain ⟨h1, h2, -⟩ := inv_one_add_sub_one
        (a := (c * t / q ^ (i + 1)) ^ 2 * s ξ ^ 2) (by positivity)
      exact ⟨h1, by linarith⟩
    have hv : (mconvE (μ 0 t) (⇑f)) = fun z => (∫ ξ, e z ξ * ψ ξ).re :=
      funext (hrec t ht.le)
    set G : ℕ → Rd d → ℂ := fun i ξ => e x ξ * (((m i ξ : ℂ) - 1) * ψ ξ) with hG
    have hGi : ∀ i, Integrable (G i) := fun i =>
      integrable_char_mul (hψ t) (Continuous.aestronglyMeasurable (by
        have := hmc i
        fun_prop)) (hm1' i) x
    have hterm : ∀ i, mconvE (maternStep d (c * t / q ^ (i + 1))) (mconvE (μ 0 t) f) x -
        mconvE (μ 0 t) f x = (∫ ξ, G i ξ).re := by
      intro i
      haveI := (charFun_maternStep (d := d) (c * t / q ^ (i + 1)) 0).1
      rw [hv, mconvE_re_fourierInvInt _ (hψ t) x]
      simp_rw [charFun_maternStep_neg]
      have h1 : Integrable fun ξ => e x ξ * (((m i ξ : ℝ) : ℂ) * ψ ξ) :=
        integrable_char_mul (hψ t) (b := fun ξ => ((m i ξ : ℝ) : ℂ))
          (Continuous.aestronglyMeasurable (by
            have := hmc i
            fun_prop)) (C := 1) (fun ξ => by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simp only [hm]; positivity)]
          exact inv_le_one_of_one_le₀ (by
            have : 0 ≤ (c * t / q ^ (i + 1)) ^ 2 * s ξ ^ 2 := by positivity
            linarith)) x
      have h2 : Integrable fun ξ => e x ξ * ψ ξ := by
        have h := integrable_char_mul (hψ t) (b := fun _ => (1 : ℂ)) aestronglyMeasurable_const
          (C := 1) (fun _ => by rw [norm_one]) x
        simpa only [one_mul] using h
      have key : (∫ ξ, e x ξ * (((m i ξ : ℝ) : ℂ) * ψ ξ)) - ∫ ξ, e x ξ * ψ ξ = ∫ ξ, G i ξ := by
        rw [← integral_sub h1 h2]
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only [hG]
        ring
      rw [← Complex.sub_re]
      exact congrArg Complex.re key
    -- summability of the terms in `L¹(dξ)`
    have hnormG : ∀ i ξ, ‖G i ξ‖ ≤
        (c * t / q ^ (i + 1)) ^ 2 * ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖F ξ‖)) := by
      intro i ξ
      change ‖Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
        (((m i ξ : ℂ) - 1) * (((E t ξ : ℝ) : ℂ) * F ξ))‖ ≤ _
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul]
      have h1 : ‖((m i ξ : ℂ) - 1)‖ ≤ (c * t / q ^ (i + 1)) ^ 2 * s ξ ^ 2 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact hm1 i ξ
      have hs2 : s ξ ^ 2 = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by rw [hs]; ring
      calc ‖((m i ξ : ℂ) - 1)‖ * (‖((E t ξ : ℝ) : ℂ)‖ * ‖F ξ‖)
          ≤ ((c * t / q ^ (i + 1)) ^ 2 * s ξ ^ 2) * (1 * ‖F ξ‖) := by
            gcongr
            exact hE1 t ξ
        _ = _ := by rw [hs2]; ring
    have hP : Integrable fun ξ : Rd d => (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖F ξ‖) :=
      (F.integrable_pow_mul volume 2).const_mul _
    have hsumG : Summable fun i => ∫ ξ, ‖G i ξ‖ := by
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun ξ => norm_nonneg _)
        (fun i => ?_) ((summable_sq_range hq c t).mul_right
          (∫ ξ, (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖F ξ‖)))
      rw [← integral_const_mul]
      exact integral_mono_of_nonneg (Eventually.of_forall fun ξ => norm_nonneg _)
        (hP.const_mul _) (Eventually.of_forall (hnormG i))
    have hHS := (hasSum_integral_of_summable_integral_norm hGi hsumG).mapL Complex.reCLM
    simp only [Complex.reCLM_apply] at hHS
    have htsum : ∀ ξ, ∑' i, G i ξ =
        e x ξ * (((∑' i, (m i ξ - 1) : ℝ) : ℂ) * ψ ξ) := by
      intro ξ
      simp only [hG]
      rw [tsum_mul_left, tsum_mul_right, Complex.ofReal_tsum]
      push_cast
      rfl
    rw [maternGenerator]
    simp_rw [hterm]
    rw [hHS.tsum_eq]
    simp_rw [htsum]
    rw [← Complex.re_ofReal_mul, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hψdef, maternLineGen, hm]
    push_cast
    ring
  refine ⟨(isW21_schwartz f).mconv (μ 0 t), fun x => (hderiv x).differentiableAt,
    Eventually.of_forall fun x => ?_⟩
  simp only
  rw [(hderiv x).deriv, hgen x]

end Pyramids
