/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.PaperVI
import AffineHemigroup.OriginLowerBound
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# `prop:recursion-helmholtz`: the recursion is a Helmholtz solve

Blueprint: `blueprint/src/parts/02-line.tex` (moved from the computation chapter at the split,
`adr/0007`), `prop:recursion-helmholtz`. Wave 2, group J, Q-0281.

On the line the transforms of the one-sided exponentials are integrals of `e^{(iω - 1/t)x}` over
`(0,∞)`, and `ℓ_t = e⁺_t * e⁻_t` is one exponential integral over `(max(0,x),∞)`. The forward pass
`w = e⁺_t * y` is `t⁻¹e^{-x/t}∫_{-∞}^x e^{u/t}y(u)du`, absolutely continuous on intervals, and the
Lebesgue differentiation theorem gives `w + tw' = y` almost everywhere; the backward pass is its
reflection. On the grid the Fourier series of `λ_t` is two geometric series; `λ_t` solves the
three-point Helmholtz equation by a computation on `n > 0`, `n = 0`, `n < 0`, and a bounded solution
of the homogeneous equation vanishes, because `e(n+1) - ae(n)` is multiplied by `a⁻¹` at each step
and `e(n+1) = ae(n)` then makes `e` grow towards `-∞`. The two recursions are geometric sums, and
`λ_t * y = (1-a)²v` because both sides are bounded solutions of `(1 - t_h²Δ_h)u = y`.
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set Filter Complex
open ScaleSpace (convPow isFiniteMeasure_convPow laplaceDensity laplaceDensity_nonneg
  integrable_laplaceDensity measurable_laplaceDensity)
open scoped Topology ENNReal RealInnerProductSpace

/-! ## The line: the transforms -/

theorem expPlus_eq_indicator (t : ℝ) :
    expPlus t = (Ioi (0 : ℝ)).indicator fun x => t⁻¹ * Real.exp (-x / t) := by
  funext x
  by_cases hx : 0 < x
  · rw [expPlus, if_pos hx, indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
  · rw [expPlus, if_neg hx, indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]

theorem expPlus_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ expPlus t x := by
  unfold expPlus
  split_ifs
  · positivity
  · exact le_rfl

theorem integrable_expPlus {t : ℝ} (ht : 0 < t) : Integrable (expPlus t) := by
  rw [expPlus_eq_indicator, integrable_indicator_iff measurableSet_Ioi]
  have h := exp_neg_integrableOn_Ioi 0 (inv_pos.2 ht)
  refine IntegrableOn.congr_fun (Integrable.const_mul h t⁻¹) (fun x _ => ?_) measurableSet_Ioi
  congr 2
  ring

theorem integrable_expMinus {t : ℝ} (ht : 0 < t) : Integrable (expMinus t) :=
  (integrable_expPlus ht).comp_neg

theorem measurable_expPlus (t : ℝ) : Measurable (expPlus t) := by
  rw [expPlus_eq_indicator]
  exact (measurable_const.mul (Real.measurable_exp.comp (measurable_id.neg.div_const _))).indicator
    measurableSet_Ioi

/-- `ê⁺_t(ω) = (1 - itω)⁻¹`. -/
theorem fourierLine_expPlus {t : ℝ} (ht : 0 < t) (ω : ℝ) :
    fourierLine (expPlus t) ω = (1 - I * ((t * ω : ℝ) : ℂ))⁻¹ := by
  set a : ℂ := (ω : ℂ) * I - ((t⁻¹ : ℝ) : ℂ) with ha
  have hre : a.re < 0 := by
    simp only [ha, ofReal_inv, sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, inv_re, normSq_ofReal, div_self_mul_self', zero_sub, Left.neg_neg_iff, inv_pos]
    exact ht
  have hpt : ∀ x : ℝ, cexp (((ω * x : ℝ) : ℂ) * I) * ((expPlus t x : ℝ) : ℂ) =
      (Ioi (0 : ℝ)).indicator (fun x : ℝ => ((t⁻¹ : ℝ) : ℂ) * cexp (a * x)) x := by
    intro x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), expPlus, if_pos hx, ha]
      push_cast
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      ring
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), expPlus, if_neg hx]
      simp
  rw [fourierLine]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul, integral_exp_mul_complex_Ioi hre]
  have ha0 : a ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [ha]
  push_cast
  have h1 : (1 : ℂ) - I * (t * ω) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hX : (ω : ℂ) * I - (t : ℂ)⁻¹ = -((t : ℂ)⁻¹) * (1 - I * (t * ω)) := by
    have e : (t : ℂ)⁻¹ * (I * (t * ω)) = I * ω := by field_simp
    linear_combination (-1 : ℂ) * e
  rw [hX]
  field_simp

/-- `ê⁻_t(ω) = (1 + itω)⁻¹`. -/
theorem fourierLine_expMinus {t : ℝ} (ht : 0 < t) (ω : ℝ) :
    fourierLine (expMinus t) ω = (1 + I * ((t * ω : ℝ) : ℂ))⁻¹ := by
  have h : fourierLine (expMinus t) ω = fourierLine (expPlus t) (-ω) := by
    rw [fourierLine, fourierLine, ← integral_neg_eq_self]
    congr 1
    funext x
    rw [expMinus, neg_neg]
    congr 3
    ring
  rw [h, fourierLine_expPlus ht]
  congr 1
  push_cast
  ring

theorem laplaceDensity_ae_eq {t : ℝ} :
    laplaceDensity t =ᵐ[volume] fun x => (expPlus t x + expMinus t x) / 2 := by
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    have : volume ({0} : Set ℝ) = 0 := Real.volume_singleton
    exact measure_eq_zero_iff_ae_notMem.1 this
  filter_upwards [h0] with x hx
  rcases lt_or_gt_of_ne hx with h | h
  · rw [laplaceDensity, expMinus, expPlus, expPlus, if_neg (not_lt.2 h.le), if_pos (neg_pos.2 h),
      abs_of_neg h, zero_add]
    field_simp
  · rw [laplaceDensity, expMinus, expPlus, expPlus, if_pos h, if_neg (by linarith), abs_of_pos h,
      add_zero]
    field_simp

/-- `ℓ̂_t(ω) = (1 + t²ω²)⁻¹`. -/
theorem fourierLine_laplace {t : ℝ} (ht : 0 < t) (ω : ℝ) :
    fourierLine (laplaceDensity t) ω = (((1 + t ^ 2 * ω ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hb : ∀ (f : ℝ → ℝ), Integrable f →
      Integrable fun x : ℝ => cexp (((ω * x : ℝ) : ℂ) * I) * ((f x : ℝ) : ℂ) := by
    intro f hf
    refine (hf.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop)
      (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have h1 : fourierLine (laplaceDensity t) ω =
      (fourierLine (expPlus t) ω + fourierLine (expMinus t) ω) / 2 := by
    rw [fourierLine, integral_congr_ae (laplaceDensity_ae_eq.mono fun x hx => by rw [hx]),
      fourierLine, fourierLine, ← integral_add (hb _ (integrable_expPlus ht))
        (hb _ (integrable_expMinus ht)), ← integral_div]
    congr 1
    funext x
    push_cast
    ring
  rw [h1, fourierLine_expPlus ht, fourierLine_expMinus ht]
  set z : ℂ := I * ((t * ω : ℝ) : ℂ) with hz
  have h2 : (1 : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hz] at this
  have h3 : (1 : ℂ) + z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hz] at this
  have hprod : (1 - z) * (1 + z) = ((1 + t ^ 2 * ω ^ 2 : ℝ) : ℂ) := by
    rw [hz]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have h4 : ((1 + t ^ 2 * ω ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 1 + t ^ 2 * ω ^ 2).ne'
  rw [inv_add_inv h2 h3, hprod, show (1 - z) + (1 + z) = 2 by ring, Complex.ofReal_inv]
  field_simp

/-- `ℓ_t = e⁺_t * e⁻_t`, pointwise. -/
theorem laplace_eq_conv {t : ℝ} (ht : 0 < t) (x : ℝ) :
    laplaceDensity t x = lineConv (expPlus t) (expMinus t) x := by
  set c := max 0 x with hc
  have hpt : ∀ y, expPlus t y * expMinus t (x - y) =
      (Ioi c).indicator (fun y => (t⁻¹ * t⁻¹ * Real.exp (x / t)) * Real.exp ((-2 / t) * y)) y := by
    intro y
    rw [expMinus, neg_sub, expPlus, expPlus]
    by_cases hy : c < y
    · have h1 : 0 < y := lt_of_le_of_lt (le_max_left _ _) hy
      have h2 : 0 < y - x := by linarith [le_max_right 0 x]
      rw [if_pos h1, if_pos h2, indicator_of_mem (show y ∈ Ioi c from hy)]
      have he : Real.exp (-y / t) * Real.exp (-(y - x) / t) =
          Real.exp (x / t) * Real.exp (-2 / t * y) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp
        ring
      linear_combination (t⁻¹ * t⁻¹) * he
    · rw [indicator_of_notMem (show y ∉ Ioi c from hy)]
      rcases le_or_gt y 0 with h | h
      · rw [if_neg (not_lt.2 h), zero_mul]
      · have : y - x ≤ 0 := by
          have hyc := not_lt.1 hy
          rcases le_total 0 x with h' | h'
          · rw [hc, max_eq_right h'] at hyc; linarith
          · rw [hc, max_eq_left h'] at hyc; linarith
        rw [if_neg (not_lt.2 this), mul_zero]
  rw [lineConv]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (by have := inv_pos.2 ht; rw [div_eq_mul_inv]; linarith) c,
    laplaceDensity]
  have hx : x - 2 * c = -|x| := by
    rcases le_total x 0 with h | h
    · rw [hc, max_eq_left h, abs_of_nonpos h]; ring
    · rw [hc, max_eq_right h, abs_of_nonneg h]; ring
  have e : t⁻¹ * t⁻¹ * Real.exp (x / t) * (-Real.exp (-2 / t * c) / (-2 / t)) =
      (2 * t)⁻¹ * Real.exp ((x - 2 * c) / t) := by
    rw [show (x - 2 * c) / t = x / t + -2 / t * c by ring, Real.exp_add]
    field_simp
  rw [e, hx, neg_div]

/-- **`prop:recursion-helmholtz`(1)**, the transforms: for `t > 0`,
`ê⁺_t(ω) = (1 - itω)⁻¹`, `ê⁻_t(ω) = (1 + itω)⁻¹`, `ℓ̂_t(ω) = (1 + t²ω²)⁻¹`, and `ℓ_t = e⁺_t * e⁻_t`.
-/
theorem recursion_line_transforms {t : ℝ} (ht : 0 < t) :
    (∀ ω : ℝ, fourierLine (expPlus t) ω = (1 - I * ((t * ω : ℝ) : ℂ))⁻¹) ∧
      (∀ ω : ℝ, fourierLine (expMinus t) ω = (1 + I * ((t * ω : ℝ) : ℂ))⁻¹) ∧
      (∀ ω : ℝ, fourierLine (laplaceDensity t) ω = (((1 + t ^ 2 * ω ^ 2)⁻¹ : ℝ) : ℂ)) ∧
      ∀ x : ℝ, laplaceDensity t x = lineConv (expPlus t) (expMinus t) x :=
  ⟨fourierLine_expPlus ht, fourierLine_expMinus ht, fourierLine_laplace ht, laplace_eq_conv ht⟩

/-! ## The line: the two passes -/

section Passes

variable {t : ℝ} (ht : 0 < t) {y : ℝ → ℝ} (hy : Integrable y)
include ht hy

/-- `u ↦ e^{u/t}y(u)` is integrable on every `(-∞, c]`. -/
theorem integrableOn_Iic_expY (c : ℝ) :
    IntegrableOn (fun u => Real.exp (u / t) * y u) (Iic c) := by
  refine (hy.integrableOn (s := Iic c)).bdd_mul (c := Real.exp (c / t))
    (Real.continuous_exp.comp (continuous_id.div_const t)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right hu ht.le)

theorem locallyIntegrable_expY : LocallyIntegrable (fun u => Real.exp (u / t) * y u) := by
  intro x
  exact ⟨Iic (x + 1), Iic_mem_nhds (by linarith), integrableOn_Iic_expY ht hy (x + 1)⟩

omit ht hy in
/-- **The forward pass in closed form**: `(e⁺_t * y)(x) = t⁻¹e^{-x/t} ∫_{-∞}^x e^{u/t}y(u) du`. -/
theorem lineConv_expPlus_eq (x : ℝ) :
    lineConv (expPlus t) y x =
      t⁻¹ * Real.exp (-x / t) * ∫ u in Iic x, Real.exp (u / t) * y u := by
  rw [lineConv, ← integral_sub_left_eq_self _ volume x]
  have hpt : ∀ u, expPlus t (x - u) * y (x - (x - u)) =
      (Iio x).indicator (fun u => t⁻¹ * Real.exp (-x / t) * (Real.exp (u / t) * y u)) u := by
    intro u
    rw [sub_sub_cancel]
    by_cases hu : u < x
    · rw [indicator_of_mem (show u ∈ Iio x from hu), expPlus, if_pos (sub_pos.2 hu)]
      rw [show -(x - u) / t = -x / t + u / t by ring, Real.exp_add]
      ring
    · rw [indicator_of_notMem (show u ∉ Iio x from hu), expPlus,
        if_neg (by simp only [sub_pos]; exact hu), zero_mul]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Iio, integral_const_mul, integral_Iic_eq_integral_Iio]

end Passes

section Passes2

variable {t : ℝ} (ht : 0 < t) {y : ℝ → ℝ} (hy : Integrable y)
include ht hy

/-- `u ↦ e^{-u/t}y(u)` is integrable on every `(c, ∞)`. -/
theorem integrableOn_Ioi_expY (c : ℝ) :
    IntegrableOn (fun u => Real.exp (-u / t) * y u) (Ioi c) := by
  refine (hy.integrableOn (s := Ioi c)).bdd_mul (c := Real.exp (-c / t))
    (Real.continuous_exp.comp (continuous_id.neg.div_const t)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (neg_le_neg (le_of_lt hu)) ht.le)

theorem locallyIntegrable_expNegY : LocallyIntegrable (fun u => Real.exp (-u / t) * y u) := by
  intro x
  exact ⟨Ioi (x - 1), Ioi_mem_nhds (by linarith), integrableOn_Ioi_expY ht hy (x - 1)⟩

omit ht hy in
/-- **The backward pass in closed form**: `(e⁻_t * y)(x) = t⁻¹e^{x/t} ∫_x^∞ e^{-u/t}y(u) du`. -/
theorem lineConv_expMinus_eq (x : ℝ) :
    lineConv (expMinus t) y x =
      t⁻¹ * Real.exp (x / t) * ∫ u in Ioi x, Real.exp (-u / t) * y u := by
  rw [lineConv, ← integral_sub_left_eq_self _ volume x]
  have hpt : ∀ u, expMinus t (x - u) * y (x - (x - u)) =
      (Ioi x).indicator (fun u => t⁻¹ * Real.exp (x / t) * (Real.exp (-u / t) * y u)) u := by
    intro u
    rw [sub_sub_cancel, expMinus, neg_sub]
    by_cases hu : x < u
    · rw [indicator_of_mem (show u ∈ Ioi x from hu), expPlus, if_pos (sub_pos.2 hu)]
      rw [show -(u - x) / t = x / t + -u / t by ring, Real.exp_add]
      ring
    · rw [indicator_of_notMem (show u ∉ Ioi x from hu), expPlus,
        if_neg (by simp only [sub_pos]; exact hu), zero_mul]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul]

end Passes2

/-- **`prop:recursion-helmholtz`(1)**, the passes: for `y ∈ L¹(ℝ)`, `w := e⁺_t * y` is locally
absolutely continuous with `(1 + t∂ₓ)w = y` almost everywhere, and `v := e⁻_t * y` is locally
absolutely continuous with `(1 - t∂ₓ)v = y` almost everywhere. -/
theorem recursion_line_passes {t : ℝ} (ht : 0 < t) (y : ℝ → ℝ) (hy : Integrable y) :
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval (lineConv (expPlus t) y) a b) ∧
      (∀ᵐ x, lineConv (expPlus t) y x + t * deriv (lineConv (expPlus t) y) x = y x) ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval (lineConv (expMinus t) y) a b) ∧
      ∀ᵐ x, lineConv (expMinus t) y x - t * deriv (lineConv (expMinus t) y) x = y x := by
  set f : ℝ → ℝ := fun u => Real.exp (u / t) * y u with hf
  set g : ℝ → ℝ := fun u => Real.exp (-u / t) * y u with hg
  set F : ℝ → ℝ := fun x => ∫ u in Iic x, f u with hFdef
  set G : ℝ → ℝ := fun x => ∫ u in Ioi x, g u with hGdef
  have hfl : LocallyIntegrable f volume := locallyIntegrable_expY ht hy
  have hgl : LocallyIntegrable g volume := locallyIntegrable_expNegY ht hy
  have hw : lineConv (expPlus t) y = fun x => (t⁻¹ * Real.exp (-x / t)) * F x :=
    funext fun x => lineConv_expPlus_eq x
  have hv : lineConv (expMinus t) y = fun x => (t⁻¹ * Real.exp (x / t)) * G x :=
    funext fun x => lineConv_expMinus_eq x
  have hF : ∀ c x, F x = F c + ∫ u in c..x, f u := fun c x => by
    rw [← intervalIntegral.integral_Iic_sub_Iic (integrableOn_Iic_expY ht hy c)
      (integrableOn_Iic_expY ht hy x)]
    ring
  have hG : ∀ c x, G x = G c - ∫ u in c..x, g u := fun c x => by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' (integrableOn_Ioi_expY ht hy c)
      (integrableOn_Ioi_expY ht hy x)]
    ring
  have hk1 : ∀ a b, AbsolutelyContinuousOnInterval (fun x : ℝ => t⁻¹ * Real.exp (-x / t)) a b :=
    fun a b => (by fun_prop : ContDiff ℝ 1 fun x : ℝ => t⁻¹ * Real.exp (-x / t)).contDiffOn
      |>.absolutelyContinuousOnInterval
  have hk2 : ∀ a b, AbsolutelyContinuousOnInterval (fun x : ℝ => t⁻¹ * Real.exp (x / t)) a b :=
    fun a b => (by fun_prop : ContDiff ℝ 1 fun x : ℝ => t⁻¹ * Real.exp (x / t)).contDiffOn
      |>.absolutelyContinuousOnInterval
  have hconst : ∀ (c a b : ℝ), AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
    fun c a b => (contDiffOn_const (c := c)).absolutelyContinuousOnInterval
  have hFac : ∀ a b, AbsolutelyContinuousOnInterval F a b := by
    intro a b
    have hii : IntervalIntegrable f volume a b :=
      ((integrableOn_Iic_expY ht hy (max a b)).mono_set fun u hu =>
        (show u ≤ max a b from hu.2)).intervalIntegrable
    have h1 := hii.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) left_mem_uIcc
    have : F = fun x => F a + ∫ u in a..x, f u := funext (hF a)
    rw [this]
    exact (hconst (F a) a b).add h1
  have hGac : ∀ a b, AbsolutelyContinuousOnInterval G a b := by
    intro a b
    have hii : IntervalIntegrable g volume a b :=
      ((integrableOn_Ioi_expY ht hy (min a b - 1)).mono_set fun u hu =>
        (show min a b - 1 < u from by
          have h := hu.1
          have : a ⊓ b = min a b := rfl
          linarith)).intervalIntegrable
    have h1 := hii.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) left_mem_uIcc
    have : G = fun x => G a - ∫ u in a..x, g u := funext (hG a)
    rw [this]
    exact (hconst (G a) a b).sub h1
  refine ⟨fun a b => ?_, ?_, fun a b => ?_, ?_⟩
  · rw [hw]
    exact (hk1 a b).mul (hFac a b)
  · filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hfl] with x hx
    have hFd : HasDerivAt F (f x) x := by
      have h := (hx 0).const_add (F 0)
      have he : (fun x => F 0 + ∫ u in (0 : ℝ)..x, f u) = F := (funext (hF 0)).symm
      rwa [he] at h
    have hkd : HasDerivAt (fun x : ℝ => t⁻¹ * Real.exp (-x / t))
        (t⁻¹ * (Real.exp (-x / t) * (-1 / t))) x := by
      have := ((hasDerivAt_id x).neg.div_const t).exp.const_mul t⁻¹
      simpa using this
    have hwd : HasDerivAt (fun x => t⁻¹ * Real.exp (-x / t) * F x)
        (t⁻¹ * (Real.exp (-x / t) * (-1 / t)) * F x + t⁻¹ * Real.exp (-x / t) * f x) x :=
      hkd.mul hFd
    rw [hw, hwd.deriv, hf]
    simp only
    have he : Real.exp (-(x / t)) * Real.exp (x / t) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    field_simp
    linear_combination t * y x * he
  · rw [hv]
    exact (hk2 a b).mul (hGac a b)
  · filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hgl] with x hx
    have hGd : HasDerivAt G (-g x) x := by
      have h := (hx 0).const_sub (G 0)
      have he : (fun x => G 0 - ∫ u in (0 : ℝ)..x, g u) = G := (funext (hG 0)).symm
      rwa [he] at h
    have hkd : HasDerivAt (fun x : ℝ => t⁻¹ * Real.exp (x / t))
        (t⁻¹ * (Real.exp (x / t) * (1 / t))) x := by
      have := ((hasDerivAt_id x).div_const t).exp.const_mul t⁻¹
      simpa using this
    have hvd : HasDerivAt (fun x => t⁻¹ * Real.exp (x / t) * G x)
        (t⁻¹ * (Real.exp (x / t) * (1 / t)) * G x + t⁻¹ * Real.exp (x / t) * -g x) x :=
      hkd.mul hGd
    rw [hv, hvd.deriv, hg]
    simp only
    have he : Real.exp (x / t) * Real.exp (-(x / t)) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    field_simp
    linear_combination t * y x * he

/-! ## The line: the increment -/

/-- The law `ℓ_t(x) dx` is a probability measure: the shared library's
`ScaleSpace.isProbabilityMeasure_laplaceLaw` (`laplaceLaw t` is this measure by definition), as an
instance. -/
instance isProbabilityMeasure_laplaceLaw {t : ℝ} [Fact (0 < t)] :
    IsProbabilityMeasure ((volume : Measure ℝ).withDensity fun x =>
      ENNReal.ofReal (laplaceDensity t x)) :=
  ScaleSpace.isProbabilityMeasure_laplaceLaw Fact.out

theorem charFun_laplaceLaw {t : ℝ} (ht : 0 < t) (ω : ℝ) :
    charFun ((volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (laplaceDensity t x)) ω =
      fourierLine (laplaceDensity t) ω := by
  rw [charFun_apply_real, integral_withDensity_eq_integral_toReal_smul
    (measurable_laplaceDensity t).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), fourierLine]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (laplaceDensity_nonneg ht x), Complex.real_smul, mul_comm]
  push_cast
  ring_nf

/-- The transform of a convolution power on the line. -/
theorem charFun_convPow_real (L : Measure ℝ) [IsFiniteMeasure L] (n : ℕ) (ω : ℝ) :
    charFun (convPow L n) ω = charFun L ω ^ n := by
  induction n with
  | zero => simp [convPow, charFun_dirac]
  | succ n ih =>
    haveI := isFiniteMeasure_convPow L n
    rw [convPow, charFun_conv, ih, pow_succ]

/-- **`prop:recursion-helmholtz`(1)**, the increment: for `0 < s < t` and every integer `γ ≥ 0`,
`((1 + s²ω²)/(1 + t²ω²))^γ = (s²/t² + (1 - s²/t²) ℓ̂_t(ω))^γ`, the transform of the `γ`-fold
convolution power of the probability measure `(s²/t²) δ₀ + (1 - s²/t²) ℓ_t(x) dx`. -/
theorem recursion_line_increment {s t : ℝ} (hs : 0 < s) (hst : s < t) (γ : ℕ) :
    IsProbabilityMeasure (maternLineMix s t) ∧
      ∀ ω : ℝ,
        ((((1 + s ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2)) ^ γ : ℝ) : ℂ) =
            (((s ^ 2 / t ^ 2 : ℝ) : ℂ) + ((1 - s ^ 2 / t ^ 2 : ℝ) : ℂ) *
              fourierLine (laplaceDensity t) ω) ^ γ ∧
          charFun (convPow (maternLineMix s t) γ) ω =
            ((((1 + s ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2)) ^ γ : ℝ) : ℂ) := by
  have ht : 0 < t := hs.trans hst
  haveI : Fact (0 < t) := ⟨ht⟩
  have hq0 : 0 ≤ s ^ 2 / t ^ 2 := by positivity
  have hq1 : s ^ 2 / t ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    exact pow_lt_pow_left₀ hst hs.le two_ne_zero
  have hq1' : 0 ≤ 1 - s ^ 2 / t ^ 2 := by linarith
  set L := (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (laplaceDensity t x)
  have hprob : IsProbabilityMeasure (maternLineMix s t) := by
    constructor
    rw [maternLineMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add hq0 hq1', add_sub_cancel, ENNReal.ofReal_one]
  refine ⟨hprob, fun ω => ⟨?_, ?_⟩⟩
  · rw [fourierLine_laplace ht]
    have h1 : (0 : ℝ) < 1 + t ^ 2 * ω ^ 2 := by positivity
    have e : (1 + s ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2) =
        s ^ 2 / t ^ 2 + (1 - s ^ 2 / t ^ 2) * (1 + t ^ 2 * ω ^ 2)⁻¹ := by
      field_simp
      ring
    rw [e]
    push_cast
    ring
  · have hmix : charFun (maternLineMix s t) ω =
        ((s ^ 2 / t ^ 2 : ℝ) : ℂ) + ((1 - s ^ 2 / t ^ 2 : ℝ) : ℂ) *
          fourierLine (laplaceDensity t) ω := by
      have hb : ∀ (m : Measure ℝ) [IsFiniteMeasure m] (c : ℝ),
          Integrable (fun x : ℝ => cexp (⟪x, ω⟫ * I)) (ENNReal.ofReal c • m) := by
        intro m _ c
        refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
        refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => ?_)
        rw [Complex.norm_exp_ofReal_mul_I]
      rw [maternLineMix, charFun_apply, integral_add_measure (hb _ _) (hb _ _),
        integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hq0,
        ENNReal.toReal_ofReal hq1', ← charFun_apply, ← charFun_apply, charFun_dirac,
        charFun_laplaceLaw ht]
      simp [Complex.real_smul]
    rw [charFun_convPow_real, hmix]
    have h1 : (0 : ℝ) < 1 + t ^ 2 * ω ^ 2 := by positivity
    have e : (1 + s ^ 2 * ω ^ 2) / (1 + t ^ 2 * ω ^ 2) =
        s ^ 2 / t ^ 2 + (1 - s ^ 2 / t ^ 2) * (1 + t ^ 2 * ω ^ 2)⁻¹ := by
      field_simp
      ring
    rw [fourierLine_laplace ht, e]
    push_cast
    ring

/-! ## The grid: the sampled kernel -/

section Grid

variable {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
include hh ht

omit hh ht in
theorem gridA_pos : 0 < Real.exp (-h / t) := Real.exp_pos _

theorem gridA_lt_one : Real.exp (-h / t) < 1 :=
  by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (div_neg_of_neg_of_pos (neg_lt_zero.2 hh) ht)

/-- **`t_h²/h² = a/(1-a)²`**, `a = e^{-h/t}`, `t_h = h/(2 sinh(h/2t))`. -/
theorem helmRange_sq_div {a : ℝ} (ha : a = Real.exp (-h / t)) :
    helmRange h t ^ 2 * (h ^ 2)⁻¹ = a / (1 - a) ^ 2 := by
  set b := Real.exp (-(h / (2 * t))) with hb
  have hb0 : 0 < b := Real.exp_pos _
  have hab : a = b ^ 2 := by
    rw [ha, hb, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hsinh : 2 * Real.sinh (h / (2 * t)) = (1 - b ^ 2) / b := by
    rw [Real.sinh_eq, hb, Real.exp_neg]
    field_simp
  have hb1 : b < 1 := by
    rw [hb, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (neg_lt_zero.2 (by positivity))
  have h1 : 1 - b ^ 2 ≠ 0 := by nlinarith
  rw [helmRange, hsinh, hab]
  field_simp

/-- The Fourier series of `a^{|n|}` on `ℤ`. -/
theorem hasSum_geom_abs (θ : ℝ) :
    HasSum (fun n : ℤ => ((Real.exp (-h / t) ^ n.natAbs : ℝ) : ℂ) * cexp (((n * θ : ℝ) : ℂ) * I))
      ((1 - ((Real.exp (-h / t) : ℝ) : ℂ) * cexp ((θ : ℂ) * I))⁻¹ +
        ((Real.exp (-h / t) : ℝ) : ℂ) * cexp (-(θ : ℂ) * I) *
          (1 - ((Real.exp (-h / t) : ℝ) : ℂ) * cexp (-(θ : ℂ) * I))⁻¹) := by
  set a := Real.exp (-h / t) with ha
  have ha0 := gridA_pos (h := h) (t := t)
  have ha1 := gridA_lt_one hh ht
  have hz : ‖(a : ℂ) * cexp ((θ : ℂ) * I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha0]
    exact ha1
  have hw : ‖(a : ℂ) * cexp (-(θ : ℂ) * I)‖ < 1 := by
    rw [norm_mul, show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha0]
    exact ha1
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · refine (hasSum_geometric_of_norm_lt_one hz).congr_fun fun n => ?_
    simp only [Int.natAbs_natCast]
    push_cast
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 2
    ring
  · refine ((hasSum_geometric_of_norm_lt_one hw).mul_left
      ((a : ℂ) * cexp (-(θ : ℂ) * I))).congr_fun fun n => ?_
    have hn : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    simp only [hn]
    push_cast
    rw [mul_pow, ← Complex.exp_nat_mul, pow_succ]
    rw [show cexp (-(↑n + 1) * ↑θ * I) = cexp (-(θ : ℂ) * I) * cexp (↑n * (-(θ : ℂ) * I)) by
      rw [← Complex.exp_add]; congr 1; ring]
    ring

/-- The two forms of the transform: `(1-a)²/(1 - 2a cos ϑ + a²) = 1/(1 + t_h²D_h(ϑ))`. -/
theorem grid_symbol_eq (θ : ℝ) :
    (1 - Real.exp (-h / t)) ^ 2 /
        (1 - 2 * Real.exp (-h / t) * Real.cos θ + Real.exp (-h / t) ^ 2) =
      1 / (1 + helmRange h t ^ 2 * lineGridSymbol h θ) := by
  set a := Real.exp (-h / t) with ha
  have ha0 := gridA_pos (h := h) (t := t)
  have ha1 := gridA_lt_one hh ht
  have hk := helmRange_sq_div hh ht ha
  have hc := Real.cos_le_one θ
  have hden : 0 < 1 - 2 * a * Real.cos θ + a ^ 2 := by nlinarith
  have hsym : helmRange h t ^ 2 * lineGridSymbol h θ = a / (1 - a) ^ 2 * (2 - 2 * Real.cos θ) := by
    rw [lineGridSymbol, ← mul_assoc, hk]
  rw [hsym]
  have h1 : (1 - a) ^ 2 ≠ 0 := by
    have : 1 - a ≠ 0 := by linarith
    positivity
  have hR : 1 + a / (1 - a) ^ 2 * (2 - 2 * Real.cos θ) =
      (1 - 2 * a * Real.cos θ + a ^ 2) / (1 - a) ^ 2 := by
    rw [eq_div_iff h1, add_mul, one_mul, mul_comm (a / (1 - a) ^ 2), mul_assoc,
      div_mul_cancel₀ _ h1]
    ring
  rw [hR, one_div_div]

/-- **`prop:recursion-helmholtz`(2)**, the sampled kernel's series: with `a := e^{-h/t}`,
`λ̂_t(ϑ) = (1-a)²/(1 - 2a cos ϑ + a²) = 1/(1 + t_h² D_h(ϑ))`, `t_h := h/(2 sinh(h/2t))`. -/
theorem recursion_grid_transform (θ : ℝ) :
    lineFourierSeries (sampledLaplace h t) θ =
        (((1 - Real.exp (-h / t)) ^ 2 /
          (1 - 2 * Real.exp (-h / t) * Real.cos θ + Real.exp (-h / t) ^ 2) : ℝ) : ℂ) ∧
      (1 - Real.exp (-h / t)) ^ 2 /
          (1 - 2 * Real.exp (-h / t) * Real.cos θ + Real.exp (-h / t) ^ 2) =
        1 / (1 + helmRange h t ^ 2 * lineGridSymbol h θ) := by
  refine ⟨?_, grid_symbol_eq hh ht θ⟩
  set a := Real.exp (-h / t) with ha
  have ha0 := gridA_pos (h := h) (t := t)
  have ha1 := gridA_lt_one hh ht
  set c : ℝ := (1 - a) / (1 + a) with hc
  have hsum := (hasSum_geom_abs hh ht θ).mul_left (c : ℂ)
  rw [← ha] at hsum
  have hfun : (fun n : ℤ => (c : ℂ) * (((a ^ n.natAbs : ℝ) : ℂ) * cexp (((n * θ : ℝ) : ℂ) * I))) =
      fun n : ℤ => ((sampledLaplace h t n : ℝ) : ℂ) * cexp (((n * θ : ℝ) : ℂ) * I) := by
    funext n
    simp only [sampledLaplace, ← ha, hc]
    push_cast
    ring
  rw [hfun] at hsum
  rw [lineFourierSeries, hsum.tsum_eq]
  set z := cexp ((θ : ℂ) * I) with hz
  set w := cexp (-(θ : ℂ) * I) with hw
  have hzw : z * w = 1 := by rw [hz, hw, ← Complex.exp_add]; simp
  have hcos : z + w = 2 * Complex.cos (θ : ℂ) := by
    rw [hz, hw, Complex.two_cos]
  have hA : (1 - (a : ℂ) * z) ≠ 0 := by
    intro h0
    have h1 : (a : ℂ) * z = 1 := by linear_combination (-1 : ℂ) * h0
    have : ‖(a : ℂ) * z‖ = 1 := by rw [h1]; simp
    rw [norm_mul, hz, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha0] at this
    linarith
  have hB : (1 - (a : ℂ) * w) ≠ 0 := by
    intro h0
    have h1 : (a : ℂ) * w = 1 := by linear_combination (-1 : ℂ) * h0
    have : ‖(a : ℂ) * w‖ = 1 := by rw [h1]; simp
    rw [norm_mul, hw, show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha0] at this
    linarith
  have hprod : (1 - (a : ℂ) * z) * (1 - (a : ℂ) * w) =
      ((1 - 2 * a * Real.cos θ + a ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (a : ℂ) ^ 2 * hzw - (a : ℂ) * hcos
  have hden : ((1 - 2 * a * Real.cos θ + a ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [← hprod]; exact mul_ne_zero hA hB
  have ha1' : (1 : ℂ) + a ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) + a ≠ 0)
  have key : (1 - (a : ℂ) * z)⁻¹ + (a : ℂ) * w * (1 - (a : ℂ) * w)⁻¹ =
      (1 - (a : ℂ) ^ 2) / ((1 - 2 * a * Real.cos θ + a ^ 2 : ℝ) : ℂ) := by
    rw [← hprod]
    field_simp
    linear_combination (-(a : ℂ) ^ 2) * hzw
  rw [key, hc]
  push_cast
  field_simp
  ring

end Grid

/-! ## The grid: uniqueness of bounded solutions -/

/-- If `|rᵐx| ≤ C` for every `m` and `r > 1`, then `x = 0`. Mathlib types only. -/
theorem zero_of_bounded_geom {r : ℝ} (hr : 1 < r) {x C : ℝ} (h : ∀ m : ℕ, |r ^ m * x| ≤ C) :
    x = 0 := by
  by_contra hx
  have hx0 : 0 < |x| := abs_pos.2 hx
  obtain ⟨m, hm⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hr).eventually
    (eventually_gt_atTop ((C + 1) / |x|))).exists
  have h1 := h m
  rw [abs_mul, abs_of_pos (pow_pos (by linarith) m)] at h1
  rw [div_lt_iff₀ hx0] at hm
  linarith

/-- A sequence on `ℤ` that is summable is bounded. Mathlib types only. -/
theorem bounded_of_summable {e : ℤ → ℝ} (hs : Summable e) : ∃ C, ∀ n, |e n| ≤ C :=
  ⟨∑' m, |e m|, fun n => hs.abs.le_tsum n fun _ _ => abs_nonneg _⟩

/-- **A bounded solution of `e(n+1) + e(n-1) = (a + a⁻¹)e(n)`, `0 < a < 1`, vanishes.** Mathlib
types only. -/
theorem helm_homog_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {e : ℤ → ℝ}
    (hb : ∃ C, ∀ n, |e n| ≤ C) (he : ∀ n, e (n + 1) + e (n - 1) = (a + a⁻¹) * e n) : e = 0 := by
  obtain ⟨C, hC⟩ := hb
  have hr : 1 < a⁻¹ := (one_lt_inv₀ ha0).2 ha1
  set f : ℤ → ℝ := fun n => e (n + 1) - a * e n with hf
  have hrec : ∀ n, f n = a⁻¹ * f (n - 1) := by
    intro n
    simp only [hf, sub_add_cancel]
    have h2 := he n
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ ha0.ne', one_mul]
    linear_combination h2
  have hfC : ∀ n, |f n| ≤ C + a * C := by
    intro n
    simp only [hf]
    calc |e (n + 1) - a * e n| ≤ |e (n + 1)| + |a * e n| := abs_sub _ _
      _ = |e (n + 1)| + a * |e n| := by rw [abs_mul, abs_of_pos ha0]
      _ ≤ C + a * C := by gcongr; exacts [hC _, hC _]
  -- `f(m) = a^{-m} f(0)` for `m ≥ 0`, so `f(0) = 0`
  have hfpos : ∀ m : ℕ, f m = a⁻¹ ^ m * f 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by push_cast; ring, hrec, add_sub_cancel_right, ih,
        pow_succ]
      ring
  have hf0 : f 0 = 0 := zero_of_bounded_geom hr fun m => by rw [← hfpos]; exact hfC m
  -- then `f ≡ 0`: forwards by `hfpos`, backwards by `f(n-1) = af(n)`
  have hfz : ∀ n, f n = 0 := by
    intro n
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · rw [hfpos, hf0, mul_zero]
    · induction m with
      | zero => simpa using hf0
      | succ m ih =>
        have h := hrec (-(m : ℤ))
        rw [ih] at h
        have h2 : f (-(m : ℤ) - 1) = 0 := by
          have : a⁻¹ ≠ 0 := by positivity
          exact (mul_eq_zero.1 h.symm).resolve_left this
        rwa [show -((m + 1 : ℕ) : ℤ) = -(m : ℤ) - 1 by push_cast; ring]
  -- so `e(n+1) = ae(n)`; `e(0) = aᵐe(-m)` makes `e(0) = 0`, and then `e ≡ 0`
  have hstep : ∀ n, e (n + 1) = a * e n := fun n => by
    have := hfz n
    simp only [hf] at this
    linarith
  have hneg : ∀ m : ℕ, e 0 = a ^ m * e (-(m : ℤ)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ih, pow_succ, mul_assoc]
      congr 1
      have := hstep (-((m + 1 : ℕ) : ℤ))
      rw [show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by push_cast; ring] at this
      rw [this]
  have he0 : e 0 = 0 := by
    refine zero_of_bounded_geom hr (C := C) fun m => ?_
    have h := hneg m
    have : a⁻¹ ^ m * e 0 = e (-(m : ℤ)) := by
      rw [h, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha0.ne', one_pow, one_mul]
    rw [this]
    exact hC _
  funext n
  simp only [Pi.zero_apply]
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · induction m with
    | zero => simpa using he0
    | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 by push_cast; ring, hstep, ih, mul_zero]
  · have h := hneg m
    rw [he0] at h
    have : a ^ m ≠ 0 := by positivity
    exact (mul_eq_zero.1 h.symm).resolve_left this

/-! ## The grid: the discrete Green's function -/

section Green

variable {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
include hh ht

omit hh ht in
theorem lineGridLap_mul (u : ℤ → ℝ) (n : ℤ) :
    helmRange h t ^ 2 * lineGridLap h u n =
      helmRange h t ^ 2 * (h ^ 2)⁻¹ * (u (n + 1) - 2 * u n + u (n - 1)) := by
  rw [lineGridLap]; ring

/-- The homogeneous equation `(1 - t_h²Δ_h)e = 0` is `e(n+1) + e(n-1) = (a + a⁻¹)e(n)`. -/
theorem helm_eq_iff {e : ℤ → ℝ} (n : ℤ) (h0 : e n - helmRange h t ^ 2 * lineGridLap h e n = 0) :
    e (n + 1) + e (n - 1) = (Real.exp (-h / t) + (Real.exp (-h / t))⁻¹) * e n := by
  set a := Real.exp (-h / t) with ha
  have ha0 := gridA_pos (h := h) (t := t)
  have ha1 := gridA_lt_one hh ht
  rw [lineGridLap_mul, helmRange_sq_div hh ht ha] at h0
  have h1 : 1 - a ≠ 0 := by linarith
  have h2 : a ≠ 0 := ha0.ne'
  field_simp at h0 ⊢
  linear_combination -h0

theorem summable_sampledLaplace : Summable (sampledLaplace h t) := by
  set a := Real.exp (-h / t) with ha
  have ha0 := gridA_pos (h := h) (t := t)
  have ha1 := gridA_lt_one hh ht
  have hg := summable_geometric_of_lt_one ha0.le ha1
  refine (Summable.of_nat_of_neg_add_one (f := fun n : ℤ => a ^ n.natAbs) ?_ ?_).mul_left
    ((1 - a) / (1 + a)) |>.congr fun n => ?_
  · exact hg.congr fun n => by rw [Int.natAbs_natCast]
  · refine ((summable_nat_add_iff 1).2 hg).congr fun n => ?_
    congr 1
  · simp [sampledLaplace, ← ha]

/-- **`prop:recursion-helmholtz`(2)**, the discrete Green's function: `λ_t` is the unique summable
solution of `(1 - t_h²Δ_h)λ = δ₀`; and `t_h < t`, with `t_h/t → 1` as `h/t → 0` (at fixed `t`,
`h → 0⁺`). -/
theorem recursion_grid_green :
    Summable (sampledLaplace h t) ∧
      (∀ n : ℤ, sampledLaplace h t n - helmRange h t ^ 2 * lineGridLap h (sampledLaplace h t) n =
        if n = 0 then 1 else 0) ∧
      (∀ u : ℤ → ℝ, Summable u →
        (∀ n : ℤ, u n - helmRange h t ^ 2 * lineGridLap h u n = if n = 0 then 1 else 0) →
        u = sampledLaplace h t) ∧
      helmRange h t < t ∧
      Tendsto (fun h' : ℝ => helmRange h' t / t) (𝓝[>] 0) (𝓝 1) := by
  set a := Real.exp (-h / t) with ha
  have ha0 := gridA_pos (h := h) (t := t)
  have ha1 := gridA_lt_one hh ht
  have hk := helmRange_sq_div hh ht ha
  have h1 : 1 - a ≠ 0 := by linarith
  have h2 : 1 + a ≠ 0 := by linarith
  have heq : ∀ n : ℤ, sampledLaplace h t n -
      helmRange h t ^ 2 * lineGridLap h (sampledLaplace h t) n = if n = 0 then 1 else 0 := by
    intro n
    rw [lineGridLap_mul, hk]
    simp only [sampledLaplace, ← ha]
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · rcases m with _ | m
      · simp only [Nat.cast_zero, zero_add, zero_sub, Int.natAbs_zero, if_true, pow_zero]
        rw [show (1 : ℤ).natAbs = 1 from rfl, show (-1 : ℤ).natAbs = 1 from rfl, pow_one]
        field_simp
        ring
      · have e1 : ((m + 1 : ℕ) : ℤ) + 1 = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
        have e2 : ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℕ) : ℤ) := by push_cast; ring
        rw [e1, e2, Int.natAbs_natCast, Int.natAbs_natCast, Int.natAbs_natCast,
          if_neg (by omega)]
        field_simp
        ring
    · rcases m with _ | m
      · simp only [Nat.cast_zero, neg_zero, zero_add, zero_sub, Int.natAbs_zero, if_true,
          pow_zero]
        rw [show (1 : ℤ).natAbs = 1 from rfl, show (-1 : ℤ).natAbs = 1 from rfl, pow_one]
        field_simp
        ring
      · have e1 : -((m + 1 : ℕ) : ℤ) + 1 = -((m : ℕ) : ℤ) := by push_cast; ring
        have e2 : -((m + 1 : ℕ) : ℤ) - 1 = -((m + 2 : ℕ) : ℤ) := by push_cast; ring
        rw [e1, e2, Int.natAbs_neg, Int.natAbs_neg, Int.natAbs_neg, Int.natAbs_natCast,
          Int.natAbs_natCast, Int.natAbs_natCast, if_neg (by omega)]
        field_simp
        ring
  refine ⟨summable_sampledLaplace hh ht, heq, fun u hu hue => ?_, ?_, ?_⟩
  · have hz := helm_homog_zero ha0 ha1 (e := fun n => u n - sampledLaplace h t n)
      (bounded_of_summable (hu.sub (summable_sampledLaplace hh ht))) fun n => by
        refine helm_eq_iff hh ht (e := fun n => u n - sampledLaplace h t n) n ?_
        have h3 := hue n
        have h4 := heq n
        simp only [lineGridLap] at h3 h4 ⊢
        linarith
    funext n
    have := congrFun hz n
    simp only [Pi.zero_apply] at this
    linarith
  · have hu : 0 < h / (2 * t) := by positivity
    have hs := Real.self_lt_sinh_iff.2 hu
    rw [helmRange, div_lt_iff₀ (by positivity)]
    calc h = 2 * t * (h / (2 * t)) := by field_simp
      _ < 2 * t * Real.sinh (h / (2 * t)) := by gcongr
      _ = t * (2 * Real.sinh (h / (2 * t))) := by ring
  · -- `t_h/t = u/sinh u` with `u = h/2t → 0⁺`, and `sinh u/u → 1`
    have hslope : Tendsto (fun u : ℝ => Real.sinh u / u) (𝓝[≠] 0) (𝓝 1) := by
      have h := (Real.hasDerivAt_sinh 0).tendsto_slope_zero
      simp only [zero_add, Real.sinh_zero, sub_zero, Real.cosh_zero, smul_eq_mul] at h
      refine h.congr fun u => ?_
      field_simp
    have hmap : Tendsto (fun h' : ℝ => h' / (2 * t)) (𝓝[>] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := ((continuous_id.div_const (2 * t)).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with h' (hh' : 0 < h')
        exact (div_pos hh' (by positivity)).ne'
    have hinv := (hslope.comp hmap).inv₀ one_ne_zero
    rw [inv_one] at hinv
    refine hinv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h' (hh' : 0 < h')
    simp only [Function.comp_apply, helmRange]
    have hs : 0 < Real.sinh (h' / (2 * t)) := Real.sinh_pos_iff.2 (by positivity)
    field_simp

/-- **`prop:recursion-helmholtz`(2)**, the factorization: `1 - t_h²Δ_h = (1-a)⁻²(1 - aS)(1 - aS⁻¹)`,
`(Su)(n) := u(n-1)`, on every sequence (in particular on `ℓ¹(ℤ)`). -/
theorem recursion_grid_factor (u : ℤ → ℝ) (n : ℤ) :
    let a := Real.exp (-h / t)
    let w : ℤ → ℝ := fun m => u m - a * shiftZInv u m
    u n - helmRange h t ^ 2 * lineGridLap h u n = ((1 - a) ^ 2)⁻¹ * (w n - a * shiftZ w n) := by
  dsimp only
  set a := Real.exp (-h / t) with ha
  have ha0 := gridA_pos (h := h) (t := t)
  have ha1 := gridA_lt_one hh ht
  have h1 : 1 - a ≠ 0 := by linarith
  rw [lineGridLap_mul, helmRange_sq_div hh ht ha]
  simp only [shiftZ, shiftZInv, sub_add_cancel]
  field_simp
  ring

end Green

/-! ## The grid: the two recursions -/

section Recursions

variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {y : ℤ → ℝ} (hy : Summable y) (σ : ℤ)
include ha0 ha1 hy

/-- `∑_n ∑_j aʲ|y(n - σj)|` converges. Mathlib types only. -/
theorem summable_geomConv_abs :
    Summable fun p : ℕ × ℤ => a ^ p.1 * |y (p.2 - σ * p.1)| := by
  have hg := summable_geometric_of_lt_one ha0.le ha1
  have hprod : Summable fun p : ℕ × ℤ => a ^ p.1 * |y p.2| :=
    hg.mul_of_nonneg hy.abs (fun j => by positivity) fun m => abs_nonneg _
  let e : ℕ × ℤ ≃ ℕ × ℤ :=
    { toFun := fun p => (p.1, p.2 + σ * p.1)
      invFun := fun p => (p.1, p.2 - σ * p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  rw [← e.summable_iff]
  refine hprod.congr fun p => ?_
  simp [e]

/-- The geometric convolution `W(n) := ∑_{j ≥ 0} aʲ y(n - σj)`. -/
noncomputable def geomConv (a : ℝ) (y : ℤ → ℝ) (σ : ℤ) (n : ℤ) : ℝ :=
  ∑' j : ℕ, a ^ j * y (n - σ * j)

theorem summable_geomConv_term (n : ℤ) : Summable fun j : ℕ => a ^ j * y (n - σ * j) :=
  Summable.of_norm ((summable_geomConv_abs ha0 ha1 hy σ).prod_symm.prod_factor n |>.congr
    fun j => by simp only [Prod.swap_prod_mk, Real.norm_eq_abs, abs_mul,
      abs_of_pos (pow_pos ha0 j)])

theorem summable_geomConv : Summable (geomConv a y σ) := by
  have hF := (summable_geomConv_abs ha0 ha1 hy σ).prod_symm.prod
  refine Summable.of_norm_bounded hF fun n => ?_
  simp only [geomConv, Prod.swap_prod_mk]
  calc ‖∑' j : ℕ, a ^ j * y (n - σ * j)‖ ≤ ∑' j : ℕ, ‖a ^ j * y (n - σ * j)‖ :=
        norm_tsum_le_tsum_norm (summable_geomConv_term ha0 ha1 hy σ n).norm
    _ = ∑' j : ℕ, a ^ j * |y (n - σ * j)| := by
        congr 1; funext j
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos ha0 j)]

theorem geomConv_rec (n : ℤ) : geomConv a y σ n = y n + a * geomConv a y σ (n - σ) := by
  rw [geomConv, (summable_geomConv_term ha0 ha1 hy σ n).tsum_eq_zero_add, geomConv,
    ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, sub_zero]
  congr 1
  congr 1
  funext j
  rw [pow_succ]
  push_cast
  ring_nf

omit hy in
/-- A bounded solution of `e(n) = a e(n - σ)` vanishes. Mathlib types only. -/
theorem geom_homog_zero {e : ℤ → ℝ} (hb : ∃ C, ∀ n, |e n| ≤ C)
    (he : ∀ n, e n = a * e (n - σ)) : e = 0 := by
  obtain ⟨C, hC⟩ := hb
  have hr : 1 < a⁻¹ := (one_lt_inv₀ ha0).2 ha1
  have hpow : ∀ (n : ℤ) (m : ℕ), e n = a ^ m * e (n - σ * m) := by
    intro n m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ih, he (n - σ * m), pow_succ, mul_assoc]
      congr 2
      push_cast
      ring
  funext n
  refine zero_of_bounded_geom hr (C := C) fun m => ?_
  have h := hpow n m
  have : a⁻¹ ^ m * e n = e (n - σ * m) := by
    rw [h, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha0.ne', one_pow, one_mul]
  rw [this]
  exact hC _

end Recursions

/-- The sampled kernel lies in `[0,1]`. -/
theorem sampledLaplace_mem {h t : ℝ} (hh : 0 < h) (ht : 0 < t) (n : ℤ) :
    0 ≤ sampledLaplace h t n ∧ sampledLaplace h t n ≤ 1 := by
  have ha0 := gridA_pos (h := h) (t := t)
  have ha1 := gridA_lt_one hh ht
  set a := Real.exp (-h / t)
  have hc0 : 0 ≤ (1 - a) / (1 + a) := div_nonneg (by linarith) (by linarith)
  have hc1 : (1 - a) / (1 + a) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have hp0 : 0 ≤ a ^ n.natAbs := pow_nonneg ha0.le _
  have hp1 : a ^ n.natAbs ≤ 1 := pow_le_one₀ ha0.le ha1.le
  exact ⟨mul_nonneg hc0 hp0, by unfold sampledLaplace; nlinarith⟩

/-- **`prop:recursion-helmholtz`(2)**, the recursion: for `y ∈ ℓ¹(ℤ)`, the forward recursion
`w(n) = y(n) + a w(n-1)` and the backward recursion `v(n) = w(n) + a v(n+1)` have unique summable
solutions (the inverses of `1 - aS` and `1 - aS⁻¹` on `ℓ¹`), and `λ_t * y = (1-a)² v`. -/
theorem recursion_grid_passes {h t : ℝ} (hh : 0 < h) (ht : 0 < t) (y : ℤ → ℝ) (hy : Summable y) :
    let a := Real.exp (-h / t)
    ∃ w v : ℤ → ℝ, Summable w ∧ (∀ n, w n = y n + a * w (n - 1)) ∧
      (∀ w' : ℤ → ℝ, Summable w' → (∀ n, w' n = y n + a * w' (n - 1)) → w' = w) ∧
      Summable v ∧ (∀ n, v n = w n + a * v (n + 1)) ∧
      (∀ v' : ℤ → ℝ, Summable v' → (∀ n, v' n = w n + a * v' (n + 1)) → v' = v) ∧
      ∀ n, ∑' m : ℤ, sampledLaplace h t m * y (n - m) = (1 - a) ^ 2 * v n := by
  intro a
  have ha0 : 0 < a := gridA_pos
  have ha1 : a < 1 := gridA_lt_one hh ht
  set w := geomConv a y 1 with hw
  have hws : Summable w := summable_geomConv ha0 ha1 hy 1
  set v := geomConv a w (-1) with hv
  have hvs : Summable v := summable_geomConv ha0 ha1 hws (-1)
  have hwr : ∀ n, w n = y n + a * w (n - 1) := fun n => geomConv_rec ha0 ha1 hy 1 n
  have hvr : ∀ n, v n = w n + a * v (n + 1) := fun n => by
    rw [hv, geomConv_rec ha0 ha1 hws (-1) n, sub_neg_eq_add]
  refine ⟨w, v, hws, hwr, fun w' hw's hw'r => ?_, hvs, hvr, fun v' hv's hv'r => ?_, ?_⟩
  · have hz := geom_homog_zero ha0 ha1 1 (e := fun n => w' n - w n)
      (bounded_of_summable (hw's.sub hws)) fun n => by
        show w' n - w n = a * (w' (n - 1) - w (n - 1))
        rw [hw'r, hwr]
        ring
    funext n
    have := congrFun hz n
    simp only [Pi.zero_apply] at this
    linarith
  · have hz := geom_homog_zero ha0 ha1 (-1) (e := fun n => v' n - v n)
      (bounded_of_summable (hv's.sub hvs)) fun n => by
        show v' n - v n = a * (v' (n - -1) - v (n - -1))
        rw [sub_neg_eq_add, hv'r, hvr]
        ring
    funext n
    have := congrFun hz n
    simp only [Pi.zero_apply] at this
    linarith
  · -- both sides are bounded solutions of `(1 - t_h²Δ_h)u = y`
    set lam := sampledLaplace h t with hlam
    have hlm := sampledLaplace_mem hh ht
    set z : ℤ → ℝ := fun n => ∑' m : ℤ, lam m * y (n - m) with hz
    have hyabs : ∀ n, Summable fun m : ℤ => |y (n - m)| := fun n =>
      (Equiv.subLeft n).summable_iff.2 hy.abs
    have hsumm : ∀ (f : ℤ → ℝ), (∀ m, |f m| ≤ 1) → ∀ n, Summable fun m => f m * y (n - m) := by
      intro f hf n
      refine Summable.of_norm_bounded (hyabs n) fun m => ?_
      rw [Real.norm_eq_abs, abs_mul]
      calc |f m| * |y (n - m)| ≤ 1 * |y (n - m)| := by gcongr; exact hf m
        _ = |y (n - m)| := one_mul _
    have hlam1 : ∀ k : ℤ, ∀ m, |lam (m + k)| ≤ 1 := fun k m => by
      rw [abs_of_nonneg (hlm _).1]; exact (hlm _).2
    have hzb : ∃ C, ∀ n, |z n| ≤ C := by
      refine ⟨∑' m : ℤ, |y m|, fun n => ?_⟩
      calc |z n| = ‖∑' m : ℤ, lam m * y (n - m)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' m : ℤ, ‖lam m * y (n - m)‖ :=
            norm_tsum_le_tsum_norm (hsumm lam (fun m => by simpa using hlam1 0 m) n).norm
        _ ≤ ∑' m : ℤ, |y (n - m)| := by
            refine (hsumm lam (fun m => by simpa using hlam1 0 m) n).norm.tsum_le_tsum
              (fun m => ?_) (hyabs n)
            rw [Real.norm_eq_abs, abs_mul]
            calc |lam m| * |y (n - m)| ≤ 1 * |y (n - m)| := by
                  gcongr; simpa using hlam1 0 m
              _ = |y (n - m)| := one_mul _
        _ = ∑' m : ℤ, |y m| := (Equiv.subLeft n).tsum_eq (fun m => |y m|)
    have hshift : ∀ (k n : ℤ), z (n + k) = ∑' m : ℤ, lam (m + k) * y (n - m) := by
      intro k n
      simp only [hz]
      rw [← (Equiv.addRight k).tsum_eq]
      congr 1
      funext m
      simp only [Equiv.coe_addRight]
      congr 2
      ring
    have hzeq : ∀ n, z n - helmRange h t ^ 2 * lineGridLap h z n = y n := by
      intro n
      have heqL := (recursion_grid_green hh ht).2.1
      rw [lineGridLap_mul]
      have h1 := hshift 1 n
      have h2 := hshift (-1) n
      rw [show n + -1 = n - 1 by ring] at h2
      rw [h1, h2]
      have hS : ∀ k : ℤ, Summable fun m => lam (m + k) * y (n - m) := fun k =>
        hsumm _ (hlam1 k) n
      have hS0 : Summable fun m => lam m * y (n - m) := by simpa using hS 0
      have e1 : z n - helmRange h t ^ 2 * (h ^ 2)⁻¹ * ((∑' m, lam (m + 1) * y (n - m)) -
          2 * z n + ∑' m, lam (m + -1) * y (n - m)) =
          ∑' m, (lam m - helmRange h t ^ 2 * (h ^ 2)⁻¹ *
            (lam (m + 1) - 2 * lam m + lam (m - 1))) * y (n - m) := by
        simp only [hz]
        rw [← tsum_mul_left, ← (hS 1).tsum_sub (hS0.mul_left 2),
          ← ((hS 1).sub (hS0.mul_left 2)).tsum_add (hS (-1)), ← tsum_mul_left,
          ← hS0.tsum_sub ((((hS 1).sub (hS0.mul_left 2)).add (hS (-1))).mul_left _)]
        congr 1
        funext m
        rw [show m + -1 = m - 1 by ring]
        ring
      rw [e1]
      have e2 : ∀ m, lam m - helmRange h t ^ 2 * (h ^ 2)⁻¹ *
          (lam (m + 1) - 2 * lam m + lam (m - 1)) = if m = 0 then 1 else 0 := by
        intro m
        have := heqL m
        rw [lineGridLap_mul] at this
        exact this
      simp_rw [e2, ite_mul, one_mul, zero_mul]
      rw [tsum_ite_eq, sub_zero]
    have hveq : ∀ n, (1 - a) ^ 2 * v n - helmRange h t ^ 2 *
        lineGridLap h (fun m => (1 - a) ^ 2 * v m) n = y n := by
      intro n
      have hf := recursion_grid_factor hh ht (fun m => (1 - a) ^ 2 * v m) n
      have hae : Real.exp (-h / t) = a := rfl
      simp only [shiftZ, shiftZInv, hae, sub_add_cancel] at hf
      rw [hf]
      have h1 : ∀ m, (1 - a) ^ 2 * v m - a * ((1 - a) ^ 2 * v (m + 1)) = (1 - a) ^ 2 * w m := by
        intro m
        rw [hvr m]
        ring
      have h2 := h1 (n - 1)
      rw [sub_add_cancel] at h2
      rw [h1, h2, hwr n]
      have h1a : 1 - a ≠ 0 := by linarith
      field_simp
      ring
    have hd := helm_homog_zero ha0 ha1 (e := fun n => z n - (1 - a) ^ 2 * v n) (by
      obtain ⟨C1, hC1⟩ := hzb
      obtain ⟨C2, hC2⟩ := bounded_of_summable (hvs.mul_left ((1 - a) ^ 2))
      exact ⟨C1 + C2, fun n => (abs_sub _ _).trans (add_le_add (hC1 n) (hC2 n))⟩) fun n => by
        refine helm_eq_iff hh ht (e := fun n => z n - (1 - a) ^ 2 * v n) n ?_
        have h3 := hzeq n
        have h4 := hveq n
        simp only [lineGridLap] at h3 h4 ⊢
        linarith
    intro n
    have := congrFun hd n
    simp only [Pi.zero_apply] at this
    change z n = _
    linarith

end Pyramids
