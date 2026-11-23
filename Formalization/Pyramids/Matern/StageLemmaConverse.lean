/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.StageLemma
import Pyramids.Matern.CreationPlane
import Pyramids.Matern.ExpSchwartz

/-!
# `prop:stage-lemma`(3): the converse

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:stage-lemma`. Phase 5, wave 3b (on the VM).

The route takes no derivative and no Fourier multiplier. Write `ρ(w) := μ̂(w)`, real for a
symmetric `μ`, so that `μ * cos⟨w,·⟩ = ρ(w) cos⟨w,·⟩`.

* **The test inputs.** `f_s(x) := ∑ₖ aₖ cos⟨wₖ,x⟩ e^{-s|x|²}` is a real Schwartz function
  (`exists_cosGauss`). As `s → 0` its output `μ * f_s` tends to `h(x) := ∑ₖ aₖρ(wₖ) cos⟨wₖ,x⟩`
  uniformly on the unit ball (dominated convergence, `exists_close`).
* **The inequality** (`sum_le_of_principle`). If `∑ₖ aₖρ(wₖ)⟨wₖ,x⟩² ≥ c|x|²`, `c > 0`, then `h` has
  a strict maximum at `0`, `h(x) ≤ h(0) - c|x|²/4` near `0`, by `|cos y - 1 + y²/2| ≤ y⁴`. The
  output `μ * f_s` then attains its maximum over a small closed ball inside it, at a local maximum
  `x_s`, where the principle gives `μ * f_s(x_s) ≤ f_s(x_s)`. Letting the ball shrink:
  `∑ₖ aₖρ(wₖ) ≤ ∑ₖ aₖ`.
* **No zero** (`re_charFun_ne_zero`). At a zero `ω₀` of `ρ` the coefficient of `cos⟨ω₀,·⟩` enters
  the right side only; with `wᵢ = teᵢ`, `ρ(teᵢ) ≥ 1/2`, it can be made `-∞`.
* **The reciprocal.** With `m := 1/ρ - 1` and `aₖ := bₖ/ρ(wₖ)` the inequality reads
  `∑ₖ bₖ⟨wₖ,x⟩² ≥ c|x|² ⇒ ∑ₖ bₖ m(wₖ) ≥ 0` (`sum_recipSub_nonneg`). Adding `ε|x|²` through the
  basis, `∑ₖ bₖ⟨wₖ,·⟩² = 0 ⇒ ∑ₖ bₖ m(wₖ) = 0` (`sum_recipSub_eq_zero`) and `m ≥ 0`. The family
  `(1, ω)`, `(∓ωᵢωⱼ/2, eᵢ + eⱼ, eᵢ, eⱼ)` has a vanishing form, so `m(ω) = ω·Mω` with
  `Mᵢⱼ := (m(eᵢ + eⱼ) - m(eᵢ) - m(eⱼ))/2` (`recipSub_eq_quad`), positive semidefinite.
* **Rotation invariance.** `μ̂` is radial (`charFun_eq_norm_smul_ebasis`), so `ω·Cω = τ|ω|²` with
  `τ := e₁·Ce₁`; a symmetric matrix is read off its form (`eq_of_quad_eq`), and at `τ = 0`,
  `μ̂ = 1` and `μ = δ₀`.

This replaces the printed route (a functional carried by a point, a Fourier multiplier `𝓛` with the
growth of `1/μ̂`, the jets of `μ * f` and their annihilator, the projections `μ_v`): no derivative
of an output, no multiplier and no distribution theory is used.

Dropped binder (2026-11-15, a strengthening): `stage_lemma_3` takes no `1 ≤ d`.

**What it reaches.** Lean core (the guard's run, `records/pyramids/WAVE3-report-3b-vm.md`).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (mconvE)
open scoped Topology ENNReal RealInnerProductSpace Matrix SchwartzMap

variable {d : ℕ}

/-! ## The test inputs -/

/-- `cos` has temperate growth: every derivative is bounded by `1`. -/
theorem hasTemperateGrowth_cos : Function.HasTemperateGrowth Real.cos := by
  refine ⟨Real.contDiff_cos, fun n => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  simpa using Real.abs_iteratedDeriv_cos_le_one n x

/-- **The test input** `f_s(x) = ∑ₖ aₖ cos⟨wₖ,x⟩ e^{-s|x|²}`. -/
noncomputable def cosGauss {ι : Type*} [Fintype ι] (a : ι → ℝ) (w : ι → Rd d) (s : ℝ)
    (x : Rd d) : ℝ :=
  ∑ k, a k * (Real.cos ⟪w k, x⟫ * Real.exp (-(s * ‖x‖ ^ 2)))

/-- **The limit output** `h(x) = ∑ₖ bₖ cos⟨wₖ,x⟩`. -/
noncomputable def cosSum {ι : Type*} [Fintype ι] (b : ι → ℝ) (w : ι → Rd d) (x : Rd d) : ℝ :=
  ∑ k, b k * Real.cos ⟪w k, x⟫

/-- The test input is a Schwartz function. -/
theorem exists_cosGauss {ι : Type*} [Fintype ι] (a : ι → ℝ) (w : ι → Rd d) {s : ℝ}
    (hs : 0 < s) : ∃ f : 𝓢(Rd d, ℝ), ∀ x, f x = cosGauss a w s x := by
  have hΨ : Function.HasTemperateGrowth fun x : Rd d => -(s * ‖x‖ ^ 2) :=
    ((Function.HasTemperateGrowth.const s).mul (Function.hasTemperateGrowth_norm_sq _)).neg
  obtain ⟨g, hg⟩ := exists_schwartz_exp hΨ (A := 0) hs (fun x => by simp)
  have ht : ∀ k, Function.HasTemperateGrowth fun x : Rd d => Real.cos ⟪w k, x⟫ := fun k =>
    hasTemperateGrowth_cos.comp (Function.hasTemperateGrowth_inner_right (w k))
  refine ⟨∑ k, a k • SchwartzMap.smulLeftCLM ℝ (fun x : Rd d => Real.cos ⟪w k, x⟫) g,
    fun x => ?_⟩
  simp [cosGauss, SchwartzMap.smulLeftCLM_apply_apply (ht _), hg]

theorem abs_cosGauss_le {ι : Type*} [Fintype ι] (a : ι → ℝ) (w : ι → Rd d) {s : ℝ}
    (hs : 0 ≤ s) (x : Rd d) : |cosGauss a w s x| ≤ ∑ k, |a k| := by
  unfold cosGauss
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (-(s * ‖x‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have := mul_nonneg hs (sq_nonneg ‖x‖); linarith)
  calc |Real.cos ⟪w k, x⟫| * Real.exp (-(s * ‖x‖ ^ 2)) ≤ 1 * 1 :=
        mul_le_mul (Real.abs_cos_le_one _) h1 (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

theorem continuous_cosGauss {ι : Type*} [Fintype ι] (a : ι → ℝ) (w : ι → Rd d) (s : ℝ) :
    Continuous (cosGauss a w s) := by
  unfold cosGauss
  fun_prop

/-! ## The transform of a symmetric law -/

/-- The real part of a transform is the integral of the cosine. -/
theorem re_charFun_eq (L : Measure (Rd d)) [IsFiniteMeasure L] (ω : Rd d) :
    (charFun L ω).re = ∫ x, Real.cos ⟪x, ω⟫ ∂L := by
  have hint : Integrable (fun x : Rd d => Complex.exp (⟪x, ω⟫ * Complex.I)) L :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply, ← RCLike.re_to_complex, ← integral_re hint]
  congr 1
  funext x
  simp [Complex.exp_ofReal_mul_I_re]

/-- The imaginary part of a transform is the integral of the sine. -/
theorem im_charFun (L : Measure (Rd d)) [IsFiniteMeasure L] (ω : Rd d) :
    (charFun L ω).im = ∫ x, Real.sin ⟪x, ω⟫ ∂L := by
  have hint : Integrable (fun x : Rd d => Complex.exp (⟪x, ω⟫ * Complex.I)) L :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply, ← RCLike.im_to_complex, ← integral_im hint]
  congr 1
  funext x
  simp [Complex.exp_ofReal_mul_I_im]

/-- The sine integrates to `0` against a symmetric law. -/
theorem integral_sin_eq_zero (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (w : Rd d) : ∫ y, Real.sin ⟪w, y⟫ ∂μ = 0 := by
  have h : ∫ y, Real.sin ⟪w, y⟫ ∂μ = ∫ y, Real.sin ⟪w, -y⟫ ∂μ := by
    conv_lhs => rw [← hsymm]
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [inner_neg_right, Real.sin_neg, integral_neg] at h
  linarith

/-- The transform of a symmetric law is real. -/
theorem charFun_eq_re (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (ω : Rd d) :
    charFun μ ω = ((charFun μ ω).re : ℂ) := by
  have him : (charFun μ ω).im = 0 := by
    rw [im_charFun]
    simp_rw [real_inner_comm ω]
    exact integral_sin_eq_zero μ hsymm ω
  exact Complex.ext (by simp) (by simp [him])

/-- **`μ * cos⟨w,·⟩ = μ̂(w) cos⟨w,·⟩`** for a symmetric law. -/
theorem integral_cos_sub (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (w x : Rd d) :
    ∫ y, Real.cos ⟪w, x - y⟫ ∂μ = (charFun μ w).re * Real.cos ⟪w, x⟫ := by
  have hc : Integrable (fun y : Rd d => Real.cos ⟪w, y⟫) μ :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hs : Integrable (fun y : Rd d => Real.sin ⟪w, y⟫) μ :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have : ∀ y, Real.cos ⟪w, x - y⟫ =
      Real.cos ⟪w, x⟫ * Real.cos ⟪w, y⟫ + Real.sin ⟪w, x⟫ * Real.sin ⟪w, y⟫ := fun y => by
    rw [inner_sub_right, Real.cos_sub]
  simp_rw [this]
  rw [integral_add (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul,
    integral_sin_eq_zero μ hsymm, re_charFun_eq]
  simp_rw [real_inner_comm w]
  ring

/-! ## The output tends to `h` -/

theorem integrable_of_bdd (μ : Measure (Rd d)) [IsFiniteMeasure μ] {g : Rd d → ℝ}
    (hg : Continuous g) {C : ℝ} (hC : ∀ y, |g y| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC y)

theorem exp_neg_le_one {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ≤ 1 :=
  Real.exp_le_one_iff.2 (by linarith)

/-- Pointwise, `|f_s - ∑ₖ aₖ cos⟨wₖ,·⟩| ≤ (∑ₖ|aₖ|)(1 - e^{-s|z|²})`. -/
theorem abs_cosGauss_sub_le {ι : Type*} [Fintype ι] (a : ι → ℝ) (w : ι → Rd d) {s : ℝ}
    (hs : 0 ≤ s) (z : Rd d) :
    |cosGauss a w s z - ∑ k, a k * Real.cos ⟪w k, z⟫| ≤
      (∑ k, |a k|) * (1 - Real.exp (-(s * ‖z‖ ^ 2))) := by
  unfold cosGauss
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have he : Real.exp (-(s * ‖z‖ ^ 2)) ≤ 1 := exp_neg_le_one (by positivity)
  have hc := Real.abs_cos_le_one ⟪w k, z⟫
  rw [show a k * (Real.cos ⟪w k, z⟫ * Real.exp (-(s * ‖z‖ ^ 2))) - a k * Real.cos ⟪w k, z⟫ =
      a k * Real.cos ⟪w k, z⟫ * (Real.exp (-(s * ‖z‖ ^ 2)) - 1) by ring, abs_mul, abs_mul,
    abs_of_nonpos (sub_nonpos.2 he)]
  nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (a k)) (sub_nonneg.2 he)) (sub_nonneg.2 hc)]

/-- **The output against the limit.** `|μ * f_s - h| ≤ (∑ₖ|aₖ|) ∫ (1 - e^{-s|x-y|²}) dμ(y)`. -/
theorem abs_mconvE_cosGauss_sub_le (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) {ι : Type*} [Fintype ι] (a : ι → ℝ) (w : ι → Rd d)
    {s : ℝ} (hs : 0 ≤ s) (f : 𝓢(Rd d, ℝ)) (hf : ∀ x, f x = cosGauss a w s x) (x : Rd d) :
    |mconvE μ f x - cosSum (fun k => a k * (charFun μ (w k)).re) w x| ≤
      (∑ k, |a k|) * ∫ y, (1 - Real.exp (-(s * ‖x - y‖ ^ 2))) ∂μ := by
  have hcos : ∀ k, Integrable (fun y : Rd d => Real.cos ⟪w k, x - y⟫) μ := fun k =>
    integrable_of_bdd μ (by fun_prop) (fun y => Real.abs_cos_le_one _)
  have hh : cosSum (fun k => a k * (charFun μ (w k)).re) w x =
      ∫ y, ∑ k, a k * Real.cos ⟪w k, x - y⟫ ∂μ := by
    rw [integral_finsetSum _ (fun k _ => (hcos k).const_mul _)]
    unfold cosSum
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_cos_sub μ hsymm]
    ring
  have hu : mconvE μ f x = ∫ y, cosGauss a w s (x - y) ∂μ := by
    simp only [mconvE, hf]
  have i1 : Integrable (fun y => cosGauss a w s (x - y)) μ :=
    integrable_of_bdd μ ((continuous_cosGauss a w s).comp (by fun_prop))
      (fun y => abs_cosGauss_le a w hs _)
  have i2 : Integrable (fun y => ∑ k, a k * Real.cos ⟪w k, x - y⟫) μ :=
    integrable_finsetSum _ fun k _ => (hcos k).const_mul _
  have i3 : Integrable (fun y : Rd d => 1 - Real.exp (-(s * ‖x - y‖ ^ 2))) μ :=
    integrable_of_bdd μ (C := 1) (by fun_prop) (fun y => by
      have h0 : 0 < Real.exp (-(s * ‖x - y‖ ^ 2)) := Real.exp_pos _
      have h1 : Real.exp (-(s * ‖x - y‖ ^ 2)) ≤ 1 := exp_neg_le_one (by positivity)
      rw [abs_le]; constructor <;> linarith)
  rw [hu, hh, ← integral_sub i1 i2, ← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono (i1.sub i2).abs (i3.const_mul _)
    fun y => abs_cosGauss_sub_le a w hs (x - y))

/-- `∫ (1 - e^{-s(1+|y|)²}) dμ → 0` as `s → 0`: some `s ∈ (0,1]` makes it small. -/
theorem exists_small_integral (μ : Measure (Rd d)) [IsProbabilityMeasure μ] {η : ℝ}
    (hη : 0 < η) :
    ∃ s, 0 < s ∧ s ≤ 1 ∧ ∫ y, (1 - Real.exp (-(s * (1 + ‖y‖) ^ 2))) ∂μ < η := by
  set G : ℕ → Rd d → ℝ := fun n y => 1 - Real.exp (-(1 / ((n : ℝ) + 1) * (1 + ‖y‖) ^ 2))
  have hlim : Tendsto (fun n => ∫ y, G n y ∂μ) atTop (𝓝 (∫ _y, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => Continuous.aestronglyMeasurable (by fun_prop)) (integrable_const 1)
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · have h0 : 0 ≤ 1 / ((n : ℝ) + 1) * (1 + ‖y‖) ^ 2 := by positivity
      have h1 := exp_neg_le_one h0
      have h2 := Real.exp_pos (-(1 / ((n : ℝ) + 1) * (1 + ‖y‖) ^ 2))
      rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [G]; linarith)]
      simp only [G]
      linarith
    · have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hc : Continuous fun t : ℝ => 1 - Real.exp (-(t * (1 + ‖y‖) ^ 2)) := by fun_prop
      have := (hc.tendsto 0).comp ht
      simp only [zero_mul, neg_zero, Real.exp_zero, sub_self] at this
      exact this
  rw [integral_zero] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  refine ⟨1 / ((N : ℝ) + 1), by positivity, ?_, hN⟩
  rw [div_le_one (by positivity)]
  linarith [N.cast_nonneg (α := ℝ)]

/-- **The outputs converge**: for `η > 0` some `s ∈ (0,1]` has `|μ * f_s - h| < η` on the unit
ball. -/
theorem exists_close (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) {ι : Type*} [Fintype ι] (a : ι → ℝ) (w : ι → Rd d)
    {η : ℝ} (hη : 0 < η) :
    ∃ s, 0 < s ∧ s ≤ 1 ∧ ∀ f : 𝓢(Rd d, ℝ), (∀ x, f x = cosGauss a w s x) → ∀ x, ‖x‖ ≤ 1 →
      |mconvE μ f x - cosSum (fun k => a k * (charFun μ (w k)).re) w x| < η := by
  set A := ∑ k, |a k| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => abs_nonneg _
  obtain ⟨s, hs, hs1, hsm⟩ := exists_small_integral μ (η := η / (A + 1)) (by positivity)
  refine ⟨s, hs, hs1, fun f hf x hx => ?_⟩
  refine (abs_mconvE_cosGauss_sub_le μ hsymm a w hs.le f hf x).trans_lt ?_
  have hb : ∀ t : ℝ, 0 ≤ t → |1 - Real.exp (-(s * t))| ≤ 1 := fun t ht => by
    have h0 : 0 < Real.exp (-(s * t)) := Real.exp_pos _
    have h1 : Real.exp (-(s * t)) ≤ 1 := exp_neg_le_one (by positivity)
    rw [abs_le]; constructor <;> linarith
  have hmono : ∫ y, (1 - Real.exp (-(s * ‖x - y‖ ^ 2))) ∂μ ≤
      ∫ y, (1 - Real.exp (-(s * (1 + ‖y‖) ^ 2))) ∂μ := by
    refine integral_mono (integrable_of_bdd μ (by fun_prop) fun y => hb _ (by positivity))
      (integrable_of_bdd μ (by fun_prop) fun y => hb _ (by positivity)) fun y => ?_
    have h1 : ‖x - y‖ ≤ 1 + ‖y‖ := (norm_sub_le x y).trans (by linarith)
    have h2 : ‖x - y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : Real.exp (-(s * (1 + ‖y‖) ^ 2)) ≤ Real.exp (-(s * ‖x - y‖ ^ 2)) :=
      Real.exp_le_exp.2 (by nlinarith)
    simp only
    linarith
  calc A * ∫ y, (1 - Real.exp (-(s * ‖x - y‖ ^ 2))) ∂μ
      ≤ A * (η / (A + 1)) := mul_le_mul_of_nonneg_left (hmono.trans hsm.le) hA0
    _ < η := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith

/-! ## The strict maximum of `h` -/

theorem abs_cos_sub_one_add_sq_le {y : ℝ} (hy : |y| ≤ 1) :
    |Real.cos y - 1 + y ^ 2 / 2| ≤ y ^ 4 := by
  have h := Real.cos_bound hy
  rw [show Real.cos y - 1 + y ^ 2 / 2 = Real.cos y - (1 - y ^ 2 / 2) by ring]
  refine h.trans ?_
  rw [show |y| ^ 4 = y ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
  nlinarith [pow_nonneg (sq_nonneg y) 2, show y ^ 4 = (y ^ 2) ^ 2 by ring]

/-- **`h` has a strict maximum at `0`**: if `∑ₖ bₖ⟨wₖ,x⟩² ≥ c|x|²`, `c > 0`, then
`h(x) ≤ h(0) - c|x|²/4` near `0`. -/
theorem cosSum_le {ι : Type*} [Fintype ι] (b : ι → ℝ) (w : ι → Rd d) {c : ℝ} (hc : 0 < c)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ∑ k, b k * ⟪w k, x⟫ ^ 2) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧
      ∀ x, ‖x‖ ≤ r0 → cosSum b w x ≤ cosSum b w 0 - c / 4 * ‖x‖ ^ 2 := by
  obtain ⟨W, hW⟩ : ∃ W, W = ∑ k, ‖w k‖ := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = ∑ k, |b k| * ‖w k‖ ^ 4 := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := hW ▸ Finset.sum_nonneg fun k _ => norm_nonneg _
  have hK0 : 0 ≤ K := hK ▸ Finset.sum_nonneg fun k _ => by positivity
  refine ⟨min 1 (min (1 / (W + 1)) (c / (4 * K + 4))), by positivity, min_le_left _ _,
    fun x hx => ?_⟩
  have hx1 : ‖x‖ ≤ 1 := hx.trans (min_le_left _ _)
  have hxW : ‖x‖ ≤ 1 / (W + 1) := hx.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hxK : ‖x‖ ≤ c / (4 * K + 4) := hx.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hy : ∀ k, |⟪w k, x⟫| ≤ 1 := fun k => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hk : ‖w k‖ ≤ W := hW ▸ Finset.single_le_sum (f := fun k => ‖w k‖)
      (fun k _ => norm_nonneg _) (Finset.mem_univ k)
    calc ‖w k‖ * ‖x‖ ≤ (W + 1) * (1 / (W + 1)) := by
          gcongr
          linarith
      _ = 1 := by field_simp
  have h4 : ∀ k, ⟪w k, x⟫ ^ 4 ≤ ‖w k‖ ^ 4 * ‖x‖ ^ 4 := fun k => by
    have := abs_real_inner_le_norm (w k) x
    rw [show ⟪w k, x⟫ ^ 4 = |⟪w k, x⟫| ^ 4 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs], ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) this 4
  have hsplit : cosSum b w x - cosSum b w 0 =
      -(∑ k, b k * ⟪w k, x⟫ ^ 2) / 2 + ∑ k, b k * (Real.cos ⟪w k, x⟫ - 1 + ⟪w k, x⟫ ^ 2 / 2) := by
    simp only [cosSum, inner_zero_right, Real.cos_zero, mul_one, ← Finset.sum_sub_distrib,
      Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hrem : ∑ k, b k * (Real.cos ⟪w k, x⟫ - 1 + ⟪w k, x⟫ ^ 2 / 2) ≤ K * ‖x‖ ^ 4 := by
    rw [hK, Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    calc b k * (Real.cos ⟪w k, x⟫ - 1 + ⟪w k, x⟫ ^ 2 / 2)
        ≤ |b k * (Real.cos ⟪w k, x⟫ - 1 + ⟪w k, x⟫ ^ 2 / 2)| := le_abs_self _
      _ = |b k| * |Real.cos ⟪w k, x⟫ - 1 + ⟪w k, x⟫ ^ 2 / 2| := abs_mul _ _
      _ ≤ |b k| * (‖w k‖ ^ 4 * ‖x‖ ^ 4) := by
          gcongr
          exact (abs_cos_sub_one_add_sq_le (hy k)).trans (h4 k)
      _ = |b k| * ‖w k‖ ^ 4 * ‖x‖ ^ 4 := by ring
  have hKx : K * ‖x‖ ^ 4 ≤ c / 4 * ‖x‖ ^ 2 := by
    have hx0 := norm_nonneg x
    have hKc : K * ‖x‖ ^ 2 ≤ c / 4 := by
      have hxx : ‖x‖ ^ 2 ≤ ‖x‖ := by
        rw [sq]; exact mul_le_of_le_one_left hx0 hx1
      have h1 : K * ‖x‖ ^ 2 ≤ K * (c / (4 * K + 4)) :=
        mul_le_mul_of_nonneg_left (hxx.trans hxK) hK0
      have h2 : K * (c / (4 * K + 4)) ≤ c / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_nonneg hK0 hc.le]
      exact h1.trans h2
    calc K * ‖x‖ ^ 4 = (K * ‖x‖ ^ 2) * ‖x‖ ^ 2 := by ring
      _ ≤ c / 4 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hKc (by positivity)
  have := hQ x
  linarith

/-- Near `0` the input is close to `∑ₖ aₖ`: `f_s(x) ≤ ∑ₖ aₖ + A₁|x|²` for `s ≤ 1`. -/
theorem cosGauss_le {ι : Type*} [Fintype ι] (a : ι → ℝ) (w : ι → Rd d) {s : ℝ} (hs : 0 ≤ s)
    (hs1 : s ≤ 1) (x : Rd d) :
    cosGauss a w s x ≤ ∑ k, a k + (∑ k, |a k| * (‖w k‖ ^ 2 / 2 + 1)) * ‖x‖ ^ 2 := by
  have hsub : cosGauss a w s x - ∑ k, a k =
      ∑ k, a k * (Real.cos ⟪w k, x⟫ * Real.exp (-(s * ‖x‖ ^ 2)) - 1) := by
    unfold cosGauss
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hterm : ∀ k, a k * (Real.cos ⟪w k, x⟫ * Real.exp (-(s * ‖x‖ ^ 2)) - 1) ≤
      |a k| * (‖w k‖ ^ 2 / 2 + 1) * ‖x‖ ^ 2 := fun k => by
    set y := ⟪w k, x⟫
    set e := Real.exp (-(s * ‖x‖ ^ 2))
    have he0 : 0 < e := Real.exp_pos _
    have he1 : e ≤ 1 := exp_neg_le_one (by positivity)
    have he2 : 1 - e ≤ ‖x‖ ^ 2 := by
      have := Real.add_one_le_exp (-(s * ‖x‖ ^ 2))
      have : s * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 := mul_le_of_le_one_left (by positivity) hs1
      linarith
    have hc1 : Real.cos y ≤ 1 := Real.cos_le_one y
    have hc2 : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
    have hy2 : y ^ 2 ≤ ‖w k‖ ^ 2 * ‖x‖ ^ 2 := by
      rw [← mul_pow]
      exact sq_le_sq' (abs_le.1 (abs_real_inner_le_norm _ _)).1
        (abs_le.1 (abs_real_inner_le_norm _ _)).2
    have habs : |Real.cos y * e - 1| ≤ (‖w k‖ ^ 2 / 2 + 1) * ‖x‖ ^ 2 := by
      rw [show Real.cos y * e - 1 = (Real.cos y - 1) * e + (e - 1) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos he0, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      nlinarith
    calc a k * (Real.cos y * e - 1) ≤ |a k * (Real.cos y * e - 1)| := le_abs_self _
      _ = |a k| * |Real.cos y * e - 1| := abs_mul _ _
      _ ≤ |a k| * ((‖w k‖ ^ 2 / 2 + 1) * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ = _ := by ring
  have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm k
  rw [← Finset.sum_mul] at this
  linarith

/-! ## The inequality -/

/-- **The principle against the test inputs.** For a symmetric probability `μ` with the principle
and `aₖ`, `wₖ` with `∑ₖ aₖμ̂(wₖ)⟨wₖ,x⟩² ≥ c|x|²`, `c > 0`: `∑ₖ aₖμ̂(wₖ) ≤ ∑ₖ aₖ`. -/
theorem sum_le_of_principle (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (hP : HasImplicitEulerPrinciple μ)
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (w : ι → Rd d) {c : ℝ} (hc : 0 < c)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ∑ k, a k * (charFun μ (w k)).re * ⟪w k, x⟫ ^ 2) :
    ∑ k, a k * (charFun μ (w k)).re ≤ ∑ k, a k := by
  set b : ι → ℝ := fun k => a k * (charFun μ (w k)).re with hb
  obtain ⟨r0, hr0, hr01, hh⟩ := cosSum_le b w hc hQ
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = ∑ k, |a k| * (‖w k‖ ^ 2 / 2 + 1) := ⟨_, rfl⟩
  have hA10 : 0 ≤ A1 := hA1 ▸ Finset.sum_nonneg fun k _ => by positivity
  have hh0 : cosSum b w 0 = ∑ k, b k := by simp [cosSum]
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨η, hη, hηdef⟩ : ∃ η, 0 < η ∧ η = ∑ k, b k - ∑ k, a k := ⟨_, by linarith, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = min r0 (η / (A1 + c + 1)) := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; exact lt_min hr0 (by positivity)
  have hrr0 : r ≤ r0 := hr ▸ min_le_left _ _
  have hr1 : r ≤ 1 := hrr0.trans hr01
  have hrη : (A1 + c / 8) * r ^ 2 < η := by
    have h1 : r ^ 2 ≤ r := by rw [sq]; exact mul_le_of_le_one_left hrpos.le hr1
    have h2 : r ≤ η / (A1 + c + 1) := hr ▸ min_le_right _ _
    calc (A1 + c / 8) * r ^ 2 ≤ (A1 + c / 8) * (η / (A1 + c + 1)) := by gcongr; exact h1.trans h2
      _ < η := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith
  obtain ⟨s, hs, hs1, hclose⟩ := exists_close μ hsymm a w (η := c * r ^ 2 / 8) (by positivity)
  obtain ⟨f, hf⟩ := exists_cosGauss a w hs
  have hcl := hclose f hf
  have hu_cont : Continuous (mconvE μ f) :=
    continuous_mconvE_of_bdd μ f.continuous (A := ∑ k, |a k|)
      (fun z => by rw [hf]; exact abs_cosGauss_le a w hs.le z)
  obtain ⟨x0, hx0, hmax⟩ := (isCompact_closedBall (0 : Rd d) r).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self hrpos.le⟩ hu_cont.continuousOn
  have hx0n : ‖x0‖ ≤ r := by simpa using hx0
  have hu0 : ∑ k, b k - c * r ^ 2 / 8 < mconvE μ f 0 := by
    have := (abs_lt.1 (hcl 0 (by simp))).1
    rw [hh0] at this
    linarith
  have h3 : mconvE μ f 0 ≤ mconvE μ f x0 := hmax (Metric.mem_closedBall_self hrpos.le)
  have hint : ‖x0‖ < r := by
    by_contra hge
    rw [not_lt] at hge
    have heq : ‖x0‖ = r := le_antisymm hx0n hge
    have h1 := hh x0 (heq ▸ hrr0)
    have h2 := (abs_lt.1 (hcl x0 (hx0n.trans hr1))).2
    rw [heq, hh0] at h1
    linarith
  have hloc : IsLocalMax (mconvE μ f) x0 :=
    hmax.isLocalMax (Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds (by simpa using hint)) Metric.ball_subset_closedBall)
  have hPx := (hP f x0).1 hloc
  have hfx := cosGauss_le a w hs.le hs1 x0
  rw [← hf, ← hA1] at hfx
  have hx2 : ‖x0‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx0n 2
  nlinarith

/-! ## The reciprocal is one plus a quadratic form -/

theorem inner_ebasis (i : Fin d) (x : Rd d) : ⟪ebasis i, x⟫ = x i := by
  simp [ebasis, EuclideanSpace.inner_single_left]

theorem norm_sq_eq_sum_inner_ebasis (x : Rd d) : ‖x‖ ^ 2 = ∑ i, ⟪ebasis i, x⟫ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [inner_ebasis, sq_abs]

theorem nonneg_of_forall_pos_add {t S : ℝ} (h : ∀ ε : ℝ, 0 < ε → 0 ≤ t + ε * S) : 0 ≤ t := by
  by_contra ht
  rw [not_le] at ht
  have hε : 0 < -t / (|S| + 1) := div_pos (by linarith) (by positivity)
  have h1 := h _ hε
  have h2 : -t / (|S| + 1) * S ≤ -t / (|S| + 1) * |S| :=
    mul_le_mul_of_nonneg_left (le_abs_self S) hε.le
  have h3 : -t / (|S| + 1) * |S| < -t := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg S]
  linarith

theorem continuous_re_charFun (μ : Measure (Rd d)) [IsFiniteMeasure μ] :
    Continuous fun ω => (charFun μ ω).re :=
  Complex.continuous_re.comp continuous_charFun

/-- **The transform has no zero.** At a zero `ω₀`, the coefficient of `cos⟨ω₀,·⟩` is free on the
right of `sum_le_of_principle` and absent on the left. -/
theorem re_charFun_ne_zero (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (hP : HasImplicitEulerPrinciple μ) (ω₀ : Rd d) :
    (charFun μ ω₀).re ≠ 0 := by
  intro h0
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 (continuous_re_charFun μ) 0 (1 / 2)
    (by norm_num)
  have hρ0 : (charFun μ 0).re = 1 := by simp [charFun_zero]
  set t := δ / 2 with ht
  have htpos : 0 < t := by positivity
  have hρ : ∀ i : Fin d, 1 / 2 ≤ (charFun μ (t • ebasis i)).re := fun i => by
    have hd : dist (t • ebasis i) 0 < δ := by
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      simp [ebasis]
      linarith
    have := hball _ hd
    rw [Real.dist_eq, hρ0, abs_lt] at this
    linarith
  set a : Option (Fin d) → ℝ := fun o => o.elim (-(d : ℝ) - 1) fun _ => 1 with ha
  set w : Option (Fin d) → Rd d := fun o => o.elim ω₀ fun i => t • ebasis i with hw
  have hQ : ∀ x, t ^ 2 / 2 * ‖x‖ ^ 2 ≤ ∑ k, a k * (charFun μ (w k)).re * ⟪w k, x⟫ ^ 2 := by
    intro x
    rw [Fintype.sum_option, norm_sq_eq_sum_inner_ebasis, Finset.mul_sum]
    simp only [ha, hw, Option.elim, h0, mul_zero, zero_mul, zero_add, one_mul, inner_smul_left,
      RCLike.conj_to_real]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hρ i
    nlinarith [sq_nonneg (t * ⟪ebasis i, x⟫), sq_nonneg ⟪ebasis i, x⟫, sq_nonneg t]
  have key := sum_le_of_principle μ hsymm hP a w (by positivity) hQ
  rw [Fintype.sum_option, Fintype.sum_option] at key
  simp only [ha, hw, Option.elim, h0, mul_zero, zero_add, one_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at key
  have hsum : 0 ≤ ∑ i : Fin d, (charFun μ (t • ebasis i)).re :=
    Finset.sum_nonneg fun i _ => by linarith [hρ i]
  linarith

/-- `m(ω) := μ̂(ω)⁻¹ - 1`, the reciprocal less one. -/
noncomputable def recipSub (μ : Measure (Rd d)) (ω : Rd d) : ℝ := ((charFun μ ω).re)⁻¹ - 1

/-- **The inequality on `m`**: `∑ₖ bₖ⟨wₖ,x⟩² ≥ c|x|²`, `c > 0`, gives `∑ₖ bₖ m(wₖ) ≥ 0`. -/
theorem sum_recipSub_nonneg (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (hP : HasImplicitEulerPrinciple μ)
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (w : ι → Rd d) {c : ℝ} (hc : 0 < c)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ∑ k, b k * ⟪w k, x⟫ ^ 2) :
    0 ≤ ∑ k, b k * recipSub μ (w k) := by
  have hne := re_charFun_ne_zero μ hsymm hP
  set a : ι → ℝ := fun k => b k / (charFun μ (w k)).re with ha
  have hab : ∀ k, a k * (charFun μ (w k)).re = b k := fun k => by
    simp only [ha]; field_simp [hne (w k)]
  have key := sum_le_of_principle μ hsymm hP a w hc (by simpa only [hab] using hQ)
  simp only [hab] at key
  have : ∑ k, b k * recipSub μ (w k) = ∑ k, a k - ∑ k, b k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [recipSub, ha]
    ring
  linarith

/-- **`m` vanishes on the kernel**: `∑ₖ bₖ⟨wₖ,·⟩² = 0` gives `∑ₖ bₖ m(wₖ) = 0`. -/
theorem sum_recipSub_eq_zero (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (hP : HasImplicitEulerPrinciple μ)
    {ι : Type*} [Fintype ι] (b : ι → ℝ) (w : ι → Rd d)
    (hQ : ∀ x, ∑ k, b k * ⟪w k, x⟫ ^ 2 = 0) :
    ∑ k, b k * recipSub μ (w k) = 0 := by
  have half : ∀ b : ι → ℝ, (∀ x, ∑ k, b k * ⟪w k, x⟫ ^ 2 = 0) →
      0 ≤ ∑ k, b k * recipSub μ (w k) := fun b hb => by
    refine nonneg_of_forall_pos_add (S := ∑ i : Fin d, recipSub μ (ebasis i)) fun ε hε => ?_
    have := sum_recipSub_nonneg μ hsymm hP (Sum.elim b fun _ : Fin d => ε)
      (Sum.elim w fun i => ebasis i) hε (fun x => by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, hb x, zero_add, norm_sq_eq_sum_inner_ebasis,
          Finset.mul_sum]
        exact le_rfl)
    rw [Fintype.sum_sum_type] at this
    simpa [Finset.mul_sum] using this
  have h1 := half b hQ
  have h2 := half (fun k => -b k) fun x => by
    simp only [neg_mul, Finset.sum_neg_distrib, hQ x, neg_zero]
  simp only [neg_mul, Finset.sum_neg_distrib] at h2
  linarith

/-- `m ≥ 0`. -/
theorem recipSub_nonneg (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (hP : HasImplicitEulerPrinciple μ) (ω : Rd d) :
    0 ≤ recipSub μ ω := by
  refine nonneg_of_forall_pos_add (S := ∑ i : Fin d, recipSub μ (ebasis i)) fun ε hε => ?_
  have := sum_recipSub_nonneg μ hsymm hP (Sum.elim (fun _ : Unit => (1 : ℝ)) fun _ : Fin d => ε)
    (Sum.elim (fun _ => ω) fun i => ebasis i) hε (fun x => by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton, one_mul,
        norm_sq_eq_sum_inner_ebasis, Finset.mul_sum]
      linarith [sq_nonneg ⟪ω, x⟫])
  rw [Fintype.sum_sum_type] at this
  simpa [Finset.mul_sum] using this

theorem inner_eq_sum_mul (ω x : Rd d) : ⟪ω, x⟫ = ∑ i, ω i * x i := by
  simp [PiLp.inner_apply, mul_comm]

theorem quad_eq_sum_mul (S : Mat d) (ω : Rd d) : quad S ω = ∑ i, ∑ j, S i j * (ω i * ω j) := by
  rw [quad_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The polarization matrix** `Mᵢⱼ := (m(eᵢ + eⱼ) - m(eᵢ) - m(eⱼ))/2`. -/
noncomputable def recipMat (μ : Measure (Rd d)) : Mat d :=
  Matrix.of fun i j =>
    (recipSub μ (ebasis i + ebasis j) - recipSub μ (ebasis i) - recipSub μ (ebasis j)) / 2

theorem recipMat_isHermitian (μ : Measure (Rd d)) : (recipMat μ).IsHermitian :=
  Matrix.IsHermitian.ext fun i j => by
    simp only [recipMat, Matrix.of_apply, star_trivial]
    rw [add_comm (ebasis j)]
    ring

/-- **`m` is the quadratic form of `M`**, by `sum_recipSub_eq_zero` on the family
`(1, ω)`, `(-ωᵢωⱼ/2, eᵢ + eⱼ)`, `(ωᵢωⱼ/2, eᵢ)`, `(ωᵢωⱼ/2, eⱼ)`, whose form
`⟨ω,x⟩² - ∑ᵢⱼ ωᵢωⱼxᵢxⱼ` vanishes. -/
theorem recipSub_eq_quad (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (hP : HasImplicitEulerPrinciple μ) (ω : Rd d) :
    recipSub μ ω = quad (recipMat μ) ω := by
  let b : Unit ⊕ ((Fin d × Fin d) ⊕ ((Fin d × Fin d) ⊕ (Fin d × Fin d))) → ℝ :=
    Sum.elim (fun _ => 1) (Sum.elim (fun p => -(ω p.1 * ω p.2) / 2)
      (Sum.elim (fun p => ω p.1 * ω p.2 / 2) fun p => ω p.1 * ω p.2 / 2))
  let w : Unit ⊕ ((Fin d × Fin d) ⊕ ((Fin d × Fin d) ⊕ (Fin d × Fin d))) → Rd d :=
    Sum.elim (fun _ => ω) (Sum.elim (fun p => ebasis p.1 + ebasis p.2)
      (Sum.elim (fun p => ebasis p.1) fun p => ebasis p.2))
  have hQ : ∀ x, ∑ k, b k * ⟪w k, x⟫ ^ 2 = 0 := fun x => by
    simp only [b, w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
      Finset.sum_singleton, one_mul, inner_add_left, inner_ebasis, Fintype.sum_prod_type]
    rw [inner_eq_sum_mul, sq, Finset.sum_mul_sum]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    ring
  have key := sum_recipSub_eq_zero μ hsymm hP b w hQ
  simp only [b, w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique,
    Finset.sum_singleton, one_mul, Fintype.sum_prod_type] at key
  rw [quad_eq_sum_mul]
  have hM : ∑ i, ∑ j, recipMat μ i j * (ω i * ω j) =
      -(∑ i, ∑ j, -(ω i * ω j) / 2 * recipSub μ (ebasis i + ebasis j) +
        (∑ i, ∑ j, ω i * ω j / 2 * recipSub μ (ebasis i) +
          ∑ i, ∑ j, ω i * ω j / 2 * recipSub μ (ebasis j))) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [recipMat, Matrix.of_apply]
    ring
  rw [hM]
  linarith

theorem recipMat_posSemidef (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (hP : HasImplicitEulerPrinciple μ) :
    (recipMat μ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (recipMat_isHermitian μ) fun x => ?_
  have h := recipSub_nonneg μ hsymm hP (WithLp.toLp 2 x)
  rw [recipSub_eq_quad μ hsymm hP, quad_eq_dotProduct] at h
  simpa using h

/-! ## `prop:stage-lemma`(3) -/

/-- **`prop:stage-lemma`(3), the converse.** A symmetric probability with the principle has
`1/μ̂(ω) = 1 + ω·Cω` for a positive semidefinite `C`. -/
theorem stage_lemma_3 (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (hP : HasImplicitEulerPrinciple μ) :
    ∃ C : Mat d, C.PosSemidef ∧ ∀ ω, charFun μ ω = (((1 + quad C ω)⁻¹ : ℝ) : ℂ) := by
  refine ⟨recipMat μ, recipMat_posSemidef μ hsymm hP, fun ω => ?_⟩
  rw [charFun_eq_re μ hsymm ω, ← recipSub_eq_quad μ hsymm hP, recipSub, add_sub_cancel, inv_inv]

/-- **`prop:stage-lemma`(3), rotation invariance.** If moreover `μ` is rotation invariant, then
`C = τI` with `τ ≥ 0`, `μ` is the Helmholtz resolvent, and the identity when `τ = 0`. -/
theorem stage_lemma_3_rotation (hd : 1 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (hP : HasImplicitEulerPrinciple μ)
    (hrot : IsRotationInvariant μ) :
    ∃ τ : ℝ, 0 ≤ τ ∧ (∀ ω, charFun μ ω = (((1 + τ * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ)) ∧
      (∀ C : Mat d, C.PosSemidef → (∀ ω, charFun μ ω = (((1 + quad C ω)⁻¹ : ℝ) : ℂ)) →
        C = τ • (1 : Mat d)) ∧
      (τ = 0 → μ = Measure.dirac 0) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hμ⟩ := stage_lemma_3 μ hsymm hP
  have hinj : ∀ p q : ℝ, (((1 + p)⁻¹ : ℝ) : ℂ) = (((1 + q)⁻¹ : ℝ) : ℂ) → p = q := fun p q h => by
    have := inv_injective (Complex.ofReal_injective h)
    linarith
  have hτ : ∀ ω, quad C ω = quad C (ebasis 0) * ‖ω‖ ^ 2 := fun ω => by
    have h1 := charFun_eq_norm_smul_ebasis hrot ω
    rw [hμ, hμ] at h1
    rw [hinj _ _ h1, AffineHemigroup.quad_smul_vec]
    ring
  refine ⟨quad C (ebasis 0), AffineHemigroup.quad_nonneg hC _, fun ω => by rw [hμ, hτ],
    fun C' hC' h => ?_, fun h0 => ?_⟩
  · refine eq_of_quad_eq hC'.1 (Matrix.IsHermitian.ext fun i j => ?_) fun x => ?_
    · simp only [Matrix.smul_apply, Matrix.one_apply, star_trivial, eq_comm (a := j)]
    · rw [hinj _ _ ((h x).symm.trans (hμ x)), hτ, AffineHemigroup.quad_smul, quad_one]
  · refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [hμ, hτ, h0, charFun_dirac]
    simp

end Pyramids
