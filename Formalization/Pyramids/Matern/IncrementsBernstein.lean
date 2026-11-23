/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.CompletelyMonotone
import Pyramids.Matern.BesselProfile
import AffineHemigroup.BernsteinUnique

/-!
# `prop:matern-increments`(1): the Bernstein function `f_{β,γ}`

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:matern-increments`. Phase 5, wave 3b.
`matern_increments_1` moved here from `PyramidsSkeleton.Ch04Matern`, its statement unchanged.

* **Complete monotonicity.** It is invariant under `x ↦ cx`, `c > 0`
  (`IsCompletelyMonotone.comp_mul`); `(x + a)⁻¹` is completely monotone for `a ≥ 0` (Mathlib's
  `iter_deriv_inv_linear`); so is `m_{a,b}(τ) = (e^{-aτ} - e^{-bτ})/τ = ∫_a^b e^{-τx} dx`, a Laplace
  transform on `(1,∞)` after `x = as` (`isCompletelyMonotone_laplace`).
* **The density of a Bernstein function is unique** (`bernstein_density_eqOn`). Two representations
  `a + bx + ∫(1 - e^{-xt}) m(t) dt` with `m, m' ≥ 0` continuous on `(0,∞)` have `m = m'` there: the
  measures `m(t) dt` and `m'(t) dt` are equal by the affine export's `bernstein_triplet_unique`
  (the uniqueness of the Laplace transform, Lean core), so the densities agree almost
  everywhere, and everywhere on `(0,∞)` by continuity. A Thorin–Bernstein representation is read
  through it: `t m(t)` is completely monotone, hence continuous and nonnegative.
* **Clause (1).** The two integral forms are the fundamental theorem of calculus and the difference
  of two Frullani integrals (`lintegral_frullani_log`). `f_{β,γ}' = (x + 1/β)⁻¹ - (x + 1/γ)⁻¹` is
  completely monotone as `f₀ - f₀(· + h)` (`completelyMonotone_sub_shift`). `t m_{β,γ}(t) =
  e^{-t/β} - e^{-t/γ}` is positive on `(0,∞)` and tends to `0` at `0`, so it is not nonincreasing,
  hence not completely monotone, and by the uniqueness of the density `f_{β,γ}` is not Thorin.

**What it reaches.** Lean core only.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter
open scoped Topology Nat ENNReal

/-! ## Complete monotonicity -/

/-- **Complete monotonicity is invariant under `x ↦ cx`**, `c > 0`. -/
theorem IsCompletelyMonotone.comp_mul {f : ℝ → ℝ} (hf : IsCompletelyMonotone f) {c : ℝ}
    (hc : 0 < c) : IsCompletelyMonotone (fun x => f (c * x)) := by
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hmaps : MapsTo (fun x : ℝ => c * x) (Ioi 0) (Ioi 0) := fun x hx => mul_pos hc hx
  have hit : ∀ n : ℕ, EqOn (iteratedDerivWithin n (fun x => f (c * x)) (Ioi 0))
      (fun x => c ^ n * iteratedDerivWithin n f (Ioi 0) (c * x)) (Ioi 0) := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih hx)]
      have hcx : c * x ∈ Ioi (0 : ℝ) := hmaps hx
      have hd : DifferentiableAt ℝ (iteratedDerivWithin n f (Ioi 0)) (c * x) :=
        ((hf.1.differentiableOn_iteratedDerivWithin (by exact_mod_cast ENat.coe_lt_top n) hU)
          (c * x) hcx).differentiableAt (isOpen_Ioi.mem_nhds hcx)
      have h1 : deriv (iteratedDerivWithin n f (Ioi 0)) (c * x) =
          iteratedDerivWithin (n + 1) f (Ioi 0) (c * x) := by
        rw [iteratedDerivWithin_succ, derivWithin_of_isOpen isOpen_Ioi hcx]
      have h2 : HasDerivAt (fun x => c ^ n * iteratedDerivWithin n f (Ioi 0) (c * x))
          (c ^ n * (iteratedDerivWithin (n + 1) f (Ioi 0) (c * x) * c)) x := by
        have := hd.hasDerivAt.comp x ((hasDerivAt_id x).const_mul c)
        rw [h1] at this
        simpa using this.const_mul (c ^ n)
      rw [h2.hasDerivWithinAt.derivWithin (hU x hx)]
      ring
  refine ⟨hf.1.comp (contDiffOn_const.mul contDiffOn_id) hmaps, fun n x hx => ?_⟩
  rw [hit n hx, mul_left_comm]
  exact mul_nonneg (pow_nonneg hc.le n) (hf.2 n _ (hmaps hx))

/-- **`(x + a)⁻¹` is completely monotone** for `a ≥ 0`. -/
theorem isCompletelyMonotone_inv_add {a : ℝ} (ha : 0 ≤ a) :
    IsCompletelyMonotone (fun x => (x + a)⁻¹) := by
  have hpos : ∀ x ∈ Ioi (0 : ℝ), x + a ≠ 0 := fun x (hx : 0 < x) => by positivity
  refine ⟨(contDiffOn_id.add contDiffOn_const).inv hpos, fun n x hx => ?_⟩
  rw [iteratedDerivWithin_of_isOpen isOpen_Ioi hx, iteratedDeriv_eq_iterate]
  have h := iter_deriv_inv_linear n (1 : ℝ) a
  simp only [one_mul] at h
  rw [h]
  simp only [one_pow, mul_one]
  have hxa : 0 < x + a := by have : (0 : ℝ) < x := hx; positivity
  have h2 : (-1 : ℝ) ^ n * ((-1) ^ n * n ! * (x + a) ^ (-1 - (n : ℤ))) =
      n ! * (x + a) ^ (-1 - (n : ℤ)) := by
    rw [← mul_assoc, ← mul_assoc, ← mul_pow]
    norm_num
  rw [h2]
  positivity

/-- `∫₁^{b/a} e^{-aτs} a ds = (e^{-aτ} - e^{-bτ})/τ`. -/
theorem integral_exp_window {a b τ : ℝ} (ha : 0 < a) (hab : a < b) (hτ : 0 < τ) :
    ∫ s in Ioi (1 : ℝ), Real.exp (-(a * τ * s)) * (Iic (b / a)).indicator (fun _ => a) s =
      (Real.exp (-(a * τ)) - Real.exp (-(b * τ))) / τ := by
  have h1 : (1 : ℝ) ≤ b / a := by rw [le_div_iff₀ ha]; linarith
  have hset : ∫ s in Ioi (1 : ℝ), Real.exp (-(a * τ * s)) * (Iic (b / a)).indicator (fun _ => a) s
      = ∫ s in Ioc (1 : ℝ) (b / a), Real.exp (-(a * τ * s)) * a := by
    have hpt : ∀ s, Real.exp (-(a * τ * s)) * (Iic (b / a)).indicator (fun _ => a) s =
        (Iic (b / a)).indicator (fun s => Real.exp (-(a * τ * s)) * a) s := by
      intro s
      by_cases h : s ∈ Iic (b / a) <;> simp [indicator, h]
    simp_rw [hpt]
    rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]
  rw [hset, ← intervalIntegral.integral_of_le h1]
  have hderiv : ∀ s ∈ uIcc (1 : ℝ) (b / a),
      HasDerivAt (fun s => -Real.exp (-(a * τ * s)) / τ) (Real.exp (-(a * τ * s)) * a) s := by
    intro s _
    have h := ((hasDerivAt_id s).const_mul (-(a * τ))).exp.neg.div_const τ
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    · field_simp
      simp
    · simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(a * τ * s)) * a).intervalIntegrable _ _)]
  rw [show a * τ * (b / a) = b * τ by field_simp, mul_one]
  ring

/-- **`m_{a,b}(τ) = (e^{-aτ} - e^{-bτ})/τ` is completely monotone** for `0 < a < b`. -/
theorem isCompletelyMonotone_expWindow {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsCompletelyMonotone (fun τ => (Real.exp (-(a * τ)) - Real.exp (-(b * τ))) / τ) := by
  set w : ℝ → ℝ := (Iic (b / a)).indicator (fun _ => a) with hw
  have hw0 : ∀ s, 0 ≤ w s := fun s => by
    simp only [hw, indicator]; split_ifs <;> linarith
  have hint : ∀ y, 0 < y → IntegrableOn (fun s => Real.exp (-(y * s)) * w s) (Ioi 1) := by
    intro y hy
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi 1 hy).const_mul a) ?_ ?_
    · exact ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(y * s))).aestronglyMeasurable.mul
        ((aestronglyMeasurable_const.indicator measurableSet_Iic)))
    · refine Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hw0 s),
        neg_mul, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      simp only [hw, indicator]; split_ifs <;> linarith
  have h := (isCompletelyMonotone_laplace (fun s _ => hw0 s) hint).comp_mul ha
  refine h.congr fun τ (hτ : 0 < τ) => ?_
  simp only
  rw [← integral_exp_window ha hab hτ]

/-! ## The density of a Bernstein function is unique -/

/-- `1 - e^{-xt} ≤ max 1 x · min 1 t` for `x, t ≥ 0`. -/
theorem one_sub_exp_le_max_mul_min {x t : ℝ} (ht : 0 ≤ t) :
    1 - Real.exp (-(x * t)) ≤ max 1 x * min 1 t := by
  have h1 : 1 - Real.exp (-(x * t)) ≤ x * t := by
    have := Real.add_one_le_exp (-(x * t)); linarith
  have h2 : 1 - Real.exp (-(x * t)) ≤ 1 := by have := Real.exp_pos (-(x * t)); linarith
  rcases le_total t 1 with h | h
  · rw [min_eq_right h]
    calc 1 - Real.exp (-(x * t)) ≤ x * t := h1
      _ ≤ max 1 x * t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht
  · rw [min_eq_left h, mul_one]
    exact h2.trans (le_max_left _ _)

/-- **A Bernstein representation in `[0,∞]`.** For `m ≥ 0` continuous on `(0,∞)` with
`∫(1 ∧ t) m(t) dt < ∞`, the integral `∫(1 - e^{-xt}) m(t) dt` is the lower integral of the same
integrand. -/
theorem ofReal_bernstein_integral {m : ℝ → ℝ} (hm0 : ∀ t, 0 < t → 0 ≤ m t)
    (hmc : ContinuousOn m (Ioi 0))
    (hfin : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (min 1 t * m t) ≠ ⊤) {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t => (1 - Real.exp (-(x * t))) * m t) (Ioi 0) ∧
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ), (1 - Real.exp (-(x * t))) * m t) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (m t) * ENNReal.ofReal (1 - Real.exp (-(x * t))) := by
  have hmeas : AEStronglyMeasurable m (volume.restrict (Ioi (0 : ℝ))) :=
    hmc.aestronglyMeasurable measurableSet_Ioi
  have hmin : IntegrableOn (fun t => min 1 t * m t) (Ioi 0) := by
    refine (lintegral_ofReal_ne_top_iff_integrable
      ((continuous_const.min continuous_id).aestronglyMeasurable.mul hmeas) ?_).1 hfin
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    exact mul_nonneg (le_min zero_le_one ht.le) (hm0 t ht)
  have hint : IntegrableOn (fun t => (1 - Real.exp (-(x * t))) * m t) (Ioi 0) := by
    refine Integrable.mono' (hmin.const_mul (max 1 x)) ?_ ?_
    · exact (by fun_prop : Continuous fun t : ℝ => 1 - Real.exp (-(x * t))).aestronglyMeasurable.mul
        hmeas
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
      have h0 : 0 ≤ 1 - Real.exp (-(x * t)) := by
        have : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (hm0 t ht)), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (one_sub_exp_le_max_mul_min (x := x) ht.le) (hm0 t ht)
  refine ⟨hint, ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hint]
  · refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [← ENNReal.ofReal_mul (hm0 t ht), mul_comm]
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    have : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    exact mul_nonneg (by linarith) (hm0 t ht)

/-- **The density of a Bernstein function is unique.** If `f(x)` is the lower integral
`∫(1 - e^{-xt}) m(t) dt` and also `a + bx + ∫(1 - e^{-xt}) m'(t) dt` for `x > 0`, with `m, m' ≥ 0`
continuous on `(0,∞)`, `a, b ≥ 0` and `∫(1 ∧ t) m'(t) dt < ∞`, then `m = m'` on `(0,∞)`. -/
theorem bernstein_density_eqOn {f m m' : ℝ → ℝ} {a b : ℝ} (hm0 : ∀ t, 0 < t → 0 ≤ m t)
    (hmc : ContinuousOn m (Ioi 0))
    (hrep : ∀ x, 0 < x → ENNReal.ofReal (f x) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (m t) * ENNReal.ofReal (1 - Real.exp (-(x * t))))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm0' : ∀ t, 0 < t → 0 ≤ m' t) (hmc' : ContinuousOn m' (Ioi 0))
    (hfin' : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (min 1 t * m' t) ≠ ⊤)
    (hrep' : ∀ x, 0 < x → f x = a + b * x + ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-(x * t))) * m' t) :
    EqOn m m' (Ioi 0) := by
  set ρ : Measure ℝ := volume.restrict (Ioi 0) with hρ
  have hae : AEMeasurable (fun t => ENNReal.ofReal (m t)) ρ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hmc.aemeasurable measurableSet_Ioi)
  have hae' : AEMeasurable (fun t => ENNReal.ofReal (m' t)) ρ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hmc'.aemeasurable measurableSet_Ioi)
  set M := ρ.withDensity fun t => ENNReal.ofReal (m t) with hM
  set M' := ρ.withDensity fun t => ENNReal.ofReal (m' t) with hM'
  have hnull : ∀ g : ℝ → ℝ≥0∞, (ρ.withDensity g) (Iic 0) = 0 := fun g => by
    rw [withDensity_apply _ measurableSet_Iic, hρ, Measure.restrict_restrict measurableSet_Iic]
    have : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by ext t; simp
    rw [this, Measure.restrict_empty, lintegral_zero_measure]
  have hlin : ∀ (g : ℝ → ℝ≥0∞), AEMeasurable g ρ → ∀ x : ℝ,
      ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(x * t))) ∂(ρ.withDensity g) =
        ∫⁻ t in Ioi (0 : ℝ), g t * ENNReal.ofReal (1 - Real.exp (-(x * t))) := by
    intro g hg x
    rw [lintegral_withDensity_eq_lintegral_mul₀ hg (by fun_prop)]
    rfl
  have hval : ∀ x, 0 < x → ENNReal.ofReal 0 + ENNReal.ofReal (0 * x) +
      ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(x * t))) ∂M = ENNReal.ofReal (f x) := by
    intro x hx
    rw [hlin _ hae x, hrep x hx]
    simp only [ENNReal.ofReal_zero, zero_mul, zero_add]
    rfl
  have hval' : ∀ x, 0 < x → ENNReal.ofReal a + ENNReal.ofReal (b * x) +
      ∫⁻ t, ENNReal.ofReal (1 - Real.exp (-(x * t))) ∂M' = ENNReal.ofReal (f x) := by
    intro x hx
    obtain ⟨hint, hI⟩ := ofReal_bernstein_integral hm0' hmc' hfin' hx.le
    have hI0 : 0 ≤ ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-(x * t))) * m' t := by
      refine setIntegral_nonneg measurableSet_Ioi fun t (ht : 0 < t) => ?_
      have : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      exact mul_nonneg (by linarith) (hm0' t ht)
    rw [hlin _ hae' x, ← hI, hrep' x hx, ENNReal.ofReal_add (by positivity) hI0,
      ENNReal.ofReal_add ha (by positivity)]
  obtain ⟨-, -, hMM⟩ := AffineHemigroup.bernstein_triplet_unique (a := 0) (b := 0) (a' := a)
    (b' := b) (m := M) (m' := M') le_rfl le_rfl ha hb (hnull _) (hnull _)
    (fun σ hσ => by rw [hval σ hσ, hval' σ hσ])
    (fun σ hσ => by rw [hval σ hσ]; exact ENNReal.ofReal_ne_top)
  have hae_eq := (withDensity_eq_iff_of_sigmaFinite hae hae').1 hMM
  have hreal : m =ᵐ[ρ] m' := by
    filter_upwards [hae_eq, ae_restrict_mem measurableSet_Ioi] with t ht (htI : 0 < t)
    have := congrArg ENNReal.toReal ht
    rwa [ENNReal.toReal_ofReal (hm0 t htI), ENNReal.toReal_ofReal (hm0' t htI)] at this
  exact Measure.eqOn_open_of_ae_eq hreal isOpen_Ioi hmc hmc'

/-- **A Thorin–Bernstein representation, read through the uniqueness of the density**: if `f` has
the representation `∫(1 - e^{-xt}) m(t) dt` of `bernstein_density_eqOn` and is a Thorin–Bernstein
function, then `t m(t)` is completely monotone. -/
theorem IsThorinBernstein.completelyMonotone_density {f m : ℝ → ℝ} (hf : IsThorinBernstein f)
    (hm0 : ∀ t, 0 < t → 0 ≤ m t) (hmc : ContinuousOn m (Ioi 0))
    (hrep : ∀ x, 0 < x → ENNReal.ofReal (f x) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (m t) * ENNReal.ofReal (1 - Real.exp (-(x * t)))) :
    IsCompletelyMonotone (fun t => t * m t) := by
  obtain ⟨-, a, b, m', ha, hb, hcm, hfin, hrep'⟩ := hf
  have hm0' : ∀ t, 0 < t → 0 ≤ m' t := fun t ht => by
    have h := hcm.2 0 t ht
    simp only [pow_zero, one_mul, iteratedDerivWithin_zero] at h
    exact nonneg_of_mul_nonneg_right (by linarith) ht
  have hmc' : ContinuousOn m' (Ioi 0) := by
    refine (hcm.1.continuousOn.div continuousOn_id fun t (ht : 0 < t) => ht.ne').congr
      fun t (ht : 0 < t) => ?_
    simp only [Pi.div_apply, id]
    field_simp
  have heq := bernstein_density_eqOn hm0 hmc hrep ha hb hm0' hmc' hfin hrep'
  exact hcm.congr fun t ht => by simp only; rw [heq ht]

/-! ## Clause (1) -/

/-- Frullani's integral `∫₀^∞ (1 - e^{-τu}) e^{-τ/β} dτ/τ = log(1 + βu)` as a Bochner integral,
with its integrability. -/
theorem frullani_integral {β u : ℝ} (hβ : 0 < β) (hu : 0 ≤ u) :
    IntegrableOn (fun τ => (1 - Real.exp (-(τ * u))) * (Real.exp (-τ / β) / τ)) (Ioi 0) ∧
      ∫ τ in Ioi (0 : ℝ), (1 - Real.exp (-(τ * u))) * (Real.exp (-τ / β) / τ) =
        Real.log (1 + β * u) := by
  have hnn : ∀ τ ∈ Ioi (0 : ℝ), 0 ≤ (1 - Real.exp (-(τ * u))) * (Real.exp (-τ / β) / τ) := by
    intro τ (hτ : 0 < τ)
    have : Real.exp (-(τ * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have := Real.exp_pos (-τ / β)
    exact mul_nonneg (by linarith) (by positivity)
  have hlin : ∫⁻ τ in Ioi (0 : ℝ), ENNReal.ofReal
      ((1 - Real.exp (-(τ * u))) * (Real.exp (-τ / β) / τ)) =
        ENNReal.ofReal (Real.log (1 + β * u)) := by
    rw [← lintegral_frullani_log hβ hu]
    refine setLIntegral_congr_fun measurableSet_Ioi fun τ (hτ : 0 < τ) => ?_
    rw [mul_comm, ENNReal.ofReal_mul (by have := Real.exp_pos (-τ / β); positivity)]
  have hm : AEStronglyMeasurable (fun τ => (1 - Real.exp (-(τ * u))) * (Real.exp (-τ / β) / τ))
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Measurable fun τ : ℝ =>
      (1 - Real.exp (-(τ * u))) * (Real.exp (-τ / β) / τ)).aestronglyMeasurable
  have hae : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun τ => (1 - Real.exp (-(τ * u))) * (Real.exp (-τ / β) / τ) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn)
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hm hae).1
    (by rw [hlin]; exact ENNReal.ofReal_ne_top), ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hae hm, hlin,
    ENNReal.toReal_ofReal (Real.log_nonneg (by nlinarith [mul_nonneg hβ.le hu]))]

/-- **The density `m_{β,γ}(τ) = (e^{-τ/β} - e^{-τ/γ})/τ`** of the Lévy measure of `f_{β,γ}`. -/
noncomputable def incDensity (β γ τ : ℝ) : ℝ := (Real.exp (-τ / β) - Real.exp (-τ / γ)) / τ

theorem maternIncExponent_eq {β γ u : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hu : 0 ≤ u) :
    maternIncExponent β γ u = Real.log (1 + β * u) - Real.log (1 + γ * u) :=
  Real.log_div (by nlinarith [mul_nonneg hβ.le hu]) (by nlinarith [mul_nonneg hγ.le hu])

theorem incDensity_nonneg {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ incDensity β γ τ := by
  have hβ : 0 < β := hγ.trans hγβ
  refine div_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 ?_)) hτ.le
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hτ.le hγ hγβ.le

theorem continuousOn_incDensity (β γ : ℝ) : ContinuousOn (incDensity β γ) (Ioi 0) :=
  ((by fun_prop : Continuous fun τ : ℝ => Real.exp (-τ / β) - Real.exp (-τ / γ)).continuousOn.div
    continuousOn_id fun τ (hτ : 0 < τ) => hτ.ne')

/-- `∫(1 ∧ τ) m_{β,γ}(τ) dτ < ∞`, by `(1 ∧ τ) m_{β,γ}(τ) ≤ e^{-τ/β}`. -/
theorem lintegral_min_incDensity_ne_top {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) :
    ∫⁻ τ in Ioi (0 : ℝ), ENNReal.ofReal (min 1 τ * incDensity β γ τ) ≠ ⊤ := by
  have hβ : 0 < β := hγ.trans hγβ
  have hi : IntegrableOn (fun τ => Real.exp (-β⁻¹ * τ)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (inv_pos.2 hβ)
  refine ne_top_of_le_ne_top hi.lintegral_lt_top.ne ?_
  refine setLIntegral_mono' measurableSet_Ioi fun τ (hτ : 0 < τ) => ENNReal.ofReal_le_ofReal ?_
  have h0 := incDensity_nonneg hγ hγβ hτ
  calc min 1 τ * incDensity β γ τ ≤ τ * incDensity β γ τ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) h0
    _ = Real.exp (-τ / β) - Real.exp (-τ / γ) := by
        rw [incDensity]; field_simp
    _ ≤ Real.exp (-β⁻¹ * τ) := by
        have := Real.exp_pos (-τ / γ)
        rw [show -β⁻¹ * τ = -τ / β by ring]
        linarith

/-- The second integral form of (1), with the integrability of its integrand. -/
theorem maternIncExponent_eq_integral {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) {u : ℝ} (hu : 0 ≤ u) :
    maternIncExponent β γ u =
      ∫ τ in Ioi (0 : ℝ), (1 - Real.exp (-(τ * u))) * incDensity β γ τ := by
  have hβ : 0 < β := hγ.trans hγβ
  obtain ⟨hiβ, hβ'⟩ := frullani_integral hβ hu
  obtain ⟨hiγ, hγ'⟩ := frullani_integral hγ hu
  rw [maternIncExponent_eq hβ hγ hu, ← hβ', ← hγ', ← integral_sub hiβ hiγ]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  simp only [incDensity]
  ring

/-- `f_{β,γ}` as the lower integral `∫(1 - e^{-xτ}) m_{β,γ}(τ) dτ`, `x > 0`. -/
theorem ofReal_maternIncExponent {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (maternIncExponent β γ x) = ∫⁻ τ in Ioi (0 : ℝ),
      ENNReal.ofReal (incDensity β γ τ) * ENNReal.ofReal (1 - Real.exp (-(x * τ))) := by
  rw [← (ofReal_bernstein_integral (fun τ hτ => incDensity_nonneg hγ hγβ hτ)
    (continuousOn_incDensity β γ) (lintegral_min_incDensity_ne_top hγ hγβ) hx.le).2,
    maternIncExponent_eq_integral hγ hγβ hx.le]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  simp only [mul_comm τ x]

/-- The first integral form of (1). -/
theorem maternIncExponent_eq_intervalIntegral {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) {u : ℝ}
    (hu : 0 ≤ u) : maternIncExponent β γ u = ∫ x in (1 / β)..(1 / γ), u / (u + x) / x := by
  have hβ : 0 < β := hγ.trans hγβ
  have hle : 1 / β ≤ 1 / γ := one_div_le_one_div_of_le hγ hγβ.le
  have hpos : ∀ x ∈ uIcc (1 / β) (1 / γ), 0 < x := fun x hx => by
    rw [uIcc_of_le hle] at hx
    exact lt_of_lt_of_le (by positivity) hx.1
  have hderiv : ∀ x ∈ uIcc (1 / β) (1 / γ),
      HasDerivAt (fun x => Real.log x - Real.log (u + x)) (u / (u + x) / x) x := by
    intro x hx
    have hx0 := hpos x hx
    have hux : 0 < u + x := by linarith
    have h1 := Real.hasDerivAt_log hx0.ne'
    have h2 := ((hasDerivAt_id x).const_add u).log hux.ne'
    refine (h1.sub h2).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hcont : ContinuousOn (fun x => u / (u + x) / x) (uIcc (1 / β) (1 / γ)) := by
    refine ContinuousOn.div (continuousOn_const.div (continuousOn_const.add continuousOn_id)
      fun x hx => by have := hpos x hx; positivity) continuousOn_id fun x hx => (hpos x hx).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable),
    maternIncExponent_eq hβ hγ hu]
  have hval : ∀ θ : ℝ, 0 < θ →
      Real.log (1 / θ) - Real.log (u + 1 / θ) = -Real.log (1 + θ * u) := by
    intro θ hθ
    rw [← Real.log_div (by positivity) (by positivity), ← Real.log_inv]
    congr 1
    field_simp
    ring
  rw [hval γ hγ, hval β hβ]
  ring

/-- `f_{β,γ}` is differentiable at `x > 0` with derivative `(x + 1/β)⁻¹ - (x + 1/γ)⁻¹`. -/
theorem hasDerivAt_maternIncExponent {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (maternIncExponent β γ) ((x + 1 / β)⁻¹ - (x + 1 / γ)⁻¹) x := by
  have hβ : 0 < β := hγ.trans hγβ
  have heq : (fun y => Real.log (1 + β * y) - Real.log (1 + γ * y)) =ᶠ[𝓝 x]
      maternIncExponent β γ := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with y (hy : 0 < y)
    exact (maternIncExponent_eq hβ hγ hy.le).symm
  have h1 : HasDerivAt (fun y => 1 + β * y) β x := by
    simpa using ((hasDerivAt_id x).const_mul β).const_add 1
  have h2 : HasDerivAt (fun y => 1 + γ * y) γ x := by
    simpa using ((hasDerivAt_id x).const_mul γ).const_add 1
  have hb : 0 < 1 + β * x := by positivity
  have hg : 0 < 1 + γ * x := by positivity
  refine ((h1.log hb.ne').sub (h2.log hg.ne')).congr_of_eventuallyEq heq.symm |>.congr_deriv ?_
  field_simp
  ring

/-- **`prop:matern-increments`(1).** The two integral forms of `f_{β,γ}`; it is a bounded complete
Bernstein function and not a Thorin–Bernstein function. -/
theorem matern_increments_1 {β γ : ℝ} (hγ : 0 < γ) (hγβ : γ < β) :
    (∀ u : ℝ, 0 ≤ u → maternIncExponent β γ u = ∫ x in (1 / β)..(1 / γ), u / (u + x) / x) ∧
      (∀ u : ℝ, 0 ≤ u → maternIncExponent β γ u =
        ∫ τ in Ioi (0 : ℝ), (1 - Real.exp (-(τ * u))) *
          ((Real.exp (-τ / β) - Real.exp (-τ / γ)) / τ)) ∧
      IsCompleteBernstein (maternIncExponent β γ) ∧
      (∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → |maternIncExponent β γ u| ≤ M) ∧
      ¬ IsThorinBernstein (maternIncExponent β γ) := by
  have hβ : 0 < β := hγ.trans hγβ
  have hm0 : ∀ τ, 0 < τ → 0 ≤ incDensity β γ τ := fun τ hτ => incDensity_nonneg hγ hγβ hτ
  have hnn : ∀ u, 0 ≤ u → 0 ≤ maternIncExponent β γ u := fun u hu =>
    Real.log_nonneg ((one_le_div (by positivity)).2 (by nlinarith [mul_nonneg hβ.le hu]))
  -- the Bernstein function
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hder : EqOn (derivWithin (maternIncExponent β γ) (Ioi 0))
      (fun x => (x + 1 / β)⁻¹ - (x + 1 / γ)⁻¹) (Ioi 0) := fun x (hx : 0 < x) =>
    (hasDerivAt_maternIncExponent hγ hγβ hx).hasDerivWithinAt.derivWithin (hU x hx)
  have hbern : IsBernsteinFunction (maternIncExponent β γ) := by
    refine ⟨fun x hx => hnn x hx.le, fun x (hx : 0 < x) =>
      (hasDerivAt_maternIncExponent hγ hγβ hx).differentiableAt.differentiableWithinAt, ?_⟩
    have hh : 0 ≤ 1 / γ - 1 / β := sub_nonneg.2 (one_div_le_one_div_of_le hγ hγβ.le)
    refine (completelyMonotone_sub_shift (isCompletelyMonotone_inv_add
      (by positivity : (0 : ℝ) ≤ 1 / β)) hh).congr fun x hx => ?_
    rw [hder hx]
    simp only
    ring_nf
  -- the density is completely monotone
  have hcmd : IsCompletelyMonotone (incDensity β γ) := by
    refine (isCompletelyMonotone_expWindow (inv_pos.2 hβ) (inv_lt_inv₀ hβ hγ |>.2 hγβ)).congr
      fun τ _ => ?_
    simp only [incDensity]
    ring_nf
  refine ⟨fun u hu => maternIncExponent_eq_intervalIntegral hγ hγβ hu,
    fun u hu => maternIncExponent_eq_integral hγ hγβ hu, ⟨hbern, 0, 0, incDensity β γ, le_rfl,
      le_rfl, hcmd, lintegral_min_incDensity_ne_top hγ hγβ, fun x hx => ?_⟩,
    ⟨Real.log (β / γ), fun u hu => ?_⟩, fun hT => ?_⟩
  · rw [maternIncExponent_eq_integral hγ hγβ hx.le, zero_add, zero_mul, zero_add]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    simp only [mul_comm τ x]
  · rw [abs_of_nonneg (hnn u hu)]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ (by positivity) hγ]
    nlinarith [mul_nonneg hβ.le hu]
  · -- `t m(t) = e^{-t/β} - e^{-t/γ}` would be completely monotone, hence nonincreasing
    have hcm := hT.completelyMonotone_density hm0 (continuousOn_incDensity β γ)
      fun x hx => ofReal_maternIncExponent hγ hγβ hx
    have hanti := hcm.antitoneOn_iteratedDerivWithin 0
    simp only [pow_zero, one_mul, iteratedDerivWithin_zero] at hanti
    set g : ℝ → ℝ := fun t => Real.exp (-t / β) - Real.exp (-t / γ) with hg
    have hgm : ∀ t, 0 < t → t * incDensity β γ t = g t := fun t ht => by
      simp only [incDensity, hg]; field_simp
    have hg1 : 0 < g 1 := by
      simp only [hg]
      refine sub_pos.2 (Real.exp_lt_exp.2 ?_)
      rw [neg_div, neg_div, neg_lt_neg_iff]
      exact one_div_lt_one_div_of_lt hγ hγβ
    have hgle : ∀ t, 0 < t → g t ≤ t / γ := fun t ht => by
      simp only [hg]
      have h1 : Real.exp (-t / β) ≤ 1 := Real.exp_le_one_iff.2 (by
        have : 0 < t / β := by positivity
        rw [neg_div]; linarith)
      have h2 := Real.add_one_le_exp (-t / γ)
      have h3 : -t / γ = -(t / γ) := neg_div γ t
      linarith
    set t₁ := min (1 / 2) (γ * g 1 / 2) with ht₁
    have ht₁0 : 0 < t₁ := lt_min (by norm_num) (by positivity)
    have ht₁1 : t₁ ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have h := hanti (mem_Ioi.2 ht₁0) (mem_Ioi.2 one_pos) ht₁1
    simp only at h
    rw [hgm t₁ ht₁0, hgm 1 one_pos] at h
    have h3 : g t₁ ≤ g 1 / 2 := by
      refine (hgle t₁ ht₁0).trans ?_
      rw [div_le_iff₀ hγ]
      have := min_le_right (1 / 2 : ℝ) (γ * g 1 / 2)
      linarith
    linarith

end Pyramids
