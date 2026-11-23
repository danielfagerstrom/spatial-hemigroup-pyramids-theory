/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.BesselProfile
import Pyramids.Matern.BesselK
import Mathlib.Analysis.PSeries

/-!
# `prop:matern-generator-octave`(3): no central value

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:matern-generator-octave`. Phase 5, wave 3b.
`matern_generator_octave_3`, `_3_plane`, `_3_high` and `_3_periodization` moved here from
`PyramidsSkeleton.Ch04Matern`, their conclusions unchanged.

* **The density tends to `+∞`.** On `‖x‖² < s ≤ 1` the integrand of `G` is at least
  `K/s`, `K = e^{-1}(4π)^{-d/2}e^{-1/4}` (here `d ≥ 2` gives `s^{-d/2} ≥ s^{-1}`), so
  `G(x) ≥ 2K log(1/‖x‖)` for `0 < ‖x‖ < 1`. The integrand decreases in `‖x‖`, so `G(0) ≥ G(x)`
  for every `x`, and `G(0) = ∞`. The print's monotone convergence is replaced by this bound.
* **`d = 2`.** `G(x) = (4π)^{-1} ∫ s^{-1}e^{-s-|x|²/(4s)} ds = (2π)^{-1}K₀(|x|)`
  (`lem:bessel-k`(1) at `ν = 0`), and `K₀(y) - log(1/y)` is bounded near `0` (`lem:bessel-k`(3)).
  A difference bounded while the comparison function tends to `∞` is negligible.
* **`d ≥ 3`.** The substitution `s = |x|²v` gives
  `G(x) = |x|^{2-d} ∫ e^{-|x|²v} (4πv)^{-d/2} e^{-1/(4v)} dv`; dominated convergence (the bound
  `(4πv)^{-d/2}e^{-1/(4v)}` is integrable for `d ≥ 3`) sends the integral to its value at `0`, and
  `v = 1/w` turns it into `(4π)^{-d/2}∫ w^{d/2-2}e^{-w/4} dw = Γ(d/2 - 1)/(4π^{d/2})`.
* **The periodization.** For `n ≠ 0`, `|ω + 2πn/h|² ≤ 2|ω|² + 2(2π/h)²|n|²`, so the terms are at
  least `κ/(1 + |n|²)`. On the plane `n = (a, b, 0, …)`, `a, b ∈ ℕ`, the row `a` sums to at least
  `(a + 1)/(1 + 2a²) ≥ 1/(2(a + 1))`, and the harmonic series diverges. The print's dyadic shells
  are replaced by rows.

Dropped binders (2026-11-15, a strengthening): `_3_periodization` takes no `r > 0` and no
`h > 0`; the others read all theirs.

**What it reaches.** Lean core. The `d = 2` asymptotic reads `lem:bessel-k`, whose entry A51 is a
theorem.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter Asymptotics
open ScaleSpace (besselK)
open scoped Topology ENNReal

variable {d : ℕ}

/-! ## A comparison lemma -/

/-- **A bounded difference is negligible** against a function tending to `∞`. -/
theorem isEquivalent_of_bdd_sub {α : Type*} {l : Filter α} {u v : α → ℝ}
    (hb : ∃ C, ∀ᶠ x in l, |u x - v x| ≤ C) (hv : Tendsto v l atTop) : u ~[l] v := by
  obtain ⟨C, hC⟩ := hb
  have h1 : (u - v) =O[l] (fun _ => (1 : ℝ)) :=
    IsBigO.of_bound C (hC.mono fun x hx => by simpa using hx)
  have h2 : (fun _ => (1 : ℝ)) =o[l] v :=
    (isLittleO_one_left_iff ℝ).2 (tendsto_norm_atTop_atTop.comp hv)
  exact h1.trans_isLittleO h2

/-! ## The density at the origin -/

/-- The integrand of `G`, as a function of `s`. -/
theorem maternGreen_integrand_lower (hd : 2 ≤ d) {x : Rd d} {s : ℝ} (hs : ‖x‖ ^ 2 < s)
    (hs1 : s ≤ 1) :
    Real.exp (-1) * ((4 * Real.pi) ^ (-(d : ℝ) / 2) * s⁻¹) * Real.exp (-(1 / 4)) ≤
      Real.exp (-s) * (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / (4 * s)) := by
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.mul_rpow (by positivity) hs0.le]
  gcongr
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hs0 hs1 (by linarith)
  · rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
    linarith

/-- The constant `K = e^{-1}(4π)^{-d/2}e^{-1/4}`. -/
noncomputable def greenLowerConst (d : ℕ) : ℝ :=
  Real.exp (-1) * (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / 4))

theorem greenLowerConst_pos (d : ℕ) : 0 < greenLowerConst d := by
  rw [greenLowerConst]; positivity

/-- **`G(x) ≥ 2K log(1/‖x‖)`** for `0 < ‖x‖ < 1`, `d ≥ 2`. -/
theorem maternGreenE_lower (hd : 2 ≤ d) {x : Rd d} (hx0 : 0 < ‖x‖) (hx1 : ‖x‖ < 1) :
    ENNReal.ofReal (2 * greenLowerConst d * -Real.log ‖x‖) ≤ maternGreenE d x := by
  set a : ℝ := ‖x‖ ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := by rw [ha]; nlinarith
  set K := greenLowerConst d with hK
  have hsub : Ioc a 1 ⊆ Ioi 0 := fun s hs => lt_trans ha0 hs.1
  have hint : IntegrableOn (fun s : ℝ => K * s⁻¹) (Ioc a 1) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.mul (continuousOn_inv₀.mono fun s hs => (lt_of_lt_of_le ha0 hs.1).ne')
  have hval : ∫ s in Ioc a 1, K * s⁻¹ = 2 * K * -Real.log ‖x‖ := by
    rw [← intervalIntegral.integral_of_le ha1.le, intervalIntegral.integral_const_mul,
      integral_inv_of_pos ha0 one_pos, one_div, Real.log_inv, ha, Real.log_pow]
    push_cast
    ring
  calc ENNReal.ofReal (2 * K * -Real.log ‖x‖)
      = ∫⁻ s in Ioc a 1, ENNReal.ofReal (K * s⁻¹) := by
        rw [← hval, ofReal_integral_eq_lintegral_ofReal hint]
        exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => by
          have : 0 < s := lt_trans ha0 hs.1
          have := greenLowerConst_pos d
          positivity)
    _ ≤ ∫⁻ s in Ioc a 1, ENNReal.ofReal (Real.exp (-s) * (4 * Real.pi * s) ^ (-(d : ℝ) / 2) *
          Real.exp (-(‖x‖ ^ 2) / (4 * s))) := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs => ENNReal.ofReal_le_ofReal ?_
        refine le_trans (le_of_eq ?_) (maternGreen_integrand_lower hd hs.1 hs.2)
        rw [hK, greenLowerConst]
        ring
    _ ≤ maternGreenE d x := lintegral_mono_set hsub

/-- `G(x) ≤ G(0)`: the integrand decreases in `‖x‖`. -/
theorem maternGreenE_le_zero (x : Rd d) : maternGreenE d x ≤ maternGreenE d 0 := by
  refine setLIntegral_mono' measurableSet_Ioi fun s (hs : 0 < s) => ENNReal.ofReal_le_ofReal ?_
  have h : Real.exp (-(‖x‖ ^ 2) / (4 * s)) ≤ Real.exp (-(‖(0 : Rd d)‖ ^ 2) / (4 * s)) := by
    rw [Real.exp_le_exp, norm_zero]
    have : 0 ≤ ‖x‖ ^ 2 / (4 * s) := by positivity
    rw [neg_div, neg_div]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero]
    linarith
  gcongr

/-- **`G → ∞` at the origin**, `d ≥ 2`. -/
theorem tendsto_maternGreenE (hd : 2 ≤ d) :
    Tendsto (maternGreenE d) (𝓝[≠] (0 : Rd d)) (𝓝 ⊤) := by
  have hn := tendsto_norm_nhdsNE_zero (E := Rd d)
  have hK := greenLowerConst_pos d
  have hlog : Tendsto (fun x : Rd d => 2 * greenLowerConst d * -Real.log ‖x‖) (𝓝[≠] 0) atTop :=
    ((tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hn)).const_mul_atTop
      (by positivity))
  refine tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp hlog) ?_
  have hev : ∀ᶠ x : Rd d in 𝓝[≠] 0, ‖x‖ ∈ Ioo 0 1 :=
    hn.eventually (Ioo_mem_nhdsGT one_pos)
  exact hev.mono fun x hx => maternGreenE_lower hd hx.1 hx.2

/-- `G(0) = ∞`, `d ≥ 2`. -/
theorem maternGreenE_zero (hd : 2 ≤ d) : maternGreenE d 0 = ⊤ := by
  haveI : NeZero d := ⟨by omega⟩
  exact top_le_iff.1 (le_of_tendsto' (tendsto_maternGreenE hd) maternGreenE_le_zero)

/-- **`prop:matern-generator-octave`(3), no central value.** For `d ≥ 2` the density `r^{-d}G(x/r)`
of `L_r` is `+∞` at the origin and tends to `+∞` there. -/
theorem matern_generator_octave_3 (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) :
    maternDensityE d r 0 = ⊤ ∧ Tendsto (maternDensityE d r) (𝓝[≠] 0) (𝓝 ⊤) := by
  have hc : ENNReal.ofReal (r ^ (-(d : ℝ))) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  refine ⟨?_, ?_⟩
  · rw [maternDensityE, smul_zero, maternGreenE_zero hd, ENNReal.mul_top hc]
  · have hs : Tendsto (fun x : Rd d => r⁻¹ • x) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_const_smul r⁻¹).tendsto' 0 0 (smul_zero _)).mono_left
          nhdsWithin_le_nhds
      · exact eventually_mem_nhdsWithin.mono fun x (hx : x ≠ 0) =>
          smul_ne_zero (inv_ne_zero hr.ne') hx
    have h := ENNReal.Tendsto.const_mul ((tendsto_maternGreenE hd).comp hs)
      (Or.inl ENNReal.top_ne_zero) (a := ENNReal.ofReal (r ^ (-(d : ℝ))))
    rw [ENNReal.mul_top hc] at h
    exact h

/-! ## The asymptotics -/

/-- The real value of the density off the origin: `r^{-d} G(x/r)`. -/
theorem maternDensityE_toReal {r : ℝ} (hr : 0 < r) {x : Rd d} (hx : x ≠ 0) :
    (maternDensityE d r x).toReal = r ^ (-(d : ℝ)) * maternGreen d (r⁻¹ • x) := by
  have hx' : r⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero hr.ne') hx
  have hG : 0 ≤ maternGreen d (r⁻¹ • x) :=
    setIntegral_nonneg measurableSet_Ioi fun s (hs : 0 < s) => by positivity
  rw [maternDensityE, maternGreenE_eq_ofReal hx', ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal (by positivity)]

/-- `‖r⁻¹ x‖ = ‖x‖/r`. -/
theorem norm_inv_smul {r : ℝ} (hr : 0 < r) (x : Rd d) : ‖r⁻¹ • x‖ = ‖x‖ / r := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_mul_eq_div]

/-- **`d = 2`: `G(y) = (2π)⁻¹ K₀(|y|)`** for `y ≠ 0`. -/
theorem maternGreen_two {y : Rd 2} (hy : y ≠ 0) :
    maternGreen 2 y = (2 * Real.pi)⁻¹ * besselK 0 ‖y‖ := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h := (bessel_k_1 0 hy0).2
  simp only [Real.rpow_zero, mul_one] at h
  have hcongr : ∀ s ∈ Ioi (0 : ℝ), Real.exp (-s) * ((4 * Real.pi * s) ^ (-((2 : ℕ) : ℝ) / 2) *
      Real.exp (-(‖y‖ ^ 2) / (4 * s))) =
      (4 * Real.pi)⁻¹ * (s ^ ((0 : ℝ) - 1) * Real.exp (-s - ‖y‖ ^ 2 / (4 * s))) := by
    intro s hs
    have hs0 : 0 < s := hs
    rw [show (-((2 : ℕ) : ℝ) / 2) = -1 by norm_num, zero_sub, Real.rpow_neg_one,
      Real.rpow_neg_one, sub_eq_add_neg, Real.exp_add, neg_div]
    field_simp
  rw [maternGreen, setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul, h]
  field_simp
  ring

/-- `‖x‖/r → 0⁺` along `x → 0`, `x ≠ 0`. -/
theorem tendsto_norm_div {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : Rd d => ‖x‖ / r) (𝓝[≠] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun x : Rd d => ‖x‖ / r) (𝓝 0) (𝓝 (‖(0 : Rd d)‖ / r)) :=
      (continuous_norm.div_const r).tendsto 0
    rw [norm_zero, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  · exact eventually_mem_nhdsWithin.mono fun x (hx : x ≠ 0) =>
      div_pos (norm_pos_iff.2 hx) hr

/-- **`prop:matern-generator-octave`(3), `d = 2`.** The density is asymptotic to
`(2πr²)⁻¹ log(1/|x|)` at the origin. -/
theorem matern_generator_octave_3_plane {r : ℝ} (hr : 0 < r) :
    Asymptotics.IsEquivalent (𝓝[≠] (0 : Rd 2)) (fun x => (maternDensityE 2 r x).toReal)
      (fun x => (2 * Real.pi * r ^ 2)⁻¹ * Real.log (1 / ‖x‖)) := by
  obtain ⟨C, hC⟩ := (bessel_k_3).2
  have hev := (tendsto_norm_div (d := 2) hr).eventually hC
  refine isEquivalent_of_bdd_sub ⟨(2 * Real.pi * r ^ 2)⁻¹ * (C + |Real.log r|), ?_⟩ ?_
  · filter_upwards [hev, eventually_mem_nhdsWithin] with x hx (hx0 : x ≠ 0)
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    rw [maternDensityE_toReal hr hx0, maternGreen_two (smul_ne_zero (inv_ne_zero hr.ne') hx0),
      norm_inv_smul hr]
    have hr2 : r ^ (-((2 : ℕ) : ℝ)) = (r ^ 2)⁻¹ := by
      rw [show (-((2 : ℕ) : ℝ)) = -(2 : ℕ) by norm_num, Real.rpow_neg hr.le, Real.rpow_natCast]
    have hlog : Real.log (1 / ‖x‖) = Real.log (1 / (‖x‖ / r)) - Real.log r := by
      rw [one_div_div, Real.log_div hr.ne' hn.ne', one_div, Real.log_inv]
      ring
    have heq : r ^ (-((2 : ℕ) : ℝ)) * ((2 * Real.pi)⁻¹ * besselK 0 (‖x‖ / r)) -
        (2 * Real.pi * r ^ 2)⁻¹ * Real.log (1 / ‖x‖) =
        (2 * Real.pi * r ^ 2)⁻¹ * ((besselK 0 (‖x‖ / r) - Real.log (1 / (‖x‖ / r))) +
          Real.log r) := by
      rw [hr2, hlog, mul_inv]
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity)]
    gcongr
    exact (abs_add_le _ _).trans (by gcongr)
  · have hn := tendsto_norm_nhdsNE_zero (E := Rd 2)
    have h : Tendsto (fun x : Rd 2 => -Real.log ‖x‖) (𝓝[≠] 0) atTop :=
      tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hn)
    refine (h.const_mul_atTop (by positivity : (0 : ℝ) < (2 * Real.pi * r ^ 2)⁻¹)).congr ?_
    intro x
    rw [one_div, Real.log_inv]

/-! ## `d ≥ 3` -/

/-- The integrand `(4πv)^{-d/2}e^{-1/(4v)}` of the Newtonian constant. -/
noncomputable def newtonH (d : ℕ) (v : ℝ) : ℝ :=
  (4 * Real.pi * v) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (4 * v)))

theorem newtonH_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ newtonH d v := by
  rw [newtonH]; positivity

/-- **`G(y) = |y|^{2-d} ∫ e^{-|y|²v} (4πv)^{-d/2}e^{-1/(4v)} dv`**, the substitution `s = |y|²v`. -/
theorem maternGreen_scaled {y : Rd d} (hy : y ≠ 0) :
    maternGreen d y = ‖y‖ ^ (2 - (d : ℝ)) *
      ∫ v in Ioi (0 : ℝ), Real.exp (-(‖y‖ ^ 2 * v)) * newtonH d v := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  set b : ℝ := ‖y‖ ^ 2 with hb
  have hb0 : 0 < b := by positivity
  set g : ℝ → ℝ := fun s => Real.exp (-s) * ((4 * Real.pi * s) ^ (-(d : ℝ) / 2) *
    Real.exp (-(‖y‖ ^ 2) / (4 * s))) with hg
  have h := integral_comp_mul_left_Ioi g 0 hb0
  rw [mul_zero, smul_eq_mul] at h
  have hG : maternGreen d y = b * ∫ v in Ioi (0 : ℝ), g (b * v) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hb0.ne', one_mul]
    rfl
  have hcongr : ∀ v ∈ Ioi (0 : ℝ), g (b * v) =
      b ^ (-(d : ℝ) / 2) * (Real.exp (-(‖y‖ ^ 2 * v)) * newtonH d v) := by
    intro v (hv : 0 < v)
    simp only [hg, newtonH]
    rw [show 4 * Real.pi * (b * v) = b * (4 * Real.pi * v) by ring,
      Real.mul_rpow hb0.le (by positivity),
      show -(‖y‖ ^ 2) / (4 * (b * v)) = -(1 / (4 * v)) by rw [hb]; field_simp]
    ring
  rw [hG, setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul, ← mul_assoc]
  congr 1
  rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_add hy0]
  congr 1
  push_cast
  ring

/-- `v = 1/x`: `x^{-2} newtonH(1/x) = (4π)^{-d/2} x^{d/2-2} e^{-x/4}`. -/
theorem newtonH_inv {x : ℝ} (hx : 0 < x) :
    (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • newtonH d (x ^ (-1 : ℝ)) =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) *
        (x ^ ((d : ℝ) / 2 - 2) * Real.exp (-(1 / 4) * x ^ (1 : ℝ))) := by
  rw [newtonH, smul_eq_mul, abs_neg, abs_one, one_mul,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le,
    Real.rpow_one, show 1 / (4 * x ^ (-1 : ℝ)) = 1 / 4 * x by
      rw [Real.rpow_neg_one]; field_simp]
  have e : x ^ ((-1 : ℝ) - 1) * x ^ ((-1 : ℝ) * (-(d : ℝ) / 2)) = x ^ ((d : ℝ) / 2 - 2) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [← e, neg_mul]
  ring_nf

/-- `(4πv)^{-d/2}e^{-1/(4v)}` is integrable on `(0,∞)` for `d ≥ 3`. -/
theorem integrableOn_newtonH (hd : 3 ≤ d) : IntegrableOn (newtonH d) (Ioi 0) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  refine (integrableOn_Ioi_comp_rpow_iff (newtonH d) (p := -1) (by norm_num)).1 ?_
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (d : ℝ) / 2 - 2) (p := 1)
    (b := 1 / 4) (by linarith) le_rfl (by norm_num)).const_mul ((4 * Real.pi) ^ (-(d : ℝ) / 2))
  exact IntegrableOn.congr_fun h (fun x (hx : 0 < x) => (newtonH_inv hx).symm) measurableSet_Ioi

/-- **`∫ (4πv)^{-d/2}e^{-1/(4v)} dv = Γ(d/2 - 1)/(4π^{d/2})`**, `d ≥ 3`. -/
theorem integral_newtonH (hd : 3 ≤ d) :
    ∫ v in Ioi (0 : ℝ), newtonH d v =
      Real.Gamma ((d : ℝ) / 2 - 1) / (4 * Real.pi ^ ((d : ℝ) / 2)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  rw [← integral_comp_rpow_Ioi (newtonH d) (p := -1) (by norm_num),
    setIntegral_congr_fun measurableSet_Ioi (fun x (hx : 0 < x) => newtonH_inv hx),
    integral_const_mul]
  have hc : ∀ x ∈ Ioi (0 : ℝ), x ^ ((d : ℝ) / 2 - 2) * Real.exp (-(1 / 4) * x ^ (1 : ℝ)) =
      x ^ (((d : ℝ) / 2 - 1) - 1) * Real.exp (-(1 / 4 * x)) := by
    intro x _
    rw [Real.rpow_one, neg_mul]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hc,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by norm_num)]
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [Real.mul_rpow (by norm_num) hπ.le, one_div_one_div]
  have h4 : (4 : ℝ) ^ (-(d : ℝ) / 2) * (4 : ℝ) ^ ((d : ℝ) / 2 - 1) = 4⁻¹ := by
    rw [← Real.rpow_add (by norm_num), show -(d : ℝ) / 2 + ((d : ℝ) / 2 - 1) = -1 by ring,
      Real.rpow_neg_one]
  have hp : 0 < Real.pi ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hπ _
  have hπr : Real.pi ^ (-(d : ℝ) / 2) = (Real.pi ^ ((d : ℝ) / 2))⁻¹ := by
    rw [neg_div, Real.rpow_neg hπ.le]
  rw [hπr]
  calc (4 : ℝ) ^ (-(d : ℝ) / 2) * (Real.pi ^ ((d : ℝ) / 2))⁻¹ *
        ((4 : ℝ) ^ ((d : ℝ) / 2 - 1) * Real.Gamma ((d : ℝ) / 2 - 1))
      = ((4 : ℝ) ^ (-(d : ℝ) / 2) * (4 : ℝ) ^ ((d : ℝ) / 2 - 1)) *
          Real.Gamma ((d : ℝ) / 2 - 1) / Real.pi ^ ((d : ℝ) / 2) := by
        ring
    _ = _ := by
        rw [h4]
        field_simp

/-- **Dominated convergence**: `∫ e^{-bv} newtonH(v) dv → ∫ newtonH` as `b ↓ 0`. -/
theorem tendsto_integral_newtonH (hd : 3 ≤ d) :
    Tendsto (fun b : ℝ => ∫ v in Ioi (0 : ℝ), Real.exp (-(b * v)) * newtonH d v) (𝓝[≥] 0)
      (𝓝 (∫ v in Ioi (0 : ℝ), newtonH d v)) := by
  have hlim : (∫ v in Ioi (0 : ℝ), newtonH d v) =
      ∫ v in Ioi (0 : ℝ), Real.exp (-(0 * v)) * newtonH d v := by
    simp
  rw [hlim]
  refine tendsto_integral_filter_of_dominated_convergence (newtonH d) ?_ ?_
    (integrableOn_newtonH hd) ?_
  · refine Eventually.of_forall fun b => Measurable.aestronglyMeasurable ?_
    unfold newtonH
    fun_prop
  · filter_upwards [self_mem_nhdsWithin] with b (hb : 0 ≤ b)
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : 0 < v) => ?_)
    have hH := newtonH_nonneg (d := d) hv
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : Real.exp (-(b * v)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  · refine Eventually.of_forall fun v => ?_
    refine (Continuous.tendsto ?_ 0).mono_left nhdsWithin_le_nhds
    fun_prop

/-- **`prop:matern-generator-octave`(3), `d ≥ 3`.** The density is asymptotic to
`N_d r^{-2} |x|^{2-d}`, `N_d = Γ(d/2 - 1)/(4π^{d/2})`. -/
theorem matern_generator_octave_3_high (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) :
    Asymptotics.IsEquivalent (𝓝[≠] (0 : Rd d)) (fun x => (maternDensityE d r x).toReal)
      (fun x => Real.Gamma ((d : ℝ) / 2 - 1) / (4 * Real.pi ^ ((d : ℝ) / 2)) * (r ^ 2)⁻¹ *
        ‖x‖ ^ (2 - (d : ℝ))) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set N : ℝ := Real.Gamma ((d : ℝ) / 2 - 1) / (4 * Real.pi ^ ((d : ℝ) / 2)) with hN
  have hN0 : 0 < N := by
    rw [hN]
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < (d : ℝ) / 2 - 1 by linarith)
    have := Real.rpow_pos_of_pos Real.pi_pos ((d : ℝ) / 2)
    positivity
  set F : ℝ → ℝ := fun b => ∫ v in Ioi (0 : ℝ), Real.exp (-(b * v)) * newtonH d v with hF
  have hFt : Tendsto F (𝓝[≥] 0) (𝓝 N) := by
    rw [hN, ← integral_newtonH hd]
    exact tendsto_integral_newtonH hd
  have hsq : Tendsto (fun x : Rd d => ‖r⁻¹ • x‖ ^ 2) (𝓝[≠] 0) (𝓝[≥] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun x => mem_Ici.2 (sq_nonneg _)⟩
    have h : Tendsto (fun x : Rd d => ‖r⁻¹ • x‖ ^ 2) (𝓝 0) (𝓝 (‖r⁻¹ • (0 : Rd d)‖ ^ 2)) :=
      (by fun_prop : Continuous fun x : Rd d => ‖r⁻¹ • x‖ ^ 2).tendsto 0
    rw [smul_zero, norm_zero] at h
    simpa using h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun x : Rd d => F (‖r⁻¹ • x‖ ^ 2) / N) (𝓝[≠] 0) (𝓝 1) := by
    have := (hFt.comp hsq).div_const N
    rwa [div_self hN0.ne'] at this
  refine isEquivalent_of_tendsto_one (hlim.congr' ?_)
  filter_upwards [eventually_mem_nhdsWithin] with x (hx : x ≠ 0)
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hx' : r⁻¹ • x ≠ 0 := smul_ne_zero (inv_ne_zero hr.ne') hx
  simp only [Pi.div_apply]
  rw [maternDensityE_toReal hr hx, maternGreen_scaled hx', norm_inv_smul hr]
  have hpow : r ^ (-(d : ℝ)) * (‖x‖ / r) ^ (2 - (d : ℝ)) = (r ^ 2)⁻¹ * ‖x‖ ^ (2 - (d : ℝ)) := by
    rw [Real.div_rpow hx0.le hr.le, mul_div_assoc', mul_comm, mul_div_assoc,
      ← Real.rpow_sub hr, show -(d : ℝ) - (2 - (d : ℝ)) = -(2 : ℕ) by push_cast; ring,
      Real.rpow_neg hr.le, Real.rpow_natCast]
    ring
  have hxp : 0 < ‖x‖ ^ (2 - (d : ℝ)) := Real.rpow_pos_of_pos hx0 _
  rw [← mul_assoc, hpow]
  simp only [hF]
  field_simp

/-! ## The periodization -/

/-- `(u + v)² ≤ 2u² + 2v²`. -/
theorem add_sq_le_two (u v : ℝ) : (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
  nlinarith [sq_nonneg (u - v)]

/-- **`prop:matern-generator-octave`(3), the periodization** `∑_{n ∈ ℤ^d} (1 + r²|ω + 2πn/h|²)⁻¹`
diverges, `d ≥ 2`. No `r > 0` and no `h > 0` (2026-11-15, a strengthening). -/
theorem matern_generator_octave_3_periodization (hd : 2 ≤ d) {r h : ℝ} (ω : Rd d) :
    ¬ Summable fun n : Zd d =>
      (1 + r ^ 2 * ∑ i, (ω i + 2 * Real.pi * (n i : ℝ) / h) ^ 2)⁻¹ := by
  intro hs
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  set emb : ℕ × ℕ → Zd d := fun p k => if k = i0 then (p.1 : ℤ) else if k = i1 then (p.2 : ℤ)
    else 0 with hemb
  have hinj : Function.Injective emb := by
    intro p p' hp
    have h0 := congrFun hp i0
    have h1 := congrFun hp i1
    simp only [hemb, if_pos rfl, if_neg h01.symm] at h0 h1
    exact Prod.ext (by exact_mod_cast h0) (by exact_mod_cast h1)
  set f : Zd d → ℝ := fun n => (1 + r ^ 2 * ∑ i, (ω i + 2 * Real.pi * (n i : ℝ) / h) ^ 2)⁻¹
    with hf
  have hfs : Summable (f ∘ emb) := hs.comp_injective hinj
  set A : ℝ := ∑ i, ω i ^ 2 with hA
  set B : ℝ := (2 * Real.pi / h) ^ 2 with hB
  set L : ℝ := 1 + 2 * r ^ 2 * A + 2 * r ^ 2 * B with hL
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hL0 : 0 < L := by positivity
  -- the squares of the embedded index
  have hnsq : ∀ p : ℕ × ℕ, ∑ k, ((emb p k : ℤ) : ℝ) ^ 2 = (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    intro p
    have hk : ∀ k, ((emb p k : ℤ) : ℝ) ^ 2 =
        (if k = i0 then (p.1 : ℝ) ^ 2 else 0) + (if k = i1 then (p.2 : ℝ) ^ 2 else 0) := by
      intro k
      simp only [hemb]
      by_cases ha : k = i0
      · subst ha
        simp [h01]
      · by_cases hb : k = i1
        · subst hb
          simp [ha]
        · simp [ha, hb]
    simp_rw [hk]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i0,
      Finset.sum_ite_eq' Finset.univ i1]
    simp
  -- the lower bound `f(emb p) ≥ L⁻¹ (1 + a² + b²)⁻¹`
  have hlow : ∀ p : ℕ × ℕ, (1 + (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)⁻¹ ≤ L * f (emb p) := by
    intro p
    have hS : ∑ i, (ω i + 2 * Real.pi * ((emb p i : ℤ) : ℝ) / h) ^ 2 ≤
        2 * A + 2 * B * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) := by
      rw [← hnsq p, hA, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := add_sq_le_two (ω i) (2 * Real.pi * ((emb p i : ℤ) : ℝ) / h)
      rw [hB]
      calc (ω i + 2 * Real.pi * ((emb p i : ℤ) : ℝ) / h) ^ 2
          ≤ 2 * ω i ^ 2 + 2 * (2 * Real.pi * ((emb p i : ℤ) : ℝ) / h) ^ 2 := this
        _ = 2 * ω i ^ 2 + 2 * (2 * Real.pi / h) ^ 2 * ((emb p i : ℤ) : ℝ) ^ 2 := by ring
    have hD : 0 < 1 + r ^ 2 * ∑ i, (ω i + 2 * Real.pi * ((emb p i : ℤ) : ℝ) / h) ^ 2 := by
      positivity
    have hE : 0 < 1 + (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by positivity
    simp only [hf]
    rw [← div_eq_mul_inv, inv_le_comm₀ hE (by positivity), inv_div, div_le_iff₀ hL0]
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    have hB0 : 0 ≤ B := sq_nonneg _
    have hab : 0 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hS hr2
    rw [hL]
    nlinarith [mul_nonneg hr2 hA0, mul_nonneg (mul_nonneg hr2 hB0) hab]
  set g : ℕ × ℕ → ℝ := fun p => (1 + (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)⁻¹ with hg
  have hg0 : 0 ≤ g := fun p => by simp only [hg]; positivity
  have hgs : Summable g :=
    Summable.of_nonneg_of_le hg0 hlow (hfs.mul_left L)
  have hrow := ((summable_prod_of_nonneg hg0).1 hgs).2
  have hrow1 := ((summable_prod_of_nonneg hg0).1 hgs).1
  -- each row is at least `1/(2(a + 1))`
  have hrowlow : ∀ a : ℕ, (1 / 2 : ℝ) * (1 / ((a : ℝ) + 1)) ≤ ∑' b, g (a, b) := by
    intro a
    have hle : ∀ b ∈ Finset.range (a + 1), (1 + 2 * (a : ℝ) ^ 2)⁻¹ ≤ g (a, b) := by
      intro b hb
      have hb' : (b : ℝ) ≤ a := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      simp only [hg]
      refine inv_anti₀ (by positivity) ?_
      have : (b : ℝ) ^ 2 ≤ (a : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hb' 2
      linarith
    calc (1 / 2 : ℝ) * (1 / ((a : ℝ) + 1)) ≤ ((a : ℝ) + 1) * (1 + 2 * (a : ℝ) ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          field_simp
          have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
          nlinarith
      _ = ∑ b ∈ Finset.range (a + 1), (1 + 2 * (a : ℝ) ^ 2)⁻¹ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ∑ b ∈ Finset.range (a + 1), g (a, b) := Finset.sum_le_sum hle
      _ ≤ ∑' b, g (a, b) := (hrow1 a).sum_le_tsum _ fun b _ => hg0 _
  have hharm : Summable fun a : ℕ => 1 / ((a : ℝ) + 1) := by
    refine (Summable.of_nonneg_of_le (fun a => by positivity) hrowlow hrow).mul_left 2 |>.congr ?_
    intro a
    ring
  refine Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 ?_)
  refine hharm.congr fun a => ?_
  push_cast
  ring

end Pyramids
