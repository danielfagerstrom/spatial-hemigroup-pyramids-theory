/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Matern
import Pyramids.Cited.A51
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# `lem:bessel-k`: the profile through Bessel functions

Blueprint: `blueprint/src/parts/04-matern.tex`, `lem:bessel-k`, chapter 4. Wave 2b: the four
declarations moved here from `PyramidsSkeleton.Ch04Matern`, their statements unchanged.

`K_ν` is the shared core's `ScaleSpace.besselK`, `K_ν(z) = ∫₀^∞ e^{-z cosh u} cosh(νu) du`
(DLMF 10.32.9, its definition).

## The route

* **(1).** `thm:cited-A51`, `cited_A51_integral`, at the order `-ν`: with `K_{-ν} = K_ν`
  (`ScaleSpace.besselK_neg`) it is the identity itself, the variable being `t = v`. The integral
  converges: its value in `[0,∞]` is finite by the shared core's substitution `u = c e^w`
  (`ScaleSpace.lintegral_Ioi_rpow_exp_besselKernel`), which turns it into the cosh integral, finite
  by `lintegral_cosh_exp_ne_top`. No cited fact beyond the proved clause (1) of A51 is read.
* **(2), another route than the printed one.** Differentiation under the integral sign in the
  definition: `∂_z e^{-z cosh u} = -cosh u e^{-z cosh u}`, dominated for `z > y/2` by
  `cosh u e^{-(y/2) cosh u}`, whose integral is `K_1(y/2)`; so `K₀' = -K₁`. For `y ≥ 1`,
  `y cosh u ≥ (y - 1) + cosh u` gives `K₀(y) ≤ e^{1-y} K₀(1) → 0`.
* **(3), the integral: the printed substitution `s = cosh u`**, by the one-dimensional change of
  variables with `|sinh u| (cosh² u - 1)^{-1/2} = 1`.
* **(3), the origin, another route than the printed one.** In `K₀(y) = ∫₀^∞ e^{-y cosh u} du`, with
  `L = log(1/y)` for `0 < y < 1`: on `(0, L]` the integrand lies between `1 - y e^u` and `1`, and on
  `(L, ∞)` it is at most `e^{-(u-L)/2}` since `y cosh u ≥ e^{u-L}/2 ≥ (u - L)/2`. So
  `L - 1 ≤ K₀(y) ≤ L + 2`.
-/

namespace Pyramids

open MeasureTheory Set Filter
open ScaleSpace (besselK)
open scoped Topology ENNReal

/-- The integrand of `K_p(z)`, `z > 0`, is integrable on `(0,∞)`. -/
theorem integrableOn_besselK (p : ℝ) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => Real.exp (-(z * Real.cosh u)) * Real.cosh (p * u)) (Ioi 0) := by
  refine ⟨(Continuous.aestronglyMeasurable (by fun_prop)), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun u => by positivity)]
  have h := lintegral_cosh_exp_ne_top p hz
  simp_rw [mul_comm (Real.exp _)]
  exact lt_top_iff_ne_top.2 h

/-! ## `lem:bessel-k` -/

/-- **`lem:bessel-k`(1).** For real `ν` and `y > 0`, the integral converges and
`∫₀^∞ v^{ν-1} e^{-v - y²/(4v)} dv = 2(y/2)^ν K_ν(y)`. -/
theorem bessel_k_1 (ν : ℝ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun v : ℝ => v ^ (ν - 1) * Real.exp (-v - y ^ 2 / (4 * v))) (Ioi 0) ∧
      ∫ v in Ioi (0 : ℝ), v ^ (ν - 1) * Real.exp (-v - y ^ 2 / (4 * v)) =
        2 * (y / 2) ^ ν * besselK ν y := by
  have hy2 : (0 : ℝ) < y / 2 := by positivity
  have hA : (0 : ℝ) < y ^ 2 / 4 := by positivity
  -- convergence, by the shared core's substitution
  have hsub := ScaleSpace.lintegral_Ioi_rpow_exp_besselKernel (p := ν) hA one_pos
  have hfin : (∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (u ^ (ν - 1) * Real.exp (-(y ^ 2 / 4 / u + 1 * u)))) ≠ ⊤ := by
    rw [hsub]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (by simp) ?_)
    exact lintegral_cosh_exp_ne_top ν (by positivity)
  have hfun : ∀ u : ℝ, Real.exp (-(y ^ 2 / 4 / u + 1 * u)) = Real.exp (-u - y ^ 2 / (4 * u)) := by
    intro u
    congr 1
    rw [div_div]
    ring
  simp_rw [hfun] at hfin
  have hint :
      IntegrableOn (fun v : ℝ => v ^ (ν - 1) * Real.exp (-v - y ^ 2 / (4 * v))) (Ioi 0) := by
    refine ⟨(Measurable.aestronglyMeasurable (by fun_prop)), ?_⟩
    rw [hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ fun u (hu : 0 < u) => by positivity))]
    exact lt_top_iff_ne_top.2 hfin
  refine ⟨hint, ?_⟩
  -- the identity, from A51 at the order `-ν`
  have hK := cited_A51_integral (-ν) hy
  rw [ScaleSpace.besselK_neg] at hK
  have hcongr : ∀ t ∈ Ioi (0 : ℝ), Real.exp (-t - y ^ 2 / (4 * t)) / t ^ (-ν + 1)
      = t ^ (ν - 1) * Real.exp (-t - y ^ 2 / (4 * t)) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [show -ν + 1 = -(ν - 1) by ring, Real.rpow_neg ht0, div_inv_eq_mul, mul_comm]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr] at hK
  have hpow : (y / 2) ^ ν * (y / 2) ^ (-ν) = 1 := by
    rw [Real.rpow_neg hy2.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hy2 ν).ne']
  rw [hK]
  calc ∫ v in Ioi (0 : ℝ), v ^ (ν - 1) * Real.exp (-v - y ^ 2 / (4 * v))
      = ((y / 2) ^ ν * (y / 2) ^ (-ν)) *
          ∫ v in Ioi (0 : ℝ), v ^ (ν - 1) * Real.exp (-v - y ^ 2 / (4 * v)) := by
        rw [hpow, one_mul]
    _ = _ := by ring

/-- **`lem:bessel-k`(1), the profile.** `b_d(y) = (4/Γ(d/2)) (y/2)^{d/2} K_{d/2}(y)` and
`b_2(y) = 2yK_1(y)`, `y > 0`. Stated for every `d`, the node's `d ≥ 1` (from
`def:matern-pyramid-data`) being unused: widened by the author's decision of 2026-11-13. -/
theorem bessel_k_1_profile {d : ℕ} {y : ℝ} (hy : 0 < y) :
    besselProfile d y =
        4 / Real.Gamma ((d : ℝ) / 2) * (y / 2) ^ ((d : ℝ) / 2) * besselK ((d : ℝ) / 2) y ∧
      besselProfile 2 y = 2 * y * besselK 1 y := by
  refine ⟨?_, ?_⟩
  · rw [besselProfile, (bessel_k_1 ((d : ℝ) / 2) hy).2]
    ring
  · have h := (bessel_k_1 1 hy).2
    simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one] at h
    rw [besselProfile]
    norm_num
    rw [h]
    ring

/-- **`lem:bessel-k`(2).** `K₀' = -K₁` on `(0,∞)`, and `K₀(y) → 0` as `y → ∞`. -/
theorem bessel_k_2 :
    (∀ y : ℝ, 0 < y → HasDerivAt (besselK 0) (-besselK 1 y) y) ∧
      Tendsto (besselK 0) atTop (𝓝 0) := by
  refine ⟨fun y hy => ?_, ?_⟩
  · -- differentiation under the integral sign
    set F : ℝ → ℝ → ℝ := fun z u => Real.exp (-(z * Real.cosh u)) * Real.cosh (0 * u) with hF
    set F' : ℝ → ℝ → ℝ := fun z u => Real.exp (-(z * Real.cosh u)) * -(1 * Real.cosh u) *
      Real.cosh (0 * u) with hF'
    set bound : ℝ → ℝ := fun u => Real.exp (-(y / 2 * Real.cosh u)) * Real.cosh (1 * u)
      with hbound
    have hy2 : (0 : ℝ) < y / 2 := by positivity
    have hball : Metric.ball y (y / 2) ∈ 𝓝 y := Metric.ball_mem_nhds y hy2
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
      (F := F) (F' := F') (bound := bound) hball
      (Eventually.of_forall fun z => Continuous.aestronglyMeasurable (by fun_prop))
      (integrableOn_besselK 0 hy) (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun u z hz => ?_) (integrableOn_besselK 1 hy2)
      (ae_of_all _ fun u z _ => ?_)
    · have hint : ∫ u in Ioi (0 : ℝ), F' y u = -besselK 1 y := by
        rw [ScaleSpace.besselK, ← integral_neg]
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only [hF']
        simp
      rw [← hint]
      exact h.2
    · -- the bound
      have hz : y / 2 < z := by
        rw [Metric.mem_ball, Real.dist_eq] at hz
        linarith [neg_abs_le (z - y)]
      have hc : 0 ≤ Real.cosh u := (Real.cosh_pos u).le
      simp only [hF', hbound, zero_mul, Real.cosh_zero, mul_one, one_mul, norm_neg, norm_mul,
        Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hc
    · -- the derivative of the integrand
      simp only [hF, hF']
      exact (((hasDerivAt_id z).mul_const (Real.cosh u)).neg.exp).mul_const _
  · -- `K₀(y) ≤ e^{1-y} K₀(1)` for `y ≥ 1`
    have hle : ∀ y : ℝ, 1 ≤ y → besselK 0 y ≤ Real.exp (1 - y) * besselK 0 1 := by
      intro y hy
      rw [ScaleSpace.besselK, ScaleSpace.besselK, ← integral_const_mul]
      refine setIntegral_mono_on (integrableOn_besselK 0 (by linarith))
        ((integrableOn_besselK 0 one_pos).const_mul _) measurableSet_Ioi fun u _ => ?_
      simp only [zero_mul, Real.cosh_zero, mul_one, one_mul]
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [Real.one_le_cosh u]
    have hlim : Tendsto (fun y : ℝ => Real.exp (1 - y) * besselK 0 1) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ => 1 - y) atTop atBot := by
        simpa [sub_eq_add_neg, add_comm] using
          tendsto_atBot_add_const_left atTop (1 : ℝ) tendsto_neg_atTop_atBot
      simpa using (Real.tendsto_exp_atBot.comp h1).mul_const (besselK 0 1)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun y => ScaleSpace.besselK_nonneg 0 y) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    exact hle y hy

/-- `cosh` maps `(0,∞)` onto `(1,∞)`. -/
theorem cosh_image_Ioi : Real.cosh '' Ioi 0 = Ioi 1 := by
  ext s
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Real.one_lt_cosh.2 (ne_of_gt hu)
  · intro hs
    have hs1 : (1 : ℝ) < s := hs
    have h0 : 0 < s ^ 2 - 1 := by nlinarith
    refine ⟨Real.arsinh (Real.sqrt (s ^ 2 - 1)), Real.arsinh_pos_iff.2 (Real.sqrt_pos.2 h0), ?_⟩
    rw [Real.cosh_arsinh, Real.sq_sqrt h0.le, show 1 + (s ^ 2 - 1) = s ^ 2 by ring,
      Real.sqrt_sq (by linarith)]

/-- **`lem:bessel-k`(3).** `K₀(y) = ∫₁^∞ e^{-ys} (s² - 1)^{-1/2} ds` for `y > 0`, the integral
converging, and `K₀(y) - log(1/y)` stays bounded as `y ↓ 0`. -/
theorem bessel_k_3 :
    (∀ y : ℝ, 0 < y →
      IntegrableOn (fun s : ℝ => Real.exp (-(y * s)) * (s ^ 2 - 1) ^ (-(1 / 2 : ℝ))) (Ioi 1) ∧
        besselK 0 y = ∫ s in Ioi (1 : ℝ), Real.exp (-(y * s)) * (s ^ 2 - 1) ^ (-(1 / 2 : ℝ))) ∧
      ∃ C : ℝ, ∀ᶠ y in 𝓝[>] (0 : ℝ), |besselK 0 y - Real.log (1 / y)| ≤ C := by
  refine ⟨fun y hy => ?_, ⟨2, ?_⟩⟩
  · -- the substitution `s = cosh u`
    have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt Real.cosh (Real.sinh u) (Ioi 0) u :=
      fun u _ => (Real.hasDerivAt_cosh u).hasDerivWithinAt
    have hinj : InjOn Real.cosh (Ioi 0) := Real.cosh_strictMonoOn.injOn.mono Ioi_subset_Ici_self
    set g : ℝ → ℝ := fun s => Real.exp (-(y * s)) * (s ^ 2 - 1) ^ (-(1 / 2 : ℝ)) with hg
    have hpull : ∀ u ∈ Ioi (0 : ℝ), |Real.sinh u| • g (Real.cosh u)
        = Real.exp (-(y * Real.cosh u)) * Real.cosh (0 * u) := by
      intro u hu
      have hs : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
      have hsq : Real.cosh u ^ 2 - 1 = Real.sinh u ^ 2 := by rw [Real.cosh_sq]; ring
      simp only [hg, smul_eq_mul, hsq, zero_mul, Real.cosh_zero, mul_one]
      rw [Real.rpow_neg (sq_nonneg _), ← Real.sqrt_eq_rpow, Real.sqrt_sq hs.le, abs_of_pos hs]
      field_simp
    have himg := cosh_image_Ioi
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj g
    have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
    rw [himg] at hiff heq
    refine ⟨hiff.2 ((integrableOn_besselK 0 hy).congr_fun (fun u hu => (hpull u hu).symm)
      measurableSet_Ioi), ?_⟩
    rw [heq, setIntegral_congr_fun measurableSet_Ioi hpull]
    rfl
  · -- the behaviour at the origin
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with y hy
    obtain ⟨hy0, hy1⟩ := hy
    set L : ℝ := Real.log (1 / y) with hL
    have hL0 : 0 ≤ L := Real.log_nonneg (by rw [one_div]; exact (one_le_inv₀ hy0).2 hy1.le)
    have hyL : Real.exp L = 1 / y := Real.exp_log (by positivity)
    have hyL' : y * Real.exp L = 1 := by rw [hyL]; field_simp
    set f : ℝ → ℝ := fun u => Real.exp (-(y * Real.cosh u)) * Real.cosh (0 * u) with hf
    have hfint := integrableOn_besselK 0 hy0
    have hsplit : besselK 0 y = (∫ u in Ioc 0 L, f u) + ∫ u in Ioi L, f u := by
      rw [ScaleSpace.besselK, ← Ioc_union_Ioi_eq_Ioi hL0]
      exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hfint.mono_set (Ioc_subset_Ioi_self)) (hfint.mono_set (Ioi_subset_Ioi hL0))
    have hfle : ∀ u, f u ≤ 1 := fun u => by
      simp only [hf, zero_mul, Real.cosh_zero, mul_one]
      exact Real.exp_le_one_iff.2 (by nlinarith [Real.cosh_pos u])
    have hf0 : ∀ u, 0 ≤ f u := fun u => by positivity
    -- the piece on `(0, L]`
    have hvol : ∫ u in Ioc 0 L, (1 : ℝ) = L := by
      simp [hL0]
    have hup1 : ∫ u in Ioc 0 L, f u ≤ L := by
      calc ∫ u in Ioc 0 L, f u ≤ ∫ u in Ioc 0 L, (1 : ℝ) :=
            setIntegral_mono_on (hfint.mono_set Ioc_subset_Ioi_self)
              (continuous_const.integrableOn_Ioc) measurableSet_Ioc fun u _ => hfle u
        _ = L := hvol
    have hlow1 : L - 1 ≤ ∫ u in Ioc 0 L, f u := by
      have hlin : ∫ u in Ioc 0 L, (1 - y * Real.exp u) = L - (1 - y) := by
        rw [← intervalIntegral.integral_of_le hL0, intervalIntegral.integral_sub
          (continuous_const.intervalIntegrable _ _)
          ((by fun_prop : Continuous fun u => y * Real.exp u).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, integral_exp, intervalIntegral.integral_const,
          smul_eq_mul, mul_one, Real.exp_zero, mul_sub, hyL', mul_one]
        ring
      have h2 : ∫ u in Ioc 0 L, (1 - y * Real.exp u) ≤ ∫ u in Ioc 0 L, f u := by
        refine setIntegral_mono_on ((Continuous.integrableOn_Ioc (by fun_prop)))
          (hfint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun u hu => ?_
        have hu0 : 0 ≤ u := le_of_lt hu.1
        have hcosh : Real.cosh u ≤ Real.exp u := by
          rw [Real.cosh_eq]
          have : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.2 (by linarith)
          linarith
        simp only [hf, zero_mul, Real.cosh_zero, mul_one]
        have h3 := Real.add_one_le_exp (-(y * Real.cosh u))
        nlinarith
      linarith
    -- the piece on `(L, ∞)`
    have hup2 : ∫ u in Ioi L, f u ≤ 2 := by
      have hbd : ∀ u ∈ Ioi L, f u ≤ Real.exp (L / 2) * Real.exp (-(1 / 2) * u) := by
        intro u _
        simp only [hf, zero_mul, Real.cosh_zero, mul_one]
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have hcosh : Real.exp u / 2 ≤ Real.cosh u := by
          rw [Real.cosh_eq]; linarith [Real.exp_pos (-u)]
        have hyexp : y * Real.exp u = Real.exp (u - L) := by
          rw [Real.exp_sub, hyL]; field_simp
        have h1 := Real.add_one_le_exp (u - L)
        nlinarith
      have hint2 : IntegrableOn (fun u => Real.exp (L / 2) * Real.exp (-(1 / 2) * u)) (Ioi L) :=
        (exp_neg_integrableOn_Ioi L (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
      calc ∫ u in Ioi L, f u ≤ ∫ u in Ioi L, Real.exp (L / 2) * Real.exp (-(1 / 2) * u) :=
            setIntegral_mono_on (hfint.mono_set (Ioi_subset_Ioi hL0)) hint2 measurableSet_Ioi hbd
        _ = 2 := by
            have he : Real.exp (L / 2) * Real.exp (-(1 / 2) * L) = 1 := by
              rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
            rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num), neg_div_neg_eq,
              ← mul_div_assoc, he]
            norm_num
    have hlow2 : 0 ≤ ∫ u in Ioi L, f u := setIntegral_nonneg measurableSet_Ioi fun u _ => hf0 u
    rw [abs_le]
    constructor <;> linarith
end Pyramids
