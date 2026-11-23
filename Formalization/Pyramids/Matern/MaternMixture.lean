/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.MaternPyramid
import AffineHemigroup.MaternLaw
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Exponential

/-!
# `thm:matern-pyramid`(1): the kernel as a Gaussian variance mixture

Blueprint: `blueprint/src/parts/04-matern.tex`, `thm:matern-pyramid`. Phase 5, wave 3b.
`matern_pyramid_1_mixture` moved here from `PyramidsSkeleton.Ch04Matern`, its conclusion unchanged;
it no longer takes `1 ≤ d`, which its proof does not read (2026-11-15, a strengthening).

* **Almost sure convergence of `V_t` from its mean.** The exponential law is carried by `(0,∞)`
  and has mean `1` (`lintegral_ofReal_expMeasure_one`, the shared Gamma integral at power `1`), so
  `∫⁻ ∑ᵢ aᵢXᵢ = ∑ᵢ aᵢ < ∞` and the series of `[0,∞]`-valued terms is finite almost surely
  (`ae_lt_top`). Its real part `W` is measurable, and equals the real series `V_t` almost surely
  (`ENNReal.summable_toReal`), so `V_t` has the law of `W`, a junk value sitting on a null set.
* **The law as a product.** `W` is a measurable function of the sequence `(Xᵢ)`, which is
  independent of `Z`, so `(W, Z)` has the product law (`indepFun_iff_map_prod_eq_prod_map_map`), and
  the law of `√(2W) Z` is the Gaussian mixture of the affine export
  (`charFun_gaussMixture_lintegral`).
* **The Laplace transform of `W`.** On the partial sums, `E e^{-u∑_{i<N} aᵢXᵢ} = ∏_{i<N}(1 + uaᵢ)⁻¹`
  by independence (`lintegral_prod_eq_prod_lintegral_of_indepFun`) and the exponential law's
  Laplace transform; dominated convergence (the integrands are at most `1`) passes to `W`, and the
  line's display (`matern_pyramid_line_display`) identifies the infinite product with
  `e^{-F_q(t|ω|)}`. The transforms agree, so the laws do.

**What it reaches.** Lean core.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

variable {d : ℕ}

/-- **The mean of the standard exponential law**: `∫⁻ x dExp(1) = 1`, the shared Gamma integral
at power `1`. -/
theorem lintegral_ofReal_expMeasure_one :
    ∫⁻ x, ENNReal.ofReal x ∂(expMeasure 1) = 1 := by
  have h := ScaleSpace.lintegral_gammaMeasure_rpow_mul_exp (a := 1) (r := 1) one_pos one_pos
    (q := 1) (s := 0) (by norm_num) le_rfl
  have hG : Real.Gamma (1 + 1) = 1 := by
    rw [show (1 : ℝ) + 1 = 2 by norm_num, show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one
      one_ne_zero, Real.Gamma_one, mul_one]
  simp only [Real.rpow_one, zero_mul, neg_zero, Real.exp_zero, mul_one, add_zero, div_one,
    Real.one_rpow, Real.Gamma_one, hG, ENNReal.ofReal_one] at h
  exact h

/-- **The Laplace transform of the standard exponential law**: `∫ e^{-ux} dExp(1) = (1 + u)⁻¹`. -/
theorem lintegral_exp_expMeasure_one {u : ℝ} (hu : 0 ≤ u) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(u * x))) ∂(expMeasure 1) = ENNReal.ofReal ((1 + u)⁻¹) := by
  change ∫⁻ x, ENNReal.ofReal (Real.exp (-(u * x))) ∂(gammaMeasure 1 1) = _
  rw [lintegral_exp_gammaMeasure one_pos hu, Real.rpow_neg_one]

/-- **`thm:matern-pyramid`(1), the mixture.** With `X_i` independent standard exponential and `Z`
standard normal on `ℝ^d` independent of them, `μ_t` is the law of `√(2V_t) Z`,
`V_t = ∑_{i ≥ 1} c² q^{-2i} t² X_i`. -/
theorem matern_pyramid_1_mixture {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (Z : Ω → Rd d) (hX : ∀ i, Measurable (X i)) (hZ : Measurable Z)
    (hXlaw : ∀ i, P.map (X i) = ProbabilityTheory.expMeasure 1)
    (hZlaw : P.map Z = ProbabilityTheory.stdGaussian (Rd d))
    (hind : ProbabilityTheory.iIndepFun X P)
    (hindZ : ProbabilityTheory.IndepFun (fun ω i => X i ω) Z P) {t : ℝ} (ht : 0 ≤ t) :
    P.map (fun ω => Real.sqrt (2 * ∑' i : ℕ, c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) * X i ω) • Z ω) =
      μ 0 t := by
  set a : ℕ → ℝ := fun i => c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) with ha_def
  have hq0 : 0 < q := by linarith
  have ha0 : ∀ i, 0 ≤ a i := fun i => by positivity
  have hasum : Summable a := by
    have hg : Summable fun i : ℕ => (q ^ 2)⁻¹ ^ i :=
      summable_geometric_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero))
    refine (hg.mul_left (c ^ 2 * t ^ 2 / q ^ 2)).congr fun i => ?_
    simp only [ha_def, inv_pow, ← pow_mul]
    rw [show 2 * (i + 1) = 2 + 2 * i by ring, pow_add]
    field_simp
  -- The variables are nonnegative almost surely.
  have hXpos : ∀ᵐ ω ∂P, ∀ i, 0 ≤ X i ω := by
    rw [ae_all_iff]
    intro i
    have h := ScaleSpace.ae_pos_gammaMeasure 1 1
    rw [show gammaMeasure 1 1 = expMeasure 1 from rfl, ← hXlaw i] at h
    exact (ae_of_ae_map (hX i).aemeasurable h).mono fun _ h => h.le
  -- The series of `[0,∞]`-valued terms, finite almost surely.
  let S : (ℕ → ℝ) → ℝ≥0∞ := fun x => ∑' i, ENNReal.ofReal (a i * x i)
  have hSm : Measurable S :=
    Measurable.tsum fun i => (measurable_const.mul (measurable_pi_apply i)).ennreal_ofReal
  let Xv : Ω → (ℕ → ℝ) := fun ω i => X i ω
  have hXv : Measurable Xv := measurable_pi_lambda _ hX
  have hterm : ∀ i, ∫⁻ ω, ENNReal.ofReal (a i * X i ω) ∂P = ENNReal.ofReal (a i) := by
    intro i
    simp_rw [ENNReal.ofReal_mul (ha0 i)]
    rw [lintegral_const_mul _ (hX i).ennreal_ofReal,
      ← lintegral_map ENNReal.measurable_ofReal (hX i), hXlaw i, lintegral_ofReal_expMeasure_one,
      mul_one]
  have hSint : ∫⁻ ω, S (Xv ω) ∂P ≠ ⊤ := by
    change ∫⁻ ω, ∑' i, ENNReal.ofReal (a i * X i ω) ∂P ≠ ⊤
    rw [lintegral_tsum fun i =>
      ((measurable_const.mul (hX i)).ennreal_ofReal).aemeasurable]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hasum]
    exact ENNReal.ofReal_ne_top
  have hSfin : ∀ᵐ ω ∂P, S (Xv ω) < ⊤ := ae_lt_top (hSm.comp hXv) hSint
  -- Its real part `W`, the series almost surely.
  let W : Ω → ℝ := fun ω => (S (Xv ω)).toReal
  have hW : Measurable W := (hSm.comp hXv).ennreal_toReal
  have hW0 : ∀ ω, 0 ≤ W ω := fun ω => ENNReal.toReal_nonneg
  have hsum_ae : ∀ᵐ ω ∂P, HasSum (fun i => a i * X i ω) (W ω) := by
    filter_upwards [hXpos, hSfin] with ω h0 hfin
    have hnn : ∀ i, 0 ≤ a i * X i ω := fun i => mul_nonneg (ha0 i) (h0 i)
    have hs : Summable (fun i => a i * X i ω) := by
      have h : Summable fun i => (ENNReal.ofReal (a i * X i ω)).toReal :=
        ENNReal.summable_toReal hfin.ne
      exact h.congr fun i => ENNReal.toReal_ofReal (hnn i)
    have hW' : W ω = ∑' i, a i * X i ω := by
      change (∑' i, ENNReal.ofReal (a i * X i ω)).toReal = _
      rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs, ENNReal.toReal_ofReal (tsum_nonneg hnn)]
    rw [hW']
    exact hs.hasSum
  -- The law of `√(2W) Z`.
  have hindW : IndepFun W Z P :=
    hindZ.comp (φ := fun x => (S x).toReal) (ψ := id) hSm.ennreal_toReal measurable_id
  set ν := P.map W with hν_def
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hW.aemeasurable
  have hν0 : ∀ᵐ v ∂ν, 0 ≤ v :=
    (ae_map_iff hW.aemeasurable measurableSet_Ici).2 (ae_of_all _ hW0)
  have hmap : P.map (fun ω => Real.sqrt (2 * ∑' i : ℕ, a i * X i ω) • Z ω) =
      (ν.prod (stdGaussian (Rd d))).map (fun p => Real.sqrt (2 * p.1) • p.2) := by
    have hae : (fun ω => Real.sqrt (2 * ∑' i : ℕ, a i * X i ω) • Z ω) =ᵐ[P]
        fun ω => Real.sqrt (2 * W ω) • Z ω :=
      hsum_ae.mono fun ω h => by simp only [h.tsum_eq]
    rw [Measure.map_congr hae, ← hZlaw,
      ← (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hZ.aemeasurable).1 hindW,
      Measure.map_map measurable_sqrtTwoSmul (hW.prodMk hZ)]
    rfl
  -- The Laplace transform of `W`.
  have hlap : ∀ u : ℝ, 0 ≤ u →
      ∫⁻ v, ENNReal.ofReal (Real.exp (-(u * v))) ∂ν =
        ENNReal.ofReal (Real.exp (-maternExponent q c (t * Real.sqrt u))) := by
    intro u hu
    rw [hν_def, lintegral_map (by fun_prop) hW]
    let V : ℕ → Ω → ℝ := fun N ω => ∑ i ∈ Finset.range N, a i * X i ω
    have hVm : ∀ N, Measurable (V N) := fun N =>
      Finset.measurable_sum _ fun i _ => measurable_const.mul (hX i)
    have hlim : Tendsto (fun N => ∫⁻ ω, ENNReal.ofReal (Real.exp (-(u * V N ω))) ∂P) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (Real.exp (-(u * W ω))) ∂P)) := by
      refine tendsto_lintegral_of_dominated_convergence (fun _ => 1)
        (fun N => (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(u * x)))).comp
          (hVm N)) (fun N => ?_) (by simp) ?_
      · filter_upwards [hXpos] with ω h0
        rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff, neg_nonpos]
        exact mul_nonneg hu (Finset.sum_nonneg fun i _ => mul_nonneg (ha0 i) (h0 i))
      · filter_upwards [hsum_ae] with ω h
        exact (ENNReal.continuous_ofReal.comp (by fun_prop :
          Continuous fun x : ℝ => Real.exp (-(u * x)))).continuousAt.tendsto.comp
            h.tendsto_sum_nat
    have hfin : ∀ N, ∫⁻ ω, ENNReal.ofReal (Real.exp (-(u * V N ω))) ∂P =
        ∏ i ∈ Finset.range N, ENNReal.ofReal ((1 + u * a i)⁻¹) := by
      intro N
      have hsplit : ∀ ω, ENNReal.ofReal (Real.exp (-(u * V N ω))) =
          ∏ i ∈ Finset.range N, ENNReal.ofReal (Real.exp (-(u * a i * X i ω))) := by
        intro ω
        rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← Real.exp_sum]
        congr 2
        simp only [V, Finset.mul_sum, ← Finset.sum_neg_distrib, mul_assoc]
      simp_rw [hsplit]
      rw [lintegral_prod_eq_prod_lintegral_of_indepFun _
        (fun i ω => ENNReal.ofReal (Real.exp (-(u * a i * X i ω))))
        (hind.comp (fun i x => ENNReal.ofReal (Real.exp (-(u * a i * x)))) fun i => by fun_prop)
        fun i => by fun_prop]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← lintegral_map (f := fun x => ENNReal.ofReal (Real.exp (-(u * a i * x))))
        (by fun_prop) (hX i), hXlaw i]
      exact lintegral_exp_expMeasure_one (mul_nonneg hu (ha0 i))
    have hprod : Tendsto (fun N => ∏ i ∈ Finset.range N, ENNReal.ofReal ((1 + u * a i)⁻¹)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-maternExponent q c (t * Real.sqrt u))))) := by
      have h := (matern_pyramid_line_display hq hc t (Real.sqrt u)).tendsto_prod_nat
      have h' := (ENNReal.continuous_ofReal.tendsto _).comp h
      refine h'.congr fun N => ?_
      simp only [Function.comp_apply]
      rw [ENNReal.ofReal_prod_of_nonneg fun i _ => by positivity]
      refine Finset.prod_congr rfl fun i _ => ?_
      congr 2
      rw [mul_pow, Real.sq_sqrt hu]
      simp only [ha_def]
      ring
    rw [funext hfin] at hlim
    exact tendsto_nhds_unique hlim hprod
  -- The transforms agree.
  rw [hmap]
  obtain ⟨hprob, hchar⟩ := hμ 0 t le_rfl ht
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_gaussMixture_lintegral ν hν0 ω, hchar ω]
  simp only [zero_mul, maternExponent_zero, sub_zero]
  rw [
    hlap _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

end Pyramids
