/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.CreationPlane
import AffineHemigroup.GaussMixture

/-!
# `prop:creation-plane`(4): the Gaussian ladder

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:creation-plane`. Phase 5, wave 3b (on the
VM). `creation_plane_4` moved here from `PyramidsSkeleton.Ch04Matern`; review round 2 strengthened
its conclusion (the rung of the rise has one maximum).

* **Diagonal Gaussians under `N(0, τI)`.** For `v > 0` coordinatewise,
  `N(0, τI) * e^{-∑ zᵢ²/(2vᵢ)} = ∏ᵢ √(vᵢ/(vᵢ + τ)) · e^{-∑ zᵢ²/(2(vᵢ + τ))}`, pointwise: the heat
  kernel and the integrand factor over the coordinates, and each factor is a one-dimensional
  Gaussian integral after completing the square (`mconvE_gaussVar_Ev`).
* **The witness is a record.** `h_{a,δ}` is the sum of the Gaussians of covariances `I` (twice,
  shifted) and `diag(4a², δ², …, δ²)`; for `τ < min(1, δ²)` each is `N(0, τI)` applied to the
  Gaussian of covariance `Σ - τI`, positive definite. So `h_{a,δ} = N(0, τI) * g`.
* **The ladder.** `N(0, (τ + 1)I) = N(0, τI) ∗ N(0, I)` (the transforms), so the record at
  `q^{2n}τ_n = τ_n + 1` is `N(0, I) * h_{a,δ}`, with two local maxima by clause (1).
* **The first rise.** Rung `0` has one maximum and rung `n` at least two; with `k + 1` the least
  rung with two (`Nat.find`), rung `k` is `N(0, sI) * h_{a,δ}`, positive and tending to `0`
  (`tendsto_creationWitness`, `tendsto_mconvE_of_tendsto`), so it attains its maximum and has
  exactly one (review round 2).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (mconvE)
open scoped Topology ENNReal RealInnerProductSpace ComplexOrder

variable {d : ℕ}

/-! ## Records against a convolution of laws -/

/-- `(μ ∗ ν) * f = ν * (μ * f)` pointwise, for `f` bounded and continuous. -/
theorem mconvE_conv_of_bdd (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : Rd d → ℝ} (hf : Continuous f) {A : ℝ} (hA : ∀ z, |f z| ≤ A) (x : Rd d) :
    mconvE (μ ∗ ν) f x = mconvE ν (mconvE μ f) x := by
  simp only [ScaleSpace.mconvE_apply]
  rw [Measure.conv, integral_map (φ := fun p : Rd d × Rd d => p.1 + p.2) (by fun_prop)
    (f := fun y => f (x - y)) (Continuous.aestronglyMeasurable (by fun_prop))]
  have hint : Integrable (fun p : Rd d × Rd d => f (x - (p.1 + p.2))) (μ.prod ν) := by
    refine (integrable_const A).mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]; exact hA _
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  congr 1
  funext y
  congr 1
  abel

/-- `N(0, (τ + σ)I) = N(0, τI) ∗ N(0, σI)`. -/
theorem gaussVar_add {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) :
    gaussVar d (τ + σ) = gaussVar d τ ∗ gaussVar d σ := by
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_conv, charFun_gaussVar (by linarith), charFun_gaussVar hτ, charFun_gaussVar hσ,
    ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-! ## Diagonal Gaussians -/

/-- `E_v(z) := e^{-∑ zᵢ²/(2vᵢ)}`. -/
noncomputable def gEv (v : Fin d → ℝ) (z : Rd d) : ℝ := Real.exp (-∑ i, z i ^ 2 / (2 * v i))

theorem gEv_pos (v : Fin d → ℝ) (z : Rd d) : 0 < gEv v z := Real.exp_pos _

theorem continuous_gEv (v : Fin d → ℝ) : Continuous (gEv v) := by
  unfold gEv
  have : ∀ i : Fin d, Continuous fun z : Rd d => z i :=
    fun i => (EuclideanSpace.proj i).continuous
  fun_prop

theorem gEv_le_one {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) (z : Rd d) : gEv v z ≤ 1 := by
  unfold gEv
  rw [Real.exp_le_one_iff, neg_nonpos]
  exact Finset.sum_nonneg fun i _ => by have := hv i; positivity

theorem gEv_prod (v : Fin d → ℝ) (z : Rd d) :
    gEv v z = ∏ i, Real.exp (-(z i ^ 2 / (2 * v i))) := by
  rw [gEv, ← Real.exp_sum, Finset.sum_neg_distrib]

/-- The heat kernel factors over the coordinates. -/
theorem heatKernel_eq_prod {τ : ℝ} (hτ : 0 < τ) (y : Rd d) :
    heatKernel d τ y =
      ∏ i, ((Real.sqrt (2 * Real.pi * τ))⁻¹ * Real.exp (-(y i ^ 2 / (2 * τ)))) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, heatKernel, EuclideanSpace.real_norm_sq_eq]
  congr 1
  swap
  · congr 1
    rw [neg_div, Finset.sum_div, Finset.sum_neg_distrib]
  have hX : 0 < 2 * Real.pi * τ := by positivity
  rw [Real.sqrt_eq_rpow, inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hX.le,
    ← Real.rpow_neg hX.le]
  congr 1
  ring

/-- **The one-dimensional step**: `∫ (2πτ)^{-1/2} e^{-s²/(2τ)} e^{-(u-s)²/(2v)} ds
= √(v/(v+τ)) e^{-u²/(2(v+τ))}`. -/
theorem integral_gauss_step {τ v : ℝ} (hτ : 0 < τ) (hv : 0 < v) (u : ℝ) :
    ∫ s : ℝ, (Real.sqrt (2 * Real.pi * τ))⁻¹ * Real.exp (-(s ^ 2 / (2 * τ))) *
        Real.exp (-((u - s) ^ 2 / (2 * v))) =
      Real.sqrt (v / (v + τ)) * Real.exp (-(u ^ 2 / (2 * (v + τ)))) := by
  set b : ℝ := (v + τ) / (2 * v * τ) with hb
  set s0 : ℝ := u * τ / (v + τ) with hs0
  have hpt : ∀ s : ℝ, (Real.sqrt (2 * Real.pi * τ))⁻¹ * Real.exp (-(s ^ 2 / (2 * τ))) *
      Real.exp (-((u - s) ^ 2 / (2 * v))) =
      ((Real.sqrt (2 * Real.pi * τ))⁻¹ * Real.exp (-(u ^ 2 / (2 * (v + τ))))) *
        Real.exp (-b * (s - s0) ^ 2) := by
    intro s
    rw [mul_assoc, ← Real.exp_add, mul_assoc _ (Real.exp _), ← Real.exp_add]
    congr 2
    rw [hb, hs0]
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub_right_eq_self (fun s => Real.exp (-b * s ^ 2)) s0,
    integral_gaussian]
  have hbpos : 0 < b := by positivity
  rw [mul_comm _ (Real.sqrt (Real.pi / b)), ← mul_assoc]
  congr 1
  rw [← Real.sqrt_inv, mul_comm, ← Real.sqrt_mul (by positivity)]
  congr 1
  rw [hb]
  field_simp

/-- **Diagonal Gaussians under `N(0, τI)`.** -/
theorem mconvE_gaussVar_gEv {τ : ℝ} (hτ : 0 < τ) {v : Fin d → ℝ} (hv : ∀ i, 0 < v i)
    (x : Rd d) :
    mconvE (gaussVar d τ) (gEv v) x =
      (∏ i, Real.sqrt (v i / (v i + τ))) * gEv (fun i => v i + τ) x := by
  rw [ScaleSpace.mconvE_apply, gaussVar_eq_withDensity hτ,
    integral_withDensity_eq_integral_toReal_smul continuous_heatKernel.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpt : ∀ y : Rd d, (ENNReal.ofReal (heatKernel d τ y)).toReal • gEv v (x - y) =
      ∏ i, ((Real.sqrt (2 * Real.pi * τ))⁻¹ * Real.exp (-(y i ^ 2 / (2 * τ))) *
        Real.exp (-((x i - y i) ^ 2 / (2 * v i)))) := by
    intro y
    have hk : 0 ≤ heatKernel d τ y := by unfold heatKernel; positivity
    rw [ENNReal.toReal_ofReal hk, smul_eq_mul, heatKernel_eq_prod hτ, gEv_prod,
      ← Finset.prod_mul_distrib]
    simp [PiLp.sub_apply]
  simp_rw [hpt]
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)
  set φ : Fin d → ℝ → ℝ := fun i s => (Real.sqrt (2 * Real.pi * τ))⁻¹ *
    Real.exp (-(s ^ 2 / (2 * τ))) * Real.exp (-((x i - s) ^ 2 / (2 * v i))) with hφ
  have key := hmp.integral_comp' (g := fun y : Fin d → ℝ => ∏ i, φ i (y i))
  refine key.trans ?_
  rw [volume_pi, integral_fintype_prod_eq_prod (f := φ)]
  simp_rw [hφ, integral_gauss_step hτ (hv _)]
  rw [Finset.prod_mul_distrib, gEv_prod]

/-- The constant of the diagonal Gaussian density. -/
noncomputable def gConst (v : Fin d → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ) / 2) * (∏ i, v i) ^ (-(1 : ℝ) / 2)

theorem gConst_pos {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) : 0 < gConst v := by
  have : 0 < ∏ i, v i := Finset.prod_pos fun i _ => hv i
  unfold gConst; positivity

/-- **The diagonal Gaussian density** is `gConst v · E_v`. -/
theorem gaussDensityCov_diagonal {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) (z : Rd d) :
    gaussDensityCov (Matrix.diagonal v) z = gConst v * gEv v z := by
  have hinv : (Matrix.diagonal v)⁻¹ = Matrix.diagonal fun i => (v i)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp [inv_mul_cancel₀ (hv _).ne']
  rw [gaussDensityCov, Matrix.det_diagonal, hinv, quad_eq_dotProduct, gConst, gEv]
  congr 2
  simp only [dotProduct, Matrix.mulVec_diagonal]
  rw [neg_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (hv i).ne'
  field_simp

theorem continuous_gaussDensityCov_diagonal {v : Fin d → ℝ} (hv : ∀ i, 0 < v i) :
    Continuous (gaussDensityCov (Matrix.diagonal v)) := by
  have : gaussDensityCov (Matrix.diagonal v) = fun z => gConst v * gEv v z :=
    funext (gaussDensityCov_diagonal hv)
  rw [this]
  exact continuous_const.mul (continuous_gEv v)

/-- `E_1 = e^{-|·|²/2}`. -/
theorem gEv_one (z : Rd d) : gEv (fun _ => 1) z = gB z := by
  rw [gEv, gB, EuclideanSpace.real_norm_sq_eq, neg_div, Finset.sum_div]
  simp

/-- `E_{diag(4a², δ², …)}` is the ridge's profile. -/
theorem gEv_ridge [NeZero d] (a δ : ℝ) (ha : a ≠ 0) (hδ : δ ≠ 0) (x : Rd d) :
    8 * a ^ 2 * gEv (fun i => if i = 0 then 4 * a ^ 2 else δ ^ 2) x = cwRidge a δ x := by
  rw [gEv, cwRidge, mul_assoc (8 * a ^ 2), ← Real.exp_add, trv_eq, EuclideanSpace.real_norm_sq_eq]
  congr 2
  have hpt : ∀ i : Fin d, x i ^ 2 / (2 * (if i = 0 then 4 * a ^ 2 else δ ^ 2)) =
      x i ^ 2 / (2 * δ ^ 2) +
        if i = 0 then x 0 ^ 2 / (8 * a ^ 2) - x 0 ^ 2 / (2 * δ ^ 2) else 0 := by
    intro i
    split_ifs with h
    · subst h; field_simp; ring
    · ring
  rw [Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), ← Finset.sum_div]
  field_simp
  ring

/-! ## The witness is a record -/

/-- **`h_{a,δ} = N(0, τI) * g`** for `0 < τ < min(1, δ²)`, with `g` a positive sum of three
diagonal Gaussians: the bumps of covariance `(1 - τ)I` at `±ae₁` and the ridge of covariance
`diag(4a² - τ, δ² - τ, …)`. -/
theorem exists_gauss_record [NeZero d] {a δ τ : ℝ} (ha : 1 < a) (hδ : 0 < δ) (hτ : 0 < τ)
    (hτ1 : τ < 1) (hτδ : τ < δ ^ 2) :
    ∃ (w0 w2 : ℝ) (v0 v2 : Fin d → ℝ), 0 < w0 ∧ 0 < w2 ∧ (∀ i, 0 < v0 i) ∧ (∀ i, 0 < v2 i) ∧
      ∀ x, mconvE (gaussVar d τ) (fun z => w0 * gConst v0 * gEv v0 (z - a • ebasis 0) +
        w0 * gConst v0 * gEv v0 (z + a • ebasis 0) + w2 * gConst v2 * gEv v2 z) x =
        creationWitness d a δ x := by
  set v0 : Fin d → ℝ := fun _ => 1 - τ with hv0
  set v2 : Fin d → ℝ := fun i => if i = 0 then 4 * a ^ 2 - τ else δ ^ 2 - τ with hv2
  have hv0p : ∀ i, 0 < v0 i := fun _ => by simp only [hv0]; linarith
  have hv2p : ∀ i, 0 < v2 i := fun i => by
    simp only [hv2]; split_ifs
    · nlinarith
    · linarith
  set K0 := ∏ i, Real.sqrt (v0 i / (v0 i + τ)) with hK0
  set K2 := ∏ i, Real.sqrt (v2 i / (v2 i + τ)) with hK2
  have hK0p : 0 < K0 := Finset.prod_pos fun i _ => Real.sqrt_pos.2 (by have := hv0p i; positivity)
  have hK2p : 0 < K2 := Finset.prod_pos fun i _ => Real.sqrt_pos.2 (by have := hv2p i; positivity)
  set w0 := (gConst v0 * K0)⁻¹ with hw0
  set w2 := 8 * a ^ 2 * (gConst v2 * K2)⁻¹ with hw2
  have hw0p : 0 < w0 := inv_pos.2 (mul_pos (gConst_pos hv0p) hK0p)
  have hw2p : 0 < w2 := by have := gConst_pos hv2p; positivity
  have hC0 := gConst_pos hv0p
  have hC2 := gConst_pos hv2p
  set p : Rd d := a • ebasis 0 with hp
  refine ⟨w0, w2, v0, v2, hw0p, hw2p, hv0p, hv2p, fun x => ?_⟩
  have i1 := integrable_comp_sub_of_bdd_Rd (gaussVar d τ)
    (f := fun z => w0 * gConst v0 * gEv v0 (z + -p)) (by have := continuous_gEv v0; fun_prop)
    (A := w0 * gConst v0) (fun z => by
      rw [abs_of_pos (by have := gEv_pos v0 (z + -p); positivity)]
      exact mul_le_of_le_one_right (mul_pos hw0p hC0).le (gEv_le_one hv0p _)) x
  have i2 := integrable_comp_sub_of_bdd_Rd (gaussVar d τ)
    (f := fun z => w0 * gConst v0 * gEv v0 (z + p)) (by have := continuous_gEv v0; fun_prop)
    (A := w0 * gConst v0) (fun z => by
      rw [abs_of_pos (by have := gEv_pos v0 (z + p); positivity)]
      exact mul_le_of_le_one_right (mul_pos hw0p hC0).le (gEv_le_one hv0p _)) x
  have i3 := integrable_comp_sub_of_bdd_Rd (gaussVar d τ)
    (f := fun z => w2 * gConst v2 * gEv v2 z) (by have := continuous_gEv v2; fun_prop)
    (A := w2 * gConst v2) (fun z => by
      rw [abs_of_pos (by have := gEv_pos v2 z; positivity)]
      exact mul_le_of_le_one_right (mul_pos hw2p hC2).le (gEv_le_one hv2p _)) x
  have hsplit : mconvE (gaussVar d τ) (fun z => w0 * gConst v0 * gEv v0 (z - p) +
        w0 * gConst v0 * gEv v0 (z + p) + w2 * gConst v2 * gEv v2 z) x =
      w0 * gConst v0 * mconvE (gaussVar d τ) (fun z => gEv v0 (z + -p)) x +
      w0 * gConst v0 * mconvE (gaussVar d τ) (fun z => gEv v0 (z + p)) x +
      w2 * gConst v2 * mconvE (gaussVar d τ) (gEv v2) x := by
    simp only [ScaleSpace.mconvE_apply]
    have e : ∀ y, w0 * gConst v0 * gEv v0 (x - y - p) + w0 * gConst v0 * gEv v0 (x - y + p) +
        w2 * gConst v2 * gEv v2 (x - y) = (w0 * gConst v0 * gEv v0 (x - y + -p) +
        w0 * gConst v0 * gEv v0 (x - y + p)) + w2 * gConst v2 * gEv v2 (x - y) := fun y => by
      rw [sub_eq_add_neg (x - y) p]
    simp_rw [e]
    have i12 : Integrable (fun y => w0 * gConst v0 * gEv v0 (x - y + -p) +
        w0 * gConst v0 * gEv v0 (x - y + p)) (gaussVar d τ) := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul]
  rw [hsplit, mconvE_comp_add, mconvE_comp_add, mconvE_gaussVar_gEv hτ hv0p,
    mconvE_gaussVar_gEv hτ hv0p, mconvE_gaussVar_gEv hτ hv2p, ← sub_eq_add_neg,
    creationWitness_eq_sum]
  have hv0τ : (fun i => v0 i + τ) = fun _ => (1 : ℝ) := by funext i; simp [hv0]
  have hv2τ : (fun i => v2 i + τ) = fun i => if i = 0 then 4 * a ^ 2 else δ ^ 2 := by
    funext i; simp only [hv2]; split_ifs <;> ring
  rw [hv0τ, hv2τ, gEv_one, gEv_one, ← hK0, ← hK2, ← gEv_ridge a δ (by linarith) hδ.ne' x]
  have hA : w0 * gConst v0 * K0 = 1 := by
    rw [hw0, mul_assoc, inv_mul_cancel₀ (mul_pos hC0 hK0p).ne']
  have hB : w2 * gConst v2 * K2 = 8 * a ^ 2 := by
    rw [hw2, mul_assoc, mul_assoc, inv_mul_cancel₀ (mul_pos hC2 hK2p).ne', mul_one]
  calc w0 * gConst v0 * (K0 * gB (x - p)) + w0 * gConst v0 * (K0 * gB (x + p)) +
        w2 * gConst v2 * (K2 * gEv (fun i => if i = 0 then 4 * a ^ 2 else δ ^ 2) x)
      = (w0 * gConst v0 * K0) * gB (x - p) + (w0 * gConst v0 * K0) * gB (x + p) +
        (w2 * gConst v2 * K2) * gEv (fun i => if i = 0 then 4 * a ^ 2 else δ ^ 2) x := by ring
    _ = _ := by rw [hA, hB, one_mul, one_mul]

/-! ## The rung below the first rise -/

/-- A record of a positive bounded continuous function is positive. -/
theorem mconvE_pos_of_pos (μ : Measure (Rd d)) [IsProbabilityMeasure μ] {f : Rd d → ℝ}
    (hf : Continuous f) {A : ℝ} (hA : ∀ z, |f z| ≤ A) (hpos : ∀ z, 0 < f z) (x : Rd d) :
    0 < mconvE μ f x := by
  rw [ScaleSpace.mconvE_apply]
  refine (integral_pos_iff_support_of_nonneg (fun y => (hpos _).le)
    (integrable_comp_sub_of_bdd_Rd μ hf hA x)).2 ?_
  have : Function.support (fun y => f (x - y)) = univ :=
    Function.support_eq_univ fun y => (hpos _).ne'
  rw [this, measure_univ]
  exact one_pos

/-- Translation keeps `|x| → ∞`. -/
theorem tendsto_sub_comap_norm (y : Rd d) :
    Tendsto (fun x : Rd d => x - y) (comap (fun x => ‖x‖) atTop) (comap (fun x => ‖x‖) atTop) := by
  refine tendsto_comap_iff.2 (?_ : Tendsto (fun x : Rd d => ‖x - y‖) _ atTop)
  refine tendsto_atTop_mono (fun x => norm_sub_norm_le x y) ?_
  exact tendsto_atTop_add_const_right _ _ tendsto_comap

/-- A record of a bounded continuous function that tends to `0` at infinity tends to `0`. -/
theorem tendsto_mconvE_of_tendsto (μ : Measure (Rd d)) [IsProbabilityMeasure μ] {f : Rd d → ℝ}
    (hf : Continuous f) {A : ℝ} (hA : ∀ z, |f z| ≤ A)
    (hlim : Tendsto f (comap (fun x => ‖x‖) atTop) (𝓝 0)) :
    Tendsto (mconvE μ f) (comap (fun x => ‖x‖) atTop) (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (l := comap (fun x : Rd d => ‖x‖) atTop)
    (F := fun x y => f (x - y)) (f := fun _ => (0 : ℝ)) (fun _ => A)
    (Eventually.of_forall fun x => (integrable_comp_sub_of_bdd_Rd μ hf hA x).1)
    (Eventually.of_forall fun x => Eventually.of_forall fun _ => by
      rw [Real.norm_eq_abs]; exact hA _)
    (integrable_const A) (Eventually.of_forall fun y => hlim.comp (tendsto_sub_comap_norm y))
  rw [integral_zero] at this
  refine this.congr fun x => ?_
  rw [ScaleSpace.mconvE_apply]

/-- A continuous function positive somewhere and tending to `0` at infinity attains its maximum, a
local maximum. -/
theorem exists_isLocalMax_of_tendsto {F : Rd d → ℝ} (hF : Continuous F) {x0 : Rd d}
    (h0 : 0 < F x0) (hlim : Tendsto F (comap (fun x => ‖x‖) atTop) (𝓝 0)) :
    ∃ x, IsLocalMax F x := by
  obtain ⟨s, hs, hsub⟩ := (Filter.mem_comap).1 (hlim.eventually (gt_mem_nhds h0))
  obtain ⟨R, hR⟩ := Filter.mem_atTop_sets.1 hs
  obtain ⟨x, -, hmax⟩ := (isCompact_closedBall (0 : Rd d) (max R ‖x0‖)).exists_isMaxOn
    ⟨x0, mem_closedBall_zero_iff.2 (le_max_right _ _)⟩ hF.continuousOn
  have hx0 : F x0 ≤ F x := hmax (mem_closedBall_zero_iff.2 (le_max_right _ _))
  refine ⟨x, Eventually.of_forall fun y => ?_⟩
  by_cases hy : ‖y‖ ≤ max R ‖x0‖
  · exact hmax (mem_closedBall_zero_iff.2 hy)
  · have : F y < F x0 := hsub (hR _ ((le_max_left _ _).trans (not_le.1 hy).le))
    linarith

theorem tendsto_gB_comap_norm :
    Tendsto (gB (d := d)) (comap (fun x => ‖x‖) atTop) (𝓝 0) := by
  have h2 : Tendsto (fun r : ℝ => Real.exp (-r ^ 2 / 2)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have : Tendsto (fun r : ℝ => r ^ 2 / 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
    have h3 := tendsto_neg_atTop_atBot.comp this
    refine h3.congr fun r => ?_
    simp only [Function.comp]
    ring
  exact h2.comp tendsto_comap

/-- The ridge lies under a Gaussian, for every `δ ≠ 0`. -/
theorem cwRidge_le_gauss_min [NeZero d] (a δ : ℝ) (z : Rd d) :
    cwRidge a δ z ≤
      8 * a ^ 2 * Real.exp (-(min (1 / (8 * a ^ 2)) (1 / (2 * δ ^ 2))) * ‖z‖ ^ 2) := by
  unfold cwRidge
  rw [mul_assoc, ← Real.exp_add]
  gcongr
  set c := min (1 / (8 * a ^ 2)) (1 / (2 * δ ^ 2)) with hc
  have hn : ‖z‖ ^ 2 = z 0 ^ 2 + trv z := by rw [trv_eq]; ring
  have ht := trv_nonneg z
  have h1 : c * z 0 ^ 2 ≤ z 0 ^ 2 / (8 * a ^ 2) := by
    rw [div_eq_mul_one_div, mul_comm (z 0 ^ 2)]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  have h2 : c * trv z ≤ trv z / (2 * δ ^ 2) := by
    rw [div_eq_mul_one_div, mul_comm (trv z)]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) ht
  rw [hn]
  have e1 : -(z 0) ^ 2 / (8 * a ^ 2) = -(z 0 ^ 2 / (8 * a ^ 2)) := by ring
  have e2 : -trv z / (2 * δ ^ 2) = -(trv z / (2 * δ ^ 2)) := by ring
  rw [e1, e2]
  nlinarith

/-- **The witness tends to `0` at infinity.** -/
theorem tendsto_creationWitness [NeZero d] {a δ : ℝ} (ha : a ≠ 0) (hδ : δ ≠ 0) :
    Tendsto (creationWitness d a δ) (comap (fun x => ‖x‖) atTop) (𝓝 0) := by
  have hc : 0 < min (1 / (8 * a ^ 2)) (1 / (2 * δ ^ 2)) := lt_min (by positivity) (by positivity)
  set c := min (1 / (8 * a ^ 2)) (1 / (2 * δ ^ 2)) with hcdef
  have hG : Tendsto (fun z : Rd d => 8 * a ^ 2 * Real.exp (-c * ‖z‖ ^ 2))
      (comap (fun x => ‖x‖) atTop) (𝓝 0) := by
    have h2 : Tendsto (fun r : ℝ => Real.exp (-c * r ^ 2)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact Tendsto.const_mul_atTop_of_neg (by linarith) (tendsto_pow_atTop two_ne_zero)
    have h3 := (h2.comp (tendsto_comap (f := fun z : Rd d => ‖z‖))).const_mul
      (8 * a ^ 2)
    rw [mul_zero] at h3
    exact h3
  have hR : Tendsto (cwRidge (d := d) a δ) (comap (fun x => ‖x‖) atTop) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG (cwRidge_nonneg a δ)
      (cwRidge_le_gauss_min a δ)
  have h1 := tendsto_gB_comap_norm.comp (tendsto_sub_comap_norm (a • ebasis 0 : Rd d))
  have h2 := tendsto_gB_comap_norm.comp (tendsto_sub_comap_norm (-(a • ebasis 0) : Rd d))
  have := (h1.add h2).add hR
  simp only [add_zero] at this
  refine this.congr fun x => ?_
  simp only [Function.comp, sub_neg_eq_add]
  rw [creationWitness_eq_sum]

/-! ## The statement -/

/-- **`prop:creation-plane`(4), the Gaussian ladder.** For `q > 1` a positive sum of three
Gaussians `g` and an `n ≥ 1` have: the Gaussian record at variance `τ_n = (q^{2n} - 1)⁻¹` has
exactly one local maximum, the one at `q^{2n} τ_n` at least two; and some rung `k < n` of the
ladder of ratio `q` has exactly one local maximum while the next has at least two. (`k + 1` is the
least rung with two; rung `k` is a positive record that tends to `0`, so it attains its maximum.) -/
theorem creation_plane_4 [NeZero d] (hd : 2 ≤ d) {q : ℝ} (hq : 1 < q) :
    ∃ (g : Rd d → ℝ) (n : ℕ), 1 ≤ n ∧ (∀ x, 0 < g x) ∧
      (∃ (w : Fin 3 → ℝ) (m : Fin 3 → Rd d) (S : Fin 3 → Mat d), (∀ k, 0 < w k ∧ (S k).PosDef) ∧
        ∀ x, g x = ∑ k, w k * gaussDensityCov (S k) (x - m k)) ∧
      {x | IsLocalMax (mconvE (gaussVar d (q ^ (2 * n) - 1)⁻¹) g) x}.encard = 1 ∧
      2 ≤ {x | IsLocalMax (mconvE (gaussVar d (q ^ (2 * n) * (q ^ (2 * n) - 1)⁻¹)) g) x}.encard ∧
      ∃ k < n,
        {x | IsLocalMax (mconvE (gaussVar d (q ^ (2 * k) * (q ^ (2 * n) - 1)⁻¹)) g) x}.encard = 1 ∧
          2 ≤ {x | IsLocalMax
            (mconvE (gaussVar d (q ^ (2 * (k + 1)) * (q ^ (2 * n) - 1)⁻¹)) g) x}.encard := by
  -- clause (1) for `N(0, I)`
  have hac : gaussVar d 1 ≪ volume := by
    rw [gaussVar_eq_withDensity one_pos]; exact withDensity_absolutelyContinuous _ _
  obtain ⟨a, δ, ha, hδ, huniq, ⟨x1, y1, hxy, hx1, hy1⟩, -⟩ :=
    creation_plane_1 hd (gaussVar d 1) hac
  -- `n`
  set mm : ℝ := min 1 (δ ^ 2) with hmm
  have hmm0 : 0 < mm := lt_min one_pos (by positivity)
  have hq2 : 1 < q ^ 2 := by nlinarith
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 + 1 / mm) hq2
  set n := N + 1 with hn
  have hQ : 1 + 1 / mm < q ^ (2 * n) := by
    rw [pow_mul]
    exact hN.trans_le (pow_le_pow_right₀ hq2.le (by omega))
  set τ : ℝ := (q ^ (2 * n) - 1)⁻¹ with hτdef
  have hQ1 : 0 < q ^ (2 * n) - 1 := by
    have : 0 < 1 / mm := by positivity
    linarith
  have hτ : 0 < τ := inv_pos.2 hQ1
  have hτm : τ < mm := by
    rw [hτdef, inv_lt_comm₀ hQ1 hmm0]
    have : 1 / mm = mm⁻¹ := one_div mm
    linarith
  have hτ1 : τ < 1 := hτm.trans_le (min_le_left _ _)
  have hτδ : τ < δ ^ 2 := hτm.trans_le (min_le_right _ _)
  -- the three Gaussians
  obtain ⟨w0, w2, v0, v2, hw0p, hw2p, hv0p, hv2p, hrecL⟩ :=
    exists_gauss_record (d := d) ha hδ hτ hτ1 hτδ
  set p : Rd d := a • ebasis 0 with hp
  set W : Fin 3 → ℝ := ![w0, w0, w2] with hW
  set Mv : Fin 3 → Rd d := ![p, -p, 0] with hMv
  set S : Fin 3 → Mat d := ![Matrix.diagonal v0, Matrix.diagonal v0, Matrix.diagonal v2] with hS
  set g : Rd d → ℝ := fun x => ∑ k, W k * gaussDensityCov (S k) (x - Mv k) with hg
  have hg3 : ∀ x, g x = w0 * gConst v0 * gEv v0 (x - p) + w0 * gConst v0 * gEv v0 (x + p) +
      w2 * gConst v2 * gEv v2 x := by
    intro x
    simp only [hg, Fin.sum_univ_three, hW, hMv, hS, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_neg_eq_add, sub_zero,
      gaussDensityCov_diagonal hv0p, gaussDensityCov_diagonal hv2p]
    ring
  -- `g` is bounded and continuous
  have hgc : Continuous g := by
    have : g = fun x => w0 * gConst v0 * gEv v0 (x - p) + w0 * gConst v0 * gEv v0 (x + p) +
        w2 * gConst v2 * gEv v2 x := funext hg3
    rw [this]
    have := continuous_gEv v0; have := continuous_gEv v2
    fun_prop
  have hC0 := gConst_pos hv0p
  have hC2 := gConst_pos hv2p
  have hgb : ∀ z, |g z| ≤ w0 * gConst v0 + w0 * gConst v0 + w2 * gConst v2 := by
    intro z
    rw [hg3]
    have e1 := gEv_le_one hv0p (z - p); have e2 := gEv_le_one hv0p (z + p)
    have e3 := gEv_le_one hv2p z
    have f1 := gEv_pos v0 (z - p); have f2 := gEv_pos v0 (z + p); have f3 := gEv_pos v2 z
    rw [abs_le]; constructor
    · nlinarith [mul_pos (mul_pos hw0p hC0) f1, mul_pos (mul_pos hw0p hC0) f2,
        mul_pos (mul_pos hw2p hC2) f3]
    · have := mul_le_mul_of_nonneg_left e1 (mul_pos hw0p hC0).le
      have := mul_le_mul_of_nonneg_left e2 (mul_pos hw0p hC0).le
      have := mul_le_mul_of_nonneg_left e3 (mul_pos hw2p hC2).le
      linarith
  -- the record at `τ` is the witness
  have hrec : ∀ x, mconvE (gaussVar d τ) g x = creationWitness d a δ x := by
    intro x
    rw [← hrecL x]
    exact congrArg (fun f => mconvE (gaussVar d τ) f x) (funext hg3)
  have hrecF : mconvE (gaussVar d τ) g = creationWitness d a δ := funext hrec
  -- the record at `q^{2n}τ = τ + 1`
  have hQτ : q ^ (2 * n) * τ = τ + 1 := by
    rw [hτdef]; field_simp; ring
  have hrec1 : mconvE (gaussVar d (q ^ (2 * n) * τ)) g = mconvE (gaussVar d 1)
      (creationWitness d a δ) := by
    funext x
    rw [hQτ, gaussVar_add hτ.le zero_le_one, mconvE_conv_of_bdd _ _ hgc hgb, hrecF]
  -- the counts
  set c : ℕ → ℕ∞ := fun k =>
    {x | IsLocalMax (mconvE (gaussVar d (q ^ (2 * k) * τ)) g) x}.encard with hc
  have hc0 : {x | IsLocalMax (mconvE (gaussVar d τ) g) x}.encard = 1 := by
    rw [hrecF, Set.encard_eq_one]
    obtain ⟨x0, hx0, hx0u⟩ := huniq
    exact ⟨x0, Set.ext fun z => ⟨fun hz => hx0u z hz, fun hz => hz ▸ hx0⟩⟩
  have hcn : 2 ≤ c n := by
    simp only [hc]
    rw [hrec1, ← Set.encard_pair hxy]
    refine Set.encard_le_encard fun z hz => ?_
    rcases hz with rfl | rfl
    · exact hx1
    · exact hy1
  have hc0' : c 0 = 1 := by
    simp only [hc, mul_zero, pow_zero, one_mul]; exact hc0
  refine ⟨g, n, by omega, fun x => ?_, ⟨W, Mv, S, fun k => ?_, fun x => rfl⟩, hc0, hcn, ?_⟩
  · rw [hg3]
    have := gEv_pos v0 (x - p); have := gEv_pos v0 (x + p); have := gEv_pos v2 x
    positivity
  · fin_cases k
    · exact ⟨hw0p, Matrix.posDef_diagonal_iff.2 hv0p⟩
    · exact ⟨hw0p, Matrix.posDef_diagonal_iff.2 hv0p⟩
    · exact ⟨hw2p, Matrix.posDef_diagonal_iff.2 hv2p⟩
  · -- `k + 1` is the least rung with two local maxima
    have hex : ∃ j, 2 ≤ c j := ⟨n, hcn⟩
    set j := Nat.find hex with hjdef
    have hj2 : 2 ≤ c j := Nat.find_spec hex
    have hjn : j ≤ n := Nat.find_min' hex hcn
    have hj0 : j ≠ 0 := by
      intro h0
      have := hj2
      rw [h0, hc0'] at this
      norm_num at this
    obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := Nat.exists_eq_succ_of_ne_zero hj0
    have hk2 : ¬ 2 ≤ c k := Nat.find_min hex (by omega)
    -- rung `k` is the witness under `N(0, sI)`, positive and tending to `0`
    set s : ℝ := (q ^ (2 * k) - 1) * τ with hsdef
    have hs : 0 ≤ s := mul_nonneg (by
      have := one_le_pow₀ (M₀ := ℝ) (a := q) hq.le (n := 2 * k); linarith) hτ.le
    have hfc : Continuous (creationWitness d a δ) := by
      have : creationWitness d a δ = fun x =>
          gB (x - a • ebasis 0) + gB (x + a • ebasis 0) + cwRidge a δ x :=
        funext (creationWitness_eq_sum a δ)
      rw [this]
      have := continuous_cwRidge (d := d) a δ
      have := continuous_gB (d := d)
      fun_prop
    have hfpos : ∀ z, 0 < creationWitness d a δ z := fun z => by
      rw [creationWitness_eq_sum]
      have := gB_pos (z - a • ebasis 0); have := gB_pos (z + a • ebasis 0)
      have := cwRidge_nonneg (d := d) a δ z
      positivity
    have hfb : ∀ z, |creationWitness d a δ z| ≤ creationWitness d a δ 0 := fun z => by
      rw [abs_of_pos (hfpos z)]; exact creationWitness_le_zero ha hδ z
    have hreck : mconvE (gaussVar d (q ^ (2 * k) * τ)) g =
        mconvE (gaussVar d s) (creationWitness d a δ) := by
      funext x
      have e : q ^ (2 * k) * τ = τ + s := by rw [hsdef]; ring
      rw [e, gaussVar_add hτ.le hs, mconvE_conv_of_bdd _ _ hgc hgb, hrecF]
    have hck : 1 ≤ c k := by
      obtain ⟨x0, hx0⟩ := exists_isLocalMax_of_tendsto
        (continuous_mconvE_of_bdd (gaussVar d s) hfc hfb)
        (mconvE_pos_of_pos (gaussVar d s) hfc hfb hfpos 0)
        (tendsto_mconvE_of_tendsto (gaussVar d s) hfc hfb
          (tendsto_creationWitness (by linarith) hδ.ne'))
      simp only [hc]
      rw [hreck, Set.one_le_encard_iff_nonempty]
      exact ⟨x0, hx0⟩
    refine ⟨k, by omega, ?_, by rw [← hk]; exact hj2⟩
    have hle : c k ≤ 1 := by
      by_contra h
      push Not at h
      exact hk2 (Order.add_one_le_of_lt h)
    exact le_antisymm hle hck

/-! ## Any prescribed variance -/

/-- `x ↦ cx` carries `N(0, sI)` to `N(0, c²sI)`. -/
theorem gaussVar_map_smul {c s : ℝ} (hs : 0 ≤ s) :
    (gaussVar d s).map (fun x => c • x) = gaussVar d (c ^ 2 * s) := by
  haveI : IsProbabilityMeasure ((gaussVar d s).map fun x => c • x) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_map_smul, charFun_gaussVar hs, charFun_gaussVar (by positivity), norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]
  congr 3
  ring

/-- **The record of a dilated input** is the dilated record at the dilated variance. -/
theorem mconvE_gaussVar_comp_smul (g : Rd d → ℝ) {c s : ℝ} (hc : c ≠ 0) (hs : 0 ≤ s)
    (x : Rd d) :
    mconvE (gaussVar d s) (fun y => g (c • y)) x = mconvE (gaussVar d (c ^ 2 * s)) g (c • x) := by
  have hm := (Homeomorph.smulOfNeZero (α := Rd d) c hc).measurableEmbedding.integral_map
    (μ := gaussVar d s) (fun z => g (c • x - z))
  rw [ScaleSpace.mconvE_apply, ScaleSpace.mconvE_apply, ← gaussVar_map_smul hs]
  refine Eq.trans ?_ hm.symm
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  change g (c • (x - y)) = g (c • x - c • y)
  rw [smul_sub]

/-- A dilation of the variable keeps the count of local maxima. -/
theorem encard_isLocalMax_comp_smul (F : Rd d → ℝ) {c : ℝ} (hc : c ≠ 0) :
    {x | IsLocalMax (fun x => F (c • x)) x}.encard = {y | IsLocalMax F y}.encard := by
  set e := Homeomorph.smulOfNeZero (α := Rd d) c hc with he
  have hiff : ∀ x, IsLocalMax (fun x => F (c • x)) x ↔ IsLocalMax F (c • x) := by
    intro x
    change (∀ᶠ y in 𝓝 x, F (e y) ≤ F (e x)) ↔ ∀ᶠ z in 𝓝 (e x), F z ≤ F (e x)
    rw [← e.map_nhds_eq x, Filter.eventually_map]
  have hset : {x | IsLocalMax (fun x => F (c • x)) x} =
      (fun y => c⁻¹ • y) '' {y | IsLocalMax F y} := by
    ext x
    constructor
    · intro hx
      exact ⟨c • x, (hiff x).1 hx, inv_smul_smul₀ hc x⟩
    · rintro ⟨y, hy, rfl⟩
      refine (hiff _).2 ?_
      rwa [smul_inv_smul₀ hc]
  rw [hset]
  exact (smul_right_injective (Rd d) (inv_ne_zero hc)).encard_image _

/-- **`prop:creation-plane`(5), any variance.** For `q > 1` and `τ > 0` a positive bounded
continuous `g` has a Gaussian record at variance `τ` with exactly one local maximum and one at
`q²τ` with at least two: the rung of (4) with one maximum, moved to `τ` by a dilation. -/
theorem creation_plane_5 [NeZero d] (hd : 2 ≤ d) {q τ : ℝ} (hq : 1 < q) (hτ : 0 < τ) :
    ∃ g : Rd d → ℝ, (∀ x, 0 < g x) ∧
      {x | IsLocalMax (mconvE (gaussVar d τ) g) x}.encard = 1 ∧
      2 ≤ {x | IsLocalMax (mconvE (gaussVar d (q ^ 2 * τ)) g) x}.encard := by
  obtain ⟨g, n, hn, hgpos, -, -, -, k, -, h1, h2⟩ := creation_plane_4 hd hq
  have hQ1 : 0 < q ^ (2 * n) - 1 := by
    have : 1 < q ^ (2 * n) := one_lt_pow₀ hq (by omega)
    linarith
  set v : ℝ := q ^ (2 * k) * (q ^ (2 * n) - 1)⁻¹ with hv
  have hvp : 0 < v := mul_pos (pow_pos (by linarith) _) (inv_pos.2 hQ1)
  set c : ℝ := Real.sqrt (v / τ) with hcdef
  have hc : 0 < c := Real.sqrt_pos.2 (div_pos hvp hτ)
  have hc2 : c ^ 2 = v / τ := Real.sq_sqrt (div_pos hvp hτ).le
  refine ⟨fun y => g (c • y), fun y => hgpos _, ?_, ?_⟩
  · have e : mconvE (gaussVar d τ) (fun y => g (c • y)) =
        fun x => mconvE (gaussVar d v) g (c • x) := by
      funext x
      rw [mconvE_gaussVar_comp_smul g hc.ne' hτ.le x, hc2, div_mul_cancel₀ _ hτ.ne']
    rw [e, encard_isLocalMax_comp_smul _ hc.ne']
    exact h1
  · have e : mconvE (gaussVar d (q ^ 2 * τ)) (fun y => g (c • y)) =
        fun x => mconvE (gaussVar d (q ^ (2 * (k + 1)) * (q ^ (2 * n) - 1)⁻¹)) g (c • x) := by
      funext x
      have hscale : v / τ * (q ^ 2 * τ) = q ^ (2 * (k + 1)) * (q ^ (2 * n) - 1)⁻¹ := by
        rw [hv, show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
        field_simp
      rw [mconvE_gaussVar_comp_smul g hc.ne' (by positivity) x, hc2, hscale]
    rw [e, encard_isLocalMax_comp_smul _ hc.ne']
    exact h2

end Pyramids
