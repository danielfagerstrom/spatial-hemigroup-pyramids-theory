/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.PolarReading
import AffineHemigroup.OriginLowerBound

/-!
# Ledger A42: the linear image of an infinitely divisible law (Sato, Prop. 11.10, p. 65)

Ledger entry A42 of `blueprint/AXIOMS.md`, with its page transcription in
`blueprint/AXIOMS-verbatim.md`; interface node `thm:cited-A42`
(`blueprint/src/parts/02-cited-facts.tex`).

Source: Sato, *Lévy Processes and Infinitely Divisible Distributions*, Proposition 11.10, printed
p. 65, formulas (11.8)–(11.10), printed for a Lévy process `{X_t}` and read for its law at time 1.
The statement is the skeleton's, unchanged, as the phase-4 review checked it against the page.

**This file declares no axiom** (review round 3, batch C, 2026-11-23). The author admitted A42 as a
Lean axiom on 2026-11-13; it is now a theorem, by the change of variables `y = Ux` in the
Lévy–Khintchine formula (8.1), the vocabulary of `thm:cited-A39` (`HasTriplet`):

* `⟪w, Ux⟫ = ⟪Uᵀw, x⟫`, so the transform of `U_*μ` at `w` is the transform of `μ` at `Uᵀw`
  (`charFun_map_toEuclideanLin`), and `⟪w, UAUᵀw⟫ = ⟪Uᵀw, AUᵀw⟫`;
* the integrand of (8.1) vanishes at `0`, so restricting `U_*ν` to `ℝⁿ ∖ {0}` changes no integral,
  and the integral against `U_*ν` is the integral of the composed integrand against `ν`;
* the two compensators differ by `i⟪w, Ux⟫(1_E(Ux) - 1_D(x))`, which is `ν`-integrable: it
  vanishes unless exactly one of `|x| ≤ 1`, `|Ux| ≤ 1` holds, and is bounded by
  `(K³ + 1) min(|x|², 1)` with `K` the norm of `U` (`norm_imageCorrection_le`); its integral is
  the correction in `γ_U`.

The infinite divisibility of `U_*μ` is the image of the `n`-th roots. The proof reads the definition
of a generating triplet only, not the existence, uniqueness or converse of A39, so
`#print axioms cited_A42` is Lean core; every spender of `cited_A42` loses that name.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Metric Complex Set
open scoped ENNReal RealInnerProductSpace Matrix

variable {d n : ℕ}

/-! ## The linear map of a rectangular matrix -/

theorem continuous_toEuclideanLin (U : Matrix (Fin n) (Fin d) ℝ) :
    Continuous (Matrix.toEuclideanLin U) :=
  (Matrix.toEuclideanLin U).continuous_of_finiteDimensional

theorem measurable_toEuclideanLin (U : Matrix (Fin n) (Fin d) ℝ) :
    Measurable (Matrix.toEuclideanLin U) :=
  (continuous_toEuclideanLin U).measurable

/-- `⟪w, Ux⟫ = ⟪Uᵀw, x⟫`. -/
theorem inner_toEuclideanLin (U : Matrix (Fin n) (Fin d) ℝ) (w : Rd n) (x : Rd d) :
    ⟪w, Matrix.toEuclideanLin U x⟫ = ⟪Matrix.toEuclideanLin U.transpose w, x⟫ := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

/-- `|Ux| ≤ K|x|` for some `K ≥ 0`. -/
theorem exists_norm_toEuclideanLin_le (U : Matrix (Fin n) (Fin d) ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Rd d, ‖Matrix.toEuclideanLin U x‖ ≤ K * ‖x‖ := by
  refine ⟨‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin U)‖, norm_nonneg _, fun x => ?_⟩
  have h := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin U)).le_opNorm x
  simpa using h

/-- **The transform of a linear image**: `\widehat{U_*μ}(w) = μ̂(Uᵀw)`. -/
theorem charFun_map_toEuclideanLin (μ : Measure (Rd d)) (U : Matrix (Fin n) (Fin d) ℝ)
    (w : Rd n) :
    charFun (μ.map (Matrix.toEuclideanLin U)) w
      = charFun μ (Matrix.toEuclideanLin U.transpose w) := by
  rw [charFun_apply, charFun_apply, integral_map (measurable_toEuclideanLin U).aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  congr 1
  ext x
  rw [real_inner_comm w, inner_toEuclideanLin, real_inner_comm x]

/-- **A linear image of an infinitely divisible finite measure is infinitely divisible**: the image
of an `k`-th root is a `k`-th root of the image. -/
theorem isInfinitelyDivisible_map_toEuclideanLin {μ : Measure (Rd d)} [IsFiniteMeasure μ]
    (hμ : IsInfinitelyDivisible μ) (U : Matrix (Fin n) (Fin d) ℝ) :
    IsInfinitelyDivisible (μ.map (Matrix.toEuclideanLin U)) := by
  intro k hk
  obtain ⟨a, ha, hak⟩ := hμ k hk
  refine ⟨a.map (Matrix.toEuclideanLin U),
    Measure.isProbabilityMeasure_map (measurable_toEuclideanLin U).aemeasurable, ?_⟩
  haveI := ScaleSpace.isFiniteMeasure_convPow_Rd (a.map (Matrix.toEuclideanLin U)) k
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_convPow, charFun_map_toEuclideanLin, ← hak, charFun_map_toEuclideanLin,
    charFun_convPow]

/-! ## The correction integrand of `γ_U` -/

/-- `min(a², 1) ≤ (K² + 1) min(b², 1)` when `0 ≤ a ≤ Kb`. -/
theorem min_sq_one_le_of_le_mul {a b K : ℝ} (ha : 0 ≤ a) (h : a ≤ K * b) :
    min (a ^ 2) 1 ≤ (K ^ 2 + 1) * min (b ^ 2) 1 := by
  rcases le_total (b ^ 2) 1 with hb1 | hb1
  · rw [min_eq_left hb1]
    calc min (a ^ 2) 1 ≤ a ^ 2 := min_le_left _ _
      _ ≤ (K * b) ^ 2 := pow_le_pow_left₀ ha h 2
      _ = K ^ 2 * b ^ 2 := by ring
      _ ≤ (K ^ 2 + 1) * b ^ 2 := by nlinarith [sq_nonneg b]
  · rw [min_eq_right hb1]
    calc min (a ^ 2) 1 ≤ 1 := min_le_right _ _
      _ ≤ (K ^ 2 + 1) * 1 := by nlinarith [sq_nonneg K]

/-- **The correction integrand** `x ↦ (1_E(Ux) - 1_D(x)) Ux` of `γ_U` in (11.10), `D`, `E` the
closed unit balls of `ℝ^d` and `ℝⁿ`. -/
noncomputable def imageCorrection (U : Matrix (Fin n) (Fin d) ℝ) (x : Rd d) : Rd n :=
  ((closedBall (0 : Rd n) 1).indicator (fun _ => (1 : ℝ)) (Matrix.toEuclideanLin U x)
    - (closedBall (0 : Rd d) 1).indicator (fun _ => (1 : ℝ)) x) • Matrix.toEuclideanLin U x

theorem measurable_imageCorrection (U : Matrix (Fin n) (Fin d) ℝ) :
    Measurable (imageCorrection U) := by
  unfold imageCorrection
  exact (((measurable_const.indicator measurableSet_closedBall).comp
    (measurable_toEuclideanLin U)).sub (measurable_const.indicator measurableSet_closedBall)).smul
    (measurable_toEuclideanLin U)

/-- The correction vanishes unless exactly one of `|x| ≤ 1`, `|Ux| ≤ 1` holds, and is bounded by
`(K³ + 1) min(|x|², 1)`: by `|Ux| ≤ 1` where `|x| > 1`, and where `|x| ≤ 1 < |Ux| ≤ K|x|` by
`K|x| ≤ (K|x|)³ ≤ K³|x|²`. -/
theorem norm_imageCorrection_le (U : Matrix (Fin n) (Fin d) ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hL : ∀ x : Rd d, ‖Matrix.toEuclideanLin U x‖ ≤ K * ‖x‖) (x : Rd d) :
    ‖imageCorrection U x‖ ≤ (K ^ 3 + 1) * min (‖x‖ ^ 2) 1 := by
  have hy := hL x
  have hK3 : 0 ≤ K ^ 3 := pow_nonneg hK 3
  unfold imageCorrection
  by_cases hx : x ∈ closedBall (0 : Rd d) 1 <;>
    by_cases hyE : Matrix.toEuclideanLin U x ∈ closedBall (0 : Rd n) 1
  · simp only [indicator_of_mem hx, indicator_of_mem hyE, sub_self, zero_smul, norm_zero]
    positivity
  · have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    have hy1 : 1 < ‖Matrix.toEuclideanLin U x‖ := by simpa using hyE
    simp only [indicator_of_mem hx, indicator_of_notMem hyE, zero_sub, norm_smul, norm_neg,
      norm_one, one_mul]
    rw [min_eq_left (by nlinarith [norm_nonneg x])]
    have h1 : 1 < K * ‖x‖ := lt_of_lt_of_le hy1 hy
    have hKx : 0 ≤ K * ‖x‖ := by positivity
    have ht : 1 ≤ (K * ‖x‖) ^ 2 := by nlinarith
    have h2 : K * ‖x‖ ≤ (K * ‖x‖) ^ 3 := by
      calc K * ‖x‖ = K * ‖x‖ * 1 := (mul_one _).symm
        _ ≤ K * ‖x‖ * (K * ‖x‖) ^ 2 := mul_le_mul_of_nonneg_left ht hKx
        _ = (K * ‖x‖) ^ 3 := by ring
    have h3 : (K * ‖x‖) ^ 3 ≤ K ^ 3 * ‖x‖ ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (norm_nonneg x) hx1 (by norm_num)) hK3
    have h4 : K ^ 3 * ‖x‖ ^ 2 ≤ (K ^ 3 + 1) * ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
    linarith
  · have hx1 : 1 < ‖x‖ := by simpa using hx
    have hy1 : ‖Matrix.toEuclideanLin U x‖ ≤ 1 := by simpa using hyE
    simp only [indicator_of_notMem hx, indicator_of_mem hyE, sub_zero, one_smul]
    rw [min_eq_right (by nlinarith)]
    linarith
  · simp only [indicator_of_notMem hx, indicator_of_notMem hyE, sub_self, zero_smul, norm_zero]
    positivity

/-- `min(|x|², 1)` is `ν`-integrable, by (8.2). -/
theorem integrable_min_sq_one (T : LevyTriplet d) :
    Integrable (fun x : Rd d => min (‖x‖ ^ 2) 1) T.ν := by
  refine ⟨(by fun_prop : Measurable fun x : Rd d => min (‖x‖ ^ 2) 1).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_))
    (lt_top_iff_ne_top.mpr T.ν_integrable)
  rw [Real.enorm_eq_ofReal (by positivity)]

/-- **The correction integrand is `ν`-integrable.** -/
theorem integrable_imageCorrection (T : LevyTriplet d) (U : Matrix (Fin n) (Fin d) ℝ) :
    Integrable (imageCorrection U) T.ν := by
  obtain ⟨K, hK, hL⟩ := exists_norm_toEuclideanLin_le U
  exact Integrable.mono' ((integrable_min_sq_one T).const_mul (K ^ 3 + 1))
    (measurable_imageCorrection U).aestronglyMeasurable
    (ae_of_all _ fun x => norm_imageCorrection_le U hK hL x)

/-! ## The triplet of the image -/

/-- **The triplet `(UAUᵀ, [νU⁻¹]_{ℝⁿ∖{0}}, γ_U)` of `U_*μ`** (11.8)–(11.10). -/
noncomputable def tripletImage (T : LevyTriplet d) (U : Matrix (Fin n) (Fin d) ℝ) :
    LevyTriplet n where
  A := U * T.A * U.transpose
  ν := (T.ν.map (Matrix.toEuclideanLin U)).restrict {0}ᶜ
  γ := Matrix.toEuclideanLin U T.γ + ∫ x, imageCorrection U x ∂T.ν
  A_posSemidef := by
    have h := T.A_posSemidef.mul_mul_conjTranspose_same U
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  ν_zero := by
    rw [Measure.restrict_apply (measurableSet_singleton 0), inter_compl_self, measure_empty]
  ν_integrable := by
    obtain ⟨K, -, hL⟩ := exists_norm_toEuclideanLin_le U
    refine ne_top_of_le_ne_top
      (b := ENNReal.ofReal (K ^ 2 + 1) * ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂T.ν)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top T.ν_integrable) ?_
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (min (‖y‖ ^ 2) 1) ∂(T.ν.map (Matrix.toEuclideanLin U)) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ x, ENNReal.ofReal (min (‖Matrix.toEuclideanLin U x‖ ^ 2) 1) ∂T.ν :=
          lintegral_map (by fun_prop) (measurable_toEuclideanLin U)
      _ ≤ ∫⁻ x, ENNReal.ofReal (K ^ 2 + 1) * ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂T.ν := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal
            (min_sq_one_le_of_le_mul (norm_nonneg _) (hL x))
      _ = ENNReal.ofReal (K ^ 2 + 1) * ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂T.ν :=
          lintegral_const_mul _ (by fun_prop)

/-- **The exponent of the image triplet** is the exponent of `T` at `Uᵀw`: the change of variables
`y = Ux`, with the compensators' difference moved into the drift. -/
theorem lkExponent_tripletImage (T : LevyTriplet d) (U : Matrix (Fin n) (Fin d) ℝ) (w : Rd n) :
    (tripletImage T U).lkExponent w = T.lkExponent (Matrix.toEuclideanLin U.transpose w) := by
  classical
  rw [LevyTriplet.lkExponent_eq, LevyTriplet.lkExponent_eq]
  have hquad : quad (tripletImage T U).A w = quad T.A (Matrix.toEuclideanLin U.transpose w) := by
    rw [quad_eq_dotProduct, quad_eq_dotProduct]
    change WithLp.ofLp w ⬝ᵥ (U * T.A * U.transpose) *ᵥ WithLp.ofLp w
      = (U.transpose *ᵥ WithLp.ofLp w) ⬝ᵥ T.A *ᵥ (U.transpose *ᵥ WithLp.ofLp w)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose]
  have hc := integrable_imageCorrection T U
  have hγ : ⟪(tripletImage T U).γ, w⟫
      = ⟪T.γ, Matrix.toEuclideanLin U.transpose w⟫ + ⟪w, ∫ x, imageCorrection U x ∂T.ν⟫ := by
    change ⟪Matrix.toEuclideanLin U T.γ + ∫ x, imageCorrection U x ∂T.ν, w⟫ = _
    rw [inner_add_left, real_inner_comm w (Matrix.toEuclideanLin U T.γ), inner_toEuclideanLin,
      real_inner_comm, real_inner_comm w]
  have hpt : ∀ x : Rd d, lkIntegrand w (Matrix.toEuclideanLin U x)
      = lkIntegrand (Matrix.toEuclideanLin U.transpose w) x
        - I * ((⟪w, imageCorrection U x⟫ : ℝ) : ℂ) := by
    intro x
    have hθ : ⟪Matrix.toEuclideanLin U.transpose w, x⟫ = ⟪w, Matrix.toEuclideanLin U x⟫ :=
      (inner_toEuclideanLin U w x).symm
    simp only [lkIntegrand, imageCorrection, real_inner_smul_right, hθ, indicator_apply,
      Pi.one_apply]
    split_ifs <;> push_cast <;> ring
  have hint : ∫ y, lkIntegrand w y ∂(tripletImage T U).ν
      = ∫ x, lkIntegrand (Matrix.toEuclideanLin U.transpose w) x ∂T.ν
        - I * ((⟪w, ∫ x, imageCorrection U x ∂T.ν⟫ : ℝ) : ℂ) := by
    change ∫ y in {0}ᶜ, lkIntegrand w y ∂(T.ν.map (Matrix.toEuclideanLin U)) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        rw [show y = 0 by simpa using hy]; simp [lkIntegrand]),
      integral_map (measurable_toEuclideanLin U).aemeasurable
        (measurable_lkIntegrand w).aestronglyMeasurable]
    simp_rw [hpt]
    rw [integral_sub (T.integrable_lkIntegrand _) ?_, integral_const_mul, integral_complex_ofReal,
      integral_inner hc w]
    exact ((hc.const_inner w).ofReal (𝕜 := ℂ)).const_mul I
  rw [hquad, hγ, hint]
  push_cast
  ring

/-- **`thm:cited-A42`, ledger A42** (Sato, Prop. 11.10, p. 65). For an `n × d` matrix `U`, `U_*μ`
is infinitely divisible with triplet `A_U = UAUᵀ`, `ν_U = [νU⁻¹]` restricted to `ℝⁿ ∖ {0}`, and
`γ_U = Uγ + ∫ Ux (1_E(Ux) - 1_D(x)) ν(dx)`, the integrand being `ν`-integrable. Admitted as an
axiom by the author on 2026-11-13; a theorem, Lean core, since review round 3 (batch C,
2026-11-23). -/
theorem cited_A42 (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsInfinitelyDivisible μ) (T : LevyTriplet d) (hT : HasTriplet μ T)
    (U : Matrix (Fin n) (Fin d) ℝ) :
    IsInfinitelyDivisible (μ.map (Matrix.toEuclideanLin U)) ∧
      Integrable (fun x : Rd d =>
        ((Metric.closedBall (0 : Rd n) 1).indicator (fun _ => (1 : ℝ)) (Matrix.toEuclideanLin U x)
          - (Metric.closedBall (0 : Rd d) 1).indicator (fun _ => (1 : ℝ)) x) •
            Matrix.toEuclideanLin U x) T.ν ∧
      ∃ T' : LevyTriplet n, HasTriplet (μ.map (Matrix.toEuclideanLin U)) T' ∧
        T'.A = U * T.A * U.transpose ∧
        T'.ν = (T.ν.map (Matrix.toEuclideanLin U)).restrict {0}ᶜ ∧
        T'.γ = Matrix.toEuclideanLin U T.γ + ∫ x : Rd d,
          ((Metric.closedBall (0 : Rd n) 1).indicator (fun _ => (1 : ℝ))
              (Matrix.toEuclideanLin U x)
            - (Metric.closedBall (0 : Rd d) 1).indicator (fun _ => (1 : ℝ)) x) •
              Matrix.toEuclideanLin U x ∂T.ν := by
  refine ⟨isInfinitelyDivisible_map_toEuclideanLin hμ U, integrable_imageCorrection T U,
    tripletImage T U, fun w => ?_, rfl, rfl, rfl⟩
  rw [charFun_map_toEuclideanLin, hT, lkExponent_tripletImage]

end Pyramids
