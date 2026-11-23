/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.FamilyDilations

/-!
# `lem:discrete-covariance-levy`: discrete covariance in Lévy coordinates

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `lem:discrete-covariance-levy`, chapter 3. Wave 2c:
the three declarations moved here from `PyramidsSkeleton.Ch03Pyramid`, their statements unchanged.

## The route

The printed one.

* **Covariance and the exponent condition.** `D_q μ_t = μ_{qt}` at the pairs `(0, t)` is
  `Ψ_{qt}(ω) = Ψ_t(qω)`; conversely the transforms of the steps are `e^{-(Ψ_t - Ψ_s)}`
  (`family_structure_data`), which the condition carries from `(s, t)` at `qω` to `(qs, qt)` at `ω`.
* **The exponent condition and the data.** `Ψ_t(q ·)` is the exponent of the data
  `(q²A_t, D_q ν_t)` (`SymLevyData.dilate`, a change of variables), and two data of one law agree
  (`isSymData_unique`, ledger A39(ii)). At `t = 0` both exponents vanish.
* **The residual** is `D_{q⁻¹} μ_{t,qt}`, infinitely divisible as the dilate of an infinitely
  divisible law (`isInfinitelyDivisible_map_smul`).
* **The octave** determines the kernels through `μ_{q^k t} = D_{q^k} μ_t`, and the kernels the steps
  through `μ̂_{s,t} = μ̂_t/μ̂_s`.
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (convPow)
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## Dilation of symmetric Lévy data -/

/-- `⟨ω, c²Aω⟩ = ⟨cω, A(cω)⟩`. -/
theorem quad_sq_smul (A : Mat d) (c : ℝ) (ω : Rd d) : quad (c ^ 2 • A) ω = quad A (c • ω) := by
  simp only [quad, lin, map_smul, FunLike.coe_smul, Pi.smul_apply, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real]
  ring

/-- **The dilate `(c²A, D_c ν)` of symmetric Lévy data**, `c ≠ 0`: `D_c ν` puts no mass at `0`, is
symmetric, and `∫ (1 ∧ |y|²) D_cν(dy) ≤ max(c², 1) ∫ (1 ∧ |x|²) ν(dx)`. -/
noncomputable def SymLevyData.dilate (D : SymLevyData d) {c : ℝ} (hc : c ≠ 0) : SymLevyData d where
  A := c ^ 2 • D.A
  ν := D.ν.map (fun x => c • x)
  A_posSemidef := D.A_posSemidef.smul (sq_nonneg c)
  ν_zero := by
    rw [Measure.map_apply (continuous_const_smul c).measurable (measurableSet_singleton 0)]
    have e : (fun x : Rd d => c • x) ⁻¹' {0} = {0} := by
      ext x
      simp [hc]
    rw [e, D.ν_zero]
  ν_integrable := by
    have hm : Measurable fun x : Rd d => ENNReal.ofReal (min (‖x‖ ^ 2) 1) :=
      (by fun_prop : Continuous fun x : Rd d => min (‖x‖ ^ 2) 1).measurable.ennreal_ofReal
    rw [lintegral_map hm (continuous_const_smul c).measurable]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top D.ν_integrable)
      (b := ENNReal.ofReal (max (c ^ 2) 1) * ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂D.ν) ?_
    rw [← lintegral_const_mul _ hm]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_right _ _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rcases le_total (‖x‖ ^ 2) 1 with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    · rw [min_eq_right h, mul_one]
      exact (min_le_right _ _).trans (le_max_right _ _)
  ν_symm := by
    rw [Measure.map_map measurable_neg (continuous_const_smul c).measurable]
    have e : ((fun x : Rd d => -x) ∘ fun x => c • x) = (fun x => c • x) ∘ fun x => -x := by
      funext x
      simp [smul_neg]
    rw [e, ← Measure.map_map (continuous_const_smul c).measurable measurable_neg, D.ν_symm]

/-- **The exponent of the dilate** is `Ψ(c ·)`: the change of variables `y = cx`. -/
theorem SymLevyData.dilate_exponent (D : SymLevyData d) {c : ℝ} (hc : c ≠ 0) (ω : Rd d) :
    (D.dilate hc).exponent ω = D.exponent (c • ω) := by
  change quad (c ^ 2 • D.A) ω + ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂(D.ν.map fun x => c • x) =
    quad D.A (c • ω) + ∫ x, (1 - Real.cos ⟪c • ω, x⟫) ∂D.ν
  rw [quad_sq_smul, integral_map (continuous_const_smul c).measurable.aemeasurable
    (by fun_prop : Continuous fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).aestronglyMeasurable]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [real_inner_smul_left, real_inner_smul_right]

/-! ## Dilates of infinitely divisible laws -/

theorem convPow_map_smul (ν : Measure (Rd d)) [IsFiniteMeasure ν] (c : ℝ) :
    ∀ n : ℕ, convPow (ν.map fun x => c • x) n = (convPow ν n).map fun x => c • x
  | 0 => by simp [convPow, Measure.map_dirac]
  | n + 1 => by
    haveI := ScaleSpace.isFiniteMeasure_convPow_Rd ν n
    rw [convPow, convPow, convPow_map_smul ν c n]
    have e : (fun x : Rd d => c • x) = ⇑(c • ContinuousLinearMap.id ℝ (Rd d)) := by
      funext x
      simp
    rw [e, Measure.map_conv_continuousLinearMap]

/-- **The dilate of an infinitely divisible law is infinitely divisible**: the dilate of an `n`-th
convolution root is an `n`-th convolution root of the dilate. -/
theorem isInfinitelyDivisible_map_smul {m : Measure (Rd d)} (h : IsInfinitelyDivisible m)
    (c : ℝ) : IsInfinitelyDivisible (m.map fun x => c • x) := by
  intro n hn
  obtain ⟨ν, hν, hνn⟩ := h n hn
  exact ⟨ν.map fun x => c • x,
    Measure.isProbabilityMeasure_map (continuous_const_smul c).measurable.aemeasurable,
    by rw [convPow_map_smul, hνn]⟩

/-! ## `lem:discrete-covariance-levy` -/

/-- **`lem:discrete-covariance-levy`, the equivalences.** `q`-covariance with `S_q t = qt` iff
`Ψ_{qt}(ω) = Ψ_t(qω)` for all `t ≥ 0`, `ω`, iff `A_{qt} = q² A_t`, `ν_{qt} = D_q ν_t` for
`t > 0`. -/
theorem discrete_covariance_levy (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) (D : ℝ → SymLevyData d)
    (hD : ∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t)) {q : ℝ} (hq : 1 < q) :
    (IsCovariantAt μ q (fun t => q * t) ↔
        ∀ t : ℝ, 0 ≤ t → ∀ ω : Rd d, (D (q * t)).exponent ω = (D t).exponent (q • ω)) ∧
      ((∀ t : ℝ, 0 ≤ t → ∀ ω : Rd d, (D (q * t)).exponent ω = (D t).exponent (q • ω)) ↔
        ∀ t : ℝ, 0 < t → (D (q * t)).A = q ^ 2 • (D t).A ∧
          (D (q * t)).ν = (D t).ν.map (fun x => q • x)) := by
  have hq0 : 0 < q := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  have hdata := family_structure_data hd μ hμ D hD
  refine ⟨⟨fun hcov t ht ω => ?_, fun hE => ?_⟩, ⟨fun hE t ht => ?_, fun hAν t ht ω => ?_⟩⟩
  · -- covariance at the pairs `(0, t)`
    have hk : (μ 0 t).map (fun x => q • x) = μ 0 (q * t) := cov_kernel hcov ht
    have h1 := congrArg (fun m => charFun m ω) hk
    rw [charFun_map_smul, hD t ht, hD (q * t) (by positivity)] at h1
    have h2 := Real.exp_injective (Complex.ofReal_injective h1)
    linarith
  · -- the exponent condition gives covariance at every pair
    refine ⟨⟨fun t ht => mul_nonneg hq0.le ht, fun u _ v _ huv => mul_lt_mul_of_pos_left huv hq0,
      fun t ht => ⟨t / q, div_nonneg ht hq0.le, mul_div_cancel₀ t hqne⟩⟩, fun s t hs hst => ?_⟩
    have hqs : 0 ≤ q * s := by positivity
    have hqst : q * s ≤ q * t := mul_le_mul_of_nonneg_left hst hq0.le
    haveI := hμ.1.isProbability s t hs hst
    haveI := hμ.1.isProbability (q * s) (q * t) hqs hqst
    haveI : IsProbabilityMeasure ((μ s t).map fun x => q • x) :=
      Measure.isProbabilityMeasure_map (continuous_const_smul q).measurable.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    change charFun ((μ s t).map fun x => q • x) ω = charFun (μ (q * s) (q * t)) ω
    rw [charFun_map_smul, (hdata.2 s t hs hst).1, (hdata.2 (q * s) (q * t) hqs hqst).1,
      hE t (hs.trans hst), hE s hs]
  · -- the exponent condition gives the data, by uniqueness (A39(ii))
    have hqt : 0 ≤ q * t := by positivity
    haveI := hμ.1.isProbability 0 (q * t) le_rfl hqt
    have h1 : IsSymData (μ 0 (q * t)) ((D t).dilate hqne) := fun ω => by
      rw [SymLevyData.dilate_exponent, ← hE t ht.le ω]
      exact hD _ hqt ω
    exact isSymData_unique (hD _ hqt) h1
  · -- the data give the exponent condition
    rcases ht.eq_or_lt with h0 | h0
    · subst h0
      have hz : ∀ ω : Rd d, (D 0).exponent ω = 0 := fun ω => by
        rw [hdata.1 0 le_rfl ω, hμ.1.diag 0 le_rfl, charFun_dirac]
        simp
      rw [mul_zero, hz, hz]
    · obtain ⟨hA, hν⟩ := hAν t h0
      rw [← SymLevyData.dilate_exponent (D t) hqne]
      change pairExponent (D (q * t)).A (D (q * t)).ν ω =
        pairExponent (q ^ 2 • (D t).A) ((D t).ν.map fun x => q • x) ω
      rw [hA, hν]

/-- **`lem:discrete-covariance-levy`, "then".** Every kernel is semi-selfdecomposable with
span `q`. -/
theorem discrete_covariance_levy_semi (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) {q : ℝ} (hq : 1 < q) (hcov : IsCovariantAt μ q (fun t => q * t)) :
    ∀ t : ℝ, 0 ≤ t → IsSemiSelfDecomposableWithSpan q (μ 0 t) := by
  intro t ht
  have hq0 : 0 < q := by linarith
  have hqt : t ≤ q * t := by nlinarith
  haveI := hμ.1.isProbability t (q * t) ht hqt
  refine ⟨hq, (μ t (q * t)).map (fun x => q⁻¹ • x),
    ⟨Measure.isProbabilityMeasure_map (continuous_const_smul _).measurable.aemeasurable,
      fun z => ?_⟩,
    isInfinitelyDivisible_map_smul ((family_structure_id hd μ hμ t (q * t) ht hqt).1) q⁻¹⟩
  rw [charFun_map_smul]
  have hk : (μ 0 t).map (fun x => q • x) = μ 0 (q * t) := cov_kernel hcov ht
  have h1 := charFun_kernel_mul_gen hμ.1 ht hqt (q⁻¹ • z)
  rw [← hk, charFun_map_smul, smul_smul, mul_inv_cancel₀ hq0.ne', one_smul] at h1
  rw [h1, mul_comm]

/-- **`lem:discrete-covariance-levy`, the octave determines the family.** Two such families whose
kernels `μ_t` agree for `t ∈ [1, q)` agree at every pair. -/
theorem discrete_covariance_levy_determined (hd : 1 ≤ d) (μ μ' : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) (hμ' : IsSymmetricFamily μ') {q : ℝ} (hq : 1 < q)
    (hcov : IsCovariantAt μ q (fun t => q * t)) (hcov' : IsCovariantAt μ' q (fun t => q * t))
    (heq : ∀ t ∈ Ico (1 : ℝ) q, μ 0 t = μ' 0 t) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t := by
  have hq0 : 0 < q := by linarith
  -- covariance iterated on the kernels
  have hiter : ∀ ν : ℝ → ℝ → Measure (Rd d), IsCovariantAt ν q (fun t => q * t) →
      ∀ k : ℕ, ∀ u : ℝ, 0 ≤ u → ν 0 (q ^ k * u) = (ν 0 u).map fun x => (q ^ k) • x := by
    intro ν hν k
    induction k with
    | zero =>
      intro u _
      simp
    | succ k ih =>
      intro u hu
      have hk : (ν 0 (q ^ k * u)).map (fun x => q • x) = ν 0 (q * (q ^ k * u)) :=
        cov_kernel hν (by positivity)
      rw [show q ^ (k + 1) * u = q * (q ^ k * u) by ring, ← hk, ih u hu,
        Measure.map_map (continuous_const_smul _).measurable (continuous_const_smul _).measurable]
      congr 1
      funext x
      simp only [Function.comp_apply, smul_smul, pow_succ]
      ring_nf
  have hinj : ∀ c : ℝ, c ≠ 0 → ∀ m m' : Measure (Rd d),
      m.map (fun x => c • x) = m'.map (fun x => c • x) → m = m' := by
    intro c hc m m' h
    have h2 := congrArg (fun n : Measure (Rd d) => n.map fun x => c⁻¹ • x) h
    simp only [Measure.map_map (continuous_const_smul _).measurable
      (continuous_const_smul _).measurable] at h2
    have e : ((fun x : Rd d => c⁻¹ • x) ∘ fun x => c • x) = id := by
      funext x
      simp [smul_smul, inv_mul_cancel₀ hc]
    rwa [e, Measure.map_id, Measure.map_id] at h2
  have hker : ∀ t : ℝ, 0 ≤ t → μ 0 t = μ' 0 t := by
    intro t ht
    rcases ht.eq_or_lt with h0 | h0
    · subst h0
      rw [hμ.1.diag 0 le_rfl, hμ'.1.diag 0 le_rfl]
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow h0 hq
    have hqn : 0 < q ^ n := zpow_pos hq0 n
    set t' := t / q ^ n with ht'def
    have ht' : t' ∈ Ico (1 : ℝ) q := by
      refine ⟨(le_div_iff₀ hqn).2 (by linarith), (div_lt_iff₀ hqn).2 ?_⟩
      rw [mul_comm, ← zpow_add_one₀ hq0.ne']
      exact hn2
    have htt : t = q ^ n * t' := (mul_div_cancel₀ t hqn.ne').symm
    have ht'0 : 0 ≤ t' := le_trans zero_le_one ht'.1
    rcases le_or_gt 0 n with hn | hn
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [htt, zpow_natCast, hiter μ hcov k t' ht'0, hiter μ' hcov' k t' ht'0, heq t' ht']
    · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hn.le
      have hqk : (0 : ℝ) < q ^ k := pow_pos hq0 k
      have ht2 : t' = q ^ k * t := by
        rw [ht'def, hk, zpow_neg, zpow_natCast]
        field_simp
      apply hinj (q ^ k) hqk.ne'
      rw [← hiter μ hcov k t ht, ← hiter μ' hcov' k t ht, ← ht2, heq t' ht']
  intro s t hs hst
  haveI := hμ.1.isProbability s t hs hst
  haveI := hμ'.1.isProbability s t hs hst
  have hK := kernelOrder_rd hd hμ
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  have h1 := charFun_kernel_mul_gen hμ.1 hs hst ω
  have h2 := charFun_kernel_mul_gen hμ'.1 hs hst ω
  rw [hker t (hs.trans hst), hker s hs] at h1
  have hne : charFun (μ' 0 s) ω ≠ 0 := by
    rw [← hker s hs]
    exact (hK.pos s hs ω).ne'
  exact mul_right_cancel₀ hne (h1.symm.trans h2)

end Pyramids
