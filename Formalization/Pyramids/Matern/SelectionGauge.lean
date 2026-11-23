/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.SelectionStage
import Pyramids.LineAppendix.KnotOrbits

/-!
# `thm:selection-stratum-two`(2): every octave stage

Blueprint: `blueprint/src/parts/04-matern.tex`, `thm:selection-stratum-two`. Phase 5, wave 3b (on
the VM).

* **Every stage.** For `t > 0` let `q^n t ∈ [1, q)`; by (1) the stage there is `L_{√τ}`, so the
  stage at `t`, its dilate by `q^{-n}`, is a resolvent and has the principle. So (1) applies at
  every `t > 0`: `μ̂_t(ω) = e^{-F¹_q(χ(t)|ω|)}` with `χ(t) > 0`.
* **`χ` is read off the transform** at a unit vector, `F¹_q` being strictly increasing on
  `[0,∞)` (`rep_unique`). Covariance at `q^n` gives `χ(q^n t) = q^nχ(t)`. If `χ(t) ≤ χ(s)` with
  `s < t`, the transform of `μ_{s,t}` is `e^{F(χ(s)r) - F(χ(t)r)} ≥ 1`, so it is `1` and
  `μ_{s,t} = δ₀`, against (ND). Continuity: `e^{-F(χ(t))} = Re μ̂_t(e)` is continuous by (I2),
  and the order of `F` transfers it to `χ`. Surjectivity: the intermediate values of `χ` on
  `[1, q]` and the dilations.
* **The family.** The transform of `μ_{s,t}` is the quotient of the kernels' (I1), which is that
  of the Matérn pyramid at `c = 1` read at `χ(s), χ(t)`. With `S := χ⁻¹(λχ)` the transforms of
  `D_λ μ_{s,t}` and `μ_{S s, S t}` agree.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace ComplexOrder

variable {d : ℕ}

/-! ## The exponent at `c = 1` -/

/-- Two scales with one transform at a unit vector are equal. -/
theorem rep_unique {q : ℝ} (hq : 1 < q) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : Real.exp (-maternExponent q 1 a) = Real.exp (-maternExponent q 1 b)) : a = b := by
  have h2 := neg_injective (Real.exp_injective h)
  exact (maternExponent_strictMonoOn hq one_pos).injOn ha hb h2

theorem maternExponent_one_le {q : ℝ} (hq : 1 < q) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    maternExponent q 1 a ≤ maternExponent q 1 b :=
  (maternExponent_strictMonoOn hq one_pos).monotoneOn ha (ha.trans hab) hab

/-! ## Every stage has the principle -/

/-- **Every stage.** If the stages at `t ∈ [1,q)` have the principle, so does every `μ_{t,qt}`,
`t > 0`. -/
theorem principle_all_of_octave (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure (Rd d))
    (hiso : IsIsotropicFamily μ) (hcov : IsCovariantAt μ q fun t => q * t)
    (hP : ∀ t : ℝ, 1 ≤ t → t < q → HasImplicitEulerPrinciple (μ t (q * t))) {t : ℝ} (ht : 0 < t) :
    HasImplicitEulerPrinciple (μ t (q * t)) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨n, hn, -⟩ := existsUnique_zpow_mul_mem_Ico hq ht
  have ht0 : 0 < q ^ n * t := mul_pos (zpow_pos hq0 n) ht
  obtain ⟨τ, hτ, hrep⟩ := (selection_stratum_two_1 hd hq μ hiso hcov ht0).1 (hP _ hn.1 hn.2)
  have h := selection_stratum_two_1_ladder hq μ hiso hcov ht0 hτ hrep (-n)
  rw [← mul_assoc, ← zpow_add₀ hq0.ne', neg_add_cancel, zpow_zero, one_mul, ← mul_assoc,
    ← zpow_add₀ hq0.ne', show -n + 1 + n = 1 by ring, zpow_one] at h
  rw [h]
  haveI := (charFun_maternStep (d := d) (Real.sqrt τ * q ^ (-n)) 0).1
  exact stage_lemma_1_helmholtz (sq_nonneg _) _ fun ω => (charFun_maternStep _ ω).2

/-- The kernel at every `t > 0` is `e^{-F¹_q(c|ω|)}` with `c > 0`. -/
theorem exists_scale (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure (Rd d))
    (hiso : IsIsotropicFamily μ) (hcov : IsCovariantAt μ q fun t => q * t)
    (hP : ∀ t : ℝ, 1 ≤ t → t < q → HasImplicitEulerPrinciple (μ t (q * t))) {t : ℝ} (ht : 0 < t) :
    ∃ c : ℝ, 0 < c ∧ ∀ ω : Rd d,
      charFun (μ 0 t) ω = ((Real.exp (-maternExponent q 1 (c * ‖ω‖)) : ℝ) : ℂ) := by
  obtain ⟨τ, hτ, hrep⟩ := (selection_stratum_two_1 hd hq μ hiso hcov ht).1
    (principle_all_of_octave hd hq μ hiso hcov hP ht)
  exact ⟨Real.sqrt τ, Real.sqrt_pos.2 hτ, fun ω => by
    rw [hrep, logSeries_eq_maternExponent hτ.le]⟩

/-! ## The gauge -/

section Gauge

variable (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure (Rd d))
  (hiso : IsIsotropicFamily μ) (hcov : IsCovariantAt μ q fun t => q * t)
  (hP : ∀ t : ℝ, 1 ≤ t → t < q → HasImplicitEulerPrinciple (μ t (q * t)))

include hd hq hiso hcov hP in
/-- **The gauge** `χ(t)`, the scale of the kernel at `t > 0` (`0` elsewhere). -/
noncomputable def selGauge : ℝ → ℝ := fun t =>
  if h : 0 < t then (exists_scale hd hq μ hiso hcov hP h).choose else 0

include hd hq hiso hcov hP in
theorem selGauge_pos {t : ℝ} (ht : 0 < t) : 0 < selGauge hd hq μ hiso hcov hP t := by
  rw [selGauge, dif_pos ht]
  exact (exists_scale hd hq μ hiso hcov hP ht).choose_spec.1

include hd hq hiso hcov hP in
theorem selGauge_rep {t : ℝ} (ht : 0 < t) (ω : Rd d) :
    charFun (μ 0 t) ω =
      ((Real.exp (-maternExponent q 1 (selGauge hd hq μ hiso hcov hP t * ‖ω‖)) : ℝ) : ℂ) := by
  rw [selGauge, dif_pos ht]
  exact (exists_scale hd hq μ hiso hcov hP ht).choose_spec.2 ω

include hd hq hiso hcov hP in
/-- `χ(q^n t) = q^n χ(t)`. -/
theorem selGauge_zpow (n : ℤ) {t : ℝ} (ht : 0 < t) :
    selGauge hd hq μ hiso hcov hP (q ^ n * t) = q ^ n * selGauge hd hq μ hiso hcov hP t := by
  have hq0 : 0 < q := by linarith
  have hqn : 0 < q ^ n := zpow_pos hq0 n
  obtain ⟨e, he⟩ := exists_unit_Rd hd
  have h := congrArg (fun m => charFun m e) (kernel_zpow_of_cov hq hcov n t ht.le)
  rw [charFun_map_smul, selGauge_rep hd hq μ hiso hcov hP (mul_pos hqn ht),
    selGauge_rep hd hq μ hiso hcov hP ht, norm_smul, he, Real.norm_of_nonneg hqn.le] at h
  have h2 := Complex.ofReal_injective h
  rw [mul_one, mul_one, mul_comm _ (q ^ n)] at h2
  exact rep_unique hq (selGauge_pos hd hq μ hiso hcov hP (mul_pos hqn ht)).le
    (mul_nonneg hqn.le (selGauge_pos hd hq μ hiso hcov hP ht).le) h2

include hd hq hiso hcov hP in
theorem selGauge_strictMonoOn : StrictMonoOn (selGauge hd hq μ hiso hcov hP) (Ioi 0) := by
  intro s hs t ht hst
  have hs0 : 0 < s := hs
  have ht0 : 0 < t := ht
  set χ := selGauge hd hq μ hiso hcov hP with hχ
  by_contra hle
  rw [not_lt] at hle
  haveI := hiso.1.1.isProbability s t hs0.le hst.le
  refine hiso.1.2 s t hs0.le hst (eq_dirac_of_charFun_one fun ω => ?_)
  have hk := charFun_kernel_mul_gen hiso.1.1 hs0.le hst.le ω
  rw [selGauge_rep hd hq μ hiso hcov hP ht0, selGauge_rep hd hq μ hiso hcov hP hs0, ← hχ] at hk
  set x := maternExponent q 1 (χ s * ‖ω‖) - maternExponent q 1 (χ t * ‖ω‖) with hx
  have hx0 : 0 ≤ x := sub_nonneg.2 (maternExponent_one_le hq
    (mul_nonneg (selGauge_pos hd hq μ hiso hcov hP ht0).le (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hle (norm_nonneg _)))
  have hc : charFun (μ s t) ω = ((Real.exp x : ℝ) : ℂ) := by
    have hne : ((Real.exp (-maternExponent q 1 (χ s * ‖ω‖)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    refine mul_right_cancel₀ hne (hk.symm.trans ?_)
    rw [← Complex.ofReal_mul, ← Real.exp_add, hx]
    congr 2
    ring
  have hn := norm_charFun_le_one (μ := μ s t) ω
  rw [hc, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff] at hn
  rw [hc, le_antisymm hn hx0, Real.exp_zero, Complex.ofReal_one]

include hd hq hiso hcov hP in
theorem selGauge_continuousOn : ContinuousOn (selGauge hd hq μ hiso hcov hP) (Ioi 0) := by
  set χ := selGauge hd hq μ hiso hcov hP with hχ
  set F := maternExponent q 1 with hF
  have hFmono := maternExponent_strictMonoOn hq one_pos
  obtain ⟨e, he⟩ := exists_unit_Rd hd
  -- `k(t) := Re μ̂_t(e) = e^{-F(χ(t))}` is continuous
  have hk : ContinuousOn (fun t => (charFun (μ 0 t) e).re) (Ioi 0) := by
    have h := hiso.1.1.continuous e
    have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Ioi 0) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
      fun t ht => ⟨le_rfl, le_of_lt ht⟩
    exact Complex.continuous_re.comp_continuousOn
      (h.comp (continuous_const.prodMk continuous_id).continuousOn hmap)
  have hkχ : ∀ t ∈ Ioi (0 : ℝ), (charFun (μ 0 t) e).re = Real.exp (-F (χ t)) := fun t ht => by
    rw [selGauge_rep hd hq μ hiso hcov hP ht, he, mul_one, Complex.ofReal_re]
  intro t₀ ht₀
  have hpos : ∀ᶠ t in 𝓝[Ioi 0] t₀, t ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
  have hlim := hk t₀ ht₀
  have ha := (selGauge_pos hd hq μ hiso hcov hP ht₀).le
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · -- the lower bound
    rcases lt_or_ge a' 0 with h0 | h0
    · filter_upwards [hpos] with t ht
      exact h0.trans (selGauge_pos hd hq μ hiso hcov hP ht)
    · have hlt : Real.exp (-F (χ t₀)) < Real.exp (-F a') :=
        Real.exp_lt_exp.2 (neg_lt_neg (hFmono h0 ha ha'))
      rw [← hkχ t₀ ht₀] at hlt
      filter_upwards [hpos, (tendsto_order.1 hlim).2 _ hlt] with t ht hkt
      rw [hkχ t ht] at hkt
      by_contra hle
      rw [not_lt] at hle
      have := maternExponent_one_le hq (selGauge_pos hd hq μ hiso hcov hP ht).le hle
      have := Real.exp_le_exp.2 (neg_le_neg this)
      linarith
  · -- the upper bound
    have h0 : 0 ≤ a' := ha.trans ha'.le
    have hlt : Real.exp (-F a') < Real.exp (-F (χ t₀)) :=
      Real.exp_lt_exp.2 (neg_lt_neg (hFmono ha h0 ha'))
    rw [← hkχ t₀ ht₀] at hlt
    filter_upwards [hpos, (tendsto_order.1 hlim).1 _ hlt] with t ht hkt
    rw [hkχ t ht] at hkt
    by_contra hle
    rw [not_lt] at hle
    have := maternExponent_one_le hq h0 hle
    have := Real.exp_le_exp.2 (neg_le_neg this)
    linarith

include hd hq hiso hcov hP in
theorem selGauge_surjOn : SurjOn (selGauge hd hq μ hiso hcov hP) (Ioi 0) (Ioi 0) := by
  set χ := selGauge hd hq μ hiso hcov hP with hχ
  have hq0 : 0 < q := by linarith
  intro y hy
  have hy0 : 0 < y := hy
  have h1 := selGauge_pos hd hq μ hiso hcov hP one_pos
  obtain ⟨m, hm, -⟩ := existsUnique_zpow_mul_mem_Ico hq (div_pos hy0 h1)
  -- `q^m y ∈ [χ 1, χ q]`
  have hχq : χ q = q * χ 1 := by
    have h := selGauge_zpow hd hq μ hiso hcov hP 1 one_pos
    simpa using h
  have hIcc : Icc (χ 1) (χ q) ⊆ χ '' Icc 1 q := by
    refine intermediate_value_Icc hq.le ?_
    exact (selGauge_continuousOn hd hq μ hiso hcov hP).mono fun t ht =>
      lt_of_lt_of_le one_pos ht.1
  have hmem : q ^ m * y ∈ Icc (χ 1) (χ q) := by
    rw [hχq]
    have h := hm
    rw [mem_Ico, mul_div_assoc', le_div_iff₀ h1, div_lt_iff₀ h1, one_mul] at h
    exact ⟨h.1, h.2.le⟩
  obtain ⟨s, hs, hχs⟩ := hIcc hmem
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs.1
  refine ⟨q ^ (-m) * s, mul_pos (zpow_pos hq0 _) hs0, ?_⟩
  rw [hχ, selGauge_zpow hd hq μ hiso hcov hP (-m) hs0, ← hχ, hχs, ← mul_assoc, ← zpow_add₀ hq0.ne',
    neg_add_cancel, zpow_zero, one_mul]

include hd hq hiso hcov hP in
theorem selGauge_mem : IsInGaugeGroup q (selGauge hd hq μ hiso hcov hP) :=
  ⟨selGauge_strictMonoOn hd hq μ hiso hcov hP,
    fun t ht => selGauge_pos hd hq μ hiso hcov hP ht,
    selGauge_surjOn hd hq μ hiso hcov hP,
    selGauge_continuousOn hd hq μ hiso hcov hP,
    fun t ht => by simpa using selGauge_zpow hd hq μ hiso hcov hP 1 ht⟩

end Gauge

/-! ## Families read in a gauge -/

/-- `extendByZero χ` is nonnegative and monotone on `[0,∞)` for `χ ∈ 𝒢_q`. -/
theorem extendByZero_nonneg {q : ℝ} {χ : ℝ → ℝ} (hχ : IsInGaugeGroup q χ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ extendByZero χ t := by
  rw [extendByZero]
  split_ifs with h
  · exact le_rfl
  · exact (hχ.mapsTo (mem_Ioi.2 (lt_of_le_of_ne ht (Ne.symm h)))).le

theorem extendByZero_mono {q : ℝ} {χ : ℝ → ℝ} (hχ : IsInGaugeGroup q χ) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : extendByZero χ s ≤ extendByZero χ t := by
  rcases hs.eq_or_lt with rfl | hs0
  · rw [show extendByZero χ 0 = 0 by simp [extendByZero]]
    exact extendByZero_nonneg hχ (le_refl 0 |>.trans hst)
  · have ht0 : 0 < t := hs0.trans_le hst
    rw [extendByZero, if_neg hs0.ne', extendByZero, if_neg ht0.ne']
    exact hχ.strictMonoOn.monotoneOn (mem_Ioi.2 hs0) (mem_Ioi.2 ht0) hst

/-- **The steps of a family whose kernels are read in a gauge.** If `μ̂_t = e^{-F(χ(t)|ω|)}` for
`t > 0`, then `μ̂_{s,t} = e^{-(F(χ(t)|ω|) - F(χ(s)|ω|))}` for `0 ≤ s ≤ t`. -/
theorem charFun_step_of_gauge {q : ℝ} {μ : ℝ → ℝ → Measure (Rd d)} (hμ : IsLawHemigroup μ)
    {χ : ℝ → ℝ}
    (hrep : ∀ t : ℝ, 0 < t → ∀ ω : Rd d,
      charFun (μ 0 t) ω = ((Real.exp (-maternExponent q 1 (χ t * ‖ω‖)) : ℝ) : ℂ))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ω : Rd d) :
    charFun (μ s t) ω = ((Real.exp (-(maternExponent q 1 (extendByZero χ t * ‖ω‖) -
      maternExponent q 1 (extendByZero χ s * ‖ω‖))) : ℝ) : ℂ) := by
  have hrep' : ∀ u : ℝ, 0 ≤ u → charFun (μ 0 u) ω =
      ((Real.exp (-maternExponent q 1 (extendByZero χ u * ‖ω‖)) : ℝ) : ℂ) := by
    intro u hu
    rcases hu.eq_or_lt with rfl | hu0
    · rw [hμ.diag 0 le_rfl, charFun_dirac]
      simp [extendByZero, maternExponent_zero]
    · rw [hrep u hu0, extendByZero, if_neg hu0.ne']
  have hk := charFun_kernel_mul_gen hμ hs hst ω
  rw [hrep' t (hs.trans hst), hrep' s hs] at hk
  have hne : ((Real.exp (-maternExponent q 1 (extendByZero χ s * ‖ω‖)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  refine mul_right_cancel₀ hne (hk.symm.trans ?_)
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  ring_nf

/-- **`S_λ := χ⁻¹(λχ)`**, extended by `0`. -/
noncomputable def gaugeShift (χ : ℝ → ℝ) (lam : ℝ) : ℝ → ℝ :=
  extendByZero fun s => Function.invFunOn χ (Ioi 0) (lam * χ s)

theorem gaugeShift_spec {q : ℝ} {χ : ℝ → ℝ} (hχ : IsInGaugeGroup q χ) {lam : ℝ} (hlam : 0 < lam)
    {s : ℝ} (hs : 0 < s) :
    0 < gaugeShift χ lam s ∧ χ (gaugeShift χ lam s) = lam * χ s := by
  have hm : lam * χ s ∈ Ioi (0 : ℝ) := mul_pos hlam (hχ.mapsTo (mem_Ioi.2 hs))
  rw [gaugeShift, extendByZero, if_neg hs.ne']
  exact ⟨Function.invFunOn_mem (hχ.surjOn hm), Function.invFunOn_eq (hχ.surjOn hm)⟩

theorem gaugeShift_zero (χ : ℝ → ℝ) (lam : ℝ) : gaugeShift χ lam 0 = 0 := by
  simp [gaugeShift, extendByZero]

theorem extendByZero_gaugeShift {q : ℝ} {χ : ℝ → ℝ} (hχ : IsInGaugeGroup q χ) {lam : ℝ}
    (hlam : 0 < lam) {s : ℝ} (hs : 0 ≤ s) :
    extendByZero χ (gaugeShift χ lam s) = lam * extendByZero χ s := by
  rcases hs.eq_or_lt with rfl | hs0
  · simp [gaugeShift_zero, extendByZero]
  · obtain ⟨h1, h2⟩ := gaugeShift_spec hχ hlam hs0
    rw [extendByZero, if_neg h1.ne', h2, extendByZero, if_neg hs0.ne']

theorem gaugeShift_isIncreasingBijection {q : ℝ} {χ : ℝ → ℝ} (hχ : IsInGaugeGroup q χ) {lam : ℝ}
    (hlam : 0 < lam) : IsIncreasingBijection (gaugeShift χ lam) := by
  refine ⟨fun s hs => ?_, fun s hs t ht hst => ?_, fun t ht => ?_⟩
  · rcases (mem_Ici.1 hs).eq_or_lt with rfl | hs0
    · rw [gaugeShift_zero]; exact mem_Ici.2 le_rfl
    · exact mem_Ici.2 (gaugeShift_spec hχ hlam hs0).1.le
  · have ht0 : 0 < t := lt_of_le_of_lt (mem_Ici.1 hs) hst
    obtain ⟨ht1, ht2⟩ := gaugeShift_spec hχ hlam ht0
    rcases (mem_Ici.1 hs).eq_or_lt with rfl | hs0
    · rw [gaugeShift_zero]; exact ht1
    · obtain ⟨hs1, hs2⟩ := gaugeShift_spec hχ hlam hs0
      by_contra hle
      rw [not_lt] at hle
      have h := hχ.strictMonoOn.monotoneOn (mem_Ioi.2 ht1) (mem_Ioi.2 hs1) hle
      rw [hs2, ht2] at h
      have := hχ.strictMonoOn (mem_Ioi.2 hs0) (mem_Ioi.2 ht0) hst
      nlinarith
  · rcases (mem_Ici.1 ht).eq_or_lt with rfl | ht0
    · exact ⟨0, mem_Ici.2 le_rfl, gaugeShift_zero χ lam⟩
    · have hm : χ t / lam ∈ Ioi (0 : ℝ) := div_pos (hχ.mapsTo (mem_Ioi.2 ht0)) hlam
      set s := Function.invFunOn χ (Ioi 0) (χ t / lam) with hsdef
      have hs0 : 0 < s := Function.invFunOn_mem (hχ.surjOn hm)
      have hχs : χ s = χ t / lam := Function.invFunOn_eq (hχ.surjOn hm)
      refine ⟨s, mem_Ici.2 hs0.le, ?_⟩
      obtain ⟨h1, h2⟩ := gaugeShift_spec hχ hlam hs0
      rw [hχs, mul_div_cancel₀ _ hlam.ne'] at h2
      exact hχ.strictMonoOn.injOn (mem_Ioi.2 h1) (mem_Ioi.2 ht0) h2

/-! ## `thm:selection-stratum-two`(2) -/

/-- **`thm:selection-stratum-two`(2), every octave stage.** If `μ_{t,qt}` has the principle for all
`t ∈ [1,q)`, there is `χ ∈ 𝒢_q` with `Ψ_t = F¹_q(χ(t)·)`; the family is the Matérn pyramid
(`c = 1`) read in the gauge `χ`, and it is fully covariant with `S_λ = χ⁻¹(λχ)`. -/
theorem selection_stratum_two_2 (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure (Rd d))
    (hiso : IsIsotropicFamily μ) (hcov : IsCovariantAt μ q fun t => q * t)
    (hP : ∀ t : ℝ, 1 ≤ t → t < q → HasImplicitEulerPrinciple (μ t (q * t))) :
    ∃ χ : ℝ → ℝ, IsInGaugeGroup q χ ∧
      (∀ t : ℝ, 0 < t → ∀ ω : Rd d,
        charFun (μ 0 t) ω = ((Real.exp (-maternExponent q 1 (χ t * ‖ω‖)) : ℝ) : ℂ)) ∧
      (∀ ν : ℝ → ℝ → Measure (Rd d), IsMaternPyramid q 1 ν → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        μ s t = ν (extendByZero χ s) (extendByZero χ t)) ∧
      ∀ lam : ℝ, 0 < lam → ∃ S : ℝ → ℝ, IsCovariantAt μ lam S ∧
        ∀ s : ℝ, 0 ≤ s → extendByZero χ (S s) = lam * extendByZero χ s := by
  set χ := selGauge hd hq μ hiso hcov hP with hχdef
  have hχ : IsInGaugeGroup q χ := selGauge_mem hd hq μ hiso hcov hP
  have hrep := fun t (ht : 0 < t) => selGauge_rep hd hq μ hiso hcov hP ht
  have hstep := fun s t (hs : 0 ≤ s) (hst : s ≤ t) =>
    charFun_step_of_gauge (q := q) hiso.1.1 (χ := χ) hrep hs hst
  refine ⟨χ, hχ, hrep, fun ν hν s t hs hst => ?_, fun lam hlam => ?_⟩
  · have h0 := extendByZero_nonneg hχ hs
    have h1 := extendByZero_mono hχ hs hst
    haveI := hiso.1.1.isProbability s t hs hst
    haveI := (hν _ _ h0 h1).1
    exact Measure.ext_of_charFun (funext fun ω => by
      rw [hstep s t hs hst ω, charFun_maternPyramid hν h0 h1])
  · set S := gaugeShift χ lam with hS
    have hSb := gaugeShift_isIncreasingBijection hχ hlam
    refine ⟨S, ⟨hSb, fun s t hs hst => ?_⟩, fun s hs => extendByZero_gaugeShift hχ hlam hs⟩
    have hSs : 0 ≤ S s := hSb.mapsTo (mem_Ici.2 hs)
    have hSst : S s ≤ S t := by
      rcases hst.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact (hSb.strictMonoOn (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst)) hlt).le
    haveI := hiso.1.1.isProbability s t hs hst
    haveI := hiso.1.1.isProbability _ _ hSs hSst
    haveI : IsProbabilityMeasure ((μ s t).map fun x => lam • x) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_map_smul, hstep s t hs hst, hstep _ _ hSs hSst,
      extendByZero_gaugeShift hχ hlam hs, extendByZero_gaugeShift hχ hlam (hs.trans hst),
      norm_smul, Real.norm_of_nonneg hlam.le]
    ring_nf

/-! ## `thm:selection-stratum-two`(2), the converse for every family (fidelity review, R22) -/

/-- `extendByZero χ` is a gauge of `[0,∞)` for `χ ∈ 𝒢_q`. -/
theorem isGauge_extendByZero {q : ℝ} {χ : ℝ → ℝ} (hχ : IsInGaugeGroup q χ) :
    IsGauge (extendByZero χ) := by
  refine ⟨by simp [extendByZero], fun s hs t ht hst => ?_, fun u hu => ?_⟩
  · have ht0 : 0 < t := lt_of_le_of_lt (mem_Ici.1 hs) hst
    rcases (mem_Ici.1 hs).eq_or_lt with rfl | hs0
    · simpa [extendByZero, ht0.ne'] using hχ.mapsTo (mem_Ioi.2 ht0)
    · simp only [extendByZero, if_neg hs0.ne', if_neg ht0.ne']
      exact hχ.strictMonoOn (mem_Ioi.2 hs0) (mem_Ioi.2 ht0) hst
  · rcases (mem_Ici.1 hu).eq_or_lt with rfl | hu0
    · exact ⟨0, mem_Ici.2 le_rfl, by simp [extendByZero]⟩
    · obtain ⟨s, hs, hχs⟩ := hχ.surjOn (mem_Ioi.2 hu0)
      refine ⟨s, mem_Ici.2 (mem_Ioi.1 hs).le, ?_⟩
      rw [extendByZero, if_neg (mem_Ioi.1 hs).ne', hχs]

/-- **`thm:selection-stratum-two`(2), the converse, for every family.** An isotropic `q`-covariant
family in the canonical discrete gauge whose exponents are `Ψ_t = F¹_q(χ(t)·)`, `χ ∈ 𝒢_q`, has the
principle at every octave stage `μ_{t,qt}`, `t > 0`. The proof reads (I1) and (I2) only. -/
theorem selection_stratum_two_2_converse_family {q : ℝ} (hq : 1 < q)
    (μ : ℝ → ℝ → Measure (Rd d)) (hiso : IsIsotropicFamily μ)
    (_hcov : IsCovariantAt μ q fun t => q * t) {χ : ℝ → ℝ} (hχ : IsInGaugeGroup q χ)
    (hrep : ∀ t : ℝ, 0 < t → ∀ ω : Rd d,
      charFun (μ 0 t) ω = ((Real.exp (-maternExponent q 1 (χ t * ‖ω‖)) : ℝ) : ℂ)) :
    ∀ t : ℝ, 0 < t → HasImplicitEulerPrinciple (μ t (q * t)) := by
  intro t ht
  have hq0 : 0 < q := by linarith
  have hχt : 0 < χ t := hχ.mapsTo (mem_Ioi.2 ht)
  have hle : t ≤ q * t := le_mul_of_one_le_left ht.le hq.le
  haveI := hiso.1.1.isProbability t (q * t) ht.le hle
  refine stage_lemma_1_helmholtz (sq_nonneg (χ t)) _ fun ω => ?_
  rw [charFun_step_of_gauge hiso.1.1 hrep ht.le hle ω]
  simp only [extendByZero, if_neg ht.ne', if_neg (mul_pos hq0 ht).ne']
  rw [hχ.equivariant t ht, mul_assoc, maternExponent_mul_q hq one_pos,
    add_sub_cancel_right, one_pow, one_mul, mul_pow, inv_one_add_eq_exp (by positivity)]

/-- **The Matérn pyramid read in a gauge is such a family.** For `χ ∈ 𝒢_q` and the Matérn pyramid
`ν` with `c = 1`, the relabelled family `(ν_{χ̃ s, χ̃ t})`, `χ̃ := extendByZero χ`, is an
isotropic `q`-covariant family in the canonical discrete gauge with the exponents
`Ψ_t = F¹_q(χ(t)·)`, so `selection_stratum_two_2_converse_family` applies to it. -/
theorem maternPyramid_gauge_family (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) {χ : ℝ → ℝ}
    (hχ : IsInGaugeGroup q χ) (ν : ℝ → ℝ → Measure (Rd d)) (hν : IsMaternPyramid q 1 ν) :
    IsIsotropicFamily (relabel ν (extendByZero χ)) ∧
      IsCovariantAt (relabel ν (extendByZero χ)) q (fun t => q * t) ∧
      ∀ t : ℝ, 0 < t → ∀ ω : Rd d, charFun (relabel ν (extendByZero χ) 0 t) ω =
        ((Real.exp (-maternExponent q 1 (χ t * ‖ω‖)) : ℝ) : ℂ) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hiso, hcov, -⟩ := matern_pyramid_1_family hd hq one_pos ν hν
  have hg := isGauge_extendByZero hχ
  have hgc := isGauge_continuousOn hg
  set g := extendByZero χ with hgdef
  have h0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ g s := fun s hs => extendByZero_nonneg hχ hs
  have hle : ∀ s t : ℝ, 0 ≤ s → s ≤ t → g s ≤ g t := fun s t hs hst => extendByZero_mono hχ hs hst
  have hlt : ∀ s t : ℝ, 0 ≤ s → s < t → g s < g t := fun s t hs hst =>
    hg.2.1 (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst.le)) hst
  have hgq : ∀ s : ℝ, 0 ≤ s → g (q * s) = q * g s := by
    intro s hs
    rcases hs.eq_or_lt with rfl | hs0
    · simp [hgdef, extendByZero]
    · rw [hgdef, extendByZero, if_neg (mul_pos hq0 hs0).ne', extendByZero, if_neg hs0.ne',
        hχ.equivariant s hs0]
  refine ⟨⟨⟨⟨fun s t hs hst => hiso.1.1.isProbability _ _ (h0 s hs) (hle s t hs hst),
      fun t ht => hiso.1.1.diag _ (h0 t ht),
      fun r s t hr hrs hst => hiso.1.1.cascade _ _ _ (h0 r hr) (hle r s hr hrs)
        (hle s t (hr.trans hrs) hst), fun ω => ?_⟩,
      fun s t hs hst => hiso.1.2 _ _ (h0 s hs) (hlt s t hs hst)⟩,
      fun s t hs hst => hiso.2 _ _ (h0 s hs) (hle s t hs hst)⟩,
    ⟨⟨fun t ht => mul_nonneg hq0.le ht, fun u _ v _ huv => mul_lt_mul_of_pos_left huv hq0,
      fun t ht => ⟨t / q, div_nonneg ht hq0.le, mul_div_cancel₀ t hq0.ne'⟩⟩,
      fun s t hs hst => ?_⟩, fun t ht ω => ?_⟩
  · have hc : ContinuousOn (fun p : ℝ × ℝ => (g p.1, g p.2)) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
      (hgc.comp continuousOn_fst fun p hp => hp.1).prodMk
        (hgc.comp continuousOn_snd fun p hp => hp.1.trans hp.2)
    exact (hiso.1.1.continuous ω).comp hc fun p hp => ⟨h0 _ hp.1, hle _ _ hp.1 hp.2⟩
  · change (ν (g s) (g t)).map (fun x => q • x) = ν (g (q * s)) (g (q * t))
    rw [(hcov q hq0).2 _ _ (h0 s hs) (hle s t hs hst), hgq s hs, hgq t (hs.trans hst)]
  · have hχt := hχ.mapsTo (mem_Ioi.2 ht)
    have hg0 : g 0 = 0 := by simp [hgdef, extendByZero]
    have hgt : g t = χ t := by simp [hgdef, extendByZero, ht.ne']
    change charFun (ν (g 0) (g t)) ω = _
    rw [hg0, hgt, charFun_maternPyramid hν le_rfl (le_of_lt hχt), zero_mul, maternExponent_zero,
      sub_zero]

/-- **`thm:selection-stratum-two`(2), the converse, at the Matérn pyramid read in a gauge.** The
family of `maternPyramid_gauge_family` has the principle at every octave stage. -/
theorem selection_stratum_two_2_converse_gauge (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) {χ : ℝ → ℝ}
    (hχ : IsInGaugeGroup q χ) (ν : ℝ → ℝ → Measure (Rd d)) (hν : IsMaternPyramid q 1 ν) :
    ∀ t : ℝ, 0 < t → HasImplicitEulerPrinciple (relabel ν (extendByZero χ) t (q * t)) := by
  obtain ⟨hiso, hcov, hrep⟩ := maternPyramid_gauge_family hd hq hχ ν hν
  exact selection_stratum_two_2_converse_family hq _ hiso hcov hχ hrep

end Pyramids
