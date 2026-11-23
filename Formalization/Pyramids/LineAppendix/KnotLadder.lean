/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.SurfacePair
import Pyramids.LineAppendix.QCinRepr

/-!
# `lem:knot-exponent-ladder`: the ladder of a knot exponent

Blueprint: `blueprint/src/parts/A1-line.tex`, `lem:knot-exponent-ladder`. Wave 3a: the four
declarations moved here from `PyramidsSkeleton.ChA1Line`, unchanged in name.
`knot_exponent_ladder_3` no longer takes the hypothesis `IsKnotExponent q Ψ1`, which its proof
does not use: membership of the orbit already makes `Ψ_1` the family's exponent (2026-11-14, a
strengthening).

## The route

* (1): `∑_{m < M} φ(q^{-m-1}ω) = Ψ_1(ω) - Ψ_1(q^{-M}ω)`, with nonnegative terms (`φ ∈ ND_s`) and
  `Ψ_1(q^{-M}ω) → Ψ_1(0) = 0` (`Ψ_1 ∈ ND_s` is continuous). The ladder's law at `n = 0` has the
  transform `e^{-φ}`, so the ladder fixes `φ`, and the series fixes `Ψ_1`.
* (2): for a family, `μ_{1,q}` has the exponent `Ψ_q - Ψ_1 = Ψ_1(q ·) - Ψ_1`
  (`charFun_octaveStep`, `lineExponent_cov`); conversely `Ψ_q - Ψ_1 = φ` gives
  `Ψ_1 = ∑ φ(q^{-m} ·)` by `lem:step-field-determines-family`(1), the knot exponent by (1).
* (3): the folded data of `μ_1` and `μ_q` are `(a(1), ϖ_1)` and `(a(q), ϖ_q)` with
  `ϖ_t = Λ((0,t] × ·)` and `a(t) = ℬ((0,t])` ((A.e1)). So `(a(q) - a(1), Λ((1,q] × ·))` is a pair
  whose sum with `(a(1), ϖ_1)` is `(a(q), ϖ_q)`; its exponent is `Ψ_q - Ψ_1 = φ`, and the
  uniqueness of the data (`lem:line-exponent-data`(1)) makes its measure the step measure.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair IsSymLevyExponent)
open scoped Topology ENNReal

/-! ## Helpers -/

/-- The exponent of a pair vanishes at `0`. -/
theorem SymLevyPair_exponent_zero (P : SymLevyPair) : P.exponent 0 = 0 := by
  simp [SymLevyPair.exponent, SymLevyPair.exponentL]

/-- An element of `ND_s` is continuous and vanishes at `0`. -/
theorem isSymLevyExponent_continuous_zero {ψ : ℝ → ℝ} (hψ : IsSymLevyExponent ψ) :
    Continuous ψ ∧ ψ 0 = 0 := by
  obtain ⟨P, hP⟩ := hψ
  have h : ψ = P.exponent := funext hP
  rw [h]
  exact ⟨P.continuous_exponent, SymLevyPair_exponent_zero P⟩

/-- **The telescoping series of a step.** If `Ψ` is continuous with `Ψ(0) = 0`, `q > 1`, and the
step `φ = Ψ(q ·) - Ψ` is nonnegative, then `Ψ(ω) = ∑_{m ≥ 0} φ(q^{-m-1}ω)`. -/
theorem hasSum_step_series {q : ℝ} (hq : 1 < q) {Ψ : ℝ → ℝ} (hc : Continuous Ψ) (h0 : Ψ 0 = 0)
    (hnn : ∀ ω : ℝ, 0 ≤ Ψ (q * ω) - Ψ ω) (ω : ℝ) :
    HasSum (fun m : ℕ => Ψ (q * (ω / q ^ (m + 1))) - Ψ (ω / q ^ (m + 1))) (Ψ ω) := by
  have hq0 : q ≠ 0 := by positivity
  set f : ℕ → ℝ := fun m => Ψ (ω / q ^ m) with hf
  have hterm : ∀ m : ℕ, Ψ (q * (ω / q ^ (m + 1))) - Ψ (ω / q ^ (m + 1)) = f m - f (m + 1) := by
    intro m
    simp only [hf]
    congr 2
    rw [pow_succ]
    field_simp
  simp_rw [hterm]
  have hnn' : ∀ m : ℕ, 0 ≤ f m - f (m + 1) := fun m => by rw [← hterm m]; exact hnn _
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn']
  simp_rw [Finset.sum_range_sub']
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ω / q ^ m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hq)
    have h2 := (hc.tendsto 0).comp h1
    rwa [h0] at h2
  have h0' : f 0 = Ψ ω := by simp [hf]
  rw [← h0']
  simpa using (tendsto_const_nhds (x := f 0)).sub hlim

/-- **The octave step of a family has the exponent `Ψ_q - Ψ_1`.** -/
theorem charFun_octaveStep {q : ℝ} (hq : 1 < q) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsSymmetricFamily μ) (ω : ℝ) :
    charFun (μ 1 q) ω =
      ((Real.exp (-(lineExponent μ q ω - lineExponent μ 1 ω)) : ℝ) : ℂ) := by
  have hq0 : 0 < q := by linarith
  have hm := charFun_kernel_mul_gen hμ.1 zero_le_one hq.le ω
  rw [charFun_kernel_eq_exp hμ hq0.le, charFun_kernel_eq_exp hμ zero_le_one] at hm
  have hne : ((Real.exp (-lineExponent μ 1 ω) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  have : charFun (μ 1 q) ω = ((Real.exp (-lineExponent μ q ω)) : ℂ) /
      ((Real.exp (-lineExponent μ 1 ω)) : ℂ) := by
    rw [hm, mul_div_cancel_right₀ _ hne]
  rw [this, ← Complex.ofReal_div, ← Real.exp_sub]
  ring_nf

/-- A real transform `e^{-f}` determines `f`. -/
theorem eq_of_charFun_exp {m : Measure ℝ} {f g : ℝ → ℝ}
    (hf : ∀ ω : ℝ, charFun m ω = ((Real.exp (-f ω) : ℝ) : ℂ))
    (hg : ∀ ω : ℝ, charFun m ω = ((Real.exp (-g ω) : ℝ) : ℂ)) : f = g := by
  funext ω
  have h := Real.exp_injective (Complex.ofReal_injective ((hf ω).symm.trans (hg ω)))
  linarith

/-- A member of the modulation orbit has `Ψ_1` the knot exponent. -/
theorem lineExponent_one_of_mem_orbit {q : ℝ} {Ψ1 : ℝ → ℝ} {μ : ℝ → ℝ → Measure ℝ}
    (hμ : μ ∈ modulationOrbit q Ψ1) : lineExponent μ 1 = Ψ1 :=
  eq_of_charFun_exp (charFun_kernel_eq_exp hμ.1.1 zero_le_one) hμ.2

/-- For a family, `Ψ_q - Ψ_1 = Ψ_1(q ·) - Ψ_1`. -/
theorem lineExponent_q_sub_one {q : ℝ} {μ : ℝ → ℝ → Measure ℝ} (hμ : IsQFamily q μ) (ω : ℝ) :
    lineExponent μ q ω - lineExponent μ 1 ω = knotStep q (lineExponent μ 1) ω := by
  have h := lineExponent_cov hμ zero_le_one ω
  rw [mul_one] at h
  rw [knotStep, h]

/-- `Λ((0,t] × ·) = Λ((0,s] × ·) + Λ((s,t] × ·)` for `0 ≤ s ≤ t`. -/
theorem slab_add (Λ : Measure (ℝ × ℝ)) {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    slab Λ r t = slab Λ r s + slab Λ s t := by
  ext A hA
  rw [Measure.add_apply, slab_apply Λ r t hA, slab_apply Λ r s hA, slab_apply Λ s t hA,
    ← measure_union _ (measurableSet_Ioc.prod hA)]
  · rw [← union_prod, Ioc_union_Ioc_eq_Ioc hrs hst]
  · exact Disjoint.set_prod_left (Ioc_disjoint_Ioc_of_le le_rfl) _ _

/-! ## `lem:knot-exponent-ladder` -/

/-- **`lem:knot-exponent-ladder`(1), the series.** `Ψ_1 = ∑_{m ≥ 1} φ(q^{-m} ·)`. -/
theorem knot_exponent_ladder_1 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ) (hΨ1 : IsKnotExponent q Ψ1)
    (ω : ℝ) : HasSum (fun m : ℕ => knotStep q Ψ1 (ω / q ^ (m + 1))) (Ψ1 ω) := by
  obtain ⟨hc, h0⟩ := isSymLevyExponent_continuous_zero hΨ1.1
  exact hasSum_step_series hq hc h0 (isSymLevyExponent_nonneg hΨ1.2.1) ω

/-- **`lem:knot-exponent-ladder`(1), "in particular".** The ladder determines `Ψ_1`, and the
modulation orbit depends on the ladder only. -/
theorem knot_exponent_ladder_1_determines {q : ℝ} (hq : 1 < q) (Ψ1 Ψ1' : ℝ → ℝ)
    (hΨ1 : IsKnotExponent q Ψ1) (hΨ1' : IsKnotExponent q Ψ1') (L : ℤ → Measure ℝ)
    (hL : IsKnotLadder q Ψ1 L) (hL' : IsKnotLadder q Ψ1' L) :
    Ψ1 = Ψ1' ∧ modulationOrbit q Ψ1 = modulationOrbit q Ψ1' := by
  have hstep : knotStep q Ψ1 = knotStep q Ψ1' := by
    have h := eq_of_charFun_exp (m := L 0) (f := fun ω => knotStep q Ψ1 (q ^ (0 : ℤ) * ω))
      (g := fun ω => knotStep q Ψ1' (q ^ (0 : ℤ) * ω)) (hL 0).2 (hL' 0).2
    funext ω
    simpa using congrFun h ω
  have h : Ψ1 = Ψ1' := by
    funext ω
    refine (knot_exponent_ladder_1 hq Ψ1 hΨ1 ω).unique ?_
    rw [hstep]
    exact knot_exponent_ladder_1 hq Ψ1' hΨ1' ω
  exact ⟨h, h ▸ rfl⟩

/-- **`lem:knot-exponent-ladder`(2).** A family lies in the modulation orbit iff its octave step
`μ_{1,q}` has the exponent `φ`. -/
theorem knot_exponent_ladder_2 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ) (hΨ1 : IsKnotExponent q Ψ1)
    (μ : ℝ → ℝ → Measure ℝ) (hμ : IsQFamily q μ) :
    μ ∈ modulationOrbit q Ψ1 ↔
      ∀ ω : ℝ, charFun (μ 1 q) ω = ((Real.exp (-knotStep q Ψ1 ω) : ℝ) : ℂ) := by
  constructor
  · intro hmem ω
    rw [charFun_octaveStep hq hμ.1, lineExponent_q_sub_one hμ,
      lineExponent_one_of_mem_orbit hmem]
  · intro hstep
    refine ⟨hμ, fun ω => ?_⟩
    have hφ : ∀ ω : ℝ, lineExponent μ q ω - lineExponent μ 1 ω = knotStep q Ψ1 ω := by
      have h := eq_of_charFun_exp (charFun_octaveStep hq hμ.1) hstep
      exact fun ω => congrFun h ω
    have hΨ : lineExponent μ 1 ω = Ψ1 ω := by
      refine (step_field_1 hq μ hμ one_pos ω).unique ?_
      simp_rw [mul_one, hφ]
      exact knot_exponent_ladder_1 hq Ψ1 hΨ1 ω
    rw [charFun_kernel_eq_exp hμ.1 zero_le_one, hΨ]

/-- **`lem:knot-exponent-ladder`(3).** Every member of the modulation orbit has
`Λ((1,q] × ·) = μ`, the step measure. -/
theorem knot_exponent_ladder_3 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ)
    (m : Measure ℝ) (hm : IsStepMeasure q Ψ1 m) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : μ ∈ modulationOrbit q Ψ1) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (hΛ : IsFamilyPair q μ Λ B) : slab Λ 1 q = m := by
  have hq0 : 0 < q := by linarith
  obtain ⟨P1, hP1, hP1ν, hP1a⟩ := hΛ.2 1 one_pos
  obtain ⟨Pq, hPq, hPqν, hPqa⟩ := hΛ.2 q hq0
  -- `a(1) ≤ a(q)`
  have ha : P1.a ≤ Pq.a := by
    have h : B (Ioc 0 1) ≤ B (Ioc 0 q) := measure_mono (Ioc_subset_Ioc_right hq.le)
    rw [← hP1a, ← hPqa] at h
    exact (ENNReal.ofReal_le_ofReal_iff Pq.a_nonneg).1 h
  -- the pair `(a(q) - a(1), Λ((1,q] × ·))`
  have hfold : ScaleSpace.IsFolded (slab Λ 1 q) := by
    rw [ScaleSpace.IsFolded, slab_apply Λ 1 q measurableSet_Iic]
    refine measure_mono_null (fun p hp => ?_) hΛ.1.carried
    simp only [mem_compl_iff, quadrant, mem_prod, mem_Ioi, not_and_or, not_lt]
    exact Or.inr hp.2
  have hle : slab Λ 1 q ≤ Pq.ν := by
    rw [hPqν, slab_add Λ zero_le_one hq.le]
    exact Measure.le_add_left le_rfl
  have hint : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(slab Λ 1 q) ≠ ⊤ :=
    ne_top_of_le_ne_top Pq.ν_integrable (lintegral_mono' hle le_rfl)
  set R : SymLevyPair := ⟨Pq.a - P1.a, slab Λ 1 q, sub_nonneg.2 ha, hfold, hint⟩ with hR
  have hsum : SymLevyPair_add R P1 = Pq := by
    cases Pq with
    | mk aq νq _ _ _ =>
      simp only [SymLevyPair_add, hR]
      congr 1
      · ring
      · simp only at hPqν
        rw [hPqν, hP1ν, slab_add Λ zero_le_one hq.le, add_comm]
  -- its exponent is `Ψ_q - Ψ_1 = φ`
  have hRexp : HasExpData (knotStep q Ψ1) R := by
    intro ω
    have h1 := lineExponent_eq_of_folded hμ.1.1 zero_le_one hP1 ω
    have hq' := lineExponent_eq_of_folded hμ.1.1 hq0.le hPq ω
    have hφ := lineExponent_q_sub_one hμ.1 ω
    rw [lineExponent_one_of_mem_orbit hμ] at hφ h1
    rw [← hφ, h1, hq', ← hsum, SymLevyPair_add_exponent]
    ring
  obtain ⟨P, hP, hPm⟩ := hm
  rw [← hPm]
  exact (line_exponent_data_1_unique _ R P hRexp hP).2

end Pyramids
