/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.FamilyDilations

/-!
# `prop:no-lattice-kernel`: no kernel from scale zero is a lattice law

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:no-lattice-kernel`, chapter 3. Wave 2d: the
declaration moved here from `PyramidsSkeleton.Ch03Pyramid`, its statement unchanged.

## The route

Another than the printed one: no Lévy data, no projection onto the span of the subgroup, and no
use of `lem:lattice-infinitely-divisible`.

* **Scales below `t`.** With `T` the bijection of `q⁻¹`-covariance (the inverse of `S_q`),
  `T u < u` for `u > 0`, since `S_q u > u` (`lem:family-dilations`(1), which reads
  `lem:family-structure`). So for every `n` some `s ≤ t` has `μ_s = D_{q^{-n}} μ_t`.
* **A convolution carried by `Γ`.** `μ_t = μ_{s,t} * μ_s` is carried by `Γ`, so for some `x` the
  law `μ_s` is carried by `Γ - x` (Tonelli's theorem on the null set of the product,
  `exists_translate_of_conv`).
* **Two atoms.** `Γ` is countable, so `μ_t`, which is not `δ₀` by (ND), has an atom `x₀ ≠ 0`, and
  by symmetry `-x₀` is one too. Both lie in every set carrying `μ_t`, so `x + q^{-n}x₀` and
  `x - q^{-n}x₀` lie in `Γ`, and so does their difference `2q^{-n}x₀`.
* **Discreteness.** The points `2q^{-n}x₀ ≠ 0` of `Γ` tend to `0`, which is isolated in `Γ`.
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {d : ℕ}

/-- **A convolution carried by a set**: if `a * b` is carried by the measurable set `C`, then for
some `x` the law `b` is carried by `C - x`. -/
theorem exists_translate_of_conv {a b : Measure (Rd d)} [IsProbabilityMeasure a]
    [IsProbabilityMeasure b] {C : Set (Rd d)} (hC : MeasurableSet C) (h : (a ∗ b) Cᶜ = 0) :
    ∃ x : Rd d, b {y | x + y ∈ Cᶜ} = 0 := by
  rw [Measure.conv, Measure.map_apply measurable_add hC.compl] at h
  have hae := Measure.measure_ae_null_of_prod_null h
  obtain ⟨x, hx⟩ := hae.exists
  exact ⟨x, hx⟩

/-- **A discrete subgroup of `ℝ^d` is countable.** -/
theorem countable_of_discrete (Γ : AddSubgroup (Rd d)) [DiscreteTopology Γ] :
    (Γ : Set (Rd d)).Countable := by
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  exact Set.countable_coe_iff.1 this

/-- **`prop:no-lattice-kernel`.** No kernel `μ_t`, `t > 0`, of a symmetric family that is
`q`-covariant for some `q > 1` is carried by a discrete subgroup of `ℝ^d`. -/
theorem no_lattice_kernel (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsSymmetricFamily μ)
    {q : ℝ} (hq : 1 < q) (hcov : IsLamCovariant μ q) {t : ℝ} (ht : 0 < t)
    (Γ : AddSubgroup (Rd d)) [DiscreteTopology Γ] : μ 0 t (Γ : Set (Rd d))ᶜ ≠ 0 := by
  intro hΓ
  have hq0 : 0 < q := by linarith
  obtain ⟨S, hS⟩ := hcov
  have hK := kernelOrder_rd hd hμ
  have hcount := countable_of_discrete Γ
  have hΓm : MeasurableSet (Γ : Set (Rd d)) := hcount.measurableSet
  haveI := hμ.1.isProbability 0 t le_rfl ht.le
  -- the inverse bijection lowers every scale
  obtain ⟨T, hT, hTS, hST⟩ := cov_inv hq0 hS
  have hTle : ∀ u : ℝ, 0 ≤ u → T u ≤ u := by
    intro u hu
    rcases hu.eq_or_lt with h0 | h0
    · subst h0; rw [incBij_zero hT.1]
    · have hTu : 0 < T u := incBij_pos hT.1 h0
      have := hK.lt_cov hq hS hTu
      rw [hST u hu] at this
      exact this.le
  -- `μ_s = D_{q^{-n}} μ_t` for some `s ≤ t`
  have hscale : ∀ n : ℕ, ∃ s : ℝ, 0 ≤ s ∧ s ≤ t ∧
      μ 0 s = (μ 0 t).map (fun x => (q⁻¹) ^ n • x) := by
    intro n
    induction n with
    | zero =>
      refine ⟨t, ht.le, le_rfl, ?_⟩
      have e : (fun x : Rd d => (q⁻¹) ^ 0 • x) = id := by funext x; simp
      rw [e, Measure.map_id]
    | succ n ih =>
      obtain ⟨s, hs, hst, hμs⟩ := ih
      refine ⟨T s, hT.1.mapsTo hs, (hTle s hs).trans hst, ?_⟩
      rw [← cov_kernel hT hs, hμs, Measure.map_map (continuous_const_smul _).measurable
        (continuous_const_smul _).measurable]
      congr 1
      funext x
      simp only [Function.comp_apply, smul_smul, pow_succ']
  -- an atom `x₀ ≠ 0` of `μ_t`, and `-x₀`
  have hatom : ∃ x₀ : Rd d, x₀ ≠ 0 ∧ μ 0 t {x₀} ≠ 0 := by
    by_contra hno
    push Not at hno
    have hnull : μ 0 t ((Γ : Set (Rd d)) \ {0}) = 0 := by
      rw [← Set.biUnion_of_singleton ((Γ : Set (Rd d)) \ {0}),
        measure_biUnion_null_iff (hcount.mono sdiff_subset)]
      intro x hx
      exact hno x hx.2
    have hc : μ 0 t {(0 : Rd d)}ᶜ = 0 := by
      refine measure_mono_null (fun x hx => ?_) (measure_union_null hΓ hnull)
      by_cases hxΓ : x ∈ (Γ : Set (Rd d))
      · exact Or.inr ⟨hxΓ, hx⟩
      · exact Or.inl hxΓ
    have h1 : μ 0 t {(0 : Rd d)} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton 0)).1 hc
    have hdir : μ 0 t = Measure.dirac 0 := by
      have hae : ∀ᵐ x ∂(μ 0 t), x ∈ ({0} : Set (Rd d)) := ae_iff.2 hc
      rw [← Measure.restrict_eq_self_of_ae_mem hae, Measure.restrict_singleton, h1, one_smul]
    exact hμ.2.1 0 t le_rfl ht hdir
  obtain ⟨x₀, hx₀, hx₀m⟩ := hatom
  have hnegm : μ 0 t {-x₀} ≠ 0 := by
    have h := hμ.2.2 0 t le_rfl ht.le
    rw [← h, Measure.map_apply measurable_neg (measurableSet_singleton _)]
    have e : (fun x : Rd d => -x) ⁻¹' {-x₀} = {x₀} := by
      ext x; simp
    rwa [e]
  -- `2 q^{-n} x₀ ∈ Γ` for every `n`
  have hmem : ∀ n : ℕ, (q⁻¹) ^ n • ((2 : ℝ) • x₀) ∈ Γ := by
    intro n
    obtain ⟨s, hs, hst, hμs⟩ := hscale n
    haveI := hμ.1.isProbability s t hs hst
    haveI := hμ.1.isProbability 0 s le_rfl hs
    have hcasc : μ 0 t = μ s t ∗ μ 0 s := hμ.1.cascade 0 s t le_rfl hs hst
    rw [hcasc] at hΓ
    obtain ⟨x, hx⟩ := exists_translate_of_conv hΓm hΓ
    have hxm : MeasurableSet {y : Rd d | x + y ∈ (Γ : Set (Rd d))ᶜ} :=
      (measurable_const_add x) hΓm.compl
    rw [hμs, Measure.map_apply (continuous_const_smul _).measurable hxm] at hx
    -- every atom of `μ_t` lies in the carrying set
    have hin : ∀ z : Rd d, μ 0 t {z} ≠ 0 → x + (q⁻¹) ^ n • z ∈ (Γ : Set (Rd d)) := by
      intro z hz
      by_contra hno
      exact hz (measure_mono_null (fun y hy => by
        rw [mem_singleton_iff.1 hy]; exact hno) hx)
    have h1 := hin x₀ hx₀m
    have h2 := hin (-x₀) hnegm
    have h3 := Γ.sub_mem h1 h2
    have e : x + (q⁻¹) ^ n • x₀ - (x + (q⁻¹) ^ n • -x₀) = (q⁻¹) ^ n • ((2 : ℝ) • x₀) := by
      rw [smul_neg, two_smul, smul_add]; abel
    rwa [e] at h3
  -- discreteness
  set y : ℕ → Γ := fun n => ⟨(q⁻¹) ^ n • ((2 : ℝ) • x₀), hmem n⟩ with hy
  have hlim : Tendsto y atTop (𝓝 0) := by
    rw [tendsto_subtype_rng]
    have h1 : Tendsto (fun n : ℕ => (q⁻¹) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hq0.le) (inv_lt_one_of_one_lt₀ hq)
    have h2 := h1.smul_const ((2 : ℝ) • x₀)
    rw [zero_smul] at h2
    exact h2
  rw [nhds_discrete, tendsto_pure] at hlim
  obtain ⟨n, hn⟩ := hlim.exists
  have h0 := congrArg Subtype.val hn
  simp only [hy, ZeroMemClass.coe_zero] at h0
  rcases smul_eq_zero.1 h0 with h | h
  · exact (pow_ne_zero n (inv_ne_zero hq0.ne')) h
  · rcases smul_eq_zero.1 h with h | h
    · norm_num at h
    · exact hx₀ h

end Pyramids
