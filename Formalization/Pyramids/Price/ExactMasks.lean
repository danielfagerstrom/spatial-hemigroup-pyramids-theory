/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Price.GridKnot
import Pyramids.Pyramid.NoBoundedStep

/-!
# `prop:exact-masks`: which masks have an exact grid pyramid

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:exact-masks`. Wave 3g: `exact_masks_1`,
`exact_masks_1_poisson` and `exact_masks_2` moved here from `PyramidsSkeleton.Ch05Price`,
unchanged in name, binders and conclusion. On 2026-11-15, by the author's decision (a
strengthening), `exact_masks_1` no longer takes a lattice: its binders `Γ`, the lattice instances
and `hw : IsLatticeMask Γ w` were replaced by the three hypotheses its proof reads, that `w` is a
probability law, symmetric and other than `δ₀`. The last sentence of (1), which reads the lattice,
is the separate `exact_masks_1_poisson`, unchanged.

## The route

* **The data of the mask.** A symmetric infinitely divisible law has symmetric data
  `(A_w, ν_w)` (`exists_symData`, A39), and on a lattice `A_w = 0` with `ν_w` finite and carried
  by `Γ ∖ {0}` (`lem:lattice-infinitely-divisible`); its transform is the compound Poisson
  transform. The support is unbounded by `prop:no-bounded-step` (A46 inside it), a symmetric
  point mass being `δ₀`.
* **(a) ⇒ (b).** A carrying family makes `w = μ_{1,q}` infinitely divisible
  (`lem:family-structure`, A41) and gives `μ_1` the data `(A_w/(q² - 1), ν*)`
  (`CarriesLatticeLadder.knot_data`); `ν*` a Lévy measure gives the moment
  (`lintegral_posLog_of_ladderNuStar`).
* **(b) ⇒ (a)** is `prop:ladder-knot-kernel`(2) (`ladder_knot_kernel_2`): a symmetric family with
  the step `w` carries the ladder. Neither direction reads the lattice.
* **(b) ⇔ (c)** is `ladder_knot_kernel_2_moments` (A49, A50).
* **(2).** The knot data are `(0, ν*)` since `A_w = 0`; non-uniqueness is
  `ladder_knot_kernel_2_not_unique`; the uniform coupling is the family of `ladder_knot_kernel_2`,
  whose kernel at `t = qⁿu`, `u ∈ [1, q)`, has the data `octaveData`, the dilate by `qⁿ` of
  `(0, ν* + (log_q u) ν_w)`, which is `uniformCouplingNu`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## Lévy measures and families -/

/-- **The Lévy measure is unique**: it is that of every triplet. -/
theorem HasLevyMeasure.unique {m ν ν' : Measure (Rd d)} (h : HasLevyMeasure m ν)
    (h' : HasLevyMeasure m ν') : ν = ν' := by
  obtain ⟨⟨T, hT⟩, hall⟩ := h
  rw [← hall T hT]
  exact h'.2 T hT

/-- A family with the ladder of `w` carries the grid pyramid of `(w, q)`. -/
theorem HasLadder.carries {q : ℝ} (hq : 1 < q) {w : Measure (Rd d)}
    {μ : ℝ → ℝ → Measure (Rd d)} (h : HasLadder q w μ) : CarriesLatticeLadder q w μ :=
  ⟨hq, h.1.1, h.2.1, h.2.2⟩

/-- **The data of an infinitely divisible mask**: `(0, ν_w)`, `ν_w` finite, nonzero and carried by
`Γ ∖ {0}`. -/
theorem lattice_mask_data_of_id (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {w : Measure (Rd d)} (hw : IsLatticeMask (Γ : Set (Rd d)) w) (hid : IsInfinitelyDivisible w) :
    ∃ Dw : SymLevyData d, IsSymData w Dw ∧ Dw.A = 0 ∧ IsFiniteMeasure Dw.ν ∧ Dw.ν ≠ 0 ∧
      Dw.ν ((Γ : Set (Rd d)) \ {0})ᶜ = 0 := by
  obtain ⟨hprob, hs, hne, hcarr⟩ := hw
  obtain ⟨Dw, hDw⟩ := exists_symData hid hs
  obtain ⟨hA, hfin, hcar⟩ := lattice_infinitely_divisible w hid _ (SymLevyData.hasTriplet hDw)
    Γ hcarr
  have hA0 : Dw.A = 0 := by
    have h2 : (2 : ℝ) • Dw.A = 0 := hA
    exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
  refine ⟨Dw, hDw, hA0, hfin, fun h0 => hne (eq_dirac_of_charFun_one fun ω => ?_), hcar⟩
  rw [hDw ω]
  simp [SymLevyData.exponent, pairExponent, hA0, h0, quad_zero]

/-- **The moment from a carrying family**: `∫ log₊|x| ν_w(dx) < ∞`, since `ν*` is the Lévy measure
of the knot kernel. -/
theorem CarriesLatticeLadder.moment (hd : 1 ≤ d) {q : ℝ} {w : Measure (Rd d)}
    [IsProbabilityMeasure w] (hs : w.map (fun x => -x) = w) {Dw : SymLevyData d}
    (hDw : IsSymData w Dw) {μ : ℝ → ℝ → Measure (Rd d)} (hμ : CarriesLatticeLadder q w μ) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dw.ν < ⊤ := by
  obtain ⟨D1, -, hν1, -⟩ := hμ.knot_data hd hs hDw
  refine lintegral_posLog_of_ladderNuStar hμ.1 Dw ?_
  rw [← hν1]
  exact D1.ν_integrable

/-- **Exactness from the moment** (`prop:ladder-knot-kernel`(2)). -/
theorem exact_of_symData_moment (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) {w : Measure (Rd d)}
    [IsProbabilityMeasure w] (hne : w ≠ Measure.dirac 0) {Dw : SymLevyData d}
    (hDw : IsSymData w Dw) (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dw.ν < ⊤) :
    IsExactLatticePyramid q w := by
  obtain ⟨μ, hlad, -, -⟩ := ladder_knot_kernel_2 hd hq w hne Dw hDw hmom
  exact ⟨μ, hlad.carries hq⟩

/-- A symmetric point mass is `δ₀`. -/
theorem eq_zero_of_dirac_symm {x : Rd d}
    (h : (Measure.dirac x).map (fun y : Rd d => -y) = Measure.dirac x) : x = 0 := by
  rw [Measure.map_dirac' measurable_neg] at h
  have h1 := congrArg (fun m : Measure (Rd d) => m {x}) h
  simp only [Measure.dirac_apply_of_mem (mem_singleton x)] at h1
  by_contra hx
  have hne : -x ∉ ({x} : Set (Rd d)) := by
    rw [mem_singleton_iff]
    intro h2
    exact hx (by
      have h3 : (2 : ℝ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [← h2]; exact neg_add_cancel x
      exact (smul_eq_zero.1 h3).resolve_left (by norm_num))
  rw [Measure.dirac_apply' _ (measurableSet_singleton x), indicator_of_notMem hne] at h1
  exact zero_ne_one h1

/-! ## `prop:exact-masks`(1) -/

/-- **`prop:exact-masks`(1), the criterion.** For a symmetric probability law `w ≠ δ₀` on `ℝ^d`
and `q > 1`: the grid pyramid is exact iff `w` is infinitely divisible with
`∫ log₊|x| ν_w(dx) < ∞`, iff `w` is infinitely divisible with `∫ log₊|x| w(dx) < ∞`. No lattice is
read (2026-11-15, a strengthening, the author's decision). -/
theorem exact_masks_1 {q : ℝ} (hq : 1 < q) (w : Measure (Rd d)) (hprob : IsProbabilityMeasure w)
    (hs : w.map (fun x => -x) = w) (hne : w ≠ Measure.dirac 0) :
    (IsExactLatticePyramid q w ↔ IsInfinitelyDivisible w ∧ ∃ ν : Measure (Rd d),
        HasLevyMeasure w ν ∧ ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂ν < ⊤) ∧
      (IsExactLatticePyramid q w ↔ IsInfinitelyDivisible w ∧
        ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂w < ⊤) := by
  haveI := hprob
  have hd := one_le_of_ne_dirac hne
  have h1 : IsExactLatticePyramid q w ↔ IsInfinitelyDivisible w ∧ ∃ ν : Measure (Rd d),
      HasLevyMeasure w ν ∧ ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂ν < ⊤ := by
    constructor
    · rintro ⟨μ, hμ⟩
      have hid : IsInfinitelyDivisible w := by
        have := isLawHemigroup_infinitelyDivisible hd hμ.2.1 1 q zero_le_one hμ.1.le
        rwa [hμ.2.2.2] at this
      obtain ⟨Dw, hDw⟩ := exists_symData hid hs
      exact ⟨hid, Dw.ν, (hasLevyMeasure_of_symData hDw).1, hμ.moment hd hs hDw⟩
    · rintro ⟨hid, ν, hν, hmom⟩
      obtain ⟨Dw, hDw⟩ := exists_symData hid hs
      rw [hν.unique (hasLevyMeasure_of_symData hDw).1] at hmom
      exact exact_of_symData_moment hd hq hne hDw hmom
  refine ⟨h1, h1.trans ⟨fun ⟨hid, ν, hν, hmom⟩ => ⟨hid, ?_⟩, fun ⟨hid, hmw⟩ => ⟨hid, ?_⟩⟩⟩
  · obtain ⟨Dw, hDw⟩ := exists_symData hid hs
    rw [hν.unique (hasLevyMeasure_of_symData hDw).1] at hmom
    exact (ladder_knot_kernel_2_moments w hid Dw hDw).1 hmom
  · obtain ⟨Dw, hDw⟩ := exists_symData hid hs
    exact ⟨Dw.ν, (hasLevyMeasure_of_symData hDw).1,
      (ladder_knot_kernel_2_moments w hid Dw hDw).2 hmw⟩

/-- **`prop:exact-masks`(1), the last sentence.** An infinitely divisible mask is the compound
Poisson law of a finite symmetric Lévy measure carried by `Γ ∖ {0}`, with no Gaussian part, and
its support is unbounded. -/
theorem exact_masks_1_poisson (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (w : Measure (Rd d)) (hw : IsLatticeMask (Γ : Set (Rd d)) w) (hid : IsInfinitelyDivisible w) :
    (∃ ν : Measure (Rd d), HasLevyMeasure w ν ∧ HasNoGaussianPart w ∧ IsFiniteMeasure ν ∧
      ν.map (fun x => -x) = ν ∧ ν ((Γ : Set (Rd d)) \ {0})ᶜ = 0 ∧ w = compoundPoissonLaw ν) ∧
      ∀ R : ℝ, w {x | R < ‖x‖} ≠ 0 := by
  haveI := hw.1
  obtain ⟨Dw, hDw, hA0, hfin, -, hcar⟩ := lattice_mask_data_of_id Γ hw hid
  obtain ⟨hLw, hGw⟩ := hasLevyMeasure_of_symData hDw
  refine ⟨⟨Dw.ν, hLw, hGw hA0, hfin, Dw.ν_symm, hcar, ?_⟩,
    fun R hR => (no_bounded_step w ⟨R, hR⟩ fun x hx => hw.2.2.1 ?_).1 hid⟩
  · haveI := hfin
    change w = cpLaw Dw.ν
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_cpLaw_symm _ Dw.ν_symm, hDw ω]
    simp [SymLevyData.exponent, pairExponent, hA0, quad_zero]
  · have h1 := hw.2.1
    rw [hx] at h1 ⊢
    rw [eq_zero_of_dirac_symm h1]

/-! ## `prop:exact-masks`(2) -/

/-- **`prop:exact-masks`(2), ladder and family.** If the grid pyramid is exact and `ν_w` is the
Lévy measure of `w`: every carrying family has the knot kernel (`eq:knot-product`), with no
Gaussian part and Lévy measure `ν* = ∑_{m ≥ 1} D_{q^{-m}} ν_w`; two carrying families differ; and
one carrying family, the uniform coupling, has kernels with no Gaussian part and the Lévy measures
`ν_t = ν* + (log_q t) ν_w` on `[1, q]`, `ν_{q^n t} = D_{q^n} ν_t`. -/
theorem exact_masks_2 (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ] [IsZLattice ℝ Γ] {q : ℝ}
    (hq : 1 < q) (w : Measure (Rd d)) (hw : IsLatticeMask (Γ : Set (Rd d)) w)
    (hex : IsExactLatticePyramid q w) (νw : Measure (Rd d)) (hνw : HasLevyMeasure w νw) :
    (∀ μ : ℝ → ℝ → Measure (Rd d), CarriesLatticeLadder q w μ →
      (∀ ω : Rd d, Tendsto (fun M => ladderProd q w M ω) atTop (𝓝 (charFun (μ 0 1) ω)) ∧
        Tendsto (fun M => charFun (ladderConv q w M) ω) atTop (𝓝 (charFun (μ 0 1) ω))) ∧
      HasNoGaussianPart (μ 0 1) ∧ HasLevyMeasure (μ 0 1) (ladderNuStar q νw)) ∧
      (∃ μ μ' : ℝ → ℝ → Measure (Rd d), CarriesLatticeLadder q w μ ∧
        CarriesLatticeLadder q w μ' ∧ ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ μ s t ≠ μ' s t) ∧
      ∃ μ : ℝ → ℝ → Measure (Rd d), CarriesLatticeLadder q w μ ∧ ∀ t : ℝ, 0 < t →
        HasNoGaussianPart (μ 0 t) ∧ HasLevyMeasure (μ 0 t) (uniformCouplingNu q νw t) := by
  obtain ⟨μ0, hμ0⟩ := hex
  haveI := hw.1
  have hd := one_le_of_ne_dirac hw.2.2.1
  obtain ⟨-, Dw, hDw, hA0, -, -, -⟩ := lattice_mask_data hd Γ hw hμ0
  have hνeq : νw = Dw.ν := hνw.unique (hasLevyMeasure_of_symData hDw).1
  have hmom := hμ0.moment hd hw.2.1 hDw
  refine ⟨fun μ hμ => ⟨hμ.product hd, ?_⟩, ?_, ?_⟩
  · -- the knot kernel
    obtain ⟨D1, hA1, hν1, hD1⟩ := hμ.knot_data hd hw.2.1 hDw
    haveI := hμ.prob le_rfl zero_le_one
    obtain ⟨hL, hG⟩ := hasLevyMeasure_of_symData hD1
    refine ⟨hG (by rw [hA1, hA0, smul_zero]), ?_⟩
    rw [hνeq, ← hν1]
    exact hL
  · -- not unique
    obtain ⟨μ, μ', hlad, hlad', s, t, hs, hst, hne⟩ :=
      ladder_knot_kernel_2_not_unique hq w hw.2.2.1 Dw hDw hmom
    exact ⟨μ, μ', hlad.carries hq, hlad'.carries hq, s, t, hs, hst, hne⟩
  · -- the uniform coupling
    have hl := isCouplingWeight_logb hq
    set Dst := ladderStarData hq Dw hmom with hDst
    set D := couplingData Dst Dw SymLevyData.zero (Real.logb q) (Real.logb q) with hD
    have hsyn : IsSynthesisData q D := isSynthesisData_uniform hq Dw hmom
      (exists_exponent_ne_zero hw.2.2.1 hDw) hl fun s t hs hst _ => logb_strictMonoOn hq hs hst
    obtain ⟨⟨μ, hμ⟩, hfam⟩ := coupling_family hq hsyn w (charFun_uniform_step hq Dw hmom hl hDw)
    obtain ⟨hlad, -, -⟩ := hfam μ hμ
    refine ⟨μ, hlad.carries hq, fun t ht => ?_⟩
    obtain ⟨hp, hc⟩ := hμ 0 t le_rfl ht.le
    haveI := hp
    have hDt : IsSymData (μ 0 t) (octaveData q D t) := fun ω => by
      rw [hc ω, octaveExponent_zero_left, sub_zero, octaveData_exponent hq]
    obtain ⟨hL, hG⟩ := hasLevyMeasure_of_symData hDt
    refine ⟨hG ?_, ?_⟩
    · rw [octaveData_A hq, octaveA, if_neg (not_le.2 ht)]
      simp [hD, couplingData, SymLevyData.addSmul, hDst, ladderStarData, hA0, SymLevyData.zero]
    · rw [octaveData_ν hq] at hL
      convert hL using 1
      rw [hνeq, octaveNu, uniformCouplingNu, if_neg (not_le.2 ht), if_neg (not_le.2 ht)]
      simp [hD, couplingData, SymLevyData.addSmul, hDst, ladderStarData, SymLevyData.zero]

end Pyramids
