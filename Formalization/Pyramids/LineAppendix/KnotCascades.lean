/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.KnotOrbits
import Pyramids.LineAppendix.QCinRays
import Pyramids.RecursionHelmholtz

/-!
# `thm:knot-atom-cascades`(3)–(4): the extreme rays and the cascades

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:knot-atom-cascades`. Wave 3a: the five
declarations `knot_atom_cascades_3`, `_3_gaussian`, `_4`, `_4_gaussian` and `_4_families` moved
here from `PyramidsSkeleton.ChA1Line`, unchanged in statement and name.

## The route

* **The extreme rays.** By (2), `σ ↦ Λ_σ` and `β ↦ ℬ` are additive, positively homogeneous and
  inverted by the restriction to the domain (`orbitMixture_spec`, `cylMeasure_spec`,
  `knot_atom_cascades_2_gaussian`). A decomposition of `Λ_σ` in the cone is a decomposition of `σ`,
  and splitting `σ = σ|_B + σ|_{Bᶜ}` shows that an extreme `σ` makes every Borel set null or
  conull. Such a measure on `ℝ²` is a multiple of a point mass: its two marginals are
  (`eq_smul_dirac_of_zero_one`, from `QCinRays.lean`), so it is carried by one point
  (`eq_smul_dirac_prod_of_zero_one`). The mass is finite by (A.e3), the weight being positive.
* **The exponent of an orbit** is a sum over its atoms in `(0,t] × (0,∞)`, read through the lower
  integral (`surfaceExponent_knotAtomOrbit`); it converges, its terms with `n → -∞` being at most
  `½(ωrθ)²q^{2n}` (`knot_summable`).
* **The knots.** `θq^m ≤ t` iff `m ≤ n` for `t ∈ [θqⁿ, θq^{n+1})` (`knot_le_iff`), so the cascade is
  constant there and gains the term `m = n` at `θqⁿ`. The law `exp[δ²_v]` has the transform
  `e^{-(1 - cos vω)}` (`charFun_randomWalkLaw`: the Poisson mixture of the powers of
  `½(δ_v + δ_{-v})`, whose transform is `cos vω`), so the kernels are convolved with it. A family
  would have `t ↦ μ̂_t(ω)` continuous at the knot `θ`, against the jump `2` of the exponent at
  `ω = π/(rθ)`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

/-! ## Measures carried by one point of the plane -/

theorem nnreal_smul_measure {α : Type*} [MeasurableSpace α] (c : ℝ≥0) (μ : Measure α) :
    c • μ = (c : ℝ≥0∞) • μ := by
  ext s hs
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

/-- A measure null off `{p}` is `σ{p} δ_p`. -/
theorem eq_smul_dirac_prod_of_compl_null {σ : Measure (ℝ × ℝ)} {p : ℝ × ℝ} (hp : σ {p}ᶜ = 0) :
    σ = σ {p} • Measure.dirac p := by
  ext A hA
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul,
    ← measure_inter_add_sdiff A (measurableSet_singleton p)]
  have h2 : σ (A \ {p}) = 0 := measure_mono_null (fun x hx => hx.2) hp
  rw [h2, add_zero]
  by_cases hpA : p ∈ A
  · rw [inter_eq_right.2 (singleton_subset_iff.2 hpA), indicator_of_mem hpA, Pi.one_apply,
      mul_one]
  · rw [inter_singleton_eq_empty.2 hpA, measure_empty, indicator_of_notMem hpA, mul_zero]

theorem compl_null_of_eq_smul_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {κ : Measure α} {τ : α} (h : κ = κ {τ} • Measure.dirac τ) : κ {τ}ᶜ = 0 := by
  rw [h, Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton τ).compl,
    indicator_of_notMem (by simp), smul_zero]

/-- **A measure on `ℝ²` for which every Borel set is null or conull is a multiple of a point
mass**: its marginals are, by `eq_smul_dirac_of_zero_one`. -/
theorem eq_smul_dirac_prod_of_zero_one {σ : Measure (ℝ × ℝ)}
    (h : ∀ B : Set (ℝ × ℝ), MeasurableSet B → σ B = 0 ∨ σ Bᶜ = 0) :
    ∃ p : ℝ × ℝ, σ = σ {p} • Measure.dirac p := by
  have h1 : ∀ B : Set ℝ, MeasurableSet B → σ.map Prod.fst B = 0 ∨ σ.map Prod.fst Bᶜ = 0 := by
    intro B hB
    rw [Measure.map_apply measurable_fst hB, Measure.map_apply measurable_fst hB.compl]
    exact h _ (measurable_fst hB)
  have h2 : ∀ B : Set ℝ, MeasurableSet B → σ.map Prod.snd B = 0 ∨ σ.map Prod.snd Bᶜ = 0 := by
    intro B hB
    rw [Measure.map_apply measurable_snd hB, Measure.map_apply measurable_snd hB.compl]
    exact h _ (measurable_snd hB)
  obtain ⟨θ, hθ⟩ := eq_smul_dirac_of_zero_one h1
  obtain ⟨r, hr⟩ := eq_smul_dirac_of_zero_one h2
  have n1 := compl_null_of_eq_smul_dirac hθ
  have n2 := compl_null_of_eq_smul_dirac hr
  rw [Measure.map_apply measurable_fst (measurableSet_singleton θ).compl] at n1
  rw [Measure.map_apply measurable_snd (measurableSet_singleton r).compl] at n2
  refine ⟨(θ, r), eq_smul_dirac_prod_of_compl_null
    (measure_mono_null (fun x hx => ?_) (measure_union_null n1 n2))⟩
  by_contra hc
  simp only [mem_union, mem_preimage, mem_compl_iff, mem_singleton_iff, not_or, not_not] at hc
  exact hx (Prod.ext hc.1 hc.2)

/-! ## `thm:knot-atom-cascades`(3): the cone of the `Λ` -/

theorem mem_surfaceCone_orbitMixture {q : ℝ} (hq : 1 < q) {σ : Measure (ℝ × ℝ)}
    (hσ : σ (cylinder q)ᶜ = 0) (hint : IsCylIntegrable σ) : orbitMixture q σ ∈ surfaceCone q := by
  obtain ⟨h1, h2, h3⟩ := orbitMixture_spec hq hσ
  exact ⟨h1, h2, by rw [h3]; exact hint⟩

theorem cylIntegral_smul_dirac (c : ℝ≥0∞) (p : ℝ × ℝ) :
    ∫⁻ x, ENNReal.ofReal (cylWeight (x.2 * x.1)) ∂(c • Measure.dirac p) =
      c * ENNReal.ofReal (cylWeight (p.2 * p.1)) := by
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]


theorem restrict_cyl_null {q : ℝ} {σ : Measure (ℝ × ℝ)} (hσ : σ (cylinder q)ᶜ = 0)
    (C : Set (ℝ × ℝ)) : (σ.restrict C) (cylinder q)ᶜ = 0 :=
  nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hσ.le)

theorem cylIntegrable_restrict {σ : Measure (ℝ × ℝ)} (h : IsCylIntegrable σ)
    (C : Set (ℝ × ℝ)) : IsCylIntegrable (σ.restrict C) :=
  ne_top_of_le_ne_top h (lintegral_mono' Measure.restrict_le_self le_rfl)

/-- The extreme rays of the cone of the `Λ` are rays of orbits. -/
theorem surfaceCone_extreme_mp {q : ℝ} (hq : 1 < q) {Λ : Measure (ℝ × ℝ)}
    (h : IsExtremeRayIn (surfaceCone q) Λ) :
    ∃ θ r : ℝ, (θ, r) ∈ cylinder q ∧ ∃ c : ℝ≥0, c ≠ 0 ∧ Λ = c • knotAtomOrbit q θ r := by
  obtain ⟨⟨hc, hinv, hint⟩, hne, hdec⟩ := h
  obtain ⟨hσc, hΛ⟩ := cylMeasure_spec hq hc hinv
  set σ := cylMeasure q Λ with hσdef
  -- every Borel set is `σ`-null or `σ`-conull
  have h01 : ∀ B : Set (ℝ × ℝ), MeasurableSet B → σ B = 0 ∨ σ Bᶜ = 0 := by
    intro B hB
    obtain ⟨c, hcB⟩ := hdec _
      (mem_surfaceCone_orbitMixture hq (restrict_cyl_null hσc B) (cylIntegrable_restrict hint B))
      _ (mem_surfaceCone_orbitMixture hq (restrict_cyl_null hσc Bᶜ)
        (cylIntegrable_restrict hint Bᶜ))
      (by rw [← orbitMixture_add, Measure.restrict_add_restrict_compl hB, hΛ])
    have h1 := congrArg (cylMeasure q) hcB
    rw [(orbitMixture_spec hq (restrict_cyl_null hσc B)).2.2, nnreal_smul_measure,
      cylMeasure_smul] at h1
    have h2 := congrArg (fun μ : Measure (ℝ × ℝ) => μ Bᶜ) h1
    simp only [Measure.restrict_apply hB.compl, compl_inter_self, measure_empty,
      Measure.smul_apply, smul_eq_mul] at h2
    rcases mul_eq_zero.1 h2.symm with h3 | h3
    · left
      have h4 := congrArg (fun μ : Measure (ℝ × ℝ) => μ B) h1
      simp only [Measure.restrict_apply hB, inter_self, Measure.smul_apply, smul_eq_mul, h3,
        zero_mul] at h4
      exact h4
    · exact Or.inr h3
  obtain ⟨p, hp⟩ := eq_smul_dirac_prod_of_zero_one h01
  set m := σ {p} with hm
  have hσ0 : σ ≠ 0 := by
    intro h0
    apply hne
    rw [← hΛ, h0, orbitMixture_zero]
  have hm0 : m ≠ 0 := by
    intro h0
    apply hσ0
    rw [hp, h0, zero_smul]
  have hpc : p ∈ cylinder q := by
    by_contra hpc
    exact hm0 (measure_mono_null (singleton_subset_iff.2 hpc) hσc)
  have hx : 0 < p.2 * p.1 := mul_pos hpc.2 (lt_of_lt_of_le one_pos hpc.1.1)
  have hmtop : m ≠ ⊤ := by
    intro htop
    have h1 : IsCylIntegrable σ := hint
    rw [IsCylIntegrable, hp, cylIntegral_smul_dirac, htop] at h1
    exact h1 (ENNReal.top_mul (by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact cylWeight_pos hx))
  refine ⟨p.1, p.2, hpc, m.toNNReal, ?_, ?_⟩
  · rw [Ne, ENNReal.toNNReal_eq_zero_iff, not_or]
    exact ⟨hm0, hmtop⟩
  · rw [← hΛ, hp, orbitMixture_smul, orbitMixture_dirac, nnreal_smul_measure,
      ENNReal.coe_toNNReal hmtop]

/-- The rays of orbits are extreme. -/
theorem surfaceCone_extreme_mpr {q : ℝ} (hq : 1 < q) {θ r : ℝ} (hθr : (θ, r) ∈ cylinder q)
    {c : ℝ≥0} (hc : c ≠ 0) : IsExtremeRayIn (surfaceCone q) (c • knotAtomOrbit q θ r) := by
  set p : ℝ × ℝ := (θ, r) with hpdef
  set σ0 : Measure (ℝ × ℝ) := (c : ℝ≥0∞) • Measure.dirac p with hσ0def
  have hσ0 : σ0 (cylinder q)ᶜ = 0 := by
    rw [hσ0def, Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_cylinder q).compl,
      indicator_of_notMem (by rw [mem_compl_iff, not_not]; exact hθr), smul_zero]
  have hσ0p : σ0 {p}ᶜ = 0 := compl_null_of_eq_smul_dirac (by
    rw [hσ0def, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton p), smul_eq_mul,
      mul_one])
  have hσ0pp : σ0 {p} = c := by
    rw [hσ0def, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton p), smul_eq_mul,
      mul_one]
  have hΛ : c • knotAtomOrbit q θ r = orbitMixture q σ0 := by
    rw [hσ0def, orbitMixture_smul, orbitMixture_dirac, nnreal_smul_measure]
  have hcyl : cylMeasure q (c • knotAtomOrbit q θ r) = σ0 := by
    rw [hΛ]; exact (orbitMixture_spec hq hσ0).2.2
  have hint : IsCylIntegrable σ0 := by
    rw [IsCylIntegrable, hσ0def, cylIntegral_smul_dirac]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  refine ⟨by rw [hΛ]; exact mem_surfaceCone_orbitMixture hq hσ0 hint, fun h0 => ?_,
    fun y hy z hz hyz => ?_⟩
  · have h1 := congrArg (fun Λ => cylMeasure q Λ {p}) h0
    simp only [hcyl, cylMeasure_zero, Measure.coe_zero, Pi.zero_apply, hσ0pp,
      ENNReal.coe_eq_zero] at h1
    exact hc h1
  · have hsum : cylMeasure q y + cylMeasure q z = σ0 := by rw [← cylMeasure_add, hyz, hcyl]
    have hy0 : cylMeasure q y {p}ᶜ = 0 := by
      have h1 := congrArg (fun μ : Measure (ℝ × ℝ) => μ {p}ᶜ) hsum
      simp only [Measure.add_apply, hσ0p] at h1
      exact (add_eq_zero.1 h1).1
    have hyrep := eq_smul_dirac_prod_of_compl_null hy0
    set a := cylMeasure q y {p} with ha
    have hac : a ≤ c := by
      have h1 := congrArg (fun μ : Measure (ℝ × ℝ) => μ {p}) hsum
      simp only [Measure.add_apply, hσ0pp] at h1
      rw [← h1]
      exact le_self_add
    have hatop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hac
    have hya : y = a • knotAtomOrbit q θ r := by
      rw [← (cylMeasure_spec hq hy.1 hy.2.1).2, hyrep, orbitMixture_smul,
        orbitMixture_dirac]
    refine ⟨a.toNNReal / c, ?_⟩
    rw [hya, smul_smul, div_mul_cancel₀ _ hc, nnreal_smul_measure, ENNReal.coe_toNNReal hatop]

/-- **The terms of the cascade are summable**: zero beyond the knots below `t`, at most
`½(ωrθ)²q^{2n}`. -/
theorem knot_summable {q : ℝ} (hq : 1 < q) {θ r : ℝ} (hθr : (θ, r) ∈ cylinder q) (t ω : ℝ) :
    Summable (fun n : ℤ => if θ * q ^ n ≤ t then 1 - Real.cos (ω * (r * θ * q ^ n)) else 0) := by
  have hq0 : 0 < q := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθr.1.1
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (t / θ) hq
  refine summable_of_le_zpow hq N ((ω * r * θ) ^ 2 / 2) (fun n => ?_) (fun n hn => ?_)
    (fun n => ?_)
  · split_ifs
    · linarith [Real.cos_le_one (ω * (r * θ * q ^ n))]
    · exact le_rfl
  · rw [if_neg]
    have h1 : q ^ (N : ℤ) ≤ q ^ n := zpow_le_zpow_right₀ hq.le hn.le
    rw [zpow_natCast] at h1
    rw [div_lt_iff₀ hθ0] at hN
    intro h2
    nlinarith
  · split_ifs
    · have h1 := Real.one_sub_sq_div_two_le_cos (x := ω * (r * θ * q ^ n))
      have e : (ω * (r * θ * q ^ n)) ^ 2 = (ω * r * θ) ^ 2 * q ^ (2 * n) := by
        rw [zpow_two_mul']; ring
      rw [e] at h1
      linarith
    · positivity

/-- **The exponent (A.e2) of an orbit** is the knot-atom cascade (A.e4). -/
theorem surfaceExponent_knotAtomOrbit {q : ℝ} (hq : 1 < q) {θ r : ℝ}
    (hθr : (θ, r) ∈ cylinder q) (t ω : ℝ) :
    surfaceExponent (knotAtomOrbit q θ r) 0 t ω = knotAtomCascade q θ r t ω := by
  have hq0 : 0 < q := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθr.1.1
  have hr : 0 < r := hθr.2
  have hS : MeasurableSet (Ioc 0 t ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioc.prod measurableSet_Ioi
  have hnn : ∀ n : ℤ, 0 ≤ (if θ * q ^ n ≤ t then 1 - Real.cos (ω * (r * θ * q ^ n)) else 0) :=
    fun n => by split_ifs <;> linarith [Real.cos_le_one (ω * (r * θ * q ^ n))]
  simp only [surfaceExponent, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, zero_mul,
    zero_add]
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun p => by simp only [Pi.zero_apply]; linarith [Real.cos_le_one (ω * p.2)])
    ((by fun_prop : Continuous fun p : ℝ × ℝ => 1 - Real.cos (ω * p.2)).aestronglyMeasurable),
    ← lintegral_indicator hS, knotAtomOrbit, lintegral_sum_measure]
  simp_rw [lintegral_dirac]
  rw [knotAtomCascade, ← ENNReal.toReal_ofReal (tsum_nonneg hnn),
    ENNReal.ofReal_tsum_of_nonneg hnn (knot_summable hq hθr t ω)]
  congr 1
  refine tsum_congr fun n => ?_
  by_cases h : θ * q ^ n ≤ t
  · rw [if_pos h, indicator_of_mem]
    exact ⟨⟨mul_pos hθ0 (zpow_pos hq0 n), h⟩, mul_pos (mul_pos hr hθ0) (zpow_pos hq0 n)⟩
  · rw [if_neg h, indicator_of_notMem, ENNReal.ofReal_zero]
    exact fun hm => h hm.1.2

/-- **`thm:knot-atom-cascades`(3), the cone of the `Λ`.** Its extreme rays are the rays of the
`Λ^{(θ,r)}`, `(θ, r) ∈ 𝒞`; every member is a mixture `Λ_σ` with `σ` unique; with `ℬ = 0` the
exponents (A.e2) of `Λ^{(θ,r)}` are the knot-atom cascade (A.e4). -/
theorem knot_atom_cascades_3 {q : ℝ} (hq : 1 < q) :
    (∀ Λ : Measure (ℝ × ℝ), IsExtremeRayIn (surfaceCone q) Λ ↔
        ∃ θ r : ℝ, (θ, r) ∈ cylinder q ∧ ∃ c : ℝ≥0, c ≠ 0 ∧ Λ = c • knotAtomOrbit q θ r) ∧
      (∀ Λ ∈ surfaceCone q, ∃! σ : Measure (ℝ × ℝ), σ (cylinder q)ᶜ = 0 ∧ Λ = orbitMixture q σ) ∧
      ∀ θ r : ℝ, (θ, r) ∈ cylinder q → ∀ t : ℝ, 0 < t → ∀ ω : ℝ,
        Summable (fun n : ℤ =>
          if θ * q ^ n ≤ t then 1 - Real.cos (ω * (r * θ * q ^ n)) else 0) ∧
        surfaceExponent (knotAtomOrbit q θ r) 0 t ω = knotAtomCascade q θ r t ω := by
  refine ⟨fun Λ => ⟨surfaceCone_extreme_mp hq, ?_⟩, fun Λ hΛ => ?_,
    fun θ r hθr t _ ω => ⟨knot_summable hq hθr t ω, surfaceExponent_knotAtomOrbit hq hθr t ω⟩⟩
  · rintro ⟨θ, r, hθr, c, hc, rfl⟩
    exact surfaceCone_extreme_mpr hq hθr hc
  · obtain ⟨h1, h2⟩ := cylMeasure_spec hq hΛ.1 hΛ.2.1
    refine ⟨cylMeasure q Λ, ⟨h1, h2.symm⟩, ?_⟩
    rintro σ ⟨hσ, rfl⟩
    exact ((orbitMixture_spec hq hσ).2.2).symm

/-! ## `thm:knot-atom-cascades`(3): the cone of the `ℬ` -/

/-- **`ℬ^{(θ)} = θ² 𝒢(δ_θ)`**: the knot Gaussian is the spread of a point mass. -/
theorem knotGaussian_eq (q θ : ℝ) :
    knotGaussian q θ = ENNReal.ofReal (θ ^ 2) • gaussSpread q (Measure.dirac θ) := by
  ext A hA
  rw [Measure.smul_apply, smul_eq_mul, gaussSpread_apply q _ hA, knotGaussian,
    Measure.sum_apply _ hA, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ (measurable_const_mul _ hA), mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
    zpow_two_mul', mul_assoc, mul_comm θ]
  rfl

theorem isFiniteMeasure_smul_dirac {c : ℝ≥0∞} (hc : c ≠ ⊤) (θ : ℝ) :
    IsFiniteMeasure (c • Measure.dirac θ) :=
  ⟨by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact hc.lt_top⟩

theorem smul_dirac_Ico_null {q θ : ℝ} {c : ℝ≥0∞} (hθ : θ ∈ Ico 1 q) :
    (c • Measure.dirac θ) (Ico 1 q)ᶜ = 0 := by
  rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ico.compl,
    indicator_of_notMem (by rw [mem_compl_iff, not_not]; exact hθ), smul_zero]

/-- The extreme rays of the cone of the `ℬ` are rays of knot Gaussians. -/
theorem gaussianCone_extreme_mp {q : ℝ} (hq : 1 < q) {B : Measure ℝ}
    (h : IsExtremeRayIn (gaussianCone q) B) :
    ∃ θ ∈ Ico 1 q, ∃ c : ℝ≥0, c ≠ 0 ∧ B = c • knotGaussian q θ := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hB, hne, hdec⟩ := h
  have hB' : gaussSpread q (B.restrict (Ico 1 q)) = B := (knot_atom_cascades_2_gaussian hq).1 B hB
  set β := B.restrict (Ico 1 q) with hβdef
  have hβf : IsFiniteMeasure β := by
    rw [hβdef, isFiniteMeasure_restrict]
    exact ne_top_of_le_ne_top (hB.2.1 q hq0)
      (measure_mono fun x hx => ⟨lt_of_lt_of_le one_pos hx.1, hx.2.le⟩)
  have hβc0 : β (Ico 1 q)ᶜ = 0 := by
    rw [hβdef, Measure.restrict_apply measurableSet_Ico.compl, compl_inter_self, measure_empty]
  have hβc : ∀ U : Set ℝ, (β.restrict U) (Ico 1 q)ᶜ = 0 := fun U =>
    nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hβc0.le)
  have hgs := (knot_atom_cascades_2_gaussian hq).2
  have h01 : ∀ U : Set ℝ, MeasurableSet U → β U = 0 ∨ β Uᶜ = 0 := by
    intro U hU
    obtain ⟨c, hcU⟩ := hdec _ (hgs _ inferInstance (hβc U)).1 _ (hgs _ inferInstance (hβc Uᶜ)).1
      (by rw [← gaussSpread_add, Measure.restrict_add_restrict_compl hU, hB'])
    have h1 := congrArg (fun μ : Measure ℝ => μ.restrict (Ico 1 q)) hcU
    try simp only at h1
    rw [(hgs _ inferInstance (hβc U)).2, nnreal_smul_measure, Measure.restrict_smul, ← hβdef] at h1
    have h2 := congrArg (fun μ : Measure ℝ => μ Uᶜ) h1
    simp only [Measure.restrict_apply hU.compl, compl_inter_self, measure_empty,
      Measure.smul_apply, smul_eq_mul] at h2
    rcases mul_eq_zero.1 h2.symm with h3 | h3
    · left
      have h4 := congrArg (fun μ : Measure ℝ => μ U) h1
      simp only [Measure.restrict_apply hU, inter_self, Measure.smul_apply, smul_eq_mul, h3,
        zero_mul] at h4
      exact h4
    · exact Or.inr h3
  obtain ⟨θ, hθ⟩ := eq_smul_dirac_of_zero_one h01
  set m := β {θ} with hm
  have hm0 : m ≠ 0 := by
    intro h0
    apply hne
    rw [← hB', hθ, h0, zero_smul, gaussSpread_zero]
  have hθI : θ ∈ Ico 1 q := by
    by_contra hθI
    apply hm0
    rw [hm, hβdef, Measure.restrict_apply (measurableSet_singleton θ),
      singleton_inter_eq_empty.2 hθI, measure_empty]
  have hmtop : m ≠ ⊤ := measure_ne_top β _
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθI.1
  have hq2 : ENNReal.ofReal (θ ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  set k := m * (ENNReal.ofReal (θ ^ 2))⁻¹ with hk
  have hktop : k ≠ ⊤ := ENNReal.mul_ne_top hmtop (ENNReal.inv_ne_top.2 hq2)
  have hk0 : k ≠ 0 := mul_ne_zero hm0 (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
  refine ⟨θ, hθI, k.toNNReal, ?_, ?_⟩
  · rw [Ne, ENNReal.toNNReal_eq_zero_iff, not_or]
    exact ⟨hk0, hktop⟩
  · rw [nnreal_smul_measure, ENNReal.coe_toNNReal hktop, knotGaussian_eq, smul_smul, hk,
      mul_assoc, ENNReal.inv_mul_cancel hq2 ENNReal.ofReal_ne_top, mul_one, ← gaussSpread_smul,
      ← hθ, hB']

/-- The rays of knot Gaussians are extreme. -/
theorem gaussianCone_extreme_mpr {q : ℝ} (hq : 1 < q) {θ : ℝ} (hθ : θ ∈ Ico 1 q) {c : ℝ≥0}
    (hc : c ≠ 0) : IsExtremeRayIn (gaussianCone q) (c • knotGaussian q θ) := by
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
  set a : ℝ≥0∞ := (c : ℝ≥0∞) * ENNReal.ofReal (θ ^ 2) with ha
  have hatop : a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have ha0 : a ≠ 0 := mul_ne_zero (ENNReal.coe_ne_zero.2 hc)
    (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)
  have hBeq : c • knotGaussian q θ = gaussSpread q (a • Measure.dirac θ) := by
    rw [nnreal_smul_measure, knotGaussian_eq, smul_smul, gaussSpread_smul]
  have hgs := (knot_atom_cascades_2_gaussian hq).2 _ (isFiniteMeasure_smul_dirac hatop θ)
    (smul_dirac_Ico_null (c := a) (q := q) (θ := θ) hθ)
  refine ⟨by rw [hBeq]; exact hgs.1, fun h0 => ?_, fun y hy z hz hyz => ?_⟩
  · have h1 := congrArg (fun μ : Measure ℝ => μ.restrict (Ico 1 q) {θ}) h0
    simp only [hBeq, hgs.2, Measure.restrict_zero, Measure.coe_zero, Pi.zero_apply,
      Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton θ), smul_eq_mul,
      mul_one] at h1
    exact ha0 h1
  · have hsum : y.restrict (Ico 1 q) + z.restrict (Ico 1 q) = a • Measure.dirac θ := by
      rw [← Measure.restrict_add, hyz, hBeq, hgs.2]
    have hy0 : y.restrict (Ico 1 q) {θ}ᶜ = 0 := by
      have h1 := congrArg (fun μ : Measure ℝ => μ {θ}ᶜ) hsum
      simp only [Measure.add_apply] at h1
      rw [compl_null_of_eq_smul_dirac (κ := a • Measure.dirac θ) (by
        rw [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton θ), smul_eq_mul,
          mul_one])] at h1
      exact (add_eq_zero.1 h1).1
    have hyrep := eq_smul_dirac_of_compl_null hy0
    set b := y.restrict (Ico 1 q) {θ} with hb
    have hba : b ≤ a := by
      have h1 := congrArg (fun μ : Measure ℝ => μ {θ}) hsum
      simp only [Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply_of_mem (mem_singleton θ), smul_eq_mul, mul_one] at h1
      rw [← h1]
      exact le_self_add
    have hbtop : b / a ≠ ⊤ := ENNReal.div_ne_top (ne_top_of_le_ne_top hatop hba) ha0
    refine ⟨(b / a).toNNReal, ?_⟩
    rw [← (knot_atom_cascades_2_gaussian hq).1 y hy, hyrep, nnreal_smul_measure,
      ENNReal.coe_toNNReal hbtop, hBeq, ← gaussSpread_smul, smul_smul,
      ENNReal.div_mul_cancel ha0 hatop]

/-- **`thm:knot-atom-cascades`(3), the cone of the `ℬ`.** Its extreme rays are those of the knot
Gaussians `ℬ^{(θ)}`, with `a(t) = ∑_{θqⁿ ≤ t} (θqⁿ)²`. -/
theorem knot_atom_cascades_3_gaussian {q : ℝ} (hq : 1 < q) :
    (∀ B : Measure ℝ, IsExtremeRayIn (gaussianCone q) B ↔
        ∃ θ ∈ Ico 1 q, ∃ c : ℝ≥0, c ≠ 0 ∧ B = c • knotGaussian q θ) ∧
      ∀ θ ∈ Ico 1 q, ∀ t : ℝ, 0 < t →
        Summable (fun n : ℤ => if θ * q ^ n ≤ t then (θ * q ^ n) ^ 2 else 0) ∧
        knotGaussian q θ (Ioc 0 t) =
          ENNReal.ofReal (∑' n : ℤ, if θ * q ^ n ≤ t then (θ * q ^ n) ^ 2 else 0) := by
  have hq0 : 0 < q := by linarith
  refine ⟨fun B => ⟨gaussianCone_extreme_mp hq, ?_⟩, fun θ hθ t ht => ?_⟩
  · rintro ⟨θ, hθ, c, hc, rfl⟩
    exact gaussianCone_extreme_mpr hq hθ hc
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
  have hnn : ∀ n : ℤ, 0 ≤ (if θ * q ^ n ≤ t then (θ * q ^ n) ^ 2 else 0) :=
    fun n => by split_ifs <;> positivity
  have hs : Summable (fun n : ℤ => if θ * q ^ n ≤ t then (θ * q ^ n) ^ 2 else 0) := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (t / θ) hq
    refine summable_of_le_zpow hq N (θ ^ 2) hnn (fun n hn => ?_) (fun n => ?_)
    · rw [if_neg]
      have h1 : q ^ (N : ℤ) ≤ q ^ n := zpow_le_zpow_right₀ hq.le hn.le
      rw [zpow_natCast] at h1
      rw [div_lt_iff₀ hθ0] at hN
      intro h2
      nlinarith
    · split_ifs
      · rw [mul_pow, zpow_two_mul']
      · positivity
  refine ⟨hs, ?_⟩
  rw [knotGaussian, Measure.sum_apply _ measurableSet_Ioc, ENNReal.ofReal_tsum_of_nonneg hnn hs]
  refine tsum_congr fun n => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ioc, smul_eq_mul]
  by_cases h : θ * q ^ n ≤ t
  · rw [if_pos h,
      indicator_of_mem (show θ * q ^ n ∈ Ioc 0 t from ⟨mul_pos hθ0 (zpow_pos hq0 n), h⟩),
      Pi.one_apply, mul_one]
  · rw [if_neg h, indicator_of_notMem (fun hm => h hm.2), mul_zero, ENNReal.ofReal_zero]

/-! ## The laws `exp[c δ²_v]` -/

theorem norm_charFun_integrand (ω x : ℝ) : ‖Complex.exp (↑ω * ↑x * Complex.I)‖ = 1 := by
  rw [← Complex.ofReal_mul]
  exact Complex.norm_exp_ofReal_mul_I _

theorem integrable_charFun_integrand {μ : Measure ℝ} [IsFiniteMeasure μ] (ω : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (↑ω * ↑x * Complex.I)) μ :=
  Integrable.of_bound
    ((by fun_prop : Continuous fun x : ℝ => Complex.exp (↑ω * ↑x * Complex.I)).aestronglyMeasurable)
    1 (ae_of_all _ fun x => (norm_charFun_integrand ω x).le)

instance isProbabilityMeasure_symStep (v : ℝ) : IsProbabilityMeasure (symStep v) := by
  refine ⟨?_⟩
  rw [symStep, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- `½(δ_v + δ_{-v})` has the transform `cos vω`. -/
theorem charFun_symStep (v ω : ℝ) : charFun (symStep v) ω = (Real.cos (v * ω) : ℂ) := by
  rw [charFun_apply_real, symStep, integral_smul_measure,
    integral_add_measure (integrable_charFun_integrand ω) (integrable_charFun_integrand ω),
    integral_dirac, integral_dirac]
  have h2 := Complex.two_cos (↑(v * ω))
  have e1 : (↑ω * ↑v * Complex.I : ℂ) = ↑(v * ω) * Complex.I := by push_cast; ring
  have e2 : (↑ω * ↑(-v) * Complex.I : ℂ) = -↑(v * ω) * Complex.I := by push_cast; ring
  rw [e1, e2, Complex.ofReal_cos, ENNReal.toReal_inv, ENNReal.toReal_ofNat, Complex.real_smul]
  push_cast at h2 ⊢
  linear_combination (-1 / 2 : ℂ) * h2

/-- The Poisson series `∑ e^{-c} cⁿ/n! xⁿ = e^{-c} e^{cx}`. -/
theorem hasSum_poissonWeights (c x : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-c) * c ^ n / n.factorial * x ^ n)
      (Real.exp (-c) * Real.exp (c * x)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (c * x)).mul_left (Real.exp (-c))
  rw [← Real.exp_eq_exp_ℝ] at h
  have e : (fun n : ℕ => Real.exp (-c) * c ^ n / n.factorial * x ^ n) =
      fun n : ℕ => Real.exp (-c) * ((c * x) ^ n / n.factorial) := by
    funext n
    rw [mul_pow]
    ring
  rw [e]
  exact h

theorem poisson_weight_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ Real.exp (-c) * c ^ n / n.factorial := by positivity

/-- `exp[c δ²_v]` is a probability law, `c ≥ 0`. -/
theorem isProbabilityMeasure_randomWalkLaw {c : ℝ} (hc : 0 ≤ c) (v : ℝ) :
    IsProbabilityMeasure (randomWalkLaw c v) := by
  refine ⟨?_⟩
  rw [randomWalkLaw, Measure.sum_apply _ MeasurableSet.univ]
  have h1 : ∀ n : ℕ, (ENNReal.ofReal (Real.exp (-c) * c ^ n / n.factorial) •
      ScaleSpace.convPow (symStep v) n) univ =
        ENNReal.ofReal (Real.exp (-c) * c ^ n / n.factorial) := by
    intro n
    haveI := ScaleSpace.isProbabilityMeasure_convPow_real (symStep v) n
    rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  simp_rw [h1]
  have hs := hasSum_poissonWeights c 1
  simp only [one_pow, mul_one] at hs
  rw [← ENNReal.ofReal_tsum_of_nonneg (poisson_weight_nonneg hc) hs.summable, hs.tsum_eq,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]

/-- **`exp[c δ²_v]` has the transform `e^{-c(1 - cos vω)}`**, `c ≥ 0`. -/
theorem charFun_randomWalkLaw {c : ℝ} (hc : 0 ≤ c) (v ω : ℝ) :
    charFun (randomWalkLaw c v) ω = ((Real.exp (-(c * (1 - Real.cos (v * ω)))) : ℝ) : ℂ) := by
  haveI := isProbabilityMeasure_randomWalkLaw hc v
  have hint := integrable_charFun_integrand (μ := randomWalkLaw c v) ω
  rw [charFun_apply_real]
  unfold randomWalkLaw at hint ⊢
  rw [integral_sum_measure hint]
  have hpow : ∀ n : ℕ, ∫ x, Complex.exp (↑ω * ↑x * Complex.I) ∂(ScaleSpace.convPow (symStep v) n) =
      ((Real.cos (v * ω) ^ n : ℝ) : ℂ) := fun n => by
    rw [← charFun_apply_real, charFun_convPow_real, charFun_symStep, Complex.ofReal_pow]
  simp_rw [integral_smul_measure, hpow, ENNReal.toReal_ofReal (poisson_weight_nonneg hc _),
    Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_tsum]
  rw [(hasSum_poissonWeights c (Real.cos (v * ω))).tsum_eq, ← Real.exp_add]
  congr 2
  ring

/-! ## `thm:knot-atom-cascades`(4) -/

/-- `θq^m ≤ t` iff `m ≤ n`, for `t ∈ [θqⁿ, θq^{n+1})`. -/
theorem knot_le_iff {q : ℝ} (hq : 1 < q) {θ : ℝ} (hθ : 0 < θ) {n : ℤ} {t : ℝ}
    (ht : t ∈ Ico (θ * q ^ n) (θ * q ^ (n + 1))) (m : ℤ) : θ * q ^ m ≤ t ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hmn
    have h1 : q ^ (n + 1) ≤ q ^ m := zpow_le_zpow_right₀ hq.le (by omega)
    have h2 := mul_le_mul_of_nonneg_left h1 hθ.le
    linarith [ht.2]
  · intro h
    exact le_trans (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hq.le h) hθ.le) ht.1

/-- The cascade gains `1 - cos(ω rθqⁿ)` at the knot `θqⁿ`. -/
theorem knotAtomCascade_jump {q : ℝ} (hq : 1 < q) {θ r : ℝ} (hθr : (θ, r) ∈ cylinder q) (n : ℤ)
    {t : ℝ} (ht : t ∈ Ico (θ * q ^ (n - 1)) (θ * q ^ n)) (ω : ℝ) :
    knotAtomCascade q θ r (θ * q ^ n) ω =
      knotAtomCascade q θ r t ω + (1 - Real.cos (ω * (r * θ * q ^ n))) := by
  have hq0 : 0 < q := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθr.1.1
  have ht' : t ∈ Ico (θ * q ^ (n - 1)) (θ * q ^ (n - 1 + 1)) := by rwa [sub_add_cancel]
  have hle1 : ∀ m : ℤ, θ * q ^ m ≤ θ * q ^ n ↔ m ≤ n := fun m => by
    rw [mul_le_mul_iff_of_pos_left hθ0, zpow_le_zpow_iff_right₀ hq]
  have hs1 := knot_summable hq hθr t ω
  have hs2 : Summable fun m : ℤ =>
      if m = n then 1 - Real.cos (ω * (r * θ * q ^ n)) else 0 :=
    (hasSum_ite_eq n _).summable
  rw [knotAtomCascade, knotAtomCascade,
    ← tsum_ite_eq n (fun _ => 1 - Real.cos (ω * (r * θ * q ^ n))),
    ← hs1.tsum_add hs2]
  refine tsum_congr fun m => ?_
  rcases lt_trichotomy m n with hmn | rfl | hmn
  · rw [if_pos ((hle1 m).2 hmn.le), if_pos ((knot_le_iff hq hθ0 ht' m).2 (by omega)),
      if_neg hmn.ne, add_zero]
  · rw [if_pos le_rfl, if_neg (fun h => by have := (knot_le_iff hq hθ0 ht' m).1 h; omega),
      if_pos rfl, zero_add]
  · rw [if_neg (fun h => by have := (hle1 m).1 h; omega),
      if_neg (fun h => by have := (knot_le_iff hq hθ0 ht' m).1 h; omega), if_neg hmn.ne', add_zero]

/-- **`thm:knot-atom-cascades`(4), the cascades.** A knot-atom cascade is constant between
consecutive knots `θqⁿ`; at each knot it gains `1 - cos(ω rθqⁿ)`, so its kernel is convolved with
`exp[δ²_{rθqⁿ}]`, the compound Poisson law of unit rate with jumps `±rθqⁿ`; and it violates (I2):
no family of laws with (I1), (I2) has these kernels. -/
theorem knot_atom_cascades_4 {q : ℝ} (hq : 1 < q) (θ r : ℝ) (hθr : (θ, r) ∈ cylinder q) :
    (∀ n : ℤ, ∀ t ∈ Ico (θ * q ^ n) (θ * q ^ (n + 1)), ∀ t' ∈ Ico (θ * q ^ n) (θ * q ^ (n + 1)),
        knotAtomCascade q θ r t = knotAtomCascade q θ r t') ∧
      (∀ n : ℤ, ∀ t ∈ Ico (θ * q ^ (n - 1)) (θ * q ^ n), ∀ ω : ℝ,
        knotAtomCascade q θ r (θ * q ^ n) ω =
          knotAtomCascade q θ r t ω + (1 - Real.cos (ω * (r * θ * q ^ n)))) ∧
      (∀ K : ℝ → Measure ℝ, (∀ t : ℝ, IsProbabilityMeasure (K t) ∧ ∀ ω : ℝ,
          charFun (K t) ω = ((Real.exp (-knotAtomCascade q θ r t ω) : ℝ) : ℂ)) →
        ∀ n : ℤ, ∀ t ∈ Ico (θ * q ^ (n - 1)) (θ * q ^ n),
          K (θ * q ^ n) = K t ∗ randomWalkLaw 1 (r * θ * q ^ n)) ∧
      ¬ ∃ μ : ℝ → ℝ → Measure ℝ, IsLawHemigroup μ ∧ ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ,
        charFun (μ 0 t) ω = ((Real.exp (-knotAtomCascade q θ r t ω) : ℝ) : ℂ) := by
  have hq0 : 0 < q := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθr.1.1
  have hr : 0 < r := hθr.2
  have hconst : ∀ n : ℤ, ∀ t ∈ Ico (θ * q ^ n) (θ * q ^ (n + 1)),
      ∀ t' ∈ Ico (θ * q ^ n) (θ * q ^ (n + 1)),
        knotAtomCascade q θ r t = knotAtomCascade q θ r t' := by
    intro n t ht t' ht'
    funext ω
    unfold knotAtomCascade
    refine tsum_congr fun m => ?_
    simp only [knot_le_iff hq hθ0 ht, knot_le_iff hq hθ0 ht']
  refine ⟨hconst, fun n t ht ω => knotAtomCascade_jump hq hθr n ht ω, ?_, ?_⟩
  · intro K hK n t ht
    haveI : ∀ s, IsProbabilityMeasure (K s) := fun s => (hK s).1
    haveI := isProbabilityMeasure_randomWalkLaw zero_le_one (r * θ * q ^ n)
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_conv, (hK _).2, (hK _).2, charFun_randomWalkLaw zero_le_one,
      knotAtomCascade_jump hq hθr n ht ω, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    rw [mul_comm (r * θ * q ^ n) ω]
    ring
  · rintro ⟨μ, hμ, hchar⟩
    -- the knot `θ = θq⁰`, approached from below through `[θq^{-1}, θ)`
    set ω₀ : ℝ := Real.pi / (r * θ) with hω₀
    set t₀ : ℝ := θ * q ^ (-1 : ℤ) with ht₀
    have ht₀pos : 0 < t₀ := mul_pos hθ0 (zpow_pos hq0 _)
    have ht₀lt : t₀ < θ := by
      rw [ht₀, zpow_neg_one]
      exact mul_lt_of_lt_one_right hθ0 (inv_lt_one_of_one_lt₀ hq)
    have hmem : ∀ t ∈ Ico t₀ θ, t ∈ Ico (θ * q ^ ((0 : ℤ) - 1)) (θ * q ^ (0 : ℤ)) := by
      intro t ht
      simpa [ht₀] using ht
    set g : ℝ → ℂ := fun t => charFun (μ 0 t) ω₀ with hg
    have hgc : ContinuousOn g (Ici 0) :=
      (hμ.continuous ω₀).comp (continuous_const.prodMk continuous_id).continuousOn
        fun t ht => ⟨le_rfl, ht⟩
    have hgconst : ∀ t ∈ Ico t₀ θ, g t = g t₀ := by
      intro t ht
      simp only [hg]
      rw [hchar t (ht₀pos.le.trans ht.1), hchar t₀ ht₀pos.le,
        hconst (-1) t (by simpa using hmem t ht) t₀ (by simpa using hmem t₀ ⟨le_rfl, ht₀lt⟩)]
    have hlim : g θ = g t₀ := by
      have hcw : ContinuousWithinAt g (Ico t₀ θ) θ :=
        (hgc θ hθ0.le).mono fun t ht => ht₀pos.le.trans ht.1
      have h1 : Tendsto g (𝓝[Ico t₀ θ] θ) (𝓝 (g θ)) := hcw.tendsto
      have h2 : Tendsto g (𝓝[Ico t₀ θ] θ) (𝓝 (g t₀)) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hgconst t ht).symm)
      haveI : (𝓝[Ico t₀ θ] θ).NeBot := by
        rw [nhdsWithin_Ico_eq_nhdsLT ht₀lt]; infer_instance
      exact tendsto_nhds_unique h1 h2
    have hjump := knotAtomCascade_jump hq hθr 0 (hmem t₀ ⟨le_rfl, ht₀lt⟩) ω₀
    have hcos : Real.cos (ω₀ * (r * θ * q ^ (0 : ℤ))) = -1 := by
      rw [zpow_zero, mul_one, hω₀, div_mul_cancel₀ _ (mul_pos hr hθ0).ne', Real.cos_pi]
    rw [hcos, zpow_zero, mul_one] at hjump
    simp only [hg] at hlim
    rw [hchar θ hθ0.le, hchar t₀ ht₀pos.le, hjump] at hlim
    have h3 := Real.exp_injective (Complex.ofReal_injective hlim)
    linarith

/-- **`thm:knot-atom-cascades`(4), the knot Gaussians.** `ℬ^{(θ)}` jumps by `(θqⁿ)²` at each knot
`θqⁿ`, so it has atoms, and no pair with (i)–(iv) has it: a knot Gaussian is not a family. -/
theorem knot_atom_cascades_4_gaussian {q : ℝ} (hq : 1 < q) (θ : ℝ) (hθ : θ ∈ Ico 1 q) :
    (∀ n : ℤ, knotGaussian q θ {θ * q ^ n} = ENNReal.ofReal ((θ * q ^ n) ^ 2)) ∧
      ∀ Λ : Measure (ℝ × ℝ), ¬ IsSurfacePair q Λ (knotGaussian q θ) := by
  have hq0 : 0 < q := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
  have hatom : ∀ n : ℤ, knotGaussian q θ {θ * q ^ n} = ENNReal.ofReal ((θ * q ^ n) ^ 2) := by
    intro n
    rw [knotGaussian, Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single n]
    · rw [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton _), smul_eq_mul, mul_one]
    · intro m hm
      rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
        indicator_of_notMem, smul_zero]
      intro h
      have h' : θ * q ^ m = θ * q ^ n := h
      exact hm (zpow_right_injective₀ hq0 hq.ne' (mul_left_cancel₀ hθ0.ne' h'))
  refine ⟨hatom, fun Λ h => ?_⟩
  have h1 := (h.no_line θ hθ0).2
  have h2 := hatom 0
  rw [zpow_zero, mul_one, h1] at h2
  exact (ENNReal.ofReal_pos.2 (by positivity : (0 : ℝ) < θ ^ 2)).ne h2

/-- **`thm:knot-atom-cascades`(4), the families.** For `σ` on `𝒞` and `ℬ` with (ii), the pair
`(Λ_σ, ℬ)` is a family's iff (A.e3), `σ({θ} × (0,∞)) = 0` for every `θ`, `β` has no atoms, and
(iv) holds. -/
theorem knot_atom_cascades_4_families {q : ℝ} (hq : 1 < q) (σ : Measure (ℝ × ℝ))
    (hσ : σ (cylinder q)ᶜ = 0) (B : Measure ℝ) (hB : IsSurfaceGaussian q B) :
    IsSurfacePair q (orbitMixture q σ) B ↔
      IsCylIntegrable σ ∧ (∀ θ : ℝ, σ ({θ} ×ˢ Ioi 0) = 0) ∧
        (∀ y : ℝ, B.restrict (Ico 1 q) {y} = 0) ∧
        ∀ s t : ℝ, 0 < s → s < t → 0 < orbitMixture q σ (Ioc s t ×ˢ Ioi 0) + B (Ioc s t) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hint, hline⟩ := knot_atom_cascades_2_integrable hq σ hσ
  obtain ⟨hc, hinv, -⟩ := orbitMixture_spec hq hσ
  constructor
  · intro h
    refine ⟨hint.1 h.integrable, hline.1 fun y hy => (h.no_line y hy).1, fun y => ?_, h.nondeg⟩
    rw [Measure.restrict_apply (measurableSet_singleton y)]
    by_cases hy : y ∈ Ico 1 q
    · exact measure_mono_null inter_subset_left
        (h.no_line y (lt_of_lt_of_le one_pos hy.1)).2
    · rw [singleton_inter_eq_empty.2 hy, measure_empty]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨hc, hinv, hint.2 h1, hB, fun y hy => ⟨hline.2 h2 y hy, ?_⟩, h4⟩
    rw [← (knot_atom_cascades_2_gaussian hq).1 B hB,
      gaussSpread_apply q _ (measurableSet_singleton y),
      ENNReal.tsum_eq_zero]
    intro n
    have e : (fun x => q ^ n * x) ⁻¹' {y} = {y / q ^ n} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro hx
        rw [← hx, mul_div_cancel_left₀ _ (zpow_pos hq0 n).ne']
      · intro hx
        rw [hx, mul_div_cancel₀ _ (zpow_pos hq0 n).ne']
    rw [e, h3, mul_zero]

end Pyramids
