/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.CirclePhase

/-!
# `prop:strata-cylinder-coordinates`, part B: the jump part's equivalences, (3)

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:strata-cylinder-coordinates`. Wave 3c: the
declarations `strata_cylinder_1_jump` and `strata_cylinder_3` moved here from
`PyramidsSkeleton.ChA1Line`, unchanged in statement. The node's other five declarations are in
`StrataCylinder.lean` and `StrataCylinderParts.lean`.

## The route

* **(a) ⟺ (b).** `(J_λ)_*Λ` has the slabs `T_λ Λ((0,t/λ] × ·)` (`slab_map_scaleDiag`), and a
  measure on the quadrant is determined by its slabs (`quadrant_measure_ext`).
* **Dilations on the cylinder.** For `σ` on the cylinder and `λ > 0`, the cylinder measure of
  `(J_λ)_*Λ_σ` is the image of `σ` under the rotation `(θ, r) ↦ ([λθ], r)`
  (`cylMeasure_map_scaleDiag`): of the points `(λθqⁿ, λrθqⁿ)` of the dilated orbit exactly one
  lies in `[1,q) × (0,∞)`, at `n = -⌊log_q λθ⌋`, and it is `([λθ], λrθqⁿ)`, with ratio `r`.
* **(c) ⟹ (b).** `Λ_{η⊗ρ̃}` is the image of `(dy/(ℓy)) ⊗ ρ̃` under `(y, r) ↦ (y, ry)`, and
  `dy/(ℓy)` is invariant under `y ↦ λy` (`orbitMixture_haarPhase_prod_map_scaleDiag`).
* **`η` is rotation invariant**, so its coefficients `j ≠ 0` vanish (`phaseCoeff_haarPhase`): the
  two facts above for `σ = η ⊗ δ₁`.
* **The slices.** For a compact `A ⊂ (0,∞)` the measure `E ↦ σ(E × A)` on `[1,q)`
  (`phaseSlice`) is finite (`rMarginal_Ici_ne_top`); if its coefficients `j ≠ 0` vanish it is
  `ρ̃(A) η` (`eq_smul_haarPhase_of_phaseCoeff`, Fourier uniqueness through `CirclePhase`). If this
  holds for every compact `A`, then `σ(E × A) = η(E) ρ̃(A)` for all Borel `E, A`
  (`measure_ext_of_Icc_pos`), and `σ = η ⊗ ρ̃` (`eq_prod_of_phaseSlice`).
* **(b) ⟹ (c).** Under (b) every slice is rotation invariant, so its coefficients `j ≠ 0` vanish.
* **(3).** The coefficients `σ̂_j(A)` are those of the slice; the spectrum is empty iff they vanish
  for every compact `A`; and for `σ = η ⊗ ρ̃`, `σ̂_j(A) = η̂_j ρ̃(A) = 0`.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter
open scoped ENNReal NNReal

/-! ## Rotations of the cylinder -/

/-- **`(θ, r) ↦ ([λθ], r)`**, the rotation of the cylinder by `λ`. -/
noncomputable def rotPair (q lam : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (qRot q lam p.1, p.2)

theorem measurable_rotPair (q lam : ℝ) : Measurable (rotPair q lam) :=
  ((measurable_qRot q lam).comp measurable_fst).prodMk measurable_snd

/-- **The cylinder measure of a dilated mixture is the rotated cylinder measure.** -/
theorem cylMeasure_map_scaleDiag {q : ℝ} (hq : 1 < q) {σ : Measure (ℝ × ℝ)}
    (hσ : σ (cylinder q)ᶜ = 0) {lam : ℝ} (hlam : 0 < lam) :
    cylMeasure q ((orbitMixture q σ).map (scaleDiag lam)) = σ.map (rotPair q lam) := by
  have hq0 : 0 < q := by linarith
  ext s hs
  have hm : MeasurableSet (cylMap ⁻¹' s ∩ cylinder q) :=
    (measurable_cylMap hs).inter (measurableSet_cylinder q)
  rw [cylMeasure_apply q _ hs, Measure.map_apply (measurable_scaleDiag lam) hm,
    orbitMixture_apply q σ (measurable_scaleDiag lam hm),
    Measure.map_apply (measurable_rotPair q lam) hs]
  set S : ℤ → Set (ℝ × ℝ) :=
    fun n => orbitPt q n ⁻¹' (scaleDiag lam ⁻¹' (cylMap ⁻¹' s ∩ cylinder q)) with hS
  have hSm : ∀ n, MeasurableSet (S n) :=
    fun n => measurable_orbitPt q n (measurable_scaleDiag lam hm)
  -- on the cylinder, `S n` is `{n = -⌊log_q λθ⌋}` intersected with the rotated `s`
  have key : ∀ p ∈ cylinder q, ∀ n : ℤ,
      p ∈ S n ↔ (n = -dgLevel q (lam * p.1) ∧ rotPair q lam p ∈ s) := by
    rintro ⟨θ, r⟩ ⟨hθ, hr⟩ n
    have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
    have hy : 0 < lam * θ := mul_pos hlam hθ0
    have hqn : 0 < q ^ n := zpow_pos hq0 n
    have hr' : (0 : ℝ) < r := hr
    have e1 : scaleDiag lam (orbitPt q n (θ, r)) =
        (q ^ n * (lam * θ), r * (q ^ n * (lam * θ))) := by
      simp only [scaleDiag, orbitPt, Prod.mk.injEq]
      constructor <;> ring
    have e2 : cylMap (q ^ n * (lam * θ), r * (q ^ n * (lam * θ))) = (q ^ n * (lam * θ), r) := by
      simp only [cylMap]
      rw [mul_div_cancel_right₀ _ (mul_pos hqn hy).ne']
    have hmem : q ^ n * (lam * θ) ∈ Ico 1 q ↔ n = -dgLevel q (lam * θ) :=
      ⟨fun h => (existsUnique_zpow_mul_mem_Ico hq hy).unique h (octave_mem hq hy),
        fun h => h ▸ octave_mem hq hy⟩
    simp only [hS, mem_preimage, mem_inter_iff, e1, e2]
    constructor
    · rintro ⟨hs', hc⟩
      have hn := hmem.1 hc.1
      subst hn
      exact ⟨rfl, hs'⟩
    · rintro ⟨hn, hs'⟩
      subst hn
      exact ⟨hs', octave_mem hq hy, mul_pos hr' (mul_pos hqn hy)⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun n => S n ∩ cylinder q) := by
    intro m n hmn
    refine Set.disjoint_left.2 fun p hm hn => hmn ?_
    rw [(key p hm.2 m).1 hm.1 |>.1, (key p hn.2 n).1 hn.1 |>.1]
  have hU : (⋃ n, S n ∩ cylinder q) = rotPair q lam ⁻¹' s ∩ cylinder q := by
    ext p
    simp only [mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨n, hn, hp⟩
      exact ⟨((key p hp n).1 hn).2, hp⟩
    · rintro ⟨hps, hp⟩
      exact ⟨-dgLevel q (lam * p.1), (key p hp _).2 ⟨rfl, hps⟩, hp⟩
  calc ∑' n, σ (S n) = ∑' n, σ (S n ∩ cylinder q) := by
        congr 1
        funext n
        rw [measure_inter_conull hσ]
    _ = σ (⋃ n, S n ∩ cylinder q) :=
        (measure_iUnion hdisj fun n => (hSm n).inter (measurableSet_cylinder q)).symm
    _ = σ (rotPair q lam ⁻¹' s) := by rw [hU, measure_inter_conull hσ]

/-- `dy/(ℓy)` is invariant under `y ↦ cy`. -/
theorem map_logHaar_mul (q : ℝ) {c : ℝ} (hc : 0 < c) :
    (logHaar q).map (fun y => c * y) = logHaar q := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul c) hs,
    ← lintegral_indicator_one (measurable_const_mul c hs), ← lintegral_indicator_one hs]
  exact lintegral_logHaar_comp_mul q hc (measurable_one.indicator hs)

/-- **`Λ_{η⊗ρ̃}` is invariant under every `J_λ`.** -/
theorem orbitMixture_haarPhase_prod_map_scaleDiag {q : ℝ} (hq : 1 < q) (ρ : Measure ℝ)
    [SFinite ρ] {lam : ℝ} (hlam : 0 < lam) :
    (orbitMixture q ((haarPhase q).prod ρ)).map (scaleDiag lam) =
      orbitMixture q ((haarPhase q).prod ρ) := by
  have hf : Measurable fun p : ℝ × ℝ => (p.1, p.2 * p.1) := by fun_prop
  have hpm : Measurable (Prod.map (fun y : ℝ => lam * y) (id : ℝ → ℝ)) :=
    (measurable_const_mul lam).prodMap measurable_id
  have hP : ((logHaar q).prod ρ).map (Prod.map (fun y => lam * y) id) = (logHaar q).prod ρ := by
    ext s hs
    rw [Measure.map_apply hpm hs, Measure.prod_apply_symm (hpm hs), Measure.prod_apply_symm hs]
    refine lintegral_congr fun r => ?_
    conv_rhs => rw [← map_logHaar_mul q hlam]
    rw [Measure.map_apply (measurable_const_mul lam) (measurable_prodMk_right hs)]
    rfl
  have e : scaleDiag lam ∘ (fun p : ℝ × ℝ => (p.1, p.2 * p.1)) =
      (fun p : ℝ × ℝ => (p.1, p.2 * p.1)) ∘ Prod.map (fun y => lam * y) id := by
    funext p
    simp only [Function.comp_apply, scaleDiag, Prod.map_fst, Prod.map_snd, id, Prod.mk.injEq,
      true_and]
    ring
  rw [orbitMixture_haarPhase_prod hq ρ, Measure.map_map (measurable_scaleDiag lam) hf, e,
    ← Measure.map_map hf hpm, hP]

/-! ## The Haar measure `η` of the circle -/

theorem haarPhase_compl_Ico (q : ℝ) : haarPhase q (Ico 1 q)ᶜ = 0 := by
  rw [haarPhase_eq_restrict, Measure.restrict_apply measurableSet_Ico.compl, compl_inter_self,
    measure_empty]

theorem haarPhase_Iic (q : ℝ) : haarPhase q (Iic 0) = 0 := by
  refine measure_mono_null ?_ (haarPhase_compl_Ico q)
  intro x hx hxI
  exact not_lt.2 (mem_Iic.1 hx) (lt_of_lt_of_le one_pos hxI.1)

/-- **`η` is invariant under every rotation `θ ↦ [λθ]`.** -/
theorem map_qRot_haarPhase {q : ℝ} (hq : 1 < q) {lam : ℝ} (hlam : 0 < lam) :
    (haarPhase q).map (qRot q lam) = haarPhase q := by
  haveI := isProbabilityMeasure_haarPhase hq
  set σ₀ : Measure (ℝ × ℝ) := (haarPhase q).prod (Measure.dirac (1 : ℝ)) with hσ₀def
  have hσ₀ : σ₀ (cylinder q)ᶜ = 0 := by
    have hsub : (cylinder q)ᶜ ⊆ (Ico 1 q)ᶜ ×ˢ univ ∪ univ ×ˢ (Ioi 0)ᶜ := by
      intro p hp
      simp only [cylinder, mem_compl_iff, mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, mem_univ _⟩
      · exact Or.inr ⟨mem_univ _, hp⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · rw [hσ₀def, Measure.prod_prod, haarPhase_compl_Ico, zero_mul]
    · rw [hσ₀def, Measure.prod_prod, Measure.dirac_apply' _ measurableSet_Ioi.compl,
        indicator_of_notMem (by simp), mul_zero]
  obtain ⟨-, -, hcyl⟩ := orbitMixture_spec hq hσ₀
  have hrot : σ₀.map (rotPair q lam) = σ₀ := by
    rw [← cylMeasure_map_scaleDiag hq hσ₀ hlam, hσ₀def,
      orbitMixture_haarPhase_prod_map_scaleDiag hq _ hlam, ← hσ₀def, hcyl]
  have hfst : σ₀.map Prod.fst = haarPhase q := by
    rw [hσ₀def, Measure.map_fst_prod, measure_univ, one_smul]
  have hcomp : Prod.fst ∘ rotPair q lam = qRot q lam ∘ Prod.fst := rfl
  calc (haarPhase q).map (qRot q lam) = (σ₀.map Prod.fst).map (qRot q lam) := by rw [hfst]
    _ = (σ₀.map (rotPair q lam)).map Prod.fst := by
        rw [Measure.map_map (measurable_qRot q lam) measurable_fst,
          Measure.map_map measurable_fst (measurable_rotPair q lam), hcomp]
    _ = haarPhase q := by rw [hrot, hfst]

/-- **The coefficients `j ≠ 0` of `η` vanish**: `∫ e^{2πij log_q θ} dθ/(ℓθ) = 0`. -/
theorem phaseCoeff_haarPhase {q : ℝ} (hq : 1 < q) {j : ℤ} (hj : j ≠ 0) :
    phaseCoeff q (haarPhase q) j = 0 :=
  phaseCoeff_eq_zero_of_invariant hq (haarPhase_Iic q)
    (fun _ hlam => map_qRot_haarPhase hq hlam) hj

/-- **A finite measure on `[1,q)` whose coefficients `j ≠ 0` vanish is a multiple of `η`.** -/
theorem eq_smul_haarPhase_of_phaseCoeff {q : ℝ} (hq : 1 < q) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ν (Ico 1 q)ᶜ = 0) (h : ∀ j : ℤ, j ≠ 0 → phaseCoeff q ν j = 0) :
    ν = ν univ • haarPhase q := by
  haveI := isProbabilityMeasure_haarPhase hq
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  haveI : IsFiniteMeasure (ν univ • haarPhase q) :=
    ⟨by
      rw [Measure.smul_apply, measure_univ (μ := haarPhase q), smul_eq_mul, mul_one]
      exact measure_lt_top ν univ⟩
  refine eq_of_map_phaseMap hq hν ?_ ?_
  · rw [Measure.smul_apply, haarPhase_compl_Ico, smul_zero]
  · refine addCircle_measure_ext fun n => ?_
    rw [integral_fourier_map_phaseMap, integral_fourier_map_phaseMap]
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [phaseCoeff, phaseChar_zero, integral_const, smul_eq_mul, mul_one,
        Measure.real, Measure.smul_apply, measure_univ]
    · rw [h n hn, phaseCoeff, integral_smul_measure, ← phaseCoeff, phaseCoeff_haarPhase hq hn,
        smul_zero]

/-! ## Slices, and the product -/

/-- **The slice `E ↦ σ(E × A)`.** -/
noncomputable def phaseSlice (σ : Measure (ℝ × ℝ)) (A : Set ℝ) : Measure ℝ :=
  (σ.restrict (univ ×ˢ A)).map Prod.fst

theorem phaseSlice_apply (σ : Measure (ℝ × ℝ)) (A : Set ℝ) {E : Set ℝ} (hE : MeasurableSet E) :
    phaseSlice σ A E = σ (E ×ˢ A) := by
  rw [phaseSlice, Measure.map_apply measurable_fst hE, Measure.restrict_apply (measurable_fst hE)]
  congr 1
  ext p
  simp [mem_prod]

/-- The slice of the rotated measure is the rotated slice. -/
theorem phaseSlice_map_qRot (q lam : ℝ) (σ : Measure (ℝ × ℝ)) {A : Set ℝ} (hA : MeasurableSet A) :
    (phaseSlice σ A).map (qRot q lam) = phaseSlice (σ.map (rotPair q lam)) A := by
  ext E hE
  rw [Measure.map_apply (measurable_qRot q lam) hE,
    phaseSlice_apply _ _ (measurable_qRot q lam hE), phaseSlice_apply _ _ hE,
    Measure.map_apply (measurable_rotPair q lam) (hE.prod hA)]
  rfl

/-- A compact subset of `(0,∞)` lies in some `[ε,∞)`, `ε > 0`. -/
theorem exists_pos_subset_Ici {A : Set ℝ} (hA : IsCompact A) (hA0 : A ⊆ Ioi 0) :
    ∃ ε : ℝ, 0 < ε ∧ A ⊆ Ici ε := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, empty_subset _⟩
  · obtain ⟨x, hx, hmin⟩ := hA.exists_isMinOn hne continuousOn_id
    exact ⟨x, hA0 hx, fun y hy => (isMinOn_iff.1 hmin) y hy⟩

/-- **Two measures on `(0,∞)` that agree on every `[a,b]`, `a > 0`, are equal**, when the first
is finite on every `[ε,∞)`. -/
theorem measure_ext_of_Icc_pos {m₁ m₂ : Measure ℝ} (h₁ : m₁ (Iic 0) = 0) (h₂ : m₂ (Iic 0) = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → m₁ (Ici ε) ≠ ⊤)
    (h : ∀ a b : ℝ, 0 < a → m₁ (Icc a b) = m₂ (Icc a b)) : m₁ = m₂ := by
  have hres : ∀ ε : ℝ, 0 < ε → m₁.restrict (Ici ε) = m₂.restrict (Ici ε) := by
    intro ε hε
    refine Measure.ext_of_Icc' _ _ (fun a b _ => ?_) (fun a b _ => ?_)
    · rw [Measure.restrict_apply measurableSet_Icc]
      exact ne_top_of_le_ne_top (hfin ε hε) (measure_mono inter_subset_right)
    · have hI : Icc a b ∩ Ici ε = Icc (max a ε) b := by
        ext x
        simp only [mem_inter_iff, mem_Icc, mem_Ici, max_le_iff]
        tauto
      rw [Measure.restrict_apply measurableSet_Icc, Measure.restrict_apply measurableSet_Icc, hI]
      exact h _ _ (lt_max_of_lt_right hε)
  ext S hS
  set T : ℕ → Set ℝ := fun n => S ∩ Ici (1 / ((n : ℝ) + 1)) with hT
  have hmono : Monotone T := by
    intro m n hmn
    refine inter_subset_inter_right _ (Ici_subset_Ici.2 ?_)
    gcongr
  have hU : S ∩ Ioi 0 = ⋃ n, T n := by
    ext x
    simp only [hT, mem_inter_iff, mem_Ioi, mem_iUnion, mem_Ici]
    constructor
    · rintro ⟨hxS, hx⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, hxS, hn.le⟩
    · rintro ⟨n, hxS, hn⟩
      exact ⟨hxS, lt_of_lt_of_le (by positivity) hn⟩
  rw [← measure_inter_conull (t := Ioi 0) (by rwa [compl_Ioi]),
    ← measure_inter_conull (μ := m₂) (s := S) (t := Ioi 0) (by rwa [compl_Ioi]), hU,
    hmono.measure_iUnion, hmono.measure_iUnion]
  refine iSup_congr fun n => ?_
  rw [hT, ← Measure.restrict_apply' measurableSet_Ici, ← Measure.restrict_apply' measurableSet_Ici,
    hres _ (by positivity)]

/-- **A measure on the cylinder whose compact slices have no coefficient `j ≠ 0` is
`η ⊗ ρ̃`.** -/
theorem eq_prod_of_phaseSlice {q : ℝ} (hq : 1 < q) {σ : Measure (ℝ × ℝ)}
    (hσ : σ (cylinder q)ᶜ = 0) (hint : IsCylIntegrable σ)
    (h : ∀ A : Set ℝ, IsCompact A → A ⊆ Ioi 0 → ∀ j : ℤ, j ≠ 0 →
      phaseCoeff q (phaseSlice σ A) j = 0) :
    σ = (haarPhase q).prod (rMarginal q σ) := by
  set ρ := rMarginal q σ with hρdef
  have hρA : ∀ A : Set ℝ, MeasurableSet A → ρ A = σ (univ ×ˢ A) := by
    intro A hA
    rw [hρdef, rMarginal_eq_map hσ, Measure.map_apply measurable_snd hA, univ_prod]
  have hfin : ∀ ε : ℝ, 0 < ε → ρ (Ici ε) ≠ ⊤ := fun ε hε => rMarginal_Ici_ne_top hσ hint hε
  have hρ0 : ρ (Iic 0) = 0 := rMarginal_Iic hσ
  haveI : SigmaFinite ρ := sigmaFinite_of_Ioi hρ0
    fun ε hε => ne_top_of_le_ne_top (hfin ε hε) (measure_mono Ioi_subset_Ici_self)
  haveI := isProbabilityMeasure_haarPhase hq
  -- the compact slices
  have hcpt : ∀ A : Set ℝ, IsCompact A → A ⊆ Ioi 0 → ∀ E : Set ℝ, MeasurableSet E →
      σ (E ×ˢ A) = haarPhase q E * ρ A := by
    intro A hA hA0 E hE
    obtain ⟨ε, hε, hAε⟩ := exists_pos_subset_Ici hA hA0
    haveI : IsFiniteMeasure (phaseSlice σ A) := by
      refine ⟨?_⟩
      rw [phaseSlice_apply σ A MeasurableSet.univ]
      refine lt_of_le_of_lt (measure_mono (prod_mono subset_rfl hAε)) ?_
      rw [← hρA _ measurableSet_Ici]
      exact (hfin ε hε).lt_top
    have hcar : phaseSlice σ A (Ico 1 q)ᶜ = 0 := by
      rw [phaseSlice_apply _ _ measurableSet_Ico.compl]
      refine measure_mono_null ?_ hσ
      intro p hp hc
      exact hp.1 hc.1
    have hs := eq_smul_haarPhase_of_phaseCoeff hq hcar (h A hA hA0)
    rw [← phaseSlice_apply σ A hE, hs, Measure.smul_apply, smul_eq_mul,
      phaseSlice_apply σ A MeasurableSet.univ, hρA A hA.measurableSet, mul_comm]
  -- every rectangle
  have hall : ∀ E : Set ℝ, MeasurableSet E → ∀ A : Set ℝ, MeasurableSet A →
      σ (E ×ˢ A) = haarPhase q E * ρ A := by
    intro E hE
    set m₁ : Measure ℝ := (σ.restrict (E ×ˢ univ)).map Prod.snd with hm₁def
    have hm₁ : ∀ A : Set ℝ, MeasurableSet A → m₁ A = σ (E ×ˢ A) := by
      intro A hA
      rw [hm₁def, Measure.map_apply measurable_snd hA,
        Measure.restrict_apply (measurable_snd hA)]
      congr 1
      ext p
      simp [mem_prod, and_comm]
    have heq : m₁ = haarPhase q E • ρ := by
      refine measure_ext_of_Icc_pos ?_ ?_ (fun ε hε => ?_) (fun a b ha => ?_)
      · rw [hm₁ _ measurableSet_Iic]
        refine measure_mono_null ?_ hσ
        intro p hp hc
        exact not_lt.2 (mem_Iic.1 hp.2) hc.2
      · rw [Measure.smul_apply, hρ0, smul_zero]
      · rw [hm₁ _ measurableSet_Ici]
        refine ne_top_of_le_ne_top (hfin ε hε) ?_
        rw [hρA _ measurableSet_Ici]
        exact measure_mono (prod_mono (subset_univ _) subset_rfl)
      · rw [hm₁ _ measurableSet_Icc, Measure.smul_apply, smul_eq_mul]
        exact hcpt _ isCompact_Icc (fun x hx => lt_of_lt_of_le ha hx.1) E hE
    intro A hA
    rw [← hm₁ A hA, heq, Measure.smul_apply, smul_eq_mul]
  exact (Measure.prod_eq fun E A hE hA => hall E hE A hA).symm

/-! ## The jump part -/

/-- **`prop:strata-cylinder-coordinates`(1), the jump part.** For a pair `(Λ, ℬ)` with (i)–(iv):
(a) `ϖ_{λt} = T_λ ϖ_t` for all `λ, t > 0` iff (b) `(J_λ)_* Λ = Λ` for every `λ > 0`, iff
(c) `σ = η ⊗ ρ̃` for a measure `ρ̃` on `(0,∞)`, read as an s-finite one: the `ρ̃` of the node is
σ-finite (null on `(-∞,0]`, finite on every `[x,∞)`), and the witness the proof builds is. -/
theorem strata_cylinder_1_jump {q : ℝ} (hq : 1 < q) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (h : IsSurfacePair q Λ B) :
    ((∀ lam t : ℝ, 0 < lam → 0 < t → slab Λ 0 (lam * t) = (slab Λ 0 t).map (fun v => lam * v)) ↔
        ∀ lam : ℝ, 0 < lam → Λ.map (scaleDiag lam) = Λ) ∧
      ((∀ lam : ℝ, 0 < lam → Λ.map (scaleDiag lam) = Λ) ↔
        ∃ ρ : Measure ℝ, SFinite ρ ∧ ρ (Iic 0) = 0 ∧ cylMeasure q Λ = (haarPhase q).prod ρ) := by
  obtain ⟨hσ, hmix⟩ := cylMeasure_spec hq h.carried h.invariant
  have hint : IsCylIntegrable (cylMeasure q Λ) := by
    refine (knot_atom_cascades_2_integrable hq _ hσ).1.1 ?_
    rw [hmix]
    exact h.integrable
  refine ⟨⟨fun ha lam hlam => ?_, fun hb lam t hlam ht => ?_⟩, ⟨fun hb => ?_, ?_⟩⟩
  · -- (a) gives (b): the slabs of `(J_λ)_*Λ` are those of `Λ`
    have hc' : Λ.map (scaleDiag lam) quadrantᶜ = 0 := by
      rw [Measure.map_apply (measurable_scaleDiag lam) measurableSet_quadrant.compl,
        preimage_compl, scaleDiag_preimage_quadrant hlam, h.carried]
    refine (quadrant_measure_ext h.carried hc'
      (fun t ht ε hε => SymLevyPair_measure_Ioi_ne_top
        (surfacePairOf Λ B t h.carried (h.integrable t ht)) hε) fun t ht => ?_).symm
    rw [slab_map_scaleDiag hlam, zero_div, ← ha lam (t / lam) hlam (div_pos ht hlam),
      mul_div_cancel₀ _ hlam.ne']
  · -- (b) gives (a)
    conv_lhs => rw [← hb lam hlam]
    rw [slab_map_scaleDiag hlam, zero_div, mul_div_cancel_left₀ _ hlam.ne']
  · -- (b) gives (c): every slice is rotation invariant
    refine ⟨rMarginal q (cylMeasure q Λ), sFinite_rMarginal hσ hint, rMarginal_Iic hσ, ?_⟩
    refine eq_prod_of_phaseSlice hq hσ hint fun A hA _ j hj => ?_
    refine phaseCoeff_eq_zero_of_invariant hq ?_ (fun lam hlam => ?_) hj
    · rw [phaseSlice_apply _ _ measurableSet_Iic]
      refine measure_mono_null ?_ hσ
      intro p hp hc
      exact not_lt.2 (mem_Iic.1 hp.1) (lt_of_lt_of_le one_pos hc.1.1)
    · have hrot : (cylMeasure q Λ).map (rotPair q lam) = cylMeasure q Λ := by
        rw [← cylMeasure_map_scaleDiag hq hσ hlam, hmix, hb lam hlam]
      rw [phaseSlice_map_qRot q lam _ hA.measurableSet, hrot]
  · -- (c) gives (b)
    rintro ⟨ρ, hρs, -, hρ⟩ lam hlam
    rw [← hmix, hρ]
    exact orbitMixture_haarPhase_prod_map_scaleDiag hq ρ hlam

/-! ## (3), the modulation spectrum -/

/-- `σ̂_j(A)` is the `j`-th coefficient of the slice `E ↦ σ(E × A)`. -/
theorem modulationCoeff_eq_phaseCoeff {q : ℝ} {σ : Measure (ℝ × ℝ)} (hσ : σ (cylinder q)ᶜ = 0)
    (j : ℤ) {A : Set ℝ} (hA : MeasurableSet A) :
    modulationCoeff q σ j A = phaseCoeff q (phaseSlice σ A) j := by
  have hσI : σ.restrict (Ico 1 q ×ˢ univ) = σ :=
    Measure.restrict_eq_self_of_ae_mem ((ae_mem_cylinder hσ).mono fun p hp => ⟨hp.1, mem_univ _⟩)
  have hres : σ.restrict (univ ×ˢ A) = σ.restrict (Ico 1 q ×ˢ A) := by
    conv_lhs => rw [← hσI]
    rw [Measure.restrict_restrict (MeasurableSet.univ.prod hA), prod_inter_prod, univ_inter,
      inter_univ]
  rw [modulationCoeff, phaseCoeff, phaseSlice, integral_map measurable_fst.aemeasurable
    (measurable_phaseChar q j).aestronglyMeasurable, hres]
  rfl

/-- **`prop:strata-cylinder-coordinates`(3).** For compact `A ⊂ (0,∞)`, `σ([1,q) × A) < ∞`; the
modulation spectrum is empty iff `σ = η ⊗ ρ̃` for some `ρ̃`, read as an s-finite one, as in
`strata_cylinder_1_jump`. -/
theorem strata_cylinder_3 {q : ℝ} (hq : 1 < q) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (h : IsSurfacePair q Λ B) :
    (∀ A : Set ℝ, IsCompact A → A ⊆ Ioi 0 → cylMeasure q Λ (Ico 1 q ×ˢ A) ≠ ⊤) ∧
      (modulationSpectrum q (cylMeasure q Λ) = ∅ ↔
        ∃ ρ : Measure ℝ, SFinite ρ ∧ ρ (Iic 0) = 0 ∧ cylMeasure q Λ = (haarPhase q).prod ρ) := by
  obtain ⟨hσ, hmix⟩ := cylMeasure_spec hq h.carried h.invariant
  have hint : IsCylIntegrable (cylMeasure q Λ) := by
    refine (knot_atom_cascades_2_integrable hq _ hσ).1.1 ?_
    rw [hmix]
    exact h.integrable
  refine ⟨fun A hA hA0 => ?_, ⟨fun hspec => ?_, ?_⟩⟩
  · -- finiteness on compacts
    obtain ⟨ε, hε, hAε⟩ := exists_pos_subset_Ici hA hA0
    refine ne_top_of_le_ne_top (rMarginal_Ici_ne_top hσ hint hε) ?_
    rw [rMarginal_eq_map hσ, Measure.map_apply measurable_snd measurableSet_Ici, ← univ_prod]
    exact measure_mono (prod_mono (subset_univ _) hAε)
  · -- an empty spectrum gives `σ = η ⊗ ρ̃`
    refine ⟨rMarginal q (cylMeasure q Λ), sFinite_rMarginal hσ hint, rMarginal_Iic hσ,
      eq_prod_of_phaseSlice hq hσ hint fun A hA hA0 j hj => ?_⟩
    rw [← modulationCoeff_eq_phaseCoeff hσ j hA.measurableSet]
    by_contra hne
    have hmem : j ∈ modulationSpectrum q (cylMeasure q Λ) := ⟨hj, A, hA, hA0, hne⟩
    rw [hspec] at hmem
    exact hmem
  · -- for `σ = η ⊗ ρ̃` every coefficient `j ≠ 0` vanishes
    rintro ⟨ρ, hρs, -, hρ⟩
    refine eq_empty_iff_forall_notMem.2 fun j ⟨hj, A, _, _, hne⟩ => hne ?_
    have hprod := setIntegral_prod_mul (μ := haarPhase q) (ν := ρ) (phaseChar q j)
      (fun _ => (1 : ℂ)) (Ico 1 q) A
    simp only [mul_one] at hprod
    rw [hρ, modulationCoeff]
    change ∫ p in Ico 1 q ×ˢ A, phaseChar q j p.1 ∂(haarPhase q).prod ρ = 0
    rw [hprod, haarPhase_eq_restrict, Measure.restrict_restrict measurableSet_Ico, inter_self,
      ← haarPhase_eq_restrict, ← phaseCoeff, phaseCoeff_haarPhase hq hj, zero_mul]

end Pyramids
