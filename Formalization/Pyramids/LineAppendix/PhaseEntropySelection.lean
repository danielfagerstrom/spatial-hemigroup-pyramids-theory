/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.PhaseEntropy

/-!
# `thm:phase-entropy-selection`(3)–(4): the maximizers of the phase entropy on a modulation orbit

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:phase-entropy-selection`. Wave 3d: the
declarations `phase_entropy_selection_3` and `phase_entropy_selection_4` moved here from
`PyramidsSkeleton.ChA1Line`, unchanged in name and conclusion; both no longer take the hypothesis
`IsKnotExponent q Ψ1`, which the proofs do not read (a strengthening).

## The route

* **The Gaussian part of the step.** For a member with pair `(Λ, ℬ)`, `(a(q) - a(1), ϖ_q - ϖ_1)`
  is a pair with exponent `Ψ_q - Ψ_1 = φ` (`exists_step_gauss`, the argument of
  `knot_exponent_ladder_3`), so by the uniqueness of the data `a(q) - a(1)` is the Gaussian
  coefficient of `φ`. With no Gaussian part, `a(q) = a(1)`, while `a(q) = q²a(1)`; so `a(1) = 0` and
  `ℬ = 0` (`gauss_eq_zero_of_noGaussianStep`).
* **(3).** `𝔈 = 0` iff (a) of `prop:strata-cylinder-coordinates`(1)
  (`phaseEntropy_eq_zero_iff_slab`); with `ℬ = 0`, (a') holds, so `𝔈 = 0` iff
  `Ψ_{λt} = Ψ_t(λ ·)` for all `λ, t` (`lineExponent_cov_iff`), iff the member is the similarity
  member, by (1).
* **(4), the members with `𝔈 = 0`**: (a) is `ϖ_t = T_t ϖ_1` for all `t > 0` (`slab_cov_iff`).
* **(4), infinitely many.** Let `(Λ₀, ℬ₀)` be the pair of the similarity member, so
  `a₀(t) = t²a(1)` with `a(1) > 0` (the step has a Gaussian part). A second Gaussian measure with
  (ii), no atoms and `ℬ((0,1]) = a(1)` is the spread `ℬ_alt` of `c · Lebesgue` on `[1,q)`,
  `c = (q + 1)a(1)` (`knot_atom_cascades_2_gaussian`); on `(1,t]`, `1 < t < q`, it gives
  `c(t - 1)`, where `ℬ₀` gives `(t² - 1)a(1)`. The mixtures `ℬ_i = w_iℬ₀ + (1 - w_i)ℬ_alt`,
  `w_i = 1/(i + 1)`, satisfy (ii)–(iv) with `Λ₀`, so `(Λ₀, ℬ_i)` is the pair of a family
  (`surface_measure_pair`); its knot exponent is `Ψ_1`, since `ℬ_i((0,1]) = a(1)`; its `𝔈` is `0`
  since `Λ₀` satisfies (a); and distinct `i` give distinct `ℬ_i`, hence distinct families
  (`surface_measure_unique`). The print takes `a_s(t) = a(1)q^{2((t-1)/(q-1))^s}`; any family of
  Gaussian measures with these properties serves, and the mixtures need no Stieltjes measure
  built from a formula.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair)
open scoped ENNReal NNReal

/-! ## The Gaussian part of the octave step -/

/-- For a member with pair `(Λ, ℬ)`: a pair with exponent `φ` and Gaussian coefficient
`a(q) - a(1)`. -/
theorem exists_step_gauss {q : ℝ} (hq : 1 < q) {Ψ1 : ℝ → ℝ} {μ : ℝ → ℝ → Measure ℝ}
    (hμ : μ ∈ modulationOrbit q Ψ1) {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}
    (hΛ : IsFamilyPair q μ Λ B) :
    ∃ R : SymLevyPair, HasExpData (knotStep q Ψ1) R ∧
      ENNReal.ofReal R.a + B (Ioc 0 1) = B (Ioc 0 q) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨P1, hP1, hP1ν, hP1a⟩ := hΛ.2 1 one_pos
  obtain ⟨Pq, hPq, hPqν, hPqa⟩ := hΛ.2 q hq0
  have ha : P1.a ≤ Pq.a := by
    have h : B (Ioc 0 1) ≤ B (Ioc 0 q) := measure_mono (Ioc_subset_Ioc_right hq.le)
    rw [← hP1a, ← hPqa] at h
    exact (ENNReal.ofReal_le_ofReal_iff Pq.a_nonneg).1 h
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
  have hRexp : HasExpData (knotStep q Ψ1) R := by
    intro ω
    have h1 := lineExponent_eq_of_folded hμ.1.1 zero_le_one hP1 ω
    have hq' := lineExponent_eq_of_folded hμ.1.1 hq0.le hPq ω
    have hφ := lineExponent_q_sub_one hμ.1 ω
    rw [lineExponent_one_of_mem_orbit hμ] at hφ h1
    rw [← hφ, h1, hq', ← hsum, SymLevyPair_add_exponent]
    ring
  refine ⟨R, hRexp, ?_⟩
  change ENNReal.ofReal (Pq.a - P1.a) + B (Ioc 0 1) = B (Ioc 0 q)
  rw [← hP1a, ← hPqa, ← ENNReal.ofReal_add (sub_nonneg.2 ha) P1.a_nonneg, sub_add_cancel]

/-- On a ladder with no Gaussian part, every member has `ℬ = 0`. -/
theorem gauss_eq_zero_of_noGaussianStep {q : ℝ} (hq : 1 < q) {Ψ1 : ℝ → ℝ}
    (hnoG : HasNoGaussianStep q Ψ1) {μ : ℝ → ℝ → Measure ℝ} (hμ : μ ∈ modulationOrbit q Ψ1)
    {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ} (hΛ : IsFamilyPair q μ Λ B) :
    ∀ t : ℝ, 0 < t → B (Ioc 0 t) = 0 := by
  have hq0 : 0 < q := by linarith
  obtain ⟨R, hR, hRB⟩ := exists_step_gauss hq hμ hΛ
  obtain ⟨P, hP, hPa⟩ := hnoG
  have hRa : R.a = 0 := (line_exponent_data_1_unique _ R P hR hP).1.trans hPa
  have hcov := hΛ.1.B_cov hq0 (t := 1)
  rw [mul_one] at hcov
  rw [hRa, ENNReal.ofReal_zero, zero_add, hcov] at hRB
  have hx := hΛ.1.B_ne_top zero_le_one
  have h1 : B (Ioc 0 1) = 0 := by
    have hr := congrArg ENNReal.toReal hRB
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg q)] at hr
    have hq2 : q ^ 2 - 1 ≠ 0 := by nlinarith
    have hm : (q ^ 2 - 1) * (B (Ioc 0 1)).toReal = 0 := by linear_combination -hr
    have h0 : (B (Ioc 0 1)).toReal = 0 := (mul_eq_zero.1 hm).resolve_left hq2
    exact ((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right hx
  have hpow : ∀ n : ℕ, B (Ioc 0 (q ^ n)) = 0 := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ', hΛ.1.B_cov hq0, ih, mul_zero]
  intro t _
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt t hq
  exact measure_mono_null (Ioc_subset_Ioc_right hn.le) (hpow n)

/-! ## (3) -/

/-- **`thm:phase-entropy-selection`(3).** On a ladder with no Gaussian part, the similarity member
is the only member with `𝔈 = 0`, the unique maximizer of the phase entropy on the orbit. The
hypothesis `IsKnotExponent q Ψ1` of the skeleton is not used and was dropped on 2026-11-14, a
strengthening. -/
theorem phase_entropy_selection_3 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ)
    (hnoG : HasNoGaussianStep q Ψ1) (μ₀ : ℝ → ℝ → Measure ℝ) (hμ₀ : μ₀ ∈ modulationOrbit q Ψ1)
    (hsim : ∀ t : ℝ, 0 < t → ∀ ω : ℝ, lineExponent μ₀ t ω = Ψ1 (t * ω)) :
    (∃ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (π : ℝ → Measure ℝ), IsFamilyPair q μ₀ Λ B ∧
        IsPhaseDisintegration q (cylMeasure q Λ) π ∧ phaseEntropy q (cylMeasure q Λ) π = 0) ∧
      ∀ μ ∈ modulationOrbit q Ψ1, ∀ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (π : ℝ → Measure ℝ),
        IsFamilyPair q μ Λ B → IsPhaseDisintegration q (cylMeasure q Λ) π →
          (phaseEntropy q (cylMeasure q Λ) π = 0 ↔ ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ₀ s t) := by
  have hsel := phase_entropy_selection_1 hq Ψ1 μ₀ hμ₀ hsim
  -- a member equal to the similarity member has `𝔈 = 0`
  have back : ∀ μ ∈ modulationOrbit q Ψ1, ∀ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
      (π : ℝ → Measure ℝ), IsFamilyPair q μ Λ B → IsPhaseDisintegration q (cylMeasure q Λ) π →
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ₀ s t) → phaseEntropy q (cylMeasure q Λ) π = 0 := by
    intro μ hμ Λ B π hΛ hπ heq
    have e : ∀ x : ℝ, 0 ≤ x → ∀ ω : ℝ, lineExponent μ x ω = lineExponent μ₀ x ω :=
      fun x hx ω => by
        unfold lineExponent
        rw [heq 0 x le_rfl hx]
    have hcov : ∀ lam t : ℝ, 0 < lam → 0 < t → ∀ ω : ℝ,
        lineExponent μ (lam * t) ω = lineExponent μ t (lam * ω) := by
      intro lam t hlam ht ω
      rw [e _ (mul_pos hlam ht).le, e t ht.le]
      exact hsel.1 lam t hlam ht ω
    exact (phaseEntropy_eq_zero_iff_slab hq hΛ.1 hπ).2 ((lineExponent_cov_iff hμ.1 hΛ).1 hcov).1
  refine ⟨?_, fun μ hμ Λ B π hΛ hπ => ⟨fun h0 => ?_, back μ hμ Λ B π hΛ hπ⟩⟩
  · obtain ⟨Λ, B, hΛ⟩ := surface_measure_family hq μ₀ hμ₀.1
    obtain ⟨-, ⟨π, hπ⟩, -⟩ := phase_disintegration_exists hq μ₀ Λ B hΛ
    exact ⟨Λ, B, π, hΛ, hπ, back μ₀ hμ₀ Λ B π hΛ hπ fun _ _ _ _ => rfl⟩
  · have hslab := (phaseEntropy_eq_zero_iff_slab hq hΛ.1 hπ).1 h0
    have hB := gauss_eq_zero_of_noGaussianStep hq hnoG hμ hΛ
    have hcov := (lineExponent_cov_iff hμ.1 hΛ).2 ⟨hslab, fun lam t hlam ht => by
      rw [hB _ (mul_pos hlam ht), hB t ht, ENNReal.toReal_zero, mul_zero]⟩
    exact hsel.2 μ hμ hcov

/-! ## (4): a second Gaussian measure -/

/-- `c · Lebesgue` on `[1,q)`. -/
noncomputable def stepBeta (q c : ℝ) : Measure ℝ := ENNReal.ofReal c • volume.restrict (Ico 1 q)

theorem isFiniteMeasure_stepBeta (q c : ℝ) : IsFiniteMeasure (stepBeta q c) := by
  refine ⟨?_⟩
  rw [stepBeta, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ico]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem stepBeta_compl (q c : ℝ) : stepBeta q c (Ico 1 q)ᶜ = 0 := by
  rw [stepBeta, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_Ico.compl,
    compl_inter_self, measure_empty, mul_zero]

theorem stepBeta_null {q c : ℝ} {S : Set ℝ} (hS : volume S = 0) : stepBeta q c S = 0 := by
  rw [stepBeta, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' measurableSet_Ico,
    measure_mono_null inter_subset_left hS, mul_zero]

/-- `aℬ + bℬ'` satisfies (ii) when `ℬ` and `ℬ'` do. -/
theorem isSurfaceGaussian_mix {q : ℝ} {B B' : Measure ℝ} (hB : IsSurfaceGaussian q B)
    (hB' : IsSurfaceGaussian q B') {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    IsSurfaceGaussian q (a • B + b • B') := by
  refine ⟨?_, fun t ht => ?_, fun A hA hA0 => ?_⟩
  · simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hB.1, hB'.1, mul_zero,
      add_zero]
  · simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ha (hB.2.1 t ht),
      ENNReal.mul_ne_top hb (hB'.2.1 t ht)⟩
  · simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hB.2.2 A hA hA0,
      hB'.2.2 A hA hA0]
    ring

/-- `(Λ, aℬ + bℬ')` satisfies (i)–(iv) when `(Λ, ℬ)` does, `ℬ'` satisfies (ii) with no atoms in
`(0,∞)`, and `a > 0`. -/
theorem isSurfacePair_mix {q : ℝ} {Λ : Measure (ℝ × ℝ)} {B B' : Measure ℝ}
    (h : IsSurfacePair q Λ B) (hB' : IsSurfaceGaussian q B') (hB'1 : ∀ y : ℝ, B' {y} = 0)
    {a b : ℝ≥0∞} (ha0 : a ≠ 0) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    IsSurfacePair q Λ (a • B + b • B') where
  carried := h.carried
  invariant := h.invariant
  integrable := h.integrable
  gaussian := isSurfaceGaussian_mix h.gaussian hB' ha hb
  no_line := fun y hy => ⟨(h.no_line y hy).1, by
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, (h.no_line y hy).2, hB'1 y,
      mul_zero, add_zero]⟩
  nondeg := fun s t hs hst => by
    have h0 := h.nondeg s t hs hst
    rw [pos_iff_ne_zero] at h0 ⊢
    intro hz
    obtain ⟨h1, h2⟩ := add_eq_zero.1 hz
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, add_eq_zero, mul_eq_zero] at h2
    apply h0
    rw [h1, zero_add]
    exact h2.1.resolve_left ha0

/-! ## (4) -/

/-- **`thm:phase-entropy-selection`(4).** On a ladder with a Gaussian part, the members with
`𝔈 = 0` are those with `ϖ_t = T_t ϖ_1` for all `t > 0`, whatever `a(t)`, and there are infinitely
many. The hypothesis `IsKnotExponent q Ψ1` of the skeleton is not used and was dropped on
2026-11-14, a strengthening. -/
theorem phase_entropy_selection_4 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ)
    (hG : ¬ HasNoGaussianStep q Ψ1) (μ₀ : ℝ → ℝ → Measure ℝ) (hμ₀ : μ₀ ∈ modulationOrbit q Ψ1)
    (hsim : ∀ t : ℝ, 0 < t → ∀ ω : ℝ, lineExponent μ₀ t ω = Ψ1 (t * ω)) :
    (∀ μ ∈ modulationOrbit q Ψ1, ∀ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (π : ℝ → Measure ℝ),
        IsFamilyPair q μ Λ B → IsPhaseDisintegration q (cylMeasure q Λ) π →
          (phaseEntropy q (cylMeasure q Λ) π = 0 ↔
            ∀ t : ℝ, 0 < t → slab Λ 0 t = (slab Λ 0 1).map (fun v => t * v))) ∧
      ∃ f : ℕ → ℝ → ℝ → Measure ℝ,
        (∀ i j : ℕ, i ≠ j → ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ f i s t ≠ f j s t) ∧
        ∀ i : ℕ, f i ∈ modulationOrbit q Ψ1 ∧
          ∃ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (π : ℝ → Measure ℝ), IsFamilyPair q (f i) Λ B ∧
            IsPhaseDisintegration q (cylMeasure q Λ) π ∧ phaseEntropy q (cylMeasure q Λ) π = 0 := by
  have hq0 : 0 < q := by linarith
  refine ⟨fun μ _ Λ B π hΛ hπ =>
    (phaseEntropy_eq_zero_iff_slab hq hΛ.1 hπ).trans (slab_cov_iff Λ), ?_⟩
  -- the pair of the similarity member: (a) and `a₀(t) = t²a(1)`
  obtain ⟨Λ₀, B₀, hΛ₀⟩ := surface_measure_family hq μ₀ hμ₀.1
  obtain ⟨hslab₀, hgauss₀⟩ :=
    (lineExponent_cov_iff hμ₀.1 hΛ₀).1 (phase_entropy_selection_1 hq Ψ1 μ₀ hμ₀ hsim).1
  obtain ⟨a1, ha1⟩ : ∃ a : ℝ, a = (B₀ (Ioc 0 1)).toReal := ⟨_, rfl⟩
  have hB01 : B₀ (Ioc 0 1) = ENNReal.ofReal a1 := by
    rw [ha1, ENNReal.ofReal_toReal (hΛ₀.1.B_ne_top zero_le_one)]
  -- `a(1) > 0`, since the step has a Gaussian part
  have ha1pos : 0 < a1 := by
    rcases (ha1 ▸ ENNReal.toReal_nonneg : (0 : ℝ) ≤ a1).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hG
      obtain ⟨R, hR, hRB⟩ := exists_step_gauss hq hμ₀ hΛ₀
      refine ⟨R, hR, ?_⟩
      have hB0 : B₀ (Ioc 0 1) = 0 := by rw [hB01, ← h, ENNReal.ofReal_zero]
      have hcov := hΛ₀.1.B_cov hq0 (t := 1)
      rw [mul_one] at hcov
      rw [hcov, hB0, mul_zero, add_zero, ENNReal.ofReal_eq_zero] at hRB
      exact le_antisymm hRB R.a_nonneg
  -- `ℬ₀((1,t]) = (t² - 1)a(1)`
  have hB0t : ∀ t : ℝ, 1 ≤ t → B₀ (Ioc 1 t) = ENNReal.ofReal ((t ^ 2 - 1) * a1) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hsplit : B₀ (Ioc 0 t) = B₀ (Ioc 0 1) + B₀ (Ioc 1 t) := by
      rw [← measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
        Ioc_union_Ioc_eq_Ioc zero_le_one ht]
    have h2 := hgauss₀ t 1 ht0 one_pos
    rw [mul_one] at h2
    have hfin : B₀ (Ioc 1 t) ≠ ⊤ := ne_top_of_le_ne_top (hΛ₀.1.B_ne_top ht0.le)
      (measure_mono (Ioc_subset_Ioc_left zero_le_one))
    rw [hsplit, ENNReal.toReal_add (hΛ₀.1.B_ne_top zero_le_one) hfin, ← ha1] at h2
    rw [← ENNReal.ofReal_toReal hfin]
    congr 1
    linarith
  -- the second Gaussian measure
  have hc0 : 0 ≤ (q + 1) * a1 := mul_nonneg (by linarith) ha1pos.le
  haveI := isFiniteMeasure_stepBeta q ((q + 1) * a1)
  obtain ⟨hBA, hBAr⟩ := (knot_atom_cascades_2_gaussian hq).2 (stepBeta q ((q + 1) * a1))
    inferInstance (stepBeta_compl q _)
  obtain ⟨BA, hBAdef⟩ : ∃ m : Measure ℝ, m = gaussSpread q (stepBeta q ((q + 1) * a1)) :=
    ⟨_, rfl⟩
  rw [← hBAdef] at hBA hBAr
  have hBAsub : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ico 1 q →
      BA A = ENNReal.ofReal ((q + 1) * a1) * volume A := by
    intro A hA hsub
    have e : BA.restrict (Ico 1 q) A = BA A := by
      rw [Measure.restrict_apply hA, inter_eq_left.2 hsub]
    rw [← e, hBAr, stepBeta, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
      inter_eq_left.2 hsub]
  have hBA1 : ∀ y : ℝ, BA {y} = 0 := by
    intro y
    rw [hBAdef, gaussSpread_apply q _ (measurableSet_singleton y)]
    refine ENNReal.tsum_eq_zero.2 fun n => ?_
    have hnull : volume ((fun x => q ^ n * x) ⁻¹' {y}) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (Real.volume_singleton (a := y / q ^ n))
      simp only [mem_preimage, mem_singleton_iff] at hx ⊢
      rw [eq_div_iff (zpow_ne_zero n hq0.ne'), mul_comm, hx]
    rw [stepBeta_null hnull, mul_zero]
  have hBA01 : BA (Ioc 0 1) = ENNReal.ofReal a1 := by
    have hsc := hBA.2.2 (Ioc 0 1) measurableSet_Ioc Ioc_subset_Ioi_self
    rw [image_mul_left_Ioc hq0, mul_zero, mul_one] at hsc
    have hsplit : BA (Ioc 0 q) = BA (Ioc 0 1) + BA (Ioo 1 q) := by
      rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hq.le,
        measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc, ← Ioo_union_right hq,
        measure_union (by simp) (measurableSet_singleton q), hBA1, add_zero]
    have hIoo : BA (Ioo 1 q) = ENNReal.ofReal ((q + 1) * a1 * (q - 1)) := by
      rw [hBAsub _ measurableSet_Ioo Ioo_subset_Ico_self, Real.volume_Ioo,
        ← ENNReal.ofReal_mul hc0]
    have hfin : BA (Ioc 0 1) ≠ ⊤ := hBA.2.1 1 one_pos
    rw [hsplit, hIoo] at hsc
    rw [← ENNReal.ofReal_toReal hfin]
    congr 1
    have hr := congrArg ENNReal.toReal hsc
    rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg hc0 (by linarith)),
      ENNReal.toReal_ofReal (sq_nonneg q)] at hr
    have hq2 : q ^ 2 - 1 ≠ 0 := by nlinarith
    have hm : (q ^ 2 - 1) * ((BA (Ioc 0 1)).toReal - a1) = 0 := by linear_combination -hr
    exact sub_eq_zero.1 ((mul_eq_zero.1 hm).resolve_left hq2)
  -- the mixtures
  let w : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1)
  have hw0 : ∀ i : ℕ, 0 < w i := fun i => by positivity
  have hw1 : ∀ i : ℕ, w i ≤ 1 := fun i => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  let Bm : ℕ → Measure ℝ := fun i => ENNReal.ofReal (w i) • B₀ + ENNReal.ofReal (1 - w i) • BA
  have hpair : ∀ i : ℕ, IsSurfacePair q Λ₀ (Bm i) := fun i =>
    isSurfacePair_mix hΛ₀.1 hBA hBA1 (ENNReal.ofReal_pos.2 (hw0 i)).ne' ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top
  have hmix : ∀ (i : ℕ) (A : Set ℝ) (x y : ℝ), 0 ≤ x → 0 ≤ y → B₀ A = ENNReal.ofReal x →
      BA A = ENNReal.ofReal y → Bm i A = ENNReal.ofReal (w i * x + (1 - w i) * y) := by
    intro i A x y hx hy hxA hyA
    simp only [Bm, Measure.add_apply, Measure.smul_apply, smul_eq_mul, hxA, hyA]
    rw [← ENNReal.ofReal_mul (hw0 i).le, ← ENNReal.ofReal_mul (sub_nonneg.2 (hw1 i)),
      ← ENNReal.ofReal_add (mul_nonneg (hw0 i).le hx) (mul_nonneg (sub_nonneg.2 (hw1 i)) hy)]
  have hBm01 : ∀ i : ℕ, Bm i (Ioc 0 1) = B₀ (Ioc 0 1) := by
    intro i
    rw [hmix i _ a1 a1 ha1pos.le ha1pos.le hB01 hBA01, hB01]
    congr 1
    ring
  -- the families
  have hfam : ∀ i : ℕ, ∃ μ : ℝ → ℝ → Measure ℝ, IsQFamily q μ ∧ IsSurfaceDataOf μ Λ₀ (Bm i) :=
    fun i => surface_measure_pair hq Λ₀ (Bm i) (hpair i)
  choose f hfQ hfD using hfam
  have he₀ := (surface_measure_exponent μ₀ hμ₀.1 Λ₀ B₀ hΛ₀.1).1 hΛ₀.2
  have horb : ∀ i : ℕ, f i ∈ modulationOrbit q Ψ1 := by
    intro i
    refine ⟨hfQ i, fun ω => ?_⟩
    have hei := (surface_measure_exponent (f i) (hfQ i) Λ₀ (Bm i) (hpair i)).1 (hfD i)
    have hs : surfaceExponent Λ₀ (Bm i) 1 ω = surfaceExponent Λ₀ B₀ 1 ω := by
      simp only [surfaceExponent, hBm01 i]
    rw [charFun_kernel_eq_exp (hfQ i).1 zero_le_one, hei 1 one_pos, hs,
      ← lineExponent_one_of_mem_orbit hμ₀, he₀ 1 one_pos]
  have hent : ∀ i : ℕ, ∃ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (π : ℝ → Measure ℝ),
      IsFamilyPair q (f i) Λ B ∧ IsPhaseDisintegration q (cylMeasure q Λ) π ∧
        phaseEntropy q (cylMeasure q Λ) π = 0 := by
    intro i
    obtain ⟨-, ⟨π, hπ⟩, -⟩ := phase_disintegration_exists hq (f i) Λ₀ (Bm i) ⟨hpair i, hfD i⟩
    exact ⟨Λ₀, Bm i, π, ⟨hpair i, hfD i⟩, hπ,
      (phaseEntropy_eq_zero_iff_slab hq (hpair i) hπ).2 hslab₀⟩
  -- distinct indices give distinct families: compare `ℬ_i((1,t₀])`, `t₀ = (1 + q)/2`
  have ht1 : 1 ≤ (1 + q) / 2 := by linarith
  have htq : (1 + q) / 2 < q := by linarith
  have hBAt : BA (Ioc 1 ((1 + q) / 2)) = ENNReal.ofReal ((q + 1) * a1 * ((1 + q) / 2 - 1)) := by
    rw [hBAsub _ measurableSet_Ioc (fun x hx => ⟨hx.1.le, lt_of_le_of_lt hx.2 htq⟩),
      Real.volume_Ioc, ← ENNReal.ofReal_mul hc0]
  have hX : 0 ≤ (((1 + q) / 2) ^ 2 - 1) * a1 := by
    refine mul_nonneg ?_ ha1pos.le
    nlinarith
  have hY : 0 ≤ (q + 1) * a1 * ((1 + q) / 2 - 1) := mul_nonneg hc0 (by linarith)
  refine ⟨f, fun i j hij => ?_, fun i => ⟨horb i, hent i⟩⟩
  by_contra H
  simp only [not_exists, not_and, ne_eq, not_not] at H
  have hdata : IsSurfaceDataOf (f j) Λ₀ (Bm i) := fun t ht => by
    rw [← H 0 t le_rfl ht.le]
    exact hfD i t ht
  obtain ⟨-, hBij⟩ := surface_measure_unique (f j) Λ₀ (Bm j) ⟨hpair j, hfD j⟩ Λ₀ (Bm i)
    hΛ₀.1.carried (hpair i).gaussian.1 hdata
  have hval := congrArg (fun m : Measure ℝ => m (Ioc 1 ((1 + q) / 2))) hBij
  rw [hmix i _ _ _ hX hY (hB0t _ ht1) hBAt, hmix j _ _ _ hX hY (hB0t _ ht1) hBAt,
    ENNReal.ofReal_eq_ofReal_iff (add_nonneg (mul_nonneg (hw0 i).le hX)
      (mul_nonneg (sub_nonneg.2 (hw1 i)) hY)) (add_nonneg (mul_nonneg (hw0 j).le hX)
      (mul_nonneg (sub_nonneg.2 (hw1 j)) hY))] at hval
  have hXY : (((1 + q) / 2) ^ 2 - 1) * a1 - (q + 1) * a1 * ((1 + q) / 2 - 1) ≠ 0 := by
    have e : (((1 + q) / 2) ^ 2 - 1) * a1 - (q + 1) * a1 * ((1 + q) / 2 - 1) =
        -(a1 * (q - 1) ^ 2 / 4) := by ring
    rw [e, neg_ne_zero]
    have : 0 < q - 1 := by linarith
    positivity
  have hw : w i = w j := by
    have hm : (w i - w j) * ((((1 + q) / 2) ^ 2 - 1) * a1 -
        (q + 1) * a1 * ((1 + q) / 2 - 1)) = 0 := by linear_combination hval
    exact sub_eq_zero.1 ((mul_eq_zero.1 hm).resolve_right hXY)
  apply hij
  have hc : ((i : ℝ) + 1) = (j : ℝ) + 1 := by
    simp only [w, one_div] at hw
    exact inv_inj.1 hw
  exact_mod_cast add_right_cancel hc

end Pyramids
