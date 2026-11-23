/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.SurfacePair
import Pyramids.Pyramid.LadderNuStar

/-!
# `thm:knot-atom-cascades`(1)–(2): the orbits of `J` and the cylinder

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:knot-atom-cascades`. Wave 3a: the five
declarations `knot_atom_cascades_1_action`, `_1_orbits`, `_2_bij`, `_2_integrable` and
`_2_gaussian` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in statement and name.

## The route

* **The orbit points.** `Λ^{(θ,r)}` is the sum of the point masses at `T_n(θ, r) := (θqⁿ, rθqⁿ)`
  (`orbitPt`), so the mixture `Λ_σ` is `∑ₙ (T_n)_* σ` (`orbitMixture_apply`,
  `orbitMixture_eq_sum`), additive and positively homogeneous in `σ`.
* **The fundamental domain.** `θqⁿ ∈ [1,q)` for `θ ∈ [1,q)` only at `n = 0`
  (`mul_zpow_mem_Ico_iff`), and every `y > 0` has exactly one `n` with `qⁿy ∈ [1,q)`. So the sets
  `J^{-n}[1,q) × (0,∞)` partition the quadrant (`measure_eq_tsum_cyl`), and an invariant `Λ` is the
  sum of the transports of its restriction to the domain: this is the bijection (2).
* **The integrability.** At `t = 1` the slab integral of `Λ_σ` is `∫ S dσ` with
  `S(θ, r) = (1 ∧ (rθ)²)𝟙_{θ = 1} + b(rθ)`, `b` the bracket `∑_{m ≥ 1} (1 ∧ x²q^{-2m})` of
  `LadderNuStar.lean` (`ladderBracket`), and `b` is comparable with the weight
  `w(x) = x² ∧ (1 + log₊x)` of (A.e3) on both sides (`ladderBracket_le_cylWeight`,
  `cylWeight_le_ladderBracket`). By `surface_measure_integrable_iff` the one `t` gives every `t`.
* **The Gaussian part** is the same argument for `y ↦ qy` with the weight `q²`
  (`gaussian_zpow`, `gaussSpread_apply`).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

/-! ## Powers of `q` -/

/-- `θqⁿ ∈ [1,q)` for `θ ∈ [1,q)` only at `n = 0`. -/
theorem mul_zpow_mem_Ico_iff {q : ℝ} (hq : 1 < q) {θ : ℝ} (hθ : θ ∈ Ico 1 q) (n : ℤ) :
    θ * q ^ n ∈ Ico 1 q ↔ n = 0 := by
  have hq0 : 0 < q := by linarith
  have hθ0 : 0 < θ := by linarith [hθ.1]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy n 0 with hn | hn | hn
    · exfalso
      have hle : q ^ n ≤ q ^ (-1 : ℤ) := zpow_le_zpow_right₀ hq.le (by omega)
      have : θ * q ^ n < 1 := by
        calc θ * q ^ n ≤ θ * q ^ (-1 : ℤ) := mul_le_mul_of_nonneg_left hle hθ0.le
          _ < q * q ^ (-1 : ℤ) := mul_lt_mul_of_pos_right hθ.2 (zpow_pos hq0 _)
          _ = 1 := by rw [zpow_neg_one, mul_inv_cancel₀ hq0.ne']
      linarith
    · exact hn
    · exfalso
      have hle : q ^ (1 : ℤ) ≤ q ^ n := zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_one] at hle
      have : q ≤ θ * q ^ n := by
        calc q ≤ q ^ n := hle
          _ = 1 * q ^ n := (one_mul _).symm
          _ ≤ θ * q ^ n := mul_le_mul_of_nonneg_right hθ.1 (zpow_pos hq0 n).le
      linarith
  · rintro rfl
    simpa using hθ

/-- `y > 0` has exactly one `n` with `qⁿy ∈ [1,q)`. -/
theorem existsUnique_zpow_mul_mem_Ico {q : ℝ} (hq : 1 < q) {y : ℝ} (hy : 0 < y) :
    ∃! n : ℤ, q ^ n * y ∈ Ico 1 q := by
  have hq0 : 0 < q := by linarith
  refine ⟨-dgLevel q y, octave_mem hq hy, fun m hm => ?_⟩
  have h0 := octave_mem hq hy
  have hm : q ^ m * y ∈ Ico 1 q := hm
  have e : q ^ m * y = q ^ (-dgLevel q y) * y * q ^ (m - -dgLevel q y) := by
    rw [mul_comm (q ^ (-dgLevel q y)) y, mul_assoc, ← zpow_add₀ hq0.ne', add_sub_cancel,
      mul_comm]
  rw [e, mul_zpow_mem_Ico_iff hq h0] at hm
  omega

/-- `q^{2n} = (qⁿ)²`. -/
theorem zpow_two_mul' (q : ℝ) (n : ℤ) : q ^ (2 * n) = (q ^ n) ^ 2 := by
  rw [mul_comm, zpow_mul, zpow_two, sq]

/-! ## The diagonal dilations -/

theorem scaleDiag_mul (a b : ℝ) : scaleDiag (a * b) = scaleDiag a ∘ scaleDiag b := by
  funext p
  simp [scaleDiag, mul_assoc]

theorem scaleDiag_one : scaleDiag 1 = id := by
  funext p
  simp [scaleDiag]

/-- An invariant `Λ` is invariant under every `J^n`, `n ∈ ℤ`. -/
theorem map_scaleDiag_zpow {q : ℝ} (hq0 : 0 < q) {Λ : Measure (ℝ × ℝ)}
    (hinv : Λ.map (scaleDiag q) = Λ) (n : ℤ) : Λ.map (scaleDiag (q ^ n)) = Λ := by
  have hinv' : Λ.map (scaleDiag q⁻¹) = Λ := by
    conv_lhs => rw [← hinv]
    rw [Measure.map_map (measurable_scaleDiag _) (measurable_scaleDiag _), ← scaleDiag_mul,
      inv_mul_cancel₀ hq0.ne', scaleDiag_one, Measure.map_id]
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, scaleDiag_one, Measure.map_id]
  | succ n ih =>
    rw [zpow_add_one₀ hq0.ne', mul_comm, scaleDiag_mul,
      ← Measure.map_map (measurable_scaleDiag _) (measurable_scaleDiag _), ih, hinv]
  | pred n ih =>
    rw [zpow_sub_one₀ hq0.ne', mul_comm, scaleDiag_mul,
      ← Measure.map_map (measurable_scaleDiag _) (measurable_scaleDiag _), ih, hinv']

theorem measure_preimage_scaleDiag_zpow {q : ℝ} (hq0 : 0 < q) {Λ : Measure (ℝ × ℝ)}
    (hinv : Λ.map (scaleDiag q) = Λ) (n : ℤ) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    Λ (scaleDiag (q ^ n) ⁻¹' s) = Λ s := by
  rw [← Measure.map_apply (measurable_scaleDiag _) hs, map_scaleDiag_zpow hq0 hinv]

theorem measurableSet_cylinder (q : ℝ) : MeasurableSet (cylinder q) :=
  measurableSet_Ico.prod measurableSet_Ioi

theorem measurableSet_quadrant : MeasurableSet quadrant :=
  measurableSet_Ioi.prod measurableSet_Ioi

/-- `p ∈ (0,∞)²` has exactly one `n` with `Jⁿp ∈ [1,q) × (0,∞)`. -/
theorem existsUnique_scaleDiag_mem_cylinder {q : ℝ} (hq : 1 < q) {p : ℝ × ℝ}
    (hp : p ∈ quadrant) : ∃! n : ℤ, scaleDiag (q ^ n) p ∈ cylinder q := by
  have hq0 : 0 < q := by linarith
  obtain ⟨n, hn, huniq⟩ := existsUnique_zpow_mul_mem_Ico hq (show 0 < p.1 from hp.1)
  refine ⟨n, ⟨hn, mul_pos (zpow_pos hq0 n) hp.2⟩, fun m hm => huniq m hm.1⟩

/-- A point some `Jⁿ` maps into the domain lies in the quadrant. -/
theorem mem_quadrant_of_scaleDiag_mem {q : ℝ} (hq0 : 0 < q) {p : ℝ × ℝ} {n : ℤ}
    (h : scaleDiag (q ^ n) p ∈ cylinder q) : p ∈ quadrant := by
  obtain ⟨⟨h1, -⟩, h2⟩ := h
  have hp : 0 < q ^ n := zpow_pos hq0 n
  exact ⟨pos_of_mul_pos_right (lt_of_lt_of_le one_pos h1) hp.le,
    pos_of_mul_pos_right (show 0 < q ^ n * p.2 from h2) hp.le⟩

/-- **The domains `J^{-n}([1,q) × (0,∞))` partition the quadrant**: for `Λ` on the quadrant,
`Λ(s) = ∑ₙ Λ(s ∩ J^{-n}…)`. -/
theorem measure_eq_tsum_cyl {q : ℝ} (hq : 1 < q) {Λ : Measure (ℝ × ℝ)}
    (hc : Λ quadrantᶜ = 0) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    Λ s = ∑' n : ℤ, Λ (s ∩ scaleDiag (q ^ n) ⁻¹' cylinder q) := by
  have hq0 : 0 < q := by linarith
  rw [← measure_inter_conull hc]
  have hU : s ∩ quadrant = ⋃ n : ℤ, s ∩ scaleDiag (q ^ n) ⁻¹' cylinder q := by
    ext p
    simp only [mem_inter_iff, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨hps, hpq⟩
      obtain ⟨n, hn, -⟩ := existsUnique_scaleDiag_mem_cylinder hq hpq
      exact ⟨n, hps, hn⟩
    · rintro ⟨n, hps, hn⟩
      exact ⟨hps, mem_quadrant_of_scaleDiag_mem hq0 hn⟩
  rw [hU, measure_iUnion]
  · intro m n hmn
    refine Set.disjoint_left.2 fun p hm hn => hmn ?_
    have hpq := mem_quadrant_of_scaleDiag_mem hq0 hm.2
    exact (existsUnique_scaleDiag_mem_cylinder hq hpq).unique hm.2 hn.2
  · exact fun n => hs.inter (measurable_scaleDiag _ (measurableSet_cylinder q))

/-! ## The orbit points and the mixture -/

/-- **The `n`-th point `(θqⁿ, rθqⁿ)` of the orbit `Λ^{(θ,r)}`**. -/
noncomputable def orbitPt (q : ℝ) (n : ℤ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * q ^ n, p.2 * p.1 * q ^ n)

theorem measurable_orbitPt (q : ℝ) (n : ℤ) : Measurable (orbitPt q n) := by
  unfold orbitPt
  fun_prop

theorem knotAtomOrbit_apply (q θ r : ℝ) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    knotAtomOrbit q θ r s = ∑' n : ℤ, s.indicator 1 (orbitPt q n (θ, r)) := by
  rw [knotAtomOrbit, Measure.sum_apply _ hs]
  simp only [Measure.dirac_apply' _ hs, orbitPt]

/-- The kernel `(θ, r) ↦ Λ^{(θ,r)}` is measurable. -/
theorem measurable_knotAtomOrbit (q : ℝ) :
    Measurable fun p : ℝ × ℝ => knotAtomOrbit q p.1 p.2 := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [knotAtomOrbit_apply q _ _ hs]
  exact Measurable.tsum fun n =>
    (measurable_one.indicator hs).comp (measurable_orbitPt q n)

/-- **`Λ_σ(s) = ∑ₙ σ(T_n^{-1}s)`**. -/
theorem orbitMixture_apply (q : ℝ) (σ : Measure (ℝ × ℝ)) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) : orbitMixture q σ s = ∑' n : ℤ, σ (orbitPt q n ⁻¹' s) := by
  rw [orbitMixture, Measure.bind_apply hs (measurable_knotAtomOrbit q).aemeasurable]
  simp_rw [knotAtomOrbit_apply q _ _ hs, Prod.mk.eta]
  rw [lintegral_tsum fun n => ?_]
  · congr 1
    funext n
    rw [← lintegral_indicator_one (measurable_orbitPt q n hs)]
    rfl
  · exact ((measurable_one.indicator hs).comp (measurable_orbitPt q n)).aemeasurable

/-- **`Λ_σ = ∑ₙ (T_n)_* σ`**. -/
theorem orbitMixture_eq_sum (q : ℝ) (σ : Measure (ℝ × ℝ)) :
    orbitMixture q σ = Measure.sum fun n : ℤ => σ.map (orbitPt q n) := by
  ext s hs
  rw [orbitMixture_apply q σ hs, Measure.sum_apply _ hs]
  simp_rw [Measure.map_apply (measurable_orbitPt q _) hs]

theorem orbitMixture_add (q : ℝ) (σ σ' : Measure (ℝ × ℝ)) :
    orbitMixture q (σ + σ') = orbitMixture q σ + orbitMixture q σ' := by
  ext s hs
  simp only [Measure.add_apply, orbitMixture_apply q _ hs]
  exact ENNReal.tsum_add

theorem orbitMixture_smul (q : ℝ) (c : ℝ≥0∞) (σ : Measure (ℝ × ℝ)) :
    orbitMixture q (c • σ) = c • orbitMixture q σ := by
  ext s hs
  simp only [Measure.smul_apply, smul_eq_mul, orbitMixture_apply q _ hs]
  exact ENNReal.tsum_mul_left

theorem orbitMixture_zero (q : ℝ) : orbitMixture q 0 = 0 := by
  ext s hs
  simp [orbitMixture_apply q _ hs]

theorem orbitMixture_dirac (q : ℝ) (p : ℝ × ℝ) :
    orbitMixture q (Measure.dirac p) = knotAtomOrbit q p.1 p.2 :=
  Measure.dirac_bind (measurable_knotAtomOrbit q) p

/-! ## The cylinder measure -/

/-- `(y, v) ↦ (y, v/y)`. -/
noncomputable def cylMap (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.2 / p.1)

theorem measurable_cylMap : Measurable cylMap := by
  unfold cylMap
  fun_prop

theorem cylMeasure_eq (q : ℝ) (Λ : Measure (ℝ × ℝ)) :
    cylMeasure q Λ = (Λ.restrict (cylinder q)).map cylMap := rfl

theorem cylMeasure_apply (q : ℝ) (Λ : Measure (ℝ × ℝ)) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) : cylMeasure q Λ s = Λ (cylMap ⁻¹' s ∩ cylinder q) := by
  rw [cylMeasure_eq, Measure.map_apply measurable_cylMap hs,
    Measure.restrict_apply (measurable_cylMap hs)]

theorem cylMeasure_add (q : ℝ) (Λ Λ' : Measure (ℝ × ℝ)) :
    cylMeasure q (Λ + Λ') = cylMeasure q Λ + cylMeasure q Λ' := by
  ext s hs
  simp only [Measure.add_apply, cylMeasure_apply q _ hs]

theorem cylMeasure_smul (q : ℝ) (c : ℝ≥0∞) (Λ : Measure (ℝ × ℝ)) :
    cylMeasure q (c • Λ) = c • cylMeasure q Λ := by
  ext s hs
  simp only [Measure.smul_apply, smul_eq_mul, cylMeasure_apply q _ hs]

theorem cylMeasure_zero (q : ℝ) : cylMeasure q 0 = 0 := by
  ext s hs
  simp [cylMeasure_apply q _ hs]

/-- A measure on the cylinder only sees sets through their trace on it. -/
theorem measure_eq_of_inter_cyl {q : ℝ} {σ : Measure (ℝ × ℝ)} (hσ : σ (cylinder q)ᶜ = 0)
    {A B : Set (ℝ × ℝ)} (h : A ∩ cylinder q = B ∩ cylinder q) : σ A = σ B := by
  rw [← measure_inter_conull hσ, h, measure_inter_conull hσ]

/-! ## `thm:knot-atom-cascades`(1) -/

/-- **`thm:knot-atom-cascades`(1), the action.** `{Jⁿ}` acts freely and properly discontinuously
on `(0,∞)²`. -/
theorem knot_atom_cascades_1_action {q : ℝ} (hq : 1 < q) :
    (∀ n : ℤ, ∀ p ∈ quadrant, scaleDiag (q ^ n) p = p → n = 0) ∧
      ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ quadrant →
        {n : ℤ | (scaleDiag (q ^ n) '' K ∩ K).Nonempty}.Finite := by
  have hq0 : 0 < q := by linarith
  refine ⟨fun n p hp h => ?_, fun K hK hKq => ?_⟩
  · have h1 : q ^ n * p.1 = 1 * p.1 := by
      rw [one_mul]
      exact congrArg Prod.fst h
    have h2 : q ^ n = q ^ (0 : ℤ) := by
      rw [zpow_zero]
      exact mul_right_cancel₀ (ne_of_gt hp.1) h1
    exact zpow_right_injective₀ hq0 hq.ne' h2
  · rcases K.eq_empty_or_nonempty with rfl | hne
    · simp
    -- the `y`-coordinates of `K` lie in `[y₁, y₂]` with `y₁ > 0`
    obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
    have ha0 : 0 < a.1 := (hKq ha).1
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (b.1 / a.1) hq
    refine (Set.finite_Icc (-(N : ℤ)) N).subset fun n hn => ?_
    obtain ⟨x, ⟨p, hpK, rfl⟩, hxK⟩ := hn
    have hp1 : a.1 ≤ p.1 := hamin hpK
    have hp1' : p.1 ≤ b.1 := hbmax hpK
    have hx1 : a.1 ≤ q ^ n * p.1 := hamin hxK
    have hx1' : q ^ n * p.1 ≤ b.1 := hbmax hxK
    have hp0 : 0 < p.1 := lt_of_lt_of_le ha0 hp1
    have hb0 : 0 < b.1 := lt_of_lt_of_le hp0 hp1'
    have hqN : b.1 < q ^ (N : ℤ) * a.1 := by
      rw [zpow_natCast]
      exact (div_lt_iff₀ ha0).1 hN
    constructor
    · -- `q^{-n} ≤ p.1 / a.1 ≤ b.1 / a.1 < q^N`
      by_contra hlt
      have hle : q ^ n ≤ q ^ (-(N : ℤ)) := zpow_le_zpow_right₀ hq.le (by omega)
      have : q ^ n * p.1 < a.1 := by
        calc q ^ n * p.1 ≤ q ^ (-(N : ℤ)) * b.1 :=
              mul_le_mul hle hp1' hp0.le (zpow_pos hq0 _).le
          _ < a.1 := by
            rw [zpow_neg, inv_mul_lt_iff₀ (zpow_pos hq0 _)]
            exact hqN
      linarith
    · by_contra hlt
      have hle : q ^ (N : ℤ) ≤ q ^ n := zpow_le_zpow_right₀ hq.le (by omega)
      have : b.1 < q ^ n * p.1 := by
        calc b.1 < q ^ (N : ℤ) * a.1 := hqN
          _ ≤ q ^ n * p.1 := mul_le_mul hle hp1 ha0.le (zpow_pos hq0 _).le
      linarith

/-- **`thm:knot-atom-cascades`(1), the orbit space.** The invariant map
`(y, v) ↦ (log y mod ℓ, v/y)` is continuous and open on `(0,∞)²`, maps it onto
`(ℝ/ℓℤ) × (0,∞)`, and its fibres are the orbits, so it induces a homeomorphism of the orbit space
onto `(ℝ/ℓℤ) × (0,∞)`; and `[1,q) × (0,∞)` meets every orbit exactly once. -/
theorem knot_atom_cascades_1_orbits {q : ℝ} (hq : 1 < q) :
    ContinuousOn (cylinderChart q) quadrant ∧
      (∀ U : Set (ℝ × ℝ), IsOpen U → U ⊆ quadrant → IsOpen (cylinderChart q '' U)) ∧
      cylinderChart q '' quadrant = univ ×ˢ Ioi 0 ∧
      (∀ p ∈ quadrant, ∀ p' ∈ quadrant,
        cylinderChart q p = cylinderChart q p' ↔ ∃ n : ℤ, p' = scaleDiag (q ^ n) p) ∧
      ∀ p ∈ quadrant, ∃! n : ℤ, scaleDiag (q ^ n) p ∈ cylinder q := by
  have hq0 : 0 < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos hq
  have hne : ∀ p ∈ quadrant, p.1 ≠ 0 := fun p hp => ne_of_gt hp.1
  -- the chart is `(coe × id) ∘ φ`, `φ(y, v) = (log y, v/y)`, with inverse `(u, r) ↦ (eᵘ, reᵘ)`
  set φ : ℝ × ℝ → ℝ × ℝ := fun p => (Real.log p.1, p.2 / p.1) with hφ
  set ψ : ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp p.1, p.2 * Real.exp p.1) with hψ
  have hchart : cylinderChart q = Prod.map (QuotientAddGroup.mk (s := AddSubgroup.zmultiples
      (Real.log q))) id ∘ φ := rfl
  refine ⟨?_, fun U hU hUq => ?_, ?_, fun p hp p' hp' => ?_,
    fun p hp => existsUnique_scaleDiag_mem_cylinder hq hp⟩
  · refine ContinuousOn.prodMk ?_ ?_
    · exact (continuous_quotient_mk'.comp_continuousOn
        (Real.continuousOn_log.comp continuousOn_fst fun p hp => hne p hp))
    · exact continuousOn_snd.div continuousOn_fst hne
  · have himage : φ '' U = ψ ⁻¹' U := by
      ext ⟨u, r⟩
      simp only [mem_image, mem_preimage, hφ, hψ, Prod.mk.injEq]
      constructor
      · rintro ⟨p, hpU, h1, h2⟩
        have hp1 : 0 < p.1 := (hUq hpU).1
        rw [← h1, ← h2, Real.exp_log hp1, div_mul_cancel₀ _ hp1.ne']
        exact hpU
      · intro h
        refine ⟨_, h, Real.log_exp u, ?_⟩
        simp only
        rw [mul_div_cancel_right₀ _ (Real.exp_pos u).ne']
    rw [hchart, image_comp, himage]
    exact (QuotientAddGroup.isOpenMap_coe.prodMap IsOpenMap.id) _
      (hU.preimage (by rw [hψ]; fun_prop))
  · ext ⟨x, r⟩
    simp only [mem_image, mem_prod, mem_univ, true_and, mem_Ioi]
    constructor
    · rintro ⟨p, hp, hpx⟩
      have h2 := congrArg Prod.snd hpx
      simp only [cylinderChart] at h2
      rw [← h2]
      exact div_pos hp.2 hp.1
    · intro hr
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
      refine ⟨(Real.exp u, r * Real.exp u), ⟨Real.exp_pos u, mul_pos hr (Real.exp_pos u)⟩, ?_⟩
      simp only [cylinderChart, Real.log_exp, Prod.mk.injEq, true_and]
      exact mul_div_cancel_right₀ _ (Real.exp_pos u).ne'
  · have hp1 : 0 < p.1 := hp.1
    have hp1' : 0 < p'.1 := hp'.1
    simp only [cylinderChart, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at h1
      obtain ⟨k, hk⟩ := h1
      refine ⟨-k, ?_⟩
      have hy : p'.1 = q ^ (-k) * p.1 := by
        have hlog : Real.log p'.1 = Real.log (q ^ (-k) * p.1) := by
          rw [Real.log_mul (zpow_pos hq0 _).ne' hp1.ne', Real.log_zpow, zsmul_eq_mul] at *
          push_cast
          linarith
        exact Real.log_injOn_pos hp1' (mul_pos (zpow_pos hq0 _) hp1) hlog
      refine Prod.ext hy ?_
      simp only [scaleDiag]
      rw [div_eq_div_iff hp1.ne' hp1'.ne'] at h2
      have hpos : 0 < q ^ (-k) := zpow_pos hq0 _
      rw [hy] at h2
      have : p'.2 * p.1 = q ^ (-k) * p.2 * p.1 := by linarith
      exact mul_right_cancel₀ hp1.ne' this
    · rintro ⟨n, rfl⟩
      simp only [scaleDiag]
      have hpos : 0 < q ^ n := zpow_pos hq0 _
      refine ⟨?_, ?_⟩
      · rw [Real.log_mul hpos.ne' hp1.ne', Real.log_zpow, QuotientAddGroup.eq_iff_sub_mem,
          AddSubgroup.mem_zmultiples_iff]
        exact ⟨-n, by rw [zsmul_eq_mul]; push_cast; ring⟩
      · rw [mul_div_mul_left _ _ hpos.ne']

/-! ## `thm:knot-atom-cascades`(2), the bijection -/

/-- `T_n` maps the cylinder into the quadrant. -/
theorem orbitPt_mem_quadrant {q : ℝ} (hq0 : 0 < q) {p : ℝ × ℝ} (hp : p ∈ cylinder q) (n : ℤ) :
    orbitPt q n p ∈ quadrant := by
  have h1 : 0 < p.1 := lt_of_lt_of_le one_pos hp.1.1
  exact ⟨mul_pos h1 (zpow_pos hq0 n), mul_pos (mul_pos hp.2 h1) (zpow_pos hq0 n)⟩

/-- `T_n p ∈ 𝒞` for `p ∈ 𝒞` only at `n = 0`. -/
theorem orbitPt_mem_cylinder_iff {q : ℝ} (hq : 1 < q) {p : ℝ × ℝ} (hp : p ∈ cylinder q)
    (n : ℤ) : orbitPt q n p ∈ cylinder q ↔ n = 0 := by
  have hq0 : 0 < q := by linarith
  constructor
  · intro h
    exact (mul_zpow_mem_Ico_iff hq hp.1 n).1 h.1
  · rintro rfl
    have h1 : 0 < p.1 := lt_of_lt_of_le one_pos hp.1.1
    simp only [orbitPt, zpow_zero, mul_one]
    exact ⟨hp.1, mul_pos hp.2 h1⟩

theorem scaleDiag_orbitPt (q : ℝ) (hq0 : 0 < q) (n : ℤ) (p : ℝ × ℝ) :
    scaleDiag q (orbitPt q n p) = orbitPt q (n + 1) p := by
  simp only [scaleDiag, orbitPt, zpow_add_one₀ hq0.ne']
  ext <;> simp only <;> ring

/-- **`thm:knot-atom-cascades`(2), the bijection, one direction**: a measure on the cylinder gives
an invariant measure on the quadrant whose cylinder measure is the given one. -/
theorem orbitMixture_spec {q : ℝ} (hq : 1 < q) {σ : Measure (ℝ × ℝ)}
    (hσ : σ (cylinder q)ᶜ = 0) :
    orbitMixture q σ quadrantᶜ = 0 ∧ (orbitMixture q σ).map (scaleDiag q) = orbitMixture q σ ∧
      cylMeasure q (orbitMixture q σ) = σ := by
  have hq0 : 0 < q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [orbitMixture_apply q σ measurableSet_quadrant.compl, ENNReal.tsum_eq_zero]
    intro n
    refine measure_mono_null (fun p hp => ?_) hσ
    intro hpc
    exact hp (orbitPt_mem_quadrant hq0 hpc n)
  · ext s hs
    rw [Measure.map_apply (measurable_scaleDiag q) hs,
      orbitMixture_apply q σ (measurable_scaleDiag q hs), orbitMixture_apply q σ hs]
    have e : ∀ n : ℤ, orbitPt q n ⁻¹' (scaleDiag q ⁻¹' s) = orbitPt q (n + 1) ⁻¹' s := by
      intro n
      ext p
      simp only [mem_preimage, scaleDiag_orbitPt q hq0]
    simp_rw [e]
    exact (Equiv.addRight (1 : ℤ)).tsum_eq fun n => σ (orbitPt q n ⁻¹' s)
  · ext s hs
    have hm : MeasurableSet (cylMap ⁻¹' s ∩ cylinder q) :=
      (measurable_cylMap hs).inter (measurableSet_cylinder q)
    rw [cylMeasure_apply q _ hs, orbitMixture_apply q σ hm, tsum_eq_single 0]
    · refine measure_eq_of_inter_cyl hσ ?_
      ext p
      simp only [mem_inter_iff, mem_preimage, and_congr_left_iff]
      intro hp
      have h1 : 0 < p.1 := lt_of_lt_of_le one_pos hp.1.1
      have hpt : orbitPt q 0 p ∈ cylinder q := (orbitPt_mem_cylinder_iff hq hp 0).2 rfl
      simp only [hpt, and_true]
      have : cylMap (orbitPt q 0 p) = p := by
        simp only [cylMap, orbitPt, zpow_zero, mul_one]
        rw [mul_div_cancel_right₀ _ h1.ne']
      rw [this]
    · intro n hn
      refine measure_mono_null (fun p hp => ?_) hσ
      intro hpc
      exact hn ((orbitPt_mem_cylinder_iff hq hpc n).1 hp.2)

/-- **`thm:knot-atom-cascades`(2), the other direction**: an invariant measure on the quadrant is
the mixture of its cylinder measure. -/
theorem cylMeasure_spec {q : ℝ} (hq : 1 < q) {Λ : Measure (ℝ × ℝ)} (hc : Λ quadrantᶜ = 0)
    (hinv : Λ.map (scaleDiag q) = Λ) :
    cylMeasure q Λ (cylinder q)ᶜ = 0 ∧ orbitMixture q (cylMeasure q Λ) = Λ := by
  have hq0 : 0 < q := by linarith
  refine ⟨?_, ?_⟩
  · rw [cylMeasure_apply q Λ (measurableSet_cylinder q).compl]
    refine measure_mono_null (fun p hp => ?_) measure_empty
    obtain ⟨hp1, hp2⟩ := hp
    have h1 : 0 < p.1 := lt_of_lt_of_le one_pos hp2.1.1
    exact hp1 ⟨hp2.1, div_pos hp2.2 h1⟩
  · ext s hs
    rw [orbitMixture_apply q _ hs, measure_eq_tsum_cyl hq hc hs]
    conv_rhs => rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1
    funext n
    simp only [Equiv.neg_apply]
    rw [cylMeasure_apply q Λ (measurable_orbitPt q n hs)]
    -- on the domain, `T_n ∘ cylMap = Jⁿ`
    have e : cylMap ⁻¹' (orbitPt q n ⁻¹' s) ∩ cylinder q =
        scaleDiag (q ^ n) ⁻¹' (s ∩ scaleDiag (q ^ (-n)) ⁻¹' cylinder q) := by
      ext p
      simp only [mem_inter_iff, mem_preimage]
      have hJ : scaleDiag (q ^ (-n)) (scaleDiag (q ^ n) p) = p := by
        rw [← Function.comp_apply (f := scaleDiag (q ^ (-n))), ← scaleDiag_mul,
          ← zpow_add₀ hq0.ne', neg_add_cancel, zpow_zero, scaleDiag_one, id]
      rw [hJ]
      refine and_congr_left fun hp => ?_
      have h1 : 0 < p.1 := lt_of_lt_of_le one_pos hp.1.1
      have : orbitPt q n (cylMap p) = scaleDiag (q ^ n) p := by
        simp only [orbitPt, cylMap, scaleDiag]
        rw [div_mul_cancel₀ _ h1.ne', mul_comm p.1, mul_comm p.2]
      rw [this]
    rw [e, measure_preimage_scaleDiag_zpow hq0 hinv n
      (hs.inter (measurable_scaleDiag _ (measurableSet_cylinder q)))]

/-- **`thm:knot-atom-cascades`(2), the bijection.** `Λ ↦ σ` maps the `J`-invariant measures on
`(0,∞)²` to measures on `𝒞`, with inverse `σ ↦ Λ_σ`. -/
theorem knot_atom_cascades_2_bij {q : ℝ} (hq : 1 < q) :
    (∀ Λ : Measure (ℝ × ℝ), Λ quadrantᶜ = 0 → Λ.map (scaleDiag q) = Λ →
        cylMeasure q Λ (cylinder q)ᶜ = 0 ∧ orbitMixture q (cylMeasure q Λ) = Λ) ∧
      ∀ σ : Measure (ℝ × ℝ), σ (cylinder q)ᶜ = 0 →
        orbitMixture q σ quadrantᶜ = 0 ∧ (orbitMixture q σ).map (scaleDiag q) = orbitMixture q σ ∧
          cylMeasure q (orbitMixture q σ) = σ :=
  ⟨fun _ hc hinv => cylMeasure_spec hq hc hinv, fun _ hσ => orbitMixture_spec hq hσ⟩

/-! ## `thm:knot-atom-cascades`(2), integrability -/

/-- **Summability on `ℤ`**: a nonnegative `f` vanishing beyond `N` and at most `Cq^{2n}`. -/
theorem summable_of_le_zpow {q : ℝ} (hq : 1 < q) {f : ℤ → ℝ} (N : ℕ) (C : ℝ)
    (h0 : ∀ n, 0 ≤ f n) (hzero : ∀ n : ℤ, (N : ℤ) < n → f n = 0)
    (hle : ∀ n, f n ≤ C * q ^ (2 * n)) : Summable f := by
  have hq0 : 0 < q := by linarith
  have hq2 : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => hzero n ?_
    simp only [Finset.mem_range, not_lt] at hn
    omega
  · refine Summable.of_nonneg_of_le (fun n => h0 _) (fun n => (hle _).trans (le_of_eq ?_))
      ((summable_geometric_of_lt_one (by positivity) hq2).mul_left C)
    rw [mul_neg, zpow_neg, zpow_mul, zpow_natCast, inv_pow, zpow_two, sq]

/-- The integrand of the slab integral at `t = 1`, pulled back to the cylinder:
`S(θ, r) = ∑ₙ 𝟙_{0 < θqⁿ ≤ 1} (1 ∧ (rθqⁿ)²)`. -/
noncomputable def cylSlabSum (q : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ∑' n : ℤ, (Ioc 0 1 ×ˢ univ).indicator (fun x : ℝ × ℝ => ENNReal.ofReal (min 1 (x.2 ^ 2)))
    (orbitPt q n p)

theorem measurableSet_Ioc_univ (s t : ℝ) : MeasurableSet (Ioc s t ×ˢ (univ : Set ℝ)) :=
  measurableSet_Ioc.prod MeasurableSet.univ

/-- **The slab integral of `Λ_σ` at `t = 1` is `∫ S dσ`**. -/
theorem lintegral_slab_orbitMixture (q : ℝ) (σ : Measure (ℝ × ℝ)) :
    ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(slab (orbitMixture q σ) 0 1) =
      ∫⁻ p, cylSlabSum q p ∂σ := by
  have hg : Measurable ((Ioc 0 1 ×ˢ univ).indicator
      (fun x : ℝ × ℝ => ENNReal.ofReal (min 1 (x.2 ^ 2)))) :=
    Measurable.indicator (by fun_prop) (measurableSet_Ioc_univ 0 1)
  rw [lintegral_slab _ _ _ (by fun_prop), ← lintegral_indicator (measurableSet_Ioc_univ 0 1),
    orbitMixture_eq_sum, lintegral_sum_measure]
  simp_rw [lintegral_map hg (measurable_orbitPt q _)]
  unfold cylSlabSum
  exact (lintegral_tsum fun n => (hg.comp (measurable_orbitPt q n)).aemeasurable).symm

/-- **`S(θ, r) = (1 ∧ (rθ)²)𝟙_{θ = 1} + b(rθ)`** on the cylinder, `b` the bracket. -/
theorem cylSlabSum_eq {q : ℝ} (hq : 1 < q) {p : ℝ × ℝ} (hp : p ∈ cylinder q) :
    cylSlabSum q p = (Ioc 0 1 ×ˢ univ).indicator
        (fun x : ℝ × ℝ => ENNReal.ofReal (min 1 (x.2 ^ 2))) (orbitPt q 0 p) +
      ENNReal.ofReal (ladderBracket q (p.2 * p.1)) := by
  have hq0 : 0 < q := by linarith
  have h1 : 1 ≤ p.1 := hp.1.1
  have hp0 : 0 < p.1 := by linarith
  unfold cylSlabSum
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  congr 1
  · rw [tsum_eq_single 0]
    · rfl
    · intro n hn
      rw [indicator_of_notMem]
      intro hmem
      have hqn : q ≤ q ^ (n : ℤ) := by rw [zpow_natCast]; exact le_self_pow₀ hq.le hn
      have h2 : (orbitPt q n p).1 ≤ 1 := hmem.1.2
      simp only [orbitPt] at h2
      nlinarith
  · rw [ladderBracket, ENNReal.ofReal_tsum_of_nonneg
      (fun m => le_min (sq_nonneg _) zero_le_one) (ladderBracket_summable hq _)]
    congr 1
    funext m
    have e : q ^ (-((m : ℤ) + 1)) = (q ^ (m + 1))⁻¹ := by
      rw [zpow_neg, show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    have hqm : q ≤ q ^ (m + 1) := le_self_pow₀ hq.le (Nat.succ_ne_zero m)
    have hpos : 0 < q ^ (m + 1) := pow_pos hq0 _
    rw [indicator_of_mem]
    · simp only [orbitPt, e]
      rw [min_comm, ← div_eq_mul_inv]
    · refine ⟨⟨?_, ?_⟩, mem_univ _⟩
      · simp only [orbitPt, e]
        positivity
      · simp only [orbitPt, e]
        rw [← div_eq_mul_inv, div_le_one hpos]
        linarith [hp.1.2]

theorem posLog_le_cylWeight {x : ℝ} : Real.posLog x ≤ cylWeight x := by
  refine le_min ?_ (le_add_of_nonneg_left zero_le_one)
  rw [Real.posLog_def]
  refine max_le (sq_nonneg x) ?_
  by_cases hx : x ≤ 1
  · by_cases hx0 : 0 ≤ x
    · exact (Real.log_nonpos hx0 hx).trans (sq_nonneg x)
    · -- `log x = log |x|`, `|x| ≤ ... `; `log x ≤ |x| - 1 < x²` for `x ≠ 0`
      have hx' : x ≠ 0 := by intro h; rw [h] at hx0; exact hx0 le_rfl
      have := Real.log_le_sub_one_of_pos (abs_pos.2 hx')
      rw [Real.log_abs] at this
      nlinarith [abs_nonneg x, sq_abs x]
  · have hx1 : 0 < x := by linarith
    have := Real.log_le_sub_one_of_pos hx1
    simp only
    nlinarith

theorem min_sq_one_le_cylWeight (x : ℝ) : min (x ^ 2) 1 ≤ cylWeight x :=
  min_le_min le_rfl (le_add_of_nonneg_right Real.posLog_nonneg)

theorem cylWeight_nonneg (x : ℝ) : 0 ≤ cylWeight x :=
  le_min (sq_nonneg x) (add_nonneg zero_le_one Real.posLog_nonneg)

/-- **`b ≤ C₁ w`**: `b(x) ≤ (1/ℓ + q²/(q² - 1)) (x² ∧ (1 + log₊x))`. -/
theorem ladderBracket_le_cylWeight {q : ℝ} (hq : 1 < q) {x : ℝ} (hx : 0 ≤ x) :
    ladderBracket q x ≤ (1 / Real.log q + q ^ 2 / (q ^ 2 - 1)) * cylWeight x := by
  have hl : 0 < Real.log q := Real.log_pos hq
  have hK : 0 ≤ q ^ 2 / (q ^ 2 - 1) := div_nonneg (sq_nonneg q) (by nlinarith)
  refine (ladderBracket_le hq hx).trans ?_
  rw [add_mul, div_eq_mul_inv (Real.posLog x), one_div, mul_comm (Real.posLog x)]
  exact add_le_add (mul_le_mul_of_nonneg_left posLog_le_cylWeight (inv_nonneg.2 hl.le))
    (mul_le_mul_of_nonneg_left (min_sq_one_le_cylWeight x) hK)

/-- **`w ≤ C₃ b`**: `x² ∧ (1 + log₊x) ≤ (q² + 1 + 2ℓ) b(x)`. -/
theorem cylWeight_le_ladderBracket {q : ℝ} (hq : 1 < q) {x : ℝ} (hx : 0 ≤ x) :
    cylWeight x ≤ (q ^ 2 + 1 + 2 * Real.log q) * ladderBracket q x := by
  have hq0 : 0 < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos hq
  have hb0 := ladderBracket_nonneg q x
  have hfirst : min ((x / q) ^ 2) 1 ≤ ladderBracket q x := by
    have := (ladderBracket_summable hq x).le_tsum 0
      (fun j _ => le_min (sq_nonneg _) zero_le_one)
    simpa [ladderBracket] using this
  by_cases hxq : x ≤ q
  · have hsq : (x / q) ^ 2 ≤ 1 := by
      rw [div_pow, div_le_one (by positivity)]
      exact pow_le_pow_left₀ hx hxq 2
    rw [min_eq_left hsq] at hfirst
    have e : x ^ 2 = q ^ 2 * (x / q) ^ 2 := by field_simp
    calc cylWeight x ≤ x ^ 2 := min_le_left _ _
      _ = q ^ 2 * (x / q) ^ 2 := e
      _ ≤ q ^ 2 * ladderBracket q x := mul_le_mul_of_nonneg_left hfirst (sq_nonneg q)
      _ ≤ (q ^ 2 + 1 + 2 * Real.log q) * ladderBracket q x := by nlinarith
  · have hxq' : q < x := lt_of_not_ge hxq
    have hsq : 1 ≤ (x / q) ^ 2 := by
      rw [div_pow, one_le_div (by positivity)]
      exact pow_le_pow_left₀ hq0.le hxq'.le 2
    rw [min_eq_right hsq] at hfirst
    have hlog := posLog_le_ladderBracket hq (show 1 < x by linarith)
    calc cylWeight x ≤ 1 + Real.posLog x := min_le_right _ _
      _ ≤ (q ^ 2 + 1 + 2 * Real.log q) * ladderBracket q x := by nlinarith

/-- `w(x) > 0` for `x > 0`. -/
theorem cylWeight_pos {x : ℝ} (hx : 0 < x) : 0 < cylWeight x :=
  lt_min (by positivity) (add_pos_of_pos_of_nonneg one_pos Real.posLog_nonneg)

/-- **`thm:knot-atom-cascades`(2), integrability and lines.** `Λ_σ` satisfies the integrability of
`thm:surface-measure`(i) iff (A.e3), and has no mass on a line `{y} × (0,∞)` iff
`σ({θ} × (0,∞)) = 0` for every `θ`. -/
theorem knot_atom_cascades_2_integrable {q : ℝ} (hq : 1 < q) (σ : Measure (ℝ × ℝ))
    (hσ : σ (cylinder q)ᶜ = 0) :
    (IsLevyIntegrableSurface (orbitMixture q σ) ↔ IsCylIntegrable σ) ∧
      ((∀ y : ℝ, 0 < y → orbitMixture q σ ({y} ×ˢ Ioi 0) = 0) ↔
        ∀ θ : ℝ, σ ({θ} ×ˢ Ioi 0) = 0) := by
  have hq0 : 0 < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos hq
  have hae : ∀ᵐ p ∂σ, p ∈ cylinder q := by rw [ae_iff]; exact hσ
  obtain ⟨-, hinv, -⟩ := orbitMixture_spec hq hσ
  refine ⟨?_, ?_⟩
  · have key : (∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(slab (orbitMixture q σ) 0 1) ≠ ⊤) ↔
        IsCylIntegrable σ := by
      rw [lintegral_slab_orbitMixture, IsCylIntegrable]
      have hC1 : 0 ≤ 1 / Real.log q + q ^ 2 / (q ^ 2 - 1) :=
        add_nonneg (by positivity) (div_nonneg (sq_nonneg q) (by nlinarith))
      have hC3 : 0 ≤ q ^ 2 + 1 + 2 * Real.log q := by positivity
      constructor
      · intro h
        refine ne_top_of_le_ne_top
          (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := q ^ 2 + 1 + 2 * Real.log q)) h) ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono_ae (hae.mono fun p hp => ?_)
        have hx : 0 ≤ p.2 * p.1 := (mul_pos hp.2 (lt_of_lt_of_le one_pos hp.1.1)).le
        rw [cylSlabSum_eq hq hp]
        calc ENNReal.ofReal (cylWeight (p.2 * p.1))
            ≤ ENNReal.ofReal ((q ^ 2 + 1 + 2 * Real.log q) * ladderBracket q (p.2 * p.1)) :=
              ENNReal.ofReal_le_ofReal (cylWeight_le_ladderBracket hq hx)
          _ = ENNReal.ofReal (q ^ 2 + 1 + 2 * Real.log q) *
              ENNReal.ofReal (ladderBracket q (p.2 * p.1)) := ENNReal.ofReal_mul hC3
          _ ≤ _ := by gcongr; exact le_add_self
      · intro h
        refine ne_top_of_le_ne_top (ENNReal.mul_ne_top
          (ENNReal.ofReal_ne_top (r := 1 + (1 / Real.log q + q ^ 2 / (q ^ 2 - 1)))) h) ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono_ae (hae.mono fun p hp => ?_)
        have hx : 0 ≤ p.2 * p.1 := (mul_pos hp.2 (lt_of_lt_of_le one_pos hp.1.1)).le
        rw [cylSlabSum_eq hq hp]
        have hind : (Ioc 0 1 ×ˢ univ).indicator
            (fun x : ℝ × ℝ => ENNReal.ofReal (min 1 (x.2 ^ 2))) (orbitPt q 0 p) ≤
            ENNReal.ofReal (cylWeight (p.2 * p.1)) := by
          refine (indicator_le_self _ _ _).trans (ENNReal.ofReal_le_ofReal ?_)
          simp only [orbitPt, zpow_zero, mul_one]
          rw [min_comm]
          exact min_sq_one_le_cylWeight _
        calc _ ≤ ENNReal.ofReal (cylWeight (p.2 * p.1)) + ENNReal.ofReal
              ((1 / Real.log q + q ^ 2 / (q ^ 2 - 1)) * cylWeight (p.2 * p.1)) :=
              add_le_add hind (ENNReal.ofReal_le_ofReal (ladderBracket_le_cylWeight hq hx))
          _ = _ := by
            rw [← ENNReal.ofReal_add (cylWeight_nonneg _)
              (mul_nonneg hC1 (cylWeight_nonneg _)), ← ENNReal.ofReal_mul (by positivity)]
            ring_nf
    rw [← key]
    exact ⟨fun h => h 1 one_pos,
      fun h => (surface_measure_integrable_iff hq _ hinv).1 ⟨1, one_pos, h⟩⟩
  · constructor
    · intro h θ
      by_cases hθ : θ ∈ Ico 1 q
      · have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
        refine le_antisymm ?_ (by simp)
        calc σ ({θ} ×ˢ Ioi 0) ≤ σ (orbitPt q 0 ⁻¹' ({θ} ×ˢ Ioi 0)) := measure_mono fun p hp => ?_
          _ ≤ ∑' n : ℤ, σ (orbitPt q n ⁻¹' ({θ} ×ˢ Ioi 0)) := ENNReal.le_tsum 0
          _ = 0 := by
            rw [← orbitMixture_apply q σ ((measurableSet_singleton θ).prod measurableSet_Ioi)]
            exact h θ hθ0
        obtain ⟨h1, h2⟩ := hp
        have h1' : p.1 = θ := h1
        have h2' : 0 < p.2 := h2
        simp only [mem_preimage, orbitPt, zpow_zero, mul_one, mem_prod, mem_singleton_iff,
          mem_Ioi]
        exact ⟨h1', mul_pos h2' (h1' ▸ hθ0)⟩
      · refine measure_mono_null (fun p hp => ?_) hσ
        intro hpc
        have h1' : p.1 = θ := hp.1
        exact hθ (h1' ▸ hpc.1)
    · intro h y _
      rw [orbitMixture_apply q σ ((measurableSet_singleton y).prod measurableSet_Ioi),
        ENNReal.tsum_eq_zero]
      intro n
      refine le_antisymm ?_ (by simp)
      calc σ (orbitPt q n ⁻¹' ({y} ×ˢ Ioi 0))
          = σ (orbitPt q n ⁻¹' ({y} ×ˢ Ioi 0) ∩ cylinder q) := (measure_inter_conull hσ).symm
        _ ≤ σ ({y / q ^ n} ×ˢ Ioi 0) := measure_mono fun p hp => ?_
        _ = 0 := h _
      have h1 : p.1 * q ^ n = y := hp.1.1
      refine ⟨?_, hp.2.2⟩
      change p.1 = y / q ^ n
      rw [← h1, mul_div_cancel_right₀ _ (zpow_pos hq0 n).ne']

/-! ## `thm:knot-atom-cascades`(2), the Gaussian part -/

theorem gaussSpread_apply (q : ℝ) (β : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    gaussSpread q β A =
      ∑' n : ℤ, ENNReal.ofReal (q ^ (2 * n)) * β ((fun y => q ^ n * y) ⁻¹' A) := by
  rw [gaussSpread, Measure.sum_apply _ hA]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_const_mul _) hA]

theorem gaussSpread_add (q : ℝ) (β β' : Measure ℝ) :
    gaussSpread q (β + β') = gaussSpread q β + gaussSpread q β' := by
  ext A hA
  simp only [Measure.add_apply, gaussSpread_apply q _ hA, mul_add]
  exact ENNReal.tsum_add

theorem gaussSpread_smul (q : ℝ) (c : ℝ≥0∞) (β : Measure ℝ) :
    gaussSpread q (c • β) = c • gaussSpread q β := by
  ext A hA
  simp only [Measure.smul_apply, smul_eq_mul, gaussSpread_apply q _ hA]
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext n
  ring

theorem gaussSpread_zero (q : ℝ) : gaussSpread q 0 = 0 := by
  ext A hA
  simp [gaussSpread_apply q _ hA]

/-- (ii) for `n = 1`, on every Borel set: `q² ℬ(q^{-1}A) = ℬ(A)`. -/
theorem gaussian_one {q : ℝ} (hq0 : 0 < q) {B : Measure ℝ} (hB : IsSurfaceGaussian q B)
    {A : Set ℝ} (hA : MeasurableSet A) :
    ENNReal.ofReal (q ^ 2) * B ((fun y => q * y) ⁻¹' A) = B A := by
  have hnull : B (Ioi 0)ᶜ = 0 := by rw [compl_Ioi]; exact hB.1
  set S := (fun y => q * y) ⁻¹' A ∩ Ioi 0 with hS
  have hSm : MeasurableSet S := (measurable_const_mul q hA).inter measurableSet_Ioi
  have himg : (fun y => q * y) '' S = A ∩ Ioi 0 := by
    ext y
    simp only [hS, mem_image, mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
      exact ⟨hx, mul_pos hq0 hx0⟩
    · rintro ⟨hy, hy0⟩
      refine ⟨q⁻¹ * y, ⟨?_, by positivity⟩, ?_⟩
      · rwa [mul_inv_cancel_left₀ hq0.ne']
      · rw [mul_inv_cancel_left₀ hq0.ne']
  have h := hB.2.2 S hSm inter_subset_right
  rw [himg, measure_inter_conull hnull, hS, measure_inter_conull hnull] at h
  exact h.symm

/-- **(ii) iterated**: `q^{2n} ℬ(q^{-n}A) = ℬ(A)` for every `n ∈ ℤ`. -/
theorem gaussian_zpow {q : ℝ} (hq0 : 0 < q) {B : Measure ℝ} (hB : IsSurfaceGaussian q B)
    (n : ℤ) {A : Set ℝ} (hA : MeasurableSet A) :
    ENNReal.ofReal (q ^ (2 * n)) * B ((fun y => q ^ n * y) ⁻¹' A) = B A := by
  have hinv : ∀ A : Set ℝ, MeasurableSet A →
      ENNReal.ofReal ((q ^ 2)⁻¹) * B ((fun y => q⁻¹ * y) ⁻¹' A) = B A := by
    intro A hA
    have h := gaussian_one hq0 hB (measurable_const_mul q⁻¹ hA)
    have e : (fun y => q * y) ⁻¹' ((fun y => q⁻¹ * y) ⁻¹' A) = A := by
      ext y
      simp only [mem_preimage, inv_mul_cancel_left₀ hq0.ne']
    rw [e] at h
    rw [← h, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
  induction n using Int.induction_on generalizing A with
  | zero => simp
  | succ n ih =>
    have e : (fun y => q ^ ((n : ℤ) + 1) * y) ⁻¹' A =
        (fun y => q * y) ⁻¹' ((fun y => q ^ (n : ℤ) * y) ⁻¹' A) := by
      ext y
      simp only [mem_preimage, zpow_add_one₀ hq0.ne']
      ring_nf
    have e2 : q ^ (2 * ((n : ℤ) + 1)) = q ^ (2 * (n : ℤ)) * q ^ 2 := by
      rw [mul_add, mul_one, zpow_add₀ hq0.ne', zpow_two, sq]
    rw [e, e2, ENNReal.ofReal_mul (by positivity), mul_assoc,
      gaussian_one hq0 hB (measurable_const_mul _ hA), ih hA]
  | pred n ih =>
    have e : (fun y => q ^ (-(n : ℤ) - 1) * y) ⁻¹' A =
        (fun y => q⁻¹ * y) ⁻¹' ((fun y => q ^ (-(n : ℤ)) * y) ⁻¹' A) := by
      ext y
      simp only [mem_preimage, zpow_sub_one₀ hq0.ne']
      ring_nf
    have e2 : q ^ (2 * (-(n : ℤ) - 1)) = q ^ (2 * (-(n : ℤ))) * (q ^ 2)⁻¹ := by
      rw [mul_sub, mul_one, zpow_sub₀ hq0.ne', div_eq_mul_inv, zpow_two, sq]
    rw [e, e2, ENNReal.ofReal_mul (by positivity), mul_assoc,
      hinv _ (measurable_const_mul _ hA), ih hA]

/-- **The intervals `q^{-n}[1,q)` partition `(0,∞)`**. -/
theorem measure_eq_tsum_Ico {q : ℝ} (hq : 1 < q) {B : Measure ℝ} (h0 : B (Iic 0) = 0)
    {A : Set ℝ} (hA : MeasurableSet A) :
    B A = ∑' n : ℤ, B (A ∩ (fun y => q ^ n * y) ⁻¹' Ico 1 q) := by
  have hq0 : 0 < q := by linarith
  have hnull : B (Ioi 0)ᶜ = 0 := by rw [compl_Ioi]; exact h0
  rw [← measure_inter_conull hnull]
  have hU : A ∩ Ioi 0 = ⋃ n : ℤ, A ∩ (fun y => q ^ n * y) ⁻¹' Ico 1 q := by
    ext y
    simp only [mem_inter_iff, mem_iUnion, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨hyA, hy⟩
      obtain ⟨n, hn, -⟩ := existsUnique_zpow_mul_mem_Ico hq hy
      exact ⟨n, hyA, hn⟩
    · rintro ⟨n, hyA, hn⟩
      exact ⟨hyA, pos_of_mul_pos_right (lt_of_lt_of_le one_pos hn.1) (zpow_pos hq0 n).le⟩
  rw [hU, measure_iUnion]
  · intro m n hmn
    refine Set.disjoint_left.2 fun y hm hn => hmn ?_
    have hy : 0 < y := pos_of_mul_pos_right (lt_of_lt_of_le one_pos hm.2.1) (zpow_pos hq0 m).le
    exact (existsUnique_zpow_mul_mem_Ico hq hy).unique hm.2 hn.2
  · exact fun n => hA.inter (measurable_const_mul _ measurableSet_Ico)

/-- **`thm:knot-atom-cascades`(2), the Gaussian part.** `ℬ` with (ii) corresponds to its restriction
`β` to `[1,q)` by `ℬ(A) = ∑ₙ q^{2n} β(q^{-n}A ∩ [1,q))`. -/
theorem knot_atom_cascades_2_gaussian {q : ℝ} (hq : 1 < q) :
    (∀ B : Measure ℝ, IsSurfaceGaussian q B → gaussSpread q (B.restrict (Ico 1 q)) = B) ∧
      ∀ β : Measure ℝ, IsFiniteMeasure β → β (Ico 1 q)ᶜ = 0 →
        IsSurfaceGaussian q (gaussSpread q β) ∧ (gaussSpread q β).restrict (Ico 1 q) = β := by
  have hq0 : 0 < q := by linarith
  refine ⟨fun B hB => ?_, fun β hβf hβ => ?_⟩
  · ext A hA
    rw [gaussSpread_apply q _ hA, measure_eq_tsum_Ico hq hB.1 hA]
    conv_rhs => rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1
    funext n
    simp only [Equiv.neg_apply]
    rw [Measure.restrict_apply (measurable_const_mul _ hA)]
    have e : (fun y => q ^ n * y) ⁻¹' A ∩ Ico 1 q =
        (fun y => q ^ n * y) ⁻¹' (A ∩ (fun y => q ^ (-n) * y) ⁻¹' Ico 1 q) := by
      ext y
      simp only [mem_inter_iff, mem_preimage]
      rw [← mul_assoc, ← zpow_add₀ hq0.ne', neg_add_cancel, zpow_zero, one_mul]
    rw [e, gaussian_zpow hq0 hB n (hA.inter (measurable_const_mul _ measurableSet_Ico))]
  · have hae : ∀ᵐ y ∂β, y ∈ Ico 1 q := by rw [ae_iff]; exact hβ
    have hzero : ∀ n : ℤ, ∀ S : Set ℝ, (∀ y ∈ Ico 1 q, q ^ n * y ∉ S) →
        β ((fun y => q ^ n * y) ⁻¹' S) = 0 := fun n S hS =>
      measure_mono_null (fun y hy hyc => hS y hyc hy) hβ
    refine ⟨⟨?_, fun t ht => ?_, fun A hA hA0 => ?_⟩, ?_⟩
    · rw [gaussSpread_apply q _ measurableSet_Iic, ENNReal.tsum_eq_zero]
      intro n
      rw [hzero n _ fun y hy hle => ?_, mul_zero]
      have : 0 < q ^ n * y := mul_pos (zpow_pos hq0 n) (lt_of_lt_of_le one_pos hy.1)
      exact absurd hle (not_le.2 this)
    · obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt t hq
      set f : ℤ → ℝ := fun n => if n < (N : ℤ) then q ^ (2 * n) else 0 with hf
      have hf0 : ∀ n, 0 ≤ f n := fun n => by
        simp only [hf]; split_ifs <;> positivity
      have hfs : Summable f := summable_of_le_zpow hq (f := f) N 1 hf0
        (fun n hn => by simp only [hf]; rw [if_neg (by omega)])
        (fun n => by simp only [hf]; split_ifs <;> linarith [zpow_pos hq0 (2 * n)])
      rw [gaussSpread_apply q _ measurableSet_Ioc]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := ∑' n, f n))
        (measure_ne_top β univ)) ?_
      rw [ENNReal.ofReal_tsum_of_nonneg hf0 hfs, ← ENNReal.tsum_mul_right]
      refine ENNReal.tsum_le_tsum fun n => ?_
      by_cases hn : n < (N : ℤ)
      · simp only [hf, if_pos hn]
        gcongr
        exact subset_univ _
      · rw [hzero n _ fun y hy hmem => ?_, mul_zero]
        · simp
        have hqn : q ^ (N : ℤ) ≤ q ^ n := zpow_le_zpow_right₀ hq.le (by omega)
        rw [zpow_natCast] at hqn
        have : q ^ n ≤ q ^ n * y := le_mul_of_one_le_right (zpow_pos hq0 n).le hy.1
        linarith [hmem.2]
    · -- the scaling `𝒢(qA) = q² 𝒢(A)`
      have himg : (fun y => q * y) '' A = (fun y => q⁻¹ * y) ⁻¹' A := by
        ext y
        simp only [mem_image, mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rwa [inv_mul_cancel_left₀ hq0.ne']
        · intro hy
          exact ⟨q⁻¹ * y, hy, mul_inv_cancel_left₀ hq0.ne' y⟩
      rw [himg, gaussSpread_apply q _ (measurable_const_mul _ hA), gaussSpread_apply q _ hA,
        ← ENNReal.tsum_mul_left]
      refine ((Equiv.addRight (1 : ℤ)).tsum_eq _).symm.trans ?_
      congr 1
      funext n
      simp only [Equiv.coe_addRight]
      have e : (fun y => q ^ (n + 1) * y) ⁻¹' ((fun y => q⁻¹ * y) ⁻¹' A) =
          (fun y => q ^ n * y) ⁻¹' A := by
        ext y
        simp only [mem_preimage, zpow_add_one₀ hq0.ne']
        rw [← mul_assoc, mul_comm q⁻¹, mul_assoc (q ^ n), mul_inv_cancel₀ hq0.ne', mul_one]
      have e2 : q ^ (2 * (n + 1)) = q ^ 2 * q ^ (2 * n) := by
        rw [mul_add, mul_one, zpow_add₀ hq0.ne', mul_comm, zpow_two, sq]
      rw [e, e2, ENNReal.ofReal_mul (by positivity), mul_assoc]
    · ext A hA
      rw [Measure.restrict_apply hA, gaussSpread_apply q _ (hA.inter measurableSet_Ico),
        tsum_eq_single 0]
      · simp only [mul_zero, zpow_zero, ENNReal.ofReal_one, one_mul, preimage_id']
        exact measure_inter_conull hβ
      · intro n hn
        rw [hzero n _ fun y hy hmem => hn ?_, mul_zero]
        rw [mul_comm] at hmem
        exact (mul_zpow_mem_Ico_iff hq hy n).1 hmem.2

end Pyramids
