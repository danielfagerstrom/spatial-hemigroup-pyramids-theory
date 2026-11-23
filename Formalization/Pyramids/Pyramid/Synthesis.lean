/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.DiscreteCovarianceLevy

/-!
# `lem:synthesis`: a family from one octave of data

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `lem:synthesis`, chapter 3. Wave 2d: the
declaration moved here from `PyramidsSkeleton.Ch03Pyramid`, its statement unchanged. Wave 2e
(2026-11-14) dropped the unused hypothesis `1 ≤ d`, a strengthening.

## The route

The printed one, organised around the data `octaveData q D t` at each `t`.

* **The extension is a dilate.** For `t = qⁿu` with `u ∈ [1, q)` the extended data are the dilate
  `(q^{2n}A_u, D_{qⁿ}ν_u)` of `D u` (`SymLevyData.dilate`), and so are they for `u = q` by the
  gluing condition (`octaveData_at`). So the data are symmetric Lévy data at every `t > 0`, and
  `Ψ_{qⁿu}(ω) = Ψ_u(qⁿω)` for `u ∈ [1, q]`.
* **Monotonicity across octaves.** Within a closed octave the order of data
  (`SymLevyData.Le`: `A' - A` positive semidefinite and `ν ≤ ν'`) and their difference are those
  of the hypothesis, carried by the dilation. Across octaves the order is transitive, and a
  difference that vanished between two ends would vanish at every point in between (the Loewner
  order and the order of measures are antisymmetric), so differences stay nonzero
  (`octaveData_lt`).
* **The increments.** For `D ≤ E` some symmetric Lévy data `Q` have `E = D + Q`: the difference of
  the measures is built on the pieces of `{0} ∪ {|x| > 1/(n+1)}`, where `ν_D` is finite, and
  symmetrised (`SymLevyData.exists_sub`). The law of `Q` exists by ledger A39(iii), and its
  transform is `e^{-(Ψ_t - Ψ_s)}`.
* **The family.** (I1) is the additivity of exponents and the identity `e⁰ = 1`; symmetry is the
  evenness of the exponent; (ND) holds because a law with the data `Q` and the transform `1` would
  give `Q = 0` by the uniqueness of data (A39(ii)); covariance is `Ψ_{qt}(ω) = Ψ_t(qω)`; and (I2)
  is the continuity of `t ↦ Ψ_t(ω)` on `[0,∞)`: on each closed octave by hypothesis, at a knot from
  the two sides, and at `0` because `0 ≤ Ψ_t(ω) ≤ Ψ_{q^{-m}}(ω) = Ψ_1(q^{-m}ω) → 0`.
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace MatrixOrder

variable {d : ℕ}

/-! ## Octave arithmetic -/

theorem dgLevel_eq {q : ℝ} (hq : 1 < q) {t : ℝ} {n : ℤ} (h1 : q ^ n ≤ t) (h2 : t < q ^ (n + 1)) :
    dgLevel q t = n := by
  have hq0 : 0 < q := by linarith
  have ht : 0 < t := lt_of_lt_of_le (zpow_pos hq0 n) h1
  unfold dgLevel
  rw [Int.floor_eq_iff]
  constructor
  · rw [Real.le_logb_iff_rpow_le hq ht, Real.rpow_intCast]
    exact h1
  · rw [Real.logb_lt_iff_lt_rpow hq ht]
    have : (q : ℝ) ^ ((n : ℝ) + 1) = q ^ (n + 1) := by
      rw [← Real.rpow_intCast]; push_cast; rfl
    rw [this]
    exact h2

theorem dgLevel_spec {q : ℝ} (hq : 1 < q) {t : ℝ} (ht : 0 < t) :
    q ^ dgLevel q t ≤ t ∧ t < q ^ (dgLevel q t + 1) := by
  unfold dgLevel
  constructor
  · rw [← Real.rpow_intCast, ← Real.le_logb_iff_rpow_le hq ht]
    exact Int.floor_le _
  · have : (q : ℝ) ^ (⌊Real.logb q t⌋ + 1) = q ^ ((⌊Real.logb q t⌋ : ℝ) + 1) := by
      rw [← Real.rpow_intCast]; push_cast; rfl
    rw [this, ← Real.logb_lt_iff_lt_rpow hq ht]
    exact Int.lt_floor_add_one _

/-- `t = qⁿu` with `n = ⌊log_q t⌋` and `u = q^{-n}t ∈ [1, q)`. -/
theorem octave_mem {q : ℝ} (hq : 1 < q) {t : ℝ} (ht : 0 < t) :
    q ^ (-dgLevel q t) * t ∈ Ico 1 q := by
  have hq0 : 0 < q := by linarith
  obtain ⟨h1, h2⟩ := dgLevel_spec hq ht
  have hp : 0 < q ^ dgLevel q t := zpow_pos hq0 _
  rw [zpow_neg]
  constructor
  · rw [le_inv_mul_iff₀ hp, mul_one]; exact h1
  · rw [inv_mul_lt_iff₀ hp, ← zpow_add_one₀ hq0.ne']; exact h2

/-! ## Symmetric Lévy data: equality, order, zero -/

theorem SymLevyData.ext' {D E : SymLevyData d} (hA : D.A = E.A) (hν : D.ν = E.ν) : D = E := by
  cases D; cases E; simp_all

/-- The zero data. -/
noncomputable def SymLevyData.zero : SymLevyData d :=
  ⟨0, 0, Matrix.PosSemidef.zero, rfl, by simp, by simp⟩

theorem SymLevyData.zero_exponent (ω : Rd d) :
    (SymLevyData.zero : SymLevyData d).exponent ω = 0 := by
  simp [SymLevyData.zero, SymLevyData.exponent, pairExponent, quad_zero]

/-- **The order of data**: `A' - A` positive semidefinite and `ν ≤ ν'`. -/
def SymLevyData.Le (D E : SymLevyData d) : Prop := D.A ≤ E.A ∧ D.ν ≤ E.ν

theorem SymLevyData.Le.refl (D : SymLevyData d) : D.Le D := ⟨le_rfl, le_rfl⟩

theorem SymLevyData.Le.trans {D E F : SymLevyData d} (h1 : D.Le E) (h2 : E.Le F) : D.Le F :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- **Antisymmetry in the middle**: `D ≤ E ≤ F` with `D`, `F` of the same data gives `E` the same
data. -/
theorem SymLevyData.Le.eq_of_eq {D E F : SymLevyData d} (h1 : D.Le E) (h2 : E.Le F)
    (h : (D.A, D.ν) = (F.A, F.ν)) : (E.A, E.ν) = (D.A, D.ν) := by
  obtain ⟨hA, hν⟩ := Prod.mk.inj h
  refine Prod.ext (le_antisymm ?_ h1.1) (le_antisymm ?_ h1.2)
  · rw [hA]; exact h2.1
  · rw [hν]; exact h2.2

theorem SymLevyData.Le.ne_left {D E F : SymLevyData d} (h1 : D.Le E) (h2 : E.Le F)
    (h : (D.A, D.ν) ≠ (E.A, E.ν)) : (D.A, D.ν) ≠ (F.A, F.ν) := fun he =>
  h (h1.eq_of_eq h2 he).symm

theorem SymLevyData.Le.ne_right {D E F : SymLevyData d} (h1 : D.Le E) (h2 : E.Le F)
    (h : (E.A, E.ν) ≠ (F.A, F.ν)) : (D.A, D.ν) ≠ (F.A, F.ν) := fun he => by
  have h3 := h1.eq_of_eq h2 he
  apply h
  rw [h3, he]

theorem SymLevyData.zero_data_le (D : SymLevyData d) : (SymLevyData.zero : SymLevyData d).Le D :=
  ⟨by rw [Matrix.le_iff]; simpa [SymLevyData.zero] using D.A_posSemidef,
    by simpa [SymLevyData.zero] using Measure.zero_le D.ν⟩

/-! ## Dilation and the order -/

theorem SymLevyData.dilate_le {D E : SymLevyData d} (h : D.Le E) {c : ℝ} (hc : c ≠ 0) :
    (D.dilate hc).Le (E.dilate hc) := by
  refine ⟨?_, Measure.map_mono h.2 (continuous_const_smul c).measurable⟩
  rw [Matrix.le_iff]
  change (c ^ 2 • E.A - c ^ 2 • D.A).PosSemidef
  rw [← smul_sub]
  exact (Matrix.le_iff.1 h.1).smul (sq_nonneg c)

theorem map_smul_injective {c : ℝ} (hc : c ≠ 0) {m m' : Measure (Rd d)}
    (h : m.map (fun x => c • x) = m'.map (fun x => c • x)) : m = m' := by
  have h2 := congrArg (fun n : Measure (Rd d) => n.map fun x => c⁻¹ • x) h
  simp only [Measure.map_map (continuous_const_smul _).measurable
    (continuous_const_smul _).measurable] at h2
  have e : ((fun x : Rd d => c⁻¹ • x) ∘ fun x => c • x) = id := by
    funext x
    simp [smul_smul, inv_mul_cancel₀ hc]
  rwa [e, Measure.map_id, Measure.map_id] at h2

theorem SymLevyData.dilate_ne {D E : SymLevyData d} {c : ℝ} (hc : c ≠ 0)
    (h : (D.A, D.ν) ≠ (E.A, E.ν)) :
    ((D.dilate hc).A, (D.dilate hc).ν) ≠ ((E.dilate hc).A, (E.dilate hc).ν) := by
  intro he
  obtain ⟨hA, hν⟩ := Prod.mk.inj he
  apply h
  refine Prod.ext ?_ (map_smul_injective hc hν)
  exact smul_right_injective _ (pow_ne_zero 2 hc) hA

theorem SymLevyData.dilate_dilate (D : SymLevyData d) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (D.dilate ha).dilate hb = D.dilate (mul_ne_zero hb ha) := by
  refine SymLevyData.ext' ?_ ?_
  · change b ^ 2 • a ^ 2 • D.A = (b * a) ^ 2 • D.A
    rw [smul_smul, mul_pow]
  · change (D.ν.map fun x => a • x).map (fun x => b • x) = D.ν.map fun x => (b * a) • x
    rw [Measure.map_map (continuous_const_smul _).measurable (continuous_const_smul _).measurable]
    congr 1
    funext x
    simp [smul_smul]

/-! ## The difference of two ordered data -/

/-- A Lévy measure is finite off every ball about `0`. -/
theorem SymLevyData.measure_norm_gt_ne_top (D : SymLevyData d) {ε : ℝ} (hε : 0 < ε) :
    D.ν {x | ε < ‖x‖} ≠ ⊤ := by
  set c : ℝ≥0∞ := ENNReal.ofReal (min (ε ^ 2) 1) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_min (by positivity) one_pos
  have hle : c * D.ν {x | c ≤ ENNReal.ofReal (min (‖x‖ ^ 2) 1)} ≤
      ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂D.ν :=
    mul_meas_ge_le_lintegral₀ (by fun_prop) c
  have hsub : {x : Rd d | ε < ‖x‖} ⊆ {x | c ≤ ENNReal.ofReal (min (‖x‖ ^ 2) 1)} := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal (min_le_min ?_ le_rfl)
    have hx' : ε < ‖x‖ := hx
    nlinarith
  have h1 : c * D.ν {x | ε < ‖x‖} ≠ ⊤ :=
    ne_top_of_le_ne_top D.ν_integrable ((mul_le_mul_right (measure_mono hsub) c).trans hle)
  intro htop
  rw [htop, ENNReal.mul_top hc0] at h1
  exact h1 rfl

/-- **The difference of two ordered Lévy measures**: if `ν_D ≤ ν'`, some measure `ρ` has
`ρ + ν_D = ν'`. Built on the pieces of `{0} ∪ {|x| > 1/(n+1)}`, made disjoint, where `ν_D` is
finite. -/
theorem SymLevyData.exists_measure_sub (D : SymLevyData d) {ν' : Measure (Rd d)}
    (hle : D.ν ≤ ν') : ∃ ρ : Measure (Rd d), ρ + D.ν = ν' := by
  set T : ℕ → Set (Rd d) := fun n => {0} ∪ {x | 1 / ((n : ℝ) + 1) < ‖x‖} with hT
  set S := disjointed T with hS
  have hTm : ∀ n, MeasurableSet (T n) := fun n =>
    (measurableSet_singleton 0).union (measurableSet_lt measurable_const measurable_norm)
  have hSm : ∀ n, MeasurableSet (S n) := MeasurableSet.disjointed hTm
  have hSd : Pairwise (Function.onFun Disjoint S) := disjoint_disjointed T
  have hSU : ⋃ n, S n = univ := by
    rw [hS, iUnion_disjointed]
    refine eq_univ_of_forall fun x => ?_
    rcases eq_or_ne x 0 with hx | hx
    · exact mem_iUnion.2 ⟨0, Or.inl hx⟩
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 hx)
      exact mem_iUnion.2 ⟨n, Or.inr hn⟩
  have hfin : ∀ n, D.ν (S n) ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top ?_ (measure_mono (disjointed_subset T n))
    refine ne_top_of_le_ne_top ?_ (measure_union_le _ _)
    rw [D.ν_zero, zero_add]
    exact D.measure_norm_gt_ne_top (by positivity)
  have hsplit : ∀ m : Measure (Rd d), m = Measure.sum fun n => m.restrict (S n) := by
    intro m
    rw [← Measure.restrict_iUnion hSd hSm, hSU, Measure.restrict_univ]
  have key : (Measure.sum fun n => ν'.restrict (S n) - D.ν.restrict (S n)) +
      Measure.sum (fun n => D.ν.restrict (S n)) = Measure.sum fun n => ν'.restrict (S n) := by
    rw [Measure.sum_add_sum]
    refine congrArg Measure.sum (funext fun n => ?_)
    haveI : IsFiniteMeasure (D.ν.restrict (S n)) :=
      isFiniteMeasure_restrict.2 (hfin n)
    exact Measure.sub_add_cancel_of_le (Measure.restrict_mono le_rfl hle)
  rw [← hsplit D.ν, ← hsplit ν'] at key
  exact ⟨_, key⟩

theorem LevyTriplet.ext' {T T' : LevyTriplet d} (hA : T.A = T'.A) (hν : T.ν = T'.ν)
    (hγ : T.γ = T'.γ) : T = T' := by
  cases T; cases T'; simp_all

/-- **The difference of ordered data**: for `D ≤ E`, symmetric Lévy data `Q` have
`Q.A = E.A - D.A`, `Q.ν + ν_D = ν_E`, and `Ψ_E = Ψ_D + Ψ_Q`. -/
theorem SymLevyData.exists_sub {D E : SymLevyData d} (h : D.Le E) :
    ∃ Q : SymLevyData d, Q.A = E.A - D.A ∧ Q.ν + D.ν = E.ν ∧
      ∀ ω : Rd d, E.exponent ω = D.exponent ω + Q.exponent ω := by
  obtain ⟨ρ, hρ⟩ := D.exists_measure_sub h.2
  -- the reflected difference is a difference too
  have hρn : ρ.map (fun x => -x) + D.ν = E.ν := by
    rw [← D.ν_symm, ← Measure.map_add _ _ measurable_neg, hρ, E.ν_symm]
  set ρs : Measure (Rd d) := (2 : ℝ≥0∞)⁻¹ • (ρ + ρ.map fun x => -x) with hρs
  have hsum : ρs + D.ν = E.ν := by
    have e2 : (2 : ℝ≥0∞)⁻¹ • E.ν + (2 : ℝ≥0∞)⁻¹ • E.ν = E.ν := by
      rw [← add_smul, ENNReal.inv_two_add_inv_two, one_smul]
    have e3 : (2 : ℝ≥0∞)⁻¹ • D.ν + (2 : ℝ≥0∞)⁻¹ • D.ν = D.ν := by
      rw [← add_smul, ENNReal.inv_two_add_inv_two, one_smul]
    have e4 : ρs + D.ν = (2 : ℝ≥0∞)⁻¹ • (ρ + D.ν) +
        (2 : ℝ≥0∞)⁻¹ • (ρ.map (fun x => -x) + D.ν) := by
      conv_lhs => rw [← e3]
      rw [hρs, smul_add, smul_add, smul_add]
      abel
    rw [e4, hρ, hρn, e2]
  have hle : ρs ≤ E.ν := hsum ▸ Measure.le_add_right le_rfl
  have hsymm : ρs.map (fun x => -x) = ρs := by
    rw [hρs, Measure.map_smul, Measure.map_add _ _ measurable_neg,
      Measure.map_map measurable_neg measurable_neg]
    have e : ((fun x : Rd d => -x) ∘ fun x => -x) = id := by funext x; simp
    rw [e, Measure.map_id, add_comm]
  have hPSD : (E.A - D.A).PosSemidef := Matrix.le_iff.1 h.1
  set Q : SymLevyData d := ⟨E.A - D.A, ρs, hPSD,
    le_antisymm ((hle _).trans (le_of_eq E.ν_zero)) bot_le,
    ne_top_of_le_ne_top E.ν_integrable (lintegral_mono' hle le_rfl), hsymm⟩ with hQ
  refine ⟨Q, rfl, hsum, fun ω => ?_⟩
  -- through the triplets
  have hT : E.triplet = D.triplet.add Q.triplet := by
    refine LevyTriplet.ext' ?_ ?_ ?_
    · change (2 : ℝ) • E.A = (2 : ℝ) • D.A + (2 : ℝ) • (E.A - D.A)
      rw [← smul_add, add_sub_cancel]
    · change E.ν = D.ν + ρs
      rw [← hsum, add_comm]
    · change (0 : Rd d) = 0 + 0
      simp
  have h1 := congrArg (fun T : LevyTriplet d => T.lkExponent ω) hT
  simp only [LevyTriplet.lkExponent_add, SymLevyData.lkExponent_triplet] at h1
  have h2 : ((E.exponent ω : ℝ) : ℂ) = ((D.exponent ω + Q.exponent ω : ℝ) : ℂ) := by
    push_cast
    linear_combination -h1
  exact_mod_cast h2

/-! ## The data at every scale -/

/-- **The extended data at `t`**: the dilate `(q^{2n}A_u, D_{qⁿ}ν_u)` of `D u`, `t = qⁿu`,
`u ∈ [1, q)`, and zero at `t ≤ 0`. -/
noncomputable def octaveData (q : ℝ) (D : ℝ → SymLevyData d) (t : ℝ) : SymLevyData d :=
  if h : 0 < t ∧ q ≠ 0 then (D (q ^ (-dgLevel q t) * t)).dilate (zpow_ne_zero (dgLevel q t) h.2)
  else SymLevyData.zero

theorem octaveData_of_nonpos (q : ℝ) (D : ℝ → SymLevyData d) {t : ℝ} (ht : t ≤ 0) :
    octaveData q D t = SymLevyData.zero := by
  rw [octaveData, dif_neg (fun h => absurd h.1 (not_lt.2 ht))]

theorem octaveData_A {q : ℝ} (hq : 1 < q) (D : ℝ → SymLevyData d) (t : ℝ) :
    (octaveData q D t).A = octaveA q D t := by
  have hq0 : q ≠ 0 := by positivity
  rcases le_or_gt t 0 with ht | ht
  · rw [octaveData_of_nonpos q D ht, octaveA, if_pos ht]; rfl
  · rw [octaveData, dif_pos ⟨ht, hq0⟩, octaveA, if_neg (not_le.2 ht)]
    change (q ^ dgLevel q t) ^ 2 • _ = _
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    rfl

theorem octaveData_ν {q : ℝ} (hq : 1 < q) (D : ℝ → SymLevyData d) (t : ℝ) :
    (octaveData q D t).ν = octaveNu q D t := by
  have hq0 : q ≠ 0 := by positivity
  rcases le_or_gt t 0 with ht | ht
  · rw [octaveData_of_nonpos q D ht, octaveNu, if_pos ht]; rfl
  · rw [octaveData, dif_pos ⟨ht, hq0⟩, octaveNu, if_neg (not_le.2 ht)]
    rfl

theorem octaveData_exponent {q : ℝ} (hq : 1 < q) (D : ℝ → SymLevyData d) (t : ℝ) (ω : Rd d) :
    (octaveData q D t).exponent ω = octaveExponent q D t ω := by
  rw [SymLevyData.exponent, octaveExponent, octaveData_A hq, octaveData_ν hq]

/-- **The data on a closed octave**: at `qⁿu`, `u ∈ [1, q]`, the extended data are the dilate of
`D u` by `qⁿ`; at `u = q` by the gluing condition. -/
theorem octaveData_at {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d} (hD : IsSynthesisData q D)
    (n : ℤ) {u : ℝ} (hu : u ∈ Icc 1 q) :
    octaveData q D (q ^ n * u) = (D u).dilate (zpow_ne_zero n (by positivity : q ≠ 0)) := by
  have hq0 : 0 < q := by linarith
  have hqn : 0 < q ^ n := zpow_pos hq0 n
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu.1
  have ht : 0 < q ^ n * u := mul_pos hqn hu0
  rcases hu.2.lt_or_eq with hlt | heq
  · -- `u ∈ [1, q)`: the level is `n`
    have hlev : dgLevel q (q ^ n * u) = n := by
      refine dgLevel_eq hq ?_ ?_
      · exact le_mul_of_one_le_right hqn.le hu.1
      · rw [zpow_add_one₀ hq0.ne']; exact mul_lt_mul_of_pos_left hlt hqn
    refine SymLevyData.ext' ?_ ?_
    · rw [octaveData_A hq, octaveA, if_neg (not_le.2 ht), hlev, zpow_neg,
        inv_mul_cancel_left₀ hqn.ne']
      change _ = (q ^ n) ^ 2 • _
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
      rfl
    · rw [octaveData_ν hq, octaveNu, if_neg (not_le.2 ht), hlev, zpow_neg,
        inv_mul_cancel_left₀ hqn.ne']
      rfl
  · -- `u = q`: the level is `n + 1`, and the gluing condition
    rw [heq] at ht ⊢
    have hlev : dgLevel q (q ^ n * q) = n + 1 := by
      refine dgLevel_eq hq ?_ ?_
      · rw [zpow_add_one₀ hq0.ne']
      · rw [zpow_add_one₀ hq0.ne', zpow_add_one₀ hq0.ne']
        exact lt_mul_of_one_lt_right (mul_pos hqn hq0) hq
    have hτ : q ^ (-(n + 1)) * (q ^ n * q) = 1 := by
      rw [← zpow_add_one₀ hq0.ne', ← zpow_add₀ hq0.ne']; simp
    refine SymLevyData.ext' ?_ ?_
    · rw [octaveData_A hq, octaveA, if_neg (not_le.2 ht), hlev, hτ]
      change _ = (q ^ n) ^ 2 • (D q).A
      rw [hD.glue.1, smul_smul]
      congr 1
      have e : (2 : ℤ) * (n + 1) = 2 * n + 2 := by ring
      rw [e, zpow_add₀ hq0.ne', mul_comm (2 : ℤ) n, zpow_mul]
      simp only [zpow_two, pow_two]
    · rw [octaveData_ν hq, octaveNu, if_neg (not_le.2 ht), hlev, hτ]
      change _ = (D q).ν.map fun x => q ^ n • x
      rw [hD.glue.2, Measure.map_map (continuous_const_smul _).measurable
        (continuous_const_smul _).measurable]
      congr 1
      funext x
      simp only [Function.comp_apply, smul_smul, ← zpow_add_one₀ hq0.ne']

/-- At `qⁿu`, `u ∈ [1, q]`: `Ψ_{qⁿu}(ω) = Ψ_u(qⁿω)`. -/
theorem octaveExponent_at {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d}
    (hD : IsSynthesisData q D) (n : ℤ) {u : ℝ} (hu : u ∈ Icc 1 q) (ω : Rd d) :
    octaveExponent q D (q ^ n * u) ω = (D u).exponent (q ^ n • ω) := by
  rw [← octaveData_exponent hq, octaveData_at hq hD n hu, SymLevyData.dilate_exponent]

/-! ## The order of the extended data -/

/-- Within the closed octave `[qⁿ, q^{n+1}]` the data increase strictly. -/
theorem octaveData_lt_same {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d}
    (hD : IsSynthesisData q D) (n : ℤ) {u v : ℝ} (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ q) :
    (octaveData q D (q ^ n * u)).Le (octaveData q D (q ^ n * v)) ∧
      ((octaveData q D (q ^ n * u)).A, (octaveData q D (q ^ n * u)).ν) ≠
        ((octaveData q D (q ^ n * v)).A, (octaveData q D (q ^ n * v)).ν) := by
  obtain ⟨hA, hν, hne⟩ := hD.increments u v hu huv hv
  rw [octaveData_at hq hD n ⟨hu, huv.le.trans hv⟩, octaveData_at hq hD n ⟨hu.trans huv.le, hv⟩]
  exact ⟨SymLevyData.dilate_le ⟨Matrix.le_iff.2 hA, hν⟩ _, SymLevyData.dilate_ne _ hne⟩

/-- **The extended data increase strictly on `(0,∞)`.** -/
theorem octaveData_lt {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d} (hD : IsSynthesisData q D)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    (octaveData q D s).Le (octaveData q D t) ∧
      ((octaveData q D s).A, (octaveData q D s).ν) ≠
        ((octaveData q D t).A, (octaveData q D t).ν) := by
  have hq0 : 0 < q := by linarith
  set P : ℝ → ℝ → Prop := fun s t => (octaveData q D s).Le (octaveData q D t) ∧
    ((octaveData q D s).A, (octaveData q D s).ν) ≠ ((octaveData q D t).A, (octaveData q D t).ν)
    with hP
  -- the same closed octave
  have same : ∀ (n : ℤ) (s t : ℝ), q ^ n ≤ s → s < t → t ≤ q ^ (n + 1) → P s t := by
    intro n s t h1 h2 h3
    have hqn : 0 < q ^ n := zpow_pos hq0 n
    have es : s = q ^ n * (q ^ (-n) * s) := by
      rw [zpow_neg, mul_inv_cancel_left₀ hqn.ne']
    have et : t = q ^ n * (q ^ (-n) * t) := by
      rw [zpow_neg, mul_inv_cancel_left₀ hqn.ne']
    have hu : 1 ≤ q ^ (-n) * s := by rw [zpow_neg, le_inv_mul_iff₀ hqn, mul_one]; exact h1
    have huv : q ^ (-n) * s < q ^ (-n) * t := mul_lt_mul_of_pos_left h2 (zpow_pos hq0 _)
    have hv : q ^ (-n) * t ≤ q := by
      rw [zpow_neg, inv_mul_le_iff₀ hqn, ← zpow_add_one₀ hq0.ne']; exact h3
    have := octaveData_lt_same hq hD n hu huv hv
    rw [← es, ← et] at this
    exact this
  have trans : ∀ s u t, P s u → P u t → P s t := fun s u t h1 h2 =>
    ⟨h1.1.trans h2.1, h1.1.ne_left h2.1 h1.2⟩
  -- across octaves
  have chain : ∀ (k : ℕ) (n : ℤ) (s t : ℝ), s ∈ Ico (q ^ n) (q ^ (n + 1)) →
      t ∈ Icc (q ^ (n + k)) (q ^ (n + k + 1)) → s < t → P s t := by
    intro k
    induction k with
    | zero =>
      intro n s t hs ht hst
      simp only [Nat.cast_zero, add_zero] at ht
      exact same n s t hs.1 hst ht.2
    | succ k ih =>
      intro n s t hs ht hst
      have h1 : P s (q ^ (n + 1)) := same n s _ hs.1 hs.2 le_rfl
      have hle : q ^ (n + 1) ≤ t := by
        refine le_trans (zpow_le_zpow_right₀ hq.le ?_) ht.1
        push_cast; omega
      rcases hle.lt_or_eq with hlt | heq
      · refine trans _ _ _ h1 (ih (n + 1) _ t ⟨le_rfl, ?_⟩ ?_ hlt)
        · exact zpow_lt_zpow_right₀ hq (by omega)
        · have e1 : n + 1 + (k : ℤ) = n + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [e1]
          exact ht
      · rw [← heq]; exact h1
  obtain ⟨hs1, hs2⟩ := dgLevel_spec hq hs
  have ht0 : 0 < t := hs.trans hst
  obtain ⟨ht1, ht2⟩ := dgLevel_spec hq ht0
  have hnm : dgLevel q s ≤ dgLevel q t := by
    have : q ^ dgLevel q s < q ^ (dgLevel q t + 1) := lt_of_le_of_lt hs1 (hst.trans ht2)
    have := (zpow_lt_zpow_iff_right₀ hq).1 this
    omega
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hnm)
  refine chain k (dgLevel q s) s t ⟨hs1, hs2⟩ ?_ hst
  have e : dgLevel q s + (k : ℤ) = dgLevel q t := by omega
  rw [e]
  exact ⟨ht1, ht2.le⟩

/-- For `0 ≤ s ≤ t` the data increase, and strictly when `s < t`. -/
theorem octaveData_le {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d} (hD : IsSynthesisData q D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (octaveData q D s).Le (octaveData q D t) ∧
      (s < t → ((octaveData q D s).A, (octaveData q D s).ν) ≠
        ((octaveData q D t).A, (octaveData q D t).ν)) := by
  have hq0 : 0 < q := by linarith
  rcases hs.eq_or_lt with h0 | h0
  · subst h0
    rw [octaveData_of_nonpos q D le_rfl]
    refine ⟨SymLevyData.zero_data_le _, fun ht => ?_⟩
    -- `(0, 0) ≠ data at t`, through the data at `t/q`
    have htq : 0 < t / q := div_pos ht hq0
    have htq' : t / q < t := div_lt_self ht hq
    obtain ⟨hle, hne⟩ := octaveData_lt hq hD htq htq'
    exact (SymLevyData.zero_data_le _).ne_right hle hne
  · rcases hst.eq_or_lt with heq | hlt
    · subst heq
      exact ⟨SymLevyData.Le.refl _, fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨hle, hne⟩ := octaveData_lt hq hD h0 hlt
      exact ⟨hle, fun _ => hne⟩

/-! ## The exponent -/

theorem pairExponent_neg (A : Mat d) (ν : Measure (Rd d)) (ω : Rd d) :
    pairExponent A ν (-ω) = pairExponent A ν ω := by
  have hq : quad A (-ω) = quad A ω := by
    have := quad_smul_vec A (-1) ω
    simpa using this
  simp only [pairExponent, hq, inner_neg_left, Real.cos_neg]

theorem octaveExponent_zero_left (q : ℝ) (D : ℝ → SymLevyData d) (ω : Rd d) :
    octaveExponent q D 0 ω = 0 := by
  simp [octaveExponent, octaveA, octaveNu, pairExponent, quad_zero]

theorem octaveExponent_zero_right {q : ℝ} (hq : 1 < q) (D : ℝ → SymLevyData d) (t : ℝ) :
    octaveExponent q D t 0 = 0 := by
  rw [← octaveData_exponent hq]
  simp [SymLevyData.exponent, pairExponent, quad, lin]

/-- **Covariance of the exponent**: `Ψ_{qt}(ω) = Ψ_t(qω)` for `t ≥ 0`. -/
theorem octaveExponent_cov {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d}
    (hD : IsSynthesisData q D) {t : ℝ} (ht : 0 ≤ t) (ω : Rd d) :
    octaveExponent q D (q * t) ω = octaveExponent q D t (q • ω) := by
  have hq0 : 0 < q := by linarith
  rcases ht.eq_or_lt with h0 | h0
  · subst h0
    rw [mul_zero, octaveExponent_zero_left, octaveExponent_zero_left]
  · have key : ∀ (n : ℤ) (u : ℝ), u ∈ Ico 1 q →
        octaveExponent q D (q * (q ^ n * u)) ω = octaveExponent q D (q ^ n * u) (q • ω) := by
      intro n u hu
      rw [show q * (q ^ n * u) = q ^ (n + 1) * u by rw [zpow_add_one₀ hq0.ne']; ring,
        octaveExponent_at hq hD _ ⟨hu.1, hu.2.le⟩, octaveExponent_at hq hD _ ⟨hu.1, hu.2.le⟩,
        smul_smul, zpow_add_one₀ hq0.ne']
    have hqn : 0 < q ^ dgLevel q t := zpow_pos hq0 _
    have et : t = q ^ dgLevel q t * (q ^ (-dgLevel q t) * t) := by
      rw [zpow_neg, mul_inv_cancel_left₀ hqn.ne']
    have h := key (dgLevel q t) _ (octave_mem hq h0)
    rw [← et] at h
    exact h

/-! ## Laws with the exponent -/

/-- **The laws exist** (ledger A39(iii)): for `0 ≤ s ≤ t`, a probability measure with transform
`e^{-(Ψ_t - Ψ_s)}`, which is the law of the difference of the data. -/
theorem exists_law {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d} (hD : IsSynthesisData q D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃ Q : SymLevyData d, (∀ ω, octaveExponent q D t ω = octaveExponent q D s ω + Q.exponent ω) ∧
      (s < t → (Q.A, Q.ν) ≠ (0, 0)) ∧
      ∃ m : Measure (Rd d), IsProbabilityMeasure m ∧ IsSymData m Q := by
  obtain ⟨hle, hne⟩ := octaveData_le hq hD hs hst
  obtain ⟨Q, hQA, hQν, hQ⟩ := SymLevyData.exists_sub hle
  refine ⟨Q, fun ω => by rw [← octaveData_exponent hq, ← octaveData_exponent hq, hQ ω],
    fun hlt h0 => hne hlt ?_, ?_⟩
  · obtain ⟨hA, hν⟩ := Prod.mk.inj h0
    refine Prod.ext ?_ ?_
    · rw [hA] at hQA; exact (sub_eq_zero.1 hQA.symm).symm
    · rw [hν, zero_add] at hQν; exact hQν
  · obtain ⟨m, hprob, -, hT⟩ := cited_A39_converse Q.triplet
    refine ⟨m, hprob, fun ω => ?_⟩
    rw [hT ω, SymLevyData.lkExponent_triplet, Complex.ofReal_exp, Complex.ofReal_neg]

/-! ## `lem:synthesis` -/

/-- **`lem:synthesis`.** Under the hypotheses on one octave, the extended data are symmetric Lévy
data at every `t > 0`, laws with transform `e^{-(Ψ_t - Ψ_s)}` exist, and any such laws form a
symmetric `q`-covariant family in dimension `d` with `S_q t = qt`. -/
theorem synthesis {q : ℝ} (hq : 1 < q) (D : ℝ → SymLevyData d)
    (hD : IsSynthesisData q D) :
    (∀ t : ℝ, 0 < t → ∃ E : SymLevyData d, E.A = octaveA q D t ∧ E.ν = octaveNu q D t) ∧
      (∃ μ : ℝ → ℝ → Measure (Rd d), IsExponentLaws (octaveExponent q D) μ) ∧
      ∀ μ : ℝ → ℝ → Measure (Rd d), IsExponentLaws (octaveExponent q D) μ →
        IsSymmetricFamily μ ∧ IsCovariantAt μ q (fun t => q * t) := by
  have hq0 : 0 < q := by linarith
  set Ψ := octaveExponent q D with hΨ
  refine ⟨fun t _ => ⟨octaveData q D t, octaveData_A hq D t, octaveData_ν hq D t⟩, ?_, ?_⟩
  · -- the laws exist
    have h : ∀ s t : ℝ, ∃ m : Measure (Rd d), 0 ≤ s → s ≤ t → IsProbabilityMeasure m ∧
        ∀ ω : Rd d, charFun m ω = ((Real.exp (-(Ψ t ω - Ψ s ω)) : ℝ) : ℂ) := by
      intro s t
      by_cases hst : 0 ≤ s ∧ s ≤ t
      · obtain ⟨Q, hQ, -, m, hm, hmQ⟩ := exists_law hq hD hst.1 hst.2
        refine ⟨m, fun _ _ => ⟨hm, fun ω => ?_⟩⟩
        simp only [hΨ]
        rw [hmQ ω, hQ ω]
        congr 3
        ring
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hst⟩
    choose μ hμ using h
    exact ⟨μ, hμ⟩
  intro μ hμ
  -- the increments are nonnegative
  have hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ω, Ψ s ω ≤ Ψ t ω := by
    intro s t hs hst ω
    obtain ⟨hp, hc⟩ := hμ s t hs hst
    have h1 := norm_charFun_le_one (μ := μ s t) ω
    rw [hc ω, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
    have := Real.exp_le_one_iff.1 h1
    linarith
  have hΨ0 : ∀ ω, Ψ 0 ω = 0 := octaveExponent_zero_left q D
  -- the continuity of `t ↦ Ψ_t(ω)` on `[0,∞)`
  have hcont : ∀ ω : Rd d, ContinuousOn (fun t => Ψ t ω) (Ici 0) := by
    intro ω
    -- on each closed octave
    have hoct : ∀ n : ℤ, ContinuousOn (fun t => Ψ t ω) (Icc (q ^ n) (q ^ (n + 1))) := by
      intro n
      have hqn : 0 < q ^ n := zpow_pos hq0 n
      have hmaps : MapsTo (fun t => q ^ (-n) * t) (Icc (q ^ n) (q ^ (n + 1))) (Icc 1 q) := by
        intro t ht
        refine ⟨?_, ?_⟩
        · rw [zpow_neg, le_inv_mul_iff₀ hqn, mul_one]; exact ht.1
        · rw [zpow_neg, inv_mul_le_iff₀ hqn, ← zpow_add_one₀ hq0.ne']; exact ht.2
      have hc : ContinuousOn (fun t => (D (q ^ (-n) * t)).exponent (q ^ n • ω))
          (Icc (q ^ n) (q ^ (n + 1))) :=
        (hD.continuous (q ^ n • ω)).comp (continuous_const.mul continuous_id).continuousOn hmaps
      refine hc.congr fun t ht => ?_
      have et : t = q ^ n * (q ^ (-n) * t) := by
        rw [zpow_neg, mul_inv_cancel_left₀ hqn.ne']
      change Ψ t ω = _
      conv_lhs => rw [et]
      exact octaveExponent_at hq hD n (hmaps ht) ω
    intro t ht
    rcases (mem_Ici.1 ht).eq_or_lt with h0 | h0
    · -- at `0`
      subst h0
      have hc1 : ContinuousAt (fun c : ℝ => (D 1).exponent (c • ω)) 0 := by
        -- `Ψ_1(ω') = -log μ̂_{0,1}(ω')`, continuous
        have hk : ∀ ω' : Rd d, (D 1).exponent ω' = -Real.log (charFun (μ 0 1) ω').re := by
          intro ω'
          have h1 := (hμ 0 1 le_rfl zero_le_one).2 ω'
          rw [h1, Complex.ofReal_re, Real.log_exp, hΨ0, sub_zero, neg_neg]
          have := octaveExponent_at hq hD 0 (u := 1) ⟨le_rfl, hq.le⟩ ω'
          simp only [zpow_zero, mul_one, one_smul] at this
          exact this.symm
        simp_rw [hk]
        haveI := (hμ 0 1 le_rfl zero_le_one).1
        refine ContinuousAt.neg (ContinuousAt.log ?_ ?_)
        · exact (Complex.continuous_re.comp (continuous_charFun.comp
            (continuous_id.smul continuous_const))).continuousAt
        · simp [charFun_zero]
      have hlim : Tendsto (fun c : ℝ => (D 1).exponent (c • ω)) (𝓝 0) (𝓝 0) := by
        have h := hc1.tendsto
        have h0 : (D 1).exponent ((0 : ℝ) • ω) = 0 := by
          rw [zero_smul]
          have := octaveExponent_at hq hD 0 (u := 1) ⟨le_rfl, hq.le⟩ 0
          simp only [zpow_zero, mul_one, one_smul] at this
          rw [← this, octaveExponent_zero_right hq]
        rwa [h0] at h
      have hpow : Tendsto (fun m : ℕ => q ^ (-(m : ℤ))) atTop (𝓝 0) := by
        have := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hq0.le)
          (inv_lt_one_of_one_lt₀ hq)
        refine this.congr fun m => ?_
        rw [zpow_neg, zpow_natCast, inv_pow]
      have hseq := hlim.comp hpow
      rw [ContinuousWithinAt, hΨ0, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.1 hseq) ε hε |>.imp fun m h => h m le_rfl
      refine ⟨q ^ (-(m : ℤ)), zpow_pos hq0 _, fun t ht htd => ?_⟩
      have ht0 : 0 ≤ t := ht
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0] at htd
      have hup : Ψ t ω ≤ Ψ (q ^ (-(m : ℤ))) ω := hmono t _ ht0 htd.le ω
      have hlow : 0 ≤ Ψ t ω := hΨ0 ω ▸ hmono 0 t le_rfl ht0 ω
      have hval : Ψ (q ^ (-(m : ℤ))) ω = (D 1).exponent (q ^ (-(m : ℤ)) • ω) := by
        have := octaveExponent_at hq hD (-(m : ℤ)) (u := 1) ⟨le_rfl, hq.le⟩ ω
        rwa [mul_one] at this
      rw [Real.dist_eq, sub_zero] at hm ⊢
      simp only [Function.comp_apply] at hm
      rw [abs_of_nonneg hlow]
      rw [← hval] at hm
      exact lt_of_le_of_lt hup (lt_of_le_of_lt (le_abs_self _) hm)
    · -- at `t > 0`: the two closed octaves about `t`
      obtain ⟨h1, h2⟩ := dgLevel_spec hq h0
      set n := dgLevel q t
      have hU : ContinuousOn (fun t => Ψ t ω) (Icc (q ^ (n - 1)) (q ^ (n + 1))) := by
        have e : Icc (q ^ (n - 1)) (q ^ (n + 1)) =
            Icc (q ^ (n - 1)) (q ^ (n - 1 + 1)) ∪ Icc (q ^ n) (q ^ (n + 1)) := by
          rw [sub_add_cancel, Icc_union_Icc_eq_Icc]
          · exact zpow_le_zpow_right₀ hq.le (by omega)
          · exact zpow_le_zpow_right₀ hq.le (by omega)
        rw [e]
        exact (hoct (n - 1)).union_of_isClosed (hoct n) isClosed_Icc isClosed_Icc
      have hlt : q ^ (n - 1) < t := lt_of_lt_of_le (zpow_lt_zpow_right₀ hq (by omega)) h1
      exact (hU.continuousAt (Icc_mem_nhds hlt h2)).continuousWithinAt
  -- the family
  have hprob : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsProbabilityMeasure (μ s t) := fun s t hs hst =>
    (hμ s t hs hst).1
  have hch := fun s t hs hst => (hμ s t hs hst).2
  have hhemi : IsLawHemigroup μ := by
    refine ⟨hprob, fun t ht => ?_, fun r s t hr hrs hst => ?_, fun ω => ?_⟩
    · haveI := hprob t t ht le_rfl
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      rw [hch t t ht le_rfl ω, charFun_dirac]
      simp
    · haveI := hprob r t hr (hrs.trans hst)
      haveI := hprob s t (hr.trans hrs) hst
      haveI := hprob r s hr hrs
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      rw [charFun_conv, hch r t hr (hrs.trans hst) ω, hch s t (hr.trans hrs) hst ω,
        hch r s hr hrs ω, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3
      ring
    · refine ContinuousOn.congr (f := fun p : ℝ × ℝ =>
        ((Real.exp (-(Ψ p.2 ω - Ψ p.1 ω)) : ℝ) : ℂ)) ?_ fun p hp => hch p.1 p.2 hp.1 hp.2 ω
      have h2 : ContinuousOn (fun p : ℝ × ℝ => Ψ p.2 ω) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
        (hcont ω).comp continuous_snd.continuousOn fun p hp => mem_Ici.2 (hp.1.trans hp.2)
      have h1 : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
        (hcont ω).comp continuous_fst.continuousOn fun p hp => mem_Ici.2 hp.1
      exact Complex.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn ((h2.sub h1).neg))
  refine ⟨⟨hhemi, fun s t hs hst hdir => ?_, fun s t hs hst => ?_⟩, ?_⟩
  · -- (ND): the uniqueness of data (A39(ii))
    obtain ⟨Q, hQ, hQne, -⟩ := exists_law hq hD hs hst.le
    haveI := hprob s t hs hst.le
    have hzero : ∀ ω, Q.exponent ω = 0 := by
      intro ω
      have h1 := hch s t hs hst.le ω
      rw [hdir, charFun_dirac] at h1
      simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h1
      have h2 : Real.exp (-(Ψ t ω - Ψ s ω)) = 1 := by exact_mod_cast h1.symm
      rw [Real.exp_eq_one_iff] at h2
      have := hQ ω
      linarith
    have hQd : IsSymData (Measure.dirac (0 : Rd d)) Q := fun ω => by
      rw [hzero ω, charFun_dirac]; simp
    have hZd : IsSymData (Measure.dirac (0 : Rd d)) SymLevyData.zero := fun ω => by
      rw [SymLevyData.zero_exponent, charFun_dirac]; simp
    obtain ⟨hA, hν⟩ := isSymData_unique hQd hZd
    exact hQne hst (Prod.ext (by simpa [SymLevyData.zero] using hA)
      (by simpa [SymLevyData.zero] using hν))
  · -- symmetry: the exponent is even
    haveI := hprob s t hs hst
    haveI : IsProbabilityMeasure ((μ s t).map fun x => -x) :=
      Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    have e : (fun x : Rd d => -x) = fun x => (-1 : ℝ) • x := by funext x; simp
    rw [e, charFun_map_smul, hch s t hs hst, hch s t hs hst, neg_one_smul]
    simp only [hΨ, octaveExponent, pairExponent_neg]
  · -- covariance with `S_q t = qt`
    refine ⟨⟨fun t ht => mul_nonneg hq0.le ht, fun u _ v _ huv => mul_lt_mul_of_pos_left huv hq0,
      fun t ht => ⟨t / q, div_nonneg ht hq0.le, mul_div_cancel₀ t hq0.ne'⟩⟩, fun s t hs hst => ?_⟩
    have hqs : 0 ≤ q * s := by positivity
    have hqst : q * s ≤ q * t := mul_le_mul_of_nonneg_left hst hq0.le
    haveI := hprob s t hs hst
    haveI := hprob (q * s) (q * t) hqs hqst
    haveI : IsProbabilityMeasure ((μ s t).map fun x => q • x) :=
      Measure.isProbabilityMeasure_map (continuous_const_smul q).measurable.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_map_smul, hch s t hs hst, hch (q * s) (q * t) hqs hqst]
    simp only [hΨ]
    rw [octaveExponent_cov hq hD (hs.trans hst), octaveExponent_cov hq hD hs]

end Pyramids
