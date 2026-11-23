/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.PhaseEntropy
import Pyramids.LineAppendix.KLMixture
import Pyramids.Line.GridPyramids
import Pyramids.Pyramid.Synthesis

/-!
# `prop:phase-entropy-ladder-bound`: the ladder bound, and the obstruction

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:phase-entropy-ladder-bound`. Wave 3f: the
three declarations `ladder_bound_1`, `_2`, `_3` moved here from `PyramidsSkeleton.ChA1Line`,
unchanged in name and conclusion. Dropped hypotheses the proofs do not read (2026-11-15, a
strengthening): `ladder_bound_1` no longer takes `IsKnotExponent q Ψ1` or `m univ ≠ 0` (when
`|μ| = 0` the marginal `ρ̃` is zero and every clause is trivial), and its identity no longer takes
`phaseEntropy … ≠ ⊥` (also dropped in print); `ladder_bound_2` no longer takes
`IsKnotExponent q Ψ1`.

## The route

* **The step through the cylinder** (`slab_one_q_eq_cylMeasure`): `μ(A) = Λ((1,q] × A)`
  (`lem:knot-exponent-ladder`(3)) is `σ({(θ, r) : rθ ∈ A})`, because `Λ` has no mass on the lines
  `{1} × (0,∞)` and `{q} × (0,∞)` (`thm:surface-measure`(iii)), is carried by the quadrant, and
  `v = (v/y)·y` on the slab. With the disintegration, `μ(A) = ∫ π_r({θ : rθ ∈ A}) ρ̃(dr)`.
* **(2)**: `𝔈 > -∞` makes `KL(π_r ‖ η)` finite, so `π_r ≪ η ≪ Lebesgue`, for `ρ̃`-almost every
  `r > 0`; a Lebesgue-null `N` has the null preimage `r⁻¹N`.
* **(3)**: a family carrying the grid ladder is a member of the modulation orbit of its own
  knot exponent `Ψ_1 = -log μ̂_{0,1}`, with step `μ_{1,q} = w`; the step measure is `ϖ_w`
  (`prop:grid-pyramids-infinitely-divisible`(1)), nonzero and carried by the countable `hℤ_{>0}`,
  so it is not absolutely continuous, and (2) applies.
* **(1)**: `|ρ̃| = |μ|` and `μ° = ∫ P_r ρ̃(dr)` are the step formula at `A = (0,∞)` and at
  `A = [·]⁻¹E`. The rotation `rot_r` agrees on `[1,q)` with a measurable bijection of `ℝ` that
  fixes `η`, so `KL(π_r ‖ η) = KL(P_r ‖ η)` (`klDiv_rotatedFibre`). The identity is
  `lintegral_klDiv_eq_add` at `ρ̄ = ρ̃/|μ|`, which holds in `[0,∞]` with no finiteness hypothesis;
  the bound (A.e6) and the equality case follow from it (Gibbs, `klDiv_eq_zero_iff`).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter ProbabilityTheory InformationTheory
open ScaleSpace (X)
open scoped ENNReal

/-! ## The rotation as a measurable bijection -/

/-- `[y] = θ` when `y = qⁿθ` with `θ ∈ [1,q)`. -/
theorem qClass_eq_of_mem {q : ℝ} (hq : 1 < q) {θ : ℝ} (hθ : θ ∈ Ico 1 q) (n : ℤ) :
    qClass q (q ^ n * θ) = θ := by
  have hq0 : 0 < q := by linarith
  have hn : dgLevel q (q ^ n * θ) = n := by
    refine dgLevel_eq hq ?_ ?_
    · exact le_mul_of_one_le_right (zpow_pos hq0 n).le hθ.1
    · rw [zpow_add_one₀ hq0.ne']
      exact mul_lt_mul_of_pos_left hθ.2 (zpow_pos hq0 n)
  rw [qClass, hn, ← mul_assoc, ← zpow_add₀ hq0.ne', neg_add_cancel, zpow_zero, one_mul]

/-- `rot_r` maps `[1,q)` into itself, for `r > 0`. -/
theorem qRot_mem {q : ℝ} (hq : 1 < q) {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ico 1 q) :
    qRot q r θ ∈ Ico 1 q :=
  octave_mem hq (mul_pos hr (lt_of_lt_of_le one_pos hθ.1))

/-- `rot_{1/r} ∘ rot_r = id` on `[1,q)`, for `r > 0`. -/
theorem qRot_inv_qRot {q : ℝ} (hq : 1 < q) {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ico 1 q) :
    qRot q r⁻¹ (qRot q r θ) = θ := by
  have e : r⁻¹ * qRot q r θ = q ^ (-dgLevel q (r * θ)) * θ := by
    rw [qRot, qClass]
    field_simp
  rw [qRot, e, qClass_eq_of_mem hq hθ]

open Classical in
/-- **The rotation `rot_r` on `[1,q)`, extended by the identity**, a measurable bijection of `ℝ`. -/
noncomputable def rotEquiv {q : ℝ} (hq : 1 < q) {r : ℝ} (hr : 0 < r) : ℝ ≃ᵐ ℝ where
  toFun := (Ico 1 q).piecewise (qRot q r) id
  invFun := (Ico 1 q).piecewise (qRot q r⁻¹) id
  left_inv θ := by
    by_cases hθ : θ ∈ Ico 1 q
    · rw [piecewise_eq_of_mem _ _ _ hθ, piecewise_eq_of_mem _ _ _ (qRot_mem hq hr hθ),
        qRot_inv_qRot hq hr hθ]
    · rw [piecewise_eq_of_notMem _ _ _ hθ, id, piecewise_eq_of_notMem _ _ _ hθ, id]
  right_inv θ := by
    have hr' : 0 < r⁻¹ := inv_pos.2 hr
    by_cases hθ : θ ∈ Ico 1 q
    · rw [piecewise_eq_of_mem _ _ _ hθ, piecewise_eq_of_mem _ _ _ (qRot_mem hq hr' hθ)]
      have h := qRot_inv_qRot hq hr' hθ
      rwa [inv_inv] at h
    · rw [piecewise_eq_of_notMem _ _ _ hθ, id, piecewise_eq_of_notMem _ _ _ hθ, id]
  measurable_toFun := (measurable_qRot q r).piecewise measurableSet_Ico measurable_id
  measurable_invFun := (measurable_qRot q r⁻¹).piecewise measurableSet_Ico measurable_id

/-- `rot_r` and the bijection agree almost everywhere for a measure carried by `[1,q)`. -/
theorem map_qRot_eq_map_rotEquiv {q : ℝ} (hq : 1 < q) {r : ℝ} (hr : 0 < r) {ν : Measure ℝ}
    (hν : ν (Ico 1 q)ᶜ = 0) : ν.map (qRot q r) = ν.map (rotEquiv hq hr) := by
  classical
  refine Measure.map_congr ?_
  have hae : ∀ᵐ θ ∂ν, θ ∈ Ico 1 q := by
    rw [ae_iff]
    exact hν
  filter_upwards [hae] with θ hθ
  change qRot q r θ = (Ico 1 q).piecewise (qRot q r) id θ
  rw [piecewise_eq_of_mem _ _ _ hθ]

/-- **Rotating a measure on the circle does not change its entropy against Haar**:
`KL((rot_r)_* ν ‖ η) = KL(ν ‖ η)` for `ν` carried by `[1,q)` and `r > 0`. -/
theorem klDiv_rotatedFibre {q : ℝ} (hq : 1 < q) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Ico 1 q)ᶜ = 0) {r : ℝ} (hr : 0 < r) :
    klDiv (ν.map (qRot q r)) (haarPhase q) = klDiv ν (haarPhase q) := by
  haveI := isProbabilityMeasure_haarPhase hq
  have hη : (haarPhase q).map (rotEquiv hq hr) = haarPhase q := by
    rw [← map_qRot_eq_map_rotEquiv hq hr (haarPhase_compl_Ico q), map_qRot_haarPhase hq hr]
  rw [map_qRot_eq_map_rotEquiv hq hr hν]
  conv_lhs => rw [← hη]
  exact klDiv_map_measurableEquiv _ ν _

/-- The rotated fibres form a measurable family. -/
theorem measurable_rotatedFibre {q : ℝ} {π : ℝ → Measure ℝ} (hπm : Measurable π)
    (hπp : ∀ r : ℝ, IsProbabilityMeasure (π r)) : Measurable (rotatedFibre q π) := by
  let K : Kernel ℝ ℝ := ⟨π, hπm⟩
  haveI : IsMarkovKernel K := ⟨hπp⟩
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hS : MeasurableSet {p : ℝ × ℝ | qRot q p.1 p.2 ∈ s} :=
    hs.preimage ((measurable_qClass q).comp (measurable_fst.mul measurable_snd))
  convert Kernel.measurable_kernel_prodMk_left (κ := K) hS using 1
  funext r
  rw [rotatedFibre, Measure.map_apply (measurable_qRot q r) hs]
  rfl

theorem isProbabilityMeasure_rotatedFibre {q : ℝ} {π : ℝ → Measure ℝ}
    (hπp : ∀ r : ℝ, IsProbabilityMeasure (π r)) (r : ℝ) :
    IsProbabilityMeasure (rotatedFibre q π r) := by
  haveI := hπp r
  exact Measure.isProbabilityMeasure_map (measurable_qRot q r).aemeasurable

/-! ## The step measure through the cylinder -/

theorem measurableSet_mul_mem {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet {p : ℝ × ℝ | p.2 * p.1 ∈ A} :=
  hA.preimage (measurable_snd.mul measurable_fst)

/-- **`Λ((1,q] × A) = σ({(θ, r) : rθ ∈ A})`** for a pair with (i)–(iv). -/
theorem slab_one_q_eq_cylMeasure {q : ℝ} (hq : 1 < q) {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}
    (h : IsSurfacePair q Λ B) {A : Set ℝ} (hA : MeasurableSet A) :
    slab Λ 1 q A = cylMeasure q Λ {p | p.2 * p.1 ∈ A} := by
  rw [slab_apply Λ 1 q hA, cylMeasure_apply q Λ (measurableSet_mul_mem hA)]
  have hset : cylMap ⁻¹' {p : ℝ × ℝ | p.2 * p.1 ∈ A} ∩ cylinder q = Ico 1 q ×ˢ (A ∩ Ioi 0) := by
    ext ⟨y, v⟩
    simp only [cylMap, cylinder, mem_inter_iff, mem_preimage, mem_setOf_eq, mem_prod, mem_Ioi]
    constructor
    · rintro ⟨h1, hy, hv⟩
      have hy0 : y ≠ 0 := (lt_of_lt_of_le one_pos hy.1).ne'
      rw [div_mul_cancel₀ v hy0] at h1
      exact ⟨hy, h1, hv⟩
    · rintro ⟨hy, h1, hv⟩
      have hy0 : y ≠ 0 := (lt_of_lt_of_le one_pos hy.1).ne'
      rw [div_mul_cancel₀ v hy0]
      exact ⟨h1, hy, hv⟩
  rw [hset]
  have hline : ∀ y : ℝ, 0 < y → Λ ({y} ×ˢ univ) = 0 := by
    intro y hy
    refine measure_mono_null (t := {y} ×ˢ Ioi 0 ∪ quadrantᶜ) ?_
      (measure_union_null (h.no_line y hy).1 h.carried)
    rintro ⟨a, b⟩ ⟨ha, -⟩
    by_cases hb : 0 < b
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr fun hq' => hb hq'.2
  have hneg : Λ (univ ×ˢ Iic 0) = 0 := by
    refine measure_mono_null ?_ h.carried
    rintro ⟨a, b⟩ ⟨-, hb⟩ hq'
    exact not_lt.2 (mem_Iic.1 hb) hq'.2
  refine measure_congr (ae_eq_set.2 ⟨?_, ?_⟩)
  · refine measure_mono_null ?_ (measure_union_null (hline q (by linarith)) hneg)
    rintro ⟨y, v⟩ ⟨⟨hy, hv⟩, hn⟩
    simp only [mem_prod, mem_Ico, mem_inter_iff, mem_Ioi, not_and_or, not_le, not_lt] at hy hn
    simp only [mem_union, mem_prod, mem_singleton_iff, mem_univ, and_true, mem_Iic, true_and]
    rcases hn with (hn | hn) | hn | hn
    · exact absurd hn (not_lt.2 hy.1.le)
    · exact Or.inl (le_antisymm hy.2 hn)
    · exact absurd hv hn
    · exact Or.inr hn
  · refine measure_mono_null ?_ (hline 1 one_pos)
    rintro ⟨y, v⟩ ⟨⟨hy, hv, -⟩, hn⟩
    simp only [mem_prod, mem_Ioc, not_and_or, not_lt] at hy hn
    simp only [mem_prod, mem_singleton_iff, mem_univ, and_true]
    rcases hn with (hn | hn) | hn
    · exact le_antisymm hn hy.1
    · exact absurd hy.2.le hn
    · exact absurd hv hn

/-- **The step formula**: `Λ((1,q] × A) = ∫ π_r({θ : rθ ∈ A}) ρ̃(dr)`. -/
theorem slab_eq_lintegral {q : ℝ} (hq : 1 < q) {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}
    (h : IsSurfacePair q Λ B) {π : ℝ → Measure ℝ}
    (hπ : IsPhaseDisintegration q (cylMeasure q Λ) π) {A : Set ℝ} (hA : MeasurableSet A) :
    slab Λ 1 q A =
      ∫⁻ r, π r ((fun θ => r * θ) ⁻¹' A) ∂(rMarginal q (cylMeasure q Λ)) := by
  rw [slab_one_q_eq_cylMeasure hq h hA, hπ.disintegrates _ (measurableSet_mul_mem hA)]
  rfl

/-- `η ≪ Lebesgue`. -/
theorem haarPhase_ac_volume (q : ℝ) : haarPhase q ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem lintegral_ne_top_of_phaseEntropy_ne_bot {q : ℝ} {σ : Measure (ℝ × ℝ)}
    {π : ℝ → Measure ℝ} (hE : phaseEntropy q σ π ≠ ⊥) :
    ∫⁻ r, klDiv (π r) (haarPhase q) ∂(rMarginal q σ) ≠ ⊤ := by
  intro htop
  apply hE
  rw [phaseEntropy, htop, EReal.coe_ennreal_top, EReal.neg_top]

/-! ## (2) -/

/-- **`prop:phase-entropy-ladder-bound`(2).** If `𝔈 > -∞` at a member, `μ` is absolutely
continuous; so if `μ` has a nonzero singular part, `𝔈 = -∞` at every member. The hypothesis
`IsKnotExponent q Ψ1` of the skeleton is not used and was dropped on 2026-11-15, a
strengthening. -/
theorem ladder_bound_2 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ)
    (m : Measure ℝ) (hm : IsStepMeasure q Ψ1 m) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : μ ∈ modulationOrbit q Ψ1) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (hΛ : IsFamilyPair q μ Λ B) (π : ℝ → Measure ℝ)
    (hπ : IsPhaseDisintegration q (cylMeasure q Λ) π) :
    (phaseEntropy q (cylMeasure q Λ) π ≠ ⊥ → m ≪ volume) ∧
      (m.singularPart volume ≠ 0 → phaseEntropy q (cylMeasure q Λ) π = ⊥) := by
  have hm' := knot_exponent_ladder_3 hq Ψ1 m hm μ hμ Λ B hΛ
  have hσ := (cylMeasure_spec hq hΛ.1.carried hΛ.1.invariant).1
  haveI := isProbabilityMeasure_haarPhase hq
  have h1 : phaseEntropy q (cylMeasure q Λ) π ≠ ⊥ → m ≪ volume := by
    intro hE
    have hae : ∀ᵐ r ∂(rMarginal q (cylMeasure q Λ)), klDiv (π r) (haarPhase q) < ⊤ :=
      ae_lt_top (measurable_klDiv_kernel hπ.measurable hπ.isProbability _)
        (lintegral_ne_top_of_phaseEntropy_ne_bot hE)
    intro N hN
    obtain ⟨T, hNT, hT, hT0⟩ := exists_measurable_superset_of_null hN
    refine measure_mono_null hNT ?_
    rw [← hm', slab_eq_lintegral hq hΛ.1 hπ hT]
    refine le_antisymm ?_ bot_le
    calc ∫⁻ r, π r ((fun θ => r * θ) ⁻¹' T) ∂(rMarginal q (cylMeasure q Λ))
        ≤ ∫⁻ _, 0 ∂(rMarginal q (cylMeasure q Λ)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae, ae_rMarginal_pos hσ] with r hr hr0
          haveI := hπ.isProbability r
          have hac : π r ≪ haarPhase q := (klDiv_ne_top_iff.1 hr.ne).1
          have hv : volume ((fun θ => r * θ) ⁻¹' T) = 0 := by
            rw [Real.volume_preimage_mul_left hr0.ne', hT0, mul_zero]
          exact (hac.trans (haarPhase_ac_volume q) hv).le
      _ = 0 := lintegral_zero
  refine ⟨h1, fun hs => ?_⟩
  by_contra hE
  exact hs (Measure.singularPart_eq_zero_of_ac (h1 hE))

/-! ## (3) -/

/-- **`prop:phase-entropy-ladder-bound`(3).** For a mask `w ≠ δ₀` on `hℤ` and every family
carrying the ladder of its grid pyramid, `𝔈 = -∞`. -/
theorem ladder_bound_3 {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : Measure ℝ) (hw : IsGridMask h w)
    (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ) (μ : ℝ → ℝ → Measure ℝ)
    (hcarry : CarriesGridLadder q w Φ S μ) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (hΛ : IsFamilyPair q μ Λ B) (π : ℝ → Measure ℝ)
    (hπ : IsPhaseDisintegration q (cylMeasure q Λ) π) :
    phaseEntropy q (cylMeasure q Λ) π = ⊥ := by
  obtain ⟨hsym, hcov, hstep⟩ := hcarry.family
  have hQ : IsQFamily q μ := ⟨hsym, hcov⟩
  have hid : IsInfinitelyDivisible w := by
    rw [← hstep]
    exact isLawHemigroup_line_infinitelyDivisible hsym.1 zero_le_one hq.le
  obtain ⟨ϖ, hϖ, hϖ0, hϖc⟩ := exists_maskLevyMeasure hh hw hid
  have hμ : μ ∈ modulationOrbit q (lineExponent μ 1) :=
    ⟨hQ, fun ω => charFun_kernel_eq_exp hsym zero_le_one ω⟩
  have hm : IsStepMeasure q (lineExponent μ 1) ϖ := by
    refine ⟨maskPair ϖ hϖ.1 hϖ.2.1, fun ω => ?_, rfl⟩
    have he := eq_of_charFun_exp (m := w) (f := knotStep q (lineExponent μ 1))
      (g := (maskPair ϖ hϖ.1 hϖ.2.1).exponent) (fun ω' => ?_) hϖ.isFoldedData
    · exact congrFun he ω
    · rw [← hstep, charFun_octaveStep hq hsym, lineExponent_q_sub_one hQ]
  by_contra hE
  have hac := (ladder_bound_2 hq _ ϖ hm μ hμ Λ B hΛ π hπ).1 hE
  set C : Set ℝ := {v : ℝ | ∃ n : ℤ, 0 < n ∧ v = h * n} with hCdef
  have hC : C.Countable :=
    (countable_range fun n : ℤ => h * n).mono fun v hv => by
      obtain ⟨n, -, hn⟩ := hv
      exact ⟨n, hn.symm⟩
  have hC0 : ϖ C = 0 := hac (hC.measure_zero volume)
  apply hϖ0
  refine Measure.measure_univ_eq_zero.1 (measure_mono_null (t := C ∪ Cᶜ) ?_
    (measure_union_null hC0 hϖc))
  intro v _
  by_cases hv : v ∈ C
  · exact Or.inl hv
  · exact Or.inr hv

/-! ## (1) -/

/-- **`prop:phase-entropy-ladder-bound`(1).** For `|μ| < ∞`: `|ρ̃| = |μ|`,
`μ° = ∫ P_r ρ̃(dr)`, the bound (A.e6) `𝔈 ≤ -|μ| KL(μ̄° ‖ η)`; where `𝔈 > -∞`,
`-𝔈 = |μ| KL(μ̄° ‖ η) + ∫ KL(P_r ‖ μ̄°) ρ̃(dr)`; and where the bound is finite, equality holds in
it iff `P_r = μ̄°` for `ρ̃`-almost every `r`. The hypotheses `IsKnotExponent q Ψ1` and
`m univ ≠ 0` of the skeleton are not used and were dropped on 2026-11-15, a strengthening; the
identity holds in `[0,∞]` whether or not `𝔈 > -∞`. -/
theorem ladder_bound_1 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ)
    (m : Measure ℝ) (hm : IsStepMeasure q Ψ1 m) (hmfin : m univ ≠ ⊤)
    (μ : ℝ → ℝ → Measure ℝ) (hμ : μ ∈ modulationOrbit q Ψ1) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (hΛ : IsFamilyPair q μ Λ B) (π : ℝ → Measure ℝ)
    (hπ : IsPhaseDisintegration q (cylMeasure q Λ) π) :
    rMarginal q (cylMeasure q Λ) univ = m univ ∧
      (∀ E : Set ℝ, MeasurableSet E →
        foldMeasure q m E = ∫⁻ r, rotatedFibre q π r E ∂(rMarginal q (cylMeasure q Λ))) ∧
      phaseEntropy q (cylMeasure q Λ) π ≤
        -(((m univ * InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q)) : ℝ≥0∞) : EReal) ∧
      ∫⁻ r, InformationTheory.klDiv (π r) (haarPhase q) ∂(rMarginal q (cylMeasure q Λ)) =
          m univ * InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q) +
            ∫⁻ r, InformationTheory.klDiv (rotatedFibre q π r) (foldedStepNorm q m)
              ∂(rMarginal q (cylMeasure q Λ)) ∧
      (InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q) ≠ ⊤ →
        (phaseEntropy q (cylMeasure q Λ) π =
            -(((m univ * InformationTheory.klDiv (foldedStepNorm q m) (haarPhase q)) : ℝ≥0∞) :
              EReal) ↔
          ∀ᵐ r ∂(rMarginal q (cylMeasure q Λ)), rotatedFibre q π r = foldedStepNorm q m)) := by
  set ρ := rMarginal q (cylMeasure q Λ) with hρdef
  have hm' := knot_exponent_ladder_3 hq Ψ1 m hm μ hμ Λ B hΛ
  have hσ := (cylMeasure_spec hq hΛ.1.carried hΛ.1.invariant).1
  haveI := isProbabilityMeasure_haarPhase hq
  have hA : ∀ A : Set ℝ, MeasurableSet A → m A = ∫⁻ r, π r ((fun θ => r * θ) ⁻¹' A) ∂ρ :=
    fun A hA => by rw [← hm']; exact slab_eq_lintegral hq hΛ.1 hπ hA
  -- `|ρ̃| = |μ|`
  have ha : ρ univ = m univ := by
    rw [hA univ MeasurableSet.univ]
    simp only [preimage_univ, fun r => (hπ.isProbability r).measure_univ, lintegral_one]
  -- `μ° = ∫ P_r ρ̃(dr)`
  have hb : ∀ E : Set ℝ, MeasurableSet E → foldMeasure q m E = ∫⁻ r, rotatedFibre q π r E ∂ρ := by
    intro E hE
    rw [foldMeasure, Measure.map_apply (measurable_qClass q) hE, hA _ (measurable_qClass q hE)]
    refine lintegral_congr fun r => ?_
    rw [rotatedFibre, Measure.map_apply (measurable_qRot q r) hE]
    rfl
  have hPm : Measurable (rotatedFibre q π) := measurable_rotatedFibre hπ.measurable hπ.isProbability
  have hPp := isProbabilityMeasure_rotatedFibre (q := q) hπ.isProbability
  -- `KL(π_r ‖ η) = KL(P_r ‖ η)`
  have hR : ∀ᵐ r ∂ρ, klDiv (π r) (haarPhase q) = klDiv (rotatedFibre q π r) (haarPhase q) := by
    filter_upwards [ae_rMarginal_pos hσ] with r hr
    haveI := hπ.isProbability r
    exact (klDiv_rotatedFibre hq (hπ.carried r) hr).symm
  haveI hMfin : IsFiniteMeasure (foldedStepNorm q m) := by
    refine ⟨?_⟩
    rw [foldedStepNorm, Measure.smul_apply, foldMeasure,
      Measure.map_apply (measurable_qClass q) MeasurableSet.univ, preimage_univ, smul_eq_mul]
    by_cases h0 : m univ = 0
    · rw [h0, mul_zero]
      exact ENNReal.zero_lt_top
    · rw [ENNReal.inv_mul_cancel h0 hmfin]
      exact ENNReal.one_lt_top
  -- the identity, in `[0,∞]`
  have hid : ∫⁻ r, klDiv (π r) (haarPhase q) ∂ρ =
      m univ * klDiv (foldedStepNorm q m) (haarPhase q) +
        ∫⁻ r, klDiv (rotatedFibre q π r) (foldedStepNorm q m) ∂ρ := by
    rw [lintegral_congr_ae hR]
    by_cases h0 : m univ = 0
    · have hρ0 : ρ = 0 := Measure.measure_univ_eq_zero.1 (ha.trans h0)
      rw [hρ0, h0]
      simp
    · obtain ⟨ρb, hρb⟩ : ∃ ρb : Measure ℝ, ρb = (m univ)⁻¹ • ρ := ⟨_, rfl⟩
      haveI : IsProbabilityMeasure ρb :=
        ⟨by rw [hρb, Measure.smul_apply, ha, smul_eq_mul, ENNReal.inv_mul_cancel h0 hmfin]⟩
      have hρ : ρ = m univ • ρb := by
        rw [hρb, smul_smul, ENNReal.mul_inv_cancel h0 hmfin, one_smul]
      let K : Kernel ℝ ℝ := ⟨rotatedFibre q π, hPm⟩
      haveI : IsMarkovKernel K := ⟨hPp⟩
      have hM : K ∘ₘ ρb = foldedStepNorm q m := by
        ext E hE
        rw [Measure.bind_apply hE K.aemeasurable, foldedStepNorm, Measure.smul_apply, hb E hE,
          hρb, lintegral_smul_measure, smul_eq_mul]
        rfl
      have key := lintegral_klDiv_eq_add ρb K (haarPhase q)
      rw [hM] at key
      rw [hρ, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul]
      rw [show ∫⁻ r, klDiv (rotatedFibre q π r) (haarPhase q) ∂ρb =
        ∫⁻ r, klDiv (K r) (haarPhase q) ∂ρb from rfl, key, mul_add]
      rfl
  refine ⟨ha, hb, ?_, hid, fun hKL => ?_⟩
  · rw [phaseEntropy, EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff, ← hρdef, hid]
    exact le_self_add
  · have hfin : m univ * klDiv (foldedStepNorm q m) (haarPhase q) ≠ ⊤ :=
      ENNReal.mul_ne_top hmfin hKL
    have hiff : ∀ y : ℝ≥0∞,
        m univ * klDiv (foldedStepNorm q m) (haarPhase q) + y =
          m univ * klDiv (foldedStepNorm q m) (haarPhase q) ↔ y = 0 := by
      intro y
      constructor
      · intro h
        exact (ENNReal.add_right_inj hfin).1 (h.trans (add_zero _).symm)
      · rintro rfl
        exact add_zero _
    rw [phaseEntropy, neg_inj, EReal.coe_ennreal_eq_coe_ennreal_iff, ← hρdef, hid, hiff,
      lintegral_eq_zero_iff (measurable_klDiv_kernel hPm hPp _)]
    constructor
    · intro h0
      filter_upwards [h0] with r hr
      haveI := hPp r
      exact klDiv_eq_zero_iff.1 hr
    · intro h0
      filter_upwards [h0] with r hr
      rw [hr, Pi.zero_apply]
      exact klDiv_self _

end Pyramids
