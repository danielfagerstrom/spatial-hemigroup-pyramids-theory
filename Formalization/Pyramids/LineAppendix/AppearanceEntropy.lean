/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.ModulatedSelection

/-!
# `prop:appearance-entropy`: the entropy of the appearance profile

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:appearance-entropy`. The second candidate
functional of the phase-entropy section: disintegrate the slab `Λ` on `F = [1,q) × (0,∞)` over the
displacements `v`, as `μ(dv) κ_v(dy)`, and put `𝔄 := -∫ KL(κ_v ‖ η) μ(dv)`.

## The route

* **The slab is a cylinder measure.** `Λ_F := Λ.restrict (cylinder q)` is carried by the cylinder
  `[1,q) × (0,∞)`, with the coordinates read as `(y, v)`. Its `r`-marginal in the sense of
  `def:phase-entropy` (the second marginal) is the step measure `μ`
  (`rMarginal_restrict_cylinder`, from `lem:knot-exponent-ladder`(3)), and it satisfies (A.e3):
  `ζ(vy) ≤ max(q², 1 + ℓ) ζ(v)` for `y ∈ [1,q)` (`cylWeight_mul_le`), and `∫ ζ(v) dΛ_F < ∞`
  is (A.e3)
  for the true cylinder measure of `Λ`. So an appearance disintegration is a phase disintegration
  of `Λ_F` (`isAppearance_iff`), and `𝔄` is its phase entropy (`appearanceEntropy_eq`); existence,
  uniqueness and `𝔄 = 0 ⇔ κ = η` a.e. are the general facts of `PhaseDisintegration` and
  `PhaseEntropy`.
* **The log-uniform slab.** `Λ_F = η ⊗ μ` iff `Λ((1,t] × ·) = (log_q t) μ` for `t ∈ [1,q]`
  (`prod_of_slab`, `slab_of_prod`). One direction is `Λ_F(Iic t × A) = Λ((1,t] × A)`
  (`restrict_cylinder_Iic_prod`, the lines `{1}`, `{q}` and the half-plane `v ≤ 0` carrying no
  mass) with
  `η(Iic t) = log_q t` (`haarPhase_Iic_eq`). The other compares, for `A` bounded away from `0`, the
  finite measures `S ↦ Λ_F(S × A)` and `μ(A) η` on the intervals `Iic x`, then extends to every `A`
  (`measure_ext_of_Ioi`) and to the product (`Measure.prod_eq`).
* **(2).** `Ψ_1 + (log_q t) φ` meets the conditions of `thm:annulus-parametrization`; its family has
  the exponents of the path on `[1,q]`, so by the uniqueness of the data its slabs are
  `ϖ_1 + (log_q t) μ`.
* **(3), uniqueness.** With no Gaussian part `ℬ = 0`; two members with `𝔄 = 0` have the same data on
  `[1,q)`, hence the same exponents, hence the same kernels (`qFamily_eq_of_lineExponent`).
* **(4).** At the similarity member `ϖ_t = T_t ϖ_1`. If also `T_t ϖ_1 = ϖ_1 + (log_q t) μ` on
  `[1,q]`, the tails `G(x) = ϖ_1([x,∞))`, `M(x) = μ([x,∞))` satisfy
  `G(x/t) = G(x) + log_q t · M(x)`; comparing two windows gives `M(x/s) = M(x)` for `s ∈ [1,q)`,
  so `M(xq) = M(x)`, and `G(x) = G(xqⁿ) + n M(x) ≥ n M(x)` for every `n` forces `M = 0`, so `μ = 0`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter ProbabilityTheory InformationTheory
open ScaleSpace (SymLevyPair IsSymLevyExponent)
open scoped ENNReal NNReal

/-! ## Definitions -/

/-- **An appearance disintegration** (`prop:appearance-entropy`): a measurable family of
probability measures `κ_v` on `[1,q)` with `Λ(E) = ∫ κ_v({y : (y,v) ∈ E}) μ(dv)` for Borel `E` in
`[1,q) × (0,∞)`, read as `Λ_F(E)` for every Borel `E`, `Λ_F` the restriction of `Λ` to
`[1,q) × (0,∞)`. -/
structure IsAppearanceDisintegration (q : ℝ) (Λ : Measure (ℝ × ℝ)) (m : Measure ℝ)
    (κ : ℝ → Measure ℝ) : Prop where
  measurable : Measurable κ
  isProbability : ∀ v : ℝ, IsProbabilityMeasure (κ v)
  carried : ∀ v : ℝ, κ v (Ico 1 q)ᶜ = 0
  disintegrates : ∀ E : Set (ℝ × ℝ), MeasurableSet E →
    Λ.restrict (cylinder q) E = ∫⁻ v, κ v ((fun y => (y, v)) ⁻¹' E) ∂m

/-- **The appearance entropy** `𝔄 := -∫ KL(κ_v ‖ η) μ(dv) ∈ [-∞, 0]`. -/
noncomputable def appearanceEntropy (q : ℝ) (m : Measure ℝ) (κ : ℝ → Measure ℝ) : EReal :=
  -(((∫⁻ v, klDiv (κ v) (haarPhase q) ∂m) : ℝ≥0∞) : EReal)

/-- **The log-uniform path** `Ψ_t := Ψ_1 + (log_q t) φ`. -/
noncomputable def logUniformPath (q : ℝ) (Ψ1 : ℝ → ℝ) (t ω : ℝ) : ℝ :=
  Ψ1 ω + Real.logb q t * knotStep q Ψ1 ω

/-! ## The lines carry no mass -/

section Lines

variable {q : ℝ} {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}

theorem appearance_line_null (h : IsSurfacePair q Λ B) {y : ℝ} (hy : 0 < y) :
    Λ ({y} ×ˢ univ) = 0 := by
  refine measure_mono_null (t := {y} ×ˢ Ioi 0 ∪ quadrantᶜ) ?_
    (measure_union_null (h.no_line y hy).1 h.carried)
  rintro ⟨a, b⟩ ⟨ha, -⟩
  by_cases hb : 0 < b
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr fun hq' => hb hq'.2

theorem appearance_neg_null (h : IsSurfacePair q Λ B) : Λ (univ ×ˢ Iic 0) = 0 := by
  refine measure_mono_null ?_ h.carried
  rintro ⟨a, b⟩ ⟨-, hb⟩ hq'
  exact not_lt.2 (mem_Iic.1 hb) hq'.2

/-- **`Λ_F(Iic x × A) = Λ((1, min x q] × A)`** (for `x < 1` both sides vanish). -/
theorem restrict_cylinder_Iic_prod (hq : 1 < q) (h : IsSurfacePair q Λ B) (x : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    Λ.restrict (cylinder q) (Iic x ×ˢ A) = slab Λ 1 (min x q) A := by
  rw [Measure.restrict_apply (measurableSet_Iic.prod hA), slab_apply Λ 1 _ hA]
  refine measure_congr (ae_eq_set.2 ⟨?_, ?_⟩)
  · refine measure_mono_null ?_ (appearance_line_null h one_pos)
    rintro ⟨y, v⟩ hp
    simp only [cylinder, Set.mem_sdiff, mem_inter_iff, mem_prod, mem_Iic, mem_Ico, mem_Ioi, mem_Ioc,
      not_and_or, not_lt, not_le] at hp
    obtain ⟨⟨⟨hyx, hvA⟩, ⟨hy1, hyq⟩, -⟩, hn⟩ := hp
    refine ⟨mem_singleton_iff.2 ?_, mem_univ v⟩
    rcases hn with (hn | hn) | hn
    · exact le_antisymm hn hy1
    · exact absurd (le_min hyx hyq.le) (not_le.2 hn)
    · exact absurd hvA hn
  · refine measure_mono_null ?_
      (measure_union_null (appearance_line_null h (by linarith : (0 : ℝ) < q))
        (appearance_neg_null h))
    rintro ⟨y, v⟩ ⟨hpT, hn⟩
    simp only [mem_prod, mem_Ioc] at hpT
    obtain ⟨⟨hy1, hyt⟩, hvA⟩ := hpT
    have hyx : y ≤ x := hyt.trans (min_le_left _ _)
    have hyq : y ≤ q := hyt.trans (min_le_right _ _)
    by_cases hv : 0 < v
    · refine Or.inl ⟨mem_singleton_iff.2 ?_, mem_univ v⟩
      by_contra hne
      exact hn ⟨⟨mem_Iic.2 hyx, hvA⟩, ⟨hy1.le, lt_of_le_of_ne hyq hne⟩, hv⟩
    · exact Or.inr ⟨mem_univ y, mem_Iic.2 (not_lt.1 hv)⟩

end Lines

/-! ## `η` on the intervals `Iic x` -/

theorem haarPhase_Iic_lt {q x : ℝ} (hx : x < 1) : haarPhase q (Iic x) = 0 := by
  refine measure_mono_null ?_ (haarPhase_compl_Ico q)
  intro y hy hyI
  exact absurd (lt_of_le_of_lt (mem_Iic.1 hy) hx) (not_lt.2 hyI.1)

/-- **`η((-∞, x]) = log_q (min x q)`** for `x ≥ 1`. -/
theorem haarPhase_Iic_eq {q : ℝ} (hq : 1 < q) {x : ℝ} (hx : 1 ≤ x) :
    haarPhase q (Iic x) = ENNReal.ofReal (Real.logb q (min x q)) := by
  have hl : 0 < Real.log q := Real.log_pos hq
  set t := min x q with ht
  have ht1 : 1 ≤ t := le_min hx hq.le
  have htq : t ≤ q := min_le_right _ _
  have hset : (Iic x ∩ Ico 1 q : Set ℝ) =ᵐ[(volume : Measure ℝ)] (Ioc 1 t : Set ℝ) := by
    refine ae_eq_set.2 ⟨measure_mono_null (t := {1}) ?_ (measure_singleton 1),
      measure_mono_null (t := {q}) ?_ (measure_singleton q)⟩
    · intro y hy
      simp only [Set.mem_sdiff, mem_inter_iff, mem_Iic, mem_Ico, mem_Ioc, not_and_or, not_lt,
        not_le] at hy
      obtain ⟨⟨hyx, hy1, hyq⟩, hn⟩ := hy
      refine mem_singleton_iff.2 ?_
      rcases hn with hn | hn
      · exact le_antisymm hn hy1
      · exact absurd (le_min hyx hyq.le) (not_le.2 hn)
    · intro y hy
      simp only [Set.mem_sdiff, mem_inter_iff, mem_Iic, mem_Ico, mem_Ioc, not_and_or, not_lt,
        not_le] at hy
      obtain ⟨⟨hy1, hyt⟩, hn⟩ := hy
      refine mem_singleton_iff.2 ?_
      rcases hn with hn | hn | hn
      · exact absurd (hyt.trans (min_le_left _ _)) (not_le.2 hn)
      · exact absurd hy1 (not_lt.2 hn.le)
      · exact le_antisymm (hyt.trans htq) hn
  have hint : IntegrableOn (fun θ : ℝ => 1 / (Real.log q * θ)) (Icc 1 t) := by
    refine ContinuousOn.integrableOn_Icc (fun θ hθ => ?_)
    have : (Real.log q * θ) ≠ 0 := (mul_pos hl (lt_of_lt_of_le one_pos hθ.1)).ne'
    exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id) this).continuousWithinAt
  rw [haarPhase, withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    setLIntegral_congr hset, ← ofReal_integral_eq_lintegral_ofReal
      (hint.mono_set Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall fun θ hθ =>
        (one_div_pos.2 (mul_pos hl (lt_trans one_pos hθ.1))).le)),
    ← intervalIntegral.integral_of_le ht1]
  simp_rw [one_div, mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (by linarith), div_one,
    Real.logb, inv_mul_eq_div]

/-! ## The slab is a cylinder measure -/

section Member

variable {q : ℝ} {Ψ1 : ℝ → ℝ} {m : Measure ℝ} {μ : ℝ → ℝ → Measure ℝ} {Λ : Measure (ℝ × ℝ)}
  {B : Measure ℝ}

theorem restrict_cylinder_compl (q : ℝ) (Λ : Measure (ℝ × ℝ)) :
    Λ.restrict (cylinder q) (cylinder q)ᶜ = 0 := by
  have hc : MeasurableSet (cylinder q) := measurableSet_Ico.prod measurableSet_Ioi
  rw [Measure.restrict_apply' hc, compl_inter_self, measure_empty]

/-- The step measure is a Lévy measure: σ-finite, null on `(-∞,0]`, finite on `(ε,∞)`. -/
theorem stepMeasure_facts (hm : IsStepMeasure q Ψ1 m) :
    SigmaFinite m ∧ m (Iic 0) = 0 ∧ ∀ ε : ℝ, 0 < ε → m (Ioi ε) ≠ ⊤ := by
  obtain ⟨R, -, hR⟩ := hm
  subst hR
  exact ⟨SymLevyPair_sigmaFinite R, R.ν_folded, fun ε hε => SymLevyPair_measure_Ioi_ne_top R hε⟩

/-- **The second marginal of `Λ_F` is the step measure.** -/
theorem rMarginal_restrict_cylinder (hq : 1 < q) (hm : IsStepMeasure q Ψ1 m)
    (hμ : μ ∈ modulationOrbit q Ψ1) (hΛ : IsFamilyPair q μ Λ B) :
    rMarginal q (Λ.restrict (cylinder q)) = m := by
  rw [rMarginal_eq_map (restrict_cylinder_compl q Λ),
    ← knot_exponent_ladder_3 hq Ψ1 m hm μ hμ Λ B hΛ]
  ext A hA
  have hL := restrict_cylinder_Iic_prod hq hΛ.1 q hA
  rw [min_self] at hL
  rw [Measure.map_apply measurable_snd hA, ← hL, Measure.restrict_apply (measurable_snd hA),
    Measure.restrict_apply (measurableSet_Iic.prod hA)]
  congr 1
  ext ⟨y, v⟩
  simp only [cylinder, mem_inter_iff, mem_preimage, mem_prod, mem_Iic, mem_Ico, mem_Ioi]
  constructor
  · rintro ⟨hv, hy, hv0⟩
    exact ⟨⟨hy.2.le, hv⟩, hy, hv0⟩
  · rintro ⟨⟨-, hv⟩, hy, hv0⟩
    exact ⟨hv, hy, hv0⟩

/-- **`Λ_F` satisfies (A.e3).** -/
theorem isCylIntegrable_restrict_cylinder (hq : 1 < q) (h : IsSurfacePair q Λ B) :
    IsCylIntegrable (Λ.restrict (cylinder q)) := by
  obtain ⟨hσ, hmix⟩ := cylMeasure_spec hq h.carried h.invariant
  have hint : IsCylIntegrable (cylMeasure q Λ) := by
    refine (knot_atom_cascades_2_integrable hq _ hσ).1.1 ?_
    rw [hmix]
    exact h.integrable
  have hmw : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (cylWeight (p.2 * p.1)) :=
    (measurable_cylWeight.comp (measurable_snd.mul measurable_fst)).ennreal_ofReal
  have hcyl : ∫⁻ p, ENNReal.ofReal (cylWeight (p.2 * p.1)) ∂(cylMeasure q Λ) =
      ∫⁻ p, ENNReal.ofReal (cylWeight p.2) ∂(Λ.restrict (cylinder q)) := by
    rw [cylMeasure_eq, lintegral_map hmw measurable_cylMap]
    refine setLIntegral_congr_fun (measurableSet_Ico.prod measurableSet_Ioi) ?_
    rintro ⟨y, v⟩ ⟨hy, -⟩
    have hy0 : y ≠ 0 := (lt_of_lt_of_le one_pos hy.1).ne'
    simp only [cylMap, div_mul_cancel₀ v hy0]
  have hc : MeasurableSet (cylinder q) := measurableSet_Ico.prod measurableSet_Ioi
  set K : ℝ := max (q ^ 2) (1 + Real.log q) with hK
  unfold IsCylIntegrable
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal K *
    ∫⁻ p, ENNReal.ofReal (cylWeight p.2) ∂(Λ.restrict (cylinder q))) ?_ ?_
  · rw [← hcyl]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hint
  · calc ∫⁻ p, ENNReal.ofReal (cylWeight (p.2 * p.1)) ∂(Λ.restrict (cylinder q))
        ≤ ∫⁻ p, ENNReal.ofReal K * ENNReal.ofReal (cylWeight p.2) ∂(Λ.restrict (cylinder q)) := by
          refine setLIntegral_mono' hc fun p hp => ?_
          have hK0 : 0 ≤ K := le_trans (by positivity) (le_max_left _ _)
          rw [← ENNReal.ofReal_mul hK0]
          exact ENNReal.ofReal_le_ofReal (cylWeight_mul_le hq hp.1)
      _ = ENNReal.ofReal K * ∫⁻ p, ENNReal.ofReal (cylWeight p.2) ∂(Λ.restrict (cylinder q)) :=
          lintegral_const_mul _ ((measurable_cylWeight.comp measurable_snd).ennreal_ofReal)

/-- An appearance disintegration is a phase disintegration of `Λ_F`. -/
theorem isAppearance_iff (hrm : rMarginal q (Λ.restrict (cylinder q)) = m) {κ : ℝ → Measure ℝ} :
    IsAppearanceDisintegration q Λ m κ ↔ IsPhaseDisintegration q (Λ.restrict (cylinder q)) κ := by
  constructor
  · intro h
    exact ⟨h.measurable, h.isProbability, h.carried, fun E hE => by
      rw [hrm]; exact h.disintegrates E hE⟩
  · intro h
    exact ⟨h.measurable, h.isProbability, h.carried, fun E hE => by
      rw [← hrm]; exact h.disintegrates E hE⟩

theorem appearanceEntropy_eq (hrm : rMarginal q (Λ.restrict (cylinder q)) = m)
    (κ : ℝ → Measure ℝ) :
    appearanceEntropy q m κ = phaseEntropy q (Λ.restrict (cylinder q)) κ := by
  rw [appearanceEntropy, phaseEntropy, hrm]

end Member

/-! ## The log-uniform slab -/

section Slab

variable {q : ℝ} {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ} {m : Measure ℝ}

/-- **`Λ_F = η ⊗ μ` gives `Λ((1,t] × ·) = (log_q t) μ`.** -/
theorem slab_of_prod (hq : 1 < q) (h : IsSurfacePair q Λ B) [SFinite m]
    (hprod : Λ.restrict (cylinder q) = (haarPhase q).prod m) {t : ℝ} (ht : t ∈ Icc 1 q) :
    slab Λ 1 t = ENNReal.ofReal (Real.logb q t) • m := by
  ext A hA
  have hmin : min t q = t := min_eq_left ht.2
  rw [← hmin, ← restrict_cylinder_Iic_prod hq h t hA, hprod, Measure.prod_prod,
    haarPhase_Iic_eq hq ht.1, Measure.smul_apply, smul_eq_mul]

/-- **`Λ((1,t] × ·) = (log_q t) μ` on `[1,q]` gives `Λ_F = η ⊗ μ`.** -/
theorem prod_of_slab (hq : 1 < q) (h : IsSurfacePair q Λ B) [SigmaFinite m]
    (hm0 : m (Iic 0) = 0) (hmfin : ∀ ε : ℝ, 0 < ε → m (Ioi ε) ≠ ⊤)
    (hs : ∀ t ∈ Icc 1 q, slab Λ 1 t = ENNReal.ofReal (Real.logb q t) • m) :
    Λ.restrict (cylinder q) = (haarPhase q).prod m := by
  haveI := isProbabilityMeasure_haarPhase hq
  set ΛF := Λ.restrict (cylinder q) with hΛF
  -- the value on `Iic x × A`
  have hIic : ∀ x : ℝ, ∀ A : Set ℝ, MeasurableSet A →
      ΛF (Iic x ×ˢ A) = haarPhase q (Iic x) * m A := by
    intro x A hA
    rcases lt_or_ge x 1 with hx | hx
    · rw [haarPhase_Iic_lt hx, zero_mul, hΛF, Measure.restrict_apply (measurableSet_Iic.prod hA)]
      refine measure_mono_null ?_ measure_empty
      rintro ⟨y, v⟩ ⟨⟨hyx, -⟩, hy, -⟩
      exact absurd (lt_of_le_of_lt (mem_Iic.1 hyx) hx) (not_lt.2 hy.1)
    · have hmem : min x q ∈ Icc 1 q := ⟨le_min hx hq.le, min_le_right _ _⟩
      rw [hΛF, restrict_cylinder_Iic_prod hq h x hA, hs _ hmem, haarPhase_Iic_eq hq hx,
        Measure.smul_apply, smul_eq_mul]
  -- for `A` bounded away from `0`, the `y`-marginals agree
  have hrect : ∀ S : Set ℝ, MeasurableSet S → ∀ A : Set ℝ, MeasurableSet A →
      ΛF (S ×ˢ A) = haarPhase q S * m A := by
    intro S hS
    have hpos : ∀ ε : ℝ, 0 < ε → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioi ε →
        ΛF (S ×ˢ A) = haarPhase q S * m A := by
      intro ε hε A hA hAε
      have hmA : m A ≠ ⊤ := ne_top_of_le_ne_top (hmfin ε hε) (measure_mono hAε)
      set M1 : Measure ℝ := (ΛF.restrict (univ ×ˢ A)).map Prod.fst with hM1
      have hM1apply : ∀ T : Set ℝ, MeasurableSet T → M1 T = ΛF (T ×ˢ A) := by
        intro T hT
        rw [hM1, Measure.map_apply measurable_fst hT,
          Measure.restrict_apply (measurable_fst hT)]
        congr 1
        ext ⟨y, v⟩
        simp
      haveI : IsFiniteMeasure M1 := by
        refine ⟨?_⟩
        rw [hM1apply univ MeasurableSet.univ]
        have hle : ΛF (univ ×ˢ A) ≤ ΛF (Iic q ×ˢ A) := by
          rw [hΛF, Measure.restrict_apply (MeasurableSet.univ.prod hA),
            Measure.restrict_apply (measurableSet_Iic.prod hA)]
          refine measure_mono ?_
          rintro ⟨y, v⟩ ⟨⟨-, hv⟩, hy, hv0⟩
          exact ⟨⟨mem_Iic.2 hy.2.le, hv⟩, hy, hv0⟩
        refine lt_of_le_of_lt hle ?_
        rw [hIic q A hA]
        exact ENNReal.mul_lt_top (measure_lt_top _ _) hmA.lt_top
      have hM : M1 = m A • haarPhase q := by
        refine Measure.ext_of_Iic M1 _ fun x => ?_
        rw [hM1apply _ measurableSet_Iic, hIic x A hA, Measure.smul_apply, smul_eq_mul,
          mul_comm]
      rw [← hM1apply S hS, hM, Measure.smul_apply, smul_eq_mul, mul_comm]
    intro A hA
    set N1 : Measure ℝ := (ΛF.restrict (S ×ˢ univ)).map Prod.snd with hN1
    have hN1apply : ∀ T : Set ℝ, MeasurableSet T → N1 T = ΛF (S ×ˢ T) := by
      intro T hT
      rw [hN1, Measure.map_apply measurable_snd hT, Measure.restrict_apply (measurable_snd hT)]
      congr 1
      ext ⟨y, v⟩
      simp [and_comm]
    have hN : N1 = haarPhase q S • m := by
      refine measure_ext_of_Ioi ?_ ?_ fun ε hε A' hA' hA'ε => ?_
      · rw [hN1apply _ measurableSet_Iic, hΛF, Measure.restrict_apply (hS.prod measurableSet_Iic)]
        refine measure_mono_null ?_ measure_empty
        rintro ⟨y, v⟩ ⟨⟨-, hv⟩, -, hv0⟩
        exact absurd (mem_Iic.1 hv) (not_le.2 hv0)
      · rw [Measure.smul_apply, hm0, smul_zero]
      · rw [hN1apply _ hA', hpos ε hε A' hA' hA'ε, Measure.smul_apply, smul_eq_mul]
    rw [← hN1apply A hA, hN, Measure.smul_apply, smul_eq_mul]
  exact (Measure.prod_eq fun S A hS hA => hrect S hS A hA).symm

end Slab

/-! ## `ϖ_t = ϖ_1 + (log_q t) μ` and `Λ((1,t] × ·) = (log_q t) μ` -/

theorem slab_zero_iff {q : ℝ} {μ : ℝ → ℝ → Measure ℝ} {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ}
    (hΛ : IsFamilyPair q μ Λ B) {m : Measure ℝ} (hm0 : m (Iic 0) = 0) {t c : ℝ} (ht : 1 ≤ t) :
    slab Λ 0 t = slab Λ 0 1 + ENNReal.ofReal c • m ↔ slab Λ 1 t = ENNReal.ofReal c • m := by
  rw [slab_add Λ zero_le_one ht]
  constructor
  · intro h
    obtain ⟨P1, -, hP1ν, -⟩ := hΛ.2 1 one_pos
    refine measure_ext_of_Ioi (slab_Iic_zero hΛ.1.carried 1 t) (by
      rw [Measure.smul_apply, hm0, smul_zero]) fun ε hε A hA hAε => ?_
    have hfin : slab Λ 0 1 A ≠ ⊤ := by
      rw [← hP1ν]
      exact ne_top_of_le_ne_top (SymLevyPair_measure_Ioi_ne_top P1 hε) (measure_mono hAε)
    have e := congrArg (fun ν : Measure ℝ => ν A) h
    simp only [Measure.add_apply] at e
    exact (ENNReal.add_right_inj hfin).1 e
  · intro h
    rw [h]

/-! ## The data along the log-uniform path -/

section Path

variable {q : ℝ} {Ψ1 : ℝ → ℝ}

/-- `Ψ_1 + cφ` has the data `(a_1 + c a_φ, ϖ_1 + cμ)`. -/
theorem hasExpData_add_smul {Ψ1 φ : ℝ → ℝ} {P R : SymLevyPair} (hP : HasExpData Ψ1 P)
    (hR : HasExpData φ R) {c : ℝ} (hc : 0 ≤ c) :
    HasExpData (fun ω => Ψ1 ω + c * φ ω) (SymLevyPair_add P (SymLevyPair_smul c hc R)) := by
  intro ω
  show Ψ1 ω + c * φ ω = _
  rw [SymLevyPair_add_exponent, SymLevyPair_smul_exponent, ← hP ω, ← hR ω]

theorem isAnnulusPath_logUniform (hq : 1 < q) (hK : IsKnotExponent q Ψ1) :
    IsAnnulusPath q (logUniformPath q Ψ1) := by
  obtain ⟨⟨P, hP⟩, ⟨R, hR⟩, ω0, hω0⟩ := hK
  have hφ0 : ∀ ω, 0 ≤ knotStep q Ψ1 ω := isSymLevyExponent_nonneg ⟨R, hR⟩
  have hΨ0 : ∀ ω, 0 ≤ Ψ1 ω := isSymLevyExponent_nonneg ⟨P, hP⟩
  have hlog : ∀ t : ℝ, 1 ≤ t → 0 ≤ Real.logb q t := fun t ht => Real.logb_nonneg hq ht
  -- a point where `Ψ_1 ≠ 0`
  have hΨne : ∃ ω1, 0 < Ψ1 ω1 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∀ ω, Ψ1 ω = 0 := fun ω => le_antisymm (hcon ω) (hΨ0 ω)
    exact hω0 (by rw [knotStep, h0, h0, sub_zero])
  obtain ⟨ω1, hω1⟩ := hΨne
  refine ⟨fun t ht => ⟨⟨_, hasExpData_add_smul hP hR (hlog t ht.1)⟩, ω1, ?_⟩,
    fun t t' ht htt' ht' => ?_, fun ω => ?_, fun ω => ?_⟩
  · have := mul_nonneg (hlog t ht.1) (hφ0 ω1)
    simp only [logUniformPath]
    exact (by linarith : Ψ1 ω1 + Real.logb q t * knotStep q Ψ1 ω1 ≠ 0)
  · have hc : 0 < Real.logb q t' - Real.logb q t :=
      sub_pos.2 (Real.logb_lt_logb hq (by linarith) htt')
    refine ⟨⟨SymLevyPair_smul _ hc.le R, fun ω => ?_⟩, ω0, ?_⟩
    · rw [SymLevyPair_smul_exponent, ← hR ω]
      simp only [logUniformPath]
      ring
    simp only [logUniformPath]
    intro h0
    have : (Real.logb q t' - Real.logb q t) * knotStep q Ψ1 ω0 = 0 := by linarith
    exact hω0 ((mul_eq_zero.1 this).resolve_left hc.ne')
  · simp only [logUniformPath, Real.logb_self_eq_one hq, Real.logb_one, one_mul, zero_mul,
      add_zero, knotStep]
    ring
  · simp only [logUniformPath]
    refine continuousOn_const.add (ContinuousOn.mul ?_ continuousOn_const)
    exact (Real.continuousOn_log.mono fun t ht => by
      simp only [mem_compl_iff, mem_singleton_iff]
      exact (lt_of_lt_of_le one_pos ht.1).ne').div_const _

end Path

/-! ## The data at `1` of a member -/

theorem exists_data_one {q : ℝ} {Ψ1 : ℝ → ℝ} {μ : ℝ → ℝ → Measure ℝ} {Λ : Measure (ℝ × ℝ)}
    {B : Measure ℝ} (hμ : μ ∈ modulationOrbit q Ψ1) (hΛ : IsFamilyPair q μ Λ B) :
    ∃ P1 : SymLevyPair, HasExpData Ψ1 P1 ∧ P1.ν = slab Λ 0 1 := by
  obtain ⟨P1, hP1f, hP1ν, -⟩ := hΛ.2 1 one_pos
  refine ⟨P1, fun ω => ?_, hP1ν⟩
  rw [← lineExponent_eq_of_folded hμ.1.1 zero_le_one hP1f ω, lineExponent_one_of_mem_orbit hμ]

/-! ## The node -/

/-- **`prop:appearance-entropy`(1).** Every member has an appearance disintegration, and any two
agree for `μ`-almost every `v`. -/
theorem appearance_entropy_1 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ) (m : Measure ℝ)
    (hm : IsStepMeasure q Ψ1 m) (μ : ℝ → ℝ → Measure ℝ) (hμ : μ ∈ modulationOrbit q Ψ1)
    (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (hΛ : IsFamilyPair q μ Λ B) :
    (∃ κ : ℝ → Measure ℝ, IsAppearanceDisintegration q Λ m κ) ∧
      ∀ κ κ' : ℝ → Measure ℝ, IsAppearanceDisintegration q Λ m κ →
        IsAppearanceDisintegration q Λ m κ' → ∀ᵐ v ∂m, κ v = κ' v := by
  have hrm := rMarginal_restrict_cylinder hq hm hμ hΛ
  have hσ := restrict_cylinder_compl q Λ
  have hint := isCylIntegrable_restrict_cylinder hq hΛ.1
  refine ⟨?_, fun κ κ' hκ hκ' => ?_⟩
  · obtain ⟨κ, hκ⟩ := exists_phaseDisintegration hq hσ hint
    exact ⟨κ, (isAppearance_iff hrm).2 hκ⟩
  · have h := phaseDisintegration_ae_eq hσ hint ((isAppearance_iff hrm).1 hκ)
      ((isAppearance_iff hrm).1 hκ')
    rwa [hrm] at h

/-- `𝔄 = 0` iff `Λ_F = η ⊗ μ`. -/
theorem appearanceEntropy_eq_zero_iff_prod {q : ℝ} (hq : 1 < q) {Ψ1 : ℝ → ℝ} {m : Measure ℝ}
    (hm : IsStepMeasure q Ψ1 m) {μ : ℝ → ℝ → Measure ℝ} (hμ : μ ∈ modulationOrbit q Ψ1)
    {Λ : Measure (ℝ × ℝ)} {B : Measure ℝ} (hΛ : IsFamilyPair q μ Λ B) {κ : ℝ → Measure ℝ}
    (hκ : IsAppearanceDisintegration q Λ m κ) :
    appearanceEntropy q m κ = 0 ↔ Λ.restrict (cylinder q) = (haarPhase q).prod m := by
  have hrm := rMarginal_restrict_cylinder hq hm hμ hΛ
  have hσ := restrict_cylinder_compl q Λ
  have hint := isCylIntegrable_restrict_cylinder hq hΛ.1
  have hπ := (isAppearance_iff hrm).1 hκ
  haveI := (stepMeasure_facts hm).1
  rw [appearanceEntropy_eq hrm, phaseEntropy_eq_zero_iff hq hπ]
  constructor
  · intro h
    haveI : SFinite (rMarginal q (Λ.restrict (cylinder q))) := by rw [hrm]; infer_instance
    have e := eq_prod_of_ae_haarPhase hπ h
    rwa [hrm] at e
  · intro hprod
    have hd := isPhaseDisintegration_haarPhase_prod hq m
    rw [← hprod] at hd
    exact phaseDisintegration_ae_eq hσ hint hπ hd

/-- **`prop:appearance-entropy`(3), the first sentence.** `𝔄 ≤ 0`, with equality iff
`ϖ_t = ϖ_1 + (log_q t) μ` for every `t ∈ [1,q]`. -/
theorem appearance_entropy_3 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ) (m : Measure ℝ)
    (hm : IsStepMeasure q Ψ1 m) (μ : ℝ → ℝ → Measure ℝ) (hμ : μ ∈ modulationOrbit q Ψ1)
    (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (hΛ : IsFamilyPair q μ Λ B) (κ : ℝ → Measure ℝ)
    (hκ : IsAppearanceDisintegration q Λ m κ) :
    appearanceEntropy q m κ ≤ 0 ∧
      (appearanceEntropy q m κ = 0 ↔
        ∀ t ∈ Icc 1 q, slab Λ 0 t = slab Λ 0 1 + ENNReal.ofReal (Real.logb q t) • m) := by
  obtain ⟨hmσ, hm0, hmfin⟩ := stepMeasure_facts hm
  haveI := hmσ
  refine ⟨EReal.neg_le_zero.2 (EReal.coe_ennreal_nonneg _), ?_⟩
  rw [appearanceEntropy_eq_zero_iff_prod hq hm hμ hΛ hκ]
  constructor
  · intro hprod t ht
    exact (slab_zero_iff hΛ hm0 ht.1).2 (slab_of_prod hq hΛ.1 hprod ht)
  · intro hs
    exact prod_of_slab hq hΛ.1 hm0 hmfin fun t ht => (slab_zero_iff hΛ hm0 ht.1).1 (hs t ht)

/-- **`prop:appearance-entropy`(2).** The log-uniform path satisfies the conditions of
`thm:annulus-parametrization`; its family is a member, with the exponents of the path on `[1,q]`,
the slabs `ϖ_t = ϖ_1 + (log_q t) μ` there, and `𝔄 = 0`. -/
theorem appearance_entropy_2 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ) (hK : IsKnotExponent q Ψ1)
    (m : Measure ℝ) (hm : IsStepMeasure q Ψ1 m) :
    IsAnnulusPath q (logUniformPath q Ψ1) ∧
      ∃ μ ∈ modulationOrbit q Ψ1,
        (∀ t ∈ Icc 1 q, ∀ ω : ℝ, lineExponent μ t ω = logUniformPath q Ψ1 t ω) ∧
        ∀ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ), IsFamilyPair q μ Λ B →
          (∀ t ∈ Icc 1 q, slab Λ 0 t = slab Λ 0 1 + ENNReal.ofReal (Real.logb q t) • m) ∧
          ∀ κ : ℝ → Measure ℝ, IsAppearanceDisintegration q Λ m κ →
            appearanceEntropy q m κ = 0 := by
  have hpath := isAnnulusPath_logUniform hq hK
  obtain ⟨⟨μ, hlaws⟩, hall⟩ := annulus_parametrization_surjective hq _ hpath
  obtain ⟨hμq, hμt⟩ := hall μ hlaws
  have hmem : μ ∈ modulationOrbit q Ψ1 := by
    refine ⟨hμq, fun ω => ?_⟩
    rw [charFun_kernel_eq_exp hμq.1 zero_le_one ω, hμt 1 ⟨le_rfl, hq.le⟩ ω]
    simp [logUniformPath, Real.logb_one]
  have hslab : ∀ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ), IsFamilyPair q μ Λ B →
      ∀ t ∈ Icc 1 q, slab Λ 0 t = slab Λ 0 1 + ENNReal.ofReal (Real.logb q t) • m := by
    intro Λ B hΛ t ht
    obtain ⟨P1, hP1, hP1ν⟩ := exists_data_one hmem hΛ
    obtain ⟨R, hR, hRν⟩ := hm
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
    obtain ⟨P, hPf, hPν, -⟩ := hΛ.2 t ht0
    have hPdata : HasExpData (logUniformPath q Ψ1 t) P := fun ω => by
      rw [← hμt t ht ω, lineExponent_eq_of_folded hμq.1 ht0.le hPf ω]
    have hc : 0 ≤ Real.logb q t := Real.logb_nonneg hq ht.1
    have hQ := hasExpData_add_smul hP1 hR hc
    have hu := (line_exponent_data_1_unique _ P _ hPdata hQ).2
    rw [← hPν, hu, ← hP1ν, ← hRν]
    rfl
  refine ⟨hpath, μ, hmem, hμt, fun Λ B hΛ => ⟨hslab Λ B hΛ, fun κ hκ => ?_⟩⟩
  exact (appearance_entropy_3 hq Ψ1 m hm μ hmem Λ B hΛ κ hκ).2.2 (hslab Λ B hΛ)

/-- **`prop:appearance-entropy`(3), uniqueness.** On a ladder with no Gaussian part, two members
with `𝔄 = 0` coincide; with (2), the log-uniform member is the unique maximizer. -/
theorem appearance_entropy_3_unique {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ) (m : Measure ℝ)
    (hm : IsStepMeasure q Ψ1 m) (hnoG : HasNoGaussianStep q Ψ1)
    (μ μ' : ℝ → ℝ → Measure ℝ) (hμ : μ ∈ modulationOrbit q Ψ1) (hμ' : μ' ∈ modulationOrbit q Ψ1)
    (Λ Λ' : Measure (ℝ × ℝ)) (B B' : Measure ℝ) (hΛ : IsFamilyPair q μ Λ B)
    (hΛ' : IsFamilyPair q μ' Λ' B') (κ κ' : ℝ → Measure ℝ)
    (hκ : IsAppearanceDisintegration q Λ m κ) (hκ' : IsAppearanceDisintegration q Λ' m κ')
    (h0 : appearanceEntropy q m κ = 0) (h0' : appearanceEntropy q m κ' = 0) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t := by
  have hs := (appearance_entropy_3 hq Ψ1 m hm μ hμ Λ B hΛ κ hκ).2.1 h0
  have hs' := (appearance_entropy_3 hq Ψ1 m hm μ' hμ' Λ' B' hΛ' κ' hκ').2.1 h0'
  have hB := gauss_eq_zero_of_noGaussianStep hq hnoG hμ hΛ
  have hB' := gauss_eq_zero_of_noGaussianStep hq hnoG hμ' hΛ'
  obtain ⟨P1, hP1, hP1ν⟩ := exists_data_one hμ hΛ
  obtain ⟨P1', hP1', hP1ν'⟩ := exists_data_one hμ' hΛ'
  have h1 : slab Λ 0 1 = slab Λ' 0 1 := by
    rw [← hP1ν, ← hP1ν', (line_exponent_data_1_unique _ P1 P1' hP1 hP1').2]
  refine qFamily_eq_of_lineExponent hq hμ.1 hμ'.1 fun t ht ω => ?_
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
  have htI : t ∈ Icc 1 q := ⟨ht.1, ht.2.le⟩
  obtain ⟨P, hPf, hPν, hPa⟩ := hΛ.2 t ht0
  obtain ⟨P', hPf', hPν', hPa'⟩ := hΛ'.2 t ht0
  rw [lineExponent_eq_of_folded hμ.1.1 ht0.le hPf ω,
    lineExponent_eq_of_folded hμ'.1.1 ht0.le hPf' ω]
  have ha : P.a = P'.a := by
    rw [hB t ht0] at hPa
    rw [hB' t ht0] at hPa'
    have e1 : P.a = 0 := le_antisymm (ENNReal.ofReal_eq_zero.1 hPa) P.a_nonneg
    have e2 : P'.a = 0 := le_antisymm (ENNReal.ofReal_eq_zero.1 hPa') P'.a_nonneg
    rw [e1, e2]
  have hν : P.ν = P'.ν := by
    rw [hPν, hPν', hs t htI, hs' t htI, h1]
  simp only [SymLevyPair.exponent, SymLevyPair.exponentL, ha, hν]

/-- **`prop:appearance-entropy`(4).** If `μ ≠ 0` and the orbit contains the similarity member, the
similarity member has `𝔄 < 0`. -/
theorem appearance_entropy_4 {q : ℝ} (hq : 1 < q) (Ψ1 : ℝ → ℝ) (m : Measure ℝ)
    (hm : IsStepMeasure q Ψ1 m) (hm0 : m ≠ 0) (μ₀ : ℝ → ℝ → Measure ℝ)
    (hμ₀ : μ₀ ∈ modulationOrbit q Ψ1)
    (hsim : ∀ t : ℝ, 0 < t → ∀ ω : ℝ, lineExponent μ₀ t ω = Ψ1 (t * ω))
    (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (hΛ : IsFamilyPair q μ₀ Λ B) (κ : ℝ → Measure ℝ)
    (hκ : IsAppearanceDisintegration q Λ m κ) :
    appearanceEntropy q m κ < 0 := by
  have h3 := appearance_entropy_3 hq Ψ1 m hm μ₀ hμ₀ Λ B hΛ κ hκ
  refine lt_of_le_of_ne h3.1 fun h0 => hm0 ?_
  have hs := h3.2.1 h0
  obtain ⟨-, hmIic, hmfin⟩ := stepMeasure_facts hm
  -- the similarity member: `ϖ_t = T_t ϖ_1`
  have hcov := ((lineExponent_cov_iff hμ₀.1 hΛ).1
    (phase_entropy_selection_1 hq Ψ1 μ₀ hμ₀ hsim).1).1
  have hT := (slab_cov_iff Λ).1 hcov
  set ϖ := slab Λ 0 1 with hϖ
  obtain ⟨P1, -, hP1ν, -⟩ := hΛ.2 1 one_pos
  have hϖfin : ∀ x : ℝ, 0 < x → ϖ (Ici x) ≠ ⊤ := fun x hx => by
    rw [hϖ, ← hP1ν]
    exact ne_top_of_le_ne_top (SymLevyPair_measure_Ioi_ne_top P1 (half_pos hx))
      (measure_mono fun y hy => lt_of_lt_of_le (half_lt_self hx) (mem_Ici.1 hy))
  have hmfin' : ∀ x : ℝ, 0 < x → m (Ici x) ≠ ⊤ := fun x hx =>
    ne_top_of_le_ne_top (hmfin _ (half_pos hx))
      (measure_mono fun y hy => lt_of_lt_of_le (half_lt_self hx) (mem_Ici.1 hy))
  set G : ℝ → ℝ := fun x => (ϖ (Ici x)).toReal with hG
  set M : ℝ → ℝ := fun x => (m (Ici x)).toReal with hM
  have hM0 : ∀ x, 0 ≤ M x := fun x => ENNReal.toReal_nonneg
  have hG0 : ∀ x, 0 ≤ G x := fun x => ENNReal.toReal_nonneg
  -- the identity of the tails
  have hid : ∀ x : ℝ, 0 < x → ∀ t ∈ Icc 1 q, G (x / t) = G x + Real.logb q t * M x := by
    intro x hx t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
    have e := congrArg (fun ν : Measure ℝ => ν (Ici x)) ((hT t ht0).symm.trans (hs t ht))
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at e
    rw [Measure.map_apply (measurable_const_mul t) measurableSet_Ici] at e
    have hpre : (fun v => t * v) ⁻¹' Ici x = Ici (x / t) := by
      ext v
      simp only [mem_preimage, mem_Ici, div_le_iff₀ ht0, mul_comm]
    rw [hpre] at e
    have e2 := congrArg ENNReal.toReal e
    rw [ENNReal.toReal_add (hϖfin x hx) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmfin' x hx)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.logb_nonneg hq ht.1)] at e2
    exact e2
  have hq0 : 0 < q := by linarith
  have hidq : ∀ x : ℝ, 0 < x → G (x / q) = G x + M x := fun x hx => by
    rw [hid x hx q ⟨hq.le, le_rfl⟩, Real.logb_self_eq_one hq, one_mul]
  -- `M(x/s) = M(x)` for `s ∈ [1,q)`
  have hMs : ∀ x : ℝ, 0 < x → ∀ s : ℝ, 1 ≤ s → s < q → M (x / s) = M x := by
    intro x hx s hs1 hsq
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
    have hqs : q / s ∈ Icc 1 q := ⟨(one_le_div hs0).2 hsq.le, div_le_self hq0.le hs1⟩
    have e1 := hid (x / s) (div_pos hx hs0) (q / s) hqs
    have e2 := hid x hx s ⟨hs1, hsq.le⟩
    have e3 := hidq x hx
    have hxx : x / s / (q / s) = x / q := by field_simp
    rw [hxx, e3, e2, Real.logb_div hq0.ne' hs0.ne', Real.logb_self_eq_one hq] at e1
    have hl : Real.logb q s < 1 := by
      rw [← Real.logb_self_eq_one hq]
      exact Real.logb_lt_logb hq hs0 hsq
    have : (1 - Real.logb q s) * (M x - M (x / s)) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left (by linarith)
    linarith
  -- `M(xq) = M(x)`
  have hMq : ∀ x : ℝ, 0 < x → M (x * q) = M x := by
    intro x hx
    have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0.le
    have hs1 : 1 ≤ Real.sqrt q := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hq.le
    have hs0 : 0 < Real.sqrt q := by linarith
    have hslt : Real.sqrt q < q := by nlinarith
    have e1 := hMs (x * q) (mul_pos hx hq0) _ hs1 hslt
    have e2 := hMs (x * Real.sqrt q) (mul_pos hx hs0) _ hs1 hslt
    have h1 : x * q / Real.sqrt q = x * Real.sqrt q := by
      field_simp
      nlinarith
    have h2 : x * Real.sqrt q / Real.sqrt q = x := by field_simp
    rw [h1] at e1
    rw [h2] at e2
    rw [← e1, e2]
  -- `G(x) = G(xqⁿ) + n M(x)`
  have hGn : ∀ x : ℝ, 0 < x → ∀ n : ℕ, G x = G (x * q ^ n) + n * M x := by
    intro x hx n
    induction n with
    | zero => simp
    | succ n ih =>
      have hxn : 0 < x * q ^ n := mul_pos hx (pow_pos hq0 n)
      have e := hidq (x * q ^ (n + 1)) (mul_pos hx (pow_pos hq0 _))
      have h1 : x * q ^ (n + 1) / q = x * q ^ n := by
        rw [pow_succ]
        field_simp
      have hMn : ∀ k : ℕ, M (x * q ^ k) = M x := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [pow_succ, ← mul_assoc, hMq _ (mul_pos hx (pow_pos hq0 k)), ihk]
      rw [h1, hMn] at e
      rw [ih, e]
      push_cast
      ring
  -- so `M = 0`
  have hMzero : ∀ x : ℝ, 0 < x → M x = 0 := by
    intro x hx
    by_contra hne
    have hpos : 0 < M x := lt_of_le_of_ne (hM0 x) (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (G x / M x)
    have e := hGn x hx n
    have := hG0 (x * q ^ n)
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have hmIci : ∀ x : ℝ, 0 < x → m (Ici x) = 0 := fun x hx =>
    ((ENNReal.toReal_eq_zero_iff _).1 (hMzero x hx)).resolve_right (hmfin' x hx)
  have hIoi : m (Ioi 0) = 0 := by
    have hU : Ioi (0 : ℝ) = ⋃ n : ℕ, Ici (1 / ((n : ℝ) + 1)) := by
      ext x
      simp only [mem_Ioi, mem_iUnion, mem_Ici]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
        exact ⟨n, hn.le⟩
      · rintro ⟨n, hn⟩
        exact lt_of_lt_of_le (by positivity) hn
    rw [hU]
    exact measure_iUnion_null fun n => hmIci _ (by positivity)
  rw [← Measure.measure_univ_eq_zero, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact measure_union_null hmIic hIoi

end Pyramids
