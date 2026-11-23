/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.QCinRepr

/-!
# `prop:strata-cylinder-coordinates-q-cin`(1): the extreme rays of `𝒦_q`

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:strata-cylinder-coordinates-q-cin`. Wave 3a:
`qcin_1_rays` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in statement and name.

## The route

Through the representation `ψ ↔ (a, κ)` of `QCinRepr.lean`, which is additive, positively
homogeneous and unique (`qCinRepr_add`, `qCinRepr_smul`, `qCinRepr_unique`), and every `(a, κ)`
whose spread is a Lévy measure represents an element of `𝒦_q` (`qCinFun_spec`).

* **The rays are extreme.** A decomposition `y + z` of `cω²` or of `cE^{(q)}_τ` in `𝒦_q` is a
  decomposition of its representation, `(c, 0)` or `(0, cδ_τ)`. A measure below `cδ_τ` is a multiple
  of `δ_τ` (`eq_smul_dirac_of_compl_null`), so `y` is a multiple of the ray.
* **Every extreme ray is one of them.** Let `ψ` be extreme, with representation `(a, κ)`. Splitting
  `κ = κ|_B + κ|_{Bᶜ}` and comparing representations shows that every Borel set is `κ`-null or
  `κ`-conull; such a measure is a multiple of a point mass (`eq_smul_dirac_of_zero_one`, at the
  point `inf {x : κ(x,∞) = 0}`). Splitting off `aω²` shows `a = 0` or `κ = 0`. The point is positive
  as `κ` is carried by `(0,∞)`, and the mass is finite as `ψ(1) < ∞` and `E^{(q)}_τ(1) > 0`.

This is the argument the proof of record cites from `thm:knot-atom-cascades`(3): the extreme rays
of a cone of measures are the point masses.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair IsSymLevyExponent)
open scoped Topology ENNReal NNReal

/-! ## Measures carried by one point -/

/-- A measure null off `{τ}` is `κ{τ} δ_τ`. -/
theorem eq_smul_dirac_of_compl_null {κ : Measure ℝ} {τ : ℝ} (hτ : κ {τ}ᶜ = 0) :
    κ = κ {τ} • Measure.dirac τ := by
  ext A hA
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul,
    ← measure_inter_add_sdiff A (measurableSet_singleton τ)]
  have h2 : κ (A \ {τ}) = 0 := measure_mono_null (fun x hx => hx.2) hτ
  rw [h2, add_zero]
  by_cases hτA : τ ∈ A
  · rw [inter_eq_right.2 (singleton_subset_iff.2 hτA), indicator_of_mem hτA, Pi.one_apply,
      mul_one]
  · rw [inter_singleton_eq_empty.2 hτA, measure_empty, indicator_of_notMem hτA, mul_zero]

/-- **A measure on `ℝ` for which every Borel set is null or conull is a multiple of a point
mass**, at `τ = inf {x : κ(x,∞) = 0}`. -/
theorem eq_smul_dirac_of_zero_one {κ : Measure ℝ}
    (h : ∀ B : Set ℝ, MeasurableSet B → κ B = 0 ∨ κ Bᶜ = 0) :
    ∃ τ : ℝ, κ = κ {τ} • Measure.dirac τ := by
  have hzero : κ univ = 0 → ∃ τ : ℝ, κ = κ {τ} • Measure.dirac τ := by
    intro h0
    have : κ = 0 := Measure.measure_univ_eq_zero.1 h0
    exact ⟨0, by rw [this]; simp⟩
  set S : Set ℝ := {x | κ (Ioi x) = 0} with hS
  by_cases hne : S.Nonempty
  swap
  · apply hzero
    have hIic : ∀ x : ℝ, κ (Iic x) = 0 := fun x => by
      rcases h (Iic x) measurableSet_Iic with h1 | h1
      · exact h1
      · exact absurd ⟨x, by rw [compl_Iic] at h1; exact h1⟩ hne
    exact measure_mono_null (fun x _ => mem_iUnion.2 ⟨⌈x⌉₊, mem_Iic.2 (Nat.le_ceil x)⟩)
      (measure_iUnion_null fun n : ℕ => hIic n)
  by_cases hbdd : BddBelow S
  swap
  · apply hzero
    have hIoi : ∀ x : ℝ, κ (Ioi x) = 0 := fun x => by
      obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.1 hbdd x
      exact measure_mono_null (Ioi_subset_Ioi hyx.le) hy
    refine measure_mono_null (fun x _ => mem_iUnion.2 ⟨⌈-x⌉₊, ?_⟩)
      (measure_iUnion_null fun n : ℕ => hIoi (-(n : ℝ) - 1))
    have := Nat.le_ceil (-x)
    rw [mem_Ioi]
    linarith
  set τ := sInf S with hτ
  have hIoi : κ (Ioi τ) = 0 := by
    have hn : ∀ n : ℕ, κ (Ioi (τ + 1 / ((n : ℝ) + 1))) = 0 := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne
        (show sInf S < τ + 1 / ((n : ℝ) + 1) by rw [← hτ]; linarith)
      exact measure_mono_null (Ioi_subset_Ioi hsx.le) hs
    refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hn)
    have hx' : 0 < x - τ := sub_pos.2 hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx'
    exact mem_iUnion.2 ⟨n, mem_Ioi.2 (by linarith)⟩
  have hIio : κ (Iio τ) = 0 := by
    have hIic : ∀ x : ℝ, x < τ → κ (Iic x) = 0 := fun x hx => by
      have hxS : x ∉ S := notMem_of_lt_csInf hx hbdd
      rcases h (Iic x) measurableSet_Iic with h1 | h1
      · exact h1
      · exact absurd (by rw [compl_Iic] at h1; exact h1) hxS
    refine measure_mono_null (fun x hx => ?_)
      (measure_iUnion_null fun n : ℕ => hIic (τ - 1 / ((n : ℝ) + 1))
        (by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]))
    have hx' : 0 < τ - x := sub_pos.2 hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx'
    exact mem_iUnion.2 ⟨n, mem_Iic.2 (by linarith)⟩
  refine ⟨τ, eq_smul_dirac_of_compl_null (measure_mono_null (fun x hx => ?_)
    (measure_union_null hIio hIoi))⟩
  rcases lt_or_gt_of_ne (show x ≠ τ from hx) with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

/-! ## The representation, as a map -/

theorem isInKq_symLevy {q : ℝ} {ψ : ℝ → ℝ} (h : IsInKq q ψ) : IsSymLevyExponent ψ :=
  let ⟨P, hP, _⟩ := h
  ⟨P, hP⟩

theorem isInKq_nonneg {q : ℝ} {ψ : ℝ → ℝ} (h : IsInKq q ψ) (ω : ℝ) : 0 ≤ ψ ω :=
  isSymLevyExponent_nonneg (isInKq_symLevy h) ω

/-- Two functions with the same representation are equal. -/
theorem eq_of_qCinRepr {q : ℝ} {ψ ψ' : ℝ → ℝ} {a a' : ℝ} {κ κ' : Measure ℝ}
    (h : IsQCinRepr q ψ a κ) (h' : IsQCinRepr q ψ' a' κ') (ha : a = a') (hκ : κ = κ')
    (hψ : ∀ ω, 0 ≤ ψ ω) (hψ' : ∀ ω, 0 ≤ ψ' ω) : ψ = ψ' := by
  subst ha hκ
  funext ω
  exact (ENNReal.ofReal_eq_ofReal_iff (hψ ω) (hψ' ω)).1 ((h.2.2 ω).trans (h'.2.2 ω).symm)

theorem qCinRepr_add {q : ℝ} {ψ ψ' : ℝ → ℝ} {a a' : ℝ} {κ κ' : Measure ℝ}
    (h : IsQCinRepr q ψ a κ) (h' : IsQCinRepr q ψ' a' κ') (hψ : ∀ ω, 0 ≤ ψ ω)
    (hψ' : ∀ ω, 0 ≤ ψ' ω) : IsQCinRepr q (ψ + ψ') (a + a') (κ + κ') := by
  refine ⟨add_nonneg h.1 h'.1, by rw [Measure.add_apply, h.2.1, h'.2.1, add_zero], fun ω => ?_⟩
  rw [Pi.add_apply, ENNReal.ofReal_add (hψ ω) (hψ' ω), h.2.2 ω, h'.2.2 ω, lintegral_add_measure,
    add_mul, ENNReal.ofReal_add (mul_nonneg h.1 (sq_nonneg ω)) (mul_nonneg h'.1 (sq_nonneg ω))]
  ring

theorem qCinRepr_smul {q : ℝ} {ψ : ℝ → ℝ} {a : ℝ} {κ : Measure ℝ} (h : IsQCinRepr q ψ a κ)
    {c : ℝ} (hc : 0 ≤ c) : IsQCinRepr q (c • ψ) (c * a) (ENNReal.ofReal c • κ) := by
  refine ⟨mul_nonneg hc h.1, by rw [Measure.smul_apply, h.2.1, smul_zero], fun ω => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul hc, h.2.2 ω, lintegral_smul_measure,
    smul_eq_mul, mul_add, ← ENNReal.ofReal_mul hc, mul_assoc]

theorem qCinRepr_sq (q : ℝ) : IsQCinRepr q (fun ω => ω ^ 2) 1 0 :=
  ⟨zero_le_one, by simp, fun ω => by simp⟩

theorem qCinRepr_ray (q : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    IsQCinRepr q (qCinRay q τ) 0 (Measure.dirac τ) := by
  refine ⟨le_rfl, ?_, fun ω => ?_⟩
  · rw [Measure.dirac_apply' _ measurableSet_Iic,
      indicator_of_notMem (show τ ∉ Iic (0 : ℝ) from not_le.2 hτ)]
  · rw [lintegral_dirac, zero_mul, ENNReal.ofReal_zero, zero_add]

/-- **The function of a representation**, `aω² + ∫ E^{(q)}_τ(ω) κ(dτ)`. -/
noncomputable def qCinFun (q a : ℝ) (κ : Measure ℝ) (ω : ℝ) : ℝ :=
  (ENNReal.ofReal (a * ω ^ 2) + ∫⁻ τ, ENNReal.ofReal (qCinRay q τ ω) ∂κ).toReal

/-- Every `(a, κ)` whose spread is a Lévy measure represents an element of `𝒦_q`. -/
theorem qCinFun_spec {q a : ℝ} (hq : 1 < q) {κ : Measure ℝ} (ha : 0 ≤ a) (hκ : κ (Iic 0) = 0)
    (hint : ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(qSpread q κ) ≠ ⊤) :
    IsInKq q (qCinFun q a κ) ∧ IsQCinRepr q (qCinFun q a κ) a κ := by
  set P : SymLevyPair := ⟨a, qSpread q κ, ha, qSpread_Iic (by linarith) hκ, hint⟩ with hP
  have hL : ∀ ω, ENNReal.ofReal (a * ω ^ 2) + ∫⁻ τ, ENNReal.ofReal (qCinRay q τ ω) ∂κ =
      P.exponentL ω := by
    intro ω
    rw [SymLevyPair.exponentL, lintegral_qCinRay_eq hq]
  refine ⟨⟨P, fun ω => ?_, qSpread_le_map (by linarith) κ⟩, ha, hκ, fun ω => ?_⟩
  · rw [qCinFun, hL ω]
    rfl
  · rw [qCinFun, ENNReal.ofReal_toReal (by rw [hL ω]; exact P.exponentL_ne_top ω)]

/-! ## `prop:strata-cylinder-coordinates-q-cin`(1), the extreme rays -/

/-- **`prop:strata-cylinder-coordinates-q-cin`(1), the extreme rays** of `𝒦_q` are those of `ω²`
and of the `E^{(q)}_τ`, `τ > 0`. -/
theorem qcin_1_rays {q : ℝ} (hq : 1 < q) :
    ∀ ψ : ℝ → ℝ, IsExtremeRayIn {ψ | IsInKq q ψ} ψ ↔
      ∃ c : ℝ≥0, c ≠ 0 ∧ (ψ = c • (fun ω => ω ^ 2) ∨ ∃ τ : ℝ, 0 < τ ∧ ψ = c • qCinRay q τ) := by
  have hcone := qcin_1_cone hq
  have nnsmul : ∀ (c : ℝ≥0) (f : ℝ → ℝ), c • f = (c : ℝ) • f := fun c f => rfl
  intro ψ
  constructor
  · rintro ⟨hψK, hψ0, hext⟩
    have hψK' : IsInKq q ψ := hψK
    have hND := isInKq_symLevy hψK'
    obtain ⟨⟨a, κ, hrep⟩, -⟩ := qcin_1_repr hq ψ hψK'
    have hint := qSpread_levy_of_qCinRepr hq hND hrep
    -- a splitting of the representation splits `ψ`, and the summand is a multiple of `ψ`
    have split : ∀ (a1 a2 : ℝ) (κ1 κ2 : Measure ℝ), 0 ≤ a1 → 0 ≤ a2 → a1 + a2 = a →
        κ1 + κ2 = κ → ∃ c : ℝ≥0, a1 = c * a ∧ κ1 = ENNReal.ofReal c • κ := by
      intro a1 a2 κ1 κ2 ha1 ha2 hsum hκsum
      have hle1 : κ1 ≤ κ := hκsum ▸ Measure.le_add_right le_rfl
      have hle2 : κ2 ≤ κ := hκsum ▸ Measure.le_add_left le_rfl
      have hfin : ∀ κ' : Measure ℝ, κ' ≤ κ → κ' (Iic 0) = 0 ∧
          ∫⁻ v, ENNReal.ofReal (min 1 (v ^ 2)) ∂(qSpread q κ') ≠ ⊤ := fun κ' hle =>
        ⟨nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hle _).trans hrep.2.1.le),
          ne_top_of_le_ne_top hint (lintegral_mono' (qSpread_mono q hle) le_rfl)⟩
      obtain ⟨hy, hyr⟩ := qCinFun_spec hq ha1 (hfin κ1 hle1).1 (hfin κ1 hle1).2
      obtain ⟨hz, hzr⟩ := qCinFun_spec hq ha2 (hfin κ2 hle2).1 (hfin κ2 hle2).2
      have hyz : qCinFun q a1 κ1 + qCinFun q a2 κ2 = ψ :=
        eq_of_qCinRepr (qCinRepr_add hyr hzr (isInKq_nonneg hy) (isInKq_nonneg hz)) hrep hsum
          hκsum (fun ω => add_nonneg (isInKq_nonneg hy ω) (isInKq_nonneg hz ω))
          (isInKq_nonneg hψK')
      obtain ⟨c, hc⟩ := hext _ hy _ hz hyz
      have hcr : IsQCinRepr q (qCinFun q a1 κ1) (c * a) (ENNReal.ofReal c • κ) := by
        rw [hc, nnsmul]
        exact qCinRepr_smul hrep c.2
      obtain ⟨h1, h2⟩ := qCinRepr_unique hq (isInKq_symLevy hy) hyr hcr
      exact ⟨c, h1, h2⟩
    -- every Borel set is null or conull
    have h01 : ∀ B : Set ℝ, MeasurableSet B → κ B = 0 ∨ κ Bᶜ = 0 := by
      intro B hB
      obtain ⟨c, -, hc⟩ := split 0 a (κ.restrict B) (κ.restrict Bᶜ) le_rfl hrep.1 (zero_add a)
        (Measure.restrict_add_restrict_compl hB)
      have e1 := congrArg (fun m : Measure ℝ => m Bᶜ) hc
      have e2 := congrArg (fun m : Measure ℝ => m B) hc
      simp only [Measure.restrict_apply hB.compl, Measure.restrict_apply hB, Measure.smul_apply,
        smul_eq_mul, compl_inter_self, inter_self, measure_empty] at e1 e2
      rcases mul_eq_zero.1 e1.symm with h | h
      · left
        rw [e2, h, zero_mul]
      · exact Or.inr h
    -- `a = 0` or `κ = 0`
    have ha0 : a = 0 ∨ κ = 0 := by
      obtain ⟨c, h1, h2⟩ := split a 0 0 κ hrep.1 le_rfl (add_zero a) (zero_add κ)
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        have hc1 : (c : ℝ) = 1 := by
          have : (c : ℝ) * a = 1 * a := by rw [← h1, one_mul]
          exact mul_right_cancel₀ ha this
        rw [hc1, ENNReal.ofReal_one, one_smul] at h2
        exact h2.symm
    rcases eq_or_ne κ 0 with hκ0 | hκ0
    · -- `ψ = aω²`
      have hψa : ψ = a • (fun ω : ℝ => ω ^ 2) :=
        eq_of_qCinRepr hrep (qCinRepr_smul (qCinRepr_sq q) hrep.1) (mul_one a).symm
          (by rw [hκ0, smul_zero]) (isInKq_nonneg hψK')
          (isInKq_nonneg (hcone.2.1 _ a hrep.1 hcone.2.2.1))
      have ha : a ≠ 0 := by
        rintro rfl
        apply hψ0
        rw [hψa, zero_smul]
      exact ⟨⟨a, hrep.1⟩, fun h => ha (NNReal.coe_eq_zero.2 h), Or.inl hψa⟩
    · -- `ψ = wE^{(q)}_τ`
      have ha : a = 0 := ha0.resolve_right hκ0
      obtain ⟨τ, hτκ⟩ := eq_smul_dirac_of_zero_one h01
      have hrep1 := hrep.2.2 1
      set w := κ {τ} with hw
      have hw0 : w ≠ 0 := by
        intro h
        apply hκ0
        rw [hτκ, h, zero_smul]
      have hτ : 0 < τ := by
        by_contra hτ
        have : κ (Iic 0) = w := by
          rw [hτκ, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iic,
            indicator_of_mem (show τ ∈ Iic (0 : ℝ) from not_lt.1 hτ), Pi.one_apply, smul_eq_mul,
            mul_one]
        exact hw0 (this.symm.trans hrep.2.1)
      rw [ha, hτκ, lintegral_smul_measure, lintegral_dirac, zero_mul, ENNReal.ofReal_zero,
        zero_add, smul_eq_mul] at hrep1
      have hwt : w ≠ ⊤ := by
        intro h
        rw [h, ENNReal.top_mul (by
          rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
          exact qCinRay_pos hq hτ.ne' one_ne_zero)] at hrep1
        exact ENNReal.ofReal_ne_top hrep1
      have hψE : ψ = w.toReal • qCinRay q τ :=
        eq_of_qCinRepr hrep (qCinRepr_smul (qCinRepr_ray q hτ) ENNReal.toReal_nonneg)
          (by rw [ha, mul_zero]) (by rw [hτκ, ENNReal.ofReal_toReal hwt]) (isInKq_nonneg hψK')
          (fun ω => mul_nonneg ENNReal.toReal_nonneg (qCinRay_nonneg q τ ω))
      refine ⟨⟨w.toReal, ENNReal.toReal_nonneg⟩, fun h => ?_, Or.inr ⟨τ, hτ, hψE⟩⟩
      have : w.toReal = 0 := NNReal.coe_eq_zero.2 h
      exact ((ENNReal.toReal_eq_zero_iff _).1 this).elim hw0 hwt
  · rintro ⟨c, hc0, hψ⟩
    have hc : (0 : ℝ) < c := lt_of_le_of_ne c.2 fun h => hc0 (NNReal.coe_eq_zero.1 h.symm)
    -- the representation of `ψ`, and `ψ ∈ 𝒦_q`
    obtain ⟨a0, κ0, hrep, hψK, hcases⟩ : ∃ (a0 : ℝ) (κ0 : Measure ℝ), IsQCinRepr q ψ a0 κ0 ∧
        IsInKq q ψ ∧ ((a0 = c ∧ κ0 = 0) ∨
          ∃ τ : ℝ, 0 < τ ∧ a0 = 0 ∧ κ0 = ENNReal.ofReal c • Measure.dirac τ) := by
      rcases hψ with rfl | ⟨τ, hτ, rfl⟩
      · refine ⟨c * 1, ENNReal.ofReal c • 0, ?_, ?_, Or.inl ⟨mul_one _, smul_zero _⟩⟩
        · rw [nnsmul]
          exact qCinRepr_smul (qCinRepr_sq q) c.2
        · rw [nnsmul]
          exact hcone.2.1 _ _ c.2 hcone.2.2.1
      · refine ⟨c * 0, ENNReal.ofReal c • Measure.dirac τ, ?_, ?_,
          Or.inr ⟨τ, hτ, mul_zero _, rfl⟩⟩
        · rw [nnsmul]
          exact qCinRepr_smul (qCinRepr_ray q hτ) c.2
        · rw [nnsmul]
          exact hcone.2.1 _ _ c.2 (hcone.2.2.2 τ hτ).1
    have hND := isInKq_symLevy hψK
    refine ⟨hψK, fun h0 => ?_, fun y hy z hz hyz => ?_⟩
    · -- `ψ ≠ 0`
      have hr0 : IsQCinRepr q ψ 0 0 := by
        rw [h0]
        exact ⟨le_rfl, by simp, fun ω => by simp⟩
      obtain ⟨ha, hκ⟩ := qCinRepr_unique hq hND hrep hr0
      rcases hcases with ⟨ha', -⟩ | ⟨τ, -, -, hκ'⟩
      · exact hc.ne' (ha' ▸ ha)
      · have h1 := congrArg (fun m : Measure ℝ => m univ) (hκ'.symm.trans hκ)
        simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Measure.coe_zero,
          Pi.zero_apply] at h1
        exact absurd (ENNReal.ofReal_eq_zero.1 h1) (not_le.2 hc)
    · have hy' : IsInKq q y := hy
      have hz' : IsInKq q z := hz
      obtain ⟨⟨ay, κy, hry⟩, -⟩ := qcin_1_repr hq y hy'
      obtain ⟨⟨az, κz, hrz⟩, -⟩ := qcin_1_repr hq z hz'
      have hsum := qCinRepr_add hry hrz (isInKq_nonneg hy') (isInKq_nonneg hz')
      rw [hyz] at hsum
      obtain ⟨ha, hκ⟩ := qCinRepr_unique hq hND hsum hrep
      have hκle : κy ≤ κ0 := hκ ▸ Measure.le_add_right le_rfl
      rcases hcases with ⟨ha0, hκ0⟩ | ⟨τ, -, ha0, hκ0⟩
      · -- `κy = 0`, and `y = (ay/c) ψ`
        have hκy : κy = 0 := le_antisymm (hκle.trans_eq hκ0) (Measure.zero_le _)
        have hay : 0 ≤ ay / c := div_nonneg hry.1 hc.le
        refine ⟨⟨ay / c, hay⟩, ?_⟩
        change y = (ay / c : ℝ) • ψ
        exact eq_of_qCinRepr hry (qCinRepr_smul hrep hay)
          (by rw [ha0, div_mul_cancel₀ _ hc.ne']) (by rw [hκy, hκ0, smul_zero])
          (isInKq_nonneg hy') (fun ω => mul_nonneg hay (isInKq_nonneg hψK ω))
      · -- `ay = 0`, `κy ≤ cδ_τ`, and `y = (κy{τ}/c) ψ`
        have hay0 : ay = 0 := by
          have : ay + az = 0 := ha.trans ha0
          linarith [hry.1, hrz.1]
        have hcompl : κy {τ}ᶜ = 0 := by
          refine nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hκle _).trans_eq ?_)
          rw [hκ0, Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton τ).compl,
            indicator_of_notMem (show τ ∉ ({τ}ᶜ : Set ℝ) from fun h => h rfl), smul_zero]
        have hκy := eq_smul_dirac_of_compl_null hcompl
        have hwle : κy {τ} ≤ ENNReal.ofReal c := by
          refine (Measure.le_iff'.1 hκle _).trans_eq ?_
          rw [hκ0, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton τ), smul_eq_mul,
            mul_one]
        set w := κy {τ} with hw
        have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwle
        have hd : 0 ≤ w.toReal / c := div_nonneg ENNReal.toReal_nonneg hc.le
        refine ⟨⟨w.toReal / c, hd⟩, ?_⟩
        change y = (w.toReal / c : ℝ) • ψ
        exact eq_of_qCinRepr hry (qCinRepr_smul hrep hd) (by rw [hay0, ha0, mul_zero])
          (by rw [hκy, hκ0, smul_smul, ← ENNReal.ofReal_mul hd, div_mul_cancel₀ _ hc.ne',
            ENNReal.ofReal_toReal hwt])
          (isInKq_nonneg hy') (fun ω => mul_nonneg hd (isInKq_nonneg hψK ω))

end Pyramids
