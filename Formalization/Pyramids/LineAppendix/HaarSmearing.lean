/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.StrataCylinderJump

/-!
# `lem:haar-smearing-injective`

Blueprint: `blueprint/src/parts/A1-line.tex`, `lem:haar-smearing-injective`. Wave 3c: the
declaration `haar_smearing_injective` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in
statement.

## The route

* **σ-finiteness.** `ρ₁, ρ₂` are null on `(-∞,0]` and finite on every `[x,∞)`, `x > 0`, so they
  are σ-finite (`sigmaFinite_of_Ioi`) and the product `η ⊗ ρᵢ` is the product measure.
* **The smearing has a density.** By Tonelli and the substitution `v = rθ` at fixed `r > 0`
  (`lintegral_logHaar_comp_mul`), the image of `η ⊗ ρ` under `(θ, r) ↦ rθ` is
  `ρ((v/q, v]) dv/(ℓv)` (`map_haarPhase_prod_mul_apply`). The density is measurable
  (`measurable_measure_Ioc_div`), and `dv/(ℓv)` is σ-finite, so equal images give
  `ρ₁((v/q, v]) = ρ₂((v/q, v])` for `dv/(ℓv)`-almost every `v`.
* **The tails.** For `x > 0`, `(x,∞)` is the disjoint union of the `(qⁿx, qⁿ⁺¹x]`, `n ≥ 0`, so
  `ρ((x,∞)) = ∑ₙ ρ((qⁿ⁺¹x/q, qⁿ⁺¹x])` (`measure_Ioi_eq_tsum_Ioc`). The dilations by `qⁿ⁺¹`
  preserve `dv/(ℓv)` (`map_logHaar_mul`), so the tails agree for almost every `x`. This replaces the
  print's differences `δ` and their vanishing at infinity: countable additivity does it at once.
* **Everywhere.** The tail `x ↦ ρ((x,∞))` is the supremum of its values to the right of `x`, and
  every interval `(x, x + 1/(n+1))` has positive `dv/(ℓv)`-measure, so it holds a point where the
  tails agree; so the tails agree at every `x > 0`.
* **The measures.** On `(ε,∞)` the restrictions are finite and agree on the π-system of the
  `(a,∞)`, which generates the Borel sets; `(0,∞)` is the increasing union of the `(1/(n+1),∞)`,
  and both measures are carried by it.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter
open scoped ENNReal

/-- The set `{(r, v) : v/q < r ≤ v}`. -/
theorem measurableSet_Ioc_div_pair (q : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.2 / q < p.1 ∧ p.1 ≤ p.2} :=
  (measurableSet_lt (by fun_prop) measurable_fst).inter (measurableSet_le measurable_fst
    measurable_snd)

/-- `v ↦ ρ((v/q, v])` is measurable for s-finite `ρ`. -/
theorem measurable_measure_Ioc_div (q : ℝ) (ρ : Measure ℝ) [SFinite ρ] :
    Measurable fun v => ρ (Ioc (v / q) v) := by
  have h := (measurable_one.indicator (measurableSet_Ioc_div_pair q)).lintegral_prod_left'
    (μ := ρ)
  convert h using 1 with v
  funext v
  rw [← lintegral_indicator_one measurableSet_Ioc]
  rfl

/-- **The Haar smearing of `ρ` has the density `ρ((v/q, v])` against `dv/(ℓv)`**: for `ρ`
s-finite and null on `(-∞,0]`, the image of `η ⊗ ρ` under `(θ, r) ↦ rθ` gives a Borel set `A`
the mass `∫_A ρ((v/q, v]) dv/(ℓv)`. -/
theorem map_haarPhase_prod_mul_apply {q : ℝ} (hq0 : 0 < q) (ρ : Measure ℝ) [SFinite ρ]
    (h0 : ρ (Iic 0) = 0) {A : Set ℝ} (hA : MeasurableSet A) :
    ((haarPhase q).prod ρ).map (fun p => p.2 * p.1) A =
      ∫⁻ v in A, ρ (Ioc (v / q) v) ∂(logHaar q) := by
  have hf : Measurable fun p : ℝ × ℝ => p.2 * p.1 := by fun_prop
  set S : Set (ℝ × ℝ) := {p | p.2 ∈ A ∧ p.2 / q < p.1 ∧ p.1 ≤ p.2} with hSdef
  have hS : MeasurableSet S := (measurable_snd hA).inter (measurableSet_Ioc_div_pair q)
  -- Tonelli on `η ⊗ ρ`
  rw [← lintegral_indicator_one hA, lintegral_map (measurable_one.indicator hA) hf,
    lintegral_prod_symm' (fun p : ℝ × ℝ => A.indicator 1 (p.2 * p.1))
      ((measurable_one.indicator hA).comp hf)]
  -- the substitution `v = rθ` at fixed `r > 0`
  have hinner : ∀ᵐ r ∂ρ, ∫⁻ θ, A.indicator 1 (r * θ) ∂(haarPhase q) =
      ∫⁻ v, S.indicator 1 (r, v) ∂(logHaar q) := by
    filter_upwards [ae_pos_of_Iic_zero h0] with r hr
    have hH : Measurable fun v => S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (r, v) :=
      (measurable_one.indicator hS).comp measurable_prodMk_left
    rw [← lintegral_logHaar_comp_mul q hr hH, haarPhase_eq_restrict,
      ← lintegral_indicator measurableSet_Ico]
    refine lintegral_congr fun θ => ?_
    have hiff : (r, r * θ) ∈ S ↔ θ ∈ Ico 1 q ∧ r * θ ∈ A := by
      have e1 : r * θ / q < r ↔ θ < q := by
        rw [div_lt_iff₀ hq0]
        exact ⟨fun h => lt_of_mul_lt_mul_left h hr.le, fun h => mul_lt_mul_of_pos_left h hr⟩
      have e2 : r ≤ r * θ ↔ 1 ≤ θ :=
        ⟨fun h => le_of_mul_le_mul_left (by rwa [mul_one]) hr,
          fun h => le_mul_of_one_le_right hr.le h⟩
      simp only [hSdef, mem_setOf_eq, mem_Ico, e1, e2]
      tauto
    by_cases hθ : θ ∈ Ico 1 q ∧ r * θ ∈ A
    · rw [indicator_of_mem hθ.1, indicator_of_mem hθ.2, indicator_of_mem (hiff.2 hθ)]
      rfl
    · rw [indicator_of_notMem (fun h => hθ (hiff.1 h))]
      by_cases h1 : θ ∈ Ico 1 q
      · rw [indicator_of_mem h1, indicator_of_notMem (fun h => hθ ⟨h1, h⟩)]
      · rw [indicator_of_notMem h1]
  rw [lintegral_congr_ae hinner, lintegral_lintegral_swap
    (f := fun r v => S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (r, v))
    (measurable_one.indicator hS).aemeasurable, ← lintegral_indicator hA]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ A
  · rw [indicator_of_mem hv, ← lintegral_indicator_one measurableSet_Ioc]
    refine lintegral_congr fun r => ?_
    simp only [indicator, hSdef, mem_setOf_eq, mem_Ioc, hv, true_and]
    rfl
  · rw [indicator_of_notMem hv]
    refine (lintegral_congr fun r => ?_).trans lintegral_zero
    simp [indicator, hSdef, hv]

/-- **The tail as a series of the octave masses**: for `x > 0`,
`ρ((x,∞)) = ∑ₙ ρ((qⁿ⁺¹x/q, qⁿ⁺¹x])`. -/
theorem measure_Ioi_eq_tsum_Ioc {q : ℝ} (hq : 1 < q) (ρ : Measure ℝ) {x : ℝ} (hx : 0 < x) :
    ρ (Ioi x) = ∑' n : ℕ, ρ (Ioc (q ^ (n + 1) * x / q) (q ^ (n + 1) * x)) := by
  have hq0 : 0 < q := by linarith
  have e : ∀ n : ℕ, q ^ (n + 1) * x / q = q ^ n * x := by
    intro n
    rw [pow_succ]
    field_simp
  simp_rw [e]
  have hmono : Monotone fun n : ℕ => q ^ n * x :=
    fun a b hab => mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq.le hab) hx.le
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => Ioc (q ^ n * x) (q ^ (n + 1) * x)) :=
    hmono.pairwise_disjoint_on_Ioc_succ
  rw [← measure_iUnion hdisj fun _ => measurableSet_Ioc]
  congr 1
  ext y
  simp only [mem_Ioi, mem_iUnion, mem_Ioc]
  constructor
  · intro hy
    classical
    have hex : ∃ n : ℕ, y ≤ q ^ (n + 1) * x := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (y / x) hq
      refine ⟨n, ?_⟩
      rw [div_lt_iff₀ hx] at hn
      exact hn.le.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq.le (Nat.le_succ n))
        hx.le)
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
    rcases hk : Nat.find hex with _ | k
    · rwa [pow_zero, one_mul]
    · have := Nat.find_min hex (show k < Nat.find hex by omega)
      exact lt_of_not_ge this
  · rintro ⟨n, h1, _⟩
    exact lt_of_le_of_lt (le_mul_of_one_le_left hx.le (one_le_pow₀ hq.le)) h1

/-- **`lem:haar-smearing-injective`.** For measures `ρ₁, ρ₂` on `(0,∞)` finite on every
`[x,∞)`, `x > 0`: if the images of `η ⊗ ρ₁` and `η ⊗ ρ₂` under `(θ, r) ↦ rθ` coincide, then
`ρ₁ = ρ₂`. -/
theorem haar_smearing_injective {q : ℝ} (hq : 1 < q) (ρ₁ ρ₂ : Measure ℝ) (h₁ : ρ₁ (Iic 0) = 0)
    (h₂ : ρ₂ (Iic 0) = 0) (hf₁ : ∀ x : ℝ, 0 < x → ρ₁ (Ici x) ≠ ⊤)
    (hf₂ : ∀ x : ℝ, 0 < x → ρ₂ (Ici x) ≠ ⊤)
    (heq : ((haarPhase q).prod ρ₁).map (fun p => p.2 * p.1) =
      ((haarPhase q).prod ρ₂).map (fun p => p.2 * p.1)) : ρ₁ = ρ₂ := by
  have hq0 : 0 < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos hq
  have hIoi₁ : ∀ x : ℝ, 0 < x → ρ₁ (Ioi x) ≠ ⊤ :=
    fun x hx => ne_top_of_le_ne_top (hf₁ x hx) (measure_mono Ioi_subset_Ici_self)
  have hIoi₂ : ∀ x : ℝ, 0 < x → ρ₂ (Ioi x) ≠ ⊤ :=
    fun x hx => ne_top_of_le_ne_top (hf₂ x hx) (measure_mono Ioi_subset_Ici_self)
  haveI : SigmaFinite ρ₁ := sigmaFinite_of_Ioi h₁ hIoi₁
  haveI : SigmaFinite ρ₂ := sigmaFinite_of_Ioi h₂ hIoi₂
  haveI : SigmaFinite (logHaar q) := by rw [logHaar]; infer_instance
  -- the octave masses agree almost everywhere
  have hG : (fun v => ρ₁ (Ioc (v / q) v)) =ᵐ[logHaar q] fun v => ρ₂ (Ioc (v / q) v) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (measurable_measure_Ioc_div q ρ₁)
      (measurable_measure_Ioc_div q ρ₂) fun A hA _ => ?_
    rw [← map_haarPhase_prod_mul_apply hq0 ρ₁ h₁ hA, ← map_haarPhase_prod_mul_apply hq0 ρ₂ h₂ hA,
      heq]
  -- the tails agree almost everywhere
  have hT : ∀ᵐ x ∂(logHaar q), 0 < x → ρ₁ (Ioi x) = ρ₂ (Ioi x) := by
    have hn : ∀ n : ℕ, ∀ᵐ x ∂(logHaar q), ρ₁ (Ioc (q ^ (n + 1) * x / q) (q ^ (n + 1) * x)) =
        ρ₂ (Ioc (q ^ (n + 1) * x / q) (q ^ (n + 1) * x)) := by
      intro n
      have hc : 0 < q ^ (n + 1) := pow_pos hq0 _
      have h := hG
      rw [EventuallyEq, ← map_logHaar_mul q hc] at h
      exact ae_of_ae_map (measurable_const_mul _).aemeasurable h
    filter_upwards [ae_all_iff.2 hn] with x hx hxpos
    rw [measure_Ioi_eq_tsum_Ioc hq ρ₁ hxpos, measure_Ioi_eq_tsum_Ioc hq ρ₂ hxpos]
    exact tsum_congr hx
  -- every interval `(x, x + ε)` has positive `dv/(ℓv)`-measure
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ logHaar q := by
    refine withDensity_absolutelyContinuous' (measurable_logHaar_density q).aemeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (ENNReal.ofReal_pos.2 (one_div_pos.2 (mul_pos hl hy))).ne'
  -- the tails agree everywhere on `(0,∞)`
  have hT' : ∀ x : ℝ, 0 < x → ρ₁ (Ioi x) = ρ₂ (Ioi x) := by
    intro x hx
    have hex : ∀ n : ℕ, ∃ y ∈ Ioo x (x + 1 / ((n : ℝ) + 1)), ρ₁ (Ioi y) = ρ₂ (Ioi y) := by
      intro n
      have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have hpos : logHaar q (Ioo x (x + 1 / ((n : ℝ) + 1))) ≠ 0 := by
        intro h0
        have h := hac h0
        rw [Measure.restrict_apply measurableSet_Ioo,
          inter_eq_left.2 (show Ioo x (x + 1 / ((n : ℝ) + 1)) ⊆ Ioi 0 from
            fun y hy => lt_trans hx hy.1), Real.volume_Ioo,
          ENNReal.ofReal_eq_zero] at h
        linarith
      haveI := ae_restrict_neBot.2 hpos
      obtain ⟨y, hy, hyeq⟩ := Filter.Eventually.exists
        (f := ae ((logHaar q).restrict (Ioo x (x + 1 / ((n : ℝ) + 1)))))
        ((ae_restrict_mem measurableSet_Ioo).and (ae_restrict_of_ae hT))
      exact ⟨y, hy, hyeq (lt_trans hx hy.1)⟩
    choose y hy hyeq using hex
    have hmono : Monotone fun n : ℕ => Ioi (x + 1 / ((n : ℝ) + 1)) := by
      intro a b hab
      refine Ioi_subset_Ioi ?_
      gcongr
    have hU : Ioi x = ⋃ n : ℕ, Ioi (x + 1 / ((n : ℝ) + 1)) := by
      ext z
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have key : ∀ ρ : Measure ℝ, ρ (Ioi x) = ⨆ n, ρ (Ioi (y n)) := by
      intro ρ
      refine le_antisymm ?_ (iSup_le fun n => measure_mono (Ioi_subset_Ioi (hy n).1.le))
      rw [hU, hmono.measure_iUnion]
      exact iSup_mono fun n => measure_mono (Ioi_subset_Ioi (hy n).2.le)
    rw [key ρ₁, key ρ₂]
    exact iSup_congr hyeq
  -- the restrictions to `(ε,∞)` agree
  have hres : ∀ ε : ℝ, 0 < ε → ρ₁.restrict (Ioi ε) = ρ₂.restrict (Ioi ε) := by
    intro ε hε
    haveI : IsFiniteMeasure (ρ₁.restrict (Ioi ε)) := isFiniteMeasure_restrict.2 (hIoi₁ ε hε)
    refine ext_of_generate_finite (range Ioi)
      (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ)) isPiSystem_Ioi ?_ ?_
    · rintro _ ⟨a, rfl⟩
      rw [Measure.restrict_apply measurableSet_Ioi, Measure.restrict_apply measurableSet_Ioi,
        Ioi_inter_Ioi]
      exact hT' _ (lt_sup_of_lt_right hε)
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      exact hT' ε hε
  -- both measures are carried by `(0,∞) = ⋃ₙ (1/(n+1),∞)`
  have hmono : Monotone fun n : ℕ => Ioi (1 / ((n : ℝ) + 1)) := by
    intro a b hab
    refine Ioi_subset_Ioi ?_
    gcongr
  have hU : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1)) := by
    ext z
    simp only [mem_Ioi, mem_iUnion]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hz
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      exact lt_trans (by positivity) hn
  have e₁ : ρ₁.restrict (Ioi 0) = ρ₁ :=
    Measure.restrict_eq_self_of_ae_mem (ae_pos_of_Iic_zero h₁)
  have e₂ : ρ₂.restrict (Ioi 0) = ρ₂ :=
    Measure.restrict_eq_self_of_ae_mem (ae_pos_of_Iic_zero h₂)
  rw [← e₁, ← e₂]
  ext s hs
  rw [hU, Measure.restrict_iUnion_apply_eq_iSup hmono.directed_le hs,
    Measure.restrict_iUnion_apply_eq_iSup hmono.directed_le hs]
  exact iSup_congr fun n => by rw [hres _ (by positivity)]

end Pyramids
