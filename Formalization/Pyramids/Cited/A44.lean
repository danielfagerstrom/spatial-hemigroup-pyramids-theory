/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Cited
import Pyramids.Cited.A39
import Pyramids.Cited.A42
import AffineHemigroup.TripletSum
import AffineHemigroup.PolarReading
import AffineHemigroup.AnisotropyBudget

/-!
# Ledger A44: semi-selfdecomposability by the Lévy measure (Sato, Thm. 15.8, p. 94)

Interface node `thm:cited-A44` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A44 of
`blueprint/AXIOMS.md`, cited from Sato, *Lévy Processes and Infinitely Divisible Distributions*,
Theorem 15.8, printed p. 94, formula (15.6).

A44 is not admitted, and **needs no axiom of its own**: Sato's proof uses only the
Lévy–Khintchine representation and the triplet of a linear image, which are this article's A39
(Sato, Thm. 8.1) and A42 (Sato, Prop. 11.10), both admitted on 2026-11-13. Write `μ_b` for the
image of `μ` under `x ↦ b⁻¹x`; by A42 at `U = b⁻¹I` it is infinitely divisible with triplet
`(b⁻²A, (b⁻¹)_*ν, γ')`, and `(b⁻¹)_*ν ≤ ν` is `ν ≤ D_bν` after the image under `x ↦ bx`.

* **Only if.** A residual `ρ` at `b` is infinitely divisible (the definition asks it); A39(i) gives
  it a triplet, the exponents of `μ_b` and `ρ` add to one of `μ`, and A39(ii) identifies the Lévy
  measures: `ν = (b⁻¹)_*ν + ν_ρ ≥ (b⁻¹)_*ν`.
* **If.** `(b⁻¹)_*ν ≤ ν` with `ν` σ-finite, so `ν_ρ := ν` with density `1 - d(b⁻¹)_*ν/dν` is a
  measure with `(b⁻¹)_*ν + ν_ρ = ν` and `ν_ρ ≤ ν`, a Lévy measure; `(1 - b⁻²)A` is positive
  semidefinite. A39(iii) gives an infinitely divisible `ρ` with the triplet
  `((1 - b⁻²)A, ν_ρ, γ - γ')`, and the exponents of `μ_b` and `ρ` add to that of `μ`.

So `#print axioms cited_A44` names A39's three names, and nothing of A44's own (`cited_A42` is a
theorem, Lean core, since review round 3, batch C, 2026-11-23).
Wave 3d, 2026-11-14: the declaration moved here from `PyramidsSkeleton.Ch02CitedFacts`, unchanged
in statement and name.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The matrix `b⁻¹I` acts as `x ↦ b⁻¹x`. -/
theorem toEuclideanLin_inv_smul_one (b : ℝ) :
    ⇑(Matrix.toEuclideanLin (b⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))) = fun x => b⁻¹ • x := by
  funext x
  simp

/-- The image of a measure without atom at `0` under `x ↦ cx`, `c ≠ 0`, restricted to the
complement of `0`, is the image itself. -/
theorem map_smul_restrict_compl_zero {ν : Measure (Rd d)} (h0 : ν {0} = 0) {c : ℝ} (hc : c ≠ 0) :
    (ν.map (fun x => c • x)).restrict {0}ᶜ = ν.map (fun x => c • x) := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  have hm : Measurable (fun x : Rd d => c • x) := measurable_const_smul c
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not]
  change (ν.map (fun x => c • x)) {0} = 0
  rw [Measure.map_apply hm (measurableSet_singleton 0)]
  refine measure_mono_null (fun x hx => ?_) h0
  simpa [hc] using hx

/-- `x ↦ b⁻¹x` undoes `x ↦ bx`, as images of a measure. -/
theorem map_smul_map_inv_smul (ν : Measure (Rd d)) {b : ℝ} (hb : b ≠ 0) :
    (ν.map (fun x => b • x)).map (fun x => b⁻¹ • x) = ν := by
  rw [Measure.map_map (measurable_const_smul _) (measurable_const_smul _)]
  have : ((fun x : Rd d => b⁻¹ • x) ∘ fun x => b • x) = id := by
    funext x; simp [smul_smul, inv_mul_cancel₀ hb]
  rw [this, Measure.map_id]

/-- `x ↦ bx` undoes `x ↦ b⁻¹x`, as images of a measure. -/
theorem map_inv_smul_map_smul (ν : Measure (Rd d)) {b : ℝ} (hb : b ≠ 0) :
    (ν.map (fun x => b⁻¹ • x)).map (fun x => b • x) = ν := by
  rw [Measure.map_map (measurable_const_smul _) (measurable_const_smul _)]
  have : ((fun x : Rd d => b • x) ∘ fun x => b⁻¹ • x) = id := by
    funext x; simp [smul_smul, mul_inv_cancel₀ hb]
  rw [this, Measure.map_id]

/-- **The image `μ_b` of `μ` under `x ↦ b⁻¹x`** (A42 at `U = b⁻¹I`): a probability measure,
infinitely divisible, whose transform is `μ̂(b⁻¹ ·)`, with a triplet whose Gaussian part is
`b⁻²A` and whose Lévy measure is `(b⁻¹)_*ν`. -/
theorem exists_triplet_inv_smul {b : ℝ} (hb : b ≠ 0) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (hμ : IsInfinitelyDivisible μ) (T : LevyTriplet d)
    (hT : HasTriplet μ T) :
    IsProbabilityMeasure (μ.map (fun x => b⁻¹ • x)) ∧
      IsInfinitelyDivisible (μ.map (fun x => b⁻¹ • x)) ∧
      (∀ z : Rd d, charFun (μ.map (fun x => b⁻¹ • x)) z = charFun μ (b⁻¹ • z)) ∧
      ∃ T' : LevyTriplet d, HasTriplet (μ.map (fun x => b⁻¹ • x)) T' ∧
        T'.A = (b⁻¹ * b⁻¹) • T.A ∧ T'.ν = T.ν.map (fun x => b⁻¹ • x) := by
  obtain ⟨hid, -, T', hT', hA', hν', -⟩ :=
    cited_A42 μ hμ T hT (b⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))
  rw [toEuclideanLin_inv_smul_one] at hid hT' hν'
  refine ⟨Measure.isProbabilityMeasure_map (measurable_const_smul _).aemeasurable, hid,
    fun z => ?_,
    T', hT', ?_, ?_⟩
  · rw [charFun_apply, charFun_apply,
      integral_map (measurable_const_smul _).aemeasurable (by fun_prop)]
    congr 1
    funext x
    rw [inner_smul_left, inner_smul_right]
    simp
  · rw [hA']
    simp [Matrix.transpose_smul, smul_smul]
  · rw [hν', map_smul_restrict_compl_zero T.ν_zero (inv_ne_zero hb)]

/-- **`thm:cited-A44`** (Sato, Thm. 15.8, p. 94). For `b > 1` and an infinitely divisible `μ` with
triplet `(A, ν, γ)`: `μ` is semi-selfdecomposable with span `b` if and only if `D_b ν ≥ ν`,
`D_b ν` the image of `ν` under `x ↦ bx`. A theorem from A39 and A42. -/
theorem cited_A44 {b : ℝ} (hb : 1 < b) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hμ : IsInfinitelyDivisible μ) (T : LevyTriplet d) (hT : HasTriplet μ T) :
    IsSemiSelfDecomposableWithSpan b μ ↔ T.ν ≤ T.ν.map (fun x => b • x) := by
  have hb0 : b ≠ 0 := by linarith
  obtain ⟨hprob, hidb, hcf, T', hT', hA', hν'⟩ := exists_triplet_inv_smul hb0 μ hμ T hT
  -- `ν ≤ D_bν` is `(b⁻¹)_*ν ≤ ν`
  have hiff : T.ν ≤ T.ν.map (fun x => b • x) ↔ T.ν.map (fun x => b⁻¹ • x) ≤ T.ν := by
    constructor
    · intro h
      have := Measure.map_mono h (measurable_const_smul b⁻¹)
      rwa [map_smul_map_inv_smul T.ν hb0] at this
    · intro h
      have := Measure.map_mono h (measurable_const_smul b)
      rwa [map_inv_smul_map_smul T.ν hb0] at this
  rw [hiff, ← hν']
  constructor
  · -- only if: the Lévy measure of `μ` is that of `μ_b` plus that of the residual
    rintro ⟨-, ρ, ⟨hρp, hρ⟩, hρid⟩
    haveI := hρp
    obtain ⟨Tρ, hTρ⟩ := cited_A39_exists ρ hρid
    have hsum : HasTriplet μ (T'.add Tρ) := fun z => by
      rw [hρ z, ← hcf z, hT' z, hTρ z, LevyTriplet.lkExponent_add, Complex.exp_add]
    obtain ⟨-, hν, -⟩ := cited_A39_unique μ hμ T (T'.add Tρ) hT hsum
    rw [hν]
    exact Measure.le_add_right le_rfl
  · -- if: the residual has the triplet `((1 - b⁻²)A, ν - (b⁻¹)_*ν, γ - γ')`
    intro hle
    haveI := sigmaFinite_of_null_finite T.ν_zero fun ε hε => T.measure_norm_gt_ne_top hε
    haveI := sigmaFinite_of_null_finite T'.ν_zero fun ε hε => T'.measure_norm_gt_ne_top hε
    set f := T'.ν.rnDeriv T.ν with hf
    have hfm : Measurable f := Measure.measurable_rnDeriv _ _
    have hf1 : f ≤ᵐ[T.ν] 1 := Measure.rnDeriv_le_one_of_le hle
    have hac : T'.ν ≪ T.ν := Measure.absolutelyContinuous_of_le hle
    have hT'ν : T.ν.withDensity f = T'.ν := Measure.withDensity_rnDeriv_eq _ _ hac
    -- the residual Lévy measure
    set νρ := T.ν.withDensity (fun x => 1 - f x) with hνρ
    have hνρle : νρ ≤ T.ν := by
      calc νρ ≤ T.ν.withDensity 1 :=
            withDensity_mono (Filter.Eventually.of_forall fun x => tsub_le_self)
        _ = T.ν := withDensity_one
    have hsplit : T'.ν + νρ = T.ν := by
      rw [← hT'ν, hνρ, ← withDensity_add_left hfm]
      conv_rhs => rw [← withDensity_one (μ := T.ν)]
      refine withDensity_congr_ae ?_
      filter_upwards [hf1] with x hx
      exact add_tsub_cancel_of_le hx
    have hbb : 0 ≤ 1 - b⁻¹ * b⁻¹ := by
      have h1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
      have h0 : 0 < b⁻¹ := inv_pos.2 (by linarith)
      nlinarith
    let Tρ : LevyTriplet d :=
      { A := (1 - b⁻¹ * b⁻¹) • T.A
        ν := νρ
        γ := T.γ - T'.γ
        A_posSemidef := T.A_posSemidef.smul hbb
        ν_zero := le_antisymm ((hνρle _).trans T.ν_zero.le) bot_le
        ν_integrable := ne_top_of_le_ne_top T.ν_integrable (lintegral_mono' hνρle le_rfl) }
    obtain ⟨ρ, hρp, hρid, hTρ⟩ := cited_A39_converse Tρ
    refine ⟨hb, ρ, ⟨hρp, fun z => ?_⟩, hρid⟩
    have hexp : T.lkExponent z = (T'.add Tρ).lkExponent z := by
      have hA : (T'.add Tρ).A = T.A := by
        change T'.A + (1 - b⁻¹ * b⁻¹) • T.A = T.A
        rw [hA', ← add_smul]; simp
      have hν : (T'.add Tρ).ν = T.ν := hsplit
      have hγ : (T'.add Tρ).γ = T.γ := by
        change T'.γ + (T.γ - T'.γ) = T.γ
        abel
      simp only [LevyTriplet.lkExponent, hA, hν, hγ]
    rw [hT z, hexp, LevyTriplet.lkExponent_add, Complex.exp_add, ← hT' z, ← hTρ z, hcf z]

end Pyramids
