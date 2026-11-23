/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.QCinRepr
import Pyramids.Cited.A43

/-!
# `prop:strata-cylinder-coordinates-q-cin`(3): `𝒦_q` is the semi-selfdecomposable class

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:strata-cylinder-coordinates-q-cin`. Wave 3a:
`qcin_3` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in statement and name.

## The route

The proof of record's, step for step.

* `ψ ∈ 𝒦_q` iff `ψ - ψ(q^{-1} ·) ∈ ND_s` (`isInKq_iff_sub`): `ψ(q^{-1} ·)` has the data
  `(q^{-2}a, T_{q^{-1}}ϖ)` (`lem:line-exponent-data`(2)), `q^{-2}a ≤ a`, and
  `T_{q^{-1}}ϖ ≤ ϖ` iff `ϖ ≤ T_qϖ` (`map_inv_le_iff`); then `lem:line-exponent-data`(3).
* For `ψ ∈ 𝒦_q` the laws of `ψ` and of `ψ - ψ(q^{-1} ·)` (`lem:line-exponent-data`(1)) are a
  semi-selfdecomposable law of span `q` and its residual.
* Conversely, a semi-selfdecomposable law on the line is infinitely divisible: ledger A43's semi
  clause, `cited_A43_semi_infinitelyDivisible`, read in `ℝ¹` through `x ↦ xe₀`
  (`isInfinitelyDivisible_of_semiSD_line`). So `μ̂ = e^{-ψ}` with `ψ ∈ ND_s`, and
  `ρ̂ = e^{-(ψ - ψ(q^{-1} ·))}` is real and even; `ρ` is symmetric and infinitely divisible, so
  `ψ - ψ(q^{-1} ·) ∈ ND_s`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair IsSymLevyExponent IsSymmetric)
open scoped Topology ENNReal

/-- `T_{q^{-1}}ν ≤ ν` iff `ν ≤ T_qν`. -/
theorem map_inv_le_iff {q : ℝ} (hq : q ≠ 0) (ν : Measure ℝ) :
    ν.map (fun v => q⁻¹ * v) ≤ ν ↔ ν ≤ ν.map (fun v => q * v) := by
  constructor
  · intro h
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.map_apply (measurable_const_mul _) hA]
    calc ν A = (ν.map fun v => q⁻¹ * v) ((fun v => q * v) ⁻¹' A) := by
          rw [Measure.map_apply (measurable_const_mul _) (measurable_const_mul _ hA)]
          congr 1
          ext x
          simp [mul_inv_cancel_left₀ hq]
      _ ≤ _ := Measure.le_iff'.1 h _
  · intro h
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.map_apply (measurable_const_mul _) hA]
    refine (Measure.le_iff'.1 h _).trans_eq ?_
    rw [Measure.map_apply (measurable_const_mul _) (measurable_const_mul _ hA)]
    congr 1
    ext x
    simp [inv_mul_cancel_left₀ hq]

/-- **`ψ ∈ 𝒦_q` iff `ψ - ψ(q^{-1} ·) ∈ ND_s`**, for `ψ ∈ ND_s`. -/
theorem isInKq_iff_sub {q : ℝ} (hq : 1 < q) {ψ : ℝ → ℝ} (P : SymLevyPair) (hP : HasExpData ψ P) :
    IsInKq q ψ ↔ IsSymLevyExponent (fun ω => ψ ω - ψ (q⁻¹ * ω)) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨Q, hQa, hQν, hQ⟩ := line_exponent_data_2 ψ P hP (inv_pos.2 hq0)
  rw [(line_exponent_data_3 _ ψ Q P hQ hP).1, hQν, map_inv_le_iff hq0.ne']
  have ha : Q.a ≤ P.a := by
    rw [hQa]
    refine mul_le_of_le_one_left P.a_nonneg (pow_le_one₀ (inv_nonneg.2 hq0.le) ?_)
    exact inv_le_one_of_one_le₀ hq.le
  constructor
  · rintro ⟨R, hR, hK⟩
    obtain ⟨-, hν⟩ := line_exponent_data_1_unique ψ R P hR hP
    rw [hν] at hK
    exact ⟨ha, hK⟩
  · rintro ⟨-, hK⟩
    exact ⟨P, hP, hK⟩

/-- **A43 on the line**: a semi-selfdecomposable law on `ℝ` is infinitely divisible. The law and its
residual are read in `ℝ¹` through `x ↦ xe₀`, where `cited_A43_semi_infinitelyDivisible` applies, and
read back through `y ↦ y₀`. -/
theorem isInfinitelyDivisible_of_semiSD_line {q : ℝ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : IsSemiSelfDecomposableWithSpan q μ) : IsInfinitelyDivisible μ := by
  obtain ⟨hq, ρ, ⟨hρp, hρ⟩, hρid⟩ := h
  haveI := hρp
  haveI : IsProbabilityMeasure (μ.map lineEmbL) :=
    Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable
  have h1 : IsSemiSelfDecomposable (μ.map lineEmbL) := by
    refine ⟨q, hq, ρ.map lineEmbL,
      ⟨Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable, fun z => ?_⟩,
      isInfinitelyDivisible_map_lineEmb hρid⟩
    rw [charFun_map_lineEmb, charFun_map_lineEmb, charFun_map_lineEmb, hρ (z 0)]
    simp [PiLp.smul_apply, smul_eq_mul]
  have hid := cited_A43_semi_infinitelyDivisible (μ.map lineEmbL) h1
  have hcomp : (lineProjL ∘ lineEmbL : ℝ → ℝ) = id :=
    funext fun x => by simp [lineProjL_apply, lineEmbL_apply, lineEmb_apply_zero]
  have hback : (μ.map lineEmbL).map lineProjL = μ := by
    rw [Measure.map_map lineProjL.continuous.measurable lineEmbL.continuous.measurable, hcomp,
      Measure.map_id]
  rw [← hback]
  exact isInfinitelyDivisible_map_lineProj hid

theorem eq_of_ofReal_exp_neg {a b : ℝ}
    (h : ((Real.exp (-a) : ℝ) : ℂ) = ((Real.exp (-b) : ℝ) : ℂ)) : a = b :=
  neg_injective (Real.exp_injective (Complex.ofReal_injective h))

/-- **The converse**: the exponent of a symmetric semi-selfdecomposable law of span `q` lies in
`𝒦_q`. Spends A43's semi clause. -/
theorem isInKq_of_semiSD {q : ℝ} (hq : 1 < q) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsymm : IsSymmetric μ) (hsemi : IsSemiSelfDecomposableWithSpan q μ) :
    ∃ P : SymLevyPair, IsInKq q P.exponent ∧
      ∀ ω : ℝ, charFun μ ω = ((Real.exp (-P.exponent ω) : ℝ) : ℂ) := by
  have hid := isInfinitelyDivisible_of_semiSD_line μ hsemi
  obtain ⟨P, hP⟩ := line_exponent_data_1_converse μ hsymm hid
  refine ⟨P, ?_, hP⟩
  obtain ⟨-, ρ, ⟨hρp, hρ⟩, hρid⟩ := hsemi
  haveI := hρp
  -- `ρ̂ = e^{-(ψ - ψ(q⁻¹ ·))}`
  have hρc : ∀ ω : ℝ, charFun ρ ω =
      ((Real.exp (-(P.exponent ω - P.exponent (q⁻¹ * ω))) : ℝ) : ℂ) := by
    intro ω
    have h := hρ ω
    rw [smul_eq_mul, hP, hP] at h
    have hne : ((Real.exp (-P.exponent (q⁻¹ * ω)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    rw [show -(P.exponent ω - P.exponent (q⁻¹ * ω)) = -P.exponent ω - -P.exponent (q⁻¹ * ω) by
      ring, Real.exp_sub, Complex.ofReal_div]
    exact eq_div_of_mul_eq hne (by rw [mul_comm]; exact h.symm)
  -- `ρ` is symmetric
  have hρs : IsSymmetric ρ := by
    haveI : IsProbabilityMeasure (ρ.map fun x => -x) :=
      Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_map_neg_real, hρc, hρc, SymLevyPair_exponent_neg, mul_neg,
      SymLevyPair_exponent_neg]
  obtain ⟨R, hR⟩ := line_exponent_data_1_converse ρ hρs hρid
  rw [isInKq_iff_sub hq P fun ω => rfl]
  exact ⟨R, fun ω => eq_of_ofReal_exp_neg ((hρc ω).symm.trans (hR ω))⟩

/-- **`prop:strata-cylinder-coordinates-q-cin`(3).** `𝒦_q` is the set of the exponents `-log μ̂`
of the symmetric semi-selfdecomposable laws of span `q`. -/
theorem qcin_3 {q : ℝ} (hq : 1 < q) :
    (∀ ψ : ℝ → ℝ, IsInKq q ψ ↔
        ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsSymmetric μ ∧
          IsSemiSelfDecomposableWithSpan q μ ∧
          ∀ ω : ℝ, charFun μ ω = ((Real.exp (-ψ ω) : ℝ) : ℂ)) ∧
      ∀ μ : Measure ℝ, IsProbabilityMeasure μ → IsSymmetric μ →
        IsSemiSelfDecomposableWithSpan q μ →
          ∃ ψ : ℝ → ℝ, IsInKq q ψ ∧ ∀ ω : ℝ, charFun μ ω = ((Real.exp (-ψ ω) : ℝ) : ℂ) := by
  refine ⟨fun ψ => ⟨fun hψ => ?_, ?_⟩, fun μ hμp hμs hsemi => ?_⟩
  · obtain ⟨P, hP, hK⟩ := hψ
    obtain ⟨μ, ⟨hμp, hμs, -, hμc⟩, -⟩ := line_exponent_data_1 ψ ⟨P, hP⟩
    have hsub := (isInKq_iff_sub hq P hP).1 ⟨P, hP, hK⟩
    obtain ⟨ρ, ⟨hρp, -, hρid, hρc⟩, -⟩ := line_exponent_data_1 _ hsub
    have hρc' : ∀ ω : ℝ, charFun ρ ω = ((Real.exp (-(ψ ω - ψ (q⁻¹ * ω))) : ℝ) : ℂ) :=
      fun ω => hρc ω
    refine ⟨μ, hμp, hμs, ⟨hq, ρ, ⟨hρp, fun z => ?_⟩, hρid⟩, hμc⟩
    rw [smul_eq_mul, hμc, hμc, hρc', ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · rintro ⟨μ, hμp, hμs, hsemi, hμc⟩
    haveI := hμp
    obtain ⟨P, hK, hP⟩ := isInKq_of_semiSD hq μ hμs hsemi
    have hψ : ψ = P.exponent :=
      funext fun ω => eq_of_ofReal_exp_neg ((hμc ω).symm.trans (hP ω))
    rw [hψ]
    exact hK
  · haveI := hμp
    obtain ⟨P, hK, hP⟩ := isInKq_of_semiSD hq μ hμs hsemi
    exact ⟨P.exponent, hK, hP⟩

end Pyramids
