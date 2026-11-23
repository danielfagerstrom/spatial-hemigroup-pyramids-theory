/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.LineAppendix
import Pyramids.Pyramid.FamilyStructure
import AffineHemigroup.LineLevyUnique

/-!
# `lem:line-exponent-data`: the data of an exponent on the line

Blueprint: `blueprint/src/parts/A1-line.tex`, `lem:line-exponent-data`, appendix A. Wave 2b: the
five declarations moved here from `PyramidsSkeleton.ChA1Line`, their statements unchanged.

## The route

The line `ℝ` is read inside `ℝ¹` through `x ↦ x e₀` (the affine export's `lineEmb`) and back through
`y ↦ y₀`; transforms, infinite divisibility and symmetry pass both ways.

* **(1), the law.** A39(iii) (`cited_A39_converse`) at the triplet `(2a, ν_s, 0)` of the pair, `ν_s`
  the symmetrization of `ϖ` (the affine export's `symLevyTriplet`, whose exponent is minus the
  pair's, `lkExponent_symLevyTriplet`), read back on `ℝ`. Its transform `e^{-ψ}` is real and even,
  so the law is symmetric; the transform determines the law.
* **(1), the converse.** The lift of a symmetric infinitely divisible law to `ℝ¹` has symmetric
  Lévy data `(A, ν)` (`exists_symData`, A39(i)–(ii), as in `lem:family-structure`); the data of
  `-log μ̂` are `a = A₀₀` and the image `ϖ` of `ν` under `y ↦ |y₀|` on `(0,∞)`.
* **(1), the data are unique**: the affine export's `line_levy_unique` (A39(ii)–(iii) at `d = 1`).
* **(2)** by the substitution `u = λv`, and **(3)** by linearity with (1); the difference
  `ϖ' - ϖ` is built on the pieces `{v ≤ 0 or v > 1/(n+1)}`, made disjoint, on each of which `ϖ` is
  finite.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair IsSymLevyExponent IsSymmetric convPow)
open scoped Topology ENNReal RealInnerProductSpace

/-! ## The line inside `ℝ¹` -/

/-- `x ↦ x e₀` as a continuous linear map. -/
noncomputable def lineEmbL : ℝ →L[ℝ] Rd 1 := (ContinuousLinearMap.id ℝ ℝ).smulRight (ebasis 0)

theorem lineEmbL_apply (x : ℝ) : lineEmbL x = lineEmb x := by
  simp [lineEmbL, lineEmb]

/-- `y ↦ y₀` as a continuous linear map. -/
noncomputable def lineProjL : Rd 1 →L[ℝ] ℝ := EuclideanSpace.proj 0

theorem lineProjL_apply (y : Rd 1) : lineProjL y = y 0 := rfl

/-- The transform of the image under `y ↦ y₀`. -/
theorem charFun_map_lineProj (m : Measure (Rd 1)) (ω : ℝ) :
    charFun (m.map lineProjL) ω = charFun m (lineEmb ω) := by
  rw [charFun_apply, charFun_apply, integral_map lineProjL.continuous.measurable.aemeasurable
    (by fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [lineProjL_apply]
  rw [real_inner_comm, inner_lineEmb]
  simp [mul_comm]

/-- The transform of the image under `x ↦ x e₀`. -/
theorem charFun_map_lineEmb (m : Measure ℝ) (z : Rd 1) :
    charFun (m.map lineEmbL) z = charFun m (z 0) := by
  rw [charFun_apply, charFun_apply, integral_map lineEmbL.continuous.measurable.aemeasurable
    (by fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [lineEmbL_apply]
  rw [real_inner_comm, inner_lineEmb]
  simp [mul_comm]

/-- The transform of the reflection, on the line. -/
theorem charFun_map_neg_real (m : Measure ℝ) (ω : ℝ) :
    charFun (m.map fun x => -x) ω = charFun m (-ω) := by
  rw [charFun_apply, charFun_apply, integral_map measurable_neg.aemeasurable (by fun_prop)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp

/-- A convolution power commutes with a continuous linear map. -/
theorem convPow_map_lineProj (ν : Measure (Rd 1)) [IsFiniteMeasure ν] :
    ∀ n : ℕ, convPow (ν.map lineProjL) n = (convPow ν n).map lineProjL
  | 0 => by simp [convPow, Measure.map_dirac]
  | n + 1 => by
    haveI := ScaleSpace.isFiniteMeasure_convPow_Rd ν n
    rw [convPow, convPow, convPow_map_lineProj ν n, Measure.map_conv_continuousLinearMap]

theorem convPow_map_lineEmb (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∀ n : ℕ, convPow (ν.map lineEmbL) n = (convPow ν n).map lineEmbL
  | 0 => by simp [convPow, Measure.map_dirac]
  | n + 1 => by
    haveI := ScaleSpace.isFiniteMeasure_convPow ν n
    rw [convPow, convPow, convPow_map_lineEmb ν n, Measure.map_conv_continuousLinearMap]

theorem isInfinitelyDivisible_map_lineProj {m : Measure (Rd 1)} (h : IsInfinitelyDivisible m) :
    IsInfinitelyDivisible (m.map lineProjL) := by
  intro n hn
  obtain ⟨ν, hν, hνn⟩ := h n hn
  exact ⟨ν.map lineProjL, Measure.isProbabilityMeasure_map lineProjL.continuous.aemeasurable,
    by rw [convPow_map_lineProj, hνn]⟩

theorem isInfinitelyDivisible_map_lineEmb {m : Measure ℝ} (h : IsInfinitelyDivisible m) :
    IsInfinitelyDivisible (m.map lineEmbL) := by
  intro n hn
  obtain ⟨ν, hν, hνn⟩ := h n hn
  exact ⟨ν.map lineEmbL, Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable,
    by rw [convPow_map_lineEmb, hνn]⟩

/-! ## Pairs -/

/-- The exponent of a pair is even. -/
theorem SymLevyPair_exponent_neg (P : SymLevyPair) (ω : ℝ) : P.exponent (-ω) = P.exponent ω := by
  simp [SymLevyPair.exponent, SymLevyPair.exponentL, neg_mul, Real.cos_neg]

/-- A Lévy measure on the line is finite off every neighbourhood of `0`. -/
theorem SymLevyPair_measure_Ioi_ne_top (P : SymLevyPair) {ε : ℝ} (hε : 0 < ε) :
    P.ν (Ioi ε) ≠ ⊤ := by
  set c : ℝ≥0∞ := ENNReal.ofReal (min 1 (ε ^ 2)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_min one_pos (by positivity)
  have hle : c * P.ν {x | c ≤ ENNReal.ofReal (min 1 (x ^ 2))} ≤
      ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂P.ν :=
    mul_meas_ge_le_lintegral₀ (by fun_prop) c
  have hsub : Ioi ε ⊆ {x | c ≤ ENNReal.ofReal (min 1 (x ^ 2))} := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal (min_le_min le_rfl ?_)
    have hx' : ε < x := hx
    nlinarith
  have h1 : c * P.ν (Ioi ε) ≠ ⊤ :=
    ne_top_of_le_ne_top P.ν_integrable ((mul_le_mul_right (measure_mono hsub) c).trans hle)
  intro htop
  rw [htop, ENNReal.mul_top hc0] at h1
  exact h1 rfl

/-- **The sum of two pairs**, with the exponents adding. -/
noncomputable def SymLevyPair_add (P R : SymLevyPair) : SymLevyPair where
  a := P.a + R.a
  ν := P.ν + R.ν
  a_nonneg := add_nonneg P.a_nonneg R.a_nonneg
  ν_folded := by
    rw [ScaleSpace.IsFolded, Measure.coe_add, Pi.add_apply, P.ν_folded, R.ν_folded, add_zero]
  ν_integrable := by
    rw [lintegral_add_measure]
    exact ENNReal.add_ne_top.mpr ⟨P.ν_integrable, R.ν_integrable⟩

theorem SymLevyPair_add_exponent (P R : SymLevyPair) (ω : ℝ) :
    (SymLevyPair_add P R).exponent ω = P.exponent ω + R.exponent ω := by
  have h : (SymLevyPair_add P R).exponentL ω = P.exponentL ω + R.exponentL ω := by
    simp only [SymLevyPair.exponentL, SymLevyPair_add, lintegral_add_measure]
    rw [show (P.a + R.a) * ω ^ 2 = P.a * ω ^ 2 + R.a * ω ^ 2 by ring,
      ENNReal.ofReal_add (mul_nonneg P.a_nonneg (sq_nonneg ω))
        (mul_nonneg R.a_nonneg (sq_nonneg ω))]
    exact add_add_add_comm _ _ _ _
  unfold SymLevyPair.exponent
  rw [h, ENNReal.toReal_add (P.exponentL_ne_top ω) (R.exponentL_ne_top ω)]

/-- **The difference of two Lévy measures on the line**: if `ϖ ≤ ϖ'`, some measure `ρ` has
`ρ + ϖ = ϖ'`. Built on the pieces of `{v ≤ 0} ∪ {v > 1/(n+1)}`, made disjoint, where `ϖ` is
finite. -/
theorem SymLevyPair_exists_sub (P P' : SymLevyPair) (hle : P.ν ≤ P'.ν) :
    ∃ ρ : Measure ℝ, ρ + P.ν = P'.ν := by
  set T : ℕ → Set ℝ := fun n => Iic 0 ∪ Ioi (1 / ((n : ℝ) + 1)) with hT
  set S := disjointed T with hS
  have hTm : ∀ n, MeasurableSet (T n) := fun n => measurableSet_Iic.union measurableSet_Ioi
  have hSm : ∀ n, MeasurableSet (S n) := MeasurableSet.disjointed hTm
  have hSd : Pairwise (Function.onFun Disjoint S) := disjoint_disjointed T
  have hSU : ⋃ n, S n = univ := by
    rw [hS, iUnion_disjointed]
    refine eq_univ_of_forall fun x => ?_
    rcases le_or_gt x 0 with hx | hx
    · exact mem_iUnion.2 ⟨0, Or.inl hx⟩
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact mem_iUnion.2 ⟨n, Or.inr hn⟩
  have hfin : ∀ n, P.ν (S n) ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top ?_ (measure_mono (disjointed_subset T n))
    refine ne_top_of_le_ne_top ?_ (measure_union_le _ _)
    rw [P.ν_folded, zero_add]
    exact SymLevyPair_measure_Ioi_ne_top P (by positivity)
  have hsplit : ∀ m : Measure ℝ, m = Measure.sum fun n => m.restrict (S n) := by
    intro m
    rw [← Measure.restrict_iUnion hSd hSm, hSU, Measure.restrict_univ]
  have key : (Measure.sum fun n => P'.ν.restrict (S n) - P.ν.restrict (S n)) +
      Measure.sum (fun n => P.ν.restrict (S n)) = Measure.sum fun n => P'.ν.restrict (S n) := by
    rw [Measure.sum_add_sum]
    refine congrArg Measure.sum (funext fun n => ?_)
    haveI : IsFiniteMeasure (P.ν.restrict (S n)) :=
      isFiniteMeasure_restrict.2 (hfin n)
    exact Measure.sub_add_cancel_of_le (Measure.restrict_mono le_rfl hle)
  rw [← hsplit P.ν, ← hsplit P'.ν] at key
  exact ⟨_, key⟩

/-! ## `lem:line-exponent-data` -/

/-- **`lem:line-exponent-data`(1), existence and uniqueness of the law.** Every `ψ ∈ ND_s` is
`-log μ̂` for exactly one symmetric infinitely divisible law `μ`. -/
theorem line_exponent_data_1 (ψ : ℝ → ℝ) (hψ : IsSymLevyExponent ψ) :
    ∃! μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsSymmetric μ ∧ IsInfinitelyDivisible μ ∧
      ∀ ω : ℝ, charFun μ ω = ((Real.exp (-ψ ω) : ℝ) : ℂ) := by
  obtain ⟨P, hP⟩ := hψ
  obtain ⟨μ1, hprob, hid, hT⟩ := cited_A39_converse (symLevyTriplet P)
  haveI := hprob
  set μ := μ1.map lineProjL with hμ
  haveI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map lineProjL.continuous.aemeasurable
  have hchar : ∀ ω : ℝ, charFun μ ω = ((Real.exp (-ψ ω) : ℝ) : ℂ) := by
    intro ω
    rw [hμ, charFun_map_lineProj, hT, lkExponent_symLevyTriplet, lineEmb_apply_zero, hP,
      Complex.ofReal_exp, Complex.ofReal_neg]
  refine ⟨μ, ⟨inferInstance, ?_, isInfinitelyDivisible_map_lineProj hid, hchar⟩, ?_⟩
  · -- symmetry: the transform is even
    haveI : IsProbabilityMeasure (μ.map fun x => -x) :=
      Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_map_neg_real, hchar, hchar, hP, hP, SymLevyPair_exponent_neg]
  · rintro μ' ⟨hprob', -, -, hchar'⟩
    haveI := hprob'
    exact Measure.ext_of_charFun (funext fun ω => by rw [hchar', hchar])

/-- **`lem:line-exponent-data`(1), the converse.** For every symmetric infinitely divisible law
`μ`, `-log μ̂` lies in `ND_s`. -/
theorem line_exponent_data_1_converse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsymm : IsSymmetric μ) (hid : IsInfinitelyDivisible μ) :
    ∃ P : SymLevyPair, ∀ ω : ℝ, charFun μ ω = ((Real.exp (-P.exponent ω) : ℝ) : ℂ) := by
  set μ1 := μ.map lineEmbL with hμ1
  haveI : IsProbabilityMeasure μ1 :=
    Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable
  have hs1 : μ1.map (fun y => -y) = μ1 := by
    haveI : IsProbabilityMeasure (μ1.map fun y => -y) :=
      Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
    refine Measure.ext_of_charFun (funext fun z => ?_)
    have h := charFun_map_isometry μ1 (LinearIsometryEquiv.neg ℝ (E := Rd 1)) z
    rw [coe_neg_isometry] at h
    rw [h, hμ1, charFun_map_lineEmb, charFun_map_lineEmb]
    have hneg : (LinearIsometryEquiv.neg ℝ (E := Rd 1)).symm z = -z := rfl
    rw [hneg, PiLp.neg_apply, ← charFun_map_neg_real, hsymm]
  obtain ⟨D, hD⟩ := exists_symData (isInfinitelyDivisible_map_lineEmb hid) hs1
  -- the folded pair
  set g : Rd 1 → ℝ := fun y => |y 0| with hg
  have hgm : Measurable g := by fun_prop
  set ϖ : Measure ℝ := (D.ν.map g).restrict (Ioi 0) with hϖ
  have ha : 0 ≤ D.A 0 0 := D.A_posSemidef.diag_nonneg
  have hfold : ScaleSpace.IsFolded ϖ := by
    rw [ScaleSpace.IsFolded, hϖ, Measure.restrict_apply measurableSet_Iic, Set.Iic_inter_Ioi,
      Ioc_self, measure_empty]
  have hlint : ∀ f : ℝ → ℝ≥0∞, Measurable f → f 0 = 0 →
      ∫⁻ v, f v ∂ϖ = ∫⁻ y, f (|y 0|) ∂D.ν := by
    intro f hf hf0
    rw [hϖ, ← lintegral_indicator measurableSet_Ioi, lintegral_map (hf.indicator measurableSet_Ioi)
      hgm]
    refine lintegral_congr fun y => ?_
    rcases (abs_nonneg (y 0)).lt_or_eq with h | h
    · simp [hg, indicator_of_mem (show |y 0| ∈ Ioi (0 : ℝ) from h)]
    · simp [hg, ← h, hf0]
  have hint : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ϖ ≠ ⊤ := by
    rw [hlint _ (by fun_prop) (by simp)]
    convert D.ν_integrable using 3 with y
    rw [sq_abs, norm_sq_rd1, min_comm]
  set P : SymLevyPair := ⟨D.A 0 0, ϖ, ha, hfold, hint⟩ with hP
  refine ⟨P, fun ω => ?_⟩
  have h1 : charFun μ ω = charFun μ1 (lineEmb ω) := by
    rw [hμ1, charFun_map_lineEmb, lineEmb_apply_zero]
  rw [h1, hD]
  congr 4
  -- the exponent of the data at `ω e₀` is the pair's exponent at `ω`
  have hquad : quad D.A (lineEmb ω) = D.A 0 0 * ω ^ 2 := by
    have hlin : (lin D.A (lineEmb ω)) 0 = D.A 0 0 * ω := by
      change (Matrix.toEuclideanLin D.A (lineEmb ω)) 0 = _
      rw [Matrix.toLpLin_apply]
      simp [Matrix.mulVec, dotProduct, lineEmb, ebasis]
    rw [quad, real_inner_comm, inner_lineEmb, hlin]
    ring
  have hcos : ∀ y : Rd 1, 1 - Real.cos ⟪lineEmb ω, y⟫ = 1 - Real.cos (ω * |y 0|) := by
    intro y
    rw [real_inner_comm, inner_lineEmb]
    rcases abs_choice (y 0) with h | h <;> rw [h] <;> simp [mul_comm, Real.cos_neg]
  have hI := D.triplet.integrable_one_sub_cos (lineEmb ω)
  have hI' : Integrable (fun y : Rd 1 => 1 - Real.cos ⟪lineEmb ω, y⟫) D.ν := hI
  have hfin : ∫⁻ y, ENNReal.ofReal (1 - Real.cos (ω * |y 0|)) ∂D.ν ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hI'.congr (ae_of_all _ hcos))
      (ae_of_all _ fun y => sub_nonneg.2 (Real.cos_le_one _))]
    exact ENNReal.ofReal_ne_top
  rw [SymLevyData.exponent, pairExponent, hquad, SymLevyPair.exponent, SymLevyPair.exponentL,
    ENNReal.toReal_add ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (mul_nonneg ha (sq_nonneg ω))]
  · rw [hlint _ (by fun_prop) (by simp), integral_congr_ae (ae_of_all _ hcos),
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => sub_nonneg.2 (Real.cos_le_one _))
        (by fun_prop)]
  · rw [hlint _ (by fun_prop) (by simp)]
    exact hfin

/-- **`lem:line-exponent-data`(1), the data are unique.** -/
theorem line_exponent_data_1_unique (ψ : ℝ → ℝ) (P P' : SymLevyPair) (hP : HasExpData ψ P)
    (hP' : HasExpData ψ P') : P.a = P'.a ∧ P.ν = P'.ν :=
  line_levy_unique P P' fun ω => (hP ω).symm.trans (hP' ω)

/-- **`lem:line-exponent-data`(2).** If `ψ` has the data `(a, ϖ)` and `λ > 0`, `ψ(λ ·)` has the
data `(λ²a, T_λ ϖ)`. -/
theorem line_exponent_data_2 (ψ : ℝ → ℝ) (P : SymLevyPair) (hP : HasExpData ψ P) {lam : ℝ}
    (hlam : 0 < lam) :
    ∃ Q : SymLevyPair, Q.a = lam ^ 2 * P.a ∧ Q.ν = P.ν.map (fun v => lam * v) ∧
      HasExpData (fun ω => ψ (lam * ω)) Q := by
  have hmeas : Measurable fun x : ℝ => lam * x := measurable_const_mul lam
  have hfold : ScaleSpace.IsFolded (P.ν.map fun x : ℝ => lam * x) := by
    rw [ScaleSpace.IsFolded, Measure.map_apply hmeas measurableSet_Iic]
    have hpre : (fun x : ℝ => lam * x) ⁻¹' Iic (0 : ℝ) = Iic (0 : ℝ) := by
      ext x
      simp only [mem_preimage, mem_Iic]
      constructor
      · intro hx; nlinarith
      · intro hx; nlinarith
    rw [hpre]
    exact P.ν_folded
  have hint : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(P.ν.map fun x : ℝ => lam * x)) ≠ ⊤ := by
    rw [lintegral_map (by fun_prop) hmeas]
    refine ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (a := ENNReal.ofReal (max 1 (lam ^ 2))) ENNReal.ofReal_ne_top
        P.ν_integrable) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left 1 (lam ^ 2)))]
    exact ENNReal.ofReal_le_ofReal (ScaleSpace.min_one_sq_mul_le lam x)
  refine ⟨⟨lam ^ 2 * P.a, P.ν.map fun x : ℝ => lam * x, mul_nonneg (sq_nonneg lam) P.a_nonneg,
    hfold, hint⟩, rfl, rfl, fun ω => ?_⟩
  change ψ (lam * ω) = _
  rw [hP (lam * ω), SymLevyPair.exponent, SymLevyPair.exponent, SymLevyPair.exponentL,
    SymLevyPair.exponentL, lintegral_map (by fun_prop) hmeas]
  simp only
  rw [show lam ^ 2 * P.a * ω ^ 2 = P.a * (lam * ω) ^ 2 by ring]
  congr 3
  funext x
  rw [show ω * (lam * x) = lam * ω * x by ring]

/-- **`lem:line-exponent-data`(3).** For `ψ, ψ' ∈ ND_s` with data `(a, ϖ)`, `(a', ϖ')`:
`ψ' - ψ ∈ ND_s` iff `a' ≥ a` and `ϖ' ≥ ϖ`, and then `ψ' - ψ` has the data `(a' - a, ϖ' - ϖ)`. -/
theorem line_exponent_data_3 (ψ ψ' : ℝ → ℝ) (P P' : SymLevyPair) (hP : HasExpData ψ P)
    (hP' : HasExpData ψ' P') :
    (IsSymLevyExponent (fun ω => ψ' ω - ψ ω) ↔ P.a ≤ P'.a ∧ P.ν ≤ P'.ν) ∧
      (P.a ≤ P'.a → P.ν ≤ P'.ν →
        ∃ Q : SymLevyPair, Q.a = P'.a - P.a ∧ Q.ν + P.ν = P'.ν ∧
          HasExpData (fun ω => ψ' ω - ψ ω) Q) := by
  -- the second clause
  have hsecond : P.a ≤ P'.a → P.ν ≤ P'.ν →
      ∃ Q : SymLevyPair, Q.a = P'.a - P.a ∧ Q.ν + P.ν = P'.ν ∧
        HasExpData (fun ω => ψ' ω - ψ ω) Q := by
    intro ha hν
    obtain ⟨ρ, hρ⟩ := SymLevyPair_exists_sub P P' hν
    have hρle : ρ ≤ P'.ν := hρ ▸ Measure.le_add_right le_rfl
    have hfold : ScaleSpace.IsFolded ρ :=
      nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hρle (Iic 0)).trans P'.ν_folded.le)
    have hint : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ρ ≠ ⊤ :=
      ne_top_of_le_ne_top P'.ν_integrable (lintegral_mono' hρle le_rfl)
    set Q : SymLevyPair := ⟨P'.a - P.a, ρ, sub_nonneg.2 ha, hfold, hint⟩ with hQ
    refine ⟨Q, rfl, hρ, fun ω => ?_⟩
    have hsum : SymLevyPair_add Q P = P' := by
      cases P' with
      | mk a' ν' _ _ _ =>
        simp only [SymLevyPair_add, hQ]
        congr 1
        simp
    change ψ' ω - ψ ω = Q.exponent ω
    rw [hP ω, hP' ω, ← hsum, SymLevyPair_add_exponent]
    ring
  refine ⟨⟨fun ⟨R, hR⟩ => ?_, fun ⟨ha, hν⟩ => ?_⟩, hsecond⟩
  · -- the data of the difference add to those of `ψ`
    obtain ⟨ha, hν⟩ := line_levy_unique (SymLevyPair_add P R) P' fun ω => by
      rw [SymLevyPair_add_exponent, ← hP ω, ← hR ω, ← hP' ω]
      ring
    refine ⟨?_, ?_⟩
    · rw [← ha]
      exact le_add_of_nonneg_right R.a_nonneg
    · rw [← hν]
      exact Measure.le_add_right le_rfl
  · obtain ⟨Q, -, -, hQ⟩ := hsecond ha hν
    exact ⟨Q, hQ⟩

end Pyramids
