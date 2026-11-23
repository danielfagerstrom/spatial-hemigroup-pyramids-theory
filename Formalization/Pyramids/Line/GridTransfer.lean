/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.NoLatticeKernelLine
import Pyramids.LineAppendix.AnnulusParametrization
import Pyramids.LineAppendix.ClassicalWeights
import Pyramids.Pyramid.LadderNotEvery
import Pyramids.Pyramid.LatticeInfinitelyDivisible
import Pyramids.Pyramid.NoBoundedStep

/-!
# Grid masks on the line, carried to `ℝ¹` and back

Blueprint: `blueprint/src/parts/02-line.tex`, `prop:grid-pyramids-infinitely-divisible`. Wave 3e:
the transfer lemmas the node's assembly needs, written once. The node's own declarations are in
`Pyramids.Line.GridPyramids` and `Pyramids.Line.GeometricMask`.

The chapter-3 nodes the proposition rests on (`lem:lattice-infinitely-divisible`,
`prop:no-bounded-step`, `prop:ladder-knot-kernel`) are stated for laws on `ℝ^d`; the mask is a law
on `ℝ`. The line is read in `ℝ¹` through `x ↦ xe₀` (`lineEmbL`) and back through `y ↦ y₀`
(`lineProjL`), as in `lem:discrete-covariance-line` and `thm:annulus-parametrization`.

* **Pairs with no Gaussian part.** A folded pair `(0, ϖ)` with `ϖ` finite has the exponent
  `∫ (1 - cos ωv) ϖ(dv)`, so "`ϖ` is the folded Lévy measure of the compound Poisson law `w`"
  (`IsMaskLevyMeasure`) is "`w` has the folded data `(0, ϖ)`" (`maskPair`). The pair is unique
  (`lem:line-exponent-data`(1)), so `ϖ` is determined by `w`, it is `0` exactly when `w = δ₀`,
  and `w` is symmetric with a positive transform. Such a `w` is infinitely divisible: its lift is
  the compound Poisson law of the symmetric lift of `ϖ`, whose `n`-th root is the compound Poisson
  law of `ϖ/n`.
* **The data in `ℝ¹`.** A law with folded data `(a, ϖ)` lifts to a law with the data
  `(a, ϖ_s)`, `ϖ_s` the symmetric lift (`SymLevyPair_toData`). The lift commutes with sums and
  dilations, so `ν* = ∑_m D_{q^{-m}} ν` of a lifted measure is the lift of
  `ϖ_1 = ∑_m T_{q^{-m}} ϖ` (`knotLevyMeasure`), and the logarithmic moments agree.
* **Families.** A family carrying the grid ladder is a symmetric `q`-covariant family with the step
  `w`; conversely a family in `ℝ¹` with the ladder of the lifted mask reads back to one on `ℝ`,
  whose kernels are those of a `CascadeCore` with (A8) at `q^ℤ` in the canonical gauge
  (`lem:line-axioms-kernels`(2), `lem:discrete-covariance-line`), with the ladder steps `T_{qⁿ}w`
  by covariance iterated.
* **The lattice `ξℤ`** is the `ℤ`-span of `ξe₀` in `ℝ¹`, discrete and of full rank.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X CascadeCore CascadeFamily IsScaleCovariant IsKernelFamily IsSymmetric
  SymLevyPair)
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace

/-! ## Pairs with no Gaussian part -/

/-- The integrand `1 - cos(ωv)` is integrable against a finite measure. -/
theorem integrable_one_sub_cos_of_finite (ν : Measure ℝ) [IsFiniteMeasure ν] (ω : ℝ) :
    Integrable (fun v => 1 - Real.cos (ω * v)) ν :=
  Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 2 (ae_of_all _ fun v => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.cos_le_one (ω * v), Real.neg_one_le_cos (ω * v)])

/-- **The exponent of a pair with `a = 0` and a finite measure** is the Bochner integral
`∫ (1 - cos ωv) ϖ(dv)`. -/
theorem symLevyPair_exponent_eq_integral (P : SymLevyPair) (ha : P.a = 0)
    [IsFiniteMeasure P.ν] (ω : ℝ) : P.exponent ω = ∫ v, (1 - Real.cos (ω * v)) ∂P.ν := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun v => sub_nonneg.2 (Real.cos_le_one _))
    (Continuous.aestronglyMeasurable (by fun_prop))]
  simp [SymLevyPair.exponent, SymLevyPair.exponentL, ha]

/-- **The pair `(0, ϖ)`** of a finite folded measure. -/
noncomputable def maskPair (ϖ : Measure ℝ) (hfin : IsFiniteMeasure ϖ)
    (hfold : ScaleSpace.IsFolded ϖ) : SymLevyPair where
  a := 0
  ν := ϖ
  a_nonneg := le_rfl
  ν_folded := hfold
  ν_integrable := by
    haveI := hfin
    refine ne_top_of_le_ne_top (measure_ne_top ϖ univ) ?_
    calc ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ϖ ≤ ∫⁻ _, 1 ∂ϖ :=
          lintegral_mono fun x => ENNReal.ofReal_le_one.2 (min_le_left _ _)
      _ = ϖ univ := lintegral_one

theorem maskPair_exponent (ϖ : Measure ℝ) (hfin : IsFiniteMeasure ϖ)
    (hfold : ScaleSpace.IsFolded ϖ) (ω : ℝ) :
    (maskPair ϖ hfin hfold).exponent ω = ∫ v, (1 - Real.cos (ω * v)) ∂ϖ := by
  haveI : IsFiniteMeasure (maskPair ϖ hfin hfold).ν := hfin
  exact symLevyPair_exponent_eq_integral (maskPair ϖ hfin hfold) rfl ω

/-- A folded Lévy measure of `w` gives `w` the folded data `(0, ϖ)`. -/
theorem IsMaskLevyMeasure.isFoldedData {w ϖ : Measure ℝ} (h : IsMaskLevyMeasure w ϖ) :
    IsFoldedData w (maskPair ϖ h.1 h.2.1) := fun ω => by
  rw [h.2.2 ω, maskPair_exponent]

/-- Folded data `(0, ϖ)` with `ϖ` finite make `ϖ` a folded Lévy measure of `w`. -/
theorem isMaskLevyMeasure_of_isFoldedData {w : Measure ℝ} {P : SymLevyPair} (ha : P.a = 0)
    (hfin : IsFiniteMeasure P.ν) (hP : IsFoldedData w P) : IsMaskLevyMeasure w P.ν := by
  haveI := hfin
  exact ⟨hfin, P.ν_folded, fun ω => by rw [hP ω, symLevyPair_exponent_eq_integral P ha ω]⟩

/-- **Folded data are unique** (`lem:line-exponent-data`(1)). -/
theorem isFoldedData_unique {m : Measure ℝ} {P P' : SymLevyPair} (hP : IsFoldedData m P)
    (hP' : IsFoldedData m P') : P.a = P'.a ∧ P.ν = P'.ν :=
  line_exponent_data_1_unique P.exponent P P' (fun _ => rfl) fun ω => by
    have h := (hP ω).symm.trans (hP' ω)
    have h2 := Real.exp_injective (Complex.ofReal_injective h)
    linarith

/-- **The folded Lévy measure of a mask is unique.** -/
theorem IsMaskLevyMeasure.unique {w ϖ ϖ' : Measure ℝ} (h : IsMaskLevyMeasure w ϖ)
    (h' : IsMaskLevyMeasure w ϖ') : ϖ = ϖ' :=
  (isFoldedData_unique h.isFoldedData h'.isFoldedData).2

theorem isMaskLevyMeasure_dirac : IsMaskLevyMeasure (Measure.dirac 0) 0 :=
  ⟨inferInstance, by simp [ScaleSpace.IsFolded], fun ω => by simp [charFun_dirac]⟩

/-- **`ϖ = 0` exactly when `w = δ₀`.** -/
theorem IsMaskLevyMeasure.eq_zero_iff {w ϖ : Measure ℝ} [IsProbabilityMeasure w]
    (h : IsMaskLevyMeasure w ϖ) : ϖ = 0 ↔ w = Measure.dirac 0 := by
  constructor
  · rintro rfl
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [h.2.2 ω]
    simp [charFun_dirac]
  · rintro rfl
    exact h.unique isMaskLevyMeasure_dirac

/-- **A law with a folded Lévy measure is symmetric**, its transform being even. -/
theorem IsMaskLevyMeasure.isSymmetric {w ϖ : Measure ℝ} [IsProbabilityMeasure w]
    (h : IsMaskLevyMeasure w ϖ) : IsSymmetric w := by
  haveI : IsProbabilityMeasure (w.map fun x => -x) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  change w.map (fun x => -x) = w
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_map_neg_real, h.2.2, h.2.2]
  simp only [neg_mul, Real.cos_neg]

/-- **The transform is positive.** -/
theorem IsMaskLevyMeasure.charFun_pos {w ϖ : Measure ℝ} (h : IsMaskLevyMeasure w ϖ) (ω : ℝ) :
    0 < charFun w ω := by
  rw [h.2.2 ω]
  exact Complex.zero_lt_real.2 (Real.exp_pos _)

/-! ## The symmetric lift -/

theorem symLift_univ (ν : Measure ℝ) : symLift ν univ = ν univ := by
  rw [symLift, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply continuous_lineEmb.measurable MeasurableSet.univ,
    Measure.map_apply measurable_lineEmb_neg MeasurableSet.univ, preimage_univ, preimage_univ,
    smul_eq_mul,
    ← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

instance isFiniteMeasure_symLift (ν : Measure ℝ) [IsFiniteMeasure ν] :
    IsFiniteMeasure (symLift ν) :=
  ⟨by rw [symLift_univ]; exact measure_lt_top ν univ⟩

theorem symLift_map_neg' (ν : Measure ℝ) : (symLift ν).map (fun x => -x) = symLift ν := by
  have h := symLift_map_neg ν
  rwa [coe_neg_isometry] at h

theorem symLift_add (ν ν' : Measure ℝ) : symLift (ν + ν') = symLift ν + symLift ν' := by
  rw [symLift, symLift, symLift, Measure.map_add _ _ continuous_lineEmb.measurable,
    Measure.map_add _ _ measurable_lineEmb_neg, ← smul_add]
  congr 1
  abel

theorem symLift_smul (c : ℝ≥0∞) (ν : Measure ℝ) : symLift (c • ν) = c • symLift ν := by
  rw [symLift, symLift, Measure.map_smul, Measure.map_smul, ← smul_add, smul_comm]

theorem symLift_sum {ι : Type*} [Countable ι] (f : ι → Measure ℝ) :
    symLift (Measure.sum f) = Measure.sum fun i => symLift (f i) := by
  ext s hs
  rw [Measure.sum_apply _ hs]
  simp only [symLift, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.map_apply continuous_lineEmb.measurable hs, Measure.map_apply measurable_lineEmb_neg hs,
    Measure.sum_apply _ (continuous_lineEmb.measurable hs),
    Measure.sum_apply _ (measurable_lineEmb_neg hs)]
  rw [← ENNReal.tsum_add, ENNReal.tsum_mul_left]

/-- **The lift of `ϖ_1` is `ν*` of the lift**: `ν*(ϖ_s) = (ϖ_1)_s`. -/
theorem ladderNuStar_symLift (q : ℝ) (ϖ : Measure ℝ) :
    ladderNuStar q (symLift ϖ) = symLift (knotLevyMeasure q ϖ) := by
  rw [ladderNuStar, knotLevyMeasure, symLift_sum]
  congr 1
  funext m
  rw [symLift_map_mul]

/-- `ϖ_1` is folded. -/
theorem knotLevyMeasure_folded {q : ℝ} (hq : 0 < q) {ϖ : Measure ℝ}
    (hϖ : ScaleSpace.IsFolded ϖ) : ScaleSpace.IsFolded (knotLevyMeasure q ϖ) := by
  rw [ScaleSpace.IsFolded, knotLevyMeasure, Measure.sum_apply _ measurableSet_Iic,
    ENNReal.tsum_eq_zero]
  intro m
  rw [Measure.map_apply (measurable_const_mul _) measurableSet_Iic]
  refine measure_mono_null (fun v hv => ?_) hϖ
  simp only [mem_preimage, mem_Iic] at hv ⊢
  have hc : 0 < q ^ (-((m : ℤ) + 1)) := zpow_pos hq _
  by_contra hv'
  push Not at hv'
  linarith [mul_pos hc hv']

/-- **The logarithmic moment of the lift** is that of the measure. -/
theorem lintegral_posLog_symLift (ν : Measure ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.posLog ‖y‖) ∂symLift ν =
      ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ν := by
  rw [lintegral_symLift ν (by fun_prop) fun x => by rw [lineEmb_neg, norm_neg]]
  simp_rw [norm_lineEmb, Real.posLog_abs]

/-- `∫ (1 - cos⟨z, y⟩) ϖ_s(dy) = ∫ (1 - cos z₀v) ϖ(dv)` for a finite folded `ϖ`. -/
theorem integral_symLift_one_sub_cos (ϖ : Measure ℝ) (hfin : IsFiniteMeasure ϖ)
    (hfold : ScaleSpace.IsFolded ϖ) (z : Rd 1) :
    ∫ y, (1 - Real.cos ⟪z, y⟫) ∂symLift ϖ = ∫ v, (1 - Real.cos (z 0 * v)) ∂ϖ := by
  have h := SymLevyPair_toData_exponent (maskPair ϖ hfin hfold) z
  rw [maskPair_exponent] at h
  rw [← h]
  simp [SymLevyPair_toData, SymLevyData.exponent, pairExponent, maskPair, quad_zero]

/-- **A law with a folded Lévy measure is infinitely divisible**: its lift is the compound Poisson
law of the lift of `ϖ`, whose `n`-th root is the compound Poisson law of `ϖ/n`. -/
theorem IsMaskLevyMeasure.isInfinitelyDivisible {w ϖ : Measure ℝ} [IsProbabilityMeasure w]
    (h : IsMaskLevyMeasure w ϖ) : IsInfinitelyDivisible w := by
  haveI := h.1
  have hsym := symLift_map_neg' ϖ
  have hcp : w.map lineEmbL = cpLaw (symLift ϖ) := by
    haveI : IsProbabilityMeasure (w.map lineEmbL) :=
      Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable
    refine Measure.ext_of_charFun (funext fun z => ?_)
    rw [charFun_map_lineEmb, h.2.2, charFun_cpLaw_symm _ hsym,
      integral_symLift_one_sub_cos ϖ h.1 h.2.1]
  have hid : IsInfinitelyDivisible (cpLaw (symLift ϖ)) := by
    intro n hn
    have hn' : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne')
    haveI : IsFiniteMeasure ((n : ℝ≥0∞)⁻¹ • symLift ϖ) := ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top hn'.lt_top (measure_lt_top _ _)⟩
    have hsym' : ((n : ℝ≥0∞)⁻¹ • symLift ϖ).map (fun x => -x) = (n : ℝ≥0∞)⁻¹ • symLift ϖ := by
      rw [Measure.map_smul, hsym]
    refine ⟨cpLaw ((n : ℝ≥0∞)⁻¹ • symLift ϖ), inferInstance, ?_⟩
    haveI := ScaleSpace.isFiniteMeasure_convPow_Rd (cpLaw ((n : ℝ≥0∞)⁻¹ • symLift ϖ)) n
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [AffineHemigroup.charFun_convPow, charFun_cpLaw_symm _ hsym', charFun_cpLaw_symm _ hsym,
      integral_smul_measure, ← Complex.ofReal_pow, ← Real.exp_nat_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, smul_eq_mul]
    congr 2
    field_simp
  have h2 := isInfinitelyDivisible_map_lineProj (show IsInfinitelyDivisible (w.map lineEmbL) by
    rw [hcp]; exact hid)
  rwa [map_lineProj_lineEmb] at h2

/-! ## The data in `ℝ¹` -/

/-- **A law with folded data `P` lifts with the data of `P`.** -/
theorem isSymData_lineEmb_of_folded {m : Measure ℝ} {P : SymLevyPair} (hP : IsFoldedData m P) :
    IsSymData (m.map lineEmbL) (SymLevyPair_toData P) := fun z => by
  rw [charFun_map_lineEmb, hP, SymLevyPair_toData_exponent]

/-- **And back.** -/
theorem isFoldedData_of_lineEmb {m : Measure ℝ} {P : SymLevyPair}
    (hP : IsSymData (m.map lineEmbL) (SymLevyPair_toData P)) : IsFoldedData m P := fun ω => by
  have h := hP (lineEmb ω)
  rwa [charFun_map_lineEmb, lineEmb_apply_zero, SymLevyPair_toData_exponent,
    lineEmb_apply_zero] at h

/-- **The data of the lift of a mask** are `(0, ϖ_s)`. -/
theorem IsMaskLevyMeasure.lineData {w ϖ : Measure ℝ} [IsProbabilityMeasure w]
    (h : IsMaskLevyMeasure w ϖ) {D : SymLevyData 1} (hD : IsSymData (w.map lineEmbL) D) :
    D.A = 0 ∧ D.ν = symLift ϖ := by
  haveI : IsProbabilityMeasure (w.map lineEmbL) :=
    Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable
  obtain ⟨hA, hν⟩ := isSymData_unique hD (isSymData_lineEmb_of_folded h.isFoldedData)
  refine ⟨hA.trans ?_, hν⟩
  change (0 : ℝ) • (1 : Mat 1) = 0
  exact zero_smul _ _

/-- `P.a • 1 = 0` on `ℝ¹` forces `P.a = 0`. -/
theorem toData_A_eq_zero {P : SymLevyPair} (h : (SymLevyPair_toData P).A = 0) : P.a = 0 := by
  have h1 := congrFun (congrFun h 0) 0
  change (P.a • (1 : Mat 1)) 0 0 = 0 at h1
  simpa using h1

/-! ## Families -/

/-- **A family carrying a grid ladder**: its kernels form a symmetric family, `q`-covariant with
`S_q t = qt`, with the step `μ_{1,q} = w`. -/
theorem CarriesGridLadder.family {q : ℝ} {w : Measure ℝ} {Φ : ℝ → ℝ → (X →L[ℝ] X)}
    {S : ℝ → ℝ → ℝ} {μ : ℝ → ℝ → Measure ℝ} (h : CarriesGridLadder q w Φ S μ) :
    IsSymmetricFamily μ ∧ IsCovariantAt μ q (fun t => q * t) ∧ μ 1 q = w := by
  unfold CarriesGridLadder at h
  obtain ⟨hΦ, hcan, hμ, hstep⟩ := h
  have hq0 : 0 < q := by linarith [hΦ.one_lt]
  obtain ⟨hsym, hcovS⟩ := qCovariantLine_family hΦ hμ
  refine ⟨hsym, isCovariantAt_mul_of_eqOn hq0 hcovS hcan, ?_⟩
  have h0 := hstep 0
  rw [zpow_zero, zero_add, zpow_one, gridLadderStep, zpow_zero] at h0
  rw [h0]
  simp only [one_mul, Measure.map_id']

/-- **Covariance at `q` iterated on the steps**: `μ_{qⁿs, qⁿt} = D_{qⁿ} μ_{s,t}`, `n ∈ ℤ`. -/
theorem step_zpow_of_cov {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : ℝ → ℝ → Measure E} {q : ℝ} (hq : 1 < q)
    (hcov : IsCovariantAt μ q (fun t => q * t)) :
    ∀ (n : ℤ) (s t : ℝ), 0 ≤ s → s ≤ t →
      μ (q ^ n * s) (q ^ n * t) = (μ s t).map (fun x => (q ^ n) • x) := by
  have hq0 : 0 < q := by linarith
  have hstep : ∀ u v : ℝ, 0 ≤ u → u ≤ v → μ (q * u) (q * v) = (μ u v).map (fun x => q • x) :=
    fun u v hu huv => (hcov.2 u v hu huv).symm
  have hmm : ∀ (b c : ℝ) (m : Measure E),
      (m.map (fun x => c • x)).map (fun x => b • x) = m.map (fun x => (b * c) • x) := by
    intro b c m
    rw [Measure.map_map (continuous_const_smul b).measurable (continuous_const_smul c).measurable]
    congr 1
    ext x
    simp [smul_smul]
  intro n
  induction n using Int.induction_on with
  | zero => intro s t _ _; simp
  | succ n ih =>
    intro s t hs hst
    have hpos : 0 < q ^ (n : ℤ) := zpow_pos hq0 _
    have hu : 0 ≤ q ^ (n : ℤ) * s := mul_nonneg hpos.le hs
    have huv : q ^ (n : ℤ) * s ≤ q ^ (n : ℤ) * t := mul_le_mul_of_nonneg_left hst hpos.le
    have e : ∀ x : ℝ, q ^ ((n : ℤ) + 1) * x = q * (q ^ (n : ℤ) * x) := fun x => by
      rw [zpow_add_one₀ hq0.ne']; ring
    rw [e s, e t, hstep _ _ hu huv, ih s t hs hst, hmm, ← zpow_one_add₀ hq0.ne', add_comm]
  | pred n ih =>
    intro s t hs hst
    have hpos : 0 < q ^ (-(n : ℤ) - 1) := zpow_pos hq0 _
    have hu : 0 ≤ q ^ (-(n : ℤ) - 1) * s := mul_nonneg hpos.le hs
    have huv : q ^ (-(n : ℤ) - 1) * s ≤ q ^ (-(n : ℤ) - 1) * t :=
      mul_le_mul_of_nonneg_left hst hpos.le
    have h2 := hstep _ _ hu huv
    have h3 : ∀ x : ℝ, q * (q ^ (-(n : ℤ) - 1) * x) = q ^ (-(n : ℤ)) * x := fun x => by
      rw [← mul_assoc, ← zpow_one_add₀ hq0.ne']
      ring_nf
    rw [h3, h3, ih s t hs hst] at h2
    have h4 := congrArg (fun m => m.map (fun x => q⁻¹ • x)) h2
    simp only [hmm] at h4
    rw [inv_mul_cancel₀ hq0.ne'] at h4
    have h5 : (fun x : E => (1 : ℝ) • x) = id := by ext x; simp
    rw [h5, Measure.map_id] at h4
    rw [← h4, show q ^ (-(n : ℤ) - 1) = q⁻¹ * q ^ (-(n : ℤ)) by
      rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by ring, zpow_add₀ hq0.ne', zpow_neg_one]]

/-- **A family in `ℝ¹` with the ladder of the lifted mask reads back to a family carrying the grid
ladder**: its kernels `(μ_{s,t})₀` are those of a `CascadeCore` with (A8) at `q^ℤ` in the
canonical discrete gauge. -/
theorem carries_of_hasLadder {q : ℝ} (hq : 1 < q) {w : Measure ℝ} {μ1 : ℝ → ℝ → Measure (Rd 1)}
    (h : HasLadder q (w.map lineEmbL) μ1) :
    ∃ (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ),
      CarriesGridLadder q w Φ S (fun s t => (μ1 s t).map lineProjL) := by
  obtain ⟨hsym1, hcov1, hstep1⟩ := h
  have hsym := isSymmetricFamily_lineProj hsym1
  have hcov := isCovariantAt_lineProj hcov1
  obtain ⟨C, hC⟩ := line_axioms_kernels_2_family _ hsym
  obtain ⟨S, hS, hcan⟩ := (scaleCovariant_canonical_iff C hC hq).2 hcov
  refine ⟨C.Φ, S, ⟨hq, ⟨C, rfl⟩, hS⟩, hcan, hC, fun n => ?_⟩
  have h1 : (μ1 1 q).map lineProjL = w := by rw [hstep1, map_lineProj_lineEmb]
  have h2 := step_zpow_of_cov hq hcov n 1 q zero_le_one hq.le
  rw [mul_one, ← zpow_add_one₀ (by linarith : q ≠ 0), h1] at h2
  change (μ1 (q ^ n) (q ^ (n + 1))).map lineProjL = _
  rw [h2, gridLadderStep]
  rfl

/-- The kernels of a fully covariant family, lifted to `ℝ¹`, are `λ`-covariant for every
`λ > 0`. -/
theorem isFullyCovariantLaws_lineEmb (Fam : CascadeFamily) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsKernelFamily Fam.Φ μ) : IsFullyCovariantLaws (fun s t => (μ s t).map lineEmbL) := by
  intro lam hlam
  have hbij : IsIncreasingBijection (Fam.S lam) :=
    ⟨Fam.covariant.S_mapsTo lam hlam hlam, Fam.covariant.S_strictMonoOn lam hlam hlam,
      Fam.covariant.S_surjOn lam hlam hlam⟩
  exact ⟨Fam.S lam, isCovariantAt_lineEmb ((isCovariantAt_iff_map_mul μ lam (Fam.S lam)).2
    ⟨hbij, (line_axioms_kernels_3 Fam.Φ μ hμ hlam (Fam.S lam) hbij).1
      (Fam.covariant.scale lam hlam hlam)⟩)⟩

/-! ## The lattice `ξℤ` in `ℝ¹` -/

/-- **The lattice `ξℤ` of the line, in `ℝ¹`**: the `ℤ`-span of `ξe₀`. -/
noncomputable def lineLattice (ξ : ℝ) : Submodule ℤ (Rd 1) := Submodule.span ℤ {lineEmb ξ}

theorem mem_lineLattice {ξ : ℝ} {y : Rd 1} : y ∈ lineLattice ξ ↔ ∃ k : ℤ, y 0 = ξ * k := by
  rw [lineLattice, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [← lineEmb_zsmul, lineEmb_apply_zero]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← lineEmb_zsmul, ← hk, lineEmb_proj]⟩

theorem countable_lineLattice (ξ : ℝ) : (lineLattice ξ : Set (Rd 1)).Countable := by
  refine (Set.countable_range fun k : ℤ => k • lineEmb ξ).mono fun y hy => ?_
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hy
  exact ⟨k, rfl⟩

theorem discreteTopology_lineLattice {ξ : ℝ} (hξ : ξ ≠ 0) : DiscreteTopology (lineLattice ξ) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hopen : IsOpen ((Subtype.val : lineLattice ξ → Rd 1) ⁻¹' Metric.ball 0 |ξ|) :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  convert hopen using 1
  ext ⟨x, hx⟩
  simp only [mem_singleton_iff, mem_preimage, Metric.mem_ball, dist_zero_right]
  constructor
  · intro h0
    have hx0 : x = 0 := congrArg Subtype.val h0
    rw [hx0, norm_zero]
    exact abs_pos.2 hξ
  · intro hlt
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [norm_zsmul ℝ, norm_lineEmb] at hlt
    have hk : k = 0 := by
      by_contra hk
      have h1 : (1 : ℝ) ≤ ‖(k : ℝ)‖ := by
        rw [Real.norm_eq_abs, ← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hk
      have : |ξ| ≤ ‖(k : ℝ)‖ * |ξ| := le_mul_of_one_le_left (abs_nonneg ξ) h1
      linarith
    subst hk
    exact Subtype.ext (zero_smul ℤ _)

theorem span_lineLattice {ξ : ℝ} (hξ : ξ ≠ 0) :
    Submodule.span ℝ (lineLattice ξ : Set (Rd 1)) = ⊤ := by
  rw [lineLattice, Submodule.span_span_of_tower]
  refine eq_top_iff.2 fun y _ => Submodule.mem_span_singleton.2 ⟨y 0 / ξ, ?_⟩
  have e : (y 0 / ξ) • lineEmb ξ = lineEmb (y 0) := by
    simp only [lineEmb, smul_smul, div_mul_cancel₀ _ hξ]
  rw [e, lineEmb_proj]

/-- The lift of a law carried by `ξℤ` is carried by the lattice. -/
theorem map_lineEmb_lineLattice_compl (m : Measure ℝ) (ξ : ℝ) :
    (m.map lineEmbL) ((lineLattice ξ : Set (Rd 1))ᶜ) = m {x : ℝ | ¬∃ k : ℤ, x = ξ * k} := by
  rw [Measure.map_apply lineEmbL.continuous.measurable
    (countable_lineLattice ξ).measurableSet.compl]
  congr 1
  ext x
  simp only [mem_preimage, mem_compl_iff, SetLike.mem_coe, mem_lineLattice, lineEmbL_apply,
    lineEmb_apply_zero, mem_setOf_eq]

/-! ## Partial products and almost everywhere -/

theorem ladderProd_lineEmb (q : ℝ) (w : Measure ℝ) (M : ℕ) (z : Rd 1) :
    ladderProd q (w.map lineEmbL) M z = ladderPartialProduct q w M (z 0) := by
  unfold ladderProd ladderPartialProduct
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [charFun_map_lineEmb]
  simp

/-- **The partial convolutions** are probability laws with the partial products as transforms. -/
theorem charFun_ladderPartialConv (q : ℝ) (w : Measure ℝ) [IsProbabilityMeasure w] (M : ℕ) :
    IsProbabilityMeasure (ladderPartialConv q w M) ∧
      ∀ ω : ℝ, charFun (ladderPartialConv q w M) ω = ladderPartialProduct q w M ω := by
  have hl : ∀ m ∈ (List.range M).map (fun k : ℕ => w.map fun x => q ^ (-((k : ℤ) + 1)) * x),
      IsProbabilityMeasure m := by
    intro m hm
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hm
    exact Measure.isProbabilityMeasure_map (measurable_const_mul _).aemeasurable
  obtain ⟨hp, hc⟩ := convList_charFun_real _ hl
  have e : ladderPartialConv q w M =
      convList ((List.range M).map fun k : ℕ => w.map fun x => q ^ (-((k : ℤ) + 1)) * x) := by
    unfold ladderPartialConv
    congr 1
    simp only [bind_pure_comp]
    rw [List.map_eq_map, List.map_map]
    rfl
  rw [e]
  refine ⟨hp, fun ω => ?_⟩
  rw [hc, List.map_map, list_prod_map_range, ladderPartialProduct]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Function.comp_apply]
  rw [charFun_map_mul]

/-- **Almost everywhere in `ℝ¹` is almost everywhere on the line**: `x ↦ xe₀` preserves
Lebesgue measure. -/
theorem ae_lineEmb {p : Rd 1 → Prop} (h : ∀ᵐ z ∂(volume : Measure (Rd 1)), p z) :
    ∀ᵐ x ∂(volume : Measure ℝ), p (lineEmb x) := by
  have hmp := (PiLp.volume_preserving_toLp (Fin 1)).comp
    (volume_preserving_funUnique (Fin 1) ℝ).symm
  filter_upwards [hmp.quasiMeasurePreserving.ae h] with x hx
  convert hx using 1
  ext i
  rw [Subsingleton.elim i 0, lineEmb_apply_zero]
  rfl

/-! ## Clause (1) on a grid -/

/-- A mask is no point mass. -/
theorem IsGridMask.not_dirac {h : ℝ} {w : Measure ℝ} (hw : IsGridMask h w) (x : ℝ) :
    w ≠ Measure.dirac x := by
  intro hx
  obtain ⟨-, hsym, hne, -⟩ := hw
  have h1 : Measure.dirac (-x) = Measure.dirac x := by
    have h2 : w.map (fun x => -x) = w := hsym
    rwa [hx, Measure.map_dirac' measurable_neg] at h2
  have hxx : -x = x := by
    by_contra hc
    have h2 : Measure.dirac (-x) {x} = Measure.dirac x {x} := by rw [h1]
    rw [Measure.dirac_apply, Measure.dirac_apply_of_mem (mem_singleton x),
      indicator_of_notMem (show -x ∉ ({x} : Set ℝ) from hc)] at h2
    exact zero_ne_one h2
  have hx0 : x = 0 := by linarith
  exact hne (hx.trans (by rw [hx0]))

/-- **A mask of bounded support is not infinitely divisible** (`prop:no-bounded-step` at
`d = 1`). -/
theorem not_infinitelyDivisible_of_bounded {h : ℝ} {w : Measure ℝ} (hw : IsGridMask h w)
    (hbdd : ∃ R : ℝ, w {x : ℝ | R < |x|} = 0) : ¬ IsInfinitelyDivisible w := by
  haveI := hw.1
  haveI : IsProbabilityMeasure (w.map lineEmbL) :=
    Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable
  intro hid
  refine (no_bounded_step (d := 1) (w.map lineEmbL) ?_ ?_).1
    (isInfinitelyDivisible_map_lineEmb hid)
  · obtain ⟨R, hR⟩ := hbdd
    refine ⟨R, ?_⟩
    rw [Measure.map_apply lineEmbL.continuous.measurable
      (measurableSet_lt measurable_const measurable_norm)]
    convert hR using 2
    ext x
    simp [lineEmbL_apply, norm_lineEmb]
  · intro x hx
    apply hw.not_dirac (x 0)
    rw [← map_lineProj_lineEmb w, hx, Measure.map_dirac' lineProjL.continuous.measurable,
      lineProjL_apply]

/-- **An infinitely divisible mask is compound Poisson**, with a folded Lévy measure `ϖ ≠ 0`
carried by `hℤ_{>0}` (`lem:lattice-infinitely-divisible` at `d = 1`). -/
theorem exists_maskLevyMeasure {h : ℝ} (hh : 0 < h) {w : Measure ℝ} (hw : IsGridMask h w)
    (hid : IsInfinitelyDivisible w) :
    ∃ ϖ : Measure ℝ, IsMaskLevyMeasure w ϖ ∧ ϖ ≠ 0 ∧
      ϖ {v : ℝ | ¬∃ n : ℤ, 0 < n ∧ v = h * n} = 0 := by
  obtain ⟨hprob, hsym, hne, hcarr⟩ := hw
  haveI := hprob
  haveI : IsProbabilityMeasure (w.map lineEmbL) :=
    Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable
  obtain ⟨P, hP⟩ := line_exponent_data_1_converse w hsym hid
  have hD := isSymData_lineEmb_of_folded (P := P) hP
  haveI := discreteTopology_lineLattice hh.ne'
  haveI : IsZLattice ℝ (lineLattice h) := ⟨span_lineLattice hh.ne'⟩
  have hcarr1 : (w.map lineEmbL) ((lineLattice h : Set (Rd 1))ᶜ) = 0 := by
    rw [map_lineEmb_lineLattice_compl]
    exact hcarr
  obtain ⟨hA, hfin, hνΓ⟩ := lattice_infinitely_divisible (w.map lineEmbL)
    (isInfinitelyDivisible_map_lineEmb hid) _ (SymLevyData.hasTriplet hD) (lineLattice h) hcarr1
  have ha : P.a = 0 := by
    have h1 := congrFun (congrFun hA 0) 0
    change ((2 : ℝ) • (P.a • (1 : Mat 1))) 0 0 = 0 at h1
    simpa using h1
  haveI hfinL : IsFiniteMeasure (symLift P.ν) := hfin
  have hfinP : IsFiniteMeasure P.ν := ⟨by
    have h3 : P.ν univ = 2 * symLift P.ν ((fun y : Rd 1 => y 0) ⁻¹' (univ ∩ Ioi 0)) := by
      rw [symLift_apply_pos P.ν_folded MeasurableSet.univ, ← mul_assoc,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    rw [h3]
    exact ENNReal.mul_lt_top ENNReal.ofNat_lt_top (measure_lt_top _ _)⟩
  have hmask := isMaskLevyMeasure_of_isFoldedData ha hfinP hP
  refine ⟨P.ν, hmask, fun h0 => hne (hmask.eq_zero_iff.1 h0), ?_⟩
  set C : Set ℝ := {v : ℝ | ¬∃ n : ℤ, 0 < n ∧ v = h * n} with hC
  have hCm : MeasurableSet C := by
    have hc : Cᶜ.Countable := (Set.countable_range fun n : ℤ => h * n).mono fun v hv => by
      simp only [hC, mem_compl_iff, mem_setOf_eq, not_not] at hv
      obtain ⟨n, -, rfl⟩ := hv
      exact ⟨n, rfl⟩
    simpa using hc.measurableSet.compl
  have h1 := symLift_apply_pos P.ν_folded hCm
  have h2 : symLift P.ν ((fun y : Rd 1 => y 0) ⁻¹' (C ∩ Ioi 0)) = 0 := by
    refine measure_mono_null (fun y hy => ?_) hνΓ
    rintro ⟨hyΓ, hy0⟩
    obtain ⟨k, hk⟩ := mem_lineLattice.1 hyΓ
    have hpos : 0 < y 0 := hy.2
    apply hy.1
    refine ⟨k, ?_, hk⟩
    by_contra hk0
    push Not at hk0
    have : h * (k : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh.le (by exact_mod_cast hk0)
    linarith
  rw [h2] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left (by simp)

end Pyramids
