/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Price.NotIsotropic
import Pyramids.Line.GeometricMask
import AffineHemigroup.FrameFamilies

/-!
# `prop:grid-pyramid-not-isotropic`(3): the frame Matérn pyramid

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:grid-pyramid-not-isotropic`. Wave 3g:
`grid_pyramid_not_isotropic_3` moved here from `PyramidsSkeleton.Ch05Price`, its statement
unchanged.

## The route

* **The data of the mask.** `w = (λ^L_a)^{⊗d}` has `ŵ(ω) = ∏ᵢ λ̂^L_a(ωᵢ)`. Each factor is
  `exp(-∫(1 - cos ωᵢv) ϖ(dv))` with the folded Lévy measure `ϖ` of `λ^L_a`
  (`isMaskLevyMeasure_geom`, `prop:grid-pyramids-infinitely-divisible`(4)), and that integral is
  the one of its symmetric lift `ϖ_s` on `ℝ¹` (`integral_symLift_one_sub_cos`). So `w` has the
  data `(0, ν_w)`, `ν_w := ∑ᵢ (ι_i)_* ϖ_s` with `ι_i(y) = y₀ eᵢ`: the sum over the axes, no
  series manipulation.
* **The mask** is a probability law with a real transform (so symmetric), not `δ₀` (`ν_w ≠ 0`,
  A39(ii)), and carried by `hℤ^d` coordinatewise.
* **Exactness**: `prop:ladder-knot-kernel`(2) (`ladder_knot_kernel_2`) with the logarithmic moment
  of `ϖ` (`log₊ x ≤ x`, a geometric series) gives a family with the ladder.
* **Every family carrying it**: the product formula of clause (1) (`CarriesLatticeLadder.product`)
  with the factors written out (`geom_symbol_eq_inv`); the data of the knot kernel
  (`CarriesLatticeLadder.knot_data`), `ν_1 = ν*`, which is (`eq:frame-levy`) once the lift of `ϖ`
  is written as point masses at `±kh` and the sum over `n ∈ ℤ ∖ {0}` is split at the sign.
* **The symmetry group**: a signed permutation fixes every partial product (the factors are even
  and permuted), hence `μ̂_1`, hence every knot kernel. Conversely a symmetry `R` of a knot kernel
  is one of `μ_1` and fixes `ν_1` (`levy_map_eq_of_push_eq`); `R((h/q)eᵢ)` is an atom of `ν_1` of
  norm `h/q`, so a point `±(h/q)e_j` of the axes; `R eᵢ = ±e_{σ(i)}` with `σ` injective.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace Matrix

variable {d : ℕ}

/-! ## The axes -/

/-- **`ι_i(y) := y₀ eᵢ`**, the line `ℝ¹` onto the `i`-th axis. -/
noncomputable def axisEmb (i : Fin d) : Rd 1 →L[ℝ] Rd d := lineProjL.smulRight (ebasis i)

theorem axisEmb_apply (i : Fin d) (y : Rd 1) : axisEmb i y = (y 0) • ebasis i := rfl

theorem ebasis_apply (i j : Fin d) : ebasis i j = if j = i then 1 else 0 := by
  simp [ebasis]

theorem lineEmb_apply_zero (x : ℝ) : lineEmb x 0 = x := by
  simp [lineEmb, ebasis]

theorem eq_zero_of_apply_zero {y : Rd 1} (h : y 0 = 0) : y = 0 := by
  ext i
  rw [Subsingleton.elim i 0, h]
  rfl

theorem inner_axisEmb (ω : Rd d) (i : Fin d) (y : Rd 1) :
    ⟪ω, axisEmb i y⟫ = ⟪lineEmb (ω i), y⟫ := by
  rw [axisEmb_apply, lineEmb, inner_smul_right, inner_smul_left]
  simp [ebasis, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  ring

/-! ## The mask -/

/-- The tensor power of probability laws is a probability law with the product transform. -/
theorem tensorPow_charFun {m : Measure ℝ} [IsProbabilityMeasure m] :
    IsProbabilityMeasure (tensorPow d m) ∧
      ∀ ω : Rd d, charFun (tensorPow d m) ω = ∏ i, charFun m (ω i) :=
  ⟨isProbabilityMeasure_prodLaw (fun _ => m) fun _ => inferInstance,
    fun ω => charFun_prodLaw (fun _ => m) (fun _ => inferInstance) ω⟩

section Mask

variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
include ha0 ha1

/-- The folded Lévy measure of `λ^L_a` is finite and folded. -/
theorem geom_fin_fold (h : ℝ) (hh : 0 < h) :
    IsFiniteMeasure (geomLevyMeasure a h) ∧ ScaleSpace.IsFolded (geomLevyMeasure a h) :=
  ⟨(isMaskLevyMeasure_geom ha0 ha1 hh).1, (isMaskLevyMeasure_geom ha0 ha1 hh).2.1⟩

end Mask

/-- **`ν_w := ∑ᵢ (ι_i)_* ϖ_s`**, the Lévy measure of the frame mask. -/
noncomputable def frameMaskNu (d : ℕ) (a h : ℝ) : Measure (Rd d) :=
  Measure.sum fun i : Fin d => (symLift (geomLevyMeasure a h)).map (axisEmb i)

theorem frameMaskNu_univ {a h : ℝ} :
    frameMaskNu d a h univ = ∑ _i : Fin d, geomLevyMeasure a h univ := by
  rw [frameMaskNu, Measure.sum_fintype, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_apply (axisEmb i).continuous.measurable MeasurableSet.univ, preimage_univ,
    symLift_univ]

section Data

variable {a h : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hh : 0 < h)
include ha0 ha1 hh

theorem symLift_geom_zero : symLift (geomLevyMeasure a h) {0} = 0 :=
  (SymLevyPair_toData (maskPair _ (geom_fin_fold ha0 ha1 h hh).1
    (geom_fin_fold ha0 ha1 h hh).2)).ν_zero

theorem isFiniteMeasure_frameMaskNu : IsFiniteMeasure (frameMaskNu d a h) := by
  haveI := (geom_fin_fold ha0 ha1 h hh).1
  exact ⟨by
    rw [frameMaskNu_univ]
    exact ENNReal.sum_lt_top.2 fun _ _ => measure_lt_top _ _⟩

/-- **The data `(0, ν_w)` of the frame mask.** -/
noncomputable def frameData : SymLevyData d where
  A := 0
  ν := frameMaskNu d a h
  A_posSemidef := Matrix.PosSemidef.zero
  ν_zero := by
    rw [frameMaskNu, Measure.sum_apply _ (measurableSet_singleton 0), ENNReal.tsum_eq_zero]
    intro i
    rw [Measure.map_apply (axisEmb i).continuous.measurable (measurableSet_singleton 0)]
    refine measure_mono_null (fun y hy => ?_) (symLift_geom_zero ha0 ha1 hh)
    have hy' : (y 0) • ebasis i = 0 := hy
    have h0 : y 0 = 0 := by
      have := congrArg (fun z : Rd d => z i) hy'
      simpa [ebasis] using this
    exact eq_zero_of_apply_zero h0
  ν_integrable := by
    haveI := isFiniteMeasure_frameMaskNu (d := d) ha0 ha1 hh
    refine ne_top_of_le_ne_top (measure_ne_top (frameMaskNu d a h) univ) ?_
    calc ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂frameMaskNu d a h ≤ ∫⁻ _, 1 ∂frameMaskNu d a h :=
          lintegral_mono fun x => ENNReal.ofReal_le_one.2 (min_le_right _ _)
      _ = _ := lintegral_one
  ν_symm := by
    rw [frameMaskNu, Measure.map_sum measurable_neg.aemeasurable]
    congr 1
    funext i
    rw [Measure.map_map measurable_neg (axisEmb i).continuous.measurable]
    have e : (fun x : Rd d => -x) ∘ axisEmb i = axisEmb i ∘ fun y => -y := by
      funext y
      simp
    rw [e, ← Measure.map_map (axisEmb i).continuous.measurable measurable_neg,
      symLift_map_neg']

theorem frameData_A : (frameData (d := d) ha0 ha1 hh).A = 0 := rfl

theorem frameData_ν : (frameData (d := d) ha0 ha1 hh).ν = frameMaskNu d a h := rfl

/-- **The frame mask has the data `(0, ν_w)`.** -/
theorem isSymData_frame :
    IsSymData (tensorPow d (gridLaw h (geomKernel a))) (frameData ha0 ha1 hh) := by
  haveI := isProbabilityMeasure_geomMask ha0 ha1 h
  haveI := isFiniteMeasure_frameMaskNu (d := d) ha0 ha1 hh
  obtain ⟨hfin, hfold⟩ := geom_fin_fold ha0 ha1 h hh
  intro ω
  rw [tensorPow_charFun.2 ω]
  have hint : Integrable (fun x : Rd d => 1 - Real.cos ⟪ω, x⟫) (frameMaskNu d a h) :=
    Integrable.of_bound (by fun_prop) 2 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [Real.cos_le_one ⟪ω, x⟫, Real.neg_one_le_cos ⟪ω, x⟫])
  have hexp : (frameData (d := d) ha0 ha1 hh).exponent ω =
      ∑ i, ∫ v, (1 - Real.cos (ω i * v)) ∂geomLevyMeasure a h := by
    simp only [SymLevyData.exponent, pairExponent, frameData, quad_zero, zero_add]
    rw [frameMaskNu] at hint ⊢
    rw [integral_sum_measure hint, tsum_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_map (axisEmb i).continuous.aemeasurable (by fun_prop)]
    simp_rw [inner_axisEmb]
    rw [integral_symLift_one_sub_cos _ hfin hfold, lineEmb_apply_zero]
  rw [hexp, ← Finset.sum_neg_distrib, Real.exp_sum, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (isMaskLevyMeasure_geom ha0 ha1 hh).2.2 (ω i)

/-- **The frame mask** is a mask on `hℤ^d` (`d ≥ 1`). -/
theorem isLatticeMask_frame (hd : 1 ≤ d) :
    IsLatticeMask (gridSet d h) (tensorPow d (gridLaw h (geomKernel a))) := by
  haveI := isProbabilityMeasure_geomMask ha0 ha1 h
  obtain ⟨hprob, hcf⟩ := tensorPow_charFun (d := d) (m := gridLaw h (geomKernel a))
  haveI := hprob
  have hD := isSymData_frame (d := d) ha0 ha1 hh
  refine ⟨hprob, map_neg_eq_of_charFun_im fun ω => ?_, fun h0 => ?_, ?_⟩
  · rw [hD ω, Complex.ofReal_im]
  · -- not `δ₀`: its data would vanish
    have hz : IsSymData (Measure.dirac (0 : Rd d)) SymLevyData.zero := fun ω => by
      rw [charFun_dirac, SymLevyData.zero_exponent]
      simp
    rw [h0] at hD
    have hν := (isSymData_unique hD hz).2
    rw [frameData_ν] at hν
    set i0 : Fin d := ⟨0, by omega⟩
    have hle : (symLift (geomLevyMeasure a h)).map (axisEmb i0) ≤ frameMaskNu d a h :=
      Measure.le_sum (fun i : Fin d => (symLift (geomLevyMeasure a h)).map (axisEmb i)) i0
    have h1 := Measure.le_iff'.1 hle univ
    rw [hν, Measure.map_apply (axisEmb i0).continuous.measurable MeasurableSet.univ,
      preimage_univ, symLift_univ] at h1
    exact geomLevyMeasure_ne_zero ha0 h (Measure.measure_univ_eq_zero.1
      (nonpos_iff_eq_zero.1 (by simpa [SymLevyData.zero] using h1)))
  · -- carried by `hℤ^d`
    have hmeas : MeasurableSet (gridSet d h)ᶜ := by
      have hc : (gridSet d h).Countable := by
        have : gridSet d h = range (latticePt h) := by
          ext x
          simp [gridSet, eq_comm]
        rw [this]
        exact countable_range _
      exact hc.measurableSet.compl
    rw [tensorPow, Measure.map_apply (PiLp.continuous_toLp 2 _).measurable hmeas]
    have hsub : (WithLp.toLp 2 : (Fin d → ℝ) → Rd d) ⁻¹' (gridSet d h)ᶜ ⊆
        ⋃ i : Fin d, Function.eval i ⁻¹' {x : ℝ | ¬∃ n : ℤ, x = h * n} := by
      intro x hx
      by_contra hcon
      simp only [mem_iUnion, mem_preimage, mem_setOf_eq, Function.eval] at hcon
      push Not at hcon
      choose n hn using hcon
      apply hx
      refine ⟨n, ?_⟩
      ext i
      simp [latticePt, hn i]
    refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
    exact Measure.pi_eval_preimage_null _ (gridLaw_apply_not_mulInt h _)

/-- **The logarithmic moment** of `ν_w`. -/
theorem lintegral_posLog_frameMaskNu :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂frameMaskNu d a h < ⊤ := by
  rw [frameMaskNu, lintegral_sum_measure, tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [lintegral_map (by fun_prop) (axisEmb i).continuous.measurable]
  have hn : ∀ y : Rd 1, ‖axisEmb i y‖ = ‖y‖ := by
    intro y
    rw [axisEmb_apply, norm_smul]
    have h1 : ‖(ebasis i : Rd d)‖ = 1 := by simp [ebasis]
    have h2 : ‖y‖ = |y 0| := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
        Real.sqrt_sq_eq_abs]
    rw [h1, mul_one, h2, Real.norm_eq_abs]
  simp_rw [hn]
  rw [lintegral_posLog_symLift, geomLevyMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have hb : ∀ k : ℕ, ENNReal.ofReal (2 * a ^ (k + 1) / (k + 1)) *
      ENNReal.ofReal (Real.posLog (h * (k + 1))) ≤ ENNReal.ofReal (2 * h * a ^ (k + 1)) := by
    intro k
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hp : Real.posLog (h * (k + 1)) ≤ h * (k + 1) := by
      rw [Real.posLog, max_le_iff]
      exact ⟨by positivity, Real.log_le_self (by positivity)⟩
    calc 2 * a ^ (k + 1) / (k + 1) * Real.posLog (h * (k + 1))
        ≤ 2 * a ^ (k + 1) / (k + 1) * (h * (k + 1)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 2 * h * a ^ (k + 1) := by field_simp
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hb) ?_
  have hs : Summable fun k : ℕ => 2 * h * a ^ (k + 1) :=
    ((summable_geometric_of_lt_one ha0.le ha1).mul_left (2 * h * a)).congr fun k => by ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
  exact ENNReal.ofReal_lt_top

end Data

/-! ## The Lévy measure of the knot kernel (`eq:frame-levy`) -/

/-- **`ϖ_s` as point masses**: `∑_{k ≥ 0} (a^{k+1}/(k+1)) (δ_{(k+1)h} + δ_{-(k+1)h})`. -/
theorem symLift_geom_apply (a h : ℝ) {s : Set (Rd 1)} (hs : MeasurableSet s) :
    symLift (geomLevyMeasure a h) s = ∑' k : ℕ, ENNReal.ofReal (a ^ (k + 1) / (k + 1)) *
      (s.indicator 1 (lineEmb (h * (k + 1))) + s.indicator 1 (lineEmb (-(h * (k + 1))))) := by
  rw [symLift, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply continuous_lineEmb.measurable hs,
    Measure.map_apply measurable_lineEmb_neg hs, geomLevyMeasure,
    Measure.sum_apply _ (continuous_lineEmb.measurable hs),
    Measure.sum_apply _ (measurable_lineEmb_neg hs), ← ENNReal.tsum_add, smul_eq_mul,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (continuous_lineEmb.measurable hs),
    Measure.dirac_apply' _ (measurable_lineEmb_neg hs)]
  have e2 : ENNReal.ofReal (2 * a ^ (k + 1) / (k + 1)) =
      2 * ENNReal.ofReal (a ^ (k + 1) / (k + 1)) := by
    rw [mul_div_assoc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [e2, ← mul_add, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero
    ENNReal.ofNat_ne_top, one_mul]
  rfl

/-- **(`eq:frame-levy`) is `ν*` of the frame mask.** -/
theorem frameKnotLevy_eq (a q h : ℝ) :
    frameKnotLevy d q h a = ladderNuStar q (frameMaskNu d a h) := by
  ext s hs
  have hsm : ∀ c : ℝ, Measurable fun x : Rd d => c • x := fun c => measurable_const_smul c
  rw [ladderNuStar, Measure.sum_apply _ hs, frameKnotLevy, Measure.sum_apply _ hs]
  simp_rw [Measure.map_apply (hsm _) hs]
  simp_rw [frameMaskNu, Measure.sum_apply _ (hsm _ hs),
    Measure.map_apply (axisEmb _).continuous.measurable (hsm _ hs),
    symLift_geom_apply a h ((hsm _ hs).preimage (axisEmb _).continuous.measurable)]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun i => ?_
  rw [Measure.sum_apply _ hs]
  refine tsum_congr fun m => ?_
  rw [Measure.sum_apply _ hs, tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable,
    tsum_eq_zero_add' ENNReal.summable]
  rw [if_pos (by simp), Measure.coe_zero, Pi.zero_apply, zero_add, ← ENNReal.tsum_add]
  refine tsum_congr fun k => ?_
  have hk1 : ((k : ℤ) + 1) ≠ 0 := by omega
  have hk2 : (-((k : ℤ) + 1)) ≠ 0 := by omega
  have hnat1 : ((k : ℤ) + 1).natAbs = k + 1 := by omega
  have hnat2 : (-((k : ℤ) + 1)).natAbs = k + 1 := by omega
  rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring, if_neg hk1, if_neg hk2,
    Measure.smul_apply, Measure.smul_apply, hnat1, hnat2, Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ hs, smul_eq_mul, smul_eq_mul, ← mul_add]
  have hc1 : (((k : ℤ) + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hc2 : ((-((k : ℤ) + 1) : ℤ) : ℝ) = -((k : ℝ) + 1) := by push_cast; ring
  have hn1 : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
  have hp1 : q ^ (-((m : ℤ) + 1)) • axisEmb i (lineEmb (h * (k + 1))) =
      ((((k : ℤ) + 1 : ℤ) : ℝ) * h * q ^ (-((m : ℤ) + 1))) • ebasis i := by
    rw [axisEmb_apply, lineEmb_apply_zero, smul_smul, hc1]
    congr 1
    ring
  have hp2 : q ^ (-((m : ℤ) + 1)) • axisEmb i (lineEmb (-(h * (k + 1)))) =
      (((-((k : ℤ) + 1) : ℤ) : ℝ) * h * q ^ (-((m : ℤ) + 1))) • ebasis i := by
    rw [axisEmb_apply, lineEmb_apply_zero, smul_smul, hc2]
    congr 1
    ring
  rw [hn1]
  congr 2
  · change _ = s.indicator 1 (q ^ (-((m : ℤ) + 1)) • axisEmb i (lineEmb (h * (k + 1))))
    rw [hp1]
  · change _ = s.indicator 1 (q ^ (-((m : ℤ) + 1)) • axisEmb i (lineEmb (-(h * (k + 1)))))
    rw [hp2]

/-- **(`eq:frame-levy`) is carried by the axes.** -/
theorem frameKnotLevy_axes (q h a : ℝ) : frameKnotLevy d q h a (axesSet d)ᶜ = 0 := by
  rw [frameKnotLevy, Measure.sum_apply_eq_zero]
  intro i
  rw [Measure.sum_apply_eq_zero]
  intro m
  rw [Measure.sum_apply_eq_zero]
  intro n
  split_ifs
  · rfl
  · rw [Measure.smul_apply, Measure.dirac_apply, indicator_of_notMem, smul_zero]
    exact fun h => h ⟨i, _, rfl⟩

/-- **The atoms `(h/q) eᵢ`** of (`eq:frame-levy`). -/
theorem frameKnotLevy_atom {q h a : ℝ} (ha0 : 0 < a) (i : Fin d) :
    frameKnotLevy d q h a {(h * q⁻¹) • ebasis i} ≠ 0 := by
  have h1 := Measure.le_sum (fun i : Fin d => Measure.sum fun m : ℕ => Measure.sum fun n : ℤ =>
    if n = 0 then (0 : Measure (Rd d)) else
      ENNReal.ofReal (a ^ n.natAbs / n.natAbs) •
        Measure.dirac (((n : ℝ) * h * q ^ (-((m : ℤ) + 1))) • ebasis i)) i
  have h2 := Measure.le_sum (fun m : ℕ => Measure.sum fun n : ℤ =>
    if n = 0 then (0 : Measure (Rd d)) else
      ENNReal.ofReal (a ^ n.natAbs / n.natAbs) •
        Measure.dirac (((n : ℝ) * h * q ^ (-((m : ℤ) + 1))) • ebasis i)) 0
  have h3 := Measure.le_sum (fun n : ℤ =>
    if n = 0 then (0 : Measure (Rd d)) else
      ENNReal.ofReal (a ^ n.natAbs / n.natAbs) •
        Measure.dirac (((n : ℝ) * h * q ^ (-(((0 : ℕ) : ℤ) + 1))) • ebasis i)) 1
  have hle := Measure.le_iff'.1 (h3.trans (h2.trans h1)) {(h * q⁻¹) • ebasis i}
  rw [← frameKnotLevy] at hle
  intro h0
  rw [h0, if_neg one_ne_zero, Measure.smul_apply, Measure.dirac_apply, indicator_of_mem] at hle
  · simp only [Int.natAbs_one, pow_one, Nat.cast_one, div_one, Pi.one_apply, smul_eq_mul,
      mul_one, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
    linarith
  · simp [zpow_neg]

/-! ## Signed permutations -/

/-- The entry of a matrix is a coordinate of its column. -/
theorem lin_ebasis_apply (R : Mat d) (i j : Fin d) : lin R (ebasis j) i = R i j := by
  rw [ofLp_lin]
  simp [ebasis, Matrix.mulVec, dotProduct]

theorem signedPerm_transpose_apply {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ} (ω : Rd d)
    (j : Fin d) :
    lin (Matrix.transpose (Matrix.of fun i j => if i = σ j then s j else 0)) ω j =
      s j * ω (σ j) := by
  rw [ofLp_lin]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

theorem signedPerm_mem_orthSet {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ}
    (hs : ∀ j, s j = 1 ∨ s j = -1) :
    (Matrix.of fun i j => if i = σ j then s j else 0) ∈ orthSet d := by
  change _ ∈ Matrix.orthogonalGroup (Fin d) ℝ
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp only [Equiv.apply_symm_apply, if_true]
    by_cases hik : i = k
    · subst hik
      simp only [if_true]
      rcases hs (σ.symm i) with h | h <;> rw [h] <;> norm_num
    · have : k ≠ i := Ne.symm hik
      simp [this, hik]
  · intro j _ hj
    have : i ≠ σ j := fun h => hj (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · simp


/-- **A symmetry in transforms**: `R_*m = m` iff `m̂(Rᵀω) = m̂(ω)` for every `ω`. -/
theorem push_eq_iff_charFun {m : Measure (Rd d)} [IsProbabilityMeasure m] (R : Mat d) :
    push R m = m ↔ ∀ ω : Rd d, charFun m (lin Rᵀ ω) = charFun m ω := by
  haveI : IsProbabilityMeasure (push R m) :=
    Measure.isProbabilityMeasure_map (lin R).continuous.aemeasurable
  constructor
  · intro h ω
    rw [← charFun_map_lin, ← push, h]
  · intro h
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [push, charFun_map_lin, h]

/-- A dilate has the symmetries of the law: `m̂_c(ξ) = m̂(cξ)`, `c ≠ 0`. -/
theorem invariant_dilate_iff {φ ψ : Rd d → ℂ} {c : ℝ} (hc : c ≠ 0)
    (h : ∀ ξ, ψ ξ = φ (c • ξ)) (R : Mat d) :
    (∀ ω, ψ (lin Rᵀ ω) = ψ ω) ↔ ∀ ω, φ (lin Rᵀ ω) = φ ω := by
  constructor
  · intro hψ ω
    have h1 := hψ (c⁻¹ • ω)
    rw [h, h, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul] at h1
    simpa [smul_smul, mul_inv_cancel₀ hc] using h1
  · intro hφ ω
    rw [h, h, ← map_smul, hφ]

section Family

variable {a h q : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hh : 0 < h)
include ha0 ha1 hh

omit hh in
/-- **The partial products of the frame mask**, written out. -/
theorem ladderProd_frame (M : ℕ) (ω : Rd d) :
    ladderProd q (tensorPow d (gridLaw h (geomKernel a))) M ω =
      ∏ m ∈ Finset.range M, ∏ i : Fin d,
        ((((1 + 2 * a / (1 - a) ^ 2 *
          (1 - Real.cos (q ^ (-((m : ℤ) + 1)) * h * ω i)))⁻¹ : ℝ)) : ℂ) := by
  haveI := isProbabilityMeasure_geomMask ha0 ha1 h
  rw [ladderProd]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [tensorPow_charFun.2]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [PiLp.smul_apply, smul_eq_mul, charFun_geomMask ha0 ha1, geom_symbol_eq_inv ha1,
    ← mul_div_assoc, show h * (q ^ (-((m : ℤ) + 1)) * ω i) = q ^ (-((m : ℤ) + 1)) * h * ω i by
      ring]

/-- **A signed permutation fixes the frame knot kernel's transform**: the factors are even in each
coordinate and are permuted. -/
theorem frame_knot_signedPerm (hd : 1 ≤ d) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder q (tensorPow d (gridLaw h (geomKernel a))) μ)
    {σ : Equiv.Perm (Fin d)} {s : Fin d → ℝ} (hs : ∀ j, s j = 1 ∨ s j = -1) (ω : Rd d) :
    charFun (μ 0 1) (lin (Matrix.transpose (Matrix.of fun i j => if i = σ j then s j else 0)) ω)
      = charFun (μ 0 1) ω := by
  haveI := isProbabilityMeasure_geomMask ha0 ha1 h
  haveI := (isLatticeMask_frame (d := d) ha0 ha1 hh hd).1
  set F : ℕ → ℝ → ℂ := fun m x =>
    ((((1 + 2 * a / (1 - a) ^ 2 * (1 - Real.cos (q ^ (-((m : ℤ) + 1)) * h * x)))⁻¹ : ℝ)) : ℂ)
    with hF
  have hP : ∀ M, ladderProd q (tensorPow d (gridLaw h (geomKernel a))) M
      (lin (Matrix.transpose (Matrix.of fun i j => if i = σ j then s j else 0)) ω) =
      ladderProd q (tensorPow d (gridLaw h (geomKernel a))) M ω := by
    intro M
    rw [ladderProd_frame ha0 ha1, ladderProd_frame ha0 ha1]
    refine Finset.prod_congr rfl fun m _ => ?_
    change ∏ j, F m _ = ∏ i, F m (ω i)
    simp_rw [signedPerm_transpose_apply]
    have heven : ∀ j, F m (s j * ω (σ j)) = F m (ω (σ j)) := by
      intro j
      rcases hs j with h1 | h1
      · rw [h1, one_mul]
      · simp only [hF, h1, neg_one_mul, mul_neg, Real.cos_neg]
    simp_rw [heven]
    exact Equiv.prod_comp σ fun i => F m (ω i)
  have h1 := (hμ.product hd (lin (Matrix.transpose
    (Matrix.of fun i j => if i = σ j then s j else 0)) ω)).1
  simp_rw [hP] at h1
  exact tendsto_nhds_unique h1 (hμ.product hd ω).1

end Family

/-- **`prop:grid-pyramid-not-isotropic`(3), the frame Matérn pyramid.** For `0 < a < 1`, `h > 0`
and every `q > 1`, `(λ^L_a)^{⊗d}` is a mask on `hℤ^d` whose grid pyramid is exact; every family
carrying it has the knot kernel `∏_i ∏_{m ≥ 1} [1 + 2a(1-a)^{-2}(1 - cos(q^{-m}hωᵢ))]⁻¹`, the Lévy
measure (`eq:frame-levy`), carried by the coordinate axes, and at every knot the hyperoctahedral
symmetry group. -/
theorem grid_pyramid_not_isotropic_3 (hd : 1 ≤ d) {h a : ℝ} (hh : 0 < h) (ha0 : 0 < a)
    (ha1 : a < 1) {q : ℝ} (hq : 1 < q) :
    IsLatticeMask (gridSet d h) (tensorPow d (gridLaw h (geomKernel a))) ∧
      IsExactLatticePyramid q (tensorPow d (gridLaw h (geomKernel a))) ∧
      ∀ μ : ℝ → ℝ → Measure (Rd d),
        CarriesLatticeLadder q (tensorPow d (gridLaw h (geomKernel a))) μ →
        (∀ ω : Rd d, Tendsto (fun M : ℕ => ∏ m ∈ Finset.range M, ∏ i : Fin d,
            ((((1 + 2 * a / (1 - a) ^ 2 *
              (1 - Real.cos (q ^ (-((m : ℤ) + 1)) * h * ω i)))⁻¹ : ℝ)) : ℂ))
          atTop (𝓝 (charFun (μ 0 1) ω))) ∧
        HasLevyMeasure (μ 0 1) (frameKnotLevy d q h a) ∧
        frameKnotLevy d q h a (axesSet d)ᶜ = 0 ∧
        ∀ n : ℤ, symmetryGroup (μ 0 (q ^ n)) = signedPermSet d := by
  have hq0 : 0 < q := by linarith
  have hmask := isLatticeMask_frame (d := d) ha0 ha1 hh hd
  haveI := hmask.1
  have hD := isSymData_frame (d := d) ha0 ha1 hh
  refine ⟨hmask, ?_, fun μ hμ => ?_⟩
  · obtain ⟨μ, hlad, -, -⟩ := ladder_knot_kernel_2 hd hq _ hmask.2.2.1 _ hD
      (lintegral_posLog_frameMaskNu ha0 ha1 hh)
    exact ⟨μ, hq, hlad.1.1, hlad.2.1, hlad.2.2⟩
  haveI := hμ.prob le_rfl zero_le_one
  obtain ⟨D1, -, hν1, hD1⟩ := hμ.knot_data hd hmask.2.1 hD
  have hF : D1.ν = frameKnotLevy d q h a := by
    rw [hν1, frameData_ν, frameKnotLevy_eq]
  refine ⟨fun ω => (hμ.product hd ω).1.congr fun M => ladderProd_frame ha0 ha1 M ω,
    hF ▸ (hasLevyMeasure_of_symData hD1).1, frameKnotLevy_axes q h a, fun n => ?_⟩
  haveI := hμ.prob le_rfl (zpow_pos hq0 n).le
  have hcn : ∀ ξ, charFun (μ 0 (q ^ n)) ξ = charFun (μ 0 1) ((q ^ n) • ξ) := fun ξ => by
    rw [hμ.zpow n, charFun_map_smul]
  have hiff : ∀ R : Mat d, push R (μ 0 (q ^ n)) = μ 0 (q ^ n) ↔ push R (μ 0 1) = μ 0 1 := by
    intro R
    rw [push_eq_iff_charFun, push_eq_iff_charFun]
    exact invariant_dilate_iff (zpow_ne_zero n hq0.ne') hcn R
  ext R
  constructor
  · -- a symmetry is a signed permutation
    rintro ⟨hRo, hpush⟩
    rw [hiff] at hpush
    have hmap := levy_map_eq_of_push_eq (isInfinitelyDivisible_of_hasTriplet
      (SymLevyData.hasTriplet hD1)) (SymLevyData.hasTriplet hD1) hRo hpush
    change D1.ν.map (lin R) = D1.ν at hmap
    rw [hF] at hmap
    set r : ℝ := h * q⁻¹ with hr
    have hrpos : 0 < r := mul_pos hh (inv_pos.2 hq0)
    have hcol : ∀ i : Fin d, ∃ j : Fin d, ∃ t : ℝ, (t = 1 ∨ t = -1) ∧
        lin R (ebasis i) = t • ebasis j := by
      intro i
      have hat := frameKnotLevy_atom (d := d) (q := q) (h := h) ha0 i
      rw [← atom_map_eq hRo hmap] at hat
      obtain ⟨j, c, hc⟩ := atom_mem (frameKnotLevy_axes q h a) hat
      have hnorm : |c| = r := by
        have h1 := congrArg norm hc
        rw [norm_lin_of_orth hRo, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hrpos] at h1
        have he : ‖(ebasis j : Rd d)‖ = 1 := by simp [ebasis]
        have he' : ‖(ebasis i : Rd d)‖ = 1 := by simp [ebasis]
        rw [he, he', mul_one, mul_one] at h1
        exact h1.symm
      refine ⟨j, c / r, ?_, ?_⟩
      · rcases abs_eq hrpos.le |>.1 hnorm with h1 | h1
        · left
          rw [h1, div_self hrpos.ne']
        · right
          rw [h1, neg_div, div_self hrpos.ne']
      · rw [map_smul] at hc
        rw [div_eq_inv_mul, mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
    choose σf t ht hRcol using hcol
    have hinj : Function.Injective σf := by
      intro i k hik
      by_contra hne
      have h1 : lin R (t k • ebasis i) = lin R (t i • ebasis k) := by
        rw [map_smul, map_smul, hRcol, hRcol, hik, smul_smul, smul_smul, mul_comm]
      have h2 := congrArg (fun z : Rd d => z i) (lin_injective_of_orth hRo h1)
      simp only [PiLp.smul_apply, smul_eq_mul, ebasis_apply, if_neg hne,
        mul_zero] at h2
      rcases ht k with h3 | h3 <;> rw [h3] at h2 <;> norm_num at h2
    set σ := Equiv.ofBijective σf (Finite.injective_iff_bijective.1 hinj) with hσ
    refine ⟨σ, t, ht, ?_⟩
    ext i j
    rw [← lin_ebasis_apply R i j, hRcol j, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul,
      ebasis_apply, Equiv.ofBijective_apply]
    split_ifs <;> simp
  · -- a signed permutation is a symmetry
    rintro ⟨σ, s, hs, rfl⟩
    refine ⟨signedPerm_mem_orthSet hs, ?_⟩
    rw [hiff, push_eq_iff_charFun]
    exact frame_knot_signedPerm ha0 ha1 hh hd hμ hs

end Pyramids
