/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Price.ResolventMask
import Pyramids.Helmholtz.NinePointFamily

/-!
# `prop:resolvent-masks-exact`(4): the instances

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:resolvent-masks-exact`. Wave 3h:
`resolvent_masks_exact_4_five`, `_4_nine` and `_4_general` moved here from
`PyramidsSkeleton.Ch05Price`, unchanged in name, binders and conclusion.

## The route

* **Laws on `hℤ^d`.** The transform of `zdLaw d h w` is the Fourier series of `w` at `ϑ = hω`
  (`charFun_zdLaw`). A probability kernel with a real Fourier series gives a mask on `hℤ^d`
  (`isLatticeMask_zdLaw`): symmetric because its transform is real, other than `δ₀` because it does
  not charge the origin fully.
* **The two resolvents** are `stepResolvent τ a` with `τ` the simple random walk step, resp. `σ_9`,
  and `a = 2dτ²/h²`, resp. `(10/3)τ²/h²` (`prop:discrete-helmholtz`, `prop:nine-point-family`).
  Its transform is `(1 + a(1 - τ̂))⁻¹` (`gridFourier_stepResolvent`), that of the resolvent mask of
  `zdLaw τ` with `p = a/(1 + a)` is `(1 - p)/(1 - pτ̂)`, and the two agree; so the laws agree by the
  uniqueness of the transform (`zdLaw_stepResolvent`). No convolution of laws on `hℤ^d` is
  computed.
* **Every nonzero point is charged.** A shortest lattice path from `0` to `n` has `|n|₁` unit steps,
  and `(μ ∗ ν){x + y} ≥ μ{x}ν{y}` along it gives `σ^{*|n|₁}{hn} > 0`; the term `k = |n|₁` of `ν_w`
  charges `hn`.
* **More generally**, the transform of `σ = (2C)⁻¹ ∑ c_y(δ_y + δ_{-y})` is `C⁻¹ ∑ c_y cos⟨y,·⟩`, and
  `1 + ∑ c_y(1 - cos⟨ω,y⟩) = (1 + C)(1 - pσ̂(ω))`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (convPow)
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## Laws on `hℤ^d` -/

theorem latticePt_add (h : ℝ) (n m : Zd d) :
    latticePt h (n + m) = latticePt h n + latticePt h m := by
  ext i
  simp [latticePt]
  ring

theorem latticePt_zero (h : ℝ) : latticePt h (0 : Zd d) = 0 := by
  ext i
  simp [latticePt]

theorem latticePt_injective {h : ℝ} (hh : h ≠ 0) : Function.Injective (latticePt (d := d) h) := by
  intro n m hnm
  funext i
  have := congrArg (fun x : Rd d => x i) hnm
  simpa [latticePt, hh] using this

theorem zdLaw_eq_latticePt (h : ℝ) (w : Zd d → ℝ) :
    zdLaw d h w = Measure.sum fun n => ENNReal.ofReal (w n) • Measure.dirac (latticePt h n) :=
  rfl

theorem zdLaw_apply (h : ℝ) (w : Zd d → ℝ) {s : Set (Rd d)} (hs : MeasurableSet s) :
    zdLaw d h w s = ∑' n, ENNReal.ofReal (w n) * s.indicator 1 (latticePt h n) := by
  rw [zdLaw_eq_latticePt, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]

theorem isProbabilityMeasure_zdLaw {h : ℝ} {w : Zd d → ℝ} (hw : IsProbKernel w) :
    IsProbabilityMeasure (zdLaw d h w) := by
  constructor
  rw [zdLaw_apply h w MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hw.1 hw.2.1, hw.2.2, ENNReal.ofReal_one]

theorem zdLaw_singleton_ge (h : ℝ) (w : Zd d → ℝ) (n : Zd d) :
    ENNReal.ofReal (w n) ≤ zdLaw d h w {latticePt h n} := by
  rw [zdLaw_apply h w (measurableSet_singleton _)]
  calc ENNReal.ofReal (w n) = ENNReal.ofReal (w n) *
        ({latticePt h n} : Set (Rd d)).indicator 1 (latticePt h n) := by simp
    _ ≤ _ := ENNReal.le_tsum (f := fun m => ENNReal.ofReal (w m) *
        ({latticePt h n} : Set (Rd d)).indicator 1 (latticePt h m)) n

theorem zdLaw_singleton {h : ℝ} (hh : h ≠ 0) (w : Zd d → ℝ) (n : Zd d) :
    zdLaw d h w {latticePt h n} = ENNReal.ofReal (w n) := by
  rw [zdLaw_apply h w (measurableSet_singleton _), tsum_eq_single n]
  · simp
  · intro m hm
    rw [indicator_of_notMem fun h' => hm (latticePt_injective hh (mem_singleton_iff.1 h')),
      mul_zero]

theorem countable_gridSet (h : ℝ) : (gridSet d h).Countable :=
  (countable_range (latticePt (d := d) h)).mono fun x hx => by
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, hn.symm⟩

theorem zdLaw_gridSet_compl (h : ℝ) (w : Zd d → ℝ) : zdLaw d h w (gridSet d h)ᶜ = 0 := by
  rw [zdLaw_apply h w (countable_gridSet h).measurableSet.compl, ENNReal.tsum_eq_zero]
  intro n
  rw [indicator_of_notMem (show latticePt h n ∉ (gridSet d h)ᶜ from fun hn => hn ⟨n, rfl⟩),
    mul_zero]

theorem zdLaw_finset_compl (h : ℝ) (w : Zd d → ℝ) (T : Finset (Zd d)) (hT : ∀ n ∉ T, w n = 0) :
    zdLaw d h w (↑(T.image (latticePt h)) : Set (Rd d))ᶜ = 0 := by
  classical
  rw [zdLaw_apply h w (Finset.measurableSet _).compl, ENNReal.tsum_eq_zero]
  intro n
  by_cases hn : n ∈ T
  · rw [indicator_of_notMem (show latticePt h n ∉ (↑(T.image (latticePt h)) : Set (Rd d))ᶜ from
      fun h' => h' (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn))), mul_zero]
  · rw [hT n hn, ENNReal.ofReal_zero, zero_mul]

/-- **The transform of a law on `hℤ^d`** is the Fourier series of its point masses at `ϑ = hω`. -/
theorem charFun_zdLaw {h : ℝ} {w : Zd d → ℝ} (hw : IsProbKernel w) (ω : Rd d) :
    charFun (zdLaw d h w) ω = gridFourier w (fun i => h * ω i) := by
  haveI := isProbabilityMeasure_zdLaw (h := h) hw
  have hint : Integrable (fun x : Rd d => Complex.exp (↑⟪x, ω⟫ * Complex.I)) (zdLaw d h w) :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply]
  rw [zdLaw_eq_latticePt] at hint ⊢
  rw [integral_sum_measure hint, gridFourier_eq]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw.1 n), Complex.real_smul]
  congr 4
  rw [latticePt, real_inner_smul_left, gphase, PiLp.inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  ring

theorem norm_gridFourier_le {w : Zd d → ℝ} (hw : IsProbKernel w) (θ : Fin d → ℝ) :
    ‖gridFourier w θ‖ ≤ 1 := by
  rw [gridFourier_eq]
  calc ‖∑' n, (w n : ℂ) * Complex.exp ((gphase θ n : ℂ) * Complex.I)‖
      ≤ ∑' n, ‖(w n : ℂ) * Complex.exp ((gphase θ n : ℂ) * Complex.I)‖ :=
        norm_tsum_le_tsum_norm (summable_fourier_term hw.2.1 θ).norm
    _ = ∑' n, w n := tsum_congr fun n => by
        rw [norm_mul, norm_cexp_gphase, mul_one, Complex.norm_real, Real.norm_of_nonneg (hw.1 n)]
    _ = 1 := hw.2.2

/-- **A probability kernel with a real Fourier series, not `δ₀`, is a mask on `hℤ^d`.** -/
theorem isLatticeMask_zdLaw {h : ℝ} (hh : h ≠ 0) {w : Zd d → ℝ} (hw : IsProbKernel w)
    (hreal : ∀ θ, ∃ φ : ℝ, gridFourier w θ = φ) (h0 : w 0 ≠ 1) :
    IsLatticeMask (gridSet d h) (zdLaw d h w) := by
  haveI := isProbabilityMeasure_zdLaw (h := h) hw
  refine ⟨inferInstance, map_neg_eq_of_charFun_im fun ω => ?_, fun hδ => h0 ?_,
    zdLaw_gridSet_compl h w⟩
  · obtain ⟨φ, hφ⟩ := hreal (fun i => h * ω i)
    rw [charFun_zdLaw hw, hφ, Complex.ofReal_im]
  · have h1 := congrArg (fun m : Measure (Rd d) => m {latticePt h 0}) hδ
    rw [zdLaw_singleton hh, latticePt_zero, Measure.dirac_apply_of_mem (mem_singleton 0),
      ENNReal.ofReal_eq_one] at h1
    exact h1

/-- **The resolvent of a step is the resolvent mask of its law**: equal transforms. -/
theorem zdLaw_stepResolvent (h : ℝ) {τ : Zd d → ℝ} (hτ : IsProbKernel τ) {a : ℝ} (ha : 0 < a)
    (hreal : ∀ θ, ∃ φ : ℝ, gridFourier τ θ = φ) :
    zdLaw d h (stepResolvent τ a) = resolventMask (a / (1 + a)) (zdLaw d h τ) := by
  haveI := isProbabilityMeasure_zdLaw (h := h) hτ
  haveI := isProbabilityMeasure_zdLaw (h := h) (isProbKernel_stepResolvent hτ ha)
  have hp0 := (stepP_pos ha).le
  have hp1 := stepP_lt_one ha
  haveI := isProbabilityMeasure_resolventMask (σ := zdLaw d h τ) hp0 hp1
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  obtain ⟨φ, hφ⟩ := hreal (fun i => h * ω i)
  have hφ1 : |φ| ≤ 1 := by
    have := norm_gridFourier_le hτ (fun i => h * ω i)
    rwa [hφ, Complex.norm_real, Real.norm_eq_abs] at this
  rw [charFun_zdLaw (isProbKernel_stepResolvent hτ ha), gridFourier_stepResolvent hτ ha _ hφ hφ1,
    charFun_resolventMask hp0 hp1, charFun_zdLaw hτ, hφ]
  have h1 : 0 < 1 + a * (1 - φ) := by nlinarith [(abs_le.1 hφ1).2]
  have h2 : (1 : ℝ) + a ≠ 0 := by linarith
  have key : (1 + a * (1 - φ))⁻¹ = (1 - a / (1 + a)) / (1 - a / (1 + a) * φ) := by
    rw [show 1 - a / (1 + a) = 1 / (1 + a) by field_simp; ring,
      show 1 - a / (1 + a) * φ = (1 + a * (1 - φ)) / (1 + a) by field_simp; ring,
      div_div_div_cancel_right₀ h2, one_div]
  rw [key]
  push_cast
  rfl

/-! ## The lattice path -/

/-- A step of the walk has mass at least `1/2d` at `±eᵢ`. -/
theorem rwStep_axis_ge (i : Fin d) {e : Zd d} (he : e = zbasis i ∨ e = -zbasis i) :
    1 / (2 * d) ≤ rwStep e := by
  unfold rwStep
  have hd : (0 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast Fin.pos i
    linarith
  calc 1 / (2 * d) ≤ ((if e = zbasis i then (1 : ℝ) else 0) + (if e = -zbasis i then 1 else 0)) /
        (2 * d) := by
        refine div_le_div_of_nonneg_right ?_ hd.le
        rcases he with h | h
        · rw [if_pos h]
          split_ifs <;> norm_num
        · rw [if_pos h]
          split_ifs <;> norm_num
    _ ≤ _ := Finset.single_le_sum (f := fun j => ((if e = zbasis j then (1 : ℝ) else 0) +
        (if e = -zbasis j then 1 else 0)) / (2 * d))
        (fun j _ => div_nonneg (by split_ifs <;> norm_num) hd.le) (Finset.mem_univ i)

/-- **`σ^{*|n|₁}` charges `hn`**: a shortest lattice path from `0` to `n`. -/
theorem convPow_zdLaw_rwStep_ne_zero (h : ℝ) :
    ∀ k : ℕ, ∀ n : Zd d, ∑ i, (n i).natAbs = k →
      convPow (zdLaw d h rwStep) k {latticePt h n} ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have hn0 : n = 0 := funext fun i => by
      have := (Finset.sum_eq_zero_iff.1 hn) i (Finset.mem_univ i)
      simpa using this
    rw [hn0, latticePt_zero]
    change Measure.dirac (0 : Rd d) {0} ≠ 0
    simp
  | succ k ih =>
    intro n hn
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hc
      push Not at hc
      simp [hc] at hn
    set e : Zd d := if 0 < n i then zbasis i else -zbasis i with he
    have he' : e = zbasis i ∨ e = -zbasis i := by
      rw [he]
      split_ifs
      · left; rfl
      · right; rfl
    have hei : ∀ j, j ≠ i → e j = 0 := fun j hj => by
      rw [he]
      split_ifs <;> simp [zbasis, hj]
    have hn' : ∑ j, ((n - e) j).natAbs = k := by
      have hsplit := Finset.add_sum_erase Finset.univ (fun j => (n j).natAbs) (Finset.mem_univ i)
      have hsplit' := Finset.add_sum_erase Finset.univ (fun j => ((n - e) j).natAbs)
        (Finset.mem_univ i)
      have hrest : ∑ j ∈ Finset.univ.erase i, ((n - e) j).natAbs =
          ∑ j ∈ Finset.univ.erase i, (n j).natAbs :=
        Finset.sum_congr rfl fun j hj => by
          rw [Pi.sub_apply, hei j (Finset.ne_of_mem_erase hj), sub_zero]
      have hii : ((n - e) i).natAbs + 1 = (n i).natAbs := by
        rw [Pi.sub_apply, he]
        split_ifs with hpos
        · simp only [zbasis, Pi.single_eq_same]
          omega
        · simp only [zbasis, Pi.neg_apply, Pi.single_eq_same]
          omega
      omega
    haveI := isProbabilityMeasure_zdLaw (h := h) (isProbKernel_rwStep (d := d) (Fin.pos i))
    have hpt : latticePt h n = latticePt h (n - e) + latticePt h e := by
      rw [← latticePt_add, sub_add_cancel]
    have hstep : 0 < zdLaw d h rwStep {latticePt h e} := by
      refine lt_of_lt_of_le ?_ (zdLaw_singleton_ge h rwStep e)
      refine ENNReal.ofReal_pos.2 (lt_of_lt_of_le ?_ (rwStep_axis_ge i he'))
      have : (0 : ℝ) < d := by exact_mod_cast Fin.pos i
      positivity
    have hle := conv_singleton_ge (convPow (zdLaw d h rwStep) k) (zdLaw d h rwStep)
      (latticePt h (n - e)) (latticePt h e)
    rw [← hpt] at hle
    exact ne_of_gt (lt_of_lt_of_le (ENNReal.mul_pos (ih _ hn') hstep.ne') hle)

/-! ## `prop:resolvent-masks-exact`(4), the five-point resolvent -/

theorem rwStep_zero : rwStep (0 : Zd d) = 0 := by
  unfold rwStep
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : (0 : Zd d) ≠ zbasis i := fun h => by
    have := congrFun h i
    simp [zbasis] at this
  have h2 : (0 : Zd d) ≠ -zbasis i := fun h => by
    have := congrFun h i
    simp [zbasis] at this
  simp [h1, h2]

/-- The walk's steps `±eᵢ`. -/
noncomputable def rwSupport (d : ℕ) : Finset (Zd d) := by
  classical exact Finset.univ.image zbasis ∪ Finset.univ.image fun i => -zbasis i

theorem rwStep_eq_zero {n : Zd d} (hn : n ∉ rwSupport d) : rwStep n = 0 := by
  classical
  unfold rwSupport at hn
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or,
    not_exists] at hn
  unfold rwStep
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [if_neg fun h => hn.1 i h.symm, if_neg fun h => hn.2 i h.symm]
  simp

/-- **`prop:resolvent-masks-exact`(4), the five-point resolvent.** On `hℤ^d`, `κ_τ` is
(`eq:resolvent-mask`) with the simple random walk step and `p = 2dτ²/(h² + 2dτ²)` (a mask with
finite support, and `0 < p < 1`), and then `ν_w` charges every nonzero point of `hℤ^d`. -/
theorem resolvent_masks_exact_4_five (hd : 1 ≤ d) {h τ : ℝ} (hh : 0 < h) (hτ : 0 < τ) :
    IsLatticeMask (gridSet d h) (zdLaw d h rwStep) ∧
      (∃ S : Finset (Rd d), zdLaw d h rwStep (↑S : Set (Rd d))ᶜ = 0) ∧
      0 < 2 * d * τ ^ 2 / (h ^ 2 + 2 * d * τ ^ 2) ∧ 2 * d * τ ^ 2 / (h ^ 2 + 2 * d * τ ^ 2) < 1 ∧
      zdLaw d h (discreteHelmholtz d h τ) =
        resolventMask (2 * d * τ ^ 2 / (h ^ 2 + 2 * d * τ ^ 2)) (zdLaw d h rwStep) ∧
      ∀ n : Zd d, n ≠ 0 →
        resolventLevy (2 * d * τ ^ 2 / (h ^ 2 + 2 * d * τ ^ 2)) (zdLaw d h rwStep)
          {latticePt h n} ≠ 0 := by
  have hσ := isProbKernel_rwStep hd
  have hreal : ∀ θ, ∃ φ : ℝ, gridFourier (rwStep (d := d)) θ = φ :=
    fun θ => ⟨_, gridFourier_rwStep θ⟩
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set a : ℝ := 2 * d * (τ ^ 2 / h ^ 2) with ha_def
  have ha : 0 < a := by positivity
  have hpa : 2 * d * τ ^ 2 / (h ^ 2 + 2 * d * τ ^ 2) = a / (1 + a) := by
    rw [ha_def]
    field_simp
  rw [hpa]
  refine ⟨isLatticeMask_zdLaw hh.ne' hσ hreal (by rw [rwStep_zero]; norm_num),
    ⟨(rwSupport d).image (latticePt h), zdLaw_finset_compl h _ _ fun n hn => rwStep_eq_zero hn⟩,
    stepP_pos ha, stepP_lt_one ha, zdLaw_stepResolvent h hσ ha hreal, fun n hn => ?_⟩
  -- the term `k = |n|₁` of `ν_w` charges `hn`
  haveI := isProbabilityMeasure_zdLaw (h := h) hσ
  have hpt0 : latticePt h n ≠ 0 := fun h0 =>
    hn (latticePt_injective hh.ne' (h0.trans (latticePt_zero h).symm))
  obtain ⟨k, hk⟩ : ∃ k, ∑ i, (n i).natAbs = k + 1 := by
    refine ⟨∑ i, (n i).natAbs - 1, ?_⟩
    have : ∑ i, (n i).natAbs ≠ 0 := fun h0 => hn (funext fun i => by
      have := (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ i)
      simpa using this)
    omega
  have hc := convPow_zdLaw_rwStep_ne_zero h (k + 1) n hk
  rw [resolventLevy_eq, Measure.restrict_apply (measurableSet_singleton _),
    inter_eq_left.2 (singleton_subset_iff.2 hpt0), resolventSeries_apply _ _
      (measurableSet_singleton _)]
  refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum k))
  refine ENNReal.mul_pos (ENNReal.ofReal_pos.2 ?_).ne' hc
  exact div_pos (pow_pos (stepP_pos ha) _) (by positivity)

/-! ## `prop:resolvent-masks-exact`(4), the nine-point resolvent -/

/-- The eight steps of `σ_9`. -/
noncomputable def nineSupport : Finset (Zd 2) := by
  classical exact ({zbasis (d := 2) 0, -zbasis (d := 2) 0, zbasis (d := 2) 1,
    -zbasis (d := 2) 1, zbasis (d := 2) 0 + zbasis 1, zbasis (d := 2) 0 - zbasis 1,
    -zbasis (d := 2) 0 + zbasis 1, -zbasis (d := 2) 0 - zbasis 1} : Finset (Zd 2))

theorem ninePointStep_eq_zero {n : Zd 2} (hn : n ∉ nineSupport) : ninePointStep n = 0 := by
  classical
  unfold nineSupport at hn
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hn
  simp [ninePointStep, Fin.sum_univ_two, h1, h2, h3, h4, h5, h6, h7, h8]

theorem zero_not_mem_nineSupport : (0 : Zd 2) ∉ nineSupport := by
  classical
  unfold nineSupport
  simp only [Finset.mem_insert, Finset.mem_singleton, zd2_eq_iff, Pi.zero_apply, Pi.add_apply,
    Pi.sub_apply, Pi.neg_apply, zbasis00, zbasis01, zbasis10, zbasis11]
  norm_num

/-- **`prop:resolvent-masks-exact`(4), the nine-point resolvent.** On `hℤ²`, `κ^9_τ` is
(`eq:resolvent-mask`) with its step `σ_9` and `p = 10τ²/(3h² + 10τ²)`. -/
theorem resolvent_masks_exact_4_nine {h τ : ℝ} (hh : 0 < h) (hτ : 0 < τ) :
    IsLatticeMask (gridSet 2 h) (zdLaw 2 h ninePointStep) ∧
      (∃ S : Finset (Rd 2), zdLaw 2 h ninePointStep (↑S : Set (Rd 2))ᶜ = 0) ∧
      0 < 10 * τ ^ 2 / (3 * h ^ 2 + 10 * τ ^ 2) ∧ 10 * τ ^ 2 / (3 * h ^ 2 + 10 * τ ^ 2) < 1 ∧
      zdLaw 2 h (ninePointHelmholtz h τ) =
        resolventMask (10 * τ ^ 2 / (3 * h ^ 2 + 10 * τ ^ 2)) (zdLaw 2 h ninePointStep) := by
  have hσ := isProbKernel_ninePointStep
  have hreal : ∀ θ, ∃ φ : ℝ, gridFourier ninePointStep θ = φ :=
    fun θ => ⟨_, gridFourier_ninePointStep θ⟩
  set a : ℝ := 10 / 3 * (τ ^ 2 / h ^ 2) with ha_def
  have ha : 0 < a := by positivity
  have hpa : 10 * τ ^ 2 / (3 * h ^ 2 + 10 * τ ^ 2) = a / (1 + a) := by
    rw [ha_def]
    field_simp
  rw [hpa, ninePointHelmholtz_eq]
  exact ⟨isLatticeMask_zdLaw hh.ne' hσ hreal
      (by rw [ninePointStep_eq_zero zero_not_mem_nineSupport]; norm_num),
    ⟨nineSupport.image (latticePt h), zdLaw_finset_compl h _ _ fun n hn =>
      ninePointStep_eq_zero hn⟩,
    stepP_pos ha, stepP_lt_one ha, zdLaw_stepResolvent h hσ ha hreal⟩

/-! ## `prop:resolvent-masks-exact`(4), more generally -/

section Stencil

variable (N : Finset (Rd d)) (c : Rd d → ℝ)

theorem stencilStep_apply {s : Set (Rd d)} (hs : MeasurableSet s) :
    stencilStep N c s = ENNReal.ofReal (2 * ∑ y ∈ N, c y)⁻¹ *
      ∑ y ∈ N, ENNReal.ofReal (c y) * (s.indicator 1 y + s.indicator 1 (-y)) := by
  rw [stencilStep, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ hs, smul_eq_mul]

variable {N c}

theorem stencilStep_compl (hNsymm : ∀ y ∈ N, -y ∈ N) :
    stencilStep N c (↑N : Set (Rd d))ᶜ = 0 := by
  rw [stencilStep_apply N c (Finset.measurableSet _).compl]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun y hy => ?_)
  rw [indicator_of_notMem (show y ∉ (↑N : Set (Rd d))ᶜ from fun h => h hy),
    indicator_of_notMem (show -y ∉ (↑N : Set (Rd d))ᶜ from fun h => h (hNsymm y hy)), add_zero,
    mul_zero]

theorem isProbabilityMeasure_stencilStep (hc : ∀ y ∈ N, 0 ≤ c y)
    (hC : 0 < ∑ y ∈ N, c y) : IsProbabilityMeasure (stencilStep N c) := by
  constructor
  rw [stencilStep_apply N c MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply]
  have e : ∑ y ∈ N, ENNReal.ofReal (c y) * (1 + 1) = ENNReal.ofReal (2 * ∑ y ∈ N, c y) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun y hy => by linarith [hc y hy]]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_comm, one_add_one_eq_two]
  rw [e, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
    ENNReal.ofReal_one]

/-- **The transform of the stencil step**: `σ̂ = (2C)⁻¹ ∑ c_y 2cos⟨y,·⟩`. -/
theorem charFun_stencilStep (hc : ∀ y ∈ N, 0 ≤ c y) (ω : Rd d) :
    charFun (stencilStep N c) ω =
      (((2 * ∑ y ∈ N, c y)⁻¹ * ∑ y ∈ N, c y * (2 * Real.cos ⟪y, ω⟫) : ℝ) : ℂ) := by
  have hC : 0 ≤ ∑ y ∈ N, c y := Finset.sum_nonneg hc
  have hb : ∀ (m : Measure (Rd d)) [IsFiniteMeasure m],
      Integrable (fun x : Rd d => Complex.exp (↑⟪x, ω⟫ * Complex.I)) m := fun m _ =>
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  have hint : ∀ y ∈ N, Integrable (fun x : Rd d => Complex.exp (↑⟪x, ω⟫ * Complex.I))
      (ENNReal.ofReal (c y) • (Measure.dirac y + Measure.dirac (-y))) := fun y _ =>
    ((hb _).add_measure (hb _)).smul_measure ENNReal.ofReal_ne_top
  rw [charFun_apply, stencilStep, integral_smul_measure, integral_finsetSum_measure hint,
    ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  have e : ∀ y ∈ N, ∫ x, Complex.exp (↑⟪x, ω⟫ * Complex.I)
      ∂(ENNReal.ofReal (c y) • (Measure.dirac y + Measure.dirac (-y))) =
      ((c y * (2 * Real.cos ⟪y, ω⟫) : ℝ) : ℂ) := fun y hy => by
    rw [integral_smul_measure, integral_add_measure (hb _) (hb _), integral_dirac,
      integral_dirac, ENNReal.toReal_ofReal (hc y hy), Complex.real_smul, inner_neg_left,
      Complex.ofReal_neg, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]
    push_cast
    ring
  rw [Finset.sum_congr rfl e]
  push_cast
  rfl

end Stencil

/-- **`prop:resolvent-masks-exact`(4), more generally.** A probability `w` with
`1/ŵ(ω) = 1 + ∑_{y ∈ 𝒩} c_y(1 - cos⟨ω, y⟩)`, `𝒩` finite and symmetric, `c_y = c_{-y} ≥ 0` not all
`0`, is (`eq:resolvent-mask`) with `C = ∑ c_y`, `p = C/(1+C)` and
`σ = (2C)⁻¹ ∑ c_y(δ_y + δ_{-y})`, `σ` being a symmetric probability `≠ δ₀` with finite support and
`0 < p < 1`. -/
theorem resolvent_masks_exact_4_general (N : Finset (Rd d)) (hN0 : ∀ y ∈ N, y ≠ 0)
    (hNsymm : ∀ y ∈ N, -y ∈ N) (c : Rd d → ℝ) (hc : ∀ y ∈ N, c (-y) = c y ∧ 0 ≤ c y)
    (hcne : ∃ y ∈ N, c y ≠ 0) (w : Measure (Rd d)) [IsProbabilityMeasure w]
    (hw : ∀ ω : Rd d,
      charFun w ω = (((1 + ∑ y ∈ N, c y * (1 - Real.cos ⟪ω, y⟫))⁻¹ : ℝ) : ℂ)) :
    IsProbabilityMeasure (stencilStep N c) ∧
      (stencilStep N c).map (fun x => -x) = stencilStep N c ∧
      stencilStep N c ≠ Measure.dirac 0 ∧ stencilStep N c (↑N : Set (Rd d))ᶜ = 0 ∧
      0 < (∑ y ∈ N, c y) / (1 + ∑ y ∈ N, c y) ∧ (∑ y ∈ N, c y) / (1 + ∑ y ∈ N, c y) < 1 ∧
      w = resolventMask ((∑ y ∈ N, c y) / (1 + ∑ y ∈ N, c y)) (stencilStep N c) := by
  have hc0 : ∀ y ∈ N, 0 ≤ c y := fun y hy => (hc y hy).2
  set C := ∑ y ∈ N, c y with hC_def
  have hC : 0 < C := by
    obtain ⟨y, hy, hcy⟩ := hcne
    exact Finset.sum_pos' hc0 ⟨y, hy, lt_of_le_of_ne (hc0 y hy) (Ne.symm hcy)⟩
  haveI := isProbabilityMeasure_stencilStep hc0 hC
  have hp0 : 0 < C / (1 + C) := by positivity
  have hp1 : C / (1 + C) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hcompl := stencilStep_compl (c := c) hNsymm
  refine ⟨inferInstance, map_neg_eq_of_charFun_im fun ω => ?_, fun hδ => ?_, hcompl, hp0, hp1,
    ?_⟩
  · rw [charFun_stencilStep hc0, Complex.ofReal_im]
  · have h0 : (0 : Rd d) ∉ (↑N : Set (Rd d)) := fun h => hN0 0 h rfl
    rw [hδ, Measure.dirac_apply_of_mem h0] at hcompl
    exact one_ne_zero hcompl
  · haveI := isProbabilityMeasure_resolventMask (σ := stencilStep N c) hp0.le hp1
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [hw, charFun_resolventMask hp0.le hp1, charFun_stencilStep hc0]
    set S := ∑ y ∈ N, c y * Real.cos ⟪y, ω⟫ with hS
    have hSC : S ≤ C := Finset.sum_le_sum fun y hy => by
      nlinarith [Real.cos_le_one ⟪y, ω⟫, hc0 y hy]
    have e1 : ∑ y ∈ N, c y * (1 - Real.cos ⟪ω, y⟫) = C - S := by
      rw [hC_def, hS, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [real_inner_comm]
      ring
    have e2 : (2 * C)⁻¹ * ∑ y ∈ N, c y * (2 * Real.cos ⟪y, ω⟫) = S / C := by
      rw [hS, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => ?_
      field_simp
    rw [e1, e2]
    have h1 : 0 < 1 + C - S := by linarith
    have hne1 : 1 + (C - S) ≠ 0 := by linarith
    have hne2 : 1 + C ≠ 0 := by linarith
    have hne3 : C ≠ 0 := hC.ne'
    have hne4 : 1 + C - S ≠ 0 := h1.ne'
    have key : (1 + (C - S))⁻¹ = (1 - C / (1 + C)) / (1 - C / (1 + C) * (S / C)) := by
      rw [show 1 - C / (1 + C) = 1 / (1 + C) by field_simp; ring,
        show 1 - C / (1 + C) * (S / C) = (1 + (C - S)) / (1 + C) by field_simp; ring]
      rw [div_div_div_cancel_right₀ hne2, one_div]
    rw [key]
    push_cast
    rfl

/-! ## A resolvent mask is a compound Poisson law (from `Helmholtz/NinePointLevy.lean`,
moved at the split, `adr/0007`: `prop:creation-grid-masks` reads it) -/

/-- **A resolvent mask is the compound Poisson law of `ν_w`**, infinitely divisible with Lévy
measure `ν_w`, for any symmetric law `σ` and `0 ≤ p < 1`: the argument of
`resolvent_masks_exact_1`, without a lattice. -/
theorem resolventMask_compoundPoisson {σ : Measure (Rd d)} [IsProbabilityMeasure σ]
    (hs : σ.map (fun x => -x) = σ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    IsInfinitelyDivisible (resolventMask p σ) ∧
      HasLevyMeasure (resolventMask p σ) (resolventLevy p σ) ∧
      resolventMask p σ = compoundPoissonLaw (resolventLevy p σ) := by
  haveI := isProbabilityMeasure_resolventMask (σ := σ) hp0 hp1
  haveI := isFiniteMeasure_resolventLevy (σ := σ) hp0 hp1
  obtain ⟨D, hA, hν, hD⟩ := exists_resolventData (σ := σ) hs hp0 hp1
  refine ⟨isInfinitelyDivisible_of_hasTriplet (SymLevyData.hasTriplet hD),
    hν ▸ (hasLevyMeasure_of_symData hD).1, ?_⟩
  change resolventMask p σ = cpLaw (resolventLevy p σ)
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_cpLaw_symm _ (resolventLevy_symm hs), hD ω, ← hν]
  simp [SymLevyData.exponent, pairExponent, hA, quad_zero]


end Pyramids
