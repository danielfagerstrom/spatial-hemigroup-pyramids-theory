/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.DiscreteHelmholtz
import Pyramids.Pyramid.EquivalentWeights
import Pyramids.Pyramid.NoBoundedStep
import Pyramids.LineAppendix.ClassicalWeights
import Pyramids.Line.GeometricMask
import Pyramids.Price.FrameMatern
import Pyramids.Price.BinomialKnot
import Pyramids.Price.FrameStep
import Pyramids.Price.ResolventInstances
import Pyramids.Matern.CreationGridInverse
import Pyramids.Price.ExactMasks
import Pyramids.Price.RecordsCreation

/-!
# `prop:creation-grid-masks`: the masks of the creation on a grid

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:creation-grid-masks`. Phase 5, wave 3b. The
five declarations are the skeleton's (`PyramidsSkeleton/Ch05Price.lean`), unchanged in name and
conclusion. Their binders are fewer (dropped on 2026-11-15, a strengthening): `_1` and `_2` take
`1 ≤ d` for `2 ≤ d`; `_3_resolvent` and `_3_frame` take `1 ≤ q` for `2 ≤ q` and no finiteness or
symmetry of `𝒩` and no `0 ∉ 𝒩`, which `records_creation` does not read.

* **The two spellings of a tensor mask** (`zdLaw_tensorIdx_eq_tensorPow`). The product measure is
  determined by its values on boxes (`Measure.pi_eq`); on a box both sides are
  `∑ₙ ∏ᵢ k(nᵢ) 1[hnᵢ ∈ sᵢ] = ∏ᵢ ∑ₘ k(m) 1[hm ∈ sᵢ]`, a finite product of sums in `ℝ≥0∞`
  (`ennreal_prod_tsum`).
* **(1).** `κ_t`: a probability (`isProbKernel_discreteHelmholtz`), symmetric (its invariance
  under `n ↦ -n`), with the transform `(1 + t²D_h)⁻¹ > 0`, which is below `1` at `ϑ = (π, …, π)`,
  so `κ_t ≠ δ₀`. The tensors: the sum is `1` and the transform is the product of the factors'
  transforms, both read from the law on `ℤ^d` through the identity above; `λ^L_a` has the transform
  `(1-a)²/(1 - 2a cos ϑ + a²) > 0`, `β` has `cos⁴(ϑ/2) ≥ 0`; the weight at `0` is `k(0)^d < 1`.
  Since 2026-11-23 the clause does not state the nonnegative transforms, which nothing read.
* **(2).** `κ_t` is the resolvent mask of the simple random walk step
  (`resolvent_masks_exact_4_five`), infinitely divisible (`resolventMask_compoundPoisson`). The
  frame mask has the data `(0, ν_w)` (`isSymData_frame`), so it is the compound Poisson law of
  `ν_w`, infinitely divisible (`isInfinitelyDivisible_cpLaw_symm`); until 2026-11-23 this went
  through its exact grid pyramid and `exact_masks_1`, which read A49. `β^{⊗d}` has bounded
  support and is no
  point mass, so it is not infinitely divisible (`no_bounded_step`).
* **(3).** `creation_grid_3` makes every bounded array a level-`k` record; `records_creation` gives
  the input.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexOrder

variable {d : ℕ}

/-! ## The two spellings of a tensor mask -/

/-- **A finite product of sums is the sum of the products** in `ℝ≥0∞`. -/
theorem ennreal_prod_tsum {α : Type*} :
    ∀ (n : ℕ) (f : Fin n → α → ℝ≥0∞), ∏ i, ∑' a, f i a = ∑' x : Fin n → α, ∏ i, f i (x i)
  | 0, f => by simp
  | n + 1, f => by
    rw [Fin.prod_univ_succ, ennreal_prod_tsum n (fun i => f i.succ), ← ENNReal.tsum_mul_right]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [← ENNReal.tsum_prod,
      ← (Fin.consEquiv fun _ : Fin (n + 1) => α).tsum_eq
        (fun x : Fin (n + 1) → α => ∏ i, f i (x i))]
    refine tsum_congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem gridLaw_apply' (h : ℝ) (k : ℤ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    gridLaw h k s = ∑' m, ENNReal.ofReal (k m) * s.indicator 1 (h * m) := by
  rw [gridLaw, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]

theorem isFiniteMeasure_gridLaw {h : ℝ} {k : ℤ → ℝ} (hk0 : ∀ n, 0 ≤ k n) (hks : Summable k) :
    IsFiniteMeasure (gridLaw h k) := by
  constructor
  rw [gridLaw_apply' h k MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hk0 hks]
  exact ENNReal.ofReal_lt_top

/-- **The two spellings of a tensor mask agree** (skeleton review 05, item 3). -/
theorem zdLaw_tensorIdx_eq_tensorPow {h : ℝ} {k : ℤ → ℝ} (hk : ∀ n, 0 ≤ k n)
    (hks : Summable k) : zdLaw d h (tensorIdx k) = tensorPow d (gridLaw h k) := by
  haveI := isFiniteMeasure_gridLaw (h := h) hk hks
  have hmeas : Measurable (WithLp.ofLp : Rd d → (Fin d → ℝ)) :=
    (PiLp.continuous_ofLp 2 _).measurable
  have hpi : Measure.pi (fun _ : Fin d => gridLaw h k) =
      (zdLaw d h (tensorIdx k)).map WithLp.ofLp := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs),
      zdLaw_apply h _ (hmeas (MeasurableSet.univ_pi hs))]
    simp_rw [gridLaw_apply' h k (hs _)]
    rw [ennreal_prod_tsum]
    refine tsum_congr fun n => ?_
    rw [tensorIdx, ENNReal.ofReal_prod_of_nonneg fun i _ => hk _]
    by_cases hall : ∀ i, (h * n i : ℝ) ∈ s i
    · have hmem : latticePt h n ∈ WithLp.ofLp ⁻¹' univ.pi s := by
        simpa [latticePt] using hall
      rw [indicator_of_mem hmem, Pi.one_apply, mul_one]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [indicator_of_mem (hall i), Pi.one_apply, mul_one]
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      have hmem : latticePt h n ∉ WithLp.ofLp ⁻¹' univ.pi s := by
        simp only [mem_preimage, mem_univ_pi, not_forall]
        exact ⟨i, by simpa [latticePt] using hi⟩
      rw [indicator_of_notMem hmem, mul_zero]
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [indicator_of_notMem hi, mul_zero])).symm
  rw [tensorPow, hpi, Measure.map_map (PiLp.continuous_toLp 2 _).measurable hmeas]
  exact (Measure.map_id).symm

/-! ## Tensors of a probability kernel on `ℤ` -/

section Tensor

variable {k : ℤ → ℝ} (hk0 : ∀ n, 0 ≤ k n) (hk1 : HasSum k 1)
include hk0 hk1

theorem isProbKernel_tensorIdx : IsProbKernel (tensorIdx (d := d) k) := by
  have hs := summable_tensorIdx (d := d) hk0 hk1.summable
  have hnn : ∀ n, 0 ≤ tensorIdx (d := d) k n := fun n => Finset.prod_nonneg fun i _ => hk0 _
  refine ⟨hnn, hs, ?_⟩
  haveI := isProbabilityMeasure_gridLaw (h := 1) hk0 hk1
  haveI := (tensorPow_charFun (d := d) (m := gridLaw 1 k)).1
  have h1 := zdLaw_tensorIdx_eq_tensorPow (d := d) (h := 1) hk0 hk1.summable
  have h2 := congrArg (fun m : Measure (Rd d) => m univ) h1
  simp only [measure_univ] at h2
  rw [zdLaw_apply 1 _ MeasurableSet.univ] at h2
  simp only [indicator_univ, Pi.one_apply, mul_one] at h2
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs, ENNReal.ofReal_eq_one] at h2
  exact h2

theorem gridFourier_tensorIdx (θ : Fin d → ℝ) :
    gridFourier (tensorIdx (d := d) k) θ = ∏ i, charFun (gridLaw 1 k) (θ i) := by
  haveI := isProbabilityMeasure_gridLaw (h := 1) hk0 hk1
  have h := charFun_zdLaw (h := 1) (isProbKernel_tensorIdx (d := d) hk0 hk1) (WithLp.toLp 2 θ)
  simp only [one_mul] at h
  rw [← h, zdLaw_tensorIdx_eq_tensorPow hk0 hk1.summable, (tensorPow_charFun (d := d)).2]

omit hk0 hk1 in
theorem tensorIdx_neg (hsymm : ∀ n, k (-n) = k n) (n : Zd d) :
    tensorIdx k (-n) = tensorIdx (d := d) k n := by
  simp [tensorIdx, hsymm]

omit hk1 in
theorem tensorIdx_ne_deltaZ (hd : 1 ≤ d) (h0 : k 0 < 1) : tensorIdx (d := d) k ≠ deltaZ := by
  intro h
  have h1 := congrFun h 0
  simp only [tensorIdx, Pi.zero_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    deltaZ, if_true] at h1
  exact (pow_lt_one₀ (hk0 0) h0 (by omega)).ne h1

end Tensor

theorem hasSum_binomialMask5 : HasSum binomialMask5 1 := by
  have hz : ∀ n ∉ Finset.Icc (-2 : ℤ) 2, binomialMask5 n = 0 := fun n hn => binomialMask5_eq_zero hn
  have hsum : ∑ n ∈ Finset.Icc (-2 : ℤ) 2, binomialMask5 n = 1 := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := binomialMask5_vals
    rw [show Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} by decide]
    simp [h1, h2, h3, h4, h5]
    norm_num
  exact hsum ▸ hasSum_sum_of_ne_finset_zero hz

theorem binomialMask5_nonneg (n : ℤ) : 0 ≤ binomialMask5 n := by
  rw [binomialMask5]; split_ifs <;> positivity

theorem binomialMask5_neg (n : ℤ) : binomialMask5 (-n) = binomialMask5 n := by
  by_cases hn : n ∈ Finset.Icc (-2 : ℤ) 2
  · obtain ⟨h1, h2, h3, h4, h5⟩ := binomialMask5_vals
    rw [show Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} by decide] at hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> simp [h1, h2, h3, h4, h5]
  · rw [binomialMask5_eq_zero hn, binomialMask5_eq_zero]
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn ⊢
    omega

/-- **A compound Poisson law of a finite symmetric measure is infinitely divisible**: its `n`-th
convolution root is the compound Poisson law of `L/n`, by the transforms (the argument of
`Pyramids.Line.GridTransfer`, here for a measure on `ℝ^d`). -/
theorem isInfinitelyDivisible_cpLaw_symm (L : Measure (Rd d)) [IsFiniteMeasure L]
    (hsym : L.map (fun x => -x) = L) : IsInfinitelyDivisible (cpLaw L) := by
  intro n hn
  have hn' : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne')
  haveI : IsFiniteMeasure ((n : ℝ≥0∞)⁻¹ • L) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hn'.lt_top (measure_lt_top _ _)⟩
  have hsym' : ((n : ℝ≥0∞)⁻¹ • L).map (fun x => -x) = (n : ℝ≥0∞)⁻¹ • L := by
    rw [Measure.map_smul, hsym]
  refine ⟨cpLaw ((n : ℝ≥0∞)⁻¹ • L), inferInstance, ?_⟩
  haveI := ScaleSpace.isFiniteMeasure_convPow_Rd (cpLaw ((n : ℝ≥0∞)⁻¹ • L)) n
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [AffineHemigroup.charFun_convPow, charFun_cpLaw_symm _ hsym', charFun_cpLaw_symm _ hsym,
    integral_smul_measure, ← Complex.ofReal_pow, ← Real.exp_nat_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  congr 2
  field_simp

/-! ## `prop:creation-grid-masks` -/

/-- **`prop:creation-grid-masks`(1).** The five-point resolvent `κ_t`, the frame mask
`(λ^L_a)^{⊗d}` and the binomial tensor mask `β^{⊗d}` are symmetric probabilities on `hℤ^d`,
different from `δ₀`. Since 2026-11-23 (review round 3, s6-7.S8) the clause no longer states
that their transforms are nonnegative: nothing read it, `prop:creation-grid` not requiring it. -/
theorem creation_grid_masks_1 (hd : 1 ≤ d) {h : ℝ} (hh : 0 < h) :
    (∀ t : ℝ, 0 < t → IsProbKernel (discreteHelmholtz d h t) ∧
      (∀ n, discreteHelmholtz d h t (-n) = discreteHelmholtz d h t n) ∧
      discreteHelmholtz d h t ≠ deltaZ) ∧
    (∀ a : ℝ, 0 < a → a < 1 → IsProbKernel (tensorIdx (d := d) (geomKernel a)) ∧
      (∀ n, tensorIdx (geomKernel a) (-n) = tensorIdx (d := d) (geomKernel a) n) ∧
      tensorIdx (d := d) (geomKernel a) ≠ deltaZ) ∧
    (IsProbKernel (tensorIdx (d := d) binomialMask5) ∧
      (∀ n, tensorIdx binomialMask5 (-n) = tensorIdx (d := d) binomialMask5 n) ∧
      tensorIdx (d := d) binomialMask5 ≠ deltaZ) := by
  refine ⟨fun t ht => ?_, fun a ha0 ha1 => ?_, ?_⟩
  · -- the five-point resolvent
    refine ⟨isProbKernel_discreteHelmholtz hd hh ht, fun n => ?_, fun hδ => ?_⟩
    · have hε : ∀ i : Fin d, (fun _ => (-1 : ℤ)) i = 1 ∨ (fun _ => (-1 : ℤ)) i = -1 :=
        fun _ => Or.inr rfl
      have := kappa_invariant (Equiv.refl (Fin d)) (fun _ => -1) hε h t n
      convert this using 2
      funext i
      simp [gmap]
    · have h1 := gridFourier_discreteHelmholtz hd hh ht (fun _ => Real.pi)
      rw [hδ, gridFourier_deltaZ] at h1
      have h2 : gridSymbol h (fun _ : Fin d => Real.pi) = (h ^ 2)⁻¹ * (4 * d) := by
        simp only [gridSymbol, Real.cos_pi, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
      have hpos : 0 < t ^ 2 * gridSymbol h (fun _ : Fin d => Real.pi) := by
        rw [h2]
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        positivity
      have h3 : (1 + t ^ 2 * gridSymbol h (fun _ : Fin d => Real.pi))⁻¹ = (1 : ℝ) := by
        exact_mod_cast h1.symm
      rw [inv_eq_one] at h3
      linarith
  · -- the frame mask
    have hk0 := geomKernel_nonneg ha0 ha1
    have hk1 := hasSum_geomKernel ha0 ha1
    refine ⟨isProbKernel_tensorIdx hk0 hk1, tensorIdx_neg geomKernel_symm,
      tensorIdx_ne_deltaZ hk0 hd ?_⟩
    simp only [geomKernel, Int.natAbs_zero, pow_zero, mul_one]
    rw [div_lt_one (by linarith)]
    linarith
  · -- the binomial tensor mask
    have hk0 := binomialMask5_nonneg
    have hk1 := hasSum_binomialMask5
    refine ⟨isProbKernel_tensorIdx hk0 hk1, tensorIdx_neg binomialMask5_neg,
      tensorIdx_ne_deltaZ hk0 hd ?_⟩
    rw [binomialMask5_vals.2.2.1]
    norm_num

/-- **`prop:creation-grid-masks`(2).** As laws on `hℤ^d`, the first two are infinitely divisible
and the third is not. -/
theorem creation_grid_masks_2 (hd : 1 ≤ d) {h : ℝ} (hh : 0 < h) :
    (∀ t : ℝ, 0 < t → IsInfinitelyDivisible (zdLaw d h (discreteHelmholtz d h t))) ∧
      (∀ a : ℝ, 0 < a → a < 1 → IsInfinitelyDivisible (zdLaw d h (tensorIdx (geomKernel a)))) ∧
      ¬ IsInfinitelyDivisible (zdLaw d h (tensorIdx binomialMask5)) := by
  refine ⟨fun t ht => ?_, fun a ha0 ha1 => ?_, ?_⟩
  · obtain ⟨⟨hprob, hs, -, -⟩, -, hp0, hp1, heq, -⟩ := resolvent_masks_exact_4_five hd hh ht
    haveI := hprob
    rw [heq]
    exact (resolventMask_compoundPoisson hs hp0.le hp1).1
  · -- the data `(0, ν_w)` of the frame mask (`isSymData_frame`, the proof of
    -- `prop:grid-pyramid-not-isotropic`(3)) make it the compound Poisson law of `ν_w`, which is
    -- infinitely divisible. Since 2026-11-23 (review round 3, s6-7.S8), in place of its exact grid
    -- pyramid and the criterion of `prop:exact-masks`(1), which read A49.
    rw [zdLaw_tensorIdx_eq_tensorPow (geomKernel_nonneg ha0 ha1)
      (hasSum_geomKernel ha0 ha1).summable]
    haveI := isProbabilityMeasure_geomMask ha0 ha1 h
    haveI := (tensorPow_charFun (d := d) (m := gridLaw h (geomKernel a))).1
    haveI := isFiniteMeasure_frameMaskNu (d := d) ha0 ha1 hh
    have hsym : (frameMaskNu d a h).map (fun x => -x) = frameMaskNu d a h :=
      (frameData (d := d) ha0 ha1 hh).ν_symm
    have hcp : tensorPow d (gridLaw h (geomKernel a)) = cpLaw (frameMaskNu d a h) := by
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      rw [charFun_cpLaw_symm _ hsym, isSymData_frame (d := d) ha0 ha1 hh ω]
      simp [SymLevyData.exponent, pairExponent, frameData_A ha0 ha1 hh, frameData_ν ha0 ha1 hh,
        quad_zero]
    rw [hcp]
    exact isInfinitelyDivisible_cpLaw_symm _ hsym
  · rw [zdLaw_tensorIdx_eq_tensorPow binomialMask5_nonneg hasSum_binomialMask5.summable]
    haveI := isProbabilityMeasure_gridLaw_binomial h
    haveI := (tensorPow_charFun (d := d) (m := gridLaw h binomialMask5)).1
    exact (no_bounded_step _ ⟨_, tensorPow_norm_gt_null (gridLaw_binomial_abs_gt_null hh)⟩
      (tensorPow_ne_dirac hd (charFun_gridLaw_binomial_pi hh))).1

/-- **`prop:creation-grid-masks`(3), the five-point resolvent.** For `w = κ_t`, integers `q ≥ 1`,
`k ≥ 0` and `𝒩` containing the axis neighbours, some bounded input has a level-`k` record with
exactly one `𝒩`-maximum, whose smoothing by `D_{q^k} w` has at least two, and a level-`(k+1)`
record with at least two. -/
theorem creation_grid_masks_3_resolvent (hd : 2 ≤ d) {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    {q : ℕ} (hq : 1 ≤ q) (k : ℕ) (N : Set (Zd d)) (haxis : axisNbrs d ⊆ N) :
    ∃ f : Zd d → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) ∧
      (∃! x, IsNMax N (decimRecord (discreteHelmholtz d h t) q f k) x) ∧
      (∃ x y, x ≠ y ∧
        IsNMax N (kconv (discreteHelmholtz d h t) (decimRecord (discreteHelmholtz d h t) q f k))
          x ∧
        IsNMax N (kconv (discreteHelmholtz d h t) (decimRecord (discreteHelmholtz d h t) q f k))
          y) ∧
      ∃ x y, x ≠ y ∧ IsNMax N (decimRecord (discreteHelmholtz d h t) q f (k + 1)) x ∧
        IsNMax N (decimRecord (discreteHelmholtz d h t) q f (k + 1)) y := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hw, hsymm, hne⟩ := (creation_grid_masks_1 hd1 hh).1 t ht
  exact records_creation hd hq k _ hw hsymm hne N haxis fun A hA =>
    creation_grid_3 hh _ hw hsymm ((creation_grid_masks_2 hd1 hh).1 t ht) q hq k A hA

/-- **`prop:creation-grid-masks`(3), the frame mask.** The same for `w = (λ^L_a)^{⊗d}`. -/
theorem creation_grid_masks_3_frame (hd : 2 ≤ d) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {q : ℕ} (hq : 1 ≤ q) (k : ℕ) (N : Set (Zd d)) (haxis : axisNbrs d ⊆ N) :
    ∃ f : Zd d → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) ∧
      (∃! x, IsNMax N (decimRecord (tensorIdx (geomKernel a)) q f k) x) ∧
      (∃ x y, x ≠ y ∧
        IsNMax N (kconv (tensorIdx (geomKernel a)) (decimRecord (tensorIdx (geomKernel a)) q f k))
          x ∧
        IsNMax N (kconv (tensorIdx (geomKernel a)) (decimRecord (tensorIdx (geomKernel a)) q f k))
          y) ∧
      ∃ x y, x ≠ y ∧ IsNMax N (decimRecord (tensorIdx (geomKernel a)) q f (k + 1)) x ∧
        IsNMax N (decimRecord (tensorIdx (geomKernel a)) q f (k + 1)) y := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hw, hsymm, hne⟩ := (creation_grid_masks_1 hd1 one_pos).2.1 a ha0 ha1
  exact records_creation hd hq k _ hw hsymm hne N haxis fun A hA =>
    creation_grid_3 one_pos _ hw hsymm ((creation_grid_masks_2 hd1 one_pos).2.1 a ha0 ha1) q hq
      k A hA

end Pyramids
