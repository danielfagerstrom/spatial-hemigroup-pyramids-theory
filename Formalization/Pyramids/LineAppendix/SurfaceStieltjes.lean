/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.SurfaceSlab
import Mathlib.Probability.Kernel.Disintegration.MeasurableStieltjes
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# `thm:surface-measure`: a measure on the quadrant from a monotone family of measures

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:surface-measure`. Wave 3a. The existence half
of the passage from a family to `Λ`, stated for any monotone family `(ϖ_t)` of measures on
`(0,∞)` that vanishes for `t ≤ 0`, is finite on every `(ε,∞)` and is right-continuous in `t` on the
sets bounded away from `0` (`exists_slab_of_monotone`): some `Λ` on the quadrant has
`Λ((0,t] × ·) = ϖ_t` for every `t > 0`.

## The route

The measure is built as `W ⊗ κ`, read with the coordinates swapped, for a base measure `W` on the
`v`-axis and a kernel `κ` from `v` to the `y`-axis; this replaces the Lebesgue–Stieltjes theorem in
two variables of the proof of record.

* **On `(0,T]`** (`exists_slab_bounded`): `W := ϖ_T`, and for rational `r` the densities
  `h(v,r) = min(1, dϖ_r/dW(v))` (`0` for `r ≤ 0`, `1` for `r ≥ T`). Their running supremum
  `f(v,r) = sup_{r' ≤ r} h(v,r')` is monotone in `r` for every `v`, and its right-continuous
  regularization `F(v,r) = inf_{r' > r} f(v,r')` is a rational distribution function for every `v`
  (`slabCDF_isMeasurableRatCDF`). Mathlib's measurable Stieltjes construction turns it into a
  Markov kernel `κ`, with `κ(v)(-∞,t] = inf_{r > t} f(v,r)`. Since `h(v,·)` is monotone for
  `W`-a.e. `v`, `f(v,r) = h(v,r)` a.e., so `∫_A f(·,r) dW = ϖ_r(A)`; monotone convergence and the
  right-continuity of `t ↦ ϖ_t(A)` give `∫_A κ(v)(-∞,t] W(dv) = ϖ_t(A)`.
* **Gluing**: the measures for `T = n + 1`, restricted to `(n, n+1] × ℝ`, are summed; by
  `quadrant_measure_ext`, the one for `T = N + 1` restricted to `(0, n+1] × ℝ` is the one for
  `T = n + 1`.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal

/-! ## Infima over the rationals -/

/-- `inf_{r > x} inf_{r' > r} g(r') = inf_{r' > x} g(r')`, over rationals, for real `x`. -/
theorem iInf_rat_gt_iInf_Ioi (g : ℚ → ℝ≥0∞) (x : ℝ) :
    ⨅ r : {r : ℚ // x < r}, ⨅ r' : Ioi (r : ℚ), g r' = ⨅ r' : {r' : ℚ // x < r'}, g r' := by
  refine le_antisymm (le_iInf fun r' => ?_) (le_iInf fun r => le_iInf fun r' => ?_)
  · obtain ⟨r, hxr, hrr'⟩ := exists_rat_btwn r'.2
    refine (iInf_le _ ⟨r, hxr⟩).trans (iInf_le_of_le ⟨r'.1, ?_⟩ le_rfl)
    exact_mod_cast hrr'
  · refine iInf_le_of_le ⟨r'.1, lt_trans r.2 ?_⟩ le_rfl
    exact_mod_cast r'.2

/-- `inf_{r > t} inf_{r' > r} g(r') = inf_{r' > t} g(r')`, over rationals. -/
theorem iInf_Ioi_iInf_Ioi (g : ℚ → ℝ≥0∞) (t : ℚ) :
    ⨅ r : Ioi t, ⨅ r' : Ioi (r : ℚ), g r' = ⨅ r' : Ioi t, g r' := by
  refine le_antisymm (le_iInf fun r' => ?_) (le_iInf fun r => le_iInf fun r' => ?_)
  · obtain ⟨r, htr, hrr'⟩ := exists_between (mem_Ioi.1 r'.2)
    exact (iInf_le _ ⟨r, htr⟩).trans (iInf_le_of_le ⟨r'.1, mem_Ioi.2 hrr'⟩ le_rfl)
  · exact iInf_le_of_le ⟨r'.1, mem_Ioi.2 (lt_trans (mem_Ioi.1 r.2) (mem_Ioi.1 r'.2))⟩ le_rfl

/-! ## The distribution functions -/

section Construction

variable (W : Measure ℝ) (ϖ : ℝ → Measure ℝ) (T : ℝ)

/-- `h(v, r)`: `0` for `r ≤ 0`, `1` for `r ≥ T`, and `min(1, dϖ_r/dW(v))` between. -/
noncomputable def slabDensity (v : ℝ) (r : ℚ) : ℝ≥0∞ :=
  if (r : ℝ) ≤ 0 then 0 else if T ≤ r then 1 else min 1 ((ϖ r).rnDeriv W v)

/-- `f(v, r) := sup_{r' ≤ r} h(v, r')`, monotone in `r`. -/
noncomputable def slabCDFAux (v : ℝ) (r : ℚ) : ℝ≥0∞ := ⨆ r' : Iic r, slabDensity W ϖ T v r'

/-- `F(v, r) := inf_{r' > r} f(v, r')`, monotone and right-continuous in `r`. -/
noncomputable def slabCDF (v : ℝ) (r : ℚ) : ℝ≥0∞ := ⨅ r' : Ioi r, slabCDFAux W ϖ T v r'

variable {W ϖ T}

theorem slabDensity_le_one (v : ℝ) (r : ℚ) : slabDensity W ϖ T v r ≤ 1 := by
  unfold slabDensity
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact min_le_left _ _

theorem slabCDFAux_le_one (v : ℝ) (r : ℚ) : slabCDFAux W ϖ T v r ≤ 1 :=
  iSup_le fun _ => slabDensity_le_one v _

theorem slabCDF_le_one (v : ℝ) (r : ℚ) : slabCDF W ϖ T v r ≤ 1 :=
  iInf_le_of_le ⟨r + 1, by simp⟩ (slabCDFAux_le_one v _)

theorem slabCDF_ne_top (v : ℝ) (r : ℚ) : slabCDF W ϖ T v r ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (slabCDF_le_one v r)

theorem measurable_slabDensity (r : ℚ) : Measurable fun v => slabDensity W ϖ T v r := by
  unfold slabDensity
  split_ifs
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const.min (Measure.measurable_rnDeriv _ _)

theorem measurable_slabCDFAux (r : ℚ) : Measurable fun v => slabCDFAux W ϖ T v r :=
  Measurable.iSup fun _ => measurable_slabDensity _

theorem measurable_slabCDF (r : ℚ) : Measurable fun v => slabCDF W ϖ T v r :=
  Measurable.iInf fun _ => measurable_slabCDFAux _

theorem slabCDFAux_mono (v : ℝ) {r s : ℚ} (h : r ≤ s) :
    slabCDFAux W ϖ T v r ≤ slabCDFAux W ϖ T v s :=
  iSup_le fun r' => le_iSup_of_le ⟨r'.1, le_trans (mem_Iic.1 r'.2) h⟩ le_rfl

theorem slabCDF_mono (v : ℝ) {r s : ℚ} (h : r ≤ s) : slabCDF W ϖ T v r ≤ slabCDF W ϖ T v s :=
  le_iInf fun r' => iInf_le_of_le ⟨r'.1, lt_of_le_of_lt h r'.2⟩ le_rfl

theorem slabCDFAux_eq_zero (v : ℝ) {r : ℚ} (hr : (r : ℝ) ≤ 0) : slabCDFAux W ϖ T v r = 0 := by
  refine le_antisymm (iSup_le fun r' => ?_) zero_le
  have h' : ((r'.1 : ℚ) : ℝ) ≤ 0 := le_trans (by exact_mod_cast mem_Iic.1 r'.2) hr
  rw [slabDensity, if_pos h']

theorem slabCDF_eq_zero (v : ℝ) {r : ℚ} (hr : r < 0) : slabCDF W ϖ T v r = 0 := by
  refine le_antisymm (iInf_le_of_le ⟨r / 2, ?_⟩ ?_) zero_le
  · change r < r / 2
    linarith
  · refine (slabCDFAux_eq_zero v ?_).le
    have : r / 2 < 0 := by linarith
    exact_mod_cast this.le

theorem slabCDF_eq_one (hT : 0 < T) (v : ℝ) {r : ℚ} (hr : T ≤ r) : slabCDF W ϖ T v r = 1 := by
  refine le_antisymm (slabCDF_le_one v r)
    (le_iInf fun r' => le_iSup_of_le ⟨r'.1, mem_Iic.2 le_rfl⟩ ?_)
  have h1 : T ≤ ((r'.1 : ℚ) : ℝ) := hr.trans (by exact_mod_cast (mem_Ioi.1 r'.2).le)
  rw [slabDensity, if_neg (not_le.2 (hT.trans_le h1)), if_pos h1]

/-- **`F` is a rational distribution function at every `v`**, measurable in `v`. -/
theorem slabCDF_isMeasurableRatCDF (hT : 0 < T) :
    IsMeasurableRatCDF fun v r => (slabCDF W ϖ T v r).toReal := by
  refine ⟨fun v => ⟨fun r s h => ENNReal.toReal_mono (slabCDF_ne_top v s) (slabCDF_mono v h),
    ?_, ?_, fun t => ?_⟩, measurable_pi_lambda _ fun r => (measurable_slabCDF r).ennreal_toReal⟩
  · obtain ⟨N, hN⟩ := exists_rat_gt T
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with r hr
    rw [slabCDF_eq_one hT v (hN.le.trans (by exact_mod_cast hr)), ENNReal.toReal_one]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_atBot 0] with r hr
    rw [slabCDF_eq_zero v hr, ENNReal.toReal_zero]
  · rw [← ENNReal.toReal_iInf fun r => slabCDF_ne_top v _]
    congr 1
    exact iInf_Ioi_iInf_Ioi _ t

/-- **The kernel** `v ↦ dF(v, ·)`. -/
noncomputable def slabKernel (hT : 0 < T) : Kernel ℝ ℝ where
  toFun v := ((slabCDF_isMeasurableRatCDF (W := W) (ϖ := ϖ) hT).stieltjesFunction v).measure
  measurable' := (slabCDF_isMeasurableRatCDF hT).measurable_measure_stieltjesFunction

instance (hT : 0 < T) : IsMarkovKernel (slabKernel (W := W) (ϖ := ϖ) hT) :=
  ⟨fun v => (slabCDF_isMeasurableRatCDF hT).instIsProbabilityMeasure_stieltjesFunction v⟩

/-- `κ(v)(-∞, t] = inf_{r > t} f(v, r)`. -/
theorem slabKernel_Iic (hT : 0 < T) (v t : ℝ) :
    slabKernel (W := W) (ϖ := ϖ) hT v (Iic t) = ⨅ r : {r : ℚ // t < r}, slabCDFAux W ϖ T v r := by
  set hF := slabCDF_isMeasurableRatCDF (W := W) (ϖ := ϖ) hT
  change (hF.stieltjesFunction v).measure (Iic t) = _
  rw [hF.measure_stieltjesFunction_Iic, ← (hF.stieltjesFunction v).iInf_rat_gt_eq t]
  simp_rw [hF.stieltjesFunction_eq]
  rw [← ENNReal.toReal_iInf fun r => slabCDF_ne_top v _, ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top (iInf_le_of_le
      (⟨(exists_rat_gt t).choose, (exists_rat_gt t).choose_spec⟩ : {r : ℚ // t < r})
      (slabCDF_le_one v _)))]
  exact iInf_rat_gt_iInf_Ioi _ t

end Construction

/-! ## On `(0, T]` -/

section Bounded

variable {W : Measure ℝ} {ϖ : ℝ → Measure ℝ} {T : ℝ}

/-- `h(v, ·)` is monotone for `W`-a.e. `v`, so `f(v, r) = h(v, r)` a.e. -/
theorem ae_slabCDFAux_eq [SigmaFinite W] (hmono : Monotone ϖ) (hle : ∀ t : ℝ, ϖ t ≤ W) :
    ∀ᵐ v ∂W, ∀ r : ℚ, slabCDFAux W ϖ T v r = slabDensity W ϖ T v r := by
  have hsf : ∀ t : ℝ, SigmaFinite (ϖ t) := fun t => Measure.sigmaFinite_of_le W (hle t)
  have hpair : ∀ᵐ v ∂W, ∀ r' r : ℚ, r' ≤ r → slabDensity W ϖ T v r' ≤ slabDensity W ϖ T v r := by
    refine ae_all_iff.2 fun r' => ae_all_iff.2 fun r => ?_
    by_cases hrr : r' ≤ r
    swap
    · exact ae_of_all _ fun v h => absurd h hrr
    have hrr' : (r' : ℝ) ≤ r := by exact_mod_cast hrr
    by_cases h0 : (r' : ℝ) ≤ 0
    · exact ae_of_all _ fun v _ => by rw [slabDensity, if_pos h0]; exact zero_le
    by_cases hT : T ≤ (r : ℝ)
    · have h1 : ∀ v, slabDensity W ϖ T v r = 1 := fun v => by
        rw [slabDensity, if_neg (by linarith), if_pos hT]
      exact ae_of_all _ fun v _ => (h1 v).symm ▸ slabDensity_le_one v r'
    have hT' : ¬ T ≤ (r' : ℝ) := fun h => hT (h.trans hrr')
    have hrn : (ϖ r').rnDeriv W ≤ᵐ[W] (ϖ r).rnDeriv W := by
      refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
        fun s _ _ => ?_
      rw [Measure.setLIntegral_rnDeriv (Measure.absolutelyContinuous_of_le (hle _)),
        Measure.setLIntegral_rnDeriv (Measure.absolutelyContinuous_of_le (hle _))]
      exact Measure.le_iff'.1 (hmono hrr') s
    filter_upwards [hrn] with v hv _
    rw [slabDensity, if_neg h0, if_neg hT', slabDensity, if_neg (by linarith), if_neg hT]
    exact min_le_min le_rfl hv
  filter_upwards [hpair] with v hv r
  exact le_antisymm (iSup_le fun r' => hv r'.1 r (mem_Iic.1 r'.2))
    (le_iSup_of_le ⟨r, mem_Iic.2 le_rfl⟩ le_rfl)

/-- `∫_A h(·, r) dW = ϖ_r(A)`. -/
theorem setLIntegral_slabDensity [SigmaFinite W] (hzero : ∀ t : ℝ, t ≤ 0 → ϖ t = 0)
    (htop : ∀ t : ℝ, T ≤ t → ϖ t = W) (hle : ∀ t : ℝ, ϖ t ≤ W) (r : ℚ) (A : Set ℝ) :
    ∫⁻ v in A, slabDensity W ϖ T v r ∂W = ϖ r A := by
  have hsf : SigmaFinite (ϖ r) := Measure.sigmaFinite_of_le W (hle r)
  unfold slabDensity
  split_ifs with h0 hT
  · rw [lintegral_zero, hzero _ h0, Measure.coe_zero, Pi.zero_apply]
  · rw [setLIntegral_one, htop _ hT]
  · rw [← Measure.setLIntegral_rnDeriv (Measure.absolutelyContinuous_of_le (hle r)) A]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [Measure.rnDeriv_le_one_of_le (hle r)] with v hv
    exact min_eq_right hv

/-- **The main identity**: `∫_A inf_{r > t} f(v, r) W(dv) = ϖ_t(A)` for `A ⊆ (ε,∞)`, by monotone
convergence and the right-continuity of `t ↦ ϖ_t(A)`. -/
theorem setLIntegral_iInf_slabCDFAux [SigmaFinite W] (hmono : Monotone ϖ)
    (hzero : ∀ t : ℝ, t ≤ 0 → ϖ t = 0) (htop : ∀ t : ℝ, T ≤ t → ϖ t = W)
    (hright : ∀ t ε : ℝ, 0 < ε → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioi ε →
      Tendsto (fun r => ϖ r A) (𝓝[>] t) (𝓝 (ϖ t A)))
    (hWfin : ∀ ε : ℝ, 0 < ε → W (Ioi ε) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) {A : Set ℝ}
    (hA : MeasurableSet A) (hAε : A ⊆ Ioi ε) (t : ℝ) :
    ∫⁻ v in A, ⨅ r : {r : ℚ // t < r}, slabCDFAux W ϖ T v r ∂W = ϖ t A := by
  have hle : ∀ s : ℝ, ϖ s ≤ W := fun s =>
    (hmono (le_max_left s T)).trans_eq (htop _ (le_max_right s T))
  have hWA : W A ≠ ⊤ := ne_top_of_le_ne_top (hWfin ε hε) (measure_mono hAε)
  have hr : ∀ r : ℚ, ∫⁻ v in A, slabCDFAux W ϖ T v r ∂W = ϖ r A := by
    intro r
    rw [← setLIntegral_slabDensity hzero htop hle r A]
    exact lintegral_congr_ae (ae_restrict_of_ae
      ((ae_slabCDFAux_eq hmono hle).mono fun v hv => hv r))
  have hlim : ⨅ r : {r : ℚ // t < r}, ϖ r A = ϖ t A := by
    refine le_antisymm ?_ (le_iInf fun r => Measure.le_iff'.1 (hmono r.2.le) A)
    refine ge_of_tendsto (hright t ε hε A hA hAε) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    obtain ⟨r, htr, hrs⟩ := exists_rat_btwn (mem_Ioi.1 hs)
    exact (iInf_le _ ⟨r, htr⟩).trans (Measure.le_iff'.1 (hmono hrs.le) A)
  by_cases h0 : W A = 0
  · rw [setLIntegral_measure_zero _ _ h0]
    exact (nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 (hle t) A).trans h0.le)).symm
  rw [lintegral_iInf_directed_of_measurable (Measure.restrict_eq_zero.not.2 h0)
    (fun r => measurable_slabCDFAux _) (fun r => ?_) ?_]
  · simp_rw [hr]
    exact hlim
  · intro r1 r2
    refine ⟨⟨min r1.1 r2.1, ?_⟩, fun v => slabCDFAux_mono v (min_le_left _ _),
      fun v => slabCDFAux_mono v (min_le_right _ _)⟩
    rw [Rat.cast_min]
    exact lt_min r1.2 r2.2
  · rw [hr]
    exact ne_top_of_le_ne_top hWA (Measure.le_iff'.1 (hle r) A)

/-- **On `(0,T]`**: a monotone family `ϖ` vanishing for `t ≤ 0`, equal to `W` for `t ≥ T` and
right-continuous on the sets bounded away from `0` is the family of slabs of some `Λ` on the
quadrant. -/
theorem exists_slab_bounded (hT : 0 < T) (hW0 : W (Iic 0) = 0)
    (hWfin : ∀ ε : ℝ, 0 < ε → W (Ioi ε) ≠ ⊤) (hmono : Monotone ϖ)
    (hzero : ∀ t : ℝ, t ≤ 0 → ϖ t = 0) (htop : ∀ t : ℝ, T ≤ t → ϖ t = W)
    (hright : ∀ t ε : ℝ, 0 < ε → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioi ε →
      Tendsto (fun r => ϖ r A) (𝓝[>] t) (𝓝 (ϖ t A))) :
    ∃ Λ : Measure (ℝ × ℝ), Λ quadrantᶜ = 0 ∧ ∀ t : ℝ, 0 < t → slab Λ 0 t = ϖ t := by
  haveI : SigmaFinite W := sigmaFinite_of_Ioi hW0 hWfin
  have hle : ∀ s : ℝ, ϖ s ≤ W := fun s =>
    (hmono (le_max_left s T)).trans_eq (htop _ (le_max_right s T))
  set Λ := (W.compProd (slabKernel (W := W) (ϖ := ϖ) hT)).map Prod.swap with hΛ
  have hprod : ∀ S A : Set ℝ, MeasurableSet S → MeasurableSet A →
      Λ (S ×ˢ A) = ∫⁻ v in A, slabKernel (W := W) (ϖ := ϖ) hT v S ∂W := by
    intro S A hS hA
    rw [hΛ, Measure.map_apply measurable_swap (hS.prod hA), preimage_swap_prod,
      Measure.compProd_apply_prod hA hS]
  have hIic : ∀ t ε : ℝ, 0 < ε → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioi ε →
      Λ (Iic t ×ˢ A) = ϖ t A := by
    intro t ε hε A hA hAε
    rw [hprod _ _ measurableSet_Iic hA]
    simp_rw [slabKernel_Iic]
    exact setLIntegral_iInf_slabCDFAux hmono hzero htop hright hWfin hε hA hAε t
  have hquad : Λ quadrantᶜ = 0 := by
    have hsub : quadrantᶜ ⊆ (univ ×ˢ Iic 0) ∪ ⋃ n : ℕ, Iic 0 ×ˢ Ioi (1 / ((n : ℝ) + 1)) := by
      rintro ⟨y, v⟩ hp
      simp only [quadrant, mem_compl_iff, mem_prod, mem_Ioi, not_and_or, not_lt] at hp
      rcases le_or_gt v 0 with hv | hv
      · exact Or.inl ⟨trivial, hv⟩
      · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hv
        exact Or.inr (mem_iUnion.2 ⟨n, hp.resolve_right (not_le.2 hv), hn⟩)
    refine measure_mono_null hsub (measure_union_null ?_ (measure_iUnion_null fun n => ?_))
    · rw [hprod _ _ MeasurableSet.univ measurableSet_Iic]
      exact setLIntegral_measure_zero _ _ hW0
    · rw [hIic 0 _ (by positivity) _ measurableSet_Ioi le_rfl, hzero 0 le_rfl,
        Measure.coe_zero, Pi.zero_apply]
  refine ⟨Λ, hquad, fun t ht => ?_⟩
  refine measure_ext_of_Ioi (slab_Iic_zero hquad 0 t)
    (nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 (hle t) _).trans hW0.le))
    fun ε hε A hA hAε => ?_
  rw [slab_apply _ _ _ hA, ← hIic t ε hε A hA hAε, ← Iic_union_Ioc_eq_Iic ht.le, union_prod,
    measure_union (Disjoint.set_prod_left (Iic_disjoint_Ioc le_rfl) _ _)
      (measurableSet_Ioc.prod hA), hIic 0 ε hε A hA hAε, hzero 0 le_rfl, Measure.coe_zero,
    Pi.zero_apply, zero_add]

end Bounded

/-! ## Gluing -/

/-- **A monotone family of measures on `(0,∞)` is the family of slabs of a measure on the
quadrant**: if `ϖ_t = 0` for `t ≤ 0`, each `ϖ_t` is null on `(-∞,0]` and finite on every `(ε,∞)`,
and `t ↦ ϖ_t(A)` is right-continuous for every Borel `A` bounded away from `0`, then some `Λ` on the
quadrant has `Λ((0,t] × ·) = ϖ_t` for every `t > 0`. -/
theorem exists_slab_of_monotone {ϖ : ℝ → Measure ℝ} (hmono : Monotone ϖ)
    (hzero : ∀ t : ℝ, t ≤ 0 → ϖ t = 0) (hpos : ∀ t : ℝ, ϖ t (Iic 0) = 0)
    (hfin : ∀ t ε : ℝ, 0 < ε → ϖ t (Ioi ε) ≠ ⊤)
    (hright : ∀ t ε : ℝ, 0 < ε → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioi ε →
      Tendsto (fun r => ϖ r A) (𝓝[>] t) (𝓝 (ϖ t A))) :
    ∃ Λ : Measure (ℝ × ℝ), Λ quadrantᶜ = 0 ∧ ∀ t : ℝ, 0 < t → slab Λ 0 t = ϖ t := by
  -- the truncations at `n + 1`
  have hn : ∀ n : ℕ, ∃ Λ : Measure (ℝ × ℝ), Λ quadrantᶜ = 0 ∧
      ∀ t : ℝ, 0 < t → slab Λ 0 t = ϖ (min t ((n : ℝ) + 1)) := by
    intro n
    have hT : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine exists_slab_bounded (W := ϖ ((n : ℝ) + 1)) (ϖ := fun t => ϖ (min t ((n : ℝ) + 1)))
      hT (hpos _) (hfin _)
      (fun s t hst => hmono (min_le_min hst le_rfl))
      (fun t ht => hzero _ ((min_le_left _ _).trans ht))
      (fun t ht => by simp only [min_eq_right ht]) fun t ε hε A hA hAε => ?_
    rcases lt_or_ge t ((n : ℝ) + 1) with htT | htT
    · rw [min_eq_left htT.le]
      refine (hright t ε hε A hA hAε).congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with r hr
      rw [min_eq_left (le_of_lt hr)]
    · rw [min_eq_right htT]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [min_eq_right (htT.trans (le_of_lt hr))]
  choose Λs hΛc hΛs using hn
  -- consistency
  have hcons : ∀ m N : ℕ, m ≤ N → (Λs N).restrict (Ioc 0 ((m : ℝ) + 1) ×ˢ univ) = Λs m := by
    intro m N hmN
    have hmN' : (m : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmN 1
    have hslab : ∀ t : ℝ, 0 < t → slab ((Λs N).restrict (Ioc 0 ((m : ℝ) + 1) ×ˢ univ)) 0 t =
        ϖ (min t ((m : ℝ) + 1)) := by
      intro t ht
      rw [slab_restrict, hΛs N _ (lt_min ht (by positivity)), min_assoc, min_eq_left hmN']
    refine quadrant_measure_ext ?_ (hΛc m) (fun t ht ε hε => ?_) (fun t ht => ?_)
    · exact nonpos_iff_eq_zero.1
        ((Measure.le_iff'.1 Measure.restrict_le_self _).trans (hΛc N).le)
    · rw [hslab t ht]
      exact hfin _ ε hε
    · rw [hslab t ht, hΛs m t ht]
  -- the sum
  set S : ℕ → Set (ℝ × ℝ) := fun n => Ioc (n : ℝ) ((n : ℝ) + 1) ×ˢ univ with hS
  set Λ := Measure.sum fun n => (Λs n).restrict (S n) with hΛ
  have hquad : Λ quadrantᶜ = 0 := by
    have hqm : MeasurableSet quadrantᶜ := (measurableSet_Ioi.prod measurableSet_Ioi).compl
    rw [hΛ, Measure.sum_apply _ hqm]
    exact ENNReal.tsum_eq_zero.2 fun n => nonpos_iff_eq_zero.1
      ((Measure.le_iff'.1 Measure.restrict_le_self _).trans (hΛc n).le)
  refine ⟨Λ, hquad, fun t ht => ?_⟩
  set N : ℕ := ⌈t⌉₊ with hN
  have htN : t ≤ N := Nat.le_ceil t
  refine measure_ext_of_Ioi (slab_Iic_zero hquad 0 t) (hpos t) fun ε hε A hA hAε => ?_
  set X := Ioc 0 t ×ˢ A with hX
  have hXm : MeasurableSet X := measurableSet_Ioc.prod hA
  have hSm : ∀ n, MeasurableSet (S n) := fun n => measurableSet_Ioc.prod MeasurableSet.univ
  rw [slab_apply _ _ _ hA, ← hX, hΛ, Measure.sum_apply _ hXm]
  simp_rw [Measure.restrict_apply hXm]
  rw [tsum_eq_sum (s := Finset.range N) (fun n hn => ?_)]
  · have hterm : ∀ n ∈ Finset.range N, (Λs n) (X ∩ S n) = (Λs N) (X ∩ S n) := by
      intro n hn
      rw [← hcons n N (Finset.mem_range.1 hn).le, Measure.restrict_apply
        (hXm.inter (hSm n)), inter_eq_left.2 (inter_subset_right.trans
          (Set.prod_mono (Ioc_subset_Ioc_left (Nat.cast_nonneg n)) le_rfl))]
    rw [Finset.sum_congr rfl hterm, ← measure_biUnion_finset (fun n _ m _ hnm => ?_)
      (fun n _ => hXm.inter (hSm n))]
    · have hcover : ⋃ n ∈ Finset.range N, X ∩ S n = X := by
        refine subset_antisymm (iUnion₂_subset fun n _ => inter_subset_left) fun p hp => ?_
        have hy : 0 < p.1 := hp.1.1
        have hc1 : 1 ≤ ⌈p.1⌉₊ := Nat.one_le_ceil_iff.2 hy
        have hcN : ⌈p.1⌉₊ ≤ N := Nat.ceil_mono hp.1.2
        refine mem_iUnion₂.2 ⟨⌈p.1⌉₊ - 1, Finset.mem_range.2 (by omega), hp, ⟨?_, ?_⟩, trivial⟩
        · rw [Nat.cast_sub hc1, Nat.cast_one]
          linarith [Nat.ceil_lt_add_one hy.le]
        · rw [Nat.cast_sub hc1, Nat.cast_one, sub_add_cancel]
          exact Nat.le_ceil _
      rw [hcover, hX, ← slab_apply _ _ _ hA, hΛs N t ht,
        min_eq_left (htN.trans (by linarith))]
    · rcases lt_or_gt_of_ne hnm with h | h
      · exact Disjoint.mono inter_subset_right inter_subset_right
          (Disjoint.set_prod_left (Ioc_disjoint_Ioc_of_le (by exact_mod_cast h)) _ _)
      · exact Disjoint.mono inter_subset_right inter_subset_right
          (Disjoint.set_prod_left (Ioc_disjoint_Ioc_of_le (by exact_mod_cast h)) _ _).symm
  · have hNn : (N : ℝ) ≤ n := by exact_mod_cast not_lt.1 (Finset.mem_range.not.1 hn)
    have hempty : X ∩ S n = ∅ := eq_empty_of_forall_notMem fun p hp =>
      absurd (hp.1.1.2.trans (htN.trans hNn)) (not_le.2 hp.2.1.1)
    rw [hempty, measure_empty]

end Pyramids
