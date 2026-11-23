/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.GridTransfer
import Pyramids.Pyramid.LadderCoupling
import Pyramids.Pyramid.LadderDivergent
import Pyramids.Pyramid.LadderStratum

/-!
# `prop:grid-pyramids-infinitely-divisible`(1)–(3): which masks have an exact grid pyramid

Blueprint: `blueprint/src/parts/02-line.tex`, `prop:grid-pyramids-infinitely-divisible`. Wave 3e:
ten of the node's twelve declarations moved here from `PyramidsSkeleton.Ch02Line`, unchanged in
name and conclusion; four of them drop hypotheses their proofs do not read (2026-11-15, a
strengthening): `grid_pyramids_id_2_knot` the spacing `0 < h`, `grid_pyramids_id_2_no_kernel` the
infinite divisibility of `w` (a mask with a folded Lévy measure is infinitely divisible),
`grid_pyramids_id_2_coupling` both, and `grid_pyramids_id_3_general` the symmetry and the unit
mass of `ϱ`. Clause (4) is `Pyramids.Line.GeometricMask`.

## The route

An assembly of the chapter-3 nodes at `d = 1`, through `Pyramids.Line.GridTransfer`.

* **(1)** `lem:lattice-infinitely-divisible` at `d = 1` on the lift (`exists_maskLevyMeasure`); the
  converse by the compound Poisson law; the positive transform from the exponent;
  `prop:no-bounded-step` at `d = 1` for the support.
* **(2)** `prop:ladder-knot-kernel`(1) on the lifted kernels gives the moment, the knot data and the
  product (`carries_knot`); (2) of that node gives a family in `ℝ¹`, read back on `ℝ`
  (`carries_of_hasLadder`); its two moments give the second criterion. The knot data `(0, ϖ_1)`:
  the lift of `ϖ_1` is `ν*` of the lift of `ϖ_w`, and a folded measure is determined by its lift.
  `ϖ_1` has the atoms `q^{-m}v₀` of an atom `v₀ ∈ hℤ_{>0}` of `ϖ_w`, which come below any `ξ`.
  Without the moment, (3) of that node; the frequency `ω = 2π/h` of
  `prop:ladder-not-every-frequency` with its law dilated by `h`. The uniform coupling is the family
  of (2) of that node, whose kernel at `t ∈ [1, q]` has the data `D* + (log_q t) D_ϱ`.
* **(3)** `prop:ladder-knot-kernel`(4)(a) at `d = 1` with the lattice `ξℤ`; a family carrying the
  ladder has the step `μ_{1,q} = w`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X CascadeCore CascadeFamily IsScaleCovariant IsKernelFamily IsSymmetric
  SymLevyPair)
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace

/-! ## Lifts of masks -/

theorem isProbabilityMeasure_map_lineEmb (w : Measure ℝ) [IsProbabilityMeasure w] :
    IsProbabilityMeasure (w.map lineEmbL) :=
  Measure.isProbabilityMeasure_map lineEmbL.continuous.aemeasurable

theorem map_lineEmb_ne_dirac {w : Measure ℝ} (hne : w ≠ Measure.dirac 0) :
    w.map lineEmbL ≠ Measure.dirac 0 := fun h => hne (by
  rw [← map_lineProj_lineEmb w, h, Measure.map_dirac' lineProjL.continuous.measurable, map_zero])

theorem lintegral_posLog_toData_mask (ϖ : Measure ℝ) (hfin : IsFiniteMeasure ϖ)
    (hfold : ScaleSpace.IsFolded ϖ) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(SymLevyPair_toData (maskPair ϖ hfin hfold)).ν =
      ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ :=
  lintegral_posLog_symLift ϖ

theorem lintegral_posLog_map_lineEmb (w : Measure ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.posLog ‖y‖) ∂(w.map lineEmbL) =
      ∫⁻ x, ENNReal.ofReal (Real.posLog |x|) ∂w := by
  rw [lintegral_map (by fun_prop) lineEmbL.continuous.measurable]
  simp_rw [lineEmbL_apply, norm_lineEmb]

/-! ## The knot kernel of a family carrying the ladder -/

/-- **`prop:ladder-knot-kernel`(1) on the line.** For a family carrying the grid ladder of a mask
with the folded Lévy measure `ϖ`, and folded data `P₁` of `μ_{0,1}`: the partial products tend to
`μ̂_{0,1}`, `P₁ = (0, ϖ_1)`, and `∫ log₊ v ϖ(dv) < ∞`. -/
theorem carries_knot {q : ℝ} (hq : 1 < q) {w ϖ : Measure ℝ} (hϖ : IsMaskLevyMeasure w ϖ)
    {Φ : ℝ → ℝ → (X →L[ℝ] X)} {S : ℝ → ℝ → ℝ} {μ : ℝ → ℝ → Measure ℝ}
    (hc : CarriesGridLadder q w Φ S μ) {P1 : SymLevyPair} (hP1 : IsFoldedData (μ 0 1) P1) :
    (∀ ω : ℝ, Tendsto (fun M => ladderPartialProduct q w M ω) atTop (𝓝 (charFun (μ 0 1) ω))) ∧
      P1.a = 0 ∧ P1.ν = knotLevyMeasure q ϖ ∧ ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ < ⊤ := by
  obtain ⟨hsym, hcov, hstep⟩ := hc.family
  have hDρ : IsSymData ((μ 1 q).map lineEmbL) (SymLevyPair_toData (maskPair ϖ hϖ.1 hϖ.2.1)) := by
    rw [hstep]
    exact isSymData_lineEmb_of_folded hϖ.isFoldedData
  obtain ⟨hlim, hA, hν, hmom⟩ := ladder_knot_kernel_1 (d := 1) le_rfl hq
    (fun s t => (μ s t).map lineEmbL) (isSymmetricFamily_lineEmb hsym) (isCovariantAt_lineEmb hcov)
    _ _ hDρ (isSymData_lineEmb_of_folded hP1)
  refine ⟨fun ω => ?_, ?_, ?_, ?_⟩
  · have h1 := (hlim (lineEmb ω)).1
    simp only [hstep, ladderProd_lineEmb, lineEmb_apply_zero, charFun_map_lineEmb] at h1
    exact h1
  · refine toData_A_eq_zero ?_
    rw [hA]
    change (q ^ 2 - 1)⁻¹ • ((0 : ℝ) • (1 : Mat 1)) = 0
    simp
  · have h1 : symLift P1.ν = symLift (knotLevyMeasure q ϖ) := by
      rw [← ladderNuStar_symLift]
      exact hν
    exact eq_of_symLift_eq P1.ν_folded (knotLevyMeasure_folded (by linarith) hϖ.2.1) h1
  · rw [← lintegral_posLog_symLift]
    exact hmom

/-- **The converse**: a mask with the moment has an exact grid pyramid
(`prop:ladder-knot-kernel`(2) at `d = 1`, read back on the line). -/
theorem exact_of_moment {q : ℝ} (hq : 1 < q) {w ϖ : Measure ℝ} [IsProbabilityMeasure w]
    (hne : w ≠ Measure.dirac 0) (hϖ : IsMaskLevyMeasure w ϖ)
    (hmom : ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ < ⊤) : IsExactGridPyramid q w := by
  haveI := isProbabilityMeasure_map_lineEmb w
  obtain ⟨μ1, hlad, -⟩ := ladder_knot_kernel_2 (d := 1) le_rfl hq (w.map lineEmbL)
    (map_lineEmb_ne_dirac hne) _ (isSymData_lineEmb_of_folded hϖ.isFoldedData)
    (by rw [lintegral_posLog_toData_mask]; exact hmom)
  obtain ⟨Φ, S, hc⟩ := carries_of_hasLadder hq hlad
  exact ⟨Φ, S, _, hc⟩

/-! ## `prop:grid-pyramids-infinitely-divisible`(1) -/

/-- **`prop:grid-pyramids-infinitely-divisible`(1), the lattice carrier.** A mask is infinitely
divisible iff it is compound Poisson with a finite folded Lévy measure `ϖ_w ≠ 0` carried by
`hℤ_{>0}`; then `ŵ > 0` and the support of `w` is unbounded; so a mask of bounded support is not
infinitely divisible. -/
theorem grid_pyramids_id_1 {h : ℝ} (hh : 0 < h) (w : Measure ℝ) (hw : IsGridMask h w) :
    (IsInfinitelyDivisible w ↔ ∃ ϖ : Measure ℝ, IsMaskLevyMeasure w ϖ ∧ ϖ ≠ 0 ∧
        ϖ {v : ℝ | ¬∃ n : ℤ, 0 < n ∧ v = h * n} = 0) ∧
      (IsInfinitelyDivisible w → (∀ ω : ℝ, 0 < charFun w ω) ∧ ∀ R : ℝ, w {x : ℝ | R < |x|} ≠ 0) ∧
      ((∃ R : ℝ, w {x : ℝ | R < |x|} = 0) → ¬ IsInfinitelyDivisible w) := by
  haveI := hw.1
  have hbdd := fun hb => not_infinitelyDivisible_of_bounded hw hb
  refine ⟨⟨exists_maskLevyMeasure hh hw, fun ⟨_, hϖ, _, _⟩ => hϖ.isInfinitelyDivisible⟩,
    fun hid => ⟨fun ω => ?_, fun R hR => hbdd ⟨R, hR⟩ hid⟩, hbdd⟩
  obtain ⟨ϖ, hϖ, -⟩ := exists_maskLevyMeasure hh hw hid
  exact hϖ.charFun_pos ω

/-! ## `prop:grid-pyramids-infinitely-divisible`(2) -/

/-- **`prop:grid-pyramids-infinitely-divisible`(2), the criterion.** The grid pyramid is exact iff
`w` is infinitely divisible with `∫ log₊ v ϖ_w(dv) < ∞`, iff `w` is infinitely divisible with
`∫ log₊ |x| w(dx) < ∞`. -/
theorem grid_pyramids_id_2 {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : Measure ℝ)
    (hw : IsGridMask h w) :
    (IsExactGridPyramid q w ↔ IsInfinitelyDivisible w ∧
        ∃ ϖ : Measure ℝ, IsMaskLevyMeasure w ϖ ∧ ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ < ⊤) ∧
      (IsExactGridPyramid q w ↔ IsInfinitelyDivisible w ∧
        ∫⁻ x, ENNReal.ofReal (Real.posLog |x|) ∂w < ⊤) := by
  haveI := hw.1
  haveI := isProbabilityMeasure_map_lineEmb w
  have h1 : IsExactGridPyramid q w ↔ IsInfinitelyDivisible w ∧
      ∃ ϖ : Measure ℝ, IsMaskLevyMeasure w ϖ ∧ ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ < ⊤ := by
    constructor
    · rintro ⟨Φ, S, μ, hc⟩
      obtain ⟨hsym, -, hstep⟩ := hc.family
      have hid : IsInfinitelyDivisible w := by
        rw [← hstep]
        exact isLawHemigroup_line_infinitelyDivisible hsym.1 zero_le_one hq.le
      obtain ⟨ϖ, hϖ, -⟩ := exists_maskLevyMeasure hh hw hid
      obtain ⟨P, hP⟩ := exists_folded hsym
      exact ⟨hid, ϖ, hϖ, (carries_knot hq hϖ hc (hP 1 zero_le_one)).2.2.2⟩
    · rintro ⟨-, ϖ, hϖ, hmom⟩
      exact exact_of_moment hq hw.2.2.1 hϖ hmom
  refine ⟨h1, h1.trans ⟨fun ⟨hid, ϖ, hϖ, hmom⟩ => ⟨hid, ?_⟩, fun ⟨hid, hmw⟩ => ⟨hid, ?_⟩⟩⟩
  · have hm := (ladder_knot_kernel_2_moments (d := 1) (w.map lineEmbL)
      (isInfinitelyDivisible_map_lineEmb hid) _ (isSymData_lineEmb_of_folded hϖ.isFoldedData)).1
      (by rw [lintegral_posLog_toData_mask]; exact hmom)
    rwa [lintegral_posLog_map_lineEmb] at hm
  · obtain ⟨ϖ, hϖ, -⟩ := exists_maskLevyMeasure hh hw hid
    have hm := (ladder_knot_kernel_2_moments (d := 1) (w.map lineEmbL)
      (isInfinitelyDivisible_map_lineEmb hid) _ (isSymData_lineEmb_of_folded hϖ.isFoldedData)).2
      (by rw [lintegral_posLog_map_lineEmb]; exact hmw)
    rw [lintegral_posLog_toData_mask] at hm
    exact ⟨ϖ, hϖ, hm⟩

/-- **`prop:grid-pyramids-infinitely-divisible`(2), the knot kernel.** Every family carrying the
ladder has `a(1) = 0`, `ϖ_1 = ∑_{m ≥ 1} T_{q^{-m}} ϖ_w`, and `μ̂_{0,1}(ω)` is the limit of the
partial products `∏_{m ≤ M} ŵ(q^{-m}ω)`, the transforms of `T_{q^{-1}}w * ⋯ * T_{q^{-M}}w`. -/
theorem grid_pyramids_id_2_knot {q h : ℝ} (hq : 1 < q) (w : Measure ℝ)
    (hw : IsGridMask h w) (ϖ : Measure ℝ) (hϖ : IsMaskLevyMeasure w ϖ)
    (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ) (μ : ℝ → ℝ → Measure ℝ)
    (hcarry : CarriesGridLadder q w Φ S μ) (P1 : SymLevyPair) (hP1 : IsFoldedData (μ 0 1) P1) :
    P1.a = 0 ∧ P1.ν = knotLevyMeasure q ϖ ∧
      ∀ ω : ℝ, Tendsto (fun M => ladderPartialProduct q w M ω) atTop (𝓝 (charFun (μ 0 1) ω)) ∧
        Tendsto (fun M => charFun (ladderPartialConv q w M) ω) atTop (𝓝 (charFun (μ 0 1) ω)) := by
  haveI := hw.1
  obtain ⟨hlim, ha, hν, -⟩ := carries_knot hq hϖ hcarry hP1
  refine ⟨ha, hν, fun ω => ⟨hlim ω, ?_⟩⟩
  simp_rw [(charFun_ladderPartialConv q w _).2 ω]
  exact hlim ω

/-- **`prop:grid-pyramids-infinitely-divisible`(2), the carrier of `ϖ_1`.** For an infinitely
divisible mask, `ϖ_1` is carried by the union of the `q^{-m}hℤ_{>0}`, `m ≥ 1`, and by no lattice
`ξℤ`. -/
theorem grid_pyramids_id_2_carrier {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : Measure ℝ)
    (hw : IsGridMask h w) (ϖ : Measure ℝ) (hϖ : IsMaskLevyMeasure w ϖ) :
    knotLevyMeasure q ϖ {v : ℝ | ¬∃ (m : ℕ) (n : ℤ), 0 < n ∧ v = q ^ (-((m : ℤ) + 1)) * (h * n)}
        = 0 ∧
      ∀ ξ : ℝ, 0 < ξ → knotLevyMeasure q ϖ {v : ℝ | ¬∃ k : ℤ, v = ξ * k} ≠ 0 := by
  haveI := hw.1
  have hq0 : 0 < q := by linarith
  obtain ⟨ϖ', hϖ', hne', hcarr'⟩ := exists_maskLevyMeasure hh hw hϖ.isInfinitelyDivisible
  rw [hϖ'.unique hϖ] at hne' hcarr'
  refine ⟨?_, fun ξ hξ => ?_⟩
  · have hTm : MeasurableSet
        {v : ℝ | ¬∃ (m : ℕ) (n : ℤ), 0 < n ∧ v = q ^ (-((m : ℤ) + 1)) * (h * n)} := by
      have hc : ({v : ℝ | ¬∃ (m : ℕ) (n : ℤ), 0 < n ∧
          v = q ^ (-((m : ℤ) + 1)) * (h * n)})ᶜ.Countable :=
        (Set.countable_range fun p : ℕ × ℤ => q ^ (-((p.1 : ℤ) + 1)) * (h * p.2)).mono
          fun v hv => by
            simp only [mem_compl_iff, mem_setOf_eq, not_not] at hv
            obtain ⟨m, n, -, rfl⟩ := hv
            exact ⟨(m, n), rfl⟩
      simpa using hc.measurableSet.compl
    rw [knotLevyMeasure, Measure.sum_apply _ hTm, ENNReal.tsum_eq_zero]
    intro m
    rw [Measure.map_apply (measurable_const_mul _) hTm]
    refine measure_mono_null (fun v hv => ?_) hcarr'
    simp only [mem_preimage, mem_setOf_eq] at hv ⊢
    rintro ⟨n, hn, rfl⟩
    exact hv ⟨m, n, hn, rfl⟩
  · -- an atom `v₀ = hn₀` of `ϖ`
    have hatom : ∃ n : ℤ, 0 < n ∧ ϖ {h * n} ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne'
      refine Measure.measure_univ_eq_zero.1 (measure_mono_null
        (t := {v : ℝ | ¬∃ n : ℤ, 0 < n ∧ v = h * n} ∪ ⋃ n : ℤ, ({h * n} : Set ℝ))
        (fun v _ => ?_) (measure_union_null hcarr' (measure_iUnion_null fun n => ?_)))
      · by_cases hv : ∃ n : ℤ, 0 < n ∧ v = h * n
        · obtain ⟨n, -, rfl⟩ := hv
          exact Or.inr (mem_iUnion.2 ⟨n, rfl⟩)
        · exact Or.inl hv
      · by_cases hn : 0 < n
        · exact hcon n hn
        · refine measure_mono_null (fun v hv => ?_) hcarr'
          rw [mem_singleton_iff] at hv
          subst hv
          rintro ⟨n', hn', he⟩
          have he' : (n : ℝ) = n' := mul_left_cancel₀ hh.ne' he
          have : n = n' := by exact_mod_cast he'
          exact hn (this ▸ hn')
    obtain ⟨n0, hn0, hat⟩ := hatom
    have hv0 : 0 < h * n0 := mul_pos hh (by exact_mod_cast hn0)
    have htend : Tendsto (fun m : ℕ => q ^ (-((m : ℤ) + 1)) * (h * n0)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => q ^ (-((m : ℤ) + 1))) atTop (𝓝 0) := by
        have e : (fun m : ℕ => q ^ (-((m : ℤ) + 1))) = fun m : ℕ => (q ^ (m + 1))⁻¹ := by
          funext m
          rw [zpow_neg]
          norm_cast
        rw [e]
        exact tendsto_inv_atTop_zero.comp
          ((tendsto_pow_atTop_atTop_of_one_lt hq).comp (tendsto_add_atTop_nat 1))
      simpa using h1.mul_const (h * n0)
    obtain ⟨m, hm⟩ := (htend.eventually (gt_mem_nhds hξ)).exists
    have hv1 : 0 < q ^ (-((m : ℤ) + 1)) * (h * n0) := mul_pos (zpow_pos hq0 _) hv0
    have hnot : q ^ (-((m : ℤ) + 1)) * (h * n0) ∈ {v : ℝ | ¬∃ k : ℤ, v = ξ * k} := by
      rintro ⟨k, hk⟩
      have h1 : 0 < (k : ℝ) := by
        by_contra hc
        push Not at hc
        have := mul_nonpos_of_nonneg_of_nonpos hξ.le hc
        linarith
      have h2 : (k : ℝ) < 1 := by
        by_contra hc
        push Not at hc
        have : ξ ≤ ξ * k := le_mul_of_one_le_right hξ.le hc
        linarith
      have h1' : 0 < k := by exact_mod_cast h1
      have h2' : k < 1 := by exact_mod_cast h2
      omega
    have h3 : ϖ {h * n0} ≤ knotLevyMeasure q ϖ {q ^ (-((m : ℤ) + 1)) * (h * n0)} := by
      calc ϖ {h * n0}
          ≤ ϖ ((fun v => q ^ (-((m : ℤ) + 1)) * v) ⁻¹' {q ^ (-((m : ℤ) + 1)) * (h * n0)}) :=
            measure_mono fun v hv => by
              rw [mem_singleton_iff] at hv
              rw [hv]
              rfl
        _ = (ϖ.map fun v => q ^ (-((m : ℤ) + 1)) * v) {q ^ (-((m : ℤ) + 1)) * (h * n0)} :=
            (Measure.map_apply (measurable_const_mul _) (measurableSet_singleton _)).symm
        _ ≤ knotLevyMeasure q ϖ {q ^ (-((m : ℤ) + 1)) * (h * n0)} := by
            rw [knotLevyMeasure]
            exact Measure.le_iff'.1 (Measure.le_sum (fun m : ℕ => ϖ.map fun v =>
              q ^ (-((m : ℤ) + 1)) * v) m) _
    intro hzero
    exact hat (nonpos_iff_eq_zero.1
      (h3.trans (measure_mono_null (singleton_subset_iff.2 hnot) hzero).le))

/-- **`prop:grid-pyramids-infinitely-divisible`(2), without the moment.** The partial products
have no limit that is a characteristic function, tend to `0` at almost every `ω`, and there is
no kernel. -/
theorem grid_pyramids_id_2_no_kernel {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : Measure ℝ)
    (hw : IsGridMask h w) (ϖ : Measure ℝ)
    (hϖ : IsMaskLevyMeasure w ϖ) (hinf : ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ = ⊤) :
    (¬ ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ ω : ℝ,
        Tendsto (fun M => ladderPartialProduct q w M ω) atTop (𝓝 (charFun ν ω))) ∧
      (∀ᵐ ω ∂volume, Tendsto (fun M => ladderPartialProduct q w M ω) atTop (𝓝 0)) ∧
      ¬ IsExactGridPyramid q w := by
  haveI := hw.1
  haveI := isProbabilityMeasure_map_lineEmb w
  obtain ⟨hno, hae⟩ := ladder_knot_kernel_3 (d := 1) hq (w.map lineEmbL) _
    (isSymData_lineEmb_of_folded hϖ.isFoldedData)
    (by rw [lintegral_posLog_toData_mask]; exact hinf)
  refine ⟨fun ⟨ν, hν, hlim⟩ => ?_, ?_, fun hex => ?_⟩
  · haveI := hν
    refine hno ⟨ν.map lineEmbL, isProbabilityMeasure_map_lineEmb ν, fun z => ?_⟩
    rw [charFun_map_lineEmb]
    simp_rw [ladderProd_lineEmb]
    exact hlim (z 0)
  · filter_upwards [ae_lineEmb hae] with x hx
    simpa [ladderProd_lineEmb, lineEmb_apply_zero] using hx
  · obtain ⟨-, ϖ', hϖ', hmom⟩ := (grid_pyramids_id_2 hq hh w hw).1.1 hex
    rw [hϖ'.unique hϖ] at hmom
    exact hmom.ne hinf

/-- The set `{x : x ∉ hℤ}` is measurable. -/
theorem measurableSet_not_mulInt (h : ℝ) : MeasurableSet {x : ℝ | ¬∃ n : ℤ, x = h * n} := by
  have hc : ({x : ℝ | ¬∃ n : ℤ, x = h * n})ᶜ.Countable :=
    (Set.countable_range fun n : ℤ => h * n).mono fun v hv => by
      simp only [mem_compl_iff, mem_setOf_eq, not_not] at hv
      obtain ⟨n, rfl⟩ := hv
      exact ⟨n, rfl⟩
  simpa using hc.measurableSet.compl

/-- **`prop:grid-pyramids-infinitely-divisible`(2), "not at every `ω ≠ 0`".** On every grid `hℤ`
there is an infinitely divisible mask without the logarithmic moment whose partial products at
`q = 2` do not tend to `0` at some `ω ≠ 0`. -/
theorem grid_pyramids_id_2_not_every {h : ℝ} (hh : 0 < h) :
    ∃ w : Measure ℝ, IsGridMask h w ∧ IsInfinitelyDivisible w ∧
      (∃ ϖ : Measure ℝ, IsMaskLevyMeasure w ϖ ∧ ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ = ⊤) ∧
      ∃ ω : ℝ, ω ≠ 0 ∧ ¬ Tendsto (fun M => ladderPartialProduct 2 w M ω) atTop (𝓝 0) := by
  obtain ⟨hfold, hmom, ⟨ρ, hρp, hρ⟩, hall⟩ := ladder_not_every_frequency
  haveI := hρp
  obtain ⟨hρZ, -, L, hL, hlim⟩ := hall ρ hρp hρ
  -- the folded measure `ϖ₀ = ∑ⱼ j⁻² δ_{2ʲ}` and its dilate by `h`
  set ϖ0 : Measure ℝ := Measure.sum fun j : ℕ => ENNReal.ofReal (((j : ℝ) + 1) ^ 2)⁻¹ •
    Measure.dirac ((2 : ℝ) ^ (j + 1)) with hϖ0
  haveI hfin0 : IsFiniteMeasure ϖ0 := by
    rw [← hfold]
    infer_instance
  have hfold0 : ϖ0 (Iic 0) = 0 := by
    rw [← hfold, Measure.restrict_apply measurableSet_Iic, Set.Iic_inter_Ioi, Ioc_self,
      measure_empty]
  set ϖ : Measure ℝ := ϖ0.map fun v => h * v with hϖ
  haveI : IsProbabilityMeasure (ρ.map lineProjL) :=
    Measure.isProbabilityMeasure_map lineProjL.continuous.aemeasurable
  set w : Measure ℝ := (ρ.map lineProjL).map fun x => h * x with hwdef
  haveI : IsProbabilityMeasure w :=
    Measure.isProbabilityMeasure_map (measurable_const_mul h).aemeasurable
  -- `ϖ` is the folded Lévy measure of `w`
  have hint : ∀ ω : ℝ, ∫ v, (1 - Real.cos (ω * v)) ∂ϖ =
      ∑' j : ℕ, notEveryW j * (1 - Real.cos (2 ^ (j + 1) * (h * ω))) := by
    intro ω
    rw [hϖ, integral_map (measurable_const_mul h).aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
    have hi : Integrable (fun v => 1 - Real.cos (ω * (h * v))) ϖ0 :=
      Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 2 (ae_of_all _ fun v => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [Real.cos_le_one (ω * (h * v)),
          Real.neg_one_le_cos (ω * (h * v))])
    rw [hϖ0] at hi ⊢
    rw [integral_sum_measure hi]
    refine tsum_congr fun j => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
      notEveryW, show ω * (h * 2 ^ (j + 1)) = 2 ^ (j + 1) * (h * ω) by ring]
  have hchar : ∀ ω : ℝ, charFun w ω =
      ((Real.exp (-∑' j : ℕ, notEveryW j * (1 - Real.cos (2 ^ (j + 1) * (h * ω)))) : ℝ) : ℂ) := by
    intro ω
    rw [hwdef, charFun_map_mul, charFun_map_lineProj, hρ, integral_one_sub_cos_notEveryNu,
      lineEmb_apply_zero]
  have hfoldϖ : ScaleSpace.IsFolded ϖ := by
    rw [ScaleSpace.IsFolded, hϖ, Measure.map_apply (measurable_const_mul h) measurableSet_Iic]
    refine measure_mono_null (fun v hv => ?_) hfold0
    simp only [mem_preimage, mem_Iic] at hv ⊢
    by_contra hc
    push Not at hc
    linarith [mul_pos hh hc]
  have hmask : IsMaskLevyMeasure w ϖ :=
    ⟨inferInstance, hfoldϖ, fun ω => by rw [hchar, hint]⟩
  -- the moment is infinite
  have hmom0 : ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ0 = ⊤ := by
    rw [← hfold, ← lintegral_indicator measurableSet_Ioi,
      lintegral_map ((by fun_prop : Measurable fun v : ℝ =>
        ENNReal.ofReal (Real.posLog v)).indicator measurableSet_Ioi) (by fun_prop)]
    rw [← hmom]
    refine lintegral_congr fun x => ?_
    have hn : ‖x‖ = |x 0| := by rw [← lineEmb_proj x, norm_lineEmb, lineEmb_apply_zero]
    rw [hn]
    by_cases hx : |x 0| ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx]
    · have h0 : |x 0| = 0 := le_antisymm (not_lt.1 hx) (abs_nonneg _)
      rw [indicator_of_notMem hx, h0, Real.posLog_zero, ENNReal.ofReal_zero]
  have hmomϖ : ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ = ⊤ := by
    rw [hϖ, lintegral_map (by fun_prop) (measurable_const_mul h)]
    by_contra hfin
    refine (ne_top_of_le_ne_top (b := ∫⁻ v, ENNReal.ofReal (Real.posLog (h * v)) ∂ϖ0 +
      ENNReal.ofReal (Real.posLog h⁻¹) * ϖ0 univ) ?_ ?_) hmom0
    · exact ENNReal.add_ne_top.2 ⟨hfin, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top _ _)⟩
    · calc ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ0
          ≤ ∫⁻ v, (ENNReal.ofReal (Real.posLog (h * v)) + ENNReal.ofReal (Real.posLog h⁻¹))
              ∂ϖ0 := lintegral_mono fun v => by
            rw [← ENNReal.ofReal_add Real.posLog_nonneg Real.posLog_nonneg]
            refine ENNReal.ofReal_le_ofReal ?_
            calc Real.posLog v = Real.posLog (h⁻¹ * (h * v)) := by
                  rw [← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
              _ ≤ Real.posLog h⁻¹ + Real.posLog (h * v) := Real.posLog_mul
              _ = Real.posLog (h * v) + Real.posLog h⁻¹ := add_comm _ _
        _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const]
  -- `w` is a mask on `hℤ`
  have hϖne : ϖ ≠ 0 := fun h0 => by
    rw [h0, lintegral_zero_measure] at hmomϖ
    exact ENNReal.zero_ne_top hmomϖ
  have hgrid : IsGridMask h w := by
    refine ⟨inferInstance, hmask.isSymmetric, fun h0 => hϖne (hmask.eq_zero_iff.2 h0), ?_⟩
    rw [hwdef, Measure.map_apply (measurable_const_mul h) (measurableSet_not_mulInt h),
      Measure.map_apply lineProjL.continuous.measurable
        ((measurable_const_mul h) (measurableSet_not_mulInt h))]
    refine measure_mono_null (fun y hy => ?_) hρZ
    simp only [mem_preimage, mem_setOf_eq, lineProjL_apply] at hy ⊢
    rintro ⟨k, hk⟩
    exact hy ⟨k, by rw [hk]⟩
  refine ⟨w, hgrid, hmask.isInfinitelyDivisible, ⟨ϖ, hmask, hmomϖ⟩, 2 * Real.pi / h,
    div_ne_zero (by positivity) hh.ne', fun h0 => ?_⟩
  -- at `ω = 2π/h` the partial products are those of `ϱ` at `2π`
  have heq : ∀ M : ℕ, ladderPartialProduct 2 w M (2 * Real.pi / h) =
      ladderProd 2 ρ M ((2 * Real.pi) • ebasis (0 : Fin 1)) := by
    intro M
    unfold ladderPartialProduct ladderProd
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [hwdef, charFun_map_mul, charFun_map_lineProj, smul_smul, lineEmb]
    congr 2
    field_simp
  simp_rw [heq] at h0
  have h1 := tendsto_nhds_unique h0 hlim
  exact hL.ne' (by exact_mod_cast h1.symm)

/-- **`prop:grid-pyramids-infinitely-divisible`(2), the uniform coupling and non-uniqueness.**
Under the criterion, one family carrying the ladder has `a(t) = 0` and
`ϖ_t = ϖ_1 + (log_q t) ϖ_w` on `[1, q]`, and two families carrying it have different kernels. -/
theorem grid_pyramids_id_2_coupling {q h : ℝ} (hq : 1 < q) (w : Measure ℝ)
    (hw : IsGridMask h w) (ϖ : Measure ℝ)
    (hϖ : IsMaskLevyMeasure w ϖ) (hmom : ∫⁻ v, ENNReal.ofReal (Real.posLog v) ∂ϖ < ⊤) :
    (∃ (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ) (μ : ℝ → ℝ → Measure ℝ),
        CarriesGridLadder q w Φ S μ ∧ ∀ t ∈ Icc (1 : ℝ) q, ∃ Q : SymLevyPair, Q.a = 0 ∧
          Q.ν = knotLevyMeasure q ϖ + ENNReal.ofReal (Real.logb q t) • ϖ ∧
          IsFoldedData (μ 0 t) Q) ∧
      ∃ (Φ Φ' : ℝ → ℝ → (X →L[ℝ] X)) (S S' : ℝ → ℝ → ℝ) (μ μ' : ℝ → ℝ → Measure ℝ),
        CarriesGridLadder q w Φ S μ ∧ CarriesGridLadder q w Φ' S' μ' ∧
          ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ μ s t ≠ μ' s t := by
  haveI := hw.1
  haveI := isProbabilityMeasure_map_lineEmb w
  have hq0 : 0 < q := by linarith
  set Dρ := SymLevyPair_toData (maskPair ϖ hϖ.1 hϖ.2.1) with hDρ
  have hDρw : IsSymData (w.map lineEmbL) Dρ := isSymData_lineEmb_of_folded hϖ.isFoldedData
  have hmom1 : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤ := by
    rw [hDρ, lintegral_posLog_toData_mask]
    exact hmom
  have hne1 := map_lineEmb_ne_dirac hw.2.2.1
  refine ⟨?_, ?_⟩
  · -- the uniform coupling: `D_t = D* + (log_q t) D_ϱ` on `[1, q]`
    have hl := isCouplingWeight_logb hq
    set Dst := ladderStarData hq Dρ hmom1 with hDst
    set D := couplingData Dst Dρ SymLevyData.zero (Real.logb q) (Real.logb q) with hD
    have hsyn : IsSynthesisData q D := isSynthesisData_uniform hq Dρ hmom1
      (exists_exponent_ne_zero hne1 hDρw) hl fun s t hs hst _ => logb_strictMonoOn hq hs hst
    obtain ⟨⟨μ1, hμ1⟩, hfam⟩ := coupling_family hq hsyn (w.map lineEmbL)
      (charFun_uniform_step hq Dρ hmom1 hl hDρw)
    obtain ⟨hlad, h1, hst⟩ := hfam μ1 hμ1
    obtain ⟨Φ, S, hc⟩ := carries_of_hasLadder hq hlad
    refine ⟨Φ, S, _, hc, fun t ht => ?_⟩
    have ht0 : 0 ≤ t := zero_le_one.trans ht.1
    have hsym1 := hlad.1
    have hDt : IsSymData (μ1 0 t) (D t) := by
      intro ω
      rw [charFun_kernel_mul_gen hsym1.1 zero_le_one ht.1 ω, hst 1 t le_rfl ht.1 ht.2 ω, h1 ω,
        ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    obtain ⟨hsymμ, -, -⟩ := hc.family
    haveI := hsymμ.1.isProbability 0 t le_rfl ht0
    obtain ⟨Q, hQ⟩ := line_exponent_data_1_converse ((μ1 0 t).map lineProjL)
      (hsymμ.2.2 0 t le_rfl ht0) (isLawHemigroup_line_infinitelyDivisible hsymμ.1 le_rfl ht0)
    have hQ1 : IsSymData (μ1 0 t) (SymLevyPair_toData Q) := by
      have h2 := isSymData_lineEmb_of_folded hQ
      rwa [map_lineEmb_lineProj] at h2
    haveI := hsym1.1.isProbability 0 t le_rfl ht0
    obtain ⟨hA, hν⟩ := isSymData_unique hQ1 hDt
    refine ⟨Q, toData_A_eq_zero (hA.trans ?_), ?_, hQ⟩
    · simp [hD, couplingData, SymLevyData.addSmul, hDst, ladderStarData, hDρ, SymLevyPair_toData,
        maskPair, SymLevyData.zero]
    · have hk : knotLevyMeasure q ϖ (Iic 0) = 0 := knotLevyMeasure_folded hq0 hϖ.2.1
      have hw0 : ϖ (Iic 0) = 0 := hϖ.2.1
      refine eq_of_symLift_eq Q.ν_folded ?_ ?_
      · rw [ScaleSpace.IsFolded, Measure.add_apply, Measure.smul_apply, hk, hw0]
        simp
      · rw [symLift_add, symLift_smul, ← ladderNuStar_symLift]
        refine hν.trans ?_
        simp only [hD, couplingData, SymLevyData.addSmul, hDst, ladderStarData, SymLevyData.zero,
          smul_zero, add_zero]
        rfl
  · -- two families with the ladder
    obtain ⟨μ1, μ1', hlad, hlad', s, t, hs, hst, hne⟩ :=
      ladder_knot_kernel_2_not_unique hq (w.map lineEmbL) hne1 Dρ hDρw hmom1
    obtain ⟨Φ, S, hc⟩ := carries_of_hasLadder hq hlad
    obtain ⟨Φ', S', hc'⟩ := carries_of_hasLadder hq hlad'
    refine ⟨Φ, Φ', S, S', _, _, hc, hc', s, t, hs, hst, fun heq => hne ?_⟩
    have h2 := congrArg (fun m : Measure ℝ => m.map lineEmbL) heq
    simpa only [map_lineEmb_lineProj] using h2

/-! ## `prop:grid-pyramids-infinitely-divisible`(3) -/

/-- **`prop:grid-pyramids-infinitely-divisible`(3), "more generally".** A law `ϱ ≠ δ₀` carried by
a lattice `ξℤ` is a step of no fully covariant family. -/
theorem grid_pyramids_id_3_general (ϱ : Measure ℝ) (hne : ϱ ≠ Measure.dirac 0) {ξ : ℝ}
    (hξ : 0 < ξ) (hlat : ϱ {x : ℝ | ¬∃ k : ℤ, x = ξ * k} = 0) (Fam : CascadeFamily)
    (μ : ℝ → ℝ → Measure ℝ) (hμ : IsKernelFamily Fam.Φ μ) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t ≠ ϱ := by
  intro s t hs hst heq
  haveI := discreteTopology_lineLattice hξ.ne'
  haveI : IsZLattice ℝ (lineLattice ξ) := ⟨span_lineLattice hξ.ne'⟩
  refine ladder_knot_kernel_4a (d := 1) le_rfl (ϱ.map lineEmbL) (map_lineEmb_ne_dirac hne)
    (lineLattice ξ) ?_ _ (isSymmetricFamily_lineEmb (line_axioms_kernels_1_family
      Fam.toCascadeCore μ hμ)) (isFullyCovariantLaws_lineEmb Fam hμ) s t hs hst
    (congrArg (Measure.map lineEmbL) heq)
  rw [map_lineEmb_lineLattice_compl]
  exact hlat

/-- **`prop:grid-pyramids-infinitely-divisible`(3).** No grid pyramid is exact in the third
stratum, and no family carrying one is fully covariant. -/
theorem grid_pyramids_id_3 {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : Measure ℝ)
    (hw : IsGridMask h w) :
    ¬ IsExactGridPyramidThird q w ∧
      ∀ (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ) (μ : ℝ → ℝ → Measure ℝ),
        CarriesGridLadder q w Φ S μ → ¬ ∃ S' : ℝ → ℝ → ℝ, IsScaleCovariant Φ (Ioi 0) S' := by
  obtain ⟨-, -, hne, hcarr⟩ := hw
  have key : ∀ (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ) (μ : ℝ → ℝ → Measure ℝ),
      CarriesGridLadder q w Φ S μ → ∀ Fam : CascadeFamily, Fam.Φ = Φ → False := by
    intro Φ S μ hc Fam hFam
    obtain ⟨-, -, hstep⟩ := hc.family
    have hμ : IsKernelFamily Fam.Φ μ := hFam ▸ hc.2.2.1
    exact grid_pyramids_id_3_general w hne hh hcarr Fam μ hμ 1 q zero_le_one hq.le hstep
  refine ⟨fun ⟨Φ, S, μ, hc, Fam, hFam⟩ => key Φ S μ hc Fam hFam, fun Φ S μ hc ⟨S', hS'⟩ => ?_⟩
  obtain ⟨C, rfl⟩ := hc.1.core
  exact key _ S μ hc ⟨C, S', hS'⟩ rfl

/-! ## `prop:grid-pyramids-infinitely-divisible`(4), masks of bounded support -/

/-- **`prop:grid-pyramids-infinitely-divisible`(4), masks of bounded support** (the B-spline masks
of odd length among them) have no exact grid pyramid. -/
theorem grid_pyramids_id_4_bounded {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : Measure ℝ)
    (hw : IsGridMask h w) (hbdd : ∃ R : ℝ, w {x : ℝ | R < |x|} = 0) :
    ¬ IsExactGridPyramid q w := fun hex =>
  not_infinitelyDivisible_of_bounded hw hbdd ((grid_pyramids_id_2 hq hh w hw).1.1 hex).1

end Pyramids
