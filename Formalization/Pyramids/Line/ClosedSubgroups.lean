/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.LineAxiomsKernels
import Mathlib.Topology.Instances.ZMultiples

/-!
# `lem:closed-subgroups`: the closed subgroups of `(0,∞)`

Blueprint: `blueprint/src/parts/02-line.tex`, `lem:closed-subgroups`. Wave 2e: the two
declarations moved here from `PyramidsSkeleton.Ch02Line`, their statements unchanged.

## The route

The printed one.

* **The classification.** A closed subgroup is one of the three: `isClosedPosSubgroup_cases`
  (`lem:family-dilations`), which reads the logarithms as a closed subgroup of `ℝ`, dense or
  cyclic. Conversely `{1}` and `(0,∞)` are closed subgroups, and so is `q^ℤ`: its logarithms are
  the multiples of `log q`, a discrete, hence closed, subgroup of `ℝ`, and the logarithm is
  continuous on `(0,∞)`.
* **The closure.** The kernels of the family are a symmetric family in dimension `1`
  (`lem:line-axioms-kernels`(1)), and (A8) at `λ` is `λ`-covariance of the kernels
  (`lem:line-axioms-kernels`(3)). So `Λ` lies in the set `G` of `lem:family-dilations`(2), a closed
  subgroup of `(0,∞)` (`KernelOrder.isClosedPosSubgroup`), which therefore contains the closed
  subgroup `Λ` generates; at each of its elements a bijection is chosen and (3) turns covariance
  back into (A8).
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set
open ScaleSpace (CascadeCore IsScaleCovariant IsKernelFamily)

/-- **`q^ℤ` is a closed subgroup of `(0,∞)`** for `q > 1`. -/
theorem qPowers_isClosedPosSubgroup {q : ℝ} (hq : 1 < q) : IsClosedPosSubgroup (qPowers q) := by
  have hq0 : 0 < q := by linarith
  refine ⟨?_, ⟨0, zpow_zero q⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact zpow_pos hq0 n
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact ⟨m + n, zpow_add₀ hq0.ne' m n⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨-n, zpow_neg q n⟩
  · -- the preimage is the preimage of the multiples of `log q` under the logarithm
    have hcl : IsClosed ((AddSubgroup.zmultiples (Real.log q) : AddSubgroup ℝ) : Set ℝ) :=
      AddSubgroup.isClosed_of_discrete
    have hlog : Continuous fun x : Ioi (0 : ℝ) => Real.log (x : ℝ) :=
      Real.continuousOn_log.comp_continuous continuous_subtype_val fun x => (ne_of_gt x.2)
    have he : ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' qPowers q) =
        (fun x : Ioi (0 : ℝ) => Real.log (x : ℝ)) ⁻¹'
          ((AddSubgroup.zmultiples (Real.log q) : AddSubgroup ℝ) : Set ℝ) := by
      ext x
      simp only [mem_preimage, SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, by rw [← hn, Real.log_zpow]⟩
      · rintro ⟨n, hn⟩
        refine ⟨n, ?_⟩
        change q ^ n = (x : ℝ)
        have hx : (0 : ℝ) < x := x.2
        rw [← Real.exp_log (zpow_pos hq0 n), ← Real.exp_log hx, Real.log_zpow, hn]
    rw [he]
    exact hcl.preimage hlog

/-- **`lem:closed-subgroups`, the classification.** The closed subgroups of `((0,∞), ×)` are
`{1}`, the `q^ℤ` with `q > 1`, and `(0,∞)`. -/
theorem closed_subgroups_1 (H : Set ℝ) :
    IsClosedPosSubgroup H ↔ H = {1} ∨ (∃ q : ℝ, 1 < q ∧ H = qPowers q) ∨ H = Ioi 0 := by
  refine ⟨isClosedPosSubgroup_cases, ?_⟩
  rintro (rfl | ⟨q, hq, rfl⟩ | rfl)
  · refine ⟨fun x hx => ?_, rfl, fun x hx y hy => ?_, fun x hx => ?_, ?_⟩
    · rw [mem_singleton_iff.1 hx]
      exact (one_pos : (0 : ℝ) < 1)
    · rw [mem_singleton_iff.1 hx, mem_singleton_iff.1 hy, one_mul]
      rfl
    · rw [mem_singleton_iff.1 hx, inv_one]
      rfl
    · exact isClosed_eq continuous_subtype_val continuous_const
  · exact qPowers_isClosedPosSubgroup hq
  · refine ⟨subset_rfl, mem_Ioi.2 one_pos,
      fun x hx y hy => mem_Ioi.2 (mul_pos (mem_Ioi.1 hx) (mem_Ioi.1 hy)),
      fun x hx => mem_Ioi.2 (inv_pos.2 (mem_Ioi.1 hx)), ?_⟩
    have he : ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioi 0) = univ :=
      eq_univ_of_forall fun x => x.2
    rw [he]
    exact isClosed_univ

/-- **`lem:closed-subgroups`, the closure.** A family with (A1)–(A7), (ND) and (A8) at every
dilation of `Λ ⊆ (0,∞)` satisfies (A8) at every dilation of the closed subgroup `Λ` generates. -/
theorem closed_subgroups_2 (C : CascadeCore) (Λ : Set ℝ) (hΛ : Λ ⊆ Ioi 0) (S : ℝ → ℝ → ℝ)
    (hS : IsScaleCovariant C.Φ Λ S) :
    ∃ S' : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (closedPosSubgroupGen Λ) S' := by
  classical
  obtain ⟨μ, hμ, -⟩ := line_axioms_kernels_1_exists C.toPreCascadeCore C.positive
  have hK := kernelOrder_line (line_axioms_kernels_1_family C μ hμ)
  -- `Λ` lies in the group `G` of dilations at which the kernels are covariant
  have hsub : Λ ⊆ covariantDilations μ := by
    intro lam hlam
    have hpos : 0 < lam := hΛ hlam
    have hbij : IsIncreasingBijection (S lam) :=
      ⟨hS.S_mapsTo _ hpos hlam, hS.S_strictMonoOn _ hpos hlam, hS.S_surjOn _ hpos hlam⟩
    refine ⟨hpos, S lam, ?_⟩
    rw [isCovariantAt_iff_map_mul]
    exact ⟨hbij, (line_axioms_kernels_3 C.Φ μ hμ hpos (S lam) hbij).1 (hS.scale lam hpos hlam)⟩
  have hgen : closedPosSubgroupGen Λ ⊆ covariantDilations μ := fun x hx =>
    mem_sInter.1 hx _ ⟨hK.isClosedPosSubgroup, hsub⟩
  -- a bijection at each element of `G`
  set S' : ℝ → ℝ → ℝ := fun lam =>
    if h : lam ∈ covariantDilations μ then Classical.choose h.2 else id with hS'
  have hS'cov : ∀ lam (h : lam ∈ covariantDilations μ), IsCovariantAt μ lam (S' lam) := by
    intro lam h
    simp only [hS', dif_pos h]
    exact Classical.choose_spec h.2
  refine ⟨S', ⟨fun lam _ hlam => (hS'cov lam (hgen hlam)).1.mapsTo,
    fun lam _ hlam => (hS'cov lam (hgen hlam)).1.strictMonoOn,
    fun lam _ hlam => (hS'cov lam (hgen hlam)).1.surjOn, fun lam hpos hlam => ?_⟩⟩
  have hc := hS'cov lam (hgen hlam)
  rw [isCovariantAt_iff_map_mul] at hc
  exact (line_axioms_kernels_3 C.Φ μ hμ hpos (S' lam) hc.1).2 hc.2

end Pyramids
