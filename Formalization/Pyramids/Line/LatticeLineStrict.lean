/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.LindebergStratumOne
import Pyramids.Line.DiscreteGaussianPyramid
import Pyramids.Pyramid.LatticeStrataStrict

/-!
# `cor:lattice-line-strict`: the three strata on the line are distinct

Blueprint: `blueprint/src/parts/02-line.tex`, `cor:lattice-line-strict`. Wave 3e: the declarations
moved here from `PyramidsSkeleton.Ch02Line`, their statements unchanged.

## The route

* **The implication.** A `CascadeFamily` is a `CascadeCore` with (A8) at every `λ > 0`; (A8) at
  `q^ℤ` is its restriction.
* **The lower strictness.** Lindeberg's family (`prop:lindeberg-stratum-one`(2)) has (A1)–(A7) and
  (ND), and (A8 at `q^ℤ`) for no `q > 1` (`prop:lindeberg-stratum-one`(3)).
* **The upper strictness.** The discrete-Gaussian pyramid is `q^ℤ`-covariant in the canonical
  gauge (`prop:discrete-gaussian-pyramid`(1)), and no relabelling, the identity among them, makes
  it fully covariant (`prop:discrete-gaussian-pyramid`(2)). The bundle takes `h = 1` for Lindeberg's
  family and the weights `w_i = 1` for `i < 0`, `0` otherwise, for the pyramid.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X CascadeCore IsScaleCovariant IsKernelFamily)

/-- (A8) at a set of ratios restricts to a smaller set. -/
theorem isScaleCovariant_mono_set {Φ : ℝ → ℝ → (X →L[ℝ] X)} {G G' : Set ℝ} {S : ℝ → ℝ → ℝ}
    (h : IsScaleCovariant Φ G S) (hG : G' ⊆ G) : IsScaleCovariant Φ G' S :=
  ⟨fun lam hlam hmem => h.S_mapsTo lam hlam (hG hmem),
    fun lam hlam hmem => h.S_strictMonoOn lam hlam (hG hmem),
    fun lam hlam hmem => h.S_surjOn lam hlam (hG hmem),
    fun lam hlam hmem => h.scale lam hlam (hG hmem)⟩

/-- The powers of `q > 0` are positive. -/
theorem qPowers_subset_Ioi {q : ℝ} (hq : 0 < q) : qPowers q ⊆ Ioi 0 := by
  rintro _ ⟨n, rfl⟩
  exact zpow_pos hq n

/-- **`cor:lattice-line-strict`, the implication.** Full covariance implies (A8 at `q^ℤ`). -/
theorem lattice_line_strict_imp {q : ℝ} (hq : 1 < q) (Φ : ℝ → ℝ → (X →L[ℝ] X))
    (hΦ : IsFullyCovariantLine Φ) : ∃ S : ℝ → ℝ → ℝ, IsQCovariantLine q Φ S := by
  obtain ⟨Fam, rfl⟩ := hΦ
  exact ⟨Fam.S, hq, ⟨Fam.toCascadeCore, rfl⟩,
    isScaleCovariant_mono_set Fam.covariant (qPowers_subset_Ioi (by linarith))⟩

/-- **`cor:lattice-line-strict`, the lower strictness, by its witness.** Lindeberg's discrete scale
space has (A1)–(A7) and (ND) and not (A8 at `q^ℤ`). -/
theorem lattice_line_strict_lower {q : ℝ} (hq : 1 < q) {h : ℝ} (hh : 0 < h) :
    ∃ C : CascadeCore, IsKernelFamily C.Φ (fun s t => lindebergKernel h (t - s)) ∧
      ¬ ∃ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (qPowers q) S := by
  obtain ⟨C, hC⟩ := lindeberg_stratum_one_2 hh
  exact ⟨C, hC, fun ⟨S, hS⟩ => (lindeberg_stratum_one_3 hh hq).2 C.Φ S hC hS⟩

/-- The identity is a gauge. -/
theorem isGauge_id' : IsGauge (fun t : ℝ => t) :=
  ⟨rfl, fun _ _ _ _ h => h, fun t ht => ⟨t, ht, rfl⟩⟩

/-- **`cor:lattice-line-strict`, the upper strictness, by its witness.** The discrete-Gaussian
pyramid is `q^ℤ`-covariant and not fully covariant. -/
theorem lattice_line_strict_upper {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : Antitone w) (hwne : ∃ i, w i ≠ 0)
    (hneg : Summable fun i : {i : ℤ // i < 0} => w i * q ^ (2 * (i : ℤ)))
    (hpos : Summable fun i : {i : ℤ // 0 ≤ i} => w i) :
    ∃ (μ : ℝ → ℝ → Measure ℝ) (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ),
      IsDGKernels q h w μ ∧ IsKernelFamily Φ μ ∧ IsQCovariantLine q Φ S ∧
        IsCanonicalDiscreteGauge q S ∧ ¬ ∃ S' : ℝ → ℝ → ℝ, IsScaleCovariant Φ (Ioi 0) S' := by
  obtain ⟨-, ⟨μ, hμ⟩, hall⟩ := discrete_gaussian_pyramid_1 hq hh w hw0 hwanti hwne hneg hpos
  obtain ⟨⟨Φ, S, hQ, hcan, hker⟩, -⟩ := hall μ hμ
  exact ⟨μ, Φ, S, hμ, hker, hQ, hcan,
    discrete_gaussian_pyramid_2 hq hh w hw0 hwanti hwne hneg hpos μ hμ Φ hker _ isGauge_id'⟩

/-- **`cor:lattice-line-strict`, both implications are strict.** Some family with (A1)–(A7) and
(ND) is not `q^ℤ`-covariant, and some `q^ℤ`-covariant family is not fully covariant. -/
theorem lattice_line_strict {q : ℝ} (hq : 1 < q) :
    (∃ C : CascadeCore, ¬ ∃ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (qPowers q) S) ∧
      ∃ (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ),
        IsQCovariantLine q Φ S ∧ ¬ IsFullyCovariantLine Φ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨C, -, hC⟩ := lattice_line_strict_lower hq one_pos
    exact ⟨C, hC⟩
  · have hw0 : ∀ i, 0 ≤ lowerStepWeights i := fun i => by
      unfold lowerStepWeights; split_ifs <;> norm_num
    have hanti : Antitone lowerStepWeights := fun i j hij => by
      unfold lowerStepWeights
      split_ifs with hj hi hi <;> first | omega | norm_num
    have hne : ∃ i, lowerStepWeights i ≠ 0 := ⟨-1, by simp [lowerStepWeights]⟩
    have hpos : Summable fun i : {i : ℤ // 0 ≤ i} => lowerStepWeights i := by
      refine (summable_zero : Summable fun _ : {i : ℤ // 0 ≤ i} => (0 : ℝ)).congr fun i => ?_
      simp [lowerStepWeights, not_lt.2 i.2]
    obtain ⟨-, Φ, S, -, -, hQ, -, hnot⟩ := lattice_line_strict_upper hq one_pos lowerStepWeights
      hw0 hanti hne (summable_lowerStepWeights hq) hpos
    exact ⟨Φ, S, hQ, fun ⟨Fam, hFam⟩ => hnot ⟨Fam.S, hFam ▸ Fam.covariant⟩⟩

end Pyramids
