/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Pyramid
import AffineHemigroup.RadialMarginal

/-!
# `lem:reduction-keeps-stratum`: the marginal family has the same covariance

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `lem:reduction-keeps-stratum`. Phase 5, wave 1c.

The affine export's `lem:radial-marginal` (`radial_marginal`, `radial_marginal_eq_dirac`) gives,
for each law of an isotropic family, the radial form `μ̂(ω) = m̂(|ω|)`, the symmetry of the
marginal, and `m = δ₀ ⟺ μ = δ₀`; `charFun_marginal` reads (I2) of the marginals at `ω e`, and
`Measure.map_conv_continuousLinearMap` carries (I1). For the covariance, `⟨e, λx⟩ = λ⟨e, x⟩`
(`marginal_map_smul`) gives one direction; the radial form at `λω` and at `ω`, with the uniqueness
of the transform, gives the other.
-/

namespace Pyramids

open AffineHemigroup MeasureTheory Set

variable {d : ℕ}

/-- The marginal of a dilate is the dilate of the marginal. -/
theorem marginal_map_smul (e : Rd d) (ν : Measure (Rd d)) (lam : ℝ) :
    marginal e (ν.map fun x => lam • x) = (marginal e ν).map fun y => lam • y := by
  rw [marginal, marginal, Measure.map_map (continuous_inner_left e).measurable
    (measurable_const_smul lam), Measure.map_map (measurable_const_smul lam)
    (continuous_inner_left e).measurable]
  congr 1
  ext x
  simp [Function.comp, real_inner_smul_right]

/-- **`lem:reduction-keeps-stratum`.** For an isotropic family and a unit vector `e`, with
`m_{s,t} = π_* μ_{s,t}`: `μ̂_{s,t}(ω) = m̂_{s,t}(|ω|)`; the `m_{s,t}` form a symmetric family on
`ℝ`; and for every `λ > 0` and increasing bijection `S` of `[0,∞)`, `D_λ μ_{s,t} = μ_{Ss,St}` for
all `s ≤ t` iff `D_λ m_{s,t} = m_{Ss,St}` for all `s ≤ t`. -/
theorem reduction_keeps_stratum (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsIsotropicFamily μ) (e : Rd d) (he : ‖e‖ = 1) :
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ω : Rd d,
        charFun (μ s t) ω = charFun (marginal e (μ s t)) ‖ω‖) ∧
      IsSymmetricFamily (fun s t => marginal e (μ s t)) ∧
      ∀ lam : ℝ, 0 < lam → ∀ S : ℝ → ℝ, IsIncreasingBijection S →
        (IsCovariantAt μ lam S ↔ IsCovariantAt (fun s t => marginal e (μ s t)) lam S) := by
  obtain ⟨⟨hH, hND⟩, hrot⟩ := hμ
  have hP := hH.isProbability
  have hrad : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ω : Rd d,
      charFun (μ s t) ω = charFun (marginal e (μ s t)) ‖ω‖ := fun s t hs hst ω => by
    haveI := hP s t hs hst
    exact (radial_marginal hd e he (μ s t) (hrot s t hs hst)).2.2.1 ω
  refine ⟨hrad, ⟨⟨fun s t hs hst => ?_, fun t ht => ?_, fun r s t hr hrs hst => ?_,
    fun ω => ?_⟩, fun s t hs hst => ?_, fun s t hs hst => ?_⟩, fun lam hlam S hS => ?_⟩
  · haveI := hP s t hs hst
    infer_instance
  · rw [hH.diag t ht, marginal, Measure.map_dirac' (continuous_inner_left e).measurable]
    simp
  · change marginal e (μ r t) = marginal e (μ s t) ∗ marginal e (μ r s)
    haveI := hP s t (hr.trans hrs) hst
    haveI := hP r s hr hrs
    rw [hH.cascade r s t hr hrs hst]
    exact Measure.map_conv_continuousLinearMap (innerSL ℝ e)
  · simp only [charFun_marginal]
    exact (hH.continuous (ω • e))
  · haveI := hP s t hs hst.le
    rw [Ne, radial_marginal_eq_dirac hd e he (μ s t) (hrot s t hs hst.le)]
    exact hND s t hs hst
  · haveI := hP s t hs hst
    exact (radial_marginal hd e he (μ s t) (hrot s t hs hst)).2.1
  · have hS0 : ∀ s, 0 ≤ s → 0 ≤ S s := fun s hs => hS.mapsTo (mem_Ici.2 hs)
    have hSle : ∀ s t, 0 ≤ s → s ≤ t → S s ≤ S t := fun s t hs hst =>
      hS.strictMonoOn.monotoneOn (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst)) hst
    constructor
    · rintro ⟨-, hcov⟩
      refine ⟨hS, fun s t hs hst => ?_⟩
      simp only
      rw [← marginal_map_smul, hcov s t hs hst]
    · rintro ⟨-, hcov⟩
      refine ⟨hS, fun s t hs hst => ?_⟩
      haveI := hP s t hs hst
      haveI := hP (S s) (S t) (hS0 s hs) (hSle s t hs hst)
      have hm := hcov s t hs hst
      simp only at hm
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      rw [charFun_map_smul, hrad s t hs hst, hrad (S s) (S t) (hS0 s hs) (hSle s t hs hst),
        ← hm, charFun_map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, smul_eq_mul]

end Pyramids
