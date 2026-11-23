/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.MaternLine

/-!
# `prop:creation-plane`(3): the frame Matérn pyramid exists

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:creation-plane`. Phase 5, wave 3b (on the
VM). `frame_matern_pyramid_exists` moved here from `PyramidsSkeleton.Ch04Matern`, its conclusion
unchanged; it no longer takes `1 ≤ d`, which its proof does not read (2026-11-15, a
strengthening).

The laws are the products `μ_{s,t} := ⊗_j ν_{s,t}` of a Matérn pyramid `ν` on the line
(`matern_pyramid_line_1`, `thm:matern-pyramid-line`), read on `ℝ^d` through `toLp`. Their
transforms are the products of the line's (`charFun_pi`), and the octave step's is
`∏_j (1 + c²t²ω_j²)⁻¹` by the telescoping `F_q(qr) = log(1 + c²r²) + F_q(r)`
(`maternExponent_mul_q`). The line's pyramid reads `levy_khintchine_converse`, inside the trust
boundary, through `thm:matern-pyramid-line`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory

variable {d : ℕ}

/-- **The frame Matérn laws**: `⊗_j ν_{s,t}` on `ℝ^d`. -/
noncomputable def frameLaws (d : ℕ) (ν : ℝ → ℝ → Measure ℝ) (s t : ℝ) : Measure (Rd d) :=
  (Measure.pi fun _ : Fin d => ν s t).map (WithLp.toLp 2)

theorem isFrameMaternPyramid_frameLaws {q c : ℝ} {ν : ℝ → ℝ → Measure ℝ}
    (hν : IsMaternPyramid q c ν) : IsFrameMaternPyramid q c (frameLaws d ν) := by
  intro s t hs hst
  haveI := (hν s t hs hst).1
  refine ⟨?_, fun ω => ?_⟩
  · unfold frameLaws
    rw [← MeasurableEquiv.coe_toLp]
    exact Measure.isProbabilityMeasure_map (MeasurableEquiv.toLp 2 _).measurable.aemeasurable
  · rw [frameLaws, charFun_pi]
    simp_rw [(hν s t hs hst).2, Real.norm_eq_abs]
    rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.sum_neg_distrib, Finset.sum_sub_distrib]

/-- **`prop:creation-plane`(3), the frame Matérn pyramid exists**: laws with the transforms
`∏_j exp(-(F_q(t|ω_j|) - F_q(s|ω_j|)))`, `0 ≤ s ≤ t`, whose octave step `μ_{t,qt}` has the
transform `∏_j (1 + c²t²ω_j²)⁻¹`. -/
theorem frame_matern_pyramid_exists {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    ∃ μ : ℝ → ℝ → Measure (Rd d), IsFrameMaternPyramid q c μ ∧
      ∀ t : ℝ, 0 < t → ∀ ω : Rd d,
        charFun (μ t (q * t)) ω = ((∏ j, (1 + c ^ 2 * t ^ 2 * ω j ^ 2)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨ν, hν⟩ := (matern_pyramid_line_1 hq hc).2.2.1
  have hμ := isFrameMaternPyramid_frameLaws (d := d) hν
  refine ⟨frameLaws d ν, hμ, fun t ht ω => ?_⟩
  rw [(hμ t (q * t) ht.le (by nlinarith)).2]
  congr 1
  have hj : ∀ j, maternExponent q c (q * t * |ω j|) - maternExponent q c (t * |ω j|) =
      Real.log (1 + c ^ 2 * t ^ 2 * ω j ^ 2) := by
    intro j
    rw [mul_assoc, maternExponent_mul_q hq hc, mul_pow, sq_abs]
    ring_nf
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_neg_distrib,
    Real.exp_sum, Finset.prod_congr rfl fun j _ => ?_]
  rw [Real.exp_neg, Real.exp_log (by positivity)]

end Pyramids
