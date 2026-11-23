/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Cited
import ScaleSpaceCore.StudentTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Ledger A51: the modified Bessel function `K_ν` (DLMF 10.32.10)

Interface node `thm:cited-A51` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A51 of
`blueprint/AXIOMS.md`, cited from the NIST Digital Library of Mathematical Functions, Version 1.2.8
(2026-09-15), equation 10.32.10. The author admitted A51 on 2026-11-13.

`K_ν` is the shared core's `ScaleSpace.besselK`, defined at real `z > 0` by DLMF 10.32.9,
`K_ν(z) = ∫₀^∞ e^{-z cosh u} cosh(νu) du` (transcribed against the definition in
`records/pyramids/VERBATIM-literature.md`, A51 addendum, MATCH).

**The node is proved here, and this file declares no axiom** (`cited_A51_integral`). The shared
core's `ScaleSpace.lintegral_Ioi_rpow_exp_besselKernel` is the substitution `u = c e^v` that turns
the integral of 10.32.10 into the cosh integral of 10.32.9, and `lintegral_cosh_exp_ne_top` below
shows that integral finite (a Gaussian bound), so the two Bochner integrals are the real values of
the two finite lower integrals. `#print axioms` gives Lean core.

The node's former clause (2), five further DLMF equations admitted on 2026-11-13 as the axiom
`cited_A51_evaluations`, was dropped the same day by the author's decision: no node and no proof
read it, `lem:bessel-k` deriving what it needs from the integral and the definition.
-/

namespace Pyramids

open MeasureTheory Set Filter
open ScaleSpace (besselK)
open scoped ENNReal Topology

/-- **The cosh integral of DLMF 10.32.9 is finite** at every real order `p` and every `z > 0`:
`cosh(pv) e^{-z cosh v} ≤ e^{2p²/z} e^{-(z/8)v²}` for `v ≥ 0`, from `cosh(pv) ≤ e^{|p|v}`,
`cosh v ≥ v²/4` and completing the square. -/
theorem lintegral_cosh_exp_ne_top (p : ℝ) {z : ℝ} (hz : 0 < z) :
    (∫⁻ v in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(z * Real.cosh v)))) ≠ ⊤ := by
  have hb : (0 : ℝ) < z / 8 := by positivity
  set C : ℝ := Real.exp (2 * p ^ 2 / z) with hC
  have hint : Integrable (fun v : ℝ => C * Real.exp (-(z / 8) * v ^ 2))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((integrable_exp_neg_mul_sq hb).const_mul C).restrict
  refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun v hv => ?_)
    hint.lintegral_lt_top)
  have hv0 : (0 : ℝ) ≤ v := le_of_lt hv
  refine ENNReal.ofReal_le_ofReal ?_
  -- `cosh (p v) ≤ exp (|p| v)`
  have h1 : Real.cosh (p * v) ≤ Real.exp (|p| * v) := by
    rw [Real.cosh_eq]
    have ha : p * v ≤ |p| * v := mul_le_mul_of_nonneg_right (le_abs_self p) hv0
    have hb' : -(p * v) ≤ |p| * v := by
      rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs p) hv0
    have := Real.exp_le_exp.mpr ha
    have := Real.exp_le_exp.mpr hb'
    linarith
  -- `cosh v ≥ v² / 4`
  have h2 : v ^ 2 / 4 ≤ Real.cosh v := by
    rw [Real.cosh_eq]
    have := Real.quadratic_le_exp_of_nonneg hv0
    have := Real.exp_pos (-v)
    nlinarith
  have h3 : Real.exp (-(z * Real.cosh v)) ≤ Real.exp (-(z * (v ^ 2 / 4))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  -- `|p| v - z v²/4 ≤ 2 p²/z - (z/8) v²`
  have h4 : |p| * v + -(z * (v ^ 2 / 4)) ≤ 2 * p ^ 2 / z + -(z / 8) * v ^ 2 := by
    have hsq : 0 ≤ (z / 4 * v - |p|) ^ 2 / (z / 2) := by positivity
    have hp2 : |p| ^ 2 = p ^ 2 := sq_abs p
    have key : 2 * p ^ 2 / z + -(z / 8) * v ^ 2 - (|p| * v + -(z * (v ^ 2 / 4)))
        = (z / 4 * v - |p|) ^ 2 / (z / 2) := by
      rw [← hp2]
      field_simp
      ring
    linarith
  calc Real.cosh (p * v) * Real.exp (-(z * Real.cosh v))
      ≤ Real.exp (|p| * v) * Real.exp (-(z * (v ^ 2 / 4))) :=
        mul_le_mul h1 h3 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (|p| * v + -(z * (v ^ 2 / 4))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2 * p ^ 2 / z + -(z / 8) * v ^ 2) := Real.exp_le_exp.mpr h4
    _ = C * Real.exp (-(z / 8) * v ^ 2) := by rw [Real.exp_add]

/-- **`thm:cited-A51`**, at real `z > 0` (DLMF 10.32.10):
`K_ν(z) = ½ (z/2)^ν ∫₀^∞ exp(-t - z²/(4t)) t^{-ν-1} dt`, every real `ν`. Proved from the definition
of `besselK` (DLMF 10.32.9) by the shared core's substitution, at `p = -ν`, `A = z²/4`, `B = 1`,
with `K_{-ν} = K_ν`. -/
theorem cited_A51_integral (ν : ℝ) {z : ℝ} (hz : 0 < z) :
    besselK ν z = 1 / 2 * (z / 2) ^ ν *
      ∫ t in Ioi (0 : ℝ), Real.exp (-t - z ^ 2 / (4 * t)) / t ^ (ν + 1) := by
  have hz2 : (0 : ℝ) < z / 2 := by positivity
  have hA : (0 : ℝ) < z ^ 2 / 4 := by positivity
  have hsqA : Real.sqrt (z ^ 2 / 4) = z / 2 := by
    rw [show z ^ 2 / 4 = (z / 2) ^ 2 by ring, Real.sqrt_sq hz2.le]
  have hsub := ScaleSpace.lintegral_Ioi_rpow_exp_besselKernel (p := -ν) hA one_pos
  rw [hsqA, Real.sqrt_one, div_one, mul_one,
    show 2 * (z / 2) = z by ring] at hsub
  have hcosh : ∀ v : ℝ, Real.cosh (-ν * v) = Real.cosh (ν * v) := fun v => by
    rw [neg_mul, Real.cosh_neg]
  simp only [hcosh] at hsub
  rw [ScaleSpace.lintegral_cosh_exp_eq_besselK ν (lintegral_cosh_exp_ne_top ν hz)] at hsub
  -- the integrand of the statement, on `(0,∞)`
  have hfun : ∀ t ∈ Ioi (0 : ℝ), Real.exp (-t - z ^ 2 / (4 * t)) / t ^ (ν + 1)
      = t ^ (-ν - 1) * Real.exp (-(z ^ 2 / 4 / t + 1 * t)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [show -ν - 1 = -(ν + 1) by ring, Real.rpow_neg ht0.le, div_eq_mul_inv, mul_comm]
    congr 2
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfun]
  rw [integral_eq_lintegral_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht => by
        have : (0 : ℝ) < t := ht
        positivity)) (by fun_prop), hsub]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (ScaleSpace.besselK_nonneg ν z)]
  have hpow : (z / 2) ^ ν * (z / 2) ^ (-ν) = 1 := by
    rw [Real.rpow_neg hz2.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hz2 ν).ne']
  simp only [ENNReal.toReal_ofNat]
  calc besselK ν z = 1 / 2 * ((z / 2) ^ ν * (z / 2) ^ (-ν)) * (2 * besselK ν z) := by
        rw [hpow]; ring
    _ = _ := by ring

end Pyramids
