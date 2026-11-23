/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.DiscreteHelmholtz
import Pyramids.Defs.Helmholtz

/-!
# `lem:cosine-bounds`: the Taylor bounds of the cosine

Blueprint: `blueprint/src/parts/05-price.tex` (since the split, `adr/0007`), `lem:cosine-bounds`.
Phase 5, wave 1a.

The chain of comparisons between `sin`, `cos` and their Taylor polynomials on `[0, ∞)`: each
difference vanishes at `0` and its derivative is the previous difference, so it keeps the sign of
that difference. The first six links are `DiscreteHelmholtz.lean`'s (`sin_ge_cubic`,
`cos_le_quartic`, `sin_le_quintic`, `cos_ge_sextic`, with Mathlib's `Real.sin_le` and
`Real.one_sub_sq_div_two_le_cos`); the two of order seven and eight are added here. The bounds for
`cos` are even in `x`, which carries them to every real `x`.
-/

namespace Pyramids

theorem sin_ge_septic {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  have h := nonneg_of_deriv_nonneg
    (f := fun x => Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040))
    (by fun_prop) (by simp) (fun y hy => by
      have : deriv (fun x => Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040)) y =
          Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720) := by
        have h1 : HasDerivAt (fun x => Real.sin x - (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040))
            (Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720)) y := by
          exact ((Real.hasDerivAt_sin y).sub ((((hasDerivAt_id y).sub
            ((hasDerivAt_pow 3 y).div_const 6)).add ((hasDerivAt_pow 5 y).div_const 120)).sub
              ((hasDerivAt_pow 7 y).div_const 5040))).congr_deriv (by push_cast; ring)
        exact h1.deriv
      rw [this]; linarith [cos_ge_sextic hy]) hx
  linarith

theorem cos_le_octic {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  have h := nonneg_of_deriv_nonneg
    (f := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - Real.cos x)
    (by fun_prop) (by simp) (fun y hy => by
      have : deriv (fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
          Real.cos x) y = -(y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040) + Real.sin y := by
        have h1 : HasDerivAt (fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
            Real.cos x) (-(y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040) + Real.sin y) y := by
          exact ((((((hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_pow 2 y).div_const 2)).add
            ((hasDerivAt_pow 4 y).div_const 24)).sub ((hasDerivAt_pow 6 y).div_const 720)).add
              ((hasDerivAt_pow 8 y).div_const 40320)).sub (Real.hasDerivAt_cos y)).congr_deriv
                (by push_cast; ring)
        exact h1.deriv
      rw [this]; linarith [sin_ge_septic hy]) hx
  linarith

/-- The four bounds for `cos` on `[0, ∞)`, in the form read by `cosine_bounds`. -/
theorem cos_four_bounds_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 ≤ Real.cos x ∧ Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 ∧
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x ∧
      Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 :=
  ⟨Real.one_sub_sq_div_two_le_cos, cos_le_quartic hx, cos_ge_sextic hx, cos_le_octic hx⟩

/-- **`lem:cosine-bounds`.** For every real `x`, with `g(x) = 2 - 2 cos x`:
`0 ≤ x² - g(x) ≤ x⁴/12`, `0 ≤ g(x) - x² + x⁴/12 ≤ x⁶/360`, and
`-x⁸/20160 ≤ g(x) - x² + x⁴/12 - x⁶/360 ≤ 0`. -/
theorem cosine_bounds (x : ℝ) :
    (0 ≤ x ^ 2 - gcos x ∧ x ^ 2 - gcos x ≤ x ^ 4 / 12) ∧
      (0 ≤ gcos x - x ^ 2 + x ^ 4 / 12 ∧ gcos x - x ^ 2 + x ^ 4 / 12 ≤ x ^ 6 / 360) ∧
      (-(x ^ 8 / 20160) ≤ gcos x - x ^ 2 + x ^ 4 / 12 - x ^ 6 / 360 ∧
        gcos x - x ^ 2 + x ^ 4 / 12 - x ^ 6 / 360 ≤ 0) := by
  have key : 1 - x ^ 2 / 2 ≤ Real.cos x ∧ Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 ∧
      1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x ∧
      Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
    rcases le_total 0 x with hx | hx
    · exact cos_four_bounds_nonneg hx
    · have h := cos_four_bounds_nonneg (x := -x) (by linarith)
      rw [Real.cos_neg] at h
      have e2 : (-x) ^ 2 = x ^ 2 := by ring
      have e4 : (-x) ^ 4 = x ^ 4 := by ring
      have e6 : (-x) ^ 6 = x ^ 6 := by ring
      have e8 : (-x) ^ 8 = x ^ 8 := by ring
      rw [e2, e4, e6, e8] at h
      exact h
  obtain ⟨h1, h2, h3, h4⟩ := key
  unfold gcos
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

end Pyramids
