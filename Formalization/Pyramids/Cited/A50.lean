/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Cited

/-!
# Ledger A50: `log(|x| ∨ e)` is submultiplicative (Sato, Prop. 25.4(iii), p. 159)

Interface node `thm:cited-A50` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A50 of
`blueprint/AXIOMS.md`, cited from Sato, *Lévy Processes and Infinitely Divisible Distributions*,
Proposition 25.4(iii), printed p. 159.

The author admitted A50 on 2026-11-14. **This file declares no axiom, and the declaration rests on
none**: the statement is elementary and is proved here, Lean core. Put `u := |x| ∨ e` and
`v := |y| ∨ e`. Both are at least `e > 2`, so `u + v ≤ uv` and `e ≤ uv`; with `|x + y| ≤ u + v` this
gives `|x + y| ∨ e ≤ uv`, so `g(x + y) ≤ log u + log v`. Both logarithms are at least `1`, so their
sum is at most twice their product: `g(x + y) ≤ 2 g(x) g(y)`.
-/

namespace Pyramids

open AffineHemigroup

variable {d : ℕ}

/-- **`thm:cited-A50`.** `log(|x| ∨ e)` is submultiplicative on `ℝ^d`, with the constant `2`.
Lean core. -/
theorem cited_A50 : IsSubmultiplicative (fun x : Rd d => Real.log (max ‖x‖ (Real.exp 1))) := by
  have he2 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
    linarith
  have hlog1 : ∀ x : Rd d, 1 ≤ Real.log (max ‖x‖ (Real.exp 1)) := fun x => by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact le_max_right _ _
  refine ⟨fun x => zero_le_one.trans (hlog1 x), 2, two_pos, fun x y => ?_⟩
  set u := max ‖x‖ (Real.exp 1) with hu
  set v := max ‖y‖ (Real.exp 1) with hv
  have hu2 : 2 ≤ u := he2.le.trans (le_max_right _ _)
  have hv2 : 2 ≤ v := he2.le.trans (le_max_right _ _)
  have hupos : 0 < u := by linarith
  have hvpos : 0 < v := by linarith
  have hsum : u + v ≤ u * v := by nlinarith
  have hxy : max ‖x + y‖ (Real.exp 1) ≤ u * v := by
    refine max_le ?_ ?_
    · calc ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
        _ ≤ u + v := add_le_add (le_max_left _ _) (le_max_left _ _)
        _ ≤ u * v := hsum
    · calc Real.exp 1 ≤ u := le_max_right _ _
        _ ≤ u * v := le_mul_of_one_le_right hupos.le (by linarith)
  have hpos : 0 < max ‖x + y‖ (Real.exp 1) := lt_max_of_lt_right (Real.exp_pos 1)
  have h1 : Real.log (max ‖x + y‖ (Real.exp 1)) ≤ Real.log u + Real.log v := by
    rw [← Real.log_mul hupos.ne' hvpos.ne']
    exact Real.log_le_log hpos hxy
  have hA := hlog1 x
  have hB := hlog1 y
  change Real.log (max ‖x + y‖ (Real.exp 1)) ≤ 2 * Real.log u * Real.log v
  nlinarith

end Pyramids
