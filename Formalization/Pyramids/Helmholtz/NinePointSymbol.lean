/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Helmholtz

/-!
# `lem:nine-point-symbol`: the three forms of the nine-point symbol

Blueprint: `blueprint/src/parts/05-price.tex` (since the split, `adr/0007`),
`lem:nine-point-symbol`. Phase 5, wave 1a.

The three forms of `h²D_9` are one polynomial identity in `cos x`, `cos y`, `sin x`, `sin y`,
after the addition formulas for `cos (x ± y)`.
-/

namespace Pyramids

/-- **`lem:nine-point-symbol`.** With `x = hω₁`, `y = hω₂`, `h²D_9` has the three forms
`10/3 - 4/3(cos x + cos y) - 2/3 cos x cos y`, `2/3(g(x) + g(y)) + 1/6(g(x+y) + g(x-y))` and
`h²D_5 - 1/6 g(x)g(y)`. -/
theorem nine_point_symbol {h : ℝ} (hh : 0 < h) (ω : Fin 2 → ℝ) :
    h ^ 2 * ninePointSymbol h ω = 10 / 3 - 4 / 3 * (Real.cos (h * ω 0) + Real.cos (h * ω 1)) -
        2 / 3 * (Real.cos (h * ω 0) * Real.cos (h * ω 1)) ∧
      h ^ 2 * ninePointSymbol h ω = 2 / 3 * (gcos (h * ω 0) + gcos (h * ω 1)) +
        1 / 6 * (gcos (h * ω 0 + h * ω 1) + gcos (h * ω 0 - h * ω 1)) ∧
      h ^ 2 * ninePointSymbol h ω =
        h ^ 2 * fivePointSymbol h ω - 1 / 6 * (gcos (h * ω 0) * gcos (h * ω 1)) := by
  have hh2 : h ^ 2 ≠ 0 := by positivity
  have e : h ^ 2 * ninePointSymbol h ω = 10 / 3 - 4 / 3 * (Real.cos (h * ω 0) +
      Real.cos (h * ω 1)) - 2 / 3 * (Real.cos (h * ω 0) * Real.cos (h * ω 1)) := by
    rw [ninePointSymbol, ← mul_assoc, mul_inv_cancel₀ hh2, one_mul]
  refine ⟨e, ?_, ?_⟩
  · rw [e]
    simp only [gcos, Real.cos_add, Real.cos_sub]
    ring
  · rw [e, fivePointSymbol, gridSymbol, mul_inv_cancel_left₀ hh2, Fin.sum_univ_two]
    simp only [gcos, Pi.smul_apply, smul_eq_mul]
    ring

end Pyramids
