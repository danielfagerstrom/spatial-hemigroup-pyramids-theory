/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.CreationGrid

/-!
# `lem:records-creation`: a mask whose records exhaust the bounded arrays creates maxima

Blueprint: `blueprint/src/parts/05-price.tex`, `lem:records-creation`. Phase 5, wave 3b. The
statement is the skeleton's (`PyramidsSkeleton/Ch05Price.lean`), unchanged in name and conclusion.
Its binders are fewer: it takes `1 ≤ q` for `2 ≤ q`, and no `ŵ ≥ 0`, no finiteness or symmetry of
`𝒩` and no `0 ∉ 𝒩`, which `creation_grid_2` does not read (dropped on 2026-11-15, a
strengthening).

The proof is the print's. In the indices of the level-`k` grid, `creation_grid_2` gives a positive
summable array `f_k` with one `𝒩`-maximum whose smoothing `w * f_k` has two, and whose restriction
`m ↦ (w * f_k)(qm)` has two. A positive summable array is bounded by its sum, so by the hypothesis
`f_k` is the level-`k` record of a bounded input; the level-`(k+1)` record is then
`m ↦ (w * f_k)(qm)` by the recursion of `decimRecord`.
-/

namespace Pyramids

variable {d : ℕ}

/-- **`lem:records-creation`.** For a symmetric probability `w ≠ δ₀` on `hℤ^d`, a set `𝒩` that
contains the axis neighbours and an integer `q ≥ 1`: if every bounded array on `q^k hℤ^d` is the
level-`k` record of a bounded input, then some bounded input has a level-`k` record with exactly one
`𝒩`-maximum, whose smoothing by `D_{q^k} w` has at least two, and a level-`(k+1)` record with at
least two (each read in its own grid's indices). -/
theorem records_creation (hd : 2 ≤ d) {q : ℕ} (hq : 1 ≤ q) (k : ℕ) (w : Zd d → ℝ)
    (hw : IsProbKernel w) (hsymm : ∀ n, w (-n) = w n) (hne : w ≠ deltaZ)
    (N : Set (Zd d)) (haxis : axisNbrs d ⊆ N)
    (hrec : ∀ A : Zd d → ℝ, (∃ C : ℝ, ∀ m, |A m| ≤ C) →
      ∃ f : Zd d → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) ∧ decimRecord w q f k = A) :
    ∃ f : Zd d → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) ∧ (∃! x, IsNMax N (decimRecord w q f k) x) ∧
      (∃ x y, x ≠ y ∧ IsNMax N (kconv w (decimRecord w q f k)) x ∧
        IsNMax N (kconv w (decimRecord w q f k)) y) ∧
      ∃ x y, x ≠ y ∧ IsNMax N (decimRecord w q f (k + 1)) x ∧
        IsNMax N (decimRecord w q f (k + 1)) y := by
  obtain ⟨A, hApos, hAsum, h1, h2, h3⟩ := creation_grid_2 hd w hw hsymm hne N haxis q hq
  have hAbdd : ∃ C : ℝ, ∀ m, |A m| ≤ C :=
    ⟨∑' m, A m, fun m => by
      rw [abs_of_pos (hApos m)]
      exact hAsum.le_tsum m fun j _ => (hApos j).le⟩
  obtain ⟨f, hfb, hfA⟩ := hrec A hAbdd
  have hsucc : decimRecord w q f (k + 1) = fun m => kconv w A ((q : ℤ) • m) := by
    funext m
    simp only [decimRecord, hfA]
  refine ⟨f, hfb, ?_, ?_, ?_⟩
  · rw [hfA]; exact h1
  · rw [hfA]; exact h2
  · rw [hsucc]; exact h3

end Pyramids
