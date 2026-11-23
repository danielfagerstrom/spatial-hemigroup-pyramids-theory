/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Pyramid
import AffineHemigroup.RadialMarginal

/-!
# `lem:isotropic-symmetric`: an isotropic family is symmetric

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `lem:isotropic-symmetric`. Phase 5, wave 1c.

The map `x ↦ -x` is the matrix `-I`, which is orthogonal (`neg_one_mem_orthSet`, the affine
export's), and `lin (-I) x = -x` (`lin_neg_one_apply`). So (I3) at `Q = -I` is the symmetry of
every law of the family.
-/

namespace Pyramids

open AffineHemigroup MeasureTheory

variable {d : ℕ}

/-- **`lem:isotropic-symmetric`.** An isotropic family in dimension `d` is symmetric: (I3) at
`Q = -I ∈ O(d)`. -/
theorem isotropicFamily_isSymmetricFamily (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsIsotropicFamily μ) : IsSymmetricFamily μ := by
  refine ⟨hμ.1.1, hμ.1.2, fun s t hs hst => ?_⟩
  have h := hμ.2 s t hs hst (-1) neg_one_mem_orthSet
  rw [push] at h
  have hfun : (lin (-1 : Mat d) : Rd d → Rd d) = fun x => -x := funext lin_neg_one_apply
  rw [hfun] at h
  exact h

end Pyramids
