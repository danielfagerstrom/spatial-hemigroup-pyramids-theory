/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.FamilyStructure
import Pyramids.Cited.A46

/-!
# `prop:no-bounded-step`: no continuous family has a step of bounded support

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:no-bounded-step`, chapter 3. Wave 2b: the
declaration moved here from `PyramidsSkeleton.Ch03Pyramid`, its statement unchanged.

The printed route. The first sentence is `cited_A46` (A46). For the second, every step of a family
with (I1) and (I2) is infinitely divisible (`isLawHemigroup_infinitelyDivisible`, Khintchine's
theorem, A41, in the affine export's form `khintchine_null_array`). In dimension `0` there is no
law other than a point mass, so the hypothesis "not a point mass" is void there.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set

variable {d : ℕ}

/-- **`prop:no-bounded-step`.** A probability measure on `ℝ^d` of bounded support, not a point
mass, is not infinitely divisible, and is no `μ_{s,t}` of any family of probability measures with
(I1) and (I2). -/
theorem no_bounded_step (w : Measure (Rd d)) [IsProbabilityMeasure w]
    (hbdd : ∃ R : ℝ, w {x | R < ‖x‖} = 0) (hnp : ∀ x : Rd d, w ≠ Measure.dirac x) :
    ¬ IsInfinitelyDivisible w ∧ ∀ μ : ℝ → ℝ → Measure (Rd d), IsLawHemigroup μ →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t ≠ w := by
  have hnid : ¬ IsInfinitelyDivisible w := by
    intro hid
    obtain ⟨R, hR⟩ := hbdd
    exact cited_A46 w hid hnp R hR
  refine ⟨hnid, fun μ hμ s t hs hst heq => ?_⟩
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- in dimension `0` every probability measure is the point mass at `0`
    subst hd0
    refine hnp 0 (Measure.ext fun A _ => ?_)
    by_cases h0 : (0 : Rd 0) ∈ A
    · have hA : A = univ := eq_univ_of_forall fun x => by
        rwa [Subsingleton.elim x 0]
      rw [hA, measure_univ, measure_univ]
    · have hA : A = ∅ := eq_empty_of_forall_notMem fun x hx => h0 (by
        rwa [Subsingleton.elim x 0] at hx)
      rw [hA, measure_empty, measure_empty]
  · exact hnid (heq ▸ isLawHemigroup_infinitelyDivisible hd hμ s t hs hst)

end Pyramids
