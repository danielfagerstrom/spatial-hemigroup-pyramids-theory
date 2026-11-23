/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Price

/-!
# The exact grid pyramid with a matrix dilation

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:expanding-grid-pyramid-not-isotropic`
(review round 2, batch C, decision D1). Definitions only: the statement is a skeleton target
(`PyramidsSkeleton.Ch05Price`). Since 2026-11-23 (review round 3, batch C, s6-7.S2, a
strengthening) the matrix is required to be invertible, where it was required to be expanding:
the proof reads one atom of the Lévy measure of a kernel, which needs `M` invertible only.

`def:exact-grid-pyramid` dilates by the scalar `q`: (c) reads `μ_{qs,qt} = D_q μ_{s,t}`
(`CarriesLatticeLadder`, unchanged). Here the dilation is a matrix `M`, and the scale ratio `q > 1`
is kept apart from it: (c) reads `μ_{qs,qt} = M_* μ_{s,t}`. At `M = q I` this is
`CarriesLatticeLadder`. The ratio is a parametrization of the scale axis: for `M = qR`, `R`
orthogonal, it is the `q` of the similarity; for a general `M` any `q > 1` serves, a change of
`q` being the relabelling `t ↦ t^{log q' / log q}`, which keeps (a)–(b).

* **The carrying family** (`CarriesMatrixLadder`): `q > 1`, `M` invertible, the laws `μ s t`,
  `0 ≤ s ≤ t`, with (a) and (b) (`IsLawHemigroup`), (c) with `M`, and (d) `μ_{1,q} = w`. Nothing
  requires `MΓ ⊆ Γ` or `M = qR`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory

variable {d : ℕ}

/-- **`μ` carries the grid pyramid of `(w, M)` at the scale ratio `q`**: `q > 1`; `M` invertible;
the `μ s t`, `0 ≤ s ≤ t`, are probability laws with (a) and (b) (`IsLawHemigroup`); (c)
`μ_{qs,qt} = M_* μ_{s,t}`; and (d) `μ_{1,q} = w`. At `M = qI` it is `CarriesLatticeLadder`. -/
def CarriesMatrixLadder (q : ℝ) (M : Mat d) (w : Measure (Rd d))
    (μ : ℝ → ℝ → Measure (Rd d)) : Prop :=
  1 < q ∧ IsUnit M ∧ IsLawHemigroup μ ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → push M (μ s t) = μ (q * s) (q * t)) ∧ μ 1 q = w

end Pyramids
