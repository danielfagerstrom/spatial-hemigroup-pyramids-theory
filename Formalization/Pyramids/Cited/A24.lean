/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Cited
import ScaleSpaceCore.PolyaFrequencyClass

/-!
# Ledger A24: Schoenberg's representation (Karlin, *Total Positivity* I, Ch. 7, Thm. 3.2(a))

**This file widens the trust base of the article: it declares one axiom**, admitted by the author
on 2026-11-15 (`adr/0005-a22-and-a24-admitted.md`). Ledger entry A24 of `blueprint/AXIOMS.md`,
with its page transcription in `blueprint/AXIOMS-verbatim.md`; interface node `thm:cited-A24`
(`blueprint/src/parts/02-cited-facts.tex`); listed in `blueprint/trust-boundary.txt`.

Source: Karlin, *Total Positivity* I, Chapter 7, Theorem 3.2(a), printed p. 345, whose statement
carries `γ + ∑ aᵢ² > 0` (p. 346 adds that it is essential; V-selection p. 35 anchors it to Remark
3.1, p. 346, which is about dropping integrability), the class `𝓔₂*` of display (2.2), p. 336, and Proposition 1.4, p. 333; as V-selection
v0.1 prints it in § 4.3, pp. 34–36, at Karlin's letter (the entry's verdict NARROWER-OK). The
necessity direction: the reciprocal of the two-sided Laplace transform `L(s) = ∫ e^{-sx} φ(x) dx`
of a Pólya frequency density is an entire function of class `𝓔₂*` with `γ + ∑ aⱼ² > 0`. `𝓔₂*`
is the shared core's `polyaE2 γ δ a`, for any square-summable sequence `a : ℕ → ℝ`.

**Admitted narrower than the page, and narrower than the skeleton's type.** The page, and the
skeleton's `cited_A24`, assert an open strip `α < Re s < β`, `α < 0 < β`, on which `L` converges
absolutely and `L ψ = 1`. Both spenders read the identity only on the imaginary axis `s = iω`,
which lies in every such strip (`records/pyramids/PRICE-unadmitted-entries.md`, A24):
`thm:matern-pyramid-line-noncreation`(3) reads that `ψ` is entire and that `L(iω) ψ(iω) = 1`;
`prop:classical-pyramids-approximate-discrete-gaussian` reads the modulus `‖ψ(iω)‖`. So the axiom
states the identity for every real `ω` at `s = ωi`, where the integral converges absolutely for
any integrable `φ`, and drops the strip and its absolute convergence. It keeps the class of
p. 336 as the page gives it: `γ ≥ 0`, `δ` real, `aⱼ` real, `∑ aⱼ² < ∞`, `ψ` entire with
`ψ(0) = 1`, and the normalization `γ + ∑ aⱼ² > 0` of Thm. 3.2(a). It is implied by the page's
statement at `s = ωi`. Not carried: the strip (Prop. 1.4); the converse (p. 336, the sentence
after (2.2)); that a Pólya frequency density has an absolutely continuous Lévy measure (plan id
A25), which `prop:classical-pyramids-approximate-discrete-gaussian` proves from this entry.

Not derived from the admitted entries: the pricing found that it needs a factorization theory of
entire functions of genus at most 2 that Mathlib lacks.
-/

namespace Pyramids

open MeasureTheory
open ScaleSpace (polyaE2)

/-- **`thm:cited-A24`, ledger A24** (Karlin, Ch. 7, Thm. 3.2(a), p. 345,
(2.2), p. 336), on the imaginary axis. For a Pólya frequency density `φ` there are `γ ≥ 0`,
`δ ∈ ℝ` and real `aⱼ` with `∑ aⱼ² < ∞` and `γ + ∑ aⱼ² > 0` such that
`ψ(s) = e^{-γs² + δs} ∏ⱼ (1 + aⱼs) e^{-aⱼs}` is entire, `ψ(0) = 1`, and `L(iω) ψ(iω) = 1` for
every real `ω`, `L(s) = ∫ e^{-sx} φ(x) dx`. Admitted by the author on 2026-11-15. -/
axiom cited_A24 (φ : ℝ → ℝ) (hφ : IsPolyaFrequencyDensity φ) :
    ∃ (γ δ : ℝ) (a : ℕ → ℝ), 0 ≤ γ ∧ Summable (fun j => a j ^ 2) ∧
      0 < γ + ∑' j, a j ^ 2 ∧ Differentiable ℂ (polyaE2 γ δ a) ∧ polyaE2 γ δ a 0 = 1 ∧
      ∀ ω : ℝ, (∫ x : ℝ, Complex.exp (-((ω : ℂ) * Complex.I) * x) * (φ x : ℂ)) *
        polyaE2 γ δ a ((ω : ℂ) * Complex.I) = 1

end Pyramids
