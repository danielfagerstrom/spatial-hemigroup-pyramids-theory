/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.PaperVI

/-!
# `lem:no-first-order-factorization`

Blueprint: `blueprint/src/parts/04-matern.tex`. Wave 2, group J, Q-0281.

On the plane `ω = se₀ + ue₁` an identity `1 + t²(s² + u²) = (α + β₀s + β₁u)(α' + β₀'s + β₁'u)` fixes
the six coefficients of the product (values at `(0,0)`, `(±1,0)`, `(0,±1)`, `(1,1)`). The linear
ones give `β₀' = -α'²β₀`, `β₁' = -α'²β₁`; then the mixed one is `α'²β₀β₁ = 0`, and the square of
it is `β₀β₀'β₁β₁' = t⁴`, so `t = 0`.
-/

namespace Pyramids

open AffineHemigroup

open Complex

variable {d : ℕ}

/-- **`lem:no-first-order-factorization`**: for `d ≥ 2` and `t > 0`, `1 + t²|ω|²` is not the product
of two polynomials of degree at most one in `ω ∈ ℝ^d` with complex coefficients. -/
theorem no_first_order_factorization (hd : 2 ≤ d) {t : ℝ} (ht : 0 < t) :
    ¬ ∃ (α α' : ℂ) (β β' : Fin d → ℂ), ∀ ω : Fin d → ℝ,
      (((1 + t ^ 2 * ∑ i, ω i ^ 2 : ℝ)) : ℂ) =
        (α + ∑ i, β i * (ω i : ℂ)) * (α' + ∑ i, β' i * (ω i : ℂ)) := by
  rintro ⟨α, α', β, β', h⟩
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  -- the identity on the plane spanned by `e₀, e₁`
  set pt : ℝ → ℝ → Fin d → ℝ := fun s u k => if k = i0 then s else if k = i1 then u else 0
    with hpt
  have hsum : ∀ (γ : Fin d → ℂ) (s u : ℝ), ∑ k, γ k * ((pt s u k : ℝ) : ℂ) =
      γ i0 * s + γ i1 * u := by
    intro γ s u
    rw [Finset.sum_eq_add i0 i1 h01]
    · simp [hpt, Ne.symm h01]
    · intro c _ hc
      simp [hpt, hc.1, hc.2]
    · simp
    · simp
  have hsq : ∀ s u : ℝ, ∑ k, pt s u k ^ 2 = s ^ 2 + u ^ 2 := by
    intro s u
    rw [Finset.sum_eq_add i0 i1 h01]
    · simp [hpt, Ne.symm h01]
    · intro c _ hc
      simp [hpt, hc.1, hc.2]
    · simp
    · simp
  have hP : ∀ s u : ℝ, ((1 + t ^ 2 * (s ^ 2 + u ^ 2) : ℝ) : ℂ) =
      (α + β i0 * s + β i1 * u) * (α' + β' i0 * s + β' i1 * u) := by
    intro s u
    have := h (pt s u)
    rw [hsum, hsum, hsq] at this
    rw [this]
    ring
  have e00 := hP 0 0
  have e10 := hP 1 0
  have em10 := hP (-1) 0
  have e01 := hP 0 1
  have e0m1 := hP 0 (-1)
  have e11 := hP 1 1
  push_cast at e00 e10 em10 e01 e0m1 e11
  -- the six coefficients
  have c0 : α * α' = 1 := by linear_combination -e00
  have cs : α * β' i0 + α' * β i0 = 0 := by linear_combination (em10 - e10) / 2
  have cu : α * β' i1 + α' * β i1 = 0 := by linear_combination (e0m1 - e01) / 2
  have css : β i0 * β' i0 = (t : ℂ) ^ 2 := by
    linear_combination (-(e10 + em10) / 2 + e00)
  have cuu : β i1 * β' i1 = (t : ℂ) ^ 2 := by
    linear_combination (-(e01 + e0m1) / 2 + e00)
  have csu : β i0 * β' i1 + β i1 * β' i0 = 0 := by
    linear_combination (-e11 + e10 + e01 - e00)
  -- elimination
  have b0 : β' i0 = -(α' ^ 2 * β i0) := by linear_combination α' * cs - β' i0 * c0
  have b1 : β' i1 = -(α' ^ 2 * β i1) := by linear_combination α' * cu - β' i1 * c0
  have hmix : α' ^ 2 * (β i0 * β i1) = 0 := by
    rw [b0, b1] at csu
    linear_combination -csu / 2
  have ht4 : (t : ℂ) ^ 4 = 0 := by
    have : (t : ℂ) ^ 4 = (β i0 * β' i0) * (β i1 * β' i1) := by rw [css, cuu]; ring
    rw [this, b0, b1]
    linear_combination (α' ^ 2 * (β i0 * β i1)) * hmix
  have : (t : ℂ) = 0 := pow_eq_zero_iff (n := 4) (by norm_num) |>.1 ht4
  exact ht.ne' (by exact_mod_cast this)

/-- **`lem:no-first-order-factorization`**, the line: `1 + t²ω² = (1 - itω)(1 + itω)`. -/
theorem first_order_factorization_line (t ω : ℝ) :
    (((1 + t ^ 2 * ω ^ 2 : ℝ)) : ℂ) =
      (1 - I * ((t * ω : ℝ) : ℂ)) * (1 + I * ((t * ω : ℝ) : ℂ)) := by
  push_cast
  ring_nf
  rw [I_sq]
  ring

end Pyramids
