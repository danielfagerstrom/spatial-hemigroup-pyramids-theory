/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.SelectionStage

/-!
# `prop:principle-other-readings`: the principle read from the origin and at every stage

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:principle-other-readings`. Phase 5, wave 3b
(on the VM).

* **(1), from the origin.** The kernel `μ_{0,t}` has the real even transform `e^{-F(t|ω|)}`, so it
  is symmetric, and `prop:stage-lemma`(3) along a unit vector `e` gives `e^{F(tx)} = 1 + kx²`,
  `k ≥ 0`, for `x ≥ 0`: `F(r) = log(1 + τr²)` with `τ = k/t²`, and `τ > 0` as `F ≢ 0`. Every kernel
  is then the Helmholtz resolvent at `τt'²` (`prop:stage-lemma`(1)). An octave step equal to a
  resolvent `(1 + ω·Cω)⁻¹` would give `(1 + ax²)(1 + kx²) = 1 + aq²x²` along `e`, `a = τt'²`; at
  `x = 1` and `x = √2` this forces `ak = 0`, so `k = 0`, and then `q² = 1`.
* **(2), every stage.** With the principle at `μ_{0,1}`, `μ_{1,2}` and `μ_{0,2}`, the stage lemma
  gives positive semidefinite `C₁`, `C₂`, `C₃`, and the cascade gives
  `(1 + x²Q₁(ω))(1 + x²Q₂(ω)) = 1 + x²Q₃(ω)`; at `x = 1` and `x = √2`, `Q₁(ω)Q₂(ω) = 0` for every
  `ω`. Writing `Cᵢ = BᵢᵀBᵢ`, a zero of `Q₁` is in the kernel of `B₁`: if `Q₁(ω₁) > 0` and
  `Q₂(ω₂) > 0`, then `Q₂(ω₁) = 0 = Q₁(ω₂)` and both are positive at `ω₁ + ω₂`. So `Q₁ ≡ 0` or
  `Q₂ ≡ 0`, and that stage is `δ₀`, against (ND).

Dropped binders (2026-11-15, a strengthening): `principle_other_readings_1` takes no continuity of
`F`; `principle_other_readings_2` takes no `1 ≤ d`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace Matrix ComplexOrder

variable {d : ℕ}

/-- Two points decide `(1 + ax²)(1 + kx²) = 1 + bx²`: `ak = 0` and `a + k = b`. -/
theorem prod_coeff_of_two_points {a k b : ℝ} (h1 : (1 + a) * (1 + k) = 1 + b)
    (h2 : (1 + a * 2) * (1 + k * 2) = 1 + b * 2) : a * k = 0 ∧ a + k = b := by
  constructor
  · linear_combination (h2 - 2 * h1) / 2
  · linear_combination (4 * h1 - h2) / 2

/-! ## Clause (1) -/

/-- **`prop:principle-other-readings`(1), from the origin.** For a family with transforms
`exp(-[F(t|ω|) - F(s|ω|)])`, `F(0) = 0`, `F ≢ 0`: if one kernel `μ_{0,t}` has the principle,
`F(r) = log(1 + τr²)` with `τ > 0`, every kernel has it, and no octave step, at any ratio `q > 1`,
is a resolvent `(1 + ω·Cω)⁻¹`. -/
theorem principle_other_readings_1 (hd : 1 ≤ d) (F : ℝ → ℝ)
    (hF0 : F 0 = 0) (hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) (μ : ℝ → ℝ → Measure (Rd d))
    (hfam : IsFamily μ)
    (hμ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ ω : Rd d,
      charFun (μ s t) ω = ((Real.exp (-(F (t * ‖ω‖) - F (s * ‖ω‖))) : ℝ) : ℂ))
    {t : ℝ} (ht : 0 < t) (hP : HasImplicitEulerPrinciple (μ 0 t)) :
    ∃ τ : ℝ, 0 < τ ∧ (∀ r : ℝ, 0 ≤ r → F r = Real.log (1 + τ * r ^ 2)) ∧
      (∀ t' : ℝ, 0 < t' → HasImplicitEulerPrinciple (μ 0 t')) ∧
      ∀ q : ℝ, 1 < q → ∀ t' : ℝ, 0 < t' → ¬ ∃ C : Mat d, ∀ ω : Rd d,
        charFun (μ t' (q * t')) ω = (((1 + quad C ω)⁻¹ : ℝ) : ℂ) := by
  have hprob := hfam.1.isProbability
  -- the kernels' transforms
  have hk0 : ∀ t' : ℝ, 0 ≤ t' → ∀ ω : Rd d,
      charFun (μ 0 t') ω = ((Real.exp (-F (t' * ‖ω‖)) : ℝ) : ℂ) := fun t' ht' ω => by
    rw [hμ 0 t' le_rfl ht' ω, zero_mul, hF0, sub_zero]
  haveI := hprob 0 t le_rfl ht.le
  have hsymm := map_neg_of_charFun_norm (G := fun r => Real.exp (-F (t * r))) (hk0 t ht.le)
  obtain ⟨e, he, k, hk, hray⟩ := exists_resolvent_ray hd hsymm hP
  -- `e^{F(tx)} = 1 + kx²` for `x ≥ 0`
  have hFt : ∀ x : ℝ, 0 ≤ x → F (t * x) = Real.log (1 + k * x ^ 2) := by
    intro x hx
    have h := (hk0 t ht.le (x • e)).symm.trans (hray x)
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg hx] at h
    have h2 := Complex.ofReal_injective h
    rw [Real.exp_neg] at h2
    rw [← inv_injective h2, Real.log_exp]
  set τ := k / t ^ 2 with hτ
  have hFτ : ∀ r : ℝ, 0 ≤ r → F r = Real.log (1 + τ * r ^ 2) := by
    intro r hr
    have h := hFt (r / t) (div_nonneg hr ht.le)
    rw [mul_div_cancel₀ r ht.ne'] at h
    rw [h, hτ, div_pow]
    congr 2
    field_simp
  have hτpos : 0 < τ := by
    rcases (div_nonneg hk (sq_nonneg t)).eq_or_lt with h0 | h0
    · obtain ⟨r, hr, hFr⟩ := hFne
      exact absurd (by rw [hFτ r hr, hτ, ← h0]; simp) hFr
    · exact h0
  -- every kernel is a Helmholtz resolvent
  have hres : ∀ t' : ℝ, 0 ≤ t' → ∀ ω : Rd d,
      charFun (μ 0 t') ω = (((1 + τ * t' ^ 2 * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ) := fun t' ht' ω => by
    rw [hk0 t' ht' ω, hFτ _ (by positivity), Real.exp_neg, Real.exp_log (by positivity)]
    ring_nf
  refine ⟨τ, hτpos, hFτ, fun t' ht' => ?_, fun q hq t' ht' => ?_⟩
  · haveI := hprob 0 t' le_rfl ht'.le
    exact stage_lemma_1_helmholtz (by positivity) _ (hres t' ht'.le)
  · rintro ⟨C, hC⟩
    have hq0 : 0 < q := by linarith
    have hle : t' ≤ q * t' := le_mul_of_one_le_left ht'.le hq.le
    -- along `e`: `(1 + ax²)(1 + Kx²) = 1 + aq²x²`
    set a := τ * t' ^ 2 with ha
    set K := quad C e with hK
    have hpoly : ∀ x : ℝ, 0 ≤ x → (1 + a * x ^ 2) * (1 + K * x ^ 2) = 1 + a * q ^ 2 * x ^ 2 := by
      intro x hx
      have h := (hμ t' (q * t') ht'.le hle (x • e)).symm.trans (hC (x • e))
      rw [norm_smul, he, mul_one, Real.norm_of_nonneg hx, Pyramids.quad_smul] at h
      have h2 := Complex.ofReal_injective h
      rw [mul_assoc q t' x, hFτ _ (by positivity), hFτ _ (by positivity), neg_sub,
        Real.exp_sub, Real.exp_log (by positivity), Real.exp_log (by positivity)] at h2
      have h3 : 1 + x ^ 2 * K = (1 + τ * (q * (t' * x)) ^ 2) / (1 + τ * (t' * x) ^ 2) := by
        rw [← inv_inv (1 + x ^ 2 * K), ← h2, inv_div]
      have hp : 0 < 1 + τ * (t' * x) ^ 2 := by positivity
      rw [eq_div_iff hp.ne'] at h3
      rw [ha]
      linear_combination h3
    have h1 := hpoly 1 zero_le_one
    have h2 := hpoly (Real.sqrt 2) (Real.sqrt_nonneg 2)
    rw [Real.sq_sqrt zero_le_two] at h2
    simp only [one_pow, mul_one] at h1
    obtain ⟨hak, hsum⟩ := prod_coeff_of_two_points h1 h2
    have hapos : 0 < a := by positivity
    have hK0 : K = 0 := (mul_eq_zero.1 hak).resolve_left hapos.ne'
    rw [hK0, add_zero] at hsum
    have : a * (q ^ 2 - 1) = 0 := by linear_combination -hsum
    rcases mul_eq_zero.1 this with h | h
    · exact hapos.ne' h
    · nlinarith

/-! ## Clause (2) -/

/-- A positive semidefinite form `Q₁` with `Q₁(ω₂) = 0` has `Q₁(ω₁ + ω₂) = Q₁(ω₁)`. -/
theorem quad_add_of_quad_eq_zero {C : Mat d} (hC : C.PosSemidef) {ω₁ ω₂ : Rd d}
    (h : quad C ω₂ = 0) : quad C (ω₁ + ω₂) = quad C ω₁ := by
  obtain ⟨B, rfl⟩ := exists_transpose_mul_self hC
  rw [quad_transpose_mul_self_eq] at h ⊢
  rw [quad_transpose_mul_self_eq, map_add, norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h),
    add_zero]

/-- Two positive semidefinite forms whose product vanishes everywhere: one vanishes. -/
theorem quad_eq_zero_of_mul {C₁ C₂ : Mat d} (h₁ : C₁.PosSemidef) (h₂ : C₂.PosSemidef)
    (h : ∀ ω, quad C₁ ω * quad C₂ ω = 0) : (∀ ω, quad C₁ ω = 0) ∨ ∀ ω, quad C₂ ω = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨⟨ω₁, hω₁⟩, ⟨ω₂, hω₂⟩⟩ := hne
  have hb₁ : quad C₂ ω₁ = 0 := (mul_eq_zero.1 (h ω₁)).resolve_left hω₁
  have ha₂ : quad C₁ ω₂ = 0 := (mul_eq_zero.1 (h ω₂)).resolve_right hω₂
  have h12 := h (ω₁ + ω₂)
  rw [quad_add_of_quad_eq_zero h₁ ha₂, add_comm, quad_add_of_quad_eq_zero h₂ hb₁] at h12
  exact (mul_eq_zero.1 h12).elim hω₁ hω₂

/-- **`prop:principle-other-readings`(2), every stage.** No symmetric family has the principle at
every stage `μ_{s,t}`, `0 ≤ s < t`. -/
theorem principle_other_readings_2 (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) :
    ¬ ∀ s t : ℝ, 0 ≤ s → s < t → HasImplicitEulerPrinciple (μ s t) := by
  intro hP
  obtain ⟨hH, hND, hS⟩ := hμ
  have hprob := hH.isProbability
  haveI := hprob 0 1 le_rfl zero_le_one
  haveI := hprob 1 2 zero_le_one one_le_two
  haveI := hprob 0 2 le_rfl zero_le_two
  obtain ⟨C₁, hC₁, h₁⟩ :=
    stage_lemma_3 (μ 0 1) (hS 0 1 le_rfl zero_le_one) (hP 0 1 le_rfl one_pos)
  obtain ⟨C₂, hC₂, h₂⟩ :=
    stage_lemma_3 (μ 1 2) (hS 1 2 zero_le_one one_le_two) (hP 1 2 zero_le_one one_lt_two)
  obtain ⟨C₃, -, h₃⟩ :=
    stage_lemma_3 (μ 0 2) (hS 0 2 le_rfl zero_le_two) (hP 0 2 le_rfl two_pos)
  -- the cascade along a ray: `(1 + x²Q₁)(1 + x²Q₂) = 1 + x²Q₃`
  have hpoly : ∀ (ω : Rd d) (x : ℝ),
      (1 + quad C₁ ω * x ^ 2) * (1 + quad C₂ ω * x ^ 2) = 1 + quad C₃ ω * x ^ 2 := by
    intro ω x
    have h := congrArg (fun ρ => charFun ρ (x • ω))
      (hH.cascade 0 1 2 le_rfl zero_le_one one_le_two)
    simp only [charFun_conv, h₁, h₂, h₃, Pyramids.quad_smul] at h
    have h2 : (1 + x ^ 2 * quad C₃ ω)⁻¹ =
        (1 + x ^ 2 * quad C₂ ω)⁻¹ * (1 + x ^ 2 * quad C₁ ω)⁻¹ := by
      exact_mod_cast h
    rw [← mul_inv, inv_inj] at h2
    linear_combination -h2
  have hzero : ∀ ω, quad C₁ ω * quad C₂ ω = 0 := fun ω => by
    have h1 := hpoly ω 1
    have h2 := hpoly ω (Real.sqrt 2)
    rw [Real.sq_sqrt zero_le_two] at h2
    simp only [one_pow, mul_one] at h1
    exact (prod_coeff_of_two_points h1 h2).1
  rcases quad_eq_zero_of_mul hC₁ hC₂ hzero with h0 | h0
  · exact hND 0 1 le_rfl one_pos (eq_dirac_of_charFun_one fun ω => by simp [h₁, h0])
  · exact hND 1 2 zero_le_one one_lt_two (eq_dirac_of_charFun_one fun ω => by simp [h₂, h0])

end Pyramids
