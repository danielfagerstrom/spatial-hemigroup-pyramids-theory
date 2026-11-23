/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.KconvBdd
import Pyramids.Helmholtz.NinePointSymbol

/-!
# `prop:nine-point-family`: the nine-point family on `hℤ²`

Blueprint: `blueprint/src/parts/05-price.tex` (since the split, `adr/0007`),
`prop:nine-point-family`. Phase 5, wave 1e.

The first section works for any probability step `τ` on `ℤ^d` and any `a > 0`: the geometric
resolvent `K := (1-p)∑ₖ pᵏτ^{*k}`, `p = a/(1+a)`, is a probability kernel with transfer
`(1 + a(1 - τ̂))⁻¹` when `τ̂` is real, it solves `(1+a)K - aK * τ = δ₀`, a bounded solution of
`(1+a)e - a e * τ = 0` vanishes (`sup|e| ≤ p sup|e|`), and two members satisfy the resolvent
identity `K_b * K_a = (aK_a - bK_b)/(a - b)`. The second section reads the nine-point step:
`σ_9` is a sum of eight weighted point masses, so `t²Δ_9 u = (10/3)ν_h(σ_9 * u - u)` for every
`u`, and `σ̂_9(x, y) = (2/5)(cos x + cos y) + (1/5)cos x cos y`, whence
`t²D_9 = (10/3)ν_h(1 - σ̂_9)`. The proposition is the first section at `τ = σ_9`,
`a = (10/3)ν_h`, with the cascade assembled as in `discrete_helmholtz_cascade`.
-/

namespace Pyramids

open AffineHemigroup

/-! ## The geometric resolvent of a probability step -/

section Resolvent

variable {d : ℕ}

/-- **The geometric resolvent** `(1-p) ∑_{k ≥ 0} pᵏ τ^{*k}`, `p = a/(1+a)`, of a step `τ`. -/
noncomputable def stepResolvent (τ : Zd d → ℝ) (a : ℝ) (n : Zd d) : ℝ :=
  (1 - a / (1 + a)) * ∑' k : ℕ, (a / (1 + a)) ^ k * kpow τ k n

variable {τ : Zd d → ℝ} {a : ℝ}

theorem stepP_pos (ha : 0 < a) : 0 < a / (1 + a) := by positivity

theorem stepP_lt_one (ha : 0 < a) : a / (1 + a) < 1 := (div_lt_one (by linarith)).2 (by linarith)

theorem summable_stepResolvent_pair (hτ : IsProbKernel τ) (ha : 0 < a) :
    Summable fun q : ℕ × Zd d => (a / (1 + a)) ^ q.1 * kpow τ q.1 q.2 := by
  have hp0 := (stepP_pos ha).le
  have hp1 := stepP_lt_one ha
  set p := a / (1 + a)
  have hnn : 0 ≤ fun q : ℕ × Zd d => p ^ q.1 * kpow τ q.1 q.2 := fun q =>
    mul_nonneg (pow_nonneg hp0 _) ((isProbKernel_kpow hτ q.1).1 _)
  have hrow : ∀ k : ℕ, Summable fun n : Zd d => p ^ k * kpow τ k n := fun k =>
    (isProbKernel_kpow hτ k).2.1.mul_left _
  have hcol : Summable fun k : ℕ => ∑' n : Zd d, p ^ k * kpow τ k n := by
    refine (summable_geometric_of_lt_one hp0 hp1).congr fun k => ?_
    rw [tsum_mul_left, (isProbKernel_kpow hτ k).2.2, mul_one]
  exact (summable_prod_of_nonneg hnn).2 ⟨hrow, hcol⟩

/-- The resolvent of a probability step is a probability kernel. -/
theorem isProbKernel_stepResolvent (hτ : IsProbKernel τ) (ha : 0 < a) :
    IsProbKernel (stepResolvent τ a) := by
  have hp0 := (stepP_pos ha).le
  have hp1 := stepP_lt_one ha
  have hF := summable_stepResolvent_pair hτ ha
  refine ⟨fun n => ?_, ?_, ?_⟩
  · exact mul_nonneg (by linarith) (tsum_nonneg fun k => mul_nonneg (pow_nonneg hp0 _)
      ((isProbKernel_kpow hτ k).1 _))
  · exact hF.prod_symm.prod.mul_left (1 - a / (1 + a))
  · unfold stepResolvent
    rw [tsum_mul_left, hF.tsum_comm (f := fun k n => (a / (1 + a)) ^ k * kpow τ k n)]
    simp_rw [tsum_mul_left, (isProbKernel_kpow hτ _).2.2, mul_one]
    rw [tsum_geometric_of_lt_one hp0 hp1]
    field_simp [show (1 : ℝ) - a / (1 + a) ≠ 0 by linarith]

/-- **The transfer of the resolvent**: if `τ̂(θ) = φ` is real, then
`K̂(θ) = (1 + a(1 - φ))⁻¹`. -/
theorem gridFourier_stepResolvent (hτ : IsProbKernel τ) (ha : 0 < a) (θ : Fin d → ℝ) {φ : ℝ}
    (hφ : gridFourier τ θ = φ) (hφ1 : |φ| ≤ 1) :
    gridFourier (stepResolvent τ a) θ = (((1 + a * (1 - φ))⁻¹ : ℝ) : ℂ) := by
  have hp0 := (stepP_pos ha).le
  have hp1 := stepP_lt_one ha
  have hF := summable_stepResolvent_pair hτ ha
  set p := a / (1 + a) with hp
  have hG : Summable fun q : ℕ × Zd d =>
      ((p ^ q.1 * kpow τ q.1 q.2 : ℝ) : ℂ) * Complex.exp ((gphase θ q.2 : ℂ) * Complex.I) :=
    Summable.of_norm (hF.norm.congr fun q => by
      simp only [norm_mul, norm_cexp_gphase, mul_one, Complex.norm_real])
  rw [gridFourier_eq]
  have e1 : ∀ n, ((stepResolvent τ a n : ℝ) : ℂ) * Complex.exp ((gphase θ n : ℂ) * Complex.I) =
      ((1 - p : ℝ) : ℂ) * ∑' k : ℕ, ((p ^ k * kpow τ k n : ℝ) : ℂ) *
        Complex.exp ((gphase θ n : ℂ) * Complex.I) := by
    intro n
    rw [stepResolvent, Complex.ofReal_mul, Complex.ofReal_tsum, mul_assoc, tsum_mul_right]
  simp_rw [e1]
  rw [tsum_mul_left, hG.tsum_comm (f := fun k n => ((p ^ k * kpow τ k n : ℝ) : ℂ) *
    Complex.exp ((gphase θ n : ℂ) * Complex.I))]
  have e2 : ∀ k : ℕ, ∑' n, ((p ^ k * kpow τ k n : ℝ) : ℂ) *
      Complex.exp ((gphase θ n : ℂ) * Complex.I) = ((p * φ : ℝ) : ℂ) ^ k := by
    intro k
    have := gridFourier_kpow hτ.2.1 θ k
    rw [hφ, gridFourier_eq] at this
    rw [show (fun n => ((p ^ k * kpow τ k n : ℝ) : ℂ) *
        Complex.exp ((gphase θ n : ℂ) * Complex.I)) =
      fun n => ((p ^ k : ℝ) : ℂ) * (((kpow τ k n : ℝ) : ℂ) *
        Complex.exp ((gphase θ n : ℂ) * Complex.I)) from funext fun n => by push_cast; ring,
      tsum_mul_left, this]
    push_cast
    ring
  simp_rw [e2]
  have hpφ1 : p * φ < 1 := by
    calc p * φ ≤ p * |φ| := by gcongr; exact le_abs_self φ
      _ ≤ p * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hp1
  have hpφ : ‖((p * φ : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hp0]
    calc p * |φ| ≤ p * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hp1
  rw [(hasSum_geometric_of_norm_lt_one hpφ).tsum_eq]
  have h1 : 1 - p * φ ≠ 0 := by linarith
  have h2 : (1 : ℝ) + a ≠ 0 := by linarith
  have h3 : (1 : ℝ) + a * (1 - φ) ≠ 0 := by
    have : φ ≤ 1 := (le_abs_self φ).trans hφ1
    nlinarith
  have h3' : (1 : ℝ) + a - a * φ ≠ 0 := by
    have : φ ≤ 1 := (le_abs_self φ).trans hφ1
    nlinarith
  rw [show ((1 : ℂ) - ((p * φ : ℝ) : ℂ)) = ((1 - p * φ : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  rw [hp]
  field_simp
  ring

/-- `K * τ = (K - (1-p)δ₀)/p`. -/
theorem kconv_stepResolvent_step (hτ : IsProbKernel τ) (ha : 0 < a) (n : Zd d) :
    kconv (stepResolvent τ a) τ n =
      (stepResolvent τ a n - (1 - a / (1 + a)) * deltaZ n) / (a / (1 + a)) := by
  have hp0 := stepP_pos ha
  have hF := summable_stepResolvent_pair hτ ha
  set p := a / (1 + a) with hp
  have hτ1 : ∀ x, τ x ≤ 1 := fun x => by
    rw [← hτ.2.2]; exact hτ.2.1.le_tsum x fun j _ => hτ.1 j
  have hH : Summable fun q : ℕ × Zd d => p ^ q.1 * kpow τ q.1 q.2 * τ (n - q.2) := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg (mul_nonneg (pow_nonneg hp0.le _)
      ((isProbKernel_kpow hτ _).1 _)) (hτ.1 _)) (fun q => ?_) hF
    calc p ^ q.1 * kpow τ q.1 q.2 * τ (n - q.2)
        ≤ p ^ q.1 * kpow τ q.1 q.2 * 1 := by
          gcongr
          · exact mul_nonneg (pow_nonneg hp0.le _) ((isProbKernel_kpow hτ _).1 _)
          · exact hτ1 _
      _ = _ := mul_one _
  have h1 : kconv (stepResolvent τ a) τ n = (1 - p) * ∑' k : ℕ, p ^ k * kpow τ (k + 1) n := by
    unfold kconv
    simp_rw [stepResolvent, ← hp, mul_assoc, ← tsum_mul_right]
    rw [tsum_mul_left]
    congr 1
    rw [hH.tsum_comm (f := fun k m => p ^ k * kpow τ k m * τ (n - m))]
    congr 1
    funext k
    simp_rw [mul_assoc]
    rw [tsum_mul_left]
    rfl
  have hs : Summable fun k : ℕ => p ^ k * kpow τ k n := hF.prod_symm.prod_factor n
  have h2 : stepResolvent τ a n =
      (1 - p) * (deltaZ n + p * ∑' k : ℕ, p ^ k * kpow τ (k + 1) n) := by
    rw [stepResolvent, ← hp, hs.tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul]
    congr 2
    exact tsum_congr fun k => by rw [pow_succ]; ring
  rw [h1, h2]
  field_simp
  ring

/-- **The resolvent equation** `(1 + a)K - aK * τ = δ₀`. -/
theorem stepResolvent_eqn (hτ : IsProbKernel τ) (ha : 0 < a) (n : Zd d) :
    (1 + a) * stepResolvent τ a n - a * kconv (stepResolvent τ a) τ n = deltaZ n := by
  rw [kconv_stepResolvent_step hτ ha]
  have h1 : (1 : ℝ) + a ≠ 0 := by linarith
  field_simp
  ring

/-- **The maximum principle**: a bounded solution of `(1 + a)e - a e * τ = 0` vanishes. -/
theorem stepResolvent_unique (hτ : IsProbKernel τ) (ha : 0 < a) {e : Zd d → ℝ}
    (hb : ∃ C, ∀ n, |e n| ≤ C) (he : ∀ n, (1 + a) * e n - a * kconv e τ n = 0) : e = 0 := by
  obtain ⟨C, hC⟩ := hb
  have hbdd : BddAbove (Set.range fun n => |e n|) := ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩
  set M := ⨆ n, |e n| with hM
  have hle : ∀ n, |e n| ≤ M := fun n => le_ciSup hbdd n
  have hM0 : 0 ≤ M := (abs_nonneg (e 0)).trans (hle 0)
  have hconv : ∀ n, |kconv e τ n| ≤ M := by
    intro n
    rw [kconv_comm]
    have hs := summable_bounded_mul hτ.2.1 hle n
    calc |kconv τ e n| = |∑' m, τ m * e (n - m)| := rfl
      _ ≤ ∑' m, |τ m * e (n - m)| := by
          simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
      _ ≤ ∑' m, τ m * M := by
          refine Summable.tsum_le_tsum (fun m => ?_) hs.abs (hτ.2.1.mul_right M)
          rw [abs_mul, abs_of_nonneg (hτ.1 m)]
          exact mul_le_mul_of_nonneg_left (hle _) (hτ.1 m)
      _ = M := by rw [tsum_mul_right, hτ.2.2, one_mul]
  have key : ∀ n, |e n| ≤ a / (1 + a) * M := by
    intro n
    have h1 : (1 + a) * e n = a * kconv e τ n := by linarith [he n]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    have : |e n| * (1 + a) = a * |kconv e τ n| := by
      rw [← abs_of_pos (show 0 < 1 + a by linarith), ← abs_mul, mul_comm, h1, abs_mul,
        abs_of_pos ha]
    rw [this]
    exact mul_le_mul_of_nonneg_left (hconv n) ha.le
  have hMle : M ≤ a / (1 + a) * M := ciSup_le key
  have hp1 := stepP_lt_one ha
  have hMz : M = 0 := by nlinarith
  funext n
  have := hle n
  rw [hMz] at this
  exact abs_nonpos_iff.1 this

/-- **The resolvent identity** `K_b * K_a = (aK_a - bK_b)/(a - b)` for `a, b > 0`, `a ≠ b`. -/
theorem stepResolvent_resolvent (hτ : IsProbKernel τ) {b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    kconv (stepResolvent τ b) (stepResolvent τ a) =
      fun n => (a * stepResolvent τ a n - b * stepResolvent τ b n) / (a - b) := by
  have hKa := (isProbKernel_stepResolvent hτ ha).2.1
  have hKb := (isProbKernel_stepResolvent hτ hb).2.1
  have hτs := hτ.2.1
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  set X := kconv (stepResolvent τ b) (stepResolvent τ a) with hX
  set Z : Zd d → ℝ := fun n => (a * stepResolvent τ a n - b * stepResolvent τ b n) / (a - b)
    with hZ
  have hXs : Summable X := summable_kconv hKb hKa
  have hZ' : Z = fun n => (a / (a - b)) * stepResolvent τ a n +
      (-b / (a - b)) * stepResolvent τ b n := funext fun n => by simp only [hZ]; ring
  have hZs : Summable Z := by
    rw [hZ']; exact (hKa.mul_left _).add (hKb.mul_left _)
  -- `(1+a)X - aX * τ = K_b`
  have hXeq : ∀ n, (1 + a) * X n - a * kconv X τ n = stepResolvent τ b n := by
    intro n
    have hassoc : kconv X τ = kconv (stepResolvent τ b) (kconv (stepResolvent τ a) τ) :=
      kconv_assoc hKb hKa hτs
    have hlin := congrFun (kconv_add_smul_right hKb hKa (summable_kconv hKa hτs) (1 + a) (-a)) n
    have hdelta : (fun m => (1 + a) * stepResolvent τ a m + -a * kconv (stepResolvent τ a) τ m) =
        deltaZ := funext fun m => by rw [← stepResolvent_eqn hτ ha m]; ring
    rw [hdelta, kconv_deltaZ_right] at hlin
    rw [hassoc, hX]
    linarith
  -- `(1+a)Z - aZ * τ = K_b`
  have hZeq : ∀ n, (1 + a) * Z n - a * kconv Z τ n = stepResolvent τ b n := by
    intro n
    have hlin := congrFun (kconv_add_smul_left hKa hKb hτs (a / (a - b)) (-b / (a - b))) n
    rw [← hZ'] at hlin
    rw [hlin]
    have ea := stepResolvent_eqn hτ ha n
    have eb := stepResolvent_eqn hτ hb n
    have hb0 : b ≠ 0 := hb.ne'
    have ha0 : a ≠ 0 := ha.ne'
    have ka : kconv (stepResolvent τ a) τ n = ((1 + a) * stepResolvent τ a n - deltaZ n) / a := by
      field_simp; linarith
    have kb : kconv (stepResolvent τ b) τ n = ((1 + b) * stepResolvent τ b n - deltaZ n) / b := by
      field_simp; linarith
    rw [ka, kb, hZ]
    field_simp
    ring
  have hz := stepResolvent_unique hτ ha (e := fun n => X n - Z n) (by
    obtain ⟨C1, hC1⟩ := bounded_of_summable_Z hXs
    obtain ⟨C2, hC2⟩ := bounded_of_summable_Z hZs
    exact ⟨C1 + C2, fun n => (abs_sub _ _).trans (add_le_add (hC1 n) (hC2 n))⟩) fun n => by
      have hlin := congrFun (kconv_add_smul_left hXs hZs hτs 1 (-1)) n
      rw [show (fun n => 1 * X n + -1 * Z n) = fun n => X n - Z n from
        funext fun n => by ring] at hlin
      rw [hlin]
      have h1 := hXeq n
      have h2 := hZeq n
      linarith
  funext n
  have := congrFun hz n
  simp only [Pi.zero_apply] at this
  linarith

end Resolvent

/-! ## The nine-point step -/

/-- **`σ_9` is a sum of eight weighted point masses.** -/
theorem ninePointStep_eq (m : Zd 2) :
    ninePointStep m =
      1 / 5 * (deltaZ (m - zbasis 0) + deltaZ (m - -zbasis 0) + deltaZ (m - zbasis 1) +
          deltaZ (m - -zbasis 1)) +
        1 / 20 * (deltaZ (m - (zbasis 0 + zbasis 1)) + deltaZ (m - (zbasis 0 - zbasis 1)) +
          deltaZ (m - (-zbasis 0 + zbasis 1)) + deltaZ (m - (-zbasis 0 - zbasis 1))) := by
  simp only [ninePointStep, Fin.sum_univ_two, deltaZ_sub_eq, mul_add, mul_ite, mul_one, mul_zero]
  ring

/-- `σ_9 * u`, for every `u`, as a finite sum. -/
theorem hasSum_ninePointStep_mul (u : Zd 2 → ℝ) (n : Zd 2) :
    HasSum (fun m => ninePointStep m * u (n - m))
      (1 / 5 * (u (n + zbasis 0) + u (n - zbasis 0) + u (n + zbasis 1) + u (n - zbasis 1)) +
        1 / 20 * (u (n + zbasis 0 + zbasis 1) + u (n + zbasis 0 - zbasis 1) +
          u (n - zbasis 0 + zbasis 1) + u (n - zbasis 0 - zbasis 1))) := by
  have H := (((((((hasSum_delta_mul (zbasis 0) n u (1 / 5)).add
    (hasSum_delta_mul (-zbasis 0) n u (1 / 5))).add
    (hasSum_delta_mul (zbasis 1) n u (1 / 5))).add
    (hasSum_delta_mul (-zbasis 1) n u (1 / 5))).add
    (hasSum_delta_mul (zbasis 0 + zbasis 1) n u (1 / 20))).add
    (hasSum_delta_mul (zbasis 0 - zbasis 1) n u (1 / 20))).add
    (hasSum_delta_mul (-zbasis 0 + zbasis 1) n u (1 / 20))).add
    (hasSum_delta_mul (-zbasis 0 - zbasis 1) n u (1 / 20))
  convert H using 1
  · funext m
    rw [ninePointStep_eq]
    ring
  · have p1 : n - (zbasis 0 + zbasis 1) = n - zbasis 0 - zbasis 1 := by abel
    have p2 : n - (zbasis 0 - zbasis 1) = n - zbasis 0 + zbasis 1 := by abel
    have p3 : n - (-zbasis 0 + zbasis 1) = n + zbasis 0 - zbasis 1 := by abel
    have p4 : n - (-zbasis 0 - zbasis 1) = n + zbasis 0 + zbasis 1 := by abel
    rw [p1, p2, p3, p4, sub_neg_eq_add, sub_neg_eq_add]
    ring

theorem kconv_ninePointStep (u : Zd 2 → ℝ) (n : Zd 2) :
    kconv u ninePointStep n =
      1 / 5 * (u (n + zbasis 0) + u (n - zbasis 0) + u (n + zbasis 1) + u (n - zbasis 1)) +
        1 / 20 * (u (n + zbasis 0 + zbasis 1) + u (n + zbasis 0 - zbasis 1) +
          u (n - zbasis 0 + zbasis 1) + u (n - zbasis 0 - zbasis 1)) := by
  rw [kconv_comm]
  exact (hasSum_ninePointStep_mul u n).tsum_eq

/-- **`σ_9` is a probability kernel.** -/
theorem isProbKernel_ninePointStep : IsProbKernel ninePointStep := by
  have hδ : ∀ m : Zd 2, 0 ≤ deltaZ m := isProbKernel_deltaZ.1
  have H := hasSum_ninePointStep_mul (fun _ => 1) 0
  simp only [mul_one] at H
  refine ⟨fun m => ?_, ?_, ?_⟩
  · rw [ninePointStep_eq]
    have := hδ (m - zbasis 0); have := hδ (m - -zbasis 0); have := hδ (m - zbasis 1)
    have := hδ (m - -zbasis 1); have := hδ (m - (zbasis 0 + zbasis 1))
    have := hδ (m - (zbasis 0 - zbasis 1)); have := hδ (m - (-zbasis 0 + zbasis 1))
    have := hδ (m - (-zbasis 0 - zbasis 1))
    positivity
  · exact H.summable
  · rw [H.tsum_eq]
    norm_num

/-- **The nine-point Laplacian through `σ_9`**: `Δ_9 u = (10/3)h⁻²(σ_9 * u - u)`, for every
`u`. -/
theorem ninePointLap_eq_step {h : ℝ} (hh : h ≠ 0) (u : Zd 2 → ℝ) (n : Zd 2) :
    ninePointLap h u n = 10 / 3 / h ^ 2 * (kconv u ninePointStep n - u n) := by
  rw [kconv_ninePointStep]
  simp only [ninePointLap, Fin.sum_univ_two]
  field_simp
  ring

theorem gphase_two (θ : Fin 2 → ℝ) (n : Zd 2) : gphase θ n = n 0 * θ 0 + n 1 * θ 1 := by
  simp [gphase, Fin.sum_univ_two]

/-- **The transfer of `σ_9`**: `σ̂_9(θ) = (2/5)(cos θ₁ + cos θ₂) + (1/5)cos θ₁ cos θ₂`. -/
theorem gridFourier_ninePointStep (θ : Fin 2 → ℝ) :
    gridFourier ninePointStep θ =
      ((2 / 5 * (Real.cos (θ 0) + Real.cos (θ 1)) + 1 / 5 * (Real.cos (θ 0) * Real.cos (θ 1)) :
        ℝ) : ℂ) := by
  set e : Zd 2 → ℂ := fun n => Complex.exp ((gphase θ n : ℂ) * Complex.I) with he
  have hd : ∀ (b : Zd 2) (w : ℝ),
      HasSum (fun n => ((w * deltaZ (n - b) : ℝ) : ℂ) * e n) ((w : ℂ) * e b) := by
    intro b w
    convert hasSum_ite_eq b ((w : ℂ) * e b) using 1
    funext n
    rw [deltaZ_sub_eq]
    split_ifs with hn
    · rw [hn]; push_cast; ring
    · push_cast; ring
  have H := (((((((hd (zbasis 0) (1 / 5)).add (hd (-zbasis 0) (1 / 5))).add
    (hd (zbasis 1) (1 / 5))).add (hd (-zbasis 1) (1 / 5))).add
    (hd (zbasis 0 + zbasis 1) (1 / 20))).add (hd (zbasis 0 - zbasis 1) (1 / 20))).add
    (hd (-zbasis 0 + zbasis 1) (1 / 20))).add (hd (-zbasis 0 - zbasis 1) (1 / 20))
  rw [gridFourier_eq]
  convert H.tsum_eq using 1
  · congr 1
    funext n
    rw [ninePointStep_eq]
    push_cast
    ring
  · simp only [he, gphase_two, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, zbasis00, zbasis01,
      zbasis10, zbasis11]
    push_cast
    simp only [zero_mul, add_zero, zero_add, one_mul, neg_mul, add_mul, Complex.exp_add,
      Complex.cos]
    ring_nf
    simp only [Complex.exp_zero, mul_one]
    ring

/-- `|σ̂_9| ≤ 1` on real phases. -/
theorem abs_ninePointStep_symbol_le (x y : ℝ) :
    |2 / 5 * (Real.cos x + Real.cos y) + 1 / 5 * (Real.cos x * Real.cos y)| ≤ 1 := by
  have h1 := Real.abs_cos_le_one x
  have h2 := Real.abs_cos_le_one y
  have h3 : |Real.cos x * Real.cos y| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ h1 (abs_nonneg _) h2
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **`t²D_9 = (10/3)ν_h(1 - σ̂_9(hω))`.** -/
theorem ninePointSymbol_eq_step {h : ℝ} (hh : h ≠ 0) (t : ℝ) (ω : Fin 2 → ℝ) :
    t ^ 2 * ninePointSymbol h ω = 10 / 3 * (t ^ 2 / h ^ 2) *
      (1 - (2 / 5 * (Real.cos (h * ω 0) + Real.cos (h * ω 1)) +
        1 / 5 * (Real.cos (h * ω 0) * Real.cos (h * ω 1)))) := by
  unfold ninePointSymbol
  field_simp
  ring

theorem ninePointSymbol_nonneg {h : ℝ} (hh : h ≠ 0) (ω : Fin 2 → ℝ) : 0 ≤ ninePointSymbol h ω := by
  have e := ninePointSymbol_eq_step hh 1 ω
  have hb := (abs_le.1 (abs_ninePointStep_symbol_le (h * ω 0) (h * ω 1))).2
  rw [one_pow, one_mul] at e
  rw [e]
  have : 0 ≤ 1 / h ^ 2 := by positivity
  nlinarith

/-! ## The nine-point resolvent -/

theorem ninePointHelmholtz_eq (h t : ℝ) :
    ninePointHelmholtz h t = stepResolvent ninePointStep (10 / 3 * (t ^ 2 / h ^ 2)) := rfl

section NinePoint

variable {h : ℝ} (hh : 0 < h)
include hh

theorem isProbKernel_ninePointHelmholtz {t : ℝ} (ht : 0 < t) :
    IsProbKernel (ninePointHelmholtz h t) := by
  rw [ninePointHelmholtz_eq]
  exact isProbKernel_stepResolvent isProbKernel_ninePointStep (by positivity)

/-- `κ̂^9_t(hω) = (1 + t²D_9(ω))⁻¹`. -/
theorem gridFourier_ninePointHelmholtz {t : ℝ} (ht : 0 < t) (ω : Fin 2 → ℝ) :
    gridFourier (ninePointHelmholtz h t) (h • ω) =
      (((1 + t ^ 2 * ninePointSymbol h ω)⁻¹ : ℝ) : ℂ) := by
  rw [ninePointHelmholtz_eq, gridFourier_stepResolvent isProbKernel_ninePointStep
    (by positivity) (h • ω) (gridFourier_ninePointStep (h • ω))
    (abs_ninePointStep_symbol_le _ _), ninePointSymbol_eq_step hh.ne' t ω]
  simp only [Pi.smul_apply, smul_eq_mul]

/-- `(1 - t²Δ_9)u = (1 + a)u - aσ_9 * u`, `a = (10/3)ν_h`, for every `u`. -/
theorem ninePoint_op_eq (t : ℝ) (u : Zd 2 → ℝ) (n : Zd 2) :
    u n - t ^ 2 * ninePointLap h u n =
      (1 + 10 / 3 * (t ^ 2 / h ^ 2)) * u n -
        10 / 3 * (t ^ 2 / h ^ 2) * kconv u ninePointStep n := by
  rw [ninePointLap_eq_step hh.ne']
  ring

theorem ninePointHelmholtz_eqn {t : ℝ} (ht : 0 < t) (n : Zd 2) :
    ninePointHelmholtz h t n - t ^ 2 * ninePointLap h (ninePointHelmholtz h t) n = deltaZ n := by
  rw [ninePoint_op_eq hh, ninePointHelmholtz_eq]
  exact stepResolvent_eqn isProbKernel_ninePointStep (by positivity) n

theorem ninePoint_bounded_unique {t : ℝ} (ht : 0 < t) (u : Zd 2 → ℝ)
    (hu : ∃ C : ℝ, ∀ n, |u n| ≤ C) (hue : ∀ n, u n - t ^ 2 * ninePointLap h u n = deltaZ n) :
    u = ninePointHelmholtz h t := by
  have hK := (isProbKernel_ninePointHelmholtz hh ht).2.1
  obtain ⟨C1, hC1⟩ := hu
  obtain ⟨C2, hC2⟩ := bounded_of_summable_Z hK
  have hz := stepResolvent_unique isProbKernel_ninePointStep
    (show 0 < 10 / 3 * (t ^ 2 / h ^ 2) by positivity) (e := fun n => u n - ninePointHelmholtz h t n)
    ⟨C1 + C2, fun n => (abs_sub _ _).trans (add_le_add (hC1 n) (hC2 n))⟩ fun n => by
      have e1 := ninePoint_op_eq hh t (fun n => u n - ninePointHelmholtz h t n) n
      have hlap : ninePointLap h (fun n => u n - ninePointHelmholtz h t n) n =
          ninePointLap h u n - ninePointLap h (ninePointHelmholtz h t) n := by
        simp only [ninePointLap, Fin.sum_univ_two]; ring
      rw [hlap] at e1
      have h1 := hue n
      have h2 := ninePointHelmholtz_eqn hh ht n
      linarith
  funext n
  have := congrFun hz n
  simp only [Pi.zero_apply] at this
  linarith

end NinePoint

/-- **`prop:nine-point-family`(1).** `0 < p < 1`; `κ^9_t` is a probability kernel on `ℤ²` with
`κ̂^9_t(hω) = (1 + t²D_9(ω))⁻¹`; it solves `(1 - t²Δ_9)κ^9_t = δ₀`, and it is the unique bounded
solution, in particular the unique summable one. -/
theorem nine_point_family_1 {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    (0 < ninePointP h t ∧ ninePointP h t < 1) ∧
      IsProbKernel (ninePointHelmholtz h t) ∧
      (∀ ω : Fin 2 → ℝ, gridFourier (ninePointHelmholtz h t) (h • ω) =
        (((1 + t ^ 2 * ninePointSymbol h ω)⁻¹ : ℝ) : ℂ)) ∧
      (∀ n : Zd 2, ninePointHelmholtz h t n - t ^ 2 * ninePointLap h (ninePointHelmholtz h t) n =
        deltaZ n) ∧
      (∀ u : Zd 2 → ℝ, (∃ C : ℝ, ∀ n, |u n| ≤ C) →
        (∀ n, u n - t ^ 2 * ninePointLap h u n = deltaZ n) → u = ninePointHelmholtz h t) ∧
      ∀ u : Zd 2 → ℝ, Summable u →
        (∀ n, u n - t ^ 2 * ninePointLap h u n = deltaZ n) → u = ninePointHelmholtz h t := by
  have ha : 0 < 10 / 3 * (t ^ 2 / h ^ 2) := by positivity
  exact ⟨⟨stepP_pos ha, stepP_lt_one ha⟩, isProbKernel_ninePointHelmholtz hh ht,
    gridFourier_ninePointHelmholtz hh ht, ninePointHelmholtz_eqn hh ht,
    ninePoint_bounded_unique hh ht,
    fun u hu hue => ninePoint_bounded_unique hh ht u (bounded_of_summable_Z hu) hue⟩

/-! ## The cascade -/

section Cascade

variable {h : ℝ} (hh : 0 < h)
include hh

/-- The resolvent identity `κ^9_s * κ^9_t = (t²κ^9_t - s²κ^9_s)/(t² - s²)`, `0 < s < t`. -/
theorem ninePoint_resolvent {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    kconv (ninePointHelmholtz h s) (ninePointHelmholtz h t) =
      fun n => (t ^ 2 * ninePointHelmholtz h t n - s ^ 2 * ninePointHelmholtz h s n) /
        (t ^ 2 - s ^ 2) := by
  have ht : 0 < t := hs.trans hst
  have hts : t ^ 2 - s ^ 2 ≠ 0 := by nlinarith
  have hne : 10 / 3 * (t ^ 2 / h ^ 2) ≠ 10 / 3 * (s ^ 2 / h ^ 2) := by
    intro heq
    have hh2 : h ^ 2 ≠ 0 := by positivity
    field_simp at heq
    exact hts (by linarith)
  rw [ninePointHelmholtz_eq, ninePointHelmholtz_eq,
    stepResolvent_resolvent isProbKernel_ninePointStep (by positivity) (by positivity) hne]
  funext n
  have hh2 : h ^ 2 ≠ 0 := by positivity
  have hd : 10 / 3 * (t ^ 2 / h ^ 2) - 10 / 3 * (s ^ 2 / h ^ 2) ≠ 0 := sub_ne_zero.2 hne
  field_simp

/-- The one-step mixture `(s²/t²)δ₀ + (1 - s²/t²)κ^9_t`. -/
noncomputable def nineMix (h s t : ℝ) (n : Zd 2) : ℝ :=
  s ^ 2 / t ^ 2 * deltaZ n + (1 - s ^ 2 / t ^ 2) * ninePointHelmholtz h t n

omit hh in
theorem ninePointIncrement_eq (γ : ℕ) (s t : ℝ) :
    ninePointIncrement h γ s t = kpow (nineMix h s t) γ := rfl

theorem isProbKernel_nineMix {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    IsProbKernel (nineMix h s t) := by
  have ht : 0 < t := lt_of_le_of_lt hs hst
  have hK := isProbKernel_ninePointHelmholtz hh ht
  have hq0 : 0 ≤ s ^ 2 / t ^ 2 := by positivity
  have hq1 : s ^ 2 / t ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; exact pow_lt_pow_left₀ hst hs two_ne_zero
  refine ⟨fun n => ?_, (summable_deltaZ.mul_left _).add (hK.2.1.mul_left _), ?_⟩
  · unfold nineMix
    exact add_nonneg (mul_nonneg hq0 (isProbKernel_deltaZ.1 n)) (mul_nonneg (by linarith) (hK.1 n))
  · unfold nineMix
    rw [(summable_deltaZ.mul_left _).tsum_add (hK.2.1.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_deltaZ, hK.2.2]
    ring

theorem summable_nineMix {s t : ℝ} (ht : 0 < t) : Summable (nineMix h s t) :=
  (summable_deltaZ.mul_left _).add ((isProbKernel_ninePointHelmholtz hh ht).2.1.mul_left _)

/-- The mixtures compose: `μ_{s,t} * μ_{r,s} = μ_{r,t}` for `0 ≤ r < s < t`. -/
theorem nineMix_kconv {r s t : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) :
    kconv (nineMix h s t) (nineMix h r s) = nineMix h r t := by
  have hs : 0 < s := lt_of_le_of_lt hr hrs
  have ht : 0 < t := hs.trans hst
  have hKs := (isProbKernel_ninePointHelmholtz hh hs).2.1
  have hKt := (isProbKernel_ninePointHelmholtz hh ht).2.1
  have hres := ninePoint_resolvent hh hs hst
  have hts : t ^ 2 - s ^ 2 ≠ 0 := by nlinarith
  have hs2 : s ^ 2 ≠ 0 := by positivity
  have ht2 : t ^ 2 ≠ 0 := by positivity
  rw [show nineMix h s t = fun n => s ^ 2 / t ^ 2 * deltaZ n +
    (1 - s ^ 2 / t ^ 2) * ninePointHelmholtz h t n from rfl,
    kconv_add_smul_left summable_deltaZ hKt (summable_nineMix hh hs)]
  funext n
  rw [kconv_deltaZ_left, show nineMix h r s = fun n => r ^ 2 / s ^ 2 * deltaZ n +
    (1 - r ^ 2 / s ^ 2) * ninePointHelmholtz h s n from rfl,
    kconv_add_smul_right hKt summable_deltaZ hKs, kconv_deltaZ_right,
    kconv_comm (ninePointHelmholtz h t), hres]
  simp only [nineMix]
  field_simp
  ring

theorem gridFourier_nineMix {s t : ℝ} (ht : 0 < t) (ω : Fin 2 → ℝ) :
    gridFourier (nineMix h s t) (h • ω) =
      (((1 + s ^ 2 * ninePointSymbol h ω) / (1 + t ^ 2 * ninePointSymbol h ω) : ℝ) : ℂ) := by
  have hK := (isProbKernel_ninePointHelmholtz hh ht).2.1
  unfold nineMix
  rw [gridFourier_add_smul summable_deltaZ hK, gridFourier_deltaZ,
    gridFourier_ninePointHelmholtz hh ht]
  have hD := ninePointSymbol_nonneg hh.ne' ω
  have h1 : (1 : ℝ) + t ^ 2 * ninePointSymbol h ω ≠ 0 := by positivity
  have ht2 : t ^ 2 ≠ 0 := by positivity
  push_cast
  have h1' : (1 : ℂ) + (t : ℂ) ^ 2 * (ninePointSymbol h ω : ℂ) ≠ 0 := by exact_mod_cast h1
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  ring

end Cascade

/-- **`prop:nine-point-family`(2), the cascade.** For an integer `γ ≥ 1`: `Λ^9_t` has transfer
`(1 + t²D_9)^{-γ}`; for `0 ≤ s < t` the mixture `(s²/t²)δ₀ + (1 - s²/t²)κ^9_t` and its `γ`-fold
power `Λ^9_{s,t}` are probability kernels, with transfer `((1 + s²D_9)/(1 + t²D_9))^γ`;
`Λ^9_{0,t} = Λ^9_t`; and `Λ^9_{r,t} = Λ^9_{s,t} * Λ^9_{r,s}` for `0 ≤ r < s < t`. -/
theorem nine_point_family_2 {h : ℝ} (hh : 0 < h) (γ : ℕ) :
    (∀ t : ℝ, 0 < t → ∀ ω : Fin 2 → ℝ, gridFourier (ninePointFamily h t γ) (h • ω) =
        ((((1 + t ^ 2 * ninePointSymbol h ω) ^ γ)⁻¹ : ℝ) : ℂ)) ∧
      (∀ s t : ℝ, 0 ≤ s → s < t →
        IsProbKernel (fun n => s ^ 2 / t ^ 2 * deltaZ n +
          (1 - s ^ 2 / t ^ 2) * ninePointHelmholtz h t n) ∧
        IsProbKernel (ninePointIncrement h γ s t) ∧
        ∀ ω : Fin 2 → ℝ, gridFourier (ninePointIncrement h γ s t) (h • ω) =
          ((((1 + s ^ 2 * ninePointSymbol h ω) / (1 + t ^ 2 * ninePointSymbol h ω)) ^ γ : ℝ) : ℂ)) ∧
      (∀ t : ℝ, 0 < t → ninePointIncrement h γ 0 t = ninePointFamily h t γ) ∧
      ∀ r s t : ℝ, 0 ≤ r → r < s → s < t →
        ninePointIncrement h γ r t =
          kconv (ninePointIncrement h γ s t) (ninePointIncrement h γ r s) := by
  refine ⟨fun t ht ω => ?_, fun s t hs hst => ⟨isProbKernel_nineMix hh hs hst,
    isProbKernel_kpow (isProbKernel_nineMix hh hs hst) γ, fun ω => ?_⟩, fun t ht => ?_,
    fun r s t hr hrs hst => ?_⟩
  · rw [ninePointFamily, gridFourier_kpow (isProbKernel_ninePointHelmholtz hh ht).2.1,
      gridFourier_ninePointHelmholtz hh ht]
    push_cast
    rw [inv_pow]
  · have ht : 0 < t := lt_of_le_of_lt hs hst
    rw [ninePointIncrement_eq, gridFourier_kpow (summable_nineMix hh ht),
      gridFourier_nineMix hh ht]
    push_cast
    ring
  · rw [ninePointIncrement_eq, ninePointFamily]
    congr 1
    funext n
    simp [nineMix]
  · have hs : 0 < s := lt_of_le_of_lt hr hrs
    have ht : 0 < t := hs.trans hst
    rw [ninePointIncrement_eq, ninePointIncrement_eq, ninePointIncrement_eq,
      kpow_kconv (summable_nineMix hh ht) (summable_nineMix hh hs),
      nineMix_kconv hh hr hrs hst]

/-! ## Invariance -/

/-- `σ_9` in coordinates: `1/5` where `|n₁| + |n₂| = 1`, `1/20` where `|n₁| = |n₂| = 1`. -/
noncomputable def nineCoord (x y : ℤ) : ℝ :=
  (if ((x = 1 ∨ x = -1) ∧ y = 0) ∨ (x = 0 ∧ (y = 1 ∨ y = -1)) then 1 / 5 else 0) +
    (if (x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1) then 1 / 20 else 0)

theorem ninePointStep_coord (n : Zd 2) : ninePointStep n = nineCoord (n 0) (n 1) := by
  simp only [ninePointStep, nineCoord, Fin.sum_univ_two, zd2_eq_iff, Pi.neg_apply, Pi.add_apply,
    Pi.sub_apply, zbasis00, zbasis01, zbasis10, zbasis11]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

theorem nineCoord_neg_left (x y : ℤ) : nineCoord (-x) y = nineCoord x y := by
  unfold nineCoord
  split_ifs <;> first | rfl | (norm_num; done) | (exfalso; omega)

theorem nineCoord_neg_right (x y : ℤ) : nineCoord x (-y) = nineCoord x y := by
  unfold nineCoord
  split_ifs <;> first | rfl | (norm_num; done) | (exfalso; omega)

theorem nineCoord_swap (x y : ℤ) : nineCoord y x = nineCoord x y := by
  unfold nineCoord
  split_ifs <;> first | rfl | (norm_num; done) | (exfalso; omega)

theorem nineCoord_sign (e x y : ℤ) (he : e = 1 ∨ e = -1) :
    nineCoord (e * x) y = nineCoord x y ∧ nineCoord x (e * y) = nineCoord x y := by
  rcases he with rfl | rfl
  · simp
  · simp only [neg_mul, one_mul]; exact ⟨nineCoord_neg_left x y, nineCoord_neg_right x y⟩

/-- **`σ_9` is invariant under the signed permutations.** -/
theorem ninePointStep_invariant (σ : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (n : Zd 2) :
    ninePointStep (gmap σ ε n) = ninePointStep n := by
  rw [ninePointStep_coord, ninePointStep_coord]
  simp only [gmap]
  rw [(nineCoord_sign _ _ _ (hε 0)).1, (nineCoord_sign _ _ _ (hε 1)).2]
  have key : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
  rcases key (σ 0) with h0 | h0
  · have h1 : σ 1 = 1 := by
      rcases key (σ 1) with h1 | h1
      · exact absurd (σ.injective (h0.trans h1.symm)) (by decide)
      · exact h1
    rw [h0, h1]
  · have h1 : σ 1 = 0 := by
      rcases key (σ 1) with h1 | h1
      · exact h1
      · exact absurd (σ.injective (h0.trans h1.symm)) (by decide)
    rw [h0, h1, nineCoord_swap]

theorem stepResolvent_invariant {d : ℕ} (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) {τ : Zd d → ℝ} (hτ : ∀ n, τ (gmap σ ε n) = τ n) (a : ℝ)
    (n : Zd d) : stepResolvent τ a (gmap σ ε n) = stepResolvent τ a n := by
  unfold stepResolvent
  simp_rw [kpow_invariant σ ε hε hτ]

theorem ninePointHelmholtz_invariant (σ : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (h t : ℝ) (n : Zd 2) :
    ninePointHelmholtz h t (gmap σ ε n) = ninePointHelmholtz h t n := by
  rw [ninePointHelmholtz_eq]
  exact stepResolvent_invariant σ ε hε (ninePointStep_invariant σ ε hε) _ n

/-- **`prop:nine-point-family`(2), invariance.** Convolution with each member and each increment
commutes with the translations of `ℤ²`, and the members and increments are invariant under the
signed permutations `n ↦ (εᵢ n_{σ(i)})ᵢ`. -/
theorem nine_point_family_2_invariance {h : ℝ} (γ : ℕ) :
    (∀ t : ℝ, 0 < t → ∀ (u : Zd 2 → ℝ) (a n : Zd 2),
        kconv (ninePointFamily h t γ) (fun m => u (m - a)) n =
          kconv (ninePointFamily h t γ) u (n - a)) ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → ∀ (u : Zd 2 → ℝ) (a n : Zd 2),
        kconv (ninePointIncrement h γ s t) (fun m => u (m - a)) n =
          kconv (ninePointIncrement h γ s t) u (n - a)) ∧
      (∀ t : ℝ, 0 < t → ∀ (σ : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℤ), (∀ i, ε i = 1 ∨ ε i = -1) →
        ∀ n : Zd 2, ninePointFamily h t γ (fun i => ε i * n (σ i)) = ninePointFamily h t γ n) ∧
      ∀ s t : ℝ, 0 ≤ s → s < t → ∀ (σ : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℤ),
        (∀ i, ε i = 1 ∨ ε i = -1) → ∀ n : Zd 2,
          ninePointIncrement h γ s t (fun i => ε i * n (σ i)) = ninePointIncrement h γ s t n := by
  refine ⟨fun t _ u a n => ?_, fun s t _ _ u a n => ?_, fun t _ σ ε hε n => ?_,
    fun s t _ _ σ ε hε n => ?_⟩
  · unfold kconv
    congr 1
    funext m
    rw [sub_right_comm]
  · unfold kconv
    congr 1
    funext m
    rw [sub_right_comm]
  · exact kpow_invariant σ ε hε (ninePointHelmholtz_invariant σ ε hε h t) γ n
  · refine kpow_invariant σ ε hε (fun m => ?_) γ n
    rw [deltaZ_invariant σ ε hε, ninePointHelmholtz_invariant σ ε hε]

end Pyramids
