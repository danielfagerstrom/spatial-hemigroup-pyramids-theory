/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# `prop:creation-plane`(3): exponentials of tempered exponents, and the Matérn series

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:creation-plane`. Phase 5, wave 3b (on the
VM). The analytic input of clause (3).

* **`e^Ψ` for a tempered exponent `Ψ`.** By Faà di Bruno's bound (`norm_iteratedFDeriv_comp_le`),
  `‖Dⁿ e^Ψ‖ ≤ n! e^Ψ Dⁿ` once `‖DⁱΨ‖ ≤ D` for `1 ≤ i ≤ n`. So `e^Ψ` has temperate growth when `Ψ`
  has and is bounded above, and is a Schwartz function when `Ψ ≤ A - κ|x|²`, `κ > 0`.
* **The series `S(x) = ∑ᵢ log(1 + βᵢ|x|²)`**, `βᵢ = b q^{-2(i+1)}`. At a point `x₀`, with
  `Q₀ = β|x₀|²`, `log(1 + β|x|²) = log(1 + Q₀) + log f(x)`, `f(x) = (1 + β|x|²)/(1 + Q₀)`, and
  `f(x₀) = 1`, `‖Df(x₀)‖ ≤ √β`, `‖D²f‖ ≤ 2β`, `D³f = 0`. Faà di Bruno with `log` on `(0, ∞)`
  gives `‖Dⁿ log(1 + β|x|²)‖ ≤ (n!)² (2β)^{n/2}` for `n ≥ 1`, uniformly in `x`. The derivative of
  `S` is the series of derivatives, with summable uniform bounds of every order, so `S` has
  temperate growth (`HasTemperateGrowth.of_fderiv`). And `S(x) ≤ ε|x|² + A_ε` for every `ε > 0`:
  the first `N` terms are at most `2√β|x|` each, the rest at most `βᵢ|x|²`.
-/

set_option autoImplicit false

namespace Pyramids

open Set Filter
open scoped Nat Topology ContDiff

section ExpTempered

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_exp_le (y : ℝ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

/-- **Faà di Bruno for `e^Ψ`.** -/
theorem norm_iteratedFDeriv_exp_comp_le {Ψ : E → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) {n k : ℕ} {B : ℝ}
    (hB : 1 ≤ B) (hD : ∀ i, 1 ≤ i → i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i Ψ x‖ ≤ B * (1 + ‖x‖) ^ k)
    (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => Real.exp (Ψ y)) x‖ ≤
      n ! * Real.exp (Ψ x) * (B * (1 + ‖x‖) ^ k) ^ n := by
  have h1 : 1 ≤ B * (1 + ‖x‖) ^ k :=
    one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ (by linarith [norm_nonneg x]))
  exact norm_iteratedFDeriv_comp_le (g := Real.exp) (f := Ψ) Real.contDiff_exp hΨ
    (by exact_mod_cast le_top) x (fun i _ => (norm_iteratedFDeriv_exp_le _ i).le)
    (fun i hi hin => (hD i hi hin x).trans (le_self_pow₀ h1 (by omega)))

/-- The derivatives of a tempered `Ψ`, of order at most `n`, under one `B ≥ 1`. -/
theorem hasTemperateGrowth_exists_bound {Ψ : E → ℝ} (hΨ : Function.HasTemperateGrowth Ψ) (n : ℕ) :
    ∃ (k : ℕ) (B : ℝ), 1 ≤ B ∧ ∀ i, i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i Ψ x‖ ≤ B * (1 + ‖x‖) ^ k := by
  obtain ⟨k, C, hC, h⟩ := hΨ.norm_iteratedFDeriv_le_uniform n
  refine ⟨k, max C 1, le_max_right _ _, fun i hi x => (h i hi x).trans ?_⟩
  gcongr
  exact le_max_left _ _

/-- **`e^Ψ` has temperate growth** when `Ψ` has and is bounded above. -/
theorem hasTemperateGrowth_exp_comp {Ψ : E → ℝ} (hΨ : Function.HasTemperateGrowth Ψ) {A : ℝ}
    (hA : ∀ x, Ψ x ≤ A) : Function.HasTemperateGrowth fun x => Real.exp (Ψ x) := by
  refine ⟨Real.contDiff_exp.comp hΨ.1, fun n => ?_⟩
  obtain ⟨k, B, hB, hD⟩ := hasTemperateGrowth_exists_bound hΨ n
  refine ⟨k * n, n ! * Real.exp A * B ^ n, fun x => ?_⟩
  refine (norm_iteratedFDeriv_exp_comp_le hΨ.1 hB (fun i _ hi => hD i hi) x).trans ?_
  rw [mul_pow, ← pow_mul, ← mul_assoc]
  gcongr
  exact hA x

/-- `(1 + r)^p e^{-κr²}` is bounded on `r ≥ 0`. -/
theorem exists_one_add_pow_mul_exp_le {κ : ℝ} (hκ : 0 < κ) (p : ℕ) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ p * Real.exp (-(κ * r ^ 2)) ≤ C := by
  refine ⟨p ! * Real.exp (1 + 1 / (4 * κ)), fun r hr => ?_⟩
  have h1 : (1 + r) ^ p ≤ p ! * Real.exp (1 + r) := by
    have := Real.pow_div_factorial_le_exp (x := 1 + r) (by linarith) p
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : 1 + r + -(κ * r ^ 2) ≤ 1 + 1 / (4 * κ) := by
    have : r - κ * r ^ 2 ≤ 1 / (4 * κ) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * κ * r - 1)]
    linarith
  calc (1 + r) ^ p * Real.exp (-(κ * r ^ 2))
      ≤ p ! * Real.exp (1 + r) * Real.exp (-(κ * r ^ 2)) := by gcongr
    _ = p ! * Real.exp (1 + r + -(κ * r ^ 2)) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ p ! * Real.exp (1 + 1 / (4 * κ)) := by gcongr

/-- **`e^Ψ` is a Schwartz function** when `Ψ` is tempered and `Ψ ≤ A - κ|x|²`, `κ > 0`. -/
theorem exists_schwartz_exp {Ψ : E → ℝ} (hΨ : Function.HasTemperateGrowth Ψ) {A κ : ℝ}
    (hκ : 0 < κ) (hA : ∀ x, Ψ x ≤ A - κ * ‖x‖ ^ 2) :
    ∃ f : SchwartzMap E ℝ, ∀ x, f x = Real.exp (Ψ x) := by
  refine ⟨⟨fun x => Real.exp (Ψ x), Real.contDiff_exp.comp hΨ.1, fun m n => ?_⟩, fun _ => rfl⟩
  obtain ⟨k, B, hB, hD⟩ := hasTemperateGrowth_exists_bound hΨ n
  obtain ⟨C, hC⟩ := exists_one_add_pow_mul_exp_le hκ (m + k * n)
  refine ⟨n ! * Real.exp A * B ^ n * C, fun x => ?_⟩
  have hx : ‖x‖ ^ m ≤ (1 + ‖x‖) ^ m := pow_le_pow_left₀ (norm_nonneg x) (by linarith) m
  have he : Real.exp (Ψ x) ≤ Real.exp A * Real.exp (-(κ * ‖x‖ ^ 2)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [hA x])
  calc ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (fun y => Real.exp (Ψ y)) x‖
      ≤ (1 + ‖x‖) ^ m * (n ! * (Real.exp A * Real.exp (-(κ * ‖x‖ ^ 2))) *
          (B * (1 + ‖x‖) ^ k) ^ n) := by
        gcongr
        exact (norm_iteratedFDeriv_exp_comp_le hΨ.1 hB (fun i _ hi => hD i hi) x).trans
          (by gcongr)
    _ = n ! * Real.exp A * B ^ n *
          ((1 + ‖x‖) ^ (m + k * n) * Real.exp (-(κ * ‖x‖ ^ 2))) := by
        rw [mul_pow, ← pow_mul, pow_add]
        ring
    _ ≤ n ! * Real.exp A * B ^ n * C := by
        gcongr
        exact hC _ (norm_nonneg x)

end ExpTempered

section LogTerm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- `‖Dⁿ⁺¹ (c + g)‖ = ‖Dⁿ⁺¹ g‖`. -/
theorem norm_iteratedFDeriv_succ_const_add (c : ℝ) (g : F → ℝ) (m : ℕ) (x : F) :
    ‖iteratedFDeriv ℝ (m + 1) (fun y => c + g y) x‖ = ‖iteratedFDeriv ℝ (m + 1) g x‖ := by
  rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv,
    show (fderiv ℝ fun y => c + g y) = fderiv ℝ g from
      funext fun y => fderiv_const_add (𝕜 := ℝ) (f := g) c]

/-- The real inner product as a continuous bilinear map. -/
noncomputable def innerRL : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ

theorem fderiv_normSq :
    fderiv ℝ (fun y : F => ‖y‖ ^ 2) = fun y => ((2 : ℝ) • (innerRL (F := F))) y := by
  funext y
  rw [fderiv_norm_sq_apply]
  ext v
  simp only [innerRL, _root_.smul_apply, smul_eq_mul, two_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  rfl

theorem norm_iteratedFDeriv_normSq_one (x : F) :
    ‖iteratedFDeriv ℝ 1 (fun y : F => ‖y‖ ^ 2) x‖ = 2 * ‖x‖ := by
  have h : ‖innerRL (F := F) x‖ = ‖x‖ := innerSL_apply_norm (𝕜 := ℝ) x
  have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0) (f := fun y : F => ‖y‖ ^ 2) (x := x)
  rw [zero_add] at h1
  rw [← h1, norm_iteratedFDeriv_zero, fderiv_normSq]
  simp only [_root_.smul_apply]
  rw [norm_smul, h, Real.norm_two]

theorem fderiv_fderiv_normSq :
    fderiv ℝ (fderiv ℝ fun y : F => ‖y‖ ^ 2) = fun _ => (2 : ℝ) • innerRL (F := F) := by
  rw [fderiv_normSq]
  funext y
  exact ContinuousLinearMap.fderiv _

theorem norm_iteratedFDeriv_normSq_two (x : F) :
    ‖iteratedFDeriv ℝ 2 (fun y : F => ‖y‖ ^ 2) x‖ ≤ 2 := by
  rw [show 2 = 0 + 1 + 1 by rfl, ← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv,
    norm_iteratedFDeriv_zero, fderiv_fderiv_normSq, norm_smul]
  have : ‖innerRL (F := F)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
      rw [show ‖innerRL (F := F) y‖ = ‖y‖ from innerSL_apply_norm (𝕜 := ℝ) y, one_mul]
  rw [Real.norm_two]
  linarith

theorem iteratedFDeriv_normSq_eq_zero (k : ℕ) (x : F) :
    ‖iteratedFDeriv ℝ (k + 3) (fun y : F => ‖y‖ ^ 2) x‖ = 0 := by
  rw [show k + 3 = k + 1 + 1 + 1 by ring, ← norm_iteratedFDeriv_fderiv,
    ← norm_iteratedFDeriv_fderiv, fderiv_fderiv_normSq, iteratedFDeriv_const_of_ne (by omega),
    Pi.zero_apply, norm_zero]

/-- **The uniform bound**: `‖Dⁿ log(1 + β|x|²)‖ ≤ (n!)² (2β)^{n/2}` for `n ≥ 1`. -/
theorem norm_iteratedFDeriv_logTerm_le {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hn : 1 ≤ n) (x₀ : F) :
    ‖iteratedFDeriv ℝ n (fun x : F => Real.log (1 + β * ‖x‖ ^ 2)) x₀‖ ≤
      n ! * n ! * Real.sqrt (2 * β) ^ n := by
  set P : ℝ := 1 + β * ‖x₀‖ ^ 2 with hP
  have hP0 : 0 < P := by positivity
  set f : F → ℝ := fun x => P⁻¹ + β * P⁻¹ * ‖x‖ ^ 2 with hf
  have hfpos : ∀ x, 0 < f x := fun x => by simp only [hf]; positivity
  have hfx0 : f x₀ = 1 := by
    simp only [hf]; field_simp; exact hP.symm
  have hlog : (fun x : F => Real.log (1 + β * ‖x‖ ^ 2)) = fun x => Real.log P + Real.log (f x) := by
    funext x
    rw [← Real.log_mul hP0.ne' (hfpos x).ne']
    congr 1
    simp only [hf]; field_simp
  have hfc : ContDiff ℝ ∞ f := contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hlog, norm_iteratedFDeriv_succ_const_add]
  have hsq : Real.sqrt β ≤ Real.sqrt (2 * β) := Real.sqrt_le_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt (2 * β) := Real.sqrt_nonneg _
  -- the derivatives of `f` at `x₀`
  have hDf : ∀ i, 1 ≤ i → i ≤ m + 1 → ‖iteratedFDeriv ℝ i f x₀‖ ≤ Real.sqrt (2 * β) ^ i := by
    intro i hi _
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hf, norm_iteratedFDeriv_succ_const_add]
    have hQ : ContDiffAt ℝ (j + 1) (fun y : F => ‖y‖ ^ 2) x₀ := (contDiff_norm_sq ℝ).contDiffAt
    rw [show (fun y : F => β * P⁻¹ * ‖y‖ ^ 2) = fun y => (β * P⁻¹) • ‖y‖ ^ 2 from rfl,
      iteratedFDeriv_const_smul_apply' hQ, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    obtain rfl | rfl | ⟨k, rfl⟩ : j = 0 ∨ j = 1 ∨ ∃ k, j = k + 2 := by
      rcases j with _ | _ | k
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨k, rfl⟩)
    · change β * P⁻¹ * ‖iteratedFDeriv ℝ 1 (fun y : F => ‖y‖ ^ 2) x₀‖ ≤ Real.sqrt (2 * β) ^ 1
      rw [norm_iteratedFDeriv_normSq_one, pow_one]
      refine le_trans ?_ hsq
      rw [← div_eq_mul_inv, div_mul_eq_mul_div, div_le_iff₀ hP0]
      have hb := Real.sq_sqrt hβ
      have := Real.sqrt_nonneg β
      have key : 0 ≤ Real.sqrt β * (Real.sqrt β * ‖x₀‖ - 1) ^ 2 :=
        mul_nonneg this (sq_nonneg _)
      have e : Real.sqrt β * P - β * (2 * ‖x₀‖) = Real.sqrt β * (Real.sqrt β * ‖x₀‖ - 1) ^ 2 := by
        rw [hP]; linear_combination (2 * ‖x₀‖ - Real.sqrt β * ‖x₀‖ ^ 2) * hb
      linarith
    · change β * P⁻¹ * ‖iteratedFDeriv ℝ 2 (fun y : F => ‖y‖ ^ 2) x₀‖ ≤ Real.sqrt (2 * β) ^ 2
      rw [Real.sq_sqrt (by linarith)]
      have h2 := norm_iteratedFDeriv_normSq_two x₀
      have hPi : P⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by simp only [hP]; nlinarith [sq_nonneg ‖x₀‖])
      calc β * P⁻¹ * ‖iteratedFDeriv ℝ 2 (fun y : F => ‖y‖ ^ 2) x₀‖
          ≤ β * 1 * 2 := by gcongr
        _ = 2 * β := by ring
    · change β * P⁻¹ * ‖iteratedFDeriv ℝ (k + 3) (fun y : F => ‖y‖ ^ 2) x₀‖ ≤ _
      rw [iteratedFDeriv_normSq_eq_zero, mul_zero]
      positivity
  -- the derivatives of `log` at `1`
  have hC : ∀ i, i ≤ m + 1 →
      ‖iteratedFDerivWithin ℝ i Real.log (Ioi 0) (f x₀)‖ ≤ (m + 1) ! := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi (show f x₀ ∈ Ioi (0 : ℝ) from hfpos x₀),
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, hfx0]
    rcases i with _ | j
    · simp
    · rw [Function.iterate_succ_apply, Real.deriv_log', iter_deriv_inv, one_zpow, mul_one,
        norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
      exact_mod_cast Nat.factorial_le (by omega)
  have := norm_iteratedFDeriv_comp_le' (g := Real.log) (f := f) (n := m + 1) (N := ∞)
    (t := Ioi 0) (by rintro _ ⟨x, rfl⟩; exact hfpos x) isOpen_Ioi.uniqueDiffOn
    (Real.contDiffOn_log.mono fun y (hy : 0 < y) => hy.ne') hfc (by exact_mod_cast le_top) x₀ hC
    hDf
  exact this

/-- `log(1 + y) ≤ 2√y` for `y ≥ 0`. -/
theorem log_one_add_le_two_sqrt {y : ℝ} (hy : 0 ≤ y) : Real.log (1 + y) ≤ 2 * Real.sqrt y := by
  rw [Real.log_le_iff_le_exp (by linarith),
    show 2 * Real.sqrt y = Real.sqrt y + Real.sqrt y by ring,
    Real.exp_add]
  have h := Real.add_one_le_exp (Real.sqrt y)
  have h0 := Real.sqrt_nonneg y
  have hs := Real.sq_sqrt hy
  nlinarith

/-! ### The series `S(x) = ∑ᵢ log(1 + b q^{-2(i+1)} |x|²)` -/

/-- The coefficients `βᵢ = b q^{-2(i+1)}`. -/
noncomputable def lsCoeff (q b : ℝ) (i : ℕ) : ℝ := b / q ^ (2 * (i + 1))

/-- **The series** `S(x) = ∑ᵢ log(1 + βᵢ|x|²)`. -/
noncomputable def logSeries (q b : ℝ) (x : F) : ℝ :=
  ∑' i : ℕ, Real.log (1 + lsCoeff q b i * ‖x‖ ^ 2)

variable {q b : ℝ}

theorem lsCoeff_nonneg (hq : 1 < q) (hb : 0 ≤ b) (i : ℕ) : 0 ≤ lsCoeff q b i := by
  unfold lsCoeff; have : 0 < q := by linarith
  positivity

theorem lsCoeff_le (hq : 1 < q) (hb : 0 ≤ b) (i : ℕ) : lsCoeff q b i ≤ b :=
  div_le_self hb (one_le_pow₀ hq.le)

theorem lsCoeff_eq (i : ℕ) : lsCoeff q b i = b * (q⁻¹ ^ 2) ^ (i + 1) := by
  unfold lsCoeff
  rw [← pow_mul, inv_pow, div_eq_mul_inv]

theorem summable_lsCoeff (hq : 1 < q) : Summable (lsCoeff q b) := by
  have h1 : q⁻¹ ^ 2 < 1 := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hq) two_ne_zero
  have e : lsCoeff q b = fun i => b * q⁻¹ ^ 2 * (q⁻¹ ^ 2) ^ i := funext fun i => by
    rw [lsCoeff_eq, pow_succ]; ring
  rw [e]
  exact (summable_geometric_of_lt_one (by positivity) h1).mul_left _

theorem sqrt_two_lsCoeff (hq : 1 < q) (hb : 0 ≤ b) (i : ℕ) :
    Real.sqrt (2 * lsCoeff q b i) = Real.sqrt (2 * b) * q⁻¹ ^ (i + 1) := by
  have hq0 : 0 < q := by linarith
  rw [lsCoeff_eq, ← mul_assoc, ← pow_mul, Real.sqrt_mul (by positivity),
    show 2 * (i + 1) = (i + 1) * 2 by ring, pow_mul, Real.sqrt_sq (by positivity)]

theorem summable_sqrt_pow (hq : 1 < q) (hb : 0 ≤ b) (n : ℕ) (hn : 1 ≤ n) (K : ℝ) :
    Summable fun i => K * Real.sqrt (2 * lsCoeff q b i) ^ n := by
  have h1 : q⁻¹ ^ n < 1 := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hq) (by omega)
  simp_rw [sqrt_two_lsCoeff hq hb, mul_pow, ← pow_mul, show ∀ i, (i + 1) * n = n * i + n by
    intro i; ring, pow_add, pow_mul]
  exact (((summable_geometric_of_lt_one (by positivity) h1).mul_right _).mul_left _).mul_left K

omit [InnerProductSpace ℝ F] in
theorem logTerm_nonneg (hq : 1 < q) (hb : 0 ≤ b) (i : ℕ) (x : F) :
    0 ≤ Real.log (1 + lsCoeff q b i * ‖x‖ ^ 2) :=
  Real.log_nonneg (by have := lsCoeff_nonneg hq hb i; nlinarith [sq_nonneg ‖x‖])

omit [InnerProductSpace ℝ F] in
theorem logTerm_le (hq : 1 < q) (hb : 0 ≤ b) (i : ℕ) (x : F) :
    Real.log (1 + lsCoeff q b i * ‖x‖ ^ 2) ≤ lsCoeff q b i * ‖x‖ ^ 2 := by
  have := Real.add_one_le_exp (lsCoeff q b i * ‖x‖ ^ 2)
  rw [Real.log_le_iff_le_exp (by have := lsCoeff_nonneg hq hb i; positivity)]
  linarith

omit [InnerProductSpace ℝ F] in
theorem summable_logTerm (hq : 1 < q) (hb : 0 ≤ b) (x : F) :
    Summable fun i => Real.log (1 + lsCoeff q b i * ‖x‖ ^ 2) :=
  ((summable_lsCoeff hq).mul_right (‖x‖ ^ 2)).of_nonneg_of_le (logTerm_nonneg hq hb · x)
    (logTerm_le hq hb · x)

omit [InnerProductSpace ℝ F] in
theorem logSeries_nonneg (hq : 1 < q) (hb : 0 ≤ b) (x : F) : 0 ≤ logSeries q b x :=
  tsum_nonneg fun i => logTerm_nonneg hq hb i x

/-- **The series has temperate growth.** -/
theorem hasTemperateGrowth_logSeries (hq : 1 < q) (hb : 0 ≤ b) :
    Function.HasTemperateGrowth (logSeries (F := F) q b) := by
  set ℓ : ℕ → F → ℝ := fun i x => Real.log (1 + lsCoeff q b i * ‖x‖ ^ 2) with hℓ
  have hℓc : ∀ i, ContDiff ℝ ∞ (ℓ i) := fun i =>
    (contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))).log fun x => by
      have := lsCoeff_nonneg hq hb i; positivity
  set v : ℕ → ℕ → ℝ :=
    fun k i => ((k + 1) ! * (k + 1) ! : ℝ) * Real.sqrt (2 * lsCoeff q b i) ^ (k + 1)
    with hv
  have hvs : ∀ k, Summable (v k) := fun k => summable_sqrt_pow hq hb (k + 1) (by omega) _
  have hbd : ∀ k i x, ‖iteratedFDeriv ℝ k (fderiv ℝ (ℓ i)) x‖ ≤ v k i := fun k i x => by
    rw [norm_iteratedFDeriv_fderiv]
    exact norm_iteratedFDeriv_logTerm_le (lsCoeff_nonneg hq hb i) (by omega) x
  have hbd0 : ∀ i x, ‖fderiv ℝ (ℓ i) x‖ ≤ v 0 i := fun i x => by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]; exact hbd 0 i x
  have hfc : ∀ i, ContDiff ℝ ∞ (fderiv ℝ (ℓ i)) := fun i => (hℓc i).fderiv_right (by norm_cast)
  have hdiff : ∀ i, Differentiable ℝ (ℓ i) := fun i => (hℓc i).differentiable (by simp)
  have h0 : Summable fun i => ℓ i 0 := by simp [hℓ]
  have hS : logSeries (F := F) q b = fun x => ∑' i, ℓ i x := rfl
  have hfS : fderiv ℝ (logSeries (F := F) q b) = fun x => ∑' i, fderiv ℝ (ℓ i) x := by
    rw [hS]; exact fderiv_tsum (hvs 0) hdiff hbd0 h0
  have hcd : ContDiff ℝ ∞ fun x => ∑' i, fderiv ℝ (ℓ i) x :=
    contDiff_tsum hfc (fun k _ => hvs k)
      (fun k i x _ => hbd k i x)
  refine Function.HasTemperateGrowth.of_fderiv (k := 2) (C := ∑' i, lsCoeff q b i) ?_
    (by rw [hS]; exact differentiable_tsum (hvs 0) (fun i x => (hdiff i x).hasFDerivAt) hbd0)
    fun x => ?_
  · rw [hfS]
    refine ⟨hcd, fun k => ⟨0, ∑' i, v k i, fun x => ?_⟩⟩
    rw [iteratedFDeriv_tsum_apply hfc (fun k _ => hvs k) (fun k i x _ => hbd k i x)
      (by exact_mod_cast le_top), pow_zero, mul_one]
    exact tsum_of_norm_bounded (hvs k).hasSum fun i => hbd k i x
  · rw [Real.norm_eq_abs, abs_of_nonneg (logSeries_nonneg hq hb x)]
    have hle : logSeries q b x ≤ (∑' i, lsCoeff q b i) * ‖x‖ ^ 2 := by
      rw [← tsum_mul_right]
      exact (summable_logTerm hq hb x).tsum_le_tsum (logTerm_le hq hb · x)
        ((summable_lsCoeff hq).mul_right _)
    refine hle.trans (mul_le_mul_of_nonneg_left ?_
      (tsum_nonneg (lsCoeff_nonneg hq hb)))
    nlinarith [norm_nonneg x]

omit [InnerProductSpace ℝ F] in
/-- **The growth of the series**: `S(x) ≤ ε|x|² + A_ε` for every `ε > 0`. -/
theorem logSeries_le (hq : 1 < q) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, ∀ x : F, logSeries q b x ≤ ε * ‖x‖ ^ 2 + A := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑' i, lsCoeff q b (i + N) ≤ ε / 2 := by
    have := (tendsto_sum_nat_add (lsCoeff q b)).eventually
      (ge_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
    obtain ⟨N, hN⟩ := this.exists
    exact ⟨N, hN⟩
  refine ⟨2 * N ^ 2 * b / ε, fun x => ?_⟩
  have hs := summable_logTerm (F := F) hq hb x
  rw [logSeries, ← hs.sum_add_tsum_nat_add N]
  have htail : ∑' i, Real.log (1 + lsCoeff q b (i + N) * ‖x‖ ^ 2) ≤ ε / 2 * ‖x‖ ^ 2 := by
    calc ∑' i, Real.log (1 + lsCoeff q b (i + N) * ‖x‖ ^ 2)
        ≤ ∑' i, lsCoeff q b (i + N) * ‖x‖ ^ 2 :=
          ((summable_nat_add_iff N).2 hs).tsum_le_tsum (fun i => logTerm_le hq hb _ x)
            (((summable_nat_add_iff N).2 (summable_lsCoeff hq)).mul_right _)
      _ ≤ ε / 2 * ‖x‖ ^ 2 := by
          rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hN (sq_nonneg _)
  have hhead : ∑ i ∈ Finset.range N, Real.log (1 + lsCoeff q b i * ‖x‖ ^ 2) ≤
      N * (2 * Real.sqrt b * ‖x‖) := by
    calc ∑ i ∈ Finset.range N, Real.log (1 + lsCoeff q b i * ‖x‖ ^ 2)
        ≤ ∑ _i ∈ Finset.range N, 2 * Real.sqrt b * ‖x‖ := by
          refine Finset.sum_le_sum fun i _ => (log_one_add_le_two_sqrt
            (by have := lsCoeff_nonneg hq hb i; positivity)).trans ?_
          rw [Real.sqrt_mul (lsCoeff_nonneg hq hb i), Real.sqrt_sq (norm_nonneg x), ← mul_assoc]
          gcongr
          exact lsCoeff_le hq hb i
      _ = N * (2 * Real.sqrt b * ‖x‖) := by simp
  have hamgm : (N : ℝ) * (2 * Real.sqrt b * ‖x‖) ≤ ε / 2 * ‖x‖ ^ 2 + 2 * N ^ 2 * b / ε := by
    have hsb := Real.sq_sqrt hb
    have key : 0 ≤ ε / 2 * (‖x‖ - 2 * N * Real.sqrt b / ε) ^ 2 := by positivity
    have e : ε / 2 * (‖x‖ - 2 * N * Real.sqrt b / ε) ^ 2 =
        ε / 2 * ‖x‖ ^ 2 + 2 * N ^ 2 * b / ε - N * (2 * Real.sqrt b * ‖x‖) := by
      have e' : ε / 2 * (‖x‖ - 2 * N * Real.sqrt b / ε) ^ 2 =
          ε / 2 * ‖x‖ ^ 2 + 2 * N ^ 2 * Real.sqrt b ^ 2 / ε - N * (2 * Real.sqrt b * ‖x‖) := by
        field_simp
        ring
      rw [e', hsb]
    linarith
  linarith

end LogTerm

end Pyramids
