/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.IncrementsBernstein
import Pyramids.LineAppendix.MaternLine
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# `prop:matern-increments`(3): the Thorin property and the sum

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:matern-increments`. Phase 5, wave 3b.
`matern_increments_3_thorin` and `matern_increments_3_sum` moved here from
`PyramidsSkeleton.Ch04Matern`, their conclusions unchanged; `_3_sum` no longer takes `0 < s`, which
its proof does not read (2026-11-15, a strengthening).

* **The sum.** `F_q(qr) = log(1 + c²r²) + F_q(r)` (`maternExponent_mul_q`) telescopes
  (`matern_increments_3_sum`).
* **If `t = q^k s`**, the exponent is `∑_{j<k} log(1 + θⱼu)`, `θⱼ = c²q^{2j}s²`, a Thorin–Bernstein
  function: its derivative `∑ (u + 1/θⱼ)⁻¹` and `τm(τ) = ∑ e^{-τ/θⱼ}` are completely monotone, and
  `log(1 + θu) = ∫(1 - e^{-uτ}) e^{-τ/θ} dτ/τ` (Frullani).
* **Only if** (without Bernstein's theorem, ledger A55; `records/pyramids/PRICE-A55.md`, A.1). The
  exponent is `∫(1 - e^{-uτ}) m(τ) dτ` with `m = ∑ᵢ m_{βᵢ,γᵢ}` (Tonelli), so a Thorin
  representation has `τm(τ) = g(τ) := ∑ᵢ (e^{-aᵢτ} - e^{-bᵢτ})` completely monotone, by the
  uniqueness of the density (`IsThorinBernstein.completelyMonotone_density`). Here
  `aᵢ = Aρ^{i+1}`, `bᵢ = Bρ^{i+1}`, `ρ = q²`, `A = (ct)⁻²`, `B = (cs)⁻²`, and `aᵢ ≠ b₀` for
  every `i` when `t/s ∉ q^ℕ`. The derivatives of the series are the series of the derivatives
  (`hasDerivAt_expSeriesDeriv`), and the Post–Widder estimate at the uncancelled atom `x* = b₀`,
  `τₙ = n/x*`, gives `(e/x*)ⁿ(-1)ⁿg⁽ⁿ⁾(τₙ) = ∑ h(aᵢ/x*)ⁿ - ∑ h(bᵢ/x*)ⁿ` with `h(u) = ue^{1-u}`;
  `0 ≤ h ≤ 1` with `h(u) = 1` only at `u = 1`, so by dominated convergence (Tannery's theorem,
  dominated by `h`) the right side tends to `0 - 1 < 0`, against complete monotonicity
  (`not_isCompletelyMonotone_expDiff`).

**What it reaches.** Lean core only.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter
open scoped Topology Nat ENNReal

/-! ## The sum -/

/-- **`prop:matern-increments`(3), the sum.** If `t = q^k s`, the exponent is
`∑_{j=0}^{k-1} log(1 + c² q^{2j} s² u)`. It no longer takes `0 < s`, which its proof does not read
(2026-11-15, a strengthening). -/
theorem matern_increments_3_sum {q c : ℝ} (hq : 1 < q) (hc : 0 < c) (s : ℝ)
    (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    maternExponent q c (q ^ k * s * Real.sqrt u) - maternExponent q c (s * Real.sqrt u) =
      ∑ j ∈ Finset.range k, Real.log (1 + c ^ 2 * q ^ (2 * j) * s ^ 2 * u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, pow_succ,
      show q ^ k * q * s * Real.sqrt u = q * (q ^ k * s * Real.sqrt u) by ring,
      maternExponent_mul_q hq hc]
    have h : (q ^ k * s * Real.sqrt u) ^ 2 = q ^ (2 * k) * s ^ 2 * u := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hu, ← pow_mul, mul_comm k 2]
    rw [h]
    ring_nf

/-! ## Series of exponentials -/

/-- `∑ᵢ (-θᵢ)ⁿ e^{-θᵢx}`, the `n`-th derivative of `∑ᵢ e^{-θᵢx}`. -/
noncomputable def expSeriesDeriv (θ : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑' i, (-θ i) ^ n * Real.exp (-(θ i * x))

theorem summable_expSeriesDeriv {θ : ℕ → ℝ} (hθ : ∀ i, 0 < θ i)
    (hsum : Summable fun i => (θ i ^ 2)⁻¹) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable fun i => (-θ i) ^ n * Real.exp (-(θ i * x)) := by
  refine Summable.of_norm ?_
  refine (summable_pow_mul_exp_neg hθ hsum n hx).congr fun i => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (hθ i), abs_of_pos (Real.exp_pos _)]

theorem hasDerivAt_expSeriesDeriv {θ : ℕ → ℝ} (hθ : ∀ i, 0 < θ i)
    (hsum : Summable fun i => (θ i ^ 2)⁻¹) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (expSeriesDeriv θ n) (expSeriesDeriv θ (n + 1) x) x := by
  have hx2 : 0 < x / 2 := by positivity
  refine hasDerivAt_tsum_of_isPreconnected (t := Ioi (x / 2))
    (u := fun i => θ i ^ (n + 1) * Real.exp (-(θ i * (x / 2))))
    (g' := fun i y => (-θ i) ^ (n + 1) * Real.exp (-(θ i * y)))
    (summable_pow_mul_exp_neg hθ hsum (n + 1) hx2) isOpen_Ioi isPreconnected_Ioi
    (fun i y _ => ?_) (fun i y hy => ?_) (y₀ := x) (by simp only [mem_Ioi]; linarith)
    (summable_expSeriesDeriv hθ hsum n hx) (by simp only [mem_Ioi]; linarith)
  · have h1 : HasDerivAt (fun y : ℝ => -(θ i * y)) (-θ i) y := by
      have := (hasDerivAt_id y).const_mul (-θ i)
      simp only [id, mul_one, neg_mul] at this
      exact this
    refine ((h1.exp).const_mul ((-θ i) ^ n)).congr_deriv ?_
    ring
  · have hy : x / 2 < y := hy
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (hθ i),
      abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by have := hθ i; positivity)
    nlinarith [hθ i]

/-- A family with `G n' = G (n + 1)` on `(0,∞)`: `G 0` is smooth there, with
`iteratedDerivWithin n (G 0) = G n`. -/
theorem iteratedDerivWithin_eq_of_hasDerivAt {G : ℕ → ℝ → ℝ}
    (hG : ∀ n x, 0 < x → HasDerivAt (G n) (G (n + 1) x) x) :
    ContDiffOn ℝ (⊤ : ℕ∞) (G 0) (Ioi 0) ∧
      ∀ n, EqOn (iteratedDerivWithin n (G 0) (Ioi 0)) (G n) (Ioi 0) := by
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hderiv : ∀ n, EqOn (derivWithin (G n) (Ioi 0)) (G (n + 1)) (Ioi 0) := by
    intro n x hx
    exact ((hG n x hx).hasDerivWithinAt).derivWithin (hU x hx)
  have hcd : ∀ m : ℕ, ∀ n, ContDiffOn ℝ m (G n) (Ioi 0) := by
    intro m
    induction m with
    | zero =>
      intro n
      exact contDiffOn_zero.2 fun x hx => (hG n x hx).continuousAt.continuousWithinAt
    | succ m ih =>
      intro n
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin hU]
      refine ⟨fun x hx => (hG n x hx).differentiableAt.differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      exact (ih (n + 1)).congr (hderiv n)
  refine ⟨contDiffOn_infty.2 fun m => hcd m 0, fun n => ?_⟩
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih hx)]
    exact hderiv n hx

theorem summable_inv_sq_geom {A ρ : ℝ} (hρ : 1 < ρ) :
    Summable fun i : ℕ => ((A * ρ ^ (i + 1)) ^ 2)⁻¹ := by
  have h0 : (0 : ℝ) ≤ (ρ ^ 2)⁻¹ := by positivity
  have h1 : (ρ ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  refine ((summable_geometric_of_lt_one h0 h1).mul_left ((A ^ 2)⁻¹ * (ρ ^ 2)⁻¹)).congr
    fun i => ?_
  have hρ0 : 0 < ρ := by linarith
  rw [mul_pow, ← pow_mul, inv_pow, mul_inv, pow_succ, mul_comm (i + 1) 2, pow_mul, pow_succ,
    mul_inv]
  ring

/-! ## The Post–Widder estimate at an uncancelled atom -/

theorem mul_exp_one_sub_le_one {u : ℝ} : u * Real.exp (1 - u) ≤ 1 := by
  have h := Real.add_one_le_exp (u - 1)
  have he := Real.exp_pos (1 - u)
  calc u * Real.exp (1 - u) ≤ Real.exp (u - 1) * Real.exp (1 - u) :=
        mul_le_mul_of_nonneg_right (by linarith) he.le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem mul_exp_one_sub_lt_one {u : ℝ} (hu : u ≠ 1) : u * Real.exp (1 - u) < 1 := by
  have h := Real.add_one_lt_exp (sub_ne_zero.2 hu)
  have he := Real.exp_pos (1 - u)
  calc u * Real.exp (1 - u) < Real.exp (u - 1) * Real.exp (1 - u) :=
        mul_lt_mul_of_pos_right (by linarith) he
    _ = 1 := by rw [← Real.exp_add]; simp

theorem summable_mul_exp_one_sub_geom {A ρ : ℝ} (hA : 0 < A) (hρ : 1 < ρ) :
    Summable fun i : ℕ => A * ρ ^ (i + 1) * Real.exp (1 - A * ρ ^ (i + 1)) := by
  have hθ : ∀ i : ℕ, 0 < A * ρ ^ (i + 1) := fun i => by
    have : 0 < ρ := by linarith
    positivity
  refine ((summable_pow_mul_exp_neg hθ (summable_inv_sq_geom (A := A) hρ) 1 one_pos).mul_left
    (Real.exp 1)).congr fun i => ?_
  rw [pow_one, mul_one, sub_eq_add_neg, Real.exp_add]
  ring

/-- **The Post–Widder estimate at an uncancelled atom.** For `0 < A < B`, `ρ > 1` and
`Aρ^{i+1} ≠ Bρ` for every `i`, the difference `∑ᵢ e^{-Aρ^{i+1}x} - ∑ᵢ e^{-Bρ^{i+1}x}` is not
completely monotone. -/
theorem not_isCompletelyMonotone_expDiff {A B ρ : ℝ} (hA : 0 < A) (hAB : A < B) (hρ : 1 < ρ)
    (hatom : ∀ i : ℕ, A * ρ ^ (i + 1) ≠ B * ρ) :
    ¬ IsCompletelyMonotone (fun x => expSeriesDeriv (fun i => A * ρ ^ (i + 1)) 0 x -
      expSeriesDeriv (fun i => B * ρ ^ (i + 1)) 0 x) := by
  intro hcm
  have hρ0 : 0 < ρ := by linarith
  have hB : 0 < B := hA.trans hAB
  set a : ℕ → ℝ := fun i => A * ρ ^ (i + 1) with ha_def
  set b : ℕ → ℝ := fun i => B * ρ ^ (i + 1) with hb_def
  have ha : ∀ i, 0 < a i := fun i => by simp only [ha_def]; positivity
  have hb : ∀ i, 0 < b i := fun i => by simp only [hb_def]; positivity
  have hsa := summable_inv_sq_geom (A := A) hρ
  have hsb := summable_inv_sq_geom (A := B) hρ
  set G : ℕ → ℝ → ℝ := fun n x => expSeriesDeriv a n x - expSeriesDeriv b n x with hG_def
  have hG : ∀ n x, 0 < x → HasDerivAt (G n) (G (n + 1) x) x := fun n x hx =>
    (hasDerivAt_expSeriesDeriv ha hsa n hx).sub (hasDerivAt_expSeriesDeriv hb hsb n hx)
  obtain ⟨-, hit⟩ := iteratedDerivWithin_eq_of_hasDerivAt hG
  -- the sign of `(-1)ⁿ g⁽ⁿ⁾`
  have hflip : ∀ (θ : ℕ → ℝ) (n : ℕ) (x : ℝ), (-1 : ℝ) ^ n * expSeriesDeriv θ n x =
      ∑' i, θ i ^ n * Real.exp (-(θ i * x)) := by
    intro θ n x
    rw [expSeriesDeriv, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  have hsign : ∀ n x, 0 < x →
      0 ≤ ∑' i, a i ^ n * Real.exp (-(a i * x)) - ∑' i, b i ^ n * Real.exp (-(b i * x)) := by
    intro n x hx
    have h := hcm.2 n x hx
    rw [show (fun x => expSeriesDeriv (fun i => A * ρ ^ (i + 1)) 0 x -
      expSeriesDeriv (fun i => B * ρ ^ (i + 1)) 0 x) = G 0 from rfl, hit n hx] at h
    simp only [hG_def, mul_sub, hflip] at h
    exact h
  -- Post–Widder at `x* = b₀`
  set xs := b 0 with hxs
  have hxs0 : 0 < xs := hb 0
  set h : ℝ → ℝ := fun u => u * Real.exp (1 - u) with hh
  have key : ∀ (n : ℕ) (θ : ℝ), (Real.exp 1 / xs) ^ n * (θ ^ n * Real.exp (-(θ * (n / xs)))) =
      h (θ / xs) ^ n := by
    intro n θ
    simp only [hh]
    rw [mul_pow, div_pow, ← Real.exp_nat_mul, div_pow, ← Real.exp_nat_mul]
    have he : (n : ℝ) * (1 - θ / xs) = n * 1 + -(θ * (n / xs)) := by ring
    rw [he, Real.exp_add]
    field_simp
  have hS : ∀ n : ℕ, 1 ≤ n → 0 ≤ ∑' i, h (a i / xs) ^ n - ∑' i, h (b i / xs) ^ n := by
    intro n hn
    have hx : 0 < (n : ℝ) / xs := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    have := mul_nonneg (pow_nonneg (by positivity : 0 ≤ Real.exp 1 / xs) n) (hsign n _ hx)
    rw [mul_sub, ← tsum_mul_left, ← tsum_mul_left] at this
    simpa only [key] using this
  -- the two limits, by dominated convergence
  have hh0 : ∀ u, 0 ≤ u → 0 ≤ h u := fun u hu => by
    simp only [hh]; have := Real.exp_pos (1 - u); positivity
  have hbound : ∀ θ : ℕ → ℝ, (∀ i, 0 ≤ θ i) → ∀ᶠ n : ℕ in atTop, ∀ i, ‖h (θ i) ^ n‖ ≤ h (θ i) := by
    intro θ hθ
    filter_upwards [eventually_ge_atTop 1] with n hn i
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hh0 _ (hθ i)) n)]
    exact pow_le_of_le_one (hh0 _ (hθ i)) mul_exp_one_sub_le_one (by omega)
  have hdiv : ∀ (C : ℝ) (i : ℕ), C * ρ ^ (i + 1) / xs = C / xs * ρ ^ (i + 1) := fun C i => by
    ring
  have hlimA : Tendsto (fun n : ℕ => ∑' i, h (a i / xs) ^ n) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (f := fun n i => h (a i / xs) ^ n)
      (g := fun _ => (0 : ℝ)) (bound := fun i => h (a i / xs))
      (by simp only [hh, ha_def, hdiv]; exact summable_mul_exp_one_sub_geom (by positivity) hρ)
      (fun i => tendsto_pow_atTop_nhds_zero_of_lt_one (hh0 _ (by have := ha i; positivity))
        (mul_exp_one_sub_lt_one fun h1 => hatom i (by
          rw [div_eq_one_iff_eq hxs0.ne'] at h1
          simpa [ha_def, hxs, hb_def] using h1)))
      (hbound _ fun i => by have := ha i; positivity)
    simpa using this
  have hlimB : Tendsto (fun n : ℕ => ∑' i, h (b i / xs) ^ n) atTop (𝓝 1) := by
    have := tendsto_tsum_of_dominated_convergence (f := fun n i => h (b i / xs) ^ n)
      (g := fun i => if i = 0 then (1 : ℝ) else 0) (bound := fun i => h (b i / xs))
      (by simp only [hh, hb_def, hdiv]; exact summable_mul_exp_one_sub_geom (by positivity) hρ)
      (fun i => ?_) (hbound _ fun i => by have := hb i; positivity)
    · rwa [tsum_ite_eq] at this
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp only [if_true, hxs, div_self (hb 0).ne', hh, sub_self, Real.exp_zero, one_mul,
          one_pow]
        exact tendsto_const_nhds
      · rw [if_neg hi.ne']
        refine tendsto_pow_atTop_nhds_zero_of_lt_one (hh0 _ (by have := hb i; positivity))
          (mul_exp_one_sub_lt_one fun h1 => ?_)
        have hbi : b i / xs = ρ ^ i := by
          simp only [hxs, hb_def]
          rw [zero_add, pow_one, pow_succ]
          field_simp
        rw [hbi] at h1
        exact (one_lt_pow₀ hρ hi.ne').ne' h1
  have hlim := hlimA.sub hlimB
  rw [zero_sub] at hlim
  obtain ⟨n, hn, hneg⟩ := ((eventually_ge_atTop 1).and
    (hlim (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 0)))).exists
  exact absurd (hS n hn) (not_le.2 hneg)

/-! ## A finite sum of logarithms is a Thorin–Bernstein function -/

theorem isCompletelyMonotone_zero : IsCompletelyMonotone (fun _ => (0 : ℝ)) :=
  (isCompletelyMonotone_exp_neg.const_mul le_rfl).congr fun x _ => by simp

theorem isCompletelyMonotone_finset_sum {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ j ∈ S, IsCompletelyMonotone (f j)) :
    IsCompletelyMonotone (fun x => ∑ j ∈ S, f j x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isCompletelyMonotone_zero
  | insert j S hj ih =>
    simp_rw [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j S)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **`∑_{j<k} log(1 + θⱼu)`, `θⱼ > 0`, is a Thorin–Bernstein function**, with `a = b = 0` and
`m(τ) = ∑ e^{-τ/θⱼ}/τ`. -/
theorem isThorinBernstein_logSum {k : ℕ} {θ : ℕ → ℝ} (hθ : ∀ j, 0 < θ j) {ψ : ℝ → ℝ}
    (hψ : ∀ u, 0 < u → ψ u = ∑ j ∈ Finset.range k, Real.log (1 + θ j * u)) :
    IsThorinBernstein ψ := by
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hder : ∀ x, 0 < x → HasDerivAt ψ (∑ j ∈ Finset.range k, (x + 1 / θ j)⁻¹) x := by
    intro x hx
    have heq : (fun u => ∑ j ∈ Finset.range k, Real.log (1 + θ j * u)) =ᶠ[𝓝 x] ψ := by
      filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with u hu
      exact (hψ u hu).symm
    refine (HasDerivAt.fun_sum fun j _ => ?_).congr_of_eventuallyEq heq.symm
    have hj := hθ j
    have h1 : HasDerivAt (fun u => 1 + θ j * u) (θ j) x := by
      simpa using ((hasDerivAt_id x).const_mul (θ j)).const_add 1
    refine (h1.log (by positivity)).congr_deriv ?_
    field_simp
    ring
  set m : ℝ → ℝ := fun τ => ∑ j ∈ Finset.range k, Real.exp (-τ / θ j) / τ with hm
  have hm0 : ∀ τ, 0 < τ → 0 ≤ m τ := fun τ hτ =>
    Finset.sum_nonneg fun j _ => by have := Real.exp_pos (-τ / θ j); positivity
  have htm : ∀ τ, 0 < τ → τ * m τ = ∑ j ∈ Finset.range k, Real.exp (-((θ j)⁻¹ * τ)) := by
    intro τ hτ
    simp only [hm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show -((θ j)⁻¹ * τ) = -τ / θ j by ring]
    field_simp
  have hint : ∀ j, IntegrableOn (fun τ => Real.exp (-((θ j)⁻¹ * τ))) (Ioi 0) := fun j => by
    simpa using exp_neg_integrableOn_Ioi 0 (inv_pos.2 (hθ j))
  refine ⟨⟨fun x hx => ?_, fun x hx => (hder x hx).differentiableAt.differentiableWithinAt, ?_⟩,
    0, 0, m, le_rfl, le_rfl, ?_, ?_, fun x hx => ?_⟩
  · rw [hψ x hx]
    exact Finset.sum_nonneg fun j _ => Real.log_nonneg (by
      have := hθ j; have : (0 : ℝ) < x := hx; nlinarith [mul_pos (hθ j) this])
  · refine (isCompletelyMonotone_finset_sum (Finset.range k) fun j _ =>
      isCompletelyMonotone_inv_add (by have := hθ j; positivity : (0 : ℝ) ≤ 1 / θ j)).congr
      fun x hx => ?_
    exact ((hder x hx).hasDerivWithinAt.derivWithin (hU x hx)).symm
  · refine (isCompletelyMonotone_finset_sum (Finset.range k) fun j _ =>
      isCompletelyMonotone_exp_neg.comp_mul (inv_pos.2 (hθ j))).congr fun τ hτ => ?_
    exact (htm τ hτ).symm
  · refine ne_top_of_le_ne_top (integrable_finsetSum (Finset.range k) fun j _ =>
      hint j).lintegral_lt_top.ne ?_
    refine setLIntegral_mono' measurableSet_Ioi fun τ (hτ : 0 < τ) => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← htm τ hτ]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (hm0 τ hτ)
  · rw [hψ x hx, zero_add, zero_mul, zero_add]
    have hfr := fun j => frullani_integral (hθ j) hx.le
    have hsum : ∀ τ, (1 - Real.exp (-(x * τ))) * m τ = ∑ j ∈ Finset.range k,
        (1 - Real.exp (-(τ * x))) * (Real.exp (-τ / θ j) / τ) := fun τ => by
      simp only [hm, Finset.mul_sum, mul_comm x τ]
    simp_rw [hsum]
    rw [integral_finsetSum _ fun j _ => (hfr j).1]
    exact Finset.sum_congr rfl fun j _ => ((hfr j).2).symm

/-! ## `prop:matern-increments`(3), the Thorin property -/

/-- **`prop:matern-increments`(3), the Thorin property.** As a function of `u = |ω|²`, the exponent
`F_q(t√u) - F_q(s√u)` of `μ_{s,t}`, `0 < s < t`, is a Thorin–Bernstein function if and only if
`t/s ∈ q^ℕ`. -/
theorem matern_increments_3_thorin {q c : ℝ} (hq : 1 < q) (hc : 0 < c) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) :
    IsThorinBernstein (fun u => maternExponent q c (t * Real.sqrt u) -
        maternExponent q c (s * Real.sqrt u)) ↔ ∃ k : ℕ, t = q ^ k * s := by
  have hq0 : 0 < q := by linarith
  have ht : 0 < t := hs.trans hst
  constructor
  swap
  · rintro ⟨k, rfl⟩
    exact isThorinBernstein_logSum (θ := fun j => c ^ 2 * q ^ (2 * j) * s ^ 2) (k := k)
      (fun j => by positivity) fun u hu => matern_increments_3_sum hq hc s k u hu.le
  intro hT
  by_contra hk
  push Not at hk
  -- the data
  set β : ℕ → ℝ := fun i => c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) with hβ_def
  set γ : ℕ → ℝ := fun i => c ^ 2 * s ^ 2 / q ^ (2 * (i + 1)) with hγ_def
  have hγ : ∀ i, 0 < γ i := fun i => by simp only [hγ_def]; positivity
  have hγβ : ∀ i, γ i < β i := fun i => by
    simp only [hγ_def, hβ_def]
    refine div_lt_div_of_pos_right (mul_lt_mul_of_pos_left ?_ (by positivity)) (by positivity)
    exact pow_lt_pow_left₀ hst hs.le two_ne_zero
  have hβ : ∀ i, 0 < β i := fun i => (hγ i).trans (hγβ i)
  set A : ℝ := (c ^ 2 * t ^ 2)⁻¹ with hA_def
  set B : ℝ := (c ^ 2 * s ^ 2)⁻¹ with hB_def
  set ρ : ℝ := q ^ 2 with hρ_def
  have hA : 0 < A := by positivity
  have hAB : A < B := by
    simp only [hA_def, hB_def]
    refine inv_strictAnti₀ (by positivity) (mul_lt_mul_of_pos_left ?_ (by positivity))
    exact pow_lt_pow_left₀ hst hs.le two_ne_zero
  have hρ : 1 < ρ := by simp only [hρ_def]; nlinarith
  set a : ℕ → ℝ := fun i => A * ρ ^ (i + 1) with ha_def
  set b : ℕ → ℝ := fun i => B * ρ ^ (i + 1) with hb_def
  have ha : ∀ i, 0 < a i := fun i => by simp only [ha_def]; positivity
  have hb : ∀ i, 0 < b i := fun i => by simp only [hb_def]; positivity
  have hsa := summable_inv_sq_geom (A := A) hρ
  have hsb := summable_inv_sq_geom (A := B) hρ
  have hβa : ∀ i τ, -τ / β i = -(a i * τ) := fun i τ => by
    simp only [hβ_def, ha_def, hA_def, hρ_def]
    rw [pow_mul]
    field_simp
  have hγb : ∀ i τ, -τ / γ i = -(b i * τ) := fun i τ => by
    simp only [hγ_def, hb_def, hB_def, hρ_def]
    rw [pow_mul]
    field_simp
  have hatom : ∀ i : ℕ, A * ρ ^ (i + 1) ≠ B * ρ := by
    intro i h
    have h2 : (q ^ i * s) ^ 2 * (q ^ 2 * c ^ 2) = t ^ 2 * (q ^ 2 * c ^ 2) := by
      simp only [hA_def, hB_def, hρ_def] at h
      field_simp at h
      linear_combination c ^ 2 * h
    have h3 := mul_right_cancel₀ (by positivity) h2
    exact hk i ((pow_left_inj₀ (by positivity) ht.le two_ne_zero).1 h3).symm
  -- the density `m = ∑ m_{βᵢ,γᵢ}` and `τm(τ) = g(τ)`
  set m : ℝ → ℝ := fun τ => ∑' i, incDensity (β i) (γ i) τ with hm_def
  have hd0 : ∀ i τ, 0 < τ → 0 ≤ incDensity (β i) (γ i) τ := fun i τ hτ =>
    incDensity_nonneg (hγ i) (hγβ i) hτ
  have hsm : ∀ τ, 0 < τ → Summable fun i => incDensity (β i) (γ i) τ := by
    intro τ hτ
    refine Summable.of_nonneg_of_le (fun i => hd0 i τ hτ) (fun i => ?_)
      (((summable_pow_mul_exp_neg ha hsa 0 hτ).div_const τ))
    simp only [incDensity, pow_zero, one_mul]
    rw [hβa]
    exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hτ.le
  set G0 : ℝ → ℝ := fun x => expSeriesDeriv a 0 x - expSeriesDeriv b 0 x with hG0_def
  have hmG : ∀ τ, 0 < τ → τ * m τ = G0 τ := by
    intro τ hτ
    have hea := summable_expSeriesDeriv ha hsa 0 hτ
    have heb := summable_expSeriesDeriv hb hsb 0 hτ
    simp only [hm_def, hG0_def, expSeriesDeriv]
    rw [← tsum_mul_left, ← hea.tsum_sub heb]
    refine tsum_congr fun i => ?_
    simp only [incDensity, pow_zero, one_mul]
    rw [hβa, hγb]
    field_simp
  have hG0c : ContinuousOn G0 (Ioi 0) := fun x hx =>
    ((hasDerivAt_expSeriesDeriv ha hsa 0 hx).sub
      (hasDerivAt_expSeriesDeriv hb hsb 0 hx)).continuousAt.continuousWithinAt
  have hmc : ContinuousOn m (Ioi 0) := by
    refine (hG0c.div continuousOn_id fun τ (hτ : 0 < τ) => hτ.ne').congr fun τ (hτ : 0 < τ) => ?_
    simp only [Pi.div_apply, id]
    rw [← hmG τ hτ]
    field_simp
  have hm0 : ∀ τ, 0 < τ → 0 ≤ m τ := fun τ hτ => tsum_nonneg fun i => hd0 i τ hτ
  -- the exponent as `∫(1 - e^{-xτ}) m(τ) dτ`
  have hrep : ∀ x, 0 < x → ENNReal.ofReal (maternExponent q c (t * Real.sqrt x) -
      maternExponent q c (s * Real.sqrt x)) = ∫⁻ τ in Ioi (0 : ℝ),
        ENNReal.ofReal (m τ) * ENNReal.ofReal (1 - Real.exp (-(x * τ))) := by
    intro x hx
    have he : ∀ (r : ℝ) (i : ℕ), c ^ 2 * (r * Real.sqrt x) ^ 2 / q ^ (2 * (i + 1)) =
        c ^ 2 * r ^ 2 / q ^ (2 * (i + 1)) * x := fun r i => by
      rw [mul_pow, Real.sq_sqrt hx.le]
      ring
    have hpt : ∀ i, Real.log (1 + c ^ 2 * (t * Real.sqrt x) ^ 2 / q ^ (2 * (i + 1))) -
        Real.log (1 + c ^ 2 * (s * Real.sqrt x) ^ 2 / q ^ (2 * (i + 1))) =
          maternIncExponent (β i) (γ i) x := fun i => by
      rw [maternIncExponent_eq (hβ i) (hγ i) hx.le, he, he]
    have hS := ((summable_maternExponent hq hc (t * Real.sqrt x)).sub
      (summable_maternExponent hq hc (s * Real.sqrt x))).congr hpt
    have hf0 : ∀ i, 0 ≤ maternIncExponent (β i) (γ i) x := fun i =>
      (matern_increments_1 (hγ i) (hγβ i)).2.2.1.1.1 x hx
    rw [maternExponent, maternExponent, ← (summable_maternExponent hq hc _).tsum_sub
      (summable_maternExponent hq hc _), tsum_congr hpt, ENNReal.ofReal_tsum_of_nonneg hf0 hS,
      tsum_congr fun i => ofReal_maternIncExponent (hγ i) (hγβ i) hx,
      ← lintegral_tsum fun i => (Measurable.aemeasurable (by unfold incDensity; fun_prop))]
    refine setLIntegral_congr_fun measurableSet_Ioi fun τ (hτ : 0 < τ) => ?_
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun i => hd0 i τ hτ) (hsm τ hτ)]
  have hcm := hT.completelyMonotone_density hm0 hmc hrep
  exact not_isCompletelyMonotone_expDiff hA hAB hρ hatom (hcm.congr fun τ hτ => hmG τ hτ)

end Pyramids
