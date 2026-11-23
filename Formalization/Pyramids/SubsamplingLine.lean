/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.DiscreteHelmholtz

/-!
# `prop:helmholtz-subsampling`(1): the line at index `1`

Blueprint: `blueprint/src/parts/06-helmholtz.tex`, `prop:helmholtz-subsampling`. Wave 2, group J,
Q-0281. Clause (1) only: on `hℤ` the kernel `κ_t` is `((1-a)/(1+a))a^{|n|}` with
`a + a⁻¹ = 2 + h²/t²`
(both are bounded solutions of `(1 - t²Δ_h)u = δ₀`), and its subsample by `q` is proportional to the
kernel with ratio `aᵠ`, a member of the family on `qhℤ`.
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set Filter

/-- The geometric kernel `((1-a)/(1+a))a^{|n|}` on `ℤ`. -/
noncomputable def geomKernel (a : ℝ) (n : ℤ) : ℝ := (1 - a) / (1 + a) * a ^ n.natAbs

/-- **`κ_t` on `hℤ` is geometric**: if `0 < a < 1` and `a + a⁻¹ = 2 + h²/t²`, then
`κ_t(n) = ((1-a)/(1+a))a^{|n|}`. -/
theorem line_kappa_eq {h t a : ℝ} (hh : 0 < h) (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    (hab : a + a⁻¹ = 2 + h ^ 2 / t ^ 2) (n : ℤ) :
    discreteHelmholtz 1 h t (fun _ => n) = geomKernel a n := by
  set e : ℤ ≃ Zd 1 := (Equiv.funUnique (Fin 1) ℤ).symm with he
  have hK := isProbKernel_discreteHelmholtz (le_refl 1) hh ht
  set U : ℤ → ℝ := fun m => discreteHelmholtz 1 h t (e m) with hU
  have hUs : Summable U := (e.summable_iff (f := discreteHelmholtz 1 h t)).2 hK.2.1
  obtain ⟨k, hk⟩ : ∃ k, k = t ^ 2 / h ^ 2 := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; positivity
  have hka : k * (1 - a) ^ 2 = a := by
    have h1 : h ^ 2 / t ^ 2 = k⁻¹ := by rw [hk, inv_div]
    rw [h1] at hab
    field_simp at hab
    nlinarith [hab]
  have hUeq : ∀ m : ℤ, U m - k * (U (m + 1) - 2 * U m + U (m - 1)) = if m = 0 then 1 else 0 := by
    intro m
    have h1 := discreteHelmholtz_eqn (le_refl 1) hh ht (e m)
    have hp : e m + zbasis 0 = e (m + 1) := by funext j; fin_cases j; simp [he, zbasis]
    have hm : e m - zbasis 0 = e (m - 1) := by funext j; fin_cases j; simp [he, zbasis]
    have h0 : deltaZ (e m) = if m = 0 then 1 else 0 := by
      unfold deltaZ
      congr 1
      exact propext ⟨fun h => by simpa [he] using congrFun h 0, fun h => by
        funext j; simp [he, h]⟩
    rw [gridLap, Fin.sum_univ_one, hp, hm, h0] at h1
    simp only [hU, hk]
    rw [← h1]
    ring
  have hGeq : ∀ m : ℤ, geomKernel a m - k * (geomKernel a (m + 1) - 2 * geomKernel a m +
      geomKernel a (m - 1)) = if m = 0 then 1 else 0 := by
    intro m
    have h1 : 1 - a ≠ 0 := by linarith
    have h2 : 1 + a ≠ 0 := by linarith
    simp only [geomKernel]
    rcases Int.eq_nat_or_neg m with ⟨j, rfl | rfl⟩
    · rcases j with _ | j
      · simp only [Nat.cast_zero, zero_add, zero_sub, Int.natAbs_zero, if_true, pow_zero]
        rw [show (1 : ℤ).natAbs = 1 from rfl, show (-1 : ℤ).natAbs = 1 from rfl, pow_one]
        field_simp
        linear_combination (2 : ℝ) * hka
      · have e1 : ((j + 1 : ℕ) : ℤ) + 1 = ((j + 2 : ℕ) : ℤ) := by push_cast; ring
        have e2 : ((j + 1 : ℕ) : ℤ) - 1 = ((j : ℕ) : ℤ) := by push_cast; ring
        rw [e1, e2, Int.natAbs_natCast, Int.natAbs_natCast, Int.natAbs_natCast,
          if_neg (by omega)]
        field_simp
        linear_combination (-(1 - a) * a ^ j) * hka
    · rcases j with _ | j
      · simp only [Nat.cast_zero, neg_zero, zero_add, zero_sub, Int.natAbs_zero, if_true,
          pow_zero]
        rw [show (1 : ℤ).natAbs = 1 from rfl, show (-1 : ℤ).natAbs = 1 from rfl, pow_one]
        field_simp
        linear_combination (2 : ℝ) * hka
      · have e1 : -((j + 1 : ℕ) : ℤ) + 1 = -((j : ℕ) : ℤ) := by push_cast; ring
        have e2 : -((j + 1 : ℕ) : ℤ) - 1 = -((j + 2 : ℕ) : ℤ) := by push_cast; ring
        rw [e1, e2, Int.natAbs_neg, Int.natAbs_neg, Int.natAbs_neg, Int.natAbs_natCast,
          Int.natAbs_natCast, Int.natAbs_natCast, if_neg (by omega)]
        field_simp
        linear_combination (-(1 - a) * a ^ j) * hka
  have hGb : ∃ C, ∀ m, |geomKernel a m| ≤ C := ⟨1, fun m => by
    unfold geomKernel
    rw [abs_of_nonneg (mul_nonneg (div_nonneg (by linarith) (by linarith)) (pow_nonneg ha0.le _))]
    have : (1 - a) / (1 + a) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have : a ^ m.natAbs ≤ 1 := pow_le_one₀ ha0.le ha1.le
    nlinarith [pow_nonneg ha0.le m.natAbs]⟩
  have hz := helm_homog_zero ha0 ha1 (e := fun m => U m - geomKernel a m) (by
    obtain ⟨C1, hC1⟩ := bounded_of_summable hUs
    obtain ⟨C2, hC2⟩ := hGb
    exact ⟨C1 + C2, fun m => (abs_sub _ _).trans (add_le_add (hC1 m) (hC2 m))⟩) fun m => by
      have h1 := hUeq m
      have h2 := hGeq m
      have hinv : a + a⁻¹ = 2 + k⁻¹ := by rw [hab, hk, inv_div]
      rw [hinv]
      field_simp
      linear_combination (-1 : ℝ) * h1 + h2
  have := congrFun hz n
  simp only [Pi.zero_apply] at this
  have hn : (fun _ : Fin 1 => n) = e n := by funext j; simp [he]
  rw [hn]
  simp only [hU] at this
  linarith

theorem geomKernel_root {B : ℝ} (hB : 2 < B) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ a + a⁻¹ = B := by
  set r := Real.sqrt (B ^ 2 - 4) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by nlinarith)
  have hr2 : r ^ 2 = B ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  have hrB : r < B := by nlinarith
  refine ⟨(B - r) / 2, by linarith, by nlinarith, ?_⟩
  have hne : B - r ≠ 0 := by linarith
  field_simp
  linear_combination hr2

theorem natAbs_mul_nat (q : ℕ) (m : ℤ) : ((q : ℤ) * m).natAbs = q * m.natAbs := by
  rw [Int.natAbs_mul, Int.natAbs_natCast]

/-- **`prop:helmholtz-subsampling`(1)**, the line at index `1`: `κ_t(n) = ((1-a)/(1+a))a^{|n|}` with
`a ∈ (0,1)`, `a + a⁻¹ = 2 + h²/t²`, and its subsample by `q` is proportional to `λ^{(qh,1)}_{t'}`,
the
kernel with ratio `a^q`, where `a^q + a^{-q} = 2 + q²h²/t'²`. -/
theorem subsampling_line_index_one {h : ℝ} (hh : 0 < h) {q : ℕ} (hq : 2 ≤ q) {t : ℝ} (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ a + a⁻¹ = 2 + h ^ 2 / t ^ 2 ∧
      (∀ n : ℤ, lineHelmKernel h t 1 n = (1 - a) / (1 + a) * a ^ n.natAbs) ∧
      ∃ t' : ℝ, 0 < t' ∧ a ^ q + (a ^ q)⁻¹ = 2 + (q : ℝ) ^ 2 * h ^ 2 / t' ^ 2 ∧
        (∀ m : ℤ, lineHelmKernel (q * h) t' 1 m = (1 - a ^ q) / (1 + a ^ q) * (a ^ q) ^ m.natAbs) ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ m : ℤ, lineHelmKernel h t 1 (q * m) = C * lineHelmKernel (q * h) t' 1 m := by
  obtain ⟨a, ha0, ha1, hab⟩ := geomKernel_root (B := 2 + h ^ 2 / t ^ 2) (by
    have : 0 < h ^ 2 / t ^ 2 := by positivity
    linarith)
  have hk1 : ∀ (hh' t' : ℝ), lineHelmKernel hh' t' 1 = fun n =>
      discreteHelmholtz 1 hh' t' (fun _ => n) := by
    intro hh' t'
    funext n
    simp [lineHelmKernel, helmKernel, kpow, kconv_deltaZ_left]
  have hfine : ∀ n : ℤ, lineHelmKernel h t 1 n = (1 - a) / (1 + a) * a ^ n.natAbs := by
    intro n
    rw [hk1]
    exact (line_kappa_eq hh ht ha0 ha1 hab n).trans rfl
  set A := a ^ q with hA
  have hq0 : 0 < q := by omega
  have hA0 : 0 < A := pow_pos ha0 q
  have hA1 : A < 1 := pow_lt_one₀ ha0.le ha1 hq0.ne'
  set t' := q * h * Real.sqrt A / (1 - A) with ht'
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA0
  have ht'0 : 0 < t' := by
    rw [ht']; have : (0 : ℝ) < q := by exact_mod_cast hq0
    have : 0 < 1 - A := by linarith
    positivity
  have hAt' : A + A⁻¹ = 2 + (q : ℝ) ^ 2 * h ^ 2 / t' ^ 2 := by
    rw [ht', div_pow, mul_pow, mul_pow, Real.sq_sqrt hA0.le]
    have : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have : 1 - A ≠ 0 := by linarith
    field_simp
    ring
  have hcoarse : ∀ m : ℤ, lineHelmKernel (q * h) t' 1 m = (1 - A) / (1 + A) * A ^ m.natAbs := by
    intro m
    have hqh : 0 < (q : ℝ) * h := by
      have : (0 : ℝ) < q := by exact_mod_cast hq0
      positivity
    rw [hk1]
    exact (line_kappa_eq hqh ht'0 hA0 hA1 (by rw [hAt']; ring) m).trans rfl
  refine ⟨a, ha0, ha1, hab, hfine, t', ht'0, hAt', hcoarse,
    ((1 - a) / (1 + a)) / ((1 - A) / (1 + A)), ?_, fun m => ?_⟩
  · have : 0 < 1 - A := by linarith
    have : 0 < 1 - a := by linarith
    positivity
  · rw [hfine, hcoarse, natAbs_mul_nat, pow_mul]
    have : (1 - A) / (1 + A) ≠ 0 := div_ne_zero (by linarith) (by linarith)
    have : 1 - A ≠ 0 := by linarith
    field_simp
    rfl

/-- **`prop:helmholtz-subsampling`(1)**, in the parametrization of `prop:recursion-helmholtz`(2):
the
subsample of the sampled Laplace kernel of range `t` on `hℤ` is proportional to the kernel of the
same range `t` on `qhℤ`. -/
theorem subsampling_sampled_laplace {h : ℝ} (hh : 0 < h) {q : ℕ} (hq : 2 ≤ q) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℤ, sampledLaplace h t (q * m) = C * sampledLaplace (q * h) t m := by
  set a := Real.exp (-h / t) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := by
    rw [ha, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (div_neg_of_neg_of_pos (by linarith) ht)
  have hq0 : 0 < q := by omega
  have hA : Real.exp (-(q * h) / t) = a ^ q := by
    rw [ha, ← Real.exp_nat_mul]; congr 1; ring
  have hA0 : 0 < a ^ q := pow_pos ha0 q
  have hA1 : a ^ q < 1 := pow_lt_one₀ ha0.le ha1 hq0.ne'
  refine ⟨((1 - a) / (1 + a)) / ((1 - a ^ q) / (1 + a ^ q)), ?_, fun m => ?_⟩
  · have : 0 < 1 - a ^ q := by linarith
    have : 0 < 1 - a := by linarith
    positivity
  · simp only [sampledLaplace, ← ha, hA]
    rw [natAbs_mul_nat, pow_mul]
    have : (1 - a ^ q) / (1 + a ^ q) ≠ 0 := div_ne_zero (by linarith) (by linarith)
    have : 1 - a ^ q ≠ 0 := by linarith
    field_simp

end Pyramids
