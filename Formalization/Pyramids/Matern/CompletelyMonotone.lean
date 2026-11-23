/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.LaplaceAtoms
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Completely monotone functions without Bernstein's theorem

Blueprint: `blueprint/src/parts/04-matern.tex`, `lem:cm-log-convex` and `lem:cm-exponential-rate`.
Phase 5, wave 3b. Two consequences of Bernstein's theorem (ledger A55), proved without it and
without constructing a measure (`records/pyramids/PRICE-A55.md`, Route A):

* **(L)** `f(x + h)² ≤ f(x) f(x + 2h)` for a completely monotone `f` and `x, h > 0`
  (`completelyMonotone_sq_le_mul`). `f - f(· + h)` is again completely monotone
  (`completelyMonotone_sub_shift`), so the functional `L(Xᵏ) := f(x + kh)` on `ℝ[X]` is
  nonnegative on every `Xᵏ(1 - X)ᵐ` (`shiftFunctional_nonneg`), hence on the Bernstein polynomials.
  Mathlib's three Bernstein identities give the moments `f(x)`, `N f(x + h)`,
  `N(N - 1) f(x + 2h)` of the weights, and Cauchy–Schwarz with `N → ∞` gives (L).
* **(D)** A positive completely monotone `f` with `e^{λr} f(r) ≤ C(1 + r)ᵖ` for large `r` has
  `e^{λr} f(r)` nonincreasing on `(0,∞)` (`completelyMonotone_antitoneOn_exp_mul`): by (L) the
  ratios along an arithmetic progression are nondecreasing, and a ratio above `1` would grow
  geometrically against the polynomial bound.

Also here: complete monotonicity is local to `(0,∞)` (`IsCompletelyMonotone.congr`), closed under
sums and nonnegative multiples, holds for `e^{-y}` and for Laplace transforms `∫₁^∞ e^{-ys} w(s) ds`
of a nonnegative `w` (`isCompletelyMonotone_laplace`), and passes to `-f'`
(`IsCompletelyMonotone.neg_derivWithin`).

**What it reaches.** Lean core only.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter Polynomial
open scoped Topology Pointwise Nat

/-! ## Closure properties -/

theorem IsCompletelyMonotone.cdwa {f : ℝ → ℝ} (hf : IsCompletelyMonotone f) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioi (0 : ℝ)) : ContDiffWithinAt ℝ n f (Ioi 0) x :=
  (hf.1.contDiffWithinAt hx).of_le (by exact_mod_cast le_top)

theorem IsCompletelyMonotone.congr {f g : ℝ → ℝ} (hf : IsCompletelyMonotone f)
    (h : EqOn f g (Ioi 0)) : IsCompletelyMonotone g := by
  refine ⟨hf.1.congr fun x hx => (h hx).symm, fun n x hx => ?_⟩
  rw [← iteratedDerivWithin_congr h hx]
  exact hf.2 n x hx

theorem IsCompletelyMonotone.add {f g : ℝ → ℝ} (hf : IsCompletelyMonotone f)
    (hg : IsCompletelyMonotone g) : IsCompletelyMonotone (fun x => f x + g x) := by
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  refine ⟨hf.1.add hg.1, fun n x hx => ?_⟩
  have h := iteratedDerivWithin_add (n := n) (show x ∈ Ioi (0 : ℝ) from hx) hU (hf.cdwa n hx)
    (hg.cdwa n hx)
  rw [show (fun x => f x + g x) = f + g from rfl, h, mul_add]
  exact add_nonneg (hf.2 n x hx) (hg.2 n x hx)

theorem IsCompletelyMonotone.const_mul {f : ℝ → ℝ} (hf : IsCompletelyMonotone f) {a : ℝ}
    (ha : 0 ≤ a) : IsCompletelyMonotone (fun x => a * f x) := by
  refine ⟨hf.1.const_smul a, fun n x hx => ?_⟩
  rw [iteratedDerivWithin_const_mul (show x ∈ Ioi (0 : ℝ) from hx) isOpen_Ioi.uniqueDiffOn a
    (hf.cdwa n hx), mul_left_comm]
  exact mul_nonneg ha (hf.2 n x hx)

/-- `-f'` of a completely monotone `f` is completely monotone. -/
theorem IsCompletelyMonotone.neg_derivWithin {f : ℝ → ℝ} (hf : IsCompletelyMonotone f) :
    IsCompletelyMonotone (fun x => -derivWithin f (Ioi 0) x) := by
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (derivWithin f (Ioi 0)) (Ioi 0) :=
    hf.1.derivWithin hU (by simp)
  refine ⟨hd.neg, fun n x hx => ?_⟩
  rw [show (fun x => -derivWithin f (Ioi 0) x) = -derivWithin f (Ioi 0) from rfl,
    iteratedDerivWithin_neg, ← iteratedDerivWithin_succ']
  have := hf.2 (n + 1) x hx
  rw [pow_succ] at this
  linarith

/-- `e^{-y}` is completely monotone. -/
theorem isCompletelyMonotone_exp_neg : IsCompletelyMonotone (fun x => Real.exp (-x)) := by
  have h := (laplace_atoms_admissible_2 (ι := Unit) le_rfl (fun _ => 1) (fun _ => one_pos)
    Summable.of_finite _ fun _ => rfl).2.2.2.2.1
  refine (h.const_mul (a := 1 / 2) (by norm_num)).congr fun x _ => ?_
  simp

/-! ## The difference `f - f(· + h)` -/

/-- `(-1)ⁿ f⁽ⁿ⁾` is nonincreasing on `(0,∞)`. -/
theorem IsCompletelyMonotone.antitoneOn_iteratedDerivWithin {f : ℝ → ℝ}
    (hf : IsCompletelyMonotone f) (n : ℕ) :
    AntitoneOn (fun x => (-1 : ℝ) ^ n * iteratedDerivWithin n f (Ioi 0) x) (Ioi 0) := by
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hd : DifferentiableOn ℝ (iteratedDerivWithin n f (Ioi 0)) (Ioi 0) :=
    hf.1.differentiableOn_iteratedDerivWithin (by exact_mod_cast ENat.coe_lt_top n) hU
  have hd' := hd.const_mul ((-1 : ℝ) ^ n)
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hd'.continuousOn
    (by rw [interior_Ioi]; exact hd') fun x hx => ?_
  rw [interior_Ioi] at hx
  rw [deriv_const_mul _ ((hd x hx).differentiableAt (isOpen_Ioi.mem_nhds hx))]
  have h1 : deriv (iteratedDerivWithin n f (Ioi 0)) x =
      iteratedDerivWithin (n + 1) f (Ioi 0) x := by
    rw [iteratedDerivWithin_succ, derivWithin_of_isOpen isOpen_Ioi hx]
  rw [h1]
  have := hf.2 (n + 1) x hx
  rw [pow_succ] at this
  linarith

/-- **`f - f(· + h)` is completely monotone** for `h ≥ 0`. -/
theorem completelyMonotone_sub_shift {f : ℝ → ℝ} (hf : IsCompletelyMonotone f) {h : ℝ}
    (hh : 0 ≤ h) : IsCompletelyMonotone (fun x => f x - f (x + h)) := by
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hmaps : MapsTo (fun x : ℝ => x + h) (Ioi 0) (Ioi 0) := fun x (hx : 0 < x) =>
    show 0 < x + h by linarith
  have hsh : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (x + h)) (Ioi 0) :=
    hf.1.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => x + h).contDiffOn hmaps
  have hshift : ∀ n, ∀ x ∈ Ioi (0 : ℝ), iteratedDerivWithin n (fun x => f (x + h)) (Ioi 0) x =
      iteratedDerivWithin n f (Ioi 0) (x + h) := by
    intro n x (hx : 0 < x)
    rw [iteratedDerivWithin_comp_add_const]
    have hv : h +ᵥ Ioi (0 : ℝ) = Ioi h := by
      ext z
      simp only [mem_vadd_set, mem_Ioi, vadd_eq_add]
      constructor
      · rintro ⟨w, hw, rfl⟩; linarith
      · intro hz; exact ⟨z - h, by linarith, by ring⟩
    rw [hv]
    exact iteratedDerivWithin_congr_right_of_isOpen f n isOpen_Ioi isOpen_Ioi
      ⟨show h < x + h by linarith, show 0 < x + h by linarith⟩
  refine ⟨hf.1.sub hsh, fun n x hx => ?_⟩
  rw [show (fun x => f x - f (x + h)) = f - fun x => f (x + h) from rfl,
    iteratedDerivWithin_sub (show x ∈ Ioi (0 : ℝ) from hx) hU (hf.cdwa n hx)
      ((hsh.contDiffWithinAt hx).of_le (by exact_mod_cast le_top)), hshift n x hx, mul_sub,
    sub_nonneg]
  exact hf.antitoneOn_iteratedDerivWithin n hx (hmaps hx) (by linarith)

/-! ## The functional `L(Xᵏ) = f(x + kh)` -/

/-- **`L(p) = ∑ₖ pₖ f(x + kh)`**, a linear functional on `ℝ[X]`. -/
noncomputable def shiftFunctional (f : ℝ → ℝ) (x h : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun k => f (x + k * h) • LinearMap.id

theorem shiftFunctional_monomial (f : ℝ → ℝ) (x h : ℝ) (k : ℕ) (a : ℝ) :
    shiftFunctional f x h (monomial k a) = f (x + k * h) * a := by
  rw [shiftFunctional, Polynomial.lsum_apply, Polynomial.sum_monomial_index] <;> simp

theorem shiftFunctional_X_pow (f : ℝ → ℝ) (x h : ℝ) (k : ℕ) :
    shiftFunctional f x h (X ^ k) = f (x + k * h) := by
  rw [← monomial_one_right_eq_X_pow, shiftFunctional_monomial, mul_one]

/-- `L_{f - f(·+h)}(p) = L_f(p) - L_f(Xp)`. -/
theorem shiftFunctional_sub_shift (f : ℝ → ℝ) (x h : ℝ) (p : ℝ[X]) :
    shiftFunctional (fun y => f y - f (y + h)) x h p =
      shiftFunctional f x h p - shiftFunctional f x h (X * p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, mul_add, map_add, map_add]; ring
  | monomial k a =>
    rw [X_mul_monomial, shiftFunctional_monomial, shiftFunctional_monomial,
      shiftFunctional_monomial]
    push_cast
    ring_nf

/-- **`L(Xᵏ(1 - X)ᵐ) ≥ 0`** for a completely monotone `f`, `x > 0`, `h ≥ 0`. -/
theorem shiftFunctional_nonneg {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (m : ℕ) :
    ∀ f : ℝ → ℝ, IsCompletelyMonotone f → ∀ k : ℕ,
      0 ≤ shiftFunctional f x h (X ^ k * (1 - X) ^ m) := by
  induction m with
  | zero =>
    intro f hf k
    rw [pow_zero, mul_one, shiftFunctional_X_pow]
    have := hf.2 0 (x + k * h) (by positivity)
    simpa using this
  | succ m ih =>
    intro f hf k
    have h1 := ih _ (completelyMonotone_sub_shift hf hh) k
    rw [shiftFunctional_sub_shift] at h1
    have e : (X ^ k * (1 - X) ^ (m + 1) : ℝ[X]) =
        X ^ k * (1 - X) ^ m - X * (X ^ k * (1 - X) ^ m) := by
      ring
    rw [e, map_sub]
    exact h1

/-! ## (L): log-convexity along arithmetic progressions -/

/-- **(L)** `f(x + h)² ≤ f(x) f(x + 2h)` for a completely monotone `f`, `x > 0`, `h ≥ 0`. -/
theorem completelyMonotone_sq_le_mul {f : ℝ → ℝ} (hf : IsCompletelyMonotone f) {x h : ℝ}
    (hx : 0 < x) (hh : 0 ≤ h) : f (x + h) ^ 2 ≤ f x * f (x + 2 * h) := by
  set L := shiftFunctional f x h with hL
  have hL0 : L 1 = f x := by
    rw [← pow_zero X, hL, shiftFunctional_X_pow]; simp
  have hL1 : L X = f (x + h) := by
    rw [← pow_one X, hL, shiftFunctional_X_pow]; simp
  have hL2 : L (X ^ 2) = f (x + 2 * h) := by
    rw [hL, shiftFunctional_X_pow]; simp
  -- the Bernstein weights
  have hw : ∀ N k : ℕ, 0 ≤ L (bernsteinPolynomial ℝ N k) := by
    intro N k
    rw [bernsteinPolynomial, mul_assoc, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
    exact mul_nonneg (by positivity) (shiftFunctional_nonneg hx hh _ f hf k)
  set a0 := f x
  set a1 := f (x + h)
  set a2 := f (x + 2 * h)
  have hkey : ∀ N : ℕ, 1 ≤ N → (N : ℝ) * (a1 ^ 2 - a0 * a2) ≤ a0 * (a1 - a2) := by
    intro N hN
    set w : ℕ → ℝ := fun k => L (bernsteinPolynomial ℝ N k)
    have hs0 : ∑ k ∈ Finset.range (N + 1), w k = a0 := by
      rw [← hL0, ← bernsteinPolynomial.sum ℝ N, map_sum]
    have hs1 : ∑ k ∈ Finset.range (N + 1), (k : ℝ) * w k = N * a1 := by
      have := congrArg L (bernsteinPolynomial.sum_smul (R := ℝ) N)
      rw [map_sum, map_nsmul, hL1, nsmul_eq_mul] at this
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => by rw [map_nsmul, nsmul_eq_mul]
    have hs2 : ∑ k ∈ Finset.range (N + 1), ((k : ℝ) * (k - 1)) * w k = N * (N - 1) * a2 := by
      have := congrArg L (bernsteinPolynomial.sum_mul_smul (R := ℝ) N)
      rw [map_sum, map_nsmul, hL2, nsmul_eq_mul] at this
      have hc : ∀ k : ℕ, (((k * (k - 1) : ℕ)) : ℝ) = (k : ℝ) * (k - 1) := by
        intro k
        rcases k with _ | k
        · simp
        · push_cast [Nat.add_sub_cancel]; ring
      rw [hc] at this
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => by rw [map_nsmul, nsmul_eq_mul, hc]
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range (N + 1))
      (r := fun k => (k : ℝ) * w k) (f := w) (g := fun k => (k : ℝ) ^ 2 * w k)
      (fun k _ => hw N k) (fun k _ => mul_nonneg (by positivity) (hw N k))
      (fun k _ => le_of_eq (by ring))
    have hs3 : ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ 2 * w k = N * (N - 1) * a2 + N * a1 := by
      rw [← hs1, ← hs2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hs1, hs0, hs3] at hcs
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have : (N : ℝ) * ((N : ℝ) * (a1 ^ 2 - a0 * a2) - a0 * (a1 - a2)) ≤ 0 := by nlinarith
    nlinarith [(mul_nonpos_iff.1 this)]
  by_contra hlt
  push Not at hlt
  have hpos : 0 < a1 ^ 2 - a0 * a2 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (a0 * (a1 - a2) / (a1 ^ 2 - a0 * a2)))
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
    exact_mod_cast this.le
  have h1 := hkey N hN1
  have h2 : a0 * (a1 - a2) / (a1 ^ 2 - a0 * a2) < N := lt_of_le_of_lt (le_max_right _ _) hN
  rw [div_lt_iff₀ hpos] at h2
  linarith

/-! ## (D): the exponential rate -/

/-- **(D)** A positive completely monotone `f` with `e^{lr} f(r) ≤ C(1 + r)ᵖ` for `r ≥ R` has
`e^{lr} f(r)` nonincreasing on `(0,∞)`. -/
theorem completelyMonotone_antitoneOn_exp_mul {f : ℝ → ℝ} (hf : IsCompletelyMonotone f)
    (hpos : ∀ x, 0 < x → 0 < f x) {l C R : ℝ} {p : ℕ}
    (hb : ∀ r, R ≤ r → Real.exp (l * r) * f r ≤ C * (1 + r) ^ p) :
    AntitoneOn (fun r => Real.exp (l * r) * f r) (Ioi 0) := by
  intro x (hx : 0 < x) y (hy : 0 < y) hxy
  rcases hxy.lt_or_eq with hlt | heq
  swap
  · rw [heq]
  set h := y - x with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  set a : ℕ → ℝ := fun n => Real.exp (l * (x + n * h)) * f (x + n * h) with ha
  have hapos : ∀ n, 0 < a n := fun n => mul_pos (Real.exp_pos _) (hpos _ (by positivity))
  -- (L) along the progression
  have hL : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2) := by
    intro n
    have h1 :=
      completelyMonotone_sq_le_mul hf (x := x + n * h) (h := h) (by positivity) hh0.le
    simp only [ha]
    have e1 : x + ((n + 1 : ℕ) : ℝ) * h = x + n * h + h := by push_cast; ring
    have e2 : x + ((n + 2 : ℕ) : ℝ) * h = x + n * h + 2 * h := by push_cast; ring
    rw [e1, e2]
    have hE : Real.exp (l * (x + n * h + h)) ^ 2 =
        Real.exp (l * (x + n * h)) * Real.exp (l * (x + n * h + 2 * h)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    calc (Real.exp (l * (x + n * h + h)) * f (x + n * h + h)) ^ 2
        = Real.exp (l * (x + n * h + h)) ^ 2 * f (x + n * h + h) ^ 2 := by ring
      _ ≤ Real.exp (l * (x + n * h + h)) ^ 2 * (f (x + n * h) * f (x + n * h + 2 * h)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by rw [hE]; ring
  -- the ratios are nondecreasing
  set ρ := a 1 / a 0 with hρ
  have hratio : ∀ n, ρ * a n ≤ a (n + 1) := by
    intro n
    induction n with
    | zero => rw [hρ, div_mul_cancel₀ _ (hapos 0).ne']
    | succ n ih =>
      have h1 := hL n
      have h2 : ρ * a (n + 1) * a n ≤ a (n + 1) * a (n + 1) := by
        nlinarith [hapos n, hapos (n + 1)]
      have h3 : a (n + 1) * a (n + 1) ≤ a n * a (n + 2) := by nlinarith
      have h4 : ρ * a (n + 1) * a n ≤ a (n + 2) * a n := by linarith
      exact le_of_mul_le_mul_right h4 (hapos n)
  have hgeom : ∀ n, a 0 * ρ ^ n ≤ a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hρ0 : 0 ≤ ρ := div_nonneg (hapos 1).le (hapos 0).le
      calc a 0 * ρ ^ (n + 1) = ρ * (a 0 * ρ ^ n) := by ring
        _ ≤ ρ * a n := mul_le_mul_of_nonneg_left ih hρ0
        _ ≤ a (n + 1) := hratio n
  -- a ratio above `1` grows too fast
  change Real.exp (l * y) * f y ≤ Real.exp (l * x) * f x
  have hy' : y = x + ((1 : ℕ) : ℝ) * h := by rw [hh]; push_cast; ring
  have hx' : x = x + ((0 : ℕ) : ℝ) * h := by simp
  rw [hy']
  conv_rhs => rw [hx']
  change a 1 ≤ a 0
  by_contra hcon
  push Not at hcon
  have hρ1 : 1 < ρ := by rw [hρ, one_lt_div (hapos 0)]; exact hcon
  set K := 1 + x + h
  have hK : 0 < K := by positivity
  have htend := (tendsto_pow_const_div_const_pow_of_one_lt p hρ1).mul_const (|C| * K ^ p)
  rw [zero_mul] at htend
  obtain ⟨N, hN⟩ := (htend.eventually (gt_mem_nhds (hapos 0))).and
    (eventually_ge_atTop (max 1 (⌈R / h⌉₊))) |>.exists_forall_of_atTop
  have hNN := hN N le_rfl
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hNN.2
  have hNR : R ≤ x + N * h := by
    have h1 : R / h ≤ N :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hNN.2)
    rw [div_le_iff₀ hh0] at h1
    linarith
  have hb' := hb _ hNR
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpoly : (1 + (x + N * h)) ^ p ≤ K ^ p * (N : ℝ) ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) p
  have hup : a N ≤ |C| * (K ^ p * (N : ℝ) ^ p) :=
    hb'.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hpoly (abs_nonneg C)))
  have hlow := hgeom N
  have hρN : 0 < ρ ^ N := by positivity
  have := hNN.1
  rw [div_mul_eq_mul_div, div_lt_iff₀ hρN] at this
  nlinarith

/-- **The use of (D).** A positive `f` with `e^{lr} f(r) ≤ C(1 + r)ᵖ` for `r ≥ R` and `e^{lr} f(r)`
unbounded on `[1,∞)` is not completely monotone. -/
theorem not_isCompletelyMonotone_of_growth {f : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 < f x)
    {l C R : ℝ} {p : ℕ} (hb : ∀ r, R ≤ r → Real.exp (l * r) * f r ≤ C * (1 + r) ^ p)
    (hunb : ∀ M : ℝ, ∃ r, 1 ≤ r ∧ M < Real.exp (l * r) * f r) : ¬ IsCompletelyMonotone f := by
  intro hf
  obtain ⟨r, hr, hM⟩ := hunb (Real.exp (l * 1) * f 1)
  have := completelyMonotone_antitoneOn_exp_mul hf hpos hb
    (show (1 : ℝ) ∈ Ioi 0 from mem_Ioi.2 one_pos)
    (show r ∈ Ioi (0 : ℝ) from show (0 : ℝ) < r by linarith) hr
  linarith

/-! ## Laplace transforms on `(1,∞)` -/

/-- **`y ↦ ∫₁^∞ e^{-ys} w(s) ds` is completely monotone** for `w ≥ 0` with every transform
integrable. -/
theorem isCompletelyMonotone_laplace {w : ℝ → ℝ} (hw : ∀ s, 1 < s → 0 ≤ w s)
    (hint : ∀ y, 0 < y → IntegrableOn (fun s => Real.exp (-(y * s)) * w s) (Ioi 1)) :
    IsCompletelyMonotone (fun y => ∫ s in Ioi (1 : ℝ), Real.exp (-(y * s)) * w s) := by
  set g : ℕ → ℝ → ℝ := fun n y => ∫ s in Ioi (1 : ℝ), (-s) ^ n * (Real.exp (-(y * s)) * w s)
    with hg
  -- `sⁿe^{-ys} ≤ (n+2)!(2/y)^{n+2} e^{-ys/2}` on `s > 1`
  have hpow : ∀ n : ℕ, ∀ y, 0 < y → ∀ s : ℝ, 1 < s →
      s ^ n * Real.exp (-(y * s)) ≤ ((n + 2)! / (y / 2) ^ (n + 2)) * Real.exp (-(y / 2 * s)) := by
    intro n y hy s hs
    have h1 := pow_mul_exp_neg_le (θ := s) (x := y / 2) (by linarith) (by positivity) n
    have hs2 : (s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    have he : Real.exp (-(y * s)) = Real.exp (-(s * (y / 2))) * Real.exp (-(y / 2 * s)) := by
      rw [← Real.exp_add]; ring_nf
    rw [he, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right (h1.trans ?_) (Real.exp_pos _).le
    calc ((n + 2)! / (y / 2) ^ (n + 2)) * (s ^ 2)⁻¹ ≤ ((n + 2)! / (y / 2) ^ (n + 2)) * 1 :=
          mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = _ := mul_one _
  have hintn : ∀ n : ℕ, ∀ y, 0 < y →
      IntegrableOn (fun s => (-s) ^ n * (Real.exp (-(y * s)) * w s)) (Ioi 1) := by
    intro n y hy
    refine Integrable.mono' ((hint (y / 2) (by positivity)).const_mul
      ((n + 2)! / (y / 2) ^ (n + 2))) ?_ ?_
    · exact (continuous_pow n |>.comp continuous_neg).aestronglyMeasurable.mul
        (hint y hy).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s (hs : 1 < s) => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < s),
        abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hw s hs), ← mul_assoc, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hpow n y hy s hs) (hw s hs)
  have hgd : ∀ n y, 0 < y → HasDerivAt (g n) (g (n + 1) y) y := by
    intro n y hy
    have hy2 : 0 < y / 2 := by positivity
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 1))
      (F := fun z s => (-s) ^ n * (Real.exp (-(z * s)) * w s))
      (F' := fun z s => (-s) ^ (n + 1) * (Real.exp (-(z * s)) * w s))
      (x₀ := y) (bound := fun s => ((n + 1 + 2)! / (y / 2 / 2) ^ (n + 1 + 2)) *
        (Real.exp (-(y / 2 / 2 * s)) * w s)) (s := Ioi (y / 2)) (Ioi_mem_nhds (by linarith)) ?_
      (hintn n y hy)
      (hintn (n + 1) y hy).aestronglyMeasurable ?_
      ((hint (y / 2 / 2) (by positivity)).const_mul _) ?_
    · exact h.2
    · filter_upwards [Ioi_mem_nhds (by linarith : y / 2 < y)] with z (hz : y / 2 < z)
      exact (hintn n z (by linarith)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s (hs : 1 < s) => ?_)
      intro z (hz' : y / 2 < z)
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < s),
        abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hw s hs), ← mul_assoc, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (hw s hs)
      refine le_trans ?_ (hpow (n + 1) (y / 2) hy2 s hs)
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      nlinarith
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s _ => ?_)
      intro z _
      have h1 : HasDerivAt (fun z : ℝ => -(z * s)) (-s) z := by
        have := ((hasDerivAt_id z).mul_const s).const_mul (-1 : ℝ)
        simp only [id, one_mul, neg_one_mul] at this
        exact this
      have h2 := ((h1.exp).mul_const (w s)).const_mul ((-s) ^ n)
      exact h2.congr_deriv (by ring)
  have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hderiv : ∀ n, EqOn (derivWithin (g n) (Ioi 0)) (g (n + 1)) (Ioi 0) := by
    intro n x hx
    exact ((hgd n x hx).hasDerivWithinAt).derivWithin (hU x hx)
  have hcd : ∀ m : ℕ, ∀ n, ContDiffOn ℝ m (g n) (Ioi 0) := by
    intro m
    induction m with
    | zero =>
      intro n
      exact contDiffOn_zero.2 fun x hx => (hgd n x hx).continuousAt.continuousWithinAt
    | succ m ih =>
      intro n
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin hU]
      refine ⟨fun x hx => (hgd n x hx).differentiableAt.differentiableWithinAt,
        fun h => absurd h (by simp), ?_⟩
      exact (ih (n + 1)).congr (hderiv n)
  have hit : ∀ n, EqOn (iteratedDerivWithin n (g 0) (Ioi 0)) (g n) (Ioi 0) := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih hx)]
      exact hderiv n hx
  have hg0 : (fun y => ∫ s in Ioi (1 : ℝ), Real.exp (-(y * s)) * w s) = g 0 := by
    funext y; simp [hg]
  rw [hg0]
  refine ⟨contDiffOn_infty.2 fun m => hcd m 0, fun n x hx => ?_⟩
  rw [hit n hx]
  simp only [hg]
  rw [← integral_const_mul]
  refine setIntegral_nonneg measurableSet_Ioi fun s (hs : 1 < s) => ?_
  rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  have := hw s hs
  have : (0 : ℝ) < s := by linarith
  positivity

end Pyramids
