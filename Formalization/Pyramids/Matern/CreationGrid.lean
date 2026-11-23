/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Matern
import Pyramids.DiscreteHelmholtz
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# `prop:creation-grid`(1), (2): creation of `𝒩`-maxima on a grid

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:creation-grid`. Phase 5, wave 3b (on the VM).
`creation_grid_1` and `creation_grid_2` moved here from `PyramidsSkeleton.Ch04Matern`, their
conclusions unchanged. They no longer take `ŵ ≥ 0`, nor that `𝒩` be finite, symmetric and free of
`0`, which their proofs do not read; `creation_grid_2` takes `q ≥ 1` for `q ≥ 2` (2026-11-15, a
strengthening).

## The route

* **An axis line of mass below `1`.** If every axis line `ℤe_i` had mass `1`, `w` would be carried
  by their intersection `{0}`, as `d ≥ 2`; so `w = δ₀` (`exists_axisLine_mass_lt_one`). Call the
  mass of that line `p < 1`, and fix `θ := 2/(1 + p) ∈ (1, 1/p)`.
* **The witness** at a scale `R ∈ ℕ`, `R ≥ 1` (`creationWitnessZ`): `f = b + r` with the bump
  `b(x) := Ψ(x_i/R) e^{-|x'|₁/R}` (`|x'|₁` the `ℓ¹` norm off the axis), the profile
  `Ψ(t) := min(1 + |t|, 2e^{1-|t|})`, and the ridge `r(x) := θ max(1 - |x_i|/R, 0)` on the line
  `x' = 0`. It is positive, even and summable (it is at most a constant times `e^{-|x|₁/R}`). From
  every `x ≠ 0` one axis step strictly raises it: toward the line off it (the bump grows), along
  the line toward `0` on it (by `(θ - 1)/R` while `|x_i| ≤ R`, by the exponential beyond). And
  `f ≤ f(0) = 1 + θ`. So `0` is its only `𝒩`-maximum, for any `𝒩` holding the axis neighbours.
* **The output.** `u := w * f` is even, positive and tends to `0` at infinity (dominated
  convergence), so it attains its maximum, and a maximizer is an `𝒩`-maximum for every `𝒩`. If
  some `z` has `u(z) > u(0)`, a maximizer `x ≠ 0` exists, and `-x` is a second one. The bump moves
  by at most `min(6|y|₁/R, 2)` under a shift by `y`, and `ε(R) := ∑ w(y) min(6|y|₁/R, 2) → 0`
  (tightness, as dominated convergence). The ridge contributes at most `θp` at `0`. So
  `u(0) ≤ 1 + ε + θp` and `u(Re_i) ≥ b(Re_i) - ε = 2 - ε`, and `1 - θp = (1 - p)/(1 + p) > 2ε`
  for large `R`. With `R = qK`, the point `Re_i` is on `qℤ^d`, which gives (2).

The print's box `Q_R`, its interior maximum and the limit profile `V` are not used, nor the
Fourier bound `P ≤ P(0)`, which needed `ŵ ≥ 0`.

**What it reaches.** Lean core.
-/

set_option autoImplicit false

namespace Pyramids

open Filter Set
open scoped Topology

variable {d : ℕ}

/-! ## Elementary bounds -/

theorem abs_exp_neg_sub_le_of_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u - v| := by
  wlog huv : u ≤ v generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]
    exact this hv hu (le_of_not_ge huv)
  have h2 : Real.exp (-v) = Real.exp (-u) * Real.exp (u - v) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : u - v + 1 ≤ Real.exp (u - v) := Real.add_one_le_exp _
  have h4 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h5 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have h1 : Real.exp (-v) ≤ Real.exp (-u) := Real.exp_le_exp.2 (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), h2]
  nlinarith [mul_nonneg h5 (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 huv)]

/-- **The profile** `Ψ(t) := min(1 + |t|, 2e^{1-|t|})`: `1 + |t|` on `[-1, 1]`, `2e^{1-|t|}`
outside. -/
noncomputable def creationProfile (t : ℝ) : ℝ := min (1 + |t|) (2 * Real.exp (1 - |t|))

theorem creationProfile_of_le {t : ℝ} (ht : |t| ≤ 1) : creationProfile t = 1 + |t| := by
  refine min_eq_left ?_
  have : 1 ≤ Real.exp (1 - |t|) := Real.one_le_exp (by linarith)
  linarith

theorem creationProfile_of_ge {t : ℝ} (ht : 1 ≤ |t|) :
    creationProfile t = 2 * Real.exp (1 - |t|) := by
  refine min_eq_right ?_
  have : Real.exp (1 - |t|) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

theorem creationProfile_pos (t : ℝ) : 0 < creationProfile t :=
  lt_min (by positivity) (by positivity)

theorem creationProfile_le_two (t : ℝ) : creationProfile t ≤ 2 := by
  rcases le_total |t| 1 with h | h
  · rw [creationProfile_of_le h]; linarith
  · rw [creationProfile_of_ge h]
    have : Real.exp (1 - |t|) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith

theorem creationProfile_neg (t : ℝ) : creationProfile (-t) = creationProfile t := by
  simp [creationProfile, abs_neg]

theorem creationProfile_abs (t : ℝ) : creationProfile |t| = creationProfile t := by
  simp [creationProfile, abs_abs]

theorem creationProfile_le_exp (t : ℝ) :
    creationProfile t ≤ 2 * Real.exp 1 * Real.exp (-|t|) := by
  rw [mul_assoc, ← Real.exp_add, ← sub_eq_add_neg]
  exact min_le_right _ _

theorem abs_creationProfile_sub_le (s t : ℝ) :
    |creationProfile s - creationProfile t| ≤ 6 * |s - t| := by
  have h2 := abs_abs_sub_abs_le_abs_sub s t
  unfold creationProfile
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [show 1 + |s| - (1 + |t|) = |s| - |t| by ring]
    linarith [abs_nonneg (s - t)]
  · have h := abs_exp_neg_sub_le_of_nonneg (abs_nonneg s) (abs_nonneg t)
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [show 2 * Real.exp (1 - |s|) - 2 * Real.exp (1 - |t|) =
        2 * Real.exp 1 * (Real.exp (-|s|) - Real.exp (-|t|)) by
      rw [sub_eq_add_neg 1 |s|, sub_eq_add_neg 1 |t|, Real.exp_add, Real.exp_add]; ring]
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 2 * Real.exp 1 * |Real.exp (-|s|) - Real.exp (-|t|)|
        ≤ 2 * Real.exp 1 * |s - t| := mul_le_mul_of_nonneg_left (h.trans h2) (by positivity)
      _ ≤ 6 * |s - t| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

/-! ## Summability over `ℤ^d` of a product -/

theorem summable_prod_pi {g : ℤ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) :
    ∀ n : ℕ, Summable fun x : Fin n → ℤ => ∏ j, g (x j)
  | 0 => Summable.of_finite
  | n + 1 => by
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
    have h := Summable.mul_of_nonneg hg (summable_prod_pi hg0 hg n) hg0
      (fun x => Finset.prod_nonneg fun j _ => hg0 _)
    refine h.congr fun p => ?_
    simp [Function.comp, Fin.consEquiv, Fin.prod_univ_succ]

theorem summable_exp_neg_abs_int {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(c * |(n : ℝ)|)) := by
  have hgeo : Summable fun n : ℕ => Real.exp (-c) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (by simpa using Real.exp_lt_exp.2 (show -c < 0 by linarith))
  have hnat : Summable fun n : ℕ => Real.exp (-(c * |((n : ℤ) : ℝ)|)) := by
    refine hgeo.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    ring
  refine summable_int_iff_summable_nat_and_neg.2 ⟨hnat, hnat.congr fun n => ?_⟩
  push_cast
  rw [abs_neg]

/-- `x ↦ e^{-c|x|₁}` is summable on `ℤ^d` for `c > 0`. -/
theorem summable_exp_neg_l1 {c : ℝ} (hc : 0 < c) :
    Summable fun x : Zd d => Real.exp (-(c * ∑ j, |(x j : ℝ)|)) := by
  refine (summable_prod_pi (fun n => (Real.exp_pos _).le) (summable_exp_neg_abs_int hc) d).congr
    fun x => ?_
  rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

/-! ## An axis line of mass below one -/

/-- **The axis line** `ℤe_i`. -/
def axisLine (i : Fin d) : Set (Zd d) := {m | ∀ j, j ≠ i → m j = 0}

theorem neg_mem_axisLine {i : Fin d} {m : Zd d} : -m ∈ axisLine i ↔ m ∈ axisLine i := by
  simp only [axisLine, mem_setOf_eq, Pi.neg_apply, neg_eq_zero]

/-- **If every axis line had mass `1`, `w` would be `δ₀`** (`d ≥ 2`). -/
theorem exists_axisLine_mass_lt_one (hd : 2 ≤ d) {w : Zd d → ℝ} (hw : IsProbKernel w)
    (hne : w ≠ deltaZ) : ∃ i : Fin d, ∑' m, (axisLine i).indicator w m < 1 := by
  by_contra hcon
  push Not at hcon
  have hind : ∀ i m, (axisLine i).indicator w m ≤ w m := fun i m =>
    indicator_le_self' (fun m _ => hw.1 m) m
  have hoff : ∀ i m, m ∉ axisLine i → w m = 0 := by
    intro i m hm
    have hs : Summable fun m => w m - (axisLine i).indicator w m :=
      hw.2.1.sub (hw.2.1.indicator _)
    have hle : ∑' m, (axisLine i).indicator w m ≤ 1 := by
      rw [← hw.2.2]
      exact Summable.tsum_le_tsum (hind i) (hw.2.1.indicator _) hw.2.1
    have h0 : ∑' m, (w m - (axisLine i).indicator w m) = 0 := by
      rw [hw.2.1.tsum_sub (hw.2.1.indicator _), hw.2.2]
      linarith [hcon i]
    have hnn : ∀ m, 0 ≤ w m - (axisLine i).indicator w m := fun m => sub_nonneg.2 (hind i m)
    have h1 := congrFun ((hasSum_zero_iff_of_nonneg hnn).1 (h0 ▸ hs.hasSum)) m
    simpa [indicator_of_notMem hm] using h1
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hd
  have hz : ∀ m, m ≠ 0 → w m = 0 := by
    intro m hm
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hm
    obtain ⟨i, hij⟩ := exists_ne j
    exact hoff i m fun hm' => hj (hm' j (Ne.symm hij))
  apply hne
  funext m
  unfold deltaZ
  split_ifs with h
  · subst h
    rw [← hw.2.2, tsum_eq_single 0 fun m hm => hz m hm]
  · exact hz m h

/-! ## The maximum of a function that tends to zero -/

theorem exists_forall_le_of_tendsto_cofinite {g : Zd d → ℝ} (hg : Tendsto g cofinite (𝓝 0))
    {z : Zd d} (hz : 0 < g z) : ∃ x, ∀ y, g y ≤ g x := by
  have hfin : {y | g z ≤ g y}.Finite := by
    have := hg.eventually (gt_mem_nhds hz)
    simpa [Filter.eventually_cofinite, not_lt] using this
  obtain ⟨x, hx, hmax⟩ := hfin.toFinset.exists_max_image g ⟨z, by simp⟩
  refine ⟨x, fun y => ?_⟩
  by_cases hy : g z ≤ g y
  · exact hmax y (by simpa using hy)
  · simp only [Finite.mem_toFinset, mem_setOf_eq] at hx
    linarith [not_le.1 hy]

/-- **Two `𝒩`-maxima of an even function that tends to `0`** and exceeds its value at `0`. -/
theorem two_nmax_of_even {N : Set (Zd d)} {g : Zd d → ℝ} (heven : ∀ x, g (-x) = g x)
    (hg : Tendsto g cofinite (𝓝 0)) {z : Zd d} (hz0 : 0 < g z) (hz : g 0 < g z) :
    ∃ x y, x ≠ y ∧ IsNMax N g x ∧ IsNMax N g y := by
  obtain ⟨x, hx⟩ := exists_forall_le_of_tendsto_cofinite hg hz0
  have hx0 : x ≠ 0 := by
    rintro rfl
    linarith [hx z]
  refine ⟨x, -x, fun h => hx0 ?_, fun y _ => hx _, fun y _ => by rw [heven]; exact hx _⟩
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  omega

theorem tendsto_kconv_cofinite {w f : Zd d → ℝ} (hw : Summable w) (hf : Summable f) :
    Tendsto (kconv w f) cofinite (𝓝 0) := by
  obtain ⟨C, hC⟩ := bounded_of_summable_Z hf
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := cofinite)
    (f := fun n m => w m * f (n - m)) (g := fun _ => (0 : ℝ)) (bound := fun m => |w m| * C)
    (hw.abs.mul_right C) (fun m => ?_) (Eventually.of_forall fun n m => ?_)
  · have h' : Tendsto (fun n => ∑' m, w m * f (n - m)) cofinite (𝓝 0) := by simpa using h
    exact h'
  · have h1 : Tendsto (fun n : Zd d => n - m) cofinite cofinite :=
      sub_left_injective.tendsto_cofinite
    simpa using (hf.tendsto_cofinite_zero.comp h1).const_mul (w m)
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)

theorem kconv_neg_of_even {w f : Zd d → ℝ} (hw : ∀ n, w (-n) = w n) (hf : ∀ n, f (-n) = f n)
    (x : Zd d) : kconv w f (-x) = kconv w f x := by
  unfold kconv
  rw [← (Equiv.neg (Zd d)).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Equiv.neg_apply, hw]
  rw [← hf]
  congr 1
  abel_nf

/-! ## The witness -/

/-- `|x'|₁ := ∑_{j ≠ i} |x_j|`, the `ℓ¹` norm off the axis `i`. -/
noncomputable def offAbs (i : Fin d) (x : Zd d) : ℝ := ∑ j ∈ Finset.univ.erase i, |(x j : ℝ)|

/-- **The bump** `b(x) := Ψ(x_i/R) e^{-|x'|₁/R}`. -/
noncomputable def creationBump (i : Fin d) (R : ℝ) (x : Zd d) : ℝ :=
  creationProfile ((x i : ℝ) / R) * Real.exp (-(offAbs i x / R))

/-- **The ridge** `θ max(1 - |x_i|/R, 0)` on the axis line `ℤe_i`. -/
noncomputable def creationRidge (i : Fin d) (R θ : ℝ) (x : Zd d) : ℝ :=
  (axisLine i).indicator (fun x : Zd d => θ * max (1 - |(x i : ℝ)| / R) 0) x

/-- **The witness** of `prop:creation-grid`(1), (2): bump plus ridge. -/
noncomputable def creationWitnessZ (i : Fin d) (R θ : ℝ) (x : Zd d) : ℝ :=
  creationBump i R x + creationRidge i R θ x

theorem offAbs_nonneg (i : Fin d) (x : Zd d) : 0 ≤ offAbs i x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem offAbs_neg (i : Fin d) (x : Zd d) : offAbs i (-x) = offAbs i x := by
  simp [offAbs, abs_neg]

theorem offAbs_of_mem {i : Fin d} {x : Zd d} (hx : x ∈ axisLine i) : offAbs i x = 0 :=
  Finset.sum_eq_zero fun j hj => by
    rw [hx j (Finset.ne_of_mem_erase hj)]; simp

theorem creationBump_pos (i : Fin d) (R : ℝ) (x : Zd d) : 0 < creationBump i R x :=
  mul_pos (creationProfile_pos _) (Real.exp_pos _)

theorem creationBump_le_two (i : Fin d) {R : ℝ} (hR : 0 < R) (x : Zd d) :
    creationBump i R x ≤ 2 := by
  have h1 : Real.exp (-(offAbs i x / R)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (offAbs_nonneg i x) hR.le))
  calc creationBump i R x ≤ 2 * 1 :=
        mul_le_mul (creationProfile_le_two _) h1 (Real.exp_pos _).le (by norm_num)
    _ = 2 := mul_one 2

theorem creationRidge_nonneg (i : Fin d) (R : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (x : Zd d) :
    0 ≤ creationRidge i R θ x :=
  indicator_nonneg (fun _ _ => mul_nonneg hθ (le_max_right _ _)) x

theorem creationRidge_of_notMem {i : Fin d} {R θ : ℝ} {x : Zd d} (hx : x ∉ axisLine i) :
    creationRidge i R θ x = 0 :=
  indicator_of_notMem hx _

theorem creationRidge_of_mem {i : Fin d} {R θ : ℝ} {x : Zd d} (hx : x ∈ axisLine i) :
    creationRidge i R θ x = θ * max (1 - |(x i : ℝ)| / R) 0 :=
  indicator_of_mem hx _

theorem creationWitnessZ_pos (i : Fin d) (R : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) (x : Zd d) :
    0 < creationWitnessZ i R θ x :=
  add_pos_of_pos_of_nonneg (creationBump_pos i R x) (creationRidge_nonneg i R hθ x)

theorem creationWitnessZ_neg (i : Fin d) (R θ : ℝ) (x : Zd d) :
    creationWitnessZ i R θ (-x) = creationWitnessZ i R θ x := by
  unfold creationWitnessZ creationBump
  have h1 : ((-x) i : ℝ) / R = -((x i : ℝ) / R) := by push_cast [Pi.neg_apply]; ring
  rw [h1, creationProfile_neg, offAbs_neg]
  congr 1
  by_cases hx : x ∈ axisLine i
  · rw [creationRidge_of_mem hx, creationRidge_of_mem (neg_mem_axisLine.2 hx)]
    simp [abs_neg]
  · rw [creationRidge_of_notMem hx, creationRidge_of_notMem (mt neg_mem_axisLine.1 hx)]

theorem sum_abs_eq_add_offAbs (i : Fin d) (x : Zd d) :
    ∑ j, |(x j : ℝ)| = |(x i : ℝ)| + offAbs i x :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

theorem creationWitnessZ_le_exp (i : Fin d) {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) (x : Zd d) :
    creationWitnessZ i R θ x ≤ (2 + θ) * Real.exp 1 * Real.exp (-(R⁻¹ * ∑ j, |(x j : ℝ)|)) := by
  have hE : Real.exp (-(R⁻¹ * ∑ j, |(x j : ℝ)|)) =
      Real.exp (-|(x i : ℝ) / R|) * Real.exp (-(offAbs i x / R)) := by
    rw [← Real.exp_add, sum_abs_eq_add_offAbs, abs_div, abs_of_pos hR, div_eq_inv_mul,
      div_eq_inv_mul]
    ring_nf
  have hb : creationBump i R x ≤ 2 * Real.exp 1 * Real.exp (-(R⁻¹ * ∑ j, |(x j : ℝ)|)) := by
    rw [hE, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (creationProfile_le_exp _) (Real.exp_pos _).le
  have hr : creationRidge i R θ x ≤ θ * Real.exp 1 * Real.exp (-(R⁻¹ * ∑ j, |(x j : ℝ)|)) := by
    by_cases hx : x ∈ axisLine i
    · rw [creationRidge_of_mem hx, hE, offAbs_of_mem hx, zero_div, neg_zero, Real.exp_zero,
        mul_one, mul_assoc]
      refine mul_le_mul_of_nonneg_left (max_le ?_ (by positivity)) hθ
      rw [← Real.exp_add, abs_div, abs_of_pos hR]
      have := Real.add_one_le_exp (1 + -(|(x i : ℝ)| / R))
      have h0 : 0 ≤ |(x i : ℝ)| / R := div_nonneg (abs_nonneg _) hR.le
      linarith
    · rw [creationRidge_of_notMem hx]
      positivity
  unfold creationWitnessZ
  linarith

theorem summable_creationWitnessZ (i : Fin d) {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) :
    Summable (creationWitnessZ i R θ) :=
  Summable.of_nonneg_of_le (fun x => (creationWitnessZ_pos i R hθ x).le)
    (creationWitnessZ_le_exp i hR hθ) ((summable_exp_neg_l1 (inv_pos.2 hR)).mul_left _)

/-! ### Values and the shift bound -/

theorem creationBump_zero (i : Fin d) (R : ℝ) : creationBump i R 0 = 1 := by
  simp [creationBump, offAbs, creationProfile_of_le]

theorem creationWitnessZ_zero (i : Fin d) (R θ : ℝ) : creationWitnessZ i R θ 0 = 1 + θ := by
  rw [creationWitnessZ, creationBump_zero, creationRidge_of_mem (by simp [axisLine])]
  simp

/-- The point `Re_i`. -/
theorem creationBump_axis (i : Fin d) {K : ℕ} (hK : 0 < K) :
    creationBump i (K : ℝ) ((K : ℤ) • zbasis i) = 2 := by
  have hx : ((K : ℤ) • zbasis i : Zd d) ∈ axisLine i := fun j hj => by
    simp [zbasis, hj]
  have hi : ((((K : ℤ) • zbasis i : Zd d) i : ℤ) : ℝ) = K := by simp [zbasis]
  rw [creationBump, offAbs_of_mem hx, hi, div_self (by positivity), creationProfile_of_le
    (by norm_num)]
  norm_num

theorem abs_creationBump_shift_le (i : Fin d) {R : ℝ} (hR : 0 < R) (x m : Zd d) :
    |creationBump i R (x - m) - creationBump i R x| ≤
      min (6 * (∑ j, |(m j : ℝ)|) / R) 2 := by
  refine le_min ?_ ?_
  · set P' := creationProfile (((x - m) i : ℤ) / R)
    set P := creationProfile ((x i : ℝ) / R)
    set E' := Real.exp (-(offAbs i (x - m) / R))
    set E := Real.exp (-(offAbs i x / R))
    have hP : |P' - P| ≤ 6 * (|(m i : ℝ)| / R) := by
      refine (abs_creationProfile_sub_le _ _).trans (le_of_eq ?_)
      congr 1
      rw [← sub_div, abs_div, abs_of_pos hR]
      have : (((x - m) i : ℤ) : ℝ) - (x i : ℝ) = -(m i : ℝ) := by
        push_cast [Pi.sub_apply]; ring
      rw [this, abs_neg]
    have hoff : |offAbs i (x - m) - offAbs i x| ≤ offAbs i m := by
      unfold offAbs
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      have := abs_abs_sub_abs_le_abs_sub ((x - m) j : ℝ) (x j : ℝ)
      push_cast [Pi.sub_apply] at this ⊢
      rw [show (x j : ℝ) - (m j : ℝ) - (x j : ℝ) = -(m j : ℝ) by ring, abs_neg] at this
      exact this
    have hE : |E' - E| ≤ offAbs i m / R := by
      refine (abs_exp_neg_sub_le_of_nonneg (div_nonneg (offAbs_nonneg _ _) hR.le)
        (div_nonneg (offAbs_nonneg _ _) hR.le)).trans ?_
      rw [← sub_div, abs_div, abs_of_pos hR]
      exact div_le_div_of_nonneg_right hoff hR.le
    have hE1 : E' ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (offAbs_nonneg i _) hR.le))
    have hE0 : 0 ≤ E' := (Real.exp_pos _).le
    have hP2 : P ≤ 2 := creationProfile_le_two _
    have hP0 : 0 ≤ P := (creationProfile_pos _).le
    have hsplit : P' * E' - P * E = (P' - P) * E' + P * (E' - E) := by ring
    have h1 : |P' * E' - P * E| ≤ |P' - P| * 1 + 2 * |E' - E| := by
      rw [hsplit]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_nonneg hE0]
        exact mul_le_mul_of_nonneg_left hE1 (abs_nonneg _)
      · rw [abs_mul, abs_of_nonneg hP0]
        exact mul_le_mul_of_nonneg_right hP2 (abs_nonneg _)
    have hsum := sum_abs_eq_add_offAbs i m
    have hdiv : 6 * (∑ j, |(m j : ℝ)|) / R = 6 * (|(m i : ℝ)| / R) + 6 * (offAbs i m / R) := by
      rw [hsum]; ring
    have ho : 0 ≤ offAbs i m / R := div_nonneg (offAbs_nonneg _ _) hR.le
    change |P' * E' - P * E| ≤ _
    rw [hdiv]
    linarith
  · have h1 := creationBump_pos i R (x - m)
    have h2 := creationBump_pos i R x
    have h3 := creationBump_le_two i hR (x - m)
    have h4 := creationBump_le_two i hR x
    rw [abs_le]
    constructor <;> linarith

/-! ### One `𝒩`-maximum -/

theorem creationWitnessZ_le_zero (i : Fin d) {K : ℕ} (hK : 0 < K) {θ : ℝ} (hθ : 1 < θ)
    (x : Zd d) : creationWitnessZ i K θ x ≤ creationWitnessZ i K θ 0 := by
  have hR : (0 : ℝ) < K := by exact_mod_cast hK
  rw [creationWitnessZ_zero]
  by_cases hx : x ∈ axisLine i
  · rw [creationWitnessZ, creationRidge_of_mem hx, creationBump, offAbs_of_mem hx, zero_div,
      neg_zero, Real.exp_zero, mul_one]
    have ha : |(x i : ℝ) / K| = |(x i : ℝ)| / K := by rw [abs_div, abs_of_pos hR]
    rcases le_total (|(x i : ℝ)| / K) 1 with h | h
    · rw [creationProfile_of_le (ha ▸ h), ha, max_eq_left (by linarith)]
      have h0 : 0 ≤ |(x i : ℝ)| / K := div_nonneg (abs_nonneg _) hR.le
      nlinarith
    · rw [max_eq_right (by linarith)]
      linarith [creationProfile_le_two ((x i : ℝ) / K)]
  · rw [creationWitnessZ, creationRidge_of_notMem hx]
    linarith [creationBump_le_two i hR x]

theorem exists_axis_step_gt (i : Fin d) {K : ℕ} (hK : 0 < K) {θ : ℝ} (hθ : 1 < θ) {x : Zd d}
    (hx0 : x ≠ 0) :
    ∃ s ∈ axisNbrs d, creationWitnessZ i K θ x < creationWitnessZ i K θ (x + s) := by
  have hR : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases hx : x ∈ axisLine i
  · -- along the line, toward `0`
    have hxi : x i ≠ 0 := by
      intro h
      apply hx0
      funext k
      by_cases hk : k = i
      · subst hk; exact h
      · exact hx k hk
    set s : Zd d := if 0 < x i then -zbasis i else zbasis i with hs
    have hsN : s ∈ axisNbrs d := by
      rw [hs]; split_ifs
      · exact ⟨i, Or.inr rfl⟩
      · exact ⟨i, Or.inl rfl⟩
    have hxs : x + s ∈ axisLine i := fun j hj => by
      rw [hs]; split_ifs <;> simp [zbasis, hj, hx j hj]
    have habs : |((x + s) i : ℝ)| = |(x i : ℝ)| - 1 := by
      rw [hs]
      split_ifs with h
      · simp only [Pi.add_apply, Pi.neg_apply, zbasis, Pi.single_eq_same]
        have : (0 : ℝ) < x i := by exact_mod_cast h
        push_cast
        rw [abs_of_pos this, abs_of_nonneg (by
          have : (1 : ℤ) ≤ x i := h
          have : (1 : ℝ) ≤ x i := by exact_mod_cast this
          linarith)]
        ring
      · simp only [Pi.add_apply, zbasis, Pi.single_eq_same]
        have h' : x i < 0 := lt_of_le_of_ne (not_lt.1 h) hxi
        have : (x i : ℝ) ≤ -1 := by
          have : x i ≤ -1 := by omega
          exact_mod_cast this
        push_cast
        rw [abs_of_neg (show (x i : ℝ) < 0 by linarith),
          abs_of_nonpos (show (x i : ℝ) + 1 ≤ 0 by linarith)]
        ring
    have hval : ∀ y : Zd d, y ∈ axisLine i → creationWitnessZ i K θ y =
        creationProfile (|(y i : ℝ)| / K) + θ * max (1 - |(y i : ℝ)| / K) 0 := by
      intro y hy
      rw [creationWitnessZ, creationRidge_of_mem hy, creationBump, offAbs_of_mem hy, zero_div,
        neg_zero, Real.exp_zero, mul_one]
      rw [show |(y i : ℝ)| / K = |(y i : ℝ) / K| by rw [abs_div, abs_of_pos hR],
        creationProfile_abs]
    have hone : (1 : ℝ) ≤ |(x i : ℝ)| := by
      have : (1 : ℤ) ≤ |x i| := Int.one_le_abs hxi
      rw [← Int.cast_abs]; exact_mod_cast this
    refine ⟨s, hsN, ?_⟩
    rw [hval x hx, hval _ hxs, habs]
    set a := |(x i : ℝ)|
    by_cases haK : a ≤ K
    · have h1 : |a / K| ≤ 1 := by
        rw [abs_div, abs_of_nonneg (by linarith), abs_of_pos hR, div_le_one hR]; exact haK
      have h2 : |(a - 1) / K| ≤ 1 := by
        rw [abs_div, abs_of_nonneg (by linarith), abs_of_pos hR, div_le_one hR]; linarith
      rw [creationProfile_of_le h1, creationProfile_of_le h2, abs_div, abs_div,
        abs_of_nonneg (show 0 ≤ a by linarith), abs_of_nonneg (show 0 ≤ a - 1 by linarith),
        abs_of_pos hR, max_eq_left (by rw [sub_nonneg, div_le_one hR]; exact haK),
        max_eq_left (by rw [sub_nonneg, div_le_one hR]; linarith)]
      have : (a - 1) / K = a / K - 1 / K := by ring
      rw [this]
      have hK1 : 0 < 1 / (K : ℝ) := by positivity
      nlinarith
    · -- `a > K`, so `a - 1 ≥ K` as both are integers
      have haK' : (K : ℝ) + 1 ≤ a := by
        have h1 : ((K : ℤ) : ℝ) < ((|x i| : ℤ) : ℝ) := by
          push_cast; exact lt_of_not_ge haK
        have h2 : (K : ℤ) + 1 ≤ |x i| := by exact_mod_cast h1
        have h3 : (((K : ℤ) + 1 : ℤ) : ℝ) ≤ ((|x i| : ℤ) : ℝ) := by exact_mod_cast h2
        push_cast at h3
        exact h3
      have h1 : 1 ≤ |a / K| := by
        rw [abs_div, abs_of_nonneg (by linarith), abs_of_pos hR, le_div_iff₀ hR]; linarith
      have h2 : 1 ≤ |(a - 1) / K| := by
        rw [abs_div, abs_of_nonneg (by linarith), abs_of_pos hR, le_div_iff₀ hR]; linarith
      rw [creationProfile_of_ge h1, creationProfile_of_ge h2,
        max_eq_right (show 1 - a / K ≤ 0 by rw [sub_nonpos, le_div_iff₀ hR]; linarith)]
      have h3 : 0 ≤ θ * max (1 - (a - 1) / K) 0 := mul_nonneg (by linarith) (le_max_right _ _)
      have h4 : Real.exp (1 - |a / K|) < Real.exp (1 - |(a - 1) / K|) := by
        refine Real.exp_lt_exp.2 ?_
        rw [abs_div, abs_div, abs_of_nonneg (show 0 ≤ a by linarith),
          abs_of_nonneg (show 0 ≤ a - 1 by linarith), abs_of_pos hR]
        have : (a - 1) / K < a / K := div_lt_div_of_pos_right (by linarith) hR
        linarith
      linarith
  · -- off the line, toward it
    obtain ⟨j, hji, hxj⟩ : ∃ j, j ≠ i ∧ x j ≠ 0 := by
      by_contra h
      push Not at h
      exact hx h
    set s : Zd d := if 0 < x j then -zbasis j else zbasis j with hs
    have hsN : s ∈ axisNbrs d := by
      rw [hs]; split_ifs
      · exact ⟨j, Or.inr rfl⟩
      · exact ⟨j, Or.inl rfl⟩
    have hsk : ∀ k, k ≠ j → (x + s) k = x k := fun k hk => by
      rw [hs]; split_ifs <;> simp [zbasis, hk]
    have habs : |((x + s) j : ℝ)| = |(x j : ℝ)| - 1 := by
      rw [hs]
      split_ifs with h
      · simp only [Pi.add_apply, Pi.neg_apply, zbasis, Pi.single_eq_same]
        have : (1 : ℝ) ≤ x j := by
          have : (1 : ℤ) ≤ x j := h
          exact_mod_cast this
        push_cast
        rw [abs_of_pos (show (0 : ℝ) < x j by linarith),
          abs_of_nonneg (show (0 : ℝ) ≤ x j + -1 by linarith)]
        ring
      · simp only [Pi.add_apply, zbasis, Pi.single_eq_same]
        have h' : x j < 0 := lt_of_le_of_ne (not_lt.1 h) hxj
        have : (x j : ℝ) ≤ -1 := by
          have : x j ≤ -1 := by omega
          exact_mod_cast this
        push_cast
        rw [abs_of_neg (show (x j : ℝ) < 0 by linarith),
          abs_of_nonpos (show (x j : ℝ) + 1 ≤ 0 by linarith)]
        ring
    have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩
    have hoff : offAbs i (x + s) = offAbs i x - 1 := by
      unfold offAbs
      rw [← Finset.add_sum_erase _ _ hj, ← Finset.add_sum_erase _ _ hj, habs]
      have : ∑ k ∈ (Finset.univ.erase i).erase j, |(((x + s) k : ℤ) : ℝ)| =
          ∑ k ∈ (Finset.univ.erase i).erase j, |((x k : ℤ) : ℝ)| :=
        Finset.sum_congr rfl fun k hk => by rw [hsk k (Finset.ne_of_mem_erase hk)]
      rw [this]
      ring
    refine ⟨s, hsN, ?_⟩
    unfold creationWitnessZ
    rw [creationRidge_of_notMem hx, add_zero]
    have hb : creationBump i K (x + s) > creationBump i K x := by
      unfold creationBump
      rw [hsk i (Ne.symm hji), hoff]
      refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) (creationProfile_pos _)
      have : (offAbs i x - 1) / K < offAbs i x / K := div_lt_div_of_pos_right (by linarith) hR
      linarith
    linarith [creationRidge_nonneg i (K : ℝ) (by linarith : (0 : ℝ) ≤ θ) (x + s)]

theorem creationWitnessZ_unique_nmax (i : Fin d) {K : ℕ} (hK : 0 < K) {θ : ℝ} (hθ : 1 < θ)
    {N : Set (Zd d)} (haxis : axisNbrs d ⊆ N) : ∃! x, IsNMax N (creationWitnessZ i K θ) x := by
  refine ⟨0, fun y _ => creationWitnessZ_le_zero i hK hθ _, fun x hx => ?_⟩
  by_contra hx0
  obtain ⟨s, hsN, hlt⟩ := exists_axis_step_gt i hK hθ hx0
  exact absurd (hx s (haxis hsN)) (not_le.2 hlt)

/-! ### The output at `0` and at `Re_i` -/

/-- `ε(R) := ∑ w(y) min(6|y|₁/R, 2)`. -/
noncomputable def creationErr (w : Zd d → ℝ) (R : ℝ) : ℝ :=
  ∑' m, w m * min (6 * (∑ j, |(m j : ℝ)|) / R) 2

theorem summable_creationErr_term {w : Zd d → ℝ} (hw : IsProbKernel w) {R : ℝ} (hR : 0 < R) :
    Summable fun m => w m * min (6 * (∑ j, |(m j : ℝ)|) / R) 2 := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg (hw.1 m) (le_min (by positivity)
    (by norm_num))) (fun m => mul_le_mul_of_nonneg_left (min_le_right _ _) (hw.1 m))
    (hw.2.1.mul_right 2)

theorem tendsto_creationErr {w : Zd d → ℝ} (hw : IsProbKernel w) :
    Tendsto (creationErr w) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun R m => w m * min (6 * (∑ j, |(m j : ℝ)|) / R) 2) (g := fun _ => (0 : ℝ))
    (bound := fun m => w m * 2) (hw.2.1.mul_right 2) (fun m => ?_) ?_
  · have h' : Tendsto (fun R => ∑' m, w m * min (6 * (∑ j, |(m j : ℝ)|) / R) 2) atTop (𝓝 0) := by
      simpa using h
    exact h'
  · have h1 : Tendsto (fun R : ℝ => 6 * (∑ j, |(m j : ℝ)|) / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (h1.min (tendsto_const_nhds (x := (2 : ℝ)))).const_mul (w m)
    simpa using h2
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR m
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw.1 m) (le_min (by positivity)
      (by norm_num)))]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hw.1 m)

theorem kconv_creationWitnessZ_zero_le (i : Fin d) {w : Zd d → ℝ} (hw : IsProbKernel w)
    {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) :
    kconv w (creationWitnessZ i R θ) 0 ≤
      1 + creationErr w R + θ * ∑' m, (axisLine i).indicator w m := by
  have hf := summable_creationWitnessZ i hR hθ
  obtain ⟨C, hC⟩ := bounded_of_summable_Z hf
  have hs1 := summable_bounded_mul hw.2.1 hC 0
  have hs2 := summable_creationErr_term hw hR
  have hs3 := (hw.2.1.indicator (axisLine i)).mul_left θ
  have hle : ∀ m, w m * creationWitnessZ i R θ (0 - m) ≤
      (w m + w m * min (6 * (∑ j, |(m j : ℝ)|) / R) 2) + θ * (axisLine i).indicator w m := by
    intro m
    have hb := abs_creationBump_shift_le i hR 0 m
    rw [creationBump_zero] at hb
    have hb' : creationBump i R (0 - m) ≤ 1 + min (6 * (∑ j, |(m j : ℝ)|) / R) 2 := by
      linarith [le_abs_self (creationBump i R (0 - m) - 1)]
    have hr : w m * creationRidge i R θ (0 - m) ≤ θ * (axisLine i).indicator w m := by
      by_cases hm : m ∈ axisLine i
      · have hm' : (0 : Zd d) - m ∈ axisLine i := by rw [zero_sub]; exact neg_mem_axisLine.2 hm
        rw [creationRidge_of_mem hm', indicator_of_mem hm]
        have : max (1 - |(((0 : Zd d) - m) i : ℝ)| / R) 0 ≤ 1 := max_le (by
          have : 0 ≤ |(((0 : Zd d) - m) i : ℝ)| / R := div_nonneg (abs_nonneg _) hR.le
          linarith) zero_le_one
        nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hθ (hw.1 m))]
      · have hm' : (0 : Zd d) - m ∉ axisLine i := by
          rw [zero_sub]; exact mt neg_mem_axisLine.1 hm
        rw [creationRidge_of_notMem hm', indicator_of_notMem hm]
        simp
    unfold creationWitnessZ
    rw [mul_add]
    have := mul_le_mul_of_nonneg_left hb' (hw.1 m)
    linarith
  calc kconv w (creationWitnessZ i R θ) 0 = ∑' m, w m * creationWitnessZ i R θ (0 - m) := rfl
    _ ≤ ∑' m, ((w m + w m * min (6 * (∑ j, |(m j : ℝ)|) / R) 2) +
          θ * (axisLine i).indicator w m) :=
        Summable.tsum_le_tsum hle hs1 ((hw.2.1.add hs2).add hs3)
    _ = 1 + creationErr w R + θ * ∑' m, (axisLine i).indicator w m := by
        rw [(hw.2.1.add hs2).tsum_add hs3, hw.2.1.tsum_add hs2, hw.2.2, tsum_mul_left]
        rfl

theorem kconv_creationWitnessZ_axis_ge (i : Fin d) {w : Zd d → ℝ} (hw : IsProbKernel w)
    {K : ℕ} (hK : 0 < K) {θ : ℝ} (hθ : 0 ≤ θ) :
    2 - creationErr w K ≤ kconv w (creationWitnessZ i K θ) ((K : ℤ) • zbasis i) := by
  have hR : (0 : ℝ) < K := by exact_mod_cast hK
  have hf := summable_creationWitnessZ i hR hθ
  obtain ⟨C, hC⟩ := bounded_of_summable_Z hf
  have hs1 := summable_bounded_mul hw.2.1 hC ((K : ℤ) • zbasis i)
  have hs2 := summable_creationErr_term hw hR
  have hle : ∀ m, 2 * w m - w m * min (6 * (∑ j, |(m j : ℝ)|) / K) 2 ≤
      w m * creationWitnessZ i K θ ((K : ℤ) • zbasis i - m) := by
    intro m
    have hb := abs_creationBump_shift_le i hR ((K : ℤ) • zbasis i) m
    rw [creationBump_axis i hK] at hb
    have hb' : 2 - min (6 * (∑ j, |(m j : ℝ)|) / K) 2 ≤
        creationBump i K ((K : ℤ) • zbasis i - m) := by
      linarith [neg_abs_le (creationBump i K ((K : ℤ) • zbasis i - m) - 2)]
    have := mul_le_mul_of_nonneg_left hb' (hw.1 m)
    have hr := mul_nonneg (hw.1 m) (creationRidge_nonneg i (K : ℝ) hθ ((K : ℤ) • zbasis i - m))
    unfold creationWitnessZ
    rw [mul_add]
    linarith
  calc 2 - creationErr w K = ∑' m, (2 * w m - w m * min (6 * (∑ j, |(m j : ℝ)|) / K) 2) := by
        rw [(hw.2.1.mul_left 2).tsum_sub hs2, tsum_mul_left, hw.2.2, mul_one]
        rfl
    _ ≤ ∑' m, w m * creationWitnessZ i K θ ((K : ℤ) • zbasis i - m) :=
        Summable.tsum_le_tsum hle ((hw.2.1.mul_left 2).sub hs2) hs1
    _ = _ := rfl

/-! ## `prop:creation-grid`(1), (2) -/

/-- **`prop:creation-grid`(2).** For an integer `q ≥ 1`, `f` can be chosen so that, besides (1),
`(w * f)|_{qhℤ^d}` has at least two `q𝒩`-maxima (in the coarse grid's indices, two `𝒩`-maxima of
`m ↦ (w * f)(qm)`). No `ŵ ≥ 0`, and `𝒩` need only contain the axis neighbours (2026-11-15, a
strengthening: the skeleton also asked `ŵ ≥ 0`, `𝒩` finite, symmetric and free of `0`, and
`q ≥ 2`). -/
theorem creation_grid_2 (hd : 2 ≤ d) (w : Zd d → ℝ) (hw : IsProbKernel w)
    (hsymm : ∀ n, w (-n) = w n) (hne : w ≠ deltaZ)
    (N : Set (Zd d)) (haxis : axisNbrs d ⊆ N) (q : ℕ) (hq : 1 ≤ q) :
    ∃ f : Zd d → ℝ, (∀ n, 0 < f n) ∧ Summable f ∧ (∃! x, IsNMax N f x) ∧
      (∃ x y, x ≠ y ∧ IsNMax N (kconv w f) x ∧ IsNMax N (kconv w f) y) ∧
      ∃ x y, x ≠ y ∧ IsNMax N (fun m => kconv w f ((q : ℤ) • m)) x ∧
        IsNMax N (fun m => kconv w f ((q : ℤ) • m)) y := by
  obtain ⟨i, hp⟩ := exists_axisLine_mass_lt_one hd hw hne
  set p := ∑' m, (axisLine i).indicator w m with hpdef
  have hp0 : 0 ≤ p := tsum_nonneg fun m => indicator_nonneg (fun m _ => hw.1 m) m
  set θ : ℝ := 2 / (1 + p) with hθdef
  have hθ1 : 1 < θ := by rw [hθdef, lt_div_iff₀ (by linarith)]; linarith
  have hθ0 : 0 ≤ θ := by linarith
  have hδ : 0 < 1 - θ * p := by
    rw [hθdef, div_mul_eq_mul_div, sub_pos, div_lt_one (by linarith)]; linarith
  -- a scale `K'` with `ε(qK') < (1 - θp)/2`
  have hqK : Tendsto (fun K : ℕ => ((q * K : ℕ) : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp ?_
    exact tendsto_id.const_mul_atTop' (by omega)
  obtain ⟨K', hK'1, hK'ε⟩ := ((eventually_ge_atTop 1).and
    (((tendsto_creationErr hw).comp hqK).eventually (gt_mem_nhds (half_pos hδ)))).exists
  set K : ℕ := q * K' with hKdef
  have hK : 0 < K := Nat.mul_pos (by omega) (by omega)
  have hR : (0 : ℝ) < K := by exact_mod_cast hK
  have hε : creationErr w K < (1 - θ * p) / 2 := hK'ε
  set f := creationWitnessZ i (K : ℝ) θ with hfdef
  have hfs : Summable f := summable_creationWitnessZ i hR hθ0
  have hfe : ∀ n, f (-n) = f n := creationWitnessZ_neg i _ _
  set u := kconv w f with hudef
  have hue : ∀ x, u (-x) = u x := kconv_neg_of_even hsymm hfe
  have hut : Tendsto u cofinite (𝓝 0) := tendsto_kconv_cofinite hw.2.1 hfs
  have hu0 : u 0 ≤ 1 + creationErr w K + θ * p := kconv_creationWitnessZ_zero_le i hw hR hθ0
  have huK : 2 - creationErr w K ≤ u ((K : ℤ) • zbasis i) :=
    kconv_creationWitnessZ_axis_ge i hw hK hθ0
  have hεn : 0 ≤ creationErr w K :=
    tsum_nonneg fun m => mul_nonneg (hw.1 m) (le_min (by positivity) (by norm_num))
  have hlt : u 0 < u ((K : ℤ) • zbasis i) := by
    nlinarith
  have hpos : 0 < u ((K : ℤ) • zbasis i) := by
    linarith [mul_nonneg hθ0 hp0]
  refine ⟨f, creationWitnessZ_pos i _ hθ0, hfs, creationWitnessZ_unique_nmax i hK hθ1 haxis,
    two_nmax_of_even hue hut hpos hlt, ?_⟩
  -- the coarse grid
  have hinj : Function.Injective fun m : Zd d => (q : ℤ) • m := by
    intro a b hab
    funext k
    have := congrFun hab k
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ (by exact_mod_cast (show q ≠ 0 by omega)) this
  have hz : (q : ℤ) • ((K' : ℤ) • zbasis i : Zd d) = (K : ℤ) • zbasis i := by
    rw [smul_smul, hKdef]; push_cast; rfl
  refine two_nmax_of_even (z := (K' : ℤ) • zbasis i) (fun x => ?_)
    (hut.comp hinj.tendsto_cofinite) ?_ ?_
  · simp only [smul_neg]
    exact hue _
  · simp only [hz]; exact hpos
  · simp only [hz, smul_zero]; exact hlt

/-- **`prop:creation-grid`(1).** For a symmetric probability `w ≠ δ₀` on `hℤ^d` and an `𝒩`
containing the axis neighbours, a summable `f > 0` with exactly one `𝒩`-maximum has `w * f` with
at least two. No `ŵ ≥ 0`, and `𝒩` need not be finite, symmetric or free of `0` (2026-11-15, a
strengthening). -/
theorem creation_grid_1 (hd : 2 ≤ d) (w : Zd d → ℝ) (hw : IsProbKernel w)
    (hsymm : ∀ n, w (-n) = w n) (hne : w ≠ deltaZ)
    (N : Set (Zd d)) (haxis : axisNbrs d ⊆ N) :
    ∃ f : Zd d → ℝ, (∀ n, 0 < f n) ∧ Summable f ∧ (∃! x, IsNMax N f x) ∧
      ∃ x y, x ≠ y ∧ IsNMax N (kconv w f) x ∧ IsNMax N (kconv w f) y := by
  obtain ⟨f, h1, h2, h3, h4, -⟩ := creation_grid_2 hd w hw hsymm hne N haxis 1 le_rfl
  exact ⟨f, h1, h2, h3, h4⟩

end Pyramids
