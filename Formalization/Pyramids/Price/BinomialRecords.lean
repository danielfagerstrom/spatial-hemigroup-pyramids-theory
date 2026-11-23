/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Price.CreationGridMasks

/-!
# `prop:binomial-records`: the records of the binomial masks

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:binomial-records`. Phase 5, wave 3b. The two
declarations are the skeleton's (`PyramidsSkeleton/Ch05Price.lean`), unchanged in name and
conclusion. Their binders are fewer (dropped on 2026-11-15, a strengthening): `_1` takes no
`2 ≤ d`, and `_2` takes no finiteness or symmetry of `𝒩` and no `0 ∉ 𝒩`, which
`records_creation` does not read.

* **The subsampled mask** `s(j) := β(qj)` is carried by `{-1, 0, 1}`: it is
  `(δ₋₁ + 6δ₀ + δ₁)/16` at `q = 2` and `(6/16)δ₀` at `q ≥ 3`. Its inverse on `ℤ` is explicit
  (`binomSubInv`): `2√2 ρ^{|n|}` with `ρ = 2√2 - 3`, a root of `ρ² + 6ρ + 1 = 0`, at `q = 2`, and
  `(16/6)δ₀` at `q ≥ 3`. This replaces the print's Neumann series.
* **The tensor inverse.** `s^{⊗d}` is carried by the box `{-1, 0, 1}^d`, so its convolution with
  a tensor kernel is a finite sum over the box, which factors into `d` line convolutions
  (`Finset.prod_univ_sum`, as for `kconv_tensorIdx_lineInv`). So `s^{⊗d} * g^{⊗d} = δ₀`, and
  `g^{⊗d}` is summable, its absolute value being a tensor of a summable kernel.
* **One step.** For a bounded `A`, `V := g^{⊗d} * A` is bounded and `s^{⊗d} * V = A`
  (`kconv_assoc_bdd`). The input `u` is `V` placed on `qℤ^d` and `0` elsewhere
  (`Function.extend`); the sum `(w * u)(qm)` runs over `qℤ^d` (`Function.Injective.tsum_eq`), where
  `w(q(m - m')) = s^{⊗d}(m - m')`.
* **(1)** by induction on `k`, the recursion of `decimRecord`; **(2)** is `records_creation`.
-/

namespace Pyramids

variable {d : ℕ}

/-! ## The subsampled mask and its inverse on the line -/

/-- **The subsample** `s(j) := β(qj)` of the binomial mask on `qℤ`. -/
noncomputable def binomSub (q : ℕ) (j : ℤ) : ℝ := binomialMask5 ((q : ℤ) * j)

/-- `ρ := 2√2 - 3`, the root of `ρ² + 6ρ + 1 = 0` in `(-1, 0)`. -/
noncomputable def binomRho : ℝ := 2 * Real.sqrt 2 - 3

/-- **The inverse of the subsampled mask** on `ℤ`: `2√2 ρ^{|n|}` at `q = 2`, `(16/6)δ₀` at
`q ≠ 2`. -/
noncomputable def binomSubInv (q : ℕ) (n : ℤ) : ℝ :=
  if q = 2 then 2 * Real.sqrt 2 * binomRho ^ n.natAbs else if n = 0 then 16 / 6 else 0

theorem binomSub_eq_zero {q : ℕ} (hq : 2 ≤ q) {j : ℤ} (hj : j ∉ triple) : binomSub q j = 0 := by
  simp only [triple, Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  refine binomialMask5_eq_zero ?_
  rw [Finset.mem_Icc, not_and_or, not_le, not_le]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  rcases lt_or_gt_of_ne hj.2.1 with h | h
  · have : j ≤ -2 := by omega
    left; nlinarith
  · have : 2 ≤ j := by omega
    right; nlinarith

theorem binomRho_sq : binomRho ^ 2 + 6 * binomRho + 1 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  simp only [binomRho]
  linear_combination 4 * h

theorem abs_binomRho_lt_one : |binomRho| < 1 := by
  have h1 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h2 : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [abs_lt]; constructor <;> simp only [binomRho] <;> linarith

/-- **The line identity** `∑_{j ∈ {-1,0,1}} s(j) g(n - j) = δ₀(n)`. -/
theorem sum_triple_binomSub {q : ℕ} (hq : 2 ≤ q) (n : ℤ) :
    ∑ j ∈ triple, binomSub q j * binomSubInv q (n - j) = if n = 0 then 1 else 0 := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := binomialMask5_vals
  simp only [triple]
  rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  simp only [binomSub, mul_neg, mul_one, mul_zero, sub_neg_eq_add, sub_zero]
  rcases eq_or_lt_of_le hq with rfl | hq3
  · simp only [binomSubInv, if_true, Nat.cast_ofNat]
    norm_num [b1, b3, b5]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hr := binomRho_sq
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · have e1 : (n + 1).natAbs + 1 = n.natAbs := by omega
      have e2 : (n - 1).natAbs = n.natAbs + 1 := by omega
      rw [if_neg hn.ne, e2, ← e1]
      linear_combination (2 * Real.sqrt 2 * binomRho ^ (n + 1).natAbs / 16) * hr
    · norm_num [binomRho]
      linear_combination (1 / 2 : ℝ) * hs
    · have e1 : (n - 1).natAbs + 1 = n.natAbs := by omega
      have e2 : (n + 1).natAbs = n.natAbs + 1 := by omega
      rw [if_neg hn.ne', e2, ← e1]
      linear_combination (2 * Real.sqrt 2 * binomRho ^ (n - 1).natAbs / 16) * hr
  · have hq2 : q ≠ 2 := by omega
    have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
    have hz1 : binomialMask5 (q : ℤ) = 0 := binomialMask5_eq_zero (by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le]; right; linarith)
    have hz2 : binomialMask5 (-(q : ℤ)) = 0 := binomialMask5_eq_zero (by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le]; left; linarith)
    rw [hz1, hz2]
    simp only [binomSubInv, hq2, if_false, b3]
    split_ifs <;> norm_num

theorem summable_abs_binomSubInv (q : ℕ) : Summable fun n => |binomSubInv q n| := by
  by_cases hq : q = 2
  · have hs := (summable_pow_natAbs_of_nonneg (abs_nonneg binomRho)
      abs_binomRho_lt_one).mul_left (2 * Real.sqrt 2)
    refine hs.congr fun n => ?_
    simp only [binomSubInv, hq, if_true, abs_mul, abs_pow, abs_two,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    simp [binomSubInv, hq, hn]

/-! ## The tensors -/

/-- The tensor of the subsample vanishes off the box `{-1, 0, 1}^d`. -/
theorem tensorIdx_binomSub_eq_zero {q : ℕ} (hq : 2 ≤ q) {m : Zd d}
    (hm : m ∉ Fintype.piFinset fun _ : Fin d => triple) : tensorIdx (binomSub q) m = 0 := by
  rw [Fintype.mem_piFinset, not_forall] at hm
  obtain ⟨i, hi⟩ := hm
  exact Finset.prod_eq_zero (Finset.mem_univ i) (binomSub_eq_zero hq hi)

/-- **The tensor inverse**: `s^{⊗d} * g^{⊗d} = δ₀`, a finite sum over the box factored into the
`d` line identities. -/
theorem kconv_tensorIdx_binomSub {q : ℕ} (hq : 2 ≤ q) :
    kconv (tensorIdx (d := d) (binomSub q)) (tensorIdx (binomSubInv q)) = deltaZ := by
  classical
  funext n
  unfold kconv
  rw [tsum_eq_sum (s := Fintype.piFinset fun _ : Fin d => triple) fun m hm => by
    rw [tensorIdx_binomSub_eq_zero hq hm, zero_mul]]
  have h : ∏ i, ∑ j ∈ triple, binomSub q j * binomSubInv q (n i - j) =
      ∑ m ∈ Fintype.piFinset fun _ : Fin d => triple,
        tensorIdx (binomSub q) m * tensorIdx (binomSubInv q) (n - m) := by
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [tensorIdx, ← Finset.prod_mul_distrib, Pi.sub_apply]
  rw [← h]
  simp_rw [sum_triple_binomSub hq]
  rw [Finset.prod_boole]
  simp only [deltaZ, Finset.mem_univ, true_implies, funext_iff, Pi.zero_apply]

theorem summable_tensorIdx_binomSubInv (q : ℕ) :
    Summable (tensorIdx (d := d) (binomSubInv q)) := by
  refine Summable.of_norm_bounded
    (summable_tensorIdx (fun n => abs_nonneg _) (summable_abs_binomSubInv q)) fun n => ?_
  simp only [tensorIdx, Real.norm_eq_abs, Finset.abs_prod, le_refl]

/-- The binomial tensor mask on `qℤ^d` is the tensor of the subsample. -/
theorem tensorIdx_binomialMask5_smul (q : ℕ) (m : Zd d) :
    tensorIdx binomialMask5 ((q : ℤ) • m) = tensorIdx (binomSub q) m := by
  simp [tensorIdx, binomSub]

/-! ## One step, and every level -/

/-- **One step.** For an integer `q ≥ 2`, every bounded array `A` is `m ↦ (β^{⊗d} * u)(qm)` for a
bounded `u`. -/
theorem binomial_records_step {q : ℕ} (hq : 2 ≤ q) (A : Zd d → ℝ)
    (hA : ∃ C : ℝ, ∀ m, |A m| ≤ C) :
    ∃ u : Zd d → ℝ, (∃ C : ℝ, ∀ n, |u n| ≤ C) ∧
      ∀ m, kconv (tensorIdx binomialMask5) u ((q : ℤ) • m) = A m := by
  classical
  set S := tensorIdx (d := d) (binomSub q)
  set R := tensorIdx (d := d) (binomSubInv q)
  have hS : Summable S := summable_of_ne_finset_zero fun _ hm => tensorIdx_binomSub_eq_zero hq hm
  have hR : Summable R := summable_tensorIdx_binomSubInv q
  set V := kconv R A
  obtain ⟨CV, hCV⟩ := kconv_bdd hR hA
  have hSV : kconv S V = A := by
    rw [← kconv_assoc_bdd hS hR hA, kconv_tensorIdx_binomSub hq, kconv_deltaZ_left]
  set e : Zd d → Zd d := fun m => (q : ℤ) • m
  have he : Function.Injective e := fun a b hab => by
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    exact smul_right_injective _ hq0 hab
  obtain ⟨u, hu⟩ : ∃ u, u = Function.extend e V 0 := ⟨_, rfl⟩
  refine ⟨u, ⟨max CV 0, fun n => ?_⟩, fun m => ?_⟩
  · by_cases hn : ∃ a, e a = n
    · obtain ⟨a, rfl⟩ := hn
      rw [hu, he.extend_apply]
      exact (hCV a).trans (le_max_left _ _)
    · rw [hu, Function.extend_apply' _ _ _ hn]
      simp
  · rw [kconv_comm]
    unfold kconv
    have hsupp : Function.support (fun n => u n * tensorIdx binomialMask5 (e m - n)) ⊆
        Set.range e := fun n hn => by
      by_contra hr
      apply hn
      simp only [hu, Function.extend_apply' _ _ _ (fun h => hr h), Pi.zero_apply, zero_mul]
    rw [← he.tsum_eq hsupp, ← hSV, kconv_comm]
    unfold kconv
    refine tsum_congr fun m' => ?_
    rw [hu, he.extend_apply]
    simp only [e, ← smul_sub, tensorIdx_binomialMask5_smul]
    rfl

/-- **`prop:binomial-records`(1).** For `w = β^{⊗d}` and an integer `q ≥ 2`, every bounded array
on `q^k hℤ^d` is the level-`k` record of a bounded input on `hℤ^d`, for every `k ≥ 0`. The node
reads it for `d ≥ 2`; the proof reads no bound on `d` (dropped on 2026-11-15, a strengthening). -/
theorem binomial_records_1 {q : ℕ} (hq : 2 ≤ q) (k : ℕ) (A : Zd d → ℝ)
    (hA : ∃ C : ℝ, ∀ m, |A m| ≤ C) :
    ∃ f : Zd d → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) ∧
      decimRecord (tensorIdx binomialMask5) q f k = A := by
  induction k generalizing A with
  | zero => exact ⟨A, hA, rfl⟩
  | succ k ih =>
    obtain ⟨u, hu, huA⟩ := binomial_records_step hq A hA
    obtain ⟨f, hf, hfu⟩ := ih u hu
    refine ⟨f, hf, ?_⟩
    funext m
    simp only [decimRecord, hfu, huA]

/-- **`prop:binomial-records`(2).** For `w = β^{⊗d}`, some bounded input has a level-`k` record
with exactly one `𝒩`-maximum, whose smoothing by `D_{q^k} w` has at least two, and a
level-`(k+1)` record with at least two. The node reads it for a finite symmetric `𝒩 ∌ 0`; the proof
reads only that `𝒩` contains the axis neighbours (dropped on 2026-11-15, a strengthening). -/
theorem binomial_records_2 (hd : 2 ≤ d) {q : ℕ} (hq : 2 ≤ q) (k : ℕ) (N : Set (Zd d))
    (haxis : axisNbrs d ⊆ N) :
    ∃ f : Zd d → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) ∧
      (∃! x, IsNMax N (decimRecord (tensorIdx binomialMask5) q f k) x) ∧
      (∃ x y, x ≠ y ∧
        IsNMax N (kconv (tensorIdx binomialMask5) (decimRecord (tensorIdx binomialMask5) q f k))
          x ∧
        IsNMax N (kconv (tensorIdx binomialMask5) (decimRecord (tensorIdx binomialMask5) q f k))
          y) ∧
      ∃ x y, x ≠ y ∧ IsNMax N (decimRecord (tensorIdx binomialMask5) q f (k + 1)) x ∧
        IsNMax N (decimRecord (tensorIdx binomialMask5) q f (k + 1)) y := by
  have h0 : binomialMask5 0 < 1 := by rw [binomialMask5_vals.2.2.1]; norm_num
  exact records_creation hd (by omega) k _
    (isProbKernel_tensorIdx binomialMask5_nonneg hasSum_binomialMask5)
    (tensorIdx_neg binomialMask5_neg)
    (tensorIdx_ne_deltaZ binomialMask5_nonneg (by omega) h0) N haxis
    fun A hA => binomial_records_1 hq k A hA

end Pyramids
