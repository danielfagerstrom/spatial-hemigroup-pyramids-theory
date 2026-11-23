/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.SubsamplingLine

/-!
# Kernels on `ℤ^d`: associativity against a bounded function, and the line mask's recursion

Helper facts that both papers read (the split, `adr/0007`; article-kit `PROCESS.md` § 5, a helper
lemma goes in a file of the first paper that needs it). They stood in `Helmholtz/GridPrinciple.lean`
(`kconv_assoc_bdd`, `kconv_bdd`), `Helmholtz/GridPrincipleFrame.lean` (`geomKernel_rec`) and
`Helmholtz/MehrstellenSplitting.lean` (`deltaZ_sub_eq`, `hasSum_delta_mul`), files of the
computation paper, from which the theory paper's `Price/FrameStep.lean`,
`Price/BinomialRecords.lean` and `Matern/CreationGridInverse.lean` read them; moved here verbatim,
names unchanged.
-/

namespace Pyramids

open AffineHemigroup

section

variable {d : ℕ}

/-- Convolution is associative when the first two kernels are summable and the third argument is
bounded. -/
theorem kconv_assoc_bdd {lam mu nu : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu)
    (hn : ∃ C, ∀ k, |nu k| ≤ C) : kconv (kconv lam mu) nu = kconv lam (kconv mu nu) := by
  funext n
  unfold kconv
  obtain ⟨C, hC⟩ := hn
  have hF : Summable fun p : Zd d × Zd d => lam p.1 * mu (p.2 - p.1) * nu (n - p.2) := by
    refine Summable.of_norm_bounded ((summable_conv_pair hl hm).norm.mul_right C) fun p => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hC _) (norm_nonneg _)
  have e1 : ∀ m, (∑' j, lam j * mu (m - j)) * nu (n - m) =
      ∑' j, lam j * mu (m - j) * nu (n - m) := fun m => (tsum_mul_right).symm
  simp_rw [e1]
  rw [hF.tsum_comm (f := fun j m => lam j * mu (m - j) * nu (n - m))]
  congr 1
  funext j
  rw [← tsum_mul_left, ← (Equiv.addRight j).tsum_eq]
  congr 1
  funext k
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [show n - (k + j) = n - j - k by abel]
  ring

/-- The convolution of a summable kernel with a bounded function is bounded. -/
theorem kconv_bdd {lam f : Zd d → ℝ} (hl : Summable lam) (hf : ∃ C, ∀ k, |f k| ≤ C) :
    ∃ C, ∀ n, |kconv lam f n| ≤ C := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨(∑' m, |lam m|) * C, fun n => ?_⟩
  have hs : Summable fun m => |lam m| * C := hl.abs.mul_right C
  calc |kconv lam f n| = |∑' m, lam m * f (n - m)| := rfl
    _ ≤ ∑' m, |lam m * f (n - m)| := by
        have := norm_tsum_le_tsum_norm (summable_bounded_mul hl hC n).norm
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' m, |lam m| * C := by
        refine Summable.tsum_le_tsum (fun m => ?_) ?_ hs
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
        · exact (summable_bounded_mul hl hC n).abs
    _ = (∑' m, |lam m|) * C := tsum_mul_right

/-- `δ₀(m - a)`, the point mass at `a`, as an `if`. -/
theorem deltaZ_sub_eq {d : ℕ} (m a : Zd d) : deltaZ (m - a) = if m = a then 1 else 0 := by
  simp [deltaZ, sub_eq_zero]

/-- The convolution term of the point mass at `a` with weight `w`. -/
theorem hasSum_delta_mul (a n : Zd d) (u : Zd d → ℝ) (w : ℝ) :
    HasSum (fun m => w * deltaZ (m - a) * u (n - m)) (w * u (n - a)) := by
  convert hasSum_ite_eq a (w * u (n - a)) using 1
  funext m
  rw [deltaZ_sub_eq]
  split_ifs with hm
  · rw [hm, mul_one]
  · rw [mul_zero, zero_mul]

end

section

variable {a : ℝ}

/-- **The three-point recursion of the sampled Laplace mask**: with `ς = a/(1-a)²`,
`(1 + 2ς)λ(m) - ς(λ(m+1) + λ(m-1)) = δ₀(m)`. -/
theorem geomKernel_rec (ha0 : 0 < a) (ha1 : a < 1) (m : ℤ) :
    (1 + 2 * (a / (1 - a) ^ 2)) * geomKernel a m -
        a / (1 - a) ^ 2 * (geomKernel a (m + 1) + geomKernel a (m - 1)) =
      if m = 0 then 1 else 0 := by
  set k := a / (1 - a) ^ 2 with hk
  have h1 : 1 - a ≠ 0 := by linarith
  have h2 : 1 + a ≠ 0 := by linarith
  have hka : k * (1 - a) ^ 2 = a := by
    rw [hk]
    field_simp
  rw [show (1 + 2 * k) * geomKernel a m - k * (geomKernel a (m + 1) + geomKernel a (m - 1)) =
    geomKernel a m - k * (geomKernel a (m + 1) - 2 * geomKernel a m + geomKernel a (m - 1)) by
      ring]
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
end

/-! ## Points of `ℤ²` (from `Helmholtz/MehrstellenSplitting.lean`) -/

theorem zd2_eq_iff (m m' : Zd 2) : m = m' ↔ m 0 = m' 0 ∧ m 1 = m' 1 := by
  rw [funext_iff, Fin.forall_fin_two]

@[simp] theorem zbasis00 : (zbasis 0 : Zd 2) 0 = 1 := by simp [zbasis]
@[simp] theorem zbasis01 : (zbasis 0 : Zd 2) 1 = 0 := by simp [zbasis]
@[simp] theorem zbasis10 : (zbasis 1 : Zd 2) 0 = 0 := by simp [zbasis]
@[simp] theorem zbasis11 : (zbasis 1 : Zd 2) 1 = 1 := by simp [zbasis]


/-! ## Summable kernels against the grid Laplacian (from `Jet/GridJet.lean`) -/

section

open MeasureTheory Set Filter Complex

variable {d : ℕ}

/-- A bounded sequence against a summable kernel, read from the other side. -/
theorem summable_bounded_mul_right {mu : Zd d → ℝ} (hm : Summable mu) {lam : Zd d → ℝ} {C : ℝ}
    (hC : ∀ k, |lam k| ≤ C) (n : Zd d) : Summable fun m => lam m * mu (n - m) := by
  have h := summable_bounded_mul hm hC n
  rw [← (Equiv.subLeft n).summable_iff]
  refine h.congr fun m => ?_
  simp [mul_comm]

/-- `Δ_h` passes onto the summable factor of a convolution with a bounded sequence. -/
theorem gridLap_kconv_right (h : ℝ) {lam mu : Zd d → ℝ} (hm : Summable mu) {C : ℝ}
    (hC : ∀ k, |lam k| ≤ C) (n : Zd d) :
    gridLap h (kconv lam mu) n = kconv lam (gridLap h mu) n := by
  have hs : ∀ a : Zd d, Summable fun m => lam m * mu (n + a - m) := fun a =>
    summable_bounded_mul_right hm hC (n + a)
  have hs' : ∀ a : Zd d, Summable fun m => lam m * mu (n - a - m) := fun a =>
    summable_bounded_mul_right hm hC (n - a)
  have hs0 : Summable fun m => lam m * mu (n - m) := summable_bounded_mul_right hm hC n
  have hterm : ∀ i : Fin d, Summable fun m => (h ^ 2)⁻¹ * (lam m * mu (n + zbasis i - m) -
      2 * (lam m * mu (n - m)) + lam m * mu (n - zbasis i - m)) := fun i =>
    (((hs (zbasis i)).sub (hs0.mul_left 2)).add (hs' (zbasis i))).mul_left _
  unfold gridLap kconv
  have hpt : ∀ m, lam m * ((h ^ 2)⁻¹ * ∑ i, (mu (n - m + zbasis i) - 2 * mu (n - m) +
      mu (n - m - zbasis i))) = ∑ i, (h ^ 2)⁻¹ * (lam m * mu (n + zbasis i - m) -
        2 * (lam m * mu (n - m)) + lam m * mu (n - zbasis i - m)) := by
    intro m
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show n + zbasis i - m = n - m + zbasis i by abel,
      show n - zbasis i - m = n - m - zbasis i by abel]
    ring
  rw [tsum_congr hpt, Summable.tsum_finsetSum (fun i _ => hterm i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left, ((hs (zbasis i)).sub (hs0.mul_left 2)).tsum_add (hs' (zbasis i)),
    (hs (zbasis i)).tsum_sub (hs0.mul_left 2), tsum_mul_left]


end

end Pyramids
