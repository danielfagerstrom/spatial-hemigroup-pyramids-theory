/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.RecursionHelmholtz
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# `prop:discrete-helmholtz`: the discrete Helmholtz family on `hℤ^d`

Blueprint: `blueprint/src/parts/05-price.tex` (moved from the computation chapter at the split,
`adr/0007`), `prop:discrete-helmholtz`. Wave 2, group J, Q-0281.

Kernels on `ℤ^d` are summable functions; their convolution is commutative, associative and
distributes over linear combinations, and the Fourier series of a convolution is the product of the
Fourier series. The kernel `κ_t = (1-p)∑ₖ pᵏσ^{*k}` is a probability kernel with transfer
`(1 + t²D_h)⁻¹`, and `κ_t * σ = (κ_t - (1-p)δ₀)/p` turns into `(1 - t²Δ_h)κ_t = δ₀`. A bounded
solution of `(1 - t²Δ_h)e = 0` vanishes by the maximum principle: `e(n)` is `p` times the mean of
its `2d` neighbours, so `sup|e| ≤ p sup|e|`. The cascade is the resolvent identity
`κ_t * κ_s = (t²κ_t - s²κ_s)/(t² - s²)`, checked by that uniqueness, which makes the one-step
mixtures compose. The symbol bound is Taylor's formula at order six, through the four elementary
inequalities between `sin`, `cos` and their Taylor polynomials; the line is the uniqueness of
`prop:recursion-helmholtz`(2).
-/

namespace Pyramids

open AffineHemigroup

open MeasureTheory Set Filter Complex
open scoped Topology

variable {d : ℕ}

/-! ## Kernels on `ℤ^d` -/

section Kernels

theorem summable_deltaZ : Summable (deltaZ (d := d)) := by
  have := hasSum_ite_eq (0 : Zd d) (1 : ℝ)
  exact this.summable.congr fun n => by simp [deltaZ]

theorem tsum_deltaZ : ∑' n, deltaZ (d := d) n = 1 := by
  rw [show deltaZ (d := d) = fun n => if n = 0 then (1 : ℝ) else 0 from rfl, tsum_ite_eq]

theorem isProbKernel_deltaZ : IsProbKernel (deltaZ (d := d)) :=
  ⟨fun n => by unfold deltaZ; split_ifs <;> norm_num, summable_deltaZ, tsum_deltaZ⟩

/-- The pairs `(m, n) ↦ λ(m)μ(n - m)` form a summable family. -/
theorem summable_conv_pair {lam mu : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu) :
    Summable fun p : Zd d × Zd d => lam p.1 * mu (p.2 - p.1) := by
  have h := summable_mul_of_summable_norm hl.norm hm.norm
  let e : Zd d × Zd d ≃ Zd d × Zd d :=
    { toFun := fun p => (p.1, p.2 + p.1)
      invFun := fun p => (p.1, p.2 - p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  rw [← e.summable_iff]
  refine h.congr fun p => ?_
  simp [e]

theorem summable_kconv_term {lam mu : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu) (n : Zd d) :
    Summable fun m => lam m * mu (n - m) :=
  (summable_conv_pair hl hm).prod_symm.prod_factor n

theorem summable_kconv {lam mu : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu) :
    Summable (kconv lam mu) :=
  (summable_conv_pair hl hm).prod_symm.prod

theorem tsum_kconv {lam mu : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu) :
    ∑' n, kconv lam mu n = (∑' n, lam n) * ∑' n, mu n := by
  have h := summable_conv_pair hl hm
  unfold kconv
  rw [h.tsum_comm (f := fun m n => lam m * mu (n - m)), ← tsum_mul_right]
  congr 1
  funext m
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.subRight m).tsum_eq mu

theorem isProbKernel_kconv {lam mu : Zd d → ℝ} (hl : IsProbKernel lam) (hm : IsProbKernel mu) :
    IsProbKernel (kconv lam mu) :=
  ⟨fun n => tsum_nonneg fun m => mul_nonneg (hl.1 m) (hm.1 _), summable_kconv hl.2.1 hm.2.1,
    by rw [tsum_kconv hl.2.1 hm.2.1, hl.2.2, hm.2.2, one_mul]⟩

theorem kconv_comm (lam mu : Zd d → ℝ) : kconv lam mu = kconv mu lam := by
  funext n
  unfold kconv
  rw [← (Equiv.subLeft n).tsum_eq]
  congr 1
  funext m
  simp [mul_comm]

theorem kconv_deltaZ_left (mu : Zd d → ℝ) : kconv deltaZ mu = mu := by
  funext n
  unfold kconv deltaZ
  simp only [ite_mul, one_mul, zero_mul]
  rw [tsum_ite_eq, sub_zero]

theorem kconv_deltaZ_right (mu : Zd d → ℝ) : kconv mu deltaZ = mu := by
  rw [kconv_comm, kconv_deltaZ_left]

/-- Convolution is linear in its first argument. -/
theorem kconv_add_smul_left {lam lam' mu : Zd d → ℝ} (hl : Summable lam) (hl' : Summable lam')
    (hm : Summable mu) (a b : ℝ) :
    kconv (fun n => a * lam n + b * lam' n) mu =
      fun n => a * kconv lam mu n + b * kconv lam' mu n := by
  funext n
  unfold kconv
  rw [← tsum_mul_left, ← tsum_mul_left, ← ((summable_kconv_term hl hm n).mul_left a).tsum_add
    ((summable_kconv_term hl' hm n).mul_left b)]
  congr 1
  funext m
  ring

theorem kconv_assoc {lam mu nu : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu)
    (hn : Summable nu) : kconv (kconv lam mu) nu = kconv lam (kconv mu nu) := by
  funext n
  unfold kconv
  -- `∑ₘ (∑ⱼ λⱼ μ_{m-j}) ν_{n-m} = ∑ⱼ λⱼ ∑ₖ μₖ ν_{n-j-k}`
  have hF : Summable fun p : Zd d × Zd d => lam p.1 * mu (p.2 - p.1) * nu (n - p.2) := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ k, ‖nu k‖ ≤ C :=
      ⟨∑' k, ‖nu k‖, fun k => hn.norm.le_tsum k fun _ _ => norm_nonneg _⟩
    refine Summable.of_norm_bounded ((summable_conv_pair hl hm).norm.mul_right C) fun p => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
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

theorem summable_bounded_mul {lam : Zd d → ℝ} (hl : Summable lam) {mu : Zd d → ℝ} {C : ℝ}
    (hC : ∀ k, |mu k| ≤ C) (n : Zd d) : Summable fun m => lam m * mu (n - m) := by
  refine Summable.of_norm_bounded (hl.norm.mul_right C) fun m => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)

/-- A summable kernel is bounded. -/
theorem bounded_of_summable_Z {e : Zd d → ℝ} (hs : Summable e) : ∃ C, ∀ n, |e n| ≤ C :=
  ⟨∑' m, |e m|, fun n => hs.abs.le_tsum n fun _ _ => abs_nonneg _⟩

end Kernels

/-! ## Fourier series on `ℤ^d` -/

section Fourier

/-- The phase `⟨n, ϑ⟩`. -/
noncomputable def gphase (θ : Fin d → ℝ) (n : Zd d) : ℝ := ∑ i, (n i : ℝ) * θ i

theorem gphase_add (θ : Fin d → ℝ) (m k : Zd d) :
    gphase θ (m + k) = gphase θ m + gphase θ k := by
  simp only [gphase, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

theorem gridFourier_eq (lam : Zd d → ℝ) (θ : Fin d → ℝ) :
    gridFourier lam θ = ∑' n, (lam n : ℂ) * cexp ((gphase θ n : ℂ) * I) := rfl

theorem norm_cexp_gphase (θ : Fin d → ℝ) (n : Zd d) : ‖cexp ((gphase θ n : ℂ) * I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem summable_fourier_term {lam : Zd d → ℝ} (hl : Summable lam) (θ : Fin d → ℝ) :
    Summable fun n => (lam n : ℂ) * cexp ((gphase θ n : ℂ) * I) :=
  Summable.of_norm (hl.norm.congr fun n => by
    rw [norm_mul, norm_cexp_gphase, mul_one, Complex.norm_real])

/-- **The Fourier series of a convolution is the product.** -/
theorem gridFourier_kconv {lam mu : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu)
    (θ : Fin d → ℝ) :
    gridFourier (kconv lam mu) θ = gridFourier lam θ * gridFourier mu θ := by
  rw [gridFourier_eq, gridFourier_eq, gridFourier_eq]
  set e : Zd d → ℂ := fun n => cexp ((gphase θ n : ℂ) * I) with he
  have hemul : ∀ m k, e (m + k) = e m * e k := fun m k => by
    simp only [he, gphase_add]; push_cast; rw [← Complex.exp_add]; ring_nf
  have hF : Summable fun p : Zd d × Zd d => (lam p.1 : ℂ) * (mu (p.2 - p.1) : ℂ) * e p.2 := by
    refine Summable.of_norm ((summable_conv_pair hl hm).norm.congr fun p => ?_)
    simp only [he, norm_mul, norm_cexp_gphase, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have e1 : ∀ n, ((kconv lam mu n : ℝ) : ℂ) * e n = ∑' m, (lam m : ℂ) * (mu (n - m) : ℂ) * e n := by
    intro n
    rw [kconv, Complex.ofReal_tsum, ← tsum_mul_right]
    congr 1
    funext m
    push_cast
    ring
  change ∑' n, ((kconv lam mu n : ℝ) : ℂ) * e n = (∑' n, (lam n : ℂ) * e n) * ∑' n, (mu n : ℂ) * e n
  simp_rw [e1]
  rw [hF.tsum_comm (f := fun m n => (lam m : ℂ) * (mu (n - m) : ℂ) * e n), ← tsum_mul_right]
  congr 1
  funext m
  rw [← tsum_mul_left, ← (Equiv.addRight m).tsum_eq]
  congr 1
  funext k
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [hemul]
  ring

theorem gridFourier_deltaZ (θ : Fin d → ℝ) : gridFourier (deltaZ (d := d)) θ = 1 := by
  rw [gridFourier_eq]
  have : ∀ n : Zd d, ((deltaZ n : ℝ) : ℂ) * cexp ((gphase θ n : ℂ) * I) =
      if n = 0 then 1 else 0 := by
    intro n
    unfold deltaZ
    split_ifs with h
    · subst h; simp [gphase]
    · simp
  simp_rw [this]
  rw [tsum_ite_eq]

/-- The Fourier series is linear. -/
theorem gridFourier_add_smul {lam mu : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu) (a b : ℝ)
    (θ : Fin d → ℝ) :
    gridFourier (fun n => a * lam n + b * mu n) θ =
      (a : ℂ) * gridFourier lam θ + (b : ℂ) * gridFourier mu θ := by
  rw [gridFourier_eq, gridFourier_eq, gridFourier_eq, ← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_fourier_term hl θ).mul_left (a : ℂ)).tsum_add
      ((summable_fourier_term hm θ).mul_left (b : ℂ))]
  congr 1
  funext n
  push_cast
  ring

end Fourier

/-! ## The random walk step -/

section RandomWalk

theorem zbasis_ne_neg (i : Fin d) : zbasis i ≠ -zbasis i := by
  intro h
  have := congrFun h i
  simp [zbasis] at this

theorem rwStep_nonneg (n : Zd d) : 0 ≤ rwStep n := by
  unfold rwStep
  refine Finset.sum_nonneg fun i _ => div_nonneg ?_ (by positivity)
  split_ifs <;> norm_num

/-- `∑ₘ u(m)σ(n - m) = (2d)⁻¹ ∑ᵢ (u(n - eᵢ) + u(n + eᵢ))`. -/
theorem hasSum_mul_rwStep (u : Zd d → ℝ) (n : Zd d) :
    HasSum (fun m => u m * rwStep (n - m))
      (∑ i, (u (n - zbasis i) + u (n + zbasis i)) / (2 * d)) := by
  have hpt : ∀ m, u m * rwStep (n - m) = ∑ i, ((if m = n - zbasis i then
      u (n - zbasis i) / (2 * d) else 0) + (if m = n + zbasis i then u (n + zbasis i) / (2 * d)
        else 0)) := by
    intro m
    unfold rwStep
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (n - m = zbasis i) ↔ (m = n - zbasis i) :=
      ⟨fun h => by rw [← h]; abel, fun h => by rw [h]; abel⟩
    have h2 : (n - m = -zbasis i) ↔ (m = n + zbasis i) := by
      constructor <;> intro h
      · rw [show m = n - (n - m) by abel, h]; abel
      · rw [h]; abel
    by_cases hm1 : m = n - zbasis i
    · have hm2 : ¬ m = n + zbasis i := by
        intro h
        have := congrFun (hm1.symm.trans h) i
        simp only [zbasis, Pi.sub_apply, Pi.add_apply, Pi.single_eq_same] at this
        omega
      rw [if_pos (h1.2 hm1), if_neg (fun h => hm2 (h2.1 h)), if_pos hm1, if_neg hm2, hm1]
      ring
    · rw [if_neg (fun h => hm1 (h1.1 h)), if_neg hm1]
      by_cases hm2 : m = n + zbasis i
      · rw [if_pos (h2.2 hm2), if_pos hm2, hm2]; ring
      · rw [if_neg (fun h => hm2 (h2.1 h)), if_neg hm2]; ring
  simp_rw [hpt]
  refine hasSum_sum fun i _ => ?_
  rw [show (u (n - zbasis i) + u (n + zbasis i)) / (2 * d) =
    u (n - zbasis i) / (2 * d) + u (n + zbasis i) / (2 * d) by ring]
  exact (hasSum_ite_eq _ _).add (hasSum_ite_eq _ _)

theorem kconv_rwStep (u : Zd d → ℝ) (n : Zd d) :
    kconv u rwStep n = ∑ i, (u (n - zbasis i) + u (n + zbasis i)) / (2 * d) :=
  (hasSum_mul_rwStep u n).tsum_eq

theorem summable_rwStep : Summable (rwStep (d := d)) := by
  have h := (hasSum_mul_rwStep (d := d) (fun _ => (1 : ℝ)) 0).summable
  refine ((Equiv.neg (Zd d)).summable_iff.1 ?_)
  refine h.congr fun m => ?_
  simp

theorem isProbKernel_rwStep (hd : 1 ≤ d) : IsProbKernel (rwStep (d := d)) := by
  refine ⟨rwStep_nonneg, summable_rwStep, ?_⟩
  have h := (hasSum_mul_rwStep (d := d) (fun _ => (1 : ℝ)) 0).tsum_eq
  simp only [one_mul, zero_sub] at h
  rw [← (Equiv.neg (Zd d)).tsum_eq] at h
  simp only [Equiv.neg_apply, neg_neg] at h
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  field_simp
  ring

theorem gphase_zbasis (θ : Fin d → ℝ) (i : Fin d) : gphase θ (zbasis i) = θ i := by
  unfold gphase zbasis
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem gphase_neg (θ : Fin d → ℝ) (n : Zd d) : gphase θ (-n) = -gphase θ n := by
  simp [gphase, Finset.sum_neg_distrib]

/-- `σ̂(ϑ) = d⁻¹ ∑ᵢ cos ϑᵢ`. -/
theorem gridFourier_rwStep (θ : Fin d → ℝ) :
    gridFourier (rwStep (d := d)) θ = ((∑ i, Real.cos (θ i) / d : ℝ) : ℂ) := by
  set e : Zd d → ℂ := fun n => cexp ((gphase θ n : ℂ) * I) with he
  rw [gridFourier_eq]
  have hc : HasSum (fun n => ((rwStep n : ℝ) : ℂ) * e n)
      (∑ i, (e (zbasis i) + e (-zbasis i)) / (2 * d)) := by
    have hpt : ∀ n, ((rwStep n : ℝ) : ℂ) * e n = ∑ i, ((if n = zbasis i then e (zbasis i) / (2 * d)
        else 0) + (if n = -zbasis i then e (-zbasis i) / (2 * d) else 0)) := by
      intro n
      unfold rwStep
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h1 : n = zbasis i
      · have h2 : ¬ n = -zbasis i := by rw [h1]; exact zbasis_ne_neg i
        rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, h1]
        simp only [Complex.ofReal_one, Complex.ofReal_zero]; ring
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : n = -zbasis i
        · rw [if_pos h2, if_pos h2, h2]
          simp only [Complex.ofReal_one, Complex.ofReal_zero]; ring
        · rw [if_neg h2, if_neg h2]
          simp only [Complex.ofReal_zero]; ring
    simp_rw [hpt]
    refine hasSum_sum fun i _ => ?_
    rw [add_div]
    exact (hasSum_ite_eq _ _).add (hasSum_ite_eq _ _)
  rw [hc.tsum_eq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [he, gphase_neg, gphase_zbasis]
  rw [Complex.cos]
  push_cast
  ring_nf

end RandomWalk

/-! ## Convolution powers -/

section Kpow

theorem isProbKernel_kpow {lam : Zd d → ℝ} (hl : IsProbKernel lam) :
    ∀ k, IsProbKernel (kpow lam k)
  | 0 => isProbKernel_deltaZ
  | k + 1 => isProbKernel_kconv (isProbKernel_kpow hl k) hl

theorem summable_kpow {lam : Zd d → ℝ} (hl : Summable lam) : ∀ k, Summable (kpow lam k)
  | 0 => summable_deltaZ
  | k + 1 => summable_kconv (summable_kpow hl k) hl

theorem gridFourier_kpow {lam : Zd d → ℝ} (hl : Summable lam) (θ : Fin d → ℝ) :
    ∀ k, gridFourier (kpow lam k) θ = gridFourier lam θ ^ k
  | 0 => by rw [pow_zero]; exact gridFourier_deltaZ θ
  | k + 1 => by
    rw [kpow, gridFourier_kconv (summable_kpow hl k) hl, gridFourier_kpow hl θ k, pow_succ]

theorem kpow_kconv {lam mu : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu) :
    ∀ k, kconv (kpow lam k) (kpow mu k) = kpow (kconv lam mu) k
  | 0 => kconv_deltaZ_left _
  | k + 1 => by
    have hA := summable_kpow hl k
    have hB := summable_kpow hm k
    rw [kpow, kpow, kpow, ← kpow_kconv hl hm k]
    -- `(A * λ) * (B * μ) = (A * B) * (λ * μ)`
    rw [kconv_assoc hA hl (summable_kconv hB hm), ← kconv_assoc hl hB hm, kconv_comm lam,
      kconv_assoc hB hl hm, ← kconv_assoc hA hB (summable_kconv hl hm)]

end Kpow

/-! ## The discrete Laplacian -/

section Lap

theorem gridLap_eq (h : ℝ) (u : Zd d → ℝ) (n : Zd d) :
    gridLap h u n = (h ^ 2)⁻¹ * (2 * d * kconv u rwStep n - 2 * d * u n) := by
  rw [kconv_rwStep, gridLap]
  congr 1
  calc ∑ i, (u (n + zbasis i) - 2 * u n + u (n - zbasis i))
      = ∑ i, ((u (n - zbasis i) + u (n + zbasis i)) - 2 * u n) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, (u (n - zbasis i) + u (n + zbasis i)) - 2 * d * u n := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
    _ = 2 * d * ∑ i, (u (n - zbasis i) + u (n + zbasis i)) / (2 * d) - 2 * d * u n := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := i.2; omega)
        field_simp

theorem gridLap_lin (h a b : ℝ) (u v : Zd d → ℝ) (n : Zd d) :
    gridLap h (fun m => a * u m + b * v m) n = a * gridLap h u n + b * gridLap h v n := by
  simp only [gridLap, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The maximum principle**: a bounded solution of `(1 - t²Δ_h)e = 0` vanishes. -/
theorem helm_grid_unique {h t : ℝ} (hh : 0 < h) (ht : 0 < t) {e : Zd d → ℝ}
    (hb : ∃ C, ∀ n, |e n| ≤ C) (he : ∀ n, e n - t ^ 2 * gridLap h e n = 0) : e = 0 := by
  obtain ⟨C, hC⟩ := hb
  set c := t ^ 2 / h ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hbdd : BddAbove (Set.range fun n => |e n|) := ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩
  set M := ⨆ n, |e n| with hM
  have hle : ∀ n, |e n| ≤ M := fun n => le_ciSup hbdd n
  have hM0 : 0 ≤ M := (abs_nonneg (e 0)).trans (hle 0)
  have key : ∀ n, |e n| * (1 + 2 * d * c) ≤ 2 * d * c * M := by
    intro n
    have h1 := he n
    simp only [gridLap] at h1
    have h2 : e n * (1 + 2 * d * c) = c * ∑ i, (e (n + zbasis i) + e (n - zbasis i)) := by
      have : t ^ 2 * (h ^ 2)⁻¹ = c := by rw [hc, div_eq_mul_inv]
      rw [← this]
      have hs : ∑ i, (e (n + zbasis i) - 2 * e n + e (n - zbasis i)) =
          ∑ i, (e (n + zbasis i) + e (n - zbasis i)) - 2 * d * e n := by
        rw [show ∑ i, (e (n + zbasis i) - 2 * e n + e (n - zbasis i)) =
          ∑ i, ((e (n + zbasis i) + e (n - zbasis i)) - 2 * e n) from
            Finset.sum_congr rfl fun i _ => by ring, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [hs] at h1
      linear_combination h1
    rw [← abs_of_pos (show 0 < 1 + 2 * d * c by positivity), ← abs_mul, h2, abs_mul,
      abs_of_pos hc0]
    calc c * |∑ i, (e (n + zbasis i) + e (n - zbasis i))|
        ≤ c * ∑ i, (|e (n + zbasis i)| + |e (n - zbasis i)|) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => abs_add_le _ _)
      _ ≤ c * ∑ _i : Fin d, (M + M) := by
          gcongr with i <;> exact hle _
      _ = 2 * d * c * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hp : ∀ n, |e n| ≤ 2 * d * c / (1 + 2 * d * c) * M := by
    intro n
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact key n
  have hMle : M ≤ 2 * d * c / (1 + 2 * d * c) * M := ciSup_le hp
  have hp1 : 2 * d * c / (1 + 2 * d * c) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have hMz : M = 0 := by nlinarith
  funext n
  have := hle n
  rw [hMz] at this
  exact abs_nonpos_iff.1 this

end Lap

/-! ## The kernel `κ_t` -/

/-- `p := 2dc/(1 + 2dc)`, `c := t²/h²`. -/
noncomputable def helmP (d : ℕ) (h t : ℝ) : ℝ :=
  2 * d * (t ^ 2 / h ^ 2) / (1 + 2 * d * (t ^ 2 / h ^ 2))

theorem discreteHelmholtz_eq (h t : ℝ) (n : Zd d) :
    discreteHelmholtz d h t n = (1 - helmP d h t) * ∑' k : ℕ, helmP d h t ^ k * kpow rwStep k n :=
  rfl

section Kappa

variable (hd : 1 ≤ d) {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
include hd hh ht

theorem helmP_pos : 0 < helmP d h t := by
  unfold helmP
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

omit hd in
theorem helmP_lt_one : helmP d h t < 1 := by
  unfold helmP
  rw [div_lt_one (by positivity)]
  linarith

theorem summable_kappa_pair :
    Summable fun p : ℕ × Zd d => helmP d h t ^ p.1 * kpow rwStep p.1 p.2 := by
  have hσ := isProbKernel_rwStep hd
  have hp0 := (helmP_pos hd hh ht).le
  have hp1 := helmP_lt_one (d := d) hh ht
  set p := helmP d h t
  have hnn : 0 ≤ fun q : ℕ × Zd d => p ^ q.1 * kpow rwStep q.1 q.2 := fun q =>
    mul_nonneg (pow_nonneg hp0 _) ((isProbKernel_kpow hσ q.1).1 _)
  have hrow : ∀ k : ℕ, Summable fun n : Zd d => p ^ k * kpow rwStep k n := fun k =>
    (isProbKernel_kpow hσ k).2.1.mul_left _
  have hcol : Summable fun k : ℕ => ∑' n : Zd d, p ^ k * kpow rwStep k n := by
    have hg : Summable fun k : ℕ => p ^ k := summable_geometric_of_lt_one hp0 hp1
    refine hg.congr fun k => ?_
    rw [tsum_mul_left, (isProbKernel_kpow hσ k).2.2, mul_one]
  exact (summable_prod_of_nonneg hnn).2 ⟨hrow, hcol⟩

/-- **`κ_t` is a probability kernel.** -/
theorem isProbKernel_discreteHelmholtz : IsProbKernel (discreteHelmholtz d h t) := by
  have hσ := isProbKernel_rwStep hd
  have hp0 := (helmP_pos hd hh ht).le
  have hp1 := helmP_lt_one (d := d) hh ht
  have hF := summable_kappa_pair hd hh ht
  refine ⟨fun n => ?_, ?_, ?_⟩
  · rw [discreteHelmholtz_eq]
    exact mul_nonneg (by linarith) (tsum_nonneg fun k => mul_nonneg (pow_nonneg hp0 _)
      ((isProbKernel_kpow hσ k).1 _))
  · exact (hF.prod_symm.prod.mul_left (1 - helmP d h t)).congr
      fun n => (discreteHelmholtz_eq h t n).symm
  · simp_rw [discreteHelmholtz_eq]
    rw [tsum_mul_left, hF.tsum_comm (f := fun k n => helmP d h t ^ k * kpow rwStep k n)]
    simp_rw [tsum_mul_left, (isProbKernel_kpow hσ _).2.2, mul_one]
    rw [tsum_geometric_of_lt_one hp0 hp1]
    field_simp [show (1 : ℝ) - helmP d h t ≠ 0 by linarith]

/-- **`κ̂_t(ϑ) = (1 + t²D_h(ϑ))⁻¹`.** -/
theorem gridFourier_discreteHelmholtz (θ : Fin d → ℝ) :
    gridFourier (discreteHelmholtz d h t) θ = (((1 + t ^ 2 * gridSymbol h θ)⁻¹ : ℝ) : ℂ) := by
  have hσ := isProbKernel_rwStep hd
  have hp0 := (helmP_pos hd hh ht).le
  have hp1 := helmP_lt_one (d := d) hh ht
  have hF := summable_kappa_pair hd hh ht
  set p := helmP d h t with hp
  set φ : ℝ := ∑ i, Real.cos (θ i) / d with hφ
  have hφ1 : |φ| ≤ 1 := by
    rw [hφ, ← Finset.sum_div, abs_div, abs_of_pos (show (0 : ℝ) < d by exact_mod_cast hd)]
    rw [div_le_one (by exact_mod_cast hd)]
    calc |∑ i, Real.cos (θ i)| ≤ ∑ i, |Real.cos (θ i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
      _ = d := by simp
  have hG : Summable fun q : ℕ × Zd d =>
      ((p ^ q.1 * kpow rwStep q.1 q.2 : ℝ) : ℂ) * cexp ((gphase θ q.2 : ℂ) * I) :=
    Summable.of_norm (hF.norm.congr fun q => by
      simp only [norm_mul, norm_cexp_gphase, mul_one, Complex.norm_real])
  rw [gridFourier_eq]
  have e1 : ∀ n, ((discreteHelmholtz d h t n : ℝ) : ℂ) * cexp ((gphase θ n : ℂ) * I) =
      ((1 - p : ℝ) : ℂ) * ∑' k : ℕ, ((p ^ k * kpow rwStep k n : ℝ) : ℂ) *
        cexp ((gphase θ n : ℂ) * I) := by
    intro n
    rw [discreteHelmholtz_eq, Complex.ofReal_mul, Complex.ofReal_tsum, mul_assoc, tsum_mul_right]
  simp_rw [e1]
  rw [tsum_mul_left, hG.tsum_comm (f := fun k n => ((p ^ k * kpow rwStep k n : ℝ) : ℂ) *
    cexp ((gphase θ n : ℂ) * I))]
  have e2 : ∀ k : ℕ, ∑' n, ((p ^ k * kpow rwStep k n : ℝ) : ℂ) * cexp ((gphase θ n : ℂ) * I) =
      ((p * φ : ℝ) : ℂ) ^ k := by
    intro k
    have := gridFourier_kpow (summable_rwStep (d := d)) θ k
    rw [gridFourier_rwStep, gridFourier_eq] at this
    rw [show (fun n => ((p ^ k * kpow rwStep k n : ℝ) : ℂ) * cexp ((gphase θ n : ℂ) * I)) =
      fun n => ((p ^ k : ℝ) : ℂ) * (((kpow rwStep k n : ℝ) : ℂ) * cexp ((gphase θ n : ℂ) * I))
        from funext fun n => by push_cast; ring, tsum_mul_left, this, ← hφ]
    push_cast
    ring
  simp_rw [e2]
  have hpφ : ‖((p * φ : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hp0]
    calc p * |φ| ≤ p * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hp1
  rw [(hasSum_geometric_of_norm_lt_one hpφ).tsum_eq]
  -- `(1-p)/(1-pφ) = (1 + t²D_h)⁻¹`
  have hD : t ^ 2 * gridSymbol h θ = 2 * d * (t ^ 2 / h ^ 2) * (1 - φ) := by
    rw [gridSymbol, hφ, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    have : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    field_simp
  have hc : 0 < 2 * d * (t ^ 2 / h ^ 2) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have h1 : 1 - p * φ ≠ 0 := by
    have : p * φ < 1 := by
      calc p * φ ≤ p * |φ| := by gcongr; exact le_abs_self φ
        _ ≤ p * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hp1
    linarith
  rw [hD]
  have h2 : (1 + 2 * d * (t ^ 2 / h ^ 2) * (1 - φ)) =
      (1 + 2 * d * (t ^ 2 / h ^ 2)) * (1 - p * φ) := by
    rw [hp, helmP]
    field_simp; ring
  rw [h2]
  have h3 : 1 - p = (1 + 2 * d * (t ^ 2 / h ^ 2))⁻¹ := by
    rw [hp, helmP]
    field_simp; ring
  rw [h3]
  have h4 : ((1 - p * φ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1
  have h5 : ((1 + 2 * d * (t ^ 2 / h ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 1 + 2 * d * (t ^ 2 / h ^ 2)).ne'
  push_cast at h4 h5 ⊢
  field_simp

/-- `κ_t * σ = (κ_t - (1-p)δ₀)/p`. -/
theorem kconv_kappa_rwStep (n : Zd d) :
    kconv (discreteHelmholtz d h t) rwStep n =
      (discreteHelmholtz d h t n - (1 - helmP d h t) * deltaZ n) / helmP d h t := by
  have hσ := isProbKernel_rwStep hd
  have hp0 := helmP_pos hd hh ht
  have hp1 := helmP_lt_one (d := d) hh ht
  have hF := summable_kappa_pair hd hh ht
  set p := helmP d h t with hp
  have hσ1 : ∀ x, rwStep (d := d) x ≤ 1 := fun x => by
    rw [← hσ.2.2]; exact hσ.2.1.le_tsum x fun _ _ => rwStep_nonneg _
  have hH : Summable fun q : ℕ × Zd d => p ^ q.1 * kpow rwStep q.1 q.2 * rwStep (n - q.2) := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg (mul_nonneg (pow_nonneg hp0.le _)
      ((isProbKernel_kpow hσ _).1 _)) (rwStep_nonneg _)) (fun q => ?_) hF
    calc p ^ q.1 * kpow rwStep q.1 q.2 * rwStep (n - q.2)
        ≤ p ^ q.1 * kpow rwStep q.1 q.2 * 1 := by
          gcongr
          · exact mul_nonneg (pow_nonneg hp0.le _) ((isProbKernel_kpow hσ _).1 _)
          · exact hσ1 _
      _ = _ := mul_one _
  -- `κ * σ = (1-p) ∑ₖ pᵏ σ^{*(k+1)}`
  have h1 : kconv (discreteHelmholtz d h t) rwStep n =
      (1 - p) * ∑' k : ℕ, p ^ k * kpow rwStep (k + 1) n := by
    unfold kconv
    simp_rw [discreteHelmholtz_eq, ← hp, mul_assoc, ← tsum_mul_right]
    rw [tsum_mul_left]
    congr 1
    rw [hH.tsum_comm (f := fun k m => p ^ k * kpow rwStep k m * rwStep (n - m))]
    congr 1
    funext k
    simp_rw [mul_assoc]
    rw [tsum_mul_left]
    rfl
  -- `κ(n) = (1-p)(δ(n) + p ∑ₖ pᵏ σ^{*(k+1)}(n))`
  have hs : Summable fun k : ℕ => p ^ k * kpow rwStep k n := hF.prod_symm.prod_factor n
  have h2 : discreteHelmholtz d h t n =
      (1 - p) * (deltaZ n + p * ∑' k : ℕ, p ^ k * kpow rwStep (k + 1) n) := by
    rw [discreteHelmholtz_eq, ← hp, hs.tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul]
    congr 2
    exact tsum_congr fun k => by rw [pow_succ]; ring
  rw [h1, h2]
  field_simp
  ring

/-- **`(1 - t²Δ_h)κ_t = δ₀`.** -/
theorem discreteHelmholtz_eqn (n : Zd d) :
    discreteHelmholtz d h t n - t ^ 2 * gridLap h (discreteHelmholtz d h t) n = deltaZ n := by
  rw [gridLap_eq, kconv_kappa_rwStep hd hh ht]
  have hp0 := helmP_pos hd hh ht
  set p := helmP d h t with hp
  set c := t ^ 2 / h ^ 2 with hc
  have hpos : 0 < 1 + 2 * d * c := by positivity
  have hpc : 2 * d * c = p * (1 + 2 * d * c) := by
    rw [hp, helmP, ← hc, div_mul_cancel₀ _ hpos.ne']
  have h1p : (1 - p) * (1 + 2 * d * c) = 1 := by
    rw [hp, helmP, ← hc, sub_mul, div_mul_cancel₀ _ hpos.ne']
    ring
  have ht2 : t ^ 2 * (h ^ 2)⁻¹ = c := by rw [hc, div_eq_mul_inv]
  have key : c * (2 * d * ((discreteHelmholtz d h t n - (1 - p) * deltaZ n) / p)) =
      (1 + 2 * d * c) * (discreteHelmholtz d h t n - (1 - p) * deltaZ n) := by
    have hq : 2 * d * c / p = 1 + 2 * d * c := by
      rw [div_eq_iff hp0.ne']; linear_combination hpc
    calc c * (2 * d * ((discreteHelmholtz d h t n - (1 - p) * deltaZ n) / p))
        = (2 * d * c / p) * (discreteHelmholtz d h t n - (1 - p) * deltaZ n) := by ring
      _ = _ := by rw [hq]
  rw [← mul_assoc, ht2, mul_sub, key]
  linear_combination (deltaZ n) * h1p

end Kappa

/-- **`prop:discrete-helmholtz`(1)**: for `d ≥ 1`, `h, t > 0`, `p ∈ (0,1)`, and `κ_t` is a
probability measure on `ℤ^d` with `κ̂_t(ϑ) = (1 + t²D_h(ϑ))⁻¹`, the unique bounded solution of
`(1 - t²Δ_h)κ = δ₀`. Strengthened on 2026-11-23 (review round 3, s6-7.R9): uniqueness among
bounded solutions, where it was stated among summable ones; a summable array is bounded
(`bounded_of_summable_Z`), so the old form follows. -/
theorem discrete_helmholtz_kernel (hd : 1 ≤ d) {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    (0 < 2 * d * (t ^ 2 / h ^ 2) / (1 + 2 * d * (t ^ 2 / h ^ 2)) ∧
        2 * d * (t ^ 2 / h ^ 2) / (1 + 2 * d * (t ^ 2 / h ^ 2)) < 1) ∧
      IsProbKernel (discreteHelmholtz d h t) ∧
      (∀ θ : Fin d → ℝ,
        gridFourier (discreteHelmholtz d h t) θ = (((1 + t ^ 2 * gridSymbol h θ)⁻¹ : ℝ) : ℂ)) ∧
      (∀ n : Zd d, discreteHelmholtz d h t n - t ^ 2 * gridLap h (discreteHelmholtz d h t) n =
        deltaZ n) ∧
      ∀ u : Zd d → ℝ, (∃ C, ∀ n, |u n| ≤ C) → (∀ n, u n - t ^ 2 * gridLap h u n = deltaZ n) →
        u = discreteHelmholtz d h t := by
  refine ⟨⟨helmP_pos hd hh ht, helmP_lt_one hh ht⟩, isProbKernel_discreteHelmholtz hd hh ht,
    gridFourier_discreteHelmholtz hd hh ht, discreteHelmholtz_eqn hd hh ht, fun u hu hue => ?_⟩
  have hk := (isProbKernel_discreteHelmholtz hd hh ht).2.1
  obtain ⟨C, hC⟩ := hu
  obtain ⟨C', hC'⟩ := bounded_of_summable_Z hk
  have hz := helm_grid_unique hh ht (e := fun n => u n - discreteHelmholtz d h t n)
    ⟨C + C', fun n => abs_le.2 ⟨by linarith [abs_le.1 (hC n), abs_le.1 (hC' n)],
      by linarith [abs_le.1 (hC n), abs_le.1 (hC' n)]⟩⟩ fun n => by
      rw [show (fun n => u n - discreteHelmholtz d h t n) =
        fun n => 1 * u n + (-1) * discreteHelmholtz d h t n from funext fun n => by ring,
        gridLap_lin]
      have h1 := hue n
      have h2 := discreteHelmholtz_eqn hd hh ht n
      linarith
  funext n
  have := congrFun hz n
  simp only [Pi.zero_apply] at this
  linarith

/-! ## The cascade -/

theorem kconv_add_smul_right {lam mu mu' : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu)
    (hm' : Summable mu') (a b : ℝ) :
    kconv lam (fun n => a * mu n + b * mu' n) =
      fun n => a * kconv lam mu n + b * kconv lam mu' n := by
  rw [kconv_comm, kconv_add_smul_left hm hm' hl, kconv_comm mu, kconv_comm mu']

/-- `Δ_h` passes through a convolution with a summable kernel. -/
theorem gridLap_kconv (h : ℝ) {lam mu : Zd d → ℝ} (hl : Summable lam) {C : ℝ}
    (hC : ∀ k, |mu k| ≤ C) (n : Zd d) :
    gridLap h (kconv lam mu) n = kconv lam (gridLap h mu) n := by
  have hs : ∀ a : Zd d, Summable fun m => lam m * mu (n + a - m) := fun a =>
    summable_bounded_mul hl hC (n + a)
  have hs' : ∀ a : Zd d, Summable fun m => lam m * mu (n - a - m) := fun a =>
    summable_bounded_mul hl hC (n - a)
  have hs0 : Summable fun m => lam m * mu (n - m) := summable_bounded_mul hl hC n
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

section Cascade

variable (hd : 1 ≤ d) {h : ℝ} (hh : 0 < h)
include hd hh

/-- **The resolvent identity** `κ_s * κ_t = (t²κ_t - s²κ_s)/(t² - s²)` for `0 < s < t`. -/
theorem kappa_resolvent {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    kconv (discreteHelmholtz d h s) (discreteHelmholtz d h t) =
      fun n => (t ^ 2 * discreteHelmholtz d h t n - s ^ 2 * discreteHelmholtz d h s n) /
        (t ^ 2 - s ^ 2) := by
  have ht : 0 < t := hs.trans hst
  have hKs := isProbKernel_discreteHelmholtz hd hh hs
  have hKt := isProbKernel_discreteHelmholtz hd hh ht
  obtain ⟨Ct, hCt⟩ := bounded_of_summable_Z hKt.2.1
  obtain ⟨Cs, hCs⟩ := bounded_of_summable_Z hKs.2.1
  have hts : t ^ 2 - s ^ 2 ≠ 0 := by nlinarith
  have hs2 : s ^ 2 ≠ 0 := by positivity
  set X := kconv (discreteHelmholtz d h s) (discreteHelmholtz d h t) with hX
  set Z : Zd d → ℝ := fun n => (t ^ 2 * discreteHelmholtz d h t n -
    s ^ 2 * discreteHelmholtz d h s n) / (t ^ 2 - s ^ 2) with hZ
  have hXeq : ∀ n, X n - t ^ 2 * gridLap h X n = discreteHelmholtz d h s n := by
    intro n
    rw [hX, gridLap_kconv h hKs.2.1 hCt]
    have h1 : (fun m => discreteHelmholtz d h t m - t ^ 2 * gridLap h (discreteHelmholtz d h t) m) =
        deltaZ := funext (discreteHelmholtz_eqn hd hh ht)
    have h2 := congrFun (kconv_add_smul_right hKs.2.1 hKt.2.1
      (show Summable (gridLap h (discreteHelmholtz d h t)) by
        have : gridLap h (discreteHelmholtz d h t) = fun m =>
            (discreteHelmholtz d h t m - deltaZ m) / t ^ 2 := by
          funext m
          have := discreteHelmholtz_eqn hd hh ht m
          field_simp
          linarith
        rw [this]
        exact (hKt.2.1.sub summable_deltaZ).div_const _) 1 (-t ^ 2)) n
    simp only [one_mul, neg_mul, ← sub_eq_add_neg] at h2
    rw [← h2]
    rw [show (fun m => discreteHelmholtz d h t m - t ^ 2 * gridLap h (discreteHelmholtz d h t) m) =
      deltaZ from h1, kconv_deltaZ_right]
  have hZeq : ∀ n, Z n - t ^ 2 * gridLap h Z n = discreteHelmholtz d h s n := by
    intro n
    rw [hZ]
    rw [show (fun n => (t ^ 2 * discreteHelmholtz d h t n - s ^ 2 * discreteHelmholtz d h s n) /
        (t ^ 2 - s ^ 2)) = fun n => (t ^ 2 / (t ^ 2 - s ^ 2)) * discreteHelmholtz d h t n +
          (-(s ^ 2) / (t ^ 2 - s ^ 2)) * discreteHelmholtz d h s n from funext fun n => by ring,
      gridLap_lin]
    have et := discreteHelmholtz_eqn hd hh ht n
    have es := discreteHelmholtz_eqn hd hh hs n
    have ht2 : t ^ 2 ≠ 0 := by positivity
    have hΔt : gridLap h (discreteHelmholtz d h t) n =
        (discreteHelmholtz d h t n - deltaZ n) / t ^ 2 := by
      field_simp; linarith
    have hΔs : gridLap h (discreteHelmholtz d h s) n =
        (discreteHelmholtz d h s n - deltaZ n) / s ^ 2 := by
      field_simp; linarith
    rw [hΔt, hΔs]
    field_simp
    ring
  have hz := helm_grid_unique hh ht (e := fun n => X n - Z n) (by
    obtain ⟨C1, hC1⟩ := bounded_of_summable_Z (summable_kconv hKs.2.1 hKt.2.1)
    obtain ⟨C2, hC2⟩ := bounded_of_summable_Z
      (((hKt.2.1.mul_left (t ^ 2)).sub (hKs.2.1.mul_left (s ^ 2))).div_const (t ^ 2 - s ^ 2))
    exact ⟨C1 + C2, fun n => (abs_sub _ _).trans (add_le_add (hC1 n) (hC2 n))⟩) fun n => by
      rw [show (fun n => X n - Z n) = fun n => 1 * X n + (-1) * Z n from funext fun n => by ring,
        gridLap_lin]
      have h1 := hXeq n
      have h2 := hZeq n
      linarith
  funext n
  have := congrFun hz n
  simp only [Pi.zero_apply] at this
  linarith

/-- The one-step mixture `(s²/t²)δ₀ + (1 - s²/t²)κ_t`. -/
noncomputable def helmMix (d : ℕ) (h s t : ℝ) (n : Zd d) : ℝ :=
  s ^ 2 / t ^ 2 * deltaZ n + (1 - s ^ 2 / t ^ 2) * discreteHelmholtz d h t n

omit hd hh in
theorem helmIncrement_eq (γ : ℕ) (s t : ℝ) : helmIncrement d h γ s t = kpow (helmMix d h s t) γ :=
  rfl

theorem isProbKernel_helmMix {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    IsProbKernel (helmMix d h s t) := by
  have ht : 0 < t := lt_of_le_of_lt hs hst
  have hK := isProbKernel_discreteHelmholtz hd hh ht
  have hq0 : 0 ≤ s ^ 2 / t ^ 2 := by positivity
  have hq1 : s ^ 2 / t ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; exact pow_lt_pow_left₀ hst hs two_ne_zero
  refine ⟨fun n => ?_, (summable_deltaZ.mul_left _).add (hK.2.1.mul_left _), ?_⟩
  · unfold helmMix
    exact add_nonneg (mul_nonneg hq0 (isProbKernel_deltaZ.1 n)) (mul_nonneg (by linarith) (hK.1 n))
  · unfold helmMix
    rw [(summable_deltaZ.mul_left _).tsum_add (hK.2.1.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_deltaZ, hK.2.2]
    ring

theorem summable_helmMix {s t : ℝ} (ht : 0 < t) : Summable (helmMix d h s t) :=
  (summable_deltaZ.mul_left _).add ((isProbKernel_discreteHelmholtz hd hh ht).2.1.mul_left _)

/-- **The mixtures compose**: `μ_{s,t} * μ_{r,s} = μ_{r,t}` for `0 ≤ r < s < t`. -/
theorem helmMix_kconv {r s t : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) :
    kconv (helmMix d h s t) (helmMix d h r s) = helmMix d h r t := by
  have hs : 0 < s := lt_of_le_of_lt hr hrs
  have ht : 0 < t := hs.trans hst
  have hKs := (isProbKernel_discreteHelmholtz hd hh hs).2.1
  have hKt := (isProbKernel_discreteHelmholtz hd hh ht).2.1
  have hres := kappa_resolvent hd hh hs hst
  have hts : t ^ 2 - s ^ 2 ≠ 0 := by nlinarith
  have hs2 : s ^ 2 ≠ 0 := by positivity
  have ht2 : t ^ 2 ≠ 0 := by positivity
  rw [show helmMix d h s t = fun n => s ^ 2 / t ^ 2 * deltaZ n +
    (1 - s ^ 2 / t ^ 2) * discreteHelmholtz d h t n from rfl,
    kconv_add_smul_left summable_deltaZ hKt (summable_helmMix hd hh hs)]
  funext n
  rw [kconv_deltaZ_left, show helmMix d h r s = fun n => r ^ 2 / s ^ 2 * deltaZ n +
    (1 - r ^ 2 / s ^ 2) * discreteHelmholtz d h s n from rfl,
    kconv_add_smul_right hKt summable_deltaZ hKs, kconv_deltaZ_right,
    kconv_comm (discreteHelmholtz d h t), hres]
  simp only [helmMix]
  field_simp
  ring

/-- `κ̂_t ... ` transfer of the mixture: `(1 + s²D_h)/(1 + t²D_h)`. -/
theorem gridFourier_helmMix {s t : ℝ} (ht : 0 < t) (θ : Fin d → ℝ) :
    gridFourier (helmMix d h s t) θ =
      (((1 + s ^ 2 * gridSymbol h θ) / (1 + t ^ 2 * gridSymbol h θ) : ℝ) : ℂ) := by
  have hK := (isProbKernel_discreteHelmholtz hd hh ht).2.1
  unfold helmMix
  rw [gridFourier_add_smul summable_deltaZ hK, gridFourier_deltaZ,
    gridFourier_discreteHelmholtz hd hh ht]
  have hD : 0 ≤ gridSymbol h θ := by
    unfold gridSymbol
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => by
      linarith [Real.cos_le_one (θ i)])
  have h1 : (1 : ℝ) + t ^ 2 * gridSymbol h θ ≠ 0 := by positivity
  have ht2 : t ^ 2 ≠ 0 := by positivity
  push_cast
  have h1' : (1 : ℂ) + (t : ℂ) ^ 2 * (gridSymbol h θ : ℂ) ≠ 0 := by exact_mod_cast h1
  have ht2' : (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast ht2
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  ring

end Cascade

/-- **`prop:discrete-helmholtz`(2)**, the exact cascade: for an integer `γ ≥ 1`, `λ_t := κ_t^{*γ}`
has transfer `(1 + t²D_h)^{-γ}`; for `0 < s < t` the increment `λ_{s,t}`, the `γ`-fold power of the
probability measure `(s²/t²)δ₀ + (1 - s²/t²)κ_t`, has transfer `((1 + s²D_h)/(1 + t²D_h))^γ`; and
`λ_{r,t} = λ_{s,t} * λ_{r,s}` for `r < s < t`. Blind review R5-6: "an exact cascade" reaches back
to the origin, so the increments are stated from `s ≥ 0` and the cascade identity from `r ≥ 0`, with
`λ_{0,t} = λ_t` (at `s = 0` the measure is `κ_t` and the increment `λ_t`), which is stronger than
the node's `0 < s` and costs nothing. -/
theorem discrete_helmholtz_cascade (hd : 1 ≤ d) {h : ℝ} (hh : 0 < h) (γ : ℕ) :
    (∀ t : ℝ, 0 < t → ∀ θ : Fin d → ℝ,
        gridFourier (helmKernel d h t γ) θ = (((1 + t ^ 2 * gridSymbol h θ) ^ γ)⁻¹ : ℝ)) ∧
      (∀ s t : ℝ, 0 ≤ s → s < t →
        IsProbKernel (fun n => s ^ 2 / t ^ 2 * deltaZ n +
          (1 - s ^ 2 / t ^ 2) * discreteHelmholtz d h t n) ∧
        IsProbKernel (helmIncrement d h γ s t) ∧
        ∀ θ : Fin d → ℝ, gridFourier (helmIncrement d h γ s t) θ =
          ((((1 + s ^ 2 * gridSymbol h θ) / (1 + t ^ 2 * gridSymbol h θ)) ^ γ : ℝ) : ℂ)) ∧
      (∀ t : ℝ, 0 < t → helmIncrement d h γ 0 t = helmKernel d h t γ) ∧
      ∀ r s t : ℝ, 0 ≤ r → r < s → s < t →
        helmIncrement d h γ r t = kconv (helmIncrement d h γ s t) (helmIncrement d h γ r s) := by
  refine ⟨fun t ht θ => ?_, fun s t hs hst => ⟨isProbKernel_helmMix hd hh hs hst,
    isProbKernel_kpow (isProbKernel_helmMix hd hh hs hst) γ, fun θ => ?_⟩, fun t ht => ?_,
    fun r s t hr hrs hst => ?_⟩
  · rw [helmKernel, gridFourier_kpow (isProbKernel_discreteHelmholtz hd hh ht).2.1,
      gridFourier_discreteHelmholtz hd hh ht]
    push_cast
    rw [inv_pow]
  · have ht : 0 < t := lt_of_le_of_lt hs hst
    rw [helmIncrement_eq, gridFourier_kpow (summable_helmMix hd hh ht),
      gridFourier_helmMix hd hh ht]
    push_cast
    ring
  · rw [helmIncrement_eq, helmKernel]
    congr 1
    funext n
    simp [helmMix]
  · have hs : 0 < s := lt_of_le_of_lt hr hrs
    have ht : 0 < t := hs.trans hst
    rw [helmIncrement_eq, helmIncrement_eq, helmIncrement_eq,
      kpow_kconv (summable_helmMix hd hh ht) (summable_helmMix hd hh hs),
      helmMix_kconv hd hh hr hrs hst]

/-! ## Invariance -/

section Invariance

variable (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ)

/-- The signed permutation `n ↦ (εᵢ n_{σ(i)})ᵢ`. -/
def gmap (n : Zd d) : Zd d := fun i => ε i * n (σ i)

/-- Its inverse. -/
def ginv (n : Zd d) : Zd d := fun j => ε (σ.symm j) * n (σ.symm j)

theorem eps_mul_self (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i : Fin d) : ε i * ε i = 1 := by
  rcases hε i with h | h <;> rw [h] <;> norm_num

/-- `gmap` as an equivalence. -/
def gEquiv (hε : ∀ i, ε i = 1 ∨ ε i = -1) : Zd d ≃ Zd d where
  toFun := gmap σ ε
  invFun := ginv σ ε
  left_inv n := by
    funext j
    simp only [gmap, ginv, Equiv.apply_symm_apply]
    rw [← mul_assoc, eps_mul_self ε hε, one_mul]
  right_inv n := by
    funext i
    simp only [gmap, ginv, Equiv.symm_apply_apply]
    rw [← mul_assoc, eps_mul_self ε hε, one_mul]

theorem gmap_sub (n m : Zd d) : gmap σ ε (n - m) = gmap σ ε n - gmap σ ε m := by
  funext i; simp only [gmap, Pi.sub_apply]; ring

variable (hε : ∀ i, ε i = 1 ∨ ε i = -1)
include hε

theorem kconv_invariant {lam mu : Zd d → ℝ} (hl : ∀ n, lam (gmap σ ε n) = lam n)
    (hm : ∀ n, mu (gmap σ ε n) = mu n) (n : Zd d) :
    kconv lam mu (gmap σ ε n) = kconv lam mu n := by
  unfold kconv
  rw [← (gEquiv σ ε hε).tsum_eq]
  congr 1
  funext m
  simp only [gEquiv, Equiv.coe_fn_mk]
  rw [hl, ← gmap_sub, hm]

theorem deltaZ_invariant (n : Zd d) : deltaZ (gmap σ ε n) = deltaZ n := by
  unfold deltaZ
  have : gmap σ ε n = 0 ↔ n = 0 := by
    constructor
    · intro h
      have := congrArg (ginv σ ε) h
      rw [show ginv σ ε (gmap σ ε n) = n from (gEquiv σ ε hε).left_inv n] at this
      rw [this]; funext j; simp [ginv]
    · rintro rfl; funext i; simp [gmap]
  simp only [this]

theorem ginv_zbasis (i : Fin d) :
    ginv σ ε (zbasis i) = if ε i = 1 then zbasis (σ i) else -zbasis (σ i) := by
  funext j
  simp only [ginv, zbasis]
  by_cases hj : σ.symm j = i
  · have hj' : j = σ i := by rw [← hj, Equiv.apply_symm_apply]
    subst hj'
    rcases hε i with h | h <;> simp [h]
  · have hj' : j ≠ σ i := fun h => hj (by rw [h, Equiv.symm_apply_apply])
    rcases hε i with h | h <;> simp [h, hj, hj']

theorem rwStep_invariant (n : Zd d) : rwStep (gmap σ ε n) = rwStep n := by
  have hiff : ∀ v n, gmap σ ε n = v ↔ n = ginv σ ε v := fun v n =>
    ⟨fun h => by rw [← h]; exact ((gEquiv σ ε hε).left_inv n).symm,
      fun h => by rw [h]; exact (gEquiv σ ε hε).right_inv v⟩
  have hneg : ∀ v, ginv σ ε (-v) = -ginv σ ε v := fun v => by
    funext j; simp only [ginv, Pi.neg_apply]; ring
  have hpair : ∀ i, ((if gmap σ ε n = zbasis i then (1 : ℝ) else 0) +
      (if gmap σ ε n = -zbasis i then 1 else 0)) =
      ((if n = zbasis (σ i) then (1 : ℝ) else 0) + (if n = -zbasis (σ i) then 1 else 0)) := by
    intro i
    simp only [hiff, hneg, ginv_zbasis σ ε hε]
    rcases hε i with h | h
    · simp [h]
    · have : ε i ≠ 1 := by rw [h]; norm_num
      simp only [this, if_false, neg_neg]
      ring
  unfold rwStep
  simp_rw [hpair]
  exact Equiv.sum_comp σ (fun j => ((if n = zbasis j then (1 : ℝ) else 0) +
    (if n = -zbasis j then 1 else 0)) / (2 * d))

theorem kpow_invariant {lam : Zd d → ℝ} (hl : ∀ n, lam (gmap σ ε n) = lam n) :
    ∀ k n, kpow lam k (gmap σ ε n) = kpow lam k n
  | 0, n => deltaZ_invariant σ ε hε n
  | k + 1, n => kconv_invariant σ ε hε (kpow_invariant hl k) hl n

theorem kappa_invariant (h t : ℝ) (n : Zd d) :
    discreteHelmholtz d h t (gmap σ ε n) = discreteHelmholtz d h t n := by
  rw [discreteHelmholtz_eq, discreteHelmholtz_eq]
  simp_rw [kpow_invariant σ ε hε (rwStep_invariant σ ε hε)]

end Invariance

/-- **`prop:discrete-helmholtz`(2)**, invariance: the family is invariant under the translations of
`ℤ^d` (its convolution operators commute with them) and under the signed permutations of the axes.
-/
theorem discrete_helmholtz_invariance {h : ℝ} (γ : ℕ) :
    (∀ t : ℝ, 0 < t → ∀ u : Zd d → ℝ, Summable u → ∀ a n : Zd d,
        kconv (helmKernel d h t γ) (fun m => u (m - a)) n = kconv (helmKernel d h t γ) u (n - a)) ∧
      (∀ t : ℝ, 0 < t → ∀ (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ), (∀ i, ε i = 1 ∨ ε i = -1) →
        ∀ n : Zd d, helmKernel d h t γ (fun i => ε i * n (σ i)) = helmKernel d h t γ n) ∧
      ∀ s t : ℝ, 0 < s → s < t → ∀ (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ),
        (∀ i, ε i = 1 ∨ ε i = -1) →
        ∀ n : Zd d,
          helmIncrement d h γ s t (fun i => ε i * n (σ i)) = helmIncrement d h γ s t n := by
  refine ⟨fun t _ u _ a n => ?_, fun t _ σ ε hε n => ?_, fun s t _ _ σ ε hε n => ?_⟩
  · unfold kconv
    congr 1
    funext m
    rw [sub_right_comm]
  · exact kpow_invariant σ ε hε (kappa_invariant σ ε hε h t) γ n
  · refine kpow_invariant σ ε hε (fun m => ?_) γ n
    rw [deltaZ_invariant σ ε hε, kappa_invariant σ ε hε]

/-- **`prop:discrete-helmholtz`, invariance, the increments** (fidelity review, R37): each increment
`K_{s,t}`, `0 ≤ s < t`, commutes with translations, as the nine-point
`nine_point_family_2_invariance` states for its increments. -/
theorem discrete_helmholtz_increment_translation {h : ℝ} (γ : ℕ) :
    ∀ s t : ℝ, 0 ≤ s → s < t → ∀ (u : Zd d → ℝ) (a n : Zd d),
      kconv (helmIncrement d h γ s t) (fun m => u (m - a)) n =
        kconv (helmIncrement d h γ s t) u (n - a) := by
  intro s t _ _ u a n
  unfold kconv
  congr 1
  funext m
  rw [sub_right_comm]

/-! ## The symbol -/

section Taylor

/-- A function vanishing at `0` with nonnegative derivative on `[0,∞)` is nonnegative there.
Mathlib types only. -/
theorem nonneg_of_deriv_nonneg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (h0 : f 0 = 0)
    (hd : ∀ x, 0 ≤ x → 0 ≤ deriv f x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hf.continuous.continuousOn
    hf.differentiableOn (fun y hy => hd y (by
      rw [interior_Ici] at hy; exact le_of_lt hy))
  have := hm (self_mem_Ici) hx hx
  rwa [h0] at this

theorem sin_ge_cubic {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have h := nonneg_of_deriv_nonneg (f := fun x => Real.sin x - x + x ^ 3 / 6)
    (by fun_prop) (by simp) (fun y _ => by
      have : deriv (fun x => Real.sin x - x + x ^ 3 / 6) y = Real.cos y - 1 + y ^ 2 / 2 := by
        have h1 : HasDerivAt (fun x => Real.sin x - x + x ^ 3 / 6)
            (Real.cos y - 1 + y ^ 2 / 2) y := by
          exact (((Real.hasDerivAt_sin y).sub (hasDerivAt_id y)).add
            ((hasDerivAt_pow 3 y).div_const 6)).congr_deriv (by push_cast; ring)
        exact h1.deriv
      rw [this]; linarith [Real.one_sub_sq_div_two_le_cos (x := y)]) hx
  linarith

theorem cos_le_quartic {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h := nonneg_of_deriv_nonneg (f := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x)
    (by fun_prop) (by simp) (fun y hy => by
      have : deriv (fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x) y =
          -y + y ^ 3 / 6 + Real.sin y := by
        have h1 : HasDerivAt (fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x)
            (-y + y ^ 3 / 6 + Real.sin y) y := by
          exact ((((hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_pow 2 y).div_const 2)).add
            ((hasDerivAt_pow 4 y).div_const 24)).sub (Real.hasDerivAt_cos y)).congr_deriv
            (by push_cast; ring)
        exact h1.deriv
      rw [this]; linarith [sin_ge_cubic hy]) hx
  linarith

theorem sin_le_quintic {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have h := nonneg_of_deriv_nonneg (f := fun x => x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x)
    (by fun_prop) (by simp) (fun y hy => by
      have : deriv (fun x => x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x) y =
          1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y := by
        have h1 : HasDerivAt (fun x => x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x)
            (1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y) y := by
          exact ((((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
            ((hasDerivAt_pow 5 y).div_const 120)).sub (Real.hasDerivAt_sin y)).congr_deriv
            (by push_cast; ring)
        exact h1.deriv
      rw [this]; linarith [cos_le_quartic hy]) hx
  linarith

theorem cos_ge_sextic {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have h := nonneg_of_deriv_nonneg
    (f := fun x => Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720))
    (by fun_prop) (by simp) (fun y hy => by
      have : deriv (fun x => Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720)) y =
          -Real.sin y + y - y ^ 3 / 6 + y ^ 5 / 120 := by
        have h1 : HasDerivAt (fun x => Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720))
            (-Real.sin y + y - y ^ 3 / 6 + y ^ 5 / 120) y := by
          exact ((Real.hasDerivAt_cos y).sub ((((hasDerivAt_const y (1 : ℝ)).sub
            ((hasDerivAt_pow 2 y).div_const 2)).add ((hasDerivAt_pow 4 y).div_const 24)).sub
              ((hasDerivAt_pow 6 y).div_const 720))).congr_deriv (by push_cast; ring)
        exact h1.deriv
      rw [this]; linarith [sin_le_quintic hy]) hx
  linarith

/-- `0 ≤ 2 - 2cos x - x² + x⁴/12 ≤ x⁶/360` for every real `x`. Mathlib types only. -/
theorem cos_taylor_six (x : ℝ) :
    0 ≤ 2 - 2 * Real.cos x - x ^ 2 + x ^ 4 / 12 ∧
      2 - 2 * Real.cos x - x ^ 2 + x ^ 4 / 12 ≤ x ^ 6 / 360 := by
  rcases le_total 0 x with hx | hx
  · constructor
    · linarith [cos_le_quartic hx]
    · linarith [cos_ge_sextic hx]
  · have hx' : 0 ≤ -x := by linarith
    have h1 := cos_le_quartic hx'
    have h2 := cos_ge_sextic hx'
    rw [Real.cos_neg] at h1 h2
    have e2 : (-x) ^ 2 = x ^ 2 := by ring
    have e4 : (-x) ^ 4 = x ^ 4 := by ring
    have e6 : (-x) ^ 6 = x ^ 6 := by ring
    rw [e2, e4] at h1
    rw [e2, e4, e6] at h2
    constructor <;> linarith

end Taylor

/-- **`prop:discrete-helmholtz`(3)**, rotation covariance fails at order `h²`:
`|D_h(hω) - |ω|² + (h²/12)∑ᵢωᵢ⁴| ≤ (h⁴/360)∑ᵢωᵢ⁶`, and for `d ≥ 2` the correction `∑ᵢωᵢ⁴` is not a
function of `|ω|`. -/
theorem discrete_helmholtz_symbol {h : ℝ} (hh : 0 < h) :
    (∀ ω : Fin d → ℝ,
      |gridSymbol h (h • ω) - ∑ i, ω i ^ 2 + h ^ 2 / 12 * ∑ i, ω i ^ 4| ≤
        h ^ 4 / 360 * ∑ i, ω i ^ 6) ∧
      (2 ≤ d → ¬ ∃ f : ℝ → ℝ, ∀ ω : Fin d → ℝ, ∑ i, ω i ^ 4 = f (∑ i, ω i ^ 2)) := by
  constructor
  · intro ω
    have hh2 : h ^ 2 ≠ 0 := by positivity
    have e : gridSymbol h (h • ω) - ∑ i, ω i ^ 2 + h ^ 2 / 12 * ∑ i, ω i ^ 4 =
        ∑ i, (h ^ 2)⁻¹ * (2 - 2 * Real.cos (h * ω i) - (h * ω i) ^ 2 + (h * ω i) ^ 4 / 12) := by
      rw [gridSymbol, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [e, abs_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (by positivity)
      (cos_taylor_six _).1), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := (cos_taylor_six (h * ω i)).2
    calc (h ^ 2)⁻¹ * (2 - 2 * Real.cos (h * ω i) - (h * ω i) ^ 2 + (h * ω i) ^ 4 / 12)
        ≤ (h ^ 2)⁻¹ * ((h * ω i) ^ 6 / 360) := by gcongr
      _ = h ^ 4 / 360 * ω i ^ 6 := by field_simp
  · rintro hd ⟨f, hf⟩
    set a : Fin d := ⟨0, by omega⟩
    set b : Fin d := ⟨1, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    have h1 := hf (Pi.single a 1)
    have h2 := hf (fun i => if i = a ∨ i = b then Real.sqrt (1 / 2) else 0)
    have hs : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    have hs4 : Real.sqrt (1 / 2) ^ 4 = 1 / 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs]; norm_num
    have e1 : ∑ i, (Pi.single a (1 : ℝ) : Fin d → ℝ) i ^ 2 = 1 := by
      rw [Finset.sum_eq_single a] <;> simp [Pi.single_apply]
    have e1' : ∑ i, (Pi.single a (1 : ℝ) : Fin d → ℝ) i ^ 4 = 1 := by
      rw [Finset.sum_eq_single a] <;> simp [Pi.single_apply]
    have hsum : ∀ k : ℕ, 0 < k → ∑ i, (if i = a ∨ i = b then Real.sqrt (1 / 2) else 0) ^ k =
        2 * Real.sqrt (1 / 2) ^ k := by
      intro k hk
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i = a ∨ i = b)]
      have hz : ∑ i ∈ Finset.univ.filter (fun i => ¬ (i = a ∨ i = b)),
          (if i = a ∨ i = b then Real.sqrt (1 / 2) else 0) ^ k = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [Finset.mem_filter] at hi
          rw [if_neg hi.2, zero_pow hk.ne']
      rw [hz, add_zero]
      have hfilt : Finset.univ.filter (fun i : Fin d => i = a ∨ i = b) = {a, b} := by
        ext i; simp
      rw [hfilt, Finset.sum_pair hab]
      simp
      ring
    rw [e1, e1'] at h1
    rw [hsum 2 (by norm_num), hsum 4 (by norm_num), hs, hs4] at h2
    norm_num at h2
    rw [← h2] at h1
    norm_num at h1

/-- **`prop:discrete-helmholtz`(4)**: at `d = 1` the family is the sampled Laplace family,
`κ_{t_h} = λ_t` of `prop:recursion-helmholtz`(2). -/
theorem discrete_helmholtz_line {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    ∀ n : Zd 1, discreteHelmholtz 1 h (helmRange h t) n = sampledLaplace h t (n 0) := by
  have hth : 0 < helmRange h t := by
    unfold helmRange
    have : 0 < Real.sinh (h / (2 * t)) := Real.sinh_pos_iff.2 (by positivity)
    positivity
  set e : ℤ ≃ Zd 1 := (Equiv.funUnique (Fin 1) ℤ).symm with he
  have hK := isProbKernel_discreteHelmholtz (le_refl 1) hh hth
  set U : ℤ → ℝ := fun m => discreteHelmholtz 1 h (helmRange h t) (e m) with hU
  have hUs : Summable U := (e.summable_iff (f := discreteHelmholtz 1 h (helmRange h t))).2 hK.2.1
  have heq : ∀ m : ℤ, U m - helmRange h t ^ 2 * lineGridLap h U m = if m = 0 then 1 else 0 := by
    intro m
    have h1 := discreteHelmholtz_eqn (le_refl 1) hh hth (e m)
    have hp : e m + zbasis 0 = e (m + 1) := by funext j; fin_cases j; simp [he, zbasis]
    have hm : e m - zbasis 0 = e (m - 1) := by funext j; fin_cases j; simp [he, zbasis]
    have h0 : deltaZ (e m) = if m = 0 then 1 else 0 := by
      unfold deltaZ
      congr 1
      exact propext ⟨fun h => by simpa [he] using congrFun h 0, fun h => by
        funext j; simp [he, h]⟩
    rw [gridLap, Fin.sum_univ_one, hp, hm, h0] at h1
    simp only [hU, lineGridLap]
    linarith
  have hUeq := (recursion_grid_green hh ht).2.2.1 U hUs heq
  intro n
  have hn : n = e (n 0) := by funext j; fin_cases j; simp [he]
  rw [hn, ← hUeq]
  simp [hU, he]

end Pyramids
