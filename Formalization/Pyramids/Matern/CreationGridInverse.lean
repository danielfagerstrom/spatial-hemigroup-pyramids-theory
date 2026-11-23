/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Fourier.Torus
import Pyramids.Line.KconvBdd
import Pyramids.Price.ResolventInstances

/-!
# `prop:creation-grid`(3): every bounded array is a record

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:creation-grid`. Phase 5, wave 3b (on the VM).
`creation_grid_3` moved here from `PyramidsSkeleton.Ch04Matern`, its conclusion unchanged. It no
longer takes `d ≥ 2`, `w ≠ δ₀` and `ŵ ≥ 0`, which its proof does not read, and takes `q ≥ 1` for
`q ≥ 2` (2026-11-15, a strengthening).

## The route

* **The Lévy kernel.** `w` is symmetric, so its law on `hℤ^d` is symmetric (its transform is real,
  `gridFourier_of_symm`) and has symmetric data `(A, ν)` (`exists_symData`, A39). The law is
  carried by the lattice `hℤ^d` (the `ℤ`-span of the basis `h e_i`), so
  `lem:lattice-infinitely-divisible` gives `A = 0` and `ν` finite and carried by `hℤ^d ∖ {0}`.
  Its point masses `a(n) := ν{hn}` form a summable symmetric kernel, and `ν` is the image of the
  measure `comap (n ↦ hn) ν` on `ℤ^d`, so the exponent is a sum:
  `ŵ(ϑ) = exp(-∑ a(n)(1 - cos⟨n,ϑ⟩)) = e^{-M} e^{â(ϑ)}`, `M := ∑ a` (`exists_levyKernel`).
* **The inverse.** `m := e^M ∑_k (-1)^k a^{*k}/k!` converges absolutely in `ℓ¹(ℤ^d)`, with norm at
  most `e^{2M}`, and its Fourier series is `e^M e^{-â}` (`gridFourier_tsum_kernels`). So
  `(w * m)^ = 1 = δ̂₀`, and the coefficients of an absolutely summable series are its terms
  (`gridCoeff_tsum`), so `w * m = δ₀` (`exists_kconv_inverse`).
* **The records.** Given a bounded array on level `k + 1`, extend it by `0` to a bounded `u` on
  level `k`; then `w * (m * u) = (w * m) * u = u` (`kconv_assoc_bdd`), which read on the coarser
  grid is the array, and induction on `k` gives the input.

The print's drift `z₀` and the compound Poisson law `π_w` are not needed: symmetry gives no drift.

**What it reaches.** The guard prints A39's `levy_khintchine_exists` and `_unique` (through
`exists_symData`), and `cited_A42` and `cited_A48` (through `lattice_infinitely_divisible`).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter Complex
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## Fourier series of kernels -/

/-- **The Fourier series of a symmetric kernel is real**: `λ̂(ϑ) = ∑ λ(n) cos⟨n,ϑ⟩`. -/
theorem gridFourier_of_symm {lam : Zd d → ℝ} (hl : Summable lam) (hs : ∀ n, lam (-n) = lam n)
    (θ : Fin d → ℝ) :
    gridFourier lam θ = ((∑' n, lam n * Real.cos (gphase θ n) : ℝ) : ℂ) := by
  have hs1 := summable_fourier_term hl θ
  have hs2 : Summable fun n => (lam n : ℂ) * cexp (-((gphase θ n : ℂ) * I)) :=
    Summable.of_norm (hl.norm.congr fun n => by
      rw [norm_mul, show -((gphase θ n : ℂ) * I) = ((-gphase θ n : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real])
  have h1 : gridFourier lam θ = ∑' n, (lam n : ℂ) * cexp (-((gphase θ n : ℂ) * I)) := by
    rw [gridFourier_eq, ← (Equiv.neg (Zd d)).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [Equiv.neg_apply, hs, gphase_neg]
    push_cast
    ring_nf
  have h2 : 2 * gridFourier lam θ = ∑' n, ((2 * (lam n * Real.cos (gphase θ n)) : ℝ) : ℂ) := by
    rw [two_mul]
    nth_rewrite 2 [h1]
    rw [gridFourier_eq, ← hs1.tsum_add hs2]
    refine tsum_congr fun n => ?_
    push_cast
    rw [Complex.cos]
    ring_nf
  have h3 : ∑' n, ((2 * (lam n * Real.cos (gphase θ n)) : ℝ) : ℂ) =
      2 * ((∑' n, lam n * Real.cos (gphase θ n) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_tsum, tsum_mul_left]
    push_cast
    ring
  rw [h3] at h2
  exact mul_left_cancel₀ two_ne_zero h2

theorem gridFourier_const_mul (c : ℝ) (lam : Zd d → ℝ) (θ : Fin d → ℝ) :
    gridFourier (fun n => c * lam n) θ = (c : ℂ) * gridFourier lam θ := by
  rw [gridFourier_eq, gridFourier_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  push_cast
  ring

/-- **The Fourier series of an absolutely convergent series of kernels** is the series of their
Fourier series. -/
theorem gridFourier_tsum_kernels {b : ℕ → Zd d → ℝ} (hb : ∀ k, Summable (b k))
    (hB : Summable fun k => ∑' n, |b k n|) (θ : Fin d → ℝ) :
    Summable (fun n => ∑' k, b k n) ∧
      gridFourier (fun n => ∑' k, b k n) θ = ∑' k, gridFourier (b k) θ := by
  have hP : Summable fun p : ℕ × Zd d => |b p.1 p.2| :=
    (summable_prod_of_nonneg fun _ => abs_nonneg _).2 ⟨fun k => (hb k).abs, hB⟩
  have hcol : ∀ n, Summable fun k => b k n := fun n =>
    Summable.of_abs (hP.prod_symm.prod_factor n)
  have hm : Summable fun n => ∑' k, b k n := by
    refine Summable.of_norm_bounded hP.prod_symm.prod fun n => ?_
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (hcol n).norm
  refine ⟨hm, ?_⟩
  set e : Zd d → ℂ := fun n => cexp ((gphase θ n : ℂ) * I) with he
  have hF : Summable fun p : ℕ × Zd d => (b p.1 p.2 : ℂ) * e p.2 :=
    Summable.of_norm (hP.congr fun p => by
      rw [he, norm_mul, norm_cexp_gphase, mul_one, Complex.norm_real, Real.norm_eq_abs])
  rw [gridFourier_eq]
  have e1 : ∀ n, ((∑' k, b k n : ℝ) : ℂ) * e n = ∑' k, (b k n : ℂ) * e n := fun n => by
    rw [Complex.ofReal_tsum, tsum_mul_right]
  change ∑' n, ((∑' k, b k n : ℝ) : ℂ) * e n = _
  simp_rw [e1]
  rw [hF.tsum_comm (f := fun k n => (b k n : ℂ) * e n)]
  rfl

/-- **The coefficients determine a summable kernel.** -/
theorem kernel_eq_of_gridFourier_eq {lam mu : Zd d → ℝ} (hl : Summable lam) (hm : Summable mu)
    (h : ∀ θ, gridFourier lam θ = gridFourier mu θ) : lam = mu := by
  have hk : ∀ {k : Zd d → ℝ}, Summable k → Summable fun n => ‖(k n : ℂ)‖ := fun hk => by
    simpa [Complex.norm_real, Real.norm_eq_abs] using summable_abs_iff.2 hk
  funext n
  have h1 := gridCoeff_tsum (hk hl) n
  have h2 := gridCoeff_tsum (hk hm) n
  have he : (fun θ => ∑' m, (lam m : ℂ) * cexp (((gphase θ m : ℝ) : ℂ) * I)) =
      fun θ => ∑' m, (mu m : ℂ) * cexp (((gphase θ m : ℝ) : ℂ) * I) := funext h
  rw [he, h2] at h1
  exact_mod_cast h1.symm

/-! ## Convolution powers -/

theorem kpow_nonneg_of_nonneg {a : Zd d → ℝ} (ha : ∀ n, 0 ≤ a n) : ∀ k n, 0 ≤ kpow a k n
  | 0, n => by unfold kpow deltaZ; split_ifs <;> norm_num
  | k + 1, n => tsum_nonneg fun m => mul_nonneg (kpow_nonneg_of_nonneg ha k m) (ha _)

theorem tsum_kpow {a : Zd d → ℝ} (hs : Summable a) : ∀ k, ∑' n, kpow a k n = (∑' n, a n) ^ k
  | 0 => by rw [pow_zero]; exact isProbKernel_deltaZ.2.2
  | k + 1 => by rw [kpow, tsum_kconv (summable_kpow hs k) hs, tsum_kpow hs k, pow_succ]

/-! ## The inverse of `w` -/

/-- **The inverse kernel** `e^M ∑_k (-1)^k a^{*k}/k!`, `M = ∑ a`. -/
noncomputable def expNegKernel (a : Zd d → ℝ) (n : Zd d) : ℝ :=
  ∑' k : ℕ, Real.exp (∑' j, a j) * ((-1) ^ k / k.factorial) * kpow a k n

theorem expNegKernel_spec {a : Zd d → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hsymm : ∀ n, a (-n) = a n) (θ : Fin d → ℝ) :
    Summable (expNegKernel a) ∧ gridFourier (expNegKernel a) θ =
      ((Real.exp (∑' j, a j) * Real.exp (-∑' n, a n * Real.cos (gphase θ n)) : ℝ) : ℂ) := by
  set M := ∑' j, a j with hM
  set c : ℕ → ℝ := fun k => Real.exp M * ((-1) ^ k / k.factorial) with hc
  set b : ℕ → Zd d → ℝ := fun k n => c k * kpow a k n with hb
  have hbk : ∀ k, Summable (b k) := fun k => (summable_kpow hs k).mul_left _
  have hbabs : ∀ k, ∑' n, |b k n| = Real.exp M * (M ^ k / k.factorial) := by
    intro k
    have : ∀ n, |b k n| = Real.exp M * (1 / k.factorial) * kpow a k n := fun n => by
      rw [hb, abs_mul, abs_of_nonneg (kpow_nonneg_of_nonneg ha k n), hc, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_div, abs_pow, abs_neg, abs_one, one_pow,
        Nat.abs_cast]
    simp_rw [this]
    rw [tsum_mul_left, tsum_kpow hs k]
    ring
  have hB : Summable fun k => ∑' n, |b k n| := by
    simp_rw [hbabs]
    exact (Real.summable_pow_div_factorial M).mul_left _
  obtain ⟨hsum, hF⟩ := gridFourier_tsum_kernels hbk hB θ
  refine ⟨hsum, ?_⟩
  set r := ∑' n, a n * Real.cos (gphase θ n) with hr
  have ha_hat : gridFourier a θ = (r : ℂ) := gridFourier_of_symm hs hsymm θ
  change gridFourier (fun n => ∑' k, b k n) θ = _
  rw [hF]
  have hterm : ∀ k, gridFourier (b k) θ = ((Real.exp M * ((-r) ^ k / k.factorial) : ℝ) : ℂ) := by
    intro k
    rw [hb, gridFourier_const_mul, gridFourier_kpow hs, ha_hat, hc]
    push_cast
    rw [neg_pow]
    ring
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, tsum_mul_left]
  congr 2
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-! ## The Lévy kernel of an infinitely divisible law on `hℤ^d` -/

/-- The basis `h e_i` of `ℝ^d`. -/
noncomputable def gridBasis {h : ℝ} (hh : h ≠ 0) : Module.Basis (Fin d) ℝ (Rd d) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.isUnitSMul (w := fun _ => h)
    fun _ => isUnit_iff_ne_zero.2 hh

theorem sum_smul_gridBasis {h : ℝ} (hh : h ≠ 0) (c : Fin d → ℝ) :
    ∑ i, c i • gridBasis (d := d) hh i = h • WithLp.toLp 2 c := by
  ext j
  simp [gridBasis, Module.Basis.isUnitSMul_apply, Pi.single_apply, mul_comm]

theorem latticePt_mem_span {h : ℝ} (hh : h ≠ 0) (n : Zd d) :
    latticePt h n ∈ Submodule.span ℤ (Set.range (gridBasis (d := d) hh)) := by
  have : latticePt h n = ∑ i, (n i) • gridBasis (d := d) hh i := by
    rw [latticePt, ← sum_smul_gridBasis hh]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_span_gridBasis {h : ℝ} (hh : h ≠ 0) {x : Rd d}
    (hx : x ∈ Submodule.span ℤ (Set.range (gridBasis (d := d) hh))) :
    ∃ n : Zd d, x = latticePt h n := by
  have h1 := (Module.Basis.mem_span_iff_repr_mem ℤ (gridBasis (d := d) hh) x).1 hx
  choose n hn using h1
  refine ⟨n, ?_⟩
  rw [latticePt, ← sum_smul_gridBasis hh]
  conv_lhs => rw [← (gridBasis (d := d) hh).sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hn i]
  rfl

theorem measurableEmbedding_latticePt {h : ℝ} (hh : h ≠ 0) :
    MeasurableEmbedding (latticePt (d := d) h) :=
  ⟨latticePt_injective hh, measurable_of_countable _,
    fun s _ => (s.to_countable.image _).measurableSet⟩

theorem latticePt_neg (h : ℝ) (n : Zd d) : latticePt h (-n) = -latticePt h n := by
  ext i
  simp [latticePt]

theorem inner_latticePt (h : ℝ) (ω : Rd d) (n : Zd d) :
    ⟪ω, latticePt h n⟫ = gphase (fun i => h * ω i) n := by
  rw [latticePt, real_inner_smul_right, gphase, PiLp.inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  ring

/-- **The Lévy kernel**: a symmetric infinitely divisible law on `hℤ^d` has
`ŵ(ϑ) = exp(-∑ a(n)(1 - cos⟨n,ϑ⟩))` with `a ≥ 0` summable and symmetric. -/
theorem exists_levyKernel {h : ℝ} (hh : 0 < h) {w : Zd d → ℝ} (hw : IsProbKernel w)
    (hsymm : ∀ n, w (-n) = w n) (hid : IsInfinitelyDivisible (zdLaw d h w)) :
    ∃ a : Zd d → ℝ, (∀ n, 0 ≤ a n) ∧ Summable a ∧ (∀ n, a (-n) = a n) ∧
      ∀ θ, gridFourier w θ =
        ((Real.exp (-∑' n, a n * (1 - Real.cos (gphase θ n))) : ℝ) : ℂ) := by
  haveI := isProbabilityMeasure_zdLaw (h := h) hw
  have hs : (zdLaw d h w).map (fun x => -x) = zdLaw d h w :=
    map_neg_eq_of_charFun_im fun ω => by
      rw [charFun_zdLaw hw, gridFourier_of_symm hw.2.1 hsymm, Complex.ofReal_im]
  obtain ⟨D, hD⟩ := exists_symData hid hs
  have hcarr : zdLaw d h w
      ((Submodule.span ℤ (Set.range (gridBasis (d := d) hh.ne')) : Set (Rd d)))ᶜ = 0 := by
    refine measure_mono_null (compl_subset_compl.2 fun x hxg => ?_) (zdLaw_gridSet_compl h w)
    obtain ⟨n, rfl⟩ := hxg
    exact latticePt_mem_span hh.ne' n
  obtain ⟨hA, hfin, hcar⟩ := lattice_infinitely_divisible _ hid _ (SymLevyData.hasTriplet hD)
    (Submodule.span ℤ (Set.range (gridBasis (d := d) hh.ne'))) hcarr
  have hA0 : D.A = 0 := by
    have h2 : (2 : ℝ) • D.A = 0 := hA
    exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
  haveI : IsFiniteMeasure D.ν := hfin
  set L := latticePt (d := d) h with hLdef
  have hL := measurableEmbedding_latticePt (d := d) hh.ne'
  have hrange : D.ν (range L)ᶜ = 0 := by
    refine measure_mono_null (compl_subset_compl.2 fun x hx' => ?_) hcar
    obtain ⟨n, rfl⟩ := mem_span_gridBasis hh.ne' hx'.1
    exact ⟨n, rfl⟩
  set ν' := D.ν.comap L with hν'
  haveI : IsFiniteMeasure ν' :=
    ⟨by rw [hν', hL.comap_apply, image_univ]; exact measure_lt_top _ _⟩
  have hmap : ν'.map L = D.ν := by
    rw [hν', hL.map_comap, Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hrange)]
  have hsing : ∀ n, ν' {n} = D.ν {L n} := fun n => by
    rw [hν', hL.comap_apply, image_singleton]
  set a : Zd d → ℝ := fun n => (D.ν {L n}).toReal with ha
  have hsumE : ∑' n, D.ν {L n} = ν' univ := by
    rw [← iUnion_of_singleton (α := Zd d), measure_iUnion
      (fun i j hij => disjoint_singleton.2 hij) fun n => measurableSet_singleton n]
    exact tsum_congr fun n => (hsing n).symm
  have has : Summable a := ENNReal.summable_toReal (by rw [hsumE]; exact measure_ne_top _ _)
  have hasymm : ∀ n, a (-n) = a n := fun n => by
    simp only [ha, hLdef, latticePt_neg]
    congr 1
    conv_rhs => rw [← D.ν_symm]
    rw [Measure.map_apply measurable_neg (measurableSet_singleton _)]
    congr 1
    ext x
    simp
  refine ⟨a, fun n => ENNReal.toReal_nonneg, has, hasymm, fun θ => ?_⟩
  set ω : Rd d := WithLp.toLp 2 fun i => θ i / h with hω
  have hθ : (fun i => h * ω i) = θ := by
    funext i
    simp only [hω]
    field_simp
  have h1 := charFun_zdLaw (h := h) hw ω
  rw [hθ, hD ω] at h1
  rw [← h1]
  congr 3
  rw [SymLevyData.exponent, pairExponent, hA0]
  simp only [quad_zero, zero_add]
  rw [← hmap, hL.integral_map]
  have hint : Integrable (fun n => 1 - Real.cos ⟪ω, L n⟫) ν' :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 2
      (ae_of_all _ fun n => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [Real.cos_le_one ⟪ω, L n⟫, Real.neg_one_le_cos ⟪ω, L n⟫])
  rw [integral_countable hint]
  refine tsum_congr fun n => ?_
  rw [measureReal_def, hsing, smul_eq_mul, hLdef, inner_latticePt, hθ]

/-- **`w` has an inverse in `ℓ¹(ℤ^d)`.** -/
theorem exists_kconv_inverse {h : ℝ} (hh : 0 < h) {w : Zd d → ℝ} (hw : IsProbKernel w)
    (hsymm : ∀ n, w (-n) = w n) (hid : IsInfinitelyDivisible (zdLaw d h w)) :
    ∃ m : Zd d → ℝ, Summable m ∧ kconv w m = deltaZ := by
  obtain ⟨a, ha0, has, hasymm, hw_hat⟩ := exists_levyKernel hh hw hsymm hid
  have hm := (expNegKernel_spec ha0 has hasymm 0).1
  refine ⟨expNegKernel a, hm, kernel_eq_of_gridFourier_eq (summable_kconv hw.2.1 hm) summable_deltaZ
    fun θ => ?_⟩
  rw [gridFourier_kconv hw.2.1 hm, gridFourier_deltaZ, hw_hat, (expNegKernel_spec ha0 has hasymm
    θ).2]
  have hs1 : Summable fun n => a n * (1 - Real.cos (gphase θ n)) :=
    Summable.of_norm_bounded (has.mul_right 2) fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 n)]
      refine mul_le_mul_of_nonneg_left ?_ (ha0 n)
      rw [abs_le]
      constructor <;> linarith [Real.cos_le_one (gphase θ n), Real.neg_one_le_cos (gphase θ n)]
  have hs2 : Summable fun n => a n * Real.cos (gphase θ n) :=
    Summable.of_norm_bounded has fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 n)]
      exact mul_le_of_le_one_right (ha0 n) (Real.abs_cos_le_one _)
  have hsplit : ∑' n, a n * (1 - Real.cos (gphase θ n)) =
      ∑' n, a n - ∑' n, a n * Real.cos (gphase θ n) := by
    rw [← has.tsum_sub hs2]
    exact tsum_congr fun n => by ring
  rw [hsplit, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  convert Complex.ofReal_one using 2
  rw [← Real.exp_zero]
  congr 1
  ring

/-! ## `prop:creation-grid`(3) -/

/-- **`prop:creation-grid`(3).** If `w` is infinitely divisible (as a law on `ℝ^d` carried by
`hℤ^d`) and `q ≥ 1` is an integer, then for every `k ≥ 0` every bounded array on `q^k hℤ^d` is the
level-`k` record `f_k` of a bounded input on `hℤ^d`. No `d ≥ 2`, `w ≠ δ₀` or `ŵ ≥ 0`, and `q ≥ 1`
for `q ≥ 2` (2026-11-15, a strengthening). -/
theorem creation_grid_3 {h : ℝ} (hh : 0 < h) (w : Zd d → ℝ) (hw : IsProbKernel w)
    (hsymm : ∀ n, w (-n) = w n) (hid : IsInfinitelyDivisible (zdLaw d h w)) (q : ℕ) (hq : 1 ≤ q)
    (k : ℕ) (A : Zd d → ℝ) (hA : ∃ C : ℝ, ∀ m, |A m| ≤ C) :
    ∃ f : Zd d → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) ∧ decimRecord w q f k = A := by
  obtain ⟨m, hm, hwm⟩ := exists_kconv_inverse hh hw hsymm hid
  have hinj : Function.Injective fun j : Zd d => (q : ℤ) • j := by
    intro a b hab
    funext l
    have := congrFun hab l
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ (by exact_mod_cast (show q ≠ 0 by omega)) this
  induction k generalizing A with
  | zero => exact ⟨A, hA, rfl⟩
  | succ k ih =>
    classical
    obtain ⟨C, hC⟩ := hA
    -- extend by `0` from `q ℤ^d`
    set u : Zd d → ℝ := fun n => if h : ∃ j, (q : ℤ) • j = n then A h.choose else 0 with hu
    have hub : ∃ C, ∀ n, |u n| ≤ C := ⟨max C 0, fun n => by
      simp only [hu]
      split_ifs
      · exact le_max_of_le_left (hC _)
      · simp⟩
    have huA : ∀ j, u ((q : ℤ) • j) = A j := fun j => by
      have hex : ∃ j', (q : ℤ) • j' = (q : ℤ) • j := ⟨j, rfl⟩
      simp only [hu, dif_pos hex]
      rw [hinj hex.choose_spec]
    obtain ⟨f, hf, hfk⟩ := ih (kconv m u) (kconv_bdd hm hub)
    refine ⟨f, hf, ?_⟩
    funext j
    change kconv w (decimRecord w q f k) ((q : ℤ) • j) = A j
    rw [hfk, ← kconv_assoc_bdd hw.2.1 hm hub, hwm, kconv_deltaZ_left, huA]

end Pyramids
