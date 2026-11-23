/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.SampledLaplacePyramid

/-!
# `prop:sampled-laplace-exact`(2): the computed level is not the sampled step from level 2

Blueprint: `blueprint/src/parts/02-line.tex`, `prop:sampled-laplace-exact`. Wave 3f:
`sampled_laplace_exact_2_later` moved here from `PyramidsSkeleton.Ch02Line`, its statement
unchanged. The route is the printed one (`SampledLaplacePyramid.lean` names it): both arrays are
sums of the geometric sequences `ρᵢ^{|m|}`, `ρᵢ = a^{q^{i+1}}`, `i < n`; independence makes the
ratios of their two last coefficients equal; and `u ↦ sinh u/u` strictly increasing separates the
ratios.
-/

namespace Pyramids

open MeasureTheory Set Filter
open ScaleSpace (laplaceDensity)
open scoped Topology Real

/-! ## The geometric kernels `g_β = N_β β^{|·|}` -/

/-- `ς_β := β/(1-β)²`. -/
noncomputable def geomSig (β : ℝ) : ℝ := β / (1 - β) ^ 2

/-- `N_β := (1-β)/(1+β)`. -/
noncomputable def geomN (β : ℝ) : ℝ := (1 - β) / (1 + β)

theorem geomN_pos {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) : 0 < geomN β :=
  div_pos (by linarith) (by linarith)

theorem geomSig_pos {β : ℝ} (h0 : 0 < β) (h1 : β < 1) : 0 < geomSig β :=
  div_pos h0 (pow_pos (by linarith) 2)

theorem geomSig_sub {β β' : ℝ} (h1 : β' < 1) (h2 : β < 1) :
    geomSig β - geomSig β' = (β - β') * (1 - β * β') / ((1 - β) ^ 2 * (1 - β') ^ 2) := by
  have : (1 : ℝ) - β ≠ 0 := by linarith
  have : (1 : ℝ) - β' ≠ 0 := by linarith
  unfold geomSig
  field_simp
  ring

theorem geomSig_lt {β β' : ℝ} (h0 : 0 < β') (h1 : β' < β) (h2 : β < 1) :
    geomSig β' < geomSig β := by
  have := geomSig_sub (h1.trans h2) h2
  have hp : 0 < (β - β') * (1 - β * β') / ((1 - β) ^ 2 * (1 - β') ^ 2) := by
    have : 0 < 1 - β * β' := by nlinarith
    have : (0 : ℝ) < 1 - β := by linarith
    have : (0 : ℝ) < 1 - β' := by linarith
    have : 0 < β - β' := by linarith
    positivity
  linarith

/-- **`g_β * g_{β'} = (ς_β g_β - ς_{β'} g_{β'})/(ς_β - ς_{β'})`**, by their transfers. -/
theorem zconv_geomKernel {β β' : ℝ} (h0 : 0 < β') (h1 : β' < β) (h2 : β < 1) :
    zconv (geomKernel β) (geomKernel β') = fun m =>
      geomSig β / (geomSig β - geomSig β') * geomKernel β m +
        -geomSig β' / (geomSig β - geomSig β') * geomKernel β' m := by
  have hb0 : 0 ≤ β := by linarith
  have hs := summable_geomKernel hb0 h2
  have hs' := summable_geomKernel h0.le (h1.trans h2)
  refine eq_of_lineFourierSeries_eq (summable_zconv hs hs')
    ((hs.mul_left _).add (hs'.mul_left _)) fun θ => ?_
  rw [lineFourierSeries_zconv hs hs', lineFourierSeries_add_smul hs hs',
    lineFourierSeries_geomKernel hb0 h2, lineFourierSeries_geomKernel h0.le (h1.trans h2)]
  have hD := geom_denom_pos' hb0 h2 θ
  have hD' := geom_denom_pos' h0.le (h1.trans h2) θ
  have hE := geomSig_sub (h1.trans h2) h2
  have e1 : (1 : ℝ) - β ≠ 0 := by linarith
  have e2 : (1 : ℝ) - β' ≠ 0 := by linarith
  have e3 : β - β' ≠ 0 := by linarith
  have e4 : 1 - β * β' ≠ 0 := by nlinarith
  have hrel : β * (1 - 2 * β' * Real.cos θ + β' ^ 2) - (1 - 2 * β * Real.cos θ + β ^ 2) * β' =
      (β - β') * (1 - β * β') := by ring
  rw [← Complex.ofReal_mul]
  generalize 1 - 2 * β * Real.cos θ + β ^ 2 = D at hD hrel ⊢
  generalize 1 - 2 * β' * Real.cos θ + β' ^ 2 = D' at hD' hrel ⊢
  have key : (1 - β) ^ 2 / D * ((1 - β') ^ 2 / D') =
      geomSig β / (geomSig β - geomSig β') * ((1 - β) ^ 2 / D) +
        -geomSig β' / (geomSig β - geomSig β') * ((1 - β') ^ 2 / D') := by
    have hDD : D * D' ≠ 0 := mul_ne_zero hD.ne' hD'.ne'
    calc (1 - β) ^ 2 / D * ((1 - β') ^ 2 / D') =
          (1 - β) ^ 2 * (1 - β') ^ 2 / ((β - β') * (1 - β * β')) *
            ((β - β') * (1 - β * β') / (D * D')) := by
          field_simp
      _ = (1 - β) ^ 2 * (1 - β') ^ 2 / ((β - β') * (1 - β * β')) * (β / D - β' / D') := by
          rw [div_sub_div _ _ hD.ne' hD'.ne', hrel]
      _ = _ := by
          rw [hE]
          unfold geomSig
          field_simp
          ring
  rw [key]
  push_cast
  ring

/-- `g_β * β'^{|·|} = (ς_β N_β/(N_{β'}(ς_β - ς_{β'}))) β^{|·|} - (ς_{β'}/(ς_β - ς_{β'}))β'^{|·|}`.
-/
theorem zconv_geomKernel_pow {β β' : ℝ} (h0 : 0 < β') (h1 : β' < β) (h2 : β < 1) (n : ℤ) :
    ∑' j, geomKernel β j * β' ^ (n - j).natAbs =
      geomSig β / (geomSig β - geomSig β') * geomN β / geomN β' * β ^ n.natAbs +
        -geomSig β' / (geomSig β - geomSig β') * β' ^ n.natAbs := by
  have hN' := geomN_pos h0.le (h1.trans h2)
  have hne : geomSig β - geomSig β' ≠ 0 := (sub_pos.2 (geomSig_lt h0 h1 h2)).ne'
  have e1 : (1 : ℝ) + β' ≠ 0 := by linarith
  have e2 : (1 : ℝ) - β' ≠ 0 := by linarith
  have e3 : (1 : ℝ) + β ≠ 0 := by linarith
  have e : ∀ j, geomKernel β j * β' ^ (n - j).natAbs =
      (geomN β')⁻¹ * (geomKernel β j * geomKernel β' (n - j)) := by
    intro j
    simp only [geomKernel, geomN]
    field_simp
  simp_rw [e]
  rw [tsum_mul_left, show (∑' j, geomKernel β j * geomKernel β' (n - j)) =
    zconv (geomKernel β) (geomKernel β') n from rfl, zconv_geomKernel h0 h1 h2]
  simp only [geomKernel, geomN]
  field_simp

/-! ## The computed level -/

section Computed

variable {h c t : ℝ} {q : ℕ}

/-- The ratios `ρᵢ := a^{q^{i+1}}`. -/
noncomputable def lvRho (h c t : ℝ) (q : ℕ) (i : ℕ) : ℝ := slRatio h (c * t) ^ (q ^ (i + 1))

/-- `A_i := ς_a/(ς_a - ς_{ρᵢ})`. -/
noncomputable def lvA (h c t : ℝ) (q : ℕ) (i : ℕ) : ℝ :=
  geomSig (slRatio h (c * t)) / (geomSig (slRatio h (c * t)) - geomSig (lvRho h c t q i))

/-- `B_i := -ς_{ρᵢ}/(ς_a - ς_{ρᵢ})`. -/
noncomputable def lvB (h c t : ℝ) (q : ℕ) (i : ℕ) : ℝ :=
  -geomSig (lvRho h c t q i) / (geomSig (slRatio h (c * t)) - geomSig (lvRho h c t q i))

variable (hh : 0 < h) (hq : 2 ≤ q) (hc : 0 < c) (ht : 0 < t)
include hh hq hc ht

theorem lvRho_mem (i : ℕ) : 0 < lvRho h c t q i ∧ lvRho h c t q i < slRatio h (c * t) := by
  have ha0 := slRatio_pos (h := h) (mul_pos hc ht)
  have ha1 := slRatio_lt_one hh (c * t)
  refine ⟨pow_pos ha0 _, pow_lt_self_of_lt_one₀ ha0 ha1 ?_⟩
  exact Nat.one_lt_pow (by omega) (by omega)

omit hh hq hc ht in
theorem lvRho_pow (i : ℕ) : lvRho h c t q i ^ q = lvRho h c t q (i + 1) := by
  unfold lvRho
  rw [← pow_mul, pow_succ (q : ℕ) (i + 1)]

theorem lvB_ne_zero (i : ℕ) : lvB h c t q i ≠ 0 := by
  obtain ⟨h0, h1⟩ := lvRho_mem hh hq hc ht i
  have ha1 := slRatio_lt_one hh (c * t)
  have := geomSig_pos h0 (h1.trans ha1)
  have := geomSig_lt h0 h1 ha1
  unfold lvB
  exact div_ne_zero (by linarith) (by linarith)

/-- One step of the computation on a sum of geometric sequences. -/
theorem pyramidLevels_succ_expand {n : ℕ} (b : ℕ → ℝ)
    (hb : ∀ m, pyramidLevels (slKernel h (c * t)) q n m =
      ∑ i ∈ Finset.range n, b i * lvRho h c t q i ^ m.natAbs) (m : ℤ) :
    pyramidLevels (slKernel h (c * t)) q (n + 1) m =
      (∑ i ∈ Finset.range n, b i * lvA h c t q i * geomN (slRatio h (c * t)) /
          geomN (lvRho h c t q i)) * lvRho h c t q 0 ^ m.natAbs +
        ∑ i ∈ Finset.range n, b i * lvB h c t q i * lvRho h c t q (i + 1) ^ m.natAbs := by
  set a := slRatio h (c * t) with ha
  have ha0 : 0 < a := slRatio_pos (mul_pos hc ht)
  have ha1 : a < 1 := slRatio_lt_one hh _
  have hg := summable_geomKernel ha0.le ha1
  rw [show pyramidLevels (slKernel h (c * t)) q (n + 1) m =
    zconv (slKernel h (c * t)) (pyramidLevels (slKernel h (c * t)) q n) (q * m) from rfl, zconv]
  simp_rw [hb, Finset.mul_sum]
  rw [Summable.tsum_finsetSum fun i _ => ?_]
  · have hterm : ∀ i ∈ Finset.range n, ∑' j, slKernel h (c * t) j *
        (b i * lvRho h c t q i ^ ((q : ℤ) * m - j).natAbs) =
        b i * lvA h c t q i * geomN a / geomN (lvRho h c t q i) * lvRho h c t q 0 ^ m.natAbs +
          b i * lvB h c t q i * lvRho h c t q (i + 1) ^ m.natAbs := by
      intro i _
      obtain ⟨hr0, hr1⟩ := lvRho_mem hh hq hc ht i
      have e : ∀ j, slKernel h (c * t) j * (b i * lvRho h c t q i ^ ((q : ℤ) * m - j).natAbs) =
          b i * (geomKernel a j * lvRho h c t q i ^ ((q : ℤ) * m - j).natAbs) := fun j => by
        rw [slKernel, ← ha]; ring
      simp_rw [e]
      rw [tsum_mul_left, zconv_geomKernel_pow hr0 hr1 ha1, natAbs_mul_nat, pow_mul, pow_mul,
        lvRho_pow]
      have h0 : a ^ q = lvRho h c t q 0 := by rw [lvRho, zero_add, pow_one]
      rw [h0, lvA, lvB, ← ha]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_mul]
  · have hy : IsBoundedSeq fun k : ℤ => b i * lvRho h c t q i ^ k.natAbs := ⟨|b i|, fun k => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (lvRho_mem hh hq hc ht i).1.le _)]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (pow_le_one₀ (lvRho_mem hh hq hc ht i).1.le
          ((lvRho_mem hh hq hc ht i).2.trans (slRatio_lt_one hh _)).le)⟩
    have hg' : Summable (slKernel h (c * t)) := hg
    exact summable_zconv_term_bdd hg' hy _

/-- **The computed level as a sum of geometric sequences**, with its two last coefficients. -/
theorem pyramidLevels_expand {n : ℕ} (hn : 1 ≤ n) :
    ∃ b : ℕ → ℝ, (∀ m, pyramidLevels (slKernel h (c * t)) q n m =
        ∑ i ∈ Finset.range n, b i * lvRho h c t q i ^ m.natAbs) ∧
      b (n - 1) = geomN (slRatio h (c * t)) * ∏ i ∈ Finset.range (n - 1), lvB h c t q i ∧
      (2 ≤ n → b (n - 2) = geomN (slRatio h (c * t)) * lvA h c t q 0 *
        geomN (slRatio h (c * t)) / geomN (lvRho h c t q 0) *
          ∏ i ∈ Finset.range (n - 2), lvB h c t q i) := by
  set a := slRatio h (c * t) with ha
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨fun _ => geomN a, fun m => ?_, by simp, fun h2 => by omega⟩
    rw [pyramidLevels_one, Finset.sum_range_one, slKernel, geomKernel, ← ha, ← geomN,
      natAbs_mul_nat, pow_mul, lvRho, zero_add, pow_one]
  | succ n hn ih =>
    obtain ⟨b, hb, hb1, hb2⟩ := ih
    refine ⟨fun i => if i = 0 then ∑ j ∈ Finset.range n, b j * lvA h c t q j * geomN a /
      geomN (lvRho h c t q j) else b (i - 1) * lvB h c t q (i - 1), fun m => ?_, ?_, fun _ => ?_⟩
    · rw [pyramidLevels_succ_expand hh hq hc ht b hb, Finset.sum_range_succ']
      beta_reduce
      rw [if_pos rfl, add_comm]
      congr 1
    · beta_reduce
      rw [Nat.add_sub_cancel, if_neg (by omega), hb1, show n = n - 1 + 1 by omega,
        Finset.prod_range_succ, Nat.add_sub_cancel]
      ring
    · beta_reduce
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · have hn1 : n = 1 := by omega
        subst hn1
        rw [show 1 + 1 - 2 = 0 by rfl, if_pos rfl, Finset.sum_range_one, Finset.prod_range_zero,
          mul_one]
        rw [show (1 : ℕ) - 1 = 0 by rfl, Finset.prod_range_zero, mul_one] at hb1
        rw [hb1]
      · rw [show n + 1 - 2 = n - 1 by omega, if_neg (by omega),
          show n - 1 - 1 = n - 2 by omega, hb2 hn2, show n - 1 = n - 2 + 1 by omega,
          Finset.prod_range_succ]
        ring

end Computed

/-! ## Geometric sequences with distinct ratios are independent -/

theorem geom_indep {ρ : ℕ → ℝ} (S : Finset ℕ) (hρ : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ρ i ≠ ρ j) :
    ∀ d : ℕ → ℝ, (∀ m : ℕ, ∑ i ∈ S, d i * ρ i ^ m = 0) → ∀ i ∈ S, d i = 0 := by
  induction S using Finset.induction_on with
  | empty => intro d _ i hi; simp at hi
  | insert j S hj ih =>
    intro d hd
    have hρ' : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → ρ i ≠ ρ k := fun i hi k hk =>
      hρ i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk)
    have hS : ∀ i ∈ S, d i * (ρ i - ρ j) = 0 := by
      refine ih hρ' (fun i => d i * (ρ i - ρ j)) fun m => ?_
      have h1 := hd (m + 1)
      have h2 := hd m
      rw [Finset.sum_insert hj] at h1 h2
      have : ∑ i ∈ S, d i * (ρ i - ρ j) * ρ i ^ m =
          ∑ i ∈ S, d i * ρ i ^ (m + 1) - ρ j * ∑ i ∈ S, d i * ρ i ^ m := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [this]
      linear_combination h1 - ρ j * h2
    have hS0 : ∀ i ∈ S, d i = 0 := fun i hi => by
      have hne : ρ i - ρ j ≠ 0 := sub_ne_zero.2 (hρ i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_self j S) fun h => hj (h ▸ hi))
      exact (mul_eq_zero.1 (hS i hi)).resolve_right hne
    have hj0 : d j = 0 := by
      have h0 := hd 0
      rw [Finset.sum_insert hj, Finset.sum_eq_zero fun i hi => by rw [hS0 i hi, zero_mul]] at h0
      simpa using h0
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hj0
    · exact hS0 i hi

/-! ## The sampled step: `L_r * L_s` and the chain -/

theorem laplaceDensity_le {s : ℝ} (hs : 0 < s) (x : ℝ) : laplaceDensity s x ≤ (2 * s)⁻¹ := by
  rw [ScaleSpace.laplaceDensity]
  have : Real.exp (-(|x| / s)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ |x| / s := by positivity
    linarith)
  have : 0 < (2 * s)⁻¹ := by positivity
  nlinarith

theorem integrable_mul_laplace_shift {f : ℝ → ℝ} (hf : Integrable f) {s : ℝ} (hs : 0 < s)
    (x : ℝ) : Integrable fun y => f y * laplaceDensity s (x - y) :=
  hf.mul_bdd (c := (2 * s)⁻¹)
    ((ScaleSpace.continuous_laplaceDensity s).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ScaleSpace.laplaceDensity_nonneg hs _)]
      exact laplaceDensity_le hs _)

theorem lineConv_laplace_of_nonneg {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) {x : ℝ}
    (hx : 0 ≤ x) : lineConv (laplaceDensity r) (laplaceDensity s) x =
      (r ^ 2 * laplaceDensity r x - s ^ 2 * laplaceDensity s x) / (r ^ 2 - s ^ 2) := by
  have hfi := integrable_mul_laplace_shift (ScaleSpace.integrable_laplaceDensity hr) hs x
  have hα : 0 < 1 / r + 1 / s := by positivity
  have hc : 1 / s - 1 / r ≠ 0 := by
    intro h0
    apply hrs
    field_simp at h0
    linarith
  have h1 : ∫ y in Iic 0, laplaceDensity r y * laplaceDensity s (x - y) =
      (2 * r)⁻¹ * (2 * s)⁻¹ * Real.exp (-x / s) * (1 / (1 / r + 1 / s)) := by
    rw [setIntegral_congr_fun measurableSet_Iic (g := fun y => (2 * r)⁻¹ * (2 * s)⁻¹ *
      Real.exp (-x / s) * Real.exp ((1 / r + 1 / s) * y)) fun y (hy : y ≤ 0) => ?_]
    · rw [integral_const_mul, integral_exp_mul_Iic hα, mul_zero, Real.exp_zero]
    · simp only [ScaleSpace.laplaceDensity]
      rw [abs_of_nonpos hy, abs_of_nonneg (by linarith : 0 ≤ x - y)]
      have e : Real.exp (-(-y / r)) * Real.exp (-((x - y) / s)) =
          Real.exp (-x / s) * Real.exp ((1 / r + 1 / s) * y) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp
        ring
      linear_combination (2 * r)⁻¹ * (2 * s)⁻¹ * e
  have h2 : ∫ y in Ioc 0 x, laplaceDensity r y * laplaceDensity s (x - y) =
      (2 * r)⁻¹ * (2 * s)⁻¹ * Real.exp (-x / s) *
        ((Real.exp ((1 / s - 1 / r) * x) - 1) / (1 / s - 1 / r)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun y => (2 * r)⁻¹ * (2 * s)⁻¹ *
      Real.exp (-x / s) * Real.exp ((1 / s - 1 / r) * y)) fun y (hy : y ∈ Ioc 0 x) => ?_]
    · rw [integral_const_mul, ← intervalIntegral.integral_of_le hx,
        intervalIntegral.integral_comp_mul_left (fun y => Real.exp y) hc, integral_exp, mul_zero,
        Real.exp_zero, smul_eq_mul]
      ring
    · simp only [ScaleSpace.laplaceDensity]
      rw [abs_of_pos hy.1, abs_of_nonneg (by linarith [hy.2] : 0 ≤ x - y)]
      have e : Real.exp (-(y / r)) * Real.exp (-((x - y) / s)) =
          Real.exp (-x / s) * Real.exp ((1 / s - 1 / r) * y) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp
        ring
      linear_combination (2 * r)⁻¹ * (2 * s)⁻¹ * e
  have h3 : ∫ y in Ioi x, laplaceDensity r y * laplaceDensity s (x - y) =
      (2 * r)⁻¹ * (2 * s)⁻¹ * Real.exp (x / s) *
        (Real.exp (-(1 / r + 1 / s) * x) / (1 / r + 1 / s)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun y => (2 * r)⁻¹ * (2 * s)⁻¹ *
      Real.exp (x / s) * Real.exp (-(1 / r + 1 / s) * y)) fun y (hy : x < y) => ?_]
    · rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x, neg_div_neg_eq]
    · simp only [ScaleSpace.laplaceDensity]
      rw [abs_of_pos (by linarith : 0 < y), abs_of_neg (by linarith : x - y < 0)]
      have e : Real.exp (-(y / r)) * Real.exp (-(-(x - y) / s)) =
          Real.exp (x / s) * Real.exp (-(1 / r + 1 / s) * y) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        field_simp
        ring
      linear_combination (2 * r)⁻¹ * (2 * s)⁻¹ * e
  have hdisj : Disjoint (Ioc 0 x) (Ioi x) :=
    Set.disjoint_left.2 fun y hy1 hy2 => absurd hy1.2 (not_le.2 hy2)
  have hsplit : lineConv (laplaceDensity r) (laplaceDensity s) x =
      (∫ y in Iic 0, laplaceDensity r y * laplaceDensity s (x - y)) +
      ((∫ y in Ioc 0 x, laplaceDensity r y * laplaceDensity s (x - y)) +
        ∫ y in Ioi x, laplaceDensity r y * laplaceDensity s (x - y)) := by
    rw [lineConv, ← integral_add_compl measurableSet_Iic hfi, compl_Iic,
      ← Ioc_union_Ioi_eq_Ioi hx, setIntegral_union hdisj measurableSet_Ioi hfi.integrableOn
        hfi.integrableOn]
  rw [hsplit, h1, h2, h3]
  have hX : Real.exp ((1 / s - 1 / r) * x) = Real.exp (-x / r) / Real.exp (-x / s) := by
    rw [eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hZ : Real.exp (-(1 / r + 1 / s) * x) = Real.exp (-x / r) / Real.exp (x / s) := by
    rw [eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hrs2 : r ^ 2 - s ^ 2 ≠ 0 := by
    intro h0
    have : (r - s) * (r + s) = 0 := by linear_combination h0
    rcases mul_eq_zero.1 this with h | h
    · exact hrs (by linarith)
    · linarith
  have hE1 := Real.exp_pos (-x / r)
  have hE2 := Real.exp_pos (-x / s)
  have hY := Real.exp_pos (x / s)
  simp only [ScaleSpace.laplaceDensity, abs_of_nonneg hx]
  rw [hX, hZ, ← neg_div, ← neg_div]
  field_simp
  ring

theorem lineConv_laplace_neg (r s x : ℝ) :
    lineConv (laplaceDensity r) (laplaceDensity s) (-x) =
      lineConv (laplaceDensity r) (laplaceDensity s) x := by
  unfold lineConv
  rw [← integral_neg_eq_self]
  congr 1
  funext y
  simp only [ScaleSpace.laplaceDensity]
  rw [abs_neg, show -x - -y = -(x - y) by ring, abs_neg]

/-- **`L_r * L_s = (r²L_r - s²L_s)/(r² - s²)`** for `r ≠ s`, pointwise. -/
theorem lineConv_laplace {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) (x : ℝ) :
    lineConv (laplaceDensity r) (laplaceDensity s) x =
      (r ^ 2 * laplaceDensity r x - s ^ 2 * laplaceDensity s x) / (r ^ 2 - s ^ 2) := by
  rcases le_total 0 x with hx | hx
  · exact lineConv_laplace_of_nonneg hr hs hrs hx
  · have hL : ∀ u, laplaceDensity u (-x) = laplaceDensity u x := fun u => by
      simp only [ScaleSpace.laplaceDensity, abs_neg]
    rw [← neg_neg x, lineConv_laplace_neg, lineConv_laplace_of_nonneg hr hs hrs (by linarith),
      hL, hL, neg_neg]

theorem lineConv_sum_laplace (S : Finset ℕ) (A : ℕ → ℝ) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) {s : ℝ}
    (hs : 0 < s) (x : ℝ) :
    lineConv (fun y => ∑ k ∈ S, A k * laplaceDensity (r k) y) (laplaceDensity s) x =
      ∑ k ∈ S, A k * lineConv (laplaceDensity (r k)) (laplaceDensity s) x := by
  unfold lineConv
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ fun k _ => (integrable_mul_laplace_shift
    (ScaleSpace.integrable_laplaceDensity (hr k)) hs x).const_mul (A k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]

/-- **The sampled step as a sum of Laplace densities**, with its two first coefficients. -/
theorem chain_expand {R Q : ℝ} (hR : 0 < R) (hQ : 1 < Q) (N : ℕ) :
    ∃ A : ℕ → ℝ, (∀ x, laplaceChainDensity (fun k => R * Q ^ k) N x =
        ∑ k ∈ Finset.range (N + 1), A k * laplaceDensity (R * Q ^ k) x) ∧
      A 0 = (∏ j ∈ Finset.range N, (1 - (Q ^ 2) ^ (j + 1)))⁻¹ ∧
      (1 ≤ N → A 1 = Q ^ 2 / (Q ^ 2 - 1) *
        (∏ j ∈ Finset.range (N - 1), (1 - (Q ^ 2) ^ (j + 1)))⁻¹) := by
  have hQ0 : 0 < Q := by linarith
  have hr : ∀ k : ℕ, 0 < R * Q ^ k := fun k => by positivity
  have hQ2 : 1 < Q ^ 2 := by nlinarith
  have hpow : ∀ j : ℕ, 1 ≤ j → 1 - (Q ^ 2) ^ j ≠ 0 := fun j hj => by
    have := one_lt_pow₀ hQ2 (by omega : j ≠ 0)
    linarith
  have hprod : ∀ N : ℕ, ∏ j ∈ Finset.range N, (1 - (Q ^ 2) ^ (j + 1)) ≠ 0 := fun N =>
    Finset.prod_ne_zero_iff.2 fun j _ => hpow (j + 1) (by omega)
  have hne : ∀ k j : ℕ, k < j → (R * Q ^ k) ^ 2 - (R * Q ^ j) ^ 2 ≠ 0 := by
    intro k j hkj h0
    have : Q ^ k < Q ^ j := pow_lt_pow_right₀ hQ hkj
    have : R * Q ^ k < R * Q ^ j := mul_lt_mul_of_pos_left this hR
    nlinarith [hr k]
  induction N with
  | zero =>
    refine ⟨fun _ => 1, fun x => ?_, by simp, fun h => by omega⟩
    simp [laplaceChainDensity]
  | succ N ih =>
    obtain ⟨A, hA, hA0, hA1⟩ := ih
    have hq2 : ∀ j : ℕ, (R * Q ^ j) ^ 2 = R ^ 2 * (Q ^ 2) ^ j := fun j => by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j 2]
    refine ⟨fun k => if k ≤ N then A k * (R * Q ^ k) ^ 2 /
        ((R * Q ^ k) ^ 2 - (R * Q ^ (N + 1)) ^ 2) else
      -∑ j ∈ Finset.range (N + 1), A j * (R * Q ^ (N + 1)) ^ 2 /
        ((R * Q ^ j) ^ 2 - (R * Q ^ (N + 1)) ^ 2), fun x => ?_, ?_, fun _ => ?_⟩
    · have hch : laplaceChainDensity (fun k => R * Q ^ k) N = fun y =>
          ∑ k ∈ Finset.range (N + 1), A k * laplaceDensity (R * Q ^ k) y := funext hA
      rw [show laplaceChainDensity (fun k => R * Q ^ k) (N + 1) x =
        lineConv (laplaceChainDensity (fun k => R * Q ^ k) N)
          (laplaceDensity (R * Q ^ (N + 1))) x from rfl, hch,
        lineConv_sum_laplace _ _ hr (hr _), Finset.sum_range_succ _ (N + 1)]
      beta_reduce
      rw [if_neg (by omega : ¬ (N + 1 ≤ N))]
      have : ∀ k ∈ Finset.range (N + 1), A k * lineConv (laplaceDensity (R * Q ^ k))
          (laplaceDensity (R * Q ^ (N + 1))) x =
          (if k ≤ N then A k * (R * Q ^ k) ^ 2 / ((R * Q ^ k) ^ 2 - (R * Q ^ (N + 1)) ^ 2) else
            -∑ j ∈ Finset.range (N + 1), A j * (R * Q ^ (N + 1)) ^ 2 /
              ((R * Q ^ j) ^ 2 - (R * Q ^ (N + 1)) ^ 2)) * laplaceDensity (R * Q ^ k) x -
          A k * (R * Q ^ (N + 1)) ^ 2 / ((R * Q ^ k) ^ 2 - (R * Q ^ (N + 1)) ^ 2) *
            laplaceDensity (R * Q ^ (N + 1)) x := by
        intro k hk
        rw [Finset.mem_range] at hk
        have hk' : R * Q ^ k ≠ R * Q ^ (N + 1) := fun h0 =>
          hne k (N + 1) (by omega) (by rw [h0]; ring)
        rw [if_pos (by omega), lineConv_laplace (hr k) (hr _) hk']
        have := hne k (N + 1) (by omega)
        field_simp
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    · beta_reduce
      rw [if_pos (Nat.zero_le N), hA0, Finset.prod_range_succ, hq2, hq2, pow_zero, mul_one]
      have h1 := hprod N
      have h2 := hpow (N + 1) (by omega)
      have hR2 : R ^ 2 ≠ 0 := by positivity
      field_simp
    · beta_reduce
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · rw [if_neg (by omega), Finset.sum_range_one, hA0, hq2, hq2]
        simp only [Finset.range_zero, Finset.prod_empty, inv_one, pow_zero, mul_one, zero_add,
          pow_one, one_mul]
        have hQ2' : Q ^ 2 - 1 ≠ 0 := by linarith
        have hR2 : R ^ 2 ≠ 0 := by positivity
        have : R ^ 2 - R ^ 2 * Q ^ 2 ≠ 0 := by
          intro h0
          have : R ^ 2 * (1 - Q ^ 2) = 0 := by linear_combination h0
          rcases mul_eq_zero.1 this with h | h
          · exact hR2 h
          · linarith
        have h1Q : 1 - Q ^ 2 ≠ 0 := by linarith
        field_simp
        ring
      · rw [if_pos (by omega), hA1 hN, hq2, hq2, pow_one]
        rw [show N + 1 - 1 = N - 1 + 1 by omega, Finset.prod_range_succ, Nat.sub_add_cancel hN]
        have h1 := hprod (N - 1)
        have h2 := hpow N hN
        have hQ2' : Q ^ 2 - 1 ≠ 0 := by linarith
        have hR2 : R ^ 2 ≠ 0 := by positivity
        have hQ2'' : Q ^ 2 ≠ 0 := by positivity
        rw [show (Q ^ 2) ^ (N + 1) = Q ^ 2 * (Q ^ 2) ^ N by ring]
        field_simp

/-! ## The hyperbolic forms and the inequality -/

theorem strictMonoOn_sinh_div : StrictMonoOn (fun u : ℝ => Real.sinh u / u) (Ioi 0) := by
  have hk : ∀ u : ℝ, 0 < u → 0 < u * Real.cosh u - Real.sinh u := by
    have hmono : StrictMonoOn (fun u : ℝ => u * Real.cosh u - Real.sinh u) (Ici 0) := by
      refine strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop) fun u hu => ?_
      rw [interior_Ici] at hu
      have hd : HasDerivAt (fun u : ℝ => u * Real.cosh u - Real.sinh u)
          (1 * Real.cosh u + u * Real.sinh u - Real.cosh u) u :=
        ((hasDerivAt_id' u).mul (Real.hasDerivAt_cosh u)).sub (Real.hasDerivAt_sinh u)
      rw [hd.deriv, show 1 * Real.cosh u + u * Real.sinh u - Real.cosh u = u * Real.sinh u by ring]
      exact mul_pos hu (Real.sinh_pos_iff.2 hu)
    intro u hu
    have := hmono self_mem_Ici (show u ∈ Ici (0 : ℝ) from hu.le) hu
    simpa using this
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ fun u hu => ?_
  · exact Real.continuous_sinh.continuousOn.div continuousOn_id fun u hu => ne_of_gt hu
  · rw [interior_Ioi] at hu
    have hd : HasDerivAt (fun u : ℝ => Real.sinh u / u)
        ((Real.cosh u * u - Real.sinh u * 1) / u ^ 2) u :=
      (Real.hasDerivAt_sinh u).div (hasDerivAt_id u) (ne_of_gt hu)
    rw [hd.deriv]
    have := hk u hu
    exact div_pos (by linarith) (pow_pos hu 2)

theorem sinhDiv_pos {u : ℝ} (hu : 0 < u) : 0 < Real.sinh u / u :=
  div_pos (Real.sinh_pos_iff.2 hu) hu

/-- `q sinh x < sinh(qx)` for `q > 1`, `x > 0`. -/
theorem q_sinh_lt {q x : ℝ} (hq : 1 < q) (hx : 0 < x) : q * Real.sinh x < Real.sinh (q * x) := by
  have hqx : x < q * x := by nlinarith
  have hqx0 : 0 < q * x := by nlinarith
  have := strictMonoOn_sinh_div (show x ∈ Ioi (0 : ℝ) from hx) (show q * x ∈ Ioi (0 : ℝ) from hqx0)
    hqx
  rw [div_lt_div_iff₀ hx hqx0] at this
  exact lt_of_mul_lt_mul_right (by nlinarith : q * Real.sinh x * x < Real.sinh (q * x) * x)
    hx.le

theorem cosh_sub_cosh_eq (x y : ℝ) :
    Real.cosh (y * x) - Real.cosh x =
      2 * Real.sinh ((y + 1) * x / 2) * Real.sinh ((y - 1) * x / 2) := by
  have h1 := Real.cosh_add ((y + 1) * x / 2) ((y - 1) * x / 2)
  have h2 := Real.cosh_sub ((y + 1) * x / 2) ((y - 1) * x / 2)
  rw [show (y + 1) * x / 2 + (y - 1) * x / 2 = y * x by ring] at h1
  rw [show (y + 1) * x / 2 - (y - 1) * x / 2 = x by ring] at h2
  linarith

theorem cosh_ratio_repr {x y : ℝ} (hx : 0 < x) (hy : 1 < y) :
    (Real.cosh (y * x) - Real.cosh x) / (y ^ 2 - 1) =
      x ^ 2 / 2 * (Real.sinh ((y + 1) * x / 2) / ((y + 1) * x / 2) *
        (Real.sinh ((y - 1) * x / 2) / ((y - 1) * x / 2))) := by
  rw [cosh_sub_cosh_eq]
  have h1 : (y + 1) * x / 2 ≠ 0 := (div_pos (mul_pos (by linarith) hx) two_pos).ne'
  have h2 : (y - 1) * x / 2 ≠ 0 := (div_pos (mul_pos (by linarith) hx) two_pos).ne'
  have h3 : y ^ 2 - 1 ≠ 0 := by nlinarith
  have h4 : y + 1 ≠ 0 := by linarith
  have h5 : y - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `y ↦ (cosh(yx) - cosh x)/(y² - 1)` is nondecreasing on `(1, ∞)`. -/
theorem cosh_ratio_mono {x y z : ℝ} (hx : 0 < x) (hy : 1 < y) (hyz : y ≤ z) :
    (Real.cosh (y * x) - Real.cosh x) / (y ^ 2 - 1) ≤
      (Real.cosh (z * x) - Real.cosh x) / (z ^ 2 - 1) := by
  rw [cosh_ratio_repr hx hy, cosh_ratio_repr hx (hy.trans_le hyz)]
  have hA : 0 < (y + 1) * x / 2 := div_pos (mul_pos (by linarith) hx) two_pos
  have hB : 0 < (y - 1) * x / 2 := div_pos (mul_pos (by linarith) hx) two_pos
  have hA' : (y + 1) * x / 2 ≤ (z + 1) * x / 2 := by nlinarith
  have hB' : (y - 1) * x / 2 ≤ (z - 1) * x / 2 := by nlinarith
  have m1 := strictMonoOn_sinh_div.monotoneOn (show _ ∈ Ioi (0 : ℝ) from hA)
    (show _ ∈ Ioi (0 : ℝ) from hA.trans_le hA') hA'
  have m2 := strictMonoOn_sinh_div.monotoneOn (show _ ∈ Ioi (0 : ℝ) from hB)
    (show _ ∈ Ioi (0 : ℝ) from hB.trans_le hB') hB'
  have p1 := sinhDiv_pos hA
  have p2 := sinhDiv_pos hB
  exact mul_le_mul_of_nonneg_left (mul_le_mul m1 m2 p2.le (p1.trans_le m1).le) (by positivity)

/-- **The inequality**: `(sinh x/sinh qx)(cosh qx - cosh x)/(cosh Mx - cosh x) <
(q² - 1)/(q(M² - 1))` for `1 < q ≤ M`, `x > 0`. -/
theorem later_ineq {q x M : ℝ} (hq : 1 < q) (hqM : q ≤ M) (hx : 0 < x) :
    Real.sinh x / Real.sinh (q * x) *
        ((Real.cosh (q * x) - Real.cosh x) / (Real.cosh (M * x) - Real.cosh x)) <
      (q ^ 2 - 1) / (q * (M ^ 2 - 1)) := by
  have hS1 : 0 < Real.sinh (q * x) := Real.sinh_pos_iff.2 (by nlinarith)
  have hqs := q_sinh_lt hq hx
  have hM : 1 < M := hq.trans_le hqM
  have hC1 : Real.cosh x < Real.cosh (q * x) := Real.cosh_lt_cosh.2 (by
    rw [abs_of_pos hx, abs_of_pos (by nlinarith)]; nlinarith)
  have hCM : Real.cosh x < Real.cosh (M * x) := Real.cosh_lt_cosh.2 (by
    rw [abs_of_pos hx, abs_of_pos (by nlinarith)]; nlinarith)
  have hmono := cosh_ratio_mono hx hq hqM
  have hq2 : 0 < q ^ 2 - 1 := by nlinarith
  have hM2 : 0 < M ^ 2 - 1 := by nlinarith
  have hX : (Real.cosh (q * x) - Real.cosh x) / (Real.cosh (M * x) - Real.cosh x) ≤
      (q ^ 2 - 1) / (M ^ 2 - 1) := by
    rw [div_le_div_iff₀ (by linarith) hM2]
    rw [div_le_div_iff₀ hq2 hM2] at hmono
    linarith
  have hX0 : 0 < (Real.cosh (q * x) - Real.cosh x) / (Real.cosh (M * x) - Real.cosh x) :=
    div_pos (by linarith) (by linarith)
  have hr : Real.sinh x / Real.sinh (q * x) < 1 / q := by
    rw [div_lt_div_iff₀ hS1 (by linarith)]
    linarith
  calc _ < 1 / q * ((Real.cosh (q * x) - Real.cosh x) / (Real.cosh (M * x) - Real.cosh x)) :=
        mul_lt_mul_of_pos_right hr hX0
    _ ≤ 1 / q * ((q ^ 2 - 1) / (M ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = _ := by
        have : q ≠ 0 := by linarith
        field_simp

theorem geomSig_exp_neg (y : ℝ) :
    geomSig (Real.exp (-y)) = 1 / (2 * (Real.cosh y - 1)) := by
  set β := Real.exp (-y) with hβ
  have hb0 : 0 < β := Real.exp_pos _
  have hc : 2 * (Real.cosh y - 1) = (1 - β) ^ 2 / β := by
    rw [Real.cosh_eq, show Real.exp y = β⁻¹ by rw [hβ, Real.exp_neg, inv_inv]]
    field_simp
    ring
  rw [hc, geomSig, one_div_div]

theorem geomN_exp_neg {y : ℝ} (hy : 0 < y) :
    geomN (Real.exp (-y)) = (Real.cosh y - 1) / Real.sinh y := by
  set β := Real.exp (-y) with hβ
  have hb0 : 0 < β := Real.exp_pos _
  have hb1 : β < 1 := by rw [hβ, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hc : Real.cosh y - 1 = (1 - β) ^ 2 / (2 * β) := by
    rw [Real.cosh_eq, show Real.exp y = β⁻¹ by rw [hβ, Real.exp_neg, inv_inv]]
    field_simp
    ring
  have hs : Real.sinh y = (1 - β) * (1 + β) / (2 * β) := by
    rw [Real.sinh_eq, show Real.exp y = β⁻¹ by rw [hβ, Real.exp_neg, inv_inv]]
    field_simp
    ring
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have h2 : (1 : ℝ) + β ≠ 0 := by linarith
  rw [hc, hs, geomN]
  field_simp

/-- **The ratio of the two last coefficients of the computed level**, in hyperbolic form. -/
theorem later_ratio_eq {x q M : ℝ} (hx : 0 < x) (hq : 1 < q) (hqM : q ≤ M) :
    geomN (Real.exp (-x)) * (-geomSig (Real.exp (-(M * x))) /
        (geomSig (Real.exp (-x)) - geomSig (Real.exp (-(M * x))))) /
      (geomN (Real.exp (-x)) * (geomSig (Real.exp (-x)) /
        (geomSig (Real.exp (-x)) - geomSig (Real.exp (-(q * x))))) * geomN (Real.exp (-x)) /
          geomN (Real.exp (-(q * x)))) =
    -(Real.sinh x / Real.sinh (q * x) *
      ((Real.cosh (q * x) - Real.cosh x) / (Real.cosh (M * x) - Real.cosh x))) := by
  have hqx : 0 < q * x := by nlinarith
  have hMx : 0 < M * x := by nlinarith
  rw [geomN_exp_neg hx, geomN_exp_neg hqx, geomSig_exp_neg, geomSig_exp_neg,
    geomSig_exp_neg]
  have hC0 : 1 < Real.cosh x := Real.one_lt_cosh.2 hx.ne'
  have hC1 : 1 < Real.cosh (q * x) := Real.one_lt_cosh.2 hqx.ne'
  have hCM : 1 < Real.cosh (M * x) := Real.one_lt_cosh.2 hMx.ne'
  have hS0 : 0 < Real.sinh x := Real.sinh_pos_iff.2 hx
  have hS1 : 0 < Real.sinh (q * x) := Real.sinh_pos_iff.2 hqx
  have hd1 : Real.cosh x < Real.cosh (q * x) := Real.cosh_lt_cosh.2 (by
    rw [abs_of_pos hx, abs_of_pos hqx]; nlinarith)
  have hdM : Real.cosh x < Real.cosh (M * x) := Real.cosh_lt_cosh.2 (by
    rw [abs_of_pos hx, abs_of_pos hMx]; nlinarith)
  generalize Real.cosh x = C0 at *
  generalize Real.cosh (q * x) = C1 at *
  generalize Real.cosh (M * x) = CM at *
  generalize Real.sinh x = S0 at *
  generalize Real.sinh (q * x) = S1 at *
  have h0 : C0 - 1 ≠ 0 := by linarith
  have h1 : C1 - 1 ≠ 0 := by linarith
  have h2 : CM - 1 ≠ 0 := by linarith
  have h3 : C1 - C0 ≠ 0 := by linarith
  have h4 : CM - C0 ≠ 0 := by linarith
  have e1 : 1 / (2 * (C0 - 1)) - 1 / (2 * (C1 - 1)) = (C1 - C0) / (2 * (C0 - 1) * (C1 - 1)) := by
    rw [div_sub_div _ _ (by positivity) (by positivity),
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have eM : 1 / (2 * (C0 - 1)) - 1 / (2 * (CM - 1)) = (CM - C0) / (2 * (C0 - 1) * (CM - 1)) := by
    rw [div_sub_div _ _ (by positivity) (by positivity),
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [e1, eM]
  have h5 : S0 ≠ 0 := hS0.ne'
  have h6 : S1 ≠ 0 := hS1.ne'
  field_simp

/-! ## The comparison -/

/-- `ρᵢ = e^{-q^{i+1}x}`, `x = h/(ct)`. -/
theorem lvRho_eq {h c t : ℝ} {q : ℕ} (hc : 0 < c) (ht : 0 < t) (i : ℕ) :
    lvRho h c t q i = Real.exp (-((q : ℝ) ^ (i + 1) * (h / (c * t)))) := by
  rw [lvRho, slRatio_of_pos (mul_pos hc ht), ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The samples of the Laplace density of range `ctq^k` on `q^n hℤ`, `k < n`. -/
theorem laplace_sample {h c t : ℝ} {q : ℕ} (hh : 0 < h) (hq : 2 ≤ q) (hc : 0 < c) (ht : 0 < t)
    {n k : ℕ} (hk : k < n) (m : ℤ) :
    laplaceDensity (c * t * (q : ℝ) ^ k) ((q : ℝ) ^ n * h * m) =
      (2 * (c * t * (q : ℝ) ^ k))⁻¹ * lvRho h c t q (n - 1 - k) ^ m.natAbs := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqk : 0 < (q : ℝ) ^ k := pow_pos hq0 k
  have hqn : (q : ℝ) ^ n = (q : ℝ) ^ (n - k) * (q : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk.le]
  have hex : -(|(q : ℝ) ^ n * h * m| / (c * t * (q : ℝ) ^ k)) =
      (m.natAbs : ℝ) * -((q : ℝ) ^ (n - 1 - k + 1) * (h / (c * t))) := by
    rw [show n - 1 - k + 1 = n - k by omega, abs_mul, abs_mul, abs_of_pos (pow_pos hq0 n),
      abs_of_pos hh, hqn, Nat.cast_natAbs, Int.cast_abs]
    field_simp
  rw [lvRho_eq hc ht, ← Real.exp_nat_mul, ScaleSpace.laplaceDensity, hex]

/-- **`prop:sampled-laplace-exact`(2), not from the second level**: `U_n ≠ V_n` for every
`n ≥ 2` and every `h, c, t > 0`. -/
theorem sampled_laplace_exact_2_later {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : 2 ≤ n) {h c t : ℝ}
    (hh : 0 < h) (hc : 0 < c) (ht : 0 < t) :
    ¬ ∃ κ : ℝ, ∀ m : ℤ, pyramidLevels (slKernel h (c * t)) q n m =
      κ * laplaceChainDensity (fun k => c * t * (q : ℝ) ^ k) (n - 1) ((q : ℝ) ^ n * h * m) := by
  rintro ⟨κ, hκ⟩
  have hct : 0 < c * t := mul_pos hc ht
  have hQ : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨b, hb, hb1, hb2⟩ := pyramidLevels_expand hh hq hc ht (by omega : 1 ≤ n)
  obtain ⟨A, hA, hA0, hA1⟩ := chain_expand hct hQ (n - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hA
  set σ : ℕ → ℝ := fun i => A (n - 1 - i) * (2 * (c * t * (q : ℝ) ^ (n - 1 - i)))⁻¹ with hσ
  have hV : ∀ m : ℤ, laplaceChainDensity (fun k => c * t * (q : ℝ) ^ k) (n - 1)
      ((q : ℝ) ^ n * h * m) = ∑ i ∈ Finset.range n, σ i * lvRho h c t q i ^ m.natAbs := by
    intro m
    rw [hA, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [laplace_sample hh hq hc ht (by omega : n - 1 - i < n),
      show n - 1 - (n - 1 - i) = i by omega, hσ]
    ring
  have ha0 := slRatio_pos (h := h) hct
  have ha1 := slRatio_lt_one hh (c * t)
  have hdist : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, i ≠ j →
      lvRho h c t q i ≠ lvRho h c t q j := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hl | hl
    · exact (pow_lt_pow_right_of_lt_one₀ ha0 ha1
        (Nat.pow_lt_pow_right (by omega) (by omega : i + 1 < j + 1))).ne'
    · exact (pow_lt_pow_right_of_lt_one₀ ha0 ha1
        (Nat.pow_lt_pow_right (by omega) (by omega : j + 1 < i + 1))).ne
  have hzero := geom_indep (Finset.range n) hdist (fun i => b i - κ * σ i) fun m => by
    have h1 := hκ (m : ℤ)
    rw [hb, hV, Int.natAbs_natCast, Finset.mul_sum] at h1
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, h1, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e1 := hzero (n - 1) (Finset.mem_range.2 (by omega))
  have e2 := hzero (n - 2) (Finset.mem_range.2 (by omega))
  rw [sub_eq_zero] at e1 e2
  -- the two coefficients of the computed level
  set P := ∏ i ∈ Finset.range (n - 2), lvB h c t q i with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => lvB_ne_zero hh hq hc ht i
  have hb1' : b (n - 1) = geomN (slRatio h (c * t)) * (P * lvB h c t q (n - 2)) := by
    rw [hb1, show n - 1 = n - 2 + 1 by omega, Finset.prod_range_succ]
  set B2 := geomN (slRatio h (c * t)) * lvA h c t q 0 * geomN (slRatio h (c * t)) /
    geomN (lvRho h c t q 0) with hB2
  have hNa := geomN_pos ha0.le ha1
  have hBn := lvB_ne_zero hh hq hc ht (n - 2)
  have hbn0 : b (n - 1) ≠ 0 := by
    rw [hb1']; exact mul_ne_zero hNa.ne' (mul_ne_zero hP0 hBn)
  have hb2' : b (n - 2) = B2 * P := hb2 hn
  have hB20 : B2 ≠ 0 := by
    intro h0
    have : b (n - 2) = 0 := by rw [hb2', h0, zero_mul]
    have hκ0 : κ ≠ 0 := by
      intro hk0; rw [hk0, zero_mul] at e1; exact hbn0 e1
    rw [e2] at this
    -- `σ(n-2) = A_1/(2ctq) ≠ 0`
    have hA1' := hA1 (by omega)
    have hσ2 : σ (n - 2) ≠ 0 := by
      simp only [hσ, show n - 1 - (n - 2) = 1 by omega]
      rw [hA1']
      have hQ2 : (q : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      have hprod : ∏ j ∈ Finset.range (n - 1 - 1), (1 - ((q : ℝ) ^ 2) ^ (j + 1)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ => by
          have := one_lt_pow₀ (by nlinarith : (1 : ℝ) < (q : ℝ) ^ 2) (by omega : j + 1 ≠ 0)
          linarith
      positivity
    exact mul_ne_zero hκ0 hσ2 this
  -- the ratio of the computed level
  have hR1 : b (n - 1) / b (n - 2) = geomN (slRatio h (c * t)) * lvB h c t q (n - 2) / B2 := by
    rw [hb1', hb2']
    field_simp
  -- the ratio of the sampled step
  set M : ℝ := (q : ℝ) ^ (n - 1) with hM
  have hqM : (q : ℝ) ≤ M := le_self_pow₀ hQ.le (by omega)
  have hM1 : 1 < M := hQ.trans_le hqM
  have hR2 : b (n - 1) / b (n - 2) = -((q ^ 2 - 1) / (q * (M ^ 2 - 1))) := by
    rw [e1, e2]
    have hκ0 : κ ≠ 0 := by
      intro hk0; rw [hk0, zero_mul] at e1; exact hbn0 e1
    simp only [hσ, show n - 1 - (n - 1) = 0 by omega, show n - 1 - (n - 2) = 1 by omega,
      pow_zero, pow_one, mul_one]
    rw [hA0, hA1 (by omega), show n - 1 = n - 1 - 1 + 1 by omega, Finset.prod_range_succ,
      show n - 1 - 1 + 1 = n - 1 by omega]
    have hMsq : ((q : ℝ) ^ 2) ^ (n - 1) = M ^ 2 := by
      rw [hM, ← pow_mul, ← pow_mul, mul_comm]
    rw [hMsq]
    have hprod : ∏ j ∈ Finset.range (n - 1 - 1), (1 - ((q : ℝ) ^ 2) ^ (j + 1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => by
        have := one_lt_pow₀ (by nlinarith : (1 : ℝ) < (q : ℝ) ^ 2) (by omega : j + 1 ≠ 0)
        linarith
    have hQ2 : (q : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have hM2 : 1 - M ^ 2 ≠ 0 := by nlinarith
    have hM2' : M ^ 2 - 1 ≠ 0 := by nlinarith
    have hq0' : (q : ℝ) ≠ 0 := hq0.ne'
    have hct' : c * t ≠ 0 := hct.ne'
    field_simp
    ring
  -- the hyperbolic form
  set x := h / (c * t) with hx
  have hx0 : 0 < x := div_pos hh hct
  have hR3 : geomN (slRatio h (c * t)) * lvB h c t q (n - 2) / B2 =
      -(Real.sinh x / Real.sinh (q * x) *
        ((Real.cosh (q * x) - Real.cosh x) / (Real.cosh (M * x) - Real.cosh x))) := by
    have ha : slRatio h (c * t) = Real.exp (-x) := by
      rw [slRatio_of_pos hct, hx, neg_div]
    have hr0 : lvRho h c t q 0 = Real.exp (-((q : ℝ) * x)) := by
      rw [lvRho_eq hc ht, zero_add, pow_one]
    have hrM : lvRho h c t q (n - 2) = Real.exp (-(M * x)) := by
      rw [lvRho_eq hc ht, show n - 2 + 1 = n - 1 by omega]
    rw [hB2, lvB, lvA, ha, hr0, hrM]
    exact later_ratio_eq hx0 hQ hqM
  have hfin := later_ineq hQ hqM hx0
  have hEq := hR2.symm.trans (hR1.trans hR3)
  linarith

end Pyramids
