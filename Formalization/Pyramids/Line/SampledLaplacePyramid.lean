/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.SampledLaplace

/-!
# `prop:sampled-laplace-exact`(2): the sampled Matérn pyramid on the grids

Blueprint: `blueprint/src/parts/02-line.tex`, `prop:sampled-laplace-exact`. Wave 3f: the
declarations `sampled_laplace_exact_2_array`, `_2_restriction`, `_2_first` and `_2_later` moved
here from `PyramidsSkeleton.Ch02Line`; `_2_array` and `_2_first` drop one hypothesis each that
their proofs do not read (2026-11-15, a strengthening), the others are unchanged.

* **The restriction**: the sampled factor `F_k` vanishes off `q^kℤ` and is `c_k g` on it, so
  `(G_n * F_n)(q^{n+1}m) = c_n ∑_j g(j) G_n(q^n(qm - j))`, and `u_n(m) = κ_n G_n(q^nm)` by
  induction; the fold is `G_n * F_n` by associativity.
* **The computed level** is `u_n(m) = ∑_{i<n} bᵢ ρᵢ^{|m|}`, `ρᵢ = a^{q^{i+1}}`, from
  `g_β * g_{β'} = (ς_β g_β - ς_{β'} g_{β'})/(ς_β - ς_{β'})` (by transfers) and
  `g_β(qm) = N_β (β^q)^{|m|}`; only the two last coefficients are computed.
* **The sampled step** is `∑_k A_k L_{r_k}` by `L_r * L_s = (r²L_r - s²L_s)/(r² - s²)`, computed
  as three exponential integrals; again only `A_0` and `A_1` are computed.
* **The comparison**: geometric sequences with distinct ratios are linearly independent, so
  `U_n = V_n` would give `b_{n-1}/b_{n-2} = σ_{n-1}/σ_{n-2}`; in hyperbolic form the first is
  `-(sinh x/sinh qx)(cosh qx - cosh x)/(cosh Mx - cosh x)`, `M = q^{n-1}`, and the second
  `-(q² - 1)/(q(M² - 1))`, and `u ↦ sinh u/u` strictly increasing separates them.
-/

namespace Pyramids

open MeasureTheory Set Filter
open ScaleSpace (laplaceDensity)
open scoped Topology Real

/-! ## (2): the same array, the first level -/

/-- **`prop:sampled-laplace-exact`(2), the same array.** In grid units the kernel of range `ctq^k`
on `q^k hℤ` is `g = λ_{ct}` at every `k ≥ 0`. -/
theorem sampled_laplace_exact_2_array {h : ℝ} {q : ℕ} (hq : 2 ≤ q) {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) (k : ℕ) :
    slKernel ((q : ℝ) ^ k * h) (c * t * (q : ℝ) ^ k) = slKernel h (c * t) := by
  have hqk : 0 < (q : ℝ) ^ k := pow_pos (by exact_mod_cast (by omega : 0 < q)) k
  rw [slKernel, slKernel, slRatio_of_pos (by positivity), slRatio_of_pos (by positivity),
    show -((q : ℝ) ^ k * h) / (c * t * (q : ℝ) ^ k) = -h / (c * t) by field_simp]

/-- `u_1(m) = g(qm)`. -/
theorem pyramidLevels_one (g : ℤ → ℝ) (q : ℕ) (m : ℤ) : pyramidLevels g q 1 m = g (q * m) := by
  simp only [pyramidLevels, zconv_zdelta_right]

/-- **`prop:sampled-laplace-exact`(2), exact at the first level**: `U_1 = V_1`. -/
theorem sampled_laplace_exact_2_first {h : ℝ} (hh : 0 < h) {q : ℕ} {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ m : ℤ,
      pyramidLevels (slKernel h (c * t)) q 1 m = κ * laplaceDensity (c * t) (q * h * m) := by
  have hct : 0 < c * t := mul_pos hc ht
  set a := slRatio h (c * t) with ha
  have ha1 : a < 1 := slRatio_lt_one hh _
  have ha0 : 0 < a := slRatio_pos hct
  refine ⟨2 * (c * t) * ((1 - a) / (1 + a)), by
    have : 0 < 1 - a := by linarith
    positivity, fun m => ?_⟩
  rw [pyramidLevels_one, slKernel, geomKernel, ScaleSpace.laplaceDensity,
    show (q : ℝ) * h * m = (((q : ℤ) * m : ℤ) : ℝ) * h by push_cast; ring,
    exp_neg_abs_int_mul hh.le, ← slRatio_of_pos hct, ← ha]
  field_simp

/-! ## (2): the restriction -/

section Restriction

variable {h c t : ℝ} {q : ℕ}

theorem laplaceDensity_int_mul {r : ℝ} (hh : 0 < h) (i : ℤ) :
    laplaceDensity r (i * h) = (2 * r)⁻¹ * Real.exp (-h / r) ^ i.natAbs := by
  rw [ScaleSpace.laplaceDensity, exp_neg_abs_int_mul hh.le]

theorem summable_sampledLaplaceFactor (hh : 0 < h) (hc : 0 < c) (ht : 0 < t) (hq : 2 ≤ q)
    (k : ℕ) : Summable (sampledLaplaceFactor h c t q k) := by
  have hqk : 0 < (q : ℝ) ^ k := pow_pos (by exact_mod_cast (by omega : 0 < q)) k
  have hr : 0 < c * t * (q : ℝ) ^ k := by positivity
  set b := Real.exp (-h / (c * t * (q : ℝ) ^ k)) with hb
  have hb1 : b < 1 := gridA_lt_one hh hr
  refine Summable.of_norm_bounded ((summable_pow_natAbs_of_nonneg (Real.exp_pos _).le hb1).mul_left
    (2 * (c * t * (q : ℝ) ^ k))⁻¹) fun i => ?_
  unfold sampledLaplaceFactor
  split_ifs
  · rw [laplaceDensity_int_mul hh, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · rw [norm_zero]; positivity

/-- `F_k(q^k j) = (q^k)⁻¹ (2ct)⁻¹ a^{|j|}`, `a = e^{-h/(ct)}`. -/
theorem sampledLaplaceFactor_mul (hh : 0 < h) (hc : 0 < c) (ht : 0 < t) (hq : 2 ≤ q) (k : ℕ)
    (j : ℤ) : sampledLaplaceFactor h c t q k ((q : ℤ) ^ k * j) =
      ((q : ℝ) ^ k)⁻¹ * ((2 * (c * t))⁻¹ * slRatio h (c * t) ^ j.natAbs) := by
  have hqk : 0 < (q : ℝ) ^ k := pow_pos (by exact_mod_cast (by omega : 0 < q)) k
  have hct : 0 < c * t := mul_pos hc ht
  rw [sampledLaplaceFactor, if_pos (dvd_mul_right _ _), ScaleSpace.laplaceDensity,
    slRatio_of_pos hct, ← exp_neg_abs_int_mul hh.le]
  push_cast
  rw [show |(q : ℝ) ^ k * j * h| = (q : ℝ) ^ k * |j * h| by
    rw [mul_assoc, abs_mul, abs_of_pos hqk]]
  field_simp

theorem sampledLaplaceFactor_of_not_dvd {k : ℕ} {i : ℤ} (hi : ¬ (q : ℤ) ^ k ∣ i) :
    sampledLaplaceFactor h c t q k i = 0 := by
  rw [sampledLaplaceFactor, if_neg hi]

/-- The fold `F_0 * (F_1 * ⋯ * (F_{n-1} * Y))` is `(F_0 * ⋯ * F_{n-1}) * Y`. -/
theorem foldr_zconv {G : ℕ → ℤ → ℝ} (hG : ∀ k, Summable (G k)) (l : List ℕ) {Y : ℤ → ℝ}
    (hY : Summable Y) :
    Summable (l.foldr (fun k f => zconv (G k) f) zdelta) ∧
      l.foldr (fun k f => zconv (G k) f) Y =
        zconv (l.foldr (fun k f => zconv (G k) f) zdelta) Y := by
  induction l with
  | nil => exact ⟨summable_zdelta, (zconv_zdelta_left Y).symm⟩
  | cons k l ih =>
    simp only [List.foldr_cons]
    refine ⟨summable_zconv (hG k) ih.1, ?_⟩
    rw [ih.2, zconv_assoc (hG k) ih.1 hY]

theorem foldr_range_succ {G : ℕ → ℤ → ℝ} (hG : ∀ k, Summable (G k)) (n : ℕ) :
    (List.range (n + 1)).foldr (fun k f => zconv (G k) f) zdelta =
      zconv ((List.range n).foldr (fun k f => zconv (G k) f) zdelta) (G n) := by
  rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, zconv_zdelta_right]
  exact (foldr_zconv hG _ (hG n)).2

/-- **`prop:sampled-laplace-exact`(2), the restriction.** `u_n` is, up to a positive constant, the
restriction to `q^n hℤ` of the convolution of the sampled factors `L_{ctq^k}` on `q^k hℤ`,
`k < n`. -/
theorem sampled_laplace_exact_2_restriction {h : ℝ} (hh : 0 < h) {q : ℕ} (hq : 2 ≤ q) {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) (n : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ m : ℤ, pyramidLevels (slKernel h (c * t)) q n m =
      κ * ((List.range n).foldr (fun k f => zconv (sampledLaplaceFactor h c t q k) f) zdelta)
        ((q : ℤ) ^ n * m) := by
  have hF := summable_sampledLaplaceFactor hh hc ht hq
  have hct : 0 < c * t := mul_pos hc ht
  set a := slRatio h (c * t) with ha
  have ha0 : 0 < a := slRatio_pos hct
  have ha1 : a < 1 := slRatio_lt_one hh _
  set g := slKernel h (c * t) with hg
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  induction n with
  | zero =>
    refine ⟨1, one_pos, fun m => ?_⟩
    simp [pyramidLevels]
  | succ n ih =>
    obtain ⟨κ, hκ, hu⟩ := ih
    -- `c_n = (q^n)⁻¹(2ct)⁻¹(1+a)/(1-a)`, `F_n(q^n j) = c_n g(j)`
    set cn : ℝ := ((q : ℝ) ^ n)⁻¹ * (2 * (c * t))⁻¹ * ((1 + a) / (1 - a)) with hcn
    have hqn : 0 < (q : ℝ) ^ n := pow_pos (by exact_mod_cast (by omega : 0 < q)) n
    have hcn0 : 0 < cn := by
      have : 0 < 1 - a := by linarith
      positivity
    have hFg : ∀ j, sampledLaplaceFactor h c t q n ((q : ℤ) ^ n * j) = cn * g j := by
      intro j
      rw [sampledLaplaceFactor_mul hh hc ht hq, hg, slKernel, geomKernel, ← ha, hcn]
      have : (1 : ℝ) - a ≠ 0 := by linarith
      have : (1 : ℝ) + a ≠ 0 := by linarith
      field_simp
    refine ⟨κ / cn, div_pos hκ hcn0, fun m => ?_⟩
    have hinj : Function.Injective fun j : ℤ => (q : ℤ) ^ n * j :=
      fun j j' hjj => mul_left_cancel₀ (pow_ne_zero n hq0) hjj
    have hG : (List.range (n + 1)).foldr (fun k f => zconv (sampledLaplaceFactor h c t q k) f)
        zdelta ((q : ℤ) ^ (n + 1) * m) = cn * ∑' j, g j *
          (List.range n).foldr (fun k f => zconv (sampledLaplaceFactor h c t q k) f) zdelta
            ((q : ℤ) ^ n * (q * m - j)) := by
      rw [foldr_range_succ hF, zconv_comm, zconv, ← tsum_mul_left]
      rw [← hinj.tsum_eq (f := fun i => sampledLaplaceFactor h c t q n i *
        (List.range n).foldr (fun k f => zconv (sampledLaplaceFactor h c t q k) f) zdelta
          ((q : ℤ) ^ (n + 1) * m - i))]
      · congr 1
        funext j
        rw [hFg, show (q : ℤ) ^ (n + 1) * m - (q : ℤ) ^ n * j = (q : ℤ) ^ n * (q * m - j) by ring]
        ring
      · intro i hi
        by_contra hr
        apply hi
        have : ¬ (q : ℤ) ^ n ∣ i := fun ⟨j, hj⟩ => hr ⟨j, hj.symm⟩
        simp only [sampledLaplaceFactor_of_not_dvd this, zero_mul]
    rw [hG]
    have hu' : ∀ j, (List.range n).foldr (fun k f => zconv (sampledLaplaceFactor h c t q k) f)
        zdelta ((q : ℤ) ^ n * (q * m - j)) = κ⁻¹ * pyramidLevels g q n (q * m - j) := by
      intro j
      rw [hu, ← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul]
    simp_rw [hu']
    rw [show pyramidLevels g q (n + 1) m = zconv g (pyramidLevels g q n) (q * m) from rfl, zconv]
    simp_rw [← mul_assoc, mul_comm _ κ⁻¹, mul_assoc]
    rw [tsum_mul_left]
    field_simp

end Restriction

end Pyramids
