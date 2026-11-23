/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Price.GridKnot
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# `prop:grid-pyramid-singular-kernels`: the kernels of an exact grid pyramid have no density

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:grid-pyramid-singular-kernels` (review round 3,
batch C, s4-5.R2). Clauses (1) and (2) are proved here; clause (3), that every kernel is singular,
is proved in print only, and its statement is typed in `PyramidsSkeleton.Ch05Price`.

## The route

* **A point of the dual.** A law carried by `Γ` has transform `1` at every `ξ` with
  `⟪γ, ξ⟫ ∈ 2πℤ` for `γ ∈ Γ`. For an integer `q` the multiples `q^k ξ` are such points too.
* **The knot kernel at `q^k ξ`.** The step `μ̂_1(qω) = ŵ(ω) μ̂_1(ω)` of a carrying family
  (`CarriesLatticeLadder.step`) gives `μ̂_1(q^{k+1} ξ) = μ̂_1(q^k ξ)`, so `μ̂_1(q^k ξ) = μ̂_1(ξ)`;
  the value is not `0`, as `μ_1` is infinitely divisible (A41) and its transform has no zero (A40).
* **Every kernel.** For `t ≤ q^n`, `μ̂_{q^n} = μ̂_{t,q^n} μ̂_t` and `|μ̂_{t,q^n}| ≤ 1`, so
  `|μ̂_t(q^{k-n} ξ)| ≥ |μ̂_1(ξ)| > 0` along a sequence tending to infinity. By the Riemann–Lebesgue
  lemma (Mathlib's `tendsto_integral_exp_inner_smul_cocompact`, read through the Radon–Nikodym
  derivative), the transform of an absolutely continuous law tends to `0`: `μ_t` is not absolutely
  continuous.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter Complex
open scoped Topology ENNReal RealInnerProductSpace Real FourierTransform

variable {d : ℕ}

/-! ## The Riemann–Lebesgue lemma for laws -/

/-- **The transform of an absolutely continuous finite measure tends to `0` at infinity**: the
Riemann–Lebesgue lemma, read through the Radon–Nikodym derivative. -/
theorem tendsto_charFun_cocompact_of_ac {m : Measure (Rd d)} [IsFiniteMeasure m]
    (hac : m ≪ volume) : Tendsto (charFun m) (cocompact (Rd d)) (𝓝 0) := by
  set f : Rd d → ℂ := fun x => ((m.rnDeriv volume x).toReal : ℂ) with hf
  have hRL := tendsto_integral_exp_inner_smul_cocompact f
  have hc : (-(2 * π)⁻¹ : ℝ) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact neg_ne_zero.2 (inv_ne_zero this.ne')
  have hmap : Tendsto (fun ω : Rd d => (-(2 * π)⁻¹ : ℝ) • ω) (cocompact (Rd d))
      (cocompact (Rd d)) :=
    (Homeomorph.smulOfNeZero _ hc).toCocompactMap.cocompact_tendsto'
  have heq : ∀ ω : Rd d, charFun m ω =
      ∫ v, 𝐞 (-⟪v, (-(2 * π)⁻¹ : ℝ) • ω⟫) • f v := by
    intro ω
    rw [charFun_apply, ← integral_rnDeriv_smul hac]
    congr 1
    funext v
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    have hexp : Complex.exp (((2 * π * -⟪v, (-(2 * π)⁻¹ : ℝ) • ω⟫ : ℝ) : ℂ) * I) =
        Complex.exp ((⟪v, ω⟫ : ℂ) * I) := by
      congr 2
      rw [inner_smul_right]
      field_simp
    rw [Circle.smul_def, Real.fourierChar_apply, hexp, hf, Complex.real_smul, smul_eq_mul,
      mul_comm]
  exact (hRL.comp hmap).congr fun ω => (heq ω).symm

/-- **A law whose transform stays away from `0` along a sequence tending to infinity is not
absolutely continuous.** -/
theorem not_ac_of_norm_charFun_ge {m : Measure (Rd d)} [IsFiniteMeasure m] {ξ : ℕ → Rd d}
    (hξ : Tendsto (fun k => ‖ξ k‖) atTop atTop) {c : ℝ} (hc : 0 < c)
    (hm : ∀ k, c ≤ ‖charFun m (ξ k)‖) : ¬ m ≪ volume := by
  intro hac
  have hcoc : Tendsto ξ atTop (cocompact (Rd d)) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    exact hξ
  have h0 := ((tendsto_charFun_cocompact_of_ac hac).comp hcoc).norm
  rw [norm_zero] at h0
  obtain ⟨k, hk⟩ := (h0.eventually (gt_mem_nhds hc)).exists
  exact absurd (hm k) (not_le.2 hk)

/-! ## The transform at the points of the dual lattice -/

/-- **A law carried by `Γ` has transform `1` at a point of the dual of `Γ`**, a point `ξ` with
`⟪γ, ξ⟫ ∈ 2πℤ` for every `γ ∈ Γ`. -/
theorem charFun_eq_one_of_mem_dual {Γ : Set (Rd d)} {w : Measure (Rd d)}
    [IsProbabilityMeasure w] (hΓ : w Γᶜ = 0) {ξ : Rd d}
    (hξ : ∀ γ ∈ Γ, ∃ n : ℤ, ⟪γ, ξ⟫ = 2 * π * n) : charFun w ξ = 1 := by
  rw [charFun_apply]
  have hae : (fun x : Rd d => Complex.exp (⟪x, ξ⟫ * I)) =ᵐ[w] fun _ => 1 := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hΓ
    rw [mem_setOf_eq] at hx
    rw [mem_compl_iff]
    intro hxΓ
    apply hx
    obtain ⟨n, hn⟩ := hξ x hxΓ
    rw [hn]
    push_cast
    rw [show (2 * π * n : ℂ) * I = n * (2 * π * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [integral_congr_ae hae]
  simp

/-- **The transform of the knot kernel takes one value along `q^k ξ`**, for `ξ` in the dual of
the lattice that carries the mask and an integer ratio `q`. -/
theorem CarriesLatticeLadder.charFun_dual_pow {q : ℕ} {Γ : Set (Rd d)} {w : Measure (Rd d)}
    [IsProbabilityMeasure w] (hΓ : w Γᶜ = 0) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder (q : ℝ) w μ) {ξ : Rd d}
    (hξ : ∀ γ ∈ Γ, ∃ n : ℤ, ⟪γ, ξ⟫ = 2 * π * n) (k : ℕ) :
    charFun (μ 0 1) (((q : ℝ) ^ k) • ξ) = charFun (μ 0 1) ξ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hdual : ∀ γ ∈ Γ, ∃ n : ℤ, ⟪γ, ((q : ℝ) ^ k) • ξ⟫ = 2 * π * n := fun γ hγ => by
      obtain ⟨n, hn⟩ := hξ γ hγ
      exact ⟨(q : ℤ) ^ k * n, by rw [inner_smul_right, hn]; push_cast; ring⟩
    rw [pow_succ', mul_smul, ← hμ.step, charFun_eq_one_of_mem_dual hΓ hdual, one_mul, ih]

/-- **The transform of the knot kernel has no zero** (A40, with A41 through
`isLawHemigroup_infinitelyDivisible`). -/
theorem CarriesLatticeLadder.charFun_one_ne_zero (hd : 1 ≤ d) {q : ℝ} {w : Measure (Rd d)}
    {μ : ℝ → ℝ → Measure (Rd d)} (hμ : CarriesLatticeLadder q w μ) (ω : Rd d) :
    charFun (μ 0 1) ω ≠ 0 := by
  haveI := hμ.prob le_rfl zero_le_one
  exact cited_A40 _ (isLawHemigroup_infinitelyDivisible hd hμ.2.1 0 1 le_rfl zero_le_one) ω

/-- **No kernel of a family carrying the ladder is absolutely continuous**, for an integer ratio and
a mask carried by a set `Γ` whose dual has a point `ξ ≠ 0`. -/
theorem CarriesLatticeLadder.kernel_not_ac (hd : 1 ≤ d) {q : ℕ} {Γ : Set (Rd d)}
    {w : Measure (Rd d)} [IsProbabilityMeasure w] (hΓ : w Γᶜ = 0) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder (q : ℝ) w μ) {ξ : Rd d} (hξ0 : ξ ≠ 0)
    (hξ : ∀ γ ∈ Γ, ∃ n : ℤ, ⟪γ, ξ⟫ = 2 * π * n) {t : ℝ} (ht : 0 < t) :
    ¬ μ 0 t ≪ volume := by
  have hq : (1 : ℝ) < q := hμ.1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, t ≤ (q : ℝ) ^ n :=
    (pow_unbounded_of_one_lt t hq).imp fun _ h => h.le
  haveI := hμ.prob le_rfl ht.le
  haveI := hμ.prob ht.le hn
  have hc : 0 < ‖charFun (μ 0 1) ξ‖ := norm_pos_iff.2 (hμ.charFun_one_ne_zero hd ξ)
  refine not_ac_of_norm_charFun_ge (ξ := fun k => ((q : ℝ) ^ k) • ξ) ?_ hc fun k => ?_
  · have hq0 : (0 : ℝ) ≤ q := by linarith
    simp_rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hq0]
    exact (tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const (norm_pos_iff.2 hξ0)
  · have hmul := charFun_kernel_mul_gen hμ.2.1 ht.le hn (((q : ℝ) ^ k) • ξ)
    have hknot : charFun (μ 0 ((q : ℝ) ^ n)) (((q : ℝ) ^ k) • ξ) = charFun (μ 0 1) ξ := by
      have hz := hμ.zpow (n : ℤ)
      rw [zpow_natCast] at hz
      rw [hz, charFun_map_smul, smul_smul, ← pow_add, hμ.charFun_dual_pow hΓ hξ]
    calc ‖charFun (μ 0 1) ξ‖
        = ‖charFun (μ t ((q : ℝ) ^ n)) (((q : ℝ) ^ k) • ξ)‖ *
            ‖charFun (μ 0 t) (((q : ℝ) ^ k) • ξ)‖ := by rw [← hknot, hmul, norm_mul]
      _ ≤ 1 * ‖charFun (μ 0 t) (((q : ℝ) ^ k) • ξ)‖ := by
          gcongr
          exact norm_charFun_le_one _
      _ = ‖charFun (μ 0 t) (((q : ℝ) ^ k) • ξ)‖ := one_mul _

/-! ## `prop:grid-pyramid-singular-kernels`, clauses (1) and (2), on `hℤ^d` -/

/-- The point `(2π/h) e_i` is in the dual of `hℤ^d`. -/
theorem mem_dual_gridSet {h : ℝ} (hh : h ≠ 0) (i : Fin d) :
    ∀ γ ∈ gridSet d h, ∃ n : ℤ, ⟪γ, (2 * π / h) • ebasis i⟫ = 2 * π * n := by
  rintro γ ⟨n, rfl⟩
  refine ⟨n i, ?_⟩
  rw [inner_smul_right, latticePt, inner_smul_left, ebasis, EuclideanSpace.inner_single_right]
  simp only [one_mul, RCLike.conj_to_real]
  field_simp

/-- **`prop:grid-pyramid-singular-kernels`(1).** For an integer ratio `q` and an exact grid pyramid
on `hℤ^d`, the transform of the knot kernel takes one value, other than `0`, at every
`2π q^k e_i / h`, `k ≥ 0`. -/
theorem grid_pyramid_singular_kernels_1 {q : ℕ} {h : ℝ} (hh : 0 < h) {w : Measure (Rd d)}
    (hw : IsLatticeMask (gridSet d h) w) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder (q : ℝ) w μ) (i : Fin d) :
    (∀ k : ℕ, charFun (μ 0 1) (((q : ℝ) ^ k * (2 * π / h)) • ebasis i) =
      charFun (μ 0 1) ((2 * π / h) • ebasis i)) ∧
      charFun (μ 0 1) ((2 * π / h) • ebasis i) ≠ 0 := by
  haveI := hw.1
  have hd : 1 ≤ d := one_le_of_ne_dirac hw.2.2.1
  refine ⟨fun k => ?_, hμ.charFun_one_ne_zero hd _⟩
  rw [mul_smul]
  exact hμ.charFun_dual_pow hw.2.2.2 (mem_dual_gridSet hh.ne' i) k

/-- **`prop:grid-pyramid-singular-kernels`(2).** For an integer ratio `q` and an exact grid pyramid
on `hℤ^d`, no kernel `μ_t`, `t > 0`, of a carrying family is absolutely continuous. -/
theorem grid_pyramid_singular_kernels_2 {q : ℕ} {h : ℝ} (hh : 0 < h) {w : Measure (Rd d)}
    (hw : IsLatticeMask (gridSet d h) w) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder (q : ℝ) w μ) {t : ℝ} (ht : 0 < t) : ¬ μ 0 t ≪ volume := by
  haveI := hw.1
  have hd : 1 ≤ d := one_le_of_ne_dirac hw.2.2.1
  set i : Fin d := ⟨0, hd⟩
  have hξ0 : (2 * π / h) • ebasis i ≠ 0 := by
    refine smul_ne_zero (by positivity) ?_
    intro h0
    have := congrArg (fun x : Rd d => x i) h0
    simp [ebasis] at this
  exact hμ.kernel_not_ac hd hw.2.2.2 hξ0 (mem_dual_gridSet hh.ne' i) ht

end Pyramids
