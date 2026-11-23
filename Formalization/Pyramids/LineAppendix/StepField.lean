/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.AnnulusParametrization
import Pyramids.Pyramid.DiscreteCovarianceLevy
import Pyramids.Pyramid.LatticeStrata

/-!
# `lem:step-field-determines-family`: the `q`-step field determines the family

Blueprint: `blueprint/src/parts/A1-line.tex`. Moved from `PyramidsSkeleton.ChA1Line` in wave 2f,
unchanged in statement and name.

* (1): covariance at the pairs `(0, t)` (`lineExponent_cov`) makes the series telescope,
  `∑_{m < M} g_{t,qt}(q^{-m-1}ω) = Ψ_t(ω) - Ψ_t(q^{-M}ω)`; its terms are nonnegative, the kernels'
  transforms decreasing in `t`, and the last term tends to `Ψ_t(0) = 0`.
* (2): by (1) the two families have the same `Ψ_t` on `[1, q)`, so the same kernels there; the
  kernels on `[1, q)` determine a `q`-covariant family (`lem:discrete-covariance-levy`, read in
  `ℝ¹` through `x ↦ xe₀`).
* The knots: the octave step `μ_{1,q}` has the exponent `g_{1,q}`, so (1) gives `Ψ_1`, and the
  knot kernels are the dilates `μ_{qⁿ} = D_{qⁿ}μ_1`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ComplexOrder

/-- `Ψ_t` is continuous, and `Ψ_t(0) = 0`. -/
theorem lineExponent_continuous {μ : ℝ → ℝ → Measure ℝ} (hμ : IsSymmetricFamily μ) {t : ℝ}
    (ht : 0 ≤ t) : Continuous (lineExponent μ t) := by
  have hK := kernelOrder_line hμ
  haveI := hμ.1.isProbability 0 t le_rfl ht
  unfold lineExponent
  refine (Continuous.log (Complex.continuous_re.comp continuous_charFun) fun ω => ?_).neg
  exact (hK.re_pos ht ω).ne'

theorem lineExponent_at_zero {μ : ℝ → ℝ → Measure ℝ} (hμ : IsSymmetricFamily μ) {t : ℝ}
    (ht : 0 ≤ t) : lineExponent μ t 0 = 0 := by
  haveI := hμ.1.isProbability 0 t le_rfl ht
  simp [lineExponent, charFun_zero]

/-- The exponent of a step is nonnegative: `Ψ_s ≤ Ψ_t` for `s ≤ t`. -/
theorem lineExponent_mono {μ : ℝ → ℝ → Measure ℝ} (hμ : IsSymmetricFamily μ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ω : ℝ) : lineExponent μ s ω ≤ lineExponent μ t ω := by
  have hK := kernelOrder_line hμ
  have h := (Complex.le_def.1 (hK.mono ω s t hs hst)).1
  unfold lineExponent
  exact neg_le_neg (Real.log_le_log (hK.re_pos (hs.trans hst) ω) h)

/-- **`lem:step-field-determines-family`(1).** `Ψ_t = ∑_{m ≥ 1} g_{t,qt}(q^{-m} ·)`,
`g_{t,qt} = Ψ_{qt} - Ψ_t`, for every `t > 0`. -/
theorem step_field_1 {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure ℝ) (hμ : IsQFamily q μ) {t : ℝ}
    (ht : 0 < t) (ω : ℝ) :
    HasSum (fun m : ℕ => lineExponent μ (q * t) (ω / q ^ (m + 1)) -
      lineExponent μ t (ω / q ^ (m + 1))) (lineExponent μ t ω) := by
  have hq0 : 0 < q := by linarith
  set f : ℕ → ℝ := fun m => lineExponent μ t (ω / q ^ m) with hf
  have hterm : ∀ m : ℕ, lineExponent μ (q * t) (ω / q ^ (m + 1)) -
      lineExponent μ t (ω / q ^ (m + 1)) = f m - f (m + 1) := by
    intro m
    rw [lineExponent_cov hμ ht.le, hf]
    congr 2
    rw [pow_succ]
    field_simp
  simp_rw [hterm]
  have hnn : ∀ m : ℕ, 0 ≤ f m - f (m + 1) := by
    intro m
    rw [← hterm m, sub_nonneg]
    exact lineExponent_mono hμ.1 ht.le (by nlinarith) _
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp_rw [Finset.sum_range_sub']
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ω / q ^ m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hq)
    have h2 := ((lineExponent_continuous hμ.1 ht.le).tendsto 0).comp h1
    rwa [lineExponent_at_zero hμ.1 ht.le] at h2
  have h0 : f 0 = lineExponent μ t ω := by simp [hf]
  rw [← h0]
  simpa using (tendsto_const_nhds (x := f 0)).sub hlim

/-- The kernels on `[1, q)` determine a `q`-covariant family on the line (read in `ℝ¹`). -/
theorem qFamily_determined {q : ℝ} (hq : 1 < q) {μ μ' : ℝ → ℝ → Measure ℝ} (hμ : IsQFamily q μ)
    (hμ' : IsQFamily q μ') (heq : ∀ t ∈ Ico (1 : ℝ) q, μ 0 t = μ' 0 t) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t := by
  intro s t hs hst
  have h := discrete_covariance_levy_determined (d := 1) le_rfl
    (fun s t => (μ s t).map lineEmbL) (fun s t => (μ' s t).map lineEmbL)
    (isSymmetricFamily_lineEmb hμ.1) (isSymmetricFamily_lineEmb hμ'.1) hq
    (isCovariantAt_lineEmb hμ.2) (isCovariantAt_lineEmb hμ'.2)
    (fun t ht => by simp only [heq t ht]) s t hs hst
  exact map_lineEmb_injective h

/-- Two families with the same exponent at every `t ∈ [1, q)` coincide. -/
theorem qFamily_eq_of_lineExponent {q : ℝ} (hq : 1 < q) {μ μ' : ℝ → ℝ → Measure ℝ}
    (hμ : IsQFamily q μ) (hμ' : IsQFamily q μ')
    (h : ∀ t ∈ Ico (1 : ℝ) q, ∀ ω : ℝ, lineExponent μ t ω = lineExponent μ' t ω) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t := by
  refine qFamily_determined hq hμ hμ' fun t ht => ?_
  have ht0 : 0 ≤ t := zero_le_one.trans ht.1
  haveI := hμ.1.1.isProbability 0 t le_rfl ht0
  haveI := hμ'.1.1.isProbability 0 t le_rfl ht0
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_kernel_eq_exp hμ.1 ht0, charFun_kernel_eq_exp hμ'.1 ht0, h t ht ω]

/-- **`lem:step-field-determines-family`(2), the field.** Two families with the same `g_{t,qt}`
for all `t ∈ [1,q)` coincide. -/
theorem step_field_2 {q : ℝ} (hq : 1 < q) (μ μ' : ℝ → ℝ → Measure ℝ) (hμ : IsQFamily q μ)
    (hμ' : IsQFamily q μ')
    (heq : ∀ t ∈ Ico 1 q, ∀ ω : ℝ, lineExponent μ (q * t) ω - lineExponent μ t ω =
      lineExponent μ' (q * t) ω - lineExponent μ' t ω) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t := by
  refine qFamily_eq_of_lineExponent hq hμ hμ' fun t ht ω => ?_
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
  refine (step_field_1 hq μ hμ ht0 ω).unique ?_
  simp_rw [heq t ht]
  exact step_field_1 hq μ' hμ' ht0 ω

/-- **`lem:step-field-determines-family`(2), the knots.** Two families with the same octave step
`μ_{1,q}` have the same knot kernels. -/
theorem step_field_2_knots {q : ℝ} (hq : 1 < q) (μ μ' : ℝ → ℝ → Measure ℝ) (hμ : IsQFamily q μ)
    (hμ' : IsQFamily q μ') (h : μ 1 q = μ' 1 q) : ∀ n : ℤ, μ 0 (q ^ n) = μ' 0 (q ^ n) := by
  have hq0 : 0 < q := by linarith
  -- the exponent of the octave step is `g_{1,q} = Ψ_q - Ψ_1`
  have hstep : ∀ ν : ℝ → ℝ → Measure ℝ, IsQFamily q ν → ∀ ω : ℝ,
      charFun (ν 1 q) ω = ((Real.exp (-(lineExponent ν q ω - lineExponent ν 1 ω)) : ℝ) : ℂ) := by
    intro ν hν ω
    have hm := charFun_kernel_mul_gen hν.1.1 zero_le_one hq.le ω
    rw [charFun_kernel_eq_exp hν.1 hq0.le, charFun_kernel_eq_exp hν.1 zero_le_one] at hm
    have hne : ((Real.exp (-lineExponent ν 1 ω) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    have : charFun (ν 1 q) ω = ((Real.exp (-lineExponent ν q ω)) : ℂ) /
        ((Real.exp (-lineExponent ν 1 ω)) : ℂ) := by
      rw [hm, mul_div_cancel_right₀ _ hne]
    rw [this, ← Complex.ofReal_div, ← Real.exp_sub]
    ring_nf
  have hg : ∀ ω : ℝ, lineExponent μ (q * 1) ω - lineExponent μ 1 ω =
      lineExponent μ' (q * 1) ω - lineExponent μ' 1 ω := by
    intro ω
    have h1 := (hstep μ hμ ω).symm.trans ((congrArg (fun m => charFun m ω) h).trans
      (hstep μ' hμ' ω))
    have h2 := Real.exp_injective (Complex.ofReal_injective h1)
    rw [mul_one]
    linarith
  -- so the knot kernels at `1` agree
  have h1 : μ 0 1 = μ' 0 1 := by
    haveI := hμ.1.1.isProbability 0 1 le_rfl zero_le_one
    haveI := hμ'.1.1.isProbability 0 1 le_rfl zero_le_one
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    have hΨ : lineExponent μ 1 ω = lineExponent μ' 1 ω := by
      refine (step_field_1 hq μ hμ one_pos ω).unique ?_
      simp_rw [hg]
      exact step_field_1 hq μ' hμ' one_pos ω
    rw [charFun_kernel_eq_exp hμ.1 zero_le_one, charFun_kernel_eq_exp hμ'.1 zero_le_one, hΨ]
  intro n
  rw [← mul_one (q ^ n), kernel_zpow_of_cov hq hμ.2 n 1 zero_le_one,
    kernel_zpow_of_cov hq hμ'.2 n 1 zero_le_one, h1]

end Pyramids
