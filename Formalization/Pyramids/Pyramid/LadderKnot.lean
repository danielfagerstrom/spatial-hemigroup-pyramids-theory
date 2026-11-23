/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.LadderNuStar
import Pyramids.Pyramid.EquivalentWeights
import Pyramids.Cited.A49
import Pyramids.Cited.A50

/-!
# `prop:ladder-knot-kernel`(1) and the two moments of (2)

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:ladder-knot-kernel`. Wave 3a:
`ladder_knot_kernel_1` and `ladder_knot_kernel_2_moments` moved here from
`PyramidsSkeleton.Ch03Pyramid`, unchanged in name. `ladder_knot_kernel_2_moments` no longer takes
the hypothesis that `ϱ` is symmetric, which its proof does not use: the data `D_ϱ` are given
(2026-11-14, a strengthening).

## The route

* **The product.** Covariance and (I1) give `ϱ̂(ω) μ̂_1(ω) = μ̂_1(qω)`, so
  `∏_{m < M} ϱ̂(q^{-m-1}ω) · μ̂_1(q^{-M}ω) = μ̂_1(ω)`; the last factor tends to `μ̂_1(0) = 1`, and
  `μ̂_1` has no zero. The partial convolutions have the partial products as transforms.
* **The data.** `lem:family-structure` and `lem:discrete-covariance-levy` give `A_q = q²A_1`,
  `A_q = A_1 + A_ϱ`, `D_q ν_1 = ν_ϱ + ν_1`; the last equation has the one solution `ν*` among the
  Lévy measures (`eq_ladderNuStar_of_map`), so `ν_1 = ν*`, and `ν*` being a Lévy measure gives the
  moment (`lintegral_posLog_of_ladderNuStar`). No Tonelli argument on exponents is needed.
* **The two moments** are A49 for `ϑ(x) = log(|x| ∨ e)`, submultiplicative by A50 and continuous,
  with `log₊|x| ≤ ϑ(x) ≤ log₊|x| + 1` and `ν_ϱ{|x| > 1} < ∞`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexOrder

variable {d : ℕ}

/-! ## The partial products -/

/-- The partial convolution over `ℕ`-indexed factors. -/
theorem ladderConv_eq (q : ℝ) (ρ : Measure (Rd d)) (M : ℕ) : ladderConv q ρ M =
    convList ((List.range M).map fun m : ℕ => ρ.map fun x => (q ^ (-((m : ℤ) + 1))) • x) := by
  unfold ladderConv
  congr 1
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [List.range_succ, List.map_append] at ih ⊢
    rw [← ih]
    simp

/-- The partial convolutions are probability measures whose transforms are the partial
products. -/
theorem ladderConv_charFun (q : ℝ) (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ] (M : ℕ) :
    IsProbabilityMeasure (ladderConv q ρ M) ∧
      ∀ ω : Rd d, charFun (ladderConv q ρ M) ω = ladderProd q ρ M ω := by
  have hl : ∀ m ∈ (List.range M).map (fun k : ℕ => ρ.map fun x => (q ^ (-((k : ℤ) + 1))) • x),
      IsProbabilityMeasure m := by
    intro m hm
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hm
    exact Measure.isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
  obtain ⟨hp, hc⟩ := convList_charFun _ hl
  rw [ladderConv_eq]
  refine ⟨hp, fun ω => ?_⟩
  rw [hc, List.map_map, list_prod_map_range, ladderProd]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Function.comp_apply]
  exact charFun_map_smul _ _

/-- `q^{-M} ω → 0`. -/
theorem tendsto_zpow_neg_smul {q : ℝ} (hq : 1 < q) (ω : Rd d) :
    Tendsto (fun M : ℕ => (q ^ (-(M : ℤ))) • ω) atTop (𝓝 0) := by
  have h1 : Tendsto (fun M : ℕ => q ^ (-(M : ℤ))) atTop (𝓝 0) := by
    simp only [zpow_neg, zpow_natCast]
    exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hq)
  simpa using h1.smul_const ω

/-- **The telescoping product.** If `ϱ̂(ω) φ(ω) = φ(qω)` for every `ω`, then
`∏_{m < M} ϱ̂(q^{-m-1}ω) · φ(q^{-M}ω) = φ(ω)`. -/
theorem ladderProd_mul_eq {q : ℝ} (hq : 0 < q) (ρ : Measure (Rd d)) {φ : Rd d → ℂ}
    (h : ∀ ω : Rd d, charFun ρ ω * φ ω = φ (q • ω)) (ω : Rd d) (M : ℕ) :
    ladderProd q ρ M ω * φ ((q ^ (-(M : ℤ))) • ω) = φ ω := by
  induction M with
  | zero => simp [ladderProd]
  | succ M ih =>
    rw [ladderProd, Finset.prod_range_succ, mul_assoc]
    push_cast
    rw [h, smul_smul]
    have e : q * q ^ (-((M : ℤ) + 1)) = q ^ (-(M : ℤ)) := by
      rw [← zpow_one_add₀ hq.ne']
      ring_nf
    rw [e]
    exact ih

/-- **The partial products converge** to `φ(ω)` when `φ` is continuous at `0` with `φ(0) = 1`, has
no zero, and satisfies `ϱ̂ φ = φ(q ·)`. -/
theorem tendsto_ladderProd {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d)) {φ : Rd d → ℂ}
    (h : ∀ ω : Rd d, charFun ρ ω * φ ω = φ (q • ω)) (hc : ContinuousAt φ 0) (h0 : φ 0 = 1)
    (hne : ∀ ω : Rd d, φ ω ≠ 0) (ω : Rd d) :
    Tendsto (fun M => ladderProd q ρ M ω) atTop (𝓝 (φ ω)) := by
  have hq0 : 0 < q := by linarith
  have hlim : Tendsto (fun M : ℕ => φ ((q ^ (-(M : ℤ))) • ω)) atTop (𝓝 1) := by
    rw [← h0]
    exact hc.tendsto.comp (tendsto_zpow_neg_smul hq ω)
  have heq : (fun M => ladderProd q ρ M ω) = fun M : ℕ => φ ω / φ ((q ^ (-(M : ℤ))) • ω) := by
    funext M
    rw [eq_div_iff (hne _)]
    exact ladderProd_mul_eq hq0 ρ h ω M
  rw [heq]
  have h2 : Tendsto (fun M : ℕ => φ ω / φ ((q ^ (-(M : ℤ))) • ω)) atTop (𝓝 (φ ω / 1)) :=
    tendsto_const_nhds.div hlim one_ne_zero
  rwa [div_one] at h2

/-! ## `prop:ladder-knot-kernel`(1) -/

/-- **`prop:ladder-knot-kernel`(1).** For a symmetric `q`-covariant family with `S_q t = qt`, with
`ϱ = μ_{1,q}` of data `(A_ϱ, ν_ϱ)` and `μ_1` of data `(A_1, ν_1)`: `μ̂_1(ω)` is the limit of the
partial products `∏_{m ≤ M} ϱ̂(q^{-m}ω)`, the transforms of `D_{q^{-1}}ϱ * ⋯ * D_{q^{-M}}ϱ`;
`A_1 = A_ϱ/(q² - 1)`; `ν_1 = ν*`; and `∫ log₊|x| ν_ϱ(dx) < ∞`. -/
theorem ladder_knot_kernel_1 (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) (hcov : IsCovariantAt μ q (fun t => q * t))
    (Dρ D1 : SymLevyData d) (hDρ : IsSymData (μ 1 q) Dρ) (hD1 : IsSymData (μ 0 1) D1) :
    (∀ ω : Rd d, Tendsto (fun M => ladderProd q (μ 1 q) M ω) atTop (𝓝 (charFun (μ 0 1) ω)) ∧
        Tendsto (fun M => charFun (ladderConv q (μ 1 q) M) ω) atTop (𝓝 (charFun (μ 0 1) ω))) ∧
      D1.A = (q ^ 2 - 1)⁻¹ • Dρ.A ∧ D1.ν = ladderNuStar q Dρ.ν ∧
      ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤ := by
  have hq0 : 0 < q := by linarith
  haveI := hμ.1.isProbability 1 q zero_le_one hq.le
  haveI := hμ.1.isProbability 0 1 le_rfl zero_le_one
  have hK := kernelOrder_rd hd hμ
  -- `ϱ̂ μ̂_1 = μ̂_1(q ·)`
  have hstep : ∀ ω : Rd d, charFun (μ 1 q) ω * charFun (μ 0 1) ω = charFun (μ 0 1) (q • ω) := by
    intro ω
    have hk : (μ 0 1).map (fun x => q • x) = μ 0 q := by
      have := cov_kernel hcov zero_le_one
      rwa [mul_one] at this
    rw [← charFun_kernel_mul μ hμ.1 zero_le_one hq.le, ← hk, charFun_map_smul]
  have hlim : ∀ ω : Rd d,
      Tendsto (fun M => ladderProd q (μ 1 q) M ω) atTop (𝓝 (charFun (μ 0 1) ω)) :=
    tendsto_ladderProd hq _ hstep continuous_charFun.continuousAt (by simp [charFun_zero])
      (fun ω => (hK.pos 1 zero_le_one ω).ne')
  refine ⟨fun ω => ⟨hlim ω, ?_⟩, ?_⟩
  · simp_rw [(ladderConv_charFun q (μ 1 q) _).2 ω]
    exact hlim ω
  -- the data
  obtain ⟨D, hD⟩ := family_structure_exists hd μ hμ
  obtain ⟨hA1, hν1⟩ := isSymData_unique (hD 1 zero_le_one) hD1
  obtain ⟨-, hdiff⟩ := family_structure_data hd μ hμ D hD
  obtain ⟨-, -, -, Q, hQA, hQν, hQ⟩ := hdiff 1 q zero_le_one hq.le
  obtain ⟨hAρ, hνρ⟩ := isSymData_unique hDρ hQ
  have hcovD := (discrete_covariance_levy hd μ hμ D hD hq).2.1
    ((discrete_covariance_levy hd μ hμ D hD hq).1.1 hcov) 1 one_pos
  rw [mul_one] at hcovD
  obtain ⟨hAq, hνq⟩ := hcovD
  -- `A_1 = A_ϱ/(q² - 1)`
  have hA : D1.A = (q ^ 2 - 1)⁻¹ • Dρ.A := by
    have hq21 : q ^ 2 - 1 ≠ 0 := by nlinarith
    rw [hAρ, hQA, hAq, hA1, show q ^ 2 • D1.A - D1.A = (q ^ 2 - 1) • D1.A by
      rw [sub_smul, one_smul], smul_smul, inv_mul_cancel₀ hq21, one_smul]
  -- `ν_1 = ν*`
  have hν : D1.ν = ladderNuStar q Dρ.ν := by
    refine eq_ladderNuStar_of_map hq D1.ν_zero (fun ε hε => D1.measure_norm_gt_ne_top hε) ?_
    rw [hνρ, ← hν1, ← hνq, ← hQν]
  refine ⟨hA, hν, lintegral_posLog_of_ladderNuStar hq Dρ ?_⟩
  rw [← hν]
  exact D1.ν_integrable

/-! ## `prop:ladder-knot-kernel`(2), the two moments -/

/-- `ϑ(x) := log(|x| ∨ e)`. -/
theorem logMaxE_bounds (r : ℝ) (hr : 0 ≤ r) :
    Real.posLog r ≤ Real.log (max r (Real.exp 1)) ∧
      Real.log (max r (Real.exp 1)) ≤ Real.posLog r + 1 := by
  rcases le_total r (Real.exp 1) with h | h
  · rw [max_eq_right h, Real.log_exp]
    refine ⟨?_, by linarith [Real.posLog_nonneg (x := r)]⟩
    rw [Real.posLog]
    refine max_le zero_le_one ?_
    rcases hr.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; exact zero_le_one
    · exact (Real.log_le_log h0 h).trans (le_of_eq (Real.log_exp 1))
  · rw [max_eq_left h]
    have hlog : 1 ≤ Real.log r := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) h
    rw [Real.posLog, max_eq_right (by linarith)]
    exact ⟨le_rfl, by linarith⟩

theorem continuous_logMaxE : Continuous fun x : Rd d => Real.log (max ‖x‖ (Real.exp 1)) :=
  (continuous_norm.max continuous_const).log fun _ =>
    (lt_of_lt_of_le (Real.exp_pos 1) (le_max_right _ _)).ne'

/-- **`prop:ladder-knot-kernel`(2), the two moments.** For an infinitely divisible `ϱ` with
symmetric data `(A_ϱ, ν_ϱ)`: `∫ log₊|x| ν_ϱ(dx) < ∞` iff `∫ log₊|x| ϱ(dx) < ∞`. -/
theorem ladder_knot_kernel_2_moments (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    (hid : IsInfinitelyDivisible ρ) (Dρ : SymLevyData d)
    (hDρ : IsSymData ρ Dρ) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤ ↔
      ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂ρ < ⊤ := by
  set g : Rd d → ℝ := fun x => Real.log (max ‖x‖ (Real.exp 1)) with hg
  have hgc : Continuous g := continuous_logMaxE
  have hgb : ∀ K : Set (Rd d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, |g x| ≤ C := by
    intro K hK
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hgc.continuousOn
    exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  have hA49 := cited_A49 g cited_A50 hgb hgc.measurable ρ hid Dρ.triplet
    (SymLevyData.hasTriplet hDρ)
  change _ ↔ (∫⁻ x in {x : Rd d | 1 < ‖x‖}, ENNReal.ofReal (g x) ∂Dρ.ν) ≠ ⊤ at hA49
  set S : Set (Rd d) := {x | 1 < ‖x‖} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hlo : ∀ x : Rd d, ENNReal.ofReal (Real.posLog ‖x‖) ≤ ENNReal.ofReal (g x) :=
    fun x => ENNReal.ofReal_le_ofReal (logMaxE_bounds ‖x‖ (norm_nonneg x)).1
  have hhi : ∀ x : Rd d, ENNReal.ofReal (g x) ≤ ENNReal.ofReal (Real.posLog ‖x‖) + 1 := by
    intro x
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add Real.posLog_nonneg zero_le_one]
    exact ENNReal.ofReal_le_ofReal (logMaxE_bounds ‖x‖ (norm_nonneg x)).2
  -- the moment of `ν_ϱ` lives on `{|x| > 1}`
  have hpl : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν =
      ∫⁻ x in S, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν := by
    rw [← lintegral_indicator hSm]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · have hx' : ‖x‖ ≤ 1 := not_lt.1 hx
      rw [indicator_of_notMem hx, Real.posLog,
        max_eq_left (Real.log_nonpos (norm_nonneg x) hx'), ENNReal.ofReal_zero]
  constructor
  · intro hν
    have h1 : (∫⁻ x in S, ENNReal.ofReal (g x) ∂Dρ.ν) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono hhi)
      rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ]
      rw [hpl] at hν
      exact ENNReal.add_ne_top.2 ⟨hν.ne, by simpa using Dρ.measure_norm_gt_ne_top one_pos⟩
    exact lt_of_le_of_lt (lintegral_mono hlo) (lt_top_iff_ne_top.2 (hA49.2 h1))
  · intro hρ
    have h1 : (∫⁻ x, ENNReal.ofReal (g x) ∂ρ) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono hhi)
      rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      exact ENNReal.add_ne_top.2 ⟨hρ.ne, ENNReal.one_ne_top⟩
    rw [hpl]
    exact lt_of_le_of_lt (setLIntegral_mono' hSm fun x _ => hlo x)
      (lt_top_iff_ne_top.2 (hA49.1 h1))

end Pyramids
