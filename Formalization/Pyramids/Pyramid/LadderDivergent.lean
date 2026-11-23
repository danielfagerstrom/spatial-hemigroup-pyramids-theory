/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.LadderNuStar
import Pyramids.LineAppendix.SurfaceFamily

/-!
# `prop:ladder-knot-kernel`(3): without the moment

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:ladder-knot-kernel`. Wave 3a:
`ladder_knot_kernel_3` moved here from `PyramidsSkeleton.Ch03Pyramid`, unchanged in name. Its proof
does not use the hypotheses `1 ≤ d`, `ϱ` symmetric and `ϱ` infinitely divisible, which were dropped
(2026-11-14, a strengthening): the data `D_ϱ` carry what is read.

## The route

Write `ψ*(ω) := ∫ (1 - cos⟨ω,x⟩) ν*(dx) ∈ [0,∞]` and `S_M(ω) := ∑_{m < M} ψ_ϱ(q^{-m-1}ω)`, so that
the partial product is `e^{-S_M(ω)}` (`ladderProd_eq_exp`) and, by Tonelli,
`ψ*(ω) ≤ sup_M S_M(ω)`, with `S_M(ω) → ∞` where `ψ*(ω) = ∞`.

* **Step 1** (`levy_of_ball_bound`): if `ψ*` is bounded on a ball, `ν*` is a Lévy measure, hence the
  moment (`lintegral_posLog_of_ladderNuStar`). The bound averages along the coordinate axes:
  `1 ∧ y² ≤ 3(1 - cos y) + ∫_0^2 (1 - cos sy) ds` at `y = c x_i`, and
  `1 ∧ |x|² ≤ c^{-2} ∑_i (1 ∧ c²x_i²)`. No Riemann–Lebesgue lemma is needed.
* **Step 2**: a limit that is a characteristic function is `> 1/2` near `0`, so `S_M < log 2` there
  for every `M`, and Step 1 applies.
* **Step 3**: `1 - cos(a + b) ≤ 2(1 - cos a) + 2(1 - cos b)` (`one_sub_cos_add_le`), so
  `ψ*(a - b) ≤ 2ψ*(a) + 2ψ*(b)`. If `{ψ* < ∞}` had positive measure, some `{ψ* ≤ k}` would, and
  Steinhaus's theorem would make `{ψ* ≤ k} - {ψ* ≤ k}`, on which `ψ* ≤ 4k`, a neighbourhood of `0`;
  Step 1 applies. So `ψ* = ∞` almost everywhere, and there the partial products tend to `0`. Neither
  Minkowski's inequality nor the subgroup `{ψ* < ∞}` is needed.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace Pointwise

variable {d : ℕ}

/-! ## S-finiteness -/

/-- A Lévy measure is s-finite: it is finite on the pieces of `{0} ∪ {|x| > 1/(n+1)}`. -/
theorem SymLevyData.sFinite (D : SymLevyData d) : SFinite D.ν := by
  set T : ℕ → Set (Rd d) := fun n => {0} ∪ {x | 1 / ((n : ℝ) + 1) < ‖x‖} with hT
  set S := disjointed T with hS
  have hTm : ∀ n, MeasurableSet (T n) := fun n =>
    (measurableSet_singleton 0).union (measurableSet_lt measurable_const measurable_norm)
  have hSm : ∀ n, MeasurableSet (S n) := MeasurableSet.disjointed hTm
  have hSd : Pairwise (Function.onFun Disjoint S) := disjoint_disjointed T
  have hSU : ⋃ n, S n = univ := by
    rw [hS, iUnion_disjointed]
    refine eq_univ_of_forall fun x => ?_
    rcases eq_or_ne x 0 with hx | hx
    · exact mem_iUnion.2 ⟨0, Or.inl hx⟩
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 hx)
      exact mem_iUnion.2 ⟨n, Or.inr hn⟩
  have hfin : ∀ n, D.ν (S n) ≠ ⊤ := by
    intro n
    refine ne_top_of_le_ne_top ?_ (measure_mono (disjointed_subset T n))
    refine ne_top_of_le_ne_top ?_ (measure_union_le _ _)
    rw [D.ν_zero, zero_add]
    exact D.measure_norm_gt_ne_top (by positivity)
  have hsplit : D.ν = Measure.sum fun n => D.ν.restrict (S n) := by
    rw [← Measure.restrict_iUnion hSd hSm, hSU, Measure.restrict_univ]
  haveI : ∀ n, IsFiniteMeasure (D.ν.restrict (S n)) := fun n =>
    isFiniteMeasure_restrict.2 (hfin n)
  rw [hsplit]
  infer_instance

theorem ladderNuStar_sFinite (q : ℝ) (D : SymLevyData d) : SFinite (ladderNuStar q D.ν) := by
  haveI := D.sFinite
  rw [ladderNuStar]
  infer_instance

/-! ## Step 1: a bound on a ball -/

/-- `min(1, ∑ aᵢ) ≤ ∑ min(1, aᵢ)` for `aᵢ ≥ 0`. -/
theorem min_one_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    min 1 (∑ i ∈ s, a i) ≤ ∑ i ∈ s, min 1 (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j _ => ha j
    have hs' : 0 ≤ ∑ j ∈ s, min 1 (a j) := Finset.sum_nonneg fun j _ => le_min zero_le_one (ha j)
    rcases le_total 1 (a i) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (le_add_of_nonneg_right hs')
    · rw [min_eq_right h]
      calc min 1 (a i + ∑ j ∈ s, a j) ≤ a i + min 1 (∑ j ∈ s, a j) := by
            rcases le_total 1 (∑ j ∈ s, a j) with h2 | h2
            · rw [min_eq_left h2]
              exact (min_le_left _ _).trans (le_add_of_nonneg_left (ha i))
            · rw [min_eq_right h2]
              exact min_le_right _ _
        _ ≤ a i + ∑ j ∈ s, min 1 (a j) := add_le_add_right ih _

/-- **Step 1.** If `∫ (1 - cos⟨ω,x⟩) m(dx) ≤ C < ∞` for `|ω| < ε`, then `m` is a Lévy measure. -/
theorem levy_of_ball_bound (m : Measure (Rd d)) [SFinite m] {ε : ℝ} (hε : 0 < ε)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ ω : Rd d, ‖ω‖ < ε → ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) ∂m ≤ C) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂m ≠ ⊤ := by
  set c : ℝ := min ε 1 / 3 with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    have := min_le_right ε 1
    linarith
  have hcε : 2 * c < ε := by
    have := min_le_left ε 1
    linarith
  set e : Fin d → Rd d := fun i => EuclideanSpace.single i (1 : ℝ) with he
  have hinner : ∀ (i : Fin d) (s : ℝ) (x : Rd d), ⟪s • e i, x⟫ = s * x i := by
    intro i s x
    simp [he, real_inner_smul_left, EuclideanSpace.inner_single_left]
  have hnorm : ∀ (i : Fin d) (s : ℝ), 0 ≤ s → ‖s • e i‖ = s := by
    intro i s hs
    simp [he, norm_smul, Real.norm_of_nonneg hs]
  -- each coordinate
  have hcoord : ∀ i : Fin d, ∫⁻ x, ENNReal.ofReal (min 1 ((c * x i) ^ 2)) ∂m ≤ 3 * C + 2 * C := by
    intro i
    set g : Rd d → ℝ → ℝ≥0∞ := fun x s => ENNReal.ofReal (1 - Real.cos ⟪(s * c) • e i, x⟫)
      with hg
    have hgm : Measurable (Function.uncurry g) := by
      simp only [hg]
      fun_prop
    have hpt : ∀ x : Rd d, ENNReal.ofReal (min 1 ((c * x i) ^ 2)) ≤
        3 * ENNReal.ofReal (1 - Real.cos ⟪c • e i, x⟫) + ∫⁻ s in Ioc (0 : ℝ) 2, g x s := by
      intro x
      refine (min_one_sq_le_avg (c * x i)).trans (le_of_eq ?_)
      simp only [hg, hinner]
      congr 3
      funext s
      congr 2
      ring_nf
    calc ∫⁻ x, ENNReal.ofReal (min 1 ((c * x i) ^ 2)) ∂m
        ≤ ∫⁻ x, (3 * ENNReal.ofReal (1 - Real.cos ⟪c • e i, x⟫) +
            ∫⁻ s in Ioc (0 : ℝ) 2, g x s) ∂m := lintegral_mono hpt
      _ = 3 * ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪c • e i, x⟫) ∂m +
            ∫⁻ s in Ioc (0 : ℝ) 2, ∫⁻ x, g x s ∂m := by
          rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
            lintegral_lintegral_swap hgm.aemeasurable]
      _ ≤ 3 * C + ∫⁻ _ in Ioc (0 : ℝ) 2, C := by
          refine add_le_add (by gcongr; exact h _ (by rw [hnorm i c hc0.le]; linarith)) ?_
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => h _ ?_
          rw [hnorm i _ (mul_nonneg hs.1.le hc0.le)]
          nlinarith [hs.2]
      _ = 3 * C + 2 * C := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_ofNat, mul_comm C 2]
  -- the coordinates control the norm
  have hpt : ∀ x : Rd d, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ≤
      ENNReal.ofReal (c ^ 2)⁻¹ * ∑ i, ENNReal.ofReal (min 1 ((c * x i) ^ 2)) := by
    intro x
    have hsum : c ^ 2 * ‖x‖ ^ 2 = ∑ i, (c * x i) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h1 : min (‖x‖ ^ 2) 1 ≤ (c ^ 2)⁻¹ * min 1 (c ^ 2 * ‖x‖ ^ 2) := by
      have hc2 : 0 < c ^ 2 := by positivity
      rcases le_total (c ^ 2 * ‖x‖ ^ 2) 1 with h2 | h2
      · rw [min_eq_right h2, inv_mul_cancel_left₀ hc2.ne']
        exact min_le_left _ _
      · rw [min_eq_left h2]
        refine (min_le_right _ _).trans ?_
        rw [mul_one, one_le_inv₀ hc2]
        nlinarith
    have h2 := min_one_sum_le Finset.univ (fun i => (c * x i) ^ 2) fun i => sq_nonneg _
    rw [← hsum] at h2
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => le_min zero_le_one (sq_nonneg _)), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ fun i _ => by
    fun_prop]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  refine ne_top_of_le_ne_top ?_ (Finset.sum_le_sum fun i _ => hcoord i)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (by norm_num) hC, ENNReal.mul_ne_top (by norm_num) hC⟩)

/-! ## The function `ψ*` -/

/-- **`ψ*(ω) := ∫ (1 - cos⟨ω,x⟩) ν*(dx)`**, in `[0,∞]`. -/
noncomputable def psiStar (q : ℝ) (ν : Measure (Rd d)) (ω : Rd d) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪ω, x⟫) ∂ladderNuStar q ν

/-- `1 - cos(a + b) ≤ 2(1 - cos a) + 2(1 - cos b)`. -/
theorem one_sub_cos_add_le (a b : ℝ) :
    1 - Real.cos (a + b) ≤ 2 * (1 - Real.cos a) + 2 * (1 - Real.cos b) := by
  have h2 : ∀ w : ℝ, 1 - Real.cos (2 * w) = 2 * Real.sin w ^ 2 := fun w => by
    rw [Real.cos_two_mul, Real.cos_sq']
    ring
  set u := a / 2
  set v := b / 2
  have ha : a = 2 * u := by ring
  have hb : b = 2 * v := by ring
  have hab : a + b = 2 * (u + v) := by ring
  rw [hab, ha, hb, h2, h2, h2]
  have hs : |Real.sin (u + v)| ≤ |Real.sin u| + |Real.sin v| := by
    rw [Real.sin_add]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · rw [abs_mul, mul_comm]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h3 : Real.sin (u + v) ^ 2 ≤ (|Real.sin u| + |Real.sin v|) ^ 2 := by
    rw [← sq_abs (Real.sin (u + v))]
    exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  nlinarith [sq_abs (Real.sin u), sq_abs (Real.sin v), sq_nonneg (|Real.sin u| - |Real.sin v|)]

theorem psiStar_add_le (q : ℝ) (ν : Measure (Rd d)) (ω ω' : Rd d) :
    psiStar q ν (ω + ω') ≤ 2 * psiStar q ν ω + 2 * psiStar q ν ω' := by
  rw [psiStar, psiStar, psiStar, ← lintegral_const_mul _ (by fun_prop),
    ← lintegral_const_mul _ (by fun_prop), ← lintegral_add_left (by fun_prop)]
  refine lintegral_mono fun x => ?_
  have h := ENNReal.ofReal_le_ofReal (one_sub_cos_add_le ⟪ω, x⟫ ⟪ω', x⟫)
  rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (sub_nonneg.2 (Real.cos_le_one _)))
      (mul_nonneg (by norm_num) (sub_nonneg.2 (Real.cos_le_one _))),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
    ← inner_add_left] at h
  exact h

theorem psiStar_neg (q : ℝ) (ν : Measure (Rd d)) (ω : Rd d) :
    psiStar q ν (-ω) = psiStar q ν ω := by
  simp only [psiStar, inner_neg_left, Real.cos_neg]

theorem measurable_psiStar (q : ℝ) (D : SymLevyData d) : Measurable (psiStar q D.ν) := by
  haveI := ladderNuStar_sFinite q D
  have h : Measurable fun p : Rd d × Rd d => ENNReal.ofReal (1 - Real.cos ⟪p.1, p.2⟫) := by
    fun_prop
  exact h.lintegral_prod_right'

/-- **Tonelli**: `ψ*(ω) = ∑_m ∫ (1 - cos⟨q^{-m-1}ω, v⟩) ν(dv)`. -/
theorem psiStar_eq_tsum (q : ℝ) (ν : Measure (Rd d)) (ω : Rd d) :
    psiStar q ν ω = ∑' m : ℕ,
      ∫⁻ v, ENNReal.ofReal (1 - Real.cos ⟪(q ^ (-((m : ℤ) + 1))) • ω, v⟫) ∂ν := by
  rw [psiStar, lintegral_ladderNuStar q ν (by fun_prop), lintegral_tsum fun m => by
    fun_prop]
  simp_rw [real_inner_smul_left, real_inner_smul_right]

/-- **Step 1 for `ν*`.** If `ψ*` is bounded on a ball, the moment holds. -/
theorem moment_of_psiStar_bound {q : ℝ} (hq : 1 < q) (D : SymLevyData d) {ε : ℝ} (hε : 0 < ε)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (h : ∀ ω : Rd d, ‖ω‖ < ε → psiStar q D.ν ω ≤ C) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂D.ν < ⊤ := by
  haveI := ladderNuStar_sFinite q D
  exact lintegral_posLog_of_ladderNuStar hq D (levy_of_ball_bound _ hε hC h)

/-! ## The partial products -/

/-- `S_M(ω) := ∑_{m < M} ψ_ϱ(q^{-m-1}ω)`. -/
noncomputable def ladderSum (q : ℝ) (D : SymLevyData d) (M : ℕ) (ω : Rd d) : ℝ :=
  ∑ m ∈ Finset.range M, D.exponent ((q ^ (-((m : ℤ) + 1))) • ω)

theorem ladderProd_eq_exp {q : ℝ} {ρ : Measure (Rd d)} {D : SymLevyData d} (hD : IsSymData ρ D)
    (M : ℕ) (ω : Rd d) : ladderProd q ρ M ω = ((Real.exp (-ladderSum q D M ω) : ℝ) : ℂ) := by
  rw [ladderProd, Finset.prod_congr rfl fun m _ => hD _, ← Complex.ofReal_prod, ← Real.exp_sum,
    ladderSum, Finset.sum_neg_distrib]

theorem ladderSum_mono (q : ℝ) (D : SymLevyData d) (ω : Rd d) :
    Monotone fun M => ladderSum q D M ω := by
  refine monotone_nat_of_le_succ fun M => ?_
  simp only [ladderSum, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (D.exponent_nonneg _)

/-- The partial sums of the Tonelli series are below `S_M`. -/
theorem sum_lintegral_le_ladderSum (q : ℝ) (D : SymLevyData d) (M : ℕ) (ω : Rd d) :
    ∑ m ∈ Finset.range M,
      ∫⁻ v, ENNReal.ofReal (1 - Real.cos ⟪(q ^ (-((m : ℤ) + 1))) • ω, v⟫) ∂D.ν ≤
        ENNReal.ofReal (ladderSum q D M ω) := by
  rw [ladderSum, ENNReal.ofReal_sum_of_nonneg fun m _ => D.exponent_nonneg _]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (D.integrable_one_sub_cos _)
    (ae_of_all _ fun _ => sub_nonneg.2 (Real.cos_le_one _))]
  refine ENNReal.ofReal_le_ofReal ?_
  change _ ≤ quad D.A _ + _
  linarith [quad_nonneg D.A_posSemidef ((q ^ (-((m : ℤ) + 1))) • ω)]

theorem psiStar_le_of_ladderSum_le (q : ℝ) (D : SymLevyData d) {ω : Rd d} {B : ℝ}
    (h : ∀ M : ℕ, ladderSum q D M ω ≤ B) : psiStar q D.ν ω ≤ ENNReal.ofReal B := by
  rw [psiStar_eq_tsum]
  exact ENNReal.tsum_le_of_sum_range_le fun M =>
    (sum_lintegral_le_ladderSum q D M ω).trans (ENNReal.ofReal_le_ofReal (h M))

/-- Where `ψ* = ∞` the partial products tend to `0`. -/
theorem tendsto_ladderProd_zero {q : ℝ} {ρ : Measure (Rd d)} {D : SymLevyData d}
    (hD : IsSymData ρ D) {ω : Rd d} (hω : psiStar q D.ν ω = ⊤) :
    Tendsto (fun M => ladderProd q ρ M ω) atTop (𝓝 0) := by
  have htop : Tendsto (fun M : ℕ => ladderSum q D M ω) atTop atTop := by
    refine tendsto_atTop.2 fun K => ?_
    have h1 := ENNReal.tendsto_nat_tsum fun m : ℕ =>
      ∫⁻ v, ENNReal.ofReal (1 - Real.cos ⟪(q ^ (-((m : ℤ) + 1))) • ω, v⟫) ∂D.ν
    rw [← psiStar_eq_tsum, hω] at h1
    filter_upwards [h1.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top (r := K)))] with M hM
    have h2 := lt_of_lt_of_le hM (sum_lintegral_le_ladderSum q D M ω)
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 h2).1.le
  simp_rw [ladderProd_eq_exp hD]
  have h3 := Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
  have h4 := (Complex.continuous_ofReal.tendsto 0).comp h3
  rw [Complex.ofReal_zero] at h4
  exact h4

/-! ## `prop:ladder-knot-kernel`(3) -/

/-- **`prop:ladder-knot-kernel`(3).** For an infinitely divisible `ϱ` with symmetric data
`(A_ϱ, ν_ϱ)` and `∫ log₊|x| ν_ϱ(dx) = ∞`, the partial products have no limit that is a
characteristic function, and they tend to `0` at almost every `ω`. -/
theorem ladder_knot_kernel_3 {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (Dρ : SymLevyData d) (hDρ : IsSymData ρ Dρ)
    (hinf : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν = ⊤) :
    (¬ ∃ ν : Measure (Rd d), IsProbabilityMeasure ν ∧
        ∀ ω : Rd d, Tendsto (fun M => ladderProd q ρ M ω) atTop (𝓝 (charFun ν ω))) ∧
      ∀ᵐ ω ∂(volume : Measure (Rd d)), Tendsto (fun M => ladderProd q ρ M ω) atTop (𝓝 0) := by
  have hnot : ∀ {ε : ℝ}, 0 < ε → ∀ {C : ℝ≥0∞}, C ≠ ⊤ →
      ¬ ∀ ω : Rd d, ‖ω‖ < ε → psiStar q Dρ.ν ω ≤ C := by
    intro ε hε C hC h
    exact (moment_of_psiStar_bound hq Dρ hε hC h).ne hinf
  refine ⟨?_, ?_⟩
  · -- Step 2
    rintro ⟨ν, hν, hlim⟩
    haveI := hν
    obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1
      ((continuous_charFun (μ := ν)).continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine hnot hε (C := ENNReal.ofReal (Real.log 2)) ENNReal.ofReal_ne_top fun ω hω => ?_
    refine psiStar_le_of_ladderSum_le q Dρ fun M => ?_
    have hre : Tendsto (fun M : ℕ => Real.exp (-ladderSum q Dρ M ω)) atTop
        (𝓝 (charFun ν ω).re) := by
      have h1 := (Complex.continuous_re.tendsto _).comp (hlim ω)
      simp_rw [Function.comp_def, ladderProd_eq_exp hDρ, Complex.ofReal_re] at h1
      exact h1
    have hanti : Antitone fun M : ℕ => Real.exp (-ladderSum q Dρ M ω) :=
      fun M N hMN => Real.exp_le_exp.2 (neg_le_neg (ladderSum_mono q Dρ ω hMN))
    have hhalf : 1 / 2 < (charFun ν ω).re := by
      have h1 := hball (show dist ω 0 < ε by rwa [dist_zero_right])
      rw [charFun_zero, probReal_univ, Complex.ofReal_one, Complex.dist_eq] at h1
      have h2 := (Complex.abs_re_le_norm (charFun ν ω - 1)).trans_lt h1
      rw [Complex.sub_re, Complex.one_re] at h2
      linarith [(abs_lt.1 h2).1]
    have hge := hanti.le_of_tendsto hre M
    by_contra hcon
    have h3 : Real.exp (-ladderSum q Dρ M ω) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
      exact Real.exp_le_exp.2 (by linarith [not_le.1 hcon])
    linarith
  · -- Step 3
    have hnull : ∀ k : ℕ, volume {ω : Rd d | psiStar q Dρ.ν ω ≤ k} = 0 := by
      intro k
      by_contra hpos
      set E := {ω : Rd d | psiStar q Dρ.ν ω ≤ k} with hE
      have hEm : MeasurableSet E := measurableSet_le (measurable_psiStar q Dρ) measurable_const
      have hst := Measure.sub_mem_nhds_zero_of_addHaar_pos volume E hEm (pos_iff_ne_zero.2 hpos)
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hst
      refine hnot hr (C := 4 * k) (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top k))
        fun ω hω => ?_
      obtain ⟨a, ha, b, hb, hab⟩ := hball (show ω ∈ Metric.ball 0 r by
        rwa [Metric.mem_ball, dist_zero_right])
      have hab' : a - b = ω := hab
      rw [← hab', sub_eq_add_neg]
      refine (psiStar_add_le q Dρ.ν a (-b)).trans ?_
      rw [psiStar_neg]
      have ha' : psiStar q Dρ.ν a ≤ k := ha
      have hb' : psiStar q Dρ.ν b ≤ k := hb
      calc 2 * psiStar q Dρ.ν a + 2 * psiStar q Dρ.ν b ≤ 2 * k + 2 * k := by gcongr
        _ = 4 * k := by ring
    have hfin : volume {ω : Rd d | psiStar q Dρ.ν ω ≠ ⊤} = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hnull)
      obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hω
      exact mem_iUnion.2 ⟨k, hk.le⟩
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hfin] with ω hω
    exact tendsto_ladderProd_zero hDρ (not_not.1 hω)

end Pyramids
