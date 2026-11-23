/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.Synthesis
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# The measure `ν* = ∑_{m ≥ 1} D_{q^{-m}} ν_ϱ` of `prop:ladder-knot-kernel`

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:ladder-knot-kernel`. Helpers for the
node's clauses, which are in `LadderKnot`, `LadderCoupling`, `LadderDivergent` and
`LadderStratum`.

* **The bracket.** `∫ (1 ∧ |x|²) ν*(dx) = ∫ b(|v|) ν_ϱ(dv)` with
  `b(r) := ∑_{m ≥ 0} (1 ∧ (r/q^{m+1})²)` (`lintegral_min_ladderNuStar`). The terms with
  `q^{m+1} ≤ r` are `1`, and the others are dominated by a geometric series, so
  `b(r) ≤ log₊ r / log q + q²/(q² - 1) · (1 ∧ r²)` (`ladderBracket_le`) and
  `log₊ r ≤ log q · (b(r) + 1)` for `r > 1` (`posLog_le_ladderBracket`). Hence `ν*` is a Lévy
  measure iff `∫ log₊|x| ν_ϱ(dx) < ∞` (`ladderNuStar_levy`, `lintegral_posLog_of_ladderNuStar`).
* **The equation.** `D_q ν* = ν_ϱ + ν*` (`map_ladderNuStar`), and `ν*` is the only Lévy measure
  with this equation (`eq_ladderNuStar_of_map`): iterating `ν = D_{q^{-1}}ν_ϱ + D_{q^{-1}}ν` gives
  `ν = ∑_{m < M} D_{q^{-m-1}}ν_ϱ + D_{q^{-M}}ν`, and the last term vanishes on every set bounded
  away from `0`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

theorem SymLevyData.exponent_nonneg (D : SymLevyData d) (ω : Rd d) : 0 ≤ D.exponent ω :=
  add_nonneg (quad_nonneg D.A_posSemidef ω)
    (integral_nonneg fun _ => sub_nonneg.2 (Real.cos_le_one _))

theorem SymLevyData.integrable_one_sub_cos (D : SymLevyData d) (ω : Rd d) :
    Integrable (fun x : Rd d => 1 - Real.cos ⟪ω, x⟫) D.ν :=
  D.triplet.integrable_one_sub_cos ω

/-! ## The bracket -/

/-- **The bracket** `b(r) := ∑_{m ≥ 0} (1 ∧ (r/q^{m+1})²)`. -/
noncomputable def ladderBracket (q r : ℝ) : ℝ := ∑' m : ℕ, min ((r / q ^ (m + 1)) ^ 2) 1

theorem ladderBracket_term_le (q r : ℝ) (m : ℕ) :
    min ((r / q ^ (m + 1)) ^ 2) 1 ≤ r ^ 2 * ((q ^ 2)⁻¹) ^ (m + 1) := by
  refine (min_le_left _ _).trans (le_of_eq ?_)
  rw [div_pow, ← pow_mul, inv_pow, ← pow_mul, div_eq_mul_inv]
  ring_nf

theorem ladderBracket_summable {q : ℝ} (hq : 1 < q) (r : ℝ) :
    Summable fun m : ℕ => min ((r / q ^ (m + 1)) ^ 2) 1 := by
  have hq2 : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
  have hg : Summable fun m : ℕ => r ^ 2 * ((q ^ 2)⁻¹) ^ (m + 1) :=
    ((summable_geometric_of_lt_one (by positivity) hq2).comp_injective
      (add_left_injective 1)).mul_left _
  exact Summable.of_nonneg_of_le (fun m => le_min (sq_nonneg _) zero_le_one)
    (ladderBracket_term_le q r) hg

theorem ladderBracket_nonneg (q r : ℝ) : 0 ≤ ladderBracket q r :=
  tsum_nonneg fun _ => le_min (sq_nonneg _) zero_le_one

/-- **The upper bound** `b(r) ≤ log₊ r / log q + q²/(q² - 1) · (1 ∧ r²)`, `r ≥ 0`. -/
theorem ladderBracket_le {q : ℝ} (hq : 1 < q) {r : ℝ} (hr : 0 ≤ r) :
    ladderBracket q r ≤ Real.posLog r / Real.log q + q ^ 2 / (q ^ 2 - 1) * min (r ^ 2) 1 := by
  have hq0 : 0 < q := by linarith
  have hlq : 0 < Real.log q := Real.log_pos hq
  set N := ⌊Real.logb q r⌋₊ with hN
  set f : ℕ → ℝ := fun m => min ((r / q ^ (m + 1)) ^ 2) 1 with hf
  have hs := ladderBracket_summable hq r
  rw [ladderBracket, ← hs.sum_add_tsum_nat_add N]
  refine add_le_add ?_ ?_
  · -- the first `N` terms are at most `1`
    refine (Finset.sum_le_sum fun m _ => min_le_right _ (1 : ℝ)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0, Nat.cast_zero]
      exact div_nonneg Real.posLog_nonneg hlq.le
    · have hlog : 0 ≤ Real.logb q r := by
        by_contra hneg
        rw [hN, Nat.floor_eq_zero.2 (lt_of_lt_of_le (not_le.1 hneg) zero_le_one)] at hpos
        exact lt_irrefl 0 hpos
      refine (Nat.floor_le hlog).trans ?_
      rw [Real.logb]
      exact div_le_div_of_nonneg_right (le_max_right _ _) hlq.le
  · -- the rest is dominated by a geometric series
    have hq2 : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
    have hkey : (r / q ^ (N + 1)) ^ 2 ≤ min (r ^ 2) 1 := by
      have hqN : 1 ≤ q ^ (N + 1) := one_le_pow₀ hq.le
      refine le_min ?_ ?_
      · rw [div_pow]
        exact div_le_self (sq_nonneg r) (one_le_pow₀ hqN)
      · rcases hr.eq_or_lt with h0 | hrpos
        · rw [← h0]; simp
        · have hlt : r < q ^ (N + 1) := by
            have h1 : Real.logb q r < (N : ℝ) + 1 := Nat.lt_floor_add_one _
            have h2 := Real.rpow_lt_rpow_of_exponent_lt hq h1
            rw [Real.rpow_logb hq0 hq.ne' hrpos] at h2
            exact_mod_cast h2
          rw [div_pow, div_le_one (by positivity)]
          exact pow_le_pow_left₀ hr hlt.le 2
    have hterm : ∀ k : ℕ, f (k + N) ≤ min (r ^ 2) 1 * ((q ^ 2)⁻¹) ^ k := by
      intro k
      refine (min_le_left _ _).trans ?_
      have e : (r / q ^ (k + N + 1)) ^ 2 = (r / q ^ (N + 1)) ^ 2 * ((q ^ 2)⁻¹) ^ k := by
        rw [show k + N + 1 = (N + 1) + k by ring, pow_add, inv_pow, ← pow_mul]
        field_simp
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hkey (by positivity)
    have hg : Summable fun k : ℕ => min (r ^ 2) 1 * ((q ^ 2)⁻¹) ^ k :=
      (summable_geometric_of_lt_one (by positivity) hq2).mul_left _
    refine (hs.comp_injective (add_left_injective N)).tsum_le_tsum hterm hg |>.trans
      (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hq2]
    have hq21 : (0 : ℝ) < q ^ 2 - 1 := by nlinarith
    field_simp

/-- **The lower bound** `log₊ r ≤ log q · (b(r) + 1)` for `r > 1`. -/
theorem posLog_le_ladderBracket {q : ℝ} (hq : 1 < q) {r : ℝ} (hr : 1 < r) :
    Real.posLog r ≤ Real.log q * (ladderBracket q r + 1) := by
  have hq0 : 0 < q := by linarith
  have hlq : 0 < Real.log q := Real.log_pos hq
  have hr0 : 0 < r := by linarith
  set N := ⌊Real.logb q r⌋₊ with hN
  have hlog : 0 ≤ Real.logb q r := (Real.logb_pos hq hr).le
  have hs := ladderBracket_summable hq r
  -- the first `N` terms are `1`
  have hfirst : ∑ m ∈ Finset.range N, min ((r / q ^ (m + 1)) ^ 2) 1 = N := by
    have h1 : ∀ m ∈ Finset.range N, min ((r / q ^ (m + 1)) ^ 2) 1 = 1 := by
      intro m hm
      have hmN : m + 1 ≤ N := Finset.mem_range.1 hm
      have hqm : q ^ (m + 1) ≤ r := by
        have h2 : (q : ℝ) ^ ((N : ℕ) : ℝ) ≤ q ^ Real.logb q r :=
          Real.rpow_le_rpow_of_exponent_le hq.le (Nat.floor_le hlog)
        rw [Real.rpow_natCast, Real.rpow_logb hq0 hq.ne' hr0] at h2
        exact (pow_le_pow_right₀ hq.le hmN).trans h2
      refine min_eq_right ?_
      rw [div_pow, one_le_div (by positivity)]
      exact pow_le_pow_left₀ (by positivity) hqm 2
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hNle : (N : ℝ) ≤ ladderBracket q r := by
    rw [← hfirst, ladderBracket]
    exact hs.sum_le_tsum _ fun m _ => le_min (sq_nonneg _) zero_le_one
  have hlt : Real.logb q r < N + 1 := Nat.lt_floor_add_one _
  rw [Real.posLog, max_eq_right (Real.log_nonneg hr.le)]
  have e : Real.log r = Real.log q * Real.logb q r := by
    rw [Real.logb]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) hlq.le

/-! ## Integrals against `ν*` -/

theorem zpow_neg_succ (q : ℝ) (m : ℕ) : q ^ (-((m : ℤ) + 1)) = (q ^ (m + 1))⁻¹ := by
  rw [zpow_neg]
  norm_cast

theorem norm_ladder_smul {q : ℝ} (hq : 0 < q) (m : ℕ) (v : Rd d) :
    ‖(q ^ (-((m : ℤ) + 1))) • v‖ = ‖v‖ / q ^ (m + 1) := by
  rw [norm_smul, zpow_neg_succ, Real.norm_of_nonneg (by positivity), inv_mul_eq_div]

/-- `∫ f dν* = ∫ ∑_m f(q^{-m-1} v) ν(dv)`. -/
theorem lintegral_ladderNuStar (q : ℝ) (ν : Measure (Rd d)) {f : Rd d → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂ladderNuStar q ν = ∫⁻ v, ∑' m : ℕ, f ((q ^ (-((m : ℤ) + 1))) • v) ∂ν := by
  rw [ladderNuStar, lintegral_sum_measure,
    lintegral_tsum (f := fun (m : ℕ) (v : Rd d) => f ((q ^ (-((m : ℤ) + 1))) • v)) fun m =>
      (hf.comp (measurable_const_smul _)).aemeasurable]
  congr 1
  funext m
  exact lintegral_map hf (measurable_const_smul _)

/-- `∫ (1 ∧ |x|²) ν*(dx) = ∫ b(|v|) ν(dv)`. -/
theorem lintegral_min_ladderNuStar {q : ℝ} (hq : 1 < q) (ν : Measure (Rd d)) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ladderNuStar q ν =
      ∫⁻ v, ENNReal.ofReal (ladderBracket q ‖v‖) ∂ν := by
  have hq0 : 0 < q := by linarith
  rw [lintegral_ladderNuStar q ν (by fun_prop)]
  refine lintegral_congr fun v => ?_
  rw [ladderBracket, ENNReal.ofReal_tsum_of_nonneg (fun m => le_min (sq_nonneg _) zero_le_one)
    (ladderBracket_summable hq _)]
  simp_rw [norm_ladder_smul hq0]

/-- **`ν*` is a Lévy measure** when `ν` is one with `∫ log₊|x| ν(dx) < ∞`. -/
theorem ladderNuStar_levy {q : ℝ} (hq : 1 < q) (D : SymLevyData d)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂D.ν < ⊤) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ladderNuStar q D.ν ≠ ⊤ := by
  have hlq : 0 < Real.log q := Real.log_pos hq
  rw [lintegral_min_ladderNuStar hq]
  have hle : ∀ v : Rd d, ENNReal.ofReal (ladderBracket q ‖v‖) ≤
      ENNReal.ofReal (Real.log q)⁻¹ * ENNReal.ofReal (Real.posLog ‖v‖) +
        ENNReal.ofReal (q ^ 2 / (q ^ 2 - 1)) * ENNReal.ofReal (min (‖v‖ ^ 2) 1) := by
    intro v
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hlq.le), ← ENNReal.ofReal_mul (by
      have : (0 : ℝ) < q ^ 2 - 1 := by nlinarith
      positivity), ← ENNReal.ofReal_add (mul_nonneg (inv_nonneg.2 hlq.le) Real.posLog_nonneg)
      (mul_nonneg (by have : (0 : ℝ) < q ^ 2 - 1 := by nlinarith
                      positivity) (le_min (sq_nonneg _) zero_le_one))]
    refine ENNReal.ofReal_le_ofReal ((ladderBracket_le hq (norm_nonneg v)).trans (le_of_eq ?_))
    rw [div_eq_inv_mul]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
    lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmom.ne,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top D.ν_integrable⟩

/-- **The moment from `ν*`**: if `ν*` is a Lévy measure, `∫ log₊|x| ν(dx) < ∞`. -/
theorem lintegral_posLog_of_ladderNuStar {q : ℝ} (hq : 1 < q) (D : SymLevyData d)
    (h : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ladderNuStar q D.ν ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂D.ν < ⊤ := by
  have hlq : 0 < Real.log q := Real.log_pos hq
  rw [lintegral_min_ladderNuStar hq] at h
  set S : Set (Rd d) := {x | 1 < ‖x‖} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hle : ∀ v : Rd d, ENNReal.ofReal (Real.posLog ‖v‖) ≤
      ENNReal.ofReal (Real.log q) * (ENNReal.ofReal (ladderBracket q ‖v‖) + S.indicator 1 v) := by
    intro v
    by_cases hv : 1 < ‖v‖
    · rw [indicator_of_mem (show v ∈ S from hv), Pi.one_apply, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (ladderBracket_nonneg _ _) zero_le_one,
        ← ENNReal.ofReal_mul hlq.le]
      exact ENNReal.ofReal_le_ofReal (posLog_le_ladderBracket hq hv)
    · have h0 : Real.posLog ‖v‖ = 0 := by
        rw [Real.posLog, max_eq_left (Real.log_nonpos (norm_nonneg v) (not_lt.1 hv))]
      rw [h0, ENNReal.ofReal_zero]
      exact bot_le
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_right _ (measurable_one.indicator hSm), lintegral_indicator_one hSm]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2
    ⟨lt_top_iff_ne_top.2 h, lt_top_iff_ne_top.2 (D.measure_norm_gt_ne_top one_pos)⟩)

/-! ## Symmetry, the origin, the equation -/

theorem ladderNuStar_zero {q : ℝ} (hq : 0 < q) {ν : Measure (Rd d)} (h0 : ν {0} = 0) :
    ladderNuStar q ν {0} = 0 := by
  rw [ladderNuStar, Measure.sum_apply _ (measurableSet_singleton 0)]
  refine ENNReal.tsum_eq_zero.2 fun m => ?_
  rw [Measure.map_apply (measurable_const_smul _) (measurableSet_singleton 0)]
  have e : (fun x : Rd d => (q ^ (-((m : ℤ) + 1))) • x) ⁻¹' {0} = {0} := by
    ext x
    simp [(zpow_pos hq _).ne']
  rw [e, h0]

theorem ladderNuStar_symm (q : ℝ) {ν : Measure (Rd d)} (hs : ν.map (fun x => -x) = ν) :
    (ladderNuStar q ν).map (fun x => -x) = ladderNuStar q ν := by
  rw [ladderNuStar, Measure.map_sum measurable_neg.aemeasurable]
  congr 1
  funext m
  rw [Measure.map_map measurable_neg (measurable_const_smul _)]
  have e : ((fun x : Rd d => -x) ∘ fun x => (q ^ (-((m : ℤ) + 1))) • x) =
      (fun x => (q ^ (-((m : ℤ) + 1))) • x) ∘ fun x => -x := by
    funext x
    simp [smul_neg]
  rw [e, ← Measure.map_map (measurable_const_smul _) measurable_neg, hs]

/-- **The data `(A_ϱ/(q² - 1), ν*)`** of `prop:ladder-knot-kernel`(1), given the moment. -/
noncomputable def ladderStarData {q : ℝ} (hq : 1 < q) (D : SymLevyData d)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂D.ν < ⊤) : SymLevyData d where
  A := (q ^ 2 - 1)⁻¹ • D.A
  ν := ladderNuStar q D.ν
  A_posSemidef := D.A_posSemidef.smul (inv_nonneg.2 (by nlinarith))
  ν_zero := ladderNuStar_zero (by linarith) D.ν_zero
  ν_integrable := ladderNuStar_levy hq D hmom
  ν_symm := ladderNuStar_symm q D.ν_symm

/-- **`D_q ν* = ν + ν*`**. -/
theorem map_ladderNuStar {q : ℝ} (hq : 0 < q) (ν : Measure (Rd d)) :
    (ladderNuStar q ν).map (fun x => q • x) = ν + ladderNuStar q ν := by
  rw [ladderNuStar, Measure.map_sum (measurable_const_smul _).aemeasurable]
  have hmm : ∀ m : ℕ, (ν.map fun x => (q ^ (-((m : ℤ) + 1))) • x).map (fun x => q • x) =
      ν.map fun x => (q ^ (-(m : ℤ))) • x := by
    intro m
    rw [Measure.map_map (measurable_const_smul _) (measurable_const_smul _)]
    congr 1
    funext x
    simp only [Function.comp_apply, smul_smul]
    congr 1
    rw [← zpow_one_add₀ hq.ne']
    ring_nf
  simp_rw [hmm]
  ext B hB
  rw [Measure.add_apply, Measure.sum_apply _ hB, Measure.sum_apply _ hB,
    tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, neg_zero, zpow_zero, one_smul, Measure.map_id', Nat.cast_add,
    Nat.cast_one, neg_add_rev]

/-- **The equation determines `ν*`.** If `ν{0} = 0`, `ν` is finite off every ball about `0`, and
`D_q ν = ν_ϱ + ν`, then `ν = ν*`. -/
theorem eq_ladderNuStar_of_map {q : ℝ} (hq : 1 < q) {ν νρ : Measure (Rd d)} (h0 : ν {0} = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤)
    (h : ν.map (fun x => q • x) = νρ + ν) : ν = ladderNuStar q νρ := by
  have hq0 : 0 < q := by linarith
  have hsm : ∀ c : ℝ, Measurable fun x : Rd d => c • x := fun c => measurable_const_smul c
  have hmm : ∀ (b c : ℝ) (m : Measure (Rd d)),
      (m.map (fun x => c • x)).map (fun x => b • x) = m.map (fun x => (b * c) • x) := by
    intro b c m
    rw [Measure.map_map (hsm b) (hsm c)]
    congr 1
    funext x
    simp [smul_smul]
  -- `ν = D_{q⁻¹} ν_ϱ + D_{q⁻¹} ν`
  have hinv : ν = νρ.map (fun x => q⁻¹ • x) + ν.map (fun x => q⁻¹ • x) := by
    have h2 := congrArg (fun m : Measure (Rd d) => m.map fun x => q⁻¹ • x) h
    simp only [hmm, inv_mul_cancel₀ hq0.ne', one_smul, Measure.map_id'] at h2
    exact h2.trans (Measure.map_add _ _ (hsm _))
  -- iterated
  have hiter : ∀ M : ℕ, ν = (∑ m ∈ Finset.range M, νρ.map fun x => (q ^ (-((m : ℤ) + 1))) • x) +
      ν.map fun x => (q ^ (-(M : ℤ))) • x := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      conv_lhs => rw [ih]
      conv_lhs => rw [hinv]
      rw [Measure.map_add _ _ (hsm _), hmm, hmm, Finset.sum_range_succ, add_assoc]
      have e : q ^ (-(M : ℤ)) * q⁻¹ = q ^ (-((M : ℤ) + 1)) := by
        rw [← zpow_neg_one, ← zpow_add₀ hq0.ne']
        ring_nf
      rw [e]
      push_cast
      rfl
  have hstar : ∀ B : Set (Rd d), MeasurableSet B →
      Tendsto (fun M : ℕ => (∑ m ∈ Finset.range M,
        νρ.map fun x => (q ^ (-((m : ℤ) + 1))) • x) B) atTop (𝓝 (ladderNuStar q νρ B)) := by
    intro B hB
    rw [ladderNuStar, Measure.sum_apply _ hB]
    simp only [Measure.coe_finsetSum, Finset.sum_apply]
    exact ENNReal.tendsto_nat_tsum _
  -- on a set bounded away from `0`
  have hfar : ∀ ε : ℝ, 0 < ε → ∀ B : Set (Rd d), MeasurableSet B → B ⊆ {x | ε < ‖x‖} →
      ν B = ladderNuStar q νρ B := by
    intro ε hε B hB hBε
    set T : ℕ → Set (Rd d) := fun M => {x | q ^ M * ε < ‖x‖} with hT
    have hTm : ∀ M, MeasurableSet (T M) := fun M =>
      measurableSet_lt measurable_const measurable_norm
    have hanti : Antitone T := by
      intro M N hMN x hx
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hq.le hMN) hε.le) hx
    have hempty : (⋂ M, T M) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (‖x‖ / ε) hq
      have := mem_iInter.1 hx M
      have h2 : ‖x‖ < q ^ M * ε := by rwa [div_lt_iff₀ hε] at hM
      exact lt_asymm h2 this
    have hlim : Tendsto (fun M => ν (T M)) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := ν) (fun M => (hTm M).nullMeasurableSet) hanti
        ⟨0, by simpa [hT] using hfin ε hε⟩
      rwa [hempty, measure_empty] at this
    have hsmall : ∀ M : ℕ, (ν.map fun x => (q ^ (-(M : ℤ))) • x) B ≤ ν (T M) := by
      intro M
      rw [Measure.map_apply (hsm _) hB]
      refine measure_mono fun x hx => ?_
      have hx' := hBε hx
      simp only [mem_setOf_eq, norm_smul, zpow_neg, zpow_natCast,
        Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg hq0.le M))] at hx'
      change q ^ M * ε < ‖x‖
      have hqM : 0 < q ^ M := pow_pos hq0 M
      rwa [inv_mul_eq_div, lt_div_iff₀ hqM, mul_comm] at hx'
    have hlim2 : Tendsto (fun M : ℕ => (ν.map fun x => (q ^ (-(M : ℤ))) • x) B) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
        hsmall
    have hsum := (hstar B hB).add hlim2
    rw [add_zero] at hsum
    have hconst : (fun M : ℕ => (∑ m ∈ Finset.range M,
        νρ.map fun x => (q ^ (-((m : ℤ) + 1))) • x) B +
        (ν.map fun x => (q ^ (-(M : ℤ))) • x) B) = fun _ => ν B := by
      funext M
      conv_rhs => rw [hiter M]
      rw [Measure.add_apply]
    rw [hconst] at hsum
    exact tendsto_nhds_unique tendsto_const_nhds hsum
  -- `ν*` has no mass at `0`
  have hρ0 : νρ {0} = 0 := by
    have h1 := congrArg (fun m : Measure (Rd d) => m {0}) h
    simp only [Measure.add_apply, Measure.map_apply (hsm q) (measurableSet_singleton 0)] at h1
    have e : (fun x : Rd d => q • x) ⁻¹' {0} = {0} := by
      ext x
      simp [hq0.ne']
    rw [e, h0] at h1
    exact (add_eq_zero.1 h1.symm).1
  have hs0 : ladderNuStar q νρ {0} = 0 := ladderNuStar_zero hq0 hρ0
  ext B hB
  set U : ℕ → Set (Rd d) := fun n => B ∩ {x | 1 / ((n : ℝ) + 1) < ‖x‖} with hU
  have hUm : Monotone U := by
    intro n m hnm x hx
    have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
    exact ⟨hx.1, show 1 / ((m : ℝ) + 1) < ‖x‖ from lt_of_le_of_lt h2 hx.2⟩
  have hUnion : (⋃ n, U n) = B \ {0} := by
    ext x
    simp only [hU, mem_iUnion, mem_inter_iff, mem_setOf_eq, Set.mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨n, hx, hn⟩
      refine ⟨hx, fun h => ?_⟩
      rw [h, norm_zero] at hn
      exact (not_lt.2 (by positivity)) hn
    · rintro ⟨hx, hx0⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.2 hx0)
      exact ⟨n, hx, hn⟩
  have hdiff : ∀ m : Measure (Rd d), m {0} = 0 → m B = m (B \ {0}) := fun m hm =>
    (measure_sdiff_null hm).symm
  rw [hdiff ν h0, hdiff _ hs0, ← hUnion]
  have h1 := tendsto_measure_iUnion_atTop (μ := ν) hUm
  have h2 := tendsto_measure_iUnion_atTop (μ := ladderNuStar q νρ) hUm
  have heq : (ν ∘ U) = (ladderNuStar q νρ ∘ U) := by
    funext n
    exact hfar (1 / ((n : ℝ) + 1)) (by positivity) (U n)
      (hB.inter (measurableSet_lt measurable_const measurable_norm)) inter_subset_right
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end Pyramids
