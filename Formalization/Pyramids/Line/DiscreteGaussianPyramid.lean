/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.LatticeLine
import Pyramids.Line.NoLatticeKernelLine
import Pyramids.Pyramid.StratumTwoExample

/-!
# `prop:discrete-gaussian-pyramid`: the discrete-Gaussian pyramid lies strictly in stratum 2

Blueprint: `blueprint/src/parts/02-line.tex`, `prop:discrete-gaussian-pyramid`. Wave 3e: the three
declarations moved here from `PyramidsSkeleton.Ch02Line`, their statements unchanged.

## The route

Directly on the line, through `thm:lattice-line`, rather than through `lem:synthesis` at `d = 1`.

* **The pairs.** `(0, ϖ_t)` is a folded pair (`dgPair`): `ϖ_t` is carried by the points `hq^j`,
  and `∫ min(1, v²) ϖ_t(dv) ≤ ∑ᵢ w_{i-1} min(1, (hqⁿqⁱ)²) < ∞`. Its exponent is `Ψ_t`, the
  series converging since `1 - cos x ≤ 2 min(x², 1)`.
* **Monotone and distinct.** On the atom `hq^j` the measure `ϖ_t` has the weight
  `W_t(j) = w_{j-n}(η)`, `t = q^{n+η}`, which is nondecreasing in `t` (within an octave by the
  phase, across octaves by `w_i(η) ≤ w_{i-1} ≤ w_{i-1+k}(η')`), and strictly increasing somewhere
  between any two scales (at a step `w_{i₀} < w_{i₀-1}` of the weights).
* **Continuity.** On the closed octave `[qⁿ, q^{n+1}]`, `Ψ_t(ω) = (1 - η)gₙ + η g_{n+1}` with
  `η = log_q t - n` and `gₙ := ∑ᵢ wᵢ(1 - cos(hq^{i+n}ω))`; `gₙ → 0` as `n → -∞` by dominated
  convergence, which gives the continuity at `0`.
* **(1).** `thm:lattice-line`(1)'s converse gives a family with these folded data, and any laws
  with the transforms are its kernels. `Ψ_{qt}(ω) = Ψ_t(qω)`, so `lem:discrete-covariance-line`
  gives (A8 at `q^ℤ`) in the canonical gauge and `T_q ϖ_t ≥ ϖ_t`.
* **(2).** Covariance of a relabelled family gives full covariance of the family itself
  (conjugating by the gauge), and then `thm:lattice-line`(3) makes some `ϖ_u`, `u > 0`, absolutely
  continuous; but `ϖ_u` has an atom.
* **(3).** `prop:no-lattice-kernel-line`(1).
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X CascadeCore IsScaleCovariant IsKernelFamily IsSymmetric SymLevyPair SDProfile
  profileMeasure)
open scoped Topology ENNReal

/-- **The hypotheses on the weights** of `prop:discrete-gaussian-pyramid`. -/
structure IsDGWeights (q : ℝ) (w : ℤ → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  anti : Antitone w
  ne : ∃ i, w i ≠ 0
  neg : Summable fun i : {i : ℤ // i < 0} => w i * q ^ (2 * (i : ℤ))
  pos : Summable fun i : {i : ℤ // 0 ≤ i} => w i

/-! ## Octave arithmetic -/

theorem dgPhase_mem (q t : ℝ) : dgPhase q t ∈ Ico (0 : ℝ) 1 := by
  unfold dgPhase
  rw [Int.self_sub_floor]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem dgPhase_mem_Icc (q t : ℝ) : dgPhase q t ∈ Icc (0 : ℝ) 1 :=
  Ico_subset_Icc_self (dgPhase_mem q t)

theorem logb_zpow_self {q : ℝ} (hq : 1 < q) (k : ℤ) : Real.logb q (q ^ k) = k := by
  rw [← Real.rpow_intCast, Real.logb_rpow (by linarith) (by linarith)]

theorem dgLevel_mul {q : ℝ} (hq : 1 < q) {t : ℝ} (ht : 0 < t) :
    dgLevel q (q * t) = dgLevel q t + 1 ∧ dgPhase q (q * t) = dgPhase q t := by
  have hq0 : 0 < q := by linarith
  have hl : Real.logb q (q * t) = Real.logb q t + 1 := by
    rw [Real.logb_mul hq0.ne' ht.ne', Real.logb_self_eq_one hq, add_comm]
  have hf : dgLevel q (q * t) = dgLevel q t + 1 := by
    unfold dgLevel
    rw [hl, Int.floor_add_one]
  refine ⟨hf, ?_⟩
  unfold dgPhase
  rw [hl, Int.floor_add_one]
  push_cast
  ring

/-! ## The weights -/

theorem dgWeight_ge {w : ℤ → ℝ} (hwanti : Antitone w) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (i : ℤ) :
    w i ≤ dgWeight w θ i := by
  unfold dgWeight
  have h1 : w i ≤ w (i - 1) := hwanti (by omega)
  nlinarith [hθ.1, hθ.2]

/-- Some step of the weights is strict. -/
theorem IsDGWeights.exists_step {q : ℝ} {w : ℤ → ℝ} (hw : IsDGWeights q w) :
    ∃ i, w i < w (i - 1) := by
  by_contra hcon
  push Not at hcon
  have hconst : ∀ i : ℤ, w i = w 0 := by
    have hstep : ∀ i : ℤ, w (i - 1) = w i := fun i =>
      le_antisymm (hcon i) (hw.anti (by omega))
    intro i
    induction i using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [← ih, ← hstep ((n : ℤ) + 1), add_sub_cancel_right]
    | pred n ih => rw [← ih, hstep (-(n : ℤ))]
  obtain ⟨i, hi⟩ := hw.ne
  haveI : Infinite {i : ℤ // 0 ≤ i} := Infinite.of_injective
    (fun n : ℕ => (⟨n, Int.natCast_nonneg n⟩ : {i : ℤ // 0 ≤ i}))
    (fun a b hab => by simpa using hab)
  have hz : w 0 = 0 := by
    have h' : Summable fun _ : {i : ℤ // 0 ≤ i} => w 0 := hw.pos.congr fun j => hconst j
    exact (summable_const_iff (w 0)).1 h'
  exact hi (by rw [hconst i, hz])

theorem one_sub_cos_le_two_min_sq (x : ℝ) : 1 - Real.cos x ≤ 2 * min (x ^ 2) 1 := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := Real.neg_one_le_cos x
  rcases le_total (x ^ 2) 1 with h | h
  · rw [min_eq_left h]; nlinarith [sq_nonneg x]
  · rw [min_eq_right h]; linarith

/-- The series of the exponent converges, at every phase and level. -/
theorem IsDGWeights.summable {q : ℝ} (hq : 1 < q) {w : ℤ → ℝ} (hw : IsDGWeights q w) (h : ℝ)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (n : ℤ) (ω : ℝ) :
    Summable fun i : ℤ => dgWeight w θ i * (1 - Real.cos (h * q ^ (i + n) * ω)) := by
  have hq0 : 0 < q := by linarith
  have hS := (train_summable (h := h * q ^ n * ω) hq w hw.nonneg hw.neg hw.pos).mul_left 2
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (dgWeight_nonneg hw.nonneg hθ i)
    (by linarith [Real.cos_le_one (h * q ^ (i + n) * ω)])) (fun i => ?_) hS
  have he : h * q ^ (i + n) * ω = h * q ^ n * ω * q ^ i := by
    rw [zpow_add₀ hq0.ne']; ring
  rw [he]
  calc dgWeight w θ i * (1 - Real.cos (h * q ^ n * ω * q ^ i))
      ≤ w (i - 1) * (2 * min ((h * q ^ n * ω * q ^ i) ^ 2) 1) :=
        mul_le_mul (dgWeight_le hw.anti hθ i) (one_sub_cos_le_two_min_sq _)
          (by linarith [Real.cos_le_one (h * q ^ n * ω * q ^ i)]) (hw.nonneg _)
    _ = 2 * (w (i - 1) * min ((h * q ^ n * ω * q ^ i) ^ 2) 1) := by ring

/-! ## The folded pairs `(0, ϖ_t)` -/

theorem dgLevyMeasure_of_nonpos (q h : ℝ) (w : ℤ → ℝ) {t : ℝ} (ht : t ≤ 0) :
    dgLevyMeasure q h w t = 0 := by
  rw [dgLevyMeasure, if_pos ht]

theorem lintegral_dgLevyMeasure (q h : ℝ) (w : ℤ → ℝ) {t : ℝ} (ht : 0 < t) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂dgLevyMeasure q h w t =
      ∑' i, ENNReal.ofReal (dgWeight w (dgPhase q t) i) * f (h * q ^ (i + dgLevel q t)) := by
  rw [dgLevyMeasure, if_neg (not_le.2 ht), lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem dgLevyMeasure_folded {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ) (t : ℝ) :
    ScaleSpace.IsFolded (dgLevyMeasure q h w t) := by
  unfold ScaleSpace.IsFolded
  rcases le_or_gt t 0 with ht | ht
  · rw [dgLevyMeasure_of_nonpos q h w ht]; rfl
  · rw [dgLevyMeasure, if_neg (not_le.2 ht), Measure.sum_apply _ measurableSet_Iic]
    refine ENNReal.tsum_eq_zero.2 fun i => ?_
    have hp : 0 < h * q ^ (i + dgLevel q t) := mul_pos hh (zpow_pos (by linarith) _)
    rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iic,
      indicator_of_notMem (by simpa using hp), smul_zero]

theorem dgLevyMeasure_integrable {q h : ℝ} (hq : 1 < q) {w : ℤ → ℝ}
    (hw : IsDGWeights q w) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂dgLevyMeasure q h w t ≠ ⊤ := by
  have hq0 : 0 < q := by linarith
  rcases le_or_gt t 0 with ht | ht
  · rw [dgLevyMeasure_of_nonpos q h w ht]; simp
  rw [lintegral_dgLevyMeasure q h w ht]
  set n := dgLevel q t
  set θ := dgPhase q t
  have hθ := dgPhase_mem_Icc q t
  have hS := train_summable (h := h * q ^ n) hq w hw.nonneg hw.neg hw.pos
  have hnn : ∀ i : ℤ, 0 ≤ w (i - 1) * min ((h * q ^ n * q ^ i) ^ 2) 1 :=
    fun i => mul_nonneg (hw.nonneg _) (le_min (sq_nonneg _) zero_le_one)
  refine ne_top_of_le_ne_top
    (ENNReal.ofReal_ne_top (r := ∑' i, w (i - 1) * min ((h * q ^ n * q ^ i) ^ 2) 1)) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg hnn hS]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← ENNReal.ofReal_mul (dgWeight_nonneg hw.nonneg hθ i)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul (dgWeight_le hw.anti hθ i) ?_
    (le_min zero_le_one (sq_nonneg _)) (hw.nonneg _))
  rw [min_comm, zpow_add₀ hq0.ne', ← mul_assoc, mul_right_comm h]

/-- **The folded pair `(0, ϖ_t)`.** -/
noncomputable def dgPair {q h : ℝ} (hq : 1 < q) (hh : 0 < h) {w : ℤ → ℝ}
    (hw : IsDGWeights q w) (t : ℝ) : SymLevyPair where
  a := 0
  ν := dgLevyMeasure q h w t
  a_nonneg := le_rfl
  ν_folded := dgLevyMeasure_folded hq hh w t
  ν_integrable := dgLevyMeasure_integrable hq hw t

theorem dgPair_a {q h : ℝ} (hq : 1 < q) (hh : 0 < h) {w : ℤ → ℝ} (hw : IsDGWeights q w) (t : ℝ) :
    (dgPair hq hh hw t).a = 0 := rfl

theorem dgPair_ν {q h : ℝ} (hq : 1 < q) (hh : 0 < h) {w : ℤ → ℝ} (hw : IsDGWeights q w) (t : ℝ) :
    (dgPair hq hh hw t).ν = dgLevyMeasure q h w t := rfl

/-- The exponent of `(0, ϖ_t)` is `Ψ_t`. -/
theorem dgPair_exponent {q h : ℝ} (hq : 1 < q) (hh : 0 < h) {w : ℤ → ℝ}
    (hw : IsDGWeights q w) (t ω : ℝ) : (dgPair hq hh hw t).exponent ω = dgExponent q h w t ω := by
  simp only [SymLevyPair.exponent, SymLevyPair.exponentL, dgPair, zero_mul, ENNReal.ofReal_zero,
    zero_add]
  rcases le_or_gt t 0 with ht | ht
  · rw [dgLevyMeasure_of_nonpos q h w ht, dgExponent, if_pos ht]; simp
  rw [lintegral_dgLevyMeasure q h w ht, dgExponent, if_neg (not_le.2 ht)]
  have hθ := dgPhase_mem_Icc q t
  have hnn : ∀ i : ℤ, 0 ≤ dgWeight w (dgPhase q t) i *
      (1 - Real.cos (h * q ^ (i + dgLevel q t) * ω)) := fun i =>
    mul_nonneg (dgWeight_nonneg hw.nonneg hθ i)
      (by linarith [Real.cos_le_one (h * q ^ (i + dgLevel q t) * ω)])
  have hS := hw.summable hq h hθ (dgLevel q t) ω
  rw [← ENNReal.toReal_ofReal (tsum_nonneg hnn), ENNReal.ofReal_tsum_of_nonneg hnn hS]
  congr 1
  refine tsum_congr fun i => ?_
  rw [ENNReal.ofReal_mul (dgWeight_nonneg hw.nonneg hθ i), mul_comm ω]

/-! ## The weights on the atoms -/

/-- **The weight of `ϖ_t` on the atom `hq^j`**, `W_t(j) = w_{j-n}(η)`. -/
noncomputable def dgAtomWeight (q : ℝ) (w : ℤ → ℝ) (t : ℝ) (j : ℤ) : ℝ :=
  dgWeight w (dgPhase q t) (j - dgLevel q t)

theorem dgLevyMeasure_atom {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ) {t : ℝ} (ht : 0 < t)
    (j : ℤ) : dgLevyMeasure q h w t {h * q ^ j} = ENNReal.ofReal (dgAtomWeight q w t j) := by
  rw [dgLevyMeasure, if_neg (not_le.2 ht), Measure.sum_apply _ (measurableSet_singleton _)]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_single (j - dgLevel q t)]
  · rw [sub_add_cancel, Measure.dirac_apply' _ (measurableSet_singleton _),
      indicator_of_mem (mem_singleton _), Pi.one_apply, mul_one, dgAtomWeight]
  · intro i hi
    rw [Measure.dirac_apply' _ (measurableSet_singleton _), indicator_of_notMem, mul_zero]
    intro hmem
    have := radius_injective hq hh (mem_singleton_iff.1 hmem)
    exact hi (by omega)

theorem dgLevyMeasure_eq_sum (q h : ℝ) (w : ℤ → ℝ) {t : ℝ} (ht : 0 < t) :
    dgLevyMeasure q h w t =
      Measure.sum fun j : ℤ =>
        ENNReal.ofReal (dgAtomWeight q w t j) • Measure.dirac (h * q ^ j) := by
  rw [dgLevyMeasure, if_neg (not_le.2 ht)]
  conv_rhs => rw [← Measure.sum_comp_equiv (Equiv.addRight (dgLevel q t))]
  congr 1
  funext i
  simp [dgAtomWeight]

/-- The weights on the atoms are nondecreasing in the scale. -/
theorem dgAtomWeight_mono {q : ℝ} (hq : 1 < q) {w : ℤ → ℝ} (hw : IsDGWeights q w) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (j : ℤ) : dgAtomWeight q w s j ≤ dgAtomWeight q w t j := by
  have hlog : Real.logb q s ≤ Real.logb q t := Real.logb_le_logb_of_le hq hs hst
  have hn : dgLevel q s ≤ dgLevel q t := Int.floor_mono hlog
  unfold dgAtomWeight
  rcases hn.eq_or_lt with he | hlt
  · rw [he]
    refine dgWeight_mono hw.anti ?_ _
    unfold dgPhase
    have : (⌊Real.logb q s⌋ : ℝ) = ⌊Real.logb q t⌋ := by exact_mod_cast he
    linarith
  · calc dgWeight w (dgPhase q s) (j - dgLevel q s)
        ≤ w (j - dgLevel q s - 1) := dgWeight_le hw.anti (dgPhase_mem_Icc q s) _
      _ ≤ w (j - dgLevel q t) := hw.anti (by omega)
      _ ≤ dgWeight w (dgPhase q t) (j - dgLevel q t) := dgWeight_ge hw.anti (dgPhase_mem_Icc q t) _

/-- Between two scales some atom weight increases strictly. -/
theorem dgAtomWeight_strict {q : ℝ} (hq : 1 < q) {w : ℤ → ℝ} (hw : IsDGWeights q w) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) : ∃ j, dgAtomWeight q w s j < dgAtomWeight q w t j := by
  obtain ⟨i₀, hi₀⟩ := hw.exists_step
  have hlog : Real.logb q s < Real.logb q t := Real.logb_lt_logb hq hs hst
  have hn : dgLevel q s ≤ dgLevel q t := Int.floor_mono hlog.le
  refine ⟨i₀ + dgLevel q s, ?_⟩
  unfold dgAtomWeight
  rcases hn.eq_or_lt with he | hlt
  · rw [← he, add_sub_cancel_right]
    have hη : dgPhase q s < dgPhase q t := by
      unfold dgPhase
      have : (⌊Real.logb q s⌋ : ℝ) = ⌊Real.logb q t⌋ := by exact_mod_cast he
      linarith
    unfold dgWeight
    nlinarith
  · have hη := dgPhase_mem q s
    calc dgWeight w (dgPhase q s) (i₀ + dgLevel q s - dgLevel q s)
        < w (i₀ - 1) := by
          rw [add_sub_cancel_right]
          unfold dgWeight
          nlinarith [hη.1, hη.2]
      _ ≤ w (i₀ + dgLevel q s - dgLevel q t) := hw.anti (by omega)
      _ ≤ dgWeight w (dgPhase q t) (i₀ + dgLevel q s - dgLevel q t) :=
          dgWeight_ge hw.anti (dgPhase_mem_Icc q t) _

/-- `ϖ_t ≠ 0` for `t > 0`: it has a positive atom. -/
theorem dgAtomWeight_pos {q : ℝ} {w : ℤ → ℝ} (hw : IsDGWeights q w) (t : ℝ) :
    ∃ j, 0 < dgAtomWeight q w t j := by
  obtain ⟨i, hi⟩ := hw.ne
  refine ⟨i + dgLevel q t, ?_⟩
  unfold dgAtomWeight
  rw [add_sub_cancel_right]
  exact lt_of_lt_of_le (lt_of_le_of_ne (hw.nonneg i) (Ne.symm hi))
    (dgWeight_ge hw.anti (dgPhase_mem_Icc q t) i)

theorem dgLevyMeasure_mono {q h : ℝ} (hq : 1 < q) {w : ℤ → ℝ} (hw : IsDGWeights q w) {s t : ℝ}
    (hst : s ≤ t) : dgLevyMeasure q h w s ≤ dgLevyMeasure q h w t := by
  rcases le_or_gt s 0 with hs | hs
  · rw [dgLevyMeasure_of_nonpos q h w hs]; exact Measure.zero_le _
  rw [dgLevyMeasure_eq_sum q h w hs, dgLevyMeasure_eq_sum q h w (hs.trans_le hst), Measure.le_iff]
  intro A hA
  rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
  refine ENNReal.tsum_le_tsum fun j => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  exact dgAtomWeight_mono hq hw hs hst j

theorem dgLevyMeasure_ne {q h : ℝ} (hq : 1 < q) (hh : 0 < h) {w : ℤ → ℝ} (hw : IsDGWeights q w)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) : dgLevyMeasure q h w s ≠ dgLevyMeasure q h w t := by
  have ht : 0 < t := hs.trans_lt hst
  intro heq
  rcases hs.eq_or_lt with h0 | hs0
  · subst h0
    obtain ⟨j, hj⟩ := dgAtomWeight_pos hw t
    have h1 := congrArg (fun m => m {h * q ^ j}) heq
    simp only [dgLevyMeasure_of_nonpos q h w le_rfl, dgLevyMeasure_atom hq hh w ht,
      Measure.coe_zero, Pi.zero_apply] at h1
    exact (ENNReal.ofReal_pos.2 hj).ne h1
  · obtain ⟨j, hj⟩ := dgAtomWeight_strict hq hw hs0 hst
    have h1 := congrArg (fun m => m {h * q ^ j}) heq
    simp only [dgLevyMeasure_atom hq hh w hs0, dgLevyMeasure_atom hq hh w ht] at h1
    have h0 : 0 ≤ dgAtomWeight q w s j :=
      dgWeight_nonneg hw.nonneg (dgPhase_mem_Icc q s) _
    exact hj.ne ((ENNReal.ofReal_eq_ofReal_iff h0 (h0.trans hj.le)).1 h1)

/-! ## The exponent along the scales -/

/-- `Ψ_{qt}(ω) = Ψ_t(qω)`. -/
theorem dgExponent_mul {q : ℝ} (hq : 1 < q) (h : ℝ) (w : ℤ → ℝ) (t ω : ℝ) :
    dgExponent q h w (q * t) ω = dgExponent q h w t (q * ω) := by
  have hq0 : 0 < q := by linarith
  rcases le_or_gt t 0 with ht | ht
  · rw [dgExponent, dgExponent, if_pos (mul_nonpos_of_nonneg_of_nonpos hq0.le ht), if_pos ht]
  have hqt : 0 < q * t := mul_pos hq0 ht
  obtain ⟨hlev, hph⟩ := dgLevel_mul hq ht
  rw [dgExponent, dgExponent, if_neg (not_le.2 hqt), if_neg (not_le.2 ht), hlev, hph]
  refine tsum_congr fun i => ?_
  rw [show i + (dgLevel q t + 1) = (i + dgLevel q t) + 1 by ring, zpow_add_one₀ hq0.ne']
  ring_nf

/-- `gₙ := ∑ᵢ wᵢ(1 - cos(hq^{i+n}ω))`, the exponent at the knot `qⁿ`. -/
noncomputable def dgKnotExponent (q h : ℝ) (w : ℤ → ℝ) (ω : ℝ) (n : ℤ) : ℝ :=
  ∑' i : ℤ, w i * (1 - Real.cos (h * q ^ (i + n) * ω))

theorem dgKnotExponent_nonneg {q h : ℝ} {w : ℤ → ℝ} (hw0 : ∀ i, 0 ≤ w i) (ω : ℝ) (n : ℤ) :
    0 ≤ dgKnotExponent q h w ω n :=
  tsum_nonneg fun i => mul_nonneg (hw0 i) (by linarith [Real.cos_le_one (h * q ^ (i + n) * ω)])

/-- **On a closed octave** `[qⁿ, q^{n+1}]`, `Ψ_t(ω) = (1 - η)gₙ + η g_{n+1}`, `η = log_q t - n`. -/
theorem dgExponent_octave {q : ℝ} (hq : 1 < q) {w : ℤ → ℝ} (hw : IsDGWeights q w) (h : ℝ)
    (n : ℤ) {t : ℝ} (ht : t ∈ Icc (q ^ n) (q ^ (n + 1))) (ω : ℝ) :
    dgExponent q h w t ω = (1 - (Real.logb q t - n)) * dgKnotExponent q h w ω n +
      (Real.logb q t - n) * dgKnotExponent q h w ω (n + 1) := by
  have hq0 : 0 < q := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (zpow_pos hq0 n) ht.1
  have hw0 : ∀ i, dgWeight w 0 i = w i := fun i => by simp [dgWeight]
  have hw1 : ∀ i, dgWeight w 1 i = w (i - 1) := fun i => by simp [dgWeight]
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rw [dgExponent, if_neg (not_le.2 ht0)]
  rcases ht.2.lt_or_eq with hlt | heq
  · have hlev : dgLevel q t = n := dgLevel_eq hq ht.1 hlt
    have hph : dgPhase q t = Real.logb q t - n := by
      have e : ⌊Real.logb q t⌋ = n := hlev
      unfold dgPhase
      rw [e]
    rw [hlev, hph]
    set η := Real.logb q t - n
    have hA := hw.summable hq h h0I n ω
    have hB := hw.summable hq h h1I n ω
    simp only [hw0, hw1] at hA hB
    have hshift : ∑' i : ℤ, w (i - 1) * (1 - Real.cos (h * q ^ (i + n) * ω)) =
        dgKnotExponent q h w ω (n + 1) := by
      rw [dgKnotExponent, ← (Equiv.addRight (1 : ℤ)).tsum_eq]
      refine tsum_congr fun i => ?_
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
      rw [show i + 1 + n = i + (n + 1) by ring]
    calc ∑' i : ℤ, dgWeight w η i * (1 - Real.cos (h * q ^ (i + n) * ω))
        = ∑' i : ℤ, ((1 - η) * (w i * (1 - Real.cos (h * q ^ (i + n) * ω))) +
            η * (w (i - 1) * (1 - Real.cos (h * q ^ (i + n) * ω)))) :=
          tsum_congr fun i => by unfold dgWeight; ring
      _ = (1 - η) * dgKnotExponent q h w ω n + η * dgKnotExponent q h w ω (n + 1) := by
          rw [Summable.tsum_add (hA.mul_left _) (hB.mul_left _), tsum_mul_left, tsum_mul_left,
            hshift]
          rfl
  · have hlev : dgLevel q t = n + 1 := by
      refine dgLevel_eq hq heq.symm.le ?_
      rw [heq]
      exact zpow_lt_zpow_right₀ hq (by omega)
    have hlog : Real.logb q t = (n : ℝ) + 1 := by
      rw [heq, logb_zpow_self hq]; push_cast; ring
    have hph : dgPhase q t = 0 := by
      have e : ⌊Real.logb q t⌋ = n + 1 := hlev
      unfold dgPhase
      rw [e, hlog]; push_cast; ring
    rw [hlev, hph, hlog]
    simp only [hw0, add_sub_cancel_left, sub_self, zero_mul, one_mul, zero_add]
    rfl

theorem summable_knot_bound {q : ℝ} (hq : 1 < q) {w : ℤ → ℝ} (hw : IsDGWeights q w) (h ω : ℝ) :
    Summable fun i : ℤ => 2 * (w (i - 1) * min ((h * ω * q ^ i) ^ 2) 1) :=
  (train_summable (h := h * ω) hq w hw.nonneg hw.neg hw.pos).mul_left 2

/-- `gₙ → 0` as `n → -∞`, by dominated convergence. -/
theorem tendsto_dgKnotExponent {q : ℝ} (hq : 1 < q) {w : ℤ → ℝ} (hw : IsDGWeights q w) (h ω : ℝ) :
    Tendsto (dgKnotExponent q h w ω) atBot (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hpow : Tendsto (fun k : ℤ => q ^ k) atBot (𝓝 0) := by
    have h1 : Tendsto (fun k : ℤ => (k : ℝ) * Real.log q) atBot atBot :=
      (tendsto_intCast_atBot_iff.2 tendsto_id).atBot_mul_const (Real.log_pos hq)
    refine (Real.tendsto_exp_atBot.comp h1).congr fun k => ?_
    rw [Function.comp_apply, ← Real.rpow_intCast, Real.rpow_def_of_pos hq0, mul_comm]
  -- `G(c) := ∑ᵢ wᵢ(1 - cos(hqⁱcω))` is continuous on `[-1, 1]`
  set G : ℝ → ℝ := fun c => ∑' i : ℤ, w i * (1 - Real.cos (h * q ^ i * c * ω)) with hG
  have hGc : ContinuousOn G (Icc (-1) 1) := by
    refine continuousOn_tsum (fun i => by fun_prop) (summable_knot_bound hq hw h ω) ?_
    intro i c hc
    have hc1 := Real.cos_le_one (h * q ^ i * c * ω)
    rw [Real.norm_of_nonneg (mul_nonneg (hw.nonneg i) (by linarith))]
    have hsq : (h * q ^ i * c * ω) ^ 2 ≤ (h * ω * q ^ i) ^ 2 := by
      have e : (h * q ^ i * c * ω) ^ 2 = (h * ω * q ^ i) ^ 2 * c ^ 2 := by ring
      have hc2 : c ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
      rw [e]
      nlinarith [sq_nonneg (h * ω * q ^ i)]
    calc w i * (1 - Real.cos (h * q ^ i * c * ω))
        ≤ w (i - 1) * (2 * min ((h * ω * q ^ i) ^ 2) 1) :=
          mul_le_mul (hw.anti (by omega)) ((one_sub_cos_le_two_min_sq _).trans
            (by gcongr)) (by linarith) (hw.nonneg _)
      _ = 2 * (w (i - 1) * min ((h * ω * q ^ i) ^ 2) 1) := by ring
  have hG0 : G 0 = 0 := by simp [hG]
  have hmem : ∀ᶠ k : ℤ in atBot, q ^ k ∈ Icc (-1 : ℝ) 1 :=
    (eventually_le_atBot (0 : ℤ)).mono fun k hk =>
      ⟨by linarith [zpow_pos hq0 k], zpow_le_one_of_nonpos₀ hq.le hk⟩
  have hlim := (hGc.continuousWithinAt ⟨by norm_num, by norm_num⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hpow, hmem⟩)
  rw [hG0] at hlim
  refine hlim.congr fun k => ?_
  simp only [Function.comp_apply, hG, dgKnotExponent]
  refine tsum_congr fun i => ?_
  rw [zpow_add₀ hq0.ne']
  ring_nf

/-- **`t ↦ Ψ_t(ω)` is continuous on `[0,∞)`.** -/
theorem dgExponent_continuousOn {q : ℝ} (hq : 1 < q) {w : ℤ → ℝ} (hw : IsDGWeights q w) (h ω : ℝ) :
    ContinuousOn (fun t => dgExponent q h w t ω) (Ici 0) := by
  have hq0 : 0 < q := by linarith
  have hoct : ∀ n : ℤ,
      ContinuousOn (fun t => dgExponent q h w t ω) (Icc (q ^ n) (q ^ (n + 1))) := by
    intro n
    have hl : ContinuousOn (Real.logb q) (Icc (q ^ n) (q ^ (n + 1))) :=
      Real.continuousOn_logb.mono fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]
        exact (lt_of_lt_of_le (zpow_pos hq0 n) ht.1).ne'
    have hc : ContinuousOn (fun t => (1 - (Real.logb q t - n)) * dgKnotExponent q h w ω n +
        (Real.logb q t - n) * dgKnotExponent q h w ω (n + 1)) (Icc (q ^ n) (q ^ (n + 1))) :=
      ((continuousOn_const.sub (hl.sub continuousOn_const)).mul continuousOn_const).add
        ((hl.sub continuousOn_const).mul continuousOn_const)
    exact hc.congr fun t ht => dgExponent_octave hq hw h n ht ω
  intro t ht
  rcases (mem_Ici.1 ht).eq_or_lt with h0 | h0
  · -- at `0`
    subst h0
    have hz : dgExponent q h w 0 ω = 0 := by rw [dgExponent, if_pos le_rfl]
    rw [ContinuousWithinAt, hz, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨M, hM⟩ := eventually_atBot.1
      ((Metric.tendsto_nhds.1 (tendsto_dgKnotExponent hq hw h ω)) ε hε)
    refine ⟨q ^ M, zpow_pos hq0 M, fun t ht htd => ?_⟩
    have ht0 : 0 ≤ t := ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0] at htd
    rw [Real.dist_eq, sub_zero]
    rcases ht0.eq_or_lt with e | ht0
    · rw [← e, hz, abs_zero]; exact hε
    obtain ⟨h1, h2⟩ := dgLevel_spec hq ht0
    set n := dgLevel q t
    have hnM : n < M := (zpow_lt_zpow_iff_right₀ hq).1 (lt_of_le_of_lt h1 htd)
    have hmem : t ∈ Icc (q ^ n) (q ^ (n + 1)) := ⟨h1, h2.le⟩
    rw [dgExponent_octave hq hw h n hmem ω]
    have hη : Real.logb q t - n ∈ Icc (0 : ℝ) 1 := by
      have hpos := dgPhase_mem_Icc q t
      exact hpos
    have hg1 := hM n hnM.le
    have hg2 := hM (n + 1) (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (dgKnotExponent_nonneg hw.nonneg ω _)] at hg1 hg2
    have hn1 := dgKnotExponent_nonneg (q := q) (h := h) hw.nonneg ω n
    have hn2 := dgKnotExponent_nonneg (q := q) (h := h) hw.nonneg ω (n + 1)
    have e1 : (1 - (Real.logb q t - n)) * dgKnotExponent q h w ω n ≤
        (1 - (Real.logb q t - n)) *
          max (dgKnotExponent q h w ω n) (dgKnotExponent q h w ω (n + 1)) :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [hη.2])
    have e2 : (Real.logb q t - n) * dgKnotExponent q h w ω (n + 1) ≤
        (Real.logb q t - n) * max (dgKnotExponent q h w ω n) (dgKnotExponent q h w ω (n + 1)) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hη.1
    have hmax := max_lt hg1 hg2
    rw [abs_of_nonneg (add_nonneg (mul_nonneg (by linarith [hη.2]) hn1) (mul_nonneg hη.1 hn2))]
    linarith
  · -- at `t > 0`: the two closed octaves about `t`
    obtain ⟨h1, h2⟩ := dgLevel_spec hq h0
    set n := dgLevel q t
    have hU : ContinuousOn (fun t => dgExponent q h w t ω) (Icc (q ^ (n - 1)) (q ^ (n + 1))) := by
      have e : Icc (q ^ (n - 1)) (q ^ (n + 1)) =
          Icc (q ^ (n - 1)) (q ^ (n - 1 + 1)) ∪ Icc (q ^ n) (q ^ (n + 1)) := by
        rw [sub_add_cancel, Icc_union_Icc_eq_Icc]
        · exact zpow_le_zpow_right₀ hq.le (by omega)
        · exact zpow_le_zpow_right₀ hq.le (by omega)
      rw [e]
      exact (hoct (n - 1)).union_of_isClosed (hoct n) isClosed_Icc isClosed_Icc
    have hlt : q ^ (n - 1) < t := lt_of_lt_of_le (zpow_lt_zpow_right₀ hq (by omega)) h1
    exact (hU.continuousAt (Icc_mem_nhds hlt h2)).continuousWithinAt

/-! ## The family -/

/-- **The family of the discrete-Gaussian pyramid**: one `CascadeCore` whose kernels are any laws
with the transforms, with the folded data `(0, ϖ_t)`; and such laws exist. -/
theorem dg_family {q h : ℝ} (hq : 1 < q) (hh : 0 < h) {w : ℤ → ℝ} (hw : IsDGWeights q w) :
    (∃ μ : ℝ → ℝ → Measure ℝ, IsDGKernels q h w μ) ∧
      ∃ C : CascadeCore, ∀ μ : ℝ → ℝ → Measure ℝ, IsDGKernels q h w μ →
        IsKernelFamily C.Φ μ ∧ ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (dgPair hq hh hw t) := by
  have hPexp : ∀ t ω, (dgPair hq hh hw t).exponent ω = dgExponent q h w t ω :=
    dgPair_exponent hq hh hw
  have h0ν : (dgPair hq hh hw 0).ν = 0 := by
    rw [dgPair_ν]; exact dgLevyMeasure_of_nonpos q h w le_rfl
  have hmono : ∀ s t : ℝ, 0 ≤ s → s < t →
      (dgPair hq hh hw s).a ≤ (dgPair hq hh hw t).a ∧
        (dgPair hq hh hw s).ν ≤ (dgPair hq hh hw t).ν ∧
        ((dgPair hq hh hw s).a, (dgPair hq hh hw s).ν) ≠
          ((dgPair hq hh hw t).a, (dgPair hq hh hw t).ν) := by
    intro s t hs hst
    rw [dgPair_a, dgPair_a, dgPair_ν, dgPair_ν]
    exact ⟨le_rfl, dgLevyMeasure_mono hq hw hst.le,
      fun he => dgLevyMeasure_ne hq hh hw hs hst (Prod.mk.inj he).2⟩
  have hcont : ∀ ω : ℝ, ContinuousOn (fun t => (dgPair hq hh hw t).exponent ω) (Ici 0) :=
    fun ω => (dgExponent_continuousOn hq hw h ω).congr fun t _ => hPexp t ω
  obtain ⟨C, μ₀, hC, hP₀⟩ := lattice_line_1_converse (dgPair hq hh hw) (dgPair_a hq hh hw 0) h0ν
    hmono hcont
  have hfam₀ := line_axioms_kernels_1_family C μ₀ hC
  have hDG₀ : IsDGKernels q h w μ₀ := fun s t hs hst =>
    ⟨hC.isProbability s t hs hst, fun ω => by
      rw [charFun_step_of_folded hfam₀.1 hP₀ hs hst, hPexp, hPexp]⟩
  have heq : ∀ μ : ℝ → ℝ → Measure ℝ, IsDGKernels q h w μ →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ₀ s t := by
    intro μ hμ s t hs hst
    haveI := (hμ s t hs hst).1
    haveI := (hDG₀ s t hs hst).1
    exact Measure.ext_of_charFun (funext fun ω => by rw [(hμ s t hs hst).2, (hDG₀ s t hs hst).2])
  refine ⟨⟨μ₀, hDG₀⟩, C, fun μ hμ => ⟨⟨fun s t hs hst => (hμ s t hs hst).1,
    fun s t hs hst f => by rw [heq μ hμ s t hs hst]; exact hC.conv s t hs hst f⟩,
    fun t ht => by rw [heq μ hμ 0 t le_rfl ht]; exact hP₀ t ht⟩⟩

/-! ## `prop:discrete-gaussian-pyramid` -/

/-- **`prop:discrete-gaussian-pyramid`(1).** The series `Ψ_t` converge; laws with
`μ̂_{s,t} = e^{-(Ψ_t - Ψ_s)}` exist; any such laws are the kernels of a `q^ℤ`-covariant family in
the canonical discrete gauge, with folded data `(0, ϖ_t)`, and `T_q ϖ_t ≥ ϖ_t`. -/
theorem discrete_gaussian_pyramid_1 {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : Antitone w) (hwne : ∃ i, w i ≠ 0)
    (hneg : Summable fun i : {i : ℤ // i < 0} => w i * q ^ (2 * (i : ℤ)))
    (hpos : Summable fun i : {i : ℤ // 0 ≤ i} => w i) :
    (∀ t ω : ℝ, 0 < t → Summable fun i : ℤ =>
      dgWeight w (dgPhase q t) i * (1 - Real.cos (h * q ^ (i + dgLevel q t) * ω))) ∧
      (∃ μ : ℝ → ℝ → Measure ℝ, IsDGKernels q h w μ) ∧
      ∀ μ : ℝ → ℝ → Measure ℝ, IsDGKernels q h w μ →
        (∃ (Φ : ℝ → ℝ → (X →L[ℝ] X)) (S : ℝ → ℝ → ℝ), IsQCovariantLine q Φ S ∧
          IsCanonicalDiscreteGauge q S ∧ IsKernelFamily Φ μ) ∧
        (∀ t : ℝ, 0 ≤ t → ∃ Q : SymLevyPair, Q.a = 0 ∧ Q.ν = dgLevyMeasure q h w t ∧
          IsFoldedData (μ 0 t) Q) ∧
        ∀ t : ℝ, 0 ≤ t → dgLevyMeasure q h w t ≤ (dgLevyMeasure q h w t).map (fun v => q * v) := by
  have hw : IsDGWeights q w := ⟨hw0, hwanti, hwne, hneg, hpos⟩
  obtain ⟨hex, C, hC⟩ := dg_family hq hh hw
  refine ⟨fun t ω _ => hw.summable hq h (dgPhase_mem_Icc q t) _ ω, hex, fun μ hμ => ?_⟩
  obtain ⟨hker, hfold⟩ := hC μ hμ
  have hcov : ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ,
      (dgPair hq hh hw (q * t)).exponent ω = (dgPair hq hh hw t).exponent (q * ω) := by
    intro t _ ω
    rw [dgPair_exponent, dgPair_exponent, dgExponent_mul hq]
  obtain ⟨S, hS, hcan⟩ := (discrete_covariance_line C μ hker _ hfold hq).1.2 hcov
  refine ⟨⟨C.Φ, S, ⟨hq, ⟨C, rfl⟩, hS⟩, hcan, hker⟩,
    fun t ht => ⟨dgPair hq hh hw t, dgPair_a hq hh hw t, dgPair_ν hq hh hw t, hfold t ht⟩,
    fun t ht => ?_⟩
  have h4 := (discrete_covariance_line_semi C μ hker _ hfold hq S hS hcan t ht).2.2.2.1
  rwa [dgPair_ν] at h4

/-- A profile measure has no atoms. -/
theorem profileMeasure_singleton (k : ℝ → ℝ) (x : ℝ) : profileMeasure k {x} = 0 := by
  refine (withDensity_absolutelyContinuous _ _) ?_
  rw [Measure.restrict_apply (measurableSet_singleton _)]
  exact measure_mono_null inter_subset_left (Real.volume_singleton)

/-- **`prop:discrete-gaussian-pyramid`(2).** No increasing relabelling of the scales makes the
family fully covariant. -/
theorem discrete_gaussian_pyramid_2 {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : Antitone w) (hwne : ∃ i, w i ≠ 0)
    (hneg : Summable fun i : {i : ℤ // i < 0} => w i * q ^ (2 * (i : ℤ)))
    (hpos : Summable fun i : {i : ℤ // 0 ≤ i} => w i)
    (μ : ℝ → ℝ → Measure ℝ) (hμ : IsDGKernels q h w μ) (Φ : ℝ → ℝ → (X →L[ℝ] X))
    (hΦ : IsKernelFamily Φ μ) (ψ : ℝ → ℝ) (hψ : IsGauge ψ) :
    ¬ ∃ S : ℝ → ℝ → ℝ, IsScaleCovariant (fun s t => Φ (ψ s) (ψ t)) (Ioi 0) S := by
  rintro ⟨S, hS⟩
  have hw : IsDGWeights q w := ⟨hw0, hwanti, hwne, hneg, hpos⟩
  obtain ⟨-, C, hC⟩ := dg_family hq hh hw
  obtain ⟨hCμ, hfold⟩ := hC μ hμ
  -- `Φ` and `C.Φ` are convolution by the same kernels
  have hΦC : ∀ s t : ℝ, 0 ≤ s → s ≤ t → Φ s t = C.Φ s t := fun s t hs hst => by
    rw [eq_mconvL1_of_kernel hΦ hs hst, eq_mconvL1_of_kernel hCμ hs hst]
  -- conjugate the relabelled covariance back by `χ = ψ⁻¹`
  obtain ⟨χ, hχ, hχψ, hψχ⟩ := isGauge_inverse hψ
  have hψb := (isGauge_iff_isIncreasingBijection ψ).1 hψ
  have hχb := (isGauge_iff_isIncreasingBijection χ).1 hχ
  have hψ0 : ∀ u : ℝ, 0 ≤ u → 0 ≤ ψ u := fun u hu => hψb.mapsTo hu
  have hχ0 : ∀ u : ℝ, 0 ≤ u → 0 ≤ χ u := fun u hu => hχb.mapsTo hu
  have hψm : ∀ u v : ℝ, 0 ≤ u → u ≤ v → ψ u ≤ ψ v := fun u v hu huv =>
    hψb.strictMonoOn.monotoneOn (mem_Ici.2 hu) (mem_Ici.2 (hu.trans huv)) huv
  have hχm : ∀ u v : ℝ, 0 ≤ u → u ≤ v → χ u ≤ χ v := fun u v hu huv =>
    hχb.strictMonoOn.monotoneOn (mem_Ici.2 hu) (mem_Ici.2 (hu.trans huv)) huv
  have hS0 : ∀ lam : ℝ, 0 < lam → ∀ u : ℝ, 0 ≤ u → 0 ≤ S lam u := fun lam hlam u hu =>
    hS.S_mapsTo lam hlam hlam hu
  have hSm : ∀ lam : ℝ, 0 < lam → ∀ u v : ℝ, 0 ≤ u → u ≤ v → S lam u ≤ S lam v :=
    fun lam hlam u v hu huv => (hS.S_strictMonoOn lam hlam hlam).monotoneOn (mem_Ici.2 hu)
      (mem_Ici.2 (hu.trans huv)) huv
  have hcovC : IsScaleCovariant C.Φ (Ioi 0) (fun lam u => ψ (S lam (χ u))) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro lam hlam _ u hu
      exact hψb.mapsTo (mem_Ici.2 (hS0 lam hlam _ (hχ0 u hu)))
    · intro lam hlam _ u hu v hv huv
      exact hψb.strictMonoOn (mem_Ici.2 (hS0 lam hlam _ (hχ0 u hu)))
        (mem_Ici.2 (hS0 lam hlam _ (hχ0 v hv)))
        (hS.S_strictMonoOn lam hlam hlam (mem_Ici.2 (hχ0 u hu)) (mem_Ici.2 (hχ0 v hv))
          (hχb.strictMonoOn hu hv huv))
    · intro lam hlam _ v hv
      obtain ⟨x, hx, hSx⟩ := hS.S_surjOn lam hlam hlam (mem_Ici.2 (hχ0 v hv))
      refine ⟨ψ x, mem_Ici.2 (hψ0 x hx), ?_⟩
      change ψ (S lam (χ (ψ x))) = v
      rw [hχψ x hx, hSx, hψχ v hv]
    · intro lam hlam hmem u v hu huv
      have hcu := hχ0 u hu
      have hcuv := hχm u v hu huv
      have h1 := hS.scale lam hlam hmem (χ u) (χ v) hcu hcuv
      rw [hψχ u hu, hψχ v (hu.trans huv), hΦC u v hu huv,
        hΦC _ _ (hψ0 _ (hS0 lam hlam _ hcu)) (hψm _ _ (hS0 lam hlam _ hcu)
          (hSm lam hlam _ _ hcu hcuv))] at h1
      exact h1
  -- `thm:lattice-line`(3): some `ϖ_u`, `u > 0`, would be a profile measure
  obtain ⟨ψ₂, D, hψ₂, hdata⟩ := (lattice_line_3 C μ hCμ _ hfold).1 ⟨_, hcovC⟩
  have hu : 0 < ψ₂ 1 := isGauge_pos hψ₂ one_pos
  have hν : dgLevyMeasure q h w (ψ₂ 1) = profileMeasure fun v => D.k (v / 1) := by
    rw [← dgPair_ν hq hh hw]; exact (hdata 1 one_pos).2
  obtain ⟨j, hj⟩ := dgAtomWeight_pos hw (ψ₂ 1)
  have h1 := congrArg (fun m => m {h * q ^ j}) hν
  simp only [dgLevyMeasure_atom hq hh w hu, profileMeasure_singleton] at h1
  exact (ENNReal.ofReal_pos.2 hj).ne' h1

/-- **`prop:discrete-gaussian-pyramid`(3).** No kernel `μ_{0,t}`, `t > 0`, is carried by a
lattice `ξℤ`, `ξ > 0`. -/
theorem discrete_gaussian_pyramid_3 {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : Antitone w) (hwne : ∃ i, w i ≠ 0)
    (hneg : Summable fun i : {i : ℤ // i < 0} => w i * q ^ (2 * (i : ℤ)))
    (hpos : Summable fun i : {i : ℤ // 0 ≤ i} => w i)
    (μ : ℝ → ℝ → Measure ℝ) (hμ : IsDGKernels q h w μ) {t : ℝ} (ht : 0 < t) {ξ : ℝ}
    (hξ : 0 < ξ) : μ 0 t {x : ℝ | ¬∃ k : ℤ, x = ξ * k} ≠ 0 := by
  obtain ⟨⟨Φ, S, hQ, -, hker⟩, -⟩ :=
    (discrete_gaussian_pyramid_1 hq hh w hw0 hwanti hwne hneg hpos).2.2 μ hμ
  exact no_lattice_kernel_line_1 Φ S hQ μ hker ht hξ

end Pyramids
