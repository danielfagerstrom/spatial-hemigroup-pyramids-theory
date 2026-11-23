/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.ModulatedSelection

/-!
# `prop:modulated-selection-strict`: modulated selection reaches beyond the covariant ladders

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:modulated-selection-strict`. New at pass 6
(2026-11-22): the example the remark after `thm:phase-entropy-modulated-selection` gave in prose,
stated and proved.

## The route

* **The factor** `p(θ) = 1 + ε cos(2π log_q θ)` lies in `[1 - |ε|, 1 + |ε|]`, is `q^ℤ`-periodic
  (`modFactor_zpow_mul`), has `∫ p dη = 1` because the coefficient `j = 1` of `η` vanishes
  (`integral_cos_haarPhase`, from `phaseCoeff_haarPhase`), and is not almost everywhere constant:
  its cosine is positive on `(1, q^{1/4})` and negative on `(q^{1/4}, q^{3/4})`.
* **The fold.** In the measure `dv/(ℓv)` the step has the density `ℓ p(v)(k(v/q) - k(v))`; its sum
  over an orbit `θqⁿ` telescopes in both directions to `ℓ p(θ) K`, `K = k(0+)`
  (`hasSum_int_telescope`), so `μ° = ℓK · p η` (`lintegral_haarPhase_tsum_zpow`). Hence
  `|μ| = ℓK`, which is finite and positive because `k` is bounded and not identically zero, and
  `μ̄° = p η`.
* **The knot exponent.** `ϖ := p(v) k(v) dv/v` is a Lévy measure, as `p ≤ 2`; its dilation is
  `T_q ϖ = p(v) k(v/q) dv/v = μ + ϖ`, so the exponent `Ψ_1` of `(0, ϖ)` has the step
  `Ψ_1(q ·) - Ψ_1`, the exponent of `(0, μ)`: no Gaussian part, step measure `μ`, and the step
  is not zero because `μ` is not (`line_exponent_data_1_unique`).
* **No similarity member** is the last clause of `thm:phase-entropy-modulated-selection`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter ProbabilityTheory InformationTheory
open ScaleSpace (SymLevyPair)
open scoped ENNReal NNReal Topology

/-! ## The log-periodic factor -/

/-- **`p(θ) = 1 + ε cos(2π log_q θ)`**, the factor of `prop:modulated-selection-strict`. -/
noncomputable def modFactor (q ε θ : ℝ) : ℝ := 1 + ε * Real.cos (2 * Real.pi * Real.logb q θ)

theorem measurable_modFactor (q ε : ℝ) : Measurable (modFactor q ε) := by
  unfold modFactor
  exact measurable_const.add (measurable_const.mul (Real.continuous_cos.measurable.comp
    (measurable_const.mul (Real.measurable_log.div_const _))))

theorem modFactor_bounds (q ε θ : ℝ) :
    1 - |ε| ≤ modFactor q ε θ ∧ modFactor q ε θ ≤ 1 + |ε| := by
  have h : |ε * Real.cos (2 * Real.pi * Real.logb q θ)| ≤ |ε| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h2 := abs_le.1 h
  unfold modFactor
  constructor <;> linarith [h2.1, h2.2]

theorem modFactor_qClass {q : ℝ} (hq : 1 < q) (ε : ℝ) {v : ℝ} (hv : 0 < v) :
    modFactor q ε (qClass q v) = modFactor q ε v := by
  unfold modFactor
  rw [logb_qClass hq hv]
  have e : 2 * Real.pi * (Real.logb q v - (dgLevel q v : ℝ)) =
      2 * Real.pi * Real.logb q v - (dgLevel q v : ℝ) * (2 * Real.pi) := by ring
  rw [e, Real.cos_sub_int_mul_two_pi]

theorem modFactor_zpow_mul {q : ℝ} (hq : 1 < q) (ε : ℝ) {v : ℝ} (hv : 0 < v) (n : ℤ) :
    modFactor q ε (q ^ n * v) = modFactor q ε v := by
  have hq0 : 0 < q := by linarith
  rw [← modFactor_qClass hq ε (mul_pos (zpow_pos hq0 n) hv), qClass_zpow_mul hq hv,
    modFactor_qClass hq ε hv]

/-- **`∫ cos(2π log_q θ) η(dθ) = 0`**: the real part of the coefficient `j = 1` of `η`. -/
theorem integral_cos_haarPhase {q : ℝ} (hq : 1 < q) :
    ∫ θ, Real.cos (2 * Real.pi * Real.logb q θ) ∂(haarPhase q) = 0 := by
  haveI := isProbabilityMeasure_haarPhase hq
  have e : ∀ θ : ℝ, 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (Real.logb q θ : ℂ) =
      ((2 * Real.pi * Real.logb q θ : ℝ) : ℂ) * Complex.I := by
    intro θ
    push_cast
    ring
  have hint : Integrable (phaseChar q 1) (haarPhase q) := by
    refine Integrable.of_bound (measurable_phaseChar q 1).aestronglyMeasurable 1
      (ae_of_all _ fun θ => ?_)
    rw [phaseChar, e, Complex.norm_exp_ofReal_mul_I]
  have hre : ∀ θ : ℝ, Real.cos (2 * Real.pi * Real.logb q θ) = (phaseChar q 1 θ).re := by
    intro θ
    rw [phaseChar, e, Complex.exp_ofReal_mul_I_re]
  have h0 : ∫ θ, phaseChar q 1 θ ∂(haarPhase q) = 0 := phaseCoeff_haarPhase hq one_ne_zero
  simp_rw [hre]
  have h1 := integral_re hint
  simp only [RCLike.re_to_complex] at h1
  rw [h1, h0, Complex.zero_re]

/-- **`∫ p dη = 1`.** -/
theorem lintegral_modFactor_haarPhase {q : ℝ} (hq : 1 < q) {ε : ℝ} (hε1 : |ε| < 1) :
    ∫⁻ θ, ENNReal.ofReal (modFactor q ε θ) ∂(haarPhase q) = 1 := by
  haveI := isProbabilityMeasure_haarPhase hq
  have hcos : Integrable (fun θ => Real.cos (2 * Real.pi * Real.logb q θ)) (haarPhase q) :=
    Integrable.of_bound (Real.continuous_cos.measurable.comp
      (measurable_const.mul (Real.measurable_log.div_const _))).aestronglyMeasurable 1
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hpint : Integrable (modFactor q ε) (haarPhase q) :=
    (integrable_const 1).add (hcos.const_mul ε)
  rw [← ofReal_integral_eq_lintegral_ofReal hpint (ae_of_all _ fun θ => by
    have := (modFactor_bounds q ε θ).1
    show (0 : ℝ) ≤ modFactor q ε θ
    linarith)]
  have h : ∫ θ, modFactor q ε θ ∂(haarPhase q) = 1 := by
    change ∫ θ, (1 + ε * Real.cos (2 * Real.pi * Real.logb q θ)) ∂(haarPhase q) = 1
    rw [integral_add (integrable_const _) (hcos.const_mul ε), integral_const_mul,
      integral_cos_haarPhase hq]
    simp
  rw [h, ENNReal.ofReal_one]

/-- **`p` is not almost everywhere constant** for `ε ≠ 0`. -/
theorem modFactor_not_ae_const {q : ℝ} (hq : 1 < q) {ε : ℝ} (hε0 : ε ≠ 0) :
    ¬ ∃ c : ℝ, ∀ᵐ θ ∂(haarPhase q), modFactor q ε θ = c := by
  rintro ⟨c, hc⟩
  have hq0 : 0 < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos hq
  have hac : volume.restrict (Ico 1 q) ≪ haarPhase q := by
    refine withDensity_absolutelyContinuous' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ico] with θ hθ
    exact (ENNReal.ofReal_pos.2 (one_div_pos.2
      (mul_pos hl (lt_of_lt_of_le one_pos hθ.1)))).ne'
  have hpos : ∀ a b : ℝ, 1 ≤ a → a < b → b ≤ q → haarPhase q (Ioo a b) ≠ 0 := by
    intro a b ha hab hb h0
    have h := hac h0
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.2 (show Ioo a b ⊆ Ico 1 q from fun x hx =>
        ⟨ha.trans hx.1.le, lt_of_lt_of_le hx.2 hb⟩),
      Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h
    linarith
  set a1 : ℝ := q ^ ((1 : ℝ) / 4) with ha1
  set a3 : ℝ := q ^ ((3 : ℝ) / 4) with ha3
  have h1a1 : 1 < a1 := Real.one_lt_rpow hq (by norm_num)
  have ha13 : a1 < a3 := Real.rpow_lt_rpow_of_exponent_lt hq (by norm_num)
  have ha3q : a3 ≤ q := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hq (show (3 : ℝ) / 4 < 1 by norm_num)
    rw [Real.rpow_one] at h
    exact h.le
  have hl1 : Real.logb q a1 = 1 / 4 := Real.logb_rpow hq0 (ne_of_gt hq)
  have hl3 : Real.logb q a3 = 3 / 4 := Real.logb_rpow hq0 (ne_of_gt hq)
  obtain ⟨θ1, hθ1, e1⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpos 1 a1 le_rfl h1a1 (ha13.trans_le ha3q).le) (ae_restrict_of_ae hc)
  obtain ⟨θ2, hθ2, e2⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpos a1 a3 h1a1.le ha13 ha3q) (ae_restrict_of_ae hc)
  have hθ10 : 0 < θ1 := lt_trans one_pos hθ1.1
  have hθ20 : 0 < θ2 := lt_trans (lt_trans one_pos h1a1) hθ2.1
  have l1a : 0 < Real.logb q θ1 := by
    have := Real.logb_lt_logb hq one_pos hθ1.1
    rwa [Real.logb_one] at this
  have l1b : Real.logb q θ1 < 1 / 4 := by
    have := Real.logb_lt_logb hq hθ10 hθ1.2
    rwa [hl1] at this
  have l2a : 1 / 4 < Real.logb q θ2 := by
    have := Real.logb_lt_logb hq (lt_trans one_pos h1a1) hθ2.1
    rwa [hl1] at this
  have l2b : Real.logb q θ2 < 3 / 4 := by
    have := Real.logb_lt_logb hq hθ20 hθ2.2
    rwa [hl3] at this
  have hπ := Real.pi_pos
  have c1 : 0 < Real.cos (2 * Real.pi * Real.logb q θ1) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
  have c2 : Real.cos (2 * Real.pi * Real.logb q θ2) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith) (by nlinarith)
  unfold modFactor at e1 e2
  have e3 : ε * Real.cos (2 * Real.pi * Real.logb q θ1) =
      ε * Real.cos (2 * Real.pi * Real.logb q θ2) := by linarith
  have e4 := mul_left_cancel₀ hε0 e3
  linarith

/-! ## Telescoping over `ℤ` -/

/-- **`∑_{n ∈ ℤ} (b_{n-1} - b_n) = K`** for `b` nonincreasing with `b_n → 0` as `n → ∞` and
`b_{-n} → K` as `n → ∞`. -/
theorem hasSum_int_telescope {b : ℤ → ℝ} (hb : Antitone b) {K : ℝ}
    (htop : Tendsto (fun N : ℕ => b N) atTop (𝓝 0))
    (hbot : Tendsto (fun N : ℕ => b (-(N : ℤ))) atTop (𝓝 K)) :
    HasSum (fun n : ℤ => b (n - 1) - b n) K := by
  have hnn : ∀ n : ℤ, 0 ≤ b (n - 1) - b n := fun n => sub_nonneg.2 (hb (by omega))
  have h1 : HasSum (fun N : ℕ => b ((N : ℤ) - 1) - b N) (b (-1)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun N => hnn N)]
    have e : ∀ N : ℕ, ∑ i ∈ Finset.range N, (b ((i : ℤ) - 1) - b i) =
        b (-1) - b ((N : ℤ) - 1) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        have : ((N + 1 : ℕ) : ℤ) - 1 = (N : ℤ) := by push_cast; ring
        rw [this]
        ring
    simp_rw [e]
    have h : Tendsto (fun N : ℕ => b ((N : ℤ) - 1)) atTop (𝓝 0) := by
      rw [← tendsto_add_atTop_iff_nat 1]
      refine htop.congr fun N => ?_
      simp
    have := (tendsto_const_nhds (x := b (-1))).sub h
    rwa [sub_zero] at this
  have h2 : HasSum (fun N : ℕ => b (-((N : ℤ) + 1) - 1) - b (-((N : ℤ) + 1))) (K - b (-1)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun N => hnn _)]
    have e : ∀ N : ℕ, ∑ i ∈ Finset.range N, (b (-((i : ℤ) + 1) - 1) - b (-((i : ℤ) + 1))) =
        b (-((N : ℤ) + 1)) - b (-1) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        have : -((N : ℤ) + 1) - 1 = -(((N + 1 : ℕ) : ℤ) + 1) := by push_cast; ring
        rw [this]
        ring
    simp_rw [e]
    have h : Tendsto (fun N : ℕ => b (-((N : ℤ) + 1))) atTop (𝓝 K) := by
      rw [← tendsto_add_atTop_iff_nat 1] at hbot
      refine hbot.congr fun N => ?_
      simp only [Nat.cast_add, Nat.cast_one]
    exact h.sub tendsto_const_nhds
  have h3 := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => b (n - 1) - b n) h1 h2
  convert h3 using 1
  ring

/-! ## The node -/

/-- **`prop:modulated-selection-strict`.** Let `0 < |ε| < 1`, and let `k ≥ 0` be nonincreasing
and bounded on `(0,∞)`, not identically zero there, with `∫ (1 ∧ x²) k(x) dx/x < ∞`. The measure
`μ(dv) = (1 + ε cos(2π log_q v))(k(v/q) - k(v)) dv/v` is the step measure of a ladder with no
Gaussian part and `0 < |μ| < ∞`, which meets hypotheses (1) and (2) of
`thm:phase-entropy-modulated-selection` with `p(θ) = 1 + ε cos(2π log_q θ)`, for which `p` is not
almost everywhere constant, and which has no similarity member. -/
theorem modulated_selection_strict {q ε : ℝ} (hq : 1 < q) (hε0 : ε ≠ 0) (hε1 : |ε| < 1)
    (k : ℝ → ℝ) (hk0 : ∀ x : ℝ, 0 < x → 0 ≤ k x) (hkanti : AntitoneOn k (Ioi 0))
    (hkbdd : BddAbove (k '' Ioi 0)) (hkne : ∃ x : ℝ, 0 < x ∧ k x ≠ 0)
    (hkint : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * k x / x) ≠ ⊤)
    (m : Measure ℝ) (hm : m = (volume.restrict (Ioi 0)).withDensity
      fun v => ENNReal.ofReal (modFactor q ε v * (k (v / q) - k v) / v)) :
    ∃ Ψ1 : ℝ → ℝ, IsKnotExponent q Ψ1 ∧ HasNoGaussianStep q Ψ1 ∧ IsStepMeasure q Ψ1 m ∧
      m univ ≠ 0 ∧ m univ ≠ ⊤ ∧
      foldedStepNorm q m =
        (haarPhase q).withDensity (fun θ => ENNReal.ofReal (modFactor q ε θ)) ∧
      (∀ᵐ θ ∂(haarPhase q), 0 < modFactor q ε θ) ∧
      klDiv (foldedStepNorm q m) (haarPhase q) ≠ ⊤ ∧
      m = (volume.restrict (Ioi 0)).withDensity
        (fun v => ENNReal.ofReal (modFactor q ε (qClass q v) * (k (v / q) - k v) / v)) ∧
      (¬ ∃ c : ℝ, ∀ᵐ θ ∂(haarPhase q), modFactor q ε θ = c) ∧
      ¬ ∃ μ ∈ modulationOrbit q Ψ1, ∀ t : ℝ, 0 < t → ∀ ω : ℝ,
        lineExponent μ t ω = Ψ1 (t * ω) := by
  have hq0 : 0 < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos hq
  haveI := isProbabilityMeasure_haarPhase hq
  set p : ℝ → ℝ := modFactor q ε with hp_def
  have hpm : Measurable p := measurable_modFactor q ε
  have hp0 : ∀ θ, 0 ≤ p θ := fun θ => by
    have := (modFactor_bounds q ε θ).1
    linarith
  have hppos : ∀ θ, 0 < p θ := fun θ => by
    have := (modFactor_bounds q ε θ).1
    linarith
  have hp2 : ∀ θ, p θ ≤ 2 := fun θ => by
    have := (modFactor_bounds q ε θ).2
    linarith
  -- a measurable version of `k`
  set kt : ℝ → ℝ := fun x => k (Real.exp (Real.log x)) with hkt
  have hkt_eq : ∀ x : ℝ, 0 < x → kt x = k x := fun x hx => by
    simp only [hkt, Real.exp_log hx]
  have hanti : Antitone fun u => k (Real.exp u) := fun u u' h =>
    hkanti (Real.exp_pos u) (Real.exp_pos u') (Real.exp_le_exp.2 h)
  have hktm : Measurable kt := hanti.measurable.comp Real.measurable_log
  have hkt0 : ∀ x : ℝ, 0 < x → 0 ≤ kt x := fun x hx => by
    rw [hkt_eq x hx]
    exact hk0 x hx
  have hktanti : AntitoneOn kt (Ioi 0) := fun x hx y hy hxy => by
    rw [hkt_eq x hx, hkt_eq y hy]
    exact hkanti hx hy hxy
  have hklim := tendsto_profile_atTop hk0 hkanti hkint
  have hktlim : Tendsto kt atTop (𝓝 0) :=
    hklim.congr' ((eventually_gt_atTop 0).mono fun x hx => (hkt_eq x hx).symm)
  -- `K = k(0+)`
  have hbdd : BddAbove (range fun u => k (Real.exp u)) := by
    obtain ⟨M, hM⟩ := hkbdd
    exact ⟨M, by rintro _ ⟨u, rfl⟩; exact hM (mem_image_of_mem k (Real.exp_pos u))⟩
  set K : ℝ := ⨆ u : ℝ, k (Real.exp u) with hK
  have hKpos : 0 < K := by
    obtain ⟨x0, hx0, hkx0⟩ := hkne
    have h1 : 0 < k x0 := lt_of_le_of_ne (hk0 x0 hx0) (Ne.symm hkx0)
    have h2 : k (Real.exp (Real.log x0)) ≤ K := le_ciSup hbdd (Real.log x0)
    rw [Real.exp_log hx0] at h2
    linarith
  -- the telescoping along an orbit
  have htel : ∀ θ : ℝ, 0 < θ →
      HasSum (fun n : ℤ => kt (θ * q ^ (n - 1)) - kt (θ * q ^ n)) K := by
    intro θ hθ
    refine hasSum_int_telescope (b := fun n : ℤ => kt (θ * q ^ n)) ?_ ?_ ?_
    · intro n n' hnn'
      exact hktanti (mul_pos hθ (zpow_pos hq0 n)) (mul_pos hθ (zpow_pos hq0 n'))
        (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hq.le hnn') hθ.le)
    · simp_rw [zpow_natCast]
      exact hktlim.comp ((tendsto_pow_atTop_atTop_of_one_lt hq).const_mul_atTop hθ)
    · have e : ∀ N : ℕ, Real.log (θ * q ^ (-(N : ℤ))) = Real.log θ + -(N * Real.log q) := by
        intro N
        rw [Real.log_mul hθ.ne' (zpow_pos hq0 _).ne', Real.log_zpow]
        push_cast
        ring
      have hlog : Tendsto (fun N : ℕ => Real.log (θ * q ^ (-(N : ℤ)))) atTop atBot := by
        refine Tendsto.congr (fun N => (e N).symm) ?_
        exact tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const hl))
      exact (tendsto_atBot_ciSup hanti hbdd).comp hlog
  -- the step measure, with the measurable `kt`
  set fm : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (p v * (kt (v / q) - kt v) / v) with hfm
  have hfmm : Measurable fm :=
    ((hpm.mul ((hktm.comp (measurable_id.div_const q)).sub hktm)).div
      measurable_id).ennreal_ofReal
  have hm' : m = (volume.restrict (Ioi 0)).withDensity fm := by
    rw [hm]
    exact withDensity_Ioi_congr fun v hv => by
      simp only [hfm, hkt_eq v hv, hkt_eq _ (div_pos hv hq0)]
  have hkdec : ∀ v : ℝ, 0 < v → kt v ≤ kt (v / q) := fun v hv =>
    hktanti (div_pos hv hq0) hv (div_le_self hv.le hq.le)
  -- the fold of the step
  set g : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.log q * p v * (kt (v / q) - kt v)) with hg
  have hgm : Measurable g :=
    ((measurable_const.mul hpm).mul ((hktm.comp (measurable_id.div_const q)).sub
      hktm)).ennreal_ofReal
  have hm_apply : ∀ S : Set ℝ, MeasurableSet S →
      m S = ∫⁻ θ, ∑' n : ℤ, S.indicator g (θ * q ^ n) ∂(haarPhase q) := by
    intro S hS
    rw [lintegral_haarPhase_tsum_zpow hq (hgm.indicator hS), lintegral_logHaar q (hgm.indicator hS),
      hm', withDensity_apply _ hS, ← lintegral_indicator hS]
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    by_cases hyS : y ∈ S
    · rw [indicator_of_mem hyS, indicator_of_mem hyS, hfm, hg]
      dsimp only
      rw [← ENNReal.ofReal_mul (one_div_nonneg.2 (mul_pos hl hy0).le)]
      congr 1
      field_simp
    · rw [indicator_of_notMem hyS, indicator_of_notMem hyS, mul_zero]
  have hfold : foldMeasure q m = (haarPhase q).withDensity
      fun θ => ENNReal.ofReal (Real.log q * K) * ENNReal.ofReal (p θ) := by
    ext A hA
    rw [foldMeasure, Measure.map_apply (measurable_qClass q) hA,
      hm_apply _ (measurable_qClass q hA), withDensity_apply _ hA, ← lintegral_indicator hA]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_haarPhase_mem q] with θ hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθ.1
    have hterm : ∀ n : ℤ, (qClass q ⁻¹' A).indicator g (θ * q ^ n) = A.indicator
        (fun _ => ENNReal.ofReal (Real.log q * p θ * (kt (θ * q ^ (n - 1)) - kt (θ * q ^ n))))
        θ := by
      intro n
      have hc : qClass q (θ * q ^ n) = θ := by rw [mul_comm]; exact qClass_eq_of_mem hq hθ n
      by_cases hA' : θ ∈ A
      · rw [indicator_of_mem (show θ * q ^ n ∈ qClass q ⁻¹' A by rw [mem_preimage, hc]; exact hA'),
          indicator_of_mem hA', hg]
        dsimp only
        have hpn : p (θ * q ^ n) = p θ := by
          rw [mul_comm]
          exact modFactor_zpow_mul hq ε hθ0 n
        have hdiv : θ * q ^ n / q = θ * q ^ (n - 1) := by
          rw [zpow_sub_one₀ hq0.ne']
          ring
        rw [hpn, hdiv]
      · rw [indicator_of_notMem (show θ * q ^ n ∉ qClass q ⁻¹' A by
          rw [mem_preimage, hc]; exact hA'), indicator_of_notMem hA']
    simp_rw [hterm]
    by_cases hA' : θ ∈ A
    · simp only [indicator_of_mem hA']
      have hs : HasSum (fun n : ℤ => Real.log q * p θ * (kt (θ * q ^ (n - 1)) - kt (θ * q ^ n)))
          (Real.log q * p θ * K) := (htel θ hθ0).mul_left _
      have hnn : ∀ n : ℤ, 0 ≤ Real.log q * p θ * (kt (θ * q ^ (n - 1)) - kt (θ * q ^ n)) := by
        intro n
        refine mul_nonneg (mul_nonneg hl.le (hp0 θ)) (sub_nonneg.2 ?_)
        exact hktanti (mul_pos hθ0 (zpow_pos hq0 _)) (mul_pos hθ0 (zpow_pos hq0 _))
          (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hq.le (by omega)) hθ0.le)
      rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs.summable, hs.tsum_eq,
        ← ENNReal.ofReal_mul (mul_pos hl hKpos).le]
      congr 1
      ring
    · simp only [indicator_of_notMem hA', tsum_zero]
  have hpη : ∫⁻ θ, ENNReal.ofReal (p θ) ∂(haarPhase q) = 1 :=
    lintegral_modFactor_haarPhase hq hε1
  have hmuniv : m univ = ENNReal.ofReal (Real.log q * K) := by
    have h1 : foldMeasure q m univ = m univ := by
      rw [foldMeasure, Measure.map_apply (measurable_qClass q) MeasurableSet.univ, preimage_univ]
    rw [← h1, hfold, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_const_mul _ hpm.ennreal_ofReal, hpη, mul_one]
  have hm0 : m univ ≠ 0 := by
    rw [hmuniv]
    exact (ENNReal.ofReal_pos.2 (mul_pos hl hKpos)).ne'
  have hmfin : m univ ≠ ⊤ := by
    rw [hmuniv]
    exact ENNReal.ofReal_ne_top
  have hfsn : foldedStepNorm q m =
      (haarPhase q).withDensity (fun θ => ENNReal.ofReal (p θ)) := by
    ext A hA
    rw [foldedStepNorm, Measure.smul_apply, smul_eq_mul, hfold, withDensity_apply _ hA,
      withDensity_apply _ hA, lintegral_const_mul _ hpm.ennreal_ofReal, ← mul_assoc, hmuniv,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 (mul_pos hl hKpos)).ne' ENNReal.ofReal_ne_top,
      one_mul]
  -- hypothesis (1): the relative entropy is finite
  have hKL : klDiv (foldedStepNorm q m) (haarPhase q) ≠ ⊤ := by
    rw [hfsn]
    haveI : IsProbabilityMeasure ((haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)) :=
      ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hpη]⟩
    refine klDiv_ne_top_iff.2 ⟨withDensity_absolutelyContinuous _ _, ?_⟩
    have hllr : llr ((haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)) (haarPhase q) =ᵐ[
        (haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)] fun θ => Real.log (p θ) := by
      have h1 : ((haarPhase q).withDensity fun θ => ENNReal.ofReal (p θ)).rnDeriv (haarPhase q)
          =ᵐ[haarPhase q] fun θ => ENNReal.ofReal (p θ) :=
        Measure.rnDeriv_withDensity _ hpm.ennreal_ofReal
      filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h1] with θ hθ
      simp only [llr, hθ, ENNReal.toReal_ofReal (hp0 θ)]
    refine Integrable.congr ?_ hllr.symm
    refine Integrable.of_bound (Real.measurable_log.comp hpm).aestronglyMeasurable
      (max |Real.log (1 - |ε|)| |Real.log (1 + |ε|)|) (ae_of_all _ fun θ => ?_)
    have hlo : 0 < 1 - |ε| := by linarith
    have hb := modFactor_bounds q ε θ
    have h1 : Real.log (1 - |ε|) ≤ Real.log (p θ) := Real.log_le_log hlo hb.1
    have h2 : Real.log (p θ) ≤ Real.log (1 + |ε|) := Real.log_le_log (hppos θ) hb.2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (1 - |ε|)),
        le_max_left |Real.log (1 - |ε|)| |Real.log (1 + |ε|)|]
    · linarith [le_abs_self (Real.log (1 + |ε|)),
        le_max_right |Real.log (1 - |ε|)| |Real.log (1 + |ε|)|]
  -- the knot measure `ϖ = p(v) k(v) dv/v`
  set fϖ : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (p v * kt v / v) with hfϖ
  have hfϖm : Measurable fϖ := ((hpm.mul hktm).div measurable_id).ennreal_ofReal
  set ϖ : Measure ℝ := (volume.restrict (Ioi 0)).withDensity fϖ with hϖ
  have hnull : (volume.restrict (Ioi (0 : ℝ))) (Iic 0) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iic, inter_comm, Ioi_inter_Iic, Ioc_self,
      measure_empty]
  have hϖfold : ScaleSpace.IsFolded ϖ := withDensity_absolutelyContinuous _ _ hnull
  have hϖint : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ϖ ≠ ⊤ := by
    rw [hϖ, lintegral_withDensity_eq_lintegral_mul _ hfϖm (by fun_prop)]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2)) hkint) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    simp only [Pi.mul_apply, hfϖ]
    rw [hkt_eq x hx0, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (hp0 x) (hk0 x hx0)) hx0.le),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmn : 0 ≤ min 1 (x ^ 2) * k x / x :=
      div_nonneg (mul_nonneg (le_min zero_le_one (sq_nonneg x)) (hk0 x hx0)) hx0.le
    calc p x * k x / x * min 1 (x ^ 2) = p x * (min 1 (x ^ 2) * k x / x) := by ring
      _ ≤ 2 * (min 1 (x ^ 2) * k x / x) := mul_le_mul_of_nonneg_right (hp2 x) hmn
  set P1 : SymLevyPair :=
    { a := 0, ν := ϖ, a_nonneg := le_rfl, ν_folded := hϖfold, ν_integrable := hϖint } with hP1
  -- `T_q ϖ = μ + ϖ`
  have hTq : ϖ.map (fun v => q * v) = m + ϖ := by
    rw [hϖ, map_mul_withDensity_Ioi hq0 hfϖm, hm', ← withDensity_add_left hfmm]
    refine withDensity_Ioi_congr fun u hu => ?_
    have hu' : u ≠ 0 := hu.ne'
    have hq' : q ≠ 0 := hq0.ne'
    simp only [hfϖ, hfm, Pi.add_apply, inv_mul_eq_div]
    have hp' : p (u / q) = p u := by
      have h := modFactor_zpow_mul hq ε (div_pos hu hq0) 1
      rw [zpow_one, mul_div_cancel₀ _ hq'] at h
      exact h.symm
    rw [hp', ← ENNReal.ofReal_mul (inv_nonneg.2 hq0.le),
      ← ENNReal.ofReal_add (div_nonneg (mul_nonneg (hp0 u) (sub_nonneg.2 (hkdec u hu))) hu.le)
        (div_nonneg (mul_nonneg (hp0 u) (hkt0 u hu)) hu.le)]
    congr 1
    field_simp
    ring
  -- the step pair `(0, μ)`
  have hmfold : ScaleSpace.IsFolded m := by
    rw [hm']
    exact withDensity_absolutelyContinuous _ _ hnull
  haveI hmfinI : IsFiniteMeasure m := ⟨lt_top_iff_ne_top.2 hmfin⟩
  set Pm : SymLevyPair := maskPair m hmfinI hmfold with hPm
  set Ψ1 : ℝ → ℝ := P1.exponent with hΨ1
  have hstep : HasExpData (knotStep q Ψ1) Pm := by
    obtain ⟨Q2, hQ2a, hQ2ν, hQ2⟩ := line_exponent_data_2 Ψ1 P1 (fun ω => rfl) hq0
    have hQ : Q2.exponent = (SymLevyPair_add Pm P1).exponent := by
      refine symLevyPair_exponent_congr ?_ ?_
      · rw [hQ2a]
        simp [SymLevyPair_add, hPm, hP1, maskPair]
      · rw [hQ2ν]
        exact hTq
    intro ω
    have h2 : Ψ1 (q * ω) = Q2.exponent ω := hQ2 ω
    have h3 : Ψ1 ω = P1.exponent ω := rfl
    rw [knotStep, h2, hQ, SymLevyPair_add_exponent, h3]
    ring
  have hK : IsKnotExponent q Ψ1 := by
    refine ⟨⟨P1, fun ω => rfl⟩, ⟨Pm, hstep⟩, ?_⟩
    by_contra hcon
    push Not at hcon
    have h0fold : ScaleSpace.IsFolded (0 : Measure ℝ) := by simp [ScaleSpace.IsFolded]
    have hz : HasExpData (knotStep q Ψ1) (maskPair 0 inferInstance h0fold) := fun ω => by
      rw [hcon ω, maskPair_exponent, integral_zero_measure]
    have h := (line_exponent_data_1_unique _ Pm _ hstep hz).2
    apply hm0
    have h' : m = 0 := h
    rw [h', Measure.coe_zero, Pi.zero_apply]
  have hnoG : HasNoGaussianStep q Ψ1 := ⟨Pm, hstep, rfl⟩
  have hstepm : IsStepMeasure q Ψ1 m := ⟨Pm, hstep, rfl⟩
  -- hypothesis (2), in the form of the theorem
  have hmk : m = (volume.restrict (Ioi 0)).withDensity
      fun v => ENNReal.ofReal (p (qClass q v) * (k (v / q) - k v) / v) := by
    rw [hm]
    exact withDensity_Ioi_congr fun v hv => by rw [hp_def, modFactor_qClass hq ε hv]
  have hnc := modFactor_not_ae_const hq hε0
  have hsel := phase_entropy_modulated_selection hq Ψ1 hK hnoG m hstepm hm0 hmfin p hpm hfsn
    (ae_of_all _ hppos) hKL k hk0 hkanti hkint hmk
  exact ⟨Ψ1, hK, hnoG, hstepm, hm0, hmfin, hfsn, ae_of_all _ hppos, hKL, hmk, hnc,
    hsel.2.2.2 hnc⟩

end Pyramids
