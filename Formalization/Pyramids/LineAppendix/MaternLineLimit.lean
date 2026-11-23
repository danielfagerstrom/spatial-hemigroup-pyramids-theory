/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.MaternLine
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# `thm:matern-pyramid-line`, clause (4): the limit `q ↓ 1`

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:matern-pyramid-line`. Phase 5, wave 3e. The
three declarations of clause (4) moved here from `PyramidsSkeleton.ChA1Line`, their statements
unchanged.

* **The bound.** With `f(u) = log(1 + c²ω²e^{-2u})`, decreasing, and `ℓ = log q`,
  `ℓF_q(ω) = ∑_{i ≥ 1} ℓf(iℓ)` and `F_∞(ω) = ∑_{i ≥ 0} ∫_{iℓ}^{(i+1)ℓ} f`, the second from
  `∫₀^{Nℓ} f → ∫₀^∞ f`. Comparing term by term, `F_∞ - ∫₀^ℓ f ≤ ℓF_q ≤ F_∞`, and
  `∫₀^ℓ f ≤ ℓf(0)`.
* **The limit.** Locally uniform from the bound, `log(1 + c²y²)` being bounded on `|y - x| < 1`.
* **The forms (A.e8).** Two changes of variable (`integral_image_eq_integral_abs_deriv_smul`):
  `θ = eᵘ/c` maps `(0,∞)` onto `(1/c,∞)` and gives the `θ` form; `v = c²ω²e^{-2u}` maps `(0,∞)` onto
  `(0, c²ω²)` and gives `F_∞(ω) = ½∫₀^{c²ω²} log(1 + v) dv/v`, which `u = -v` turns into
  `-½ Li₂(-c²ω²)` with `Li₂(x) = -∫₀ˣ log(1 - u) du/u` (`dilog`).
* **The profile.** `k_∞(x) = 2∫_{1/c}^∞ e^{-θx} dθ/θ` is nonnegative and nonincreasing; by Tonelli
  `∫₀^∞ x k_∞(x) dx = ∫_{1/c}^∞ 2θ^{-3} dθ < ∞`, which bounds both integrability conditions of an
  `SDProfile`; and by Tonelli and `lem:laplace-atoms-admissible`(1) its exponent is the `θ` form.
* **The laws.** They exist by `lem:line-exponent-data`(1) (`dilatePair` of a multiple of the
  profile). The weak convergence is Mathlib's Lévy continuity theorem
  (`ProbabilityMeasure.tendsto_of_tendsto_charFun`), along every sequence `q_n ↓ 1`
  (`tendsto_iff_seq_tendsto`). For the kernels, `F_q(y) ≥ F_∞(y)/ℓ - log(1 + c²y²) → ∞` for `y ≠ 0`,
  since `F_∞(y) > 0`; so a weak limit `ν` would have `∫ cos(ωx) ν(dx) = 0` for every `ω ≠ 0`,
  against its continuity at `0` with the value `1`. This direction needs only the definition of weak
  convergence, tested on `x ↦ cos(ωx)`.

**What it reaches.** The bound and the limit print Lean core; the laws print A39's
`levy_khintchine_converse` (their existence, from `line_exponent_data_1`). Mathlib's Lévy
continuity theorem is Lean core.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter
open ScaleSpace (SDProfile)
open scoped Topology ENNReal BoundedContinuousFunction

variable {q c : ℝ}

/-! ## The integrand `f(u) = log(1 + Ae^{-2u})` -/

/-- `f_A(u) := log(1 + Ae^{-2u})`, so that `F_∞(ω) = ∫₀^∞ f_{c²ω²}`. -/
noncomputable def limitIntegrand (A u : ℝ) : ℝ := Real.log (1 + A * Real.exp (-2 * u))

section Integrand

variable {A : ℝ} (hA : 0 ≤ A)
include hA

theorem limitIntegrand_pos_arg (u : ℝ) : 0 < 1 + A * Real.exp (-2 * u) := by
  have := Real.exp_pos (-2 * u)
  positivity

theorem limitIntegrand_nonneg (u : ℝ) : 0 ≤ limitIntegrand A u :=
  Real.log_nonneg (by have := Real.exp_pos (-2 * u); nlinarith)

theorem limitIntegrand_le (u : ℝ) : limitIntegrand A u ≤ A * Real.exp (-2 * u) := by
  have := Real.log_le_sub_one_of_pos (limitIntegrand_pos_arg hA u)
  rw [limitIntegrand]
  linarith

theorem limitIntegrand_antitone : Antitone (limitIntegrand A) := by
  intro u v huv
  refine Real.log_le_log (limitIntegrand_pos_arg hA v) ?_
  have : Real.exp (-2 * v) ≤ Real.exp (-2 * u) := Real.exp_le_exp.2 (by linarith)
  nlinarith

theorem continuous_limitIntegrand : Continuous (limitIntegrand A) :=
  Continuous.log (by fun_prop) fun u => (limitIntegrand_pos_arg hA u).ne'

theorem integrableOn_limitIntegrand : IntegrableOn (limitIntegrand A) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 two_pos).const_mul A)
    (continuous_limitIntegrand hA).aestronglyMeasurable ?_
  refine Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (limitIntegrand_nonneg hA u)]
  exact limitIntegrand_le hA u

end Integrand

theorem maternLineLimit_eq (c ω : ℝ) :
    maternLineLimit c ω = ∫ u in Ioi (0 : ℝ), limitIntegrand (c ^ 2 * ω ^ 2) u := rfl

/-- `log(1 + c²ω²q^{-2(i+1)}) = f((i+1)ℓ)`, `ℓ = log q`. -/
theorem maternTerm_eq_limitIntegrand (hq : 1 < q) (c ω : ℝ) (i : ℕ) :
    Real.log (1 + c ^ 2 * ω ^ 2 / q ^ (2 * (i + 1))) =
      limitIntegrand (c ^ 2 * ω ^ 2) ((i + 1 : ℕ) * Real.log q) := by
  have hq0 : 0 < q := by linarith
  have e : q ^ (2 * (i + 1)) = Real.exp (2 * ((i + 1 : ℕ) * Real.log q)) := by
    rw [← Real.exp_log hq0, ← Real.exp_nat_mul, Real.log_exp]
    push_cast
    ring_nf
  rw [limitIntegrand, e, div_eq_mul_inv, ← Real.exp_neg]
  ring_nf

/-! ## The bound -/

/-- **`thm:matern-pyramid-line`(4), the bound.** `0 ≤ F_∞(ω) - ℓF_q(ω) ≤ ℓ log(1 + c²ω²)`. -/
theorem matern_pyramid_line_4_bound {q c : ℝ} (hq : 1 < q) (hc : 0 < c) (ω : ℝ) :
    0 ≤ maternLineLimit c ω - Real.log q * maternExponent q c ω ∧
      maternLineLimit c ω - Real.log q * maternExponent q c ω ≤
        Real.log q * Real.log (1 + c ^ 2 * ω ^ 2) := by
  set A := c ^ 2 * ω ^ 2 with hAdef
  have hA : 0 ≤ A := by positivity
  set ℓ := Real.log q with hℓdef
  have hℓ : 0 < ℓ := Real.log_pos hq
  set f := limitIntegrand A with hfdef
  have hf0 := limitIntegrand_nonneg hA
  have hfa := limitIntegrand_antitone hA
  have hfc := continuous_limitIntegrand hA
  have hfi := integrableOn_limitIntegrand hA
  -- the pieces `a_i = ∫_{iℓ}^{(i+1)ℓ} f`
  set a : ℕ → ℝ := fun i => ∫ u in (i * ℓ)..((i + 1 : ℕ) * ℓ), f u with hadef
  have hle : ∀ i : ℕ, (i : ℝ) * ℓ ≤ (i + 1 : ℕ) * ℓ := fun i => by
    push_cast
    nlinarith
  have hlen : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) * ℓ - i * ℓ = ℓ := fun i => by push_cast; ring
  have ha0 : ∀ i, 0 ≤ a i := fun i =>
    intervalIntegral.integral_nonneg (hle i) fun u _ => hf0 u
  have haup : ∀ i, a i ≤ ℓ * f (i * ℓ) := by
    intro i
    have h := intervalIntegral.integral_mono_on (μ := volume) (hle i) (hfc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun u hu => hfa hu.1)
    rwa [intervalIntegral.integral_const, hlen, smul_eq_mul] at h
  have halo : ∀ i, ℓ * f ((i + 1 : ℕ) * ℓ) ≤ a i := by
    intro i
    have h := intervalIntegral.integral_mono_on (μ := volume) (hle i)
      (continuous_const.intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _) (fun u hu => hfa hu.2)
    rwa [intervalIntegral.integral_const, hlen, smul_eq_mul] at h
  -- `∑ a_i = F_∞`
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, a i = ∫ u in (0 : ℝ)..(N * ℓ), f u := by
    intro N
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
      (a := fun i : ℕ => (i : ℝ) * ℓ) (n := N) fun k _ => hfc.intervalIntegrable _ _
    simp only [Nat.cast_zero, zero_mul] at h
    rw [← h]
  have hlim : Tendsto (fun N : ℕ => ∫ u in (0 : ℝ)..(N * ℓ), f u) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), f u)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hfi
      (tendsto_natCast_atTop_atTop.atTop_mul_const hℓ)
  have ha : HasSum a (maternLineLimit c ω) := by
    rw [maternLineLimit_eq, ← hAdef]
    exact (hasSum_iff_tendsto_nat_of_nonneg ha0 _).2 (by simpa only [hpart] using hlim)
  -- `ℓF_q = ∑ ℓ f((i+1)ℓ)`
  have hb : HasSum (fun i : ℕ => ℓ * f ((i + 1 : ℕ) * ℓ)) (ℓ * maternExponent q c ω) := by
    refine ((maternExponent_hasSum hq hc ω).mul_left ℓ).congr_fun fun i => ?_
    rw [maternTerm_eq_limitIntegrand hq]
  have hshift : HasSum (fun i => a (i + 1)) (maternLineLimit c ω - a 0) := by
    have h := (hasSum_nat_add_iff' 1).2 ha
    simpa using h
  have hup : ℓ * maternExponent q c ω ≤ maternLineLimit c ω := hasSum_le halo hb ha
  have hlo : maternLineLimit c ω - a 0 ≤ ℓ * maternExponent q c ω := by
    refine hasSum_le (fun i => ?_) hshift hb
    have := haup (i + 1)
    simpa using this
  have h0 : a 0 ≤ ℓ * Real.log (1 + A) := by
    have := haup 0
    simpa [hfdef, limitIntegrand] using this
  exact ⟨by linarith, by linarith⟩

/-! ## The limit -/

/-- `log q → 0` as `q ↓ 1`. -/
theorem tendsto_log_nhdsGT_one : Tendsto Real.log (𝓝[>] 1) (𝓝 0) := by
  have h := (Real.continuousAt_log one_ne_zero).tendsto
  rw [Real.log_one] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **`ℓF_q → F_∞` locally uniformly** as `q ↓ 1`, from the bound. -/
theorem tendstoLocallyUniformly_maternExponent (hc : 0 < c) :
    TendstoLocallyUniformly (fun (q : ℝ) ω => Real.log q * maternExponent q c ω)
      (maternLineLimit c) (𝓝[>] 1) := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  set K := Real.log (1 + c ^ 2 * (|x| + 1) ^ 2) with hKdef
  have hK : 0 ≤ K := Real.log_nonneg (by nlinarith [sq_nonneg (c * (|x| + 1))])
  have hev : ∀ᶠ q in 𝓝[>] (1 : ℝ), Real.log q < ε / (K + 1) :=
    (tendsto_order.1 tendsto_log_nhdsGT_one).2 _ (by positivity)
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with q hq hq1
  intro y hy
  have hq1' : 1 < q := hq1
  obtain ⟨h1, h2⟩ := matern_pyramid_line_4_bound hq1' hc y
  have hℓ : 0 < Real.log q := Real.log_pos hq1'
  have hy' : |y| < |x| + 1 := by
    have h := Metric.mem_ball.1 hy
    rw [Real.dist_eq] at h
    linarith [abs_sub_abs_le_abs_sub y x]
  have hy2 : y ^ 2 ≤ (|x| + 1) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hy'.le 2
  have hlogy : Real.log (1 + c ^ 2 * y ^ 2) ≤ K :=
    Real.log_le_log (by positivity) (by nlinarith [sq_nonneg c])
  rw [Real.dist_eq, abs_of_nonneg h1]
  have h3 : Real.log q * (K + 1) < ε := by rwa [lt_div_iff₀ (by positivity)] at hq
  calc maternLineLimit c y - Real.log q * maternExponent q c y
      ≤ Real.log q * Real.log (1 + c ^ 2 * y ^ 2) := h2
    _ ≤ Real.log q * K := mul_le_mul_of_nonneg_left hlogy hℓ.le
    _ < ε := by nlinarith

/-- **The form in `θ`**: `F_∞(ω) = ∫_{1/c}^∞ log(1 + ω²/θ²) dθ/θ`, by `θ = eᵘ/c`. -/
theorem maternLineLimit_theta (hc : 0 < c) (ω : ℝ) :
    maternLineLimit c ω = ∫ θ in Ioi (1 / c), Real.log (1 + ω ^ 2 / θ ^ 2) / θ := by
  have himg : (fun u => Real.exp u / c) '' Ioi 0 = Ioi (1 / c) := by
    ext θ
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_lt_div_of_pos_right (Real.one_lt_exp_iff.2 hu) hc
    · intro hθ
      have hcθ : 1 < θ * c := (div_lt_iff₀ hc).1 hθ
      refine ⟨Real.log (θ * c), Real.log_pos hcθ, ?_⟩
      rw [Real.exp_log (by linarith)]
      field_simp
  have hinj : InjOn (fun u => Real.exp u / c) (Ioi 0) := fun u _ v _ h =>
    Real.exp_injective ((div_left_inj' hc.ne').1 h)
  have hder : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun u => Real.exp u / c) (Real.exp u / c) (Ioi 0) u :=
    fun u _ => ((Real.hasDerivAt_exp u).div_const c).hasDerivWithinAt
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj,
    maternLineLimit]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  have he := Real.exp_pos u
  rw [abs_of_pos (div_pos he hc), smul_eq_mul, show -2 * u = -(u + u) by ring, Real.exp_neg,
    Real.exp_add]
  field_simp

/-- `∫₀^A log(1 + v) dv/v = 2∫₀^∞ log(1 + Ae^{-2u}) du`, by `v = Ae^{-2u}`. -/
theorem integral_log_one_add_div {A : ℝ} (hA : 0 < A) :
    ∫ v in (0 : ℝ)..A, Real.log (1 + v) / v = 2 * ∫ u in Ioi (0 : ℝ), limitIntegrand A u := by
  have himg : (fun u => A * Real.exp (-2 * u)) '' Ioi 0 = Ioo 0 A := by
    ext v
    simp only [mem_image, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨by positivity, ?_⟩
      have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.2 (by linarith)
      nlinarith
    · rintro ⟨hv0, hvA⟩
      have hvA' : v / A < 1 := (div_lt_one hA).2 hvA
      have hlog : Real.log (v / A) < 0 := Real.log_neg (by positivity) hvA'
      refine ⟨-Real.log (v / A) / 2, by linarith, ?_⟩
      rw [show -2 * (-Real.log (v / A) / 2) = Real.log (v / A) by ring,
        Real.exp_log (by positivity)]
      field_simp
  have hinj : InjOn (fun u => A * Real.exp (-2 * u)) (Ioi 0) := fun u _ v _ h => by
    have h' : Real.exp (-2 * u) = Real.exp (-2 * v) := (mul_right_inj' hA.ne').1 h
    have := Real.exp_injective h'
    linarith
  have hder : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u => A * Real.exp (-2 * u))
      (A * (Real.exp (-2 * u) * (-2))) (Ioi 0) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => -2 * u) (-2) u := by
      simpa using (hasDerivAt_id u).const_mul (-2 : ℝ)
    exact (h1.exp.const_mul A).hasDerivWithinAt
  rw [intervalIntegral.integral_of_le hA.le, integral_Ioc_eq_integral_Ioo, ← himg,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  have he := Real.exp_pos (-2 * u)
  rw [abs_of_neg (by nlinarith), smul_eq_mul, limitIntegrand]
  field_simp

/-- `∫₀^{-A} log(1 - u) du/u = ∫₀^A log(1 + v) dv/v`. -/
theorem integral_log_one_sub_div (A : ℝ) :
    ∫ u in (0 : ℝ)..(-A), Real.log (1 - u) / u = ∫ v in (0 : ℝ)..A, Real.log (1 + v) / v := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -A)
    (fun v => -(Real.log (1 + v) / v))
  simp only [neg_neg, neg_zero, intervalIntegral.integral_neg] at h
  rw [intervalIntegral.integral_symm 0 A, neg_neg] at h
  rw [← h, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [div_neg, neg_neg, sub_eq_add_neg]

/-- **The dilogarithm form**: `F_∞(ω) = -½ Li₂(-c²ω²)`. -/
theorem maternLineLimit_eq_dilog (c ω : ℝ) : maternLineLimit c ω = maternLimitExponent c ω := by
  rw [maternLimitExponent, dilog, integral_log_one_sub_div]
  rcases (sq_nonneg (c * ω)).lt_or_eq with h | h
  · have hA : 0 < c ^ 2 * ω ^ 2 := by rw [← mul_pow]; exact h
    rw [integral_log_one_add_div hA, maternLineLimit_eq]
    ring
  · have hA : c ^ 2 * ω ^ 2 = 0 := by rw [← mul_pow]; exact h.symm
    rw [maternLineLimit_eq, hA]
    simp [limitIntegrand]

/-! ## The profile of `F_∞` -/

/-- `k_∞(x) := 2∫_{1/c}^∞ e^{-θx} dθ/θ` for `x > 0`, and `0` otherwise. -/
noncomputable def limitProfile (c x : ℝ) : ℝ :=
  if 0 < x then 2 * ∫ θ in Ioi (1 / c), Real.exp (-(θ * x)) / θ else 0

theorem mem_Ioi_inv_pos (hc : 0 < c) {θ : ℝ} (hθ : θ ∈ Ioi (1 / c)) : 0 < θ :=
  lt_trans (by positivity) hθ

theorem integrableOn_limitKernel (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun θ => Real.exp (-(θ * x)) / θ) (Ioi (1 / c)) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi (1 / c) hx).const_mul c)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ hθ => ?_)
  have hθ0 := mem_Ioi_inv_pos hc hθ
  have hθc : 1 < θ * c := (div_lt_iff₀ hc).1 hθ
  have he := Real.exp_pos (-(θ * x))
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg he.le hθ0.le), show -x * θ = -(θ * x) by ring,
    div_le_iff₀ hθ0]
  nlinarith

theorem limitProfile_nonneg (hc : 0 < c) (x : ℝ) : 0 ≤ limitProfile c x := by
  unfold limitProfile
  split_ifs
  · refine mul_nonneg zero_le_two (setIntegral_nonneg measurableSet_Ioi fun θ hθ => ?_)
    exact div_nonneg (Real.exp_pos _).le (mem_Ioi_inv_pos hc hθ).le
  · exact le_rfl

theorem limitProfile_antitone (hc : 0 < c) : AntitoneOn (limitProfile c) (Ioi 0) := by
  intro x hx y hy hxy
  simp only [limitProfile, if_pos (show (0 : ℝ) < x from hx), if_pos (show (0 : ℝ) < y from hy)]
  refine mul_le_mul_of_nonneg_left (setIntegral_mono_on (integrableOn_limitKernel hc hy)
    (integrableOn_limitKernel hc hx) measurableSet_Ioi fun θ hθ => ?_) zero_le_two
  have hθ0 := mem_Ioi_inv_pos hc hθ
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hθ0.le

/-- `ofReal(C k_∞(x)) = ∫⁻_{θ > 1/c} ofReal(2C e^{-θx}/θ)`. -/
theorem ofReal_mul_limitProfile (hc : 0 < c) {x : ℝ} (hx : 0 < x) {C : ℝ} (hC : 0 ≤ C) :
    ENNReal.ofReal (C * limitProfile c x) =
      ∫⁻ θ in Ioi (1 / c), ENNReal.ofReal (2 * C * (Real.exp (-(θ * x)) / θ)) := by
  rw [limitProfile, if_pos hx, ← mul_assoc, mul_comm C 2, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal ((integrableOn_limitKernel hc hx).const_mul _)]
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ hθ => ?_)
  have hθ0 := mem_Ioi_inv_pos hc hθ
  have := Real.exp_pos (-(θ * x))
  simp only [Pi.zero_apply]
  positivity

/-- `∫₀^∞ x k_∞(x) dx < ∞`: by Tonelli, `∫_{1/c}^∞ 2θ^{-3} dθ`. -/
theorem lintegral_mul_limitProfile (hc : 0 < c) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x * limitProfile c x) ≠ ⊤ := by
  rw [setLIntegral_congr_fun measurableSet_Ioi fun x hx =>
    ofReal_mul_limitProfile hc (show (0 : ℝ) < x from hx) (le_of_lt hx)]
  rw [lintegral_lintegral_swap (Measurable.aemeasurable (by fun_prop))]
  have e2 : ∀ θ ∈ Ioi (1 / c), ∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (2 * x * (Real.exp (-(θ * x)) / θ)) = ENNReal.ofReal (2 / θ * (θ ^ 2)⁻¹) := by
    intro θ hθ
    have hθ0 := mem_Ioi_inv_pos hc hθ
    rw [← lintegral_mul_exp_neg hθ0 (2 / θ) (by positivity)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    congr 1
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi e2]
  have hint : IntegrableOn (fun θ : ℝ => 2 * θ ^ (-3 : ℝ)) (Ioi (1 / c)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by positivity)).const_mul 2
  refine ne_of_lt (lt_of_eq_of_lt (setLIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_)
    hint.lintegral_lt_top)
  have hθ0 := mem_Ioi_inv_pos hc hθ
  congr 1
  rw [Real.rpow_neg hθ0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-- **The profile of `F_∞`**, with `a = 0` and `k = k_∞`. -/
noncomputable def limitSDProfile (hc : 0 < c) : SDProfile where
  a := 0
  k := limitProfile c
  a_nonneg := le_rfl
  k_nonneg := fun x _ => limitProfile_nonneg hc x
  k_antitone := limitProfile_antitone hc
  k_zero := by simp [limitProfile]
  integrable_near_zero := ne_top_of_le_ne_top (lintegral_mul_limitProfile hc)
    (lintegral_mono_set Ioo_subset_Ioi_self)
  integrable_at_top := by
    refine ne_top_of_le_ne_top (lintegral_mul_limitProfile hc) ?_
    refine le_trans (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun x hx => ENNReal.ofReal_le_ofReal ?_)))
      (lintegral_mono_set (Ioi_subset_Ioi zero_le_one))
    have hx1 : (1 : ℝ) < x := hx
    have hk := limitProfile_nonneg hc x
    calc limitProfile c x / x ≤ limitProfile c x := div_le_self hk hx1.le
      _ ≤ x * limitProfile c x := le_mul_of_one_le_left hk hx1.le

/-- `F_∞` is the exponent of `(0, k_∞)`: Tonelli and `lem:laplace-atoms-admissible`(1). -/
theorem limitSDProfile_exponent (hc : 0 < c) (ω : ℝ) :
    (limitSDProfile hc).exponent ω = maternLineLimit c ω := by
  rw [maternLineLimit_theta hc ω, SDProfile.exponent, SDProfile.exponentL]
  simp only [limitSDProfile, zero_mul, ENNReal.ofReal_zero, zero_add]
  have e1 : ∀ x ∈ Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * limitProfile c x / x) =
      ∫⁻ θ in Ioi (1 / c), ENNReal.ofReal
        (2 * ((1 - Real.cos (ω * x)) / x) * (Real.exp (-(θ * x)) / θ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [show (1 - Real.cos (ω * x)) * limitProfile c x / x =
      (1 - Real.cos (ω * x)) / x * limitProfile c x by ring]
    exact ofReal_mul_limitProfile hc hx0
      (div_nonneg (sub_nonneg.2 (Real.cos_le_one _)) hx0.le)
  rw [setLIntegral_congr_fun measurableSet_Ioi e1,
    lintegral_lintegral_swap (Measurable.aemeasurable (by fun_prop))]
  have e2 : ∀ θ ∈ Ioi (1 / c), ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
      (2 * ((1 - Real.cos (ω * x)) / x) * (Real.exp (-(θ * x)) / θ)) =
        ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ ^ 2) / θ) := by
    intro θ hθ
    have hθ0 := mem_Ioi_inv_pos hc hθ
    have h1 := laplace_atoms_admissible_1 hθ0 ω
    have e : Real.log (1 + ω ^ 2 / θ ^ 2) / θ =
        ∫ x in Ioi (0 : ℝ), 2 / θ * ((1 - Real.cos (ω * x)) * Real.exp (-(θ * x)) / x) := by
      rw [integral_const_mul, h1]
      field_simp
    rw [e, ofReal_integral_eq_lintegral_ofReal ((integrableOn_laplaceAtom hθ0 ω).const_mul _)]
    · refine setLIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      congr 1
      ring
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
      have hx0 : (0 : ℝ) < x := hx
      have := Real.exp_pos (-(θ * x))
      have := sub_nonneg.2 (Real.cos_le_one (ω * x))
      simp only [Pi.zero_apply]
      positivity
  rw [setLIntegral_congr_fun measurableSet_Ioi e2]
  refine (integral_eq_lintegral_of_nonneg_ae ?_
    (Measurable.aestronglyMeasurable (by fun_prop))).symm
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ hθ => ?_)
  have hθ0 := mem_Ioi_inv_pos hc hθ
  have : 0 ≤ Real.log (1 + ω ^ 2 / θ ^ 2) :=
    Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  simp only [Pi.zero_apply]
  positivity

/-- **`thm:matern-pyramid-line`(4), the limit and its forms (A.e8).** `ℓF_q → F_∞` locally
uniformly as `q ↓ 1`; `F_∞(ω) = -½ Li₂(-c²ω²) = ∫_{1/c}^∞ log(1 + ω²/θ²) dθ/θ`; and `F_∞` is
admissible with `a = 0` and profile `k_∞(x) = 2∫_{1/c}^∞ e^{-θx} dθ/θ`. -/
theorem matern_pyramid_line_4_limit {c : ℝ} (hc : 0 < c) :
    TendstoLocallyUniformly (fun (q : ℝ) ω => Real.log q * maternExponent q c ω)
        (maternLineLimit c) (𝓝[>] 1) ∧
      (∀ ω : ℝ, maternLineLimit c ω = maternLimitExponent c ω ∧
        maternLineLimit c ω = ∫ θ in Ioi (1 / c), Real.log (1 + ω ^ 2 / θ ^ 2) / θ) ∧
      ∃ P : SDProfile, P.a = 0 ∧
        (∀ x : ℝ, 0 < x → P.k x = 2 * ∫ θ in Ioi (1 / c), Real.exp (-(θ * x)) / θ) ∧
        ∀ ω : ℝ, maternLineLimit c ω = P.exponent ω :=
  ⟨tendstoLocallyUniformly_maternExponent hc,
    fun ω => ⟨maternLineLimit_eq_dilog c ω, maternLineLimit_theta hc ω⟩,
    ⟨limitSDProfile hc, rfl, fun _ hx => if_pos hx, fun ω => (limitSDProfile_exponent hc ω).symm⟩⟩

/-! ## The laws -/

/-- Pointwise, `ℓF_q(y) → F_∞(y)` as `q ↓ 1`. -/
theorem tendsto_maternExponent_at (hc : 0 < c) (y : ℝ) :
    Tendsto (fun q => Real.log q * maternExponent q c y) (𝓝[>] 1) (𝓝 (maternLineLimit c y)) :=
  (tendstoLocallyUniformlyOn_univ.2 (tendstoLocallyUniformly_maternExponent hc)).tendsto_at
    (mem_univ y)

/-- For a profile `P`, `a ≥ 0` and `t > 0`, the law with the exponent `aF(t ·)` exists
(`lem:line-exponent-data`(1)). -/
theorem exists_law_smul_dilate (P : SDProfile) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ ω : ℝ, charFun ν ω = ((Real.exp (-(a * P.exponent (t * ω))) : ℝ) : ℂ) := by
  obtain ⟨ν, ⟨hp, -, -, hcf⟩, -⟩ := line_exponent_data_1 (fun ω => a * P.exponent (t * ω))
    ⟨dilatePair (P.smul ha) ht, fun ω => by rw [dilatePair_exponent, SDProfile.exponent_smul]⟩
  exact ⟨ν, hp, hcf⟩

/-- `F_∞(y) > 0` for `y ≠ 0`: the bound at `q = e` and the first term of `F_e`. -/
theorem maternLineLimit_pos (hc : 0 < c) {y : ℝ} (hy : y ≠ 0) : 0 < maternLineLimit c y := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
  have h1 := (matern_pyramid_line_4_bound he hc y).1
  rw [Real.log_exp, one_mul] at h1
  have hs := summable_maternExponent he hc y
  have hterm : 0 < Real.log (1 + c ^ 2 * y ^ 2 / Real.exp 1 ^ (2 * (0 + 1))) :=
    Real.log_pos (lt_add_of_pos_right _ (by positivity))
  have hle : Real.log (1 + c ^ 2 * y ^ 2 / Real.exp 1 ^ (2 * (0 + 1))) ≤
      maternExponent (Real.exp 1) c y :=
    hs.le_tsum 0 fun j _ => Real.log_nonneg (le_add_of_nonneg_right (by positivity))
  linarith

/-- For `y ≠ 0`, `F_q(y) → ∞` as `q ↓ 1`, so `e^{-F_q(y)} → 0`. -/
theorem tendsto_exp_neg_maternExponent (hc : 0 < c) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun q => Real.exp (-maternExponent q c y)) (𝓝[>] 1) (𝓝 0) := by
  set L := Real.log (1 + c ^ 2 * y ^ 2)
  have hpos := maternLineLimit_pos hc hy
  have hlog : Tendsto Real.log (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_log_nhdsGT_one, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact Real.log_pos hq
  have hinf : Tendsto (fun q => maternLineLimit c y * (Real.log q)⁻¹ - L) (𝓝[>] 1) atTop :=
    tendsto_atTop_add_const_right _ _
      ((tendsto_inv_nhdsGT_zero.comp hlog).const_mul_atTop hpos)
  have hF : Tendsto (fun q => maternExponent q c y) (𝓝[>] 1) atTop := by
    refine tendsto_atTop_mono' _ ?_ hinf
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq1 : 1 < q := hq
    have hℓ : 0 < Real.log q := Real.log_pos hq1
    have h2 := (matern_pyramid_line_4_bound hq1 hc y).2
    have : maternLineLimit c y * (Real.log q)⁻¹ ≤ maternExponent q c y + L := by
      rw [mul_inv_le_iff₀ hℓ]
      linarith
    linarith
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hF

/-- **`thm:matern-pyramid-line`(4), the laws.** For `t > 0` the laws with exponent `ℓF_q(t ·)`
exist and converge weakly as `q ↓ 1` to the law with exponent `F_∞(t ·)`, while the kernels `μ_t`
of the Matérn pyramids have no weak limit. -/
theorem matern_pyramid_line_4_laws {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    (∀ q : ℝ, 1 < q → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ ω : ℝ,
        charFun ν ω = ((Real.exp (-(Real.log q * maternExponent q c (t * ω))) : ℝ) : ℂ)) ∧
      (∃ ν₀ : Measure ℝ, IsProbabilityMeasure ν₀ ∧ ∀ ω : ℝ,
        charFun ν₀ ω = ((Real.exp (-maternLineLimit c (t * ω)) : ℝ) : ℂ)) ∧
      (∀ ν : ℝ → Measure ℝ, (∀ q : ℝ, 1 < q → IsProbabilityMeasure (ν q) ∧ ∀ ω : ℝ,
          charFun (ν q) ω = ((Real.exp (-(Real.log q * maternExponent q c (t * ω))) : ℝ) : ℂ)) →
        ∀ ν₀ : Measure ℝ, IsProbabilityMeasure ν₀ →
          (∀ ω : ℝ, charFun ν₀ ω = ((Real.exp (-maternLineLimit c (t * ω)) : ℝ) : ℂ)) →
          ∀ φ : ℝ →ᵇ ℝ, Tendsto (fun q => ∫ x, φ x ∂(ν q)) (𝓝[>] 1) (𝓝 (∫ x, φ x ∂ν₀))) ∧
      ∀ μ : ℝ → ℝ → ℝ → Measure ℝ, (∀ q : ℝ, 1 < q → IsMaternPyramid q c (μ q)) →
        ¬ ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ φ : ℝ →ᵇ ℝ,
          Tendsto (fun q => ∫ x, φ x ∂(μ q 0 t)) (𝓝[>] 1) (𝓝 (∫ x, φ x ∂ν)) := by
  refine ⟨fun q hq => ?_, ?_, ?_, ?_⟩
  · -- the laws of `ℓF_q(t ·)`
    obtain ⟨P, -, -, hP⟩ := exists_maternProfile hq hc
    obtain ⟨ν, hν, hcf⟩ := exists_law_smul_dilate P (Real.log_pos hq).le ht
    exact ⟨ν, hν, fun ω => by rw [hcf, hP]⟩
  · -- the law of `F_∞(t ·)`
    obtain ⟨ν, hν, hcf⟩ := exists_law_smul_dilate (limitSDProfile hc) zero_le_one ht
    exact ⟨ν, hν, fun ω => by rw [hcf, one_mul, limitSDProfile_exponent]⟩
  · -- weak convergence: Lévy's continuity theorem along every sequence `q_n ↓ 1`
    intro ν hν ν₀ hν₀ hcf₀ φ
    rw [tendsto_iff_seq_tendsto]
    intro x hx
    have hev : ∀ᶠ n in atTop, 1 < x n := hx self_mem_nhdsWithin
    classical
    let μs : ℕ → ProbabilityMeasure ℝ := fun n =>
      if h : 1 < x n then ⟨ν (x n), (hν _ h).1⟩ else ⟨ν₀, hν₀⟩
    let μ₀ : ProbabilityMeasure ℝ := ⟨ν₀, hν₀⟩
    have hμs : ∀ n, 1 < x n → (μs n : Measure ℝ) = ν (x n) := fun n hn => by
      simp only [μs, dif_pos hn]
      rfl
    have hcf : ∀ ω : ℝ, Tendsto (fun n => charFun (μs n : Measure ℝ) ω) atTop
        (𝓝 (charFun (μ₀ : Measure ℝ) ω)) := by
      intro ω
      have hlim := (Complex.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp
        ((tendsto_maternExponent_at hc (t * ω)).comp hx).neg)
      rw [show (μ₀ : Measure ℝ) = ν₀ from rfl, hcf₀ ω]
      refine hlim.congr' ?_
      filter_upwards [hev] with n hn
      rw [hμs n hn, (hν _ hn).2 ω]
      rfl
    have hw := ProbabilityMeasure.tendsto_of_tendsto_charFun hcf
    have hφ := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hw φ
    refine hφ.congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp_apply]
    rw [hμs n hn]
  · -- the kernels: the transforms tend to `𝟙_{ω = 0}`, not continuous at `0`
    rintro μ hμ ⟨ν, hν, hconv⟩
    have hcos : ∀ ω : ℝ, ω ≠ 0 → ScaleSpace.fourierCos ν ω = 0 := by
      intro ω hω
      let φ : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
        ⟨fun x => Real.cos (ω * x), by fun_prop⟩ 2 fun x y => by
          rw [Real.dist_eq]
          have := Real.abs_cos_le_one (ω * x)
          have := Real.abs_cos_le_one (ω * y)
          calc |Real.cos (ω * x) - Real.cos (ω * y)| ≤ |Real.cos (ω * x)| + |Real.cos (ω * y)| :=
                abs_sub _ _
            _ ≤ 2 := by linarith
      have h1 := hconv φ
      have hk : ∀ᶠ q in 𝓝[>] (1 : ℝ),
          ∫ x, φ x ∂(μ q 0 t) = Real.exp (-maternExponent q c (t * ω)) := by
        filter_upwards [self_mem_nhdsWithin] with q hq
        have hm := (hμ q hq) 0 t le_rfl ht.le
        haveI := hm.1
        have e := ScaleSpace.fourierCos_eq_charFun_re (μ q 0 t) ω
        rw [hm.2 ω, Complex.ofReal_re] at e
        change ScaleSpace.fourierCos (μ q 0 t) ω = _
        rw [e]
        beta_reduce
        rw [zero_mul, maternExponent_zero, sub_zero, Real.norm_eq_abs, maternExponent_mul_abs]
      have h2 := (tendsto_exp_neg_maternExponent hc (mul_ne_zero ht.ne' hω)).congr'
        (hk.mono fun q h => h.symm)
      exact tendsto_nhds_unique h1 h2
    haveI := hν
    have hc0 : Tendsto (ScaleSpace.fourierCos ν) (𝓝[≠] 0) (𝓝 (ScaleSpace.fourierCos ν 0)) :=
      (ScaleSpace.continuous_fourierCos ν).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hc1 : Tendsto (ScaleSpace.fourierCos ν) (𝓝[≠] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun ω hω => (hcos ω hω).symm)
    have h := tendsto_nhds_unique hc0 hc1
    rw [ScaleSpace.fourierCos_zero] at h
    exact one_ne_zero h

end Pyramids
