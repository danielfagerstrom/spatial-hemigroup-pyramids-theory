/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.LineAppendix
import Pyramids.Defs.Cited
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# `lem:laplace-atoms-admissible`: sums of Laplace atoms are admissible

Blueprint: `blueprint/src/parts/A1-line.tex`, `lem:laplace-atoms-admissible`. Phase 5, wave 1d.

* **(1), the Frullani-type identity.** Both sides vanish at `ω = 0`. The left side is
  differentiated under the integral (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), the
  derivative `sin(ωx)e^{-ϑx}` being dominated by `e^{-ϑx}`; its integral is the imaginary part of
  `∫₀^∞ e^{(-ϑ + iω)x} dx = 1/(ϑ - iω)`, which is `ω/(ϑ² + ω²)`, the derivative of the right side.
  Two functions with the same derivative everywhere and the same value at `0` agree.
* **(2).** `0 ≤ log(1 + y) ≤ y` gives the convergence and the bound. The bound
  `ϑⁿe^{-ϑx} ≤ (n+2)!x^{-(n+2)}ϑ^{-2}` (from `yⁿ⁺²/(n+2)! ≤ eʸ`) makes every series
  `∑ (-ϑᵢ)ⁿe^{-ϑᵢx}` converge locally uniformly on `(0,∞)`, so the profile is differentiated term
  by term (`hasDerivAt_tsum_of_isPreconnected`): its `n`-th derivative is
  `2∑ (-ϑᵢ)ⁿe^{-ϑᵢx}`, and `(-1)ⁿ` times it is `2∑ ϑᵢⁿe^{-ϑᵢx} ≥ 0`. The integral bound uses
  `min(1, x²)/x ≤ x` and `∫₀^∞ x e^{-ϑx} dx = ϑ^{-2}`, with Tonelli (`lintegral_tsum`); it gives
  `2∑ϑᵢ^{-2}`, the constant of the statement (`4` until review round 3, supp.S10). The exponent
  of the profile is computed by Tonelli and (1), term by term.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter
open ScaleSpace (SDProfile)
open scoped Topology ENNReal Nat

/-! ## Elementary bounds -/

/-- `1 - cos y ≤ |y|`. -/
theorem one_sub_cos_le_abs (y : ℝ) : 1 - Real.cos y ≤ |y| := by
  rcases le_or_gt |y| 2 with h | h
  · have h1 := Real.one_sub_sq_div_two_le_cos (x := y)
    have h2 : y ^ 2 / 2 ≤ |y| := by
      have : y ^ 2 = |y| * |y| := by rw [← sq_abs y, sq]
      nlinarith [abs_nonneg y]
    linarith
  · have := Real.neg_one_le_cos y
    linarith

/-- `ϑⁿe^{-ϑx} ≤ (n+2)!x^{-(n+2)}ϑ^{-2}`. -/
theorem pow_mul_exp_neg_le {θ x : ℝ} (hθ : 0 < θ) (hx : 0 < x) (n : ℕ) :
    θ ^ n * Real.exp (-(θ * x)) ≤ ((n + 2)! / x ^ (n + 2)) * (θ ^ 2)⁻¹ := by
  have h := Real.pow_div_factorial_le_exp _ (mul_pos hθ hx).le (n + 2)
  have hf : (0 : ℝ) < (n + 2)! := by positivity
  rw [div_le_iff₀ hf] at h
  have hE := Real.exp_pos (θ * x)
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hx0 : x ≠ 0 := hx.ne'
  calc θ ^ n * Real.exp (-(θ * x))
      = (θ * x) ^ (n + 2) * (Real.exp (θ * x))⁻¹ * (x ^ (n + 2))⁻¹ * (θ ^ 2)⁻¹ := by
        rw [Real.exp_neg]
        field_simp
        ring
    _ ≤ (n + 2)! * (x ^ (n + 2))⁻¹ * (θ ^ 2)⁻¹ := by
        gcongr
        rw [← div_eq_mul_inv, div_le_iff₀ hE]
        linarith
    _ = _ := by ring

theorem summable_pow_mul_exp_neg {ι : Type*} {θ : ι → ℝ} (hθ : ∀ i, 0 < θ i)
    (hsum : Summable fun i => (θ i ^ 2)⁻¹) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable fun i => θ i ^ n * Real.exp (-(θ i * x)) :=
  Summable.of_nonneg_of_le (fun i => by have := (hθ i).le; positivity)
    (fun i => pow_mul_exp_neg_le (hθ i) hx n) (hsum.mul_left _)

/-! ## Clause (1) -/

/-- `∫₀^∞ sin(ωx) e^{-ϑx} dx = ω/(ϑ² + ω²)`. -/
theorem integral_sin_mul_exp_neg {θ : ℝ} (hθ : 0 < θ) (ω : ℝ) :
    ∫ x in Ioi (0 : ℝ), Real.sin (ω * x) * Real.exp (-(θ * x)) = ω / (θ ^ 2 + ω ^ 2) := by
  set a : ℂ := -θ + ω * Complex.I with ha
  have hre : a.re < 0 := by simp [ha, hθ]
  have hint := integrableOn_exp_mul_complex_Ioi hre 0
  have h := integral_exp_mul_complex_Ioi hre 0
  have him := congrArg Complex.im h
  have hI : ∫ x in Ioi (0 : ℝ), (Complex.exp (a * x)).im =
      (∫ x in Ioi (0 : ℝ), Complex.exp (a * x)).im := integral_im hint
  rw [← hI] at him
  have hpt : ∀ x : ℝ, (Complex.exp (a * x)).im = Real.sin (ω * x) * Real.exp (-(θ * x)) := by
    intro x
    rw [Complex.exp_im]
    simp [ha]
    ring_nf
  simp_rw [hpt] at him
  rw [him]
  have hne : (θ : ℝ) ^ 2 + ω ^ 2 ≠ 0 := by positivity
  simp [ha, Complex.div_im, Complex.normSq]
  field_simp

/-- The integrand of (1) is integrable on `(0,∞)`. -/
theorem integrableOn_laplaceAtom {θ : ℝ} (hθ : 0 < θ) (ω : ℝ) :
    IntegrableOn (fun x => (1 - Real.cos (ω * x)) * Real.exp (-(θ * x)) / x) (Ioi 0) := by
  have hb : IntegrableOn (fun x => |ω| * Real.exp (-θ * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hθ).const_mul _
  refine Integrable.mono' hb ?_ ?_
  · exact (by fun_prop : Measurable fun x : ℝ =>
      (1 - Real.cos (ω * x)) * Real.exp (-(θ * x)) / x).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx : 0 < x := hx
    have h1 := one_sub_cos_le_abs (ω * x)
    have h2 : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg h2, abs_of_pos (Real.exp_pos _),
      abs_of_pos hx, div_le_iff₀ hx, neg_mul]
    rw [abs_mul, abs_of_pos hx] at h1
    have := Real.exp_pos (-(θ * x))
    nlinarith

/-- **`lem:laplace-atoms-admissible`(1)**, the Frullani-type identity
`∫₀^∞ (1 - cos ωx) e^{-ϑx} dx/x = ½ log(1 + ω²/ϑ²)`. -/
theorem laplace_atoms_admissible_1 {θ : ℝ} (hθ : 0 < θ) (ω : ℝ) :
    ∫ x in Ioi (0 : ℝ), (1 - Real.cos (ω * x)) * Real.exp (-(θ * x)) / x =
      1 / 2 * Real.log (1 + ω ^ 2 / θ ^ 2) := by
  set L : ℝ → ℝ := fun w => ∫ x in Ioi (0 : ℝ), (1 - Real.cos (w * x)) * Real.exp (-(θ * x)) / x
  set R : ℝ → ℝ := fun w => 1 / 2 * Real.log (1 + w ^ 2 / θ ^ 2)
  have hL : ∀ w, HasDerivAt L (w / (θ ^ 2 + w ^ 2)) w := by
    intro w
    rw [← integral_sin_mul_exp_neg hθ w]
    have hb : IntegrableOn (fun x => Real.exp (-θ * x)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hθ
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun w x => (1 - Real.cos (w * x)) * Real.exp (-(θ * x)) / x)
      (F' := fun w x => Real.sin (w * x) * Real.exp (-(θ * x)))
      (bound := fun x => Real.exp (-θ * x)) (Metric.ball_mem_nhds w one_pos)
      (Eventually.of_forall fun w' => (by fun_prop : Measurable fun x : ℝ =>
        (1 - Real.cos (w' * x)) * Real.exp (-(θ * x)) / x).aestronglyMeasurable)
      (integrableOn_laplaceAtom hθ w)
      ((by fun_prop : Measurable fun x : ℝ =>
        Real.sin (w * x) * Real.exp (-(θ * x))).aestronglyMeasurable)
      (Eventually.of_forall fun x w' _ => ?_) hb ?_).2
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_sin_le_one _)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx w' _ => ?_)
      have hx : (x : ℝ) ≠ 0 := (show (0 : ℝ) < x from hx).ne'
      have h1 : HasDerivAt (fun w => w * x) x w' := by
        simpa using (hasDerivAt_id w').mul_const x
      have h2 := ((h1.cos).const_sub 1).mul_const (Real.exp (-(θ * x)))
      refine (h2.div_const x).congr_deriv ?_
      rw [div_eq_iff hx]
      ring
  have hR : ∀ w, HasDerivAt R (w / (θ ^ 2 + w ^ 2)) w := by
    intro w
    have hpos : 0 < 1 + w ^ 2 / θ ^ 2 := by positivity
    have h1 : HasDerivAt (fun w : ℝ => 1 + w ^ 2 / θ ^ 2) (2 * w / θ ^ 2) w := by
      refine (((hasDerivAt_pow 2 w).div_const (θ ^ 2)).const_add 1).congr_deriv ?_
      norm_num
    refine ((h1.log hpos.ne').const_mul (1 / 2)).congr_deriv ?_
    have hθ2 : θ ^ 2 ≠ 0 := by positivity
    field_simp
  have hconst : ∀ w, L w - R w = L 0 - R 0 := by
    intro w
    refine is_const_of_deriv_eq_zero (f := fun w => L w - R w)
      (fun w => ((hL w).sub (hR w)).differentiableAt) (fun w => ?_) w 0
    exact ((hL w).sub (hR w)).deriv.trans (sub_self _)
  have hL0 : L 0 = 0 := by simp [L]
  have hR0 : R 0 = 0 := by simp [R]
  have := hconst ω
  rw [hL0, hR0, sub_zero, sub_eq_zero] at this
  exact this

/-! ## Clause (2) -/

/-- `∫₀^∞ x e^{-ϑx} dx = ϑ⁻²`, with its integrability. -/
theorem integral_mul_exp_neg {θ : ℝ} (hθ : 0 < θ) :
    IntegrableOn (fun x => x * Real.exp (-(θ * x))) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), x * Real.exp (-(θ * x)) = (θ ^ 2)⁻¹ := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hθ
  have hc : ∀ x ∈ Ioi (0 : ℝ), x ^ ((2 : ℝ) - 1) * Real.exp (-(θ * x)) =
      x * Real.exp (-(θ * x)) := by
    intro x _
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hc, Real.Gamma_two, mul_one,
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div, inv_pow] at h
  refine ⟨?_, h⟩
  refine Integrable.of_integral_ne_zero ?_
  rw [h]
  positivity

theorem lintegral_mul_exp_neg {θ : ℝ} (hθ : 0 < θ) (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (c * (x * Real.exp (-(θ * x)))) =
      ENNReal.ofReal (c * (θ ^ 2)⁻¹) := by
  obtain ⟨hi, he⟩ := integral_mul_exp_neg hθ
  rw [← he, ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hi.const_mul c)]
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  have hx : (0 : ℝ) < x := hx
  simp only [Pi.zero_apply]
  have := Real.exp_pos (-(θ * x))
  positivity

/-- **`lem:laplace-atoms-admissible`(2).** The series converges with
`0 ≤ F ≤ (a + ∑ ϑᵢ⁻²)ω²`; `F` is admissible with Gaussian coefficient `a` and the completely
monotone profile `k(x) = 2∑ e^{-ϑᵢx}`, `∫ (1 ∧ x²) k(x) dx/x ≤ 2∑ ϑᵢ⁻²`; and `F ≢ 0` unless
`a = 0` and `I` is empty. -/
theorem laplace_atoms_admissible_2 {ι : Type*} [Countable ι] {a : ℝ} (ha : 0 ≤ a) (θ : ι → ℝ)
    (hθ : ∀ i, 0 < θ i) (hsum : Summable fun i => (θ i ^ 2)⁻¹) (F : ℝ → ℝ)
    (hF : ∀ ω : ℝ, F ω = a * ω ^ 2 + ∑' i, Real.log (1 + ω ^ 2 / θ i ^ 2)) :
    (∀ ω : ℝ, Summable fun i => Real.log (1 + ω ^ 2 / θ i ^ 2)) ∧
      (∀ ω : ℝ, 0 ≤ F ω ∧ F ω ≤ (a + ∑' i, (θ i ^ 2)⁻¹) * ω ^ 2) ∧
      (∀ x : ℝ, 0 < x → Summable fun i => Real.exp (-(θ i * x))) ∧
      (∃ P : SDProfile, P.a = a ∧ (∀ x : ℝ, 0 < x → P.k x = 2 * ∑' i, Real.exp (-(θ i * x))) ∧
        ∀ ω : ℝ, F ω = P.exponent ω) ∧
      IsCompletelyMonotone (fun x => 2 * ∑' i, Real.exp (-(θ i * x))) ∧
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * (2 * ∑' i, Real.exp (-(θ i * x))) / x) ≤
        ENNReal.ofReal (2 * ∑' i, (θ i ^ 2)⁻¹) ∧
      ((∃ ω : ℝ, F ω ≠ 0) ↔ a ≠ 0 ∨ Nonempty ι) := by
  -- the atoms
  have hlog0 : ∀ ω i, 0 ≤ Real.log (1 + ω ^ 2 / θ i ^ 2) := fun ω i =>
    Real.log_nonneg (by
      have h : 0 ≤ ω ^ 2 / θ i ^ 2 := by have := hθ i; positivity
      linarith)
  have hlog1 : ∀ ω i, Real.log (1 + ω ^ 2 / θ i ^ 2) ≤ ω ^ 2 * (θ i ^ 2)⁻¹ := by
    intro ω i
    have hp : 0 < 1 + ω ^ 2 / θ i ^ 2 := by have := hθ i; positivity
    have := Real.log_le_sub_one_of_pos hp
    rw [div_eq_mul_inv] at this ⊢
    linarith
  have hsL : ∀ ω : ℝ, Summable fun i => Real.log (1 + ω ^ 2 / θ i ^ 2) := fun ω =>
    Summable.of_nonneg_of_le (hlog0 ω) (hlog1 ω) (hsum.mul_left _)
  have hsE : ∀ x : ℝ, 0 < x → Summable fun i => Real.exp (-(θ i * x)) := by
    intro x hx
    simpa using summable_pow_mul_exp_neg hθ hsum 0 hx
  -- the profile
  set k : ℝ → ℝ := fun x => 2 * ∑' i, Real.exp (-(θ i * x)) with hk
  have hk0 : ∀ x, 0 ≤ k x := fun x =>
    mul_nonneg zero_le_two (tsum_nonneg fun i => (Real.exp_pos _).le)
  -- the integral bound, with `2∑ϑᵢ⁻²`
  have hbound : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * k x / x) ≤
      ENNReal.ofReal (2 * ∑' i, (θ i ^ 2)⁻¹) := by
    calc ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * k x / x)
        ≤ ∫⁻ x in Ioi (0 : ℝ), ∑' i, ENNReal.ofReal (2 * (x * Real.exp (-(θ i * x)))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
          have hx : (0 : ℝ) < x := hx
          rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun i => by have := Real.exp_pos (-(θ i * x)); positivity)
            (((hsE x hx).mul_left x).mul_left 2)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [tsum_mul_left, tsum_mul_left, div_le_iff₀ hx]
          have hm : min 1 (x ^ 2) ≤ x ^ 2 := min_le_right _ _
          have := hk0 x
          simp only [hk] at this ⊢
          nlinarith
      _ = ∑' i, ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * (x * Real.exp (-(θ i * x)))) :=
          lintegral_tsum fun i => (by fun_prop : Measurable fun x : ℝ =>
            ENNReal.ofReal (2 * (x * Real.exp (-(θ i * x))))).aemeasurable
      _ = ∑' i, ENNReal.ofReal (2 * (θ i ^ 2)⁻¹) := by
          congr 1
          funext i
          exact lintegral_mul_exp_neg (hθ i) 2 zero_le_two
      _ = ENNReal.ofReal (2 * ∑' i, (θ i ^ 2)⁻¹) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by have := hθ i; positivity)
            (hsum.mul_left 2), tsum_mul_left]
  have hfin : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (x ^ 2) * k x / x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  -- the SDProfile
  set k' : ℝ → ℝ := fun x => if 0 < x then k x else 0 with hk'
  have hk'eq : ∀ x, 0 < x → k' x = k x := fun x hx => if_pos hx
  have hanti : AntitoneOn k' (Ioi 0) := by
    intro x hx y hy hxy
    have hx : (0 : ℝ) < x := hx
    have hy : (0 : ℝ) < y := hy
    rw [hk'eq x hx, hk'eq y hy]
    refine mul_le_mul_of_nonneg_left ?_ zero_le_two
    exact Summable.tsum_le_tsum (fun i => Real.exp_le_exp.2 (by nlinarith [hθ i])) (hsE y hy)
      (hsE x hx)
  let P : SDProfile :=
    { a := a
      k := k'
      a_nonneg := ha
      k_nonneg := fun x hx => (hk'eq x hx).symm ▸ hk0 x
      k_antitone := hanti
      k_zero := by simp [hk']
      integrable_near_zero := by
        refine ne_top_of_le_ne_top hfin ?_
        refine le_trans ?_ (lintegral_mono_set (s := Ioo (0 : ℝ) 1) Ioo_subset_Ioi_self)
        refine setLIntegral_mono' measurableSet_Ioo fun x hx => ?_
        have hx0 : (0 : ℝ) < x := hx.1
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [hk'eq x hx0, min_eq_right (by nlinarith [hx.2])]
        field_simp
      integrable_at_top := by
        refine ne_top_of_le_ne_top hfin ?_
        refine le_trans ?_ (lintegral_mono_set (s := Ioi (1 : ℝ)) (Ioi_subset_Ioi zero_le_one))
        refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
        have hx1 : (1 : ℝ) < x := hx
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [hk'eq x (zero_lt_one.trans hx1), min_eq_left (by nlinarith)]
        ring }
  -- the exponent of the profile
  have hexp : ∀ ω : ℝ, F ω = P.exponent ω := by
    intro ω
    have hI : ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x) =
        ENNReal.ofReal (∑' i, Real.log (1 + ω ^ 2 / θ i ^ 2)) := by
      have hcos : ∀ x, 0 ≤ 1 - Real.cos (ω * x) := fun x => by linarith [Real.cos_le_one (ω * x)]
      calc ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x)
          = ∫⁻ x in Ioi (0 : ℝ), ∑' i, ENNReal.ofReal
              (2 * ((1 - Real.cos (ω * x)) * Real.exp (-(θ i * x)) / x)) := by
            refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
            have hx : (0 : ℝ) < x := hx
            rw [← ENNReal.ofReal_tsum_of_nonneg
              (fun i => by have := Real.exp_pos (-(θ i * x)); have := hcos x; positivity)
              ((((hsE x hx).mul_left (1 - Real.cos (ω * x))).div_const x).mul_left 2)]
            congr 1
            change (1 - Real.cos (ω * x)) * k' x / x = _
            rw [hk'eq x hx]
            change (1 - Real.cos (ω * x)) * (2 * ∑' i, Real.exp (-(θ i * x))) / x = _
            rw [tsum_mul_left, tsum_div_const, tsum_mul_left]
            ring
        _ = ∑' i, ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
              (2 * ((1 - Real.cos (ω * x)) * Real.exp (-(θ i * x)) / x)) :=
            lintegral_tsum fun i => (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal
              (2 * ((1 - Real.cos (ω * x)) * Real.exp (-(θ i * x)) / x))).aemeasurable
        _ = ∑' i, ENNReal.ofReal (Real.log (1 + ω ^ 2 / θ i ^ 2)) := by
            congr 1
            funext i
            rw [← ofReal_integral_eq_lintegral_ofReal
              ((integrableOn_laplaceAtom (hθ i) ω).const_mul 2), integral_const_mul,
              laplace_atoms_admissible_1 (hθ i) ω]
            · ring_nf
            · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
              have hx : (0 : ℝ) < x := hx
              have := Real.exp_pos (-(θ i * x))
              have := hcos x
              simp only [Pi.zero_apply]
              positivity
        _ = _ := (ENNReal.ofReal_tsum_of_nonneg (hlog0 ω) (hsL ω)).symm
    change F ω = (ENNReal.ofReal (a * ω ^ 2) +
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x)).toReal
    rw [hI, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (tsum_nonneg (hlog0 ω)), hF]
  -- complete monotonicity
  set g : ℕ → ℝ → ℝ := fun n x => 2 * ∑' i, (-θ i) ^ n * Real.exp (-(θ i * x)) with hg
  have hsg : ∀ n x, 0 < x → Summable fun i => (-θ i) ^ n * Real.exp (-(θ i * x)) := by
    intro n x hx
    refine Summable.of_norm ?_
    refine (summable_pow_mul_exp_neg hθ hsum n hx).congr fun i => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (hθ i),
      abs_of_pos (Real.exp_pos _)]
  have hgd : ∀ n x, 0 < x → HasDerivAt (g n) (g (n + 1) x) x := by
    intro n x hx
    have hx2 : 0 < x / 2 := by positivity
    refine HasDerivAt.const_mul 2 ?_
    refine hasDerivAt_tsum_of_isPreconnected (t := Ioi (x / 2))
      (u := fun i => θ i ^ (n + 1) * Real.exp (-(θ i * (x / 2))))
      (g' := fun i y => (-θ i) ^ (n + 1) * Real.exp (-(θ i * y)))
      (summable_pow_mul_exp_neg hθ hsum (n + 1) hx2) isOpen_Ioi isPreconnected_Ioi
      (fun i y _ => ?_) (fun i y hy => ?_) (y₀ := x) (by simp only [mem_Ioi]; linarith)
      (hsg n x hx) (by simp only [mem_Ioi]; linarith)
    · have h1 : HasDerivAt (fun y : ℝ => -(θ i * y)) (-θ i) y := by
        have := (hasDerivAt_id y).const_mul (-θ i)
        simp only [id, mul_one, neg_mul] at this
        exact this
      refine ((h1.exp).const_mul ((-θ i) ^ n)).congr_deriv ?_
      ring
    · have hy : x / 2 < y := hy
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (hθ i),
        abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by have := hθ i; positivity)
      nlinarith [hθ i]
  have hcm : IsCompletelyMonotone k := by
    have hkg : k = g 0 := by
      funext x
      simp [hk, hg]
    rw [hkg]
    have hU : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
    have hderiv : ∀ n, EqOn (derivWithin (g n) (Ioi 0)) (g (n + 1)) (Ioi 0) := by
      intro n x hx
      exact ((hgd n x hx).hasDerivWithinAt).derivWithin (hU x hx)
    have hcd : ∀ m : ℕ, ∀ n, ContDiffOn ℝ m (g n) (Ioi 0) := by
      intro m
      induction m with
      | zero =>
        intro n
        exact contDiffOn_zero.2 fun x hx => (hgd n x hx).continuousAt.continuousWithinAt
      | succ m ih =>
        intro n
        rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin hU]
        refine ⟨fun x hx => (hgd n x hx).differentiableAt.differentiableWithinAt,
          fun h => absurd h (by simp), ?_⟩
        exact (ih (n + 1)).congr (hderiv n)
    have hit : ∀ n, EqOn (iteratedDerivWithin n (g 0) (Ioi 0)) (g n) (Ioi 0) := by
      intro n
      induction n with
      | zero => intro x _; simp
      | succ n ih =>
        intro x hx
        rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih hx)]
        exact hderiv n hx
    refine ⟨contDiffOn_infty.2 fun m => hcd m 0, fun n x hx => ?_⟩
    rw [hit n hx]
    simp only [hg]
    rw [← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, ← tsum_mul_left]
    refine mul_nonneg zero_le_two (tsum_nonneg fun i => ?_)
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
    have := hθ i
    have := Real.exp_pos (-(θ i * x))
    positivity
  refine ⟨hsL, fun ω => ⟨?_, ?_⟩, hsE, ⟨P, rfl, fun x hx => hk'eq x hx, hexp⟩,
    hcm, hbound, ?_⟩
  · rw [hF]
    exact add_nonneg (by positivity) (tsum_nonneg (hlog0 ω))
  · rw [hF, add_mul, mul_comm (∑' i, _) (ω ^ 2), ← tsum_mul_left]
    have := Summable.tsum_le_tsum (hlog1 ω) (hsL ω) (hsum.mul_left _)
    nlinarith
  · constructor
    · rintro ⟨ω, hω⟩
      by_contra h
      simp only [not_or, ne_eq, not_not, not_nonempty_iff] at h
      obtain ⟨ha0, hι⟩ := h
      apply hω
      rw [hF, ha0, tsum_empty]
      ring
    · intro h
      refine ⟨1, ?_⟩
      rw [hF]
      have hT : 0 ≤ ∑' i, Real.log (1 + 1 ^ 2 / θ i ^ 2) := tsum_nonneg (hlog0 1)
      rcases h with h | hne
      · have : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
        nlinarith
      · obtain ⟨i⟩ := hne
        have hi : 0 < Real.log (1 + 1 ^ 2 / θ i ^ 2) := by
          have h1 : 0 < 1 ^ 2 / θ i ^ 2 := by have := hθ i; positivity
          exact Real.log_pos (by linarith)
        have := (hsL 1).le_tsum i (fun j _ => hlog0 1 j)
        nlinarith

end Pyramids
