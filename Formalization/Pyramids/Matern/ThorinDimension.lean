/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.CompletelyMonotone
import Pyramids.Matern.BesselK
import Pyramids.Matern.MaternPyramid
import Pyramids.LineAppendix.MaternLine

/-!
# `prop:thorin-in-dimension-d`: where the Thorin property goes in `d ≥ 2`

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:thorin-in-dimension-d`. Phase 5, wave 3b. The
five declarations moved here from `PyramidsSkeleton.Ch04Matern` with their conclusions unchanged;
`thorin_dimension_2_profile` no longer takes `1 ≤ d`, which its proof does not read (2026-11-15, a
strengthening).

* **The two bounds.** For `d ≥ 2`, `e^y b_d(y) ≤ (2/Γ(d/2))(e y^{d/2} + 4^{d/2}Γ(d/2))` for `y > 0`
  (`exp_mul_besselProfile_le`: the integrand is compared with `e^{-y}(e y^{d/2-1}e^{-v/y} +
  v^{d/2-1}e^{-v/4})`, split at `v = y`), and `e^y b_d(y) ≥ (2/Γ(d/2))e^{-2}(y/2)^{d/2-1}√y` for
  `y ≥ 1` (`exp_mul_besselProfile_ge`: the window `[y/2, y/2 + √y]`).
* **Clause (1).** `b_d` and `k_d` are positive, `e^{λr}` times each is at most a polynomial and
  unbounded (`λ = 1` and `λ = q/c`; the series `k_d` against a geometric series), so neither is
  completely monotone (`not_isCompletelyMonotone_of_growth`, which is (D) of
  `lem:cm-exponential-rate`; no Bernstein representation). For `d = 1`, `b_1 = 2e^{-y}` and
  `k_1 = 2∑e^{-rqⁱ/c}` (the line's `matern_pyramid_line_1`).
* **Clause (2).** The substitution `v = (r/c)e^u` gives the profile. `P_1 = 2E_1`,
  `P_3 = 2E_1 + 2e^{-y}` from `lem:bessel-profile`(3); `P_2 = 2K_0` from `lem:bessel-k`(1)–(2).
  The three are completely monotone as Laplace transforms on `(1,∞)`
  (`E_1(y) = ∫₁^∞e^{-ys}ds/s`, `lem:bessel-k`(3)). For `d ≥ 4`, `P_d' = -b_d(y)/y`, and if `P_d`
  were completely monotone so would be `b_d(y)/y`, which the two bounds exclude with `λ = 1`.

**What it reaches.** Lean core only: `lem:bessel-k` is proved from Mathlib (its entry A51 is a
theorem), and nothing reads ledger A55.
-/

set_option autoImplicit false

namespace Pyramids

open MeasureTheory Set Filter
open ScaleSpace (besselK)
open scoped Topology

variable {d : ℕ} {q c : ℝ}

/-! ## The two bounds on `e^y b_d(y)` -/

theorem besselProfile_integrand_upper {s y v : ℝ} (hs : 1 ≤ s) (hy : 0 < y) (hv : 0 < v) :
    v ^ (s - 1) * Real.exp (-v - y ^ 2 / (4 * v)) ≤
      Real.exp (-y) * (Real.exp 1 * y ^ (s - 1) * Real.exp (-(y⁻¹ * v)) +
        v ^ (s - 1) * Real.exp (-(1 / 4 * v))) := by
  have h4 : 0 < 4 * v := by positivity
  have hfrac : -v - y ^ 2 / (4 * v) = -(4 * v ^ 2 + y ^ 2) / (4 * v) := by field_simp; ring
  rcases le_or_gt v y with hvy | hvy
  · have hp : v ^ (s - 1) ≤ y ^ (s - 1) := Real.rpow_le_rpow hv.le hvy (by linarith)
    have he : Real.exp (-v - y ^ 2 / (4 * v)) ≤ Real.exp (-y) := by
      refine Real.exp_le_exp.2 ?_
      rw [hfrac, div_le_iff₀ h4]
      nlinarith [sq_nonneg (2 * v - y)]
    have h1 : 1 ≤ Real.exp 1 * Real.exp (-(y⁻¹ * v)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have : y⁻¹ * v ≤ 1 := by rw [inv_mul_le_iff₀ hy]; linarith
      linarith
    calc v ^ (s - 1) * Real.exp (-v - y ^ 2 / (4 * v)) ≤ y ^ (s - 1) * Real.exp (-y) :=
          mul_le_mul hp he (by positivity) (by positivity)
      _ ≤ y ^ (s - 1) * Real.exp (-y) * (Real.exp 1 * Real.exp (-(y⁻¹ * v))) :=
          le_mul_of_one_le_right (by positivity) h1
      _ = Real.exp (-y) * (Real.exp 1 * y ^ (s - 1) * Real.exp (-(y⁻¹ * v))) := by ring
      _ ≤ _ := by
          rw [mul_add]
          exact le_add_of_nonneg_right (by positivity)
  · have he : Real.exp (-v - y ^ 2 / (4 * v)) ≤ Real.exp (-y) * Real.exp (-(1 / 4 * v)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      rw [hfrac, div_le_iff₀ h4]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * v - y) (by linarith : (0 : ℝ) ≤ v - y)]
    calc v ^ (s - 1) * Real.exp (-v - y ^ 2 / (4 * v))
        ≤ v ^ (s - 1) * (Real.exp (-y) * Real.exp (-(1 / 4 * v))) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = Real.exp (-y) * (v ^ (s - 1) * Real.exp (-(1 / 4 * v))) := by ring
      _ ≤ _ := by
          rw [mul_add]
          exact le_add_of_nonneg_left (by positivity)

/-- **The upper bound** `e^y b_d(y) ≤ (2/Γ(d/2))(e y^{d/2} + 4^{d/2}Γ(d/2))`, `d ≥ 2`, `y > 0`. -/
theorem exp_mul_besselProfile_le (hd : 2 ≤ d) {y : ℝ} (hy : 0 < y) :
    Real.exp y * besselProfile d y ≤ 2 / Real.Gamma ((d : ℝ) / 2) *
      (Real.exp 1 * y ^ ((d : ℝ) / 2) + 4 ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2)) := by
  set s : ℝ := (d : ℝ) / 2 with hsdef
  have hs : 1 ≤ s := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [hsdef]; linarith
  have hs0 : 0 < s := by linarith
  have hΓ := Real.Gamma_pos_of_pos hs0
  have hI1 : IntegrableOn (fun v : ℝ => Real.exp (-(y⁻¹ * v))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 (inv_pos.2 hy)
  have hI2 : IntegrableOn (fun v : ℝ => v ^ (s - 1) * Real.exp (-(1 / 4 * v))) (Ioi 0) := by
    have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (by linarith) le_rfl
      (b := 1 / 4) (by norm_num)
    simpa only [Real.rpow_one, neg_mul] using h2
  have hE1 : ∫ v in Ioi (0 : ℝ), Real.exp (-(y⁻¹ * v)) = y := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) one_pos (inv_pos.2 hy)
    simpa using h
  have hE2 : ∫ v in Ioi (0 : ℝ), v ^ (s - 1) * Real.exp (-(1 / 4 * v)) = 4 ^ s * Real.Gamma s := by
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 (by norm_num)]
    norm_num
  have hle : ∫ v in Ioi (0 : ℝ), v ^ (s - 1) * Real.exp (-v - y ^ 2 / (4 * v)) ≤
      ∫ v in Ioi (0 : ℝ), Real.exp (-y) * (Real.exp 1 * y ^ (s - 1) * Real.exp (-(y⁻¹ * v)) +
        v ^ (s - 1) * Real.exp (-(1 / 4 * v))) :=
    setIntegral_mono_on (integrableOn_besselProfile hs0 y)
      (((hI1.const_mul (Real.exp 1 * y ^ (s - 1))).add hI2).const_mul _) measurableSet_Ioi
      fun v (hv : 0 < v) => besselProfile_integrand_upper hs hy hv
  rw [integral_const_mul, integral_add (hI1.const_mul _) hI2, integral_const_mul, hE1, hE2] at hle
  have hys : y ^ (s - 1) * y = y ^ s := by
    rw [Real.rpow_sub_one hy.ne', div_mul_cancel₀ _ hy.ne']
  rw [besselProfile]
  calc Real.exp y * (2 / Real.Gamma s *
        ∫ v in Ioi (0 : ℝ), v ^ (s - 1) * Real.exp (-v - y ^ 2 / (4 * v)))
      ≤ Real.exp y * (2 / Real.Gamma s * (Real.exp (-y) *
          (Real.exp 1 * y ^ (s - 1) * y + 4 ^ s * Real.Gamma s))) := by gcongr
    _ = 2 / Real.Gamma s * (Real.exp 1 * y ^ s + 4 ^ s * Real.Gamma s) := by
        rw [← hys]
        have : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
        linear_combination (2 / Real.Gamma s * (Real.exp 1 * y ^ (s - 1) * y +
          4 ^ s * Real.Gamma s)) * this

/-- **The upper bound, polynomial form**: `e^y b_d(y) ≤ C(1 + y)^d` for `y > 0`, `d ≥ 2`. -/
theorem exists_exp_mul_besselProfile_le (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, 0 < y → Real.exp y * besselProfile d y ≤ C * (1 + y) ^ d := by
  set s : ℝ := (d : ℝ) / 2 with hsdef
  have hsd : s ≤ d := by
    have : (0 : ℝ) ≤ d := by positivity
    rw [hsdef]; linarith
  have hs0 : 0 < s := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [hsdef]; linarith
  have hΓ := Real.Gamma_pos_of_pos hs0
  refine ⟨2 / Real.Gamma s * (Real.exp 1 + 4 ^ s * Real.Gamma s), by positivity, fun y hy => ?_⟩
  refine (exp_mul_besselProfile_le hd hy).trans ?_
  have h1 : (1 : ℝ) ≤ (1 + y) ^ d := one_le_pow₀ (by linarith)
  have h2 : y ^ s ≤ (1 + y) ^ d := by
    calc y ^ s ≤ (1 + y) ^ s := Real.rpow_le_rpow hy.le (by linarith) hs0.le
      _ ≤ (1 + y) ^ (d : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hsd
      _ = (1 + y) ^ d := Real.rpow_natCast _ _
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith [Real.exp_pos 1, mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) s) hΓ]

/-- **The lower bound** `e^y b_d(y) ≥ (2/Γ(d/2))e^{-2}(y/2)^{d/2-1}√y`, `d ≥ 2`, `y ≥ 1`. -/
theorem exp_mul_besselProfile_ge (hd : 2 ≤ d) {y : ℝ} (hy : 1 ≤ y) :
    2 / Real.Gamma ((d : ℝ) / 2) * Real.exp (-2) * ((y / 2) ^ ((d : ℝ) / 2 - 1) * Real.sqrt y) ≤
      Real.exp y * besselProfile d y := by
  set s : ℝ := (d : ℝ) / 2 with hsdef
  have hs : 1 ≤ s := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [hsdef]; linarith
  have hs0 : 0 < s := by linarith
  have hΓ := Real.Gamma_pos_of_pos hs0
  have hy0 : 0 < y := by linarith
  set a := y / 2
  set b := y / 2 + Real.sqrt y
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0.le
  have hab : a ≤ b := by simp only [a, b]; linarith [Real.sqrt_nonneg y]
  have hsub : Icc a b ⊆ Ioi 0 := fun v hv => show 0 < v by simp only [a] at hv; linarith [hv.1]
  set F := fun v : ℝ => v ^ (s - 1) * Real.exp (-v - y ^ 2 / (4 * v))
  have hint := integrableOn_besselProfile hs0 y
  have hpt : ∀ v ∈ Icc a b, a ^ (s - 1) * Real.exp (-y - 2) ≤ F v := by
    intro v hv
    have hv0 : 0 < v := hsub hv
    have hw0 : 0 ≤ v - y / 2 := by simp only [a] at hv; linarith [hv.1]
    have hw1 : v - y / 2 ≤ Real.sqrt y := by simp only [b] at hv; linarith [hv.2]
    have hw2 : (v - y / 2) ^ 2 ≤ y := (pow_le_pow_left₀ hw0 hw1 2).trans hsq.le
    refine mul_le_mul (Real.rpow_le_rpow (by positivity) hv.1 (by linarith))
      (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
    have h4 : 0 < 4 * v := by positivity
    rw [show -v - y ^ 2 / (4 * v) = -(4 * v ^ 2 + y ^ 2) / (4 * v) by field_simp; ring,
      le_div_iff₀ h4]
    nlinarith
  have h1 : ∫ v in Icc a b, F v ≤ ∫ v in Ioi (0 : ℝ), F v :=
    setIntegral_mono_set hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : 0 < v) =>
        by positivity))
      hsub.eventuallyLE
  have h2 : ∫ v in Icc a b, a ^ (s - 1) * Real.exp (-y - 2) ≤ ∫ v in Icc a b, F v :=
    setIntegral_mono_on continuous_const.integrableOn_Icc (hint.mono_set hsub) measurableSet_Icc
      hpt
  rw [setIntegral_const, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, show b - a = Real.sqrt y by simp only [a, b]; ring] at h2
  rw [besselProfile]
  have hey : Real.exp y * Real.exp (-y - 2) = Real.exp (-2) := by
    rw [← Real.exp_add]; ring_nf
  calc 2 / Real.Gamma s * Real.exp (-2) * (a ^ (s - 1) * Real.sqrt y)
      = Real.exp y * (2 / Real.Gamma s * (Real.sqrt y * (a ^ (s - 1) * Real.exp (-y - 2)))) := by
        rw [← hey]; ring
    _ ≤ Real.exp y * (2 / Real.Gamma s * ∫ v in Ioi (0 : ℝ), F v) := by
        gcongr
        exact h2.trans h1

/-- `b_d > 0` on `[0,∞)`. -/
theorem besselProfile_pos (hd : 1 ≤ d) {y : ℝ} (hy : 0 ≤ y) : 0 < besselProfile d y :=
  lt_of_le_of_lt (besselProfile_nonneg hd (y + 1))
    (besselProfile_strictAntiOn hd hy (show (0 : ℝ) ≤ y + 1 by linarith) (by linarith))

/-- `M < m√r` for some `r ≥ a`. -/
theorem exists_lt_mul_sqrt {m : ℝ} (hm : 0 < m) (M a : ℝ) : ∃ r, a ≤ r ∧ M < m * Real.sqrt r := by
  refine ⟨max a ((|M| / m) ^ 2 + 1), le_max_left _ _, ?_⟩
  have h1 : |M| / m < Real.sqrt (max a ((|M| / m) ^ 2 + 1)) := by
    rw [Real.lt_sqrt (by positivity)]
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  rw [div_lt_iff₀ hm] at h1
  linarith [le_abs_self M]

/-- `e^y b_d(y)` is unbounded: `M < (2/Γ(d/2))e^{-2}√y ≤ e^y b_d(y)` for some `y ≥ a`, `a ≥ 2`. -/
theorem exists_lt_exp_mul_besselProfile (hd : 2 ≤ d) (M : ℝ) {a : ℝ} (ha : 2 ≤ a) :
    ∃ y, a ≤ y ∧ M < Real.exp y * besselProfile d y := by
  have hs : 1 ≤ (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hΓ := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < (d : ℝ) / 2)
  obtain ⟨y, hy, hM⟩ := exists_lt_mul_sqrt (m := 2 / Real.Gamma ((d : ℝ) / 2) * Real.exp (-2))
    (by positivity) M a
  refine ⟨y, hy, hM.trans_le ?_⟩
  refine le_trans ?_ (exp_mul_besselProfile_ge hd (by linarith))
  have h1 : 1 ≤ (y / 2) ^ ((d : ℝ) / 2 - 1) := Real.one_le_rpow (by linarith) (by linarith)
  have := Real.sqrt_nonneg y
  rw [← mul_assoc (2 / Real.Gamma ((d : ℝ) / 2) * Real.exp (-2))]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.Gamma ((d : ℝ) / 2) * Real.exp (-2))
    this]

/-! ## Clause (1) -/

theorem maternPolarProfile_pos (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) {r : ℝ} (hr : 0 < r) :
    besselProfile d (r * q / c) ≤ maternPolarProfile q c d r ∧ 0 < maternPolarProfile q c d r := by
  have hq0 : 0 < q := by linarith
  have h := (summable_maternProfile hd hq hc hr).le_tsum 0 fun j _ => besselProfile_nonneg hd _
  simp only [zero_add, pow_one] at h
  exact ⟨h, lt_of_lt_of_le (besselProfile_pos hd (by positivity)) h⟩

/-- `e^{(q/c)r} k_d(r) ≤ C(1 + r)^d` for large `r`, `d ≥ 2`. -/
theorem exists_exp_mul_maternPolarProfile_le (hd : 2 ≤ d) (hq : 1 < q) (hc : 0 < c) :
    ∃ C R : ℝ, ∀ r, R ≤ r →
      Real.exp (q / c * r) * maternPolarProfile q c d r ≤ C * (1 + r) ^ d := by
  have hd1 : 1 ≤ d := by omega
  have hq0 : 0 < q := by linarith
  obtain ⟨Cb, hCb, hb⟩ := exists_exp_mul_besselProfile_le hd
  set x0 := Real.log (2 * q ^ d) / (q - 1)
  set K := max 1 (q / c)
  refine ⟨2 * Cb * K ^ d, max 1 (x0 * c / q), fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : 0 < r := by linarith
  set x := q / c * r with hx
  have hx0 : 0 < x := by positivity
  have hxx0 : x0 ≤ x := by
    have := le_trans (le_max_right _ _) hr
    rw [div_le_iff₀ hq0] at this
    rw [hx, div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  set ρ := q ^ d * Real.exp (-(x * (q - 1)))
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ : ρ ≤ 1 / 2 := by
    have h1 : Real.log (2 * q ^ d) ≤ x * (q - 1) := by
      have := mul_le_mul_of_nonneg_right hxx0 (by linarith : (0 : ℝ) ≤ q - 1)
      rwa [div_mul_cancel₀ _ (by linarith : q - 1 ≠ 0)] at this
    have h2 : 2 * q ^ d ≤ Real.exp (x * (q - 1)) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 * q ^ d)]
      exact Real.exp_le_exp.2 h1
    simp only [ρ, Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith
  -- the terms
  have hterm : ∀ i : ℕ, Real.exp x * besselProfile d (r * q ^ (i + 1) / c) ≤
      Cb * (1 + x) ^ d * (1 / 2) ^ i := by
    intro i
    have hqi : 1 ≤ q ^ i := one_le_pow₀ hq.le
    have hyi : r * q ^ (i + 1) / c = x * q ^ i := by rw [hx, pow_succ]; field_simp
    rw [hyi]
    have hy0 : 0 < x * q ^ i := by positivity
    have h1 := hb _ hy0
    have h2 : besselProfile d (x * q ^ i) ≤
        Cb * (1 + x * q ^ i) ^ d * Real.exp (-(x * q ^ i)) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), mul_comm]
      exact h1
    have h3 : (1 + x * q ^ i) ^ d ≤ (q ^ d) ^ i * (1 + x) ^ d := by
      rw [← pow_mul, mul_comm d i, pow_mul, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) d
    have h4 : Real.exp x * Real.exp (-(x * q ^ i)) ≤ Real.exp (-(x * (q - 1))) ^ i := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      have hb' := one_add_mul_le_pow (a := q - 1) (by linarith) i
      rw [add_sub_cancel] at hb'
      nlinarith
    calc Real.exp x * besselProfile d (x * q ^ i)
        ≤ Real.exp x * (Cb * ((q ^ d) ^ i * (1 + x) ^ d) * Real.exp (-(x * q ^ i))) := by
          gcongr
          exact h2.trans (by gcongr)
      _ = Cb * (1 + x) ^ d * ((q ^ d) ^ i * (Real.exp x * Real.exp (-(x * q ^ i)))) := by ring
      _ ≤ Cb * (1 + x) ^ d * ((q ^ d) ^ i * Real.exp (-(x * (q - 1))) ^ i) := by gcongr
      _ = Cb * (1 + x) ^ d * ρ ^ i := by rw [← mul_pow]
      _ ≤ Cb * (1 + x) ^ d * (1 / 2) ^ i := by gcongr
  have hsum := Summable.tsum_le_tsum hterm
    ((summable_maternProfile hd1 hq hc hr0).mul_left (Real.exp x))
    ((summable_geometric_two).mul_left (Cb * (1 + x) ^ d))
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_two] at hsum
  have hK : 1 + x ≤ K * (1 + r) := by
    have h1 : 1 ≤ K := le_max_left _ _
    have h2 : q / c ≤ K := le_max_right _ _
    nlinarith
  calc Real.exp (q / c * r) * maternPolarProfile q c d r ≤ Cb * (1 + x) ^ d * 2 := hsum
    _ ≤ Cb * (K * (1 + r)) ^ d * 2 := by gcongr
    _ = 2 * Cb * K ^ d * (1 + r) ^ d := by rw [mul_pow]; ring

/-- **`prop:thorin-in-dimension-d`(1), `d ≥ 2`.** Neither `b_d` nor `k_d` is completely monotone
on `(0,∞)`. -/
theorem thorin_dimension_1 (hd : 2 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    ¬ IsCompletelyMonotone (besselProfile d) ∧
      ¬ IsCompletelyMonotone (maternPolarProfile q c d) := by
  have hd1 : 1 ≤ d := by omega
  have hq0 : 0 < q := by linarith
  obtain ⟨Cb, -, hb⟩ := exists_exp_mul_besselProfile_le hd
  refine ⟨?_, ?_⟩
  · refine not_isCompletelyMonotone_of_growth (l := 1) (C := Cb) (R := 1) (p := d)
      (fun x hx => besselProfile_pos hd1 hx.le) (fun r hr => ?_) fun M => ?_
    · rw [one_mul]; exact hb r (by linarith)
    · obtain ⟨y, hy, hM⟩ := exists_lt_exp_mul_besselProfile hd M le_rfl
      exact ⟨y, by linarith, by rwa [one_mul]⟩
  · obtain ⟨C, R, hk⟩ := exists_exp_mul_maternPolarProfile_le hd hq hc
    refine not_isCompletelyMonotone_of_growth (l := q / c) (C := C) (R := R) (p := d)
      (fun x hx => (maternPolarProfile_pos hd1 hq hc hx).2) hk fun M => ?_
    obtain ⟨y, hy, hM⟩ := exists_lt_exp_mul_besselProfile hd M (le_max_left 2 (q / c))
    have hy2 : q / c ≤ y := le_trans (le_max_right _ _) hy
    refine ⟨y * c / q, ?_, ?_⟩
    · rw [le_div_iff₀ hq0, one_mul]
      rwa [div_le_iff₀ hc] at hy2
    · have hy0 : (0 : ℝ) < y := by linarith [le_max_left 2 (q / c)]
      have hr0 : 0 < y * c / q := by positivity
      have e1 : q / c * (y * c / q) = y := by field_simp
      have e2 : y * c / q * q / c = y := by field_simp
      have h := (maternPolarProfile_pos hd1 hq hc hr0).1
      rw [e2] at h
      rw [e1]
      exact hM.trans_le (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le)

/-- **`prop:thorin-in-dimension-d`(1), `d = 1`.** Both are completely monotone. -/
theorem thorin_dimension_1_line {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    IsCompletelyMonotone (besselProfile 1) ∧ IsCompletelyMonotone (maternPolarProfile q c 1) := by
  have hq0 : 0 < q := by linarith
  refine ⟨(isCompletelyMonotone_exp_neg.const_mul (a := 2) (by norm_num)).congr fun y hy =>
    (besselProfile_one_pos hy).symm, ?_⟩
  have h := (laplace_atoms_admissible_2 (ι := ℕ) le_rfl (maternTheta q c)
    (maternTheta_pos hq hc) (summable_maternTheta hq hc) (maternExponent q c)
    (maternExponent_eq_atoms hq hc)).2.2.2.2.1
  refine h.congr fun x (hx : 0 < x) => ?_
  change 2 * _ = _
  rw [maternPolarProfile, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [besselProfile_one_pos (by positivity), maternTheta]
  ring_nf

/-! ## Clause (2) -/

/-- **`prop:thorin-in-dimension-d`(2), the limit profile** of `thm:matern-pyramid`(5) is
`P_d(r/c)`. It no longer takes `1 ≤ d`, which the substitution does not read (2026-11-15, a
strengthening). -/
theorem thorin_dimension_2_profile {c : ℝ} (hc : 0 < c) (r : ℝ) (hr : 0 < r) :
    ∫ u in Ioi (0 : ℝ), besselProfile d (r * Real.exp u / c) = besselTail d (r / c) := by
  set a := r / c with ha
  have ha0 : 0 < a := by positivity
  have himage : (fun u => a * Real.exp u) '' Ioi 0 = Ioi a := by
    ext v
    constructor
    · rintro ⟨u, (hu : 0 < u), rfl⟩
      change a < a * Real.exp u
      exact lt_mul_of_one_lt_right ha0 (Real.one_lt_exp_iff.2 hu)
    · intro (hv : a < v)
      have hva : 0 < v / a := by have : 0 < v := by linarith
                                 positivity
      refine ⟨Real.log (v / a), Real.log_pos ((one_lt_div ha0).2 hv), ?_⟩
      simp only
      rw [Real.exp_log hva]
      field_simp
  have hderiv : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun u => a * Real.exp u) (a * Real.exp u) (Ioi 0) u :=
    fun u _ => ((Real.hasDerivAt_exp u).const_mul a).hasDerivWithinAt
  have hinj : InjOn (fun u => a * Real.exp u) (Ioi 0) := fun u _ w _ h =>
    Real.exp_injective (mul_left_cancel₀ ha0.ne' h)
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun v => besselProfile d v / v)
  rw [himage] at h
  rw [besselTail, h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  have hp : 0 < a * Real.exp u := by positivity
  rw [smul_eq_mul, abs_of_pos hp, mul_div_cancel₀ _ hp.ne', ha]
  congr 1
  ring

theorem integrableOn_besselTail_integrand (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun v => besselProfile d v / v) (Ioi a) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi a (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    (a⁻¹ * (2 : ℝ) ^ (1 + (d : ℝ) / 2))) ?_ ?_
  · exact ((continuous_besselProfile hd).measurable.div measurable_id).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : a < v) => ?_)
    have hv0 : 0 < v := by linarith
    have hb0 := besselProfile_nonneg hd v
    rw [Real.norm_of_nonneg (div_nonneg hb0 hv0.le)]
    calc besselProfile d v / v ≤ besselProfile d v / a := div_le_div_of_nonneg_left hb0 ha hv.le
      _ ≤ (2 : ℝ) ^ (1 + (d : ℝ) / 2) * Real.exp (-v / 2) / a := by
          gcongr; exact besselProfile_le hd v
      _ = _ := by rw [show -v / 2 = -(1 / 2) * v by ring]; field_simp

/-- **`prop:thorin-in-dimension-d`(2), the limit profile, with its integrability** (fidelity review,
R47): for `d ≥ 1` both integrands of `thorin_dimension_2_profile` are integrable, by
`b_d(y) ≤ C_d e^{-y/2}`, so the identity is one of two finite integrals. -/
theorem thorin_dimension_2_profile_integrable (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) (r : ℝ)
    (hr : 0 < r) :
    IntegrableOn (fun u => besselProfile d (r * Real.exp u / c)) (Ioi 0) ∧
      IntegrableOn (fun v => besselProfile d v / v) (Ioi (r / c)) ∧
      ∫ u in Ioi (0 : ℝ), besselProfile d (r * Real.exp u / c) = besselTail d (r / c) := by
  refine ⟨?_, integrableOn_besselTail_integrand hd (by positivity),
    thorin_dimension_2_profile hc r hr⟩
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul
    (2 * (2 : ℝ) ^ (1 + (d : ℝ) / 2) * c / r)) ?_ (Eventually.of_forall fun u => ?_)
  · exact ((continuous_besselProfile hd).comp (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (besselProfile_nonneg hd _)]
    have h := besselProfile_le_div hd (y := r * Real.exp u / c) (by positivity)
    refine h.trans (le_of_eq ?_)
    rw [Real.exp_neg]
    field_simp

/-- **`P_d' = -b_d(y)/y`** on `(0,∞)`. -/
theorem hasDerivAt_besselTail (hd : 1 ≤ d) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (besselTail d) (-(besselProfile d y / y)) y := by
  set g := fun v => besselProfile d v / v
  set a := y / 2
  have ha : 0 < a := by positivity
  have hay : a < y := by simp only [a]; linarith
  have hint := integrableOn_besselTail_integrand hd ha
  have hcont : ContinuousOn g (Ioi 0) :=
    (continuous_besselProfile hd).continuousOn.div continuousOn_id fun v hv => ne_of_gt hv
  have hII : IntervalIntegrable g volume a y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hay.le).2 (hint.mono_set Ioc_subset_Ioi_self)
  have hD := intervalIntegral.integral_hasDerivAt_right hII
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi y hy) (hcont.continuousAt (Ioi_mem_nhds hy))
  have hD' := (hasDerivAt_const y (∫ v in Ioi a, g v)).sub hD
  rw [zero_sub] at hD'
  refine hD'.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hay] with z (hz : a < z)
  change _ = (∫ v in Ioi a, g v) - ∫ x in a..z, g x
  rw [besselTail, ← intervalIntegral.integral_Ioi_sub_Ioi hint hz.le]
  ring

/-- **`prop:thorin-in-dimension-d`(2), `d ≥ 4`.** `P_d` is not completely monotone. -/
theorem thorin_dimension_2_high (hd : 4 ≤ d) : ¬ IsCompletelyMonotone (besselTail d) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  intro hP
  have hcm : IsCompletelyMonotone (fun y => besselProfile d y / y) := by
    refine hP.neg_derivWithin.congr fun y (hy : 0 < y) => ?_
    simp only
    rw [((hasDerivAt_besselTail hd1 hy).hasDerivWithinAt).derivWithin
      (isOpen_Ioi.uniqueDiffOn y hy), neg_neg]
  obtain ⟨Cb, hCb, hb⟩ := exists_exp_mul_besselProfile_le hd2
  refine not_isCompletelyMonotone_of_growth (l := 1) (C := Cb) (R := 1) (p := d)
    (fun x hx => div_pos (besselProfile_pos hd1 hx.le) hx) (fun r hr => ?_) (fun M => ?_) hcm
  · rw [one_mul, ← mul_div_assoc]
    exact (div_le_self (mul_nonneg (Real.exp_pos _).le (besselProfile_nonneg hd1 r)) hr).trans
      (hb r (by linarith))
  · have hs : 2 ≤ (d : ℝ) / 2 := by
      have : (4 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hΓ := Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < (d : ℝ) / 2)
    set m := 2 / Real.Gamma ((d : ℝ) / 2) * Real.exp (-2)
    have hm : 0 < m := by positivity
    obtain ⟨y, hy, hM⟩ := exists_lt_mul_sqrt (m := m / 2) (by positivity) M 2
    refine ⟨y, by linarith, hM.trans_le ?_⟩
    have hy0 : 0 < y := by linarith
    have hlow := exp_mul_besselProfile_ge hd2 (by linarith : 1 ≤ y)
    have h1 : y / 2 ≤ (y / 2) ^ ((d : ℝ) / 2 - 1) := by
      conv_lhs => rw [← Real.rpow_one (y / 2)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [one_mul, ← mul_div_assoc, le_div_iff₀ hy0]
    have hsq := Real.sqrt_nonneg y
    calc m / 2 * Real.sqrt y * y = m * (y / 2 * Real.sqrt y) := by ring
      _ ≤ m * ((y / 2) ^ ((d : ℝ) / 2 - 1) * Real.sqrt y) := by gcongr
      _ ≤ _ := hlow

/-- `2E_1(y) = ∫₁^∞ e^{-ys}(2/s) ds`, `y > 0`. -/
theorem two_mul_expIntegralE1_eq {y : ℝ} (hy : 0 < y) :
    2 * expIntegralE1 y = ∫ s in Ioi (1 : ℝ), Real.exp (-(y * s)) * (2 / s) := by
  have h := integral_comp_mul_left_Ioi (fun v => Real.exp (-v) / v) 1 hy
  rw [mul_one] at h
  rw [expIntegralE1]
  have hc : ∀ s ∈ Ioi (1 : ℝ), Real.exp (-(y * s)) * (2 / s) =
      2 * y * (Real.exp (-(y * s)) / (y * s)) := by
    intro s (hs : 1 < s)
    have : s ≠ 0 := by positivity
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hc, integral_const_mul, h, smul_eq_mul]
  field_simp

theorem integrableOn_exp_neg_div {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun v => Real.exp (-v) / v) (Ioi y) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi y one_pos).const_mul y⁻¹) ?_ ?_
  · exact (by fun_prop : Measurable fun v : ℝ => Real.exp (-v) / v).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : y < v) => ?_)
    have hv0 : 0 < v := by linarith
    rw [Real.norm_of_nonneg (by positivity), neg_mul, one_mul, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hy hv.le) (Real.exp_pos _).le

/-- **`prop:thorin-in-dimension-d`(2), `d ≤ 3`.** `P_1 = 2E_1`, `P_2 = 2K_0`, `P_3 = 2E_1 + 2e^{-y}`
on `(0,∞)`, and the three are completely monotone. -/
theorem thorin_dimension_2_low :
    (∀ y : ℝ, 0 < y → besselTail 1 y = 2 * expIntegralE1 y ∧ besselTail 2 y = 2 * besselK 0 y ∧
      besselTail 3 y = 2 * expIntegralE1 y + 2 * Real.exp (-y)) ∧
      IsCompletelyMonotone (besselTail 1) ∧ IsCompletelyMonotone (besselTail 2) ∧
      IsCompletelyMonotone (besselTail 3) := by
  have h1 : ∀ y : ℝ, 0 < y → besselTail 1 y = 2 * expIntegralE1 y := by
    intro y hy
    rw [besselTail, expIntegralE1, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : y < v) => ?_
    rw [besselProfile_one_pos (by linarith)]
    ring
  have h3 : ∀ y : ℝ, 0 < y → besselTail 3 y = 2 * expIntegralE1 y + 2 * Real.exp (-y) := by
    intro y hy
    have hc : ∀ v ∈ Ioi y, besselProfile 3 v / v =
        2 * (Real.exp (-v) / v) + 2 * Real.exp (-v) := by
      intro v (hv : y < v)
      have hv0 : 0 < v := by linarith
      rw [besselProfile_three_pos hv0]
      field_simp
    have hi2 : IntegrableOn (fun v => Real.exp (-v)) (Ioi y) := by
      simpa using exp_neg_integrableOn_Ioi y one_pos
    rw [besselTail, setIntegral_congr_fun measurableSet_Ioi hc,
      integral_add ((integrableOn_exp_neg_div hy).const_mul 2) (hi2.const_mul 2),
      integral_const_mul, integral_const_mul, integral_exp_neg_Ioi, expIntegralE1]
  have h2 : ∀ y : ℝ, 0 < y → besselTail 2 y = 2 * besselK 0 y := by
    intro y hy
    have hc : ∀ v ∈ Ioi y, besselProfile 2 v / v = 2 * besselK 1 v := by
      intro v (hv : y < v)
      have hv0 : 0 < v := by linarith
      rw [(bessel_k_1_profile (d := 2) hv0).2]
      field_simp
    have hint : IntegrableOn (fun v => -besselK 1 v) (Ioi y) := by
      have h' : IntegrableOn (fun v => -(1 / 2) * (besselProfile 2 v / v)) (Ioi y) :=
        (integrableOn_besselTail_integrand (d := 2) (by norm_num) hy).const_mul _
      refine h'.congr_fun (fun v hv => ?_) measurableSet_Ioi
      simp only
      rw [hc v hv]
      ring
    have hK := integral_Ioi_of_hasDerivAt_of_tendsto
      ((bessel_k_2.1 y hy).continuousAt.continuousWithinAt)
      (fun x (hx : y < x) => bessel_k_2.1 x (by linarith)) hint bessel_k_2.2
    rw [integral_neg, zero_sub, neg_inj] at hK
    rw [besselTail, setIntegral_congr_fun measurableSet_Ioi hc, integral_const_mul, hK]
  -- complete monotonicity
  have hcm1 :
      IsCompletelyMonotone (fun y => ∫ s in Ioi (1 : ℝ), Real.exp (-(y * s)) * (2 / s)) := by
    refine isCompletelyMonotone_laplace (fun s hs => by positivity) fun y hy => ?_
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi 1 hy).const_mul 2) ?_ ?_
    · exact (by fun_prop : Measurable fun s : ℝ =>
        Real.exp (-(y * s)) * (2 / s)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s (hs : 1 < s) => ?_)
      have hs0 : 0 < s := by linarith
      rw [Real.norm_of_nonneg (by positivity), neg_mul, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [div_le_iff₀ hs0]
      linarith
  have hcm1' : IsCompletelyMonotone (besselTail 1) :=
    hcm1.congr fun y (hy : 0 < y) => by rw [h1 y hy, two_mul_expIntegralE1_eq hy]
  refine ⟨fun y hy => ⟨h1 y hy, h2 y hy, h3 y hy⟩, hcm1', ?_, ?_⟩
  · have hw : ∀ s : ℝ, 1 < s → 0 ≤ 2 * (s ^ 2 - 1) ^ (-(1 / 2 : ℝ)) := fun s hs =>
      mul_nonneg zero_le_two (Real.rpow_nonneg (by nlinarith) _)
    refine (isCompletelyMonotone_laplace hw fun y hy => ?_).congr fun y (hy : 0 < y) => ?_
    · have h' : IntegrableOn (fun s => 2 * (Real.exp (-(y * s)) * (s ^ 2 - 1) ^ (-(1 / 2 : ℝ))))
          (Ioi 1) := ((bessel_k_3.1 y hy).1).const_mul 2
      exact h'.congr_fun (fun s _ => by ring) measurableSet_Ioi
    · rw [h2 y hy, (bessel_k_3.1 y hy).2, ← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun s _ => by ring
  · refine (hcm1.add (isCompletelyMonotone_exp_neg.const_mul (a := 2) zero_le_two)).congr
      fun y (hy : 0 < y) => ?_
    rw [h3 y hy, two_mul_expIntegralE1_eq hy]

end Pyramids
