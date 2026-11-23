/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.QCinRepr

/-!
# `prop:strata-cylinder-coordinates-q-cin`(2): the `q`-Cin rays tend to the Cin ray

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:strata-cylinder-coordinates-q-cin`. Wave 3a:
`qcin_2` and `qcin_2_limit` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in statement and
name.

## The route

Let `x = τω > 0` and `b_i = xq^{-i}`. `Cin(x)` is the sum of the pieces
`Cin(b_i) - Cin(b_i/q) = ∫_{b_i/q}^{b_i} (1 - cos v) dv/v`, which telescope to `Cin(x)` since
`Cin(xq^{-n}) → Cin(0) = 0`; and `ℓ(1 - cos b) = ∫_{b/q}^{b} (1 - cos b) dv/v`. The difference of
the two integrands is `(cos v - cos b)/v`, at most `(b - v)/v` in absolute value, whose integral is
`b(ℓ - 1 + 1/q)` (`cin_piece_bound`). Then `ℓ - 1 + 1/q ≤ ℓ²/2`, which is `e^{-ℓ} ≤ 1 - ℓ + ℓ²/2`
(`log_sub_one_add_inv_le`, from `e^ℓ ≥ 1 + ℓ + ℓ²/2 + ℓ³/6`), and `∑_i b_i = xq/(q - 1)`.
Negative `x` follow by evenness. For the limit, `qℓ²/(2(q - 1)) ≤ qℓ/2 → 0`, since `ℓ ≤ q - 1`.

The proof of record substitutes `v = xe^{-u}` and compares a Riemann sum with its integral; the
checked route stays in the variable `v`, and its constant is the same.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (cin cinIntegrand continuous_cin continuous_cinIntegrand monotoneOn_cin cin_zero
  cin_neg intervalIntegrable_cinIntegrand)
open scoped Topology

/-- `ℓ - 1 + 1/q ≤ ℓ²/2` for `q > 1`, `ℓ = log q`: that is `e^{-ℓ} ≤ 1 - ℓ + ℓ²/2`. -/
theorem log_sub_one_add_inv_le {q : ℝ} (hq : 1 < q) :
    Real.log q - 1 + 1 / q ≤ Real.log q ^ 2 / 2 := by
  have hq0 : 0 < q := by linarith
  set t := Real.log q with ht
  have ht0 : 0 ≤ t := Real.log_nonneg hq.le
  have he : Real.exp t = q := by rw [ht, Real.exp_log hq0]
  have h4 := Real.sum_le_exp_of_nonneg ht0 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    Nat.cast_ofNat, pow_zero, pow_one, zero_add, Nat.succ_eq_add_one, Nat.reduceAdd,
    Nat.reduceMul, div_one] at h4
  rw [he] at h4
  -- `(1 - t + t²/2)(1 + t + t²/2 + t³/6) ≥ 1`
  have hQ : 0 ≤ 1 - t + t ^ 2 / 2 := by nlinarith [sq_nonneg (t - 1)]
  have hQP : 1 ≤ (1 - t + t ^ 2 / 2) * q := by
    have h1 : (1 - t + t ^ 2 / 2) * (1 + t + t ^ 2 / 2 + t ^ 3 / 6) ≤ (1 - t + t ^ 2 / 2) * q :=
      mul_le_mul_of_nonneg_left (by linarith) hQ
    have h2 : 1 ≤ (1 - t + t ^ 2 / 2) * (1 + t + t ^ 2 / 2 + t ^ 3 / 6) := by
      nlinarith [pow_nonneg ht0 3, pow_nonneg ht0 4, pow_nonneg ht0 5]
    linarith
  have : 1 / q ≤ 1 - t + t ^ 2 / 2 := by
    rw [div_le_iff₀ hq0]
    linarith
  linarith

/-- **One piece.** For `b > 0`, `|ℓ(1 - cos b) - (Cin(b) - Cin(b/q))| ≤ b(ℓ - 1 + 1/q)`. -/
theorem cin_piece_bound {q b : ℝ} (hq : 1 < q) (hb : 0 < b) :
    |Real.log q * (1 - Real.cos b) - (cin b - cin (b / q))| ≤ b * (Real.log q - 1 + 1 / q) := by
  have hq0 : 0 < q := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  have hbne : b ≠ 0 := hb.ne'
  have hbq : 0 < b / q := div_pos hb hq0
  have hbq_le : b / q ≤ b := div_le_self hb.le hq.le
  have hnot0 : (0 : ℝ) ∉ uIcc (b / q) b := by
    rw [uIcc_of_le hbq_le]
    exact fun h => absurd h.1 (not_le.2 hbq)
  have hInv : IntervalIntegrable (fun v : ℝ => v⁻¹) volume (b / q) b :=
    (continuousOn_inv₀.mono fun v hv (h0 : v = 0) => hnot0 (h0 ▸ hv)).intervalIntegrable
  have hratio : b / (b / q) = q := by field_simp
  have hpiece : cin b - cin (b / q) = ∫ v in (b / q)..b, cinIntegrand v :=
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_cinIntegrand hb.le)
      (intervalIntegrable_cinIntegrand hbq.le)
  have hlog : Real.log q * (1 - Real.cos b) = ∫ v in (b / q)..b, (1 - Real.cos b) * v⁻¹ := by
    rw [intervalIntegral.integral_const_mul, integral_inv hnot0, hratio]
    ring
  have hg : ∫ v in (b / q)..b, (b * v⁻¹ - 1) = b * (Real.log q - 1 + 1 / q) := by
    rw [intervalIntegral.integral_sub (hInv.const_mul b) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_inv hnot0, intervalIntegral.integral_const,
      hratio, smul_eq_mul, mul_one]
    ring
  rw [hpiece, hlog, ← intervalIntegral.integral_sub (hInv.const_mul _)
    (continuous_cinIntegrand.intervalIntegrable _ _), ← hg, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le hbq_le (ae_of_all _ fun v hv => ?_)
    ((hInv.const_mul b).sub intervalIntegrable_const)
  have hv0 : 0 < v := hbq.trans hv.1
  have hvb : v ≤ b := hv.2
  have hdiff : (1 - Real.cos b) * v⁻¹ - cinIntegrand v = (Real.cos v - Real.cos b) * v⁻¹ := by
    rw [cinIntegrand, div_eq_mul_inv]
    ring
  have hcos := Real.abs_cos_sub_cos_le v b
  rw [abs_of_nonpos (by linarith : v - b ≤ 0)] at hcos
  have hrhs : b * v⁻¹ - 1 = (b - v) * v⁻¹ := by
    field_simp
  rw [hdiff, hrhs, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hv0)]
  exact mul_le_mul_of_nonneg_right (by linarith) (inv_pos.2 hv0).le

/-- **The bound for `x > 0`.** `|ℓ∑_i (1 - cos(xq^{-i})) - Cin(x)| ≤ qℓ²/(2(q - 1)) x`. -/
theorem cinSeries_bound {q x : ℝ} (hq : 1 < q) (hx : 0 < x) :
    |Real.log q * ∑' i : ℕ, (1 - Real.cos (x / q ^ i)) - cin x| ≤
      q * Real.log q ^ 2 / (2 * (q - 1)) * x := by
  have hq0 : 0 < q := by linarith
  have hqi : ∀ i : ℕ, 0 < q ^ i := fun i => pow_pos hq0 i
  have hb : ∀ i : ℕ, 0 < x / q ^ i := fun i => div_pos hx (hqi i)
  have hsucc : ∀ i : ℕ, x / q ^ i / q = x / q ^ (i + 1) := fun i => by rw [pow_succ, div_div]
  have hs : Summable fun i : ℕ => 1 - Real.cos (x / q ^ i) :=
    (qCinRay_summable hq x 1).congr fun i => by rw [one_mul]
  -- the pieces of `Cin` telescope
  have hpieces : HasSum (fun i : ℕ => cin (x / q ^ i) - cin (x / q ^ (i + 1))) (cin x) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have htel : ∀ n : ℕ, ∑ i ∈ Finset.range n, (cin (x / q ^ i) - cin (x / q ^ (i + 1))) =
          cin x - cin (x / q ^ n) := by
        intro n
        rw [Finset.sum_range_sub' (fun i => cin (x / q ^ i)) n]
        simp
      simp only [htel]
      have h0 : Tendsto (fun n : ℕ => x / q ^ n) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hq)
      have h2 : Tendsto (fun n : ℕ => cin x - cin (x / q ^ n)) atTop (𝓝 (cin x - cin 0)) :=
        tendsto_const_nhds.sub ((continuous_cin.tendsto 0).comp h0)
      rwa [cin_zero, sub_zero] at h2
    · intro i
      refine sub_nonneg.2 (monotoneOn_cin (hb (i + 1)).le (hb i).le ?_)
      exact div_le_div_of_nonneg_left hx.le (hqi i) (pow_le_pow_right₀ hq.le (Nat.le_succ i))
  have hd : HasSum (fun i : ℕ => Real.log q * (1 - Real.cos (x / q ^ i)) -
      (cin (x / q ^ i) - cin (x / q ^ (i + 1))))
      (Real.log q * ∑' i : ℕ, (1 - Real.cos (x / q ^ i)) - cin x) :=
    (hs.hasSum.mul_left _).sub hpieces
  have hr : 0 ≤ q⁻¹ := by positivity
  have hr1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have he : HasSum (fun i : ℕ => x / q ^ i * (Real.log q - 1 + 1 / q))
      (x * (1 - q⁻¹)⁻¹ * (Real.log q - 1 + 1 / q)) := by
    have := ((hasSum_geometric_of_lt_one hr hr1).mul_left x).mul_right (Real.log q - 1 + 1 / q)
    have hfun : (fun i : ℕ => x / q ^ i * (Real.log q - 1 + 1 / q)) =
        fun i => x * q⁻¹ ^ i * (Real.log q - 1 + 1 / q) :=
      funext fun i => by rw [inv_pow, div_eq_mul_inv]
    rw [hfun]
    exact this
  have hpiece : ∀ i : ℕ, |Real.log q * (1 - Real.cos (x / q ^ i)) -
      (cin (x / q ^ i) - cin (x / q ^ (i + 1)))| ≤ x / q ^ i * (Real.log q - 1 + 1 / q) := by
    intro i
    rw [← hsucc i]
    exact cin_piece_bound hq (hb i)
  have hle := hasSum_le (fun i => (abs_le.1 (hpiece i)).2) hd he
  have hge := hasSum_le (fun i => (abs_le.1 (hpiece i)).1) he.neg hd
  have hfac : (1 - q⁻¹)⁻¹ = q / (q - 1) := by
    have : q - 1 ≠ 0 := by linarith
    field_simp
  have hE : x * (1 - q⁻¹)⁻¹ * (Real.log q - 1 + 1 / q) ≤
      q * Real.log q ^ 2 / (2 * (q - 1)) * x := by
    rw [hfac]
    calc x * (q / (q - 1)) * (Real.log q - 1 + 1 / q)
        ≤ x * (q / (q - 1)) * (Real.log q ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (log_sub_one_add_inv_le hq)
            (mul_nonneg hx.le (div_nonneg hq0.le (by linarith)))
      _ = q * Real.log q ^ 2 / (2 * (q - 1)) * x := by
          have : q - 1 ≠ 0 := by linarith
          field_simp
  rw [abs_le]
  constructor <;> linarith

/-- **`prop:strata-cylinder-coordinates-q-cin`(2), the bound.**
`|ℓE^{(q)}_τ(ω) - Cin(τω)| ≤ qℓ²/(2(q - 1)) |τω|`. The hypothesis `0 < τ` of the skeleton is
dropped (2026-11-14, a strengthening): the series depends on `τω` only, and `τω = 0` is trivial. -/
theorem qcin_2 {q : ℝ} (hq : 1 < q) (τ ω : ℝ) :
    |Real.log q * qCinRay q τ ω - cin (τ * ω)| ≤
      q * Real.log q ^ 2 / (2 * (q - 1)) * |τ * ω| := by
  have hser : ∀ ω : ℝ, qCinRay q τ ω = ∑' i : ℕ, (1 - Real.cos (τ * ω / q ^ i)) := fun ω =>
    tsum_congr fun i => by rw [show ω * (τ / q ^ i) = τ * ω / q ^ i by ring]
  rcases lt_trichotomy (τ * ω) 0 with h | h | h
  · have h' : 0 < τ * -ω := by
      rw [mul_neg]
      exact neg_pos.2 h
    have e1 : qCinRay q τ ω = qCinRay q τ (-ω) := by
      unfold qCinRay
      exact tsum_congr fun i => by rw [neg_mul, Real.cos_neg]
    rw [e1, hser, abs_of_neg h, show -(τ * ω) = τ * -ω by ring,
      show cin (τ * ω) = cin (τ * -ω) by rw [mul_neg, cin_neg]]
    exact cinSeries_bound hq h'
  · rw [hser, h]
    simp [cin_zero]
  · rw [hser, abs_of_pos h]
    exact cinSeries_bound hq h

/-- **`prop:strata-cylinder-coordinates-q-cin`(2), the limit.** `ℓE^{(q)}_τ → Cin(τ ·)` as
`q ↓ 1`, uniformly on bounded sets of `τω`. The conjunct `0 < τ` of the skeleton's set is dropped
(2026-11-14, a strengthening), as in `qcin_2`. -/
theorem qcin_2_limit (R : ℝ) :
    TendstoUniformlyOn (fun (q : ℝ) (p : ℝ × ℝ) => Real.log q * qCinRay q p.1 p.2)
      (fun p => cin (p.1 * p.2)) (𝓝[>] 1) {p : ℝ × ℝ | |p.1 * p.2| ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun q : ℝ => q * Real.log q / 2 * (|R| + 1)) (𝓝[>] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun q : ℝ => q * Real.log q / 2 * (|R| + 1)) 1 :=
      ((continuousAt_id.mul (Real.continuousAt_log one_ne_zero)).div_const 2).mul_const _
    have := hc.tendsto
    simp only [Real.log_one, mul_zero, zero_div, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  filter_upwards [hlim (Iio_mem_nhds hε), self_mem_nhdsWithin] with q hqε hq1
  intro p hp
  have hq : 1 < q := hq1
  have hq0 : 0 < q := by linarith
  have hℓ0 : 0 ≤ Real.log q := Real.log_nonneg hq.le
  have hℓ : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos hq0
  have hK : q * Real.log q ^ 2 / (2 * (q - 1)) ≤ q * Real.log q / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hℓ (mul_nonneg hq0.le hℓ0)]
  have hpR : |p.1 * p.2| ≤ |R| + 1 := by
    have hp' : |p.1 * p.2| ≤ R := hp
    linarith [le_abs_self R]
  rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm]
  calc |Real.log q * qCinRay q p.1 p.2 - cin (p.1 * p.2)|
      ≤ q * Real.log q ^ 2 / (2 * (q - 1)) * |p.1 * p.2| := qcin_2 hq p.1 p.2
    _ ≤ q * Real.log q / 2 * (|R| + 1) :=
        mul_le_mul hK hpR (abs_nonneg _) (by positivity)
    _ < ε := hqε

end Pyramids
