/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.MaternGenerator
import Pyramids.NoFactorization

/-!
# `prop:matern-generator-octave`(1)–(2): the generator's symbol, the octave step

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:matern-generator-octave`. Phase 5, wave 3b.
`matern_generator_octave_1_terms`, `_1_symbol`, `_1_size` and `_2` moved here from
`PyramidsSkeleton.Ch04Matern`, their conclusions unchanged.

* **The terms and the symbol.** Both are `thm:matern-pyramid`(4)'s computation
  (`integral_maternGenerator_char`, `integral_mconvE_mul_char`): tested against the character
  `e^{i⟨·,ω⟩}`, `L_r * g` gives `L̂_r(ω) = (1 + r²|ω|²)⁻¹` times `ĝ(ω)`, and
  `(1 + β|ω|²)⁻¹ - 1 = -β|ω|²/(1 + β|ω|²)`. The bound `4/t` is `2/t` times
  `maternStep_sub_bounded`'s `2`.
* **The size.** With `y = ct|ω| ≥ 1`, `a_i = y²q^{-2(i+1)}` and `M = ⌊log_q y⌋`: the terms
  `i < M` have `a_i ≥ 1` and `1 - a_i/(1 + a_i) ≤ 1/a_i ≤ q^{-2(M-1-i)}`, the terms `i ≥ M` have
  `a_i/(1 + a_i) ≤ a_i < q^{-2(i-M)}`; each geometric tail is at most `G = (1 - q^{-2})⁻¹`. So the
  sum lies in `[M - G, M + G]`, and `M ≤ log_q y < M + 1` gives the constant `C = 2(1 + G)`, one
  for every `t`. Unboundedness follows, `log_q y` being unbounded along an axis.
* **The octave step** is `lem:no-first-order-factorization` read on `ℝ^d` through its
  coordinates, `|ω|² = ∑ ωᵢ²`.

Dropped binders (2026-11-15, a strengthening): `_1_terms` takes no `1 ≤ d`, `1 < q`, `0 < c`;
`_1_symbol` no `1 ≤ d`, `0 < c`, `0 < t`; `_1_size` and `_2` read all theirs.

**What it reaches.** Lean core.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (mconvE)
open scoped Topology ENNReal RealInnerProductSpace

variable {d : ℕ}

/-! ## The terms and the symbol -/

/-- `fourierPlus` against a real function, written as the character integral of
`thm:matern-pyramid`(4). -/
theorem fourierPlus_ofReal_eq (g : Rd d → ℝ) (ω : Rd d) :
    fourierPlus (fun x => (g x : ℂ)) ω =
      ∫ x, (g x : ℂ) * Complex.exp (↑⟪x, ω⟫ * Complex.I) := by
  rw [fourierPlus]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [real_inner_comm, mul_comm]

/-- `(1 + a)⁻¹ - 1 = -a/(1 + a)` for `a ≥ 0`. -/
theorem inv_one_add_sub_one_eq {a : ℝ} (ha : 0 ≤ a) : (1 + a)⁻¹ - 1 = -(a / (1 + a)) := by
  have : (1 + a) ≠ 0 := by positivity
  field_simp
  ring

/-- `β_i|ω|²` in the two forms: `(ct/q^{i+1})²|ω|² = c²t²/q^{2(i+1)} |ω|²`. -/
theorem sq_range_eq (c t q : ℝ) (i : ℕ) (w : ℝ) :
    (c * t / q ^ (i + 1)) ^ 2 * w = c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) * w := by
  rw [div_pow, mul_pow, ← pow_mul, mul_comm (i + 1) 2]

/-- **`prop:matern-generator-octave`(1), the terms.** The term `i` is the symbol of the bounded
operator `(2/t)(L_{ctq^{-i}} - I)`: for every `g ∈ L¹` the image is integrable with
`‖(2/t)(L_{ctq^{-i}} - I)g‖₁ ≤ (4/t)‖g‖₁`, and its transform is
`-(2/t) β_i|ω|²/(1 + β_i|ω|²)` times `ĝ`, `β_i = c² q^{-2i} t²`. No `1 ≤ d`, `1 < q` and
`0 < c` (2026-11-15, a strengthening). -/
theorem matern_generator_octave_1_terms {q c : ℝ} {t : ℝ}
    (ht : 0 < t) (i : ℕ) (g : Rd d → ℝ) (hg : Integrable g) :
    Integrable (fun x => (2 / t) * (mconvE (maternStep d (c * t / q ^ (i + 1))) g x - g x)) ∧
      eLpNorm (fun x => (2 / t) * (mconvE (maternStep d (c * t / q ^ (i + 1))) g x - g x)) 1
          volume ≤ ENNReal.ofReal (4 / t) * eLpNorm g 1 volume ∧
      ∀ ω : Rd d, fourierPlus (fun x => (((2 / t) *
          (mconvE (maternStep d (c * t / q ^ (i + 1))) g x - g x) : ℝ) : ℂ)) ω =
        ((-(2 / t) * (c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) * ‖ω‖ ^ 2 /
          (1 + c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) * ‖ω‖ ^ 2)) : ℝ) : ℂ) *
          fourierPlus (fun x => (g x : ℂ)) ω := by
  set r : ℝ := c * t / q ^ (i + 1) with hr
  obtain ⟨hi, hn⟩ := maternStep_sub_bounded (d := d) r hg
  haveI := (charFun_maternStep (d := d) r 0).1
  refine ⟨hi.const_mul _, ?_, fun ω => ?_⟩
  · have h : (fun x => (2 / t) * (mconvE (maternStep d r) g x - g x)) =
        (2 / t) • fun x => mconvE (maternStep d r) g x - g x := rfl
    rw [h, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    calc ENNReal.ofReal (2 / t) * eLpNorm (fun x => mconvE (maternStep d r) g x - g x) 1 volume
        ≤ ENNReal.ofReal (2 / t) * (2 * eLpNorm g 1 volume) := by gcongr
      _ = ENNReal.ofReal (4 / t) * eLpNorm g 1 volume := by
          rw [← mul_assoc]
          congr 1
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  · set e : Rd d → ℂ := fun x => Complex.exp (↑⟪x, ω⟫ * Complex.I) with he
    have hec : Continuous e := by fun_prop
    have hen : ∀ x, ‖e x‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I _
    have hg1 : Integrable fun x => (g x : ℂ) * e x :=
      hg.ofReal.mul_bdd hec.aestronglyMeasurable (Eventually.of_forall fun x => (hen x).le)
    have hL1 : Integrable fun x => (mconvE (maternStep d r) g x : ℂ) * e x :=
      (ScaleSpace.integrable_mconvE _ hg.1 hg).ofReal.mul_bdd hec.aestronglyMeasurable
        (Eventually.of_forall fun x => (hen x).le)
    rw [fourierPlus_ofReal_eq, fourierPlus_ofReal_eq]
    have hfun : (fun x => ((((2 / t) * (mconvE (maternStep d r) g x - g x)) : ℝ) : ℂ) * e x) =
        fun x => ((2 / t : ℝ) : ℂ) *
          ((mconvE (maternStep d r) g x : ℂ) * e x - (g x : ℂ) * e x) := by
      funext x
      push_cast
      ring
    rw [hfun, integral_const_mul, integral_sub hL1 hg1, integral_mconvE_mul_char _ hg ω,
      (charFun_maternStep _ ω).2]
    have hb : (0 : ℝ) ≤ r ^ 2 * ‖ω‖ ^ 2 := by positivity
    have key : ((2 / t : ℝ) : ℂ) * ((((1 + r ^ 2 * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ) - 1) =
        ((-(2 / t) * (c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) * ‖ω‖ ^ 2 /
          (1 + c ^ 2 * t ^ 2 / q ^ (2 * (i + 1)) * ‖ω‖ ^ 2)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
        inv_one_add_sub_one_eq hb, hr, sq_range_eq]
      congr 1
      ring
    rw [← key]
    ring

/-- **`prop:matern-generator-octave`(1), the symbol.** On `W^{2,1}`, `H_t` has the symbol
`σ_t`. No `1 ≤ d`, `0 < c` and `0 < t` (2026-11-15, a strengthening). -/
theorem matern_generator_octave_1_symbol {q c : ℝ} (hq : 1 < q)
    {t : ℝ} (g : Rd d → ℝ) (hg : IsW21 g) (ω : Rd d) :
    fourierPlus (fun x => (maternGenerator d q c t g x : ℂ)) ω =
      (maternGenSymbol q c t ω : ℂ) * fourierPlus (fun x => (g x : ℂ)) ω := by
  rw [fourierPlus_ofReal_eq, fourierPlus_ofReal_eq, integral_maternGenerator_char hq hg ω]
  congr 1
  rw [maternGenSymbol, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_tsum, neg_mul,
    ← mul_neg, ← tsum_neg]
  congr 1
  refine tsum_congr fun i => ?_
  have hb : (0 : ℝ) ≤ (c * t / q ^ (i + 1)) ^ 2 * ‖ω‖ ^ 2 := by positivity
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, inv_one_add_sub_one_eq hb, sq_range_eq,
    Complex.ofReal_neg]

/-! ## The size -/

/-- The terms `a_i/(1 + a_i)`, `a_i = y² q^{-2(i+1)}`, of the symbol's sum. -/
noncomputable def symTerm (q y : ℝ) (i : ℕ) : ℝ :=
  y ^ 2 / q ^ (2 * (i + 1)) / (1 + y ^ 2 / q ^ (2 * (i + 1)))

/-- `G = (1 - q^{-2})⁻¹ = ∑ⱼ q^{-2j}`. -/
theorem tsum_geom_sq {q : ℝ} (hq : 1 < q) :
    Summable (fun j : ℕ => (q ^ 2)⁻¹ ^ j) ∧
      ∑' j : ℕ, (q ^ 2)⁻¹ ^ j = (1 - (q ^ 2)⁻¹)⁻¹ := by
  have h0 : 0 ≤ (q ^ 2)⁻¹ := by positivity
  have h1 : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
  exact ⟨summable_geometric_of_lt_one h0 h1, tsum_geometric_of_lt_one h0 h1⟩

/-- **The sum between `M - G` and `M + G`**, for `q^M ≤ y < q^{M+1}`. -/
theorem symTerm_bounds {q y : ℝ} (hq : 1 < q) (M : ℕ) (hM : q ^ M ≤ y) (hM' : y < q ^ (M + 1)) :
    Summable (symTerm q y) ∧
      (M : ℝ) - (1 - (q ^ 2)⁻¹)⁻¹ ≤ ∑' i, symTerm q y i ∧
      ∑' i, symTerm q y i ≤ M + (1 - (q ^ 2)⁻¹)⁻¹ := by
  have hq0 : 0 < q := by linarith
  have hy : 0 < y := lt_of_lt_of_le (by positivity) hM
  obtain ⟨hgs, hgt⟩ := tsum_geom_sq hq
  set G := (1 - (q ^ 2)⁻¹)⁻¹ with hG
  set a : ℕ → ℝ := fun i => y ^ 2 / q ^ (2 * (i + 1)) with ha
  have ha0 : ∀ i, 0 < a i := fun i => by positivity
  have hterm : ∀ i, symTerm q y i = a i / (1 + a i) := fun i => rfl
  have hle_a : ∀ i, symTerm q y i ≤ a i := fun i => by
    rw [hterm]; exact div_le_self (ha0 i).le (by linarith [ha0 i])
  have hnn : ∀ i, 0 ≤ symTerm q y i := fun i => by rw [hterm]; have := ha0 i; positivity
  have hle1 : ∀ i, symTerm q y i ≤ 1 := fun i => by
    rw [hterm, div_le_one (by linarith [ha0 i])]; linarith
  -- the tail: `a_{j+M} ≤ q^{-2j}`
  have htail : ∀ j, symTerm q y (j + M) ≤ (q ^ 2)⁻¹ ^ j := by
    intro j
    refine (hle_a _).trans ?_
    have hy2 : y ^ 2 ≤ q ^ (2 * (M + 1)) :=
      calc y ^ 2 ≤ (q ^ (M + 1)) ^ 2 := pow_le_pow_left₀ hy.le hM'.le 2
        _ = q ^ (2 * (M + 1)) := by ring
    have hr : (q ^ 2)⁻¹ ^ j * q ^ (2 * (j + M + 1)) = q ^ (2 * (M + 1)) := by
      rw [inv_pow, ← pow_mul, show 2 * (j + M + 1) = 2 * j + 2 * (M + 1) by ring, pow_add,
        inv_mul_cancel_left₀ (by positivity)]
    simp only [ha]
    rw [div_le_iff₀ (by positivity), hr]
    exact hy2
  have hsumm : Summable (symTerm q y) := by
    refine (summable_nat_add_iff M).1 ?_
    exact Summable.of_nonneg_of_le (fun j => hnn _) htail hgs
  refine ⟨hsumm, ?_, ?_⟩
  · -- lower bound: the first `M` terms, each at least `1 - q^{-2(M-1-i)}`
    have hhead : ∀ i ∈ Finset.range M, 1 - (q ^ 2)⁻¹ ^ (M - 1 - i) ≤ symTerm q y i := by
      intro i hi
      have hi' : i < M := Finset.mem_range.1 hi
      have hqM : (q ^ M) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) hM 2
      have hinv : 1 / a i ≤ (q ^ 2)⁻¹ ^ (M - 1 - i) := by
        simp only [ha]
        rw [one_div_div, div_le_iff₀ (by positivity), inv_pow, ← pow_mul]
        calc q ^ (2 * (i + 1)) = (q ^ (2 * (M - 1 - i)))⁻¹ * (q ^ M) ^ 2 := by
              rw [← pow_mul, eq_inv_mul_iff_mul_eq₀ (by positivity), ← pow_add]
              congr 1
              omega
          _ ≤ (q ^ (2 * (M - 1 - i)))⁻¹ * y ^ 2 := by gcongr
      have hai : 1 - 1 / a i ≤ symTerm q y i := by
        have hne : 1 + a i ≠ 0 := by linarith [ha0 i]
        have e : a i / (1 + a i) = 1 - 1 / (1 + a i) := by
          rw [eq_sub_iff_add_eq, ← add_div, add_comm, div_self hne]
        have h2 : 1 / (1 + a i) ≤ 1 / a i := one_div_le_one_div_of_le (ha0 i) (by linarith)
        rw [hterm, e]
        linarith
      linarith
    have hgeomM : ∑ i ∈ Finset.range M, (q ^ 2)⁻¹ ^ (M - 1 - i) ≤ G := by
      rw [Finset.sum_range_reflect (fun j => (q ^ 2)⁻¹ ^ j) M, ← hgt]
      exact hgs.sum_le_tsum _ fun j _ => by positivity
    calc (M : ℝ) - G ≤ ∑ i ∈ Finset.range M, (1 - (q ^ 2)⁻¹ ^ (M - 1 - i)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          linarith
      _ ≤ ∑ i ∈ Finset.range M, symTerm q y i := Finset.sum_le_sum hhead
      _ ≤ ∑' i, symTerm q y i := hsumm.sum_le_tsum _ fun i _ => hnn i
  · rw [← hsumm.sum_add_tsum_nat_add M]
    have h1 : ∑ i ∈ Finset.range M, symTerm q y i ≤ M := by
      calc ∑ i ∈ Finset.range M, symTerm q y i ≤ ∑ i ∈ Finset.range M, (1 : ℝ) :=
            Finset.sum_le_sum fun i _ => hle1 i
        _ = M := by simp
    have h2 : ∑' j, symTerm q y (j + M) ≤ G := by
      rw [← hgt]
      exact ((summable_nat_add_iff M).2 hsumm).tsum_le_tsum htail hgs
    linarith

/-- **`|∑ a_i/(1 + a_i) - log_q y| ≤ 1 + G`** for `y ≥ 1`. -/
theorem symTerm_logb {q y : ℝ} (hq : 1 < q) (hy : 1 ≤ y) :
    |∑' i, symTerm q y i - Real.logb q y| ≤ 1 + (1 - (q ^ 2)⁻¹)⁻¹ := by
  have hq0 : 0 < q := by linarith
  have hy0 : 0 < y := by linarith
  have hl0 : 0 ≤ Real.logb q y := Real.logb_nonneg hq hy
  set M := ⌊Real.logb q y⌋₊ with hMdef
  have hM1 : (M : ℝ) ≤ Real.logb q y := Nat.floor_le hl0
  have hM2 : Real.logb q y < M + 1 := Nat.lt_floor_add_one _
  have hqM : q ^ M ≤ y := by
    rw [← Real.rpow_natCast, ← Real.rpow_logb hq0 hq.ne' hy0]
    exact Real.rpow_le_rpow_of_exponent_le hq.le hM1
  have hqM' : y < q ^ (M + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_logb hq0 hq.ne' hy0]
    refine Real.rpow_lt_rpow_of_exponent_lt hq ?_
    push_cast
    exact hM2
  obtain ⟨-, hlo, hhi⟩ := symTerm_bounds hq M hqM hqM'
  rw [abs_le]
  constructor <;> linarith

/-- `σ_t(ω) = -(2/t) ∑ symTerm q (ct|ω|)`. -/
theorem maternGenSymbol_eq (q c t : ℝ) (ω : Rd d) :
    maternGenSymbol q c t ω = -(2 / t) * ∑' i, symTerm q (c * t * ‖ω‖) i := by
  rw [maternGenSymbol]
  congr 1
  refine tsum_congr fun i => ?_
  rw [symTerm, mul_pow, mul_pow, div_mul_eq_mul_div]

/-- `|σ_t(ω)| = (2/t) ∑ symTerm q (ct|ω|)` for `t > 0`. -/
theorem abs_maternGenSymbol {q c t : ℝ} (hq : 0 < q) (ht : 0 < t) (ω : Rd d) :
    |maternGenSymbol q c t ω| = 2 / t * ∑' i, symTerm q (c * t * ‖ω‖) i := by
  rw [maternGenSymbol_eq, abs_mul, abs_neg, abs_of_pos (by positivity),
    abs_of_nonneg (tsum_nonneg fun i => by rw [symTerm]; positivity)]

/-- **`prop:matern-generator-octave`(1), the size.** `σ_t` is unbounded, and
`|σ_t(ω)| = (2/t) log_q(ct|ω|) + O(1/t)` as `|ω| → ∞`: with one constant `C` for every `t > 0`,
the error is at most `C/t` once `ct|ω| ≥ 1`. -/
theorem matern_generator_octave_1_size (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    (∀ t : ℝ, 0 < t → ¬ ∃ B : ℝ, ∀ ω : Rd d, |maternGenSymbol q c t ω| ≤ B) ∧
      ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ ω : Rd d, 1 ≤ c * t * ‖ω‖ →
        |abs (maternGenSymbol q c t ω) - 2 / t * Real.logb q (c * t * ‖ω‖)| ≤ C / t := by
  set G := (1 - (q ^ 2)⁻¹)⁻¹ with hG
  have hsize : ∀ t : ℝ, 0 < t → ∀ ω : Rd d, 1 ≤ c * t * ‖ω‖ →
      |abs (maternGenSymbol q c t ω) - 2 / t * Real.logb q (c * t * ‖ω‖)| ≤ 2 * (1 + G) / t := by
    intro t ht ω hω
    rw [abs_maternGenSymbol (by linarith) ht, ← mul_sub, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / t)]
    have h := symTerm_logb hq hω
    calc 2 / t * |∑' i, symTerm q (c * t * ‖ω‖) i - Real.logb q (c * t * ‖ω‖)|
        ≤ 2 / t * (1 + G) := by gcongr
      _ = 2 * (1 + G) / t := by ring
  refine ⟨fun t ht => ?_, ⟨2 * (1 + G), hsize⟩⟩
  rintro ⟨B, hB⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (t * B / 2 + 1 + G)
  set ρ : ℝ := q ^ N / (c * t) with hρ_def
  have hρ : 0 < ρ := by have : 0 < q := by linarith
                        positivity
  set ω : Rd d := ρ • ebasis (⟨0, hd⟩ : Fin d) with hω_def
  have hω : ‖ω‖ = ρ := by rw [hω_def, norm_smul, norm_ebasis, mul_one, Real.norm_of_nonneg hρ.le]
  have hy : c * t * ‖ω‖ = q ^ N := by rw [hω, hρ_def]; field_simp
  have h1 : 1 ≤ c * t * ‖ω‖ := by rw [hy]; exact one_le_pow₀ hq.le
  have hlog : Real.logb q (c * t * ‖ω‖) = N := by
    rw [hy, Real.logb_pow, Real.logb_self_eq_one hq, mul_one]
  have h := hsize t ht ω h1
  rw [hlog, abs_le] at h
  have hb := hB ω
  have hb' : |maternGenSymbol q c t ω| ≤ B := hb
  have h2 : 2 / t * N - 2 * (1 + G) / t ≤ B := by linarith [h.1]
  have h3 : 2 / t * N - 2 * (1 + G) / t = 2 / t * (N - (1 + G)) := by ring
  rw [h3, div_mul_eq_mul_div, div_le_iff₀ ht] at h2
  nlinarith

/-! ## Clause (2): the octave step -/

/-- **`prop:matern-generator-octave`(2).** For `d ≥ 2` and `r > 0`, `1 + r²|ω|²` is not the product
of two polynomials of degree at most one with complex coefficients. -/
theorem matern_generator_octave_2 (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) :
    ¬ ∃ (α α' : ℂ) (β β' : Fin d → ℂ), ∀ ω : Rd d,
      (((1 + r ^ 2 * ‖ω‖ ^ 2 : ℝ)) : ℂ) =
        (α + ∑ i, β i * (ω i : ℂ)) * (α' + ∑ i, β' i * (ω i : ℂ)) := by
  rintro ⟨α, α', β, β', h⟩
  refine no_first_order_factorization hd hr ⟨α, α', β, β', fun ω => ?_⟩
  have h' := h (WithLp.toLp 2 ω)
  rw [EuclideanSpace.norm_sq_eq] at h'
  simpa using h'

end Pyramids
