/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.LadderKnot
import AffineHemigroup.OriginLowerBound
import Mathlib.Analysis.PSeries

/-!
# `prop:ladder-not-every-frequency`: the partial products at one frequency

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:ladder-not-every-frequency`. Wave 3a:
`ladder_not_every_frequency` moved here from `PyramidsSkeleton.Ch03Pyramid`, unchanged in statement
and name.

## The route

* **The compound Poisson law** is the affine export's `cpLaw`, `e^{-ν(ℝ)} ∑ ν^{*n}/n!`, a
  probability law with the transform `e^{-ν(ℝ)} exp ν̂` (`isProbabilityMeasure_cpLaw`,
  `charFun_cpLaw`). For the symmetric `ν = ν_ϱ` this is `exp[-∫ (1 - cos⟨ω,x⟩) ν(dx)]`
  (`charFun_cpLaw_symm`), and any law with that transform is `cpLaw ν` (`Measure.ext_of_charFun`).
* **Carried by `ℤ`**: `ν` is, and a convolution of two laws carried by the additive subgroup
  `{x : x₀ ∈ ℤ}` is carried by it (`conv_intPts_null`).
* **Infinitely divisible**: `cpLaw ν = (cpLaw (ν/n))^{*n}`, the transforms being equal.
* **The partial products at `2π`** are `exp(-∑_{m<M} g(m))`, `g(m) = ∑_j j^{-2}(1 - cos(2π2^{j-m}))`
  (the sum written from `j = 0` with `(j+1)^{-2}` and `2^{j+1}`). The terms with `m ≤ j` vanish and
  the others are at most `2π²(j+1)^{-2}4^{-(m-j)}`, so the double series converges (Tonelli in
  `[0,∞]`), and the partial products tend to `exp(-∑ g) > 0`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal RealInnerProductSpace

/-! ## The measure `ν_ϱ` -/

/-- The weight `(j+1)^{-2}` of the pair of atoms at `±2^{j+1}`. -/
noncomputable def notEveryW (j : ℕ) : ℝ := (((j : ℝ) + 1) ^ 2)⁻¹

theorem notEveryW_nonneg (j : ℕ) : 0 ≤ notEveryW j := by unfold notEveryW; positivity

theorem summable_notEveryW : Summable notEveryW := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine h.congr fun j => ?_
  simp [notEveryW]

/-- The atom `a • e₀` of `ℝ¹`. -/
theorem ebasis_smul_apply (a : ℝ) : ((a • ebasis (0 : Fin 1) : Rd 1) 0) = a := by simp [ebasis]

theorem norm_ebasis_smul (a : ℝ) : ‖(a • ebasis (0 : Fin 1) : Rd 1)‖ = |a| := by
  simp [ebasis, norm_smul]

theorem inner_ebasis_smul (ω : Rd 1) (a : ℝ) :
    ⟪ω, (a • ebasis (0 : Fin 1) : Rd 1)⟫ = a * ω 0 := by
  simp [ebasis, inner_smul_right, EuclideanSpace.inner_single_right]

/-- **`ν_ϱ(B) = ∑ⱼ (j+1)^{-2}/2 (𝟙_B(2^{j+1}e₀) + 𝟙_B(-2^{j+1}e₀))`**. -/
theorem notEveryNu_apply {B : Set (Rd 1)} (hB : MeasurableSet B) :
    notEveryNu B = ∑' j : ℕ, ENNReal.ofReal (notEveryW j / 2) *
      (B.indicator 1 (((2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1)) +
        B.indicator 1 ((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1))) := by
  rw [notEveryNu, Measure.sum_apply _ hB]
  simp only [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hB, smul_eq_mul,
    notEveryW]

theorem notEveryNu_univ : notEveryNu univ = ENNReal.ofReal (∑' j, notEveryW j) := by
  rw [notEveryNu_apply MeasurableSet.univ,
    ENNReal.ofReal_tsum_of_nonneg notEveryW_nonneg summable_notEveryW]
  refine tsum_congr fun j => ?_
  simp only [indicator_univ, Pi.one_apply, one_add_one_eq_two]
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by have := notEveryW_nonneg j; positivity)]
  ring_nf

instance isFiniteMeasure_notEveryNu : IsFiniteMeasure notEveryNu :=
  ⟨by rw [notEveryNu_univ]; exact ENNReal.ofReal_lt_top⟩

theorem notEveryNu_symm : notEveryNu.map (fun x => -x) = notEveryNu := by
  ext B hB
  rw [Measure.map_apply measurable_neg hB, notEveryNu_apply hB,
    notEveryNu_apply (measurable_neg hB)]
  refine tsum_congr fun j => ?_
  rw [add_comm]
  congr 2
  · have h : ((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1) : Rd 1) ∈ Neg.neg ⁻¹' B ↔
        ((2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1) ∈ B := by
      change -((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1)) ∈ B ↔ _
      rw [neg_smul, neg_neg]
    simp only [indicator]
    by_cases hb : ((2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1) ∈ B
    · rw [if_pos (h.2 hb), if_pos hb]; rfl
    · rw [if_neg (fun h' => hb (h.1 h')), if_neg hb]
  · have h : ((2 : ℝ) ^ (j + 1) • ebasis (0 : Fin 1) : Rd 1) ∈ Neg.neg ⁻¹' B ↔
        ((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1)) ∈ B := by
      change -((2 : ℝ) ^ (j + 1) • ebasis (0 : Fin 1)) ∈ B ↔ _
      rw [neg_smul]
    simp only [indicator]
    by_cases hb : ((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1) : Rd 1) ∈ B
    · rw [if_pos (h.2 hb), if_pos hb]; rfl
    · rw [if_neg (fun h' => hb (h.1 h')), if_neg hb]

/-- **The integral against `ν_ϱ`** of a bounded continuous function. -/
theorem integral_notEveryNu {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {g : Rd 1 → G} (hgc : Continuous g) (C : ℝ) (hgb : ∀ x, ‖g x‖ ≤ C) :
    ∫ x, g x ∂notEveryNu = ∑' j : ℕ, (notEveryW j / 2) •
      (g (((2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1)) +
        g ((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1))) := by
  have hint : ∀ (μ : Measure (Rd 1)) [IsFiniteMeasure μ], Integrable g μ := fun μ _ =>
    Integrable.of_bound hgc.aestronglyMeasurable C (ae_of_all _ hgb)
  have hg' := hint notEveryNu
  rw [notEveryNu] at hg'
  rw [notEveryNu, integral_sum_measure hg']
  refine tsum_congr fun j => ?_
  rw [integral_smul_measure, integral_add_measure (hint _) (hint _), integral_dirac,
    integral_dirac, ENNReal.toReal_ofReal (by positivity)]
  rfl


theorem indicator_one_congr {α β : Type*} {s : Set α} {t : Set β} {a : α} {b : β}
    (h : a ∈ s ↔ b ∈ t) : s.indicator (1 : α → ℝ≥0∞) a = t.indicator 1 b := by
  by_cases hb : b ∈ t
  · rw [indicator_of_mem (h.2 hb), indicator_of_mem hb]; rfl
  · rw [indicator_of_notMem (fun h' => hb (h.1 h')), indicator_of_notMem hb]

/-- `∫ (1 - cos⟨ω,x⟩) ν_ϱ(dx) = ∑ⱼ (j+1)^{-2}(1 - cos(2^{j+1}ω₀))`. -/
theorem integral_one_sub_cos_notEveryNu (ω : Rd 1) :
    ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂notEveryNu =
      ∑' j : ℕ, notEveryW j * (1 - Real.cos ((2 : ℝ) ^ (j + 1) * ω 0)) := by
  rw [integral_notEveryNu (by fun_prop) 2 (fun x => by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.cos_le_one ⟪ω, x⟫, Real.neg_one_le_cos ⟪ω, x⟫])]
  refine tsum_congr fun j => ?_
  rw [inner_ebasis_smul, inner_ebasis_smul, smul_eq_mul, neg_mul, Real.cos_neg]
  ring

/-! ## The compound Poisson law of a symmetric finite measure -/

/-- **`π̂_L(ξ) = exp[-∫ (1 - cos⟨ξ,x⟩) L(dx)]`** for a symmetric finite `L`. -/
theorem charFun_cpLaw_symm {d : ℕ} (L : Measure (Rd d)) [IsFiniteMeasure L]
    (hsym : L.map (fun x => -x) = L) (ξ : Rd d) :
    charFun (cpLaw L) ξ = ((Real.exp (-∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂L) : ℝ) : ℂ) := by
  have hint : Integrable (fun x : Rd d => Real.cos ⟪x, ξ⟫) L :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hcomm : ∀ x : Rd d, ⟪ξ, x⟫ = ⟪x, ξ⟫ := fun x => real_inner_comm x ξ
  have hI : ∫ x, (1 - Real.cos ⟪ξ, x⟫) ∂L = (L univ).toReal - ∫ x, Real.cos ⟪x, ξ⟫ ∂L := by
    simp_rw [hcomm]
    rw [integral_sub (integrable_const 1) hint]
    simp [integral_const, measureReal_def]
  rw [charFun_cpLaw, charFun_of_symm L hsym ξ, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    ← Real.exp_add, hI]
  congr 2
  ring

/-! ## Laws carried by the integers -/

/-- **The integer points `{x : x₀ ∈ ℤ}` of `ℝ¹`**. -/
def intPts : Set (Rd 1) := {x | ∃ k : ℤ, x 0 = k}

theorem measurableSet_intPts : MeasurableSet intPts := by
  have e : intPts = (fun x : Rd 1 => x 0) ⁻¹' range (Int.cast : ℤ → ℝ) := by
    ext x
    simp only [intPts, mem_setOf_eq, mem_preimage, mem_range]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
  rw [e]
  exact (by fun_prop : Continuous fun x : Rd 1 => x 0).measurable
    (Set.countable_range _).measurableSet

theorem zero_mem_intPts : (0 : Rd 1) ∈ intPts := ⟨0, by simp⟩

theorem add_mem_intPts {x y : Rd 1} (hx : x ∈ intPts) (hy : y ∈ intPts) : x + y ∈ intPts := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [show (x + y) 0 = x 0 + y 0 from rfl, ha, hb]
  push_cast
  ring

/-- A convolution of two measures carried by the integer points is carried by them. -/
theorem conv_intPts_null {μ ν : Measure (Rd 1)} [SFinite μ] [SFinite ν]
    (hμ : μ intPtsᶜ = 0) (hν : ν intPtsᶜ = 0) : (μ ∗ ν) intPtsᶜ = 0 := by
  rw [Measure.conv, Measure.map_apply measurable_add measurableSet_intPts.compl]
  refine measure_mono_null (t := (intPtsᶜ ×ˢ univ) ∪ (univ ×ˢ intPtsᶜ)) (fun p hp => ?_)
    (measure_union_null ?_ ?_)
  · by_contra hc
    simp only [mem_union, mem_prod, mem_compl_iff, mem_univ, and_true, true_and, not_or,
      not_not] at hc
    exact hp (add_mem_intPts hc.1 hc.2)
  · rw [Measure.prod_prod, hμ, zero_mul]
  · rw [Measure.prod_prod, hν, mul_zero]

theorem cpLaw_intPts_null (L : Measure (Rd 1)) [IsFiniteMeasure L] (hL : L intPtsᶜ = 0) :
    cpLaw L intPtsᶜ = 0 := by
  have hpow : ∀ n : ℕ, ScaleSpace.convPow L n intPtsᶜ = 0 := by
    intro n
    induction n with
    | zero =>
      rw [ScaleSpace.convPow, Measure.dirac_apply' _ measurableSet_intPts.compl,
        indicator_of_notMem (not_not.2 zero_mem_intPts)]
    | succ n ih =>
      haveI := ScaleSpace.isFiniteMeasure_convPow_Rd L n
      rw [ScaleSpace.convPow]
      exact conv_intPts_null ih hL
  rw [cpLaw, Measure.sum_apply _ measurableSet_intPts.compl, ENNReal.tsum_eq_zero]
  intro n
  rw [Measure.smul_apply, hpow n, smul_zero]

theorem notEveryNu_intPts_null : notEveryNu intPtsᶜ = 0 := by
  rw [notEveryNu_apply measurableSet_intPts.compl, ENNReal.tsum_eq_zero]
  intro j
  have h1 : ((2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1) ∈ intPts :=
    ⟨2 ^ (j + 1), by rw [ebasis_smul_apply]; push_cast; ring⟩
  have h2 : ((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1) : Rd 1) ∈ intPts :=
    ⟨-2 ^ (j + 1), by rw [ebasis_smul_apply]; push_cast; ring⟩
  rw [indicator_of_notMem (not_not.2 h1), indicator_of_notMem (not_not.2 h2), add_zero, mul_zero]

/-! ## The partial products at `2π` -/

/-- The term `(j+1)^{-2}(1 - cos(2^{j+1} 2^{-(m+1)} 2π))` of `-log ϱ̂(2^{-(m+1)}2π)`. -/
noncomputable def gNE (m j : ℕ) : ℝ :=
  notEveryW j * (1 - Real.cos ((2 : ℝ) ^ (j + 1) * ((2 : ℝ) ^ (-((m : ℤ) + 1)) * (2 * Real.pi))))

theorem gNE_nonneg (m j : ℕ) : 0 ≤ gNE m j := by
  unfold gNE
  exact mul_nonneg (notEveryW_nonneg j) (sub_nonneg.2 (Real.cos_le_one _))

theorem gNE_le (m j : ℕ) : gNE m j ≤ 2 * notEveryW j := by
  unfold gNE
  have h1 := notEveryW_nonneg j
  have h2 := Real.neg_one_le_cos ((2 : ℝ) ^ (j + 1) * ((2 : ℝ) ^ (-((m : ℤ) + 1)) * (2 * Real.pi)))
  nlinarith

theorem two_pow_mul_zpow (j m : ℕ) :
    (2 : ℝ) ^ (j + 1) * (2 : ℝ) ^ (-((m : ℤ) + 1)) = (2 : ℝ) ^ ((j : ℤ) - m) := by
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
  congr 1
  push_cast
  ring

/-- The terms with `m ≤ j` vanish: `2^{j-m}` is an integer. -/
theorem gNE_eq_zero {m j : ℕ} (h : m ≤ j) : gNE m j = 0 := by
  unfold gNE
  rw [← mul_assoc, two_pow_mul_zpow, show (j : ℤ) - m = ((j - m : ℕ) : ℤ) by omega,
    zpow_natCast, show (2 : ℝ) ^ (j - m) = ((2 ^ (j - m) : ℕ) : ℝ) by push_cast; ring,
    Real.cos_nat_mul_two_pi, sub_self, mul_zero]

/-- The terms with `m = j + 1 + i` are at most `2π²(j+1)^{-2}4^{-i}`. -/
theorem gNE_le_geom (i j : ℕ) :
    gNE (i + j + 1) j ≤ notEveryW j * (2 * Real.pi ^ 2) * (1 / 4) ^ i := by
  unfold gNE
  rw [← mul_assoc, two_pow_mul_zpow, show (j : ℤ) - ((i + j + 1 : ℕ) : ℤ) = -((i + 1 : ℕ) : ℤ)
    by push_cast; ring, zpow_neg, zpow_natCast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (notEveryW_nonneg j)
  set x := ((2 : ℝ) ^ (i + 1))⁻¹ * (2 * Real.pi) with hx
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h4 : (1 / 4 : ℝ) ^ i = ((1 / 2 : ℝ) ^ i) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h5 : ((2 : ℝ) ^ (i + 1))⁻¹ = (1 / 2 : ℝ) ^ i * (1 / 2) := by
    rw [pow_succ, mul_inv, one_div, inv_pow]
  have h2 : x ^ 2 / 2 = 2 * Real.pi ^ 2 * (1 / 4) ^ i / 4 := by
    rw [hx, h5, h4]; ring
  have h3 : 0 ≤ 2 * Real.pi ^ 2 * (1 / 4 : ℝ) ^ i := by positivity
  linarith

theorem summable_gNE_j (m : ℕ) : Summable (gNE m) :=
  Summable.of_nonneg_of_le (gNE_nonneg m) (gNE_le m) (summable_notEveryW.mul_left 2)

/-- **The double series `∑ₘ ∑ⱼ` converges.** -/
theorem summable_gNE : Summable fun m : ℕ => ∑' j, gNE m j := by
  have hofr : ∀ m : ℕ, ENNReal.ofReal (∑' j, gNE m j) = ∑' j, ENNReal.ofReal (gNE m j) :=
    fun m => ENNReal.ofReal_tsum_of_nonneg (gNE_nonneg m) (summable_gNE_j m)
  have hfin : ∑' m : ℕ, ENNReal.ofReal (∑' j, gNE m j) ≠ ⊤ := by
    simp_rw [hofr]
    rw [ENNReal.tsum_comm]
    -- for each `j`, the sum over `m` is at most `2π²(j+1)^{-2} · 4/3`
    have hj : ∀ j : ℕ, ∑' m : ℕ, ENNReal.ofReal (gNE m j) ≤
        ENNReal.ofReal (notEveryW j * (2 * Real.pi ^ 2)) * (1 - ENNReal.ofReal (1 / 4))⁻¹ := by
      intro j
      have hsupp : Function.support (fun m : ℕ => ENNReal.ofReal (gNE m j)) ⊆
          range (fun i : ℕ => i + j + 1) := by
        intro m hm
        by_cases h : m ≤ j
        · exact absurd (show ENNReal.ofReal (gNE m j) = 0 by
            rw [gNE_eq_zero h, ENNReal.ofReal_zero]) hm
        · exact ⟨m - j - 1, by simp only; omega⟩
      have hinj : Function.Injective (fun i : ℕ => i + j + 1) := fun a b h => by
        simp only at h; omega
      rw [← hinj.tsum_eq hsupp, ← ENNReal.tsum_geometric, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun i => ?_
      rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by
        have := notEveryW_nonneg j; positivity)]
      exact ENNReal.ofReal_le_ofReal (gNE_le_geom i j)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hj)
    rw [ENNReal.tsum_mul_right]
    refine ENNReal.mul_ne_top ?_ (ENNReal.inv_ne_top.2 ?_)
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by have := notEveryW_nonneg j; positivity)
        (summable_notEveryW.mul_right _)]
      exact ENNReal.ofReal_ne_top
    · rw [Ne, tsub_eq_zero_iff_le, not_le, ← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)
  have := ENNReal.summable_toReal hfin
  refine this.congr fun m => ?_
  exact ENNReal.toReal_ofReal (tsum_nonneg (gNE_nonneg m))

/-- `ϱ̂(2^{-(m+1)}2π e₀) = exp(-∑ⱼ gNE m j)`. -/
theorem charFun_cpLaw_notEveryNu_two_pi (m : ℕ) :
    charFun (cpLaw notEveryNu)
        (((2 : ℝ) ^ (-((m : ℤ) + 1))) • ((2 * Real.pi) • ebasis (0 : Fin 1))) =
      ((Real.exp (-∑' j, gNE m j) : ℝ) : ℂ) := by
  rw [charFun_cpLaw_symm _ notEveryNu_symm, integral_one_sub_cos_notEveryNu, smul_smul,
    ebasis_smul_apply]
  rfl

/-! ## `prop:ladder-not-every-frequency` -/

/-- **`prop:ladder-not-every-frequency`.** On `ℝ¹`, with `ν_ϱ = ∑_{j ≥ 1} j^{-2} ½(δ_{2^j} +
δ_{-2^j})`: its folded measure is `∑ j^{-2} δ_{2^j}`; `∫ log₊|x| ν_ϱ(dx) = ∞`; the compound
Poisson law `ϱ` with this Lévy measure exists; and every such law is carried by `ℤ`, infinitely
divisible, and its partial products `∏_{m=1}^M ϱ̂(2^{-m}ω)` have a positive limit at `ω = 2π`. -/
theorem ladder_not_every_frequency :
    (notEveryNu.map (fun x : Rd 1 => |x 0|)).restrict (Ioi 0) =
        Measure.sum (fun j : ℕ => ENNReal.ofReal (((j : ℝ) + 1) ^ 2)⁻¹ •
          Measure.dirac ((2 : ℝ) ^ (j + 1))) ∧
      ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂notEveryNu = ⊤ ∧
      (∃ ρ : Measure (Rd 1), IsProbabilityMeasure ρ ∧ ∀ ω : Rd 1,
        charFun ρ ω = ((Real.exp (-∫ x, (1 - Real.cos ⟪ω, x⟫) ∂notEveryNu) : ℝ) : ℂ)) ∧
      ∀ ρ : Measure (Rd 1), IsProbabilityMeasure ρ → (∀ ω : Rd 1,
        charFun ρ ω = ((Real.exp (-∫ x, (1 - Real.cos ⟪ω, x⟫) ∂notEveryNu) : ℝ) : ℂ)) →
          ρ {x | ¬ ∃ k : ℤ, x 0 = k} = 0 ∧ IsInfinitelyDivisible ρ ∧
          ∃ L : ℝ, 0 < L ∧ Tendsto (fun M => ladderProd 2 ρ M ((2 * Real.pi) • ebasis (0 : Fin 1)))
            atTop (𝓝 (L : ℂ)) := by
  have hpow0 : ∀ j : ℕ, (0 : ℝ) < 2 ^ (j + 1) := fun j => by positivity
  refine ⟨?_, ?_, ⟨cpLaw notEveryNu, inferInstance, charFun_cpLaw_symm _ notEveryNu_symm⟩,
    fun ρ hρp hρ => ?_⟩
  · -- the folded measure
    have hmeas : Measurable fun x : Rd 1 => |x 0| := by fun_prop
    ext A hA
    rw [Measure.restrict_apply hA, Measure.map_apply hmeas (hA.inter measurableSet_Ioi),
      notEveryNu_apply (hmeas (hA.inter measurableSet_Ioi)), Measure.sum_apply _ hA]
    refine tsum_congr fun j => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
    have h1 : ((fun x : Rd 1 => |x 0|) ⁻¹' (A ∩ Ioi 0)).indicator (1 : Rd 1 → ℝ≥0∞)
        (((2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1)) = A.indicator 1 ((2 : ℝ) ^ (j + 1)) := by
      refine indicator_one_congr ?_
      change |(((2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1) : Rd 1) 0| ∈ A ∩ Ioi 0 ↔ _
      rw [ebasis_smul_apply, abs_of_pos (hpow0 j)]
      exact ⟨fun h => h.1, fun h => ⟨h, hpow0 j⟩⟩
    have h2 : ((fun x : Rd 1 => |x 0|) ⁻¹' (A ∩ Ioi 0)).indicator (1 : Rd 1 → ℝ≥0∞)
        ((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1)) = A.indicator 1 ((2 : ℝ) ^ (j + 1)) := by
      refine indicator_one_congr ?_
      change |((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1) : Rd 1) 0| ∈ A ∩ Ioi 0 ↔ _
      rw [ebasis_smul_apply, abs_neg, abs_of_pos (hpow0 j)]
      exact ⟨fun h => h.1, fun h => ⟨h, hpow0 j⟩⟩
    rw [h1, h2, ← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by have := notEveryW_nonneg j; positivity),
      div_mul_cancel₀ _ two_ne_zero]
    rfl
  · -- the logarithmic moment is infinite
    rw [notEveryNu, lintegral_sum_measure]
    simp_rw [lintegral_smul_measure, lintegral_add_measure, lintegral_dirac]
    by_contra hfin
    have hs := ENNReal.summable_toReal hfin
    have hterm : ∀ j : ℕ, (ENNReal.ofReal ((((j : ℝ) + 1) ^ 2)⁻¹ / 2) •
        (ENNReal.ofReal (Real.posLog ‖((2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1)‖) +
          ENNReal.ofReal
            (Real.posLog ‖((-(2 : ℝ) ^ (j + 1)) • ebasis (0 : Fin 1) : Rd 1)‖))).toReal =
        Real.log 2 * (1 / ((j : ℝ) + 1)) := by
      intro j
      have hlog : Real.posLog (2 ^ (j + 1) : ℝ) = ((j : ℝ) + 1) * Real.log 2 := by
        rw [Real.posLog_eq_log (by rw [abs_of_pos (hpow0 j)]; exact one_le_pow₀ one_le_two),
          Real.log_pow]
        push_cast
        ring
      rw [norm_ebasis_smul, norm_ebasis_smul, abs_neg, abs_of_pos (hpow0 j), hlog, smul_eq_mul,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]
      field_simp
      ring
    have hs' : Summable fun j : ℕ => 1 / ((j : ℝ) + 1) := by
      have := (hs.congr hterm).mul_left (Real.log 2)⁻¹
      refine this.congr fun j => ?_
      rw [← mul_assoc, inv_mul_cancel₀ (Real.log_pos one_lt_two).ne', one_mul]
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 (by
      refine hs'.congr fun j => ?_
      push_cast
      ring_nf))
  · -- every such law is the compound Poisson law
    have hρeq : ρ = cpLaw notEveryNu :=
      Measure.ext_of_charFun (funext fun ω => by rw [hρ, charFun_cpLaw_symm _ notEveryNu_symm])
    refine ⟨?_, ?_, ?_⟩
    · rw [hρeq]
      exact cpLaw_intPts_null _ notEveryNu_intPts_null
    · intro n hn
      have hn' : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne')
      haveI : IsFiniteMeasure ((n : ℝ≥0∞)⁻¹ • notEveryNu) := ⟨by
        rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top hn'.lt_top (measure_lt_top _ _)⟩
      have hsym : ((n : ℝ≥0∞)⁻¹ • notEveryNu).map (fun x => -x) = (n : ℝ≥0∞)⁻¹ • notEveryNu := by
        rw [Measure.map_smul, notEveryNu_symm]
      refine ⟨cpLaw ((n : ℝ≥0∞)⁻¹ • notEveryNu), inferInstance, ?_⟩
      haveI := ScaleSpace.isFiniteMeasure_convPow_Rd (cpLaw ((n : ℝ≥0∞)⁻¹ • notEveryNu)) n
      rw [hρeq]
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      rw [AffineHemigroup.charFun_convPow, charFun_cpLaw_symm _ hsym,
        charFun_cpLaw_symm _ notEveryNu_symm, integral_smul_measure, ← Complex.ofReal_pow,
        ← Real.exp_nat_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
      congr 2
      field_simp
    · -- the partial products
      refine ⟨Real.exp (-∑' m, ∑' j, gNE m j), Real.exp_pos _, ?_⟩
      have hprod : ∀ M : ℕ, ladderProd 2 ρ M ((2 * Real.pi) • ebasis (0 : Fin 1)) =
          ((Real.exp (-∑ m ∈ Finset.range M, ∑' j, gNE m j) : ℝ) : ℂ) := by
        intro M
        rw [ladderProd, hρeq]
        simp_rw [charFun_cpLaw_notEveryNu_two_pi]
        rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.sum_neg_distrib]
      simp_rw [hprod]
      have h1 := summable_gNE.hasSum.tendsto_sum_nat
      exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).tendsto
        _).comp h1

end Pyramids
