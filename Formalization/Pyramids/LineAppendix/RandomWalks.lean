/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.KnotCascades
import Pyramids.LineAppendix.QCinLimit
import Pyramids.LineAppendix.ClassicalWeights
import ScaleSpaceCore.L1Continuity

/-!
# `prop:extreme-rays-random-walks`: the `q`-Cin rays as cascades of random walks

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:extreme-rays-random-walks`. Wave 3c: the six
declarations `extreme_rays_random_walks_1` to `_5` and `_5_finite` moved here from
`PyramidsSkeleton.ChA1Line`, unchanged in statement and name.

## The route

* **Lattices.** A convolution of measures carried by a set closed under addition is carried by it
  (`conv_compl_null`), so `exp[cδ²_v]`, a mixture of convolution powers of `½(δ_v + δ_{-v})`, is
  carried by `vℤ` (`randomWalkLaw_lattice_null`), and so is a convolution of a list of laws
  carried by `vℤ` (`convList_compl_null`). The probability and the transform of `exp[cδ²_v]` are
  wave 3a's (`isProbabilityMeasure_randomWalkLaw`, `charFun_randomWalkLaw`).
* **Lévy's continuity theorem, the existence clause** (`exists_law_of_tendsto_charFun`): if the
  transforms of a sequence of laws converge pointwise to a function continuous at `0`, the limit is
  the transform of a law. Mathlib gives the tightness (`isTightMeasureSet_of_tendsto_charFun`) and
  Prokhorov's theorem; the limit of a convergent subsequence has the limit transform. The
  convergence clause is the shared core's `levy_continuity`.
* **(2).** The transform of `K_N` is the product of the transforms; the remainder of the series is
  bounded by the geometric tail. **(4)** reads `prop:strata-cylinder-coordinates-q-cin`(2)
  (`qcin_2`) and is taken along sequences, the filter `q ↓ 1` being countably generated.
  **(5)** sums the series of the cascade over the knots `θqⁿ ≤ t` (those with `n ≤ ⌊log_q(t/θ)⌋`),
  and for finitely many atoms computes (A.e2) of the mixture atom by atom.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (convPow cin)
open scoped Topology ENNReal NNReal BoundedContinuousFunction

/-! ## Lattices -/

/-- The lattice `vℤ`. -/
def lattice (v : ℝ) : Set ℝ := {x | ∃ n : ℤ, x = v * n}

theorem lattice_eq_range (v : ℝ) : lattice v = range fun n : ℤ => v * n := by
  ext x
  simp only [lattice, mem_setOf_eq, mem_range, eq_comm]

theorem measurableSet_lattice (v : ℝ) : MeasurableSet (lattice v) := by
  rw [lattice_eq_range]
  exact (countable_range _).measurableSet

theorem compl_lattice (v : ℝ) : (lattice v)ᶜ = {x | ¬ ∃ n : ℤ, x = v * n} := rfl

theorem zero_mem_lattice (v : ℝ) : (0 : ℝ) ∈ lattice v := ⟨0, by simp⟩

theorem add_mem_lattice {v x y : ℝ} (hx : x ∈ lattice v) (hy : y ∈ lattice v) :
    x + y ∈ lattice v := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  exact ⟨m + n, by push_cast; ring⟩

/-- `v'ℤ ⊆ vℤ` when `v' = vk`, `k ∈ ℤ`. -/
theorem lattice_subset {v v' : ℝ} (k : ℤ) (h : v' = v * k) : lattice v' ⊆ lattice v := by
  rintro x ⟨n, rfl⟩
  exact ⟨k * n, by rw [h]; push_cast; ring⟩

/-- A convolution of two measures carried by a set closed under addition is carried by it. -/
theorem conv_compl_null {S : Set ℝ} (hS : MeasurableSet S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0) : (μ ∗ ν) Sᶜ = 0 := by
  rw [Measure.conv, Measure.map_apply measurable_add hS.compl]
  refine measure_mono_null (t := (Sᶜ ×ˢ univ) ∪ (univ ×ˢ Sᶜ)) (fun p hp => ?_)
    (measure_union_null ?_ ?_)
  · by_contra hc
    simp only [mem_union, mem_prod, mem_compl_iff, mem_univ, and_true, true_and, not_or,
      not_not] at hc
    exact hp (hadd _ hc.1 _ hc.2)
  · rw [Measure.prod_prod, hμ, zero_mul]
  · rw [Measure.prod_prod, hν, mul_zero]

theorem dirac_zero_compl_null {S : Set ℝ} (hS : MeasurableSet S) (h0 : (0 : ℝ) ∈ S) :
    Measure.dirac (0 : ℝ) Sᶜ = 0 := by
  rw [Measure.dirac_apply' _ hS.compl, indicator_of_notMem (not_not.2 h0)]

/-- `½(δ_v + δ_{-v})` is carried by `vℤ`. -/
theorem symStep_lattice_null (v : ℝ) : symStep v (lattice v)ᶜ = 0 := by
  have hv : v ∈ lattice v := ⟨1, by simp⟩
  have hv' : -v ∈ lattice v := ⟨-1, by simp⟩
  rw [symStep, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply' _ (measurableSet_lattice v).compl,
    Measure.dirac_apply' _ (measurableSet_lattice v).compl,
    indicator_of_notMem (not_not.2 hv), indicator_of_notMem (not_not.2 hv')]
  simp

/-- **`exp[cδ²_v]` is carried by `vℤ`.** -/
theorem randomWalkLaw_lattice_null (c v : ℝ) : randomWalkLaw c v (lattice v)ᶜ = 0 := by
  have hS := measurableSet_lattice v
  have hpow : ∀ n : ℕ, convPow (symStep v) n (lattice v)ᶜ = 0 := by
    intro n
    induction n with
    | zero => exact dirac_zero_compl_null hS (zero_mem_lattice v)
    | succ n ih =>
      haveI := ScaleSpace.isProbabilityMeasure_convPow_real (symStep v) n
      rw [convPow]
      exact conv_compl_null hS (fun x hx y hy => add_mem_lattice hx hy) ih
        (symStep_lattice_null v)
  rw [randomWalkLaw, Measure.sum_apply _ hS.compl, ENNReal.tsum_eq_zero]
  intro n
  rw [Measure.smul_apply, hpow n, smul_zero]

/-- A convolution of a list of laws carried by a set closed under addition is carried by it. -/
theorem convList_compl_null {S : Set ℝ} (hS : MeasurableSet S) (h0 : (0 : ℝ) ∈ S)
    (hadd : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (l : List (Measure ℝ))
    (hp : ∀ μ ∈ l, IsProbabilityMeasure μ) (h : ∀ μ ∈ l, μ Sᶜ = 0) : convList l Sᶜ = 0 := by
  induction l with
  | nil => exact dirac_zero_compl_null hS h0
  | cons μ l ih =>
    haveI := (convList_charFun_real l fun ν hν => hp ν (List.mem_cons_of_mem _ hν)).1
    haveI := hp μ List.mem_cons_self
    rw [convList]
    exact conv_compl_null hS hadd (h μ List.mem_cons_self)
      (ih (fun ν hν => hp ν (List.mem_cons_of_mem _ hν))
        fun ν hν => h ν (List.mem_cons_of_mem _ hν))

/-! ## `prop:extreme-rays-random-walks`(1) -/

/-- **`prop:extreme-rays-random-walks`(1).** `exp[cδ²_v]` is a probability law carried by `vℤ`
with transform `e^{-c(1 - cos vω)}`. -/
theorem extreme_rays_random_walks_1 {c v : ℝ} (hc : 0 < c) :
    IsProbabilityMeasure (randomWalkLaw c v) ∧
      randomWalkLaw c v {x | ¬ ∃ n : ℤ, x = v * n} = 0 ∧
      ∀ ω : ℝ, charFun (randomWalkLaw c v) ω =
        ((Real.exp (-(c * (1 - Real.cos (v * ω)))) : ℝ) : ℂ) :=
  ⟨isProbabilityMeasure_randomWalkLaw hc.le v, randomWalkLaw_lattice_null c v,
    charFun_randomWalkLaw hc.le v⟩

/-! ## `prop:extreme-rays-random-walks`(3) -/

/-- **`prop:extreme-rays-random-walks`(3).** For an integer `q ≥ 2`, `K_N` is carried by the lattice
`τq^{-N}ℤ`, and its `i`-th factor by `τq^{-i}ℤ`. -/
theorem extreme_rays_random_walks_3 {q : ℕ} (hq : 2 ≤ q) {τ : ℝ} (N : ℕ) :
    qCinTruncation q τ N {x | ¬ ∃ n : ℤ, x = τ / (q : ℝ) ^ N * n} = 0 ∧
      ∀ i : ℕ, i ≤ N →
        randomWalkLaw (Real.log q) (τ / (q : ℝ) ^ i)
          {x | ¬ ∃ n : ℤ, x = τ / (q : ℝ) ^ i * n} = 0 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hl : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  refine ⟨?_, fun i _ => randomWalkLaw_lattice_null _ _⟩
  rw [← compl_lattice, qCinTruncation]
  refine convList_compl_null (measurableSet_lattice _) (zero_mem_lattice _)
    (fun x hx y hy => add_mem_lattice hx hy) _ ?_ ?_
  · intro μ hμ
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hμ
    exact isProbabilityMeasure_randomWalkLaw hl _
  · intro μ hμ
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hμ
    have hiN : i ≤ N := Nat.lt_succ_iff.1 (List.mem_range.1 hi)
    refine measure_mono_null (compl_subset_compl.2 (lattice_subset ((q : ℤ) ^ (N - i)) ?_))
      (randomWalkLaw_lattice_null _ _)
    push_cast
    have hN : (q : ℝ) ^ N = (q : ℝ) ^ i * (q : ℝ) ^ (N - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hiN]
    have hqi : (q : ℝ) ^ (N - i) ≠ 0 := (pow_pos hq0 _).ne'
    rw [hN, div_mul_eq_mul_div, mul_comm ((q : ℝ) ^ i), ← div_div, mul_div_cancel_right₀ _ hqi]

/-! ## Lévy's continuity theorem, the existence clause -/

/-- **Lévy's continuity theorem, existence.** If the transforms of a sequence of laws on `ℝ`
converge pointwise to a function `f` continuous at `0`, then `f` is the transform of a law. -/
theorem exists_law_of_tendsto_charFun {μ : ℕ → Measure ℝ} [hμ : ∀ n, IsProbabilityMeasure (μ n)]
    {f : ℝ → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ ω, Tendsto (fun n => charFun (μ n) ω) atTop (𝓝 (f ω))) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ ω, charFun ν ω = f ω := by
  set P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨μ n, hμ n⟩ with hP
  have hsetEq : {ν : Measure ℝ | ∃ Q ∈ Set.range P, (Q : Measure ℝ) = ν} = Set.range μ := by
    ext ν
    constructor
    · rintro ⟨-, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  have hset : IsTightMeasureSet {ν : Measure ℝ | ∃ Q ∈ Set.range P, (Q : Measure ℝ) = ν} := by
    rw [hsetEq]
    exact isTightMeasureSet_of_tendsto_charFun hf h
  have hcompact : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet hset
  obtain ⟨Q, -, φ, hφ, hQ⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨(Q : Measure ℝ), Q.2, fun ω => ?_⟩
  have h1 := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hQ) ω
  exact tendsto_nhds_unique h1 ((h ω).comp hφ.tendsto_atTop)

/-! ## Products of exponentials -/

theorem list_prod_range_ofReal_exp (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map fun i => ((Real.exp (f i) : ℝ) : ℂ)).prod =
      ((Real.exp (∑ i ∈ Finset.range n, f i) : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.sum_range_succ,
      Real.exp_add, Complex.ofReal_mul]
    simp

theorem finset_prod_ofReal_exp {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, ((Real.exp (f i) : ℝ) : ℂ) = ((Real.exp (∑ i ∈ s, f i) : ℝ) : ℂ) := by
  rw [Real.exp_sum, Complex.ofReal_prod]

/-- `ofReal ∘ exp ∘ neg` along a convergent sequence of reals. -/
theorem tendsto_ofReal_exp_neg {α : Type*} {l : Filter α} {g : α → ℝ} {x : ℝ}
    (h : Tendsto g l (𝓝 x)) :
    Tendsto (fun a => ((Real.exp (-g a) : ℝ) : ℂ)) l (𝓝 ((Real.exp (-x) : ℝ) : ℂ)) :=
  (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp continuous_neg)).continuousAt.tendsto.comp h

/-! ## `prop:extreme-rays-random-walks`(2) -/

section Two

variable {q τ : ℝ}

theorem isProbabilityMeasure_qCinTruncation (hq : 1 < q) (N : ℕ) :
    IsProbabilityMeasure (qCinTruncation q τ N) := by
  refine (convList_charFun_real _ fun μ hμ => ?_).1
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hμ
  exact isProbabilityMeasure_randomWalkLaw (Real.log_nonneg hq.le) _

theorem charFun_qCinTruncation (hq : 1 < q) (N : ℕ) (ω : ℝ) :
    charFun (qCinTruncation q τ N) ω = ((Real.exp (-(Real.log q *
      ∑ i ∈ Finset.range (N + 1), (1 - Real.cos (ω * (τ / q ^ i))))) : ℝ) : ℂ) := by
  have hl : 0 ≤ Real.log q := Real.log_nonneg hq.le
  rw [qCinTruncation, (convList_charFun_real _ fun μ hμ => ?_).2 ω, List.map_map]
  · have e : ((fun μ => charFun μ ω) ∘ fun i : ℕ => randomWalkLaw (Real.log q) (τ / q ^ i)) =
        fun i => ((Real.exp (-(Real.log q * (1 - Real.cos (ω * (τ / q ^ i))))) : ℝ) : ℂ) := by
      funext i
      simp only [Function.comp_apply, charFun_randomWalkLaw hl, mul_comm (τ / q ^ i) ω]
    rw [e, list_prod_range_ofReal_exp, Finset.mul_sum, ← Finset.sum_neg_distrib]
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hμ
    exact isProbabilityMeasure_randomWalkLaw hl _

/-- The remainder of the series: `0 ≤ E − ∑_{i ≤ N} ≤ τ²ω²q^{-2N}/(2(q² − 1))`. -/
theorem qCinRay_sub_partial (hq : 1 < q) (N : ℕ) (ω : ℝ) :
    0 ≤ qCinRay q τ ω - ∑ i ∈ Finset.range (N + 1), (1 - Real.cos (ω * (τ / q ^ i))) ∧
      qCinRay q τ ω - ∑ i ∈ Finset.range (N + 1), (1 - Real.cos (ω * (τ / q ^ i))) ≤
        τ ^ 2 * ω ^ 2 / q ^ (2 * N) / (2 * (q ^ 2 - 1)) := by
  have hq0 : 0 < q := by linarith
  set a : ℕ → ℝ := fun i => 1 - Real.cos (ω * (τ / q ^ i)) with ha
  have hsum := qCinRay_summable hq τ ω
  have hnn : ∀ i, 0 ≤ a i := fun i => sub_nonneg.2 (Real.cos_le_one _)
  have hsplit : qCinRay q τ ω - ∑ i ∈ Finset.range (N + 1), a i = ∑' i, a (i + (N + 1)) := by
    rw [qCinRay, ← hsum.sum_add_tsum_nat_add (N + 1)]
    ring
  rw [hsplit]
  set r : ℝ := (q ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
  have hbound : ∀ i, a (i + (N + 1)) ≤ (ω * τ) ^ 2 / 2 * r ^ (N + 1) * r ^ i := by
    intro i
    have h := Real.one_sub_sq_div_two_le_cos (x := ω * (τ / q ^ (i + (N + 1))))
    have e : (ω * (τ / q ^ (i + (N + 1)))) ^ 2 = (ω * τ) ^ 2 * (r ^ (N + 1) * r ^ i) := by
      rw [hr, inv_pow, inv_pow, ← pow_mul, ← pow_mul]
      field_simp
      ring
    rw [e] at h
    simp only [ha]
    nlinarith
  have hgeo := (summable_geometric_of_lt_one hr0 hr1).mul_left ((ω * τ) ^ 2 / 2 * r ^ (N + 1))
  refine ⟨tsum_nonneg fun i => hnn _, ?_⟩
  refine (Summable.tsum_le_tsum hbound ((summable_nat_add_iff (N + 1)).2 hsum) hgeo).trans
    (le_of_eq ?_)
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, hr, inv_pow, ← pow_mul]
  have hq2 : q ^ 2 - 1 ≠ 0 := by nlinarith
  have hqne : q ≠ 0 := hq0.ne'
  have e : q ^ (2 * (N + 1)) = q ^ (2 * N) * q ^ 2 := by rw [← pow_add]; ring_nf
  rw [e]
  field_simp

/-- `ω ↦ ℓE^{(q)}_τ(ω)` tends to `0` at `0`. -/
theorem tendsto_qCinRay_zero (hq : 1 < q) :
    Tendsto (fun ω => Real.log q * qCinRay q τ ω) (𝓝 0) (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hq2 : 0 < q ^ 2 - 1 := by nlinarith
  have hl : 0 ≤ Real.log q := Real.log_nonneg hq.le
  have hup : ∀ ω, Real.log q * qCinRay q τ ω ≤
      Real.log q * (τ ^ 2 * ω ^ 2 / 2 + τ ^ 2 * ω ^ 2 / (2 * (q ^ 2 - 1))) := by
    intro ω
    obtain ⟨-, h2⟩ := qCinRay_sub_partial (τ := τ) hq 0 ω
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, div_one,
      mul_zero] at h2
    have h3 := Real.one_sub_sq_div_two_le_cos (x := ω * τ)
    refine mul_le_mul_of_nonneg_left ?_ hl
    nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun ω => mul_nonneg hl (qCinRay_nonneg q τ ω)) hup
  have : Tendsto (fun ω : ℝ => Real.log q * (τ ^ 2 * ω ^ 2 / 2 +
      τ ^ 2 * ω ^ 2 / (2 * (q ^ 2 - 1)))) (𝓝 0)
      (𝓝 (Real.log q * (τ ^ 2 * 0 ^ 2 / 2 + τ ^ 2 * 0 ^ 2 / (2 * (q ^ 2 - 1))))) :=
    ((continuous_const.mul ((continuous_const.mul (continuous_pow 2)).div_const _ |>.add
      ((continuous_const.mul (continuous_pow 2)).div_const _)))).tendsto 0
  simpa using this

theorem tendsto_charFun_qCinTruncation (hq : 1 < q) (ω : ℝ) :
    Tendsto (fun N : ℕ => charFun (qCinTruncation q τ N) ω) atTop
      (𝓝 ((Real.exp (-(Real.log q * qCinRay q τ ω)) : ℝ) : ℂ)) := by
  simp_rw [charFun_qCinTruncation hq]
  refine tendsto_ofReal_exp_neg (Tendsto.const_mul _ ?_)
  exact ((qCinRay_summable hq τ ω).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

/-- **`prop:extreme-rays-random-walks`(2).** `K_N` has the exponent `ℓ∑_{i ≤ N} (1 - cos ωτq^{-i})`,
which differs from `ℓE^{(q)}_τ` by at most `ℓτ²ω²q^{-2N}/(2(q² - 1))`; the law `K^{(q)}_τ` with
transform `exp[-ℓE^{(q)}_τ]` exists and is the weak limit of `K_N`.

The hypothesis `0 < τ` is not used: every clause holds for every real `τ`. -/
theorem extreme_rays_random_walks_2 (hq : 1 < q) :
    (∀ (N : ℕ) (ω : ℝ), charFun (qCinTruncation q τ N) ω = ((Real.exp (-(Real.log q *
        ∑ i ∈ Finset.range (N + 1), (1 - Real.cos (ω * (τ / q ^ i))))) : ℝ) : ℂ)) ∧
      (∀ (N : ℕ) (ω : ℝ), |Real.log q * qCinRay q τ ω -
          Real.log q * ∑ i ∈ Finset.range (N + 1), (1 - Real.cos (ω * (τ / q ^ i)))| ≤
        Real.log q * τ ^ 2 * ω ^ 2 / q ^ (2 * N) / (2 * (q ^ 2 - 1))) ∧
      (∃ K : Measure ℝ, IsProbabilityMeasure K ∧ ∀ ω : ℝ,
        charFun K ω = ((Real.exp (-(Real.log q * qCinRay q τ ω)) : ℝ) : ℂ)) ∧
      ∀ K : Measure ℝ, IsProbabilityMeasure K →
        (∀ ω : ℝ, charFun K ω = ((Real.exp (-(Real.log q * qCinRay q τ ω)) : ℝ) : ℂ)) →
        ∀ φ : ℝ →ᵇ ℝ, Tendsto (fun N : ℕ => ∫ x, φ x ∂(qCinTruncation q τ N)) atTop
          (𝓝 (∫ x, φ x ∂K)) := by
  have hl : 0 ≤ Real.log q := Real.log_nonneg hq.le
  haveI := fun N => isProbabilityMeasure_qCinTruncation (τ := τ) hq N
  refine ⟨charFun_qCinTruncation hq, fun N ω => ?_, ?_, fun K hK hKc => ?_⟩
  · obtain ⟨h1, h2⟩ := qCinRay_sub_partial (τ := τ) hq N ω
    rw [← mul_sub, abs_of_nonneg (mul_nonneg hl h1)]
    calc Real.log q * (qCinRay q τ ω - ∑ i ∈ Finset.range (N + 1), (1 - Real.cos (ω * (τ / q ^ i))))
        ≤ Real.log q * (τ ^ 2 * ω ^ 2 / q ^ (2 * N) / (2 * (q ^ 2 - 1))) :=
          mul_le_mul_of_nonneg_left h2 hl
      _ = _ := by ring
  · refine exists_law_of_tendsto_charFun (μ := fun N => qCinTruncation q τ N) ?_
      (tendsto_charFun_qCinTruncation hq)
    have h0 : qCinRay q τ 0 = 0 := by simp [qCinRay]
    have := tendsto_ofReal_exp_neg (tendsto_qCinRay_zero (τ := τ) hq)
    rw [ContinuousAt, h0, mul_zero]
    exact this
  · haveI := hK
    refine ScaleSpace.levy_continuity fun ω => ?_
    rw [hKc]
    exact tendsto_charFun_qCinTruncation hq ω

end Two


/-! ## `prop:extreme-rays-random-walks`(4) -/

/-- `qℓ²/(2(q - 1)) → 0` as `q ↓ 1`: `0 ≤ ℓ ≤ q - 1`. -/
theorem tendsto_qcin_coeff :
    Tendsto (fun q : ℝ => q * Real.log q ^ 2 / (2 * (q - 1))) (𝓝[>] 1) (𝓝 0) := by
  have hup : Tendsto (fun q : ℝ => q * (q - 1) / 2) (𝓝[>] 1) (𝓝 0) := by
    have h := (by fun_prop : Continuous fun q : ℝ => q * (q - 1) / 2).tendsto (1 : ℝ)
    simp only [sub_self, mul_zero, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : (1 : ℝ) < q := hq
    have : 0 < q - 1 := by linarith
    positivity
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : (1 : ℝ) < q := hq
    have h1 : 0 < q - 1 := by linarith
    have hl0 : 0 ≤ Real.log q := Real.log_nonneg hq'.le
    have hl1 : Real.log q ≤ q - 1 := by
      have := Real.add_one_le_exp (Real.log q)
      rw [Real.exp_log (by linarith)] at this
      linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    have : Real.log q ^ 2 ≤ (q - 1) ^ 2 := pow_le_pow_left₀ hl0 hl1 2
    nlinarith

/-- **`ℓE^{(q)}_τ → Cin(τ ·)` pointwise as `q ↓ 1`**, from `qcin_2`. -/
theorem tendsto_logq_qCinRay (τ ω : ℝ) :
    Tendsto (fun q => Real.log q * qCinRay q τ ω) (𝓝[>] 1) (𝓝 (cin (τ * ω))) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have h0 : Tendsto (fun q : ℝ => q * Real.log q ^ 2 / (2 * (q - 1)) * |τ * ω|) (𝓝[>] 1)
      (𝓝 0) := by
    simpa using tendsto_qcin_coeff.mul_const |τ * ω|
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [Real.norm_eq_abs]
  exact qcin_2 hq τ ω

/-- **`prop:extreme-rays-random-walks`(4).** As `q ↓ 1` through real values, `K^{(q)}_τ` converges
weakly to the Cin kernel of step `τ`, the law with exponent `Cin(τω)`.

The hypothesis `0 < τ` is not used: the statement holds for every real `τ`. -/
theorem extreme_rays_random_walks_4 {τ : ℝ} :
    (∃ K₀ : Measure ℝ, IsProbabilityMeasure K₀ ∧ ∀ ω : ℝ,
        charFun K₀ ω = ((Real.exp (-cin (τ * ω)) : ℝ) : ℂ)) ∧
      ∀ K : ℝ → Measure ℝ, (∀ q : ℝ, 1 < q → IsProbabilityMeasure (K q) ∧ ∀ ω : ℝ,
          charFun (K q) ω = ((Real.exp (-(Real.log q * qCinRay q τ ω)) : ℝ) : ℂ)) →
        ∀ K₀ : Measure ℝ, IsProbabilityMeasure K₀ →
          (∀ ω : ℝ, charFun K₀ ω = ((Real.exp (-cin (τ * ω)) : ℝ) : ℂ)) →
          ∀ φ : ℝ →ᵇ ℝ, Tendsto (fun q => ∫ x, φ x ∂(K q)) (𝓝[>] 1) (𝓝 (∫ x, φ x ∂K₀)) := by
  refine ⟨?_, fun K hK K₀ hK₀ hK₀c φ => ?_⟩
  · set qs : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1) with hqs_def
    have hqs : ∀ n, 1 < qs n := fun n => by
      simp only [hqs_def]
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hqs_t : Tendsto qs atTop (𝓝[>] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hqs⟩
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
      simpa only [add_zero] using this
    choose K hK hKc using fun n => (extreme_rays_random_walks_2 (τ := τ) (hqs n)).2.2.1
    refine exists_law_of_tendsto_charFun (μ := K) (hμ := hK) ?_ fun ω => ?_
    · exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (ScaleSpace.continuous_cin.comp (continuous_const.mul continuous_id)).neg)).continuousAt
    · simp_rw [hKc]
      exact tendsto_ofReal_exp_neg ((tendsto_logq_qCinRay τ ω).comp hqs_t)
  · rw [tendsto_iff_seq_tendsto]
    intro x hx
    have hev : ∀ᶠ n in atTop, 1 < x n := hx.eventually self_mem_nhdsWithin
    let μ : ℕ → Measure ℝ := fun n => if 1 < x n then K (x n) else K₀
    have hμ : ∀ n, IsProbabilityMeasure (μ n) := by
      intro n
      by_cases h : 1 < x n
      · simp only [μ, if_pos h]
        exact (hK _ h).1
      · simp only [μ, if_neg h]
        exact hK₀
    have hch : ∀ ω, Tendsto (fun n => charFun (μ n) ω) atTop (𝓝 (charFun K₀ ω)) := by
      intro ω
      rw [hK₀c]
      refine (tendsto_ofReal_exp_neg ((tendsto_logq_qCinRay τ ω).comp hx)).congr' ?_
      filter_upwards [hev] with n hn
      simp only [μ, if_pos hn, Function.comp_apply]
      exact ((hK _ hn).2 ω).symm
    refine (ScaleSpace.levy_continuity (μ := μ) (hμ := hμ) (hμ₀ := hK₀) hch φ).congr' ?_
    filter_upwards [hev] with n hn
    simp only [μ, if_pos hn, Function.comp_apply]

/-! ## `prop:extreme-rays-random-walks`(5) -/

/-- The knots below `t`: `θqⁿ ≤ t` iff `n ≤ ⌊log_q(t/θ)⌋`. -/
theorem mul_zpow_le_iff {q : ℝ} (hq : 1 < q) {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t) (n : ℤ) :
    θ * q ^ n ≤ t ↔ n ≤ dgLevel q (t / θ) := by
  obtain ⟨h1, h2⟩ := dgLevel_spec hq (div_pos ht hθ)
  rw [← le_div_iff₀' hθ]
  constructor
  · intro h
    by_contra hn
    have hn' := not_le.1 hn
    have : q ^ (dgLevel q (t / θ) + 1) ≤ q ^ n := zpow_le_zpow_right₀ hq.le (by omega)
    linarith
  · intro hn
    exact (zpow_le_zpow_right₀ hq.le hn).trans h1

/-- A sum over a flattened list is the sum of the sums. -/
theorem sum_map_flatMap {ι : Type*} (l : List ι) (f : ι → List (ℝ × ℝ)) (h : ℝ × ℝ → ℝ) :
    ((l.flatMap f).map h).sum = (l.map fun i => ((f i).map h).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- **A finite convolution of laws `exp[cδ²_v]`**: a probability law whose exponent is the sum of
the exponents. -/
theorem randomWalk_list {l : List (ℝ × ℝ)} (hc : ∀ p ∈ l, 0 ≤ p.1) :
    IsProbabilityMeasure (convList (l.map fun p => randomWalkLaw p.1 p.2)) ∧ ∀ ω,
      charFun (convList (l.map fun p => randomWalkLaw p.1 p.2)) ω =
        ((Real.exp (-((l.map fun p => p.1 * (1 - Real.cos (ω * p.2))).sum)) : ℝ) : ℂ) := by
  induction l with
  | nil =>
    refine ⟨by rw [List.map_nil, convList]; infer_instance, fun ω => ?_⟩
    rw [List.map_nil, convList, charFun_dirac]
    simp
  | cons p l ih =>
    obtain ⟨h1, h2⟩ := ih fun x hx => hc x (List.mem_cons_of_mem _ hx)
    haveI := h1
    haveI := isProbabilityMeasure_randomWalkLaw (hc p List.mem_cons_self) p.2
    refine ⟨by rw [List.map_cons, convList]; infer_instance, fun ω => ?_⟩
    rw [List.map_cons, convList, charFun_conv, h2, charFun_randomWalkLaw (hc p List.mem_cons_self),
      List.map_cons, List.sum_cons, neg_add, Real.exp_add, Complex.ofReal_mul, mul_comm p.2 ω]

/-- **`prop:extreme-rays-random-walks`(5), the knot-atom cascade.** The kernel at scale `t` of the
cascade (A.e4) is the convolution of the laws `exp[δ²_{rθqⁿ}]` over the knots `θqⁿ ≤ t`: the weak
limit of the finite convolutions over the knots with `-N ≤ n`. -/
theorem extreme_rays_random_walks_5 {q : ℝ} (hq : 1 < q) (θ r : ℝ) (hθr : (θ, r) ∈ cylinder q)
    {t : ℝ} (ht : 0 < t) (K : Measure ℝ) [IsProbabilityMeasure K]
    (hK : ∀ ω : ℝ, charFun K ω = ((Real.exp (-knotAtomCascade q θ r t ω) : ℝ) : ℂ)) :
    ∀ φ : ℝ →ᵇ ℝ, Tendsto (fun N : ℕ => ∫ x, φ x ∂(convList
        (((Finset.Icc (-(N : ℤ)) (dgLevel q (t / θ))).toList).map
          fun n => randomWalkLaw 1 (r * θ * q ^ n)))) atTop (𝓝 (∫ x, φ x ∂K)) := by
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθr.1.1
  set L := dgLevel q (t / θ) with hL
  have hlist : ∀ N : ℕ, ((Finset.Icc (-(N : ℤ)) L).toList.map
      fun n => randomWalkLaw 1 (r * θ * q ^ n)) =
      ((Finset.Icc (-(N : ℤ)) L).toList.map fun n => ((1 : ℝ), r * θ * q ^ n)).map
        fun p => randomWalkLaw p.1 p.2 := by
    intro N
    rw [List.map_map]
    rfl
  have hone : ∀ N : ℕ, ∀ p ∈ ((Finset.Icc (-(N : ℤ)) L).toList.map
      fun n => ((1 : ℝ), r * θ * q ^ n)), 0 ≤ p.1 := by
    intro N p hp
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hp
    exact zero_le_one
  have hμ : ∀ N : ℕ, IsProbabilityMeasure (convList ((Finset.Icc (-(N : ℤ)) L).toList.map
      fun n => randomWalkLaw 1 (r * θ * q ^ n))) := fun N => by
    rw [hlist]
    exact (randomWalk_list (hone N)).1
  have hch : ∀ (N : ℕ) (ω : ℝ), charFun (convList ((Finset.Icc (-(N : ℤ)) L).toList.map
      fun n => randomWalkLaw 1 (r * θ * q ^ n))) ω = ((Real.exp (-∑ n ∈ Finset.Icc (-(N : ℤ)) L,
        (1 - Real.cos (ω * (r * θ * q ^ n)))) : ℝ) : ℂ) := by
    intro N ω
    rw [hlist, (randomWalk_list (hone N)).2, List.map_map, Finset.sum_map_toList]
    simp only [Function.comp_apply, one_mul]
  intro φ
  refine ScaleSpace.levy_continuity (hμ := hμ) (fun ω => ?_) φ
  simp_rw [hch, hK]
  refine tendsto_ofReal_exp_neg ?_
  set F : ℤ → ℝ := fun n => if θ * q ^ n ≤ t then 1 - Real.cos (ω * (r * θ * q ^ n)) else 0
    with hF_def
  have hF : HasSum F (knotAtomCascade q θ r t ω) := (knot_summable hq hθr t ω).hasSum
  have htend : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) fun n => ⟨n.natAbs, ?_⟩
    · exact Finset.Icc_subset_Icc (by omega) (by omega)
    · rw [Finset.mem_Icc]
      omega
  have h1 : Tendsto (fun s : Finset ℤ => ∑ b ∈ s, F b) atTop (𝓝 (knotAtomCascade q θ r t ω)) :=
    hF
  refine (h1.comp htend).congr' ?_
  filter_upwards [eventually_ge_atTop L.toNat] with N hN
  have hLN : L ≤ (N : ℤ) := by omega
  simp only [Function.comp_apply]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hLN) fun n hn hnot => ?_]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [hF_def]
    simp only
    rw [if_pos ((mul_zpow_le_iff hq hθ0 ht n).2 (Finset.mem_Icc.1 hn).2)]
  · rw [hF_def]
    simp only
    rw [if_neg]
    intro h
    exact hnot (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hn).1, (mul_zpow_le_iff hq hθ0 ht n).1 h⟩)

/-! ## `prop:extreme-rays-random-walks`(5), finitely many atoms -/

theorem orbitMixture_sum {ι : Type*} [Countable ι] (q : ℝ) (μ : ι → Measure (ℝ × ℝ)) :
    orbitMixture q (Measure.sum μ) = Measure.sum fun i => orbitMixture q (μ i) := by
  ext s hs
  rw [orbitMixture_apply q _ hs, Measure.sum_apply _ hs]
  simp_rw [orbitMixture_apply q _ hs, Measure.sum_apply _ (measurable_orbitPt q _ hs)]
  exact ENNReal.tsum_comm

/-- The slab integral of an orbit: `∫_{(0,t] × (0,∞)} (1 - cos ωv) dΛ^{(θ,r)}` is the cascade. -/
theorem lintegral_knotAtomOrbit_slab {q : ℝ} (hq : 1 < q) {θ r : ℝ} (hθr : (θ, r) ∈ cylinder q)
    (t ω : ℝ) :
    ∫⁻ p in Ioc 0 t ×ˢ Ioi 0, ENNReal.ofReal (1 - Real.cos (ω * p.2)) ∂(knotAtomOrbit q θ r) =
      ENNReal.ofReal (knotAtomCascade q θ r t ω) := by
  have hq0 : 0 < q := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθr.1.1
  have hr : 0 < r := hθr.2
  have hS : MeasurableSet (Ioc 0 t ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioc.prod measurableSet_Ioi
  have hnn : ∀ n : ℤ, 0 ≤ (if θ * q ^ n ≤ t then 1 - Real.cos (ω * (r * θ * q ^ n)) else 0) :=
    fun n => by split_ifs <;> linarith [Real.cos_le_one (ω * (r * θ * q ^ n))]
  rw [← lintegral_indicator hS, knotAtomOrbit, lintegral_sum_measure, knotAtomCascade,
    ENNReal.ofReal_tsum_of_nonneg hnn (knot_summable hq hθr t ω)]
  refine tsum_congr fun n => ?_
  rw [lintegral_dirac]
  have hpos : 0 < θ * q ^ n := mul_pos hθ0 (zpow_pos hq0 n)
  by_cases h : θ * q ^ n ≤ t
  · rw [indicator_of_mem (show (θ * q ^ n, r * θ * q ^ n) ∈ Ioc 0 t ×ˢ Ioi (0 : ℝ) from
      ⟨⟨hpos, h⟩, by rw [mul_assoc]; exact mul_pos hr hpos⟩), if_pos h]
  · rw [indicator_of_notMem (fun hm => h hm.1.2), if_neg h, ENNReal.ofReal_zero]

/-- **(A.e2) of a mixture of finitely many orbits**, with `ℬ = 0`. -/
theorem surfaceExponent_finite {q : ℝ} (hq : 1 < q) {J : ℕ} (c θ r : Fin J → ℝ)
    (hc : ∀ j, 0 < c j) (hθr : ∀ j, (θ j, r j) ∈ cylinder q) (t ω : ℝ) :
    surfaceExponent (orbitMixture q
        (Measure.sum fun j => ENNReal.ofReal (c j) • Measure.dirac (θ j, r j))) 0 t ω =
      ∑ j, c j * knotAtomCascade q (θ j) (r j) t ω := by
  have hS : MeasurableSet (Ioc 0 t ×ˢ Ioi (0 : ℝ)) := measurableSet_Ioc.prod measurableSet_Ioi
  have hK0 : ∀ j, 0 ≤ knotAtomCascade q (θ j) (r j) t ω := fun j => by
    rw [knotAtomCascade]
    exact tsum_nonneg fun n => by
      split_ifs <;> linarith [Real.cos_le_one (ω * (r j * θ j * q ^ n))]
  have hmix : orbitMixture q
      (Measure.sum fun j => ENNReal.ofReal (c j) • Measure.dirac (θ j, r j)) =
      Measure.sum fun j => ENNReal.ofReal (c j) • knotAtomOrbit q (θ j) (r j) := by
    rw [orbitMixture_sum]
    congr 1
    funext j
    rw [orbitMixture_smul, orbitMixture_dirac]
  simp only [surfaceExponent, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, zero_mul,
    zero_add]
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun p => by simp only [Pi.zero_apply]; linarith [Real.cos_le_one (ω * p.2)])
    ((by fun_prop : Continuous fun p : ℝ × ℝ => 1 - Real.cos (ω * p.2)).aestronglyMeasurable),
    hmix, Measure.restrict_sum _ hS, lintegral_sum_measure, tsum_fintype]
  simp_rw [Measure.restrict_smul, lintegral_smul_measure, lintegral_knotAtomOrbit_slab hq (hθr _),
    smul_eq_mul, ← ENNReal.ofReal_mul (hc _).le]
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hc j).le (hK0 j),
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun j _ => mul_nonneg (hc j).le (hK0 j))]

/-- **The increment of a cascade** between `s < t` is the finite sum over the knots in `(s,t]`. -/
theorem knotAtomCascade_sub {q : ℝ} (hq : 1 < q) {θ r : ℝ} (hθr : (θ, r) ∈ cylinder q) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (ω : ℝ) :
    knotAtomCascade q θ r t ω - knotAtomCascade q θ r s ω =
      ∑ n ∈ Finset.Ioc (dgLevel q (s / θ)) (dgLevel q (t / θ)),
        (1 - Real.cos (ω * (r * θ * q ^ n))) := by
  have hθ0 : 0 < θ := lt_of_lt_of_le one_pos hθr.1.1
  have ht : 0 < t := hs.trans hst
  have hiff_t := mul_zpow_le_iff hq hθ0 ht
  have hiff_s := mul_zpow_le_iff hq hθ0 hs
  have hLL : dgLevel q (s / θ) ≤ dgLevel q (t / θ) :=
    (hiff_t _).1 (((hiff_s _).2 le_rfl).trans hst.le)
  rw [knotAtomCascade, knotAtomCascade,
    ← (knot_summable hq hθr t ω).tsum_sub (knot_summable hq hθr s ω)]
  rw [tsum_eq_sum (s := Finset.Ioc (dgLevel q (s / θ)) (dgLevel q (t / θ))) fun n hn => ?_]
  · refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
    rw [if_pos ((hiff_t n).2 h2), if_neg (fun h => by have := (hiff_s n).1 h; omega), sub_zero]
  · rw [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hn
    rcases hn with h | h
    · have hst' : θ * q ^ n ≤ t := ((hiff_s n).2 h).trans hst.le
      rw [if_pos hst', if_pos ((hiff_s n).2 h), sub_self]
    · rw [if_neg (fun h' => by have := (hiff_t n).1 h'; omega),
        if_neg (fun h' => by have := (hiff_s n).1 h'; omega), sub_self]

/-- **`prop:extreme-rays-random-walks`(5), finitely many atoms.** For `σ = ∑_j c_j δ_{(θ_j, r_j)}`,
the step from `s` to `t` of the member `(Λ_σ, 0)` of the cone (the law with transform
`e^{-(Ψ_t - Ψ_s)}`, `Ψ` of (A.e2) with `ℬ = 0`) is the convolution of the finitely many laws
`exp[c_j δ²_{r_jθ_jqⁿ}]` over the pairs `(j, n)` with `s < θ_jqⁿ ≤ t`. -/
theorem extreme_rays_random_walks_5_finite {q : ℝ} (hq : 1 < q) {J : ℕ} (c θ r : Fin J → ℝ)
    (hc : ∀ j, 0 < c j) (hθr : ∀ j, (θ j, r j) ∈ cylinder q) {s t : ℝ} (hs : 0 < s)
    (hst : s < t) :
    IsProbabilityMeasure (convList ((Finset.univ : Finset (Fin J)).toList.flatMap fun j =>
        ((Finset.Ioc (dgLevel q (s / θ j)) (dgLevel q (t / θ j))).toList.map
          fun n => randomWalkLaw (c j) (r j * θ j * q ^ n)))) ∧
      ∀ ω : ℝ, charFun (convList ((Finset.univ : Finset (Fin J)).toList.flatMap fun j =>
          ((Finset.Ioc (dgLevel q (s / θ j)) (dgLevel q (t / θ j))).toList.map
            fun n => randomWalkLaw (c j) (r j * θ j * q ^ n)))) ω =
        ((Real.exp (-(surfaceExponent (orbitMixture q
            (Measure.sum fun j => ENNReal.ofReal (c j) • Measure.dirac (θ j, r j))) 0 t ω -
          surfaceExponent (orbitMixture q
            (Measure.sum fun j => ENNReal.ofReal (c j) • Measure.dirac (θ j, r j))) 0 s ω)) :
          ℝ) : ℂ) := by
  set l : List (ℝ × ℝ) := (Finset.univ : Finset (Fin J)).toList.flatMap fun j =>
    (Finset.Ioc (dgLevel q (s / θ j)) (dgLevel q (t / θ j))).toList.map
      fun n => (c j, r j * θ j * q ^ n) with hl
  have hlist : ((Finset.univ : Finset (Fin J)).toList.flatMap fun j =>
      (Finset.Ioc (dgLevel q (s / θ j)) (dgLevel q (t / θ j))).toList.map
        fun n => randomWalkLaw (c j) (r j * θ j * q ^ n)) =
      l.map fun p => randomWalkLaw p.1 p.2 := by
    rw [hl, List.map_flatMap]
    congr 1
    funext j
    rw [List.map_map]
    rfl
  have hcl : ∀ p ∈ l, 0 ≤ p.1 := by
    intro p hp
    obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hp
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hj
    exact (hc j).le
  obtain ⟨h1, h2⟩ := randomWalk_list hcl
  refine ⟨by rw [hlist]; exact h1, fun ω => ?_⟩
  rw [hlist, h2, surfaceExponent_finite hq c θ r hc hθr, surfaceExponent_finite hq c θ r hc hθr,
    ← Finset.sum_sub_distrib]
  congr 3
  rw [hl, sum_map_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_sub, knotAtomCascade_sub hq (hθr j) hs hst, List.map_map, Finset.sum_map_toList,
    Finset.mul_sum]
  rfl

end Pyramids
