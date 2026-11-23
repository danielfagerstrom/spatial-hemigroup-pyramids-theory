/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Pyramid
import Pyramids.Cited.A39
import Pyramids.Cited.A40
import Pyramids.Cited.A42
import AffineHemigroup.CascadeDivisible
import AffineHemigroup.PolarReading
import AffineHemigroup.TripletSum
import AffineHemigroup.Gauge
import AffineHemigroup.InvariantOrders

/-!
# `lem:family-structure`: the structure of a symmetric family in dimension `d`

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `lem:family-structure`, chapter 3. Wave 2b: the
five declarations moved here from `PyramidsSkeleton.Ch03Pyramid`, their statements unchanged.

## The route

* **Infinite divisibility of every step** (`isLawHemigroup_infinitelyDivisible`): the affine
  export's `cascade_interval_infinitelyDivisible`, read on the segment `u ↦ s + u(t - s)`. That
  theorem builds the null array of the printed proof from (I1) and (I2) (uniformly small short
  steps, by Lévy's continuity theorem and the portmanteau inequality) and applies Khintchine's
  theorem in the export's measure form, `khintchine_null_array`, which is ledger A41's admitted
  name. Neither symmetry nor (ND) is used, which is what `prop:no-bounded-step` reads.
* **Positivity of the transform**: a symmetric law has a real transform; `cited_A40` (A40) gives no
  zero; along the segment from `0` to `ω` the real part starts at `1` and cannot cross `0`.
* **The data**: a symmetric infinitely divisible law has the triplet `(A^S, ν, γ)` of
  `cited_A39`(i); the reflected law has the triplet pushed by `x ↦ -x` (`LevyTriplet.pushIso`), so
  uniqueness (A39(ii)) gives `γ = 0` and `ν` symmetric, and the exponent is `⟨ω, Aω⟩ + ∫ (1 -
  cos⟨ω,x⟩) ν(dx)` with `A = A^S/2` (`lkExponent_of_symm_general`). Conversely data `(A, ν)` are the
  triplet `(2A, ν, 0)` (`SymLevyData.triplet`), and two data of one law agree by A39(ii).
* **The increments**: the triplet of `μ_t = μ_s ∗ μ_{s,t}` is the sum of the two triplets
  (`HasTriplet.conv`), and uniqueness identifies it with the triplet of the data of `μ_t`.
* **The isotropic clause**: `cited_A42` (A42) at an orthogonal `Q` gives the triplet of `Q_*μ_t =
  μ_t`; uniqueness gives `QA_tQᵀ = A_t` and `Q_*ν_t = ν_t`, and the export's
  `eq_smul_one_of_orth_invariant` makes `A_t` a multiple of `I`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace

variable {d : ℕ}

/-! ## Infinite divisibility of the steps -/

/-- **Every step of a family with (I1) and (I2) is infinitely divisible**, in dimension `d ≥ 1`:
the affine export's `cascade_interval_infinitelyDivisible` on the segment `u ↦ s + u(t - s)`
(Khintchine's theorem, ledger A41, in the export's form `khintchine_null_array`). -/
theorem isLawHemigroup_infinitelyDivisible (hd : 1 ≤ d) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : IsLawHemigroup μ) : ∀ s t : ℝ, 0 ≤ s → s ≤ t → IsInfinitelyDivisible (μ s t) := by
  intro s t hs hst
  set L : ℝ → ℝ := fun u => s + u * (t - s) with hL
  have hL0 : ∀ u, 0 ≤ u → 0 ≤ L u := fun u hu => by simp only [hL]; nlinarith
  have hLmono : ∀ u v, u ≤ v → L u ≤ L v := fun u v huv => by simp only [hL]; nlinarith
  have h := cascade_interval_infinitelyDivisible hd (fun u v => μ (L u) (L v))
    (fun u v hu huv _ => hμ.isProbability _ _ (hL0 u hu) (hLmono u v huv))
    (fun u hu _ => hμ.diag _ (hL0 u hu))
    (fun u v w hu huv hvw _ => hμ.cascade _ _ _ (hL0 u hu) (hLmono u v huv) (hLmono v w hvw))
    (fun ω => by
      have hc : ContinuousOn (fun p : ℝ × ℝ => (L p.1, L p.2))
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} :=
        (Continuous.continuousOn (by fun_prop))
      exact (hμ.continuous ω).comp hc fun p hp => ⟨hL0 _ hp.1, hLmono _ _ hp.2.1⟩)
    0 1 le_rfl zero_le_one le_rfl
  have h0 : L 0 = s := by simp [hL]
  have h1 : L 1 = t := by simp [hL]
  simpa [h0, h1] using h

/-! ## The transform of a symmetric infinitely divisible law -/

/-- The reflection `x ↦ -x` as a linear isometry. -/
theorem coe_neg_isometry : ⇑(LinearIsometryEquiv.neg ℝ (E := Rd d)) = fun x => -x := rfl

/-- The transform of a symmetric law is real. -/
theorem charFun_im_eq_zero_of_symm {μ : Measure (Rd d)} (hs : μ.map (fun x => -x) = μ)
    (ω : Rd d) : (charFun μ ω).im = 0 := by
  have h := charFun_map_isometry μ (LinearIsometryEquiv.neg ℝ (E := Rd d)) ω
  rw [coe_neg_isometry, hs] at h
  have h' : charFun μ ω = (starRingEnd ℂ) (charFun μ ω) := by
    rw [← charFun_neg]
    simpa using h
  exact Complex.conj_eq_iff_im.1 h'.symm

/-- **The transform of a symmetric infinitely divisible law is positive**: real, without zeros
(`cited_A40`), and `1` at the origin. -/
theorem charFun_pos_of_symm {μ : Measure (Rd d)} [IsProbabilityMeasure μ]
    (hid : IsInfinitelyDivisible μ) (hs : μ.map (fun x => -x) = μ) (ω : Rd d) :
    0 < charFun μ ω := by
  have him : ∀ ω, (charFun μ ω).im = 0 := charFun_im_eq_zero_of_symm hs
  have hne : ∀ ω, (charFun μ ω).re ≠ 0 := fun ω h =>
    cited_A40 μ hid ω (Complex.ext h (him ω))
  set g : ℝ → ℝ := fun t => (charFun μ (t • ω)).re with hg
  have hgc : Continuous g :=
    Complex.continuous_re.comp (continuous_charFun.comp (continuous_id.smul continuous_const))
  have hg0 : g 0 = 1 := by simp [hg, charFun_zero]
  have hpos : 0 < g 1 := by
    by_contra hle
    push Not at hle
    obtain ⟨c, -, hgc0⟩ := intermediate_value_Icc' zero_le_one hgc.continuousOn
      ⟨hle, by rw [hg0]; exact zero_le_one⟩
    exact hne _ hgc0
  rw [Complex.lt_def]
  refine ⟨by simpa [hg] using hpos, ?_⟩
  rw [him ω]
  rfl

/-! ## Symmetric Lévy data and triplets -/

/-- **The exponent of a triplet with `γ = 0` and a symmetric Lévy measure**:
`-(½⟨z, A^S z⟩ + ∫ (1 - cos⟨z,x⟩) ν(dx))`; the odd part of the integrand integrates to `0`. -/
theorem lkExponent_of_symm_general (T : LevyTriplet d) (hγ : T.γ = 0)
    (hsym : T.ν.map (fun x => -x) = T.ν) (z : Rd d) :
    T.lkExponent z = -(((quad T.A z / 2 + ∫ x, (1 - Real.cos ⟪z, x⟫) ∂T.ν : ℝ)) : ℂ) := by
  have hsymI : ∫ x, (lkIntegrand z x).im ∂T.ν = 0 := by
    have h1 : ∫ x, (lkIntegrand z x).im ∂T.ν = ∫ x, (lkIntegrand z (-x)).im ∂T.ν := by
      conv_lhs => rw [← hsym]
      exact integral_map (f := fun x => (lkIntegrand z x).im) measurable_neg.aemeasurable
        ((Complex.measurable_im.comp (measurable_lkIntegrand z)).aestronglyMeasurable)
    simp_rw [im_lkIntegrand_neg, integral_neg] at h1
    linarith
  have hint := T.integrable_lkIntegrand z
  apply Complex.ext
  · rw [T.re_lkExponent, Complex.neg_re, Complex.ofReal_re]
    ring
  · rw [T.lkExponent_eq, Complex.add_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, Complex.ofReal_im, ← RCLike.im_to_complex, ← integral_im hint]
    simp_rw [RCLike.im_to_complex, hsymI]
    simp [hγ]

/-- **The triplet of symmetric data** `(A, ν)`: `(2A, ν, 0)`, Sato's covariance being twice this
paper's Gaussian datum. -/
noncomputable def SymLevyData.triplet (D : SymLevyData d) : LevyTriplet d where
  A := (2 : ℝ) • D.A
  ν := D.ν
  γ := 0
  A_posSemidef := D.A_posSemidef.smul (by norm_num)
  ν_zero := D.ν_zero
  ν_integrable := D.ν_integrable

/-- The exponent of the triplet of data is minus the exponent of the data. -/
theorem SymLevyData.lkExponent_triplet (D : SymLevyData d) (z : Rd d) :
    D.triplet.lkExponent z = -((D.exponent z : ℝ) : ℂ) := by
  rw [lkExponent_of_symm_general D.triplet rfl D.ν_symm z]
  congr 2
  simp only [SymLevyData.triplet, SymLevyData.exponent, pairExponent, quad_smul]
  ring

/-- Data of a law give its triplet. -/
theorem SymLevyData.hasTriplet {μ : Measure (Rd d)} {D : SymLevyData d} (h : IsSymData μ D) :
    HasTriplet μ D.triplet := fun z => by
  rw [h z, D.lkExponent_triplet, Complex.ofReal_exp, Complex.ofReal_neg]

/-- A probability measure with a triplet is infinitely divisible: the law of A39(iii) has the same
transform. -/
theorem isInfinitelyDivisible_of_hasTriplet {μ : Measure (Rd d)} [IsProbabilityMeasure μ]
    {T : LevyTriplet d} (hT : HasTriplet μ T) : IsInfinitelyDivisible μ := by
  obtain ⟨μ', hprob, hid, hT'⟩ := cited_A39_converse T
  haveI := hprob
  have heq : μ' = μ := Measure.ext_of_charFun (funext fun z => by rw [hT' z, hT z])
  rw [← heq]
  exact hid

/-- **Two data of one law agree** (A39(ii)). -/
theorem isSymData_unique {μ : Measure (Rd d)} [IsProbabilityMeasure μ] {D D' : SymLevyData d}
    (h : IsSymData μ D) (h' : IsSymData μ D') : D.A = D'.A ∧ D.ν = D'.ν := by
  obtain ⟨hA, hν, -⟩ := cited_A39_unique μ (isInfinitelyDivisible_of_hasTriplet
    (SymLevyData.hasTriplet h)) _ _ (SymLevyData.hasTriplet h) (SymLevyData.hasTriplet h')
  refine ⟨?_, hν⟩
  have h2 : (2 : ℝ) • D.A = (2 : ℝ) • D'.A := hA
  exact smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0) h2

/-- **A symmetric infinitely divisible law has symmetric Lévy data** (A39(i), (ii)). -/
theorem exists_symData {μ : Measure (Rd d)} [IsProbabilityMeasure μ]
    (hid : IsInfinitelyDivisible μ) (hs : μ.map (fun x => -x) = μ) :
    ∃ D : SymLevyData d, IsSymData μ D := by
  obtain ⟨T, hT⟩ := cited_A39_exists μ hid
  set Q := LinearIsometryEquiv.neg ℝ (E := Rd d) with hQ
  have hT' : HasTriplet μ (T.pushIso Q) := fun z => by
    have h := charFun_map_isometry μ Q z
    rw [hQ, coe_neg_isometry, hs] at h
    rw [h, hT, LevyTriplet.lkExponent_pushIso]
  obtain ⟨-, hν, hγ⟩ := cited_A39_unique μ hid T (T.pushIso Q) hT hT'
  have hγ0 : T.γ = 0 := by
    have h1 : T.γ = -T.γ := hγ
    have h2 : (2 : ℝ) • T.γ = 0 := by rw [two_smul]; nth_rewrite 2 [h1]; exact add_neg_cancel _
    exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
  have hsym : T.ν.map (fun x => -x) = T.ν := hν.symm
  refine ⟨⟨(1 / 2 : ℝ) • T.A, T.ν, T.A_posSemidef.smul (by norm_num), T.ν_zero, T.ν_integrable,
    hsym⟩, fun z => ?_⟩
  rw [hT z, lkExponent_of_symm_general T hγ0 hsym z, Complex.ofReal_exp, Complex.ofReal_neg]
  congr 3
  simp only [SymLevyData.exponent, pairExponent, quad_smul]
  ring

/-- A law with a real transform is symmetric. (Moved here from `Pyramids.Price.GridKnot` for
`symmetric_levy_khintchine`, 2026-11-23; statement and proof unchanged.) -/
theorem map_neg_eq_of_charFun_im {m : Measure (Rd d)} [IsProbabilityMeasure m]
    (h : ∀ ω : Rd d, (charFun m ω).im = 0) : m.map (fun x => -x) = m := by
  haveI : IsProbabilityMeasure (m.map fun x => -x) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  have h1 := charFun_map_isometry m (LinearIsometryEquiv.neg ℝ (E := Rd d)) ω
  rw [coe_neg_isometry] at h1
  have hn : (LinearIsometryEquiv.neg ℝ (E := Rd d)).symm ω = -ω := rfl
  rw [h1, hn, charFun_neg]
  exact Complex.conj_eq_iff_im.2 (h ω)

/-- **`lem:symmetric-levy-khintchine`: the symmetric Lévy–Khintchine form.** A probability measure
on `ℝ^d` is symmetric and infinitely divisible iff it has symmetric Lévy data `(A, ν)`
(`exists_symData`; conversely `isInfinitelyDivisible_of_hasTriplet` and
`map_neg_eq_of_charFun_im`); the data are unique (`isSymData_unique`); and data give the triplet
`(2A, ν, 0)` (`SymLevyData.hasTriplet`). The node's statement, assembled from the declarations its
citing proofs call. -/
theorem symmetric_levy_khintchine {μ : Measure (Rd d)} [IsProbabilityMeasure μ] :
    ((IsInfinitelyDivisible μ ∧ μ.map (fun x => -x) = μ) ↔
        ∃ D : SymLevyData d, IsSymData μ D) ∧
      (∀ D D' : SymLevyData d, IsSymData μ D → IsSymData μ D' → D.A = D'.A ∧ D.ν = D'.ν) ∧
      ∀ D : SymLevyData d, IsSymData μ D → HasTriplet μ D.triplet := by
  refine ⟨⟨fun h => exists_symData h.1 h.2, fun ⟨D, hD⟩ => ⟨?_, ?_⟩⟩,
    fun D D' h h' => isSymData_unique h h', fun D h => SymLevyData.hasTriplet h⟩
  · exact isInfinitelyDivisible_of_hasTriplet (SymLevyData.hasTriplet hD)
  · exact map_neg_eq_of_charFun_im fun ω => by rw [hD ω, Complex.ofReal_im]

/-- **The triplet of a rotation-invariant law** is invariant: `QA^SQᵀ = A^S` and `Q_*ν = ν` for
every `Q ∈ O(d)` (A42 at `U = Q`, read at time `1`, with A39(ii)). -/
theorem triplet_rotation {μ : Measure (Rd d)} [IsProbabilityMeasure μ]
    (hid : IsInfinitelyDivisible μ) (hrot : IsRotationInvariant μ) {T : LevyTriplet d}
    (hT : HasTriplet μ T) :
    (∀ Q ∈ orthSet d, act Q T.A = T.A) ∧ IsRotationInvariant T.ν := by
  have key : ∀ Q ∈ orthSet d, act Q T.A = T.A ∧ push Q T.ν = T.ν := by
    intro Q hQ
    have hmap : μ.map (Matrix.toEuclideanLin Q) = μ := hrot Q hQ
    obtain ⟨-, -, T', hT', hA', hν', -⟩ := cited_A42 μ hid T hT Q
    rw [hmap] at hT'
    obtain ⟨hA, hν, -⟩ := cited_A39_unique μ hid _ _ hT hT'
    have hinj : ∀ x : Rd d, Matrix.toEuclideanLin Q x = 0 → x = 0 := by
      intro x hx
      have h1 : lin Q.transpose (lin Q x) = x := by
        change (lin Q.transpose * lin Q) x = x
        rw [← lin_mul, orth_transpose_mul hQ, lin_one]
        rfl
      rw [← h1]
      have h2 : lin Q x = 0 := hx
      rw [h2, map_zero]
    refine ⟨(hA.trans hA').symm, ?_⟩
    have h0 : (T.ν.map (Matrix.toEuclideanLin Q)) {0} = 0 := by
      rw [Measure.map_apply (Matrix.toEuclideanLin Q).continuous_of_finiteDimensional.measurable
        (measurableSet_singleton 0)]
      refine measure_mono_null (fun x hx => ?_) T.ν_zero
      exact hinj x hx
    have hrestr : (T.ν.map (Matrix.toEuclideanLin Q)).restrict {0}ᶜ
        = T.ν.map (Matrix.toEuclideanLin Q) := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff]
      simpa using h0
    exact ((hν.trans hν').trans hrestr).symm
  exact ⟨fun Q hQ => (key Q hQ).1, fun Q hQ => (key Q hQ).2⟩

/-- **The data of a rotation-invariant law** are invariant: `QAQᵀ = A` and `Q_*ν = ν` for every
`Q ∈ O(d)` (`triplet_rotation` at the triplet `(2A, ν, 0)`). -/
theorem symData_rotation {μ : Measure (Rd d)} [IsProbabilityMeasure μ]
    (hid : IsInfinitelyDivisible μ) (hrot : IsRotationInvariant μ) {D : SymLevyData d}
    (hD : IsSymData μ D) :
    (∀ Q ∈ orthSet d, act Q D.A = D.A) ∧ IsRotationInvariant D.ν := by
  obtain ⟨hA, hν⟩ := triplet_rotation hid hrot (SymLevyData.hasTriplet hD)
  refine ⟨fun Q hQ => ?_, hν⟩
  have h2 : act Q ((2 : ℝ) • D.A) = (2 : ℝ) • D.A := hA Q hQ
  rw [act, Matrix.mul_smul, Matrix.smul_mul] at h2
  exact smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0) h2

/-! ## `lem:family-structure` -/

/-- **`lem:family-structure`, infinite divisibility.** Each step `μ_{s,t}` of a symmetric family
in dimension `d` is infinitely divisible with `μ̂_{s,t} > 0`. -/
theorem family_structure_id (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      IsInfinitelyDivisible (μ s t) ∧ ∀ ω : Rd d, 0 < charFun (μ s t) ω := by
  intro s t hs hst
  haveI := hμ.1.isProbability s t hs hst
  have hid := isLawHemigroup_infinitelyDivisible hd hμ.1 s t hs hst
  exact ⟨hid, charFun_pos_of_symm hid (hμ.2.2 s t hs hst)⟩

/-- **`lem:family-structure`, the data exist**: every kernel `μ_t`, `t ≥ 0`, has symmetric Lévy
data `(A_t, ν_t)`, `Ψ_t = -log μ̂_t` being their exponent. -/
theorem family_structure_exists (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) :
    ∃ D : ℝ → SymLevyData d, ∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t) := by
  have h : ∀ t : ℝ, ∃ E : SymLevyData d, 0 ≤ t → IsSymData (μ 0 t) E := by
    intro t
    by_cases ht : 0 ≤ t
    · haveI := hμ.1.isProbability 0 t le_rfl ht
      obtain ⟨E, hE⟩ := exists_symData (isLawHemigroup_infinitelyDivisible hd hμ.1 0 t le_rfl ht)
        (hμ.2.2 0 t le_rfl ht)
      exact ⟨E, fun _ => hE⟩
    · exact ⟨⟨0, 0, Matrix.PosSemidef.zero, rfl, by simp, by simp⟩, fun h => absurd h ht⟩
  choose D hD using h
  exact ⟨D, hD⟩

/-- **`lem:family-structure`, the data.** For the data `D t` of the kernels: `Ψ_t = -log μ̂_t`;
`μ̂_{s,t} = e^{-(Ψ_t - Ψ_s)}`; `A_t` and `ν_t` are nondecreasing (`A_t - A_s` positive
semidefinite, `ν_s ≤ ν_t` setwise); and `μ_{s,t}` has the data `(A_t - A_s, ν_t - ν_s)`. -/
theorem family_structure_data (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) (D : ℝ → SymLevyData d)
    (hD : ∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t)) :
    (∀ t : ℝ, 0 ≤ t → ∀ ω : Rd d, (D t).exponent ω = -Real.log (charFun (μ 0 t) ω).re) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        (∀ ω : Rd d, charFun (μ s t) ω =
          ((Real.exp (-((D t).exponent ω - (D s).exponent ω)) : ℝ) : ℂ)) ∧
        ((D t).A - (D s).A).PosSemidef ∧ (D s).ν ≤ (D t).ν ∧
        ∃ Q : SymLevyData d, Q.A = (D t).A - (D s).A ∧ Q.ν + (D s).ν = (D t).ν ∧
          IsSymData (μ s t) Q := by
  refine ⟨fun t ht ω => ?_, fun s t hs hst => ?_⟩
  · rw [hD t ht ω, Complex.ofReal_re, Real.log_exp, neg_neg]
  haveI := hμ.1.isProbability s t hs hst
  haveI := hμ.1.isProbability 0 s le_rfl hs
  haveI := hμ.1.isProbability 0 t le_rfl (hs.trans hst)
  obtain ⟨E, hE⟩ := exists_symData (isLawHemigroup_infinitelyDivisible hd hμ.1 s t hs hst)
    (hμ.2.2 s t hs hst)
  have hcasc : μ 0 t = μ 0 s ∗ μ s t := by
    rw [hμ.1.cascade 0 s t le_rfl hs hst, Measure.conv_comm]
  -- the exponents add
  have hexp : ∀ ω : Rd d, (D t).exponent ω = (D s).exponent ω + E.exponent ω := by
    intro ω
    have h := charFun_conv (μ := μ 0 s) (ν := μ s t) ω
    rw [← hcasc, hD t (hs.trans hst) ω, hD s hs ω, hE ω, ← Complex.ofReal_mul,
      ← Real.exp_add] at h
    have h' := Real.exp_injective (Complex.ofReal_injective h)
    linarith
  -- the data add
  have hT : HasTriplet (μ 0 t) ((D s).triplet.add E.triplet) := by
    rw [hcasc]
    exact (SymLevyData.hasTriplet (hD s hs)).conv (SymLevyData.hasTriplet hE)
  obtain ⟨hA, hν, -⟩ := cited_A39_unique (μ 0 t)
    (isLawHemigroup_infinitelyDivisible hd hμ.1 0 t le_rfl (hs.trans hst)) _ _
    (SymLevyData.hasTriplet (hD t (hs.trans hst))) hT
  have hA' : (D t).A = (D s).A + E.A := by
    have h2 : (2 : ℝ) • (D t).A = (2 : ℝ) • ((D s).A + E.A) := by
      rw [smul_add]; exact hA
    exact smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0) h2
  have hν' : (D t).ν = (D s).ν + E.ν := hν
  have hEA : E.A = (D t).A - (D s).A := by rw [hA']; abel
  refine ⟨fun ω => ?_, hEA ▸ E.A_posSemidef, ?_, E, hEA, by rw [hν', add_comm], hE⟩
  · rw [hE ω, hexp ω]
    congr 3
    ring
  · rw [hν']
    exact Measure.le_add_right le_rfl

/-- For `0 ≤ s ≤ t`: `μ̂_t = μ̂_{s,t} μ̂_s`. -/
theorem charFun_kernel_mul (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsLawHemigroup μ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ω : Rd d) :
    charFun (μ 0 t) ω = charFun (μ s t) ω * charFun (μ 0 s) ω := by
  haveI := hμ.isProbability s t hs hst
  haveI := hμ.isProbability 0 s le_rfl hs
  rw [hμ.cascade 0 s t le_rfl hs hst, charFun_conv]

/-- **`lem:family-structure`, injectivity and monotonicity.** `t ↦ μ_t` is injective on `[0,∞)`,
and `t ↦ μ̂_t(ω)` is nonincreasing (in the order of `ℂ`, which also says the values are real). -/
theorem family_structure_monotone (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) :
    InjOn (fun t => μ 0 t) (Ici 0) ∧
      ∀ ω : Rd d, ∀ s t : ℝ, 0 ≤ s → s ≤ t → charFun (μ 0 t) ω ≤ charFun (μ 0 s) ω := by
  have hid := family_structure_id hd μ hμ
  -- two kernels at `t < t'` differ
  have hne : ∀ t t' : ℝ, 0 ≤ t → t < t' → μ 0 t ≠ μ 0 t' := by
    intro t t' ht htt' heq
    haveI := hμ.1.isProbability t t' ht htt'.le
    have h1 : ∀ ω, charFun (μ t t') ω = 1 := by
      intro ω
      have h := charFun_kernel_mul μ hμ.1 ht htt'.le ω
      rw [← heq] at h
      have h0 : charFun (μ 0 t) ω ≠ 0 := ((hid 0 t le_rfl ht).2 ω).ne'
      have h2 : charFun (μ t t') ω * charFun (μ 0 t) ω = 1 * charFun (μ 0 t) ω := by
        rw [← h, one_mul]
      exact mul_right_cancel₀ h0 h2
    have hdirac : μ t t' = Measure.dirac 0 :=
      Measure.ext_of_charFun (funext fun ω => by rw [h1 ω, charFun_dirac]; simp)
    exact hμ.2.1 t t' ht htt' hdirac
  refine ⟨fun t ht t' ht' heq => ?_, fun ω s t hs hst => ?_⟩
  · by_contra hneq
    rcases lt_or_gt_of_ne hneq with hlt | hlt
    · exact hne t t' ht hlt heq
    · exact hne t' t ht' hlt heq.symm
  · haveI := hμ.1.isProbability s t hs hst
    rw [charFun_kernel_mul μ hμ.1 hs hst ω]
    have hc := (hid s t hs hst).2 ω
    have ha := (hid 0 s le_rfl hs).2 ω
    rw [Complex.lt_def] at hc ha
    have hcle : (charFun (μ s t) ω).re ≤ 1 :=
      (Complex.re_le_norm _).trans (norm_charFun_le_one ω)
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · rw [Complex.mul_re, ← hc.2, ← ha.2]
      simp only [Complex.zero_im, mul_zero, sub_zero]
      exact mul_le_of_le_one_left ha.1.le hcle
    · rw [Complex.mul_im, ← hc.2, ← ha.2]
      simp

/-- **`lem:family-structure`, the isotropic clause.** If the family is also isotropic,
`A_t = a(t) I` and `ν_t` is rotation invariant. -/
theorem family_structure_isotropic (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) (hrot : IsRotationInvariantLaws μ) (D : ℝ → SymLevyData d)
    (hD : ∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t)) :
    ∃ a : ℝ → ℝ, ∀ t : ℝ, 0 ≤ t → (D t).A = a t • (1 : Mat d) ∧ IsRotationInvariant (D t).ν := by
  haveI : NeZero d := ⟨by omega⟩
  refine ⟨fun t => (D t).A 0 0, fun t ht => ?_⟩
  haveI := hμ.1.isProbability 0 t le_rfl ht
  obtain ⟨hA, hν⟩ := symData_rotation (isLawHemigroup_infinitelyDivisible hd hμ.1 0 t le_rfl ht)
    (hrot 0 t le_rfl ht) (hD t ht)
  exact ⟨eq_smul_one_of_orth_invariant hA, hν⟩

end Pyramids
