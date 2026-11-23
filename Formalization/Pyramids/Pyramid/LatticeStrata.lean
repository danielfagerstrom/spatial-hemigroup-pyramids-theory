/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.Synthesis
import Pyramids.Pyramid.DiscreteCovarianceLevy
import Pyramids.Pyramid.IsotropicSymmetric
import Pyramids.Cited.A31
import AffineHemigroup.SimilarityGeneral

/-!
# `thm:lattice-strata`: the lattice of strata in `ℝ^d`

Blueprint: `blueprint/src/parts/03-pyramid.tex`. Moved from `PyramidsSkeleton.Ch03Pyramid` in wave
2f, unchanged in statement and name.

* (1), the direct half, is `lem:family-structure` with the diagonal, the order of the data, (ND)
  and the continuity of `-log μ̂_t`.
* (1), the converse: the laws of the differences of the data exist by A39(iii)
  (`SymLevyData.exists_sub`, `cited_A39_converse`); (I1) and (I2) are the additivity and the
  continuity of the exponents; (ND) is A39(ii) (`isSymData_unique`); (I3) is the invariance of the
  exponent of rotation-invariant data.
* (2) is `lem:discrete-covariance-levy`, with `A_t = a(t)I`, and covariance iterated.
* (3) is A31 (`cited_A31`), read through the bridge between a family that is `λ`-covariant for
  every `λ > 0` and the affine export's `IsIsotropicCascadeFamily` (a chosen action `S`).
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology Matrix

variable {d : ℕ}

/-- The scalar of `c • 1` is read off its `(0,0)` entry. -/
theorem smul_one_inj (hd : 1 ≤ d) {a b : ℝ} (h : a • (1 : Mat d) = b • (1 : Mat d)) : a = b := by
  have := congrFun (congrFun h ⟨0, hd⟩) ⟨0, hd⟩
  simpa using this

/-- Data `(cI, ν)` with `ν` invariant under `O(d)` have an `O(d)`-invariant exponent. -/
theorem SymLevyData.exponent_orth (E : SymLevyData d) {c : ℝ} (hA : E.A = c • (1 : Mat d))
    (hν : IsRotationInvariant E.ν) {Q : Mat d} (hQ : Q ∈ orthSet d) (ω : Rd d) :
    E.exponent (lin Qᵀ ω) = E.exponent ω := by
  simp only [SymLevyData.exponent, pairExponent, hA, quad_smul, quad_one,
    norm_lin_of_orth (transpose_mem_orthSet hQ)]
  congr 1
  have hinner : ∀ x : Rd d, ⟪lin Qᵀ ω, x⟫ = ⟪ω, lin Q x⟫ := fun x => by
    rw [inner_lin_left, Matrix.transpose_transpose]
  simp_rw [hinner]
  have hmap : E.ν.map (lin Q) = E.ν := hν Q hQ
  rw [← integral_map (lin Q).continuous.aemeasurable
    (by fun_prop : Continuous fun x : Rd d => 1 - Real.cos ⟪ω, x⟫).aestronglyMeasurable, hmap]

/-- `push (λI)` is the image under `x ↦ λx`. -/
theorem push_smul_one_eq_map (lam : ℝ) (m : Measure (Rd d)) :
    push (lam • (1 : Mat d)) m = m.map (fun x => lam • x) := by
  have h : (⇑(lin (lam • (1 : Mat d))) : Rd d → Rd d) = fun x => lam • x := by
    ext x
    simp [lin_smul, lin_one]
  rw [push, h]

/-- A law with the exponent `0` is `δ₀`. -/
theorem eq_dirac_of_charFun_one {m : Measure (Rd d)} [IsProbabilityMeasure m]
    (h : ∀ ω : Rd d, charFun m ω = 1) : m = Measure.dirac 0 :=
  Measure.ext_of_charFun (funext fun ω => by rw [h ω, charFun_dirac, inner_zero_left,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero])

/-- Two data with one exponent are equal (A39(ii) on a law with these data, A39(iii)). -/
theorem SymLevyData.eq_of_exponent {E E' : SymLevyData d}
    (h : ∀ ω : Rd d, E.exponent ω = E'.exponent ω) : E.A = E'.A ∧ E.ν = E'.ν := by
  obtain ⟨m, hprob, -, hT⟩ := cited_A39_converse E.triplet
  haveI := hprob
  have hm : IsSymData m E := fun ω => by
    rw [hT ω, SymLevyData.lkExponent_triplet, Complex.ofReal_exp, Complex.ofReal_neg]
  exact isSymData_unique hm fun ω => by rw [hm ω, h ω]

/-! ## (1) -/

/-- **`thm:lattice-strata`(1), the direct half.** For an isotropic family with data
`(a(t) I, ν_t)`: the data vanish at `t = 0`, `a` and `ν_t` are nondecreasing, the difference is
nonzero for `s < t`, and `t ↦ Ψ_t(ω)` is continuous. -/
theorem lattice_strata_1 (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsIsotropicFamily μ)
    (D : ℝ → SymLevyData d) (hD : ∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t)) (a : ℝ → ℝ)
    (ha : ∀ t : ℝ, 0 ≤ t → (D t).A = a t • (1 : Mat d)) :
    (D 0).A = 0 ∧ (D 0).ν = 0 ∧ MonotoneOn a (Ici 0) ∧ MonotoneOn (fun t => (D t).ν) (Ici 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → (a s, (D s).ν) ≠ (a t, (D t).ν)) ∧
      ∀ ω : Rd d, ContinuousOn (fun t => (D t).exponent ω) (Ici 0) := by
  have hsym := isotropicFamily_isSymmetricFamily μ hμ
  obtain ⟨hlog, hdiff⟩ := family_structure_data hd μ hsym D hD
  -- the data at `0`
  haveI := hsym.1.isProbability 0 0 le_rfl le_rfl
  have hzero : IsSymData (μ 0 0) (SymLevyData.zero : SymLevyData d) := fun ω => by
    rw [hsym.1.diag 0 le_rfl, SymLevyData.zero_exponent, charFun_dirac, inner_zero_left]
    simp
  obtain ⟨hA0, hν0⟩ := isSymData_unique (hD 0 le_rfl) hzero
  refine ⟨hA0, hν0, fun s hs t ht hst => ?_, fun s hs t ht hst => (hdiff s t hs hst).2.2.1,
    fun s t hs hst heq => ?_, fun ω => ?_⟩
  · -- `a` is nondecreasing: the difference `(a t - a s) I` is positive semidefinite
    have hps := (hdiff s t hs hst).2.1
    rw [ha t (le_trans hs hst), ha s hs, ← sub_smul] at hps
    have h00 := hps.diag_nonneg (i := ⟨0, hd⟩)
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
    linarith
  · -- (ND)
    obtain ⟨has, hνs⟩ := Prod.mk.inj heq
    have hAeq : (D s).A = (D t).A := by rw [ha s hs, ha t (hs.trans hst.le), has]
    have hexp : ∀ ω, (D s).exponent ω = (D t).exponent ω := fun ω => by
      simp only [SymLevyData.exponent, pairExponent, hAeq, hνs]
    haveI := hsym.1.isProbability s t hs hst.le
    refine hμ.1.2 s t hs hst (eq_dirac_of_charFun_one fun ω => ?_)
    rw [(hdiff s t hs hst.le).1 ω, hexp ω, sub_self, neg_zero, Real.exp_zero, Complex.ofReal_one]
  · -- continuity: `Ψ_t = -log μ̂_t`, and `μ̂_t > 0`
    have hc : ContinuousOn (fun t => charFun (μ 0 t) ω) (Ici 0) := by
      have h := hsym.1.continuous ω
      refine h.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht => ?_
      exact ⟨le_rfl, ht⟩
    have hre : ContinuousOn (fun t => (charFun (μ 0 t) ω).re) (Ici 0) :=
      Complex.continuous_re.comp_continuousOn hc
    have hpos : ∀ t ∈ Ici (0 : ℝ), (charFun (μ 0 t) ω).re ≠ 0 := fun t ht => by
      have := ((family_structure_id hd μ hsym 0 t le_rfl ht).2 ω)
      exact (Complex.pos_iff.1 this).1.ne'
    refine ((hre.log hpos).neg).congr fun t ht => ?_
    exact hlog t ht ω

/-- **`thm:lattice-strata`(1), the converse.** Rotation-invariant data `(a(t) I, ν_t)` with
nonnegative nonzero differences for `s < t` and `Ψ_t(ω)` continuous in `t`: laws with
transform `e^{-(Ψ_t - Ψ_s)}` exist, and any such laws form an isotropic family. -/
theorem lattice_strata_1_converse (hd : 1 ≤ d) (D : ℝ → SymLevyData d) (a : ℝ → ℝ)
    (ha : ∀ t : ℝ, 0 ≤ t → (D t).A = a t • (1 : Mat d))
    (hrot : ∀ t : ℝ, 0 ≤ t → IsRotationInvariant (D t).ν)
    (hinc : ∀ s t : ℝ, 0 ≤ s → s < t →
      a s ≤ a t ∧ (D s).ν ≤ (D t).ν ∧ (a s, (D s).ν) ≠ (a t, (D t).ν))
    (hcont : ∀ ω : Rd d, ContinuousOn (fun t => (D t).exponent ω) (Ici 0)) :
    (∃ μ : ℝ → ℝ → Measure (Rd d), IsExponentLaws (fun t ω => (D t).exponent ω) μ) ∧
      ∀ μ : ℝ → ℝ → Measure (Rd d), IsExponentLaws (fun t ω => (D t).exponent ω) μ →
        IsIsotropicFamily μ := by
  set Ψ : ℝ → Rd d → ℝ := fun t ω => (D t).exponent ω with hΨ
  -- the laws exist
  have hlaw : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ∃ m : Measure (Rd d), IsProbabilityMeasure m ∧
      ∀ ω : Rd d, charFun m ω = ((Real.exp (-(Ψ t ω - Ψ s ω)) : ℝ) : ℂ) := by
    intro s t hs hst
    have hle : (D s).Le (D t) := by
      rcases hst.eq_or_lt with h | h
      · rw [h]; exact SymLevyData.Le.refl _
      · obtain ⟨has, hνs, -⟩ := hinc s t hs h
        refine ⟨?_, hνs⟩
        rw [ha s hs, ha t (hs.trans hst), Matrix.le_iff, ← sub_smul]
        exact Matrix.PosSemidef.one.smul (by linarith)
    obtain ⟨Q, -, -, hQ⟩ := SymLevyData.exists_sub hle
    obtain ⟨m, hprob, -, hT⟩ := cited_A39_converse Q.triplet
    refine ⟨m, hprob, fun ω => ?_⟩
    rw [hT ω, SymLevyData.lkExponent_triplet, Complex.ofReal_exp, Complex.ofReal_neg]
    simp only [hΨ, hQ ω]
    ring_nf
  refine ⟨?_, fun μ hμ => ?_⟩
  · have h : ∀ s t : ℝ, ∃ m : Measure (Rd d), 0 ≤ s → s ≤ t → IsProbabilityMeasure m ∧
        ∀ ω : Rd d, charFun m ω = ((Real.exp (-(Ψ t ω - Ψ s ω)) : ℝ) : ℂ) := by
      intro s t
      by_cases hst : 0 ≤ s ∧ s ≤ t
      · obtain ⟨m, hm⟩ := hlaw s t hst.1 hst.2
        exact ⟨m, fun _ _ => hm⟩
      · exact ⟨Measure.dirac 0, fun h1 h2 => absurd ⟨h1, h2⟩ hst⟩
    choose μ hμ using h
    exact ⟨μ, fun s t hs hst => hμ s t hs hst⟩
  have hprob := fun s t (hs : 0 ≤ s) (hst : s ≤ t) => (hμ s t hs hst).1
  have hc := fun s t (hs : 0 ≤ s) (hst : s ≤ t) => (hμ s t hs hst).2
  have hL : IsLawHemigroup μ := by
    refine ⟨hprob, fun t ht => ?_, fun r s t hr hrs hst => ?_, fun ω => ?_⟩
    · haveI := hprob t t ht le_rfl
      exact eq_dirac_of_charFun_one fun ω => by
        rw [hc t t ht le_rfl ω, sub_self, neg_zero, Real.exp_zero, Complex.ofReal_one]
    · haveI := hprob r t hr (hrs.trans hst)
      haveI := hprob s t (hr.trans hrs) hst
      haveI := hprob r s hr hrs
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      rw [charFun_conv, hc r t hr (hrs.trans hst), hc s t (hr.trans hrs) hst, hc r s hr hrs,
        ← Complex.ofReal_mul, ← Real.exp_add]
      ring_nf
    · have hcs : ContinuousOn (fun p : ℝ × ℝ => ((Real.exp (-(Ψ p.2 ω - Ψ p.1 ω)) : ℝ) : ℂ))
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by
        have h1 : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
          (hcont ω).comp continuous_fst.continuousOn fun p hp => hp.1
        have h2 : ContinuousOn (fun p : ℝ × ℝ => Ψ p.2 ω) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
          (hcont ω).comp continuous_snd.continuousOn fun p hp => (show (0 : ℝ) ≤ p.2 from
            hp.1.trans hp.2)
        exact Complex.continuous_ofReal.comp_continuousOn
          (Real.continuous_exp.comp_continuousOn ((h2.sub h1).neg))
      exact hcs.congr fun p hp => hc p.1 p.2 hp.1 hp.2 ω
  refine ⟨⟨hL, fun s t hs hst heq => ?_⟩, fun s t hs hst Q hQ => ?_⟩
  · -- (ND): equal exponents give equal data (A39(ii)), against `hinc`
    haveI := hprob s t hs hst.le
    have h1 : ∀ ω : Rd d, Ψ t ω = Ψ s ω := fun ω => by
      have h := hc s t hs hst.le ω
      rw [heq, charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
        at h
      have h2 : Real.exp (-(Ψ t ω - Ψ s ω)) = 1 := by exact_mod_cast h.symm
      have h3 := Real.exp_eq_one_iff _ |>.1 h2
      linarith
    obtain ⟨hA, hν⟩ := SymLevyData.eq_of_exponent (E := D s) (E' := D t) fun ω => (h1 ω).symm
    have has : a s = a t := by
      rw [ha s hs, ha t (hs.trans hst.le)] at hA
      exact smul_one_inj hd hA
    exact (hinc s t hs hst).2.2 (by rw [has, hν])
  · -- (I3)
    haveI := hprob s t hs hst
    haveI : IsProbabilityMeasure (push Q (μ s t)) :=
      Measure.isProbabilityMeasure_map (lin Q).continuous.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [push, charFun_map_lin, hc s t hs hst, hc s t hs hst]
    simp only [hΨ, SymLevyData.exponent_orth (D t) (ha t (hs.trans hst)) (hrot t (hs.trans hst)) hQ,
      SymLevyData.exponent_orth (D s) (ha s hs) (hrot s hs) hQ]

/-! ## (2) -/

/-- Covariance at `q` iterated: `μ_{qⁿt} = D_{qⁿ} μ_t` for every `n ∈ ℤ`, over any space. -/
theorem kernel_zpow_of_cov {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : ℝ → ℝ → Measure E} {q : ℝ} (hq : 1 < q)
    (hcov : IsCovariantAt μ q (fun t => q * t)) :
    ∀ (n : ℤ) (t : ℝ), 0 ≤ t → μ 0 (q ^ n * t) = (μ 0 t).map (fun x => (q ^ n) • x) := by
  have hq0 : 0 < q := by linarith
  have hstep : ∀ u : ℝ, 0 ≤ u → μ 0 (q * u) = (μ 0 u).map (fun x => q • x) := fun u hu => by
    have h := hcov.2 0 u le_rfl hu
    simp only [mul_zero] at h
    exact h.symm
  have hmm : ∀ (b c : ℝ) (m : Measure E),
      (m.map (fun x => c • x)).map (fun x => b • x) = m.map (fun x => (b * c) • x) := by
    intro b c m
    rw [Measure.map_map (continuous_const_smul b).measurable (continuous_const_smul c).measurable]
    congr 1
    ext x
    simp [smul_smul]
  intro n
  induction n using Int.induction_on with
  | zero => intro t _; simp
  | succ n ih =>
    intro t ht
    have hu : 0 ≤ q ^ (n : ℤ) * t := mul_nonneg (zpow_pos hq0 _).le ht
    rw [zpow_add_one₀ hq0.ne', mul_comm (q ^ (n : ℤ)) q, mul_assoc, hstep _ hu, ih t ht, hmm]
  | pred n ih =>
    intro t ht
    have hu : 0 ≤ q ^ (-(n : ℤ) - 1) * t := mul_nonneg (zpow_pos hq0 _).le ht
    have h2 := hstep _ hu
    have h3 : q * (q ^ (-(n : ℤ) - 1) * t) = q ^ (-(n : ℤ)) * t := by
      rw [← mul_assoc, ← zpow_one_add₀ hq0.ne']
      ring_nf
    rw [h3, ih t ht] at h2
    have h4 := congrArg (fun m => m.map (fun x => q⁻¹ • x)) h2
    simp only [hmm] at h4
    rw [inv_mul_cancel₀ hq0.ne'] at h4
    have h5 : (fun x : E => (1 : ℝ) • x) = id := by ext x; simp
    rw [h5, Measure.map_id] at h4
    rw [← h4, show q ^ (-(n : ℤ) - 1) = q⁻¹ * q ^ (-(n : ℤ)) by
      rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by ring, zpow_add₀ hq0.ne', zpow_neg_one]]

/-- **`thm:lattice-strata`(2), covariance under one dilation.** `q`-covariance with `S_q t = qt`
iff `a(qt) = q² a(t)` and `ν_{qt} = D_q ν_t` for `t > 0`; then every kernel is
semi-selfdecomposable with span `q`, and `μ_{q^n t} = D_{q^n} μ_t`. -/
theorem lattice_strata_2 (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsIsotropicFamily μ)
    (D : ℝ → SymLevyData d) (hD : ∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t)) (a : ℝ → ℝ)
    (ha : ∀ t : ℝ, 0 ≤ t → (D t).A = a t • (1 : Mat d)) {q : ℝ} (hq : 1 < q) :
    (IsCovariantAt μ q (fun t => q * t) ↔
        ∀ t : ℝ, 0 < t → a (q * t) = q ^ 2 * a t ∧ (D (q * t)).ν = (D t).ν.map (fun x => q • x)) ∧
      (IsCovariantAt μ q (fun t => q * t) →
        (∀ t : ℝ, 0 ≤ t → IsSemiSelfDecomposableWithSpan q (μ 0 t)) ∧
          ∀ (n : ℤ) (t : ℝ), 0 ≤ t → μ 0 (q ^ n * t) = (μ 0 t).map (fun x => (q ^ n) • x)) := by
  have hsym := isotropicFamily_isSymmetricFamily μ hμ
  have hq0 : 0 < q := by linarith
  obtain ⟨h1, h2⟩ := discrete_covariance_levy hd μ hsym D hD hq
  refine ⟨h1.trans (h2.trans ⟨fun h t ht => ?_, fun h t ht => ?_⟩), fun hcov =>
    ⟨discrete_covariance_levy_semi hd μ hsym hq hcov, kernel_zpow_of_cov hq hcov⟩⟩
  · obtain ⟨hA, hν⟩ := h t ht
    refine ⟨?_, hν⟩
    rw [ha _ (mul_pos hq0 ht).le, ha t ht.le, smul_smul] at hA
    exact smul_one_inj hd hA
  · obtain ⟨hA, hν⟩ := h t ht
    refine ⟨?_, hν⟩
    rw [ha _ (mul_pos hq0 ht).le, ha t ht.le, smul_smul, hA]

/-! ## (3) -/

/-- A family that is `λ`-covariant for every `λ > 0` is an isotropic cascade family of the affine
export (with a chosen action), and conversely. -/
theorem isFullyCovariant_iff_cascade (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsIsotropicFamily μ) :
    IsFullyCovariantLaws μ ↔ ∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily μ S := by
  constructor
  · intro hfull
    have hS : ∀ lam : ℝ, ∃ S : ℝ → ℝ, 0 < lam → IsCovariantAt μ lam S := by
      intro lam
      by_cases hl : 0 < lam
      · obtain ⟨S, hS⟩ := hfull lam hl
        exact ⟨S, fun _ => hS⟩
      · exact ⟨id, fun h => absurd h hl⟩
    choose S hS using hS
    refine ⟨S, ⟨hμ.1.1.isProbability, hμ.1.1.diag, hμ.1.1.cascade, hμ.1.1.continuous,
      fun Q hQ s t hs hst => hμ.2 s t hs hst Q hQ, fun lam hl => (hS lam hl).1,
      fun lam hl s t hs hst => ?_, hμ.1.2⟩⟩
    rw [push_smul_one_eq_map]
    exact (hS lam hl).2 s t hs hst
  · rintro ⟨S, hS⟩ lam hl
    refine ⟨S lam, hS.scale_bij lam hl, fun s t hs hst => ?_⟩
    rw [← push_smul_one_eq_map]
    exact hS.scale lam hl s t hs hst

/-- **`thm:lattice-strata`(3), full covariance.** The family is `λ`-covariant for every `λ > 0`
iff, in some gauge `χ`, `Ψ_t = F(χ(t) |·|)` with `F ∈ 𝒜_d`. -/
theorem lattice_strata_3 (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsIsotropicFamily μ)
    (D : ℝ → SymLevyData d) (hD : ∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t)) :
    IsFullyCovariantLaws μ ↔
      ∃ χ F : ℝ → ℝ, IsGauge χ ∧ classA d F ∧
        ∀ t : ℝ, 0 ≤ t → ∀ ω : Rd d, (D t).exponent ω = F (χ t * ‖ω‖) := by
  have hsym := isotropicFamily_isSymmetricFamily μ hμ
  obtain ⟨-, hdiff⟩ := family_structure_data hd μ hsym D hD
  rw [isFullyCovariant_iff_cascade μ hμ, cited_A31 hd μ hsym.1.isProbability]
  constructor
  · rintro ⟨χ, F, hχ, hF, -, hrep⟩
    refine ⟨χ, F, hχ, hF, fun t ht ω => ?_⟩
    have h1 := (hD t ht ω).symm.trans (hrep 0 t le_rfl ht ω)
    rw [hχ.1, zero_mul, classA_zero hF, sub_zero] at h1
    have h2 := Real.exp_injective (Complex.ofReal_injective h1)
    linarith
  · rintro ⟨χ, F, hχ, hF, hexp⟩
    have hχnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ χ t := fun t ht => by
      have := hχ.2.1.monotoneOn (self_mem_Ici) ht ht
      rw [hχ.1] at this
      exact this
    refine ⟨χ, F, hχ, hF, ?_, fun s t hs hst ω => ?_⟩
    · -- `F ≢ 0`: otherwise `μ_1 = δ₀`
      by_contra hcon
      push Not at hcon
      haveI := hsym.1.isProbability 0 1 le_rfl zero_le_one
      refine hμ.1.2 0 1 le_rfl zero_lt_one (eq_dirac_of_charFun_one fun ω => ?_)
      rw [hD 1 zero_le_one ω, hexp 1 zero_le_one ω,
        hcon _ (mul_nonneg (hχnn 1 zero_le_one) (norm_nonneg ω))]
      simp
    · rw [(hdiff s t hs hst).1 ω, hexp t (hs.trans hst) ω, hexp s hs ω]

end Pyramids
