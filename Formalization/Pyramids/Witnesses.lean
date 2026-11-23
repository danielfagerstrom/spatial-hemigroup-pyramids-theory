/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.LatticeStrata
import Pyramids.Matern.MaternPyramid
import Pyramids.Matern.MaternDensity
import Pyramids.Matern.MaternMixture
import Pyramids.Matern.MaternProjections
import Pyramids.Matern.MaternGenerator
import Pyramids.Matern.MaternLimit
import Pyramids.Matern.SelectionStage
import Pyramids.Matern.SelectionGauge
import Pyramids.Matern.SelectionFree
import Pyramids.Price.FrameMatern
import Pyramids.Price.GridKnot
import Pyramids.Price.NotIsotropic
import Pyramids.Price.ExactMasks
import Pyramids.Pyramid.StratumTwoExample
import Pyramids.Line.LatticeLineStrict
import Pyramids.Cited.A4
import Pyramids.LineAppendix.MaternLine
import Pyramids.LineAppendix.MaternNonCreation
import Pyramids.DiscreteHelmholtz
import Pyramids.Pyramid.WhatDoesNotLiftChain
import Pyramids.Matern.IncrementsThorin
import Pyramids.Pyramid.LadderStratum
import Pyramids.Pyramid.LadderClassA
import AffineHemigroup.GaussVar
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Pyramids.Price.ResolventMask
import Pyramids.Price.ResolventInstances

/-!
# Witnesses: the headline theorems' hypotheses are jointly satisfiable

The fidelity review's P1 (`blueprint/PLAN-fidelity-review.md` § 2 item 2, § 5; ledger row R21 of
`blueprint/REVIEW-fidelity.md`). Each `witness_<target>_<model>` instantiates **all** the
hypotheses of one headline declaration at once, at a named model, so that no headline theorem is
true only because nothing meets its hypotheses (F1). They are named theorems, not `example`s, so
that `CIAxiomGuard.lean` prints their axioms. Nothing in the development imports this file but the
root `Pyramids.lean`; nothing cites it.

The account per target and per model, with what is not witnessed and why, is
`records/pyramids/FIDELITY-witnesses.md`. In short ("core": `#print axioms` shows `propext`,
`Classical.choice`, `Quot.sound` only; "ledger": admitted names of `trust-boundary.txt`):

## The models

* **The Gaussian (heat) family** `gaussFamily d`, `μ_{s,t} = N(0, 2(t² - s²)I)`, data
  `(t²I, 0)`; built here, core. On the line, `heatLine` and the cascade family `heatCascade`
  (core).
* **The Matérn pyramid** `maternPyr`, chosen from `matern_pyramid_1_exists`: ledger (A39's
  `levy_khintchine_*` and A35's `sato_polar_criterion`, `selfDecomposable_infinitelyDivisible`,
  through the membership `F_q ∈ 𝒜_d`). It meets every target for **every** `q > 1`, `c > 0`,
  `d ≥ 1`; no target needs a narrower range. The concrete `(q, c, d) = (2, 1, 2)` is
  `witness_matern_pyramid_1_family_matern_2_1_2`.
* **A family at one ratio only**: in `ℝ^d` the example of `prop:stratum-two-example`
  (`witness_lattice_strata_2_stratumTwo`), on the line `lattice_line_strict`; both ledger.
* **The frame Matérn mask** `(λ^L_{1/2})^{⊗d}` on the lattice `stdLattice d = ℤ^d` (core) and a
  family carrying it (ledger: A39, A42, and A48 for the mask's infinite divisibility).

## Per target

* `thm:lattice-strata`: (1), its converse, (2), (3), every hypothesis at the Gaussian family, with
  both sides of the equivalences of (2) and (3) true; core. (2) and (3) at a family covariant at
  one ratio only (the left side of (3) false): ledger.
* `thm:matern-pyramid`: `IsMaternPyramid` for (1)–(5) (ledger); the mixture's probability space
  `Exp(1)^{⊗ℕ} ⊗ N(0, I)` (core); the functional equation of (2) at `F_q` (core); the family of
  (2), the Matérn pyramid itself as `μ'` (ledger); (3) at the signal `f = 0` in every `d ≥ 1`, and
  at the nonzero signal `e^{-⟨e₀,x⟩²}` in `d = 1` (ledger for the pyramid, core for the signal);
  the laws of (5) and the family over `q` that its last clause quantifies over (ledger).
* `thm:selection-stratum-two`: (1) at the Matérn pyramid (principle and representation, ledger)
  and at the Gaussian family (principle fails, core); (2) and its converse with `χ = id` (ledger);
  (3) with both outcomes, `t = qs` and `t = q²s` (ledger); (4)'s laws, core.
* `prop:grid-pyramid-not-isotropic` (1), (2) and `prop:exact-masks`: the frame Matérn mask on
  `ℤ^d` and a carrying family (ledger); the premise `span (supp w) = ℝ^d` of (2)'s second half at
  that mask (core); (3)'s ranges (core).
* Tier 0 (R21): `CascadeFamily` (the heat family, core); self-decomposable and
  semi-selfdecomposable laws (`N(0, 2I)`, core); the pure-Gaussian origin datum (core);
  `IsKnotExponent` (`ω²`, core); `IsKnotLadder` (Gaussian and Matérn ladders, core);
  `IsIsotropicCarrier` (Gaussian core, Matérn ledger); `stencilFamily (gridLap h)`
  (`helmKernel`, core); `maskPowers` (core); `IsExactSubsampleIn`, `IsExactSampleArray` (core,
  degenerate members).

## Not witnessed here

* `matern_pyramid_3_counts` at a nonzero signal in `d ≥ 2`: only `d = 1` is built, where the
  projection along `e₀` is a measure-preserving equivalence. In `d ≥ 2` it needs Fubini on `ℝ^d`.
* `IsExactSubsampleIn`, `IsExactSampleArray` at a non-degenerate member: `δ₀` and the indicator
  of `{0}` only. No member of `stencilFamily (gridLap h)` is witnessed exactly subsampled, which
  is consistent with the negative results of `SubsamplingGrid.lean`, `SubsamplingRatio.lean`.
* A family with the principle at one octave stage but not at all of them
  (`selection_stratum_two_1_free`'s second family): its stages are not computed here.
* No Matérn pyramid and no exact grid pyramid is built without the ledger: both need the
  existence of an infinitely divisible law from its exponent.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology SchwartzMap

variable {d : ℕ}

/-! ## The Gaussian (heat) family in `ℝ^d` -/

/-- **The Gaussian family**: `μ_{s,t} = N(0, 2(t² - s²) I)`, with transform
`exp(-(t² - s²)|ω|²)` for `s² ≤ t²`. -/
noncomputable def gaussFamily (d : ℕ) (s t : ℝ) : Measure (Rd d) :=
  gaussVar d (2 * (t ^ 2 - s ^ 2))

instance isProbabilityMeasure_gaussFamily (d : ℕ) (s t : ℝ) :
    IsProbabilityMeasure (gaussFamily d s t) :=
  isProbabilityMeasure_gaussVar d _

theorem charFun_gaussFamily {s t : ℝ} (h : s ^ 2 ≤ t ^ 2) (ω : Rd d) :
    charFun (gaussFamily d s t) ω = ((Real.exp (-(t ^ 2 * ‖ω‖ ^ 2 - s ^ 2 * ‖ω‖ ^ 2)) : ℝ) : ℂ) := by
  rw [gaussFamily, charFun_gaussVar (by linarith)]
  congr 2
  ring

theorem sq_le_sq_of_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : s ^ 2 ≤ t ^ 2 :=
  pow_le_pow_left₀ hs hst 2

/-- **The data of the Gaussian family**: `(t² I, 0)`. -/
noncomputable def gaussData (d : ℕ) (t : ℝ) : SymLevyData d where
  A := t ^ 2 • (1 : Mat d)
  ν := 0
  A_posSemidef := Matrix.PosSemidef.one.smul (sq_nonneg t)
  ν_zero := rfl
  ν_integrable := by simp
  ν_symm := by simp

theorem gaussData_exponent (t : ℝ) (ω : Rd d) :
    (gaussData d t).exponent ω = t ^ 2 * ‖ω‖ ^ 2 := by
  simp [SymLevyData.exponent, pairExponent, gaussData, AffineHemigroup.quad_smul, quad_one]

theorem isSymData_gaussFamily (t : ℝ) :
    IsSymData (gaussFamily d 0 t) (gaussData d t) := fun ω => by
  rw [charFun_gaussFamily (by nlinarith) ω, gaussData_exponent]
  congr 3
  ring

theorem gaussFamily_map_smul {lam : ℝ} (s t : ℝ) (h : s ^ 2 ≤ t ^ 2) :
    (gaussFamily d s t).map (fun x => lam • x) = gaussFamily d (lam * s) (lam * t) := by
  haveI : IsProbabilityMeasure ((gaussFamily d s t).map fun x => lam • x) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  have h' : (lam * s) ^ 2 ≤ (lam * t) ^ 2 := by
    rw [mul_pow, mul_pow]; exact mul_le_mul_of_nonneg_left h (sq_nonneg lam)
  rw [charFun_map_smul, charFun_gaussFamily h, charFun_gaussFamily h', norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  congr 3
  ring

/-- **The Gaussian family is an isotropic family in dimension `d ≥ 1`.** Lean core. -/
theorem isIsotropicFamily_gaussFamily (hd : 1 ≤ d) : IsIsotropicFamily (gaussFamily d) := by
  refine ⟨⟨⟨fun s t _ _ => inferInstance, fun t _ => ?_, fun r s t hr hrs hst => ?_,
    fun ω => ?_⟩, fun s t hs hst heq => ?_⟩, fun s t hs hst Q hQ => ?_⟩
  · exact eq_dirac_of_charFun_one fun ω => by
      rw [charFun_gaussFamily le_rfl, sub_self, neg_zero, Real.exp_zero, Complex.ofReal_one]
  · refine Measure.ext_of_charFun (funext fun ω => ?_)
    have h1 := sq_le_sq_of_le hr (hrs.trans hst)
    have h2 := sq_le_sq_of_le (hr.trans hrs) hst
    have h3 := sq_le_sq_of_le hr hrs
    rw [charFun_conv, charFun_gaussFamily h1, charFun_gaussFamily h2, charFun_gaussFamily h3,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  · have hc : ContinuousOn (fun p : ℝ × ℝ =>
        ((Real.exp (-(p.2 ^ 2 * ‖ω‖ ^ 2 - p.1 ^ 2 * ‖ω‖ ^ 2)) : ℝ) : ℂ))
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := by fun_prop
    exact hc.congr fun p hp => charFun_gaussFamily (sq_le_sq_of_le hp.1 hp.2) ω
  · set e : Rd d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1
    have he : ‖e‖ = 1 := by simp [e]
    have h := charFun_gaussFamily (d := d) (sq_le_sq_of_le hs hst.le) e
    rw [heq, charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero, he]
      at h
    have h2 : Real.exp (-(t ^ 2 * 1 ^ 2 - s ^ 2 * 1 ^ 2)) = 1 := by exact_mod_cast h.symm
    have h3 := (Real.exp_eq_one_iff _).1 h2
    nlinarith
  · haveI : IsProbabilityMeasure (push Q (gaussFamily d s t)) :=
      Measure.isProbabilityMeasure_map (lin Q).continuous.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    have h := sq_le_sq_of_le hs hst
    rw [push, charFun_map_lin, charFun_gaussFamily h, charFun_gaussFamily h,
      norm_lin_of_orth (transpose_mem_orthSet hQ)]

/-- **The Gaussian family is `λ`-covariant with `S_λ t = λt`, for every `λ > 0`.** Lean core. -/
theorem isCovariantAt_gaussFamily {lam : ℝ} (hlam : 0 < lam) :
    IsCovariantAt (gaussFamily d) lam (fun t => lam * t) :=
  ⟨isIncreasingBijection_mul hlam, fun s t hs hst =>
    gaussFamily_map_smul s t (sq_le_sq_of_le hs hst)⟩

theorem isFullyCovariantLaws_gaussFamily : IsFullyCovariantLaws (gaussFamily d) :=
  fun _ hlam => ⟨_, isCovariantAt_gaussFamily hlam⟩

theorem gaussData_A (t : ℝ) : (gaussData d t).A = t ^ 2 • (1 : Mat d) := rfl

theorem isInfinitelyDivisible_gaussFamily {s t : ℝ} (h : s ^ 2 ≤ t ^ 2) :
    IsInfinitelyDivisible (gaussFamily d s t) :=
  isInfinitelyDivisible_gaussian (Matrix.PosSemidef.one.smul (by linarith))

/-! ### The pure-Gaussian profile, origin datum and law of the class `𝒜_d` -/

/-- **The pure-Gaussian profile on the line**: `a = 1`, `k = 0`, exponent `ω²`. -/
noncomputable def gaussProfile : ScaleSpace.SDProfile where
  a := 1
  k := 0
  a_nonneg := zero_le_one
  k_nonneg := fun _ _ => le_rfl
  k_antitone := fun _ _ _ _ _ => le_rfl
  k_zero := rfl
  integrable_near_zero := by simp
  integrable_at_top := by simp

theorem gaussProfile_exponent (ω : ℝ) : gaussProfile.exponent ω = ω ^ 2 := by
  simp [ScaleSpace.SDProfile.exponent, ScaleSpace.SDProfile.exponentL, gaussProfile, sq_nonneg]

/-- **The pure-Gaussian origin datum**: `a = 2`, `k ≡ 0`, exponent `|ξ|²`. -/
noncomputable def gaussOriginDatum (d : ℕ) : OriginDatum d where
  a := 2
  k := 0
  a_nonneg := zero_le_two
  k_nonneg := fun _ _ => le_rfl
  k_antitone := fun _ _ _ _ _ => le_rfl
  integrable_near_zero := by simp
  integrable_at_top := by simp

theorem gaussOriginDatum_exponent (ξ : Rd d) : (gaussOriginDatum d).exponent ξ = ‖ξ‖ ^ 2 := by
  simp [OriginDatum.exponent, OriginDatum.exponentL, OriginDatum.levyMeasure, gaussOriginDatum]

/-- **The Gaussian `N(0, 2I)` is self-decomposable** (the shared core's form): for `c ∈ (0,1)`,
`μ = D_c μ ∗ N(0, 2(1 - c²)I)`. Lean core. -/
theorem isSelfDecomposable_gaussFamily_one :
    ScaleSpace.IsSelfDecomposable (gaussFamily d 0 1) := by
  intro c hc0 hc1
  refine ⟨gaussFamily d c 1, inferInstance, ?_⟩
  have hc2 : c ^ 2 ≤ 1 ^ 2 := by nlinarith
  haveI : IsProbabilityMeasure ((gaussFamily d 0 1).map (c • ·)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_conv, charFun_map_smul, charFun_gaussFamily (by norm_num),
    charFun_gaussFamily (by norm_num), charFun_gaussFamily hc2, ← Complex.ofReal_mul,
    ← Real.exp_add, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  congr 3
  ring

/-- **The Gaussian `N(0, 2I)` is self-decomposable at Sato's letter**: for `b > 1` the residual
is `N(0, 2(1 - b⁻²)I)`. Lean core. -/
theorem isSelfDecomposableSato_gaussFamily_one :
    IsSelfDecomposableSato (gaussFamily d 0 1) := by
  intro b hb
  refine ⟨gaussFamily d b⁻¹ 1, inferInstance, fun z => ?_⟩
  have hb2 : b⁻¹ ^ 2 ≤ 1 ^ 2 := by
    have : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
    have : 0 < b⁻¹ := inv_pos.2 (by linarith)
    nlinarith
  rw [charFun_gaussFamily (by norm_num), charFun_gaussFamily (by norm_num),
    charFun_gaussFamily hb2, ← Complex.ofReal_mul, ← Real.exp_add, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  congr 3
  ring

/-- **The Gaussian `N(0, 2I)` is semi-selfdecomposable with every span `b > 1`**, with the
infinitely divisible residual `N(0, 2(1 - b⁻²)I)`. Lean core. -/
theorem isSemiSelfDecomposableWithSpan_gaussFamily_one {b : ℝ} (hb : 1 < b) :
    IsSemiSelfDecomposableWithSpan b (gaussFamily d 0 1) := by
  obtain ⟨ρ, -, -⟩ := isSelfDecomposableSato_gaussFamily_one (d := d) b hb
  have hb2 : b⁻¹ ^ 2 ≤ 1 ^ 2 := by
    have : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
    have : 0 < b⁻¹ := inv_pos.2 (by linarith)
    nlinarith
  refine ⟨hb, gaussFamily d b⁻¹ 1, ⟨inferInstance, fun z => ?_⟩,
    isInfinitelyDivisible_gaussFamily hb2⟩
  rw [charFun_gaussFamily (by norm_num), charFun_gaussFamily (by norm_num),
    charFun_gaussFamily hb2, ← Complex.ofReal_mul, ← Real.exp_add, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  congr 3
  ring

/-- **`F(r) = r²` is in `𝒜_d`**: the pure-Gaussian profile, and the law `N(0, 2I)`. Lean core. -/
theorem classA_sq : classA d (fun r => r ^ 2) := by
  refine ⟨⟨gaussProfile, fun r _ => (gaussProfile_exponent r).symm⟩, gaussFamily d 0 1,
    inferInstance, isSelfDecomposable_gaussFamily_one, fun ξ => ?_⟩
  rw [charFun_gaussFamily (by norm_num)]
  congr 3
  ring

/-! ## Witnesses of `thm:lattice-strata` -/

/-- **Witness, `thm:lattice-strata`(1), the direct half (`lattice_strata_1`)**, at the Gaussian
family with the data `(t² I, 0)`, `a(t) = t²`: every hypothesis at once, in every `d ≥ 1`. Lean
core. -/
theorem witness_lattice_strata_1_gauss (hd : 1 ≤ d) :
    IsIsotropicFamily (gaussFamily d) ∧
      (∀ t : ℝ, 0 ≤ t → IsSymData (gaussFamily d 0 t) (gaussData d t)) ∧
      ∀ t : ℝ, 0 ≤ t → (gaussData d t).A = (fun t : ℝ => t ^ 2) t • (1 : Mat d) :=
  ⟨isIsotropicFamily_gaussFamily hd, fun t _ => isSymData_gaussFamily t, fun t _ => gaussData_A t⟩

/-- **Witness, `thm:lattice-strata`(1), the converse (`lattice_strata_1_converse`)**, at the data
`(t² I, 0)`: the hypotheses at once, and the laws the conclusion asserts exist, the Gaussian family,
built here with no ledger entry (the declaration itself builds them from A39(iii)). Lean core. -/
theorem witness_lattice_strata_1_converse_gauss :
    (∀ t : ℝ, 0 ≤ t → (gaussData d t).A = (fun t : ℝ => t ^ 2) t • (1 : Mat d)) ∧
      (∀ t : ℝ, 0 ≤ t → IsRotationInvariant (gaussData d t).ν) ∧
      (∀ s t : ℝ, 0 ≤ s → s < t →
        (fun t : ℝ => t ^ 2) s ≤ (fun t : ℝ => t ^ 2) t ∧ (gaussData d s).ν ≤ (gaussData d t).ν ∧
          ((fun t : ℝ => t ^ 2) s, (gaussData d s).ν) ≠ ((fun t : ℝ => t ^ 2) t, (gaussData d t).ν)) ∧
      (∀ ω : Rd d, ContinuousOn (fun t => (gaussData d t).exponent ω) (Ici 0)) ∧
      IsExponentLaws (fun t ω => (gaussData d t).exponent ω) (gaussFamily d) := by
  refine ⟨fun t _ => gaussData_A t, fun t _ Q _ => ?_, fun s t hs hst => ?_, fun ω => ?_,
    fun s t hs hst => ⟨inferInstance, fun ω => ?_⟩⟩
  · simp [gaussData, push]
  · have h : s ^ 2 < t ^ 2 := by nlinarith
    refine ⟨h.le, le_rfl, fun he => h.ne ?_⟩
    exact congrArg Prod.fst he
  · simp_rw [gaussData_exponent]
    fun_prop
  · rw [charFun_gaussFamily (sq_le_sq_of_le hs hst)]
    simp only [gaussData_exponent]

/-- **Witness, `thm:lattice-strata`(2) (`lattice_strata_2`)**, at the Gaussian family and any
`q > 1`: the hypotheses at once, and both sides of the equivalence hold (`q`-covariance with
`S_q t = qt`; `a(qt) = q² a(t)`, `ν_{qt} = D_q ν_t`), so the equivalence is not vacuous on either
side. Lean core. -/
theorem witness_lattice_strata_2_gauss (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    (IsIsotropicFamily (gaussFamily d) ∧
      (∀ t : ℝ, 0 ≤ t → IsSymData (gaussFamily d 0 t) (gaussData d t)) ∧
      (∀ t : ℝ, 0 ≤ t → (gaussData d t).A = (fun t : ℝ => t ^ 2) t • (1 : Mat d)) ∧ 1 < q) ∧
      IsCovariantAt (gaussFamily d) q (fun t => q * t) ∧
      ∀ t : ℝ, 0 < t → (fun t : ℝ => t ^ 2) (q * t) = q ^ 2 * (fun t : ℝ => t ^ 2) t ∧
        (gaussData d (q * t)).ν = (gaussData d t).ν.map (fun x => q • x) := by
  refine ⟨⟨(witness_lattice_strata_1_gauss hd).1, (witness_lattice_strata_1_gauss hd).2.1,
    (witness_lattice_strata_1_gauss hd).2.2, hq⟩, isCovariantAt_gaussFamily (by linarith),
    fun t _ => ⟨by ring, by simp [gaussData]⟩⟩

/-- **Witness, `thm:lattice-strata`(3) (`lattice_strata_3`)**, at the Gaussian family: the
hypotheses at once, and both sides of the equivalence hold, with the gauge `χ = id` and
`F(r) = r² ∈ 𝒜_d`. Lean core. -/
theorem witness_lattice_strata_3_gauss (hd : 1 ≤ d) :
    (IsIsotropicFamily (gaussFamily d) ∧
      ∀ t : ℝ, 0 ≤ t → IsSymData (gaussFamily d 0 t) (gaussData d t)) ∧
      IsFullyCovariantLaws (gaussFamily d) ∧
      IsGauge id ∧ classA d (fun r => r ^ 2) ∧
        ∀ t : ℝ, 0 ≤ t → ∀ ω : Rd d, (gaussData d t).exponent ω = (fun r : ℝ => r ^ 2) (id t * ‖ω‖) := by
  refine ⟨⟨(witness_lattice_strata_1_gauss hd).1, (witness_lattice_strata_1_gauss hd).2.1⟩,
    isFullyCovariantLaws_gaussFamily, ⟨rfl, strictMonoOn_id, fun y hy => ⟨y, hy, rfl⟩⟩, classA_sq,
    fun t _ ω => ?_⟩
  rw [gaussData_exponent]
  simp only [id]
  ring

/-! ## The Matérn pyramid -/

section Matern

variable {q c : ℝ}

/-- **A Matérn pyramid with the constants `q`, `c` in dimension `d`**, chosen from
`matern_pyramid_1_exists`. -/
noncomputable def maternPyr (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) : ℝ → ℝ → Measure (Rd d) :=
  (matern_pyramid_1_exists hd hq hc).choose

theorem isMaternPyramid_maternPyr (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) :
    IsMaternPyramid q c (maternPyr hd hq hc) :=
  (matern_pyramid_1_exists hd hq hc).choose_spec

theorem charFun_maternPyr_zero (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t)
    (ω : Rd d) :
    charFun (maternPyr hd hq hc 0 t) ω =
      ((Real.exp (-maternExponent q c (t * ‖ω‖)) : ℝ) : ℂ) := by
  rw [charFun_maternPyramid (isMaternPyramid_maternPyr hd hq hc) le_rfl ht, zero_mul,
    maternExponent_zero, sub_zero]

/-- The unit vector `e₀` of `ℝ^d`, `d ≥ 1`. -/
noncomputable def unitE0 (hd : 1 ≤ d) : Rd d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1

theorem norm_unitE0 (hd : 1 ≤ d) : ‖unitE0 hd‖ = 1 := by simp [unitE0]

/-- **Witness, `thm:matern-pyramid`(1) (`matern_pyramid_1_family`)**, and the hypothesis
`IsMaternPyramid q c μ` that `matern_pyramid_1_mixture`, `_3_marginal`, `_3_polya`, `_3_counts`,
`_4` and `selection_stratum_two_3` also take: a Matérn pyramid exists for every `q > 1`, `c > 0`,
`d ≥ 1`. Through `matern_pyramid_1_exists`, so through the ledger (`cited_A34` on `𝒜_d`
membership, `matern_pyramid_1_admissible`). -/
theorem witness_matern_pyramid_1_family_matern (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) :
    1 ≤ d ∧ 1 < q ∧ 0 < c ∧ IsMaternPyramid q c (maternPyr hd hq hc) :=
  ⟨hd, hq, hc, isMaternPyramid_maternPyr hd hq hc⟩

/-- **The concrete instance** `q = 2`, `c = 1`, `d = 2` of `witness_matern_pyramid_1_family_matern`. -/
theorem witness_matern_pyramid_1_family_matern_2_1_2 :
    IsMaternPyramid 2 1 (maternPyr (d := 2) (by norm_num) (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1)) :=
  isMaternPyramid_maternPyr _ _ _

/-- **Witness, `thm:matern-pyramid`(1), the mixture (`matern_pyramid_1_mixture`)**: the
probability space `(ℕ → ℝ) × ℝ^d` with the law `Exp(1)^{⊗ℕ} ⊗ N(0, I)`, the coordinates `X_i` and
the last factor `Z`, meets every hypothesis on `(Ω, P, X, Z)` at once (with the Matérn pyramid of
`witness_matern_pyramid_1_family_matern` for `μ`). The probability space is Lean core. -/
theorem witness_matern_pyramid_1_mixture_product :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ) (Z : Ω → Rd d),
      (∀ i, Measurable (X i)) ∧ Measurable Z ∧
      (∀ i, P.map (X i) = ProbabilityTheory.expMeasure 1) ∧
      P.map Z = ProbabilityTheory.stdGaussian (Rd d) ∧
      ProbabilityTheory.iIndepFun X P ∧
      ProbabilityTheory.IndepFun (fun ω i => X i ω) Z P := by
  haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure (r := 1) one_pos
  set E : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ProbabilityTheory.expMeasure 1
  set P : Measure ((ℕ → ℝ) × Rd d) := E.prod (ProbabilityTheory.stdGaussian (Rd d))
  have hX : ∀ i, Measurable fun ω : (ℕ → ℝ) × Rd d => ω.1 i := fun i => by fun_prop
  have hXlaw : ∀ i, P.map (fun ω : (ℕ → ℝ) × Rd d => ω.1 i) = ProbabilityTheory.expMeasure 1 := by
    intro i
    have : (fun ω : (ℕ → ℝ) × Rd d => ω.1 i) = (fun x : ℕ → ℝ => x i) ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply i) measurable_fst, Measure.map_fst_prod,
      measure_univ, one_smul, Measure.infinitePi_map_eval]
  refine ⟨(ℕ → ℝ) × Rd d, inferInstance, P, inferInstance, fun i ω => ω.1 i, fun ω => ω.2, hX,
    measurable_snd, hXlaw, ?_, ?_, ?_⟩
  · rw [Measure.map_snd_prod, measure_univ, one_smul]
  · rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map hX]
    simp_rw [hXlaw]
    have : (fun (ω : (ℕ → ℝ) × Rd d) (i : ℕ) => ω.1 i) = Prod.fst := rfl
    rw [this, Measure.map_fst_prod, measure_univ, one_smul]
  · exact ProbabilityTheory.indepFun_prod (X := id) (Y := id) measurable_id measurable_id

/-- **Witness, `thm:matern-pyramid`(2), the functional equation (`matern_pyramid_2_equation`)**:
`F̃ = F_q` itself meets every hypothesis (continuity on `[0,∞)`, `F̃(0) = 0`, the equation), for
every `q > 1`, `c > 0`. Lean core. -/
theorem witness_matern_pyramid_2_equation_matern (hq : 1 < q) (hc : 0 < c) :
    ContinuousOn (maternExponent q c) (Ici 0) ∧ maternExponent q c 0 = 0 ∧
      ∀ r : ℝ, 0 ≤ r → maternExponent q c (q * r) - maternExponent q c r =
        Real.log (1 + c ^ 2 * r ^ 2) :=
  ⟨(continuous_maternExponent hq hc).continuousOn, maternExponent_zero q c, fun r _ => by
    rw [maternExponent_mul_q hq hc]; ring_nf⟩

/-- **Witness, `thm:matern-pyramid`(2), the family (`matern_pyramid_2_family`)**: the Matérn
pyramid itself, as `μ'`, is an isotropic cascade family (with `S_λ t = λt`) whose knot kernels have
the transforms `exp(-F_q(q^n|ω|))`. Through the ledger, as `witness_matern_pyramid_1_family_matern`
and `matern_pyramid_1_family`. -/
theorem witness_matern_pyramid_2_family_matern (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) :
    IsMaternPyramid q c (maternPyr hd hq hc) ∧
      (∃ S : ℝ → ℝ → ℝ, IsIsotropicCascadeFamily (maternPyr hd hq hc) S) ∧
      ∀ (n : ℤ) (ω : Rd d), charFun (maternPyr hd hq hc 0 (q ^ n)) ω =
        ((Real.exp (-maternExponent q c (q ^ n * ‖ω‖)) : ℝ) : ℂ) := by
  have hμ := isMaternPyramid_maternPyr hd hq hc
  obtain ⟨hiso, hcov, -⟩ := matern_pyramid_1_family hd hq hc _ hμ
  refine ⟨hμ, (isFullyCovariant_iff_cascade _ hiso).1 fun lam hl => ⟨_, hcov lam hl⟩,
    fun n ω => charFun_maternPyr_zero hd hq hc (zpow_pos (by linarith) n).le ω⟩

/-- **Witness, `thm:matern-pyramid`(3) (`matern_pyramid_3_marginal`, `_3_polya`,
`_3_counts`)** at the Matérn pyramid, the unit vector `e₀`, and the signal `f = 0`, whose
projection `g = 0` is the primitive of `g' = 0`. Every hypothesis at once. The signal is the
degenerate member; a nonzero signal is `witness_matern_pyramid_3_counts_bump` (`d = 1`). Through the ledger, as `witness_matern_pyramid_1_family_matern`. -/
theorem witness_matern_pyramid_3_matern (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) :
    IsMaternPyramid q c (maternPyr hd hq hc) ∧ ‖unitE0 hd‖ = 1 ∧
      Integrable (0 : Rd d → ℝ) ∧ IsProjectionDensity (unitE0 hd) 0 0 ∧
      Integrable (0 : ℝ → ℝ) ∧ ∃ C : ℝ, ∀ x, (0 : ℝ → ℝ) x = C + ∫ y in (0 : ℝ)..x, (0 : ℝ → ℝ) y :=
  ⟨isMaternPyramid_maternPyr hd hq hc, norm_unitE0 hd, integrable_zero _ _ _,
    ⟨integrable_zero _ _ _, fun _ _ => by simp⟩, integrable_zero _ _ _, 0, fun _ => by simp⟩

/-- The Gaussian bump `e^{-y²}` on the line. -/
noncomputable def bump (y : ℝ) : ℝ := Real.exp (-1 * y ^ 2)

/-- Its derivative `-2y e^{-y²}`. -/
noncomputable def bump' (y : ℝ) : ℝ := -2 * (y * Real.exp (-1 * y ^ 2))

/-- The signal `x ↦ e^{-⟨e₀,x⟩²}` on `ℝ¹`. -/
noncomputable def bumpSignal (x : Rd 1) : ℝ := bump ⟪unitE0 le_rfl, x⟫

/-- On `ℝ¹`, `x ↦ ⟨e₀, x⟩` is the measure-preserving equivalence `ℝ¹ ≃ ℝ`. -/
noncomputable def lineEquiv : Rd 1 ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

theorem lineEquiv_eq_inner (x : Rd 1) : lineEquiv x = ⟪unitE0 le_rfl, x⟫ := by
  simp [lineEquiv, unitE0, EuclideanSpace.inner_single_left]

theorem measurePreserving_lineEquiv : MeasurePreserving lineEquiv :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1)).trans
    (volume_preserving_funUnique (Fin 1) ℝ)

/-- **Witness, `thm:matern-pyramid`(3) (`matern_pyramid_3_counts`) at a nonzero signal**, in
`d = 1`: the signal `f(x) = e^{-⟨e₀,x⟩²}` is integrable and nonzero, its projection along `e₀`
is `g = e^{-y²}`, and `g` is the primitive of the integrable `g' = -2y e^{-y²}`. Every hypothesis
at once; the Matérn half through the ledger, as `witness_matern_pyramid_1_family_matern`, the
signal half Lean core. In `d ≥ 2` the projection of a nonzero signal needs Fubini on `ℝ^d`,
which is not built here; the clause's hypotheses do not depend on `d` otherwise. -/
theorem witness_matern_pyramid_3_counts_bump (hq : 1 < q) (hc : 0 < c) :
    IsMaternPyramid q c (maternPyr (d := 1) le_rfl hq hc) ∧ ‖unitE0 (d := 1) le_rfl‖ = 1 ∧
      Integrable bumpSignal ∧ bumpSignal ≠ 0 ∧
      IsProjectionDensity (unitE0 le_rfl) bumpSignal bump ∧
      Integrable bump' ∧ ∃ C : ℝ, ∀ x, bump x = C + ∫ y in (0 : ℝ)..x, bump' y := by
  have hE := measurePreserving_lineEquiv
  have hsig : bumpSignal = bump ∘ lineEquiv := by
    funext x; simp [bumpSignal, lineEquiv_eq_inner]
  have hg : Integrable bump := integrable_exp_neg_mul_sq one_pos
  have hg' : Integrable bump' := (integrable_mul_exp_neg_mul_sq one_pos).const_mul (-2)
  refine ⟨isMaternPyramid_maternPyr le_rfl hq hc, norm_unitE0 le_rfl, ?_, ?_, ⟨hg, fun A _ => ?_⟩,
    hg', bump 0, fun x => ?_⟩
  · rw [hsig]; exact (hE.integrable_comp_emb lineEquiv.measurableEmbedding).2 hg
  · intro h
    have h0 := congrFun h 0
    simp [bumpSignal, bump] at h0
  · have hpre : (fun x : Rd 1 => ⟪unitE0 le_rfl, x⟫) ⁻¹' A = lineEquiv ⁻¹' A := by
      ext x; simp [lineEquiv_eq_inner]
    rw [hpre, hsig]
    exact (hE.setIntegral_preimage_emb lineEquiv.measurableEmbedding bump A).symm
  · have hderiv : ∀ y : ℝ, HasDerivAt bump (bump' y) y := by
      intro y
      have h := ((hasDerivAt_pow 2 y).const_mul (-1)).exp
      convert h using 1
      · rfl
      · simp only [bump']; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hg'.intervalIntegrable)]
    ring

/-- **Witness, `thm:matern-pyramid`(4) (`matern_pyramid_4`)** at the Matérn pyramid and the
Schwartz function `0`, at any `t > 0`; `matern_pyramid_4_series` takes only the ranges
`d ≥ 1`, `q > 1`, `c > 0`, `t > 0`. Through the ledger, as
`witness_matern_pyramid_1_family_matern`. -/
theorem witness_matern_pyramid_4_matern (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) :
    IsMaternPyramid q c (maternPyr hd hq hc) ∧ ∃ _ : 𝓢(Rd d, ℝ), ∃ t : ℝ, 0 < t :=
  ⟨isMaternPyramid_maternPyr hd hq hc, 0, 1, one_pos⟩

/-- **Witness, `thm:matern-pyramid`(5), weak convergence (`matern_pyramid_5_weak`)**: for every
`c > 0` and `t`, laws `ν q` with the exponents `ℓ F_q(t|·|)`, `q > 1`, and a law `ν₀` with the
exponent `Λ(t|·|)` exist, in every `d ≥ 1`. Through the ledger (`matern_pyramid_5_multiples`,
`matern_pyramid_5_classA`, which read A35). -/
theorem witness_matern_pyramid_5_weak_matern (hd : 1 ≤ d) (hc : 0 < c) (t : ℝ) :
    ∃ ν : ℝ → Measure (Rd d), (∀ q : ℝ, 1 < q → IsProbabilityMeasure (ν q) ∧ ∀ ω : Rd d,
      charFun (ν q) ω = ((Real.exp (-(Real.log q * maternExponent q c (t * ‖ω‖))) : ℝ) : ℂ)) ∧
      ∃ ν₀ : Measure (Rd d), IsProbabilityMeasure ν₀ ∧
        ∀ ω : Rd d, charFun ν₀ ω = ((Real.exp (-maternLimitExponent c (t * ‖ω‖)) : ℝ) : ℂ) := by
  have h1 : ∀ (q x : ℝ), maternExponent q c (|t| * x) = maternExponent q c (t * x) := by
    intro q x; simp only [maternExponent, mul_pow, sq_abs]
  have h2 : ∀ x : ℝ, maternLimitExponent c (|t| * x) = maternLimitExponent c (t * x) := by
    intro x; simp only [maternLimitExponent, mul_pow, sq_abs]
  have hν : ∀ q : ℝ, ∃ m : Measure (Rd d), 1 < q → IsProbabilityMeasure m ∧ ∀ ω : Rd d,
      charFun m ω = ((Real.exp (-(Real.log q * maternExponent q c (t * ‖ω‖))) : ℝ) : ℂ) := by
    intro q
    by_cases hq : 1 < q
    · obtain ⟨m, hm, hcf⟩ := (matern_pyramid_5_multiples hd hq hc).2 |t| (abs_nonneg t)
      exact ⟨m, fun _ => ⟨hm, fun ω => by rw [hcf ω, h1]⟩⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose ν hν using hν
  obtain ⟨-, μ₀, hμ₀, -, hcf₀⟩ := (matern_pyramid_5_classA hd hc).1
  haveI := hμ₀
  refine ⟨ν, hν, μ₀.map (fun x => t • x), Measure.isProbabilityMeasure_map (by fun_prop),
    fun ω => ?_⟩
  rw [charFun_map_smul, hcf₀, norm_smul, Real.norm_eq_abs, h2]

/-- **Witness, `thm:matern-pyramid`(5), the kernels (`matern_pyramid_5_kernels`)**: the family
of Matérn pyramids over `q > 1` that the last clause quantifies over exists, for every `c > 0`
and `d ≥ 1`, so that clause is not vacuous. Through the ledger, as
`witness_matern_pyramid_1_family_matern`. -/
theorem witness_matern_pyramid_5_kernels_matern (hd : 1 ≤ d) (hc : 0 < c) :
    ∃ μ : ℝ → ℝ → ℝ → Measure (Rd d), ∀ q : ℝ, 1 < q → IsMaternPyramid q c (μ q) := by
  classical
  refine ⟨fun q => if hq : 1 < q then maternPyr hd hq hc else fun _ _ => 0, fun q hq => ?_⟩
  simp only [dif_pos hq]
  exact isMaternPyramid_maternPyr hd hq hc

end Matern

/-! ## Witnesses of `thm:selection-stratum-two` -/

section Selection

variable {q c : ℝ}

theorem isIsotropicFamily_maternPyr (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) :
    IsIsotropicFamily (maternPyr hd hq hc) :=
  (matern_pyramid_1_family hd hq hc _ (isMaternPyramid_maternPyr hd hq hc)).1

theorem isCovariantAt_maternPyr (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) :
    IsCovariantAt (maternPyr hd hq hc) q (fun t => q * t) :=
  (matern_pyramid_1_family hd hq hc _ (isMaternPyramid_maternPyr hd hq hc)).2.1 q (by linarith)

theorem hasImplicitEulerPrinciple_maternPyr_octave (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c)
    {t : ℝ} (ht : 0 < t) : HasImplicitEulerPrinciple (maternPyr hd hq hc t (q * t)) :=
  ((selection_stratum_two_3 hd hq hc _ (isMaternPyramid_maternPyr hd hq hc)).1 t (q * t) ht
    (lt_mul_of_one_lt_left ht hq)).2 rfl

/-- **Witness, `thm:selection-stratum-two`(1) (`selection_stratum_two_1`,
`selection_stratum_two_1_ladder`)**, at the Matérn pyramid with the constants `q`, `c`, at any
`t > 0`: an isotropic `q`-covariant family in the canonical discrete gauge; the stage `μ_{t,qt}`
has the principle, and the representation with `τ = c²t²` holds, which is the hypothesis of the
ladder clause. So both sides of the equivalence hold here. Through the ledger, as
`witness_matern_pyramid_1_family_matern`. -/
theorem witness_selection_stratum_two_1_matern (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) {t : ℝ}
    (ht : 0 < t) :
    IsIsotropicFamily (maternPyr hd hq hc) ∧
      IsCovariantAt (maternPyr hd hq hc) q (fun t => q * t) ∧
      HasImplicitEulerPrinciple (maternPyr hd hq hc t (q * t)) ∧
      0 < c ^ 2 * t ^ 2 ∧ ∀ ω : Rd d, charFun (maternPyr hd hq hc 0 t) ω =
        ((Real.exp (-∑' n : ℕ,
          Real.log (1 + c ^ 2 * t ^ 2 * ‖ω‖ ^ 2 / q ^ (2 * (n + 1)))) : ℝ) : ℂ) := by
  refine ⟨isIsotropicFamily_maternPyr hd hq hc, isCovariantAt_maternPyr hd hq hc,
    hasImplicitEulerPrinciple_maternPyr_octave hd hq hc ht, by positivity, fun ω => ?_⟩
  rw [charFun_maternPyr_zero hd hq hc ht.le, maternExponent]
  congr 5
  funext n
  ring_nf

/-- **Witness, `thm:selection-stratum-two`(1) (`selection_stratum_two_1`), the other side**: the
Gaussian family meets the hypotheses (isotropic, `q`-covariant in the canonical discrete gauge)
and its stage `μ_{t,qt}` fails the principle, so the equivalence is not vacuous on its left side.
Through the ledger only by `selection_stratum_two_4_gaussian`. -/
theorem witness_selection_stratum_two_1_gauss (hd : 1 ≤ d) (hq : 1 < q) {t : ℝ} (ht : 0 < t) :
    IsIsotropicFamily (gaussFamily d) ∧ IsCovariantAt (gaussFamily d) q (fun t => q * t) ∧
      ¬ HasImplicitEulerPrinciple (gaussFamily d t (q * t)) := by
  refine ⟨isIsotropicFamily_gaussFamily hd, isCovariantAt_gaussFamily (by linarith), ?_⟩
  have h1 : t < q * t := lt_mul_of_one_lt_left ht hq
  have ha : 0 < (q * t) ^ 2 - t ^ 2 := by nlinarith
  exact selection_stratum_two_4_gaussian hd ha

/-- **Witness, `thm:selection-stratum-two`(2) (`selection_stratum_two_2`)**, at the Matérn pyramid
with `c = 1`: an isotropic `q`-covariant family in the canonical discrete gauge with the principle
at every octave stage `t ∈ [1, q)`. Through the ledger, as `witness_matern_pyramid_1_family_matern`. -/
theorem witness_selection_stratum_two_2_matern (hd : 1 ≤ d) (hq : 1 < q) :
    IsIsotropicFamily (maternPyr hd hq one_pos) ∧
      IsCovariantAt (maternPyr hd hq one_pos) q (fun t => q * t) ∧
      ∀ t : ℝ, 1 ≤ t → t < q → HasImplicitEulerPrinciple (maternPyr hd hq one_pos t (q * t)) :=
  ⟨isIsotropicFamily_maternPyr hd hq one_pos, isCovariantAt_maternPyr hd hq one_pos,
    fun _ ht _ => hasImplicitEulerPrinciple_maternPyr_octave hd hq one_pos (by linarith)⟩

/-- **Witness, `thm:selection-stratum-two`(2), the converse (`selection_stratum_two_2_converse`)**:
the gauge `χ = id ∈ 𝒢_q` (`isInGaugeGroup_id`, Lean core) and the Matérn pyramid with `c = 1`.
Through the ledger, as `witness_matern_pyramid_1_family_matern`. -/
theorem witness_selection_stratum_two_2_converse_matern (hd : 1 ≤ d) (hq : 1 < q) :
    IsInGaugeGroup q id ∧ IsMaternPyramid q 1 (maternPyr hd hq one_pos) :=
  ⟨isInGaugeGroup_id q, isMaternPyramid_maternPyr hd hq one_pos⟩

/-- **Witness, `thm:selection-stratum-two`(3) (`selection_stratum_two_3`)**: the hypothesis is the
Matérn pyramid's, and both outcomes of the equivalence occur, `t = qs` (the principle) and
`t = q²s` (no principle), at every `s > 0`. Through the ledger, as
`witness_matern_pyramid_1_family_matern`. -/
theorem witness_selection_stratum_two_3_matern (hd : 1 ≤ d) (hq : 1 < q) (hc : 0 < c) {s : ℝ}
    (hs : 0 < s) :
    IsMaternPyramid q c (maternPyr hd hq hc) ∧
      HasImplicitEulerPrinciple (maternPyr hd hq hc s (q * s)) ∧
      ¬ HasImplicitEulerPrinciple (maternPyr hd hq hc s (q * (q * s))) := by
  have h3 := (selection_stratum_two_3 hd hq hc _ (isMaternPyramid_maternPyr hd hq hc)).1
  have hqs : s < q * s := lt_mul_of_one_lt_left hs hq
  have hqqs : s < q * (q * s) := hqs.trans (lt_mul_of_one_lt_left (hs.trans hqs) hq)
  refine ⟨isMaternPyramid_maternPyr hd hq hc, hasImplicitEulerPrinciple_maternPyr_octave hd hq hc hs,
    fun h => ?_⟩
  have := (h3 s _ hs hqqs).1 h
  have := mul_left_cancel₀ (show q ≠ 0 by linarith) this
  linarith

/-- **The Laplace law along the axis `ℝe_j`**: the image of `L_r` on the line under
`x ↦ x e_j`, with transform `(1 + r²ω_j²)⁻¹`. -/
noncomputable def axisLaplace (d : ℕ) (j : Fin d) (r : ℝ) : Measure (Rd d) :=
  (ScaleSpace.laplaceLaw r).map fun x => x • ebasis j

theorem isProbabilityMeasure_axisLaplace (j : Fin d) {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (axisLaplace d j r) := by
  haveI := ScaleSpace.isProbabilityMeasure_laplaceLaw hr
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem charFun_axisLaplace (j : Fin d) {r : ℝ} (hr : 0 < r) (ω : Rd d) :
    charFun (axisLaplace d j r) ω = (((1 + r ^ 2 * ω j ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [← charFun_laplaceLaw_real hr, axisLaplace, charFun_apply, charFun_apply,
    integral_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp [ebasis, real_inner_smul_left, EuclideanSpace.inner_single_left, mul_comm]

/-- **Witness, `thm:selection-stratum-two`(4) (`selection_stratum_two_4_gaussian`,
`_4_frame`, `_4_axis`)** for `c, t > 0`: `a = 1 > 0`; the frame step, the tensor power of the
Laplace law `L_{ct}`, in `d ≥ 2`; and the axis pass, the Laplace law `L_{ct}` along `e_j`. Each
law exists with the transform the clause assumes. Lean core. -/
theorem witness_selection_stratum_two_4_laplace (hd : 2 ≤ d) (hc : 0 < c) {t : ℝ} (ht : 0 < t)
    (j : Fin d) :
    2 ≤ d ∧ (0 : ℝ) < 1 ∧
      (IsProbabilityMeasure (tensorPow d (ScaleSpace.laplaceLaw (c * t))) ∧
        ∀ ω : Rd d, charFun (tensorPow d (ScaleSpace.laplaceLaw (c * t))) ω =
          ((∏ j, (1 + c ^ 2 * t ^ 2 * ω j ^ 2)⁻¹ : ℝ) : ℂ)) ∧
      (IsProbabilityMeasure (axisLaplace d j (c * t)) ∧
        ∀ ω : Rd d, charFun (axisLaplace d j (c * t)) ω =
          (((1 + c ^ 2 * t ^ 2 * ω j ^ 2)⁻¹ : ℝ) : ℂ)) := by
  have hr : 0 < c * t := mul_pos hc ht
  haveI := ScaleSpace.isProbabilityMeasure_laplaceLaw hr
  refine ⟨hd, one_pos, ⟨(tensorPow_charFun (d := d)).1, fun ω => ?_⟩,
    ⟨isProbabilityMeasure_axisLaplace j hr, fun ω => ?_⟩⟩
  · rw [(tensorPow_charFun (d := d)).2 ω, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [charFun_laplaceLaw_real hr, mul_pow]
  · rw [charFun_axisLaplace j hr, mul_pow]

end Selection

/-! ## Witnesses of `prop:grid-pyramid-not-isotropic` and `prop:exact-masks` -/

section Grid

/-- **The lattice `ℤ^d`** as a `ℤ`-submodule of `ℝ^d`: the `ℤ`-span of the standard basis. Mathlib
supplies `DiscreteTopology` and `IsZLattice ℝ` for it. -/
noncomputable def stdLattice (d : ℕ) : Submodule ℤ (Rd d) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)

instance (d : ℕ) : DiscreteTopology (stdLattice d) := by
  unfold stdLattice; infer_instance

instance (d : ℕ) : IsZLattice ℝ (stdLattice d) := by
  unfold stdLattice; infer_instance

theorem gridSet_one_subset_stdLattice : gridSet d 1 ⊆ (stdLattice d : Set (Rd d)) := by
  rintro x ⟨n, rfl⟩
  rw [SetLike.mem_coe, stdLattice, Module.Basis.mem_span_iff_repr_mem]
  intro i
  refine ⟨n i, ?_⟩
  simp [latticePt]

/-- **The frame Matérn mask** `(λ^L_{1/2})^{⊗d}` on `ℤ^d`. -/
noncomputable def frameMask (d : ℕ) : Measure (Rd d) :=
  tensorPow d (gridLaw 1 (geomKernel (1 / 2)))

theorem isLatticeMask_frameMask (hd : 1 ≤ d) :
    IsLatticeMask (stdLattice d : Set (Rd d)) (frameMask d) := by
  obtain ⟨⟨hp, hs, hne, hnull⟩, -⟩ :=
    grid_pyramid_not_isotropic_3 (q := 2) hd one_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
  exact ⟨hp, hs, hne, measure_mono_null (compl_subset_compl.2 gridSet_one_subset_stdLattice) hnull⟩

theorem isExactLatticePyramid_frameMask (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    IsExactLatticePyramid q (frameMask d) :=
  (grid_pyramid_not_isotropic_3 hd one_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hq).2.1

/-- **A family carrying the frame Matérn pyramid**, chosen. -/
noncomputable def frameFamily (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) : ℝ → ℝ → Measure (Rd d) :=
  (isExactLatticePyramid_frameMask hd hq).choose

theorem carriesLatticeLadder_frameFamily (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    CarriesLatticeLadder q (frameMask d) (frameFamily hd hq) :=
  (isExactLatticePyramid_frameMask hd hq).choose_spec

/-- **Witness, `prop:grid-pyramid-not-isotropic`(1), (2) (`grid_pyramid_not_isotropic_1`,
`_2`)**, at the lattice `ℤ^d`, the frame Matérn mask `(λ^L_{1/2})^{⊗d}` and a family carrying it,
for every `q > 1` (`d ≥ 1` for (1); `_2` asks `d ≥ 2`). Every hypothesis at once. Through the
ledger: the exactness is `grid_pyramid_not_isotropic_3`, which reads A39(iii) (through
`prop:ladder-knot-kernel`(2)), A40, A42; the lattice is Lean core. -/
theorem witness_grid_pyramid_not_isotropic_frame (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    IsLatticeMask (stdLattice d : Set (Rd d)) (frameMask d) ∧
      CarriesLatticeLadder q (frameMask d) (frameFamily hd hq) :=
  ⟨isLatticeMask_frameMask hd, carriesLatticeLadder_frameFamily hd hq⟩

/-- **Witness, `prop:grid-pyramid-not-isotropic`(3) (`grid_pyramid_not_isotropic_3`)**: its
hypotheses are the ranges `d ≥ 1`, `h > 0`, `0 < a < 1`, `q > 1`, met at `h = 1`, `a = 1/2`,
`q = 2`. -/
theorem witness_grid_pyramid_not_isotropic_3_frame :
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧ (1 : ℝ) < 2 := by norm_num

/-- **Witness, `prop:exact-masks` (`exact_masks_1`, `exact_masks_1_poisson`, `exact_masks_2`)**,
at the lattice `ℤ^d` and the frame Matérn mask, for every `q > 1`: a symmetric probability law
`≠ δ₀`; carried by the lattice; infinitely divisible; with a Lévy measure; and its grid pyramid
exact. Every hypothesis at once. Through the ledger, as
`witness_grid_pyramid_not_isotropic_frame` (and `grid_pyramid_not_isotropic_1` for the infinite
divisibility and the Lévy measure: A39, A41, A42, A48). -/
theorem witness_exact_masks_frame (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    IsProbabilityMeasure (frameMask d) ∧ (frameMask d).map (fun x => -x) = frameMask d ∧
      frameMask d ≠ Measure.dirac 0 ∧
      IsLatticeMask (stdLattice d : Set (Rd d)) (frameMask d) ∧
      IsInfinitelyDivisible (frameMask d) ∧
      IsExactLatticePyramid q (frameMask d) ∧
      ∃ νw : Measure (Rd d), HasLevyMeasure (frameMask d) νw := by
  have hw := isLatticeMask_frameMask (d := d) hd
  obtain ⟨-, hid, ⟨νw, hνw, -⟩, -⟩ :=
    grid_pyramid_not_isotropic_1 (stdLattice d) (frameMask d) hw _
      (carriesLatticeLadder_frameFamily hd hq)
  exact ⟨hw.1, hw.2.1, hw.2.2.1, hw, hid, isExactLatticePyramid_frameMask hd hq, νw, hνw⟩

/-- The frame Matérn mask charges each point of `ℤ^d`: the weight of `n` is
`∏_j λ^L_{1/2}(n_j) > 0`. -/
theorem frameMask_singleton_ne_zero (n : Zd d) : frameMask d {latticePt 1 n} ≠ 0 := by
  have hpt : latticePt 1 n = WithLp.toLp 2 (fun i => (n i : ℝ)) := by simp [latticePt]
  rw [frameMask, tensorPow, Measure.map_apply (PiLp.continuous_toLp 2 _).measurable
    (measurableSet_singleton _), hpt]
  have hpre : (WithLp.toLp 2 : (Fin d → ℝ) → Rd d) ⁻¹' {WithLp.toLp 2 (fun i => (n i : ℝ))} =
      Set.univ.pi fun i => {(n i : ℝ)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ_pi]
    rw [← funext_iff]
    exact ⟨fun h => congrArg WithLp.ofLp h, fun h => h ▸ rfl⟩
  haveI := isProbabilityMeasure_geomMask (a := 1 / 2) (by norm_num) (by norm_num) 1
  rw [hpre, Measure.pi_pi, Finset.prod_ne_zero_iff]
  intro i _
  rw [gridLaw, Measure.sum_apply _ (measurableSet_singleton _)]
  refine (lt_of_lt_of_le ?_ (ENNReal.le_tsum (n i))).ne'
  rw [Measure.smul_apply, one_mul, Measure.dirac_apply_of_mem (Set.mem_singleton _), smul_eq_mul,
    mul_one]
  refine ENNReal.ofReal_pos.2 ?_
  unfold geomKernel
  positivity

/-- **Witness, the premise of `grid_pyramid_not_isotropic_2`'s second half**: the support of the
frame Matérn mask spans `ℝ^d`, since it holds every point of `ℤ^d`, the standard basis among them.
Lean core. -/
theorem witness_grid_pyramid_not_isotropic_2_span_frame :
    Submodule.span ℝ {x : Rd d | frameMask d {x} ≠ 0} = ⊤ := by
  rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  change frameMask d {_} ≠ 0
  rw [show ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis i : Rd d) =
      latticePt 1 (Pi.single i 1) from ?_]
  · exact frameMask_singleton_ne_zero _
  ext j
  by_cases hj : j = i
  · subst hj; simp [latticePt]
  · simp [latticePt, hj, Pi.single_apply]

end Grid

/-! ## Tier 0: members of the definitions (ledger row R21) -/

section Tier0

/-! ### A cascade family on the line: the heat family -/

/-- **The heat kernels on the line**: `κ_{s,t} = N(0, 2(t² - s²))`, transform
`exp(-(t²ω² - s²ω²))` for `s² ≤ t²`. -/
noncomputable def heatLine (s t : ℝ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (2 * (t ^ 2 - s ^ 2)).toNNReal

/-- The construction data `(χ, F) = (id, ω²)`. -/
noncomputable def heatData : ScaleSpace.ConstructionData :=
  constructionDataOf (fun t => t) gaussProfile isGauge_idFun

theorem isGaugeKernels_heatLine : IsGaugeKernels heatData heatLine := by
  refine ⟨fun _ _ => by unfold heatLine; infer_instance, fun s t => ?_, fun s t hs hst ω => ?_⟩
  · rw [ScaleSpace.IsSymmetric, heatLine, ProbabilityTheory.gaussianReal_map_neg, neg_zero]
  · have h : 0 ≤ 2 * (t ^ 2 - s ^ 2) := by nlinarith
    rw [heatLine, ProbabilityTheory.charFun_gaussianReal, Real.coe_toNNReal _ h]
    simp only [ScaleSpace.ConstructionData.expo, heatData, constructionDataOf,
      gaussProfile_exponent]
    push_cast
    congr 1
    ring_nf

/-- **The heat family on the line as a `CascadeFamily`**: (A1)–(A8) and (ND), with the kernels
`heatLine` and `S_λ t = λt`. -/
noncomputable def heatCascade : ScaleSpace.CascadeFamily :=
  isGaugeKernels_heatLine.cascadeFamily ⟨1, by
    simp [heatData, constructionDataOf, gaussProfile_exponent]⟩

/-- **Witness, `ScaleSpace.CascadeFamily` (T0.1, `def:q-covariant-line`)**: the heat family on the
line is a cascade family, fully covariant, represented by the kernels `N(0, 2(t² - s²))`, and
`q^ℤ`-covariant for every `q > 1` (`lattice_line_strict_imp`). -/
theorem witness_cascadeFamily_heat {q : ℝ} (hq : 1 < q) :
    ScaleSpace.IsKernelFamily heatCascade.Φ heatLine ∧ IsFullyCovariantLine heatCascade.Φ ∧
      (∃ S : ℝ → ℝ → ℝ, IsQCovariantLine q heatCascade.Φ S) ∧
      ∀ s t ω : ℝ, 0 ≤ s → s ≤ t →
        charFun (heatLine s t) ω = ((Real.exp (-(t ^ 2 * ω ^ 2 - s ^ 2 * ω ^ 2)) : ℝ) : ℂ) := by
  refine ⟨isGaugeKernels_heatLine.cascadeData.isKernelFamily, ⟨_, rfl⟩,
    lattice_line_strict_imp hq _ ⟨_, rfl⟩, fun s t ω hs hst => ?_⟩
  rw [isGaugeKernels_heatLine.charFun_eq s t hs hst ω]
  simp only [ScaleSpace.ConstructionData.expo, heatData, constructionDataOf, gaussProfile_exponent]
  ring_nf

/-- **Witness, a family at one ratio only, on the line (`def:q-covariant-line`)**: for every
`q > 1`, a `q^ℤ`-covariant family that is not fully covariant (`lattice_line_strict`, the
discrete-Gaussian pyramid). Through the ledger. -/
theorem witness_qCovariantLine_oneRatio {q : ℝ} (hq : 1 < q) :
    ∃ (Φ : ℝ → ℝ → (ScaleSpace.X →L[ℝ] ScaleSpace.X)) (S : ℝ → ℝ → ℝ),
      IsQCovariantLine q Φ S ∧ ¬ IsFullyCovariantLine Φ :=
  (lattice_line_strict hq).2

/-! ### Self-decomposable laws and the pure-Gaussian origin datum -/

/-- **Witness, `def:self-decomposable`, `def:semi-selfdecomposable` (T0.4, T0.14)**: the
Gaussian `N(0, 2I)` on `ℝ^d` is a probability law, self-decomposable (the shared core's form and
Sato's), and semi-selfdecomposable with every span `q > 1`. Lean core. -/
theorem witness_selfDecomposable_gauss {q : ℝ} (hq : 1 < q) :
    IsProbabilityMeasure (gaussFamily d 0 1) ∧ ScaleSpace.IsSelfDecomposable (gaussFamily d 0 1) ∧
      IsSelfDecomposableSato (gaussFamily d 0 1) ∧
      IsSemiSelfDecomposableWithSpan q (gaussFamily d 0 1) :=
  ⟨inferInstance, isSelfDecomposable_gaussFamily_one, isSelfDecomposableSato_gaussFamily_one,
    isSemiSelfDecomposableWithSpan_gaussFamily_one hq⟩

/-- **Witness, `def:isotropic-origin-data` (T0.3)**: the pure-Gaussian origin datum
`(a, k) = (2, 0)`, whose exponent is `|ξ|²`, the exponent of the law `N(0, 2I)`, which is in
`𝒜_d` with the pure-Gaussian profile on the line. Lean core. -/
theorem witness_originDatum_gauss :
    (gaussOriginDatum d).a = 2 ∧ (∀ r, (gaussOriginDatum d).k r = 0) ∧
      (∀ ξ : Rd d, (gaussOriginDatum d).exponent ξ = ‖ξ‖ ^ 2) ∧
      (∀ ξ : Rd d, charFun (gaussFamily d 0 1) ξ =
        ((Real.exp (-(gaussOriginDatum d).exponent ξ) : ℝ) : ℂ)) ∧
      classA d (fun r => r ^ 2) := by
  refine ⟨rfl, fun _ => rfl, gaussOriginDatum_exponent, fun ξ => ?_, classA_sq⟩
  rw [charFun_gaussFamily (by norm_num), gaussOriginDatum_exponent]
  congr 3
  ring_nf

/-! ### Knot exponents and ladders (`def:modulation-orbit`) -/

/-- `ω ↦ aω²`, `a ≥ 0`, is a symmetric Lévy exponent: the pair `(a, 0)`. -/
theorem isSymLevyExponent_sq {a : ℝ} (ha : 0 ≤ a) :
    ScaleSpace.IsSymLevyExponent (fun ω => a * ω ^ 2) :=
  ⟨⟨a, 0, ha, by simp [ScaleSpace.IsFolded], by simp⟩, fun ω => by
    simp [ScaleSpace.SymLevyPair.exponent, ScaleSpace.SymLevyPair.exponentL,
      mul_nonneg ha (sq_nonneg ω)]⟩

/-- **Witness, `IsKnotExponent` (T0.15)**: the Gaussian exponent `Ψ_1(ω) = ω²`, whose step is
`(q² - 1)ω²`, for every `q > 1`. Lean core. -/
theorem witness_isKnotExponent_gauss {q : ℝ} (hq : 1 < q) :
    IsKnotExponent q (fun ω => ω ^ 2) := by
  have hstep : knotStep q (fun ω => ω ^ 2) = fun ω => (q ^ 2 - 1) * ω ^ 2 := by
    funext ω; simp only [knotStep]; ring_nf
  have hq2 : 0 ≤ q ^ 2 - 1 := by nlinarith
  refine ⟨by simpa using isSymLevyExponent_sq zero_le_one, ?_, 1, ?_⟩
  · rw [hstep]; exact isSymLevyExponent_sq hq2
  · rw [hstep]; norm_num; nlinarith

/-- **Witness, `IsKnotLadder` (T0.15), the Gaussian ladder**: `L_n = N(0, 2(q² - 1)q^{2n})`.
Lean core. -/
theorem witness_isKnotLadder_gauss {q : ℝ} (hq : 1 < q) :
    IsKnotLadder q (fun ω => ω ^ 2) fun n : ℤ =>
      ProbabilityTheory.gaussianReal 0 (2 * (q ^ 2 - 1) * (q ^ n) ^ 2).toNNReal := by
  intro n
  refine ⟨inferInstance, fun ω => ?_⟩
  have h : 0 ≤ 2 * (q ^ 2 - 1) * (q ^ n) ^ 2 := by
    have : 0 ≤ q ^ 2 - 1 := by nlinarith
    positivity
  rw [ProbabilityTheory.charFun_gaussianReal, Real.coe_toNNReal _ h]
  simp only [knotStep]
  push_cast
  congr 1
  ring_nf

/-- **Witness, `IsKnotLadder` (T0.15), the Matérn ladder**: for `Ψ_1 = F_q` (constant `c`), the
step is `log(1 + c²ω²)` and the ladder is `L_n = L_{cq^n}`, the Laplace laws. Lean core. -/
theorem witness_isKnotLadder_matern {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    IsKnotLadder q (maternExponent q c) fun n : ℤ => ScaleSpace.laplaceLaw (c * q ^ n) := by
  intro n
  have hr : 0 < c * q ^ n := mul_pos hc (zpow_pos (by linarith) n)
  refine ⟨ScaleSpace.isProbabilityMeasure_laplaceLaw hr, fun ω => ?_⟩
  rw [charFun_laplaceLaw_eq_exp hr, knotStep, maternExponent_mul_q hq hc]
  congr 4
  ring_nf

/-! ### The isotropic carrier (`def:exact-grid-pyramid`) -/

theorem isSORotationInvariant_of_isotropic {μ : ℝ → ℝ → Measure (Rd d)} (hμ : IsIsotropicFamily μ)
    {t : ℝ} (ht : 0 ≤ t) : IsSORotationInvariant (μ 0 t) :=
  fun R hR _ => hμ.2 0 t le_rfl ht R hR

/-- **Witness, `IsIsotropicCarrier` (T0.18)**: the Gaussian family (Lean core) and, in every
`d ≥ 1` (so at `d ≥ 2`), the Matérn pyramid (through the ledger) have rotation-invariant
kernels. Neither carries a grid pyramid (`prop:grid-pyramid-not-isotropic`(2) forbids it in
`d ≥ 2`); the predicate is met by continuum families. -/
theorem witness_isIsotropicCarrier_gauss_matern (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q)
    (hc : 0 < c) :
    IsIsotropicCarrier (gaussFamily d) ∧ IsIsotropicCarrier (maternPyr hd hq hc) :=
  ⟨⟨1, one_pos, isSORotationInvariant_of_isotropic (isIsotropicFamily_gaussFamily hd) zero_le_one⟩,
    ⟨1, one_pos, isSORotationInvariant_of_isotropic (isIsotropicFamily_maternPyr hd hq hc)
      zero_le_one⟩⟩

/-! ### Grid families and the senses of exact (`def:grid-family`, `def:exact-senses`) -/

/-- **Witness, `stencilFamily (gridLap h)` (T0.17, R1)**: the discrete Helmholtz family
`helmKernel d h t γ = κ_t^{*γ}`, `t > 0`, `γ ≥ 1`, is a member, for `d ≥ 1`, `h > 0`. Lean core. -/
theorem witness_stencilFamily_helmKernel (hd : 1 ≤ d) {h t : ℝ} (hh : 0 < h) (ht : 0 < t)
    {γ : ℕ} (hγ : 1 ≤ γ) : helmKernel d h t γ ∈ stencilFamily (gridLap h) :=
  ⟨t, ht, γ, hγ, discreteHelmholtz d h t,
    ⟨(isProbKernel_discreteHelmholtz hd hh ht).2.1, discreteHelmholtz_eqn hd hh ht⟩, rfl⟩

/-- **Witness, `maskPowers` (T0.17)**: the two-step random walk `σ^{*2}` is a member of the grid
family of the random-walk mask `σ`. Lean core. -/
theorem witness_maskPowers_rwStep : kpow (rwStep (d := d)) 2 ∈ maskPowers (rwStep (d := d)) :=
  ⟨2, by norm_num, rfl⟩

theorem deltaZ_zsmul {q : ℕ} (hq : 2 ≤ q) (m : Zd d) : deltaZ ((q : ℤ) • m) = deltaZ m := by
  have : (q : ℤ) • m = 0 ↔ m = 0 := by
    constructor
    · intro h
      funext i
      have := congrFun h i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at this
      rcases this with h0 | h0
      · omega
      · exact h0
    · rintro rfl; funext i; simp
  unfold deltaZ
  exact if_congr this rfl rfl

/-- **Witness, `IsExactSubsampleIn` (T0.18)**: `δ₀` is exactly subsampled at every integer
`q ≥ 2` into the grid family `maskPowers δ₀`. The degenerate member: a non-degenerate one (a
nontrivial mask whose subsample is a member of a named family) is not built here. Lean core. -/
theorem witness_isExactSubsampleIn_deltaZ {q : ℕ} (hq : 2 ≤ q) :
    IsExactSubsampleIn (maskPowers (deltaZ (d := d))) q (deltaZ (d := d)) := by
  have hsum : ∑' m : Zd d, deltaZ ((q : ℤ) • m) = 1 := by
    simp_rw [deltaZ_zsmul hq]; exact tsum_deltaZ
  refine ⟨hq, by rw [hsum]; exact one_pos, 1, le_rfl, ?_⟩
  funext m
  rw [hsum, inv_one, one_mul, deltaZ_zsmul hq]
  simp [kpow, kconv_deltaZ_left]

/-- **Witness, `IsExactSampleArray` (T0.18)**: the "density" `1_{0}` sampled on `ℤ^d` gives the
array `δ₀` exactly. The degenerate member (the sampled function is not a probability density
of a continuum kernel); a sampled Gaussian or Matérn density is not built here. Lean core. -/
theorem witness_isExactSampleArray_indicator :
    IsExactSampleArray 1 (fun x : Rd d => if x = 0 then 1 else 0) (deltaZ (d := d)) := by
  have hpt : ∀ m : Zd d, (if latticePt 1 m = 0 then (1 : ℝ) else 0) = deltaZ m := by
    intro m
    have : latticePt 1 m = 0 ↔ m = 0 := by
      constructor
      · intro h
        funext i
        have := congrArg (fun x : Rd d => x i) h
        simpa [latticePt] using this
      · rintro rfl; ext i; simp [latticePt]
    unfold deltaZ
    exact if_congr this rfl rfl
  unfold IsExactSampleArray
  simp only [hpt]
  refine ⟨summable_deltaZ, by rw [tsum_deltaZ]; exact one_pos, fun n => by rw [tsum_deltaZ, div_one]⟩


/-! ### A family in `ℝ^d` covariant at one ratio only -/

/-- The weights `w_i = 1` for `i ≤ 0`, `0` for `i > 0`. -/
def stepWeights (i : ℤ) : ℝ := if i ≤ 0 then 1 else 0

/-- **Witness, `thm:lattice-strata`(2), (3) at a family covariant at one ratio only**: for every
`q > 1` and `d ≥ 1`, an isotropic family with data `(a(t)I, ν_t)` meeting the hypotheses of
`lattice_strata_2` and `_3`, `q`-covariant with `S_q t = qt`, and not `λ`-covariant for every
`λ > 0` (the example of `prop:stratum-two-example`, with the weights `stepWeights` and `h = 1`). So
the left side of (3) fails while that of (2) holds. Through the ledger (`stratum_two_example`,
`lem:synthesis`, `lem:family-structure`: A39). -/
theorem witness_lattice_strata_2_stratumTwo (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    ∃ (μ : ℝ → ℝ → Measure (Rd d)) (D : ℝ → SymLevyData d) (a : ℝ → ℝ),
      IsIsotropicFamily μ ∧ (∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t)) ∧
      (∀ t : ℝ, 0 ≤ t → (D t).A = a t • (1 : Mat d)) ∧
      IsCovariantAt μ q (fun t => q * t) ∧ ¬ IsFullyCovariantLaws μ := by
  have hq0 : 0 < q := by linarith
  have hw0 : ∀ i, 0 ≤ stepWeights i := fun i => by unfold stepWeights; split_ifs <;> norm_num
  have hwanti : Antitone stepWeights := fun i j hij => by
    unfold stepWeights; split_ifs <;> first | omega | norm_num
  have hwne : ∃ i, stepWeights i ≠ 0 := ⟨0, by simp [stepWeights]⟩
  have hneg : Summable fun i : {i : ℤ // i < 0} => stepWeights i * q ^ (2 * (i : ℤ)) := by
    have hg : Summable fun i : ℤ => if i < 0 then (q ^ 2)⁻¹ ^ i.natAbs else (0 : ℝ) := by
      rw [summable_int_iff_summable_nat_and_neg]
      have hr : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
      have hgeo := summable_geometric_of_lt_one (by positivity) hr
      refine ⟨summable_of_ne_finset_zero (s := ∅) fun n _ => by simp, ?_⟩
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeo
      · split_ifs <;> positivity
      · split_ifs
        · simp
        · positivity
    refine (hg.subtype {i : ℤ | i < 0}).congr fun ⟨i, hi⟩ => ?_
    have hi' : i < 0 := hi
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨i.natAbs, by omega⟩
    simp only [Function.comp_apply]
    rw [if_pos hi', stepWeights, if_pos hi'.le, one_mul,
      show (2 : ℤ) * -(k : ℤ) = -((2 * k : ℕ) : ℤ) by push_cast; ring_nf, zpow_neg, zpow_natCast,
      pow_mul, inv_pow, Int.natAbs_neg, Int.natAbs_natCast]
  have hpos : Summable fun i : {i : ℤ // 0 ≤ i} => stepWeights i := by
    refine summable_of_ne_finset_zero (s := {⟨0, le_rfl⟩}) fun ⟨i, hi⟩ hs => ?_
    have : i ≠ 0 := fun h => hs (by simp [h])
    simp [stepWeights, show ¬ i ≤ 0 by omega]
  obtain ⟨⟨D₀, hD₀⟩, -⟩ := stratum_two_example_data (d := d) hd hq one_pos stepWeights hw0 hwanti
    hwne hneg hpos
  obtain ⟨⟨μ, hμ⟩, hall⟩ := stratum_two_example hd hq one_pos stepWeights hw0 hwanti hwne hneg hpos
    D₀ hD₀
  obtain ⟨hiso, hcov, hnot, -⟩ := hall μ hμ
  have hsym := isotropicFamily_isSymmetricFamily μ hiso
  obtain ⟨D, hD⟩ := family_structure_exists hd μ hsym
  obtain ⟨a, ha⟩ := family_structure_isotropic hd μ hsym hiso.2 D hD
  exact ⟨μ, D, a, hiso, hD, fun t ht => (ha t ht).1, hcov, hnot⟩

end Tier0

/-! ### Witnesses owed by P3 and Tiers 2–3 (fidelity review, R51, R68) -/

section FixPhase

variable {d : ℕ} {q : ℝ}

/-- The polar Lévy measure of the zero profile is the zero measure. -/
theorem polarLevyMeasure_zeroProfile : polarLevyMeasure d (fun _ => 0) = 0 := by
  simp [polarLevyMeasure]

/-- **Witness, `prop:ladder-knot-kernel`(4)(b) (`ladder_knot_kernel_4b_equation`, `_4b_classA`,
`_4b_family`)** at a Gaussian step with `k = 0` (R51): the step `ϱ = N(0, 2(q² - 1)I)`, with
`a = 2(q² - 1)` and the zero polar profile, meets every hypothesis of the three declarations, with
the unit vector `e` and `F(r) = r²`, which is in `𝒜_d` (`classA_sq`). Lean core. -/
theorem witness_ladder_knot_kernel_4b_gauss (hd : 1 ≤ d) (hq : 1 < q) :
    gaussFamily d 1 q ≠ Measure.dirac 0 ∧ IsRotationInvariant (gaussFamily d 1 q) ∧
      0 ≤ 2 * (q ^ 2 - 1) ∧ Measurable (fun _ : ℝ => (0 : ℝ)) ∧
      ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂polarLevyMeasure d (fun _ => 0) ≠ ⊤ ∧
      (∀ ω : Rd d, charFun (gaussFamily d 1 q) ω = ((Real.exp (-(2 * (q ^ 2 - 1) / 2 * ‖ω‖ ^ 2 +
        ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂polarLevyMeasure d (fun _ => 0))) : ℝ) : ℂ)) ∧
      ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂polarLevyMeasure d (fun _ => 0) < ⊤ ∧
      ∃ e : Rd d, ‖e‖ = 1 ∧ ContinuousOn (fun r : ℝ => r ^ 2) (Set.Ici 0) ∧
        (fun r : ℝ => r ^ 2) 0 = 0 ∧
        (∀ r : ℝ, 0 ≤ r → (q * r) ^ 2 - r ^ 2 = radialExponent (gaussFamily d 1 q) e r) ∧
        classA d (fun r => r ^ 2) := by
  have hq2 : (1 : ℝ) ^ 2 ≤ q ^ 2 := by nlinarith
  have hcf : ∀ ω : Rd d, charFun (gaussFamily d 1 q) ω =
      ((Real.exp (-(2 * (q ^ 2 - 1) / 2 * ‖ω‖ ^ 2 +
        ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂polarLevyMeasure d (fun _ => 0))) : ℝ) : ℂ) := by
    intro ω
    rw [charFun_gaussFamily hq2, polarLevyMeasure_zeroProfile, integral_zero_measure]
    congr 2
    ring
  obtain ⟨e, he⟩ := exists_unit_Rd hd
  refine ⟨fun h => ?_, (isIsotropicFamily_gaussFamily hd).2 1 q zero_le_one (by linarith),
    by nlinarith, measurable_const, by simp [polarLevyMeasure_zeroProfile], hcf,
    by simp [polarLevyMeasure_zeroProfile], e, he, by fun_prop, by norm_num, fun r _ => ?_, classA_sq⟩
  · have h1 := charFun_gaussFamily (d := d) hq2 e
    rw [h, charFun_dirac] at h1
    have h2 := congrArg Complex.re h1
    simp only [Complex.ofReal_re] at h2
    have h3 : -(q ^ 2 * ‖e‖ ^ 2 - 1 ^ 2 * ‖e‖ ^ 2) < 0 := by rw [he]; nlinarith
    have := Real.exp_lt_exp.2 h3
    rw [Real.exp_zero] at this
    simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      Complex.one_re] at h2
    linarith
  · rw [radialExponent, charFun_gaussFamily hq2, Complex.ofReal_re, Real.log_exp, norm_smul, he,
      Real.norm_eq_abs, mul_one, sq_abs]
    ring

/-- **Witness, `prop:what-does-not-lift-chain`(1) (`what_does_not_lift_chain_1`)** (R51): the
exponent `Λ` of the limit law of `thm:matern-pyramid`(5), `c = 1`, is in `𝒜_d`, `d ≥ 1`
(`matern_pyramid_5_classA`), so the hypothesis `classA d F` is met, and the conclusion follows.
Through the ledger: the three Lévy–Khintchine names, `sato_polar_criterion`,
`selfDecomposable_infinitelyDivisible` and `cited_A43_residual_infinitelyDivisible`. -/
theorem witness_what_does_not_lift_chain_1_limit (hd : 1 ≤ d) (hq : 1 < q) :
    classA d (maternLimitExponent 1) ∧ classAq q d (maternLimitExponent 1) :=
  ⟨(matern_pyramid_5_classA hd one_pos).1,
    what_does_not_lift_chain_1 hq _ (matern_pyramid_5_classA hd one_pos).1⟩

/-- **Witness, `lem:cm-uncancelled-atom` (`not_isCompletelyMonotone_expDiff`)** (R68): `A = 1`,
`B = 2`, `ρ = 3` meet its hypotheses, `3^{i+1}` being odd and `6` even. Lean core. -/
theorem witness_cm_uncancelled_atom :
    (0 : ℝ) < 1 ∧ (1 : ℝ) < 2 ∧ (1 : ℝ) < 3 ∧ ∀ i : ℕ, (1 : ℝ) * 3 ^ (i + 1) ≠ 2 * 3 := by
  refine ⟨one_pos, one_lt_two, by norm_num, fun i h => ?_⟩
  have h' : (3 : ℕ) ^ (i + 1) = 2 * 3 := by exact_mod_cast (by linarith : (3 : ℝ) ^ (i + 1) = 2 * 3)
  have hodd : Odd ((3 : ℕ) ^ (i + 1)) := Odd.pow (by decide)
  rw [h'] at hodd
  exact absurd hodd (by decide)


end FixPhase

/-! ### Witnesses owed by P3 and the vacuity passes, the fix phase's second run (fidelity
review, R51, R59, R68) -/

section FixPhaseTwo

open ProbabilityTheory (multivariateGaussian iIndepFun IndepFun indepFun_prod
  iIndepFun_iff_map_fun_eq_infinitePi_map)
open ScaleSpace (convPow)
open scoped Matrix

variable {d : ℕ} {q : ℝ}

/-- The log-coordinate profile of the wobbling gauge: `L + (a/2) sin(L/a)`. -/
noncomputable def wobbleLog (a L : ℝ) : ℝ := L + a / 2 * Real.sin (L / a)

/-- **A nonlinear member of `𝒢_q`**: `χ(t) = exp(f(log t))` with `f(L) = L + (a/2) sin(L/a)`,
`a = log q / (2π)`. -/
noncomputable def wobbleGauge (q : ℝ) (t : ℝ) : ℝ :=
  Real.exp (wobbleLog (Real.log q / (2 * Real.pi)) (Real.log t))

theorem hasDerivAt_wobbleLog {a : ℝ} (L : ℝ) :
    HasDerivAt (wobbleLog a) (1 + a / 2 * (Real.cos (L / a) * (1 / a))) L := by
  have h1 : HasDerivAt (fun L : ℝ => L / a) (1 / a) L := by
    simpa using (hasDerivAt_id L).div_const a
  exact (hasDerivAt_id L).add ((h1.sin).const_mul (a / 2))

theorem strictMono_wobbleLog {a : ℝ} (ha : 0 < a) : StrictMono (wobbleLog a) := by
  refine strictMono_of_deriv_pos fun L => ?_
  rw [(hasDerivAt_wobbleLog L).deriv]
  have hc := Real.neg_one_le_cos (L / a)
  have : a / 2 * (Real.cos (L / a) * (1 / a)) = Real.cos (L / a) / 2 := by field_simp
  rw [this]; linarith

theorem continuous_wobbleLog (a : ℝ) : Continuous (wobbleLog a) := by
  unfold wobbleLog; fun_prop

theorem isInGaugeGroup_wobbleGauge (hq : 1 < q) : IsInGaugeGroup q (wobbleGauge q) := by
  have hlq : 0 < Real.log q := Real.log_pos hq
  set a := Real.log q / (2 * Real.pi) with ha_def
  have ha : 0 < a := by positivity
  have hmono := strictMono_wobbleLog ha
  refine ⟨fun s hs t ht hst => ?_, fun t _ => Real.exp_pos _, fun y hy => ?_, ?_, fun t ht => ?_⟩
  · exact Real.exp_lt_exp.2 (hmono (Real.log_lt_log hs hst))
  · set L0 := Real.log y
    have hab : L0 - a ≤ L0 + a := by linarith
    have hlo : wobbleLog a (L0 - a) ≤ L0 := by
      have := Real.sin_le_one ((L0 - a) / a); unfold wobbleLog; nlinarith
    have hhi : L0 ≤ wobbleLog a (L0 + a) := by
      have := Real.neg_one_le_sin ((L0 + a) / a); unfold wobbleLog; nlinarith
    obtain ⟨L, -, hL⟩ := intermediate_value_Icc hab (continuous_wobbleLog a).continuousOn
      ⟨hlo, hhi⟩
    refine ⟨Real.exp L, Real.exp_pos L, ?_⟩
    simp only [wobbleGauge, Real.log_exp, ← ha_def, hL, L0, Real.exp_log hy]
  · exact (Real.continuous_exp.comp (continuous_wobbleLog a)).comp_continuousOn
      (Real.continuousOn_log.mono fun t ht => ne_of_gt (mem_Ioi.1 ht))
  · have hq0 : 0 < q := by linarith
    simp only [wobbleGauge, ← ha_def]
    rw [Real.log_mul hq0.ne' ht.ne', ← Real.exp_log hq0, ← Real.exp_add, Real.exp_log hq0]
    congr 1
    unfold wobbleLog
    have : (Real.log q + Real.log t) / a = Real.log t / a + 2 * Real.pi := by
      rw [ha_def]; field_simp; ring
    rw [this, Real.sin_add_two_pi]; ring

/-- The wobbling gauge is not linear: `χ(t)/t` takes two values. -/
theorem wobbleGauge_not_linear (hq : 1 < q) :
    ¬ ∃ c : ℝ, ∀ t : ℝ, 0 < t → wobbleGauge q t = c * t := by
  rintro ⟨c, hc⟩
  have hlq : 0 < Real.log q := Real.log_pos hq
  set a := Real.log q / (2 * Real.pi) with ha_def
  have ha : 0 < a := by positivity
  have key : ∀ L : ℝ, Real.exp (L + a / 2 * Real.sin (L / a)) = c * Real.exp L := fun L => by
    have := hc (Real.exp L) (Real.exp_pos L)
    simpa [wobbleGauge, wobbleLog, ← ha_def] using this
  have h1 := key (a * (Real.pi / 2))
  have h2 := key (a * (3 * Real.pi / 2))
  rw [mul_div_cancel_left₀ _ ha.ne', Real.sin_pi_div_two, Real.exp_add] at h1
  have hs3 : Real.sin (3 * Real.pi / 2) = -1 := by
    have : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [this, Real.sin_add_pi, Real.sin_pi_div_two]
  rw [mul_div_cancel_left₀ _ ha.ne', hs3, Real.exp_add] at h2
  have e1 : c = Real.exp (a / 2) := by field_simp at h1; linarith
  have e2 : c = Real.exp (-(a / 2)) := by field_simp at h2; linarith
  have := Real.exp_lt_exp.2 (show -(a / 2) < a / 2 by linarith)
  linarith

/-- **Witness, `thm:selection-stratum-two`(2) (`selection_stratum_two_2`,
`selection_stratum_two_2_converse_family`) at a nonlinear gauge** (R59): the Matérn pyramid
relabelled by the wobbling gauge `χ ∈ 𝒢_q`, which is not linear, is an isotropic `q`-covariant
family in the canonical discrete gauge with the principle at every octave stage `t ∈ [1, q)`.
The gauge is Lean core; the family, through the ledger, as
`witness_selection_stratum_two_2_matern` (A39, A45, A43's first clause). -/
theorem witness_selection_stratum_two_2_wobble (hd : 1 ≤ d) (hq : 1 < q) :
    IsInGaugeGroup q (wobbleGauge q) ∧
      (¬ ∃ c : ℝ, ∀ t : ℝ, 0 < t → wobbleGauge q t = c * t) ∧
      IsIsotropicFamily (relabel (maternPyr hd hq one_pos) (extendByZero (wobbleGauge q))) ∧
      IsCovariantAt (relabel (maternPyr hd hq one_pos) (extendByZero (wobbleGauge q))) q
        (fun t => q * t) ∧
      ∀ t : ℝ, 1 ≤ t → t < q → HasImplicitEulerPrinciple
        (relabel (maternPyr hd hq one_pos) (extendByZero (wobbleGauge q)) t (q * t)) := by
  have hχ := isInGaugeGroup_wobbleGauge hq
  obtain ⟨hiso, hcov, -⟩ :=
    maternPyramid_gauge_family hd hq hχ _ (isMaternPyramid_maternPyr hd hq one_pos)
  exact ⟨hχ, wobbleGauge_not_linear hq, hiso, hcov, fun t ht _ =>
    selection_stratum_two_2_converse_gauge hd hq hχ _ (isMaternPyramid_maternPyr hd hq one_pos) t
      (by linarith)⟩

/-- The probability mass function of a nonnegative summable real array of total mass one. -/
noncomputable def pmfOfReal {α : Type*} (f : α → ℝ) (h0 : ∀ a, 0 ≤ f a) (hs : Summable f)
    (h1 : ∑' a, f a = 1) : PMF α :=
  ⟨fun a => ENNReal.ofReal (f a), by
    have := ENNReal.ofReal_tsum_of_nonneg h0 hs
    rw [h1, ENNReal.ofReal_one] at this
    exact this ▸ ENNReal.summable.hasSum⟩

theorem pmfOfReal_toMeasure_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) (h0 : ∀ a, 0 ≤ f a) (hs : Summable f)
    (h1 : ∑' a, f a = 1) (a : α) :
    ((pmfOfReal f h0 hs h1).toMeasure {a}).toReal = f a := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a)]
  exact ENNReal.toReal_ofReal (h0 a)

/-- The geometric array `(1 - p) p^k` on `ℕ`, `0 ≤ p < 1`, is a probability array. -/
theorem geomArray_prob {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (∀ k : ℕ, 0 ≤ (1 - p) * p ^ k) ∧ Summable (fun k : ℕ => (1 - p) * p ^ k) ∧
      ∑' k : ℕ, (1 - p) * p ^ k = 1 := by
  have hs := summable_geometric_of_lt_one hp0 hp1
  refine ⟨fun k => mul_nonneg (by linarith) (pow_nonneg hp0 k), hs.mul_left _, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hp0 hp1]
  field_simp [show (1 - p) ≠ 0 by linarith]



/-- The nearest-neighbour step on `ℤ^d` is a lattice mask for `stdLattice d`. -/
theorem isLatticeMask_rwStep_stdLattice (hd : 1 ≤ d) :
    IsLatticeMask (stdLattice d : Set (Rd d)) (zdLaw d 1 rwStep) := by
  obtain ⟨⟨hp, hs, hne, hnull⟩, -⟩ := resolvent_masks_exact_4_five hd one_pos one_pos
  exact ⟨hp, hs, hne, measure_mono_null (compl_subset_compl.2 gridSet_one_subset_stdLattice) hnull⟩

/-- The support of the nearest-neighbour step spans `ℝ^d`: it holds the standard basis. -/
theorem span_rwStep_support :
    Submodule.span ℝ {x : Rd d | zdLaw d 1 rwStep {x} ≠ 0} = ⊤ := by
  rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  change zdLaw d 1 rwStep {_} ≠ 0
  rw [show ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis i : Rd d) = latticePt 1 (zbasis i) from ?_]
  · refine (lt_of_lt_of_le ?_ (zdLaw_singleton_ge 1 rwStep (zbasis i))).ne'
    refine ENNReal.ofReal_pos.2 (lt_of_lt_of_le ?_ (rwStep_axis_ge i (Or.inl rfl)))
    have : (0 : ℝ) < d := by exact_mod_cast Fin.pos i
    positivity
  ext j
  by_cases hj : j = i
  · subst hj; simp [latticePt, zbasis]
  · simp [latticePt, zbasis, hj, Pi.single_apply]

/-- **Witness, `prop:resolvent-masks-exact`(1)–(3) (`resolvent_masks_exact_1`, `_2`, `_3`)** at
`d ≥ 2` (R51): the lattice `ℤ^d`, the nearest-neighbour step `σ` (a finitely supported lattice
mask whose support spans `ℝ^d`), `p = 1/2`, `q = 2`, `γ = 1`, and a family carrying the grid
pyramid of the resolvent mask, which `_2` makes exact: every hypothesis of the three at once. The
mask is Lean core; the carrying family, through the ledger (A39, A41, by `_2`). -/
theorem witness_resolvent_masks_exact_rwStep (hd : 2 ≤ d) :
    IsLatticeMask (stdLattice d : Set (Rd d)) (zdLaw d 1 rwStep) ∧
      (∃ S : Finset (Rd d), zdLaw d 1 rwStep (↑S : Set (Rd d))ᶜ = 0) ∧
      Submodule.span ℝ {x : Rd d | zdLaw d 1 rwStep {x} ≠ 0} = ⊤ ∧
      ∃ μ : ℝ → ℝ → Measure (Rd d),
        CarriesLatticeLadder 2 (convPow (resolventMask (1 / 2) (zdLaw d 1 rwStep)) 1) μ := by
  have hd1 : 1 ≤ d := by omega
  have hσ := isLatticeMask_rwStep_stdLattice hd1
  have hfin := (resolvent_masks_exact_4_five hd1 one_pos one_pos).2.1
  haveI := hσ.1
  exact ⟨hσ, hfin, span_rwStep_support,
    (resolvent_masks_exact_2 (stdLattice d) _ hσ (lintegral_posLog_lt_top_of_finset hfin)
      (by norm_num) (by norm_num)
      (by norm_num : (1 : ℝ) < 2) le_rfl).1⟩



end FixPhaseTwo

end Pyramids
