/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Witnesses
import Pyramids.Line.LatticeLine
import Pyramids.Line.LatticeLineStrict
import Pyramids.Pyramid.LatticeStrata
import Pyramids.Pyramid.LatticeStrataStrict
import Pyramids.Pyramid.WhatDoesNotLiftChain
import Pyramids.Pyramid.LadderKnot
import Pyramids.Pyramid.LadderCoupling
import Pyramids.Pyramid.LadderUnique
import Pyramids.Pyramid.NoBoundedStep
import Pyramids.Matern.MaternDensity
import Pyramids.Matern.CreationPlane
import Pyramids.Matern.StageLemmaConverse
import Pyramids.Matern.SelectionGauge
import Pyramids.Matern.SelectionStage
import Pyramids.Price.NotIsotropic
import Pyramids.Price.ExactMasks
import Pyramids.DiscreteHelmholtz

/-!
# Positive probes: the theory module (blueprint chapters 2–5)

The boundary harness's second check (article-kit `docs/LINKAGE.md` rule 5, `linkage boundary`;
`linkage.toml` `[boundary]`). Each probe **uses** one headline declaration of the theory part,
§§ 2–5.3 of the draft (the line, the strata in `ℝ^d`, the Matérn pyramid and its selection, the
exact grid pyramid), and keeps one clause of it, read at a model of `Witnesses.lean` where that
makes it concrete. A headline statement weakened into something that still type-checks (a clause
dropped, a hypothesis strengthened, an iff cut to one direction) stops one of these from building.

The computation paper's probes are in `Pyramids.ProbesComputation`, a root of the module
`computation`; this file is a root of the module `pyramids` (`adr/0007`), and imports no file of
the computation paper.

The file is part of the library (CI builds it, and the guard against unproved declarations scans
it); nothing imports it.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X CascadeCore IsScaleCovariant IsKernelFamily IsSymmetric SymLevyPair SDProfile
  profileMeasure mconvE)
open scoped ENNReal Topology RealInnerProductSpace ComplexOrder

variable {d : ℕ}

/-! ## § 2: the theory on the line -/

/-- `thm:lattice-line`(1) keeps its increments: every increment `μ_{s,t}` of a kernel family is
infinitely divisible, with folded data whose Gaussian part is the difference of the levels'. A
theorem that lost the increment clause, or the infinite divisibility in it, stops this. -/
theorem probe_lattice_line_1 (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsKernelFamily C.Φ μ) (P : ℝ → SymLevyPair)
    (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IsInfinitelyDivisible (μ s t) ∧
      ∃ Q : SymLevyPair, Q.a = (P t).a - (P s).a ∧ IsFoldedData (μ s t) Q := by
  obtain ⟨-, -, hinc, -⟩ := lattice_line_1 C μ hμ P hP
  obtain ⟨-, hid, Q, hQa, -, hQ⟩ := hinc s t hs hst
  exact ⟨hid, Q, hQa, hQ⟩

/-- `thm:lattice-line`(2) keeps both halves: covariance at the ratio `q` scales the Gaussian part
by `q²` from `t` to `qt`, and makes every kernel semi-selfdecomposable with span `q`. -/
theorem probe_lattice_line_2 (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsKernelFamily C.Φ μ) (P : ℝ → SymLevyPair)
    (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t)) {q : ℝ} (hq : 1 < q)
    (hS : ∃ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (qPowers q) S ∧ IsCanonicalDiscreteGauge q S)
    {t : ℝ} (ht : 0 < t) :
    (P (q * t)).a = q ^ 2 * (P t).a ∧ IsSemiSelfDecomposableWithSpan q (μ 0 t) :=
  ⟨(((lattice_line_2 C μ hμ P hP hq).1.1 hS) t ht).1,
    ((lattice_line_2 C μ hμ P hP hq).2 hS).1 t ht.le⟩

/-- `thm:lattice-line`(3), necessity: a family covariant under every dilation has, in some gauge,
the self-similar Gaussian part `D.a t²`. -/
theorem probe_lattice_line_3 (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsKernelFamily C.Φ μ) (P : ℝ → SymLevyPair)
    (hP : ∀ t : ℝ, 0 ≤ t → IsFoldedData (μ 0 t) (P t))
    (hS : ∃ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (Ioi 0) S) :
    ∃ (ψ : ℝ → ℝ) (D : SDProfile), IsGauge ψ ∧ ∀ t : ℝ, 0 < t → (P (ψ t)).a = D.a * t ^ 2 := by
  obtain ⟨ψ, D, hψ, h⟩ := (lattice_line_3 C μ hμ P hP).1 hS
  exact ⟨ψ, D, hψ, fun t ht => (h t ht).1⟩

/-- `cor:lattice-line-strict` at `q = 2`: some cascade core is not covariant at the ratio `2`. A
corollary weakened to the strictness of the upper inclusion only stops this. -/
theorem probe_lattice_line_strict :
    ∃ C : CascadeCore, ¬ ∃ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (qPowers 2) S :=
  (lattice_line_strict (q := 2) (by norm_num)).1

/-! ## § 3: the strata in `ℝ^d` -/

/-- `thm:lattice-strata`(1) keeps the nondegeneracy: distinct scales carry distinct data, and the
data start at `0`. A theorem that lost the strict increase stops this. -/
theorem probe_lattice_strata_1 (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsIsotropicFamily μ) (D : ℝ → SymLevyData d)
    (hD : ∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t)) (a : ℝ → ℝ)
    (ha : ∀ t : ℝ, 0 ≤ t → (D t).A = a t • (1 : Mat d)) :
    (D 0).ν = 0 ∧ ∀ s t : ℝ, 0 ≤ s → s < t → (a s, (D s).ν) ≠ (a t, (D t).ν) := by
  obtain ⟨-, h0, -, -, hne, -⟩ := lattice_strata_1 hd μ hμ D hD a ha
  exact ⟨h0, hne⟩

/-- `thm:lattice-strata`(2) keeps both halves, as `probe_lattice_line_2` on the line. -/
theorem probe_lattice_strata_2 (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsIsotropicFamily μ) (D : ℝ → SymLevyData d)
    (hD : ∀ t : ℝ, 0 ≤ t → IsSymData (μ 0 t) (D t)) (a : ℝ → ℝ)
    (ha : ∀ t : ℝ, 0 ≤ t → (D t).A = a t • (1 : Mat d)) {q : ℝ} (hq : 1 < q)
    (hcov : IsCovariantAt μ q (fun t => q * t)) {t : ℝ} (ht : 0 < t) :
    a (q * t) = q ^ 2 * a t ∧ IsSemiSelfDecomposableWithSpan q (μ 0 t) :=
  ⟨(((lattice_strata_2 hd μ hμ D hD a ha hq).1.1 hcov) t ht).1,
    ((lattice_strata_2 hd μ hμ D hD a ha hq).2 hcov).1 t ht.le⟩

/-- `thm:lattice-strata`(3), sufficiency, at the Gaussian family: the gauge `id` and `F(r) = r²`
give covariance under every dilation. A theorem cut to its necessity direction stops this. -/
theorem probe_lattice_strata_3 (hd : 1 ≤ d) : IsFullyCovariantLaws (gaussFamily d) := by
  obtain ⟨⟨hiso, hsym⟩, -, hχ, hF, hrep⟩ := witness_lattice_strata_3_gauss (d := d) hd
  exact (lattice_strata_3 hd (gaussFamily d) hiso (gaussData d) hsym).2 ⟨id, _, hχ, hF, hrep⟩

/-- `thm:lattice-strata-strict` in the plane at `q = 2`: some isotropic family is covariant at the
ratio `2` and not under every dilation, so the middle stratum is not the top one. -/
theorem probe_lattice_strata_strict :
    ∃ μ : ℝ → ℝ → Measure (Rd 2), IsIsotropicFamily μ ∧ IsLamCovariant μ 2 ∧
      ¬ IsFullyCovariantLaws μ :=
  (lattice_strata_strict (d := 2) (by norm_num) (by norm_num : (1 : ℝ) < 2)).2

/-- `prop:what-does-not-lift-chain`(2), its first step at `q = 2`: some exponent admitted on the
line is not admitted in the plane. -/
theorem probe_what_does_not_lift_chain_strict :
    ∃ F : ℝ → ℝ, classAq 2 1 F ∧ ¬ classAq 2 (1 + 1) F :=
  what_does_not_lift_chain_strict (by norm_num : (1 : ℝ) < 2) le_rfl

/-- `prop:ladder-knot-kernel`(1) keeps the knot kernel's Gaussian part and the logarithmic moment:
under covariance at `q`, the Gaussian part of `μ_1` is `(q² - 1)⁻¹` times the step's, and the step's
Lévy measure has a finite logarithmic moment. -/
theorem probe_ladder_knot_kernel_1 (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsSymmetricFamily μ)
    (hcov : IsCovariantAt μ q (fun t => q * t)) (Dρ D1 : SymLevyData d)
    (hDρ : IsSymData (μ 1 q) Dρ) (hD1 : IsSymData (μ 0 1) D1) :
    D1.A = (q ^ 2 - 1)⁻¹ • Dρ.A ∧ ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤ := by
  obtain ⟨-, hA, -, hmom⟩ := ladder_knot_kernel_1 hd hq μ hμ hcov Dρ D1 hDρ hD1
  exact ⟨hA, hmom⟩

/-- `prop:ladder-knot-kernel`(2) keeps the existence and the rotation clause: every symmetric
infinitely divisible step `≠ δ₀` with a logarithmic moment has a family through its ladder, which
is rotation invariant when the step is. -/
theorem probe_ladder_knot_kernel_2 (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0) (Dρ : SymLevyData d)
    (hDρ : IsSymData ρ Dρ) (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤)
    (hrot : IsRotationInvariant ρ) :
    ∃ μ : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ ∧ IsRotationInvariantLaws μ := by
  obtain ⟨μ, hL, -, hR⟩ := ladder_knot_kernel_2 hd hq ρ hne Dρ hDρ hmom
  exact ⟨μ, hL, hR hrot⟩

/-- `prop:ladder-knot-kernel`(2) keeps the moment equivalence (headline since review round 3,
batch C, s6-7.R4): the step's Lévy measure has a finite logarithmic moment exactly when the step
has, so the hypothesis of `ladder_knot_kernel_2` may be read on the step itself. An equivalence cut
to one direction stops this. -/
theorem probe_ladder_knot_kernel_2_moments (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q)
    (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ] (hid : IsInfinitelyDivisible ρ)
    (hne : ρ ≠ Measure.dirac 0) (Dρ : SymLevyData d) (hDρ : IsSymData ρ Dρ)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂ρ < ⊤) :
    (∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) ∧
      ∃ μ : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ := by
  have hν := (ladder_knot_kernel_2_moments ρ hid Dρ hDρ).2 hmom
  obtain ⟨μ, hL, -⟩ := ladder_knot_kernel_2 hd hq ρ hne Dρ hDρ hν
  exact ⟨hν, μ, hL⟩

/-- `prop:ladder-knot-kernel`(2) keeps both directions of the uniqueness up to `𝒢_q` (headline since
review round 3, batch C, s1-3.S3): any two families with the ladder are relabellings of each other
exactly when the step's data span an extreme ray, here read as two implications. An equivalence cut
to one direction stops this. -/
theorem probe_ladder_knot_kernel_2_unique_iff (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q)
    (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0) (Dρ : SymLevyData d)
    (hDρ : IsSymData ρ Dρ) (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) :
    (Dρ.IsExtremeIn (fun _ => True) → ∀ μ μ' : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ →
      HasLadder q ρ μ' → ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (extendByZero g s) (extendByZero g t)) ∧
      (¬ Dρ.IsExtremeIn (fun _ => True) → ∃ μ μ' : ℝ → ℝ → Measure (Rd d),
        HasLadder q ρ μ ∧ HasLadder q ρ μ' ∧ ¬ ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
          ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (extendByZero g s) (extendByZero g t)) := by
  have h := ladder_knot_kernel_2_unique_iff hd hq ρ hne Dρ hDρ hmom
  refine ⟨h.2, fun hn => ?_⟩
  by_contra hc
  push Not at hc
  exact hn (h.1 fun μ μ' hL hL' => hc μ μ' hL hL')

/-- `prop:ladder-knot-kernel`(2) keeps the isotropic uniqueness: for a rotation-invariant step whose
data span an extreme ray of the invariant cone, any two isotropic families with the ladder are
relabellings of each other; and conversely. -/
theorem probe_ladder_knot_kernel_2_unique_iff_rot (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q)
    (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0)
    (hrot : IsRotationInvariant ρ) (Dρ : SymLevyData d) (hDρ : IsSymData ρ Dρ)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) :
    Dρ.IsExtremeIn SymLevyData.IsOrthInvariant ↔
      ∀ μ μ' : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ → IsRotationInvariantLaws μ →
        HasLadder q ρ μ' → IsRotationInvariantLaws μ' → ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
          ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (extendByZero g s) (extendByZero g t) :=
  (ladder_knot_kernel_2_unique_iff_rot hd hq ρ hne hrot Dρ hDρ hmom).symm

/-- `prop:no-bounded-step` keeps the family clause: a law of bounded support other than a point
mass is no kernel `μ_{s,t}` of any law hemigroup. A proposition cut to "not infinitely divisible"
stops this. -/
theorem probe_no_bounded_step (w : Measure (Rd d)) [IsProbabilityMeasure w]
    (hbdd : ∃ R : ℝ, w {x | R < ‖x‖} = 0) (hnp : ∀ x : Rd d, w ≠ Measure.dirac x)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsLawHemigroup μ) : μ 0 1 ≠ w :=
  (no_bounded_step w hbdd hnp).2 μ hμ 0 1 le_rfl zero_le_one

/-! ## § 4: the Matérn pyramid and its selection -/

/-- `thm:matern-pyramid`(1) at a Matérn pyramid: its octave step from `t` to `qt` is the Bessel
potential `maternStep d (ct)`, and it is covariant under every dilation. -/
theorem probe_matern_pyramid_1_family (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    {t : ℝ} (ht : 0 < t) :
    maternPyr hd hq hc t (q * t) = maternStep d (c * t) ∧
      ∀ lam : ℝ, 0 < lam → IsCovariantAt (maternPyr hd hq hc) lam fun s => lam * s := by
  obtain ⟨-, hcov, hstep, -⟩ :=
    matern_pyramid_1_family hd hq hc _ (isMaternPyramid_maternPyr hd hq hc)
  exact ⟨hstep t ht, hcov⟩

/-- `prop:creation-plane`(1) keeps the creation: in `d ≥ 2`, some witness with one local maximum
has two after smoothing by any absolutely continuous law. -/
theorem probe_creation_plane_1 [NeZero d] (hd : 2 ≤ d) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (hac : μ ≪ volume) :
    ∃ a δ : ℝ, 1 < a ∧ 0 < δ ∧ ∃ x y, x ≠ y ∧
      IsLocalMax (mconvE μ (creationWitness d a δ)) x ∧
      IsLocalMax (mconvE μ (creationWitness d a δ)) y := by
  obtain ⟨a, δ, ha, hδ, -, hxy, -⟩ := creation_plane_1 hd μ hac
  exact ⟨a, δ, ha, hδ, hxy⟩

/-- `prop:stage-lemma`(3), the converse: a symmetric law with the implicit-Euler principle has a
real transform, `(1 + ωᵀCω)⁻¹`. A converse that lost the form stops this. -/
theorem probe_stage_lemma_3 (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hsymm : μ.map (fun x => -x) = μ) (hP : HasImplicitEulerPrinciple μ) (ω : Rd d) :
    (charFun μ ω).im = 0 := by
  obtain ⟨C, -, hC⟩ := stage_lemma_3 μ hsymm hP
  rw [hC ω, Complex.ofReal_im]

/-- `thm:selection-stratum-two`(2) at the Matérn pyramid with `c = 1`: the selection returns, in a
gauge of `𝒢_q`, the Matérn exponent. -/
theorem probe_selection_stratum_two_2 (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    ∃ χ : ℝ → ℝ, IsInGaugeGroup q χ ∧ ∀ t : ℝ, 0 < t → ∀ ω : Rd d,
      charFun (maternPyr hd hq one_pos 0 t) ω =
        ((Real.exp (-maternExponent q 1 (χ t * ‖ω‖)) : ℝ) : ℂ) := by
  obtain ⟨hiso, hcov, hP⟩ := witness_selection_stratum_two_2_matern hd hq
  obtain ⟨χ, hχ, hrep, -⟩ := selection_stratum_two_2 hd hq _ hiso hcov hP
  exact ⟨χ, hχ, hrep⟩

/-- `thm:selection-stratum-two`(2), the converse, at the gauge `id`: every octave stage of the
Matérn pyramid has the implicit-Euler principle. -/
theorem probe_selection_stratum_two_2_converse (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) {t : ℝ}
    (ht : 0 < t) :
    HasImplicitEulerPrinciple
      (maternPyr hd hq one_pos (extendByZero id t) (extendByZero id (q * t))) :=
  selection_stratum_two_2_converse hq id (isInGaugeGroup_id q) _
    (isMaternPyramid_maternPyr hd hq one_pos) t ht

/-! ## §§ 5.1–5.3: the exact grid pyramid -/

/-- `prop:grid-pyramid-not-isotropic`(2) in the plane, at the frame Matérn mask and `q = 2`: no
kernel of the family carrying it is rotation invariant. -/
theorem probe_grid_pyramid_not_isotropic_2 {t : ℝ} (ht : 0 < t) :
    ¬ IsSORotationInvariant
      (frameFamily (d := 2) (by norm_num) (by norm_num : (1 : ℝ) < 2) 0 t) :=
  (grid_pyramid_not_isotropic_2 le_rfl (stdLattice 2) (frameMask 2)
    (isLatticeMask_frameMask (by norm_num)) _
    (carriesLatticeLadder_frameFamily (by norm_num) (by norm_num))).1 t ht

/-- `prop:exact-masks`(1), the second equivalence, at the frame Matérn mask: an exact grid pyramid
has a step with a finite logarithmic moment. -/
theorem probe_exact_masks_1 (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂(frameMask d) < ⊤ := by
  obtain ⟨hprob, hs, hne, -, -, hex, -⟩ := witness_exact_masks_frame hd hq
  exact ((exact_masks_1 hq (frameMask d) hprob hs hne).2.1 hex).2

/-- `prop:exact-masks`(2) keeps the non-uniqueness, at the frame Matérn mask: two families carry
its pyramid and differ somewhere. -/
theorem probe_exact_masks_2 (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) :
    ∃ μ μ' : ℝ → ℝ → Measure (Rd d), CarriesLatticeLadder q (frameMask d) μ ∧
      CarriesLatticeLadder q (frameMask d) μ' ∧ ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ μ s t ≠ μ' s t := by
  obtain ⟨-, -, -, hw, -, hex, νw, hνw⟩ := witness_exact_masks_frame hd hq
  exact (exact_masks_2 (stdLattice d) hq (frameMask d) hw hex νw hνw).2.1

/-! ## § 5.4 of the blueprint: the discrete Helmholtz family (here since the split, `adr/0007`) -/

/-- `prop:discrete-helmholtz`, the kernel, on `ℤ²` with `h = t = 1`: the discrete Helmholtz kernel
is a probability kernel with symbol `(1 + t² σ_h(θ))⁻¹`. -/
theorem probe_discrete_helmholtz_kernel :
    IsProbKernel (discreteHelmholtz 2 1 1) ∧ ∀ θ : Fin 2 → ℝ,
      gridFourier (discreteHelmholtz 2 1 1) θ =
        (((1 + (1 : ℝ) ^ 2 * gridSymbol 1 θ)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨-, hprob, hsym, -⟩ :=
    discrete_helmholtz_kernel (d := 2) (by norm_num) (h := 1) (t := 1) one_pos one_pos
  exact ⟨hprob, hsym⟩

/-- `prop:discrete-helmholtz` keeps the cascade: the increments compose. A family that lost the
cascade law stops this. -/
theorem probe_discrete_helmholtz_cascade (hd : 1 ≤ d) {h : ℝ} (hh : 0 < h) (γ : ℕ) {r s t : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) :
    helmIncrement d h γ r t = kconv (helmIncrement d h γ s t) (helmIncrement d h γ r s) :=
  (discrete_helmholtz_cascade hd hh γ).2.2.2 r s t hr hrs hst

end Pyramids
