/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.Synthesis
import ScaleSpaceCore.Cascade
import ScaleSpaceCore.Construction
import ScaleSpaceCore.Covariance

/-!
# `lem:line-axioms-kernels`: the axioms on the line, read on the kernels

Blueprint: `blueprint/src/parts/02-line.tex`, `lem:line-axioms-kernels`. Wave 2d: the seven
declarations moved here from `PyramidsSkeleton.Ch02Line`, their statements unchanged. Wave 2e
(2026-11-14) dropped the unused hypothesis (A4) from `line_axioms_kernels_1`, a strengthening: the
kernels' symmetry comes from (A3) and the representation.

## The route

The shared core's, which is the printed one with the core's names.

* **(1)** The kernels are `ScaleSpace.exists_kernelFamily`, unique by the uniqueness clause of
  `ScaleSpace.representation_existsUnique` (ledger A1, which the shared core proves; this
  article's `thm:cited-A1` is its statement). Symmetry, (I1) and the joint continuity of the
  transforms are `kernel_symmetric`, `kernel_diag`, `kernel_conv` and
  `continuousOn_fourierCos_kernel` (the last is (A7) against the Gaussian test function, whose
  transform has no zero); a symmetric law has the real transform `fourierCos`. (ND) is
  `kernel_ne_dirac`, and conversely `Φ_{s,t} = μ_{s,t} * · = id` forces `μ_{s,t} = δ₀`.
* **(2)** The core's `CascadeData` builds (A1)–(A7) from symmetric probability kernels with (I1)
  and the continuity of the cosine transform; (A7) there is Lévy's continuity theorem
  (`CascadeData.continuousOn_mconvL1`). The kernels are totalised by `δ₀` off `0 ≤ s ≤ t`.
* **(3)** The core's `map_mul_kernel_of_covariant` and `isScaleCovariant_of_map_mul`, whose proofs
  read only the representation; they are restated here for a bare operator family.
* **The last sentence.** The bijection of `qⁿ` is `S_q` iterated `n` times, or its inverse
  iterated, through the group laws of covariance (`cov_mul`, `cov_inv`).
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X PreCascadeCore CascadeCore CascadeData IsPositive IsNondegenerate
  IsScaleCovariant IsKernelFamily IsSymmetric dilL1 mconvL1 fourierCos mconv)
open scoped Topology

/-! ## Kernels and laws -/

/-- A symmetric law on `ℝ` has the real transform `fourierCos`. -/
theorem charFun_eq_fourierCos {m : Measure ℝ} [IsProbabilityMeasure m] (h : IsSymmetric m)
    (ω : ℝ) : charFun m ω = ((fourierCos m ω : ℝ) : ℂ) :=
  ScaleSpace.charFun_eq_fourierCos_of_symmetric h ω

/-! ## (3) for a bare operator family -/

section Bare

variable {Φ : ℝ → ℝ → (X →L[ℝ] X)} {μ : ℝ → ℝ → Measure ℝ}

/-- (A8) at one dilation gives the identity of measures (`ScaleSpace.map_mul_kernel_of_covariant`,
for a bare operator family). -/
theorem map_mul_kernel_of_scale (hker : IsKernelFamily Φ μ) {lam : ℝ} (hlam : 0 < lam)
    {s t s' t' : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hs' : 0 ≤ s') (hst' : s' ≤ t')
    (hop : (dilL1 hlam).comp (Φ s t) = (Φ s' t').comp (dilL1 hlam)) :
    (μ s t).map (fun x => lam * x) = μ s' t' := by
  haveI := hker.isProbability s t hs hst
  haveI := hker.isProbability s' t' hs' hst'
  haveI : IsProbabilityMeasure ((μ s t).map (fun x => lam * x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine ScaleSpace.eq_of_mconv_gaussTest_ae ?_
  set f : X := dilL1 (inv_pos.mpr hlam) ScaleSpace.gaussL1 with hfdef
  have hcoeF : ((f : X) : ℝ → ℝ) =ᵐ[volume] ScaleSpace.dilate lam⁻¹ ScaleSpace.gaussTest :=
    (ScaleSpace.coeFn_dilL1 _ _).trans (ScaleSpace.dilate_congr_ae (inv_ne_zero hlam.ne')
      ScaleSpace.coeFn_gaussL1_gaussTest)
  have hop' := congrArg (fun T : X →L[ℝ] X => T f) hop
  simp only [ContinuousLinearMap.comp_apply] at hop'
  have hleft : ((dilL1 hlam (Φ s t f) : X) : ℝ → ℝ)
      =ᵐ[volume] mconv ((μ s t).map (fun x => lam * x)) ScaleSpace.gaussTest := by
    refine (ScaleSpace.coeFn_dilL1 hlam _).trans ?_
    refine (ScaleSpace.dilate_congr_ae hlam.ne' ((hker.conv s t hs hst f).trans
      (ScaleSpace.mconv_congr_ae _ hcoeF))).trans ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [ScaleSpace.mconv_map_mul (μ s t) hlam ScaleSpace.gaussTest x]
  have hright : ((Φ s' t' (dilL1 hlam f) : X) : ℝ → ℝ)
      =ᵐ[volume] mconv (μ s' t') ScaleSpace.gaussTest := by
    refine (hker.conv _ _ hs' hst' _).trans (ScaleSpace.mconv_congr_ae _ ?_)
    refine (ScaleSpace.coeFn_dilL1 hlam f).trans ?_
    refine (ScaleSpace.dilate_congr_ae hlam.ne' hcoeF).trans ?_
    rw [ScaleSpace.dilate_dilate_inv hlam.ne']
  exact hleft.symm.trans ((by rw [hop'] : ((dilL1 hlam (Φ s t f) : X) : ℝ → ℝ)
    =ᵐ[volume] ((Φ s' t' (dilL1 hlam f) : X) : ℝ → ℝ)).trans hright)

/-- The identity of measures gives (A8) at one dilation (`ScaleSpace.isScaleCovariant_of_map_mul`,
for a bare operator family). -/
theorem scale_of_map_mul_kernel (hker : IsKernelFamily Φ μ) {lam : ℝ} (hlam : 0 < lam)
    {s t s' t' : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hs' : 0 ≤ s') (hst' : s' ≤ t')
    (h : (μ s t).map (fun x => lam * x) = μ s' t') :
    (dilL1 hlam).comp (Φ s t) = (Φ s' t').comp (dilL1 hlam) := by
  haveI := hker.isProbability s t hs hst
  haveI := hker.isProbability s' t' hs' hst'
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [ContinuousLinearMap.comp_apply]
  refine Lp.ext_iff.mpr ?_
  have hleft : ((dilL1 hlam (Φ s t f) : X) : ℝ → ℝ)
      =ᵐ[volume] ScaleSpace.dilate lam (mconv (μ s t) ((f : X) : ℝ → ℝ)) :=
    (ScaleSpace.coeFn_dilL1 hlam _).trans
      (ScaleSpace.dilate_congr_ae hlam.ne' (hker.conv s t hs hst f))
  have hright : ((Φ s' t' (dilL1 hlam f) : X) : ℝ → ℝ)
      =ᵐ[volume] ScaleSpace.dilate lam (mconv (μ s t) ((f : X) : ℝ → ℝ)) := by
    refine (hker.conv _ _ hs' hst' _).trans ?_
    refine (ScaleSpace.mconv_congr_ae _ (ScaleSpace.coeFn_dilL1 hlam f)).trans ?_
    rw [← h]
    refine Filter.Eventually.of_forall fun x => ?_
    rw [ScaleSpace.mconv_map_mul (μ s t) hlam _ x, ScaleSpace.dilate_inv_dilate hlam.ne']
  exact hleft.trans hright.symm

end Bare

/-! ## `lem:line-axioms-kernels` -/

/-- **`lem:line-axioms-kernels`(1), the kernels exist and are unique.** Under (A1)–(A7) there is a
kernel family, and any two agree on `0 ≤ s ≤ t`. -/
theorem line_axioms_kernels_1_exists (Fam : PreCascadeCore) (hpos : IsPositive Fam.Φ) :
    ∃ μ : ℝ → ℝ → Measure ℝ, IsKernelFamily Fam.Φ μ ∧
      ∀ μ' : ℝ → ℝ → Measure ℝ, IsKernelFamily Fam.Φ μ' →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ s t := by
  obtain ⟨μ, hμ⟩ := ScaleSpace.exists_kernelFamily Fam hpos
  refine ⟨μ, hμ, fun μ' hμ' s t hs hst => ?_⟩
  exact (ScaleSpace.representation_existsUnique Fam.Φ Fam.translation hpos Fam.unit_mass
    hs hst).unique ⟨hμ'.isProbability s t hs hst, hμ'.conv s t hs hst⟩
    ⟨hμ.isProbability s t hs hst, hμ.conv s t hs hst⟩

/-- **`lem:line-axioms-kernels`(1), their properties.** The kernels of a family with (A1)–(A7) are
symmetric and satisfy (I1) and (I2), and (ND) holds if and only if `μ_{s,t} ≠ δ₀` for `s < t`. -/
theorem line_axioms_kernels_1 (Fam : PreCascadeCore)
    (μ : ℝ → ℝ → Measure ℝ) (hμ : IsKernelFamily Fam.Φ μ) :
    IsSymmetricLaws μ ∧ IsLawHemigroup μ ∧ (IsNondegenerate Fam.Φ ↔ IsNondegenerateLaws μ) := by
  have hsym : IsSymmetricLaws μ := fun s t hs hst => ScaleSpace.kernel_symmetric hμ hs hst
  refine ⟨hsym, ⟨hμ.isProbability, fun t ht => ScaleSpace.kernel_diag hμ ht,
    fun r s t hr hrs hst => ?_, fun ω => ?_⟩, ⟨fun hnd s t hs hst =>
      ScaleSpace.kernel_ne_dirac hμ hnd hs hst, fun hnd s t hs hst hid => ?_⟩⟩
  · haveI := hμ.isProbability r s hr hrs
    haveI := hμ.isProbability s t (hr.trans hrs) hst
    rw [ScaleSpace.kernel_conv hμ hr hrs hst, Measure.conv_comm]
  · refine ContinuousOn.congr (f := fun p : ℝ × ℝ => ((fourierCos (μ p.1 p.2) ω : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp_continuousOn
        (ScaleSpace.continuousOn_fourierCos_kernel hμ ω)) fun p hp => ?_
    haveI := hμ.isProbability p.1 p.2 hp.1 hp.2
    exact charFun_eq_fourierCos (hsym p.1 p.2 hp.1 hp.2) ω
  · haveI := hμ.isProbability s t hs hst.le
    refine hnd s t hs hst (ScaleSpace.eq_dirac_of_mconvL1_eq_id ?_)
    rw [← ScaleSpace.Phi_eq_mconvL1 hμ hs hst.le, hid]

/-- **`lem:line-axioms-kernels`(1), "so"**: the kernels of a family with (A1)–(A7) and (ND) are a
symmetric family in dimension `1`. -/
theorem line_axioms_kernels_1_family (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsKernelFamily C.Φ μ) : IsSymmetricFamily μ := by
  obtain ⟨hsym, hhemi, hnd⟩ := line_axioms_kernels_1 C.toPreCascadeCore μ hμ
  exact ⟨hhemi, hnd.1 C.nondegenerate, hsym⟩

/-- The laws, totalised by `δ₀` off `0 ≤ s ≤ t`. -/
noncomputable def totalLaws (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) : Measure ℝ := by
  classical
  exact if 0 ≤ s ∧ s ≤ t then μ s t else Measure.dirac 0

theorem totalLaws_of {μ : ℝ → ℝ → Measure ℝ} {s t : ℝ} (h : 0 ≤ s ∧ s ≤ t) :
    totalLaws μ s t = μ s t := by
  simp [totalLaws, h.1, h.2]

theorem totalLaws_of_not {μ : ℝ → ℝ → Measure ℝ} {s t : ℝ} (h : ¬ (0 ≤ s ∧ s ≤ t)) :
    totalLaws μ s t = Measure.dirac 0 := by
  unfold totalLaws
  simp only [h, if_false]

/-- The cascade data of symmetric laws with (I1) and (I2), totalised by `δ₀`. -/
noncomputable def lawsCascadeData (μ : ℝ → ℝ → Measure ℝ) (hsymm : IsSymmetricLaws μ)
    (hμ : IsLawHemigroup μ) : CascadeData where
  κ := totalLaws μ
  prob := fun s t => by
    by_cases h : 0 ≤ s ∧ s ≤ t
    · rw [totalLaws_of h]; exact hμ.isProbability s t h.1 h.2
    · rw [totalLaws_of_not h]; infer_instance
  sym := fun s t => by
    by_cases h : 0 ≤ s ∧ s ≤ t
    · rw [totalLaws_of h]; exact hsymm s t h.1 h.2
    · rw [totalLaws_of_not h]; exact ScaleSpace.isSymmetric_dirac_zero
  self := fun t ht => by rw [totalLaws_of ⟨ht, le_rfl⟩]; exact hμ.diag t ht
  conv := fun r s t hr hrs hst => by
    rw [totalLaws_of ⟨hr, hrs⟩, totalLaws_of ⟨hr.trans hrs, hst⟩,
      totalLaws_of ⟨hr, hrs.trans hst⟩]
    haveI := hμ.isProbability r s hr hrs
    haveI := hμ.isProbability s t (hr.trans hrs) hst
    rw [hμ.cascade r s t hr hrs hst, Measure.conv_comm]
  cos_continuousOn := fun ω => by
    refine ContinuousOn.congr (f := fun p : ℝ × ℝ => (charFun (μ p.1 p.2) ω).re)
      (Complex.continuous_re.comp_continuousOn (hμ.continuous ω)) fun p hp => ?_
    change fourierCos (totalLaws μ p.1 p.2) ω = (charFun (μ p.1 p.2) ω).re
    rw [totalLaws_of hp]
    haveI := hμ.isProbability p.1 p.2 hp.1 hp.2
    rw [charFun_eq_fourierCos (hsymm p.1 p.2 hp.1 hp.2) ω, Complex.ofReal_re]

theorem lawsCascadeData_κ {μ : ℝ → ℝ → Measure ℝ} (hsymm : IsSymmetricLaws μ)
    (hμ : IsLawHemigroup μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (lawsCascadeData μ hsymm hμ).κ s t = μ s t :=
  totalLaws_of ⟨hs, hst⟩

theorem lawsCascadeData_isKernelFamily {μ : ℝ → ℝ → Measure ℝ} (hsymm : IsSymmetricLaws μ)
    (hμ : IsLawHemigroup μ) : IsKernelFamily (lawsCascadeData μ hsymm hμ).preCore.Φ μ := by
  have h := (lawsCascadeData μ hsymm hμ).isKernelFamily
  refine ⟨hμ.isProbability, fun s t hs hst f => ?_⟩
  have := h.conv s t hs hst f
  rwa [lawsCascadeData_κ hsymm hμ hs hst] at this

/-- **`lem:line-axioms-kernels`(2), the converse.** Symmetric probability measures with (I1) and
(I2) are the kernels of a family with (A1)–(A7), which has (ND) if and only if `μ_{s,t} ≠ δ₀` for
`s < t`. -/
theorem line_axioms_kernels_2 (μ : ℝ → ℝ → Measure ℝ) (hsymm : IsSymmetricLaws μ)
    (hμ : IsLawHemigroup μ) :
    ∃ Fam : PreCascadeCore, IsPositive Fam.Φ ∧ IsKernelFamily Fam.Φ μ ∧
      (IsNondegenerate Fam.Φ ↔ IsNondegenerateLaws μ) := by
  set D := lawsCascadeData μ hsymm hμ with hD
  refine ⟨D.preCore, D.isPositive, lawsCascadeData_isKernelFamily hsymm hμ,
    ⟨fun hnd s t hs hst hdir => ?_, fun hnd => D.isNondegenerate fun s t hs hst => ?_⟩⟩
  · apply hnd s t hs hst
    have hκ : D.κ s t = Measure.dirac 0 := by rw [lawsCascadeData_κ hsymm hμ hs hst.le, hdir]
    rw [D.preCore_Φ, ScaleSpace.mconvL1_congr hκ, ScaleSpace.mconvL1_dirac_zero]
  · rw [lawsCascadeData_κ hsymm hμ hs hst.le]
    exact hnd s t hs hst

/-- **`lem:line-axioms-kernels`(2), "in particular"**: a symmetric family in dimension `1` gives
a family with (A1)–(A7) and (ND). -/
theorem line_axioms_kernels_2_family (μ : ℝ → ℝ → Measure ℝ) (hμ : IsSymmetricFamily μ) :
    ∃ C : CascadeCore, IsKernelFamily C.Φ μ := by
  set D := lawsCascadeData μ hμ.2.2 hμ.1 with hD
  refine ⟨D.cascadeCore fun s t hs hst => ?_, lawsCascadeData_isKernelFamily hμ.2.2 hμ.1⟩
  rw [lawsCascadeData_κ hμ.2.2 hμ.1 hs hst.le]
  exact hμ.2.1 s t hs hst

/-- **`lem:line-axioms-kernels`(3).** For operators with kernels `μ`, `λ > 0` and an increasing
bijection `S` of `[0,∞)`: `D_λ Φ_{s,t} = Φ_{Ss,St} D_λ` for all `s ≤ t` if and only if
`T_λ μ_{s,t} = μ_{Ss,St}` for all `s ≤ t`. -/
theorem line_axioms_kernels_3 (Φ : ℝ → ℝ → (X →L[ℝ] X)) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsKernelFamily Φ μ) {lam : ℝ} (hlam : 0 < lam) (S : ℝ → ℝ)
    (hS : IsIncreasingBijection S) :
    (∀ s t : ℝ, 0 ≤ s → s ≤ t →
        (dilL1 hlam).comp (Φ s t) = (Φ (S s) (S t)).comp (dilL1 hlam)) ↔
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → (μ s t).map (fun x => lam * x) = μ (S s) (S t) := by
  have hS0 : ∀ s, 0 ≤ s → 0 ≤ S s := fun s hs => hS.mapsTo hs
  have hSle : ∀ s t, 0 ≤ s → s ≤ t → S s ≤ S t := fun s t hs hst =>
    hS.strictMonoOn.monotoneOn hs (hs.trans hst) hst
  exact ⟨fun h s t hs hst => map_mul_kernel_of_scale hμ hlam hs hst (hS0 s hs) (hSle s t hs hst)
      (h s t hs hst),
    fun h s t hs hst => scale_of_map_mul_kernel hμ hlam hs hst (hS0 s hs) (hSle s t hs hst)
      (h s t hs hst)⟩

/-- `λ • x = λ * x` on `ℝ`: covariance in the two spellings. -/
theorem isCovariantAt_iff_map_mul (μ : ℝ → ℝ → Measure ℝ) (lam : ℝ) (S : ℝ → ℝ) :
    IsCovariantAt μ lam S ↔ IsIncreasingBijection S ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → (μ s t).map (fun x => lam * x) = μ (S s) (S t) := by
  simp only [IsCovariantAt, smul_eq_mul]

/-- **`lem:line-axioms-kernels`, the last sentence.** Read through its kernels, a family with
(A1)–(A7) and (ND) satisfying (A8) at the dilations `q^ℤ` is a symmetric family whose kernels are
`q^n`-covariant with the same bijections, and a `q`-covariant kernel family comes from such
bijections, with the same `S_q`. -/
theorem line_axioms_kernels_qcov (C : CascadeCore) (μ : ℝ → ℝ → Measure ℝ)
    (hμ : IsKernelFamily C.Φ μ) {q : ℝ} (hq : 1 < q) :
    (∀ S : ℝ → ℝ → ℝ, IsScaleCovariant C.Φ (qPowers q) S →
        ∀ n : ℤ, IsCovariantAt μ (q ^ n) (S (q ^ n))) ∧
      ∀ Sq : ℝ → ℝ, IsCovariantAt μ q Sq →
        ∃ S : ℝ → ℝ → ℝ, S q = Sq ∧ IsScaleCovariant C.Φ (qPowers q) S := by
  have hq0 : 0 < q := by linarith
  refine ⟨fun S hS n => ?_, fun Sq hSq => ?_⟩
  · -- (A8) at `qⁿ` is `qⁿ`-covariance of the kernels
    have hmem : q ^ n ∈ qPowers q := ⟨n, rfl⟩
    have hpos : 0 < q ^ n := zpow_pos hq0 n
    rw [isCovariantAt_iff_map_mul]
    refine ⟨⟨hS.S_mapsTo _ hpos hmem, hS.S_strictMonoOn _ hpos hmem, hS.S_surjOn _ hpos hmem⟩,
      fun s t hs hst => ?_⟩
    exact ScaleSpace.map_mul_kernel_of_covariant (Fam := C.toPreCascadeCore) hμ hS hpos hmem
      hs hst
  · -- the bijections at `qⁿ`, by iterating `S_q` and its inverse
    obtain ⟨T, hT, -, -⟩ := cov_inv hq0 hSq
    have hpow : ∀ (R : ℝ → ℝ) (a : ℝ), IsCovariantAt μ a R →
        ∀ k : ℕ, IsCovariantAt μ (a ^ k) (R^[k]) := by
      intro R a hR k
      induction k with
      | zero => simpa using cov_one μ
      | succ k ih =>
        rw [pow_succ', Function.iterate_succ']
        exact cov_mul hR ih
    set Siter : ℤ → ℝ → ℝ := fun n => if 0 ≤ n then Sq^[n.toNat] else T^[(-n).toNat]
      with hSiter
    have hcovn : ∀ n : ℤ, IsCovariantAt μ (q ^ n) (Siter n) := by
      intro n
      simp only [hSiter]
      split_ifs with hn
      · have := hpow Sq q hSq n.toNat
        rwa [← zpow_natCast, Int.toNat_of_nonneg hn] at this
      · have := hpow T q⁻¹ hT (-n).toNat
        rwa [inv_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_neg, neg_neg]
          at this
    set S : ℝ → ℝ → ℝ := fun lam => Siter (dgLevel q lam) with hSdef
    have hlev : ∀ n : ℤ, dgLevel q (q ^ n) = n := fun n =>
      dgLevel_eq hq le_rfl (zpow_lt_zpow_right₀ hq (by omega))
    have hSn : ∀ n : ℤ, S (q ^ n) = Siter n := fun n => by simp only [hSdef, hlev]
    refine ⟨S, ?_, ?_⟩
    · have h1 := hSn 1
      rw [zpow_one] at h1
      rw [h1]
      simp [hSiter]
    · have hcov : ∀ lam, 0 < lam → lam ∈ qPowers q → IsCovariantAt μ lam (S lam) := by
        rintro lam - ⟨n, rfl⟩
        rw [hSn n]
        exact hcovn n
      refine ScaleSpace.isScaleCovariant_of_map_mul (Fam := C.toPreCascadeCore) hμ
        (fun lam hlam hmem => (hcov lam hlam hmem).1.mapsTo)
        (fun lam hlam hmem => (hcov lam hlam hmem).1.strictMonoOn)
        (fun lam hlam hmem => (hcov lam hlam hmem).1.surjOn)
        (fun lam hlam hmem s t hs hst => ?_)
      exact ((isCovariantAt_iff_map_mul μ lam (S lam)).1 (hcov lam hlam hmem)).2 s t hs hst

end Pyramids
