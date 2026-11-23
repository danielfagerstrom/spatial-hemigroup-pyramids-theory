/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.LadderCoupling
import Pyramids.LineAppendix.GaugeGroup
import Pyramids.Matern.SelectionGauge

/-!
# `prop:ladder-knot-kernel`(2): uniqueness up to `𝒢_q`

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:ladder-knot-kernel`(2). Review round 3,
batch C (s1-3.F6/S3): the families with the ladder of `ϱ` are unique up to a relabelling in
`𝒢_q` exactly when the data of the step span an extreme ray of the cone of symmetric data, and the
isotropic ones exactly when the data span an extreme ray of the cone of invariant data. Both
directions are proved.

## The route

* **The steps split the data.** For `t ∈ [1, q]` the steps `μ_{1,t}` and `μ_{t,q}` have data `E`,
  `F` with `E + F = D_ϱ`: the exponents add by (I1), and A39(ii) reads the data off the exponent
  (`ladder_step_split`).
* **Extreme data.** Then `E = c(t) D_ϱ`, so `μ̂_{1,t} = e^{-c(t)ψ_ϱ}`. Read at one `ω₀` with
  `ψ_ϱ(ω₀) > 0`, `c` is continuous by (I2), strictly increasing by (ND), `c(1) = 0` and
  `c(q) = 1`; so `φ := q^c` extends to some `g ∈ 𝒢_q` (`gauge_group_3`). The kernels agree with
  those of the uniform coupling relabelled by `g`: on `[1, q]` through `μ_t = μ_{1,t} * μ_1`, the
  two knot kernels being the limit of the partial products of `ϱ̂`; elsewhere by covariance; and
  the steps follow by (I1) (`relabel_of_proportional`). Two families are relabellings of the
  uniform one, so of each other through the inverse gauge (`exists_gauge_comp_inv`).
* **Data not extreme.** `D_ϱ = F + G` with `F` no multiple `cD_ϱ`, `c ≥ 0`. Then `F ≠ 0` (else
  `c = 0`) and `G ≠ 0` (else `c = 1`), and the split coupling of `F` and `G` is not the uniform
  coupling relabelled: at `√q` the step would give `F = (log_q g(√q)) D_ϱ`
  (`ladder_split_not_relabel`, the argument of `ladder_knot_kernel_2_split_rot` with `F`, `G` in
  place of `(A_ϱ/2, ν_a)`, `(A_ϱ/2, ν_b)`).
* **Isotropy.** The same with invariant data: the steps of an isotropic family have invariant
  exponents (`isOrthInvariant_of_rotationInvariant`), and the split coupling of invariant `F`, `G`
  is isotropic, its knot data being invariant as the limit of the partial products
  (`ladderStar_exponent_orth`).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace MatrixOrder Matrix

variable {d : ℕ}

/-! ## Extreme data -/

/-- **Data invariant under `O(d)`**: the exponent is invariant. -/
def SymLevyData.IsOrthInvariant (D : SymLevyData d) : Prop :=
  ∀ Q ∈ orthSet d, ∀ ω : Rd d, D.exponent (lin Qᵀ ω) = D.exponent ω

/-- **`D` is `0` or spans an extreme ray of the cone of the data with the property `P`**: in every
split `D = F + G` with `F`, `G` in the cone, `F = cD` for some `c ≥ 0`. With `P` true this is the
cone of all symmetric data; with `P = IsOrthInvariant` the cone of invariant data. -/
def SymLevyData.IsExtremeIn (P : SymLevyData d → Prop) (D : SymLevyData d) : Prop :=
  ∀ F G : SymLevyData d, P F → P G → F.A + G.A = D.A → F.ν + G.ν = D.ν →
    ∃ c : ℝ, 0 ≤ c ∧ F.A = c • D.A ∧ F.ν = ENNReal.ofReal c • D.ν

/-- The exponent of `cD` is `c Ψ_D`. -/
theorem SymLevyData.exponent_of_smul {F D : SymLevyData d} {c : ℝ} (hc : 0 ≤ c)
    (hA : F.A = c • D.A) (hν : F.ν = ENNReal.ofReal c • D.ν) (ω : Rd d) :
    F.exponent ω = c * D.exponent ω := by
  have e : F = SymLevyData.zero.addSmul D c :=
    SymLevyData.ext' (by simp [SymLevyData.addSmul, SymLevyData.zero, hA, max_eq_left hc])
      (by simp [SymLevyData.addSmul, SymLevyData.zero, hν])
  rw [e, SymLevyData.addSmul_exponent, SymLevyData.zero_exponent, zero_add, max_eq_left hc]

/-- Data with the exponent `c Ψ_D`, `c ≥ 0`, are `cD` (A39(ii)). -/
theorem SymLevyData.smul_of_exponent {F D : SymLevyData d} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ω : Rd d, F.exponent ω = c * D.exponent ω) :
    F.A = c • D.A ∧ F.ν = ENNReal.ofReal c • D.ν := by
  have h2 := SymLevyData.eq_of_exponent (E := F) (E' := SymLevyData.zero.addSmul D c) fun ω => by
    rw [h ω, SymLevyData.addSmul_exponent, SymLevyData.zero_exponent, zero_add, max_eq_left hc]
  simp only [SymLevyData.addSmul, SymLevyData.zero, zero_add, max_eq_left hc] at h2
  exact h2

/-- A rotation-invariant law has invariant data. -/
theorem isOrthInvariant_of_rotationInvariant {m : Measure (Rd d)} (hrot : IsRotationInvariant m)
    {D : SymLevyData d} (hD : IsSymData m D) : D.IsOrthInvariant := by
  intro Q hQ ω
  have h := (hD (lin Qᵀ ω)).symm.trans ((charFun_orth_of_rotationInvariant hrot hQ ω).trans
    (hD ω))
  have h2 := Real.exp_injective (Complex.ofReal_injective h)
  linarith

/-! ## The uniform coupling, with its isotropy -/

/-- **Isotropy from the octave**, for data invariant under `O(d)`. -/
theorem isRotationInvariantLaws_of_octave_orth {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d}
    (hinv : ∀ u ∈ Icc 1 q, (D u).IsOrthInvariant)
    {μ : ℝ → ℝ → Measure (Rd d)} (hμ : IsExponentLaws (octaveExponent q D) μ) :
    IsRotationInvariantLaws μ := by
  have hq0 : 0 < q := by linarith
  have hrotΨ : ∀ (t : ℝ) {Q : Mat d}, Q ∈ orthSet d → ∀ ω : Rd d,
      octaveExponent q D t (lin Qᵀ ω) = octaveExponent q D t ω := by
    intro t Q hQ ω
    rw [← octaveData_exponent hq, ← octaveData_exponent hq]
    rcases le_or_gt t 0 with ht | ht
    · rw [octaveData_of_nonpos q D ht, SymLevyData.zero_exponent, SymLevyData.zero_exponent]
    · rw [octaveData, dif_pos ⟨ht, hq0.ne'⟩, SymLevyData.dilate_exponent,
        SymLevyData.dilate_exponent, ← ContinuousLinearMap.map_smul]
      exact hinv _ (Ico_subset_Icc_self (octave_mem hq ht)) Q hQ _
  intro s t hs hst Q hQ
  obtain ⟨hp, hc⟩ := hμ s t hs hst
  haveI := hp
  haveI : IsProbabilityMeasure (push Q (μ s t)) :=
    Measure.isProbabilityMeasure_map (lin Q).continuous.aemeasurable
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [push, charFun_map_lin, hc, hc, hrotΨ t hQ, hrotΨ s hQ]

/-- **The knot data of a family with a rotation-invariant step are invariant**: the knot kernel's
transform is the limit of the partial products of `ϱ̂` (`prop:ladder-knot-kernel`(1)). -/
theorem ladderStar_exponent_orth (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) {ρ : Measure (Rd d)}
    {μ : ℝ → ℝ → Measure (Rd d)} (hlad : HasLadder q ρ μ) {Dst : SymLevyData d}
    (h1 : IsSymData (μ 0 1) Dst) (hrot : IsRotationInvariant ρ) : Dst.IsOrthInvariant := by
  obtain ⟨hsym, hcov, hstepρ⟩ := hlad
  haveI := hsym.1.isProbability 0 1 le_rfl zero_le_one
  have hK := kernelOrder_rd hd hsym
  have hkstep : ∀ ω : Rd d, charFun (μ 1 q) ω * charFun (μ 0 1) ω =
      charFun (μ 0 1) (q • ω) := by
    intro ω
    have hk : (μ 0 1).map (fun x => q • x) = μ 0 q := by
      have := cov_kernel hcov zero_le_one
      rwa [mul_one] at this
    rw [← charFun_kernel_mul μ hsym.1 zero_le_one hq.le, ← hk, charFun_map_smul]
  have hlim := tendsto_ladderProd hq (μ 1 q) hkstep continuous_charFun.continuousAt
    (by simp [charFun_zero]) fun ω => (hK.pos 1 zero_le_one ω).ne'
  intro Q hQ ω
  have hprod : ∀ M : ℕ, ladderProd q (μ 1 q) M (lin Qᵀ ω) = ladderProd q (μ 1 q) M ω := by
    intro M
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [hstepρ, ← ContinuousLinearMap.map_smul, charFun_orth_of_rotationInvariant hrot hQ]
  have h2 := hlim (lin Qᵀ ω)
  simp_rw [hprod] at h2
  have h3 := tendsto_nhds_unique h2 (hlim ω)
  rw [h1 (lin Qᵀ ω), h1 ω] at h3
  have h4 := Real.exp_injective (Complex.ofReal_injective h3)
  linarith

/-- **The uniform coupling**: a family with the ladder of `ϱ`, the knot data `D*`, the steps
`μ̂_{s,t} = e^{-(log_q t - log_q s)ψ_ϱ}` for `1 ≤ s ≤ t ≤ q`, isotropic if `ϱ` is rotation
invariant. -/
theorem uniform_coupling_family (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0) (Dρ : SymLevyData d)
    (hDρ : IsSymData ρ Dρ) (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) :
    ∃ μ : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ ∧
      IsSymData (μ 0 1) (ladderStarData hq Dρ hmom) ∧
      (∀ s t : ℝ, 1 ≤ s → s ≤ t → t ≤ q → ∀ ω : Rd d, charFun (μ s t) ω =
        ((Real.exp (-((Real.logb q t - Real.logb q s) * Dρ.exponent ω)) : ℝ) : ℂ)) ∧
      (IsRotationInvariant ρ → IsRotationInvariantLaws μ) := by
  have hl := isCouplingWeight_logb hq
  set Dst := ladderStarData hq Dρ hmom with hDst
  set D := couplingData Dst Dρ SymLevyData.zero (Real.logb q) (Real.logb q) with hD
  have hsyn : IsSynthesisData q D := isSynthesisData_uniform hq Dρ hmom
    (exists_exponent_ne_zero hne hDρ) hl fun s t hs hst _ => logb_strictMonoOn hq hs hst
  obtain ⟨⟨μ, hμ⟩, hfam⟩ := coupling_family hq hsyn ρ (charFun_uniform_step hq Dρ hmom hl hDρ)
  obtain ⟨hlad, h1, hstep⟩ := hfam μ hμ
  have hD1 : D 1 = Dst := couplingData_one Dst Dρ _ hl hl
  have h1' : IsSymData (μ 0 1) Dst := hD1 ▸ h1
  refine ⟨μ, hlad, h1', fun s t hs hst ht ω => ?_, fun hrot => ?_⟩
  · rw [hstep s t hs hst ht ω, hD, couplingData_exponent_of_mem hl hl ⟨hs.trans hst, ht⟩,
      couplingData_exponent_of_mem hl hl ⟨hs, hst.trans ht⟩, SymLevyData.zero_exponent]
    congr 3
    ring
  · have hstQ := ladderStar_exponent_orth hd hq hlad h1' hrot
    have hρQ := isOrthInvariant_of_rotationInvariant hrot hDρ
    exact isRotationInvariantLaws_of_octave_orth hq (fun u hu Q hQ ω => by
      rw [hD, couplingData_exponent_of_mem hl hl hu, couplingData_exponent_of_mem hl hl hu,
        hstQ Q hQ, hρQ Q hQ, SymLevyData.zero_exponent, SymLevyData.zero_exponent]) hμ

/-! ## Extreme data: every family is a relabelling -/

/-- **The steps of a family split the data of the step**: `μ_{1,t}` and `μ_{t,q}`, `t ∈ [1,q]`,
have data `E`, `F` with `E + F = D_ϱ`. -/
theorem ladder_step_split (hd : 1 ≤ d) {q : ℝ} {ρ : Measure (Rd d)}
    {Dρ : SymLevyData d} (hDρ : IsSymData ρ Dρ) {μ : ℝ → ℝ → Measure (Rd d)}
    (hlad : HasLadder q ρ μ) {t : ℝ} (ht : t ∈ Icc 1 q) :
    ∃ E F : SymLevyData d, IsSymData (μ 1 t) E ∧ IsSymData (μ t q) F ∧
      E.A + F.A = Dρ.A ∧ E.ν + F.ν = Dρ.ν := by
  obtain ⟨hsym, -, hρ⟩ := hlad
  obtain ⟨D, hD⟩ := family_structure_exists hd μ hsym
  have hdat := (family_structure_data hd μ hsym D hD).2
  obtain ⟨-, -, -, E, -, -, hE⟩ := hdat 1 t zero_le_one ht.1
  obtain ⟨-, -, -, F, -, -, hF⟩ := hdat t q (zero_le_one.trans ht.1) ht.2
  refine ⟨E, F, hE, hF, ?_⟩
  have hexp : ∀ ω : Rd d, (E.addSmul F 1).exponent ω = Dρ.exponent ω := by
    intro ω
    haveI := hsym.1.isProbability 1 t zero_le_one ht.1
    haveI := hsym.1.isProbability t q (zero_le_one.trans ht.1) ht.2
    have h := charFun_conv (μ := μ t q) (ν := μ 1 t) ω
    rw [← hsym.1.cascade 1 t q zero_le_one ht.1 ht.2, hρ, hDρ ω, hF ω, hE ω,
      ← Complex.ofReal_mul, ← Real.exp_add] at h
    have h' := Real.exp_injective (Complex.ofReal_injective h)
    rw [SymLevyData.addSmul_exponent, max_eq_left zero_le_one, one_mul]
    linarith
  have h2 := SymLevyData.eq_of_exponent hexp
  simp only [SymLevyData.addSmul, max_eq_left zero_le_one, one_smul, ENNReal.ofReal_one] at h2
  exact h2

/-- **Extreme data make every step a multiple**: `μ̂_{1,t} = e^{-cψ_ϱ}`, `c ≥ 0`, for `t ∈ [1,q]`,
when the data of the steps `μ_{1,t}`, `μ_{t,q}` lie in the cone of `P`. -/
theorem ladder_step_proportional (hd : 1 ≤ d) {q : ℝ} {ρ : Measure (Rd d)}
    {Dρ : SymLevyData d} (hDρ : IsSymData ρ Dρ) {P : SymLevyData d → Prop}
    (hext : Dρ.IsExtremeIn P) {μ : ℝ → ℝ → Measure (Rd d)} (hlad : HasLadder q ρ μ)
    (hP : ∀ t ∈ Icc 1 q, ∀ E F : SymLevyData d, IsSymData (μ 1 t) E → IsSymData (μ t q) F →
      P E ∧ P F) :
    ∀ t ∈ Icc 1 q, ∃ c : ℝ, 0 ≤ c ∧ ∀ ω : Rd d,
      charFun (μ 1 t) ω = ((Real.exp (-(c * Dρ.exponent ω)) : ℝ) : ℂ) := by
  intro t ht
  obtain ⟨E, F, hE, hF, hA, hν⟩ := ladder_step_split hd hDρ hlad ht
  obtain ⟨hPE, hPF⟩ := hP t ht E F hE hF
  obtain ⟨c, hc, hcA, hcν⟩ := hext E F hPE hPF hA hν
  exact ⟨c, hc, fun ω => by rw [hE ω, SymLevyData.exponent_of_smul hc hcA hcν]⟩

/-- **A family whose steps `μ_{1,t}` are `e^{-cψ_ϱ}` is the uniform coupling relabelled.** -/
theorem relabel_of_proportional (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) {ρ : Measure (Rd d)}
    {Dρ : SymLevyData d} (hDρ : IsSymData ρ Dρ) (hψ : ∃ ω : Rd d, Dρ.exponent ω ≠ 0)
    {μ μ' : ℝ → ℝ → Measure (Rd d)} (hlad : HasLadder q ρ μ) (hlad' : HasLadder q ρ μ')
    (hU : ∀ u ∈ Icc 1 q, ∀ ω : Rd d,
      charFun (μ 1 u) ω = ((Real.exp (-(Real.logb q u * Dρ.exponent ω)) : ℝ) : ℂ))
    (hprop : ∀ t ∈ Icc 1 q, ∃ c : ℝ, 0 ≤ c ∧ ∀ ω : Rd d,
      charFun (μ' 1 t) ω = ((Real.exp (-(c * Dρ.exponent ω)) : ℝ) : ℂ)) :
    ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (extendByZero g s) (extendByZero g t) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hsym, hcov, hρ⟩ := hlad
  obtain ⟨hsym', hcov', hρ'⟩ := hlad'
  obtain ⟨ω₀, hω₀⟩ := hψ
  have hψ0 : 0 < Dρ.exponent ω₀ := lt_of_le_of_ne (Dρ.exponent_nonneg ω₀) (Ne.symm hω₀)
  -- the weight `c(t)`, read at `ω₀`
  set c : ℝ → ℝ := fun t => -Real.log (charFun (μ' 1 t) ω₀).re / Dρ.exponent ω₀ with hcdef
  have hc : ∀ t ∈ Icc 1 q, ∀ ω : Rd d,
      charFun (μ' 1 t) ω = ((Real.exp (-(c t * Dρ.exponent ω)) : ℝ) : ℂ) := by
    intro t ht ω
    obtain ⟨c', -, hc'⟩ := hprop t ht
    have e : c t = c' := by
      simp only [hcdef]
      rw [hc' ω₀, Complex.ofReal_re, Real.log_exp, neg_neg, mul_div_assoc, div_self hψ0.ne',
        mul_one]
    rw [e]
    exact hc' ω
  have hc1 : c 1 = 0 := by
    simp only [hcdef]
    rw [hsym'.1.diag 1 zero_le_one, charFun_dirac]
    simp
  have hcq : c q = 1 := by
    simp only [hcdef]
    rw [hρ', hDρ ω₀, Complex.ofReal_re, Real.log_exp, neg_neg, div_self hψ0.ne']
  -- the steps inside the octave
  have hstep : ∀ s t : ℝ, s ∈ Icc 1 q → t ∈ Icc 1 q → s ≤ t → ∀ ω : Rd d,
      charFun (μ' s t) ω = ((Real.exp (-((c t - c s) * Dρ.exponent ω)) : ℝ) : ℂ) := by
    intro s t hs ht hst ω
    haveI := hsym'.1.isProbability s t (zero_le_one.trans hs.1) hst
    haveI := hsym'.1.isProbability 1 s zero_le_one hs.1
    have h := charFun_conv (μ := μ' s t) (ν := μ' 1 s) ω
    rw [← hsym'.1.cascade 1 s t zero_le_one hs.1 hst, hc t ht ω, hc s hs ω] at h
    have hne : ((Real.exp (-(c s * Dρ.exponent ω)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    refine mul_right_cancel₀ hne (h.symm.trans ?_)
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  -- `c` is strictly increasing, by (ND)
  have hcmono : StrictMonoOn c (Icc 1 q) := by
    intro s hs t ht hst
    by_contra hle
    rw [not_lt] at hle
    haveI := hsym'.1.isProbability s t (zero_le_one.trans hs.1) hst.le
    refine hsym'.2.1 s t (zero_le_one.trans hs.1) hst (eq_dirac_of_charFun_one fun ω => ?_)
    have hx0 : 0 ≤ (c s - c t) * Dρ.exponent ω :=
      mul_nonneg (sub_nonneg.2 hle) (Dρ.exponent_nonneg ω)
    have hn := norm_charFun_le_one (μ := μ' s t) ω
    rw [hstep s t hs ht hst.le ω, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_one_iff] at hn
    have h0 : (c t - c s) * Dρ.exponent ω = 0 := by nlinarith
    rw [hstep s t hs ht hst.le ω, h0, neg_zero, Real.exp_zero, Complex.ofReal_one]
  -- `c` is continuous, by (I2)
  have hcont : ContinuousOn c (Icc 1 q) := by
    have h1 : ContinuousOn (fun t => charFun (μ' 1 t) ω₀) (Icc 1 q) := by
      have h := hsym'.1.continuous ω₀
      have hmap : MapsTo (fun t : ℝ => ((1 : ℝ), t)) (Icc 1 q)
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} := fun t ht => ⟨zero_le_one, ht.1⟩
      exact h.comp (continuous_const.prodMk continuous_id).continuousOn hmap
    have h2 : ContinuousOn (fun t => (charFun (μ' 1 t) ω₀).re) (Icc 1 q) :=
      Complex.continuous_re.comp_continuousOn h1
    have h3 : ContinuousOn (fun t => Real.log (charFun (μ' 1 t) ω₀).re) (Icc 1 q) :=
      h2.log fun t ht => by
        rw [hc t ht ω₀, Complex.ofReal_re]
        exact (Real.exp_pos _).ne'
    exact h3.neg.div_const _
  have hcI : ∀ t ∈ Icc 1 q, c t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    have h1 := hcmono.monotoneOn ⟨le_rfl, hq.le⟩ ht ht.1
    have h2 := hcmono.monotoneOn ht ⟨hq.le, le_rfl⟩ ht.2
    rw [hc1] at h1
    rw [hcq] at h2
    exact ⟨h1, h2⟩
  -- the gauge `q^c`
  set φ : ℝ → ℝ := fun t => q ^ c t with hφ
  have hφc : ContinuousOn φ (Icc 1 q) :=
    continuousOn_const.rpow hcont fun _ _ => Or.inl hq0.ne'
  have hφm : StrictMonoOn φ (Icc 1 q) := fun s hs t ht hst =>
    Real.rpow_lt_rpow_of_exponent_lt hq (hcmono hs ht hst)
  have hφp : MapsTo φ (Icc 1 q) (Ioi 0) := fun t _ => Real.rpow_pos_of_pos hq0 _
  have hφq : φ q = q * φ 1 := by
    simp only [hφ, hcq, hc1, Real.rpow_one, Real.rpow_zero, mul_one]
  obtain ⟨g, hg, hgφ⟩ := (gauge_group_3 hq).2.2 φ hφc hφm hφp hφq
  have hgI : ∀ t ∈ Icc 1 q, g t ∈ Icc 1 q ∧ Real.logb q (g t) = c t := by
    intro t ht
    rw [hgφ ht]
    refine ⟨⟨Real.one_le_rpow hq.le (hcI t ht).1, ?_⟩, Real.logb_rpow hq0 hq.ne'⟩
    calc q ^ c t ≤ q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq.le (hcI t ht).2
      _ = q := Real.rpow_one q
  -- the knot kernels agree: both are the limit of the partial products of `ϱ̂`
  have hD1 : ∀ ω : Rd d, charFun (μ' 0 1) ω = charFun (μ 0 1) ω := by
    obtain ⟨D, hD⟩ := family_structure_exists hd μ hsym
    obtain ⟨D', hD'⟩ := family_structure_exists hd μ' hsym'
    have hDρ1 : IsSymData (μ 1 q) Dρ := by rw [hρ]; exact hDρ
    have hDρ1' : IsSymData (μ' 1 q) Dρ := by rw [hρ']; exact hDρ
    have h1 := (ladder_knot_kernel_1 hd hq μ hsym hcov Dρ (D 1) hDρ1 (hD 1 zero_le_one)).1
    have h1' := (ladder_knot_kernel_1 hd hq μ' hsym' hcov' Dρ (D' 1) hDρ1'
      (hD' 1 zero_le_one)).1
    intro ω
    have a := (h1 ω).1
    have b := (h1' ω).1
    rw [hρ] at a
    rw [hρ'] at b
    exact tendsto_nhds_unique b a
  -- the kernels agree on `[1, q]`
  have hkerI : ∀ u ∈ Icc 1 q, ∀ ω : Rd d, charFun (μ' 0 u) ω = charFun (μ 0 (g u)) ω := by
    intro u hu ω
    obtain ⟨hgu, hlog⟩ := hgI u hu
    rw [charFun_kernel_mul μ' hsym'.1 zero_le_one hu.1,
      charFun_kernel_mul μ hsym.1 zero_le_one hgu.1, hc u hu ω, hU _ hgu ω, hlog, hD1 ω]
  -- and everywhere, by covariance
  have hker : ∀ t : ℝ, 0 ≤ t → ∀ ω : Rd d,
      charFun (μ' 0 t) ω = charFun (μ 0 (extendByZero g t)) ω := by
    intro t ht ω
    rcases ht.eq_or_lt with h0 | htpos
    · subst h0
      rw [show extendByZero g 0 = 0 by simp [extendByZero], hsym'.1.diag 0 le_rfl,
        hsym.1.diag 0 le_rfl]
    · obtain ⟨n, hn, -⟩ := existsUnique_zpow_mul_mem_Ico hq htpos
      have hqn : 0 < q ^ n := zpow_pos hq0 n
      have hu0 : 0 < q ^ n * t := lt_of_lt_of_le one_pos hn.1
      have et : t = q ^ (-n) * (q ^ n * t) := by
        rw [zpow_neg, inv_mul_cancel_left₀ hqn.ne']
      have hext : extendByZero g t = q ^ (-n) * g (q ^ n * t) := by
        rw [extendByZero, if_neg htpos.ne']
        conv_lhs => rw [et]
        exact hg.zpow hq (-n) _ hu0
      have hgu0 : 0 ≤ g (q ^ n * t) := (hg.mapsTo hu0).le
      rw [hext]
      conv_lhs => rw [et]
      rw [kernel_zpow_of_cov hq hcov' (-n) _ hu0.le, kernel_zpow_of_cov hq hcov (-n) _ hgu0,
        charFun_map_smul, charFun_map_smul, hkerI _ ⟨hn.1, hn.2.le⟩ (q ^ (-n) • ω)]
  -- the steps, by (I1)
  have hK := kernelOrder_rd hd hsym'
  refine ⟨g, hg, fun s t hs hst => ?_⟩
  have h0s := extendByZero_nonneg hg hs
  have hmono := extendByZero_mono hg hs hst
  haveI := hsym'.1.isProbability s t hs hst
  haveI := hsym.1.isProbability _ _ h0s hmono
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  have h1 := charFun_kernel_mul μ' hsym'.1 hs hst ω
  have h2 := charFun_kernel_mul μ hsym.1 h0s hmono ω
  rw [hker t (hs.trans hst) ω, hker s hs ω, h2] at h1
  have hne : charFun (μ 0 (extendByZero g s)) ω ≠ 0 := by
    rw [← hker s hs ω]
    exact (hK.pos s hs ω).ne'
  exact (mul_right_cancel₀ hne h1).symm

/-- **`g₂ = g₁ ∘ g`** for some `g ∈ 𝒢_q`: the inverse of `g₁` composed with `g₂`. -/
theorem exists_gauge_comp_inv {q : ℝ} (hq : 1 < q) {g₁ g₂ : ℝ → ℝ} (hg₁ : IsInGaugeGroup q g₁)
    (hg₂ : IsInGaugeGroup q g₂) :
    ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
      ∀ t : ℝ, 0 ≤ t → extendByZero g₁ (extendByZero g t) = extendByZero g₂ t := by
  have hq0 : 0 < q := by linarith
  obtain ⟨ψ, hψ, hψχ, hχψ⟩ := isGauge_inverse (isGauge_extendByZero hg₁)
  have hψpos : ∀ u : ℝ, 0 < u → 0 < ψ u := fun u hu => isGauge_pos hψ hu
  have hχ : ∀ u : ℝ, 0 < u → extendByZero g₁ u = g₁ u := fun u hu => by
    rw [extendByZero, if_neg hu.ne']
  -- `ψ(qy) = qψ(y)`
  have hψq : ∀ y : ℝ, 0 < y → ψ (q * y) = q * ψ y := by
    intro y hy
    have hpy : 0 < ψ y := hψpos y hy
    have h1 : extendByZero g₁ (q * ψ y) = q * y := by
      rw [hχ _ (mul_pos hq0 hpy), hg₁.equivariant _ hpy, ← hχ _ hpy, hχψ y hy.le]
    rw [← h1, hψχ _ (mul_pos hq0 hpy).le]
  refine ⟨fun t => ψ (g₂ t), ⟨?_, ?_, ?_, ?_, ?_⟩, fun t ht => ?_⟩
  · intro a ha b hb hab
    exact hψ.2.1 (mem_Ici.2 (hg₂.mapsTo ha).le) (mem_Ici.2 (hg₂.mapsTo hb).le)
      (hg₂.strictMonoOn ha hb hab)
  · intro t ht
    exact hψpos _ (hg₂.mapsTo ht)
  · intro y hy
    have hy0 : 0 < y := hy
    obtain ⟨u, hu, hgu⟩ := hg₂.surjOn (hg₁.mapsTo hy)
    refine ⟨u, hu, ?_⟩
    change ψ (g₂ u) = y
    rw [hgu, ← hχ y hy0, hψχ y hy0.le]
  · exact (isGauge_continuousOn hψ).comp hg₂.continuousOn
      fun t ht => mem_Ici.2 (hg₂.mapsTo ht).le
  · intro t ht
    rw [hg₂.equivariant t ht, hψq _ (hg₂.mapsTo ht)]
  · rcases ht.eq_or_lt with h0 | hpos
    · subst h0
      simp [extendByZero]
    · have hg2 : 0 < g₂ t := hg₂.mapsTo hpos
      rw [show extendByZero (fun t => ψ (g₂ t)) t = ψ (g₂ t) by
          rw [extendByZero, if_neg hpos.ne'],
        hχψ _ hg2.le, extendByZero, if_neg hpos.ne']

/-- **Extreme data: two families with the ladder are relabellings of each other**, when the data
of their steps lie in the cone of `P`. -/
theorem ladder_relabel_of_extreme (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0) (Dρ : SymLevyData d)
    (hDρ : IsSymData ρ Dρ) (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤)
    {P : SymLevyData d → Prop} (hext : Dρ.IsExtremeIn P) {μ μ' : ℝ → ℝ → Measure (Rd d)}
    (hlad : HasLadder q ρ μ) (hlad' : HasLadder q ρ μ')
    (hP : ∀ t ∈ Icc 1 q, ∀ E F : SymLevyData d, IsSymData (μ 1 t) E → IsSymData (μ t q) F →
      P E ∧ P F)
    (hP' : ∀ t ∈ Icc 1 q, ∀ E F : SymLevyData d, IsSymData (μ' 1 t) E → IsSymData (μ' t q) F →
      P E ∧ P F) :
    ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (extendByZero g s) (extendByZero g t) := by
  obtain ⟨μ₀, hlad₀, -, hst₀, -⟩ := uniform_coupling_family hd hq ρ hne Dρ hDρ hmom
  have hU : ∀ u ∈ Icc 1 q, ∀ ω : Rd d,
      charFun (μ₀ 1 u) ω = ((Real.exp (-(Real.logb q u * Dρ.exponent ω)) : ℝ) : ℂ) := by
    intro u hu ω
    rw [hst₀ 1 u le_rfl hu.1 hu.2 ω, Real.logb_one, sub_zero]
  have hψ := exists_exponent_ne_zero hne hDρ
  obtain ⟨g₁, hg₁, hrel₁⟩ := relabel_of_proportional hd hq hDρ hψ hlad₀ hlad hU
    (ladder_step_proportional hd hDρ hext hlad hP)
  obtain ⟨g₂, hg₂, hrel₂⟩ := relabel_of_proportional hd hq hDρ hψ hlad₀ hlad' hU
    (ladder_step_proportional hd hDρ hext hlad' hP')
  obtain ⟨g, hg, hcomp⟩ := exists_gauge_comp_inv hq hg₁ hg₂
  refine ⟨g, hg, fun s t hs hst => ?_⟩
  rw [hrel₂ s t hs hst, hrel₁ _ _ (extendByZero_nonneg hg hs) (extendByZero_mono hg hs hst),
    hcomp s hs, hcomp t (hs.trans hst)]

/-! ## Data not extreme: the split coupling -/

/-- **Data not extreme: two families with the ladder that are not relabellings.** If
`D_ϱ = F + G` with `F` no multiple `cD_ϱ`, `c ≥ 0`, the split coupling of `F` and `G` is not the
uniform coupling relabelled by any `g ∈ 𝒢_q`; both are isotropic when `ϱ`, `F` and `G` are
invariant. -/
theorem ladder_split_not_relabel (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0) (Dρ : SymLevyData d)
    (hDρ : IsSymData ρ Dρ) (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤)
    (F G : SymLevyData d) (hA : F.A + G.A = Dρ.A) (hν : F.ν + G.ν = Dρ.ν)
    (hnp : ¬ ∃ c : ℝ, 0 ≤ c ∧ F.A = c • Dρ.A ∧ F.ν = ENNReal.ofReal c • Dρ.ν) :
    ∃ μ μ' : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ ∧ HasLadder q ρ μ' ∧
      (¬ ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (extendByZero g s) (extendByZero g t)) ∧
      (IsRotationInvariant ρ → F.IsOrthInvariant → G.IsOrthInvariant →
        IsRotationInvariantLaws μ ∧ IsRotationInvariantLaws μ') := by
  have hq0 : 0 < q := by linarith
  have hwa := isCouplingWeight_splitA hq
  have hwb := isCouplingWeight_splitB hq
  -- `F ≠ 0`, else `F = 0 · D_ϱ`; `G ≠ 0`, else `F = 1 · D_ϱ`
  obtain ⟨ωa, hωa⟩ : ∃ ω : Rd d, F.exponent ω ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h2 := SymLevyData.eq_of_exponent (E := F) (E' := SymLevyData.zero) fun ω => by
      rw [hcon ω, SymLevyData.zero_exponent]
    refine hnp ⟨0, le_rfl, ?_, ?_⟩
    · rw [h2.1, zero_smul]
      rfl
    · rw [h2.2, ENNReal.ofReal_zero, zero_smul]
      rfl
  obtain ⟨ωb, hωb⟩ : ∃ ω : Rd d, G.exponent ω ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h2 := SymLevyData.eq_of_exponent (E := G) (E' := SymLevyData.zero) fun ω => by
      rw [hcon ω, SymLevyData.zero_exponent]
    refine hnp ⟨1, zero_le_one, ?_, ?_⟩
    · rw [one_smul, ← hA, h2.1]
      exact (add_zero _).symm
    · rw [ENNReal.ofReal_one, one_smul, ← hν, h2.2]
      exact (add_zero _).symm
  have hωa' : 0 < F.exponent ωa := lt_of_le_of_ne (F.exponent_nonneg ωa) (Ne.symm hωa)
  have hωb' : 0 < G.exponent ωb := lt_of_le_of_ne (G.exponent_nonneg ωb) (Ne.symm hωb)
  -- the uniform coupling
  obtain ⟨μ, hlad, h1, hst, hrotU⟩ := uniform_coupling_family hd hq ρ hne Dρ hDρ hmom
  set Dst := ladderStarData hq Dρ hmom with hDst
  -- the split coupling
  have hsyn' : IsSynthesisData q (couplingData Dst F G (fun t => min 1 (2 * Real.logb q t))
      (fun t => max 0 (2 * Real.logb q t - 1))) := by
    refine isSynthesisData_coupling hq Dρ hmom F G hA hν hwa hwb fun s t hs hst ht => ?_
    have hsI : s ∈ Icc 1 q := ⟨hs, hst.le.trans ht⟩
    have htI : t ∈ Icc 1 q := ⟨hs.trans hst.le, ht⟩
    have hlt := logb_strictMonoOn hq hs hst
    have ha0 := hwa.mono hsI htI hst.le
    have hb0 := hwb.mono hsI htI hst.le
    rcases lt_or_ge (Real.logb q s) (1 / 2) with hhalf | hhalf
    · refine ⟨ωa, (add_pos_of_pos_of_nonneg (mul_pos ?_ hωa')
        (mul_nonneg (sub_nonneg.2 hb0) (G.exponent_nonneg ωa))).ne'⟩
      rw [sub_pos, min_eq_right (by linarith : 2 * Real.logb q s ≤ 1)]
      exact lt_min (by linarith) (by linarith)
    · refine ⟨ωb, (add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.2 ha0)
        (F.exponent_nonneg ωb)) (mul_pos ?_ hωb')).ne'⟩
      rw [sub_pos, max_eq_right (by linarith : 0 ≤ 2 * Real.logb q s - 1),
        max_eq_right (by linarith : 0 ≤ 2 * Real.logb q t - 1)]
      linarith
  have hρ' : ∀ ω : Rd d, charFun ρ ω = ((Real.exp (-((couplingData Dst F G
      (fun t => min 1 (2 * Real.logb q t)) (fun t => max 0 (2 * Real.logb q t - 1)) q).exponent ω -
      (couplingData Dst F G (fun t => min 1 (2 * Real.logb q t))
      (fun t => max 0 (2 * Real.logb q t - 1)) 1).exponent ω)) : ℝ) : ℂ) := by
    intro ω
    rw [couplingData_exponent_of_mem hwa hwb ⟨hq.le, le_rfl⟩,
      couplingData_exponent_of_mem hwa hwb ⟨le_rfl, hq.le⟩, hwa.top, hwb.top, hwa.one, hwb.one,
      hDρ ω, SymLevyData.exponent_of_add hA hν]
    congr 3
    ring
  obtain ⟨⟨μ', hμ'⟩, hfam'⟩ := coupling_family hq hsyn' ρ hρ'
  obtain ⟨hlad', h1', hst'⟩ := hfam' μ' hμ'
  have h1st : IsSymData (μ' 0 1) Dst := by
    rw [couplingData_one Dst _ _ hwa hwb] at h1'
    exact h1'
  refine ⟨μ, μ', hlad, hlad', ?_, fun hrot hF hG => ⟨hrotU hrot, ?_⟩⟩
  rotate_left
  · -- the split coupling is isotropic
    have hstQ := ladderStar_exponent_orth hd hq hlad' h1st hrot
    exact isRotationInvariantLaws_of_octave_orth hq (fun u hu Q hQ ω => by
      rw [couplingData_exponent_of_mem hwa hwb hu, couplingData_exponent_of_mem hwa hwb hu,
        hstQ Q hQ, hF Q hQ, hG Q hQ]) hμ'
  -- it is not a relabelling of the uniform one
  rintro ⟨g, hg, hrel⟩
  have hext1 : extendByZero g 1 = g 1 := by simp [extendByZero]
  have hext0 : extendByZero g 0 = 0 := by simp [extendByZero]
  -- `g` fixes `1`: the two knot kernels agree, and `t ↦ μ_t` is injective
  have hg1 : g 1 = 1 := by
    have hpos : 0 < g 1 := hg.mapsTo (mem_Ioi.2 one_pos)
    have hrel1 := hrel 0 1 le_rfl zero_le_one
    rw [hext0, hext1] at hrel1
    have hk : μ' 0 1 = μ 0 1 := by
      haveI := hlad.1.1.isProbability 0 1 le_rfl zero_le_one
      haveI := hlad'.1.1.isProbability 0 1 le_rfl zero_le_one
      exact Measure.ext_of_charFun (funext fun ω => by rw [h1st ω, h1 ω])
    have hinj := (family_structure_monotone hd μ hlad.1).1
    exact hinj (mem_Ici.2 hpos.le) (mem_Ici.2 zero_le_one) (hrel1.symm.trans hk)
  -- at `√q`
  set t : ℝ := q ^ (1 / 2 : ℝ) with ht
  have hlogt : Real.logb q t = 1 / 2 := by
    rw [ht, Real.logb_rpow hq0 hq.ne']
  have ht1 : 1 < t := Real.one_lt_rpow hq (by norm_num)
  have htq : t < q := by
    calc t < q ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hq (by norm_num)
      _ = q := Real.rpow_one q
  have htI : t ∈ Icc 1 q := ⟨ht1.le, htq.le⟩
  set u := g t with hu
  have hu1 : 1 < u := by
    have := hg.strictMonoOn (mem_Ioi.2 one_pos) (mem_Ioi.2 (lt_trans one_pos ht1)) ht1
    rwa [hg1] at this
  have huq : u < q := by
    have h2 := hg.strictMonoOn (mem_Ioi.2 (lt_trans one_pos ht1)) (mem_Ioi.2 hq0) htq
    have h3 := hg.equivariant 1 one_pos
    rw [mul_one, hg1, mul_one] at h3
    rwa [h3] at h2
  have hrelt := hrel 1 t zero_le_one ht1.le
  have hextt : extendByZero g t = u := by
    rw [extendByZero, if_neg (lt_trans one_pos ht1).ne']
  rw [hext1, hg1, hextt] at hrelt
  -- the step `μ'_{1,√q}` has the exponent `ψ_F`, and `μ_{1,u}` has `(log_q u) ψ_ϱ`
  have hexp : ∀ ω : Rd d, F.exponent ω = Real.logb q u * Dρ.exponent ω := by
    intro ω
    have h2 := (hst' 1 t le_rfl ht1.le htq.le ω).symm.trans
      ((congrArg (fun m => charFun m ω) hrelt).trans (hst 1 u le_rfl hu1.le huq.le ω))
    have h3 := Real.exp_injective (Complex.ofReal_injective h2)
    rw [couplingData_exponent_of_mem hwa hwb htI, couplingData_exponent_of_mem hwa hwb
      ⟨le_rfl, hq.le⟩, hlogt, Real.logb_one] at h3
    norm_num at h3
    linarith
  have hc0 : 0 ≤ Real.logb q u := Real.logb_nonneg hq hu1.le
  exact hnp ⟨Real.logb q u, hc0, SymLevyData.smul_of_exponent hc0 hexp⟩

/-! ## `prop:ladder-knot-kernel`(2), uniqueness up to `𝒢_q` -/

/-- **`prop:ladder-knot-kernel`(2), uniqueness up to `𝒢_q`.** For a symmetric infinitely divisible
`ϱ ≠ δ₀` with the logarithmic moment, any two families with the ladder of `ϱ` are relabellings of
each other by elements of `𝒢_q` if and only if the data `D_ϱ` span an extreme ray of the cone of
symmetric data. -/
theorem ladder_knot_kernel_2_unique_iff (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0) (Dρ : SymLevyData d)
    (hDρ : IsSymData ρ Dρ) (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) :
    (∀ μ μ' : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ → HasLadder q ρ μ' →
      ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (extendByZero g s) (extendByZero g t)) ↔
      Dρ.IsExtremeIn fun _ => True := by
  constructor
  · intro huniq F G _ _ hA hν
    by_contra hnp
    obtain ⟨μ, μ', hlad, hlad', hnot, -⟩ :=
      ladder_split_not_relabel hd hq ρ hne Dρ hDρ hmom F G hA hν hnp
    exact hnot (huniq μ μ' hlad hlad')
  · intro hext μ μ' hlad hlad'
    exact ladder_relabel_of_extreme hd hq ρ hne Dρ hDρ hmom hext hlad hlad'
      (fun _ _ _ _ _ _ => ⟨trivial, trivial⟩) (fun _ _ _ _ _ _ => ⟨trivial, trivial⟩)

/-- **`prop:ladder-knot-kernel`(2), uniqueness up to `𝒢_q` among isotropic families.** For `ϱ` as
in `ladder_knot_kernel_2_unique_iff` and rotation invariant, any two isotropic families with the
ladder of `ϱ` are relabellings of each other by elements of `𝒢_q` if and only if `D_ϱ` spans an
extreme ray of the cone of the data invariant under `O(d)`. -/
theorem ladder_knot_kernel_2_unique_iff_rot (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q)
    (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0)
    (hrot : IsRotationInvariant ρ) (Dρ : SymLevyData d) (hDρ : IsSymData ρ Dρ)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) :
    (∀ μ μ' : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ → IsRotationInvariantLaws μ →
      HasLadder q ρ μ' → IsRotationInvariantLaws μ' →
      ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (extendByZero g s) (extendByZero g t)) ↔
      Dρ.IsExtremeIn SymLevyData.IsOrthInvariant := by
  constructor
  · intro huniq F G hF hG hA hν
    by_contra hnp
    obtain ⟨μ, μ', hlad, hlad', hnot, hiso⟩ :=
      ladder_split_not_relabel hd hq ρ hne Dρ hDρ hmom F G hA hν hnp
    obtain ⟨hi, hi'⟩ := hiso hrot hF hG
    exact hnot (huniq μ μ' hlad hi hlad' hi')
  · intro hext μ μ' hlad hi hlad' hi'
    refine ladder_relabel_of_extreme hd hq ρ hne Dρ hDρ hmom hext hlad hlad'
      (fun t ht E F hE hF => ⟨?_, ?_⟩) (fun t ht E F hE hF => ⟨?_, ?_⟩)
    · exact isOrthInvariant_of_rotationInvariant (hi 1 t zero_le_one ht.1) hE
    · exact isOrthInvariant_of_rotationInvariant (hi t q (zero_le_one.trans ht.1) ht.2) hF
    · exact isOrthInvariant_of_rotationInvariant (hi' 1 t zero_le_one ht.1) hE
    · exact isOrthInvariant_of_rotationInvariant (hi' t q (zero_le_one.trans ht.1) ht.2) hF

end Pyramids
