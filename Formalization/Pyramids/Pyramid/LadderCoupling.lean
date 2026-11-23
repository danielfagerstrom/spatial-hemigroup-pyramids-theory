/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.LadderKnot
import Pyramids.Pyramid.LatticeStrata
import AffineHemigroup.SimilarityLine

/-!
# `prop:ladder-knot-kernel`(2): the couplings

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:ladder-knot-kernel`. Wave 3a:
`ladder_knot_kernel_2`, `ladder_knot_kernel_2_not_unique` and `ladder_knot_kernel_2_split` moved
here from `PyramidsSkeleton.Ch03Pyramid`, unchanged in name. Their proofs do not use the
hypotheses that `ϱ` is symmetric and infinitely divisible, which the data `D_ϱ` already carry;
`_not_unique` does not use `1 ≤ d`; `_split` does not use `ϱ ≠ δ₀` (it follows from `ν_a ≠ 0`)
nor the measurability of `B_a`. All were dropped (2026-11-14, a strengthening).

Wave 3b (on the VM, 2026-11-15): the proof of `ladder_knot_kernel_2_split` became
`ladder_knot_kernel_2_split_rot`, which also gives the isotropy of both families when the data are
invariant under the isometries (`isRotationInvariantLaws_of_octave`); `_split` is read off it, its
statement unchanged. `thm:selection-stratum-two`(1) reads the isotropy.
`SymLevyData.exponent_isometry` moved here from `LadderClassA.lean`, unchanged.

## The route

* **A coupling** is the data `D_t = D* + a(t) F + b(t) G` on `[1, q]`, with
  `D* = (A_ϱ/(q² - 1), ν*)` the knot data, `F + G = D_ϱ`, and weights `a, b` continuous and
  nondecreasing from `0` at `1` to `1` at `q` (`couplingData`). `lem:synthesis` applies
  (`isSynthesisData_coupling`): the exponent is `Ψ* + a(t)ψ_F + b(t)ψ_G`, continuous in `t`;
  the increments are positive, and nonzero when `(a(t) - a(s))ψ_F + (b(t) - b(s))ψ_G ≢ 0`;
  and the gluing is `D_q ν* = ν_ϱ + ν*` (`map_ladderNuStar`) with
  `A_ϱ/(q² - 1) + A_ϱ = q² A_ϱ/(q² - 1)`. The family has the step `μ_{1,q} = ϱ` and the knot data
  `D*` (`coupling_family`).
* **The uniform coupling**: `F = D_ϱ`, `G = 0`, `a = b = log_q`. **Isotropy**: if `ϱ` is rotation
  invariant, so is `ψ_ϱ`; the knot kernel's transform is the limit of the partial products
  (`prop:ladder-knot-kernel`(1)), each rotation invariant, so `Ψ*` is too, and with it every
  exponent of the family. No invariance of the data is read.
* **Not unique**: the uniform coupling and the one with `a = b = log_q²` differ at `t = √q`.
* **The split coupling**: `F = (A_ϱ/2, ν_a)`, `G = (A_ϱ/2, ν_b)`, `a = 1 ∧ 2log_q`,
  `b = 0 ∨ (2log_q - 1)`. A relabelling `g` with `μ^{split}_{s,t} = μ^{unif}_{g(s),g(t)}` would fix
  `1` (the kernels are injective in `t`), and the step `μ^{split}_{1,√q}`, of exponent `ψ_a`, would
  be `μ^{unif}_{1,g(√q)}`, of exponent `log_q g(√q) · ψ_ϱ`; the uniqueness of the data gives
  `ν_a = c ν_ϱ`, false on `B_b`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace MatrixOrder Matrix

variable {d : ℕ}

/-! ## Sums of data -/

/-- If `F + G = H` as data, the exponents add. -/
theorem SymLevyData.exponent_of_add {F G H : SymLevyData d} (hA : F.A + G.A = H.A)
    (hν : F.ν + G.ν = H.ν) (ω : Rd d) : H.exponent ω = F.exponent ω + G.exponent ω := by
  simp only [SymLevyData.exponent, pairExponent]
  rw [← hA, ← hν, quad_add, integral_add_measure (F.integrable_one_sub_cos ω)
    (G.integrable_one_sub_cos ω)]
  ring

/-- **`E + c F`**, the weight read as `max c 0`. -/
noncomputable def SymLevyData.addSmul (E F : SymLevyData d) (c : ℝ) : SymLevyData d where
  A := E.A + max c 0 • F.A
  ν := E.ν + ENNReal.ofReal c • F.ν
  A_posSemidef := E.A_posSemidef.add (F.A_posSemidef.smul (le_max_right c 0))
  ν_zero := by simp [E.ν_zero, F.ν_zero]
  ν_integrable := by
    rw [lintegral_add_measure, lintegral_smul_measure]
    exact ENNReal.add_ne_top.2 ⟨E.ν_integrable,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top F.ν_integrable⟩
  ν_symm := by rw [Measure.map_add _ _ measurable_neg, Measure.map_smul, E.ν_symm, F.ν_symm]

theorem SymLevyData.addSmul_exponent (E F : SymLevyData d) (c : ℝ) (ω : Rd d) :
    (E.addSmul F c).exponent ω = E.exponent ω + max c 0 * F.exponent ω := by
  simp only [SymLevyData.exponent, pairExponent, SymLevyData.addSmul]
  rw [quad_add, quad_smul, integral_add_measure (E.integrable_one_sub_cos ω)
    ((F.integrable_one_sub_cos ω).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
    ENNReal.toReal_ofReal', smul_eq_mul]
  ring

theorem SymLevyData.addSmul_zero (E F : SymLevyData d) : E.addSmul F 0 = E :=
  SymLevyData.ext' (by simp [SymLevyData.addSmul]) (by simp [SymLevyData.addSmul])

/-- A law other than `δ₀` with data `D` has `Ψ_D ≢ 0`. -/
theorem exists_exponent_ne_zero {ρ : Measure (Rd d)} [IsProbabilityMeasure ρ]
    (hne : ρ ≠ Measure.dirac 0) {D : SymLevyData d} (hD : IsSymData ρ D) :
    ∃ ω : Rd d, D.exponent ω ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hne (eq_dirac_of_charFun_one fun ω => by rw [hD ω, hcon ω]; simp)

/-- Nonzero data have a nonzero exponent (A39(ii), (iii)). -/
theorem SymLevyData.exists_exponent_ne_zero {D : SymLevyData d} (hν : D.ν ≠ 0) :
    ∃ ω : Rd d, D.exponent ω ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h := (SymLevyData.eq_of_exponent (E := D) (E' := SymLevyData.zero) fun ω => by
    rw [hcon ω, SymLevyData.zero_exponent]).2
  exact hν h

/-! ## Couplings -/

/-- **The weights of a coupling**: continuous and nondecreasing on `[1, q]`, from `0` to `1`. -/
structure IsCouplingWeight (q : ℝ) (a : ℝ → ℝ) : Prop where
  cont : ContinuousOn a (Icc 1 q)
  mono : MonotoneOn a (Icc 1 q)
  one : a 1 = 0
  top : a q = 1

theorem IsCouplingWeight.nonneg {q : ℝ} {a : ℝ → ℝ} (h : IsCouplingWeight q a) {t : ℝ}
    (ht : t ∈ Icc 1 q) : 0 ≤ a t := by
  have := h.mono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  rwa [h.one] at this

/-- **The coupling** `D_t = D* + a(t) F + b(t) G`. -/
noncomputable def couplingData (Dst F G : SymLevyData d) (a b : ℝ → ℝ) (t : ℝ) : SymLevyData d :=
  (Dst.addSmul F (a t)).addSmul G (b t)

theorem couplingData_exponent (Dst F G : SymLevyData d) (a b : ℝ → ℝ) (t : ℝ) (ω : Rd d) :
    (couplingData Dst F G a b t).exponent ω =
      Dst.exponent ω + max (a t) 0 * F.exponent ω + max (b t) 0 * G.exponent ω := by
  rw [couplingData, SymLevyData.addSmul_exponent, SymLevyData.addSmul_exponent]

theorem couplingData_exponent_of_mem {q : ℝ} {Dst F G : SymLevyData d} {a b : ℝ → ℝ}
    (ha : IsCouplingWeight q a) (hb : IsCouplingWeight q b) {t : ℝ} (ht : t ∈ Icc 1 q)
    (ω : Rd d) : (couplingData Dst F G a b t).exponent ω =
      Dst.exponent ω + a t * F.exponent ω + b t * G.exponent ω := by
  rw [couplingData_exponent, max_eq_left (ha.nonneg ht), max_eq_left (hb.nonneg ht)]

theorem couplingData_one {q : ℝ} (Dst F G : SymLevyData d) {a b : ℝ → ℝ}
    (ha : IsCouplingWeight q a) (hb : IsCouplingWeight q b) :
    couplingData Dst F G a b 1 = Dst := by
  rw [couplingData, ha.one, hb.one, SymLevyData.addSmul_zero, SymLevyData.addSmul_zero]

/-- **`lem:synthesis` applies to a coupling.** -/
theorem isSynthesisData_coupling {q : ℝ} (hq : 1 < q) (Dρ : SymLevyData d)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) (F G : SymLevyData d)
    (hA : F.A + G.A = Dρ.A) (hν : F.ν + G.ν = Dρ.ν) {a b : ℝ → ℝ} (ha : IsCouplingWeight q a)
    (hb : IsCouplingWeight q b)
    (hne : ∀ s t : ℝ, 1 ≤ s → s < t → t ≤ q →
      ∃ ω : Rd d, (a t - a s) * F.exponent ω + (b t - b s) * G.exponent ω ≠ 0) :
    IsSynthesisData q (couplingData (ladderStarData hq Dρ hmom) F G a b) := by
  have hq0 : 0 < q := by linarith
  set Dst := ladderStarData hq Dρ hmom with hDst
  set D := couplingData Dst F G a b with hD
  have hmaxa : ∀ t ∈ Icc 1 q, max (a t) 0 = a t := fun t ht => max_eq_left (ha.nonneg ht)
  have hmaxb : ∀ t ∈ Icc 1 q, max (b t) 0 = b t := fun t ht => max_eq_left (hb.nonneg ht)
  refine ⟨fun ω => ?_, fun s t hs hst ht => ?_, ?_⟩
  · -- continuity
    have h1 : ContinuousOn (fun t => Dst.exponent ω + a t * F.exponent ω + b t * G.exponent ω)
        (Icc 1 q) :=
      (continuousOn_const.add (ha.cont.mul continuousOn_const)).add
        (hb.cont.mul continuousOn_const)
    refine h1.congr fun t ht => ?_
    exact couplingData_exponent_of_mem ha hb ht ω
  · have hsI : s ∈ Icc 1 q := ⟨hs, hst.le.trans ht⟩
    have htI : t ∈ Icc 1 q := ⟨hs.trans hst.le, ht⟩
    have has : a s ≤ a t := ha.mono hsI htI hst.le
    have hbs : b s ≤ b t := hb.mono hsI htI hst.le
    refine ⟨?_, ?_, ?_⟩
    · -- the Gaussian parts increase
      have e : (D t).A - (D s).A = (a t - a s) • F.A + (b t - b s) • G.A := by
        simp only [hD, couplingData, SymLevyData.addSmul, hmaxa s hsI, hmaxa t htI,
          hmaxb s hsI, hmaxb t htI, sub_smul]
        abel
      rw [e]
      exact (F.A_posSemidef.smul (sub_nonneg.2 has)).add
        (G.A_posSemidef.smul (sub_nonneg.2 hbs))
    · -- the measures increase
      intro B
      simp only [hD, couplingData, SymLevyData.addSmul, Measure.add_apply,
        Measure.smul_apply, smul_eq_mul]
      gcongr
    · -- the increments are nonzero
      intro heq
      obtain ⟨ω, hω⟩ := hne s t hs hst ht
      have hDeq : D s = D t := SymLevyData.ext' (Prod.mk.inj heq).1 (Prod.mk.inj heq).2
      have h1 := congrArg (fun E : SymLevyData d => E.exponent ω) hDeq
      rw [hD, couplingData_exponent_of_mem ha hb hsI, couplingData_exponent_of_mem ha hb htI]
        at h1
      exact hω (by linarith)
  · -- the gluing
    have h1 : D 1 = Dst := couplingData_one Dst F G ha hb
    have hqI : q ∈ Icc 1 q := ⟨hq.le, le_rfl⟩
    have hq21 : q ^ 2 - 1 ≠ 0 := by nlinarith
    refine ⟨?_, ?_⟩
    · rw [h1]
      simp only [hD, couplingData, SymLevyData.addSmul, ha.top, hb.top, hDst, ladderStarData]
      rw [max_eq_left zero_le_one, one_smul, one_smul, add_assoc, hA, smul_smul]
      have e : q ^ 2 * (q ^ 2 - 1)⁻¹ = (q ^ 2 - 1)⁻¹ + 1 := by
        field_simp
        ring
      rw [e, add_smul, one_smul]
    · rw [h1]
      simp only [hD, couplingData, SymLevyData.addSmul, ha.top, hb.top, ENNReal.ofReal_one,
        one_smul, hDst, ladderStarData]
      rw [map_ladderNuStar hq0, add_assoc, hν, add_comm]

/-- The exponent of the family at `u ∈ [1, q]` is that of the data. -/
theorem octaveExponent_of_mem {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d}
    (hD : IsSynthesisData q D) {u : ℝ} (hu : u ∈ Icc 1 q) (ω : Rd d) :
    octaveExponent q D u ω = (D u).exponent ω := by
  have h := octaveExponent_at hq hD 0 hu ω
  simpa using h

/-- **The family of a coupling**: laws exist; any such laws form a family with the step
`μ_{1,q} = ϱ`, the knot data `D_1`, and the steps `μ_{s,t}`, `1 ≤ s ≤ t ≤ q`, of exponent
`Ψ_t - Ψ_s`. -/
theorem coupling_family {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d}
    (hD : IsSynthesisData q D) (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    (hρ : ∀ ω : Rd d, charFun ρ ω = ((Real.exp (-((D q).exponent ω - (D 1).exponent ω)) : ℝ) : ℂ)) :
    (∃ μ : ℝ → ℝ → Measure (Rd d), IsExponentLaws (octaveExponent q D) μ) ∧
      ∀ μ : ℝ → ℝ → Measure (Rd d), IsExponentLaws (octaveExponent q D) μ →
        HasLadder q ρ μ ∧ IsSymData (μ 0 1) (D 1) ∧
          ∀ s t : ℝ, 1 ≤ s → s ≤ t → t ≤ q → ∀ ω : Rd d,
            charFun (μ s t) ω = ((Real.exp (-((D t).exponent ω - (D s).exponent ω)) : ℝ) : ℂ) := by
  obtain ⟨-, hex, hfam⟩ := synthesis hq D hD
  refine ⟨hex, fun μ hμ => ?_⟩
  obtain ⟨hsym, hcov⟩ := hfam μ hμ
  have h1I : (1 : ℝ) ∈ Icc 1 q := ⟨le_rfl, hq.le⟩
  have hqI : q ∈ Icc 1 q := ⟨hq.le, le_rfl⟩
  have hstep : ∀ s t : ℝ, 1 ≤ s → s ≤ t → t ≤ q → ∀ ω : Rd d,
      charFun (μ s t) ω = ((Real.exp (-((D t).exponent ω - (D s).exponent ω)) : ℝ) : ℂ) := by
    intro s t hs hst ht ω
    rw [(hμ s t (zero_le_one.trans hs) hst).2 ω,
      octaveExponent_of_mem hq hD ⟨hs.trans hst, ht⟩,
      octaveExponent_of_mem hq hD ⟨hs, hst.trans ht⟩]
  refine ⟨⟨hsym, hcov, ?_⟩, fun ω => ?_, hstep⟩
  · haveI := (hμ 1 q zero_le_one hq.le).1
    exact Measure.ext_of_charFun (funext fun ω => by rw [hstep 1 q le_rfl hq.le le_rfl, hρ])
  · rw [(hμ 0 1 le_rfl zero_le_one).2 ω, octaveExponent_zero_left, sub_zero,
      octaveExponent_of_mem hq hD h1I]

/-! ## The uniform coupling -/

theorem isCouplingWeight_logb {q : ℝ} (hq : 1 < q) : IsCouplingWeight q (Real.logb q) := by
  have hq0 : 0 < q := by linarith
  refine ⟨?_, ?_, Real.logb_one, Real.logb_self_eq_one hq⟩
  · exact (Real.continuousOn_logb).mono fun t ht => by
      simp only [mem_compl_iff, mem_singleton_iff]
      exact (lt_of_lt_of_le one_pos ht.1).ne'
  · intro s hs t ht hst
    exact Real.logb_le_logb_of_le hq (lt_of_lt_of_le one_pos hs.1) hst

theorem logb_strictMonoOn {q : ℝ} (hq : 1 < q) {s t : ℝ} (hs : 1 ≤ s) (hst : s < t) :
    Real.logb q s < Real.logb q t :=
  Real.logb_lt_logb hq (lt_of_lt_of_le one_pos hs) hst

theorem isCouplingWeight_logb_sq {q : ℝ} (hq : 1 < q) :
    IsCouplingWeight q (fun t => Real.logb q t ^ 2) := by
  have hl := isCouplingWeight_logb hq
  refine ⟨hl.cont.pow 2, fun s hs t ht hst => ?_, by simp [hl.one], by simp [hl.top]⟩
  exact pow_le_pow_left₀ (hl.nonneg hs) (hl.mono hs ht hst) 2

/-- The uniform coupling's hypotheses, for a weight `a` strictly increasing on `[1,q]`. -/
theorem isSynthesisData_uniform {q : ℝ} (hq : 1 < q) (Dρ : SymLevyData d)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) (hψ : ∃ ω : Rd d, Dρ.exponent ω ≠ 0)
    {a : ℝ → ℝ} (ha : IsCouplingWeight q a)
    (hstrict : ∀ s t : ℝ, 1 ≤ s → s < t → t ≤ q → a s < a t) :
    IsSynthesisData q (couplingData (ladderStarData hq Dρ hmom) Dρ SymLevyData.zero a a) := by
  refine isSynthesisData_coupling hq Dρ hmom Dρ SymLevyData.zero (by simp [SymLevyData.zero])
    (by simp [SymLevyData.zero]) ha ha fun s t hs hst ht => ?_
  obtain ⟨ω, hω⟩ := hψ
  refine ⟨ω, ?_⟩
  rw [SymLevyData.zero_exponent, mul_zero, add_zero]
  exact mul_ne_zero (sub_ne_zero.2 (hstrict s t hs hst ht).ne') hω

/-- The uniform coupling's step is `ϱ`. -/
theorem charFun_uniform_step {q : ℝ} (hq : 1 < q) (Dρ : SymLevyData d)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) {a : ℝ → ℝ}
    (ha : IsCouplingWeight q a) {ρ : Measure (Rd d)} (hDρ : IsSymData ρ Dρ) (ω : Rd d) :
    charFun ρ ω = ((Real.exp (-((couplingData (ladderStarData hq Dρ hmom) Dρ SymLevyData.zero
      a a q).exponent ω - (couplingData (ladderStarData hq Dρ hmom) Dρ SymLevyData.zero
      a a 1).exponent ω)) : ℝ) : ℂ) := by
  rw [couplingData_exponent_of_mem ha ha ⟨hq.le, le_rfl⟩, couplingData_exponent_of_mem ha ha
    ⟨le_rfl, hq.le⟩, ha.top, ha.one, hDρ ω, SymLevyData.zero_exponent]
  congr 3
  ring

/-! ## Isotropy from the data -/

/-- **Data `(cI, ν)` with `ν` invariant under `Q`** have an exponent invariant under `Q`. -/
theorem SymLevyData.exponent_isometry (D : SymLevyData d) {c : ℝ} (hA : D.A = c • (1 : Mat d))
    (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (hν : D.ν.map Q = D.ν) (ω : Rd d) :
    D.exponent (Q ω) = D.exponent ω := by
  simp only [SymLevyData.exponent, pairExponent, hA, quad_smul, quad_one,
    LinearIsometryEquiv.norm_map]
  congr 1
  conv_lhs => rw [← hν]
  rw [integral_map Q.continuous.measurable.aemeasurable (by fun_prop)]
  simp only [LinearIsometryEquiv.inner_map_map]

/-- **Isotropy from the octave**: if every exponent `(D u).exponent`, `u ∈ [1,q]`, is invariant
under the isometries, every family of laws with the octave's exponents is rotation invariant. -/
theorem isRotationInvariantLaws_of_octave {q : ℝ} (hq : 1 < q) {D : ℝ → SymLevyData d}
    (hinv : ∀ u ∈ Icc 1 q, ∀ R : Rd d ≃ₗᵢ[ℝ] Rd d, ∀ ω : Rd d,
      (D u).exponent (R ω) = (D u).exponent ω)
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
      exact hinv _ (Ico_subset_Icc_self (octave_mem hq ht))
        (orthIsometry (transpose_mem_orthSet hQ)) _
  intro s t hs hst Q hQ
  obtain ⟨hp, hc⟩ := hμ s t hs hst
  haveI := hp
  haveI : IsProbabilityMeasure (push Q (μ s t)) :=
    Measure.isProbabilityMeasure_map (lin Q).continuous.aemeasurable
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [push, charFun_map_lin, hc, hc, hrotΨ t hQ, hrotΨ s hQ]

/-- A coupling of invariant data has invariant exponents on `[1, q]`. -/
theorem couplingData_exponent_isometry {q : ℝ} {Dst F G : SymLevyData d} {a b : ℝ → ℝ}
    (ha : IsCouplingWeight q a) (hb : IsCouplingWeight q b)
    (hst : ∀ R : Rd d ≃ₗᵢ[ℝ] Rd d, ∀ ω, Dst.exponent (R ω) = Dst.exponent ω)
    (hF : ∀ R : Rd d ≃ₗᵢ[ℝ] Rd d, ∀ ω, F.exponent (R ω) = F.exponent ω)
    (hG : ∀ R : Rd d ≃ₗᵢ[ℝ] Rd d, ∀ ω, G.exponent (R ω) = G.exponent ω) :
    ∀ u ∈ Icc 1 q, ∀ R : Rd d ≃ₗᵢ[ℝ] Rd d, ∀ ω : Rd d,
      (couplingData Dst F G a b u).exponent (R ω) = (couplingData Dst F G a b u).exponent ω := by
  intro u hu R ω
  rw [couplingData_exponent_of_mem ha hb hu, couplingData_exponent_of_mem ha hb hu, hst, hF, hG]

/-! ## `prop:ladder-knot-kernel`(2) -/

/-- A rotation-invariant law has a rotation-invariant transform. -/
theorem charFun_orth_of_rotationInvariant {ρ : Measure (Rd d)} (hrot : IsRotationInvariant ρ)
    {Q : Mat d} (hQ : Q ∈ orthSet d) (ω : Rd d) : charFun ρ (lin Qᵀ ω) = charFun ρ ω := by
  have h := charFun_map_lin Q ρ ω
  have hmap : ρ.map (lin Q) = ρ := hrot Q hQ
  rw [hmap] at h
  exact h.symm

/-- **`prop:ladder-knot-kernel`(2), existence.** A symmetric infinitely divisible `ϱ ≠ δ₀` with the
logarithmic moment is the step `μ_{1,q}` of some symmetric `q`-covariant family with `S_q t = qt`,
whose knot kernel has the data `(A_ϱ/(q² - 1), ν*)` of (1), and which is isotropic if `ϱ` is
rotation invariant. -/
theorem ladder_knot_kernel_2 (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0) (Dρ : SymLevyData d)
    (hDρ : IsSymData ρ Dρ) (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) :
    ∃ μ : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ ∧
      (∃ D1 : SymLevyData d, D1.A = (q ^ 2 - 1)⁻¹ • Dρ.A ∧ D1.ν = ladderNuStar q Dρ.ν ∧
        IsSymData (μ 0 1) D1) ∧
      (IsRotationInvariant ρ → IsRotationInvariantLaws μ) := by
  have hq0 : 0 < q := by linarith
  have hl := isCouplingWeight_logb hq
  set Dst := ladderStarData hq Dρ hmom with hDst
  set D := couplingData Dst Dρ SymLevyData.zero (Real.logb q) (Real.logb q) with hD
  have hsyn : IsSynthesisData q D := isSynthesisData_uniform hq Dρ hmom
    (exists_exponent_ne_zero hne hDρ) hl fun s t hs hst _ => logb_strictMonoOn hq hs hst
  obtain ⟨⟨μ, hμ⟩, hfam⟩ := coupling_family hq hsyn ρ (charFun_uniform_step hq Dρ hmom hl hDρ)
  obtain ⟨hlad, h1, -⟩ := hfam μ hμ
  have hD1 : D 1 = Dst := couplingData_one Dst Dρ _ hl hl
  refine ⟨μ, hlad, ⟨Dst, rfl, rfl, hD1 ▸ h1⟩, fun hrot => ?_⟩
  -- isotropy
  obtain ⟨hsym, hcov, hstepρ⟩ := hlad
  have hρQ : ∀ Q ∈ orthSet d, ∀ ω : Rd d, Dρ.exponent (lin Qᵀ ω) = Dρ.exponent ω := by
    intro Q hQ ω
    have h := (hDρ (lin Qᵀ ω)).symm.trans ((charFun_orth_of_rotationInvariant hrot hQ ω).trans
      (hDρ ω))
    have h2 := Real.exp_injective (Complex.ofReal_injective h)
    linarith
  -- the knot kernel: the limit of the partial products
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
  have hstQ : ∀ Q ∈ orthSet d, ∀ ω : Rd d, Dst.exponent (lin Qᵀ ω) = Dst.exponent ω := by
    intro Q hQ ω
    have hprod : ∀ M : ℕ, ladderProd q (μ 1 q) M (lin Qᵀ ω) = ladderProd q (μ 1 q) M ω := by
      intro M
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [hstepρ, ← ContinuousLinearMap.map_smul, charFun_orth_of_rotationInvariant hrot hQ]
    have h2 := hlim (lin Qᵀ ω)
    simp_rw [hprod] at h2
    have h3 := tendsto_nhds_unique h2 (hlim ω)
    have h1' : IsSymData (μ 0 1) Dst := hD1 ▸ h1
    rw [h1' (lin Qᵀ ω), h1' ω] at h3
    have h4 := Real.exp_injective (Complex.ofReal_injective h3)
    linarith
  -- every exponent of the octave, hence every exponent, is invariant
  have hDQ : ∀ u ∈ Icc 1 q, ∀ Q ∈ orthSet d, ∀ ω : Rd d,
      (D u).exponent (lin Qᵀ ω) = (D u).exponent ω := by
    intro u hu Q hQ ω
    rw [hD, couplingData_exponent_of_mem hl hl hu, couplingData_exponent_of_mem hl hl hu,
      hstQ Q hQ, hρQ Q hQ, SymLevyData.zero_exponent, SymLevyData.zero_exponent]
  have hrotΨ : ∀ (t : ℝ) {Q : Mat d}, Q ∈ orthSet d → ∀ ω : Rd d,
      octaveExponent q D t (lin Qᵀ ω) = octaveExponent q D t ω := by
    intro t Q hQ ω
    rw [← octaveData_exponent hq, ← octaveData_exponent hq]
    rcases le_or_gt t 0 with ht | ht
    · rw [octaveData_of_nonpos q D ht, SymLevyData.zero_exponent, SymLevyData.zero_exponent]
    · rw [octaveData, dif_pos ⟨ht, hq0.ne'⟩, SymLevyData.dilate_exponent,
        SymLevyData.dilate_exponent, ← ContinuousLinearMap.map_smul]
      exact hDQ _ (Ico_subset_Icc_self (octave_mem hq ht)) Q hQ _
  intro s t hs hst Q hQ
  obtain ⟨hp, hc⟩ := hμ s t hs hst
  haveI := hp
  haveI : IsProbabilityMeasure (push Q (μ s t)) :=
    Measure.isProbabilityMeasure_map (lin Q).continuous.aemeasurable
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [push, charFun_map_lin, hc, hc, hrotΨ t hQ, hrotΨ s hQ]

/-- **`prop:ladder-knot-kernel`(2), not unique.** Two families with the ladder of `ϱ` differ at
some pair. -/
theorem ladder_knot_kernel_2_not_unique {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0) (Dρ : SymLevyData d)
    (hDρ : IsSymData ρ Dρ) (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) :
    ∃ μ μ' : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ ∧ HasLadder q ρ μ' ∧
      ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ μ s t ≠ μ' s t := by
  have hl := isCouplingWeight_logb hq
  have hl2 := isCouplingWeight_logb_sq hq
  set Dst := ladderStarData hq Dρ hmom with hDst
  obtain ⟨ω₀, hω₀⟩ := exists_exponent_ne_zero hne hDρ
  have hsyn := isSynthesisData_uniform hq Dρ hmom ⟨ω₀, hω₀⟩ hl
    fun s t hs hst _ => logb_strictMonoOn hq hs hst
  have hsyn2 := isSynthesisData_uniform hq Dρ hmom ⟨ω₀, hω₀⟩ hl2
    fun s t hs hst _ => pow_lt_pow_left₀ (logb_strictMonoOn hq hs hst) (Real.logb_nonneg hq hs)
      two_ne_zero
  obtain ⟨⟨μ, hμ⟩, hfam⟩ := coupling_family hq hsyn ρ (charFun_uniform_step hq Dρ hmom hl hDρ)
  obtain ⟨⟨μ', hμ'⟩, hfam'⟩ := coupling_family hq hsyn2 ρ
    (charFun_uniform_step hq Dρ hmom hl2 hDρ)
  obtain ⟨hlad, -, hst⟩ := hfam μ hμ
  obtain ⟨hlad', -, hst'⟩ := hfam' μ' hμ'
  -- at `t = √q`
  set t : ℝ := q ^ (1 / 2 : ℝ) with ht
  have hq0 : 0 < q := by linarith
  have hlogt : Real.logb q t = 1 / 2 := by
    rw [ht, Real.logb_rpow hq0 hq.ne']
  have htI : t ∈ Icc 1 q := by
    refine ⟨Real.one_le_rpow hq.le (by norm_num), ?_⟩
    calc t ≤ q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq.le (by norm_num)
      _ = q := Real.rpow_one q
  refine ⟨μ, μ', hlad, hlad', 1, t, zero_le_one, htI.1, fun heq => hω₀ ?_⟩
  have h1 := (hst 1 t le_rfl htI.1 htI.2 ω₀).symm.trans
    ((congrArg (fun m => charFun m ω₀) heq).trans (hst' 1 t le_rfl htI.1 htI.2 ω₀))
  have h2 := Real.exp_injective (Complex.ofReal_injective h1)
  rw [couplingData_exponent_of_mem hl hl htI, couplingData_exponent_of_mem hl hl ⟨le_rfl, hq.le⟩,
    couplingData_exponent_of_mem hl2 hl2 htI,
    couplingData_exponent_of_mem hl2 hl2 ⟨le_rfl, hq.le⟩, hlogt, hl.one] at h2
  simp only [SymLevyData.zero_exponent] at h2
  nlinarith [h2]

/-! ## The split coupling -/

/-- The data `(A/2, ν')` for a symmetric part `ν' ≤ ν` of a Lévy measure. -/
noncomputable def SymLevyData.halfPart (D : SymLevyData d) (ν' : Measure (Rd d)) (hle : ν' ≤ D.ν)
    (hs : ν'.map (fun x => -x) = ν') : SymLevyData d where
  A := (1 / 2 : ℝ) • D.A
  ν := ν'
  A_posSemidef := D.A_posSemidef.smul (by norm_num)
  ν_zero := le_antisymm ((hle _).trans (le_of_eq D.ν_zero)) bot_le
  ν_integrable := ne_top_of_le_ne_top D.ν_integrable (lintegral_mono' hle le_rfl)
  ν_symm := hs

theorem isCouplingWeight_splitA {q : ℝ} (hq : 1 < q) :
    IsCouplingWeight q (fun t => min 1 (2 * Real.logb q t)) := by
  have hl := isCouplingWeight_logb hq
  refine ⟨ContinuousOn.inf continuousOn_const (continuousOn_const.mul hl.cont),
    fun s hs t ht hst => ?_,
    by simp [hl.one], by simp [hl.top]⟩
  exact min_le_min le_rfl (by linarith [hl.mono hs ht hst])

theorem isCouplingWeight_splitB {q : ℝ} (hq : 1 < q) :
    IsCouplingWeight q (fun t => max 0 (2 * Real.logb q t - 1)) := by
  have hl := isCouplingWeight_logb hq
  refine ⟨ContinuousOn.sup continuousOn_const
    ((continuousOn_const.mul hl.cont).sub continuousOn_const),
    fun s hs t ht hst => ?_, by simp [hl.one], by norm_num [hl.top]⟩
  exact max_le_max le_rfl (by linarith [hl.mono hs ht hst])

/-- **`prop:ladder-knot-kernel`(2), not unique up to `𝒢_q`, with isotropy.** The split coupling
and the uniform one; both are isotropic when `A_ϱ = cI` and `ν*`, `ν_a`, `ν_b` are invariant under
the isometries. -/
theorem ladder_knot_kernel_2_split_rot (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (Dρ : SymLevyData d) (hDρ : IsSymData ρ Dρ)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) (νa νb : Measure (Rd d))
    (hsum : Dρ.ν = νa + νb) (hna : νa ≠ 0) (hnb : νb ≠ 0) (hsa : νa.map (fun x => -x) = νa)
    (hsb : νb.map (fun x => -x) = νb) (Ba Bb : Set (Rd d))
    (hBb : MeasurableSet Bb) (hdisj : Disjoint Ba Bb) (hca : νa Baᶜ = 0) (hcb : νb Bbᶜ = 0) :
    ∃ μ μ' : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ ∧ HasLadder q ρ μ' ∧
      (¬ ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (extendByZero g s) (extendByZero g t)) ∧
      ((∃ c : ℝ, Dρ.A = c • (1 : Mat d)) →
        (∀ R : Rd d ≃ₗᵢ[ℝ] Rd d, (ladderNuStar q Dρ.ν).map R = ladderNuStar q Dρ.ν ∧
          νa.map R = νa ∧ νb.map R = νb) →
        IsRotationInvariantLaws μ ∧ IsRotationInvariantLaws μ') := by
  have hq0 : 0 < q := by linarith
  have hl := isCouplingWeight_logb hq
  have hwa := isCouplingWeight_splitA hq
  have hwb := isCouplingWeight_splitB hq
  set Dst := ladderStarData hq Dρ hmom with hDst
  set Da := Dρ.halfPart νa (hsum ▸ Measure.le_add_right le_rfl) hsa with hDa
  set Db := Dρ.halfPart νb (hsum ▸ Measure.le_add_left le_rfl) hsb with hDb
  have hAab : Da.A + Db.A = Dρ.A := by
    simp only [hDa, hDb, SymLevyData.halfPart, ← add_smul]
    norm_num
  have hνab : Da.ν + Db.ν = Dρ.ν := hsum.symm
  obtain ⟨ωa, hωa⟩ := SymLevyData.exists_exponent_ne_zero (D := Da) hna
  obtain ⟨ωb, hωb⟩ := SymLevyData.exists_exponent_ne_zero (D := Db) hnb
  have hωa' : 0 < Da.exponent ωa := lt_of_le_of_ne (Da.exponent_nonneg ωa) (Ne.symm hωa)
  have hωb' : 0 < Db.exponent ωb := lt_of_le_of_ne (Db.exponent_nonneg ωb) (Ne.symm hωb)
  -- `ψ_ϱ ≢ 0`
  have hψ : ∃ ω : Rd d, Dρ.exponent ω ≠ 0 := by
    refine ⟨ωa, ?_⟩
    rw [SymLevyData.exponent_of_add hAab hνab]
    exact (add_pos_of_pos_of_nonneg hωa' (Db.exponent_nonneg ωa)).ne'
  -- the two couplings
  have hsyn := isSynthesisData_uniform hq Dρ hmom hψ hl
    fun s t hs hst _ => logb_strictMonoOn hq hs hst
  have hsyn' : IsSynthesisData q (couplingData Dst Da Db (fun t => min 1 (2 * Real.logb q t))
      (fun t => max 0 (2 * Real.logb q t - 1))) := by
    refine isSynthesisData_coupling hq Dρ hmom Da Db hAab hνab hwa hwb fun s t hs hst ht => ?_
    have hsI : s ∈ Icc 1 q := ⟨hs, hst.le.trans ht⟩
    have htI : t ∈ Icc 1 q := ⟨hs.trans hst.le, ht⟩
    have hlt := logb_strictMonoOn hq hs hst
    have ha0 := hwa.mono hsI htI hst.le
    have hb0 := hwb.mono hsI htI hst.le
    rcases lt_or_ge (Real.logb q s) (1 / 2) with hhalf | hhalf
    · -- the first weight increases strictly
      refine ⟨ωa, (add_pos_of_pos_of_nonneg (mul_pos ?_ hωa')
        (mul_nonneg (sub_nonneg.2 hb0) (Db.exponent_nonneg ωa))).ne'⟩
      rw [sub_pos, min_eq_right (by linarith : 2 * Real.logb q s ≤ 1)]
      exact lt_min (by linarith) (by linarith)
    · -- the second weight increases strictly
      refine ⟨ωb, (add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.2 ha0)
        (Da.exponent_nonneg ωb)) (mul_pos ?_ hωb')).ne'⟩
      rw [sub_pos, max_eq_right (by linarith : 0 ≤ 2 * Real.logb q s - 1),
        max_eq_right (by linarith : 0 ≤ 2 * Real.logb q t - 1)]
      linarith
  have hρ' : ∀ ω : Rd d, charFun ρ ω = ((Real.exp (-((couplingData Dst Da Db
      (fun t => min 1 (2 * Real.logb q t)) (fun t => max 0 (2 * Real.logb q t - 1)) q).exponent ω -
      (couplingData Dst Da Db (fun t => min 1 (2 * Real.logb q t))
      (fun t => max 0 (2 * Real.logb q t - 1)) 1).exponent ω)) : ℝ) : ℂ) := by
    intro ω
    rw [couplingData_exponent_of_mem hwa hwb ⟨hq.le, le_rfl⟩,
      couplingData_exponent_of_mem hwa hwb ⟨le_rfl, hq.le⟩, hwa.top, hwb.top, hwa.one, hwb.one,
      hDρ ω, SymLevyData.exponent_of_add hAab hνab]
    congr 3
    ring
  obtain ⟨⟨μ, hμ⟩, hfam⟩ := coupling_family hq hsyn ρ (charFun_uniform_step hq Dρ hmom hl hDρ)
  obtain ⟨⟨μ', hμ'⟩, hfam'⟩ := coupling_family hq hsyn' ρ hρ'
  obtain ⟨hlad, h1, hst⟩ := hfam μ hμ
  obtain ⟨hlad', h1', hst'⟩ := hfam' μ' hμ'
  refine ⟨μ, μ', hlad, hlad', ?_, fun ⟨c, hc⟩ hR => ⟨isRotationInvariantLaws_of_octave hq
    (couplingData_exponent_isometry hl hl ?_ ?_ ?_) hμ,
    isRotationInvariantLaws_of_octave hq (couplingData_exponent_isometry hwa hwb ?_ ?_ ?_) hμ'⟩⟩
  rotate_left
  · exact fun R ω => Dst.exponent_isometry (c := (q ^ 2 - 1)⁻¹ * c)
      (by simp [hDst, ladderStarData, hc, smul_smul]) R
      (by simpa [hDst, ladderStarData] using (hR R).1) ω
  · exact fun R ω => Dρ.exponent_isometry hc R (by
      rw [hsum, Measure.map_add _ _ R.continuous.measurable, (hR R).2.1, (hR R).2.2]) ω
  · exact fun R ω => by simp [SymLevyData.zero_exponent]
  · exact fun R ω => Dst.exponent_isometry (c := (q ^ 2 - 1)⁻¹ * c)
      (by simp [hDst, ladderStarData, hc, smul_smul]) R
      (by simpa [hDst, ladderStarData] using (hR R).1) ω
  · exact fun R ω => Da.exponent_isometry (c := 1 / 2 * c)
      (by simp [hDa, SymLevyData.halfPart, hc, smul_smul]) R
      (by simpa [hDa, SymLevyData.halfPart] using (hR R).2.1) ω
  · exact fun R ω => Db.exponent_isometry (c := 1 / 2 * c)
      (by simp [hDb, SymLevyData.halfPart, hc, smul_smul]) R
      (by simpa [hDb, SymLevyData.halfPart] using (hR R).2.2) ω
  rintro ⟨g, hg, hrel⟩
  have hext1 : extendByZero g 1 = g 1 := by simp [extendByZero]
  have hext0 : extendByZero g 0 = 0 := by simp [extendByZero]
  -- `g` fixes `1`: the two knot kernels at `1` agree, and `t ↦ μ_t` is injective
  have hg1 : g 1 = 1 := by
    have hpos : 0 < g 1 := hg.mapsTo (mem_Ioi.2 one_pos)
    have hrel1 := hrel 0 1 le_rfl zero_le_one
    rw [hext0, hext1] at hrel1
    have hk : μ' 0 1 = μ 0 1 := by
      haveI := hlad.1.1.isProbability 0 1 le_rfl zero_le_one
      haveI := hlad'.1.1.isProbability 0 1 le_rfl zero_le_one
      refine Measure.ext_of_charFun (funext fun ω => ?_)
      rw [h1 ω, h1' ω, couplingData_one Dst _ _ hl hl, couplingData_one Dst _ _ hwa hwb]
    have hinj := (family_structure_monotone hd μ hlad.1).1
    exact hinj (mem_Ici.2 hpos.le) (mem_Ici.2
      zero_le_one) (hrel1.symm.trans hk)
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
    have := hg.strictMonoOn (mem_Ioi.2 one_pos)
      (mem_Ioi.2 (lt_trans one_pos ht1)) ht1
    rwa [hg1] at this
  have huq : u < q := by
    have h2 := hg.strictMonoOn (mem_Ioi.2 (lt_trans one_pos ht1))
      (mem_Ioi.2 hq0) htq
    have h3 := hg.equivariant 1 one_pos
    rw [mul_one, hg1, mul_one] at h3
    rwa [h3] at h2
  have huI : u ∈ Icc 1 q := ⟨hu1.le, huq.le⟩
  have hrelt := hrel 1 t zero_le_one ht1.le
  have hextt : extendByZero g t = u := by
    rw [extendByZero, if_neg (lt_trans one_pos ht1).ne']
  rw [hext1, hg1, hextt] at hrelt
  -- the exponents of the two steps
  have hexp : ∀ ω : Rd d, Da.exponent ω = Real.logb q u * Dρ.exponent ω := by
    intro ω
    have h2 := (hst' 1 t le_rfl ht1.le htq.le ω).symm.trans
      ((congrArg (fun m => charFun m ω) hrelt).trans (hst 1 u le_rfl hu1.le huq.le ω))
    have h3 := Real.exp_injective (Complex.ofReal_injective h2)
    rw [couplingData_exponent_of_mem hwa hwb htI, couplingData_exponent_of_mem hwa hwb
      ⟨le_rfl, hq.le⟩, couplingData_exponent_of_mem hl hl huI,
      couplingData_exponent_of_mem hl hl ⟨le_rfl, hq.le⟩, hlogt, hwa.one, hwb.one, hl.one,
      SymLevyData.zero_exponent] at h3
    norm_num at h3
    linarith
  -- so `ν_a = c ν_ϱ` with `c = log_q u`
  have hc0 : 0 ≤ Real.logb q u := hl.nonneg huI
  have hdata := (SymLevyData.eq_of_exponent (E := Da)
    (E' := SymLevyData.zero.addSmul Dρ (Real.logb q u)) fun ω => by
      rw [hexp ω, SymLevyData.addSmul_exponent, SymLevyData.zero_exponent,
        max_eq_left hc0, zero_add]).2
  simp only [SymLevyData.addSmul, SymLevyData.zero, zero_add, hDa, SymLevyData.halfPart] at hdata
  -- on `B_b`
  have haBb : νa Bb = 0 := measure_mono_null (fun x hx hxa => hdisj.ne_of_mem hxa hx rfl) hca
  have hbBb : νb Bb ≠ 0 := by
    intro h0
    apply hnb
    rw [← Measure.measure_univ_eq_zero, ← measure_add_measure_compl hBb, h0, hcb, add_zero]
  have h2 := congrArg (fun m : Measure (Rd d) => m Bb) hdata
  simp only [Measure.smul_apply, smul_eq_mul, haBb, hsum, Measure.add_apply, zero_add] at h2
  have hc : ENNReal.ofReal (Real.logb q u) = 0 := by
    rcases mul_eq_zero.1 h2.symm with h | h
    · exact h
    · exact absurd h hbBb
  apply hna
  rw [hdata, hc, zero_smul]


/-- **`prop:ladder-knot-kernel`(2), not unique up to `𝒢_q`.** When `ν_ϱ = ν_a + ν_b` with `ν_a`,
`ν_b` nonzero, symmetric and carried by disjoint sets, two families with the ladder of `ϱ` are not
relabellings of each other by any `g ∈ 𝒢_q`. -/
theorem ladder_knot_kernel_2_split (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (Dρ : SymLevyData d) (hDρ : IsSymData ρ Dρ)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂Dρ.ν < ⊤) (νa νb : Measure (Rd d))
    (hsum : Dρ.ν = νa + νb) (hna : νa ≠ 0) (hnb : νb ≠ 0) (hsa : νa.map (fun x => -x) = νa)
    (hsb : νb.map (fun x => -x) = νb) (Ba Bb : Set (Rd d))
    (hBb : MeasurableSet Bb) (hdisj : Disjoint Ba Bb) (hca : νa Baᶜ = 0) (hcb : νb Bbᶜ = 0) :
    ∃ μ μ' : ℝ → ℝ → Measure (Rd d), HasLadder q ρ μ ∧ HasLadder q ρ μ' ∧
      ¬ ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ' s t = μ (extendByZero g s) (extendByZero g t) := by
  obtain ⟨μ, μ', h1, h2, h3, -⟩ := ladder_knot_kernel_2_split_rot hd hq ρ Dρ hDρ hmom νa νb hsum
    hna hnb hsa hsb Ba Bb hBb hdisj hca hcb
  exact ⟨μ, μ', h1, h2, h3⟩

end Pyramids
