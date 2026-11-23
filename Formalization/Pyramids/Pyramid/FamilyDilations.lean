/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.FamilyStructure
import Pyramids.LineAppendix.LineExponentData
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Algebra.Order.Group.End

/-!
# `lem:family-dilations`: the dilations of a symmetric family

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `lem:family-dilations`, chapter 3. Wave 2c: the six
declarations moved here from `PyramidsSkeleton.Ch03Pyramid`, their statements unchanged.

## The route

The proofs run over any finite-dimensional real inner product space `E`, from four facts about the
kernels `μ_t = μ_{0,t}` collected in `KernelOrder`: the family is symmetric, `t ↦ μ_t` is injective
on `[0,∞)`, and `μ̂_t` is positive and nonincreasing in `t`. On `ℝ^d` they are
`lem:family-structure` (`family_structure_id`, `family_structure_monotone`); on `ℝ`, for clause (4),
they are read through the embedding `x ↦ xe₁` of `ℝ` in `ℝ¹` (`kernelOrder_line`).

* **(1)** Uniqueness is the injectivity. For `λ > 1` and `t > 0`, `S_λ t ≤ t` would give
  `μ̂_t(λω) = μ̂_{S_λ t}(ω) ≥ μ̂_t(ω)` at every `ω`, hence `μ̂_t(ω) ≥ μ̂_t(λ^{-n}ω) → 1`, so
  `μ_t = δ₀`, against (ND). This argument works at the one scale `t`: the printed proof's
  fixed-point step and the intermediate value theorem are not needed.
* **(2)** The group laws compose and invert the bijections. Closedness: along `λ_n → λ`, the
  values `S_{λ_n} t` are bounded by `S_g t` for one `g ∈ G` above the `λ_n` (when `G ≠ {1}`), a
  subsequence converges to some `τ`, and continuity gives `μ_τ = D_λ μ_t`. The kernels
  `D_λ μ_t = μ_{S t}` and `D_{λ⁻¹} μ_t = μ_{S' t}` then define the bijection
  (`KernelOrder.mem_of_kernels`), and `μ̂_{s,t} = μ̂_t/μ̂_s` gives the pairs. The trichotomy is
  Mathlib's `AddSubgroup.dense_or_cyclic` on the logarithms.
* **(3)** The homeomorphism `χ` is built on the orbit `S_q^n 1`, `n ∈ ℤ`, which tends to `∞` and
  to `0` (a finite limit would be a fixed point): `χ(t) = q^n g(S_q^{-n} t)` on
  `[S_q^n 1, S_q^{n+1} 1)`, `g` affine from `[1, S_q 1)` onto `[1, q)`. It is strictly increasing
  and onto, hence continuous (`isGauge_continuousOn`). The relabelling and the choices follow the
  printed proof.
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace

/-! ## Increasing bijections of `[0,∞)` -/

theorem incBij_zero {S : ℝ → ℝ} (h : IsIncreasingBijection S) : S 0 = 0 :=
  ((isGauge_iff_isIncreasingBijection S).2 h).1

theorem incBij_pos {S : ℝ → ℝ} (h : IsIncreasingBijection S) {t : ℝ} (ht : 0 < t) : 0 < S t := by
  have h1 := h.strictMonoOn (self_mem_Ici : (0 : ℝ) ∈ Ici 0) (mem_Ici.2 ht.le) ht
  rwa [incBij_zero h] at h1

/-- **The inverse of an increasing bijection of `[0,∞)`** is one. -/
theorem incBij_inverse {S : ℝ → ℝ} (h : IsIncreasingBijection S) :
    ∃ T : ℝ → ℝ, IsIncreasingBijection T ∧ (∀ t : ℝ, 0 ≤ t → T (S t) = t) ∧
      ∀ t : ℝ, 0 ≤ t → S (T t) = t := by
  classical
  set T := Function.invFunOn S (Ici 0) with hTdef
  have hST : ∀ t : ℝ, 0 ≤ t → S (T t) = t := fun t ht => Function.invFunOn_eq (h.surjOn ht)
  have hT0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ T t := fun t ht => Function.invFunOn_mem (h.surjOn ht)
  have hTS : ∀ t : ℝ, 0 ≤ t → T (S t) = t := fun t ht =>
    h.strictMonoOn.injOn (hT0 _ (h.mapsTo ht)) ht (hST _ (h.mapsTo ht))
  refine ⟨T, ⟨fun t ht => hT0 t ht, ?_, fun t ht => ⟨S t, h.mapsTo ht, hTS t ht⟩⟩, hTS, hST⟩
  intro u hu v hv huv
  by_contra hle
  push Not at hle
  have h1 := h.strictMonoOn.monotoneOn (hT0 v hv) (hT0 u hu) hle
  rw [hST u hu, hST v hv] at h1
  linarith

/-- **A gauge is continuous on `[0,∞)`**: a strictly increasing map of `[0,∞)` onto itself has no
jump. -/
theorem isGauge_continuousOn {χ : ℝ → ℝ} (h : IsGauge χ) : ContinuousOn χ (Ici 0) := by
  obtain ⟨h0, hm, hs⟩ := h
  intro a ha
  have hχa : 0 ≤ χ a := by
    rcases (mem_Ici.1 ha).eq_or_lt with h' | h'
    · rw [← h', h0]
    · have h1 := hm self_mem_Ici ha h'
      rw [h0] at h1
      exact h1.le
  have hright : ContinuousWithinAt χ (Ici a) a := by
    refine hm.continuousWithinAt_right_of_surjOn ?_ ?_
    · exact mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.2 ha)
    · intro y hy
      exact hs (mem_Ici.2 (hχa.trans (le_of_lt hy)))
  rcases (mem_Ici.1 ha).eq_or_lt with h' | h'
  · subst h'
    exact hright
  · have hleft : ContinuousWithinAt χ (Iic a) a := by
      refine hm.continuousWithinAt_left_of_exists_between ?_ ?_
      · exact mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds h')
      · intro b hb
        have hχpos : 0 < χ a := by
          have h1 := hm self_mem_Ici ha h'
          rwa [h0] at h1
        obtain ⟨c, hc, hcb⟩ := hs (mem_Ici.2 (le_max_right b 0))
        exact ⟨c, hc, by rw [hcb]; exact le_max_left b 0, by rw [hcb]; exact max_lt hb hχpos⟩
    exact (hleft.union hright).mono fun x _ => le_total x a

/-! ## The four facts about the kernels, over any space -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]

/-- **The facts about the kernels `μ_t = μ_{0,t}` that `lem:family-dilations` reads**: the family
is symmetric, `t ↦ μ_t` is injective on `[0,∞)`, and `μ̂_t` is positive and nonincreasing in `t`
(in the order of `ℂ`, which also says the values are real). On `ℝ^d` they are
`lem:family-structure`. -/
structure KernelOrder (μ : ℝ → ℝ → Measure E) : Prop where
  fam : IsSymmetricFamily μ
  inj : InjOn (fun t => μ 0 t) (Ici 0)
  pos : ∀ t : ℝ, 0 ≤ t → ∀ ω : E, 0 < charFun (μ 0 t) ω
  mono : ∀ ω : E, ∀ s t : ℝ, 0 ≤ s → s ≤ t → charFun (μ 0 t) ω ≤ charFun (μ 0 s) ω

/-- `μ̂_t = μ̂_{s,t} μ̂_s`, from (I1). -/
theorem charFun_kernel_mul_gen {μ : ℝ → ℝ → Measure E} (hμ : IsLawHemigroup μ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ω : E) :
    charFun (μ 0 t) ω = charFun (μ s t) ω * charFun (μ 0 s) ω := by
  haveI := hμ.isProbability s t hs hst
  haveI := hμ.isProbability 0 s le_rfl hs
  rw [hμ.cascade 0 s t le_rfl hs hst, charFun_conv]

/-- Covariance at the pairs `(0, t)`: `D_λ μ_t = μ_{S t}`. -/
theorem cov_kernel {μ : ℝ → ℝ → Measure E} {lam : ℝ} {S : ℝ → ℝ} (hS : IsCovariantAt μ lam S)
    {t : ℝ} (ht : 0 ≤ t) : (μ 0 t).map (fun x => lam • x) = μ 0 (S t) := by
  have h1 := hS.2 0 t le_rfl ht
  rwa [incBij_zero hS.1] at h1

namespace KernelOrder

variable {μ : ℝ → ℝ → Measure E}

theorem im_eq (h : KernelOrder μ) {t : ℝ} (ht : 0 ≤ t) (ω : E) : (charFun (μ 0 t) ω).im = 0 :=
  ((Complex.lt_def.1 (h.pos t ht ω)).2).symm

theorem re_pos (h : KernelOrder μ) {t : ℝ} (ht : 0 ≤ t) (ω : E) : 0 < (charFun (μ 0 t) ω).re :=
  (Complex.lt_def.1 (h.pos t ht ω)).1

theorem re_mono (h : KernelOrder μ) (ω : E) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (charFun (μ 0 t) ω).re ≤ (charFun (μ 0 s) ω).re :=
  (Complex.le_def.1 (h.mono ω s t hs hst)).1

theorem re_le_one (h : KernelOrder μ) {t : ℝ} (ht : 0 ≤ t) (ω : E) :
    (charFun (μ 0 t) ω).re ≤ 1 := by
  haveI := h.fam.1.isProbability 0 t le_rfl ht
  exact (Complex.re_le_norm _).trans (norm_charFun_le_one ω)

theorem charFun_eq_re (h : KernelOrder μ) {t : ℝ} (ht : 0 ≤ t) (ω : E) :
    charFun (μ 0 t) ω = ((charFun (μ 0 t) ω).re : ℂ) :=
  Complex.ext (by simp) (by simp [h.im_eq ht ω])

/-- Two kernels with the same real transform are equal. -/
theorem eq_of_re_eq (h : KernelOrder μ) {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (he : ∀ ω : E, (charFun (μ 0 t) ω).re = (charFun (μ 0 t') ω).re) : μ 0 t = μ 0 t' := by
  haveI := h.fam.1.isProbability 0 t le_rfl ht
  haveI := h.fam.1.isProbability 0 t' le_rfl ht'
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [h.charFun_eq_re ht ω, h.charFun_eq_re ht' ω, he ω]

/-- A kernel whose transform is `≥ 1` everywhere is `δ₀`. -/
theorem eq_dirac_of_one_le (h : KernelOrder μ) {t : ℝ} (ht : 0 ≤ t)
    (h1 : ∀ ω : E, 1 ≤ (charFun (μ 0 t) ω).re) : μ 0 t = Measure.dirac 0 := by
  haveI := h.fam.1.isProbability 0 t le_rfl ht
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_dirac, h.charFun_eq_re ht ω, le_antisymm (h.re_le_one ht ω) (h1 ω)]
  simp

end KernelOrder

/-- If `f(ω) ≤ f(λω)` everywhere, `λ > 1`, and `f` is continuous, then `f(0) ≤ f(ω)`:
`f(ω) ≥ f(λ^{-n}ω) → f(0)`. -/
theorem le_of_le_smul {f : E → ℝ} (hf : Continuous f) {lam : ℝ} (hlam : 1 < lam)
    (h : ∀ ω : E, f ω ≤ f (lam • ω)) (ω : E) : f 0 ≤ f ω := by
  have hl0 : lam ≠ 0 := by positivity
  have hn : ∀ n : ℕ, f ((lam⁻¹) ^ n • ω) ≤ f ω := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine le_trans ?_ ih
      have h1 := h ((lam⁻¹) ^ (n + 1) • ω)
      have e : lam • ((lam⁻¹) ^ (n + 1) • ω) = (lam⁻¹) ^ n • ω := by
        rw [smul_smul, pow_succ', ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]
      rwa [e] at h1
  have h1 : Tendsto (fun n : ℕ => (lam⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hlam)
  have h2 : Tendsto (fun n : ℕ => (lam⁻¹) ^ n • ω) atTop (𝓝 0) := by
    simpa using h1.smul_const ω
  exact le_of_tendsto' ((hf.tendsto 0).comp h2) hn

/-! ### Clause (1) -/

namespace KernelOrder

variable {μ : ℝ → ℝ → Measure E}

/-- **(1), uniqueness**: two bijections serving `λ` agree on `[0,∞)`. -/
theorem cov_unique (h : KernelOrder μ) {lam : ℝ} {S S' : ℝ → ℝ} (hS : IsCovariantAt μ lam S)
    (hS' : IsCovariantAt μ lam S') : EqOn S S' (Ici 0) := by
  intro t ht
  have e : μ 0 (S t) = μ 0 (S' t) := by rw [← cov_kernel hS ht, ← cov_kernel hS' ht]
  exact h.inj (hS.1.mapsTo ht) (hS'.1.mapsTo ht) e

/-- **(1), the direction**: for `λ > 1`, `S_λ t > t` at every `t > 0`. -/
theorem lt_cov (h : KernelOrder μ) {lam : ℝ} (hlam : 1 < lam) {S : ℝ → ℝ}
    (hS : IsCovariantAt μ lam S) {t : ℝ} (ht : 0 < t) : t < S t := by
  by_contra hle
  push Not at hle
  have hSt : 0 ≤ S t := hS.1.mapsTo ht.le
  haveI := h.fam.1.isProbability 0 t le_rfl ht.le
  set f : E → ℝ := fun ω => (charFun (μ 0 t) ω).re with hf
  have hfc : Continuous f := Complex.continuous_re.comp continuous_charFun
  have hstep : ∀ ω : E, f ω ≤ f (lam • ω) := by
    intro ω
    simp only [hf]
    rw [← charFun_map_smul, cov_kernel hS ht.le]
    exact h.re_mono ω hSt hle
  have h1 : ∀ ω : E, 1 ≤ (charFun (μ 0 t) ω).re := by
    intro ω
    have h2 := le_of_le_smul hfc hlam hstep ω
    haveI := h.fam.1.isProbability 0 t le_rfl ht.le
    simpa [hf, charFun_zero] using h2
  exact h.fam.2.1 0 t le_rfl ht (h.eq_dirac_of_one_le ht.le h1)

end KernelOrder

/-! ### Clause (2): the group -/

theorem cov_one (μ : ℝ → ℝ → Measure E) : IsCovariantAt μ 1 id := by
  refine ⟨⟨fun t ht => ht, fun a _ b _ hab => hab, fun t ht => ⟨t, ht, rfl⟩⟩, fun s t _ _ => ?_⟩
  simp

theorem cov_mul {μ : ℝ → ℝ → Measure E} {a b : ℝ} {S S' : ℝ → ℝ} (hS : IsCovariantAt μ a S)
    (hS' : IsCovariantAt μ b S') : IsCovariantAt μ (a * b) (S ∘ S') := by
  refine ⟨⟨fun t ht => hS.1.mapsTo (hS'.1.mapsTo ht), fun u hu v hv huv =>
    hS.1.strictMonoOn (hS'.1.mapsTo hu) (hS'.1.mapsTo hv) (hS'.1.strictMonoOn hu hv huv),
    fun t ht => ?_⟩, fun s t hs hst => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := hS.1.surjOn ht
    obtain ⟨v, hv, rfl⟩ := hS'.1.surjOn hu
    exact ⟨v, hv, rfl⟩
  · have hm : (fun x : E => (a * b) • x) = (fun x : E => a • x) ∘ (fun x : E => b • x) := by
      funext x
      simp [mul_smul]
    rw [hm, ← Measure.map_map (continuous_const_smul a).measurable
      (continuous_const_smul b).measurable, hS'.2 s t hs hst,
      hS.2 _ _ (hS'.1.mapsTo hs) (hS'.1.strictMonoOn.monotoneOn hs (hs.trans hst) hst)]
    rfl

theorem cov_inv {μ : ℝ → ℝ → Measure E} {a : ℝ} (ha : 0 < a) {S : ℝ → ℝ}
    (hS : IsCovariantAt μ a S) :
    ∃ T : ℝ → ℝ, IsCovariantAt μ a⁻¹ T ∧ (∀ t : ℝ, 0 ≤ t → T (S t) = t) ∧
      ∀ t : ℝ, 0 ≤ t → S (T t) = t := by
  obtain ⟨T, hT, hTS, hST⟩ := incBij_inverse hS.1
  refine ⟨T, ⟨hT, fun s t hs hst => ?_⟩, hTS, hST⟩
  have hle : T s ≤ T t := hT.strictMonoOn.monotoneOn hs (hs.trans hst) hst
  have e := hS.2 (T s) (T t) (hT.mapsTo hs) hle
  rw [hST s hs, hST t (hs.trans hst)] at e
  rw [← e, Measure.map_map (continuous_const_smul _).measurable
    (continuous_const_smul _).measurable]
  have hid : ((fun x : E => a⁻¹ • x) ∘ fun x : E => a • x) = id := by
    funext x
    simp [smul_smul, inv_mul_cancel₀ ha.ne']
  rw [hid, Measure.map_id]

namespace KernelOrder

variable {μ : ℝ → ℝ → Measure E}

/-- **The bijections increase with `λ`**: for `a < b` in `G`, `S_a ≤ S_b` on `[0,∞)`. -/
theorem cov_le (h : KernelOrder μ) {a b : ℝ} (ha : 0 < a) (hab : a < b) {Sa Sb : ℝ → ℝ}
    (hSa : IsCovariantAt μ a Sa) (hSb : IsCovariantAt μ b Sb) {t : ℝ} (ht : 0 ≤ t) :
    Sa t ≤ Sb t := by
  obtain ⟨T, hT, -, hST⟩ := cov_inv ha hSa
  have hc := cov_mul hT hSb
  have h1 : 1 < a⁻¹ * b := by
    rw [inv_mul_eq_div, one_lt_div ha]
    exact hab
  rcases ht.eq_or_lt with h0 | h0
  · subst h0
    rw [incBij_zero hSa.1, incBij_zero hSb.1]
  · have h2 := h.lt_cov h1 hc h0
    have h3 := hSa.1.strictMonoOn.monotoneOn ht (hT.1.mapsTo (hSb.1.mapsTo ht)) h2.le
    rwa [hST _ (hSb.1.mapsTo ht)] at h3

/-- **Closedness, the kernel at the limit**: if `λ_n ∈ G` tend to `λ > 0`, then for every `t ≥ 0`
some `τ ≥ 0` has `μ_τ = D_λ μ_t`. -/
theorem exists_limit_kernel (h : KernelOrder μ) {lam : ℝ} (hlam : 0 < lam) {l : ℕ → ℝ}
    (hl : ∀ n, l n ∈ covariantDilations μ) (hlim : Tendsto l atTop (𝓝 lam)) {t : ℝ}
    (ht : 0 ≤ t) : ∃ τ : ℝ, 0 ≤ τ ∧ μ 0 τ = (μ 0 t).map (fun x => lam • x) := by
  by_cases hG : ∃ g ∈ covariantDilations μ, 1 < g
  · obtain ⟨g, hgG, hg1⟩ := hG
    have hpow : ∀ k : ℕ, g ^ k ∈ covariantDilations μ := by
      intro k
      induction k with
      | zero => exact ⟨one_pos, id, by simpa using cov_one μ⟩
      | succ k ih =>
        obtain ⟨S1, hS1⟩ := ih.2
        obtain ⟨S2, hS2⟩ := hgG.2
        exact ⟨pow_pos hgG.1 _, S1 ∘ S2, by rw [pow_succ]; exact cov_mul hS1 hS2⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, lam + 1 < g ^ k := pow_unbounded_of_one_lt (lam + 1) hg1
    obtain ⟨Sg, hSg⟩ := (hpow k).2
    choose S hS using fun n => (hl n).2
    have hev : ∀ᶠ n in atTop, S n t ∈ Icc 0 (Sg t) := by
      filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_one lam))] with n hn
      exact ⟨(hS n).1.mapsTo ht, h.cov_le (hl n).1 (hn.trans hk) (hS n) hSg ht⟩
    obtain ⟨τ, hτ, φ, hφ, hτlim⟩ :=
      tendsto_subseq_of_frequently_bounded (Metric.isBounded_Icc 0 (Sg t)) hev.frequently
    rw [closure_Icc] at hτ
    refine ⟨τ, hτ.1, ?_⟩
    haveI := h.fam.1.isProbability 0 τ le_rfl hτ.1
    haveI := h.fam.1.isProbability 0 t le_rfl ht
    haveI : IsProbabilityMeasure ((μ 0 t).map (fun x => lam • x)) :=
      Measure.isProbabilityMeasure_map (continuous_const_smul lam).measurable.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_map_smul]
    have hc : ContinuousOn (fun s => charFun (μ 0 s) ω) (Ici 0) :=
      (h.fam.1.continuous ω).comp (continuousOn_const.prodMk continuousOn_id)
        (fun s hs => ⟨le_rfl, hs⟩)
    have L1 : Tendsto (fun n => charFun (μ 0 (S (φ n) t)) ω) atTop (𝓝 (charFun (μ 0 τ) ω)) :=
      ((hc τ hτ.1).tendsto).comp (tendsto_nhdsWithin_iff.2
        ⟨hτlim, Eventually.of_forall fun n => (hS (φ n)).1.mapsTo ht⟩)
    have L2 : Tendsto (fun n => charFun (μ 0 (S (φ n) t)) ω) atTop
        (𝓝 (charFun (μ 0 t) (lam • ω))) := by
      have e : (fun n => charFun (μ 0 (S (φ n) t)) ω) =
          fun n => charFun (μ 0 t) (l (φ n) • ω) := by
        funext n
        rw [← cov_kernel (hS (φ n)) ht, charFun_map_smul]
      rw [e]
      exact (continuous_charFun.tendsto _).comp ((hlim.comp hφ.tendsto_atTop).smul_const ω)
    exact tendsto_nhds_unique L1 L2
  · push Not at hG
    have hone : ∀ n, l n = 1 := by
      intro n
      obtain ⟨S, hS⟩ := (hl n).2
      obtain ⟨T, hT, -, -⟩ := cov_inv (hl n).1 hS
      have h2 := hG _ ⟨inv_pos.2 (hl n).1, T, hT⟩
      rw [inv_le_one₀ (hl n).1] at h2
      exact le_antisymm (hG _ (hl n)) h2
    have hl1 : lam = 1 := by
      have e : l = fun _ => 1 := funext hone
      rw [e] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    subst hl1
    exact ⟨t, ht, by simp⟩

/-- **A dilation whose kernels are kernels of the family is in `G`**: if `D_λ μ_t` and
`D_{λ⁻¹} μ_t` are kernels `μ_τ` for every `t ≥ 0`, then the family is `λ`-covariant. -/
theorem mem_of_kernels (h : KernelOrder μ) {lam : ℝ} (hlam : 0 < lam)
    (hf : ∀ t : ℝ, 0 ≤ t → ∃ τ : ℝ, 0 ≤ τ ∧ μ 0 τ = (μ 0 t).map (fun x => lam • x))
    (hb : ∀ t : ℝ, 0 ≤ t → ∃ τ : ℝ, 0 ≤ τ ∧ μ 0 τ = (μ 0 t).map (fun x => lam⁻¹ • x)) :
    lam ∈ covariantDilations μ := by
  classical
  choose! S hS0 hS using hf
  choose! T hT0 hT using hb
  have hmapinv : ∀ m : Measure E,
      ((m.map fun x => lam⁻¹ • x).map fun x => lam • x) = m := by
    intro m
    rw [Measure.map_map (continuous_const_smul _).measurable (continuous_const_smul _).measurable]
    have hid : ((fun x : E => lam • x) ∘ fun x : E => lam⁻¹ • x) = id := by
      funext x
      simp [smul_smul, mul_inv_cancel₀ hlam.ne']
    rw [hid, Measure.map_id]
  have hST : ∀ u : ℝ, 0 ≤ u → S (T u) = u := fun u hu =>
    h.inj (hS0 _ (hT0 u hu)) hu (by
      change μ 0 (S (T u)) = μ 0 u
      rw [hS _ (hT0 u hu), hT u hu, hmapinv])
  have hsm : ∀ u : ℝ, 0 ≤ u → ∀ ω : E,
      charFun (μ 0 (S u)) ω = charFun (μ 0 u) (lam • ω) := by
    intro u hu ω
    rw [hS u hu, charFun_map_smul]
  have hmono : StrictMonoOn S (Ici 0) := by
    intro u hu v hv huv
    by_contra hle
    push Not at hle
    have heq : μ 0 v = μ 0 u := h.eq_of_re_eq hv hu fun ω => by
      have h1 := h.re_mono (lam⁻¹ • ω) (hS0 v hv) hle
      rw [hsm u hu, hsm v hv, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul] at h1
      exact le_antisymm (h.re_mono ω hu huv.le) h1
    exact huv.ne (h.inj hu hv heq.symm)
  have hbij : IsIncreasingBijection S :=
    ⟨fun t ht => hS0 t ht, hmono, fun u hu => ⟨T u, hT0 u hu, hST u hu⟩⟩
  refine ⟨hlam, S, hbij, fun s t hs hst => ?_⟩
  have hSst : S s ≤ S t := hmono.monotoneOn hs (hs.trans hst) hst
  haveI := h.fam.1.isProbability s t hs hst
  haveI := h.fam.1.isProbability (S s) (S t) (hS0 s hs) hSst
  haveI : IsProbabilityMeasure ((μ s t).map (fun x => lam • x)) :=
    Measure.isProbabilityMeasure_map (continuous_const_smul lam).measurable.aemeasurable
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_map_smul]
  have h1 := charFun_kernel_mul_gen h.fam.1 hs hst (lam • ω)
  have h2 := charFun_kernel_mul_gen h.fam.1 (hS0 s hs) hSst ω
  rw [hsm s hs, hsm t (hs.trans hst)] at h2
  have hne : charFun (μ 0 s) (lam • ω) ≠ 0 := (h.pos s hs _).ne'
  exact mul_right_cancel₀ hne (h1.symm.trans h2)

/-- **`G` is closed in `(0,∞)`.** -/
theorem isClosed (h : KernelOrder μ) :
    IsClosed ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' covariantDilations μ) := by
  refine IsSeqClosed.isClosed fun x p hx hp => ?_
  have hl : Tendsto (fun n => (x n : ℝ)) atTop (𝓝 (p : ℝ)) :=
    (continuous_subtype_val.tendsto p).comp hp
  have hp0 : 0 < (p : ℝ) := p.2
  have hlinv : Tendsto (fun n => (x n : ℝ)⁻¹) atTop (𝓝 (p : ℝ)⁻¹) := hl.inv₀ hp0.ne'
  have hxinv : ∀ n, (x n : ℝ)⁻¹ ∈ covariantDilations μ := by
    intro n
    obtain ⟨S, hS⟩ := (hx n).2
    obtain ⟨T, hT, -, -⟩ := cov_inv (hx n).1 hS
    exact ⟨inv_pos.2 (hx n).1, T, hT⟩
  exact h.mem_of_kernels hp0 (fun t ht => h.exists_limit_kernel hp0 hx hl ht)
    (fun t ht => h.exists_limit_kernel (inv_pos.2 hp0) hxinv hlinv ht)

/-- **`G` is a closed subgroup of `(0,∞)`.** -/
theorem isClosedPosSubgroup (h : KernelOrder μ) :
    IsClosedPosSubgroup (covariantDilations μ) := by
  refine ⟨fun x hx => hx.1, ⟨one_pos, id, cov_one μ⟩, fun x hx y hy => ?_, fun x hx => ?_,
    h.isClosed⟩
  · obtain ⟨S, hS⟩ := hx.2
    obtain ⟨S', hS'⟩ := hy.2
    exact ⟨mul_pos hx.1 hy.1, S ∘ S', cov_mul hS hS'⟩
  · obtain ⟨S, hS⟩ := hx.2
    obtain ⟨T, hT, -, -⟩ := cov_inv hx.1 hS
    exact ⟨inv_pos.2 hx.1, T, hT⟩

end KernelOrder

/-! ### Clause (3): the relabelling -/

/-- **The relabelled family** `(μ_{ψ s, ψ t})`, `ψ` inverse to a gauge `χ` with `χ S = qχ`, is a
symmetric family with `S_q t = qt`. -/
theorem relabel_family {μ : ℝ → ℝ → Measure E} (hμ : IsSymmetricFamily μ) {q : ℝ} (hq : 0 < q)
    {S : ℝ → ℝ} (hS : IsCovariantAt μ q S) (χ ψ : ℝ → ℝ) (hχ : IsGauge χ)
    (hχS : ∀ t : ℝ, 0 ≤ t → χ (S t) = q * χ t) (hψχ : ∀ t : ℝ, 0 ≤ t → ψ (χ t) = t)
    (hχψ : ∀ t : ℝ, 0 ≤ t → χ (ψ t) = t) :
    IsSymmetricFamily (relabel μ ψ) ∧ IsCovariantAt (relabel μ ψ) q (fun t => q * t) := by
  have hχb := (isGauge_iff_isIncreasingBijection χ).1 hχ
  have hψ0 : ∀ u : ℝ, 0 ≤ u → 0 ≤ ψ u := by
    intro u hu
    obtain ⟨s, hs, rfl⟩ := hχ.2.2 hu
    rw [hψχ s hs]
    exact hs
  have hψm : StrictMonoOn ψ (Ici 0) := by
    intro u hu v hv huv
    obtain ⟨s, hs, rfl⟩ := hχ.2.2 hu
    obtain ⟨s', hs', rfl⟩ := hχ.2.2 hv
    rw [hψχ s hs, hψχ s' hs']
    by_contra hle
    push Not at hle
    exact absurd huv (not_lt.2 (hχ.2.1.monotoneOn hs' hs hle))
  have hψg : IsGauge ψ := by
    refine ⟨?_, hψm, fun s hs => ⟨χ s, hχb.mapsTo hs, hψχ s hs⟩⟩
    have h1 := hψχ 0 le_rfl
    rwa [hχ.1] at h1
  have hψc := isGauge_continuousOn hψg
  have hψle : ∀ s t : ℝ, 0 ≤ s → s ≤ t → ψ s ≤ ψ t := fun s t hs hst =>
    hψm.monotoneOn hs (hs.trans hst) hst
  refine ⟨⟨⟨fun s t hs hst => hμ.1.isProbability _ _ (hψ0 s hs) (hψle s t hs hst),
    fun t ht => hμ.1.diag _ (hψ0 t ht),
    fun r s t hr hrs hst => hμ.1.cascade _ _ _ (hψ0 r hr) (hψle r s hr hrs)
      (hψle s t (hr.trans hrs) hst), fun ω => ?_⟩,
    fun s t hs hst => hμ.2.1 _ _ (hψ0 s hs) (hψm hs (hs.trans hst.le) hst),
    fun s t hs hst => hμ.2.2 _ _ (hψ0 s hs) (hψle s t hs hst)⟩, ?_⟩
  · have hc : ContinuousOn (fun p : ℝ × ℝ => (ψ p.1, ψ p.2)) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2} :=
      (hψc.comp continuousOn_fst fun p hp => hp.1).prodMk
        (hψc.comp continuousOn_snd fun p hp => hp.1.trans hp.2)
    exact (hμ.1.continuous ω).comp hc fun p hp => ⟨hψ0 _ hp.1, hψle _ _ hp.1 hp.2⟩
  · refine ⟨⟨fun t ht => mul_nonneg hq.le ht, fun u _ v _ huv => mul_lt_mul_of_pos_left huv hq,
      fun t ht => ⟨t / q, div_nonneg ht hq.le, mul_div_cancel₀ t hq.ne'⟩⟩, fun s t hs hst => ?_⟩
    have hSψ : ∀ u : ℝ, 0 ≤ u → S (ψ u) = ψ (q * u) := by
      intro u hu
      have h1 : χ (S (ψ u)) = q * u := by rw [hχS _ (hψ0 u hu), hχψ u hu]
      rw [← h1, hψχ _ (hS.1.mapsTo (hψ0 u hu))]
    change (μ (ψ s) (ψ t)).map (fun x => q • x) = μ (ψ (q * s)) (ψ (q * t))
    rw [hS.2 _ _ (hψ0 s hs) (hψle s t hs hst), hSψ s hs, hSψ t (hs.trans hst)]

end Generic

/-! ### Clause (2): the trichotomy -/

/-- **A closed subgroup of `(0,∞)` is `{1}`, some `q^ℤ` with `q > 1`, or `(0,∞)`**: its logarithms
form a closed subgroup of `ℝ`, dense or cyclic (`AddSubgroup.dense_or_cyclic`). -/
theorem isClosedPosSubgroup_cases {G : Set ℝ} (hG : IsClosedPosSubgroup G) :
    G = {1} ∨ (∃ q : ℝ, 1 < q ∧ G = qPowers q) ∨ G = Ioi 0 := by
  obtain ⟨hpos, h1, hmul, hinv, hcl⟩ := hG
  let K : AddSubgroup ℝ :=
    { carrier := {x | Real.exp x ∈ G}
      add_mem' := fun {a b} ha hb => by
        change Real.exp (a + b) ∈ G
        rw [Real.exp_add]
        exact hmul _ ha _ hb
      zero_mem' := by
        change Real.exp 0 ∈ G
        rw [Real.exp_zero]
        exact h1
      neg_mem' := fun {a} ha => by
        change Real.exp (-a) ∈ G
        rw [Real.exp_neg]
        exact hinv _ ha }
  have hmemK : ∀ x : ℝ, x ∈ K ↔ Real.exp x ∈ G := fun x => Iff.rfl
  have hlogK : ∀ g ∈ G, Real.log g ∈ K := fun g hg => by
    rw [hmemK, Real.exp_log (hpos hg)]
    exact hg
  have hKcl : IsClosed (K : Set ℝ) := by
    have hc : Continuous (fun x : ℝ => (⟨Real.exp x, Real.exp_pos x⟩ : Ioi (0 : ℝ))) :=
      Real.continuous_exp.subtype_mk _
    exact hcl.preimage hc
  rcases K.dense_or_cyclic with hd | ⟨a, ha⟩
  · right
    right
    have hK : (K : Set ℝ) = univ := by
      rw [← hKcl.closure_eq]
      exact hd.closure_eq
    refine Subset.antisymm hpos fun y hy => ?_
    have hy' : Real.log y ∈ K := by
      rw [← SetLike.mem_coe, hK]
      trivial
    rwa [hmemK, Real.exp_log hy] at hy'
  · rw [← AddSubgroup.zmultiples_eq_closure] at ha
    have hmz : ∀ x : ℝ, x ∈ K ↔ ∃ k : ℤ, (k : ℝ) * a = x := by
      intro x
      rw [ha, AddSubgroup.mem_zmultiples_iff]
      simp [zsmul_eq_mul]
    by_cases ha0 : a = 0
    · left
      refine Subset.antisymm (fun g hg => ?_) (singleton_subset_iff.2 h1)
      obtain ⟨k, hk⟩ := (hmz _).1 (hlogK g hg)
      rw [ha0, mul_zero] at hk
      change g = 1
      rw [← Real.exp_log (hpos hg), ← hk, Real.exp_zero]
    · right
      left
      have hexp : ∀ x : ℝ, ∀ k : ℤ, Real.exp (k * x) = Real.exp x ^ k := by
        intro x k
        rw [mul_comm, Real.exp_mul, Real.rpow_intCast]
      refine ⟨Real.exp |a|, Real.one_lt_exp_iff.2 (abs_pos.2 ha0),
        Subset.antisymm (fun g hg => ?_) ?_⟩
      · obtain ⟨k, hk⟩ := (hmz _).1 (hlogK g hg)
        have hg' : g = Real.exp (k * a) := by rw [hk, Real.exp_log (hpos hg)]
        rcases le_or_gt 0 a with ha1 | ha1
        · exact ⟨k, by rw [abs_of_nonneg ha1, hg', hexp]⟩
        · refine ⟨-k, ?_⟩
          change Real.exp |a| ^ (-k) = g
          rw [abs_of_neg ha1, hg', ← hexp]
          congr 1
          push_cast
          ring
      · rintro _ ⟨n, rfl⟩
        change Real.exp |a| ^ n ∈ G
        rw [← hexp, ← hmemK, hmz]
        rcases le_or_gt 0 a with ha1 | ha1
        · exact ⟨n, by rw [abs_of_nonneg ha1]⟩
        · exact ⟨-n, by rw [abs_of_neg ha1]; push_cast; ring⟩

/-! ### Clause (3): the homeomorphism -/

/-- **(3), existence**: an increasing bijection `S` of `[0,∞)` with `S t > t` for `t > 0` is
conjugate to `t ↦ qt` by a gauge `χ`, `χ S = qχ`. The gauge is `q^n g(S^{-n} t)` on
`[S^n 1, S^{n+1} 1)`, with `g` affine from `[1, S 1)` onto `[1, q)`. -/
theorem exists_conj_of_lt {q : ℝ} (hq : 1 < q) {S : ℝ → ℝ} (hS : IsIncreasingBijection S)
    (hlt : ∀ t : ℝ, 0 < t → t < S t) :
    ∃ χ : ℝ → ℝ, IsGauge χ ∧ ContinuousOn χ (Ici 0) ∧ ∀ t : ℝ, 0 ≤ t → χ (S t) = q * χ t := by
  classical
  have hq0 : 0 < q := by linarith
  have hSc : ContinuousOn S (Ici 0) :=
    isGauge_continuousOn ((isGauge_iff_isIncreasingBijection S).2 hS)
  -- the order isomorphism of `(0,∞)` given by `S`
  let f : Ioi (0 : ℝ) → Ioi (0 : ℝ) := fun x => ⟨S x, incBij_pos hS x.2⟩
  have hfm : StrictMono f := fun x y hxy =>
    hS.strictMonoOn (Ioi_subset_Ici_self x.2) (Ioi_subset_Ici_self y.2) hxy
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hS.surjOn (mem_Ici.2 (le_of_lt y.2))
    have hx0 : 0 < x := by
      rcases (mem_Ici.1 hx).eq_or_lt with h | h
      · exfalso
        rw [← h, incBij_zero hS] at hxy
        exact (y.2 : (0 : ℝ) < y).ne hxy
      · exact h
    exact ⟨⟨x, hx0⟩, Subtype.ext hxy⟩
  let σ : Ioi (0 : ℝ) ≃o Ioi (0 : ℝ) := StrictMono.orderIsoOfSurjective f hfm hfs
  have hσ : ∀ x : Ioi (0 : ℝ), (σ x : ℝ) = S x := fun x => rfl
  have hadd : ∀ (m n : ℤ) (x : Ioi (0 : ℝ)), (σ ^ m) ((σ ^ n) x) = (σ ^ (m + n)) x := by
    intro m n x
    rw [zpow_add]
    rfl
  have hzero : ∀ x : Ioi (0 : ℝ), (σ ^ (0 : ℤ)) x = x := by
    intro x
    rw [zpow_zero]
    rfl
  have hone : ∀ x : Ioi (0 : ℝ), (σ ^ (1 : ℤ)) x = σ x := by
    intro x
    rw [zpow_one]
  have hcancel : ∀ (n : ℤ) (x : Ioi (0 : ℝ)), (σ ^ (-n)) ((σ ^ n) x) = x := by
    intro n x
    rw [hadd, neg_add_cancel, hzero]
  -- the orbit of `1`
  let one : Ioi (0 : ℝ) := ⟨1, mem_Ioi.2 one_pos⟩
  let a : ℤ → ℝ := fun n => ((σ ^ n) one : ℝ)
  have hapos : ∀ n : ℤ, 0 < a n := fun n => ((σ ^ n) one).2
  have hasucc : ∀ n : ℤ, a (n + 1) = S (a n) := by
    intro n
    change (((σ ^ (n + 1)) one : Ioi (0 : ℝ)) : ℝ) = S ((σ ^ n) one)
    rw [add_comm, ← hadd, hone, hσ]
  have hamono : StrictMono a :=
    strictMono_int_of_lt_succ fun n => by rw [hasucc]; exact hlt _ (hapos n)
  have hup : ∀ t : ℝ, ∃ n : ℤ, t < a n := by
    intro t
    by_contra hcon
    push Not at hcon
    let b : ℕ → ℝ := fun k => a k
    have hbm : Monotone b := fun i j hij => hamono.monotone (by exact_mod_cast hij)
    have hbb : BddAbove (range b) := ⟨t, by rintro _ ⟨k, rfl⟩; exact hcon k⟩
    have hL : Tendsto b atTop (𝓝 (⨆ k, b k)) := tendsto_atTop_ciSup hbm hbb
    have hL0 : 0 < ⨆ k, b k := lt_of_lt_of_le (hapos _) (le_ciSup hbb 0)
    have h1 : Tendsto (fun k => S (b k)) atTop (𝓝 (S (⨆ k, b k))) :=
      ((hSc _ (le_of_lt hL0)).tendsto).comp (tendsto_nhdsWithin_iff.2
        ⟨hL, Eventually.of_forall fun k => le_of_lt (hapos _)⟩)
    have h2 : Tendsto (fun k => S (b k)) atTop (𝓝 (⨆ k, b k)) := by
      have e : (fun k => S (b k)) = fun k => b (k + 1) := by
        funext k
        change S (a k) = a ((k + 1 : ℕ) : ℤ)
        rw [Nat.cast_succ, hasucc]
      rw [e]
      exact (tendsto_add_atTop_iff_nat 1).2 hL
    exact (hlt _ hL0).ne (tendsto_nhds_unique h2 h1)
  have hdown : ∀ t : ℝ, 0 < t → ∃ n : ℤ, a n ≤ t := by
    intro t ht
    by_contra hcon
    push Not at hcon
    let c : ℕ → ℝ := fun k => a (-(k : ℤ))
    have hcm : Antitone c := fun i j hij =>
      hamono.monotone (neg_le_neg (by exact_mod_cast hij))
    have hcb : BddBelow (range c) := ⟨t, by rintro _ ⟨k, rfl⟩; exact (hcon _).le⟩
    have hL : Tendsto c atTop (𝓝 (⨅ k, c k)) := tendsto_atTop_ciInf hcm hcb
    have hLt : t ≤ ⨅ k, c k := le_ciInf fun k => (hcon _).le
    have hL0 : 0 < ⨅ k, c k := ht.trans_le hLt
    have h1 : Tendsto (fun k => S (c (k + 1))) atTop (𝓝 (S (⨅ k, c k))) :=
      ((hSc _ hL0.le).tendsto).comp (tendsto_nhdsWithin_iff.2
        ⟨(tendsto_add_atTop_iff_nat 1).2 hL, Eventually.of_forall fun k => (hapos _).le⟩)
    have h2 : (fun k => S (c (k + 1))) = c := by
      funext k
      change S (a (-((k + 1 : ℕ) : ℤ))) = a (-(k : ℤ))
      rw [← hasucc]
      congr 1
      push_cast
      ring
    rw [h2] at h1
    exact (hlt _ hL0).ne (tendsto_nhds_unique hL h1)
  -- the level of a scale
  have hlevel : ∀ t : ℝ, 0 < t → ∃ n : ℤ, a n ≤ t ∧ t < a (n + 1) := by
    intro t ht
    obtain ⟨m, hm⟩ := hup t
    obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd (P := fun n => a n ≤ t)
      ⟨m, fun z hz => by
        by_contra hzm
        push Not at hzm
        have h1 := hamono.monotone hzm.le
        linarith⟩
      (hdown t ht)
    refine ⟨n, hn, ?_⟩
    by_contra h'
    push Not at h'
    have h1 := hmax (n + 1) h'
    omega
  have hlev_unique : ∀ t : ℝ, ∀ m n : ℤ, a m ≤ t → t < a (m + 1) → a n ≤ t → t < a (n + 1) →
      m = n := by
    intro t m n hm1 hm2 hn1 hn2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := hamono.monotone (show m + 1 ≤ n by omega)
      linarith
    · have h1 := hamono.monotone (show n + 1 ≤ m by omega)
      linarith
  choose! lev hlev using hlevel
  -- the position of a point in its octave
  have hrange : ∀ (n : ℤ) (x : Ioi (0 : ℝ)),
      (a n ≤ x ∧ (x : ℝ) < a (n + 1)) ↔
        (1 ≤ ((σ ^ (-n)) x : ℝ) ∧ ((σ ^ (-n)) x : ℝ) < S 1) := by
    intro n x
    have e1 : a n ≤ x ↔ one ≤ (σ ^ (-n)) x :=
      Subtype.coe_le_coe.trans ((σ ^ (-n)).le_iff_le.symm.trans (by rw [hcancel]))
    have e2 : (x : ℝ) < a (n + 1) ↔ (σ ^ (-n)) x < σ one :=
      Subtype.coe_lt_coe.trans ((σ ^ (-n)).lt_iff_lt.symm.trans
        (by rw [hadd, show -n + (n + 1) = 1 by ring, hone]))
    rw [e1, e2]
    rfl
  let pos : ℝ → Ioi (0 : ℝ) := fun t => if h : 0 < t then ⟨t, h⟩ else one
  have hposeq : ∀ t : ℝ, ∀ ht : 0 < t, pos t = ⟨t, ht⟩ := fun t ht => dif_pos ht
  let r : ℝ → ℝ := fun t => ((σ ^ (-lev t)) (pos t) : ℝ)
  have hr : ∀ t : ℝ, 0 < t → 1 ≤ r t ∧ r t < S 1 := by
    intro t ht
    have h1 := (hrange (lev t) ⟨t, ht⟩).1 (hlev t ht)
    change 1 ≤ ((σ ^ (-lev t)) (pos t) : ℝ) ∧ ((σ ^ (-lev t)) (pos t) : ℝ) < S 1
    rw [hposeq t ht]
    exact h1
  have hS1 : 1 < S 1 := hlt 1 one_pos
  let g : ℝ → ℝ := fun u => 1 + (q - 1) * (u - 1) / (S 1 - 1)
  have hgm : StrictMono g := by
    intro u v huv
    have h1 : 0 < S 1 - 1 := by linarith
    have h2 : 0 < q - 1 := by linarith
    change 1 + (q - 1) * (u - 1) / (S 1 - 1) < 1 + (q - 1) * (v - 1) / (S 1 - 1)
    have h3 : (q - 1) * (u - 1) < (q - 1) * (v - 1) := mul_lt_mul_of_pos_left (by linarith) h2
    linarith [div_lt_div_of_pos_right h3 h1]
  have hg1 : g 1 = 1 := by simp [g]
  have hgS : g (S 1) = q := by
    have h1 : S 1 - 1 ≠ 0 := by linarith
    simp only [g]
    field_simp
    ring
  have hgr : ∀ t : ℝ, 0 < t → 1 ≤ g (r t) ∧ g (r t) < q := by
    intro t ht
    obtain ⟨h1, h2⟩ := hr t ht
    refine ⟨?_, ?_⟩
    · rw [← hg1]
      exact hgm.monotone h1
    · rw [← hgS]
      exact hgm h2
  let χ : ℝ → ℝ := fun t => if 0 < t then q ^ lev t * g (r t) else 0
  have hχpos : ∀ t : ℝ, 0 < t → χ t = q ^ lev t * g (r t) := fun t ht => if_pos ht
  have hχ0 : χ 0 = 0 := if_neg (lt_irrefl 0)
  have hbounds : ∀ t : ℝ, 0 < t → q ^ lev t ≤ χ t ∧ χ t < q ^ (lev t + 1) := by
    intro t ht
    rw [hχpos t ht, zpow_add_one₀ hq0.ne']
    have hz : 0 < q ^ lev t := zpow_pos hq0 _
    obtain ⟨h1, h2⟩ := hgr t ht
    exact ⟨le_mul_of_one_le_right hz.le h1, mul_lt_mul_of_pos_left h2 hz⟩
  have hχp : ∀ t : ℝ, 0 < t → 0 < χ t := fun t ht =>
    lt_of_lt_of_le (zpow_pos hq0 _) (hbounds t ht).1
  -- strictly increasing
  have hmono : StrictMonoOn χ (Ici 0) := by
    intro u hu v hv huv
    have hv0 : 0 < v := lt_of_le_of_lt hu huv
    rcases (mem_Ici.1 hu).eq_or_lt with h0 | hu0
    · rw [← h0, hχ0]
      exact hχp v hv0
    obtain ⟨hu1, hu2⟩ := hlev u hu0
    obtain ⟨hv1, hv2⟩ := hlev v hv0
    rcases lt_trichotomy (lev u) (lev v) with hl | hl | hl
    · calc χ u < q ^ (lev u + 1) := (hbounds u hu0).2
        _ ≤ q ^ lev v := zpow_le_zpow_right₀ hq.le (by omega)
        _ ≤ χ v := (hbounds v hv0).1
    · rw [hχpos u hu0, hχpos v hv0, hl]
      refine mul_lt_mul_of_pos_left (hgm ?_) (zpow_pos hq0 _)
      change ((σ ^ (-lev u)) (pos u) : ℝ) < ((σ ^ (-lev v)) (pos v) : ℝ)
      rw [hl, hposeq u hu0, hposeq v hv0]
      exact (σ ^ (-lev v)).strictMono huv
    · exfalso
      have h1 := hamono.monotone (show lev v + 1 ≤ lev u by omega)
      linarith
  -- onto `[0,∞)`
  have hsurj : SurjOn χ (Ici 0) (Ici 0) := by
    intro y hy
    rcases (mem_Ici.1 hy).eq_or_lt with h0 | hy0
    · exact ⟨0, self_mem_Ici, by rw [hχ0, h0]⟩
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hy0 hq
    have hqn : 0 < q ^ n := zpow_pos hq0 n
    set v := y / q ^ n with hvdef
    have hv1 : 1 ≤ v := by rw [hvdef, le_div_iff₀ hqn, one_mul]; exact hn1
    have hv2 : v < q := by
      rw [hvdef, div_lt_iff₀ hqn, mul_comm, ← zpow_add_one₀ hq0.ne']
      exact hn2
    set u := 1 + (v - 1) * (S 1 - 1) / (q - 1) with hudef
    have hq1 : 0 < q - 1 := by linarith
    have hs1 : 0 < S 1 - 1 := by linarith
    have hu1 : 1 ≤ u := by
      have : 0 ≤ (v - 1) * (S 1 - 1) / (q - 1) :=
        div_nonneg (mul_nonneg (by linarith) hs1.le) hq1.le
      linarith
    have hu2 : u < S 1 := by
      have : (v - 1) * (S 1 - 1) / (q - 1) < S 1 - 1 := by
        rw [div_lt_iff₀ hq1]
        nlinarith [mul_lt_mul_of_pos_right (show v - 1 < q - 1 by linarith) hs1]
      linarith
    have hgu : g u = v := by
      simp only [g, hudef]
      field_simp
      ring
    let x : Ioi (0 : ℝ) := (σ ^ n) ⟨u, mem_Ioi.2 (by linarith)⟩
    have hx : 0 < (x : ℝ) := x.2
    have hxr : ((σ ^ (-n)) x : ℝ) = u := by
      change (((σ ^ (-n)) ((σ ^ n) ⟨u, _⟩) : Ioi (0 : ℝ)) : ℝ) = u
      rw [hcancel]
    have hxin : a n ≤ x ∧ (x : ℝ) < a (n + 1) := (hrange n x).2 ⟨by rw [hxr]; exact hu1,
      by rw [hxr]; exact hu2⟩
    have hlx : lev x = n :=
      hlev_unique _ _ _ (hlev _ hx).1 (hlev _ hx).2 hxin.1 hxin.2
    refine ⟨x, le_of_lt hx, ?_⟩
    rw [hχpos _ hx]
    have hrx : r x = u := by
      change ((σ ^ (-lev x)) (pos x) : ℝ) = u
      rw [hlx, hposeq _ hx]
      exact hxr
    rw [hrx, hgu, hlx, hvdef, mul_div_cancel₀ _ hqn.ne']
  have hgauge : IsGauge χ := ⟨hχ0, hmono, hsurj⟩
  refine ⟨χ, hgauge, isGauge_continuousOn hgauge, fun t ht => ?_⟩
  rcases ht.eq_or_lt with h0 | ht0
  · rw [← h0, incBij_zero hS, hχ0, mul_zero]
  have hSt : 0 < S t := incBij_pos hS ht0
  have hσt : (σ ⟨t, ht0⟩ : ℝ) = S t := hσ _
  have hin : a (lev t + 1) ≤ S t ∧ S t < a (lev t + 1 + 1) := by
    rw [hasucc, hasucc (lev t + 1), hasucc]
    obtain ⟨h1, h2⟩ := hlev t ht0
    refine ⟨hS.strictMonoOn.monotoneOn (le_of_lt (hapos _)) ht h1, ?_⟩
    rw [← hasucc]
    exact hS.strictMonoOn ht (le_of_lt (hapos _)) h2
  have hlS : lev (S t) = lev t + 1 :=
    hlev_unique _ _ _ (hlev _ hSt).1 (hlev _ hSt).2 hin.1 hin.2
  have hrS : r (S t) = r t := by
    change ((σ ^ (-lev (S t))) (pos (S t)) : ℝ) = ((σ ^ (-lev t)) (pos t) : ℝ)
    have hp : pos (S t) = σ (pos t) := by
      rw [hposeq _ hSt, hposeq _ ht0]
      exact Subtype.ext hσt.symm
    rw [hp, hlS, ← hone, hadd, show -(lev t + 1) + 1 = -lev t by ring]
  rw [hχpos _ hSt, hχpos _ ht0, hlS, hrS, zpow_add_one₀ hq0.ne']
  ring

/-- **(3), the choices**: two gauges conjugating `S` to `t ↦ qt` differ by an element of `𝒢_q`. -/
theorem gauge_choice {q : ℝ} {S : ℝ → ℝ} (hS : IsIncreasingBijection S)
    (χ χ' : ℝ → ℝ) (hχ : IsGauge χ) (hχS : ∀ t : ℝ, 0 ≤ t → χ (S t) = q * χ t)
    (hχ' : IsGauge χ') (hχ'c : ContinuousOn χ' (Ici 0))
    (hχ'S : ∀ t : ℝ, 0 ≤ t → χ' (S t) = q * χ' t) :
    ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧ ∀ t : ℝ, 0 ≤ t → χ' t = extendByZero g (χ t) := by
  have hχb := (isGauge_iff_isIncreasingBijection χ).1 hχ
  have hχ'b := (isGauge_iff_isIncreasingBijection χ').1 hχ'
  obtain ⟨ψ, hψ, hψχ, hχψ⟩ := incBij_inverse hχb
  have hψc := isGauge_continuousOn ((isGauge_iff_isIncreasingBijection ψ).2 hψ)
  refine ⟨χ' ∘ ψ, ⟨fun u hu v hv huv => hχ'.2.1 (hψ.mapsTo (Ioi_subset_Ici_self hu))
    (hψ.mapsTo (Ioi_subset_Ici_self hv))
    (hψ.strictMonoOn (Ioi_subset_Ici_self hu) (Ioi_subset_Ici_self hv) huv),
    fun t ht => incBij_pos hχ'b (incBij_pos hψ ht), fun y hy => ?_,
    hχ'c.comp (hψc.mono Ioi_subset_Ici_self) fun t ht => hψ.mapsTo (Ioi_subset_Ici_self ht),
    fun t ht => ?_⟩, fun t ht => ?_⟩
  · obtain ⟨s, hs, hsy⟩ := hχ'.2.2 (Ioi_subset_Ici_self hy)
    have hs0 : 0 < s := by
      rcases (mem_Ici.1 hs).eq_or_lt with h | h
      · exfalso
        rw [← h, hχ'.1] at hsy
        exact (ne_of_lt (mem_Ioi.1 hy)) hsy
      · exact h
    exact ⟨χ s, incBij_pos hχb hs0, by simp only [Function.comp_apply]; rw [hψχ s hs, hsy]⟩
  · have hψt := hψ.mapsTo (le_of_lt ht)
    have h1 : χ (S (ψ t)) = q * t := by rw [hχS _ hψt, hχψ t (le_of_lt ht)]
    have h2 : ψ (q * t) = S (ψ t) := by rw [← h1, hψχ _ (hS.mapsTo hψt)]
    simp only [Function.comp_apply]
    rw [h2, hχ'S _ hψt]
  · by_cases h0 : χ t = 0
    · have ht0 : t = 0 := hχ.2.1.injOn ht self_mem_Ici (by rw [h0, hχ.1])
      rw [h0, ht0, hχ'.1]
      simp [extendByZero]
    · simp only [extendByZero, if_neg h0, Function.comp_apply]
      rw [hψχ t ht]

/-! ## The line, read inside `ℝ¹` -/

/-- **The kernel facts for a symmetric family on `ℝ`**, from `lem:family-structure` at `d = 1`
through `x ↦ xe₁`. -/
theorem kernelOrder_line {μ : ℝ → ℝ → Measure ℝ} (hμ : IsSymmetricFamily μ) : KernelOrder μ := by
  set ν : ℝ → ℝ → Measure (Rd 1) := fun s t => (μ s t).map lineEmbL with hν
  have hcf : ∀ s t : ℝ, ∀ z : Rd 1, charFun (ν s t) z = charFun (μ s t) (z 0) :=
    fun s t z => charFun_map_lineEmb _ z
  have hcf' : ∀ s t x : ℝ, charFun (μ s t) x = charFun (ν s t) (lineEmb x) := by
    intro s t x
    rw [hcf, lineEmb_apply_zero]
  have hνfam : IsSymmetricFamily ν := by
    refine ⟨⟨fun s t hs hst => ?_, fun t ht => ?_, fun r s t hr hrs hst => ?_, fun ω => ?_⟩,
      fun s t hs hst h0 => ?_, fun s t hs hst => ?_⟩
    · haveI := hμ.1.isProbability s t hs hst
      exact Measure.isProbabilityMeasure_map lineEmbL.continuous.measurable.aemeasurable
    · simp only [hν]
      rw [hμ.1.diag t ht, Measure.map_dirac' lineEmbL.continuous.measurable, map_zero]
    · haveI := hμ.1.isProbability s t (hr.trans hrs) hst
      haveI := hμ.1.isProbability r s hr hrs
      simp only [hν]
      rw [hμ.1.cascade r s t hr hrs hst, Measure.map_conv_continuousLinearMap]
    · simp only [hcf]
      exact (hμ.1.continuous (ω 0))
    · apply hμ.2.1 s t hs hst
      haveI := hμ.1.isProbability s t hs hst.le
      refine Measure.ext_of_charFun (funext fun x => ?_)
      rw [hcf', h0, charFun_dirac, charFun_dirac]
      simp
    · simp only [hν]
      rw [Measure.map_map measurable_neg lineEmbL.continuous.measurable]
      have e : ((fun x : Rd 1 => -x) ∘ lineEmbL) = lineEmbL ∘ fun x : ℝ => -x :=
        funext fun x => (map_neg lineEmbL x).symm
      rw [e, ← Measure.map_map lineEmbL.continuous.measurable measurable_neg,
        hμ.2.2 s t hs hst]
  have hid := family_structure_id le_rfl ν hνfam
  have hmo := family_structure_monotone le_rfl ν hνfam
  refine ⟨hμ, fun t ht t' ht' e => hmo.1 ht ht' (by
      change (μ 0 t).map lineEmbL = (μ 0 t').map lineEmbL
      rw [show μ 0 t = μ 0 t' from e]), fun t ht ω => ?_, fun ω s t hs hst => ?_⟩
  · rw [hcf']
    exact (hid 0 t le_rfl ht).2 _
  · rw [hcf', hcf']
    exact hmo.2 _ s t hs hst

/-- **The kernel facts on `ℝ^d`**: `lem:family-structure`. -/
theorem kernelOrder_rd {d : ℕ} (hd : 1 ≤ d) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : IsSymmetricFamily μ) : KernelOrder μ :=
  ⟨hμ, (family_structure_monotone hd μ hμ).1,
    fun t ht ω => ((family_structure_id hd μ hμ) 0 t le_rfl ht).2 ω,
    (family_structure_monotone hd μ hμ).2⟩

/-! ## `lem:family-dilations` -/

variable {d : ℕ}

/-- **`lem:family-dilations`(1).** For `λ ∈ G` the bijection `S_λ` is unique on `[0,∞)`, and
`S_λ t > t` for `t > 0` when `λ > 1`. -/
theorem family_dilations_1 (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsSymmetricFamily μ)
    {lam : ℝ} (S S' : ℝ → ℝ) (hS : IsCovariantAt μ lam S)
    (hS' : IsCovariantAt μ lam S') :
    EqOn S S' (Ici 0) ∧ (1 < lam → ∀ t : ℝ, 0 < t → t < S t) :=
  ⟨(kernelOrder_rd hd hμ).cov_unique hS hS', fun h1 _ ht => (kernelOrder_rd hd hμ).lt_cov h1 hS ht⟩

/-- **`lem:family-dilations`(2).** `G` is a closed subgroup of `(0,∞)`, so it is `{1}`, some `q^ℤ`
with `q > 1`, or `(0,∞)`. -/
theorem family_dilations_2 (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) :
    IsClosedPosSubgroup (covariantDilations μ) ∧
      (covariantDilations μ = {1} ∨ (∃ q : ℝ, 1 < q ∧ covariantDilations μ = qPowers q) ∨
        covariantDilations μ = Ioi 0) :=
  ⟨(kernelOrder_rd hd hμ).isClosedPosSubgroup,
    isClosedPosSubgroup_cases (kernelOrder_rd hd hμ).isClosedPosSubgroup⟩

/-- **`lem:family-dilations`(3), the homeomorphism.** If `q ∈ G`, `q > 1`, there is an increasing
homeomorphism `χ` of `[0,∞)` with `χ S_q = qχ`. -/
theorem family_dilations_3_exists (hd : 1 ≤ d) (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) {q : ℝ} (hq : 1 < q) (S : ℝ → ℝ) (hS : IsCovariantAt μ q S) :
    ∃ χ : ℝ → ℝ, IsGauge χ ∧ ContinuousOn χ (Ici 0) ∧ ∀ t : ℝ, 0 ≤ t → χ (S t) = q * χ t :=
  exists_conj_of_lt hq hS.1 fun _ ht => (kernelOrder_rd hd hμ).lt_cov hq hS ht

/-- **`lem:family-dilations`(3), the relabelling.** For every such `χ`, the relabelled family
`(μ_{χ⁻¹s, χ⁻¹t})` is a symmetric family with the canonical discrete gauge `S_q t = qt`. -/
theorem family_dilations_3_relabel (μ : ℝ → ℝ → Measure (Rd d))
    (hμ : IsSymmetricFamily μ) {q : ℝ} (hq : 1 < q) (S : ℝ → ℝ) (hS : IsCovariantAt μ q S)
    (χ ψ : ℝ → ℝ) (hχ : IsGauge χ)
    (hχS : ∀ t : ℝ, 0 ≤ t → χ (S t) = q * χ t) (hψχ : ∀ t : ℝ, 0 ≤ t → ψ (χ t) = t)
    (hχψ : ∀ t : ℝ, 0 ≤ t → χ (ψ t) = t) :
    IsSymmetricFamily (relabel μ ψ) ∧ IsCovariantAt (relabel μ ψ) q (fun t => q * t) :=
  relabel_family hμ (by linarith) hS χ ψ hχ hχS hψχ hχψ

/-- **`lem:family-dilations`(3), the choices.** Two such `χ`, `χ'` differ by an element of `𝒢_q`,
extended by `g(0) := 0`: `χ' = gχ` on `[0,∞)`. -/
theorem family_dilations_3_unique (μ : ℝ → ℝ → Measure (Rd d))
    {q : ℝ} (S : ℝ → ℝ) (hS : IsCovariantAt μ q S)
    (χ χ' : ℝ → ℝ) (hχ : IsGauge χ)
    (hχS : ∀ t : ℝ, 0 ≤ t → χ (S t) = q * χ t) (hχ' : IsGauge χ')
    (hχ'c : ContinuousOn χ' (Ici 0)) (hχ'S : ∀ t : ℝ, 0 ≤ t → χ' (S t) = q * χ' t) :
    ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧ ∀ t : ℝ, 0 ≤ t → χ' t = extendByZero g (χ t) :=
  gauge_choice hS.1 χ χ' hχ hχS hχ' hχ'c hχ'S

/-- **`lem:family-dilations`(4), the line.** A symmetric family on `ℝ` that is `q`-covariant,
`q > 1`, has a bijection `S_q` with no fixed point in `(0,∞)`; some relabelling of (3) gives it the
canonical discrete gauge; and the relabelling is unique up to `𝒢_q`. -/
theorem family_dilations_4 (μ : ℝ → ℝ → Measure ℝ) (hμ : IsSymmetricFamily μ) {q : ℝ}
    (hq : 1 < q) (S : ℝ → ℝ) (hS : IsCovariantAt μ q S) :
    (∀ t : ℝ, 0 < t → S t ≠ t) ∧
      (∃ χ ψ : ℝ → ℝ, IsGauge χ ∧ ContinuousOn χ (Ici 0) ∧
        (∀ t : ℝ, 0 ≤ t → χ (S t) = q * χ t) ∧ (∀ t : ℝ, 0 ≤ t → ψ (χ t) = t ∧ χ (ψ t) = t) ∧
        IsSymmetricFamily (relabel μ ψ) ∧ IsCovariantAt (relabel μ ψ) q (fun t => q * t)) ∧
      ∀ χ χ' : ℝ → ℝ, IsGauge χ → ContinuousOn χ (Ici 0) → (∀ t : ℝ, 0 ≤ t → χ (S t) = q * χ t) →
        IsGauge χ' → ContinuousOn χ' (Ici 0) → (∀ t : ℝ, 0 ≤ t → χ' (S t) = q * χ' t) →
          ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧ ∀ t : ℝ, 0 ≤ t → χ' t = extendByZero g (χ t) := by
  have h := kernelOrder_line hμ
  have hlt : ∀ t : ℝ, 0 < t → t < S t := fun _ ht => h.lt_cov hq hS ht
  refine ⟨fun t ht => (hlt t ht).ne', ?_, fun χ χ' hχ _ hχS hχ' hχ'c hχ'S =>
    gauge_choice hS.1 χ χ' hχ hχS hχ' hχ'c hχ'S⟩
  obtain ⟨χ, hχ, hχc, hχS⟩ := exists_conj_of_lt hq hS.1 hlt
  obtain ⟨ψ, -, hψχ, hχψ⟩ := incBij_inverse ((isGauge_iff_isIncreasingBijection χ).1 hχ)
  exact ⟨χ, ψ, hχ, hχc, hχS, fun t ht => ⟨hψχ t ht, hχψ t ht⟩,
    relabel_family hμ (by linarith) hS χ ψ hχ hχS hψχ hχψ⟩

end Pyramids
