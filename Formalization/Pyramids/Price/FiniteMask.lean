/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Price.NotIsotropic
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# `prop:no-isotropic-refinable-finite-mask`: no rotation-invariant refinable law of a mask

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:no-isotropic-refinable-finite-mask`. Review
round 2, batch C (open question (4) of the theory paper's § 7.2); widened in review round 3,
batch C (s1-3.S13, s6-7.S7, 2026-11-23, a strengthening).

In `d ≥ 2`, let `μ` be a probability law on `ℝ^d` invariant under `SO(d)` and `q > 1`.

1. (`no_isotropic_refinable_mask_exp`) If `w` is a probability law carried by a countable set,
   with an exponential moment `∫ e^{c|x|} w(dx) < ∞`, `c > 0`, and `D_q μ = μ * w`, then
   `w = δ₀` and `μ = δ₀`. A law carried by a finite set is the case
   `no_isotropic_refinable_finite_mask`, the statement of round 2.
2. (`no_isotropic_refinable_signed_finite_mask`) If `w = ∑_{x} a(x) δ_x` has finitely many complex
   weights `a`, signed ones included, and `μ̂(qω) = μ̂(ω) ŵ(ω)` for every `ω`, the knot relation
   read on transforms, then `a = δ₀` and `μ = δ₀`.

## The route

* **Analytic along lines.** For a law with an exponential moment, `s ↦ ŵ(sv)` is the complex
  moment generating function of `⟨·, v⟩` on the imaginary axis, which lies inside its strip of
  analyticity (`ProbabilityTheory.analyticAt_complexMGF`), as `e^{t⟨x,v⟩} ≤ e^{c|x|}` for
  `|t| |v| ≤ c` (`analyticOnNhd_charFun_line`). A finite exponential sum is analytic on `ℝ^d`
  (`analyticOnNhd_finTransform`), hence along lines.
* **Radial near `0`, then everywhere** (`transform_invariant_of_knot`). The knot relation reads
  `μ̂(qω) = μ̂(ω)ŵ(ω)` and `μ̂(Rᵀω) = μ̂(ω)` for `R ∈ SO(d)`; near `0`, `μ̂ ≠ 0`, so
  `ŵ(Rᵀω) = ŵ(ω)` there. Along the line through `ω` both sides are analytic in the parameter and
  agree near `0`, so they agree at `ω` (`AnalyticOnNhd.eq_of_eventuallyEq` on `ℝ`).
* **The atoms.** (1) `R_*w = w` (`eq_of_charFun_eq`); an atom `x ≠ 0` would put the sphere
  `{|y| = |x|}` among the atoms, hence in the countable carrier (`compl_zero_null_of_rot`).
  (2) The weights are the coefficients of the exponential sum, unique by the linear independence of
  the characters `ω ↦ e^{i⟨x,ω⟩}` (`finTransform_injective`, Dedekind's lemma
  `linearIndependent_monoidHom`), so `a ∘ R⁻¹ = a`, and a weight `a(x) ≠ 0`, `x ≠ 0`, would put the
  sphere into the finite support.
* **The law.** Then `ŵ ≡ 1`, so `μ̂(qω) = μ̂(ω)`, `μ̂(ω) = μ̂(q^{-n}ω) → μ̂(0) = 1`, and `μ = δ₀`
  (`eq_dirac_of_knot_one`).

**What it reaches.** Lean core: no Lévy–Khintchine datum is read.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter Complex
open scoped Topology ENNReal RealInnerProductSpace Matrix

variable {d : ℕ}

/-- **The transform of a law carried by a finite set** is a finite exponential sum. -/
theorem charFun_eq_finset_sum {w : Measure (Rd d)} [IsFiniteMeasure w] {S : Finset (Rd d)}
    (hS : w (↑S)ᶜ = 0) (ω : Rd d) :
    charFun w ω = ∑ x ∈ S, w.real {x} • cexp (⟪x, ω⟫ * I) := by
  have hres : w.restrict (S : Set (Rd d)) = w :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hS)
  have hint : Integrable (fun x : Rd d => cexp (⟪x, ω⟫ * I)) w :=
    Integrable.of_bound (by fun_prop) 1
      (ae_of_all _ fun x => by rw [norm_exp_ofReal_mul_I])
  have h := setIntegral_finset (μ := w) S hint.integrableOn
  rw [hres] at h
  rw [charFun_apply, h]

/-- **The transform of a finitely carried law is real-analytic on `ℝ^d`.** -/
theorem analyticOnNhd_charFun_finite {w : Measure (Rd d)} [IsFiniteMeasure w] {S : Finset (Rd d)}
    (hS : w (↑S)ᶜ = 0) : AnalyticOnNhd ℝ (charFun w) univ := by
  have heq : charFun w = fun ω => ∑ x ∈ S, w.real {x} • cexp (⟪x, ω⟫ * I) :=
    funext (charFun_eq_finset_sum hS)
  rw [heq]
  intro ω _
  simp only [Complex.real_smul]
  refine Finset.analyticAt_fun_sum (𝕜 := ℝ) S fun x _ => ?_
  refine analyticAt_const.mul ?_
  have hlin : AnalyticAt ℝ (fun ω : Rd d => ((⟪x, ω⟫ : ℝ) : ℂ) * I) ω := by
    have h1 : AnalyticAt ℝ (fun ω : Rd d => ((⟪x, ω⟫ : ℝ) : ℂ)) ω :=
      (Complex.ofRealCLM.comp (innerSL ℝ x)).analyticAt ω
    exact h1.mul analyticAt_const
  exact (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp hlin

/-! ## The common steps -/

/-- A function analytic on `ℝ^d` is analytic along every line through `0`. -/
theorem analyticOnNhd_line {ψ : Rd d → ℂ} (h : AnalyticOnNhd ℝ ψ univ) (v : Rd d) :
    AnalyticOnNhd ℝ (fun s : ℝ => ψ (s • v)) univ := fun s _ => by
  have hL : (fun s : ℝ => ψ (s • v)) = ψ ∘ (ContinuousLinearMap.toSpanSingleton ℝ v) := by
    funext s
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [hL]
  exact (h _ (mem_univ _)).comp ((ContinuousLinearMap.toSpanSingleton ℝ v).analyticAt s)

/-- **The mask's transform is invariant under a symmetry of the law**, when it is analytic along
every line through `0`. Near `0`, `μ̂ ≠ 0` and the knot relation give `ŵ(Rᵀω) = ŵ(ω)`; along the
line through `ω` both sides are analytic in the parameter and agree near `0`, so they agree at
`ω`. -/
theorem transform_invariant_of_knot {q : ℝ} {φ ψ : Rd d → ℂ} (hφc : Continuous φ)
    (hφ0 : φ 0 = 1) (hk : ∀ ω, φ (q • ω) = φ ω * ψ ω) {R : Mat d}
    (hrot : ∀ ω, φ (lin Rᵀ ω) = φ ω)
    (hline : ∀ v : Rd d, AnalyticOnNhd ℝ (fun s : ℝ => ψ (s • v)) univ) (ω : Rd d) :
    ψ (lin Rᵀ ω) = ψ ω := by
  have hnear : (fun ω => ψ (lin Rᵀ ω)) =ᶠ[𝓝 0] ψ := by
    have hne : ∀ᶠ ω in 𝓝 (0 : Rd d), φ ω ≠ 0 :=
      hφc.continuousAt.eventually_ne (by rw [hφ0]; exact one_ne_zero)
    filter_upwards [hne] with ω hω
    have h1 := hk (lin Rᵀ ω)
    rw [← (lin Rᵀ).map_smul, hrot (q • ω), hk ω, hrot ω] at h1
    exact (mul_left_cancel₀ hω h1).symm
  have ht : Tendsto (fun s : ℝ => s • ω) (𝓝 0) (𝓝 0) := by
    have h := ((continuous_id.smul continuous_const : Continuous fun s : ℝ => s • ω).tendsto 0)
    simpa using h
  have hev : (fun s : ℝ => ψ (s • lin Rᵀ ω)) =ᶠ[𝓝 0] fun s => ψ (s • ω) := by
    filter_upwards [ht.eventually hnear] with s hs
    rw [← (lin Rᵀ).map_smul]
    exact hs
  have hglob := AnalyticOnNhd.eq_of_eventuallyEq (hline (lin Rᵀ ω)) (hline ω) hev
  simpa using congrFun hglob 1

/-- **A law fixed by its knot relation with `ŵ ≡ 1` is `δ₀`**: `μ̂(ω) = μ̂(q^{-n}ω) → μ̂(0)`. -/
theorem eq_dirac_of_knot_one {q : ℝ} (hq : 1 < q) {μ : Measure (Rd d)} [IsProbabilityMeasure μ]
    (hinv : ∀ ω, charFun μ (q • ω) = charFun μ ω) : μ = Measure.dirac 0 := by
  have hq0 : 0 < q := by linarith
  have hφc : Continuous (charFun μ) := continuous_charFun
  have hφ0 : charFun μ 0 = 1 := by simp
  have hiter : ∀ (n : ℕ) (ω : Rd d), charFun μ ((q⁻¹) ^ n • ω) = charFun μ ω := by
    intro n
    induction n with
    | zero => intro ω; simp
    | succ n ih =>
      intro ω
      have hc : q * (q⁻¹) ^ (n + 1) = (q⁻¹) ^ n := by
        rw [pow_succ, mul_comm, mul_assoc, inv_mul_cancel₀ hq0.ne', mul_one]
      rw [← ih ω, ← hinv ((q⁻¹) ^ (n + 1) • ω), smul_smul, hc]
  have hφ1 : ∀ ω, charFun μ ω = 1 := by
    intro ω
    have hlim : Tendsto (fun n : ℕ => (q⁻¹) ^ n • ω) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 hq0.le)
        (inv_lt_one_of_one_lt₀ hq)).smul_const ω
      simpa using this
    have h2 := (hφc.tendsto 0).comp hlim
    rw [hφ0] at h2
    have h3 : (charFun μ ∘ fun n : ℕ => (q⁻¹) ^ n • ω) = fun _ => charFun μ ω :=
      funext fun n => hiter n ω
    rw [h3] at h2
    exact tendsto_nhds_unique tendsto_const_nhds h2
  refine eq_of_charFun_eq fun ω => ?_
  rw [hφ1, charFun_dirac]
  simp

/-- **A law carried by a countable set and invariant under `SO(d)`, `d ≥ 2`, has no atom off
`0`**: the sphere through an atom would lie in the carrier. -/
theorem compl_zero_null_of_rot (hd : 2 ≤ d) {w : Measure (Rd d)} {C : Set (Rd d)}
    (hC : C.Countable) (hcarr : w Cᶜ = 0)
    (hrot : ∀ R ∈ orthSet d, R.det = 1 → w.map (lin R) = w) :
    w ({0} : Set (Rd d))ᶜ = 0 := by
  have hatom : ∀ x : Rd d, x ≠ 0 → w {x} = 0 := by
    intro x hx0
    by_contra hx
    refine not_countable_sphere hd (norm_pos_iff.2 hx0) (hC.mono fun y hy => ?_)
    obtain ⟨R, hR, hdet, hRx⟩ := exists_SO_map hd hy
    refine atom_mem hcarr ?_
    rw [← hRx, atom_map_eq hR (hrot R hR hdet)]
    exact hx
  have hCoff : w (C \ {0}) = 0 := by
    rw [← Set.biUnion_of_singleton (C \ {0})]
    exact (measure_biUnion_null_iff (hC.mono sdiff_subset)).2 fun x hx => hatom x hx.2
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hcarr hCoff)
  by_cases hxC : x ∈ C
  · exact Or.inr ⟨hxC, hx⟩
  · exact Or.inl hxC

/-- A probability law with no mass off `0` is `δ₀`. -/
theorem eq_dirac_of_compl_zero {w : Measure (Rd d)} [IsProbabilityMeasure w]
    (hw0 : w ({0} : Set (Rd d))ᶜ = 0) : w = Measure.dirac 0 := by
  have h1 : w {0} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton 0)).1 hw0
  refine eq_of_charFun_eq fun ω => ?_
  rw [charFun_eq_finset_sum (S := {0}) (by simpa using hw0), charFun_dirac]
  simp [measureReal_def, h1]

/-! ## (1) A law on a countable set with an exponential moment -/

/-- **With an exponential moment the transform is analytic along every line**: `s ↦ ŵ(sv)` is the
complex moment generating function of `⟨·, v⟩` at `s i`, and `0` is interior to the set of `t`
with `e^{t⟨x,v⟩}` integrable, which contains `|t| < c/(|v| + 1)`. -/
theorem analyticOnNhd_charFun_line {w : Measure (Rd d)} [IsFiniteMeasure w] {c : ℝ} (hc : 0 < c)
    (hexp : Integrable (fun x : Rd d => Real.exp (c * ‖x‖)) w) (v : Rd d) :
    AnalyticOnNhd ℝ (fun s : ℝ => charFun w (s • v)) univ := by
  have heq : (fun s : ℝ => charFun w (s • v)) =
      fun s : ℝ => ProbabilityTheory.complexMGF (fun x : Rd d => ⟪x, v⟫) w ((s : ℂ) * I) := by
    funext s
    rw [charFun_apply, ProbabilityTheory.complexMGF]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [real_inner_smul_right, Complex.ofReal_mul]
    congr 1
    ring
  have hc' : 0 < c / (‖v‖ + 1) := div_pos hc (by positivity)
  have hsub : Ioo (-(c / (‖v‖ + 1))) (c / (‖v‖ + 1)) ⊆
      ProbabilityTheory.integrableExpSet (fun x : Rd d => ⟪x, v⟫) w := by
    intro t ht
    have hbound : |t| * ‖v‖ ≤ c := by
      have h1 : |t| < c / (‖v‖ + 1) := abs_lt.2 ht
      have h2 : |t| * (‖v‖ + 1) < c := (lt_div_iff₀ (by positivity)).1 h1
      nlinarith [abs_nonneg t]
    change Integrable (fun x : Rd d => Real.exp (t * ⟪x, v⟫)) w
    refine hexp.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]
    refine Real.exp_le_exp.2 ?_
    calc t * ⟪x, v⟫ ≤ |t| * |⟪x, v⟫| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |t| * (‖x‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x v) (abs_nonneg t)
      _ = (|t| * ‖v‖) * ‖x‖ := by ring
      _ ≤ c * ‖x‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg x)
  have h0 : (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet (fun x : Rd d => ⟪x, v⟫) w) :=
    interior_mono hsub (by rw [interior_Ioo]; exact ⟨by linarith, hc'⟩)
  rw [heq]
  intro s _
  have hz : ((s : ℂ) * I).re ∈
      interior (ProbabilityTheory.integrableExpSet (fun x : Rd d => ⟪x, v⟫) w) := by
    simpa using h0
  have hlin : AnalyticAt ℝ (fun s : ℝ => (s : ℂ) * I) s :=
    (Complex.ofRealCLM.analyticAt s).mul analyticAt_const
  have hg : AnalyticAt ℝ (ProbabilityTheory.complexMGF (fun x : Rd d => ⟪x, v⟫) w)
      ((s : ℂ) * I) :=
    (ProbabilityTheory.analyticAt_complexMGF hz).restrictScalars (𝕜 := ℝ)
  exact AnalyticAt.comp (f := fun t : ℝ => (t : ℂ) * I) (x := s) hg hlin

/-- **`prop:no-isotropic-refinable-finite-mask`(1).** In `d ≥ 2`, a probability law `μ` on `ℝ^d`
invariant under `SO(d)` with `D_q μ = μ * w`, `q > 1`, for a probability law `w` carried by a
countable set and with an exponential moment `∫ e^{c|x|} w(dx) < ∞`, `c > 0`, is `δ₀`, and so is
`w`. -/
theorem no_isotropic_refinable_mask_exp (hd : 2 ≤ d) {q : ℝ} (hq : 1 < q)
    {μ w : Measure (Rd d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure w]
    (hμ : IsSORotationInvariant μ) {C : Set (Rd d)} (hC : C.Countable) (hcarr : w Cᶜ = 0)
    {c : ℝ} (hc : 0 < c) (hexp : Integrable (fun x : Rd d => Real.exp (c * ‖x‖)) w)
    (hknot : μ.map (fun x => q • x) = μ ∗ w) :
    w = Measure.dirac 0 ∧ μ = Measure.dirac 0 := by
  have hk : ∀ ω, charFun μ (q • ω) = charFun μ ω * charFun w ω := fun ω => by
    rw [← charFun_map_smul, hknot, charFun_conv]
  have hrot : ∀ R ∈ orthSet d, R.det = 1 → ∀ ω, charFun μ (lin Rᵀ ω) = charFun μ ω :=
    fun R hR hdet ω => by rw [← charFun_map_lin, ← push, hμ R hR hdet]
  have hwrot : ∀ R ∈ orthSet d, R.det = 1 → w.map (lin R) = w := by
    intro R hR hdet
    haveI : IsProbabilityMeasure (w.map (lin R)) :=
      Measure.isProbabilityMeasure_map (lin R).continuous.aemeasurable
    refine eq_of_charFun_eq fun ω => ?_
    rw [charFun_map_lin]
    exact transform_invariant_of_knot continuous_charFun (by simp) hk (hrot R hR hdet)
      (analyticOnNhd_charFun_line hc hexp) ω
  have hwδ := eq_dirac_of_compl_zero (compl_zero_null_of_rot hd hC hcarr hwrot)
  refine ⟨hwδ, eq_dirac_of_knot_one hq fun ω => ?_⟩
  rw [hk, hwδ, charFun_dirac]
  simp

/-- **`prop:no-isotropic-refinable-finite-mask`, a law carried by a finite set** (the statement of
review round 2). In `d ≥ 2`, a probability law `μ` on `ℝ^d` invariant under `SO(d)` with
`D_q μ = μ * w`, `q > 1`, for a probability law `w` carried by a finite set, is `δ₀`, and so is
`w`. Since 2026-11-23 a corollary of `no_isotropic_refinable_mask_exp`: a law carried by a finite
set has every exponential moment. -/
theorem no_isotropic_refinable_finite_mask (hd : 2 ≤ d) {q : ℝ} (hq : 1 < q)
    {μ w : Measure (Rd d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure w]
    (hμ : IsSORotationInvariant μ) {S : Finset (Rd d)} (hS : w (↑S)ᶜ = 0)
    (hknot : μ.map (fun x => q • x) = μ ∗ w) :
    w = Measure.dirac 0 ∧ μ = Measure.dirac 0 := by
  refine no_isotropic_refinable_mask_exp hd hq hμ S.countable_toSet hS one_pos ?_ hknot
  refine Integrable.of_bound (by fun_prop) (Real.exp (∑ s ∈ S, ‖s‖)) ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS] with x hx
  rw [mem_compl_iff, not_not] at hx
  rw [Real.norm_eq_abs, Real.abs_exp, one_mul]
  exact Real.exp_le_exp.2 (Finset.single_le_sum (f := fun s => ‖s‖) (fun s _ => norm_nonneg s) hx)

/-! ## (2) A signed or complex mask carried by a finite set -/

/-- **The transform of a finitely supported complex weight** `a`, `∑_x a(x) e^{i⟨x,ω⟩}`: the
transform of the complex measure `∑_x a(x) δ_x`. -/
noncomputable def finTransform (a : Rd d →₀ ℂ) (ω : Rd d) : ℂ :=
  a.sum fun x c => c * cexp (⟪x, ω⟫ * I)

/-- A finite exponential sum is analytic on `ℝ^d`. -/
theorem analyticOnNhd_finTransform (a : Rd d →₀ ℂ) :
    AnalyticOnNhd ℝ (finTransform a) univ := by
  intro ω _
  unfold finTransform Finsupp.sum
  refine Finset.analyticAt_fun_sum (𝕜 := ℝ) a.support fun x _ => ?_
  refine analyticAt_const.mul ?_
  have h1 : AnalyticAt ℝ (fun ω : Rd d => ((⟪x, ω⟫ : ℝ) : ℂ)) ω :=
    (Complex.ofRealCLM.comp (innerSL ℝ x)).analyticAt ω
  exact (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp (h1.mul analyticAt_const)

/-- **The character `ω ↦ e^{i⟨x,ω⟩}`**, a monoid hom from `Multiplicative (ℝ^d)` to `ℂ`. -/
noncomputable def charHom (x : Rd d) : Multiplicative (Rd d) →* ℂ where
  toFun ω := cexp (⟪x, ω.toAdd⟫ * I)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, inner_add_right, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- Distinct points give distinct characters: at `ω = π u/|u|²`, `u = x - y`, the quotient of the
two is `e^{iπ} = -1`. -/
theorem charHom_injective : Function.Injective (charHom (d := d)) := by
  intro x y hxy
  by_contra hne
  have hu0 : x - y ≠ 0 := sub_ne_zero.2 hne
  have hn : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.2 hu0
  have h1 := DFunLike.congr_fun hxy (Multiplicative.ofAdd ((Real.pi / ‖x - y‖ ^ 2) • (x - y)))
  simp only [charHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h1
  have h3 : ⟪x - y, (Real.pi / ‖x - y‖ ^ 2) • (x - y)⟫ = Real.pi := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h2 : cexp (((⟪x - y, (Real.pi / ‖x - y‖ ^ 2) • (x - y)⟫ : ℝ) : ℂ) * I) = 1 := by
    rw [inner_sub_left, Complex.ofReal_sub, sub_mul, Complex.exp_sub, h1,
      div_self (Complex.exp_ne_zero _)]
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

/-- **The weights of a finite exponential sum are unique** (Dedekind's lemma: distinct characters
are linearly independent). -/
theorem finTransform_injective {a b : Rd d →₀ ℂ}
    (h : ∀ ω, finTransform a ω = finTransform b ω) : a = b := by
  have hli : LinearIndependent ℂ (fun x : Rd d => ⇑(charHom x)) :=
    (linearIndependent_monoidHom (Multiplicative (Rd d)) ℂ).comp _ charHom_injective
  have h' : Finsupp.linearCombination ℂ (fun x : Rd d => ⇑(charHom x)) a =
      Finsupp.linearCombination ℂ (fun x : Rd d => ⇑(charHom x)) b := by
    funext m
    have hm := h (Multiplicative.toAdd m)
    simp only [finTransform, Finsupp.sum] at hm
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, charHom, MonoidHom.coe_mk, OneHom.coe_mk]
    exact hm
  exact hli h'

/-- A linear change of variables in the transform moves the weights: `ŵ(Rᵀω)` is the transform of
the weights carried forward by `R`. -/
theorem finTransform_lin (a : Rd d →₀ ℂ) (R : Mat d) (ω : Rd d) :
    finTransform a (lin Rᵀ ω) = finTransform (a.mapDomain (lin R)) ω := by
  unfold finTransform
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by rw [add_mul])]
  simp only [inner_lin_left]

/-- **`prop:no-isotropic-refinable-finite-mask`(2).** In `d ≥ 2`, let `μ` be a probability law on
`ℝ^d` invariant under `SO(d)`, `q > 1`, and `a` finitely many complex weights (signed ones
included), with `μ̂(qω) = μ̂(ω) ∑_x a(x) e^{i⟨x,ω⟩}` for every `ω`: the knot relation
`D_q μ = μ * w`, `w = ∑_x a(x) δ_x`, read on transforms. Then `a = δ₀` and `μ = δ₀`. -/
theorem no_isotropic_refinable_signed_finite_mask (hd : 2 ≤ d) {q : ℝ} (hq : 1 < q)
    {μ : Measure (Rd d)} [IsProbabilityMeasure μ] (hμ : IsSORotationInvariant μ)
    (a : Rd d →₀ ℂ) (hknot : ∀ ω, charFun μ (q • ω) = charFun μ ω * finTransform a ω) :
    a = Finsupp.single 0 1 ∧ μ = Measure.dirac 0 := by
  have hrot : ∀ R ∈ orthSet d, R.det = 1 → ∀ ω, charFun μ (lin Rᵀ ω) = charFun μ ω :=
    fun R hR hdet ω => by rw [← charFun_map_lin, ← push, hμ R hR hdet]
  have hainv : ∀ R ∈ orthSet d, R.det = 1 → a.mapDomain (lin R) = a := by
    intro R hR hdet
    refine finTransform_injective fun ω => ?_
    rw [← finTransform_lin]
    exact transform_invariant_of_knot continuous_charFun (by simp) hknot (hrot R hR hdet)
      (analyticOnNhd_line (analyticOnNhd_finTransform a)) ω
  have hoff : ∀ x : Rd d, x ≠ 0 → a x = 0 := by
    intro x hx0
    by_contra hx
    refine not_countable_sphere hd (norm_pos_iff.2 hx0)
      ((a.support.countable_toSet).mono fun y hy => ?_)
    obtain ⟨R, hR, hdet, hRx⟩ := exists_SO_map hd hy
    have h1 : a (lin R x) = a x := by
      conv_lhs => rw [← hainv R hR hdet]
      exact Finsupp.mapDomain_apply (lin_injective_of_orth hR) a x
    rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hRx, h1]
    exact hx
  have ha : a = Finsupp.single 0 (a 0) := by
    ext x
    by_cases hx : x = 0
    · subst hx
      simp
    · rw [hoff x hx, Finsupp.single_apply, if_neg (Ne.symm hx)]
  have hT : ∀ ω, finTransform a ω = a 0 := fun ω => by
    rw [ha]
    simp [finTransform]
  have ha0 : a 0 = 1 := by
    have h0 := hknot 0
    have h1 : charFun μ 0 = 1 := by simp
    rw [smul_zero, hT, h1, one_mul] at h0
    exact h0.symm
  refine ⟨by rw [ha, ha0], eq_dirac_of_knot_one hq fun ω => ?_⟩
  rw [hknot, hT, ha0, mul_one]

end Pyramids
