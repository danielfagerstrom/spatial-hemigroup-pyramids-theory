/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Cited.A22
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Ledger A23: the counting clause (V-selection v0.1, Prop. 4.5(2), p. 35), proved from A22

**No axiom.** Ledger entry A23 is not admitted (`adr/0005-a22-and-a24-admitted.md`): it is
proved here from A22's variation-diminishing clause, `cited_A22_variation`, by the page's own
derivation (p. 39): "Clause (2) follows from the variation-diminishing property of clause (1)
applied to `f - c`, which is bounded because the primitive of an integrable function is, and to
`f'`, using `∂ₓu(t,·) = μ_{0,t} * f'`." Interface node `thm:cited-A23`.

**What is proved here, beside the page.**

* *The primitive.* For a probability `μ` and `f = C + ∫₀^x f'` with `f'` integrable,
  `μ * f = (μ * f)(0) + ∫₀^x μ * f'` at every point (`mconv_primitive`): Fubini on
  `[0,x] × μ`, through the core's `integrable_uncurry_sub`. So `μ * f` is absolutely continuous
  and, by the Lebesgue differentiation theorem, `∂ₓ(μ * f) = μ * f'` almost everywhere
  (`deriv_mconv_primitive_ae`); the count `S⁻` does not see the null set (`essSignChanges_congr`).
* *The level shift.* `μ * f - c = μ * (f - c)` at every point, `f` being bounded and continuous.
* *`F ≡ 0`.* The page's range is an admissible family, and A22 is admitted there
  (`cited_A22_variation` takes `F ≢ 0`). The statement here is the skeleton's, without that
  hypothesis: at `F ≡ 0` the kernel is `δ₀` (its transform is `1`), and both counts are equalities
  (`variation_of_form`).
-/

namespace Pyramids

open MeasureTheory Set Filter
open scoped Interval
open ScaleSpace (IsAdmissibleExponent mconv mconv_apply integrable_uncurry_sub integrable_mconv
  mconv_dirac_zero)

/-- `S⁻` does not see a change on a null set. -/
theorem essSignChanges_congr {g g' : ℝ → ℝ} (h : g =ᵐ[volume] g') :
    essSignChanges g = essSignChanges g' := by
  unfold essSignChanges
  apply le_antisymm
  · refine le_iInf₂ fun k hk => iInf₂_le k ?_
    filter_upwards [hk, h] with x h1 h2
    linarith
  · refine le_iInf₂ fun k hk => iInf₂_le k ?_
    filter_upwards [hk, h] with x h1 h2
    linarith

/-- The primitive of an integrable function is bounded. -/
theorem abs_primitive_le {f' : ℝ → ℝ} (hf' : Integrable f') (C x : ℝ) :
    |C + ∫ y in (0 : ℝ)..x, f' y| ≤ |C| + ∫ y, ‖f' y‖ := by
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
  exact setIntegral_le_integral hf'.norm (Eventually.of_forall fun _ => norm_nonneg _)

/-- The primitive of an integrable function is continuous. -/
theorem continuous_primitive' {f' : ℝ → ℝ} (hf' : Integrable f') (C : ℝ) :
    Continuous fun x => C + ∫ y in (0 : ℝ)..x, f' y :=
  continuous_const.add
    (intervalIntegral.continuous_primitive (fun _ _ => hf'.intervalIntegrable) 0)

/-- A bounded continuous function is integrable against a finite measure, after any
translation and reflection. -/
theorem integrable_comp_sub_of_bdd (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (x : ℝ) :
    Integrable (fun y => f (x - y)) μ :=
  Integrable.of_bound (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable M
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _)

/-- **The primitive under a convolution**: for a probability `μ` and `f = C + ∫₀^x f'`,
`(μ * f)(x) = (μ * f)(0) + ∫₀^x (μ * f')`. -/
theorem mconv_primitive (μ : Measure ℝ) [IsProbabilityMeasure μ] {f' : ℝ → ℝ}
    (hf' : Integrable f') (C x : ℝ) :
    mconv μ (fun x => C + ∫ y in (0 : ℝ)..x, f' y) x =
      mconv μ (fun x => C + ∫ y in (0 : ℝ)..x, f' y) 0 + ∫ z in (0 : ℝ)..x, mconv μ f' z := by
  set f := fun x => C + ∫ y in (0 : ℝ)..x, f' y with hfdef
  have hfc : Continuous f := continuous_primitive' hf' C
  have hM : ∀ x, |f x| ≤ |C| + ∫ y, ‖f' y‖ := abs_primitive_le hf' C
  -- the difference of the two values, under the integral
  have hdiff : ∀ y, f (x - y) - f (0 - y) = ∫ z in (0 : ℝ)..x, f' (z - y) := by
    intro y
    simp only [hfdef]
    rw [intervalIntegral.integral_comp_sub_right (fun z => f' z) y, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left hf'.intervalIntegrable hf'.intervalIntegrable]
  have hint : Integrable (Function.uncurry fun z y : ℝ => f' (z - y))
      ((volume.restrict (Ι (0 : ℝ) x)).prod μ) := by
    have h := integrable_uncurry_sub μ hf'.aestronglyMeasurable hf'
    have heq : (volume.restrict (Ι (0 : ℝ) x)).prod μ =
        (volume.prod μ).restrict (Ι (0 : ℝ) x ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [heq]
    exact h.restrict
  have hswap := intervalIntegral_integral_swap hint
  simp only [mconv_apply] at hswap ⊢
  rw [hswap]
  have h1 := integrable_comp_sub_of_bdd μ hfc hM x
  have h0 := integrable_comp_sub_of_bdd μ hfc hM 0
  rw [← sub_eq_iff_eq_add', ← integral_sub h1 h0]
  exact integral_congr_ae (Eventually.of_forall hdiff)

/-- **`∂ₓ(μ * f) = μ * f'` almost everywhere**, for `f` the primitive of an integrable `f'`. -/
theorem deriv_mconv_primitive_ae (μ : Measure ℝ) [IsProbabilityMeasure μ] {f' : ℝ → ℝ}
    (hf' : Integrable f') (C : ℝ) :
    deriv (mconv μ fun x => C + ∫ y in (0 : ℝ)..x, f' y) =ᵐ[volume] mconv μ f' := by
  have hg : Integrable (mconv μ f') := integrable_mconv μ hf'.aestronglyMeasurable hf'
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable] with x hx
  have hfun : (mconv μ fun x => C + ∫ y in (0 : ℝ)..x, f' y) = fun x =>
      mconv μ (fun x => C + ∫ y in (0 : ℝ)..x, f' y) 0 + ∫ z in (0 : ℝ)..x, mconv μ f' z :=
    funext (mconv_primitive μ hf' C)
  rw [hfun]
  exact ((hx 0).const_add _).deriv

/-- A probability law with transform `1` is `δ₀`. -/
theorem dirac_of_charFun_eq_one_line {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h : ∀ ω : ℝ, charFun ν ω = 1) : ν = Measure.dirac 0 :=
  Measure.ext_of_charFun (funext fun ω => by rw [h, charFun_dirac]; simp)

/-- **Variation diminution, `F ≡ 0` included**: the A22 axiom where `F ≢ 0`, and `μ_t = δ₀`
where `F ≡ 0`. -/
theorem variation_of_form {ι : Type*} [Countable ι] (F : ℝ → ℝ) (hF : IsAdmissibleExponent F)
    (a : ℝ) (ha : 0 ≤ a) (θ : ι → ℝ) (hθ : ∀ i, 0 < θ i) (hsum : Summable fun i => (θ i ^ 2)⁻¹)
    (hform : ∀ ω : ℝ, F ω = a * ω ^ 2 + ∑' i, Real.log (1 + ω ^ 2 / θ i ^ 2))
    (μ : ℝ → Measure ℝ) (hμ : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hμF : ∀ t : ℝ, 0 < t → ∀ ω : ℝ, charFun (μ t) ω = ((Real.exp (-F (t * ω)) : ℝ) : ℂ))
    {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ)
    (hg : Integrable g ∨ (AEStronglyMeasurable g volume ∧ ∃ C : ℝ, ∀ x, |g x| ≤ C)) :
    essSignChanges (mconv (μ t) g) ≤ essSignChanges g := by
  by_cases hFne : ∃ ω : ℝ, F ω ≠ 0
  · exact cited_A22_variation F hF hFne a ha θ hθ hsum hform μ hμ hμF ht g hg
  · push Not at hFne
    haveI := hμ t ht
    have hδ : μ t = Measure.dirac 0 :=
      dirac_of_charFun_eq_one_line fun ω => by rw [hμF t ht, hFne]; simp
    rw [hδ, mconv_dirac_zero]

/-- **`thm:cited-A23`**, ledger A23 (V-selection v0.1, Prop. 4.5(2), p. 35; derived on p. 39),
proved from A22's variation-diminishing clause. For a family as in `thm:cited-A22` and `f` a
primitive of an integrable `f'`, the scale space `u(t,·) = μ_t * f` has, at every `t > 0`,
`S⁻(u(t,·) - c) ≤ S⁻(f - c)` for every level `c` and `S⁻(∂ₓu(t,·)) ≤ S⁻(f')`. -/
theorem cited_A23 {ι : Type*} [Countable ι] (F : ℝ → ℝ) (hF : IsAdmissibleExponent F)
    (a : ℝ) (ha : 0 ≤ a) (θ : ι → ℝ) (hθ : ∀ i, 0 < θ i) (hsum : Summable fun i => (θ i ^ 2)⁻¹)
    (hform : ∀ ω : ℝ, F ω = a * ω ^ 2 + ∑' i, Real.log (1 + ω ^ 2 / θ i ^ 2))
    (μ : ℝ → Measure ℝ) (hμ : ∀ t : ℝ, 0 < t → IsProbabilityMeasure (μ t))
    (hμF : ∀ t : ℝ, 0 < t → ∀ ω : ℝ, charFun (μ t) ω = ((Real.exp (-F (t * ω)) : ℝ) : ℂ))
    (f f' : ℝ → ℝ) (hf' : Integrable f') (hprim : ∃ C : ℝ, ∀ x, f x = C + ∫ y in (0 : ℝ)..x, f' y)
    {t : ℝ} (ht : 0 < t) :
    (∀ c : ℝ, essSignChanges (fun x => mconv (μ t) f x - c) ≤ essSignChanges (fun x => f x - c)) ∧
      essSignChanges (deriv (mconv (μ t) f)) ≤ essSignChanges f' := by
  haveI := hμ t ht
  obtain ⟨C, hC⟩ := hprim
  have hfeq : f = fun x => C + ∫ y in (0 : ℝ)..x, f' y := funext hC
  have hfc : Continuous f := hfeq ▸ continuous_primitive' hf' C
  have hM : ∀ x, |f x| ≤ |C| + ∫ y, ‖f' y‖ := fun x => hfeq ▸ abs_primitive_le hf' C x
  have hvar := variation_of_form F hF a ha θ hθ hsum hform μ hμ hμF ht
  refine ⟨fun c => ?_, ?_⟩
  · have hshift : (fun x => mconv (μ t) f x - c) = mconv (μ t) (fun x => f x - c) := by
      funext x
      simp only [mconv_apply]
      rw [integral_sub (integrable_comp_sub_of_bdd _ hfc hM x) (integrable_const c),
        integral_const, probReal_univ, one_smul]
    rw [hshift]
    refine hvar _ (Or.inr ⟨(hfc.sub continuous_const).aestronglyMeasurable,
      (|C| + ∫ y, ‖f' y‖) + |c|, fun x => ?_⟩)
    exact (abs_sub _ _).trans (add_le_add (hM x) le_rfl)
  · rw [hfeq, essSignChanges_congr (deriv_mconv_primitive_ae (μ t) hf' C)]
    exact hvar f' (Or.inl hf')

end Pyramids
