/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.StrataCylinder
import Pyramids.LineAppendix.SurfacePair
import Pyramids.LineAppendix.LineExponentData

/-!
# `prop:strata-cylinder-coordinates`, part A: the Gaussian part, both parts, "then"

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:strata-cylinder-coordinates`. Wave 3c: the
declarations `strata_cylinder_1_gaussian`, `strata_cylinder_1_both` and `strata_cylinder_1_then`
moved here from `PyramidsSkeleton.ChA1Line`, unchanged in statement, except that
`strata_cylinder_1_both` no longer takes the hypothesis `1 < q`, which its proof does not use (a
strengthening).

## The route

* **The Gaussian part.** A measure on `(0,∞)`, finite on the intervals `(0,t]`, that scales by
  `λ²` on them scales by `λ²` on every Borel set (`image_mul_of_Ioc`: the image of `m` under
  `y ↦ y/λ` and `λ²m` agree on the intervals). (a') gives `a(t) = a(1)t²`, so `ℬ` is
  `2a(1) y dy` (`gaussDensity`) by the same uniqueness. Conversely, two measures with (ii) and the
  same restriction to `[1,q)` are equal (`thm:knot-atom-cascades`(2), `gaussSpread`), and
  `b y dy` has (ii); so (c') gives `ℬ = b y dy`, which is `λ²`-homogeneous with `a(t) = (b/2)t²`.
* **Both parts.** `Ψ_t` has the data `(a(t), ϖ_t)` (`surfacePairOf_exponent`), `Ψ_t(λ ·)` the data
  `(λ²a(t), T_λϖ_t)` (`line_exponent_data_2`). The direction "(a) and (a') give the covariance"
  compares the exponents of equal data; the other direction reads the uniqueness of the data,
  `line_exponent_data_1_unique`, which is A39(ii)–(iii).
* **"Then".** The mixture of the orbits of `η ⊗ ρ̃` is the image of `(dy/(ℓy)) ⊗ ρ̃` under
  `(y, r) ↦ (y, ry)` (`orbitMixture_haarPhase_prod`, by Tonelli and the unfolding
  `lintegral_haarPhase_tsum_zpow`), and `Λ` is the mixture of its cylinder measure. The weight `w`
  is nondecreasing, so (A.e3) bounds `w(x)ρ̃([x,∞))`. The slab formula is Tonelli again, with the
  substitution `v = ry` at fixed `r` (the invariance of `dy/(ℓy)`).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (SymLevyPair profileMeasure)
open scoped ENNReal NNReal

/-! ## Measures on `(0,∞)` that scale by `λ²` -/

/-- **`b y dy` on `(0,∞)`**. -/
noncomputable def gaussDensity (b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun y => ENNReal.ofReal (b * y)

theorem gaussDensity_Iic (b : ℝ) : gaussDensity b (Iic 0) = 0 := by
  have h : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
    exact id
  rw [gaussDensity, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, h, Measure.restrict_empty, lintegral_zero_measure]

/-- `∫₀ᵗ b y dy = (b/2)t²`. -/
theorem gaussDensity_Ioc {b : ℝ} (hb : 0 ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    gaussDensity b (Ioc 0 t) = ENNReal.ofReal (b / 2 * t ^ 2) := by
  rw [gaussDensity, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self]
  have hI : IntegrableOn (fun y : ℝ => b * y) (Ioc 0 t) :=
    ((continuous_const.mul continuous_id).integrableOn_Icc (a := 0) (b := t)).mono_set
      Ioc_subset_Icc_self
  have e : ENNReal.ofReal (∫ y in Ioc 0 t, b * y) = ∫⁻ y in Ioc 0 t, ENNReal.ofReal (b * y) :=
    ofReal_integral_eq_lintegral_ofReal hI
      ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall fun y hy => mul_nonneg hb hy.1.le))
  rw [← e, ← intervalIntegral.integral_of_le ht, intervalIntegral.integral_const_mul, integral_id]
  congr 1
  ring

/-- `b y dy` restricted to `[1,q)`. -/
theorem gaussDensity_restrict (b q : ℝ) :
    (gaussDensity b).restrict (Ico 1 q) =
      (volume.restrict (Ico 1 q)).withDensity fun θ => ENNReal.ofReal (b * θ) := by
  rw [gaussDensity, restrict_withDensity measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico,
    (inter_eq_left (s := Ico 1 q) (t := Ioi (0 : ℝ))).2
      (fun y hy => show (0 : ℝ) < y from lt_of_lt_of_le one_pos hy.1)]

/-- **A measure on `(0,∞)` that scales by `λ²` on the intervals `(0,t]` scales by `λ²` on every
Borel set.** -/
theorem image_mul_of_Ioc {m : Measure ℝ} (h0 : m (Iic 0) = 0)
    (hfin : ∀ t : ℝ, 0 < t → m (Ioc 0 t) ≠ ⊤) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ t : ℝ, 0 < t → m (Ioc 0 (lam * t)) = ENNReal.ofReal (lam ^ 2) * m (Ioc 0 t))
    {A : Set ℝ} (hA : MeasurableSet A) :
    m ((fun y => lam * y) '' A) = ENNReal.ofReal (lam ^ 2) * m A := by
  have hli : 0 < lam⁻¹ := inv_pos.2 hlam
  have hmeas : Measurable fun y : ℝ => lam⁻¹ * y := measurable_const_mul _
  have himg : (fun y => lam * y) '' A = (fun y => lam⁻¹ * y) ⁻¹' A := by
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [inv_mul_cancel_left₀ hlam.ne']
    · intro hy
      exact ⟨lam⁻¹ * y, hy, mul_inv_cancel_left₀ hlam.ne' y⟩
  have hIoc : ∀ t : ℝ, (fun y => lam⁻¹ * y) ⁻¹' Ioc 0 t = Ioc 0 (lam * t) := by
    intro t
    rw [preimage_const_mul_Ioc₀ _ _ hli, zero_div, div_inv_eq_mul, mul_comm]
  have hext : m.map (fun y => lam⁻¹ * y) = ENNReal.ofReal (lam ^ 2) • m := by
    refine measure_ext_of_Ioc_zero ?_ ?_ ?_ ?_
    · rw [Measure.map_apply hmeas measurableSet_Iic, preimage_const_mul_Iic₀ _ hli, zero_div, h0]
    · rw [Measure.smul_apply, h0, smul_zero]
    · intro t ht
      rw [Measure.map_apply hmeas measurableSet_Ioc, hIoc, h t ht]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin t ht)
    · intro t ht
      rw [Measure.map_apply hmeas measurableSet_Ioc, hIoc, h t ht, Measure.smul_apply, smul_eq_mul]
  rw [himg, ← Measure.map_apply hmeas hA, hext, Measure.smul_apply, smul_eq_mul]

/-- `b y dy` scales by `λ²`. -/
theorem gaussDensity_image_mul {b : ℝ} (hb : 0 ≤ b) {lam : ℝ} (hlam : 0 < lam) {A : Set ℝ}
    (hA : MeasurableSet A) :
    gaussDensity b ((fun y => lam * y) '' A) = ENNReal.ofReal (lam ^ 2) * gaussDensity b A := by
  refine image_mul_of_Ioc (gaussDensity_Iic b)
    (fun t ht => by rw [gaussDensity_Ioc hb ht.le]; exact ENNReal.ofReal_ne_top) hlam
    (fun t ht => ?_) hA
  rw [gaussDensity_Ioc hb (mul_pos hlam ht).le, gaussDensity_Ioc hb ht.le,
    ← ENNReal.ofReal_mul (sq_nonneg lam)]
  congr 1
  ring

/-- `b y dy` has (ii). -/
theorem isSurfaceGaussian_gaussDensity {q b : ℝ} (hq0 : 0 < q) (hb : 0 ≤ b) :
    IsSurfaceGaussian q (gaussDensity b) :=
  ⟨gaussDensity_Iic b, fun t ht => by rw [gaussDensity_Ioc hb ht.le]; exact ENNReal.ofReal_ne_top,
    fun _ hA _ => gaussDensity_image_mul hb hq0 hA⟩

/-- **`prop:strata-cylinder-coordinates`(1), the Gaussian part.** (a') `a(λt) = λ²a(t)` iff
(b') `ℬ(λA) = λ²ℬ(A)` for all `λ > 0` and Borel `A`, iff (c') `β(dθ) = bθ dθ` with `b ≥ 0`; then
`a(t) = (b/2)t²`. -/
theorem strata_cylinder_1_gaussian {q : ℝ} (hq : 1 < q) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (h : IsSurfacePair q Λ B) :
    ((∀ lam t : ℝ, 0 < lam → 0 < t →
          (B (Ioc 0 (lam * t))).toReal = lam ^ 2 * (B (Ioc 0 t)).toReal) ↔
        ∀ lam : ℝ, 0 < lam → ∀ A : Set ℝ, MeasurableSet A →
          B ((fun y => lam * y) '' A) = ENNReal.ofReal (lam ^ 2) * B A) ∧
      ((∀ lam : ℝ, 0 < lam → ∀ A : Set ℝ, MeasurableSet A →
          B ((fun y => lam * y) '' A) = ENNReal.ofReal (lam ^ 2) * B A) ↔
        ∃ b : ℝ, 0 ≤ b ∧ B.restrict (Ico 1 q) =
          (volume.restrict (Ico 1 q)).withDensity fun θ => ENNReal.ofReal (b * θ)) ∧
      ∀ b : ℝ, 0 ≤ b →
        B.restrict (Ico 1 q) = (volume.restrict (Ico 1 q)).withDensity
          (fun θ => ENNReal.ofReal (b * θ)) →
        ∀ t : ℝ, 0 < t → (B (Ioc 0 t)).toReal = b / 2 * t ^ 2 := by
  have hq0 : 0 < q := by linarith
  have h0 : B (Iic 0) = 0 := h.gaussian.1
  have hfin : ∀ t : ℝ, 0 < t → B (Ioc 0 t) ≠ ⊤ := h.gaussian.2.1
  -- (b') gives (a')
  have hba : (∀ lam : ℝ, 0 < lam → ∀ A : Set ℝ, MeasurableSet A →
      B ((fun y => lam * y) '' A) = ENNReal.ofReal (lam ^ 2) * B A) →
      ∀ lam t : ℝ, 0 < lam → 0 < t →
        (B (Ioc 0 (lam * t))).toReal = lam ^ 2 * (B (Ioc 0 t)).toReal := by
    intro hb lam t hlam _
    have e := hb lam hlam (Ioc 0 t) measurableSet_Ioc
    rw [image_mul_left_Ioc hlam, mul_zero] at e
    rw [e, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg lam)]
  -- (a') gives `ℬ = 2a(1) y dy`
  have hab : (∀ lam t : ℝ, 0 < lam → 0 < t →
      (B (Ioc 0 (lam * t))).toReal = lam ^ 2 * (B (Ioc 0 t)).toReal) →
      B = gaussDensity (2 * (B (Ioc 0 1)).toReal) := by
    intro ha
    refine measure_ext_of_Ioc_zero h0 (gaussDensity_Iic _) hfin fun t ht => ?_
    have e := ha t 1 ht one_pos
    rw [mul_one] at e
    rw [gaussDensity_Ioc (by positivity) ht.le, ← ENNReal.ofReal_toReal (hfin t ht), e]
    congr 1
    ring
  -- (c') gives `ℬ = b y dy`
  have hcb : ∀ b : ℝ, 0 ≤ b → B.restrict (Ico 1 q) =
      (volume.restrict (Ico 1 q)).withDensity (fun θ => ENNReal.ofReal (b * θ)) →
      B = gaussDensity b := by
    intro b hb hβ
    have h1 := (knot_atom_cascades_2_gaussian hq).1 B h.gaussian
    have h2 := (knot_atom_cascades_2_gaussian hq).1 _ (isSurfaceGaussian_gaussDensity hq0 hb)
    rw [← h1, ← h2, hβ, gaussDensity_restrict]
  refine ⟨⟨fun ha lam hlam A hA => ?_, hba⟩, ⟨fun hb => ?_, ?_⟩, ?_⟩
  · rw [hab ha]
    exact gaussDensity_image_mul (by positivity) hlam hA
  · refine ⟨2 * (B (Ioc 0 1)).toReal, by positivity, ?_⟩
    rw [hab (hba hb), gaussDensity_restrict]
    rw [← hab (hba hb)]
  · rintro ⟨b, hb, hβ⟩ lam hlam A hA
    rw [hcb b hb hβ]
    exact gaussDensity_image_mul hb hlam hA
  · intro b hb hβ t ht
    rw [hcb b hb hβ, gaussDensity_Ioc hb ht.le, ENNReal.toReal_ofReal (by positivity)]

/-! ## Both parts -/

/-- Two pairs with the same data have the same exponent. -/
theorem symLevyPair_exponent_congr {P Q : SymLevyPair} (ha : P.a = Q.a) (hν : P.ν = Q.ν) :
    P.exponent = Q.exponent := by
  funext ω
  simp only [SymLevyPair.exponent, SymLevyPair.exponentL, ha, hν]

/-- **`prop:strata-cylinder-coordinates`(1), both parts.** `Ψ_{λt}(ω) = Ψ_t(λω)` for all
`λ, t > 0` iff (a) and (a'). -/
theorem strata_cylinder_1_both {q : ℝ} (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (h : IsSurfacePair q Λ B) :
    (∀ lam t : ℝ, 0 < lam → 0 < t → ∀ ω : ℝ,
        surfaceExponent Λ B (lam * t) ω = surfaceExponent Λ B t (lam * ω)) ↔
      (∀ lam t : ℝ, 0 < lam → 0 < t → slab Λ 0 (lam * t) = (slab Λ 0 t).map (fun v => lam * v)) ∧
        ∀ lam t : ℝ, 0 < lam → 0 < t →
          (B (Ioc 0 (lam * t))).toReal = lam ^ 2 * (B (Ioc 0 t)).toReal := by
  have hexp : ∀ t : ℝ, ∀ ht : 0 < t, HasExpData (surfaceExponent Λ B t)
      (surfacePairOf Λ B t h.carried (h.integrable t ht)) :=
    fun t ht ω => (surfacePairOf_exponent B h.carried _ ω).symm
  constructor
  · intro H
    have key : ∀ lam t : ℝ, 0 < lam → 0 < t →
        (B (Ioc 0 (lam * t))).toReal = lam ^ 2 * (B (Ioc 0 t)).toReal ∧
          slab Λ 0 (lam * t) = (slab Λ 0 t).map (fun v => lam * v) := by
      intro lam t hlam ht
      obtain ⟨Q, hQa, hQν, hQ⟩ := line_exponent_data_2 _ _ (hexp t ht) hlam
      have hQ' : HasExpData (surfaceExponent Λ B (lam * t)) Q :=
        fun ω => (H lam t hlam ht ω).trans (hQ ω)
      obtain ⟨ha, hν⟩ := line_exponent_data_1_unique _ _ _ (hexp (lam * t) (mul_pos hlam ht)) hQ'
      exact ⟨ha.trans hQa, hν.trans hQν⟩
    exact ⟨fun lam t hlam ht => (key lam t hlam ht).2, fun lam t hlam ht => (key lam t hlam ht).1⟩
  · rintro ⟨hjump, hgauss⟩ lam t hlam ht ω
    obtain ⟨Q, hQa, hQν, hQ⟩ := line_exponent_data_2 _ _ (hexp t ht) hlam
    have hP : (surfacePairOf Λ B (lam * t) h.carried (h.integrable _ (mul_pos hlam ht))).exponent =
        Q.exponent :=
      symLevyPair_exponent_congr ((hgauss lam t hlam ht).trans hQa.symm)
        ((hjump lam t hlam ht).trans hQν.symm)
    rw [hexp (lam * t) (mul_pos hlam ht) ω, hP]
    exact (hQ ω).symm

/-! ## The jump part, "then" -/

/-- `dy/(ℓy)`-almost every `y` is positive. -/
theorem ae_logHaar_pos (q : ℝ) : ∀ᵐ y ∂(logHaar q), 0 < y :=
  ae_pos_of_Iic_zero (logHaar_Iic q)

/-- **The orbits of `η ⊗ ρ̃`**: `Λ_{η ⊗ ρ̃}` is the image of `(dy/(ℓy)) ⊗ ρ̃` under
`(y, r) ↦ (y, ry)`. -/
theorem orbitMixture_haarPhase_prod {q : ℝ} (hq : 1 < q) (ρ : Measure ℝ) [SFinite ρ] :
    orbitMixture q ((haarPhase q).prod ρ) =
      ((logHaar q).prod ρ).map (fun p => (p.1, p.2 * p.1)) := by
  have hf : Measurable fun p : ℝ × ℝ => (p.1, p.2 * p.1) := by fun_prop
  ext s hs
  have hind : ∀ n : ℤ, Measurable ((orbitPt q n ⁻¹' s).indicator (1 : ℝ × ℝ → ℝ≥0∞)) :=
    fun n => measurable_one.indicator (measurable_orbitPt q n hs)
  have hsum : Measurable fun p : ℝ × ℝ => ∑' n : ℤ, (orbitPt q n ⁻¹' s).indicator 1 p :=
    Measurable.tsum fun n => hind n
  rw [orbitMixture_apply q _ hs, Measure.map_apply hf hs,
    ← lintegral_indicator_one (hf hs),
    lintegral_prod_symm _ ((measurable_one.indicator (hf hs)).aemeasurable)]
  simp_rw [← lintegral_indicator_one (measurable_orbitPt q _ hs)]
  rw [← lintegral_tsum fun n => (hind n).aemeasurable, lintegral_prod_symm _ hsum.aemeasurable]
  refine lintegral_congr fun r => ?_
  have hG : Measurable fun u : ℝ => s.indicator (1 : ℝ × ℝ → ℝ≥0∞) (u, r * u) :=
    (measurable_one.indicator hs).comp (measurable_id.prodMk (measurable_const.mul measurable_id))
  have e : ∀ y : ℝ, ((fun p : ℝ × ℝ => (p.1, p.2 * p.1)) ⁻¹' s).indicator
      (1 : ℝ × ℝ → ℝ≥0∞) (y, r) = s.indicator 1 (y, r * y) := fun y => rfl
  simp_rw [e]
  rw [← lintegral_haarPhase_tsum_zpow hq hG]
  refine lintegral_congr fun θ => tsum_congr fun n => ?_
  have ho : orbitPt q n (θ, r) = (θ * q ^ n, r * (θ * q ^ n)) := by
    simp only [orbitPt, mul_assoc]
  change (orbitPt q n ⁻¹' s).indicator 1 (θ, r) = s.indicator 1 (θ * q ^ n, r * (θ * q ^ n))
  rw [← ho]
  rfl

/-- **The slab formula**: for `Λ` the image of `(dy/(ℓy)) ⊗ ρ̃`,
`Λ((0,t] × dv) = ℓ⁻¹ρ̃([v/t,∞)) dv/v`. -/
theorem slab_logHaar_prod {q : ℝ} (hq : 1 < q) {ρ : Measure ℝ} [SFinite ρ]
    (hρ0 : ρ (Iic 0) = 0) (hfin : ∀ x : ℝ, 0 < x → ρ (Ici x) ≠ ⊤) {t : ℝ} (ht : 0 < t) :
    slab (((logHaar q).prod ρ).map fun p => (p.1, p.2 * p.1)) 0 t =
      profileMeasure (fun v => (ρ (Ici (v / t))).toReal / Real.log q) := by
  have hl : 0 < Real.log q := Real.log_pos hq
  have hf : Measurable fun p : ℝ × ℝ => (p.1, p.2 * p.1) := by fun_prop
  ext A hA
  have hS : MeasurableSet (Ioc 0 t ×ˢ A) := measurableSet_Ioc.prod hA
  rw [slab_apply _ _ _ hA, Measure.map_apply hf hS, ← lintegral_indicator_one (hf hS),
    lintegral_prod_symm _ ((measurable_one.indicator (hf hS)).aemeasurable)]
  -- the substitution `v = ry` at fixed `r > 0`
  set F : ℝ → ℝ → ℝ≥0∞ := fun r v => if v ≤ r * t then A.indicator 1 v else 0 with hF
  have hFm : Measurable (Function.uncurry F) :=
    Measurable.ite (measurableSet_le measurable_snd (measurable_fst.mul_const t))
      ((measurable_one.indicator hA).comp measurable_snd) measurable_const
  have hinner : ∀ r : ℝ, 0 < r →
      ∫⁻ y, ((fun p : ℝ × ℝ => (p.1, p.2 * p.1)) ⁻¹' (Ioc 0 t ×ˢ A)).indicator 1 (y, r)
        ∂(logHaar q) = ∫⁻ v, F r v ∂(logHaar q) := by
    intro r hr
    have hG : Measurable (F r) :=
      Measurable.ite measurableSet_Iic (measurable_one.indicator hA) measurable_const
    rw [← lintegral_logHaar_comp_mul q hr hG]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_logHaar_pos q] with y hy
    have hiff : r * y ≤ r * t ↔ y ≤ t := mul_le_mul_iff_of_pos_left hr
    simp only [hF, hiff]
    by_cases h1 : y ≤ t <;> by_cases h2 : r * y ∈ A <;> simp [h1, h2, hy]
  rw [lintegral_congr_ae ((ae_pos_of_Iic_zero hρ0).mono fun r hr => hinner r hr),
    lintegral_lintegral_swap hFm.aemeasurable,
    lintegral_logHaar q (show Measurable fun v => ∫⁻ r, F r v ∂ρ from
      Measurable.lintegral_prod_left' hFm), profileMeasure,
    withDensity_apply _ hA, ← lintegral_indicator hA]
  refine setLIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : (0 : ℝ) < v := hv
  have hFv : ∫⁻ r, F r v ∂ρ = A.indicator 1 v * ρ (Ici (v / t)) := by
    rw [← lintegral_indicator_const measurableSet_Ici]
    refine lintegral_congr fun r => ?_
    simp only [hF, indicator_apply, mem_Ici, div_le_iff₀ ht]
  rw [hFv]
  by_cases hvA : v ∈ A
  · rw [indicator_of_mem hvA, indicator_of_mem hvA, Pi.one_apply, one_mul]
    have hX : ρ (Ici (v / t)) = ENNReal.ofReal (ρ (Ici (v / t))).toReal :=
      (ENNReal.ofReal_toReal (hfin _ (div_pos hv0 ht))).symm
    conv_lhs => rw [hX]
    rw [← ENNReal.ofReal_mul (one_div_pos.2 (mul_pos hl hv0)).le]
    congr 1
    field_simp
  · rw [indicator_of_notMem hvA, indicator_of_notMem hvA, zero_mul, mul_zero]

/-- **`prop:strata-cylinder-coordinates`(1), the jump part, "then".** If `σ = η ⊗ ρ̃`, `Λ` is the
image of `(dy/(ℓy)) ⊗ ρ̃` under `(y, r) ↦ (y, ry)`, `ρ̃([x,∞)) < ∞` for `x > 0`, and
`ϖ_t(dv) = k(v/t) dv/v` with `k(x) := ℓ⁻¹ ρ̃([x,∞))`, nonincreasing. The node's `ρ̃` is
σ-finite, so `ρ̃` is taken s-finite, which `η ⊗ ρ̃` needs to be the product measure. -/
theorem strata_cylinder_1_then {q : ℝ} (hq : 1 < q) (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ)
    (h : IsSurfacePair q Λ B) (ρ : Measure ℝ) [SFinite ρ] (hρ0 : ρ (Iic 0) = 0)
    (hρ : cylMeasure q Λ = (haarPhase q).prod ρ) :
    Λ = ((logHaar q).prod ρ).map (fun p => (p.1, p.2 * p.1)) ∧
      (∀ x : ℝ, 0 < x → ρ (Ici x) ≠ ⊤) ∧
      AntitoneOn (fun x => (ρ (Ici x)).toReal / Real.log q) (Ioi 0) ∧
      ∀ t : ℝ, 0 < t →
        slab Λ 0 t = profileMeasure (fun v => (ρ (Ici (v / t))).toReal / Real.log q) := by
  have hl : 0 < Real.log q := Real.log_pos hq
  obtain ⟨hσ, hmix⟩ := cylMeasure_spec hq h.carried h.invariant
  have hΛ : Λ = ((logHaar q).prod ρ).map (fun p => (p.1, p.2 * p.1)) := by
    rw [← orbitMixture_haarPhase_prod hq ρ, ← hρ, hmix]
  have hint : IsCylIntegrable ((haarPhase q).prod ρ) := by
    rw [← hρ]
    refine (knot_atom_cascades_2_integrable hq _ hσ).1.1 ?_
    rw [hmix]
    exact h.integrable
  have hw : ∫⁻ r, ENNReal.ofReal (cylWeight r) ∂ρ ≠ ⊤ :=
    (isCylIntegrable_prod_iff hq ρ hρ0).1 hint
  have hfin : ∀ x : ℝ, 0 < x → ρ (Ici x) ≠ ⊤ := by
    intro x hx
    have hle : ENNReal.ofReal (cylWeight x) * ρ (Ici x) ≤
        ∫⁻ r, ENNReal.ofReal (cylWeight r) ∂ρ := by
      rw [← setLIntegral_const]
      refine (setLIntegral_mono measurable_cylWeight.ennreal_ofReal fun r hr => ?_).trans
        (setLIntegral_le_lintegral _ _)
      exact ENNReal.ofReal_le_ofReal (cylWeight_mono hx.le hr)
    intro htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (cylWeight_pos hx)).ne'] at hle
    exact hw (top_le_iff.1 hle)
  refine ⟨hΛ, hfin, fun x hx y _ hxy => ?_, fun t ht => ?_⟩
  · exact div_le_div_of_nonneg_right
      (ENNReal.toReal_mono (hfin x hx) (measure_mono (Ici_subset_Ici.2 hxy))) hl.le
  · rw [hΛ]
    exact slab_logHaar_prod hq hρ0 hfin ht

end Pyramids
