/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.FamilyStructure
import AffineHemigroup.RotationInvariant
import AffineHemigroup.LineLevyUnique
import AffineHemigroup.ParameterSpace
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# `prop:what-does-not-lift`: what does not lift

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:what-does-not-lift`, chapter 3. Wave 2b:
the two declarations moved here from `PyramidsSkeleton.Ch03Pyramid`, their statements unchanged.

## The route

* **The polar decomposition, without a Haar measure on `O(d)`.** The printed proof averages over
  `O(d)`. Here the measure `ν' := ∫_{(0,∞)} σ_r ν̄(dr)` is built (`Measure.bind`), and `ν = ν'` by
  the affine export's `eq_of_rotationInvariant`: both are invariant under every linear isometry,
  null at `0`, finite off every ball, and have the same image `ν̄` under `|·|`. Then the display is
  `ν'{x : |⟨e,x⟩| ∈ B} = ∫ σ_r{x : |⟨e,x⟩| ∈ B} ν̄(dr)`, with `σ_r{|⟨e,x⟩| ∈ B} = D_rβ_d(B)` after
  an isometry taking `e₀` to `e` (the surface measure is invariant, `toSphere_map_isometry`).
* **`β_d` is absolutely continuous for `d ≥ 2`** (`betaLaw_absolutelyContinuous`), without its
  density: `σ{η : η₀ ∈ M}` is `d` times the volume of the cone `{x ≠ 0, |x| < 1 : x₀/|x| ∈ M}`, and
  that cone, off the null line `{x₁ = 0}`, is the image of the null set `{y : y₀ ∈ M, |y₀| < 1, y ≠
  y₀e₀}` under the map `y ↦ y - y₀e₀ + (|y - y₀e₀| y₀ (1 - y₀²)^{-1/2}) e₀`, differentiable there; a
  differentiable image of a null set is null (Mathlib's
  `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`).
* **The last sentence**: the Lévy measure `ν` of a rotation-invariant law is rotation invariant
  (`triplet_rotation`, A42 with A39(ii)); A42 at the row `eᵀ` gives the triplet of the marginal,
  with Lévy measure the image of `ν` off `0`; a pair `(a, ϖ)` with the marginal's exponent has the
  triplet `(2a, ϖ_s, 0)` (the affine export's `symLevyTriplet`), so A39(ii) identifies the two Lévy
  measures, and an atom of `ϖ` at `v > 0` would be an atom of the absolutely continuous folded
  measure.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal RealInnerProductSpace Pointwise

variable {d : ℕ}

/-! ## Null sets of `ℝ^d` -/

/-- A cylinder over a null set of one coordinate is null. -/
theorem volume_coord_null (i : Fin d) {M : Set ℝ} (hM : volume M = 0) :
    volume {x : Rd d | x i ∈ M} = 0 := by
  classical
  obtain ⟨M', hMM', hM'm, hM'0⟩ := exists_measurable_superset_of_null hM
  refine measure_mono_null (t := {x : Rd d | x i ∈ M'}) (fun x hx => hMM' hx) ?_
  set f : Fin d → Set ℝ := Function.update (fun _ => univ) i M' with hf
  have hfm : ∀ j, MeasurableSet (f j) := by
    intro j
    by_cases h : j = i
    · subst h; simpa [hf] using hM'm
    · simp [hf, Function.update_of_ne h]
  have hset : {x : Rd d | x i ∈ M'} = WithLp.ofLp ⁻¹' (Set.univ.pi f) := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, Set.mem_pi, mem_univ, true_implies]
    constructor
    · intro hx j
      by_cases h : j = i
      · subst h; simpa [hf] using hx
      · simp [hf, Function.update_of_ne h]
    · intro hx
      simpa [hf] using hx i
  rw [hset, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi hfm).nullMeasurableSet, volume_pi, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [hf] using hM'0)

/-- `x ↦ x - x₀ e₀`. -/
noncomputable def perp0 [NeZero d] (x : Rd d) : Rd d := x - x 0 • ebasis (0 : Fin d)

theorem ebasis_zero_apply [NeZero d] (j : Fin d) :
    (ebasis (0 : Fin d)) j = if j = 0 then 1 else 0 := by
  simp [ebasis, PiLp.single_apply]

theorem perp0_apply_zero [NeZero d] (x : Rd d) : (perp0 x) 0 = 0 := by
  simp [perp0, ebasis_zero_apply]

theorem perp0_add [NeZero d] (x : Rd d) (c : ℝ) : perp0 (perp0 x + c • ebasis 0) = perp0 x := by
  have h0 : (perp0 x + c • ebasis (0 : Fin d)) 0 = c := by
    simp [perp0_apply_zero, ebasis_zero_apply]
  rw [perp0, h0]
  abel

theorem perp0_add_self [NeZero d] (x : Rd d) : perp0 x + x 0 • ebasis 0 = x := by
  simp [perp0]

theorem norm_sq_perp0 [NeZero d] (x : Rd d) : ‖x‖ ^ 2 = x 0 ^ 2 + ‖perp0 x‖ ^ 2 := by
  have hin : ⟪x 0 • ebasis (0 : Fin d), perp0 x⟫ = 0 := by
    rw [real_inner_smul_left]
    simp [ebasis, EuclideanSpace.inner_single_left, perp0_apply_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℝ) _ _ hin
  rw [add_comm, perp0_add_self] at h
  have he : ‖ebasis (0 : Fin d)‖ = 1 := by simp [ebasis]
  rw [norm_smul, he, mul_one, Real.norm_eq_abs] at h
  nlinarith [sq_abs (x 0)]

/-- **The cone of directions over a null set is null** (`d ≥ 2`):
`{x ≠ 0 : x₀/|x| ∈ M}` is null when `M` is. -/
theorem volume_direction_null (hd : 2 ≤ d) [NeZero d] {M : Set ℝ} (hM : volume M = 0) :
    volume {x : Rd d | x ≠ 0 ∧ x 0 / ‖x‖ ∈ M} = 0 := by
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  have hi1ne : i1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [hi1] at this
  set c0 : Rd d →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin d) with hc0
  have hc0x : ∀ x, c0 x = x 0 := fun x => rfl
  set s : Set (Rd d) := {y | y 0 ∈ M ∧ y 0 ^ 2 < 1 ∧ perp0 y ≠ 0} with hs
  set Φ : Rd d → Rd d := fun y =>
    perp0 y + (‖perp0 y‖ * c0 y / Real.sqrt (1 - c0 y ^ 2)) • ebasis 0 with hΦ
  have hs0 : volume s = 0 := measure_mono_null (fun y hy => hy.1) (volume_coord_null 0 hM)
  have hdiff : DifferentiableOn ℝ Φ s := by
    intro y hy
    refine DifferentiableAt.differentiableWithinAt ?_
    have hp : DifferentiableAt ℝ (fun y : Rd d => perp0 y) y := by
      have : (fun y : Rd d => perp0 y) = fun y => y - c0 y • ebasis 0 := rfl
      rw [this]
      fun_prop
    have hn : DifferentiableAt ℝ (fun y : Rd d => ‖perp0 y‖) y := hp.norm ℝ hy.2.2
    have hpos : 0 < 1 - c0 y ^ 2 := by rw [hc0x]; linarith [hy.2.1]
    have hsq : DifferentiableAt ℝ (fun y : Rd d => Real.sqrt (1 - c0 y ^ 2)) y :=
      (by fun_prop : DifferentiableAt ℝ (fun y : Rd d => 1 - c0 y ^ 2) y).sqrt hpos.ne'
    have hsqne : Real.sqrt (1 - c0 y ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    have hq : DifferentiableAt ℝ
        (fun y : Rd d => ‖perp0 y‖ * c0 y / Real.sqrt (1 - c0 y ^ 2)) y :=
      by
        simp only [div_eq_mul_inv]
        exact (hn.mul c0.differentiableAt).mul (hsq.inv hsqne)
    exact hp.add (hq.smul_const _)
  have hcover : {x : Rd d | x ≠ 0 ∧ x 0 / ‖x‖ ∈ M} ⊆ Φ '' s ∪ {x | x i1 ∈ ({0} : Set ℝ)} := by
    rintro x ⟨hx0, hxM⟩
    by_cases hp : perp0 x = 0
    · right
      have h := congrArg (fun z : Rd d => z i1) hp
      simp only [perp0, PiLp.sub_apply, PiLp.smul_apply, ebasis_zero_apply, if_neg hi1ne,
        smul_eq_mul, mul_zero, sub_zero] at h
      exact h
    · left
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hppos : 0 < ‖perp0 x‖ := norm_pos_iff.2 hp
      have hnsq := norm_sq_perp0 x
      set y := perp0 x + (x 0 / ‖x‖) • ebasis (0 : Fin d) with hy
      have hy0 : y 0 = x 0 / ‖x‖ := by
        simp [hy, perp0_apply_zero, ebasis_zero_apply]
      have hpy : perp0 y = perp0 x := perp0_add x _
      have hlt : (x 0 / ‖x‖) ^ 2 < 1 := by
        rw [div_pow, div_lt_one (by positivity)]
        nlinarith
      have hroot : Real.sqrt (1 - (x 0 / ‖x‖) ^ 2) = ‖perp0 x‖ / ‖x‖ := by
        rw [show 1 - (x 0 / ‖x‖) ^ 2 = (‖perp0 x‖ / ‖x‖) ^ 2 by
          field_simp
          linarith]
        exact Real.sqrt_sq (by positivity)
      refine ⟨y, ⟨hy0 ▸ hxM, hy0 ▸ hlt, hpy ▸ hp⟩, ?_⟩
      simp only [hΦ, hc0x, hpy, hy0, hroot]
      have hcoef : ‖perp0 x‖ * (x 0 / ‖x‖) / (‖perp0 x‖ / ‖x‖) = x 0 := by
        field_simp
      rw [hcoef, perp0_add_self]
  exact measure_mono_null hcover (measure_union_null
    (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hs0)
    (volume_coord_null i1 Real.volume_singleton))

/-! ## The normalised surface measure -/

theorem measurableSet_coord [NeZero d] {M : Set ℝ} (hM : MeasurableSet M) :
    MeasurableSet {x : Rd d | x 0 ∈ M} :=
  (EuclideanSpace.proj (0 : Fin d)).continuous.measurable hM

/-- **`σ̄{η : η₀ ∈ M} = 0` for a null set `M`**, `d ≥ 2`. -/
theorem normSphere_coord_null (hd : 2 ≤ d) [NeZero d] {M : Set ℝ} (hM : volume M = 0) :
    normSphere d {x : Rd d | x 0 ∈ M} = 0 := by
  obtain ⟨M', hMM', hM'm, hM'0⟩ := exists_measurable_superset_of_null hM
  refine measure_mono_null (t := {x : Rd d | x 0 ∈ M'}) (fun x hx => hMM' hx) ?_
  have hsm := measurableSet_coord (d := d) hM'm
  rw [normSphere, Measure.smul_apply, Measure.map_apply measurable_subtype_coe hsm,
    Measure.toSphere_apply' _ (measurable_subtype_coe hsm)]
  have hnull : volume (Ioo (0 : ℝ) 1 • (Subtype.val '' (Subtype.val ⁻¹' {x : Rd d | x 0 ∈ M'} :
      Set (sphere (0 : Rd d) 1)))) = 0 := by
    refine measure_mono_null ?_ (volume_direction_null hd hM'0)
    intro x hx
    obtain ⟨r, hr, y, ⟨η, hη, rfl⟩, rfl⟩ := Set.mem_smul.1 hx
    have hη1 : ‖(η : Rd d)‖ = 1 := norm_eq_of_mem_sphere η
    have hr0 : 0 < r := hr.1
    have hηne : (η : Rd d) ≠ 0 := by
      intro h; rw [h, norm_zero] at hη1; exact zero_ne_one hη1
    refine ⟨smul_ne_zero hr0.ne' hηne, ?_⟩
    rw [norm_smul, hη1, mul_one, Real.norm_eq_abs, abs_of_pos hr0, PiLp.smul_apply, smul_eq_mul,
      mul_div_cancel_left₀ _ hr0.ne']
    exact hη
  rw [hnull, mul_zero, smul_zero]

theorem sphereLaw_one : sphereLaw d 1 = normSphere d := by
  simp [sphereLaw]

/-- **`β_d` is absolutely continuous**, `d ≥ 2`. -/
theorem betaLaw_absolutelyContinuous (hd : 2 ≤ d) [NeZero d] : betaLaw d ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_
  have hmeas : Measurable fun η : Rd d => |η 0| :=
    continuous_abs.measurable.comp (EuclideanSpace.proj (0 : Fin d)).continuous.measurable
  rw [betaLaw, Measure.map_apply hmeas hN, sphereLaw_one]
  have h2 : volume (N ∪ -N) = 0 :=
    measure_union_null hN0 (by rw [Measure.measure_neg]; exact hN0)
  refine measure_mono_null (fun η hη => ?_) (normSphere_coord_null hd h2)
  simp only [mem_preimage] at hη
  simp only [mem_setOf_eq, mem_union, Set.mem_neg]
  rcases abs_choice (η 0) with h | h
  · left; rw [← h]; exact hη
  · right; rw [← h]; exact hη

/-- `σ̄` is invariant under every linear isometry. -/
theorem normSphere_map_isometry (Q : Rd d ≃ₗᵢ[ℝ] Rd d) : (normSphere d).map Q = normSphere d := by
  rw [normSphere, Measure.map_smul, Measure.map_map Q.continuous.measurable measurable_subtype_coe]
  have h : (Q ∘ Subtype.val : sphere (0 : Rd d) 1 → Rd d) = Subtype.val ∘ sphereMap Q := rfl
  rw [h, ← Measure.map_map measurable_subtype_coe (measurable_sphereMap Q), toSphere_map_isometry]

/-- `σ̄` of a set containing, or missing, the whole unit sphere. -/
theorem normSphere_of_sphere (hd : 1 ≤ d) {s : Set (Rd d)} (hs : MeasurableSet s) :
    ((∀ x : Rd d, ‖x‖ = 1 → x ∈ s) → normSphere d s = 1) ∧
      ((∀ x : Rd d, ‖x‖ = 1 → x ∉ s) → normSphere d s = 0) := by
  obtain ⟨harea, hpos⟩ := sphereArea_eq_toSphere (d := d) hd
  have hne0 : (volume : Measure (Rd d)).toSphere univ ≠ 0 := by
    rw [← harea]; exact ENNReal.ofReal_pos.2 hpos |>.ne'
  have hnetop : (volume : Measure (Rd d)).toSphere univ ≠ ⊤ := by
    rw [← harea]; exact ENNReal.ofReal_ne_top
  rw [normSphere, Measure.smul_apply, Measure.map_apply measurable_subtype_coe hs, smul_eq_mul]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hpre : (Subtype.val ⁻¹' s : Set (sphere (0 : Rd d) 1)) = univ :=
      eq_univ_of_forall fun η => h η (norm_eq_of_mem_sphere η)
    rw [hpre, ENNReal.inv_mul_cancel hne0 hnetop]
  · have hpre : (Subtype.val ⁻¹' s : Set (sphere (0 : Rd d) 1)) = ∅ :=
      eq_empty_of_forall_notMem fun η => h η (norm_eq_of_mem_sphere η)
    rw [hpre, measure_empty, mul_zero]

theorem sphereLaw_apply (r : ℝ) {s : Set (Rd d)} (hs : MeasurableSet s) :
    sphereLaw d r s = normSphere d ((fun x => r • x) ⁻¹' s) :=
  Measure.map_apply (measurable_const_smul r) hs

/-- `σ_r` is invariant under every linear isometry. -/
theorem sphereLaw_map_isometry (Q : Rd d ≃ₗᵢ[ℝ] Rd d) (r : ℝ) :
    (sphereLaw d r).map Q = sphereLaw d r := by
  rw [sphereLaw, Measure.map_map Q.continuous.measurable (measurable_const_smul r)]
  have h : (Q ∘ fun x : Rd d => r • x) = (fun x => r • x) ∘ Q := by
    funext x; simp
  rw [h, ← Measure.map_map (measurable_const_smul r) Q.continuous.measurable,
    normSphere_map_isometry]

theorem measurable_sphereLaw (hd : 1 ≤ d) : Measurable (sphereLaw d) := by
  haveI : IsProbabilityMeasure (normSphere d) :=
    ⟨(normSphere_of_sphere hd MeasurableSet.univ).1 fun _ _ => trivial⟩
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hS : MeasurableSet {p : ℝ × Rd d | p.1 • p.2 ∈ s} := (measurable_fst.smul measurable_snd) hs
  have h := measurable_measure_prodMk_left (ν := normSphere d) hS
  convert h using 1
  funext r
  rw [sphereLaw_apply r hs]
  rfl

/-! ## The polar decomposition -/

/-- **The polar decomposition of a rotation-invariant Lévy measure**, `d ≥ 1`:
`ν(s) = ∫_{(0,∞)} σ_r(s) ν̄(dr)` for every Borel set `s`, with `ν̄` the image of `ν` under `|·|`.
The measure `ν' := ∫ σ_r ν̄(dr)` (`Measure.bind`) is invariant under every linear isometry, null at
`0`, finite off every ball and has the radial image `ν̄`; the affine export's
`eq_of_rotationInvariant` gives `ν = ν'`. Split out of `what_does_not_lift` in wave 2g, which
`what_does_not_lift_chain_strict` reads too. -/
theorem rotationInvariant_polar (hd1 : 1 ≤ d) (ν : Measure (Rd d)) (hν0 : ν {0} = 0)
    (hνint : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν ≠ ⊤) (hrot : IsRotationInvariant ν)
    {s : Set (Rd d)} (hs : MeasurableSet s) :
    ν s = ∫⁻ r, sphereLaw d r s ∂((ν.map fun x => ‖x‖).restrict (Ioi 0)) := by
  -- the invariance, in the isometry form
  have hrotQ : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, ν.map Q = ν := fun Q => by
    have h := hrot (isoMat Q) (isoMat_mem_orthSet Q)
    rw [push, lin_isoMat] at h
    exact h
  -- finiteness off every ball
  set T0 : LevyTriplet d := ⟨0, ν, 0, Matrix.PosSemidef.zero, hν0, hνint⟩ with hT0
  have hfin : ∀ ε : ℝ, 0 < ε → ν {x | ε < ‖x‖} ≠ ⊤ := fun ε hε => T0.measure_norm_gt_ne_top hε
  have hnorm : Measurable fun x : Rd d => ‖x‖ := continuous_norm.measurable
  set νbar : Measure ℝ := (ν.map fun x => ‖x‖).restrict (Ioi 0) with hνbar
  set ν' : Measure (Rd d) := νbar.bind (sphereLaw d) with hν'
  have hbind : ∀ s, MeasurableSet s → ν' s = ∫⁻ r, sphereLaw d r s ∂νbar := fun s hs =>
    Measure.bind_apply hs (measurable_sphereLaw hd1).aemeasurable
  have hcongr : ∀ f g : ℝ → ℝ≥0∞, (∀ r, 0 < r → f r = g r) →
      ∫⁻ r, f r ∂νbar = ∫⁻ r, g r ∂νbar := fun f g h =>
    setLIntegral_congr_fun measurableSet_Ioi fun r hr => h r hr
  -- `σ_r` of a radial set
  have hrad_set : ∀ (r : ℝ), 0 < r → ∀ p : ℝ → Prop, MeasurableSet {x : Rd d | p ‖x‖} →
      sphereLaw d r {x | p ‖x‖} = {t | p t}.indicator 1 r := by
    intro r hr p hp
    rw [sphereLaw_apply r hp]
    have hpre : MeasurableSet ((fun x : Rd d => r • x) ⁻¹' {x | p ‖x‖}) :=
      measurable_const_smul r hp
    by_cases hpr : p r
    · rw [indicator_of_mem (show r ∈ {t | p t} from hpr), Pi.one_apply]
      refine (normSphere_of_sphere hd1 hpre).1 fun x hx => ?_
      simp only [mem_preimage, mem_setOf_eq, norm_smul, hx, mul_one, Real.norm_eq_abs,
        abs_of_pos hr]
      exact hpr
    · rw [indicator_of_notMem (show r ∉ {t | p t} from hpr)]
      refine (normSphere_of_sphere hd1 hpre).2 fun x hx => ?_
      simp only [mem_preimage, mem_setOf_eq, norm_smul, hx, mul_one, Real.norm_eq_abs,
        abs_of_pos hr]
      exact hpr
  -- (a) `ν'` is invariant
  have h'rot : ∀ Q : Rd d ≃ₗᵢ[ℝ] Rd d, ν'.map Q = ν' := by
    intro Q
    ext s hs
    rw [Measure.map_apply Q.continuous.measurable hs, hbind _ (Q.continuous.measurable hs),
      hbind s hs]
    refine lintegral_congr fun r => ?_
    rw [← Measure.map_apply Q.continuous.measurable hs, sphereLaw_map_isometry]
  -- (b) `ν'{0} = 0`
  have h'0 : ν' {0} = 0 := by
    rw [hbind _ (measurableSet_singleton 0)]
    rw [hcongr _ (fun _ => 0) fun r hr => ?_, lintegral_zero]
    have h := hrad_set r hr (fun t => t = 0) (measurableSet_eq_fun hnorm measurable_const)
    have hset : {x : Rd d | ‖x‖ = 0} = {0} := by ext x; simp
    rw [hset] at h
    rw [h, indicator_of_notMem (show r ∉ {t : ℝ | t = 0} from hr.ne')]
  -- (c) `ν'` is finite off every ball
  have h'fin : ∀ ε : ℝ, 0 < ε → ν' {x | ε < ‖x‖} ≠ ⊤ := by
    intro ε hε
    have hm : MeasurableSet {x : Rd d | ε < ‖x‖} := measurableSet_lt measurable_const hnorm
    rw [hbind _ hm, hcongr (fun r => sphereLaw d r {x : Rd d | ε < ‖x‖}) ((Ioi ε).indicator 1)
      (fun r hr => hrad_set r hr (fun t => ε < t) hm),
      lintegral_indicator_one measurableSet_Ioi]
    refine ne_top_of_le_ne_top (hfin ε hε) ?_
    rw [hνbar, Measure.restrict_apply measurableSet_Ioi]
    refine (measure_mono inter_subset_left).trans (le_of_eq ?_)
    rw [Measure.map_apply hnorm measurableSet_Ioi]
    rfl
  -- (d) the radial images agree
  have hrad : ν.map (fun x => ‖x‖) = ν'.map (fun x => ‖x‖) := by
    ext B hB
    rw [Measure.map_apply hnorm hB, Measure.map_apply hnorm hB, hbind _ (hnorm hB),
      hcongr (fun r => sphereLaw d r ((fun x : Rd d => ‖x‖) ⁻¹' B)) (B.indicator 1)
        (fun r hr => hrad_set r hr (fun t => t ∈ B) (hnorm hB)),
      lintegral_indicator_one hB, hνbar, Measure.restrict_apply hB,
      Measure.map_apply hnorm (hB.inter measurableSet_Ioi)]
    have hsplit := measure_inter_add_sdiff (μ := ν) ((fun x : Rd d => ‖x‖) ⁻¹' B)
      (hnorm (measurableSet_Ioi (a := (0 : ℝ))))
    have hdiff : ν ((fun x : Rd d => ‖x‖) ⁻¹' B \ (fun x : Rd d => ‖x‖) ⁻¹' Ioi 0) = 0 := by
      refine measure_mono_null (fun x hx => ?_) hν0
      have h1 : ¬ 0 < ‖x‖ := hx.2
      simpa using h1
    rw [hdiff, add_zero] at hsplit
    rw [← hsplit]
    rfl
  have hνeq : ν = ν' := eq_of_rotationInvariant hd1 hrotQ h'rot hν0 h'0 hfin h'fin hrad
  have h1 : ν s = ν' s := by rw [← hνeq]
  rw [h1, hbind s hs]

/-! ## `prop:what-does-not-lift` -/

/-- **`prop:what-does-not-lift`, the display and absolute continuity.** For `d ≥ 2`, a unit
vector `e` and a rotation-invariant Lévy measure `ν`, with `ν̄` its image under `|·|`: the folded
Lévy measure of the marginal is `∫_{(0,∞)} D_r β_d ν̄(dr)`, and it is absolutely continuous. -/
theorem what_does_not_lift [NeZero d] (hd : 2 ≤ d) (e : Rd d) (he : ‖e‖ = 1)
    (ν : Measure (Rd d)) (hν0 : ν {0} = 0)
    (hνint : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν ≠ ⊤) (hrot : IsRotationInvariant ν) :
    (∀ B : Set ℝ, MeasurableSet B →
        foldedMarginal e ν B =
          ∫⁻ r, ((betaLaw d).map fun y => r * y) B ∂((ν.map fun x => ‖x‖).restrict (Ioi 0))) ∧
      foldedMarginal e ν ≪ volume := by
  have hd1 : 1 ≤ d := by omega
  set νbar : Measure ℝ := (ν.map fun x => ‖x‖).restrict (Ioi 0) with hνbar
  have hcongr : ∀ f g : ℝ → ℝ≥0∞, (∀ r, 0 < r → f r = g r) →
      ∫⁻ r, f r ∂νbar = ∫⁻ r, g r ∂νbar := fun f g h =>
    setLIntegral_congr_fun measurableSet_Ioi fun r hr => h r hr
  -- the polar decomposition
  have hpolar : ∀ s, MeasurableSet s → ν s = ∫⁻ r, sphereLaw d r s ∂νbar := fun s hs =>
    rotationInvariant_polar hd1 ν hν0 hνint hrot hs
  -- an isometry taking `e₀` to `e`
  set e0 : Rd d := ebasis (0 : Fin d) with he0
  have he0n : ‖e0‖ = 1 := by simp [he0, ebasis]
  set Q : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (e0 - e))ᗮ with hQ
  have hQe : Q e0 = e := Submodule.reflection_sub (he0n.trans he.symm)
  have hinner : ∀ x : Rd d, ⟪e, x⟫ = (Q.symm x) 0 := by
    intro x
    rw [← hQe, inner_isometry_symm]
    simp [he0, ebasis, EuclideanSpace.inner_single_left]
  have hcoord : Measurable fun x : Rd d => x 0 :=
    (EuclideanSpace.proj (0 : Fin d)).continuous.measurable
  -- `σ_r` of the folded marginal set
  have hsph : ∀ r : ℝ, 0 < r → ∀ B : Set ℝ, MeasurableSet B →
      sphereLaw d r ((fun x : Rd d => |⟪e, x⟫|) ⁻¹' (B ∩ Ioi 0)) =
        ((betaLaw d).map fun y => r * y) B := by
    intro r hr B hB
    have hf : Measurable fun x : Rd d => |⟪e, x⟫| := by fun_prop
    have hSm : MeasurableSet ((fun x : Rd d => |⟪e, x⟫|) ⁻¹' (B ∩ Ioi 0)) :=
      hf (hB.inter measurableSet_Ioi)
    have hbm : Measurable fun η : Rd d => |η 0| := continuous_abs.measurable.comp hcoord
    rw [sphereLaw_apply r hSm, Measure.map_apply (measurable_const_mul r) hB, betaLaw,
      Measure.map_apply hbm (measurable_const_mul r hB), sphereLaw_one]
    -- rotate `e` to `e₀`
    have hset1 : (fun x : Rd d => r • x) ⁻¹' ((fun x : Rd d => |⟪e, x⟫|) ⁻¹' (B ∩ Ioi 0)) =
        Q.symm ⁻¹' {y : Rd d | r * |y 0| ∈ B ∩ Ioi 0} := by
      ext x
      simp only [mem_preimage, mem_setOf_eq, hinner, LinearIsometryEquiv.map_smul, PiLp.smul_apply,
        smul_eq_mul, abs_mul, abs_of_pos hr]
    have hS1m : MeasurableSet {y : Rd d | r * |y 0| ∈ B ∩ Ioi 0} :=
      ((measurable_const_mul r).comp hbm) (hB.inter measurableSet_Ioi)
    rw [hset1, ← Measure.map_apply Q.symm.continuous.measurable hS1m, normSphere_map_isometry]
    -- the two sets differ inside `{y₀ = 0}`
    have hS2m : MeasurableSet {y : Rd d | r * |y 0| ∈ B} :=
      ((measurable_const_mul r).comp hbm) hB
    have hz := normSphere_coord_null hd (M := {0}) Real.volume_singleton
    refine le_antisymm ?_ ?_
    · refine measure_mono fun y hy => ?_
      exact hy.1
    · calc normSphere d ((fun η : Rd d => |η 0|) ⁻¹' ((fun y => r * y) ⁻¹' B))
          ≤ normSphere d ({y : Rd d | r * |y 0| ∈ B ∩ Ioi 0} ∪
              {x : Rd d | x 0 ∈ ({0} : Set ℝ)}) := by
            refine measure_mono fun y hy => ?_
            by_cases h0 : y 0 = 0
            · exact Or.inr h0
            · exact Or.inl ⟨hy, mul_pos hr (abs_pos.2 h0)⟩
        _ ≤ _ := (measure_union_le _ _).trans (by rw [hz, add_zero])
  -- the display
  have hdisplay : ∀ B : Set ℝ, MeasurableSet B →
      foldedMarginal e ν B =
        ∫⁻ r, ((betaLaw d).map fun y => r * y) B ∂((ν.map fun x => ‖x‖).restrict (Ioi 0)) := by
    intro B hB
    have hf : Measurable fun x : Rd d => |⟪e, x⟫| := by fun_prop
    have hSm := hf (hB.inter (measurableSet_Ioi (a := (0 : ℝ))))
    rw [foldedMarginal, Measure.restrict_apply hB,
      Measure.map_apply hf (hB.inter measurableSet_Ioi)]
    rw [hpolar _ hSm]
    exact hcongr _ _ fun r hr => hsph r hr B hB
  refine ⟨hdisplay, Measure.AbsolutelyContinuous.mk fun N hN hN0 => ?_⟩
  rw [hdisplay N hN]
  have hzero : ∀ r : ℝ, 0 < r → ((betaLaw d).map fun y => r * y) N = 0 := by
    intro r hr
    rw [Measure.map_apply (measurable_const_mul r) hN]
    refine betaLaw_absolutelyContinuous hd ?_
    rw [Real.volume_preimage_mul_left hr.ne', hN0, mul_zero]
  rw [hcongr _ (fun _ => 0) hzero, lintegral_zero]

/-- **`prop:what-does-not-lift`, "hence".** For `d ≥ 2`, a line exponent whose folded Lévy measure
has an atom is not the exponent of the marginal along `e` of any rotation-invariant infinitely
divisible law on `ℝ^d`. -/
theorem what_does_not_lift_atom [NeZero d] (hd : 2 ≤ d) (e : Rd d) (he : ‖e‖ = 1)
    (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (hid : IsInfinitelyDivisible μ)
    (hrot : IsRotationInvariant μ) (P : ScaleSpace.SymLevyPair) (hatom : ∃ v : ℝ, P.ν {v} ≠ 0) :
    ¬ IsFoldedData (marginal e μ) P := by
  intro hF
  obtain ⟨T, hT⟩ := cited_A39_exists μ hid
  have hνrot := (triplet_rotation hid hrot hT).2
  have hac := (what_does_not_lift hd e he T.ν T.ν_zero T.ν_integrable hνrot).2
  -- the marginal as the image under the row `eᵀ`
  set U : Matrix (Fin 1) (Fin d) ℝ := fun _ j => e j with hU
  set L := Matrix.toEuclideanLin U with hL
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hLx : ∀ x : Rd d, L x = lineEmb ⟪e, x⟫ := by
    intro x
    ext j
    rw [Subsingleton.elim j 0, lineEmb_apply_zero, hL, Matrix.toLpLin_apply]
    simp [hU, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
  obtain ⟨hidU, -, T', hT', -, hν', -⟩ := cited_A42 μ hid T hT U
  haveI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map hLm.aemeasurable
  have hTP : HasTriplet (μ.map L) (symLevyTriplet P) := fun z => by
    have h1 : charFun (μ.map L) z = charFun (marginal e μ) (z 0) := by
      rw [charFun_apply, charFun_apply, marginal, integral_map hLm.aemeasurable (by fun_prop),
        integral_map (continuous_inner_left e).aemeasurable (by fun_prop)]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only
      rw [hLx, real_inner_comm, inner_lineEmb]
      simp [mul_comm]
    rw [h1, hF, lkExponent_symLevyTriplet, Complex.ofReal_exp, Complex.ofReal_neg]
  obtain ⟨-, hνeq, -⟩ := cited_A39_unique (μ.map L) hidU _ _ hTP hT'
  obtain ⟨v, hv⟩ := hatom
  have hvpos : 0 < v := by
    by_contra h
    push Not at h
    exact hv (measure_mono_null (fun x hx => by rw [mem_singleton_iff.1 hx]; exact h)
      P.ν_folded)
  have h1 := symLift_apply_pos P.ν_folded (measurableSet_singleton v)
  set S : Set (Rd 1) := (fun y : Rd 1 => y 0) ⁻¹' ({v} ∩ Ioi 0) with hS
  have hSm : MeasurableSet S :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable
      ((measurableSet_singleton v).inter measurableSet_Ioi)
  have h2 : symLift P.ν S = 0 := by
    have hfm : Measurable fun x : Rd d => |⟪e, x⟫| := by fun_prop
    have hfold0 : foldedMarginal e T.ν {v} = 0 := hac Real.volume_singleton
    rw [foldedMarginal, Measure.restrict_apply (measurableSet_singleton v)] at hfold0
    have hle := Measure.le_map_apply (μ := T.ν) hfm.aemeasurable ({v} ∩ Ioi 0)
    rw [hfold0] at hle
    have h3 : (symLevyTriplet P).ν = symLift P.ν := rfl
    rw [← h3, hνeq, hν']
    refine nonpos_iff_eq_zero.1 ((Measure.restrict_le_self S).trans ?_)
    rw [Measure.map_apply hLm hSm]
    refine (measure_mono fun x hx => ?_).trans hle
    simp only [hS, mem_preimage, hLx, lineEmb_apply_zero, mem_inter_iff, mem_singleton_iff,
      mem_Ioi] at hx ⊢
    rw [hx.1, abs_of_pos hvpos]
    exact ⟨rfl, hvpos⟩
  rw [h2] at h1
  exact hv ((mul_eq_zero.1 h1.symm).resolve_left (by norm_num))

end Pyramids
