/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.LadderCoupling
import Pyramids.Pyramid.LatticeInfinitelyDivisible
import Pyramids.Pyramid.NoLatticeKernel
import Pyramids.Cited.A45
import Pyramids.Cited.A34

/-!
# `prop:ladder-knot-kernel`(4): stratum 3

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:ladder-knot-kernel`. Wave 3a:
`ladder_knot_kernel_4a`, `ladder_knot_kernel_4b_equation` and `ladder_knot_kernel_4b_family` moved
here from `PyramidsSkeleton.Ch03Pyramid`, unchanged in name; `ladder_knot_kernel_4b_classA` is in
`LadderClassA`. Unused hypotheses were dropped (2026-11-14, a strengthening): from `_4b_equation`
`1 ≤ d`, `ϱ ≠ δ₀`, the rotation invariance of `ϱ`, `k ≥ 0`, the measurability of `k`, `|e| = 1` and
that `ϱ` is a probability measure (the equation holds along any vector, with the exponent of the
data); from `_4b_family` `a ≥ 0`, `k ≥ 0`, the measurability of `k`, the Lévy integrability, the
moment, and the continuity of `F` and `F(0) = 0` (which `F ∈ 𝒜_d` gives).

## The route

* **(4)(a).** A kernel `μ_t` of a fully covariant family is self-decomposable (the residual for the
  ratio `b` is the step from `S_b^{-1}t` to `t`), so by A45 its Lévy measure has the polar form,
  which gives every countable set the mass `0`. The step `ϱ = μ_{s,t}`, `s < t`, has
  `ν_ϱ ≤ ν_t`; by `lem:lattice-infinitely-divisible` it has `A_ϱ = 0` and `ν_ϱ` carried by the
  countable set `Γ`. So `ν_ϱ = 0`, and `ϱ = δ₀`.
* **(4)(c)** (2026-11-16). The same polar form gives every sphere about `0` the mass `0`, a ray
  meeting it in at most two points; the step's Lévy measure, identified by the uniqueness of the
  data (A39(ii)), is at most `ν_t`, so it charges no sphere.
* **(4)(b), the equation.** With the data `D_ϱ = (a/2 · I, ν_ϱ)` of `ϱ` and the knot data `D*`,
  `Ψ*(qω) = Ψ*(ω) + ψ_ϱ(ω)` (`ladderStarData_exponent_smul`: the dilate of `D*` is `D_ϱ + D*`, by
  `D_q ν* = ν_ϱ + ν*`). So `G(r) := Ψ*(re)` is a continuous solution with `G(0) = 0`, and every such
  solution is the series, by telescoping (`hasSum_step_Ici`). No Tonelli argument and no family is
  needed.
* **(4)(b), the family.** A34 with `χ = id` gives a fully covariant isotropic family with the
  exponents `F(t|·|)`; any laws with these exponents are that family on `0 ≤ s ≤ t`. Its octave
  steps have the exponents `F(q^{n+1}|·|) - F(qⁿ|·|) = ψ_ϱ(qⁿ|·|)`, the exponent of `D_{qⁿ}ϱ`, `ϱ`
  being rotation invariant.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace Matrix

variable {d : ℕ}

/-! ## (4)(a) -/

/-- **A kernel of a fully covariant family is self-decomposable**: for `b > 1` the residual is the
step `μ_{u,t}`, `S_b u = t`. -/
theorem kernel_selfDecomposable (hd : 1 ≤ d) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : IsSymmetricFamily μ) (hfull : IsFullyCovariantLaws μ) {t : ℝ} (ht : 0 < t) :
    IsSelfDecomposableSato (μ 0 t) := by
  intro b hb
  obtain ⟨S, hS⟩ := hfull b (by linarith)
  obtain ⟨-, hlt⟩ := family_dilations_1 hd μ hμ S S hS hS
  obtain ⟨u, hu0, hSu⟩ := hS.1.surjOn (show t ∈ Ici (0 : ℝ) from mem_Ici.2 ht.le)
  have hu0' : (0 : ℝ) ≤ u := hu0
  have hS0 : S 0 = 0 := incBij_zero hS.1
  have hupos : 0 < u := by
    rcases hu0'.eq_or_lt with h0 | h0
    · rw [← h0, hS0] at hSu
      exact absurd hSu ht.ne
    · exact h0
  have hut : u < t := by
    have := hlt hb u hupos
    rwa [hSu] at this
  refine ⟨μ u t, hμ.1.isProbability u t hu0' hut.le, fun z => ?_⟩
  have hcasc := hμ.1.cascade 0 u t le_rfl hu0' hut.le
  have hmap : (μ 0 u).map (fun x => b • x) = μ 0 t := by
    have := hS.2 0 u le_rfl hu0'
    rwa [hS0, hSu] at this
  have hbz : b • b⁻¹ • z = z := by
    rw [smul_smul, mul_inv_cancel₀ (by linarith), one_smul]
  haveI := hμ.1.isProbability u t hu0' hut.le
  haveI := hμ.1.isProbability 0 u le_rfl hu0'
  conv_lhs => rw [hcasc]
  rw [charFun_conv, ← hmap, charFun_map_smul, hbz, mul_comm]

/-- **`prop:ladder-knot-kernel`(4)(a).** A law `ϱ ≠ δ₀` carried by a full-rank lattice is no step
`μ_{s,t}` of a symmetric family that is `λ`-covariant for every `λ > 0`. -/
theorem ladder_knot_kernel_4a (hd : 1 ≤ d) (ρ : Measure (Rd d)) (hne : ρ ≠ Measure.dirac 0)
    (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (hcarr : ρ (Γ : Set (Rd d))ᶜ = 0) (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsSymmetricFamily μ)
    (hfull : IsFullyCovariantLaws μ) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t ≠ ρ := by
  intro s t hs hst heq
  have hlt : s < t := by
    refine lt_of_le_of_ne hst fun h => hne ?_
    rw [← heq, h]
    exact hμ.1.diag t (h ▸ hs)
  have ht : 0 < t := lt_of_le_of_lt hs hlt
  obtain ⟨D, hD⟩ := family_structure_exists hd μ hμ
  haveI := hμ.1.isProbability 0 t le_rfl ht.le
  -- the Lévy measure of `μ_t` gives countable sets the mass `0`
  have hid := (family_structure_id hd μ hμ 0 t le_rfl ht.le).1
  obtain ⟨lam, k, -, -, -, -, hpolar⟩ := (cited_A45 (μ 0 t) hid _
    (SymLevyData.hasTriplet (hD t ht.le))).1 (kernel_selfDecomposable hd hμ hfull ht)
  have hΓc : (Γ : Set (Rd d)).Countable := by
    haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
    exact Set.countable_coe_iff.1 this
  have hνt : (D t).ν Γ = 0 := by
    have h := hpolar Γ hΓc.measurableSet
    change (D t).ν Γ = _ at h
    rw [h]
    refine (lintegral_congr fun ξ => ?_).trans lintegral_zero
    have hξ0 : (ξ : Rd d) ≠ 0 := by
      intro h0
      have := mem_sphere_zero_iff_norm.1 ξ.2
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hcount : {r : ℝ | r • (ξ : Rd d) ∈ (Γ : Set (Rd d))}.Countable :=
      hΓc.preimage (smul_left_injective ℝ hξ0)
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) ?_, lintegral_zero]
    filter_upwards [ae_restrict_of_ae (hcount.ae_notMem volume)] with r hr
    simp [Set.indicator_of_notMem hr]
  -- the data of the step
  obtain ⟨-, -, -, Q, -, hQν, hQ⟩ := (family_structure_data hd μ hμ D hD).2 s t hs hst
  haveI := hμ.1.isProbability s t hs hst
  have hid' := (family_structure_id hd μ hμ s t hs hst).1
  rw [heq] at hQ hid'
  haveI : IsProbabilityMeasure ρ := heq ▸ hμ.1.isProbability s t hs hst
  obtain ⟨hA0, -, hcarrQ⟩ := lattice_infinitely_divisible ρ hid' Q.triplet
    (SymLevyData.hasTriplet hQ) Γ hcarr
  have hQA : Q.A = 0 := by
    have h2 : (2 : ℝ) • Q.A = 0 := hA0
    exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
  have hQΓ : Q.ν Γ = 0 := by
    refine le_antisymm ?_ bot_le
    rw [← hνt, ← hQν, Measure.add_apply]
    exact le_self_add
  have hQ0 : Q.ν = 0 := by
    rw [← Measure.measure_univ_eq_zero]
    have hsub : (Γ : Set (Rd d)) \ {0} ⊆ Γ := sdiff_subset
    refine measure_mono_null (fun x _ => ?_) (measure_union_null (measure_mono_null
      hsub hQΓ) hcarrQ)
    by_cases hx : x ∈ (Γ : Set (Rd d)) \ {0}
    · exact Or.inl hx
    · exact Or.inr hx
  refine hne (eq_dirac_of_charFun_one fun ω => ?_)
  rw [hQ ω]
  simp [SymLevyData.exponent, pairExponent, hQA, hQ0, quad_zero]

/-! ## (4)(c) -/

/-- **`prop:ladder-knot-kernel`(4)(c).** A law whose Lévy measure charges a sphere `{|x| = r}` is no
step `μ_{s,t}` of a symmetric family that is `λ`-covariant for every `λ > 0`. The argument of (4)(a)
with the sphere in place of the countable set: the Lévy measure of the kernel `μ_t` has the polar
form (A45), and a ray meets the sphere in at most two points, so `ν_t` gives the sphere the mass
`0`; the step's Lévy measure is at most `ν_t`. Neither `r > 0` nor `ϱ` a law is asked: `ν {0} = 0`, and
`ϱ = μ_{s,t}` is a law. -/
theorem ladder_knot_kernel_4c (hd : 1 ≤ d) (ρ : Measure (Rd d)) (Dρ : SymLevyData d)
    (hρ : IsSymData ρ Dρ) {r : ℝ} (hr : Dρ.ν (Metric.sphere (0 : Rd d) r) ≠ 0)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsSymmetricFamily μ) (hfull : IsFullyCovariantLaws μ) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t ≠ ρ := by
  intro s t hs hst heq
  haveI hprob : IsProbabilityMeasure ρ := heq ▸ hμ.1.isProbability s t hs hst
  rcases hst.eq_or_lt with h | hlt
  · -- the step `μ_{s,s} = δ₀` has the data `0`
    have hdir : ρ = Measure.dirac 0 := by
      rw [← heq, h]
      exact hμ.1.diag t (h ▸ hs)
    have hzero : IsSymData ρ (SymLevyData.zero : SymLevyData d) := fun ω => by
      rw [hdir, SymLevyData.zero_exponent, charFun_dirac, inner_zero_left]
      simp
    have hν := (isSymData_unique hρ hzero).2
    exact hr (by simp [hν, SymLevyData.zero])
  have ht : 0 < t := lt_of_le_of_lt hs hlt
  obtain ⟨D, hD⟩ := family_structure_exists hd μ hμ
  haveI := hμ.1.isProbability 0 t le_rfl ht.le
  -- the Lévy measure of `μ_t` gives every sphere about `0` the mass `0`
  have hid := (family_structure_id hd μ hμ 0 t le_rfl ht.le).1
  obtain ⟨lam, k, -, -, -, -, hpolar⟩ := (cited_A45 (μ 0 t) hid _
    (SymLevyData.hasTriplet (hD t ht.le))).1 (kernel_selfDecomposable hd hμ hfull ht)
  have hS : MeasurableSet (Metric.sphere (0 : Rd d) r) := Metric.isClosed_sphere.measurableSet
  have hνt : (D t).ν (Metric.sphere (0 : Rd d) r) = 0 := by
    have h := hpolar _ hS
    change (D t).ν _ = _ at h
    rw [h]
    refine (lintegral_congr fun ξ => ?_).trans lintegral_zero
    have hξ : ‖(ξ : Rd d)‖ = 1 := mem_sphere_zero_iff_norm.1 ξ.2
    have hcount : {r' : ℝ | r' • (ξ : Rd d) ∈ Metric.sphere (0 : Rd d) r}.Countable := by
      refine ((Set.countable_singleton r).union (Set.countable_singleton (-r))).mono ?_
      intro r' hr'
      have habs : |r'| = r := by
        have h1 : ‖r' • (ξ : Rd d)‖ = r := mem_sphere_zero_iff_norm.1 hr'
        rwa [norm_smul, hξ, mul_one, Real.norm_eq_abs] at h1
      rcases abs_choice r' with h1 | h1
      · exact Or.inl (show r' = r by linarith)
      · exact Or.inr (show r' = -r by linarith)
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) ?_, lintegral_zero]
    filter_upwards [ae_restrict_of_ae (hcount.ae_notMem volume)] with r' hr'
    simp [Set.indicator_of_notMem hr']
  -- the data of the step
  obtain ⟨-, -, -, Q, -, hQν, hQ⟩ := (family_structure_data hd μ hμ D hD).2 s t hs hst
  rw [heq] at hQ
  have hν : Q.ν = Dρ.ν := (isSymData_unique hQ hρ).2
  refine hr (le_antisymm ?_ bot_le)
  rw [← hν, ← hνt, ← hQν, Measure.add_apply]
  exact le_self_add

/-! ## The data of a rotation-invariant step -/

/-- The density of `k(|x|)(|S^{d-1}| |x|^d)^{-1} dx` at `Qx` is that at `x`. -/
theorem polarLevyMeasure_map_isometry (k : ℝ → ℝ) (Q : Rd d ≃ₗᵢ[ℝ] Rd d) :
    (polarLevyMeasure d k).map Q = polarLevyMeasure d k := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply Q.continuous.measurable hB, polarLevyMeasure,
    withDensity_apply _ (Q.continuous.measurable hB), withDensity_apply _ hB,
    ← lintegral_indicator (Q.continuous.measurable hB), ← lintegral_indicator hB]
  have h := (Q.measurePreserving).lintegral_comp_emb Q.toHomeomorph.measurableEmbedding
    (B.indicator fun x => ({0}ᶜ : Set (Rd d)).indicator
      (fun x => ENNReal.ofReal (k ‖x‖ / (sphereArea d * ‖x‖ ^ d))) x)
  rw [← h]
  refine lintegral_congr fun x => ?_
  by_cases hx : Q x ∈ B
  · rw [indicator_of_mem (show x ∈ Q ⁻¹' B from hx), indicator_of_mem hx]
    simp only [LinearIsometryEquiv.norm_map, mem_compl_iff, mem_singleton_iff,
      LinearIsometryEquiv.map_eq_zero_iff, indicator]
  · rw [indicator_of_notMem (show x ∉ Q ⁻¹' B from hx), indicator_of_notMem hx]

theorem polarLevyMeasure_zero (k : ℝ → ℝ) : polarLevyMeasure d k {0} = 0 := by
  rw [polarLevyMeasure, withDensity_apply _ (measurableSet_singleton 0), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac]
  simp

/-- **The data `(a/2 · I, ν_ϱ)`** of a step with the polar Lévy measure. -/
noncomputable def polarData {a : ℝ} (ha : 0 ≤ a) (k : ℝ → ℝ)
    (hlevy : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂polarLevyMeasure d k ≠ ⊤) : SymLevyData d where
  A := (a / 2) • (1 : Mat d)
  ν := polarLevyMeasure d k
  A_posSemidef := Matrix.PosSemidef.one.smul (by positivity)
  ν_zero := polarLevyMeasure_zero k
  ν_integrable := hlevy
  ν_symm := by
    have h := polarLevyMeasure_map_isometry (d := d) k (LinearIsometryEquiv.neg ℝ)
    rwa [coe_neg_isometry] at h

theorem isSymData_polar {ρ : Measure (Rd d)} {a : ℝ} (ha : 0 ≤ a) (k : ℝ → ℝ)
    (hlevy : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂polarLevyMeasure d k ≠ ⊤)
    (htrans : ∀ ω : Rd d, charFun ρ ω = ((Real.exp (-(a / 2 * ‖ω‖ ^ 2 +
      ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂polarLevyMeasure d k)) : ℝ) : ℂ)) :
    IsSymData ρ (polarData ha k hlevy) := fun ω => by
  rw [htrans ω]
  simp [SymLevyData.exponent, pairExponent, polarData, quad_smul, quad_one]

theorem radialExponent_eq {ρ : Measure (Rd d)} {D : SymLevyData d} (hD : IsSymData ρ D)
    (e : Rd d) (r : ℝ) : radialExponent ρ e r = D.exponent (r • e) := by
  rw [radialExponent, hD, Complex.ofReal_re, Real.log_exp, neg_neg]

/-! ## The knot data -/

theorem SymLevyData.exponent_zero (D : SymLevyData d) : D.exponent 0 = 0 := by
  simp [SymLevyData.exponent, pairExponent, quad]

/-- **The exponent of data is continuous**: it is `-log` of the transform of a law with these data
(A39(iii)). -/
theorem SymLevyData.continuous_exponent (D : SymLevyData d) : Continuous D.exponent := by
  obtain ⟨m, hprob, -, hT⟩ := cited_A39_converse D.triplet
  haveI := hprob
  have hm : IsSymData m D := fun ω => by
    rw [hT ω, SymLevyData.lkExponent_triplet, Complex.ofReal_exp, Complex.ofReal_neg]
  have h : D.exponent = fun ω => -Real.log (charFun m ω).re := by
    funext ω
    rw [hm ω, Complex.ofReal_re, Real.log_exp, neg_neg]
  rw [h]
  refine (Continuous.log (Complex.continuous_re.comp continuous_charFun) fun ω => ?_).neg
  simp only [Function.comp_apply, hm ω, Complex.ofReal_re]
  exact (Real.exp_pos _).ne'

/-- **`Ψ*(qω) = Ψ*(ω) + ψ_ϱ(ω)`**: the dilate of `D*` is `D_ϱ + D*`. -/
theorem ladderStarData_exponent_smul {q : ℝ} (hq : 1 < q) (D : SymLevyData d)
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂D.ν < ⊤) (ω : Rd d) :
    (ladderStarData hq D hmom).exponent (q • ω) =
      (ladderStarData hq D hmom).exponent ω + D.exponent ω := by
  have hq0 : 0 < q := by linarith
  rw [← SymLevyData.dilate_exponent _ hq0.ne', add_comm]
  refine SymLevyData.exponent_of_add ?_ ?_ ω
  · change D.A + (q ^ 2 - 1)⁻¹ • D.A = q ^ 2 • (q ^ 2 - 1)⁻¹ • D.A
    have hq21 : q ^ 2 - 1 ≠ 0 := by nlinarith
    rw [smul_smul, show q ^ 2 * (q ^ 2 - 1)⁻¹ = 1 + (q ^ 2 - 1)⁻¹ by field_simp; ring, add_smul,
      one_smul]
  · change D.ν + ladderNuStar q D.ν = (ladderNuStar q D.ν).map fun x => q • x
    rw [map_ladderNuStar hq0]

/-- **The telescoping series on `[0,∞)`.** If `G` is continuous on `[0,∞)` with `G(0) = 0`, and
`G(qr) - G(r) = ψ(r) ≥ 0` for `r ≥ 0`, then `G(r) = ∑_{m ≥ 1} ψ(q^{-m} r)` for `r ≥ 0`. -/
theorem hasSum_step_Ici {q : ℝ} (hq : 1 < q) {G ψ : ℝ → ℝ} (hc : ContinuousOn G (Ici 0))
    (h0 : G 0 = 0) (heq : ∀ r : ℝ, 0 ≤ r → G (q * r) - G r = ψ r)
    (hnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ ψ r) {r : ℝ} (hr : 0 ≤ r) :
    HasSum (fun m : ℕ => ψ (q ^ (-((m : ℤ) + 1)) * r)) (G r) := by
  have hq0 : 0 < q := by linarith
  set f : ℕ → ℝ := fun m => G (r / q ^ m) with hf
  have hx : ∀ m : ℕ, 0 ≤ r / q ^ m := fun m => div_nonneg hr (by positivity)
  have hterm : ∀ m : ℕ, ψ (q ^ (-((m : ℤ) + 1)) * r) = f m - f (m + 1) := by
    intro m
    have e1 : q ^ (-((m : ℤ) + 1)) * r = r / q ^ (m + 1) := by
      rw [zpow_neg_succ, inv_mul_eq_div]
    have e2 : q * (r / q ^ (m + 1)) = r / q ^ m := by
      rw [pow_succ]
      field_simp
    rw [e1, ← heq _ (hx (m + 1)), e2]
  simp_rw [hterm]
  have hnn' : ∀ m : ℕ, 0 ≤ f m - f (m + 1) := fun m => by
    rw [← hterm m]
    exact hnn _ (mul_nonneg (zpow_pos hq0 _).le hr)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn']
  simp_rw [Finset.sum_range_sub']
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => r / q ^ m) atTop (𝓝[Ici 0] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hq))
        (Eventually.of_forall hx)
    have h2 := ((hc 0 self_mem_Ici).tendsto).comp h1
    rwa [h0] at h2
  have h0' : f 0 = G r := by simp [hf]
  rw [← h0']
  simpa using (tendsto_const_nhds (x := f 0)).sub hlim

/-! ## `prop:ladder-knot-kernel`(4)(b), the equation -/

/-- **`prop:ladder-knot-kernel`(4)(b), the equation.** For a law `ϱ` with Gaussian part
`½ a |ω|²`, Lévy measure `k(|x|)(|S^{d-1}| |x|^d)^{-1} dx` and the logarithmic moment, and
`ψ_ϱ(r) = -log ϱ̂(re)`: the series `F = ∑_{m ≥ 1} ψ_ϱ(q^{-m} ·)` converges on `[0,∞)`, and `F` is
the unique continuous solution of `F(qr) - F(r) = ψ_ϱ(r)`, `r ≥ 0`, with `F(0) = 0`. -/
theorem ladder_knot_kernel_4b_equation {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d)) {a : ℝ}
    (ha : 0 ≤ a) (k : ℝ → ℝ)
    (hlevy : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂polarLevyMeasure d k ≠ ⊤)
    (htrans : ∀ ω : Rd d, charFun ρ ω = ((Real.exp (-(a / 2 * ‖ω‖ ^ 2 +
      ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂polarLevyMeasure d k)) : ℝ) : ℂ))
    (hmom : ∫⁻ x, ENNReal.ofReal (Real.posLog ‖x‖) ∂polarLevyMeasure d k < ⊤)
    (e : Rd d) :
    (∀ r : ℝ, 0 ≤ r → Summable fun m : ℕ => radialExponent ρ e (q ^ (-((m : ℤ) + 1)) * r)) ∧
      ContinuousOn (knotSeries q (radialExponent ρ e)) (Ici 0) ∧
      knotSeries q (radialExponent ρ e) 0 = 0 ∧
      (∀ r : ℝ, 0 ≤ r → knotSeries q (radialExponent ρ e) (q * r) -
        knotSeries q (radialExponent ρ e) r = radialExponent ρ e r) ∧
      ∀ G : ℝ → ℝ, ContinuousOn G (Ici 0) → G 0 = 0 →
        (∀ r : ℝ, 0 ≤ r → G (q * r) - G r = radialExponent ρ e r) →
          ∀ r : ℝ, 0 ≤ r → G r = knotSeries q (radialExponent ρ e) r := by
  set Dρ : SymLevyData d := polarData ha k hlevy with hDρ
  have hD : IsSymData ρ Dρ := isSymData_polar ha k hlevy htrans
  set Dst := ladderStarData hq Dρ hmom with hDst
  set G0 : ℝ → ℝ := fun r => Dst.exponent (r • e) with hG0
  have hGc : Continuous G0 := Dst.continuous_exponent.comp (continuous_id.smul continuous_const)
  have hG00 : G0 0 = 0 := by simp [hG0, SymLevyData.exponent_zero]
  have hGeq : ∀ r : ℝ, G0 (q * r) - G0 r = radialExponent ρ e r := by
    intro r
    simp only [hG0]
    rw [mul_smul, ladderStarData_exponent_smul hq Dρ hmom, radialExponent_eq hD]
    ring
  have hnn : ∀ r : ℝ, 0 ≤ radialExponent ρ e r := fun r => by
    rw [radialExponent_eq hD]
    exact Dρ.exponent_nonneg _
  have hsum : ∀ r : ℝ, 0 ≤ r →
      HasSum (fun m : ℕ => radialExponent ρ e (q ^ (-((m : ℤ) + 1)) * r)) (G0 r) :=
    fun r hr => hasSum_step_Ici hq hGc.continuousOn hG00 (fun r _ => hGeq r) (fun r _ => hnn r) hr
  have hser : ∀ r : ℝ, 0 ≤ r → knotSeries q (radialExponent ρ e) r = G0 r :=
    fun r hr => (hsum r hr).tsum_eq
  refine ⟨fun r hr => (hsum r hr).summable, hGc.continuousOn.congr fun r hr => hser r hr,
    by rw [hser 0 le_rfl, hG00], fun r hr => ?_, fun G hGc' hG0' hGeq' r hr => ?_⟩
  · rw [hser _ (mul_nonneg (by linarith) hr), hser r hr, hGeq]
  · rw [hser r hr]
    exact (hasSum_step_Ici hq hGc' hG0' hGeq' (fun r _ => hnn r) hr).unique (hsum r hr)

/-! ## `prop:ladder-knot-kernel`(4)(b), the family -/

/-- A rotation-invariant law has `ϱ̂(ξ) = ϱ̂(|ξ| e)` for a unit vector `e`. -/
theorem charFun_eq_norm_smul {ρ : Measure (Rd d)} (hrot : IsRotationInvariant ρ) {e : Rd d}
    (he : ‖e‖ = 1) (ξ : Rd d) : charFun ρ ξ = charFun ρ (‖ξ‖ • e) := by
  have hn : ‖‖ξ‖ • e‖ = ‖ξ‖ := by rw [norm_smul, he, mul_one, norm_norm]
  set R := Submodule.reflection (ℝ ∙ (‖ξ‖ • e - ξ) : Submodule ℝ (Rd d))ᗮ with hR
  have hRξ : R (‖ξ‖ • e) = ξ := Submodule.reflection_sub hn
  have h := charFun_orth_of_rotationInvariant hrot (isoMat_mem_orthSet R.symm) ξ
  rw [lin_isoMat_transpose, LinearIsometryEquiv.symm_symm] at h
  change charFun ρ (R ξ) = charFun ρ ξ at h
  have hRR : R ξ = ‖ξ‖ • e := by
    conv_lhs => rw [← hRξ]
    exact Submodule.reflection_reflection (ℝ ∙ (‖ξ‖ • e - ξ) : Submodule ℝ (Rd d))ᗮ (‖ξ‖ • e)
  rw [← h, hRR]

/-- **Transfer of an isotropic cascade family** along equality on `0 ≤ s ≤ t`. -/
theorem isotropicCascade_congr {μ μ' : ℝ → ℝ → Measure (Rd d)} {S : ℝ → ℝ → ℝ}
    (h : IsIsotropicCascadeFamily μ' S) (heq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t) :
    IsIsotropicCascadeFamily μ S := by
  have hS : ∀ lam : ℝ, 0 < lam → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      0 ≤ S lam s ∧ S lam s ≤ S lam t := fun lam hl s t hs hst =>
    ⟨(h.scale_bij lam hl).mapsTo (mem_Ici.2 hs),
      (h.scale_bij lam hl).strictMonoOn.monotoneOn (mem_Ici.2 hs) (mem_Ici.2 (hs.trans hst)) hst⟩
  refine ⟨fun s t hs hst => heq s t hs hst ▸ h.isProbability s t hs hst,
    fun t ht => (heq t t ht le_rfl).trans (h.diag t ht),
    fun r s t hr hrs hst => ?_, fun ξ => ?_, fun Q hQ s t hs hst => ?_, h.scale_bij,
    fun lam hl s t hs hst => ?_, fun s t hs hst => ?_⟩
  · rw [heq r t hr (hrs.trans hst), heq s t (hr.trans hrs) hst, heq r s hr hrs]
    exact h.cascade r s t hr hrs hst
  · refine (h.continuous ξ).congr fun p hp => ?_
    simp only [heq p.1 p.2 hp.1 hp.2]
  · rw [heq s t hs hst]
    exact h.rotation Q hQ s t hs hst
  · obtain ⟨h1, h2⟩ := hS lam hl s t hs hst
    rw [heq s t hs hst, heq _ _ h1 h2]
    exact h.scale lam hl s t hs hst
  · rw [heq s t hs hst.le]
    exact h.nondegenerate s t hs hst

/-- **`prop:ladder-knot-kernel`(4)(b), the family.** If `F ∈ 𝒜_d` solves the equation, laws with the
exponents `Ψ_t = F(t|·|)` exist, and any such laws form an isotropic family, `λ`-covariant for
every `λ > 0`, with the ladder `(D_{q^n} ϱ)_n` of `ϱ`. -/
theorem ladder_knot_kernel_4b_family (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ] (hne : ρ ≠ Measure.dirac 0) (hrot : IsRotationInvariant ρ) {a : ℝ}
    (k : ℝ → ℝ)
    (htrans : ∀ ω : Rd d, charFun ρ ω = ((Real.exp (-(a / 2 * ‖ω‖ ^ 2 +
      ∫ x, (1 - Real.cos ⟪ω, x⟫) ∂polarLevyMeasure d k)) : ℝ) : ℂ))
    (e : Rd d) (he : ‖e‖ = 1) (F : ℝ → ℝ)
    (hFeq : ∀ r : ℝ, 0 ≤ r → F (q * r) - F r = radialExponent ρ e r) (hA : classA d F) :
    (∃ μ : ℝ → ℝ → Measure (Rd d), IsExponentLaws (fun t ω => F (t * ‖ω‖)) μ) ∧
      ∀ μ : ℝ → ℝ → Measure (Rd d), IsExponentLaws (fun t ω => F (t * ‖ω‖)) μ →
        IsIsotropicFamily μ ∧ IsFullyCovariantLaws μ ∧ ∀ n : ℤ, ladder μ q n = dilLadder q ρ n := by
  have hq0 : 0 < q := by linarith
  -- `ϱ̂(re) = e^{-ψ_ϱ(r)}`
  have hρe : ∀ r : ℝ, charFun ρ (r • e) = ((Real.exp (-radialExponent ρ e r) : ℝ) : ℂ) := by
    intro r
    rw [radialExponent, htrans, Complex.ofReal_re, Real.log_exp, neg_neg]
  -- `F ≢ 0`
  have hFne : ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hne (eq_dirac_of_charFun_one fun ξ => ?_)
    rw [charFun_eq_norm_smul hrot he ξ, hρe, ← hFeq _ (norm_nonneg ξ),
      hcon _ (mul_nonneg hq0.le (norm_nonneg ξ)), hcon _ (norm_nonneg ξ)]
    simp
  have hid : IsGauge id := ⟨rfl, strictMonoOn_id, fun t ht => ⟨t, ht, rfl⟩⟩
  obtain ⟨μ0, hp0, ⟨S, hS⟩, hc0⟩ := cited_A34 hd id F hid hA hFne
  refine ⟨⟨μ0, fun s t hs hst => ⟨hp0 s t hs hst, fun ω => hc0 s t hs hst ω⟩⟩, fun μ hμ => ?_⟩
  have heq : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ0 s t := by
    intro s t hs hst
    haveI := (hμ s t hs hst).1
    haveI := hp0 s t hs hst
    exact Measure.ext_of_charFun (funext fun ω => by rw [(hμ s t hs hst).2, hc0 s t hs hst]; rfl)
  have hS' := isotropicCascade_congr hS heq
  have hiso : IsIsotropicFamily μ :=
    ⟨⟨⟨hS'.isProbability, hS'.diag, hS'.cascade, hS'.continuous⟩, hS'.nondegenerate⟩,
      fun s t hs hst Q hQ => hS'.rotation Q hQ s t hs hst⟩
  refine ⟨hiso, (isFullyCovariant_iff_cascade μ hiso).2 ⟨S, hS'⟩, fun n => ?_⟩
  -- the ladder
  have hqn : 0 < q ^ n := zpow_pos hq0 n
  have h1 : 0 ≤ q ^ n := hqn.le
  have h2 : q ^ n ≤ q ^ (n + 1) := by
    rw [zpow_add_one₀ hq0.ne']
    exact le_mul_of_one_le_right h1 hq.le
  haveI := (hμ _ _ h1 h2).1
  haveI : IsProbabilityMeasure (dilLadder q ρ n) :=
    Measure.isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
  change μ (q ^ n) (q ^ (n + 1)) = _
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [(hμ _ _ h1 h2).2, dilLadder, charFun_map_smul, charFun_eq_norm_smul hrot he,
    hρe, norm_smul, Real.norm_of_nonneg h1, ← hFeq _ (mul_nonneg h1 (norm_nonneg ξ)),
    zpow_add_one₀ hq0.ne']
  congr 4
  ring_nf

end Pyramids
