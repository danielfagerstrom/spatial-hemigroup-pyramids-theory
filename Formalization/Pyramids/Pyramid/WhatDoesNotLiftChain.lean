/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.WhatDoesNotLift
import Pyramids.Pyramid.StratumTwoExample
import Pyramids.Cited.A43

/-!
# `prop:what-does-not-lift-chain`: the classes of one dilation, dimension by dimension

Blueprint: `blueprint/src/parts/03-pyramid.tex`, `prop:what-does-not-lift-chain`, chapter 3. Wave
2g: the three declarations moved here from `PyramidsSkeleton.Ch03Pyramid`.

## The route

* **The first inclusion.** A law of `𝒜_n` is self-decomposable (the shared core's measure form,
  Sato's form by `isSelfDecomposable_iff_sato`), hence semi-selfdecomposable with span `q`
  (`cited_A43_span`). `F ≥ 0` on `[0,∞)` because `F` is the exponent of a profile there.
* **The second inclusion.** `P : ℝ^{n+1} → ℝ^n` drops the coordinate `0`; its transpose
  `ω ↦ (0, ω)` is an isometry, so `P_*μ'` has the transform `e^{-F(|ω|)}`, and `P_*ϱ` is a residual.
  `P_*ϱ` is infinitely divisible because `P_*` carries a convolution root of `ϱ` to one of `P_*ϱ`
  (`isInfinitelyDivisible_map_lin`). No cited fact.
* **Strictness.** The witness is not the family of `prop:stratum-two-example` but its kernel at
  `t = q` alone, built directly: the data `E₁ = (0, ∑_{i ≤ 1} σ_{q^i})`, the train with weights
  `w_i = 1` for `i ≤ 0`, `0` for `i > 0` at phase `1`, and the law with these data (A39(iii)).
  The train at phase `0` is `D_{q⁻¹}` of the train at phase `1` and lies below it, so the
  difference `σ_q` gives data `Q` with `Ψ_{E₁}(ω) = Ψ_{E₁}(q⁻¹ω) + Ψ_Q(ω)`, and the law of `Q`
  is an infinitely divisible residual at span `q`. The exponent is `O(n)`-invariant, so it is
  `F(|ω|)` with `F(r) := Ψ_{E₁}(r e₀)`.
  Were `F ∈ 𝒜^{(q)}_{n+1}`, with the law `μ'`: `μ'` is infinitely divisible (A43, the semi
  clause), rotation invariant (its transform is radial), so its Lévy measure `ν'` is rotation
  invariant (`triplet_rotation`, A42 with A39(ii)); A42 at `P` and A39(ii) give
  `ν_{E₁} = [P_*ν']` off `0`. The polar decomposition of `ν'` (`rotationInvariant_polar`) puts no
  mass on `{x : |Px| = q}`: on the unit sphere `|Pη|² = 1 - η₀²`, so the set is, on each sphere,
  the set where `η₀` takes one of two values, and `σ{η₀ ∈ M} = 0` for a null set `M`
  (`normSphere_coord_null`, `n + 1 ≥ 2`). But `ν_{E₁}` gives the sphere `{|y| = q}` the mass `1`.
  The printed proof's density of a projected sphere is not needed: one sphere suffices.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (convPow)
open scoped ENNReal RealInnerProductSpace Topology Matrix MatrixOrder

/-! ## Linear images of infinitely divisible laws -/

theorem convPow_map_clm {m n : ℕ} (L : Rd m →L[ℝ] Rd n) (ν : Measure (Rd m))
    [IsFiniteMeasure ν] : ∀ k : ℕ, convPow (ν.map L) k = (convPow ν k).map L
  | 0 => by simp [convPow, Measure.map_dirac' L.continuous.measurable]
  | k + 1 => by
    haveI := ScaleSpace.isFiniteMeasure_convPow_Rd ν k
    rw [convPow, convPow, convPow_map_clm L ν k, Measure.map_conv_continuousLinearMap]

/-- **The linear image of an infinitely divisible law is infinitely divisible**: the image of a
`k`-th convolution root is a `k`-th convolution root of the image. -/
theorem isInfinitelyDivisible_map_lin {m n : ℕ} (L : Rd m →ₗ[ℝ] Rd n) {μ : Measure (Rd m)}
    (h : IsInfinitelyDivisible μ) : IsInfinitelyDivisible (μ.map L) := by
  intro k hk
  obtain ⟨ν, hν, hνk⟩ := h k hk
  haveI := hν
  have hL : (⇑(LinearMap.toContinuousLinearMap L) : Rd m → Rd n) = ⇑L := rfl
  refine ⟨ν.map L, Measure.isProbabilityMeasure_map
    (LinearMap.continuous_of_finiteDimensional L).measurable.aemeasurable, ?_⟩
  have := convPow_map_clm (LinearMap.toContinuousLinearMap L) ν k
  rw [hL] at this
  rw [this, hνk]

/-! ## Dropping the coordinate `0` -/

/-- **The matrix of `P : ℝ^{n+1} → ℝ^n`**, `(Px)_i = x_{i+1}`. -/
def dropMat (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℝ := fun i j => if j = i.succ then 1 else 0

variable {n : ℕ}

theorem dropLin_apply (x : Rd (n + 1)) (i : Fin n) :
    Matrix.toEuclideanLin (dropMat n) x i = x i.succ := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, dropMat]

theorem padLin_apply_zero (ω : Rd n) : Matrix.toEuclideanLin (dropMat n)ᵀ ω 0 = 0 := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, dropMat,
    Matrix.transpose_apply, (Fin.succ_ne_zero _).symm]

theorem padLin_apply_succ (ω : Rd n) (i : Fin n) :
    Matrix.toEuclideanLin (dropMat n)ᵀ ω i.succ = ω i := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, dropMat,
    Matrix.transpose_apply]

/-- `⟨Px, ω⟩ = ⟨x, Pᵀω⟩`. -/
theorem inner_dropLin (x : Rd (n + 1)) (ω : Rd n) :
    ⟪Matrix.toEuclideanLin (dropMat n) x, ω⟫ = ⟪x, Matrix.toEuclideanLin (dropMat n)ᵀ ω⟫ := by
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, dropLin_apply, padLin_apply_zero,
    padLin_apply_succ, inner_zero_right, zero_add]

/-- `|Pᵀω| = |ω|`. -/
theorem norm_padLin (ω : Rd n) : ‖Matrix.toEuclideanLin (dropMat n)ᵀ ω‖ = ‖ω‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  simp only [padLin_apply_zero, padLin_apply_succ, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add]

/-- `|x|² = x₀² + |Px|²`. -/
theorem norm_sq_dropLin (x : Rd (n + 1)) :
    ‖x‖ ^ 2 = x 0 ^ 2 + ‖Matrix.toEuclideanLin (dropMat n) x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp only [dropLin_apply, Real.norm_eq_abs, sq_abs]

/-- **The transform of `P_*μ`** is `μ̂(Pᵀ ·)`. -/
theorem charFun_map_dropLin (μ : Measure (Rd (n + 1))) (ω : Rd n) :
    charFun (μ.map (Matrix.toEuclideanLin (dropMat n))) ω =
      charFun μ (Matrix.toEuclideanLin (dropMat n)ᵀ ω) := by
  have hc : Continuous (Matrix.toEuclideanLin (dropMat n)) :=
    LinearMap.continuous_of_finiteDimensional _
  rw [charFun_apply, charFun_apply, integral_map hc.aemeasurable (by fun_prop)]
  simp_rw [inner_dropLin]

/-- **On a sphere of `ℝ^{n+1}`, `n ≥ 1`, the set `{|Px| = c}` is null**: on the unit sphere
`|Pη|² = 1 - η₀²`, so `r|Pη| = c` fixes `η₀` up to sign. -/
theorem sphereLaw_dropLin_null (hn : 1 ≤ n) (r c : ℝ) (hr : 0 < r) :
    sphereLaw (n + 1) r {x | ‖Matrix.toEuclideanLin (dropMat n) x‖ = c} = 0 := by
  set L := Matrix.toEuclideanLin (dropMat n) with hL
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional _
  have hS : MeasurableSet {x : Rd (n + 1) | ‖L x‖ = c} :=
    measurableSet_eq_fun (continuous_norm.comp hLc).measurable measurable_const
  rw [sphereLaw, Measure.map_apply (measurable_const_smul r) hS]
  set a : ℝ := 1 - (c / r) ^ 2 with ha
  set M : Set ℝ := {Real.sqrt a, -Real.sqrt a} with hM
  have hM0 : volume M = 0 := (Set.toFinite M).measure_zero volume
  have hnull : normSphere (n + 1) {u : Rd (n + 1) | ‖u‖ ≠ 1} = 0 := by
    have := ae_normSphere_norm (d := n + 1)
    rwa [ae_iff] at this
  refine measure_mono_null (t := {u | ‖u‖ ≠ 1} ∪ {u : Rd (n + 1) | u 0 ∈ M}) (fun u hu => ?_)
    (measure_union_null hnull (normSphere_coord_null (by omega) hM0))
  by_cases hu1 : ‖u‖ = 1
  · right
    have hu : ‖L (r • u)‖ = c := hu
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hu
    have hsq := norm_sq_dropLin u
    rw [hu1] at hsq
    have hLu : ‖L u‖ = c / r := by rw [← hu]; field_simp
    have h2 : u 0 ^ 2 = a := by rw [ha, ← hLu]; linarith
    have habs : |u 0| = Real.sqrt a := by rw [← h2, Real.sqrt_sq_eq_abs]
    rcases abs_eq (Real.sqrt_nonneg a) |>.1 habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact Or.inl hu1

/-- **A rotation-invariant Lévy measure on `ℝ^{n+1}`, `n ≥ 1`, puts no mass on `{|Px| = c}`**,
by the polar decomposition. -/
theorem levy_dropLin_null (hn : 1 ≤ n) (ν : Measure (Rd (n + 1))) (hν0 : ν {0} = 0)
    (hνint : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂ν ≠ ⊤) (hrot : IsRotationInvariant ν)
    (c : ℝ) : ν {x | ‖Matrix.toEuclideanLin (dropMat n) x‖ = c} = 0 := by
  have hLc : Continuous (Matrix.toEuclideanLin (dropMat n)) :=
    LinearMap.continuous_of_finiteDimensional _
  have hS : MeasurableSet {x : Rd (n + 1) | ‖Matrix.toEuclideanLin (dropMat n) x‖ = c} :=
    measurableSet_eq_fun (continuous_norm.comp hLc).measurable measurable_const
  rw [rotationInvariant_polar (by omega) ν hν0 hνint hrot hS]
  rw [setLIntegral_congr_fun (g := fun _ => (0 : ℝ≥0∞)) measurableSet_Ioi
    (fun r hr => sphereLaw_dropLin_null hn r c hr), lintegral_zero]

/-! ## The witness -/

/-- The weights of the witness: `1` for `i ≤ 0`, `0` for `i > 0`. -/
noncomputable def chainWeight (i : ℤ) : ℝ := if i ≤ 0 then 1 else 0

theorem chainWeight_nonneg (i : ℤ) : 0 ≤ chainWeight i := by
  unfold chainWeight; split_ifs <;> norm_num

theorem chainWeight_antitone : Antitone chainWeight := by
  intro i j hij
  unfold chainWeight
  split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | norm_num

theorem chainWeight_neg {q : ℝ} (hq : 1 < q) :
    Summable fun i : {i : ℤ // i < 0} => chainWeight i * q ^ (2 * (i : ℤ)) := by
  have hq0 : 0 < q := by linarith
  have hr : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by norm_num))
  have hgeo : Summable fun m : ℕ => ((q ^ 2)⁻¹) ^ m :=
    summable_geometric_of_lt_one (by positivity) hr
  have hinj : Function.Injective fun i : {i : ℤ // i < 0} => (i : ℤ).natAbs := by
    intro i j hij
    have h1 : (i : ℤ) = -((i : ℤ).natAbs : ℤ) := by have := i.2; omega
    have h2 : (j : ℤ) = -((j : ℤ).natAbs : ℤ) := by have := j.2; omega
    exact Subtype.ext (by rw [h1, h2]; simp only at hij; rw [hij])
  refine (hgeo.comp_injective hinj).congr fun i => ?_
  have hi : (i : ℤ) < 0 := i.2
  have h1 : (i : ℤ) = -((i : ℤ).natAbs : ℤ) := by omega
  simp only [Function.comp, chainWeight, if_pos hi.le, one_mul]
  conv_rhs => rw [h1]
  rw [inv_pow, ← pow_mul, mul_neg, zpow_neg, zpow_mul, zpow_natCast, zpow_ofNat]
  ring

theorem chainWeight_pos : Summable fun i : {i : ℤ // 0 ≤ i} => chainWeight i := by
  refine summable_of_ne_finset_zero (s := {⟨0, le_rfl⟩}) fun i hi => ?_
  have hi0 : (i : ℤ) ≠ 0 := fun h => hi (Finset.mem_singleton.2 (Subtype.ext h))
  have : ¬ (i : ℤ) ≤ 0 := by have := i.2; omega
  simp [chainWeight, this]

/-- An isometry carrying `|ω| e₀` to `ω`. -/
theorem exists_isometry_norm_smul [NeZero n] (ω : Rd n) :
    ∃ R : Rd n ≃ₗᵢ[ℝ] Rd n, R (‖ω‖ • ebasis (0 : Fin n)) = ω := by
  by_cases hω : ω = 0
  · exact ⟨LinearIsometryEquiv.refl ℝ _, by simp [hω]⟩
  set e0 : Rd n := ebasis (0 : Fin n) with he0
  have he0n : ‖e0‖ = 1 := by simp [he0, ebasis]
  have hωpos : 0 < ‖ω‖ := norm_pos_iff.2 hω
  set u : Rd n := ‖ω‖⁻¹ • ω with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hωpos.ne']
  refine ⟨Submodule.reflection (ℝ ∙ (e0 - u))ᗮ, ?_⟩
  rw [LinearIsometryEquiv.map_smul, Submodule.reflection_sub (he0n.trans hun.symm), hu,
    smul_smul, mul_inv_cancel₀ hωpos.ne', one_smul]

/-- **The witness.** For `n ≥ 1` there are symmetric data `E` on `ℝ^n` with `A = 0` and a Lévy
measure giving the sphere `{|y| = q}` the mass `1`, a profile `F` with `Ψ_E(ω) = F(|ω|)`, `F ≥ 0`,
and `F ∈ 𝒜^{(q)}_n`. -/
theorem chain_witness (hn : 1 ≤ n) {q : ℝ} (hq : 1 < q) :
    ∃ (E : SymLevyData n) (F : ℝ → ℝ), E.ν {y : Rd n | ‖y‖ = 1 * q ^ (1 : ℤ)} = 1 ∧
      (∀ ω : Rd n, E.exponent ω = F ‖ω‖) ∧ classAq q n F := by
  haveI : NeZero n := ⟨by omega⟩
  have hq0 : 0 < q := by linarith
  have hθ0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hθ1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨E0, hE0A, hE0ν⟩ := exists_trainData (d := n) hq one_pos chainWeight_nonneg
    chainWeight_antitone (chainWeight_neg hq) chainWeight_pos hn hθ0
  obtain ⟨E1, hE1A, hE1ν⟩ := exists_trainData (d := n) hq one_pos chainWeight_nonneg
    chainWeight_antitone (chainWeight_neg hq) chainWeight_pos hn hθ1
  -- the mass of the sphere of radius `q`
  have hmass : E1.ν {y : Rd n | ‖y‖ = 1 * q ^ (1 : ℤ)} = 1 := by
    rw [hE1ν, sphereTrain_sphere hn hq one_pos]
    simp [dgWeight, chainWeight]
  -- the difference of the two trains
  have hle : E0.Le E1 := ⟨le_of_eq (by rw [hE0A, hE1A]), by
    rw [hE0ν, hE1ν]; exact sphereTrain_mono chainWeight_antitone zero_le_one⟩
  obtain ⟨Q, -, -, hQ⟩ := SymLevyData.exists_sub hle
  -- the train at phase `1` is `D_q` of the train at phase `0`
  have hdil : ∀ ω : Rd n, E1.exponent ω = E0.exponent (q • ω) := by
    intro ω
    rw [← SymLevyData.dilate_exponent E0 hq0.ne']
    simp only [SymLevyData.exponent, SymLevyData.dilate, hE0A, hE1A, smul_zero, hE1ν, hE0ν,
      sphereTrain_one hq]
  have hres : ∀ ω : Rd n, E1.exponent ω = E1.exponent (q⁻¹ • ω) + Q.exponent ω := by
    intro ω
    rw [hQ ω, hdil (q⁻¹ • ω), smul_smul, mul_inv_cancel₀ hq0.ne', one_smul]
  -- the radial profile
  set F : ℝ → ℝ := fun r => E1.exponent (r • ebasis (0 : Fin n)) with hF
  have hrad : ∀ ω : Rd n, E1.exponent ω = F ‖ω‖ := by
    intro ω
    obtain ⟨R, hR⟩ := exists_isometry_norm_smul ω
    have h := trainData_exponent_orth hE1A hE1ν (isoMat_mem_orthSet R) ω
    rw [lin_isoMat_transpose] at h
    have h2 : (R.symm : Rd n →L[ℝ] Rd n) ω = ‖ω‖ • ebasis (0 : Fin n) := by
      conv_lhs => rw [← hR]
      simp
    rw [h2] at h
    exact h.symm
  have hnn : ∀ ω : Rd n, 0 ≤ E1.exponent ω := by
    intro ω
    simp only [SymLevyData.exponent, pairExponent, hE1A, quad_zero, zero_add]
    exact integral_nonneg fun x => sub_nonneg.2 (Real.cos_le_one _)
  -- the laws
  obtain ⟨μ1, hprob1, -, hT1⟩ := cited_A39_converse E1.triplet
  obtain ⟨ρ, hprobρ, hidρ, hTρ⟩ := cited_A39_converse Q.triplet
  have hμ1 : IsSymData μ1 E1 := fun ω => by
    rw [hT1 ω, SymLevyData.lkExponent_triplet, Complex.ofReal_exp, Complex.ofReal_neg]
  have hρ : IsSymData ρ Q := fun ω => by
    rw [hTρ ω, SymLevyData.lkExponent_triplet, Complex.ofReal_exp, Complex.ofReal_neg]
  refine ⟨E1, F, hmass, hrad, fun r hr => ?_, μ1, hprob1, ⟨hq, ρ, ⟨hprobρ, fun z => ?_⟩, hidρ⟩,
    fun ω => by rw [hμ1 ω, hrad ω]⟩
  · have h := hnn (r • ebasis (0 : Fin n))
    exact h
  · rw [hμ1 z, hμ1 (q⁻¹ • z), hρ z, ← Complex.ofReal_mul, ← Real.exp_add, hres z]
    congr 2
    ring

/-! ## `prop:what-does-not-lift-chain` -/

/-- **`prop:what-does-not-lift-chain`, the first inclusion.** The restrictions to `[0,∞)` of the
elements of `𝒜_n` lie in `𝒜^{(q)}_n`. -/
theorem what_does_not_lift_chain_1 {q : ℝ} (hq : 1 < q) (F : ℝ → ℝ)
    (hF : classA n F) : classAq q n F := by
  obtain ⟨⟨P, hP⟩, μ, hprob, hsd, hcf⟩ := hF
  haveI := hprob
  have hsato : IsSelfDecomposableSato μ := (isSelfDecomposable_iff_sato μ).1 hsd
  exact ⟨fun r hr => by rw [hP r hr]; exact ENNReal.toReal_nonneg, μ, hprob,
    cited_A43_span μ hsato hq, hcf⟩

/-- **`prop:what-does-not-lift-chain`, the second inclusion**, `𝒜^{(q)}_{n+1} ⊆ 𝒜^{(q)}_n`. -/
theorem what_does_not_lift_chain_2 {q : ℝ} (F : ℝ → ℝ)
    (hF : classAq q (n + 1) F) : classAq q n F := by
  obtain ⟨hF0, μ, hprob, ⟨hq, ρ, ⟨hprobρ, hres⟩, hidρ⟩, hcf⟩ := hF
  haveI := hprob
  haveI := hprobρ
  set L := Matrix.toEuclideanLin (dropMat n) with hL
  have hLm : Measurable L := (LinearMap.continuous_of_finiteDimensional L).measurable
  refine ⟨hF0, μ.map L, Measure.isProbabilityMeasure_map hLm.aemeasurable,
    ⟨hq, ρ.map L, ⟨Measure.isProbabilityMeasure_map hLm.aemeasurable, fun z => ?_⟩,
      isInfinitelyDivisible_map_lin L hidρ⟩, fun ω => ?_⟩
  · rw [charFun_map_dropLin, charFun_map_dropLin, charFun_map_dropLin, map_smul]
    exact hres _
  · rw [charFun_map_dropLin, hcf, norm_padLin]

/-- **`prop:what-does-not-lift-chain`, strictness**: some element of `𝒜^{(q)}_n` is not in
`𝒜^{(q)}_{n+1}`. -/
theorem what_does_not_lift_chain_strict {q : ℝ} (hq : 1 < q) (hn : 1 ≤ n) :
    ∃ F : ℝ → ℝ, classAq q n F ∧ ¬ classAq q (n + 1) F := by
  obtain ⟨E, F, hmass, hrad, hFq⟩ := chain_witness hn hq
  refine ⟨F, hFq, ?_⟩
  rintro ⟨-, μ', hprob', hsemi', hcf'⟩
  haveI := hprob'
  have hid' : IsInfinitelyDivisible μ' := cited_A43_semi_infinitelyDivisible μ' ⟨q, hsemi'⟩
  -- `μ'` is rotation invariant: its transform is radial
  have hrot' : IsRotationInvariant μ' := by
    intro P hP
    haveI : IsProbabilityMeasure (push P μ') :=
      Measure.isProbabilityMeasure_map (lin P).continuous.aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [push, charFun_map_lin, hcf', hcf', norm_lin_of_orth (transpose_mem_orthSet hP)]
  obtain ⟨T', hT'⟩ := cited_A39_exists μ' hid'
  have hνrot := (triplet_rotation hid' hrot' hT').2
  -- the image under `P`
  set L := Matrix.toEuclideanLin (dropMat n) with hL
  have hLm : Measurable L := (LinearMap.continuous_of_finiteDimensional L).measurable
  obtain ⟨hidU, -, T'', hT'', -, hν'', -⟩ := cited_A42 μ' hid' T' hT' (dropMat n)
  haveI : IsProbabilityMeasure (μ'.map L) := Measure.isProbabilityMeasure_map hLm.aemeasurable
  have hsym : IsSymData (μ'.map L) E := fun ω => by
    rw [charFun_map_dropLin, hcf', norm_padLin, hrad ω]
  obtain ⟨-, hνeq, -⟩ := cited_A39_unique (μ'.map L) hidU _ _ (SymLevyData.hasTriplet hsym) hT''
  -- the sphere of radius `q`
  set S : Set (Rd n) := {y : Rd n | ‖y‖ = 1 * q ^ (1 : ℤ)} with hS
  have hSm : MeasurableSet S := measurableSet_eq_fun continuous_norm.measurable measurable_const
  have h0 : T'.ν (L ⁻¹' S) = 0 :=
    levy_dropLin_null hn T'.ν T'.ν_zero T'.ν_integrable hνrot _
  have h1 : E.ν S ≤ 0 := by
    have hE : E.ν = T''.ν := hνeq
    rw [hE, hν'']
    refine (Measure.restrict_le_self S).trans ?_
    rw [Measure.map_apply hLm hSm, h0]
  rw [hmass] at h1
  exact one_ne_zero (nonpos_iff_eq_zero.1 h1)

end Pyramids
