/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Price
import Pyramids.Pyramid.LadderKnot
import Pyramids.Pyramid.LadderCoupling
import Pyramids.Pyramid.LatticeInfinitelyDivisible
import Pyramids.Pyramid.LadderNotEvery
import Pyramids.Line.GridTransfer

/-!
# `prop:grid-pyramid-not-isotropic`: the set `Γ_q` and clause (1)

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:grid-pyramid-not-isotropic`. Wave 3g:
`grid_pyramid_not_isotropic_union` and `grid_pyramid_not_isotropic_1` moved here from
`PyramidsSkeleton.Ch05Price`, unchanged in name and conclusion. `_union` no longer takes
`2 ≤ q` and `0 < h`, which its proof does not read (2026-11-15, a strengthening).

## The route

* **The family.** Khintchine's theorem through `isLawHemigroup_infinitelyDivisible` (A41) makes
  every law of the family infinitely divisible; the mask is `μ_{1,q}`, and `d ≥ 1` because on
  `ℝ⁰` every law is `δ₀`.
* **The mask.** `lem:lattice-infinitely-divisible` gives `A = 0` and a finite Lévy measure on
  `Γ ∖ {0}`; symmetry gives data `(0, ν_w)` (`exists_symData`, A39), whose transform is that of the
  compound Poisson law (`charFun_cpLaw_symm`).
* **The knot kernel** (`carries_knot_data`, for any symmetric mask with data): the product formula
  is `tendsto_ladderProd`, with `μ̂_1 ≠ 0` from A40; the transform is real as a limit of real
  products, so `μ_1` is symmetric and has data `D_1`; `μ_q = D_q μ_1 = w ∗ μ_1` gives
  `q²A_1 = A_w + A_1` and `D_q ν_1 = ν_w + ν_1`, so `ν_1 = ν*` (`eq_ladderNuStar_of_map`). This is
  `prop:ladder-knot-kernel`(1) without the symmetry and (ND) of the whole family.
* **The knots** are dilates: `μ_{q^n} = D_{q^n} μ_1` has the data dilated by `q^n`.
* **Between the knots** the triplets of `μ_{q^{n+1}} = μ_{t,q^{n+1}} ∗ μ_t` and
  `μ_t = μ_{q^n,t} ∗ μ_{q^n}` add (A39(ii)); two positive semidefinite matrices with sum `0`
  vanish, and `ν_{q^n} ≤ ν_t ≤ ν_{q^{n+1}}` puts `ν_t` on `Γ_q` and makes it nonzero.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexOrder RealInnerProductSpace MatrixOrder

variable {d : ℕ}

/-! ## The set `Γ_q` -/

theorem latticePt_smul (c h : ℝ) (n : Zd d) : c • latticePt h n = latticePt (c * h) n := by
  simp [latticePt, smul_smul]

/-- **`prop:grid-pyramid-not-isotropic`, the set `Γ_q`.** For an integer `q ≥ 2`,
`⋃_k q^k hℤ^d = hℤ[1/q]^d`. The identity holds for every natural `q` and real `h`. -/
theorem grid_pyramid_not_isotropic_union {q : ℕ} {h : ℝ} :
    qLatticeUnion (q : ℝ) (gridSet d h) =
      {x | ∃ (k : ℕ) (n : Zd d), x = latticePt (h / (q : ℝ) ^ k) n} := by
  ext x
  simp only [qLatticeUnion, gridSet, mem_iUnion, mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨k, y, ⟨n, rfl⟩, rfl⟩
    rcases le_or_gt 0 k with hk | hk
    · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      refine ⟨0, (q : ℤ) ^ j • n, ?_⟩
      ext i
      simp [latticePt]
      ring
    · obtain ⟨j, hj⟩ := Int.exists_eq_neg_ofNat hk.le
      refine ⟨j, n, ?_⟩
      rw [latticePt_smul, hj, zpow_neg, zpow_natCast, div_eq_inv_mul]
  · rintro ⟨k, n, rfl⟩
    refine ⟨-(k : ℤ), latticePt h n, ⟨n, rfl⟩, ?_⟩
    rw [latticePt_smul, zpow_neg, zpow_natCast, div_eq_inv_mul]

/-- A full-rank lattice is countable (a discrete subspace of a second-countable space). -/
theorem countable_lattice (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ] :
    (Γ : Set (Rd d)).Countable := by
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  exact Set.countable_coe_iff.1 this

theorem countable_qLatticeUnion (q : ℝ) {Γ : Set (Rd d)} (hΓ : Γ.Countable) :
    (qLatticeUnion q Γ).Countable :=
  Set.countable_iUnion fun _ => hΓ.image _

/-- `q^k Γ ⊆ Γ_q`. -/
theorem smul_mem_qLatticeUnion (q : ℝ) {Γ : Set (Rd d)} {x : Rd d} (hx : x ∈ Γ) (k : ℤ) :
    (q ^ k) • x ∈ qLatticeUnion q Γ :=
  mem_iUnion.2 ⟨k, x, hx, rfl⟩

/-! ## Families carrying a ladder -/

/-- On `ℝ⁰` every probability law is `δ₀`, so a law other than `δ₀` needs `d ≥ 1`. -/
theorem one_le_of_ne_dirac {w : Measure (Rd d)} [IsProbabilityMeasure w]
    (hne : w ≠ Measure.dirac 0) : 1 ≤ d := by
  by_contra hd
  have hd0 : d = 0 := by omega
  subst hd0
  refine hne (eq_dirac_of_charFun_one fun ω => ?_)
  have h0 : ω = 0 := by
    ext i
    exact Fin.elim0 i
  simp [h0, charFun_zero]

/-- The kernels and steps of a carrying family are probability laws. -/
theorem CarriesLatticeLadder.prob {q : ℝ} {w : Measure (Rd d)} {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder q w μ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IsProbabilityMeasure (μ s t) :=
  hμ.2.1.isProbability s t hs hst

/-- **`μ_{q^n s, q^n t} = D_{q^n} μ_{s,t}`.** -/
theorem CarriesLatticeLadder.zpow {q : ℝ} {w : Measure (Rd d)} {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder q w μ) (n : ℤ) : μ 0 (q ^ n) = (μ 0 1).map fun x => (q ^ n) • x := by
  have h := step_zpow_of_cov hμ.1 hμ.2.2.1 n 0 1 le_rfl zero_le_one
  rwa [mul_zero, mul_one] at h

/-- **The step of the knot kernel**: `ŵ μ̂_1 = μ̂_1(q ·)`. -/
theorem CarriesLatticeLadder.step {q : ℝ} {w : Measure (Rd d)} {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder q w μ) (ω : Rd d) :
    charFun w ω * charFun (μ 0 1) ω = charFun (μ 0 1) (q • ω) := by
  obtain ⟨hq, hfam, hcov, hw⟩ := hμ
  have hk : (μ 0 1).map (fun x => q • x) = μ 0 q := by
    have := cov_kernel hcov zero_le_one
    rwa [mul_one] at this
  rw [← hw, ← charFun_kernel_mul μ hfam zero_le_one hq.le, ← hk, charFun_map_smul]

/-- **The product formula** (`eq:knot-product`): the partial products and the transforms of the
partial convolutions converge to `μ̂_1`. -/
theorem CarriesLatticeLadder.product (hd : 1 ≤ d) {q : ℝ} {w : Measure (Rd d)}
    [IsProbabilityMeasure w] {μ : ℝ → ℝ → Measure (Rd d)} (hμ : CarriesLatticeLadder q w μ)
    (ω : Rd d) :
    Tendsto (fun M => ladderProd q w M ω) atTop (𝓝 (charFun (μ 0 1) ω)) ∧
      Tendsto (fun M => charFun (ladderConv q w M) ω) atTop (𝓝 (charFun (μ 0 1) ω)) := by
  haveI := hμ.prob le_rfl zero_le_one
  have hid := isLawHemigroup_infinitelyDivisible hd hμ.2.1 0 1 le_rfl zero_le_one
  have hlim : ∀ ω : Rd d, Tendsto (fun M => ladderProd q w M ω) atTop
      (𝓝 (charFun (μ 0 1) ω)) :=
    tendsto_ladderProd hμ.1 w hμ.step continuous_charFun.continuousAt (by simp [charFun_zero])
      (cited_A40 _ hid)
  refine ⟨hlim ω, ?_⟩
  simp_rw [(ladderConv_charFun q w _).2 ω]
  exact hlim ω

/-- **The knot kernel of a symmetric mask is symmetric**: its transform is a limit of real
products. -/
theorem CarriesLatticeLadder.symm_one (hd : 1 ≤ d) {q : ℝ} {w : Measure (Rd d)}
    [IsProbabilityMeasure w] (hs : w.map (fun x => -x) = w) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder q w μ) : (μ 0 1).map (fun x => -x) = μ 0 1 := by
  haveI := hμ.prob le_rfl zero_le_one
  refine map_neg_eq_of_charFun_im fun ω => ?_
  have hlim := (Complex.continuous_im.tendsto _).comp (hμ.product hd ω).1
  have hzero : ∀ M, (ladderProd q w M ω).im = 0 := by
    intro M
    rw [ladderProd]
    have : ∀ m ∈ Finset.range M, charFun w ((q ^ (-((m : ℤ) + 1))) • ω) =
        (((charFun w ((q ^ (-((m : ℤ) + 1))) • ω)).re : ℝ) : ℂ) := fun m _ =>
      Complex.ext rfl (by simp [charFun_im_eq_zero_of_symm hs])
    rw [Finset.prod_congr rfl this, ← Complex.ofReal_prod, Complex.ofReal_im]
  simp only [Function.comp_def, hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Data of a law with symmetric data `D` and a probability law `m`: the dilate. -/
theorem isSymData_map_smul {m : Measure (Rd d)} {D : SymLevyData d} (h : IsSymData m D) {c : ℝ}
    (hc : c ≠ 0) : IsSymData (m.map fun x => c • x) (D.dilate hc) := fun ω => by
  rw [charFun_map_smul, h, SymLevyData.dilate_exponent]

/-- **The data of the knot kernel.** For a family carrying the ladder of a symmetric mask with
data `D_w`: `μ_1` has the data `(A_w/(q² - 1), ν*)`. -/
theorem CarriesLatticeLadder.knot_data (hd : 1 ≤ d) {q : ℝ} {w : Measure (Rd d)}
    [IsProbabilityMeasure w] (hs : w.map (fun x => -x) = w) {Dw : SymLevyData d}
    (hDw : IsSymData w Dw) {μ : ℝ → ℝ → Measure (Rd d)} (hμ : CarriesLatticeLadder q w μ) :
    ∃ D1 : SymLevyData d, D1.A = (q ^ 2 - 1)⁻¹ • Dw.A ∧ D1.ν = ladderNuStar q Dw.ν ∧
      IsSymData (μ 0 1) D1 := by
  have hq := hμ.1
  have hq0 : q ≠ 0 := by linarith
  haveI := hμ.prob le_rfl zero_le_one
  have hid := isLawHemigroup_infinitelyDivisible hd hμ.2.1 0 1 le_rfl zero_le_one
  obtain ⟨D1, hD1⟩ := exists_symData hid (hμ.symm_one hd hs)
  haveI : IsProbabilityMeasure ((μ 0 1).map fun x => q • x) :=
    Measure.isProbabilityMeasure_map (measurable_const_smul q).aemeasurable
  -- the two data of `μ_q`
  have hsum : IsSymData ((μ 0 1).map fun x => q • x) (Dw.addSmul D1 1) := fun ω => by
    rw [charFun_map_smul, ← hμ.step, hDw, hD1, SymLevyData.addSmul_exponent, max_eq_left
      zero_le_one, one_mul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add]
  obtain ⟨hA, hν⟩ := isSymData_unique (isSymData_map_smul hD1 hq0) hsum
  simp only [SymLevyData.dilate, SymLevyData.addSmul, max_eq_left zero_le_one, one_smul,
    ENNReal.ofReal_one] at hA hν
  refine ⟨D1, ?_, eq_ladderNuStar_of_map hq D1.ν_zero (fun ε hε => D1.measure_norm_gt_ne_top hε)
    hν, hD1⟩
  have hq21 : q ^ 2 - 1 ≠ 0 := by nlinarith
  rw [show Dw.A = (q ^ 2 - 1) • D1.A by rw [sub_smul, one_smul, hA, add_sub_cancel_right],
    smul_smul, inv_mul_cancel₀ hq21, one_smul]

/-- **`lem:knot-data`: the knot kernel of a carrying family.** For a family carrying the ladder of a
symmetric probability law `w`, the family itself not assumed symmetric: the partial products
converge to `μ̂_1` (`CarriesLatticeLadder.product`), `μ_1` is symmetric
(`CarriesLatticeLadder.symm_one`), and if `w` has data `D_w`, `μ_1` has the data
`(A_w/(q² - 1), ν*)` (`CarriesLatticeLadder.knot_data`). The node's statement, assembled from the
declarations its citing proofs call. -/
theorem knot_kernel_data (hd : 1 ≤ d) {q : ℝ} {w : Measure (Rd d)} [IsProbabilityMeasure w]
    (hs : w.map (fun x => -x) = w) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder q w μ) :
    (∀ ω : Rd d, Tendsto (fun M => ladderProd q w M ω) atTop (𝓝 (charFun (μ 0 1) ω))) ∧
      (μ 0 1).map (fun x => -x) = μ 0 1 ∧
      ∀ Dw : SymLevyData d, IsSymData w Dw → ∃ D1 : SymLevyData d,
        D1.A = (q ^ 2 - 1)⁻¹ • Dw.A ∧ D1.ν = ladderNuStar q Dw.ν ∧ IsSymData (μ 0 1) D1 :=
  ⟨fun ω => (hμ.product hd ω).1, hμ.symm_one hd hs, fun _ hDw => hμ.knot_data hd hs hDw⟩

/-! ## Lévy measures through data and triplets -/

/-- **Data give the Lévy measure and the Gaussian part** (A39(ii)). -/
theorem hasLevyMeasure_of_symData {m : Measure (Rd d)} [IsProbabilityMeasure m]
    {D : SymLevyData d} (h : IsSymData m D) :
    HasLevyMeasure m D.ν ∧ (D.A = 0 → HasNoGaussianPart m) := by
  have hT := SymLevyData.hasTriplet h
  have hid := isInfinitelyDivisible_of_hasTriplet hT
  refine ⟨⟨⟨_, hT⟩, fun T hT' => (cited_A39_unique m hid _ _ hT' hT).2.1⟩,
    fun hA => ⟨⟨_, hT⟩, fun T hT' => ?_⟩⟩
  rw [(cited_A39_unique m hid _ _ hT' hT).1]
  simp [SymLevyData.triplet, hA]

/-- A triplet gives the Lévy measure (A39(ii)). -/
theorem hasLevyMeasure_of_hasTriplet {m : Measure (Rd d)} [IsProbabilityMeasure m]
    {T : LevyTriplet d} (h : HasTriplet m T) :
    HasLevyMeasure m T.ν ∧ (T.A = 0 → HasNoGaussianPart m) := by
  have hid := isInfinitelyDivisible_of_hasTriplet h
  refine ⟨⟨⟨_, h⟩, fun T' hT' => (cited_A39_unique m hid _ _ hT' h).2.1⟩,
    fun hA => ⟨⟨_, h⟩, fun T' hT' => ?_⟩⟩
  rw [(cited_A39_unique m hid _ _ hT' h).1, hA]

/-- `D_{q^n} ν* = ∑_{m ≥ 1} D_{q^{n-m}} ν`. -/
theorem map_ladderNuStar_zpow {q : ℝ} (hq : 0 < q) (ν : Measure (Rd d)) (n : ℤ) :
    (ladderNuStar q ν).map (fun x => (q ^ n) • x) =
      Measure.sum fun m : ℕ => ν.map fun x => (q ^ (n - ((m : ℤ) + 1))) • x := by
  rw [ladderNuStar, Measure.map_sum (measurable_const_smul _).aemeasurable]
  congr 1
  funext m
  rw [Measure.map_map (measurable_const_smul _) (measurable_const_smul _)]
  congr 1
  funext x
  simp only [Function.comp_apply, smul_smul, sub_eq_add_neg, zpow_add₀ hq.ne']

/-- Two positive semidefinite matrices with sum `0` vanish. -/
theorem posSemidef_eq_zero_of_add {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : A + B = 0) : A = 0 := by
  have hA' : 0 ≤ A := hA.nonneg
  have hB' : 0 ≤ B := hB.nonneg
  have h1 : A = -B := eq_neg_of_add_eq_zero_left h
  exact le_antisymm (by rw [h1]; exact neg_nonpos.2 hB') hA'

/-- A map by `c •` of a measure is `0` only if the measure is. -/
theorem map_smul_ne_zero {ν : Measure (Rd d)} (hν : ν ≠ 0) (c : ℝ) :
    ν.map (fun x => c • x) ≠ 0 := by
  intro h0
  apply hν
  have h1 := congrArg (fun m : Measure (Rd d) => m univ) h0
  simp only [Measure.map_apply (measurable_const_smul c) MeasurableSet.univ, preimage_univ,
    Measure.coe_zero, Pi.zero_apply] at h1
  exact Measure.measure_univ_eq_zero.1 h1

/-- `∑_m D_{c_m} ν` is carried by `Γ_q` when `ν` is carried by `Γ`. -/
theorem sum_map_qLatticeUnion_compl {q : ℝ} {Γ : Set (Rd d)} (hΓ : Γ.Countable)
    {ν : Measure (Rd d)} (hν : ν Γᶜ = 0) (k : ℕ → ℤ) :
    (Measure.sum fun m : ℕ => ν.map fun x => (q ^ k m) • x) (qLatticeUnion q Γ)ᶜ = 0 := by
  have hmeas : MeasurableSet (qLatticeUnion q Γ)ᶜ :=
    (countable_qLatticeUnion q hΓ).measurableSet.compl
  rw [Measure.sum_apply _ hmeas, ENNReal.tsum_eq_zero]
  intro m
  rw [Measure.map_apply (measurable_const_smul _) hmeas]
  refine measure_mono_null (fun x hx => ?_) hν
  intro hxΓ
  exact hx (smul_mem_qLatticeUnion q hxΓ (k m))

/-! ## `prop:grid-pyramid-not-isotropic`(1) -/

/-- **The data of the mask**: a mask on a full-rank lattice is infinitely divisible with data
`(0, ν_w)`, `ν_w` finite, nonzero and carried by `Γ ∖ {0}`. -/
theorem lattice_mask_data (hd : 1 ≤ d) (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ]
    [IsZLattice ℝ Γ] {q : ℝ} {w : Measure (Rd d)} (hw : IsLatticeMask (Γ : Set (Rd d)) w)
    {μ : ℝ → ℝ → Measure (Rd d)} (hμ : CarriesLatticeLadder q w μ) :
    IsInfinitelyDivisible w ∧ ∃ Dw : SymLevyData d, IsSymData w Dw ∧ Dw.A = 0 ∧
      IsFiniteMeasure Dw.ν ∧ Dw.ν ≠ 0 ∧ Dw.ν ((Γ : Set (Rd d)) \ {0})ᶜ = 0 := by
  obtain ⟨hprob, hs, hne, hcarr⟩ := hw
  have hid : IsInfinitelyDivisible w := by
    have := isLawHemigroup_infinitelyDivisible hd hμ.2.1 1 q zero_le_one hμ.1.le
    rwa [hμ.2.2.2] at this
  obtain ⟨Dw, hDw⟩ := exists_symData hid hs
  obtain ⟨hA, hfin, hcar⟩ := lattice_infinitely_divisible w hid _ (SymLevyData.hasTriplet hDw)
    Γ hcarr
  have hA0 : Dw.A = 0 := by
    have h2 : (2 : ℝ) • Dw.A = 0 := hA
    exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
  refine ⟨hid, Dw, hDw, hA0, hfin, fun h0 => hne (eq_dirac_of_charFun_one fun ω => ?_), hcar⟩
  rw [hDw ω]
  simp [SymLevyData.exponent, pairExponent, hA0, h0, quad_zero]

/-- `ν_{q^n} := ∑_{m ≥ 1} D_{q^{n-m}} ν`, the Lévy measure at the knot `q^n`. -/
noncomputable def knotNu (q : ℝ) (ν : Measure (Rd d)) (n : ℤ) : Measure (Rd d) :=
  Measure.sum fun m : ℕ => ν.map fun x => (q ^ (n - ((m : ℤ) + 1))) • x

/-- **The data at the knots**: `μ_{q^n}` has the data `(0, ν_{q^n})` when the mask has
`(0, ν_w)`. -/
theorem CarriesLatticeLadder.knots (hd : 1 ≤ d) {q : ℝ} {w : Measure (Rd d)}
    [IsProbabilityMeasure w] (hs : w.map (fun x => -x) = w) {Dw : SymLevyData d}
    (hDw : IsSymData w Dw) (hA0 : Dw.A = 0) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder q w μ) (n : ℤ) :
    ∃ Dn : SymLevyData d, IsSymData (μ 0 (q ^ n)) Dn ∧ Dn.A = 0 ∧ Dn.ν = knotNu q Dw.ν n := by
  have hq0 : 0 < q := by linarith [hμ.1]
  obtain ⟨D1, hA1, hν1, hD1⟩ := hμ.knot_data hd hs hDw
  refine ⟨D1.dilate (zpow_ne_zero n hq0.ne'), ?_, ?_, ?_⟩
  · rw [hμ.zpow n]
    exact isSymData_map_smul hD1 _
  · simp [SymLevyData.dilate, hA1, hA0]
  · simp only [SymLevyData.dilate]
    rw [hν1, map_ladderNuStar_zpow hq0, knotNu]

/-- `D_{q^{n-1}} ν ≤ ν_{q^n}`. -/
theorem map_le_knotNu (q : ℝ) (ν : Measure (Rd d)) (n : ℤ) :
    ν.map (fun x => (q ^ (n - 1)) • x) ≤ knotNu q ν n := by
  have h := Measure.le_sum (fun m : ℕ => ν.map fun x => (q ^ (n - ((m : ℤ) + 1))) • x) 0
  rw [knotNu]
  simpa using h

/-- **Between the knots.** For `t > 0` and `n = ⌊log_q t⌋`, the law `μ_t` has a triplet with no
Gaussian part and `ν_{q^n} ≤ ν_t ≤ ν_{q^{n+1}}`. -/
theorem CarriesLatticeLadder.between (hd : 1 ≤ d) {q : ℝ} {w : Measure (Rd d)}
    [IsProbabilityMeasure w] (hs : w.map (fun x => -x) = w) {Dw : SymLevyData d}
    (hDw : IsSymData w Dw) (hA0 : Dw.A = 0) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder q w μ) {t : ℝ} (ht : 0 < t) :
    IsInfinitelyDivisible (μ 0 t) ∧ ∃ T : LevyTriplet d, HasTriplet (μ 0 t) T ∧ T.A = 0 ∧
      knotNu q Dw.ν (dgLevel q t) ≤ T.ν ∧ T.ν ≤ knotNu q Dw.ν (dgLevel q t + 1) := by
  have hq := hμ.1
  have hq0 : 0 < q := by linarith
  obtain ⟨hn1, hn2⟩ := dgLevel_spec hq ht
  set n := dgLevel q t with hn
  have hfam := hμ.2.1
  have ht0 : 0 ≤ t := ht.le
  have hqn : 0 ≤ q ^ n := (zpow_pos hq0 n).le
  haveI := hμ.prob le_rfl ht0
  haveI := hμ.prob ht0 hn2.le
  haveI := hμ.prob hqn hn1
  haveI := hμ.prob le_rfl hqn
  haveI := hμ.prob le_rfl (zpow_pos hq0 (n + 1)).le
  have hidt := isLawHemigroup_infinitelyDivisible hd hfam 0 t le_rfl ht0
  have hida := isLawHemigroup_infinitelyDivisible hd hfam t _ ht0 hn2.le
  have hidb := isLawHemigroup_infinitelyDivisible hd hfam _ t hqn hn1
  obtain ⟨Tt, hTt⟩ := cited_A39_exists _ hidt
  obtain ⟨Ta, hTa⟩ := cited_A39_exists _ hida
  obtain ⟨Tb, hTb⟩ := cited_A39_exists _ hidb
  obtain ⟨Dn, hDn, -, hDnν⟩ := hμ.knots hd hs hDw hA0 n
  obtain ⟨Dn1, hDn1, hDn1A, hDn1ν⟩ := hμ.knots hd hs hDw hA0 (n + 1)
  -- `μ_{q^{n+1}} = μ_{t,q^{n+1}} ∗ μ_t`
  have hup : HasTriplet (μ 0 (q ^ (n + 1))) (Ta.add Tt) := by
    rw [hfam.cascade 0 t _ le_rfl ht0 hn2.le]
    exact hTa.conv hTt
  -- `μ_t = μ_{q^n,t} ∗ μ_{q^n}`
  have hlow : HasTriplet (μ 0 t) (Tb.add Dn.triplet) := by
    rw [hfam.cascade 0 _ t le_rfl hqn hn1]
    exact hTb.conv (SymLevyData.hasTriplet hDn)
  have hidn1 := isLawHemigroup_infinitelyDivisible hd hfam 0 _ le_rfl (zpow_pos hq0 (n + 1)).le
  obtain ⟨hAu, hνu, -⟩ := cited_A39_unique _ hidn1 _ _ hup (SymLevyData.hasTriplet hDn1)
  obtain ⟨-, hνl, -⟩ := cited_A39_unique _ hidt _ _ hlow hTt
  have hAt : Tt.A = 0 := by
    have h2 : Tt.A + Ta.A = 0 := by
      rw [add_comm]
      change Ta.A + Tt.A = (2 : ℝ) • Dn1.A at hAu
      rw [hAu, hDn1A, smul_zero]
    exact posSemidef_eq_zero_of_add Tt.A_posSemidef Ta.A_posSemidef h2
  refine ⟨hidt, Tt, hTt, hAt, ?_, ?_⟩
  · rw [← hDnν, ← hνl]
    exact Measure.le_add_left le_rfl
  · have h1 : Ta.ν + Tt.ν = Dn1.ν := hνu
    rw [← hDn1ν, ← h1]
    exact Measure.le_add_left le_rfl

/-- **`prop:grid-pyramid-not-isotropic`(1), the covariant kernel.** For an exact grid pyramid
carried by `μ`: `Γ_q` is countable; the mask is infinitely divisible, the compound Poisson law of a
finite Lévy measure `ν_w ≠ 0` carried by `Γ ∖ {0}`, with no Gaussian part; `μ̂_1(ω)` is the limit
of the partial products `∏_{m ≤ M} ŵ(q^{-m}ω)` and of the transforms of
`D_{q^{-1}}w * ⋯ * D_{q^{-M}}w`; every `μ_t`, `t > 0`, is infinitely divisible with no Gaussian
part and a nonzero Lévy measure carried by `Γ_q`; and `ν_{q^n} = ∑_{m ≥ 1} D_{q^{n-m}} ν_w`. -/
theorem grid_pyramid_not_isotropic_1 (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ]
    [IsZLattice ℝ Γ] {q : ℝ} (w : Measure (Rd d)) (hw : IsLatticeMask (Γ : Set (Rd d)) w)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : CarriesLatticeLadder q w μ) :
    (qLatticeUnion q (Γ : Set (Rd d))).Countable ∧ IsInfinitelyDivisible w ∧
      (∃ νw : Measure (Rd d), HasLevyMeasure w νw ∧ HasNoGaussianPart w ∧ IsFiniteMeasure νw ∧
        νw ≠ 0 ∧ νw ((Γ : Set (Rd d)) \ {0})ᶜ = 0 ∧ w = compoundPoissonLaw νw) ∧
      (∀ ω : Rd d, Tendsto (fun M => ladderProd q w M ω) atTop (𝓝 (charFun (μ 0 1) ω)) ∧
        Tendsto (fun M => charFun (ladderConv q w M) ω) atTop (𝓝 (charFun (μ 0 1) ω))) ∧
      (∀ t : ℝ, 0 < t → IsInfinitelyDivisible (μ 0 t) ∧ HasNoGaussianPart (μ 0 t) ∧
        ∃ ν : Measure (Rd d), HasLevyMeasure (μ 0 t) ν ∧ ν ≠ 0 ∧
          ν (qLatticeUnion q (Γ : Set (Rd d)))ᶜ = 0) ∧
      ∀ νw : Measure (Rd d), HasLevyMeasure w νw → ∀ n : ℤ,
        HasLevyMeasure (μ 0 (q ^ n))
          (Measure.sum fun m : ℕ => νw.map fun x => (q ^ (n - ((m : ℤ) + 1))) • x) := by
  haveI := hw.1
  have hd := one_le_of_ne_dirac hw.2.2.1
  have hq0 : 0 < q := by linarith [hμ.1]
  have hΓc := countable_lattice Γ
  obtain ⟨hid, Dw, hDw, hA0, hfin, hne, hcar⟩ := lattice_mask_data hd Γ hw hμ
  obtain ⟨hLw, hGw⟩ := hasLevyMeasure_of_symData hDw
  have hΓ0 : Dw.ν (Γ : Set (Rd d))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 sdiff_subset) hcar
  refine ⟨countable_qLatticeUnion q hΓc, hid, ⟨Dw.ν, hLw, hGw hA0, hfin, hne, hcar, ?_⟩,
    hμ.product hd, fun t ht => ?_, fun νw hνw n => ?_⟩
  · -- the compound Poisson law
    haveI := hfin
    change w = cpLaw Dw.ν
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_cpLaw_symm _ Dw.ν_symm, hDw ω]
    simp [SymLevyData.exponent, pairExponent, hA0, quad_zero]
  · -- between the knots
    haveI := hμ.prob le_rfl ht.le
    obtain ⟨hidt, Tt, hTt, hAt, hlo, hhi⟩ := hμ.between hd hw.2.1 hDw hA0 ht
    obtain ⟨hLt, hGt⟩ := hasLevyMeasure_of_hasTriplet hTt
    refine ⟨hidt, hGt hAt, Tt.ν, hLt, fun h0 => ?_, ?_⟩
    · rw [h0] at hlo
      exact map_smul_ne_zero hne _
        (le_antisymm ((map_le_knotNu q Dw.ν _).trans hlo) (Measure.zero_le _))
    · exact nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hhi _).trans_eq
        (sum_map_qLatticeUnion_compl hΓc hΓ0 _))
  · -- at the knots
    have hνeq : νw = Dw.ν := by
      obtain ⟨⟨T, hT⟩, hall⟩ := hνw
      rw [← hall T hT]
      exact hLw.2 T hT
    obtain ⟨Dn, hDn, -, hDnν⟩ := hμ.knots hd hw.2.1 hDw hA0 n
    haveI := hμ.prob le_rfl (zpow_pos hq0 n).le
    rw [hνeq, ← knotNu, ← hDnν]
    exact (hasLevyMeasure_of_symData hDn).1

end Pyramids
