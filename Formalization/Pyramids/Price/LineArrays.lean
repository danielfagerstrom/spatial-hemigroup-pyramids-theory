/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Price.ExactMasks
import Pyramids.Line.GridPyramids
import Pyramids.Pyramid.EquivalentWeights
import Pyramids.Price.ResolventMask

/-!
# `prop:line-and-arrays`: the line, and the arrays

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:line-and-arrays`. Phase 5, wave 3b. The
statements are the skeleton's (`PyramidsSkeleton/Ch05Price.lean`), unchanged in name, binders and
conclusion.

**(1) The line, without A30.** The printed proof read iso v0.1's Lemma 3.3 (ledger A30) to pass
between operators and laws. Both bridges are already proved on the line:

* *from operators to laws*, `CarriesGridLadder.family` (`Line/GridTransfer.lean`) returns a
  symmetric family, `q`-covariant with `S_q t = qt` and step `w`, which carries the lattice ladder;
* *from laws to operators*, the two criteria agree: lifted to `ℝ¹`, a family carrying the lattice
  ladder makes the mask infinitely divisible with `∫ log₊|x| w(dx) < ∞` (`exact_masks_1`, which
  reads no lattice), and that is the second criterion of `grid_pyramids_id_2`, which builds the
  operator family.

So the node cites nothing of its own.

**(2) The arrays.** The records are computed on the lattice through its basis `b`, `ι k = ∑ kᵢbᵢ`.
The tools:

* `integral_eq_tsum_of_carried`: against a finite law carried by `Γ`, a bounded function
  integrates to `∑ₖ μ{ι k} g(ι k)`, with no measurability asked of `g` (the law is read through the
  measurable embedding `ι` of the countable `ℤ^d`);
* `latticeApply_eq_mconvE`: so `latticeApply b μ f m = (μ * f_Γ)(ι m)` for the extension `f_Γ` of
  `f` by `0` off `Γ`, which is measurable;
* `mconvE_mconvE`: `ν * (μ * φ) = (μ ∗ ν) * φ` at every point, for bounded measurable `φ`;
* `equivWeight_succ`: `W_{n+1} = W_n ∗ D_{q^n}w`, by the transforms.

Then the record formula is an induction on the level, the one the print gives; and for a family
carrying the ladder `μ_{1,q^n} = W_n` by the cascade and `step_zpow_of_cov`. The exactness of the
pyramid, assumed in the second conjunct, is not read: every family carrying the ladder has
`μ_{1,q^n} = W_n`, and a family carrying it exists exactly when the pyramid is exact.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (mconvE)
open scoped Topology ENNReal

variable {d : ℕ}

/-! ## (1) The line -/

/-- **`prop:line-and-arrays`(1), the line.** For a mask `w` on `hℤ` and `q > 1`, the grid pyramid
is exact on laws (`def:exact-grid-pyramid` at `E = ℝ`) iff it is exact on operators
(`def:grid-pyramid-line`). -/
theorem line_and_arrays_1 {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : Measure ℝ)
    (hw : IsGridMask h w) : IsExactLatticePyramid q w ↔ IsExactGridPyramid q w := by
  constructor
  · rintro ⟨μ, hq', hhem, hcov, h1⟩
    obtain ⟨hprob, hsym, hne, hcarr⟩ := hw
    haveI := hprob
    have hsym1 : (w.map lineEmbL).map (fun x => -x) = w.map lineEmbL := by
      rw [Measure.map_map measurable_neg lineEmbL.continuous.measurable]
      have e : ((fun x : Rd 1 => -x) ∘ lineEmbL) = lineEmbL ∘ fun x : ℝ => -x :=
        funext fun x => (map_neg lineEmbL x).symm
      rw [e, ← Measure.map_map lineEmbL.continuous.measurable measurable_neg]
      exact congrArg (fun m : Measure ℝ => m.map lineEmbL) hsym
    have hcar : CarriesLatticeLadder q (w.map lineEmbL) (fun s t => (μ s t).map lineEmbL) :=
      ⟨hq', isLawHemigroup_lineEmb hhem, isCovariantAt_lineEmb hcov, by simp only [h1]⟩
    obtain ⟨hid, hmom⟩ := (exact_masks_1 hq _ (isProbabilityMeasure_map_lineEmb w) hsym1
      (map_lineEmb_ne_dirac hne)).2.1 ⟨_, hcar⟩
    refine (grid_pyramids_id_2 hq hh w ⟨hprob, hsym, hne, hcarr⟩).2.2 ⟨?_, ?_⟩
    · have := isInfinitelyDivisible_map_lineProj hid
      rwa [map_lineProj_lineEmb] at this
    · rwa [lintegral_posLog_map_lineEmb] at hmom
  · rintro ⟨Φ, S, μ, hc⟩
    obtain ⟨hsymF, hcov, h1⟩ := hc.family
    exact ⟨μ, hq, hsymF.1, hcov, h1⟩

/-! ## (2) The lattice read through a basis -/

section Lattice

variable {Γ : Submodule ℤ (Rd d)} (b : Module.Basis (Fin d) ℤ Γ)

theorem latticeIdxPt_add (k l : Zd d) :
    latticeIdxPt b (k + l) = latticeIdxPt b k + latticeIdxPt b l := by
  simp [latticeIdxPt, map_add]

theorem latticeIdxPt_sub (k l : Zd d) :
    latticeIdxPt b (k - l) = latticeIdxPt b k - latticeIdxPt b l := by
  simp [latticeIdxPt, map_sub]

theorem latticeIdxPt_zsmul (c : ℤ) (k : Zd d) :
    latticeIdxPt b (c • k) = c • latticeIdxPt b k := by
  unfold latticeIdxPt
  rw [map_zsmul]
  rfl

theorem latticeIdxPt_zero : latticeIdxPt b (0 : Zd d) = 0 := by
  simp [latticeIdxPt]

theorem latticeIdxPt_injective : Function.Injective (latticeIdxPt b) := by
  intro k l h
  exact b.equivFun.symm.injective (Subtype.ext h)

theorem range_latticeIdxPt : range (latticeIdxPt b) = (Γ : Set (Rd d)) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact (b.equivFun.symm k).2
  · intro hx
    exact ⟨b.equivFun ⟨x, hx⟩, by simp [latticeIdxPt]⟩

include b in
theorem countable_latticeIdx : (Γ : Set (Rd d)).Countable := by
  rw [← range_latticeIdxPt b]
  exact countable_range _

theorem measurableEmbedding_latticeIdxPt : MeasurableEmbedding (latticeIdxPt b) where
  injective := latticeIdxPt_injective b
  measurable := measurable_of_countable _
  measurableSet_image' := fun s _ =>
    ((countable_range _).mono (image_subset_range _ s)).measurableSet

/-- **A bounded function against a finite law carried by `Γ`** is the sum over the atoms. No
measurability is asked of `g`. -/
theorem integral_eq_tsum_of_carried (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (hμ : μ (Γ : Set (Rd d))ᶜ = 0) {g : Rd d → ℝ} {C : ℝ} (hg : ∀ x, |g x| ≤ C) :
    ∫ x, g x ∂μ = ∑' k, (μ {latticeIdxPt b k}).toReal * g (latticeIdxPt b k) := by
  have hemb := measurableEmbedding_latticeIdxPt b
  have hres : μ.restrict (range (latticeIdxPt b)) = μ := by
    rw [range_latticeIdxPt]
    exact Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 hμ |>.mono
      fun x hx => by simpa using hx)
  have hmap : (μ.comap (latticeIdxPt b)).map (latticeIdxPt b) = μ := by
    rw [hemb.map_comap, hres]
  haveI : IsFiniteMeasure (μ.comap (latticeIdxPt b)) := by
    refine ⟨?_⟩
    rw [hemb.comap_apply]
    exact measure_lt_top _ _
  conv_lhs => rw [← hmap]
  rw [hemb.integral_map, integral_countable]
  · refine tsum_congr fun k => ?_
    rw [smul_eq_mul, measureReal_def, hemb.comap_apply, image_singleton]
  · exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
      (Eventually.of_forall fun k => by rw [Real.norm_eq_abs]; exact hg _)

/-- **The array `f`, as a function on `ℝ^d`**: `f_Γ(ι k) = f k`, and `0` off `Γ`. -/
noncomputable def latticeExt (f : Zd d → ℝ) : Rd d → ℝ :=
  Function.extend (latticeIdxPt b) f 0

theorem latticeExt_apply (f : Zd d → ℝ) (k : Zd d) :
    latticeExt b f (latticeIdxPt b k) = f k :=
  (latticeIdxPt_injective b).extend_apply _ _ _

theorem measurable_latticeExt (f : Zd d → ℝ) : Measurable (latticeExt b f) :=
  (measurableEmbedding_latticeIdxPt b).measurable_extend (measurable_of_countable _)
    measurable_const

theorem abs_latticeExt_le {f : Zd d → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C) (x : Rd d) :
    |latticeExt b f x| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf 0)
  unfold latticeExt
  by_cases hx : ∃ k, latticeIdxPt b k = x
  · obtain ⟨k, rfl⟩ := hx
    rw [(latticeIdxPt_injective b).extend_apply]
    exact hf k
  · rw [Function.extend_apply' _ _ _ hx]
    simpa using hC

/-- **`latticeApply` is a convolution on `ℝ^d`**: `latticeApply b μ f m = (μ * f_Γ)(ι m)` for a
finite law carried by `Γ` and a bounded array. -/
theorem latticeApply_eq_mconvE (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (hμ : μ (Γ : Set (Rd d))ᶜ = 0) {f : Zd d → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C) (m : Zd d) :
    latticeApply b μ f m = mconvE μ (latticeExt b f) (latticeIdxPt b m) := by
  rw [mconvE, integral_eq_tsum_of_carried b μ hμ (g := fun x => latticeExt b f
    (latticeIdxPt b m - x)) (fun x => abs_latticeExt_le b hf _), latticeApply]
  refine tsum_congr fun k => ?_
  rw [← latticeIdxPt_sub, latticeExt_apply]

end Lattice

/-! ## Convolutions of bounded measurable functions, pointwise -/

theorem abs_mconvE_le (μ : Measure (Rd d)) [IsProbabilityMeasure μ] {φ : Rd d → ℝ} {C : ℝ}
    (hφ : ∀ x, |φ x| ≤ C) (x : Rd d) : |mconvE μ φ x| ≤ C := by
  rw [mconvE, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := C) (Eventually.of_forall fun y => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact hφ _
  · simp

theorem measurable_mconvE (μ : Measure (Rd d)) [SFinite μ] {φ : Rd d → ℝ} (hφ : Measurable φ) :
    Measurable (mconvE μ φ) := by
  have h : StronglyMeasurable (Function.uncurry fun x y : Rd d => φ (x - y)) :=
    (hφ.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := μ)).measurable

/-- **`ν * (μ * φ) = (μ ∗ ν) * φ` at every point**, for finite laws and a bounded measurable
`φ`. -/
theorem mconvE_mconvE (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {φ : Rd d → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (x : Rd d) :
    mconvE ν (mconvE μ φ) x = mconvE (μ ∗ ν) φ x := by
  have hadd : Measurable fun p : Rd d × Rd d => p.1 + p.2 := measurable_fst.add measurable_snd
  have hm : Measurable fun z : Rd d => φ (x - z) := hφ.comp (measurable_const.sub measurable_id)
  have hint : Integrable (fun p : Rd d × Rd d => φ (x - (p.1 + p.2))) (μ.prod ν) :=
    Integrable.of_bound (hm.comp hadd).aestronglyMeasurable C
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC _)
  simp only [mconvE]
  rw [Measure.conv, integral_map hadd.aemeasurable hm.aestronglyMeasurable,
    integral_prod_symm _ hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  congr 1
  abel

/-! ## The equivalent weights -/

/-- `W_{n+1} = W_n ∗ D_{q^n} w`. -/
theorem equivWeight_succ (q : ℝ) (w : Measure (Rd d)) [IsProbabilityMeasure w] (n : ℕ) :
    equivWeight q w (n + 1) = equivWeight q w n ∗ w.map (fun x => (q ^ n) • x) := by
  obtain ⟨hp1, hc1⟩ := equivWeight_charFun q w (n + 1)
  obtain ⟨hp0, hc0⟩ := equivWeight_charFun q w n
  haveI := hp0
  haveI : IsProbabilityMeasure (w.map fun x => (q ^ n) • x) :=
    Measure.isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_conv, hc1, hc0, Finset.prod_range_succ, charFun_map_smul]

theorem isProbabilityMeasure_equivWeight (q : ℝ) (w : Measure (Rd d)) [IsProbabilityMeasure w]
    (n : ℕ) : IsProbabilityMeasure (equivWeight q w n) :=
  (equivWeight_charFun q w n).1

theorem equivWeight_zero (q : ℝ) (w : Measure (Rd d)) : equivWeight q w 0 = Measure.dirac 0 := by
  simp [equivWeight, convList]

/-- **`W_n` is carried by `Γ`** when `w` is and `q` is an integer. -/
theorem equivWeight_carried {Γ : Submodule ℤ (Rd d)} (b : Module.Basis (Fin d) ℤ Γ) (q : ℕ)
    (w : Measure (Rd d)) [IsProbabilityMeasure w] (hw : w (Γ : Set (Rd d))ᶜ = 0) (n : ℕ) :
    equivWeight (q : ℝ) w n (Γ : Set (Rd d))ᶜ = 0 := by
  have hΓm : MeasurableSet (Γ : Set (Rd d)) := (countable_latticeIdx b).measurableSet
  have hsmul : ∀ (k : ℕ) (x : Rd d), x ∈ (Γ : Set (Rd d)) →
      ((q : ℝ) ^ k) • x ∈ (Γ : Set (Rd d)) := by
    intro k x hx
    have : ((q : ℝ) ^ k) • x = ((q : ℤ) ^ k) • x := by
      rw [← Int.cast_smul_eq_zsmul ℝ]; push_cast; rfl
    rw [this]
    exact Γ.smul_mem _ hx
  induction n with
  | zero =>
    rw [equivWeight_zero, Measure.dirac_apply' _ hΓm.compl,
      indicator_of_notMem (show (0 : Rd d) ∉ (Γ : Set (Rd d))ᶜ from fun h => h Γ.zero_mem)]
  | succ n ih =>
    haveI := isProbabilityMeasure_equivWeight (q : ℝ) w n
    haveI : IsProbabilityMeasure (w.map fun x => ((q : ℝ) ^ n) • x) :=
      Measure.isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
    rw [equivWeight_succ]
    refine conv_compl_null_Rd (A := (Γ : Set (Rd d))) (B := (Γ : Set (Rd d))) hΓm ?_ ih ?_
    · intro x hx y hy
      exact Γ.add_mem hx hy
    · rw [Measure.map_apply (measurable_const_smul _) hΓm.compl]
      refine measure_mono_null (fun x hx => ?_) hw
      intro hxΓ
      exact hx (hsmul n x hxΓ)

/-! ## (2) The arrays -/

/-- **The record formula, in convolution form**: the level-`n` record at `m` is
`(W_n * f_Γ)(ι(qⁿm))`. -/
theorem decimRecord_eq_mconvE {Γ : Submodule ℤ (Rd d)} (b : Module.Basis (Fin d) ℤ Γ) {q : ℕ}
    (w : Measure (Rd d)) [IsProbabilityMeasure w] (hcarr : w (Γ : Set (Rd d))ᶜ = 0)
    {f : Zd d → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C) (n : ℕ) (m : Zd d) :
    decimRecord (latticeIdxKernel b w) q f n m =
      mconvE (equivWeight (q : ℝ) w n) (latticeExt b f)
        (latticeIdxPt b (((q : ℤ) ^ n) • m)) := by
  induction n generalizing m with
  | zero =>
    rw [equivWeight_zero, pow_zero, one_smul]
    simp [decimRecord, mconvE, latticeExt_apply]
  | succ n ih =>
    haveI := isProbabilityMeasure_equivWeight (q : ℝ) w n
    set G := mconvE (equivWeight (q : ℝ) w n) (latticeExt b f) with hG
    have hGm : Measurable G := measurable_mconvE _ (measurable_latticeExt b f)
    have hGb : ∀ x, |G x| ≤ C := abs_mconvE_le _ (abs_latticeExt_le b hf)
    set X := latticeIdxPt b (((q : ℤ) ^ (n + 1)) • m) with hX
    have hscal : ∀ y : Rd d, ((q : ℝ) ^ n) • y = ((q : ℤ) ^ n) • y := by
      intro y; rw [← Int.cast_smul_eq_zsmul ℝ]; push_cast; rfl
    -- the right side as an integral against `w`
    have hR : mconvE (equivWeight (q : ℝ) w (n + 1)) (latticeExt b f) X =
        ∫ z, G (X - ((q : ℝ) ^ n) • z) ∂w := by
      rw [equivWeight_succ, ← mconvE_mconvE _ _ (measurable_latticeExt b f)
        (abs_latticeExt_le b hf), mconvE, ← hG,
        integral_map (measurable_const_smul _).aemeasurable (f := fun y => G (X - y))
          (hGm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable]
    rw [hR, integral_eq_tsum_of_carried b w hcarr (C := C) fun x => hGb _]
    simp only [decimRecord, kconv, latticeIdxKernel]
    refine tsum_congr fun j => ?_
    rw [ih]
    congr 1
    rw [hG, hX, hscal, ← latticeIdxPt_zsmul, ← latticeIdxPt_sub]
    congr 2
    rw [smul_sub, smul_smul, pow_succ]

/-- **A family carrying the ladder has `μ_{1,qⁿ} = W_n`**: the cascade and `D_{q^k}` iterated. -/
theorem carries_equivWeight {q : ℝ} {w : Measure (Rd d)} {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : CarriesLatticeLadder q w μ) (n : ℕ) : μ 1 (q ^ n) = equivWeight q w n := by
  obtain ⟨hq, hhem, hcov, h1⟩ := hμ
  haveI : IsProbabilityMeasure w := h1 ▸ hhem.isProbability 1 q zero_le_one hq.le
  induction n with
  | zero => rw [pow_zero, hhem.diag 1 zero_le_one, equivWeight_zero]
  | succ n ih =>
    have hle : (1 : ℝ) ≤ q ^ n := one_le_pow₀ hq.le
    have hstep : μ (q ^ n) (q ^ (n + 1)) = w.map fun x => (q ^ n) • x := by
      have := step_zpow_of_cov hq hcov (n : ℤ) 1 q zero_le_one hq.le
      rw [zpow_natCast, mul_one, h1, ← pow_succ] at this
      exact this
    haveI := isProbabilityMeasure_equivWeight q w n
    haveI : IsProbabilityMeasure (w.map fun x => (q ^ n) • x) :=
      Measure.isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
    rw [hhem.cascade 1 (q ^ n) (q ^ (n + 1)) zero_le_one hle
        (pow_le_pow_right₀ hq.le (Nat.le_succ n)), hstep, ih, equivWeight_succ,
      Measure.conv_comm]

/-- **`prop:line-and-arrays`(2), the arrays.** For an integer `q`, a probability `w` on a
full-rank lattice `Γ` with basis `b` and a bounded array `f` on `Γ`: the level-`n` record is
`(D_{q^{n-1}}w * ⋯ * w * f)` read on `q^nΓ`; if the grid pyramid is exact, every carrying family
has `μ_{1,q^n} = D_{q^{n-1}}w * ⋯ * w`, and the record is `μ_{1,q^n} * f` read on `q^nΓ`, exact in
sense (i). The skeleton's `2 ≤ q` is not read and was dropped on 2026-11-15, a strengthening;
the exactness assumed in the second conjunct is not read either (a family carrying the ladder
exists exactly when the pyramid is exact). -/
theorem line_and_arrays_2 (Γ : Submodule ℤ (Rd d)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (b : Module.Basis (Fin d) ℤ Γ) {q : ℕ} (w : Measure (Rd d))
    [IsProbabilityMeasure w] (hcarr : w (Γ : Set (Rd d))ᶜ = 0) (f : Zd d → ℝ)
    (hf : ∃ C : ℝ, ∀ n, |f n| ≤ C) (n : ℕ) :
    (∀ m : Zd d, decimRecord (latticeIdxKernel b w) q f n m =
      latticeApply b (equivWeight (q : ℝ) w n) f (((q : ℤ) ^ n) • m)) ∧
      (IsExactLatticePyramid (q : ℝ) w → ∀ μ : ℝ → ℝ → Measure (Rd d),
        CarriesLatticeLadder (q : ℝ) w μ →
        μ 1 ((q : ℝ) ^ n) = equivWeight (q : ℝ) w n ∧
          IsExactLawArray (decimRecord (latticeIdxKernel b w) q f n)
            (fun m => latticeApply b (μ 1 ((q : ℝ) ^ n)) f (((q : ℤ) ^ n) • m))) := by
  obtain ⟨C, hC⟩ := hf
  haveI := isProbabilityMeasure_equivWeight (q : ℝ) w n
  have h1 : ∀ m : Zd d, decimRecord (latticeIdxKernel b w) q f n m =
      latticeApply b (equivWeight (q : ℝ) w n) f (((q : ℤ) ^ n) • m) := fun m => by
    rw [decimRecord_eq_mconvE b w hcarr hC,
      latticeApply_eq_mconvE b _ (equivWeight_carried b q w hcarr n) hC]
  refine ⟨h1, fun _ μ hμ => ?_⟩
  have hW := carries_equivWeight hμ n
  exact ⟨hW, fun m => by rw [hW]; exact h1 m⟩

end Pyramids
