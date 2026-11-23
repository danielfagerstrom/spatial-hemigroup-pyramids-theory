/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Cited.A23
import Pyramids.LineAppendix.LaplaceAtoms
import Pyramids.LineAppendix.LineExponentData
import Pyramids.LineAppendix.MaternLine

/-!
# `prop:ladder-non-creation-line`: ladder non-creation on the line

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:ladder-non-creation-line`. Phase 5, wave 3b.
The statements are the skeleton's (`PyramidsSkeleton/ChA1Line.lean`), unchanged.

**The rearrangement, by multiplicities in `[0,∞]`.** For `F = aω² + ∑ᵢ log(1 + ω²/ϑᵢ²)`, the series
`F(q·)` lists the atoms `ϑᵢ/q`, and `mult_{ϑ/q}(ϑ) = mult(qϑ)`. Every sum of a function
`g : ℝ → [0,∞]` over a family is the sum over the values weighted by the multiplicities
(`tsum_comp_eq_tsum_atomMult`, through the fibres of the family). The new atoms are indexed by
`J = Σ_{ϑ ∈ S} {k : ℕ // k < m(ϑ)}`, `m(ϑ) = mult(qϑ) - mult(ϑ)` in `ℕ∞` and `S` the countable
set of the `ϑᵢ/q`; `{k // k < m}` has `m` elements, `⊤` included, so no finiteness of the
fibres is needed, and `mult(qϑ) = mult(ϑ) + m(ϑ)` is `add_tsub_cancel_of_le`. Then
`∑ g(ϑᵢ/q) = ∑ g(ϑᵢ) + ∑_J g(ϑ'ⱼ)` for every such `g` (`tsum_rearrange`), and for nonnegative real
`g` with `∑ g(ϑᵢ/q) < ∞` the same in `ℝ`, both sums on the right converging (`rearrange_real`).
At `g(ϑ) = ϑ⁻²` it gives `∑_J ϑ'ⱼ⁻² < ∞`; at `g(ϑ) = log(1 + ω²/ϑ²)` the form
`G(ω) = F(qω) - F(ω) = a(q² - 1)ω² + ∑_J log(1 + ω²/ϑ'ⱼ²)`; and `G ≢ 0`: if `a = 0` the family is
not empty (`F ≢ 0`), so `∑ϑᵢ⁻² ∈ (0,∞)`, and `J = ∅` would give `q²∑ϑᵢ⁻² = ∑ϑᵢ⁻²`.

**The laws** exist by `lem:line-exponent-data`(1)–(2), from the pairs that
`lem:laplace-atoms-admissible`(2) gives `F` and `G`. **(1)** is A22's determinant clause at `G`,
for the family of steps. **(2)**: `u(qs) = μ_{s,qs} * u(s)` at every point (the cascade and the
pointwise associativity of convolution against a bounded measurable function, `mconv_mconv`);
`u(s)` is the primitive of the integrable `μ_s * f'` (`mconv_primitive`); A23 (proved from A22)
for the family of steps at scale `s` gives the counts, and `∂ₓu(s) = μ_s * f'` almost everywhere
(`deriv_mconv_primitive_ae`) makes the right side the count of `∂ₓu(s)`.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (IsAdmissibleExponent mconv mconv_apply integrable_mconv SymLevyPair SDProfile
  profile_integrability_pair)
open scoped Topology ENNReal

/-! ## Multiplicities -/

/-- **A sum over a family is the sum over its values, weighted by the multiplicities.** -/
theorem tsum_comp_eq_tsum_atomMult {κ : Type*} (f : κ → ℝ) (g : ℝ → ℝ≥0∞) :
    ∑' i, g (f i) = ∑' x : ℝ, (atomMult f x : ℝ≥0∞) * g x := by
  rw [← (Equiv.sigmaFiberEquiv f).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun x => ?_
  have h : ∀ i : {i // f i = x}, g (f ((Equiv.sigmaFiberEquiv f) ⟨x, i⟩)) = g x := fun i => by
    simp [Equiv.sigmaFiberEquiv, i.2]
  rw [tsum_congr h, ENNReal.tsum_const, atomMult]

/-- `{k : ℕ // k < m}` has `m` elements, for every `m ∈ ℕ∞`. -/
theorem enatCard_lt (m : ℕ∞) : ENat.card {k : ℕ // (k : ℕ∞) < m} = m := by
  induction m using ENat.recTopCoe with
  | top =>
    rw [ENat.card_congr (Equiv.subtypeUnivEquiv fun k => ENat.coe_lt_top k)]
    exact ENat.card_eq_top_of_infinite
  | coe n =>
    have e : {k : ℕ // (k : ℕ∞) < n} ≃ Fin n :=
      (Equiv.subtypeEquivRight fun k => by exact_mod_cast Iff.rfl).trans Fin.equivSubtype.symm
    rw [ENat.card_congr e, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

section Rearrange

variable {ι : Type*} {q : ℝ} (θ : ι → ℝ)

/-- The new multiplicity `m(ϑ) = mult(qϑ) - mult(ϑ)`. -/
noncomputable def newMult (q : ℝ) (ϑ : ℝ) : ℕ∞ := atomMult θ (q * ϑ) - atomMult θ ϑ

/-- The atoms of `F(q·)`. -/
def atomsDivQ (q : ℝ) : Set ℝ := range fun i => θ i / q

/-- **The index of the new atoms**: `J = Σ_{ϑ ∈ S} {k : ℕ // k < m(ϑ)}`. -/
def NewAtomIdx (q : ℝ) : Type _ := Σ ϑ : atomsDivQ θ q, {k : ℕ // (k : ℕ∞) < newMult θ q ϑ}

/-- The new atoms. -/
def newAtom (q : ℝ) (j : NewAtomIdx θ q) : ℝ := (j.1 : ℝ)

instance [Countable ι] : Countable (NewAtomIdx θ q) := by
  haveI : Countable (atomsDivQ θ q) := (countable_range _).to_subtype
  unfold NewAtomIdx
  infer_instance

theorem atomMult_div (hq : q ≠ 0) (ϑ : ℝ) :
    atomMult (fun i => θ i / q) ϑ = atomMult θ (q * ϑ) := by
  unfold atomMult
  refine ENat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
  constructor
  · intro h
    change θ i / q = ϑ at h
    rw [← h]
    field_simp
  · intro h
    change θ i / q = ϑ
    rw [h]
    field_simp

theorem atomMult_eq_zero_of_nonpos (hθ : ∀ i, 0 < θ i) {ϑ : ℝ} (hϑ : ϑ ≤ 0) :
    atomMult θ ϑ = 0 := by
  unfold atomMult
  rw [ENat.card_eq_zero_iff_empty]
  exact ⟨fun ⟨i, hi⟩ => by have := hθ i; linarith⟩

theorem atomMult_le_mul (hθ : ∀ i, 0 < θ i)
    (hmult : ∀ ϑ : ℝ, 0 < ϑ → atomMult θ ϑ ≤ atomMult θ (q * ϑ)) (ϑ : ℝ) :
    atomMult θ ϑ ≤ atomMult θ (q * ϑ) := by
  rcases le_or_gt ϑ 0 with h | h
  · rw [atomMult_eq_zero_of_nonpos θ hθ h]; exact zero_le
  · exact hmult ϑ h

theorem tsum_newAtom (hq : q ≠ 0) (g : ℝ → ℝ≥0∞) :
    ∑' j : NewAtomIdx θ q, g (newAtom θ q j) = ∑' ϑ : ℝ, (newMult θ q ϑ : ℝ≥0∞) * g ϑ := by
  unfold NewAtomIdx newAtom
  rw [ENNReal.tsum_sigma']
  have h : ∀ ϑ : atomsDivQ θ q,
      ∑' k : {k : ℕ // (k : ℕ∞) < newMult θ q ϑ}, g ϑ = (newMult θ q ϑ : ℝ≥0∞) * g ϑ := by
    intro ϑ
    rw [ENNReal.tsum_const, enatCard_lt]
  rw [tsum_congr h]
  refine tsum_subtype_eq_of_support_subset (f := fun ϑ => (newMult θ q ϑ : ℝ≥0∞) * g ϑ)
    fun ϑ hϑ => ?_
  have hm : newMult θ q ϑ ≠ 0 := by
    intro h0
    simp [h0] at hϑ
  have hpos : atomMult θ (q * ϑ) ≠ 0 := by
    intro h0
    apply hm
    simp [newMult, h0]
  unfold atomMult at hpos
  rw [Ne, ENat.card_eq_zero_iff_empty, not_isEmpty_iff] at hpos
  obtain ⟨i, hi⟩ := hpos
  refine ⟨i, ?_⟩
  simp only
  rw [hi]
  field_simp

/-- **The rearrangement in `[0,∞]`**: `∑ g(ϑᵢ/q) = ∑ g(ϑᵢ) + ∑_J g(ϑ'ⱼ)`. -/
theorem tsum_rearrange (hq : 1 < q) (hθ : ∀ i, 0 < θ i)
    (hmult : ∀ ϑ : ℝ, 0 < ϑ → atomMult θ ϑ ≤ atomMult θ (q * ϑ)) (g : ℝ → ℝ≥0∞) :
    ∑' i, g (θ i / q) = ∑' i, g (θ i) + ∑' j : NewAtomIdx θ q, g (newAtom θ q j) := by
  have hq0 : q ≠ 0 := by positivity
  rw [tsum_comp_eq_tsum_atomMult (fun i => θ i / q) g, tsum_comp_eq_tsum_atomMult θ g,
    tsum_newAtom θ hq0, ← ENNReal.tsum_add]
  refine tsum_congr fun ϑ => ?_
  rw [atomMult_div θ hq0, ← add_mul, ← ENat.toENNReal_add, newMult,
    add_tsub_cancel_of_le (atomMult_le_mul θ hθ hmult ϑ)]

/-- **The rearrangement in `ℝ`**, for a nonnegative `g` summable over the atoms of `F(q·)`. -/
theorem rearrange_real (hq : 1 < q) (hθ : ∀ i, 0 < θ i)
    (hmult : ∀ ϑ : ℝ, 0 < ϑ → atomMult θ ϑ ≤ atomMult θ (q * ϑ)) {g : ℝ → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hs : Summable fun i => g (θ i / q)) :
    Summable (fun i => g (θ i)) ∧ Summable (fun j : NewAtomIdx θ q => g (newAtom θ q j)) ∧
      ∑' i, g (θ i / q) = ∑' i, g (θ i) + ∑' j : NewAtomIdx θ q, g (newAtom θ q j) := by
  have hE := tsum_rearrange θ hq hθ hmult (fun x => ENNReal.ofReal (g x))
  have hA : ∑' i, ENNReal.ofReal (g (θ i / q)) = ENNReal.ofReal (∑' i, g (θ i / q)) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun i => hg _) hs).symm
  have hfin : ∑' i, ENNReal.ofReal (g (θ i / q)) ≠ ⊤ := by rw [hA]; exact ENNReal.ofReal_ne_top
  have hB : ∑' i, ENNReal.ofReal (g (θ i)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (by rw [hE]; exact le_self_add)
  have hC : ∑' j : NewAtomIdx θ q, ENNReal.ofReal (g (newAtom θ q j)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (by rw [hE]; exact le_add_self)
  have hsB : Summable fun i => g (θ i) :=
    (ENNReal.summable_toReal hB).congr fun i => ENNReal.toReal_ofReal (hg _)
  have hsC : Summable fun j : NewAtomIdx θ q => g (newAtom θ q j) :=
    (ENNReal.summable_toReal hC).congr fun j => ENNReal.toReal_ofReal (hg _)
  refine ⟨hsB, hsC, ?_⟩
  rw [hA, ← ENNReal.ofReal_tsum_of_nonneg (fun i => hg _) hsB,
    ← ENNReal.ofReal_tsum_of_nonneg (fun j => hg _) hsC,
    ← ENNReal.ofReal_add (tsum_nonneg fun i => hg _) (tsum_nonneg fun j => hg _)] at hE
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun i => hg _)
    (add_nonneg (tsum_nonneg fun i => hg _) (tsum_nonneg fun j => hg _))).1 hE

end Rearrange

/-! ## The exponent of the step -/

/-- **The exponent of the octave step**: `G(ω) = F(qω) - F(ω)` has Gaussian coefficient
`a(q² - 1)` and the atoms `ϑ'ⱼ`, with `∑ ϑ'ⱼ⁻² < ∞`, and `G ≢ 0`. -/
theorem step_exponent_form {ι : Type*} [Countable ι] {q : ℝ} (hq : 1 < q) {a : ℝ}
    (ha : 0 ≤ a) (θ : ι → ℝ) (hθ : ∀ i, 0 < θ i) (hsum : Summable fun i => (θ i ^ 2)⁻¹)
    (F : ℝ → ℝ) (hF : ∀ ω : ℝ, F ω = a * ω ^ 2 + ∑' i, Real.log (1 + ω ^ 2 / θ i ^ 2))
    (hFne : ∃ ω : ℝ, F ω ≠ 0) (hmult : ∀ ϑ : ℝ, 0 < ϑ → atomMult θ ϑ ≤ atomMult θ (q * ϑ)) :
    (∀ j, 0 < newAtom θ q j) ∧ Summable (fun j => (newAtom θ q j ^ 2)⁻¹) ∧
      (∀ ω : ℝ, F (q * ω) - F ω =
        a * (q ^ 2 - 1) * ω ^ 2 + ∑' j, Real.log (1 + ω ^ 2 / newAtom θ q j ^ 2)) ∧
      ∃ ω : ℝ, F (q * ω) - F ω ≠ 0 := by
  have hq0 : 0 < q := by linarith
  have hθq : ∀ i, 0 < θ i / q := fun i => div_pos (hθ i) hq0
  have hpos : ∀ j, 0 < newAtom θ q j := by
    rintro ⟨⟨ϑ, i, rfl⟩, k⟩
    exact hθq i
  -- the inverse squares
  have hinv : ∀ i, ((θ i / q) ^ 2)⁻¹ = q ^ 2 * (θ i ^ 2)⁻¹ := fun i => by
    have := (hθ i).ne'
    field_simp
  have hsq : Summable fun i => ((θ i / q) ^ 2)⁻¹ :=
    (hsum.mul_left (q ^ 2)).congr fun i => (hinv i).symm
  obtain ⟨-, hsJ, hidJ⟩ := rearrange_real θ hq hθ hmult (g := fun x => (x ^ 2)⁻¹)
    (fun x => inv_nonneg.2 (sq_nonneg x)) hsq
  have hform : ∀ ω : ℝ, F (q * ω) - F ω =
      a * (q ^ 2 - 1) * ω ^ 2 + ∑' j, Real.log (1 + ω ^ 2 / newAtom θ q j ^ 2) := by
    intro ω
    have hlogq := (laplace_atoms_admissible_2 (ι := ι) ha (fun i => θ i / q) hθq hsq
      (fun ω => a * ω ^ 2 + ∑' i, Real.log (1 + ω ^ 2 / (θ i / q) ^ 2)) fun _ => rfl).1 ω
    obtain ⟨-, -, hid⟩ := rearrange_real θ hq hθ hmult
      (g := fun x => Real.log (1 + ω ^ 2 / x ^ 2))
      (fun x => Real.log_nonneg (le_add_of_nonneg_right (div_nonneg (sq_nonneg ω) (sq_nonneg x))))
      hlogq
    have e : ∀ i, Real.log (1 + (q * ω) ^ 2 / θ i ^ 2) =
        Real.log (1 + ω ^ 2 / (θ i / q) ^ 2) := fun i => by
      have := (hθ i).ne'
      congr 2
      field_simp
    rw [hF, hF, tsum_congr e, hid]
    ring
  refine ⟨hpos, hsJ, hform, ?_⟩
  -- `G ≢ 0`
  have hadm := laplace_atoms_admissible_2 (ι := NewAtomIdx θ q)
    (mul_nonneg ha (by nlinarith : (0 : ℝ) ≤ q ^ 2 - 1)) (newAtom θ q) hpos hsJ
    (fun ω => F (q * ω) - F ω) hform
  refine hadm.2.2.2.2.2.2.2 ?_
  rcases ha.lt_or_eq with ha' | ha'
  · left
    have : 0 < q ^ 2 - 1 := by nlinarith
    positivity
  · right
    have hne := (laplace_atoms_admissible_2 ha θ hθ hsum F hF).2.2.2.2.2.2.1 hFne
    have hι : Nonempty ι := hne.resolve_left (by rw [← ha']; exact fun h => h rfl)
    by_contra hJ
    rw [not_nonempty_iff] at hJ
    have h0 : ∑' j : NewAtomIdx θ q, (newAtom θ q j ^ 2)⁻¹ = 0 := by
      haveI := hJ
      exact tsum_empty
    rw [h0, add_zero] at hidJ
    obtain ⟨i₀⟩ := hι
    have hT : 0 < ∑' i, (θ i ^ 2)⁻¹ :=
      hsum.tsum_pos (fun i => inv_nonneg.2 (sq_nonneg _)) i₀
        (inv_pos.2 (pow_pos (hθ i₀) 2))
    rw [tsum_congr hinv, tsum_mul_left] at hidJ
    have : q ^ 2 = 1 := by
      have h1 := mul_right_cancel₀ hT.ne' (hidJ.trans (one_mul _).symm)
      exact h1
    nlinarith

/-! ## Laws with given exponents -/

/-- For an exponent with a folded pair, laws with the transforms `e^{-H(s·)}`, `s > 0`, exist. -/
theorem exists_scaled_laws {H : ℝ → ℝ} {Q : SymLevyPair} (hH : HasExpData H Q) :
    ∃ μ : ℝ → Measure ℝ, ∀ s : ℝ, 0 < s → IsProbabilityMeasure (μ s) ∧
      ∀ ω : ℝ, charFun (μ s) ω = ((Real.exp (-H (s * ω)) : ℝ) : ℂ) := by
  have h : ∀ s : ℝ, 0 < s → ∃ m : Measure ℝ, IsProbabilityMeasure m ∧
      ∀ ω : ℝ, charFun m ω = ((Real.exp (-H (s * ω)) : ℝ) : ℂ) := by
    intro s hs
    obtain ⟨Qs, -, -, hQs⟩ := line_exponent_data_2 H Q hH hs
    obtain ⟨m, ⟨hm1, -, -, hm2⟩, -⟩ := line_exponent_data_1 _ ⟨Qs, hQs⟩
    exact ⟨m, hm1, hm2⟩
  choose! μ hμ using h
  exact ⟨μ, hμ⟩

/-- An exponent of the form of `lem:laplace-atoms-admissible`(2) has a folded pair. -/
theorem exists_pair_of_form {ι : Type*} [Countable ι] {a : ℝ} (ha : 0 ≤ a) (θ : ι → ℝ)
    (hθ : ∀ i, 0 < θ i) (hsum : Summable fun i => (θ i ^ 2)⁻¹) (F : ℝ → ℝ)
    (hF : ∀ ω : ℝ, F ω = a * ω ^ 2 + ∑' i, Real.log (1 + ω ^ 2 / θ i ^ 2)) :
    IsAdmissibleExponent F ∧ ∃ Q : SymLevyPair, HasExpData F Q := by
  obtain ⟨P, -, -, hP⟩ := (laplace_atoms_admissible_2 ha θ hθ hsum F hF).2.2.2.1
  obtain ⟨Q, -, -, hQ⟩ := profile_integrability_pair P
  exact ⟨⟨P, hP⟩, Q, fun ω => (hP ω).trans (hQ ω)⟩

/-! ## Convolution against a bounded measurable function, pointwise -/

/-- **`ν * (μ * φ) = (μ ∗ ν) * φ` at every point**, for finite laws on `ℝ` and a bounded
measurable `φ`. -/
theorem mconv_mconv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {φ : ℝ → ℝ}
    (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (x : ℝ) :
    mconv ν (mconv μ φ) x = mconv (μ ∗ ν) φ x := by
  have hadd : Measurable fun p : ℝ × ℝ => p.1 + p.2 := measurable_fst.add measurable_snd
  have hm : Measurable fun z : ℝ => φ (x - z) := hφ.comp (measurable_const.sub measurable_id)
  have hint : Integrable (fun p : ℝ × ℝ => φ (x - (p.1 + p.2))) (μ.prod ν) :=
    Integrable.of_bound (hm.comp hadd).aestronglyMeasurable C
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC _)
  simp only [mconv_apply]
  rw [Measure.conv, integral_map hadd.aemeasurable hm.aestronglyMeasurable,
    integral_prod_symm _ hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  congr 1
  ring

/-! ## The node -/

/-- **`prop:ladder-non-creation-line`.** For `F = aω² + ∑ log(1 + ω²/ϑᵢ²) ≢ 0` with
`mult(qϑ) ≥ mult(ϑ)`: the laws `μ_s`, `μ_{s,qs}` exist, `μ_{qs} = μ_{s,qs} * μ_s`; (1) every
`μ_{s,qs}` is a Pólya frequency density; (2) for `f` the primitive of an integrable `f'`,
`u(qs) = μ_{qs} * f` crosses each level, and changes monotonicity, no more often than
`u(s) = μ_s * f`. -/
theorem ladder_non_creation_line {ι : Type*} [Countable ι] {q : ℝ} (hq : 1 < q) {a : ℝ}
    (ha : 0 ≤ a) (θ : ι → ℝ) (hθ : ∀ i, 0 < θ i) (hsum : Summable fun i => (θ i ^ 2)⁻¹)
    (F : ℝ → ℝ) (hF : ∀ ω : ℝ, F ω = a * ω ^ 2 + ∑' i, Real.log (1 + ω ^ 2 / θ i ^ 2))
    (hFne : ∃ ω : ℝ, F ω ≠ 0) (hmult : ∀ ϑ : ℝ, 0 < ϑ → atomMult θ ϑ ≤ atomMult θ (q * ϑ)) :
    (∃ μ1 : ℝ → Measure ℝ, ∀ s : ℝ, 0 < s → IsProbabilityMeasure (μ1 s) ∧
        ∀ ω : ℝ, charFun (μ1 s) ω = ((Real.exp (-F (s * ω)) : ℝ) : ℂ)) ∧
      (∃ step : ℝ → Measure ℝ, ∀ s : ℝ, 0 < s → IsProbabilityMeasure (step s) ∧
        ∀ ω : ℝ, charFun (step s) ω = ((Real.exp (-(F (q * s * ω) - F (s * ω))) : ℝ) : ℂ)) ∧
      ∀ μ1 step : ℝ → Measure ℝ,
        (∀ s : ℝ, 0 < s → IsProbabilityMeasure (μ1 s) ∧
          ∀ ω : ℝ, charFun (μ1 s) ω = ((Real.exp (-F (s * ω)) : ℝ) : ℂ)) →
        (∀ s : ℝ, 0 < s → IsProbabilityMeasure (step s) ∧
          ∀ ω : ℝ, charFun (step s) ω = ((Real.exp (-(F (q * s * ω) - F (s * ω))) : ℝ) : ℂ)) →
        (∀ s : ℝ, 0 < s → μ1 (q * s) = step s ∗ μ1 s) ∧
        (∀ s : ℝ, 0 < s → IsPolyaFrequencyKernel (step s)) ∧
        ∀ f f' : ℝ → ℝ, Integrable f' → (∃ C : ℝ, ∀ x, f x = C + ∫ y in (0 : ℝ)..x, f' y) →
          ∀ s : ℝ, 0 < s →
            (∀ α : ℝ, essSignChanges (fun x => mconv (μ1 (q * s)) f x - α) ≤
              essSignChanges (fun x => mconv (μ1 s) f x - α)) ∧
            essSignChanges (deriv (mconv (μ1 (q * s)) f)) ≤
              essSignChanges (deriv (mconv (μ1 s) f)) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hpos, hsJ, hform, hGne⟩ := step_exponent_form hq ha θ hθ hsum F hF hFne hmult
  set G : ℝ → ℝ := fun ω => F (q * ω) - F ω with hG
  have hGa : 0 ≤ a * (q ^ 2 - 1) := mul_nonneg ha (by nlinarith)
  obtain ⟨hFadm, QF, hQF⟩ := exists_pair_of_form ha θ hθ hsum F hF
  obtain ⟨hGadm, QG, hQG⟩ := exists_pair_of_form hGa (newAtom θ q) hpos hsJ G hform
  -- the step's transform is `e^{-G(s·)}`
  have hGs : ∀ s ω : ℝ, F (q * s * ω) - F (s * ω) = G (s * ω) := fun s ω => by
    simp only [hG, mul_assoc]
  refine ⟨exists_scaled_laws hQF, ?_, fun μ1 step hμ1 hstep => ?_⟩
  · obtain ⟨st, hst⟩ := exists_scaled_laws hQG
    exact ⟨st, fun s hs => ⟨(hst s hs).1, fun ω => by rw [hGs]; exact (hst s hs).2 ω⟩⟩
  have hstepG : ∀ t : ℝ, 0 < t → ∀ ω : ℝ,
      charFun (step t) ω = ((Real.exp (-G (t * ω)) : ℝ) : ℂ) := fun t ht ω => by
    rw [(hstep t ht).2 ω, hGs]
  have hcasc : ∀ s : ℝ, 0 < s → μ1 (q * s) = step s ∗ μ1 s := by
    intro s hs
    haveI := (hμ1 s hs).1
    haveI := (hstep s hs).1
    haveI := (hμ1 (q * s) (mul_pos hq0 hs)).1
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    rw [charFun_conv, (hμ1 _ (mul_pos hq0 hs)).2 ω, (hstep s hs).2 ω, (hμ1 s hs).2 ω,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  refine ⟨hcasc, fun s hs => cited_A22_polya G hGadm hGne _ hGa (newAtom θ q) hpos hsJ hform
    step (fun t ht => (hstep t ht).1) hstepG hs, ?_⟩
  intro f f' hf' hprim s hs
  haveI := (hμ1 s hs).1
  haveI := (hstep s hs).1
  obtain ⟨C, hC⟩ := hprim
  have hfeq : f = fun x => C + ∫ y in (0 : ℝ)..x, f' y := funext hC
  have hfc : Continuous f := hfeq ▸ continuous_primitive' hf' C
  have hM : ∀ x, |f x| ≤ |C| + ∫ y, ‖f' y‖ := fun x => hfeq ▸ abs_primitive_le hf' C x
  -- `u(qs) = μ_{s,qs} * u(s)`
  have hu : mconv (μ1 (q * s)) f = mconv (step s) (mconv (μ1 s) f) := by
    funext x
    rw [hcasc s hs, Measure.conv_comm, mconv_mconv _ _ hfc.measurable hM]
  -- `u(s)` is the primitive of `μ_s * f'`
  have hint' : Integrable (mconv (μ1 s) f') := integrable_mconv _ hf'.aestronglyMeasurable hf'
  have hprim' : ∃ C' : ℝ, ∀ x, mconv (μ1 s) f x = C' + ∫ y in (0 : ℝ)..x, mconv (μ1 s) f' y :=
    ⟨mconv (μ1 s) f 0, fun x => by rw [hfeq]; exact mconv_primitive _ hf' C x⟩
  obtain ⟨h1, h2⟩ := cited_A23 G hGadm _ hGa (newAtom θ q) hpos hsJ hform step
    (fun t ht => (hstep t ht).1) hstepG (mconv (μ1 s) f) (mconv (μ1 s) f') hint' hprim' hs
  refine ⟨fun α => ?_, ?_⟩
  · rw [hu]; exact h1 α
  · rw [hu, essSignChanges_congr (g := deriv (mconv (μ1 s) f)) (g' := mconv (μ1 s) f')]
    · exact h2
    · rw [hfeq]; exact deriv_mconv_primitive_ae _ hf' C

/-! ## The Matérn case -/

open Classical in
/-- The fibre of an injective family has `1` element on its range and none off it. -/
theorem atomMult_of_injective {κ : Type*} {f : κ → ℝ} (hf : Function.Injective f) (x : ℝ) :
    atomMult f x = if x ∈ range f then 1 else 0 := by
  unfold atomMult
  split_ifs with h
  · obtain ⟨i, rfl⟩ := h
    haveI : Unique {j // f j = f i} :=
      ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext (hf j.2)⟩
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_unique]
    rfl
  · rw [ENat.card_eq_zero_iff_empty]
    exact ⟨fun ⟨j, hj⟩ => h ⟨j, hj⟩⟩

/-- **`prop:ladder-non-creation-line`, the Matérn case.** `F_q` is the case `a = 0`,
`ϑᵢ = qⁱ/c`, where `mult(qϑ) - mult(ϑ)` is `1` at `ϑ = 1/c` and `0` elsewhere. -/
theorem ladder_non_creation_line_matern {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    (∀ ω : ℝ, maternExponent q c ω = ∑' i : ℕ, Real.log (1 + ω ^ 2 / (q ^ (i + 1) / c) ^ 2)) ∧
      ∀ ϑ : ℝ, 0 < ϑ → atomMult (fun i : ℕ => q ^ (i + 1) / c) (q * ϑ) =
        atomMult (fun i : ℕ => q ^ (i + 1) / c) ϑ + (if ϑ = 1 / c then 1 else 0) := by
  have hq0 : 0 < q := by linarith
  refine ⟨fun ω => by rw [maternExponent_eq_atoms hq hc, zero_mul, zero_add]; rfl,
    fun ϑ _ => ?_⟩
  have hinj : Function.Injective fun i : ℕ => q ^ (i + 1) / c := by
    intro i j hij
    have h1 : q ^ (i + 1) = q ^ (j + 1) := by
      simpa [div_left_inj' hc.ne'] using hij
    have := pow_right_injective₀ hq0 hq.ne' h1
    omega
  rw [atomMult_of_injective hinj, atomMult_of_injective hinj]
  have hnot1 : (1 / c) ∉ range fun i : ℕ => q ^ (i + 1) / c := by
    rintro ⟨i, hi⟩
    have : q ^ (i + 1) = 1 := by
      field_simp at hi
      linarith
    have h2 : 1 < q ^ (i + 1) := one_lt_pow₀ hq (Nat.succ_ne_zero i)
    linarith
  by_cases h : ϑ = 1 / c
  · subst h
    have hmem : q * (1 / c) ∈ range fun i : ℕ => q ^ (i + 1) / c := ⟨0, by simp [div_eq_mul_inv]⟩
    rw [if_pos hmem, if_neg hnot1, if_pos rfl, zero_add]
  · rw [if_neg h, add_zero]
    have hiff : (q * ϑ ∈ range fun i : ℕ => q ^ (i + 1) / c) ↔
        ϑ ∈ range fun i : ℕ => q ^ (i + 1) / c := by
      constructor
      · rintro ⟨i, hi⟩
        cases i with
        | zero =>
          exfalso
          apply h
          have : q * ϑ = q / c := by rw [← hi]; simp
          field_simp at this ⊢
          nlinarith
        | succ k =>
          refine ⟨k, ?_⟩
          have : q * ϑ = q * (q ^ (k + 1) / c) := by rw [← hi]; ring
          exact (mul_left_cancel₀ hq0.ne' this).symm
      · rintro ⟨i, hi⟩
        exact ⟨i + 1, by rw [← hi]; ring⟩
    by_cases hm : ϑ ∈ range fun i : ℕ => q ^ (i + 1) / c
    · rw [if_pos (hiff.2 hm), if_pos hm]
    · rw [if_neg (fun h' => hm (hiff.1 h')), if_neg hm]

end Pyramids
