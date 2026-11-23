/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Line.DiscreteGaussianPyramid
import Pyramids.LineAppendix.LaplaceAtoms
import Pyramids.LineAppendix.LineExponentData
import Pyramids.LineAppendix.MaternNonCreation

/-!
# `prop:classical-pyramids-approximate-discrete-gaussian`: neither a lattice law nor Pólya

Blueprint: `blueprint/src/parts/A1-line.tex`,
`prop:classical-pyramids-approximate-discrete-gaussian`.
Phase 5, wave 3b. The statement is the skeleton's (`PyramidsSkeleton/ChA1Line.lean`), unchanged.

* **Carried by no lattice**: `prop:discrete-gaussian-pyramid`(3), `discrete_gaussian_pyramid_3`.
* **Not a Pólya frequency density**, by the modulus route rather than the printed one. If
  `μ_t = φ dx` with `φ` a Pólya frequency density, A24 (`cited_A24`, on the imaginary axis) gives
  `L(iω) ψ(iω) = 1` with `L(iω) = μ̂_t(-ω) = e^{-Ψ_t(ω)}`, and the core's `norm_polyaE2_mul_I`
  gives `‖ψ(iω)‖ = exp(γω² + ½∑ⱼ log(1 + aⱼ²ω²))`. So
  `2Ψ_t(ω) = 2γω² + ∑_{aⱼ ≠ 0} log(1 + ω²/ϑⱼ²)`, `ϑⱼ = 1/|aⱼ|`, which by
  `lem:laplace-atoms-admissible`(2) is the exponent of a profile, with the absolutely continuous
  folded Lévy measure `k(x) dx/x`. The folded data `(0, ϖ_t)` of `μ_t`
  (`prop:discrete-gaussian-pyramid`(1)) added to themselves have the exponent `2Ψ_t` too, so by the
  uniqueness of the folded pair (`lem:line-exponent-data`(1)) `2ϖ_t = k(x) dx/x`. But `ϖ_t` has an
  atom of positive mass, and `k(x) dx/x` has none.

The printed route (a complex Frullani integral, the drift, A39(ii)–(iii)) is not needed.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter Complex
open ScaleSpace (SymLevyPair SDProfile profileMeasure polyaE2 norm_polyaE2_mul_I
  profile_integrability_pair)
open scoped Topology ENNReal

/-- **The exponent is Karlin's modulus**: if `μ_t = φ dx` with `φ` a Pólya frequency density,
then `Ψ_t(ω) = γω² + ½∑ log(1 + aⱼ²ω²)` for the parameters of A24. -/
theorem dgExponent_eq_of_polya {q h : ℝ} {w : ℤ → ℝ} {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsDGKernels q h w μ) {t : ℝ} (ht : 0 < t) {φ : ℝ → ℝ}
    (hφ : IsPolyaFrequencyDensity φ)
    (hμφ : μ 0 t = (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (φ x)) :
    ∃ (γ : ℝ) (a : ℕ → ℝ), 0 ≤ γ ∧ Summable (fun j => a j ^ 2) ∧ ∀ ω : ℝ,
      dgExponent q h w t ω = γ * ω ^ 2 + (1 / 2) * ∑' j, Real.log (1 + a j ^ 2 * ω ^ 2) := by
  obtain ⟨γ, δ, a, hγ, ha, -, -, -, hL⟩ := cited_A24 φ hφ
  refine ⟨γ, a, hγ, ha, fun ω => ?_⟩
  have h1 := hL (-ω)
  rw [← charFun_neg_of_polya hφ, ← hμφ, neg_neg, (hμ 0 t le_rfl ht.le).2 ω] at h1
  have h2 := congrArg norm h1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_polyaE2_mul_I ha, norm_one, ← Real.exp_add] at h2
  have h3 := Real.exp_eq_one_iff _ |>.1 h2
  have h0 : dgExponent q h w 0 ω = 0 := by simp [dgExponent]
  rw [h0, sub_zero] at h3
  have e1 : (-ω) ^ 2 = ω ^ 2 := by ring
  simp only [e1] at h3
  linarith

/-- **`prop:classical-pyramids-approximate-discrete-gaussian`.** For weights not all zero, the
kernel `μ_t`, `t > 0`, of the discrete-Gaussian pyramid is carried by no lattice `ξℤ` and is not a
Pólya frequency density. -/
theorem discrete_gaussian_neither {q h : ℝ} (hq : 1 < q) (hh : 0 < h) (w : ℤ → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hwanti : Antitone w) (hwne : ∃ i, w i ≠ 0)
    (hneg : Summable fun i : {i : ℤ // i < 0} => w i * q ^ (2 * (i : ℤ)))
    (hpos : Summable fun i : {i : ℤ // 0 ≤ i} => w i)
    (μ : ℝ → ℝ → Measure ℝ) (hμ : IsDGKernels q h w μ) {t : ℝ} (ht : 0 < t) :
    (∀ ξ : ℝ, 0 < ξ → μ 0 t {x | ¬ ∃ n : ℤ, x = ξ * n} ≠ 0) ∧
      ¬ IsPolyaFrequencyKernel (μ 0 t) := by
  refine ⟨fun ξ hξ => discrete_gaussian_pyramid_3 hq hh w hw0 hwanti hwne hneg hpos μ hμ ht hξ,
    ?_⟩
  rintro ⟨φ, hφ, hμφ⟩
  have hw : IsDGWeights q w := ⟨hw0, hwanti, hwne, hneg, hpos⟩
  obtain ⟨γ, a, hγ, ha, hΨ⟩ := dgExponent_eq_of_polya hμ ht hφ hμφ
  -- `2Ψ_t` in the form of `lem:laplace-atoms-admissible`(2), over the `j` with `aⱼ ≠ 0`
  set ι := {j : ℕ // a j ≠ 0}
  set θ : ι → ℝ := fun j => 1 / |a j| with hθdef
  have hθ : ∀ j : ι, 0 < θ j := fun j => one_div_pos.2 (abs_pos.2 j.2)
  have hθsq : ∀ j : ι, (θ j ^ 2)⁻¹ = a j ^ 2 := fun j => by
    rw [hθdef]; simp only [one_div, inv_pow, inv_inv, sq_abs]
  have hsum : Summable fun j : ι => (θ j ^ 2)⁻¹ := by
    simp_rw [hθsq]
    exact ha.subtype _
  have hform : ∀ ω : ℝ, 2 * dgExponent q h w t ω =
      2 * γ * ω ^ 2 + ∑' j : ι, Real.log (1 + ω ^ 2 / θ j ^ 2) := by
    intro ω
    have e : ∀ j : ι, Real.log (1 + ω ^ 2 / θ j ^ 2) = Real.log (1 + a j ^ 2 * ω ^ 2) := by
      intro j
      rw [div_eq_mul_inv, hθsq, mul_comm]
    simp_rw [e]
    have hsub : ∑' j : ι, Real.log (1 + a j ^ 2 * ω ^ 2) =
        ∑' j, Real.log (1 + a j ^ 2 * ω ^ 2) := by
      refine tsum_subtype_eq_of_support_subset (f := fun j => Real.log (1 + a j ^ 2 * ω ^ 2))
        (s := {j | a j ≠ 0}) ?_
      intro j hj
      by_contra h0
      simp only [ne_eq, mem_setOf_eq, not_not] at h0
      simp [h0] at hj
    rw [hsub, hΨ]
    ring
  obtain ⟨P, -, -, hP⟩ := (laplace_atoms_admissible_2 (by positivity : 0 ≤ 2 * γ) θ hθ hsum
    (fun ω => 2 * dgExponent q h w t ω) hform).2.2.2.1
  obtain ⟨Q, -, hQν, hQ⟩ := profile_integrability_pair P
  -- the doubled folded data of `μ_t`
  set D := SymLevyPair_add (dgPair hq hh hw t) (dgPair hq hh hw t)
  have hD : HasExpData (fun ω => 2 * dgExponent q h w t ω) D := fun ω => by
    simp only [D, SymLevyPair_add_exponent, dgPair_exponent]
    ring
  have hQ' : HasExpData (fun ω => 2 * dgExponent q h w t ω) Q := fun ω => (hP ω).trans (hQ ω)
  have hν := (line_exponent_data_1_unique _ Q D hQ' hD).2
  obtain ⟨j, hj⟩ := dgAtomWeight_pos hw t
  have h1 := congrArg (fun m : Measure ℝ => m {h * q ^ j}) hν
  simp only [hQν, profileMeasure_singleton, D, SymLevyPair_add, dgPair_ν, Measure.coe_add,
    Pi.add_apply, dgLevyMeasure_atom hq hh w ht] at h1
  have hpos' : (0 : ℝ≥0∞) < ENNReal.ofReal (dgAtomWeight q w t j) := ENNReal.ofReal_pos.2 hj
  have hz : ENNReal.ofReal (dgAtomWeight q w t j) + ENNReal.ofReal (dgAtomWeight q w t j) = 0 :=
    h1.symm
  exact hpos'.ne' (add_eq_zero.1 hz).1

end Pyramids
