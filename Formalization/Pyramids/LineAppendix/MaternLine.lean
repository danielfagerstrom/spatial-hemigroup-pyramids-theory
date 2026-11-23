/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Matern
import Pyramids.LineAppendix.LaplaceAtoms
import Pyramids.LineAppendix.PhaseEntropy
import Pyramids.LineAppendix.PhaseEntropySelection
import Pyramids.Cited.A4
import Pyramids.Line.LineAxiomsKernels
import Pyramids.Line.LatticeLine
import Pyramids.RecursionHelmholtz

/-!
# `thm:matern-pyramid-line`, clauses (1)–(3): the Matérn pyramid on the line

Blueprint: `blueprint/src/parts/A1-line.tex`, `thm:matern-pyramid-line`. Phase 5, wave 3e. The
declarations moved here from `PyramidsSkeleton.ChA1Line` with their statements unchanged; clause
(4) is `MaternLineLimit`, and the realization of (3) is `prop:recursion-helmholtz`(1)
(`recursion_line_transforms`, `recursion_line_passes`, `Pyramids.RecursionHelmholtz`).

* **The series.** `F_q(r) = ∑_{i ≥ 0} log(1 + r²/ϑᵢ²)` with the Laplace atoms
  `ϑᵢ = q^{i+1}/c`, `∑ ϑᵢ⁻² < ∞`; `lem:laplace-atoms-admissible`(2) gives the convergence, the
  bound `0 ≤ F_q(r) ≤ (∑ ϑᵢ⁻²) r²`, the profile `2∑ e^{-ϑᵢx}`, its complete monotonicity and
  `F_q ≢ 0`. The display (A.e7) is `HasSum.rexp` of the series. The telescoping
  `F_q(qr) = log(1 + c²r²) + F_q(r)` splits off the first term (`tsum_eq_zero_add`).
* **(1), the family.** The kernels of `(χ, F) = (id, F_q)` are built from A39(iii) as in
  `thm:cited-A4`'s construction (`exists_isGaugeKernels`), and a given Matérn pyramid, totalised
  by `δ₀`, has the kernels of `(id, F_q)`: so it is the kernel family of the `CascadeFamily` built
  on it (`IsGaugeKernels.cascadeFamily`), whose `S_λ = χ⁻¹(λχ(·))` is `t ↦ λt`. The octave step has
  the transform `(1 + c²t²ω²)⁻¹`, that of `L_{ct}` (`fourierLine_laplace`).
* **(2).** A Matérn pyramid is a `q^ℤ`-covariant family (`lem:line-axioms-kernels`(1) and a
  transform computation) whose knot kernel has the exponent `F_q`, so it is a member of the orbit,
  and it is the similarity member (`Ψ_t(ω) = F_q(tω)`). The ladder has no Gaussian part: its step
  `log(1 + c²ω²)` is the exponent of one Laplace atom, with `a = 0`. Then
  `thm:phase-entropy-selection`(1) and (3). Directly: `D = F̃ - F_q` has `D(qω) = D(ω)` and
  `D(0+) = 0`, and `D(ω) = D(q^{-n}ω) → 0`.
* **(3).** The series of `t`-derivatives is dominated on `(0, 2t)` by
  `4c²tω²q^{-2(i+1)}` (`hasDerivAt_tsum_of_isPreconnected`); its sum is `-h_t(ω)`. The asymptotics
  are uniform: for `X = ct|ω| ≥ 1` and `N = ⌊log_q X⌋`, the first `N` terms differ from `1` by at
  most `∑_j q^{-2j}` in total and the others sum to at most the same, so
  `|-(t/2)h_t(ω) - log_q X| ≤ 1 + (1 - q^{-2})⁻¹`.

**What it reaches.** The display, (2) directly and (3) print Lean core. (1) prints A39's
`levy_khintchine_converse` (the kernels, from `line_exponent_data_1`); (2) prints A39's three names
and `khintchine_null_array` (A41), through `thm:phase-entropy-selection` and
`thm:surface-measure`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X CascadeFamily IsKernelFamily SymLevyPair SDProfile laplaceLaw
  ConstructionData IsSymLevyExponent)
open scoped Topology ENNReal

/-! ## The series `F_q` -/

variable {q c : ℝ}

/-- The Laplace atoms of `F_q`: `ϑᵢ = q^{i+1}/c`, `i ≥ 0`. -/
noncomputable def maternTheta (q c : ℝ) (i : ℕ) : ℝ := q ^ (i + 1) / c

theorem maternTheta_pos (hq : 1 < q) (hc : 0 < c) (i : ℕ) : 0 < maternTheta q c i :=
  div_pos (pow_pos (by linarith) _) hc

/-- `c² r²/q^{2(i+1)} = r²/ϑᵢ²`. -/
theorem maternTerm_eq (hq : 1 < q) (hc : 0 < c) (r : ℝ) (i : ℕ) :
    c ^ 2 * r ^ 2 / q ^ (2 * (i + 1)) = r ^ 2 / maternTheta q c i ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hqi : 0 < q ^ (i + 1) := pow_pos hq0 _
  rw [maternTheta, show 2 * (i + 1) = (i + 1) * 2 by ring, pow_mul, div_pow]
  field_simp

theorem summable_maternTheta (hq : 1 < q) (hc : 0 < c) :
    Summable fun i => (maternTheta q c i ^ 2)⁻¹ := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 ≤ (q ^ 2)⁻¹ := by positivity
  have hr1 : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
  refine ((summable_geometric_of_lt_one hr0 hr1).mul_left (c ^ 2 * (q ^ 2)⁻¹)).congr fun i => ?_
  have hqi : 0 < q ^ i := pow_pos hq0 _
  have e : (q ^ (i + 1)) ^ 2 = q ^ 2 * (q ^ 2) ^ i := by ring
  have hq2 : 0 < (q ^ 2) ^ i := by positivity
  rw [maternTheta, div_pow, e, inv_pow]
  field_simp

/-- `F_q` in the form of `lem:laplace-atoms-admissible`(2), with `a = 0`. -/
theorem maternExponent_eq_atoms (hq : 1 < q) (hc : 0 < c) (ω : ℝ) :
    maternExponent q c ω = 0 * ω ^ 2 + ∑' i, Real.log (1 + ω ^ 2 / maternTheta q c i ^ 2) := by
  rw [zero_mul, zero_add, maternExponent]
  exact tsum_congr fun i => by rw [maternTerm_eq hq hc]

/-- `lem:laplace-atoms-admissible`(2) at the atoms of `F_q`. -/
local notation "maternAtoms" hq:max hc:max =>
  laplace_atoms_admissible_2 (ι := ℕ) le_rfl (maternTheta _ _) (maternTheta_pos hq hc)
    (summable_maternTheta hq hc) (maternExponent _ _) (maternExponent_eq_atoms hq hc)

theorem summable_maternExponent (hq : 1 < q) (hc : 0 < c) (r : ℝ) :
    Summable fun i : ℕ => Real.log (1 + c ^ 2 * r ^ 2 / q ^ (2 * (i + 1))) :=
  ((maternAtoms hq hc).1 r).congr fun i => by rw [maternTerm_eq hq hc]

theorem maternExponent_hasSum (hq : 1 < q) (hc : 0 < c) (r : ℝ) :
    HasSum (fun i : ℕ => Real.log (1 + c ^ 2 * r ^ 2 / q ^ (2 * (i + 1))))
      (maternExponent q c r) :=
  (summable_maternExponent hq hc r).hasSum

theorem maternExponent_zero (q c : ℝ) : maternExponent q c 0 = 0 := by
  simp [maternExponent]

theorem maternExponent_neg (q c r : ℝ) : maternExponent q c (-r) = maternExponent q c r := by
  simp [maternExponent]

theorem maternExponent_abs (q c r : ℝ) : maternExponent q c |r| = maternExponent q c r := by
  simp [maternExponent, sq_abs]

theorem maternExponent_mul_abs (q c t r : ℝ) :
    maternExponent q c (t * |r|) = maternExponent q c (t * r) := by
  simp [maternExponent, mul_pow, sq_abs]

theorem maternExponent_nonneg (hq : 1 < q) (hc : 0 < c) (r : ℝ) : 0 ≤ maternExponent q c r :=
  ((maternAtoms hq hc).2.1 r).1

theorem maternExponent_le (hq : 1 < q) (hc : 0 < c) (r : ℝ) :
    maternExponent q c r ≤ (∑' i, (maternTheta q c i ^ 2)⁻¹) * r ^ 2 := by
  have h := ((maternAtoms hq hc).2.1 r).2
  rwa [zero_add] at h

/-- **The telescoping**: `F_q(qr) = log(1 + c²r²) + F_q(r)`. -/
theorem maternExponent_mul_q (hq : 1 < q) (hc : 0 < c) (r : ℝ) :
    maternExponent q c (q * r) = Real.log (1 + c ^ 2 * r ^ 2) + maternExponent q c r := by
  have hq0 : q ≠ 0 := by linarith
  rw [maternExponent, (summable_maternExponent hq hc (q * r)).tsum_eq_zero_add, maternExponent]
  congr 1
  · congr 2
    rw [mul_pow, zero_add, mul_one]
    field_simp
  · refine tsum_congr fun i => ?_
    congr 2
    rw [mul_pow, show 2 * (i + 1 + 1) = 2 * (i + 1) + 2 by ring, pow_add]
    field_simp

/-- `F_q(r) → 0` as `r → 0`. -/
theorem tendsto_maternExponent_zero (hq : 1 < q) (hc : 0 < c) :
    Tendsto (maternExponent q c) (𝓝 0) (𝓝 0) := by
  set K := ∑' i, (maternTheta q c i ^ 2)⁻¹
  have hK : Tendsto (fun r : ℝ => K * r ^ 2) (𝓝 0) (𝓝 0) := by
    have : Continuous fun r : ℝ => K * r ^ 2 := by fun_prop
    simpa using this.tendsto 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hK
    (maternExponent_nonneg hq hc) (maternExponent_le hq hc)


/-! ## The display (A.e7) -/

/-- **`thm:matern-pyramid-line`, the display (A.e7)**:
`e^{-F_q(tω)} = ∏_{i ≥ 1} (1 + c²q^{-2i}t²ω²)⁻¹`. -/
theorem matern_pyramid_line_display {q c : ℝ} (hq : 1 < q) (hc : 0 < c) (t ω : ℝ) :
    HasProd (fun i : ℕ => (1 + c ^ 2 * (t * ω) ^ 2 / q ^ (2 * (i + 1)))⁻¹)
      (Real.exp (-maternExponent q c (t * ω))) := by
  have h := (maternExponent_hasSum hq hc (t * ω)).neg.rexp
  convert h using 1
  funext i
  have hq0 : 0 < q := by linarith
  have hp : 0 < 1 + c ^ 2 * (t * ω) ^ 2 / q ^ (2 * (i + 1)) := by positivity
  simp only [Function.comp_apply, Real.exp_neg, Real.exp_log hp]


/-! ## Clause (1): the profile, the family, the octave step -/

/-- **The profile of `F_q`**: `a = 0` and `k(x) = 2∑_{i ≥ 1} e^{-xqⁱ/c}`, from
`lem:laplace-atoms-admissible`(2). -/
theorem exists_maternProfile (hq : 1 < q) (hc : 0 < c) :
    ∃ P : SDProfile, P.a = 0 ∧
      (∀ x : ℝ, 0 < x → P.k x = 2 * ∑' i : ℕ, Real.exp (-(x * q ^ (i + 1) / c))) ∧
      ∀ ω : ℝ, maternExponent q c ω = P.exponent ω := by
  obtain ⟨P, hPa, hPk, hP⟩ := (maternAtoms hq hc).2.2.2.1
  refine ⟨P, hPa, fun x hx => ?_, hP⟩
  rw [hPk x hx]
  congr 1
  exact tsum_congr fun i => by rw [maternTheta]; ring_nf

/-- `F_q ≢ 0`. -/
theorem exists_maternExponent_ne (hq : 1 < q) (hc : 0 < c) : ∃ ω : ℝ, maternExponent q c ω ≠ 0 :=
  ((maternAtoms hq hc).2.2.2.2.2.2).2 (Or.inr ⟨0⟩)

/-- The identity is a gauge. -/
theorem isGauge_idFun : IsGauge (fun t : ℝ => t) :=
  ⟨rfl, fun _ _ _ _ h => h, fun t ht => ⟨t, ht, rfl⟩⟩

/-- The construction data of a profile with the gauge `χ = id`. -/
noncomputable def idData (P : SDProfile) : ConstructionData :=
  constructionDataOf (fun t => t) P isGauge_idFun

theorem idData_expo {P : SDProfile} (hP : ∀ ω : ℝ, maternExponent q c ω = P.exponent ω)
    (s t ω : ℝ) :
    (idData P).expo s t ω = maternExponent q c (t * ‖ω‖) - maternExponent q c (s * ‖ω‖) := by
  rw [Real.norm_eq_abs, maternExponent_mul_abs, maternExponent_mul_abs, hP, hP]
  rfl

theorem idData_gaugeAction (P : SDProfile) {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    (idData P).gaugeAction lam t = lam * t :=
  (idData P).chiInv_chi (mul_nonneg hlam.le ht)

/-- A Matérn pyramid, totalised by `δ₀`, has the kernels of `(id, F_q)`. -/
theorem isGaugeKernels_of_matern {P : SDProfile}
    (hP : ∀ ω : ℝ, maternExponent q c ω = P.exponent ω) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsMaternPyramid q c μ) : IsGaugeKernels (idData P) (totalLaws μ) := by
  have hprob : ∀ s t, IsProbabilityMeasure (totalLaws μ s t) := fun s t => by
    by_cases hst : 0 ≤ s ∧ s ≤ t
    · rw [totalLaws_of hst]
      exact (hμ s t hst.1 hst.2).1
    · rw [totalLaws_of_not hst]
      infer_instance
  have hcf : ∀ s t, 0 ≤ s → s ≤ t → ∀ ω : ℝ,
      charFun (totalLaws μ s t) ω = ((Real.exp (-((idData P).expo s t ω)) : ℝ) : ℂ) :=
    fun s t hs hst ω => by
      rw [totalLaws_of ⟨hs, hst⟩, (hμ s t hs hst).2 ω, idData_expo hP]
  refine ⟨hprob, fun s t => ?_, hcf⟩
  by_cases hst : 0 ≤ s ∧ s ≤ t
  · haveI := hprob s t
    exact isSymmetric_of_charFun ((idData P).expo_isSymLevyExponent hst.1 hst.2)
      (hcf s t hst.1 hst.2)
  · rw [totalLaws_of_not hst, ScaleSpace.IsSymmetric, Measure.map_dirac' measurable_neg,
      neg_zero]

/-- **The family**: Matérn pyramids exist, and any one is the kernel family of a family with
(A1)–(A8) and (ND), `S_λ t = λt`. -/
theorem matern_family (hq : 1 < q) (hc : 0 < c) :
    (∃ μ : ℝ → ℝ → Measure ℝ, IsMaternPyramid q c μ) ∧
      ∀ μ : ℝ → ℝ → Measure ℝ, IsMaternPyramid q c μ →
        ∃ Fam : CascadeFamily, IsKernelFamily Fam.Φ μ ∧
          ∀ lam : ℝ, 0 < lam → ∀ t : ℝ, 0 ≤ t → Fam.S lam t = lam * t := by
  obtain ⟨P, -, -, hP⟩ := exists_maternProfile hq hc
  have hne : ∃ ω : ℝ, (idData P).P.exponent ω ≠ 0 := by
    obtain ⟨ω, hω⟩ := exists_maternExponent_ne hq hc
    exact ⟨ω, show P.exponent ω ≠ 0 by rw [← hP]; exact hω⟩
  refine ⟨?_, fun μ hμ => ?_⟩
  · obtain ⟨κ, hκ⟩ := exists_isGaugeKernels (idData P)
    refine ⟨κ, fun s t hs hst => ⟨hκ.prob s t, fun ω => ?_⟩⟩
    rw [hκ.charFun_eq s t hs hst ω, idData_expo hP]
  · have hκ := isGaugeKernels_of_matern hP hμ
    have hker := hκ.cascadeData.isKernelFamily
    refine ⟨hκ.cascadeFamily hne, ⟨fun s t hs hst => (hμ s t hs hst).1, fun s t hs hst f => ?_⟩,
      fun lam hlam t ht => idData_gaugeAction P hlam ht⟩
    have h := hker.conv s t hs hst f
    rwa [IsGaugeKernels.cascadeData_κ, totalLaws_of ⟨hs, hst⟩] at h

/-- `L̂_r(ω) = (1 + r²ω²)⁻¹`. -/
theorem charFun_laplaceLaw_real {r : ℝ} (hr : 0 < r) (ω : ℝ) :
    charFun (laplaceLaw r) ω = (((1 + r ^ 2 * ω ^ 2)⁻¹ : ℝ) : ℂ) :=
  (charFun_laplaceLaw hr ω).trans (fourierLine_laplace hr ω)

/-- **The octave step** of a Matérn pyramid is `L_{ct}`. -/
theorem matern_octave_step (hq : 1 < q) (hc : 0 < c) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsMaternPyramid q c μ) {t : ℝ} (ht : 0 < t) : μ t (q * t) = laplaceLaw (c * t) := by
  have hle : t ≤ q * t := le_mul_of_one_le_left ht.le hq.le
  haveI := (hμ t (q * t) ht.le hle).1
  haveI : IsProbabilityMeasure (laplaceLaw (c * t)) :=
    ScaleSpace.isProbabilityMeasure_laplaceLaw (mul_pos hc ht)
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  have hp : 0 < 1 + c ^ 2 * (t * ‖ω‖) ^ 2 := by positivity
  rw [(hμ t (q * t) ht.le hle).2 ω, charFun_laplaceLaw_real (mul_pos hc ht)]
  beta_reduce
  rw [mul_assoc,
    maternExponent_mul_q hq hc, add_sub_cancel_right, Real.exp_neg, Real.exp_log hp,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring_nf

/-- **`thm:matern-pyramid-line`(1).** `F_q` is admissible with `a = 0` and the completely monotone
profile `k(x) = 2∑_{i ≥ 1} e^{-xqⁱ/c}`; its similarity family exists and satisfies (A1)–(A8) and
(ND) with `S_λ t = λt`; `F_q(qtω) - F_q(tω) = log(1 + c²t²ω²)`, so `μ_{t,qt} = L_{ct}`, the law with
`L̂_r(ω) = (1 + r²ω²)⁻¹`. -/
theorem matern_pyramid_line_1 {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    (∃ P : SDProfile, P.a = 0 ∧
        (∀ x : ℝ, 0 < x → P.k x = 2 * ∑' i : ℕ, Real.exp (-(x * q ^ (i + 1) / c))) ∧
        ∀ ω : ℝ, maternExponent q c ω = P.exponent ω) ∧
      IsCompletelyMonotone (fun x => 2 * ∑' i : ℕ, Real.exp (-(x * q ^ (i + 1) / c))) ∧
      (∃ μ : ℝ → ℝ → Measure ℝ, IsMaternPyramid q c μ) ∧
      (∀ μ : ℝ → ℝ → Measure ℝ, IsMaternPyramid q c μ →
        ∃ Fam : CascadeFamily, IsKernelFamily Fam.Φ μ ∧
          ∀ lam : ℝ, 0 < lam → ∀ t : ℝ, 0 ≤ t → Fam.S lam t = lam * t) ∧
      (∀ t ω : ℝ, maternExponent q c (q * t * ω) - maternExponent q c (t * ω) =
        Real.log (1 + c ^ 2 * t ^ 2 * ω ^ 2)) ∧
      (∀ μ : ℝ → ℝ → Measure ℝ, IsMaternPyramid q c μ → ∀ t : ℝ, 0 < t →
        μ t (q * t) = laplaceLaw (c * t)) ∧
      ∀ r : ℝ, 0 < r → ∀ ω : ℝ, charFun (laplaceLaw r) ω = (((1 + r ^ 2 * ω ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hCM : IsCompletelyMonotone (fun x => 2 * ∑' i : ℕ, Real.exp (-(x * q ^ (i + 1) / c))) := by
    have h := (maternAtoms hq hc).2.2.2.2.1
    convert h using 3 with x
    exact tsum_congr fun i => by rw [maternTheta]; ring_nf
  refine ⟨exists_maternProfile hq hc, hCM, (matern_family hq hc).1, (matern_family hq hc).2,
    fun t ω => ?_, fun μ hμ t ht => matern_octave_step hq hc hμ ht,
    fun r hr ω => charFun_laplaceLaw_real hr ω⟩
  rw [mul_assoc, maternExponent_mul_q hq hc, add_sub_cancel_right, mul_pow]
  ring_nf



/-! ## Clause (2): the selection -/

/-- The exponent of a Matérn pyramid: `Ψ_t(ω) = F_q(tω)`. -/
theorem lineExponent_matern {μ : ℝ → ℝ → Measure ℝ} (hμ : IsMaternPyramid q c μ) {t : ℝ}
    (ht : 0 ≤ t) (ω : ℝ) : lineExponent μ t ω = maternExponent q c (t * ω) := by
  rw [lineExponent, (hμ 0 t le_rfl ht).2 ω, Complex.ofReal_re]
  beta_reduce
  rw [zero_mul, maternExponent_zero, sub_zero, Real.log_exp, neg_neg, Real.norm_eq_abs,
    maternExponent_mul_abs]

/-- Two Matérn pyramids have the same laws. -/
theorem matern_eq {μ μ' : ℝ → ℝ → Measure ℝ} (hμ : IsMaternPyramid q c μ)
    (hμ' : IsMaternPyramid q c μ') : ∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ' s t := by
  intro s t hs hst
  haveI := (hμ s t hs hst).1
  haveI := (hμ' s t hs hst).1
  exact Measure.ext_of_charFun (funext fun ω => by rw [(hμ s t hs hst).2, (hμ' s t hs hst).2])

/-- A Matérn pyramid is a `q^ℤ`-covariant family in the canonical discrete gauge. -/
theorem isQFamily_matern (hq : 1 < q) (hc : 0 < c) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsMaternPyramid q c μ) : IsQFamily q μ := by
  have hq0 : 0 < q := by linarith
  obtain ⟨Fam, hker, -⟩ := (matern_family hq hc).2 μ hμ
  refine ⟨line_axioms_kernels_1_family Fam.toCascadeCore μ hker,
    ⟨fun t ht => mul_nonneg hq0.le ht, fun u _ v _ huv => mul_lt_mul_of_pos_left huv hq0,
      fun t ht => ⟨t / q, div_nonneg ht hq0.le, mul_div_cancel₀ t hq0.ne'⟩⟩, fun s t hs hst => ?_⟩
  have hqs : 0 ≤ q * s := mul_nonneg hq0.le hs
  have hqst : q * s ≤ q * t := mul_le_mul_of_nonneg_left hst hq0.le
  haveI := (hμ s t hs hst).1
  haveI := (hμ (q * s) (q * t) hqs hqst).1
  haveI : IsProbabilityMeasure ((μ s t).map fun x => q • x) :=
    Measure.isProbabilityMeasure_map (measurable_const_smul q).aemeasurable
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_map_smul, (hμ s t hs hst).2, (hμ (q * s) (q * t) hqs hqst).2]
  beta_reduce
  simp only [norm_smul, Real.norm_of_nonneg hq0.le]
  ring_nf

/-- A Matérn pyramid lies in the modulation orbit of its ladder. -/
theorem matern_mem_orbit (hq : 1 < q) (hc : 0 < c) {μ : ℝ → ℝ → Measure ℝ}
    (hμ : IsMaternPyramid q c μ) : μ ∈ modulationOrbit q (maternExponent q c) := by
  refine ⟨isQFamily_matern hq hc hμ, fun ω => ?_⟩
  rw [(hμ 0 1 le_rfl zero_le_one).2 ω]
  beta_reduce
  rw [zero_mul, one_mul, maternExponent_zero, sub_zero, Real.norm_eq_abs, maternExponent_abs]

/-- The ladder of `F_q` has no Gaussian part: its step `log(1 + c²ω²)` is one Laplace atom. -/
theorem matern_noGaussianStep (hq : 1 < q) (hc : 0 < c) :
    HasNoGaussianStep q (maternExponent q c) := by
  obtain ⟨-, -, -, ⟨D, hDa, -, hD⟩, -⟩ := laplace_atoms_admissible_2 (ι := Unit) le_rfl
    (fun _ => 1 / c) (fun _ => by positivity) (Summable.of_finite)
    (fun ω => Real.log (1 + c ^ 2 * ω ^ 2)) (fun ω => by
      rw [zero_mul, zero_add, tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
      congr 2
      field_simp)
  refine ⟨dilatePair D one_pos, fun ω => ?_, by simp [dilatePair, hDa]⟩
  rw [dilatePair_exponent, one_mul, ← hD, knotStep, maternExponent_mul_q hq hc,
    add_sub_cancel_right]

/-- **`thm:matern-pyramid-line`(2), selection.** On the modulation orbit of its ladder, the
similarity family is the only member with `Ψ_{λt} = Ψ_t(λ ·)` and the unique maximizer of the phase
entropy. -/
theorem matern_pyramid_line_2 {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    (∀ μ : ℝ → ℝ → Measure ℝ, IsMaternPyramid q c μ → μ ∈ modulationOrbit q (maternExponent q c)) ∧
      (∀ μ ∈ modulationOrbit q (maternExponent q c),
        (∀ lam t : ℝ, 0 < lam → 0 < t → ∀ ω : ℝ,
          lineExponent μ (lam * t) ω = lineExponent μ t (lam * ω)) ↔ IsMaternPyramid q c μ) ∧
      (∀ μ : ℝ → ℝ → Measure ℝ, IsMaternPyramid q c μ →
        ∃ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (π : ℝ → Measure ℝ), IsFamilyPair q μ Λ B ∧
          IsPhaseDisintegration q (cylMeasure q Λ) π ∧ phaseEntropy q (cylMeasure q Λ) π = 0) ∧
      ∀ μ ∈ modulationOrbit q (maternExponent q c),
        ∀ (Λ : Measure (ℝ × ℝ)) (B : Measure ℝ) (π : ℝ → Measure ℝ),
        IsFamilyPair q μ Λ B → IsPhaseDisintegration q (cylMeasure q Λ) π →
          phaseEntropy q (cylMeasure q Λ) π ≤ 0 ∧
            (phaseEntropy q (cylMeasure q Λ) π = 0 ↔ IsMaternPyramid q c μ) := by
  obtain ⟨μ₀, hμ₀⟩ := (matern_family hq hc).1
  have hmem₀ := matern_mem_orbit hq hc hμ₀
  have hnoG := matern_noGaussianStep hq hc
  have hsim : ∀ (μ : ℝ → ℝ → Measure ℝ), IsMaternPyramid q c μ → ∀ t : ℝ, 0 < t → ∀ ω : ℝ,
      lineExponent μ t ω = maternExponent q c (t * ω) :=
    fun μ hμ t ht ω => lineExponent_matern hμ ht.le ω
  have hsel1 := phase_entropy_selection_1 hq _ μ₀ hmem₀ (hsim μ₀ hμ₀)
  have hsel3 := phase_entropy_selection_3 hq _ hnoG μ₀ hmem₀ (hsim μ₀ hμ₀)
  have hiff : ∀ μ : ℝ → ℝ → Measure ℝ,
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → μ s t = μ₀ s t) ↔ IsMaternPyramid q c μ := by
    intro μ
    refine ⟨fun h s t hs hst => ?_, fun h => matern_eq h hμ₀⟩
    rw [h s t hs hst]
    exact hμ₀ s t hs hst
  refine ⟨fun μ hμ => matern_mem_orbit hq hc hμ, fun μ hμ =>
    ⟨fun hcov => (hiff μ).1 (hsel1.2 μ hμ hcov), fun hM lam t hlam ht ω => ?_⟩,
    fun μ hμ => (phase_entropy_selection_3 hq _ hnoG μ (matern_mem_orbit hq hc hμ)
      (hsim μ hμ)).1,
    fun μ hμ Λ B π hΛ hπ => ⟨phaseEntropy_nonpos q _ π, (hsel3.2 μ hμ Λ B π hΛ hπ).trans (hiff μ)⟩⟩
  rw [lineExponent_matern hM (mul_pos hlam ht).le, lineExponent_matern hM ht.le]
  congr 1
  ring

/-- **`thm:matern-pyramid-line`(2), directly.** A function `F̃` on `(0,∞)` with
`F̃(qω) - F̃(ω) = log(1 + c²ω²)` and `F̃(0+) = 0` is `F_q` there. -/
theorem matern_pyramid_line_2_direct {q c : ℝ} (hq : 1 < q) (hc : 0 < c) (F : ℝ → ℝ)
    (heq : ∀ ω : ℝ, 0 < ω → F (q * ω) - F ω = Real.log (1 + c ^ 2 * ω ^ 2))
    (h0 : Tendsto F (𝓝[>] 0) (𝓝 0)) : ∀ ω : ℝ, 0 < ω → F ω = maternExponent q c ω := by
  intro ω hω
  have hq0 : 0 < q := by linarith
  set D : ℝ → ℝ := fun x => F x - maternExponent q c x with hDdef
  have hD : ∀ x : ℝ, 0 < x → D (q * x) = D x := fun x hx => by
    simp only [hDdef]
    have := heq x hx
    rw [maternExponent_mul_q hq hc]
    linarith
  have hiter : ∀ n : ℕ, D (ω / q ^ n) = D ω := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, ← hD _ (div_pos hω (pow_pos hq0 _))]
      congr 1
      rw [pow_succ]
      field_simp
  have hseq : Tendsto (fun n : ℕ => ω / q ^ n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => div_pos hω (pow_pos hq0 _)⟩
    exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hq)
  have hlim : Tendsto (fun n : ℕ => D (ω / q ^ n)) atTop (𝓝 (0 - 0)) :=
    (h0.comp hseq).sub
      ((tendsto_maternExponent_zero hq hc).comp (hseq.mono_right nhdsWithin_le_nhds))
  have hc0 : D ω = 0 := by
    rw [sub_zero] at hlim
    exact tendsto_nhds_unique (tendsto_const_nhds.congr fun n => (hiter n).symm) hlim
  simp only [hDdef] at hc0
  linarith

/-! ## Clause (3): the generator -/

/-- `(1 + a)⁻¹ - 1 ∈ [-1, 0]` and `|(1 + a)⁻¹ - 1| ≤ a` for `a ≥ 0`. -/
theorem inv_one_add_sub_one {a : ℝ} (ha : 0 ≤ a) :
    -1 ≤ (1 + a)⁻¹ - 1 ∧ (1 + a)⁻¹ - 1 ≤ 0 ∧ |(1 + a)⁻¹ - 1| ≤ a := by
  have h1 : 0 < 1 + a := by linarith
  have hle : (1 + a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hpos : 0 < (1 + a)⁻¹ := inv_pos.2 h1
  have e : (1 + a)⁻¹ - 1 = -(a / (1 + a)) := by field_simp; ring
  have hb : a / (1 + a) ≤ a := div_le_self ha (by linarith)
  refine ⟨by linarith, by linarith, ?_⟩
  rw [e, abs_neg, abs_of_nonneg (div_nonneg ha h1.le)]
  exact hb

/-- `A q^{-2(i+1)}` is summable. -/
theorem summable_genTerm (hq : 1 < q) (A : ℝ) :
    Summable fun i : ℕ => A / q ^ (2 * (i + 1)) := by
  have hq0 : 0 < q := by linarith
  have hr0 : 0 ≤ (q ^ 2)⁻¹ := by positivity
  have hr1 : (q ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
  refine ((summable_geometric_of_lt_one hr0 hr1).mul_left (A * (q ^ 2)⁻¹)).congr fun i => ?_
  rw [pow_mul, inv_pow, pow_succ]
  field_simp
  ring

theorem genArg_eq (q c t ω : ℝ) (i : ℕ) :
    (c * t / q ^ (i + 1)) ^ 2 * ω ^ 2 = c ^ 2 * t ^ 2 * ω ^ 2 / q ^ (2 * (i + 1)) := by
  rw [div_pow, mul_comm 2 (i + 1), pow_mul]
  ring

theorem summable_maternLineGen (hq : 1 < q) (c t ω : ℝ) :
    Summable fun i : ℕ => (1 + (c * t / q ^ (i + 1)) ^ 2 * ω ^ 2)⁻¹ - 1 := by
  refine Summable.of_norm_bounded (summable_genTerm hq (c ^ 2 * t ^ 2 * ω ^ 2)) fun i => ?_
  rw [Real.norm_eq_abs, ← genArg_eq]
  exact (inv_one_add_sub_one (by positivity)).2.2

/-- The derivative of `F_q(τω)` at `τ = t > 0`, term by term. -/
theorem hasDerivAt_maternExponent_mul (hq : 1 < q) (hc : 0 < c) {t : ℝ} (ht : 0 < t) (ω : ℝ) :
    HasDerivAt (fun τ => maternExponent q c (τ * ω)) (-maternLineGen q c t ω) t := by
  have hq0 : 0 < q := by linarith
  set g : ℕ → ℝ → ℝ := fun i τ => Real.log (1 + c ^ 2 * (τ * ω) ^ 2 / q ^ (2 * (i + 1)))
  set g' : ℕ → ℝ → ℝ := fun i τ =>
    2 * c ^ 2 * τ * ω ^ 2 / q ^ (2 * (i + 1)) / (1 + c ^ 2 * (τ * ω) ^ 2 / q ^ (2 * (i + 1)))
  have hg : ∀ i τ, τ ∈ Ioo 0 (2 * t) → HasDerivAt (g i) (g' i τ) τ := by
    intro i τ _
    have hQ : 0 < q ^ (2 * (i + 1)) := pow_pos hq0 _
    have hp : 0 < 1 + c ^ 2 * (τ * ω) ^ 2 / q ^ (2 * (i + 1)) := by positivity
    have h0 : HasDerivAt (fun y : ℝ => y * ω) ω τ := by
      simpa using (hasDerivAt_id τ).mul_const ω
    have hin : HasDerivAt (fun y => 1 + c ^ 2 * (y * ω) ^ 2 / q ^ (2 * (i + 1)))
        (2 * c ^ 2 * τ * ω ^ 2 / q ^ (2 * (i + 1))) τ := by
      have h2 := (((h0.pow 2).const_mul (c ^ 2)).div_const (q ^ (2 * (i + 1)))).const_add 1
      refine h2.congr_deriv ?_
      norm_num
      ring
    exact hin.log hp.ne'
  have hg' : ∀ i τ, τ ∈ Ioo 0 (2 * t) →
      ‖g' i τ‖ ≤ 2 * c ^ 2 * (2 * t) * ω ^ 2 / q ^ (2 * (i + 1)) := by
    intro i τ hτ
    have hQ : 0 < q ^ (2 * (i + 1)) := pow_pos hq0 _
    have h1 : 1 ≤ 1 + c ^ 2 * (τ * ω) ^ 2 / q ^ (2 * (i + 1)) := by
      have : 0 ≤ c ^ 2 * (τ * ω) ^ 2 / q ^ (2 * (i + 1)) := by positivity
      linarith
    have hn : 0 ≤ 2 * c ^ 2 * τ * ω ^ 2 / q ^ (2 * (i + 1)) := by
      have := hτ.1.le
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn (by linarith))]
    refine (div_le_self hn h1).trans ?_
    gcongr
    exact hτ.2.le
  have hsum := summable_genTerm hq (2 * c ^ 2 * (2 * t) * ω ^ 2)
  have hmem : t ∈ Ioo 0 (2 * t) := ⟨ht, by linarith⟩
  have hD := hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioo isPreconnected_Ioo hg hg' hmem
    (summable_maternExponent hq hc (t * ω)) hmem
  have e : -maternLineGen q c t ω = ∑' i, g' i t := by
    rw [maternLineGen, ← tsum_mul_left, ← tsum_neg]
    refine tsum_congr fun i => ?_
    have hQ : 0 < q ^ (i + 1) := pow_pos hq0 _
    have e : q ^ (2 * (i + 1)) = (q ^ (i + 1)) ^ 2 := by rw [mul_comm, pow_mul]
    simp only [g']
    rw [e]
    field_simp
    ring
  rw [e]
  exact hD

/-- **The asymptotics**, a uniform bound: for `X ≥ 1`,
`|∑_{i ≥ 1} (1 - (1 + X²q^{-2i})⁻¹) - log_q X| ≤ 1 + (1 - q^{-2})⁻¹`. -/
theorem maternSum_logb (hq : 1 < q) {X : ℝ} (hX : 1 ≤ X) :
    |∑' i : ℕ, (1 - (1 + (X / q ^ (i + 1)) ^ 2)⁻¹) - Real.logb q X| ≤
      1 + (1 - (q ^ 2)⁻¹)⁻¹ := by
  have hq0 : 0 < q := by linarith
  have hX0 : 0 < X := by linarith
  set r : ℝ := (q ^ 2)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq two_ne_zero)
  set B : ℝ := (1 - r)⁻¹ with hB
  set f : ℕ → ℝ := fun i => 1 - (1 + (X / q ^ (i + 1)) ^ 2)⁻¹ with hf
  -- the terms
  have hfb : ∀ i, 0 ≤ f i ∧ f i ≤ 1 ∧ f i ≤ (X / q ^ (i + 1)) ^ 2 := by
    intro i
    obtain ⟨h1, h2, h3⟩ := inv_one_add_sub_one (sq_nonneg (X / q ^ (i + 1)))
    rw [abs_of_nonpos h2] at h3
    simp only [hf]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le (fun i => (hfb i).1) (fun i => (hfb i).2.2) ?_
    refine (summable_genTerm hq (X ^ 2)).congr fun i => ?_
    rw [div_pow, ← pow_mul, mul_comm]
  -- the floor of `log_q X`
  set L := Real.logb q X with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg hq hX
  set N := ⌊L⌋₊ with hN
  have hNL : (N : ℝ) ≤ L := Nat.floor_le hL0
  have hLN : L < N + 1 := Nat.lt_floor_add_one L
  have hqL : q ^ L = X := Real.rpow_logb hq0 hq.ne' hX0
  have hqN : q ^ N ≤ X := by
    rw [← hqL, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq.le hNL
  have hXN : X < q ^ (N + 1) := by
    rw [← hqL, ← Real.rpow_natCast]
    push_cast
    exact Real.rpow_lt_rpow_of_exponent_lt hq hLN
  -- the head: `N - B ≤ ∑_{i < N} f i ≤ N`
  have hhead1 : ∑ i ∈ Finset.range N, f i ≤ N := by
    calc ∑ i ∈ Finset.range N, f i ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (hfb i).2.1
      _ = N := by simp
  have hhead2 : (N : ℝ) - B ≤ ∑ i ∈ Finset.range N, f i := by
    have hterm : ∀ i ∈ Finset.range N, 1 - r ^ (N - 1 - i) ≤ f i := by
      intro i hi
      have hiN : i + 1 ≤ N := Finset.mem_range.1 hi
      have hsplit : q ^ N = q ^ (i + 1) * q ^ (N - 1 - i) := by
        rw [← pow_add]
        congr 1
        omega
      have hx : q ^ (N - 1 - i) ≤ X / q ^ (i + 1) := by
        rw [le_div_iff₀ (pow_pos hq0 _), mul_comm, ← hsplit]
        exact hqN
      have hx0 : 0 < q ^ (N - 1 - i) := pow_pos hq0 _
      have hsq : (q ^ 2) ^ (N - 1 - i) ≤ (X / q ^ (i + 1)) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]
        exact pow_le_pow_left₀ hx0.le hx 2
      have hpos : 0 < (q ^ 2) ^ (N - 1 - i) := by positivity
      have : (1 + (X / q ^ (i + 1)) ^ 2)⁻¹ ≤ r ^ (N - 1 - i) := by
        rw [hr, inv_pow]
        exact inv_anti₀ hpos (by linarith)
      simp only [hf]
      linarith
    have hgeom : ∑ i ∈ Finset.range N, r ^ (N - 1 - i) ≤ B := by
      rw [Finset.sum_range_reflect (fun j => r ^ j) N, hB, ← tsum_geometric_of_lt_one hr0 hr1]
      exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ fun j _ => pow_nonneg hr0 j
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib] at this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    linarith
  -- the tail: `0 ≤ ∑_{i ≥ N} f i ≤ B`
  have htail1 : 0 ≤ ∑' i, f (i + N) := tsum_nonneg fun i => (hfb _).1
  have htail2 : ∑' i, f (i + N) ≤ B := by
    rw [hB, ← tsum_geometric_of_lt_one hr0 hr1]
    refine ((summable_nat_add_iff N).2 hfs).tsum_le_tsum (fun i => ?_)
      (summable_geometric_of_lt_one hr0 hr1)
    refine (hfb _).2.2.trans ?_
    have hsplit : q ^ (i + N + 1) = q ^ (N + 1) * q ^ i := by
      rw [← pow_add]
      congr 1
      omega
    have hx : X / q ^ (i + N + 1) ≤ 1 / q ^ i := by
      rw [hsplit, div_le_div_iff₀ (by positivity) (by positivity), one_mul, mul_comm]
      exact (mul_le_mul_of_nonneg_left hXN.le (pow_pos hq0 i).le).trans_eq (mul_comm _ _)
    have hx0 : 0 ≤ X / q ^ (i + N + 1) := by positivity
    calc (X / q ^ (i + N + 1)) ^ 2 ≤ (1 / q ^ i) ^ 2 := pow_le_pow_left₀ hx0 hx 2
      _ = r ^ i := by
        rw [hr, inv_pow, ← pow_mul, mul_comm 2 i, pow_mul, ← inv_pow, one_div]
  have hS : ∑' i, f i = ∑ i ∈ Finset.range N, f i + ∑' i, f (i + N) :=
    (hfs.sum_add_tsum_nat_add N).symm
  change |∑' i, f i - L| ≤ 1 + B
  rw [abs_le, hS]
  constructor <;> linarith

/-- **`thm:matern-pyramid-line`(3), the generator.** `∂_t e^{-F_q(tω)} = h_t(ω) e^{-F_q(tω)}`; each
term of `h_t` lies in `[-2/t, 0]`; `-h_t(ω) = (2/t) log_q(ct|ω|) + O(1/t)` as `|ω| → ∞`, uniformly;
and `h_t` is unbounded. -/
theorem matern_pyramid_line_3 {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    (∀ t : ℝ, 0 < t → ∀ ω : ℝ,
        Summable (fun i : ℕ => (1 + (c * t / q ^ (i + 1)) ^ 2 * ω ^ 2)⁻¹ - 1) ∧
        HasDerivAt (fun τ => Real.exp (-maternExponent q c (τ * ω)))
          (maternLineGen q c t ω * Real.exp (-maternExponent q c (t * ω))) t) ∧
      (∀ t : ℝ, 0 < t → ∀ (ω : ℝ) (i : ℕ),
        -(2 / t) ≤ 2 / t * ((1 + (c * t / q ^ (i + 1)) ^ 2 * ω ^ 2)⁻¹ - 1) ∧
          2 / t * ((1 + (c * t / q ^ (i + 1)) ^ 2 * ω ^ 2)⁻¹ - 1) ≤ 0) ∧
      (∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ ω : ℝ, 1 ≤ c * t * |ω| →
        |-maternLineGen q c t ω - 2 / t * Real.logb q (c * t * |ω|)| ≤ C / t) ∧
      ∀ t : ℝ, 0 < t → ¬ ∃ M : ℝ, ∀ ω : ℝ, |maternLineGen q c t ω| ≤ M := by
  have hq0 : 0 < q := by linarith
  set B : ℝ := 1 + (1 - (q ^ 2)⁻¹)⁻¹ with hB
  have hasym : ∀ t : ℝ, 0 < t → ∀ ω : ℝ, 1 ≤ c * t * |ω| →
      |-maternLineGen q c t ω - 2 / t * Real.logb q (c * t * |ω|)| ≤ 2 * B / t := by
    intro t ht ω hX
    have e : -maternLineGen q c t ω =
        2 / t * ∑' i : ℕ, (1 - (1 + (c * t * |ω| / q ^ (i + 1)) ^ 2)⁻¹) := by
      rw [maternLineGen, ← mul_neg, ← tsum_neg]
      congr 1
      refine tsum_congr fun i => ?_
      rw [div_pow, div_pow, mul_pow (c * t), sq_abs]
      ring
    have h2t : 0 < 2 / t := by positivity
    rw [e, ← mul_sub, abs_mul, abs_of_pos h2t]
    calc 2 / t * |∑' i : ℕ, (1 - (1 + (c * t * |ω| / q ^ (i + 1)) ^ 2)⁻¹) -
          Real.logb q (c * t * |ω|)| ≤ 2 / t * B :=
          mul_le_mul_of_nonneg_left (maternSum_logb hq hX) h2t.le
      _ = 2 * B / t := by ring
  refine ⟨fun t ht ω => ⟨summable_maternLineGen hq c t ω, ?_⟩, fun t ht ω i => ?_,
    ⟨2 * B, hasym⟩, fun t ht => ?_⟩
  · have h : HasDerivAt (fun τ => Real.exp (-maternExponent q c (τ * ω)))
        (Real.exp (-maternExponent q c (t * ω)) * -(-maternLineGen q c t ω)) t :=
      (hasDerivAt_maternExponent_mul hq hc ht ω).neg.exp
    convert h using 1
    ring
  · obtain ⟨h1, h2, -⟩ := inv_one_add_sub_one (a := (c * t / q ^ (i + 1)) ^ 2 * ω ^ 2)
      (by positivity)
    have h2t : 0 < 2 / t := by positivity
    constructor <;> nlinarith
  · rintro ⟨M, hM⟩
    obtain ⟨K, hK⟩ := exists_nat_gt ((M * t + 2 * B) / 2)
    have hct : 0 < c * t := mul_pos hc ht
    set ω : ℝ := q ^ K / (c * t) with hω
    have hX : c * t * |ω| = q ^ K := by
      rw [abs_of_pos (by positivity), hω]
      field_simp
    have h1 : 1 ≤ c * t * |ω| := by
      rw [hX]
      exact one_le_pow₀ hq.le
    have ha := hasym t ht ω h1
    rw [hX, Real.logb_pow, Real.logb_self_eq_one hq, mul_one] at ha
    have hb := (abs_le.1 (hM ω)).1
    have hc1 := (abs_le.1 ha).1
    have hMt : M * t < 2 * K - 2 * B := by linarith
    have hlt : M < (2 * K - 2 * B) / t := by
      rw [lt_div_iff₀ ht]
      exact hMt
    have e : (2 * K - 2 * B) / t = 2 / t * K - 2 * B / t := by ring
    linarith

end Pyramids
