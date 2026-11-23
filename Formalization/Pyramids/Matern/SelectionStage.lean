/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.StageLemmaConverse
import Pyramids.Matern.MaternPyramid
import Pyramids.Matern.IncrementsLevy
import Pyramids.Pyramid.IsotropicSymmetric
import Pyramids.Pyramid.LadderKnot
import Pyramids.Pyramid.LatticeStrata
import Pyramids.Line.GridTransfer
import Pyramids.LineAppendix.MaternLine

/-!
# `thm:selection-stratum-two`(1), (2)'s converse, (3) and (4): one stage

Blueprint: `blueprint/src/parts/04-matern.tex`, `thm:selection-stratum-two`. Phase 5, wave 3b (on
the VM).

* **(1), one stage.** The stage `μ_{t,qt}` of an isotropic family is symmetric and rotation
  invariant, so `prop:stage-lemma`(3) makes it the resolvent `(1 + τ|ω|²)⁻¹`, `τ > 0` by (ND).
  Covariance and (I1) give `μ̂_t(qω) = (1 + τ|ω|²)⁻¹ μ̂_t(ω)`, and the partial products of the
  ladder tend to `μ̂_t` (`tendsto_ladderProd`, `prop:ladder-knot-kernel`(1)), which is the series
  `∑_{n ≥ 1} log(1 + τq^{-2n}r²) = F¹_q(√τ r)`. Conversely the telescoping
  `F_q(qr) = log(1 + c²r²) + F_q(r)` gives the stage's transform, and `prop:stage-lemma`(1)
  applies. The ladder is the dilates of `L_{√τ}` (`step_zpow_of_cov`).
* **(3), which stages.** If a stage `μ^M_{s,t}`, `0 ≤ s < t`, has the principle, then along a unit
  vector `D(x) := F_q(tx) - F_q(sx) = log(1 + kx²)`, `k ≥ 0`. The telescoping at `x` and `qx` gives
  `(1 + kq²u)(1 + c²s²u) = (1 + c²t²u)(1 + ku)`, `u = x²`; at `u = 1` and `u = 2` the coefficients
  of `u` and `u²` vanish: `k(t² - q²s²) = 0` and `c²(t² - s²) = k(q² - 1)`. So `k > 0` and
  `t = qs`; at `s = 0` this is impossible. This replaces the print's comparison of zeros and poles
  of a meromorphic quotient.
* **(4).** The Gaussian's reciprocal `e^{ax²}` would be `1 + kx²` at `x = 1` and `x = √2`, so
  `(1 + k)² = 1 + 2k`, `k = 0`, `a = 0`. The frame step's reciprocal on the diagonal
  `x(e₁ + e₂)` is `(1 + c²t²x²)²`, which is not `1 + Qx²` (the same two points). The axis pass is
  the resolvent of the positive semidefinite `c²t²eⱼeⱼᵀ`.

Dropped binders (2026-11-15, a strengthening): `selection_stratum_two_1_ladder` and
`selection_stratum_two_2_converse` take no `1 ≤ d`;
`selection_stratum_two_4_axis` takes no `1 ≤ d`, `0 < c`, `0 < t`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace Matrix ComplexOrder

variable {d : ℕ}

/-! ## The series -/

/-- The printed series is `F¹_q(√τ r)`. -/
theorem logSeries_eq_maternExponent {q τ : ℝ} (hτ : 0 ≤ τ) (r : ℝ) :
    ∑' n : ℕ, Real.log (1 + τ * r ^ 2 / q ^ (2 * (n + 1))) =
      maternExponent q 1 (Real.sqrt τ * r) := by
  simp only [maternExponent, one_pow, one_mul, mul_pow, Real.sq_sqrt hτ]

/-- `(1 + x)⁻¹ = e^{-log(1 + x)}` for `x ≥ 0`. -/
theorem inv_one_add_eq_exp {x : ℝ} (hx : 0 ≤ x) :
    (1 + x)⁻¹ = Real.exp (-Real.log (1 + x)) := by
  rw [Real.exp_neg, Real.exp_log (by linarith)]

/-! ## Stages of a family -/

/-- The stage `μ_{t,qt}` of a `q`-covariant family relates the kernels:
`μ̂_t(qω) = μ̂_{t,qt}(ω) μ̂_t(ω)`. -/
theorem charFun_kernel_q {q : ℝ} {μ : ℝ → ℝ → Measure (Rd d)} (hμ : IsLawHemigroup μ)
    (hcov : IsCovariantAt μ q fun t => q * t) {t : ℝ} (ht : 0 ≤ t) (hle : t ≤ q * t)
    (ω : Rd d) :
    charFun (μ 0 t) (q • ω) = charFun (μ t (q * t)) ω * charFun (μ 0 t) ω := by
  have hk : (μ 0 t).map (fun x => q • x) = μ 0 (q * t) := cov_kernel hcov ht
  rw [← charFun_map_smul, hk, charFun_kernel_mul_gen hμ ht hle]

/-- **The stage from the kernel.** If `μ̂_t(ω) = e^{-F¹_q(√τ|ω|)}`, then
`μ̂_{t,qt}(ω) = (1 + τ|ω|²)⁻¹`. -/
theorem charFun_stage_of_rep {q : ℝ} (hq : 1 < q) {μ : ℝ → ℝ → Measure (Rd d)}
    (hμ : IsLawHemigroup μ) (hcov : IsCovariantAt μ q fun t => q * t) {t : ℝ} (ht : 0 < t)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hrep : ∀ ω : Rd d, charFun (μ 0 t) ω = ((Real.exp (-∑' n : ℕ,
        Real.log (1 + τ * ‖ω‖ ^ 2 / q ^ (2 * (n + 1)))) : ℝ) : ℂ)) (ω : Rd d) :
    charFun (μ t (q * t)) ω = (((1 + τ * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hq0 : 0 < q := by linarith
  have hle : t ≤ q * t := le_mul_of_one_le_left ht.le hq.le
  have h := charFun_kernel_q hμ hcov ht.le hle ω
  rw [hrep, hrep, logSeries_eq_maternExponent hτ, logSeries_eq_maternExponent hτ, norm_smul,
    Real.norm_of_nonneg hq0.le, mul_left_comm, maternExponent_mul_q hq one_pos, neg_add,
    Real.exp_add, Complex.ofReal_mul] at h
  have hne : ((Real.exp (-maternExponent q 1 (Real.sqrt τ * ‖ω‖)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  have h2 := mul_right_cancel₀ hne h
  rw [← h2, one_pow, one_mul, mul_pow, Real.sq_sqrt hτ, inv_one_add_eq_exp (by positivity)]

/-- `D_a L_r = L_{ar}`. -/
theorem maternStep_map_smul (a r : ℝ) :
    (maternStep d r).map (fun x => a • x) = maternStep d (a * r) := by
  rw [maternStep, maternStep, Measure.map_map (measurable_const_smul a) (measurable_const_smul r)]
  congr 1
  funext x
  simp [smul_smul]

/-- A probability with the transform `(1 + τ|ω|²)⁻¹`, `τ ≥ 0`, is `L_{√τ}`. -/
theorem eq_maternStep_of_charFun {ρ : Measure (Rd d)} [IsProbabilityMeasure ρ] {τ : ℝ}
    (hτ : 0 ≤ τ) (h : ∀ ω : Rd d, charFun ρ ω = (((1 + τ * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ)) :
    ρ = maternStep d (Real.sqrt τ) := by
  haveI := (charFun_maternStep (d := d) (Real.sqrt τ) 0).1
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [h, (charFun_maternStep _ ω).2, Real.sq_sqrt hτ]

/-! ## Clause (1) -/

/-- The partial products of the ladder of `(1 + τ|ω|²)⁻¹` tend to `e^{-∑ log(1 + τq^{-2n}|ω|²)}`. -/
theorem tendsto_ladderProd_resolvent {q τ : ℝ} (hq : 1 < q) (hτ : 0 ≤ τ) (ρ : Measure (Rd d))
    (hρ : ∀ ω : Rd d, charFun ρ ω = (((1 + τ * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ)) (ω : Rd d) :
    Tendsto (fun M => ladderProd q ρ M ω) atTop (𝓝 ((Real.exp (-∑' n : ℕ,
        Real.log (1 + τ * ‖ω‖ ^ 2 / q ^ (2 * (n + 1)))) : ℝ) : ℂ)) := by
  have hq0 : 0 < q := by linarith
  have hsum : Summable fun n : ℕ => Real.log (1 + τ * ‖ω‖ ^ 2 / q ^ (2 * (n + 1))) := by
    have h := summable_maternExponent hq one_pos (Real.sqrt τ * ‖ω‖)
    simpa only [one_pow, one_mul, mul_pow, Real.sq_sqrt hτ] using h
  have heq : ∀ M : ℕ, ladderProd q ρ M ω = ((Real.exp (-∑ n ∈ Finset.range M,
      Real.log (1 + τ * ‖ω‖ ^ 2 / q ^ (2 * (n + 1)))) : ℝ) : ℂ) := by
    intro M
    rw [ladderProd, ← Finset.sum_neg_distrib, Real.exp_sum, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [hρ, norm_smul, Real.norm_of_nonneg (zpow_pos hq0 _).le, mul_pow, zpow_neg_succ,
      inv_pow, ← pow_mul, mul_comm (n + 1) 2, inv_one_add_eq_exp (by positivity)]
    congr 4
    field_simp
  simp_rw [heq]
  refine (Complex.continuous_ofReal.tendsto _).comp ?_
  refine (Real.continuous_exp.tendsto _).comp ?_
  exact hsum.hasSum.tendsto_sum_nat.neg

/-- **`thm:selection-stratum-two`(1), one stage.** For an isotropic `q`-covariant family in the
canonical discrete gauge and `t > 0`: `μ_{t,qt}` has the principle if and only if
`Ψ_t(r) = ∑_{n ≥ 1} log(1 + τ q^{-2n} r²)` for some `τ > 0`, read on the transform. -/
theorem selection_stratum_two_1 (hd : 1 ≤ d) {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure (Rd d))
    (hiso : IsIsotropicFamily μ) (hcov : IsCovariantAt μ q fun t => q * t) {t : ℝ} (ht : 0 < t) :
    HasImplicitEulerPrinciple (μ t (q * t)) ↔ ∃ τ : ℝ, 0 < τ ∧ ∀ ω : Rd d,
      charFun (μ 0 t) ω = ((Real.exp (-∑' n : ℕ,
        Real.log (1 + τ * ‖ω‖ ^ 2 / q ^ (2 * (n + 1)))) : ℝ) : ℂ) := by
  have hle : t ≤ q * t := le_mul_of_one_le_left ht.le hq.le
  have hlt : t < q * t := lt_mul_of_one_lt_left ht hq
  have hsym := isotropicFamily_isSymmetricFamily μ hiso
  haveI := hiso.1.1.isProbability t (q * t) ht.le hle
  haveI := hiso.1.1.isProbability 0 t le_rfl ht.le
  constructor
  · intro hP
    obtain ⟨τ, hτ, hρ, -, h0⟩ := stage_lemma_3_rotation hd (μ t (q * t))
      (hsym.2.2 t (q * t) ht.le hle) hP (hiso.2 t (q * t) ht.le hle)
    have hτpos : 0 < τ := by
      rcases hτ.eq_or_lt with h | h
      · exact absurd (h0 h.symm) (hiso.1.2 t (q * t) ht.le hlt)
      · exact h
    refine ⟨τ, hτpos, fun ω => ?_⟩
    -- `μ̂_t(ω) = P_M(ω) μ̂_t(q^{-M}ω)`, and `μ̂_t(q^{-M}ω) → 1`
    have hstep : ∀ ω, charFun (μ t (q * t)) ω * charFun (μ 0 t) ω = charFun (μ 0 t) (q • ω) :=
      fun ω => (charFun_kernel_q hiso.1.1 hcov ht.le hle ω).symm
    have hone : Tendsto (fun M : ℕ => charFun (μ 0 t) ((q ^ (-(M : ℤ))) • ω)) atTop (𝓝 1) := by
      have h1 : charFun (μ 0 t) 0 = 1 := by simp [charFun_zero]
      rw [← h1]
      exact continuous_charFun.continuousAt.tendsto.comp (tendsto_zpow_neg_smul hq ω)
    have hlim := (tendsto_ladderProd_resolvent hq hτ _ hρ ω).mul hone
    rw [mul_one] at hlim
    exact tendsto_nhds_unique (tendsto_const_nhds.congr fun M =>
      (ladderProd_mul_eq (by linarith) _ hstep ω M).symm) hlim
  · rintro ⟨τ, hτ, hrep⟩
    exact stage_lemma_1_helmholtz hτ.le _ (charFun_stage_of_rep hq hiso.1.1 hcov ht hτ.le hrep)

/-- **`thm:selection-stratum-two`(1), the ladder.** Then the ladder through `t` is the Matérn
pyramid's, `μ_{q^k t, q^{k+1} t} = L_{√τ q^k}`, `k ∈ ℤ`. -/
theorem selection_stratum_two_1_ladder {q : ℝ} (hq : 1 < q)
    (μ : ℝ → ℝ → Measure (Rd d)) (hiso : IsIsotropicFamily μ)
    (hcov : IsCovariantAt μ q fun t => q * t) {t : ℝ} (ht : 0 < t) {τ : ℝ} (hτ : 0 < τ)
    (hrep : ∀ ω : Rd d, charFun (μ 0 t) ω = ((Real.exp (-∑' n : ℕ,
        Real.log (1 + τ * ‖ω‖ ^ 2 / q ^ (2 * (n + 1)))) : ℝ) : ℂ)) :
    ∀ k : ℤ, μ (q ^ k * t) (q ^ (k + 1) * t) = maternStep d (Real.sqrt τ * q ^ k) := by
  have hq0 : 0 < q := by linarith
  have hle : t ≤ q * t := le_mul_of_one_le_left ht.le hq.le
  haveI := hiso.1.1.isProbability t (q * t) ht.le hle
  have hstep : μ t (q * t) = maternStep d (Real.sqrt τ) :=
    eq_maternStep_of_charFun hτ.le (charFun_stage_of_rep hq hiso.1.1 hcov ht hτ.le hrep)
  intro k
  have h := step_zpow_of_cov hq hcov k t (q * t) ht.le hle
  rw [← mul_assoc, ← zpow_add_one₀ hq0.ne'] at h
  rw [h, hstep, maternStep_map_smul, mul_comm]

/-! ## Clause (2), the converse -/

/-- **`thm:selection-stratum-two`(2), the converse.** The Matérn pyramid (`c = 1`) read in a gauge
`χ ∈ 𝒢_q` has the principle at every octave stage. -/
theorem selection_stratum_two_2_converse {q : ℝ} (hq : 1 < q) (χ : ℝ → ℝ)
    (hχ : IsInGaugeGroup q χ) (ν : ℝ → ℝ → Measure (Rd d)) (hν : IsMaternPyramid q 1 ν) :
    ∀ t : ℝ, 0 < t → HasImplicitEulerPrinciple (ν (extendByZero χ t) (extendByZero χ (q * t))) := by
  intro t ht
  have hq0 : 0 < q := by linarith
  have hχt : 0 < χ t := hχ.mapsTo (mem_Ioi.2 ht)
  have hqt : q * t ≠ 0 := (mul_pos hq0 ht).ne'
  rw [extendByZero, if_neg ht.ne', extendByZero, if_neg hqt, hχ.equivariant t ht]
  have hle : χ t ≤ q * χ t := le_mul_of_one_le_left hχt.le hq.le
  haveI := (hν _ _ hχt.le hle).1
  refine stage_lemma_1_helmholtz (sq_nonneg (χ t)) _ fun ω => ?_
  rw [charFun_maternPyramid hν hχt.le hle, mul_assoc, maternExponent_mul_q hq one_pos,
    add_sub_cancel_right, one_pow, one_mul, mul_pow, inv_one_add_eq_exp (by positivity)]

/-! ## Clause (3) -/

/-- **The coefficients.** If `(1 + kq²u)(1 + βu) = (1 + αu)(1 + ku)` at `u = 1` and `u = 2`, the
coefficients of `u²` and `u` agree. -/
theorem coeff_of_two_points {α β k q : ℝ}
    (h1 : (1 + k * q ^ 2) * (1 + β) = (1 + α) * (1 + k))
    (h2 : (1 + k * q ^ 2 * 2) * (1 + β * 2) = (1 + α * 2) * (1 + k * 2)) :
    k * (α - q ^ 2 * β) = 0 ∧ α - β + k * (1 - q ^ 2) = 0 := by
  constructor
  · linear_combination (2 * h1 - h2) / 2
  · linear_combination h2 / 2 - 2 * h1

/-- A symmetric probability whose transform is even. -/
theorem map_neg_of_charFun_norm {ρ : Measure (Rd d)} [IsProbabilityMeasure ρ] {G : ℝ → ℝ}
    (h : ∀ ω : Rd d, charFun ρ ω = ((G ‖ω‖ : ℝ) : ℂ)) : ρ.map (fun x => -x) = ρ :=
  map_neg_eq_of_charFun_even ρ fun ω => by rw [h, h, norm_neg]

/-- Along a unit vector, a resolvent transform reads `1 + kx²` with `k ≥ 0`. -/
theorem exists_resolvent_ray (hd : 1 ≤ d) {ρ : Measure (Rd d)} [IsProbabilityMeasure ρ]
    (hsymm : ρ.map (fun x => -x) = ρ) (hP : HasImplicitEulerPrinciple ρ) :
    ∃ e : Rd d, ‖e‖ = 1 ∧ ∃ k : ℝ, 0 ≤ k ∧
      ∀ x : ℝ, charFun ρ (x • e) = (((1 + k * x ^ 2)⁻¹ : ℝ) : ℂ) := by
  obtain ⟨C, hC, hρ⟩ := stage_lemma_3 ρ hsymm hP
  obtain ⟨e, he⟩ := exists_unit_Rd hd
  refine ⟨e, he, quad C e, AffineHemigroup.quad_nonneg hC e, fun x => ?_⟩
  rw [hρ, Pyramids.quad_smul, mul_comm]

/-- **A Matérn stage with the principle is an octave step**: `0 ≤ s < t` and the principle for
`μ^M_{s,t}` give `t = qs`. -/
theorem eq_q_mul_of_principle (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    {μ : ℝ → ℝ → Measure (Rd d)} (hμ : IsMaternPyramid q c μ) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (hP : HasImplicitEulerPrinciple (μ s t)) : t = q * s := by
  have hq0 : 0 < q := by linarith
  have ht : 0 < t := hs.trans_lt hst
  haveI := (hμ s t hs hst.le).1
  have hsymm := map_neg_of_charFun_norm (G := fun r =>
    Real.exp (-(maternExponent q c (t * r) - maternExponent q c (s * r))))
    (charFun_maternPyramid hμ hs hst.le)
  obtain ⟨e, he, k, hk, hray⟩ := exists_resolvent_ray hd hsymm hP
  -- `e^{D(x)} = 1 + kx²` for `x ≥ 0`
  have hD : ∀ x : ℝ, 0 ≤ x →
      Real.exp (maternExponent q c (t * x) - maternExponent q c (s * x)) = 1 + k * x ^ 2 := by
    intro x hx
    have h := (charFun_maternPyramid hμ hs hst.le (x • e)).symm.trans (hray x)
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg hx] at h
    have h2 := Complex.ofReal_injective h
    rw [Real.exp_neg] at h2
    have hp : 0 < 1 + k * x ^ 2 := by positivity
    exact inv_injective h2
  -- the telescoping at `x` and `qx`
  have hpoly : ∀ x : ℝ, 0 ≤ x →
      (1 + k * q ^ 2 * x ^ 2) * (1 + c ^ 2 * s ^ 2 * x ^ 2) =
        (1 + c ^ 2 * t ^ 2 * x ^ 2) * (1 + k * x ^ 2) := by
    intro x hx
    have h1 := hD (q * x) (mul_nonneg hq0.le hx)
    rw [mul_left_comm t, mul_left_comm s, maternExponent_mul_q hq hc,
      maternExponent_mul_q hq hc, add_sub_add_comm, Real.exp_add, Real.exp_sub,
      Real.exp_log (by positivity), Real.exp_log (by positivity), hD x hx] at h1
    have hs' : 0 < 1 + c ^ 2 * (s * x) ^ 2 := by positivity
    field_simp at h1
    linear_combination -h1
  have h1 := hpoly 1 zero_le_one
  have h2 := hpoly (Real.sqrt 2) (Real.sqrt_nonneg 2)
  rw [Real.sq_sqrt zero_le_two] at h2
  simp only [one_pow, mul_one] at h1
  obtain ⟨hB, hA⟩ := coeff_of_two_points (α := c ^ 2 * t ^ 2) (β := c ^ 2 * s ^ 2) (k := k) (q := q)
    (by linear_combination h1) (by linear_combination h2)
  have hc2 : 0 < c ^ 2 := by positivity
  rcases hk.eq_or_lt with hk0 | hkpos
  · subst hk0
    have : t ^ 2 = s ^ 2 := by
      have h := hA
      simp only [zero_mul, add_zero] at h
      have : c ^ 2 * (t ^ 2 - s ^ 2) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc2.ne'
      · linarith
    have := (pow_left_inj₀ ht.le hs two_ne_zero).1 this
    linarith
  · have h := (mul_eq_zero.1 hB).resolve_left hkpos.ne'
    have h2 : t ^ 2 = (q * s) ^ 2 := by
      have : c ^ 2 * (t ^ 2 - (q * s) ^ 2) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc2.ne'
      · linarith
    exact (pow_left_inj₀ ht.le (mul_nonneg hq0.le hs) two_ne_zero).1 h2

/-- **`thm:selection-stratum-two`(3), which stages.** A stage `μ^M_{s,t}`, `0 < s < t`, of the
Matérn pyramid has the principle if and only if `t = qs`, and `μ^M_{0,t}` never has it. -/
theorem selection_stratum_two_3 (hd : 1 ≤ d) {q c : ℝ} (hq : 1 < q) (hc : 0 < c)
    (μ : ℝ → ℝ → Measure (Rd d)) (hμ : IsMaternPyramid q c μ) :
    (∀ s t : ℝ, 0 < s → s < t → (HasImplicitEulerPrinciple (μ s t) ↔ t = q * s)) ∧
      ∀ t : ℝ, 0 < t → ¬ HasImplicitEulerPrinciple (μ 0 t) := by
  refine ⟨fun s t hs hst => ⟨eq_q_mul_of_principle hd hq hc hμ hs.le hst, ?_⟩, fun t ht hP => ?_⟩
  · rintro rfl
    have hle : s ≤ q * s := le_mul_of_one_le_left hs.le hq.le
    haveI := (hμ s (q * s) hs.le hle).1
    rw [matern_octave_step_d hd hq hc hμ hs]
    haveI := (charFun_maternStep (d := d) (c * s) 0).1
    exact stage_lemma_1_helmholtz (sq_nonneg (c * s)) _ fun ω => (charFun_maternStep _ ω).2
  · have h := eq_q_mul_of_principle hd hq hc hμ le_rfl ht hP
    rw [mul_zero] at h
    exact ht.ne' h

/-! ## Clause (4) -/

/-- **`thm:selection-stratum-two`(4), the Gaussian stage** `N(0, 2aI)`, `a > 0`, fails the
principle. -/
theorem selection_stratum_two_4_gaussian (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) :
    ¬ HasImplicitEulerPrinciple (gaussVar d (2 * a)) := by
  intro hP
  have h2a : 0 ≤ 2 * a := by positivity
  have hch : ∀ ω : Rd d, charFun (gaussVar d (2 * a)) ω =
      ((Real.exp (-(2 * a * ‖ω‖ ^ 2) / 2) : ℝ) : ℂ) := charFun_gaussVar h2a
  have hsymm := map_neg_of_charFun_norm (G := fun r => Real.exp (-(2 * a * r ^ 2) / 2)) hch
  obtain ⟨e, he, k, hk, hray⟩ := exists_resolvent_ray hd hsymm hP
  have hx : ∀ x : ℝ, Real.exp (a * x ^ 2) = 1 + k * x ^ 2 := by
    intro x
    have h := (hch (x • e)).symm.trans (hray x)
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs] at h
    have h2 := Complex.ofReal_injective h
    have e1 : -(2 * a * x ^ 2) / 2 = -(a * x ^ 2) := by ring
    rw [e1, Real.exp_neg] at h2
    exact inv_injective h2
  have h1 := hx 1
  have h2 := hx (Real.sqrt 2)
  rw [Real.sq_sqrt zero_le_two] at h2
  simp only [one_pow, mul_one] at h1
  have h3 : Real.exp (a * 2) = Real.exp a ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  rw [h3, h1] at h2
  have hk0 : k = 0 := by nlinarith
  rw [hk0, add_zero, Real.exp_eq_one_iff] at h1
  exact ha.ne' h1

/-- **`thm:selection-stratum-two`(4), the frame step** `∏_j (1 + c²t²ω_j²)⁻¹` fails the principle in
`d ≥ 2`. -/
theorem selection_stratum_two_4_frame (hd : 2 ≤ d) {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (ρ : Measure (Rd d)) [IsProbabilityMeasure ρ]
    (hρ : ∀ ω : Rd d, charFun ρ ω = ((∏ j, (1 + c ^ 2 * t ^ 2 * ω j ^ 2)⁻¹ : ℝ) : ℂ)) :
    ¬ HasImplicitEulerPrinciple ρ := by
  intro hP
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  have hsymm : ρ.map (fun x => -x) = ρ :=
    map_neg_eq_of_charFun_even ρ fun ω => by
      rw [hρ, hρ]
      simp only [PiLp.neg_apply, neg_sq]
  obtain ⟨C, hC, hC'⟩ := stage_lemma_3 ρ hsymm hP
  set K := c ^ 2 * t ^ 2 with hK
  have hKpos : 0 < K := by positivity
  set e : Rd (n + 2) := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 with he
  have hx : ∀ x : ℝ, (1 + K * x ^ 2) ^ 2 = 1 + quad C e * x ^ 2 := by
    intro x
    have h := (hρ (x • e)).symm.trans (hC' (x • e))
    rw [Pyramids.quad_smul] at h
    have h2 := Complex.ofReal_injective h
    rw [Finset.prod_inv_distrib, inv_inj] at h2
    rw [mul_comm (quad C e), ← h2, Fin.prod_univ_succ, Fin.prod_univ_succ]
    have hrest : ∀ i : Fin n, (x • e) i.succ.succ = 0 := fun i => by
      have hne : i.succ.succ ≠ 1 := fun h' => by
        have := congrArg Fin.val h'
        simp at this
      simp [he, Fin.succ_ne_zero, hne]
    simp only [hrest, sq, mul_zero, add_zero, Finset.prod_const_one, mul_one]
    simp [he]
  have h1 := hx 1
  have h2 := hx (Real.sqrt 2)
  rw [Real.sq_sqrt zero_le_two] at h2
  simp only [one_pow, mul_one] at h1
  nlinarith

/-- **`thm:selection-stratum-two`(4), the axis passes**: the Laplace law on the line `ℝe_j` with
transform `(1 + c²t²ω_j²)⁻¹` has the principle. -/
theorem selection_stratum_two_4_axis {c t : ℝ} (j : Fin d) (ρ : Measure (Rd d))
    [IsProbabilityMeasure ρ]
    (hρ : ∀ ω : Rd d, charFun ρ ω = (((1 + c ^ 2 * t ^ 2 * ω j ^ 2)⁻¹ : ℝ) : ℂ)) :
    HasImplicitEulerPrinciple ρ := by
  set C : Mat d := Matrix.diagonal (Pi.single j (c ^ 2 * t ^ 2)) with hCdef
  have hC : C.PosSemidef := by
    rw [hCdef, Matrix.posSemidef_diagonal_iff]
    intro i
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same]; positivity
    · simp [h]
  refine hasImplicitEulerPrinciple_resolvent hC ρ fun ω => ?_
  have hq : quad C ω = c ^ 2 * t ^ 2 * ω j ^ 2 := by
    rw [quad_eq_sum_mul, Finset.sum_eq_single j (fun i _ hi => Finset.sum_eq_zero fun k _ => by
        rw [hCdef, Matrix.diagonal_apply]
        split_ifs <;> simp [Pi.single_eq_of_ne hi]) (by simp),
      Finset.sum_eq_single j (fun k _ hk => by
        rw [hCdef, Matrix.diagonal_apply_ne _ (Ne.symm hk), zero_mul]) (by simp),
      hCdef, Matrix.diagonal_apply_eq, Pi.single_eq_same]
    ring
  rw [hρ, hq]

end Pyramids
