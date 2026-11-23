/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.AnnulusParametrization
import Pyramids.LineAppendix.GaugeGroup
import Pyramids.LineAppendix.StepField
import Pyramids.Line.LineAxiomsKernels
import Pyramids.Cited.A4

/-!
# `thm:annulus-parametrization-phase`: the octave phase

Blueprint: `blueprint/src/parts/A1-line.tex`. Moved from `PyramidsSkeleton.ChA1Line` in wave 3d,
unchanged in statement and name, except that `annulus_phase_1_converse` no longer takes the unused
`1 < q` (2026-11-14, a strengthening).

## The route

The printed one.

* **(1)** Covariance at the pairs `(0, t)` (`lineExponent_cov`), with `t = e^u`, `ω = e^v`; the
  exponents are even (`lineExponent_abs`). The converse is a rewrite by the periodicity.
* **(2)** `F(r) := Ξ(log r; 0)` for `r > 0` and `F(0) := 0`. If `Ψ_t(ω) = F(t|ω|)`, the
  transforms of the steps give `T_λμ_{s,t} = μ_{λs,λt}`. The family is then fully covariant, and
  `thm:cited-A4`'s "only if", applied to the operator family of its kernels
  (`lem:line-axioms-kernels`(2)–(3); `exists_profile_of_fullCov`), gives a gauge `χ` and an
  admissible `F' ≢ 0` with `Ψ_t = F'(χ(t) ·)`. At `t = 1`, `F = F'(c ·)`, `c = χ(1) > 0`, and
  `F'(c ·)` is admissible (`profile_exists_dilate`, the substitution `y = cx`).
* **(3)** The same pair: `F(χ(qt) ·) = F(qχ(t) ·)` and the injectivity of `r ↦ F(r ·)` on
  `(0,∞)` (`eq_of_comp_mul_eq`) give `χ(qt) = qχ(t)`; `lem:gauge-group`(1) at the identity gauge
  then puts `χ` on `(0,∞)` in `𝒢_q`.
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (X CascadeCore CascadeFamily IsScaleCovariant IsKernelFamily SDProfile
  profileJumpL profileMeasure)
open scoped Topology ENNReal

/-! ## Evenness and the steps -/

/-- The exponent is even. -/
theorem lineExponent_neg (μ : ℝ → ℝ → Measure ℝ) (t ω : ℝ) :
    lineExponent μ t (-ω) = lineExponent μ t ω := by
  simp only [lineExponent, charFun_neg, Complex.conj_re]

theorem lineExponent_abs (μ : ℝ → ℝ → Measure ℝ) (t ω : ℝ) :
    lineExponent μ t |ω| = lineExponent μ t ω := by
  rcases abs_choice ω with h | h
  · rw [h]
  · rw [h, lineExponent_neg]

/-- **The transform of a step**, `μ̂_{s,t} = e^{-(Ψ_t - Ψ_s)}`. -/
theorem charFun_step_eq_exp {μ : ℝ → ℝ → Measure ℝ} (hμ : IsSymmetricFamily μ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ω : ℝ) :
    charFun (μ s t) ω = ((Real.exp (-(lineExponent μ t ω - lineExponent μ s ω)) : ℝ) : ℂ) := by
  have h := charFun_kernel_mul_gen hμ.1 hs hst ω
  rw [charFun_kernel_eq_exp hμ (hs.trans hst) ω, charFun_kernel_eq_exp hμ hs ω] at h
  have hne : ((Real.exp (-lineExponent μ s ω) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  rw [eq_div_of_mul_eq hne h.symm, ← Complex.ofReal_div, ← Real.exp_sub]
  congr 2
  ring

/-! ## (1) -/

/-- **`thm:annulus-parametrization-phase`(1).** `ψ(u + ℓ, v) = ψ(u, v + ℓ)`; `Ξ` is `ℓ`-periodic in
its second argument; and `Ψ_t(ω) = Ξ(log(t|ω|); log t)` for `t > 0`, `ω ≠ 0`. -/
theorem annulus_phase_1 {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure ℝ) (hμ : IsQFamily q μ) :
    (∀ u v : ℝ, octavePsi (lineExponent μ) (u + Real.log q) v =
        octavePsi (lineExponent μ) u (v + Real.log q)) ∧
      (∀ w ξ : ℝ, octaveXi (lineExponent μ) w (ξ + Real.log q) = octaveXi (lineExponent μ) w ξ) ∧
      ∀ t : ℝ, 0 < t → ∀ ω : ℝ, ω ≠ 0 →
        lineExponent μ t ω = octaveXi (lineExponent μ) (Real.log (t * |ω|)) (Real.log t) := by
  have hq0 : 0 < q := by linarith
  have h1 : ∀ u v : ℝ, octavePsi (lineExponent μ) (u + Real.log q) v =
      octavePsi (lineExponent μ) u (v + Real.log q) := by
    intro u v
    simp only [octavePsi, Real.exp_add, Real.exp_log hq0]
    rw [mul_comm (Real.exp u) q, lineExponent_cov hμ (Real.exp_pos u).le, mul_comm q]
  refine ⟨h1, fun w ξ => ?_, fun t ht ω hω => ?_⟩
  · simp only [octaveXi]
    rw [h1]
    congr 1
    ring
  · simp only [octaveXi, octavePsi]
    have hω' : 0 < |ω| := abs_pos.2 hω
    rw [Real.exp_log ht, Real.exp_sub, Real.exp_log (mul_pos ht hω'), Real.exp_log ht,
      mul_div_cancel_left₀ _ ht.ne', lineExponent_abs]

/-- **`thm:annulus-parametrization-phase`(1), the converse.** For every `Ξ` on `ℝ²`, `ℓ`-periodic
in its second argument, `ψ(u, v) := Ξ(u + v; u)` has `ψ(u + ℓ, v) = ψ(u, v + ℓ)`. The skeleton's
`1 < q` is not used and was dropped on 2026-11-14 (wave 3d), a strengthening. -/
theorem annulus_phase_1_converse {q : ℝ} (Ξ : ℝ → ℝ → ℝ)
    (hΞ : ∀ w ξ : ℝ, Ξ w (ξ + Real.log q) = Ξ w ξ) :
    ∀ u v : ℝ, Ξ (u + Real.log q + v) (u + Real.log q) = Ξ (u + (v + Real.log q)) u := by
  intro u v
  rw [hΞ]
  congr 1
  ring

/-! ## The dilate of a profile -/

/-- **`F(c ·)` is admissible** when `F` is (`c > 0`): the profile `k(· / c)` with Gaussian
coefficient `c²a`. -/
theorem profile_exists_dilate (P : SDProfile) {c : ℝ} (hc : 0 < c) :
    ∃ Q : SDProfile, ∀ ω : ℝ, Q.exponent ω = P.exponent (c * ω) := by
  have hkm : AEMeasurable P.k (volume.restrict (Ioi (0 : ℝ))) := P.aemeasurable_k
  have hkc : AntitoneOn (fun u => P.k (u / c)) (Ioi (0 : ℝ)) :=
    ScaleSpace.antitoneOn_comp_div P.k_antitone hc
  have hkcm : AEMeasurable (fun u : ℝ => P.k (u / c)) (volume.restrict (Ioi (0 : ℝ))) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hkc
  have hkc0 : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ P.k (x / c) := fun x hx =>
    P.k_nonneg _ (mem_Ioi.mpr (div_pos hx hc))
  have hνP : (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(profileMeasure P.k)) ≠ ⊤ :=
    (ScaleSpace.profile_integrability P.k_nonneg hkm).mpr
      ⟨P.integrable_near_zero, P.integrable_at_top⟩
  have hint := (ScaleSpace.profile_integrability hkc0 hkcm).mp
    (ScaleSpace.lintegral_min_profileMeasure_comp_div_ne_top P.k_antitone P.k_nonneg hνP hc)
  refine ⟨⟨P.a * c ^ 2, fun u => P.k (u / c), mul_nonneg P.a_nonneg (sq_nonneg c), hkc0, hkc,
    by simp [P.k_zero], hint.1, hint.2⟩, fun ω => ?_⟩
  simp only [ScaleSpace.SDProfile.exponent, ScaleSpace.SDProfile.exponentL_eq_add_jump]
  rw [ScaleSpace.profileJumpL_comp_div P.k hc ω,
    show P.a * c ^ 2 * ω ^ 2 = P.a * (c * ω) ^ 2 by ring]

theorem profile_exponent_zero (P : SDProfile) : P.exponent 0 = 0 := by
  simp [ScaleSpace.SDProfile.exponent, ScaleSpace.SDProfile.exponentL]

theorem profile_exponent_abs (P : SDProfile) (ω : ℝ) : P.exponent |ω| = P.exponent ω := by
  rcases abs_choice ω with h | h
  · rw [h]
  · rw [h, ScaleSpace.SDProfile.exponent_neg]

/-! ## A fully covariant family and `thm:cited-A4` -/

/-- **The classification, read on the kernels.** A symmetric family on `ℝ` that is `λ`-covariant
for every `λ > 0` has `Ψ_t = F(χ(t) ·)` for a gauge `χ` and an admissible `F ≢ 0`:
`thm:cited-A4`'s "only if", applied to the operator family of its kernels
(`lem:line-axioms-kernels`(2)–(3)). -/
theorem exists_profile_of_fullCov {μ : ℝ → ℝ → Measure ℝ} (hμ : IsSymmetricFamily μ)
    (hfull : ∀ lam : ℝ, 0 < lam → ∃ S : ℝ → ℝ, IsCovariantAt μ lam S) :
    ∃ (χ : ℝ → ℝ) (P : SDProfile), IsGauge χ ∧ (∃ ω : ℝ, P.exponent ω ≠ 0) ∧
      ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ, lineExponent μ t ω = P.exponent (χ t * ω) := by
  classical
  obtain ⟨C, hC⟩ := line_axioms_kernels_2_family μ hμ
  have hS : ∀ lam : ℝ, ∃ S : ℝ → ℝ, 0 < lam → IsCovariantAt μ lam S := by
    intro lam
    by_cases hlam : 0 < lam
    · obtain ⟨S, hS⟩ := hfull lam hlam
      exact ⟨S, fun _ => hS⟩
    · exact ⟨id, fun h => absurd h hlam⟩
  choose S hS using hS
  have hcov : IsScaleCovariant C.Φ (Ioi 0) S :=
    { S_mapsTo := fun lam hlam _ => (hS lam hlam).1.mapsTo
      S_strictMonoOn := fun lam hlam _ => (hS lam hlam).1.strictMonoOn
      S_surjOn := fun lam hlam _ => (hS lam hlam).1.surjOn
      scale := fun lam hlam _ s t hs hst =>
        ((line_axioms_kernels_3 C.Φ μ hC hlam (S lam) (hS lam hlam).1).2
          ((isCovariantAt_iff_map_mul μ lam (S lam)).1 (hS lam hlam)).2) s t hs hst }
  let Fam : CascadeFamily := { toCascadeCore := C, S := S, covariant := hcov }
  obtain ⟨χ, P, μ', hχ, hne, hker', hcf⟩ := (cited_A4 C.Φ).1 ⟨Fam, rfl⟩
  -- the kernels of one operator family agree
  have heq : ∀ t : ℝ, 0 ≤ t → μ' 0 t = μ 0 t := by
    intro t ht
    haveI := hker'.isProbability 0 t le_rfl ht
    haveI := hC.isProbability 0 t le_rfl ht
    refine ScaleSpace.mconvL1_injective ?_
    rw [← eq_mconvL1_of_kernel hker' le_rfl ht, ← eq_mconvL1_of_kernel hC le_rfl ht]
  refine ⟨χ, P, hχ, hne, fun t ht ω => ?_⟩
  have h := hcf 0 t ω le_rfl ht
  rw [heq t ht, hχ.1, zero_mul, profile_exponent_zero, sub_zero] at h
  rw [lineExponent, h, Complex.ofReal_re, Real.log_exp, neg_neg]

/-- **`r ↦ F(r ·)` is injective on `(0,∞)`** for a continuous `F ≢ 0` with `F(0) = 0`: from
`F(r ·) = F(r' ·)`, `r < r'`, follows `F = F((r/r')ⁿ ·) → F(0) = 0`. -/
theorem eq_of_comp_mul_eq {G : ℝ → ℝ} (hG : Continuous G) (hG0 : G 0 = 0)
    (hne : ∃ ω : ℝ, G ω ≠ 0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ ω : ℝ, G (a * ω) = G (b * ω)) : a = b := by
  -- if `a < b`, then `G = G((a/b) ·)`, hence `G ≡ 0`
  have key : ∀ {a b : ℝ}, 0 < a → 0 < b → a < b → (∀ ω : ℝ, G (a * ω) = G (b * ω)) →
      ∀ x : ℝ, G x = 0 := by
    intro a b ha hb hab h x
    set ρ : ℝ := a / b with hρ
    have hρ0 : 0 ≤ ρ := (div_pos ha hb).le
    have hρ1 : ρ < 1 := (div_lt_one hb).2 hab
    have hstep : ∀ y : ℝ, G y = G (ρ * y) := fun y => by
      have := h (y / b)
      rw [show b * (y / b) = y by field_simp, show a * (y / b) = ρ * y by rw [hρ]; ring] at this
      exact this.symm
    have hiter : ∀ n : ℕ, G x = G (ρ ^ n * x) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [ih, hstep (ρ ^ n * x), pow_succ, mul_comm (ρ ^ n) ρ, mul_assoc]
    have hlim : Tendsto (fun n : ℕ => G (ρ ^ n * x)) atTop (𝓝 (G 0)) := by
      have h1 : Tendsto (fun n : ℕ => ρ ^ n * x) atTop (𝓝 (0 * x)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const x
      rw [zero_mul] at h1
      exact (hG.tendsto 0).comp h1
    have hconst : Tendsto (fun n : ℕ => G (ρ ^ n * x)) atTop (𝓝 (G x)) := by
      simp_rw [← hiter]
      exact tendsto_const_nhds
    rw [← hG0]
    exact tendsto_nhds_unique hconst hlim
  obtain ⟨ω₀, hω₀⟩ := hne
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd (key ha hb hab h ω₀) hω₀
  · exact hab
  · exact absurd (key hb ha hab (fun ω => (h ω).symm) ω₀) hω₀

/-! ## (2) -/

/-- **`thm:annulus-parametrization-phase`(2).** `Ξ` does not depend on its second argument iff
`Ψ_t(ω) = F(t|ω|)` for a function `F`; then `F` is admissible on `[0,∞)`, `F ≢ 0`, and the family
is `λ`-covariant with `S_λ t = λt` for every `λ > 0`. -/
theorem annulus_phase_2 {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure ℝ) (hμ : IsQFamily q μ) :
    ((∀ w ξ ξ' : ℝ, octaveXi (lineExponent μ) w ξ = octaveXi (lineExponent μ) w ξ') ↔
        ∃ F : ℝ → ℝ, ∀ t : ℝ, 0 < t → ∀ ω : ℝ, lineExponent μ t ω = F (t * |ω|)) ∧
      ∀ F : ℝ → ℝ, (∀ t : ℝ, 0 < t → ∀ ω : ℝ, lineExponent μ t ω = F (t * |ω|)) →
        (∃ P : SDProfile, ∀ r : ℝ, 0 ≤ r → F r = P.exponent r) ∧ (∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0) ∧
          ∀ lam : ℝ, 0 < lam → IsCovariantAt μ lam (fun t => lam * t) := by
  have hphase := annulus_phase_1 hq μ hμ
  refine ⟨⟨fun hind => ?_, fun ⟨F, hF⟩ w ξ ξ' => ?_⟩, fun F hF => ?_⟩
  · -- the phase drops out: `F(r) := Ξ(log r; 0)`, `F(0) := 0`
    refine ⟨fun r => if r = 0 then 0 else octaveXi (lineExponent μ) (Real.log r) 0,
      fun t ht ω => ?_⟩
    rcases eq_or_ne ω 0 with hω | hω
    · simp [hω, lineExponent_at_zero hμ.1 ht.le]
    · have hpos : t * |ω| ≠ 0 := (mul_pos ht (abs_pos.2 hω)).ne'
      simp only [if_neg hpos]
      rw [hphase.2.2 t ht ω hω]
      exact hind _ _ _
  · -- the phase is absent: `Ξ(w; ξ) = F(e^w)`
    have hXi : ∀ ξ : ℝ, octaveXi (lineExponent μ) w ξ = F (Real.exp w) := by
      intro ξ
      simp only [octaveXi, octavePsi]
      rw [hF _ (Real.exp_pos ξ), abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      congr 2
      ring
    rw [hXi ξ, hXi ξ']
  -- the covariance, from the transforms of the steps
  have hsym := hμ.1
  have hΨcov : ∀ lam : ℝ, 0 < lam → ∀ t : ℝ, 0 ≤ t → ∀ ω : ℝ,
      lineExponent μ (lam * t) ω = lineExponent μ t (lam * ω) := by
    intro lam hlam t ht ω
    rcases ht.eq_or_lt with h0 | htpos
    · rw [← h0, mul_zero, lineExponent_zero hsym, lineExponent_zero hsym]
    · rw [hF _ (mul_pos hlam htpos), hF t htpos, abs_mul, abs_of_pos hlam]
      ring_nf
  have hcov : ∀ lam : ℝ, 0 < lam → IsCovariantAt μ lam (fun t => lam * t) := by
    intro lam hlam
    refine ⟨⟨fun t ht => mul_nonneg hlam.le ht, fun s _ t _ hst => mul_lt_mul_of_pos_left hst hlam,
      fun t ht => ⟨t / lam, div_nonneg ht hlam.le, by field_simp⟩⟩, fun s t hs hst => ?_⟩
    change (μ s t).map (fun x => lam • x) = μ (lam * s) (lam * t)
    haveI := hsym.1.isProbability s t hs hst
    haveI := hsym.1.isProbability (lam * s) (lam * t) (mul_nonneg hlam.le hs)
      (mul_le_mul_of_nonneg_left hst hlam.le)
    haveI : IsProbabilityMeasure ((μ s t).map fun x => lam • x) :=
      Measure.isProbabilityMeasure_map (continuous_const_smul lam).aemeasurable
    refine Measure.ext_of_charFun (funext fun ω => ?_)
    simp only [smul_eq_mul]
    rw [charFun_map_mul, charFun_step_eq_exp hsym hs hst,
      charFun_step_eq_exp hsym (mul_nonneg hlam.le hs) (mul_le_mul_of_nonneg_left hst hlam.le),
      hΨcov lam hlam t (hs.trans hst), hΨcov lam hlam s hs]
  refine ⟨?_, ?_, hcov⟩
  · -- admissible: `F = F'(c ·)`, `c = χ(1)`
    obtain ⟨χ, P, hχ, -, hrep⟩ := exists_profile_of_fullCov hsym fun lam hlam =>
      ⟨_, hcov lam hlam⟩
    obtain ⟨Q, hQ⟩ := profile_exists_dilate P (isGauge_pos hχ one_pos)
    refine ⟨Q, fun r hr => ?_⟩
    have h1 := hF 1 one_pos r
    rw [one_mul, abs_of_nonneg hr, hrep 1 zero_le_one r] at h1
    rw [← h1, hQ]
  · -- `F ≢ 0`
    obtain ⟨χ, P, hχ, ⟨ω, hω⟩, hrep⟩ := exists_profile_of_fullCov hsym fun lam hlam =>
      ⟨_, hcov lam hlam⟩
    have hc := isGauge_pos hχ one_pos
    refine ⟨|ω| / χ 1, div_nonneg (abs_nonneg ω) hc.le, fun h0 => hω ?_⟩
    have h1 := hF 1 one_pos (|ω| / χ 1)
    have hcancel : χ 1 * (|ω| / χ 1) = |ω| := by field_simp
    rw [one_mul, abs_of_nonneg (div_nonneg (abs_nonneg ω) hc.le), hrep 1 zero_le_one,
      hcancel, profile_exponent_abs, h0] at h1
    exact h1

/-! ## (3) -/

/-- **`thm:annulus-parametrization-phase`(3).** A family in the canonical discrete gauge that is
`λ`-covariant for every `λ > 0` takes the form of (2) after the relabelling `t ↦ g(t)` by some
`g ∈ 𝒢_q`: `Ψ_t(ω) = F(g(t)|ω|)` with `F` admissible on `[0,∞)`, `F ≢ 0`. -/
theorem annulus_phase_3 {q : ℝ} (hq : 1 < q) (μ : ℝ → ℝ → Measure ℝ) (hμ : IsQFamily q μ)
    (hfull : ∀ lam : ℝ, 0 < lam → ∃ S : ℝ → ℝ, IsCovariantAt μ lam S) :
    ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧ ∃ F : ℝ → ℝ,
      (∀ t : ℝ, 0 < t → ∀ ω : ℝ, lineExponent μ t ω = F (g t * |ω|)) ∧
        (∃ P : SDProfile, ∀ r : ℝ, 0 ≤ r → F r = P.exponent r) ∧ ∃ r : ℝ, 0 ≤ r ∧ F r ≠ 0 := by
  have hq0 : 0 < q := by linarith
  obtain ⟨χ, P, hχ, hne, hrep⟩ := exists_profile_of_fullCov hμ.1 hfull
  -- `χ(qt) = qχ(t)`, by the injectivity of `r ↦ F(r ·)`
  have hχq : ∀ t : ℝ, 0 ≤ t → χ (q * t) = q * χ t := by
    intro t ht
    rcases ht.eq_or_lt with h0 | htpos
    · rw [← h0, mul_zero, hχ.1, mul_zero]
    refine eq_of_comp_mul_eq P.continuous_exponent (profile_exponent_zero P) hne
      (isGauge_pos hχ (mul_pos hq0 htpos)) (mul_pos hq0 (isGauge_pos hχ htpos)) fun ω => ?_
    rw [← hrep _ (mul_pos hq0 htpos).le, lineExponent_cov hμ ht, hrep t ht]
    ring_nf
  -- `χ` on `(0,∞)` lies in `𝒢_q` (`lem:gauge-group`(1) at the identity gauge)
  have hid : IsGauge (id : ℝ → ℝ) := ⟨rfl, strictMonoOn_id, surjOn_id _⟩
  obtain ⟨g, hg, hχg⟩ := (gauge_group_1 μ hq (fun t => q * t) hμ.2 id hid (fun t _ => rfl)).1 χ hχ
    (isGauge_continuousOn hχ) hχq
  refine ⟨g, hg, P.exponent, fun t ht ω => ?_, ⟨P, fun r _ => rfl⟩, ?_⟩
  · have hgt : χ t = g t := by
      rw [hχg t ht.le]
      simp [extendByZero, ht.ne']
    have hgpos : 0 < g t := hg.mapsTo ht
    rw [hrep t ht.le, hgt, ← profile_exponent_abs, abs_mul, abs_of_pos hgpos]
  · obtain ⟨ω, hω⟩ := hne
    exact ⟨|ω|, abs_nonneg ω, by rwa [profile_exponent_abs]⟩

end Pyramids
