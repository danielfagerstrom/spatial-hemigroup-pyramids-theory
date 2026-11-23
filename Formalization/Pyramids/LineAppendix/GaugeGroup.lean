/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Pyramid.Synthesis
import Pyramids.Defs.LineAppendix

/-!
# `lem:gauge-group`: the gauge group

Blueprint: `blueprint/src/parts/A1-line.tex`, `lem:gauge-group`. Wave 2d: the four declarations
moved here from `PyramidsSkeleton.ChA1Line`. Wave 2e (2026-11-14) dropped the unused hypotheses,
a strengthening: the family's symmetry in (1) and (4), and the continuity of `χ` and `χ'`, which
follows from their monotonicity (`isGauge_continuousOn`).

## The route

The printed one.

* **(1)** `g := χ'χ⁻¹` on `(0,∞)`, with `χ⁻¹` the inverse gauge (`incBij_inverse`); `χ⁻¹(qu) =
  S_q χ⁻¹(u)` gives `g(qu) = qg(u)`. Conversely `g χ`, `g` extended by `0`, is a strictly
  increasing map of `[0,∞)` onto itself, hence a gauge, hence continuous (`isGauge_continuousOn`).
  The family enters only through `S_q` mapping `[0,∞)` into itself.
* **(2)** `g̃ = log ∘ g ∘ exp` and `g = exp ∘ g̃ ∘ log`, with `g(qt) = qg(t)` read as
  `g̃(u + ℓ) = g̃(u) + ℓ`, `ℓ = log q`.
* **(3)** `g(qⁿu) = qⁿg(u)` for `n ∈ ℤ` gives uniqueness. Given `φ`, `g(qⁿu) := qⁿφ(u)`,
  `u ∈ [1, q)`, agrees with `qⁿφ(q^{-n} ·)` on each closed octave `[qⁿ, q^{n+1}]` by
  `φ(q) = qφ(1)`, so it is strictly increasing and continuous on each, hence on `(0,∞)`
  (`strictMonoOn_Ioi_of_octaves`, `continuousOn_Ioi_of_octaves`); it is onto by the intermediate
  value theorem on `[1, q]`.
* **(4)** With `χ(t₁) = 1`: `χ(S_λ t₁) = λ` and injectivity give `S_{χ(t)} t₁ = t`, so
  `χ'(t) = χ(t)χ'(t₁)`.
-/

set_option linter.unusedSectionVars false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open scoped Topology

/-! ## Gauges -/

theorem isGauge_pos {χ : ℝ → ℝ} (h : IsGauge χ) {t : ℝ} (ht : 0 < t) : 0 < χ t := by
  have h1 := h.2.1 (self_mem_Ici : (0 : ℝ) ∈ Ici 0) (mem_Ici.2 ht.le) ht
  rwa [h.1] at h1

theorem isGauge_eq_zero {χ : ℝ → ℝ} (h : IsGauge χ) {t : ℝ} (ht : 0 ≤ t) (h0 : χ t = 0) :
    t = 0 := by
  rcases ht.eq_or_lt with e | e
  · exact e.symm
  · exact absurd h0 (isGauge_pos h e).ne'

/-- The inverse of a gauge is a gauge. -/
theorem isGauge_inverse {χ : ℝ → ℝ} (h : IsGauge χ) :
    ∃ ψ : ℝ → ℝ, IsGauge ψ ∧ (∀ t : ℝ, 0 ≤ t → ψ (χ t) = t) ∧ ∀ t : ℝ, 0 ≤ t → χ (ψ t) = t := by
  obtain ⟨ψ, hψ, h1, h2⟩ := incBij_inverse ((isGauge_iff_isIncreasingBijection χ).1 h)
  exact ⟨ψ, (isGauge_iff_isIncreasingBijection ψ).2 hψ, h1, h2⟩

/-! ## Elements of `𝒢_q` -/

theorem IsInGaugeGroup.zpow {q : ℝ} (hq : 1 < q) {g : ℝ → ℝ} (hg : IsInGaugeGroup q g) :
    ∀ (n : ℤ) (u : ℝ), 0 < u → g (q ^ n * u) = q ^ n * g u := by
  have hq0 : 0 < q := by linarith
  have hnat : ∀ (k : ℕ) (u : ℝ), 0 < u → g (q ^ k * u) = q ^ k * g u := by
    intro k
    induction k with
    | zero => intro u _; simp
    | succ k ih =>
      intro u hu
      rw [pow_succ', mul_assoc, hg.equivariant _ (by positivity), ih u hu, mul_assoc]
  intro n u hu
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have := hnat k u hu
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using this
  · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hn.le
    subst hk
    have hqk : (0 : ℝ) < q ^ k := pow_pos hq0 k
    have h1 := hnat k (q ^ (-(k : ℤ)) * u) (by positivity)
    rw [← mul_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ hqk.ne', one_mul] at h1
    rw [zpow_neg, zpow_natCast, h1, ← mul_assoc, inv_mul_cancel₀ hqk.ne', one_mul]

/-! ## Functions built octave by octave -/

/-- **Continuity from the closed octaves**: a function continuous on every `[qⁿ, q^{n+1}]` is
continuous on `(0,∞)`. -/
theorem continuousOn_Ioi_of_octaves {q : ℝ} (hq : 1 < q) {f : ℝ → ℝ}
    (h : ∀ n : ℤ, ContinuousOn f (Icc (q ^ n) (q ^ (n + 1)))) : ContinuousOn f (Ioi 0) := by
  intro t ht
  obtain ⟨h1, h2⟩ := dgLevel_spec hq ht
  set n := dgLevel q t
  have hU : ContinuousOn f (Icc (q ^ (n - 1)) (q ^ (n + 1))) := by
    have e : Icc (q ^ (n - 1)) (q ^ (n + 1)) =
        Icc (q ^ (n - 1)) (q ^ (n - 1 + 1)) ∪ Icc (q ^ n) (q ^ (n + 1)) := by
      rw [sub_add_cancel, Icc_union_Icc_eq_Icc]
      · exact zpow_le_zpow_right₀ hq.le (by omega)
      · exact zpow_le_zpow_right₀ hq.le (by omega)
    rw [e]
    exact (h (n - 1)).union_of_isClosed (h n) isClosed_Icc isClosed_Icc
  have hlt : q ^ (n - 1) < t := lt_of_lt_of_le (zpow_lt_zpow_right₀ hq (by omega)) h1
  exact (hU.continuousAt (Icc_mem_nhds hlt h2)).continuousWithinAt

/-- **Strict monotonicity from the closed octaves**: a function strictly increasing on every
`[qⁿ, q^{n+1}]` is strictly increasing on `(0,∞)`. -/
theorem strictMonoOn_Ioi_of_octaves {q : ℝ} (hq : 1 < q) {f : ℝ → ℝ}
    (h : ∀ n : ℤ, StrictMonoOn f (Icc (q ^ n) (q ^ (n + 1)))) : StrictMonoOn f (Ioi 0) := by
  have hq0 : 0 < q := by linarith
  have knot : ∀ (n : ℤ), f (q ^ n) < f (q ^ (n + 1)) := fun n =>
    h n ⟨le_rfl, zpow_le_zpow_right₀ hq.le (by omega)⟩
      ⟨zpow_le_zpow_right₀ hq.le (by omega), le_rfl⟩ (zpow_lt_zpow_right₀ hq (by omega))
  have knots : ∀ (k : ℕ) (n : ℤ), f (q ^ n) ≤ f (q ^ (n + k)) := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      have e : n + ((k + 1 : ℕ) : ℤ) = n + k + 1 := by push_cast; ring
      rw [e]
      exact (ih n).trans (knot _).le
  intro s hs t ht hst
  obtain ⟨hs1, hs2⟩ := dgLevel_spec hq hs
  obtain ⟨ht1, ht2⟩ := dgLevel_spec hq ht
  set n := dgLevel q s
  set m := dgLevel q t
  have hnm : n ≤ m := by
    have : q ^ n < q ^ (m + 1) := lt_of_le_of_lt hs1 (hst.trans ht2)
    have := (zpow_lt_zpow_iff_right₀ hq).1 this
    omega
  rcases hnm.eq_or_lt with e | e
  · rw [← e] at ht1 ht2
    exact h n ⟨hs1, hs2.le⟩ ⟨ht1, ht2.le⟩ hst
  · -- `s < q^{n+1} ≤ q^m ≤ t`
    have h1 : f s < f (q ^ (n + 1)) :=
      h n ⟨hs1, hs2.le⟩ ⟨zpow_le_zpow_right₀ hq.le (by omega), le_rfl⟩ hs2
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 (show n + 1 ≤ m by omega))
    have h2 : f (q ^ (n + 1)) ≤ f (q ^ m) := by
      have := knots k (n + 1)
      rwa [show n + 1 + (k : ℤ) = m by omega] at this
    have h3 : f (q ^ m) ≤ f t := by
      rcases ht1.eq_or_lt with e' | e'
      · rw [e']
      · exact (h m ⟨le_rfl, zpow_le_zpow_right₀ hq.le (by omega)⟩ ⟨ht1, ht2.le⟩ e').le
    exact lt_of_lt_of_le h1 (h2.trans h3)

/-! ## `lem:gauge-group` -/

/-- **`lem:gauge-group`(1).** For a `q`-covariant family with the bijection `S_q`, two increasing
homeomorphisms `χ, χ'` of `[0,∞)` with `χS_q = qχ`, `χ'S_q = qχ'` satisfy `χ' = gχ` for some
`g ∈ 𝒢_q` (extended by `g(0) := 0`), and `gχ` is such a homeomorphism for every `g ∈ 𝒢_q`. -/
theorem gauge_group_1 (μ : ℝ → ℝ → Measure ℝ) {q : ℝ} (hq : 1 < q)
    (S : ℝ → ℝ) (hS : IsCovariantAt μ q S) (χ : ℝ → ℝ) (hχ : IsGauge χ)
    (hχS : ∀ t : ℝ, 0 ≤ t → χ (S t) = q * χ t) :
    (∀ χ' : ℝ → ℝ, IsGauge χ' → ContinuousOn χ' (Ici 0) → (∀ t : ℝ, 0 ≤ t → χ' (S t) = q * χ' t) →
        ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧ ∀ t : ℝ, 0 ≤ t → χ' t = extendByZero g (χ t)) ∧
      ∀ g : ℝ → ℝ, IsInGaugeGroup q g →
        IsGauge (fun t => extendByZero g (χ t)) ∧
          ContinuousOn (fun t => extendByZero g (χ t)) (Ici 0) ∧
          ∀ t : ℝ, 0 ≤ t → extendByZero g (χ (S t)) = q * extendByZero g (χ t) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨ψ, hψ, hψχ, hχψ⟩ := isGauge_inverse hχ
  refine ⟨fun χ' hχ' hχ'c hχ'S => ?_, fun g hg => ?_⟩
  · -- `g := χ' ∘ ψ`
    have hψpos : ∀ u : ℝ, 0 < u → 0 < ψ u := fun u hu => isGauge_pos hψ hu
    refine ⟨fun u => χ' (ψ u), ⟨?_, ?_, ?_, ?_, ?_⟩, fun t ht => ?_⟩
    · intro a ha b hb hab
      exact hχ'.2.1 (mem_Ici.2 (hψpos a ha).le) (mem_Ici.2 (hψpos b hb).le)
        (hψ.2.1 (mem_Ici.2 (le_of_lt ha)) (mem_Ici.2 (le_of_lt hb)) hab)
    · intro u hu
      exact isGauge_pos hχ' (hψpos u hu)
    · intro v hv
      obtain ⟨s, hs, hsv⟩ := hχ'.2.2 (mem_Ici.2 (le_of_lt hv))
      have hs0 : 0 < s := by
        rcases (mem_Ici.1 hs).eq_or_lt with e | e
        · rw [← e, hχ'.1] at hsv; exact absurd hsv (ne_of_lt hv)
        · exact e
      refine ⟨χ s, isGauge_pos hχ hs0, ?_⟩
      change χ' (ψ (χ s)) = v
      rw [hψχ s hs, hsv]
    · have hmapsψ : MapsTo ψ (Ici 0) (Ici 0) :=
        ((isGauge_iff_isIncreasingBijection ψ).1 hψ).mapsTo
      exact (hχ'c.comp (isGauge_continuousOn hψ) hmapsψ).mono Ioi_subset_Ici_self
    · intro u hu
      have hu0 : 0 ≤ ψ u := (hψpos u hu).le
      have hSψ : 0 ≤ S (ψ u) := hS.1.mapsTo hu0
      have e : ψ (q * u) = S (ψ u) := by
        have h1 : χ (S (ψ u)) = q * u := by rw [hχS _ hu0, hχψ u hu.le]
        rw [← h1, hψχ _ hSψ]
      change χ' (ψ (q * u)) = q * χ' (ψ u)
      rw [e, hχ'S _ hu0]
    · simp only [extendByZero]
      split_ifs with h0
      · rw [isGauge_eq_zero hχ ht h0, hχ'.1]
      · rw [hψχ t ht]
  · -- `g ∘ χ`
    have hgχ : IsGauge (fun t => extendByZero g (χ t)) := by
      refine ⟨by simp [extendByZero, hχ.1], ?_, ?_⟩
      · intro a ha b hb hab
        have hb0 : 0 < b := lt_of_le_of_lt ha hab
        have hχb : 0 < χ b := isGauge_pos hχ hb0
        simp only [extendByZero, if_neg hχb.ne']
        rcases (mem_Ici.1 ha).eq_or_lt with e | e
        · rw [← e, hχ.1, if_pos rfl]
          exact hg.mapsTo hχb
        · have hχa : 0 < χ a := isGauge_pos hχ e
          rw [if_neg hχa.ne']
          exact hg.strictMonoOn hχa hχb (hχ.2.1 ha hb hab)
      · intro y hy
        rcases (mem_Ici.1 hy).eq_or_lt with e | e
        · exact ⟨0, self_mem_Ici, by simp [extendByZero, hχ.1, ← e]⟩
        · obtain ⟨u, hu, rfl⟩ := hg.surjOn e
          obtain ⟨t, ht, htu⟩ := hχ.2.2 (mem_Ici.2 (le_of_lt hu))
          refine ⟨t, ht, ?_⟩
          simp only [extendByZero]
          rw [htu, if_neg (ne_of_gt hu)]
    refine ⟨hgχ, isGauge_continuousOn hgχ, fun t ht => ?_⟩
    simp only [extendByZero]
    rw [hχS t ht]
    by_cases h0 : χ t = 0
    · simp [h0]
    · have hχt : 0 < χ t := lt_of_le_of_ne (by
        rcases ht.eq_or_lt with e | e
        · rw [← e, hχ.1]
        · exact (isGauge_pos hχ e).le) (Ne.symm h0)
      rw [if_neg (mul_ne_zero hq0.ne' h0), if_neg h0, hg.equivariant _ hχt]

/-- **`lem:gauge-group`(2).** `g ↦ g̃`, `g̃(u) = log g(e^u)`, is an isomorphism of `𝒢_q` onto the
increasing homeomorphisms `g̃` of `ℝ` with `g̃(u + ℓ) = g̃(u) + ℓ`: it lands there, is onto, is
injective (elements of `𝒢_q` being read on `(0,∞)`), and turns composition into composition. -/
theorem gauge_group_2 {q : ℝ} (hq : 1 < q) :
    (∀ g : ℝ → ℝ, IsInGaugeGroup q g → IsCircleLift (Real.log q) (logConj g)) ∧
      (∀ G : ℝ → ℝ, IsCircleLift (Real.log q) G → ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧ logConj g = G) ∧
      (∀ g g' : ℝ → ℝ, IsInGaugeGroup q g → IsInGaugeGroup q g' → logConj g = logConj g' →
        EqOn g g' (Ioi 0)) ∧
      ∀ g g' : ℝ → ℝ, IsInGaugeGroup q g → IsInGaugeGroup q g' →
        IsInGaugeGroup q (g ∘ g') ∧ logConj (g ∘ g') = logConj g ∘ logConj g' := by
  have hq0 : 0 < q := by linarith
  refine ⟨fun g hg => ?_, fun G hG => ?_, fun g g' hg hg' he t ht => ?_, fun g g' hg hg' => ?_⟩
  · -- the map lands among the lifts
    have hpos : ∀ u : ℝ, 0 < g (Real.exp u) := fun u => hg.mapsTo (Real.exp_pos u)
    refine ⟨fun a b hab => ?_, ?_, fun v => ?_, fun u => ?_⟩
    · exact Real.log_lt_log (hpos a)
        (hg.strictMonoOn (Real.exp_pos a) (Real.exp_pos b) (Real.exp_lt_exp.2 hab))
    · have hc : Continuous fun u => g (Real.exp u) :=
        hg.continuousOn.comp_continuous Real.continuous_exp fun u => Real.exp_pos u
      exact hc.log fun u => (hpos u).ne'
    · obtain ⟨s, hs, hsv⟩ := hg.surjOn (Real.exp_pos v)
      refine ⟨Real.log s, ?_⟩
      simp only [logConj]
      rw [Real.exp_log hs, hsv, Real.log_exp]
    · simp only [logConj]
      rw [Real.exp_add, Real.exp_log hq0, mul_comm, hg.equivariant _ (Real.exp_pos u),
        Real.log_mul hq0.ne' (hpos u).ne']
      ring
  · -- the inverse map
    obtain ⟨hmono, hcont, hsurj, hper⟩ := hG
    refine ⟨fun t => Real.exp (G (Real.log t)), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro a ha b hb hab
      exact Real.exp_lt_exp.2 (hmono (Real.log_lt_log ha hab))
    · intro t _
      exact Real.exp_pos _
    · intro y hy
      obtain ⟨u, hu⟩ := hsurj (Real.log y)
      refine ⟨Real.exp u, Real.exp_pos u, ?_⟩
      simp only [Real.log_exp, hu, Real.exp_log hy]
    · exact (Real.continuous_exp.comp_continuousOn (hcont.comp_continuousOn
        (Real.continuousOn_log.mono fun t ht => ne_of_gt ht)))
    · intro t ht
      rw [Real.log_mul hq0.ne' ht.ne', add_comm, hper, Real.exp_add, Real.exp_log hq0, mul_comm]
    · funext u
      simp only [logConj, Real.log_exp]
  · -- injectivity
    have h1 := congrFun he (Real.log t)
    simp only [logConj, Real.exp_log ht] at h1
    exact Real.log_injOn_pos (hg.mapsTo ht) (hg'.mapsTo ht) h1
  · -- composition
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro a ha b hb hab
      exact hg.strictMonoOn (hg'.mapsTo ha) (hg'.mapsTo hb) (hg'.strictMonoOn ha hb hab)
    · intro t ht
      exact hg.mapsTo (hg'.mapsTo ht)
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := hg.surjOn hy
      obtain ⟨v, hv, rfl⟩ := hg'.surjOn hu
      exact ⟨v, hv, rfl⟩
    · exact hg.continuousOn.comp hg'.continuousOn fun t ht => hg'.mapsTo ht
    · intro t ht
      simp only [Function.comp_apply]
      rw [hg'.equivariant t ht, hg.equivariant _ (hg'.mapsTo ht)]
    · funext u
      simp only [logConj, Function.comp_apply]
      rw [Real.exp_log (hg'.mapsTo (Real.exp_pos u))]

/-- **`lem:gauge-group`(3).** Restriction to `[1,q]` is a bijection of `𝒢_q` onto the continuous,
strictly increasing `φ : [1,q] → (0,∞)` with `φ(q) = qφ(1)`. -/
theorem gauge_group_3 {q : ℝ} (hq : 1 < q) :
    (∀ g : ℝ → ℝ, IsInGaugeGroup q g →
        ContinuousOn g (Icc 1 q) ∧ StrictMonoOn g (Icc 1 q) ∧ MapsTo g (Icc 1 q) (Ioi 0) ∧
          g q = q * g 1) ∧
      (∀ g g' : ℝ → ℝ, IsInGaugeGroup q g → IsInGaugeGroup q g' → EqOn g g' (Icc 1 q) →
        EqOn g g' (Ioi 0)) ∧
      ∀ φ : ℝ → ℝ, ContinuousOn φ (Icc 1 q) → StrictMonoOn φ (Icc 1 q) →
        MapsTo φ (Icc 1 q) (Ioi 0) → φ q = q * φ 1 →
          ∃ g : ℝ → ℝ, IsInGaugeGroup q g ∧ EqOn g φ (Icc 1 q) := by
  have hq0 : 0 < q := by linarith
  have hsub : Icc 1 q ⊆ Ioi (0 : ℝ) := fun u hu => lt_of_lt_of_le one_pos hu.1
  refine ⟨fun g hg => ⟨hg.continuousOn.mono hsub, hg.strictMonoOn.mono hsub,
    fun u hu => hg.mapsTo (hsub hu), by simpa using hg.equivariant 1 one_pos⟩,
    fun g g' hg hg' he t ht => ?_, fun φ hφc hφm hφp hφq => ?_⟩
  · -- the restriction determines the element
    obtain ⟨h1, h2⟩ := dgLevel_spec hq ht
    have hu := octave_mem hq ht
    have hqn : 0 < q ^ dgLevel q t := zpow_pos hq0 _
    have et : t = q ^ dgLevel q t * (q ^ (-dgLevel q t) * t) := by
      rw [zpow_neg, mul_inv_cancel_left₀ hqn.ne']
    have hu0 : 0 < q ^ (-dgLevel q t) * t := lt_of_lt_of_le one_pos hu.1
    rw [et, hg.zpow hq _ _ hu0, hg'.zpow hq _ _ hu0, he ⟨hu.1, hu.2.le⟩]
  · -- the extension of `φ`
    set g : ℝ → ℝ := fun t => q ^ dgLevel q t * φ (q ^ (-dgLevel q t) * t) with hgdef
    -- `g(qⁿu) = qⁿφ(u)` on the closed octave
    have hoct : ∀ (n : ℤ) (u : ℝ), u ∈ Icc 1 q → g (q ^ n * u) = q ^ n * φ u := by
      intro n u hu
      have hqn : 0 < q ^ n := zpow_pos hq0 n
      rcases hu.2.lt_or_eq with hlt | heq
      · have hlev : dgLevel q (q ^ n * u) = n := by
          refine dgLevel_eq hq (le_mul_of_one_le_right hqn.le hu.1) ?_
          rw [zpow_add_one₀ hq0.ne']; exact mul_lt_mul_of_pos_left hlt hqn
        simp only [hgdef, hlev]
        rw [zpow_neg, inv_mul_cancel_left₀ hqn.ne']
      · rw [heq]
        have hlev : dgLevel q (q ^ n * q) = n + 1 := by
          refine dgLevel_eq hq (by rw [zpow_add_one₀ hq0.ne']) ?_
          rw [zpow_add_one₀ hq0.ne', zpow_add_one₀ hq0.ne']
          exact lt_mul_of_one_lt_right (mul_pos hqn hq0) hq
        have hτ : q ^ (-(n + 1)) * (q ^ n * q) = 1 := by
          rw [← zpow_add_one₀ hq0.ne', ← zpow_add₀ hq0.ne']; simp
        simp only [hgdef, hlev, hτ]
        rw [hφq, zpow_add_one₀ hq0.ne']
        ring
    -- on the closed octave `[qⁿ, q^{n+1}]`, `g = qⁿφ(q^{-n} ·)`
    have hmaps : ∀ n : ℤ, MapsTo (fun t => q ^ (-n) * t) (Icc (q ^ n) (q ^ (n + 1))) (Icc 1 q) := by
      intro n t ht
      have hqn : 0 < q ^ n := zpow_pos hq0 n
      refine ⟨?_, ?_⟩
      · rw [zpow_neg, le_inv_mul_iff₀ hqn, mul_one]; exact ht.1
      · rw [zpow_neg, inv_mul_le_iff₀ hqn, ← zpow_add_one₀ hq0.ne']; exact ht.2
    have hon : ∀ n : ℤ, EqOn g (fun t => q ^ n * φ (q ^ (-n) * t)) (Icc (q ^ n) (q ^ (n + 1))) := by
      intro n t ht
      have hqn : 0 < q ^ n := zpow_pos hq0 n
      have et : t = q ^ n * (q ^ (-n) * t) := by rw [zpow_neg, mul_inv_cancel_left₀ hqn.ne']
      change g t = _
      conv_lhs => rw [et]
      exact hoct n _ (hmaps n ht)
    have hgc : ContinuousOn g (Ioi 0) := continuousOn_Ioi_of_octaves hq fun n =>
      ((continuousOn_const.mul (hφc.comp (continuous_const.mul continuous_id).continuousOn
        (hmaps n)))).congr (hon n)
    have hgm : StrictMonoOn g (Ioi 0) := strictMonoOn_Ioi_of_octaves hq fun n => by
      intro a ha b hb hab
      rw [hon n ha, hon n hb]
      exact mul_lt_mul_of_pos_left (hφm (hmaps n ha) (hmaps n hb)
        (mul_lt_mul_of_pos_left hab (zpow_pos hq0 _))) (zpow_pos hq0 n)
    have hφ1 : 0 < φ 1 := hφp ⟨le_rfl, hq.le⟩
    refine ⟨g, ⟨hgm, fun t ht => ?_, fun y hy => ?_, hgc, fun t ht => ?_⟩, fun u hu => ?_⟩
    · -- positive
      have hu := octave_mem hq ht
      exact mul_pos (zpow_pos hq0 _) (hφp ⟨hu.1, hu.2.le⟩)
    · -- onto: the intermediate value theorem on `[1, q]`
      have hyc : 0 < y / φ 1 := div_pos hy hφ1
      set m := dgLevel q (y / φ 1)
      have hw := octave_mem hq hyc
      set w := q ^ (-m) * (y / φ 1)
      have hw' : φ 1 * w ∈ Icc (φ 1) (φ q) := by
        rw [hφq]
        exact ⟨le_mul_of_one_le_right hφ1.le hw.1, by
          rw [mul_comm q]; exact (mul_lt_mul_of_pos_left hw.2 hφ1).le⟩
      obtain ⟨u, hu, hφu⟩ := intermediate_value_Icc hq.le hφc hw'
      refine ⟨q ^ m * u, mul_pos (zpow_pos hq0 m) (lt_of_lt_of_le one_pos hu.1), ?_⟩
      rw [hoct m u hu, hφu]
      simp only [w]
      rw [zpow_neg]
      field_simp
    · -- equivariant
      have hu := octave_mem hq ht
      have hqn : 0 < q ^ dgLevel q t := zpow_pos hq0 _
      have et : t = q ^ dgLevel q t * (q ^ (-dgLevel q t) * t) := by
        rw [zpow_neg, mul_inv_cancel_left₀ hqn.ne']
      have eqt : q * t = q ^ (dgLevel q t + 1) * (q ^ (-dgLevel q t) * t) := by
        conv_lhs => rw [et]
        rw [zpow_add_one₀ hq0.ne']; ring
      rw [eqt, hoct _ _ ⟨hu.1, hu.2.le⟩]
      conv_rhs => rw [et, hoct _ _ ⟨hu.1, hu.2.le⟩]
      rw [zpow_add_one₀ hq0.ne']; ring
    · -- agrees with `φ` on `[1, q]`
      have := hoct 0 u hu
      simpa using this

/-- **`lem:gauge-group`(4).** For a family `λ`-covariant for every `λ > 0` with the bijections
`S_λ`, two increasing homeomorphisms `χ, χ'` of `[0,∞)` with `χS_λ = λχ`, `χ'S_λ = λχ'` for every
`λ > 0` satisfy `χ' = cχ` for a constant `c > 0`. -/
theorem gauge_group_4 (μ : ℝ → ℝ → Measure ℝ) (S : ℝ → ℝ → ℝ)
    (hS : ∀ lam : ℝ, 0 < lam → IsCovariantAt μ lam (S lam)) (χ χ' : ℝ → ℝ) (hχ : IsGauge χ)
    (hχS : ∀ lam : ℝ, 0 < lam → ∀ t : ℝ, 0 ≤ t → χ (S lam t) = lam * χ t) (hχ' : IsGauge χ')
    (hχ'S : ∀ lam : ℝ, 0 < lam → ∀ t : ℝ, 0 ≤ t → χ' (S lam t) = lam * χ' t) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t → χ' t = c * χ t := by
  obtain ⟨t₁, ht₁, h1⟩ := hχ.2.2 (mem_Ici.2 zero_le_one)
  have ht₁0 : 0 < t₁ := by
    rcases (mem_Ici.1 ht₁).eq_or_lt with e | e
    · rw [← e, hχ.1] at h1; norm_num at h1
    · exact e
  refine ⟨χ' t₁, isGauge_pos hχ' ht₁0, fun t ht => ?_⟩
  rcases ht.eq_or_lt with e | e
  · rw [← e, hχ.1, hχ'.1, mul_zero]
  · have hl : 0 < χ t := isGauge_pos hχ e
    have hSt : 0 ≤ S (χ t) t₁ := (hS _ hl).1.mapsTo ht₁
    have h2 : χ (S (χ t) t₁) = χ t := by rw [hχS _ hl t₁ ht₁, h1, mul_one]
    have h3 : S (χ t) t₁ = t := hχ.2.1.injOn hSt ht h2
    calc χ' t = χ' (S (χ t) t₁) := by rw [h3]
      _ = χ t * χ' t₁ := hχ'S _ hl t₁ ht₁
      _ = χ' t₁ * χ t := mul_comm _ _

end Pyramids
