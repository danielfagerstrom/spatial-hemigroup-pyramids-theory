/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.MaternGenerator

/-!
# `prop:creation-plane`(1): one step creates a local maximum

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:creation-plane`. Phase 5, wave 3b (on the
VM). `creation_plane_1` moved here from `PyramidsSkeleton.Ch04Matern`; review round 2
dropped `μ̂ ≥ 0`.

* **The witness.** `h_{a,δ}(x) = P(x₁, |x'|²)` with `P(s, r)` strictly decreasing in `r` and, at
  `r = 0`, even and strictly decreasing in `|s|` (`cwProfile`): the bumps' axis profile `φ` has
  `φ'(s) ≤ s` for `s ≥ 0`, since `y ↦ y e^{-y²/2} + y/2` is nondecreasing, and the ridge's
  derivative is at most `-2e^{-1/8}s` on `(0, a]`. So `0` is the only local maximum, and from any
  point of `{h > C}` the path that moves `x'` to `0`, then `x₁` to `0`, stays in it.
* **The bumps.** `W := μ * e^{-|·|²/2}` is continuous, positive, and tends to `0` at infinity, for
  every probability `μ`; take `r ≥ 1` with `W < W(0)/4` off `B_r` and `a := r + 1`. (The earlier
  route, `W(0) > max_{|x|=1} W` by Fourier inversion, needed `μ̂ ≥ 0`; review round 2 dropped it.)
* **The ridge.** With `K` the density of `μ`, `K R ≤ M R + 8a² (K - M)⁺` pointwise, so
  `μ * R ≤ M‖R‖₁ + 8a²∫(K - M)⁺`; both terms tend to `0`, the first by dominated convergence as
  `δ → 0`, the line `x' = 0` being null in `d ≥ 2`.
* **Two maxima.** `μ * h` is at least `W(0)` at `±ae₁` and below `3W(0)/4` on the spheres of
  radius `r` about them, so it has a local maximum inside each ball, and those spheres separate
  `{μ * h > 3W(0)/4}`.
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (mconvE)
open scoped Topology ENNReal RealInnerProductSpace ComplexOrder

/-! ## The profile of the witness -/

/-- **`P(s, r)`**: `h_{a,δ}(x) = P(x₁, |x'|²)`. -/
noncomputable def cwProfile (a δ s r : ℝ) : ℝ :=
  (Real.exp (-(s - a) ^ 2 / 2) + Real.exp (-(s + a) ^ 2 / 2)) * Real.exp (-r / 2) +
    8 * a ^ 2 * Real.exp (-s ^ 2 / (8 * a ^ 2)) * Real.exp (-r / (2 * δ ^ 2))

theorem cwProfile_strictAnti {a δ : ℝ} (ha : a ≠ 0) (hδ : δ ≠ 0) (s : ℝ) :
    StrictAnti (cwProfile a δ s) := by
  intro r r' hr
  unfold cwProfile
  have h1 : Real.exp (-r' / 2) < Real.exp (-r / 2) := Real.exp_lt_exp.2 (by linarith)
  have h2 : Real.exp (-r' / (2 * δ ^ 2)) < Real.exp (-r / (2 * δ ^ 2)) :=
    Real.exp_lt_exp.2 (div_lt_div_of_pos_right (by linarith) (by positivity))
  have hA : 0 < Real.exp (-(s - a) ^ 2 / 2) + Real.exp (-(s + a) ^ 2 / 2) := by positivity
  have hB : 0 < 8 * a ^ 2 * Real.exp (-s ^ 2 / (8 * a ^ 2)) := by positivity
  nlinarith [mul_lt_mul_of_pos_left h1 hA, mul_lt_mul_of_pos_left h2 hB]

theorem cwProfile_neg (a δ s : ℝ) : cwProfile a δ (-s) 0 = cwProfile a δ s 0 := by
  unfold cwProfile
  have e1 : -(-s - a) ^ 2 / 2 = -(s + a) ^ 2 / 2 := by ring
  have e2 : -(-s + a) ^ 2 / 2 = -(s - a) ^ 2 / 2 := by ring
  rw [e1, e2, neg_sq]
  ring

/-- `y ↦ y e^{-y²/2} + y/2` is nondecreasing: `(y² - 1) e^{-y²/2} ≤ 1/2`. -/
theorem monotone_kfun : Monotone fun y : ℝ => y * Real.exp (-y ^ 2 / 2) + y / 2 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y * Real.exp (-y ^ 2 / 2) + y / 2)
      ((1 - y ^ 2) * Real.exp (-y ^ 2 / 2) + 1 / 2) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-y) y := by
      have := ((hasDerivAt_pow 2 y).neg).div_const 2
      refine this.congr_deriv ?_
      norm_num
      ring
    have h2 := (hasDerivAt_id y).mul h1.exp
    have h3 := h2.add ((hasDerivAt_id y).div_const 2)
    refine h3.congr_deriv ?_
    simp only [id]
    ring
  refine monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt) fun y => ?_
  rw [(hd y).deriv]
  -- `(y² - 1) e^{-y²/2} ≤ 1/2`, from `e^t ≥ 4t - 2` at `t = y²/2`
  set t := y ^ 2 / 2 with ht
  have hexp : Real.exp (-y ^ 2 / 2) = (Real.exp t)⁻¹ := by
    rw [← Real.exp_neg, ht, neg_div]
  have he : 4 * t - 2 ≤ Real.exp t := by
    have h15 : (4 : ℝ) ≤ Real.exp (3 / 2) := by
      have hq := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
      have : Real.exp (3 / 2) = Real.exp (1 / 2) ^ 3 := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num
      rw [this]
      have hu : (13 / 8 : ℝ) ≤ Real.exp (1 / 2) := by linarith
      have := pow_le_pow_left₀ (by norm_num) hu 3
      linarith
    have hl := Real.add_one_le_exp (t - 3 / 2)
    have hsplit : Real.exp t = Real.exp (3 / 2) * Real.exp (t - 3 / 2) := by
      rw [← Real.exp_add]; ring_nf
    rcases le_or_gt (1 / 2) t with h | h
    · rw [hsplit]
      nlinarith [Real.exp_pos (t - 3 / 2)]
    · nlinarith [Real.exp_pos t]
  rw [hexp]
  have hpos := Real.exp_pos t
  rw [show (1 - y ^ 2) = 1 - 2 * t by rw [ht]; ring]
  have : (1 - 2 * t) * (Real.exp t)⁻¹ ≥ -1 / 2 := by
    rw [ge_iff_le, ← sub_nonneg]
    have : (1 - 2 * t) * (Real.exp t)⁻¹ - -1 / 2 =
        ((2 - 4 * t) + Real.exp t) / (2 * Real.exp t) := by
      field_simp
      ring
    rw [this]
    exact div_nonneg (by linarith) (by positivity)
  linarith

/-- The axis profile `g(s) := P(s, 0)` has a negative derivative on `(0, ∞)`. -/
theorem hasDerivAt_cwAxis {a : ℝ} (ha : a ≠ 0) (δ s : ℝ) :
    HasDerivAt (fun s => cwProfile a δ s 0)
      ((a - s) * Real.exp (-(a - s) ^ 2 / 2) - (a + s) * Real.exp (-(a + s) ^ 2 / 2) -
        2 * s * Real.exp (-s ^ 2 / (8 * a ^ 2))) s := by
  have hg : ∀ (b c : ℝ), HasDerivAt (fun s : ℝ => -(s + b) ^ 2 / c) (-(2 * (s + b)) / c) s := by
    intro b c
    have := (((hasDerivAt_id s).add_const b).pow 2).neg.div_const c
    refine this.congr_deriv ?_
    simp only [id, Nat.cast_ofNat]
    ring
  have h1 := (hg (-a) 2).exp
  have h2 := (hg a 2).exp
  have h3 := ((hg 0 (8 * a ^ 2)).exp).const_mul (8 * a ^ 2)
  have h := (h1.add h2).add h3
  have hf : (fun s => cwProfile a δ s 0) = fun s => Real.exp (-(s + -a) ^ 2 / 2) +
      Real.exp (-(s + a) ^ 2 / 2) + 8 * a ^ 2 * Real.exp (-(s + 0) ^ 2 / (8 * a ^ 2)) := by
    funext s
    simp [cwProfile, sub_eq_add_neg]
  rw [hf]
  refine h.congr_deriv ?_
  have e1 : -(a - s) ^ 2 / 2 = -(s + -a) ^ 2 / 2 := by ring
  have e2 : -(a + s) ^ 2 / 2 = -(s + a) ^ 2 / 2 := by ring
  rw [e1, e2, add_zero]
  field_simp
  ring

theorem cwAxis_strictAntiOn {a δ : ℝ} (ha : 1 < a) :
    StrictAntiOn (fun s => cwProfile a δ s 0) (Ici 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0)
    (fun s _ => (hasDerivAt_cwAxis (by linarith : a ≠ 0) δ s).continuousAt.continuousWithinAt)
    fun s hs => ?_
  rw [interior_Ici] at hs
  have hs : 0 < s := hs
  rw [(hasDerivAt_cwAxis (by linarith : a ≠ 0) δ s).deriv]
  have hE : 0 < Real.exp (-s ^ 2 / (8 * a ^ 2)) := Real.exp_pos _
  rcases le_or_gt s a with hsa | hsa
  · -- `k(a - s) - k(a + s) ≤ s` and the ridge term is at most `-2·(7/8)s`
    have hk := monotone_kfun (show a - s ≤ a + s by linarith)
    simp only at hk
    have h78 : 7 / 8 ≤ Real.exp (-s ^ 2 / (8 * a ^ 2)) := by
      have := Real.add_one_le_exp (-s ^ 2 / (8 * a ^ 2))
      have hq : s ^ 2 / (8 * a ^ 2) ≤ 1 / 8 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have : -s ^ 2 / (8 * a ^ 2) = -(s ^ 2 / (8 * a ^ 2)) := by ring
      linarith
    nlinarith
  · have h1 : (a - s) * Real.exp (-(a - s) ^ 2 / 2) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)
    have h2 : 0 < (a + s) * Real.exp (-(a + s) ^ 2 / 2) :=
      mul_pos (by linarith) (Real.exp_pos _)
    nlinarith

/-- `g(s') < g(s)` when `|s| < |s'|`, and `g(s') ≤ g(s)` when `|s| ≤ |s'|`. -/
theorem cwAxis_lt_of_abs_lt {a δ : ℝ} (ha : 1 < a) {s s' : ℝ} (h : |s| < |s'|) :
    cwProfile a δ s' 0 < cwProfile a δ s 0 := by
  have e : ∀ u, cwProfile a δ u 0 = cwProfile a δ |u| 0 := fun u => by
    rcases abs_choice u with hu | hu <;> rw [hu]
    rw [cwProfile_neg]
  rw [e s, e s']
  exact cwAxis_strictAntiOn ha (abs_nonneg s) (abs_nonneg s') h

theorem cwAxis_le_of_abs_le {a δ : ℝ} (ha : 1 < a) {s s' : ℝ} (h : |s| ≤ |s'|) :
    cwProfile a δ s' 0 ≤ cwProfile a δ s 0 := by
  rcases h.lt_or_eq with h | h
  · exact (cwAxis_lt_of_abs_lt ha h).le
  · have e : ∀ u, cwProfile a δ u 0 = cwProfile a δ |u| 0 := fun u => by
      rcases abs_choice u with hu | hu <;> rw [hu]
      rw [cwProfile_neg]
    rw [e s, e s', h]

/-! ## The witness in the coordinates `(x₁, |x'|²)` -/

variable {d : ℕ} [NeZero d]

/-- `|x'|² = |x - x₁e₁|²`. -/
noncomputable def trv (x : Rd d) : ℝ := ‖x - x 0 • ebasis 0‖ ^ 2

theorem inner_ebasis0 (x : Rd d) : ⟪x, ebasis 0⟫ = x 0 := by
  simp [ebasis, EuclideanSpace.inner_single_right]

theorem norm_ebasis0 : ‖(ebasis 0 : Rd d)‖ = 1 := by
  simp [ebasis]

theorem norm_sub_smul_ebasis0_sq (x : Rd d) (b : ℝ) :
    ‖x - b • ebasis 0‖ ^ 2 = (x 0 - b) ^ 2 + trv x := by
  have key : ∀ c : ℝ, ‖x - c • ebasis 0‖ ^ 2 = ‖x‖ ^ 2 - 2 * c * x 0 + c ^ 2 := by
    intro c
    rw [norm_sub_sq_real, real_inner_smul_right, inner_ebasis0, norm_smul, norm_ebasis0,
      Real.norm_eq_abs, mul_one, sq_abs]
    ring
  rw [trv, key, key]
  ring

theorem trv_eq (x : Rd d) : trv x = ‖x‖ ^ 2 - x 0 ^ 2 := by
  have h := norm_sub_smul_ebasis0_sq x 0
  rw [zero_smul, sub_zero, sub_zero] at h
  linarith

theorem trv_nonneg (x : Rd d) : 0 ≤ trv x := sq_nonneg _

theorem creationWitness_eq (a δ : ℝ) (x : Rd d) :
    creationWitness d a δ x = cwProfile a δ (x 0) (trv x) := by
  have hp : ‖x + a • ebasis 0‖ ^ 2 = (x 0 + a) ^ 2 + trv x := by
    have := norm_sub_smul_ebasis0_sq x (-a)
    rw [neg_smul, sub_neg_eq_add, sub_neg_eq_add] at this
    exact this
  rw [creationWitness, norm_sub_smul_ebasis0_sq, hp, cwProfile, ← trv_eq]
  have e1 : -((x 0 - a) ^ 2 + trv x) / 2 = -(x 0 - a) ^ 2 / 2 + -trv x / 2 := by ring
  have e2 : -((x 0 + a) ^ 2 + trv x) / 2 = -(x 0 + a) ^ 2 / 2 + -trv x / 2 := by ring
  rw [e1, e2, Real.exp_add, Real.exp_add, neg_div (2 * δ ^ 2)]
  ring

theorem trv_sub_smul (x : Rd d) (t : ℝ) : trv (x - t • (x - x 0 • ebasis 0)) = (1 - t) ^ 2 * trv x ∧
    (x - t • (x - x 0 • ebasis 0) : Rd d) 0 = x 0 := by
  have h0 : (x - t • (x - x 0 • ebasis 0) : Rd d) 0 = x 0 := by
    simp [ebasis]
  refine ⟨?_, h0⟩
  rw [trv, h0, trv]
  have : x - t • (x - x 0 • ebasis 0) - x 0 • ebasis 0 = (1 - t) • (x - x 0 • ebasis 0) := by
    rw [sub_smul, one_smul]; abel
  rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem trv_smul (x : Rd d) (t : ℝ) : trv (t • x) = t ^ 2 * trv x := by
  rw [trv_eq, trv_eq, norm_smul, PiLp.smul_apply, smul_eq_mul, mul_pow, Real.norm_eq_abs, sq_abs,
    mul_pow]
  ring

/-- **The witness has the global maximum at `0`.** -/
theorem creationWitness_le_zero {a δ : ℝ} (ha : 1 < a) (hδ : 0 < δ) (x : Rd d) :
    creationWitness d a δ x ≤ creationWitness d a δ 0 := by
  rw [creationWitness_eq, creationWitness_eq]
  have h0 : trv (0 : Rd d) = 0 := by simp [trv]
  rw [h0]
  calc cwProfile a δ (x 0) (trv x) ≤ cwProfile a δ (x 0) 0 :=
        (cwProfile_strictAnti (by linarith) hδ.ne' _).antitone (trv_nonneg x)
    _ ≤ cwProfile a δ ((0 : Rd d) 0) 0 := cwAxis_le_of_abs_le ha (by simp)

omit [NeZero d] in
/-- A point from which a continuous path strictly increases `f` is not a local maximum. -/
theorem not_isLocalMax_of_path {f : Rd d → ℝ} {x : Rd d} (y : ℝ → Rd d) (hy : Continuous y)
    (hy0 : y 0 = x) (hlt : ∀ t ∈ Ioo (0 : ℝ) 1, f x < f (y t)) : ¬ IsLocalMax f x := by
  intro hmax
  have hT : Tendsto y (𝓝[>] 0) (𝓝 x) := hy0 ▸ (hy.tendsto 0).mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (y t) ≤ f x := hT.eventually hmax
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  exact absurd ht1 (not_le.2 (hlt t ht2))

/-- **The witness has exactly one local maximum.** -/
theorem creationWitness_unique_localMax {a δ : ℝ} (ha : 1 < a) (hδ : 0 < δ) :
    ∃! x : Rd d, IsLocalMax (creationWitness d a δ) x := by
  refine ⟨0, Filter.Eventually.of_forall fun x => creationWitness_le_zero ha hδ x, fun x hx => ?_⟩
  by_contra hne
  have hP := cwProfile_strictAnti (a := a) (δ := δ) (by linarith) hδ.ne'
  rcases (trv_nonneg x).lt_or_eq with htr | htr
  · refine not_isLocalMax_of_path (fun t => x - t • (x - x 0 • ebasis 0)) (by fun_prop)
      (by simp) (fun t ht => ?_) hx
    simp only
    obtain ⟨h1, h2⟩ := trv_sub_smul x t
    rw [creationWitness_eq, creationWitness_eq, h1, h2]
    refine hP _ ?_
    have : (1 - t) ^ 2 < 1 := by nlinarith [ht.1, ht.2]
    nlinarith
  · have hx0 : x 0 ≠ 0 := by
      intro h0
      apply hne
      have : ‖x‖ ^ 2 = 0 := by have := trv_eq x; rw [h0] at this; linarith
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    refine not_isLocalMax_of_path (fun t => (1 - t) • x) (by fun_prop) (by simp)
      (fun t ht => ?_) hx
    rw [creationWitness_eq, creationWitness_eq, trv_smul, ← htr, mul_zero, PiLp.smul_apply,
      smul_eq_mul]
    refine cwAxis_lt_of_abs_lt ha ?_
    rw [abs_mul, abs_of_pos (by linarith [ht.2] : (0 : ℝ) < 1 - t)]
    have := abs_pos.2 hx0
    nlinarith [ht.1]

/-- **Every nonempty superlevel set of the witness is connected**: from any of its points, the path
moving `x'` to `0` and then `x₁` to `0` stays in it. -/
theorem creationWitness_isConnected {a δ : ℝ} (ha : 1 < a) (hδ : 0 < δ) {C : ℝ}
    (hC : C < creationWitness d a δ 0) : IsConnected {x | C < creationWitness d a δ x} := by
  have hP := fun s => (cwProfile_strictAnti (a := a) (δ := δ) (by linarith) hδ.ne' s).antitone
  refine ⟨⟨0, hC⟩, isPreconnected_of_forall 0 fun y hy => ?_⟩
  refine ⟨segment ℝ y (y 0 • ebasis 0) ∪ segment ℝ (y 0 • ebasis 0) 0, ?_,
    Or.inr (right_mem_segment _ _ _), Or.inl (left_mem_segment _ _ _),
    (convex_segment _ _).isPreconnected.union _ (right_mem_segment _ _ _)
      (left_mem_segment _ _ _) (convex_segment _ _).isPreconnected⟩
  have hy' : C < cwProfile a δ (y 0) (trv y) := by rw [← creationWitness_eq]; exact hy
  rintro z (⟨u, v, hu, hv, huv, rfl⟩ | ⟨u, v, hu, hv, huv, rfl⟩)
  · rw [mem_setOf_eq]
    have hz : u • y + v • (y 0 • ebasis 0) = y - v • (y - y 0 • ebasis 0) := by
      rw [show u = 1 - v by linarith, sub_smul, one_smul, smul_sub]; abel
    rw [hz, creationWitness_eq, (trv_sub_smul y v).1, (trv_sub_smul y v).2]
    refine hy'.trans_le (hP _ ?_)
    have : (1 - v) ^ 2 ≤ 1 := by nlinarith
    nlinarith [trv_nonneg y]
  · rw [mem_setOf_eq, smul_zero, add_zero, smul_smul, creationWitness_eq, trv_smul]
    have h0 : trv (ebasis 0 : Rd d) = 0 := by
      rw [trv_eq, norm_ebasis0]; simp [ebasis]
    rw [h0, mul_zero]
    have he : ((u * y 0) • (ebasis 0 : Rd d)) 0 = u * y 0 := by simp [ebasis]
    rw [he]
    refine hy'.trans_le ((hP _ (trv_nonneg y)).trans (cwAxis_le_of_abs_le ha ?_))
    rw [abs_mul, abs_of_nonneg hu]
    exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)


/-! ## Records of bounded continuous functions -/

omit [NeZero d] in
theorem integrable_comp_sub_of_bdd_Rd (μ : Measure (Rd d)) [IsFiniteMeasure μ] {f : Rd d → ℝ}
    (hf : Continuous f) {A : ℝ} (hA : ∀ z, |f z| ≤ A) (x : Rd d) :
    Integrable (fun y => f (x - y)) μ := by
  refine (integrable_const A).mono'
    (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact hA _

omit [NeZero d] in
theorem continuous_mconvE_of_bdd (μ : Measure (Rd d)) [IsFiniteMeasure μ] {f : Rd d → ℝ}
    (hf : Continuous f) {A : ℝ} (hA : ∀ z, |f z| ≤ A) : Continuous (mconvE μ f) := by
  refine continuous_of_dominated (bound := fun _ => A)
    (fun x => (integrable_comp_sub_of_bdd_Rd μ hf hA x).1)
    (fun x => Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hA _)
    (integrable_const A)
    (Eventually.of_forall fun y => hf.comp (continuous_id.sub continuous_const))

omit [NeZero d] in
theorem mconvE_comp_add (μ : Measure (Rd d)) (f : Rd d → ℝ) (p x : Rd d) :
    mconvE μ (fun z => f (z + p)) x = mconvE μ f (x + p) := by
  simp only [ScaleSpace.mconvE_apply]
  congr 1
  funext y
  congr 1
  abel

/-! ## The bumps: `W := μ * e^{-|·|²/2}` -/

/-- `e^{-|z|²/2}`. -/
noncomputable def gB (z : Rd d) : ℝ := Real.exp (-‖z‖ ^ 2 / 2)

omit [NeZero d] in
theorem continuous_gB : Continuous (gB (d := d)) := by unfold gB; fun_prop

omit [NeZero d] in
theorem gB_pos (z : Rd d) : 0 < gB z := Real.exp_pos _

omit [NeZero d] in
theorem gB_le_one (z : Rd d) : gB z ≤ 1 := by
  unfold gB
  rw [Real.exp_le_one_iff]
  have := sq_nonneg ‖z‖
  linarith

omit [NeZero d] in
theorem abs_gB_le (z : Rd d) : |gB z| ≤ 1 := by
  rw [abs_of_pos (gB_pos z)]; exact gB_le_one z

omit [NeZero d] in
theorem integrable_exp_neg_mul_sq_norm_Rd {c : ℝ} (hc : 0 < c) :
    Integrable fun z : Rd d => Real.exp (-c * ‖z‖ ^ 2) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Rd d) (b := (c : ℂ))
    (by simpa using hc) 0 0).norm
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero]
  rw [Complex.norm_exp]
  congr 1
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]

omit [NeZero d] in
theorem mconvE_gB_nonneg (μ : Measure (Rd d)) (x : Rd d) : 0 ≤ mconvE μ gB x :=
  integral_nonneg fun _ => (gB_pos _).le

omit [NeZero d] in
theorem mconvE_gB_le_one (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (x : Rd d) :
    mconvE μ gB x ≤ 1 := by
  rw [ScaleSpace.mconvE_apply]
  calc ∫ y, gB (x - y) ∂μ ≤ ∫ _y, (1 : ℝ) ∂μ :=
        integral_mono (integrable_comp_sub_of_bdd_Rd μ continuous_gB abs_gB_le x)
          (integrable_const 1) fun y => gB_le_one _
    _ = 1 := by simp

omit [NeZero d] in
/-- **`W` tends to `0` at infinity.** -/
theorem mconvE_gB_small (μ : Measure (Rd d)) [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ x : Rd d, R ≤ ‖x‖ → mconvE μ gB x < ε := by
  set L : Filter (Rd d) := comap (fun x => ‖x‖) atTop with hL
  have hpt : ∀ y : Rd d, Tendsto (fun x => gB (x - y)) L (𝓝 0) := by
    intro y
    have h1 : Tendsto (fun x : Rd d => ‖x - y‖) L atTop := by
      refine tendsto_atTop_mono (fun x => norm_sub_norm_le x y) ?_
      exact tendsto_atTop_add_const_right _ _ tendsto_comap
    have h2 : Tendsto (fun r : ℝ => Real.exp (-r ^ 2 / 2)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have : Tendsto (fun r : ℝ => r ^ 2 / 2) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
      have h3 := tendsto_neg_atTop_atBot.comp this
      refine h3.congr fun r => ?_
      simp only [Function.comp]
      ring
    exact h2.comp h1
  have hW : Tendsto (mconvE μ gB) L (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := L)
      (F := fun x y => gB (x - y)) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (Eventually.of_forall fun x => (integrable_comp_sub_of_bdd_Rd μ continuous_gB abs_gB_le x).1)
      (Eventually.of_forall fun x => Eventually.of_forall fun _ => by
        rw [Real.norm_eq_abs]; exact abs_gB_le _)
      (integrable_const 1) (Eventually.of_forall fun y => hpt y)
    rw [integral_zero] at this
    refine this.congr fun x => ?_
    rw [ScaleSpace.mconvE_apply]
  obtain ⟨s, hs, hsub⟩ := (Filter.mem_comap).1 (hW.eventually (gt_mem_nhds hε))
  obtain ⟨R, hR⟩ := Filter.mem_atTop_sets.1 hs
  exact ⟨R, fun x hx => hsub (hR _ hx)⟩

/-! ## The ridge -/

/-- **The ridge** `R_δ(z) := 8a² e^{-z₁²/(8a²)} e^{-|z'|²/(2δ²)}`. -/
noncomputable def cwRidge (a δ : ℝ) (z : Rd d) : ℝ :=
  8 * a ^ 2 * Real.exp (-(z 0) ^ 2 / (8 * a ^ 2)) * Real.exp (-trv z / (2 * δ ^ 2))

theorem creationWitness_eq_sum (a δ : ℝ) (x : Rd d) :
    creationWitness d a δ x = gB (x - a • ebasis 0) + gB (x + a • ebasis 0) + cwRidge a δ x := by
  rw [creationWitness, cwRidge, gB, gB, trv_eq]

theorem continuous_trv : Continuous (trv (d := d)) := by
  unfold trv
  have : Continuous fun x : Rd d => x 0 := (EuclideanSpace.proj (0 : Fin d)).continuous
  fun_prop

theorem continuous_cwRidge (a δ : ℝ) : Continuous (cwRidge (d := d) a δ) := by
  unfold cwRidge
  have : Continuous fun x : Rd d => x 0 := (EuclideanSpace.proj (0 : Fin d)).continuous
  have := continuous_trv (d := d)
  fun_prop

theorem cwRidge_nonneg (a δ : ℝ) (z : Rd d) : 0 ≤ cwRidge a δ z := by
  unfold cwRidge; positivity

theorem cwRidge_le (a δ : ℝ) (z : Rd d) : cwRidge a δ z ≤ 8 * a ^ 2 := by
  unfold cwRidge
  have h1 : Real.exp (-(z 0) ^ 2 / (8 * a ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (z 0)]) (by positivity)
  have h2 : Real.exp (-trv z / (2 * δ ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [trv_nonneg z]) (by positivity)
  have h8 : 0 ≤ 8 * a ^ 2 := by positivity
  calc 8 * a ^ 2 * Real.exp (-(z 0) ^ 2 / (8 * a ^ 2)) * Real.exp (-trv z / (2 * δ ^ 2))
      ≤ 8 * a ^ 2 * 1 * 1 := by gcongr
    _ = 8 * a ^ 2 := by ring

theorem abs_cwRidge_le (a δ : ℝ) (z : Rd d) : |cwRidge a δ z| ≤ 8 * a ^ 2 := by
  rw [abs_of_nonneg (cwRidge_nonneg a δ z)]; exact cwRidge_le a δ z

/-- For `δ ≤ 1` the ridge lies under the Gaussian `8a² e^{-|z|²/(8a²)}`. -/
theorem cwRidge_le_gauss {a δ : ℝ} (ha : 1 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (z : Rd d) :
    cwRidge a δ z ≤ 8 * a ^ 2 * Real.exp (-(1 / (8 * a ^ 2)) * ‖z‖ ^ 2) := by
  unfold cwRidge
  rw [mul_assoc, ← Real.exp_add]
  gcongr
  have hn : ‖z‖ ^ 2 = z 0 ^ 2 + trv z := by rw [trv_eq]; ring
  have ht := trv_nonneg z
  have h8 : 0 < 8 * a ^ 2 := by positivity
  have hd2 : δ ^ 2 ≤ 1 := by nlinarith
  have hq : trv z / (8 * a ^ 2) ≤ trv z / (2 * δ ^ 2) := by
    apply div_le_div_of_nonneg_left ht (by positivity)
    nlinarith
  rw [hn]
  have : -(1 / (8 * a ^ 2)) * (z 0 ^ 2 + trv z) =
      -(z 0) ^ 2 / (8 * a ^ 2) + -(trv z / (8 * a ^ 2)) := by
    field_simp
    ring
  rw [this]
  have : -trv z / (2 * δ ^ 2) = -(trv z / (2 * δ ^ 2)) := by ring
  rw [this]
  linarith

theorem integrable_cwRidge {a δ : ℝ} (ha : 1 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Integrable (cwRidge (d := d) a δ) := by
  refine ((integrable_exp_neg_mul_sq_norm_Rd (d := d)
    (by positivity : (0 : ℝ) < 1 / (8 * a ^ 2))).const_mul (8 * a ^ 2)).mono'
    (continuous_cwRidge a δ).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (cwRidge_nonneg a δ z)]
  exact cwRidge_le_gauss ha hδ hδ1 z

/-- **The axis is null in `d ≥ 2`.** -/
theorem volume_trv_eq_zero (hd : 2 ≤ d) : (volume : Measure (Rd d)) {z | trv z = 0} = 0 := by
  set S : Submodule ℝ (Rd d) := Submodule.span ℝ {ebasis 0} with hS
  have hsub : {z : Rd d | trv z = 0} ⊆ (S : Set (Rd d)) := by
    intro z hz
    have : ‖z - z 0 • ebasis 0‖ = 0 := by
      have h : ‖z - z 0 • ebasis 0‖ ^ 2 = 0 := hz
      exact pow_eq_zero_iff two_ne_zero |>.1 h
    rw [norm_eq_zero, sub_eq_zero] at this
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hne : S ≠ ⊤ := by
    intro htop
    have hmem : (ebasis ⟨1, by omega⟩ : Rd d) ∈ S := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    have := congrArg (fun v : Rd d => v ⟨1, by omega⟩) hc
    simp [ebasis] at this
  exact measure_mono_null hsub (Measure.addHaar_submodule volume S hne)

/-- `‖R_δ‖₁ → 0` along `δ = 1/(n+1)`. -/
theorem tendsto_integral_cwRidge (hd : 2 ≤ d) {a : ℝ} (ha : 1 < a) :
    Tendsto (fun n : ℕ => ∫ z, cwRidge (d := d) a (1 / ((n : ℝ) + 1)) z) atTop (𝓝 0) := by
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hδ1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  have h := tendsto_integral_of_dominated_convergence
    (F := fun (n : ℕ) (z : Rd d) => cwRidge a (1 / ((n : ℝ) + 1)) z) (f := fun _ => 0)
    (fun z => 8 * a ^ 2 * Real.exp (-(1 / (8 * a ^ 2)) * ‖z‖ ^ 2))
    (fun n => (continuous_cwRidge a _).aestronglyMeasurable)
    ((integrable_exp_neg_mul_sq_norm_Rd (d := d)
      (by positivity : (0 : ℝ) < 1 / (8 * a ^ 2))).const_mul (8 * a ^ 2))
    (fun n => Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cwRidge_nonneg _ _ z)]
      exact cwRidge_le_gauss ha (hδ n) (hδ1 n) z)
    (by
      have hnull := volume_trv_eq_zero (d := d) hd
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz
      have htr : 0 < trv z := (trv_nonneg z).lt_of_ne (Ne.symm hz)
      have hlim : Tendsto (fun n : ℕ => -trv z / (2 * (1 / ((n : ℝ) + 1)) ^ 2)) atTop atBot := by
        have e : ∀ n : ℕ, -trv z / (2 * (1 / ((n : ℝ) + 1)) ^ 2) =
            -(trv z / 2) * ((n : ℝ) + 1) ^ 2 := fun n => by field_simp
        simp_rw [e]
        refine Tendsto.const_mul_atTop_of_neg (by linarith) ?_
        exact (tendsto_pow_atTop two_ne_zero).comp
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      have := (Real.tendsto_exp_atBot.comp hlim).const_mul
        (8 * a ^ 2 * Real.exp (-(z 0) ^ 2 / (8 * a ^ 2)))
      rw [mul_zero] at this
      exact this)
  simpa using h

omit [NeZero d] in
/-- `∫(K - n)⁺ → 0` for an integrable `K`. -/
theorem tendsto_integral_posPart_sub {K : Rd d → ℝ} (hK : Integrable K) :
    Tendsto (fun n : ℕ => ∫ y, max (K y - n) 0) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (F := fun (n : ℕ) (y : Rd d) => max (K y - n) 0) (f := fun _ => 0) (fun y => ‖K y‖)
    (fun n => (hK.1.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const)
    hK.norm
    (fun n => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ (abs_nonneg _)
      linarith [le_abs_self (K y), n.cast_nonneg (α := ℝ)])
    (Eventually.of_forall fun y => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (K y)]
        with n hn
      exact (max_eq_right (by linarith)).symm)
  simpa using h

/-- **The ridge's record is uniformly small** for a suitable `δ ∈ (0, 1]`. -/
theorem cwRidge_record_small (hd : 2 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hac : μ ≪ volume) {a : ℝ} (ha : 1 < a) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Rd d, mconvE μ (cwRidge a δ) x ≤ η := by
  set K : Rd d → ℝ := fun y => (μ.rnDeriv volume y).toReal with hKdef
  have hK : Integrable K := Measure.integrable_toReal_rnDeriv
  have hK0 : ∀ y, 0 ≤ K y := fun y => ENNReal.toReal_nonneg
  have hA : 0 < 8 * a ^ 2 := by positivity
  -- `M`
  obtain ⟨M, hM⟩ := ((tendsto_integral_posPart_sub hK).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < η / (2 * (8 * a ^ 2))))).exists
  -- `δ`
  have hMp : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  obtain ⟨n, hn⟩ := ((tendsto_integral_cwRidge hd ha).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < η / (2 * ((M : ℝ) + 1))))).exists
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
  refine ⟨δ, hδ, fun x => ?_⟩
  have hR := integrable_cwRidge (d := d) ha hδ hδ1
  -- the record against the density
  have hrec : mconvE μ (cwRidge a δ) x = ∫ y, K y * cwRidge a δ (x - y) := by
    rw [ScaleSpace.mconvE_apply]
    have h1 : ∫ y, cwRidge a δ (x - y) ∂μ =
        ∫ y, cwRidge a δ (x - y) ∂(volume.withDensity (μ.rnDeriv volume)) := by
      rw [Measure.withDensity_rnDeriv_eq μ volume hac]
    rw [h1, integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top μ volume)]
    rfl
  have hRx : Integrable fun y => cwRidge a δ (x - y) := hR.comp_sub_left x
  have hi1 : Integrable fun y => K y * cwRidge a δ (x - y) := by
    refine (hK.norm.const_mul (8 * a ^ 2)).mono' (hK.1.mul hRx.1)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul (abs_cwRidge_le a δ _) le_rfl (abs_nonneg _) hA.le
  have hpos : Integrable fun y => max (K y - M) 0 := by
    refine hK.mono' ((hK.1.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [n.cast_nonneg (α := ℝ), M.cast_nonneg (α := ℝ)]) (hK0 y)
  have hi2 : Integrable fun y => (M : ℝ) * cwRidge a δ (x - y) + 8 * a ^ 2 * max (K y - M) 0 :=
    (hRx.const_mul _).add (hpos.const_mul _)
  rw [hrec]
  calc ∫ y, K y * cwRidge a δ (x - y)
      ≤ ∫ y, ((M : ℝ) * cwRidge a δ (x - y) + 8 * a ^ 2 * max (K y - M) 0) := by
        refine integral_mono hi1 hi2 fun y => ?_
        have h0 := cwRidge_nonneg a δ (x - y)
        have h8 := cwRidge_le a δ (x - y)
        rcases le_or_gt (K y) M with hk | hk
        · have : max (K y - M) 0 = 0 := max_eq_right (by linarith)
          simp only [this, mul_zero, add_zero]
          exact mul_le_mul_of_nonneg_right hk h0
        · have : max (K y - M) 0 = K y - M := max_eq_left (by linarith)
          simp only [this]
          nlinarith
    _ = (M : ℝ) * (∫ z : Rd d, cwRidge a δ z) + 8 * a ^ 2 * ∫ y, max (K y - M) 0 := by
        rw [integral_add (hRx.const_mul _) (hpos.const_mul _), integral_const_mul,
          integral_const_mul,
          integral_sub_left_eq_self (μ := (volume : Measure (Rd d))) (fun z => cwRidge a δ z)]
    _ ≤ ((M : ℝ) + 1) * (η / (2 * ((M : ℝ) + 1))) + 8 * a ^ 2 * (η / (2 * (8 * a ^ 2))) := by
        have hI0 : 0 ≤ ∫ z : Rd d, cwRidge a δ z := integral_nonneg (cwRidge_nonneg a δ)
        have h1 := mul_le_mul (by linarith : (M : ℝ) ≤ M + 1) hn.le hI0 hMp.le
        have h2 := mul_le_mul_of_nonneg_left hM.le hA.le
        linarith
    _ = η := by field_simp; ring

/-! ## Two maxima -/

omit [NeZero d] in
/-- A continuous function larger at the centre than on the sphere of radius `r` about it has a local
maximum inside the ball. -/
theorem exists_isLocalMax_ball {F : Rd d → ℝ} (hF : Continuous F) (c : Rd d) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x ∈ Metric.sphere c r, F x < F c) : ∃ x ∈ Metric.ball c r, IsLocalMax F x := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall c r).exists_isMaxOn
    ⟨c, Metric.mem_closedBall_self hr⟩ hF.continuousOn
  have hcx : F c ≤ F x := hmax (Metric.mem_closedBall_self hr)
  have hxb : x ∈ Metric.ball c r := by
    rcases (Metric.mem_closedBall.1 hx).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (h x heq) (not_lt.2 hcx)
  refine ⟨x, hxb, ?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds hxb] with y hy
  exact hmax (Metric.ball_subset_closedBall hy)

theorem norm_smul_ebasis0 (a : ℝ) : ‖a • (ebasis 0 : Rd d)‖ = |a| := by
  rw [norm_smul, norm_ebasis0, mul_one, Real.norm_eq_abs]

omit [NeZero d] in
theorem two_norm_le (x p : Rd d) : 2 * ‖p‖ ≤ ‖x - p‖ + ‖x + p‖ := by
  have h := norm_sub_le (x + p) (x - p)
  have e : x + p - (x - p) = (2 : ℝ) • p := by rw [two_smul]; abel
  rw [e, norm_smul, Real.norm_two] at h
  linarith

omit [NeZero d] in
/-- `W(0) > 0`: the Gaussian is positive and `μ` a probability. -/
theorem mconvE_gB_pos (μ : Measure (Rd d)) [IsProbabilityMeasure μ] (x : Rd d) :
    0 < mconvE μ gB x := by
  rw [ScaleSpace.mconvE_apply]
  refine (integral_pos_iff_support_of_nonneg (fun y => (gB_pos _).le)
    (integrable_comp_sub_of_bdd_Rd μ continuous_gB abs_gB_le x)).2 ?_
  have : Function.support (fun y => gB (x - y)) = univ :=
    Function.support_eq_univ fun y => (gB_pos _).ne'
  rw [this, measure_univ]
  exact one_pos

/-- **`prop:creation-plane`(1), one step.** For an absolutely continuous probability `μ`, some
`h = h_{a,δ}` has exactly one local maximum while `μ * h` has at least two, and for some level `C`,
`{h > C}` is connected while `{μ * h > C}` is not. Neither a nonnegative transform nor symmetry is
assumed: `W := μ * e^{-|·|²/2}` is positive at `0` and below `W(0)/4` off a ball `B_r`, and the
bumps sit at `±p` with `|p| = a > r`. -/
theorem creation_plane_1 (hd : 2 ≤ d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hac : μ ≪ volume) :
    ∃ a δ : ℝ, 1 < a ∧ 0 < δ ∧ (∃! x, IsLocalMax (creationWitness d a δ) x) ∧
      (∃ x y, x ≠ y ∧ IsLocalMax (mconvE μ (creationWitness d a δ)) x ∧
        IsLocalMax (mconvE μ (creationWitness d a δ)) y) ∧
      ∃ C : ℝ, IsConnected {x | C < creationWitness d a δ x} ∧
        ¬ IsPreconnected {x | C < mconvE μ (creationWitness d a δ) x} := by
  set W := mconvE μ (gB (d := d)) with hWdef
  have hWc : Continuous W := continuous_mconvE_of_bdd μ continuous_gB abs_gB_le
  have hW0p : 0 < W 0 := mconvE_gB_pos μ 0
  -- `r`, with `W < W(0)/4` off `B_r`
  obtain ⟨R, hR⟩ := mconvE_gB_small μ (by positivity : (0 : ℝ) < W 0 / 4)
  set r := max R 1 with hrdef
  have hr1 : 1 ≤ r := le_max_right _ _
  have hfar : ∀ z : Rd d, r ≤ ‖z‖ → W z < W 0 / 4 := fun z hz =>
    hR z ((le_max_left R 1).trans hz)
  -- `a`
  set a := r + 1 with hadef
  have ha : 1 < a := by linarith
  -- `δ`
  obtain ⟨δ, hδ, hridge⟩ := cwRidge_record_small hd μ hac ha (by positivity : (0 : ℝ) < W 0 / 4)
  refine ⟨a, δ, ha, hδ, creationWitness_unique_localMax ha hδ, ?_⟩
  set p : Rd d := a • ebasis 0 with hpdef
  have hp : ‖p‖ = a := by rw [hpdef, norm_smul_ebasis0, abs_of_pos (by linarith)]
  set Rr := mconvE μ (cwRidge (d := d) a δ) with hRr
  have hRrc : Continuous Rr := continuous_mconvE_of_bdd μ (continuous_cwRidge a δ)
    (abs_cwRidge_le a δ)
  have hRr0 : ∀ x, 0 ≤ Rr x := fun x => integral_nonneg fun y => cwRidge_nonneg a δ _
  set F := mconvE μ (creationWitness d a δ) with hFdef
  have hF : ∀ x, F x = W (x - p) + W (x + p) + Rr x := by
    intro x
    have hi1 := integrable_comp_sub_of_bdd_Rd μ (f := fun z => gB (z - p))
      (continuous_gB.comp (continuous_id.sub continuous_const)) (fun z => abs_gB_le _) x
    have hi2 := integrable_comp_sub_of_bdd_Rd μ (f := fun z => gB (z + p))
      (continuous_gB.comp (continuous_id.add continuous_const)) (fun z => abs_gB_le _) x
    have hi3 := integrable_comp_sub_of_bdd_Rd μ (continuous_cwRidge (d := d) a δ)
      (abs_cwRidge_le a δ) x
    have e1 : W (x - p) = mconvE μ (fun z => gB (z + -p)) x := by
      rw [mconvE_comp_add, sub_eq_add_neg]
    have e2 : W (x + p) = mconvE μ (fun z => gB (z + p)) x := by rw [mconvE_comp_add]
    rw [e1, e2, hFdef, hRr]
    simp only [ScaleSpace.mconvE_apply]
    simp_rw [creationWitness_eq_sum, ← sub_eq_add_neg, ← hpdef]
    rw [← integral_add hi1 hi2]
    exact integral_add (hi1.add hi2) hi3
  have hFc : Continuous F := by
    have : F = fun x => W (x - p) + W (x + p) + Rr x := funext hF
    rw [this]; fun_prop
  have hW0 : ∀ z, 0 ≤ W z := mconvE_gB_nonneg μ
  -- the centres and the spheres
  have hcp : W 0 ≤ F p := by
    rw [hF, sub_self]; linarith [hW0 (p + p), hRr0 p]
  have hcm : W 0 ≤ F (-p) := by
    rw [hF, neg_add_cancel]; linarith [hW0 (-p - p), hRr0 (-p)]
  have hsp : ∀ x ∈ Metric.sphere p r, F x < 3 * W 0 / 4 := by
    intro x hx
    rw [mem_sphere_iff_norm] at hx
    have h2 := two_norm_le x p
    have h1 := hfar _ hx.ge
    have h3 := hfar (x + p) (by rw [hp] at h2; linarith)
    have h4 := hridge x
    rw [hF]; linarith
  have hsm : ∀ x ∈ Metric.sphere (-p) r, F x < 3 * W 0 / 4 := by
    intro x hx
    rw [mem_sphere_iff_norm, sub_neg_eq_add] at hx
    have h2 := two_norm_le x p
    have h1 := hfar _ hx.ge
    have h3 := hfar (x - p) (by rw [hp] at h2; linarith)
    have h4 := hridge x
    rw [hF]; linarith
  obtain ⟨x, hxb, hxmax⟩ := exists_isLocalMax_ball hFc p (r := r) (by linarith) fun x hx => by
    linarith [hsp x hx]
  obtain ⟨y, hyb, hymax⟩ := exists_isLocalMax_ball hFc (-p) (r := r) (by linarith) fun x hx => by
    linarith [hsm x hx]
  refine ⟨⟨x, y, ?_, hxmax, hymax⟩, 3 * W 0 / 4, ?_, ?_⟩
  · rintro rfl
    rw [Metric.mem_ball, dist_eq_norm] at hxb hyb
    rw [sub_neg_eq_add] at hyb
    have := two_norm_le x p
    rw [hp] at this
    linarith
  · refine creationWitness_isConnected ha hδ ?_
    have h0 : cwRidge (d := d) a δ 0 = 8 * a ^ 2 := by
      have ht : trv (0 : Rd d) = 0 := by simp [trv]
      simp [cwRidge, ht]
    have hle := mconvE_gB_le_one μ (0 : Rd d)
    rw [creationWitness_eq_sum, h0]
    have := gB_pos ((0 : Rd d) - a • ebasis 0)
    have := gB_pos ((0 : Rd d) + a • ebasis 0)
    nlinarith
  · intro hpc
    obtain ⟨z, hzS, hzu, hzv⟩ := hpc (Metric.ball p r) (Metric.closedBall p r)ᶜ
      Metric.isOpen_ball Metric.isClosed_closedBall.isOpen_compl
      (fun z hz => by
        simp only [mem_setOf_eq] at hz
        rcases lt_trichotomy (dist z p) r with h | h | h
        · exact Or.inl h
        · exact absurd (hsp z h) (by linarith)
        · exact Or.inr (by simp [Metric.mem_closedBall, not_le.2 h]))
      ⟨p, by simp only [mem_setOf_eq]; linarith, Metric.mem_ball_self (by linarith)⟩
      ⟨-p, by simp only [mem_setOf_eq]; linarith, by
        simp only [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le]
        have : -p - p = (-2 : ℝ) • p := by rw [neg_smul, two_smul]; abel
        rw [this, norm_smul, hp]; norm_num; linarith⟩
    exact hzv (Metric.ball_subset_closedBall hzu)

end Pyramids
