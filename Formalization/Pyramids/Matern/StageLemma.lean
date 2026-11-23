/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Matern.MaternGenerator
import Pyramids.Matern.CreationGridInverse
import Pyramids.Line.KconvBdd

/-!
# `prop:stage-lemma`(1)–(2): sufficiency, on `ℝ^d` and on the grid

Blueprint: `blueprint/src/parts/04-matern.tex`, `prop:stage-lemma`. Phase 5, wave 3b.
`stage_lemma_1`, `_1_helmholtz` and `_2` moved here from `PyramidsSkeleton.Ch04Matern`, their
conclusions unchanged; clause (3) stays there, priced.

## Sufficiency, clause (1)

* **Existence.** `C = BᵀB` (`CStarAlgebra.nonneg_iff_eq_star_mul_self`), and the image of `L_1`
  (`maternStep d 1`, transform `(1 + |ω|²)⁻¹`) under `x ↦ Bᵀx` has transform
  `(1 + |Bω|²)⁻¹ = (1 + ω·Cω)⁻¹` (`charFun_map_lin`); it is symmetric, its transform being even.
* **The principle, with no derivative of `u`.** For real Schwartz `f`, Fourier inversion
  (`schwartz_inversion`, `mconvE_re_fourierInvInt`) writes `u = μ * f` and `f` as
  `Re ∫ e(ξ,·) g` and `Re ∫ e(ξ,·)(1 + 4π²ξ·Cξ) g`, `g := μ̂(-2π·)f̂`, so that
  `f(x) - u(x) = 4π² ∑ₖ Qₖ`, `Qₖ := Re ∫ e(ξ,x)⟨ξ,bₖ⟩² g`, `bₖ := Bᵀeₖ`. Each `-4π²Qₖ` is the limit
  as `s → 0` of the second difference `(u(x + sbₖ) + u(x - sbₖ) - 2u(x))/s²`
  (`tendsto_second_diff`, dominated convergence with `|2cos y - 2| ≤ y²`), which is `≤ 0` near a
  local maximum. Minima follow with `-f`.

Dropped binders (2026-11-15, a strengthening): `stage_lemma_1` and `_1_helmholtz` take no
`1 ≤ d`.

## The grid, clause (2)

The kernel is `κ_t` of `prop:discrete-helmholtz` at `t = √τ` (`discreteHelmholtz`), whose
transform `(1 + t²D_h)⁻¹` is the printed one, `2 - 2cos ϑ = 4 sin²(ϑ/2)`; at `τ = 0` it is `δ₀`.
A probability kernel with that transform is that kernel (`kernel_eq_of_gridFourier_eq`), hence
symmetric. For bounded `f`, `u := κ * f` has `u - τΔ_h u = (κ - τΔ_hκ) * f = f`
(`gridLap_kconv_right`, read with `f` on the left), and at an axis maximum `Δ_h u(x) ≤ 0`.

**What it reaches.** Lean core (the guard's run, `records/pyramids/WAVE3-report-3b-vm.md`).
-/

set_option autoImplicit false

namespace Pyramids

open AffineHemigroup
open MeasureTheory Set Filter
open ScaleSpace (mconvE)
open scoped Topology ENNReal RealInnerProductSpace Matrix SchwartzMap FourierTransform

variable {d : ℕ}

/-! ## The grid -/

section Grid

/-- `Δ_h κ` of a summable kernel is summable. -/
theorem summable_gridLap {κ : Zd d → ℝ} (hκ : Summable κ) (h : ℝ) :
    Summable (gridLap h κ) := by
  have hs : Summable (kconv κ rwStep) := summable_kconv hκ summable_rwStep
  have : gridLap h κ = fun n => (h ^ 2)⁻¹ * (2 * d) * kconv κ rwStep n +
      (-((h ^ 2)⁻¹ * (2 * d))) * κ n := by
    funext n
    rw [gridLap_eq]
    ring
  rw [this]
  exact (hs.mul_left _).add (hκ.mul_left _)

/-- **The resolvent equation gives the principle on the axis neighbours.** A summable kernel
with `κ - τΔ_hκ = δ₀`, `τ ≥ 0`, has the principle on `{±eᵢ}`: `u := κ * f` has
`u - τΔ_h u = f`, and `Δ_h u ≤ 0` at an axis maximum. -/
theorem hasGridImplicitEulerPrinciple_of_resolvent {κ : Zd d → ℝ} (hκ : Summable κ) {h τ : ℝ}
    (hτ : 0 ≤ τ) (heq : ∀ n, κ n - τ * gridLap h κ n = deltaZ n) :
    HasGridImplicitEulerPrinciple (axisNbrs d) κ := by
  intro f ⟨C, hC⟩ x
  have hL := summable_gridLap hκ h
  -- `u - τΔ_h u = f`
  have key : kconv κ f x - τ * gridLap h (kconv κ f) x = f x := by
    have hcomm : kconv κ f = kconv f κ := kconv_comm κ f
    rw [hcomm, gridLap_kconv_right h hκ hC x, kconv_comm f κ, kconv_comm f (gridLap h κ)]
    have h1 := summable_bounded_mul hκ hC x
    have h2 := summable_bounded_mul hL hC x
    unfold kconv
    rw [← tsum_mul_left, ← Summable.tsum_sub h1 (h2.mul_left τ)]
    have : (fun m => κ m * f (x - m) - τ * (gridLap h κ m * f (x - m))) =
        fun m => deltaZ m * f (x - m) := by
      funext m
      rw [← heq m]
      ring
    rw [this]
    exact congrFun (kconv_deltaZ_left f) x
  have hmem : ∀ i : Fin d, zbasis i ∈ axisNbrs d ∧ -zbasis i ∈ axisNbrs d := fun i =>
    ⟨⟨i, Or.inl rfl⟩, ⟨i, Or.inr rfl⟩⟩
  refine ⟨fun hmax => ?_, fun hmin => ?_⟩
  · have hlap : gridLap h (kconv κ f) x ≤ 0 := by
      unfold gridLap
      refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun i _ => ?_)
      have h1 := hmax _ (hmem i).1
      have h2 := hmax _ (hmem i).2
      rw [← sub_eq_add_neg] at h2
      linarith
    nlinarith
  · have hlap : 0 ≤ gridLap h (kconv κ f) x := by
      unfold gridLap
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
      have h1 := hmin _ (hmem i).1
      have h2 := hmin _ (hmem i).2
      rw [← sub_eq_add_neg] at h2
      simp only at h1 h2
      linarith
    nlinarith

/-- `t²D_h(ϑ) = 4t²h⁻² ∑ⱼ sin²(ϑⱼ/2)`. -/
theorem sq_mul_gridSymbol (h t : ℝ) (θ : Fin d → ℝ) :
    t ^ 2 * gridSymbol h θ = 4 * t ^ 2 / h ^ 2 * ∑ j, Real.sin (θ j / 2) ^ 2 := by
  rw [gridSymbol]
  have : ∀ j, 2 - 2 * Real.cos (θ j) = 4 * Real.sin (θ j / 2) ^ 2 := fun j => by
    have := Real.cos_two_mul (θ j / 2)
    rw [mul_div_cancel₀ _ two_ne_zero] at this
    have h2 := Real.sin_sq_add_cos_sq (θ j / 2)
    linarith
  simp_rw [this, ← Finset.mul_sum, div_eq_mul_inv]
  ring

/-- **`prop:stage-lemma`(2), the grid.** On `hℤ^d`, read in the indices with `ϑ = hω`, the kernel
with transform `(1 + 4τh⁻² ∑_j sin²(ϑ_j/2))⁻¹`, `τ ≥ 0`, exists as a probability; every probability
kernel with that transform is symmetric and has the principle on the `2d` axis neighbours. -/
theorem stage_lemma_2 (hd : 1 ≤ d) {h τ : ℝ} (hh : 0 < h) (hτ : 0 ≤ τ) :
    (∃ κ : Zd d → ℝ, IsProbKernel κ ∧ ∀ θ : Fin d → ℝ,
      gridFourier κ θ = (((1 + 4 * τ / h ^ 2 * ∑ j, Real.sin (θ j / 2) ^ 2)⁻¹ : ℝ) : ℂ)) ∧
      ∀ κ : Zd d → ℝ, IsProbKernel κ →
        (∀ θ : Fin d → ℝ,
          gridFourier κ θ = (((1 + 4 * τ / h ^ 2 * ∑ j, Real.sin (θ j / 2) ^ 2)⁻¹ : ℝ) : ℂ)) →
        (∀ n, κ (-n) = κ n) ∧ HasGridImplicitEulerPrinciple (axisNbrs d) κ := by
  -- the kernel `κ₀`: `δ₀` at `τ = 0`, `κ_{√τ}` otherwise
  obtain ⟨κ₀, hκ₀, hF, hsymm, heq⟩ : ∃ κ₀ : Zd d → ℝ, IsProbKernel κ₀ ∧
      (∀ θ : Fin d → ℝ,
        gridFourier κ₀ θ = (((1 + 4 * τ / h ^ 2 * ∑ j, Real.sin (θ j / 2) ^ 2)⁻¹ : ℝ) : ℂ)) ∧
      (∀ n, κ₀ (-n) = κ₀ n) ∧ ∀ n, κ₀ n - τ * gridLap h κ₀ n = deltaZ n := by
    rcases hτ.eq_or_lt with h0 | hpos
    · subst h0
      refine ⟨deltaZ, isProbKernel_deltaZ, fun θ => ?_, fun n => ?_, fun n => by ring⟩
      · rw [gridFourier_deltaZ]; simp
      · simp [deltaZ, neg_eq_zero]
    · set t := Real.sqrt τ with ht
      have ht0 : 0 < t := Real.sqrt_pos.2 hpos
      have ht2 : t ^ 2 = τ := Real.sq_sqrt hτ
      refine ⟨discreteHelmholtz d h t, isProbKernel_discreteHelmholtz hd hh ht0, fun θ => ?_,
        fun n => ?_, fun n => ?_⟩
      · rw [gridFourier_discreteHelmholtz hd hh ht0, sq_mul_gridSymbol, ht2]
      · have hε : ∀ i : Fin d, (fun _ => (-1 : ℤ)) i = 1 ∨ (fun _ => (-1 : ℤ)) i = -1 :=
          fun _ => Or.inr rfl
        have := kappa_invariant (Equiv.refl (Fin d)) (fun _ => (-1 : ℤ)) hε h t n
        rwa [show gmap (Equiv.refl (Fin d)) (fun _ => (-1 : ℤ)) n = -n by
          funext i; simp [gmap]] at this
      · rw [← ht2]; exact discreteHelmholtz_eqn hd hh ht0 n
  refine ⟨⟨κ₀, hκ₀, hF⟩, fun κ hκ hκF => ?_⟩
  have hκeq : κ = κ₀ := kernel_eq_of_gridFourier_eq hκ.2.1 hκ₀.2.1 fun θ => by rw [hκF, hF]
  subst hκeq
  exact ⟨hsymm, hasGridImplicitEulerPrinciple_of_resolvent hκ₀.2.1 hτ heq⟩

end Grid

/-! ## Sufficiency on `ℝ^d` -/

section Continuum

/-- `ω·C(aω) = a²ω·Cω`. -/
theorem quad_smul (C : Mat d) (a : ℝ) (ω : Rd d) : quad C (a • ω) = a ^ 2 * quad C ω := by
  simp only [quad, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

/-- `ω·(BᵀB)ω = |Bω|²`. -/
theorem quad_transpose_mul_self_eq (B : Mat d) (ω : Rd d) : quad (Bᵀ * B) ω = ‖lin B ω‖ ^ 2 := by
  rw [quad, show lin (Bᵀ * B) ω = lin Bᵀ (lin B ω) by rw [lin_mul]; rfl,
    ← Matrix.transpose_transpose B, ← inner_lin_left, Matrix.transpose_transpose,
    real_inner_self_eq_norm_sq]

/-- `ω·(BᵀB)ω = ∑ₖ ⟨ω, bₖ⟩²`, `bₖ := Bᵀeₖ`. -/
theorem quad_transpose_mul_self (B : Mat d) (ω : Rd d) :
    quad (Bᵀ * B) ω = ∑ k, ⟪ω, lin Bᵀ (ebasis k)⟫ ^ 2 := by
  rw [quad_transpose_mul_self_eq, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.norm_eq_abs, sq_abs, ← inner_lin_left]
  congr 1
  simp [ebasis, EuclideanSpace.inner_single_right]

/-- A positive semidefinite `C` is `BᵀB`. -/
theorem exists_transpose_mul_self {C : Mat d} (hC : C.PosSemidef) : ∃ B : Mat d, C = Bᵀ * B := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg
  exact ⟨B, by rw [hB, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]⟩

/-- `ω·Cω ≥ 0` for `C` positive semidefinite. -/
theorem quad_nonneg {C : Mat d} (hC : C.PosSemidef) (ω : Rd d) : 0 ≤ quad C ω := by
  obtain ⟨B, rfl⟩ := exists_transpose_mul_self hC
  rw [quad_transpose_mul_self]
  positivity

/-- `(2cos(as) - 2)/s² → -a²` as `s → 0`. -/
theorem tendsto_two_cos_sub_two_div_sq (a : ℝ) :
    Tendsto (fun s : ℝ => (2 * Real.cos (a * s) - 2) / s ^ 2) (𝓝[≠] 0) (𝓝 (-a ^ 2)) := by
  have hb : ∀ s : ℝ, s ≠ 0 →
      |(2 * Real.cos (a * s) - 2) / s ^ 2 - -a ^ 2| ≤ a ^ 4 / 12 * s ^ 2 := by
    intro s hs
    have hs2 : 0 < s ^ 2 := by positivity
    set y := a * s with hy
    have hu := cos_le_quartic (abs_nonneg y)
    have hl := Real.one_sub_sq_div_two_le_cos (x := y)
    rw [Real.cos_abs, sq_abs, show |y| ^ 4 = y ^ 4 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]] at hu
    have he : (2 * Real.cos y - 2) / s ^ 2 - -a ^ 2 = (2 * Real.cos y - 2 + y ^ 2) / s ^ 2 := by
      rw [hy]; field_simp; ring
    rw [he, abs_div, abs_of_pos hs2, div_le_iff₀ hs2, abs_le]
    have hy4 : y ^ 4 = a ^ 4 * s ^ 4 := by rw [hy]; ring
    constructor <;> nlinarith [sq_nonneg y, pow_two_nonneg (y ^ 2)]
  have h0 : Tendsto (fun s : ℝ => a ^ 4 / 12 * s ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => a ^ 4 / 12 * s ^ 2) (𝓝 0) (𝓝 (a ^ 4 / 12 * 0 ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact hb s hs

/-- The character `e(ξ, z) := e^{2πi⟨ξ,z⟩}`. -/
noncomputable def echar (ξ z : Rd d) : ℂ := Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) * Complex.I)

theorem norm_echar (ξ z : Rd d) : ‖echar ξ z‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_echar (z : Rd d) : Continuous fun ξ : Rd d => echar ξ z := by
  unfold echar; fun_prop

/-- `e(ξ, x + sv) + e(ξ, x - sv) - 2e(ξ, x) = e(ξ, x)(2cos(2πs⟨ξ,v⟩) - 2)`. -/
theorem char_second_diff (ξ x v : Rd d) (s : ℝ) :
    (echar ξ (x + s • v) + echar ξ (x - s • v) - 2 * echar ξ x) =
      echar ξ x * ((2 * Real.cos (2 * Real.pi * ⟪ξ, v⟫ * s) - 2 : ℝ) : ℂ) := by
  have hp : echar ξ (x + s • v) = echar ξ x *
      Complex.exp (↑(2 * Real.pi * ⟪ξ, v⟫ * s) * Complex.I) := by
    unfold echar
    rw [← Complex.exp_add]
    congr 1
    rw [inner_add_right, inner_smul_right]
    push_cast; ring
  have hm : echar ξ (x - s • v) = echar ξ x *
      Complex.exp (-(↑(2 * Real.pi * ⟪ξ, v⟫ * s) * Complex.I)) := by
    unfold echar
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_right, inner_smul_right]
    push_cast; ring
  rw [hp, hm]
  push_cast
  simp only [Complex.cos, neg_mul]
  ring

/-- **The second difference of an inverse transform.** For `g` integrable with `|ξ|²g`
integrable, `U(z) := Re ∫ e(ξ,z) g(ξ) dξ` has
`(U(x + sv) + U(x - sv) - 2U(x))/s² → -4π² Re ∫ e(ξ,x) ⟨ξ,v⟩² g(ξ) dξ`. -/
theorem tendsto_second_diff {g : Rd d → ℂ} (hg : Integrable g)
    (hg2 : Integrable fun ξ => ‖ξ‖ ^ 2 * ‖g ξ‖) (x v : Rd d) :
    Tendsto (fun s : ℝ => ((∫ ξ, echar ξ (x + s • v) * g ξ).re +
        (∫ ξ, echar ξ (x - s • v) * g ξ).re - 2 * (∫ ξ, echar ξ x * g ξ).re) / s ^ 2)
      (𝓝[≠] 0)
      (𝓝 (-(4 * Real.pi ^ 2) *
        (∫ ξ, echar ξ x * ((⟪ξ, v⟫ ^ 2 : ℝ) : ℂ) * g ξ).re)) := by
  have hint : ∀ z : Rd d, Integrable fun ξ => echar ξ z * g ξ := fun z => by
    refine hg.bdd_mul (c := 1) (continuous_echar z).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_echar]
  -- the quotient, as one integral
  have hrw : ∀ s : ℝ, ((∫ ξ, echar ξ (x + s • v) * g ξ).re +
      (∫ ξ, echar ξ (x - s • v) * g ξ).re - 2 * (∫ ξ, echar ξ x * g ξ).re) / s ^ 2 =
      (∫ ξ, echar ξ x * (((2 * Real.cos (2 * Real.pi * ⟪ξ, v⟫ * s) - 2) / s ^ 2 : ℝ) : ℂ) *
        g ξ).re := by
    intro s
    have hsum : (∫ ξ, echar ξ (x + s • v) * g ξ) + (∫ ξ, echar ξ (x - s • v) * g ξ) -
        2 * (∫ ξ, echar ξ x * g ξ) =
        ∫ ξ, echar ξ x * ((2 * Real.cos (2 * Real.pi * ⟪ξ, v⟫ * s) - 2 : ℝ) : ℂ) * g ξ := by
      have h3 : Integrable fun ξ => echar ξ (x + s • v) * g ξ + echar ξ (x - s • v) * g ξ :=
        (hint _).add (hint _)
      rw [← integral_add (hint _) (hint _), ← integral_const_mul,
        ← integral_sub h3 ((hint x).const_mul 2)]
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      simp only
      rw [← char_second_diff]
      ring
    have hc : ∀ ξ, echar ξ x * (((2 * Real.cos (2 * Real.pi * ⟪ξ, v⟫ * s) - 2) / s ^ 2 : ℝ) : ℂ) *
        g ξ = (echar ξ x * ((2 * Real.cos (2 * Real.pi * ⟪ξ, v⟫ * s) - 2 : ℝ) : ℂ) * g ξ) *
          (((s ^ 2)⁻¹ : ℝ) : ℂ) := fun ξ => by
      push_cast; ring
    simp_rw [hc]
    rw [integral_mul_const, ← hsum, Complex.re_mul_ofReal, div_eq_mul_inv]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero]
  simp_rw [hrw]
  have hlim : Tendsto (fun s : ℝ => ∫ ξ, echar ξ x *
      (((2 * Real.cos (2 * Real.pi * ⟪ξ, v⟫ * s) - 2) / s ^ 2 : ℝ) : ℂ) * g ξ) (𝓝[≠] 0)
      (𝓝 (∫ ξ, echar ξ x * ((-(2 * Real.pi * ⟪ξ, v⟫) ^ 2 : ℝ) : ℂ) * g ξ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ => (2 * Real.pi * ‖v‖) ^ 2 * (‖ξ‖ ^ 2 * ‖g ξ‖)) ?_ ?_ (hg2.const_mul _) ?_
    · exact Eventually.of_forall fun s =>
        ((continuous_echar x).mul (by fun_prop)).aestronglyMeasurable.mul hg.1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Eventually.of_forall fun ξ => ?_
      rw [norm_mul, norm_mul, norm_echar, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have hs0 : s ≠ 0 := hs
      have hs2 : 0 < s ^ 2 := by positivity
      set a := 2 * Real.pi * ⟪ξ, v⟫
      have hcos := Real.one_sub_sq_div_two_le_cos (x := a * s)
      have hc1 := Real.cos_le_one (a * s)
      have hq : |(2 * Real.cos (a * s) - 2) / s ^ 2| ≤ a ^ 2 := by
        rw [abs_div, abs_of_pos hs2, div_le_iff₀ hs2, abs_of_nonpos (by linarith)]
        nlinarith
      have ha : a ^ 2 ≤ (2 * Real.pi * ‖v‖) ^ 2 * ‖ξ‖ ^ 2 := by
        have := abs_real_inner_le_norm ξ v
        have hpi := Real.pi_pos
        rw [show a ^ 2 = (2 * Real.pi) ^ 2 * |⟪ξ, v⟫| ^ 2 by rw [sq_abs]; ring]
        rw [show (2 * Real.pi * ‖v‖) ^ 2 * ‖ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * (‖ξ‖ * ‖v‖) ^ 2 by ring]
        gcongr
      calc |(2 * Real.cos (a * s) - 2) / s ^ 2| * ‖g ξ‖ ≤ a ^ 2 * ‖g ξ‖ :=
            mul_le_mul_of_nonneg_right hq (norm_nonneg _)
        _ ≤ (2 * Real.pi * ‖v‖) ^ 2 * ‖ξ‖ ^ 2 * ‖g ξ‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ = _ := by ring
    · refine Eventually.of_forall fun ξ => ?_
      refine ((tendsto_const_nhds.mul ?_).mul tendsto_const_nhds)
      exact (Complex.continuous_ofReal.tendsto _).comp
        (tendsto_two_cos_sub_two_div_sq (2 * Real.pi * ⟪ξ, v⟫))
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hval : (∫ ξ, echar ξ x * ((-(2 * Real.pi * ⟪ξ, v⟫) ^ 2 : ℝ) : ℂ) * g ξ).re =
      -(4 * Real.pi ^ 2) * (∫ ξ, echar ξ x * ((⟪ξ, v⟫ ^ 2 : ℝ) : ℂ) * g ξ).re := by
    rw [← Complex.re_ofReal_mul, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    push_cast
    ring
  rw [hval] at hre
  exact hre

/-- `e(ξ,x)⟨ξ,v⟩²g(ξ)` is integrable when `|ξ|²g` is. -/
theorem integrable_echar_inner_sq {g : Rd d → ℂ} (hg : Integrable g)
    (hg2 : Integrable fun ξ => ‖ξ‖ ^ 2 * ‖g ξ‖) (x v : Rd d) :
    Integrable fun ξ => echar ξ x * ((⟪ξ, v⟫ ^ 2 : ℝ) : ℂ) * g ξ := by
  refine (hg2.const_mul (‖v‖ ^ 2)).mono'
    (((continuous_echar x).mul (by fun_prop)).aestronglyMeasurable.mul hg.1)
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, norm_mul, norm_echar, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  have h := abs_real_inner_le_norm ξ v
  have h2 : ⟪ξ, v⟫ ^ 2 ≤ ‖v‖ ^ 2 * ‖ξ‖ ^ 2 := by
    rw [← sq_abs, show ‖v‖ ^ 2 * ‖ξ‖ ^ 2 = (‖ξ‖ * ‖v‖) ^ 2 by ring]
    gcongr
  calc ⟪ξ, v⟫ ^ 2 * ‖g ξ‖ ≤ ‖v‖ ^ 2 * ‖ξ‖ ^ 2 * ‖g ξ‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = _ := by ring

/-- The transform of a resolvent law at `-2πξ`. -/
theorem charFun_resolvent_neg {C : Mat d} {μ : Measure (Rd d)}
    (hμ : ∀ ω, charFun μ ω = (((1 + quad C ω)⁻¹ : ℝ) : ℂ)) (ξ : Rd d) :
    charFun μ (-(2 * Real.pi) • ξ) = (((1 + 4 * Real.pi ^ 2 * quad C ξ)⁻¹ : ℝ) : ℂ) := by
  rw [hμ, quad_smul]
  congr 3
  ring

/-- **The clause at maxima.** If `μ̂ = (1 + ω·Cω)⁻¹` with `C` positive semidefinite, then
`u := μ * f` has `u(x) ≤ f(x)` at every local maximum, for every real Schwartz `f`. With
`C = BᵀB` and `bₖ := Bᵀeₖ`, `f(x) - u(x) = 4π² ∑ₖ Re ∫ e(ξ,x)⟨ξ,bₖ⟩²ĝ`, `ĝ := μ̂(-2π·)f̂`, and
each term is `-(1/4π²)` times the limit of the second differences of `u` along `bₖ`, which are
`≤ 0` near a local maximum. -/
theorem le_of_isLocalMax_resolvent {C : Mat d} (hC : C.PosSemidef) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (hμ : ∀ ω, charFun μ ω = (((1 + quad C ω)⁻¹ : ℝ) : ℂ))
    (f : 𝓢(Rd d, ℝ)) (x : Rd d) (hmax : IsLocalMax (mconvE μ f) x) :
    mconvE μ f x ≤ f x := by
  obtain ⟨B, rfl⟩ := exists_transpose_mul_self hC
  set ψ : 𝓢(Rd d, ℂ) := 𝓕 (schwartzC f) with hψ
  set b : Fin d → Rd d := fun k => lin Bᵀ (ebasis k) with hb
  set r : Rd d → ℝ := fun ξ => (1 + 4 * Real.pi ^ 2 * quad (Bᵀ * B) ξ)⁻¹ with hr
  have hq : ∀ ξ, 0 ≤ quad (Bᵀ * B) ξ := quad_nonneg hC
  have hpos : ∀ ξ, 0 < 1 + 4 * Real.pi ^ 2 * quad (Bᵀ * B) ξ := fun ξ => by
    have := hq ξ; positivity
  have hr1 : ∀ ξ, ‖(r ξ : ℂ)‖ ≤ 1 := fun ξ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos ξ))]
    exact inv_le_one_of_one_le₀ (by have := hq ξ; nlinarith [Real.pi_pos])
  have hquadc : Continuous (quad (Bᵀ * B)) := by
    unfold quad; exact continuous_id.inner (lin _).continuous
  have hrc : Continuous r :=
    (continuous_const.add (continuous_const.mul hquadc)).inv₀ fun ξ => (hpos ξ).ne'
  set g : Rd d → ℂ := fun ξ => (r ξ : ℂ) * ψ ξ with hgdef
  have hg : Integrable g := ψ.integrable.bdd_mul (c := 1)
    (Complex.continuous_ofReal.comp hrc).aestronglyMeasurable (Eventually.of_forall hr1)
  have hg2 : Integrable fun ξ => ‖ξ‖ ^ 2 * ‖g ξ‖ := by
    refine (ψ.integrable_pow_mul volume 2).mono'
      ((continuous_norm.pow 2).aestronglyMeasurable.mul hg.1.norm)
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hgdef, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa using mul_le_mul_of_nonneg_right (hr1 ξ) (norm_nonneg (ψ ξ))) (by positivity)
  -- `u` through the transform
  have hu : ∀ z, mconvE μ f z = (∫ ξ, echar ξ z * g ξ).re := by
    intro z
    have hfz : (f : Rd d → ℝ) = fun z => (∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, z⟫) *
        Complex.I) * ψ ξ).re := funext (schwartz_inversion f)
    rw [hfz, mconvE_re_fourierInvInt μ ψ.integrable z]
    simp_rw [charFun_resolvent_neg hμ]
    rfl
  -- each `Qₖ ≥ 0`
  have hQ : ∀ v : Rd d, 0 ≤ (∫ ξ, echar ξ x * ((⟪ξ, v⟫ ^ 2 : ℝ) : ℂ) * g ξ).re := by
    intro v
    have hlim := tendsto_second_diff hg hg2 x v
    have hp : Tendsto (fun s : ℝ => x + s • v) (𝓝 0) (𝓝 x) := by
      have : Continuous fun s : ℝ => x + s • v := by fun_prop
      simpa using this.tendsto 0
    have hm : Tendsto (fun s : ℝ => x - s • v) (𝓝 0) (𝓝 x) := by
      have : Continuous fun s : ℝ => x - s • v := by fun_prop
      simpa using this.tendsto 0
    have hev : ∀ᶠ s in 𝓝[≠] (0 : ℝ), ((∫ ξ, echar ξ (x + s • v) * g ξ).re +
        (∫ ξ, echar ξ (x - s • v) * g ξ).re - 2 * (∫ ξ, echar ξ x * g ξ).re) / s ^ 2 ≤ 0 := by
      have h1 := (hp.eventually hmax).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
      have h2 := (hm.eventually hmax).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
      filter_upwards [h1, h2] with s hs1 hs2
      rw [hu, hu] at hs1 hs2
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    have hle := le_of_tendsto hlim hev
    have h4 : 0 < 4 * Real.pi ^ 2 := by positivity
    nlinarith
  -- `f(x) - u(x) = 4π² ∑ₖ Qₖ`
  have hint : ∀ v, Integrable fun ξ => echar ξ x * ((⟪ξ, v⟫ ^ 2 : ℝ) : ℂ) * g ξ :=
    integrable_echar_inner_sq hg hg2 x
  have hintg : Integrable fun ξ => echar ξ x * g ξ := hg.bdd_mul (c := 1)
    (continuous_echar x).aestronglyMeasurable (Eventually.of_forall fun ξ => (norm_echar ξ x).le)
  have hsplit : (∫ ξ, echar ξ x * ψ ξ) = (∫ ξ, echar ξ x * g ξ) +
      ∑ k, ((4 * Real.pi ^ 2 : ℝ) : ℂ) *
        ∫ ξ, echar ξ x * ((⟪ξ, b k⟫ ^ 2 : ℝ) : ℂ) * g ξ := by
    have hpt : ∀ ξ, echar ξ x * ψ ξ = echar ξ x * g ξ +
        ∑ k, ((4 * Real.pi ^ 2 : ℝ) : ℂ) * (echar ξ x * ((⟪ξ, b k⟫ ^ 2 : ℝ) : ℂ) * g ξ) := by
      intro ξ
      have hrq : (r ξ : ℂ) * (1 + 4 * Real.pi ^ 2 * ∑ k, ((⟪ξ, b k⟫ ^ 2 : ℝ) : ℂ)) = 1 := by
        have h := inv_mul_cancel₀ (hpos ξ).ne'
        rw [quad_transpose_mul_self] at h
        simp only [hr]
        rw [quad_transpose_mul_self]
        exact_mod_cast h
      have hs : ∑ k, ((4 * Real.pi ^ 2 : ℝ) : ℂ) * (echar ξ x * ((⟪ξ, b k⟫ ^ 2 : ℝ) : ℂ) * g ξ) =
          4 * Real.pi ^ 2 * echar ξ x * g ξ * ∑ k, ((⟪ξ, b k⟫ ^ 2 : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast; ring
      rw [hs, hgdef]
      simp only
      linear_combination (-(echar ξ x * ψ ξ)) * hrq
    simp_rw [hpt]
    rw [integral_add hintg (integrable_finsetSum _ fun k _ => (hint (b k)).const_mul _),
      integral_finsetSum _ fun k _ => (hint (b k)).const_mul _]
    simp_rw [integral_const_mul]
  have hfx : f x = (∫ ξ, echar ξ x * ψ ξ).re := schwartz_inversion f x
  rw [hfx, hsplit, hu, Complex.add_re, Complex.re_sum, le_add_iff_nonneg_right]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) (hQ (b k))

/-- **The principle of a resolvent law.** -/
theorem hasImplicitEulerPrinciple_resolvent {C : Mat d} (hC : C.PosSemidef) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (hμ : ∀ ω, charFun μ ω = (((1 + quad C ω)⁻¹ : ℝ) : ℂ)) :
    HasImplicitEulerPrinciple μ := by
  intro f x
  refine ⟨le_of_isLocalMax_resolvent hC μ hμ f x, fun hmin => ?_⟩
  have hneg : mconvE μ ⇑(-f) = fun z => -mconvE μ f z := by
    funext z
    simp only [ScaleSpace.mconvE_apply, neg_apply, integral_neg]
  have h := le_of_isLocalMax_resolvent hC μ hμ (-f) x (by rw [hneg]; exact hmin.neg)
  rw [hneg, neg_apply] at h
  linarith

/-- **`prop:stage-lemma`(1).** For `C` positive semidefinite there is a symmetric probability with
transform `(1 + ω·Cω)⁻¹`, and every probability with that transform has the principle. -/
theorem stage_lemma_1 (C : Mat d) (hC : C.PosSemidef) :
    (∃ μ : Measure (Rd d), IsProbabilityMeasure μ ∧ μ.map (fun x => -x) = μ ∧
      ∀ ω, charFun μ ω = (((1 + quad C ω)⁻¹ : ℝ) : ℂ)) ∧
      ∀ μ : Measure (Rd d), IsProbabilityMeasure μ →
        (∀ ω, charFun μ ω = (((1 + quad C ω)⁻¹ : ℝ) : ℂ)) → HasImplicitEulerPrinciple μ := by
  refine ⟨?_, fun μ _ hμ => hasImplicitEulerPrinciple_resolvent hC μ hμ⟩
  obtain ⟨B, rfl⟩ := exists_transpose_mul_self hC
  haveI : IsProbabilityMeasure (maternStep d 1) := (charFun_maternStep (d := d) 1 0).1
  set μ₀ := (maternStep d 1).map (lin Bᵀ) with hμ₀
  haveI hP : IsProbabilityMeasure μ₀ :=
    Measure.isProbabilityMeasure_map (lin Bᵀ).continuous.aemeasurable
  have hch : ∀ ω, charFun μ₀ ω = (((1 + quad (Bᵀ * B) ω)⁻¹ : ℝ) : ℂ) := fun ω => by
    rw [hμ₀, charFun_map_lin, Matrix.transpose_transpose, (charFun_maternStep 1 _).2, one_pow,
      one_mul, quad_transpose_mul_self_eq]
  refine ⟨μ₀, hP, ?_, hch⟩
  haveI : IsProbabilityMeasure (μ₀.map fun x => -x) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun (funext fun ω => ?_)
  rw [charFun_apply, integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop))]
  have h := hch (-ω)
  rw [charFun_apply] at h
  simp_rw [inner_neg_left, ← inner_neg_right]
  rw [h, hch, show -ω = (-1 : ℝ) • ω by simp, quad_smul]
  simp

/-- **`prop:stage-lemma`(1), the Helmholtz resolvent** `(I - τΔ)⁻¹`, `τ ≥ 0`, has the principle. -/
theorem stage_lemma_1_helmholtz {τ : ℝ} (hτ : 0 ≤ τ) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (hμ : ∀ ω, charFun μ ω = (((1 + τ * ‖ω‖ ^ 2)⁻¹ : ℝ) : ℂ)) :
    HasImplicitEulerPrinciple μ := by
  have hC : (τ • (1 : Mat d)).PosSemidef := Matrix.PosSemidef.one.smul hτ
  refine hasImplicitEulerPrinciple_resolvent hC μ fun ω => ?_
  rw [hμ]
  congr 4
  rw [quad, lin_smul, lin_one, smul_apply, one_apply_eq_self,
    inner_smul_right, real_inner_self_eq_norm_sq]

end Continuum

end Pyramids
