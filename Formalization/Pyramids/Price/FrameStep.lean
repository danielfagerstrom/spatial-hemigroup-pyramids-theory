/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.Defs.Price
import Pyramids.Line.KconvBdd
import Pyramids.Line.ZConv

/-!
# `prop:grid-frame-step-not-selected`: the frame step on the grid is not selected

Blueprint: `blueprint/src/parts/05-price.tex`, `prop:grid-frame-step-not-selected`. Wave 3h:
`grid_frame_step_not_selected_1` and `_2` moved here from `PyramidsSkeleton.Ch05Price`, unchanged
in name and conclusion. Dropped on 2026-11-15, a strengthening: `_1` no longer takes `hN`,
`hNsymm`, `h0` (the counterexample's origin is a maximum over the whole grid, so it is an
`𝒩`-maximum for every set `𝒩`), and `_2` no longer takes `hd`, `hN`, `hNsymm`, `h0` (the "if"
direction reads only `±eᵢ ∈ 𝒩`).

## The route

* **The inverse on the line**, `m := (1 + 2ς)δ₀ - ς(δ₁ + δ₋₁)` with `ς = a/(1-a)²`
  (`lineInv`), is supported on `{-1, 0, 1}`, and its convolution with `g` is the three-point
  expression of `geomKernel_rec`.
* **The tensor inverse.** `m^{⊗d}` is supported on the finite box `{-1, 0, 1}^d`, so its
  convolution with a tensor kernel is a finite sum over the box, which factors as the product of
  the `d` line convolutions (`Finset.prod_univ_sum`). No infinite product of series is needed. So
  `w * m^{⊗d} = δ₀` by `geomKernel_rec` in each coordinate.
* **(1).** The witness `u := -1` on the four points `±e₁ ± e₂` (and `0` elsewhere) has the origin
  as a global maximum, `u = w * f` for the finitely supported `f := m^{⊗d} * u`, and every term
  of `f(0) = ∑ m^{⊗d}(y) u(-y)` is `≤ 0`, the one at `y = e₁ + e₂` being
  `-ς² (1 + 2ς)^{d-2} < 0`.
* **(2).** The axis kernel's inverse is `(1 + 2ς)δ₀ - ς(δ_{eᵢ} + δ_{-eᵢ})`, by `geomKernel_rec`
  on the axis and trivially off it; then `f(x) = u(x) + ς(2u(x) - u(x + eᵢ) - u(x - eᵢ))`.
-/

namespace Pyramids

open AffineHemigroup

variable {d : ℕ} {a : ℝ}

/-! ## The line inverse and the box -/

/-- **The three-point inverse** `(1 + 2ς)δ₀ - ς(δ₁ + δ₋₁)` of the sampled Laplace mask on `ℤ`. -/
noncomputable def lineInv (s : ℝ) (j : ℤ) : ℝ :=
  if j = 0 then 1 + 2 * s else if j = 1 ∨ j = -1 then -s else 0

/-- `{-1, 0, 1}`. -/
def triple : Finset ℤ := {-1, 0, 1}

theorem lineInv_eq_zero (s : ℝ) {j : ℤ} (hj : j ∉ triple) : lineInv s j = 0 := by
  simp only [triple, Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  simp [lineInv, hj.1, hj.2.1, hj.2.2]

/-- The line convolution of `lineInv` with `g`, over the support of `lineInv`. -/
theorem sum_triple_lineInv (s : ℝ) (g : ℤ → ℝ) (m : ℤ) :
    ∑ j ∈ triple, lineInv s j * g (m - j) =
      (1 + 2 * s) * g m - s * (g (m + 1) + g (m - 1)) := by
  simp only [triple]
  rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  simp only [lineInv]
  norm_num
  ring

/-- The tensor inverse vanishes off the box `{-1, 0, 1}^d`. -/
theorem tensorIdx_lineInv_eq_zero (s : ℝ) {m : Zd d}
    (hm : m ∉ Fintype.piFinset fun _ : Fin d => triple) : tensorIdx (lineInv s) m = 0 := by
  rw [Fintype.mem_piFinset, not_forall] at hm
  obtain ⟨i, hi⟩ := hm
  exact Finset.prod_eq_zero (Finset.mem_univ i) (lineInv_eq_zero s hi)

theorem summable_tensorIdx_lineInv (s : ℝ) : Summable (tensorIdx (d := d) (lineInv s)) :=
  summable_of_ne_finset_zero fun _ hm => tensorIdx_lineInv_eq_zero s hm

/-- **The convolution of the tensor inverse with a tensor kernel** is the product of the line
convolutions: a finite sum over the box, factored by `Finset.prod_univ_sum`. -/
theorem kconv_tensorIdx_lineInv (s : ℝ) (g : ℤ → ℝ) (n : Zd d) :
    kconv (tensorIdx (lineInv s)) (tensorIdx g) n =
      ∏ i, ((1 + 2 * s) * g (n i) - s * (g (n i + 1) + g (n i - 1))) := by
  classical
  unfold kconv
  rw [tsum_eq_sum (s := Fintype.piFinset fun _ : Fin d => triple) fun m hm => by
    rw [tensorIdx_lineInv_eq_zero s hm, zero_mul]]
  simp_rw [← sum_triple_lineInv s g]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [tensorIdx, ← Finset.prod_mul_distrib, Pi.sub_apply]

/-- **A tensor of a nonnegative summable kernel is summable** on `ℤ^d`: a finite set of indices
lies in the box of its coordinates, whose sum is a product of `d` finite sums. -/
theorem summable_tensorIdx {k : ℤ → ℝ} (hk0 : ∀ n, 0 ≤ k n) (hk : Summable k) :
    Summable (tensorIdx (d := d) k) := by
  classical
  refine summable_of_sum_le (c := (∑' n, k n) ^ d)
    (fun n => Finset.prod_nonneg fun i _ => hk0 _) fun F => ?_
  set T : Fin d → Finset ℤ := fun i => F.image fun n => n i
  have hsub : F ⊆ Fintype.piFinset T := fun n hn =>
    Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ hn
  calc ∑ n ∈ F, tensorIdx k n ≤ ∑ n ∈ Fintype.piFinset T, tensorIdx k n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
          Finset.prod_nonneg fun i _ => hk0 _
    _ = ∏ i, ∑ j ∈ T i, k j := (Finset.prod_univ_sum T fun _ j => k j).symm
    _ ≤ ∏ _i : Fin d, ∑' n, k n :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => hk0 j)
          fun i _ => hk.sum_le_tsum _ fun j _ => hk0 j
    _ = (∑' n, k n) ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The tensor inverse of the frame mask**: `(λ^L_a)^{⊗d} * m^{⊗d} = δ₀` on `ℤ^d`. -/
theorem kconv_tensorIdx_geomKernel_lineInv (ha0 : 0 < a) (ha1 : a < 1) :
    kconv (tensorIdx (d := d) (geomKernel a)) (tensorIdx (lineInv (a / (1 - a) ^ 2))) =
      deltaZ := by
  funext n
  rw [kconv_comm, kconv_tensorIdx_lineInv]
  simp_rw [geomKernel_rec ha0 ha1]
  rw [Finset.prod_boole]
  simp only [deltaZ, Finset.mem_univ, true_implies, funext_iff, Pi.zero_apply]

/-- The value of the tensor inverse at a diagonal point `±e_{i₀} ± e_{i₁}` is positive:
`ς · ς · (1 + 2ς)^{d-2}`. -/
theorem tensorIdx_lineInv_diag_pos {s : ℝ} (hs : 0 < s) {i₀ i₁ : Fin d} (h01 : i₀ ≠ i₁)
    {m : Zd d} (hm0 : m i₀ = 1 ∨ m i₀ = -1) (hm1 : m i₁ = 1 ∨ m i₁ = -1)
    (hm : ∀ j, j ≠ i₀ → j ≠ i₁ → m j = 0) : 0 < tensorIdx (lineInv s) m := by
  have hpm : ∀ j : ℤ, (j = 1 ∨ j = -1) → lineInv s j = -s := fun j hj => by
    have : j ≠ 0 := by rcases hj with rfl | rfl <;> decide
    simp [lineInv, this, hj]
  have h1 : i₁ ∈ Finset.univ.erase i₀ := Finset.mem_erase.2 ⟨h01.symm, Finset.mem_univ _⟩
  unfold tensorIdx
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), ← Finset.mul_prod_erase _ _ h1,
    hpm _ hm0, hpm _ hm1]
  refine lt_of_lt_of_eq (mul_pos (mul_pos hs hs) (Finset.prod_pos fun j hj => ?_)) (by ring)
  obtain ⟨hj1, hj⟩ := Finset.mem_erase.1 hj
  obtain ⟨hj0, -⟩ := Finset.mem_erase.1 hj
  rw [hm j hj0 hj1]
  simp only [lineInv, if_true]
  linarith

/-! ## (1): no principle on any neighbourhood -/

/-- **`prop:grid-frame-step-not-selected`(1).** In `d ≥ 2` the frame mask `(λ^L_a)^{⊗d}` does not
have the principle on any `𝒩 ⊂ ℤ^d`. The node reads it for finite symmetric `𝒩 ⊂ ℤ^d ∖ {0}`; the
proof reads none of the three (dropped on 2026-11-15, a strengthening). -/
theorem grid_frame_step_not_selected_1 (hd : 2 ≤ d) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (N : Set (Zd d)) : ¬ HasGridImplicitEulerPrinciple N (tensorIdx (geomKernel a)) := by
  intro hP
  set s := a / (1 - a) ^ 2 with hs
  have hs0 : 0 < s := by
    have : 0 < 1 - a := by linarith
    positivity
  set i₀ : Fin d := ⟨0, by omega⟩
  set i₁ : Fin d := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  set κ := tensorIdx (d := d) (geomKernel a) with hκ
  set T := tensorIdx (d := d) (lineInv s) with hT
  have hTs : Summable T := summable_tensorIdx_lineInv s
  have hκs : Summable κ :=
    summable_tensorIdx (geomKernel_nonneg' ha0.le ha1) (summable_geomKernel ha0.le ha1)
  -- the witness: `-1` on the four diagonal points `±e_{i₀} ± e_{i₁}`
  set D : Zd d → Prop := fun m => (m i₀ = 1 ∨ m i₀ = -1) ∧ (m i₁ = 1 ∨ m i₁ = -1) ∧
    ∀ j, j ≠ i₀ → j ≠ i₁ → m j = 0 with hD
  classical
  set u : Zd d → ℝ := fun n => if D n then -1 else 0 with hu
  have hub : ∃ C : ℝ, ∀ n, |u n| ≤ C := ⟨1, fun n => by
    simp only [hu]
    split_ifs <;> norm_num⟩
  have hule : ∀ n, u n ≤ 0 := fun n => by
    simp only [hu]
    split_ifs <;> norm_num
  have hu0 : u 0 = 0 := by
    have : ¬ D 0 := fun h => by
      rcases h.1 with h | h <;> simp at h
    simp [hu, this]
  set f := kconv T u with hf
  have hfb := kconv_bdd hTs hub
  have hκu : kconv κ f = u := by
    rw [hf, ← kconv_assoc_bdd hκs hTs hub, hκ, hT, hs,
      kconv_tensorIdx_geomKernel_lineInv ha0 ha1, kconv_deltaZ_left]
  have hmax : IsNMax N (kconv κ f) 0 := by
    rw [hκu]
    intro y _
    rw [hu0]
    exact hule _
  have h1 := (hP f hfb 0).1 hmax
  rw [hκu, hu0] at h1
  -- every term of `f(0)` is `≤ 0`, the one at `e_{i₀} + e_{i₁}` is `< 0`
  have hterm : ∀ m, T m * u (0 - m) ≤ 0 := fun m => by
    simp only [hu, zero_sub]
    split_ifs with hm
    · obtain ⟨hm0, hm1, hmj⟩ := hm
      have hpos : 0 < T m := by
        refine tensorIdx_lineInv_diag_pos hs0 h01 (m := m) ?_ ?_ fun j hj0 hj1 => ?_
        · simp only [Pi.neg_apply, neg_eq_iff_eq_neg] at hm0
          rcases hm0 with h | h <;> [right; left] <;> linarith
        · simp only [Pi.neg_apply, neg_eq_iff_eq_neg] at hm1
          rcases hm1 with h | h <;> [right; left] <;> linarith
        · have := hmj j hj0 hj1
          simpa using this
      linarith
    · simp
  set y : Zd d := -(zbasis i₀ + zbasis i₁)
  have hy : D (-y) := by
    simp only [y, neg_neg, hD, Pi.add_apply, zbasis, Pi.single_apply, if_true,
      if_neg h01.symm, if_neg h01]
    refine ⟨by simp, by simp, fun j hj0 hj1 => by simp [hj0, hj1]⟩
  have hylt : T y * u (0 - y) < 0 := by
    have hpos : 0 < T y := by
      refine tensorIdx_lineInv_diag_pos hs0 h01 ?_ ?_ fun j hj0 hj1 => ?_
      · right
        simp [y, zbasis, h01]
      · right
        simp [y, zbasis, h01.symm]
      · simp [y, zbasis, hj0, hj1]
    simp only [hu, zero_sub, if_pos hy]
    linarith
  have hsum : Summable fun m => T m * u (0 - m) := summable_bounded_mul hTs hub.choose_spec 0
  have hlt : f 0 < 0 := by
    have := hsum.tsum_lt_tsum (f := fun m => T m * u (0 - m)) (g := fun _ => (0 : ℝ))
      hterm hylt summable_zero
    simpa [hf, kconv] using this
  linarith

/-! ## (2): the axis pass has the principle -/

/-- The axis kernel vanishes off the axis `ℤ eᵢ`, the range of `Pi.single i`. -/
theorem axisPassIdx_eq_zero (k : ℤ → ℝ) (i : Fin d) {n : Zd d}
    (hn : n ∉ Set.range fun j : ℤ => (Pi.single i j : Zd d)) : axisPassIdx k i n = 0 := by
  classical
  unfold axisPassIdx
  rw [if_neg]
  intro h
  refine hn ⟨n i, funext fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj, h j hj]

theorem axisPassIdx_single (k : ℤ → ℝ) (i : Fin d) (j : ℤ) :
    axisPassIdx k i (Pi.single i j) = k j := by
  classical
  unfold axisPassIdx
  rw [if_pos fun l hl => by simp [hl]]
  simp

theorem summable_axisPassIdx {k : ℤ → ℝ} (hk : Summable k) (i : Fin d) :
    Summable (axisPassIdx k i) := by
  have e := (Pi.single_injective (M := fun _ : Fin d => ℤ) i).summable_iff
    (f := axisPassIdx k i) fun n hn => axisPassIdx_eq_zero k i hn
  refine e.1 ?_
  convert hk using 1
  funext j
  exact axisPassIdx_single k i j

/-- The axis inverse `(1 + 2ς)δ₀ - ς(δ_{eᵢ} + δ_{-eᵢ})`, convolved with any `u`. -/
theorem hasSum_axisInv_mul (s : ℝ) (i : Fin d) (u : Zd d → ℝ) (n : Zd d) :
    HasSum (fun m => ((1 + 2 * s) * deltaZ (m - 0) + -s * deltaZ (m - zbasis i) +
        -s * deltaZ (m - -zbasis i)) * u (n - m))
      ((1 + 2 * s) * u (n - 0) + -s * u (n - zbasis i) + -s * u (n - -zbasis i)) := by
  have H := ((hasSum_delta_mul 0 n u (1 + 2 * s)).add (hasSum_delta_mul (zbasis i) n u (-s))).add
    (hasSum_delta_mul (-zbasis i) n u (-s))
  convert H using 1
  funext m
  ring

/-- **`prop:grid-frame-step-not-selected`(2).** The axis pass along `eᵢ`, the law `λ^L_a` carried
by `ℤeᵢ`, has the principle on every `𝒩 ⊂ ℤ^d` containing `±eᵢ`. The node reads it for `d ≥ 2`
and finite symmetric `𝒩 ⊂ ℤ^d ∖ {0}`; the proof reads none of the four (dropped on 2026-11-15, a
strengthening). -/
theorem grid_frame_step_not_selected_2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (i : Fin d) (N : Set (Zd d)) (hi : zbasis i ∈ N ∧ -zbasis i ∈ N) :
    HasGridImplicitEulerPrinciple N (axisPassIdx (geomKernel a) i) := by
  classical
  set s := a / (1 - a) ^ 2 with hs
  have hs0 : 0 < s := by
    have : 0 < 1 - a := by linarith
    positivity
  set κ := axisPassIdx (geomKernel a) i with hκ
  set k : Zd d → ℝ := fun m => (1 + 2 * s) * deltaZ (m - 0) + -s * deltaZ (m - zbasis i) +
    -s * deltaZ (m - -zbasis i) with hk
  have hku : ∀ (u : Zd d → ℝ) (n : Zd d), kconv k u n =
      (1 + 2 * s) * u (n - 0) + -s * u (n - zbasis i) + -s * u (n - -zbasis i) :=
    fun u n => (hasSum_axisInv_mul s i u n).tsum_eq
  have hks : Summable k := by
    have := (hasSum_axisInv_mul s i (fun _ => 1) 0).summable
    simpa only [mul_one] using this
  have hκs : Summable κ := summable_axisPassIdx (summable_geomKernel ha0.le ha1) i
  have hzi : ∀ j, j ≠ i → (zbasis i : Zd d) j = 0 := fun j hj => by
    simp [zbasis, hj]
  have hzii : (zbasis i : Zd d) i = 1 := by simp [zbasis]
  -- `k * κ = δ₀`: the recursion on the axis, three zeros off it
  have hinv : kconv k κ = deltaZ := by
    funext n
    rw [hku]
    by_cases hax : ∀ j, j ≠ i → n j = 0
    · have hax' : ∀ v : Zd d, (∀ j, j ≠ i → v j = 0) → κ v = geomKernel a (v i) := fun v hv => by
        simp only [hκ, axisPassIdx, if_pos hv]
      rw [hax' _ (by simpa using hax), hax' _ fun j hj => by simp [hax j hj, hzi j hj],
        hax' _ fun j hj => by simp [hax j hj, hzi j hj]]
      have hd : deltaZ n = if n i = 0 then 1 else 0 := by
        unfold deltaZ
        congr 1
        exact propext ⟨fun h => by rw [h]; rfl, fun h => funext fun j => by
          by_cases hj : j = i
          · rw [hj, h]; rfl
          · exact hax j hj⟩
      rw [hd, ← geomKernel_rec ha0 ha1 (n i), ← hs]
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.zero_apply, sub_zero, sub_neg_eq_add, hzii]
      ring_nf
    · push Not at hax
      obtain ⟨j, hji, hnj⟩ := hax
      have hoff : ∀ v : Zd d, v j ≠ 0 → κ v = 0 := fun v hv => by
        simp only [hκ, axisPassIdx]
        rw [if_neg fun h => hv (h j hji)]
      have hn0 : n ≠ 0 := fun h => hnj (by rw [h]; rfl)
      rw [hoff _ (by simpa using hnj), hoff _ (by simpa [hzi j hji] using hnj),
        hoff _ (by simpa [hzi j hji] using hnj)]
      simp [deltaZ, hn0]
  intro f hf x
  set u := kconv κ f with hu_def
  have hu : ∃ C, ∀ n, |u n| ≤ C := kconv_bdd hκs hf
  have hfu : f = kconv k u := by
    rw [hu_def, ← kconv_assoc_bdd hks hκs hf, hinv, kconv_deltaZ_left]
  have hfx : f x = (1 + 2 * s) * u x + -s * u (x - zbasis i) + -s * u (x + zbasis i) := by
    rw [hfu, hku, sub_zero, sub_neg_eq_add]
  have hxm : x - zbasis i = x + -zbasis i := sub_eq_add_neg _ _
  constructor
  · intro hmax
    have h1 := hmax _ hi.1
    have h2 := hmax _ hi.2
    rw [← hxm] at h2
    rw [hfx]
    nlinarith
  · intro hmin
    have h1 := hmin _ hi.1
    have h2 := hmin _ hi.2
    rw [← hxm] at h2
    dsimp only at h1 h2
    rw [hfx]
    nlinarith

end Pyramids
