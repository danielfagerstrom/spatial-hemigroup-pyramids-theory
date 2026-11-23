/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import Pyramids.LineAppendix.ClassicalWeights

/-!
# `prop:classical-pyramids-approximate`(4): lattice non-creation of the binomial mask

Blueprint: `blueprint/src/parts/A1-line.tex`, `prop:classical-pyramids-approximate`. Wave 3a:
`classical_pyramids_approximate_4` moved here from `PyramidsSkeleton.ChA1Line`, unchanged in
statement and name.

## The route

The printed one. Sign changes are counted along chains: `x` has a chain of `p` changes when there
are `k₀ < ⋯ < k_p` with `x(k_i)x(k_{i+1}) < 0` (`ZAltChain`). `S⁻(x)` is the largest such `p`: a
finite sequence with `p` sign changes, zeros deleted, has an alternating subsequence of length
`p + 1` (`exists_alt_sublist`), and an alternating sequence has exactly its length less one
(`seqSignChanges_eq_of_isChain`). So `S⁻(x) ≤ S⁻(y)` as soon as every chain of `x` gives a chain
of `y` of the same length (`zSignChanges_le_of_zAltChain`).

Chains pass back through a subsequence, a positive factor, and the sum of consecutive terms
`x(k) + x(k-1)` (`ZAltChain.of_pairSum`, the printed argument: pick in each pair the term of the
sign of the sum). The binomial mask is `1/16` times four such sums, shifted by `2`
(`zconv_binomialMask5`, `zPairSum_four`); it commutes with differences; and
`Δz(k) = Δy(2k+1) + Δy(2k)`.
-/

namespace Pyramids

open MeasureTheory Set

/-! ## Sign changes along chains -/

/-- **`x` changes sign `p` times along a chain**: there are `k₀ < ⋯ < k_p` with
`x(k_i)x(k_{i+1}) < 0`. -/
def ZAltChain (x : ℤ → ℝ) (p : ℕ) : Prop :=
  ∃ k : Fin (p + 1) → ℤ, StrictMono k ∧ ∀ i : Fin p, x (k i.castSucc) * x (k i.succ) < 0

/-- Every sequence has a chain of no sign change. -/
theorem zAltChain_zero (x : ℤ → ℝ) : ZAltChain x 0 :=
  ⟨fun _ => 0, fun i j hij => by
    have := i.isLt
    have := j.isLt
    rw [Fin.lt_def] at hij
    omega, fun i => i.elim0⟩

/-- The number of adjacent pairs of opposite signs in a list. -/
noncomputable def negPairs (l : List ℝ) : ℕ :=
  ((l.zip l.tail).filter fun p => p.1 * p.2 < 0).length

theorem seqSignChanges_eq_negPairs (l : List ℝ) :
    seqSignChanges l = negPairs (l.filter fun x => x ≠ 0) := rfl

theorem negPairs_singleton (a : ℝ) : negPairs [a] = 0 := by
  simp [negPairs]

theorem negPairs_cons_cons (a b : ℝ) (t : List ℝ) :
    negPairs (a :: b :: t) = (if a * b < 0 then 1 else 0) + negPairs (b :: t) := by
  simp only [negPairs, List.tail_cons, List.zip_cons_cons, List.filter_cons]
  by_cases hab : a * b < 0 <;> simp [hab, add_comm]

/-- **An alternating subsequence**: a list of nonzero reals starting at `a` has an alternating
subsequence starting at `a`, with one more term than the list has sign changes. -/
theorem exists_alt_sublist (a : ℝ) (t : List ℝ) (hne : ∀ y ∈ a :: t, y ≠ 0) :
    ∃ s : List ℝ, List.Sublist (a :: s) (a :: t) ∧ (a :: s).IsChain (fun u v => u * v < 0) ∧
      s.length = negPairs (a :: t) := by
  induction t generalizing a with
  | nil =>
    exact ⟨[], List.Sublist.refl _, List.IsChain.singleton a, by rw [negPairs_singleton]; rfl⟩
  | cons b t ih =>
    obtain ⟨s, hs, hc, hl⟩ := ih b fun y hy => hne y (List.mem_cons_of_mem _ hy)
    have ha : a ≠ 0 := hne a List.mem_cons_self
    have hb : b ≠ 0 := hne b (List.mem_cons_of_mem _ List.mem_cons_self)
    by_cases hab : a * b < 0
    · refine ⟨b :: s, hs.cons_cons a, List.isChain_cons_cons.2 ⟨hab, hc⟩, ?_⟩
      rw [negPairs_cons_cons, if_pos hab, List.length_cons, hl, add_comm]
    · refine ⟨s, ((List.cons_sublist_cons.1 hs).cons b).cons_cons a, ?_, ?_⟩
      · cases s with
        | nil => exact List.IsChain.singleton a
        | cons c s =>
          obtain ⟨hbc, hc'⟩ := List.isChain_cons_cons.1 hc
          refine List.isChain_cons_cons.2 ⟨?_, hc'⟩
          have hab' : 0 < a * b := lt_of_le_of_ne (not_lt.1 hab) (mul_ne_zero ha hb).symm
          have hbb : 0 < b * b := mul_self_pos.2 hb
          have he : (a * c) * (b * b) = (a * b) * (b * c) := by ring
          have hneg : (a * c) * (b * b) < 0 := by rw [he]; exact mul_neg_of_pos_of_neg hab' hbc
          by_contra hcon
          exact absurd hneg (not_lt.2 (mul_nonneg (not_lt.1 hcon) hbb.le))
      · rw [negPairs_cons_cons, if_neg hab, hl, zero_add]

/-- **The sign changes of a list are those of an alternating subsequence.** -/
theorem exists_alt_sublist_of_pos (l : List ℝ) (hp : 0 < seqSignChanges l) :
    ∃ s : List ℝ, List.Sublist s l ∧ s.IsChain (fun u v => u * v < 0) ∧
      s.length = seqSignChanges l + 1 := by
  rw [seqSignChanges_eq_negPairs] at hp ⊢
  obtain ⟨a, t, ht⟩ : ∃ a t, l.filter (fun x => x ≠ 0) = a :: t := by
    cases hl : l.filter (fun x => x ≠ 0) with
    | nil => rw [hl] at hp; simp [negPairs] at hp
    | cons a t => exact ⟨a, t, rfl⟩
  have hne : ∀ y ∈ a :: t, y ≠ 0 := by
    intro y hy
    rw [← ht, List.mem_filter] at hy
    simpa using hy.2
  obtain ⟨s, hs, hc, hl⟩ := exists_alt_sublist a t hne
  refine ⟨a :: s, hs.trans (ht ▸ List.filter_sublist), hc, ?_⟩
  rw [ht, List.length_cons, hl]

/-- An alternating list has as many sign changes as its length less one. -/
theorem seqSignChanges_eq_of_isChain (l : List ℝ) (hc : l.IsChain (fun u v => u * v < 0)) :
    seqSignChanges l = l.length - 1 := by
  rw [seqSignChanges_eq_negPairs]
  match l, hc with
  | [], _ => rfl
  | [a], _ =>
    by_cases ha : a = 0
    · simp [ha, negPairs]
    · simp [ha, negPairs]
  | a :: b :: t, hc =>
    have hne : ∀ y ∈ a :: b :: t, y ≠ 0 := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      have hchain := List.isChain_iff_getElem.1 hc
      by_cases hi' : i + 1 < (a :: b :: t).length
      · exact (left_ne_zero_of_mul (hchain i hi').ne)
      · have hi1 : 0 < i := by simp only [List.length_cons] at hi hi' ⊢; omega
        have := hchain (i - 1) (by omega)
        simp only [Nat.sub_add_cancel hi1] at this
        exact (right_ne_zero_of_mul this.ne)
    rw [List.filter_eq_self.2 (fun y hy => by simpa using hne y hy)]
    clear hne
    induction t generalizing a b with
    | nil =>
      rw [negPairs_cons_cons, if_pos (List.isChain_cons_cons.1 hc).1, negPairs_singleton]
      rfl
    | cons c t ih =>
      obtain ⟨hab, hc'⟩ := List.isChain_cons_cons.1 hc
      rw [negPairs_cons_cons, if_pos hab, ih b c hc']
      simp only [List.length_cons]
      omega

/-- A sublist of the values along a chain of indices gives a chain of sign changes. -/
theorem zAltChain_of_sublist {x : ℤ → ℝ} {n : ℕ} {k : Fin n → ℤ} (hk : StrictMono k)
    {s : List ℝ} (hs : List.Sublist s (List.ofFn fun i => x (k i)))
    (hc : s.IsChain fun u v => u * v < 0) : ZAltChain x (s.length - 1) := by
  rcases Nat.eq_zero_or_pos s.length with h0 | hpos
  · rw [h0]; exact zAltChain_zero x
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 hs
  have hlen : s.length - 1 + 1 = s.length := Nat.sub_add_cancel hpos
  refine ⟨fun i => k (Fin.cast List.length_ofFn (f (Fin.cast hlen i))), ?_, fun i => ?_⟩
  · intro i j hij
    apply hk
    rw [Fin.lt_def, Fin.val_cast, Fin.val_cast]
    exact f.strictMono (by rw [Fin.lt_def, Fin.val_cast, Fin.val_cast]; exact hij)
  · have h1 := hf (Fin.cast hlen i.castSucc)
    have h2 := hf (Fin.cast hlen i.succ)
    rw [List.get_ofFn] at h1 h2
    change x (k (Fin.cast _ (f (Fin.cast hlen i.castSucc)))) *
      x (k (Fin.cast _ (f (Fin.cast hlen i.succ)))) < 0
    rw [← h1, ← h2]
    have := List.isChain_iff_getElem.1 hc i (by omega)
    simpa using this

/-- The sign changes along a chain of indices give a chain of sign changes. -/
theorem zAltChain_of_strictMono (x : ℤ → ℝ) {n : ℕ} {k : Fin n → ℤ} (hk : StrictMono k) :
    ZAltChain x (seqSignChanges (List.ofFn fun i => x (k i))) := by
  rcases Nat.eq_zero_or_pos (seqSignChanges (List.ofFn fun i => x (k i))) with h0 | hpos
  · rw [h0]; exact zAltChain_zero x
  obtain ⟨s, hs, hc, hl⟩ := exists_alt_sublist_of_pos _ hpos
  have := zAltChain_of_sublist hk hs hc
  rwa [hl, Nat.add_sub_cancel] at this

/-- A chain of `p` sign changes gives `S⁻(x) ≥ p`. -/
theorem le_zSignChanges_of_zAltChain {x : ℤ → ℝ} {p : ℕ} (h : ZAltChain x p) :
    (p : ℕ∞) ≤ zSignChanges x := by
  obtain ⟨k, hk, hneg⟩ := h
  refine le_iSup_of_le (p + 1) (le_iSup_of_le k (le_iSup_of_le hk ?_))
  have hc : (List.ofFn fun i => x (k i)).IsChain fun u v => u * v < 0 := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_ofFn] at hi
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact hneg ⟨i, by omega⟩
  rw [seqSignChanges_eq_of_isChain _ hc, List.length_ofFn, Nat.add_sub_cancel]

/-- **Comparison of sign changes through chains.** -/
theorem zSignChanges_le_of_zAltChain {x y : ℤ → ℝ} (h : ∀ p, ZAltChain x p → ZAltChain y p) :
    zSignChanges x ≤ zSignChanges y :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun hk =>
    le_zSignChanges_of_zAltChain (h _ (zAltChain_of_strictMono x hk))

/-! ## Chains pass back through the operations of the pyramid -/

/-- A chain of a subsequence is a chain of the sequence. -/
theorem ZAltChain.of_comp {x : ℤ → ℝ} {σ : ℤ → ℤ} (hσ : StrictMono σ) {p : ℕ}
    (h : ZAltChain (fun k => x (σ k)) p) : ZAltChain x p := by
  obtain ⟨k, hk, hneg⟩ := h
  exact ⟨σ ∘ k, hσ.comp hk, hneg⟩

/-- A chain of `c x` is a chain of `x`. -/
theorem ZAltChain.of_mul {x : ℤ → ℝ} {c : ℝ} {p : ℕ}
    (h : ZAltChain (fun k => c * x k) p) : ZAltChain x p := by
  obtain ⟨k, hk, hneg⟩ := h
  refine ⟨k, hk, fun i => ?_⟩
  have := hneg i
  have he : c * x (k i.castSucc) * (c * x (k i.succ)) =
      (c * c) * (x (k i.castSucc) * x (k i.succ)) := by ring
  rw [he] at this
  by_contra hcon
  exact absurd this (not_lt.2 (mul_nonneg (mul_self_nonneg c) (not_lt.1 hcon)))

/-- **The sum of consecutive terms**, `x(k) + x(k - 1)`. -/
def zPairSum (x : ℤ → ℝ) (k : ℤ) : ℝ := x k + x (k - 1)

/-- **A chain of `x(k) + x(k-1)` is a chain of `x`**: in each pair pick a term of the sign of
the sum. -/
theorem ZAltChain.of_pairSum {x : ℤ → ℝ} {p : ℕ} (h : ZAltChain (zPairSum x) p) :
    ZAltChain x p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact zAltChain_zero x
  obtain ⟨k, hk, hneg⟩ := h
  -- every term of the chain is nonzero
  have hy : ∀ i : Fin (p + 1), zPairSum x (k i) ≠ 0 := by
    intro i
    by_cases hi : (i : ℕ) < p
    · have h1 := hneg ⟨i, hi⟩
      have he : (⟨i, hi⟩ : Fin p).castSucc = i := Fin.ext rfl
      rw [he] at h1
      exact left_ne_zero_of_mul h1.ne
    · have h1 := hneg ⟨p - 1, by omega⟩
      have he : (⟨p - 1, by omega⟩ : Fin p).succ = i := Fin.ext (by simp; omega)
      rw [he] at h1
      exact right_ne_zero_of_mul h1.ne
  -- the chosen terms
  let j : Fin (p + 1) → ℤ := fun i => if 0 < x (k i) * zPairSum x (k i) then k i else k i - 1
  have hj : ∀ i, 0 < x (j i) * zPairSum x (k i) ∧ k i - 1 ≤ j i ∧ j i ≤ k i := by
    intro i
    simp only [j]
    split_ifs with hpos
    · exact ⟨hpos, by omega, le_rfl⟩
    · refine ⟨?_, le_rfl, by omega⟩
      have hyy : 0 < zPairSum x (k i) * zPairSum x (k i) := mul_self_pos.2 (hy i)
      have he : x (k i - 1) * zPairSum x (k i) =
          zPairSum x (k i) * zPairSum x (k i) - x (k i) * zPairSum x (k i) := by
        simp only [zPairSum]; ring
      rw [he]
      linarith [not_lt.1 hpos]
  have hprod : ∀ i : Fin p, x (j i.castSucc) * x (j i.succ) < 0 := by
    intro i
    have h1 := (hj i.castSucc).1
    have h2 := (hj i.succ).1
    have h3 := hneg i
    have h4 : 0 < (x (j i.castSucc) * x (j i.succ)) *
        (zPairSum x (k i.castSucc) * zPairSum x (k i.succ)) := by
      have he : (x (j i.castSucc) * x (j i.succ)) *
          (zPairSum x (k i.castSucc) * zPairSum x (k i.succ)) =
          (x (j i.castSucc) * zPairSum x (k i.castSucc)) *
            (x (j i.succ) * zPairSum x (k i.succ)) := by ring
      rw [he]
      exact mul_pos h1 h2
    by_contra hcon
    exact absurd h4 (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (not_lt.1 hcon) h3.le))
  refine ⟨j, Fin.strictMono_iff_lt_succ.2 fun i => ?_, hprod⟩
  have hki : k i.castSucc < k i.succ := hk Fin.castSucc_lt_succ
  have hle : j i.castSucc ≤ j i.succ := by
    linarith [(hj i.castSucc).2.2, (hj i.succ).2.1]
  refine lt_of_le_of_ne hle fun heq => ?_
  have := hprod i
  rw [heq] at this
  exact absurd this (not_lt.2 (mul_self_nonneg _))

/-- `S⁻(x(σ ·)) ≤ S⁻(x)` for a strictly increasing `σ`. -/
theorem zSignChanges_comp_le (x : ℤ → ℝ) {σ : ℤ → ℤ} (hσ : StrictMono σ) :
    zSignChanges (fun k => x (σ k)) ≤ zSignChanges x :=
  zSignChanges_le_of_zAltChain fun _ h => h.of_comp hσ

/-- `S⁻(x(k) + x(k-1)) ≤ S⁻(x)`. -/
theorem zSignChanges_pairSum_le (x : ℤ → ℝ) : zSignChanges (zPairSum x) ≤ zSignChanges x :=
  zSignChanges_le_of_zAltChain fun _ h => h.of_pairSum

/-! ## The binomial mask -/

/-- **The binomial mask on `ℤ`**:
`(w * x)(n) = (x(n+2) + 4x(n+1) + 6x(n) + 4x(n-1) + x(n-2))/16`. -/
theorem zconv_binomialMask5 (x : ℤ → ℝ) (n : ℤ) :
    zconv binomialMask5 x n =
      (x (n + 2) + 4 * x (n + 1) + 6 * x n + 4 * x (n - 1) + x (n - 2)) / 16 := by
  rw [zconv, tsum_eq_sum (s := Finset.Icc (-2 : ℤ) 2) fun m hm => by
    rw [binomialMask5_eq_zero hm, zero_mul]]
  obtain ⟨h1, h2, h3, h4, h5⟩ := binomialMask5_vals
  rw [show Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, h1, h2, h3, h4, h5]
  simp only [sub_neg_eq_add, sub_zero]
  ring

/-- Four sums of consecutive terms are the binomial coefficients, shifted by `2`. -/
theorem zPairSum_four (x : ℤ → ℝ) (n : ℤ) :
    zPairSum (zPairSum (zPairSum (zPairSum x))) (n + 2) =
      x (n + 2) + 4 * x (n + 1) + 6 * x n + 4 * x (n - 1) + x (n - 2) := by
  simp only [zPairSum]
  ring_nf

/-- `S⁻(w * x) ≤ S⁻(x)` for the binomial mask `w`. -/
theorem zSignChanges_binomial_le (x : ℤ → ℝ) :
    zSignChanges (zconv binomialMask5 x) ≤ zSignChanges x := by
  refine zSignChanges_le_of_zAltChain fun p h => ?_
  have he : zconv binomialMask5 x =
      fun n => (1 / 16 : ℝ) * zPairSum (zPairSum (zPairSum (zPairSum x))) (n + 2) := by
    funext n
    rw [zconv_binomialMask5, zPairSum_four]
    ring
  rw [he] at h
  have h1 := h.of_mul.of_comp (σ := fun n => n + 2) fun a b hab => by
    simp only; omega
  exact h1.of_pairSum.of_pairSum.of_pairSum.of_pairSum

/-- The binomial mask commutes with differences. -/
theorem zDiff_zconv_binomialMask5 (x : ℤ → ℝ) :
    zDiff (zconv binomialMask5 x) = zconv binomialMask5 (zDiff x) := by
  funext n
  simp only [zDiff, zconv_binomialMask5]
  ring_nf

/-! ## `prop:classical-pyramids-approximate`(4) -/

/-- **`prop:classical-pyramids-approximate`(4), lattice non-creation.** For every real sequence
`x`, `y = w * x` and `z(k) = y(2k)` satisfy `S⁻(z) ≤ S⁻(y) ≤ S⁻(x)` and
`S⁻(Δz) ≤ S⁻(Δy) ≤ S⁻(Δx)`. -/
theorem classical_pyramids_approximate_4 (x : ℤ → ℝ) :
    zSignChanges (fun k => zconv binomialMask5 x (2 * k)) ≤ zSignChanges (zconv binomialMask5 x) ∧
      zSignChanges (zconv binomialMask5 x) ≤ zSignChanges x ∧
      zSignChanges (zDiff fun k => zconv binomialMask5 x (2 * k)) ≤
        zSignChanges (zDiff (zconv binomialMask5 x)) ∧
      zSignChanges (zDiff (zconv binomialMask5 x)) ≤ zSignChanges (zDiff x) := by
  set y := zconv binomialMask5 x with hy
  have h2 : StrictMono fun k : ℤ => 2 * k := fun a b hab => by simp only; omega
  refine ⟨zSignChanges_comp_le y h2, zSignChanges_binomial_le x, ?_, ?_⟩
  · -- `Δz(k) = Δy(2k+1) + Δy(2k)`
    have he : (zDiff fun k => y (2 * k)) = fun k => zPairSum (zDiff y) (2 * k + 1) := by
      funext k
      simp only [zDiff, zPairSum]
      rw [show 2 * k + 1 - 1 = 2 * k by ring, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
      ring
    rw [he]
    exact (zSignChanges_comp_le (zPairSum (zDiff y)) (σ := fun k => 2 * k + 1)
      fun a b hab => by simp only; omega).trans (zSignChanges_pairSum_le _)
  · rw [hy, zDiff_zconv_binomialMask5]
    exact zSignChanges_binomial_le _

end Pyramids
