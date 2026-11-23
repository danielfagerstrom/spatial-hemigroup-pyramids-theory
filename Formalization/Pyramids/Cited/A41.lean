/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Daniel Fagerström
-/
import AffineHemigroup.Interfaces
import Mathlib.Probability.Independence.Basic

/-!
# Ledger A41: Khintchine's theorem on null arrays (Sato, Thm. 9.3, p. 47)

Interface node `thm:cited-A41` (`blueprint/src/parts/02-cited-facts.tex`); ledger entry A41 of
`blueprint/AXIOMS.md`, cited from Sato, *Lévy Processes and Infinitely Divisible Distributions*,
Theorem 9.3, printed p. 47, with Definition 9.2 and (9.1) on the same page.

The author admitted A41 on 2026-11-13. **This file declares no axiom.** The statement, typed at the
page's letter with random variables (the skeleton's finding 8), is derived from the affine export's
axiom `AffineHemigroup.khintchine_null_array` (its ledger A6, the same theorem of Sato, transcribed
there from the same page), which states it for the laws of the rows. Two steps connect them, both
proved here:

1. **The law of a row sum.** For independent `Z₁, …, Z_m` the law of `Z₁ + ⋯ + Z_m` is the
   convolution of their laws (`map_sum_eq_convList`, by induction on `m` from Mathlib's
   `IndepFun.map_add_eq_map_conv_map`).
2. **Empty rows.** The affine axiom asks every row to be nonempty, `r_n ≥ 1`, a narrowing it records
   beside itself; this statement allows `r_n = 0`. Each row is given one more entry, the point mass
   at `0`, in front. That changes neither the row sum's law (`δ₀ ∗ ρ = ρ`) nor the maximum in (9.1)
   (`δ₀{|x| > ε} = 0`), and makes every row nonempty.

So `#print axioms` names `khintchine_null_array` and nothing of A41's own.
-/

namespace Pyramids

open AffineHemigroup
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

variable {d : ℕ}

/-- **The law of a sum of independent random variables is the convolution of their laws**, in the
affine export's `convList` (right-nested, `convList [] = δ₀`). -/
theorem map_sum_eq_convList {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    ∀ (m : ℕ) (Z : Fin m → Ω → Rd d), (∀ k, Measurable (Z k)) → iIndepFun Z P →
      P.map (fun ω => ∑ k, Z k ω) = convList (List.ofFn fun k => P.map (Z k))
  | 0, Z, _, _ => by
    simp [convList, Measure.map_const]
  | m + 1, Z, hZ, hind => by
    rw [List.ofFn_succ, convList]
    have ih := map_sum_eq_convList P m (fun k => Z k.succ) (fun k => hZ _)
      (hind.precomp (Fin.succ_injective _))
    have hsum : (fun ω => ∑ k, Z k ω) = Z 0 + fun ω => ∑ k : Fin m, Z k.succ ω := by
      ext ω : 1
      simp [Fin.sum_univ_succ]
    have hind' : IndepFun (∑ j ∈ Finset.univ.map (Fin.succEmb m), Z j) (Z 0) P :=
      hind.indepFun_finsetSum_of_notMem hZ (by simp)
    have hfun : (∑ j ∈ Finset.univ.map (Fin.succEmb m), Z j) =
        fun ω => ∑ k : Fin m, Z k.succ ω := by
      ext ω : 1
      simp [Finset.sum_apply]
    rw [hfun] at hind'
    have hmeas : Measurable fun ω => ∑ k : Fin m, Z k.succ ω :=
      Finset.measurable_sum _ fun k _ => hZ _
    rw [hsum, hind'.symm.map_add_eq_map_conv_map (hZ 0) hmeas, ih]

/-- **`thm:cited-A41`** (Sato, Thm. 9.3, p. 47). A null array `Z n k`, `k < r n`, on a probability
space, independent within each row, with `max_k P[|Z n k| > ε] → 0`: if the law of `S_n - b_n`
converges to `μ` (against every bounded continuous function), `μ` is infinitely divisible. Derived
from `AffineHemigroup.khintchine_null_array` (module docstring). -/
theorem cited_A41 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : ℕ → ℕ) (Z : (n : ℕ) → Fin (r n) → Ω → Rd d) (hZ : ∀ n k, Measurable (Z n k))
    (hind : ∀ n, ProbabilityTheory.iIndepFun (Z n) P)
    (hnull : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ⨆ k : Fin (r n), P {ω | ε < ‖Z n k ω‖}) atTop (𝓝 0))
    (b : ℕ → Rd d) (μ : Measure (Rd d)) [IsProbabilityMeasure μ]
    (hconv : ∀ f : Rd d →ᵇ ℝ,
      Tendsto (fun n => ∫ ω, f ((∑ k, Z n k ω) - b n) ∂P) atTop (𝓝 (∫ x, f x ∂μ))) :
    IsInfinitelyDivisible μ := by
  classical
  -- the rows, with the point mass at `0` put in front
  let L : (n : ℕ) → Fin (r n + 1) → Measure (Rd d) := fun n =>
    Fin.cons (Measure.dirac 0) fun k => P.map (Z n k)
  have hL0 : ∀ n, L n 0 = Measure.dirac 0 := fun n => rfl
  have hLs : ∀ n (k : Fin (r n)), L n k.succ = P.map (Z n k) := fun n k => rfl
  have hprob : ∀ n k, IsProbabilityMeasure (L n k) := by
    intro n k
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [hL0]; infer_instance
    · rw [hLs]; exact Measure.isProbabilityMeasure_map (hZ n k).aemeasurable
  have hS : ∀ ε : ℝ, MeasurableSet {x : Rd d | ε < ‖x‖} := fun ε =>
    measurableSet_lt measurable_const measurable_norm
  -- (9.1) is unchanged
  have hsup : ∀ (ε : ℝ), 0 < ε → ∀ n,
      (⨆ k, L n k {x | ε < ‖x‖}) = ⨆ k : Fin (r n), P {ω | ε < ‖Z n k ω‖} := by
    intro ε hε n
    refine le_antisymm (iSup_le fun k => ?_) (iSup_le fun k => ?_)
    · refine Fin.cases ?_ (fun k => ?_) k
      · rw [hL0, Measure.dirac_apply' _ (hS ε)]
        simp [Set.indicator, hε.not_gt]
      · rw [hLs, Measure.map_apply (hZ n k) (hS ε)]
        exact le_iSup (fun k : Fin (r n) => P {ω | ε < ‖Z n k ω‖}) k
    · refine le_iSup_of_le k.succ ?_
      rw [hLs, Measure.map_apply (hZ n k) (hS ε)]
      rfl
  -- the law of the row sum is unchanged
  have hlaw : ∀ n, convList (List.ofFn (L n)) = P.map (fun ω => ∑ k, Z n k ω) := by
    intro n
    rw [List.ofFn_succ, convList, hL0]
    change Measure.dirac 0 ∗ convList (List.ofFn fun k => P.map (Z n k)) = _
    rw [← map_sum_eq_convList P (r n) (Z n) (hZ n) (hind n)]
    haveI : IsProbabilityMeasure (P.map fun ω => ∑ k, Z n k ω) :=
      Measure.isProbabilityMeasure_map (Finset.measurable_sum _ fun k _ => hZ n k).aemeasurable
    exact Measure.dirac_zero_conv _
  refine khintchine_null_array (fun n => r n + 1) (fun n => Nat.succ_pos _) L hprob
    (fun ε hε => ?_) b μ (fun f => ?_)
  · simpa only [hsup ε hε] using hnull ε hε
  · refine (hconv f).congr fun n => ?_
    have hmeas : Measurable fun ω => ∑ k, Z n k ω := Finset.measurable_sum _ fun k _ => hZ n k
    haveI : IsProbabilityMeasure (P.map fun ω => ∑ k, Z n k ω) :=
      Measure.isProbabilityMeasure_map hmeas.aemeasurable
    rw [hlaw n, Measure.conv_dirac, Measure.map_map (measurable_add_const _) hmeas,
      integral_map ((measurable_add_const _).comp hmeas).aemeasurable
        f.continuous.aestronglyMeasurable]
    simp [sub_eq_add_neg]

end Pyramids
