# Response plan: external review round 2 of the theory paper

*The input is round 2 of `PROCESS.md` § 9, against the build frozen at the tag `pyramids-review-r2`
(paper 115 pp., supplement 46 pp.). The author ran part A, the content review, in GPT-6.2 Astra at
its Ultra setting on 2026-11-23: `reviews/review-A-r2-gpt6.2-astra-ultra.md`, with the PDF it
returned beside it. Part B was not run this round.*

*Every finding was checked against the text of r2, its LaTeX at the tag, the blueprint and the Lean
before it was sorted. Six agents that did not write the text did the checking:*
- *opus: the headline claims, the local proofs, the four "open" questions and the numerics;*
- *sonnet: the trust base, prior work and prose;*
- *the librarian: the sources, read from held copies.*

*The numerics checker reran the scripts and recomputed in high precision (mpmath). Locations are
`file.tex:line` at the tag. Pages are r2's printed pages, and statement numbers are r2's.*

## Summary

The reviewer recommends major revision and says the principal theorems stand. The checks agree:
**no statement of record is false and no theorem fails.** What the review finds is of four kinds.

1. **Four questions the paper calls open are settled**, three as worded and one on its natural
   reading (§ 7.2 and pp. 76, 84, 85, 102). Each answer is short, and each was checked step by step:
   - (1) the first-rung Gaussian creation follows from Prop. 5.15(4) by taking the least rung;
   - (2) a principle after decimation fails for the (2d+1)-point resolvent, by a finite example;
   - (3) no isotropic exact grid pyramid under x ↦ qRx, by the proof of Prop. 6.5;
   - (4) no rotation-invariant refinable law with a finite mask other than δ₀, by analytic
     continuation.
2. **Two sentences are false as printed, and a set of others are loose.**
   - A carrying family (Def. 6.3) need not be symmetric. The reviewer's drift
     b(t) = t sin(2π log_q t) v checks out. Yet p. 108 says "Symmetry is required of every family
     studied", and p. 84 applies the symmetric results of § 3 to every carrier. Every theorem of § 6
     holds for every carrier: Lemma 6.4 assumes no symmetry.
   - The loose sentences omit a hypothesis or blur two objects: the cascade, integer decimation,
     knot law against increment, and the selection's clock.
3. **Small slips in shared text**, none severe, each a word or a phrase:
   - the shell indices of Prop. 3.14;
   - "R fixes only 0" (p. 90);
   - the compensator parenthetical (p. 46);
   - Prop. 3.20(4)(b), which needs "symmetric" and |e| = 1, both of which the Lean has;
   - t > 0 in Thm 5.19(3);
   - C > 0 in Def. 6.2(2), which the Lean has.
4. **Attribution, numerics and the trust base.**
   - Maejima and Ueda (2009), Thm 3.3, is the knot criterion of Prop. 3.20(1) for one span. It is
     not cited. The librarian acquired it.
   - The pair (0.7, 3.0) of the sampled-Gaussian check has a true negative coefficient
     (−2.82·10⁻³³ at ±36). The text calls the printed number rounding and lets it read as no
     negative coefficient.
   - Figure 2's log-periodic part is plotted, not proved.
   - p. 102 says lattice points carry no mass when they do.
   - p. 113 names a public export, a tag and a DOI that do not exist yet.

What the reviewer got wrong or asks for needlessly is short:
- Thm 3.12(1)'s converse is correct as stated.
- Prop. 5.18 already keeps symmetry in d = 1.
- The Burt–Adelson distinction, the point-mass exception and Prop. 4.5's degree restriction are
  already in the text.
- The cuts it proposes for a journal version are a restructuring, not a correction.

| Verdict | Items |
|---|---|
| holds; a statement or proof of record to change | §3 Prop. 3.14 indices; p. 46; 3.20(4)(b); 5.19(3); p. 90; Def. 6.2(2) |
| holds; prose false as printed | False scope statement (p. 108, p. 84); open questions (1), (3), (4); p. 102; p. 113 |
| holds; prose loose or incomplete | most of §2; p. 32; p. 40; p. 72; p. 76; p. 105; S.17, S.23, S.35, S.39, S.42, S.43; [28]; R1; Figure 2; Table 1's caption |
| partly; ill-posed question | open question (2) |
| already done | Prop. 5.18 symmetry; Burt–Adelson residual; point-mass exception; 4.5's step and degree; Def. 6.2(ii) and the sampled Gaussian; the admitted facts' checks |
| wrong as an error claim | Thm 3.12(1)'s converse (an optional clause) |
| optional strengthening | Prop. 5.15(1) without μ̂ ≥ 0 (the reviewer's proof checks) |

## The findings

### § 2, headline claims

| Item | Finding | Check | Response |
|---|---|---|---|
| Bounded support | "any family continuous in scale" drops the cascade (abstract, p. 3, p. 107); p. 108 says continuity alone excludes finite masks | partly. "Family" is the term of art (Def. 3.1 has (I1)), but unqualified. The uniform-law counterexample checks. Point-mass exception already stated. | **Accept** (A): "hemigroup" or "cascade" in the three places; p. 108 names both hypotheses. |
| Classification | "cannot be read off from the line" (p. 3, `01-introduction.tex:107`; p. 107) | **confirmed** misleading. Lemma 3.16 determines an isotropic family by its marginal; the fully covariant classes also shrink with d (p. 32). | **Accept** (A): extendibility to dimension d is the point, not determination. "Kernel" in the abstract means μ_t; add it. |
| Line and grids | nested scalar grids need integer q, never stated | partly. Decimation claims are already restricted to integer q. | **Accept** (A): one sentence where Def. 6.3 first applies the array on qⁿΓ. |
| Selection | which relabellings keep the clock | partly. The introduction names 𝒢_q; the abstract's "a relabelling that keeps this" is ambiguous. | **Accept** (A): the abstract names g(qt) = q g(t). |
| Level differences | p. 2 cites Figure 4 for the Gaussian ladder | **confirmed**. Figure 4 is the Matérn step. The Burt–Adelson point is already made (p. 74). | **Accept** (A): move the reference. p. 4 says the input depends on the level. |
| Exactness and isotropy | "exact or isotropic, but not both" suggests an empty option | **confirmed**. Isotropy is defined through a carrier. | **Accept** (A): one sentence on p. 4. |
| Verification | the abstract lacks the boundary of § 1.1 | partly. | **Accept** (A): one sentence: the prose, the numerics and the statement comparison are outside. |
| False scope statement | carriers need not be symmetric | **confirmed**: the drift counterexample satisfies (a)–(d), and the knots stay symmetric. False: p. 108 (`07-discussion.tex:69–72`). Loose: p. 84 (`06-price.tex:12–16`), p. 2 on (ND). | **Accept** (A): p. 108 "the mask is symmetric; a carrier need not be"; p. 84 cites Lemma 6.4 or "some carrier is symmetric (Prop. 6.7)"; p. 2 qualifies (ND). |

### § 3, mathematical correctness

| Item | Finding | Check | Response |
|---|---|---|---|
| Lemmas 3.3–3.5, p. 46 | the compensator parenthetical is insufficient before finiteness | **confirmed** (wording). `04-line.tex:395`, shared. | **Accept** (B): "(Lemma 3.4)". |
| Thm 3.12(1) | specify zero initial data | wrong as an error. The converse claims only an isotropic family, and the Lean has no such hypothesis. | **Optional** (B): one clause naming the origin data (a(t)−a(0), ν_t−ν_0). |
| Prop. 3.14 | "over each octave … rises from w_i to w_{i−1}" | **confirmed**. True on [1, q] only; on [qⁿ, qⁿ⁺¹] the indices are i−n, i−n−1. `03-pyramid.tex:775`, shared; the Lean does not formalize the clause. | **Accept** (B): "over [1, q]", or the general indices. |
| p. 32 | knot-atom cascades and q-Cin rays called "families" | **confirmed**. They violate (I2) or are exponents. The conclusion holds. | **Accept** (A): one sentence. |
| Prop. 3.20(4)(b) | Gaussian part and Lévy measure do not fix the drift; |e| = 1 | partly. Read through Lemma 3.4 it is symmetric already; read with Sato's triplet it is not. The Lean (`htrans`, `he`) has both. | **Accept** (B): "the symmetric law with transform …" and "if moreover |e| = 1". No Lean change. |
| p. 40 | the cubic spline read "as a knot kernel" | **confirmed**: it is the kernel of no family. | **Accept** (A): "a refinable law, a solution of the knot relation". |
| Prop. 4.5's step | — | the reviewer's check is right; the text already separates the five-tap case and keeps r ≥ 2. | **None.** |
| Prop. 5.18 in d = 1 | keep symmetry | already done (Def. 5.17, Prop. 5.18). | **None.** |
| Thm 5.19 remarks | clock, domains, projections | no erroneous target found. | **None** (S5 below adds a lead). |
| Prop. 5.15(1) | needs only absolute continuity | **confirmed**: the reviewer's proof checks, step by step. | **Strengthen** (C), by the standing rule: drop μ̂ ≥ 0 from (1), Lean with it. |
| p. 76 | "grows faster than every C_ε e^{ε\|ω\|²}" | **confirmed**: false for ε ≥ a; the conclusion stands. | **Accept** (A): "for ε < a". |
| Thm 5.19(3) | μ_{0,t} needs t > 0 | **confirmed**; the Lean has `0 < t`. | **Accept** (B): one word. |
| p. 90 | "as R fixes only 0" | **confirmed** false (R = I); the step needs R injective. `06-price.tex:375`, shared. | **Accept** (B): "as R maps only 0 to 0". |
| Frame weights, −3/10 | — | both verified. | **None.** |
| S.38–S.39 | "log-uniform density dθ/θ" against U = 2 dθ/θ | **confirmed**, factor 2 against (5.1) of the cone paper (read at its tag). | **Accept** (A): name dθ/θ the mixing measure and U = 2·1_{θ>1/c} dθ/θ. |

### § 3, the four "open" questions (R7 in part, R8)

| Question | Where | Check | Response |
|---|---|---|---|
| (1) first-rung Gaussian creation | § 7.2(1), p. 108; p. 76 (`05-matern.tex:1418–1428`) | **settled, yes.** The least rung j with two maxima has one maximum at j−1, as a positive Gaussian mixture attains its maximum; dilation places the pair at any τ. | **Strengthen** (C): Prop. 5.15(4) states that some rung has one maximum and the next two (`Nat.find` and one lemma in `creation_plane_4`). Withdraw the question and the p. 76 contrast. |
| (2) a principle after decimation | § 7.2(2), pp. 108–109; p. 84 (`05-matern.tex:2003–2005`) | **ill-posed as printed** ("a principle"). The pointwise reading fails: u(0) = 1, u(±he_j) = 2, f = (I − τΔ_h)u gives f(0) = 1 − 2dτ/h² < u(0) after decimation. The frame mask fails before decimation already (Prop. 6.6). | **Replace** (C): the example as a small statement, a finite computation. |
| (3) similarities x ↦ qRx | § 7.2(3), p. 109 | **settled, no.** The proof of Prop. 6.5 carries over: qR A Rᵀq = A forces A = 0; the jump measure is a countable sum. It needs neither MΓ ⊆ Γ nor M = qR, only M expanding. | **Decision D1.** |
| (4) isotropic refinable limits of finite masks | p. 85 (`06-price.tex:33–35`), p. 102 (`:1285–1288`) | **settled, no**: ŵ = μ̂(q·)/μ̂ is radial near 0, analytic, so radial everywhere; a finite invariant mask is δ₀. | **Replace** (C): a new proposition, with Lean (the identity theorem for analytic functions). |

### § 3, checks on the ten admitted facts; § 5, the trust base

| Item | Check | Response |
|---|---|---|
| Admitted facts | the reviewer confirms each; A^S = 2A and the zero centering are already stated | **None.** |
| Inventory (27 interfaces; 5.19(2)) | consistent; the paper already distinguishes declaration from theorem | **None.** |
| "Every step is machine-checked" | 56 proof sign-offs, inside shared proofs; § 1.1 never defines the phrase | **Accept** (A): one sentence in § 1.1 that the sign-off means the formal counterpart of the numbered statement. Round 1's D4 keeps the sign-offs. |
| Public tag v0.1 and DOI, p. 113 | **confirmed**: the declarations name a public export, tag v0.1 and a DOI "printed on its first page"; p. 1 is a working draft with no DOI; both URLs return 404 | **Decision D3.** |
| Bernstein facts "read by no proof" | true of the formal development, not of §5's prose (pp. 65–66) | **Accept** (A): "read by no formal proof". |
| p. 7 "each fact a proof takes as given" | standard background (Lévy continuity, Steinhaus, Radon–Nikodym, the chain rule) is used unlisted | **Accept** (A): one clause. |

### § 4, numerical examples (R9, S3)

| Item | Check | Response |
|---|---|---|
| Table 1 | all twelve entries reproduce exactly; window halving leaves seven digits; roundoff below 2·10⁻¹⁶. The caption does not say that the script convolves directly with a window-cut, renormalized kernel, while the text describes the recursion | **Accept** (A): two caption sentences (the method, the physical window, renormalization, the halving check). |
| Sampled Gaussians | the paper concludes only for the first two pairs. In high precision (0.7, 3.0) has −2.82·10⁻³³ at ±36 (periodic grid and infinite lattice agree); the printed "−2·10⁻¹⁷, which is rounding" is noise. The trend sentence mixes scale and ratio | **Accept** (A): state the (0.7, 3.0) value by high-precision evaluation (script in mpmath), or drop the pair; reword the trend. |
| Fourth-moment certificate (S3) | **valid** for (0.5, 0.6) on ℤ: E Y² = 0.1366, E Y⁴ = 0.0160 < E Y². Fails for the other pairs | **Accept** (A): a paragraph turning the (0.5, 0.6) evidence into a proof on the infinite lattice, marked as printed and not formalized. |
| Figure 2 | the nonconstant log-periodic part is plotted, not proved (it is true: its Fourier coefficients have modulus 1/(2π\|k\|)); the caption's "so" skips the convergence step; cutoffs missing | **Accept** (A): soften to what is shown and give the cutoffs (m ≤ 89; the quadrature). The Mellin proof is optional. |
| Figure 4 | numbers reproduce; "two maxima" is a grid count | **Accept** (A): name the detection rule. |
| Figure 5, p. 102 | masses reproduce (ratio 1.4102). p. 102 says the other points of the circle carry no mass; the ten other lattice points do | **Accept** (A): "the nonlattice points"; the right panel's mesh, cutoffs and solver in the caption. |

### § 6, prior work (R1, R10)

| Item | Check | Response |
|---|---|---|
| Maejima–Ueda (R1) | **confirmed**: Thm 3.3 (arXiv:0911.3449, p. 5; Commun. Stoch. Anal. 3(3), 2009): for b > 1, ρ infinitely divisible with μ̂(z) = μ̂(b⁻¹z)ρ̂(z) iff ρ has a log moment and μ = Φ_b(ρ), the product from power 0; in ℝ^d, no symmetry. The paper cites Maejima–Naito, Sato § 15 and Maejima–Sato, claims none of this as new, and attributes nothing to Prop. 3.20(1) | **Accept** (A): cite Maejima–Ueda at Prop. 3.20's lead and in § 1's relation to the literature; say the probability content of the knot criterion is theirs (the product indices differ by one). The statement is unchanged. |
| Burt 1981 | p. 1's "leaves the family open" against Obs. 1 (p. 24, the characteristic kernel) | partly: the introduction cites Obs. 1 and narrows the claim; the abstract does not. **Accept** (A): a clause in the abstract. |
| Hanke–Groetsch, Radmoser et al. | [28] "Weicker" | **confirmed**, in the `.bib` and in Zotero. **Accept**: the librarian corrects the Zotero item and re-exports. |
| p. 72 "only as q ↓ 1" | **confirmed**: the first term dominates at low frequency for fixed q. **Accept** (A). |
| S.43 Mallat "no hemigroup law" | **confirmed**: nested projections compose. **Accept** (A): "no convolution hemigroup of probability laws". |
| p. 105, γ ≤ d/2 | **confirmed**: γ = 0 is δ₀. **Accept** (A): 0 < γ ≤ d/2. |
| Lindeberg time-causal (S4) | p. 65 already identifies the exponent with Lindeberg 2016's limit kernel; Thm 2.13's two sections are the line form of the reflection identity | **Accept** (A): one sentence tying Thm 2.13 to it. |
| S.35 "raw unit mass" | **confirmed**: each polyphase part sums to 2⁻ᵈ. **Accept** (A). |

### § 7, exposition; § 8, the rest

| Item | Check | Response |
|---|---|---|
| Four objects at first use; S1 (Figure 1) | partly done: Figure 1's caption separates the knot kernel from the stored level. W_n is not drawn | **Accept** (A): name origin law and increment at first use; Figure 1 gains W_n in its caption (drawing optional). |
| Def. 6.2(2), λ(qΓ) > 0 (R12) | **confirmed**: printed without it; the Lean `IsExactSubsampleIn` has `0 < ∑'` | **Accept** (B): "with C > 0". |
| Fixed-spacing Laplace example | partly: the grid-Helmholtz parameter depends on h, never said | **Accept** (A): a clause. |
| Supplement wording: S.17, S.23, S.42 | **confirmed**: S.17 calls the generator δ² a step; S.23 lacks "exact"; S.42's "create no extrema" counts sign changes | **Accept** (A): a phrase each. S.25–S.26 already done. |
| S2 (one worked example of the normalizations) | the conventions are stated but scattered | **Accept** (A): one paragraph in § 2.1.5. |
| S5 (a lead for the rank-one argument and the clock) | partly: p. 79 has a lead; the clock recovery has none | **Accept** (A): a short lead before Thm 5.19's proof. |
| What to cut; S6 | a restructuring for a journal version | **Decision D2.** |

## Found while checking

- Table 1's text says the pyramid is computed "by one forward and one backward recursion"
  (`04-line.tex:728`), while the table's script convolves directly. The caption fix above covers
  it.
- The double-precision value printed for (2.0, 2.5) is off in its fourth digit (−2.82285·10⁻⁷
  against −2.82256·10⁻⁷). The printed −2.8·10⁻⁷ stands.

## Decisions for the author

- **D1. Similarities x ↦ qRx (open question (3)).** The answer is no, and the proof is that of
  Prop. 6.5 with D_q replaced by an expanding matrix M. The options:
  - a printed remark with its proof, listed in § 1.1 as not formalized;
  - a blueprint node with a Lean generalization of Def. 6.3(c) and Prop. 6.5(1)–(2) to M. This
    is larger: the carrying ladder and the knot lemma are stated for D_q.

  **Recommendation:** the printed remark now, with the Lean as optional later work. The paper's
  scope is the scalar ratio, and the remark only closes the question it raises.
- **D2. The journal-length cuts (§ 7 "What to cut", S6).** Moving the supplement-like
  material and the verification ledgers to companion material is a restructuring for a journal
  submission. **Recommendation:** keep the preprint as it is and record the list for the
  journal version.
- **D3. The verification export (p. 113).** The declarations name `spatial-hemigroup-pyramids-theory`
  at tag v0.1 and a DOI on the first page, none of which exists in a draft. **Recommendation:**
  word the declarations for the draft state ("will be deposited at the release"), and keep the
  release wording in the AI statement's list of what to update. The declarations are the author's.

**Settled by the author (2026-11-23):** "Yes, as recommended. But D1 should be part of the
blueprint, so that we are explicit about its state."
- **D1:** a blueprint node, not a paper-side remark. It is a proposition with its printed proof,
  marked `\notready`, as `prop:subsampling-discrepancy` is. If a Lean statement can be typed
  against a matrix form of Def. 6.3, it goes in the skeleton, unproved. § 1.1 and the abstract then
  name it among what is proved in print only. It belongs to batch C.
- **D2:** deferred to a journal version. The list stays in this plan.
- **D3:** the declarations are worded for the draft state (batch A).

## Batches

- **Batch A (paper-side prose, captions, the bibliography, one script):**
  - every "Accept (A)" above;
  - the withdrawn questions (1) and (4) and the replaced (2), whose new statements come in batch C;
  - Maejima–Ueda in `references.bib`;
  - the librarian's Weickert correction;
  - `sampled_gaussian_increments.py` gains a high-precision run for (0.7, 3.0);
  - the fourth-moment paragraph;
  - then a blind register review of the new prose, and the summaries compared with their statements.
- **Batch B (shared text, no Lean change):**
  - Prop. 3.14's indices;
  - p. 46's parenthetical;
  - Prop. 3.20(4)(b);
  - Thm 5.19(3)'s t > 0;
  - p. 90;
  - Def. 6.2(2)'s C > 0;
  - optionally Thm 3.12(1)'s origin data.

  Through the blueprint, then transcribed, with `linkage check` verbatim.
- **Batch C (shared text with Lean, one VM run):**
  - Prop. 5.15(1) without μ̂ ≥ 0, a strengthening;
  - Prop. 5.15(4) with the first rung, a strengthening;
  - the decimation example (2);
  - the finite-mask proposition (4);
  - the similarity node (3), printed proof, `\notready` (D1).

  These are new nodes or clauses, so the numbering, the axiom guard and Table 4 change.
- **Then the freeze `pyramids-review-r3`**, when the author wants a third round.

**Batch A's state (2026-11-23): done, except the open questions.** Every "Accept (A)" item is in:
- the abstract, the introduction, § 1.1, the § 2 lead and its worked example of the
  normalizations;
- the § 3 prose (p. 32, the Prop. 3.20 lead with Maejima–Ueda, p. 40);
- § 5 (p. 72, p. 76's quantifier, the time-causal factor, the lead before Thm 5.19's proof);
- § 6 (the lead, p. 102, p. 105);
- the discussion;
- the supplement (S.17, S.23, S.35, S.39, S.42, S.43);
- the captions of Figures 1, 2, 4, 5 and Table 1;
- the sampled-Gaussian paragraph with the fourth-moment argument;
- the declarations (D3);
- the bibliography: Maejima–Ueda added, and Weickert corrected here and in Zotero (the librarian,
  from the held PDF).

`scripts/sampled_gaussian_increments.py` now also evaluates (0.7, 3.0) at 60 digits and prints the
certificate's moments. The open questions (1), (2), (4) of § 7.2 and pp. 76, 84, 85 and 102 are
rewritten in batch C, once the statements that answer them exist. Question (3) is the D1 node.

A blind register review (draft-reviewer, opus) read the changed prose and checked every summary
against its statement. Its 25 flags are applied:
- a factor 2 in the worked example of the normalizations;
- the lead on Thm 5.19's clock, moved after the statement and completed with covariance and
  surjectivity;
- "in d ≥ 2" in the § 6 heading of the contributions and the § 6 lead;
- isotropy said of every carrying family;
- the fourth-moment argument's status in § 1.1;
- "smooth rapidly decreasing input";
- the rest, register.

It confirmed the fourth-moment mathematics and every other number it checked.

**Batch B's state (2026-11-23): done.** The six slips are fixed in the blueprint and transcribed
(`linkage check` verbatim):
- Prop. 3.14's indices, over [1, q] and [qⁿ, qⁿ⁺¹];
- Prop. 4.5(1)'s triplet, by Lemma 3.4;
- Prop. 3.20(4)(b): "the symmetric infinitely divisible law", and |e| = 1 in its last assertion;
- Thm 5.19(3): t > 0;
- Prop. 6.5(2)'s proof: "R maps only 0 to 0";
- Def. 6.2(2): C > 0.

Each matches what the Lean already states, so no Lean changes and no statement is renumbered. The
optional clause for Thm 3.12(1)'s origin data is not taken, since the statement is correct as it
stands. The computation paper's restated nodes are unchanged.

**Batch C's state (2026-11-23): done.** Through the blueprint, with Lean, and transcribed
(`linkage check` verbatim):
- Prop. 5.15(1) without μ̂ ≥ 0 and Prop. 5.15(4) with a rung of one maximum before the rise:
  strengthenings, `creation_plane_1` and `creation_plane_4`. A new clause (5), `creation_plane_5`,
  moves that rung to any variance by a dilation, which is the answer to question (1).
- The decimation example, Prop. 5.21 `prop:principle-after-decimation` (Lean core).
- The finite-mask proposition, Prop. 6.16 `prop:no-isotropic-refinable-finite-mask` (Lean core),
  for any probability mask carried by a finite set.
- D1: Prop. 6.6 `prop:expanding-grid-pyramid-not-isotropic`, for every expanding dilation matrix,
  printed proof, `\notready`; its statement is typed in the skeleton over `CarriesMatrixLadder`.
  § 1.1 and the abstract name it as proved in print only.
- The four questions are rewritten as their answers (§ 7.2, § 7.1, pp. 76, 84, 85, 102, § 1).
- The axiom guard has the two new declarations; Table 4 is regenerated; the renumbering is in
  `CHANGELOG.md`.

A blind register review (draft-reviewer, opus) read the new prose and found no mathematical error.
Its 18 flags are applied (`CHANGELOG.md` lists them). The next round is frozen at `pyramids-review-r3`.
