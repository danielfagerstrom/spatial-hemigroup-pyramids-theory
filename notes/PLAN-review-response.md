# Response plan: external review round 1 of the theory paper

*The input is round 1 of `PROCESS.md` § 9, against the build frozen at the tag `pyramids-review-r1`
(paper 112 pp., supplement 46 pp.). Both parts were run by the author in Gemini Argon 4 at its High
setting on 2026-11-22. Part B (presentation) is `reviews/review-B-r1-gemini-argon4-high.md`, and
part A (content, a referee report) is `reviews/review-A-r1-gemini-argon4-high.md`. Part A is sorted
in its own section below. Its answers are merged into the batches at the end.*

*Every finding was checked against the text of r1, its LaTeX at the tag, the blueprint and the Lean
before it was sorted. Four agents that did not write the text did the checking (opus for the
structural and mathematical findings, sonnet for notation and layout); their reports are summarised
in the table. Locations are `file.tex:line` at the tag, and pages are r1's printed pages.*

## Summary

*This summary covers part B. Part A's is at the head of its own section.*

None of the twenty findings is an error in the mathematics. One error that the review did not raise
was found while checking it, in § 1.1 (the trust base). It is fixed first (batch 0).

| Verdict | Findings |
|---|---|
| holds as stated | none in full |
| holds in part | 1, 2, 3, 4, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20 |
| already done in substance | 5, 8 |

Three of the reviewer's proposed additions are wrong as written and are corrected before use:
- **11:** the Sobolev threshold is $2$ against $d$, not against $d/2$.
- **10:** the profile's complete monotonicity is tied to the generator's form only on the line.
- **6:** the duality in the converse is over signed measures, and the converse also needs Step 2, that $\widehat\mu$ has no zero.

Two of its causes do not hold:
- **The repeated proof blocks do not "mirror Lean".** Lean proves the symmetric data, the tail bound, the split coupling and the sampled-Laplace series once each. The print works them out again.
- **The saving is not "~8 pages".** The duplicated text is about 2–2.5 pages.

## The findings

| # | Finding | Verdict | What was found | Answer |
|---|---|---|---|---|
| 1 | The front matter delays the mathematics to p. 19 | partly | Definition 3.1 is on p. 19, and § 2 has 33 items, five with proofs (2.2, 2.3, 2.9, 2.16, 2.22, about two pages). § 1.1 does not list the fifteen axioms: Table 2 does. § 1.1 does repeat Appendix A's inventory: the ten facts with their counts, "six of the fifteen", ScaleSpaceCore declaring no axiom, the six unread facts (`01-introduction.tex:275, 290–293`, against `appendix-verification.tex:20–28, 103–105`). The tools of § 2.2.2–2.2.4 are read only in § 5 and in the supplement. | **Accept in part** (batch 1): drop the inventory sentences of § 1.1 that Appendix A holds, keeping every caveat in § 1.1. **Decline**: compressing § 1.1 into one paragraph, and moving the cited facts out of § 2. The standard requires § 1.1 to own the trust base, and requires § 2 to hold the cited facts with their anchors (`WRITING.md` §§ 3–4). The five short proofs in § 2 stay. |
| 2 | The symmetric Lévy–Khintchine cancellation is repeated seven times; state a symmetric corollary | partly | It is worked out four times, not seven: Lemma 3.4 (p. 20), Prop. 5.16(3) (p. 74), Prop. 6.4 (p. 86) and Prop. 6.6 (p. 91). The other three of the reviewer's pages, and four the reviewer missed, are one-clause remarks. The symmetric form exists only for the kernels of a family (Lemma 3.4), with no converse. Lean has the general statement once (`exists_symData`, `isSymData_unique`, `SymLevyData.hasTriplet`). The generator as a superposition of second differences is already (2.2), p. 11, on the line only. | **Accept** (batch 2): a shared lemma, the symmetric Lévy–Khintchine form with uniqueness and its converse, bound to the existing Lean. The four derivations cite it. **Accept** (batch 1): one sentence reading (2.2) in $\mathbb R^d$ as a superposition of second differences of span $x$, in the § 2 lead or § 2.1.5. |
| 3 | The Matérn family and the Matérn pyramid are easily conflated | partly | The kernels and steps are as the reviewer writes them, at index 1. At index $\gamma$ the family's step is the $\gamma$-th power. The § 4.3 lead names both families, but nowhere sets them side by side. Prop. 5.20(1), p. 81, makes the contrast late. Both families are fully covariant, and a comparison must not suggest otherwise. | **Accept** (batch 1): two or three sentences in § 2.1.5 (the notation), and a clause in the § 4.3 lead. |
| 4 | "Exact" in senses (i)–(iii) is used forty pages before Definition 6.2; use descriptive names | partly | The senses are glossed in a bulleted list where § 4.2 first uses them (p. 43, `04-line.tex:296–309`), and § 4.3 points back to that list. The introduction's mention (p. 3) has no gloss. "Exact cascade" is the paper's own fourth use, and it is flagged. Definition 6.1 depends on § 6.4's kernels, so Definitions 6.1–6.2 cannot move to § 4.2 alone. The reviewer's name for (i) is narrower than Definition 6.2(1). | **Accept in part** (batch 1): a one-line gloss of the three senses at p. 3. **Decision D2**: whether the senses get descriptive names. The names are vocabulary, so the choice is the author's. Renaming touches the shared Definition 6.2 and about twelve uses. **Decline**: moving Definitions 6.1–6.2. |
| 5 | Read semi-selfdecomposability as pyramid refinability | done in substance | The dilation form is displayed in Lemma 3.8's proof (pp. 23–24). The § 3.2 opening says "the residual is a dilate of an octave step". Missing: the word "refinable" arrives only in § 3.5, 14 pages later. | **Accept** (batch 1): one sentence in the § 3.2 lead. Semi-selfdecomposable with span $q$ means refinable at ratio $q$ with an infinitely divisible mask, with a pointer to § 3.5. Definition 2.4 stays at Sato's letter. |
| 6 | Give the intuition before the stage lemma, Prop. 5.18 | partly | The implicit-Euler reading is in the § 5 and § 5.3 leads, and the grid clause of the proof is the PDE argument. The continuum sufficiency computes $f-u$ as a sum of second directional derivatives, without saying so. | **Accept** (batch 1): a short paragraph in the lead before Prop. 5.18. Sufficiency: at a weak local maximum $f-u=-\operatorname{tr}(C\nabla^2u)\ge0$, valid for every $\mu_C$, the derivatives falling on $f$. The converse in outline: a duality over finitely supported *signed* measures, with Step 2 (no zero of $\widehat\mu$) named. |
| 7 | Four proof blocks are repeated across §§ 3–6 | partly | Every copy is adapted, not verbatim, and every copy is inside a shared proof. (1) The tail bound appears in 3.19(2), 4.5(2), 5.19(1) and, as a lower bound only, in 6.6(1). (2) The coupling: the split coupling is redone in full only in 5.19(1), about 50 lines, because 3.19(2) states isotropy for the uniform coupling only. Lean's `ladder_knot_kernel_2_split_rot` already has both. (3) The telescoping appears in 3.19(1), 6.4(1), 6.6(1) and Supp. Thm S.30. The § 6 copies cannot cite 3.19(1), because Definition 6.3's family is not assumed symmetric. (4) The sampled-Laplace series appears in 4.5(4) and 6.4(3). | **Accept** (batch 2): add the isotropy clause for the split coupling to 3.19(2), with no Lean work, and let 5.19(1) and 4.5(2) cite it. 6.4(3) cites 4.5(4). A shared lemma for the § 6 telescoping (Lean's `knot_data`) lets 6.4(1) and 6.6(1) cite it. This brings the print onto the machine-checked route (`WRITING.md` § 4). |
| 8 | Two normalizations of the Gaussian part | done | The conversion is stated at every switch: Definition 2.10, Theorem 2.11(2), § 2.1.5, Lemma 3.4, 3.19(4)(b) and § 5 (p. 74). | **Decline.** Definition 2.10 and Theorem 2.11 restate a cited result at its letter, and 3.19(4)(b) already names its normalization. |
| 9 | κ_t, Δ_9, σ_9 and κ_t^9 are used before § 6.4 defines them | partly | Every use has a pointer, and § 6.1 says twice that § 6.4 "may be read first". σ_9 is not glossed at its first use (p. 93), and Figure 5's caption does not point to Prop. 6.15. | **Accept in part** (batch 1): the defining formulas of κ_t and σ_9 in the § 6.1 gloss (`06-price.tex:79–90`), and Prop. 6.15 in Figure 5's caption. **Decline**: moving § 6.4. Its proofs and § 6.2 depend on each other, and moving only the definitions would duplicate shared statements. |
| 10 | The Thorin–Bernstein detour splits § 5.1; its imaging meaning is never given | partly | Lemmas 5.5–5.7 serve only Props. 5.8–5.9. The step's meaning is given on pp. 62, 64 and 66, and in the supplement (p. S.38). The imaging stake of Prop. 5.9 is missing. The proposed motivation is wrong in $d\ge2$: the generator there is still a sum of resolvent differences, and Prop. 5.9 denies only the complete monotonicity of the profile. Prop. 5.8 holds in every dimension. | **Accept, corrected** (batch 1): two or three sentences before Prop. 5.9, saying what the profile property means and that on the line it is what makes the exponent a mixture of Laplace atoms, without tying it to the generator's form in the plane. **Decline**: the move, which would make the paper's order diverge from the blueprint's for no gain once the lead explains the detour. |
| 11 | Explain why the octave step is singular at 0 and the knot kernel smooth | partly | The singularity is Prop. 5.11(3), smoothness is Thm. 5.4(1), and the link to sampling and to the principle is stated (pp. 69, 80–81). The Sobolev reason is not given. The reviewer's version is wrong: $(1+\lvert\omega\rvert^2)^{-1}\in L^1(\mathbb R^d)$ only for $d=1$, so the comparison is two derivatives against $d$, not $d/2$. | **Accept, corrected** (batch 1): a remark of a few sentences after Prop. 5.11. One resolvent has a transform that decays like $\lvert\omega\rvert^{-2}$, integrable only on the line, with $d=2$ the logarithmic borderline. A cascade of $N$ resolvents has a bounded continuous density once $2N>d$, and the knot kernel's transform decays faster than any power. |
| 12 | Say that the grid input is read at scale 1; explain $U_n\ne V_n$ | partly | Scale 1 is stated only on pp. 46 and 98, and Figure 1's caption does not say it. The spatial reason for $U_n\ne V_n$ is stated three times; the Fourier account is not given. The reviewer's Fourier account is right: $U=V$ plus nonnegative cross-alias terms, present exactly when $n\ge2$. | **Accept** (batch 1): a sentence in Figure 1's caption and in the § 4.3 lead. A remark after Prop. 4.7 gives the Fourier account as an interaction of aliases across levels, which p. 98 distinguishes from the aliased mass of Prop. 4.7(3). The pre-smoothing reading of $\mu_{0,1}$ is worded as a reading, not a claim. |
| 13 | Show why the freedom between knots exceeds the relabellings | partly | The freedom is stated (p. 22, and Prop. 3.19(2)). The reason is in the proof, p. 34. The supplement says it in words (p. S.21), but its Figure 1 does not draw it. | **Accept** (batch 1): a remark of two to four sentences after Prop. 3.19. A relabelling runs one clock for every jump size, while the split coupling schedules small and large jumps in different halves of the octave. It carries a pointer to the supplement. |
| 14 | Prop. 4.5 re-proves the $d=1$ case of Props. 3.19 and 6.6 | partly | It is not literally that case. The hypotheses differ (Definition 4.4 against Definition 6.3, linked by Prop. 6.12(1)), and 4.5 has more content (an iff, no lattice support, the no-moment behaviour, clause (3)). § 4.1 already identifies operators with laws first. Clauses (1)–(3) already cite 3.19, except clause (1) and the converse construction in (2), about half a page. | **Accept in part** (batch 2): the converse in 4.5(2) cites 3.19(2) at $d=1$ with a folding translation (with 7). **Decline**: recasting 4.5 as the $d=1$ case of 6.6, a forward reference of 50 pages that would drop content. |
| 15 | Give the symmetric form of Schoenberg's representation next to Thm. 2.32 | partly | The derivation is correct, and it is already in the proof of Prop. S.39 (p. S.42). Thm. 2.32 as printed gives only necessity, so the remark does not make Thm. 2.15 "transparent". | **Accept** (batch 1): a three-line unnumbered remark after Thm. 2.32, marked as the paper's consequence and not part of the citation. It points to S.39. |
| 16 | Kernels on $\mathbb Z^d$ against laws on $h\mathbb Z^d$ | partly | Both readings occur. The clearest convention is at the head of § 6.4 (p. 100), seventeen pages after § 6.1. The proofs translate in one or two sentences each, not a paragraph. | **Accept** (batch 1): one convention paragraph at the head of § 6, with the reviewer's formulas, which are correct. Shortening the in-proof sentences is left to batch 2's re-transcription, where they are shared. |
| 17 | Symbol collisions; add a symbol table | partly | Each collision is real. Four of five are disclosed where they occur: $D_h$ against $D_c$ at p. 100, $L_r$ as an operator at p. 55, $\sigma_r$ against $\sigma_{d-1}$ at p. 26, the supplement's $\mu$ at Definition S.19. § 2.1.5 is a notation paragraph that does not cover $D_h$, $L_r$ or $\sigma$. $T_c$ is Sato's notation. | **Accept in part** (batch 1): extend § 2.1.5 to name the overloaded symbols and where each meaning is fixed. **Decline**: the renames. $D_h$, $D_5$, $D_9$ and the supplement's $\mu$ run through shared proofs, and $T_c$ is the source's notation. A table instead of the paragraph is the author's call (D3). |
| 18 | Proofs set as walls of text | partly | It holds for Prop. 5.15(3), p. 72: about 35 lines, with the italic step headers run in. It does not hold for Prop. 4.7(2) or Prop. 5.18(3), whose steps are separate paragraphs. Thm. 5.4(1)'s "For the density" starts mid-line. | **Accept** (batch 2, shared): paragraph breaks at the step headers of 5.15(3) and Thm. 5.4(1), with the Faà di Bruno bound and $m(\xi)$ displayed. |
| 19 | Add a strata table; Figure 5 is illegible | partly | There is no strata comparison table. Figure 5 is drawn 13.8 in wide and scaled by 0.45: titles and axes come out at about 4.5 pt, contour labels at about 3.2 pt. Its panel titles already say what each panel plots, and the caption explains the asymmetry. | **Accept** (batch 1): a table after Thm. 3.14, with "strictly" in the stratum-1 witness row (Prop. 3.12), and grid masks in stratum 2 only. Figure 5 redrawn in `scripts/make_figures_theory.py` at its printed width, with readable labels and the atom supports in the panel titles. |
| 20 | Table 3 floats past the References; double citations in proofs | partly | Table 3 (`[ht]`, `appendix-verification.tex:66`) prints alone on p. 112, after the References. There are about 20 double citations, of the form "[12, …, pp.] (Theorem 2.11)": none in § 6, most inside shared proofs. | **Accept** (batch 0): Table 3 placed in Appendix A. **Accept** (batch 2): the internal number alone in proofs, since § 2 carries the anchors. Paper-side copies (`03-pyramid.tex:413–418`, `04-line.tex:271, 570`) go in batch 1. |

## Part A: the referee report

Part A recommends major revision. It finds no false theorem and no gap in any proof (A§3), and it
checks the ten admitted facts against their sources (A§3.3), in agreement with the pass-7 audit. Its
three reasons for revision are these:
- The headline sentences drop scope. This holds in part (rows R1–R6 below).
- The paper is long and repetitive. This holds in part: about 3–4 pages, not 45–55 pages' worth.
- The main paper is not self-contained. This is a wrong premise. The paper never claims to be, and
  the supplement belongs to it (`adr/0007`, `adr/0008`).

Its points that repeat part B are answered there: the forward references (R10 = B4, R14 = B9), the
coupling repetitions (A§7.2.2 = B7), the symmetric boilerplate (A§7.2.5, first half = B2), the line
section (A§7.2.4 = B14), and Table 3 (R16 = B20, done). Three agents (two opus, one sonnet) and the
librarian checked the rest against r1, the sources and `adr/`.

Two summary sentences drop a hypothesis of their statement (R2, and R3 in part). `WRITING.md` says
"summaries drop hypotheses" and requires the summaries to be compared with their statements before a
freeze. So these are fixed before r2, whatever else waits.

| Item | Finding | Verdict | What was found | Answer |
|---|---|---|---|---|
| R1, A§2.1 | "The finite masks of the classical pyramids are the octave steps of no family" omits positivity; Burt's mask at $a=0.6$ has a negative weight | partly | The sentence is in Contribution 1 (p. 3) and at pp. S8 and S34, not in the abstract, which says "law". It is true as printed, because every step is a probability measure. But its "So" points to Prop. 3.21, which covers only laws, and for a signed mask the reason is positivity. § 7.1 (p. 105) and Prop. S.33 say this. | **Accept** (batch 1): one clause each in Contribution 1 and at `supp-line.tex:33, 2055`, saying that a family's steps are probability laws, so a mask with a negative weight is outside it from the start. |
| R2, A§2.2 | "Up to the choice of the scale coordinate" is not what Thm. 5.19 proves | **confirmed** | The octave step $t\to qt$ presupposes the canonical gauge (Def. 3.6). Under it the remaining freedom is $\mathcal G_q$ (Lemma 3.5(3), Thm. 5.19(2)–(3)). The sentence is not false, but it misdescribes the class. The same phrase is in Contribution 3 (p. 3) and the § 5 lead (`05-matern.tex:24–25`). The discussion is already exact (p. 104). | **Accept, before r2** (batch 1): "up to a relabelling of the scales in $\mathcal G_q$", or "the scales labelled so that the dilation by $q$ maps $t$ to $qt$", in the abstract, Contribution 3 and the § 5 lead. |
| R3, A§2.3 | "A symmetric mask" should be "a symmetric probability mask" | partly | Definitions 4.4 and 6.3 say probability law. The abstract, Contributions 2 and 4, and the discussion do not. No counterexample exists, since both sides of the iff are false for a signed mask, but the scope is unstated where the reader meets it. | **Accept, before r2** (batch 1): "probability" or "nonnegative, of unit mass" in those four places. |
| R4, A§2.5 | "The paper's own numbered statements" is ambiguous | partly | § 2's 27 theorems are numbered restatements of cited facts. § 1.1 already opens with the reviewer's wording (`01-introduction.tex:231–232`). | **Accept** (batch 1): the abstract takes § 1.1's wording. |
| R5, A§2.4 | Contribution 4 does not say why the Lévy measure is nonzero | **confirmed** | p. 4 never says that a lattice law has no Gaussian part. The § 6 lead (p. 82), Lemma 3.7 and Prop. 6.4(1) do. | **Accept** (batch 1): one clause in Contribution 4. |
| R6, A§2.4 | Contribution 4 does not say the dilation is scalar | partly | § 7.1 and Open Problem 3 say it. Contribution 4 does not, although Crowley's turned lattice is named on the same page. | **Accept** (batch 1): one clause in Contribution 4. |
| R7, A§5.1 | Cite Karlin for Thm. 2.15 beside the author's own paper | partly; the reviewer's citation is wrong in part | The librarian read Karlin. PF holds by Ch. 7, Thm. 3.2(a) with (1.6), pp. 335 and 345, with $a_i=\pm1/\theta_i$ in pairs. The variation-diminishing property is Ch. 5, Thm. 3.1, p. 233. The reviewer's Thm. 5.1 is the converse. The local-extrema clause is not in Karlin; it needs the step to the derivative, with smoothness from p. 355. | **Accept, corrected** (batch 2, a cited-fact restatement and its ledger entry): Thm. 2.15 keeps the selection paper as its source as printed, and adds Karlin with those three anchors for the PF and sign-change clauses. § 1.1's sentence on the source of the ten facts follows (batch 1). |
| R8, A§6 | Cite Maejima and Sato 1999 in § 3.2 | **confirmed** | It is cited only in the supplement (`supp-line.tex:192–196`), and § 3.2 cites no source for the synthesis from one octave. The librarian read Thm. 7, p. 361: it builds the process from a family of laws over one period. | **Accept** (batch 1): one sentence in the lead of Lemma 3.9, worded "from a family of laws over one period", as the supplement words it. |
| R9, A§6 | Say that the binomial mask's limit, the cubic B-spline, is classical | partly; the reviewer's sources do not state it | Neither Cavaretta, Dahmen and Micchelli nor Unser, Aldroubi and Eden states it as a result. The nearest is Cavaretta Thm. 3.3, p. 48 (convergence for nonnegative masks), with p. 161 (the binomial mask's refinable function is the B-spline). Unser's binomial REDUCE filter tends to a Gaussian in $n$, which is a different limit. | **Accept, corrected** (batch 1): one sentence in the lead of Prop. 3.22, saying that the convergence is classical in stationary subdivision [Cavaretta, Thm. 3.3, p. 48, with p. 161], and that what the paper adds is the reading as a knot relation. |
| R11, A§4 | Numerical parameters missing | **confirmed** | The script fixes each parameter, and the text prints none of them: Table 1's window $\pm2^{15}$ with halving supports; the 4096-point ring on $[-2048,2048)$, with no recorded argmin; Figure 4's box $[-18,18]\times[-8,8]$, $900\times9600$ points, not square; Figure 5's series cut at $K=143$ ($p^K/K<10^{-16}$) on a box of side 287. The scripts are in the repository (Declarations), but `appendix-verification.tex:17–19` holds a release TODO on whether the export copies them. | **Accept** (batch 1): a clause in each caption or sentence, and the argmin printed by `sampled_gaussian_increments.py`. The release TODO stays with the release checklist. |
| R12, A§7.1.3 | Main-paper proofs depend on the supplement | the premise is wrong | The list is nearly complete: Prop. 4.5 cites S.1 and S.3; Thm. 5.4 cites S.35–S.37 and (S.7); Props. 5.8, 5.9 and 5.14 cite S.35 and S.34(2); Prop. 6.13 cites S.33. But the paper never claims to read without the supplement. The § 5 lead and `supp-intro.tex:11–14` say the opposite. The supplement is part of the article, under one DOI (`adr/0007`), and `adr/0008` rejected re-pointing these citations because the proofs follow the checked route. Two of the reviewer's "special case" claims are wrong: Thm. 5.4(5) cites S.35(4) and does not re-prove it, and S.35(3)'s derivative identity is not in Prop. 5.11(1). | **Decline**, by `adr/0007`–`0008`. **Accept** (batch 1): one sentence in the introduction's plan of the paper, saying that some proofs cite the supplement's statements on the line. |
| R13, A§3.1.3 | The density of $L_r$ has no continuous finite value at 0 | **confirmed** | The sentence at `05-matern.tex:1080–1081` (p. 69) is true but weaker than Prop. 5.11(3). It makes the failure look like a choice of representative. | **Accept** (batch 1): the sentence rewritten from Prop. 5.11(3), with the blueprint's parallel prose (`04-matern.tex:1535–1537`) kept in step. |
| R15, A§7.2 | Shorten to 45–55 pages | partly | The duplication is real but about 3–4 pages, not 57–67: B7's blocks, and Prop. 4.5 against § 6. Prop. 4.5 is not the $d=1$ case of 6.13, and "~10 pages" is about 3.5. The Viète proof is given twice, in 3.22(2) and 6.13, and only cited in S.38. The bump-function argument appears once (p. 60, 7 lines). | **Accept in part** (batch 2): B2, B7 and B14, plus Prop. 6.13 citing 3.22(2) for the limit. **Decline**: the 45–55-page target. The paper has no page limit (pass 4 is skipped), and the remaining length is content. |
| A§7.2.4, S4 | Condense supplement § S1 | already decided | `adr/0008` moved the line strata into the supplement as they are. | **Decline**, by `adr/0008`. |
| S1 | "The B-spline masks of odd length" groups two families | **confirmed** | Prop. 4.5(4) covers the binomial masks and the renormalized B-spline samples under one label (`04-line.tex:375–380`). | **Accept** (batch 2, shared): name the two families. |
| S2 | `\hat` against `\widehat` | **confirmed** | 6 uses of `\hat` against about 540 of `\widehat`, on two lines of `05-matern.tex` (1020, 1116), both shared. | **Accept** (batch 2). |
| S3, A§7.2.5 | Remove the "Every step is machine-checked …" footers | partly | 54 of 96 proofs carry one, none in § 5, all of them shared text. Each names the cited facts the proof uses. That is the one sentence inside a proof that `WRITING.md` § 3 allows, and it is what Table 4 is built from. | **Decline**, as the standard allows it. **Decision D4** is the author's, if a lighter convention is wanted. |

## Found while checking

- **§ 1.1 names the wrong table.** `01-introduction.tex:312–314` (p. 6) says Table 3 "maps the
  fifteen axioms to the ten admitted facts". That is Table 2. § 1.1 owns the trust base, so this is
  fixed first (batch 0).

## Decisions for the author

**All four are settled (2026-11-23).** D1 and D3 were done as proposed. On D2 and D4 the
author answered "Yes, as recommended". No text changes follow from either.

- **D1. The order of the work.** Batch 0 is done. Batch 1 is paper-side prose, captions, a figure
  and one script. Batch 2 changes shared proofs, adds two shared lemmas and one cited-fact anchor,
  through the blueprint and `linkage`. The proposal:
  - batch 1 first, with R2 and R3 as its first items, because they are summaries that drop a hypothesis;
  - batch 2 next, in one blueprint session;
  - freeze round 2 after both.

  **Settled:** done in this order, with batch 2b after batch 2.
- **D2. Descriptive names for the senses of "exact" (finding 4).** The reviewer proposes:
  - "hemigroup-exact" for (iii);
  - "subsampling-closed" for (ii);
  - "sample-commuting" for (i), which must be widened to cover Definition 6.2(1).

  The names touch the shared Definition 6.2 and about twelve uses. The alternative is the gloss
  alone.

  **Settled: no names.** The glosses stay: the introduction's list from batch 1 and the list in
  § 4.2. The naming part of finding 4 is declined, and Definitions 6.1–6.2 stay where they are.
- **D3. A symbol table (finding 17)** in place of the extended notation paragraph.
  **Settled: yes.** Batch 1 added a table of the overloaded symbols in § 2.1.5.
- **D4. The proof footers (A, S3).** The standard allows them, and they are kept. The author may
  prefer a lighter form, for example one sentence per section, with Table 4 carrying the rest. That
  would be 54 edits to shared text.

  **Settled: the footers stay as they are.** S3 is declined.

## Batches

- **Batch 0** (paper-side, **done** with this plan): the § 1.1 table reference, and Table 3's
  placement (`[!htbp]` and a `\clearpage` before Table 4, so the order is Tables 2, 3, 4, then the
  References).
- **Batch 1** (paper-side prose, captions, a figure, one script):
  - first, the summaries: part A's R2, R3, R1, R4, R5 and R6;
  - part A's R7 (§ 1.1's sentence), R8, R9, R11, R12 (one sentence) and R13;
  - part B's 1 (§ 1.1 inventory), 2 (the reading of (2.2)), 3, 4 (gloss), 5, 6, 9 (gloss, caption), 10 (lead), 11, 12, 13, 15, 16 (convention), 17 (notation), 19, 20 (paper-side copies);
  - then a blind register review of the new prose (`PROCESS.md` § 8), and the summaries compared
    with their statements once more.

  **Batch 1's state (2026-11-23).**
  - **Done:** all of the above but two items, with D3 taken as the author's yes (a table of the
    overloaded symbols in § 2.1.5).
  - **Kept as they are, after reading them:**
    - B1: every sentence of § 1.1 that repeats Appendix A states an assumption of the development
      (the inherited axioms, the core declaring none, the facts not proved). The standard keeps such
      a sentence in § 1.1 when in doubt.
    - B20's paper-side copies (`03-pyramid.tex:413–418`, `04-line.tex:271, 570`): these are leads,
      where naming the source with its page is the point. Only the copies inside proofs go to batch 2.
    - R7's sentence in § 1.1 moves to batch 2, with Thm. 2.15's anchors.
  - **Figure 5:** redrawn with readable labels and the atom supports in the titles. The ratio
    annotation moved under the middle panel.
  - **The sampled-Gaussian script:** now prints the site of the least coefficient.
- **Batch 2** (blueprint, then re-transcription, `linkage check`):
  - the symmetric Lévy–Khintchine lemma (2), and the four derivations citing it;
  - the split-coupling isotropy clause in 3.19(2), and 5.19(1) and 4.5(2) citing it (7, 14);
  - the § 6 telescoping lemma (7);
  - 6.4(3) citing 4.5(4) (7);
  - paragraph breaks in 5.15(3) and 5.4(1) (18);
  - single citations in proofs (20);
  - from part A: Karlin's anchors in Thm. 2.15 and its ledger entry (R7); 6.13 citing 3.22(2) for
    the Viète limit (R15); the two families named in 4.5(4) (S1); `\widehat` (S2).

  **Batch 2's state (2026-11-23).**
  - **Done:**
    - the isotropy clause for the split coupling in 3.19(2), bound to
      `ladder_knot_kernel_2_split_rot`, with 5.19(1) and 4.5(2) citing 3.19(2);
    - 6.13 citing 3.22(2) and 6.4(3) citing 4.5(4), each as its Lean proof does;
    - the paragraph breaks in 5.15(3) and 5.4(1);
    - 16 double citations inside proofs reduced to the Section 2 number;
    - Karlin's anchors beside Thm. 2.15, in its lead and in § 1.1 (R7), with the theorem itself
      unchanged;
    - the two families named in 4.5(4) (S1);
    - `\widehat` (S2).
  - **Left for batch 2b:**
    - the symmetric Lévy–Khintchine lemma (B2), with the four derivations citing it;
    - the § 6 telescoping lemma (B7), with 6.4(1) and 6.6(1) citing it.

    Both add numbered statements, which renumbers the paper from § 3 on, and both need a Lean run
    for the axiom guard and Table 4. D2 (names for the senses of "exact") was with the author then;
    it is now settled, with no names.

  **Batch 2b's state (2026-11-23): done.** Numbers here are r2's; the rest of this plan uses r1's.
  - **The symmetric Lévy–Khintchine lemma (B2)** is Lemma 3.4 (`lem:symmetric-levy-khintchine`), in
    § 3.1 before the structure lemma, so every citation of it points backward. It states the
    equivalence, the uniqueness of $(A, \nu)$ and the triplet $(2A, \nu, 0)$. The four derivations
    cite it: Lemma 3.5 (was 3.4), Prop. 5.16(3), Prop. 6.5 (was 6.4) and Prop. 6.7 "Data" (was 6.6).
  - **The § 6 telescoping lemma (B7)** is Lemma 6.4 (`lem:knot-data`), before Prop. 6.5. It gives the
    product formula, the symmetry and the data of the knot kernel for a family carrying the ladder
    of a symmetric mask, the family not assumed symmetric. Prop. 6.5(1) and (3), and (a) implies (b)
    of Prop. 6.7(1), cite it.
  - **Lean.** `linkage` reads only the first segment of a dotted declaration name, so
    `SymLevyData.hasTriplet` and the `CarriesLatticeLadder.*` names cannot be bound, and `knot_data`
    passed only by matching an unrelated theorem of the line appendix. Each lemma is therefore bound
    to one declaration that assembles the ones its citing proofs call:
    `symmetric_levy_khintchine` (`FamilyStructure.lean`, with `map_neg_eq_of_charFun_im` moved
    there unchanged) and `knot_kernel_data` (`GridKnot.lean`). Both are in the axiom guard. Both
    roots built on the VM, the guard passed, and Table 4 was regenerated by its script there.
  - **Renumbering:** § 3 from 3.4 and § 6 from 6.4 shift by one; the full list is in `CHANGELOG.md`.
  - **D2 and D4** are settled with no text change (see "Decisions for the author"). Nothing else
    stands before the freeze `pyramids-review-r2`.

  The Lean bindings exist for the new lemmas. Where a proof is changed to cite an earlier result
  (4.5(2) to 3.19(2), 5.19(1) to 3.19(2)), it is because the Lean proof already calls that result.
  The print moves onto the checked route. `adr/0008`'s objection was to moving off it. Both roots
  build.

After batches 1–2, a new freeze (`pyramids-review-r2`), as § 9 requires for any change after a
freeze.

**The freeze's state (2026-11-23).** The build from `main` after batch 2b has every gate green.
It had one overfull box (12.8pt) that build r1 did not have. Batch 2's paragraph break at "The
input" in the proof of Prop. 5.15(3) put an unbreakable inline formula at the start of that
paragraph. The formula is now displayed, in the blueprint and the paper at once. The prompt is
`reviews/PROMPT-round2.md`. The tag goes on the merge of the freeze pull request.
