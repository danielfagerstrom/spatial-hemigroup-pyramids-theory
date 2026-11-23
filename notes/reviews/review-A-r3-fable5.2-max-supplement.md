# Referee report, Part A (content): the supplement in detail, the paper for consistency with it

**Manuscript.** *Spatial scale space from hemigroup axioms: the theory of image pyramids* (119 pages) and its supplement (46 pages), third round.

**Brief of this report.** The supplement, S-pages 1 to 46, statement by statement and proof by proof; the paper's abstract and Section 1 for what they say the supplement carries; the paper's Sections 2 to 4 where the supplement cites them or they cite the supplement; the passages of Sections 5 to 7 and Appendix A that cite the supplement. Items 3, 4, 6 and 7 are answered for the supplement, items 1 and 8 give the assessment of the supplement. Supplement pages are written S1 to S46, paper pages p. 1 to p. 119.

---

## 0. What was read, what was recomputed, what could not be checked

- **Read.** Only the three files. The supplement in full, every proof line by line. The paper pp. 1–58 closely; pp. 59–119 for every place that cites the supplement or is cited by it (Theorem 5.4, Propositions 5.8, 5.9, 5.14, Theorem 5.19, Proposition 6.15, Section 7), and Appendix A in full.
- **Recomputed by hand.** Every displayed identity and constant of the supplement that I list in Section 3.2; two entries of Table 1 of the paper; the two moments and the least coefficient of the sampled-Gaussian argument (Section 4 below).
- **Not checkable under the conditions of this review.** (a) The Lean development: it is not in the files, and p. 117 says the repository, tag and DOI do not exist yet. (b) The page anchors of the third-party sources (Sato, Karlin, Kallenberg, Maejima–Sato, Lindeberg 2016, Burt, Mallat); where I compare with a source I do so from memory and say so. (c) The author's earlier modules, cited as Zenodo preprints at version 0.1 (S45).

---

## 1. Overall assessment and recommendation

**Recommendation: major revision.**

For the supplement the reason is not the mathematics. I found **no false numbered statement** in S.1–S.40, and no proof with a gap that I could not close in a line; the slips are local (Section 3.3). The reasons are four.

1. **Positioning.** Section S1 and Sections S2.1–S2.2 (about half of the supplement) restate, for symmetric laws on the line and in new coordinates, the known theory of additive processes in law and of selfsimilar and semi-selfsimilar additive processes. The attribution is one sentence (S10). Details in Section 6.
2. **The one new principle is weaker than its summaries say.** The phase entropy (S2.3) selects by definition where it selects (Theorem S.26), is minus infinity on every grid pyramid (Proposition S.29(3)), is identically zero on a Gaussian ladder, is not invariant under the residual gauge group, and its quantitative theorems (Proposition S.29(1), Theorem S.30) exclude the Matérn ladder itself. The summaries on S8 and S23, and the paper on p. 5 and p. 57, say more than this.
3. **Structure.** A main theorem of the paper (Theorem 5.4, clauses 1, 3, 4, 5) and four propositions rest on supplement statements S.34–S.37, while S1 duplicates Section 3 at d = 1. The split between paper and supplement is not the split between what is needed and what is optional.
4. **Trust-base wording.** Twenty-seven of the supplement's proofs end with the sentence "Every step is machine-checked" (the supplement's own wording), which by the paper's Section 1.1 (pp. 5–6) does not refer to the printed steps. For at least five statements the dependencies reported in Table 4 show that the formal counterpart is a conditional statement of a different shape from the printed one.

None of the required changes needs new mathematics. Several need a different account of what is new.

---

## 2. The headline claims against what is proved, as they concern the supplement

| Claim | Where | Carried by | Verdict |
|---|---|---|---|
| The supplement has an entropy that selects the fully covariant member when the ladder has one and no Gaussian part | p. 5 | Theorem S.26(3) | **Wrong as worded.** The orbit has infinitely many fully covariant members (S38 says so: every relabelling in the gauge group that fixes the knots is one). What is selected is the similarity member, the one labelled so that the dilation by λ maps scale t to λt. |
| The supplement measures the freedom between the knots of a grid pyramid | p. 57 (pointer to S2.3); p. 49 says S2.3 compares the families | Proposition S.29(3) | **Wrong in substance.** On the ladder of every grid pyramid the phase entropy is minus infinity at every member. It measures nothing there. Only the appearance entropy (Proposition S.32) distinguishes a member, and neither page says so. |
| On the line a family is also selected by its phase entropy; in R^d Theorem 5.19 takes its place | p. 66 | Theorem S.26 | **Scope wrong.** The entropy compares the members of one ladder. It never selects a ladder. Theorem 5.19(2) selects the ladder and the interpolation, up to the gauge. The two are different kinds of statement, and Theorem 5.19 also holds at d = 1. |
| The phase entropy picks one member on a strictly larger class of ladders | S8, S23 | Theorem S.30, Proposition S.31 | **Misleading.** The class of Theorem S.30 requires a finite step measure; the class of Theorem S.26(3) does not. They are incomparable. The Matérn ladder has step measure 2e^(−x/c)dx/x, of infinite mass, so it lies in the first class and outside the second. S31 states the comparison correctly (among ladders with a finite step); S8 and S23 do not. |
| The Matérn pyramid creates no extrema from one level to the next | S8 | Proposition S.37 | **Qualification missing.** True on the line, as a count of sign changes of the record minus a level and of its derivative, for an input that is the primitive of an integrable function. S42 states the sense; the summary does not. |
| The finite masks of the classical pyramids that are probability laws are steps of no family | S8, S35; abstract for Proposition 3.22 | Proposition S.33 via Proposition 3.22 | **Holds.** It needs the cascade and continuity only, as the abstract says. It is a two-line corollary of the unbounded support of an infinitely divisible law and should be presented as such. |
| The rescaled equivalent weights of the binomial pyramid tend to the cubic B-spline, not to a Gaussian | S35, S41 | Proposition S.38(3) | **Holds, and is classical** (the refinable function of the mask). The paper attributes it (p. 41); the supplement does not. |
| Every statement of the supplement is machine-checked under the trust base of Section 1.1 | S1; abstract | Appendix A | **Cannot be verified by a referee**, and holds only with the gloss of pp. 5–6. See Section 5. |
| Machine-checked in all but one step and one proposition, from ten cited facts taken as axioms | abstract | Section 1.1, Table 2 | **Consistent as a count**: twelve axioms for eight facts of Sato, two for Theorem 2.15, one for Theorem 2.32; one step of Proposition 4.5(4), Proposition 6.6. The abstract's last sentence states the three further exceptions. |

---

## 3. Mathematical correctness

### 3.1 Outcome

No numbered statement of the supplement is false as stated. Every proof was followed to the end. Sections 3.3 and 3.4 list what is wrong locally and what is correct but narrower than the surrounding text suggests.

### 3.2 Verification log

| Statement | Pages | What was checked | Result |
|---|---|---|---|
| Lemma S.1 | S1–S2 | The triplet (2a, half the two-sided copy of the folded measure, 0) gives the exponent; the image under dilation; the order clause through sigma-finiteness | correct |
| Lemma S.2 | S2 | Closed subgroups of the positive reals; reduction to Lemma 3.6(2), whose proof (pp. 23–24) I also followed | correct |
| Lemma S.3 | S2–S3 | Both equivalences; the residual is the contraction by 1/q of the octave step, which matches Sato's convention for the span | correct |
| Theorem S.4 | S3–S4 | (1) both directions with continuity and nondegeneracy; (3) the substitution v = tx, the bound max(1, t²), the transport of the bijections through the gauge | correct |
| Proposition S.5 | S5–S6 | Generating function of the modified Bessel functions; failure of the criterion of Theorem 2.22 on the sphere of radius h | correct |
| Proposition S.6 | S6–S7 | Lévy integrability; monotonicity across octaves; the strict atom; continuity on octaves and at 0; covariance | correct |
| Theorem S.7, Proposition S.8 | S7–S8 | Through Proposition 3.19, whose proof (p. 34) is correct | correct |
| Lemma S.9, Theorems S.10, S.11 | S9–S11 | Group identities; the bijection of S.10 (its condition (1) follows from (2), (3) and membership of the first exponent; harmless redundancy); injectivity of r ↦ F(r·) | correct |
| Lemma S.12 | S12 | The Taylor bound gives 3(1 − cos v) ≥ (33/24)v² on [−1, 1]; the integral is 2 − sin(2v)/v ≥ 1 off it | correct |
| Theorem S.13 | S13–S14 | The construction of the measure from rational-indexed densities; uniqueness on a pi-system; (i)–(iv) in both directions | correct |
| Lemma S.14, Theorem S.15 | S14–S17 | The two-sided comparison of f(x) = Σ_{m≥1} min(1, x²q^(−2m)) with x² ∧ (1 + log₊x), with the constants 1/ℓ + q²/(q²−1), q² and 1 + 2ℓ; extremality; the failure of continuity at ω = π/(rθ) | correct |
| Proposition S.16 | S17–S19 | (a)⇔(b)⇔(c); the choice λ = q^(1/(2j)) kills the j-th coefficient; the profile; ½Θ ≤ g ≤ Θ; the circle average (S.5) | correct |
| Proposition S.17 | S19–S21 | Existence, uniqueness, extreme rays; the product (1 − ℓ + ℓ²/2)(1 + ℓ + ℓ²/2 + ℓ³/6) = 1 + ℓ³/6 + ℓ⁴/12 + ℓ⁵/12; the bound of clause (2) | correct; index slip (3.3) |
| Lemmas S.18, S.20, S.21 | S21–S22 | Telescoping; (q² − 1)a(1) = 0 | correct |
| Lemmas S.22, S.23, Proposition S.25 | S23–S25 | Standard measurability and disintegration; the rotation of the fibres under a change of unit | correct |
| Theorem S.26 | S25–S26 | (4): the alternative Gaussian measure has mass a₀(1) on (0, 1], and the difference at t₀ = (1+q)/2 is −a₀(1)(q−1)²/4 | correct |
| Lemmas S.27, S.28, Proposition S.29 | S26–S29 | Density of the smearing; injectivity through tails; the step formula; the compensation identity; clauses (2), (3) | correct |
| Theorem S.30, Proposition S.31 | S29–S32 | The two hypotheses are consistent only with k(0+) = \|μ\|/ℓ; the candidate is a member; uniqueness through Lemma S.28; the value; ∫cos(2π log_q θ)η(dθ) = 0 | correct |
| Proposition S.32 | S32–S34 | (4): G(x/t) = G(x) + (log_q t)M(x) forces M constant, then M = 0 | correct |
| Proposition S.33 | S35 | Burt's two constraints give 4b = 1; the zeros of the transforms | correct |
| Lemma S.34 | S35–S36 | The integral of clause (1) by differentiation in ω; complete monotonicity; the proof gives 2Σϑ⁻², the statement 4Σϑ⁻² | correct |
| Theorem S.35 | S36–S38 | Octave identity; generator; the constant 2(1 + q²/(q²−1)); the Riemann-sum sandwich; the dilogarithm form; no weak limit of the kernels | correct |
| Theorem S.36 | S39 | The zero q/(cs) of N_s is a zero of N_t exactly when t/s is a power of q | correct |
| Proposition S.37 | S40 | The rearrangement by multiplicities; the step exponent | correct |
| Proposition S.38 | S41–S42 | Transform cos⁴(hω/2); κ₂ = h², κ₄ = −h⁴/2; variance (4ⁿ−1)h²/3; kurtosis −(3/10)(4ⁿ+1)/(4ⁿ−1), which is −1/2 at n = 1 as it must be; the B-spline cumulants h²/3 and −h⁴/30; the sign-change lemma | correct |
| Propositions S.39, S.40 | S42–S45 | Moduli of Schoenberg's product; the remainder ℓτ²ω²q^(−2N)/(2(q²−1)); the lattice clause | correct |

### 3.3 What is wrong, locally

1. **S20, existence part of Proposition S.17.** The displayed identity sums over i < n. It must be 0 ≤ i < n; read as printed, over all integers below n, the sum includes negative i and the identity is false.
2. **S1, second paragraph.** The list of what the paper's proofs read from the supplement is inaccurate. Lemma S.9 is cited only in the prose of Section 4.1 (pp. 44–45), in no proof that I found. Lemma S.3 is read twice by the proof of Proposition 4.5 (pp. 47–48) and is not listed. Lemma S.34 is read by the proof of Proposition 5.9 (p. 70) and is not among the statements after Theorem S.35. Proposition S.33 is cited in the proof of Proposition 6.15 (p. 105), and S1 names Sections 4 and 5 only, where p. 5 says Sections 4 to 6.
3. **S43.** The supplement refers to the knot relation of Definition 2.4. Definition 2.4 (p. 9) does not define that term; it is introduced on p. 25 and again on pp. 40–41.
4. **S43.** The phrase about the grid pyramid of sampled Matérn levels uses a defined term (Definition 4.4, p. 46: the ladder of a mask) for something else. Proposition 4.7(2) is about the grid pyramid of the sampled Laplace mask, whose computed arrays are compared with samples of Matérn steps.
5. **Paper p. 39.** The pointer for the coordinates of displacement and scale is to Section S2.1. They are in Section S2.2 (Theorem S.13, Figure 1 on S12).
6. **Paper p. 15, table of symbols.** The bare letter μ is said to be a step measure in Section S2.2. It is so used throughout S2.3 as well (Propositions S.29, S.31, S.32, Theorem S.30).
7. **Lemma S.34, S36.** The stated bound has the constant 4, the proof gives 2 and then weakens it without reason. Not an error, but the statement is not what the proof shows.

### 3.4 Correct statements whose reach is narrower than the text around them

1. **Theorem S.26 selects by definition.** The entropy is minus a relative entropy against Haar measure, so it vanishes exactly at Haar fibres, and Haar fibres are full covariance of the jump part by Proposition S.16(1). Theorem S.26(3) is therefore Proposition S.16(1) restated; any strictly convex divergence would give the same theorem. The summaries present it as a variational principle that returns the similarity member. It is a characterization, and should be called one.
2. **The entropy is not invariant under the gauge group.** S25 says that a relabelling other than a dilation is not covered. The consequence is not drawn: a relabelling of the similarity member by an element of the gauge group that fixes the knots is again a member, is fully covariant, is the same family in the sense of the covariance axiom (which allows any bijections), and has strictly negative entropy when there is a jump part (the map r ↦ T_r of a nonzero Lévy measure is injective, so Haar fibres force the relabelling to be linear). So the principle selects a labelling of the scales as much as a family. The headline theorem of the paper is stated up to exactly this group.
3. **The entropy is silent on the Gaussian ladder.** There the orbit consists of the relabellings of the Gaussian family and the entropy is zero on all of it. Theorem S.26(4) contains this; the text never says that the central example of scale space is the case where the principle says nothing.
4. **Proposition S.29(1) and Theorem S.30 exclude the Matérn ladder.** Both assume a step measure of finite positive mass. A similarity ladder with profile k has step mass ℓ·k(0+); the Matérn profile is unbounded at 0. For ladders with an infinite step measure and no similarity member the supplement proves nothing in either direction, unless the step has a singular part. This should be listed with the open question on S32.
5. **Theorem S.30 is an equivalence.** Under hypothesis (1), the bound (S.6) is attained if and only if hypothesis (2) holds: the uniqueness part of the proof (S30–S31) shows that a member attaining the bound has a step equal to the density times the smearing of its ratio marginal, which is a covariant step. Stating the theorem one way leaves the reader unsure what happens when (2) fails.
6. **Proposition S.37 is also an equivalence.** If every octave step of a similarity family is a Pólya frequency law, then the step exponent G is a Gaussian term plus Laplace atoms, and F = Σ_{m≥1} G(q^(−m)·) has the stated form with multiplicities nondecreasing along q. The hypothesis is necessary, not only sufficient.
7. **Proposition S.38(4) is proved for the mask that has no family.** The same count holds for the sampled Laplace mask of the exact geometric pyramid (Proposition 4.5(4)): its generating function is a constant over (1 − az)(1 − a/z), a Pólya frequency sequence, so convolution is variation-diminishing and decimation takes a subsequence. The supplement proves non-creation on the lattice for the inexact pyramid and is silent on the exact one.

### 3.5 The statements of the paper that the supplement uses

I followed the proofs of Theorems 2.3 and 2.22, Lemmas 3.3–3.6 and 3.8–3.10, Theorem 3.12, Propositions 3.13, 3.14, 3.19, 3.20(1)–(2), 3.22, 3.23, Lemma 4.2, Proposition 4.5 (including the one step shown in print only: the binomial masks 4^(−k)C(2k, k+n) and the sampled B-splines of degree at least 2 are symmetric laws with finitely many atoms, not point masses), Proposition 4.6 and Proposition 4.7(1), (3). I found no error. For Proposition 4.7(2) I checked the two ratios at level 2 (Section 4).

The cited facts that the supplement reads are Theorems 2.15, 2.17, 2.19, 2.20, 2.21, 2.24, 2.25 and 2.32. As far as I can compare from memory with Sato (Theorems 8.1 and 9.3, Propositions 11.10 and 15.5, Corollaries 24.4 and 24.6) and Karlin (Chapter 7, Schoenberg's representation; Chapter 5, variation diminution), each is stated at or below its source's strength, and each use in the supplement meets the hypotheses: the image of a law under an injective linear map (S.5, S.29); a symmetric residual for Theorem 2.21 (S.17(3)); an integrable density for Theorem 2.32 (S.36, S.39). One point deserves a sentence in the paper: Theorem 2.15 is used for bounded inputs that are not integrable (the record minus a level, S.37(2)), with the count taken in the essential sense; Karlin's theorem counts pointwise for bounded measurable functions. The passage from one to the other is routine and is inside an admitted axiom, so it should be stated.

### 3.6 Incidental checks outside the brief

Reported because I did them, not as a review of these sections. Proposition 6.6 (print only, pp. 93–95): the argument is complete; the Gaussian part vanishes because M^(−n) tends to 0, the Lévy measure of each kernel is nonzero and carried by the countable union of the images of the lattice, and a rotation-invariant Lévy measure cannot have an atom off the origin in d ≥ 2. Proposition 5.18(3) (pp. 81–82): Steps 1 to 3 are correct, including the polarization that gives the quadratic form. Proposition 5.21 (pp. 85–86) and the first half of Proposition 5.15(1) (p. 75, one local maximum for every a > 1) are correct.

---

## 4. The numerical examples

**The supplement has none.** Its numbers are closed forms, all recomputed in Section 3.2. Figure 1 (S12) is a schematic and is consistent with Theorems S.13 and S.15: the four dots are one orbit, one of them in the shaded octave, and the solid line y = t has three of them on its left.

**One inconsistency with the paper.** S43 says that how much a level aliases is measured in further work. The paper measures the level error at q = 2 in Table 1 (p. 55) and explains it as aliases meeting across levels (p. 55). The supplement should point there and say what remains.

**Section 4 of the paper, recomputed.**

- *Table 1.* From the two ratios in the proof of Proposition 4.7(2) (p. 54), at level 2 and q = 2 the computed array is proportional to ρ₁^|m| − ρ₂^|m|/(2 cosh x) and the sampled step to ρ₁^|m| − ρ₂^|m|/2, with x = h/(ct), ρ₁ = e^(−2x), ρ₂ = e^(−4x). Normalizing and taking half the ℓ¹ distance I get 6.25 % at x = 1 (difference 0.0625 at the centre, −0.0264 at ±1, −0.0042 at ±2) and 0.0567 % at x = 0.1. Table 1 prints 6.3 % and 0.057 %, and the caption of Figure 3 gives the centre difference as between 0.062 and 0.068. Both agree. At level 2 the entry is thus a closed form; printing it would let a reader check the script without running it.
- *The sampled Gaussians at 0.5 and 0.6 (p. 56).* With sums cut at |k| ≤ 5 I get second and fourth moments 0.21501 and 0.22135 at 0.5, and 0.35162 and 0.41357 at 0.6; hence 0.13661 and 0.01598 for the hypothetical step. The paper prints 0.1366 and 0.0160. The fourth moment is below the second by a factor of eight, so the contradiction on the integers does not depend on the last digits, and the tail at |k| = 6 is below 10⁻¹⁸ as stated. The argument is correct. (That the step lives on the integers needs no atom at 0: both the sum and one summand do.)
- *The least coefficient −0.011 at ±2 (p. 55).* Deconvolving on the integers with the inverse of the three-point part of the narrower kernel, and correcting for its weight at ±2, I get −0.0109.

**Design and reach.** The checks are well chosen: the first-level agreement is a control, three window sizes agree, and the text states that no bound is proved and that the signs for the other three Gaussian pairs are computed on a periodic grid. Nothing is concluded that the computation cannot show. Reproduction from the manuscript is possible for the cases above; the scripts themselves are in a repository that does not exist yet (p. 117).

---

## 5. The trust base, as it concerns the supplement

1. **The closing sentence says something other than what it means.** By pp. 5–6 it means that a formal counterpart of the statement was checked, and it does not certify the printed argument. A reader of the supplement meets it twenty-seven times with no such gloss; S1 has only a pointer to Section 1.1. It should be replaced by a sentence that says what is certified. Eleven proofs (S.7, S.8, S.11, S.17, S.18, S.34–S.39) carry no closing sentence at all, with no stated reason.
2. **The formal counterparts are in places conditional statements.** Table 4 (p. 116) reports no cited fact for Theorem S.15, Lemma S.23 and Proposition S.25, and only Theorem 2.17 for Proposition S.16. As printed, each of these is about a covariant family with its pair of measures, and the existence of that pair is Theorem S.13, which needs Theorems 2.17 and 2.19. Likewise Theorem S.36 is printed as a statement about the Matérn pyramid of Theorem S.35 (Theorems 2.17, 2.19) and is reported with Theorems 2.15 and 2.32 only. The reports are consistent only if the formal statements take the pair, or the laws, as hypotheses. That is legitimate, but it is exactly the match between print and formal statement that is not machine-checked, and the reader is told nothing. Clause (4) of Theorem S.15 (the families are the pairs with the three listed properties) is the clearest case: in print it is a statement about families.
3. **The printed proof and the checked proof differ.** Lemma S.22 (S23) says so openly: the print reads a theorem of Kallenberg, the formal proof a construction of Mathlib. This is the honest form; it also shows that the closing sentence cannot be read as a statement about the printed steps.
4. **Table 4 agrees with the supplement.** I compared every closing sentence of the supplement that names cited facts with the rows S1 and S2 of Table 4. They agree in every case, provided a sentence saying that the cited facts enter through named lemmas only is read as an upper bound (Lemma S.3 names Lemma 3.5, which reads Theorem 2.20; Table 4 gives Theorems 2.17 and 2.19 for S.3).
5. **A question I could not settle.** Table 4 (p. 115) lists the classification on the line (Theorem 2.5) and in R^d (Theorem 2.8) under Theorem 2.17 alone. As printed, both need the infinite divisibility of the kernels, which the paper itself derives from Khintchine's theorem (Lemma 3.3, Theorem 2.19) or from Theorem 2.21. Section 1.1 says that the imported core takes cited facts as hypotheses. Either the formal Theorem 2.5 keeps such a hypothesis, in which case the statement on p. 9 is wider than what is checked and p. 7 promises that Section 2 would say so, or infinite divisibility is reached another way. The formal statement of that declaration would settle it. Theorems S.4(3), S.11 and S.35 rest on Theorem 2.5.
6. **What a referee is asked to accept.** The comparison of formal and printed statements was done by AI agents only (pp. 6, 116), and the development is unreleased. For the supplement this means that the assurance offered beyond the printed proofs cannot be weighed at all at present. The printed proofs stand on their own, as Section 3 reports; the paper should not ask for more credit than that until the repository exists.

---

## 6. Novelty and relation to prior work

**What I take to be new in the supplement:** the phase entropy with Theorems S.26, S.30 and Propositions S.29, S.31; the appearance entropy (Proposition S.32); the circle-average identity (Proposition S.16(2)); the failure of the Pólya frequency property for increments off the powers of q (Theorem S.36) and the count along the ladder (Proposition S.37); Proposition S.39; the limits as q tends to 1 (Propositions S.17(2), S.40(4), Theorem S.35(4)). This is a modest list, and the first item is limited as Section 3.4 says.

**What is presented without the attribution it needs.** The comparisons below are from memory of the sources; the author should check each against the held copies.

1. **Stratum 1 is the theory of additive processes in law.** A family with the cascade and continuity is the system of increment laws of an additive process in law. That its laws are infinitely divisible is Sato's Theorem 9.1 with 9.7(i), proved there by the same null-array argument as Lemma 3.3 (p. 21). The description by nondecreasing, continuous triplets with its converse, which is Theorem S.4(1) (S3) and Theorem 3.12(1), is Sato's Theorem 9.8 for symmetric laws. The paper cites the neighbouring Theorem 9.3 and not these.
2. **Stratum 3 is the theory of selfsimilar additive processes.** That the laws at positive scales are exactly the selfdecomposable ones, and that every such law is realized, is Sato's Theorem 16.1 (after Sato 1991), up to a deterministic change of time, which is the gauge. The paper attributes the statement to the author's earlier modules only (p. 25); Theorem S.4(3) inherits this.
3. **Stratum 2 is the theory of semi-selfsimilar additive processes.** This is acknowledged in one sentence (S10, p. 26) for the annulus parametrization. The octave-phase structure of Theorem S.11 and the cylinder coordinates of Theorem S.15 are, as far as I recall, the passage in logarithmic time to an additive process with periodically stationary increments, treated by Maejima and Sato in 2003 (semi-Lévy processes). Convolution hemigroups with the scaling property of the canonical discrete gauge have also been studied under the name semistable hemigroups (Becker-Kern, J. Theoret. Probab., 2003, as I recall it). Neither is cited. If my recollection is right, the three nested strata are the known hierarchy additive, semi-selfsimilar additive, selfsimilar additive, restricted to symmetric laws.
4. **The surface measure is the jump intensity.** The measure of Theorem S.13 (S13) is the measure on time and displacement that Sato attaches to the system of Lévy measures of an additive process (Section 19, the intensity of the Poisson random measure of jumps), folded to positive displacements. Absence of mass on vertical lines is stochastic continuity. The proof on S13–S14 rebuilds it by hand.
5. **The q-Cin representation is the Maejima–Ueda representation.** In Proposition S.17(1) the mixing measure is the folded Lévy measure of the residual in Sato's sense, and the representation is the product formula that the paper itself attributes to Maejima and Ueda for Proposition 3.20(1) (p. 35). The supplement proves it four times (existence part of S.17, Lemmas S.18(1), S.20(1), the knot-measure paragraph of Theorem S.30) and cites it nowhere. Proposition S.40(2) is the same series read as a sum of independent rescaled compound Poisson variables.
6. **The Matérn pyramid on the line is in the earlier cone module.** Theorem 2.14 (p. 13) states the product formula, the uniqueness and the admissibility, with the Matérn pyramid as its named case. Theorem S.35(1)–(2) restates this with no reference to it. The uniqueness of the solution of the octave identity is printed four times (Theorem 2.14, Proposition 3.20(4)(b), Theorems S.35(2) and 5.4(2)).
7. **Lindeberg's time-causal limit kernel.** S39 treats it as a twin in time. Two facts belong in the positioning: the knot kernel of the line's Matérn pyramid is that kernel convolved with its reflection (the paper says so on p. 66, the supplement does not), and that kernel is, to my knowledge, the published example of a scale-space kernel covariant under the powers of one ratio only. The axiom of this paper has that precedent.
8. **Proposition S.38.** Clause (3) is the classical limit of the binomial subdivision scheme; the paper cites Cavaretta, Dahmen and Micchelli for it on p. 41, the supplement cites nothing on S35 or S41. Clause (4) is the variation-diminishing property of two-point averages, due to Schoenberg and the basis of Lindeberg's 1990 classification of discrete scale-space kernels; reference [9] of the supplement is cited two paragraphs later for something else.

**Against the list of the brief.** Burt and Burt–Adelson: the constraints and the equivalent weights are reported correctly on S35, with the equal-contribution constraint read correctly as equal mass on the cosets; I cannot check the pages. Meer, Baugher and Rosenfeld: one sentence on S43, fair. Lindeberg 1990: placed correctly in stratum 1 (Proposition S.5); see items 7 and 8 and Section 3.4(7). Maejima–Naito and Sato Section 15: Proposition S.17(3) is immediate from the criterion of Theorem 2.22 and is presented as such. Maejima–Sato 1999: cited once. Maejima–Ueda 2009: not cited in the supplement (item 5). Hanke–Groetsch and Radmoser–Scherzer–Weickert: absent from the supplement; a pointer at Theorem S.35, whose line family is that iteration with geometric parameters, would suffice. Mallat: the remark on S43 is fair, and is the third statement of the same point (after p. 41 and Proposition 6.15). Whittle and Lindgren–Rue–Lindström: absent from the supplement, which uses the name Matérn from S34 on; on the line the octave step is the exponential-covariance kernel, and saying so once would help. Cavaretta–Dahmen–Micchelli: item 8.

---

## 7. Exposition and structure

**Where the paper needs the supplement.** Proposition 4.5 reads Lemmas S.1 and S.3 (pp. 47–48). Proposition 4.7(2) is stated in terms of Theorem S.35 (p. 52). Theorem 5.4 reads Theorem S.35 in clauses (1), (3), (4), (5), Theorem S.36 and Proposition S.37 in clause (3) (pp. 62–65). Propositions 5.8, 5.9 and 5.14 read Theorem S.35 and Lemma S.34 (pp. 69, 70, 74). So about six pages of the supplement (S35–S40) are part of the proof of a main theorem. They belong in the paper. Lemmas S.1 and S.3 are the paper's Lemmas 3.4, 3.5 and 3.9 at d = 1 and could be replaced by them in the proof of Proposition 4.5. Proposition S.33 is cited on p. 105 as an aside. Nothing else in the supplement is needed by a proof of the paper.

**Where the supplement leans on the earlier papers.** Theorems S.4(3), S.11 and S.35 rest on Theorem 2.5, restated in the paper. Beyond that, the narrative of S2.2 and S2.5 rests on the statement that the extreme rays of the fully covariant cone are the Gaussian ray and the Cin rays (S8, S19, S45), cited directly to the cone module and not restated in Section 2. The index of Section 2.1.4 (p. 12) says it lists what the paper and the supplement cite from the released modules; it omits this one, the generator of a Thorin exponent (S38) and the remark on the readings of non-creation (S39, S42). The frame families are named on S35 with a reference to the affine paper and no description.

**Where the argument is hard to follow.**

- S13–S14: the construction of the surface measure. A reader who knows that a nondecreasing, continuous system of Lévy measures defines a measure on the product does not need it; one who does not is not helped by a page and a half of rational-indexed densities. Cite or shorten.
- S23–S31: the chain S.22, S.23, S.27, S.28, S.29, S.30. The idea of Theorem S.30 (the bound is attained when every rotated fibre equals the folded step) is one paragraph; it is reached after seven pages of measurability lemmas.
- The same telescoping series is proved four times in the supplement and at least four more in the paper (Proposition 3.20(1), Proposition 4.5(2), Lemma 6.4, Theorem 5.19(1)).

**Definitions before use, names, notation.**

- The compound Poisson notation of (S.9) (S43) is used on S16 and S17.
- The modulation spectrum is defined in Proposition S.16(3) (S17) and used in one remark (S26). The modulation orbit (Definition S.19) is, by the text's own account (S21–S22), not an orbit.
- A knot exponent (Definition S.19) is a nonzero element of the cone of Proposition S.17. The two are never connected.
- One family has two names: the uniform coupling in the paper (pp. 36, 47, 97) and the log-uniform member in the supplement (S33). Neither text mentions the other name, and Proposition S.32, which characterizes it, is not cited where the paper introduces it.
- Two different pyramids have nearly the same name: the geometric pyramid (Proposition 4.5(4), the sampled Laplace mask) and the geometric-jump pyramid (Proposition S.6, the family of Proposition 3.14 at d = 1).
- The octave exponent is θ in Proposition 3.14 and on p. 33, and ζ in Proposition S.6; in the supplement θ is the phase q^ζ in [1, q). The symbol of the generator is h_t in Theorem S.35(3) and in the proof of Theorem 5.4(4), and σ_t in Proposition 5.11.
- Theorem S.35(1) calls the octave steps single Matérn steps. In the paper's Section 2.1.5 the Matérn family and the Matérn pyramid have different octave steps, and the word alone does not say which.
- The bare letter μ is a step measure from Definition S.19 on, after being a law in Lemma S.1 and Proposition S.17. The warning is in a parenthesis on S22.

**Forward references that carry weight.** Proposition S.6(3) is proved by Proposition S.8(1) (harmless, no circle). Proposition S.29(3) depends on Definition 4.4 and Proposition 4.5(1) of the paper, whose proof depends on Lemmas S.1 and S.3 (no circle, but the reader must hold both documents open). Theorem S.35(4) points to Theorem 5.4(5), which is proved from Theorem S.35(4).

**What a journal version should lose.** Section S1 (S1–S8) is Section 3 at d = 1, statement for statement (the paper lists the pairs on p. 44); Lemma S.1 and a dictionary of one page would do. The hand construction in Theorem S.13, Lemma S.14 as a separate statement, the modulation spectrum, and the appearance entropy as a numbered proposition can go to remarks. Section S2.5 is about the cone of semi-selfdecomposable exponents, not about pyramids, and belongs with the cone module. With S35–S40 moved to the paper, the supplement would be about twenty pages.

---

## 8. Required changes and suggestions

### Required changes

1. **S3–S4, S10; paper pp. 21–28.** Say that a family is the system of increment laws of an additive process in law, and attribute Lemma 3.3 and Theorems S.4(1), 3.12(1) to Sato's Theorems 9.1, 9.7, 9.8, and Theorem S.4(3) to his Theorem 16.1. Reason: known theorems are stated and proved as the paper's own.
2. **S11–S19.** Attribute the surface measure to the jump-intensity measure of an additive process and the cylinder coordinates to the semi-selfsimilar literature (after checking the 2003 paper of Maejima and Sato and the work on semistable hemigroups), and state what S2.1–S2.2 add. Reason: the present account (S10) attributes one construction and leaves the rest looking new.
3. **S19–S22, S29–S30, S43–S44.** Attribute Proposition S.17(1), Lemmas S.18(1), S.20(1) and Proposition S.40(2) to the representation of Maejima and Ueda; say that the mixing measure of S.17 is the folded Lévy measure of the residual; state which measures occur (those integrating τ² ∧ (1 + log₊τ)). Reason: the paper attributes the same formula on p. 35 and the supplement does not, and the range of the parametrization is missing from the statement.
4. **S8, S23, S25, S29–S32.** Restate the reach of the phase entropy: incomparable classes for Theorems S.26 and S.30; finite step measure excludes the Matérn ladder; zero on Gaussian ladders; not invariant under the gauge group, with the relabelled similarity member as the example; the uncovered cases listed as open. Reason: the summaries claim more than Section S2.3 proves.
5. **Paper pp. 5, 49, 57, 66.** Correct the four descriptions of Section S2.3: similarity member in place of the fully covariant member; on a grid pyramid the phase entropy is minus infinity for every member; the entropy selects within a ladder and Theorem 5.19 among ladders. Reason: each sentence is contradicted by a statement of the supplement (S38, Proposition S.29(3), Definition S.19).
6. **S1 and all closing sentences; paper pp. 5–6, 115–116.** Replace the closing sentence by one that says a formal counterpart was checked, and say for Theorems S.15, S.36, Lemma S.23, Propositions S.16, S.25 that the counterpart takes the pair or the laws as hypotheses, or print the formal statements. Reason: the sentence reads as a claim about the printed proof, and Table 4 shows the counterparts are conditional.
7. **S1, S35–S40; paper pp. 47–48, 52, 62–65, 69–70, 74, 105.** Move Lemma S.34, Theorems S.35, S.36 and Proposition S.37 into the paper, or state in Theorem 5.4 that its clauses are proved from them; correct the list on S1 (Lemma S.3, Lemma S.34, Proposition S.33; Sections 4 to 6). Reason: a main theorem is proved from the supplement, and the supplement's own account of what is read is inaccurate.
8. **S36–S39; paper pp. 13, 57, 66.** State at Theorem S.35 that clauses (1)–(2) are the named case of Theorem 2.14, and that the knot kernel is the time-causal limit kernel convolved with its reflection, a kernel already covariant under one ratio in the literature. Reason: the theorem reads as the introduction of a new family.
9. **S35, S41–S42.** Attribute Proposition S.38(3) to subdivision theory, as p. 41 does, and S.38(4) to Schoenberg and to Lindeberg 1990. Reason: classical results are proved without attribution.
10. **S20, S43; paper pp. 15, 39.** Correct the slips of Section 3.3, items 1 and 3 to 6. Reason: one false display, three wrong pointers and one misused defined term.
11. **Paper p. 12; S19, S38, S39, S42.** Complete the index of Section 2.1.4 with the statements of the earlier modules that the supplement cites, and restate the one on the extreme rays of the fully covariant cone. Reason: the index claims to cover the supplement and does not, and that statement carries the narrative of S2.2 and S2.5.
12. **S8.** Qualify the summary on non-creation of extrema: on the line, as counts of sign changes, for inputs that are primitives of integrable functions. Reason: the body (S40, S42) has the qualifications and the headline does not.
13. **S6, S33, S36; paper pp. 30, 33, 36, 47, 71.** One name and one letter per object across the two documents: uniform coupling and log-uniform member; geometric and geometric-jump pyramid; θ and ζ; h_t and σ_t. Reason: the supplement is declared part of the paper (p. 5) and a reader cannot tell that these are the same objects, or that they are different ones.

### Suggestions

1. **S1–S8.** Reduce Section S1 to Lemma S.1 and a one-page dictionary. Reason: it repeats Section 3 at d = 1.
2. **S13–S15.** Replace the construction in the proof of Theorem S.13 by a citation or a short extension argument, and fold Lemma S.14 into the proof of Theorem S.15. Reason: length without insight.
3. **S29–S32.** State Theorem S.30 as an equivalence between hypothesis (2) and attainment of the bound, which its proof gives. Reason: it tells the reader what happens outside the hypothesis.
4. **S19, S22, S40.** Note that knot exponents are the nonzero elements of the cone of Proposition S.17, and that the hypothesis of Proposition S.37 is necessary. Reason: two definitions of one class, and a characterization stated as a sufficient condition.
5. **S41–S42.** Add the lattice count for the sampled Laplace mask. Reason: it is the mask of the exact pyramid, and the argument is the one already printed.
6. **S17, S32–S34, S43–S45.** Move the modulation spectrum and the appearance entropy to remarks and Section S2.5 to the cone module. Reason: none is used by a later statement.
7. **S19–S22, S30.** Prove the telescoping series once and cite Proposition 3.20(1). Reason: four proofs of one identity.
8. **S34.** Add a table of the three selections on the line (phase entropy, appearance entropy, the implicit-Euler principle of Theorem 5.19 at d = 1), with what each fixes: the ladder, the interpolation, the labelling. Note that one stage of the principle (Theorem 5.19(1)) with maximal phase entropy (Theorem S.26(3)) gives the Matérn pyramid in its similarity labelling. Reason: the comparison is now scattered over S34 and pp. 66, 82.
9. **S21–S22.** Rename the modulation orbit. Reason: the text says it is not an orbit.
10. **S35–S36.** State in Lemma S.34 the bound that the proof gives. Reason: an unexplained factor of two.
11. **S24–S25.** Add that the entropy for the span q^k is k times the entropy for q (the cylinder is covered k times, the fibre densities repeat). Reason: a family covariant under q is covariant under q^k, and the reader will ask whether the principle depends on the choice.
12. **S10, S23, S39, S42, S43.** Give the name of each third-party theorem beside its number and page (Kallenberg, Maejima–Sato, Karlin, Lindeberg, Mallat). Reason: numbers differ between editions, and a referee without the copies cannot place them.
13. **S4 and throughout.** Punctuate the two sentences on S4 that run a theorem number into the clause, and give every proof the same closing line or none. Reason: eleven proofs lack it for no visible reason.
