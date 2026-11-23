# Response plan: review round 3 of the theory paper

*The input is round 3 of `PROCESS.md` § 9, against the build frozen at the tag `pyramids-review-r3`
(`848ac64`; paper 119 pp., supplement 46 pp.). At the author's word the round was run by Claude
Fable 5.2 at its highest effort, as four blind agents, each given only part A of
`reviews/PROMPT-round3.md` and the two PDFs and told to open no other file. Each reviewed one block
in detail and the rest for consistency: `reviews/review-A-r3-fable5.2-max-{s1-3,s4-5,s6-7-appendix,supplement}.md`.
It is a same-vendor read, a weaker test of independence than rounds 1 and 2.*

*Every finding was checked against the r3 text, its LaTeX at the tag, the blueprint and the Lean
before it was sorted. Four opus agents did the checking, one per report, and recomputed the numbers
(mpmath, scipy). The reviewers had no sources, so every claim about a source was sent to the
librarian, who reads held copies. Item names are `<block>.<item>` with the report's own numbering
(R = required change, S = suggestion). Pages and statement numbers are r3's.*

## Summary

Each block recommends major revision, and each says the mathematics stands. The checks agree:
**no numbered statement is false and no printed proof has a gap.** Prop. 6.6, the one statement
proved in print only, was checked step by step by its reviewer and its verifier. Of the 53 required
changes and 68 suggestions, about a fifth repeat decisions of rounds 1 and 2. What is new is of five
kinds.

1. **One consequence the paper does not draw, which makes two sentences false.** For an integer q
   every exact mask has ŵ > 0 (Prop. 4.5(1), 6.8(1)). The kernel's transform is then constant along
   2πq^k/h, so no kernel μ_t, t > 0, of a family carrying an exact grid pyramid is absolutely
   continuous; by Kolmogorov's 0–1 law on the countable group hℤ[1/q] each is singular. pp. 35 and
   45 say without condition that "an implemented pyramid samples them on grids", which is false on
   the line for every exact grid pyramid. The same fact means no exact mask meets Burt and Adelson's
   equal-contribution condition (mass q^{-d} on each coset ⇔ ŵ = 0 at the alias frequencies). Two
   blocks found this independently.
2. **The isotropy obstruction rests on continuity in scale as much as on the lattice.** Two blocks
   construct a positive, symmetric, band-limited mask w on ℤ^d of infinite support with a
   rotation-invariant refinable law μ (D_qμ = μ * w). The verifier checked every step. w is not
   infinitely divisible, so no family continuous in scale carries it, and a family without (b) that
   jumps at the knots is isotropic. Nothing printed is contradicted, since every sentence is stated
   for finite masks or for families continuous in scale; but pp. 89, 104 and 106 and § 7.2(4) frame
   the obstruction as the lattice's alone, and § 7.2(4) answers only the finite case.
3. **Headlines out of step with the body.**
   - The abstract and contribution 3 never say that the selected Matérn pyramid is covariant under
     every dilation (Thm 5.4(1), 5.19(2)).
   - The selection's qualifications proved in the body (Prop. 5.18: the principle ⇔ the step is a
     resolvent; Thm 5.19(3): only λ = q; Prop. 5.20(2); the finite-step form rejects the Gaussian)
     reach neither the abstract, contribution 3 nor § 7.1.
   - Contribution 4 (p. 4) still calls a rotating dilation "outside the statement", which Prop. 6.6
     now answers; Props. 6.6 and 6.16 are named in no contribution.
   - p. 5 says the phase entropy "selects the fully covariant member"; it selects the similarity
     member, and its reach is narrower than S8, S23, p. 49, p. 57 and p. 66 say (it is not invariant
     under 𝒢_q, it excludes the Matérn ladder's infinite step, and it vanishes on every member of a
     Gaussian ladder).
   - p. 111: "On the line the count of local extrema gives that reason" is unsupported for stratum 2
     (S.37 gives a sufficient class, no selection).
4. **Small errors in text and tables.**
   - The Figure 4 caption (p. 78): a = 5/2 does not meet the proof's a = r + 1 (it needs a ≥ 3.33;
     W(r) = W(0)/4 at r = 2.331); the argument only needs a > r.
   - p. 66 identifies two members of Lindeberg's time-causal family: the squared-modulus reading is
     the member with time constants cq^{-i}, ratio q, not the one of ratio q² named before it.
   - Table 4 has no row and no sentence for Prop. 6.6; Table 3's row for Prop. 3.20(1), (2) claims
     the moment equivalence, which `ladder_knot_kernel_2` does not state (`_moments` does, reading
     Thm 2.26).
   - "in d ≥ 2" is missing at pp. 99–100 and p. 112 (false at d = 1), and Def. 6.3's SO(d) is
     trivial at d = 1.
   - p. 98 cites Prop. 6.18(1) for bounded uniqueness, which it states only for summable solutions.
   - p. 31 "by no fully covariant one" cites a statement about symmetric families.
   - The supplement's list of what the paper reads (S1) is wrong on four counts; its index entry
     misses five citations of the earlier modules.
   - Slips: "Lemma 3.5" for 3.4 (twice), "q > 0" in Prop. 3.23, "i < n" in S.17's proof, the S.34
     constant (4 where the proof gives 2), a pointer to S2.1 for S2.2, the bibliography (Stein's
     publisher, "P. WHITTLE", a title printing "R^n").
5. **Attribution and positioning.** Section 3's core is described by the reviewers as the theory of
   additive processes and semi-selfdecomposable laws (Sato §§ 9, 16; Maejima–Sato; Maejima–Ueda),
   which the paper attributes in two places only; the lattice criterion is unattributed in the
   abstract, the contributions and § 6.3; the two-pass recursion (Shen–Castan, Unser; held and read
   in this project's records) and Scherzer–Weickert (held) are not cited. Each source claim is the
   librarian's; see "Sources".

**The trust base.** Two blocks ask that the footers "Every step is machine-checked" go, or be made
uniform, and that formal statements whose object is a hypothesis (Theorem 3.12 takes A_t = a(t)I;
Prop. 5.15(3) and S.36 take `IsMaternPyramid`; S.15, S.16, S.23, S.25 take the pair of S.13) be
explained. The verifiers find the formal statements are the printed ones, universally quantified over
the defining predicate: nothing of substance is unchecked. Round 1's D4 keeps the footers; one
sentence in Appendix A explains the hypothesis form, and the proof of Thm 3.12(2) reads "as the
statement assumes" where it now cites Lemma 3.5.

**Strengthenings found.** Under the standing rule these are made and reported:
- Thm 2.20 follows from Thm 2.17 (y = Ux), and Thm 2.25's finiteness from its support clause: one
  admitted axiom (`cited_A42`) becomes a theorem, so "ten cited facts" becomes nine;
- Prop. 6.6 needs only an invertible M (an atom argument), not "expanding";
- Prop. 6.9(2) holds under a logarithmic moment of σ, not only finite support;
- Prop. 3.20(2)'s uniqueness up to relabelling holds exactly when the ladder's data span an extreme
  ray; the printed condition misses the Gaussian-plus-jump split;
- Prop. 6.16 holds for masks with an exponential moment (analytic transform) and for signed finite
  masks of mass one;
- S.30 is an equivalence; S.34's constant is 2; S.17(1) gains its range clause
  (∫ τ² ∧ (1 + log₊τ) dκ < ∞); Prop. 6.18(1) states bounded uniqueness; Prop. 6.12 drops an unused
  hypothesis and, through Prop. 6.5(1), Thm 2.26.

## The findings

Verdicts: **C** confirmed, **P** partly, **W** wrong, **AD** already decided (round, item), **S**
turns on a source. "Paper" is paper-side prose; "shared" is blueprint text transcribed; "Lean" adds a
formal change.

### Block s1-3 (§§ 1–3)

| Item | Finding | Verdict | Response | Lands |
|---|---|---|---|---|
| R1 | Full covariance of the Matérn pyramid absent from abstract and contribution 3 | C | a clause each | paper (A) |
| R2 | p. 4 "outside the statement" against Prop. 6.6; the abstract names 6.6 without stating it | C | rewrite contribution 4; state 6.6 in the abstract | paper (A) |
| R3 | Maejima–Ueda absent from the abstract and contributions 1, 2, 4 | C | a clause each, with what is theirs and what is the paper's | paper (A) |
| R4 | Lemma 3.3, 3.5, Thm 3.12(1), Prop. 3.22, Lemma 3.6(2) unattributed to additive-process theory | C / S | lead sentences after the librarian | paper (A) |
| R5 | "classification" for a description | P | "a description of the families by their Lévy data" | paper (A) |
| R6 | the footers | AD (r1 D4, r2) | kept; Appendix A sentence (F1) | — |
| R7 | print the axioms' Lean statements | P | decision D1 | — |
| R8 | "as its source states it, or narrower": Thm 2.25 adds finiteness from Sato's proof | P | moot after the strengthening (finiteness derived) | shared + Lean (C) |
| R9 | Prop. 6.6 missing from Table 4's lead; A-numbers unexplained | C | two sentences | paper (A) |
| R10 | scope of the isotropy results | P | with s6-7.R5 | paper (A) |
| R11 | Lindeberg's time-causal kernel absent from § 1 | C | one sentence on p. 5, with the member fixed (s4-5.R6) | paper (A) |
| R12 | p. 31 "by no fully covariant one" cites a symmetric-family statement | C | "symmetric" | paper (A) |
| R13 | halve the block | AD (r2 D2) | deferred to a journal version | — |
| S1 | Fig. 2's oscillation can be proved (Mellin: mean square 1/12); caption names no script | C | name the script in the caption (A); the proof in batch D | paper |
| S2 | prove Thms 2.24, 2.25 | P | 2.25's clause derived (C); 2.24 stays admitted | shared + Lean (C) |
| S3 | Prop. 3.20(2): the exact uniqueness condition | C | strengthening | shared + Lean (C) |
| S4 | 3.20(4)(b): e, the restriction of A_d, the normalization | C | phrases | shared (B) |
| S5 | "in the proof of Lemma 3.5" → 3.4 (two places) | C | a word each | shared (B) |
| S6 | "q > 0" in Prop. 3.23 | C | "q > 1", or say why q > 0 | shared (B) |
| S7 | "marginal of no" wording; p. 33 drops "infinitely divisible" | P | a word, a clause | shared, paper (B) |
| S8 | a(0) = 0 in Thm 3.12(1)'s converse | W; AD (r2) | none | — |
| S9 | Prop. 3.14's last clause rests on the later Prop. 3.19 | C | move the node before 3.14 | shared (D) |
| S10, S11 | one symbol per dilation; "pyramid" names three objects; strata relative to q | P / C | one sentence on the three uses (S11); symbols AD (r1 D3) | paper (A) |
| S12 | move the six unread facts | AD (r2 D2) | — | — |
| S13 | Prop. 6.16 for an exponential moment, signed masks | C | strengthening | shared + Lean (C) |
| S14 | Prop. 3.20(3) without symmetry or infinite divisibility | C / S | a remark citing the source, after the librarian | paper (A) |
| S15 | stage lemma and the positive maximum principle | P / S | a sentence after the librarian | paper (A) |
| S16 | "good for one decimation" is vague | C / S | name the criterion after the librarian | paper (A) |
| S17 | bibliography: Stein, Karlin, Whittle | C | fix | bib (A) |
| F1 | Thm 3.12 against Tables 3, 4 | P | proof phrase "as the statement assumes"; Appendix A sentence | shared (B), paper (A) |
| F10 | Thm 3.12, Props. 3.13, 3.14, Thm 3.15 lack the footer | C | AD (r1 D4: footers as they are) | — |
| 2.9 / T6 | abstract omits AI-only comparison; "numbered statements" includes definitions | C | a clause each | paper (A) |

### Block s4-5 (§§ 4–5)

| Item | Finding | Verdict | Response | Lands |
|---|---|---|---|---|
| R2 | kernels singular for integer q; pp. 35, 45 "samples them on grids" | C | new proposition (non-a.c. in Lean, singular in its proof); pp. 35, 45 rewritten | shared + Lean (C), paper (A) |
| R1 | no exact mask meets equal contribution | C | a sentence at S-35, the Prop. 4.5 lead and § 7.1; a clause in the new proposition | paper (A) |
| R3 | the selection's qualifications | P | abstract, contribution 3, § 7.1 | paper (A) |
| R4 | p. 111 "count of local extrema gives that reason" | C | "counting selects among the fully covariant families; on a ladder it holds for a class (S.37)" | paper (A) |
| R5 | Fig. 4 caption: a = 5/2 | C | caption: the argument needs a > r, r = 2.33 admissible; δ below 0.002 | paper (A) |
| R6 | p. 66 identifies two members of Lindeberg's family | C | name the member (ratio q, constants cq^{-i}) | paper (A) |
| R7 | Maejima–Ueda at contribution 2, the § 4.2 lead | P | with s1-3.R3 | paper (A) |
| R8 | 2-D non-creation in Lindeberg 1994, p. 101 | S | a sentence after the librarian | paper (A) |
| R9 | non-enhancement, regularization as diffusion | P / S | cite Scherzer–Weickert, Nielsen–Florack–Deriche (held) and what the librarian confirms | paper, bib (A) |
| R10 | the two-pass recursion is classical | C | cite Shen–Castan, Unser (held) at Prop. 4.6 | paper, bib (A) |
| R11 | Def. 6.2(1) does not name its reference | C (the senses AD r1 B4/D2) | a clause | shared (B) |
| R12 | S.34–S.37 into the main text | AD (r1 R12, adr 0007–0008) | — | — |
| R13 | p. 112 "in d ≥ 2"; Prop. 5.21 | C / P | a phrase; a sentence on what does hold | paper (A) |
| R14 | "Measured: the size of the error" | P | a sentence on why V_n is the reference | paper (A) |
| R15 | "can rise at every rung" (pp. 74, 100, 112) | C | "for an input that depends on the rung" | paper (A) |
| R16 | Table 4 lists 5.11, 5.15 with no cited fact | W as an anomaly | with F1's sentence | paper (A) |
| R17 | repository availability | not a finding (r2 D3) | — | — |
| S1, S2, S7, S8, S9 | restructure 5.15; 5.21 as a remark; moves; renames | editorial / AD (r1 B10, B14, B17, D3; adr 0008) | — | — |
| S3 | the level-set reading of the principle | C | a remark | paper (D) |
| S4, S5 | explicit variant only δ₀; grid converse (sufficiency) | C (first parts) | optional | (D) |
| S6 | build the Matérn pyramid directly | P (saving smaller) | none | — |
| S10 | Table 1 at q = 3 and h/(ct) = √2 | C (recomputed) | optional rows | paper, script (D) |
| S11 | λ_{s,t}, 0 < s < t, are not Pólya frequency sequences | C / S | a remark | paper (D) |
| S12, S13 | cite Lowe, Lindeberg 2024, Crowley; singular ID laws | S | after the librarian | paper (A) |
| S14 | no kernel μ_t is a Matérn law | P (p. 58 has γ > d/2) | a sentence | paper (A) |
| S16 | small repairs in shared proofs (K ρ_δ pointwise; g_Σ undefined; "that lemma" → Thm 2.9; "u = 1 and u = 2"; c reused; Lemma 5.3's cited fact) | C | a phrase each | shared (B) |
| S17 | p. 49 "rescaled to the finest grid" | C | a phrase | shared, paper (B) |
| S18 | Thm 2.15 in the essential sense | S | after the librarian | — |

### Block s6-7-appendix (§§ 6–7, Appendix A)

| Item | Finding | Verdict | Response | Lands |
|---|---|---|---|---|
| R5 | the band-limited mask | C (mathematics); P (text) | sentences at pp. 89, 104, 106, § 7.1, § 7.2(4); the example per decision D2 | paper (A), D2 |
| R3 | Table 4 omits Prop. 6.6 | C | a sentence in Appendix A; the script emits it | paper, script (A) |
| R4 | Table 3's row for 3.20(1), (2) | C | add `ladder_knot_kernel_2_moments` (Thm 2.26) to the row, pinned in the guard | paper, Lean guard (C) |
| R6 | contribution 4 | P | with s1-3.R2 | paper (A) |
| R1 | print the Lean statements | P | decision D1 | — |
| R2 | the abstract: comparison by AI agents only | P | a clause | paper (A) |
| R7 | attribution of the criterion (abstract, § 6.3 lead, § 7); the step "w infinitely divisible from continuity" is not Maejima–Ueda's | P | say which part is whose | paper (A) |
| R8 | § 6.4 as known material | S / P | attribute after the librarian (Lindeberg 1990 γ = 1/3, Whittle, Besag) | paper (A) |
| R9 | p. 98 bounded uniqueness; pp. 99–100 and p. 112 "in d ≥ 2"; SO(d) at d = 1; γ ≥ 1 against γ ≥ 0 | C | 6.18(1) strengthened (C); phrases (A); a d = 1 note in Def. 6.3 (B); γ known (handoff) | mixed |
| R10 | Thm 2.15 is the author's own proposition | P (said in § 1.1) | a clause in the abstract | paper (A) |
| S1 | one knot lemma for a linear M | sound | with D2 of round 2's formal work, later | (D) |
| S2 | 6.6 from one atom, without "expanding" | C | strengthening | shared + skeleton (C) |
| S3 | the criterion does not involve q | C | a sentence | paper (A) |
| S4 | exact masks violate equal contribution | C | with s4-5.R1 | paper (A) |
| S5 | an operational test for infinite divisibility | C (with ŵ > 0 first) | a sentence | paper (A) |
| S6 | Prop. 6.9(2) under a logarithmic moment | C | strengthening | shared + Lean (C) |
| S7 | Prop. 6.16 for signed or complex masks | C / S | with s1-3.S13 | (C) |
| S8 | Prop. 6.12: unused hypothesis; Thm 2.26 avoidable | C | strengthening | shared + Lean (C) |
| S9 | Thm 2.20 from 2.17; 2.25 shortened | C | strengthening: nine admitted facts | shared + Lean (C) |
| S10 | sphere uncountability proved twice | C (moves AD r1) | prove once | shared (B) |
| S11 | § 7 repeats pp. 2–4 | AD (r2 D2) | — | — |
| S12 | § 7.2(2): what does hold after decimation | P | a sentence | paper (A) |
| S13 | κ_t as an exponential-time mixture of the discrete heat semigroup | C / S | a sentence after the librarian | paper (A) |
| S14 | p. 100 "every pyramid whose octave steps are a.c." | P | "for an arbitrary input" | paper (A) |
| S15, S20 | references; [17]'s title, [25]'s numbering | C / S | bib | (A) |
| S16 | "family" for Def. 6.3's carrier, which lacks (ND) | C | a clause | shared (B) |
| S17, S18 | notation; footers | P / AD (r1 D3, D4) | — | — |
| S19 | q ≥ 1 in Def. 6.10, Prop. 6.14(2) | P (harmless) | a clause | shared (B) |
| § 3.1 r3 | "isotropic" for a family in 6.6 | C | a phrase | shared (B) |
| § 3.3 | Prop. 6.5's opening irrelevant to (3) | C | a sentence | shared (B) |
| § 5.5 | Def. 6.2's formal counterparts unstated | P | with F1's sentence | paper (A) |

### Block supplement

| Item | Finding | Verdict | Response | Lands |
|---|---|---|---|---|
| R1, R2 | additive processes in law, jump intensity, semistable hemigroups | S | the S2.1 lead, after the librarian | paper (A) |
| R3 | Maejima–Ueda in the supplement; S.17(1)'s range; four telescoping proofs | C | attribution (A); range clause (C); telescoping once (D) | mixed |
| R4 | the phase entropy's reach (S8, S23, after S.25, after S.31) | C | a paragraph: gauge non-invariance, the Gaussian ladder, the Matérn exclusion, the incomparable classes | paper (A) |
| R5 | p. 5 "fully covariant member" (wrong), p. 66 scope (wrong), pp. 49, 57 (loose) | P | four sentences | paper (A) |
| R6 | closing sentences; formal counterparts over the pair | P | with F1's sentence; a gloss in S1 | paper (A) |
| R7 | S.34–S.37 carry a main theorem; the S1 list wrong | P (move AD r1) | fix the list | paper (A) |
| R8 | S.35(1)–(2) is Thm 2.14's case | C | cite it; the reflection reading | paper (A) |
| R9 | S.38(3), (4) attribution | P / S | a sentence each | paper (A) |
| R10 | slips: "i < n"; "knot relation of Def. 2.4"; "sampled Matérn levels"; S2.1 → S2.2; the symbol table's "Section S2.2" | C / P | a symbol, phrases | shared (B), paper (A) |
| R11 | the § 2.1.4 index misses five citations | C | bullets (A); the extreme rays restated per decision D3 | paper (A) |
| R12 | S8 non-creation unqualified | C | a clause | paper (A) |
| R13 | one name per object (uniform coupling = log-uniform member; θ/ζ; h_t/σ_t) | C | name the identity where both appear; renames AD (r1 D3) | paper (A) |
| S1, S2, S6 | reductions and moves | AD (r2 D2, adr 0008) | — | — |
| S3 | S.30 as an equivalence | C | strengthening | shared + Lean (C) |
| S4 | knot exponents = K_q \ {0}; S.37's hypothesis necessary | C | a remark | paper (D) |
| S5 | the lattice count for the sampled Laplace mask | P | a new lemma | (D) |
| S7, S8, S9 | telescoping once; a table; rename the orbit | C / P | (D) | — |
| S10 | S.34's constant | C | 2 in place of 4 | shared + Lean (C) |
| S11 | span q^k gives k times the entropy | C | a remark | paper (A) |
| S12, S13 | theorem names; punctuation on S4 | C | words | paper, shared (B) |
| § 5.4 | closing sentences against Table 4 (S.3, S.29) | C | with F1's sentence | paper (A) |
| § 5.5 | Thm 2.5 listed under 2.17 alone | W | none | — |

## Found while checking

- **The obstruction without continuity.** The verifier of s6-7 built, from the band-limited mask, a
  family with (a), (c), (d) but not (b): μ_{s,t} = ∗_{n: s < qⁿ ≤ t} D_{q^{n−1}}w. It is isotropic and
  jumps at every knot. So the obstruction of Props. 6.5 and 6.6 needs (b) together with the lattice.
  p. 90 already says "(d) together with the continuity (b)"; the other passages should agree.
- **Prop. 5.21's mechanism is general**: any mask whose summable inverse has a negative weight off the
  coarse lattice gives the same failure after decimation (s4-5.R13).
- **Prop. 3.20(4)(a)'s general case** (no fully covariant family, symmetric or not, carries a lattice
  mask) is plausible but unproved: symmetrizing loses (ND). The paper should say "symmetric" (s1-3.R12)
  and claim nothing more.

## Sources

The librarian's answers, read from held copies, are `reviews/LIBRARIAN-r3.md`; the verifiers'
condensed verdicts are `reviews/r3-verification/`. Two sources were acquired (open access):
`lindeberg2024discrete`, `lowe2004distinctive`. What they change:

- **Additive processes (s1-3.R4, supp.R1).** Sato states what the reviewers said: Thm 9.1 and 9.7(i)
  (pp. 47, 51; Khintchine through a null array) is Lemma 3.3; Thm 9.8 (p. 52, systems of triplets, with
  the converse) is Lemma 3.5 and Thm 3.12(1); Thm 16.1 (pp. 99–100) is stratum 3; Thm 19.2 (p. 120,
  stated for additive processes) is the jump intensity of S2.1. Becker-Kern 2003 (J. Theoret. Probab.
  16, p. 574) treats convolution hemigroups with B m_{s,t} = m_{ls,lt}, including the (B, c)-semistable
  case of one ratio: it is cited in § 1 and § 3. Maejima–Sato 2003 (Thm 1.1, p. 611) passes to
  logarithmic time with a periodic random measure: cited at S2.1–S2.2. Each goes in as attribution at
  the lead of the statement; no statement changes.
- **Maejima–Sato 1999, Thm 1(ii), p. 349** is a dichotomy (b^ℤ or (0, ∞)), not the reviewer's
  trichotomy; Lemma 3.6(2) cites it with "cf.".
- **Vervaat 1979, Thm 1.6(b) and Lemma 1.7, p. 757**: Σ cⁿ Yₙ converges a.s. iff E log₊|Y| < ∞, with no
  symmetry and no infinite divisibility (s1-3.S14). Wolfe 1982 is the continuous-time version only.
- **Singular kernels (s4-5.R2).** Sato Thm 27.16 (Hartman–Wintner, p. 182): A = 0 and a discrete Lévy
  measure of infinite mass give a law that is absolutely continuous or continuous singular. With the
  non-a.c. part of the new proposition this gives "continuous singular" from a cited fact, an alternative
  to the 0–1 argument; batch C chooses the route that Lean can check. Jessen–Wintner 1935 is not held
  (Sato Prop. 27.18, p. 182, states it).
- **Sato Cor. 24.6, p. 149**: the finiteness of ν is in the proof, not the statement, as Thm 2.25's lead
  already says; batch C derives it, so the admitted statement keeps only what Sato states.
- **Karlin, Ch. 5, Thm 3.1, p. 233** is for bounded Borel functions, the output count pointwise and the
  input count essential. Thm 2.15 restates the selection module's Prop. 4.5 (p. 35), which extends it to
  integrable inputs and to the essential count and lists those steps among its admitted statements
  (its A.2). So Thm 2.15 is stated as its named source states it (s1-3.R8, s4-5.S18 settled); one
  clause in its lead says what the module adds to Karlin.
- **Burt–Adelson p. 533; Burt 1981, pp. 23–24.** Equal contribution is motivated by equal weight of the
  samples under reduction and by convergence, not by aliasing; Burt–Adelson state it for ratio 2, Burt
  for any order r. The new sentence says so and does not call it an aliasing condition.
- **Meer–Baugher–Rosenfeld 1987, pp. 513–515**: a mask is judged by closeness to the ideal low-pass for
  decimation by 2 (an antialiasing and a filtering index); p. 1's "good for one decimation" names it.
- **Lindeberg 1990, p. 246**: γ = 1/3 gives the nine-point operator, the most isotropic at large scales,
  and γ is explicitly not selected; § 6.4 cites it. **Lindeberg 2016, p. 62 and (41)–(47), p. 63**: the
  limit kernel is covariant under integer powers of c; § 1 cites it. **Lindeberg 1994**: p. 101 argues
  (Lifshitz–Pizer), without a theorem, that no non-trivial kernel in 2-D avoids creating extrema, cited
  as such at p. 5; p. 82 and p. 122 say pyramids are not covered and ask whether subsampling can keep a
  continuous scale parameter, which places the abstract's first sentences.
- **Scherzer–Weickert 2000**: Lemma 6, p. 53, the extremum principle for one Tikhonov step, and p. 43, one
  regularization step as one implicit diffusion step: cited in § 5.3. **Alvarez et al. 1993, Thm 2,
  p. 211**, and **Courrège 1966, Thm 0.1, p. 2-01** (the local positive maximum principle gives a
  second-order operator): cited beside the stage lemma.
- **Cavaretta–Dahmen–Micchelli** does not state Prop. 6.16 or anything on rotation-invariant refinable
  functions; no precedent is claimed. **Simoncelli–Freeman 1995, p. 445**: a strictly band-limited
  low-pass "to prevent aliasing", which places the band-limited example. **Van De Ville–Blu–Unser 2005**:
  nearly isotropic, quincunx, not exactly rotation invariant.
- **Lowe 2004, pp. 6–7**: a Gaussian family at ratio k = 2^{1/s}, resampled each octave: a pyramid that
  computes the steps of a family, cited in § 1's literature paragraph. **Lindeberg 2024, p. 762**
  excludes subsampling; **Lindeberg–Bretzner 2003, § 3.1** reduces by binomial diffusion steps.
- **Lindgren–Rue–Lindström, p. 429**: integer powers of the lattice (κ² − Δ_h) are their precision
  operators; the lattice Bessel covariance is Besag 1981 (not held), cited through them. **Weickert et
  al. 1998, p. 405**: AOS shows "a preference of certain directions" at large steps.
- **Bibliography**: Stein 1970, Princeton University Press; Karlin 1968, Volume I, Stanford.
- **Not held**: Inusah–Kozubowski 2006, Besag 1981, Jessen–Wintner 1935; none is cited directly.
  Maejima–Ueda's journal version is open access but refused the librarian's download (403): the paper
  keeps the arXiv numbering until the author downloads it.

## Decisions for the author

**D1. Print the formal statements of the admitted facts?** Two blocks ask for the Lean statements of
the fifteen axioms (and of the headline declarations) in print, since the export repository does not
exist before the release and the comparison of formal with printed statements was made by AI agents
only. *Recommendation:* yes, the axioms only, as a generated appendix of the supplement (about three
pages, produced from the Lean source by a script beside `theory_axioms_table.py`); the headline
declarations stay in the repository. It makes the trust base readable without the code, at no cost to
the paper's length.

**D2. The band-limited mask: a numbered statement or a sentence?** The example is correct and settles
the infinite-mask half of question 4 the other way. *Recommendation:* a numbered proposition beside
Prop. 6.16, proved in print and marked `\notready` like Prop. 6.6 (its Lean needs Poisson summation on
ℤ^d, which Mathlib does not have in that form); § 1.1 and the abstract then name two propositions
proved in print only. The alternative is two sentences in § 7.2(4) that describe it without a number,
which `WRITING.md` § 3 discourages for a proof.

**D3. Restate the cone module's extreme rays in § 2?** The supplement cites V-cone Prop. 3.3 (the
extreme rays of the fully covariant cone) without restating it. *Recommendation:* yes, as a cited fact
"stated for the reader" (no Lean), with its page; it joins the six unread facts.

**Settled by the author (2026-11-23): D1–D3 as recommended.** D2 is a blueprint node, as round 2's
D1 was, "so that we keep track on our statements, and don't get sloppy just because we are close to
finished": a numbered proposition with its printed proof, marked `\notready`, its statement typed in
`PyramidsSkeleton` with `sorry` where Lean can state it, and named in § 1.1 and the abstract as
proved in print only. The same holds for every new statement of this round: the proposition on
singular kernels is a blueprint node too (its non-a.c. part in Lean; its singular part in Lean too if
Mathlib's Kolmogorov 0–1 law gives a short route, otherwise a separate clause proved in print, which
§ 1.1 then names), and D3's restated fact is a blueprint node in § 2, stated for the
reader.

Already decided and not reopened: the footers (round 1 D4, raised again by three blocks), the
journal-length cuts and moves (round 2 D2; adr 0007–0008), the names of the senses of "exact" (round 1
D2), the symbol renames (round 1 D3).

## Batches

- **A, paper-side** (one session, no Lean): every "paper (A)" row; the attribution rows once the
  librarian's answers are filed; the bibliography. Gates as usual.
- **B, shared text without Lean**: every "shared (B)" row, through the blueprint and transcribed
  (`linkage check` verbatim).
- **C, Lean, one VM run**: the new proposition on singular kernels (the transform does not tend to 0,
  in Lean; singular in its printed proof); the strengthenings (Thm 2.20 derived and 2.25 shortened,
  nine admitted facts; Prop. 6.6 for an invertible M, in the skeleton; 6.9(2); 3.20(2); 6.16; 6.18(1);
  6.12; S.17(1); S.30; S.34); Table 3's row; then the axiom guard, Table 4, the counts in § 1.1 and the
  abstract, and D1–D3 as decided. Renumbering in `CHANGELOG.md`.
- **D, optional, after the release if at all**: Fig. 2's proof; the level-set remark; Table 1's extra
  rows; λ_{s,t} not PF; S.37's necessity; the Laplace-mask count; Prop. 3.14's order; telescoping once.

**Batches A and B's state (2026-11-23).** Done on the branch `claude/pyramids-review-r3-batch-ab`,
one PR; `CHANGELOG.md` lists every change. Every "paper (A)" and "shared (B)" row has its sentence,
clause or phrase, with these readings:
- pp. 35 and 45 now say that for an integer q the *knot kernels* of an exact grid pyramid have no
  density, with the argument in prose (Lemma 6.4's product, the period of ŵ, Thm 2.18). The claim
  for every kernel μ_t and the word "singular" wait for batch C's proposition; `TODO(batch C)`
  comments mark the place there and at the band-limited example (pp. 4, 87, 89, 104, § 7.1,
  § 7.2(4)), which the prose names without a number.
- p. 98 no longer calls κ_t * f "the unique bounded solution"; a `TODO(batch C)` restores it with
  the strengthening of Prop. 6.18(1).
- s1-3.S4: the unit vector e of Prop. 3.20(4)(b) is kept as the round-2 wording had it (the
  equation is stated for every vector); the normalization and "restriction of an element of 𝒜_d"
  are fixed.
- s1-3.S14 and the refinable-law remark rest on Vervaat's Thm 1.6(b) and Lemma 1.7 (p. 757), on the
  line only.
- Lemma 5.3's closing sentence against Table 4 is answered by Appendix A's sentence on cited facts
  that the development proves (Thm 2.33), not by a change in the shared proof.
- Not taken: theorem names beside every third-party number (supp.S12, cosmetic); a theory-axioms
  script change for Prop. 6.6 (Appendix A's sentence covers it; batch C regenerates Table 4).
- Four sources were acquired after the plan (`reviews/LIBRARIAN-r3.md`, "Acquired after the
  plan"): Maejima–Ueda is cited in its journal version (Thm 3.3, p. 353), Inusah–Kozubowski before
  Prop. 4.6, Besag's K₀ as an approximation in § 6.4; Jessen–Wintner (Thm 35, p. 86) waits for
  batch C's proof that the kernels are singular.
- The abstract grew to about 570 words with the headline qualifications (about 630 after batch C); `linkage paper` flags
  the template's 150–250 as advisory, as it did before. A journal version cuts it.
- A blind register review (`draft-reviewer`, opus) of the changed prose gave about 75 flags, all
  applied or answered in the text; the commentary it found inside Defs. 6.2–6.3 and Props. 3.23,
  6.5(3) was moved out through the blueprint.

**Batch C's state (2026-11-23).** Done on `claude/pyramids-review-r3-batch-c`, in four mathematician
runs (opus) that compiled on the VM by `vm.sh run`, from the brief `BRIEF-review-r3-batch-c.md`;
the coordinating session transcribed, renumbered and wrote D1. Every item of the batch is made,
none narrowed, no axiom added, nothing found false:
- Thm 2.20 (A42) is a theorem with no cited fact (276 Lean lines), Thm 2.25 (A48) admits only
  Cor. 24.6's sentence: nine admitted facts, fourteen axioms.
- Strengthenings: Prop. 6.6 for an invertible M (print); 6.9(2) under a logarithmic moment; 6.12
  without A49; 6.16 for an exponential moment and signed finite masks; 6.18(1) bounded uniqueness;
  3.20(2) the exact uniqueness condition, both directions in Lean (the extreme rays' description in
  print); S.17(1) its range; S.30 an equivalence; S.34 the constant 2.
- New nodes: Prop. 6.7 (singular kernels; (1)–(2) in Lean, (3) in print), Prop. 6.18 (the
  band-limited example, in print, D2), Thm 2.13 (V-cone Prop. 3.3, stated for the reader, D3).
- D1: supplement Section S3, generated from the Lean source.
- Table 3's row (s6-7.R4) and Table 4 regenerated. Renumbering in `CHANGELOG.md`.
- A blind register review (opus) of batch C's prose: the paper-side flags applied, and in the shared
  text the proof of Thm 2.21 (`w` renamed ξ, its closing sentence). Shared-text style flags left,
  "blueprint, left": long sentences in Prop. 3.20(2)'s statement and proof and in Prop. 6.13's
  proof; the letter clashes ψ (Prop. 6.17's proof against the bump of 6.18), `w(τ)` in the proofs
  of S.17 and S.30, data written D next to the dilation D_q; S.30's closing sentence.
- Left: the Lean of Props. 6.6 (250–400 lines), 6.7(3) (500–800) and 6.18 (1200–2000, Poisson
  summation); Prop. 3.20(2)'s description of the extreme rays in Lean; the precedent search for
  Prop. 6.16 in the refinable-function literature; batch D.

Then the release (`RELEASE.md`), before the computation paper's pass 6 (the author, 2026-11-23).

**The round is answered (2026-11-23, release preparation).** Batches A–C are the response; batch D
is optional and deferred past the first release, as this plan's "Batches" leaves it. The release's
record is `RELEASE-prep-pyramids-v0.1.md`.
