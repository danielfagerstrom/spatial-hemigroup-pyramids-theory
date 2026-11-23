# Verifier verdicts, block s1-3 (opus, condensed)

No SEVERE. Repeats: footers (r1 D4, r2), journal cuts (r2 D2), Fig 2 Mellin optional (r2), Thm 3.12(1) converse clause (r2 not taken), Lindeberg time-causal (r2 S4 in §§2,5).

- R1 CONFIRMED: abstract + contribution 3 omit that Matérn pyramid is covariant under every dilation (Thm 5.4(1), 5.19(2), p.15, table p.31). Paper-side clause each.
- R2 CONFIRMED: p.4 (intro:181-182) "outside the statement (Section 7)" vs Prop 6.6; abstract names 6.6 without stating it. Paper-side.
- R3 CONFIRMED text: Maejima–Ueda missing at abstract, contributions 1, 2, 4 (present p.5, p.35). Paper-side.
- R4 CONFIRMED text / SOURCE: Lemma 3.3, 3.5, Thm 3.12(1), Prop 3.22, Lemma 3.6(2) lack attribution to Sato additive processes (Thm 9.1, 9.7, 9.8), Maejima–Sato, Wolfe/Vervaat, Becker-Kern hemigroups. Paper-side leads + refs.
- R5 PARTLY: "classification" vs "description" — judgment, one word.
- R6 (footers) PARTLY, already decided r1 D4 / r2.
- R7 PARTLY: print axioms/declarations in Appendix A — judgment.
- R8 PARTLY: Thm 2.25 adds finiteness of ν from Sato's proof (one-line from supp ⊆ Z); § 1.1 "as its source states it, or narrower" needs a word. Thm 2.15 OK as named source.
- R9 CONFIRMED: Prop 6.6 missing from Table 4 lead-in (appendix-verification.tex:96-106); A-numbers in Table 2 unexplained.
- R10 PARTLY: isotropy vacuous without family already said (intro:190-192, 06-price:35-36); 6.16 and 7.2(4) say finite; nothing false. 6.16 proof extends to exponential moment / signed finite masks. Counterexample: other verifier.
- R11 CONFIRMED: Lindeberg time-causal limit kernel absent from § 1 (p.66, S-39 have it). Paper-side, p.5.
- R12 CONFIRMED: p.31 (03-pyramid:867-868) "by no fully covariant one" cites 3.20(4)(a), stated for symmetric families; general case unproved. One word "symmetric".
- R13 ALREADY-DECIDED (r2 D2).
- S1 CONFIRMED: Fig 2 "read from the plot" provable (Mellin: |coef| = 1/(2π|k|), mean-square 1/12); caption names no script. r2 left optional.
- S2 PARTLY: Thms 2.24, 2.25 provable in print (2.24 not via 2.17); removing axioms A46/A48 is Lean work.
- S3 CONFIRMED (strengthening): Prop 3.20(2) uniqueness-up-to-relabelling condition is extreme ray of the data cone; printed condition misses Gaussian+jump split and Gaussian rank ≥ 2. Shared + Lean.
- S4 CONFIRMED minor: 3.20(4)(b) e / A_d restriction / normalization phrase.
- S5 CONFIRMED minor: "in the proof of Lemma 3.5" → Lemma 3.4 (03-pyramid:576, :659).
- S6 CONFIRMED minor: Prop 3.23 "q > 0" (03-pyramid:1601).
- S7 PARTLY: "marginal of no" wording (03-pyramid:943-945); p.33 drops "infinitely divisible" (:1026); p.3 is fine.
- S8 WRONG as error / already decided (r2).
- S9 CONFIRMED: Prop 3.14 last clause rests on later Prop 3.19 (no circle). Move node.
- S10 PARTLY judgment (r1 D3 symbol table).
- S11 CONFIRMED: "pyramid" three objects; strata relative to q vs intrinsic trichotomy (intro:107-112). A sentence.
- S12 ALREADY-DECIDED (r2 D2).
- S13 CONFIRMED math: 6.16 extends (exp moment, signed finite). Remark.
- S14 CONFIRMED math: 3.20(3) convergence iff E log+|Y| < ∞, no symmetry/ID needed (Wolfe/Vervaat SOURCE).
- S15 PARTLY: stage lemma vs positive maximum principle (Courrège SOURCE).
- S16 CONFIRMED vague "good for one decimation" (intro:11), SOURCE.
- S17 CONFIRMED: bib [32] Stein no publisher, [16] Karlin no volume, [36] "P. WHITTLE".
- F1 PARTLY (Table 4 vs Thm 3.12): lattice_strata_1/_2 take A_t = a(t)I as hypothesis, so read no A42; printed proof (2) says "by Lemma 3.5". Fix: proof phrase "as the statement assumes" + one Appendix A sentence (a statement whose hypothesis comes from an earlier statement lists only its own axioms). Same for creation_plane_3 / IsMaternPyramid. No Lean change.
- F10 CONFIRMED: Thm 3.12, Prop 3.13, 3.14, Thm 3.15 (and Thm 2.16) lack the footer.
- 2.9/T6 CONFIRMED: abstract omits AI-only statement comparison and affine axioms; "numbered statements" includes definitions while § 1.1 says lemma/prop/thm/cor.

Needs held copy: Sato (Thm 9.1, 9.7, 9.8; Cor 24.6 p.149 finiteness; Thm 8.1, Prop 11.10, 15.5, Thm 15.10, Cor 24.4, Thm 25.3); Maejima–Sato 1999 epochs dichotomy; Wolfe 1982 / Vervaat 1979 log-moment series; Becker-Kern 2003 hemigroups J Theoret Probab; Karlin Ch5 Thm 3.1 p.233 hypotheses; Lindeberg 2016 covariance under integer powers; Meer–Baugher–Rosenfeld criterion; Courrège PMP; Hanke–Groetsch / RSW extremum principle; CDM 1991 radial refinable.
