# Verifier verdicts, block supplement (opus, condensed)

No SEVERE.

- R1 additive processes in law (Sato 9.1, 9.7, 9.8, 16.1) not cited: SOURCE; paper cites Sato 8.1, 9.3, §15, 19.2(i), 24.4/24.6, 25.4 only. Sentences in § 3 and S2.1 lead after librarian.
- R2 surface measure as jump intensity; Maejima–Sato 2003; Becker-Kern: SOURCE; only attribution is Maejima–Sato 1999 Thm 7 (supp-line:193-196).
- R3 Maejima–Ueda not cited in supplement (S.17(1), S.18(1), S.20(1), S.40(2)): CONFIRMED. Mixing measure = folded Lévy measure of residual: holds. Range of parametrization missing from S.17(1) statement (supp-line:874-880; converse only in proof :939-941; Lean qcin_1_repr representation+uniqueness): condition ∫ τ²∧(1+log₊τ) dκ < ∞. Four telescoping proofs (S.17 :915-921, S.18(1), S.20(1), S.30). Fix: attribution sentence; S.17(1) range clause (shared + small Lean).
- R4 phase entropy reach: CONFIRMED in substance. Selects by definition (S.26 proof; remark after S.26 :1414-1417 already says KL vanishes at Haar); not for S.30. −∞ on grid pyramids (already said S8, S23). Zero on Gaussian ladders: every member maximizer, not said explicitly. Not gauge-invariant: relabelled similarity member is fully covariant with E' < 0 — not said (S38 :2342-2345 says orbit has other fully covariant members). S.29(1), S.30 assume 0 < |μ| < ∞; Matérn step L_c infinite mass ⇒ excluded; Matérn in S.26's class; classes incomparable. S8 (:29-30) and S23 (:1154) "a strictly larger class of ladders with a finite step" ambiguous/false on natural reading. Fix: supplement prose S8, S23, after S.25, after S.31; a paragraph.
- R5 paper pp. 5, 49, 57, 66: p.5 (01-introduction:252) "selects the fully covariant member" WRONG → "the similarity member". p.66 (05-matern:607-610) "On the line ... phase entropy ... In R^d Thm 5.19 takes its place" wrong scope (5.19 holds at d=1 too). pp.49 (04-line:513-514), 57 (04-line:1066) loose. Four sentences.
- R6 closing sentences: 27 with, 11 without (S.7, S.8, S.11, S.17, S.18, S.34–S.39). Five (S.15, S.16, S.23, S.25, S.36) take pair / IsMaternPyramid as hypothesis — universally quantified, same content. "Reader told nothing" false (abstract, § 1.1). Fix: one Appendix A sentence (same as F1, R16); optional S1 gloss. D4 repeat.
- R7 S.34–S.37 carry main theorem: CONFIRMED (Thm 5.4 (1),(3),(4),(5); 5.8, 5.9, 5.14; 4.7(2); 4.5 reads S.1, S.3; 6.15 reads S.33). Move declined r1 (adr 0007-0008). NEW: S1 list (supp-intro:11-14) wrong: S.9 only prose, S.3 omitted, S.34 not covered, S.33 read in § 6 while p.5 (01-introduction:254) says Sections 4–6. Fix: one sentence in supp-intro.
- R8 S.35(1)–(2) is Thm 2.14's named case, not cited (supp-line:2188-2234); uniqueness printed four times; supplement lacks the reflection reading (p.66 has it, itself mismatched). Fix: two sentences after S.35.
- R9 S.38(3) subdivision attribution indirect via 3.23(2); S.38(4) Schoenberg / Lindeberg 1990 SOURCE. Sentences.
- R10 slips: (1) "i < n" → 0 ≤ i < n (supp-line:915-917, S20) shared, no Lean; (3) "knot relation of Definition 2.4" (:2679, S43) term defined p.40 (03-pyramid:1582) — phrase; (4) "grid pyramid of sampled Matérn levels" (:2693) wrong object — phrase; (5) p.39 pointer "Section S2.1" → S2.2 (03-pyramid:1466); (6) p.15 symbol table (02-cited-facts:644) "alone, in Section S2.2, a step measure" → through S2.3.
- R11 index § 2.1.4 misses supplement citations: V-cone Prop 3.3 pp.15–16 (supp-line:851), V-cone Prop 6.4(4) p.58 (:2352), V-selection Prop 4.5 p.35 (:2428), Remark 4.15 (:2425, :2623), §4.3 pp.34–35 (:2650). CONFIRMED. Index bullets; restating extreme rays = new cited-fact node, stated for reader.
- R12 S8 (supp-line:34-35) "creates no extrema from one level to the next" unqualified: CONFIRMED. A clause.
- R13 one name per object: "uniform coupling" (03-pyramid:1300, 04-line:355, 06-price:734, 806) = "log-uniform member" (supp-line:1916-2033); θ vs ζ (S.6 supp-strata:373); h_t vs σ_t (05-matern:1016); geometric vs geometric-jump partly. Renames.
- S1 reduce § S1: declined (adr 0008, r2 D2).
- S2 cite/shorten S.13 construction: SOURCE/editorial; D2.
- S3 S.30 as equivalence: CONFIRMED math. Shared clause + small Lean.
- S4 knot exponents = nonzero elements of K_q; S.37 hypothesis necessary (PF pairing step must be stated): CONFIRMED. Remark or clause.
- S5 lattice count sampled Laplace mask: PARTLY; needs extra lemma for infinite mask. New clause + Lean.
- S6 move modulation spectrum / appearance entropy: declined (D2, adr 0008).
- S7 telescoping once: CONFIRMED, optional.
- S8 table of three selections: partly done (S34 :2040-2048).
- S9 rename modulation orbit: CONFIRMED editorial.
- S10 Lemma S.34 constant: statement 4Σϑ_i⁻² (supp-line:2138), proof gives 2Σ then ≤ 4Σ (:2174), Lean 4 (LaplaceAtoms.lean:217). Strengthen to 2: shared + Lean.
- S11 entropy for span q^k = k × E: CONFIRMED. Remark.
- S12 theorem names beside numbers: cosmetic.
- S13 punctuation S4 (supp-strata:226, 257) "uniqueness of the folded pair Theorem 2.3 (a(s), …)": shared, a word.
- §2 S.33 two-line: already done in substance.
- §5.4 S.3 names Lemma 3.5 (2.17, 2.19, 2.20) while row {2.17, 2.19}; S.29 "cites no fact of its own" beside {2.17, 2.19, 2.20, 2.25}: upper-bound reading confirmed (same as F1).
- §5.5 Thm 2.5 under 2.17 alone: WRONG as worry (cited_A4 via line_levy_unique).

Needs held copy: Sato 9.1, 9.7, 9.8, 16.1, §19 jump intensity for additive; Maejima–Sato 2003; Becker-Kern 2003; Maejima–Ueda Lévy measure Σ T_{b^{-i}}ν and log-moment; Lindeberg 2016 covariance under c^j; Lindeberg 1990 VD classification, two-point averaging; Schoenberg / Karlin Ch5 Thm 3.1 p.233 pointwise vs essential; V-selection Prop 4.5 p.35 (essential sense, bounded g); V-line Thm 7.3 p.37 stratum 3 attribution to Sato 16.1; V-cone Prop 3.3 pp.15–16, Prop 6.4(4) p.58, V-selection Remark 4.15 pp.50–51; CDM 1991 Thm 3.3 p.48 for S.38(3).
