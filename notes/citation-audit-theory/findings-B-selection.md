# Citation check, group B-selection

Checker: a sonnet subagent that did not write the sentences, 2026-11-22. Its write was refused
("subagents return findings as text"); the session saved its returned table here unchanged.

Held copies: fagerstrom2026selection: `Own Publications/spatial-hemigroup-scale-space-selection-v0.1.pdf`,
the released V-selection v0.1 (title page "September 30, 2026 (v0.1)", doi 10.5281/zenodo.23047056;
Zotero's extra line names tag v0.1, concept DOI 10.5281/zenodo.23047055). Page offset 0, checked on
pp. 15-70. The text layer has the inequalities, indices and Greek letters right, so no page images
were taken. Sections: 1 Introduction (p. 1), 2 Setup (p. 8), 3 Locality (p. 15), 4 Non-creation
(p. 28), 5 Jet (p. 53), 6 Concluding remarks (p. 67), App. A Verification (p. 69).

Item pages: Thm 3.3 p. 16; Prop 3.8 p. 24; Thm 4.2 starts p. 30 (clauses (1)-(2) on p. 30, clause
(3) on p. 31); Cor 4.4 p. 33; Schoenberg's representation, end of p. 34 into p. 35 (§4.3 starts
p. 34); Prop 4.5 p. 35; Thm 4.10 p. 43; Remark 4.15 pp. 50-51 (the Lindeberg paragraph p. 51);
Prop 5.6 p. 60; the plane/diffusion sentence of §6 on p. 69.

Counts over 27 rows (25 input ids, X1, X2): OK 17, MINOR 6, LOCATOR 4, UNSUPPORTED 0,
HYPOTHESIS 0, UNREAD 0.

| id | where | locator | verdict | evidence | fix |
|----|-------|---------|---------|----------|-----|
| C009 | 01-introduction.tex:46 | §4 | OK | §4 (pp. 28-52) is the non-creation section. Four readings select three nested classes of line families (Rem 4.15, p. 50). | none |
| C023 | 01-introduction.tex:264 | none (progpaper) | OK | The Pólya frequency clause (variation diminution iff Pólya frequency kernel, plus Schoenberg's representation) is Prop 4.5, p. 35, with the cited facts at the end of p. 34. | optional: Prop. 4.5, p. 35 |
| C026 | 02-cited-facts.tex:10 | none (progpaper) | OK | Title and abstract: "locality, non-creation and the selection of the Gaussian". | none |
| C050 | 02-cited-facts.tex:441 | Thm. 4.2, p. 30 | MINOR | Thm 4.2: (2) global-extrema non-enhancement for every family (p. 30); (3) local extrema hold for F = a w^2 and fail when varpi is nonzero (p. 31). Cor 4.4, p. 33, matches. | `Thm.~4.2, pp.~30--31` |
| C051 | 02-cited-facts.tex:444 | Thm. 4.10, p. 43 | OK | Every interior increment variation-diminishing implies F = a w^2; conversely the Gaussian's increments are. | none |
| C052 | 02-cited-facts.tex:446 | Prop. 5.6, p. 60 | OK | Prop 5.6(1), p. 60, "The Helmholtz identity": (1 - t^2 d_x^2)^gamma u = f, integer gamma; for gamma = 1, d_x^2 u = (u - f)/t^2. | none |
| C053 | 02-cited-facts.tex:447 | §6, p. 67 | LOCATOR | §6 starts on p. 67. "In two dimensions the diffusion equation creates new local extrema" is in its last paragraph, p. 69, an attributed remark (Lindeberg, Lifshitz and Pizer), not a numbered result. | `\S~6, p.~69` |
| C126 | 05-matern.tex:474 | Prop. 4.5(2), p. 35 | OK | For F of the Pólya form and f the primitive of an integrable f': S^-(u - c) <= S^-(f - c) and S^-(d_x u) <= S^-(f'). The paper's hypotheses (a = 0, theta_i = q^i/c, sum theta_i^-2 < infinity, atoms listed once) match. | none |
| C134 | 05-matern.tex:1138 | Prop. 5.6(1), p. 60 | OK | For gamma = 1, u - t^2 d_x^2 u = f with u = mu_{0,t} * f. The source states it for f in D (Schwartz); the paper proves its version itself. | none |
| C136 | 05-matern.tex:1211 | §6 | MINOR | Supported by §6, p. 69; attributed there, not proved in the module. | `\S 6, p.~69` |
| C137 | 05-matern.tex:1535 | Thm. 4.2(3), p. 30 | LOCATOR | Clause (3) is on p. 31. It states d_t u <= 0 at local maxima for F = a w^2, so it supports the sentence. | `Thm.~4.2(3), p.~31` |
| C138 | 05-matern.tex:1544 | Thm. 4.2(3) and Cor. 4.4, pp. 30, 33 | LOCATOR | Thm 4.2(3) is on p. 31, Cor 4.4 on p. 33. Content right. Rem 4.15, p. 50, says the same. | `pp.~31, 33` |
| C148 | 07-discussion.tex:41 | §4 | OK | §4 selects line families by counting (Prop 4.5, Thm 4.10). | none |
| C152 | 07-discussion.tex:88 | §4 | OK | The counting statements are on the line. §6, p. 69, says they "would not carry over as they stand" to d >= 2. | none |
| C174 | supp-line.tex:2383 | Prop. 4.5(1), p. 35 | OK | F = a w^2 + sum log(1 + w^2/theta_i^2), sum theta_i^-2 < infinity, gives Pólya frequency kernels (iff). The paper's F_q has a = 0, theta_i = q^i/c. The restatement gives only the "if" direction, less than the source. | none |
| C175 | supp-line.tex:2420 | Remark 4.15 | MINOR | Rem 4.15, pp. 50-51: four readings, three nested classes. No page given. | `Remark~4.15, pp.~50--51` |
| C176 | supp-line.tex:2421 | Thm. 4.2(2), p. 30 | OK | Global-extrema non-enhancement for every admissible family, p. 30. | none |
| C177 | supp-line.tex:2423 | Prop. 4.5, p. 35 | OK | Endpoint counting holds for the Pólya frequency subclass (also Rem 4.15). | none |
| C178 | supp-line.tex:2424 | Thm. 4.2(3), Cor. 4.4 | MINOR | Supported. No page given. | `Thm.~4.2(3), Cor.~4.4, pp.~31, 33` |
| C179 | supp-line.tex:2425 | Thm. 4.10, p. 43 | OK | As C051. | none |
| C180 | supp-line.tex:2486 | Prop. 4.5(1), p. 35 | OK | As C174. | none |
| C181 | supp-line.tex:2493 | Prop. 4.5(2), p. 35 | OK | Clause (2) is applied at the signal u(s), which the paper shows is the primitive of the integrable mu_s * f'. Both inequalities match. | none |
| C182 | supp-line.tex:2506 | §6, p. 67 | LOCATOR | "The counting readings of §4 would not carry over as they stand" is on p. 69. | `\S~6, p.~69` |
| C184 | supp-line.tex:2617 | Remark 4.15 | MINOR | p. 51: Lindeberg's Thm 1 gives non-creation for a single kernel exactly when its coefficients form a Pólya frequency sequence; Thm 4 adds the semigroup law and leaves the discrete Gaussian alone. No page given. | `Remark~4.15, p.~51` |
| C186 | supp-line.tex:2644 | §4.3, pp. 34-35 | MINOR | Schoenberg's representation is at the foot of p. 34 into p. 35 (Karlin Ch. 7 Thm 3.2(a), p. 345). In the source gamma + sum a_j^2 > 0 and psi(0) = 1 appear only with the converse half (the sentence after (2.2), p. 336). The paper's thm:cited-A24 puts them in the forward direction; the proof here does not use them. | none required |
| X1 | blueprint/src/parts/02-line.tex:2030 | Thm. 3.3 (no page) | OK | Thm 3.3, p. 16: scale-locally generated iff F is a polynomial iff F = a w^2, a > 0. | `Thm.~3.3, p.~16` |
| X2 | blueprint/src/parts/02-line.tex:2033 | Prop. 3.8 (no page) | OK | Prop 3.8, p. 24: the Matérn family is jointly local of order 3, (1 - t^2 d_x^2) d_t u - 2 gamma t d_x^2 u = 0; clause (2): not of order at most 2. | `Prop.~3.8, p.~24` |

## Critical

None. No sentence is unsupported and no restatement claims more than the source.
