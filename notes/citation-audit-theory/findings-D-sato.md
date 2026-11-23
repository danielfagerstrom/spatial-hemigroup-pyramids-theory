# Citation check, group D-sato

Checker: a sonnet subagent that did not write the sentences, 2026-11-22. Its write was refused
("subagents return findings as text"); the session saved its returned table here unchanged.

Held copies: sato1999levy: the scanned book (Cambridge Studies in Advanced Mathematics 68, 1st ed.
1999). `library page --printed N` returns the right page; printed N is PDF N+14 in the body. Every
cited page was read as an image (the text layer is poor OCR, and nothing rests on it).

Counts over 29 rows: OK 24, MINOR 4, LOCATOR 1, UNSUPPORTED 0, HYPOTHESIS 0, UNREAD 0.

| id | where | locator | verdict | evidence (printed page) | fix |
|---|---|---|---|---|---|
| C015 | 01-introduction.tex:190 | Def. 15.1, p. 90 | OK | Semi-selfdecomposable: some b>1 and some infinitely divisible rho_b with mu^(z)=mu^(b^-1 z)rho_b^(z); "span" defined there. | none |
| C022 | 01-introduction.tex:257 | none | OK | The attribution list (Lévy–Khintchine, Khintchine, linear image, (semi-)selfdecomposability, polar form, supports, g-moment) is all in Sato. | none |
| C033 | 02-cited-facts.tex:162 | Def. 15.1, p. 90 | OK | As C015. | none |
| C060 | 02-cited-facts.tex:565 | none | MINOR | Sato defines T_r, (T_r rho)(B)=rho(r^-1 B), in (13.8), p. 75, for measures on R^d. Same formula as the paper's. | Add locator `(13.8), p.~75`. |
| C061 | 02-cited-facts.tex:588 | none | OK | Right source for the Lévy–Khintchine theory. | none |
| C065 | 02-cited-facts.tex:604 | Thm. 8.1(i)–(iii), pp. 37–38 | OK | Thm 8.1 starts on p. 37 with (i), (8.1), (8.2); (ii), (iii) and "gamma in R^d" are on p. 38. A39 checked against it: the formula, A symmetric nonnegative-definite, nu({0})=0, int(|x|^2 ^ 1)dnu<inf, uniqueness and the converse all match. The factor 2 between the paper's Gaussian part and Sato's A is right (Sato has 1/2<z,Az>). | none |
| C066 | 02-cited-facts.tex:605 | Def. 8.2, p. 38 | OK | Generating triplet, Gaussian covariance matrix, Lévy measure. | none |
| C067 | 02-cited-facts.tex:630 | Lemma 7.5, p. 32 | OK | An infinitely divisible mu has mu^(z)≠0. A40 identical. | none |
| C068 | 02-cited-facts.tex:642 | Thm. 9.3, p. 47 | OK | Def. 9.2 (null array) and Thm 9.3 are both on p. 47. A41 identical. | none |
| C069 | 02-cited-facts.tex:658 | Prop. 11.10, p. 65 | OK | A_U=UAU', nu_U=[nu U^-1] restricted to R^n\{0}, gamma_U=U gamma+int Ux(1_E(Ux)-1_D(x))nu(dx), stated for a Lévy process. A42 matches term by term. The paper's sentence already says it is read at time 1. | none |
| C070 | 02-cited-facts.tex:677 | Prop. 15.5, p. 93 | OK | Selfdecomposable gives infinitely divisible with rho_b unique and infinitely divisible. Semi-selfdecomposable gives infinitely divisible with rho_b unique. The sentence after the proof says selfdecomposable gives semi-selfdecomposable for every span. A43 matches all four clauses. | none |
| C071 | 02-cited-facts.tex:678 | Thm. 15.8, p. 94 | OK | Fix b>1; mu infinitely divisible with triplet (A,nu,gamma); span b iff T_b nu >= nu (15.6); no restriction on A, gamma. A44 identical (D_b = T_b). | none |
| C072 | 02-cited-facts.tex:753 | Thm. 15.10, p. 95 | OK | Polar form with lambda finite on S and k_xi(r) measurable in xi and "decreasing in r"; no restriction on A, gamma. The paper's "nonincreasing" is Sato's wide-sense "decreasing", as in Example 15.9 and Cor. 15.11. | none |
| C073 | 02-cited-facts.tex:770 | Cor. 24.4, p. 149 | OK | Infinitely divisible and not a point mass gives unbounded support. A46 identical. | none |
| C074 | 02-cited-facts.tex:771 | Cor. 24.6, p. 149 | OK | In d=1, S_mu in Z iff A=0, S_nu in Z and gamma_0 in Z. The proof shows nu(R)<inf and the last line states it. A48 claims less (omits gamma_0 in Z). | none |
| C075 | 02-cited-facts.tex:791 | Thm. 25.3, p. 159 | MINOR | Def. 25.1 and 25.2 and Thm 25.3 are on p. 159. Sato states it for a Lévy process: finite g-moment of X_t for every t>0 iff [nu]_{|x|>1} has finite g-moment, "not a time dependent" property. The paper's A49, for an infinitely divisible mu, follows by reading at t=1, but the sentence does not say so (unlike C069). Hypotheses on g match. | Add "printed there for a Lévy process, read here for its law at time 1". |
| C076 | 02-cited-facts.tex:806 | Prop. 25.4(iii), p. 159 | OK | The list includes log(|x| v e). The paper's own proof (u+v<=uv; g(x+y)<=g(x)+g(y)<=2g(x)g(y)) is correct. | none |
| C080 | 02-cited-facts.tex:877 | Thm. 30.1, pp. 197–198 | OK | The theorem starts on p. 197 (subordinator) and continues on p. 198 (Y_t=X_{Z_t} is a Lévy process, (30.5)–(30.9)). The range covers it. A Lévy process is infinitely divisible at each time (Example 7.3, p. 32). | none |
| C087 | 03-pyramid.tex:209 | Thm. 8.1, pp. 37–38 | LOCATOR | Thm 8.1 gives the representation and does not read the Lévy measure as a jump rate. That is Thm 19.2(i), p. 120: the jump counting measure is a Poisson random measure with intensity nu~((0,t]xB)=nu_t(B). | `Thm.~19.2(i), p.~120`. |
| C088 | 03-pyramid.tex:393 | Def. 15.1, p. 90 | OK | With c=1/b, "for every 0<c<1 the law of cX+Y" is the same as Sato's definition. | none |
| C092 | 03-pyramid.tex:412 | Prop. 15.5, p. 93 | MINOR | The proposition does not state "self-decomposable is semi-selfdecomposable for every span". That is the sentence after the proof, p. 93. | `Prop.~15.5 and the sentence after it, p.~93` (as at C070). |
| C093 | 03-pyramid.tex:416 | Thm. 15.8, p. 94 | OK | As C071; "does not impose any restriction on A and gamma". | none |
| C103 | 03-pyramid.tex:1261 | Prop. 25.4(iii), p. 159 | OK | log(|x| v e) is submultiplicative. Continuity and hence local boundedness are the paper's own remark. | none |
| C131 | 05-matern.tex:815 | Thm. 8.1(ii), p. 38 | OK | Uniqueness of the representation. | none |
| C132 | 05-matern.tex:829 | Thm. 8.1(iii), p. 38 | OK | Existence of an infinitely divisible law with a given triplet. The cross-reference to 8.1(ii), same page, is right. | none |
| C162 | supp-line.tex:994 | Prop. 15.5, p. 93 | OK | Semi-selfdecomposable gives infinitely divisible, in any dimension, so d=1 is covered. | none |
| C189 | supp-strata.tex:47 | Thm. 8.1(iii), pp. 37–38 | MINOR | Part (iii) is stated on p. 38 only. The use (existence of the law with the triplet) is exactly (iii). | `p.~38`. |
| C190 | supp-strata.tex:49 | Thm. 8.1(ii), p. 38 | OK | Uniqueness of the triplet. Applying it to the law and its reflection is the paper's own step (reflection has triplet (A,nu(-.),-gamma), by Prop. 11.10 with U=-1). | none |
| C194 | supp-strata.tex:347 | Thm. 15.8, p. 94 | OK | The criterion applies to m_t with triplet (0,t sigma,0). T_q(t sigma) puts mass 0 on |x|=h (atoms move to |x|=qh), so T_q(t sigma) >= t sigma fails. The computation is correct. | none |

## Critical

None. The Section 2 restatements attributed to Sato (A39-A46, A48, A49) were compared with the page
images hypothesis by hypothesis; none drops a hypothesis, strengthens a conclusion, or changes a
constant or range. Sato states A42 and A49 for Lévy processes; both are read at time 1 (Example 7.3,
p. 32), and only A42's sentence says so.
