# Citation check, group A-isotropic

Checker: a sonnet subagent that did not write the sentences, 2026-11-22. Its write was refused
("subagents return findings as text"); the session saved its returned table here unchanged.

Held copies: fagerstrom2026isotropic: the released v0.1 (title page "October 14, 2026 (v0.1)",
doi 10.5281/zenodo.23357468); page offset 0, checked on pp. 1, 8, 10-17, 26-28. The library marks
the PDF `contested` because the item holds the paper and a supplement PDF; the paper is primary and
no page read was affected. Read as text: the cited statements are words and set inclusions.

Counts: OK 22, LOCATOR 1, HYPOTHESIS (minor, the paper claims less) 1, MINOR 4, UNSUPPORTED 0,
UNREAD 0.

| id | where | locator | verdict | evidence (printed page) | fix |
|----|-------|---------|---------|---------|-----|
| C008 | 01-introduction.tex:27 | Thm. 3.6, p. 13 | OK | Thm. 3.6 classifies the isotropic cascade families in R^d: transform exp(-(F(chi(t)abs xi) - F(chi(s)abs xi))), F in A_d, F not identically 0. | none |
| C027 | 02-cited-facts.tex:11 | none (attribution) | OK | The iso paper carries the axioms (Defs. 3.1, 3.2) and the classification (Thm. 3.6) to R^d. | none |
| C037 | 02-cited-facts.tex:251 | Def. 3.1, pp. 10-11 | OK | Def. 3.1 runs from (A1)-(A3) on p. 10 to (A4)-(A8), (ND) on p. 11; (A3) is rotation invariance. | none |
| C038 | 02-cited-facts.tex:252 | Lemma 3.3(1)-(2), p. 11 | LOCATOR | Clauses (1)-(2) match the restatement. The claim that the definitions describe the same families is clauses (3)-(4), p. 12. | "Lemma 3.3, pp. 11-12" |
| C039 | 02-cited-facts.tex:278 | Prop. 2.6, p. 8 | OK | Prop. 2.6(1): A_1 is the whole admissible cone and A_{d+1} is contained in A_d. | none |
| C040 | 02-cited-facts.tex:279 | Thm. 3.6, p. 13 | HYPOTHESIS (minor) | Everything matches except the uniqueness clause: the restatement requires F' in A_d, the source allows any real F' with F'(0)=0. The paper claims less. | optional: drop "F' in A_d" |
| C041 | 02-cited-facts.tex:299 | S 3.2, p. 12 | OK | The reduction to the line starts on p. 12; the subsection spans pp. 12-17. | none (pp. 12-13 would be exact) |
| C042 | 02-cited-facts.tex:301 | Lem. 3.8, p. 14 | OK | Every pair (chi, F), F in A_d, F not identically 0, is realised by an isotropic cascade family. | none |
| C043 | 02-cited-facts.tex:342 | Prop. 3.11(1)-(2), pp. 15-16 | OK | (1) on p. 15: self-decomposable exponent iff exponent of an origin datum. (2) on p. 16: F is admissible and A_d is the set of such F. | none |
| C054 | 02-cited-facts.tex:448 | Prop. 3.12, pp. 16-17 | OK | The bridge in R^d, with the Matern (2), stable (3) and Student-t (4) kernels. | none |
| C055 | 02-cited-facts.tex:450 | Prop. 3.22, p. 27 | OK | (1) the polar profile one dimension down is continuous; (2) A_{d+1} is strictly inside A_d for every d. | none |
| C058 | 02-cited-facts.tex:558 | Prop. 3.12(2), p. 16 | OK | Transform (1 + t^2 abs xi^2/2)^{-gamma}, so range t/sqrt2. | none |
| C086 | 03-pyramid.tex:88 | Def. 3.2, p. 11 | OK | (I3) is rotation invariance and (I4) is covariance with some bijection S_lambda. | none |
| C090 | 03-pyramid.tex:398 | Thm. 3.6, p. 13 | MINOR | Thm. 3.6 supports the exponents; the kernels claim is Cor. 3.9(1), p. 14, "other than delta_0". | add Cor. 3.9, p. 14, and "nondegenerate" |
| C094 | 03-pyramid.tex:605 | Thm. 3.6, p. 13 | OK | Family iff gauge chi and F in A_d with (3.1). F not identically 0 is automatic given (ND). The converse follows from (3.1) and S_lambda = chi^{-1}(lambda chi(.)). | none |
| C096 | 03-pyramid.tex:812 | S 3.2, p. 12 | OK | The marginal is the image under x -> <e,x>, the projection of tomography. Lemma 3.5 (p. 13): the marginals form a line family with the same S_lambda. | none |
| C097 | 03-pyramid.tex:855 | Thm. 3.6, p. 13 | OK | The proof applies Thm. 2.3 (A8 for every lambda) to the marginals. | none |
| C098 | 03-pyramid.tex:962 | Prop. 2.6, p. 8 | OK | A_{d+1} is contained in A_d. The jump-profile witness is Prop. 3.22(2), p. 27. | none |
| C099 | 03-pyramid.tex:963 | Prop. 3.22(2), p. 27 | OK | The step datum (0, b 1_(0,tau)) has exponent in A_d minus A_{d+1}, so A_{d+1} is strictly inside A_d for every d >= 1. | none |
| C104 | 03-pyramid.tex:1334 | Prop. 3.11(1)-(2), pp. 15-16 | OK | Clause (2) supplies admissibility, as the paper says. a_0 vs a is notation only. | none |
| C105 | 03-pyramid.tex:1354 | Lem. 3.8, p. 14 | OK | chi = id, F in A_d, F not identically 0 (checked by the paper) gives a fully covariant family. | none |
| C121 | 05-matern.tex:87 | Prop. 3.12(2), p. 16 | OK | gamma = 1 at t = sqrt2 r gives (1 + r^2 abs xi^2)^{-1}. | none |
| C123 | 05-matern.tex:380 | Prop. 3.11(1)-(2), p. 15 | MINOR | Clause (1) is on p. 15, clause (2) on p. 16. | "pp. 15-16" |
| C124 | 05-matern.tex:382 | Lem. 3.8, p. 14 | OK | Hypotheses F in A_d and F not identically 0 are met (b_d > 0). | none |
| C125 | 05-matern.tex:437 | Thm. 3.6, p. 13 | OK | Gauge chi is an increasing bijection (a homeomorphism). The pair is unique up to (chi, F) -> (c chi, F(c^{-1} .)). F(0)=0 and chi(0)=0 hold. | none |
| C127 | 05-matern.tex:568 | Prop. 3.11(1)-(2), p. 15 | MINOR | Same as C123. | "pp. 15-16" |
| C139 | 06-price.tex:205 | Def. 3.2, p. 11 | MINOR | (a) is (I1), (b) is (I2), (c) is (I4) at one ratio. The sentence's "two changes" omits (ND) and the fixed S_q t = qt. | say "three/four changes" or add "(ND) is not required; the relabelling is fixed" |
| C146 | 07-discussion.tex:36 | Thm. 3.6, p. 13 | OK | Thm. 3.6 classifies the fully covariant isotropic families, which stratum 2 is compared with. | none |

## Critical

None.
