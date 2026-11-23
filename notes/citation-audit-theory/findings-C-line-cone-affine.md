# Citation check, group C-line-cone-affine

Checker: a sonnet subagent that did not write the sentences, 2026-11-22. Its write was refused
("subagents return findings as text"); the session saved its returned table here unchanged.

Held copies (read as text through `library get --pages`; page offset 0 for all three):
- `fagerstrom2026spatial`: title page "September 15, 2026 (v0.1)", 49 pp., the released v0.1.
- `fagerstrom2026cone`: title page "September 20, 2026 (v0.1)", 89 pp., the released v0.1.
- `fagerstrom2026affine`: title page "November 4, 2026 (v0.1)", 116 pp., the released v0.1.

The extracted text is clean; no page image was opened. The displays that matter (cone (6.2),
Prop. 6.4, Prop. 7.5, Prop. 5.7 (5.1)) were compared sign by sign with the restatements and agree.

Counts over 39 rows: OK 34, MINOR 5 (C020, C034, C112, C128, C155), LOCATOR 0, UNSUPPORTED 0,
HYPOTHESIS 0, UNREAD 0.

| id | where | key | locator | verdict | evidence | fix |
|---|---|---|---|---|---|---|
| C007 | 01-intro:26 | spatial | Thm. 7.3, p. 37 | OK | Thm 7.3, p. 37: (A1)-(A8)+(ND) hold iff there are a gauge chi and F of form (2.3), F≢0, with kernel transform exp(-[F(chi(t)w)-F(chi(s)w)]). | none |
| C020 | 01-intro:245 | spatial | attribution | MINOR | The held line paper (p. 49, "Where to look") pins ScaleSpaceCore at v0.2.0, not v0.5.0; v0.5.0 is the tag the affine paper pins. Neither held paper says the library supplies "the Bessel function K_nu". The affine paper says ScaleSpaceCore "makes no assumption of its own", consistent with "declares no axiom". | Say ScaleSpaceCore is the line paper's shared core, pinned here at v0.5.0; check the K_nu and classification content against the library itself. |
| C021 | 01-intro:250 | affine | attribution | OK | The affine paper has a Lean development at tag v0.1, namespace AffineHemigroup, on ScaleSpaceCore v0.5.0. | none |
| C024 | 02-cited:6 | spatial | attribution | OK | The line paper states the axioms (p. 17) and classifies the families (Thm 7.3, p. 37). | none |
| C025 | 02-cited:8 | cone | attribution | OK | Convex cone (Lemma 2.7, p. 12), extreme rays and Cin generators (Lemma 3.1, Prop. 3.3), implementation on the line (§7). | none |
| C028 | 02-cited:12 | affine | attribution | OK | Frame families are Prop. F.1, p. 93. | optional locator "Prop. F.1, p. 93" |
| C029 | 02-cited:64 | spatial | Lemma 4.1, pp. 22–23 | OK | Lemma 4.1 starts p. 22 and finishes p. 23: unique probability measure under (A1),(A2),(A4),(A5); symmetric under (A3); converse. | none |
| C030 | 02-cited:81 | spatial | Lemma 4.1, p. 22 | OK | Existence and uniqueness are on p. 22; symmetry and converse on p. 23. The restatement cited-A1 matches. | none |
| C031 | 02-cited:113 | spatial | Thm. 5.2, p. 26 | OK | Under (A1)-(A7), g = a w^2 + ∫(1-cos wx) nu(dx), ∫(1∧x^2) nu < ∞, a ≥ 0, pair unique; every kernel is infinitely divisible. | none |
| C032 | 02-cited:118 | spatial | Prop. 2.3(3), p. 9 | OK | Symmetric Lévy–Khintchine (2.2), pair (a, nu) unique. | none |
| C034 | 02-cited:187 | spatial | Prop. 2.13, p. 13 | MINOR | Prop. 2.13, p. 13: a symmetric infinitely divisible law is self-decomposable iff nu = k(x)/x dx with k ≥ 0 nonincreasing, giving (2.3). The statement agrees. The source says the proposition is "stated for orientation: it lies on no proof path"; the proved form is Lemma 7.1, pp. 33–34. | optionally add "Lemma 7.1, pp. 33–34" |
| C035 | 02-cited:189 | spatial | Thm. 7.3, p. 37 | OK | The restatement cited-A4 (iff, gauge, F≢0, unique once chi(1)=1, converse) matches p. 37 and the converse proof on p. 38. | none |
| C036 | 02-cited:215 | cone | Lemma 2.7, p. 12 | OK | F1+F2 and cF1 are admissible with data (a1+a2, k1+k2) and (c·a1, c·k1): a convex cone. Matérn data (a=0, k=2γe^{-x}) is Prop. 5.2(1), p. 43. | none |
| C044 | 02-cited:407 | cone | Prop. 6.2, (6.2), p. 56 | OK | A_t g = 2at g'' − t^{-1}∫[g − ½(g(x−tv)+g(x+tv))] varpi(dv), varpi = −dk, f in D = S(R) (Def. 6.1), canonical gauge. Equals the paper's H_t with delta^2_h. | none |
| C045 | 02-cited:410 | cone | Lemma 3.1(1), p. 13 | OK | The profile 1_(0,tau) is admissible, a = 0, exponent Cin(tau w). | none |
| C046 | 02-cited:411 | cone | Prop. 6.4(5), p. 58 | OK | The Cin ray has A_t = t^{-1} delta^2_{t tau}, a single symmetric second difference. | none |
| C047 | 02-cited:437 | spatial | Remark 6.7, pp. 32–33 | OK | Remark 6.7 (gauge freedom) starts p. 32 and ends p. 33. | none |
| C048 | 02-cited:438 | cone | §4, p. 24 | OK | §4 "The subordination bridge" begins p. 24. | none |
| C049 | 02-cited:440 | cone | Prop. 5.7, p. 48 | OK | k completely monotone iff the symmetric Thorin representation (5.1). | none |
| C056 | 02-cited:452 | affine | Prop. F.1, p. 93 | OK | Frame families: (1) cascade and covariance, (2) Gaussian frame, (3) only the Gaussian loses its frame; statement complete on p. 93. | none |
| C059 | 02-cited:560 | cone | Prop. 5.2(2), p. 43 | OK | e^{-F(tw)} = (1+t^2w^2)^{-γ}, the law at range t. | none |
| C089 | 03-pyramid:397 | spatial | Thm. 7.3, p. 37 | OK | Thm 7.3 gives F of form (2.3). Prop. 2.13 / Lemma 7.1 identify (2.3) with the symmetric self-decomposable exponents. The line paper's §8 and abstract state "exactly the symmetric self-decomposable laws" citing Thm 7.3. | optional "with Prop. 2.13, p. 13" |
| C112 | 04-line:271 | cone | Prop. 7.5(2), p. 65 | MINOR | Locator and use are right. The source says F is admissible "exactly when this k is nonincreasing"; the restatement cited-A20 says "has a nonincreasing version (k_R fixed only up to a null set)". A refinement, not a stronger claim. | none needed |
| C114 | 04-line:570 | cone | Prop. 7.2, p. 60 | OK | Prop. 7.2 opens p. 60 and ends p. 61 (integer γ, forward–backward sections, γ=1 four-term mixture). cited-A19 matches. | use "pp. 60–61", as at 02-cited:452 |
| C116 | 04-line:1020 | cone | attribution | OK | The cone module holds the generator (Prop. 6.2, 6.4) and the interpolation criterion (Prop. 7.5(2)). | none |
| C117 | 04-line:1023 | cone | Lemma 3.1(1), p. 13 | OK | Cin ray with exponent Cin(tau w). | none |
| C128 | 05-matern:610 | cone | §4 | MINOR | The substitution Psi(w)=F_I(w^2/2), i.e. sigma = w^2/2, is in §4.2 and Lemma 4.2, p. 26. The locator carries no page. | "§4.2, p. 26 (Lemma 4.2)" |
| C155 | appendix-verif:22 | spatial | attribution | MINOR | As C020: the line paper pins v0.2.0. | as C020 |
| C156 | appendix-verif:23 | affine | attribution | OK | The export namespace AffineHemigroup, tag v0.1. | none |
| C157 | supp-line:131 | spatial | Remark 6.7, pp. 32–33 | OK | See C047. | none |
| C159 | supp-line:240 | spatial | Thm. 7.3, p. 37 | OK | Applied to a family with (A1)-(A8),(ND); Psi_t = F'(chi(t)\|.\|). | none |
| C160 | supp-line:682 | cone | Prop. 6.4(5), p. 58 | OK | See C046. | none |
| C161 | supp-line:849 | cone | Prop. 3.3, pp. 15–16 | OK | The statement starts at the foot of p. 15 and runs to p. 16: the extreme rays are the Gaussian ray and the Cin rays. | none |
| C166 | supp-line:2111 | affine | Prop. F.1, p. 93 | OK | Frame family mu_A = A_*(product of 1-D hemigroups); A=I is the separable tensor-product case. | none |
| C168 | supp-line:2244 | spatial | Thm. 7.3, p. 37 | OK | The converse (proof on p. 38) gives (A1)-(A8),(ND) with S_lambda t = lambda t. | none |
| C169 | supp-line:2349 | cone | Prop. 5.7, (5.1), p. 48 | OK | F = a w^2 + ½∫log(1+w^2/theta^2)U(dtheta). With U = Σ 2δ_{q^i/c} this gives Σ log(1+c^2 q^{-2i} w^2); normalization checked. | none |
| C170 | supp-line:2350 | cone | Prop. 6.4(4), p. 58 | OK | A_t = t^{-1}∫(Lap_{t/theta} − I)U(dtheta) for a=0, g in C^2 with g, g'' bounded; the paper's stated scope is the source's. | none |
| C191 | supp-strata:226 | spatial | Prop. 2.3(3), p. 9 | OK | Uniqueness of the pair (a, nu). | none |
| C192 | supp-strata:257 | spatial | Prop. 2.3(3), p. 9 | OK | Same uniqueness, used to read off a'(t) = alpha t^2 and varpi'_t(dv) = k(v/t) v^{-1} dv. | none |

## Critical

None.
