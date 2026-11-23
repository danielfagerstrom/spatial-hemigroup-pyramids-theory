# Citation check, group E1-imaging

Checker: a sonnet subagent that did not write the sentences, 2026-11-22. Its write was refused
("subagents return findings as text"); the session saved its returned table here unchanged.

Held copies:
- burt1981fast: Burt, CVGIP 16:20-51 (1981), page scan. No Page Offset in `library` (default 0,
  wrong); printed = pdf + 19.
- burt1983laplacian: Burt-Adelson, IEEE Trans. Commun. COM-31(4) 532-540, scan; printed = pdf + 531.
- meer1987frequency: PAMI-9(4) 512-522, offset 511 (correct).
- lindeberg1990scalespace: the held PDF is the 32-page CVAP report version of "Scale-space for
  discrete signals" (own pagination, offset 0), not the journal pagination (234-254). Theorem 4
  p. 13, Prop. 12 p. 16, Thm 6 p. 16 in the report. Journal numbering not compared.
- lindeberg2016time: JMIV 55:50-88, printed labels correct (offset 0).
- mallat1989theory: PAMI-11(7), p. 676 = pdf 3 (offset 673).
- hanke1998nonstationary: JOTA 98(1) 37-53 headers (offset 36); the Extra field "preprint" is stale.
- radmoser2000scale: JVCIR 11:96-114, offset 95.
- farbman2008edge: ACM TOG 27(3), art. 67, offset 0.
- kovacevic1992nonseparable: journal scan, IEEE Trans. IT 38(2) 533-555, no text layer;
  printed = pdf + 532.
- watson1989hexagonal: IEEE TBME 36(1) 97-106, labels correct.
- collatz1960numerical: book scan; `--printed` fails; printed = pdf − 16 (pdf 402 = p. 386).
- lindgren2011explicit: the journal version (JRSSB 73(4) 423-498, offset 422); eq. (1) and (2)
  both on p. 426; Extra field "preprint" is stale; an alternate item `lindgren2011.pdf` is
  contested.
- whittle1954stationary: Biometrika 41, offset 433.

Counts over 51 rows: OK 43, MINOR 8, LOCATOR 0, UNSUPPORTED 0, HYPOTHESIS 0, UNREAD 0.

Burt's constraints and weights were checked on the page images: Burt 1981 p. 24 gives
1/4 ≤ a ≤ 1/2, b = 1/4, c = 1/4 − a/2, and equal contribution is (C4) on p. 23, so the supplement's
argument (a + 2b + 2c = 1 and a + 2c = 2b give 4b = 1) is right; the binomial 1/16[1,4,6,4,1] has
a = 3/8. Collatz p. 386 was read as an image: the Hermitian formula
4u_a − Σu_b + h²r_a = D[u] + O(h⁶), D[u] = (1/6)(Σu_c − 2Σu_b + 4u_a) − (h²/12)(Σr_b − 4r_a), gives
the weights (−20, 4, 1)/6h².

| id | where | key | locator | verdict | evidence | fix |
|----|-------|-----|---------|---------|----------|-----|
| C001 | 01-introduction.tex:8 | burt1981fast | none | OK | HDC of order r (r=2 example), levels p.21 (1); reduced HDC (decimation) Sect. 4, p.29 | none (optional p.21, Sect. 4) |
| C002 | 01-introduction.tex:8 | burt1983laplacian | none | OK | p.533 REDUCE (1), node spacing doubles per level | none |
| C003 | 01-introduction.tex:10 | burt1983laplacian | p. 533 | OK | p.533: w separable, normalized, symmetric, equal contribution (all four) | none |
| C004 | 01-introduction.tex:11 | meer1987frequency | none | OK | one decimation by 2, ideal low-pass target, antialiasing index pp.512-514 | optional pp.512-514 |
| C005 | 01-introduction.tex:12 | burt1981fast | none | OK | Obs. 1 p.24: rescaled equivalent kernel converges to a characteristic form | optional Obs. 1, p.24 |
| C006 | 01-introduction.tex:19 | lindeberg1990scalespace | none | OK | Thm 4 (report p.13): semigroup T(.;s)*T(.;t)=T(.;s+t) gives e^{-αt}I_n(αt) | optional Thm 4 |
| C010 | 01-introduction.tex:185 | hanke1998nonstationary | pp. 38-39 | OK | p.38 geometric choice α_n = α q^(n−1); p.39 iteration (5) with (T*T+α_n I)^{-1}; step ~1/α_n grows geometrically | none |
| C011 | 01-introduction.tex:186 | radmoser2000scale | none | OK | p.98 parameter read as diffusion time, single implicit time step; Sect. 4 varying parameters | add p.98 |
| C012 | 01-introduction.tex:186 | farbman2008edge | none | OK | Sect. 3.1 p.4 (13)-(14): λ multiplied by c per level, F_λ inverse of sparse matrix; no downsampling | add Sect. 3.1, (13)-(14), p.4 |
| C013 | 01-introduction.tex:188 | burt1981fast | none | OK | Sect. 4 "Reduced HDC" p.29: sample count reduced by r per level | add Sect. 4, p.29 |
| C016 | 01-introduction.tex:191 | mallat1989theory | none | OK | p.676 (2)-(8) nested dyadic subspaces, orthogonal projections | optional (2)-(8), p.676 |
| C017 | 01-introduction.tex:193 | lindeberg1990scalespace | none | OK | right source for discrete scale space e^{-t}I_n(t), Thm 4 p.13; the stratum claim is the paper's | none |
| C018 | 01-introduction.tex:195 | whittle1954stationary | none | MINOR | Whittle: plane only, index 1, p.448 (64)-(68), κrK_1(κr); not general γ, d. The printed "(2)" is Lindgren's, which carries general d and index | optional p.448; general index is Lindgren |
| C019 | 01-introduction.tex:195 | lindgren2011explicit | (2) | OK | p.426: (1) Matérn covariance; (2) (κ²−Δ)^{α/2}x = W, α = ν + d/2 | add (1)-(2), p.426 |
| C095 | 03-pyramid.tex:712 | lindeberg1990scalespace | none | OK | (19) p.13, generator (28) p.16; the d>=2 axis-neighbour family = separable member of the report's Sect. 9 (pp.24-25) | optional Thm 4, (19); Sect. 9 |
| C100 | 03-pyramid.tex:1114 | burt1981fast | (2)-(4), pp. 21-23 | OK | (2) p.21 equivalent kernel h_l; (3) p.23 h_l = w convolved with dilates; (4) p.23 M_l | none |
| C101 | 03-pyramid.tex:1116 | burt1983laplacian | p. 533 | OK | "Equivalent Weighting Functions" heading, g_l = h_l ⊕ g_0 | none |
| C102 | 03-pyramid.tex:1119 | burt1981fast | Obs. 1, p. 24, and (5), p. 25 | OK | Obs. 1 p.24, ĥ_l = 2^l h_l(2^l x); p.25 "characteristic kernel", (5) sup bound m/(r^{l+1}(r−1)) | none |
| C106 | 03-pyramid.tex:1459 | burt1983laplacian | p. 533 | OK | separable w(m,n)=ŵ(m)ŵ(n), same pattern at every level | none |
| C107 | 03-pyramid.tex:1461 | burt1981fast | p. 24 | OK | five-tap family 1/4 ≤ a ≤ 1/2, b = 1/4, c = 1/4 − a/2; binomial has a = 3/8 | none |
| C108 | 03-pyramid.tex:1492 | burt1981fast | Obs. 1, p. 24 | OK | as C102 | none |
| C111 | 04-line.tex:208 | lindeberg1990scalespace | none | OK | e^{-t}I_n(t), symbol exp(t(cos hω − 1)), compound Poisson on {±h}; matches (19), (28) | none |
| C113 | 04-line.tex:533 | burt1983laplacian | p. 533 | OK | p.533 equivalent weighting functions; the product of dilates is Burt 1981 (3) p.23 | optionally add burt1981fast (3), p.23 |
| C115 | 04-line.tex:992 | lindeberg1990scalespace | Prop. 12 and the sentence after it | MINOR | report p.16 Prop. 12: sampled-Gaussian transition is a scale-space iff t_1 = 0 or t_2/t_1 an odd integer; next sentence: the semigroup property of the Gaussian is not preserved after discretization. The held copy is the report; journal numbering unverified | check the journal's numbering |
| C119 | 05-matern.tex:85 | whittle1954stationary | none | MINOR | as C018 | as C018 |
| C120 | 05-matern.tex:85 | lindgren2011explicit | (2) | OK | as C019, p.426 | add p.426 |
| C129 | 05-matern.tex:616 | lindeberg2016time | Sect. 5, (38), p. 62 | OK | Sect. 5 starts p.61; (38) p.62: ∏_{k≥1} 1/(1 + i c^{-k}√(c²−1)√τ ω); c = q², κ = 2c² is the paper's reading | none |
| C130 | 05-matern.tex:617 | lindeberg2016time | Sect. 6.2, p. 64 | OK | Sect. 6.2 starts p.64, first-order recursive filters | none |
| C135 | 05-matern.tex:1141 | burt1983laplacian | p. 535 | OK | p.535 L_l = g_l − EXPAND(g_{l+1}), "similar to convolving an appropriately scaled Laplacian" | none |
| C140 | 06-price.tex:431 | burt1983laplacian | p. 533 | OK | as C101 | none |
| C141 | 06-price.tex:1460 | whittle1954stationary | none | MINOR | Whittle only the plane, index 1; general d, γ > d/2 with smoothness γ − d/2 is Lindgren (2) | as C018 |
| C142 | 06-price.tex:1460 | lindgren2011explicit | (2) | OK | ν = α − d/2 > 0 iff γ > d/2, p.426 | add p.426 |
| C143 | 06-price.tex:1484 | collatz1960numerical | Ch. V § 2.5, p. 386 | OK | image p.386 (§2.5 runs from p.384); weights (−20,4,1)/6h², r-terms are the correction | none |
| C144 | 07-discussion.tex:7 | burt1983laplacian | p. 533 | OK | generating kernel chosen subject to constraints on the mask | none |
| C145 | 07-discussion.tex:7 | meer1987frequency | none | OK | kernels judged by frequency-response indices pp.512-514 | none |
| C147 | 07-discussion.tex:37 | lindeberg1990scalespace | none | OK | as C006/C017 | none |
| C149 | 07-discussion.tex:48 | burt1983laplacian | none | OK | p.535 Laplacian pyramid level differences | add p.535 |
| C150 | 07-discussion.tex:52 | hanke1998nonstationary | pp. 38-39 | OK | as C010 | none |
| C151 | 07-discussion.tex:72 | burt1983laplacian | p. 533 | MINOR | p.533 w(±2) = 1/4 − a/2 (negative for a > 1/2); the negative lobes at a = 0.6 are stated on p.534 (Fig. 3) | pp. 533-534 |
| C153 | 07-discussion.tex:102 | kovacevic1992nonseparable | none | MINOR | filter banks and wavelets; quincunx D_1 = [[1,1],[1,−1]], D_1² = 2I, p.534 eq. (2); no "pyramid" | add Sect. I, (2), p.534; say "quincunx filter bank" |
| C154 | 07-discussion.tex:103 | watson1989hexagonal | none | OK | p.97, p.99: seven weights (point + six neighbours), spacing √7, rotated 19.1° | optional pp.97, 99 |
| C164 | supp-line.tex:2098 | burt1981fast | pp. 23-24 | OK | p.23 (C1), (C4); p.24 a + 2b + 2c = 1, a + 2c = 2b ⇒ b = 1/4 | none |
| C165 | supp-line.tex:2109 | burt1983laplacian | p. 533 | OK | equal contribution: same total weight (1/4 in 2D) to the next level | none |
| C167 | supp-line.tex:2113 | burt1983laplacian | p. 533 | MINOR | the Gaussian-like equivalent weighting function is p.534 (Fig. 2, a = 0.4; triangular at 0.5); p.533 says only that a member of the family resembles a Gaussian | pp. 533-534 |
| C171 | supp-line.tex:2353 | burt1983laplacian | none | OK | right source for the Laplacian pyramid (p.535) | add p.535 |
| C172 | supp-line.tex:2362 | lindeberg2016time | Sect. 5, (38), p. 62 | OK | as C129 | none |
| C173 | supp-line.tex:2363 | lindeberg2016time | Sect. 6.2, p. 64 | OK | as C130 | none |
| C183 | supp-line.tex:2616 | lindeberg1990scalespace | none | MINOR | Thm 4 (report p.13): symmetric, normalized, semigroup, non-increasing extrema ⇒ e^{-αt}I_n(αt), α ≥ 0; the sentence omits symmetry, normalization and α | add Thm 4 and the hypotheses |
| C187 | supp-line.tex:2669 | mallat1989theory | (2)-(8), p. 676 | OK | all of (2)-(8) on p.676 | none |
| C188 | supp-line.tex:2684 | meer1987frequency | none | OK | one reduction by 2, antialiasing index p.513, filtering index p.514 | optional pp.513-514 |
| C193 | supp-strata.tex:298 | lindeberg1990scalespace | none | OK | (19) p.13, generator (28) Thm 6 p.16, symbol e^{-t(1−cos hω)}; α = 1 | optional (19), Thm 6 |

## Critical

None.
