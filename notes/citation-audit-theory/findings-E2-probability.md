# Citation check, group E2-probability

Checker: a sonnet subagent that did not write the sentences, 2026-11-22. Its write was refused
("subagents return findings as text"); the session saved its returned table here unchanged.

Held copies:
- maejima1998semi: PTRF 112(1) 13-31 (Springer open access); printed = pdf + 12 (p. 19 = pdf 7).
- maejima1999semi: J. Theoret. Probab. 12(2) 347-373; printed = pdf + 346 (p. 361 = pdf 15).
- karlin1968total: Total Positivity Vol. 1, scan; printed = pdf - 12 (p. 345 = pdf 357). Page
  images read for pp. 333, 336, 344, 345.
- dlmf2026: no PDF held, only a Ch. 6 markdown file. 10.32.9 and 10.32.10 were read on
  dlmf.nist.gov/10.32, not from a held copy.
- schilling2012bernstein: 2nd edition; printed = pdf - 14 (p. 21 = pdf 35). `library search`
  reports offset 0 "via labels", but `page --printed N` resolves to the right pages.
- stein1970singular: PMS-30 scan; printed = pdf - 14 (p. 132 = pdf 146); image of p. 132 read.
- bondesson1992generalized: Springer 1992 scan; printed = pdf - 8 (p. 30 = pdf 38).
- kallenberg2021foundations: 3rd ed.; the page labels carry a FEFF prefix, so `--printed` fails;
  `--offset -3` works (p. 200 = pdf 203).

Counts over 22 rows: OK 17, MINOR 5, LOCATOR 0, UNSUPPORTED 0, HYPOTHESIS 0, UNREAD 0.

| id | where | key | locator | verdict | evidence | fix |
|----|-------|-----|---------|---------|----------|-----|
| C014 | 01-introduction.tex:190 | maejima1998semi | Def. 3.1, p. 19 | OK | Def 3.1 (p. 19): for 0<b<1, mu in L_0(b)=Q(P(R^d),b) is b-semi-selfdecomposable. | none |
| C057 | 02-cited-facts.tex:506 | karlin1968total | none | OK | PF function = f(x-y) totally positive of all orders; PF density = integrable PF normalised to integral 1 (Ch. 7 §1, p. 332). The paper's definition matches. | add Ch.~7, \S1, p.~332 |
| C062 | 02-cited-facts.tex:589 | karlin1968total | none | OK | Schoenberg's representation is Ch. 7 Thm 3.2, p. 345; right source. | optional: Ch.~7, Thm.~3.2, p.~345 |
| C063 | 02-cited-facts.tex:590 | dlmf2026 | none | OK | The K_nu integral representation is DLMF 10.32.9 and 10.32.10 (checked online); right source. | optional: 10.32.10 |
| C064 | 02-cited-facts.tex:592 | schilling2012bernstein | none | OK | Bernstein: Def 3.1 and Thm 3.2, p. 21. Complete Bernstein: Def 6.1, p. 69. Thorin-Bernstein: Def 8.1, p. 109. The paper's definitions of the last two match in content. | optional: Def.~6.1, p.~69 and Def.~8.1, p.~109 at the two definitions |
| C077 | 02-cited-facts.tex:832 | schilling2012bernstein | Thm. 3.2, p. 21 | OK | Thm 3.2 (p. 21): f is Bernstein iff f = a + b·lambda + ∫(1-e^{-lambda t}) mu(dt), a,b>=0, ∫(1∧t) mu(dt)<∞; triplet unique. Def 3.1 gives f>=0, C^∞, (-1)^{n-1}f^(n)>=0. The remark on p. 21: nonnegative f is Bernstein iff f' is completely monotone. All match. | none |
| C078 | 02-cited-facts.tex:860 | schilling2012bernstein | Thm. 1.4, p. 3 | OK | Thm 1.4 (Bernstein), p. 3: f completely monotone iff the Laplace transform of a unique measure on [0,∞). thm:cited-A55 drops uniqueness and the converse, so it claims less. | none |
| C079 | 02-cited-facts.tex:874 | schilling2012bernstein | Thm. 13.14, p. 212 | OK | Thm 13.14, p. 212: f:(0,∞)->[0,∞) is Bernstein iff f(\|xi\|^2) is continuous negative definite on R^d for all d; "sufficiency follows from Example 13.13", same page. The paper uses that direction. thm:cited-A57 adds f(0+)=0, narrower than the source. The "infinitely divisible law" part comes from Sato Thm 30.1 (group D). | none |
| C081 | 02-cited-facts.tex:894 | karlin1968total | Ch. 7, Thm. 3.2(a), p. 345 | OK | Thm 3.2(a), p. 345: a density on (-∞,∞) is PF iff the reciprocal of its Laplace transform is an entire function of class E_2^* with gamma + sum a_i^2 > 0. thm:cited-A24 matches hypothesis by hypothesis: gamma>=0, delta real, a_j real, sum a_j^2<∞, gamma+sum a_j^2>0, psi(0)=1. The factor s^k of (2.2) is k=0 because psi(0)=1. Karlin's sign convention is the paper's. The paper uses only necessity and only the imaginary axis, which is narrower. | none |
| C082 | 02-cited-facts.tex:895 | karlin1968total | (2.2), p. 336 | OK | (2.2), p. 336: class E_2 is psi(s)=e^{-gamma s^2+delta s} s^k ∏(1+a_i s)e^{-a_i s}, gamma>=0, delta real, a_i real, sum a_i^2<∞; E_2^* is psi(0)=1. | none |
| C083 | 02-cited-facts.tex:898 | karlin1968total | Prop. 1.4, p. 333 | MINOR | Prop 1.4 (p. 333): for a PF_2 density the Laplace transform "exists in an open strip containing the imaginary axis". It does not state "alpha<0<beta" or "absolutely"; both hold for a density but are the paper's gloss. The strip is Prop 1.4's, not part of Thm 3.2(a). | reword to the source's statement, or drop "absolutely" |
| C084 | 02-cited-facts.tex:920 | dlmf2026 | 10.32.9 | MINOR | 10.32.9: K_nu(z)=∫_0^∞ e^{-z cosh t} cosh(nu t) dt, \|ph z\|<pi/2, no condition on nu. The formula matches. DLMF does not define K_nu by it (the definition is 10.25(ii)); it is a representation. | "takes K_nu to be given by the integral of 10.32.9" |
| C085 | 02-cited-facts.tex:920 | dlmf2026 | 10.32.10 | OK | 10.32.10: K_nu(z)=(1/2)(z/2)^nu ∫_0^∞ exp(-t-z^2/(4t)) dt/t^{nu+1}, \|ph z\|<pi/4, no condition on nu. thm:cited-A51 matches, restricted to real z>0. | none |
| C091 | 03-pyramid.tex:403 | maejima1998semi | Def. 3.1, p. 19 | MINOR | Def 3.1 (p. 19) defines L_0(b)=Q(P(R^d),b). The explicit form mu^(z)=mu^(bz)rho^(z) with rho infinitely divisible is Thm 3.1(i), p. 20. Content right. | Def.~3.1, p.~19, and Thm.~3.1(i), p.~20 |
| C109 | 03-pyramid.tex:1556 | maejima1998semi | Rem. 3.1, p. 19 | MINOR | Rem 3.1 starts at the foot of p. 19 and ends on p. 20: Loève would call these laws b-decomposable, which "are not necessarily infinitely divisible". Supported. | Rem.~3.1, pp.~19--20 |
| C110 | 04-line.tex:190 | maejima1998semi | none | OK | Right source (Def 3.1, p. 19; Thm 3.1(i), p. 20). | optional: Def.~3.1, p.~19 |
| C118 | 05-matern.tex:81 | stein1970singular | Ch. V, §3.1, (26) and Prop. 2, p. 132 | OK | (26) defines G_alpha; Prop 2 (p. 132): G_alpha is in L^1 with integral 1 and Fourier transform (1+4pi^2\|x\|^2)^{-alpha/2}. J_alpha=(I-Delta)^{-alpha/2} is introduced on p. 131. Stein's convention differs by x→2pi x, which "read in this paper's convention" covers. (26) is in §3 on p. 132; §3.1 begins later. | Ch.~V, \S3, (26) and Prop.~2, p.~132 |
| C122 | 05-matern.tex:243 | dlmf2026 | none | OK | DLMF is the right source for K_1. | optional: DLMF 10.25(ii) |
| C133 | 05-matern.tex:941 | bondesson1992generalized | §3.1, p. 30 | MINOR | The GGC definition (mgf form, on [0,∞)) is on p. 29. P. 30: GGCs are exactly the weak limits of finite convolutions of Gamma laws, closed under shift, scale, convolution and weak limits. Supported. | §3.1, pp.~29--30 |
| C158 | supp-line.tex:194 | maejima1999semi | Thm. 7, p. 361 | OK | Thm 7 (p. 361): a>1, H>0; laws {mu_t, 1<=t<a} with (1) nondegenerate, (2) nonvanishing characteristic function, (3) mu_t=mu_s*mu_{s,t}, (4) weak continuity, (5) lim_{t->a} mu_t^(z)=mu_1^(a^H z). Then there is a unique-in-law nontrivial, stochastically continuous, H-semi-selfsimilar additive process with epoch a. | none |
| C163 | supp-line.tex:1182 | kallenberg2021foundations | Thm. 9.27, p. 200 | OK | Thm 9.27 (kernel densities), p. 200: for a probability kernel mu: S->T×U with T,U Borel, the ratios mu(s,dt×B)/mu(s,dt×U) have versions forming a probability kernel S×T->U. With S=T=R, U={0,1}, this gives the density of pi_r w.r.t. pi_r+eta, jointly measurable, in [0,1]. Borel hypotheses hold. | none |
| C185 | supp-line.tex:2643 | karlin1968total | Ch. 7, Thm. 3.2(a), p. 345 | OK | As C081. | none |

## Critical

None.

## The session's check

Group B (C186) read the selection paper's account and noted that `γ + Σa_j² > 0` and `ψ(0) = 1`
appear in Karlin only with the converse. The session read Karlin p. 345 as an image: Thm. 3.2(a)
is "a necessary and sufficient condition ... class E_2^* with γ + Σ a_i² > 0", so the condition is in
both directions and thm:cited-A24 is right as printed. C186 is OK.
