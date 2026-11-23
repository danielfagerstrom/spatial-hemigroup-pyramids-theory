# The axiom ledger

This module's **trust boundary**: the mathematics it cites rather than proves. Every `[A]` node of
the blueprint names its entries here with `\ledger{A<N>}`, and every entry carries a page-anchored
citation into a held source. The page was read from the page image by the librarian, and the
source's wording is transcribed in `AXIOMS-verbatim.md`, one section per entry (LINKAGE.md rule 5),
copied from the transcription records `records/pyramids/VERBATIM-V-line.md`, `VERBATIM-V-cone.md`,
`VERBATIM-selection-iso-affine.md`, `VERBATIM-Sato.md` and `VERBATIM-literature.md`. Each entry
states the source's verdict there (MATCH, NARROWER-OK, MISMATCH) and what the statement as used
does with it.

**The Lean axioms: seven entries, by the author's decision of 2026-11-13.** The author admitted
A39, A40, A41, A42, A46, A48 and A51 as Lean axioms, and nothing else. Each of the seven has a
`**Lean:**` line naming its declarations in `Formalization/Pyramids/Cited/A<N>.lean`, and its
interface node is `\leanok` on them. Admitting an entry did not always mean declaring an axiom:

- A42, A46 and A48 were declared as axioms of this module (`cited_A42`, `cited_A46`,
  `cited_A48`). Since review round 3 (batch C, 2026-11-23) `cited_A42` is a theorem with no axiom,
  and `cited_A48` admits the corollary's statement only, the finiteness of $\nu$ being proved
  (their **Lean:** lines). A51 is proved from the definition of `besselK` with no axiom; its former clause
  (2), five further DLMF equations admitted as `cited_A51_evaluations`, was dropped the same day,
  by the author's decision, as no node read it.
- A39 and A41 are already axioms of the affine export, which this development requires, for the
  same theorems of Sato at the same pages (its ledger A3 and A6). They are not declared again: the
  interface nodes' declarations are proved from the export's axioms `levy_khintchine_exists`,
  `levy_khintchine_unique`, `levy_khintchine_converse` and `khintchine_null_array`, and those four
  names are listed in `trust-boundary.txt` on the grounds of the entries A39 and A41 below.
- A40 is proved from A39(i), and clause (1) of A51 from the definition of the shared core's
  `besselK` (DLMF 10.32.9), with no axiom.

**Seven more entries, by the author's decision of 2026-11-14.** The author admitted A31, A34, A35,
A43, A45, A49 and A50 as Lean axioms. Each has a `**Lean:**` line, and its interface node is
`\leanok` on the declarations of `Formalization/Pyramids/Cited/A<N>.lean`:

- A31, A34 and A35 are theorems of the affine export (its `isotropic_classification`,
  `isotropic_classification_unique`, `isotropic_realisation`, `polar_reading`,
  `polar_reading_unique`, `polar_reading_admissible`, `classA_iff_originDatum`), which proves the
  isotropic paper's statements on its own ledger. They declare no axiom here; they reach A39's
  names, and A35 also the two names below for A43 and A45. A34 reaches none.
- A45 is the affine export's axiom `sato_polar_criterion` (its ledger A2, Sato Thm. 15.10), and the
  first clause of A43 its axiom `selfDecomposable_infinitelyDivisible` (its ledger A4, Sato
  Prop. 15.5). Both are listed in `trust-boundary.txt` by their own names.
- A43's other two infinite-divisibility clauses are declared here
  (`cited_A43_residual_infinitelyDivisible`, `cited_A43_semi_infinitelyDivisible`); its two
  uniqueness clauses and its last sentence are proved.
- A49 is declared here (`cited_A49`).
- A50 is proved, Lean core.

`trust-boundary.txt` listed twelve names after these decisions.

**Two more entries, by the author's decision of 2026-11-15** (`adr/0005-a22-and-a24-admitted.md`).
The author admitted A22 and A24 as Lean axioms, and decided that A23 and A30 are not admitted. Each
of the two has a `**Lean:**` line, and its interface node is `\leanok` on the declarations of
`Formalization/Pyramids/Cited/A<N>.lean`:

- A22 is declared here as two axioms, one per clause, `cited_A22_polya` (the kernels are Pólya
  frequency kernels) and `cited_A22_variation` (variation diminution), both at the page's range,
  an admissible family `F ≢ 0`.
- A24 is declared here as one axiom, `cited_A24`, **narrower than the page**: the identity
  $L(s)\psi(s) = 1$ is admitted on the imaginary axis $s = i\omega$ only, where both spenders read
  it, and the strip of Proposition 1.4 and the absolute convergence on it are not admitted.
- A23 is proved from `cited_A22_variation`, by the page's own derivation (p. 39), and A30 has no
  spender: `prop:line-and-arrays` is proved through checked nodes.

`trust-boundary.txt` listed fifteen names; it lists fourteen since review round 3 (batch C,
2026-11-23), when `Pyramids.cited_A42` was proved and left it. `Formalization/CIAxiomGuard.lean`
prints each.

**A1 is a theorem, by the author's decision of 2026-11-14.** The shared core proves the line
paper's representation lemma with no axiom, so `thm:cited-A1` was regraded [T] and is `\leanok`
with a proof; its declarations, in `Formalization/Pyramids/Cited/A1.lean`, print Lean core. The
entry keeps the page anchor and its transcription. It admits nothing.

**A34 is a theorem likewise, regraded in wave 2g (2026-11-14).** The affine export proves the
isotropic paper's realization lemma with no axiom, so `thm:cited-A34` is `[T]` and `\leanok` with a
proof; `Pyramids.cited_A34` prints Lean core. The two nodes that named A34 on their status lines,
`prop:ladder-knot-kernel` and `thm:matern-pyramid`, no longer do. The entry keeps the page anchor
and its transcription. A31 stays `[A]`: its uniqueness declaration prints Lean core, but its
equivalence reaches A39(ii), (iii).

The other seven entries (A13, A15, A19, A20, A30, A55, A57; six until review round 3, batch C,
made A15 one by the author's decision D3) enter no Lean proof: they are the trust base of the proofs in print, the
nodes that are `\notready` and proved on paper, and their statements are typed with `sorry` in the
skeleton.

**The interface nodes.** Each entry is also a blueprint node, its interface node: `thm:cited-A<N>`
in chapter 2 (`blueprint/src/parts/02-cited-facts.tex`), the entry's statement as used, `[A]` on
this entry alone, with no proof; `thm:cited-A1` and `thm:cited-A34`, `[T]` nodes with a proof since
2026-11-14, are the two exceptions. A node that names the entry on its status line `\uses` the
interface node (LINKAGE.md rule 14). The first label of each `**Blueprint:**` line is that node; the
others are the nodes that spend the entry, read off their status lines.

**The identifiers** are opaque and stable (LINKAGE.md rule 5). They were assigned in
`records/pyramids/BLUEPRINT-BRIEF.md`, "The ledger entries", before the chapters were written, one
per cited fact the draft named. The facts no chapter spends, and the ones the librarian's reading
showed are not printed as cited, were dropped and their ids are not reused: hence the gaps. The last
section lists them.

Format contract (enforced by `linkage check`, fatal checks 2 and 6):

```
## A<N> — <one-line statement of what is taken on trust>
**Blueprint:** `<interface node>`; `<spending nodes>`
**Cite:** @<citekey> — <statement, printed page>

- **Statement as used.** …
- **Primary — <the named theorem>.** …
- **What the entry does NOT carry.** …
```

The released modules are cited by their printed numbers in their released versions (hub
`RELEASES.md`): V-line v0.1 (`fagerstrom2026spatial`, DOI 10.5281/zenodo.22761632), V-cone
cone-v0.1 (`fagerstrom2026cone`, DOI 10.5281/zenodo.22864170), V-selection v0.1
(`fagerstrom2026selection`), iso v0.1 (`fagerstrom2026isotropic`), affine v0.1
(`fagerstrom2026affine`).

| chapter | entries |
|---|---|
| Ch. 2 — the axioms on the line and the classification (§ 2.1), the theory on the line | A1 (proved, `thm:cited-A1`), A4, A9; A13, A15, A19, A20 referred to, not spent |
| Ch. 2 — the axioms in $\mathbb{R}^d$, the classification and its polar form (§ 2.1) | A30, A31, A34, A35 (stated; spent in chs. 3–5) |
| Ch. 3 — the pyramid in $\mathbb{R}^d$: the structure of a family, the strata, the examples, what does not lift, the ladder | A39–A46, A48–A50; A31, A34, A35 |
| Ch. 4 — the Matérn pyramid: the Bessel profile, the increments, the Thorin class in dimension $d$, the selection | A51, A39; A31, A34, A35; A55 and A57 stated, not spent (A55 no longer spent, wave 3b) |
| Ch. 5 — the price of a grid: no isotropic grid pyramid, the exact masks, the line and the arrays | A39–A42, A46, A49, A50 (A30 no longer spent, wave 3b) |
| App. A — the line: the exponent data, the annulus, the Matérn pyramid on the line, non-creation, the classical pyramids | A4, A22, A23, A24, A39, A43 |

## A1 — Under (A1), (A2), (A4), (A5) each operator is the convolution with a unique probability measure, symmetric under (A3)
**Blueprint:** `thm:cited-A1` (the node stating it, ch. 2, regraded [T] by the author on 2026-11-14). No node spends it: `lem:line-axioms-kernels`, which reads it through that node, was regraded [T] in wave 2e (2026-11-14)
**Cite:** @fagerstrom2026spatial — Lemma 4.1 (representation), printed pp. 22–23 (V-line v0.1; existence and uniqueness on p. 22, the symmetry and the converse on p. 23)
**Verdict:** NARROWER-OK (`VERBATIM-V-line.md`, A1): the draft cited "§ 4, p. 22" and assumed all of (A1)–(A8); the lemma needs (A1), (A2), (A4), (A5), and its symmetry clause is on p. 23.
**Lean:** `Pyramids.cited_A1_repr`, `Pyramids.cited_A1_symm`, `Pyramids.cited_A1_converse` (`Formalization/Pyramids/Cited/A1.lean`), theorems with no axiom, proved from the shared core: `ScaleSpace.representation_existsUnique` (existence and uniqueness), `ScaleSpace.isSymmetric_of_reflL1` (the symmetry) and the core's lemmas on `mconvL1` (the converse). Not admitted, and no axiom is needed: the author regraded the node [T] on 2026-11-14, and the entry keeps the page anchor and its transcription.

- **Statement as used.** Let $\Phi_{s,t}$, $0 \le s \le t$, be linear operators on $L^1(\mathbb{R})$
  with (A1), (A2), (A4) and (A5). Then for each pair there is a unique probability measure
  $\mu_{s,t}$ on $\mathbb{R}$ with $\Phi_{s,t}f = \mu_{s,t} * f$ for $f \in L^1$; under (A3) it is
  symmetric. Conversely every symmetric probability measure on $\mathbb{R}$ defines, by
  convolution, an operator with (A1)–(A5). `lem:line-axioms-kernels`(1)–(2) reads it, as the
  theorem `thm:cited-A1`, to read the axioms on the line on the kernels.
- **Primary — V-line v0.1, Lemma 4.1, pp. 22–23.** Stated at its letter; the axioms are those of
  Def. 3.1, p. 17 (`def:cascade-measurement-family`).
- **What the entry does NOT carry.** The translation of (A6), (A7) and (ND) into (I1), (I2) and
  (ND), which the spending node proves; the continuity of the transforms (the line paper's
  Lemma 4.2), which no node cites.

## A4 — The classification on the line (the draft's Theorem 2.0): the families with (A1)–(A8) and (ND) are the similarity families of the admissible exponents, in a gauge
**Blueprint:** `thm:cited-A4` (the interface node, ch. 2; the draft's Theorem 2.0); `thm:lattice-line`, `thm:annulus-parametrization-phase`, `thm:matern-pyramid-line`
**Cite:** @fagerstrom2026spatial — Theorem 7.3 (main theorem), printed p. 37 (V-line v0.1), with the form (2.3), printed p. 13
**Verdict:** MATCH (`VERBATIM-V-line.md`, A4).
**Lean:** `Pyramids.cited_A4`, `Pyramids.cited_A4_exists`, `Pyramids.cited_A4_unique` (`Formalization/Pyramids/Cited/A4.lean`), not admitted and found to need no axiom (wave 3d, 2026-11-14): theorems. The "only if" is the shared core's `main_analysis_exists` on `AffineHemigroup.line_levy_unique` (A39(ii)–(iii)); the uniqueness is the shared core's `main_uniqueness`, Lean core; the construction and the "if" replay the shared core's construction, whose only cited step (a law with a given symmetric exponent; the core's `LineLawInterfaces`, which bundles Bochner's theorem) is taken from A39(iii) through `line_exponent_data_1`. `#print axioms` names `AffineHemigroup.levy_khintchine_unique` and `AffineHemigroup.levy_khintchine_converse` only.

- **Statement as used.** A family $(\Phi_{s,t})$ of linear operators on $L^1(\mathbb{R})$ satisfies
  (A1)–(A8) and (ND) if and only if there are an increasing bijection $\chi$ of $[0,\infty)$, the
  gauge, and $F \not\equiv 0$ of the form
  $F(\omega) = a\omega^2 + \int_0^\infty(1 - \cos\omega x)\,k(x)\,x^{-1}dx$, $a \ge 0$, $k \ge 0$
  nonincreasing, $\int_0^\infty(1 \wedge x^2)\,k(x)\,x^{-1}dx < \infty$ (the draft's (2.0)), with
  $\Phi_{s,t}f = \mu_{s,t} * f$ and
  $\hat\mu_{s,t}(\omega) = \exp(-[F(\chi(t)\omega) - F(\chi(s)\omega)])$. Conversely, for every
  such pair $(\chi, F)$ there are probability measures $\mu_{s,t}$ with these transforms, and the
  operators $f \mapsto \mu_{s,t} * f$ satisfy (A1)–(A8) and (ND) (the construction clause, written
  out at the skeleton review, M1: the theorem's "if" read for the measures its display names; the
  page's text after the theorem calls it "construction"). The pair $(\chi, F)$ is
  unique once $\chi(1) = 1$. `thm:lattice-line`(3) spends the "only if";
  `thm:annulus-parametrization-phase`(2)–(3) the admissibility of $F$ and the form
  $F(\chi(t)\,\cdot)$; `thm:matern-pyramid-line`(1) the "if", read through the construction's
  lemmas in `Cited/A4.lean` (`exists_isGaugeKernels`, `IsGaugeKernels.cascadeFamily`) at
  $\chi = \mathrm{id}$, so that the bijections $S_\lambda t = \lambda t$ of the family built on the
  given laws are visible (wave 3e).
- **Primary — V-line v0.1, Theorem 7.3, p. 37.** The page's $F$ is "of the form (2.3)", p. 13; the
  integrability is that of a Lévy measure (the line paper's Lemma 2.15, p. 13), which the draft's
  (2.0) writes into the form.
- **What the entry does NOT carry.** The monotonicity in $t$ of the data of the stages: the line
  paper's Theorem 5.2 does not state it (plan id A2, dropped), and `lem:family-structure` proves it.
  The folded Lévy measure $k(v/t)\,dv/v$ of a marginal (plan id A5, dropped): the page never prints
  it, and `thm:lattice-line` derives it from this entry with A9 and a change of variables.

## A9 — The folded Lévy–Khintchine pair $(a, \nu)$ of a symmetric exponent on the line is unique
**Blueprint:** `thm:cited-A9` (the interface node, ch. 2); `thm:lattice-line` (`prop:discrete-gaussian-pyramid` reads it only through `thm:lattice-line` since wave 3e, and cites nothing of its own)
**Cite:** @fagerstrom2026spatial — Proposition 2.3(3) (the symmetric Lévy–Khintchine clause, with display (2.2)), printed p. 9 (V-line v0.1)
**Verdict:** MATCH (`VERBATIM-V-line.md`, A8 and A9): the plan's A8 (display (2.2)) and A9 (the uniqueness) are one statement on one page, folded into this entry; A8 is not an entry.
**Lean:** `Pyramids.cited_A9` (`Formalization/Pyramids/Cited/A9.lean`), not admitted and found to need no axiom (wave 3d, 2026-11-14): a theorem, the affine module's `AffineHemigroup.line_levy_unique`, proved from A39(ii)–(iii) at `d = 1`. `#print axioms` names `AffineHemigroup.levy_khintchine_unique` and `AffineHemigroup.levy_khintchine_converse` only.

- **Statement as used.** Let $a, a' \ge 0$ and let $\nu$, $\nu'$ be measures on $(0,\infty)$ with
  $\int(1 \wedge x^2)\,d\nu < \infty$ and $\int(1 \wedge x^2)\,d\nu' < \infty$. If
  $a\omega^2 + \int(1 - \cos\omega x)\,\nu(dx) = a'\omega^2 + \int(1 - \cos\omega x)\,\nu'(dx)$ for
  every $\omega$, then $a = a'$ and $\nu = \nu'$. This is the clause's "the pair $(a,\nu)$ being
  unique", read for two pairs defining one function. `thm:lattice-line`(3) spends it to identify the
  data of the relabelled kernels with $(at^2, k(\cdot/t)\,v^{-1}dv)$.
- **Primary — V-line v0.1, Proposition 2.3(3), p. 9.** "Every $\psi \in \mathrm{ND}_s$ has the
  representation (2.2) … the pair $(a,\nu)$ being unique; and conversely every such pair defines a
  member of $\mathrm{ND}_s$." The line paper's sources note on the same page names Sato, Thm. 8.1,
  pp. 37–38, as the origin (A39 here).
- **What the entry does NOT carry.** The existence half and the converse of the clause, which no
  node spends; the class $\mathrm{ND}_s$, which is not restated; any two-sided form (the folding
  convention, p. 10).

## A13 — The generator of the Cin ray of step $\tau$ is one symmetric second difference, $\mathcal{H}_t = t^{-1}\delta^2_{t\tau}$
**Blueprint:** `thm:cited-A13` (the interface node, ch. 2; referred to in `subsec:line-strata` after `prop:lindeberg-stratum-one`, spent by no node)
**Cite:** @fagerstrom2026cone — Proposition 6.4(5), printed p. 58 (V-cone cone-v0.1), with Proposition 6.2 and Definition 6.1, printed p. 56, for the generator and its domain
**Verdict:** MATCH (`VERBATIM-V-cone.md`, A13).

- **Statement as used.** Let $\tau > 0$ and $F$ the admissible exponent with data
  $(0, \mathbf{1}_{(0,\tau)})$. In the canonical gauge the scale space $u(t,\cdot) = \mu_{0,t} * f$
  of $f \in \mathcal{S}(\mathbb{R})$ satisfies $\partial_t u = t^{-1}\delta^2_{t\tau}u$ for $t > 0$,
  $\delta^2_hg = \tfrac12(g(\cdot - h) + g(\cdot + h)) - g$.
- **Primary — V-cone, Proposition 6.4(5), p. 58.** "Cin ray of step $\tau$:
  $\mathcal{A}_t = \frac1t\delta^2_{t\tau}$", the generator $\mathcal{A}_t$ being that of Prop. 6.2
  on $\mathcal{D} = \mathscr{S}(\mathbb{R})$ (Def. 6.1). The clause prints no domain of its own; the
  statement reads it through Prop. 6.2.
- **What the entry does NOT carry.** The generator form (2.0″) for other exponents (Prop. 6.2,
  cited in the prose of § 2.1 and spent by no node); the value $\mathrm{Cin}(\tau\omega)$ of the ray
  (Lemma 3.1(1), plan id A14, not an entry).

## A15 — The Choquet structure of the admissible cone: $(a, \varpi) \mapsto a\omega^2 + \int\mathrm{Cin}(\tau\omega)\,\varpi(d\tau)$ is a bijection onto the admissible exponents, and the extreme rays are the Gaussian ray and the Cin rays
**Blueprint:** `thm:cited-A15` (the interface node, ch. 2, after `thm:cited-A13`; referred to in `subsec:cited-generator` and after `prop:strata-cylinder-coordinates` in Appendix A, spent by no node)
**Cite:** @fagerstrom2026cone — Proposition 3.3, printed pp. 15–16 (V-cone cone-v0.1; the statement opens at the foot of p. 15 and ends at the top of p. 16, after Figure 2, the extreme rays inside it)
**Verdict:** MATCH (`VERBATIM-V-cone.md`, A15; re-read from the page images on 2026-11-23, `records/pyramids/reviews/LIBRARIAN-r3.md`, "For batch C").

Made an entry in review round 3, batch C (2026-11-23), by the author's decision D3 of
`records/pyramids/PLAN-review-response-theory-round3.md`: stated for the reader, as A13, A19, A20,
A30, A55 and A57 are. The id is the one the blueprint brief assigned to this proposition, unspent
until now. Not admitted: its statement is typed with `sorry` in
`Formalization/PyramidsSkeleton/Ch02CitedFacts.lean` (`cited_A15_admissible`, `_injective`,
`_inverse`, `_extreme`).

- **Statement as used.** The map $(a, \varpi) \mapsto F$,
  $F(\omega) = a\omega^2 + \int_{(0,\infty)}\mathrm{Cin}(\tau\omega)\,\varpi(d\tau)$, is a bijection
  from the pairs with $a \ge 0$ and $\varpi$ a positive Borel measure on $(0,\infty)$ with
  $\int\min(\tau^2, 1 + \log_+\tau)\,\varpi(d\tau) < \infty$ onto the admissible exponents (the cone
  of V-cone Lemma 2.7). Its inverse takes the exponent with data $(a, k)$ to $(a, \varpi)$ with
  $\varpi = -dk$, $k(x) = \varpi((x,\infty))$ for almost every $x > 0$. The extreme rays of the cone
  are the Gaussian ray $\omega \mapsto \omega^2$ and the Cin rays $\mathrm{Cin}(\tau\,\cdot)$,
  $\tau > 0$, and every admissible exponent is a unique superposition of Cin rays and the Gaussian
  term $a\omega^2$.
- **Primary — V-cone, Proposition 3.3, pp. 15–16.** The page's "the superposition map of
  Lemma 3.1" is display (3.1) of Lemma 3.1(2), a mis-resolved cross-reference inside the statement
  (LIBRARIAN-r3).
- **What the entry does NOT carry.** The page's "linear", the additivity and positive homogeneity
  of the map, which no node reads; the folded Lévy density $x^{-1}\mathbf{1}_{(0,\tau)}$ of a Cin
  ray, which is Lemma 3.1(1) (plan id A14, not an entry); the closure of the cone under convergent
  series (plan id A16, not an entry). The page's $k(x) = \varpi((x,\infty))$ is read almost
  everywhere, as an exponent fixes its profile only up to a null set.

## A19 — The Matérn cascade on the line by forward–backward first-order sections, between knots $0 < t_k < t_{k+1}$
**Blueprint:** `thm:cited-A19` (the interface node, ch. 2; referred to by `subsec:sampled-laplace`, spent by no node)
**Cite:** @fagerstrom2026cone — Proposition 7.2, printed pp. 60–61 (V-cone cone-v0.1; the statement opens at the foot of p. 60 with (7.1); the realization and (7.2) on p. 61)
**Verdict:** NARROWER-OK, with a caveat on the case (`VERBATIM-V-cone.md`, A19): the draft's rung is $t_k = 0$, which the printed clause ($r \in (0,1)$) does not state.

- **Statement as used.** For an integer $\gamma \ge 1$ and the Matérn family
  $e^{-F(t\omega)} = (1 + t^2\omega^2)^{-\gamma}$ in the canonical gauge, and knots
  $0 < t_k < t_{k+1}$, $r := t_k/t_{k+1}$: the increment has transform
  $((1 + t_k^2\omega^2)/(1 + t_{k+1}^2\omega^2))^\gamma$ and is a cascade of $\gamma$ causal
  sections, each the convolution with $r\delta_0 + (1 - r)\mathrm{Exp}_+(t_{k+1})$ with the
  realization $w' = (y - w)/t_{k+1}$, $v = ry + (1 - r)w$, $w \in L^1$, and $\gamma$ anticausal
  mirror images; for $\gamma = 1$ the increment is
  $r^2\delta_0 + r(1 - r)(\mathrm{Exp}_+ + \mathrm{Exp}_-) + (1 - r)^2\mathrm{Lap}_{t_{k+1}}$.
- **Primary — V-cone, Proposition 7.2, pp. 60–61.** Stated at the kernels of the sections. The
  page's complex factorization of (7.1) follows the cone module's sign of the transform and is not
  restated: the kernels do not depend on it.
- **What the entry does NOT carry.** The rung from scale zero, $t_k = 0$, with increment
  $\mathrm{Lap}_{t_{k+1}} = \mathrm{Exp}_+ * \mathrm{Exp}_-$ (the identity is in the proof, p. 61,
  not the statement); the cost of a sampled cascade, which the page states and no node uses.

## A20 — For a symmetric rational infinitely divisible transform $R$ and $q > 1$, the unique continuous $F$ with $F(0) = 0$ and $F(q\omega) - F(\omega) = -\log R(\omega)$, and its admissibility
**Blueprint:** `thm:cited-A20` (the interface node, ch. 2; referred to in `subsec:grid-pyramids-line`, the lead and the paragraph after `prop:grid-pyramids-infinitely-divisible`, spent by no node)
**Cite:** @fagerstrom2026cone — Proposition 7.5(2), printed p. 65 (V-cone cone-v0.1; statement and proof on that page)
**Verdict:** MATCH (`VERBATIM-V-cone.md`, A20); the draft's locator "pp. 60–72" is corrected to p. 65, and the draft's italic quotation in its Remark 2.22 is a paraphrase, not the page's words.

- **Statement as used.** Let $R$ be a symmetric rational function that is the transform of an
  infinitely divisible law, with folded Lévy profile $k_R$. Then for each $q > 1$ there is exactly
  one continuous $F$ with $F(0) = 0$ and $F(q\omega) - F(\omega) = -\log R(\omega)$, namely
  $e^{-F} = \prod_{m \ge 1}R(q^{-m}\,\cdot)$, with folded profile
  $k(x) = \sum_{m \ge 1}k_R(q^mx)$; it is admissible exactly when $k$ has a nonincreasing version,
  in particular whenever $k_R$ is nonincreasing. The Matérn pyramid is the case
  $R(\omega) = (1 + \omega^2)^{-1}$. ("Has a nonincreasing version" restates the page's "is
  nonincreasing" at the reading of its proof, "the monotonicity is monotonicity of a
  representative": skeleton review, m2.)
- **Primary — V-cone, Proposition 7.5(2), p. 65.** At the page's words, with the reading above;
  the Gaussian coefficient of $F$ is $0$ by the proof on the same page ("at the pair $(0,k)$").
- **What the entry does NOT carry.** Clause (1) of the proposition; the proof's remark that for
  real poles $k_R$ is a finite combination of exponentials; any lattice form, which
  `prop:grid-pyramids-infinitely-divisible` proves.

## A22 — The similarity family of an admissible $a\omega^2 + \sum_i\log(1 + \omega^2/\theta_i^2)$, $\sum_i\theta_i^{-2} < \infty$, has Pólya frequency kernels
**Blueprint:** `thm:cited-A22` (the interface node, ch. 2); `thm:matern-pyramid-line-noncreation`, `prop:ladder-non-creation-line`
**Cite:** @fagerstrom2026selection — Proposition 4.5(1), printed p. 35 (V-selection v0.1)
**Verdict:** NARROWER-OK (`VERBATIM-selection-iso-affine.md`, A22): the draft uses the "if" of the page's equivalence; the hypothesis "admissible" is kept.
**Lean:** `Pyramids.cited_A22_polya`, `Pyramids.cited_A22_variation` (`Formalization/Pyramids/Cited/A22.lean`), two axioms, admitted by the author on 2026-11-15 (ADR-0005), one per clause of the statement as used, both with "admissible" and $F \not\equiv 0$. `cited_A22_polya` is the skeleton's statement; `cited_A22_variation` is the skeleton's with $F \not\equiv 0$ added, the page's range (the skeleton had typed it without, a statement true at $F \equiv 0$ but outside the page). The kernels are any probability measures with the transforms $e^{-F(t\cdot)}$, $t > 0$; "integrable or bounded $g$" is `Integrable g` or a.e.-strongly measurable and bounded.

- **Statement as used.** Let $F \not\equiv 0$ (the page's "an admissible family" presupposes it;
  skeleton review, m1) be admissible with
  $F(\omega) = a\omega^2 + \sum_i\log(1 + \omega^2/\theta_i^2)$, $a \ge 0$, countably many
  $\theta_i > 0$, $\sum_i\theta_i^{-2} < \infty$. Then the kernels $\mu_{0,t}$ of its similarity
  family are Pólya frequency kernels: $S^-(\mu_{0,t} * g) \le S^-(g)$ for every $t > 0$ and every
  integrable or bounded $g$, $S^-$ the number of sign changes in the essential sense.
  `thm:matern-pyramid-line-noncreation` spends it for $F_q$ and $\log(1 + \omega^2)$;
  `prop:ladder-non-creation-line`(1) for the exponent $G$ of its proof.
- **Primary — V-selection, Proposition 4.5(1), p. 35.** The "if" half.
- **What the entry does NOT carry.** The "only if"; the page's list of members and non-members; the
  admissibility of the exponents it is applied to, which the spending nodes prove.

## A23 — The counting clause: for such a family, no more zero crossings at any level and no more changes of monotonicity than the signal
**Blueprint:** `thm:cited-A23` (the interface node, ch. 2); `thm:matern-pyramid`, `prop:ladder-non-creation-line`
**Cite:** @fagerstrom2026selection — Proposition 4.5(2), printed p. 35 (V-selection v0.1; its derivation from clause (1) on p. 39)
**Verdict:** MATCH (`VERBATIM-selection-iso-affine.md`, A23).
**Lean:** `Pyramids.cited_A23` (`Formalization/Pyramids/Cited/A23.lean`), not admitted (ADR-0005) and found to need no axiom of its own (wave 3b, 2026-11-15): a theorem, proved from `Pyramids.cited_A22_variation` by the page's derivation on p. 39, with the primitive under the convolution (Fubini on $[0,x] \times \mu_{0,t}$), the Lebesgue differentiation theorem for $\partial_xu(t,\cdot) = \mu_{0,t} * f'$ a.e., and the case $F \equiv 0$ (kernel $\delta_0$) proved directly. `#print axioms` names `cited_A22_variation` only, beside Lean core.

- **Statement as used.** For a family as in A22 and $f$ the primitive of an integrable $f'$:
  $S^-(u(t,\cdot) - c) \le S^-(f - c)$ for every $c \in \mathbb{R}$ and
  $S^-(\partial_xu(t,\cdot)) \le S^-(f')$, at every $t > 0$. `prop:ladder-non-creation-line`(2)
  spends it for the similarity family of $G$, applied to the signal at the rung.
- **Primary — V-selection, Proposition 4.5(2), p. 35.** Derived on p. 39 from clause (1) applied to
  the bounded $f - c$ and to $f'$.
- **What the entry does NOT carry.** Any signal that is not the primitive of an integrable function.

## A24 — Schoenberg's representation: the reciprocal two-sided Laplace transform of a Pólya frequency density is $e^{-\gamma s^2 + \delta s}\prod_j(1 + a_js)e^{-a_js}$ on a strip around the imaginary axis
**Blueprint:** `thm:cited-A24` (the interface node, ch. 2); `thm:matern-pyramid-line-noncreation`, `prop:classical-pyramids-approximate-discrete-gaussian`
**Cite:** @karlin1968total — Chapter 7, Theorem 3.2(a), printed p. 345, whose statement carries the condition $\gamma + \sum_ja_j^2 > 0$ (p. 346 adds that it is essential; V-selection p. 35 anchors it to Remark 3.1, p. 346, which is about dropping integrability), the class $\mathscr{E}_2^*$ of display (2.2), p. 336, and Proposition 1.4, p. 333 · @fagerstrom2026selection — § 4.3, printed pp. 34–36 (the fact as V-selection v0.1 prints it, at Karlin's letter)
**Verdict:** NARROWER-OK (`VERBATIM-selection-iso-affine.md` and `VERBATIM-literature.md`, A24): the pages are right; the draft omits $\gamma \ge 0$, real $a_j$ and the normalization $\gamma + \sum_ja_j^2 > 0$, which are stated here.
**Lean:** `Pyramids.cited_A24` (`Formalization/Pyramids/Cited/A24.lean`), an axiom, admitted by the author on 2026-11-15 (ADR-0005), **narrower than the page and than the skeleton's type**: the identity $L(i\omega)\psi(i\omega) = 1$ for every real $\omega$, with Karlin's class as the page gives it ($\gamma \ge 0$, $\delta$ and the $a_j$ real, $\sum_ja_j^2 < \infty$, $\gamma + \sum_ja_j^2 > 0$, $\psi$ entire, $\psi(0) = 1$); the strip $\alpha < \mathrm{Re}\,s < \beta$ and the absolute convergence of $L$ on it (Prop. 1.4) are dropped, since both spenders read the identity only on the imaginary axis, which lies in the strip. $\psi$ is the shared core's `polyaE2 γ δ a`, for any square-summable sequence `a : ℕ → ℝ` (a finite family padded by zeros is one case).

- **Statement as used** (narrowed on 2026-11-15 at the admission, ADR-0005; it was the page's strip form). For a Pólya frequency density $\phi$ on $\mathbb{R}$ with
  $L(s) = \int e^{-sx}\phi(x)\,dx$ there are $\gamma \ge 0$, $\delta \in \mathbb{R}$ and
  real $a_j$ with $\sum_ja_j^2 < \infty$ and $\gamma + \sum_ja_j^2 > 0$ such that
  $\psi(s) = e^{-\gamma s^2 + \delta s}\prod_j(1 + a_js)e^{-a_js}$ is entire, $\psi(0) = 1$, and
  $L(i\omega)\psi(i\omega) = 1$ for every real $\omega$. The page gives the identity on an open strip
  $\alpha < \mathrm{Re}\,s < \beta$, $\alpha < 0 < \beta$, on which $L$ converges absolutely; only its
  restriction to the imaginary axis is used and admitted.
  `thm:matern-pyramid-line-noncreation` spends the extension of $1/L$ from the imaginary axis to the entire $\psi$;
  `prop:classical-pyramids-approximate-discrete-gaussian` the modulus of $\psi$ on the imaginary axis.
- **Primary — Karlin, Total Positivity I, Ch. 7, Theorem 3.2(a), p. 345.** "A necessary and
  sufficient condition that a density function $f(u)$ be PF is that the reciprocal of its Laplace
  transform be an entire function of class $\mathscr{E}_2^*$ with $\gamma + \sum a_i^2 > 0$"; the class
  is (2.2), p. 336; the strip is Prop. 1.4, p. 333 (stated for PF$_2$ densities, so for PF densities).
  V-selection § 4.3 prints the same fact in the form used, pp. 34–36.
- **What the entry does NOT carry.** The converse (Karlin, p. 336, the sentence after (2.2)); and
  that a Pólya frequency density has an absolutely continuous Lévy measure (plan id A25, dropped:
  V-selection § 4.3 does not print it), which
  `prop:classical-pyramids-approximate-discrete-gaussian` proves from this entry and the uniqueness of the folded pair (`lem:line-exponent-data`(1)), for the exponent of its kernel (wave 3b; the print read A39 there).

## A30 — Operators and kernels in dimension $d$: an operator with (A1), (A2), (A4), (A5) is a convolution; convergence of transforms is convergence of the operators on $L^1$
**Blueprint:** `thm:cited-A30` (the interface node, ch. 2). No node spends it since wave 3b (2026-11-15): `prop:line-and-arrays`, its only spender, is proved through checked nodes (`CarriesGridLadder.family`, `exact_masks_1`, `grid_pyramids_id_2`) and is [T]; A30 is not admitted (ADR-0005), as A13, A19 and A20 are unspent
**Cite:** @fagerstrom2026isotropic — Lemma 3.3(1)–(2), printed p. 11 (iso v0.1; clause (2) proved in the supplement, § S3.1)
**Verdict:** MATCH (`VERBATIM-selection-iso-affine.md`, A30).

- **Statement as used.** (1) A bounded, translation-commuting, positive, mass-preserving linear
  operator on $L^1(\mathbb{R}^d)$ is $f \mapsto \mu * f$ for a unique probability measure $\mu$, and
  conversely. (2) $\hat\mu_n \to \hat\mu$ pointwise iff $\mu_n * f \to \mu * f$ in $L^1$ for every
  $f$. No node spends it: `prop:line-and-arrays`(1), which spent both at $d = 1$, is proved
  through checked nodes since wave 3b (2026-11-15).
- **Primary — iso v0.1, Lemma 3.3(1)–(2), p. 11.**
- **What the entry does NOT carry.** Clauses (3)–(4) of the lemma, p. 12.

## A31 — The classification in $\mathbb{R}^d$ (the draft's Theorem 2.0′): the isotropic cascade families are those with $\hat\mu_{s,t}(\omega) = \exp(-[F(\chi(t)|\omega|) - F(\chi(s)|\omega|)])$, $F \in \mathcal{A}_d$
**Blueprint:** `thm:cited-A31` (the interface node, ch. 2; the draft's Theorem 2.0′); `thm:lattice-strata`, `thm:matern-pyramid`
**Cite:** @fagerstrom2026isotropic — Theorem 3.6, printed p. 13 (iso v0.1), with the gauge of its § 2.2 and $\mathcal{A}_d$ of its Proposition 2.6, p. 8
**Verdict:** NARROWER-OK (`VERBATIM-selection-iso-affine.md`, A31): the draft drops the page's sentence on the kernels from scale zero and its wider uniqueness.
**Lean:** `Pyramids.cited_A31`, `Pyramids.cited_A31_unique` (`Formalization/Pyramids/Cited/A31.lean`), admitted by the author on 2026-11-14 and found to need no axiom of its own: theorems, the affine export's `AffineHemigroup.isotropic_classification` (which reaches `levy_khintchine_unique` and `levy_khintchine_converse`, A39) and `AffineHemigroup.isotropic_classification_unique` (Lean core), with `F'(0) = 0` read from `F' ∈ 𝒜_d`.

- **Statement as used.** For $d \ge 1$ and $\mathcal{A}_d$ the admissible $F$ with $F(|\cdot|)$ the
  exponent of a self-decomposable law on $\mathbb{R}^d$: a family of probability measures on
  $\mathbb{R}^d$ is an isotropic cascade family iff there are a gauge $\chi$ and $F \in \mathcal{A}_d$,
  $F \not\equiv 0$, with $\hat\mu_{s,t}(\omega) = \exp(-[F(\chi(t)|\omega|) - F(\chi(s)|\omega|)])$;
  the pair is unique up to $(\chi, F) \mapsto (c\chi, F(c^{-1}\cdot))$, so unique once
  $\chi(1) = 1$. `thm:lattice-strata`(3) spends both directions; `thm:matern-pyramid`(2) the form of
  a fully covariant family.
- **Primary — iso v0.1, Theorem 3.6, p. 13.**
- **What the entry does NOT carry.** The page's uniqueness against any real $F'$ with $F'(0) = 0$;
  the reduction to the marginals (iso Lem. 3.4–3.5, plan ids A32–A33, not entries), which
  `lem:reduction-keeps-stratum` replaces with its own proof.

## A34 — Every pair $(\chi, F)$ with $F \in \mathcal{A}_d$, $F \not\equiv 0$, is realized by an isotropic cascade family
**Blueprint:** `thm:cited-A34` (the node stating it, ch. 2, regraded [T] in wave 2g on 2026-11-14, as `thm:cited-A1` was). No node spends it: `prop:ladder-knot-kernel` and `thm:matern-pyramid` read it through that node, and it left their status lines the same day
**Cite:** @fagerstrom2026isotropic — Lemma 3.8, printed p. 14 (iso v0.1)
**Verdict:** MATCH (`VERBATIM-selection-iso-affine.md`, A34).
**Lean:** `Pyramids.cited_A34` (`Formalization/Pyramids/Cited/A34.lean`), a theorem with no axiom: the affine export's `AffineHemigroup.isotropic_realisation`, which `#print axioms` shows to be Lean core. Admitted by the author on 2026-11-14 and found to need no axiom, so the node was regraded [T] the same day (wave 2g); the entry keeps the page anchor and its transcription, and admits nothing.

- **Statement as used.** For $d \ge 1$, a gauge $\chi$ and $F \in \mathcal{A}_d$, $F \not\equiv 0$,
  there is an isotropic cascade family in dimension $d$ with
  $\hat\mu_{s,t}(\omega) = \exp(-[F(\chi(t)|\omega|) - F(\chi(s)|\omega|)])$. Both spending nodes
  take $\chi = \mathrm{id}$.
- **Primary — iso v0.1, Lemma 3.8, p. 14.**
- **What the entry does NOT carry.** Uniqueness of the family (A31).

## A35 — The polar form of $\mathcal{A}_d$: $F(|\cdot|)$ is a self-decomposable exponent on $\mathbb{R}^d$ iff it is the exponent of an isotropic origin datum, and then $F$ is admissible
**Blueprint:** `thm:cited-A35` (the interface node, ch. 2); `prop:ladder-knot-kernel`, `thm:matern-pyramid`
**Cite:** @fagerstrom2026isotropic — Proposition 3.11(1)–(2), printed pp. 15–16 (iso v0.1; clause (1) on p. 15, clause (2) on p. 16)
**Verdict:** MATCH, with a page correction (`VERBATIM-selection-iso-affine.md`, A35): the draft and the brief put both clauses on p. 15.
**Lean:** `Pyramids.cited_A35_reading`, `Pyramids.cited_A35_unique`, `Pyramids.cited_A35_admissible`, `Pyramids.cited_A35_classA` (`Formalization/Pyramids/Cited/A35.lean`), admitted by the author on 2026-11-14 and found to need no axiom of its own: theorems, the affine export's `polar_reading`, `polar_reading_unique`, `polar_reading_admissible` and `classA_iff_originDatum`, which reach A39's names, `AffineHemigroup.sato_polar_criterion` (A45) and `AffineHemigroup.selfDecomposable_infinitelyDivisible` (A43, first clause).

- **Statement as used.** For $d \ge 1$ and $F : [0,\infty) \to [0,\infty)$: (1) $F(|\cdot|)$ is the
  exponent of a self-decomposable law on $\mathbb{R}^d$ iff it is the exponent $F_d$ of an
  isotropic origin datum $(a, k_d)$ (`def:isotropic-origin-data`), the datum then unique, $k_d$ up
  to a null set; (2) then $F$ is admissible, with Gaussian coefficient $\tfrac12a'$ and profile
  $k_1$ for its datum $(a', k_1)$ in dimension 1, so $\mathcal{A}_d$ is the set of $F$ for which
  $F(|\cdot|)$ is the exponent of an isotropic origin datum. `thm:matern-pyramid`(1), (5) spend the
  membership in $\mathcal{A}_d$; `prop:ladder-knot-kernel`(4) clauses (1) and (2), the equivalence with uniqueness and the admissibility of a replaced profile, in (4)(b).
- **Primary — iso v0.1, Proposition 3.11(1)–(2), pp. 15–16.** The definition of the data is
  Def. 3.10, p. 15, with its two integrability conditions.
- **What the entry does NOT carry.** Clause (3), the classification in polar form (plan id A36,
  unspent); the strict filtration of iso Prop. 3.22, cited in prose.

## A39 — The Lévy–Khintchine representation on $\mathbb{R}^d$: existence of the generating triplet, its uniqueness, and every triplet occurs
**Blueprint:** `thm:cited-A39` (the interface node, ch. 2); `prop:lindeberg-stratum-one`, `lem:family-structure`, `lem:discrete-covariance-levy`, `lem:synthesis`, `thm:lattice-strata`, `prop:stratum-one-example`, `prop:what-does-not-lift`, `prop:what-does-not-lift-chain`, `prop:ladder-knot-kernel`, `prop:matern-increments`, `thm:selection-stratum-two`, `prop:grid-pyramid-not-isotropic`, `prop:exact-masks`, `lem:line-exponent-data`, `prop:grid-pyramid-singular-kernels` (clause (3), in print; review round 3, batch C)
**Cite:** @sato1999levy — Theorem 8.1(i)–(iii), printed pp. 37–38 ((i) with (8.1)–(8.2) at the foot of p. 37; (ii) and (iii) at the head of p. 38), with Definition 8.2, p. 38
**Verdict:** MATCH, with a page correction (`VERBATIM-Sato.md`, A39): the uniqueness (ii) is on p. 38, where the draft's lines 490, 794, 796, 798 cite p. 37.
**Lean:** `AffineHemigroup.levy_khintchine_exists`, `AffineHemigroup.levy_khintchine_unique`, `AffineHemigroup.levy_khintchine_converse`, the affine export's axioms for the same three clauses (its ledger A3, Sato Thm. 8.1, pp. 37–38), admitted here by the author on 2026-11-13 and listed in `trust-boundary.txt` by their own names; the interface node's declarations `Pyramids.cited_A39_exists`, `Pyramids.cited_A39_unique`, `Pyramids.cited_A39_converse` (`Formalization/Pyramids/Cited/A39.lean`) are those axioms, at the statements the skeleton typed. No axiom of this module's own.

- **Statement as used.** (i) An infinitely divisible $\mu$ on $\mathbb{R}^d$ has
  $\hat\mu(z) = \exp[-\tfrac12\langle z, Az\rangle + i\langle\gamma, z\rangle + \int(e^{i\langle z,x\rangle} - 1 - i\langle z,x\rangle\mathbf{1}_D(x))\,\nu(dx)]$,
  $A$ symmetric nonnegative-definite, $\gamma \in \mathbb{R}^d$, $\nu(\{0\}) = 0$,
  $\int(|x|^2 \wedge 1)\,d\nu < \infty$, $D$ the closed unit ball; (ii) the triplet is unique;
  (iii) every such triplet occurs. Each spending node names the clauses it reads in its own
  annotation: (i) for the form of the exponent, (ii) to identify data (additivity under
  convolution, symmetries of the law passed to the Lévy measure, the data of a linear image), (iii)
  for the laws of prescribed data.
- **Primary — Sato, Lévy Processes and Infinitely Divisible Distributions, Theorem 8.1, pp. 37–38.**
- **What the entry does NOT carry.** The reductions for symmetric laws ($\gamma = 0$ and the cosine
  form; a real or radial transform gives a symmetric or rotation-invariant law), which the spending
  nodes prove in one line; the normalization of this paper, whose Gaussian part is half of Sato's
  matrix (linear, so (ii) transfers).

## A40 — The transform of an infinitely divisible law has no zero
**Blueprint:** `thm:cited-A40` (the interface node, ch. 2); `lem:family-structure`, `prop:grid-pyramid-not-isotropic`; since review round 3, batch C, `prop:grid-pyramid-singular-kernels` (1)–(2), machine-checked, and `prop:band-limited-refinable-mask`(1), in print
**Cite:** @sato1999levy — Lemma 7.5, printed p. 32
**Verdict:** NARROWER-OK (`VERBATIM-Sato.md`, A40): the draft's "real" and "positive" are its own steps.
**Lean:** `Pyramids.cited_A40` (`Formalization/Pyramids/Cited/A40.lean`), admitted by the author on 2026-11-13 and found to need no axiom of its own: a theorem, proved in two lines from A39(i), `AffineHemigroup.levy_khintchine_exists` (the transform is a complex exponential, which has no zero). `#print axioms` names that axiom only.

- **Statement as used.** If $\mu$ is infinitely divisible on $\mathbb{R}^d$, then $\hat\mu(z) \ne 0$
  for every $z$.
- **Primary — Sato, Lemma 7.5, p. 32.**
- **What the entry does NOT carry.** That a symmetric law has a real transform, positive by
  continuity from $\hat\mu(0) = 1$, which the spending nodes prove.

## A41 — Khintchine's theorem: a limit of the shifted row sums of a null array is infinitely divisible
**Blueprint:** `thm:cited-A41` (the interface node, ch. 2); `lem:steps-infinitely-divisible`, through which `lem:family-structure`, `prop:no-bounded-step`, `prop:grid-pyramid-not-isotropic` and `prop:exact-masks` spend it, and since review round 3, batch C, `prop:grid-pyramid-singular-kernels` and `prop:band-limited-refinable-mask`(3), the latter in print
**Cite:** @sato1999levy — Theorem 9.3 (Khintchine), printed p. 47, with Definition 9.2 and (9.1) on the same page
**Verdict:** NARROWER-OK (`VERBATIM-Sato.md`, A41).
**Lean:** `AffineHemigroup.khintchine_null_array`, the affine export's axiom for the same theorem (its ledger A6, Sato Thm. 9.3, p. 47), stated there for the laws of nonempty rows; admitted here by the author on 2026-11-13 and listed in `trust-boundary.txt` by its own name. The interface node's declaration `Pyramids.cited_A41` (`Formalization/Pyramids/Cited/A41.lean`), at the page's letter with random variables and rows allowed empty, is a theorem proved from it: the law of a sum of independent variables is the convolution of their laws (`Pyramids.map_sum_eq_convList`), and a point mass at `0` put in front of each row changes neither the row sum's law nor (9.1). No axiom of this module's own.

- **Statement as used.** For a null array $\{Z_{nk}\}$ on $\mathbb{R}^d$ (independent in each row,
  $\lim_n\max_k P[|Z_{nk}| > \varepsilon] = 0$ for every $\varepsilon > 0$) with row sums $S_n$: if
  the law of $S_n - b_n$ converges to $\mu$ for some $b_n$, then $\mu$ is infinitely divisible. The
  spending nodes take $b_n = 0$ and row sums whose laws all equal the law in question.
- **Primary — Sato, Theorem 9.3, p. 47.**
- **What the entry does NOT carry.** The construction of the null array from (I1) and (I2).

## A42 — The linear image $U_*\mu$ of an infinitely divisible law has triplet $(UAU^{\top}, [\nu U^{-1}]_{\mathbb{R}^n\setminus\{0\}}, \gamma_U)$
**Blueprint:** `thm:cited-A42` (the interface node, ch. 2); `lem:family-structure`, `lem:lattice-infinitely-divisible`, `prop:what-does-not-lift`, `prop:what-does-not-lift-chain`, `prop:grid-pyramid-not-isotropic`
**Cite:** @sato1999levy — Proposition 11.10, printed p. 65 (formulas (11.8)–(11.10)), printed for a Lévy process and read for its law at time 1 through the correspondence stated on the same page
**Verdict:** NARROWER-OK (`VERBATIM-Sato.md`, A42): process versus law; the statement is for the law.
**Lean:** `Pyramids.cited_A42` (`Formalization/Pyramids/Cited/A42.lean`), admitted by the author on 2026-11-13 as an axiom, at the statement the skeleton typed (with the $\nu$-integrability of the correction integrand); a theorem since review round 3 (batch C, 2026-11-23), the statement unchanged: the change of variables $y = Ux$ in the formula (8.1) of A39(i), the correction integrand bounded by $(K^3 + 1)\min(|x|^2, 1)$ with $K$ the norm of $U$. It reads the definition of a generating triplet and none of A39's axioms; `#print axioms` prints Lean core, and the name left `trust-boundary.txt`.

- **Statement as used.** For $\mu$ infinitely divisible on $\mathbb{R}^d$ with triplet
  $(A,\nu,\gamma)$ and an $n \times d$ matrix $U$, $U_*\mu$ is infinitely divisible on
  $\mathbb{R}^n$ with $A_U = UAU^{\top}$, $\nu_U = [\nu U^{-1}]_{\mathbb{R}^n \setminus \{0\}}$,
  $\gamma_U = U\gamma + \int Ux(\mathbf{1}_E(Ux) - \mathbf{1}_D(x))\,\nu(dx)$. Spent for $qI$,
  $q^nI$, an invertible $G^{-1}$, rotations, the reflection $-I$ and coordinate maps. Every spender reads $\mathcal{I}(U_*\mu)$,
  $A_U$ and $\nu_U$ only: the six call sites of `cited_A42` discard $\gamma_U$ and the
  integrability conjunct (`prop:grid-pyramid-not-isotropic` at `Price/NotIsotropic.lean:57` among them).
- **Primary — Sato, Proposition 11.10, p. 65.** Stated for a Lévy process $\{X_t\}$; the law is
  $P_{X_1} = \mu$.
- **What the entry does NOT carry.** Anything about the process beyond its law at time 1.

## A43 — A self-decomposable law is infinitely divisible with unique infinitely divisible residuals, and semi-selfdecomposable for every span; a semi-selfdecomposable law is infinitely divisible with a unique residual
**Blueprint:** `thm:cited-A43` (the interface node, ch. 2); `prop:what-does-not-lift-chain`, `prop:strata-cylinder-coordinates-q-cin`
**Cite:** @sato1999levy — Proposition 15.5, printed p. 93, with the sentence after it on the same page
**Verdict:** MATCH (`VERBATIM-Sato.md`, A43).
**Lean:** `AffineHemigroup.selfDecomposable_infinitelyDivisible`, the affine export's axiom for the first clause (its ledger A4, Sato Prop. 15.5, p. 93), and `Pyramids.cited_A43_residual_infinitelyDivisible`, `Pyramids.cited_A43_semi_infinitelyDivisible`, two axioms declared in `Formalization/Pyramids/Cited/A43.lean` for the infinite divisibility of the residual of a self-decomposable law and of a semi-selfdecomposable law; admitted by the author on 2026-11-14. The interface node's declarations `Pyramids.cited_A43_sd`, `Pyramids.cited_A43_semi`, `Pyramids.cited_A43_span` are theorems from these three; both uniqueness clauses are proved by the page's own argument (the transform has no zero, `cited_A40`), and the last sentence from the first clause.

- **Statement as used.** If $\mu$ is self-decomposable, it is infinitely divisible and every
  $\rho_b$, $b > 1$, is unique and infinitely divisible; if semi-selfdecomposable, it is infinitely
  divisible and $\rho_b$ is unique; so a self-decomposable law is semi-selfdecomposable with every
  $b > 1$ as a span. `prop:what-does-not-lift-chain` spends the last clause and the infinite
  divisibility.
- **Primary — Sato, Proposition 15.5, p. 93.** Definitions: Def. 15.1, p. 90
  (`def:self-decomposable`).
- **What the entry does NOT carry.** The criterion by the Lévy measure (A44).

## A44 — An infinitely divisible law is semi-selfdecomposable with span $b$ iff $D_b\nu \ge \nu$
**Blueprint:** `thm:cited-A44` (the interface node, ch. 2); `prop:lindeberg-stratum-one`, `prop:stratum-one-example`
**Cite:** @sato1999levy — Theorem 15.8, printed p. 94 (formula (15.6); $T_r$ defined at (13.8), p. 75)
**Verdict:** MATCH (`VERBATIM-Sato.md`, A44).
**Lean:** `Pyramids.cited_A44` (`Formalization/Pyramids/Cited/A44.lean`), not admitted and found to need no axiom (wave 3d, 2026-11-14): a theorem, by the argument of Sato's proof. A42 at `U = b⁻¹I` gives the triplet `(b⁻²A, (b⁻¹)_*ν, γ')` of the image of `μ` under `x ↦ b⁻¹x`; the "only if" adds the triplet of the residual (A39(i)) and identifies the Lévy measures (A39(ii)); the "if" builds the residual from the triplet `((1 - b⁻²)A, ν - (b⁻¹)_*ν, γ - γ')` by A39(iii), the difference of measures taken as `ν` with density `1 - d(b⁻¹)_*ν/dν`. `#print axioms` names `AffineHemigroup.levy_khintchine_exists`, `_unique`, `_converse` only (and `Pyramids.cited_A42` until review round 3, batch C, when that was proved).

- **Statement as used.** Fix $b > 1$; an infinitely divisible $\mu$ on $\mathbb{R}^d$ with triplet
  $(A,\nu,\gamma)$ is semi-selfdecomposable with span $b$ iff $D_b\nu \ge \nu$, $D_b\nu$ the image
  of $\nu$ under $x \mapsto bx$ (Sato's $T_b\nu$); no restriction on $A$, $\gamma$.
- **Primary — Sato, Theorem 15.8, p. 94.**
- **What the entry does NOT carry.** The shell form (15.7).

## A45 — An infinitely divisible law on $\mathbb{R}^d$ is self-decomposable iff its Lévy measure has the polar form $\int\lambda(d\xi)\int\mathbf{1}_B(r\xi)k_\xi(r)\,dr/r$ with $k_\xi$ nonincreasing
**Blueprint:** `thm:cited-A45` (the interface node, ch. 2); `prop:stratum-two-example`, `prop:ladder-knot-kernel`
**Cite:** @sato1999levy — Theorem 15.10, printed p. 95 (formula (15.8))
**Verdict:** NARROWER-OK (`VERBATIM-Sato.md`, A45): the draft's consequences (countable sets and spheres have mass 0) are not printed; Cor. 15.11 is on p. 95.
**Lean:** `AffineHemigroup.sato_polar_criterion`, the affine export's axiom for the same theorem (its ledger A2, Sato Thm. 15.10, p. 95), admitted here by the author on 2026-11-14 and listed in `trust-boundary.txt` by its own name; the interface node's declaration `Pyramids.cited_A45` (`Formalization/Pyramids/Cited/A45.lean`) is that axiom, at the statement the skeleton typed. No axiom of this module's own.

- **Statement as used.** For $\mu$ infinitely divisible on $\mathbb{R}^d$ with triplet
  $(A,\nu,\gamma)$: $\mu$ is self-decomposable iff
  $\nu(B) = \int_S\lambda(d\xi)\int_0^\infty\mathbf{1}_B(r\xi)k_\xi(r)\,dr/r$ with $\lambda$ finite on
  the unit sphere $S$ and $k_\xi(r) \ge 0$ measurable in $\xi$ and nonincreasing in $r$ (Sato's
  "decreasing" is weak); no restriction on $A$, $\gamma$. The spending nodes use the "only if".
- **Primary — Sato, Theorem 15.10, p. 95.**
- **What the entry does NOT carry.** The consequences for countable sets and spheres (proved in the
  spending nodes, one line each); the line case with a density, Cor. 15.11, p. 95, which no node
  spends (plan's A45 included it; `thm:lattice-line` says it is not used).

## A46 — An infinitely divisible law other than a point mass has unbounded support
**Blueprint:** `thm:cited-A46` (the interface node, ch. 2); `prop:no-bounded-step`, `prop:exact-masks`
**Cite:** @sato1999levy — Corollary 24.4, printed p. 149
**Verdict:** MATCH (`VERBATIM-Sato.md`, A46).
**Lean:** `Pyramids.cited_A46` (`Formalization/Pyramids/Cited/A46.lean`), an axiom, admitted by the author on 2026-11-13; "unbounded support" is read as positive mass outside every ball.

- **Statement as used.** If $\mu$ is infinitely divisible on $\mathbb{R}^d$ and not a point mass,
  its support is unbounded.
- **Primary — Sato, Corollary 24.4, p. 149.**
- **What the entry does NOT carry.** The shape of the support (Thm. 24.5, plan id A47, unspent).

## A48 — An infinitely divisible law on $\mathbb{R}$ carried by $\mathbb{Z}$ has $A = 0$ and a Lévy measure carried by $\mathbb{Z}$
**Blueprint:** `thm:cited-A48` (the interface node, ch. 2); `lem:lattice-infinitely-divisible`
**Cite:** @sato1999levy — Corollary 24.6 (Support in $\mathbb{Z}$), printed p. 149, its "only if"
**Verdict:** NARROWER-OK (`VERBATIM-Sato.md`, A48): stated on $\mathbb{R}$; the drift clause is not used. The finiteness of $\nu$ is in the proof, not the statement, and since review round 3 it is proved here, not admitted.
**Lean:** `Pyramids.cited_A48` (`Formalization/Pyramids/Cited/A48.lean`), an axiom, admitted by the author on 2026-11-13, on $\mathbb{R}^1$; "carried by $\mathbb{Z}$" is read as "the complement of $\mathbb{Z}$ is null". Since review round 3 (batch C, 2026-11-23) the axiom is $A = 0$ and $\nu$ carried by $\mathbb{Z}$, what the corollary states; until then it also admitted $\nu(\mathbb{R}) < \infty$ from the proof on the page. That clause is the theorem `Pyramids.isFiniteMeasure_levy_of_int` (Lean core: $\nu$ is carried by $\mathbb{Z} \setminus \{0\}$, where $\min(|x|^2, 1) = 1$), and `Pyramids.cited_A48_finite` is the former three-clause statement, for its user.

- **Statement as used.** For $\mu$ infinitely divisible on $\mathbb{R}$ with triplet
  $(A,\nu,\gamma)$: if the support of $\mu$ lies in $\mathbb{Z}$, then $A = 0$ and the support of
  $\nu$ lies in $\mathbb{Z}$. `lem:lattice-infinitely-divisible` spends it on the coordinate images
  of a law on a lattice, with $\nu(\mathbb{R}) < \infty$, which the interface node proves from it.
- **Primary — Sato, Corollary 24.6, p. 149.**
- **What the entry does NOT carry.** The converse; the drift clause; any form on $\mathbb{R}^d$;
  the finiteness of $\nu$ (proved; Sato's proof on the same page shows it: "Hence it is shown that
  $\nu(\mathbb{R}) < \infty$").

## A49 — For $g$ submultiplicative, locally bounded and measurable, an infinitely divisible law has finite $g$-moment iff its Lévy measure on $\{|x| > 1\}$ does
**Blueprint:** `thm:cited-A49` (the interface node, ch. 2); `prop:ladder-knot-kernel`, `prop:exact-masks`
**Cite:** @sato1999levy — Theorem 25.3 ($g$-moment), printed p. 159, with Definitions 25.1–25.2 on the same page
**Verdict:** NARROWER-OK, one hypothesis added (`VERBATIM-Sato.md`, A49): the page requires $g$ locally bounded, which the draft does not name; the page is for a Lévy process, read at $t = 1$.
**Lean:** `Pyramids.cited_A49` (`Formalization/Pyramids/Cited/A49.lean`), an axiom, admitted by the author on 2026-11-14, at the statement the skeleton typed; both directions, since both are spent.

- **Statement as used.** Let $g$ on $\mathbb{R}^d$ be submultiplicative ($g \ge 0$,
  $g(x + y) \le a\,g(x)g(y)$), locally bounded and measurable, and $\mu$ infinitely divisible with
  Lévy measure $\nu$. Then $\int g\,d\mu < \infty$ iff $\int_{|x| > 1}g\,d\nu < \infty$. Spent with
  $g(x) = \log(|x| \vee e)$, continuous, hence locally bounded.
- **Primary — Sato, Theorem 25.3, p. 159.** "Finiteness of the $g$-moment is not a time dependent
  distributional property", so the process form gives the law $P_{X_1} = \mu$.
- **What the entry does NOT carry.** The comparison of $\log(|x| \vee e)$ with $\log_+|x|$, made by
  the spending nodes.

## A50 — $\log(|x| \vee e)$ is submultiplicative
**Blueprint:** `thm:cited-A50` (the interface node, ch. 2); `prop:ladder-knot-kernel`, `prop:exact-masks`
**Cite:** @sato1999levy — Proposition 25.4(iii), printed p. 159
**Verdict:** MATCH (`VERBATIM-Sato.md`, A50).
**Lean:** `Pyramids.cited_A50` (`Formalization/Pyramids/Cited/A50.lean`), admitted by the author on 2026-11-14 and found to need no axiom: a theorem, Lean core, with the constant `a = 2` (for `u, v ≥ e > 2`, `u + v ≤ uv`, so `g(x + y) ≤ g(x) + g(y) ≤ 2g(x)g(y)`, both values being at least `1`).

- **Statement as used.** $g(x) = \log(|x| \vee e)$ is submultiplicative on $\mathbb{R}^d$.
- **Primary — Sato, Proposition 25.4(iii), p. 159.** One function of the list.
- **What the entry does NOT carry.** The rest of the list and clauses (i)–(ii); local boundedness,
  which is not on the page and holds by continuity.

## A51 — The integral representation of $K_\nu$, DLMF 10.32.10
**Blueprint:** `thm:cited-A51` (the interface node, ch. 2); `lem:bessel-k`
**Cite:** @dlmf2026 — NIST Digital Library of Mathematical Functions, equation 10.32.10, https://dlmf.nist.gov/10.32.E10 (Version 1.2.8, 2026-09-15, read online), with the definition 10.32.9 (below)
**Verdict:** MATCH, with a correction of the draft's own sentence (`VERBATIM-literature.md`, A51): the draft's "only the integral form is used below" (line 541) is untrue of its lines 590 and 602, which read the further equations.
**Lean:** `Pyramids.cited_A51_integral`, a theorem with no axiom, proved from the definition of the shared core's `besselK` (DLMF 10.32.9) by its substitution lemma `ScaleSpace.lintegral_Ioi_rpow_exp_besselKernel` and a Gaussian bound showing the cosh integral finite (`Pyramids.lintegral_cosh_exp_ne_top`), in `Formalization/Pyramids/Cited/A51.lean`. Admitted by the author on 2026-11-13; the axiom `cited_A51_evaluations` for the former clause (2) was dropped the same day, by the author's decision, as no node read it.

- **Statement as used.** $K_\nu(z) = \tfrac12(\tfrac12z)^\nu\int_0^\infty\exp(-t - z^2/(4t))\,t^{-\nu-1}dt$
  at real $z > 0$, every real $\nu$ (the page prints it for $|\mathrm{ph}\,z| < \pi/4$ and no
  condition on $\nu$; narrowed to the real half-line at the skeleton review, M2, the range
  `lem:bessel-k` reads). `lem:bessel-k` spends it at $\nu = 0, 1, d/2$ (its proof reads it at the
  order $-\nu$), and proves from the definition 10.32.9 below what the draft read from the further
  equations 10.29.3, 10.32.8 and 10.30.3; its Lean reaches no axiom.
- **Dropped clause (2), 2026-11-13.** The node stated, and the author first admitted, five further
  equations: $K_0' = -K_1$, $I_0' = I_1$ (10.29.3); the integral over $(1,\infty)$ (10.32.8);
  $K_{\pm1/2}$ (10.39.2); the recurrence 10.29.1; $K_0(z) \sim -\ln z$ (10.30.3). No node and no
  proof read them, so the clause and its axiom were dropped (a safe-direction change); their
  transcriptions stay in `AXIOMS-verbatim.md`.
- **Primary — DLMF 10.32.10.** The library's record `dlmf2026` was created against Version 1.2.7;
  the librarian read 1.2.8, whose equation numbers are stable.
- **DLMF 10.32.9, the definition.** The Lean's $K_\nu$ is the shared core's `besselK`, defined by
  the integral $\int_0^\infty e^{-z\cosh u}\cosh(\nu u)\,du$ at real $z > 0$, which is DLMF 10.32.9
  restricted to the real half-line (transcribed and compared on 2026-11-13, MATCH;
  `AXIOMS-verbatim.md`, A51, the addendum). Clause (1) is proved from that definition, so it rests
  on no citation.
- **What the entry does NOT carry.** $K_\nu$ at complex argument; the exponential
  integral $E_1$ (DLMF 6.2.1), which chapter 4 uses only through its definition.

## A55 — Bernstein's theorem: a completely monotone function on $(0,\infty)$ is the Laplace transform of a measure on $[0,\infty)$
**Blueprint:** `thm:cited-A55` (the interface node, ch. 2). No node spends it since wave 3b (2026-11-15): `prop:thorin-in-dimension-d` (1)–(2) and `prop:matern-increments`(3), its two spenders, are proved without it, from `lem:cm-log-convex`, `lem:cm-exponential-rate` and `lem:cm-uncancelled-atom` (`records/pyramids/PRICE-A55.md`, Route A); the first is [T], the second [A] on A39 only. A55 need not be admitted; A13, A19, A20 and A30 are unspent likewise
**Cite:** @schilling2012bernstein — Theorem 1.4 (Bernstein), printed p. 3
**Verdict:** MATCH (`VERBATIM-literature.md`, A55).

- **Statement as used.** A completely monotone $f : (0,\infty) \to \mathbb{R}$ is
  $f(\lambda) = \int_{[0,\infty)}e^{-\lambda t}\,\mu(dt)$ for a (positive) measure $\mu$ on $[0,\infty)$.
- **Primary — Schilling, Song and Vondraček, Bernstein Functions (2nd ed.), Theorem 1.4, p. 3.**
- **What the entry does NOT carry.** The uniqueness of $\mu$ and the converse, both on the page and
  unused.

## A57 — For a Bernstein function $f$ with $f(0+) = 0$, $e^{-f(|\omega|^2)}$ is the transform of an infinitely divisible law on $\mathbb{R}^d$ in every dimension
**Blueprint:** `thm:cited-A57` (the interface node, ch. 2; stated in chapter 4's prose before `prop:matern-increments`, spent by no node)
**Cite:** @schilling2012bernstein — Theorem 13.14 (Schoenberg; Bochner), printed p. 212, the direction proved by Example 13.13 on the same page, with (13.21) · @sato1999levy — Theorem 30.1 (subordination), printed pp. 197–198
**Verdict:** MISMATCH, mild (`VERBATIM-Sato.md`, A57): a two-source fact. Sato has the mechanism, dimension-free, but not the word "Bernstein", and Brownian motion with triplet $(I,0,0)$ gives $f(|z|^2/2)$; Schilling–Song–Vondraček state the fact (`VERBATIM-literature.md`, A57, MATCH) with a killing caveat, $f(0) > 0$ giving sub-probability measures. Stated here at the second source, with $f(0+) = 0$.

- **Statement as used.** For a Bernstein function $f$ with $f(0+) = 0$, and $f(0) := f(0+) = 0$
  (the value $f(|\omega|^2)$ reads at $\omega = 0$; skeleton review, m6), and every $d \ge 1$,
  $\omega \mapsto f(|\omega|^2)$ is continuous and negative definite on $\mathbb{R}^d$, and
  $e^{-f(|\omega|^2)}$ is the transform of an infinitely divisible probability measure on
  $\mathbb{R}^d$: the measures $\nu^t_d$ of (13.21), of mass $e^{-tf(0)} = 1$, form a convolution
  semigroup, so $\nu^1_d = (\nu^{1/n}_d)^{*n}$.
- **Primary — Schilling, Song and Vondraček, Theorem 13.14, p. 212.** Corroboration: Sato,
  Theorem 30.1, pp. 197–198, with $X$ Brownian motion of transform $e^{-|z|^2/2}$ and the
  subordinator of exponent $u \mapsto f(2u)$, so that (30.6) gives $e^{-f(|z|^2)}$ at time 1.
- **What the entry does NOT carry.** The converse of Theorem 13.14; the killed case $f(0+) > 0$.

## What is deliberately NOT here

The brief's table assigned ids A1–A57. Only the 28 above are entries (27 until review round 3,
batch C, made A15 one); the others are not, and their ids stay unused.

- **Dropped by the librarian's verdicts.** **A2** (V-line Thm. 5.2): the representation matches, but
  the monotonicity of $a$ and $\varpi$ in the scale, the part the draft used it for, is not in the
  theorem (`VERBATIM-V-line.md`, A2); `lem:family-structure` proves it. **A5** (V-line Thm. 7.3 with
  (2.3)): the folded measure $k(v/t)\,dv/v$ is a two-line derivation, not a printed statement;
  `thm:lattice-line` derives it from A4 and A9. **A6** (V-line Lemma 6.1): the group law of the
  $S_\lambda$ is not in it (it is Lemma 6.4(2), p. 30, under full (A8)); the chapters prove what
  they need on $q^{\mathbb{Z}}$. **A10** (V-line Lemma 6.2): it needs full (A8) and a ratio that is
  neither an integer nor the inverse of one; the draft's discrete case (`prop:no-lattice-kernel`
  and its line case) carries its own proof. **A11** (V-line Lemma 4.2 with Prop. 2.8): neither
  states the weak or vague continuity of the Lévy measures in $t$ that the draft used; the chapters
  avoid it. **A25** (V-selection § 4.3): it does not print that a Pólya frequency density has an
  absolutely continuous Lévy measure; `prop:classical-pyramids-approximate-discrete-gaussian`
  proves what it needs of it from A24 and `lem:line-exponent-data`(1) (wave 3b; A39 before).
- **Folded into another entry.** **A8** (V-line display (2.2)) is one statement with A9 on p. 9.
- **Unspent.** No node's status line names **A3, A7, A12, A14, A16, A17, A18, A21, A26, A27,
  A28, A29, A32, A33, A36, A37, A38, A47, A52, A53, A54, A56**: the chapters cite these statements
  in prose, restate and prove what they use, or do not use them. The librarian's readings of them
  stay in the `VERBATIM-*.md` records, so that an entry can be made with its transcription if a
  later revision spends one. Two of them were mismatched against the draft's use: A16 (V-cone
  Lemma 2.7 is about finite sums, the draft needed convergent series) and A18 (the mass of the atom
  train in V-cone Prop. 5.7 is $2\delta_{q^i/c}$, not $\delta_{q^i/c}$).
