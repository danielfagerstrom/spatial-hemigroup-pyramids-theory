# Citation audit of the theory paper (pass 7)

`PROCESS.md` § 8, pass 7, on `paper/main.tex` and `paper/supplement.tex` (module `pyramids`),
2026-11-22, on the text as pass 6 left it (`d898c29`). Every citation was read against the copy the
library holds, by agents that did not write the sentences.

## How it was done

- **Inventory.** A script listed every citation of the paper and the supplement, comments stripped:
  `[\sscite{key}, locator]`, `\cite[locator]{key}`, `\prog{module}{locator}` and the bare forms.
  194 citations, 150 with a locator, of 22 sources (`citation-audit-theory/inventory.json`).
- **Checks.** Six sonnet agents, one per group of sources, each with the brief
  `citation-audit-theory/BRIEF.md`: locator, support, and hypothesis by hypothesis for every statement
  of § 2 that restates a source. Page images were read for every scan and every formula (Sato, Karlin,
  Stein, Bondesson, Burt, Burt–Adelson, Collatz, Kovačević–Vetterli). The agents' writes to the
  repository were refused ("subagents return findings as text"); the session saved each returned
  table unchanged as `citation-audit-theory/findings-<group>.md`. Two blueprint citations of the
  selection paper without a page (rows X1, X2) were checked with them.
- **Sweep.** The librarian looked for the sources of the five `TODO(citation sweep)` comments and the
  open anchors, read each locator from a held copy, and queued what is not held.
- **The session's own checks.** Where an agent's finding changed a locator to a new place, or two
  agents disagreed, the session read the page image itself: Sato p. 120 (Thm. 19.2(i)), Karlin
  p. 345 (Thm. 3.2(a)), the isotropic paper pp. 11, 12, 14.

## Result

**No citation fails to support its sentence, and no restatement claims more than its source.**
Nothing went to the author as critical.

| verdict | count |
|---|---|
| OK | 157 |
| MINOR (a page that should be a range, a better locator, wording) | 32 |
| LOCATOR (a wrong page or item) | 6 |
| HYPOTHESIS (the paper claims less than the source) | 1 |
| UNSUPPORTED | 0 |

The six wrong locators, all fixed: the isotropic paper's Lemma 3.3 (pp. 11-12, not p. 11); Sato's
jump rate (Thm. 19.2(i), p. 120, not Thm. 8.1); the selection paper's Thm. 4.2(3) (p. 31, not p. 30,
twice) and its § 6 remark on the plane (p. 69, not p. 67, twice).

The one HYPOTHESIS row (C040) is left: `thm:cited-A31` asks `F' ∈ 𝒜_d` in its uniqueness clause where
the isotropic paper's Thm. 3.6 allows any real `F'` with `F'(0) = 0`; the paper claims less, as its
formal statement does.

Of the 32 MINOR rows, 28 were fixed. C186 was settled by the session's reading of Karlin (no
change), C034 and C112 need none, and C115 waits on the journal copy (below). Seventeen OK rows
also got a locator, or a more exact one, where a reader is helped (C011, C012, C013, C016, C019,
C057, C064, C089, C114, C118, C120, C142, C149, C154, C171, X1, X2).

## What changed

- **Locators** in the blueprint (`02-cited-facts`, `02-line`, `03-pyramid`, `04-matern`, `05-price`,
  `A1-line`, and the same citations in `07-computation` and `08-jet`), re-transcribed into the paper,
  the supplement and the computation paper; `linkage check` reports every shared statement verbatim.
  Prose locators in the paper's own text.
- **Wording**, where the source says less or other than the sentence: "kernels ... other than
  `δ_0`" with the isotropic paper's Cor. 3.9(1); "three changes" from the isotropic axioms in § 6
  (the relabelling fixed to `t ↦ qt` and (ND) required only of the octave step); Lindeberg's
  characterization with its hypotheses (symmetric, normalized, up to a constant in scale); the
  quincunx neighbour as a filter bank, not a pyramid; Karlin's strip "containing the imaginary axis,
  on which `L` exists"; DLMF 10.32.9 as a representation; the A49 sentence read at time 1; the
  ScaleSpaceCore tag as a later tag of the core first released with the line paper (the line paper
  pins v0.2.0).
- **The five `TODO(citation sweep)` comments are settled**, each with a held source and its locator:
  - the classical semigroup axiom: Duits, Florack, de Graaf and ter Haar Romeny 2004 (§ 3, Axiom 6,
    p. 270), Lindeberg 1994 (§ 2.4.4, p. 41); Iijima's weaker composition axiom through Weickert,
    Ishikawa and Imiya 1999 (§ 3, p. 241). Koenderink 1984 states no semigroup axiom and is not cited
    for it.
  - other pyramids: Crowley's √2 resampling (thesis 1981, § 3.3.2, p. 32), Lindeberg and Bretzner's
    hybrid pyramids (2003, § 3.1), the polynomial spline pyramids of Unser, Aldroubi and Eden (1993,
    § IV.B, p. 370). Crowley's resampling turns the lattice, so it also joins the discussion's list of
    rotating dilations.
  - creation in the plane: Lifshitz and Pizer's example as Lindeberg 1994 gives it (§ 4.1, p. 101),
    and Damon 1995 (p. 369); also cited in § 5.
  - "refinable": Cavaretta, Dahmen and Micchelli 1991, (1.7), pp. 4-5.
  - the refinement equation in transforms: the same memoir, Ch. 6, p. 107 (at `q = 2`, with a mask
    of sum `2^d`), and p. 5 for wavelet theory.
- **New in `references.bib`:** `lindeberg1994scale`, `weickert1999linear`, `duits2004axioms`,
  `crowley1981representation`, `lindeberg2003real`, `unser1993polynomial`,
  `damonLocalMorseTheory1995`, `cavaretta1991stationary`; `lindeberg1990scalespace`'s entry
  corrected (author, journal, issue, pages).
- **Blueprint only:** the selection paper's Thm. 3.3 (p. 16) and Prop. 3.8 (p. 24) in `02-line`
  (HANDOFF's open anchors).

## The library

Fixed by the librarian: the metadata of `damonLocalMorseTheory1995`, `lindeberg1990scalespace` and
`cavaretta1991stationary` (now a book in the AMS Memoirs); the stale "preprint" notes of
`hanke1998nonstationary` and `lindgren2011explicit`; the page offsets of `burt1981fast` (+19),
`burt1983laplacian` (+531), `kovacevic1992nonseparable` (+532), `collatz1960numerical` (−16) and
`kallenberg2021foundations` (−3).

**Queued for acquisition by the audit**, all held since 2026-11-22 (see "After the audit"):

| citekey | what | why |
|---|---|---|
| `lifshitz1990multiresolution` | Lifshitz and Pizer, IEEE PAMI 1990 | the creation example, now cited through Lindeberg 1994 |
| `kuijper2004relevance` | Kuijper and Florack, IJCV 2004 (identity to verify) | creation of extrema in 2-D scale space; not needed by any sentence now |
| `crowley1984fast` | Crowley and Stern, IEEE PAMI 1984 | the DOLP transform; the thesis is cited now |
| `daubechies1992ten` | Daubechies, Ten Lectures on Wavelets | the refinement equation; the memoir is cited now |

## Left open

- The library's `lindgren2011explicit` has a second attachment and its primary is flagged
  "contested"; the held copy read here is the journal version.
- DLMF is held as a Ch. 6 markdown file only; 10.32.9 and 10.32.10 were read on dlmf.nist.gov.

## After the audit

On 2026-11-22, after build r1 was frozen at `pyramids-review-r1`, the author added the journal
version of Lindeberg 1990 (TPAMI 12(3), 234-254) to the library. Its pages 240 and 242 were read
as page images, and C115 is closed:

- **C115** (`paper/04-line.tex`, blueprint `02-line.tex`, the sampled Gaussian family): the
  journal's Proposition 12 on p. 242 is the report's Prop. 12. It says that the sampled Gaussian
  representation is a scale-space transformation from $t_1$ to $t_2$ iff $t_1 = 0$ or $t_2/t_1$ is
  an odd integer. The remark after its proof attributes this to the semigroup property of the
  Gaussian kernel not being preserved after discretization. The number stands. The locator now
  reads "Prop. 12 and the remark after it, p. 242", because the remark is two sentences.
- The blueprint's proof note in `02-line.tex` (the kernels of stratum 1, not transcribed) cited
  "the report, Thm. 4 and eq. (28)". It now cites Lindeberg's paper, Thm. 4, pp. 240-241, and
  eq. (28), p. 242. The journal's Theorem 4 gives $T(n;t) = e^{-\alpha t} I_n(\alpha t)$ from the
  semigroup law and non-creation, and its (28) is the semi-discretized diffusion equation.
- No other citation of Lindeberg 1990 carries a locator.

Build r1 has the old wording. `reviews/README.md` lists it for the review response.

The library: the author then acquired the four other queued items. Each has its metadata from
Crossref (DOI, venue, volume, pages; Daubechies also has its ISBN). Each attachment was checked
against its first page, and its printed pages resolve:
- `lifshitz1990multiresolution`: TPAMI 12(6), 529-540, 1990, with page offset 528 set;
- `kuijper2004relevance`: IJCV 57(1), 67-84, 2004, "The relevance of non-generic events in scale
  space models", which is not the ECCV 2002 version;
- `crowley1984fast`: TPAMI PAMI-6(2), 212-222, 1984;
- `daubechies1992ten`: SIAM 1992, CBMS-NSF 61.

No sentence of the paper cites them now. The To Acquire queue is empty. The CVAP report is still
attached to `lindeberg1990scalespace` as a second file, so `resolve` flags the item "contested".

## Every citation

The ids are the inventory's; "where" and "locator" are as audited, before the fixes. X1 and X2 are
the blueprint's two citations of the selection paper without a page.

| id | where (as audited) | key | locator (as audited) | verdict | fix |
|----|-------|-----|---------|---------|-----|
| C001 | 01-introduction.tex:8 | burt1981fast | (none) | OK | none |
| C002 | 01-introduction.tex:8 | burt1983laplacian | (none) | OK | none |
| C003 | 01-introduction.tex:10 | burt1983laplacian | p.~533 | OK | none |
| C004 | 01-introduction.tex:11 | meer1987frequency | (none) | OK | none |
| C005 | 01-introduction.tex:12 | burt1981fast | (none) | OK | none |
| C006 | 01-introduction.tex:19 | lindeberg1990scalespace | (none) | OK | none |
| C007 | 01-introduction.tex:26 | fagerstrom2026spatial | Thm.~7.3, p.~37 | OK | none |
| C008 | 01-introduction.tex:27 | fagerstrom2026isotropic | Thm.~3.6, p.~13 | OK | none |
| C009 | 01-introduction.tex:46 | fagerstrom2026selection | \S4 | OK | none |
| C010 | 01-introduction.tex:185 | hanke1998nonstationary | pp.~38--39 | OK | none |
| C011 | 01-introduction.tex:186 | radmoser2000scale | (none) | OK | p. 98 |
| C012 | 01-introduction.tex:186 | farbman2008edge | (none) | OK | §3.1, (13)-(14) |
| C013 | 01-introduction.tex:188 | burt1981fast | (none) | OK | §4, p. 29 (also the computation paper's introduction) |
| C014 | 01-introduction.tex:190 | maejima1998semi | Def.~3.1, p.~19 | OK | none |
| C015 | 01-introduction.tex:190 | sato1999levy | Def.~15.1, p.~90 | OK | none |
| C016 | 01-introduction.tex:191 | mallat1989theory | (none) | OK | (2)-(8), p. 676 |
| C017 | 01-introduction.tex:193 | lindeberg1990scalespace | (none) | OK | none |
| C018 | 01-introduction.tex:195 | whittle1954stationary | ; \sscite{lindgren2011explicit}, (2) | MINOR | Whittle p. 448; Lindgren (2), p. 426 |
| C019 | 01-introduction.tex:195 | lindgren2011explicit | (none) | OK | p. 426 |
| C020 | 01-introduction.tex:245 | fagerstrom2026spatial | (none) | MINOR | reworded: the core first released with the line paper, here at its later tag v0.5.0 |
| C021 | 01-introduction.tex:250 | fagerstrom2026affine | (none) | OK | none |
| C022 | 01-introduction.tex:257 | sato1999levy | (none) | OK | none |
| C023 | 01-introduction.tex:264 | fagerstrom2026selection | (none) | OK | none |
| C024 | 02-cited-facts.tex:6 | fagerstrom2026spatial | (none) | OK | none |
| C025 | 02-cited-facts.tex:8 | fagerstrom2026cone | (none) | OK | none |
| C026 | 02-cited-facts.tex:10 | fagerstrom2026selection | (none) | OK | none |
| C027 | 02-cited-facts.tex:11 | fagerstrom2026isotropic | (none) | OK | none |
| C028 | 02-cited-facts.tex:12 | fagerstrom2026affine | (none) | OK | none |
| C029 | 02-cited-facts.tex:64 | fagerstrom2026spatial | Lemma~4.1, pp.~22--23 | OK | none |
| C030 | 02-cited-facts.tex:81 | fagerstrom2026spatial | Lemma~4.1, p.~22 | OK | none |
| C031 | 02-cited-facts.tex:113 | fagerstrom2026spatial | Thm.~5.2, p.~26 | OK | none |
| C032 | 02-cited-facts.tex:118 | fagerstrom2026spatial | Prop.~2.3(3), p.~9 | OK | none |
| C033 | 02-cited-facts.tex:162 | sato1999levy | Def.~15.1, p.~90 | OK | none |
| C034 | 02-cited-facts.tex:187 | fagerstrom2026spatial | Prop.~2.13, p.~13 | MINOR | left (optional) |
| C035 | 02-cited-facts.tex:189 | fagerstrom2026spatial | Thm.~7.3, p.~37 | OK | none |
| C036 | 02-cited-facts.tex:215 | fagerstrom2026cone | Lemma~2.7, p.~12 | OK | none |
| C037 | 02-cited-facts.tex:251 | fagerstrom2026isotropic | Def.~3.1, pp.~10--11 | OK | none |
| C038 | 02-cited-facts.tex:252 | fagerstrom2026isotropic | Lemma~3.3(1)--(2), p.~11 | LOCATOR | Lemma 3.3, pp. 11-12 |
| C039 | 02-cited-facts.tex:278 | fagerstrom2026isotropic | Prop.~2.6, p.~8 | OK | none |
| C040 | 02-cited-facts.tex:279 | fagerstrom2026isotropic | Thm.~3.6, p.~13 | HYPOTHESIS (minor) | left: the restatement claims less than the source (F' in A_d), as its formal statement does |
| C041 | 02-cited-facts.tex:299 | fagerstrom2026isotropic | \S~3.2, p.~12 | OK | none |
| C042 | 02-cited-facts.tex:301 | fagerstrom2026isotropic | Lem.~3.8, p.~14 | OK | none |
| C043 | 02-cited-facts.tex:342 | fagerstrom2026isotropic | Prop.~3.11(1)--(2),
pp.~15--16 | OK | none |
| C044 | 02-cited-facts.tex:407 | fagerstrom2026cone | Prop.~6.2, display (6.2), p.~56 | OK | none |
| C045 | 02-cited-facts.tex:410 | fagerstrom2026cone | Lemma~3.1(1), p.~13 | OK | none |
| C046 | 02-cited-facts.tex:411 | fagerstrom2026cone | Prop.~6.4(5), p.~58 | OK | none |
| C047 | 02-cited-facts.tex:437 | fagerstrom2026spatial | Remark~6.7, pp.~32--33 | OK | none |
| C048 | 02-cited-facts.tex:438 | fagerstrom2026cone | \S~4, p.~24 | OK | none |
| C049 | 02-cited-facts.tex:440 | fagerstrom2026cone | Prop.~5.7, p.~48 | OK | none |
| C050 | 02-cited-facts.tex:441 | fagerstrom2026selection | Thm.~4.2, p.~30 | MINOR | pp. 30-31 (blueprint and paper) |
| C051 | 02-cited-facts.tex:444 | fagerstrom2026selection | Thm.~4.10, p.~43 | OK | none |
| C052 | 02-cited-facts.tex:446 | fagerstrom2026selection | Prop.~5.6, p.~60 | OK | none |
| C053 | 02-cited-facts.tex:447 | fagerstrom2026selection | \S~6, p.~67 | LOCATOR | p. 69 (blueprint and paper) |
| C054 | 02-cited-facts.tex:448 | fagerstrom2026isotropic | Prop.~3.12, pp.~16--17 | OK | none |
| C055 | 02-cited-facts.tex:450 | fagerstrom2026isotropic | Prop.~3.22, p.~27 | OK | none |
| C056 | 02-cited-facts.tex:452 | fagerstrom2026affine | Prop.~F.1, p.~93 | OK | none |
| C057 | 02-cited-facts.tex:506 | karlin1968total | (none) | OK | Ch. 7, §1, p. 332 |
| C058 | 02-cited-facts.tex:558 | fagerstrom2026isotropic | Prop.~3.12(2), p.~16 | OK | none |
| C059 | 02-cited-facts.tex:560 | fagerstrom2026cone | Prop.~5.2(2), p.~43 | OK | none |
| C060 | 02-cited-facts.tex:565 | sato1999levy | (none) | MINOR | (13.8), p. 75 |
| C061 | 02-cited-facts.tex:588 | sato1999levy | (none) | OK | none |
| C062 | 02-cited-facts.tex:589 | karlin1968total | (none) | OK | none |
| C063 | 02-cited-facts.tex:590 | dlmf2026 | (none) | OK | none |
| C064 | 02-cited-facts.tex:592 | schilling2012bernstein | (none) | OK | Def. 6.1, p. 69 and Def. 8.1, p. 109 at the two definitions (blueprint and paper) |
| C065 | 02-cited-facts.tex:604 | sato1999levy | Thm.~8.1(i)--(iii), pp.~37--38 | OK | none |
| C066 | 02-cited-facts.tex:605 | sato1999levy | Def.~8.2, p.~38 | OK | none |
| C067 | 02-cited-facts.tex:630 | sato1999levy | Lemma~7.5,
p.~32 | OK | none |
| C068 | 02-cited-facts.tex:642 | sato1999levy | Thm.~9.3, p.~47 | OK | none |
| C069 | 02-cited-facts.tex:658 | sato1999levy | Prop.~11.10, p.~65 | OK | none |
| C070 | 02-cited-facts.tex:677 | sato1999levy | Prop.~15.5, p.~93 | OK | none |
| C071 | 02-cited-facts.tex:678 | sato1999levy | Thm.~15.8, p.~94 | OK | none |
| C072 | 02-cited-facts.tex:753 | sato1999levy | Thm.~15.10, p.~95 | OK | none |
| C073 | 02-cited-facts.tex:770 | sato1999levy | Cor.~24.4, p.~149 | OK | none |
| C074 | 02-cited-facts.tex:771 | sato1999levy | Cor.~24.6, p.~149 | OK | none |
| C075 | 02-cited-facts.tex:791 | sato1999levy | Thm.~25.3, p.~159 | MINOR | "printed there for a Lévy process and read here for its law at time 1" added |
| C076 | 02-cited-facts.tex:806 | sato1999levy | Prop.~25.4(iii), p.~159 | OK | none |
| C077 | 02-cited-facts.tex:832 | schilling2012bernstein | Thm.~3.2,
p.~21 | OK | none |
| C078 | 02-cited-facts.tex:860 | schilling2012bernstein | Thm.~1.4, p.~3 | OK | none |
| C079 | 02-cited-facts.tex:874 | schilling2012bernstein | Thm.~13.14, p.~212 | OK | none |
| C080 | 02-cited-facts.tex:877 | sato1999levy | Thm.~30.1,
pp.~197--198 | OK | none |
| C081 | 02-cited-facts.tex:894 | karlin1968total | Ch.~7, Thm.~3.2(a),
p.~345 | OK | none |
| C082 | 02-cited-facts.tex:895 | karlin1968total | (2.2), p.~336 | OK | none |
| C083 | 02-cited-facts.tex:898 | karlin1968total | Prop.~1.4,
p.~333 | MINOR | reworded: a strip containing the imaginary axis, on which L exists (paper; blueprint ledger note) |
| C084 | 02-cited-facts.tex:920 | dlmf2026 | 10.32.9 | MINOR | "given by" in place of "defined by" |
| C085 | 02-cited-facts.tex:920 | dlmf2026 | 10.32.10 | OK | none |
| C086 | 03-pyramid.tex:88 | fagerstrom2026isotropic | Def.~3.2, p.~11 | OK | none |
| C087 | 03-pyramid.tex:209 | sato1999levy | Thm.~8.1, pp.~37--38 | LOCATOR | Thm. 19.2(i), p. 120 (the session read the page image) |
| C088 | 03-pyramid.tex:393 | sato1999levy | Def.~15.1, p.~90 | OK | none |
| C089 | 03-pyramid.tex:397 | fagerstrom2026spatial | Thm.~7.3, p.~37 | OK | "at positive scales ... other than δ0"; Prop. 2.13, p. 13 added |
| C090 | 03-pyramid.tex:398 | fagerstrom2026isotropic | Thm.~3.6, p.~13 | MINOR | Cor. 3.9(1), p. 14, "other than δ0" |
| C091 | 03-pyramid.tex:403 | maejima1998semi | Def.~3.1, p.~19 | MINOR | Thm. 3.1(i), p. 20 added (blueprint and paper) |
| C092 | 03-pyramid.tex:412 | sato1999levy | Prop.~15.5, p.~93 | MINOR | "the sentence after its proof" |
| C093 | 03-pyramid.tex:416 | sato1999levy | Thm.~15.8,
p.~94 | OK | none |
| C094 | 03-pyramid.tex:605 | fagerstrom2026isotropic | Thm.~3.6, p.~13 | OK | none |
| C095 | 03-pyramid.tex:712 | lindeberg1990scalespace | (none) | OK | none |
| C096 | 03-pyramid.tex:812 | fagerstrom2026isotropic | \S~3.2, p.~12 | OK | none |
| C097 | 03-pyramid.tex:855 | fagerstrom2026isotropic | Thm.~3.6, p.~13 | OK | none |
| C098 | 03-pyramid.tex:962 | fagerstrom2026isotropic | Prop.~2.6, p.~8 | OK | none |
| C099 | 03-pyramid.tex:963 | fagerstrom2026isotropic | Prop.~3.22(2), p.~27 | OK | none |
| C100 | 03-pyramid.tex:1114 | burt1981fast | (2)--(4), pp.~21--23 | OK | none |
| C101 | 03-pyramid.tex:1116 | burt1983laplacian | p.~533 | OK | none |
| C102 | 03-pyramid.tex:1119 | burt1981fast | Obs.~1, p.~24, and (5), p.~25 | OK | none |
| C103 | 03-pyramid.tex:1261 | sato1999levy | Prop.~25.4(iii),
p.~159 | OK | none |
| C104 | 03-pyramid.tex:1334 | fagerstrom2026isotropic | Prop.~3.11(1)--(2), pp.~15--16 | OK | none |
| C105 | 03-pyramid.tex:1354 | fagerstrom2026isotropic | Lem.~3.8, p.~14 | OK | none |
| C106 | 03-pyramid.tex:1459 | burt1983laplacian | p.~533 | OK | none |
| C107 | 03-pyramid.tex:1461 | burt1981fast | p.~24 | OK | none |
| C108 | 03-pyramid.tex:1492 | burt1981fast | Obs.~1, p.~24 | OK | none |
| C109 | 03-pyramid.tex:1556 | maejima1998semi | Rem.~3.1, p.~19 | MINOR | pp. 19-20 (blueprint and paper) |
| C110 | 04-line.tex:190 | maejima1998semi | (none) | OK | none |
| C111 | 04-line.tex:208 | lindeberg1990scalespace | (none) | OK | none |
| C112 | 04-line.tex:271 | fagerstrom2026cone | Prop.~7.5(2), p.~65 | MINOR | left (optional) |
| C113 | 04-line.tex:533 | burt1983laplacian | p.~533 | OK | none |
| C114 | 04-line.tex:570 | fagerstrom2026cone | Prop.~7.2, p.~60 | OK | pp. 60-61 (blueprint 02-line, 07, 08; paper; computation paper) |
| C115 | 04-line.tex:992 | lindeberg1990scalespace | Prop.~12 and the sentence after it | MINOR | after the audit: the journal's Prop. 12 is the same; the locator now reads "Prop. 12 and the remark after it, p. 242" (blueprint and paper) |
| C116 | 04-line.tex:1020 | fagerstrom2026cone | (none) | OK | none |
| C117 | 04-line.tex:1023 | fagerstrom2026cone | Lemma~3.1(1), p.~13 | OK | none |
| C118 | 05-matern.tex:81 | stein1970singular | Ch.~V, \S 3.1, (26) and Prop.~2, p.~132 | OK | §3 in place of §3.1 (blueprint and paper) |
| C119 | 05-matern.tex:85 | whittle1954stationary | ; \sscite{lindgren2011explicit}, (2) | MINOR | as C018 |
| C120 | 05-matern.tex:85 | lindgren2011explicit | (none) | OK | p. 426 |
| C121 | 05-matern.tex:87 | fagerstrom2026isotropic | Prop.~3.12(2), p.~16 | OK | none |
| C122 | 05-matern.tex:243 | dlmf2026 | (none) | OK | none |
| C123 | 05-matern.tex:380 | fagerstrom2026isotropic | Prop.~3.11(1)--(2), p.~15 | MINOR | pp. 15-16 (blueprint and paper; also blueprint 04-matern:462) |
| C124 | 05-matern.tex:382 | fagerstrom2026isotropic | Lem.~3.8, p.~14 | OK | none |
| C125 | 05-matern.tex:437 | fagerstrom2026isotropic | Thm.~3.6, p.~13 | OK | none |
| C126 | 05-matern.tex:474 | fagerstrom2026selection | Prop.~4.5(2), p.~35 | OK | none |
| C127 | 05-matern.tex:568 | fagerstrom2026isotropic | Prop.~3.11(1)--(2), p.~15 | MINOR | pp. 15-16 (blueprint and paper) |
| C128 | 05-matern.tex:610 | fagerstrom2026cone | \S 4 | MINOR | §4.2, p. 26 (paper and blueprint 04-matern) |
| C129 | 05-matern.tex:616 | lindeberg2016time | Sect.~5, (38), p.~62 | OK | none |
| C130 | 05-matern.tex:617 | lindeberg2016time | Sect.~6.2, p.~64 | OK | none |
| C131 | 05-matern.tex:815 | sato1999levy | Thm.~8.1(ii), p.~38 | OK | none |
| C132 | 05-matern.tex:829 | sato1999levy | Thm.~8.1(iii), p.~38 | OK | none |
| C133 | 05-matern.tex:941 | bondesson1992generalized | \S 3.1, p.~30 | MINOR | pp. 29-30 (blueprint and paper) |
| C134 | 05-matern.tex:1138 | fagerstrom2026selection | Prop.~5.6(1), p.~60 | OK | none |
| C135 | 05-matern.tex:1141 | burt1983laplacian | p.~535 | OK | none |
| C136 | 05-matern.tex:1211 | fagerstrom2026selection | \S 6 | MINOR | p. 69; Lindeberg 1994, §4.1, p. 101 added |
| C137 | 05-matern.tex:1535 | fagerstrom2026selection | Thm.~4.2(3), p.~30 | LOCATOR | p. 31 (blueprint and paper) |
| C138 | 05-matern.tex:1544 | fagerstrom2026selection | Thm.~4.2(3) and Cor.~4.4, pp.~30, 33 | LOCATOR | pp. 31, 33 |
| C139 | 06-price.tex:205 | fagerstrom2026isotropic | Def.~3.2, p.~11 | MINOR | "three changes": the fixed relabelling and (ND) named |
| C140 | 06-price.tex:431 | burt1983laplacian | p.~533 | OK | none |
| C141 | 06-price.tex:1460 | whittle1954stationary | ; \sscite{lindgren2011explicit}, (2) | MINOR | as C018 (paper and blueprint 05-price) |
| C142 | 06-price.tex:1460 | lindgren2011explicit | (none) | OK | p. 426 |
| C143 | 06-price.tex:1484 | collatz1960numerical | Ch.~V \S 2.5, p.~386 | OK | none |
| C144 | 07-discussion.tex:7 | burt1983laplacian | p.~533 | OK | none |
| C145 | 07-discussion.tex:7 | meer1987frequency | (none) | OK | none |
| C146 | 07-discussion.tex:36 | fagerstrom2026isotropic | Thm.~3.6, p.~13 | OK | none |
| C147 | 07-discussion.tex:37 | lindeberg1990scalespace | (none) | OK | none |
| C148 | 07-discussion.tex:41 | fagerstrom2026selection | \S4 | OK | none |
| C149 | 07-discussion.tex:48 | burt1983laplacian | (none) | OK | p. 535 |
| C150 | 07-discussion.tex:52 | hanke1998nonstationary | pp.~38--39 | OK | none |
| C151 | 07-discussion.tex:72 | burt1983laplacian | p.~533 | MINOR | pp. 533-534 |
| C152 | 07-discussion.tex:88 | fagerstrom2026selection | \S4 | OK | none |
| C153 | 07-discussion.tex:102 | kovacevic1992nonseparable | (none) | MINOR | reworded: "the quincunx filter banks, whose dilation matrix squares to 2I", (2), p. 534 |
| C154 | 07-discussion.tex:103 | watson1989hexagonal | (none) | OK | pp. 97, 99 |
| C155 | appendix-verification.tex:22 | fagerstrom2026spatial | (none) | MINOR | as C020 (Appendix A) |
| C156 | appendix-verification.tex:23 | fagerstrom2026affine | (none) | OK | none |
| C157 | supp-line.tex:131 | fagerstrom2026spatial | Remark~6.7, pp.~32--33 | OK | none |
| C158 | supp-line.tex:194 | maejima1999semi | Thm.~7, p.~361 | OK | none |
| C159 | supp-line.tex:240 | fagerstrom2026spatial | Thm.~7.3, p.~37 | OK | none |
| C160 | supp-line.tex:682 | fagerstrom2026cone | Prop.~6.4(5), p.~58 | OK | none |
| C161 | supp-line.tex:849 | fagerstrom2026cone | Prop.~3.3, pp.~15--16 | OK | none |
| C162 | supp-line.tex:994 | sato1999levy | Prop.~15.5, p.~93 | OK | none |
| C163 | supp-line.tex:1182 | kallenberg2021foundations | Thm.~9.27, p.~200 | OK | none |
| C164 | supp-line.tex:2098 | burt1981fast | pp.~23--24 | OK | none |
| C165 | supp-line.tex:2109 | burt1983laplacian | p.~533 | OK | none |
| C166 | supp-line.tex:2111 | fagerstrom2026affine | Prop.~F.1, p.~93 | OK | none |
| C167 | supp-line.tex:2113 | burt1983laplacian | p.~533 | MINOR | pp. 533-534 (blueprint and supplement) |
| C168 | supp-line.tex:2244 | fagerstrom2026spatial | Thm.~7.3, p.~37 | OK | none |
| C169 | supp-line.tex:2349 | fagerstrom2026cone | Prop.~5.7, (5.1), p.~48 | OK | none |
| C170 | supp-line.tex:2350 | fagerstrom2026cone | Prop.~6.4(4), p.~58 | OK | none |
| C171 | supp-line.tex:2353 | burt1983laplacian | (none) | OK | p. 535 |
| C172 | supp-line.tex:2362 | lindeberg2016time | Sect.~5, (38), p.~62 | OK | none |
| C173 | supp-line.tex:2363 | lindeberg2016time | Sect.~6.2, p.~64 | OK | none |
| C174 | supp-line.tex:2383 | fagerstrom2026selection | Prop.~4.5(1), p.~35 | OK | none |
| C175 | supp-line.tex:2420 | fagerstrom2026selection | Remark~4.15 | MINOR | pp. 50-51 (blueprint and supplement) |
| C176 | supp-line.tex:2421 | fagerstrom2026selection | Thm.~4.2(2), p.~30 | OK | none |
| C177 | supp-line.tex:2423 | fagerstrom2026selection | Prop.~4.5, p.~35 | OK | none |
| C178 | supp-line.tex:2424 | fagerstrom2026selection | Thm.~4.2(3), Cor.~4.4 | MINOR | pp. 31, 33 (blueprint and supplement) |
| C179 | supp-line.tex:2425 | fagerstrom2026selection | Thm.~4.10, p.~43 | OK | none |
| C180 | supp-line.tex:2486 | fagerstrom2026selection | Prop.~4.5(1), p.~35 | OK | none |
| C181 | supp-line.tex:2493 | fagerstrom2026selection | Prop.~4.5(2), p.~35 | OK | none |
| C182 | supp-line.tex:2506 | fagerstrom2026selection | \S~6, p.~67 | LOCATOR | p. 69 (blueprint and supplement) |
| C183 | supp-line.tex:2616 | lindeberg1990scalespace | (none) | MINOR | the hypotheses added: symmetric, normalized, up to a constant in scale (blueprint and supplement) |
| C184 | supp-line.tex:2617 | fagerstrom2026selection | Remark~4.15 | MINOR | p. 51 (blueprint and supplement) |
| C185 | supp-line.tex:2643 | karlin1968total | Ch.~7, Thm.~3.2(a),
p.~345 | OK | none |
| C186 | supp-line.tex:2644 | fagerstrom2026selection | \S~4.3, pp.~34--35 | MINOR | none: the session read Karlin p. 345, the condition is in both directions |
| C187 | supp-line.tex:2669 | mallat1989theory | (2)--(8), p.~676 | OK | none |
| C188 | supp-line.tex:2684 | meer1987frequency | (none) | OK | none |
| C189 | supp-strata.tex:47 | sato1999levy | Thm.~8.1(iii),
pp.~37--38 | MINOR | p. 38 (blueprint A1 and supplement) |
| C190 | supp-strata.tex:49 | sato1999levy | Thm.~8.1(ii),
p.~38 | OK | none |
| C191 | supp-strata.tex:226 | fagerstrom2026spatial | Prop.~2.3(3), p.~9 | OK | none |
| C192 | supp-strata.tex:257 | fagerstrom2026spatial | Prop.~2.3(3), p.~9 | OK | none |
| C193 | supp-strata.tex:298 | lindeberg1990scalespace | (none) | OK | none |
| C194 | supp-strata.tex:347 | sato1999levy | Thm.~15.8, p.~94 | OK | none |
| X1 | blueprint 02-line | fagerstrom2026selection | Thm.~3.3 | OK | p. 16 (blueprint 02-line) |
| X2 | blueprint 02-line | fagerstrom2026selection | Prop.~3.8 | OK | p. 24 (blueprint 02-line) |
