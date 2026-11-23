# External reviews of the theory paper

Referee-style reviews of *Spatial scale space from hemigroup axioms: the theory of image pyramids*
(module `pyramids`, `paper/main.tex` with `paper/supplement.tex`), solicited by the author from AI
systems of other vendors than the one that wrote the text, against a frozen build, and kept here
verbatim as provenance (`PROCESS.md` § 9). The author runs `PROMPT-round<N>.md` in each system's
own interface with the PDFs attached and saves the output here unedited, the system and its
reasoning setting in the filename. The article session then checks every finding against the
text, the blueprint and the sources before anything changes, and sorts them in
`../PLAN-review-response-theory.md` (`-round<N>` for later rounds). A review is an input, not a
statement by the author; no finding is acted on because a reviewer asked for it alone.

## Round 1

**The reviewed build** is the tag `pyramids-review-r1`, on the merge of the pass-7 pull request
into `main`: the paper and its supplement after passes 1-3 and 5-7 of `PROCESS.md` § 8. Build:
`cd paper && latexmk -pdf main.tex supplement.tex && latexmk -g -pdf main.tex supplement.tex`.
The PDFs are `review-build-r1-paper.pdf` and `review-build-r1-supplement.pdf` in this directory,
ignored by git and reproducible from the tag. Page references in the reviews are to that build.

**Changed on `main` since the tag** (a finding on these is checked against `main`, not the build):

- The locator of Lindeberg 1990 at `paper/04-line.tex` (§ 4, the sampled Gaussian family) reads
  "Prop. 12 and the remark after it, p. 242" in the journal version. Build r1 has "Prop. 12 and
  the sentence after it" without a page. The number is the same in the journal. Record:
  `../REVIEW-citation-audit-theory-paper.md`, "After the audit".

- § 1.1 named Table 3 where Table 2 maps the axioms to the admitted facts, and Table 3 printed after
  the References (p. 112). Both are fixed on `main` (the response plan's batch 0).

- `PROMPT-round1.md`: the prompt, part A (content) and part B (presentation).
- `review-B-r1-gemini-argon4-high.md`: part B, Gemini Argon 4 at its High setting, saved
  2026-11-22.
- `review-A-r1-gemini-argon4-high.md`: part A, the same system and setting, saved 2026-11-22.
  Both are verified and sorted in `../PLAN-review-response-theory.md`.
- `review-A-r1-<system>-<setting>.md`, `review-B-r1-<system>-<setting>.md`: the outputs, when the
  author has run them.

## Round 2

**The reviewed build** is the tag `pyramids-review-r2`, on the merge of the freeze pull request
into `main`. It is the paper and its supplement after round 1's response, batches 0, 1, 2 and 2b
of `../PLAN-review-response-theory.md`. The build command is the same as round 1's. The PDFs are
`review-build-r2-paper.pdf` (115 pages) and `review-build-r2-supplement.pdf` (46 pages) in this
directory, ignored by git and reproducible from the tag. Page references in the reviews are to
that build.

**Statement numbers changed from round 1.** Lemma 3.4 and Lemma 6.4 are new, so a § 3 statement
from 3.4 on and a § 6 statement from 6.4 on are one higher than in build r1. For example, round 1's
Proposition 3.19 is 3.20, and Proposition 6.6 is 6.7. A round-1 finding is matched to round 2 by
its label, through the response plan.

- `PROMPT-round2.md`: the prompt. It is round 1's with the new numbers and a list of what is new
  in this version.
- `review-A-r2-gpt6.2-astra-ultra.md`: part A, GPT-6.2 Astra at its Ultra setting, saved
  2026-11-23. The system returned a PDF. It is kept beside the text as
  `review-A-r2-gpt6.2-astra-ultra.pdf` and holds the links the text loses. The `.md` is its text,
  extracted by `pdftotext` without its running heads and page numbers, with the headings marked.
  Verified and sorted in `../PLAN-review-response-theory-round2.md`.
- `review-B-r2-<system>-<setting>.md`: part B, when the author has run it.

## Round 3

**The reviewed build** is the tag `pyramids-review-r3`, on the merge of the freeze pull request
into `main`. It is the paper and its supplement after round 2's response, batches A, B and C of
`../PLAN-review-response-theory-round2.md`. The build command is the same as round 1's. The PDFs
are `review-build-r3-paper.pdf` (119 pages) and `review-build-r3-supplement.pdf` (46 pages) in this
directory, ignored by git and reproducible from the tag. Page references in the reviews are to
that build.

**Statement numbers changed from round 2.** Propositions 5.21, 6.6 and 6.16 are new. Round 2's
Propositions 6.6 to 6.14 are 6.7 to 6.15, and its 6.15 to 6.19 are 6.17 to 6.21; § 5 up to 5.20, § 3
and the supplement keep their numbers. For example, round 2's Proposition 6.7 is 6.8. A finding of
an earlier round is matched to round 3 by its label, through the response plans and `CHANGELOG.md`.

- `PROMPT-round3.md`: the prompt. It is round 2's with the new numbers, Proposition 6.6 among the
  claims and the steps proved in print only, and a list of what is new in this version.
- `review-A-r3-fable5.2-max-<block>.md`: part A, Claude Fable 5.2 at its highest effort, one file
  per block of sections (`s1-3`, `s4-5`, `s6-7-appendix`, `supplement`). This is the author's
  choice, since the external systems available were used in rounds 1 and 2, and it is a
  same-vendor read (`PROMPT-round3.md` says how it was kept blind). Saved 2026-11-23, verified and
  sorted in `../PLAN-review-response-theory-round3.md`.
- `r3-verification/`: the four verifiers' verdicts, condensed by the article session, one file per
  block. `LIBRARIAN-r3.md`: the librarian's answers to the source questions the reviews raised, read
  from held copies.
