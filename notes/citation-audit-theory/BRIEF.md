# Brief for the citation checkers (pass 7, theory paper)

The theory paper of Paper VI (`paper/main.tex` and `paper/supplement.tex`) cites its sources as
`[\sscite{key}, locator]`, `\cite[locator]{key}`, or `\prog{<module> v0.1}{locator}` (the author's
released earlier modules: `V-line v0.1` = `fagerstrom2026spatial`, `V-cone v0.1` =
`fagerstrom2026cone`, `V-selection v0.1` = `fagerstrom2026selection`, `iso v0.1` =
`fagerstrom2026isotropic`, `affine v0.1` = `fagerstrom2026affine`). Your input file lists the
citations of your group, each with an id, the file and line under `paper/`, the citekey, the locator
as printed, and the paragraph around it (comments stripped).

You did not write these sentences. Read each against the copy the library holds, never from memory,
and never from this repository's earlier records (`READING-*`, `VERBATIM-*`, `CITATION-CHECK-*`):
this pass exists to check them independently.

## How to read a source

- `library resolve <key> --json` (artifacts, page offset), `library toc <key>`,
  `library search <key> "<query>"` (hits come with printed pages), `library page <key> --printed N`
  (text), `library get <key> --format md` (the markdown, where stored), `library get <key> --pages a-b`.
- **For a scanned page, or any page where the statement has inequalities, Greek letters, signs or
  indices, read the page image**: `library page <key> --printed N --format image --out-dir
  <a folder under records/pyramids/citation-audit-theory/img/>`, then open the PNG with the Read
  tool. OCR misreads `≤`, `<`, Greek letters and subscripts. Delete nothing; the images folder is
  not committed.
- Printed page = the number printed on the page, not the PDF page. If the `Page Offset` is wrong,
  say so and give the right mapping.
- For an author's module, check that the held PDF is the released v0.1 (its title page or Zenodo
  version line) and say what you found.

## What to check, per citation

1. **Locator.** The numbered item (Theorem, Lemma, Def., Eq., §, Obs.) exists with that number, and
   is on the printed page(s) given. A page range must cover the item; a single page must be where
   the item is stated (or where the cited part of it is).
2. **Support.** The source, at that place, says what the sentence uses it for. Read the paper's
   sentence or statement closely: the claim attributed, its scope, the dimension, the class of
   objects.
3. **Hypotheses.** Where the paper restates a cited result (the statements of Section 2, "What is
   cited", restate them as numbered theorems), compare hypothesis by hypothesis and conclusion by
   conclusion. A hypothesis the paper drops, a conclusion stronger than the source's, a changed
   constant, sign, exponent or range is a finding. Notation that differs but means the same is not.
4. A citation with no locator is an attribution: check only that the source is the right one for
   what is attributed, and propose a locator where one would help a reader (say where it is).

## Verdicts

- `OK`: locator right, claim supported, hypotheses match.
- `LOCATOR`: the item or page is wrong; give the right one.
- `UNSUPPORTED`: the source does not say what the sentence uses it for. **Critical**: say exactly
  what the source says instead.
- `HYPOTHESIS`: the restatement differs from the source in a hypothesis or conclusion. Critical if
  the paper claims more than the source gives; minor if it claims less.
- `MINOR`: wording, a page that should be a range, a better locator, notation.
- `UNREAD`: you could not read the place (say why: not held, page missing, unreadable).

## Output

Write **one file**, `records/pyramids/citation-audit-theory/findings-<group>.md` (your group's name
is in your input file's name), with the Write tool, and nothing else in the repository. Format:

```
# Citation check, group <group>

Held copies: <key>: <what the held PDF is, version, page offset found>.

| id | where | key | locator | verdict | evidence (what the source says there, with printed page) | fix |
|----|-------|-----|---------|---------|-----------------------------------------------------------|-----|
```

One row per input id, in order. Evidence: the item's number, its printed page, and a short
paraphrase of what it states (a quotation of at most a dozen words where wording matters). Fix:
the exact replacement locator or sentence, or "none".

After the table, a section `## Critical` listing every `UNSUPPORTED` and critical `HYPOTHESIS`
row with a paragraph each, or "none".

Do not edit any `.tex` file. When you are done, check that your findings file exists (`ls`) and say
so in your reply, with the count of rows per verdict.
