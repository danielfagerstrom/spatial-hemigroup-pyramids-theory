# How Paper VI was made: the process account

The account behind the two papers' statements on the use of AI (`paper/ai-statement.tex`,
`paper-b/ai-statement.tex`), written for pass 5 of `PROCESS.md` § 8 (article-kit). It is exported
with each release as `notes/PROCESS.md`. It holds the origin of the main ideas, the division of
labour in numbers, the reviews, and the caveats the numbers travel with. It does not repeat the trust
base, which each paper's Section 1.1 owns.

*Status: drafted 2026-11-16; the numbers re-derived for the theory paper's first release at its
freeze, 2026-11-23, to the session archive's sync of that day (20:13 UTC; its last turn is 19:51
UTC). A later version re-derives them again.*

## One history, then two papers

Paper VI was one article until 2026-11-16, when it was split into the theory paper (`paper/`) and the
computation paper (`paper-b/`), the author's decision (`adr/0007`). Both papers' statements of record
are blueprint chapters written before the split, so their production is one campaign up to that day.
The numbers below are the module's, and both statements cite them. Of the archived sessions after the
split, the theory paper's two hold 2.2 active hours and the computation paper's two hold 2.7; the
queue runs of that day are not separable by paper.

## Where the main ideas came from

From the session archive and the hub's record, not from memory:

- **Covariance under one ratio, and the strata.** An AI assistant, in a conversation with the author
  of 2026-08-10 about hemigroup scale spaces in the plane, named the discrete stratum as the theory of
  image pyramids; the discrete stratum itself goes back to Paper I. The decision that the pyramid paper
  is about `d ≥ 2`, with the line as its first step, is the author's (hub `queue/Q-0190.md`).
- **The Matérn pyramid.** Named by an AI assistant in the same conversation. Its reading as one
  implicit heat step per octave first appears in a proposal of the hub's research office, an agent
  (`proposals/P-0016.md`, 2026-09-30). `adr/0003` says that this reading is not claimed as new.
- **The selection by the implicit-Euler maximum principle.** The research office's proposal P-0016
  (2026-09-30), accepted that day and proved as the stage lemma on 2026-10-01.
- **No exact grid pyramid on a lattice is isotropic.** The research office's proposal P-0003
  (2026-09-07), accepted 2026-09-08, proved in the draft on 2026-09-28 (commit `5098607`).

The programme, the questions, the decisions of scope (one paper became two; what each claims and
declines to claim) and the organization of the material are the author's.

## By the numbers

Computed 2026-11-23 by the archivist for the freeze of `pyramids-v0.1` (first computed 2026-11-16:
core 109, range 27 to 109; earlier on 2026-11-23, to the sync of 2026-11-22: core 85, range 26 to 85),
to the archive's sync of 2026-11-23, 20:13 UTC, whose last turn is 19:51 UTC, from
`ai-archive/canonical/sessions.jsonl`, with the method of the affine module's derivation
(`spatial-hemigroup-affine`, `records/affine/ai-figures-2026-10-13.md`), extended. **Core** is every
session tagged to this repository, with the worktree sessions named for Paper VI; **ceiling** adds the
hub's coordinating session and its shift sessions, which also served other modules.

| | core | ceiling |
|---|---|---|
| sessions | 144 | 149 |
| unattended runs | 128 (67 queue, 31 pull-request review, 30 prover, mathematician or smoke) | same |
| archived days | 23 | 38 |
| active hours | 114.4 | 209.7 |
| the author's typed words, pasted text out | 2,501 | 10,813 |
| the author's typed words, pasted text kept | 7,490 | 17,665 |
| agents' words, subagents included | 202,524 | 351,235 |
| ratio, pasted text out | 81 | 32 |
| ratio, pasted text kept | 27 | 20 |

The range to quote is **20 to 81 to 1**, the low end being the ceiling with the pasted text kept
(19.9), the high end the core with it out (81.0). The pasted text grew with the external
presentation review pasted on 2026-11-22 (4,864 words), which is why the low end fell. The Lean
formalization sessions hold 65.0 of the 114.4 core active hours.

**What 2026-11-23 adds.** The review rounds' coordinating session (the pass-7 session of 2026-11-22,
which ran to 18:24 UTC that day and was already in the core), two worktree sessions of the rounds
(round 1's batch 2b; round 3's batches A and B), this release preparation to 19:51 UTC, and two
plugin probes of 2026-11-22 without active time. **The sessions behind the other pull requests of
the three rounds (#93 to #105) are not archived** (on the VM or in the cloud, it seems): their work
is in git and absent from every figure here, so the rounds are under-counted.

**What is excluded from the author's words, and why.** Text the harness inserts into a session as if
typed (notices of side sessions and of CI, and the task briefs an agent writes for the sessions it
starts) is not the author's: 14,306 words in the core (about 9,600 of briefs). Kept, it would put the
core ratio at 12. Pasted blocks are also out (4,989 words in the core, among them the presentation
review and the terminal output of the DOI's reservation). One duplicated session (contained wholly in
another) is counted once.

**How it was reproduced.** No script was saved at the first derivation; the archivist rebuilt the
method from this section and checked it against the 2026-11-16 cut: the sessions (135), the
unattended runs, the archived days (17) and the excluded words (6,968) match, the typed words agree
within 1 per cent, the active hours within 2 (sessions still open at the earlier cut). The ceiling's
five hub sessions are the coordinating session and the four shift sessions of the affine module's
derivation, inferred, since the first derivation did not name them.

## Reviews

Every internal review of this module was by AI agents (Claude models), blind, with no part in the
writing: of the blueprint (two rounds, by part), of the statement skeleton, of each section of both
papers' drafts, and referee reads of the new results (`records/pyramids/REVIEW-*`, `REFEREE-*`).
The theory paper then had three external review rounds (`PROCESS.md` § 9), all by AI systems, each
against a build frozen at a tag (`reviews/`): round 1 by Gemini Argon 4 High (`pyramids-review-r1`),
round 2 by GPT-6.2 Astra Ultra (`pyramids-review-r2`), round 3 by four blind Claude Fable 5.2 agents
(`pyramids-review-r3`), a same-vendor read and a weaker test of independence. Every finding was
checked against the text, the blueprint and the Lean before it was answered; the answers are the
three response plans (`PLAN-review-response-theory*.md`). No human beyond the author has reviewed
either paper.

## Caveats

- Every figure is a lower bound on the agents' share.
- Paper VI's production from 2026-09-07 to 2026-09-23 sits in hub and line-paper sessions not
  attributable to this module, and is not counted.
- The Lean was developed in the affine module's repository until it moved here on 2026-11-12;
  sessions there are not counted, and this repository's git history of the Lean starts that day.
- Sessions run in the cloud or on the VM, and anything after the sync's last turn (2026-11-23,
  19:51 UTC), are missing: most of the sessions behind the review rounds' pull requests among them.
- Active time caps each gap at 15 minutes and includes subagents' time.

## Before a release

Re-derive the range through the archivist after the archive's sync that follows the last change to
the paper (`WRITING.md` § 6, rule 2), and update the table, the statement's sentence and its date.
