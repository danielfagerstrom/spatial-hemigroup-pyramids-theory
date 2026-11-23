# Prompt for the second external review of the theory paper

Filled from article-kit `docs/templates/external-review-prompt.md`, on the model of
`PROMPT-round1.md`. The procedure is `PROCESS.md` § 9; this directory's `README.md` says what is
kept here.

## For the author

Attach **both** PDFs of the frozen build, tag `pyramids-review-r2` (the commit is named in
`README.md`): the paper, `review-build-r2-paper.pdf` (115 pages), and its supplement,
`review-build-r2-supplement.pdf` (46 pages). Both are in this directory and untracked. Run it in a system of another vendor than
the one that wrote the text (it was written with Anthropic's Claude), set to its highest
reasoning effort. Round 1 was Gemini Argon 4 High, and a different system gives an independent read. Save the
output verbatim here as `review-<part>-r2-<system>-<setting>.md`, with `<part>` `A` (content) or
`B` (presentation). Round 1's reviews are **not** attached: the reviewer meets the text as a new
referee does. If the system stops before the end, run part A once per block of sections (§§ 1–3,
§§ 4–5, §§ 6–7 with the appendix, the supplement), with "Review sections N to M in detail and the
rest for consistency with them" added at its head, and save each output with the block in the name.

---

## Part A, a content review

You are a referee for a mathematical-imaging journal (JMIV class), reviewing the attached
manuscript, *Spatial scale space from hemigroup axioms: the theory of image pyramids*, and its
supplement. It belongs to a series on linear scale space built from hemigroup axioms (two
smoothing steps compose to one, with no additive scale parameter). The earlier papers classify
the scale-space kernels on the line and, with rotation invariance, in R^d, under covariance by
every dilation. This one keeps covariance by the powers of one ratio q only, the case an image
pyramid tests. Section 2 restates, as numbered theorems with pages, everything it uses of the
earlier papers and of the literature, and the manuscript is meant to be readable on its own: say
where it is not. The manuscript has been revised after a referee report. You have not seen that
report, and you should not assume that anything has already been checked. Write a detailed
referee report. Be specific, cite pages of the PDF (the supplement's pages as S-pages), and
separate what is wrong from what is merely improvable.

1. **Overall assessment and recommendation** (accept, minor revision, major revision, reject),
   with the reasons in a paragraph.
2. **The headline claims against what is proved.** The abstract, the contributions list of
   Section 1, and the discussion of Section 7 make claims; check each against the statements and
   proofs that are supposed to carry it. Say where a claim is stronger than its result, where a
   qualification made in the body is missing from the headline, and where a scope statement
   leaves a wrong impression. The claims most at risk:
   - no law of bounded support other than a point mass is an octave step of any family continuous
     in scale (Proposition 3.22);
   - the Matérn pyramid is, up to a relabelling of the scales, the one isotropic family covariant
     under q whose octave steps from every scale obey the maximum principle of an implicit Euler
     step (Theorem 5.19, with the stage lemma, Proposition 5.18);
   - on a lattice, a symmetric probability mask other than a point mass has an exact grid pyramid
     exactly when it is infinitely divisible with a logarithmic moment (Proposition 6.7);
   - in d ≥ 2 no exact grid pyramid whose mask is carried by a lattice is isotropic
     (Proposition 6.5).

   Check also "machine-checked in all but one step, from ten cited facts taken as axioms" in the
   abstract against Section 1.1.
3. **Mathematical correctness.** Read the statements and proofs. Report every gap, error or
   unjustified step, with the page. Pay particular attention to what Section 1.1 says is not
   machine-checked, where the printed argument is all there is: the one step of Proposition 4.5(4)
   that the binomial masks and the B-spline samples are masks of bounded support; the connecting
   prose between the numbered statements; and the six cited facts that Appendix A says are stated
   for the reader and read by no proof. New in this version, and to be read first:
   - two lemmas: Lemma 3.4, the Lévy–Khintchine representation of a symmetric infinitely divisible
     law in the form the paper uses, and Lemma 6.4, the transform of the kernel at scale 1 of an
     exact grid pyramid as an infinite product, with its Lévy data;
   - the proofs that now cite them: Lemma 3.5, Proposition 5.16(3), Proposition 6.5 and
     Proposition 6.7;
   - Proposition 3.20(2), which now also states that when the step and both parts of its Lévy
     measure are rotation invariant, the two families it builds are isotropic;
   - the proofs that now cite Proposition 3.20(2): Theorem 5.19(1) and the converse of
     Proposition 4.5(2);
   - Proposition 6.14, whose proof now cites Proposition 3.23(2), and Proposition 6.5(3), which
     reads its series from the proof of Proposition 4.5(4).

   The steps that deserve a second look:
   - the three nested strata and their strictness in R^d (Theorems 3.12 and 3.15: the description
     of each stratum by the Gaussian part and the Lévy measure, and the witnesses that separate
     them);
   - what does not lift from the line (Proposition 3.17: no line exponent with an atom in its Lévy
     measure is the marginal of a rotation-invariant infinitely divisible law in d ≥ 2), and the
     strict shrinking of the isotropic classes of one ratio with the dimension (Proposition 3.18);
   - the ladder and the knot kernel (Proposition 3.20: the kernel at a knot as an infinite
     convolution of the rungs below it; infinitely divisible with a logarithmic moment as the exact
     condition);
   - the stage lemma (Proposition 5.18: a rotation-invariant law other than δ0 with the
     implicit-Euler principle is a Bessel potential) and the selection theorem it carries;
   - the creation of local maxima in the plane by one step of every absolutely continuous law with
     a nonnegative transform (Proposition 5.15), and on the grid by three masks across one
     decimated level (Propositions 6.11 and 6.12);
   - the lattice argument (Lemma 3.8) that the Lévy measure of an infinitely divisible lattice
     law lies on the lattice, and why that excludes rotation invariance in d ≥ 2.

   The cited facts to check against their sources' hypotheses are the ten admitted ones, listed
   in Section 1.1 and stated in Sections 2.1 and 2.2:
   - from Sato's book: the Lévy–Khintchine representation, Khintchine's theorem on null arrays,
     the triplet of a linear image, the infinite divisibility of self-decomposable and
     semi-selfdecomposable laws and their residuals, the polar form of a self-decomposable Lévy
     measure, the unbounded support of an infinitely divisible law, the lattice-carried infinitely
     divisible laws on the line, and the g-moment theorem;
   - the Pólya frequency clause of the selection paper;
   - Schoenberg's representation of Pólya frequency densities, from Karlin's book.
4. **The numerical examples.** Section 4 reports sizes of errors measured on the grid, computed
   by scripts the text names, and the figures show creation of maxima and the ladders. Are the
   checks well designed, do the reported numbers support what the text concludes, and is anything
   concluded that a computation cannot show? Is each computation described well enough to be
   reproduced?
5. **The trust base.** Section 1.1 states what the machine-checked development (Lean 4, Mathlib)
   assumes and what is not formalized, and Appendix A gives the inventory. Is the account clear,
   complete and honest as a reader would judge it? Is anything claimed as verified that the text
   elsewhere qualifies?
6. **Novelty and relation to prior work.** Check the positioning against this prior work:
   - Burt (1981) and Burt and Adelson (1983), on the generating kernel and the equivalent weights;
   - Meer, Baugher and Rosenfeld (1987);
   - Lindeberg's scale space for discrete signals (1990);
   - semi-selfdecomposable laws (Maejima and Naito 1998; Sato's book, § 15) and semi-selfsimilar
     processes (Maejima and Sato 1999);
   - nonstationary iterated Tikhonov regularization (Hanke and Groetsch 1998), and its reading as
     diffusion (Radmoser, Scherzer and Weickert 2000);
   - multiresolution analysis (Mallat 1989);
   - the Matérn covariances and the SPDE approach (Whittle 1954; Lindgren, Rue and Lindström 2011);
   - refinable functions and stationary subdivision (Cavaretta, Dahmen and Micchelli 1991).

   Is anything claimed as new that is known, attributed wrongly, or missing?
7. **Exposition and structure.** Where does the argument become hard to follow, where is a
   definition used before it is given, where is a forward reference load-bearing, where does the
   paper lean on the earlier papers, what does the supplement carry that the paper needs, and what
   should a journal version of a paper of this length lose?
8. **A numbered list of required changes** and a separate **numbered list of suggestions**, each
   item with a page reference and one sentence of reason.

Do not summarize the paper back to the author beyond what the assessment needs. Do not soften
findings; a wrong claim should be called wrong. If you are unsure whether something is an error,
say so and say what would settle it.

---

## Part B, a presentation review (optional, a second run)

You are an experienced editor of a mathematical-imaging journal. Read the attached manuscript,
*Spatial scale space from hemigroup axioms: the theory of image pyramids*, as its intended reader
would. That reader is a mathematically mature researcher in scale-space theory and mathematical
imaging, at ease with Fourier analysis, PDEs and linear scale space. They are not assumed to know
infinitely divisible laws, Lévy measures, self-decomposability or Pólya frequency functions beyond
what the paper teaches. Rank the twenty changes that would most improve its readability, each with
a page reference, what is wrong, and a concrete fix. Mathematical correctness is out of scope.
