# Changelog

All releases of this module are recorded here, newest first, with what changed and why, and in
particular which statements were renumbered, strengthened, weakened or withdrawn (hub `RELEASES.md`,
rule 2).

## pyramids-v0.1 — 2026-11-23 — first release of the theory paper: the theory of image pyramids

The article *Spatial scale space from hemigroup axioms: the theory of image pyramids*: a paper of
131 pages (Sections 1 to 7 and Appendix A) and a supplement of 52 pages (Sections S1 to S3), from
one set of sources. It is the first of the two papers of Paper VI; the second, on computing these
pyramids in the plane, is released after it and cites it. It restates in its Section 2 what it uses
of the line paper (`v0.1`), the cone and selection modules (`cone-v0.1`, `selection-v0.1`), the
isotropic paper (`iso-v0.1`) and the affine paper (`v0.1`), by their released statement numbers.
This is its first release: no statement is renumbered, strengthened, weakened or withdrawn against
an earlier version, and the statement numbers below are the ones to cite.

What it states. Kernel families on ℝ^d under the hemigroup axioms of linear scale space, with
covariance under the powers of one ratio q in place of every dilation. The isotropic families form
three nested strata, and in the middle one, covariant under q^ℤ, the kernel from scale 0 to each
scale is semi-selfdecomposable (Theorem 3.12; both inclusions are strict, Theorem 3.15). The ladder of
octave steps determines the kernels at the knots q^n (Proposition 3.20), and no law of bounded
support other than a point mass is a step of a family continuous in scale (Proposition 3.22). The
line and its grids are Section 4 (the grid pyramids of a mask on hℤ, Proposition 4.5). Every
octave step of the Matérn pyramid is one implicit heat step, a Helmholtz resolvent (Theorem 5.4),
and up to a relabelling of the scales the Matérn pyramid is the one isotropic family covariant
under q whose octave steps obey the maximum principle of an implicit Euler step (Theorem 5.19, from
the stage lemma, Proposition 5.18). On a lattice a symmetric mask other than a point mass has an
exact grid pyramid if and only if it is infinitely divisible with a logarithmic moment
(Proposition 6.9). In d ≥ 2 no kernel at a positive scale of an exact grid pyramid on a lattice is
rotation invariant (Proposition 6.5), nor when the dilation is an invertible matrix
(Proposition 6.6); for an integer ratio the kernels of an exact grid pyramid on hℤ^d are singular
(Proposition 6.7); without continuity in scale a band-limited mask has a rotation-invariant
refinable law (Proposition 6.18). The supplement holds the discrete stratum on the line
(Sections S1 and S2) and prints the admitted facts as the Lean source states them (Section S3).

What is machine-checked. The numbered lemmas, propositions, theorems and corollaries of Sections 3
to 6 and of the supplement have formal counterparts in Lean 4 (`v4.31.0`, on Mathlib at
`v4.31.0`), importing `ScaleSpaceCore` at `v0.5.0` and the affine paper's development at `v0.1`.
All are machine-checked but one step of Proposition 4.5(4) and three results proved in print only,
in whole or in part: Proposition 6.6, clause (3) of Proposition 6.7, and Proposition 6.18; their
formal statements are typed in a skeleton library that the development does not import. The
formal counterparts rest on Lean's three logical axioms and nine cited facts, taken as fourteen
axioms (Section 1.1 and Appendix A; the supplement's Section S3); Table 4 says which statement
rests on which. Of the nineteen cited facts that are not admitted, twelve are theorems of the
development and seven are stated for the reader and read by no formal proof. The connecting prose
and the numerical examples are not machine-checked, and the formal statements and definitions were
compared with the printed ones by AI agents only.

Reviews. Three external rounds, all by AI systems, each against a build frozen at a tag
(`pyramids-review-r1` to `-r3`): Gemini Argon 4 High, GPT-6.2 Astra Ultra, and four blind Claude
Fable 5.2 agents, a same-vendor read. The reports and the plans that record what was done with each
finding are under `notes/`. No human other than the author has reviewed the paper; the statement on
the use of AI says how the work was done.
