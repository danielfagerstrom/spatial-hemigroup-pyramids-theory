# Referee report, Part A (content review)

**Manuscript:** *Spatial scale space from hemigroup axioms: the theory of image pyramids*, with supplement.
**Block reviewed in detail:** Section 6, Section 7, Appendix A, the AI statement, the declarations and the references (PDF pp. 86–119). The abstract and Section 1 (pp. 1–7) were read for what they claim about this block and about the trust base. Sections 2–5 were read as far as the proofs of the block cite them (in particular Lemmas 3.3, 3.4, 3.8, 3.10, Propositions 3.20, 3.22, 3.23, 4.5–4.7, 5.15, 5.16, 5.18, 5.21, Theorem 5.19). Of the supplement I read S-pp. 1–8 and 30–46.

**What I could and could not check.** I had the two PDFs only. I did not see the Lean development, the scripts, or any cited source; statements about sources below are from memory and are marked as such. I verified the printed proofs by hand and reran three numbers with a few lines of my own code (Section 4 of this report).

---

## 1. Overall assessment and recommendation

**Recommendation: major revision.**

I found no mathematical error in any numbered statement of Section 6, including Proposition 6.6, whose printed proof is all there is. The four answers of Section 7.2 each follow from the statement they cite. The major revision is asked for on four other grounds.

- **The trust claim cannot be assessed.** The repository, its tag and the DOI "do not exist yet" (p. 117). By the paper's own account no human has compared the Lean statements with the printed ones (p. 116). Appendix A has two gaps a reader can detect from the paper alone (Section 5 below).
- **The isotropy result is framed more broadly than it is.** Section 6 says the obstruction "belongs to the lattice" (p. 106). It belongs to the lattice together with continuity in scale, which forces the mask to be infinitely divisible. For an infinite lattice mask that is not infinitely divisible, rotation-invariant knot kernels exist (Section 2.2(a) below gives one). The paper's fourth question (p. 113) asks this for finite masks only, and the reader is left with the wrong impression.
- **Positioning.** The criterion of Proposition 6.8 is stated in the abstract and in Section 7 as a result of the paper, while pp. 5 and 35 attribute it to Maejima and Ueda. Section 6.4 proves textbook facts at length without saying they are known, and its nine-point family has exactly the generator of Lindeberg's discrete scale space at his isotropy parameter 1/3, which is not cited.
- **Length and structure.** 119 pages plus 46, of which Section 6.4, Section 6.1 and the first third of Section 7 could be cut or moved without loss.

For the block alone: the mathematics is sound and the corrections are of statement, scope and attribution, none needing a new theorem.

---

## 2. The headline claims against what is proved

### 2.1 Claims that are carried

- **Criterion for an exact mask** (abstract p. 1; p. 4; p. 111). Proposition 6.8(1) (pp. 96–97) proves: a symmetric probability law other than the point mass at 0 has an exact ladder iff it is infinitely divisible with a logarithmic moment, of its Lévy measure or equivalently of itself. The proof is correct. On a lattice the mask is then compound Poisson with unbounded support.
- **No isotropy on a lattice** (abstract; p. 4; p. 111). Proposition 6.5(2) (p. 91, proof p. 92) proves that no kernel at a positive scale of any carrying family is rotation invariant in d ≥ 2, and that the orthogonal symmetry group is finite when the mask's support spans. Correct.
- **Expanding dilation matrix** (p. 5; p. 113). Proposition 6.6 (pp. 93–95) is correct as printed; see Section 3.1.
- **The selection claim as restated in Section 7** (p. 111). "Up to the gauge, the one whose every octave stage has the principle" matches Theorem 5.19(2) (pp. 82–84) with its hypotheses: isotropic, covariant under q, canonical discrete gauge, the principle at every t in [1, q). I checked the converse of the stage lemma (Proposition 5.18(3), pp. 81–82, Steps 1–3) and the recovery of the gauge (p. 84); both hold.
- **Bounded support** (p. 111). Matches Proposition 3.22 (p. 40).
- **"Machine-checked in all but one step and one proposition, from ten cited facts taken as axioms"** (abstract). The counts agree with Section 1.1 and with Table 2: fifteen axioms, ten facts (three for Theorem 2.17, three for 2.21, two for 2.15, one each for 2.19, 2.20, 2.23, 2.24, 2.25, 2.26, 2.32), six of the fifteen in the imported namespace. The seventeen facts not admitted split 11 + 6 as stated (p. 6).

### 2.2 Where a headline is stronger than the result, or leaves a wrong impression

**(a) The obstruction to isotropy is an obstruction for infinitely divisible masks, not for lattices.**
Section 6 is titled "Exact or isotropic on a lattice, not both". Page 87 adds "Nor does a finite mask other than δ0 have a rotation-invariant refinable law". Page 106 says "The obstruction belongs to the lattice, and the continuum has none". Page 111 says "Computing on a lattice has a price". Page 89 promises that "Why the continuity (b) is required instead is the subject of Proposition 6.15", and p. 104 repeats the question.

Proposition 6.15 does not give a reason for requiring continuity. It shows that the knot relation alone admits the binomial mask. And once continuity is dropped, the obstruction disappears for infinite masks:

> *Example.* Fix d ≥ 1 and q > 1, and take r ≤ 2π/(q+1). Let ψ ≠ 0 be real, radial, smooth and supported in the ball of radius r/2, and φ := ψ∗ψ/‖ψ‖². Then φ is radial, supported in the ball B_r, φ(0) = 1, and φ is the characteristic function of a rotation-invariant Schwartz density p ≥ 0 (a constant times the square of the inverse transform of ψ). Put w := Σ p(n) δ_n over n in Z^d. By Poisson summation ŵ(ω) = Σ_k φ(ω − 2πk), so w is a symmetric probability law on Z^d with all moments, and w ≠ δ0. On |η| < 2π − r one has ŵ = φ, and φ vanishes for |η| ≥ r. Take any ω. Either |ω|/q < 2π − r, and then ŵ(q^{-m}ω) = φ(q^{-m}ω) for all m ≥ 1; or some q^{-m}ω has modulus in [r, qr), which lies in [r, 2π − r), and there both ŵ and φ vanish. So Π_{m≥1} ŵ(q^{-m}ω) = Π_{m≥1} φ(q^{-m}ω) for every ω. The right side is the transform of μ, the law of Σ q^{-m} X_m with X_m independent of density p. This μ is rotation invariant, has a smooth density, is not δ0, and satisfies D_q μ = μ ∗ w.

So a positive mask on a lattice can have a rotation-invariant refinable law, and its rescaled equivalent weights (Burt's characteristic kernel) then converge to a rotation-invariant limit. The mask is not infinitely divisible, since its transform has zeros, and that is the only reason Proposition 6.5 does not reach it. Band-limited radial low-pass filters of this kind are what the steerable pyramid uses.

Consequences for the text:
- Page 106's sentence is wrong as an explanation.
- Question 4 of Section 7.2 (p. 113) is answered correctly but only for finite masks, and nothing says that the answer flips for infinite ones.
- The paper itself says that "whatever the ladder leaves free is invisible" in a pyramid's output (p. 2). The requirement that produces the obstruction, continuity between the knots, is of that invisible kind. Section 7.1 should say so.

**(b) The contributions list is out of date.** Contribution 4 (p. 4) says: "The ratio here is a scalar. A pyramid whose dilation also turns the lattice is outside the statement (Section 7)." Proposition 6.6 and Section 7.2(3) now treat exactly that case, and Section 7.1 (p. 112) says the obstruction "is carried over". Neither Proposition 6.6 nor Proposition 6.16 appears in the contributions list, while Section 7.2 calls their content answers to questions raised by "each main result".

**(c) The criterion is stated as the paper's own where it is a headline.** Page 5 and p. 35 say the criterion and the product formula "are a theorem of Maejima and Ueda … in R^d and without symmetry", and p. 26 credits the family between the knots to Maejima and Sato's construction. The abstract, Section 6.3 (pp. 96–98) and Section 7 (p. 111) state the criterion with no attribution. Lemma 6.4 (p. 90) re-proves the product formula for a carrier that need not be symmetric, which is the case p. 35 says the source already covers.

**(d) What "exact" amounts to is not said plainly.** Conditions (b) and (c) of Proposition 6.8(1) do not involve q. So a mask is exact for one ratio iff it is exact for every ratio, non-integer ones included. Exactness in sense (iii) is therefore a property of the mask alone: it is infinitely divisible and its backward product converges. Stating this would let the reader see how weak the tie between the mask and the pyramid's ratio is.

**(e) Section 7.2(2)** (p. 112). The answer "Read pointwise, no" is supported by Proposition 5.21 (pp. 85–86). The example is the generic one: a maximum over coarse-grid neighbours need not be one over fine-grid neighbours. The text on p. 85 says as much; the answer on p. 112 reads as a finding about the principle. The sentence there that "On hZ^d … the frame mask has it on no finite symmetric neighbourhood" is false at d = 1, where the frame mask is the three-point resolvent; Proposition 6.7 assumes d ≥ 2.

**(f) Page 100**, "So in the plane counting extrema excludes every pyramid whose octave steps are absolutely continuous". This holds if the principle is "no step creates a maximum for any input". For records, Proposition 5.15 covers the Matérn, frame Matérn and Gaussian ladders only (clauses (3)–(5)). The sentence should say which reading it uses.

---

## 3. Mathematical correctness

### 3.1 Proposition 6.6 (pp. 93–95), proved in print only

I read it line by line.

- *The matrix.* The eigenvalues of the inverse have modulus below 1, so its powers tend to 0 in norm by Gelfand's formula. Correct.
- *The mask.* Lemma 3.3 needs only (a) and (b). Lemma 3.8 (p. 25, which I also checked) gives no Gaussian part and a finite Lévy measure on the lattice minus the origin. It is nonzero because a symmetric point mass is δ0. Correct.
- *The knot kernel.* From (a), (c_M), (d): M_*μ1 = μ1 ∗ w. Theorem 2.20 and uniqueness give M A1 Mᵀ = A1 and M_*ν1 = ν1 + νw. Iterating the first gives A1 = 0. Iterating the second N times leaves a remainder ν1(M^N B), bounded by ν1 of the complement of a ball of radius ε/‖M^{-N}‖, which tends to 0. Correct, including the inequality |M^N x| ≥ |x|/‖M^{-N}‖.
- *All kernels.* (c_M) at s = 0, inverted for negative n, gives the knot kernels. The two factorizations of μ_t between consecutive knots give no Gaussian part and the sandwich for ν_t. Correct.
- *No isotropy.* As in Proposition 6.5(2). Correct.

Remarks, none affecting validity:

1. **"Expanding" is not used by the conclusion.** The conclusion needs only one atom x ≠ 0 of ν_t: a rotation-invariant Lévy measure in d ≥ 2 has no atom off the origin, since the orbit would carry infinite mass at one distance. An atom is obtained from ν_t ≥ (M^{n−1})_*νw, which needs M invertible and nothing else. The Gaussian part, the series for ν1 and the countability of Γ_M are not needed. The same holds for Proposition 6.5(2): the countability of Γ_q is not needed for its first sentence.
2. Since the proof "is that of Proposition 6.5(1)–(2), with D_q replaced by M_*", one lemma for a linear M and a non-symmetric carrier would yield Proposition 3.20(1), Lemma 6.4, Proposition 6.5(1) and Proposition 6.6 together. Formalizing that lemma would remove the one print-only proposition.
3. The "grid pyramid of (w, M)" is defined only inside the statement, and the second sentence applies "isotropic" to a family, where Definition 6.3 defines it for a pyramid.
4. Nothing says whether carriers with (c_M) exist for a given mask; Section 7.1 (p. 112) is honest that only the obstruction is carried over.

### 3.2 Proposition 6.16 (pp. 105–106)

Correct. The chain on p. 105 uses the knot relation at Rᵀω and at ω and divides by the transform of μ only where it is nonzero; the neighbourhood U need not be rotation invariant. The identity theorem then gives rotation invariance of the mask everywhere, a finite invariant support is {0}, and the transform of μ is constant along q^{-n}ω.

The argument never uses positivity of the mask or of μ. It holds verbatim for a signed or complex finite mask of total mass one and for a finite signed measure μ whose transform is nonzero at 0. Wavelet and subdivision masks are signed, so that is the generality worth stating. I would expect a statement of this kind to exist in the refinable-function literature; I cannot name a source, and the author should look before presenting it as new.

### 3.3 The other numbered statements of Section 6

All checked; all correct. Notes only where there is something to say.

- **Lemma 6.4** (p. 90). Correct. The carrier may be non-symmetric and may be degenerate between knots; the proof does not need otherwise.
- **Proposition 6.5** (pp. 90–93). Clauses (1)–(3) correct. In (3) I rechecked the transform of the sampled Laplace mask, its folded Lévy measure Σ (2a^k/k) δ_{kh}, the bound on the logarithmic moment, and both directions of the symmetry-group argument. The statement opens with "Let (w, q) be an exact grid pyramid", a hypothesis that clause (3), an existence statement, does not use.
- **Proposition 6.7** (pp. 95–96). Correct: the three-point recursion, the tensor inverse, the value f(0) = −4ς²(1+2ς)^{d−2}, and clause (2).
- **Proposition 6.8** (pp. 96–98). Correct, including the lower bound of the bracket by ⌊log_q |v|⌋ and the gluing condition of Lemma 3.10 for the uniform coupling.
- **Proposition 6.9** (pp. 98–100). Correct. Clause (1) is the classical fact that a geometric compound is compound Poisson with a logarithmic-series Lévy measure. Clause (2) assumes finite support of σ; a logarithmic moment of σ suffices and is also necessary, since w ≥ (1−p)pσ and log₊ of a sum of k terms is at most log k plus the sum of the log₊.
- **Definition 6.10, Lemma 6.11, Propositions 6.12, 6.13** (pp. 101–103). Correct. I checked Proposition 5.16 (pp. 77–79), on which they rest, including the Lipschitz bound for the witness and the choice R = qK. I checked the inverse of the subsampled binomial mask at q = 2: ρ = 2√2 − 3 solves ρ² + 6ρ + 1 = 0 and the normalization is 1. In 6.12(1) the words "with a nonnegative transform" are not used by anything. In 6.12(2) the frame mask is shown infinitely divisible by way of Proposition 6.8(1), which brings Theorem 2.26 into the axioms of 6.12 (Table 4, p. 116) for no reason; the data were computed directly in the proof of 6.5(3).
- **Proposition 6.14** (pp. 103–104). Correct. Clause (2) is associativity of convolution and nesting of the grids.
- **Proposition 6.15** (pp. 104–105). Correct.
- **Lemma 6.17, Proposition 6.18, Definition 6.19, Lemma 6.20, Proposition 6.21** (pp. 107–110). Correct. I rechecked the factorization 1 + t²D_h = (1 + 2dν_h)(1 − pφ), the resolvent identity, the expansion of the product of two mixtures (p. 110), the three forms of the nine-point symbol, and the expansion D_9 = |ω|² − (h²/12)|ω|⁴ + O(h⁴) on p. 109.

### 3.4 Section 7.2 against the statements it cites

1. Proposition 5.15(5) (p. 75, proof p. 77) states exactly what answer 1 says. The proof of (4) is correct (τ_n + 1 = q^{2n}τ_n; the least rung with two maxima; the rung below attains its maximum), and (5) is a dilation of the input.
2. See 2.2(e).
3. Proposition 6.6 covers the similarities cR with c > 1. Correct.
4. Proposition 6.16. Correct, with the scope remark of 2.2(a).

### 3.5 Statements in the connecting prose that are wrong or uncovered as worded

- p. 4, contribution 4: out of date (2.2(b)).
- p. 89 and p. 104: Proposition 6.15 is said to explain why continuity is required; it does not (2.2(a)).
- p. 98: "the (2d+1)-point resolvent κ_t gives the unique bounded solution v of (1 − t²Δ_h)v = f (Proposition 6.18(1))". Proposition 6.18(1) states uniqueness of the summable solution of the equation with right side δ0. The claim is true and follows from the proof on p. 108, but by the rule of Section 1.1 (p. 6) a claim in the prose is covered only through the statement it cites, and this one is not. Proposition 6.21(1) by contrast states uniqueness among bounded solutions.
- p. 100: "it is not of the form (6.3)" holds for d ≥ 2 only; at d = 1 the frame mask is of that form.
- p. 106: "The obstruction belongs to the lattice" (2.2(a)).
- p. 112: the frame-mask sentence of 7.2(2) needs d ≥ 2 (2.2(e)).
- p. 89: isotropy is defined with SO(d); everywhere else rotation invariance is O(d) (Definitions 2.6, 3.1). In d ≥ 2 the two agree. In d = 1 the definition makes every pyramid isotropic, also one with a non-symmetric carrier.
- p. 88 against p. 107: the index γ of the grid family is "γ ≥ 1" in Definition 6.1 and "γ ≥ 0" in Proposition 6.18(2).
- pp. 101, 103: Definition 6.10 and Proposition 6.14(2) take "q ≥ 1 an integer" where the surrounding statements take q ≥ 2.

### 3.6 The cited facts used in this block

The block reads Theorems 2.17, 2.18, 2.19, 2.20, 2.24, 2.25, 2.26 and, through Proposition 3.20, 2.21 and 2.23. From memory of Sato's book, the statements on pp. 16–18 agree with Theorem 8.1, Lemma 7.5, Theorem 9.3, Proposition 11.10, Proposition 15.5, Theorems 15.8 and 15.10, Corollary 24.4 and Theorem 25.3, in their hypotheses as well. I could not open the book, so this is not a check against the source.

Two remarks.
- **Theorem 2.25** (p. 18). The third conclusion, that ν is finite, follows from the second: a Lévy measure carried by Z puts no mass at 0 and is finite off the unit ball. The remark about "the proof printed on the same page" is not needed and the axiom can be shortened.
- **Theorem 2.20** is a change of variables in the formula of Theorem 2.17 plus uniqueness, of the kind the paper does by hand for dilations in Lemma 3.9 (p. 26). It need not be an axiom.

None of the six cited facts that no formal proof reads (Theorems 2.7, 2.12, 2.13, 2.14, 2.30, 2.31) is used in Sections 6–7.

---

## 4. Numerical items in the block

Outside my assigned items; reported because I reran them.

- **Figure 5, middle panel** (p. 94). I recomputed the Lévy measure of the five-point resolvent at p = 4/5 from the series of Proposition 6.9(1). The masses at (5, 0) and (3, 4) are 3.588 × 10⁻⁴ and 2.545 × 10⁻⁴, ratio 1.410, as the figure says. The cut at k ≤ 143 is where p^k/k first falls below 10⁻¹⁶ (1.22 × 10⁻¹⁶ at 142, 9.7 × 10⁻¹⁷ at 143). The twelve lattice points on the circle of radius 5h form two orbits of the square's symmetry group, as stated on p. 106.
- **The sampled Gaussians of standard deviations 0.5 and 0.6** (p. 56, print only). I recomputed E Y² = 0.13661 and E Y⁴ = 0.01598 with the sums cut at |k| ≤ 5 and at |k| ≤ 40; they agree to the digits shown, and the omitted tail is of order 10⁻¹⁹. The argument is correct: Y is integer valued because X has an atom at 0, and then Y⁴ ≥ Y².

The caption of Figure 5 describes the computation well enough to reproduce it. The scripts themselves are not available (p. 117).

---

## 5. The trust base (Section 1.1, Appendix A, the AI statement)

**What is good.** The account is unusually candid. It says which step and which proposition are not machine-checked, that the closing sentence of a proof certifies the formal counterpart and not the printed steps (p. 6), that the prose is covered only through the statements it cites, and that the match between formal and printed statements was made by AI agents (p. 6, p. 116). The counts are internally consistent (Section 2.1 above).

**What is missing or does not hold up.**

1. **Nothing can be checked.** "This draft is not yet released: the repository, the tag and the DOI do not exist yet" (p. 117). A referee can assess neither the fifteen axioms as formalized nor one headline declaration. Appendix A gives names only. A misformalized axiom can make every dependent theorem vacuous; a reader has no means to exclude this.
2. **No human has compared formal and printed statements.** "Beyond me, no human has reviewed the paper, and the formal statements in Lean have been reviewed by AI agents only" (p. 116). The abstract's "machine-checked" therefore rests, for its meaning, on an unaudited correspondence. The abstract does say the match is not machine-checked. It does not say that it is not human-checked either.
3. **Appendix A omits the one excepted proposition.** Page 115 says Table 4 covers "every numbered statement of the paper and of the supplement". Proposition 6.6 has no row, and the appendix does not mention it. Section 1.1 (p. 5) says its formal statement "is written … and not proved". The reader is not told in what form an unproved statement sits in a development whose build is said to fail when an axiom list changes: as a definition of a proposition, or as a theorem with a gap. Nor is it said that nothing depends on it.
4. **Table 3 disagrees with a printed proof.** The row for Proposition 3.20(1), (2) (p. 114) lists Theorems 2.17 and 2.19. The printed clause (2) contains the equivalence of the two logarithmic moments, and its proof on p. 37 reads Theorem 2.26. Table 4 lists 2.26 for the proposition as a whole. So the headline declaration for clause (2) is narrower than the printed clause, or the row is wrong. The row for Proposition 6.8(1) is annotated "the criterion"; this one is not.
5. **Formal counterparts whose content is unclear.** Section 1.1 says the numbered statements of Sections 3–6 have formal counterparts (p. 5), and Table 4 lists Definition 6.2 in its "none" row (p. 116). Sense (i) of that definition is "a property of an implementation" (p. 89); what its formal counterpart says is not told. Table 4 gives "none" for Proposition 5.15, whose clause (3) is about the Matérn pyramid of Theorem 5.4 and the frame pyramid of Proposition 5.14, both of which exist by cited facts. That is possible only if the formal clause is stated for laws with given transforms. Each such reshaping is where a printed and a formal statement can part; printing the formal statements would settle it.
6. **One of the "ten cited facts" is the author's own.** Theorem 2.15, two of the fifteen axioms, "restates the selection module's proposition, which is the statement the formal development takes as an axiom" (p. 14). Section 1.1 calls it "a classical fact of Schoenberg's that Karlin proves". The abstract's "ten cited facts" does not distinguish it from the nine facts of the literature, and [11] is an unrefereed release of September 2026. Its variation-diminishing clause is stated "for every integrable or bounded g" with sign changes "in the essential sense"; whether Karlin's theorem has those hypotheses should be shown. This block does not use Theorem 2.15.
7. **Small things.** The axiom names cited_A42, cited_A46, … (Table 2, p. 113) refer to a ledger that is not printed. The sentence "Every step is machine-checked" closes some proofs and not others: Lemma 6.11, Propositions 6.12, 6.13, 6.14, 6.21 and Lemmas 6.17, 6.20 lack it, and only Table 4 tells the reader they are checked.

**Is anything claimed as verified that the text elsewhere qualifies?** Apart from items 3 and 4, no. The supplement's "Every statement here is machine-checked" (S-p. 1) is consistent with Table 4.

---

## 6. Novelty and relation to prior work

Against the list in the instructions, for this block.

- **Burt (1981), Burt and Adelson (1983).** The reading of the product (6.1) as the equivalent weighting function run downward (p. 93, p. 111) is fair. A consequence is not drawn. An infinitely divisible mask has a transform with no zero (Theorem 2.18; Proposition 4.5(1) says ŵ > 0) and a positive weight at the origin. Burt and Adelson's equal-contribution constraint is, at q = 2, the vanishing of the transform at the alias frequencies (the supplement states it as mass 2^{-d} on each coset, S-p. 35). So no exact mask, finite or not, satisfies equal contribution. Of the four classical constraints, the paper's standard is incompatible with one, and this deserves a sentence in Section 7.
- **Meer, Baugher and Rosenfeld (1987).** Cited twice, as judging the mask "on its own" (p. 110). Their criterion is low-pass quality for one decimation. Exact masks cannot null any frequency, and the example of 2.2(a) is of their kind. The two standards pull in opposite directions; Section 7 should say so.
- **Lindeberg (1990).** Placed in stratum 1 (p. 111; Proposition S.5), correctly. Two attributions are missing. First, the nine-point Laplacian of Definition 6.19 is (2/3) of the five-point one plus (1/3) of the diagonal one (Lemma 6.20, second form). As I recall, this is the generator of Lindeberg's two-dimensional discrete scale space at his parameter γ = 1/3, which he singles out for rotational symmetry; the symbol agrees term by term. Section 6.4 cites Collatz for the stencil and nobody for its use as an isotropic generator of a scale space on the grid. Second, the resolvent κ_t is the exponential-time mixture of the semigroup generated by the discrete Laplacian, which is Lindeberg's kernel family: the grid analogue of Definition 5.1. That link is not made.
- **Semi-selfdecomposable laws.** See 2.2(c). In addition, as far as I recall: Lemma 3.3, on which the first line of every proof in Section 6 rests, is Sato's Theorem 9.1 for the increments of an additive process in law. The logarithmic-moment condition for the continuous span is Sato's Theorem 17.5 (Wolfe; Jurek and Vervaat; Sato and Yamazato). Convergence of Σ q^{-m} Y_m iff E log₊|Y| is finite holds for arbitrary independent identically distributed Y, which would give Proposition 3.20(3) without infinite divisibility or symmetry. And I believe the trichotomy of Lemma 3.6(2), stated as a result on p. 111, is proved for the epochs of a semi-selfsimilar process by Maejima and Sato (1999). These are from memory and should be checked.
- **Hanke and Groetsch; Radmoser, Scherzer and Weickert.** The claims on p. 111 are hedged ("was not found in that literature"), which is the right register. The standard reference for one Tikhonov step as one implicit diffusion step is Scherzer and Weickert, *Relations between regularization and diffusion filtering*, in this journal's class (JMIV, 2000); it is not cited. The forward–backward first-order recursion for an implicit heat step on a grid is the recursive filter of Alvarez and Mazorra (1994) and of Deriche; not cited. The frame step, a product of one-dimensional implicit steps, is the locally one-dimensional splitting of the implicit step; the additive-operator-splitting literature (Weickert, ter Haar Romeny and Viergever, 1998) discusses its axis bias and belongs next to Proposition 6.7.
- **Mallat (1989); Cavaretta, Dahmen and Micchelli (1991).** The identification of the knot relation with the refinement equation (p. 112) is correct, including the mask sum 2^d. For Proposition 6.16 and question 4 the relevant prior work is on isotropy with refinability: the steerable pyramid of Simoncelli and Freeman, with band-limited radial low-pass filters, and the isotropic polyharmonic B-splines of Van De Ville, Blu and Unser (2005), refinable on Cartesian and quincunx lattices with infinite masks. Neither is cited.
- **Whittle (1954); Lindgren, Rue and Lindström (2011).** Page 108 says the continuum family is classical and calls Λ_t "its grid counterpart". The grid family is itself in that literature: integer powers of (κ² − Δ_h) are the lattice precision operators of Lindgren et al., and the lattice analogue of the Bessel covariance goes back to Whittle and to Besag (1981). Proposition 6.18(1)–(2) is the Green's function of the killed lattice walk and the resolvent identity.

**Net.** New in this block, as far as I can judge: the reading of the knot product and of exactness for pyramids; the lattice obstruction, which is one observation (an infinitely divisible lattice law has an atomic Lévy measure, and a rotation-invariant Lévy measure has no atom); the creation of maxima across a decimated level (Lemma 6.11 to Proposition 6.13), which I found the most original part of Section 6; Proposition 6.7; and Proposition 6.16, subject to a literature check. Known: Section 6.4, Proposition 6.9(1), Proposition 6.15, and the criterion of Proposition 6.8(1).

---

## 7. Exposition and structure

- **Forward references that carry weight.** Definition 6.1 (p. 88) and Proposition 6.9(4) (p. 98) use the kernels of Propositions 6.18 and 6.21, constructed in Section 6.4, which "may be read first" (p. 87). Then it should come first, or go to the supplement. Proposition 4.7(2) (p. 52) is stated in terms of Definition 6.2, forty pages ahead. Definition 4.4 and Definition 6.3 define "exact grid pyramid" twice, reconciled only by Proposition 6.14(1).
- **"Exact" has too many uses.** Three senses (Definition 6.2), "exact cascade" as a fourth (p. 89), "exact in the third stratum" (Definition 4.4), and "Lindeberg's discrete scale space is exact but not a pyramid" (S-p. 42) as another. Sense (ii) is used for one statement in the whole paper (Proposition 4.7(2), as p. 88 says) and should be stated there.
- **"Family" changes meaning.** In Definition 6.3 the carrier is a family without (ND) and without symmetry (p. 89), while Definition 3.1 requires (ND), and Sections 3–5 mostly assume symmetry. The text flags it, but the same word is used, and the abstract's "one family continuous in scale and covariant under q" is the weaker object.
- **Repetition.** The knot product is derived three times (Proposition 3.20(1), Lemma 6.4, Proposition 6.6). The uncountability of a sphere is proved twice in the same words (pp. 92, 106). Pages 110–111 of Section 7 repeat the contributions of pp. 2–4 almost sentence by sentence. Many proofs spell out steps at the grain of the formal proof (the tensor-power paragraph on p. 101, the description of Γ_q on p. 91).
- **Notation.** M is a dilation matrix (p. 93), an inverse mask (p. 95), a product index (p. 90) and a supremum (p. 108). D is a dilation of measures, the symbols D_h, D_5, D_9, a set of four indices (p. 95) and the unit ball. ν_h := t²/h² (p. 107) sits among Lévy measures ν. The image of a law under R is written both D_R μ and R_*μ in one proof (p. 92). t is a scale and, in Propositions 6.9(4), 6.18, 6.21, a range.
- **Reliance on the earlier papers.** The block itself needs them only through Theorem 5.4. The five self-citations [9]–[13] are releases of September to November 2026, none refereed as far as the references show.
- **What the supplement carries that this block needs.** Proposition S.33 (cited on p. 105; redundant beside Proposition 3.22) and, through Proposition 4.5, Lemmas S.1 and S.3, which are Lemmas 3.4 and 3.9 at d = 1. The dependence is avoidable.
- **What a journal version should lose from this block.** Section 6.4 except a half-page statement with references; Section 6.1 except Definition 6.3's own sense; the first part of Section 7; the closing sentences listing cited facts, which Table 4 already holds.

---

## 8. Required changes and suggestions

### Required changes

1. **Make the formal development available to referees, and print in the supplement the Lean statements of the fifteen axioms and of the headline declarations of Table 3** (pp. 113–117). Without them "machine-checked" cannot be assessed.
2. **State who, if anyone human, has compared each printed headline statement and each axiom with its formal counterpart, and say it where the abstract says "machine-checked"** (pp. 1, 6, 116). At present no human has, and the abstract does not say so.
3. **Appendix A: add Proposition 6.6** (pp. 113–116, against p. 5). Table 4 is said to cover every numbered statement and omits it. Say in what form its unproved formal statement exists and that nothing depends on it.
4. **Reconcile Table 3 with the printed proofs, and annotate each row with the part of the clause it covers** (p. 114 against p. 37). The row for Proposition 3.20(2) lists Theorems 2.17 and 2.19, while the printed clause needs Theorem 2.26. Say also what the formal counterparts of Definition 6.2 and of Proposition 5.15(3) state (p. 115).
5. **Qualify the isotropy obstruction wherever it is stated as a fact about lattices** (pp. 4, 86–87, 89, 104, 106, 111, 113). It follows from continuity in scale; for infinite lattice masks the knot relation has rotation-invariant solutions (2.2(a)). State that, with the example or a proof, next to Proposition 6.16 and in question 4. Correct the claim that Proposition 6.15 explains why continuity is required.
6. **Rewrite contribution 4** (p. 4). It says a rotating dilation is outside the statement, which Proposition 6.6 and Section 7.2(3) contradict. It names neither Proposition 6.6 nor 6.16.
7. **Attribute the criterion where it is a headline** (p. 1, pp. 96–97, p. 111). By pp. 5 and 35 it is Maejima and Ueda's theorem with Maejima and Sato's construction; the abstract, Section 6.3 and Section 7 state it without them.
8. **Present Section 6.4 as known material, with attribution** (pp. 106–110). The resolvent of the lattice walk, its resolvent identity, the lattice Matérn operators, and the nine-point generator chosen for isotropy (Lindeberg's discrete scale space at γ = 1/3) are in the literature.
9. **Correct the statements listed in Section 3.5 of this report** (pp. 89, 98, 100, 107, 112). Each is wrong or uncovered as worded: the frame mask at d = 1 in two places, the citation of Proposition 6.18(1) for a claim it does not state, SO(d) against O(d), and the range of γ.
10. **Say in the abstract or in Section 1.1's list that one of the ten admitted facts is a proposition of the author's own module, and give the hypotheses under which Karlin's theorems yield it** (pp. 6, 14, 113). "Cited facts" reads as facts of the literature.

### Suggestions

1. (pp. 91–95) State one knot-kernel lemma for a linear map M and a non-symmetric carrier; derive Proposition 3.20(1), Lemma 6.4, Proposition 6.5(1) and Proposition 6.6 from it; formalize it. This removes the print-only exception.
2. (pp. 92, 94) In Propositions 6.5(2) and 6.6, argue from one atom of the Lévy measure; drop the countability of the carrier, and in 6.6 the hypothesis that M is expanding, which the conclusion does not use.
3. (pp. 96–98, 111) Say that the criterion of Proposition 6.8 does not involve q, so exactness is a property of the mask alone.
4. (pp. 110–111; S-p. 35) Say that an exact mask has a positive transform and a positive weight at the origin, hence violates Burt and Adelson's equal contribution and cannot null an alias frequency. It places the result against [2] and [27].
5. (pp. 90–91, 96) Give the operational test: a symmetric lattice mask is infinitely divisible iff the logarithm of its transform has a summable Fourier series with nonnegative coefficients off the origin. A designer can check it; "infinitely divisible" alone is not a test.
6. (p. 98) In Proposition 6.9(2) replace finite support of σ by a logarithmic moment, which is also necessary.
7. (pp. 105–106) State Proposition 6.16 for signed or complex finite masks of total mass one; the proof is unchanged. Check the refinable-function literature for precedent.
8. (pp. 101–102) In Proposition 6.12 delete "with a nonnegative transform", and take the infinite divisibility of the frame mask from the data in the proof of 6.5(3), not from Proposition 6.8(1), so that Theorem 2.26 leaves its axiom list.
9. (pp. 16, 18, 113) Derive Theorem 2.20 from Theorem 2.17 by the change of variables already used in Lemma 3.9, and drop the finiteness clause of Theorem 2.25. Two axioms fewer or shorter.
10. (pp. 86–110) Move Section 6.4 first or to the supplement; state sense (ii) where it is used; prove the uncountability of a sphere once.
11. (pp. 110–111) Cut the part of Section 7 that repeats pp. 2–4.
12. (p. 112) In Section 7.2(2) say that the example is the generic one, and say what does hold: at a coarse-grid maximum that is also a maximum over the fine-grid axis neighbours, the inequality holds by Proposition 5.18(2).
13. (pp. 87–88, 106–108) Write κ_t as the exponential-time mixture of the semigroup of the discrete Laplacian, the grid analogue of Definition 5.1, and cite Lindeberg's kernels there.
14. (p. 100) Say in which reading "counting extrema excludes every pyramid whose octave steps are absolutely continuous" is meant.
15. (pp. 5, 111) Add the references named in Section 6 of this report, after checking them: Scherzer and Weickert (2000); Alvarez and Mazorra (1994); the splitting literature for the frame step; the steerable pyramid and the isotropic polyharmonic B-splines; Sato's Theorems 9.1 and 17.5; Maejima and Sato for the trichotomy.
16. (pp. 86, 89) Use another word than "family" for the carrier of Definition 6.3, or add (ND) and note that Proposition 3.20(2) supplies a carrier that has it.
17. (pp. 15, 87–110) Reduce the overloading of M, D, ν_h, t, S; choose one of D_R μ and R_*μ.
18. (pp. 113–116) Print the ledger that the axiom names refer to, or rename them; close every proof with the machine-check sentence or none, and leave the record to Table 4.
19. (pp. 101, 103) Take q ≥ 2 in Definition 6.10 and Proposition 6.14(2), as in the statements around them, or say why q = 1 is admitted.
20. (pp. 117–119) References: [32] lacks a publisher; [36] has the author in capitals; [17] prints "Rˆn"; [25] is cited by the theorem and page numbers of the arXiv version, where the journal version should be used.
