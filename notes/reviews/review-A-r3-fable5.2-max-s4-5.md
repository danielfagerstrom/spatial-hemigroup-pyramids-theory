# Referee report, Part A (content review)

**Manuscript:** *Spatial scale space from hemigroup axioms: the theory of image pyramids* (119 pp.) with its supplement (46 pp.), third version.
**Assignment:** Sections 4 and 5 (PDF pp. 42–86) in detail; the rest for consistency with them.
Pages of the paper are cited as "p. n", pages of the supplement as "S-p. n".

---

## 0. What was read, what was recomputed, what could not be checked

- **Read line by line:** pp. 42–86 (Section 4, Section 5, and Proposition 5.21, which ends on p. 86).
- **Read for the claims they make about this block:** pp. 1–7 (abstract, Section 1, Section 1.1), pp. 110–113 (Section 7), pp. 113–116 (Appendix A), p. 117 (availability).
- **Read as far as the block's proofs cite them:** Section 2 (in particular Theorems 2.2, 2.5, 2.8, 2.9, 2.11–2.16, 2.33 and Section 2.1.5); Section 3 (Lemmas 3.3–3.6, 3.8–3.10, Propositions 3.19–3.23); Section 6 (Definitions 6.1–6.3, Propositions 6.5, 6.7, 6.14, 6.18); supplement Lemmas S.1, S.3, S.9, S.34, Theorems S.4, S.35, S.36, Propositions S.8, S.37.
- **Verified by hand:** every displayed identity and inequality in the statements and proofs of the block (list in 3.1).
- **Recomputed independently**, from the formulas printed in the manuscript and not from the author's scripts (which a referee cannot obtain, p. 117): Table 1 and Figure 3 (p. 55–56), the sampled-Gaussian moments and step coefficients (pp. 55–56), the numbers of Figure 4 (p. 78), and two quantities the paper does not compute (3.3 below).
- **Not checked:** I could not open the cited sources, so page anchors and the wording of cited theorems are unchecked. Prior work that I name in Section 6 is cited from memory; each item should be checked by the author. I could not inspect the Lean development ("the repository, the tag and the DOI do not exist yet", p. 117). For a referee "machine-checked" is therefore an assertion, and every verdict on correctness below rests on the printed proofs.

---

## 1. Overall assessment of the block and recommendation

**Recommendation: major revision.**

I found **no error in any numbered statement or proof of Sections 4–5.** Every proof I followed closes, including the four new or changed items (Proposition 5.15(1), (4), (5) and Proposition 5.21), the one step of Proposition 4.5(4) that is in print only, and the printed argument on the sampled Gaussians. All the numbers of the block that I recomputed agree with the paper to the digits printed. That is unusual for 45 pages of proofs and should be said.

The reasons for a major rather than a minor revision are these.

1. **A consequence of Proposition 4.5(1) is not drawn and changes what "exact" means for imaging.** An infinitely divisible mask has a strictly positive transform. For an integer ratio this excludes Burt's equal-contribution constraint for every exact mask, and it makes every kernel of every family that carries an exact grid pyramid a *singular* measure (3.3). The text on pp. 35 and 45 says that an implemented pyramid samples these kernels on grids. For the pyramids of Definition 4.4 that is false: there is no density to sample.
2. **The selection is announced without the qualifications the body proves.** By the stage lemma the principle is *equivalent* to "the step is a resolvent". It holds for single octave steps only, fails for two octaves together and from scale zero (Theorem 5.19(3)), is satisfied at all stages by no family (Proposition 5.20(2)), rejects the Gaussian that the classical form of non-enhancement selects, and ties the selected continuum family to the ratio q. None of this reaches the abstract, the contribution list or the discussion.
3. **Attribution.** A sizeable part of the block is classical or a direct corollary of known results, and is either attributed thinly or announced in the headline without the attribution that the body gives (Section 6).
4. **The block is not readable on its own and is too long for what it carries.** Proposition 4.7(2) and Theorem 5.4 are stated and proved through Theorems S.35–S.37 of the supplement and Definition 6.2 forty pages ahead; a journal version can lose roughly a third of these 45 pages without touching a headline result (Section 7).

---

## 2. Headline claims against what is proved

### 2.1 The selection (abstract p. 1; contribution 3, p. 4; Section 7, p. 111; Theorem 5.19, pp. 82–84; Proposition 5.18, pp. 80–82)

**What is proved** is exactly what is stated, converse included: an isotropic q-covariant family in the canonical discrete gauge has the implicit-Euler principle at every octave stage μ_{t,qt}, t in [1,q), if and only if Ψ_t = F_q^1(χ(t)·) for some χ in G_q. I checked the proof step by step (3.1).

**What the headline leaves out.**

- (a) *The principle is the conclusion in other words.* Proposition 5.18(1) and (3) together say that a symmetric law has the principle if and only if 1/μ̂ = 1 + ω·Cω. So "every octave step obeys the principle" is the same sentence as "every octave step is one implicit Euler step of a constant-coefficient heat equation", and Theorem 5.19(2) is then the telescoping of Theorem 5.4(2) applied at each phase t. The mathematical content of the selection is the converse of the stage lemma. The paper says "the selection rests on the stage lemma" (p. 4), which is true but understates it: the abstract's "the one isotropic family ... whose octave steps ... obey the maximum principle" reads as an independent axiom picking out a family.
- (b) *The principle is not closed under composition* (Theorem 5.19(3), p. 83; Proposition 5.20, p. 85). Two octaves together fail; the kernels from scale zero fail; no symmetric family has it at every stage. Consequences that are nowhere stated: the selected family depends on q in an essential way (among all dilation ratios λ of the fully covariant family F_q, the step μ_{t,λt} has the principle only for λ = q); the Matérn pyramid of ratio q, read at every second level, is a q²-pyramid that violates the principle; pyramids of ratio 2 and of ratio √2 select different, mutually incompatible continuum families; and as q ↓ 1 the kernels have no limit (Theorem 5.4(5), p. 62). A reader of the abstract, of contribution 3 and of p. 111 expects a canonical family. Section 7.1 ("What the results do not say") is the place for this and does not have it.
- (c) *It is not a discretization of the classical axiom in the sense of sharing its solutions.* Page 79 calls the finite-step form "the implicit Euler discretization of the classical form" and then states that the classical form selects the Gaussian ray while the finite-step form rejects every Gaussian stage (Theorem 5.19(4)). Both sentences are correct. Together they mean that the paper replaces non-enhancement by a different axiom that is incompatible with it. The introduction (p. 4: "The principle that replaces the count of extrema is the maximum principle of an implicit Euler step") does not say so.
- (d) *The hypothesis quantifies over steps no pyramid computes.* A pyramid applies one octave step per level. Required of those steps, the principle fixes the ladder L_{√τ q^k} and nothing else (Theorem 5.19(1)); the uniqueness "up to the gauge" concerns the family between the knots, which by the paper's own account (p. 2) "is invisible in its output". The abstract's "from every scale" is accurate; p. 111 ("the one whose every octave stage has the ... principle") is accurate; contribution 3 is accurate. But the reader should be told plainly that for the pyramid as computed the result is clause (1), a one-parameter family of ladders, and that clause (2) is a statement about a continuum of pyramids with shifted knots.
- (e) *The selected octave step has no bounded density in d ≥ 2* (Proposition 5.11(3), p. 71) and no exact lattice pyramid carries it (p. 111). The second is in the discussion; the first is a property of the selected object that belongs next to the claim. The heuristic on p. 84 in fact shows more than it says: any step whose kernel has a C² density with a nondegenerate maximum fails the principle, so the principle *forces* a kernel that is singular at its centre.
- (f) *Scope words.* The family is isotropic a priori, the laws are symmetric (so drift resolvents are excluded by fiat, not by the lemma), the inputs are signed Schwartz functions, and the inequality is required at weak maxima. These are in Definition 5.17 and the theorem; they are fine, and "for every smooth rapidly decreasing input" in the abstract carries the third.

### 2.2 "Every octave step of the Matérn pyramid is one implicit heat step, a Bessel potential" (abstract; Theorem 5.4(1), p. 62)

Proved. See 6.8 on the name.

### 2.3 The lattice criterion on the line (abstract; contribution 2, p. 3; Proposition 4.5(2), pp. 46–48)

Proved, by reduction to Proposition 3.20 at d = 1. Three remarks.

- By the paper's own account (p. 5, p. 35) the criterion and the product formula are a theorem of Maejima and Ueda; what Section 4 adds is the lattice reading (Lemma 3.8) and the interpolation between the knots, which is the linear-in-log t coupling. The abstract ("a symmetric probability mask other than a point mass has an exact grid pyramid if and only if ...") and contribution 2 state it as a result of this paper. A qualification made in the body is missing from the headline.
- "Exact" here is sense (iii) only. The same mask is, in the same section, the mask of a computation that is *not* exact in sense (i) for the Matérn pyramid from level 2 on (Proposition 4.7(2)). The contribution list says both within four sentences (p. 3–4); the abstract says only the first.
- The two consequences in 3.3 below (no equal contribution; singular kernels) are qualifications of "exact" that a reader in imaging needs and that the paper does not give.

### 2.4 "No mask of bounded support has one" (contribution 2; Proposition 4.5(1), (4))

Proved; it is Proposition 3.22 on a lattice, that is, the infinite divisibility of the increments of a stochastically continuous additive process together with the unbounded support of a nondegenerate infinitely divisible law. Both are textbook facts (the paper cites the second as Theorem 2.24 and proves the first as Lemma 3.3 from Khintchine's theorem, as the textbook does). The statement is correct and useful; as a headline it should carry its source.

### 2.5 Counting (p. 2, p. 4, p. 5, p. 74, p. 100, p. 112)

- "One step of every absolutely continuous law can create a local maximum" (Proposition 5.15(1)): proved, with no condition on the transform.
- "The count can rise at every rung of the Matérn and frame Matérn pyramids" (p. 74, p. 100, p. 112): proved in the sense that for every rung there is an input, depending on the rung, whose count rises there (Proposition 5.15(3)). Section 6 says "for an input that depends on the level" (p. 4, p. 103); the continuum statements on pp. 74, 100 and 112 omit it.
- "On the line the count of local extrema gives that reason" (p. 111, in a paragraph about choosing one family of stratum 2): **not supported.** In stratum 2 the paper proves a sufficient condition for rung-to-rung non-creation for a class of fully covariant families (Proposition S.37, S-p. 40), and its own text says "it holds for a class of families that includes the fully covariant Matérn pyramid" (S-p. 39). No characterization and no selection of a pyramid by counting is proved on the line. The motivating story "counting selects on the line, fails in the plane, so replace it" is stronger than the results.

### 2.6 Section 7.2, questions 1 and 2 (p. 112)

- Question 1 ("Can the Gaussian ladder create extrema at a chosen rung? Yes", Proposition 5.15(5)): the answer is exactly clause (5).
- Question 2 ("Does the implicit-Euler principle survive decimation? Read pointwise, no", Proposition 5.21): literally correct. But the example uses no property of the resolvent (3.5), so the answer is not a finding about the discrete Helmholtz step, which is what the question suggests. And the sentence "the frame mask has it on no finite symmetric neighbourhood (Proposition 6.7)" lacks "in d ≥ 2": at d = 1 the frame mask is the three-point resolvent of Proposition 4.6(2), which has the principle, and Proposition 5.21 is stated for d ≥ 1.

### 2.7 The computed pyramid on the line (contribution 2, p. 3–4; Proposition 4.7(2))

"Equals the samples of its continuum steps at the first level, and differs from them at every later level, for every spacing": proved; I checked the closed forms of the proof numerically as well (3.1).

### 2.8 "Machine-checked in all but one step and one proposition, from ten cited facts taken as axioms" (abstract) against Section 1.1

Consistent with pp. 5–7 and with Tables 2–4: one step (Proposition 4.5(4)) and one proposition (6.6); ten facts, fifteen axioms. The step of the block is correct as printed (3.4). One anomaly in Table 4 that touches the block is in Section 5 of this report.

---

## 3. Mathematical correctness

### 3.1 What I verified, and found correct

**Section 4.**

- Lemma 4.2 (p. 43–44): all three clauses, including the two-move argument for (A7) (the case s ≤ t < s_n ≤ t_n is the only one where the first move must be made in s) and the identity (T_λ μ) * (D_λ f) = D_λ(μ * f).
- Proposition 4.5 (pp. 46–49): clause (1) both directions; clause (2) both directions, the atoms q^{-m} v_0 → 0 that exclude a lattice, and the counterexample w = T_h ϱ at ω = 2π/h; clause (3); clause (4): the mass (1+a)/(1−a), the transform (1−a)²/(1 − 2a cos hω + a²), the logarithmic series giving the folded Lévy measure Σ (2a^k/k) δ_{kh}, the identity 1 − 2a cos ϑ + a² = (1−a)² + 2a(1 − cos ϑ). The remark on p. 49 that the Poisson rate is 2 log(t/h) + O(h/t) is right (the next term is h/t).
- Proposition 4.6 (pp. 50–51): the three transforms, L_t = e_t^+ * e_t^-, the two first-order equations, the mixture identity, t_h²/h² = a/(1−a)², the factorization (1−a)^{-2}(1 − aS)(1 − aS^{-1}), and the uniqueness of the bounded solution. Consistent with Theorem 2.13 (I checked that r²δ_0 + r(1−r)(e^+ + e^-) + (1−r)² L = r² δ_0 + (1−r²) L).
- Proposition 4.7 (pp. 51–55): the periodization constant C_t = (h/2t)(1+a_t)/(1−a_t) = 1 + α_t(0); the identity p + (1−p)(1−a_t)/(1−a_t z) = (1−a_t)(1−a_s z)/((1−a_s)(1−a_t z)); the one-state recursion; the two identities for g_β; the recursion for b_i^{(n)}; R_n = −(sinh x / sinh qx)(cosh qx − cosh x)/(cosh q^{n−1}x − cosh x); the partial fractions L_r * L_s = (r² L_r − s² L_s)/(r² − s²) and the three exponential integrals; A_0, A_1 and σ_n/σ_{n−1} = −(q²−1)/(q(q^{2(n−1)} − 1)); the monotonicity of (cosh yx − cosh x)/(y² − 1); the bound α_t(0) < h²/(12t²). Numerically, the closed forms reproduce a direct simulation of the recursion (e.g. q = 2, x = 1: R_2 = −0.324027 against σ_2/σ_1 = −0.5; R_3 = −0.027908 against −0.1).

**Section 5.1.**

- Lemma 5.2 (pp. 59–61): transform, Green identity, Frullani, the substitution giving b_d, the bound C_d = 2^{1+d/2}, and the closed forms b_1 = 2e^{-y}, b_3 = 2(1+y)e^{-y} (J_1 = J_2 = √π/2 and the integration by parts for the second).
- Lemma 5.3 (p. 61): all three clauses; the bound |K_0(y) − log(1/y)| ≤ 2.
- Theorem 5.4 (pp. 62–65): the profile and its bound k_d ≤ M/r; the mixture representation; the density bound through the first N factors; clause (2) through Theorem 2.8; clause (3), P_e(μ*f) = (π_*μ) * P_e f; clause (4), including ∂_t e^{-F_q(tr)} and the unboundedness argument with |ω| = q^N/(ct); clause (5), the Riemann sum and −½ Li_2.
- Lemmas 5.5–5.7 (pp. 66–67): the Bernstein-polynomial proof of log-convexity along a progression, the growth lemma, and the dominated-convergence argument at x = n/x_*.
- Proposition 5.8 (pp. 67–69): both integral forms; the mixture (γ/β)δ_0 + (1 − γ/β) L_{√β} and its Lévy measure (a consistency check the paper could print: the compound Poisson mass log(β/γ) gives the atom e^{-log(β/γ)} = γ/β at the origin); clause (3) with A ρ^i = B ρ iff t = q^{i−1} s.
- Proposition 5.9 (pp. 69–70): both bounds on e^y b_d(y) (the factorization (3v − y)(v − y)), the geometric bound for k_d, P_1, P_2, P_3 and the failure for d ≥ 4.
- Lemma 5.10, Propositions 5.11, 5.12, 5.14 (pp. 71–74): correct; in 5.11(3) the constant N_d = Γ(d/2 − 1)/(4π^{d/2}) is the Newtonian constant, as it should be.

**Section 5.2.**

- Proposition 5.15 (pp. 75–77), all five clauses; details in 3.5.
- Proposition 5.16 (pp. 77–79): the witness, the Lipschitz bound 6|y|_1/R, u(Re_1) − u(0) ≥ 1 − θp − 2ε(R), and the inversion m = e^M Σ (−1)^k a^{*k}/k!.

**Section 5.3.**

- Proposition 5.18 (pp. 80–82): clause (1) through the second difference quotient; clause (2), κ − τΔ_h κ = δ_0; clause (3), Steps 1–3. In Step 1 the chain h(0) − cr²/8 < u(0) ≤ u(x_s) ≤ f_s(x_s) ≤ Σ a_k + A_1 r² is right, including the sign cases behind the bound on f_s. In Step 3 the polarization Σ_{i,j} [−(ω_i ω_j/2)(x_i+x_j)² + (ω_i ω_j/2) x_i² + (ω_i ω_j/2) x_j²] = −⟨ω,x⟩² is right.
- Theorem 5.19 (pp. 82–84): all four clauses; in (2) the monotonicity, continuity and surjectivity of χ; in (3) the two coefficient equations; in (4) both two-point evaluations.
- Proposition 5.20 (p. 85) and Proposition 5.21 (pp. 85–86): correct.

### 3.2 Statements that are wrong or unsupported as written

None is in a numbered statement. All are in captions or connecting prose, which Section 1.1 says is not machine-checked.

1. **Figure 4, caption (p. 78): "The value a = 5/2 meets the proof's condition on a."** Wrong for the proof as printed. The proof (p. 75) takes r ≥ 1 with W < W(0)/4 on {|x| ≥ r} and puts a := r + 1. For μ = L_1 in the plane, W(x) = ∫_0^∞ ρ e^{-ρ²/2} J_0(ρ|x|)/(1+ρ²) dρ, W(0) = ½ e^{1/2} E_1(½) = 0.4615, and W(1.5) = 0.2479 = 0.537 W(0). The inequality W < W(0)/4 first holds at r = 2.331, so the proof's recipe gives a ≥ 3.33. What is true is that a = 5/2 satisfies the weaker condition the argument actually uses (a > r, with some r in [2.34, 2.5)). Either state the proof with "a > r" or change the caption. The second half of the sentence ("the proof takes δ smaller") is right and understated: at δ = 1/100 the ridge term K * ρ_δ is 0.610 at the origin, against the 0.115 = W(0)/4 that the proof requires, so even at a = 5/2 the figure's δ is about five times too large for the proof (the bound is met at δ = 0.0019).
2. **Page 66: "Read in the frequency variable r instead, the product e^{-F_q(r)} is the squared modulus of the transform of his kernel."** "His kernel" in the preceding sentences is the time-causal limit kernel with ratio q² and constant 2c². The squared-modulus identity holds for a different member of that family, the limit kernel with ratio q and time constants c q^{-i} (each factor is |1 + i c q^{-i} r|^{-2}, as the same sentence says). As written the sentence identifies two different kernels. The same paragraph is on S-p. 39.
3. **Pages 35 and 45: "an implemented pyramid samples them on grids"** (the kernels of a q-covariant family). False for the pyramids of Definitions 4.4 and 6.3 with an integer ratio: their kernels have no density (3.3(b)).
4. **Page 111: "On the line the count of local extrema gives that reason."** Unsupported (2.5).
5. **Page 112, answer 2:** "the frame mask has it on no finite symmetric neighbourhood" is false at d = 1 (2.6).
6. **Page 55, heading "Measured: the size of the error".** Table 1 measures the distance between two discretizations, the computed array U_n and the sampled step V_n. Neither is the continuum pyramid, and V_n aliases too (Proposition 4.7(3)). "Error" presupposes that V_n is the truth. Not wrong arithmetic; wrong word.
7. **Page 49: "the equivalent weight of M levels rescaled to the finest grid".** T_{q^{-1}}w * ... * T_{q^{-M}}w lives on q^{-M}hZ, which is finer than every grid of the pyramid. Page 35 says it correctly ("rescaled back to the scale of ϱ").

### 3.3 Two consequences of Proposition 4.5(1) that the paper does not draw

Proposition 4.5(1) proves that an infinitely divisible symmetric mask on hZ has ŵ > 0 everywhere. The paper uses this for the support. It has two further consequences for an integer ratio q ≥ 2, which is the only case in which the pyramid decimates. I did not find either stated anywhere in the paper or the supplement.

**(a) No exact mask satisfies equal contribution.** Burt's condition that every fine node contribute the same total weight to the coarse level is, in the paper's own words (S-p. 35), that the mask put equal mass on each coset of the coarse lattice. On hZ with ratio q that is ŵ(2πj/(qh)) = 0 for j = 1, ..., q−1; at q = 2 it is ŵ(π/h) = 0. Since ŵ > 0, **no mask with an exact grid pyramid meets it**, in any dimension and on any lattice (in R^d use the dual lattice). For the sampled Laplace mask ŵ(π/h) = ((1−a)/(1+a))², which is 0.214 at a = e^{-1}: the alternating pattern on the fine grid reaches the coarse grid as a constant with a fifth of its amplitude. More generally an exact mask annihilates no frequency at all, which is also why Propositions 5.16(3) and 6.12 can invert it. The paper presents its criterion as "another standard" beside the classical ones (p. 110). It is not beside them; it excludes one of the four constraints of Burt and Adelson that the first page lists, and the one that controls aliasing under decimation. This belongs in Proposition 4.5, in the paragraph on S-p. 35 ("None of the four constrains the family across levels") and in Section 7.1.

**(b) The kernels of an exact grid pyramid are singular measures.** By (4.2), μ̂_{0,1}(ω) = Π_{m≥1} ŵ(q^{-m}ω), and ŵ has period 2π/h. At ω_k = 2π q^k/h with k ≥ 0 the factors with m ≤ k equal ŵ(2π·integer/h) = 1, so

  μ̂_{0,1}(2π q^k/h) = Π_{j≥1} ŵ(2π q^{-j}/h) = μ̂_{0,1}(2π/h) > 0 for every k ≥ 0.

The transform does not tend to 0 at infinity, so by the Riemann–Lebesgue lemma μ_{0,1} is not absolutely continuous. It is an infinite convolution of purely atomic laws, hence of pure type (the zero-one argument of Jessen and Wintner: a null set N with μ(N) > 0 gives the invariant null set N + hZ[1/q] of measure one), so it is singular; its Lévy measure is infinite, so it has no atom. Every other kernel μ_{0,t} is the convolution of a dilate of μ_{0,1} with a compound Poisson lattice law (the Lévy measure of μ_{q^n,t} is at most D_{q^n}ν_w, Proposition 6.5(1)), so it is singular too. For the geometric pyramid (4.3) at q = 2, h = 1, a = e^{-1}, I computed μ̂_{0,1}(2π·2^k) = 0.040876 for k = 0, ..., 6, constant to all digits; at q = 3 the value is 0.175900.

So for an integer ratio, **exactness and a density exclude each other**, and for the same reason as (a): a refinable law with a density needs zeros of ŵ at the aliasing frequencies (the binomial mask has them and its limit is the B-spline), and infinite divisibility forbids them. Consequences for the text:

- the "pyramid principle" (p. 35, p. 45, Proposition S.8(2)), which is conditional on a continuous density, never applies to a family that carries an exact grid pyramid of integer ratio;
- the sentences "the kernels of a pyramid are continuum kernels, and an implemented pyramid samples them on grids" (p. 35) and "an implemented pyramid samples them on grids" (p. 45) are false for these pyramids;
- the two readings of a pyramid that the paper uses, a ladder of lattice steps (Definition 4.4) and the samples of a continuum kernel (Figure 1, Proposition 4.7(2)), are mutually exclusive for integer q, and the paper should say so where it lists the "four objects kept apart";
- Section 6 could be strengthened: on a lattice with integer ratio, exact pyramids are not only not isotropic, their kernels have no densities at all.

The phenomenon is classical for infinitely divisible laws whose Lévy measure sits on {b^{-n}} with b an integer (it is in Section 27 of the book the paper already relies on, going back to Hartman and Wintner; the author should check the theorem number), and the q-Cin kernels of Proposition S.40 are of exactly that type.

What would settle (b) if the author doubts it: evaluate (4.3) at 2π q^k/h.

### 3.4 The items of the block that Section 1.1 says are not machine-checked

- **The one step of Proposition 4.5(4)** (p. 48–49). Correct. The binomial weights 4^{-k} C(2k, k+n) are symmetric, sum to one and are the refinement masks of the B-splines of degree 2k−1 (2^{-(2k)} C(2k, j) is the probability-normalized two-scale mask). A centred B-spline of degree r with unit knots is positive exactly on (−(r+1)/2, (r+1)/2), so for r ≥ 2 its integer samples charge 0 and ±1. Two small points: the renormalization is vacuous, since the integer samples of a centred B-spline already sum to one; and "degree at least 2" is exactly what is needed, since degrees 0 and 1 sample to δ_0.
- **The sampled Gaussians of standard deviations 0.5 and 0.6** (p. 56). Correct. Y lives on Z because X has an atom at 0; the moments of Y are finite for the same reason; EY = 0, EX = EX³ = 0 give EY² = EZ² − EX² and EY⁴ = EZ⁴ − EX⁴ − 6 EX² EY². I recomputed by hand and at 40 digits: EX² = 0.215013, EX⁴ = 0.221347, EZ² = 0.351622, EZ⁴ = 0.413569, hence EY² = 0.136609 and EY⁴ = 0.015985. The omitted tail of the fourth-moment sum beyond |k| ≤ 5 is 5.0·10^{-19} before normalization. On the integers Y⁴ ≥ Y², so no such Y exists. The margin (0.016 against 0.137) is large, so the argument does not hang on the last digits. At the other three pairs EY⁴ ≥ EY² (0.58 against 0.44; 15.19 against 2.25; 217.3 against 8.51), as the paper says.
- **The connecting prose.** I checked every mathematical claim made between the numbered statements of the block. The ones that fail are listed in 3.2. The heuristic comparisons that the text itself marks as unproved (the Fourier account of the cross terms on p. 55; the dominance of the first term of I − e^{τΔ} on p. 73; the picture of the Gaussian stage on p. 84) are sound as heuristics; I checked the first by writing out the double periodization and it is right, including the absence of cross terms at n = 1.
- **The cited facts read by no proof.** Theorems 2.12, 2.13, 2.14, 2.30 and 2.31 occur in the block only in prose (pp. 45, 49, 57, 66, 67). Theorem 2.13 agrees with Proposition 4.6(1), and Theorem 2.14 at R = (1+ω²)^{-1} agrees with Theorem S.35(1) (profile 2 Σ e^{-q^m x}). No statement of the block depends on them.

### 3.5 The new items

**Proposition 5.15(1)** (p. 75–76). Correct, and the removal of every condition on the transform is real: absolute continuity enters once, through ∫(K − M)^+ → 0, which makes ‖K * ρ_δ‖_∞ small. Unimodality of the witness holds for every a and δ (the bound e^{-x_1²/(8a²)} ≥ 7/8 on (0, a] is what makes the ridge beat φ′(x_1) ≤ x_1); a > 1 is used only through r ≥ 1. One notational point: "Kρ_δ ≤ Mρ_δ + 8a²(K − M)^+ pointwise" is an inequality between integrands K(y)ρ_δ(x − y), not between products of functions at one point; write the arguments.

**Clause (2)** is correct but is used by no other clause. The proof of (3) repeats its argument in the Schwartz class with its own growth bound. It can go, or become a remark.

**Clause (3)** is correct. The order of choices is sound though it reads backwards ("With a and δ fixed below"): the step μ_{s,qs} fixes a and δ through (1), then τ = min(1, δ²)/2, then g. The Faà di Bruno bound n! C D^n is valid because the number of set partitions of n elements is at most n!. Two things a reader should be told at the statement and not a page later: g is signed (a deconvolved witness, made positive only by adding a constant, which takes it out of S), and g depends on s.

**Clause (4)** is correct: τ_n + 1 = q^{2n} τ_n; rung 0 is the witness; the least rung with two maxima has a predecessor with exactly one because a positive continuous record vanishing at infinity attains its maximum. The notation g_Σ is not defined (it is the density of N(0, Σ), and the bumps are translates of (2π)^{d/2} g_I, not of g_I).

**Clause (5)** is correct (c²τ = v, c² q² τ = q^{2(k+1)} τ_n). The detour through (4) is needed, because the witness is a Gaussian record only at variances below min(1, δ²). But the statement of (4) (three quantifiers and the auxiliary τ_n) is then only a step of the proof of (5). State (5) with "g a positive sum of three Gaussians" and move (4) into its proof. The letter c is used here for the dilation and in clause (3) of the same proposition for the Matérn constant.

**Proposition 5.21** (pp. 85–86). Correct and trivial. It uses of κ only that κ * f = u for f := u − τΔ_h u, that is, that κ has a summable inverse. The same construction works for every mask with a summable inverse that has a negative weight off the coarse lattice. What happens at the origin is that u(0) = 1 < u(±he_j) = 2: the origin is a strict *minimum* over the fine axis neighbours, where the fine-grid principle gives u(0) ≥ f(0), and decimation relabels it a maximum. So the proposition says that a coarse-grid maximum need not be a fine-grid maximum, which the sentence before it (p. 85) already says. It is a remark, not a proposition, and it should come with what does survive: the inequality at coarse maxima that are fine maxima, and the global bound sup u ≤ sup f.

### 3.6 Gaps and unclear steps

None is a gap in the mathematics. They are places where the printed proof is harder to follow than it needs to be.

- p. 63, "By that lemma with χ = id": the reference is to Theorem 2.9.
- p. 84, proof of 5.19(3): "At u = 1 and u = 2 the coefficients of u² and of u agree" means that a quadratic identity holding at u = 0, 1, 2 holds coefficientwise. Say that, or simply compare coefficients, since the identity holds for all u ≥ 0.
- p. 61, end of proof of Lemma 5.3: "The one cited fact is DLMF 10.32.10". Table 4 (p. 115) lists Lemma 5.3 under "none", because Theorem 2.33 is proved in the imported library (p. 6). Both are right; together they confuse.
- p. 64, Theorem 5.4(3): the count rests on Theorem 2.15, an admitted fact in an "essential" sense of sign changes for integrable or bounded inputs. That is not the form in which the variation-diminishing theorem is usually stated (pointwise sign changes). The reduction is short, but this is the one place where the block depends on an admitted statement that is not literally its classical source; print the reduction or state the axiom in the classical form.
- p. 62–63, Theorem 5.4(1): existence goes through Theorems 2.9 and 2.11 and so through three admitted facts. It need not: the steps are the infinite convolutions of the mixtures of Proposition 5.8(2), and the kernels are the Gaussian mixtures already constructed in the proof. Table 4 suggests the formal development knows this (Section 5 of this report).

---

## 4. The numerical examples

**Table 1 and Figure 3 (pp. 55–56).** I reproduced all twelve entries by direct convolution and decimation on a window of 12001 sites, and again from the closed forms of the proof of Proposition 4.7(2):

| h/(ct) | level 2 | level 3 | level 4 |
|---|---|---|---|
| 1 | 6.252 % | 6.725 % | 6.597 % |
| 0.5 | 2.020 % | 1.348 % | 1.078 % |
| 0.25 | 0.3844 % | 0.2491 % | 0.2130 % |
| 0.1 | 0.0567 % | 0.0371 % | 0.0330 % |

These round to the printed table. At level 1 I get 2·10^{-17} to 2·10^{-16}. The centre differences at h/(ct) = 1 are 0.0625, 0.0672, 0.0660 (Figure 3: "between 0.062 and 0.068"); U_3(0) = 0.669, V_3(0) = 0.602. The window argument on p. 55 (mass cut off of order e^{-2^{12} h/(ct)}) is right.

*Design.* The description is sufficient to reproduce the table without the script. The conclusions drawn are modest and supported: "stays of one order from level 2 to level 4", the factors 110 and 200, and "no bound on it is proved". Three things are missing.

- The data say more than the text does. At level 2 the distance is 0.056·(h/ct)² for small h/(ct) (0.0601, 0.0567, 0.0558, 0.0556 at 0.2, 0.1, 0.05, 0.025), and at fixed ratio it converges with the level (6.39 % at ratio 1 and 0.0317 % at ratio 0.1 by level 10). A second-order rate and saturation in n are worth one sentence each, marked as observed.
- Only q = 2 is shown, while Proposition 4.7(2) is for every integer q ≥ 2. At q = 3 I get 2.97, 3.27, 3.30 % at ratio 1 and 0.079, 0.043, 0.039 % at ratio 0.1.
- Nothing says which ratio matters. The Laplace mask of range ct has standard deviation √2·ct; matching the binomial mask's standard deviation h puts practice near h/(ct) = 1.4, where I get 5.8, 7.1, 7.4 %. The small entries of the table are for masks ten times wider than any pyramid would use before decimating by two. The reader should be told that in the regime of use the two arrays differ by six to seven per cent in total variation.

And, as said in 3.2, this is a discrepancy between two discretizations. If the sampled step is the intended reference, say why.

**The sampled Gaussians (pp. 55–56).** Reproduced on the periodic grid of 4096 sites: least step coefficient −1.093·10^{-2} at ±2 (pair 0.5, 0.6), −4.601·10^{-3} at ±2 (1.0, 1.2), −2.823·10^{-7} at ±10 (2.0, 2.5); for (0.7, 3.0) double precision gives noise of order 10^{-17}, and at 70 digits the least coefficient among the sites |k| ≤ 60 is −2.822·10^{-33} at ±36. All as printed. The text keeps apart what is computed ("computed signs on a periodic grid", "no inequality is proved here for all scales") and what is proved (one pair, by the moment argument). That is the right standard. The pairs are arbitrary, and the last one shows only that the sign survives to 10^{-33}; nothing is concluded from it that it cannot bear.

**Figure 4 (p. 78).** Reproduced semi-analytically (W by a Hankel integral, the ridge term by a one-dimensional integral with the inner integral in closed form): (L_1 * f)(0, 0) = 0.8035; the maximum along the axis x_2 = 0 is at x_1 = ±2.2845 with value 1.0146; midway level 0.9091. The caption's ±2.28 and α = 0.909 are right. The caption separates the computed count from the proved "at least two", which is correct practice. Its sentence on a is wrong (3.2, item 1), and neither parameter of the figure lies in the range for which the proof works. The figure is an independent numerical illustration at parameters where the proof's sufficient conditions fail; say that in those words, or draw it where proof and picture coincide (for L_1 in the plane, a ≥ 3.34 and then δ ≤ 0.001). The witness has a ridge of height 50 and width 0.01 beside bumps of height 1. The paper claims nothing about natural images, and the figure should not be read as if it did.

**What a computation cannot show.** Nothing is concluded from a computation that only a proof can give. No numbered statement of the block rests on a number.

---

## 5. The trust base, as it touches the block

- The account in Section 1.1 is clear, and for this block it is consistent with what the proofs use: the stage lemma, clause (2) of the selection theorem and Proposition 5.15(1) use only standard analysis, which matches "none" in Table 3.
- **One anomaly.** Table 4 (p. 115) lists Propositions 5.11 and 5.15 with no cited fact. Both are stated for "the Matérn pyramid of Theorem 5.4", whose existence clause is listed with Theorems 2.17, 2.21 and 2.23 (Table 3), and Proposition 5.12 and Theorem 5.19, stated for the same object, carry those facts. So either the formal statements of 5.11 and 5.15(3) are about laws constructed directly (the mixtures), and then they are not the printed statements, or the table is wrong. The abstract says that "the match of each formal statement with its printed one" is not machine-checked; this is a place where a reader can see that the match is not literal. Print what the formal statements quantify over.
- The sentence "Every step is machine-checked ..." closes the proofs of Lemma 4.2, Propositions 4.5, 4.7 and 5.21 and is absent from every other proof of Section 5, although Section 1.1 gives it a defined meaning and says all of them are checked. Close all proofs with it or none.
- A referee cannot check any of this (p. 117). The journal should not send the paper out again without the repository.

---

## 6. Novelty and relation to prior work

What follows is from memory; the author should check each reference.

**6.1 Burt (1981), Burt and Adelson (1983).** The reading of the knot kernel as the equivalent weighting function run downward (p. 49) is apt and attributed. Missing is the relation of the paper's criterion to equal contribution (3.3(a)): the paper's exact masks are exactly disjoint from the masks Burt's constraint admits. Proposition 5.12 ("the Laplacian pyramid is a Laplacian") is the resolvent identity (I − τΔ)^{-1} − I = τΔ(I − τΔ)^{-1}; it is a pleasant observation and not a result. The classical counterpart, that a difference of Gaussians approximates the scale-normalized Laplacian, should be cited where p. 73 calls the comparison heuristic (Lindeberg's book; Lowe 2004).

**6.2 Lindeberg (1990).** Used for the discrete scale space as the example of stratum 1 and for the sampled Gaussian. Two things in that paper bear on the block and are not used.

- Its classification of discrete scale-space kernels, through the Edrei–Schoenberg form of the generating function, has the first-order recursive filters as primitive kernels. The sampled Laplace kernel λ_t is one forward and one backward such filter, so it is a discrete scale-space kernel in that sense. The cascade steps λ_{s,t}, 0 < s < t, of Proposition 4.7(1) are not: their generating function has the factors (1 − a_s z)(1 − a_s z^{-1}) in the numerator, with the wrong sign. This is the grid counterpart of Theorem S.36 and worth a sentence, since Section 4.3 otherwise presents the sampled Laplace cascade as the well-behaved grid family.
- As I recall, that paper and [19, §4.1], the page the manuscript cites for the Gaussian case, state that in dimension two and higher no nontrivial kernel is guaranteed not to increase the number of local extrema, with the ridge-between-two-peaks example of Lifshitz and Pizer. The witness of Proposition 5.15 is that picture. The introduction (p. 5) says the Gaussian case is classical and "here it is shown for one step of every absolutely continuous law". If the general statement is in those sources, then what is new is a complete proof in this generality, the versions on records of the two ladders, and "at any prescribed scale". The author has the page and should say which it is.

**6.3 Semi-selfdecomposable laws.** The block's use is correct, and Section 3.4 attributes the criterion to Maejima and Ueda. The abstract and contribution 2 do not (2.3). Two further items: the mask λ_a^L of Proposition 4.5(4) is the discrete Laplace law (Inusah and Kozubowski, 2006), the law of the difference of two independent geometric variables, whose infinite divisibility is immediate from that; and the family "covariant under the powers of one ratio" has, besides the semi-selfsimilar additive processes of Maejima and Sato, a direct precedent in the literature on semistable convolution hemigroups (Becker-Kern, around 2003), where the word hemigroup of the title is already in use. The convergence criterion E log_+ |X| < ∞ for Σ b^{-j} X_j is also classical in the literature on random difference equations.

**6.4 Nonstationary iterated Tikhonov regularization; regularization as diffusion.** Cited in the introduction and the discussion, but not in Section 5, where the object is defined (p. 57) and the principle is introduced (pp. 79–80). Two papers of the journal class this is submitted to are missing and are the nearest neighbours of Section 5.3: Scherzer and Weickert (2000), on regularization as one fully implicit step of a diffusion with its scale-space properties, the extremum principle among them; and Nielsen, Florack and Deriche (1997), on first-order Tikhonov regularization as the filter (1 + λω²)^{-1}, its recursive implementation, and its behaviour in higher dimensions. Definition 5.17 is a *local* version of the extremum principle proved in that literature; the paper should say so and say that its contribution is the converse.

**6.5 The classical form of non-enhancement.** Page 79 cites only the author's own module [11] for "∂_t u ≤ 0 at a spatial local maximum". The axiom is Lindeberg's (and Koenderink's causality before it). The converse of the stage lemma is the finite-step counterpart of a classical fact, that a translation-invariant operator G with Gu(x) ≤ 0 at every local maximum of u is a second-order operator with nonnegative characteristic form; that fact is how non-enhancement gives the generator in Lindeberg's axiomatics and how the comparison principle gives second-order equations in Alvarez, Guichard, Lions and Morel. Here G = I − μ^{-1} on the range of μ. The proof by cosine test functions is self-contained and I have no objection to it; it needs the attribution of the idea. "The lemma belongs to the author's work ... not yet published" (p. 80) is not a positioning.

**6.6 Lindeberg's time-causal limit kernel.** Cited once, as a "twin in time" (p. 66). It is more than that. It is defined as an infinite convolution of first-order kernels with time constants in geometric progression, it satisfies the recurrence "kernel = one first-order step convolved with the kernel rescaled by the ratio", and the property stated for it is scale covariance under the integer powers of its distribution parameter, which map its discrete set of scale levels to itself. That is covariance under the powers of one ratio, the knot relation and the product formula of this paper, with a single first-order step as the octave step, in a scale-space paper of this journal. On the line the kernel of the Matérn pyramid is that kernel (ratio q, time constants c q^{-i}) convolved with its reflection. This belongs in the introduction's account of prior work, stated exactly (see 3.2, item 2).

**6.7 Recursions.** Proposition 4.6 is classical: the two-sided geometric mask with the normalization (1−a)/(1+a), realized by one causal and one anticausal first-order recursion, is the infinite symmetric exponential filter of Shen and Castan; the recursive literature (Deriche; Unser, Aldroubi and Eden for the spline prefilters, which is the recursion of Proposition 6.13) should be cited. The factorization of the three-point Helmholtz operator is the LU factorization of a tridiagonal matrix.

**6.8 Matérn covariances and the SPDE approach.** The attribution of the name is careful (p. 5, p. 58). Still, in the plane the octave step has γ = 1 = d/2 and is not a Matérn covariance (the paper says so only on p. 108), and no kernel μ_t is a Matérn law in any dimension. A pyramid named after a family to which neither its steps (in the plane) nor its kernels belong will mislead readers from spatial statistics; say this at Definition 5.1. Bessel potentials as scale-space kernels, with the order as the scale, have been proposed (the "Bessel scale-space" of Burgeth, Didas and Weickert, as I recall); the present family is different, and a sentence should say how.

**6.9 Scale-space pyramids (outside the block, bearing on it).** The abstract says the design literature "does not ask for a family of kernels at every scale whose steps the pyramid computes". Pyramids built as sampled Gaussian scale spaces do exactly that: Crowley's, the hybrid pyramids of Lindeberg and Bretzner that the paper cites on p. 5, and the octave pyramid of Lowe (2004), which is not cited at all. The Gaussian ladder of Proposition 5.15(4)–(5) is that construction. What is new here is the weakening of the covariance axiom to one ratio, not the reading of a pyramid as a sampled scale space.

**6.10 Sampled Gaussians.** A recent paper of this journal class on discrete approximations of Gaussian smoothing (Lindeberg, 2024) treats the sampled and the normalized sampled Gaussian kernel and their failure of the cascade property; cite it beside [18] on p. 55.

---

## 7. Exposition and structure

**Where the block is not readable on its own.**

- Proposition 4.7(2) (p. 52) is stated in terms of "sense (ii) of Definition 6.2" and "sense (i)", defined on p. 88, and of "the Matérn pyramid of Theorem S.35", in the supplement. A numbered statement of the main text depends on a definition forty pages later and on a theorem outside the paper.
- Theorem 5.4 (pp. 62–65) cites (S.7), Theorem S.35(3) and (4), Theorem S.36 and Proposition S.37 in its proof, Proposition 5.8 cites S.35(1), Proposition 5.9 cites Lemma S.34, Proposition 5.14 is built on S.35. The main existence theorem of Section 5 is not proved in the paper. Lemma S.34 and Theorems S.35–S.37 (five pages) belong in the main text; Sections S2.2–S2.3 do not.
- Section 4 leans on Lemma S.1, Lemma S.3 and Theorem S.4, which are Lemma 3.4, Lemma 3.9 and Theorem 3.12 at d = 1 in other notation.

**Forward references that carry weight:** Definition 6.2 (pp. 46, 52); Proposition 6.14 (pp. 46, 49, 56), without which the reader cannot tell what the recursion of Proposition 4.7(2) computes; Proposition 6.7 (p. 84) for the grid half of Theorem 5.19(4); Proposition 6.18(1) (p. 73).

**Terms used before they are defined:** "frame mask" (p. 42; Definition 5.13 is on p. 74 and the word "frame" is never explained; the standard word is *separable*); "exact cascade" (p. 3, p. 46; described on p. 89); "geometric pyramid" (p. 33; named in Proposition 4.5(4)); "record" (p. 57; defined inside Theorem 5.4(3)); "stage" (p. 79, a third word beside "step" and "increment" for one object).

**The word "exact".** Four meanings: three senses and "exact cascade", plus "exact in the third stratum". Sense (i) is not a property of a computation: the recursion of Proposition 4.7(2) is exact in sense (i) for the geometric pyramid (Proposition 6.14(2)) and inexact in sense (i) for the Matérn pyramid, so it is relative to the kernels "it stands for", which the definition leaves to the context. Sense (iii) has a standard name in probability, embeddability in a continuous convolution hemigroup. One word for four things, defined after its first use in a theorem, is the main obstacle to reading Section 4. Define the senses once before Section 4, and rename at least one.

**Duplication.** Definition 4.4 and Definition 6.3 define the same notion twice and are reconciled in Proposition 6.14(1). Proposition 4.5(1)–(2) is Proposition 6.8 at d = 1; Proposition 4.5(4) is Proposition 6.5(3) at d = 1. Section 4.1 and Section S1 exist to restate Section 3 in the operator axioms of the earlier papers. A reader who has Section 3 needs none of it.

**Notation.** The table on p. 15 lists eleven overloaded letters; the block adds at least c (Matérn constant; normalizer in the proof of 4.6; c_k in 4.7; the constant of Step 1 in 5.18; the dilation in 5.15(5)), τ (step size; variance in 5.15; integration variable in 5.8), a (Gaussian coefficient; e^{-h/t}; the witness parameter; τh^{-2} in 5.18(2)), h (spacing; three different functions on pp. 67, 81; a progression step), Λ (the limit exponent of Theorem 5.4(5); a measure in the supplement; the discrete Helmholtz family), ρ, D, M, R, s and t as scales and as dummies (p. 75: "e^t ≥ 4t − 2 for all t"). Each is local and none caused an error that I found, but the reader pays for it on every page.

**Where the argument is hard to follow.** The statement of Proposition 4.7(2), which interleaves five definitions with three claims; the proof of Proposition 5.15(3), where the parameters are fixed after they are used; the statement of Proposition 5.15(4); the passage on pp. 49 and 56 that explains three times which of two "Matérn" objects a recursion computes (the answer, that it computes the geometric pyramid of the mask λ_{ct} and not the Matérn pyramid, would be clearer said once, with Proposition 6.14(2) moved forward).

**What a journal version should lose from this block.**

- Section 4.1 and its operator axioms (three pages), to a remark; Section S1 entirely.
- Lemmas 5.5–5.7 and Propositions 5.8–5.9 (pp. 66–70): the Thorin digression is used by nothing in Sections 5.2, 5.3 or 6. Keep Proposition 5.8(2) as a remark.
- Lemma 5.3, Lemma 5.10 and Proposition 5.11(1)–(2): textbook material; keep the statement of 5.11(3).
- Theorem 5.4(4)–(5): used by nothing later.
- Proposition 5.15(2) and (4) as separate clauses; Proposition 5.21 as a proposition.
- The elementary verifications that are printed only because they were formalized (the Taylor bounds, the closed forms of b_1 and b_3, the linear independence of geometric sequences).

That is about fifteen of the forty-five pages, and none of it carries a headline claim.

---

## 8. Required changes and suggestions

### Required changes

1. **Proposition 4.5, pp. 46–49; S-p. 35; Section 7.1.** State that ŵ > 0 excludes Burt's equal-contribution condition for every exact mask of integer ratio. *Reason:* the criterion is incompatible with a classical constraint the paper lists on its first page, and the paper presents it as merely "another standard".
2. **pp. 35, 45, 47, 111.** State that for an integer ratio every kernel of every family carrying an exact grid pyramid is a singular measure, and correct "an implemented pyramid samples them on grids". *Reason:* the sentence is false for the pyramids of Definition 4.4, and the pyramid principle never applies to them.
3. **p. 1 (abstract), p. 4 (contribution 3), p. 111, Section 7.1.** Say that the principle is equivalent to "the step is a resolvent" (Proposition 5.18), holds for single octave steps only (Theorem 5.19(3), Proposition 5.20), rejects the Gaussian that classical non-enhancement selects, and makes the selected family depend on q. *Reason:* qualifications proved in the body are missing from every headline statement of the selection.
4. **p. 111.** Remove or prove "On the line the count of local extrema gives that reason". *Reason:* in stratum 2 the paper proves only a sufficient condition for a class of families (Proposition S.37).
5. **p. 78, Figure 4 caption.** Correct "The value a = 5/2 meets the proof's condition on a". *Reason:* with the proof's a = r + 1 the condition needs a ≥ 3.33, since W(1.5) = 0.537 W(0) for L_1 in the plane.
6. **p. 66 and S-p. 39; p. 5.** Correct "his kernel" and state the relation to the time-causal limit kernel exactly, in the introduction's account of prior work. *Reason:* the squared-modulus identity holds for the limit kernel of ratio q, not the one of ratio q² named in the same paragraph, and that kernel is the nearest precedent for covariance under the powers of one ratio.
7. **p. 1, p. 3, p. 46.** Attribute the lattice criterion to Maejima and Ueda where it is announced. *Reason:* it is stated as a result of this paper in the abstract and the contribution list, and as their theorem on p. 35.
8. **p. 5, pp. 74–77.** Check and attribute the statement that no nontrivial kernel in dimension two or more preserves the number of local extrema, and state what Propositions 5.15–5.16 add. *Reason:* the general statement appears to be in the source cited for the Gaussian case.
9. **pp. 79–82.** Attribute classical non-enhancement and the characterization of second-order operators by the local maximum principle, and relate Definition 5.17 to the extremum principles of the regularization-as-diffusion literature. *Reason:* only the author's own module is cited for a standard axiom, and the nearest prior papers on implicit steps as scale spaces are absent.
10. **pp. 47–53.** Attribute Proposition 4.6 and the mask of Proposition 4.5(4). *Reason:* the two-pass recursion with this normalization and the discrete Laplace law are classical and are stated without a source.
11. **pp. 46, 52, 88–89.** Define the senses of "exact" before Proposition 4.7 uses them, and make sense (i) name its reference kernel. *Reason:* a numbered statement depends on a definition forty pages later, and the same computation is exact and inexact in sense (i) according to an unstated target.
12. **pp. 52, 62–65, 68–70, 74.** Bring Lemma S.34, Theorems S.35–S.36 and Proposition S.37 into the main text, or restate them with proofs. *Reason:* Proposition 4.7(2), Theorem 5.4 and Propositions 5.8, 5.9, 5.14 are stated or proved through them, so the block is not readable on its own.
13. **pp. 85–86, p. 112.** In Proposition 5.21 and in answer 2 of Section 7.2, say that the example uses no property of the resolvent, and add "in d ≥ 2" for the frame mask. *Reason:* the answer reads as a finding about the discrete Helmholtz step, and the sentence on the frame mask is false at d = 1.
14. **p. 55.** Call Table 1 a discrepancy between two discretizations at q = 2, or justify the sampled step as the reference. *Reason:* "the size of the error" presupposes a truth that neither array is.
15. **pp. 74, 100, 112.** Add "for an input that depends on the rung" to the continuum statements that the count can rise at every rung. *Reason:* that is what Proposition 5.15(3) proves.
16. **p. 115 (Table 4), pp. 61, 71, 75.** Explain why Propositions 5.11 and 5.15 are listed with no cited fact while they are stated for the family of Theorem 5.4(1), and unify the closing sentence on machine checking. *Reason:* the table implies that the formal statements differ from the printed ones.
17. **p. 117.** Make the scripts and the Lean development available to referees. *Reason:* no numerical or formal claim of the paper can at present be checked by anyone but the author.

### Suggestions

1. **p. 75.** State Proposition 5.15(5) with "g a positive sum of three Gaussians", move (4) into its proof, and drop clause (2). *Reason:* (4) is a step of (5), and (2) is used by nothing.
2. **pp. 85–86.** Make Proposition 5.21 a remark and add what survives decimation. *Reason:* it is the observation of the sentence before it.
3. **p. 80.** Add the reading of the principle on level sets: every bounded component of {u > α} meets {f > α}. *Reason:* it is immediate from Definition 5.17, it is the finite-step form of causality, and it gives the principle a meaning for images.
4. **pp. 79–80.** Note that the explicit variant, at maxima of the input, is satisfied only by δ_0, and say whether the converse of the stage lemma survives nonnegative inputs and strict maxima. *Reason:* it shows the implicit form is the only nontrivial finite-step reading and how robust the axiom is.
5. **pp. 80–81, p. 96.** Prove the converse on the grid: a symmetric probability mask has the principle on a neighbourhood exactly when its inverse is a stencil on that neighbourhood with nonpositive weights off the origin. *Reason:* the remark after Proposition 6.7 gives the sufficiency; the converse would make the grid selection parallel to the continuum one.
6. **pp. 62–63.** Construct the Matérn pyramid directly, as the infinite convolution of the mixtures of Proposition 5.8(2). *Reason:* it removes three admitted facts and two theorems of an earlier paper from the existence proof.
7. **pp. 66–72.** Move Lemmas 5.5–5.7, Propositions 5.8–5.9, Lemma 5.3, Lemma 5.10 and Proposition 5.11(1)–(2) to the supplement. *Reason:* no later result of the paper uses them.
8. **pp. 42–45; S-pp. 1–8.** Reduce Section 4.1 to a remark, drop Section S1, and merge Proposition 4.5 with Propositions 6.5(3) and 6.8. *Reason:* they are Section 3 and Section 6 at d = 1.
9. **pp. 14–15.** Extend the table of overloaded letters, replace "frame" by "separable", and use one word for step, stage and increment. *Reason:* readability.
10. **p. 55.** Report the observed second-order rate (0.056·(h/ct)² at level 2), the saturation in the level, a second ratio q = 3, and the ratio at which the mask has the binomial mask's width. *Reason:* the table supports more than the text says, and the regime of use is not marked.
11. **pp. 51–53.** Note that the cascade steps λ_{s,t}, 0 < s < t, are not Pólya frequency sequences while the kernels λ_t are. *Reason:* it is the grid counterpart of Theorem S.36 and connects Section 4.3 with the classification of discrete scale-space kernels.
12. **p. 1, p. 5, p. 55, p. 73.** Cite the scale-space pyramids (Crowley, Lowe), the difference-of-Gaussians approximation of the Laplacian and the recent work on discrete approximations of Gaussian smoothing; reword the abstract's sentence on the design literature. *Reason:* the reading of a pyramid as a sampled scale space is standard.
13. **pp. 35, 47.** Cite the classical continuous singular infinitely divisible laws for the fact of required change 2, and the literature on semistable hemigroups for the notion. *Reason:* both are in or next to sources the paper already uses.
14. **p. 58–59.** Say at Definition 5.1 that in the plane the octave step is not a Matérn covariance and that no kernel μ_t is a Matérn law. *Reason:* the name suggests otherwise, and the caveat first appears on p. 108.
15. **p. 78.** Redraw Figure 4 at parameters inside the proof's range, or print W(a − 1)/W(0) and sup K * ρ_δ for the parameters shown. *Reason:* the reader cannot tell from the caption how far the picture is from the proof.
16. **pp. 61, 63, 75, 77, 84.** Small repairs: write the arguments in "Kρ_δ ≤ Mρ_δ + 8a²(K − M)^+"; define g_Σ; "By that lemma" is Theorem 2.9; compare coefficients in the proof of 5.19(3); free the letter c in 5.15(5); reconcile "the one cited fact" of Lemma 5.3 with Table 4. *Reason:* each costs the reader a minute.
17. **p. 49.** Replace "rescaled to the finest grid" by the wording of p. 35. *Reason:* the rescaled weight lives on a grid finer than any grid of the pyramid.
18. **p. 14, p. 64.** Print the reduction of Theorem 2.15 from the pointwise variation-diminishing theorem. *Reason:* Theorem 5.4(3) is the one statement of the block that rests on an admitted fact not in the form of its classical source.
