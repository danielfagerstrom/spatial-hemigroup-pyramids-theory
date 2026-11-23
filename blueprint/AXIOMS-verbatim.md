# The axiom ledger: the sources' wording, verbatim

The companion of `AXIOMS.md` (LINKAGE.md rule 5): for every entry, the source's statement as
printed, transcribed from the page image by the librarian, beside what the draft used it for and
the librarian's verdict. Each section below is copied unchanged from the transcription record it
names, in `records/pyramids/` (2026-11-12); the record states how each page was rendered. Display
mathematics is re-set in LaTeX by hand in the records; the words are as printed. Where a record
quotes a line from a PDF text layer rather than the image, it says so, and no entry rests on such a
line alone.

The definitions that the blueprint restates (chapter 2's definition nodes) come first, under
`## Definitions`; then one `## A<N>` section per ledger entry, in the order of the ledger.

## Definitions

**For `def:cascade-measurement-family`.**

### From `records/pyramids/VERBATIM-V-line.md`, section "Definition -- the axioms (A1)-(A8), (ND)"

**Cite:** fagerstrom2026spatial -- Def. 3.1, printed p. 17 (§ 3.6, "The axiom system")

**Source, verbatim (p. 17).**
> **Definition 3.1** (symmetric cascade measurement family). A family of linear operators
> $\Phi_{s,t} : L^1 \to L^1$, $0 \le s \le t < \infty$, is a *symmetric cascade measurement family* if:
>
> (A1) *Boundedness.* Each $\Phi_{s,t}$ is a bounded operator on $L^1$.
> (A2) *Translation covariance.* $\Phi_{s,t} T_a = T_a \Phi_{s,t}$ for every $a \in \mathbb{R}$.
> (A3) *Reflection symmetry.* $\Phi_{s,t} R = R \Phi_{s,t}$.
> (A4) *Positivity.* $\Phi_{s,t} L^1_+ \subseteq L^1_+$.
> (A5) *Unit mass.* $\int \Phi_{s,t} f = \int f$ for every $f \in L^1_+$.
> (A6) *Cascade (hemigroup).* $\Phi_{t,t} = \mathrm{Id}$, and $\Phi_{s,t}\Phi_{r,s} = \Phi_{r,t}$ for all $r \le s \le t$.
> (A7) *Continuity.* For every $f \in L^1$ the map $(s,t) \mapsto \Phi_{s,t} f$ is continuous from $\{0 \le s \le t\}$ to $L^1$.
> (A8) *Scale covariance.* There is a family $(S_\lambda)_{\lambda>0}$ of increasing bijections of $[0,\infty)$ with $D_\lambda \Phi_{s,t} = \Phi_{S_\lambda s,\, S_\lambda t} D_\lambda$ for all $0 \le s \le t$ and all $\lambda > 0$.
> (ND) *Nondegeneracy.* $\Phi_{s,t} \ne \mathrm{Id}$ whenever $s < t$.

The actions are defined on p. 7: $(T_a f)(x) = f(x-a)$; $(Rf)(x) = f(-x)$; $(D_\lambda f)(x) = \lambda^{-1} f(x/\lambda)$.

**Used as (the draft, lines 47-57):** the eight axioms and (ND) restated in the draft's own wording,
with $D_\lambda$ written out.

**Verdict: MATCH.** Each draft clause says what the printed one says (the draft's "nonnegative
functions to nonnegative functions" is $L^1_+ \subseteq L^1_+$; its $D_\lambda$ is the one on p. 7).
Page 17 is correct.

**For `def:isotropic-cascade-family` (the operator form, iso Def. 3.1, named in its annotation).**

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "Def. 3.1 (iso) -- isotropic cascade measurement family (operator axioms)"

**Cite:** fagerstrom2026isotropic -- Def. 3.1, printed **pp. 10-11** ((A1)-(A3) at the foot of p. 10; (A4)-(A8), (ND) on p. 11); the draft gives p. 10 (cat. A40)

**Source, verbatim (p. 10, preface and Def. 3.1).**
> The axioms are those of the line, Definition 2.1, with $\mathbb{R}^d$ in place of $\mathbb{R}$ and the orthogonal group in place of the reflection. They are stated on operators, which assumes neither a convolution nor a probability kernel, and on kernels, which is the form the proofs use. Lemma 3.3 joins the two. The operator $\Phi_{s,t}$ takes the record of an image at scale $s$ to its record at the coarser scale $t$.
>
> **Definition 3.1** (isotropic cascade measurement family). Fix an integer $d\ge1$. On the real space $L^1(\mathbb{R}^d)$ write $T_af:=f(\cdot-a)$ for the translation by $a\in\mathbb{R}^d$, $R_Qf:=f(Q^{-1}\cdot)$ for the action of an orthogonal matrix $Q\in\mathrm{O}(d)$, and $D_\lambda f:=\lambda^{-d}f(\cdot/\lambda)$ for the dilation by $\lambda>0$. A family $(\Phi_{s,t})_{0\le s\le t}$ of linear operators on $L^1(\mathbb{R}^d)$ is an *isotropic cascade measurement family in dimension $d$* if:
>
> (A1) each $\Phi_{s,t}$ is a bounded operator on $L^1(\mathbb{R}^d)$;
> (A2) *(translation invariance)* $\Phi_{s,t}T_a=T_a\Phi_{s,t}$ for every $a\in\mathbb{R}^d$;
> (A3) *(rotation invariance)* $\Phi_{s,t}R_Q=R_Q\Phi_{s,t}$ for every $Q\in\mathrm{O}(d)$;

**(p. 11, head).**
> (A4) *(positivity)* $\Phi_{s,t}$ maps nonnegative functions to nonnegative functions;
> (A5) *(mass)* $\int\Phi_{s,t}f=\int f$ for every nonnegative $f\in L^1(\mathbb{R}^d)$;
> (A6) *(cascade)* $\Phi_{t,t}=\mathrm{Id}$, and $\Phi_{s,t}\Phi_{r,s}=\Phi_{r,t}$ whenever $r\le s\le t$;
> (A7) *(continuity)* for every $f\in L^1(\mathbb{R}^d)$ the map $(s,t)\mapsto\Phi_{s,t}f$ is continuous from $\{0\le s\le t\}$ to $L^1(\mathbb{R}^d)$;
> (A8) *(dilation covariance)* there is a family $(S_\lambda)_{\lambda>0}$ of increasing bijections of $[0,\infty)$ with $D_\lambda\Phi_{s,t}=\Phi_{S_\lambda s,S_\lambda t}D_\lambda$ for all $0\le s\le t$ and all $\lambda>0$;
> (ND) *(nondegeneracy)* $\Phi_{s,t}\neq\mathrm{Id}$ whenever $s<t$.

**Used as (the draft, lines 77, 770):** the operator axioms (A1)-(A8), (ND) in $\mathbb{R}^d$, "with the rotations in place of the reflection".

**Verdict: MATCH.** Page range corrected to pp. 10-11. A definition, so no axiom is needed.

**For `def:isotropic-cascade-family`.**

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "Def. 3.2 (iso) -- isotropic cascade family (kernel axioms)"

**Cite:** fagerstrom2026isotropic -- Def. 3.2, printed p. 11 (cat. A41)

**Source, verbatim (p. 11).**
> **Definition 3.2** (isotropic cascade family). Fix an integer $d\ge1$. For $A\in\mathrm{GL}(d)$ write $A_*\mu:=\mu\circ A^{-1}$ for the image of a measure $\mu$ on $\mathbb{R}^d$, and $\hat\mu(\xi)=\int e^{i\langle\xi,x\rangle}\mu(dx)$, so that $\widehat{A_*\mu}(\xi)=\hat\mu(A^{\mathsf T}\xi)$. An *isotropic cascade family in dimension $d$* is a family $(\mu_{s,t})_{0\le s\le t}$ of probability measures on $\mathbb{R}^d$ such that
>
> (I1) *(cascade)* $\mu_{t,t}=\delta_0$, and $\mu_{r,t}=\mu_{s,t}*\mu_{r,s}$ whenever $r\le s\le t$;
> (I2) *(continuity)* for every $\xi\in\mathbb{R}^d$ the map $(s,t)\mapsto\hat\mu_{s,t}(\xi)$ is continuous on $\{0\le s\le t\}$;
> (I3) *(rotation invariance)* $Q_*\mu_{s,t}=\mu_{s,t}$ for every $Q\in\mathrm{O}(d)$ and every pair;
> (I4) *(dilation covariance)* there is a family $(S_\lambda)_{\lambda>0}$ of increasing bijections of $[0,\infty)$ with $(\lambda I)_*\mu_{s,t}=\mu_{S_\lambda s,S_\lambda t}$ for every $\lambda>0$ and every pair;
> (ND) *(nondegeneracy)* $\mu_{s,t}\neq\delta_0$ whenever $s<t$.
>
> The two definitions correspond axiom by axiom. (I1) is the cascade (A6), (I2) the continuity (A7), (I3) the rotation invariance (A3), (I4) the dilation covariance (A8) with the same bijections $S_\lambda$, and (ND) is (ND).

**Used as (the draft, lines 69, 368, 770):** the axioms (I1)-(I4), (ND); line 368 takes (I1), (I2), (ND), restates (I3) as "$Q_*\mu=\mu$" and (I4) at one dilation.

**Verdict: MATCH.** The draft's (I4) "$D_\lambda\mu_{s,t}=\mu_{S_\lambda s,S_\lambda t}$" is the page's $(\lambda I)_*\mu_{s,t}$ in the draft's own notation for the dilation of a measure.

**For `def:isotropic-origin-data`.**

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "Def. 3.10 (iso) -- isotropic origin data, the polar profile"

**Cite:** fagerstrom2026isotropic -- Def. 3.10, printed p. 15 (cat. A49)

**Source, verbatim (p. 15).**
> **Definition 3.10** (isotropic origin data in dimension $d$, and the polar profile). Fix an integer $d\ge1$ and write $\sigma_{d-1}$ for the surface measure of the unit sphere $S^{d-1}\subset\mathbb{R}^d$ and $|S^{d-1}|=\sigma_{d-1}(S^{d-1})$ for its surface area. An *isotropic origin datum in dimension $d$* is a pair $(a,k_d)$ with $a\ge0$ and $k_d:(0,\infty)\to[0,\infty)$ nonincreasing, subject to
> $$\int_0^1k_d(r)\,r\,dr<\infty\qquad\text{and}\qquad\int_1^\infty k_d(r)\,\frac{dr}{r}<\infty.$$
> Its Lévy measure is the rotation-invariant measure $\nu_d$ on $\mathbb{R}^d\setminus\{0\}$ with radial density $f_d(r)=k_d(r)\big(|S^{d-1}|\,r^d\big)^{-1}$, so that
> $$\int_{\mathbb{R}^d}g\,d\nu_d=\frac1{|S^{d-1}|}\int_{S^{d-1}}\sigma_{d-1}(d\eta)\int_0^\infty g(r\eta)\,k_d(r)\,\frac{dr}{r}\tag{3.2}$$
> for every nonnegative Borel $g$ vanishing at the origin. Its *exponent* is
> $$F_d(\xi)=\tfrac12a|\xi|^2+\int_{\mathbb{R}^d}\big(1-\cos\langle\xi,x\rangle\big)\,\nu_d(dx),\qquad\xi\in\mathbb{R}^d,\tag{3.3}$$
> and its *law* is the symmetric infinitely divisible law $\mu$ on $\mathbb{R}^d$ with $\hat\mu=e^{-F_d}$. We call $k_d$ the datum's *polar profile* and $c:=k_d(0+)\in[0,\infty]$ its *profile at the origin*. The datum is *subordinated* when there is a delay datum $(a,k_{\mathrm I})$ in the sense of §2.3, with $k_{\mathrm I}$ nonincreasing, whose polar profile [16, (4.6)] is $k_d$: [(3.4)]

**Used as (the draft, lines 376, 418, 428, 553):** the Gaussian coefficient $a\ge0$ enters as $\tfrac12a|\omega|^2$, the polar profile is nonincreasing, the Lévy measure has radial density $k_d(|x|)(|S^{d-1}||x|^d)^{-1}$, the jump rate on $r_1<|x|<r_2$ is $\int k_d\,dr/r$; line 553 uses "the integrability conditions of Def. 3.10".

**Verdict: MATCH.** The draft's prose at 418 omits the two integrability conditions; the blueprint's definition must carry them (they are in the definition, and line 553 uses them). The Gaussian coefficient is $\tfrac12a$ here against $a_{\mathrm V}$ on the line (the page says $a=2a_{\mathrm V}$, p. 15; Prop. 3.11(2) on p. 16 gives $a_{\mathrm V}=\tfrac12a'$), which line 376 records.

**For `def:self-decomposable`.**

### From `records/pyramids/VERBATIM-Sato.md`, section "Def. 15.1 -- selfdecomposable and semi-selfdecomposable laws"

**Cite:** sato1999levy -- Definition 15.1, printed p. 90 (the definition with (15.1), at the foot of the page, opening Section 15).

**Source, verbatim (p. 90).**
> DEFINITION 15.1. Let $\mu$ be a probability measure on $\mathbb{R}^d$. It is called *selfdecomposable*, or *of class L*, if, for any $b > 1$, there is a probability measure $\rho_b$ on $\mathbb{R}^d$ such that
>
> (15.1) $\quad \hat\mu(z) = \hat\mu(b^{-1}z)\,\hat\rho_b(z).$
>
> It is called *semi-selfdecomposable* if there are some $b > 1$ and some infinitely divisible probability measure $\rho_b$ satisfying (15.1). If $\mu$ is semi-selfdecomposable, then $b$ in the definition is called a *span* of $\mu$.

**Used as (the draft, lines 61, 134, 402, 457):** the definitions of "self-decomposable" (for every $c \in (0,1)$ a probability law $\rho_c$ with $\hat\mu(\omega) = \hat\mu(c\omega)\hat\rho_c(\omega)$) and "semi-selfdecomposable with span $q > 1$" (some infinitely divisible $\rho_q$ with $\hat\mu = \hat\mu(q^{-1}\cdot)\hat\rho_q$, the residual).

**Verdict: MATCH.** The draft's $c$ is Sato's $b^{-1}$; the definitions agree word for word, including that $\rho_b$ is only a probability measure in the selfdecomposable case and is required infinitely divisible in the semi case (the selfdecomposable $\rho_b$ is infinitely divisible by Prop. 15.5, A43). The gloss at line 61, "the law of $cX + Y_c$ with $Y_c$ independent of $X$", is the equivalent probabilistic form and is not printed on p. 90; it is a one-line equivalence and may stay a gloss.

**For `def:complete-bernstein`, `def:thorin-bernstein`.**

### From `records/pyramids/VERBATIM-literature.md`, section "Definitions -- complete Bernstein (Def. 6.1) and Thorin-Bernstein (Def. 8.1)"

**Cite:** schilling2012bernstein -- Definition 6.1, printed p. 69; Definition 8.1, printed p. 109; both refer to the representation (3.2) of Theorem 3.2, printed p. 21 (also rendered).

**Source, verbatim (p. 69, Def. 6.1).**
> **Definition 6.1.** A Bernstein function $f$ is said to be a *complete Bernstein function* if its Levy measure $\mu$ in (3.2) has a completely monotone density $m(t)$ with respect to Lebesgue measure,
> $$f(\lambda) = a + b\lambda + \int_{(0,\infty)}(1 - e^{-\lambda t})\,m(t)\,dt. \qquad (6.1)$$
> We will use $\mathcal{CBF}$ to denote the collection of all complete Bernstein functions.

**Source, verbatim (p. 109, Def. 8.1).**
> **Definition 8.1.** A Bernstein function $f$ is called a *Thorin-Bernstein function* if the Levy measure $\mu$ from (3.2) has a density $m(t)$ such that $t \mapsto t\cdot m(t)$ is completely monotone, i.e.
> $$f(\lambda) = a + b\lambda + \int_{(0,\infty)}(1 - e^{-\lambda t})\,m(t)\,dt, \qquad (8.1)$$
> where $a, b \ge 0$, $\int_{(0,\infty)}(1\wedge t)\,m(t)\,dt < \infty$ and $t \mapsto t\cdot m(t)$ is completely monotone. We will use $\mathcal{TBF}$ to denote the family of all Thorin-Bernstein functions.

Same page: "Observe that the complete monotonicity of $t \mapsto t\cdot m(t)$ implies immediately that $m(t) = t^{-1}\cdot(t\cdot m(t))$ is completely monotone. Therefore, $\mathcal{TBF} \subset \mathcal{CBF}$."

**Source, verbatim (p. 21, Thm. 3.2, the representation (3.2) the definitions use).**
> **Theorem 3.2.** A function $f : (0,\infty) \to \mathbb{R}$ is a Bernstein function if, and only if, it admits the representation
> $$f(\lambda) = a + b\lambda + \int_{(0,\infty)}(1 - e^{-\lambda t})\,\mu(dt), \qquad (3.2)$$
> where $a, b \ge 0$ and $\mu$ is a measure on $(0,\infty)$ satisfying $\int_{(0,\infty)}(1\wedge t)\,\mu(dt) < \infty$. In particular, the triplet $(a,b,\mu)$ determines $f$ uniquely and vice versa.

**Verdict: both pages correct** (p. 69, p. 109). Def. 6.1 does not restate $a, b \ge 0$ and the $(1\wedge t)$ integrability; they come from (3.2) through "Bernstein function". Def. 8.1 restates them. A blueprint definition should quote (3.2) first, or carry those hypotheses itself.

## A1

### From `records/pyramids/VERBATIM-V-line.md`, section "A1 -- each operator is a convolution with a symmetric probability measure"

**Cite:** fagerstrom2026spatial -- Lemma 4.1 (representation), printed pp. 22-23 (§ 4; the statement
begins at the foot of p. 22 and its symmetry clause is at the top of p. 23)

**Source, verbatim (pp. 22-23).**
> **Lemma 4.1** (representation). *Under (A1), (A2), (A4), (A5), for each pair $0 \le s \le t$ there is a unique probability measure $\mu_{s,t}$ on $\mathbb{R}$ with*
> $$\Phi_{s,t} f = \mu_{s,t} * f, \qquad f \in L^1;$$
> *under (A3) it is symmetric, $R\mu_{s,t} = \mu_{s,t}$. Conversely every symmetric probability measure on $\mathbb{R}$ defines an operator satisfying (A1)-(A5).*

The sentence that introduces it (p. 22, the opening of § 4): "The aim is Lemma 4.1: under (A1)-(A5)
every operator $\Phi_{s,t}$ is a convolution by a symmetric probability measure $\mu_{s,t}$ on $\mathbb{R}$,
so the apertures of §3 are measures."

**Used as (the draft, line 59):** "Each $\Phi_{s,t}$ is then the convolution with a symmetric
probability measure $\mu_{s,t}$ [V-line v0.1, § 4, p. 22]", after all of (A1)-(A8) are stated.

**Verdict: NARROWER-OK.** The draft assumes more than the lemma needs ((A1)-(A5) suffice). The
citation should name the statement, Lemma 4.1, and give pp. 22-23: p. 22 carries existence and
uniqueness, p. 23 the symmetry under (A3). "§ 4, p. 22" alone misses the symmetry clause.

## A4

### From `records/pyramids/VERBATIM-V-line.md`, section "A4 -- the classification on the line"

**Cite:** fagerstrom2026spatial -- Thm. 7.3 (main theorem), printed p. 37

**Source, verbatim (p. 37).**
> **Theorem 7.3** (main theorem). *A family $(\Phi_{s,t})_{0\le s\le t}$ satisfies (A1)-(A8) and (ND) if and only if there are an increasing bijection $\chi$ of $[0,\infty)$, the gauge, and a function $F$ of the form (2.3) with $F \not\equiv 0$, such that*
> $$\Phi_{s,t} f = \mu_{s,t} * f, \qquad \hat\mu_{s,t}(\omega) = \exp\!\big[-\big(F(\chi(t)\,\omega) - F(\chi(s)\,\omega)\big)\big].$$
> *In the canonical gauge the kernel at scale $t$ is the symmetric probability measure $\phi_t$ with $\hat\phi_t = e^{-F(t\,\cdot)}$, and the pair $(\chi, F)$ is unique up to the normalization $\chi(1) = 1$.*

Following text (p. 37): "In the canonical gauge, what the axioms leave free is exactly the pair
$(a,k)$ of (2.3): a Gaussian variance and a nonincreasing displacement profile. The Gaussian scale
space is $(a, 0)$." And: "The theorem is machine-checked in all three clauses (construction, analysis,
uniqueness) and its trust base is Lean core together with two cited facts and no more: Bochner's
theorem in the forward direction, and the symmetric Lévy-Khintchine representation at its converse and
its uniqueness clauses (§1.1)."

**Used as (the draft, line 65, "Theorem 2.0"):** the same equivalence, with $F \not\equiv 0$ of the form
(2.0), and "the pair $(\chi,F)$ is unique once $\chi(1) = 1$".

**Verdict: MATCH.** The draft's clause is the paper's, in the same hypotheses and conclusion; the
draft's (2.0) is the paper's (2.3) plus integrability (see A3). Page 37 is correct (the statement and
the first lines of the proof fill the lower half of the page; the proof continues on p. 38).

## A9

The plan's A8 (display (2.2)) and A9 (its uniqueness clause) are one statement on p. 9; both sections of the record are copied.

### From `records/pyramids/VERBATIM-V-line.md`, section "A8 -- display (2.2), the Lévy representation"

**Cite:** fagerstrom2026spatial -- display (2.2), printed p. 9, inside Prop. 2.3(3) (the Lévy-Khintchine clause)

**Source, verbatim (p. 9).**
> 3. (Lévy-Khintchine, symmetric form.) *Every $\psi \in \mathrm{ND}_s$ has the representation*
> $$\psi(\omega) = a\,\omega^2 + \int_{(0,\infty)} (1 - \cos \omega x)\,\nu(dx), \qquad a \ge 0, \qquad \int_{(0,\infty)} (1 \wedge x^2)\,\nu(dx) < \infty, \tag{2.2}$$
> *the pair $(a,\nu)$ being unique; and conversely every such pair defines a member of $\mathrm{ND}_s$.*

The measure $\nu$ lives on $(0,\infty)$: the folded form. The text on p. 10 ("The folding convention")
says a two-sided symmetric Lévy measure $\nu_2$ on $\mathbb{R} \setminus \{0\}$ enters (2.2) as its image
under $x \mapsto |x|$.

**Used as (the draft, line 140):** "matching the representations [V-line, (2.2)], unique by
[Prop. 2.3(3)]", with $\Psi_t$ having data $(a(t), \varpi_t)$ on $(0,\infty)$.

**Verdict: MATCH.** The draft's folded $\varpi$ is the paper's $\nu$. Page 9; the display is inside
Prop. 2.3(3), so A8 and A9 are one statement on one page.

### From `records/pyramids/VERBATIM-V-line.md`, section "A9 -- Prop. 2.3(3): uniqueness of the representation"

**Cite:** fagerstrom2026spatial -- Prop. 2.3(3), printed p. 9 (clause 3 of "the Fourier toolbox")

**Source, verbatim (p. 9).** The clause quoted under A8: "[...] *the pair $(a,\nu)$ being unique; and
conversely every such pair defines a member of $\mathrm{ND}_s$.*" Sources note on the same page: "Clause
(3) is [31], Thm. 8.1, pp. 37-38, whose parts (i), (ii) and (iii) are existence, uniqueness and the
converse". Remark after Def. 2.5 (p. 10): the Lean development takes "the converse and uniqueness
clauses of (3)" and uses "Clause (2), the existence half of (3) and clause (4) [...] by no proof".

**Used as (the draft, line 140):** "matching the representations (2.2), unique by Prop. 2.3(3), the
second [display]": the identification of the pairs from equality of the functions.

**Verdict: MATCH.** Uniqueness of $(a,\nu)$ from the function $\psi$ is exactly the clause. Page 9.

## A13

Prop. 6.2 with (6.2), read with this clause for the generator and its domain, is transcribed under A12 of the same record, p. 56 (Definition 6.1 and Proposition 6.2), and that section is copied after this one. A12 itself (the Thorin clause, Prop. 6.4(4)) is not an entry.

### From `records/pyramids/VERBATIM-V-cone.md`, section "A13 -- Cin-ray generator (Prop. 6.4(5))"

**Cite:** fagerstrom2026cone -- Prop. 6.4(5), printed p. 58 (clause (5) of the generators of the corners).

**Source, verbatim (p. 58).**
> **Proposition 6.4** (the generators of the corners). *In the canonical gauge, and with $\mathrm{Lap}_\theta$ denoting convolution by the Laplace kernel $\frac{1}{2\theta}e^{-|x|/\theta}$ of range $\theta$:* ...
> 5. *Cin ray of step $\tau$: $\mathcal{A}_t = \frac1t\,\delta^2_{t\tau}$, a single symmetric second difference, where $\delta_h^2 g := \frac12\big(g(\cdot - h) + g(\cdot + h)\big) - g$.*

**Used as (the draft, lines 85, 189):** "Its generator is a single symmetric second difference, $\mathcal{H}_t = t^{-1}\delta^2_{t\tau}$"; the knot-atom cascade applies one second-difference step $\delta^2_{r\theta q^n}$ at each knot.

**Verdict: MATCH.** Same operator and same $\delta^2_h$ convention (average of the neighbours minus the value, symbol $\cos\omega h - 1 \le 0$). The clause on the page has no explicit domain; Schwartz functions are inside the class of Prop. 6.2.

### From `records/pyramids/VERBATIM-V-cone.md`, section "A12 -- Generator of a Thorin family (Prop. 6.4(4)); with Prop. 6.2, 6.4(1), 6.4(3)"

**Cite:** fagerstrom2026cone -- Prop. 6.4(4), printed p. 58 (clause (4) of "the generators of the corners"); also Prop. 6.2
with display (6.2), printed p. 56, and Prop. 6.4(1), (3), printed p. 58.

**Source, verbatim (p. 56): Definition 6.1 and Proposition 6.2.**
> **Definition 6.1** (the signal class). $\mathcal{D} := \mathscr{S}(\mathbb{R})$ is the Schwartz class on the line: smooth functions all of whose derivatives decay faster than every polynomial. It is contained in $L^1$, is stable under differentiation, and its Fourier image is itself.
>
> **Proposition 6.2** (the scale evolution in generator form). *Let $F$ be admissible with data $(a,k)$ and $\varpi = -dk$, and let $u(t,\cdot) := \mu_{0,t} * f$ be the scale space of $f \in \mathcal{D}$ in the canonical gauge. Then on the Fourier side*
> $$\partial_t \hat u(t,\omega) = -\frac1t\, B(t\omega)\,\hat u(t,\omega), \qquad B(\omega) = \omega F^\prime(\omega) = 2a\omega^2 + \int_{(0,\infty)} (1 - \cos\omega v)\,\varpi(dv), \tag{6.1}$$
> *for every $\omega$ and every $t > 0$, and on the signal side*
> $$\partial_t u(t,x) = \mathcal{A}_t u(t,x), \qquad \mathcal{A}_t g(x) := 2at\,g^{\prime\prime}(x) - \frac1t \int_{(0,\infty)} \Big[ g(x) - \tfrac12\big(g(x - tv) + g(x + tv)\big) \Big]\,\varpi(dv), \tag{6.2}$$
> *the integral converging absolutely for $g \in \mathcal{D}$. The generators at different scales are conjugate, $\mathcal{A}_t = t^{-1} D_t \mathcal{A}_1 D_t^{-1}$, with $\mathcal{A}_1 = -B(D)$ and $D = -i\partial_x$; in log-scale $\theta = \log t$ the evolution reads $\partial_\theta u = D_t \mathcal{A}_1 D_t^{-1} u$.*

**Source, verbatim (p. 58): Proposition 6.4.**
> **Proposition 6.4** (the generators of the corners). *In the canonical gauge, and with $\mathrm{Lap}_\theta$ denoting convolution by the Laplace kernel $\frac{1}{2\theta}e^{-|x|/\theta}$ of range $\theta$:*
>
> 1. *Gaussian: $\mathcal{A}_t = 2at\,\partial_x^2$, the heat equation $\partial_v u = \partial_x^2 u$ in the variance gauge $v = at^2$.*
> 2. *Symmetric stable, $F = |\omega|^\alpha$ with $0 < \alpha < 2$: $\mathcal{A}_t = -\alpha t^{\alpha-1}(-\partial_x^2)^{\alpha/2}$, the fractional Laplacian; in $v = t^\alpha$ the equation is $\partial_v u = -(-\partial_x^2)^{\alpha/2}u$, and the jump measure is $\varpi(dv) = C_\alpha^{-1}\alpha\,v^{-\alpha-1}dv$.*
> 3. *Matérn, $F = \gamma\log(1+\omega^2)$: $\mathcal{A}_t = \frac{2\gamma}{t}(\mathrm{Lap}_t - I)$, a bounded operator of norm at most $4\gamma/t$. It is the generator of a compound Poisson process, whose jumps are Laplace-distributed of range $t$ and arrive at the rate $2\gamma/t$.*
> 4. *Thorin members, with Thorin measure $U$ as in (5.1) and $a = 0$:*
> $$\mathcal{A}_t = \frac1t \int_{(0,\infty)} \big(\mathrm{Lap}_{t/\theta} - I\big)\,U(d\theta),$$
> *the Thorin mixture of Matérn generators, as an identity at every $g$ that is twice continuously differentiable with $g$ and $g^{\prime\prime}$ bounded. Under the hypothesis of Remark 5.11 the Student-$t$ family is the case of the Bessel Thorin measure: $U$ is twice the image of the causal $U_{\mathrm I}$ of (5.2) under $\theta \mapsto \sqrt{2\theta}$, by Proposition 5.7(3).*
> 5. *Cin ray of step $\tau$: $\mathcal{A}_t = \frac1t\,\delta^2_{t\tau}$, a single symmetric second difference, where $\delta_h^2 g := \frac12\big(g(\cdot - h) + g(\cdot + h)\big) - g$.*

(Proof on p. 58: "(1) is Proposition 6.2 with $\varpi = 0$." and "(3) and (4) are one computation. For $\theta > 0$, $\int_0^\infty [g - \frac12(g(\cdot - v) + g(\cdot + v))]\,\theta e^{-\theta v}\,dv = g - \mathrm{Lap}_{1/\theta}\,g$, because ...". The rest is on p. 59, not rendered.)

**Used as (the draft, lines 83-85, 189, 230, 237):** Lines 83-84 restate 6.2 as $\mathcal{H}_t g = 2at\,g^{\prime\prime} + t^{-1}\int \delta^2_{tv}g\,\kappa(dv)$, $\kappa = -dk$, $\delta^2_h g = \frac12(g(x-h)+g(x+h)) - g(x)$, on Schwartz $f$; line 85 cites 6.4(1), 6.4(5), and 6.4(3)-(4) ("the Matérn and Thorin clauses ... which sum (2.0 double-prime) over Laplace kernels"); lines 230 and 237(4) use 6.4(4) for $\mathcal{H}_t = \frac2t\sum_{i\ge1}(L_{ctq^{-i}} - I)$.

**Verdict: MATCH** (6.2, 6.4(1), 6.4(3)); **NARROWER-OK** (6.4(4)).
- 6.2: the operator of the draft is (6.2) with the sign absorbed, $-\frac1t\int[g - \frac12(\dots)]\varpi = +\frac1t\int\delta^2_{tv}g\,\varpi$; same domain ($\mathscr S(\mathbb R)$), same equation $\partial_t u = \mathcal A_t u$.
- 6.4(4): with $U = \sum_{i\ge1}2\delta_{q^i/c}$ (see A18) the clause gives $\frac1t\sum_i 2(\mathrm{Lap}_{t/\theta_i} - I) = \frac2t\sum_i(\mathrm{Lap}_{ctq^{-i}} - I)$, since $t/\theta_i = ctq^{-i}$: the formula of the draft. The draft states it without the hypotheses on the page: $a = 0$, and the identity only at $g \in C^2$ with $g$, $g^{\prime\prime}$ bounded. The blueprint must carry that domain.
- Catalogue row A15 describes 6.4(3) as "Matern kernel at scale t has transform $(1+t^2\omega^2)^{-1}$". That is not what 6.4(3) says (it is Prop. 5.2(2) at $\gamma = 1$); 6.4(3) is the generator $\frac{2\gamma}{t}(\mathrm{Lap}_t - I)$. The line-85 sentence of the draft uses 6.4(3) correctly.

## A15

Added in review round 3, batch C (2026-11-23), when A15 became an entry (decision D3). The
librarian re-read the statement from the page images of pp. 15-16 that day and found it as below,
the extreme-rays sentence inside the statement (`records/pyramids/reviews/LIBRARIAN-r3.md`, "For
batch C"); the "Lemma 3.1" at its head is the display (3.1) of Lemma 3.1(2).

### From `records/pyramids/VERBATIM-V-cone.md`, section "A15 -- Choquet structure of the admissible cone (Prop. 3.3)"

**Cite:** fagerstrom2026cone -- Prop. 3.3, printed p. 15 (the statement opens at the foot of p. 15 and ends at the top of p. 16).

**Source, verbatim (pp. 15-16).**
> **Proposition 3.3** (Choquet structure of the admissible cone). *The superposition map of Lemma 3.1,*
> $$ (a,\varpi) \mapsto F, \qquad F(\omega) = a\omega^2 + \int_{(0,\infty)} \mathrm{Cin}(\tau\omega)\,\varpi(d\tau),$$
> *is a linear bijection from $\lbrace (a,\varpi) : a \ge 0,\ \varpi$ a positive Borel measure on $(0,\infty)$, $\int[\tau^2 \wedge (1 + \log_+\tau)]\,\varpi(d\tau) < \infty\rbrace$ onto the cone of Lemma 2.7, with inverse $\varpi = -dk$, $k(x) = \varpi((x,\infty))$, and $a$ the Gaussian coefficient. Consequently the extreme rays of the cone are the Gaussian ray $\omega \mapsto \omega^2$ together with the one-parameter family $\mathrm{Cin}(\tau\,\cdot)$, $\tau > 0$, whose folded Lévy densities are $x^{-1}\mathbf 1_{(0,\tau)}(x)$; and every admissible family is a unique superposition of* Cin *rays and Gaussian jitter, the term $a\omega^2$.*

(Proof, p. 16: "... the two integrability conditions of Lemma 2.3 are the domain condition read through Tonelli ... Since $\frac12(\tau\wedge1)^2 + \log_+\tau \le \tau^2\wedge(1+\log_+\tau) \le 2[\frac12(\tau\wedge1)^2 + \log_+\tau]$ for" (page breaks).)

**Used as (the draft, lines 85, 187, 235, 247):** the Choquet representation $F(\omega) = a\omega^2 + \int\mathrm{Cin}(\tau\omega)\,\kappa(d\tau)$, unique, with $\kappa = -dk$ (line 85); the integrability condition $\int[(r\theta)^2 \wedge (1 + \log_+(r\theta))]\,\sigma < \infty$ of Thm 2.11, marked "check against Prop. 3.3" (line 187); closure "Lemma 2.7 with Prop. 3.3" (lines 235, 247).

**Verdict: MATCH** for lines 85 and 187. The condition at 187 is the condition $\tau^2 \wedge (1 + \log_+\tau)$ of Prop. 3.3 with $\tau = r\theta$ on the cylinder, so the check marked on line 187 is resolved: it agrees. For lines 235, 247 see A16.

## A19

### From `records/pyramids/VERBATIM-V-cone.md`, section "A19 -- Prop. 7.2: the Matérn cascade, forward-backward first-order sections"

**Cite:** fagerstrom2026cone -- Prop. 7.2, printed p. 60 (the statement opens at the foot of p. 60 with (7.1); the realization and (7.2) continue on p. 61; proof on p. 61).

**Source, verbatim (pp. 60-61).**
> **Proposition 7.2** (the Matérn cascade: forward-backward first-order sections). *For the Matérn family with integer $\gamma$, so that $e^{-F(t\omega)} = (1 + t^2\omega^2)^{-\gamma}$, the increment between adjacent knots has transform*
> $$ \hat\mu_{t_k,t_{k+1}}(\omega) = \Big(\frac{1 + t_k^2\omega^2}{1 + t_{k+1}^2\omega^2}\Big)^{\gamma} = \Big(\frac{1 + it_k\omega}{1 + it_{k+1}\omega}\cdot\frac{1 - it_k\omega}{1 - it_{k+1}\omega}\Big)^{\gamma}, \tag{7.1}$$
> *[p. 61]* *a cascade of $\gamma$ identical causal first-order pole-zero sections in $x$, called* lag sections *below, and $\gamma$ identical anticausal ones, each with the one-state realization*
> $$ w^\prime = \frac{y - w}{t_{k+1}}\ \text{(forward)}, \qquad v = \frac{t_k}{t_{k+1}}\,y + \Big(1 - \frac{t_k}{t_{k+1}}\Big)w,$$
> *and its mirror image run backward. Which solution of the state equation is meant is part of the realization: its solutions differ by a multiple of $e^{-x/t_{k+1}}$, and the one intended is the solution in $L^1$, equivalently the one with $w(-\infty) = 0$ for the forward pass and $w(+\infty) = 0$ for the backward one. The zero of the transfer function costs no differentiation of the input: the output is a convex combination of the input and the state. The section's kernel is the mixture $\frac{t_k}{t_{k+1}}\delta_0 + (1 - \frac{t_k}{t_{k+1}})\mathrm{Exp}_+(t_{k+1})$ of no displacement and a one-sided exponential displacement, $\mathrm{Exp}_\pm(t)$ denoting the one-sided exponential kernels $t^{-1}e^{-|x|/t}$ carried by $\pm(0,\infty)$; so the two-sided increment for $\gamma = 1$ is the four-term mixture*
> $$ r^2\delta_0 + r(1 - r)\big(\mathrm{Exp}_+ + \mathrm{Exp}_-\big) + (1 - r)^2\,\mathrm{Lap}_{t_{k+1}}, \qquad r := \frac{t_k}{t_{k+1}} \in (0,1), \tag{7.2}$$
> *where $\mathrm{Exp}_\pm$ are taken at the range $t_{k+1}$ and $\mathrm{Lap}_t$ is the Laplace kernel of range $t$; positivity and unit mass are manifest at the realization level. Sampled on a grid, a full scale space over $M$ knots costs $2\gamma M$ first-order states and $O(\gamma M)$ multiply-adds per sample, in a forward and a backward pass at each knot. Sampling the signal is a separate approximation and is not treated here.*

(Printing notes: the connecting words between "(7.1)," and "a cascade of" are absent in the source on both pages, and the text layer confirms it; read: the increment has transform (7.1), [and is] a cascade of ... Proof, p. 61: "The increment transform is the ratio of the endpoint transforms, the denominators being nonvanishing (Lemma 4.2 of [17]), which is Proposition 5.2(2); the factorization is $1 + t^2\omega^2 = (1 + it\omega)(1 - it\omega)$ ... and the convex-combination clause is $0 < t_k/t_{k+1} < 1$ ... For (7.2), convolve the causal and anticausal mixtures and use $\mathrm{Exp}_+(t) * \mathrm{Exp}_-(t) = \mathrm{Lap}_t$, whose transform identity is $(1 + it\omega)^{-1}(1 - it\omega)^{-1} = (1 + t^2\omega^2)^{-1}$.")

**Used as (the draft, lines 227, 230, 237):** "its ladder is realized exactly by one forward-backward first-order section per octave ([V-cone, section 7, Prop. 7.2])", at $\gamma = 1$; line 227: "one Laplace kernel of range $ct$ per octave".

**Verdict: NARROWER-OK on the count; one caveat on the case.** The count on the page is $2\gamma$ first-order sections per step ($\gamma$ forward, $\gamma$ backward), so "one forward-backward section per octave" at $\gamma = 1$ is the count of the page. The rung of the draft is $\Phi_{t,qt}$ with transform $(1 + c^2t^2\omega^2)^{-1}$, the Matérn kernel from the origin at range $ct$: the increment of Prop. 7.2 with $t_k = 0$ (Prop. 7.1 allows $t_0 = 0$). The clause as printed has $r \in (0,1)$ and the proof says "the convex-combination clause is $0 < t_k/t_{k+1} < 1$": the degenerate $t_k = 0$ (section kernel $\mathrm{Exp}_+(t_{k+1})$, two-sided increment $\mathrm{Lap}_{t_{k+1}} = \mathrm{Exp}_+ * \mathrm{Exp}_-$) is not stated, except through the last sentence of the proof on p. 61. The blueprint should either cite that sentence (p. 61, not p. 60) or enter the $t_k = 0$ case as what the entry asserts.

## A20

### From `records/pyramids/VERBATIM-V-cone.md`, section "A20 -- Prop. 7.5(2): rational increments and the pyramid they interpolate"

**Cite:** fagerstrom2026cone -- Prop. 7.5, clause (2), printed p. 65 (statement and the whole proof on this one page; Figure 8, "the pyramid of Proposition 7.5(2)", is on p. 64). The "pp. 60-72" of the draft check should read p. 65.

**Source, verbatim (p. 65).**
> **Proposition 7.5** (rational increments and the pyramid they interpolate). 1. *If*
> $$ F(\omega) = \sum_{i=1}^N w_i\log\Big(1 + \frac{\omega^2}{\theta_i^2}\Big)$$
> *with positive integer weights $w_i$ and no Gaussian part, then every increment is rational,*
> $$ \hat\mu_{s,t} = \prod_i\Big(\frac{1 + s^2\omega^2/\theta_i^2}{1 + t^2\omega^2/\theta_i^2}\Big)^{w_i},$$
> *of order $2\sum_iw_i$, realized by $\sum_iw_i$ forward and $\sum_iw_i$ backward lag sections, each pole-zero pair at the common ratio $s/t$.*
>
> 2. *Let $R$ be a symmetric rational function that is the transform of an infinitely divisible law, with folded Lévy profile $k_R$. Then for each $q > 1$ there is exactly one function $F$ that is continuous with $F(0) = 0$ and satisfies $F(q\omega) - F(\omega) = -\log R(\omega)$, namely*
> $$ e^{-F(\omega)} = \prod_{m\ge1} R(q^{-m}\omega), \qquad\text{with folded profile}\qquad k(x) = \sum_{m\ge1} k_R(q^m x);$$
> *it is admissible exactly when this $k$ is nonincreasing, in particular whenever $k_R$ is. The Matérn pyramid is the case $R(\omega) = (1 + \omega^2)^{-1}$.*
>
> The index in the profile sum runs from $m = 1$. Write $F = \sum_{m\ge1}\psi(q^{-m}\,\cdot)$ with $\psi = -\log R$. The dilate $\psi(c\,\cdot)$ has profile $k_R(x/c)$, so the term with $c = q^{-m}$ contributes $k_R(q^m x)$. An $m = 0$ term would make the $q$-step increment $\psi(q\,\cdot)$ in place of $\psi$.
>
> *Proof.* (1) The increment transform telescopes by Proposition 7.1, and each factor $\big((1 + s^2\omega^2/\theta^2)/(1 + t^2\omega^2/\theta^2)\big)$ is realized as in Proposition 7.2 after the gauge change $t \mapsto t/\theta$; admissibility is Proposition 5.7 with $U = \sum_i 2w_i\delta_{\theta_i}$.
>
> (2) *Uniqueness.* If $F$ and $\tilde F$ both solve the equation and are continuous with value 0 at the origin, then $D := F - \tilde F$ satisfies $D(q\omega) = D(\omega)$, so $D(\omega) = D(q^{-m}\omega) \to D(0) = 0$ as $m \to \infty$; hence $D \equiv 0$. *Existence.* Write $\psi := -\log R$, which is a symmetric Lévy exponent. Near the origin $\psi(\omega) = O(\omega^2)$: $R$ is rational and even with $R(0) = 1$, so it is an analytic function of $\omega^2$ near the origin with value 1 there, and so is its logarithm, with value 0. Then $\sum_{m\ge1}\psi(q^{-m}\omega)$ converges, the terms being $O(q^{-2m}\omega^2)$, and its value $F$ satisfies $F(q\omega) - F(\omega) = \psi(\omega)$ by telescoping. *The pair of $\psi$.* It has no Gaussian coefficient: $R$ is rational, so $\psi$ grows like a multiple of $\log|\omega|$, while a positive Gaussian coefficient forces quadratic growth. Its Lévy measure is $k_R(x)\,dx/x$ with $k_R$ the folded profile named in the hypothesis, which is what the substitution below reads; the hypothesis asks for that profile, and for a rational $R$ with real poles it is a finite combination of exponentials. *The profile.* Substituting $u = cx$ in the representation shows that $\psi(c\,\cdot)$ has folded profile $k_R(u/c)$; taking $c = q^{-m}$ and summing over $m \ge 1$ gives $k(x) = \sum_{m\ge1}k_R(q^m x)$, the exchange of the sum with the integral being Tonelli, the summands being nonnegative. That $F$ is of the form (2.3) at the pair $(0,k)$ — that is, that $k$ satisfies the two integrability conditions of Lemma 2.3 — follows from the finiteness of $F(1)$, which the convergence of the series gives. *Admissibility* is Theorem 2.5 through clause (3) of Lemma 7.1 of [17], the representation (2.3) — and not the differentiability clause of that lemma, which is a different statement: $F$ is of that form with $k$ nonincreasing exactly when the family is admissible, and $k$ inherits monotonicity from $k_R$ when $k_R$ is nonincreasing, each summand being so. In the other direction, that admissibility *forces* $k$ to be nonincreasing is the uniqueness of the Lévy pair (Proposition 2.3 of [17](3)), and it fixes $k$ only up to a null set, so the monotonicity is monotonicity of a representative.

**Used as (the draft, lines 283, 293):** Remark 2.22 quotes clause (2) in full (line 293): "*let $R$ be a symmetric rational function that is the transform of an infinitely divisible law, with folded Lévy profile $k_R$; then for each $q > 1$ there is exactly one continuous $F$ with $F(0) = 0$ and $F(q\omega) - F(\omega) = -\log R(\omega)$, namely $e^{-F} = \prod_{m\ge1}R(q^{-m}\,\cdot)$, with folded profile $k(x) = \sum_{m\ge1}k_R(q^mx)$, and it is admissible exactly when that $k$ is nonincreasing, in particular whenever $k_R$ is; the Matérn pyramid is the case $R(\omega) = (1 + \omega^2)^{-1}$.*" Line 283 uses "the substitution of the proof of [Prop. 7.5(2)] read on an atomic measure", an analogy ($\psi(c\,\cdot)$ has folded profile $k_R(u/c)$).

**Word-for-word comparison (line 293 against p. 65).**
1. "Let $R$ ... $k_R$. Then" against "let $R$ ... $k_R$; then": capital and punctuation only.
2. "exactly one function $F$ that is continuous with $F(0) = 0$ and satisfies $F(q\omega) - F(\omega) = -\log R(\omega)$" against "exactly one continuous $F$ with $F(0) = 0$ and $F(q\omega) - F(\omega) = -\log R(\omega)$": same content, compressed.
3. "$e^{-F(\omega)} = \prod_{m\ge1}R(q^{-m}\omega)$" against "$e^{-F} = \prod_{m\ge1}R(q^{-m}\,\cdot)$": same (functions for values).
4. "with folded profile $k(x) = \sum_{m\ge1}k_R(q^mx)$; it is admissible exactly when this $k$ is nonincreasing, in particular whenever $k_R$ is. The Matérn pyramid is the case ..." against "..., and it is admissible exactly when that $k$ is nonincreasing, in particular whenever $k_R$ is; the Matérn pyramid is the case ...": "this" for "that", punctuation, an added "and". Same assertions.
5. Nothing in the quotation is stronger than the page. The sentence after it in the draft (Theorem 2.17 is its case $R = (1 + c^2\omega^2)^{-1}$ and could be written as a corollary of it) belongs to the draft, not to the page.

**Verdict: MATCH** (a faithful paraphrase of the printed statement, not a verbatim quotation: the italic quotation of Remark 2.22 should not be presented as verbatim, or should be brought to the words above). The page proof also uses a restriction that the statement does not print, "for a rational $R$ with real poles it is a finite combination of exponentials"; the ledger entry should carry the statement as printed.

## A22

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "A22 -- Prop. 4.5(1), Pólya frequency members of the similarity family"

**Cite:** fagerstrom2026selection -- Prop. 4.5(1), printed p. 35 (statement, the whole clause; cat. A32)

**Source, verbatim (p. 35).**
> **Proposition 4.5** (non-creation from the signal; the Pólya frequency members). *Write $S^-(g)$ for the number of sign changes of $g$ on $\mathbb{R}$, in the essential sense.*
>
> 1. *An admissible family has Pólya frequency kernels, so that convolution with $\mu_{0,t}$ is variation-diminishing, $S^-(\mu_{0,t} * g) \le S^-(g)$ for every $t>0$ and every integrable or bounded $g$, if and only if*
> $$F(\omega) = a\,\omega^2 + \sum_i \log\Big(1+\frac{\omega^2}{\theta_i^2}\Big), \qquad \theta_i>0,\quad \sum_i \theta_i^{-2}<\infty :$$
> *Gaussian jitter, the term $a\,\omega^2$, together with integer-weighted symmetric Thorin atoms, the summability being finiteness of the variance $2a+2\sum_i\theta_i^{-2}$. Equivalently the kernels are Gaussians convolved with countably many Laplace kernels, the convolution read at the transform,*
> $$e^{-F(\omega)} = e^{-a\omega^2}\prod_i\Big(1+\frac{\omega^2}{\theta_i^2}\Big)^{-1},$$
> *where the product converges at every $\omega$, and unconditionally, because $\sum_i\theta_i^{-2}<\infty$. The Gaussian family and the Matérn families of integer $\gamma$ are members; the Matérn families of non-integer $\gamma$, the non-Gaussian stable families and the Cin rays are not.*

(The statement does not restate $a\ge0$; "admissible" carries it. The Gaussian coefficient is $a$,
not $\tfrac12 a$, in this paper's line convention.)

**Used as (the draft, lines 229, 235, 243, 247):** the sufficiency half only: $a\ge0$ (or $a=0$) and
$\theta_i>0$, $\sum\theta_i^{-2}<\infty$ give a similarity family with Pólya frequency kernels (so
$S^-(\mu_{0,t}*g)\le S^-(g)$ for integrable or bounded $g$); line 247 first checks admissibility of
$G$ and then applies the clause to the family of $G$, whose kernel at scale $t$ is $\Phi_{t,qt}$.

**Verdict: NARROWER-OK.** The draft uses "if" only; the page gives "if and only if". Page 35 is
correct. The hypothesis "admissible family" must be kept in the blueprint node; the draft supplies
it at line 247.

## A23

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "A23 -- Prop. 4.5(2), the counting clause"

**Cite:** fagerstrom2026selection -- Prop. 4.5(2), printed p. 35 (statement); its derivation from clause (1) is on p. 39, the first lines (cat. A33)

**Source, verbatim (p. 35, statement).**
> 2. *For such a family and $f$ the primitive of an integrable $f'$, the scale space has, at every scale, no more zero crossings than the signal at every level, $S^-(u(t,\cdot)-c)\le S^-(f-c)$, and no more changes of monotonicity, $S^-(\partial_x u(t,\cdot))\le S^-(f')$.*

and the sentence after it:
> The counting clauses of (2) follow from the variation-diminishing property alone, so the whole content is clause (1).

**Source, verbatim (p. 39, the derivation).**
> Clause (2) follows from the variation-diminishing property of clause (1) applied to $f-c$, which is bounded because the primitive of an integrable function is, and to $f'$, using $\partial_x u(t,\cdot)=\mu_{0,t}*f'$.

**Used as (the draft, line 247):** "apply the variation-diminishing property to the record minus a
constant, which is bounded, and to its derivative, which is integrable", to the increment
$\Phi_{t,qt}$; and the statement of Remark 2.17' (line 243).

**Verdict: MATCH.** The draft re-runs the page's own derivation (bounded $f-c$, integrable $f'$).
"The record" in the draft's proof must mean the signal $f$ at the rung (the primitive of an
integrable $f'$), as at line 243; if it meant $u(t,\cdot)$ the sentence would need the same
hypotheses on $u$, which the page does not state. The page for the derivation is p. 39, not p. 35.

## A24

Two records: Karlin's pages read directly (`VERBATIM-literature.md`), and the same fact as V-selection v0.1 prints it in its section 4.3 (`VERBATIM-selection-iso-affine.md`).

### From `records/pyramids/VERBATIM-literature.md`, section "A24 -- Reciprocal of the Laplace transform of a Polya frequency density (Karlin)"

**Cite:** karlin1968total -- Ch. 7, Thm. 3.2(a), printed p. 345 (text continues on p. 346), with Prop. 1.4, printed p. 333; the class
script-E_2^* is defined on p. 336, (2.2).

**Source, verbatim (p. 345, Thm. 3.2(a)).**
> THEOREM 3.2. (a) A necessary and sufficient condition that a density function $f(u)$ ($-\infty < u < \infty$) be PF is that the reciprocal of its Laplace transform be an entire function of class $\mathscr{E}_2^*$ with $\gamma + \sum_{i=1}^\infty a_i^2 > 0$.

Just before it, on the same page:
> THEOREM 3.1. Let $f(u)$ be a PF density function on $-\infty < u < \infty$. Let $\phi(s)$ denote the Laplace transform of $f$ and $\psi(s) = \frac{1}{\phi(s)} = \sum_{m=0}^\infty \frac{c_m}{m!}s^m$, $c_0 = 1$, which converges for $|s| < A$ (some $A > 0$). Then [(3.14) $A_n^*(s) = \sum_{m=0}^n \binom{n}{m} c_m s^m$ has only real zeros; ...] Moreover, $A_n^*(s/n)$ converges uniformly to $\psi(s)$ for $|s| \le A_0$ ($0 < A_0 < A$).

**Source, verbatim (p. 336, (2.2) and the sentences after it).**
> The class $\mathscr{E}_2$ of entire functions of the form
> $$\psi(s) = e^{-\gamma s^2 + \delta s}s^k\prod_{i=1}^\infty (1 + a_i s)e^{-a_i s} \qquad (2.2)$$
> where $\gamma \ge 0$, $\delta$ is real, $k$ is a nonnegative integer, the $a_i$ are real, and $\sum_{i=1}^\infty a_i^2 < \infty$, is fundamental in the theory of general PF functions on the line. We define $\mathscr{E}_2^*$ as the subclass of $\mathscr{E}_2$ for which $\psi(0) = 1$. ... Also, $\phi(s) = 1/\psi(s)$ for $\psi(s) \in \mathscr{E}_2^*$ is the Laplace transform of a PF density, provided $\gamma + \sum a_i^2 > 0$.

($\psi(0) = 1$ forces $k = 0$ in (2.2).)

**Source, verbatim (p. 333, Prop. 1.4).**
> PROPOSITION 1.4. If $f$ is a PF$_2$ density, then its Laplace transform exists in an open strip containing the imaginary axis.

p. 346 adds: "The condition $\gamma + \sum_{i=1}^\infty a_i^2 > 0$ in (a) is essential in order that $f$ be a bona fide density function".

**Used as (the draft, line 235; the same fact behind line 255):** For a Polya frequency density $\phi$, the two-sided Laplace transform
$L(p) = \int e^{-px}\phi(x)\,dx$ is analytic on an open strip containing the imaginary axis, and there $1/L = e^{-\gamma p^2 + \delta p}\prod_j (1 + a_jp)e^{-a_jp}$, $\sum a_j^2 < \infty$.

**Verdict: MATCH** (pages 345 and 333 correct). The product is exactly (2.2) with $k = 0$; $\gamma \ge 0$, $\delta$ real, $a_j$ real (the draft
does not print these ranges, harmless for its use). "Analytic on the strip" combines two things: Prop. 1.4 gives existence of the transform on
an open strip containing the imaginary axis, and its analyticity there (interior of the strip of convergence) is the standard fact, not
printed on the page; "there $1/L$ equals the entire function" is Thm. 3.2(a) read as the analytic continuation of $1/\phi$, which Thm. 3.1
sets up near 0. Prop. 1.4 is stated for PF$_2$ densities, the theorem for PF densities (all orders); the draft’s "Polya frequency density"
is the theorem’s hypothesis. The class definition is on p. 336, not 345: if the blueprint states the class, cite (2.2), p. 336, as well.

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "A24 -- Schoenberg's representation as printed in § 4.3 (Karlin 1968, Ch. 7, Thm. 3.2(a) and Prop. 1.4)"

**Cite:** fagerstrom2026selection -- § 4.3 (heading on p. 34), the cited fact printed at the foot of p. 34 and the head of p. 35, restated with the strip on p. 36 (cat. A34, A75)

**Source, verbatim (p. 34, the foot; the sentence runs over the page).**
> *The cited facts.* Variation diminution of convolution by a kernel and total positivity of the kernel are equivalent. The direction from total positivity is [20], Ch. 5, Thm. 3.1(i), p. 233, and the converse is Thm. 4.2, pp. 242-243, where it is stated for a density. Schoenberg's representation is the second fact ([33], (4'), p. 165; [34], Theorem I, pp. 333-334), read here at Karlin's letter. A density $\phi$ is a Pólya frequency density if and only if the reciprocal of its

**(p. 35, the head).**
> two-sided Laplace transform is $e^{-\gamma s^2+\delta s}\prod_j(1+a_j s)\,e^{-a_j s}$, with $\gamma\ge0$, real $a_j$ and $\sum_j a_j^2<\infty$ (Ch. 7, Thm. 3.2(a), p. 345, with Remark 3.1, p. 346). The identity holds at complex $s$ on an open strip containing the imaginary axis (Ch. 7 §1, Prop. 1.4, p. 333). The converse half is the sentence after (2.2) on p. 336: for such a product $\psi$ with $\psi(0)=1$ and $\gamma+\sum_j a_j^2>0$, the reciprocal $1/\psi$ is the Laplace transform of a Pólya frequency density.

**(p. 36, "The two cited facts", the representation in the form used).**
> for a Pólya frequency density $\phi$ there are $\gamma\ge0$, $\delta\in\mathbb{R}$ and real $a_j$ with $\sum_j a_j^2<\infty$ and $\gamma+\sum_j a_j^2>0$, and an open strip $\alpha<\mathrm{Re}\,s<\beta$ with $\alpha<0<\beta$, on which $L$ converges absolutely and
> $$L(s)\,\psi(s)=1,\qquad \psi(s)=e^{-\gamma s^2+\delta s}\prod_j(1+a_j s)\,e^{-a_j s}.$$
> The strip is Karlin's Proposition 1.4.

with $L(s):=\int_{\mathbb{R}}e^{-sx}\phi(x)\,dx$ (p. 35, foot) and "Laplace transform in Karlin's sign" (p. 36, top).

**Used as (the draft, line 235):** for a Pólya frequency density $\phi$, $L(p)=\int e^{-px}\phi(x)\,dx$ is
analytic on an open strip containing the imaginary axis and there $1/L=e^{-\gamma p^2+\delta p}\prod_j(1+a_jp)e^{-a_jp}$, $\sum a_j^2<\infty$; cited as Karlin Ch. 7 Thm. 3.2(a), p. 345, with Prop. 1.4, p. 333.

**Verdict: NARROWER-OK.** The draft's anchors (Thm. 3.2(a) p. 345, Prop. 1.4 p. 333) are exactly
as § 4.3 prints them, and the sign convention ($e^{-px}$) is Karlin's. What the draft leaves out and
the page states: $\gamma\ge0$, real $a_j$, and the normalisation $\gamma+\sum a_j^2>0$ (which
excludes the point mass); the page also cites Remark 3.1, p. 346, with Thm. 3.2(a), and the
earlier Schoenberg sources [33] p. 165 and [34] Thm. I pp. 333-334. "Analytic" is the draft's word;
the page says "converges absolutely" on the strip (analyticity there is standard). The draft's
argument at line 237 needs only the identity $L\psi=1$ on the strip, so it is within the page.
Printed pages: pp. 34-35 for the statement, p. 36 for the strip and absolute convergence.

## A30

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "A30 -- Lem. 3.3(1)-(2), operators and kernels"

**Cite:** fagerstrom2026isotropic -- Lemma 3.3(1)-(2), printed p. 11 ((3)-(4) are on p. 12) (cat. A42)

**Source, verbatim (p. 11).**
> **Lemma 3.3** (operators and kernels in dimension $d$). *Fix $d\ge1$, and for a probability measure $\mu$ on $\mathbb{R}^d$ and $f\in L^1(\mathbb{R}^d)$ write $(\mu*f)(x):=\int f(x-y)\,\mu(dy)$.*
>
> 1. *(One operator.) Let $\Phi$ be a linear operator on $L^1(\mathbb{R}^d)$ with the four axioms of Definition 3.1 that concern one operator: (A1) $\Phi$ is bounded; (A2) $\Phi T_a=T_a\Phi$ for every $a\in\mathbb{R}^d$; (A4) $\Phi f\ge0$ whenever $f\ge0$; (A5) $\int\Phi f=\int f$ whenever $f\ge0$. Then there is a unique probability measure $\mu$ on $\mathbb{R}^d$ with*
> $$\Phi f=\mu*f,\qquad f\in L^1(\mathbb{R}^d).$$
> *Conversely, for every probability measure $\mu$ on $\mathbb{R}^d$ the operator $f\mapsto\mu*f$ satisfies (A1), (A2), (A4) and (A5).*
>
> 2. *(Continuity.) Let $\mu_n$ and $\mu$ be probability measures on $\mathbb{R}^d$. Then $\hat\mu_n(\xi)\to\hat\mu(\xi)$ for every $\xi\in\mathbb{R}^d$ if and only if $\mu_n*f\to\mu*f$ in $L^1(\mathbb{R}^d)$ for every $f\in L^1(\mathbb{R}^d)$.*

(With the surrounding sentence, p. 11: "The point that needs an argument is its clause (2), that the two continuities are the same: (A7) requires convergence in $L^1(\mathbb{R}^d)$, and (I2) convergence of the transforms at each frequency. The proof is in the supplement (§S3.1).")

**Used as (the draft, lines 77, 446, 856):** an operator with (A1), (A2), (A4), (A5) is convolution with a unique probability measure; convergence of the transforms at each frequency is convergence of the operators on $L^1$.

**Verdict: MATCH.** Dimension $d\ge1$ as stated. "Convergence of the operators on $L^1$" is read strongly (for every $f$), as on the page.

## A31

The class A_d that the theorem quantifies over is iso Prop. 2.6, p. 8, also copied.

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "A31 -- Thm. 3.6, the isotropic classification in dimension $d$"

**Cite:** fagerstrom2026isotropic -- Theorem 3.6, printed p. 13 (cat. A44)

**Source, verbatim (p. 13).**
> **Theorem 3.6** (the isotropic classification in dimension $d$). *Let $d\ge1$. A family $(\mu_{s,t})_{0\le s\le t}$ of probability measures on $\mathbb{R}^d$ is an isotropic cascade family in dimension $d$ if and only if there are a gauge $\chi$ and an $F\in\mathcal{A}_d$ with $F\not\equiv0$ such that*
> $$\hat\mu_{s,t}(\xi)=\exp\Big[-\big(F(\chi(t)|\xi|)-F(\chi(s)|\xi|)\big)\Big],\qquad0\le s\le t,\ \xi\in\mathbb{R}^d.\tag{3.1}$$
> *In particular the kernels from scale zero are $\hat\mu_{0,t}(\xi)=e^{-F(\chi(t)|\xi|)}$. The pair is unique up to $(\chi,F)\mapsto(c\chi,F(c^{-1}\cdot))$ with $c>0$, in the sense that if a gauge $\chi'$ and a real function $F'$ on $[0,\infty)$ with $F'(0)=0$ also satisfy (3.1), then $\chi'=c\chi$ and $F'=F(c^{-1}\cdot)$ for some $c>0$, and $c=1$ when $\chi(1)=\chi'(1)=1$.*

(The page's lead-in: "A gauge, self-decomposability (2.2) and the admissible exponents (2.1) are as in §2.2"; $\mathcal{A}_d$ is the class of Prop. 2.6, p. 8.)

**Used as (the draft, lines 79, 424, 428, 555):** Theorem 2.0': the same statement with the draft's symbols, "unique up to ... so unique once $\chi(1)=1$"; used for the classification of fully covariant families and for $\Psi_t=F(\chi(t)|\cdot|)$.

**Verdict: NARROWER-OK.** The draft states the same iff and drops "In particular the kernels from scale zero ..." and the wider form of the uniqueness (any real $F'$ with $F'(0)=0$); it uses less. The blueprint must define "gauge" and $\mathcal{A}_d$ as the iso paper does (§2.2, Prop. 2.6); this page does not restate them. Page 13 is right.

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "Prop. 2.6 (iso, no id) -- the dimension filtration"

**Cite:** fagerstrom2026isotropic -- Prop. 2.6, printed p. 8, clauses (1)-(3) (cat. A43)

**Source, verbatim (p. 8).**
> **Proposition 2.6** (the dimension filtration, [16, Prop. 4.9(1), (2) and (4)]). *For an integer $d\ge1$ let $\mathcal{A}_d$ be the set of admissible $F$ for which $\xi\mapsto F(|\xi|)$, $\xi\in\mathbb{R}^d$, is the exponent of a self-decomposable law on $\mathbb{R}^d$, and let $\mathcal{A}_\infty$ be the intersection of all the $\mathcal{A}_d$.*
> 1. *$\mathcal{A}_1$ is the whole admissible cone, and $\mathcal{A}_{d+1}\subseteq\mathcal{A}_d$ for every $d\ge1$.*
> 2. *$\mathcal{S}\subseteq\mathcal{A}_d$ for every $d\ge1$.*
> 3. *$\mathcal{A}_\infty=\mathcal{S}$.*
>
> So $\mathcal{S}=\mathcal{A}_\infty\subseteq\cdots\subseteq\mathcal{A}_2\subseteq\mathcal{A}_1$.

(The page before it: "The admissible exponents form a convex cone"; $\mathcal{S}$ is the subordinated slice, the set of $F_{\mathrm I}(\cdot^2/2)$.)

**Used as (the draft, lines 77, 459):** "$\mathcal{A}_1$ is the whole cone and $\mathcal{A}_{d+1}\subseteq\mathcal{A}_d$"; no proof of the draft uses it.

**Verdict: MATCH.** It is a restatement of the cone paper, [16] Prop. 4.9(1), (2), (4); cite at p. 8.

## A34

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "A34 -- Lem. 3.8, every pair is realised"

**Cite:** fagerstrom2026isotropic -- Lemma 3.8, printed p. 14 (cat. A48)

**Source, verbatim (p. 14).**
> **Lemma 3.8** (every pair is realised). *Let $d\ge1$, let $\chi$ be a gauge, and let $F\in\mathcal{A}_d$ with $F\not\equiv0$. Then there is an isotropic cascade family $(\mu_{s,t})_{0\le s\le t}$ in dimension $d$ that satisfies (3.1) with the pair $(\chi,F)$.*

**Used as (the draft, lines 81, 500, 553):** every pair $(\chi,F)$ with $F\in\mathcal{A}_d$, $F\not\equiv0$ is realised by an isotropic family; lines 500, 553 take $\chi=\mathrm{id}$.

**Verdict: MATCH.** Page right.

## A35

### From `records/pyramids/VERBATIM-selection-iso-affine.md`, section "A35 -- Prop. 3.11(1)-(2), the polar form of $\mathcal{A}_d$"

**Cite:** fagerstrom2026isotropic -- Prop. 3.11(1) on printed p. 15, (2) on **p. 16**; the draft and brief put both on p. 15 (cat. A50)

**Source, verbatim (p. 15, foot).**
> **Proposition 3.11** (the polar form of $\mathcal{A}_d$). *Let $d\ge1$ and $F:[0,\infty)\to[0,\infty)$.*
>
> 1. *(The reading.) $\xi\mapsto F(|\xi|)$ is the exponent of a self-decomposable law on $\mathbb{R}^d$ if and only if it is the exponent $F_d$ of an isotropic origin datum $(a,k_d)$ in dimension $d$ (Definition 3.10):*
> $$F(|\xi|)=\tfrac12a|\xi|^2+\int_{\mathbb{R}^d}\big(1-\cos\langle\xi,x\rangle\big)\frac{k_d(|x|)}{|S^{d-1}|\,|x|^d}\,dx,\qquad\xi\in\mathbb{R}^d.$$
> *The datum is then unique, $k_d$ up to modification on a Lebesgue-null set.*

**(p. 16, head).**
> 2. *(The class.) If this holds, $F$ is admissible, of the form (2.1) with $a_{\mathrm V}=\tfrac12a'$ and $k=k_1$ for its datum $(a',k_1)$ in dimension 1. So $\mathcal{A}_d$ is the set of $F$ for which $F(|\cdot|)$ is the exponent of an isotropic origin datum in dimension $d$.*

**Used as (the draft, lines 418, 428, 500, 553):** $\mathcal{A}_d$ is the set of exponents of isotropic origin data $(a,k_d)$; line 500 uses (1) with the uniqueness of the datum; line 553 uses (1) to put $F_q$ in $\mathcal{A}_d$.

**Verdict: MATCH, with a page correction** ((1) p. 15, (2) p. 16). One precision: the draft defines $\mathcal{A}_d$ for $F:[0,\infty)\to[0,\infty)$ without "admissible"; Prop. 2.6 (p. 8) defines it among admissible $F$, and (2) shows the two agree, so the draft's version is equivalent by (1) and (2) together. Cite both clauses where "$\mathcal{A}_d$ is inside the admissible cone" is needed.

## A39

### From `records/pyramids/VERBATIM-Sato.md`, section "A39 -- The Levy-Khintchine representation: existence, uniqueness, every triplet occurs"

**Cite:** sato1999levy -- Theorem 8.1 (i)-(iii), printed pp. 37-38 ((i) with (8.1), (8.2) at the foot of p. 37; (ii), (iii) at the head of p. 38).

**Source, verbatim (p. 37, foot, and p. 38, head).**
> THEOREM 8.1. (i) *If $\mu$ is an infinitely divisible distribution on $\mathbb{R}^d$, then*
>
> (8.1) $\quad \hat\mu(z) = \exp\Big[-\tfrac12\langle z, Az\rangle + \mathrm{i}\langle \gamma, z\rangle + \int_{\mathbb{R}^d}\big(\mathrm{e}^{\mathrm{i}\langle z,x\rangle} - 1 - \mathrm{i}\langle z,x\rangle 1_D(x)\big)\,\nu(\mathrm{d}x)\Big],\quad z \in \mathbb{R}^d,$
>
> *where $A$ is a symmetric nonnegative-definite $d \times d$ matrix, $\nu$ is a measure on $\mathbb{R}^d$ satisfying*
>
> (8.2) $\quad \nu(\{0\}) = 0 \quad\text{and}\quad \int_{\mathbb{R}^d}(|x|^2 \wedge 1)\,\nu(\mathrm{d}x) < \infty,$
>
> *and $\gamma \in \mathbb{R}^d$.* (p. 38:) (ii) *The representation of $\hat\mu(z)$ in (i) by $A$, $\nu$, and $\gamma$ is unique.* (iii) *Conversely, if $A$ is a symmetric nonnegative-definite $d \times d$ matrix, $\nu$ is a measure satisfying (8.2), and $\gamma \in \mathbb{R}^d$, then there exists an infinitely divisible distribution $\mu$ whose characteristic function is given by (8.1).*

Context: "Let $D = \{x : |x| \le 1\}$, the closed unit ball" (p. 37, preceding sentence). Definition 8.2 (p. 38): $(A,\nu,\gamma)$ is the *generating triplet*; $A$ the Gaussian covariance matrix, $\nu$ the Levy measure. Corollary 8.3 (p. 38): $\mu^t$ has triplet $(tA, t\nu, t\gamma)$.

**Used as (the draft, lines 255, 376, 378, 416, 428, 490, 794, 796, 798):** uniqueness of the triplet (the Levy measure is unique; data additive under convolution; invariance under $O(d)$; matching data after a linear image) and existence (every difference of data is the triplet of a symmetric / rotation-invariant infinitely divisible law).

**Verdict: MATCH, with a page correction and two notes.**
1. **Page.** Uniqueness is (ii), on **p. 38**. Draft lines 490, 794, 796, 798 print "Thm. 8.1, p. 37" for uniqueness: correct to "Thm. 8.1(ii), p. 38" (or "pp. 37-38"). Existence "(iii), p. 38" at 416 and 428 is right.
2. **Normalization.** Sato's $A$ is the covariance matrix (exponent $-\frac12\langle z,Az\rangle$); the draft's Gaussian datum is half of it (line 376 says so). The factor is linear, so uniqueness and additivity transfer unchanged. "Triplets add under convolution" (796) is (ii) together with the product of transforms, not a printed clause.
3. **Symmetric reductions.** The draft writes the exponent of a symmetric law as $\int(1 - \cos\langle\omega,x\rangle)\nu(dx)$ (794) and calls the law of (iii) "symmetric" (416) or "rotation invariant" (428). Neither is on the page. The first is (8.1) with $\gamma = 0$ and $\nu$ symmetric: the compensator part of the integrand is odd and absolutely integrable, so contributes $0$. The second: the transform given by (8.1) is real (resp. radial) and a transform determines the law, so the law is symmetric (resp. rotation invariant). Both are one-line steps the blueprint should state, not part of the axiom.

## A40

### From `records/pyramids/VERBATIM-Sato.md`, section "A40 -- An infinitely divisible law has a transform without zeros"

**Cite:** sato1999levy -- Lemma 7.5, printed p. 32 (statement near the foot of the page; the proof continues on p. 33).

**Source, verbatim (p. 32).**
> LEMMA 7.5. *If $\mu$ is infinitely divisible, then $\hat\mu(z)$ has no zero, that is, $\hat\mu(z) \neq 0$ for any $z \in \mathbb{R}^d$.*

Context: "Now we will show in several lemmas that, for any infinitely divisible distribution $\mu$, the $n$th root is uniquely defined and further, for any $t \ge 0$, the $t$th power of $\mu$ is definable" (preceding sentence).

**Used as (the draft, lines 378, 794):** a symmetric infinitely divisible law has a real transform without zeros, positive by continuity from $\hat\mu(0) = 1$.

**Verdict: NARROWER-OK.** The draft uses the "no zero" part, on $\mathbb{R}^d$ as it needs. "Real" is the symmetry of $\mu$ and "positive" is continuity plus no zero; neither is in the lemma. At line 378 the bracket "[Sato, Lemma 7.5, p. 32]" closes the whole sentence "real transform without zeros"; the blueprint axiom should say only "no zero".

## A41

### From `records/pyramids/VERBATIM-Sato.md`, section "A41 -- Khintchine: limits of null-array row sums are infinitely divisible"

**Cite:** sato1999levy -- Theorem 9.3 (Khintchine), printed p. 47 (statement at the foot of the page, with Definition 9.2 and (9.1) above it).

**Source, verbatim (p. 47).**
> DEFINITION 9.2. A double sequence of random variables $\{Z_{nk} : k = 1, 2, \ldots, r_n;\ n = 1, 2, \ldots\}$ on $\mathbb{R}^d$ is called a *null array* if, for each fixed $n$, $Z_{n1}, Z_{n2}, \ldots, Z_{nr_n}$ are independent and if, for any $\varepsilon > 0$,
>
> (9.1) $\quad \lim_{n\to\infty}\max_{1 \le k \le r_n} P[\,|Z_{nk}| > \varepsilon\,] = 0.$
>
> The sums $S_n = \sum_{k=1}^{r_n} Z_{nk}$, $n = 1, 2, \ldots$, are called the *row sums*.
>
> THEOREM 9.3 (Khintchine [254]). *Let $\{Z_{nk}\}$ be a null array on $\mathbb{R}^d$ with row sums $S_n$. If, for some $b_n \in \mathbb{R}^d$, $n = 1, 2, \ldots$, the distribution of $S_n - b_n$ converges to a distribution $\mu$, then $\mu$ is infinitely divisible.*

**Used as (the draft, lines 378, 788):** the factors of $\mu_{s,t}$ over partitions of $[s,t]$ of vanishing mesh form a null array whose row sums all have law $\mu_{s,t}$, so $\mu_{s,t}$ is infinitely divisible.

**Verdict: NARROWER-OK.** The draft takes $b_n = 0$ and a constant sequence of row-sum laws (trivially convergent), on $\mathbb{R}^d$ as Sato states it. The null property (9.1) is what the draft supplies from (I2); "independent in each row" is a choice of realization of the given factor laws.

## A42

### From `records/pyramids/VERBATIM-Sato.md`, section "A42 -- The linear image of a Levy process (infinitely divisible law)"

**Cite:** sato1999levy -- Proposition 11.10, printed p. 65 (statement with (11.8)-(11.10); the proof begins below it on the same page).

**Source, verbatim (p. 65).**
> PROPOSITION 11.10. *Let $\{X_t\}$ be a Levy process on $\mathbb{R}^d$ with generating triplet $(A,\nu,\gamma)$ and let $U$ be an $n \times d$ matrix. Then $\{UX_t\}$ is a Levy process on $\mathbb{R}^n$ with generating triplet $(A_U, \nu_U, \gamma_U)$ given by*
>
> (11.8) $\quad A_U = UAU^\top,$
>
> (11.9) $\quad \nu_U = [\nu U^{-1}]_{\mathbb{R}^n\setminus\{0\}},$
>
> (11.10) $\quad \gamma_U = U\gamma + \int Ux\,(1_E(Ux) - 1_D(x))\,\nu(\mathrm{d}x),$
>
> *where $(\nu U^{-1})(B) = \nu(\{x : Ux \in B\})$, $D = \{x \in \mathbb{R}^d : |x| \le 1\}$, $E = \{y \in \mathbb{R}^n : |y| \le 1\}$ and $[\nu U^{-1}]_{\mathbb{R}^n\setminus\{0\}}$ is the restriction of the measure $\nu U^{-1}$ to $\mathbb{R}^n \setminus \{0\}$.*

(In (11.8) the book prints $U$ with a prime for the transpose; written $U^\top$ here.) Context: "As a special case, projections of Levy processes are again Levy processes" (next sentence). Above: "The correspondence of a Levy process $\{X_t\}$ and an infinitely divisible distribution $\mu$ through $P_{X_1} = \mu$ has been established. The generating triplet $(A,\nu,\gamma)$ of $\mu$ is called the generating triplet of the Levy process."

**Used as (the draft, lines 410, 457, 467, 774, 796, 798):** the image of an infinitely divisible law under $x \mapsto qx$, an invertible $G^{-1}$, a coordinate map, or an orthogonal projection has Gaussian part $UAU^\top$ and Levy measure the image of $\nu$ off $0$.

**Verdict: NARROWER-OK.** The page is for a Levy process; applied to the one with $P_{X_1} = \mu$ it gives the law's triplet (the p. 65 sentence above). The draft's matrices ($qI$, $G^{-1}$, a coordinate row, a projection) are all $n \times d$ matrices. The $\gamma_U$ clause is not used. The blueprint axiom should be stated for the law, citing the process form and the same-page sentence.

## A43

### From `records/pyramids/VERBATIM-Sato.md`, section "A43 -- A semi-selfdecomposable law is infinitely divisible, and its residual is unique"

**Cite:** sato1999levy -- Proposition 15.5, printed p. 93 (statement just below the middle of the page; proof below it).

**Source, verbatim (p. 93).**
> PROPOSITION 15.5. *If $\mu$ is selfdecomposable, then $\mu$ is infinitely divisible and, for any $b > 1$, $\rho_b$ in (15.1) is uniquely determined and infinitely divisible. If $\mu$ is semi-selfdecomposable, then $\mu$ is infinitely divisible and $\rho_b$ is uniquely determined.*

Proof, as printed: "Let $\mu$ be selfdecomposable. Then Theorem 9.3 and the proof of Theorem 15.3 show the infinite divisibility of $\mu$ and $\rho_b$. The uniqueness of $\rho_b$ comes from the fact that $\hat\mu(z)$ has no zero by Lemma 7.5. Let $\mu$ be semi-selfdecomposable with span $b$. ... for any $n$, there is an infinitely divisible distribution $\rho_{b^n}$ such that $\hat\mu(z) = \hat\mu(b^{-n}z)\hat\rho_{b^n}(z)$. Since $\hat\mu(b^{-n}z) \to 1$ as $n \to \infty$, $\hat\rho_{b^n}(z) \to \hat\mu(z)$ for any $z$. Hence $\mu$ is infinitely divisible by Lemma 7.8. Hence $\hat\mu(z)$ has no zero and $\rho_b$ is unique." Next paragraph: "It follows from the proposition above that, for any $b > 1$, any selfdecomposable distribution is semi-selfdecomposable with $b$ as a span."

**Used as (the draft, lines 134, 402, 457):** a semi-selfdecomposable law is infinitely divisible with a unique residual; a self-decomposable law has infinitely divisible residuals and is semi-selfdecomposable for every span.

**Verdict: MATCH.** Both halves, and the closing sentence about every span, are on p. 93.

## A44

### From `records/pyramids/VERBATIM-Sato.md`, section "A44 -- Semi-selfdecomposable with span $b$ iff $T_b\nu \ge \nu$"

**Cite:** sato1999levy -- Theorem 15.8, printed p. 94 (statement in the middle of the page; $T_r$ is defined at (13.8), p. 75).

**Source, verbatim (p. 94).**
> THEOREM 15.8. *Fix $b > 1$. Let $\mu$ be an infinitely divisible distribution on $\mathbb{R}^d$ with generating triplet $(A,\nu,\gamma)$. Then $\mu$ is semi-selfdecomposable with $b$ as a span if and only if*
>
> (15.6) $\quad T_b\nu \ge \nu.$
>
> *In other words, $\mu$ is semi-selfdecomposable with $b$ as a span if and only if, for any $n \in \mathbb{Z}$,*
>
> (15.7) $\quad T_b([\nu]_{S_n(b)}) \ge [\nu]_{S_{n+1}(b)}.$
>
> Semi-selfdecomposability does not impose any restriction on $A$ and $\gamma$.

Definitions used (p. 75, (13.8), and p. 76, (13.10)): "We define, for any $r > 0$, a transformation $T_r$ of measures $\rho$ on $\mathbb{R}^d$ by $(T_r\rho)(B) = \rho(r^{-1}B)$ for $B \in \mathcal{B}(\mathbb{R}^d)$"; $S_n(b) = \{x : b^n < |x| \le b^{n+1}\}$. The proof (pp. 94-95) uses Prop. 11.10 for the triplet of $\hat\mu(b^{-1}z)$ and "$A - A^{(b)}$ is nonnegative-definite, since $b > 1$".

**Used as (the draft, lines 134, 402, 457):** an infinitely divisible law with Levy measure $\nu$ is semi-selfdecomposable with span $q$ iff $T_q\nu \ge \nu$ ($T_q$ the pushforward under $x \mapsto qx$), with no condition on the Gaussian part; written $D_q\nu \ge \nu$ at 402.

**Verdict: MATCH.** The pushforward reading of $T_q$ is exactly (13.8), and "no restriction on $A$ and $\gamma$" is on the page.

## A45

### From `records/pyramids/VERBATIM-Sato.md`, section "A45 -- The polar density form of a self-decomposable law's Levy measure (Thm. 15.10), and the line case (Cor. 15.11)"

**Cite:** sato1999levy -- Theorem 15.10 and Corollary 15.11, both printed p. 95 (statements in the middle of the page; the proof of 15.10 begins at the foot of p. 95 and runs onto p. 96).

**Source, verbatim (p. 95).**
> Let $S = \{\xi \in \mathbb{R}^d : |\xi| = 1\}$, the unit sphere.
>
> THEOREM 15.10. *Let $\mu$ be an infinitely divisible distribution on $\mathbb{R}^d$ with generating triplet $(A,\nu,\gamma)$. Then, $\mu$ is selfdecomposable if and only if*
>
> (15.8) $\quad \nu(B) = \int_S \lambda(\mathrm{d}\xi)\int_0^\infty 1_B(r\xi)\,k_\xi(r)\,\frac{\mathrm{d}r}{r}$
>
> *with a finite measure $\lambda$ on $S$ and a nonnegative function $k_\xi(r)$ measurable in $\xi \in S$ and decreasing in $r > 0$.*
>
> Selfdecomposability imposes no restriction on $A$ and $\gamma$.
>
> COROLLARY 15.11. *A probability measure $\mu$ on $\mathbb{R}$ is selfdecomposable if and only if*
>
> (15.9) $\quad \hat\mu(z) = \exp\Big[-\tfrac12 Az^2 + \mathrm{i}\gamma z + \int_{-\infty}^{\infty}\big(\mathrm{e}^{\mathrm{i}zx} - 1 - \mathrm{i}zx\,1_{[-1,1]}(x)\big)\frac{k(x)}{|x|}\,\mathrm{d}x\Big],$
>
> *where $A \ge 0$, $\gamma \in \mathbb{R}$, $k(x) \ge 0$, $\int_{-\infty}^{\infty}(|x|^2 \wedge 1)\frac{k(x)}{|x|}\,\mathrm{d}x < \infty$, and $k(x)$ is increasing on $(-\infty, 0)$ and decreasing on $(0, \infty)$.*

Proof of 15.10 begins: "Let $\mu$ be selfdecomposable. Then, for any $b > 1$, it is semi-selfdecomposable with span $b$. Hence (15.6) for every $b > 1$." (p. 95), continuing on p. 96 to "Then we get (15.8) for $B = (r,\infty)C$."

**Used as (the draft, lines 152, 158, 436, 500):** (a) a self-decomposable law's Levy measure has the polar form $\nu(B) = \int\lambda(d\eta)\int_0^\infty 1_B(r\eta)k_\eta(r)dr/r$ (500); (b) hence it gives every countable set mass $0$ (500) and every sphere about $0$ mass $0$ (436); (c) on the line, the density form $k(x)dx/x$ with $k$ monotone is self-decomposability (152; 158, "an atomic Levy measure is self-decomposable for no parameter values").

**Verdict: NARROWER-OK.** (a) is Thm. 15.10 verbatim (the draft's $\eta$ is Sato's $\xi$). (b) is a consequence that is not printed: for each $\xi$ the set of $r$ with $r\xi$ in a countable set (or on a sphere about $0$) is countable, hence $dr/r$-null, so the iterated integral is $0$; and $\nu(\{0\}) = 0$ by (8.2). The blueprint should state (b) as a corollary with that one-line reason. (c) is Cor. 15.11 as printed on **p. 95**. The draft's "$k$ nonincreasing" for the symmetric folded case is Sato's "increasing on $(-\infty,0)$, decreasing on $(0,\infty)$" restricted to even $k$, "decreasing" being weak. Sato's exponent has $-\frac12Az^2$ and the unfolded measure; the draft's (2.0) has $a\omega^2$ and the folded one, the same up to the conventions recorded at A39.

## A46

### From `records/pyramids/VERBATIM-Sato.md`, section "A46 -- An infinitely divisible law other than a point mass has unbounded support"

**Cite:** sato1999levy -- Corollary 24.4, printed p. 149 (statement at the head of the page, after the end of the preceding proof).

**Source, verbatim (p. 149).**
> COROLLARY 24.4. *If $\mu$ is infinitely divisible on $\mathbb{R}^d$ and if $\mu$ is not a $\delta$-distribution, then $S_\mu$ is unbounded.*

($S_\mu$ is the support of $\mu$.)

**Used as (the draft, lines 219, 279, 508, 815):** an infinitely divisible law that is not a point mass has unbounded support, "a statement on $\mathbb{R}^d$".

**Verdict: MATCH.** Stated on $\mathbb{R}^d$, as the draft says; a "$\delta$-distribution" is a point mass.

## A48

### From `records/pyramids/VERBATIM-Sato.md`, section "A48 -- An infinitely divisible law carried by $\mathbb{Z}$ has no Gaussian part and a finite Levy measure carried by $\mathbb{Z}$"

**Cite:** sato1999levy -- Corollary 24.6 (Support in $\mathbb{Z}$), printed p. 149 (statement in the middle; the proof follows on the same page).

**Source, verbatim (p. 149).**
> COROLLARY 24.6 (Support in $\mathbb{Z}$). *Let $\mu$ be an infinitely divisible distribution on $\mathbb{R}$ with generating triplet $(A,\nu,\gamma)$. Then $S_\mu \subset \mathbb{Z}$ if and only if $A = 0$, $S_\nu \subset \mathbb{Z}$, and the drift $\gamma_0$ is in $\mathbb{Z}$.*

The source of "finite", in the proof: "Hence it is shown that $\nu(\mathbb{R}) < \infty$" (the only-if part) and, at the end, "Note that $S_\nu \subset \mathbb{Z}$ implies that the total mass of $\nu$ is finite."

**Used as (the draft, lines 279, 774):** a law supported in $h\mathbb{Z}$ has no Gaussian part and its Levy measure is carried by $h\mathbb{Z}$ and finite (rescaled by $h$, 279); each coordinate image of a law carried by $\mathbb{Z}^d$ has $A_{ii} = 0$ and a finite Levy measure on $\mathbb{Z}$ (774, with Prop. 11.10).

**Verdict: NARROWER-OK.** The draft uses the "only if" half. Two points for the axiom: it is stated on **$\mathbb{R}$** (the draft applies it for $d = 1$ and to coordinate images, so no $d$-dimensional version is needed; the catalogue's "carried by $\mathbb{Z}$" is right, "on $\mathbb{R}^d$" would not be), and finiteness of $\nu$ is in the *proof*, not the statement, so the axiom should read "$\nu$ carried by $\mathbb{Z}$ and finite (p. 149, in the proof)". The drift condition $\gamma_0 \in \mathbb{Z}$ is not used.

## A49

### From `records/pyramids/VERBATIM-Sato.md`, section "A49 -- The $g$-moment theorem"

**Cite:** sato1999levy -- Theorem 25.3 ($g$-Moment), printed p. 159 (with Definitions 25.1, 25.2 above it on the same page).

**Source, verbatim (p. 159).**
> DEFINITION 25.1. Let $g(x)$ be a nonnegative measurable function on $\mathbb{R}^d$. We call $\int g(x)\mu(\mathrm{d}x)$ the *$g$-moment* of a measure $\mu$ on $\mathbb{R}^d$. We call $E[g(X)]$ the *$g$-moment* of a random variable $X$ on $\mathbb{R}^d$.
>
> DEFINITION 25.2. A function $g(x)$ on $\mathbb{R}^d$ is called *submultiplicative* if it is nonnegative and there is a constant $a > 0$ such that
>
> (25.1) $\quad g(x + y) \le a\,g(x)g(y)$ for $x, y \in \mathbb{R}^d$.
>
> A function bounded on every compact set is called *locally bounded*.
>
> THEOREM 25.3 ($g$-Moment). *Let $g$ be a submultiplicative, locally bounded, measurable function on $\mathbb{R}^d$. Then, finiteness of the $g$-moment is not a time dependent distributional property in the class of Levy processes. Let $\{X_t\}$ be a Levy process on $\mathbb{R}^d$ with Levy measure $\nu$. Then, $X_t$ has finite $g$-moment for every $t > 0$ if and only if $[\nu]_{\{|x|>1\}}$ has finite $g$-moment.*

**Used as (the draft, lines 285, 496, 823):** an infinitely divisible law has a finite $g$-moment iff its Levy measure restricted to $\{|x| > 1\}$ does, with $g(x) = \log(|x| \vee e)$, "stated on $\mathbb{R}^d$" (823).

**Verdict: NARROWER-OK, one hypothesis to add.** (a) *Law versus process.* The theorem says "for every $t > 0$" and that finiteness "is not a time dependent distributional property", so it holds at $t = 1$, the law $P_{X_1}$. (b) *Hypothesis the draft omits.* $g$ must be submultiplicative **and locally bounded** and measurable. For $g = \log(|x| \vee e)$ this is immediate (continuous, $\ge 1$), but the axiom should name it. (c) The draft's "$g - \log_+|\cdot|$ is bounded" (823, 496) is its own step from $g$ to $\log_+|x|$, not on the page.

## A50

### From `records/pyramids/VERBATIM-Sato.md`, section "A50 -- $\log(|x| \vee \mathrm{e})$ is submultiplicative"

**Cite:** sato1999levy -- Proposition 25.4(iii), printed p. 159 (below Theorem 25.3).

**Source, verbatim (p. 159).**
> PROPOSITION 25.4. (i) *The product of two submultiplicative functions is submultiplicative.* (ii) *If $g(x)$ is submultiplicative on $\mathbb{R}^d$, then so is $g(cx + \gamma)^\alpha$ with $c \in \mathbb{R}$, $\gamma \in \mathbb{R}^d$, and $\alpha > 0$.* (iii) *Let $0 < \beta \le 1$. Then the following functions are submultiplicative:*
>
> $|x| \vee 1,\ |x_j| \vee 1,\ x_j \vee 1,\ \exp(|x|^\beta),\ \exp(|x_j|^\beta),$
> $\exp((x_j \vee 0)^\beta),\ \log(|x| \vee \mathrm{e}),\ \log(|x_j| \vee \mathrm{e}),\ \log(x_j \vee \mathrm{e}),$
> $\log\log(|x| \vee \mathrm{e}^\mathrm{e}),\ \log\log(|x_j| \vee \mathrm{e}^\mathrm{e}),\ \log\log(x_j \vee \mathrm{e}^\mathrm{e}).$
>
> *Here $x_j$ is the $j$th component of $x$.*

**Used as (the draft, lines 285, 496, 823):** $g(x) = \log(|x| \vee e)$ is submultiplicative.

**Verdict: MATCH.** The function is in the list of (iii) ($\beta$ plays no role for it). Local boundedness, which Thm. 25.3 needs (A49), is not printed here and is immediate for this $g$.

## A51

### From `records/pyramids/VERBATIM-literature.md`, section "A51 -- DLMF 10.32.10 and the K_nu evaluations at lines 590 and 602"

**Cite:** DLMF, https://dlmf.nist.gov/10.32.E10 (Version 1.2.8, release date 2026-09-15), Section 10.32 "Integral Representations",
equation 10.32.10; also 10.32.8, 10.29.3, 10.29.1, 10.39.2, 10.30.3 for the further facts the draft uses.

**Source, verbatim (DLMF 10.32.10, as published).**
> $$K_\nu(z) = \tfrac12(\tfrac12 z)^\nu\int_0^\infty \exp\left(-t - \frac{z^2}{4t}\right)\frac{dt}{t^{\nu+1}},\qquad |\mathrm{ph}\,z| < \tfrac14\pi.$$

(TeX source on the page: `K_{\nu}(z)=\tfrac{1}{2}(\tfrac{1}{2}z)^{\nu}\int_{0}^{\infty}\exp(-t-\frac{z^{2}}{4t})\frac{dt}{t^{\nu+1}}`, `|\operatorname{ph}z|<\tfrac{1}{4}\pi`.
No condition on $\nu$ is printed.) For real $y > 0$ the phase condition holds.

The other facts the draft uses, as published in the same release:
> 10.32.8: $K_\nu(z) = \frac{\pi^{1/2}(\frac12 z)^\nu}{\Gamma(\nu+\frac12)}\int_0^\infty e^{-z\cosh t}(\sinh t)^{2\nu}\,dt = \frac{\pi^{1/2}(\frac12 z)^\nu}{\Gamma(\nu+\frac12)}\int_1^\infty e^{-zt}(t^2-1)^{\nu-\frac12}\,dt$, $\Re\nu > -\frac12$, $|\mathrm{ph}\,z| < \frac12\pi$.
> 10.39.2: $K_{1/2}(z) = K_{-1/2}(z) = \left(\frac{\pi}{2z}\right)^{1/2}e^{-z}$.
> 10.29.3: $I_0'(z) = I_1(z)$, $K_0'(z) = -K_1(z)$.
> 10.29.1: $\mathscr{Z}_{\nu-1}(z) - \mathscr{Z}_{\nu+1}(z) = (2\nu/z)\mathscr{Z}_\nu(z)$, $\mathscr{Z}_{\nu-1}(z) + \mathscr{Z}_{\nu+1}(z) = 2\mathscr{Z}'_\nu(z)$ ($\mathscr{Z}$ a modified cylinder function, $I_\nu$ or $e^{\nu\pi i}K_\nu$; for $K$ this reads $K_{\nu+1} = K_{\nu-1} + (2\nu/z)K_\nu$).
> 10.30.3: $K_0(z) \sim -\ln z$ ($z \to 0$).

**Used as (the draft, lines 541, 590, 602):** (541) $K_\nu$ by 10.32.10; the substitution $t = y^2/(4v)$ gives
$\int_0^\infty v^{\nu-1}e^{-v-y^2/(4v)}\,dv = 2(y/2)^\nu K_\nu(y)$, hence $b_d(y) = \frac{4}{\Gamma(d/2)}(y/2)^{d/2}K_{d/2}(y)$.
(590) $b_1 = 2e^{-y}$, $b_2(v)/v = 2K_1(v)$, $b_3 = 2(1+v)e^{-v}$; the antiderivative by $K_0' = -K_1$; $K_0(y) = \int_1^\infty e^{-ys}(s^2-1)^{-1/2}ds$.
(602) $G = (2\pi)^{-1}K_0(|x|)$ at $d = 2$ and $K_0(y) \sim \log(1/y)$.

**Verdict: MATCH, with a correction of the draft’s own sentence.** 10.32.10 is as the draft prints it. My check of the substitution: with
$c = y^2/4$ and $t = c/v$, $\int_0^\infty t^{-\nu-1}e^{-t-c/t}dt = c^{-\nu}\int_0^\infty v^{\nu-1}e^{-v-c/v}dv$, so
$\int v^{\nu-1}e^{-v-y^2/(4v)}dv = 2(y/2)^\nu K_\nu(y)$, as printed. Closed forms: $d = 1$, by 10.39.2, $b_1 = \frac{4}{\sqrt\pi}\sqrt{y/2}\sqrt{\pi/(2y)}e^{-y} = 2e^{-y}$ (draft: same);
$d = 2$: $b_2 = 2yK_1(y)$, so $b_2(v)/v = 2K_1$ (draft: same); $d = 3$ needs $K_{3/2}$, which is 10.39.2 with the recurrence 10.29.1,
$K_{3/2} = K_{-1/2} + z^{-1}K_{1/2} = (\pi/2z)^{1/2}e^{-z}(1 + 1/z)$, giving $b_3 = 2(1+y)e^{-y}$ (draft: same); the density at $d = 2$ ($\nu = 0$):
$\int_0^\infty s^{-1}e^{-s-y^2/(4s)}ds = 2K_0(y)$, so $G = (4\pi)^{-1}\cdot 2K_0 = (2\pi)^{-1}K_0$ (draft: same). What is wrong is the
sentence "Only the integral form is used below" (541): 590 and 602 use the explicit $K_0$, $K_1$, $K_{3/2}$ evaluations, $K_0' = -K_1$
(10.29.3), the $K_0$ integral (10.32.8 at $\nu = 0$, where $\pi^{1/2}/\Gamma(1/2) = 1$) and the behaviour at 0 (10.30.3). The blueprint should cite
those equation numbers and drop "only the integral form". $K_{1/2}$ enters only at $d = 1$ (line 541, "elementary"). The
$E_1(y) = \int_1^\infty e^{-ys}ds/s$ of line 590 is $E_1(y) = \int_y^\infty e^{-t}dt/t$ after $t = ys$ (DLMF 6.2.1; section 6.2 not rendered here).

### From `records/pyramids/VERBATIM-literature.md`, section "A51, addendum: DLMF 10.32.9 (2026-11-13)"

**Cite:** DLMF, https://dlmf.nist.gov/10.32.E9 (Version 1.2.8, release date 2026-09-15), Section 10.32 "Integral Representations", equation 10.32.9; record `dlmf2026`.

**Source, verbatim (DLMF 10.32.9, as published).**
> $$K_\nu(z) = \int_0^\infty e^{-z\cosh t}\cosh(\nu t)\,dt,\qquad |\mathrm{ph}\,z| < \tfrac12\pi.$$

(TeX source on the page: `K_{\nu}\left(z\right)=\int_{0}^{\infty}e^{-z\cosh t}\cosh\left(\nu t\right)\,\mathrm{d}t`, condition `|\operatorname{ph}z|<\tfrac{1}{2}\pi`. No condition on $\nu$ is printed.)

**The Lean definition** (shared core `ScaleSpaceCore/StudentTransform.lean`, line 74, attributed there to DLMF 10.32.9):
`noncomputable def besselK (nu z : Real) : Real := integral u in Ioi 0, Real.exp (-(z * Real.cosh u)) * Real.cosh (nu * u)`,
docstring "valid for `z > 0`".

**Comparison.** Integrand $e^{-z\cosh u}\cosh(\nu u)$ over $(0,\infty)$ in the bound variable $u$ (DLMF: $t$): the same formula. Variables: real $\nu$ (DLMF allows any $\nu$) and real $z$. Range: the DLMF condition $|\mathrm{ph}\,z| < \tfrac12\pi$ restricted to real $z$ is exactly $z > 0$, which is the range the docstring states. For $z \le 0$ the integral diverges and the Bochner integral returns the junk value $0$; the definition is total but is $K_\nu$ only for $z > 0$, so a use of `besselK` must carry $0 < z$ (the core's `lintegral_cosh_exp_eq_besselK` carries it as a hypothesis). Complex $z$ with $\Re z > 0$ is not covered, and is not used.

**Verdict: MATCH** (formula, variables and range $z > 0$; the Lean definition is the real-$z$ restriction of 10.32.9).

## A55

### From `records/pyramids/VERBATIM-literature.md`, section "A55 -- Bernstein’s theorem (Schilling-Song-Vondracek, Thm. 1.4)"

**Cite:** schilling2012bernstein -- Theorem 1.4 (Bernstein), printed p. 3.

**Source, verbatim (p. 3).**
> **Theorem 1.4** (Bernstein). Let $f : (0,\infty) \to \mathbb{R}$ be a completely monotone function. Then it is the Laplace transform of a unique measure $\mu$ on $[0,\infty)$, i.e. for all $\lambda > 0$,
> $$f(\lambda) = \mathscr{L}(\mu;\lambda) = \int_{[0,\infty)}e^{-\lambda t}\,\mu(dt).$$
> Conversely, whenever $\mathscr{L}(\mu;\lambda) < \infty$ for every $\lambda > 0$, $\lambda \mapsto \mathscr{L}(\mu;\lambda)$ is a completely monotone function.

**Used as (the draft, line 588):** $k_d$ completely monotone gives $k_d(r) = \int_{[0,\infty)}e^{-rs}\,m(ds)$ for a positive measure $m$.

**Verdict: MATCH.** Same statement and the same space $[0,\infty)$; uniqueness is not used. (The measure is positive because $f \ge 0$ for completely monotone $f$; the book’s "measure" is a positive measure.)

## A57

Two records: Schilling-Song-Vondracek, Thm. 13.14 with Example 13.13 (the primary, `VERBATIM-literature.md`), and Sato, Thm. 30.1 (the mechanism, `VERBATIM-Sato.md`).

### From `records/pyramids/VERBATIM-literature.md`, section "A57 -- f(|xi|^2), f a Bernstein function, is an exponent on R^d in every d (subordination of Brownian motion)"

**Cite:** schilling2012bernstein -- Theorem 13.14 (Schoenberg; Bochner), printed p. 212, with Example 13.13 (same page) for the direction used. (Sato 1999 not read here.)

**Source, verbatim (p. 212, Thm. 13.14 and its proof).**
> **Theorem 13.14** (Schoenberg; Bochner). *A function $f : (0,\infty) \to [0,\infty)$ is a Bernstein function if, and only if, for all $d \in \mathbb{N}$ the function $\xi \mapsto f(|\xi|^2)$, $\xi \in \mathbb{R}^d$, is continuous and negative definite.*
>
> *Proof.* Since $\xi \mapsto |\xi|^2$ is continuous and negative definite in all dimensions, sufficiency follows from Example 13.13.
> Conversely, fix $d \in \mathbb{N}$ and assume that $f(|\xi|^2)$ is continuous and negative definite. By Proposition 4.4 this is equivalent to saying that $F_t(|\xi|^2) := \exp(-tf(|\xi|^2))$ is continuous and positive definite for all $t > 0$, and by Bochner’s theorem, Theorem 4.14, we know that $F_t(|\xi|^2)$ is for fixed $t > 0$ a Fourier transform. This means that
> $$F_t(|\xi|^2) = \int_{\mathbb{R}^d}e^{i\xi\cdot y}\,\nu^t_d(dy),\quad t > 0, \qquad (13.21)$$
> with a measure $\nu^t_d$ on $\mathbb{R}^d$ which is invariant under rotations and whose total mass $\nu^t_d(\mathbb{R}^d) = F_t(0) = \exp(-tf(0))$ does not depend on the dimension $d$.

Example 13.13 (p. 212) is the subordination: the Levy process $(X_t)$ with exponent $\psi$ and the (killed) subordinator of $f$ give $\mathbb{E}e^{i\xi X^f_t} = e^{-tf(\psi(\xi))}$; with $\psi(\xi) = |\xi|^2$ this is the exponent $f(|\xi|^2)$.

**Used as:** a Bernstein function $f$ gives, in every $d$, $f(|\xi|^2)$ as the exponent of a rotation-invariant convolution semigroup, i.e. of an infinitely divisible law, on $\mathbb{R}^d$.

**Verdict: MATCH on the statement; one caveat.** The direction used (a Bernstein function gives a continuous negative definite $f(|\xi|^2)$ in every $d$) is Thm. 13.14, by Example 13.13; the
semigroup $e^{-tf(|\xi|^2)}$ is the Fourier transform of the rotation-invariant $\nu^t_d$ in (13.21), of total mass $e^{-tf(0)}$. So the laws are probability laws exactly when $f(0) = 0$ (no
killing); for $f(0) > 0$ the semigroup is sub-probability. The page does not use the phrase "infinitely divisible law"; it says the exponent of a Levy process / convolution semigroup,
which for $f(0) = 0$ is the same statement. A blueprint statement should carry $f(0) = 0$ (as the draft’s $\log(1+cu)$ does). The page is 212 (one page, with the proof by Example 13.13).

### From `records/pyramids/VERBATIM-Sato.md`, section "A57 -- A Bernstein function of $|\omega|^2$ is the exponent of an infinitely divisible law on $\mathbb{R}^d$ (subordination of Brownian motion)"

**Cite:** sato1999levy -- Theorem 30.1 (subordination of Levy processes), printed pp. 197-198 (hypotheses and (30.1)-(30.3) at the foot of p. 197; (30.4)-(30.9) at the head of p. 198). Sato does not use the word "Bernstein".

**Source, verbatim (p. 197, foot, and p. 198, head).**
> THEOREM 30.1. *Let $\{Z_t : t \ge 0\}$ be a subordinator (an increasing Levy process on $\mathbb{R}$) with Levy measure $\rho$, drift $\beta_0$, and $P_{Z_1} = \lambda$. That is,*
>
> (30.1) $\quad E[\mathrm{e}^{-uZ_t}] = \int_{[0,\infty)}\mathrm{e}^{-us}\lambda^t(\mathrm{d}s) = \mathrm{e}^{t\Psi(-u)},\quad u \ge 0,$
>
> *where, for any complex $w$ with $\mathrm{Re}\,w \le 0$,*
>
> (30.2) $\quad \Psi(w) = \beta_0 w + \int_{(0,\infty)}(\mathrm{e}^{ws} - 1)\rho(\mathrm{d}s)$
>
> *with*
>
> (30.3) $\quad \beta_0 \ge 0 \quad\text{and}\quad \int_{(0,\infty)}(1 \wedge s)\rho(\mathrm{d}s) < \infty.$
>
> *Let $\{X_t\}$ be a Levy process on $\mathbb{R}^d$ with generating triplet $(A,\nu,\gamma)$ and let $\mu = P_{X_1}$. Suppose that $\{X_t\}$ and $\{Z_t\}$ are independent. Define*
>
> (30.4) $\quad Y_t(\omega) = X_{Z_t(\omega)}(\omega),\quad t \ge 0.$
>
> *Then $\{Y_t\}$ is a Levy process on $\mathbb{R}^d$ and*
>
> (30.5) $\quad P[Y_t \in B] = \int_{[0,\infty)}\mu^s(B)\lambda^t(\mathrm{d}s),\quad B \in \mathcal{B}(\mathbb{R}^d),$
>
> (30.6) $\quad E[\mathrm{e}^{\mathrm{i}\langle z,Y_t\rangle}] = \mathrm{e}^{t\Psi(\log\hat\mu(z))},\quad z \in \mathbb{R}^d.$
>
> *The generating triplet $(A^\sharp,\nu^\sharp,\gamma^\sharp)$ of $\{Y_t\}$ is as follows:* (30.7) $A^\sharp = \beta_0A$, (30.8) $\nu^\sharp(B) = \beta_0\nu(B) + \int_{(0,\infty)}\mu^s(B)\rho(\mathrm{d}s)$, $B \in \mathcal{B}(\mathbb{R}^d \setminus \{0\})$, (30.9) $\gamma^\sharp = \beta_0\gamma + \int_{(0,\infty)}\rho(\mathrm{d}s)\int_{|x|\le 1}x\mu^s(\mathrm{d}x)$. *If $\beta_0 = 0$ and $\int_{(0,1]}s^{1/2}\rho(\mathrm{d}s) < \infty$, then $\{Y_t\}$ is of type A or B and has drift $0$.*

Definition 30.2 (p. 198): the transformation of $\{X_t\}$ to $\{Y_t\}$ is called *subordination* by the subordinator $\{Z_t\}$; "any Levy process identical in law with $\{Y_t\}$ is said to be *subordinate* to $\{X_t\}$". Chapter 6 opening (p. 197): "Subordination is a transformation of a stochastic process to a new stochastic process through random time change by an increasing Levy process (subordinator) independent of the original process."

The statement the draft needs is read off Thm. 30.1 with $X_t$ Brownian motion on $\mathbb{R}^d$ (triplet $(I,0,0)$, so $\hat\mu(z) = \mathrm{e}^{-|z|^2/2}$ and $\log\hat\mu(z) = -|z|^2/2$). By (30.6), $E[\mathrm{e}^{\mathrm{i}\langle z,Y_1\rangle}] = \mathrm{e}^{\Psi(-|z|^2/2)}$, and by (30.2) $-\Psi(-u) = f(u) := \beta_0u + \int_{(0,\infty)}(1-\mathrm{e}^{-us})\rho(\mathrm{d}s)$. So $Y_1$ has an infinitely divisible law on $\mathbb{R}^d$ with transform $\mathrm{e}^{-f(|z|^2/2)}$, for every $d$.

**Used as (the draft, line 561):** "A Bernstein function is a function $f \ge 0$ on $(0, \infty)$ whose derivative is completely monotone, and $e^{-f(|\omega|^2)}$ is then the transform of an infinitely divisible law in every dimension, by subordination."

**Verdict: MISMATCH (mild: a two-source fact with a factor 2).** Sato holds the mechanism, and it is dimension-free ($d$ arbitrary in Thm. 30.1), which is what "in every dimension" needs. Three gaps between the page and the sentence:
1. *Term.* Sato writes the subordinator exponent as $f(u) = \beta_0u + \int(1-e^{-us})\rho(ds)$ with (30.3). That a function $f \ge 0$ with completely monotone derivative has this form (a Bernstein function) is not in Sato: the word does not occur on pp. 197-199. It is the Bernstein representation in the Schilling-Song-Vondracek book the draft already cites in the next sentence. The subordinator with exponent $f$ exists by Sato Thm. 8.1(iii) and the Levy process construction of Section 11.
2. *Factor 2.* Brownian motion with triplet $(I,0,0)$ gives $e^{-f(|\omega|^2/2)}$. For $e^{-F(|\omega|^2)}$ subordinate with $\tilde f(u) = f(2u)$ (again of the form (30.2), with $\beta_0$ doubled and $\rho$ rescaled), or use Brownian motion with triplet $(2I,0,0)$. The sentence is right; the page proves $f(|z|^2/2)$.
3. *Law versus process.* The statement is for $Y_1$, a Levy process at time $1$.

Recommended anchor: "[Sato, Thm. 30.1, pp. 197-198, with $X$ Brownian motion; the Bernstein representation is SSV]", with the factor-2 step stated as the blueprint own one line.

