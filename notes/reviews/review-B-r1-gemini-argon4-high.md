Here is a ranked list of the twenty editorial changes that would most improve the readability of the manuscript for a mathematical-imaging researcher. Page references are to the main paper (`pp. 1–112`), with references to the supplement marked `Supp. pp. S.1–S.46`.

---

### 1. Move the Lean verification ledger out of Sections 1.1 and 2 so the mathematical story begins before page 19
* **Page reference:** `pp. 5–18` (Sections 1.1 and 2) and `pp. 106–112` (Appendix A).
* **What is wrong:** A reader does not reach the paper’s first new mathematical definition (Definition 3.1) until **page 19**. Section 1.1 (`pp. 5–6`) spends two pages listing Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`, `AffineHemigroup.khintchine_null_array`, etc.) that duplicate Appendix A (`pp. 106–108`). Section 2 (`pp. 6–18`, *"What is cited"*) is organized as a 12-page verification ledger of 33 definitions and theorems—including full proofs of five background lemmas (Theorems 2.2, 2.3, 2.9, 2.16, 2.22) and six theorems (Theorems 2.7, 2.12, 2.13, 2.14, 2.30, 2.31) that *"are stated for the reader and read by no proof of this paper"* (`p. 6`).
* **Concrete fix:** Compress Section 1.1 into a single paragraph at the end of the Introduction pointing to Appendix A. Rename Section 2 *"Preliminaries on hemigroups and infinitely divisible laws"*, trim it to 4–5 pages covering only what Section 3 needs immediately, move the proofs of Theorems 2.2, 2.3, 2.9, 2.16, and 2.22 to an appendix, and move the specialized tools for Section 5 (Bernstein classes in §2.2.2, Schoenberg’s theorem in §2.2.3, and the Bessel integral in §2.2.4) to Section 5 where they are actually used.

---

### 2. Give a spatial-filtering and PDE interpretation of "infinitely divisible laws" and "Lévy measures" when they first appear, and state a single symmetric Lévy–Khintchine corollary
* **Page reference:** `pp. 8, 11, 14, 20` (Theorem 2.17, equation (2.2), and Lemma 3.4); see also `pp. 27, 74, 86, 91, 93`.
* **What is wrong:** On `p. 8` and `p. 21`, the paper explains the Lévy measure $\nu_t$ (or its fold $\varpi_t$) by saying that it *"counts the jumps by their length"* or *"is the rate of the jumps of each size and direction"*. To an imaging researcher used to spatial convolution kernels and PDEs, "jumps" of a smooth spatial filter (such as a Cauchy or Matérn kernel) is jarring because there is no time process jumping in space. Moreover, Theorem 2.17 (`p. 14`) states Sato’s general asymmetric Lévy–Khintchine formula with drift $\gamma$ and compensator $i\langle z,x\rangle\mathbf{1}_D(x)$. Because every law in the paper is symmetric, seven different proofs (`p. 8`, `p. 20`, `p. 27`, `p. 74`, `p. 86`, `p. 91`, `p. 93`) repeat the exact same paragraph showing that under $x \mapsto -x$ the drift $\gamma$ vanishes and the odd part $i\sin\langle\omega,x\rangle - i\langle\omega,x\rangle\mathbf{1}_{\{|x|\le 1\}}$ integrates to zero.
* **Concrete fix:**
  1. In Section 2 (`pp. 8, 11`), explain that the scale parameter $t$ plays the role of time in a stochastic process: in the generator (2.2) on `p. 11`, the Gaussian part $A$ generates local diffusion ($\Delta$), while the Lévy measure $\nu(dx)$ weights nonlocal finite-difference smoothing operators $\delta_x^2 g(y) = \frac{1}{2}(g(y-x)+g(y+x)) - g(y)$ of spatial span $x$.
  2. Immediately after Theorem 2.17 (`p. 14`), state a **Symmetric Lévy–Khintchine Corollary**: a law $\mu$ on $\mathbb{R}^d$ is symmetric and infinitely divisible iff $\widehat{\mu}(\omega) = \exp[-\langle \omega, A\omega\rangle - \int_{\mathbb{R}^d}(1-\cos\langle\omega,x\rangle)\,\nu(dx)]$ for a unique positive semidefinite $A$ and unique symmetric Lévy measure $\nu$ with $\nu(\{0\})=0$. Cite this corollary throughout Sections 3–6 instead of re-deriving the cancellation of the compensator seven times.

---

### 3. Disentangle the "Matérn pyramid" from the "Matérn family" early and explicitly
* **Page reference:** `pp. 12–13` (Theorem 2.13 and §2.1.5), `p. 47` (Proposition 4.6(1)), `p. 49` (Proposition 4.7(2)), `pp. 55–58` (Definition 5.1 and Theorem 5.4), and `p. 81` (Proposition 5.20(1)).
* **What is wrong:** The manuscript uses the name "Matérn" for two different scale-space families whose roles of *kernel* and *octave step* are swapped:
  * In the **Matérn scale-space family** (Theorem 2.13 on `p. 12`, §2.1.5 on `p. 13`, Proposition 4.6(1) on `p. 47`, and Proposition 5.20(1) on `p. 81`), the *kernel from scale zero* $\mu_{0,t}$ is the Matérn/Bessel potential law $L_t$ with transform $(1+t^2|\omega|^2)^{-1}$ (or power $-\gamma$), while its *octave step* $\mu_{t,qt}$ is the mixture $q^{-2}\delta_0 + (1-q^{-2})L_{qt}$.
  * In the **Matérn pyramid** (Proposition 4.7(2) on `p. 49` and Theorem 5.4 on `p. 58`), the *octave step* $\mu_{t,qt}$ is the single Bessel potential $L_{ct}$ with transform $(1+c^2t^2|\omega|^2)^{-1}$, while the *kernel from scale zero* $\mu_{0,t}$ is the infinite product $\prod_{i\ge 1}(1+c^2q^{-2i}t^2|\omega|^2)^{-1}$.
  Because Proposition 4.6(1) (`p. 47`) treats the first and Proposition 4.7(2) (`p. 49`) switches to the second without warning, a reader can easily conflate them.
* **Concrete fix:** Add a short displayed comparison table or remark in Section 2.1.5 (`p. 13`, with a reminder at the start of Section 4.3 on `p. 46` and Section 5.1 on `p. 55`) contrasting the **Matérn family** ($\mu_{0,t} = L_t$, $\mu_{t,qt} = q^{-2}\delta_0 + (1-q^{-2})L_{qt}$) and the **Matérn pyramid** ($\mu_{0,t} = *_{i\ge 1} L_{ctq^{-i}}$, $\mu_{t,qt} = L_{ct}$).

---

### 4. Replace the numbered labels "exact in sense (i), (ii), (iii)" and "exact cascade" with self-explanatory terms, and define them before Section 4.3
* **Page reference:** `p. 3`, `pp. 42–43` (Section 4.2), `pp. 48–49` (Proposition 4.7), and `pp. 83–84` (Definitions 6.1 and 6.2).
* **What is wrong:** The paper uses the single word *exact* for four different properties: (i) zero discretization/aliasing discrepancy between a grid algorithm and the kernels it represents, (ii) closure of a parametric grid kernel family under subsampling, (iii) embeddability of a discrete mask ladder $D_{q^n}w$ into a continuous-scale $q$-covariant hemigroup, and (iv) a discrete hemigroup on a fixed grid (*"exact cascade on the grid"*). Worse, Section 4.2 (`p. 43`) and Proposition 4.7 (`pp. 48–49`) use *"exact in sense (i)"*, *"exact in sense (ii) of Definition 6.2"*, and *"exact in sense (iii)"* **forty pages before Definition 6.2 appears on page 83**.
* **Concrete fix:** Move Definitions 6.1 and 6.2 to Section 4.2 (`p. 43`, or to a subsection of Section 3.4), and replace the opaque numbers *(i), (ii), (iii)* with descriptive names throughout the text:
  * **hemigroup-exact** (or simply **exact pyramid**) for sense (iii) (Definition 6.3);
  * **subsampling-closed** for sense (ii) (subsampling a grid-family kernel by $q$ yields another member of the same grid family);
  * **sample-commuting** (or **step-exact**) for sense (i) (the decimated grid recursion equals the sampled continuum step);
  * **grid hemigroup** for *"exact cascade on the grid"*.

---

### 5. Translate "semi-selfdecomposability with span $q$ and residual $\varrho_q$" directly into the pyramid refinability equation $D_q\mu_t = \mu_t * \mu_{t,qt}$
* **Page reference:** `p. 1` (Abstract), `p. 8` (Definition 2.4), `pp. 23–24` (Section 3.2 and Lemma 3.8), and `pp. 37–38` (Section 3.5).
* **What is wrong:** Definition 2.4 (`p. 8`) introduces semi-selfdecomposability in probability-theory form via contraction by $b^{-1}$: $\widehat{\mu}(z) = \widehat{\mu}(b^{-1}z)\widehat{\varrho}_b(z)$, calling $b$ the *span* and $\varrho_b$ the *residual*. In a pyramid (Lemma 3.8, `pp. 23–24`), covariance acts by dilating *upward* from scale $t$ to $qt$: $D_q\mu_t = \mu_{qt} = \mu_t * \mu_{t,qt}$, so the "residual" $\varrho_q = D_{q^{-1}}\mu_{t,qt}$ is simply the octave step rescaled by $q^{-1}$. To an imaging reader familiar with wavelet/subdivision refinability ($D_q\mu_1 = \mu_1 * w$, Section 3.5, `p. 37`), the terms *semi-selfdecomposable*, *span*, and *residual* obscure a very simple concept.
* **Concrete fix:** In Definition 2.4 (`p. 8`) and at the opening of Section 3.2 (`p. 23`), write the dilation form $D_q\mu_t = \mu_t * \mu_{t,qt}$ alongside the contraction form $\mu_t = D_{q^{-1}}\mu_t * \varrho_q$, and state explicitly: *"In pyramid terms, a kernel $\mu_t$ is semi-selfdecomposable with span $q$ if and only if it is refinable at ratio $q$ ($D_q\mu_t = \mu_t * \mu_{t,qt}$) with an infinitely divisible octave step $\mu_{t,qt} = D_q\varrho_q$."*

---

### 6. Precede the Stage Lemma (Proposition 5.18) with the 3-line PDE and Fourier-moment intuition for the implicit-Euler maximum principle
* **Page reference:** `pp. 75–78` (Definition 5.17 and Proposition 5.18).
* **What is wrong:** Proposition 5.18 (`pp. 76–78`) is the cornerstone of Section 5: a symmetric law $\mu$ satisfies $u(x) \le f(x)$ at every weak local maximum of $u = \mu * f$ iff $\widehat{\mu}(\omega) = (1 + \omega\cdot C\omega)^{-1}$ with $C \ge 0$. However, the proof jumps straight into Fourier integrals $Q_v$ and a two-page test-function argument with $f_s(x) = \sum_k a_k \cos\langle w_k,x\rangle e^{-s|x|^2}$ without explaining *why* the theorem is true.
* **Concrete fix:** Add a short intuitive paragraph before Proposition 5.18 (`p. 76`) explaining both directions in PDE/Fourier terms:
  * *Sufficiency:* When $\widehat{\mu}(\omega) = (1+\omega\cdot C\omega)^{-1}$, $u = \mu * f$ solves $(I - \nabla\cdot C\nabla)u = f$. At a local maximum $x$ of a smooth output $u$, the Hessian $\nabla^2 u(x)$ is negative semidefinite, so $f(x) - u(x) = -\operatorname{tr}(C\,\nabla^2 u(x)) \ge 0$.
  * *Converse:* Requiring $(f-u)(0) \ge 0$ whenever $u$ has a strict local maximum at $0$ means that in Fourier space $\int (\widehat{\mu}(\omega)^{-1}-1)\widehat{u}(\omega)\,d\omega \ge 0$ whenever the Hessian quadratic form $\int \langle\omega,v\rangle^2 \widehat{u}(\omega)\,d\omega \ge c|v|^2 > 0$. By linear duality (Step 3 on `p. 77`), a function that is nonnegative on all measures with positive definite second-moment matrix must be a positive semidefinite quadratic form $\widehat{\mu}(\omega)^{-1} - 1 = \omega\cdot C\omega$.

---

### 7. Factor out four recurring proof blocks instead of repeating them verbatim across Sections 3, 4, 5, and 6
* **Page reference:** `pp. 33–34` (Proposition 3.19), `pp. 44–45` (Proposition 4.5), `pp. 79–80` (Theorem 5.19(1)), `pp. 86–87` (Proposition 6.4), and `pp. 91–92` (Proposition 6.6).
* **What is wrong:** Because the proofs mirror standalone Lean declarations, four multi-paragraph calculations are written out repeatedly:
  1. *The tail-series bound for $\nu^* = \sum_{m\ge 1} D_{q^{-m}}\nu_\varrho$* (splitting $\sum_{m\ge 1}(1\wedge q^{-2m}|v|^2)$ at $N = \lfloor\log_q|v|\rfloor$ into $\log_q|v|$ and a geometric series): written out in Proposition 3.19(1)–(2) (`pp. 33–34`), Proposition 4.5(2) (`pp. 44–45`), Theorem 5.19(1) (`p. 79`), and Proposition 6.6(1) (`p. 91`).
  2. *The uniform coupling and split coupling construction showing non-uniqueness up to $\mathcal{G}_q$*: proved in Proposition 3.19(2) (`p. 34`) and then re-proved over a full page for $L_{\sqrt{\tau}}$ in Theorem 5.19(1) (`pp. 79–80`), plus again in Proposition 4.5(2) (`p. 45`) and Proposition 6.6(2) (`p. 92`).
  3. *Telescoping $D_q\nu_1 = \nu_w + \nu_1$ to $\nu_1 = \sum_{m\ge 1} D_{q^{-m}}\nu_w$ via $\nu_1(\{|x|>q^M\varepsilon\}) \to 0$*: repeated on `p. 33`, `p. 44`, `p. 86`, and `p. 91`.
  4. *The power-series derivation of the sampled Laplace Lévy measure $\varpi = \sum_{k\ge 1}\frac{2a^k}{k}\delta_{kh}$*: written out in Proposition 4.5(4) (`p. 45`) and repeated verbatim in Proposition 6.4(3) (`p. 87`).
* **Concrete fix:** State the $\nu^*$ logarithmic-moment equivalence and the uniform/split coupling construction once in Proposition 3.19(1)–(2) (`pp. 32–34`, noting that the split coupling is isotropic whenever $\nu_a, \nu_b$ are rotation invariant, e.g., by splitting a radial $\nu_\varrho$ at $\{|x|\le 1\}$ and $\{|x|>1\}$). In Proposition 4.5, Theorem 5.19(1), Proposition 6.4, and Proposition 6.6, cite Proposition 3.19 directly, cutting ~8 pages of duplicate proof text.

---

### 8. Standardize on a single normalization for the Gaussian part instead of switching between $a$, $A$, $A^{\mathrm{S}}$, and $a_0$
* **Page reference:** `pp. 8, 10–11` (Definition 2.10 and Theorem 2.11), `pp. 13–14` (§2.1.5 and Theorem 2.17), `p. 20` (Lemma 3.4), `p. 25` (Theorem 3.11), and `pp. 33, 35` (Proposition 3.19(4)(b)).
* **What is wrong:** The paper switches back and forth between two normalizations of the Gaussian term in the exponent:
  * **Paper normalization:** $\langle \omega, A_t\omega\rangle$ and $a(t)|\omega|^2$ (equation (2.1) on `p. 8`, Lemma 3.4 on `p. 20`, Theorem 3.11 on `p. 25`).
  * **Sato normalization:** $\frac{1}{2}\langle z, A^{\mathrm{S}}z\rangle$ and $\frac{1}{2}a_0|\xi|^2$ (Definition 2.10 on `p. 10`, Theorem 2.11 on `p. 11`, Theorem 2.17 on `p. 14`, and Proposition 3.19(4)(b) on `pp. 33, 35`, where $A_\varrho := \frac{1}{2}a_\varrho I$).
  Having to remember whether $a_0$ or $a(t)$ carries a factor of $\frac{1}{2}$ in Theorem 2.11(2) ($a = \frac{1}{2}a_0'$) and Proposition 3.19(4)(b) is a needless distraction.
* **Concrete fix:** Use the paper’s normalization $a|\omega|^2$ and $\langle \omega, A\omega\rangle$ in *all* of the paper’s own definitions and propositions—writing $a_0|\xi|^2$ in Definition 2.10 (`p. 10`), Theorem 2.11 (`p. 11`), and $a_\varrho|\omega|^2$ in Proposition 3.19(4)(b) (`p. 33`)—so that $A^{\mathrm{S}} = 2A$ appears only in the statement of Sato’s Theorem 2.17 (`p. 14`).

---

### 9. Move Section 6.4 (or the definitions of the discrete Helmholtz and nine-point resolvents $\kappa_t$ and $\kappa_t^9$) to the start of Section 6
* **Page reference:** `p. 83` (Section 6.1, Definition 6.1), `pp. 92–96` (Propositions 6.7 and 6.10), and `pp. 100–104` (Section 6.4).
* **What is wrong:** Section 6 cannot be read in linear order. On `p. 83`, the text advises twice that Section 6.4 *"may be read first"*. Definition 6.1(1) (`p. 83`), Figure 5 (`p. 89`), Proposition 6.7(4) (`p. 93`), and Proposition 6.10(1) (`p. 95`) all use the $(2d+1)$-point resolvent $\kappa_t$, the nine-point Laplacian $\Delta_9$, its random-walk step $\sigma_9$, and its resolvent $\kappa_t^9$, which are not defined until `pp. 101–103`.
* **Concrete fix:** Move the definitions of $\Delta_h, \kappa_t$ (from Proposition 6.15) and $\Delta_9, \sigma_9, \kappa_t^9$ (from Definition 6.16 and Proposition 6.18) to Section 6.1 right before Definition 6.1 (`p. 83`), or make Section 6.4 into Section 6.1.

---

### 10. Relocate the 5-page Bernstein / Thorin–Bernstein detour (Lemmas 5.5–5.7, Propositions 5.8–5.9) so it does not split Section 5.1 in half, and explain its imaging meaning
* **Page reference:** `pp. 16–17` (§2.2.2) and `pp. 62–67` (Lemmas 5.5–5.7 and Propositions 5.8–5.9).
* **What is wrong:** Right between the definition of the Matérn pyramid (Theorem 5.4, `p. 58`) and its computational/Laplacian properties (Lemma 5.10 and Propositions 5.11–5.12, `pp. 67–69`), Section 5.1 stops for five pages to prove technical lemmas on completely monotone functions along arithmetic progressions (Lemmas 5.5–5.7) and whether intermediate increments $\mu_{s,t}$ and polar profiles $b_d, k_d$ belong to the Thorin–Bernstein class (Propositions 5.8–5.9). An imaging reader who is not a specialist in Bernstein functions is never told *why* the Thorin property matters for scale space or image pyramids.
* **Concrete fix:**
  1. Move Lemmas 5.5–5.7 and Propositions 5.8–5.9 to the end of Section 5.1 (after Proposition 5.14, or into a separate subsection), so that Theorem 5.4 flows directly into Lemma 5.10 and Propositions 5.11–5.12.
  2. Add a three-sentence motivation before Proposition 5.8 explaining that on the line ($d=1$), a completely monotone profile $k_1$ means the Lévy measure is a positive mixture of exponential decays (the Thorin class), so the generator is a superposition of 1D Helmholtz resolvents; Propositions 5.8–5.9 show that in $d \ge 2$ the radial profile $k_d$ loses this exponential-mixture structure, while multi-octave steps ($t = q^k s$) remain finite cascades of $d$-dimensional Helmholtz resolvents.

---

### 11. Explain in PDE terms why the octave step $L_{ct}$ is singular at the origin in $d \ge 2$ while the knot kernel $\mu_t$ is $C^\infty$
* **Page reference:** `p. 55` (Lemma 5.2(1)), `pp. 58–60` (Theorem 5.4(1)), `pp. 67–68` (Proposition 5.11(3)), and `pp. 80–81`.
* **What is wrong:** In Lemma 5.2(1) and Proposition 5.11(3) (`pp. 67–68`), the octave step $L_{ct}$ has a density that blows up at the origin in $d \ge 2$ ($\sim \log(1/|x|)$ for $d=2$, $\sim |x|^{2-d}$ for $d \ge 3$), whereas in Theorem 5.4(1) (`p. 58`) the kernel $\mu_t$ from scale zero has a bounded $C^\infty$ density. The mathematical proofs are given, but the intuitive PDE explanation connecting them—and connecting the singularity of $L_{ct}$ to both the failure of point sampling (Proposition 5.11(3)) and the success of the implicit-Euler maximum principle (`pp. 80–81`)—is left implicit.
* **Concrete fix:** Add a short remark after Theorem 5.4 (`p. 62`) or Proposition 5.11 (`p. 68`): in $d \ge 2$, a single implicit Euler step $L_{ct} = (I - c^2t^2\Delta)^{-1}$ gains only two Sobolev derivatives (order $-2$), which is below the Sobolev embedding threshold $d/2$ for boundedness at $x=0$, producing the Green's function singularity at the origin (and preventing naive point-sampling discretization on $h\mathbb{Z}^d$). By contrast, the kernel $\mu_t = *_{i\ge 1} L_{ctq^{-i}}$ from scale zero applies infinitely many implicit steps at finer scales, gaining infinitely many derivatives and yielding a $C^\infty$ kernel.

---

### 12. Clarify the two practical caveats of grid pyramid computation: $\mu_{1,q^n}$ vs. $\mu_{0,q^n}$ (starting at scale $1$ vs. scale $0$) and why $U_n \ne V_n$ for $n \ge 2$
* **Page reference:** `p. 2` (Figure 1), `p. 46`, `pp. 49–52` (Proposition 4.7(2), Table 1, and Figure 3), and `p. 98` (Proposition 6.12(2)).
* **What is wrong:** Two key practical distinctions for anyone implementing a pyramid are buried late in technical proofs:
  1. The finest grid $h\mathbb{Z}^d$ is placed at knot scale $t = 1$ (not $t = 0$), so $n$ stages of the pyramid algorithm apply the finite ladder increment $\mu_{1,q^n} = w * D_q w * \cdots * D_{q^{n-1}}w$ rather than the knot kernel $\mu_{0,q^n} = D_{q^n}\mu_1 = \mu_1 * \mu_{1,q^n}$. This is only explained on `p. 46` (last two sentences) and `p. 98` (after Proposition 6.12).
  2. In Proposition 4.7(2) (`pp. 49–52`), the proof shows algebraically that the decimated recursion $U_n$ equals the sampled continuum Matérn step $V_n$ at level $n=1$ and differs from it for all $n \ge 2$, without explaining *why* in signal-processing terms.
* **Concrete fix:**
  1. In the caption of Figure 1 (`p. 2`) and at the start of Section 4.3 (`p. 46`), state clearly that a discrete input on $h\mathbb{Z}^d$ enters at scale $t=1$ (with $\mu_{0,1}$ representing the implicit pre-smoothing from the continuum to grid scale $1$), so level $n$ of the algorithm applies $\mu_{1,q^n}$.
  2. After Proposition 4.7(2) (`p. 52`), add a two-sentence Fourier explanation of $U_n \ne V_n$: at $n=1$, sampling commutes with a single Laplace step because $\lambda_{ct}$ is subsampling-closed; for $n \ge 2$, $U_n$ decimates *between* stages—folding high frequencies into the baseband before multiplying by the next stage’s transfer function—whereas $V_n$ multiplies the continuum transfer functions $(1+c^2t^2q^{2k}\omega^2)^{-1}$ first and aliases only once at the end.

---

### 13. Illustrate the difference between a gauge change $g \in \mathcal{G}_q$ and the inter-knot freedom ("modulation orbit") visually in Section 3.4
* **Page reference:** `pp. 21–22` (Lemma 3.5(3)), `pp. 32–34` (Proposition 3.19(2)), and `Supp. pp. S.12, S.21–S.22` (Supplement Figure 1 and Definition S.19).
* **What is wrong:** On `p. 22` and `pp. 33–34`, the paper emphasizes that the ladder fixes the knot kernels $\mu_{q^n}$ but leaves the family between the knots free, *"and not unique up to a relabelling in $\mathcal{G}_q$ either"*. In the main paper, the explanation of *why* this freedom is strictly larger than reparametrizing scale ($t \mapsto g(t)$ with $g(qt)=qg(t)$) is hidden inside the algebraic proof of Proposition 3.19(2) (`p. 34`, "the uniform coupling" vs. "the split coupling"), while the geometric picture that makes it obvious—the $(y,v)$ scale-displacement quadrant and cylinder $\mathcal{C} = [1,q)\times(0,\infty)$ in Supplement Figure 1 (`Supp. p. S.12`)—is only in the Supplement.
* **Concrete fix:** After Proposition 3.19 (`p. 36`), add a brief geometric remark (with an explicit pointer to Supplement Figure 1, `Supp. p. S.12`): a gauge relabelling $g \in \mathcal{G}_q$ advances *all* jump sizes at the same rate $p(t) = \log_q g(t)$ across the octave $t \in [1,q]$, whereas a general Stratum 2 family with the same ladder can schedule different jump sizes at different phases of the octave (e.g., turning on small jumps in $[1,\sqrt{q}]$ and large jumps in $[\sqrt{q},q]$).

---

### 14. Eliminate the redundancy between the 1D operator proofs in Section 4.1–4.2 and the $d$-dimensional law proofs in Sections 3 and 6
* **Page reference:** `pp. 39–46` (Sections 4.1 and 4.2) and `pp. 97–98` (Proposition 6.12(1)); see also `Supp. pp. S.1–S.7`.
* **What is wrong:** Section 3 proves the strata and ladder theorem in $\mathbb{R}^d$ for all $d \ge 1$ on probability laws, and Section 6 proves the exact grid-pyramid theorem on any lattice $\Gamma \subset \mathbb{R}^d$ for all $d \ge 1$. Yet Section 4.1–4.2 (`pp. 39–46`) re-formulates the 1D case in terms of $L^1(\mathbb{R})$ operators $\Phi_{s,t}$ and folded measures $\varpi_t$, spends two pages (`pp. 44–45`) re-proving Proposition 4.5 (which is the $d=1$ case of Proposition 6.6 on `p. 91`), and repeatedly invokes the boilerplate embedding *"read through the identification $x \mapsto xe_1$ of $\mathbb{R}$ with $\mathbb{R}^1$"* (`pp. 22, 39, 44, 45`), while Section S1 of the Supplement (`Supp. pp. S.1–S.7`) proves the 1D operator strata a third time.
* **Concrete fix:** In Section 4.1 (`pp. 39–41`), use Lemma 4.2 once to identify 1D operator families with $d=1$ symmetric law families, introduce the folded measure $\varpi_t$ (Definition 4.3), and state Proposition 4.5(1)–(3) as the immediate $d=1$ specialization of Propositions 3.19 and 6.6 (replacing the two-page proof of clauses (1)–(3) on `pp. 44–45` with a short paragraph translating $\nu_w$ on $\mathbb{R}\setminus\{0\}$ to its fold $\varpi_w$ on $(0,\infty)$, and keeping only the 1D-specific proof of clause (4) for the sampled Laplace and B-spline masks).

---

### 15. State the symmetric specialization of Schoenberg’s Pólya frequency theorem in Section 2.2.3
* **Page reference:** `p. 13` (Theorem 2.15), `pp. 17–18` (Theorem 2.32), `p. 58` (Theorem 5.4(3)), and `Supp. pp. S.39, S.42` (Theorem S.36 and Proposition S.39).
* **What is wrong:** The reader is not assumed to know Pólya frequency functions beyond what the paper teaches. Section 2.1.4 (`p. 13`) states that kernels with exponent $F(\omega) = a\omega^2 + \sum_i \log(1+\omega^2/\theta_i^2)$ are Pólya frequency densities (Theorem 2.15), and Section 2.2.3 (`pp. 17–18`) states Schoenberg’s general two-sided Laplace representation $L(i\omega)\psi(i\omega) = 1$ with $\psi(s) = e^{-\gamma s^2 + \delta s}\prod_j (1+a_j s)e^{-a_j s}$ (Theorem 2.32). However, the main paper never connects the two by pointing out that for a *symmetric* density $\phi$, $L(i\omega) = \widehat{\phi}(\omega) > 0$, so taking moduli in Schoenberg’s formula immediately yields $\widehat{\phi}(\omega)^{-1} = e^{\gamma\omega^2}\prod_j (1+a_j^2\omega^2)^{1/2}$, i.e., $-\log\widehat{\phi}(\omega) = \gamma\omega^2 + \frac{1}{2}\sum_j \log(1+a_j^2\omega^2)$.
* **Concrete fix:** Add a three-line remark right after Theorem 2.32 (`p. 18`) deriving this symmetric Fourier form of Schoenberg’s representation. This makes Theorem 2.15 (`p. 13`), the projection counts of Theorem 5.4(3) (`p. 58`), and the 1D Matérn Pólya-frequency results (Theorem S.36 and Proposition S.39, `Supp. pp. S.39, S.42`) immediately transparent.

---

### 16. Unify the indexing of grid kernels on $\mathbb{Z}^d$ vs. laws on $h\mathbb{Z}^d$ across Sections 4.3 and 6
* **Page reference:** `pp. 47–48` (Propositions 4.6(2) and 4.7), `p. 77` (proof of Proposition 5.18(2)), `p. 89` (proof of Proposition 6.5), `p. 94` (proof of Proposition 6.7(4)), `p. 96` (proof of Proposition 6.10), and `pp. 101–103` (Propositions 6.15 and 6.18).
* **What is wrong:** The manuscript alternates between treating a grid kernel as a probability measure on the scaled lattice $h\mathbb{Z}^d$ (with transform in spatial frequency $\omega \in \mathbb{R}^d$ and shifts $x \pm he_i$, as on `p. 44`, `p. 77`, `p. 85`) and as a sequence on the integer lattice $\mathbb{Z}^d$ (with transform in dimensionless phase $\vartheta = h\omega$ and unit shifts $n \pm e_i$, as on `pp. 47–48` and `pp. 101–103`). In Proposition 6.15 (`p. 101`), $\Delta_h$ is called *"the $(2d+1)$-point Laplacian on $h\mathbb{Z}^d$"* but is written with unit integer shifts $u(n+e_i)-2u(n)+u(n-e_i)$, and $\kappa_t$ is called *"a probability measure on $\mathbb{Z}^d$ with $\widehat{\kappa}_t(\vartheta) = (1+t^2 D_h(\vartheta))^{-1}$"*, whereas in Proposition 6.18 (`p. 103`) $\kappa_t^9$ has transform written $\widehat{\kappa_t^9}(h\omega) = (1+t^2 D_9(\omega))^{-1}$. Consequently, the proofs on `p. 89`, `p. 94`, and `p. 96` each have to spend a paragraph translating between sequences on $\mathbb{Z}^d$ and measures on $h\mathbb{Z}^d$.
* **Concrete fix:** Fix a single convention at the start of Section 4.2 (`p. 42`) and Section 6 (`p. 83`): a grid kernel on $h\mathbb{Z}^d$ is a measure $w = \sum_{n\in\mathbb{Z}^d} w(n)\,\delta_{hn}$ with weight sequence $w(n)$ on $\mathbb{Z}^d$, spatial Fourier transform $\widehat{w}(\omega) = \sum_{n\in\mathbb{Z}^d} w(n)e^{ih\langle n,\omega\rangle}$, and phase transfer function $\widetilde{w}(\vartheta) = \widehat{w}(\vartheta/h)$ at $\vartheta = h\omega$. State once that convolution on $h\mathbb{Z}^d$ is convolution of the weight sequences $w(n)$ on $\mathbb{Z}^d$, and eliminate the repeated translation paragraphs in Section 6.

---

### 17. Resolve symbol collisions ($D_c / \mathcal{D}_\lambda / D_h / D_5 / D_9$, $L_r$, $\sigma$, and $\mu$) and add a symbol table in Section 2.1.5
* **Page reference:** `pp. 7, 10, 13–15, 26–27, 47, 55, 67, 100, 102` and `Supp. pp. S.15, S.22`.
* **What is wrong:** Several core symbols are overloaded in ways that cause friction across sections:
  * $D$: $D_c\mu$ is measure dilation on $\mathbb{R}^d$ (`p. 13`, while $T_c\mu$ is measure dilation on $\mathbb{R}$), $\mathcal{D}_\lambda f$ is function dilation (`p. 7`), $D$ is the closed unit ball (`pp. 14–15`), $D^k$ is differentiation (`p. 69`), and $D_h(\vartheta), D_5(\omega), D_9(\omega)$ are the Fourier symbols of the discrete Laplacians (`p. 47`, `pp. 100–102`, requiring a disclaimer on `p. 100` that $D_h, D_5, D_9$ are not dilations $D_c$).
  * $L_r$: denotes the Matérn/Laplace probability measure on $\mathbb{R}^d$, its density on $\mathbb{R}$ (`p. 47`), *and* the convolution operator $f \mapsto L_r * f$ (`p. 55`).
  * $\sigma$: $\sigma_{d-1}$ is the *unnormalized* surface measure on $S^{d-1}$ (Definition 2.10, `p. 10`), $\sigma_r$ (and $\sigma_1$) is the *normalized* uniform probability measure on $rS^{d-1}$ (`pp. 26–27, 29`), $\sigma_t(\omega)$ is the symbol of the generator $\mathcal{H}_t$ (Proposition 5.11(1), `p. 67`), $\sigma$ is the random-walk step (`pp. 76, 92, 101`), and in the Supplement $\sigma$ is the cylinder measure (`Supp. p. S.15`).
  * $\mu$: in the main paper $\mu_t$ and $\mu_{s,t}$ are kernels, while in Supplement §S2.2–S2.3 (`Supp. p. S.22`, Definition S.19) unindexed $\mu$ is the *step folded Lévy measure*.
* **Concrete fix:** Add a compact Nomenclature Table in Section 2.1.5 (`p. 14`), rename the discrete Laplacian symbols $D_h, D_5, D_9$ to $s_h, s_5, s_9$ (or $\widehat{\Delta}_h, \widehat{\Delta}_5, \widehat{\Delta}_9$), use $D_c$ for measure dilation in all dimensions (retiring $T_c$), and write $\varpi_{\mathrm{step}}$ instead of $\mu$ for the step folded Lévy measure in Supplement §S2.

---

### 18. Break up the 40–50-line wall-of-text proof paragraphs and display their key intermediate equations
* **Page reference:** `pp. 50–51` (proof of Proposition 4.7(2)), `pp. 59–60` (proof of Theorem 5.4(1) and (3)), `p. 72` (proof of Proposition 5.15(3)), and `p. 77` (proof of Proposition 5.18(3)).
* **What is wrong:** Several major proofs are typeset as unbroken 40-to-50-line paragraphs packed with inline formulas. Most notably, clause (3) of the proof of Proposition 5.15 (`p. 72`) is a single 48-line paragraph spanning almost the entire page, with italicized sub-headers (*Growth.*, *Derivatives.*, *The input.*) embedded mid-line rather than starting new paragraphs. Similarly, the proof of Theorem 5.4(1) (`pp. 59–60`, *"For the mixture..."*) and Step 3 of Proposition 5.18(3) (`p. 77`) pack dense multi-step derivations into inline text.
* **Concrete fix:** Start a new paragraph at every italicized proof step (*Growth*, *Derivatives*, *The input* on `p. 72`; *The mixture*, *The smooth density* on `pp. 59–60`; *Step 1*, *Step 2*, *Step 3* on `p. 77`), and display key intermediate formulas (such as the Faà di Bruno bound and Schwartz multiplier $m(\xi) := e^{\Psi_0(\xi)-2\pi^2\tau|\xi|^2}$ on `p. 72`, and the quadratic test identity $\langle\omega,x\rangle^2 - \sum_{i,j}\omega_i\omega_j x_i x_j = 0$ on `p. 77`).

---

### 19. Add a summary table comparing the three strata in Section 3.2, and improve the legibility and panel alignment of Figure 5
* **Page reference:** `pp. 25–28` (Section 3.2) and `p. 89` (Figure 5).
* **What is wrong:**
  1. The classification into three strata (Theorem 3.11 and Theorem 3.14, `pp. 25–28`) and its grid implications (Sections 4.2 and 6.2) are central to the paper, yet there is no summary table or diagram comparing Strata 1, 2, and 3.
  2. In Figure 5 (`p. 89`), the contour labels (`0.1, 0.3, 0.5, 0.7, 0.9`) and the annotation `$\nu_w(\{5he_1\})/\nu_w(\{(3h,4h)\}) = 1.41$` are printed at a nearly illegible font size. Moreover, the left panel plots the **knot kernel** Lévy measure $\nu_1 = \sum_{m\ge 1} D_{q^{-m}}\nu_w$ of the frame mask (on the dense axes $\bigcup_{m\ge 1} q^{-m}h\mathbb{Z}$), whereas the middle panel plots the **single-step** Lévy measure $\nu_w$ of the 5-point resolvent mask (on $h\mathbb{Z}^2\setminus\{0\}$), an asymmetry that is easy to misread when comparing the two panels visually.
* **Concrete fix:**
  1. Add a 3-row summary table after Theorem 3.14 (`p. 28`) comparing **Stratum 1** ($G=\{1\}$), **Stratum 2** ($G=q^{\mathbb{Z}}$, pyramids), and **Stratum 3** ($G=(0,\infty)$, classical scale space) across: *Scaling of $(A_t,\nu_t)$*, *Kernel law class*, *Continuum witness in $\mathbb{R}^d$*, and *Exact grid-pyramid masks*.
  2. In Figure 5 (`p. 89`), double the font size of the panel titles, axis labels, and contour numbers, and make the panel titles explicit: *"Frame knot kernel $\nu_1$ (atoms on axes $q^{-m}h\mathbb{Z}$)"* vs. *"Five-point step $\nu_w$ (atoms on all of $h\mathbb{Z}^2\setminus\{0\}$)"*.

---

### 20. Fix the placement of Table 3 (floating after the References on page 112) and drop redundant double citations inside proofs
* **Page reference:** `p. 6`, `pp. 35, 59–60, 62, 65`, `pp. 106–112` (Appendix A and Table 3), and `Supp. pp. S.4–S.5, S.39, S.42`.
* **What is wrong:**
  1. In Appendix A (`p. 106`), Table 3 is introduced before Table 4, but in the compiled PDF **Table 3 floats to page 112, after the References** (`pp. 109–111`), while Table 2 and Table 4 appear on `pp. 107–108`. Furthermore, `p. 6` discusses specific rows of Table 3 and Table 4 before any of the paper’s theorems have been stated.
  2. Even though Section 2 restates every cited external fact as a numbered theorem with its source and page number, the proofs in Sections 3–6 and the Supplement repeatedly cite *both* the external source (with page numbers) and the internal theorem number inline, e.g., `by [12, Prop. 3.11(1)–(2), pp. 15–16] (Theorem 2.11)` (`pp. 35, 59, 62`), `by [12, Lem. 3.8, p. 14] (Theorem 2.9)` (`pp. 35, 59`), and `By [28, Thm. 8.1(ii), p. 38] (Theorem 2.17)` (`p. 65`).
* **Concrete fix:**
  1. Force Table 3 to appear on `p. 107` inside Appendix A (before Table 4 and before the References).
  2. Once Section 2 has linked each restated theorem to its external citation and page number, cite only the internal theorem number (e.g., *"by Theorem 2.11"*) inside all subsequent proofs.
