# Verifier verdicts, block s6-7-appendix (opus, condensed)

No SEVERE. No printed statement of § 6 false.

- R5 / §2.2(a) band-limited mask: mathematics CONFIRMED in every step. w(n) = p(n), p = c(F⁻¹ψ)², φ = ψ∗ψ/‖ψ‖², supp φ ⊂ B_r, r ≤ 2π/(q+1); ŵ = φ on [−π,π]^d; μ̂ = Π φ(q^{−m}·); D_qμ = μ∗w; w infinite support, not ID (ŵ has zeros); μ rotation invariant, smooth density. No continuous carrying family (step not ID, Lemma 3.3). Without (b) a jump family exists: μ_{s,t} = ∗_{n: s<qⁿ≤t} D_{q^{n−1}}w, isotropic, jumps at knots. Contradicts no printed sentence: p.87 (finite masks), pp.86–87 (isotropy via family), p.90 (06-price:282-284 already says (d)+(b)), 7.2(4) (finite), 6.16 (finite). Oversells: p.89 (:222-224) and p.104 (:1298-1304) "is the subject of Prop 6.15" — the example is the stronger reason; p.106 (:1424) "The obstruction belongs to the lattice, and the continuum has none" misleading in placement after 6.16. Fix: paper-side sentences at p.89, p.104, p.106, 7.2(4), 7.1; optional print-only remark with the example. r2 settled (4) for finite masks only; infinite case new.
- R3 Table 4 omits 6.6: CONFIRMED. p.115 "every numbered statement"; generator comment only. Lean: skeleton theorem with sorry, nothing imports it. Fix: one sentence in appendix-verification.tex (optionally script emits it).
- R4 Table 3 row 3.20(1),(2): CONFIRMED in substance. ladder_knot_kernel_2 does not state the moment equivalence (ladder_knot_kernel_2_moments reads A49), non-uniqueness, split coupling. Fix: annotate the row, or add _moments row + guard pin.
- R6 contribution 4: PARTLY — not false (scalar 6.5), stale, sends reader to § 7 which answers. 6.6, 6.16 not in contributions. Fix: a sentence or two.
- R1 print Lean statements of axioms: PARTLY, legitimate new request; "do not exist yet" expected (r2 D3).
- R2 abstract: say comparison by AI agents only: PARTLY (said in § 1.1 and AI statement). A clause.
- R7 attribution of criterion at abstract, § 6.3 lead (06-price:691-712), § 7 (07-discussion:12-17): PARTLY. Note: grid criterion step "w ID from continuity" (Lemma 3.3) is not Maejima–Ueda's.
- R8 § 6.4 as known material: SOURCE/PARTLY. No novelty claim; Collatz cited; lattice resolvent/identity/Matérn operators unsourced. D₉ = (2/3)D₅ + (1/3)D_× exact. Lindeberg γ=1/3 SOURCE. r1 declined moving § 6.4.
- R9 § 3.5 items CONFIRMED, all small:
  - p.98 (06-price:825-827) "unique bounded solution (Prop 6.18(1))" — 6.18(1) states summable with δ0; Lean discrete_helmholtz_kernel summable uniqueness (proof uses helm_grid_unique). Strengthen 6.18(1) or reword.
  - p.99-100 (:991-992) "not of the form (6.3)" false at d=1; needs "in d ≥ 2".
  - p.112 (07-discussion:141-142) frame mask claim false at d=1; needs d ≥ 2.
  - p.89 Def 6.3 SO(d) vs Def 3.1 O(d): at d=1 SO(1) trivial. d=1 note.
  - γ ≥ 1 (Def 6.1) vs γ ≥ 0 (6.18(2)) uneven (already known in handoff).
- R10 Thm 2.15 author's own: PARTLY (already said § 1.1 and lead); abstract only. Karlin hypotheses SOURCE.
- S1 one knot lemma for linear M: sound, Lean work.
- S2 argue from one atom: CONFIRMED. Rotation-invariant Lévy measure in d≥2 has no atom off 0. 6.6 does not need "expanding": ν_t ≥ M^{n−1}_*ν_w atom. Strengthening (shared + skeleton).
- S3 criterion independent of q: CONFIRMED. A sentence.
- S4 exact masks violate Burt–Adelson equal contribution: CONFIRMED math (ŵ > 0; w({0}) ≥ e^{−ν(R^d)}; equal contribution ⇔ ŵ = 0 at alias freqs). Paper-side sentence; BA criterion SOURCE.
- S5 operational ID test: CONFIRMED with caveat ŵ > 0. A sentence.
- S6 Prop 6.9(2) under log moment of σ: CONFIRMED, strengthening, shared + Lean (resolvent_masks_exact_2 takes finite support).
- S7 6.16 signed/complex masks: CONFIRMED; novelty SOURCE; Lean rework.
- S8 6.12(1) unused "nonnegative transform" (Lean discards it); 6.12(2) could drop A49 via 6.5(1)+(3). CONFIRMED. Shared + Lean proof edit + Table 4. (handoff already lists creation-grid-masks(1) nonneg transform)
- S9 derive Thm 2.20 from 2.17 (y = Ux); 2.25 third clause from second: CONFIRMED. Lean: cited_A42 becomes theorem; counts ten/fifteen change.
- S10 sphere-uncountability twice (06-price:385-387, 1410-1412) CONFIRMED; moving § 6.4 / senses declined r1.
- S11 § 7 repeats pp. 2–4: deferred r2 D2.
- S12 § 7.2(2) generic example; positive statement holds (coarse max over fine axis nbrs ⇒ u ≤ f by 5.18(2)). A sentence.
- S13 κ_t exponential-time mixture of discrete heat semigroup: math CONFIRMED; Lindeberg link SOURCE.
- S14 p.100 "counting extrema excludes every pyramid whose octave steps are AC": PARTLY, clarifying phrase.
- S16 "family" for Def 6.3 carrier (no ND, no symmetry): CONFIRMED, a word.
- S17 notation overloads M, D, ν_h, t: PARTLY (r1 D3 table).
- S18 footers missing 6.11-6.14, 6.17, 6.20, 6.21: repeat (r1 D4).
- S19 q ≥ 1 in Def 6.10, 6.14(2) (06-price:1021, :1230): harmless; a clause.
- S20 bib: [32] Stein publisher, [36] P. WHITTLE, [17] title "R^n" via {R}{\textasciicircum}n (references.bib:413), [25] arXiv vs journal numbering SOURCE.
- §3.1 remark 3: 6.6 "isotropic" applied to family vs Def 3.1 all-steps notion; a phrase.
- §3.1 remark 4: no carrier for rotating M shown to exist; 6.6 not vacuous (M = qI).
- §3.3 Prop 6.5 opening irrelevant to clause (3); a sentence.
- §5.5 Def 6.2 formal counterparts unstated; creation_plane_3 hypothesis IsMaternPyramid (as F1). A sentence in Appendix A.

Needs held copy: Simoncelli–Freeman 1995; Lindeberg 1990 TPAMI γ=1/3; Van De Ville–Blu–Unser 2005; CDM 1991 finite mask radial; Burt–Adelson 1983 p.533 / Burt 1981 pp.23-24 equal contribution; Meer–Baugher–Rosenfeld 1987; Maejima–Ueda journal numbering; Maejima–Sato 1999 epochs; Sato Thm 9.1, 17.5; Scherzer–Weickert JMIV 2000; Alvarez–Mazorra 1994 / Deriche recursion; Weickert–ter Haar Romeny–Viergever 1998 AOS; Lindgren–Rue–Lindström, Whittle, Besag lattice precision; Karlin Ch5 Thm 3.1; Stein 1970 publisher.
