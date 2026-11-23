# Verifier verdicts, block s4-5 (opus, condensed). Recomputations in scratchpad/v45/.

No error in any numbered statement or proof.

- R2 singular kernels: CONFIRMED. For integer q, μ̂₁(2πq^k/h) = μ̂₁(2π/h) ≠ 0 (0.040876 at q=2, a=e⁻¹; 0.17590 at q=3) ⇒ not AC (Riemann–Lebesgue). Singular by Kolmogorov 0–1 on the countable group G = hℤ[1/q] (tail event {X ∈ N+G}); no source needed. All μ_t, t>0 singular (μ_{q^n,t} compound Poisson on q^n hℤ times δ_b). Atomless needs Sato Thm 27.4 (SOURCE), not needed. Integer q only. Text: p.35 (03-pyramid:1172) "an implemented pyramid samples them on grids" and p.45 (04-line:240-244) same clause unconditional; false on the line for exact grid pyramids. "Singular" nowhere in paper. Fix: paper-side sentences at both; optional remark/numbered statement (print only or Lean).
- R5 Figure 4 caption (05-matern:1476, p.78) "a = 5/2 meets the proof's condition": CONFIRMED wrong. Proof: r with W < W(0)/4 off B_r, a := r+1. L₁ in plane: W(0)=0.461455, W(1.5)/W(0)=0.537117, W = W(0)/4 at r=2.33082 ⇒ a=r+1 needs a ≥ 3.331. Argument only uses a > r, so 5/2 works with r ∈ [2.331, 2.5). δ: ridge 0.6101 at δ=1/100 vs W(0)/4=0.1154; met at δ≈0.0019; "proof takes δ smaller" right. Fix: caption sentence.
- R6 p.66 (05-matern:612-627, :621-622) "squared modulus of the transform of his kernel": CONFIRMED mismatch: subordination reading has time constants 2c²q^{−2i} (ratio q²); |1+icq^{−i}r|^{−2} is the member with time constants cq^{−i}, ratio q. On the line μ_t = Ψ∗Ψ(−·), Ψ limit kernel of time constants ctq^{−i}. Fix: one clause naming the member. "S-p.39 same paragraph" WRONG. Intro precedent: author's call.
- R4 p.111 (07-discussion:41-42) "On the line the count of local extrema gives that reason [11, §4]": CONFIRMED unsupported for stratum 2 ([11] selects among fully covariant; S.37 sufficiency for a class). Fix: one sentence.
- R1 ŵ>0 excludes Burt equal contribution: CONFIRMED math (ŵ(π/h) = 0.2136 at a=e⁻¹); not stated (S-p.35 supp-line:2109-2113 describes it). Fix: sentence at S-35, Prop 4.5 lead, § 7.1; optional clause in 4.5(1)/6.8(1).
- R3 selection qualifications missing from headlines: PARTLY. Body states: 5.18 equivalence (p.80), 5.19(3) only λ=q, 5.20(2), 5.4(5), p.79 two forms select differently / rejects Gaussian. Not in abstract, contribution 3, § 7.1. Paper-side clauses.
- R7 Maejima–Ueda at abstract, contribution 2, Prop 4.5 lead (p.46): PARTLY (pp.5,35 have it). Paper-side.
- §2.3 "exact" in abstract is sense (iii) only: editorial phrase.
- §2.4 Prop 3.22 headline without sources: editorial.
- R8 general 2-D non-creation at Lindeberg 1994 §4.1 p.101 (records/pyramids/READING-lindeberg1994scale.md:12 "Lifshitz–Pizer"): SOURCE; p.5 cites page only for Gaussian. Sentence.
- R9 attribution non-enhancement / regularization-as-diffusion: PARTLY; Scherzer–Weickert 2000, Nielsen–Florack–Deriche 1997 held, read, not in bib; Alvarez readings exist. SOURCE for extremum principle.
- R10 two-pass recursion classical: CONFIRMED by held records (READING-shen1992optimal.md pp.121-122 ISEF, a₀=(1−b)/(1+b); READING-unser1991recursive.md p.273) not cited. Inusah–Kozubowski not held. Bib + sentences.
- R11 senses of exact: mostly ALREADY-DECIDED (r1 B4/D2). New: Def 6.2(1) (06-price:133-135) "the kernels they stand for" doesn't name the reference; 6.14(2) and 4.7(2) use two references. Shared clause.
- R12 S.34–S.37 into main text: ALREADY-DECIDED (r1 R12, adr 0007/0008).
- R13 p.112 answer 2 "in d ≥ 2" missing: CONFIRMED (also s6-7 R9). "Prop 5.21 uses no property of the resolvent": PARTLY; generalization holds (any mask with summable inverse having a negative weight off coarse lattice).
- R14 "Measured: the size of the error" (04-line:932, p.55): PARTLY; say why V_n is the reference. Sentence.
- R15 "can rise at every rung" without "for an input that depends on the rung" at p.74 (05-matern:1244), p.100 (06-price:1002), p.112 (07-discussion:89): CONFIRMED ambiguity. Phrase ×3.
- R16 Table 4 5.11, 5.15 "none": WRONG as anomaly (family as hypothesis, as F1). One Appendix A sentence. Footers repeat r1 D4.
- R17 repo availability: not a finding (r2 D3).
- S1 restructure 5.15: editorial (clause (2) used by none).
- S2 5.21 as remark: editorial, repeats r2 choice.
- S3 level-set reading: CONFIRMED, remark.
- S4 explicit variant only δ₀: CONFIRMED first part.
- S5 grid converse sufficiency CONFIRMED; necessity unproved.
- S6 direct construction of Matérn: PARTLY (saving smaller: Thm 2.9 uses no cited fact; facts via 2.11).
- S7, S8: ALREADY-DECIDED (r1 B10, B14, adr 0008).
- S9 notation renames: partly decided (r1 B17, D3); "stage" third word p.79.
- S10 Table 1 extensions: all 12 entries reproduce; q=3 and h/(ct)=√2 values computed (v45). Optional.
- S11 λ_{s,t}, 0<s<t, not PF: CONFIRMED (Edrei form SOURCE). Remark.
- S12 cite Crowley, Lowe, Lindeberg 2024 etc.: SOURCE.
- S13 classical singular ID laws: SOURCE, optional.
- S14 Def 5.1: octave step not Matérn covariance: PARTLY (p.58 already says γ > d/2); "no μ_t is a Matérn law" true, unstated. Sentence.
- S16 small repairs in shared proofs, CONFIRMED minor: Kρ_δ "pointwise"; g_Σ undefined (05-matern:1409-1411); "By that lemma with χ = id" (p.63) → Thm 2.9; 5.19(3) "At u = 1 and u = 2"; c reused in 5.15(5) proof; Lemma 5.3 "one cited fact DLMF 10.32.10 (Thm 2.33)" vs Table 4 "none".
- S17 p.49 "rescaled to the finest grid" (04-line:510; blueprint 02-line:1390): CONFIRMED, a phrase.
- S18 Thm 2.15 "essential sense": SOURCE (Karlin).

Needs held copy: Sato §27 (Thm 27.4, Hartman–Wintner); Jessen–Wintner 1935; Lindeberg 2016 p.63 (41)-(44); Lindeberg 1994 §4.1 p.101 and p.80 Thm 3.16; Karlin Ch5 Thm 3.1; Burt–Adelson 1983 p.533; Scherzer–Weickert 2000 §§3.2–6; Alvarez–Guichard–Lions–Morel 1993; Inusah–Kozubowski 2006 (not held); Becker-Kern; Lowe 2004, Lindeberg 2024, Burgeth–Didas–Weickert, Lindeberg–Bretzner 2003; Vervaat 1979 (held).
