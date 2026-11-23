r"""Appendix A's per-statement table of the theory paper, from Lean's `#print axioms`.

Two steps, the first run where the Lean project is built (the VM):

  linkage check --emit-manifest /tmp/manifest.json
  python scripts/theory_axioms_table.py lean /tmp/manifest.json > /tmp/TheoryAxioms.lean
  (cd Formalization && lake env lean /tmp/TheoryAxioms.lean) > /tmp/theory-axioms.out 2>&1
  python scripts/theory_axioms_table.py table /tmp/manifest.json /tmp/theory-axioms.out \
      > paper/appendix-axioms-table.tex

`lean` writes a file printing the axioms of every declaration that a `\leanok` statement of the
theory paper (the nodes printed under a `% shared with blueprint` marker in paper/) names in its
`\lean{}` tag. `table` reads Lean's output, maps each axiom to its cited fact (Appendix A's
Table tab:axioms; any other axiom but Lean's three is an error), and writes one row per section
and set of cited facts, listing the statements that read exactly that set.
"""
import json
import os
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"

# The paper file each statement prints in, in reading order, and how the table names it.
SECTIONS = [
    ("02-cited-facts.tex", "2"),
    ("03-pyramid.tex", "3"),
    ("04-line.tex", "4"),
    ("05-matern.tex", "5"),
    ("06-price.tex", "6"),
    ("supp-strata.tex", "S1"),
    ("supp-line.tex", "S2"),
]

LOGICAL = {"propext", "Classical.choice", "Quot.sound"}
ENTRY = {
    "AffineHemigroup.levy_khintchine_exists": "A39",
    "AffineHemigroup.levy_khintchine_unique": "A39",
    "AffineHemigroup.levy_khintchine_converse": "A39",
    "AffineHemigroup.khintchine_null_array": "A41",
    "Pyramids.cited_A42": "A42",
    "AffineHemigroup.selfDecomposable_infinitelyDivisible": "A43",
    "Pyramids.cited_A43_residual_infinitelyDivisible": "A43",
    "Pyramids.cited_A43_semi_infinitelyDivisible": "A43",
    "AffineHemigroup.sato_polar_criterion": "A45",
    "Pyramids.cited_A46": "A46",
    "Pyramids.cited_A48": "A48",
    "Pyramids.cited_A49": "A49",
    "Pyramids.cited_A22_polya": "A22",
    "Pyramids.cited_A22_variation": "A22",
    "Pyramids.cited_A24": "A24",
}
KIND = {"theorem": "Theorem", "proposition": "Proposition", "lemma": "Lemma",
        "corollary": "Corollary", "definition": "Definition"}
KINDS_PL = {"Theorem": "Theorems", "Proposition": "Propositions", "Lemma": "Lemmas",
            "Corollary": "Corollaries", "Definition": "Definitions"}


def printed_labels():
    """[(label, section)] in the order the paper prints them; first print wins."""
    seen, out = set(), []
    for fname, sec in SECTIONS:
        text = (PAPER / fname).read_text(encoding="utf-8")
        for m in re.finditer(r"^% shared with blueprint (.+)$", text, re.M):
            for lab in m.group(1).split():
                lab = lab.strip(",")
                if lab not in seen and re.match(r"^(thm|prop|lem|cor|def):", lab):
                    seen.add(lab)
                    out.append((lab, sec))
    return out


def nodes(manifest):
    labels = json.loads(pathlib.Path(manifest).read_text(encoding="utf-8"))["labels"]
    rows = []
    for lab, sec in printed_labels():
        n = labels.get(lab)
        if n is None:
            sys.exit(f"{lab}: printed in the paper but not in the manifest")
        rows.append((lab, sec, n))
    return rows


def cmd_lean(manifest):
    decls = []
    for lab, _, n in nodes(manifest):
        if n.get("leanok") and n.get("lean"):
            decls += [d for d in n["lean"] if d not in decls]
    print("import Pyramids\n")
    for d in decls:
        print(f"#print axioms {d}")


def parse_axioms(text):
    out = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S):
        out[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        out[m.group(1)] = []
    return out


def entry_key(e):
    return int(e[1:])


def cmd_table(manifest, leanout):
    axioms = parse_axioms(pathlib.Path(leanout).read_text(encoding="utf-8"))
    printed = [lab for lab, _ in printed_labels()]

    def printed_at(entry):
        # The cited facts in the order Section 2 prints them, so their numbers increase.
        lab = f"thm:cited-{entry}"
        return printed.index(lab) if lab in printed else len(printed) + entry_key(entry)

    groups, order, skipped = {}, [], []
    for lab, sec, n in nodes(manifest):
        if not (n.get("leanok") and n.get("lean")):
            skipped.append(lab)
            continue
        cited = set()
        for d in n["lean"]:
            if d not in axioms:
                if os.environ.get("THEORY_AXIOMS_PARTIAL"):
                    print(f"% MISSING {lab}: {d}")
                    continue
                sys.exit(f"{lab}: no #print axioms output for {d}")
            for a in axioms[d]:
                if a in LOGICAL:
                    continue
                if a not in ENTRY:
                    sys.exit(f"{lab}: {d} depends on {a}, which is no admitted axiom")
                cited.add(ENTRY[a])
        key = (sec, tuple(sorted(cited, key=entry_key)))
        if key not in groups:
            groups[key] = []
            order.append(key)
        groups[key].append((KIND[n["env"]], lab))
    print("% Generated by scripts/theory_axioms_table.py from `#print axioms`; do not edit by hand.")
    if skipped:
        print("% Printed statements with no \\leanok declaration: " + ", ".join(skipped) + ".")
    order.sort(key=lambda k: ([s for _, s in SECTIONS].index(k[0]), len(k[1]), k[1]))
    for sec, cited in order:
        by_kind = {}
        for kind, lab in groups[(sec, cited)]:
            by_kind.setdefault(kind, []).append(lab)
        parts = []
        for kind in ("Definition", "Lemma", "Proposition", "Theorem", "Corollary"):
            labs = by_kind.get(kind)
            if not labs:
                continue
            name = kind if len(labs) == 1 else KINDS_PL[kind]
            parts.append(name + "~" + ", ".join(f"\\ref{{{lab}}}" for lab in labs))
        refs = [f"\\ref{{thm:cited-{e}}}" for e in sorted(cited, key=printed_at)]
        facts = ("none" if not refs else
                 ("Theorem~" if len(refs) == 1 else "Theorems~") + ", ".join(refs))
        print(f"{sec} & {facts} & {'; '.join(parts)} \\\\")


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "lean":
        cmd_lean(sys.argv[2])
    elif len(sys.argv) == 4 and sys.argv[1] == "table":
        cmd_table(sys.argv[2], sys.argv[3])
    else:
        sys.exit(__doc__)
