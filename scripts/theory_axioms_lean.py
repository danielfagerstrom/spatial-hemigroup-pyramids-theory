r"""The supplement's section on the admitted facts in Lean, generated from the Lean source.

Decision D1 of the theory paper's review round 3 (records/pyramids/PLAN-review-response-theory-
round3.md): print the Lean statements of the axioms, so that the trust base can be read without
the code. This script reads the admitted names from blueprint/trust-boundary.txt (with the ledger
entry each belongs to, from the `# A<n> -- ...` comment above it), finds each `axiom` in the
formal development or in the affine export it imports, and prints its statement as the source
has it. It also prints the definitions of this project and of the export that the axioms name
(DEFINITIONS below; Mathlib's are not printed). Run it on the laptop or the VM, from any checkout
whose `Formalization/.lake/packages/AffineHemigroup` holds the export's source:

  python scripts/theory_axioms_lean.py > paper/supp-axioms-lean.tex
  python scripts/theory_axioms_lean.py --unicode > paper/supp-axioms-unicode.tex

It fails on an admitted name it cannot find, on a definition it cannot find, and on a character
outside UNICODE (add the character there, with its LaTeX). Regenerate after any change to an
axiom, to trust-boundary.txt, or to a definition listed here.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
FORMAL = ROOT / "Formalization"
PROJECT = FORMAL / "Pyramids"
EXPORT = FORMAL / ".lake" / "packages" / "AffineHemigroup" / "Formalization" / "AffineHemigroup"
CORE = FORMAL / ".lake" / "packages" / "ScaleSpaceCore" / "ScaleSpaceCore"
ROOTS = {"Pyramids": PROJECT, "AffineHemigroup": EXPORT, "ScaleSpaceCore": CORE}
BOUNDARY = ROOT / "blueprint" / "trust-boundary.txt"

# The definitions the axioms name, in the order a reader needs them: (namespace, name).
DEFINITIONS = [
    ("AffineHemigroup", "Rd", None),
    ("AffineHemigroup", "IsInfinitelyDivisible", None),
    ("AffineHemigroup", "LevyTriplet", None),
    ("AffineHemigroup", "HasTriplet", None),
    ("AffineHemigroup", "IsSelfDecomposableSato", None),
    ("Pyramids", "IsSDResidual", None),
    ("Pyramids", "IsSemiSelfDecomposableWithSpan", None),
    ("Pyramids", "IsSemiSelfDecomposable", None),
    ("Pyramids", "IsSubmultiplicative", None),
    ("ScaleSpaceCore", "SDProfile", None),
    ("ScaleSpaceCore", "exponentL", "namespace SDProfile"),
    ("ScaleSpaceCore", "exponent", "namespace SDProfile"),
    ("ScaleSpaceCore", "IsAdmissibleExponent", None),
    ("ScaleSpaceCore", "mconv", None),
    ("Pyramids", "essSignChanges", None),
    ("Pyramids", "IsPolyaFrequencyKernel", None),
    ("Pyramids", "IsPolyaFrequencyDensity", None),
    ("ScaleSpaceCore", "polyaE2", None),
]

# Each character outside ASCII that the printed Lean may contain, and how LaTeX prints it.
UNICODE = {
    "ℝ": r"\ensuremath{\mathbb{R}}", "ℕ": r"\ensuremath{\mathbb{N}}", "ℤ": r"\ensuremath{\mathbb{Z}}",
    "ℂ": r"\ensuremath{\mathbb{C}}", "ℚ": r"\ensuremath{\mathbb{Q}}",
    "∀": r"\ensuremath{\forall}", "∃": r"\ensuremath{\exists}", "→": r"\ensuremath{\to}",
    "↦": r"\ensuremath{\mapsto}", "↔": r"\ensuremath{\leftrightarrow}", "←": r"\ensuremath{\leftarrow}",
    "≤": r"\ensuremath{\le}", "≥": r"\ensuremath{\ge}", "≠": r"\ensuremath{\ne}",
    "∫": r"\ensuremath{\int}", "∂": r"\ensuremath{\partial}", "•": r"\ensuremath{\bullet}",
    "∑": r"\ensuremath{\sum}", "∏": r"\ensuremath{\prod}", "∈": r"\ensuremath{\in}",
    "∉": r"\ensuremath{\notin}", "∧": r"\ensuremath{\wedge}", "∨": r"\ensuremath{\vee}",
    "¬": r"\ensuremath{\neg}", "∘": r"\ensuremath{\circ}", "×": r"\ensuremath{\times}",
    "·": r"\ensuremath{\cdot}", "⊆": r"\ensuremath{\subseteq}", "⊂": r"\ensuremath{\subset}",
    "∩": r"\ensuremath{\cap}", "∪": r"\ensuremath{\cup}", "∅": r"\ensuremath{\emptyset}",
    "⊤": r"\ensuremath{\top}", "⊥": r"\ensuremath{\bot}", "∞": r"\ensuremath{\infty}",
    "≃": r"\ensuremath{\simeq}", "≫": r"\ensuremath{\gg}", "⁻": r"\ensuremath{^{-}}",
    "¹": r"\ensuremath{^{1}}", "²": r"\ensuremath{^{2}}", "ᶜ": r"\ensuremath{^{c}}",
    "ᵀ": r"\ensuremath{^{T}}", "‖": r"\ensuremath{\Vert}", "⟨": r"\ensuremath{\langle}",
    "⟩": r"\ensuremath{\rangle}", "⟪": r"\ensuremath{\langle\!\langle}",
    "⟫": r"\ensuremath{\rangle\!\rangle}", "⁅": r"[", "⁆": r"]", "⌊": r"\ensuremath{\lfloor}",
    "⌋": r"\ensuremath{\rfloor}", "∣": r"\ensuremath{\mid}", "≢": r"\ensuremath{\not\equiv}",
    "α": r"\ensuremath{\alpha}", "β": r"\ensuremath{\beta}", "γ": r"\ensuremath{\gamma}",
    "δ": r"\ensuremath{\delta}", "ε": r"\ensuremath{\varepsilon}", "ζ": r"\ensuremath{\zeta}",
    "η": r"\ensuremath{\eta}", "θ": r"\ensuremath{\theta}", "ι": r"\ensuremath{\iota}",
    "κ": r"\ensuremath{\kappa}", "λ": r"\ensuremath{\lambda}", "μ": r"\ensuremath{\mu}",
    "ν": r"\ensuremath{\nu}", "ξ": r"\ensuremath{\xi}", "π": r"\ensuremath{\pi}",
    "ρ": r"\ensuremath{\rho}", "σ": r"\ensuremath{\sigma}", "τ": r"\ensuremath{\tau}",
    "φ": r"\ensuremath{\varphi}", "χ": r"\ensuremath{\chi}", "ψ": r"\ensuremath{\psi}",
    "ω": r"\ensuremath{\omega}", "Γ": r"\ensuremath{\Gamma}", "Δ": r"\ensuremath{\Delta}",
    "Λ": r"\ensuremath{\Lambda}", "Φ": r"\ensuremath{\Phi}", "Ψ": r"\ensuremath{\Psi}",
    "Ω": r"\ensuremath{\Omega}", "ℓ": r"\ensuremath{\ell}",
    "é": r"\'e", "ᵇ": r"\ensuremath{^{b}}", "ᵐ": r"\ensuremath{^{m}}", "₀": r"\ensuremath{_{0}}",
    "₁": r"\ensuremath{_{1}}", "∗": r"\ensuremath{\ast}", "⨅": r"\ensuremath{\textstyle\bigwedge}",
    "⨆": r"\ensuremath{\textstyle\bigvee}", "𝓝": r"\ensuremath{\mathcal{N}}",
}

WORDS = ["no", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten",
         "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen", "seventeen", "eighteen"]


# The cited fact of each ledger entry, as the paper labels it.
def label(entry):
    return "thm:cited-" + entry


def admitted():
    """(ledger entry, full name) for each admitted name, in the file's order."""
    out, entry = [], None
    for line in BOUNDARY.read_text(encoding="utf-8").splitlines():
        m = re.match(r"#\s*(A\d+)\s+--", line)
        if m:
            entry = m.group(1)
            continue
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        if entry is None:
            sys.exit(f"theory_axioms_lean: no ledger entry above {s}")
        out.append((entry, s))
    return out


def sources(namespace):
    root = ROOTS[namespace]
    if not root.is_dir():
        sys.exit(f"theory_axioms_lean: {root} is missing (archive the package sources first)")
    return sorted(root.rglob("*.lean"))


STOP = re.compile(r"^(/--|/-|theorem |lemma |def |noncomputable |abbrev |structure |class |"
                  r"instance |axiom |end |namespace |section |variable |open |@\[|#)")


def block(path, lines, start):
    """The declaration starting at lines[start], to the line before a blank line or the next one."""
    out = [lines[start]]
    for line in lines[start + 1:]:
        if not line.strip() or STOP.match(line):
            break
        out.append(line)
    if PROJECT in path.parents:
        base = FORMAL
    elif EXPORT in path.parents:
        base = EXPORT.parent.parent
    else:
        base = CORE.parent
    return "\n".join(out).rstrip(), path.relative_to(base).as_posix()


def find(namespace, name, kinds, anchor=None):
    pat = re.compile(r"^(?:noncomputable\s+)?(?:" + "|".join(kinds) + r")\s+" + re.escape(name)
                     + r"(?:\s|$|\{|\(|\[|:)")
    for path in sources(namespace):
        lines = path.read_text(encoding="utf-8").splitlines()
        first = 0
        if anchor is not None:
            hits = [i for i, line in enumerate(lines) if line.strip() == anchor]
            if not hits:
                continue
            first = hits[0]
        for i, line in enumerate(lines):
            if i >= first and pat.match(line):
                return block(path, lines, i)
    sys.exit(f"theory_axioms_lean: {namespace}.{name} not found")


def tex_verbatim(text):
    return "\\begin{verbatim}\n" + text + "\n\\end{verbatim}\n"


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    axioms =[(e, n, *find(n.split(".")[0], n.split(".", 1)[1], ["axiom"])) for e, n in admitted()]
    shown = {"Pyramids": "Pyramids", "AffineHemigroup": "AffineHemigroup", "ScaleSpaceCore": "ScaleSpace"}
    defs = [((shown[ns] + ".SDProfile") if anchor else shown[ns], n,
             *find(ns, n, ["def", "abbrev", "structure", "class"], anchor))
            for ns, n, anchor in DEFINITIONS]

    chars = set()
    for item in axioms + defs:
        chars |= {c for c in item[2] if ord(c) > 127}
    unknown = sorted(c for c in chars if c not in UNICODE)
    if unknown:
        sys.exit("theory_axioms_lean: characters without a LaTeX form: " + " ".join(unknown))

    entries = []
    for e, _, _, _ in axioms:
        if e not in entries:
            entries.append(e)

    w = sys.stdout.write
    w("% Generated by scripts/theory_axioms_lean.py from the Lean source; do not edit by hand.\n")
    if "--unicode" in sys.argv:
        w("% The preamble's map of the Unicode characters that supp-axioms-lean.tex prints.\n")
        for c in sorted(chars):
            w(f"\\newunicodechar{{{c}}}{{{UNICODE[c]}}}\n")
        return
    w("% Decision D1 of review round 3: the admitted facts' Lean statements in print.\n")
    w("\\section{The admitted facts in Lean}\n\\label{supp:axioms}\n\n")
    w(f"This section prints the {WORDS[len(axioms)]} axioms of the formal development, grouped by "
      f"the {WORDS[len(entries)]} cited facts of the paper that they state (Section~\\ref{{sec:trust}} and "
      "Table~\\ref{tab:axioms} of the paper), as the Lean source has them. "
      f"{WORDS[sum(n.startswith('AffineHemigroup.') for _, n, _, _ in axioms)].capitalize()} of "
      "them live in the "
      "affine paper's export \\texttt{AffineHemigroup}, which the development imports, and the "
      "others in \\texttt{Pyramids}. The definitions of the two developments that the axioms name follow "
      "them, with those of the shared core \\texttt{ScaleSpaceCore}; the rest is Mathlib's. The "
      "script \\nolinkurl{scripts/theory_axioms_lean.py} writes this section from the source, so "
      "that what is printed is what Lean reads.\n\n{\\raggedright\n")
    for e in entries:
        group = [a for a in axioms if a[0] == e]
        names = "; ".join("\\nolinkurl{" + n + "} in \\nolinkurl{" + rel + "}"
                          for _, n, _, rel in group)
        w(f"\\paragraph{{Theorem\\nobreakspace\\ref{{{label(e)}}}.}} {names}.\n")
        w("{\\scriptsize\n" + "".join(tex_verbatim(a[2]) for a in group) + "}\n\n")
    w("\\subsection{The definitions the axioms name}\n\n")
    for ns, n, text, rel in defs:
        w(f"\\paragraph{{\\nolinkurl{{{ns}.{n}}}}} in \\nolinkurl{{{rel}}}.\n")
        w("{\\scriptsize\n" + tex_verbatim(text) + "}\n\n")
    w("}\n")


if __name__ == "__main__":
    main()
