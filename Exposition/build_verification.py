#!/usr/bin/env python3
"""Assemble Exposition/Verification.md from the per-chapter sections in Exposition/verification/.

Each section file `chNN.md` starts with a heading `## Chapter N (HWZ …): status`, contains V-items,
a `### What is not verified in this chapter` list and a `### Sign-off items` list. The assembler
numbers the sections, moves every sign-off list to a final numbered sign-off section, adds the
summary table (Lean lines per chapter directory, counted with `wc -l`), and builds `Verification.pdf`
through pandoc and xelatex when both are installed (otherwise the PDF step is skipped with a message).

Usage: python3 build_verification.py
"""
import datetime, glob, os, re, shutil, subprocess, sys

# ---- project configuration -------------------------------------------------------------------
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)                 # the project folder
LIB = "Polyfold"                             # the Lean library root inside it
SEC = os.path.join(HERE, "verification")
OUT_MD = os.path.join(HERE, "Verification.md")
OUT_PDF = os.path.join(HERE, "Verification.pdf")
BOOK_SHORT = "HWZ"
TEST_FILE = f"{LIB}/Test.lean"
PDF_ARGS = [  # the same pandoc settings as the chapters
    "--pdf-engine=xelatex",
    "-V", "mainfont=Palatino", "-V", "mathfont=latinmodern-math.otf",
    "-V", "geometry:margin=1in", "-V", "papersize=letter", "-V", "fontsize=11pt",
    "-V", "colorlinks=true", "-V", "linkcolor=blue", "-V", "urlcolor=blue",
    "-V", "header-includes=\\usepackage{amssymb}\\usepackage{float}\\floatplacement{figure}{H}",
    "--resource-path", HERE,
]
CHAPTERS = [  # file key, HWZ sections, short content (for the summary table), Lean dirs
    ("01", "Ch. 1, §§1.1–1.4", "sc-Banach spaces, sc-operators and sc-Fredholm operators, sc-differentiability "
     "and its relation to classical differentiability, the chain rule, the degeneracy index", ["Chapter1"]),
    ("02", "Ch. 2", "sc-smooth retractions and retracts, M-polyfolds, the degeneracy index, tame M-polyfolds, "
     "strong bundles", ["Chapter2"]),
    ("03", "Ch. 3", "sc-Fredholm sections and the implicit function theorem", ["Chapter3"]),
    ("04", "Ch. 4, §§4.1–4.4", "manifolds with boundary with corners: sc⁺-retracts and the characterization, smooth "
     "finite-dimensional submanifolds, families and Sard's theorem (vendored)", ["Chapter4", "Vendor/MilnorSard"]),
    ("05", "Ch. 5, §§5.1–5.4", "the Fredholm package for M-polyfolds: auxiliary norms, compactness, sc⁺-sections and "
     "bump functions, transversality, general and good position, homotopies, partitions of unity", ["Chapter5"]),
    ("06", "Ch. 6, §§6.1–6.5, 6.7", "linearizations and orientations: determinant lines and exact sequences, the "
     "determinant of a Fredholm operator, good left-projections, stabilization, the determinant line bundle, the "
     "propagation of orientations along paths, orientable and oriented sc-Fredholm sections, the orientation of "
     "the solution set", ["Chapter6"]),
    ("07", "Part II, Ch. 7, §§7.1–7.5 (2017 numbering)", "ep-groupoids: groupoids of M-polyfolds with local "
     "sc-diffeomorphisms as source and target and a local properness, the orbit space, the natural representation "
     "of the isotropy groups, local uniformizers, ep-subgroupoids, effective and reduced ep-groupoids, the topology "
     "of the orbit space, index lifts, invariant sc-smooth partitions of unity, proper subsets", ["Chapter7"]),
]
# ------------------------------------------------------------------------------------------------

INTRO = r"""# Polyfold Theory, verified: the machine-checked edition

*A companion to the expanded exposition of Part I, and of Chapter 7 of Part II, of H. Hofer, K. Wysocki and
E. Zehnder's* Polyfold and Fredholm Theory *(Springer 2021; for Part I the 2014 preprint arXiv 1407.3185 is the
text in hand, and its numbering and pages are used, marked as such; the numbers and pages of the book's arXiv
version, 1707.08941, are in `Exposition/BookConcordance.md`. Part II has no preprint: for it the 2017 arXiv
version is the text, and its numbers and printed pages are the only numbering used. The Springer edition is not
checked). That exposition is
written to be read; this edition is written to be checked. It records, chapter by chapter, exactly
which statements of the text have been verified by the Lean 4 proof assistant against the Mathlib
library, what each verified statement says when read back in ordinary language, which hypotheses the
text left silent, where the formal statement or proof departs from the text's, and what remains
unverified and why. Nothing here needs to be read in Lean; every checked statement is restated in
prose, and the Lean names are given only so that the claims can be audited.*

**Where to start.** The project has three parts:

- the expanded exposition (`Exposition/Chapter1.md`, …), the book for reading;
- *Polyfold Theory, Checked*, the Lean formalization (`Polyfold/`) and the reports on it;
- the sign-off page, the list of statements a reader is asked to confirm.

This edition is the way into the second part. Its reports each answer one question:

- **What is proved?** This edition: every checked result in plain language, with all its
  hypotheses, and the list of statements to sign off.
- **How is it proved?** *Polyfold Theory, proof by proof* (`Exposition/ProofByProof.md`): the formal
  proofs retold as mathematics, with a trace tag on each step naming the Lean declaration that
  carries it.
- **How does it differ from the text?** *Polyfold Theory beside Lean*, the comparison
  (`Exposition/polyfold-beside-lean.html`): each result of the book beside the checked statement, with
  a verdict (the same, restated, hypotheses made explicit, stronger, narrower) and the differences.

A result has the same number, V1.5 say, in this edition, the comparison and the sign-off page.

---
"""

HOWTO = r"""## 1. How to read a verified statement

**The statements are the contract.** A machine-checked proof guarantees that the *stated* theorem
follows from Lean's axioms. It guarantees nothing about whether the statement is the one the authors
meant. The reader's job, and the only mathematical judgement this document asks for, is to read
each prose restatement and confirm that it says what the text means. Where the restatement is
weaker or stronger than the text, or uses a different but equivalent definition, this is flagged as
a **Deviation**.

**The setting.** An sc-Banach space is formalized as an indexed family of real Banach spaces $E_m$,
$m \ge 0$, with injective compact continuous linear inclusions $E_{m+1} \to E_m$ and the smooth
points dense in every level; the text's subspace picture $E_0 \supset E_1 \supset \cdots$ is
recovered by identifying $E_m$ with its image in $E_0$, and "$x \in E_m$" for $x \in E_0$ means
that $x$ is in that image. A map $f : U \to F$ on a subset $U \subseteq E_0$ is a total function
$E_0 \to F_0$ whose values off $U$ play no role; its level maps $f_m : U_m \to F_m$ are determined
by the injectivity of the inclusions. "Relatively open in a partial quadrant" enters most theorems
only through its consequences on each level, that $U_m$ is the intersection of an open and a convex
set and has unique differentiability at each of its points (an *sc-domain*); whenever the text's
hypothesis is replaced by this weaker one the item says so.

**Classical differentiability.** $C^k$ on a relatively open subset of a partial quadrant means
Mathlib's $C^k$ *within the set*, with derivatives within the set; on these sets derivatives are
unique, so the notion agrees with the exposition's Definition 3.C.

**Axioms.** Every verified theorem depends only on the three standard axioms of Lean's Mathlib
(`propext`, `Classical.choice`, `Quot.sound`), as `TEST_FILE` prints; there is no `sorry`.
""".replace("TEST_FILE", TEST_FILE)


def lean_lines(dirs):
    files = []
    for d in dirs:
        files += [f for f in glob.glob(os.path.join(ROOT, LIB, d, "*.lean"))
                  if not os.path.basename(f).startswith("WIP_")]
    return sum(sum(1 for _ in open(f, encoding="utf-8")) for f in files), len(files)


def toolchain():
    try:
        return open(os.path.join(ROOT, "lean-toolchain"), encoding="utf-8").read().strip().split(":")[-1]
    except OSError:
        return "?"


def main():
    body, signoffs, rows = [], [], []
    k = 2
    for key, secs, content, dirs in CHAPTERS:
        path = os.path.join(SEC, f"ch{key}.md")
        lines, nfiles = lean_lines(dirs)
        chap = f"Chapter {int(key)}"
        if not os.path.exists(path):
            rows.append(f"| {chap} | {secs} | {content} | not verified | {lines:,} |" if lines else
                        f"| {chap} | {secs} | {content} | not verified | — |")
            continue
        text = open(path, encoding="utf-8").read().strip()
        head = re.match(r"##\s+(.*)", text)
        status = head.group(1).split(":")[-1].strip() if head else "verified"
        rows.append(f"| {chap} | {secs} | {content} | **{status}** | {lines:,} |")
        m = re.search(r"^###\s+Sign-off items\s*\n(.*?)(?=^##\s|\Z)", text, re.S | re.M)
        if m:
            items = re.findall(r"^\d+\.\s+(.*?)(?=^\d+\.\s|\Z)", m.group(1), re.S | re.M)
            signoffs += [" ".join(i.split()) for i in items]
            text = (text[:m.start()] + text[m.end():]).rstrip()
        text = re.sub(r"^##\s+", f"## {k}. ", text, count=1, flags=re.M)
        body.append(text)
        k += 1
    total_lines, total_files = lean_lines(sorted({d for *_, ds in CHAPTERS for d in ds}))
    ver = toolchain()
    summary = ["## 0. Summary", "",
               f"| Chapter | {BOOK_SHORT} | Content | Status | Lean lines |",
               "|:--|:--|:--|:--|--:|"] + rows + ["",
               f"Total: {total_lines:,} lines of Lean in {total_files} files under `{LIB}/` "
               f"(`wc -l`, excluding unfinished `WIP_` files). "
               f"Toolchain: Lean {ver}, Mathlib {ver}. To reproduce: `lake build`, then "
               f"`lake env lean -DmaxSynthPendingDepth=3 {TEST_FILE}`, which prints the axioms "
               f"of every main theorem. Edition of {datetime.date.today():%-d %B %Y}.", ""]
    sign = [f"## {k}. Sign-off", "",
            f"The statements below are the ones the reader is asked to confirm say what {BOOK_SHORT} mean. "
            "Each is a summary of the V-item it names; the standing hypotheses of that item are not "
            "repeated.", ""] + [f"{i}. {s}" for i, s in enumerate(signoffs, 1)]
    doc = "\n\n---\n\n".join([INTRO.rstrip().rstrip("-").rstrip(), "\n".join(summary).rstrip(), HOWTO.strip(),
                                 "\n\n---\n\n".join(body), "\n".join(sign)]) + "\n"
    open(OUT_MD, "w", encoding="utf-8").write(doc)
    print(f"{os.path.basename(OUT_MD)}: {len(body)} chapter sections, {len(signoffs)} sign-off items, "
          f"{len(doc.split()):,} words")
    if shutil.which("pandoc") is None or shutil.which("xelatex") is None:
        print(f"{os.path.basename(OUT_PDF)}: skipped (needs pandoc and xelatex on the PATH)")
        return
    r = subprocess.run(["pandoc", "-f", "markdown", "-o", OUT_PDF, "--toc", "--toc-depth=1"] + PDF_ARGS,
                       input=doc, text=True, capture_output=True, cwd=HERE)
    print(f"{os.path.basename(OUT_PDF)}:", "ok" if r.returncode == 0 else "FAILED\n" + r.stderr[-2000:])


if __name__ == "__main__":
    main()
