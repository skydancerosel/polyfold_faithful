#!/usr/bin/env python3
"""Assemble Exposition/ProofByProof.md from the parts in Exposition/pbp/.

1. `--normalize` (run once, after all parts exist): subsection numbers become `<Roman part>.k`
   ("### 2.3" in Part II becomes "### II.3"; Part 0 keeps "0.k"). Unlike the Morse project, the
   cross-references "§2.3" are *not* rewritten here, because the book's own sections are numbered
   "§1.1", "§2.3", … and would be hit; write cross-references to the parts as "§II.3" directly.
2. Concatenate: the title, the prologue (Exposition/pbp/prologue.md, if present) and the parts in
   order, into Exposition/ProofByProof.md.

Usage: python3 assemble_pbp.py [--normalize]
Then:  python3 build_proofbyproof.py [outdir]
"""
import pathlib, re, sys

# ---- project configuration -------------------------------------------------------------------
HERE = pathlib.Path(__file__).resolve().parent
PBP = HERE / 'pbp'
OUT = HERE / 'ProofByProof.md'
TITLE = '# Polyfold Theory, proof by proof'
DEK = ('*The formal proof of Hofer–Wysocki–Zehnder\'s* Polyfold and Fredholm Theory, *Parts I–III, Chapters 1–16, retold '
       'as mathematics: every definition as the formalization makes it, every proof step by step as '
       'the Lean proof goes, and on every step of substance a trace tag naming the declaration that '
       'proves it.*')
# ------------------------------------------------------------------------------------------------

ROMAN = {1: 'I', 2: 'II', 3: 'III', 4: 'IV', 5: 'V', 6: 'VI', 7: 'VII', 8: 'VIII', 9: 'IX',
         10: 'X', 11: 'XI', 12: 'XII', 13: 'XIII', 14: 'XIV', 15: 'XV', 16: 'XVI'}


def parts():
    return sorted(p for p in PBP.glob('part[0-9][0-9].md'))


def normalize():
    files = parts()
    for f in files:
        n = int(f.stem[4:])
        if n == 0:
            continue
        rom = ROMAN[n]
        # headings "### n.k" -> "### ROM.k"
        f.write_text(re.sub(rf'(?m)^(###\s+){n}\.(\d+)\b', rf'\g<1>{rom}.\2', f.read_text()))
    print(f'normalized {len(files)} parts')


def assemble():
    chunks = [TITLE, '', DEK, '']
    pro = PBP / 'prologue.md'
    if pro.exists():
        chunks += [pro.read_text().strip(), '']
    for f in parts():
        chunks += [f.read_text().strip(), '']
    OUT.write_text('\n'.join(chunks) + '\n')
    words = len(OUT.read_text().split())
    print(f'{OUT.name}: {len(parts())} parts, {words:,} words')


if __name__ == '__main__':
    if '--normalize' in sys.argv:
        normalize()
    assemble()
