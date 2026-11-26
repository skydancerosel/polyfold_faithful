# Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*, in Lean 4

A formalization in Lean 4 and Mathlib of Hofer, Wysocki and Zehnder,
[*Polyfold and Fredholm Theory*](https://doi.org/10.1007/978-3-030-78007-4)
(Springer, Ergebnisse der Mathematik 72, 2021): Part I (Chapters 1–6), Part II (Chapters 7–11),
Part III (Chapters 12–16) and Part IV (Chapters 17–19). The Springer edition
is the authority; the reports cite its numbers and pages first, with the numbers of the 2014
preprint (Part I) and the 2017 arXiv version (Parts II–IV) in parentheses. It follows the same method as our formalizations of Milnor
([`math_faithful`](https://github.com/skydancerosel/math_faithful)).

The Lean code and the reports were written by Claude models under the direction of the project
lead. Lean checks every proof. Whether the definitions and statements say what the authors
meant is for human readers to confirm; that review has not started.

## Status

All four parts of the book, Chapters 1–19, are formalized, and the main theorems are proved. Lean
checks every proof: there is no `sorry`, and every declaration depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), checked in `Polyfold/Test.lean`.

**A worked example** ([`Exposition/WorkedExample-Mathematics.pdf`](Exposition/WorkedExample-Mathematics.pdf);
with references to the Lean proofs, [`Exposition/WorkedExample.pdf`](Exposition/WorkedExample.pdf)) carries Theorem 16.6.6 through on one
small polyfold: the orbifold ℂ/ℤ₅ with the section z ↦ z² of weight 2. No single-valued equivariant
perturbation makes it transversal, so multisections are needed. Every hypothesis of Theorem 16.6.6
holds together, and the invariant is 2/5; the same holds with an infinite-dimensional sc-Hilbert
factor.

**The classical case** (same documents, last section): for a finite group G acting linearly on an
oriented vector space, a proper equivariant map φ and a regular value c, the invariant of
Theorem 16.6.6 is the classical count (1/|G|) · Σ_{x ∈ φ⁻¹(c)} sign Dφ(x), and the effective count is
the same sum over |G/K|, K the subgroup acting trivially. For z ↦ zᵏ on ℂ/ℤₚ it is k/p, and for
z ↦ z̄ᵏ it is −k/p; the same holds with an infinite-dimensional factor.

**The statements, checked from the book alone** ([`RoundTrip/`](RoundTrip/README.md)). For every formalized statement
of Chapters 1–11 and the main statements of Parts III and IV, a model shown only the book's statement
wrote it in Lean, and a separate prover compared it with the project's statement in Lean, with a check that
the comparison does not use the theorems being compared. Where the two differ, the difference is a reading
the comparison records (for example tame germ data, Definition 3.6.3), the blind writer's reading, or a
formal statement more general than the book's. Theorem 17.1.28 and Proposition 17.3.6 hold for one
uniformizer per lift; for every pair they do not hold as we read Definition 17.1.8 (Findings, Chapter 17,
item 16).

| | Chapters | State |
|---|---|---|
| Part I, *Basic Theory in M-Polyfolds* | 1–6 | Formalized; the main theorems proved, Theorems 5.3.15 and 6.7.1 included |
| Part II, *Ep-Groupoids* | 7–11 | Formalized, including branched integration and Stokes' theorem (Theorems 9.5.15–9.5.18) with the text's hypotheses, and on every ep-groupoid without partitions of unity, as Remark 9.5.19 expects |
| Part III, *Fredholm Theory in Ep-Groupoids* | 12–16 | Formalized; the main theorems proved, Theorems 14.1.9, 15.3.9, 16.4.6 and 16.5.7 as printed; Theorem 15.4.3 and Corollary 15.4.4 with the standing assumptions of §15.3 and no partitions of unity; Theorem 16.6.6 over all admissible perturbations, with no bump functions and no partitions of unity, the hypotheses in the model of the orientation being tame germ data and the index |
| Part IV, *Fredholm Theory in Groupoidal Categories* | 17–19 | Formalized; the main theorems proved, Theorems 17.1.18, 18.6.1, 19.5.1 and 19.6.13 included; Theorems 17.6.7 and 17.6.10 as printed |

Every numbered item of the book is compared with its formal version, with a verdict and every
difference listed. Where the formal version needs more than a translation of the text (a step left
to the reader, an example the text does not give, a convention left implicit, or a long argument
written out in full), the comparison records it (G.1–G.275) and says how it is formalized. Where a
formal statement is narrower than the book's, the comparison names the added hypothesis and shows
that it can be satisfied.

The trusted base, the declarations whose statements a reader has to check, is
`Exposition/checklist/TrustedBase.lean`. Nothing is assumed without proof.

## How to build and check it

Toolchain: Lean and Mathlib `v4.33.1`.

```bash
lake exe cache get                                         # Mathlib, once
lake build Polyfold                                        # the whole library
lake env lean -DmaxSynthPendingDepth=3 Polyfold/Test.lean  # #print axioms for every theorem
```

The last command must print, for every theorem, only `propext`, `Classical.choice` and `Quot.sound`
(or a subset): no `sorryAx`, no project axioms. The reports are checked against the Lean sources by
the scripts in `Exposition/`, run from the project folder:

```bash
python3 Exposition/check_names.py Exposition/Verification.md Exposition/Comparison.md   # every cited name exists
python3 Exposition/check_trace.py Exposition/ProofByProof.md                           # every trace tag resolves
python3 Exposition/build_comparison.py      # Comparison.json, Comparison.md, polyfold-beside-lean.html
python3 Exposition/build_verification.py    # Verification.md, Verification.pdf
python3 Exposition/build_signoff.py         # polyfold-signoff.html
```

Where `lake` cannot run `git`, put a working `git` first on `PATH` before any `lake` call or
`Exposition/` script.

## Reading guide

| Document | What it is |
|---|---|
| `Exposition/ReviewerChecklist.md` | **Start here.** The statements and definitions a person has to check (Lean checks the rest), in tiers. |
| `Exposition/Path-16.6.6.md` | Checking one theorem: what a reader checks to trust Theorem 16.6.6, the statement first and then the definitions it uses, leaves first. |
| `Exposition/polyfold-beside-lean.html`, `Exposition/Comparison.md` | The comparison: every statement of the book beside its formal version, with the verdict (same, hypotheses explicit, stronger, narrower, restated, …) and every difference. |
| `Exposition/Verification.pdf` | The verified edition: the same items as a document, each ending in the sentence to confirm. |
| `Exposition/ProofByProof.pdf` | Every formal proof retold as mathematics, each step tagged with the Lean declaration that checks it. |
| `Exposition/Findings.md` | Points left to the reader, hypotheses we made explicit, the readings chosen and the examples behind them, with what was done about each. |
| `Exposition/WorkedExample-Mathematics.pdf`; `Exposition/WorkedExample.pdf` with the Lean references, summary in `Exposition/WorkedExample.md` | A worked example: the orbifold ℂ/ℤ₅ with the section z ↦ z², where multisections are needed and the invariant of Theorem 16.6.6 is 2/5, also with an infinite-dimensional sc-Hilbert factor; and the classical case, a finite group acting linearly on an oriented vector space, where the invariant is the signed count of solutions divided by the order of the group. |
| `Exposition/polyfold-signoff.html` | The sign-off list (below). |
| `RoundTrip/README.md`, `RoundTrip/REPORT.md`, `RoundTrip/REPORT-III-IV.md` | The round-trip audit of the statements: the method, how to run it, and the results item by item. |
| `Exposition/Chapter1.md` … `Chapter11.md` | An expanded exposition of Parts I–II with complete proofs, for a first-year graduate student. |
| `Exposition/BookConcordance.md` | The 2014, 2017 and 2021 numberings side by side. |

The HTML pages open straight from the folder; they need no server.

**Where the files are.** A file's chapter folder is its position in the dependency order: a file in
`Polyfold/ChapterN/` imports only files of chapters ≤ N (Part I is Chapters 1–6, Part II 7–11,
Part III 12–16). A result whose proof needs machinery of a later chapter therefore lives in that
later folder: Chapter 3's theorems on the index along paths and its local constancy are in
`Polyfold/Chapter5/` (they use the bump functions of Chapter 5), and the results of §7.4 on tangent
maps of ep-groupoids are in `Polyfold/Chapter8/ZhouTangent.lean`. Each comparison row names the file
of every declaration it cites, so the book number leads to the file.

## Signing off

A web browser is enough: no Lean and no GitHub account are needed.

1. **Download** the [ZIP](https://github.com/skydancerosel/polyfold_faithful/archive/refs/heads/main.zip)
   and unzip it.
2. **Open** `Exposition/polyfold-signoff.html` in your browser (stay online: the formulas are typeset
   from the internet).
3. **Check each item.** Each has a one-sentence summary and the verdict comparing the formal statement
   with the book's. **The full statement, HWZ beside Lean** shows the book's statement with its page
   beside what Lean proves. Tick **says what HWZ mean**, or leave it unticked and write your question
   in the notes box.
4. **Stop whenever you like.** Ticks and notes are kept in your browser; **unsigned only** hides what
   you have ticked.
5. **Save it** with **Export SIGNOFF.md**: keep the file, or send it to the maintainer of this
   project. **Import…** reloads it, for example on another computer.

## Open questions

None of these is a hypothesis of a theorem here; each is stated precisely in the Findings.

* Do the germ reading and the whole-chart reading of Definition 3.1.11 (p. 96) agree for sections
  sc-smooth on `X`?
* Does a weak bump function (Definition 5.5.2, p. 229) give one non-zero at a given point of a general
  M-polyfold?
* Is the index locally constant along the zero set for germ data that are not tame?
* The text's own Question 4.2.4 (p. 187).

Remark 9.5.19 (p. 451) expects that sc-smooth partitions of unity are "very likely not needed" for
Stokes' theorem on ep-groupoids. It holds without them on every ep-groupoid, along the route the remark
sketches (`EP.stokesWithoutPartitions_all`), and Theorems 16.4.6, 17.6.7 and 17.6.10 hold as printed with it.

Corollary 5.2.5 (p. 213) holds for one family `P^i : Y^i → X^i` indexed by `i`, with `P^{i+1} = (P^i)^1`
(`BundledStrongBundle.corollary_5_2_5_family`).

On the text's question on p. 340, whether property (5) of Definition 7.1.3 follows from (1)–(4): as
we read the definition, the Čech groupoid of a Prüfer-type surface with uncountably many charts
satisfies (1)–(4) but not (5)
(`exists_epGroupoid_not_hasParacompactOrbitSpace`).

**Not formalized, by decision:** the infinite-dimensional examples of the applications (splicings);
preprint Theorem 5.27 (in neither the 2017 nor the 2021 text); the pull-back of forms on `∂X` along a
general sc-smooth map, which the 2021 text does not use beyond Theorem 6.7.1.

## License

The Lean code is under the [Apache License 2.0](LICENSE), the license of Mathlib; the prose is under
[CC BY 4.0](LICENSE-CC-BY-4.0). *Polyfold and Fredholm Theory* remains the copyright of its authors and
publisher; the source texts are not distributed.

## For maintainers

`HANDOFF.md` has the conventions, the layout and the checks that must pass after every change. Lean
names use the 2021 numbers (`theorem_3_6_8` is Theorem 3.6.8); suffixes mark other forms:
`_preprint`, `_2017` (an earlier version's statement), `_hyp` (with auxiliary hypotheses). One file:
`lake env lean -DmaxSynthPendingDepth=3 Polyfold/Chapter1/ScBanach.lean`.
