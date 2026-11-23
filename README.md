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

Every numbered item of the book is compared with its formal version, with a verdict and every
difference listed. In 275 places (G.1–G.275) the formal version needs more than a translation of
the text: a step left to the reader, an example the text does not give, a convention left implicit,
or a long argument written out in full. 264 are formalized and 11 have nothing to formalize (questions,
comments, remarks that motivate or look ahead, exercises, and a preprint theorem absent from the 2021 text). Where a formal statement is narrower than the book's, the
comparison names the added hypothesis and shows that it can be satisfied.

| | Chapters | State |
|---|---|---|
| Part I, *Basic Theory in M-Polyfolds* | 1–6 | Formalized; the main theorems proved, Theorems 5.3.15 and 6.7.1 included |
| Part II, *Ep-Groupoids* | 7–11 | Formalized, including branched integration and Stokes' theorem (Theorems 9.5.15–9.5.18) with the text's hypotheses, and on every ep-groupoid without partitions of unity, as Remark 9.5.19 expects |
| Part III, *Fredholm Theory in Ep-Groupoids* | 12–16 | Formalized; the main theorems proved, Theorems 14.1.9, 15.3.9, 16.4.6 and 16.5.7 as printed; Theorem 15.4.3 and Corollary 15.4.4 with the standing assumptions of §15.3 and no partitions of unity; Theorem 16.6.6 over all admissible perturbations, with no bump functions and no partitions of unity, the hypotheses in the model of the orientation being tame germ data and the index |
| Part IV, *Fredholm Theory in Groupoidal Categories* | 17–19 | Formalized; the main theorems proved, Theorems 17.1.18, 18.6.1, 19.5.1 and 19.6.13 included; Theorems 17.6.7 and 17.6.10 as printed |

The trusted base, the declarations whose statements a reader has to check, is
`Exposition/checklist/TrustedBase.lean`. Nothing is assumed without proof: every declaration
depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), checked in
`Polyfold/Test.lean`.

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

## The reviewer's path

| Document | What it is |
|---|---|
| `Exposition/ReviewerChecklist.md` | **Start here.** The statements and definitions a person has to check (Lean checks the rest), in tiers. |
| `Exposition/polyfold-beside-lean.html`, `Exposition/Comparison.md` | The comparison: every statement of the book beside its formal version, with the verdict (same, hypotheses explicit, stronger, narrower, restated, …) and every difference. |
| `Exposition/Verification.pdf` | The verified edition: the same items as a document, each ending in the sentence to confirm. |
| `Exposition/ProofByProof.pdf` | Every formal proof retold as mathematics, each step tagged with the Lean declaration that checks it. |
| `Exposition/Findings.md` | Points left to the reader, hypotheses we made explicit, the readings chosen and the examples behind them, with what was done about each. |
| `Exposition/WorkedExample.md` | A worked example: the orbifold ℂ/ℤ₅ with the section z ↦ z², where multisections are needed and the invariant of Theorem 16.6.6 is 2/5. |
| `Exposition/polyfold-signoff.html` | The sign-off list (below). |
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
5. **Send it back** with **Export SIGNOFF.md** and email the file to whoever invited you.
   **Import…** reloads it, for example on another computer.

## What a reviewer is most needed for

1. **The definitions**: sc-structures, retracts and M-polyfolds, strong bundles, sc-Fredholm germs and
   sections, ep-groupoids, branched ep⁺-subgroupoids, sc⁺-multisections, polyfolds. Are they the
   authors' notions? Lean cannot tell a definition that differs from the authors' in a detail, so
   this is where a mismatch is hardest to see.
2. **The readings we had to choose**, each recorded in the Findings with its reason:
   * sc-smooth germs live on neighbourhoods whose levels may shrink with the level (Definitions 3.1.4,
     3.1.6, 3.1.11);
   * "tame strong bundle" (used from Theorem 3.6.8 on, not defined in the 2021 text) is read as the
     2014 and 2017 versions define it, and the germ data of §§3.6, 6.2, 6.6 and 12.5 are taken in a
     tame chart;
   * bump functions are read pointwise, `f(x) ≠ 0` (Definitions 5.3.1, 12.3.1);
   * index sets of structured multisections are non-empty, as the factor `1/|I_x|` of Definitions
     13.2.5 and 14.1.3 presumes;
   * the equivalence of Definition 13.3.8, as Definition 14.6.2 and Theorem 14.6.3 use it, also
     compares the sections, as the step on p. 682 states;
   * the strong polyfold bundle structure (Definition 16.3.1) carries local regularity as printed in
     Definition 8.4.2 (`IsLRLocal`); the form for strong bundle maps of `W` (`IsLR`) follows from it,
     and whether the two agree is not known to us (Findings, Chapter 8);
   * the lateral term of Stokes' theorem on the cobordism over `[0, 1] × X` (Remark 6.6.19) is the
     integral over the part of the boundary with `0 < t < 1`, a limit of cut-off integrals, for a
     tame `X` with or without faces;
   * the frame convention for the 1-dimensional cobordism of index 0 (Corollary 15.4.4) is read in a
     signed form;
   * in Part IV a covering family has a uniformizer at every object, `F(α) ≠ ∅` (§17.1, Proposition 17.3.4,
     Theorem 19.2.2), and condition (v3) of Definition 19.4.1 asks for a limit in the fibre over `z`.
3. **The arguments we supplied** where a proof step could not be completed from the text alone. Each
   is marked in the comparison and retold in ProofByProof.
4. **Where our reading needed a condition the text does not print.** In each case the statement with
   the condition is proved, and a small example in Lean shows why we used it. A different reading on
   our side may well make the condition unnecessary; the Findings give the details.

| Where | What our reading uses |
|---|---|
| Definition 1.1.9, p. 8; §5.3, p. 217 | Details in the Findings, Chapters 1 and 5 |
| Remark 2.4.8, p. 47 | We have not found an example for the remark |
| (2.44) and Proposition 2.7.12, pp. 82–84 | `V` centred at `x` |
| Proof of Theorem 3.2.3, p. 107 | Another route for one step |
| Theorem 3.6.8 (2), p. 136 | "Tame strong bundle" as in the 2014 and 2017 versions |
| Lemma 3.8.1, p. 145 | Details in the Findings, Chapter 3 |
| Theorem 4.3.1 and the formula for `dω`, pp. 193–201 | Sign and bracket conventions (Findings, Chapter 4) |
| Theorems 5.5.7 and 5.5.10, pp. 231–232 | Details of the proofs (Findings, Chapter 5) |
| Before Remark 6.4.6, p. 248; `DET(E, F)`, p. 262 | Details in the Findings, Chapter 6 |
| Lemma 7.2.11 (3), p. 315 | `T_R` Hausdorff, the setting of Theorem 7.2.14 |
| Proposition 9.1.11, pp. 407–408 | Uniqueness among the decompositions the proof builds |
| Lemmas 9.3.4, 9.4.4, 9.5.2 | Sheets of one dimension |
| Theorems 10.3.19 and 10.5.7, pp. 493, 508 | An effective target |
| Proposition 11.1.6, p. 524 | The intersection of two faces as a union of faces |
| Theorem 14.6.3 with Definition 13.3.8, p. 682 | The equivalence also compares the sections, as p. 682 uses it |
| §§16.1–16.3, pp. 707–723 | An effective target, as for Theorem 10.3.19 |
| Lemmas 17.1.9 and 17.2.10, pp. 748, 773 | `Ψ̂` continuous in Definition 17.1.8 |
| Proposition 17.1.25, p. 758 | Details in the Findings, Chapter 17 |
| Lemma 17.4.13, p. 798 | Tame in the sense of Definition 2.5.18 |
| Lemma 18.1.8, p. 847 | The continuity of Definition 12.2.1 in Definition 18.1.7 |
| Lemma 19.4.3, p. 881 | Details in the Findings, Chapter 19 |
| Definition 19.7.11, p. 910 | Compatible uniformizers, as in Definition 19.6.4 (A) |
| Proposition 19.7.18, Corollary 19.7.20 (3), Theorem 19.7.25 (4b), pp. 919–926 | Details in the Findings, Chapter 19 |
| The remark after Lemma 19.7.19, p. 920 | Details in the Findings, Chapter 19 |

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
