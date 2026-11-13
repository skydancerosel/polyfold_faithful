# Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*, in Lean 4

A formalization in Lean 4 and Mathlib of Hofer, Wysocki and Zehnder, *Polyfold and Fredholm Theory*
(Springer, Ergebnisse der Mathematik 72, 2021): Part I (Chapters 1–6), Part II (Chapters 7–11) and
most of Part III (Chapters 12–16). The Springer edition is the authority; the reports cite its
numbers and pages first, with the numbers of the 2014 preprint (Part I) and the 2017 arXiv version
(Parts II–III) in parentheses. It follows the same method as our formalizations of Milnor
([`math_faithful`](https://github.com/skydancerosel/math_faithful)).

The Lean code and the reports were written by AI agents (Claude models) under the direction of the
project lead. Lean checks every proof. Whether the definitions and statements say what the authors
meant is for human readers to confirm; that review has not started.

## How to check it and sign off

A web browser is enough: no Lean and no GitHub account are needed.

1. **Download** the [ZIP](https://github.com/skydancerosel/polyfold_faithful/archive/refs/heads/main.zip)
   and unzip it.
2. **Open** `Exposition/polyfold-signoff.html` in your browser (stay online: the formulas are typeset
   from the internet).
3. **Check each item.** Each has a one-sentence summary and a label comparing the formal statement
   with the book's (same, hypotheses explicit, stronger, narrower, restated, …). **The full statement,
   HWZ beside Lean** shows the book's statement with its page beside what Lean proves. Tick **says what
   HWZ mean**, or leave it unticked and write your question in the notes box.
4. **Stop whenever you like.** Ticks and notes are kept in your browser; **unsigned only** hides what
   you have ticked.
5. **Send it back** with **Export SIGNOFF.md** and email the file to whoever invited you.
   **Import…** reloads it, for example on another computer.

## Status

| | Chapters | State | Open gaps |
|---|---|---|---|
| Part I, *Basic Theory in M-Polyfolds* | 1–6 | Formalized; the main theorems proved, Theorems 5.3.15 and 6.7.1 included | 1, in part: families on `[0, 1]ⁿ` beyond Proposition 6.6.3 and Lemmas 6.6.4–6.6.5 |
| Part II, *Ep-Groupoids* | 7–11 | Formalized, including branched integration and Stokes' theorem (Theorems 9.5.15–9.5.18) with the text's hypotheses | 1, in part: the branched subgroupoid and integrals of the example in Remark 9.5.20 |
| Part III, *Fredholm Theory in Polyfolds* | 12–16 | The main theorems of Chapters 12–14 and Theorem 15.3.7 proved, some in a narrower form; Theorems 15.3.9 and 16.6.6 and Corollary 15.4.4 proved up to steps still open | 22 |

Every numbered item of the book is compared with its formal version, with a verdict and every
difference listed (`Exposition/Verification.md`). Where a formal statement is narrower than the book's,
the comparison names the added hypothesis, shows it can be satisfied, and records what removing it
would take as a numbered gap (`Exposition/cmp/`). The trusted base, the declarations whose statements a
reader has to check, is `Exposition/checklist/TrustedBase.lean`; every declaration depends only on the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), checked in `Polyfold/Test.lean`.

## Where to start reading

| Document | What it is |
|---|---|
| `Exposition/ReviewerChecklist.md` | **Start here.** The statements and definitions a person has to check (Lean checks the rest), in tiers. |
| `Exposition/polyfold-signoff.html` | The sign-off list (above). |
| `Exposition/polyfold-beside-lean.html` | Every statement of the book beside its formal version, with the verdict. |
| `Exposition/Verification.pdf` | The same items as a document, each ending in the sentence to confirm. |
| `Exposition/Findings.md` | Gaps, hidden hypotheses, counterexamples, readings chosen and possible misprints, with what was done about each. |
| `Exposition/ProofByProof.pdf` | Every formal proof retold as mathematics, each step tagged with the Lean declaration that checks it. |
| `Exposition/Chapter1.md` … `Chapter11.md` | An expanded exposition with complete proofs, for a first-year graduate student. |
| `Exposition/BookConcordance.md` | The 2014, 2017 and 2021 numberings side by side. |

The HTML pages open straight from the folder; they need no server.

## What a reviewer is most needed for

1. **The definitions**: sc-structures, retracts and M-polyfolds, strong bundles, sc-Fredholm germs and
   sections, ep-groupoids, branched ep⁺-subgroupoids, sc⁺-multisections, polyfolds. Are they the
   authors' notions? Two such mismatches in our own definitions were found and repaired, so this is
   where silent errors are most likely.
2. **The readings we had to choose**, each recorded in the Findings with its reason. The main ones:
   sc-smooth germs live on neighbourhoods that may shrink with the level; "tame strong bundle"
   (used from Theorem 3.6.8 on, not defined in the 2021 text) is read as the 2014 and 2017 versions
   define it; index sets of structured multisections are non-empty, as the factor `1/|I_x|` of
   Definitions 13.2.5 and 14.1.3 presumes.
3. **The arguments we supplied** where a proof step could not be completed from the text alone. Each
   is marked in the comparison and retold in ProofByProof.
4. **The statements that do not hold as we read them.** Each has a counterexample checked in Lean;
   each is a counterexample to our reading, and a misreading on our side would remove it.

| Where | As we read it |
|---|---|
| Definition 1.1.9, p. 8; §5.3, p. 217 (“not complete”) | Details in the Findings, Chapters 1 and 5 |
| Remark 2.4.8, p. 47 | The claim has no example; the 2021 example is not an sc-smooth retract |
| (2.44) and Proposition 2.7.12, pp. 82–84 | The stated mapping property of `Φ_(x,V,θ)` (Findings, Chapter 2) |
| Proof of Theorem 3.2.3, p. 107 | A step of the proof; the theorem itself holds, by another route |
| Theorem 3.6.8 (2), p. 136 | With the 2021 germ data as printed: a tame strong bundle over `ℝ` whose solution set is a half-line |
| Lemma 3.8.1, p. 145 | At `P = {0}` |
| Proof of Theorem 4.3.1, p. 193; the bracket sentence, p. 201; the formula for `dω`, p. 197 | Details in the Findings, Chapter 4 |
| Theorems 5.5.7 (“Clearly”) and 5.5.10, pp. 231–232 | Details in the Findings, Chapter 5 |
| The remark that `DET(E, F)` is not orientable, p. 262 | For finite-dimensional `E`, `F` |
| The remark after Definition 7.1.7, p. 291; Proposition 7.2.10, p. 313; Lemma 7.2.11 (3), p. 315 | Details in the Findings, Chapter 7 |
| Proposition 9.1.11, pp. 407–408 | Uniqueness of the dimensional decomposition |
| Lemmas 9.3.4, 9.4.4, 9.5.2 | Need the sheets to have one dimension |
| Theorems 10.3.19 and 10.5.7, pp. 493, 508 | Need an effective target |
| Proposition 11.1.6, p. 524 | Two faces can meet in a set that is not a face; the union form is proved |
| After Definition 16.1.2, Remark 16.1.7, Definition 16.1.10, Lemma 16.2.1, after Definition 16.3.3, pp. 707–723 | Need an effective target, as Theorem 10.3.19 does |

## Open questions

None of these is a hypothesis of a theorem here; each is stated precisely in the Findings.

* Do the germ reading and the whole-chart reading of Definition 3.1.11 (p. 96) agree for sections
  sc-smooth on `X`?
* Does a weak bump function (Definition 5.5.2, p. 229) give one non-zero at a given point of a general
  M-polyfold?
* Is the index locally constant along the zero set for germ data that are not tame?
* Is there a single family `P^i` for all `i` in Corollary 5.2.5 (p. 213)?
* The text's own Question 4.2.4 (p. 187).

The text's question on p. 340, whether property (5) of Definition 7.1.3 follows from (1)–(4), has a
negative answer: the Čech groupoid of a Prüfer-type surface with uncountably many charts
(`exists_epGroupoid_not_hasParacompactOrbitSpace`).

**Not formalized, by decision:** the infinite-dimensional examples of the applications (splicings);
preprint Theorem 5.27 (in neither the 2017 nor the 2021 text); the pull-back of forms on `∂X` along a
general sc-smooth map, which the 2021 text does not use beyond Theorem 6.7.1.

## License

The Lean code is under the [Apache License 2.0](LICENSE), the license of Mathlib; the prose is under
[CC BY 4.0](LICENSE-CC-BY-4.0). *Polyfold and Fredholm Theory* remains the copyright of its authors and
publisher; the source texts are not distributed.

## For maintainers

`HANDOFF.md` has the conventions and the checks that must pass after every change. Lean names use the
2021 numbers (`theorem_3_6_8` is Theorem 3.6.8); suffixes mark other forms: `_preprint`, `_2017` (an
earlier version's statement), `_hyp` (with auxiliary hypotheses). Toolchain: Lean and Mathlib
`v4.33.1`. Build: `lake exe cache get` once, then `lake build`; one file:
`lake env lean -DmaxSynthPendingDepth=3 Polyfold/Chapter1/X.lean`. Where `lake` cannot run `git`,
put a working `git` first on `PATH` before any `lake` call or `Exposition/` script, or `lake` deletes its
Mathlib checkout.
