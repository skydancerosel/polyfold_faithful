# Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*, Part I, in Lean 4

Part I of HWZ's book, *Basic Theory in M-Polyfolds* (the sc-calculus, retracts and M-polyfolds,
strong bundles, sc-Fredholm sections, the implicit function theorems, the Fredholm package and
orientations),
formalized against Mathlib with the same faithful layer as our formalizations of Milnor's
*Topology from the Differentiable Viewpoint* and *Morse Theory*
([`math_faithful`](https://github.com/skydancerosel/math_faithful)). The text used is the 2014
preprint, arXiv 1407.3185; a concordance gives the numbers of the book's 2017 arXiv version
(1707.08941). The 2021 Springer edition was not available to us.

The Lean code, the exposition and the reports were written by AI agents (Claude models) under the
direction of the project lead. Lean checks the proofs; whether the definitions and statements mean
what the authors meant is for human readers to confirm, and that review has not started yet.

## How to check it and sign off

No Lean and no GitHub account are needed: a web browser is enough, and you can work at your own
pace.

1. **Download.** Click [Download
   ZIP](https://github.com/skydancerosel/polyfold_faithful/archive/refs/heads/main.zip) and unzip
   the file (on a Mac, double-click it).
2. **Open the sign-off page.** In the unzipped folder, double-click
   `Exposition/polyfold-signoff.html`. It opens in your browser. Stay online: the formulas are
   typeset from the internet.
3. **Check each item.** Each of the 401 items has a one-sentence summary and a label saying how the
   formal statement compares with the book's (as in the book, hypotheses explicit, stronger,
   narrower, restated, …). Click **the full statement, HWZ beside Lean** to see the book's
   statement, with its page, beside what Lean proves, with every hypothesis it uses. If the formal
   statement says what the book means, tick **says what HWZ mean**; if not, leave it unticked and
   write your objection or question in the notes box.
4. **Stop and come back whenever you like.** Ticks and notes are saved in your browser as you go: to
   continue, open the same file in the same browser. **unsigned only** hides the items you have
   already ticked.
5. **Send it back.** When you are done, or want to send what you have so far, click **Export
   SIGNOFF.md**. This saves a small text file; email it to the person who invited you to review.
   **Import…** loads such a file again, for example to continue on another computer.

To read rather than sign: `Exposition/Verification.pdf` has the same items as a document, and
`Exposition/polyfold-beside-lean.html` puts every statement of the book beside its formal version
(open it the same way). `Exposition/Findings.md` lists the questions the formalization raised;
GitHub displays it directly.

## Status (7 November 2026)

* **Chapters 1–6 are formalized**, Chapter 6 except Theorem 6.43 (the invariant `Ψ_(f,o)`) and the
  admissible sections of §6.6: about 127,500 lines of Lean in 204 files; every theorem has its
  axioms printed in `Polyfold/Test.lean` (4,942 declarations), all on `propext`,
  `Classical.choice`, `Quot.sound`; no `sorry`, no `axiom`.
* **Every numbered item of the text is compared with its formal version** (401 items, each with a
  verdict: same, restated, hypothesis made explicit, stronger, narrower, or extra), with a gap list
  of what is not formalized and why (G.1–G.69).
* **Round-trip audit**: for all 269 items of Chapters 1–5 not labelled *extra*, an independent model
  formalized the text's statement blind, and the two statements were related by short Lean proofs
  (`RoundTrip/REPORT.md`; refreshed against the current code on 2 November 2026). The Chapter 6
  items have not been audited yet.
* **Human sign-off**: not started.

## Where to start reading (no Lean needed)

| Document | What it is |
|---|---|
| `Exposition/polyfold-beside-lean.html` | The comparison: the book's statement beside the formal one, in mathematical language, with the verdict and every difference listed. |
| `Exposition/polyfold-signoff.html` | The sign-off list: one sentence per item to confirm or flag. Ticks are kept in your browser and can be exported as text. |
| `Exposition/Verification.pdf` | The verified edition: each item as a short paragraph ending in the sentence to confirm. |
| `Exposition/Findings.md` | Every gap, hidden hypothesis, counterexample, reading chosen and possible misprint, numbered, with what was done about it. |
| `Exposition/ProofByProof.pdf` (or `polyfold-proof-by-proof.html`) | Each formal proof retold step by step, with a tag on every step naming the Lean declaration that checks it. |
| `Exposition/Chapter1.md` … `Chapter6.md` | The expanded exposition, with complete proofs, for a first-year graduate student. |
| `RoundTrip/REPORT.md` | The round-trip audit: results, disagreements for human review, statements of the text that do not hold in the formal reading. |

Open the HTML pages in a browser straight from the folder; they need no server.

## What a reviewer is most needed for

1. **The definitions** (sc-structures, retracts and M-polyfolds, strong bundles, fillers, basic
   germs, sc-Fredholm germs and sections, good position, tame charts): are they the authors'
   notions? Two silent errors of this kind in the project's own definitions were found and
   repaired: a tameness hypothesis that no strong bundle satisfies (Findings, Chapter 3, items
   190–199), and an sc-Fredholm germ asked on a fixed chart instead of on germs, which is strictly
   stronger (items 220–222, 260–334).
2. **The readings the formalization had to choose**: sc-smooth germs on neighbourhoods that may
   shrink with the level; "strong bundle chart" as any chart compatible with the atlas; "tame" as
   tame charts for the germ data; "a bump function with `f ≠ 0`" as `f(x) ≠ 0`; Definition 6.1
   with locally defined sections. Each is recorded in the Findings with its reason.
3. **The new arguments** supplied where we could not complete a proof step from the text alone,
   before anyone cites them:
   surjectivity of `f'(y)` at the zeros near a zero in good position (V3.82, V3.93, V3.94; the same
   step is in the 2017 version); the passage from the tangent germ property to a sub-M-polyfold for
   solution sets (V3.73, V3.85); the implicit function theorems in the germ reading; filler
   condition (3) on level 1 in Corollary 5.8 (V5.14); Proposition 6.2 by the stabilization device
   (V3.98).
4. **The claims about the text**, against the Springer edition. Eight statements or proof steps
   do not hold as we formalized them, each with a counterexample checked in Lean: Theorem 3.27's
   proof (V3.73), Remark 2.28 (V2.33), Theorem 4.23's proof (V4.64), Theorem 5.37 (V5.55),
   Definition 1.8 (V1.7), Lemma 5.23 (V5.42), Theorem 5.34's "Clearly" (Findings, Chapter 5,
   item 43) and §5.3's "not complete" (V5.21). Each counterexample is to our reading of the text,
   and a misreading on our side would remove it; telling which is the reviewer's task. Also:
   hypotheses a proof seems to use without stating them, such as `X` tame in Theorem 5.18, and
   possible misprints. The 2017 arXiv version reads the same at all eight points; of the unstated
   hypotheses, it adds the tameness in Theorem 5.18 (`Exposition/BookConcordance.md`).

## Open questions

None of these is a hypothesis of a theorem of the project; each is stated precisely in the Findings.

* Whether the text's germ reading and the stricter whole-chart reading of Definition 3.11 agree for
  sections sc-smooth on `X` (Chapter 3, item 264).
* Whether germ data can always be moved to a compatible tame chart when the atlas is tame (item 199;
  re-centring a chart of the atlas provably cannot do it, items 350–353).
* Whether a weak bump function (Definition 5.29) gives one non-zero at a given non-smooth point
  (Chapter 5, item 163; at smooth points of sc-Banach spaces it does).
* The local constancy of the index along the zero set for germ data that are not tame (item 243).
* The tameness of the shifted charts in Corollary 5.8 and a single family `P^i` for all `i`.
* The text's own open question after Proposition 4.15.

Not formalized (by decision, see the gap list in the comparison): Theorems 5.22 and 5.27 (5.27 has
no proof in the text), the Banach-space theorems 5.32, 5.40, 5.43 (cited, used as hypotheses),
§4.4 (sc-differential forms), Lemma 4.10, the dense form of Theorem 5.19, Theorem 6.43 (it needs
§4.4, integration and Stokes' theorem; G.54) with the admissible sections of §6.6, used only there
(G.55), and the infinite-dimensional examples of the applications (weighted Sobolev scales,
splicings).

## License

The Lean code is under the [Apache License 2.0](LICENSE), the license of Mathlib. The prose (the
expositions, the verified edition, the proof-by-proof report, the comparison and the audit reports)
is under [CC BY 4.0](LICENSE-CC-BY-4.0). *Polyfold and Fredholm Theory* remains the copyright of its
authors and publisher; the source texts are not distributed.

## For maintainers

`HANDOFF.md` has the state, the conventions, the four checks that must pass after every change
and the history; `PLAN.md` the original plan. Until 5 November 2026 the project was the folder
`Polyfold/` of [`math_faithful`](https://github.com/skydancerosel/math_faithful); it moved here
on that date. Toolchain: Lean `v4.33.1`, Mathlib `v4.33.1`. Build from the repository root:
`lake exe cache get` once, then `lake build`; check a file with
`lake env lean -DmaxSynthPendingDepth=3 Polyfold/Chapter1/X.lean`. On a machine where `lake` cannot
run `git`, put a working `git` first on `PATH` before any `lake` call (also before the scripts in
`Exposition/`, which call `lake`): otherwise `lake` deletes its Mathlib checkout (`HANDOFF.md`, §1).

The source texts (the 2014 preprint of Part I, arXiv 1407.3185, and the 2010 survey, arXiv
1002.3381, as extracted text) are kept untracked in `Exposition/sources/`; the book's PDF, when
present, is `PolyfoldFredholm.pdf` (untracked).
