# Round-trip audit of Part I and Part II, Chapters 7–11 — method and how to run it

Modelled on `Morse/RoundTrip/` of [`math_faithful`](https://github.com/skydancerosel/math_faithful) (see its `REPORT.md` for the method in detail). The audit checks
the *statements* of the comparison (`Exposition/cmp/*.json`): for each item, an independent model
writes the text's claim in Lean without seeing the project's theorems, and a second model tries to
prove the two statements equivalent in Lean.

## Method (layer 1, statements)

1. **Blind statement B.** A model shown only the text's statement as the comparison quotes it
   (`$RT_DIR/blind/<ID>.md`; never the project's Lean sources, the verdict or the exposition)
   writes the claim as `RoundTrip.<ID>.B` in `RoundTrip/Blind/<ID>.lean`. It may use Mathlib and
   the project's *definitions* (types and docstrings, `$RT_DIR/vocab.md`), not its theorems.
   Prompt: `harness/BLIND_PROMPT.md`.
2. **A.** The conjunction of the types of the theorems the comparison cites (universes at 0).
3. **Proofs.** A separate prover, not told the verdict, tries `A → B` and `B → A` in
   `RoundTrip/Items/<ID>.lean`. `#rt_check` (`RoundTrip/Check.lean`) rejects any proof that uses
   the item's own theorems, directly or through project lemmas built on them, and any proof
   containing `sorryAx`; `#rt_overlap` lists the lemmas of the formal proof that a `B → A` proof
   reuses. Prompt: `harness/PROVER_PROMPT.md`. Each item also gets a JSON record (relation,
   effort-only flag, the diagnosis, vacuous directions flagged by `uses_hypothesis`).
4. **Score.** Expected relation from the verdict: *same / explicit / restated* → equivalent;
   *stronger* → A ⇒ B only; *narrower* → B ⇒ A only (`harness/score.py`). Items labelled
   *extra* (project material with no counterpart in the text) are not audited.

Differences from the Morse audit: the text is the HWZ preprint (statements quoted in the
comparison's `book` field); the provers are told to look for hypotheses of A that cannot hold
(Findings, Chapter 3 item 190: a hypothesis quantified over all compatible charts would make the
§3.6 theorems vacuous); there is no embedded special case.

## Running it

```
export PATH=<git shim>:$PATH            # HANDOFF §1: lake needs /usr/bin/git first on the PATH
export RT_DIR=<scratch folder>; mkdir -p $RT_DIR
python3 RoundTrip/harness/make_inputs.py          # blind/, keys/, decls/ from Exposition/cmp/*.json
lake env lean RoundTrip/harness/Vocab.lean        # $RT_DIR/vocab.md (project definitions)
lake build RoundTrip.Check
```

Substitute `<P>` (this folder), `<RT>` (`$RT_DIR`), `<SHIM>` (the shim's folder) and `<IDS>` in
the prompts before handing them to a model. Four Lean sessions at a time fit on a 128 GB machine
(each compiles single files only); one blind session per ~9 items, one prover session per ~5–6 items.
`harness/summarize.py --rows` writes the report's tables. Recompile everything at the end
(`lake env lean RoundTrip/Items/<ID>.lean` for every item: no error, no `rt_check FAIL`).

## Status

All 604 non-extra, formalized items of Chapters 1–11 are audited; see `REPORT.md`. Chapters 1–5 (269
items) were audited against commit 12924a4, Chapter 6 (60 items) against commit 439bc62, Chapter 7
(64 items, quoted from the 2017 book) against commit 919831f, and Chapters 8–11 (211 items;
Chapters 9–11 and the 2021-only items of Chapter 8 quoted from the Springer 2021 book) against
commit caf6bfc. The Chapters 1–5 items follow the germ reading of Definitions 3.3 and 3.11
(`IsScFredholmGerm`, `IsScFredholmSection` and their tame and good-position variants state the
text's hypotheses; the whole-chart forms are `…WholeChart` / `…_wholeChart`; Findings Ch. 3 items
270–334): for the 82 items concerned, A is the conjunction of the current row and the item's JSON
record carries a `refresh` field. For seven items (V3.82, V3.85, V3.94, V3.98, V3.100, V5.13,
V5.14) a second blind statement `Blind/<ID>_r2.lean` (`RoundTrip.<ID>_r2.B`) written by
`harness/BLIND_PROMPT.md` is the one in use, because the first one does not mean the text under the
germ reading (or does not cover the full row, V3.98); the first ones are kept, the item's JSON names
the statement in use (`blind_current`) and keeps the result against the first (`blind_r1`).

To recompile without `lake build` (which would rebuild the `Polyfold` olean if its sources moved):
refresh a blind module with `lake env lean RoundTrip/Blind/<ID>.lean -o
.lake/build/lib/lean/RoundTrip/Blind/<ID>.olean -i .lake/build/lib/lean/RoundTrip/Blind/<ID>.ilean`, then
`lake env lean RoundTrip/Items/<ID>.lean`. V1_13 and V1_35 `import Polyfold.Test`, whose olean must be
current (the refresh compiled it into a scratch overlay put first on `LEAN_PATH`).
