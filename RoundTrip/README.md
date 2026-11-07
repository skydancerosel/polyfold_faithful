# Round-trip audit of Part I — method and how to run it

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
(Findings, Chapter 3 item 190: a hypothesis quantified over all compatible charts made the §3.6
theorems vacuous until it was repaired); there is no embedded special case.

## Running it

```
export PATH=<git shim>:$PATH            # HANDOFF §1: lake needs /usr/bin/git first on the PATH
export RT_DIR=<scratch folder>; mkdir -p $RT_DIR
python3 RoundTrip/harness/make_inputs.py          # blind/, keys/, decls/ from Exposition/cmp/*.json
lake env lean RoundTrip/harness/Vocab.lean        # $RT_DIR/vocab.md (project definitions)
lake build RoundTrip.Check
```

Substitute `<P>` (this folder), `<RT>` (`$RT_DIR`), `<SHIM>` (the shim's folder) and `<IDS>` in
the prompts before handing them to an agent. Four Lean agents at a time worked on the 128 GB Mac
(each compiles single files only); one blind agent per ~9 items, one prover agent per ~5–6 items.
`harness/summarize.py --rows` writes the report's tables. Recompile everything at the end
(`lake env lean RoundTrip/Items/<ID>.lean` for every item: no error, no `rt_check FAIL`).

## Status

2026-11-01: complete — all 269 non-extra items audited; see `REPORT.md`. 2026-11-07: the 60 non-extra Chapter 6 items audited against commit 439bc62 (`REPORT.md`, "Chapter 6, audited on 2026-11-07"); all 329 items now. 2026-11-02: refreshed against
HEAD (below), second blind statements for seven items, Proposition 6.2 without bump functions in V3.98.

The items compile against HEAD (commit 12924a4; refreshed 2026-11-02). After the audit, phase 2 of the
germ-versus-chart work (Findings Ch. 3 items 270–334) switched Definitions 3.3 and 3.11 and the
notions built on them in place to the text's germ reading (`IsScFredholmGerm`, `IsScFredholmSection`,
their tame and good-position variants now state the text's hypotheses; the whole-chart forms are
`…WholeChart` / `…_wholeChart`), and the comparison rows gained declarations (Corollary 5.8,
Proposition 6.2, Remark 4.3's example, the metric `ρ`, the audit's glue moved into the project). The
82 affected items were redone (A restated from the current row, both directions retried, records
updated with a `refresh` field), the 269 blind statements recompiled unchanged, and all 269 item
files recompiled with no error, no `rt_check FAIL` and no `sorry`; see `REPORT.md`, "Refreshed on
2026-11-02". Seven first blind statements no longer meant the text under the current definitions
(V3.82, V3.85, V3.94, V3.100, V5.13, V5.14) or did not cover the extended row (V3.98); second blind
statements were written the same day by `harness/BLIND_PROMPT.md` as `Blind/<ID>_r2.lean`
(`RoundTrip.<ID>_r2.B`), the first ones kept; the item's JSON names the statement in use
(`blind_current`) and keeps the result against the first (`blind_r1`).

To recompile without `lake build` (which would rebuild the `Polyfold` olean if its sources moved):
refresh a blind module with `lake env lean RoundTrip/Blind/<ID>.lean -o
.lake/build/lib/lean/RoundTrip/Blind/<ID>.olean -i .lake/build/lib/lean/RoundTrip/Blind/<ID>.ilean`, then
`lake env lean RoundTrip/Items/<ID>.lean`. V1_13 and V1_35 `import Polyfold.Test`, whose olean must be
current (the refresh compiled it into a scratch overlay put first on `LEAN_PATH`).
