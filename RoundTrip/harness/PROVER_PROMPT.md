You are the PROVER in a round-trip audit of a Lean 4 formalization of Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* ("the text": Part I, Chapters 1–6, from the 2014 preprint *Polyfold and Fredholm Theory I*; Part II, Chapters 7–8, from the 2017 book, arXiv 1707.08941, Chapters 9–11 from the Springer 2021 book; each item's statement file names its source). Project <P>. Before EVERY `lake` command run `export PATH=<SHIM>:$PATH` (a git shim; without it lake deletes Mathlib). Check files with `cd <P> && lake env lean <file>`; build a module with `lake build RoundTrip.Blind.<ID>` (needed once before an Items file can import it). Do NOT commit. Another Lean agent shares the machine (memory is tight): compile ONE file at a time; never run a bare `lake build`.

Item IDs: <IDS>.
For each ID:
- B := `RoundTrip.<ID>.B` in <P>/RoundTrip/Blind/<ID>.lean — an independent formalization of the text's statement by someone who never saw the project's theorem. Do NOT edit Blind files (if B has a bug that makes it not mean what the text says, record it in B_issue).
- A := the project's formal statement: the declarations in <RT>/decls/<ID>.txt (short names inside `namespace Polyfold`; resolve the full name with `#check`). Definitions there are vocabulary; A is the conjunction of the TYPES of the listed THEOREMS (`type_of% @Polyfold.name.{0,…}` — instantiate universes at 0 since B lives in `Type`; record that). If the item lists only definitions, A = True: then compare the project's definitions with B's notions (prove they agree) and report that.
- The text's statement: <RT>/blind/<ID>.md. Do NOT read <RT>/keys/, <P>/Exposition/cmp/, <P>/Exposition/Verification.md, <P>/Exposition/Comparison.* or <P>/Exposition/ProofByProof.md (they contain the expected answers).
- Format examples from an earlier audit of another project (read one or two for the file layout only): ~/math_faithful/Morse/RoundTrip/Items/{V2_13,V3_12}.lean and .json.

Write <P>/RoundTrip/Items/<ID>.lean:
```lean
import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.<ID>
namespace RoundTrip.<ID>
open Polyfold
def A : Prop := …
theorem A_holds : A := …
theorem A_to_B : A → B := …        -- only if fully proved
theorem B_to_A : B → A := …        -- only if fully proved
-- theorem not_B : ¬ B := …        -- only if B is false and you proved it
#rt_check RoundTrip.<ID>.A_to_B [<fully qualified theorem names from decls>]
#rt_check RoundTrip.<ID>.B_to_A [<same>]
#rt_overlap RoundTrip.<ID>.B_to_A [<same>]
end RoundTrip.<ID>
```
Rules: no `sorry`/`admit`/axioms; omit directions you can't prove. Every included direction must pass `#rt_check` (you may NOT use the item's own theorems, directly or through lemmas built on them; in A_to_B use the hypothesis). If `#rt_check` fails only because a banned theorem is reached through the proof fields of a definition, use `#rt_check_soft` and say so in the JSON. You MAY use Mathlib and any other project lemma (grep <P>/Polyfold/ freely). Budget roughly 20–30 minutes of effort per item: real effort on glue (unfolding, specializing settings, matching universes, repackaging structures) is expected, but when a direction would need re-proving substantial mathematics, stop and diagnose. The diagnosis is the main output: say precisely what one side has that the other lacks, and whether a failure is a genuine difference or only proof effort. Watch for hypotheses of A that can never hold (e.g. quantified over all charts): if A_to_B fails because B's hypotheses do not give one of A's, say which hypothesis and whether it is satisfiable.

Also write <P>/RoundTrip/Items/<ID>.json:
{"id": "...", "A_to_B": "proved|failed|false", "B_to_A": "proved|failed|false", "not_B": true|false, "relation": "equivalent|A_stronger|A_narrower|incomparable|unclear", "effort_only": true|false, "why": "<2–5 sentences: the precise mathematical difference, or why a proof failed>", "B_issue": null|"...", "overlap": "<summary of #rt_overlap output>", "uses_hypothesis": {"A_to_B": true|false, "B_to_A": true|false}}
(uses_hypothesis: false when a direction was proved by proving its conclusion outright without using the hypothesis — such directions are vacuous for the audit and must be flagged. A_stronger: A ⇒ B only. A_narrower: B ⇒ A only. incomparable: each has content the other lacks. effort_only: true if a failed direction is believed TRUE and just not proved.)

Final report (≤ 400 words): table ID | A→B | B→A | relation | one-line why; plus anything systematic.
