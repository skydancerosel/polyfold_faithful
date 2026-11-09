# Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*, Part I, in Lean 4

Part I of HWZ's book, *Basic Theory in M-Polyfolds* (the sc-calculus, retracts and M-polyfolds,
strong bundles, sc-Fredholm sections, the implicit function theorems, the Fredholm package and
orientations),
formalized against Mathlib with the same faithful layer as our formalizations of Milnor's
*Topology from the Differentiable Viewpoint* and *Morse Theory*
([`math_faithful`](https://github.com/skydancerosel/math_faithful)). Part II, *Ep-Groupoids*, is
under way: Chapters 7–11 are formalized (Chapter 11 without its §§11.2 and 11.4 on forms and
integration). The authoritative text is the
Springer edition (Ergebnisse der Mathematik und ihrer Grenzgebiete 72, 2021): the reports cite its three-level numbers and
pages first, with the numbers of the earlier versions in parentheses (the 2014 preprint, arXiv
1407.3185, for Part I; the 2017 arXiv version, 1707.08941, for Part II). Lean names keep the
numbers they were given first; items added or changed in 2021 have names ending in `_2021`, and
`Exposition/BookConcordance.md` maps the three numberings.

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
3. **Check each item.** Each of the 824 items has a one-sentence summary and a label saying how the
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

## Status (8 November 2026)

* **Part I, Chapters 1–6, is formalized**, Chapter 6 except Theorem 6.7.1 (preprint 6.43; the
  invariant `Ψ_(f,o)`) and the admissible sections of §6.7.
* **Part II, Chapters 7 and 8, is formalized** (ep-groupoids, orbit spaces, invariant partitions of
  unity; the tangent ep-groupoid and functor, strong bundles over ep-groupoids, proper covering
  functors). In the 2021 text the reduced ep-groupoid exists when `T_R` is Hausdorff (Theorem
  7.2.14), and `T_R` is always paracompact (proved); that `𝐗^R` need not be Hausdorff is checked in
  Lean. The sc-differential forms of §8.2 are not formalized.
* **The additions and changes of the 2021 edition in Chapters 1–8 are formalized**, among them
  locally complete spaces (§2.1), the tame boundary `bX` (§2.7, Theorem 2.7.13) and the boundary
  ep-groupoid (Theorem 7.6.9), Proposition 2.3.17 for all `i`, the global Lie bracket (§4.4–4.5),
  the topology of the orientation space (Theorem 6.6.17), the rewritten §7.2 and the Zhou condition
  (§7.4, §8.1).
* **Part II, Chapter 9, is formalized**, §§9.1–9.5 (branched ep⁺-subgroupoids, local branching
  structures, the tangent and the boundary, good points, orientations, the geometry of local
  branching structures, sets of measure zero and the canonical σ-algebras), with the parts that need
  level-0 sc-calculus in general M-polyfolds taken as explicit hypotheses, each shown satisfiable and
  discharged on `ℝᵐ`. Branched integration, the boundary measures and Stokes' theorems (Theorems
  9.5.4, 9.5.5, 9.5.15–9.5.18) are not formalized; they need the sc-differential forms of §8.2.
* **Part II, Chapter 10, is formalized**, §§10.1–10.5 with the Appendix proofs 10.6.1–10.6.2
  (equivalences of ep-groupoids, natural equivalences, the weak fibred product, localization at the
  equivalences, the category of generalized maps and the orbit-space functor, strong bundle
  equivalences, push-forward and pull-back of sections along generalized strong bundle
  isomorphisms, the weak fibred product of strong bundles and the category `SEP(F⁻¹)`). Local
  regularity under equivalences (Propositions 10.1.9, 10.1.10, 10.1.19, 10.3.16) is proved.
  Theorems 10.3.19 and 10.5.7 do not hold as we read them (counterexamples in Lean); Theorem
  10.3.19 holds when the target is effective. Not formalized: Propositions 10.4.6–10.4.7 (local
  regularity for strong bundles), the Fredholm parts of Theorems 10.4.5 and 10.5.4, the iterated
  products of Theorem 10.2.2, and the universal property of the localization.
* **Part II, Chapter 11, is formalized** except §11.2 (sc-differential forms under equivalences)
  and §11.4 (integration), which need the forms of §8.2: the tangent functor on `EP(E⁻¹)`, the
  degeneracy index and the faces under generalized isomorphisms (§11.1), branched
  ep⁺-subgroupoids, their tangent sections and orientations pushed forward and pulled back
  (§11.3; Theorem 11.3.9 for a representative, under an explicit hypothesis on the boundary
  operations, satisfied by the identity), strong bundles up to equivalence (§11.5), and
  equivalences of proper coverings with Theorem 11.6.6 and Proposition 11.6.8 (§11.6). Not
  formalized besides: the structures of Proposition 11.1.6, parts of Proposition 11.5.1 and the
  local section structures of §11.5, the localization `PC(E⁻¹)` and Remark 11.6.9 (G.128–G.135).
* About 211,000 lines of Lean in 330 files; every theorem has its axioms printed in
  `Polyfold/Test.lean` (10,746 declarations), all on `propext`, `Classical.choice`, `Quot.sound`; no
  `sorry`, no `axiom`.
* **Every numbered item of Chapters 1–11 is compared with its formal version** (824 items, each with
  a verdict: same, restated, hypothesis made explicit, stronger, narrower, or extra), with a gap
  list of what is not formalized and why (G.1–G.135).
* **Round-trip audit**: for all 604 items of Chapters 1–11 not labelled *extra* or *gap*, an
  independent model formalized the text's statement blind, and the two statements were related by
  short Lean proofs (`RoundTrip/REPORT.md`; Chapters 1–5 refreshed against the current code on 2
  November 2026, Chapters 6 and 7 audited on 7 November 2026, Chapters 8–11 on 8 November 2026). In Chapter 7 it proved that `𝐗^R`
  need not be Hausdorff (Propositions 7.9–7.10, gap G.71; `RoundTrip/Items/V7_40.lean`). In Chapters 8–11 every statement it found
  not to hold in the formal reading was one the project already records. One example is Theorems 10.3.19 and 10.5.7 (Findings Ch10
  item 58); it also gave a counterexample to Proposition 9.6.5 (1) read literally (Findings Ch9 item 104).
* **Human sign-off**: not started.

## Where to start reading (no Lean needed)

| Document | What it is |
|---|---|
| `Exposition/polyfold-beside-lean.html` | The comparison: the book's statement beside the formal one, in mathematical language, with the verdict and every difference listed. |
| `Exposition/polyfold-signoff.html` | The sign-off list: one sentence per item to confirm or flag. Ticks are kept in your browser and can be exported as text. |
| `Exposition/Verification.pdf` | The verified edition: each item as a short paragraph ending in the sentence to confirm. |
| `Exposition/Findings.md` | Every gap, hidden hypothesis, counterexample, reading chosen and possible misprint, numbered, with what was done about it. |
| `Exposition/ProofByProof.pdf` (or `polyfold-proof-by-proof.html`) | Each formal proof retold step by step, with a tag on every step naming the Lean declaration that checks it. |
| `Exposition/Chapter1.md` … `Chapter11.md` | The expanded exposition, with complete proofs, for a first-year graduate student. |
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
   tame charts for the germ data; "a bump function with `f ≠ 0`" as `f(x) ≠ 0`; Definition 6.2.1
   (preprint 6.1), p. 239, with locally defined sections. Each is recorded in the Findings with its reason.
3. **The new arguments** supplied where we could not complete a proof step from the text alone,
   before anyone cites them:
   surjectivity of `f'(y)` at the zeros near a zero in good position (V3.82, V3.93, V3.94; the proof of
   Theorem 3.6.8 (preprint 3.54), p. 139, still takes this step as in 2014 and 2017); the passage from the tangent germ property to a sub-M-polyfold for
   solution sets (V3.73, V3.85); the implicit function theorems in the germ reading; filler
   condition (3) on level 1 in Corollary 5.2.5 (preprint 5.8), p. 213 (V5.14); Proposition 6.2.2
   (preprint 6.2), p. 240, by the stabilization device (V3.98).
4. **The claims about the text**, against the Springer edition. Eight statements or proof steps
   do not hold as we formalized them, each with a counterexample checked in Lean: the proof of
   Theorem 3.2.3 (preprint 3.27), p. 107 (V3.73), Remark 2.4.8 (preprint 2.28), p. 47 (V2.33),
   the proof of Theorem 4.3.1 (preprint 4.23), p. 193 (V4.64), Theorem 5.5.10 (preprint 5.37), p. 232
   (V5.55), Definition 1.1.9 (preprint 1.8), p. 8 (V1.7), Lemma 5.3.16 (preprint 5.23), p. 224 (V5.42),
   the "Clearly" in Theorem 5.5.7 (preprint 5.34), p. 231 (Findings, Chapter 5, item 43) and the "not
   complete" in §5.3, p. 217 (V5.21). Each counterexample is to our reading of the text, and a
   misreading on our side would remove it; telling which is the reviewer's task. How the 2021 edition
   reads at the eight points: the same at six (Theorem 3.2.3, Theorem 4.3.1, Theorem 5.5.10,
   Definition 1.1.9, Theorem 5.5.7, §5.3), although Theorem 4.3.1 is restated in its conclusion (1);
   changed at Remark 2.4.8, which now gives an example (the intersection of a 3-plane
   with `[0,∞)⁴`) that, as we read it, is not an sc-smooth retract, so the claim still has no valid
   example; fixed at Lemma 5.3.16, since Definition 5.3.13 (3) now asks `dt` onto at every smooth
   point, which supplies the hypothesis the proof of Theorem 5.3.15 (preprint 5.22) needed
   (`Exposition/BookConcordance.md`, `Findings.md`, marks "book 2021"). Also: hypotheses a proof seems
   to use without stating them, and possible misprints; the tameness of `X` in Theorem 5.3.10
   (preprint 5.18), p. 220, was added in the 2017 version and is kept in 2021.
5. **The remark after Definition 7.1.7** (2017: 7.7), Part II, p. 291 (2017 pp. 228–229): that a
   functor between ep-groupoids which is sc-smooth on objects is sc-smooth on morphisms does not hold
   as we read it in the 2017 form. The counterexample, checked in Lean, is on `ℤ/3` acting trivially
   on `ℝ`: the identity on objects, `(g, y) ↦ (g, y)` for `y ≤ 0` and `(g², y)` for `y > 0` on
   morphisms. The 2021 edition keeps the remark and now also asks for continuity on level 0 of
   morphisms, which is what its argument uses and what is formalized
   (`isScSmoothMap_mor_of_continuous`); the counterexample no longer contradicts the text (V7.10;
   Findings, Chapter 7, items 9, 104). To confirm: that this is the intended definition.
6. **Proposition 7.2.10 (2017: 7.9), p. 313, and the reduced morphism space `𝐗^R`**: the 2021
   edition rewrote this. Proposition 7.2.10 now concludes only that `X^R` with the natural topology
   `T_R` has charts with sc-smooth transitions, Remark 7.2.8 says that it need not be an M-polyfold,
   and the reduced ep-groupoid exists when `T_R` is Hausdorff (Theorem 7.2.14, p. 318, an explicit
   hypothesis; 2017: Proposition 7.10). The formalization takes this hypothesis, proves that `T_R` is
   always paracompact (Proposition 7.2.12, p. 317), and checks in Lean that `𝐗^R` need not be Hausdorff
   (gap G.71, closed by the 2021 text; V7.39, V7.40; Findings, Chapter 7, items 129, 143). The question
   we had for the authors is answered by the 2021 text.
7. **Formula (2.44) and Proposition 2.7.12** (§2.7.4, pp. 82–84): "`Φ_(x,V,θ)` maps `U(x, V, θ)`
   bijectively onto `θ`" does not hold as we read it for every `V` in `N_{X,x}`, but only for `V`
   centred at `x`, where `Φ` is a bijection onto `θ`; for non-centred representatives its image is
   `θ ∩ V^x`, and the formalization proves Proposition 2.7.12 for every representative (V2.85, V2.104;
   Findings, Chapter 2, items 68, 73). Is "sufficiently small" (p. 85) meant to give centred `V`?
8. **The sentence on brackets, p. 201 (§4.5.1)**: "`[A, B](x)` belongs to level 1" for `x` in `O₂`
   does not hold as we read it; the counterexample, checked in Lean, uses two sc-operators on a
   weighted sequence space (V4.73; Findings, Chapter 4, item 156). Lemma 4.5.1 itself is formalized
   (V4.74, V4.77).
9. **Lemma 7.2.11** (p. 315, new in 2021): its part (3) does not hold as we read it for every
   ep-groupoid, because the proof uses the uniqueness of limits in `T_R`; it holds when `T_R` is
   Hausdorff, which is the setting of Theorem 7.2.14 where it is used (V7.76; Findings, Chapter 7,
   item 124).
10. **Proposition 9.1.11** (pp. 407–408; 2017: 9.2): the uniqueness of the dimensional decomposition
    `(Θ_k)` does not hold as we read it: on the trivial ep-groupoid of `ℝ²`, the indicator of a line
    has two decompositions satisfying (1) and (2) (`not_proposition_9_1_11_rn`,
    `Polyfold/Chapter9/Propositions.lean`; V9.9; Findings, Chapter 9, item 8). Uniqueness holds among
    the decompositions the proof constructs, those given near each point by the dimensional parts of a
    local branching structure (`proposition_9_1_11_unique_rn`, `isDimDecomposition_unique`,
    `Polyfold/Chapter9/DimDecompositionUnique.lean`; Findings, Chapter 9, item 105), and such a
    decomposition exists: read this way, with local finiteness, the proposition holds for every
    ep-groupoid over `ℝᵐ` (`proposition_9_1_11_local_rn`, `Polyfold/Chapter9/DimDecompositionExists.lean`;
    Findings, Chapter 9, item 106).
11. **Sheets of different dimensions in §§9.3–9.5**: Lemma 9.3.4 (p. 423), Lemma 9.4.4 with the note
    in Definition 9.4.7 (pp. 431–432), and Lemma 9.5.2 (p. 437) do not hold as we read them when the
    local branching structure has sheets of different dimensions; each counterexample is checked in
    Lean (`lemma_9_3_4_mixed_dim`, `lemma_9_4_4_mixed_dim`, `isNull_transfer_mixed_dim`), and each
    statement is proved for sheets of one dimension (V9.32, V9.42, V9.50; Findings, Chapter 9, items
    53, 72, 81). Is equidimensionality, as in Definition 9.3.6, meant throughout?
12. **Theorems 10.3.19 and 10.5.7** (pp. 493 and 508; 2017: 10.7, 10.10): that generalized
    isomorphisms (of ep-groupoids, or of strong bundles) with the local regularity property are
    determined by their orbit maps does not hold as we read it. On `ℤ/3` acting trivially on `ℝ`,
    which has (LR), the identity and the inversion functor `g ↦ g⁻¹` are generalized isomorphisms
    with the same orbit map that differ; the step on p. 494 uses families `α_z` that are not natural,
    and no natural transformation `1 ⇒ Inv` exists (`not_theorem_10_3_19`, `not_theorem_10_5_7`,
    `Polyfold/Chapter10/LocalizationLRCounterexample.lean`; V10.65, V10.67; Findings, Chapter 10,
    item 58). Both hold when the target is effective: Theorem 10.3.19 (`theorem_10_3_19_of_isEffective`,
    V10.66), and Theorem 10.5.7 with the hypothesis of the text for the target, Definition 8.4.2
    read for local strong bundle isomorphisms (`theorem_10_5_7_of_isEffective_of_isLRLocal`,
    `Polyfold/Chapter10/LocalizationLRBundleBase.lean`; Findings, Chapter 10, items 71, 72). Is an
    effectiveness hypothesis intended?

## Open questions

None of these is a hypothesis of a theorem of the project; each is stated precisely in the Findings.

* Whether the text's germ reading and the stricter whole-chart reading of Definition 3.1.11 (preprint 3.11), p. 96, agree for
  sections sc-smooth on `X` (Chapter 3, item 264).
* Whether germ data can always be moved to a compatible tame chart when the atlas is tame (item 199;
  re-centring a chart of the atlas provably cannot do it, items 350–353; the kernel condition can
  always be met, by stabilization, item 379).
* Whether a weak bump function (Definition 5.5.2 (preprint 5.29), p. 229) gives one non-zero at a given point of a
  general M-polyfold (Chapter 5, item 163; on an sc-Banach space it does at every point, since its bump points
  are all points or none, item 180).
* The local constancy of the index along the zero set for germ data that are not tame (item 243).
* A single family `P^i` for all `i` in Corollary 5.2.5 (preprint 5.8), p. 213 (the tameness of the shifted charts
  is proved, Chapter 5, item 181).
* The text's own open question after Proposition 4.2.3 (preprint 4.15), Question 4.2.4, p. 187.

Settled since: the text's own question on p. 340 of Part II (2017: p. 249), whether property (5) of a
paracompact orbit space follows from properties (1)–(4) of an ep-groupoid, has a negative answer: the Čech
groupoid of a Prüfer-type surface with uncountably many charts is an ep-groupoid whose orbit space is not
paracompact (`exists_epGroupoid_not_hasParacompactOrbitSpace`, `Polyfold/Chapter7/PropertyFiveResearch.lean`;
Chapter 7, item 152).

Not formalized (by decision, see the gap list in the comparison): Theorems 5.3.15 (preprint 5.22),
p. 223, and 5.27 (preprint; in neither the 2017 nor the 2021 text), the Banach-space theorems 5.5.5,
5.5.13, 5.5.16 (preprint 5.32, 5.40, 5.43; cited, used as hypotheses), the sc-differential forms of
§4.4, p. 195 (the Lie bracket is formalized), Lemma 4.1.11 (preprint 4.10), the dense form of
Theorem 5.3.12 (preprint 5.19), Theorem 6.7.1 (preprint 6.43), p. 277 (it needs the forms, integration
and Stokes' theorem; G.54) with the admissible sections of §6.7 (preprint §6.6), used only there
(G.55), and the infinite-dimensional examples of the applications (weighted Sobolev scales,
splicings). In Chapter 7: the tangent `Tφ` of a morphism as an sc-isomorphism (deferred to Chapter
8; G.70), the set `|X_∞|` of the filtration of the orbit space (G.72), and the density of `X_∞` in
`X_k` (G.73). (The paracompactness and Hausdorffness of `𝐗^R`, gap G.71, are settled; see item 6
above.) In Chapter 8: the sc-differential forms on ep-groupoids and the sc-de Rham complex
(Definitions 8.2.1, 8.2.2, pp. 372–373; 2017: 8.2, 8.3; G.74), and Lemma 8.1.2 (2017: 8.1), p. 359,
as printed, the identification of the tangent of the fibred product (G.75).

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
