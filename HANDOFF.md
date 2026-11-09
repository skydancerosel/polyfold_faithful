# Handoff: the Polyfold project (HWZ Part I)

Written 2026-10-24 at the end of a cloud session; rewritten 2026-10-26 at the end of the first local
session on the Mac (Chapters 1–5 of Part I complete; the round-trip audit is next). Everything is committed on `main`. Resume with
the first message in §4. Updated 2026-11-07: Chapter 6 is formalized except Theorem 6.43 (G.54) and
§6.6 (G.55). Later on 2026-11-07: Part II has begun; Chapter 7 is formalized (waves W0–W4 of the Part
II plan in `PLAN.md`), its reports are written (wave W5, commit 919831f) and its round-trip audit is
done (§2, §3 item 11).

## 1. Setup

```bash
cd ~/polyfold_faithful && git pull
lake exe cache get      # Mathlib, once
lake build              # minutes, not hours (no Milnor/Morse dependency)
```

Until 2026-11-05 this project was the folder `Polyfold/` of `github.com/skydancerosel/math_faithful`
(now Milnor's two books only). It moved to `github.com/skydancerosel/polyfold_faithful`, which
starts from a single snapshot of that day: the development history before it is not published,
and the commit hashes cited below refer to that history. The local checkout moved from
`~/math_faithful/Polyfold` to `~/polyfold_faithful`.

Sources (not in git): the pdftotext of the two arXiv preprints go in `Exposition/sources/` as
`HWZ-PartI-2014.txt` (arXiv 1407.3185, Part I of the book) and `HWZ-ScSmoothness-2010.txt` (arXiv
1002.3381): `curl -sSL https://arxiv.org/pdf/1407.3185 -o a.pdf && pdftotext -layout a.pdf
Exposition/sources/HWZ-PartI-2014.txt`, same for the other. Chapter line ranges in the Part I text:
Ch. 1 = 151–633, Ch. 2 = 633–2395, Ch. 3 = 2395–6021, Ch. 4 = 6021–6914, Ch. 5 = 6914–8184,
Ch. 6 = 8185–9775 (the references follow).
The book's PDF (Springer 2021), when available, is kept untracked as `PolyfoldFredholm.pdf`;
every statement number and page in the exposition and reports is the preprint's, marked *(book?)*
until checked.

**On this Mac** (2026-10-26): `/usr/local/bin/git` is a stale x86 binary ("Bad CPU type"); Lean's
process spawn finds it first on the PATH, so every `lake` call (also inside `check_names.py`) fails
and then **deletes `.lake/packages/mathlib`**. Put a directory containing `git -> /usr/bin/git` first
on the PATH for every lake or check-script call. Mathlib was not downloaded: `cp -c -R
~/math_faithful/Morse/.lake/packages .lake/packages` (same Mathlib rev, already built; re-clone `mathlib` from
Morse the same way if it disappears). The preprint text was regenerated from the local
`~/math_faithful/1407.3185v1.pdf` (same line ranges); the 2010 paper could not be downloaded. The book's arXiv
version (1707.08941, July 2017) is used as a stand-in for the Springer PDF (not on this Mac):
`Exposition/BookConcordance.md` maps every numbered item of preprint Chapters 1–6 to it (Chapter 6
added 2026-11-07; the 2017 Chapter 6 is pp. 181–221); its section "Part II" lists the items of
Chapter 7 (pp. 225–256) by their 2017 numbers, the only numbering of Part II, which has no preprint
(added 2026-11-07); and the
*(book?)* marks are annotated *(book 2017: …)*. Its `pdftotext -layout` text is kept untracked as
`Exposition/sources/HWZ-Book-2017.txt` (since 2026-11-02). On 2026-11-02 every *(book 2017: …)*
annotation was checked against it: those of Chapters 1–3 were right; Findings Ch. 4 item 87, Ch. 5
items 60, 61, 70–72, 80, 86, 87, 100–104 and five module docstrings (`TameGermData`,
`LocalStructure`, `GeneralPosition`, `Homotopy`, `Transversality`) had numbers off by one or more
and were corrected to the concordance, which the text confirms. The points of the brief to the
authors (statements that do not hold as we read them, proof steps that needed a further argument)
were then checked against the 2017 text: all read the same there except Theorem 5.18's unstated
tameness (2017 Theorem 5.6 assumes `X` tame); see `BookConcordance.md`, "Is the 2017 text a later
version in substance?".

Checks that must stay green:

```bash
lake build
lake env lean -DmaxSynthPendingDepth=3 Polyfold/Test.lean | grep -v "propext, Classical.choice, Quot.sound\]"   # nothing but continuation lines
python3 Exposition/check_names.py                       # every cited name exists
python3 Exposition/check_trace.py Exposition/ProofByProof.md   # 0 unresolved
```

Rules as in Morse: no `sorry`; `#print axioms` in `Polyfold/Test.lean` for every theorem;
temporary files only as gitignored `WIP_*.lean`; V-items keep their numbers once a human has
started signing off (no sign-off has started on this project yet).

Wording about the text (the project lead, 2026-11-04): in everything the authors may read (the
brief, this README, `RoundTrip/REPORT.md`), a counterexample refutes *our reading* of a statement,
not the statement. Say "does not hold as we read it", "we could not see why", "possible misprint";
do not call the text wrong or speak of its "errors".

## 2. State (2026-10-26, end of the first local session; Chapters 6–7 added 2026-11-07, Chapters 8–11 and the 2021 edition 2026-11-08)

* **Chapters 1–6 of Part I are complete** (Chapter 6 except Theorem 6.43 and §6.6, see below): Lean,
  exposition (`Exposition/Chapter1.md` – `Chapter6.md`) and reports (`verification/ch01–ch06.md`,
  `cmp/ch01–ch06.json`, `pbp/part01–part06.md`; outputs
  `polyfold-beside-lean.html`, `Verification.md/.pdf`, `ProofByProof.md/.pdf`,
  `polyfold-proof-by-proof.html`, `polyfold-signoff.html`). V-items V1.1–V1.39, V2.1–V2.64,
  V3.1–V3.107, V4.1–V4.64, V5.1–V5.63, V6.1–V6.64, and V7.1–V7.68, V8.1–V8.43 for Part II's Chapters 7 and 8 (below);
  **512 sign-off items** (401 for Part I, 68 for Chapter 7, 43 for Chapter 8); gaps G.1–G.75 (G.70–G.73
  for Chapter 7, G.74–G.75 for Chapter 8). **Since 2026-11-08** (2021 edition and Chapters 9–11, below):
  **824 sign-off items**, 959 comparison rows, gaps G.1–G.135, V9.1–V9.62, V10.1–V10.71, V11.1–V11.42;
  3,741 trace tags (3,127 distinct declarations; 2026-11-02, Chapters 1–5). The user started
  hand-checking on 2026-10-26 from copies in `Exposition/review-2026-10-26/` (untracked); the
  sign-off page keeps ticks in browser
  storage keyed by V-id (export SIGNOFF.md). **No sign-off is recorded in the repository yet**, so
  V-items may still be edited in place; never renumber them.
* **Chapter 3: the sc-Fredholm implicit function theorem holds with the text's hypotheses**
  (Findings "## Chapter 3" 157, 189, 190–199). Theorems 3.19, 3.23, 3.54 (`theorem_3_19'`,
  `theorem_3_23'`, `theorem_3_54'`, with dimension = Fredholm index and the index locally constant:
  `theorem_3_23_index`, `theorem_3_54_index_locally_constant`), Corollary 3.24, Theorems 3.56, 3.57,
  Theorem 3.18, Corollary 3.39, the sharp Proposition 3.52. Two gaps of the text are closed by new
  arguments: the surjectivity of `f'(y)` at the nearby zeros (the text's Corollary 3.41 gives only
  the filled linearization; the same gap is in the book's arXiv version, its Theorem 3.13; Findings
  100, 180–189) and Theorem 3.27's two false steps for solution sets (Findings 82–83, 130–133,
  150–159). **A vacuous hypothesis was found and repaired on 2026-10-26** (Findings 190–199): the
  §3.6 theorems had assumed that the base retraction of *every* compatible strong bundle chart is
  tame, which no strong bundle satisfies; they now assume the text's tame germ data
  (`IsScFredholmSectionTame`, `IsGoodPositionGermTame`, `Chapter3/TameGermsG.lean`; since phase 2,
  2026-11-01, in the text's germ reading of Definition 3.11, the whole-chart forms kept as
  `…WholeChart`, §3 item 9). A complete
  non-vacuity witness was added on 2026-10-31 (`Chapter3/NonVacuity.lean`, Findings 200): the
  graph of a `C^∞` map `ℝⁿ → ℝᵏ` with `0` a regular value, in the trivial bundle, meets every
  hypothesis of Theorem 3.57; `Chapter3/NonVacuityCorner.lean` (Findings 201) does the same over
  the half-space `[0, ∞) × ℝᵐ`, with good position at boundary zeros (`W = 0` in both; a witness
  with an infinite-dimensional contraction part is not done); `Chapter3/TameVacuityChart.lean`
  (Findings 202) proves the old `htame` false for the same trivial bundle. **Proposition 6.2 and
  the index along the zero set no longer need bump functions** (2026-11-02, Findings 349, 360–367):
  the restriction of M-polyfolds and strong bundles to open sets (`MPolyfold.restrictOpen`,
  `StrongBundle.restrictOpen`, germ data and the index carried over) lets the text's device run on
  a chart domain, where its sections `R(·, e)` need no cut-off; the index of `f'(y)` is locally
  constant along the zero set for tame germ data (`index_locally_constant_tame`), and the index
  of Definition 6.1, read with the text's locally defined sections (`IsIndexAtLocal`), is constant
  along every sc-smooth path `ℝ → X` (`proposition_6_2_local`); with bump functions the local and
  the global reading agree (`isIndexAtLocal_iff_isIndexAt`). Comparison V3.98 stays "narrower"
  only because the path is on `ℝ`, not `[0, 1]` (the project has no M-polyfold `[0, 1]`). Added
  hypotheses left: `Y` closed (Def. 3.25, Lemma 3.55); the regularity conditions of Theorem 3.27
  for general subsets (not for solution sets).
* **Chapter 4**: complete except Lemma 4.10 (not needed; G.32), §4.4 sc-differential forms (out of
  scope; G.37–G.40) and the open question after Prop 4.15. Remark 4.3's "X¹ ≠ X" has an example
  since 2026-11-02 (`remark_4_3_example`, a retraction that loses a level, sc-smooth by a new
  criterion `IsLossFamily.isScSmooth`; even the topologies of `X` and `X¹` differ; G.31 closed).
  Proposition 4.9 by a direct proof (the text's route gives only germ regularity); Theorem 4.23 with
  a repaired covering step; Sard's theorem vendored from the Milnor project into
  `Polyfold/Vendor/MilnorSard/` (namespace `Polyfold.MilnorSard`, Milnor commit 53704ad, no lakefile
  change).
* **Chapter 5**: complete except Theorems 5.22 (Morse-type structure) and 5.27 (no proof in the
  text), the dense form of Theorem 5.19, and the cited Banach-space theorems 5.32, 5.40, 5.43 (5.43
  an explicit hypothesis of Corollary 5.44). Since 2026-11-02: Corollary 5.8 on the shifted strong
  bundle `P¹ : Y¹ → X¹` (`corollary_5_8`, `corollary_5_8_two`; each fixed `i` by iteration, a
  uniform family `P^i` not formalized; the filler condition on level `1` proved; G.41 closed) and
  the metric `ρ` on `Γ^{+,1}_U(P)` (`StrongBundle.allowableMetric`; "not complete" proved for
  `ℝ × ℝ → ℝ` and false for `U = ∅` or a point base, so it needs a hypothesis; G.42 closed). Theorem 5.18
  needs `X` tame (hidden hypothesis); Finding 88 (the parametrized section of Theorem 5.19 is not in
  good position at boundary zeros) is checked on paper only.
* **Chapter 6** (2026-11-06 to 2026-11-07; plan in `PLAN.md` §6): formalized except Theorem 6.43,
  the invariant `Ψ_(f,o)` (it needs §4.4's sc-differential forms, integration and Stokes' theorem;
  decision D1, G.54), and the admissible sections of §6.6, used only there (G.55). V6.1–V6.64
  (`verification/ch06.md`), Findings "## Chapter 6". Theorems 6.35 and 6.37 (the local propagation
  of orientations and the functor `Γ_f`) hold with the readings recorded there; Proposition 6.28 (1)
  is replaced by (1′) (G.61); Theorem 6.41 is verified as tangent orientations along the paths of
  zeros in a chart and Remark 6.42 at a point, their global parts and the perturbation paragraph
  after Theorem 6.41 are not formalized (G.66–G.69). Lemma 6.10 holds by another construction (the
  text's proof and the 2017 remark do not hold as we read them; Findings Ch. 6 item 4); formula (94)
  and Remark 6.42 are used with the sign `(−1)^{dim coker}` (items 50, 95). Paths on `ℝ` (decision
  D2, G.65). The round-trip audit of the 60 non-extra Chapter 6 items is done (2026-11-07; `RoundTrip/REPORT.md`, "Chapter 6, audited on 2026-11-07").
  Part II followed (next item).
* **Part II has begun: Chapter 7** (2026-11-07; plan in `PLAN.md`, "Part II plan"): formalized in
  `Polyfold/Chapter7/` (21 files; waves W0–W4, and `ReducedNotHausdorff.lean` after the audit);
  V7.1–V7.68 (`verification/ch07.md`), Findings "## Chapter 7" (items 1–116, numbered in blocks), exposition `Exposition/Chapter7.md`, the "Part II"
  table of `BookConcordance.md`. Part II has no preprint: numbers and pages are the 2017 text's
  (pp. 225–256). Theorems 7.1–7.6 hold with the readings recorded there; Propositions 7.9 and 7.10
  under `[T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]`, which the proof does not give as
  we read it (G.71; discharged for effective `X`; `Examples.exists_not_t2Space_reducedMor` shows that
  `𝐗^R` need not be Hausdorff); `Tφ` of Definition 7.4 only defined (G.70, deferred to Chapter 8);
  `|X_∞|` not stated (G.72); the density of `X_∞` in `X_k` not formalized (G.73). The remark after Definition 7.7 does not hold as we read it
  (counterexample `Examples.remark_definition_7_7_counterexample`); it holds for functors continuous
  on morphisms. Proved on the way: the local path connectedness of M-polyfolds (G.56, first fact),
  Michael's theorem (G.15), the tameness of index lifts (Ch. 5 item 145). Wave W5 done: the reports
  (commit 919831f) and the round-trip audit of the 64 non-extra, non-gap items (`RoundTrip/REPORT.md`,
  "Chapter 7, audited on 2026-11-07": 39 equivalent, 5 B false). The audit proved that `𝐗^R` need
  not be Hausdorff (`RoundTrip/Items/V7_40.lean`, namespace `NotB`, on Remark 4.3's retract), which
  settles the Hausdorff half of G.71 negatively; moved into `Polyfold/Chapter7/ReducedNotHausdorff.lean`
  the same day (Findings, Chapter 7, item 107). The audit also found that the density of `X_∞` in
  `X_k` (p. 227) is not in Part I for M-polyfolds (G.73, Findings item 116).
* **Part II, Chapter 8, Lean** (2026-11-08; plan in `PLAN.md` §II.9): formalized in
  `Polyfold/Chapter8/` (14 files): the tangent ep-groupoid `TX` (Theorems 8.1–8.3, Lemmas 8.1–8.8,
  Remark 8.1, Proposition 8.1, `TangentEp.lean`, `TangentTame.lean`), `|TX|` paracompact
  (Theorem 8.4, by metrizability, `TangentOrbit.lean`), strong bundles over ep-groupoids
  (Definitions 8.4–8.7, 8.10, §8.5.2, `EpStrongBundle.lean`), proper covering functors (Definition
  8.8, Theorem 8.5, Remark 8.2, Lemmas 8.9–8.11, Propositions 8.2, 8.4, `ProperCovering*.lean`),
  covering functors and geometric lifts (Definition 8.9, Proposition 8.3, Theorem 8.6,
  `GeometricLift.lean`), witnesses (`NonVacuity.lean`, `NonVacuityBundle.lean`). Not formalized:
  Definitions 8.2–8.3 (sc-forms, sc-de Rham; G.74) and Lemma 8.1 as printed (G.75). Reports done
  2026-11-08: V8.1–V8.43 (`verification/ch08.md`), Findings "## Chapter 8" (items 1–114, numbered in
  blocks), `Exposition/Chapter8.md`, `cmp/ch08.json`, `pbp/part08.md`, the Chapter 8 table of
  `BookConcordance.md`; G.70 now partly formalized (`tangentMor_tSrc`, `tangentMor_comp`). Theorem
  8.5 (5) as printed does not hold as we read it (counterexample
  `CoveringExamples.theorem_8_5_five_as_printed`; Findings Ch. 8 item 54). Not done: the round-trip
  audit of Chapter 8.
* **Part II, Chapter 9** (2026-11-08; 2021 numbering, names without suffix, e.g. `lemma_9_1_7`):
  `Polyfold/Chapter9/` (25 files, 16,925 lines), §§9.1–9.5 and §9.6.1: branched ep⁺-subgroupoids and
  local branching structures, dimension, the tangent and the boundary, good points, orientations,
  the geometry of local branching structures, sets of measure zero and the canonical σ-algebras.
  The parts that need level-0 sc-calculus in general M-polyfolds are explicit hypotheses, each shown
  satisfiable and discharged on `ℝᵐ`. Proposition 9.1.11's uniqueness does not hold as we read it
  (`not_proposition_9_1_11_rn`). Not formalized: branched integration, the boundary measures and
  Stokes (Theorems 9.5.4, 9.5.5, 9.5.15–9.5.18; they need §8.2's forms). Reports: V9.1–V9.62,
  Findings "## Chapter 9", `Exposition/Chapter9.md`, gaps G.93–G.110.
* **Part II, Chapter 10** (2026-11-08): `Polyfold/Chapter10/` (23 files, 11,770 lines), §§10.1–10.5
  with the Appendix proofs 10.6.1–10.6.2: equivalences, natural equivalences, the weak fibred
  product, the localization `EP(E⁻¹)` and its orbit-space functor, strong bundle equivalences,
  push-forward and pull-back of sections, the strong bundle weak fibred product and the category
  `SEP(F⁻¹)`. Propositions 10.1.9, 10.1.10, 10.1.19, 10.3.16 and Theorem 10.3.21 are proved.
  Theorems 10.3.19 and 10.5.7 do not hold as we read them (`not_theorem_10_3_19`,
  `not_theorem_10_5_7`, on the trivial `ℤ/3` action, `LocalizationLRCounterexample.lean`); Theorem
  10.3.19 holds for an effective target (`theorem_10_3_19_of_isEffective`). Reports: V10.1–V10.71,
  Findings "## Chapter 10", `Exposition/Chapter10.md`, gaps G.111–G.127 (open: G.111, G.112, G.116,
  G.117, G.121, G.122, G.124–G.126).
* **Part II, Chapter 11** (2026-11-08): `Polyfold/Chapter11/` (11 files, 6,508 lines), §§11.1, 11.3,
  11.5, 11.6: the tangent functor on `EP(E⁻¹)`, the degeneracy index and the face bijection under
  generalized isomorphisms (`EpEquivalenceGeometry*`); branched ep⁺-subgroupoids pushed forward and
  pulled back, Γ(π̂), orientations, Theorems 11.3.3–11.3.9 (`BranchedEquivalence*`; Theorem 11.3.9 for
  a representative under `MPolyfold.IsBoundaryTransfer`, satisfiable by `isBoundaryTransfer_id`);
  strong bundles up to equivalence (`StrongBundleUpToEquivalence`); equivalences of proper coverings,
  Theorem 11.6.6, Proposition 11.6.8 (`CoveringEquivalence*`). Not formalized: §11.2 (forms) and §11.4
  (integration), which need G.74/G.80; the structures of Proposition 11.1.6; Proposition 11.5.1 (1),
  (2); the local section structures; `PC(E⁻¹)`; Remark 11.6.9. Nothing in Chapter 11 fails to hold as
  we read it; five possible misprints (checked against the 2021 text). Reports: V11.1–V11.42,
  Findings "## Chapter 11", `Exposition/Chapter11.md`, gaps G.128–G.135.
* **Lean counts** (2026-11-08, end of Chapter 11): 10,746 `#print axioms` lines in `Test.lean`
  (4,942 for Chapters 1–6, 989 for Chapter 7, 830 for Chapter 8, 1,386 for the 2021 additions to
  Chapters 1–8, 1,053 for Chapter 9, 1,014 for Chapter 10, 532 for Chapter 11), all on `propext,
  Classical.choice, Quot.sound`; no `sorry`, no `axiom`; 329 Lean files and 210,713 lines under
  `Polyfold/` (tracked files, `wc -l`), of which 25 files and 16,925 lines in `Chapter9/`, 23 files
  and 11,770 lines in `Chapter10/`, 11 files and 6,508 lines in `Chapter11/`.
* **Leftovers**: gitignored `WIP_*.lean` scratch files in `Polyfold/Chapter2–11/` (agents may not
  delete; some duplicate declarations and would not compile). All of them, with `Exposition/pages/`,
  are archived in `~/repo-history-backups/polyfold-scratch-2026-11-08-*.tar.gz`; delete them. The
  per-chapter `Test.lean` generators are `WIP_N_list*.lean` (e.g. `Chapter11/WIP_N_list16.lean`):
  keep them while a chapter still changes (add a module to its imports and `phaseCMods`, run it with
  `lake env lean -DmaxSynthPendingDepth=3`, replace the block). The *(book 2017: …)* marks were
  annotated against the arXiv version 1707.08941 before the Springer PDF arrived (next item;
  `Exposition/BookConcordance.md`, text in `sources/HWZ-Book-2017.txt`); the 2010 paper's text is
  not in `sources/`.
* **The 2021 Springer book is the authoritative version** (user, 2026-11-08): `Exposition/sources/Polyfold
  and Fredholm Theory.pdf` (1008 pp., gitignored with all of `sources/`; never commit it or its text),
  extracted to `sources/HWZ-Book-2021.txt` (`pdftotext -layout`). It numbers items in three levels
  (Definition 9.1.2 for 2017's Definition 9.1) and has other pages (Chapter 7 p. 287, Chapter 8 p. 357,
  Chapter 9 p. 401, Chapter 10 p. 461) and some new items (e.g. Remark 9.1.4, Propositions 9.1.11–9.1.12,
  §7.6). From Chapter 9 on, cite the 2021 numbers and pages first, the 2017 ones in parentheses.
  **To do:** a 2021 column in `BookConcordance.md` for Part I and Chapters 7–8, a check of the *(book?)*
  marks and of the Chapter 7–8 statements against the 2021 text (new or changed items), without
  renumbering V-items or Lean names.

## 3. What remains, in order (the user's instructions: after Chapter 3, build the comparison HTML,
the proof by proof in PDF and HTML, and the sign-off HTML; then Chapter 4; update the reports as
each chapter lands)

1. ~~**Register the four compiling files**~~ — done 2026-10-24 (commit e334145; 342 theorems).
2. ~~**Chapter 1 consistency**~~ — done 2026-10-24 (commit 6de752e: the Fredholm index on Banach
   spaces and Prop 1.10's index statement proved; sc¹ = C¹ on relatively open subsets of quadrants,
   boundary included; `Chapter1/ExpositionLemmas.lean`; V1.28–V1.36; reports rebuilt). Original list:
   (a) the exposition's Prop 1.10 / Lemma 2.D
   claim `ind(T+S) = ind(T)` and level-wise index — `FredholmIndex.lean` was written for this; make
   prose and Lean agree; (b) "sc¹ = C¹ in finite dimensions with one-sided derivatives at the
   boundary" — Lean has the open-set case only; (c) Cor 1.20's "`C^{l+1}` on `U_l` for all `l` ⇒
   sc-smooth" — Lean needs `C^∞`, or `C^{k+1}` on every level; (d) exposition Lemmas 1.A(2), 2.B,
   2.C, 3.A(2), 3.B, 3.F have no Lean counterpart — mark or prove; (e) stale "not yet formalized"
   notes in Chapter1.md §7, `Chapter1/Degeneracy.lean`'s docstring and Findings.md about Theorem
   1.25 (it is proved). Then update cmp/ch01.json, verification/ch01.md (append V-items), pbp/part01.md
   and rebuild.
3. **Chapter 3 core** — done 2026-10-24 except Def 3.14 / Theorem 3.15 (they need strong bundle
   charts over M-polyfolds, item 4) and the passage of Theorem 3.12 / Cor 3.13 from germs to
   M-polyfolds (commits f3fcfd8, 2e04b7d, f89d7c3, cf7d305: `theorem_3_33`, `corollary_3_34`,
   `theorem_3_35`, Theorem 3.40, `theorem_3_12_local`, fillers; **the solution germ is sc^k only on
   a germ shrunk by `s_k` levels**, Findings "## Chapter 3" items 1–17). Original: fix and finish
   `ContractionGerm.lean` (Def 3.28, Theorem 3.30, Lemmas
   3.31–3.32, **Theorem 3.33 Germ-IFT**, Cor 3.34, Thm 3.35); Theorem 3.12 (local compactness), Cor
   3.13, Def 3.14, Theorem 3.15 (stability under sc⁺), Lemma 3.17. This is the project's test:
   formalize with the text's hypotheses; where one is missing add the weakest that works and record
   it in the docstring and Findings.md.
4. ~~**Chapter 2 finish**~~ — done 2026-10-24 with no added hypothesis (Props 2.35–2.46 incl. the
   partial cone, corner germs, products and fibred products; Defs 2.50–2.54, `Y[1]`, `P[1]`;
   Theorem 2.16 by Smirnov; Prop 2.19 (3); Prop 2.21 (3)–(4) in a chart). Left: Theorem 2.31's
   general non-tame equality case; Prop 2.21 (3)–(4) transported to `T_aX`; the category SBR.
   Reports: `cmp/ch02.json` V2.1–V2.64 (commits 37ee681, e492cd8).
5. **Chapter 3 second half** — mostly done 2026-10-25: good position (3.21–3.22, 3.45, 3.65,
   3.69–3.70), quadrant IFT 3.78 and inverse function theorem 3.72–3.75, sections of strong bundles
   (3.1–3.11, 3.14), Theorems 3.12–3.13 on M-polyfolds, 3.15, Prop 3.5, Thm 3.38, Cor 3.41,
   Thms 3.43/3.47 (local solvability), Prop 3.52, Lemma 3.55, Def 3.53, Thm 3.54 (3) as
   `theorem_3_54_graph`, Def 3.25 and **Thm 3.27 under `IsRegular`** (two counterexamples to the
   text's proof: Findings 82–83), Thms 3.56–3.57 of the tangent germ property. In progress (agents
   of 2026-10-25): Lemma 3.61 and 3.58–3.60; Thm 3.54 (1)–(2) via recentring, Prop 3.26, and
   3.19/3.23–3.24 as corollaries. Superseded by the proofs given: 3.62–3.64, 3.66–3.68, 3.76.
5b. ~~**Chapter 3, what is left**~~ — done 2026-10-26 ((a) Findings 100–117, 150–159, 180–189;
   (b) `IsRegular` holds for solution sets, Findings 130–133, 150–151; (c) Cor 3.39, Findings 121–123;
   (d) `proposition_3_52_index`, Finding 120; (e) not done). Original list: (a) Theorem 3.54 (1)–(2)
   at the zeros `y ≠ x₀`: the text's "proceeding as above" re-centres the chart with a new filler at
   `y`; needs a chart centred at `y`, a filler at `y`, chart-independence of `f'(y)` surjective and
   of good position (gap G.13, do it in charts), and `N_v = ker D(h+t)(z)` from the derivative of
   `(h+t)(v+σ(v)) = 0` along the quadrant (Findings 87, 91, 94, 96); (b) whether `IsRegular`
   follows from the text's hypotheses for the solution set of an sc-Fredholm section (the
   counterexamples 82–83 are for abstract tangent-germ sets) — prove it, or record precisely why
   not, under a Findings item "Does the sc-Fredholm IFT hold with the text's hypotheses?"; then
   `theorem_3_54`, 3.19, 3.23, 3.24, 3.56, 3.57 unconditionally or under `IsRegular`; (c) Cor 3.39
   (package Thm 3.38's linear coordinate change as an `IsStrongBundleIso` between shifted
   structures; composition lemma; `IsConjugateToBasicGerm` for `(g+s)¹`); (d) the sharper Prop
   3.52 (patch above); (e) Prop 3.10's second statement on levels m ≥ 1; Lemmas 3.55/3.70 for a
   general presentation of `C` (so `d_M = d_X` in Thm 3.27); Theorem 3.18; Remark 3.36.
5a. ~~**Cleanup after the Chapter 3 Lean settles**~~ — done 2026-10-25 (Chapter 2: 601c861; Chapter 3:
   3faaca4; `theorem_3_33` keeps `∃ s`, the shift `s_k = 2^k − 1` is recorded). Original list:
   stale docstrings calling proved things "assumed"/"not formalized" in `Chapter2/{MPolyfold,
   LevelPolyfold,TangentBundle,SubMPolyfold,Tame,DegeneracyIndex}.lean`, `Chapter3/Filler.lean`
   (Thm 3.15, Def 3.14) and `Chapter3/LocalCompactness.lean` (global 3.12/3.13); the docstrings of
   `ContractionGerm.lean` (l. 28) and `GermIFT.lean` (l. 37) cite a non-existent `ContractionGerm.of`
   (it is `IsSc0ContractionGerm.toContractionGerm`); sharpen `theorem_3_33`'s `∃ s` to
   `s_k = 2^k − 1` (read off `isSckGerm_succ_of_next`) or record it; Findings "## Chapter 3":
   item 11 superseded by 40–45, item 17 resolved by `StrongBundle.IsScFredholmGerm.sectionAdd`,
   page refs in items 13 (p. 98) and 19 (p. 77); add items: the shrinking may not be intrinsic
   (toy example of Chapter3.md §3), the sc^∞-germ reading needed by Def 3.25 (ii) / Thm 3.43 (1) /
   Cor 3.47 (1), the silent sc⁺ step in Prop 3.10, the example `f(x,y) = (x, y + x²)` for Thm 3.72 (2).
6. ~~**Exposition Chapter 3**~~ — done 2026-10-26 (§5, §8: c4b081b; §4, §6: 616e02f; the new
   surjectivity proof in §6.3 Step 5: bd18969; the tameness repair: b6d6227).
7. ~~**Reports for Chapters 2–3**~~ — done 2026-10-26 (Chapter 3 addenda 7ee9add, 8320424, 6e4b8cf:
   V3.68–V3.107); Chapter 4 reports b8fa911, Chapter 5 reports 078ba09.
8. ~~**Chapters 4 and 5**~~ — done 2026-10-26 (Lean, exposition, reports; see §2 for what is not
   formalized and why). Optional later work, none of it on the main line: Lemma 4.10 (trivial strong
   bundle `U ◁ Y` as a `StrongBundle`), ~~Corollary 5.8 beyond the chart level~~ (done 2026-11-02,
   Chapter 5 Findings 140–146), the chart-level vacuity proof and "tame atlas ⇒ tame germ charts"
   (Chapter 3 Finding 199; the re-centring strategy is refuted, the implication open, Findings
   350–354), the dense form of Theorem 5.19, Finding 88 in Lean, Remark 3.20, Remark 3.36 quantitatively, the gaps G.6/G.7/G.13 (levels `X^i`, `i ≥ 2`, and
   the linear structure of `T_xX`, which would let the chart-form statements be stated intrinsically).
9. **The round-trip audit** — **done** (2026-11-01; `RoundTrip/`, README and REPORT there): all 269
   non-extra items have a blind statement and a prover record; all compile, every proved direction
   passes `#rt_check`. **Refreshed against HEAD on 2026-11-02**: 82 items redone, all 269 item files
   recompile; 7 items await new blind statements for the strengthened theorems (V3.98, V5.13,
   V5.14, V3.82, V3.85, V3.94, V3.100), in progress on 2026-11-02. The headline theorems imply
   independent restatements of the text's claims.
   Statements of the text that do not hold in the formal reading: Theorem 3.27's step "δ sc^∞ near every v₀" (V3.73), the finite
   subcover in Theorem 4.23's proof (V4.64), Theorem 5.37 (i)⇒(ii) as written (V5.55), Definition
   1.8's "F = C ⊕ T(E_m)" (V1.7). Definitional differences: germs vs the whole chart in §3.1 (the
   project's sc-Fredholm germ was stricter than the text's; removed in phase 2, below), the
   algebraic good complement (V3.20), bump functions. Missing in the project (REPORT, "Missing in the project"): sc-Fredholm theory on
   all levels, restriction of strong bundle charts, transitivity of strong-atlas equivalence, several
   examples. Remark 2.28's negative claim does not hold in the formal reading — proved after the audit (`remark_2_28_isPartialQuadrant`,
   `Chapter2/PartialConeQuadrant.lean`, Flor's theorem in the needed case). Moved into the
   project afterwards (f063505): the text's sc-complement form of Theorems 3.54 (1), 3.23, 3.56,
   3.57 (`Chapter3/GoodPositionSc.lean`), restriction of strong bundle charts and the equivalence
   relation on strong-bundle and M-polyfold atlases, Lemma 5.2 literally, Remark 5.12's closedness,
   Lemma 3.9 on level m, Lemma 3.81 on all of V₀ (Findings Ch. 2 40–44, Ch. 3 210–217, Ch. 5 130–131).
   sc-Fredholm theory on all levels, added the same day (Findings Ch. 3 items 230–236): Proposition
   3.10's second statement on every level `m` (`proposition_3_10_level`); the criterion "sc-Fredholm
   ⟺ Fredholm on level 0 and regularizing" (`isScFredholm_iff`, `Chapter1/ScFredholmCriterion.lean`);
   Propositions 3.5, 3.52 and Theorem 3.19's "f'(x₀) is sc-Fredholm" in the centred chart
   (`proposition_3_52_sc`, `theorem_3_19_linearization_sc`, `Chapter3/FredholmGermLinearizationSc.lean`;
   filler condition (3) needed on level 0 only). Then (items 237–239, 250–252, Ch. 1 follow-up 1):
   `Lin(z)` sc-Fredholm at every zero in **every** chart (`StrongBundle.linAt_isScFredholm`,
   `Chapter3/LinearizationChartsSc.lean`, no tameness); filler (3) on every level at a zero; the
   converse of Proposition 3.5 in sc form (needs (3) on every level — level 0 alone fails, example in
   item 238, not formalized); the solution germ of Corollary 3.34 / Theorem 3.35 sc-smooth on one
   germ and `f⁽¹⁾` a Definition 3.28 germ (`Chapter3/GermIFTSmooth.lean`); the example after
   Definition 1.14, an sc¹ map with `Df` not norm-continuous (`Chapter1/ScOneNotNormContinuous.lean`,
   gap G.3).
   The index of `f'(y)` is locally constant along the zero set without good position, for tame germ
   data and bump functions (`theorem_3_54_index_locally_constant_general`,
   `Chapter3/IndexLocallyConstant.lean`, the text's stabilization device of Proposition 6.2; Findings
   Ch. 3 items 240–244); with the text's hypotheses (tame germ data, no bump functions) it is the
   same device on the restriction of the bundle to a chart domain, done 2026-11-02
   (`index_locally_constant_tame`, items 360–363); without tame germ data it is open, the missing
   step being `ind C(z) = 0` at nearby zeros (items 243, 343).
   Done on 2026-11-02 (commit 08c08c6; records in the fourth addendum of the comparison):
   Corollary 5.8 on the shifted strong bundle (`corollary_5_8`, `corollary_5_8_two`, Ch. 5 items
   140–146); Definition 6.1 and Proposition 6.2 along sc-smooth paths `ℝ → X` by the text's device,
   with tame germ data and bump functions (`StrongBundle.IsIndexAt`, `proposition_6_2`, Ch. 3 items
   340–348); the examples of V4.6 (`remark_4_3_example`, Ch. 4 items 140–146) and V5.21 (`ρ` a metric,
   not complete for `ℝ × ℝ → ℝ`, complete for `U = ∅` or a point base, Ch. 5 items 150–153); item 199
   sharpened (re-centring an atlas chart cannot give tame germ data, Ch. 3 items 350–355); weak bump
   functions give pointwise ones at smooth points of sc-Banach spaces (Ch. 5 items 160–164);
   Definition 3.3 in the germ reading. Done later on 2026-11-02 (commit 12924a4; records in the
   fifth addendum of the comparison): **Proposition 6.2 and the index along the zero set without
   bump functions** — the restriction of M-polyfolds and strong bundles to open sets
   (`Chapter3/RestrictOpen.lean`, `RestrictOpenGerms.lean`), the index along the zero set for tame
   germ data (`index_locally_constant_tame`, `IndexLocallyConstantLocal.lean`), Definition 6.1 with
   the text's locally defined sections (`StrongBundle.IsIndexAtLocal`) and Proposition 6.2 with the
   text's hypotheses for paths `ℝ → X` (`proposition_6_2_local`, `IndexAlongPathsLocal.lean`), the
   two readings of Definition 6.1 agreeing under bump functions (`isIndexAtLocal_iff_isIndexAt`,
   `IndexAlongPathsLocalBump.lean`) (Ch. 3 items 349, 360–367).
   Open next steps (none is the hypothesis of a theorem): whether the text's germ reading and the
   project's earlier whole-chart reading of Definition 3.11 agree for sections sc-smooth on `X`
   (Findings Ch. 3 item 264; the obstruction is on level 0; no theorem depends on it); item 199's
   remaining implication, germ data in some compatible chart ⟹ germ data in some compatible tame
   chart when the atlas is tame (Ch. 3 item 353); the weak-vs-pointwise bump question at non-smooth
   points (Ch. 5 item 163); Proposition 6.2 for paths sc-smooth on `[0, 1]` only, which needs
   `[0, 1]` as an M-polyfold with boundary (Ch. 3 items 347, 365); the tameness of the
   index raises of tame charts (the tame form of Corollary 5.8) and a uniform family `P^i` with
   `(X¹)¹ = X₂` as spaces (Ch. 5 items 145, 146; gap G.6); item 243 for non-tame germ data, the
   local constancy of the index along the zero set, equivalent to `ind C(z) = 0` (Ch. 3 item 343).
   **The germ-vs-whole-chart gap of §3.1 is closed (phase 2, commits b74e15e–452a9b3,
   2026-11-01; Findings Ch. 3 items 260–334).** Definition 3.11 and everything built on it were
   switched in place to the text's germ reading: the filling (`IsFillingGerm`) and the sc⁺-section
   (`IsScPlusGerm`) are sc-smooth germs on germs whose levels may shrink. `StrongBundle.IsScFredholmGerm`,
   `IsScFredholmSection`, the tame and good-position variants and the canonical theorems
   (`theorem_3_12`, `theorem_3_15`, `theorem_3_18`, `proposition_3_52`, `theorem_3_19`, `theorem_3_23`,
   `theorem_3_54`, `theorem_3_56`, `theorem_3_57`, …; Chapter 5 follows) carry the text's hypotheses
   with no added hypothesis; the whole-chart notions and theorems are kept as `…WholeChart` /
   `…_wholeChart` (142 renamed twins), the phase-2 names as aliases (`GermReadingAliases.lean`).
   Item 221's example is machine-checked (`exists_isScSmoothGerm_not_isScSmooth`). Definition 3.3
   (`IsScSmoothSectionGerm`), the hypothesis of no theorem, followed on 2026-11-02.
   The round-trip items (`RoundTrip/Items/`) were not renamed: they are pinned to commit b4d1d8c,
   where the canonical names denote the whole-chart notions. The comparison rows, verification text
   and REPORT were updated for the switch (V3.5–V3.107, V5.14).
10. ~~**Chapter 6**~~ — done 2026-11-07 except Theorem 6.43 (G.54) and §6.6 (G.55) (`PLAN.md` §6;
    state in §2). Round-trip audit of its 60 non-extra items done 2026-11-07. Left for Chapter 6: the gaps
    G.56–G.69.
11. **Part II, Chapter 7** — Lean done 2026-11-07 (waves W0–W4 of the Part II plan in `PLAN.md`; state
    in §2). Wave W5 done: the reports and the round-trip audit (2026-11-07). Left for Chapter 7: the
    gaps G.70–G.73 (G.70 with Chapter 8; G.71 now only paracompactness, since `𝐗^R` need not be
    Hausdorff).
12. **Part II, Chapter 8** — Lean and reports done 2026-11-08 (`PLAN.md` §II.9; state in §2). Left:
    the round-trip audit of Chapter 8, the gaps G.74–G.75, and small refactors (Lemma 7.4's quotient
    metric and two `Lift.lean` helpers are repeated privately in `TangentOrbit.lean`,
    `TangentTame.lean`; `FullOb`, `MPolyfoldCat.ofOpen`, `ScDiffeo.ofOpen`,
    `IsFullyFaithfulOpenEmbedding` could move to `Chapter8/Basic.lean`).
13. **Part II, Chapter 9** (Branched Ep⁺-Subgroupoids, pp. 291–331) — started 2026-11-08: plan in
    `PLAN.md` §II.10 (inventory, decisions P10.1–P10.4, waves W0–W4). Wave W0 done 2026-11-08 (`Chapter9/Basic.lean`,
    325 lines, 38 `#print axioms` lines, 6,799 in all): Definition 9.1 (`IsBranchedEpSubgroupoid`,
    `LocalBranchingStructure`), Definitions 9.2–9.3, Lemma 9.1 (`lemma_9_1`, by a shorter route than
    the text), witnesses (`Θ = 0`, the indicator of a point of `ℝⁿ`). Then (same day, 2021 numbering): `Chapter9/Symmetric.lean`, the
    restriction remark (`LocalBranchingStructure.restrict`, at `x`), Lemma 9.1.7 (2017: 9.2;
    `lemma_9_1_7`, symmetric structures), Part I facts (`IsSmoothSubmanifold.inter_isOpen`,
    `.image_of_isScDiffeoOn`); `Basic.lean` switched to 2021 numbering (`lemma_9_1` renamed
    `lemma_9_1_5`) and Definition 9.1.2 (1) of 2021 adds that `|supp Θ|` is paracompact (field
    `paracompactSpace_orbitSupp`; 2017 does not have it). 61 `#print axioms` lines for Chapter 9 (6,822
    in all). Not yet: dimension (`n`-dimensional, locally equidimensional; Part I has no rank for
    tangent spaces, G.7), Remark 9.1.3 (b), the restriction at another point `x₀`, Remark 9.1.4,
    Propositions 9.1.9, 9.1.11, 9.1.12. **Next: finish W0, then decide P10.4 (forms,
    measures, Stokes) before §9.4–§9.5.** After Chapter 9, the user's order (2026-11-08): Chapter 10
    (Equivalences and Localization, p. 333) if budget remains.
    Update (2026-11-08, later): `Chapter9/Propositions.lean` (3a6e377): chart-independent dimension
    (`HasDimAt`), Proposition 9.1.11 as printed with a counterexample to its uniqueness as we read it
    (`not_proposition_9_1_11_rn`), Proposition 9.1.12 in the equidimensional case, Remark 9.1.3 (b).
    Chapter 9 is paused for item 14.
14. **The Springer 2021 edition, Chapters 1–8** (user, 2026-11-08: "let us update the whole thing to
    match the book"; chosen: reports cite 2021 numbers and pages first, old ones in parentheses;
    the changed and new 2021 items are formalized; Lean names and V-/G-numbers are kept, new ones
    appended; Chapters 1–8 before Chapter 9 continues). **Done (2026-11-08)**: the 2021 section of
    `Exposition/BookConcordance.md`, 121 `(book 2021: …)` marks in `Findings.md`, all report
    citations switched to 2021-first (9b4be2d); new Lean files with names ending in `_2021`,
    registered in `Polyfold.lean` and in the `Test.lean` block "Axioms: Chapters 1–8, additions and
    changes of the Springer 2021 edition" (generator `Polyfold/WIP_N_list2021.lean`, gitignored; add a
    module to its imports and `phaseCMods`, run it, then replace the block): Chapter1/Book2021;
    Chapter2/LocalTopology(+Example), Book2021, TameBoundary(+Topology, Example, Structure,
    NonCentred), TameSub, TangentLift(+All); Chapter3/Book2021Germs, Book2021Items; Chapter4/Book2021,
    VectorFields(+Global), BracketLevel; Chapter5/Book2021; Chapter6/Book2021(+Continuity),
    OrientationSpace; Chapter7/ReducedCriterion, Book2021Basic, Zhou(+Levels), TameBoundaryEp(+Structure);
    Chapter8/Book2021, TangentZhou(+Levels). Reports for all of them (9281a4d, bfaf619): 649 sign-off
    items, 741 comparison rows, new gaps G.76–G.92 (pinned by a `"g"` field in `notFormalized`, read
    by `build_comparison.py`), closed: G.6, G.38, G.48, G.71 (by the 2021 text), G.76, G.77, G.78,
    G.81, G.84, G.88 (8.1.17 (2) only). 8,308 `#print axioms` lines in all. Findings per Lean file
    and the G-table are in the notes folder (`2021-report-items.md`, `gtable-2021.md`). Open 2021 gaps:
    G.79 (untamed germs), G.80/G.87 (forms, Stokes), G.82, G.83, G.85 (Part I facts as hypotheses),
    G.86, G.89, G.90–G.92.
    Chapter 9 resumed 2026-11-08 with wave W1 (§9.2: `Chapter9/Tangent.lean`,
    `Chapter9/BoundaryPosition.lean`).
15. ~~**Part II, Chapters 9–11**~~ — done 2026-11-08 (state in §2): Lean, reports, Findings, the
    exposition `Chapter9.md`–`Chapter11.md`, gaps G.93–G.135. Part II of the book ends with Chapter
    11; Part III, *Fredholm Theory in Ep-Groupoids*, begins with Chapter 12, *Sc-Fredholm Sections*
    (2021 p. 569). Left for Part II: the round-trip audit of Chapters 8–11; the open gaps (Chapter 10:
    Propositions 10.4.6–10.4.7, the Fredholm parts of Theorems 10.4.5 and 10.5.4, the iterated
    products of Theorem 10.2.2, the universal property of the localization; Chapter 11: §§11.2,
    11.4, G.128, G.130, G.132–G.135); the docstrings of Chapters 9–11 were checked for numbering
    against the 2021 and 2017 texts by the report agents (slips fixed 2026-11-08).

Model guidance (from the Morse audit): Opus 5.5 for provers and report writing; Fable 5.1 only
where proving is the bottleneck (e.g. the Germ-IFT). Run at most two Lean agents at a time on the
Polyfold project to leave memory for `lake build`.

## 4. First message for the next session (local, on the Mac)

> Read `HANDOFF.md` (§1 setup on this Mac, §2 state, §3 item 15) and `PLAN.md`. Work in
> `~/polyfold_faithful` on `main` (build from the repository root, with the git shim of §1 on the
> PATH for every lake call). Parts I and II (Chapters 1–11) of HWZ, *Polyfold and Fredholm Theory*
> (Springer 2021, the authoritative text, in `Exposition/sources/`, gitignored), are formalized and
> reported. Ask the user which comes next: the round-trip audit of Chapters 8–11 (modelled on
> `RoundTrip/`), Part III from Chapter 12 (cite 2021 numbers first; Lean names with the 2021 numbers
> and no suffix; G-items from G.136; a new `Test.lean` block per chapter), or the open gaps of §3
> item 15. Keep the four checks of §1 green; no `sorry`; `#print axioms` for every theorem; never
> renumber V-items, G-items or Findings items; check every hypothesis that quantifies over all charts
> for satisfiability (Chapter 3 Finding 190); never call HWZ wrong or speak of "errors" ("does not
> hold as we read it", "possible misprint"), and machine-check every "does not hold" before it goes
> into the Findings. At most two Lean agents at a time.
