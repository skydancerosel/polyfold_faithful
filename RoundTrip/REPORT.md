# Round-trip audit of Part I and Part II, Chapters 7–11 — report

Status 2026-11-01 (the audit; Chapter 6 added 2026-11-07, see "Chapter 6, audited on 2026-11-07" below; Part II, Chapter 7 added 2026-11-07, see "Chapter 7, audited on 2026-11-07"; Chapters 8–11 added 2026-11-08, see "Chapters 8–11, audited on 2026-11-08"); the lists of what the project lacks updated 2026-11-02; refreshed against
HEAD (commit 12924a4) on 2026-11-02, see "Refreshed on 2026-11-02" below. Method and how to run:
`README.md`. Layer 1 (statements).

## Coverage

**All 604 items** of the comparison that are not labelled *extra* or *gap* (Chapter 1: 31, Chapter 2: 58,
Chapter 3: 95, Chapter 4: 43, Chapter 5: 42, Chapter 6: 60, Chapter 7: 64, Chapter 8: 49, Chapter 9: 60,
Chapter 10: 71, Chapter 11: 31; Chapter 6 against commit 439bc62, Chapter 7 against commit 919831f, Chapters
8–11 against commit caf6bfc; V7.57, V11.9–V11.13, V11.27–V11.29 and V11.42 are gaps and have no item). Every item has a blind statement
(`Blind/<ID>.lean`) and a prover record (`Items/<ID>.lean`, `Items/<ID>.json`); all files compile
against HEAD (commit 12924a4, recompiled 2026-11-02), no `sorry`, and every proved direction passes
`#rt_check` (or `#rt_check_soft`, or a documented `A'`-factoring, noted in the item's JSON; see
"Harness" below). 134 Opus agents (blind batches of
about 9 items, prover batches of 5–8), four at a time; the refresh of 82 items: nine more prover
agents, then three blind and three prover agents for seven second blind statements, three Lean
processes at a time. Chapter 6: 21 more Opus agents (seven blind batches of 6–9 items, fourteen
prover batches of 3–5), up to twelve at a time on the 137 GB machine. Chapter 7: 18 more Opus agents (seven blind
batches of 9–10 items, eleven prover batches of 5–6), up to seven at a time. Chapters 8–11: 54 more Opus agents
(18 blind batches of 9–13 items, 36 prover batches of 4–7), up to seventeen at a time; the 211 item files of
Chapters 8–11 were recompiled at caf6bfc (with this commit's docstring edits) on 2026-11-08.

## Results

Proved directions (vacuous directions not counted), by chapter:

| | equivalent | A ⇒ B only | B ⇒ A only | neither | B false | n |
|---|---|---|---|---|---|---|
| V1 | 15 | 13 | 0 | 1 | 2 | 31 |
| V2 | 31 | 12 | 6 | 8 | 1 | 58 |
| V3 | 1 | 54 | 0 | 36 | 4 | 95 |
| V4 | 16 | 14 | 1 | 11 | 1 | 43 |
| V5 | 7 | 13 | 4 | 17 | 1 | 42 |
| V6 | 19 | 9 | 4 | 22 | 6 | 60 |
| V7 | 39 | 6 | 8 | 6 | 5 | 64 |
| V8 | 28 | 5 | 9 | 4 | 3 | 49 |
| V9 | 6 | 17 | 10 | 22 | 5 | 60 |
| V10 | 46 | 7 | 8 | 8 | 2 | 71 |
| V11 | 11 | 9 | 3 | 8 | 0 | 31 |

Proved directions by verdict:

| | equivalent | A ⇒ B only | B ⇒ A only | neither | B false | n |
|---|---|---|---|---|---|---|
| same | 98 | 27 | 15 | 23 | 1 | 164 |
| explicit | 16 | 26 | 7 | 16 | 0 | 65 |
| narrower | 7 | 12 | 14 | 34 | 12 | 79 |
| restated | 72 | 48 | 14 | 57 | 9 | 200 |
| stronger | 26 | 46 | 3 | 13 | 8 | 96 |

Provers' judgement of content, by verdict:

| | equivalent | A_stronger | A_narrower | incomparable | n |
|---|---|---|---|---|---|
| same | 126 | 27 | 6 | 5 | 164 |
| explicit | 18 | 27 | 7 | 13 | 65 |
| narrower | 8 | 16 | 22 | 33 | 79 |
| restated | 106 | 45 | 14 | 35 | 200 |
| stronger | 25 | 48 | 7 | 16 | 96 |

Against the verdict: {'match': 320, 'mismatch': 235, 'partial': 49}

(Chapters 8–11 alone: {'match': 127, 'mismatch': 64, 'partial': 20}; Chapter 7 alone: {'match': 44, 'mismatch': 17, 'partial': 3}; Chapters 1–6 alone: {'match': 149,
'mismatch': 154, 'partial': 26}; Chapters 1–5 alone: {'match': 125, 'mismatch': 127, 'partial': 17}.)

(At the audit, with the verdicts of that time: {'match': 117, 'mismatch': 128, 'partial': 24}. The
refresh changed the result or the score of 29 items, listed in "Refreshed on 2026-11-02" below.)

Reading the tables. A ⇒ B means the project's formal statements imply the independent restatement
of the text's claim; B ⇒ A the converse. Directions proved without using their hypothesis (definition
items, where B is proved outright) are not counted; for those the result is in the JSON ("the
project's definition is the text's"). "B false" means `¬B` is proved or B was shown false (a literal
misprint, or a statement that does not hold in the formal reading, below). "A ⇒ B only" is the expected outcome whenever the formal
result is more general than the text (dropped tameness, wider domains, weaker hypotheses) or when
the comparison's declaration list bundles proof lemmas into A that the text never states — the
second is the main reason why items labelled *same/explicit/restated* come out "A ⇒ B only".
At the audit Chapter 3's many "neither" were mostly the germ/whole-chart difference and the missing
sc-level theory described below; since the refresh both are gone from A, and Chapter 3's remaining
"neither" are tameness (the blind statements assume tame bundles or tame germ data where the
project's theorems take germ data in any compatible chart, or the converse), data "for every datum"
against the project's existential data, and blind statements whose own definitions are whole-chart
(see "Refreshed on 2026-11-02").

## What the audit found

### The headline theorems imply the text's statements

For the global implicit function theorems — Theorem 3.56 (V3.86, V3.50), Theorem 3.57 (V3.87,
V3.51), Corollary 3.24 (V3.70), Theorems 3.19/3.23 at a zero (V3.95, V3.69), Theorem 3.54 (1) at
the nearby zeros with the text's sc-complement and Theorem 3.54 (2) (V3.82, V3.85, V3.94; at HEAD
against second blind statements, see "Refreshed on 2026-11-02") — `A → B` is proved, non-vacuously:
the project's theorems imply an independent formalization of the text's claim by a model that never
saw them. The blind formalizers read "tame strong bundle" as "some equivalent atlas of tame charts"
(not "every compatible chart is tame", the vacuous hypothesis of Findings Chapter 3 item 190). The
same holds for the germ implicit function theorem and local solvability (Theorems 3.29, 3.30, 3.33,
3.35, 3.38, 3.40, 3.78), the appendix (Lemmas 3.65, 3.70, 3.74, Proposition 3.69, Theorems 3.72,
3.73), Theorems 3.12, 3.15, 3.18, Theorem 4.2 (both directions), Theorems 4.18, 4.23, Theorems
5.5–5.7, and most of Chapters 1, 2 and 4, where many items are equivalent outright (the
definitions of sc-Banach spaces, sc-operators, retracts, charts, atlases, M-polyfolds, sub-M-
polyfolds, faces, strong bundles, corner structures, sc⁺-retractions).

### Statements of the text that do not hold in the formal reading (`¬B` proved)

Each `¬B` refutes a blind formalizer's reading of the text, not the text itself: if that reading
misses what the authors meant, the counterexample says nothing against the text. Which it is, is
for a human reviewer to judge.

* **Theorem 3.27, the step "δ is an sc^∞-germ near every v₀ ∈ V"** (V3.73, V3.74): does not hold
  for an arbitrary set with the tangent germ property; counter-model `M = {(t³, t)} ⊆ ℝ²` with an
  explicit datum whose `δ` is not differentiable at a point of `V` (Findings Ch. 3 item 82 stated
  this in prose; it is now proved).
* **Remark 2.28, "C_xO is in general not a partial quadrant in T_xO"** (V2.33): does not hold as
  read — `C_xO` is a partial quadrant in `T_xO` at every smooth point of every sc-smooth retract,
  tame or not (`Polyfold.remark_2_4_8_isPartialQuadrant`, `Chapter2/PartialConeQuadrant.lean`,
  proved after the audit with Flor's theorem in the needed case; Findings Ch. 2 item 50). The text
  proves the positive statement only for tame retracts (Proposition 2.36).
* **Proof of Theorem 4.23, "a finite subcover"** (V4.64): we could not see why `K` is compact;
  counter-model `X = ℝ`, `A = (−2,2)×{0} ∪ (0,2)×{1}`. The project uses a countable cover instead.
* **Theorem 5.37 (i) ⇒ (ii) as written** (V5.55): "the sc-smooth function f ∘ φ" for continuous
  `f` does not hold (`min(|x|, 1)` on `ℝ`); we take "continuous" to be meant.
* **Definition 1.8 / Lemma 1.9: "F = C ⊕ T(E_m)"**, read as `F_m` (V1.7, V1.29); as written, a
  counterexample on an explicit infinite-dimensional sc-Banach space (`ℓ²`, inclusions
  `diag(2⁻ᵏ)`).
* **Lemma 5.23 without the hypothesis we believe it leaves implicit** (V5.42): a counterexample on
  the trivial bundle.
* Possible misprints that the blind formalizers also noticed and read as intended (agreeing with
  the Findings): Theorem 5.13 "N(f(x)) ≤ 1", "(f, x)" for "(f + s, x)" (V5.29, V5.40),
  Proposition 1.7's quotient set (V1.6), Corollary 3.13's limit point (V3.15), Lemma 5.20's vacuous
  bound (V5.20).

### Where the project's definitions differ from the text's

* **Germs versus the whole chart** (V3.5, V3.9, V3.13, V3.16, V3.19, V3.43, V3.45, V3.103) —
  **removed in phase 2** (commits b74e15e–452a9b3, 2026-11-01). The audit found that the project
  required the text's §3.1 germ notions (filling, sc⁺-germ) on the chart's whole `U` (levels
  `U ∩ E_m`), which is stricter for germs whose levels shrink with the level: a function `C^k` on
  `(−1/k, 1/k)` for every `k` is a smooth germ in the text's sense and smooth on no neighbourhood
  (`¬B` proved for the literal identification in V3.43; the example is now machine-checked,
  `exists_isScSmoothGerm_not_isScSmooth`). Since phase 2 the canonical notions are the text's germ
  reading — `StrongBundle.IsScFredholmGerm` (filling `IsFillingGerm`, sc⁺-section `IsScPlusGerm`),
  `IsScFredholmSection`, their tame and good-position variants — and the theorems built on them
  (`theorem_3_1_13_preprint`, `theorem_3_1_18_preprint`, `theorem_3_1_21_preprint`, `proposition_3_6_5_preprint`, `theorem_3_1_22`,
  `theorem_3_1_26`, `theorem_3_6_8`, `theorem_3_6_10`, `theorem_3_6_11`, Chapter 5) carry the text's
  hypotheses with no added hypothesis. The whole-chart notions and theorems are kept as
  `…WholeChart` / `…_wholeChart`; they imply the germ ones. Whether the two readings agree for
  sections sc-smooth on `X` is still open (Findings Ch. 3 item 264), but no theorem depends on it.
  Definition 3.3 (`IsScSmoothSectionGerm`, V3.5), the hypothesis of no theorem, followed on
  2026-11-02 (commit 08c08c6). The item files (`RoundTrip/Items/`) were refreshed against HEAD on
  2026-11-02, where the canonical names denote the germ reading: the filling, Definition 3.3 and the
  sc⁺-germ now agree with the text (V3.5, V3.7, V3.9, V3.43), and what is left of Definition 3.11 is
  the tame chart (V3.13, V3.16; see "Refreshed on 2026-11-02") (Findings Ch. 3 items 220–221,
  260–266, 330–334).
* **Good complement** (V3.20): the project's `IsGoodComplement` accepts a non-closed algebraic
  complement (`¬B` with `ℓ²` and the kernel of a discontinuous functional); "text's good complement
  = project's + closed" is proved. Findings Ch. 3 item 19 records the choice. Where good position is
  a *conclusion*, the upgrade from the project's algebraic complement to the text's sc-complement
  turned out to be glue, not new mathematics (V3.82, V3.85, V4.38, V4.42: a closed complement of a
  smooth finite-dimensional kernel inside an sc-subspace gives an sc-complement).
* **Bump functions** (V5.16, V5.17, V5.20, V5.44, V5.51; Findings Ch. 5 item 41): the text's
  Definitions 5.9/5.29/5.33 say "f ≠ 0" (not identically zero); the project reads `f(x) ≠ 0`, which
  Proposition 5.30's proof needs. This one word is the only obstacle to A ⇒ B in Theorems 5.13,
  5.18, 5.19, 5.25, 5.34 once the misprints are corrected. Since 2026-11-02: on an sc-Banach space
  weak bumps give pointwise ones at every smooth point (`AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth`),
  on Hilbert models both readings hold everywhere (`admitsBumpFunctions_of_hilbert`), and the weak
  reading follows from the density of the points with a pointwise bump (`admitsBumpFunctionsWeak_of_dense`);
  whether weak bumps give a bump non-zero at a non-smooth point is open (Findings Ch. 5 items 160–163).
* Tameness: the project drops the text's tameness hypotheses wherever its proofs do not use them
  (Theorems 3.12, 3.15, 3.27, 4.2, 5.5, 5.7; Definition 5.20's homotopies need only `X` tame,
  V5.41); the blind statements keep them, so `B → A` fails for a reason that favours the project.

### Missing in the project (A ⇏ B), each believed true unless marked

* **sc-Fredholm theory on all levels**: Proposition 3.10, 3.52, Theorem 3.19 "f'(x₀) sc-Fredholm",
  the index on the solution set (V3.12, V3.46, V3.68, V3.96–V3.100) — the project proves the level-0
  (classical) statements (added later: `proposition_3_1_10_level`, `proposition_3_6_5_sc`,
  `theorem_3_1_22_linearization_sc`, `StrongBundle.linAt_isScFredholm` in every chart,
  `theorem_3_6_8_index_locally_constant_general` under tame germ data and bump functions; see
  "sc-Fredholm theory on all levels, added afterwards" below). Corollary 5.8 "f^i is sc-Fredholm on
  P^i" (V5.13, V5.14) and Proposition 6.2 along paths (V3.98 (a)) were added on 2026-11-02, see
  "Added on 2026-11-02" below; what is still open is listed there. Since the refresh `A ⇒ B` is
  proved for V3.12, V3.46, V3.96 from the added results.
* **Theorem 3.27** needs the regularity of the tangent germ data (V3.24, V3.72; the text's proof
  fails without it, see above); **Theorem 3.54 graph form** for every datum (V3.48, V3.80, V3.84).
* **Proposition 2.21 (3)–(4)** on `T_aX` (V2.25, gap G.7); level charts for `m ≥ 2` (V2.16, G.6;
  the levels of `X¹` are those of `X` shifted, as sets, since 2026-11-02,
  `MPolyfold.mem_shift_levelSet_iff`); `p : TX → X₁` open (V2.20, G.8); Proposition 2.54's "natural" (`f*Y → Y` a strong bundle map;
  V2.61); transitivity of strong-bundle-atlas equivalence (V2.58); **restriction of strong bundle
  charts** (built in V5.4, ~200 lines) (both added later: `StrongBundleAtlas.Equiv.trans`,
  `StrongBundleChart.restrict`, commit f063505); Theorem 4.22's local faces of a neighbourhood (V4.50);
  Remark 4.14's good-position claim without tameness (V4.32).
* Examples the text asserts: an sc¹ map with `Df` not norm-continuous (V1.13, V1.34) (added later:
  `exists_isSc1_not_continuousOn_deriv`, `Chapter1/ScOneNotNormContinuous.lean`); an M-polyfold
  with `X₀ = X_∞` where `1₀¹` is not an sc-diffeomorphism (V4.6); `Γ^{+,1}_U` not complete (V5.21)
  (both added on 2026-11-02: `remark_4_1_3_example`; `TrivialBundle.not_completeSpace_allowableSections`,
  with the correction that "not complete" needs a hypothesis; see below; since the refresh `A ⇒ B`
  is proved for V1.13, V1.34, V4.6, V5.21).
* Proved in the audit and missing in the project (all added later: Remark 5.12, Lemma 3.9 and
  Lemma 3.81 in commit f063505 — `remark_5_3_4_of_isScFredholmSection`,
  `IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le`, `Radii.norm_τ_sub_le_global`; the rest as
  marked): the closedness of the solution set in Remark 5.12
  (V5.22, flagged in the project's docstring); Lemma 3.9 with level-`m` smallness (V3.11; the
  docstring says level-1 smallness is needed — it is not); the Lipschitz estimate of Lemma 3.81 on
  all of `V₀` (V3.66; the docstring says only near `k₀`); Corollary 3.34's single germ for all `k`
  (V3.31, V3.32) (added later: `corollary_3_3_7_isScSmoothGerm`, `theorem_3_35_isScSmoothGerm_preprint`,
  `theorem_3_35_of_isSc0ContractionGerm_preprint`, `isSckGerm_of_levels`, `Chapter3/GermIFTSmooth.lean`);
  "f⁽¹⁾ is a Definition 3.28 contraction germ" (V3.28) (added later:
  `ContractionGerm.isSc0ContractionGerm_next`).

### Moved into the project after the audit (commit f063505)

* `Chapter3/GoodPositionSc.lean`: Definitions 3.21 and 3.53 with the text's sc-complement, the
  upgrade from the project's algebraic good complement at a zero, and Theorems 3.54 (1), 3.23,
  3.56, 3.57, Corollary 3.24 in the text's form (Findings Ch. 3 items 210–214).
* `Chapter2/StrongBundleRestrict.lean`, `Chapter3/StrongBundleMaximalAtlas.lean`: restriction of
  strong bundle charts, locality of compatibility, equivalence of strong bundle atlases (and of
  M-polyfold atlases: `MAtlas.Equiv.trans` was missing too) as equivalence relations; `IsChart`
  characterised by the class (Findings Ch. 2 items 40–43). `Chapter5/AuxNormLiteral.lean`: Lemma 5.2
  in the text's literal form (item 44).
* `Chapter5/SolutionSetClosed.lean`: Remark 5.12 as stated (Findings Ch. 5 items 130–131); Lemma 3.9
  with smallness on level `m` and Lemma 3.81's estimate on all of `V₀`, with the docstrings that said
  otherwise corrected (Findings Ch. 3 items 215–217).

### sc-Fredholm theory on all levels, added afterwards (same day)

* `Chapter3/BasicGermLinearizationLevel.lean`: Proposition 3.10's second statement on every level
  `m` (`proposition_3_1_10_level`; V3.12's clause (ii), checked against the blind statement in a
  scratch file).
* `Chapter1/ScFredholmCriterion.lean`: an sc-operator is sc-Fredholm iff it is Fredholm on level 0
  and regularizing (`isScFredholm_iff`); restrictions to sc-subspaces (`IsScFredholm.restrict`).
* `Chapter3/FredholmGermLinearizationSc.lean`: Propositions 3.5 and 3.52 and Theorem 3.19's
  "`f'(x₀)` is sc-Fredholm" in the chart centred at the zero (V3.46, V3.68, V3.96 in that chart;
  every chart: next bullet). Findings Ch. 3 items 230–236.
* `Chapter3/LinearizationChartsSc.lean`: the linearization at every zero is sc-Fredholm in every
  chart (`StrongBundle.linAt_isScFredholm`; V3.46, V3.96), filler condition (3) on every level at a
  zero, the converse of Proposition 3.5 in sc form, the index locally constant in sc form (V3.98
  under good position). Findings Ch. 3 items 237–239.
* `Chapter3/IndexLocallyConstant.lean`: the index locally constant along the zero set without good
  position, for tame germ data and bump functions (V3.98 (b) under these hypotheses; the general
  case is open, Findings Ch. 3 items 240–244).
* Since phase 2 (above) these files hold the whole-chart forms (`proposition_3_6_5_sc_wholeChart`,
  `StrongBundle.linAt_isScFredholm_wholeChart`, …); the names cited here that take sc-Fredholm
  germ data denote the germ-reading forms in the `…G.lean` files beside them (`FredholmGermLinearizationScG.lean`,
  `LinearizationChartsScG.lean`, `IndexLocallyConstantG.lean`; Findings Ch. 3 items 289–290,
  314–315, 331).

### Added on 2026-11-02 (commit 08c08c6; the fourth addendum of the comparison)

* **Corollary 5.8** (V5.13, V5.14; gap G.41; Findings Ch. 5 items 140–146): the shifted strong
  bundle `P¹ : Y¹ → X¹` (`StrongBundle.shift`: total space `Y_{1,1}`, the index raises of the strong
  bundle charts as atlas; `Chapter5/StrongBundleShift.lean`); `f¹` is an sc-Fredholm section of it
  with compact solution set (`corollary_5_2_5`), `f²` of `P² = (P¹)¹` (`corollary_5_2_5_two`), every
  fixed `i` by iteration; the filler condition (3) on level `1`, which "it is a priori clear" hides,
  is proved for every datum of Definition 3.11 (`IsFillingGerm.germ_shift`,
  `Chapter5/Corollary58.lean`). No added hypothesis; tameness not used.
* **Definition 6.1 and Proposition 6.2** (V3.98 (a); Findings Ch. 3 items 340–348):
  `StrongBundle.IsIndexAt` (well defined without Proposition 1.10), `proposition_6_2_2` by the text's
  device, for tame germ data on M-polyfolds admitting bump functions and sc-smooth paths `ℝ → X`
  (`Chapter3/IndexAlongPaths.lean`, `Chapter3/IndexAlongPathsDevice.lean`). Item 243 sharpened: the
  candidate counterexample of items 188, 243 is excluded under tame germ data (item 343).
* **Proposition 6.2 without bump functions** (V3.98; commit 12924a4; Findings Ch. 3 items 349,
  360–367): restriction of M-polyfolds and strong bundles to open sets (`StrongBundle.restrictOpen`),
  Definition 6.1 with the text's locally defined sections (`StrongBundle.IsIndexAtLocal`, agreeing
  with `IsIndexAt` under bump functions, `isIndexAtLocal_iff_isIndexAt`), the index locally constant
  along the zero set for tame germ data (`index_locally_constant_tame`) and Proposition 6.2 with the
  text's hypotheses (`proposition_6_2_2_local`; `Chapter3/IndexAlongPathsLocal.lean`).
* **Remark 4.3's example** (V4.6; gap G.31; Findings Ch. 4 items 140–146): `remark_4_1_3_example`, an
  M-polyfold with `X₀ = X_∞` and `1₀¹` not sc-smooth (even the topologies of `X` and `X¹` differ),
  from a retraction that loses a level, sc-smooth by a new criterion (`IsLossFamily.isScSmooth`,
  `Chapter4/RemarkFourThreeExample.lean`, `Chapter4/RemarkFourThreeFamily.lean`).
* **The allowable sections** (V5.21; gap G.42; Findings Ch. 5 items 150–153): `ρ` is a metric
  (`StrongBundle.allowableMetric`); `(Γ^{+,1}_U(P), ρ)` is not complete for the trivial bundle
  `ℝ × ℝ → ℝ`, and is complete for `U = ∅` and over a point, so the text's "not complete" needs a
  hypothesis (`Chapter5/AllowableSectionsMetric.lean`).
* **Item 199** (V3.13, V3.103; Findings Ch. 3 items 350–355): re-centring a chart of a tame atlas
  cannot give tame germ data — a filling needs `ker Dr(0) ≅ ker ρ(0)` in its chart, and a tame
  one-chart atlas of the trivial bundle carries no germ data (`tame_atlas_no_germData_in_atlas_chart`,
  `Chapter3/TameGermData.lean`). **Bump functions** (V5.16; Findings Ch. 5 items 160–164): see
  "Bump functions" above (`Chapter5/BumpWeakPointwise.lean`). **Definition 3.3** in the germ reading
  (V3.5).

**Still open after 2026-11-02** (each believed true unless marked; none is the hypothesis of a
theorem of the project):

* whether the text's germ reading and the project's earlier whole-chart reading of Definition 3.11
  agree for sections sc-smooth on `X` (Findings Ch. 3 item 264); no theorem depends on it;
* the remaining implication of item 199: germ data in some compatible chart ⟹ germ data in some
  compatible tame chart, when the atlas consists of tame charts (Definition 3.11 ⟹ Definition 3.50;
  Findings Ch. 3 item 353; neither a proof nor a counterexample is known);
* whether weak bump functions give a bump non-zero at a non-smooth point (Findings Ch. 5 item 163;
  open both ways);
* the tameness of the index raises of tame charts (the tame form of Corollary 5.8: germ data of `f¹`
  in tame charts of `P¹`; no counterexample known), and a uniform family `P^i` indexed by `i`, with
  `(X¹)¹` identified with `X₂` as a topological space (gap G.6) (Findings Ch. 5 items 145, 146);
* item 243 for non-tame germ data: the local constancy of the index along the zero set without tame
  germ data, where it is equivalent to `ind C(z) = 0` for the normal block of the filling at the
  nearby zeros (Findings Ch. 3 items 243, 343; open, not believed either way).

### Refreshed on 2026-11-02 (against HEAD, commits d0b6817 and 12924a4)

The audit was run against the project before commit b4d1d8c. Since then (452a9b3 … d0b6817)
Definitions 3.3 and 3.11 and the notions built on them were switched in place to the text's germ
reading (142 theorems swapped names: old `X` → `X_wholeChart`, germ `X_germ` → `X`; the phase-2
names survive as aliases, `Chapter3/GermReadingAliases.lean`), and the comparison rows gained
declarations (the audit's glue moved into the project, sc-level theory, Remark 2.28, Corollary 5.8,
Proposition 6.2, Remark 4.3's example, the metric `ρ`). The inputs were regenerated
(`make_inputs.py`), all 269 blind statements recompiled unchanged against HEAD (none edited; none
needed a repair), and the affected items were redone by nine prover agents following
`PROVER_PROMPT.md` (A restated from the current row, both directions retried, `#rt_check` with the
current list banned). Each refreshed JSON has a `refresh` field with the record before and a note.

**Affected items (82)**, by reason (an item can have several):

* A's declaration list changed since the audit (50): V1.2, V1.8, V1.9, V1.13, V1.34, V2.11, V2.16,
  V2.33, V2.37, V2.57, V2.58, V3.5, V3.7, V3.8, V3.9, V3.11, V3.12, V3.13, V3.16, V3.19, V3.20,
  V3.28, V3.31, V3.32, V3.43, V3.45, V3.46, V3.47, V3.66, V3.68, V3.70, V3.81, V3.82, V3.86, V3.87,
  V3.94, V3.95, V3.96, V3.97, V3.98, V3.99, V3.103, V4.6, V5.4, V5.13, V5.14, V5.16, V5.21, V5.22,
  V5.30.
* A theorem of A states the germ reading in place, under its old name (49; found by the statement
  closure of each declaration): V3.5, V3.13–V3.18, V3.46–V3.48, V3.68–V3.70, V3.77, V3.80–V3.82,
  V3.84–V3.87, V3.91, V3.92, V3.94–V3.101, V3.103, V3.105, V3.106, V5.10–V5.14, V5.22, V5.29, V5.30,
  V5.36, V5.38–V5.41, V5.45, V5.46.
* B uses a project notion that switched (`IsScFredholmGerm`, `IsScFredholmSection(Tame)`,
  `IsGoodPositionGermTame`, `IsScSmoothSectionGerm`; 52 items, mostly the same as above, plus V3.45,
  V3.50, V3.51, V3.74, V5.42, V5.44). The blind formalizers took these for the text's notions, which
  they now are; where B's *own* definitions are built from whole-chart pieces next to them, see
  "needs a new blind statement" below.
* The verdict changed (11): V2.33 same → stronger; V3.11, V3.12, V3.66, V3.96, V4.6 narrower →
  stronger; V3.19 restated → stronger; V3.46 narrower → restated; V5.4 restated → same; V5.13, V5.14
  narrower → same. The text quoted by the row changed for V3.98 and V5.14.
* The item file no longer compiled at HEAD (16, repaired): V3.5, V3.13, V3.45, V3.51, V3.69, V3.70,
  V3.82, V3.84, V3.85, V3.87, V3.94–V3.97, V3.100, V3.103 (renamed theorems; the germ form of
  `isGoodPositionGerm_of_chart` needs a germ through the centre of the chart, so the glue now goes
  through `isGoodPositionGerm_of_linAt_surj`).

**Changes of the result** (29 of the 82, counting the second blind statements below; the other 53
keep their relation and score, with names, A and the diagnosis brought up to date). `proved` counts
non-vacuous directions; the score is against the current verdict (before: the audit's record against
the verdict at the audit):

| item | verdict | proved | content | against the verdict |
|---|---|---|---|---|
| V1.9 | same | equivalent → **A ⇒ B only** | equivalent → **A_stronger** | match → **mismatch** |
| V1.13 | explicit | B ⇒ A only → **equivalent** | A_narrower → **equivalent** | mismatch → **match** |
| V1.34 | restated | neither → **A ⇒ B only** | incomparable → **A_stronger** | mismatch |
| V2.33 | same → **stronger** | B false | A_narrower → **incomparable** | mismatch → **partial** |
| V2.58 | restated | neither → **A ⇒ B only** | incomparable → **A_stronger** | mismatch |
| V3.5 | explicit | neither | A_narrower → **equivalent** | mismatch → **match** |
| V3.8 | stronger | neither → **A ⇒ B only** | incomparable → **A_stronger** | partial → **match** |
| V3.9 | restated | neither | A_narrower → **equivalent** | mismatch → **match** |
| V3.11 | narrower → **stronger** | neither → **A ⇒ B only** | incomparable → **A_stronger** | partial → **match** |
| V3.12 | narrower → **stronger** | neither → **A ⇒ B only** | incomparable → **A_stronger** | partial → **match** |
| V3.13 | restated | neither | incomparable → **A_narrower** | mismatch |
| V3.15 | restated | neither → **A ⇒ B only** | incomparable → **A_stronger** | mismatch |
| V3.16 | same | neither | incomparable → **A_narrower** | mismatch |
| V3.19 | restated → **stronger** | neither → **A ⇒ B only** | incomparable → **A_stronger** | mismatch → **match** |
| V3.43 | same | B false | A_narrower → **equivalent** | mismatch → **match** |
| V3.45 | same | neither | A_stronger → **A_narrower** | mismatch |
| V3.46 | narrower → **restated** | neither → **A ⇒ B only** | incomparable → **A_stronger** | partial → **mismatch** |
| V3.66 | narrower → **stronger** | A ⇒ B only | A_stronger | mismatch → **match** |
| V3.81 | narrower | neither | incomparable → **A_stronger** | partial → **mismatch** |
| V3.92 | restated | neither → **A ⇒ B only** | incomparable → **A_stronger** | mismatch |
| V3.94 | restated | neither → **A ⇒ B only** | incomparable → **A_stronger** | mismatch |
| V3.96 | narrower → **stronger** | neither → **A ⇒ B only** | incomparable → **A_stronger** | partial → **match** |
| V3.100 | explicit | neither → **A ⇒ B only** | incomparable → **A_stronger** | mismatch |
| V4.6 | narrower → **stronger** | B ⇒ A only → **A ⇒ B only** | A_narrower → **A_stronger** | match |
| V5.4 | restated → **same** | A ⇒ B only | A_stronger | mismatch |
| V5.13 | narrower → **same** | neither → **A ⇒ B only** | incomparable → **A_stronger** | partial → **mismatch** |
| V5.14 | narrower → **same** | neither → **A ⇒ B only** | incomparable → **A_stronger** | partial → **mismatch** |
| V5.16 | restated | neither | equivalent → **A_stronger** | match → **mismatch** |
| V5.21 | restated | neither → **A ⇒ B only** | A_narrower → **A_stronger** | mismatch |

* **A ⇒ B newly proved** (non-vacuously): V1.13, V1.34 (`exists_isSc1_not_continuousOn_deriv`),
  V2.58 (`StrongBundleAtlas.equivalence`), V3.8 (Proposition 3.5 for fillings), V3.11 and V3.19 (until
  now proved only by proving B outright), V3.12 (`proposition_3_1_10_full`), V3.15 (the text's germ
  notion implies the project's: shrinking the chart into `U₀`, `Ψ` and the basic germ restricted),
  V3.46 and V3.96 (`StrongBundle.linAt_isScFredholm` in every chart), V3.92 (non-centred charts by
  `StrongBundleChart.recentre`), V4.6 (`remark_4_1_3_retract_example`), V5.21
  (`TrivialBundle.not_completeSpace_allowableSections`, with `ρ = allowableDist`).
* **Definition items now agree**: Definition 3.3 (V3.5), the filling (V3.7, V3.9, V3.43:
  `IsFillingGerm` is the text's filling field for field). In V3.13, V3.16 the filling and the
  sc⁺-germ now agree both ways; what is left is the text's tame chart against the project's any
  compatible chart (Findings Ch. 3 item 353, open) and two pieces of glue not attempted there (`Ψ`
  on `U₀ ⊆ U`, done in V3.15's item file; `ℝⁿ` against an abstract `Pn` in the conjugation), so the
  project's Definition 3.11 is the broader one (A_narrower). V3.45 turned from A_stronger to
  A_narrower: its blind statement reads "local sc⁺-section" as sc-smooth on a relatively open `U₀`,
  stricter than the project's germ (and than V3.13's blind statement).
* **B ⇒ A lost because A grew** by results B does not state (auxiliary or more general): V1.9 (the
  criterion `isScFredholm_of_isRegularizing`), V2.33 (Flor's theorem; A now refutes B,
  `A_to_not_B`), V4.6, V5.16, V5.21 (the specific example and the point case).
* **Against the first blind statements** V3.82 and V3.85 had lost `A ⇒ B` and V3.94 stayed failed:
  their own good position at the nearby zeros (`IsGoodPositionGermSc`, `IsGoodPosData`, defined in
  the blind files) was built from `IsFilledVersion`, `IsScSmooth c.U s`, `ConjugationData c.U` — the
  whole-chart reading — while their hypothesis `IsScFredholmSectionTame` is now the germ reading.
  With that conclusion read on germs `A ⇒ B` was proved (`A_to_Bgerm_r1`). The second blind
  statements (below) settle these items.
* **Unchanged**: the global implicit function theorems and the theorems at a zero (V3.50, V3.51,
  V3.69, V3.70, V3.86, V3.87, V3.95), Theorems 3.12, 3.15, 3.18 and their tame forms (V3.14,
  V3.17, V3.18, V3.91, V3.105, V3.106), Theorems 5.5–5.7, 5.13–5.25 (V5.10–V5.46): `A ⇒ B` where it
  was proved is still proved and uses its hypothesis, now with the germ reading on both sides; the
  remaining failures are tameness (the blind statements assume tame bundles or tame germ data,
  every project IFT needs tame germ data where V3.68, V3.97, V3.99, V3.101 assume only Definition
  3.14), weak against pointwise bump functions, the text's misprints, and data "for every datum"
  against the project's existential ones (V3.48, V3.77, V3.80). V3.81 is now effort only (the smooth
  kernel at nearby zeros follows from `linAt_isScFredholm`, `linAt_chart_independence`,
  `linAt_eq_germDeriv`; a few hundred lines of glue not written).

**Second blind statements (same day).** Seven first blind statements no longer meant the text
under the current definitions or did not cover the row: V3.82, V3.85, V3.94, V3.100 (their own good
position was whole-chart, see above), V5.13, V5.14 (they predated `StrongBundle.shift` and built the
level-`i` germ data of `f^i` from whole-chart pieces next to a germ-reading hypothesis, so at `i = 0`
they claimed "germ data ⇒ whole-chart data"), V3.98 (the row now quotes Definition 6.1 at every
smooth point and Proposition 6.2 over a tame M-polyfold; the first B covered only zeros of `f`). New
blind statements were written by `harness/BLIND_PROMPT.md` (three blind agents, the text's statement
and a regenerated `vocab.md` only, the superseded files of their own IDs closed to them) as
`Blind/<ID>_r2.lean` (`RoundTrip.<ID>_r2.B`); the first ones are kept. The provers redid the items
against them (`PROVER_PROMPT.md`, `#rt_check`); each JSON names the current blind statement
(`blind_current`) and keeps the record against the first one (`blind_r1`):

| item | A ⇒ B | B ⇒ A | relation | against the first blind statement |
|---|---|---|---|---|
| V3.82 | proved | failed | A_stronger | neither, incomparable |
| V3.85 | proved | failed | A_stronger | neither, incomparable |
| V3.94 | proved | failed | A_stronger | neither, incomparable |
| V3.100 | proved | failed | A_stronger | neither, incomparable |
| V5.13 | proved | failed | A_stronger | neither, incomparable |
| V5.14 | proved | failed | A_stronger | neither, incomparable |
| V3.98 | failed | failed | incomparable | neither, incomparable |

* V3.82, V3.85, V3.94: the blind statements now use the project's germ-reading
  `IsGoodPositionGermSc` and an equivalent tame atlas; Theorem 3.54 (1) gives good position at the
  nearby zeros (through `isGoodPositionGermFilled_of_isGoodPositionGerm` and the sc-complement upgrade
  `IsGoodPositionGermTame.isGoodPositionGermSc`), (2) the sub-M-polyfold with corner structure
  (`theorem_3_6_8_two`, `TangentGermChart.shrink`, `theorem_3_2_3_of_isRegular`). V3.100: at `d_X(x) = 0` (and for
  `∂X = ∅`) good position ⟺ `f'(x)` onto, by `isGoodPositionGermSc_iff` and A. B ⇒ A fails in all four:
  A needs no tame bundle and contains chart-level lemmas.
* V5.13, V5.14: the blind statements build `P^i` by iterating the project's `StrongBundle.shift` and
  `sectionShift` (so a wrong shift construction would not be caught here); A ⇒ B for every `i` by
  induction over `corollary_5_2_5` / `corollary_5_2_5_isScFredholmSection` on `P^i` (V5.14 with
  `#rt_check_soft`: `StrongBundleChart.Compatible.shift` is reached only through the proof fields of
  `StrongBundle.shiftAtlas`). B ⇒ A fails: A holds without tameness and has side lemmas.
* V3.98 (its row now also cites `proposition_6_2_2_local`, `IsIndexAtLocal`,
  `isIndexAtLocal_iff_isIndexAt`, `index_locally_constant_tame`): A gives B's Definition 6.1 (the
  index exists and is independent of the section and the chart, level 0) and the local constancy
  along the zero set (`B0_of_A`, `Ba_of_A`); B's Proposition 6.2 fails only because B assumes
  sections of Definition 3.14 over a tame M-polyfold (no tame germ data; the project has no lemma
  producing them) and a path sc-smooth near `[0, 1]` (the project's path is sc-smooth on `ℝ`); with
  these two hypotheses A gives it (`Bb_of_tame_global`). Recorded in `B_issue` as the blind author's
  own doubt. V3.68's row now also cites `StrongBundle.linAt_isScFredholm`: B's first clause follows
  from A; the tameness gap of the second clause is unchanged (incomparable).
* Clause-level `B_issue`s remain, harmless for the result: V3.9 (b) and V3.43 equate the text's
  filling with `IsFilledVersion` (now the whole-chart special case; the row's `IsFillingGerm` is proved
  to be the text's); V3.74 claim (2) (weaker than the text; `¬B` unaffected); V3.46, V3.48, V3.97 (B
  covers fewer germs than the text).

**Harness.** V4.6: A's statement mentions `RemarkFourThreeData`, whose `IsLossFamily.retraction`
calls the banned `IsLossFamily.isScSmooth` in a proof field not abstracted as `_proof_N`, so
`A_to_B` is checked as `A'_to_B` (as in V2.24). V2.58: `StrongBundle.maximalAtlas` contains the
banned `IsChart.compatible` in its body; the checked proof is `A_to_B_core` from the five original
conjuncts. V2.57 needs `#rt_check_soft` (`StrongBundleChart.restrict`); V2.33's `¬B` uses A's own
theorems, the checked statement is `A_to_not_B`. **For the project**: the restriction of a strong
bundle chart *into* a given `U₀` (built in `Items/V3_15.lean` with `restrictIn`) is what the
docstrings of `GermFillingChart.lean`/`GermVsChart.lean` attribute to `StrongBundleChart.restrict`,
which gives `U ∩ r⁻¹(φ(s))`, not necessarily inside `U₀`; `StrongBundle.linAt_isScFredholm` settles
the sc-level claims of V3.68 and V3.98 but is not cited in their rows.

**Full recompile** (2026-11-02, after commit 12924a4 and the second blind statements: all 269 item
files, `lake env lean`, at most three at a time; log `rt3/logs/final/` in the session scratchpad):
all 269 compile with no error, no `rt_check FAIL`, no `sorry` (486 `rt_check`/`rt_check_soft` OK
lines; 11 items prove no direction and have no check, as in their records; only linter and
deprecation warnings, in 9 files). The seven `Blind/<ID>_r2.lean` compile, and so do the 269 first
blind statements (unchanged).

### Chapter 6, audited on 2026-11-07 (commit 439bc62)

The 60 items of `Exposition/cmp/ch06.json` not labelled *extra* (V6.29, V6.36, V6.53, V6.54 are
extra). Every blind statement and item file compiles at 439bc62 (all 60 item files recompiled at the
end: no error, no `rt_check FAIL`, no `sorry`). Chapter 6: 19 equivalent, 9 A ⇒ B only, 4 B ⇒ A
only, 22 neither, 6 B false.

**Statements of the text that do not hold in the formal reading.** Each agrees with a reading the
project already records (`Exposition/Findings.md`, Chapter 6).
* V6.11 (Lemma 6.10): the lemma holds (A ⇒ B); the construction of its proof, formalized separately
  as `B_proof`, is refuted (`not_B_proof`, on ℝ² with `T = id`), and the project's
  `lemma_6_10_text_reading_preprint` implies the refutation (Findings, item 4).
* V6.40 (the stabilization principle without the sign `(−1)^{dim coker}` of formula (94)): `not_B`,
  from the project's `StabCounterexample` moved to `[0, 1]` (Findings, item 50).
* V6.41: `push_eq_iff` — the text's unsigned push-forward equals the project's exactly when
  `dim coker T₀` and `dim coker T₁` have the same parity, which changes in a finite-dimensional model
  (`not_B` not formalized; counted as *neither*).
* V6.44 (Proposition 6.32) and V6.47 (Lemma 6.34), the unsigned push-forward: counterexamples on
  paper on `X = ℝ` with the trivial bundle (the sections `s = 0` and `s′ = t·y`; the cokernel
  dimension jumps at `t = 1`); not formalized, since the whole instance would be needed.
* V6.49 and V6.52 (the composition of paths with `ψ(β(s))` on `[1/2, 1]`): `not_B` at `s = 1/2`; with
  `ψ(β(s) − 1)` (`BIntended`) the project's statements imply the text's.
* V6.62 (Remark 6.42): `not_B` (`A → ¬B`): with `L₀ = 0` and `L₁ = id` in `Lin(f, 0)` on the trivial
  bundle `ℝ¹ × ℝ¹`, the literal `h ↦ h̃` is not continuous; the project's `extDetN` carries the sign
  `(−1)^{dim coker L}` (Findings, items 95–97).

**Where the readings differ** (most of the *neither*).
* *Contractible neighbourhoods* (gap G.61; V6.48, V6.50, V6.55–V6.61). The blind statements use
  sc-smoothly contractible open sets, the project pairs `V ⊆ U` and property (∗) on every open
  propagation neighbourhood. Contractible ⇒ pair is glue (`exists_path_of_contractible`, V6.59). The
  converse needs a basis of sc-smoothly contractible open sets at the smooth points, which neither
  the text nor the project supplies; with such a cover assumed, the uniqueness of `Γ_f` and
  6.38 ⇔ 6.39 carry over (V6.57 `A_to_BExtra`, V6.59 `D638_of_D639_of_A`), and without it (∗) on the
  contractible sets alone does not exclude a functor twisted by `ℤ/2` (V6.57).
* *Property (P)*: general position of the slices `F_t` in the text against that of the parametrized
  section near `[0, 1]` in the project (V6.33, V6.39, V6.42, V6.43); bridging it is Lemma 6.30 work.
* Lemma 6.19 (gap G.59) blocks V6.22 A ⇒ B and V6.23 (effort only); the manifold statements of
  Lemma 6.30 (gap G.62) V6.34; tame germ data (`IsScFredholmSectionTame` in Chapter 6 against
  `IsScFredholmSection` with `PX.IsTame` in the blind statements, no bridge) V6.46, V6.61.
* Extra hypotheses of A, all satisfiable: bump functions, `HasScPlusSectionsThrough`, tame germ data,
  paracompactness instances (V6.30–V6.33, V6.48, V6.55, V6.57, V6.58). The project's `Lin(f, x)` is
  made with global sc⁺-sections where the text's are local (V6.1, *B ⇒ A only*).
* Generality: the §6.3 lemmas drop completeness and Fredholmness (V6.10, V6.12, V6.16, V6.18,
  *A ⇒ B only*).

**Missing in the project, believed true.**
* Every operator of the ball of an admissible triple `(T, P, ε)` is Fredholm, which the text's "γ maps
  onto `DET(T, P, ε)`" needs; proved in `Items/V6_24.lean` (`chart_isFredholm`, about 60 lines).
* In an orientable neighbourhood `HasScPlusSectionsThrough` is redundant:
  `linSet_nonempty_of_localPropagation` (`Items/V6_50.lean`).
* V6.12 B ⇒ A through `E/ker T` and the closed range theorem (effort only); Lemma 6.19, the manifold
  statements of Lemma 6.30 and contractible propagation neighbourhoods (above).

**Blind statements doubted in their own generality** (recorded as `B_issue`, not decided): V6.34,
V6.37, V6.38 quantify over every chart point while their sections are sc⁺ only near `[0, 1] × U`,
where the chart linearization is the junk value `0` (`kerProd_eq_TProd_of_not_isSc1`,
`B_concl_forces_Phi_zero`); V6.61 where its Definition 6.40 is vacuous; V6.1, whose clauses imply
global sc⁺-sections.

**Harness.** Banned theorems inside definitions (`directSumVec`, `ScPathClass.comp`, `Orx`, `extDet`,
`SubspaceFamily.contEquiv`, `ChartPoint.detLin`) were handled as before by `#rt_check_soft`, an `A′`
factoring or a local `#rt_check_except_defs`, with the plain check's failure kept by `#guard_msgs`;
the JSON of each item says which. Cost: about 5.4M agent tokens (Opus 5.5), roughly 7% of a week's
budget.

### Chapter 7, audited on 2026-11-07 (commit 919831f)

The 64 items of `Exposition/cmp/ch07.json` not labelled *extra* or *gap* (V7.4, V7.18, V7.24 are
extra; V7.57, Remark 7.2, is a gap). Part II has no preprint: its blind inputs quote the 2017 book
(arXiv 1707.08941; `harness/make_inputs.py`). Every blind statement and item file compiles at
919831f (all 64 item files recompiled at the end: no error, no `rt_check FAIL`, no `sorry`).
Chapter 7: 39 equivalent, 6 A ⇒ B only, 8 B ⇒ A only, 6 neither, 5 B false. Three of the
*neither* are definition items (V7.26, V7.49, V7.56): A = True, both directions are vacuous, and
`B_holds` proves that the project's definition is the text's.

**Statements of the text that do not hold in the formal reading (`¬B` proved).** Each agrees with
a reading the project already records (`Exposition/Findings.md`, Chapter 7).
* V7.10 (the remark after Definition 7.7, "sc-smooth on objects suffices"): `not_B` by the project's
  `remarkFunctor` on `ℤ/3 × ℝ ⇉ ℝ`; with `Continuous f₁` added (`BRepaired`) B ⇔ A (Findings,
  items 9, 104). The blind formalizer found a counterexample of the same kind (`ℤ/2 ⋉ ℝ`) on its own.
* V7.40 (Proposition 7.10; the same claim is V7.39, Proposition 7.9): `𝐗^R` need not be Hausdorff.
  `Items/V7_40.lean`, namespace `NotB`: `ℤˣ` acting by `(t, z) ↦ (t, ±z)` on the dimension-jumping
  sc-retract of Remark 4.3 (`RemarkFourThree.fam`: a point over `t ≤ 0`, a line over `t > 0`), as
  `actionEpGroupoid`; `(−1, (t, 0)) ∈ 𝐗^T` for `t < 0` but `(−1, (0, 0)) ∉ 𝐗^T`, so the classes of
  `(±1, (−1/(n+1), 0))` converge to both `[(−1, 0)] ≠ [(1, 0)]` (`NotB.not_t2 : ¬ T2Space
  Xg.ReducedMor`; axioms propext, Classical.choice, Quot.sound). With `𝐗^R` Hausdorff and
  paracompact, A ⇒ B (`A_to_B_of_hyp`): the hypotheses the project adds are exactly what is missing.
  This settles the Hausdorff half of gap G.71 negatively; the example was on paper in `PLAN.md`
  (II.6, item 2), and the blind formalizer of V7.39 found it independently. V7.39 (*B ⇒ A only*)
  was not refuted separately; V7.40's example applies to it. Moved the same day into
  `Polyfold/Chapter7/ReducedNotHausdorff.lean` (`EpGroupoid.Examples.JumpingRetract.not_t2Space_reducedMor`;
  `Exposition/Findings.md`, Chapter 7, item 107).
* V7.22 and V7.27 (pp. 231–237: `Γ` a functor; Proposition 7.6): with "natural representation"
  read from Theorem 7.1 as printed, where `U` need not be connected, `Γ` need not be a functor:
  `not_B` on `trivialZ3EpGroupoid` with `U = {y < 1} ∪ {y > 1}` and `Γ` twisted on `{y > 1}`. This
  is why the project's `NaturalRep` asks `U` connected (Findings, items 20, 22; p. 231 speaks of
  "the connected open neighborhood `U(x)`").
* V7.28 (Definition 7.9): B's clause (D) identified its own reading of a local uniformizer with
  `LocalUniformizer`; refuted twice (`U` connected; `Ψ` the inclusion on objects), both readings
  its author had flagged (`B_issue`). This is not a statement of the text.

**Where the readings differ.**
* *Connectedness of `U(x)`* (V7.21, V7.23, V7.64, V7.66, V7.67). The blind statements' natural
  action allows a disconnected `U`; the project's `NaturalRep` does not. For Theorems 7.1 and 7.5
  it costs nothing (V7.17, V7.62: B ⇒ A shrinks `U` to the component of `x`, open because
  M-polyfolds are locally connected). Where no functoriality is used the text's claim holds without
  it: V7.21's B (`G_x ⋉ U` an ep-groupoid) holds outright by `actionEpGroupoid`, so
  `translationEpGroupoid` is narrower than it needs to be. For connected `V(x)`, A ⇒ B for Lemma 7.10
  (`A_to_B_of_isConnected`, V7.66).
* Lemma 7.10 (V7.66): the project drops `x ∈ U(x)` and adds `tsupport f ⊆ cl U(x)`. The proof of
  Theorem 7.4 (V7.67): the blind statement follows the text's steps for every choice, with the
  normalisation `h_i/Σh_j`; the project goes through `BumpCovering` on `|X|`, and only the first two
  claims follow (`A_to_B_first_claims`).
* Generality (*A ⇒ B only*, A_stronger): V7.50 (Michael's lemma without Hausdorff or regularity;
  B ⇏ A, since locally finite closed refinements do not give regularity), V7.54 (local metrizability
  of `|X¹|` without paracompactness), V7.64 (Lemma 7.9 with the identities that make `Φ` a
  homomorphism). Ten *stronger* items come out *equivalent* (V7.13, V7.16, V7.17, V7.32, V7.34–V7.37,
  V7.61, V7.63): the project's extra conjuncts are true facts that B ⇒ A re-proves from other project
  lemmas, so "equivalent" there means that the main claim matches.

**Missing in the project, believed true (effort only).**
* V7.5 (Definition 7.4): the tangent claims on `Tφ` (gap G.70): `Ts` injective on the fibre, the
  locality of tangent maps, `T_xU ≅ T_xX` for open `U`, linearity in charts.
* V7.6 (p. 227): "`X_∞` is dense in every `X_k`". The text states it without proof, Part I does not
  state it for M-polyfolds, and the project has it only for sc-Banach spaces
  (`ScBanach.denseRange_incl`); `A_to_B_of_density` shows it is the only difference. The sentence
  "the density of `X_∞` is Part I's" in `verification/ch07.md` (V7.6) and Findings item 112 is to be
  corrected.
* V7.30, V7.31 (Proposition 7.7, p. 238): the tangent facts (3)–(4) of sub-M-polyfolds (gap G.7, as
  in V2.25).
* V7.68 (Corollary 7.3): the project assumes the Godefroy–Troyanski–Whitfield–Zizler statement for
  each chart's `E₀` (not formalized; Findings, item 95).
* V7.23: (i)–(v) without connectedness would mean re-proving the item.

**Blind statements doubted in their own reading** (`B_issue`): V7.28 above. V7.25 and V7.26 read the
target of `t` as `U(y′)` where the text has `U(y)` (possible misprint; the project reads it the same
way).

**Harness.** Banned theorems inside definitions (`liftOne`, `reducedEpGroupoid`, `sheetAt :=
(exists_sheet φ).choose`, `subMorPolyfold`, `subEpGroupoid`, `discretePolyfold`, `IsScSmoothComp`,
`NaturalRep.functor`, `NaturalRep.orbitQuotientMap`, `trivialSubgroup`, `reducedSetoid`,
`reducedChart`) were handled by `#rt_check_soft`, a definitionally equal restatement `Ar` (V7.52),
checked cores, or a local `#rt_check_except_defs` / `#rt_check_opaque` (V7.5, V7.31, V7.32, V7.40),
with the plain check's failure kept by `#guard_msgs`; the JSON of each item says which. In V7.54
`metrizableSpace_of_pullback` is left off the banned list: the instance
`MPolyfold.paracompactSpace_level`, needed to state `X¹`, reaches it, and so does B. Cost: 18 Opus
5.5 agents (seven blind batches of 9–10 items, eleven prover batches of 5–6), up to seven at a time;
about 4.5M agent tokens, roughly 5% of a week's budget.

### Chapters 8–11, audited on 2026-11-08 (commit caf6bfc)

The 211 items of `Exposition/cmp/ch08.json`–`ch11.json` not labelled *extra* or *gap*:
- Chapter 8: 49 (V8.2, V8.19, V8.34 extra).
- Chapter 9: 60 (V9.3, V9.53 extra).
- Chapter 10: 71.
- Chapter 11: 31 (V11.19, V11.26 extra; V11.9–V11.13, V11.27–V11.29, V11.42 gaps, among them §§11.2 and 11.4).

Sources of the blind inputs:
- Chapters 7–8 quote the 2017 book. Exception: Chapter 8 items labelled "2021 edition" quote the Springer 2021 book.
- Chapters 9–11 quote the Springer 2021 book (`harness/make_inputs.py`).

Every blind statement and item file compiles against caf6bfc plus this commit's docstring-only edits to two Chapter 10 files. All 211 item modules, and the blind modules they import, were recompiled at the end in one `lake build`, with no error, no `rt_check FAIL` and no `sorry`.

| | equivalent | A ⇒ B only | B ⇒ A only | neither | B false | n |
|---|---|---|---|---|---|---|
| V8 | 28 | 5 | 9 | 4 | 3 | 49 |
| V9 | 6 | 17 | 10 | 22 | 5 | 60 |
| V10 | 46 | 7 | 8 | 8 | 2 | 71 |
| V11 | 11 | 9 | 3 | 8 | 0 | 31 |

Against the verdict, for Chapters 8–11: 127 match, 64 mismatch, 20 partial. By chapter:

| | match | mismatch | partial |
|---|---|---|---|
| V8 | 39 | 7 | 3 |
| V9 | 23 | 26 | 11 |
| V10 | 49 | 20 | 2 |
| V11 | 16 | 11 | 4 |

Most mismatches are *same* or *restated* items that the provers judge A_stronger or incomparable. In those, A states the project's lemmas more generally than the text (arbitrary or full functors in place of equivalences, any functor Θ in place of a branched one, any W, any sign). B ⇒ A could not produce that generality, so it was re-proved outright and flagged in the JSON.

**Statements of the text that do not hold in the formal reading (`¬B` proved).** Each agrees with a reading that `Exposition/Findings.md` already records.
* **V8.12 (Remark 8.1.10):** with trivial isotropy, (φ, h) ↦ (Tφ, Ts h) is not injective. This is Findings Ch8 item 10.
* **V8.30 (Theorem 8.5.3 (5)):** the square as printed fails, by the identity functor of ℤ/2 ⋉ ℝ. This is `theorem_8_5_3_five_as_printed`, Findings Ch8 item 54.
* **V8.35 (Proposition 8.5.7):** D = ∅ is allowed. This is `geometricLiftFunctor_surjective_iff`, Findings Ch8 item 59.
* **V9.9 (Proposition 9.1.11):** the dimensional decomposition is not unique. This is `not_proposition_9_1_11_rn`, Findings Ch9 item 8.
* **V9.11 (Gr(x)):** the blind statement also allows negative weights, which is its own `B_issue`. The project's generators are recorded in Ch9 item 20 and gap G.7.
* **V9.24 (Lemma 9.2.13):** the (2) ⇒ (1) direction at interior points, by {0} ⊂ ℝ. This is Ch9 item 41.
* **V9.27 (Definition 9.2.16):** (1) and (2) as printed do not determine ∂Θ. This is `not_unique_isBoundaryCharacterized_halfLine`, Ch9 item 44.
* **V9.62 (Proposition 9.6.5 (1)):** with the printed `I_k = I¹ ⊔ ⋯ ⊔ I^p` the formula would read `Θ_k(x) = ♯(classes)·Θ_k(x)`. It fails for `1_{y=0} + 1_{y=x}` on ℝ².
  - Ch9 item 92 recorded this partition as a possible misprint.
  - The audit's counterexample is new: Ch9 item 104.
* **V10.65 and V10.67 (Theorems 10.3.19, 10.5.7):** the ℤ/3 × ℝ ⇉ ℝ example. This is `not_theorem_10_3_19` and `remark_10_5_5`, Ch10 item 58.
  - Not independent: the blind inputs' titles already say "does not hold as we read it".
  - The blind formalizer also read the vocabulary docstrings that say so.

**What the project assumes or leaves out (A ⇏ B), each believed true.**
* **Part I facts taken as hypotheses and proved only on ℝᵐ.**
  - `HasIndependentTangentSums` (Theorem 9.2.1 (1)): V9.13, V9.26, V11.21–V11.24.
  - Graph charts, local constancy of dimension and `TopMultiplicity`: V9.2, V9.10, V9.14, V9.21–V9.23, V9.58, V9.61.
  - The oriented Proposition 9.2.8: V9.32.
  - `TangentZhouReflect`, `HasConnectedDenseLevelOneReps` and the openness of the tangent projection (G.8): V8.44, V8.45, V8.52.
  
  Findings Ch9 item 100 lists them with their witnesses.
* **`SheetGeometry` and `SheetNullSets` (§§9.4–9.5).** The project takes them as abstract data with the text's lemmas (9.4.4, 9.4.6, 9.5.2) as fields.
  - The fields are not tied to the geometry of the sheets: degenerate data on `discretePolyfold` satisfy them (`Items/V9_46.lean`, `tG`).
  - So the comparisons with concrete null sets and embedded manifolds come out incomparable (V9.42, V9.45, V9.47, V9.48, V9.50–V9.52).
  - The concrete notions would need second countability of the sheets and positive measure of the n-dimensional sheets.
  - Recorded as Findings Ch9 item 103 (gap G.105).
* **The weak fibred product (V10.18–V10.21).** The project builds X ×_Y Z on nested subtypes with the iterated sub-M-polyfold structure. The blind statements use the triple product.
  - B ⇒ A goes through an isomorphism functor (V10.19–V10.21).
  - A ⇒ B needs the triple-product sets to be sub-M-polyfolds, and the ep-groupoid structure transported along an sc-diffeomorphism.
  - The project does not need either result.
* **Not formalized, as the project's headers say.**
  - Lemma 9.4.3 (V9.41).
  - Proposition 8.4.3: the project's `EpStrongBundle.IsLR` tests strong bundle maps on all of W (V8.48, V10.61; Findings Ch8 item 119, G.86).
  - Proposition 10.4.6 (V10.61).
  - The Fred part of Theorem 10.4.5 (V10.27).
  - The germ q and its lift Q (V10.54).
  - The converse of Remark 10.5.3 (V10.57).
  - The fibre conditions of auxiliary norms (V11.30).
  - The local sc⁺-section structure of multisections (V11.31, V11.32).
  - Boundary operations natural under sc-diffeomorphisms (V11.25).

**Blind statements and inputs.**
* **V9.31 (Remark 9.3.3) and V9.28 (Remark 9.2.17):** the comparison rows paraphrased the remarks inaccurately. This commit corrects both rows in `cmp/ch09.json`.
  - V9.31's clause (a), "the oriented representation (9.9) is not unique", came from the old paraphrase. It has no counterpart in the text.
  - V9.28's "not the restriction of Θ to ∂X" is in the text, before Lemma 9.2.13.
* **V8.40 (A_stronger):** the blind statement's matching of the Θ_j is not total, which makes it weaker than the text.
* **V11.8:** `proposition_11_1_8` holds by the definition of `faceMap`. The content, f_* = Ψ_*∘Φ^* on faces, is `faceMap_homMk` (V11.5).
* **V10.48:** A and B each hold outright.
  - The non-uniqueness of f in Remark 10.3.18 is proved in Remark 10.5.5's example.
  - `LocalizationProperties.lean` still listed it as not formalized. This commit corrects that header, and the stale notes on Propositions 10.1.9 and 10.3.16 and Theorem 10.3.19 in `EquivalenceZhou.lean` and `LocalizationProperties.lean`.
* **Disclosures, names only:** some blind formalizers saw theorem names inside definition bodies or docstrings, for example `EpGroupoid.lemma_8_1_8` and `pushforwardTheta_eq`. The V9.9 formalizer saw the vocabulary docstring of `Proposition_9_1_11`.

**Harness.** Banned theorems inside definitions or statements were handled with patterns already in use. In each case the plain check's failure is kept by `#guard_msgs`, and the JSON says which pattern was used.
* **`#rt_check_soft`:** V8.32, V8.33, V8.47, V8.51, V9.4, V9.11, V9.13, V10.10, V10.37, V10.55, V10.70, V11.1, V11.17, V11.21, V11.34, V11.35.
* **An `A'` equal to `A` by `rfl`:** V8.4, V8.9, V10.42, V10.45, V11.38. In V11.38 the copy is made by a small elaborator, `replace_hFunctor%`.
* **Local `#rt_check_except_defs`:** V8.22, V8.25, V8.37, V10.3, V10.17, V10.18, V10.26, V10.29, V10.40, V10.52, V10.71.
* **New local variants:**
  - `#rt_check_defthm_V8_1` and V8.35's `#rt_check_fields`: `#rt_check_soft`, where a theorem in the body of a project definition also counts as soft. Such a theorem can occur there only as a proof.
  - V8.18's `#rt_check_beyond_stmt`: the proof may reach only what the statement reaches. B mentions `tangentEpGroupoid`, which reaches `metrizableSpace_of_pullback`.
  - V8.27's `#rt_check_except_struct`: the auto-generated constants of `IsProperCovering` are not followed, because a banned theorem sits in a field type.
* **Limits:**
  - The except-defs traversals cannot see a projection of a field of a skipped definition. V8.22 checks the conjuncts it re-proves with plain `#rt_check` instead.
  - V10.18's relation, `A_stronger`, is the prover's judgement: neither direction is proved.
* **Cost:** 54 Opus 5.5 agents, up to seventeen at a time on the 128 GB machine, about 13.5M agent tokens.
  - 18 blind batches of 9–13 items.
  - 36 prover batches of 4–7 items.

### Harness

* **Banned theorems inside definitions.** When a definition in A's statement calls one of the item's
  own theorems in its body (`IsScSplitting.scProj`, `subChart`, `subPolyfold`, `Radii.τ`, the
  instance of `proposition_2_6_8`), every proof mentioning A fails `#rt_check`. The provers factored
  `A_to_B` through a projection `A → A'` and checked `A'_to_B`, or ran a local check that does not
  unfold that definition (V1.32, V2.24, V2.49, V2.51, V2.53, V2.61, V3.64, V3.92); the JSON records it.
* **Proof lemmas in A.** The comparison's declaration lists often include lemmas of the proof besides
  the main theorem; `B → A` cannot produce them, so they were re-proved from the definitions and the
  directions flagged in the JSON.
* Cost: about 260k agent tokens per blind batch and 280k per prover batch (Opus 5.5); the whole audit
  used roughly 19% of a week's budget, four agents at a time on the 128 GB machine.

## Per-item table

`content` is the prover's judgement; `proved` counts only non-vacuous directions; the full
diagnosis is in each item's JSON.

| item | verdict | proved | content | why |
|---|---|---|---|---|
| V1_1 | restated | equivalent | equivalent | Definition item: B characterizes the project's ScBanach as the text's sc-structure (complete levels, injective compact inclusions, E_∞ dense in every E_m), both ways up to level-wise isomorphism, and adds the finite-dimensional, sum and shift claims; everything is proved, so the project's ScScale/Sc |
| V1_2 | restated | equivalent | equivalent | Definition item: B states that the project's IsScOperator, ScOperator and ScIso are exactly the text's sc-operators / linear sc-isomorphisms (level maps only assumed continuous, base map only linear); all three characterizations are proved, so the project's notions agree with the text. The only glue |
| V1_3 | same | equivalent | equivalent | B (1) characterizes the project's ScPlus E F (= ScOperator E F.shift, with underlying sc-operator F.shiftIncl ∘ S) as the text's sc⁺-operator, and (2) asserts sc-compactness; both are proved from A, (1) by glue (the text's level maps S_m : E_m → F_{m+1} are automatically linear and commute with the  |
| V1_4 | restated | equivalent | equivalent | Definition item: B says the project's IsScSubspace and IsScSplitting are exactly the text's sc-subspace and sc-splitting (full sc-structure on F_m = F ∩ E_m: complete levels, injective compact inclusions, F ∩ E_∞ dense in every F_m; complement G with its own sc-structure and E_m = F_m ⊕ G_m topologi |
| V1_5 | same | equivalent | equivalent | Same notions on both sides (the project's IsScSubspace, smooth, IsScSplitting; finite-dimensionality as an instance in A, an explicit hypothesis in B). The only difference is packaging of the second sentence: A's proposition_1_1_7 assumes F ≤ E_∞, B's assumes F is an sc-subspace; the shared first conj |
| V1_6 | stronger | A ⇒ B only | A_stronger | The conclusions agree: A's 'sc-Banach Q with a level-wise surjective sc-operator q : E → Q, ker q_m = A_m' gives B's level-wise isomorphisms Q_m ≃L E_m/A_m intertwining the inclusions (the induced maps E_m/A_m → Q_m are continuous bijections of Banach spaces, inverted by the open mapping theorem), a |
| V1_7 | restated | B false | A_narrower | The literal B is false (not_B proved): its conjunct 'F = C ⊕ T(E_m)' read inside F₀ forces, for T = id, every inclusion E_m → E₀ to be onto (B_implies_toBase_surjective), hence the compact inclusion E₁ → E₀ to be invertible and every sc-Banach space to be finite-dimensional (B_implies_finiteDimensio |
| V1_8 | same | equivalent | equivalent | Same statement for the core: proposition_1_1_10 quantifies over the data s : ScFredholmSplitting T, B over the proposition IsScFredholmB T, an existential over the same K, X, C, Y with exactly the seven fields of ScFredholmSplitting (isScFredholmB_iff repackages them); IsScFredholm.isRegularizing is th |
| V1_9 | same | A ⇒ B only | A_stronger | B's hand-written IsScFredholmB has exactly the fields of the project's ScFredholmSplitting (repackaged by isScFredholmB_iff), and T.add S.toScOperator is definitionally T + S.toScOperator, so proposition_1_1_11_preprint is literally B (A_to_B). B still gives proposition_1_1_11_preprint and the bootstrap lemma ScPlus.regu |
| V1_10 | same | equivalent | equivalent | The project's definitions agree with the text's (B is true): IsPartialQuadrant writes C = T₀⁻¹([0,∞)ⁿ ⊕ W₀) where the text writes T₀(C) = [0,∞)ⁿ ⊕ W₀ plus 'C closed convex' — equivalent because T₀ is bijective, and closedness/convexity are exactly A's IsPartialQuadrant.isClosed/.convex (used in A_to |
| V1_11 | restated | A ⇒ B only | equivalent | The project's IsSc0 is the text's sc⁰ (B is true). The only difference is the target: the project's IsSc0 E F U f asks f(U_m) ⊆ F_m with levelMap f m continuous on U_m, the text asks f(U_m) ⊆ U'_m; for f(U) ⊆ U' the extra U'_m-clause is exactly A's IsSc0.levelMap_mapsTo (used in A_to_B), and the bli |
| V1_12 | same | neither | incomparable | Both directions hold only vacuously (uses_hypothesis false for both), so the content comparison is what matters. The notions agree (tanSpace E = E.tangent = E¹ ⊕ E and tanSet E A = E.tangentSet A, both rfl), but A does not contain the text's claim that (TU, TC, TE) is again a tuple: the project neve |
| V1_13 | explicit | equivalent | equivalent | Definition 1.14 itself is formalized identically on both sides (Sc1With/Sc1/tanMap/tanSet are IsSc1With/IsSc1/tangentMapWith/tangentSet, rfl or field-for-field); B is the three remarks after it. A_to_B: remark (a) ('x ↦ Df(x) is in general not operator-norm continuous') is now A's exists_isSc1_not_c |
| V1_14 | same | A ⇒ B only | equivalent | The blind notions agree with the project's on tuples: tanSet/tanMap/Sc1With are literally tangentSet/tangentMapWith/IsSc1With, and the blind SckB (k+1) ('sc¹ with SOME derivative family D and Tf = tanMap f D sc^k') equals the project's IsSck (k+1) ('sc¹ with Tf built from the CHOSEN scDeriv sc^k') o |
| V1_15 | restated | A ⇒ B only | A_stronger | Same notions (B's levelTo f (m+1) m is levelMap f m ∘ ι_m by rfl; IsSc0/IsSc1/IsSc1With/IsScOperator/E_∞ are the project's), and B's (1)–(2) (C¹ with fderivWithin, continuity of df, an extension family Dl) match the project's IsSc1Levels on domains with unique differentiability, so A ⇒ B is glue aro |
| V1_16 | same | A ⇒ B only | A_stronger | Same notions on both sides (B's levelTo f 1 1 is levelMap f 1 by rfl; U¹ = E.lvlSet U 1 in E.shift; sc^k = IsSck), so A ⇒ B is IsSck.shift on the sc-domain U (IsRelOpenInQuadrant.isScDomain) plus IsSc0.levelMap_mapsTo for f(U¹) ⊆ V¹. B ⇒ A fails for a genuine reason: A's conjuncts are stated for arb |
| V1_17 | same | A ⇒ B only | A_stronger | Same notions on both sides (the project's IsSck, Mathlib ContDiffOn on U_{m+l}); B's levelTo f (m+l) m is definitionally invFun ι_m ∘ f ∘ ι_{m+l} = levelMap f m ∘ inclK m l, so A ⇒ B is glue plus IsRelOpenInQuadrant.isScDomain. B ⇒ A fails for a genuine reason: every conjunct of A is stated for an a |
| V1_18 | same | A ⇒ B only | A_stronger | Same notions: B's levelTo f (m+l) m equals levelMap f m ∘ inclK m l (pointwise via toBase_inclK), B's membership hypothesis at l = 0 plus C¹ on U_m is IsSc0, and sc^{k+1} is IsSck (k+1); so A ⇒ B is proposition_1_2_4_text (the text's hypothesis, not the stronger C^{k+1}-on-every-level one) on the sc- |
| V1_19 | same | A ⇒ B only | A_stronger | Same notions (constant sc-structure on the target, f ∘ E.toBase l on U_l, Mathlib ContDiffOn, IsSck), so A ⇒ B is corollary_1_2_5_text with V = Fin N → ℝ on the sc-domain U. B ⇒ A fails for a genuine reason: every conjunct of A is stated for an arbitrary IsScDomain U (e.g. a closed disc, not relative |
| V1_20 | same | A ⇒ B only | A_stronger | Same notions (IsSc1, tangentMap with the chosen scDeriv, tangentSet); A ⇒ B is theorem_1_3_1 plus the trivial (g∘f)(U) ⊆ W, and conversely B gives theorem_1_3_1 exactly (B_to_theorem_1_21, rt_check OK, taking W = Q = G₀), so on the text's statement the two agree. B ⇒ A fails because A contains strictl |
| V1_21 | same | equivalent | equivalent | The blind definitions coincide with the project's definitionally: Presentation E C is the data of IsPartialQuadrant E C ({p / ∀ i, 0 ≤ p.1 i} is quadrant n W 0 by rfl), degWith T x is degIndexWith T x = quadrantDeg (T 0 x) by rfl, and degC / degIndex both evaluate the count with a chosen presentatio |
| V1_22 | same | equivalent | equivalent | lemma_1_3_4 is B verbatim (same degIndexWith, same presentations T, T' with possibly different n, W, same quantification over x ∈ C). The other two conjuncts of A follow from B: lemma_1_3_4_dim by B at x = T⁻¹(0) (index n vs n'), and the core quadrantDeg_eq_of_equiv (an arbitrary level-0 linear equiva |
| V1_23 | stronger | A ⇒ B only | A_stronger | A ⇒ B: theorem_1_3_5 applied to the shrunken domains O∩U, O'∩U' (still relatively open in C, C'), with sc-smooth ⇒ sc¹, then degIndex_eq (Lemma 1.24, outside this item) turns the project's choice-based degIndex into degIndexWith for B's arbitrary presentations T, T'. B ⇒ A is not derivable: theorem_1 |
| V1_29 | stronger | B false | incomparable | B is false (not_B, as its author predicted): its clause 'F = C ⊕ T(E_m)' read literally in F₀ forces, for the identity operator with K = C = 0, every inclusion E_m → E₀ to be onto (B_surj); this fails for the sc-Banach space Model.G (ℓ² on every level, inclusions the compact injective diagonal opera |
| V1_30 | stronger | equivalent | A_stronger | B is the text's Proposition 1.10 (T + S is sc-Fredholm, index not mentioned); A is the project's index statement: ind(T+S) = ind T, and every (T+S)_m is Fredholm of index ind T. A_to_B genuinely uses A's level conjunct and does not use proposition_1_1_11_preprint. If all level maps of T' are Fredholm with the  |
| V1_31 | restated | equivalent | equivalent | B's hand-written IsScStructure (complete levels, injective compact inclusions, E_inf dense in each level) is literally the project's ScScale + dense_smooth (glue: toScBanach / isScStructure_of_scBanach, with inclTo0 = toBase by induction). Uniqueness: A's toBase_bijective_of_finiteDimensional gives  |
| V1_32 | explicit | equivalent | equivalent | Common content: an idempotent continuous on every level gives the sc-splitting E = P(E) + (1-P)(E). A_to_B gets it from isScSplitting_of_idem, applied to the ScOperator built from B's level maps; this uses ker P = (1-P)(E). B's first conjunct (the project's IsScSplitting, algebraic IsCompl on each l |
| V1_33 | same | equivalent | equivalent | Both assume A is an sc-subspace: B's hand-written IsScSubspaceText (closed, complete levels, compact inclusions, A_inf dense in each A_m) is equivalent to the project's IsScSubspace (closed + density), the extra fields being automatic (glue lemmas isScSubspace_of_text / text_of_isScSubspace). The co |
| V1_34 | restated | A ⇒ B only | A_stronger | Both sides share the claim that x ↦ Df(x) is continuous on U₁ for the compact-open topology: A's deriv_uniformOnCompact gives B's first conjunct via Mathlib (compact-open = uniform convergence on compacts). B's second conjunct (some sc¹ map has Df not norm-continuous) is now A's exists_isSc1_not_con |
| V1_35 | explicit | A ⇒ B only | A_stronger | A is stated only for the constant structures const V, const W, while B allows any ScBanach E, F with E_0, F_0 finite-dimensional. A_to_B bridges this with the sc-isomorphisms E = const E_0 and F = const F_0 (isoConstOfFiniteDimensional from V1_31, the identity on level 0) and the chain rule theorem_ |
| V1_36 | same | equivalent | equivalent | B is the conjunction of IsRelOpenInQuadrant.tangentSet and IsRelOpenInQuadrant.shift, word for word (same project notions tangent, tangentSet, shift, lvlSet, IsRelOpenInQuadrant), so A_to_B projects two conjuncts. B_to_A gets the two IsRelOpenInQuadrant statements from B directly and the two IsParti |
| V2_1 | same | equivalent | equivalent | B's definition IsScRetractionB (relatively open U in a partial quadrant, r(U) ⊆ U, IsScSmooth U r, r ∘ r = r on U) is exactly the field list of the project's ScRetraction, so the definitional conjunct is structure packing (no universe parameters; ScBanach lives in Type). The projection claim for x ∈ |
| V2_2 | same | B ⇒ A only | equivalent | Definition item. B's IsScRetractB (∃ U r, r an sc-smooth retraction on U relatively open in the partial quadrant C, O = r(U)) is the project's IsScRetract (∃ R : ScRetraction E C, R.retract = O) unfolded, and every LocalModel carries IsScRetract, so B is provable outright by structure packing; A_to_ |
| V2_3 | same | equivalent | equivalent | Same notions on both sides: B writes out ScRetraction.tangent (tangentMap R.U R '' E.tangentSet R.U), so the main conjunct proposition_2_1_11 is B verbatim (A_to_B and the first conjunct of B_to_A are rfl-level). The other conjuncts of A are proof-internal helpers: r' ∘ r = r on U when r(U) ⊆ r'(U'), t |
| V2_4 | same | equivalent | equivalent | Same notions. B's explicit TOB R = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E} (r(x) as the level-1 point over r(ι₁x₁)) equals the project's R.tangent = Tr(TU) by mem_tangent_iff_exists plus levelMap_eq_of_toBase_eq / IsSc0.toBase_levelMap; then 'TO := Tr(TU) for any r onto O' is retractTangent_eq, the E- and  |
| V2_5 | explicit | equivalent | equivalent | Same notions on both sides (ScRetraction, IsScSmooth on r.U of f ∘ r, tangentMap, TO = Tr(TU) = ScRetraction.tangent). A ⇒ B: (1) is proposition_2_1_13_one in both directions; (2)/(3) are proposition_2_1_13_two/_3 after identifying B's Tρ(TU_ρ) for an arbitrary retraction ρ onto O with r.tangent via Propositi |
| V2_6 | restated | equivalent | equivalent | Same notions. B reads Definition 2.7 existentially (f(O) ⊆ O' and f ∘ r sc-smooth for SOME r onto O); the project's IsScSmoothRetractMap quantifies over EVERY r, and isScSmoothRetractMap_iff_exists (Proposition 2.6 (1)) is exactly B's first conjunct for a retract O. With B's explicit TOB R identifie |
| V2_7 | explicit | equivalent | equivalent | Same notions on both sides (ScRetraction, IsScRetract, tangentMap of Definition 1.14, TO = Tr(TU)). B's hypothesis 'f∘r sc-smooth for SOME retraction' is the project's IsScSmoothRetractMap ('for EVERY retraction') by Proposition 2.6(1) (isScSmoothRetractMap_iff_exists), and the project's retractTang |
| V2_8 | restated | equivalent | equivalent | Same notions: B's TEB/TCB/TUB are E.tangent, E.tangentSet C, E.tangentSet U definitionally, and B's explicit TOB R equals Tr(TU) = retractTangent E C O (glue + retractTangent_eq). B's 'TO is a retract', 'Tf is a morphism TO → TO'' (Tf(TO) ⊆ TO' and Tf ∘ ρ sc-smooth for every ρ onto TO), 'T(1) = 1' a |
| V2_9 | restated | equivalent | equivalent | Same notions (IsScRetract, open subset of O read as O ∩ W with W open in E₀, same C and E). (1) is proposition_2_3_1_one verbatim. For (2), the project states it for any retract V (not only an open subset of a retract O) with the 'every retraction' notion IsScSmoothRetractMap; B takes V = O ∩ W and the |
| V2_10 | restated | equivalent | equivalent | Same notions. A project MChart is exactly a text chart (open V, homeomorphism V ≃ₜ O onto a LocalModel), and every text chart around a point x₀ is a project chart with the same model and source (glue: chartHomeo / mkChart, x₀ as junk value of the total inverse; only the chart on an empty domain in a |
| V2_11 | same | equivalent | equivalent | Same notions. The project's MAtlas asks compatibility for ALL pairs of charts (including φ with itself) where B's IsAtlasB uses Set.Pairwise (distinct pairs); the diagonal is MChart.compatible_self (item V2_10, not banned), so the chart sets of project atlases are exactly B's atlases. MAtlas.Equiv i |
| V2_12 | restated | equivalent | equivalent | Same notions. MPolyfold X (for Hausdorff paracompact X) is one atlas standing for its class, and MPolyfold.IsChart (compatible with every chart of the atlas) is exactly 'lies in some atlas of the class' (B (c)): → by adjoining φ to P.atlas, ← by A's isChart_congr. B (a), that atlas equivalence is an |
| V2_13 | explicit | equivalent | equivalent | Same notion of sc-smooth map. The project's IsScSmoothMap (continuity as a field + ψ ∘ f ∘ φ⁻¹ sc-smooth on φ(V) for EVERY pair of charts of the maximal atlases and every open V ⊆ dom φ with f(V) ⊆ dom ψ, 'every retraction' Def. 2.7) is equivalent to B's existential reading (around each x SOME chart |
| V2_14 | restated | equivalent | equivalent | Same X_m, X_∞ and topology. P.levelSet m (φ(x) ∈ range ι_m for some chart of the maximal atlas) is B's levelSetB (∃ z ∈ O_m with ι_m z = φ(x)) definitionally since φ(x) ∈ O; chart independence is A's mem_levelSet_iff; X_0 = X, X_{m+1} ⊆ X_m, X_∞ = ⋂ X_m match. The project's generators {x ∈ V / level |
| V2_15 | same | equivalent | equivalent | Identical statements: both say that P.levelIncl m : (X_{m+1}, P.levelTopology (m+1)) → (X_m, P.levelTopology m) is continuous for every M-polyfold P on a Type and every m. The only difference is binder kind (lemma_2_3_9 takes X implicitly, B explicitly); A is instantiated at universe 0. B reuses the  |
| V2_16 | narrower | B ⇒ A only | A_narrower | B states for EVERY level m that the charts (V_m, φ_m, (O_m, C_m, E^m)) are charts on (X_m, levelTopology m), pairwise compatible, covering; A (and the project) builds charts and the M-polyfold only for m = 1 (levelChart_compatible, shift_isChart). The added mem_shift_levelSet_iff gives (X¹)_m = X_{m |
| V2_17 | explicit | equivalent | equivalent | Same objects on both sides (P.Level m with P.levelTopology m, which is the project's instance; X_∞ = P.SmoothLevel). B gives X_∞ the infimum of the topologies induced by the inclusions X_∞ → X_m; the project's instance is induced from the product ∏ X_m, and the two agree (smoothLevel_topology_eq, re |
| V2_18 | restated | equivalent | equivalent | Definitions agree: the project's tangentSpace E C O x₁ is B's TxOB R x₁ = {h / (x₁,h) ∈ {(r x, Dr(x)h)}} = range Dr(x₁) for every retraction R onto O (TOB R = R.tangent, retractTangent_eq); the fields of TangentPre are exactly B's IsTupleB (levelSetB = levelSet). The two relations point in opposite  |
| V2_19 | narrower | equivalent | equivalent | A (tangentChartMap_mk_self, _injOn, _mk_ofVec, _mk_ofVec_of_mem, universe 0) and B (the project's TX, p, T_xX, TV, Tφ and topology are the text's, T_xX is a vector space with every Tφ linear on it) are interderivable. The project's Tφ = tangentChartMap is [(x,ψ,h)] ↦ T(φ∘ψ⁻¹)(ψ(x),h) (any representa |
| V2_20 | narrower | B ⇒ A only | A_narrower | B's topology τB = generateFrom 𝓑 is the project's instance on TX (tangentBasis = TfamB, via tangentChartMap_mk_self), so B ⇒ A is direct: continuity of p, openness of TV (a member of the basis 𝓑), metrizable and paracompact are read off B. A ⇒ B fails only on B (2) 'p : TX → X_1 is an OPEN map': the |
| V2_21 | narrower | equivalent | equivalent | Same content. B's TV/Tφ/τB/TO/TC are the project's tangentChartSet/tangentChartMap/instance/retractTangent/tangentSet, and B's chart (TV, Tφ, (TO,TC,TE)) is tangentChart hφ α₀ (when TX is empty, TV and TO are both empty). A ⇒ B: formula (5) from tangentChart_overlap and tangentChart_transition (over |
| V2_23 | same | B ⇒ A only | equivalent | Definition item: A is only isSubMPolyfold_univ (X is a sub-M-polyfold of itself, universe 0); the real comparison is P.IsSubMPolyfold vs B's IsSubMPolyfoldB, which are proved equivalent for every A (isSubMPolyfold_iff). Both have the same V, r, r(V) ⊆ V, r∘r = r on V, r(V) = A ∩ V; they differ only  |
| V2_24 | explicit | A ⇒ B only | A_stronger | A ⇒ B: Q := subPolyfold hA; B (1) is A's subPolyfold_inclusion_isScSmooth plus IsEmbedding.subtypeVal (subspace topology on both sides); B's (V, r) is exactly a SubData, and A's subPolyfold_retraction_isScSmooth for the project's i⁻¹∘r (retractInto, junk value a₀ off V) transfers to every g agreeing |
| V2_25 | narrower | neither | A_stronger | A is the text's proof in coordinates (compRetraction_retract, proposition_2_3_19_three/4): for ANY sc-retraction R with retract O and ANY sc-smooth idempotent s of O, at a ∈ s(O)₁ (smooth for (3)), T_aO = Dr(a)E, T_a s(O) = Dt(a)E (t = s ∘ r), the explicit sc-complement (Dr(a) − Dt(a))E levelwise, s : O → |
| V2_26 | restated | equivalent | equivalent | Definition item; A = degIndex_le ∧ exists_isChart_degIndex_eq ∧ eventually_chartDegIndex_le (universe 0). The definitions agree: chartDegIndex φ x is d_C(φ(x)) by rfl (B (a)), and P.degIndex x is the sInf of exactly B's set chartIndicesB P x (same charts P.IsChart φ around x, same d_C(φ x); rfl), so |
| V2_27 | same | equivalent | equivalent | A = lemma_2_4_3 ∧ eventually_degIndexWith_le ∧ isOpen_setOf_degIndex_lt ∧ isClosed_setOf_le_degIndex (universe 0). lemma_2_4_3 (∀ᶠ y in 𝓝 x, d_X y ≤ d_X x) is B (an open U ∋ x with d_X ≤ d_X(x) on U) up to mem_nhds_iff, both ways; the open/closed level-set corollaries are derived from B. The one conju |
| V2_28 | restated | equivalent | equivalent | A = proposition_2_4_4 ∧ transportChart_isChart ∧ degIndex_le_of_isScDiffeoOn (universes 0,0). B uses the project's IsScDiffeoOn (f sc-smooth on open U, g sc-smooth on open V, mutually inverse, f(U) ⊆ V, g(V) ⊆ U) with x ∈ U, so B is proposition_2_4_4 verbatim and degIndex_le_of_isScDiffeoOn is its ≤ h |
| V2_29 | same | B ⇒ A only | equivalent | Definition item; the project's boundary = {x / 1 ≤ degIndex x} and IsWithoutBoundary = ∀ x, degIndex x = 0 are literally B's (rfl), so A ⇒ B is proved outright without A. A = isWithoutBoundary_iff ∧ isClosed_boundary ∧ isOpen_interior ∧ isClosed_corners ∧ IsScDiffeoOn.mem_boundary_iff (universe 0; 0 |
| V2_30 | explicit | equivalent | equivalent | A (lemma_2_4_6.{0}) states d_A ≤ d_X for the project's particular structure subPolyfold hA on A; B states it for every M-polyfold structure Q on A satisfying properties (1), (2) of Proposition 2.21. A ⇒ B: any such Q is sc-diffeomorphic to subPolyfold hA by the identity on V ∩ A (V the sub-M-polyfold |
| V2_31 | restated | equivalent | equivalent | Definition item. The project's minimalSubspaceWith T x and partialQuadrantAtWith T x are exactly B's transports T⁻¹(E_{Tx}), T⁻¹(C_{Tx}) of the text's E_x = ⋂_{i∈I(x)} E_i and C_x = ⋂_{i∈I(x)} H_i (via mem_minimalSubspaceWith, and by unfolding for C_x), and dim(E/E_x) = d_C(x) on the standard quadra |
| V2_32 | stronger | neither | equivalent | Definition item; the comparison is between the definitions, which agree: at every x₁ ∈ O₁ (smoothness unused) the project's partialConeWith R T x₁ = range Dr(x) ∩ partialQuadrantAtWith T x and reducedTangentSpaceWith R T x₁ = range Dr(x) ⊓ minimalSubspaceWith T x are B's T_xO ∩ C_x and T_xO ∩ E_x, b |
| V2_33 | stronger | B false | incomparable | A now holds the project's whole treatment of Remark 2.28: T^R_xO ⊆ C_xO (reducedTangentSpaceWith_subset_partialConeWith) and its refutation of the remark's negative claim — at every smooth x of every sc-smooth retract, T_xO and T^R_xO are sc-subspaces and C_xO IS a partial quadrant in T_xO (remark_2 |
| V2_35 | stronger | A ⇒ B only | A_stronger | A ⇒ B: B's germ (f sc-smooth O∩V → O'∩V' with sc-smooth inverse g) is an IsDiffeoGerm between a retraction RV onto O∩V and R'.restrict V' (A's isDiffeoGerm), so A's proposition_2_4_10_reduced/cone apply at x₁; the reduced spaces and partial cones computed with RV, R'.restrict V' equal B's (computed wi |
| V2_36 | restated | neither | equivalent | Both directions are proved outright, so the comparison is between B and the project's definitions, which agree. A's theorems say little about the text's claim: selfChart_isChart concerns X_U for U relatively open in a partial quadrant (not a general retract), and Compatible.isDiffeoGerm turns compat |
| V2_37 | stronger | A ⇒ B only | A_stronger | Same notions on both sides (T_xO = range Dr(x), E_x = minimalSubspaceWith T x, quotDim, d_O = degIndex of LocalModel.toMPolyfold); the project's reducedTangentSpaceWith is T_xO ⊓ E_x, and quotDim A (A ⊓ B) = quotDim A B, so A ⇒ B is theorem_2_4_12_retract applied at the level-1 lift x₁ of B's smooth p |
| V2_38 | stronger | A ⇒ B only | A_stronger | Same notions (X_C = hC.toMPolyfold hne, d_X = MPolyfold.degIndex, d_C = degIndex E C). A ⇒ B: C is relatively open in itself (V = E₀) and corollary_2_4_13 at U = C. B ⇒ A fails for a genuine reason on the fourth conjunct degIndexWith_le_of_germ (core of Theorem 2.31): d_C(x) ≤ d_{C'}(F x) for a germ F |
| V2_39 | restated | A ⇒ B only | A_stronger | The definitions agree: partialQuadrantAtWith T e = CeB T e and minimalSubspaceWith T e = EeB T e for every T and e (pq_eq, ms_eq, unfolding). A ⇒ B uses A: E_e ⊆ C_e is A's first conjunct, and B's cardinal codimension is A's finrank_quotient_minimalSubspaceWith (quotient finite-dimensional) plus deg |
| V2_40 | restated | neither | A_stronger | Definition item with four listed lemmas. The definitions agree and B holds outright (B_holds, A unused): for a presentation T, R.IsTameWith T ↔ IsTameWithB R T (isTameWith_iff) — (1) degIndex E C = degIndexWith T = dCB T on C ⊇ U; (2) the project's level-1 point x ∈ O₁ ∩ (E₁)_∞ is B's smooth x ∈ O w |
| V2_41 | stronger | equivalent | equivalent | Same notions: B's complB R x₁ = range(id − Dr(x)) and tangentAt R x₁ = range Dr(x) (rfl), and 'smooth x ∈ O with lift x₁' is the project's x₁ ∈ O₁ ∩ (E₁)_∞. A ⇒ B: B assumes R.IsTame (every presentation) and fixes T; A's proposition_2_5_3 needs only R.IsTameWith T; B's sc-subspace clause is part of I |
| V2_42 | stronger | equivalent | equivalent | Same notions on both sides (range Dr(x) = T_xO, reducedTangentSpaceWith, partialConeWith, ofSubspace/IsPartialQuadrant, d_O = degIndex of LocalModel.toMPolyfold). A ⇒ B: A is stated for a retraction R₀ tame w.r.t. the given presentation T, B for EVERY retraction R onto O; glue: range Dr(x) does not  |
| V2_43 | same | B ⇒ A only | equivalent | Definition item. The project's MPolyfold.IsTame and B's IsTameMB are the same existential except for the equivalence of atlases: the project's MAtlas.Equiv A B ('some atlas D has chart set A ∪ B') vs B's EquivB ('all charts of A ∪ B pairwise compatible'), equivalent via the project's MAtlas.equiv_if |
| V2_44 | same | neither | equivalent | Definition item; both directions hold only outright (flagged). The definitions agree on EVERY M-polyfold (B's tameness hypothesis is not needed): the project's face closure(connectedComponentIn {d_X = 1} x) with d_X(x) = 1 is B's closure(val '' connectedComponent s), s in the subtype {d_X = 1}, by M |
| V2_46 | explicit | equivalent | equivalent | Same notions: B's faces are MPolyfold.IsFace of LocalModel.toMPolyfold, A's are IsRetractFace in E₀, linked by isFace_toMPolyfold_iff (part of A). The only real difference is the extended faces: A uses the hyperplanes f_i = coordHyper T i of ONE presentation T, B (IsExtFaceB) those of ANY presentati |
| V2_47 | same | equivalent | equivalent | Same notions on both sides: B spells out IsFaceStructured (encard of the faces through x = d_O(x)) for the M-polyfold LocalModel.toMPolyfold of a tame retract, which is exactly corollary_2_5_13 (A ⇒ B is that theorem after unfolding). B ⇒ A: corollary_2_5_13 is B after `cases` on the local model; isFace |
| V2_48 | restated | equivalent | equivalent | Same mathematics, different packaging of 'the faces of V'. A (proposition_2_5_14) takes V = dom φ for a tame chart φ : V → O and states the local claims on the model: d_X(y) = d_C(φ y) = d_O(φ y) and the M-polyfold O is face-structured; B uses the induced structure P.subPolyfold hV on the subtype ↥V ( |
| V2_49 | restated | A ⇒ B only | A_stronger | Same vocabulary (IsFace/degIndex of LocalModel.toMPolyfold, ScRetraction, IsSubMPolyfold, subPolyfold, IsTame). A ⇒ B: B's retraction s : V* → V* onto F is the S of proposition_2_5_15 (S.U ⊆ R.U, F ⊆ S.U, S.retract = F), after moving F between ↥O and E₀ with isFace_toMPolyfold_iff (V2_46, not banned); |
| V2_50 | restated | neither | A_stronger | A states Prop 2.44 on the model of a tame chart φ : V → O: faces of the M-polyfold O through φx (count d_X(x); each a tame sub-M-polyfold OF O with d_F(φx)+1 = d_X(x)) and, for σ ⊆ I(φx), only the GERM of the corner: A_σ = φ⁻¹(B ∩ ⋂_{i∈σ} F_i) for some small open B is a tame sub-M-polyfold of X with |
| V2_51 | explicit | A ⇒ B only | A_stronger | Same vocabulary (IsTame, IsFace, degIndex, IsFaceStructured, IsSubMPolyfold, subPolyfold). B reads 'the interior of F = closure G' as F ∩ {d_X = 1}; the project's interior is the component G itself, and theorem_2_5_17_interior says the two coincide, so B's first claim is theorem_2_45_isSubMPolyfold_in |
| V2_53 | stronger | A ⇒ B only | A_stronger | Same vocabulary on both sides (MPolyfold.prod, IsLocalScDiffeo, fibredProduct, IsSubMPolyfold, subPolyfold, IsTame, degIndex). A ⇒ B: sub-M-polyfold is isSubMPolyfold_fibredProduct, the tame clause is isTame_fibredProduct + degIndex_fibredProduct_eq_snd, the last clause is proposition_2_46_of_isLoca |
| V2_54 | restated | neither | equivalent | Definition item; the substance is the comparison of definitions, which B itself asserts and which is proved outright (B_holds): doubleLevel = doubleLevelB (U_m ⊕ F_k), the levels of (U ◁ F)[i] = U × F^i are U_m ⊕ F_{m+i}, and IsStrongBundleMap / IsStrongBundleRetraction ⇔ B's IsStrongBundleMapB / Is |
| V2_55 | restated | equivalent | equivalent | Same notions. The project's IsStrongBundleRetraction and B's IsStrongBundleRetractionB agree for U relatively open (B's [1]-map is any sc-smooth lift Φ₁, the project's is shiftFiber R; they agree on U ⊕ F₁, so sc-smoothness transfers by IsScSmooth.congr), hence IsStrongBundleRetract = B's local stro |
| V2_56 | restated | A ⇒ B only | A_stronger | The definitions agree. The project's IsScSmoothSection (fst_eq on O plus Definition 2.7 in the 'every retraction onto O' form) is B's IsScSmoothSectionB (f(O) ⊆ K, (f x).1 = x, Definition 2.7 with one retraction) because O = r(U) is a retract (baseRetraction, after converting B's strong bundle retra |
| V2_57 | explicit | A ⇒ B only | A_stronger | The definitions agree (for continuous P, which B assumes). Charts: every field of StrongBundleChart is a clause of B's IsStrongBundleChartB (strong bundle retraction converted, r(U) = O definitional), with fibre continuity from A's continuous_fiber; conversely a B-chart is a project chart exactly wh |
| V2_58 | restated | A ⇒ B only | A_stronger | The notions agree where both speak: B's clauses (b) (strong bundle structures = classes of atlases of project StrongBundles), (d) (Y_{m,k} nested, = doubleLevel, oneSet = Y_{0,1}), (e) (Y[0] = toMPolyfold0 with levels Y_{m,m}, P[0] sc-smooth) and (f) (Y[1] = toMPolyfold1 with levels Y_{m,m+1}, P[1]  |
| V2_59 | restated | equivalent | equivalent | Same notions. IsSection (∀ x, P (f x) = x) is B's P ∘ f = id (funext); StrongBundle.IsScSmoothSection is literally B's 'section, sc-smooth into Y[0] = toMPolyfold0'. The project defines sc⁺-sections chart-wise (principal part in F₁ and localRepOne : O → K[1] sc-smooth in every strong bundle chart),  |
| V2_60 | same | A ⇒ B only | A_stronger | The definitions agree definitionally: pullbackSpace P f = {(z, y) / P y = f z} with Mathlib's subtype (= induced) topology, pullbackProj = (z, y) ↦ z, pullbackProj' = (z, y) ↦ y; A ⇒ B is these rfl's plus pullback_comm for P ∘ P' = f ∘ P_f. B ⇒ A fails only by scope: B states P ∘ P' = f ∘ P_f in the |
| V2_61 | explicit | neither | incomparable | A formalizes 'natural structure' as a specific atlas: proposition_2_6_8 says ∃ B' : StrongBundle PZ (pullbackProj P f) whose charts are exactly the pulled-back charts Φ_f(z,y) = (ψ(z), pr_F Φ(y)) (pullbackAtlas), plus construction lemmas (transition formulas, compatibility, R_g and its image K_g, par |
| V2_62 | stronger | equivalent | equivalent | B is literally the type of metrizableSpace_of_locally.{0} (Smirnov: paracompact Hausdorff + every point has an open metrizable neighbourhood ⇒ metrizable), so A ⇒ B is a projection. B ⇒ A: the other conjuncts of A are the project's proof-route forms. metrizableSpace_of_partition follows from B after |
| V3_1 | restated | neither | equivalent | Definition item in substance: the project's ScNbhdGerm has exactly the fields of B's IsScGermB (nested along incl, U m = O ∩ lvlSet C m with O open, 0 ∈ U m; lvlSet C m is definitionally B's levelB), every IsScGermB sequence is the levels of a ScNbhdGerm, the project's tangent germ has levels U(m+1) |
| V3_2 | same | neither | equivalent | Definition item in substance: B (the project's IsSc0Germ / IsSc1GermWith / IsSc1Germ / IsSckGerm / IsScSmoothGerm agree with B's notions on every germ of a partial quadrant) is proved outright. sc⁰: the project's levelMap is a level lift, and any lift agrees with levelMap on U_m. sc¹: HasFDerivWithi |
| V3_5 | explicit | neither | equivalent | The definitions now agree. At HEAD the project's StrongBundle.IsScSmoothSectionGerm asks f̂ ∘ r to be sc-smooth on SOME sc-germ of neighbourhoods G with G₀ ⊆ U of a centred compatible chart (the germ reading), as B (the text) does. B additionally asks f to be continuous on an open V ∋ x₀ with φ⁻¹(r( |
| V3_7 | explicit | neither | equivalent | Definition item in substance; B is proved outright. Under B's hypothesis g sc-smooth on U, the project's whole-U conditions IsFillerOf are the text's filling IsFillingB: (1), (2) coincide literally (rB, ρB, kB are r, ρ, fillDefect R g definitionally); Lr = scDeriv U r 0, Lk = scDeriv U k 0 satisfy B |
| V3_8 | stronger | A ⇒ B only | A_stronger | A now contains the germ form of Proposition 3.5 (IsFillingGerm.proposition_3_1_5, exists_kerEquiv, deriv_comp_r_eq_zero) for any derivative family Dg of the filling germ g on a germ G ⊆ U, which is exactly B's setting (g an sc-smooth section germ, section property near 0). A ⇒ B (A_to_B): B's IsFillin |
| V3_9 | restated | neither | equivalent | A is now the two bridges IsFilledVersion.isFillingGerm and IsFillingGerm.isFilledVersion (the latter assuming g sc-smooth on U); the row's canonical notion of Definition 3.6 is the germ filling IsFillingGerm, with IsFilledVersion its whole-chart special case G = ofSet U. Proved: IsFillingGerm ↔ the  |
| V3_10 | restated | neither | equivalent | Definition item: only IsBasicGerm and IsSc0ContractionGerm are listed, so A = True and both implications are vacuous; the content is B itself (the project's basic germs on C̃ = [0,∞)^k ⊕ ℝ^{n−k} ⊕ W coincide with the text's), proved outright as B_holds. Project ⇒ text: the project's B agrees with w  |
| V3_11 | stronger | A ⇒ B only | A_stronger | A now contains the text's Lemma 3.9 on level m with smallness on level m (IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le: every ε, every m, x ∈ U_{m+1} with /ιx/_m < r, for any sc⁰-contraction germ B with an sc¹ derivative family), besides D₂B(0,0)=0 (deriv_zero_snd) and the older level-0 / ½-co |
| V3_12 | stronger | A ⇒ B only | A_stronger | A now contains both statements of Proposition 3.10: proposition_3_1_10 (Df(0) sc-Fredholm of index dim P − dim Q) and proposition_3_1_10_level / proposition_3_1_10_full (for every m there is δ with levelDeriv Df m x Fredholm of index dim P − dim Q for x ∈ U_{m+1}, /ιx/_m < δ), for any basic germ h, sc⁺-ge |
| V3_13 | restated | neither | A_narrower | A is now four auxiliary theorems (IsScFredholmGermWholeChart.isScFredholmGerm, isScFredholmGerm_iff_germG_wholeChart, IsFillingGerm.nonempty_kerEquiv, TrivialBundle.not_isFillingGerm_evenBundleChart), re-proved outright in B_to_A; B (project IsScFredholmGerm ↔ text IsScFredholmGermB on tame bundles) |
| V3_14 | stronger | A ⇒ B only | A_stronger | Same conclusion: nested open neighbourhoods O(i) of x0 with cl_X{x in O(i) / f(x)=0} a compact subset of X_i for the level topology; A phrases it as levelVal '' K = closure with K compact in PX.Level i (= levelSet i with levelTopology i), B as closure inside levelSet i plus compactness of its preima |
| V3_15 | restated | A ⇒ B only | A_stronger | Same conclusion (A_to_B_projGerm: corollary_3_1_15_preprint gives B verbatim with the project's germ notion; Level m = levelSet m with levelTopology m, 'eventually' = ∃ K, ∀ k ≥ K, the limit read as x₀). At HEAD corollary_3_1_15_preprint assumes the germ reading IsScFredholmGerm (filling and sc⁺-section as germs), so the |
| V3_16 | same | neither | A_narrower | A is two auxiliary theorems (zeros of an sc-Fredholm section are smooth points, now for the germ-reading notion; whole-chart sc-Fredholm sections are germ-reading ones); the content is B, the comparison of IsScFredholmSection (germ reading at HEAD) with the text's Definition 3.14 on tame bundles. Cl |
| V3_17 | stronger | A ⇒ B only | A_stronger | Both sides use the same notions, at HEAD the germ reading of Definition 3.11 (IsScFredholmSection with IsScFredholmGerm built from IsFillingGerm/IsScPlusGerm), plus IsScPlusSection and sectionAdd. B adds the hypothesis PX.IsTame (the text's 'over a tame M-polyfold'); A's theorem_3_1_18_preprint drops it (tamen |
| V3_18 | restated | A ⇒ B only | A_stronger | A = lemma_3_1_19 ∧ IsScFredholmGerm.sectionAdd (universes u v of the latter at 0; at HEAD the latter is the germ-reading statement). B's (1) s̃ = s on O and (2) R(r(u), s̃(u)) = s(r(u)) are lemma_3_1_19 (from the hypothesis) applied to the principal part ι∘ŝ of the sc⁺-section (section condition from Is |
| V3_19 | stronger | A ⇒ B only | A_stronger | A now contains Lemma 3.17 in the germ reading: IsFillingGerm.add_section (g a filling germ of f̂, ŝ sc-smooth on U with (x, ŝ(x)) ∈ K on O ⟹ g + ŝ∘r a filling germ of f̂ + ŝ) and add_section_germ (ŝ a germ), besides the whole-chart lemma_3_1_20/IsFillerOf.congr_left. A ⇒ B is proved from A (A_to_B, no |
| V3_20 | stronger | B false | A_narrower | A is now the conjunction of the new theorems about the text's notion as written (IsScGoodComplement: an sc-splitting E = N ⊕ P with the ε-property; IsInGoodPositionSc): the forgetful map to the project's notion, the upgrade lemmas (a closed good complement of a smooth finite-dimensional N is a good  |
| V3_21 | same | A ⇒ B only | A_stronger | A = proposition_3_1_25 ∧ exists_quadrantNormalForm ∧ mem_quadCone_of_vanIdx ∧ sigmaCoord_surjective (V universes at 0). A ⇒ B: B's good position (sc-complement for smooth N, closed complement otherwise, plus ε) gives the project's IsInGoodPosition (the level-0 part of an sc-splitting is an algebraic c |
| V3_22 | narrower | neither | A_stronger | A = IsScSmoothGerm.isScInftyGermAt ∧ IsScSmooth.isScInftyGermAt; B = (project HasTangentGermProperty ↔ text's) in a tame M-polyfold. Half proved using A (mpr_of_A: text ⇒ project; B's sc-complement Y is closed and an algebraic good complement, δ reset to 0 off V, B's fixed sc-smooth germ gives the p |
| V3_23 | same | neither | A_stronger | A = proposition_3_2_2 ∧ proposition_3_2_2_image (universes at 0), about the project's HasTangentGermProperty; B is the same invariance for the text's notion HasTangentGermPropertyB, with X tame. B is proved OUTRIGHT (B_holds: the data N, Y, V, δ, G, D are carried by the chart ϕ∘ψ⁻¹ = transportChart, a |
| V3_24 | narrower | neither | incomparable | A's Theorem 3.27 assumes at every point of M tangent-germ data satisfying TangentGermChart.IsRegular: (a) delta sc-smooth on the whole of V (set sense), (b) the projection pi along Y maps the retract O into C. These are extra hypotheses the project adds because the text's proof fails without them (d |
| V3_25 | restated | neither | equivalent | All listed declarations are definitions, so A = True and both directions are vacuous; the content is B itself, the vocabulary check IsSc0ContractionGerm Ct G B <-> IsSc0ContractionGermText Ct G B, proved outright (iff_text, without even using the partial-quadrant hypothesis). sc0 of B and of f = w - |
| V3_26 | explicit | A ⇒ B only | A_stronger | A => B: existence is the conjunct theorem_3_3_2_of_isSc0ContractionGerm of A (partial quadrant => quadrant-like; level-0 membership from the level-m one via levelMap_zero); B's uniqueness as a germ follows from the same conjunct's radius r: two solution germs delta, delta' are continuous with value 0 |
| V3_27 | restated | A ⇒ B only | A_stronger | A => B: B's sc1 hypothesis on f = w - B(a,w) gives sc1 of B (pairing with pr2 and the sc-operator (u,v) -> u - v); the conjunct theorem_3_3_3 of A, applied to the working form h.toContractionGerm, gives sol sc1 on germ 1; B's arbitrary solution representative delta equals sol near 0 (uniqueness of fi |
| V3_28 | restated | A ⇒ B only | A_stronger | A => B from the conjuncts lemma_3_3_4 and (new) isSc0ContractionGerm_next, applied to the working form h.toContractionGerm with its parameter regions N m shrunk into the V_i (i <= m) and the region {delta in O 0}, so that B's arbitrary solution germ delta is sol there and gives sol sc^j on germ 0; G^ |
| V3_29 | restated | A ⇒ B only | A_stronger | A => B: B only asks for SOME sc0-contraction germ f^(j) of class sc^{min(k-j,1)} with solution germ T^j delta, so the trivial germ f^(j)(a,w) = w - T^j delta(a) (contraction constant 0) is a witness once T^j delta is regular; A's sol_isSckGerm (j := k) for h.toContractionGerm gives sol sc^k on some  |
| V3_30 | restated | A ⇒ B only | A_stronger | A => B: A's theorem_3_3_6 applied to the working form h.toContractionGerm of B's sc0-contraction germ gives the canonical solution germ sol of class sc^k on germ s; B's arbitrary solution representative delta equals sol near 0 by uniqueness of fixed points in O 0 (ContractionGerm.eq_sol, continuity o |
| V3_31 | same | A ⇒ B only | A_stronger | A => B is proved entirely from A now. Clause (1): corollary_3_3_7 for the working form h.toContractionGerm (sc-smoothness of f = w - B gives that of B; B's arbitrary solution germ delta agrees with sol near 0 by uniqueness in O 0) gives V_{m,k} (shrunk into V_0 and the agreement region) with sol on l |
| V3_32 | restated | A ⇒ B only | A_stronger | A now contains Theorem 3.35 in the text's form (theorem_3_35_of_isSc0ContractionGerm_preprint: Definition 3.28 contraction germ on any quadrant-like C~ in a finite-dimensional P, any representative (V, delta) of the solution germ; f sc^k gives delta sc^k on a smaller germ, f sc-smooth gives delta sc-smooth o |
| V3_33 | same | neither | equivalent | The only listed declaration (IsBasicGerm) is a definition, so A = True and both directions are vacuous; the content is B, the vocabulary check (exists B, IsBasicGerm (stdQuadrant n k) G f B) <-> IsBasicGermText G f, proved outright. The project carries the contraction map B as an extra argument tied |
| V3_34 | restated | A ⇒ B only | A_stronger | A => B (substantial glue, no new mathematics): B's sc+-germ s has an R^N-component which the project's StabilityData drops; it is absorbed into the basic germ f' = f + (s_RN, 0) (same contraction map), so f + s = fsum f' with s_W = W-part of s; exists_of_scPlus (in A) gives the data S, theorem_3_4_2  |
| V3_35 | stronger | A ⇒ B only | A_stronger | A => B: the conjunct theorem_3_1_13_local of A, applied to B's basic germ h and the sc0 part of B's sc+-germ s (a partial quadrant is closed), gives nested open O(i) containing 0 in E_0 with cl(S cap O(i)) = iota_i(K_i), K_i compact in E_i; B's relatively open O(m) are O(m) cap G.U 0, and cl(S cap O(m |
| V3_36 | restated | A ⇒ B only | A_stronger | A => B from the conjunct corollary_3_5_3 alone. Glue: B's sc+-germ s takes values in (R^N + W)^1 while the project's StabilityData only carries the W-component s2; the R^N-component s1 is absorbed into the basic germ (h' = h + (s1, 0) is basic with the same B, and h + s = fsum h'); the sc-Fredholm sp |
| V3_37 | restated | neither | A_narrower | A = StabilityData.lemma_3_5_5 (toShiftedBasicData is vocabulary; no universe parameters): for the project's ONE explicit coordinate change of Theorem 3.38 (linear (split₀, fiber₀), g = pushMap₀ f = Φ_*(f + s)), for every ε > 0 there is r > 0 such that zeros x of g with /x/₀ < r have their fibre compo |
| V3_38 | restated | neither | incomparable | A = theorem_3_5_6_sc_smooth ∧ theorem_3_5_6 ∧ Sol.exists_contDiffOn_level ∧ H_contDiffOn ∧ Sol.exists_eq_add_τ ∧ exists_proj_mem_of_eq_zero (no universe parameters). A is a germ-form core statement. It takes any sc-smooth g with g¹ basic (ShiftedBasicData) and assumes (i) K' = ker Dg(0) is in good pos |
| V3_39 | same | neither | incomparable | A = ShiftedBasicData.Deriv.ker_Dg_eq ∧ snd_Dg_inr ∧ DH₀_surjective (no universe parameters), stated for the project's data 𝒟 : ShiftedBasicData (g an sc-smooth germ on G₀ whose index raise is basic on exactly the shifted germ G₁, δ = 𝒞.sol) with 𝒱 : 𝒟.Deriv. Proved: kerEquiv_of_A — in A's own settin |
| V3_40 | stronger | A ⇒ B only | A_stronger | A = IsGoodComplement.map ∧ IsInGoodPosition.map (no universe parameters). A ⇒ B by glue, using the IsGoodComplement.map conjunct: ψ = base Φ, ψ' = base Φ' are inverse sc-smooth maps U ⇄ U' with ψ(0) = 0; B's Dφ 0 equals the chosen scDeriv U ψ 0 (uniqueness at 0 ∈ U₁); S = Dψ(0) is a linear isomorphi |
| V3_41 | same | neither | incomparable | A = lemma_3_5_10 ∧ lemma_3_5_10_isInGoodPosition (no universe parameters): the linear core for arbitrary finite-dimensional P, sc-Banach W, L : P → W₀, K̃ ⊆ P — if the graph K' = {(α, Lα) / α ∈ K̃} has an algebraic good complement w.r.t. C̃ × W, then K̃ has a good complement Z w.r.t. C̃ and Z ⊕ W is a g |
| V3_42 | restated | neither | incomparable | A = theorem_3_5_11_sc_smooth ∧ theorem_3_5_11 ∧ StabilityData.scDerivGerm_pushMap₀ (no universe parameters). A ⇒ B fails on the conclusion. A only produces an algebraic good complement Y (IsCompl on level 0), but B, following Definition 3.21 of the text, requires an sc-complement (E.IsScSplitting K Y) w |
| V3_43 | same | B false | equivalent | Definition item: the decls are the definitions IsFillingGerm (the canonical germ-reading filling) and IsFillerOf, so A = True and B → A is vacuous. B asserts IsFilledVersion ↔ IsFillingB, i.e. identifies the text's filling with the project's whole-chart IsFilledVersion. The canonical notion IsFillin |
| V3_44 | same | neither | incomparable | A = IsFillerOf.remark_3_6_2 (no universe parameters): from a filler (IsFillerOf: (1), (2) near 0, k = [1 − ρ(r)]g sc¹ on the whole U, linearization via scDeriv U) get an open W ∋ 0 with f = g on O ∩ W and (2) on U ∩ W. Its content is just the filter step: A_direct proves A from (1), (2) alone without |
| V3_45 | same | neither | A_narrower | Definition item: A = True (all decls are definitions), B = (IsScFredholmGermTame ↔ IsFredGermB) ∧ (IsScFredholmSectionTame ↔ IsFredSectionB) for sc-smooth sections of tame bundles. At HEAD the project's notions are the germ reading. Same tame chart on both sides; the filling agrees field for field ( |
| V3_46 | restated | A ⇒ B only | A_stronger | A now contains StrongBundle.linAt_isScFredholm (germ reading): for an sc-Fredholm section at a zero x and every strong bundle chart around x, Lin(z) = D(f^ o r)(z)/TzO : TzO -> Kz (z the level-1 lift of phi(x)) is an sc-operator between the sc-subspaces TzO and Kz = rho(z)F, sc-Fredholm, of level-0  |
| V3_47 | restated | neither | incomparable | A = forall_isGoodPositionAtGerm (good position at Dg(0) for every derivative family, same chart), IsFillingGerm.ker_deriv_le_range (ker Dg(0) <= T0O), IsGoodPositionGermTame.isGoodPositionGermSc and isGoodPositionGermSc_iff (at a zero of a tame sc-Fredholm section, good position with an algebraic co |
| V3_48 | narrower | neither | incomparable | A = theorem_3_6_8_graph (germ reading at HEAD: hypothesis IsGoodPositionGermTame) plus seven lemmas of the proof (theorem_3_6_8_linear(_of_isTameWith), IsInGoodPositionIn.isInGoodPosition, scDeriv_mem_iff_of_inverse, pushforward_linearization, theorem_3_6_8_pushforward, scDeriv_eq_of_eqOn_nhds), univer |
| V3_49 | narrower | A ⇒ B only | A_stronger | A = lemma_3_6_9_preprint ∧ lemma_3_6_9_core.{0} ∧ fderivWithin_mem_of_mapsTo.{0,0}. A ⇒ B was proved from the conjunct lemma_3_6_9_core alone (coordinates ℓ_i = (T·)_i of B's presentation, P = Y): B's τ : V → E₁ on a relatively open V ∋ 0 is pushed to E₀ and extended to the whole cone N ∩ C by a bump (σ ∘ (b·id |
| V3_50 | narrower | A ⇒ B only | A_stronger | A = theorem_3_6_10_of_tangentGerm (universes 0), unchanged by the germ reading: in an M-polyfold with d_X ≡ 0, a nonempty set with the regular tangent germ property of one fixed dimension n is a sub-M-polyfold whose induced structure is an n-manifold without boundary; A has no Fredholm hypothesis. A ⇒ |
| V3_51 | narrower | A ⇒ B only | A_stronger | A = theorem_3_6_11_of_tangentGerm (universes 0), unchanged by the germ reading: a nonempty solution set with the regular tangent germ property of one fixed dimension n is a sub-M-polyfold whose induced structure is tame and an n-dimensional manifold with corners; A has no Fredholm hypothesis. A ⇒ B is |
| V3_52 | restated | A ⇒ B only | A_stronger | A = lemma_3_7_2 (abstract: any family b ↦ L(b) of sc-operators X → Y over a finite-dimensional parameter space, jointly continuous on level 0, with L(0) injective and the family compactness property, is injective near 0). B is the concrete Lemma 3.59 in the setting of Theorem 3.58. A ⇒ B was proved b |
| V3_53 | restated | A ⇒ B only | A_stronger | A = lemma_3_7_3 (abstract: on a compact parameter set K, a family of sc-operators X → Y, jointly continuous on level m, injective on level m, with the family compactness property, has a uniform lower bound c_m). B is the concrete Lemma 3.60 in the setting of Theorem 3.58, with the O of Lemma 3.59. A  |
| V3_54 | restated | A ⇒ B only | A_stronger | A = lemma_3_7_4 ∧ famInv_isSc0Germ ∧ famInv_isSc1GermWith ∧ famInv_hasFDerivWithinAt ∧ famInv_isSckGerm ∧ exists_forall_norm_le_of_isCompact (no universe parameters). lemma_3_7_4 is stated for sc-germs at 0 (a germ Gv of relatively open neighbourhoods of 0 in C̃, levels allowed to shrink with m), B fo |
| V3_55 | same | A ⇒ B only | A_stronger | A = lemma_3_8_8.{0} ∧ sigmaCoord_surjective.{0} (vanIdx is vocabulary). A ⇒ B was proved from the lemma_3_8_8 conjunct with ℓ_i the coordinate functionals of ℝⁿ ⊕ W and P = N^⊥: the blind Σ is literally the project's vanIdx for these functionals, and only the ε-property of B's good complement is used  |
| V3_56 | restated | equivalent | equivalent | A = proposition_3_8_12 (no universe parameters; QuadrantNormalForm is vocabulary). A ⇒ B: B's good position (sc-complement with the ε-property) gives the project's IsInGoodPosition (algebraic complement, via levelSub at level 0); d_C on the quadrant is quadrantDeg = blind dC (degIndex_quadrant), x ∉ W |
| V3_57 | explicit | A ⇒ B only | A_stronger | A = lemma_3_8_13 ∧ lemma_3_8_13_core.{0} ∧ exists_rayDecomp.{0} ∧ exists_lipschitz_small.{0}. A ⇒ B was proved from the lemma_3_8_13 conjunct alone: B's τ : N → E₁ (Y-valued only on N ∩ C) is pushed to E₀ by ι₁ and set to 0 off the cone, so it is Y-valued everywhere as lemma_3_8_13 requires; C¹ and Dτ(0) =  |
| V3_58 | stronger | A ⇒ B only | A_stronger | A = theorem_3_8_15 ∧ surjective_of_image_eq ∧ degIndex_map_eq ∧ degIndex_eq_zero_iff (no universe parameters). theorem_3_8_15 is stated for C^j maps (j ≥ 1) and, for each j, produces its own U', V', g, so B's single C^∞ diffeomorphism is not read off directly. A ⇒ B was proved from theorem_3_8_15 with j = |
| V3_59 | stronger | A ⇒ B only | A_stronger | A = proposition_3_8_17 ∧ InvData.contDiffOn_inv (no universe parameters; InvData is vocabulary). A ⇒ B was proved from the proposition_3_8_17 conjunct: B's hypotheses give InvData C U f j for every j ≥ 1 (C^∞ ⇒ C^j; hypothesis (3) d_C(x) = d_C(f(x)) gives the project's weaker 'x interior ⟺ f(x) interior |
| V3_60 | same | A ⇒ B only | A_stronger | A = InvData.half_norm_le ∧ InvData.norm_sub_le ∧ InvData.injOn ∧ InvData.ball_inter_subset_image ∧ InvData.image_relOpen (no universe parameters). A ⇒ B was proved: B's hypotheses give InvData C U f 1 (C^∞ ⇒ C^1; d_C-equality ⇒ interior preservation via degIndex_eq_zero_iff); image_relOpen gives f(U |
| V3_61 | same | A ⇒ B only | A_stronger | A = type of corollary_3_8_19 (no universe parameters, V : Type): under InvData C U f j, f is continuous on U, g = invFunOn f U is continuous on f(U), and g∘f = id on U, f∘g = id on f(U). A ⇒ B: B's Hyp373 gives InvData C U f 1 (C^∞ ⇒ C¹; d_C-equality used only through d_C = 0 ⟺ interior, degIndex_eq_z |
| V3_62 | narrower | neither | incomparable | A = InvData.hasFDerivWithinAt_inv ∧ InvData.contDiffOn_inverse_deriv (no universe parameters). The project proves Lemma 3.77 only under InvData, i.e. Proposition 3.73's hypotheses (U convex, ‖Df(x) − 1‖ ≤ 1/2 on U, interior points preserved), from which it derives the homeomorphism and the invertibi |
| V3_63 | stronger | A ⇒ B only | A_stronger | A = theorem_3_8_22 ∧ ContractionData.exists_solution (no universe parameters). A ⇒ B: B's setting (ℝⁿ = Fin n → ℝ, C = quadC n k, f into Fin N → ℝ) is an instance of theorem_3_8_22. quadC is a partial quadrant via ℝⁿ ≅ ℝᵏ × ℝⁿ⁻ᵏ, fderivWithin f U 0 = L by unique differentiability of U, B's good position |
| V3_64 | same | A ⇒ B only | A_stronger | A = ContractionData.exists_radii ∧ Radii.norm_sub_le ∧ Radii.eq_τ (no universe parameters): for abstract normalized data (ContractionData on K × Y), admissible radii exist (ε, a, b with εa ≤ b, the region R ⊆ U and ‖DB‖ ≤ ε/(2(1+ε)) on R); on R, B is c₀-Lipschitz in both variables; and fixed points  |
| V3_65 | explicit | A ⇒ B only | A_stronger | A = Radii.mapsTo_ball ∧ Radii.exists_fixed (no universe parameters; Radii.τ is a definition, vocabulary only): for abstract normalized data (ContractionData on K × Y: convex Cp, B(0) = 0, DB(0) = 0) and ANY admissible Radii S (good constant ε, radii a, b with εa ≤ b, ‖DB‖ ≤ ε/(2(1+ε)) on the region) |
| V3_66 | stronger | A ⇒ B only | A_stronger | A = Radii.norm_τ_le ∧ norm_τ_sub_le ∧ continuousOn_τ ∧ (new) norm_τ_sub_le_global ∧ norm_τ_sub_le_eps ∧ lipschitzOnWith_τ ∧ norm_τ_sub_le_of_norm_le (no universe parameters): for abstract normalized data and any admissible Radii, /τ(k)/ ≤ ε/k//2, /τ(k) − τ(k₀)/ ≤ (1 + 2ε)/k − k₀/, τ continuous on V₀ |
| V3_67 | stronger | A ⇒ B only | A_stronger | A = Radii.hasFDerivWithinAt_τ ∧ Radii.contDiffOn_Φ ∧ Radii.contDiffOn_τ (no universe parameters): for abstract normalized data and any admissible Radii, τ has derivative Φ(k, τk) = Ring.inverse(1 − D₂B)·D₁B within V₀, Φ is C^{j−1} on the region, and τ is C^j on all of V₀. A ⇒ B: same glue as V3_65 w |
| V3_68 | narrower | neither | incomparable | A = theorem_3_1_22 ∧ theorem_3_1_22_linearization ∧ theorem_3_1_26 ∧ lemma_2_4_6 ∧ theorem_3_1_22_linearization_sc ∧ StrongBundle.linAt_isScFredholm (germ reading, universes 0). A => B fails on B's second clause only: B's first clause (at every zero, in every strong bundle chart, f'(x0) sc-Fredholm) now foll |
| V3_69 | narrower | A ⇒ B only | A_stronger | A = theorem_3_1_26_of_nearby ∧ theorem_3_1_26 ∧ theorem_3_6_8_two ∧ theorem_3_2_3_of_isRegular (universes 0), the first three now in the text's germ reading. A ⇒ B through A's theorem_3_1_26: B's IsSurjGoodPosAt (sc-complement good position of Lin(z) in some tame chart) gives IsGoodPositionGermTame (isGoodPositionGerm_o |
| V3_70 | explicit | A ⇒ B only | A_stronger | A = corollary_3_1_27 ∧ theorem_3_6_11 ∧ corollary_3_1_27_sc ∧ forall_isGoodPositionGermSc_iff (universes 0, germ reading). A assumes only IsScFredholmSection, good position in a centred tame chart at every zero (IsGoodPositionGermTame with an algebraic complement, or IsGoodPositionGermSc with the text's s |
| V3_72 | narrower | neither | incomparable | A = theorem_3_2_3_loc_of_isRegular (universe 0) ∧ the four theorem_3_27_loc_* lemmas (universe 0). As in V3_24: every theorem of A assumes regular project data (IsRegular: (a) δ sc-smooth on all of V, (b) π(O) ⊆ C) at every point, B only the blind Definition 3.25 (fixed sc-smooth germ, no condition on π(O)) plus  |
| V3_73 | narrower | B false | A_narrower | B is false (not_B, rt_check OK), as its author predicted: it claims, for every Definition 3.25 datum at x ∈ M, every v₀ ∈ V and every datum at x₀ = φ⁻¹(v₀ + δ(v₀)), that k(w) = πφψ⁻¹(w + τ(w)) has an invertible linearization, is a local diffeomorphism, and that δ is an sc^∞-germ near v₀; Definition  |
| V3_74 | narrower | B false | A_narrower | B is false (not_B, rt_check OK): its claim (1) says that for every Definition 3.25 datum at every point of a tangent-germ set M of a tame M-polyfold, δ is an sc^∞-germ near every v₀ ∈ V, but Definition 3.25 controls δ only near 0. Counter-model in the file: X = ℝ² (rnPolyfold 2, tame), M = {(t³, t)} |
| V3_76 | restated | neither | incomparable | A = corollary_3_4_3 ∧ corollary_3_4_3_isConjugate ∧ compIso_eq_strongShift ∧ four general strong-bundle-isomorphism lemmas (no universe parameters). A ⇒ B fails at the hypotheses: A's corollary assumes g and s sc-smooth on the relatively open U (set sense), B only that s is an sc-smooth germ (IsScSmoo |
| V3_77 | stronger | neither | incomparable | A = theorem_3_5_6_closed/proj, theorem_3_5_11_proj/closed, theorem_3_6_8_graph_proj (universes 0; germ reading at HEAD, hypothesis IsGoodPositionGermTame) and three lemmas. The new IsClosed Y closes the complement gap of V3_38/V3_42: a closed complement of the smooth kernel is an sc-complement, and B's  |
| V3_80 | narrower | neither | incomparable | A = theorem_3_6_8_nearby (universes 0; germ reading at HEAD, hypothesis IsGoodPositionGermTame) ∧ lemma_3_6_9_relOpen ∧ exists_surjective_Dfs'_graph. A ⇒ B fails on the conclusion: B is claimed for every good-position datum (chart c, filler g, sc⁺ s, conjugation D) handed to it, while theorem_3_54_nea |
| V3_81 | narrower | neither | A_stronger | A = theorem_3_6_8_nearby_kernel.{0,0} ∧ theorem_3_6_8_chart_kernel ∧ graphSpace_eq_ker_Dfs' ∧ scDeriv_pushforward_at ∧ ker_scDeriv_eq_map ∧ scDeriv_mem_partialQuadrantAtWith_iff ∧ isInGoodPositionIn_of_le ∧ ker_deriv_eq_map_germ (germ reading at HEAD). A's kernel claim at the nearby zeros is made in O |
| V3_82 | narrower | A ⇒ B only | A_stronger | A = theorem_3_6_8_one ∧ IsGoodPositionGermFilled.isGoodPositionGerm (universes 0,0) ∧ exists_range_deriv_eq_ρ_of_normal_injective_germ, germ reading; the r2 blind B uses the project's StrongBundle.IsGoodPositionGermSc (germ reading, sc-complement) in hypothesis and conclusion. A ⇒ B (from hA.1): B's  |
| V3_84 | narrower | neither | incomparable | A = theorem_3_6_8_tangentGermChart_proj ∧ theorem_3_6_8_tangentGermChart (universes 0,0; germ reading at HEAD: hypothesis IsGoodPositionGermTame) ∧ MChart.compDiffeo_isChart ∧ TangentGermChart.π_mem_of_projectsInto (universe 0) ∧ isScInftyGermAt_of_lifts ∧ StabilityData.ker_Dfs_le_smooth. A gives the  |
| V3_85 | narrower | A ⇒ B only | A_stronger | A = theorem_3_6_8_two ∧ theorem_3_6_8 ∧ theorem_3_6_8_tangentGermChart_solutionSet (universes 0,0) ∧ TangentGermChart.exists_isRegular_of_locally (universe 0), germ reading; the r2 blind B (identical to V3_94's) uses the project's StrongBundle.IsGoodPositionGermSc in hypothesis and (1), and HasCornerSt |
| V3_86 | restated | A ⇒ B only | A_stronger | A = theorem_3_6_10 ∧ theorem_3_6_11 ∧ lemma_2_4_6 ∧ theorem_3_6_10_sc (universes 0; the Chapter 3 theorems in the text's germ reading). A ⇒ B: PX.boundary = ∅ ↔ IsWithoutBoundary (isWithoutBoundary_iff); B's IsLinSurjAt at a zero with d_X = 0 plus the tame germ data give IsGoodPositionGermTame (germ form o |
| V3_87 | stronger | A ⇒ B only | A_stronger | A = theorem_3_6_11 ∧ theorem_3_6_11_dim ∧ theorem_3_2_3_loc_of_isRegular ∧ theorem_3_6_11_sc (universes 0; germ reading; solutionSetDim is vocabulary). A has no tame-bundle/tame-base hypothesis, only IsScFredholmSection and good position in a centred tame chart at every zero (IsGoodPositionGermTame, or IsGoodPositionGe |
| V3_88 | restated | A ⇒ B only | A_stronger | A = theorem_3_7_1_of_family ∧ contrMap358_contraction ∧ norm_sub_sub_le_of_hasFDerivWithinAt_segment.{0,0,0} ∧ fiberIsoMap_isStrongBundleIso ∧ famInv_isScSmooth_of (DerivCondition is vocabulary). Both work in the same coordinates E = B ⊕ X, F = A ⊕ Y, C = C̃ ⊕ X with the given family L(b) = P_Y Df(b, |
| V3_89 | narrower | neither | A_stronger | A = theorem_3_7_1 ∧ familyCompactness_derivFamOp ∧ fredholmIndex_block.{0,0,0,0} ∧ surjective_of_fredholmIndex_block.{0,0,0,0} ∧ lemma_3_7_2 ∧ lemma_3_7_3. A ⇒ B is believed to be glue plus standard sc-Fredholm facts, not proved. theorem_3_7_1 is in coordinates E = P ⊕ X, C = C̃ ⊕ X, F = Q ⊕ Y; B has ar |
| V3_90 | restated | A ⇒ B only | A_stronger | A = InvDataW.injOn ∧ InvDataW.hasFDerivWithinAt_inv ∧ InvDataW.contDiffOn_inv (universe 0): the Prop. 3.73 / Lemma 3.77 machinery under weak hypotheses (U convex with unique differentiability, f of class C^j, ‖Df − 1‖ ≤ 1/2, and the unique differentiability of f(U) ASSUMED; no quadrant, no d_C condi |
| V3_91 | stronger | A ⇒ B only | A_stronger | A = theorem_3_1_21_preprint ∧ theorem_3_1_21' ∧ paramSection_eq_sectionAdd ∧ IsScFredholmSection.param ∧ isScPlusSection_paramComb ∧ IsBasicGerm.paramExtend ∧ IsConjugateToBasicGerm.paramExtend ∧ IsStrongBundleIso.paramMap ∧ prod_rn_isTame ∧ isScSmooth_smul (universes 0; paramSection and StrongBundle.pullback ar |
| V3_92 | restated | A ⇒ B only | A_stronger | A = linAt_paramSection_zero ∧ linAt_paramSection ∧ scDeriv_paramSection ∧ PullbackChartData.ofProd_mem_tangent (universes 0); at HEAD the three formulas take f an sc-Fredholm section in the germ reading (only its sc-smoothness is used), as does B, so the germ reading plays no role here. Every conjun |
| V3_94 | restated | A ⇒ B only | A_stronger | A = theorem_3_6_8_one' ∧ theorem_3_6_8' ∧ isGoodPositionGermTame_of_chart_dense ∧ theorem_3_6_8_two ∧ IsGoodPositionGerm.toTame ∧ theorem_3_6_8_one_sc_of_tame ∧ theorem_3_6_8_one_sc ∧ theorem_3_6_8_sc (universes 0), germ reading; the r2 blind B uses the project's StrongBundle.IsGoodPositionGermSc (sc-comp |
| V3_95 | explicit | A ⇒ B only | A_stronger | A = theorem_3_1_26' ∧ theorem_3_1_22' ∧ theorem_3_1_26_of_nearby ∧ lemma_2_4_6 ∧ theorem_3_1_26_sc (universes 0; germ reading). A ⇒ B (3.23): B's IsSurjGoodPosAt (non-centred tame chart, sc-complement) gives IsGoodPositionGermTame (isGoodPositionGerm_of_linAt_surj, IsGoodPositionGerm.toTame); theorem_3_1_26' g |
| V3_96 | stronger | A ⇒ B only | A_stronger | A = linAt_index_of_conjugationData ∧ isSurjLinOfIndex_of_conjugationData ∧ IsGoodPositionGerm.exists_isSurjLinOfIndex ∧ theorem_3_1_22_linearization_index ∧ finrank_ker_eq_fredholmIndex_of_surjective ∧ linAt_isScFredholm ∧ linAt_isScFredholm_of_isSurjLinOfIndex ∧ proposition_3_6_5_sc ∧ theorem_3_19_lin |
| V3_97 | stronger | neither | incomparable | A = theorem_3_6_8_tangentGermChart_index ∧ …_solutionSet_index ∧ theorem_3_6_8_two_index ∧ theorem_3_1_26_index ∧ theorem_3_1_22_index ∧ theorem_3_6_11_index ∧ theorem_3_6_8_graph_proj_conj ∧ theorem_3_6_8_tangentGermChart_proj_conj ∧ linAt_isScFredholm_of_isSurjLinOfIndex (germ reading, universes 0). Proved  |
| V3_98 | narrower | neither | incomparable | A = the 20 theorems of the current decls (germ reading, universes 0). A => B: B(0) (Definition 6.1 exists at every smooth point, independent of chart and chart-level sc+-section) and B(a) (constancy along the solution set) are proved from the hypothesis A (B0_of_A, Ba_of_A): B's chart-level section  |
| V3_99 | restated | neither | incomparable | A = theorem_3_6_8_ker_eq_tangent ∧ theorem_3_6_8_nearby_kernel ∧ linAt_eq_germDeriv (germ reading, universes 0). A => B fails on hypotheses and on content: B assumes d_X = 0, a non-tame IsScFredholmSection and IsLinSurjAt, while A's theorems need (f, x0) in good position in a tame chart (IsGoodPositio |
| V3_100 | explicit | A ⇒ B only | A_stronger | A = isInGoodPositionIn_of_subset ∧ isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero ∧ isGoodPositionGerm_of_isLinSurjAt ∧ IsGoodPositionGerm.isLinSurjAt ∧ isGoodPositionGerm_iff_isLinSurjAt ∧ IsLinSurjAt.linAt_surjective (universes 0, germ reading); the r2 blind B states, for a tame bundle, an I |
| V3_101 | stronger | neither | incomparable | A = theorem_3_1_22_of_surjective ∧ theorem_3_6_10_of_surjective ∧ theorem_3_6_10_tame (universes 0; germ reading). B's (3.56) conjunct follows from A (A_to_B_3_56 in the file: theorem_3_6_10_of_surjective when S ≠ ∅, the empty atlas when S = ∅, ∂X = ∅ ⇔ d_X ≡ 0, open-chart glue). Its (3.19) conjunct does no |
| V3_103 | explicit | neither | incomparable | A = eight auxiliary theorems (tame germ data are germ data; tame good position ⇒ good position / tame germ; the filled hypothesis ⇒ tame good position; identity base retraction is tame; IsTame.congr; nonempty_kerEquiv; the bundleEven example tame_atlas_no_germData_in_atlas_chart), universes 0; B = f |
| V3_105 | explicit | A ⇒ B only | A_stronger | A = theorem_3_1_18_tame ∧ StrongBundle.IsScFredholmGermTame.sectionAdd (universes 0); at HEAD both and B's IsScFredholmSectionTame use the germ reading of Definitions 3.50/3.51 (filling and sc⁺-section as germs, data in a tame chart). B is theorem_3_1_18_tame with the extra hypothesis IsTameStrongBundle |
| V3_106 | explicit | A ⇒ B only | A_stronger | A = theorem_3_1_21_tame ∧ PullbackChartData.ofProd_isTame ∧ IsScFredholmGermTame.param ∧ IsScFredholmSectionTame.param (universes 0); at HEAD the tame notions on both sides are the germ reading of Definitions 3.50/3.51 (filling and sc⁺-section as germs in a tame chart). B is theorem_3_1_21_tame with the |
| V4_1 | restated | equivalent | equivalent | A = hasCornerStructure_iff ∧ HasCornerStructure.isTame ∧ IsCornerChart.isTameRetract ∧ IsCornerChart.isScPlusRetract (universe 0); IsCornerChart/HasCornerStructure are vocabulary. B: HasCornerStructure ↔ B's corner atlas (pairwise compatible, covering charts of P on relatively open subsets of partia |
| V4_2 | same | equivalent | equivalent | A = IsCornerChart.contDiffOn_transition ∧ isRelOpenInQuadrant_overlap (universe 0). A ⇒ B: B's corner charts (any finite-dimensional sc-model with onto inclusions) are replaced by project corner charts id ∘ χ over ScBanach.const E₀ (compDiffeo with isScDiffeoQuadrant_toConst) with definitionally the |
| V4_3 | restated | equivalent | equivalent | A = finiteDimensional_lvl ∧ toBase_surjective ∧ mem_smooth_of_finiteDimensional (no universe parameters); B's uniqueness half says every inclusion E_m → E₀ of an sc-structure on a finite-dimensional E₀ is a linear homeomorphism. A ⇒ B builds that equivalence as LinearEquiv.ofBijective (injective by  |
| V4_5 | stronger | equivalent | equivalent | A = theorem_4_1_2 ∧ theorem_4_1_2_general (universe 0); B is the same equivalence (i) HasCornerStructure ↔ (ii) X₀ = X_∞, 1₀¹ sc-smooth, centred tame charts with T₀O finite-dimensional in good position, for tame X. Differences are only bookkeeping: smoothSet = univ vs ∀ x, x ∈ smoothSet; A fixes one jun |
| V4_6 | stronger | A ⇒ B only | A_stronger | A = remark_4_1_3_levelVal.{0} ∧ remark_4_1_3_isScDiffeo.{0} ∧ remark_4_1_3_const ∧ remark_4_1_3_example ∧ remark_4_1_3_retract_example ∧ IsLossFamily.isScSmooth ∧ exists_retract_smooth_not_scPlus_of_data ∧ mem_shift_levelSet_iff.{0} (liftOne, toLevelOne vocabulary). A ⇒ B (proved): B's clauses 1, 2, 4 from th |
| V4_8 | explicit | A ⇒ B only | A_stronger | A = exists_scPlus_deriv ∧ isCompactOperator_deriv ∧ finiteDimensional_range_of_isCompactOperator_of_idem.{0}. A ⇒ B is glue: at o₁ with ι₁o₁ ∈ O the point is smooth (lemma_4_1_7_i) and in U₁, A's sc⁺-operator S : E → E¹ with S.toScOperator 0 = Dr(o) yields B's level maps E_m → E_{m+1} and E_m → E_m (S |
| V4_9 | restated | equivalent | equivalent | A = type of ScRetraction.IsScPlus.mem_lvlSet_succ (r(U_m) ⊆ U_{m+1}); ScRetraction.IsScPlus and MPolyfold.IsScPlusRetractionOn are vocabulary, and B says both agree with the text's definitions. Retraction half: the project's IsScPlus R.U R (canonical lift E.liftOne ∘ r sc-smooth into E¹) is B's 'som |
| V4_10 | same | equivalent | equivalent | A = type of lemma_4_1_5: ∀ E C T S, T.IsScPlus → T.retract = S.retract → S.IsScPlus. B is the same statement with the equation of retracts oriented the other way (s.retract = t.retract); both directions are one-line term proofs (Eq.symm). Both use the project's ScRetraction.IsScPlus as the notion of s |
| V4_11 | same | equivalent | equivalent | A = IsScPlusRetract.isScPlus ∧ isScPlusRetract_iff_forall (IsScPlusRetract is vocabulary: ∃ R, R.retract = O ∧ R.IsScPlus). B = (project IsScPlusRetract ↔ blind IsScPlusRetractB) ∧ intrinsic-ness. The definitions agree exactly: R.IsScPlus (canonical lift E.liftOne ∘ R sc-smooth into E¹) ↔ B's Defini |
| V4_12 | explicit | equivalent | equivalent | A = lemma_4_1_7_i ∧ lemma_4_1_7_ii ∧ lemma_4_1_7_ii_tangentSpace. (i): A's R.retract ⊆ E.smooth is B's 'every o ∈ O lifts to every level' (mem_smooth_iff). (ii): A's lemma_4_1_7_ii is B's finite-dimensionality verbatim; A's tangent-space clause is stated for SOME smooth lift o₁ of o, B's for EVERY level-1 o |
| V4_13 | same | equivalent | equivalent | A = proposition_4_1_8: IsScRetract E C O → (IsScPlusRetract E C O ↔ O ⊆ E_∞ ∧ IsScSmoothRetractMap E C O E¹ C¹ O¹ E.liftOne). Same statement as B up to glue: IsScPlusRetract ↔ B's IsScPlusRetractB (IsScPlus.iff_exists + mem_lvlSet_succ, as in V4_9/V4_11); O ⊆ E_∞ ↔ pointwise lifts (mem_smooth_iff); A  |
| V4_19 | restated | A ⇒ B only | A_stronger | A (types at universe 0 for exists_norm_sub_sub_le_of_hasFDerivWithinAt) = for EVERY sc⁺-retraction and EVERY level k+1: t_{k+1} = lvlMap k has derivative lvlDeriv k x within U_{k+1}, lvlDeriv k is operator-norm continuous on U_{k+1}, the mean value estimate exists_mvt at every u₀, plus the abstract  |
| V4_20 | explicit | neither | A_stronger | The two statements are about different maps. A's p is the continuous projection onto N = T_0O along an ARBITRARY closed good complement Y (project's IsInGoodPosition with an algebraic complement; plus the graph form Γ(a) − a ∈ Y), while B follows the item literally: p = Dt(0) (B's good-position hypo |
| V4_21 | restated | A ⇒ B only | A_stronger | A = qL_lvlDeriv_zero ∧ lvlDeriv_zero_of_mem_N ∧ exists_contraction_radius ∧ eq_of_p_eq, for EVERY GraphData and EVERY level k+1: the quantitative ingredients of Lemma 4.11 ((1−p)Dt(0) = 0, Dt(0) = 1 on N, the level-(k+1) mean value/contraction estimate with arbitrary θ, and 'same p-projection + cont |
| V4_22 | restated | neither | incomparable | Different statements. A (exists_graph_point, the project's Lemma 4.12 by a level-1 contraction for y ↦ (1−p)t(a+y)) is an EXISTENCE claim: for a ∈ N ∩ C with ‖a‖₁ < ρ there is u ∈ O₁ with p(u) = a, u − a ∈ Y and ‖u − a‖₁ ≤ ε'‖a‖₁ (under hypotheses on θ, r, the mean value estimate). B (the text's Lem |
| V4_27 | explicit | A ⇒ B only | A_stronger | A is the set of chart-level lemmas used by the formal proof of (i) ⇒ (ii); B is the implication (i) ⇒ (ii) itself for a tame M-polyfold. A ⇒ B is real glue: hasCornerStructure_iff gives a corner chart at every point, mem_smooth (A) + mem_smoothSet_iff give X_0 = X_∞, isScSmoothMap_toLevelOne_of_cove |
| V4_28 | explicit | A ⇒ B only | A_stronger | Same notions (HasCornerStructure, smoothSet, toLevelOne/shift, IsChart, T_0O = Dr(0)E = tangentSpace). A ⇒ B is hasCornerStructure_of_centred (A) plus glue: a junk point x₀ ∈ X₁ from any point (X_0 = X_∞), the empty X via hasCornerStructure_iff, B's T_0O = range Dr(0) for some R onto O equals the pr |
| V4_29 | same | B ⇒ A only | equivalent | The project's Definition 4.13 (IsSmoothSubmanifold: every a ∈ A has an open V ∋ a and s with IsScPlusRetractionOn s V and s '' V = A ∩ V) is exactly B's IsSmoothSubmanifoldB; the only glue is the sc⁺-retraction notion on an open set (retractionOn_iff, as in V4_9: B's IsOpen V is the isOpen field of  |
| V4_30 | explicit | equivalent | equivalent | Same mathematics in two packagings. A's exists_chartRetraction works with a retraction R onto the WHOLE chart model O and the shrunken set W = V ∩ dom φ ∩ s⁻¹(V ∩ dom φ), producing t = φ∘s∘φ⁻¹∘R on U ∩ R⁻¹(G) (φ(W) = O ∩ G); B (2) is the reduced situation V ⊆ dom φ, r(U) = φ(V), with t on all of U.  |
| V4_31 | restated | equivalent | equivalent | Both read Remark 4.14 in a chart but in different chart situations: A uses an arbitrary chart φ around a, the shrunken set W = V ∩ dom φ ∩ s⁻¹(V ∩ dom φ), T_aX = T_zO for the whole model O and Ts(a) = the tangent map of ρ = φ∘s∘φ⁻¹ between the retracts φ(W) (retractTangentMap), concluding z smooth,  |
| V4_32 | narrower | neither | incomparable | The project formalizes only the d_X = 0 half of the remark: A = two chart-level facts (every N is in good position to E; C_e = E when d_C(e) = 0), Definition 4.16 good position at points with d_X(a) = 0, and a GLOBAL corner structure on A when d_X ≡ 0 on A. B is local and has two claims. Its first ( |
| V4_33 | explicit | equivalent | equivalent | Same hypotheses (B's IsSmoothSubmanifoldB = the project's IsSmoothSubmanifold, glue of V4_29). A ⇒ B: A ⊆ X_∞ is subset_smoothSet; B's existential sub-M-polyfold proof and paracompactness are IsSmoothSubmanifold.isSubMPolyfold and paracompactSpace_subtype; (subPolyfold hA).levelSet 1 = univ from A's |
| V4_34 | restated | equivalent | equivalent | A = proposition_4_2_3_two (universe 0): a smooth finite-dimensional submanifold is IsLocallyClosed (Mathlib). B uses the text's definition literally (every a ∈ A has an open V ∋ a with every b ∈ V whose open neighbourhoods all meet A lying in A, i.e. V ∩ closure A ⊆ A). The two notions of 'locally clos |
| V4_35 | same | equivalent | equivalent | A = proposition_4_2_3_three (universe 0): Subtype.val '' (subPolyfold hA.isSubMPolyfold).boundary ⊆ P.boundary for a smooth submanifold with [ParacompactSpace A]. B states the same pointwise with degeneracy indices (1 ≤ d_A(a) → 1 ≤ d_X(a)), quantifying over an arbitrary proof hA : IsSubMPolyfold A and t |
| V4_36 | same | equivalent | equivalent | A = proposition_4_2_3_four (universe 0): for every junk value x₀ ∈ A¹, every point of A is smooth for the induced structure and toLevelOne x₀ : A → A¹ is sc-smooth. B: A = A_1 for the induced structure and toLevelOne a₀ is sc-smooth for every a₀. A ⇒ B: the sc-smoothness is A's; B's A = A_1 cannot be re |
| V4_38 | restated | neither | equivalent | Definition item with one listed theorem: A = type of SubmanifoldData.isGoodPositionChart_iff (universe 0), the explicit chart form 'Dt(z)E in good position to C_z inside Dr(z)E'; it is orthogonal to B, so A_to_B is B_holds (no use of A) and B_to_A re-proves A outright from tangentSpace_eq_coe_submod |
| V4_40 | same | neither | equivalent | Definition item: only IsTameSubmanifold is listed, so A = True and both implications are vacuous; the content is B itself, proved outright (B_holds). The project's IsTameSubmanifold A is ∃ hA : IsSmoothSubmanifold A, (subPolyfold hA.isSubMPolyfold).IsTame; B's text reading is ∃ hA : IsSubMPolyfold A |
| V4_41 | same | A ⇒ B only | A_stronger | A = theorem_4_2_7 ∧ hasCornerStructure_of_centred_isInGoodPosition ∧ IsGoodPositionAt.isInGoodPosition_of_tame (universe 0). theorem_4_2_7 alone is equivalent to B: A→B only needs the paracompactness of A, which B packages existentially and which holds for every subset (paracompactSpace_subtype, via m |
| V4_42 | explicit | A ⇒ B only | A_stronger | A = isGoodComplement_sup_range ∧ lemma_4_2_8 ∧ IsInGoodPositionIn.isInGoodPosition: general linear algebra in any sc-Banach space with a presented partial quadrant C, a bounded idempotent π with (1 − π)E ⊆ E₀ (minimal subspace at 0) and N ⊆ πE in good position to C inside πE with an ALGEBRAIC good co |
| V4_43 | explicit | A ⇒ B only | A_stronger | A = tangentSpace_eq_range_graph ∧ remark_4_2_9 (universe 0) ∧ lemma_3_6_9_relOpen ∧ IsInGoodPosition.isInGoodPositionIn_of_le. The main conjunct remark_4_2_9 is equivalent to B: B uses its own chart reading IsGoodPositionAtB of Definition 4.16 (verbatim the blind V4_38's), which for tame X, smooth A an |
| V4_44 | restated | neither | equivalent | Definition item: only IsGeneralPositionRetractAt, SubmanifoldData.IsGeneralPositionChart and MPolyfold.IsGeneralPositionAt are listed, so A = True and both implications are vacuous (flagged); the content is B, proved outright (B_holds): for a smooth submanifold A and a ∈ A, the project's IsGeneralPo |
| V4_46 | restated | neither | incomparable | A consists of level-0 coordinate lemmas at the corner 0 (E_0 = {λ = 0}, adding E_0-vectors preserves C and d_C, λ/_N onto ℝⁿ when N + E_0 = E, a CLOSED ALGEBRAIC complement Y ⊆ E_0 that is good, d_{N∩C} = d_C on the slice with the CONSTANT sc-structure on N); B states the text's step at the sc level |
| V4_47 | explicit | A ⇒ B only | A_stronger | A = exists_scComplement_le ∧ isGeneralPositionRetractAt_of_sup_eq_top: general sc-linear algebra (any finite-dimensional smooth N, any sc-subspace TR, M = N + TR) and its chart form for an arbitrary sc-retract Q ⊆ R.retract, R tame for T, at a smooth level-1 point y with T_yQ + E_0 = E. B is the ins |
| V4_49 | restated | A ⇒ B only | A_stronger | A = sup_minimalSubspaceWith_eq_top ∧ sup_minimalSubspaceWith_eq_top_graph ∧ theorem_4_2_11_chart: statements about an arbitrary sc-space with a tame retraction R (presentation T) and an sc⁺-retraction t onto Q ∋ 0 with T₀Q in general position: N + E_0 = E, a CLOSED GOOD complement Y = ker p ⊆ E_0, the |
| V4_50 | restated | neither | incomparable | Statements (2) d_X = d_A on A ∩ U and (3) general position on A ∩ U agree and are derived from A (A_to_B23, rt_check OK; paracompactness of A from metrizability). (1) and (4) differ in content: A counts the faces of the chart's MODEL RETRACT O through ψ(x) = 0 (Corollary 2.41 in a tame chart centred |
| V4_53 | restated | equivalent | equivalent | A = type of prod_rn_isTame (universe 0; fibreSet, rnPres, IsStratRegularPoint, IsStratRegularValue are vocabulary). B = (i) ℝᵐ × X with the product structure is tame for tame X ∧ (ii) the project's IsStratRegularPoint is the text's 'regular point of p_σ' in a product chart. (i) is literally A up to  |
| V4_54 | stronger | A ⇒ B only | A_stronger | Hypotheses agree (both read the misprinted (2) as general position of A at every point, Definition 4.21; /λ/ = √Σλᵢ² vs Σλᵢ² ≤ ε²; B's ∃-paracompact IsTameSubmanifold gives A's IsSmoothSubmanifold, instance and tameness). Conclusions differ in one point: A's Σ consists of stratified regular values ( |
| V4_55 | explicit | A ⇒ B only | A_stronger | A = quotDim_le_finrank_of_eq_sup ∧ remark_4_3_2_chart ∧ remark_4_3_2_codim ∧ remark_4_3_2 ∧ remark_4_3_2_not_mem_boundary (universe 0). A ⇒ B is proved entirely from A plus chart-change glue: B quantifies over EVERY tame chart and presentation for (a) and over EVERY chart (tame or not) for (b), (c), whi |
| V4_57 | restated | neither | incomparable | A = finrank_stratSub ∧ measure_image_stratCritSet (no universe parameters) is the finite-dimensional MODEL of the step: in a finite-dimensional V with onto coordinates ℓ, dim stratSub ℓ σ + #σ = dim V, and for f ∈ C^∞(O ∩ {ℓ ≥ 0}) the stratified critical values f(stratCritSet) are null for every Haa |
| V4_58 | stronger | A ⇒ B only | A_stronger | A = exists_solution_smooth ∧ theorem_3_8_22_smooth ∧ exists_radii ∧ Radii.contDiffOn_τ ∧ theorem_3_8_22 (no universe parameters). A ⇒ B: B is Theorem 3.78 for every j ∈ ℕ ∪ {∞}, j ≥ 1, in the blind coordinates; the case j = ∞ is an instance of theorem_3_8_22_smooth, finite j of theorem_3_8_22 (glue of V3_63 |
| V4_62 | restated | neither | incomparable | A = isGeneralPositionRetractAt_slice (no universe parameters) is a chart lemma: for retractions t (onto the chart model of A in ℝᵐ ⊕ E, inside id × r with r tame for T_X) and τ (sc⁺, onto the chart model of the fibre), general position of t at z plus stratified regularity plus the hypothesis hTQ (T_ |
| V4_63 | restated | neither | incomparable | A = exists_local_family (universe 0): for X tame, A ⊆ ℝᵐ × X a smooth submanifold in general position everywhere (no compactness, no (1), no tameness of A), each z₀ ∈ A has an open U and a null CV with FibreLocal at every z ∈ A ∩ U, z.1 ∉ CV (stratified regularity T_zA ∩ E_z ↠ ℝᵐ, local sc⁺-data for |
| V4_64 | stronger | B false | A_narrower | A = theorem_4_3_1_of_subset (universe 0): Theorem 4.23's conclusions over any parameter set S, proved with a COUNTABLE subcover of A (A is second countable). B formalizes the text's covering step literally: every choice of open neighbourhoods U(z) of the points of K = {z ∈ A : /p(z)/ ≤ ε} has a finit |
| V5_3 | restated | B ⇒ A only | equivalent | A = IsAuxNorm.nonneg ∧ IsAuxNorm.smul (universes 0); the listed IsCompleteFiberNorm/IsAuxNorm are vocabulary. The real comparison is B itself, proved outright (B_holds): the blind topology oneTopology on Y_{0,1} is definitionally the project's instance on Bd.One (topology_eq : rfl; (E.prod F.shift)  |
| V5_4 | same | A ⇒ B only | A_stronger | A = lemma_5_1_2 ∧ exists_le_mul_norm_liftOne ∧ IsAuxNorm.exists_norm_liftOne_le ∧ IsAuxNorm.exists_bounds ∧ lemma_5_1_2_literal (universes 0). lemma_5_1_2_literal is B itself (B's fiberNormOne c y unfolds to ‖(c.liftOne y).2‖): B_gives_lemma_5_2_literal, and A ⇒ B could be read off it; the recorded A_to_B |
| V5_5 | same | A ⇒ B only | A_stronger | A = proposition_5_1_3_exists ∧ continuous_gluedNorm ∧ isCompleteFiberNorm_gluedNorm ∧ gluedNorm_bounds (universes 0, chart index type also at 0). The first conjunct is B exactly (every strong bundle, no tameness, ∃ N, IsAuxNorm N), so A ⇒ B is projection. B ⇒ A fails because the other three conjuncts  |
| V5_6 | same | equivalent | equivalent | A = proposition_5_1_3_compare (universes 0) is literally B: for auxiliary norms N₀, N₁ of any strong bundle (no tameness) there is a continuous f : X → ℝ, f > 0, with f(P w)·N₀(w) ≤ N₁(w) ≤ f(P w)⁻¹·N₀(w) for all w ∈ Y_{0,1}. Both directions are instantiation; same setting, same instance arguments. |
| V5_7 | explicit | A ⇒ B only | A_stronger | A = IsProper.isWeaklyProper (for any continuous f) ∧ IsWeaklyProper.isCompact_solutionSet (universes 0); AuxLe/IsWeaklyProper/IsProper are vocabulary. B's definitional conjuncts hold by Iff.rfl (solSetB = solutionSet, suppB = closure{¬IsZeroAt}, NLe = AuxLe, same quantifier structure over auxiliary  |
| V5_10 | stronger | A ⇒ B only | A_stronger | Same notions on both sides (IsScFredholmSection — at HEAD the germ reading of Definition 3.14 —, IsProper, IsWeaklyProper, solutionSet = {x / IsZeroAt P f x}); A is theorem_5_2_2_preprint (compact solution set => proper) and theorem_5_2_2_iff (proper <-> weakly proper <-> compact solution set) for an arbitrary M |
| V5_11 | same | equivalent | equivalent | Both: for an sc-Fredholm section (IsScFredholmSection, germ reading on both sides; no tameness on either side) and a zero x there are open, nested U(i) containing x such that the closure in X_0 of the zeros in U(i) is a compact subset of X_i with the project's level topology. A phrases it as 'the cl |
| V5_12 | stronger | A ⇒ B only | A_stronger | A = theorem_5_2_4 ∧ tendsto_smoothLevel_iff ∧ smoothLevel_topology_eq ∧ metrizableSpace_smoothLevel (universes 0). Main content agrees: for an sc-Fredholm section (IsScFredholmSection, the germ reading on both sides) with S = f⁻¹(0) compact in X₀, S ⊆ X_∞ and S is compact in X_∞; B's own inverse-limit |
| V5_13 | same | A ⇒ B only | A_stronger | A = corollary_5_2_5 ∧ corollary_5_2_5_two ∧ StrongBundle.solutionSet_sectionShift ∧ isCompact_solutionSet_level (universes 0); B (r2) = over a tame X, for sc-Fredholm f (germ reading) with compact f⁻¹(0), for every i the iterated index raise f^i (P^{i+1} = (P^i).shift, f^{i+1} = sectionShift f^i) is sc- |
| V5_14 | same | A ⇒ B only | A_stronger | A = the twelve theorems of the decls (universes 0), among them corollary_5_2_5_isScFredholmSection (f sc-Fredholm ⇒ f¹ sc-Fredholm on P¹ = StrongBundle.shift, germ reading, no tameness/compactness); B (r2) = for sc-Fredholm f and every i, the iterated f^i is sc-Fredholm on the iterated P^i (no tamenes |
| V5_16 | restated | neither | A_stronger | Definition item. A = AdmitsBumpFunctions.weak ∧ admitsBumpFunctionsWeak_of_dense ∧ AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth ∧ admitsBumpFunctions_of_hilbert (universe 0); AdmitsBumpFunctions, AdmitsBumpFunctionsWeak, HasBumpAt vocabulary. The definitions agree with B's by Iff.rfl (AdmitsBumpF |
| V5_17 | same | B ⇒ A only | A_narrower | Same conclusion on both sides (sc-smooth f : X -> [0,1], f(x) = 1, tsupport f ⊆ U, f = 1 near x), same setting (no tameness). The only difference is the hypothesis: A (proposition_5_5_3 / proposition_5_3_2, universe 0) assumes AdmitsBumpFunctions (a bump with f(x) != 0, the project's reading of Def. 5 |
| V5_20 | stronger | neither | incomparable | A = lemma_5_3_3 (universes 0): for ANY strong bundle (no tameness), assuming AdmitsBumpFunctions (bump with f(x) != 0), an auxiliary norm, smooth x and e in (Y[0])_inf over x, it gives an sc+-section s with s(x) = e, supp s ⊆ U and N(s(y)) < N(e) + eps for EVERY y. B assumes tameness of base and bund |
| V5_21 | restated | A ⇒ B only | A_stronger | A = allowableDist_le_iff ∧ TrivialBundle.not_completeSpace_allowableSections ∧ completeSpace_allowableSections_empty ∧ TrivialBundle.completeSpace_allowableSections_point (universes 0); allowableSections, sectionDistAt, allowableDist, allowableMetric vocabulary. Notions agree: Γ^{+,1}_U(P) = B's Gam |
| V5_22 | restated | A ⇒ B only | A_stronger | A = remark_5_3_4 ∧ IsAuxNorm.auxLe_of_sectionAdd ∧ IsInAllowableCompletion.isClosed_solutionSet_sectionAdd ∧ remark_5_3_4_completion ∧ remark_5_3_4_of_isScFredholmSection (universes 0); IsInAllowableCompletion is B's InCompletion (inCompletion_of). B: f sc-Fredholm (germ reading, as in A) with compact  |
| V5_23 | restated | A ⇒ B only | A_stronger | A = IsLinSurjAt.linAt_surjective (universes 0): at a zero y of an sc-smooth section where the linearization is onto in SOME strong bundle chart (IsLinSurjAt), it is onto in EVERY chart around y at the level-1 lift of φ'(y). B: for sc-smooth g, the project's IsTransversal g (IsLinSurjAt at every zero |
| V5_29 | explicit | neither | incomparable | A = theorem_5_3_5_generic (universes 0): the generic family form (for every s₀ with N(s₀) ≤ 1−ε a finite family s₀ + Σλᵢtᵢ that is allowable, transversal, with compact solution set which, if nonempty, is a tame manifold without boundary of dimension the Fredholm index, for a.e. small λ), assuming str |
| V5_30 | explicit | B ⇒ A only | A_narrower | A = theorem_5_3_5_preprint ∧ StrongBundle.allowableDist_le_iff (universes 0). theorem_5_3_5_preprint assumes AdmitsBumpFunctions (a bump with f(x) ≠ 0) and IsScFredholmSectionTame f (now the germ reading with tame germ data; changed in place), B assumes AdmitsBumpFunctionsWeak (literal 'not identically zero') and IsScF |
| V5_31 | restated | neither | equivalent | A = IsGeneralPositionGerm.isLinSurjAt (universes 0): general position at y gives IsLinSurjAt at y, a projection of the definition. B says that at zeros the project's IsGeneralPositionGerm equals the text's notion as B reads it (some tame strong bundle chart, a level-1 lift z, the linearization onto  |
| V5_36 | restated | neither | A_stronger | A = IsParamGP.comp ∧ isGeneralPositionGerm_paramSection_of_isParamGP ∧ isParamGP_of_isGeneralPositionGerm ∧ exists_sections_isParamGP (universes 0). B has four parts: (1) the project's IsParamGP equals the text's (i)–(ii) in a chart centred at the point; (2) (i)–(ii) are preserved under Fin.append;  |
| V5_38 | explicit | neither | incomparable | A = theorem_5_3_10_param (universes 0): over a tame X with strong bump functions (f(x) ≠ 0), for every s₀ with N(s₀) ≤ 1−ε a finite family s₀ + Σλᵢtᵢ such that for a.e. small λ the perturbation is allowable and SolutionSetInGeneralPosition holds (transversal, (f+s, x) in general position at every zero, S co |
| V5_39 | explicit | neither | incomparable | Both have a compact solution set, an auxiliary norm, tame germ data (IsScFredholmSectionTame, the germ reading on both sides), an open U with S_{f+s} compact on Γ^{+,1}_U, and a ρ-dense set of perturbations in general position at every zero. A => B fails only on bump functions: B assumes AdmitsBumpF |
| V5_40 | stronger | neither | incomparable | A is theorem_5_3_12_param ∧ IsGoodPositionGermTame.congr_nhds (universes 0; germ reading of Definitions 3.51/3.53 on both sides), in generic form. Assuming strong bump functions (f(x) ≠ 0) and NO tameness, it gives a finite family t_i with supports disjoint from ∂X such that, for a.e. small λ, s_λ = Σλᵢtᵢ i |
| V5_41 | restated | neither | A_narrower | A = IsGenCompactHomotopy.isCompact_solutionSet_restrict (universes 0): the restricted problems have compact solution sets. This is a corollary of the definition and says nothing about whether the definition is correct. B says the project's IsGenCompactHomotopy equals B's notion. The two definitions  |
| V5_42 | explicit | A ⇒ B only | A_stronger | A = lemma_5_3_16_preprint ∧ ne_zero_of_isCompl_ker ∧ exists_isCompl_ker_of_ne_zero (universes 0): linear algebra on ARBITRARY real modules. B is the chart instance at a smooth zero: (1) a one-dimensional SMOOTH sc-complement Z of ker dt(x) in T_zO, split on every level, exists iff dt(x) ≠ 0 on T_zO; (2) a uniq |
| V5_44 | restated | neither | incomparable | A = exists_scPlusSection_linAt ∧ lemma_5_3_17 (universes 0). B is Lemma 5.24 in the setting of Lemma 5.23: tame strong bundle, AdmitsBumpFunctionsWeak, f with tame germ data (germ reading), x a smooth zero, Z a smooth line splitting T_zO = Z ⊕ ker dt(x), b : T_xS → Z with dt∘b = τ, and any open V ∋ x. |
| V5_45 | restated | neither | incomparable | A ⇒ B fails for two genuine reasons. (1) B assumes only AdmitsBumpFunctionsWeak (f ≢ 0), but A needs AdmitsBumpFunctions (f(x) ≠ 0), and the project has only strong ⇒ weak. (2) B reads 'an associated open neighbourhood U' universally: for EVERY open U ⊇ S_f with S_{f+s} compact for all s ∈ Γ^{+,1}_U |
| V5_46 | stronger | A ⇒ B only | A_stronger | A = isInGoodPositionIn_of_scComplement_le_reduced ∧ IsGeneralPositionGerm.isGoodPositionGerm ∧ IsGeneralPositionGerm.isGoodPositionGermTame (germ theorems at universes 0). B is pointwise: for a tame strong bundle and f with tame germ data, at a zero, IsGeneralPositionGerm ⇒ IsGoodPositionGermTame. B |
| V5_47 | restated | neither | equivalent | Definition item: only MPolyfold.IsScSmoothPartitionOfUnity and MPolyfold.AdmitsScPartitionsOfUnity are listed, so A = True and both implications are vacuous. The content is B itself, proved outright as B_holds: the project's notion (Mathlib PartitionOfUnity ι X, subordinate, every ρᵢ sc-smooth into  |
| V5_50 | same | neither | equivalent | Definition item: only HasContDiffBump and AdmitsContDiffPartitionsOfUnity are listed, so A = True and both implications are vacuous. The content is B itself, proved outright as B_holds: the project's HasContDiffBump V k (∃ f, ContDiff ℝ k f ∧ f ≠ 0 ∧ IsBounded (support f)) is B's HasCkBumpB V k (∃ f |
| V5_51 | restated | neither | incomparable | A is the type of the listed lemma closure_inter_ball_subset: O ∩ cl B(z, r/2) ⊆ O when B(z, r) lies in the open W' with C ∩ W' the domain of a retraction onto O. It has no universe parameters and says nothing about bump functions. B claims the project's LocalModel.HasBumpProperty (f(x) ≠ 0) equals t |
| V5_52 | explicit | neither | incomparable | The two sides read 'f ≠ 0' differently. A (theorem_5_5_7, universe 0) uses the strong reading: AdmitsBumpFunctions and LocalModel.HasBumpProperty, both with f(x) ≠ 0. B uses the literal reading of Definitions 5.29/5.33: AdmitsBumpFunctionsWeak and HasBumpPropertyWeak, both with f not identically zero |
| V5_53 | restated | A ⇒ B only | A_stronger | A is hasBumpProperty_of_quadratic ∧ proposition_5_5_8 ∧ admitsBumpFunctions_of_hilbert (the last at universe 0). A ⇒ B is proved using A, and the derivation has two parts. First, proposition_5_5_8 applies to B's Hilbert E₀ (‖v‖² = b(v, v); B's symmetry of b is unused) and gives the pointwise bump prop |
| V5_54 | restated | neither | equivalent | Definition item: only LocalModel.HasApproxProperty is listed, so A = True and both implications are vacuous. The content is B itself, proved outright as B_holds. The two definitions differ only in how the open V ⊆ O is presented. The project uses an open W ⊆ E₀ with cl_E(O ∩ W) ⊆ O and supports (tak |
| V5_55 | narrower | B false | incomparable | A is hasApproxProperty_restrict ∧ MChart.isClosed_inter_preimage, both at universe 0. hasApproxProperty_restrict gives the approximation property only for a chart restricted to an open s with cl_X(s) ⊆ dom φ. B is false (not_B, as its author predicted). It reads the text's 'the sc-smooth function f  |
| V5_56 | restated | equivalent | equivalent | A is the conjunction (universe 0) of the project's four lemmas for (ii)=>(i): exists_small_nhds, exists_approx, exists_isScSmoothMap_urysohn and admitsScPartitionsOfUnity_of_approx. B is the text's quotient construction (W, Q, f, g, γ = ĝ/Σĝ) plus conclusion (i). The project's proof is different (Ur |
| V5_57 | restated | equivalent | equivalent | Both sides use the same notions, AdmitsScPartitionsOfUnity (Definition 5.28) and LocalModel.HasApproxProperty (Definition 5.36). The only difference is how 'an atlas' is written. A (theorem_5_5_10, universe 0) uses a set S of charts of the structure (PX.IsChart) covering X. B uses an MAtlas A with A.E |
| V5_58 | explicit | equivalent | equivalent | A (proposition_5_5_11; it has no universe parameter, LocalModel lives in Type) and B make the same claim: for every local model M, if E_0 admits C^infinity partitions of unity (AdmitsContDiffPartitionsOfUnity (M.E 0) ⊤), then M.HasApproxProperty. B writes M.E.lvl 0 for the project's M.E 0. That is the |
| V5_59 | restated | equivalent | equivalent | A is mem_cZero_iff ∧ norm_cZero (universe 0). cZero, IsCoordinatewiseContDiffEmbedding and TorunczykStatement are vocabulary that B compares with its own notions. (1) Elements: mem_cZero_iff is literally B's c0SetB condition; that every function satisfying it is bounded, hence lies in ℓ^∞, is proved |
| V5_60 | same | neither | equivalent | Definition item: only IsWCG and IsReflexive are listed, so A = True and both implications are vacuous (flagged). The content is B, proved outright (B_holds): for every real Banach space V : Type, the project's IsWCG V is B's IsWCGB V. The two differ only in how 'weakly compact' is written. The proje |
| V5_61 | same | equivalent | equivalent | Both sides use the project's IsReflexive and IsWCG. A (all three theorems at universe 0) is stated for every real normed space; B, following the text's 'E a Banach space', only for complete ones. A => B is specialization. B => A has three parts. (i) A reflexive normed space is automatically complete |
| V5_63 | narrower | B ⇒ A only | A_narrower | Both sides use the same approximation property, and their Hilbert notions agree: the project asks for a continuous bilinear b with //v//^2 = b(v,v), B also asks b to be symmetric, and symmetrizing to (b + b^T)/2 makes them equal (hilbert_iff). The real difference is that corollary_5_5_17 takes the cit |
| V6_1 | restated | B ⇒ A only | A_narrower | The project's Lin(f, x) (ChartPoint.linSet) is built from GLOBAL sc⁺-sections s with (f + s)(x) = 0; the text's, and B's LinB, from LOCAL sc⁺-sections in a chart (the text's s(y) = R(y, f(x))). B's clause (1) asserts linSet = LinB at every smooth point, and with B's (2) (LinB nonempty) this already  |
| V6_2 | same | equivalent | equivalent | The definitions are the text's: maxPow E is literally ⋀[ℝ]^(dim E) E, maxPowDual E is Module.Dual ℝ (maxPow E), maxPowDualMap is the transpose of maxPowMap (B's (1), (2), (6) hold by rfl), and A's finrank_maxPow, maxPowMap_wedge, maxPowMap_ne_zero_iff, maxPowMap_comp, dualVec_self give B's (1), (3), |
| V6_3 | same | equivalent | equivalent | Same iotaDual on both sides. A's iotaDual_wedge_wedge and iotaDual_wedge_dualBasis give B's (1) and (4) at k = dim E (proof irrelevance for the dimension casts), and A's iotaDual_ne_zero gives B's (3) (a nonzero map of lines is bijective). B's (2), the convention λ({0}*) = ℝ, is not in A and was pro |
| V6_4 | same | equivalent | equivalent | A (proposition_6_3_2, universes at 0) and B are the same equality of linear maps lambda*(Phi) o iota_F = iota_E o lambda(Phi*) : lambda(F*) -> lambda*(E) for a linear isomorphism Phi : E ≃ F of finite-dimensional real spaces, built from the same maxPowDualMap, iotaDual and maxPowMap. The only differen |
| V6_5 | same | equivalent | equivalent | The row is mostly definitions (FourTermExact, Choice, Choice.value, canonicalChoice, phi, phiEquiv); its only theorem, A = phi_ne_zero (Φ_E ≠ 0), is equivalent to B's clause (3) (Φ_E bijective) because both sides are lines: a nonzero map of lines is bijective, an injective map out of a line is nonze |
| V6_6 | restated | equivalent | equivalent | A (lemma_6_3_3) says the project's Φ_E, defined by (91) from the canonical choice, satisfies (91) for every project Choice; B is that same statement for B's Choice91 (bases indexed by Fin (finrank ·), dimension equations as fields; the wedges are definitionally the project's wedgeB/wedgeC/source), con |
| V6_7 | restated | equivalent | equivalent | A (proposition_6_3_5) is Ψ_E(w_C ⊗ (w_A ⊗ w_D*)) = w_B for every project Choice; B conjoins (1) ῑ(v ⊗ b ⊗ v*) = b, (2) the defining formula (92) Ψ_E(c ⊗ h) = ῑ(c ⊗ Φ_E(h)), (3) Ψ_E bijective, (4) the same formula as A for every Choice91 and every φ_D with φ_D(w_D) = 1. (1) is contractDual_tmul (ῑ(v ⊗  |
| V6_8 | same | equivalent | equivalent | A (finrank_fredholmDet) is 'det(T) is a line' for Mathlib-Fredholm T (strict, closed range, finite-dimensional kernel, finite codimension, complemented kernel) between normed spaces, not necessarily complete; B, for Banach spaces and textbook-Fredholm T, conjoins (1) fredholmDet T = λ(ker T) ⊗ λ*(co |
| V6_9 | same | neither | equivalent | Definition item with two extra theorems. B is the definitional reading of Definition 6.8 (for Banach spaces and textbook-Fredholm T, FredholmOrientation T = Module.Ray ℝ (λ(ker T) ⊗ λ*(coker T))); it holds by rfl (B_holds): the project's FredholmOrientation is the abbrev Module.Ray ℝ (fredholmDet T) |
| V6_10 | same | A ⇒ B only | A_stronger | The definitions agree literally: B's IsGLP/PiT/PLe are the project's IsGoodLeftProj (same three fields), goodLeftProjs and ProjLE (isGLP_iff, piT_eq, pLe_iff, rt_check OK), and fredIdx is fredholmIndex by rfl; B's classical IsFredholmOp is Mathlib's IsFredholm on Banach spaces (isFredholm_of_banach  |
| V6_11 | stronger | A ⇒ B only | A_stronger | A = lemma_6_10_preprint (no Fredholm hypothesis, arbitrary normed spaces) and lemma_6_10_text_reading_preprint (a concrete R^2 counterexample to the text's construction). A => B by instantiating lemma_6_10_preprint. B => A fails: B only covers Banach spaces with T Fredholm, and the conjunct lemma_6_10_text_reading_preprint is unrelate |
| V6_12 | same | A ⇒ B only | A_stronger | The maps are definitionally B's (jMap = projSeqJ, PhiMap = projSeqPhi, piMap = projSeqPi, all rfl; IsGLP = IsGoodLeftProj fieldwise), and A => B is instantiation. The only difference: A (proposition_6_4_10) has no Fredholm hypothesis on T, B keeps the text's standing assumption that T is Fredholm (unused by |
| V6_13 | same | equivalent | equivalent | A says the project's gammaProj hT hP satisfies (91) for every Choice of E(T,P) (gammaProj_tmul) and for every family choice (gammaProj_wedge_tmul); B says some isomorphism det T -> det PT satisfies (91) for every family choice. A => B: gamma := gammaProj, with A's family form; the C-side cosets (cok |
| V6_14 | same | equivalent | equivalent | Same notions: B's gammas are characterized by (91) (IsGamma) and are exactly the project's gammaProj (gammaProj_eq_of_isGamma, from B-side data plus the definition of gammaProj; conversely isGamma_gammaProj from V6_13's gammaProj_wedge_tmul, not banned here); B's identification det(P(QT)) = det(PT)  |
| V6_15 | same | equivalent | equivalent | A (corollary_6_4_12) is the formula (γ^P_{RT})⁻¹ ∘ γ^P_{ST} = γ^R_T ∘ (γ^S_T)⁻¹ for the project's gammaProj, with the identification linDetEquivOfEq of det(P(ST)) = det(P(RT)) in between; B states the same formula (and independence of P) for arbitrary maps characterized by (91) for every choice (IsGam |
| V6_16 | same | A ⇒ B only | A_stronger | B's Tphi, jS, piS, clsPhi are definitionally the project's T.coprod φ, stabJ, stabPi, stabClass, and B's exactness conclusion is literally lemma_6_14's, so A ⇒ B is instantiation (B's IsFredholmOp and completeness hypotheses unused). B ⇒ A fails for genuine reasons: lemma_6_4_14 holds for arbitrary no |
| V6_17 | same | equivalent | equivalent | A (stabPsi_dualVec) is (94) for the project's specific ψ = stabPsi hφ : λ*(ℝⁿ) → λ*(F/R(T_φ)) (a smulRight with value 1* at (e₁∧…∧eₙ)*), with det taken as (Pi.basisFun).det c; B is (94) for every linear ψ with ψ((e₁∧…∧eₙ)*) = 1* into λ*(Z) for an arbitrary subsingleton Z, plus the existence of such  |
| V6_18 | restated | A ⇒ B only | A_stronger | A = stabIota_bijective ∧ stab_card_eq ∧ isCompl_range_stabPi_span ∧ proposition_6_4_15 for the project's ι_φ = lTensor(stabPsi) ∘ (stabSeq hφ).phi. A ⇒ B: m + l = n is stab_card_eq; B's Φ_E (any map with (91) for every choice) agrees with (stabSeq hφ).phi on the given vector (phi_wedge_tmul for the sa |
| V6_19 | same | equivalent | equivalent | Same notions on both sides (fredholmDet, wedge, dualVec, kerInl/kerInr/cokerInl/cokerInr, prodMap). A => B: Psi := directSumDet, an equivalence by directSumDet_bijective, and B's formula is definition_6_4_16 (B's length proofs hk, hc agree with directSumVec's by proof irrelevance). B => A: T ⊕ S Fredh |
| V6_20 | stronger | equivalent | equivalent | Same notions (IsGoodLeftProj = Π_T, Submodule.IsTopCompl, operator norm); A's (e : Y →L R(P)) = projRestrict P S Y is B's pointwise e y = P (S y). A has no hypothesis that T is Fredholm, B has one, so A => B is instantiation. B => A is not instantiation: B is applied to a different Fredholm operator |
| V6_21 | restated | equivalent | equivalent | B's hypotheses are exactly the fields of a LocalDetChart, so A => B instantiates A at that chart: y := ySol, Φ(S,k) = (S, kerMap S k) with inverse (S,x) ↦ (S, kerProj x) (A's third and fourth conjuncts), continuous by A's first conjunct and continuity of kerProj (kerProj is definitionally B's projec |
| V6_22 | narrower | B ⇒ A only | A_narrower | A = frame_ne_zero (the chart frame ω(S) ≠ 0) ∧ proposition_6_5_4 (frames of two charts with the same P differ by a continuous nowhere-zero factor on the common ball); B = λ(ker PS), λ*(coker PS) and DET(T,P,ε) are topological line bundles for the final topologies of ALL continuous local frames. B =>  |
| V6_23 | stronger | neither | incomparable | A = gammaProj_frame_eq (an explicit formula (91): γ^Q_{PS}(ω_c(S)) = (det(kerProj(k,z))·det([d],[f])⁻¹)·ω_{c'}(S)) ∧ lemma_6_5_5 (γ^Q_{PS}(ω_c) = g·ω_{c'} with g continuous and nowhere zero, for two charts with arbitrary centres and radii, S Fredholm in both balls): statements about chart frames only |
| V6_24 | restated | equivalent | A_narrower | A is exists_localDetChart (universes 0): every Fredholm T is the centre of a LocalDetChart. B's admissible triples IsDetChart T P ε are exactly the (c.T, c.P, c.ε) of the project's charts (chartOf/hcOf; Y is existential in B), so B (1) ⇔ A, and B_to_A uses B (1). B (2), that γ_(T,P,ε) is a bijection |
| V6_25 | same | neither | equivalent | Definition item: only detBasis is listed, so A = True and both implications are vacuous. The content is B (detBasis E F = detB), proved outright as B_holds. The project's 𝓑: B ⊆ c.pretriv.source with c.pretriv '' B open in F(E,F) × ℝ. B's 𝓑: B lies over the ball of an admissible (T,P,ε) and γ(B) is  |
| V6_26 | same | A ⇒ B only | A_stronger | Both sides use the same 𝓑 (detBasis_eq, with the glue of V6_25). A (proposition_6_5_7, universes 0) says 𝓑 is a topological basis of the project's topology 𝒯, the total-space topology of detPrebundle. B says 𝓑 is a basis of generateFrom 𝓑. A ⇒ B uses A: IsTopologicalBasis.eq_generateFrom gives 𝒯 = ge |
| V6_27 | same | A ⇒ B only | A_stronger | A (proposition_6_5_8, universes 0): for 𝒯, VectorBundle ℝ ℝ DetFiber, and every chart c has an atlas trivialization e with e.baseSet = c.baseSet and e = c.pretriv. B: for generateFrom 𝓑, every point lies in a fibrewise-linear trivialization with fibre ℝ, and every γ_(T,P,ε) is a homeomorphism from th |
| V6_28 | same | equivalent | equivalent | A = lemma_6_5_9 ∧ lemma_6_5_9_local (universes 0): the transition function g(S) = c'.coord S (c.coordInv S 1) is continuous and nowhere zero on the common ball (locally: a continuous nowhere-zero φ near each S₀). B = Formula ∧ TopIso: TopIso (the transition (S, t) ↦ (S, coord'(coordInv t)) is a homeom |
| V6_30 | stronger | neither | incomparable | A = proposition_6_6_1 (universes 0): for a NONEMPTY convex set C of Fredholm operators between arbitrary Banach spaces, DetOn C is a vector bundle with exactly two orientations. B: for every chart point of a smooth x, Lin(f, x) is convex and contractible, DET(f, x) is a vector bundle and has Nat.card |
| V6_31 | restated | B ⇒ A only | A_narrower | A = isFredholm_of_mem_linSet ∧ exists_two_or ∧ nonempty_equiv_of_two ∧ equiv_eq_of_apply_eq_of_two (first two at universes 0; the last two are stated for Sort u and are instantiated at 1, i.e. for types — at 0 they would speak about propositions). B: (1) every orientation o of DET(f, x) has an oppos |
| V6_32 | narrower | neither | incomparable | A (universes 0) = proposition_6_6_3 plus eight tool lemmas. proposition_6_6_3 assumes PX.AdmitsBumpFunctions and gives open U ⊆ W ⊆ dom φ_c with (1′) two sc-smooth paths in U with equal end points are sc-smoothly homotopic rel end points inside the larger W, (2) compact solution set in cl U, (3) for a |
| V6_33 | narrower | neither | incomparable | A (universes 0) = isZeroAt_paramSection_zero ∧ exists_sections_isGeneralPositionGerm_of_isCompact ∧ lemma_6_6_4. lemma_6_6_4 assumes PX.IsTame, PX.AdmitsBumpFunctions and IsScFredholmSectionTame f, a globally sc-smooth Φ : ℝⁿ → X and a global sc⁺-section S with (f̃ + S)(q, Φ q) = 0 near [0,1]ⁿ, and gi |
| V6_34 | narrower | neither | incomparable | The two sides state different things. A is the analytic core used later: in every chart the kernel has the dimension of the index (finrank_linKer); along a continuous family of zeros in tame good position inside ONE chart, the kernels ker Lin(z_q) ⊆ E₀ have continuous local frames and form a Subspac |
| V6_35 | restated | equivalent | equivalent | Both sides use the project's SubspaceFamily, det (λ(L) with the frame-trivialization bundle structure) and LineOrientation, and the base [0, 1] is unitInterval on both sides (here B did not replace [0, 1] by ℝ). B says that an orientation of one line λ(L_q₀) extends to exactly one orientation of λ(L |
| V6_37 | restated | neither | incomparable | B's claim: in the product chart (ofProd p.c 0).toChart q₀ at (0, z), F_t'(λ, v) = T v + Σ λᵢ sᵢ(φ(t), t), with T = (f − s(·, t))'(φ(t)) and T(ℝᵏ × O) ≅ ℝᵏ × T_zO. This is one instance of A's scDeriv_paramSection_apply (at a = r₀ = 0) together with A's ofProd_mem_tangent_iff. A needs one hypothesis t |
| V6_38 | restated | neither | incomparable | B has four conjuncts. Its first three (j injective, exactness at ker(T ⊕ φ) and at ℝᵏ) are pure linear algebra for any T and φ and are proved outright (B_alg_part, without A). The content is the fourth: c is onto under (P), read as general position of the slice F_t = (f − S) + Σ λᵢ σᵢ at (0, x) over |
| V6_39 | restated | neither | incomparable | A (universes at 0) is the continuation algebra of λ(L) over an arbitrary simply connected, locally path-connected base Q (SubspaceFamily.cont_eq/self/trans/comp/eq_transport) and the push-forward lemmas propagate_self/trans/comp for given stabilized end points. B is the text's construction along a p |
| V6_40 | restated | B false | incomparable | B (the formula (94) principle read literally, without the sign): for every norm-continuous family T_q of Fredholm operators over J = [0,1] with continuous φ_q, T_q ⊕ φ_q onto, and every orientation o_q of DET continuous along q ↦ T_q, the rays Φ(o_q) of λ(ker(T_q ⊕ φ_q)) form an orientation. This do |
| V6_41 | restated | neither | incomparable | B says the project's IsStabKernels.push equals the text's literal push-forward F.push (o₀ ↦ o₀(T_0), Φ_{E_0}, continuation, Φ_{E_1}⁻¹, no sign); the project's push inserts stabSign α(T) = (−1)^{dim coker T} at both end points, and A's lemmas are about that signed push. Proved (push_eq_iff, rt_check_ |
| V6_42 | narrower | neither | incomparable | A (universes at 0): exists_continuousOn_lift_chart and exists_isStabKernels — for Φ : ℝⁿ → X with Φ([0,1]ⁿ) in a chart, S with f̃ + S = 0 along Φ near [0,1]ⁿ and s₁…s_k with the project's parametrized (P) (general position of f̃ + S + Σλᵢsᵢ on ℝᵏ × ℝⁿ × X near [0,1]ⁿ, IsScFredholmSectionTame), the s |
| V6_43 | restated | neither | incomparable | A (universes at 0): pt1_mem_Icc, exists_lift_of_smooth, isZeroAt_sectionAdd_reparamSection, push_eq_of_eq, isPush_reparam, IsPush.split and exists_isPush (tame X admitting bump functions, f with tame germ data, a chart c and W ⊆ dom c with property (3) of Proposition 6.28 giving f̃ + S = 0 along pat |
| V6_44 | restated | B false | incomparable | A (proposition_6_6_7 via IsPush/IsStabKernels.push) is about the sign-normalized push-forward orEquivRay^-1 ∘ α(T1) ∘ propagate ∘ α(T0) ∘ orEquivRay, α(T) = stabSign T = (−1)^{dim coker T}; B's Facts.push is the text's map read literally, without α. For the same data they differ by α(T0)α(T1), which  |
| V6_45 | restated | A ⇒ B only | A_stronger | A ⇒ B from the conjunct propagate_append: the operators T_t of the enlarged reading equal those of the original (same s), its stabilization is appendStab φ_t ψ_t with ψ_t = Φ'_t(0 ++ ·), and the side conditions of propagate_append (λ ↦ λ ++ 0 maps L_t into L'_t, the added coordinates of L'_t are ont |
| V6_46 | same | neither | incomparable | Proved: A ⇒ B(1)∧(2)∧(3) (A_to_B123: linear reparametrization = A's affine reparam with b = 0; slices = project lemma IsScPlusSection.pullbackSlice; the convex combination over the square = A's reparam along (τ,t) ↦ t, product rule and sum), and A ⇒ B(4) for g with tame germ data (A_to_B4_tame, afte |
| V6_47 | restated | B false | incomparable | A (push_square) is invariance of the sign-normalized IsStabKernels.push under deformations with fixed end points over any parameter space; B(1) asserts invariance of the literal, unsigned Facts.push along the convex homotopy s^τ. They differ by α(T^τ_0)α(T^τ_1) with α = (−1)^{dim coker}, and T^τ_{0, |
| V6_48 | narrower | neither | incomparable | A = theorem_6_6_11 ∧ push_eq_of_homotopy (universes at 0). B = (B1) every smooth x of a tame X has an open, sc-smoothly contractible U ∋ x with HasLocalPropagation in some chart, for any sc-Fredholm f, ∧ (B2) two sc-smooth paths with the same end points in an open sc-smoothly contractible U are sc-smo |
| V6_49 | narrower | B false | incomparable | B is false (not_B, as its author predicted): the literal composition formula ψ(β(s)) on [1/2, 1] forces φ(β(1/2)) = ψ(β(1/2)) at s = 1/2; for φ = id (from 0 to 1) and ψ = 1 + id (from 1 to 2) on ℝ¹ this is impossible whatever β(1/2) is. So ¬(A → B) (not_A_to_B, since A holds) and B ⇒ A only ex falso |
| V6_50 | restated | neither | incomparable | A = exists_two_isContinuousOrientation ∧ exists_orientableNbhd ∧ exists_isOrientableNbhd (universes 0). B: (1) path independence and ψ_*o_{y₁} = o_{y₂} in an orientable neighbourhood, (2) IsContinuousOrientation (V = U) = B's IsContOrB, (3) an orientable neighbourhood (open, sc-smoothly contractible |
| V6_51 | same | A ⇒ B only | A_stronger | A = mem_smoothSet_of_isScSmoothMap ∧ contDiff_pt2_comp ∧ isScHomotopyRel_reparam ∧ reparam_mem ∧ concatPath_halves (universes 0). B: ScHomotopic is an equivalence relation on the paths x → y, homotopic paths have the same end points, and the composite through any admissible β (corrected ψ(β(s) − 1), |
| V6_52 | restated | B false | A_narrower | B is false (not_B, rt_check OK), as its author predicted. B uses the literal p. 228 formula, psi(beta(s)) on [1/2,1]. Take beta0(s) = kappa(3s) + kappa(3s-2), which satisfies all of B's conditions. In X = R^1, phi = the constant path at 0 and psi = id, a path from 0 to 1, have no composite: at s = 1 |
| V6_55 | restated | neither | incomparable | A's exists_two_orx assumes Bd.HasScPlusSectionsThrough, and B's setting does not give it. The project's Lin(f,x) (linSet) is built from GLOBAL sc+-sections s with f(x)+s(x)=0. When there is none, linSet is empty, and Or = LineOrientation over an empty base has exactly one element, so B (Nat.card = 2 |
| V6_56 | restated | neither | incomparable | A is the abstract transport theory of an arbitrary LocalTransport: any family O x, good open sets covering X_inf, and push-forwards that compose. It covers dyadic transport, Lebesgue numbers, (*), homotopy invariance, reparametrization, concatenation and uniqueness, plus equiv_paste_squares (taken a |
| V6_57 | restated | neither | incomparable | Every theorem of A, theorem_6_6_13_hyp included, assumes PX.AdmitsBumpFunctions, a TAME sc-Fredholm section (IsScFredholmSectionTame), HasScPlusSectionsThrough (from the bumps) and two more paracompactness instance families. B gives none of these; they are satisfiable but not consequences of B. With them  |
| V6_58 | restated | neither | incomparable | A (isOrientableSection_iff_exists) is an internal characterization: Gamma_f([phi]) is path-independent iff some y -> o_y is carried along by Gamma_f. B identifies the project's IsOrientableSection, under hX, hbump, tame hfT and hsec, with the text's notion IsOrientableB (every functor G with B's (*) |
| V6_59 | stronger | B ⇒ A only | A_narrower | A is isOrientableSection'_iff_exists ∧ isOrientableSection_iff (universes 0), stated under tameness, bump functions, tame germ data and sc⁺-sections through points. B ⇒ A works by glue: B's (2) applied to Γ_f = orFunctorMap gives 6.38 ⇔ text-6.39, B's (1) gives text-6.39 ⇔ project-6.39. B's IsGammaF |
| V6_60 | restated | neither | incomparable | B is definitional. For every M-polyfold (no tameness) and every y ↦ o_y, the project's IsSectionOrientation equals the text's D640. The project asks continuity over V, for paths in U, for every orientable pair V ⊆ U. D640 asks continuity over every open, sc-smoothly contractible U with the local pro |
| V6_61 | narrower | neither | incomparable | A is the conjunction of the 16 theorems among the 22 declarations (universes 0). B is Theorem 6.41 plus the non-generic sentence. Hypotheses: A's give B's, since IsSectionOrientation → D640 is proved (D640_of_isSectionOrientation, rt_check OK). B's do not give A's. D640 → IsSectionOrientation needs  |
| V6_62 | narrower | B false | A_narrower | B is false, as its author predicted, and A ⇒ ¬B is proved (A_to_not_B). B asks for an orientation ô of DET(f̂,(t,x)) with ô(L̂) = conjDet(extDet(ω(L))) for every L ∈ Lin(f,x), i.e. the text's h ↦ h̃ WITHOUT the sign (−1)^{dim coker L} that the project puts into extDetN. Counterexample: the trivial b |
| V6_63 | restated | equivalent | equivalent | A (Choice.exists_smul_source_value) is the conclusion of §6.7.1: for two choices χ, χ' of the data of (91), source and value scale by one common r ≠ 0. B is the blind author's three steps: (1) a change of the basis of Z by any σ multiplies both wedges by det σ (and leaves wB ⊗ wC* unchanged if det σ |
| V6_64 | restated | equivalent | equivalent | A is the three lemmas the project extracts from §6.7.2: gammaProj_wedge_tmul (formula (91) for γ^P_T on arbitrary families a, d, b, lifts c), mem_span_append_of_ker (in F: g ∈ ker Q lies in span(d, Tb)) and comp_comp_eq_of_projLE (P(QT) = PT). B is the blind author's computation for the text's speci |
| V7_1 | restated | equivalent | equivalent | The listed theorems are GroupoidStr.π_eq_π_iff, isSaturated_iff and orbitSetoid_eq (universe 0); the rest are definitions, which B characterizes. B (a)/(b): the project's GroupoidStr (total comp whose laws are asked only on composable pairs, units stated as φ ∘ 1_{sφ} = φ) is exactly the text's grou |
| V7_2 | restated | equivalent | equivalent | A is Isotropy.val_mul, val_one, val_inv (universe 0): the group operations of the project's Isotropy x are g * h = g ∘ h, 1 = 1_x, g⁻¹ = ι g, in the text's order. These are verbatim B's last three conjuncts; B's other conjuncts (G_x = {φ / sφ = x = tφ} closed under ∘, 1_x, ι; val injective; range va |
| V7_3 | restated | equivalent | equivalent | B (a)/(b): the project's EpGroupoid is exactly B's text ep-groupoid. The only non-literal points: (3) the project's IsProperMap vs B's 'continuous with compact preimages' — equivalent because X is metrizable (MPolyfold.metrizableSpace), hence compactly generated Hausdorff (isProperMap_iff_isCompact_ |
| V7_5 | narrower | B ⇒ A only | A_narrower | A (universe 0) is Sheet.isScDiffeoOn_hat, exists_sheet, mem_sheetAt, isScDiffeoOn_hat, hat_src: only the sheets and φ̂. B (1)–(3) follow from A (A_to_B_sheets in the file). B (4)–(7) are claims about Tφ = tangentMor φ (Tφ ∘ Tj = Tφ̂ on T_xU(x), with Tj : T_xU(x) → T_xX onto; Tφ : T_xX → T_yX bijecti |
| V7_6 | narrower | B ⇒ A only | A_narrower | A (universes 0) is mem_levelSet_src_iff/_tgt_iff, IsLocalScDiffeo.maxLevel_eq, IsLocalScDiffeo.degIndex_eq, degIndex_src/_tgt. A ⇒ B fails at exactly one conjunct: B's FiltrationB asserts that X_∞ is dense in every X_k for the level-k topology (levelTopology k), for both X and 𝐗; A says nothing abou |
| V7_7 | same | equivalent | equivalent | A is degIndexOrbit_π: d_{/X/}(π x) = d_X(x) (universe 0), which is B (b). B's presupposition (a), d_X(x) = d_X(x') for x ∼ x', also follows from A: π x = π x' (Quotient.sound) so d_X(x) = d_{/X/}(π x) = d_{/X/}(π x') = d_X(x'). The project's well-definedness proof (the Quotient.lift field of degInde |
| V7_8 | restated | equivalent | equivalent | A = exists_tame_chart ∧ IsLocalScDiffeo.isTame ∧ isTame_iff_of_surjective (universes 0, 0). B (a) is Iff.rfl because EpGroupoid.IsTame is defined as X.PObj.IsTame; (b) is isTame applied to s : 𝐗 → X (X.isLocalScDiffeo_src); (c) is literally isTame. B_to_A: isTame and the backward half of isTame_iff_ |
| V7_9 | restated | A ⇒ B only | equivalent | The item is mostly definitions. A has only two theorems, GroupoidFunctor.mor_inv and EpFunctor.ext (universes 0, 0). The real check is B's comparison of the project's definitions with the text, proved in A_to_B. EpFunctor's fields are exactly B's IsFunctorB (s, t, m on composable pairs, u) plus sc-s |
| V7_10 | narrower | B false | incomparable | B reads the remark literally: a functor (f₀, f₁) between ep-groupoids with f₀ sc-smooth has f₁ sc-smooth, plus the local neighbourhoods and the formula. As its author predicted, B does not hold as we read it. not_B applies B to the project's remarkFunctor on ℤ/3 × ℝ ⇉ ℝ (trivial action): the identit |
| V7_11 | restated | equivalent | equivalent | B is that π is open for the quotient topology orbitTop X = coinduced X.π. This is definitionally the project's instance on X.OrbitSpace (Mathlib's quotient topology on Quotient X.orbitSetoid), so A_to_B is proposition_7_1_8 at universe 0. B_to_A: proposition_7_1_8 is B. proposition_7_1_8_isOpenQuotientMap |
| V7_12 | restated | equivalent | equivalent | proposition_7_1_9 states ∃ V : ℕ → Set /X/, (∀ k, IsOpen (V k) ∧ z ∈ V k) ∧ (𝓝 z).HasAntitoneBasis V. This is B's 'open, containing z, V (k+1) ⊆ V k, every open N ∋ z contains some V k' repackaged. HasAntitoneBasis gives the basis property and Antitone, and conversely antitone_nat_of_succ_le with mem_ |
| V7_13 | stronger | equivalent | equivalent | B is proposition_7_1_10 with an extra, redundant z and the hypothesis π x = z, over the same topology (B's orbitTop is definitionally the project's quotient instance). A_to_B is hA.1 X x; B_to_A gets proposition_7_1_10 from B at z = π x. A's second conjunct, proposition_7_1_10_of_isProperMap, is more general |
| V7_14 | restated | equivalent | equivalent | B is literally the project's EpGroupoid.lemma_7_1_11 at universe 0 (same open U ∋ x₀, same properness of (s⁻¹(cl U)).domRestrict t, same set {ψ / s ψ = x ∧ t ψ ∈ U}); A_to_B is hA.1 with binders reordered. B_to_A: lemma_7_1_11 is B, and lemma_7_1_11_swap (s and t exchanged, the form of the text's proof) foll |
| V7_15 | same | equivalent | equivalent | The project's proposition_7_1_12 (instance Finite (X.Isotropy x)) and B ({g / s g = x ∧ t g = x}.Finite) say the same thing: X.Isotropy x is the structure of morphisms with the two equations, and val is a bijection onto B's set (Isotropy.ext for injectivity). A_to_B uses A's instance; B_to_A derives pr |
| V7_16 | stronger | equivalent | equivalent | B's two claims ((1) isomorphic objects have isomorphic isotropy groups; (2) for φ : x → y, g ↦ φ ∘ (g ∘ φ⁻¹) is a multiplicative bijection Gset x → Gset y) follow from A: by A's isotropyConj_val the project's MulEquiv isotropyConj φ : G_x ≃* G_y has underlying morphism (φ ∘ g) ∘ φ⁻¹, equal to B's co |
| V7_17 | stronger | equivalent | equivalent | A's theorem_7_1_13 (∃ R : X.NaturalRep x, R.U ⊆ V) gives every clause of B's IsNatRepData directly from the NaturalRep fields (Φ(g⁻¹) as the inverse witness, Φ_mul for the homomorphism, Γ sc-smooth on U, (1)–(3)), with B's Gx (a subtype) and the project's Isotropy (a structure) identified and the produ |
| V7_19 | same | equivalent | equivalent | A's ten NaturalRep facts say that for EVERY natural representation R (U connected) the sheets 𝐔(g) = Γ(g, U) are open, connected, pairwise disjoint, cover 𝐔(x) = morOn U, are its connected components, and s, t : 𝐔(g) → U are sc-diffeomorphisms; A's lemma_7_6_2 gives the 'properness' shrinking. B is an |
| V7_20 | restated | A ⇒ B only | equivalent | B asks for the existence of SOME M-polyfold structure on Gx × U (any open U ∋ x) whose sheets {g} × U are sc-diffeomorphic to U ⊆ X by the projection. A consists of properties of the project's specific construction (discreteChart charts pairwise compatible; maps into discretePolyfold are sc-smooth i |
| V7_21 | stronger | B ⇒ A only | A_narrower | A = translation_isLocalScDiffeo_src/_tgt, translation_isScSmoothCompSheet, translation_isProperMap (every V) at universe 0, all for R : X.NaturalRep x (U connected); B asks, for every natural action with U merely open, for an EpGroupoid on (U, G_x × U) with the text's s, t, ∘ and the charts of restr |
| V7_22 | stronger | B false | A_narrower | A (Γ_mul, Γ_one, Γ_inv, full, faithful at universe 0) is stated for R : X.NaturalRep x, whose U is required connected; B is stated for every natural action IsNatAction (Theorem 7.1's data and (1)-(3), U open but not required connected). On a disconnected U, (1)-(3) do not force Γ to be a functor, an |
| V7_23 | same | B ⇒ A only | A_narrower | A = the ten listed theorems at universe 0, about the project's Φhat (defined as the conjugation Γ(g, tφ) ∘ φ ∘ Γ(g, sφ)⁻¹) for R : NaturalRep (U connected). B uses the text's formula Φ̂(g)(φ) = Γ(ghg⁻¹, g∗sφ) for φ ∈ 𝐔(h) (index chosen) and asserts (i)–(v) for every natural action with U merely open |
| V7_25 | restated | equivalent | equivalent | A = exists_star ∧ proposition_7_1_15_2017 ∧ proposition_7_1_15_of_mem_nhdsSet at universe 0. The main content, Nonempty (X.NaturalRepFinite Y V) for mutually isomorphic finite Y and V ∈ 𝓝ˢ Y, is equivalent to B's ∃ U F, IsNatRepFinB X Y V U F: isNatRepFinB_of / exists_natRepFinite (the V7_26 comparison: the pr |
| V7_26 | same | neither | equivalent | The item lists only definitions (the structure EpGroupoid.NaturalRepFinite = Definition 7.8, and the def NatRepFinite.mono), so A = True and the comparison is B itself, proved outright as B_holds: B's IsNatRepFinB (the properties of Proposition 7.5, with 𝐔(ψ) read as connectedComponentIn 𝐔 ψ and the |
| V7_27 | stronger | B false | A_narrower | A = the three listed theorems at universe 0 (π_eq_π_iff_exists_smul, isOpenEmbedding_orbitQuotientMap, range_orbitQuotientMap); proposition_7_1_19, proposition_7_1_19_fullyFaithful, proposition_7_1_19_orbitMap, translationOrbitHomeomorph and orbitQuotientMap are data definitions (proposition_7_1_19 is assembled |
| V7_28 | restated | B false | incomparable | B is false (not_B, two independent counterexamples, both on readings B's author flagged as doubts). B's conjunct (D) claims the text's notion IsLocalUniformizerB is equivalent to the data of a project LocalUniformizer; text ⇒ project fails because the project's LocalUniformizer (i) contains a Natura |
| V7_29 | same | B ⇒ A only | equivalent | B is the definitional statement 'X.IsEpSubgroupoid A ↔ A is a sub-M-polyfold of X.PObj and π⁻¹(π(A)) = A'; the project's structure IsEpSubgroupoid has exactly these two fields and GroupoidStr.IsSaturated is literally π⁻¹(π(A)) = A, so B holds outright (B_holds) and A → B does not use A. A's four the |
| V7_30 | narrower | neither | incomparable | A is facts (1), (2) for the project's specific structure subObjPolyfold hA; B asserts ONE structure Q on A with facts (1)–(4), including the tangent-space facts (3) T_aA has an sc-complement in T_aX and (4) T_aA = Tr(a)T_aX. With Q = subObjPolyfold hA, A gives (1), (2) and the sc-smoothness half of  |
| V7_31 | restated | B ⇒ A only | incomparable | B = (a) at every φ ∈ 𝐀 a sheet s : 𝐔(φ) → U(a) and a retraction r of U(a) onto U(a) ∩ A exist, (b) for EVERY such choice σ∘r∘s retracts 𝐔 onto 𝐔 ∩ 𝐀, (c) 𝐀 is a sub-M-polyfold, (d) some structure on 𝐀 with facts (1)–(4). All but the tangent facts (3), (4) of (d) are proved from A (A_to_B_noTangent:  |
| V7_32 | stronger | equivalent | equivalent | A → B: B's Y is assembled from A's six conditions of Definition 7.3 for fullSub A with subObjPolyfold/subMorPolyfold (not from the definition subEpGroupoid); facts (1), (2) for these structures are Part I's, the structure-map equations are rfl and fullSub_comp_val. B → A: the six conditions for the  |
| V7_33 | same | equivalent | equivalent | B = the project's IsEffective, IsRegular, regularSet agree with B's (which state g ≠ 1_x, G_x = {1_x} on the underlying morphisms) plus 'if s(φ) is regular so is t(φ)'. The definitional parts hold outright (Isotropy.ext and (1 : G_x).val = u(x) by rfl); B's last conjunct is A's isRegular_tgt_of_isRe |
| V7_34 | stronger | equivalent | equivalent | A is lemma_7_2_2 (IsOpen X.regularSet) and NaturalRep.subset_regularSet (for every natural representation R at a regular x, R.U ⊆ X_reg), universes at 0. B's X_reg = {x / ∀ g : G_x, g.val = 1_x} is the project's regularSet = {x / ∀ g, g = 1} by Isotropy.ext, so lemma_7_2_2 and B are the same statement.  |
| V7_35 | stronger | equivalent | equivalent | B is lemma_7_2_3 after a dictionary: IsEffectiveB (g.val ≠ 1_x) = IsEffective (g ≠ 1); B's NatRepB has the same fields as NaturalRep (both with U connected) except that Φ(g) need only have some sc-smooth inverse, and Φ(g⁻¹) is recovered from Φ(1) = id on U; B's injectivity (Φg = Φh on U ⇒ g = h) is eq |
| V7_36 | stronger | equivalent | equivalent | proposition_7_2_4 is B after the dictionary IsEffectiveB = IsEffective and XregB = regularSet (Isotropy.ext). A also contains the converse isEffective_of_dense_regularSet and the equivalence isEffective_iff_dense_regularSet, which are not in the text and do not follow from B; they are re-proved outrig |
| V7_37 | stronger | equivalent | equivalent | With the dictionary NatRepB/NaturalRep (so ActsTriviallyB = ActsTrivially and TxB = trivialSet, needing no hypothesis), B's (a) arbitrarily small natural representations, (c) 1 ∈ T_x, (d) arbitrarily small U with ker Φ = T_x and (e) T_x normal follow from A's exists_naturalRep_trivialSet_iff, one_me |
| V7_38 | restated | A ⇒ B only | equivalent | B says the project's definitions are the text's: nonEffectivePart = 𝐗^T, ReducedRel = ∼ (both hold by the dictionary TxB = trivialSet alone, the formulas being identical), ∼ is an equivalence relation, and reducedπ is onto and identifies exactly the ∼-equivalent morphisms. In A → B the equivalence-r |
| V7_39 | narrower | B ⇒ A only | A_narrower | B's last conjunct asserts for EVERY ep-groupoid that 𝐗^R (quotient topology) is Hausdorff and paracompact and carries an M-polyfold structure Q making each Ψ = π/W an sc-diffeomorphism. A has Hausdorff/paracompact only for effective X (t2Space_/paracompactSpace_reducedMor_of_isEffective) or from reg |
| V7_40 | narrower | B false | A_narrower | A (universes at 0) gives the six conditions of Definition 7.3 for (X, 𝐗^R), effectivity of reducedEpGroupoid and proposition_7_10_2017, all (except exists_isProperMap_reduced) under the hypotheses [T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor] (satisfiable, e.g. for effective X). B asserts for ev |
| V7_41 | same | equivalent | equivalent | A (universes at 0) = surjective_reducedIsotropyHom ∧ ker_reducedIsotropyHom ∧ normalClosure_trivialSet: g ↦ [g], G_x → G̃_x (isotropy of x in reducedGroupoidStr) is onto with kernel T_x, and normalClosure(T_x) = T_x (the other five listed declarations are definitions). B: T_x normal, g ↦ [g] onto wi |
| V7_42 | restated | equivalent | equivalent | A (universes at 0) = theorem_7_3_1 (/X/ locally metrizable, RegularSpace, T2Space) ∧ theorem_7_3_1_metrizable (ParacompactSpace /X/ → MetrizableSpace /X/) ∧ metrizableSpace_of_locally (Part I: every paracompact Hausdorff locally metrizable space is metrizable). B: locally metrizable, the text's regulari |
| V7_43 | restated | equivalent | equivalent | A (universes at 0) = metrizableSpace_orbitRel_quotient_naturalRep (G_x\U(x) metrizable for every natural representation R) ∧ lemma_7_3_2_naturalRep (π(R.U) metrizable) ∧ lemma_7_3_2 (every z ∈ /X/ has an open metrizable neighbourhood). B: the local metrizability, and for every natural representation R a |
| V7_44 | same | equivalent | equivalent | A is lemma_7_3_3 at universe 0: for every ep-groupoid X (Obj Mor : Type) and z ∈ /X/ there is V : ℕ → Set /X/ with every V k open and containing z and (𝓝 z).HasAntitoneBasis V. B: open V k, z ∈ V (k+1) ⊆ V k, and (𝓝 z).HasBasis (fun _ ↦ True) V (index shift ℕ from 0 instead of 1). Mathlib's HasAntiton |
| V7_45 | restated | equivalent | equivalent | A (universes at 0) is t1Space_orbitSpace ∧ lemma_7_3_4: /X/ = X.OrbitSpace (quotient topology) is T1 and T2 for every ep-groupoid X : EpGroupoid Obj Mor, Obj Mor : Type. B is T2Space X.OrbitSpace in the same setting. A ⇒ B is the second conjunct; B ⇒ A adds T1 from T2 (Mathlib instance). The extra T1  |
| V7_46 | restated | equivalent | equivalent | A is EpGroupoid.lemma_7_3_5 at universe 0 (Mathlib RegularSpace on the quotient topology of X.OrbitSpace, for every ep-groupoid with Obj Mor : Type); B is the text's definition of regularity stated literally (nonempty closed set and an outside point have disjoint open neighbourhoods). The two notions  |
| V7_47 | same | equivalent | equivalent | A is EpGroupoid.corollary_7_3_6 at universe 0: for every ep-groupoid with [SecondCountableTopology X.OrbitSpace], MetrizableSpace X.OrbitSpace. B is the same statement with second countability as an explicit hypothesis; same Mathlib notions on the same quotient topology. The two are the same propositi |
| V7_48 | same | equivalent | equivalent | A = exists_metrizable_nhds_subtype (every subset S of /X/ is locally metrizable) ∧ metrizableSpace_of_paracompactSpace_subtype (paracompact subsets are metrizable), universes 0. B = every subset is locally metrizable, regular (text's definition) and Hausdorff. A ⇒ B: local metrizability is A's first |
| V7_49 | same | neither | equivalent | Definition item: only EpGroupoid.IsComponentCompact is listed, so A = True and both implications are vacuous. The content is B itself, proved outright as B_holds: the project's IsComponentCompact K (∀ z, IsCompact (K ∩ connectedComponent z)) is B's text notion (∀ C of the form connectedComponent z,  |
| V7_50 | stronger | A ⇒ B only | A_stronger | A ⇒ B: B's Lemma 2.7 is lemma_2_7_3 and B's Proposition 2.17 is proposition_2_7_4 (universes 0; B's extra [T2Space] is simply unused). B ⇒ A fails for a genuine reason: A is strictly more general. All ten listed theorems drop the text's Hausdorff assumption (RegularSpace only), and paracompactSpace_of |
| V7_51 | restated | equivalent | equivalent | A = locallyPathConnectedSpace_orbitSpace ∧ exists_isOpen_metrizableSpace_closure ∧ corollary_7_3_8_of_isCompact ∧ corollary_7_3_8 (universes 0); B = the text's Corollary 7.2 (open U ⊇ K, cl U paracompact and metrizable, U metrizable) with B's IsComponentCompactB, which is the project's IsComponentCompac |
| V7_52 | restated | equivalent | equivalent | A (13 theorems, universes 0) says the project's liftOne is an ep-groupoid on (X_1, X_1-morphisms) with PObj = X.PObj.shift, PMor = X.PMor.shift, the level-1 restrictions of s,t,u,i,m, tame if X is; B says some ep-groupoid Y with atlases equivalent to those of X^1, 𝐗^1 and the same restricted structu |
| V7_53 | restated | equivalent | equivalent | Definition 7.15: HasParacompactOrbitSpace is Mathlib's ParacompactSpace X.OrbitSpace, whose single field is literally B's IsParacompactB (index types in Type, no Hausdorff condition), so B's first conjunct holds outright. The sentence before Remark 7.1 is remark_7_5_2 in A and B's second conjunct, bot |
| V7_54 | stronger | A ⇒ B only | A_stronger | A ⇒ B: Y = X.liftOne satisfies IsLiftB by rfl/liftOne_comp_val and proposition_7_5_3 gives paracompactness. B gives back the headline conjuncts: proposition_7_5_3 for liftOne (B's Y has the same s,t, hence the same orbit setoid and orbit space; B_gives_proposition_7_12) and metrizableSpace_liftOne_orb |
| V7_55 | same | equivalent | equivalent | theorem_7_5_4 and B agree: (1) is identical (Mathlib PartitionOfUnity on /X/, IsSubordinate, index type in Type); in (2) A's saturated open neighbourhood W ⊆ X meeting finitely many tsupports corresponds to B's open V ⊆ /X/ with π⁻¹(V) meeting finitely many (V = π(W), open since π is open, Proposition |
| V7_56 | restated | neither | equivalent | Definition item (HasScPartitionsOfUnity, IsScSmoothPartitionOfUnity), so A = True and both directions are vacuous; the content is B itself, proved outright as B_holds: the project's HasScPartitionsOfUnity is B's HasScPUB field by field (same Mathlib PartitionOfUnity indexed by a type in Obj's univer |
| V7_58 | same | equivalent | equivalent | theorem_7_5_7 (universe 0) and B have the same hypotheses (HasParacompactOrbitSpace, PObj.AdmitsScPartitionsOfUnity) and conclusions that agree by the V7_56 rephrasing (HasScPartitionsOfUnity ⇔ B's HasScPUB: invariance β(s φ) = β(t φ) vs. IsoB y z → β z = β y, everything else literally equal). Both di |
| V7_59 | same | equivalent | equivalent | A (universes 0) is the conjunction of exists_hasPropernessProperty, HasPropernessProperty.mono, isProperSubset_iff_isCompact and isProperSubset_iff_exists_tendsto_subseq; B says the project's IsProperSubset (Mathlib IsProperMap of t on s^{-1}(Q)) and HasPropernessProperty (for open U) agree with the |
| V7_60 | same | equivalent | equivalent | A (universes 0) is the conjunction of proposition_7_5_9 and its alias IsProperSubset.isClosed, both 'X.IsProperSubset Q -> IsClosed Q' in the object space; B is the same statement with all binders explicit. Both directions are one-line re-applications of the hypothesis; same definitions on both sides |
| V7_61 | stronger | equivalent | equivalent | A (universes 0; the index type of isProperSubset_iUnion_of_locallyFinite also at Type) is the conjunction of 8 theorems; its proposition_7_5_10_one and proposition_7_5_10_two ([ParacompactSpace X.OrbitSpace] as instance) are exactly B's (1) and (2), with the same orbit space, quotient topology, pi and I |
| V7_62 | restated | equivalent | equivalent | A (universes 0) is theorem_7_6_1 (exists NaturalRep R with R.U in V), exists_sheets and exists_naturalRep_sheets (Sheets D and R with R.U in V, R.U in s(N_g), R.Phi = t_g o s_g^{-1}, R.Gamma = s_g^{-1} as functions). B asks for an open U in V with the natural action (U NOT required connected, unlike t |
| V7_63 | stronger | equivalent | equivalent | A (lemma_7_6_2, universe 0) holds for ANY open N_g containing g and any neighbourhood U0 of x; B holds only for the proof's choices (U0 open, N^s_g, N^t_g open with s, resp. t, an sc-diffeomorphism onto U0, the N^s_g u N^t_g pairwise disjoint, N_g = N^s_g n N^t_g). So A is formally more general; A->B  |
| V7_64 | stronger | A ⇒ B only | A_stronger | A_to_B uses only the lemma_7_6_3 conjunct: B's choices (s, t sc-diffeomorphisms of N^s_g, N^t_g onto a common U0, N^s_g u N^t_g disjoint) give project Sheets on N_g = N^s_g n N^t_g by restriction; B's U1 lies in U0 but need not lie in the smaller s(N_g), so Lemma 7.9 is applied to U1 n (intersection o |
| V7_65 | same | equivalent | equivalent | A is EpGroupoid.theorem_7_6_4 at universe 0: HasParacompactOrbitSpace (by definition ParacompactSpace X.OrbitSpace) and X.PObj.AdmitsScPartitionsOfUnity imply HasScPartitionsOfUnity (Definition 7.16 with a Mathlib PartitionOfUnity indexed by a Type). B has the same hypotheses and the same conclusion w |
| V7_66 | stronger | neither | incomparable | A (lemma_7_6_5) takes the natural action as a project NaturalRep, whose domain V(x) = R.U must be CONNECTED; B takes Theorem 7.1's clauses as data on any open V(x) (IsNatActionB, no connectedness). For connected V(x) B's data is a NaturalRep (Phi(1) = id and Phi(g)^-1 = Phi(g^-1) follow from Phi_mul) |
| V7_67 | restated | neither | incomparable | A is 7 lemmas of the project's proof (neighbourhoods (1)-(4), orbitExtension sc-smoothness, the invariant sc-smooth Urysohn lemma, Part I's admitsScPartitionsOfUnity_of_approx, theorem_7_5_7); B is the text's chain of claims, quantified over EVERY choice of V(x), W(x) with B's natural action (IsNatAct |
| V7_68 | narrower | B ⇒ A only | A_narrower | A (corollary_7_6_6, MPolyfold.admitsScPartitionsOfUnity_of_hilbert, corollary_7_6_6_hypotheses_rn) requires for each chart's E0, besides a Hilbert norm (norm^2 = b(v,v), b continuous bilinear), the explicit hypothesis GodefroyTroyanskiWhitfieldZizlerStatement E0 (WCG + C^inf bump implies C^inf partition |
| V8_1 | restated | equivalent | equivalent | A is the conjunction of the eight listed theorems (fibre injectivity tangent_ext, fibre surjectivity exists_tSrc_eq, src_tBase_eq, the (8.5) characterization tComp_spec/tBase_tComp/tSrc_tComp, uniqueness tComp_eq, and (8.8) tUnit_eq), universes at 0. These are exactly B's embedded claims: B's fibrew |
| V8_3 | restated | equivalent | equivalent | A = theorem_8_1_1 ∧ theorem_8_1_1_tame (universes at 0). Apart from its (8.5) clause, theorem_8_1's type is a list of rfl identifications of the project's tangentEpGroupoid (M-polyfolds TX, T𝐗; src, tgt, unit, inv = Ts, Tt, Tu, Tι; comp = tComp) and of tangentProjFunctor (obj, mor = the projections). Th |
| V8_4 | restated | equivalent | equivalent | A states Lemma 8.1 in the sheet form of the text's proof: for a sheet s : W → V with inverse σ and g(φ') = m(σ(t φ'), φ'), sc-smooth on t⁻¹(V) by condition (4) in sheet form (isScSmoothCompSheet), k ∘ h = Tg(h) when k lies over W. It adds the auxiliary sheet facts Tσ(Ts k) = k and h ∈ T(t⁻¹V). The p |
| V8_5 | same | equivalent | equivalent | B is the lemma for composable pairs: Ts(Ψ ∘ Φ) = Ts Φ and Tt(Ψ ∘ Φ) = Tt Ψ, with B's tCompB (the vector over p Ψ ∘ p Φ with the same Ts as Φ, by choice). tCompB is the project's tComp by rfl (same Classical choice; B's tangentMap hs is tSrc by proof irrelevance), so A's lemma_8_1_3 is B verbatim with  |
| V8_6 | same | equivalent | equivalent | A is lemma_8_1_4: (l ∘ k) ∘ h = l ∘ (k ∘ h) for Ts l = Tt k, Ts k = Tt h, with the project's tComp. B's tCompB is tComp by rfl (same Classical choice; B's tangentMap hs is tSrc by proof irrelevance). B asserts the equality of the bracketings plus the text's description of the common value: it lies ove |
| V8_7 | same | equivalent | equivalent | A is about the project's unit tUnit = Tu (the tangent of the unit map): Ts(Tu q) = q, Tt(Tu q) = q, k ∘ Tu(Ts k) = k, Tu(Tt h) ∘ h = h, and lemma_8_1_5 (Tu q lies over 1_x, has source and target q, is a two-sided identity). B is about the text's 1_q, characterized as a vector over 1_x with Ts = q: suc |
| V8_8 | same | equivalent | equivalent | Same notions on both sides. By proof irrelevance B's tangentMap hs / ht / hι are the project's tSrc / tTgt / tInv, baseB is tBase and B's tCompB is tComp (the same choice term). A ⇒ B is lemma_8_1_6 read clause by clause. B characterizes the unit 1_q by IsTUnitB (over 1_{p q}, Ts = q) plus uniqueness; |
| V8_9 | restated | equivalent | equivalent | On T(X, 𝐗) both sides claim the same things: s_T, t_T are surjective local sc-diffeomorphisms; u_T and ι_T = Tι are sc-smooth; m_T is sc-smooth on T𝐗 _{s_T}×_{t_T} T𝐗 as a sub-M-polyfold of T𝐗 × T𝐗. B's tangentMap hs/ht/hι and tCompB are tSrc/tTgt/tInv/tComp by proof irrelevance. B's IsScSmoothMulOn |
| V8_10 | same | equivalent | equivalent | Both sides say the same thing. Every a ∈ TX has an open V ∋ a such that t_T restricted to s_T⁻¹(cl V) is proper. B's tangentMap hs / ht are tSrc / tTgt by proof irrelevance. The only difference is the reading of 'proper'. A uses Mathlib's IsProperMap (ultrafilter / universally closed). B's IsProperB |
| V8_11 | same | A ⇒ B only | A_stronger | B is the lemma's claim: for every ep-groupoid X in Type, X tame ⇒ TX tame, with tameness of an ep-groupoid being tameness of its object M-polyfold (Definition 7.6). A ⇒ B is A's MPolyfold.IsTame.tangent; lemma_8_1_9 gives the same, since the object M-polyfold of tangentEpGroupoid is tangentPolyfold. B |
| V8_12 | narrower | B false | incomparable | B formalizes the remark literally, and its author predicted that it fails. The bijection G : T𝐗 → {(Tφ, a)} is taken with Tφ the bare map (B's TφB: Tφ on T_{sφ}X, the identity elsewhere). not_B shows B fails as we read it. On Chapter 7's ℤ/3 × ℝ ⇉ ℝ (trivial action, s = t), B's own clause (vi), Tφ(T |
| V8_13 | same | equivalent | equivalent | Both sides say that TΦ = tangentMap Φ.isScSmoothMap_obj and T𝚽 = tangentMap Φ.isScSmoothMap_mor are sc-smooth between the tangent M-polyfolds and that T𝚽 is compatible with s_T, t_T, the composition (8.5) and the units. A adds Φ.tangent.obj = TΦ and Φ.tangent.mor = T𝚽, which hold by rfl. B's tangent |
| V8_14 | restated | neither | equivalent | Both sides make the same claims: X ↦ TX, Φ ↦ TΦ is a functor on ep-groupoids, TΦ preserves the structure maps, and T preserves tameness. They differ only in universe level. The project's tangentFunctor : EP.{max u 1} ⥤ EP.{max u 1} at u = 0 is an endofunctor of EP.{1}, the ep-groupoids on spaces in  |
| V8_15 | same | neither | equivalent | Definition item: only EpNatTrans (a structure) and EpFunctor.NaturallyEquivalent (Nonempty (EpNatTrans F G)) are listed, so A = True and both implications are vacuous; the content is B itself, proved outright as B_holds. The fields of EpNatTrans (app sc-smooth X → 𝐘, s(app x) = F x, t(app x) = G x,  |
| V8_16 | same | equivalent | equivalent | A (universes at 0) is the conjunction of isScSmoothMap_comp_app, NaturallyEquivalent.refl/.symm/.trans, naturallyEquivalent_equivalence and the whiskering results comp_left/comp_right; B says B's own reading NatEquivB of F ≃ G (re-stated from Definition 8.1.13, not the project's) is an Equivalence o |
| V8_17 | same | equivalent | equivalent | A (proposition_8_1_14, universes at 0): every project τ : Φ → Ψ has Tτ : EpNatTrans Φ.tangent Ψ.tangent with Tτ.app = tangentMap τ, and Φ ≃ Ψ → TΦ ≃ TΨ. B: for τ satisfying B's reading of Definition 8.1.13 there are EpFunctors TΦ, TΨ : T(X,𝐗) → T(Y,𝐘) whose object/morphism maps are the tangent maps of  |
| V8_18 | stronger | A ⇒ B only | A_stronger | B (/X/ paracompact ⇒ /TX/ paracompact, quotient topology written as coinduced π) is exactly A's theorem_8_1_15 (OrbitParacompactB ↔ HasParacompactOrbitSpace is Iff.rfl), so A ⇒ B is immediate. A (13 theorems, universes at 0; metrizableSpace_of_pullback at 0,0) also contains the project's whole proof of |
| V8_20 | restated | B ⇒ A only | equivalent | Definition item: A (universes at 0) is only P_μ (P ∘ μ = t ∘ π₁) and continuous_μ; the content is B, proved outright (B_holds): the project's EpStrongBundle fields are exactly B's IsEpStrongBundleB. isStrongBundleMap, surjective and isLocalScDiffeo are B's clauses verbatim (B's paracompactness insta |
| V8_21 | stronger | equivalent | equivalent | A (universes at 0): fiberMor_apply (rfl), μ_add, μ_smul (μ(ψ,·) additive and homogeneous W_{sψ} → W_{tψ}) and μ_inv_μ, μ_μ_inv (μ(ψ⁻¹,·) is a two-sided inverse). B: a family L ψ : W_{sψ} ≃ₗ W_{tψ} of linear isomorphisms with L ψ = μ(ψ,·), L(1_x) = id and L(ψ∘γ) = L ψ ∘ L γ on points. A ⇒ B builds L  |
| V8_22 | restated | equivalent | equivalent | A (universe 0) has nine theorems about the project's (W, 𝐖); B states, for the project's E.toEpGroupoid, the text's structure maps, the covering/local-diffeo/fibre-linearity of s_𝐖, t_𝐖, an EpFunctor (P, π₁), orbit covering and a surjective continuous /P/. A ⇒ B: structure maps are rfl except the co |
| V8_23 | same | B ⇒ A only | equivalent | The item is Definition 8.3.2 (EpStrongBundle.IsMap, vocabulary) plus the non-vacuity theorem isMap_id, so A = type of isMap_id at universes 0. B asks that IsMap equal B's literal reading IsMapB (an IsStrongBundleMap covering φ.obj, plus Φ(μ(γ,w)) = μ'(φ(γ),Φ(w)) with the fibred-product membership pa |
| V8_24 | restated | B ⇒ A only | equivalent | The item is Definition 8.3.3 (IsStrongBundleFunctor, vocabulary) plus three theorems, so A (universe 0) = projFunctor_comp ∧ mor_val ∧ isStrongBundleFunctor_id. B says (a) for an EpFunctor Φ, IsStrongBundleFunctor iff B's IsSBFunctorB: strong bundle maps on objects and on morphisms, with both coveri |
| V8_25 | same | equivalent | equivalent | A (universe 0) has six conjuncts: the four theorems relating Definitions 8.3.2 and 8.3.3 (isMap, isStrongBundleFunctor_liftFunctor, eq_liftFunctor, isMap_iff_strongBundleFunctor), and two general pull-back lemmas (isScSmoothMap_to_pullback_one, the universal property at level [1], and isLinearMap_fi |
| V8_26 | restated | equivalent | equivalent | A (universes 0) has eleven conjuncts. Eight are about Γ, Γ⁺ and Fred: fiberZero ∈ Γ, Γ closed under sectionAdd and constant sectionSmul, Γ⁺ ⊆ Γ, the same three for Γ⁺, and Fred ⊆ Γ. The other three are Part I's lemmas over an arbitrary M-polyfold: sums, constant multiples and the zero section are sc |
| V8_27 | restated | equivalent | equivalent | The item is Definition 8.5.1 (IsProperCovering and fibredMap, vocabulary) plus two theorems, so A (universes 0) = isSubMPolyfold_fibredProduct (Part I's Proposition 2.46, listed because condition (3) uses it) ∧ isProperCovering_id. B says IsProperCovering F ↔ IsProperCoveringB F, B's literal reading |
| V8_28 | narrower | B ⇒ A only | A_narrower | A (universes 0) gives these results for a proper covering F. (1) d_𝐘(φ) = d_{𝐗ₛ×_F Y}(Lφ) and d_𝐗(Fφ) = d_𝐘(φ). (2) In general only d_{𝐗×Y}(Fφ, sφ) ≤ 2d_𝐘(φ). (3) The equalities d_{𝐗×Y}(Fφ, sφ) = 2d_𝐘(φ) and 2d_{𝐗ₛ×_F Y} = d_{𝐗×Y} only for tame X and Y. A also has Part I's d_{X×Y} ≤ d_X + d_Y, the t |
| V8_29 | same | equivalent | equivalent | B is literally the project's proposition_8_5_2 at universe 0 (the same EpFunctor.IsProperCovering, the same EpFunctor.comp, arguments in another order), so A ⇒ B is the third conjunct of A. Conversely B gives (F ∘ H).IsProperCovering, and the other two conjuncts of A, evenlyCovered_comp and isScDiffeo |
| V8_30 | stronger | B false | incomparable | B formalizes (5) as printed: right arrow t, so the square says t ∘ F = F ∘ s on 𝐔(ψ₀). As its author predicted, B does not hold as we read it. not_B applies B to the identity functor of ℤ/2 ⋉ ℝ at x = 0 (EpFunctor.isProperCovering_id), with a natural representation inside B's V (Chapter 7's theorem_ |
| V8_31 | restated | equivalent | equivalent | Both sides say the same things, (a) F(φ) ∈ G_x and (b) uniqueness of (Φ, Γ), U(y), 𝐔(ψ₀) given U(x), and both are true. They are scoped differently, so each direction is only partly a real derivation. A's (b) theorems (remark_8_5_4_b, connectedComponentIn_U/_sheet) are about full charts F.ProperCoveri |
| V8_32 | restated | neither | equivalent | This is a definition item and the definitions agree: B (the project's Diff_sc, covering functors and geometric lifts are the text's) is proved outright (B_holds). (i) A morphism of MPolyfoldCat is a ScDiffeo, whose IsScDiffeoOn … univ univ unfolds to B's 'sc-smooth map with an sc-smooth two-sided in |
| V8_33 | same | A ⇒ B only | equivalent | Same objects on both sides: B's τ(y) = (L.τ.app y).toFun and φ_{yy'}(ψ) = (L.LD.map ψ).toFun are definitionally the project's τy, φ, and B's actions g ∗ z = L_C(g)(z), h ∗ z = L_D(h)(z) are the project's scoped MulAction instances (smul_def, smul_def' are rfl). A ⇒ B is glue: isScDiffeoOn_τy, isScDi |
| V8_35 | narrower | B false | incomparable | B asserts the construction for every covering functor f : D → C, including D = ∅, which the text's Definition 8.5.5 allows. As its author predicted, B does not hold as we read it. not_B uses D = Discrete PEmpty, G = Unit, L_C(⋆) = ℝ and L_D empty; f is a covering functor (a bijection of empty sets), |
| V8_36 | narrower | equivalent | A_stronger | A_to_B: (a) is covering_restrict. For (b), V is the W of the non-item theorem_8_5_3_of_naturalRep; B's connected natural action (U, Φr, Γr) is a project NaturalRep, hence C.R for a chart C, and the witnesses are C.geometricLift and C.Ψ hF (properties from hA). Lg, A and Φ are actionEpGroupoid, geometr |
| V8_37 | restated | A ⇒ B only | equivalent | The definitions agree: B, which says the blind transcription IsPSBCoveringB A holds iff A is the object map of a functor with the project's IsProperStrongBundleCovering, is proved. The differences are only presentational. (a) B reads 'strong bundle map A with Q∘A = F∘P' as the project's IsMap (Def.  |
| V8_38 | restated | equivalent | equivalent | A (universes at 0) has seven theorems. A_to_B builds B's bijection mor(F⁻¹(x)) → G_x × F⁻¹(x): bijective_fibredMap gives injectivity, existsUnique_lift gives surjectivity. Finiteness and the count come from finite_morOn_fiber and ncard_morOn_fiber, with Nat.card G_x = #{g / s g = x = t g}. A Fin q-i |
| V8_39 | same | equivalent | equivalent | A (universes at 0) is morOn_fiberClass_eq ∧ lemma_8_6_1. The project indexes the classes by c ∈ /Y/ (fiberClass x c = F⁻¹(x) ∩ π⁻¹(c), possibly empty). B indexes them by a point y₀ ∈ F⁻¹(x): classB … y₀ = fiberClass x (π y₀), and every nonempty fiberClass x c is the class of each of its points. A_to_B |
| V8_40 | restated | A ⇒ B only | A_stronger | A (universes at 0) has exists_isomorphic_of_isomorphic (every y ∈ F⁻¹(x) has an isomorphic y' ∈ F⁻¹(x')), fiberIndex_eq (π(F⁻¹(x)) = π(F⁻¹(x'))), lemma_8_6_2 and lemma_8_6_2_equiv. A_to_B: B's 'before the lemma' claim is transitivity of ≅. For an arbitrary enumeration Θ of the classes of F⁻¹(x), it se |
| V8_41 | same | equivalent | equivalent | A (universes at 0) is ncard_fiber_eq_sum (#F⁻¹(x) = ∑_{c ∈ π(F⁻¹(x))} #Θ_c), lemma_8_6_3 (#Θ_c = #Θ'_c for all c ∈ /Y/, and #F⁻¹(x) = #F⁻¹(x')) and ncard_fiber_eq_of_isomorphic. B takes arbitrary Fin q-indexed decompositions Θ, Θ' matched as in Lemma 8.6.2. The bridges: each class is fiberClass x (π  |
| V8_42 | restated | equivalent | equivalent | A (universes at 0) has five theorems: one_le_ncard_fiber, eventually_ncard_fiber_eq, isLocallyConstant_ncard_fiber, isLocallyConstant_fiberCardOrbit and proposition_8_6_4. A_to_B: constancy on the components of /X/ is proposition_8_6_4, and the bound ≥ 1 is one_le_ncard_fiber. B's sc-smooth functor X →  |
| V8_43 | restated | equivalent | equivalent | A's mor_val is B's (1) (A(φ, w) = (F φ, A w)) and A's μ_comm, applied to the strong bundle functor part of the covering, is B's (3) (μ_X(F φ, A w) = A(μ_Y(φ, w))); section_8_5_2 is (3) at w = v, written through fiberMor/fiberEquiv. B's remaining conjuncts are not in A's theorems but hold outright: ( |
| V8_44 | narrower | B ⇒ A only | A_narrower | A's proposition_8_1_16 concludes TX.IsZhou from X.IsZhou only under the extra hypothesis X.TangentZhouReflect: for a smooth b ∈ TX and (g, h) ∈ G_b, T(g, h) = id on T_b(TX) implies Tg = id on T_{p(b)}X. This is the step of the text's proof that differentiates (8.16) and uses that Tτ_X is onto;  |
| V8_45 | narrower | B ⇒ A only | A_narrower | A's nonEffectivePart_tangent_eq, proposition_8_1_17_one and proposition_8_1_17_two carry two hypotheses the text does not state and B's premises do not give: X.HasConnectedDenseLevelOneReps (natural representations with U(x) ∩ X₁ preconnected in X¹ and dense in U(x), an assumption of the t |
| V8_46 | restated | neither | equivalent | The item is a definition. B states that the project's EpStrongBundle.IsAuxNorm is the text's notion IsAuxNormB, and this is proved outright (B_holds): IsAuxNorm is Part I's StrongBundle.IsAuxNorm (continuity on W_{0,1} = B.One with the W[1] topology, a complete norm on every fibre, P(h_k) → x ∧ N(h_ |
| V8_47 | narrower | B ⇒ A only | A_narrower | B is the three-way equivalence /X/ ⇔ /W[0]/ ⇔ /W[1]/ paracompact; A proves only (2) ⇒ (1) (proposition_8_4_1_two_imp_one, via metrizability of /W/ and the zero-section embedding /X/ → /W/) together with the zero-section lemmas. A's instance hypothesis ParacompactSpace (𝐗 ₛ×_P W) is a theorem (S |
| V8_48 | restated | B ⇒ A only | A_narrower | A is only the witness isLR_trivial: every strong bundle over a trivial ep-groupoid has (LR). The project does not formalize Proposition 8.4.3, while B contains it as (ii): X effective with (LR) implies the bundle has (LR). B also contains (i), the claim that the project's EpStrongBundle.IsLR is the  |
| V8_49 | same | equivalent | equivalent | Same content, with one difference in generality. B states injectivity of f : G_d → G_{f d} for covering functors into an arbitrary groupoid C (its own IsCoveringB). A's injective_map_end covers only one-object C = SingleObj G, which is the text's setting: Definition 8.5.5 has C = {x}. For C = Single |
| V8_50 | restated | equivalent | equivalent | Both directions are proved. The project's IsProperStrongBundleCovering2021 (2021 Definition 8.5.9 for the object map A) and B's right-hand side state the same condition. B's right-hand side lists: a strong bundle map with Q ∘ A = F ∘ P, condition (0), and a functor Â with Â.obj = A and Â(ψ, w) = (F  |
| V8_51 | narrower | equivalent | equivalent | B's (a)–(c) match the project's lemma_8_5_10 together with bundleB_val. (a) says w ↦ (P w, A w) is a strong bundle isomorphism W → F*V over id_Y; (b) is (8.23); (c) is A = Ā ∘ B. B's (d) asks that F*V carry an EpStrongBundle structure over Y with structure map μ_{F*V}. A does not contain (d), a |
| V8_52 | explicit | B ⇒ A only | A_narrower | The project's proposition_8_1_17_two_all assumes two hypotheses that B lacks, for every i. hR: HasConnectedDenseLevelOneReps (Xⁱ), natural representations with U(x) ∩ X₁ connected and dense (the text's V(x)). hp: the tangent projection p : T𝐗ⁱ → (𝐗ⁱ)¹ is open (Part I gap G.8). B is the text's c |
| V9_1 | restated | B ⇒ A only | equivalent | The definitions agree, so B (project IsBranchedEpSubgroupoid ⇔ blind IsBranchedB) is proved outright (B_holds), in both directions, for every ep-groupoid and every Θ. Every field matches one to one: nonneg, functor, supp ⊆ X_∞, paracompact /supp/, a Fintype index in Type, x ∈ Mᵢ ⊆ U, σᵢ > 0 and the  |
| V9_2 | narrower | neither | incomparable | B = (a) local constancy of dim T_mM on every submanifold of every M-polyfold, (b) the project's IsNDimensional ⇔ the blind IsNDimB, (c) the footnote (nonempty support, n- and m-dimensional ⇒ m = n). A ⇒ B fails on (a) and (c), which A does not contain. A has local constancy only in ℝᵐ (hasLocallyCon |
| V9_4 | restated | equivalent | equivalent | Both formalize the example with the same hypotheses (HypB is Remark913Hyp field by field) and the same Θ (countB ![graphB β₁, graphB β₂] = thetaGraphs β₁ β₂). A ⇒ B: (a) comes from remark_9_1_3_b. B's structures at each x of the support (the graphs through x, cut to U) are the project's localBranchi |
| V9_5 | same | equivalent | equivalent | B is Lemma 9.1.5 for the blind IsBranchedB: IsLocallyClosed (π '' suppB Θ). A's lemma_9_1_5 is the same statement for the project's IsBranchedEpSubgroupoid, and π '' suppB = orbitSupp by definition. The two hypotheses are equivalent, as in V9_1: properness of Mᵢ → U(x) on either side is 'Mᵢ closed i |
| V9_6 | same | B ⇒ A only | equivalent | B says the project's IsClosedBranched Θ and IsCompactBranched Θ are IsClosed (π '' suppB Θ) and IsCompact (π '' suppB Θ). Both hold by Iff.rfl, since orbitSupp Θ is π '' supp Θ and supp is suppB, so the definitions agree exactly. A is only the witness isCompactBranched_indicator (the indicator of a  |
| V9_7 | stronger | equivalent | equivalent | B has three parts: (R) the restriction to an open V ∋ x₀ with x₀ arbitrary, (L) Lemma 9.1.7, (C) the J = I × G_x construction for any natural-representation datum (IsNatRepData) on an open U ⊆ U'. A has Lemma 9.1.7 with U(x) inside any given V (lemma_9_1_7, lemma_9_1_7') and general facts (isClosed_ |
| V9_8 | same | B ⇒ A only | equivalent | The item lists two definitions and one witness theorem. A is the type of the witness, isManifoldType_indicator: the indicator of a point of ℝⁿ is of manifold type in the trivial ep-groupoid; it has no universe parameters. B says the project's IsManifoldType and IsOrbifoldType are the text's notions  |
| V9_9 | narrower | B false | A_narrower | B is the literal Proposition 9.1.11: ∃! locally finite family of k-dimensional branched ep⁺-subgroupoids with Θ = ∑ᶠ Θ_k. As its author predicted, B does not hold as we read it, and A agrees. A contains not_proposition_9_1_11_rn, the project's decompositions decompA (Θ₀ = 1_{0}, Θ₁ = 1_{L∖0}) and de |
| V9_10 | explicit | B ⇒ A only | A_narrower | B is Proposition 9.1.12 for every ep-groupoid and every branched Θ. A proves it for ep-groupoids over ℝᵐ (proposition_9_1_12_rn, rn_zero, rn_one), or under TopMultiplicity / HasGraphChartAt on the M-polyfold, which the project establishes only for ℝᵐ. A also contains the equidimensional case, the sh |
| V9_11 | restated | B false | A_narrower | A is the six fibre/push lemmas for Gr(X) at universe 0 (Tφ on fibres, grPush_mem/comp/unit). B says the project's Gr x, GrObj and grProj are the text's. For Gr(x), B uses GrB: ℚ-weights of any sign on sets L ⊆ T_xX that are finite-dimensional linear subspaces in some chart. The project's Gr x is a d |
| V9_12 | restated | equivalent | equivalent | The project's T_yM (submanifoldTangent) is the set of vectors over y fixed by Tr. B's T_yM is the image Tr(T_yX). A ⇒ B: Tr is idempotent (tmap_tmap) and maps T_yX into T_{r(y)}X = T_yX. So the image is the fixed set, and with mem_submanifoldTangent_iff (any data computes the fixed set) B (c) follow |
| V9_13 | explicit | B ⇒ A only | A_narrower | A is the project's Theorem 9.2.1 (tangentValue_eq, grPush_tangentValue, theorem_9_2_1), plus tangentSum_transport. All of it assumes HasIndependentTangentSums Θ: that ∑ σᵢ T_xMᵢ does not depend on the local branching structure, which is the hard part of Theorem 9.2.1 (1). B asserts this independence |
| V9_14 | explicit | B ⇒ A only | A_narrower | Same sums: B's sumB is the project's tangentSum. B is the text's claim: for every branched Θ on every ep-groupoid, ∑ σᵢ · T_xMᵢ is the same for any two local branching structures at x ∈ supp Θ. A (9 theorems, universes at 0) proves this only in special cases: at good points; when supp Θ ⊆ S^g; under |
| V9_15 | restated | neither | equivalent | This item is a definition, and the definitions agree with the text's. B_holds proves B outright: the project's MU is ⋃ᵢ Mᵢ (rfl), its IsGoodPoint is the text's good point IsGoodAt (an open V ∋ y with V ⊆ U(x) and Mᵢ ∩ V = Mⱼ ∩ V for all i, j with y ∈ Mᵢ ∩ Mⱼ; the two differ only by inter_comm and by |
| V9_16 | stronger | A ⇒ B only | A_stronger | Both sides use the same notion of good point: B's IsGoodAt is the project's IsGoodPoint up to inter_comm. A (lemma_9_2_3, universe 0) holds for every Θ : Obj → ℚ, with no branched and no dimension hypothesis. It covers a structure B at x and a structure B' at any x', with different domains, for any  |
| V9_17 | restated | A ⇒ B only | A_stronger | Same good points: B's IsGoodAt is IsGoodPoint up to inter_comm. Universes are at 0. A ⇒ B holds. (a): a point good for B₁ lies in supp Θ, hence in goodSet, and remark_9_2_4_a makes it good for B₂. (b): the data (V, M, Θ(y)) of remark_9_2_4_b form a local branching structure at y with ι = Unit and we |
| V9_18 | stronger | A ⇒ B only | A_stronger | Same notion of good point. B's IsGoodPt X Θ y (good, in the IsGoodAt sense, for some structure whose domain contains y) is exactly the project's y ∈ goodSet X Θ (isGoodPt_iff); the y ∈ supp Θ clause of goodSet is automatic. A ⇒ B is lemma_9_2_5 rewritten. Universes are at 0. B ⇒ A fails for a genuin |
| V9_19 | restated | A ⇒ B only | A_stronger | The definitions agree with the text. The project's goodSet is {y ∈ supp Θ / y good for some structure whose domain contains y}, which is B's {y ∈ supp Θ / IsGoodPt y} up to inter_comm. Its badSet = supp Θ ∖ goodSet is B's {y ∈ supp Θ / ¬ IsGoodPt y}. These two parts of B are definitional (goodSet_eq |
| V9_20 | stronger | A ⇒ B only | A_stronger | A ⇒ B: B's IsGoodAt is the project's IsGoodPoint (⋃ Mᵢ = MU, Mᵢ ∩ V vs V ∩ Mᵢ), so B's Sg, Sb are exactly the preimages of goodSet, badSet in the subtype supp Θ (Sg_eq, Sb_eq), and lemma_9_2_7_1 plus lemma_9_2_7_1_dense give the four claims; B's equidimensionality hypothesis is never used. B ⇒ A fai |
| V9_21 | explicit | neither | incomparable | A's general lemma_9_2_7_2 needs two things that B's hypotheses (Θ branched and equidimensional, x bad, B any structure at x) do not supply. (i) It needs the given structure to be n-dimensional (B.IsOfDim n), whereas IsNDimensional Θ n only provides SOME n-dimensional structure at each point. (ii) It |
| V9_22 | narrower | neither | incomparable | Every general-M-polyfold theorem of A is conditional on a graph-representation hypothesis (HasGraphChartsAt / HasGraphChartAt / HasGraphBallAt, plus HasContinuousLevelOneOn) that the project proves only in ℝᵐ. B asserts Proposition 9.2.8 and Lemmas 9.2.9–9.2.11 in every M-polyfold, for every structu |
| V9_23 | explicit | neither | incomparable | Both sides concern the same function, the project's tangentTheta. B's (1), TΘ = 0 over {Θ = 0}, is the non-item lemma tangentTheta_eq_zero. B states (2), the local formula for every structure, and (3), TΘ a branched ep⁺-subgroupoid of TX, for every branched Θ with no further hypothesis. A has them o |
| V9_24 | stronger | B false | incomparable | B reads Lemma 9.2.13 literally at every x ∈ M: (x ∈ ∂X ∧ x ∉ ∂M) ↔ IsTangentReducedAt M x. As its author predicted, B does not hold as we read it. not_B uses the point {0} of ℝ¹: off ∂X, (2) holds (isTangentReducedAt_of_not_mem_boundary, the first half of the project's lemma_9_2_13_of_not_mem_bounda |
| V9_25 | restated | equivalent | equivalent | B uses the project's submanifoldBoundary, which for a smooth M and x ∈ M is 1 ≤ subDegIndex (mem_submanifoldBoundary_iff_subDegIndex, not an item theorem), i.e. by definition membership in the boundary of the induced structure. A ⇒ B is remark_9_2_14_iff. B ⇒ A: remark_9_2_14, remark_9_2_14_not_isTa |
| V9_26 | explicit | B ⇒ A only | A_narrower | Universes at 0. A's forms of Proposition 9.2.15 (1) and (3), the local formula boundaryTheta_eq, isFunctorial_boundaryTheta and filter_tangentValue_eq all take hind : HasIndependentTangentSums Θ, i.e. Theorem 9.2.1's claim that ∑ σᵢ T_xMᵢ does not depend on the local branching structure. B claims (1 |
| V9_27 | narrower | B false | A_narrower | B is Definition 9.2.16 read literally. It says the project's ∂Θ is a functor X → ℚ⁺ with (1) supp ⊆ ∂X and (2) the local formula at the points of supp(F), and that it is the only such functor. As its author predicted, B does not hold as we read it. (2) is vacuous for F = 0, while for Θ = 1 on [0, ∞) |
| V9_28 | restated | A ⇒ B only | equivalent | B is the existential content of the remark: some branched ep⁺-subgroupoid has a local branching structure at x ∈ supp Θ and a y ∈ U(x) ∩ ∂X with ∑_{y ∈ ∂Mᵢ} σᵢ ≠ Θ(y). A_to_B takes A's witness boundaryTheta_halfLineCorner (Θ = 1_{0} on [0, ∞)): 0 ∈ ∂X, Θ(0) = 1 and ∂Θ(0) = 0. A local branching struc |
| V9_29 | restated | equivalent | equivalent | B (a) says the project's Gr̂(x) is the set of finitely supported sums with weights ≥ 0 of oriented tangent sets over x (IsOrientedAt). This is the definition of GrHat (Iff.rfl). B (b) asks for a functor F : Gr̂(X) → Gr(X) that is (x, ∑σ(L, o)) ↦ (x, ∑σL) (Finsupp.mapDomain carrier) on objects and th |
| V9_30 | restated | B ⇒ A only | equivalent | This item is a definition. B says the project's IsOrientation Θ T is the text's Definition 9.3.2 (blind IsOrientationB) for every branched Θ and every T. It holds (B_holds, so A_to_B does not use A). The fields mem, natural / functor and lifts agree by unfolding GrHat, grHatPush and grForget. In (9. |
| V9_31 | stronger | A ⇒ B only | incomparable | A (remark_9_3_3) says that for Θ = 1_{p} on ℝⁿ, q ↦ q·(T_p{p}, +) + (1 − q)·(T_p{p}, −), q ∈ (0, 1) ∩ ℚ, is an injective family of orientations. B (b), that some Θ has two orientations differing at a smooth point, follows from A (T̂_{1/2} ≠ T̂_{1/3}). B (a) asks for an orientation with two oriented  |
| V9_32 | narrower | B ⇒ A only | A_narrower | A's general Lemma 9.3.4 (lemma_9_3_4, universes at 0) concludes T₁ = T₂ on X_∞ for n-dimensional orientations (IsOrientationOfDim) agreeing at the good points, but only under hgood : ∀ x ∈ supp Θ, HasOrientedGoodPointsAt x n. That hypothesis is the oriented form of Proposition 9.2.8, with locally co |
| V9_33 | narrower | neither | incomparable | B quantifies over every β with β(0) = 0, β > 0 off 0 and all four β^{±±} smooth. A (eleven theorems, no universes) is about the single project β = betaPP (expNegInvGlue s + expNegInvGlue (−s)). So A ⇒ B fails for every other β. The project's lemmas that matter (isOrientation_sum_rn, hasIndependentTa |
| V9_34 | restated | neither | incomparable | This item is a definition plus witnesses. A (universes at 0) is isTameBranched_zero ∧ isTameBranched_indicator ∧ hasTameInducedStructure_of_degIndex_eq_zero: two satisfiability witnesses of IsTameBranched and a sufficient condition for a tame induced structure. B says (a) the project's IsTameBranche |
| V9_35 | stronger | A ⇒ B only | A_stronger | A (universes at 0) contains B's statement in a stronger form: subDegIndex_eq_of_submanifoldTangent_eq gives d_{M₁}(y) = d_{M₂}(y) from T_yM₁ = T_yM₂ for smooth submanifolds with tame induced structures, without B's hypotheses that Y is tame and that M₁, M₂ have the same dimension. A_to_B applies tha |
| V9_36 | narrower | neither | incomparable | A (universes at 0) formalizes Definition 9.3.8 with T_y∂M and the outward vector as data K, e. It proves that boundaryFrames O K e orients K when K ⊆ T_yM has m-dimensional chart image and e ∉ K (isOrientedAt_boundaryFrames), and that the frames are unchanged under e ↦ c e + k with c > 0, k ∈ K, rea |
| V9_37 | narrower | neither | incomparable | B's (9.11) part follows from A (A_to_B_9_11, rt_check OK, uses the hypothesis). B's (B, n, o) become project OrientedBranchingStructures; the dimensions come from the orientations, via the glue lemma isSubmanifoldOfDim_of_orientation. At smooth y ∈ U ∩ U' both represent T y, so eq_9_11 gives equal d |
| V9_38 | narrower | neither | equivalent | The item lists only the definition boundaryLift bd T y = mapDomain bd (degree-1 part of T y), so A = True. The content is B, which is proved outright (B_holds, universes at 0) for every boundary operation bd. First clause: an orientation vanishes at smooth points off supp Θ (IsOrientation.eq_zero_of |
| V9_39 | restated | A ⇒ B only | A_stronger | The notions agree. On the quadrant model, B's unit vectors lim (φ(z_k) − φ(z))//φ(z_k) − φ(z)/ (sequences z_k ∈ K∖{z} → z in M) are exactly the project's unitDirections of the chart image φ(V∩K) at φ(z) (glue lemma unitVecsB_eq: tails lie in the chart domain, where φ is injective and continuous, and |
| V9_40 | same | A ⇒ B only | A_stronger | Both sides state the same two claims about the same project definition essentialSet: (essentialSet K) is closed, and K ∖ essentialSet K is open, as preimages under the inclusion K → M. A (lemma_9_4_2 and lemma_9_4_2_open, universes at 0) holds for every model with corners I : H → E (any real normed  |
| V9_41 | restated | B ⇒ A only | A_narrower | B is (a) the project's PropertyT V ⇔ the text's (T) on V and (b) Lemma 9.4.3: (T) holds on some open U'(x) ⊆ U(x). (a) holds outright (propertyT_iff), by pure logic. The project's iff 'equal at y₀ ⇔ equal at y' splits into B's ε = 1 case (forward) and its ε = -1 case (backward, by contraposition), w |
| V9_42 | narrower | neither | incomparable | A is lemma_9_4_4_mixed_dim, a counterexample: for different dimensions (K = ℝ × 0 inside ℝ and inside ℝ²) Lemma 9.4.4 fails. Lemma 9.4.4 itself is not a theorem of the project. The project's sheets are submanifolds of an M-polyfold with no manifold structure of their own. Their essential points and  |
| V9_43 | restated | neither | equivalent | This is a definition item, and the definitions agree exactly. B (for the quadrant model [0,∞)ⁿ ⊆ EuclideanSpace ℝ (Fin n)) holds by Iff.rfl (B_holds): the project's IsMeasureZero I K is ∀ e ∈ maximalAtlas I ∞ M, volume (chartImage I e K) = 0, chartImage I e K is e.extend I '' (e.source ∩ K), and bot |
| V9_44 | stronger | A ⇒ B only | A_stronger | A (universes at 0) is lemma_9_4_6 and isMeasureZero_setOf_relTangent_ne_top for every subset K of every smooth finite-dimensional Mathlib manifold with corners (any model I : H → E), plus three Euclidean lemmas: span_unitDirections (the hull of the text's unit directions is the span of Mathlib's tan |
| V9_45 | restated | neither | incomparable | A (universes at 0) is the bookkeeping over an abstract SheetGeometry G on an M-polyfold: with Lemma 9.4.4 (field ess_comm) and the note T_zN = T_zN' at essential points (field submanifoldTangent_eq) given, the chain relation is an equivalence and preserves P.submanifoldTangent. B asks for these two  |
| V9_46 | restated | A ⇒ B only | A_stronger | A (universes at 0) is lemma_9_4_8 and isNullIn_diff_MStar for every SheetGeometry on every M-polyfold. A ⇒ B applies lemma_9_4_8 to a SheetGeometry tG L built from B's structure. It lives on the discrete M-polyfold F ⊕ (ι × ι), and sheet i is Mᵢ plus the tags (p, q) with p = i or q = i. The tags of  |
| V9_47 | explicit | neither | incomparable | A (universes at 0) is proposition_9_4_9 and tangentValue_eq_sum for an oriented local branching structure on an ep-groupoid. It uses an abstract SheetGeometry on X.PObj, tangent spaces and OrTangents in Part I's tangent bundle, TΘ = X.tangentValue under HasIndependentTangentSums, and Property (T) as |
| V9_48 | stronger | neither | incomparable | A (universes at 0) is proposition_9_4_10 and tangent_eq_iff_of_mem_ess for oriented local branching structures on an ep-groupoid. It uses an abstract SheetGeometry on X.PObj and tangent spaces and OrTangents in Part I's tangent bundle; proposition_9_4_10 does not need (T). A also contains three Exam |
| V9_49 | restated | neither | equivalent | B says the project's IsMeasureZeroSupp equals the blind reading IsMeasureZeroB. This holds outright (isMeasureZeroSupp_iff, B_holds) for every ep-groupoid, SheetNullSets and A, without B's hypotheses (oriented, tame, compact, n-dimensional, A ⊆ S). Both ask, at every x ∈ supp(Θ), for one tame local  |
| V9_50 | narrower | neither | incomparable | Both directions are vacuous; the statements use different notions of measure zero. A (universes at 0) is Lemma 9.5.2 and five companion facts for an abstract null-set system G : SheetNullSets S, whose field isNull_transfer (two sheets of S induce the same null sets on their intersection) carries the |
| V9_51 | restated | neither | incomparable | Both sides define L(S) the same way: B's LSB is the project's borelNullSigma of its null sets, by rfl. A (universes at 0) states the remark for any σ-ideal 𝒩 (measurableSet_borelNullSigma_iff) and for the project's lebesgueSigma over an abstract SheetNullSets. B states it for its concrete null sets  |
| V9_52 | explicit | neither | incomparable | A (universes at 0) has two theorems. isMeasureZeroBoundaryAll_of: if a choice of tame structures has null boundary preimages, every structure has them, for an abstract SheetNullSets G' on the boundaries ∂Mᵢ, under the hypothesis HasIndependentTangentSums Θ (the independence of TΘ from Theorem 9.2.1) |
| V9_54 | narrower | A ⇒ B only | A_stronger | A (universes at 0) is the isotropy and set part of Lemma 9.5.9 for a project NaturalRep R and a local branching structure with B.U = R.U: π_Φ, H = stabilizer ↔ Φ(g)y = y, ♯(G_x/H)·♯G_y = ♯G_x, exists_slice (an H-invariant V inside any open W, disjoint from its other translates), Φ(g)(M_U) ⊆ M_U and  |
| V9_55 | narrower | A ⇒ B only | A_stronger | A (universes at 0) is ♯G^eff_x · ♯T_x = ♯G_x, and for a natural representation R with R.HasLUC: ker Φ = T_x, ker Φ ⊆ H, h ∈ ker Φ ↔ stabilizerEquivIsotropy h ∈ T_y, ♯T_y = ♯T_x and (9.23) ♯(G_x/H) · ♯G^eff_y = ♯G^eff_x. B states, for X with global LUC and B's natural action on a connected U, that T_ |
| V9_56 | narrower | A ⇒ B only | A_stronger | A (universes at 0) is card_isotropy_eq_of_mor and card_effIsotropy_eq_of_mor for every morphism (the effective one without LUC), IsFunctorial.eq_of_π_eq, image_π_MU_eq for every onto map f : U → U' with /f z/ = /z/ between two local branching structures, and NaturalRep.Φ_hyps. B states, for φ with B |
| V9_57 | narrower | A ⇒ B only | A_stronger | A (universes at 0) = A1 card_effIsotropy_eq_of_isEffective (effective ⇒ ♯G^eff_x = ♯G_x), A2 isFunctorial_reduced_iff (Θ functorial on X_R iff on X), A3 card_effIsotropy_eq_reduced (♯G^eff_x = ♯G^R_x and ♯(G^R_x)^eff = ♯G^R_x for every X with T_R Hausdorff and paracompact, no LUC hypothesis); toRedu |
| V9_58 | stronger | neither | incomparable | A (universes at 0) = HasDimAt.le_of_inter_subset ∧ exists_mem_forall_notMem (the covering lemmas replacing 'measure zero') ∧ lemma_9_6_1 ∧ localTopDim_eq ∧ localTopDim_eq_bot. lemma_9_6_1 says two structures at x whose sheets carry constant-dimension labels (IsSubmanifoldOfDim) have the same max lab |
| V9_59 | same | A ⇒ B only | A_stronger | A (universes at 0) = lemma_9_6_2 (M_U^k ∩ U' = M'^k_U ∩ U for two dimension-labelled structures at x) ∧ mem_topUnion_iff_of_mem (the same pointwise on U ∩ U'), with no hypothesis on Θ or x; topUnion is vocabulary. B is the same equation for a branched Θ, x ∈ supp Θ and blind labels IsDimLabelB (HasD |
| V9_60 | restated | neither | equivalent | The item is a definition. IsTopGoodPoint and IsTopBadPoint are vocabulary; A (universe 0) is the type of the one listed theorem, dimPart_topDim_eq_of_isTopGoodPoint (p. 456: Θ_k agrees at a point of U ∩ U' that is top-good for two labelled structures). B says the project's IsTopGoodPoint / IsTopBadP |
| V9_61 | explicit | neither | incomparable | A (universes at 0) has seven conjuncts. lemma_9_6_4 and isTopBadPoint_iff give Lemma 9.6.4 for two labelled structures and any Θ, but only under the hypothesis MPolyfold.TopMultiplicity of the top dimension. lemma_9_6_4_of_hasGraphChartAt gives it under the graph representation at every point. The o |
| V9_62 | narrower | B false | A_narrower | A (universes at 0) is Proposition 9.6.5 and the formula of p. 457 in slice form. proposition_9_6_5: under HasGraphChartAt x, every open W ∋ x contains a finite top slice S for the class of i₀, at every x and for every Θ; the points of S are not claimed top-good. sum_class_eq_sum_of_isTopSlice and di |
| V10_1 | same | equivalent | equivalent | A (universes at 0) is the nine listed theorems: full_iff, faithful_iff, essSurj_iff (for arbitrary groupoids), the consequences IsEquivalence.essSurj/exists_iso/exists_mor_eq/mor_injective, and the witnesses IsEquivalence.id, isEquivalence_pairToPoint. B says the project's IsEquivalence (and EP.equi |
| V10_2 | stronger | equivalent | equivalent | A (universes at 0) is lemma_10_1_2, isEquivalence_iff, isEquivalence_toFunctor, IsEquivalence.comp, the orbit-map lemmas (injective_orbitMap_of_full, surjective_orbitMap_iff, bijective_orbitMap_of_isEquivalence, continuous_orbitMap, isOpenMap_orbitMap) and not_exists_leftInverse_pairToPoint. B is (a |
| V10_3 | explicit | equivalent | equivalent | A (universe 0, Obj Mor ι : Type) is the four listed ep-groupoid conditions of X_𝒰 (isLocalScDiffeo_src/tgt, exists_isProperMap, isScSmoothCompSheet), proposition_10_1_3 and the reflectionCover witness pair. B pins 𝒰.epGroupoid and 𝒰.functor down by their data (objects, morphisms, structure maps, POb |
| V10_4 | same | equivalent | equivalent | A (universes at 0) is definition_10_1_4, naturallyEquivalent_equivalence, NaturallyEquivalent.comp_left and comp_right. B says EpNatTrans F G is exactly the blind IsNatTransB (sc-smooth τ : X → 𝐘, τ(x) : F x → G x, naturality for φ : x → x'), NaturallyEquivalent ↔ NatEqB, NatEqB is an equivalence re |
| V10_5 | same | equivalent | equivalent | A (universes at 0) is proposition_10_1_5 (F ≃ G ⇒ (F equivalence ↔ G equivalence)), IsEquivalence.of_natTrans, and three lemmas on τ: continuous_app, isLocalScDiffeo_app, isLocalScDiffeo_obj (only F local sc-diffeo on objects assumed). B: NatEqB F G ⇒ (IsEquivB F ↔ IsEquivB G). A ⇒ B: a blind natura |
| V10_6 | same | equivalent | equivalent | A (universes at 0) is proposition_10_1_6 plus seven general lemmas: IsLocalScDiffeoAt.comp/congr/of_comp_left/of_comp_right and EpFunctor.isLocalScDiffeoAt_mor, isLocalScDiffeo_mor, isLocalScDiffeoAt_obj_tgt (transport of local sc-diffeomorphy along a morphism, which the project adds to the text's a |
| V10_7 | same | equivalent | equivalent | A (universes 0) is theorem_10_1_7: F.IsEquivalence → F.tangent.IsEquivalence. B states the same with its own IsEquivB (full and faithful via src/tgt/mor, a homeomorphism of Quot-orbit spaces extending /x/ ↦ /Fx/, local sc-diffeomorphism on objects), plus five equations pinning TX and TF (object/morp |
| V10_8 | stronger | equivalent | equivalent | A has five conjuncts: isEquivalence_negFunctor, orbitMap_id_eq_negFunctor, remark_10_1_11_family (α_z = (-1, z) is an sc-smooth family F(z) → G(z)), remark_10_1_11 (no α merely continuous at 0 with α 0 = 1_0 and the source/target conditions eventually), and remark_10_1_11_scSmooth (no α sc-smooth on |
| V10_9 | same | equivalent | equivalent | A (universes 0) has three conjuncts. isotropyHom_mem_trivialSet_iff: for F only a local sc-diffeomorphism on objects, F(g) ∈ T_{Fx} ↔ g ∈ T_x. bijective_isotropyHom: for an equivalence, g ↦ F(g) is bijective G_x → G_{Fx}. remark_10_1_12: the remark, with value (ψ∘F g)∘ψ⁻¹ and e g ∈ T_y ↔ g ∈ T_x. B  |
| V10_10 | same | equivalent | equivalent | A (universes 0) has nine conjuncts. proposition_10_1_13: for an equivalence, F.reducedMap is continuous and open, and T2 𝐗^R ↔ T2 𝐘^R. IsEquivalence.isClosed_nonEffectivePart_iff: 𝐗^T is closed iff 𝐘^T is. Five lemmas for functors that are only local sc-diffeomorphisms on objects: mor_mem_nonEffecti |
| V10_11 | same | equivalent | equivalent | A (universes 0) has two conjuncts. reducedπ_eq_of_mor: for an equivalence and with no Hausdorff hypothesis, φ and φ' with the same source and target and [Fφ] = [Fφ'] have [φ] = [φ']. proposition_10_1_14: with [T2Space X.ReducedMor] [T2Space Y.ReducedMor], F.reduced is an equivalence. B, under the sa |
| V10_12 | stronger | equivalent | equivalent | A has five conjuncts. Four are computations in the example: (2, x) ∈ 𝐗^T; (2, 0) ∉ 𝐘^T; [(1, x)] = [(3, x)] in 𝐗^R; [(1, 0)] ≠ [(3, 0)] in 𝐘^R. The fifth, example_10_1_15, says no f : 𝐗^R → 𝐘^R has f[φ] = [Φφ], verbatim B's claim. B also pins down the example. Every equation is rfl except X's target |
| V10_13 | same | equivalent | equivalent | A (universes at 0) is proposition_10_1_16 (X.IsLUC ↔ Y.IsLUC for an equivalence F), isClosed_nonEffectivePart_iff (𝐗^T closed iff 𝐘^T closed) and Chapter 7's proposition_7_2_21 ((LUC) iff 𝐗^T closed). B is proposition_10_1_16 verbatim, so A_to_B is immediate. B_to_A takes 10.1.16 from B and get |
| V10_14 | same | equivalent | equivalent | A (universes at 0) has six conjuncts: mem_smoothSet_src_iff and mem_smoothSet_tgt_iff (s φ, t φ smooth iff φ is), tangentMor_mor (naturality T(Fφ) ∘ TF = TF ∘ Tφ), the two halves isZhou_of_isZhou and isZhou_of_isZhou_right, and proposition_10_1_17 (X.IsZhou ↔ Y.IsZhou for an equivalence). B is propo |
| V10_15 | same | equivalent | equivalent | A (universes at 0; EpFunctor.liftOne is vocabulary) has three conjuncts: IsEquivalence.liftOne (F¹ : X¹ → Y¹ is an equivalence), EP.exists_isEquivalence_lift (equivalences Fⁱ : Xⁱ → Yⁱ exist for all i) and EP.proposition_10_1_18 (A.IsSLUC ↔ B.IsSLUC). B's SLUC is EP.IsSLUC by rfl. A_to_B is proposit |
| V10_16 | same | equivalent | equivalent | A (universes at 0) has three conjuncts: EP.proposition_10_1_19 (A.IsSLR ↔ B.IsSLR for an equivalence F, derived in EquivalenceLR.lean from Proposition 10.1.9), EP.isSLR_iff_of_isLR_iff (the same conclusion under an extra hypothesis, that (LR) passes along every equivalence of lifts) and EP.isLR_iff_ |
| V10_17 | restated | B ⇒ A only | equivalent | The item is a definition. A (universes at 0) is the three listed lemmas: conj_comp_mor, conj_recover and src_eq_tgt_iff (the composable pairs). B says the project's Obj F G, Mor F G and groupoid F G are the text's: objects and morphisms are exactly the constrained triples (entries, extensionality, m |
| V10_18 | stronger | neither | A_stronger | The two sides put different M-polyfold structures on different carriers. In A, Obj F G is a nested subtype of ObjX × objRight G, with objRight G ⊆ MorY × ObjZ. Its structure PObj F G h is the iterated sub-M-polyfold structure: objRight ⊆ 𝐘 × Z first, then objSet ⊆ X × PA G (likewise for morphisms).  |
| V10_19 | same | B ⇒ A only | A_narrower | Both sides make the same claims for an equivalence F: π_Z is an equivalence, F∘π_X ≃ G∘π_Z, d = d_Z∘π_Z, and tameness and a paracompact orbit space pass from Z. They make them about different ep-groupoids. A uses the project's epGroupoid F G h on Obj F G, with the iterated sub-M-polyfold structure.  |
| V10_20 | stronger | B ⇒ A only | A_narrower | Same carrier/structure mismatch as V10_19. A is about the project's epGroupoid F G h on Obj F G, with the iterated sub-M-polyfold structure. B is about some E on objSetB ⊆ X × 𝐘 × Z, with the triple-product structure (IsWFPEpB). B ⇒ A is proved with the comparison functor toE : epGroupoid → E, copie |
| V10_21 | same | B ⇒ A only | A_narrower | Same carrier/structure mismatch as V10_19. A (remark_10_2_3) is about the project's epGroupoid F G _ on Obj F G, with the iterated sub-M-polyfold structure. B is about some E on objSetB ⊆ X × 𝐘 × Z, with the triple-product structure (IsWFPEpB). B ⇒ A is proved with the comparison functor toE (copied |
| V10_22 | restated | equivalent | equivalent | A (universe 0; the two example theorems have no universe) is the conjunction of ten theorem types: IsStrongBundleFunctor.comp, covers, eq_of_obj_eq, isLocalScDiffeo_obj, isLocalScDiffeo_one, isStrongBundleEquivalence_id, IsStrongBundleEquivalence.comp, isStrongBundleEquivalence_of_inverse and the wi |
| V10_23 | restated | A ⇒ B only | A_stronger | A (universe 0) has ten conjuncts. Seven are the pull-back / push-forward theorems: obj_pullback, pullback_eq, isFunctorialSection_pullback, pushforward_eq (10.22), isFunctorialSection_pushforward, pullback_pushforward, pushforward_pullback. They are stated for arbitrary sections and functorial secti |
| V10_24 | stronger | A ⇒ B only | A_stronger | A (universe 0) = proposition_10_4_2 ∧ pullback_eq_of_orbitMap_eq. proposition_10_4_2 is the text's statement, for f' ∈ Γ(P', μ'). pullback_eq_of_orbitMap_eq is the project's helper, for every functorial section, sc-smooth or not. B has the same content as proposition_10_4_2, once the vocabulary is m |
| V10_25 | stronger | equivalent | equivalent | A (universes at 0) is proposition_10_4_3 (Φ_* f = Ψ_* f for f ∈ Γ(P, μ) when /Φ/ = /Ψ/ : /W/ → /W'/) together with pushforward_eq_of_orbitMap_eq (the same for every functorial section, sc-smooth or not). B states the first with its own push-forward pushB, which picks some (x, σ : ϕ(x) → x') by Class |
| V10_26 | stronger | A ⇒ B only | A_stronger | A (universes at 0) has two conjuncts. proposition_10_4_4 gives (Ψ∘Φ)^* = Φ^*∘Ψ^* for every section f'' of P'' and (Ψ∘Φ)_* = Ψ_*∘Φ_* for every functorial section f, with no sc-smoothness. IsStrongBundleEquivalence.comp says Ψ∘Φ is again a strong bundle equivalence; B presupposes this but does not sta |
| V10_27 | narrower | B ⇒ A only | A_narrower | A (universes at 0) is theorem_10_4_5 plus twelve supporting lemmas. theorem_10_4_5 says Φ_* and Φ^* are mutually inverse bijections Γ ⇄ Γ'; when /Φ/ = /Ψ/, Φ_* = Ψ_* and Φ^* = Ψ^*; and both restrict to Γ⁺. The project docstring says the Fred part is not formalized. B has this content as (a)–(f), wit |
| V10_28 | restated | B ⇒ A only | equivalent | The item is a definition; its only theorem is the witness strongBundleNatEquiv_example (Φ ≃ Φ for the concrete strong bundle equivalence (-id)*W' → W'), and A is its type. B is the real comparison: the project's StrongBundleNatTrans has exactly the text's data. Its fields src_T, tgt_T, naturality an |
| V10_29 | explicit | A ⇒ B only | A_stronger | A (universes at 0) has six conjuncts. T_val and T_eq give T(w) = (τ(P(w)), Φ(w)); obj_eq gives (10.23) Ψ(w) = μ'(τ(P(w)), Φ(w)); unique says Ψ on objects and T are determined by Φ and τ.app; unique_functor says the functor Ψ itself is determined when both candidates are strong bundle functors coveri |
| V10_30 | explicit | A ⇒ B only | A_stronger | A (universes at 0) has three conjuncts. isStrongBundleNatTransMap gives 10.4.8 ⇒ 10.4.10 and needs only Φ to be a strong bundle functor. The two orbitMap_eq give Φ ≃ Ψ ⇒ /Φ/ = /Ψ/, which B does not mention. B (a) is a definitional comparison: the project's IsStrongBundleNatTransMap (T_val, strong bu |
| V10_31 | restated | neither | equivalent | This is a definition item: SEP, SEP.Hom, SEP.equivalences, SEP.toEP and negSEPHom are vocabulary. A (universe 0) is the conjunction of two side theorems: toEP_map_mem_equivalences (the forgetful functor SEP → EP maps F into E) and negSEPHom_mem_equivalences (a witness in F). Neither is part of Defin |
| V10_32 | same | equivalent | equivalent | A (universes at 0) has three conjuncts: isEquivalence_of_isIso (an IsIso morphism of the category EP is an equivalence), IsEquivalence.comp, and proposition_10_1_5 (if F ≃ G, then F is an equivalence iff G is). B states (E1) for B's own componentwise notion of isomorphism, IsIsoB (an EpFunctor G inv |
| V10_33 | restated | equivalent | equivalent | Diagram, IsRefinement and precomp are vocabulary. A (universe 0) has three conjuncts: IsRefinement.refl, isRefinement_precomp (the first example, X ←F∘H A' →Φ∘H Y) and isRefinement_of_naturallyEquivalent (the second example, X ←G A →Ψ Y with G ≃ F and Ψ ≃ Φ, via H = 1_A). B's parts (a) (the left leg |
| V10_34 | same | equivalent | equivalent | A (universe 0) has two conjuncts: lemma_10_3_2 (d' refines d and d'' refines d', so d'' refines d) and IsRefinement.trans (the same with the hypotheses swapped). B states the lemma for its own IsRefinementB, copied from the blind V10_33. That relation is the project's Diagram.IsRefinement by definit |
| V10_35 | same | neither | equivalent | This is a definition item. Only Diagram.IsCommonRefinement (d''.IsRefinement d ∧ d''.IsRefinement d') is listed, so A = True and both implications are vacuous. The content is B itself, proved outright as B_holds by Iff.rfl. B's IsRefinementB is the project's IsRefinement by definition, since Natural |
| V10_36 | same | equivalent | equivalent | A (universe 0) has three conjuncts: lemma_10_3_4 and Equiv.trans (Equiv d d' → Equiv d' d'' → Equiv d d''), and IsRefinement.equiv (a refinement is equivalent to the diagram it refines). The project's Diagram.Equiv d d' is by definition ∃ e, e.IsRefinement d ∧ e.IsRefinement d'. That is B's 'has a c |
| V10_37 | restated | equivalent | equivalent | A (universe 0) is Equiv.refl, Equiv.symm, equiv_iff (d ≈ d' ↔ Equiv d d' for Diagram.setoid) and the witness equiv_pairToPoint_id. B (at universe 0) says Diagram.Equiv is 'having a common refinement' (EquivB, with refinements written out from Definition 10.3.1) and that ⟦d⟧ = ⟦d'⟧ for the project's  |
| V10_38 | same | equivalent | equivalent | A (universes 0) is the lemma itself (lemma_10_3_6), its corollary for equivalent diagrams (Equiv.orbitMap_eq), and four side facts. The side facts are continuity of /d/, /d/ ∘ /F/ = /Φ/, NaturallyEquivalent.orbitMap_eq (F ≃ G ⇒ /F/ = /G/) and EpFunctor.orbitMap_comp. B: if d' refines d, then orbB d  |
| V10_39 | same | equivalent | equivalent | A (universe 0) is orbitMapQ_mk (/⟦d⟧/ = d.orbitMap = /Φ/ ∘ /F/⁻¹ for every representative) and isHomeomorph_orbitMap (d.orbitMap is a homeomorphism when d.Φ is an equivalence). B: Diagram.orbitMapQ ⟦d⟧ = orbB d, and orbitMapQ ⟦d⟧ is a homeomorphism when d.Φ is an equivalence. The blind orbB is defin |
| V10_40 | restated | equivalent | equivalent | B (universe 0) states the three claims for EquivB, using the project's Diagram.comp and Diagram.id: the class of the composite depends only on the classes, composition is associative, and [1_Y] ∘ [d] = [d] = [d] ∘ [1_X]. EquivB is definitionally Diagram.Equiv, which is the project's ≈, so A_to_B is  |
| V10_41 | same | neither | equivalent | The item is a definition. A (universe 0) is the single theorem isGeneralizedIso_iff_isIso: IsGeneralizedIso f ↔ Mathlib's IsIso f in the project's category EPLoc. B (universe 0) checks the project's definitions against the text, in three parts. (1) Every generalized map is a class homMk d = ⟦d⟧. (2) |
| V10_42 | same | equivalent | equivalent | B (universe 0): IsGenIsoB d ↔ d.Φ.IsEquivalence, where IsGenIsoB d means some e has EquivB (d.comp e) (id X) and EquivB (e.comp d) (id Y). When Φ is an equivalence, the reversed diagram revB d hΦ (definitionally d.symm hΦ) is a two-sided inverse. The glue isGenIso_iff (IsGeneralizedIso (homMk d) ↔ I |
| V10_43 | same | equivalent | equivalent | A (universes at 0) is the conjunction of five theorems: orbitMap_homMk (/[d]/ = /d/, rfl), EPLoc.continuous_orbitMap, EPLoc.orbitMap_id, Diagram.orbitMap_comp (/d.comp e/ = /e/ ∘ /d/ on representatives) and EPLoc.proposition_10_3_11 (/f ≫ g/ = /g/ ∘ /f/ on classes). B states the text's equation on r |
| V10_44 | restated | equivalent | equivalent | Definition item. A (universes at 0) is the six listed lemmas about the project's EPLoc (Category instance with Hom = Quotient (Diagram.setoid)): toEP_of and of_toEP; homMk_comp ([d] ≫ [e] = [d.comp e]); id_eq (𝟙 = [1_X]); homMk_eq_homMk_iff ([d] = [d'] iff Diagram.Equiv); and homMk_surjective. B cha |
| V10_45 | same | equivalent | equivalent | A (universes at 0; the Examples have none) is ten theorems about localizationFunctor (obj X = of X, map Φ = [X ←1 X →Φ Y]): isRefinement_ofFunctor_comp, obj/map, theorem_10_3_14 (identity on objects; i(F) a generalized isomorphism with inverse [Y ←F X →1 X]), isInvertedBy_localizationFunctor, inv_lo |
| V10_46 | same | equivalent | equivalent | A (universe 0) is theorem_10_3_15 about the defined functor orbitFunctor : EPLoc ⥤ TopCat. It says orbitFunctor.obj (of X) = TopCat.of /X/ and ⇑(orbitFunctor.map [d]).hom = /Φ/ ∘ /F/⁻¹; both are rfl given the definition. The functoriality is in the definition: orbitFunctor is a Mathlib Functor, with |
| V10_47 | same | equivalent | equivalent | A (universes at 0) has three theorems: exists_diagram_of_isGeneralizedIso (a generalized isomorphism has a representative X ←F A →Φ Y with Φ an equivalence; Theorem 10.3.10), iff_of_isGeneralizedIso (a property invariant under equivalences is invariant under generalized isomorphisms), and propositio |
| V10_48 | narrower | neither | incomparable | Both directions hold only outright (uses_hypothesis false for both), so the comparison is of content. A (universes at 0) is Rel.refl, Rel.symm, Rel.trans for every topological Z (the project drops metrizability) plus the witness rel_pairEP_pointEP. B is (1) the definition on representatives for metr |
| V10_49 | same | neither | equivalent | Definition item: only EPreg, EPLocReg (Mathlib's ObjectProperty.FullSubcategory of EP resp. EPLoc on the objects with IsLR) and the witnesses pointReg, pointLocReg are listed, so A = True and both implications are vacuous; the content is B itself, proved outright as B_holds. For both categories the  |
| V10_50 | same | equivalent | equivalent | A (universe 0) is theorem_10_3_21 ((LUC), (SLUC), (ZHOU)) ∧ theorem_10_3_21_all (all five properties as ↔), both for X Y : EP and f : of X ⟶ of Y a generalized isomorphism. B states the five ↔ for X Y : EPLoc and f : X ⟶ Y with IsGeneralizedIso f. EPLoc is a one-field structure around EP, so of X.to |
| V10_51 | same | equivalent | equivalent | A (universe 0) is twelve facts about the project's SDiagram / IsRefinement / Equiv / cls. They are the two refinement examples (precomp, of_natEquiv), refl/trans of refinement, refl/symm of Equiv, IsRefinement.equiv, NatEquiv.comp_left, cls_eq_cls_of_equiv, cls_eq_cls_iff, and the foldDiagram witnes |
| V10_52 | same | equivalent | equivalent | A (universe 0): IsRefinement.base, Equiv.base, Equiv.total, SDiagram.continuous_orbitMap, Equiv.orbitMap_eq, GenSBMap.orbitMap_eq_total, GenSBMap.continuous_orbitMap. B: (a) equivalent diagrams have the same [d] = homMk(base diagram), (b) GenSBMap.base [D] = [d], (c) /Φ/ : /W''/ → /W/ is a bijection |
| V10_53 | same | equivalent | equivalent | A (universe 0) is SDiagram.orbitMap_square (/P'/∘/D/ = /d/∘/P/ for a diagram), GenSBMap.orbitMap_square (the same for a class f, with f.base), and SDiagram.orbitMap_orbitMap_Φ (/D/(/Φ/q) = /Ψ/q, the lemma behind the square). B states the square pointwise for [D]: if /[D]/(/w/) = /w'/ then /[d]/(/P w |
| V10_54 | stronger | neither | incomparable | A (universe 0) is isotropyHom_spec, bijective_isotropyHom (γ is bijective when ψ is an equivalence) and exists_isotropyData. All three are stated for an arbitrary diagram of ep-groupoids and the project's specific γ = isotropyHom. B, for the base diagram of a strong bundle diagram D, has (i) the dat |
| V10_55 | explicit | equivalent | equivalent | A (universe 0) is the conjunction of seven theorems about the project's category SEPLoc: localizationPrefunctor_map_id, homMk_comp, id_eq, homMk_eq_homMk_iff ([D] = [D'] iff common refinement, i.e. the transitivity of Equiv), homMk_surjective, localizationFunctor_toPrefunctor and isInvertedBy_locali |
| V10_56 | same | B ⇒ A only | equivalent | A (universe 0) is the conjunction of isGeneralizedIso_symm (the reversed diagram W' ←Ψ W'' →Φ W of a representative with Ψ a strong bundle equivalence is a generalized strong bundle isomorphism), isGeneralizedIso_ofHom ([W ←1 W →Ψ W'] for Ψ a strong bundle equivalence) and isGeneralizedIso_negDiagra |
| V10_57 | restated | B ⇒ A only | A_narrower | A (universe 0) is remark_10_5_3 (a generalized strong bundle isomorphism [D] covers a generalized isomorphism of the bases, induces one of the total spaces, and /[D]/ is a homeomorphism) together with isIso_of_isGeneralizedIso ([D] with both legs strong bundle equivalences is an isomorphism of SEP(F |
| V10_58 | stronger | equivalent | equivalent | A (universe 0) has eight conjuncts: pushforward_eq_of_isRefinement (the text's step, a refinement by H does not change Ψ_* Φ*), three orbit lemmas on section functors (π_μ, π_eq_π_of_isFunctorialSection, eq_of_forall_π_eq: a section functor is determined by the orbits of its values), π_pushforward ( |
| V10_59 | narrower | equivalent | equivalent | A (universe 0) is theorem_10_5_4 together with pushforward_eq, pullback_eq (every representative with both legs equivalences gives [D]_*, [D]^*), the SDiagram-level invOn_pullback_pushforward, bijOn_pushforward, bijOn_pushforward_plus, and the two examples (bijOn_pushforward_negDiagram; pushforward_ |
| V10_60 | same | equivalent | equivalent | A (universe 0; the example theorems have no universe) has eleven conjuncts. remark_10_5_5: for every k, [W ←1 W →Inv W] and [1_W] over ℤ/3 × ℝ ⇉ ℝ are generalized strong bundle isomorphisms with the same /[D]/, different base classes, and [Inv] ≠ [1]. The others are pushforward_inv_eq_pushforward_id |
| V10_61 | narrower | neither | A_narrower | A (universe 0) is only the reduction step GenSBMap.iff_of_isGeneralizedIso: for ANY property Pr of SEP invariant under strong bundle equivalences, a generalized strong bundle isomorphism A → A' gives Pr A ↔ Pr A'. No project theorem says anything about (LR) of strong bundles, because Proposition 10. |
| V10_62 | explicit | equivalent | equivalent | A (universes at 0) has eleven conjuncts: proposition_10_1_9 (an equivalence F gives X.IsLR ↔ Y.IsLR) and ten lemmas of its proof. These are exists_transportChart, TransportChart.bijective_conj, TransportChart.Q_Φ, exists_naturalRep_push/pull, isLR_iff_hasLR, NaturalRep.hasLR_iff_of_equivariant, Natu |
| V10_63 | stronger | equivalent | equivalent | A (universes at 0) has four conjuncts. proposition_10_1_10_one assumes (LR) for X only, and gives a natural representation inside every open O ∋ x with an sc-smooth α_z : F(z) → G(z). proposition_10_1_10_one_of_isLR_right is the same with (LR) for Y. proposition_10_1_10_two gives F.tangent.orbitMap  |
| V10_64 | same | equivalent | equivalent | A (universe 0) has two conjuncts. EPLoc.proposition_10_3_16 says that for a generalized isomorphism f : of X ⟶ of Y, X.X.IsLR ↔ Y.X.IsLR. The general reduction EPLoc.iff_of_isGeneralizedIso says a property of EP invariant under equivalences is invariant under generalized isomorphisms. B is Propositi |
| V10_65 | restated | B false | A_narrower | B is the literal Theorem 10.3.19: (LR) on one side and /f/ = /f'/ make generalized isomorphisms f, f' : X ⟶ Y in EPLoc.{0} equal. B is the project's Theorem_10_3_19.{0} (B_iff_Theorem, up to structure eta), and A is its refutation plus ingredients: not_theorem_10_3_19, theorem_10_3_19_counterexample |
| V10_66 | narrower | equivalent | equivalent | A (universes at 0) has six conjuncts. theorem_10_3_19_of_isEffective assumes Y effective and (LR) on one side, and then equal orbit maps make generalized isomorphisms of X ⟶ of Y equal. Three lemmas of its proof follow: naturallyEquivalent_of_isEffective, eqOn_of_isEffective and eqOn_unit_of_isEffec |
| V10_67 | restated | B false | A_narrower | A has three conjuncts. not_theorem_10_5_7 says the project's transcription Theorem_10_5_7 (universe 0, with the project's EpStrongBundle.IsLR) is false. isLR_z3EpBundle says the trivial bundle ℝ × ℝᵏ → ℝ over ℤ/3 × ℝ ⇉ ℝ (trivial μ) has that (LR). remark_10_5_5 says [W ←1 W →Inv W] and [1_W] are gen |
| V10_68 | explicit | A ⇒ B only | A_stronger | A (universes at 0) is about the project's specific construction W ×_{W'} W'' := wfpSEP hΦ Ψ = πZ*W'', with ΠZ = projZ and ΠX = projX. Its conjuncts: theorem_10_2_2 (projZ is a strong bundle equivalence, projX ≫ Φ ≃ projZ ≫ Ψ, the legs cover πX and πZ); theorem_10_2_2_right; nonempty_wfpSEP; two gene |
| V10_69 | explicit | equivalent | equivalent | A (universes at 0) has four conjuncts: lemma_10_3_4 and its alias Equiv.trans (transitivity of 'having a common refinement' on SDiagram A A'), equivalence_equiv (it is an equivalence relation) and cls_eq_cls_iff ([D] = [D'] in GenSBMap iff D ≈ D'). B says, for all A A' : SEP.{0}, that SDiagram.Equiv |
| V10_70 | explicit | A ⇒ B only | A_stronger | A (universes at 0) has ten conjuncts. Five are class-level facts about the composite D.comp E (the weak-fibred-product diagram): Equiv.comp, equiv_assoc, equiv_comp_id, equiv_id_comp, and cls_comp_cls (rfl). Two are refinement-level: IsRefinement.comp (refinements of the factors give a refinement of |
| V10_71 | narrower | equivalent | equivalent | A (universes at 0) has seven conjuncts: SEPLoc.theorem_10_3_10 ([D] is an isomorphism of SEP(F⁻¹) when Ψ is a strong bundle equivalence, and every two-sided inverse is [D.symm hΨ]), isIso_of_isGeneralizedIso, inv_homMk, SDiagram.equiv_comp_symm / equiv_symm_comp (D ∘ D⁻¹ ≈ 1, D⁻¹ ∘ D ≈ 1), isEquival |
| V11_1 | same | equivalent | equivalent | UNIVERSES: the project's tangent functor lives on EP.{max u 1}, and B is stated on EP.{1}/EPLoc.{1} with EP.tangent.{0}. So A's theorems on EP(E⁻¹) are taken at u = 0 (objects in EP.{1}). The helper lemmas on unbundled ep-groupoids (tangent_comp, tangent_id, projLeft/Right_comp_wfpLift) are taken at |
| V11_2 | same | equivalent | equivalent | A (universes at 0, matching B's EP.{0}) has four conjuncts. proposition_11_1_2: for a generalized isomorphism f and /f/(/x/) = /y/, d_X(x₀) = d_Y(y₀) for all x₀ ∈ /x/, y₀ ∈ /y/, plus d_{/X/}(/x/) = d_{/Y/}(/y/). It also has the orbit-map forms d_{/Y/} ∘ /f/ = d_{/X/} for a generalized isomorphism, f |
| V11_3 | restated | B ⇒ A only | equivalent | The item is a definition. A (universes at 0) is the conjunction of five lemmas about the project's notions: faceMor_eq, isSaturated_faceObj, isOrbitFace_iff_isFaceIn, orbitFacesThrough_eq, and isEpFaceStructured_iff. B says the project's IsOrbitFace, faceObj/faceMor, IsEpFace, IsEpFaceStructured and |
| V11_4 | stronger | A ⇒ B only | A_stronger | A (no universe parameters except isHomeomorph_π_trivial, at 0) is example_11_1_4 for every sc-Banach space W, with C = [0,∞)² ⊕ W: trivial C is face structured, and ℤ/2 ⋉ C (swapEpGroupoid W) is weakly face structured and not face structured. It also has five auxiliary lemmas: every [0,∞)ⁿ ⊕ W is fa |
| V11_5 | same | equivalent | equivalent | A (universes at 0, matching B's EP.{0}) has twelve conjuncts. First, remark_11_1_5. For an equivalence Φ: θ ↦ /Φ/(θ) is a bijection of the faces of /X/ onto those of /Y/, Φ_*(X_θ) = saturation(Φ(X_θ)) = Y_{/Φ/(θ)}, and Φ^*(Y_θ') = X_{/Φ/⁻¹(θ')}. For [d] with Φ an equivalence: [d]_* = Ψ_* ∘ Φ^*, [d]^ |
| V11_6 | narrower | A ⇒ B only | A_stronger | A (universes at 0) is proposition_11_1_6 plus four helpers: isOrbitFace_faceMap/faceComap, faceComap_faceMap, faceMap_faceComap. For any generalized isomorphism f, A says three things. θ ↦ /f/(θ) is a bijection of the faces of /X/ onto those of /Y/, with inverse θ' ↦ /f/⁻¹(θ'). Y_{f_*θ} = π⁻¹(/f/(θ) |
| V11_7 | same | equivalent | A_stronger | A (universes at 0) has four conjuncts. remark_11_1_7 is the text's remark: for a generalized isomorphism f : X → Y, X.IsEpFaceStructured ↔ Y.IsEpFaceStructured, where the project's notion includes tameness. The other three state the invariance of tameness alone along an equivalence F : X → Y, in bot |
| V11_8 | narrower | A ⇒ B only | equivalent | A (proposition_11_1_8, universe 0) concludes faceMap f = faceMap g, faceComap f = faceComap g, and, for every θ ⊆ /X/, MapsTo /f/ θ (faceMap g θ) and EqOn /f/ /g/ θ. The project defines faceMap f θ := /f/(θ) and faceComap f θ' := /f/⁻¹(θ'), so A's conclusion is immediate from /f/ = /g/. Its face-str |
| V11_14 | restated | A ⇒ B only | equivalent | This is a definition item. pullbackTheta and pushforwardTheta are vocabulary; A (universes at 0) is the conjunction of four side theorems about them: pullbackTheta_apply (rfl), pushforwardTheta_of_not_exists and its contrapositive (the value 0 where no F(x) is isomorphic to y), and pushforwardTheta_ |
| V11_15 | stronger | A ⇒ B only | A_stronger | A (universes at 0) states Lemma 11.3.2 under weaker hypotheses, as the item's title says. Well-definedness, functoriality of F_*Θ and F^*F_*Θ = Θ need only fullness of F; F_*F^*Θ' = Θ' needs only essential surjectivity; invariance of F_* under natural equivalence needs fullness of F and G, and invar |
| V11_16 | stronger | equivalent | A_stronger | A (universes at 0) has nineteen conjuncts on the project's f_* = Φ_*F^* (Diagram/EPLoc.pushTheta) and f^* = F_*Φ^* (pullTheta), stated for every functor Θ to ℚ of any sign. They cover: independence of the representative, for generalized isomorphisms (push) and for all generalized maps (pull); the re |
| V11_17 | explicit | A ⇒ B only | A_stronger | A (universes at 0; the three Part I lemmas have two universe parameters, both at 0) is the 23 project lemmas for an equivalence F: (1)-(6) of Theorem 11.3.3 for F_*, F^*, the orbit-set identities, exists_localBranchingStructure_pushforwardTheta (only ∃ B' preserving dimension) and general facts abou |
| V11_18 | restated | A ⇒ B only | A_stronger | A (universes at 0, X Y : EP.{0}) is theorem_11_3_3_one…six for EPLoc.pushTheta/pullTheta f (computed on the chosen representative rep f), isNDimensional_push/pullTheta, orbitSupp_pushTheta and the counterexample not_proposition_9_1_11_rn. B states (1)–(6) for every representative d of a generalized  |
| V11_20 | restated | A ⇒ B only | A_stronger | A (universes at 0) is twenty lemmas on the section maps F_*, F^* of Gr̂ (11.8), (11.9) and f_* = G_*F^*, f^* = F_*G^*. B states (11.8) for every choice of (x, ψ), (11.9) literally, F_*, F^* : Γ → Γ for an equivalence, and, on every choice of representatives of generalized isomorphisms, well-definedn |
| V11_21 | explicit | neither | incomparable | A (universes at 0; two Part I lemmas with two universe parameters, both at 0) proves the orientation transport (isOrientation_push/pullSection for equivalences, theorem_11_3_5_push/pull for generalized isomorphisms) only under HasIndependentTangentSums Θ (resp. Θ'), Theorem 9.2.1 (1)'s independence  |
| V11_22 | restated | neither | incomparable | A (universes at 0, EP.{0}) is push_comp, pull_comp and pull_push for the project's OrientedBranched, which carries HasIndependentTangentSums Θ (Theorem 9.2.1 (1)'s independence) as a field, plus EPLoc.pushTheta_pullTheta (any functorial Θ') and EPLoc.pushSection_pullSection (any T' ∈ Γ). B is about  |
| V11_23 | explicit | neither | incomparable | Universes: B's statement is in universe 1 (X Y : EP.{1}; the tangent ep-groupoid and Diagram.tangent exist only on EP.{max u 1}), so A is instantiated to match: tangentFunctor_map_eq and theorem_11_3_7_push/pull at .{0} (EP.{max 0 1} = EP.{1}), the Type u / EP.{u} lemmas (EpFunctor.*, LocalBranching |
| V11_24 | explicit | B ⇒ A only | A_narrower | A (universes at 0; the two M-polyfold lemmas at .{0,0}) is the conjunction of eight theorems: three local sc-diffeomorphism lemmas (tangent-reducedness and 'f(a) ∈ ∂f(M) iff a ∈ ∂M'), the local step boundaryTheta_apply_of_isScDiffeoOn, (11.11) for an equivalence (push, pull) and (11.11) for a genera |
| V11_25 | narrower | neither | incomparable | A (universes at 0) is isBoundaryTransfer_id, push/pullSection_boundaryLift along an equivalence and theorem_11_3_9_push/pull on a representative X ←F A →Φ Y. These assume HasIndependentTangentSums and boundary operations bd, bdA, bd' on X, d.A, Y satisfying IsBoundaryTransfer along TF(a)⁻¹ and Tψ∘TΦ |
| V11_30 | narrower | neither | incomparable | A (universe 0) is proposition_11_5_1 plus 19 supporting lemmas on pullNorm, oneOrbitMap, oneToOrbit, oneMap and IsOneInvariant. proposition_11_5_1 gives independence of the representative, the formula N'(Ψ(e'')), continuity and condition (3) for auxiliary norms, inverses on invariant functions, and  |
| V11_31 | narrower | neither | incomparable | A (universes at 0, α : Type) has eight lemmas about functors Λ : W → α (IsWFunctor, Λ(μ(φ,w)) = Λ(w)): pushMult_eq (independence of the choices), lemma_11_5_2 (Φ_*Λ is a functor), the inverses, eq_of_π_eq, π_obj_choose, IsWFunctor.pullMult and isWFunctor_const. There is no local section structure. B |
| V11_32 | narrower | neither | incomparable | A (universes at 0, α : Type) is proposition_11_5_3, for functors W → ℚ≥0, plus eight SDiagram lemmas for functors into an arbitrary α. Together they give push/pull formulas, functoriality, inverses and orbit-map dependence. None of A mentions local sc⁺-section structures. B, for sc⁺-multisections Λ  |
| V11_33 | same | equivalent | equivalent | A (universes at 0) is the conjunction of six theorems: lemma_11_6_1 (on morphisms F is surjective and a local sc-diffeomorphism) and five lemmas about the chosen lift α⁻¹(φ, y) = IsProperCovering.lift (mor_lift, src_lift, eq_lift, obj_tgt_lift) and existsUnique_lift_tgt (unique lifts with prescribed |
| V11_34 | restated | equivalent | equivalent | A (universes at 0) has six theorems: lemma_11_6_2 (the action formula g • a = t(lift), and toTranslation : Y(x) ⥤ G_x ⋉ Y_x is the identity on objects and α on morphisms, bijective on objects, full, faithful, an equivalence), fiberSMul_val_of and smul_val_of (g • y = t(ψ) for any lift ψ), bijective_ |
| V11_35 | same | equivalent | equivalent | A (universes at 0) has five theorems: lemma_11_6_3 (B_φ = transportFiber φ is bijective and equivariant along conjIsotropy φ, and φ̃ = translationMap φ is bijective on objects, full, faithful, an equivalence), transportFiber_val_of, transportFiber_inv_transportFiber, bijective_transportFiber and tra |
| V11_36 | stronger | equivalent | equivalent | This is a definition item. A (universes at 0) has seven theorems: ProperCoveringHom.ext, mapsTo_fiber, IsEquivalence.id, IsEquivalence.comp, isFiberBijective_of_isEquivalence, isEquivalence_iff and the witness isEquivalence_pairToPointCovering. B says that ProperCoveringHom F F' is exactly the set o |
| V11_37 | same | B ⇒ A only | equivalent | This is a definition item. A (universes at 0) has five theorems about the definition NatTrans: naturality_F (the diagram on p. 555), naturallyEquivalent_equivalence, NaturallyEquivalent.comp_left/comp_right, and the witness naturallyEquivalent_pairToPointCovering. B says that Γ.NatTrans Γ' is exactl |
| V11_38 | stronger | A ⇒ B only | A_stronger | A (universes at 0) is the twelve step lemmas of Theorem 11.6.6 (1): well-definedness of H (mor_conj, hMor_src/tgt), steps (A)-(C) (surjective_hObj, isLocalScDiffeo_hObj, isScDiffeo_fibredMap_hFunctor, finite_fiber_hObj, isProperMap_hObj), three general lemmas (IsScDiffeoOn.restrictTarget, IsLocalScD |
| V11_39 | same | equivalent | equivalent | A (universes at 0) has five conjuncts: theorem_11_6_6 (all claims, for H = hFunctor, (π_Y,π_X) = projLeftHom, (π_Y'',π_X'') = projRightHom), the witnesses theorem_11_6_6_pairToPoint and nonempty_fiber_id, Chapter 10's isEquivalence_projRight, and Chapter 7's IsLocalScDiffeo.isTame. B states the same |
| V11_40 | same | neither | equivalent | This is a definition item: PC, PC.equivalences, PC.fibred/fibredFst/fibredSnd, PC.Diagram, Diagram.CommonRefinement, HasCommonRefinement and the example objects and diagrams are vocabulary. A (universe 0) is the conjunction of three side theorems: ProperCoveringHom.comp_assoc and the witnesses equiv |
| V11_41 | same | equivalent | equivalent | A (universe 0) has four conjuncts: proposition_11_6_8 (transitivity of HasCommonRefinement), hasCommonRefinement_equivalence (it is an equivalence relation), and the witnesses diagram ≈ diagram' and diagram ≈ diagram. B is transitivity, using B's own reading of Definition 11.6.7. The glue is hasComm |
