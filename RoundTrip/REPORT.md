# Round-trip audit of Part I — report

Status 2026-11-01 (the audit); the lists of what the project lacks updated 2026-11-02; refreshed against
HEAD (commit 12924a4) on 2026-11-02, see "Refreshed on 2026-11-02" below. Method and how to run:
`README.md`. Layer 1 (statements).

## Coverage

**All 269 items** of the comparison that are not labelled *extra* (Chapter 1: 31, Chapter 2: 58,
Chapter 3: 95, Chapter 4: 43, Chapter 5: 42). Every item has a blind statement
(`Blind/<ID>.lean`) and a prover record (`Items/<ID>.lean`, `Items/<ID>.json`); all files compile
against HEAD (commit 12924a4, recompiled 2026-11-02), no `sorry`, and every proved direction passes
`#rt_check` (or `#rt_check_soft`, or a documented `A'`-factoring, noted in the item's JSON; see
"Harness" below). 134 Opus agents (blind batches of
about 9 items, prover batches of 5–8), four at a time; the refresh of 82 items: nine more prover
agents, then three blind and three prover agents for seven second blind statements, three Lean
processes at a time.

## Results

Proved directions (vacuous directions not counted), by chapter:

| | equivalent | A ⇒ B only | B ⇒ A only | neither | B false | n |
|---|---|---|---|---|---|---|
| V1 | 15 | 13 | 0 | 1 | 2 | 31 |
| V2 | 31 | 12 | 6 | 8 | 1 | 58 |
| V3 | 1 | 54 | 0 | 36 | 4 | 95 |
| V4 | 16 | 14 | 1 | 11 | 1 | 43 |
| V5 | 7 | 13 | 4 | 17 | 1 | 42 |

Proved directions by verdict:

| | equivalent | A ⇒ B only | B ⇒ A only | neither | B false | n |
|---|---|---|---|---|---|---|
| same | 24 | 19 | 6 | 13 | 1 | 63 |
| explicit | 12 | 21 | 1 | 9 | 0 | 43 |
| narrower | 2 | 6 | 3 | 13 | 3 | 27 |
| restated | 27 | 32 | 1 | 32 | 1 | 93 |
| stronger | 5 | 28 | 0 | 6 | 4 | 43 |

Provers' judgement of content, by verdict:

| | equivalent | A_stronger | A_narrower | incomparable | n |
|---|---|---|---|---|---|
| same | 37 | 19 | 3 | 4 | 63 |
| explicit | 14 | 22 | 1 | 6 | 43 |
| narrower | 2 | 10 | 5 | 10 | 27 |
| restated | 40 | 35 | 4 | 14 | 93 |
| stronger | 5 | 29 | 2 | 7 | 43 |

Against the verdict: {'match': 125, 'mismatch': 127, 'partial': 17}

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
  tame or not (`Polyfold.remark_2_28_isPartialQuadrant`, `Chapter2/PartialConeQuadrant.lean`,
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
  (`theorem_3_12`, `theorem_3_15`, `theorem_3_18`, `proposition_3_52`, `theorem_3_19`,
  `theorem_3_23`, `theorem_3_54`, `theorem_3_56`, `theorem_3_57`, Chapter 5) carry the text's
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
  (classical) statements (added later: `proposition_3_10_level`, `proposition_3_52_sc`,
  `theorem_3_19_linearization_sc`, `StrongBundle.linAt_isScFredholm` in every chart,
  `theorem_3_54_index_locally_constant_general` under tame germ data and bump functions; see
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
  (both added on 2026-11-02: `remark_4_3_example`; `TrivialBundle.not_completeSpace_allowableSections`,
  with the correction that "not complete" needs a hypothesis; see below; since the refresh `A ⇒ B`
  is proved for V1.13, V1.34, V4.6, V5.21).
* Proved in the audit and missing in the project (all added later: Remark 5.12, Lemma 3.9 and
  Lemma 3.81 in commit f063505 — `remark_5_12_of_isScFredholmSection`,
  `IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le`, `Radii.norm_τ_sub_le_global`; the rest as
  marked): the closedness of the solution set in Remark 5.12
  (V5.22, flagged in the project's docstring); Lemma 3.9 with level-`m` smallness (V3.11; the
  docstring says level-1 smallness is needed — it is not); the Lipschitz estimate of Lemma 3.81 on
  all of `V₀` (V3.66; the docstring says only near `k₀`); Corollary 3.34's single germ for all `k`
  (V3.31, V3.32) (added later: `corollary_3_34_isScSmoothGerm`, `theorem_3_35_isScSmoothGerm`,
  `theorem_3_35_of_isSc0ContractionGerm`, `isSckGerm_of_levels`, `Chapter3/GermIFTSmooth.lean`);
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
  `m` (`proposition_3_10_level`; V3.12's clause (ii), checked against the blind statement in a
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
* Since phase 2 (above) these files hold the whole-chart forms (`proposition_3_52_sc_wholeChart`,
  `StrongBundle.linAt_isScFredholm_wholeChart`, …); the names cited here that take sc-Fredholm
  germ data denote the germ-reading forms in the `…G.lean` files beside them (`FredholmGermLinearizationScG.lean`,
  `LinearizationChartsScG.lean`, `IndexLocallyConstantG.lean`; Findings Ch. 3 items 289–290,
  314–315, 331).

### Added on 2026-11-02 (commit 08c08c6; the fourth addendum of the comparison)

* **Corollary 5.8** (V5.13, V5.14; gap G.41; Findings Ch. 5 items 140–146): the shifted strong
  bundle `P¹ : Y¹ → X¹` (`StrongBundle.shift`: total space `Y_{1,1}`, the index raises of the strong
  bundle charts as atlas; `Chapter5/StrongBundleShift.lean`); `f¹` is an sc-Fredholm section of it
  with compact solution set (`corollary_5_8`), `f²` of `P² = (P¹)¹` (`corollary_5_8_two`), every
  fixed `i` by iteration; the filler condition (3) on level `1`, which "it is a priori clear" hides,
  is proved for every datum of Definition 3.11 (`IsFillingGerm.germ_shift`,
  `Chapter5/Corollary58.lean`). No added hypothesis; tameness not used.
* **Definition 6.1 and Proposition 6.2** (V3.98 (a); Findings Ch. 3 items 340–348):
  `StrongBundle.IsIndexAt` (well defined without Proposition 1.10), `proposition_6_2` by the text's
  device, for tame germ data on M-polyfolds admitting bump functions and sc-smooth paths `ℝ → X`
  (`Chapter3/IndexAlongPaths.lean`, `Chapter3/IndexAlongPathsDevice.lean`). Item 243 sharpened: the
  candidate counterexample of items 188, 243 is excluded under tame germ data (item 343).
* **Proposition 6.2 without bump functions** (V3.98; commit 12924a4; Findings Ch. 3 items 349,
  360–367): restriction of M-polyfolds and strong bundles to open sets (`StrongBundle.restrictOpen`),
  Definition 6.1 with the text's locally defined sections (`StrongBundle.IsIndexAtLocal`, agreeing
  with `IsIndexAt` under bump functions, `isIndexAtLocal_iff_isIndexAt`), the index locally constant
  along the zero set for tame germ data (`index_locally_constant_tame`) and Proposition 6.2 with the
  text's hypotheses (`proposition_6_2_local`; `Chapter3/IndexAlongPathsLocal.lean`).
* **Remark 4.3's example** (V4.6; gap G.31; Findings Ch. 4 items 140–146): `remark_4_3_example`, an
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
  now proved only by proving B outright), V3.12 (`proposition_3_10_full`), V3.15 (the text's germ
  notion implies the project's: shrinking the chart into `U₀`, `Ψ` and the basic germ restricted),
  V3.46 and V3.96 (`StrongBundle.linAt_isScFredholm` in every chart), V3.92 (non-centred charts by
  `StrongBundleChart.recentre`), V4.6 (`remark_4_3_retract_example`), V5.21
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
  (`theorem_3_54_two`, `TangentGermChart.shrink`, `theorem_3_27`). V3.100: at `d_X(x) = 0` (and for
  `∂X = ∅`) good position ⟺ `f'(x)` onto, by `isGoodPositionGermSc_iff` and A. B ⇒ A fails in all four:
  A needs no tame bundle and contains chart-level lemmas.
* V5.13, V5.14: the blind statements build `P^i` by iterating the project's `StrongBundle.shift` and
  `sectionShift` (so a wrong shift construction would not be caught here); A ⇒ B for every `i` by
  induction over `corollary_5_8` / `corollary_5_8_isScFredholmSection` on `P^i` (V5.14 with
  `#rt_check_soft`: `StrongBundleChart.Compatible.shift` is reached only through the proof fields of
  `StrongBundle.shiftAtlas`). B ⇒ A fails: A holds without tameness and has side lemmas.
* V3.98 (its row now also cites `proposition_6_2_local`, `IsIndexAtLocal`,
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

### Harness

* **Banned theorems inside definitions.** When a definition in A's statement calls one of the item's
  own theorems in its body (`IsScSplitting.scProj`, `subChart`, `subPolyfold`, `Radii.τ`, the
  instance of `proposition_2_54`), every proof mentioning A fails `#rt_check`. The provers factored
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
| V1_5 | same | equivalent | equivalent | Same notions on both sides (the project's IsScSubspace, smooth, IsScSplitting; finite-dimensionality as an instance in A, an explicit hypothesis in B). The only difference is packaging of the second sentence: A's proposition_1_6 assumes F ≤ E_∞, B's assumes F is an sc-subspace; the shared first conj |
| V1_6 | stronger | A ⇒ B only | A_stronger | The conclusions agree: A's 'sc-Banach Q with a level-wise surjective sc-operator q : E → Q, ker q_m = A_m' gives B's level-wise isomorphisms Q_m ≃L E_m/A_m intertwining the inclusions (the induced maps E_m/A_m → Q_m are continuous bijections of Banach spaces, inverted by the open mapping theorem), a |
| V1_7 | restated | B false | A_narrower | The literal B is false (not_B proved): its conjunct 'F = C ⊕ T(E_m)' read inside F₀ forces, for T = id, every inclusion E_m → E₀ to be onto (B_implies_toBase_surjective), hence the compact inclusion E₁ → E₀ to be invertible and every sc-Banach space to be finite-dimensional (B_implies_finiteDimensio |
| V1_8 | same | equivalent | equivalent | Same statement for the core: proposition_1_9 quantifies over the data s : ScFredholmSplitting T, B over the proposition IsScFredholmB T, an existential over the same K, X, C, Y with exactly the seven fields of ScFredholmSplitting (isScFredholmB_iff repackages them); IsScFredholm.isRegularizing is th |
| V1_9 | same | A ⇒ B only | A_stronger | B's hand-written IsScFredholmB has exactly the fields of the project's ScFredholmSplitting (repackaged by isScFredholmB_iff), and T.add S.toScOperator is definitionally T + S.toScOperator, so proposition_1_10 is literally B (A_to_B). B still gives proposition_1_10 and the bootstrap lemma ScPlus.regu |
| V1_10 | same | equivalent | equivalent | The project's definitions agree with the text's (B is true): IsPartialQuadrant writes C = T₀⁻¹([0,∞)ⁿ ⊕ W₀) where the text writes T₀(C) = [0,∞)ⁿ ⊕ W₀ plus 'C closed convex' — equivalent because T₀ is bijective, and closedness/convexity are exactly A's IsPartialQuadrant.isClosed/.convex (used in A_to |
| V1_11 | restated | A ⇒ B only | equivalent | The project's IsSc0 is the text's sc⁰ (B is true). The only difference is the target: the project's IsSc0 E F U f asks f(U_m) ⊆ F_m with levelMap f m continuous on U_m, the text asks f(U_m) ⊆ U'_m; for f(U) ⊆ U' the extra U'_m-clause is exactly A's IsSc0.levelMap_mapsTo (used in A_to_B), and the bli |
| V1_12 | same | neither | incomparable | Both directions hold only vacuously (uses_hypothesis false for both), so the content comparison is what matters. The notions agree (tanSpace E = E.tangent = E¹ ⊕ E and tanSet E A = E.tangentSet A, both rfl), but A does not contain the text's claim that (TU, TC, TE) is again a tuple: the project neve |
| V1_13 | explicit | equivalent | equivalent | Definition 1.14 itself is formalized identically on both sides (Sc1With/Sc1/tanMap/tanSet are IsSc1With/IsSc1/tangentMapWith/tangentSet, rfl or field-for-field); B is the three remarks after it. A_to_B: remark (a) ('x ↦ Df(x) is in general not operator-norm continuous') is now A's exists_isSc1_not_c |
| V1_14 | same | A ⇒ B only | equivalent | The blind notions agree with the project's on tuples: tanSet/tanMap/Sc1With are literally tangentSet/tangentMapWith/IsSc1With, and the blind SckB (k+1) ('sc¹ with SOME derivative family D and Tf = tanMap f D sc^k') equals the project's IsSck (k+1) ('sc¹ with Tf built from the CHOSEN scDeriv sc^k') o |
| V1_15 | restated | A ⇒ B only | A_stronger | Same notions (B's levelTo f (m+1) m is levelMap f m ∘ ι_m by rfl; IsSc0/IsSc1/IsSc1With/IsScOperator/E_∞ are the project's), and B's (1)–(2) (C¹ with fderivWithin, continuity of df, an extension family Dl) match the project's IsSc1Levels on domains with unique differentiability, so A ⇒ B is glue aro |
| V1_16 | same | A ⇒ B only | A_stronger | Same notions on both sides (B's levelTo f 1 1 is levelMap f 1 by rfl; U¹ = E.lvlSet U 1 in E.shift; sc^k = IsSck), so A ⇒ B is IsSck.shift on the sc-domain U (IsRelOpenInQuadrant.isScDomain) plus IsSc0.levelMap_mapsTo for f(U¹) ⊆ V¹. B ⇒ A fails for a genuine reason: A's conjuncts are stated for arb |
| V1_17 | same | A ⇒ B only | A_stronger | Same notions on both sides (the project's IsSck, Mathlib ContDiffOn on U_{m+l}); B's levelTo f (m+l) m is definitionally invFun ι_m ∘ f ∘ ι_{m+l} = levelMap f m ∘ inclK m l, so A ⇒ B is glue plus IsRelOpenInQuadrant.isScDomain. B ⇒ A fails for a genuine reason: every conjunct of A is stated for an a |
| V1_18 | same | A ⇒ B only | A_stronger | Same notions: B's levelTo f (m+l) m equals levelMap f m ∘ inclK m l (pointwise via toBase_inclK), B's membership hypothesis at l = 0 plus C¹ on U_m is IsSc0, and sc^{k+1} is IsSck (k+1); so A ⇒ B is proposition_1_19_text (the text's hypothesis, not the stronger C^{k+1}-on-every-level one) on the sc- |
| V1_19 | same | A ⇒ B only | A_stronger | Same notions (constant sc-structure on the target, f ∘ E.toBase l on U_l, Mathlib ContDiffOn, IsSck), so A ⇒ B is corollary_1_20_text with V = Fin N → ℝ on the sc-domain U. B ⇒ A fails for a genuine reason: every conjunct of A is stated for an arbitrary IsScDomain U (e.g. a closed disc, not relative |
| V1_20 | same | A ⇒ B only | A_stronger | Same notions (IsSc1, tangentMap with the chosen scDeriv, tangentSet); A ⇒ B is theorem_1_21 plus the trivial (g∘f)(U) ⊆ W, and conversely B gives theorem_1_21 exactly (B_to_theorem_1_21, rt_check OK, taking W = Q = G₀), so on the text's statement the two agree. B ⇒ A fails because A contains strictl |
| V1_21 | same | equivalent | equivalent | The blind definitions coincide with the project's definitionally: Presentation E C is the data of IsPartialQuadrant E C ({p / ∀ i, 0 ≤ p.1 i} is quadrant n W 0 by rfl), degWith T x is degIndexWith T x = quadrantDeg (T 0 x) by rfl, and degC / degIndex both evaluate the count with a chosen presentatio |
| V1_22 | same | equivalent | equivalent | lemma_1_24 is B verbatim (same degIndexWith, same presentations T, T' with possibly different n, W, same quantification over x ∈ C). The other two conjuncts of A follow from B: lemma_1_24_dim by B at x = T⁻¹(0) (index n vs n'), and the core quadrantDeg_eq_of_equiv (an arbitrary level-0 linear equiva |
| V1_23 | stronger | A ⇒ B only | A_stronger | A ⇒ B: theorem_1_25 applied to the shrunken domains O∩U, O'∩U' (still relatively open in C, C'), with sc-smooth ⇒ sc¹, then degIndex_eq (Lemma 1.24, outside this item) turns the project's choice-based degIndex into degIndexWith for B's arbitrary presentations T, T'. B ⇒ A is not derivable: theorem_1 |
| V1_29 | stronger | B false | incomparable | B is false (not_B, as its author predicted): its clause 'F = C ⊕ T(E_m)' read literally in F₀ forces, for the identity operator with K = C = 0, every inclusion E_m → E₀ to be onto (B_surj); this fails for the sc-Banach space Model.G (ℓ² on every level, inclusions the compact injective diagonal opera |
| V1_30 | stronger | equivalent | A_stronger | B is the text's Proposition 1.10 (T + S is sc-Fredholm, index not mentioned); A is the project's index statement: ind(T+S) = ind T, and every (T+S)_m is Fredholm of index ind T. A_to_B genuinely uses A's level conjunct and does not use proposition_1_10. If all level maps of T' are Fredholm with the  |
| V1_31 | restated | equivalent | equivalent | B's hand-written IsScStructure (complete levels, injective compact inclusions, E_inf dense in each level) is literally the project's ScScale + dense_smooth (glue: toScBanach / isScStructure_of_scBanach, with inclTo0 = toBase by induction). Uniqueness: A's toBase_bijective_of_finiteDimensional gives  |
| V1_32 | explicit | equivalent | equivalent | Common content: an idempotent continuous on every level gives the sc-splitting E = P(E) + (1-P)(E). A_to_B gets it from isScSplitting_of_idem, applied to the ScOperator built from B's level maps; this uses ker P = (1-P)(E). B's first conjunct (the project's IsScSplitting, algebraic IsCompl on each l |
| V1_33 | same | equivalent | equivalent | Both assume A is an sc-subspace: B's hand-written IsScSubspaceText (closed, complete levels, compact inclusions, A_inf dense in each A_m) is equivalent to the project's IsScSubspace (closed + density), the extra fields being automatic (glue lemmas isScSubspace_of_text / text_of_isScSubspace). The co |
| V1_34 | restated | A ⇒ B only | A_stronger | Both sides share the claim that x ↦ Df(x) is continuous on U₁ for the compact-open topology: A's deriv_uniformOnCompact gives B's first conjunct via Mathlib (compact-open = uniform convergence on compacts). B's second conjunct (some sc¹ map has Df not norm-continuous) is now A's exists_isSc1_not_con |
| V1_35 | explicit | A ⇒ B only | A_stronger | A is stated only for the constant structures const V, const W, while B allows any ScBanach E, F with E_0, F_0 finite-dimensional. A_to_B bridges this with the sc-isomorphisms E = const E_0 and F = const F_0 (isoConstOfFiniteDimensional from V1_31, the identity on level 0) and the chain rule theorem_ |
| V1_36 | same | equivalent | equivalent | B is the conjunction of IsRelOpenInQuadrant.tangentSet and IsRelOpenInQuadrant.shift, word for word (same project notions tangent, tangentSet, shift, lvlSet, IsRelOpenInQuadrant), so A_to_B projects two conjuncts. B_to_A gets the two IsRelOpenInQuadrant statements from B directly and the two IsParti |
| V2_1 | same | equivalent | equivalent | B's definition IsScRetractionB (relatively open U in a partial quadrant, r(U) ⊆ U, IsScSmooth U r, r ∘ r = r on U) is exactly the field list of the project's ScRetraction, so the definitional conjunct is structure packing (no universe parameters; ScBanach lives in Type). The projection claim for x ∈ |
| V2_2 | same | B ⇒ A only | equivalent | Definition item. B's IsScRetractB (∃ U r, r an sc-smooth retraction on U relatively open in the partial quadrant C, O = r(U)) is the project's IsScRetract (∃ R : ScRetraction E C, R.retract = O) unfolded, and every LocalModel carries IsScRetract, so B is provable outright by structure packing; A_to_ |
| V2_3 | same | equivalent | equivalent | Same notions on both sides: B writes out ScRetraction.tangent (tangentMap R.U R '' E.tangentSet R.U), so the main conjunct proposition_2_4 is B verbatim (A_to_B and the first conjunct of B_to_A are rfl-level). The other conjuncts of A are proof-internal helpers: r' ∘ r = r on U when r(U) ⊆ r'(U'), t |
| V2_4 | same | equivalent | equivalent | Same notions. B's explicit TOB R = {(r(x), Dr(x)h) : x ∈ U₁, h ∈ E} (r(x) as the level-1 point over r(ι₁x₁)) equals the project's R.tangent = Tr(TU) by mem_tangent_iff_exists plus levelMap_eq_of_toBase_eq / IsSc0.toBase_levelMap; then 'TO := Tr(TU) for any r onto O' is retractTangent_eq, the E- and  |
| V2_5 | explicit | equivalent | equivalent | Same notions on both sides (ScRetraction, IsScSmooth on r.U of f ∘ r, tangentMap, TO = Tr(TU) = ScRetraction.tangent). A ⇒ B: (1) is proposition_2_6_1 in both directions; (2)/(3) are proposition_2_6_2/_3 after identifying B's Tρ(TU_ρ) for an arbitrary retraction ρ onto O with r.tangent via Propositi |
| V2_6 | restated | equivalent | equivalent | Same notions. B reads Definition 2.7 existentially (f(O) ⊆ O' and f ∘ r sc-smooth for SOME r onto O); the project's IsScSmoothRetractMap quantifies over EVERY r, and isScSmoothRetractMap_iff_exists (Proposition 2.6 (1)) is exactly B's first conjunct for a retract O. With B's explicit TOB R identifie |
| V2_7 | explicit | equivalent | equivalent | Same notions on both sides (ScRetraction, IsScRetract, tangentMap of Definition 1.14, TO = Tr(TU)). B's hypothesis 'f∘r sc-smooth for SOME retraction' is the project's IsScSmoothRetractMap ('for EVERY retraction') by Proposition 2.6(1) (isScSmoothRetractMap_iff_exists), and the project's retractTang |
| V2_8 | restated | equivalent | equivalent | Same notions: B's TEB/TCB/TUB are E.tangent, E.tangentSet C, E.tangentSet U definitionally, and B's explicit TOB R equals Tr(TU) = retractTangent E C O (glue + retractTangent_eq). B's 'TO is a retract', 'Tf is a morphism TO → TO'' (Tf(TO) ⊆ TO' and Tf ∘ ρ sc-smooth for every ρ onto TO), 'T(1) = 1' a |
| V2_9 | restated | equivalent | equivalent | Same notions (IsScRetract, open subset of O read as O ∩ W with W open in E₀, same C and E). (1) is proposition_2_10_1 verbatim. For (2), the project states it for any retract V (not only an open subset of a retract O) with the 'every retraction' notion IsScSmoothRetractMap; B takes V = O ∩ W and the |
| V2_10 | restated | equivalent | equivalent | Same notions. A project MChart is exactly a text chart (open V, homeomorphism V ≃ₜ O onto a LocalModel), and every text chart around a point x₀ is a project chart with the same model and source (glue: chartHomeo / mkChart, x₀ as junk value of the total inverse; only the chart on an empty domain in a |
| V2_11 | same | equivalent | equivalent | Same notions. The project's MAtlas asks compatibility for ALL pairs of charts (including φ with itself) where B's IsAtlasB uses Set.Pairwise (distinct pairs); the diagonal is MChart.compatible_self (item V2_10, not banned), so the chart sets of project atlases are exactly B's atlases. MAtlas.Equiv i |
| V2_12 | restated | equivalent | equivalent | Same notions. MPolyfold X (for Hausdorff paracompact X) is one atlas standing for its class, and MPolyfold.IsChart (compatible with every chart of the atlas) is exactly 'lies in some atlas of the class' (B (c)): → by adjoining φ to P.atlas, ← by A's isChart_congr. B (a), that atlas equivalence is an |
| V2_13 | explicit | equivalent | equivalent | Same notion of sc-smooth map. The project's IsScSmoothMap (continuity as a field + ψ ∘ f ∘ φ⁻¹ sc-smooth on φ(V) for EVERY pair of charts of the maximal atlases and every open V ⊆ dom φ with f(V) ⊆ dom ψ, 'every retraction' Def. 2.7) is equivalent to B's existential reading (around each x SOME chart |
| V2_14 | restated | equivalent | equivalent | Same X_m, X_∞ and topology. P.levelSet m (φ(x) ∈ range ι_m for some chart of the maximal atlas) is B's levelSetB (∃ z ∈ O_m with ι_m z = φ(x)) definitionally since φ(x) ∈ O; chart independence is A's mem_levelSet_iff; X_0 = X, X_{m+1} ⊆ X_m, X_∞ = ⋂ X_m match. The project's generators {x ∈ V / level |
| V2_15 | same | equivalent | equivalent | Identical statements: both say that P.levelIncl m : (X_{m+1}, P.levelTopology (m+1)) → (X_m, P.levelTopology m) is continuous for every M-polyfold P on a Type and every m. The only difference is binder kind (lemma_2_15 takes X implicitly, B explicitly); A is instantiated at universe 0. B reuses the  |
| V2_16 | narrower | B ⇒ A only | A_narrower | B states for EVERY level m that the charts (V_m, φ_m, (O_m, C_m, E^m)) are charts on (X_m, levelTopology m), pairwise compatible, covering; A (and the project) builds charts and the M-polyfold only for m = 1 (levelChart_compatible, shift_isChart). The added mem_shift_levelSet_iff gives (X¹)_m = X_{m |
| V2_17 | explicit | equivalent | equivalent | Same objects on both sides (P.Level m with P.levelTopology m, which is the project's instance; X_∞ = P.SmoothLevel). B gives X_∞ the infimum of the topologies induced by the inclusions X_∞ → X_m; the project's instance is induced from the product ∏ X_m, and the two agree (smoothLevel_topology_eq, re |
| V2_18 | restated | equivalent | equivalent | Definitions agree: the project's tangentSpace E C O x₁ is B's TxOB R x₁ = {h / (x₁,h) ∈ {(r x, Dr(x)h)}} = range Dr(x₁) for every retraction R onto O (TOB R = R.tangent, retractTangent_eq); the fields of TangentPre are exactly B's IsTupleB (levelSetB = levelSet). The two relations point in opposite  |
| V2_19 | narrower | equivalent | equivalent | A (tangentChartMap_mk_self, _injOn, _mk_ofVec, _mk_ofVec_of_mem, universe 0) and B (the project's TX, p, T_xX, TV, Tφ and topology are the text's, T_xX is a vector space with every Tφ linear on it) are interderivable. The project's Tφ = tangentChartMap is [(x,ψ,h)] ↦ T(φ∘ψ⁻¹)(ψ(x),h) (any representa |
| V2_20 | narrower | B ⇒ A only | A_narrower | B's topology τB = generateFrom 𝓑 is the project's instance on TX (tangentBasis = TfamB, via tangentChartMap_mk_self), so B ⇒ A is direct: continuity of p, openness of TV (a member of the basis 𝓑), metrizable and paracompact are read off B. A ⇒ B fails only on B (2) 'p : TX → X_1 is an OPEN map': the |
| V2_21 | narrower | equivalent | equivalent | Same content. B's TV/Tφ/τB/TO/TC are the project's tangentChartSet/tangentChartMap/instance/retractTangent/tangentSet, and B's chart (TV, Tφ, (TO,TC,TE)) is tangentChart hφ α₀ (when TX is empty, TV and TO are both empty). A ⇒ B: formula (5) from tangentChart_overlap and tangentChart_transition (over |
| V2_23 | same | B ⇒ A only | equivalent | Definition item: A is only isSubMPolyfold_univ (X is a sub-M-polyfold of itself, universe 0); the real comparison is P.IsSubMPolyfold vs B's IsSubMPolyfoldB, which are proved equivalent for every A (isSubMPolyfold_iff). Both have the same V, r, r(V) ⊆ V, r∘r = r on V, r(V) = A ∩ V; they differ only  |
| V2_24 | explicit | A ⇒ B only | A_stronger | A ⇒ B: Q := subPolyfold hA; B (1) is A's subPolyfold_inclusion_isScSmooth plus IsEmbedding.subtypeVal (subspace topology on both sides); B's (V, r) is exactly a SubData, and A's subPolyfold_retraction_isScSmooth for the project's i⁻¹∘r (retractInto, junk value a₀ off V) transfers to every g agreeing |
| V2_25 | narrower | neither | A_stronger | A is the text's proof in coordinates (compRetraction_retract, proposition_2_21_3/4): for ANY sc-retraction R with retract O and ANY sc-smooth idempotent s of O, at a ∈ s(O)₁ (smooth for (3)), T_aO = Dr(a)E, T_a s(O) = Dt(a)E (t = s ∘ r), the explicit sc-complement (Dr(a) − Dt(a))E levelwise, s : O → |
| V2_26 | restated | equivalent | equivalent | Definition item; A = degIndex_le ∧ exists_isChart_degIndex_eq ∧ eventually_chartDegIndex_le (universe 0). The definitions agree: chartDegIndex φ x is d_C(φ(x)) by rfl (B (a)), and P.degIndex x is the sInf of exactly B's set chartIndicesB P x (same charts P.IsChart φ around x, same d_C(φ x); rfl), so |
| V2_27 | same | equivalent | equivalent | A = lemma_2_23 ∧ eventually_degIndexWith_le ∧ isOpen_setOf_degIndex_lt ∧ isClosed_setOf_le_degIndex (universe 0). lemma_2_23 (∀ᶠ y in 𝓝 x, d_X y ≤ d_X x) is B (an open U ∋ x with d_X ≤ d_X(x) on U) up to mem_nhds_iff, both ways; the open/closed level-set corollaries are derived from B. The one conju |
| V2_28 | restated | equivalent | equivalent | A = proposition_2_24 ∧ transportChart_isChart ∧ degIndex_le_of_isScDiffeoOn (universes 0,0). B uses the project's IsScDiffeoOn (f sc-smooth on open U, g sc-smooth on open V, mutually inverse, f(U) ⊆ V, g(V) ⊆ U) with x ∈ U, so B is proposition_2_24 verbatim and degIndex_le_of_isScDiffeoOn is its ≤ h |
| V2_29 | same | B ⇒ A only | equivalent | Definition item; the project's boundary = {x / 1 ≤ degIndex x} and IsWithoutBoundary = ∀ x, degIndex x = 0 are literally B's (rfl), so A ⇒ B is proved outright without A. A = isWithoutBoundary_iff ∧ isClosed_boundary ∧ isOpen_interior ∧ isClosed_corners ∧ IsScDiffeoOn.mem_boundary_iff (universe 0; 0 |
| V2_30 | explicit | equivalent | equivalent | A (lemma_2_26.{0}) states d_A ≤ d_X for the project's particular structure subPolyfold hA on A; B states it for every M-polyfold structure Q on A satisfying properties (1), (2) of Proposition 2.21. A ⇒ B: any such Q is sc-diffeomorphic to subPolyfold hA by the identity on V ∩ A (V the sub-M-polyfold |
| V2_31 | restated | equivalent | equivalent | Definition item. The project's minimalSubspaceWith T x and partialQuadrantAtWith T x are exactly B's transports T⁻¹(E_{Tx}), T⁻¹(C_{Tx}) of the text's E_x = ⋂_{i∈I(x)} E_i and C_x = ⋂_{i∈I(x)} H_i (via mem_minimalSubspaceWith, and by unfolding for C_x), and dim(E/E_x) = d_C(x) on the standard quadra |
| V2_32 | stronger | neither | equivalent | Definition item; the comparison is between the definitions, which agree: at every x₁ ∈ O₁ (smoothness unused) the project's partialConeWith R T x₁ = range Dr(x) ∩ partialQuadrantAtWith T x and reducedTangentSpaceWith R T x₁ = range Dr(x) ⊓ minimalSubspaceWith T x are B's T_xO ∩ C_x and T_xO ∩ E_x, b |
| V2_33 | stronger | B false | incomparable | A now holds the project's whole treatment of Remark 2.28: T^R_xO ⊆ C_xO (reducedTangentSpaceWith_subset_partialConeWith) and its refutation of the remark's negative claim — at every smooth x of every sc-smooth retract, T_xO and T^R_xO are sc-subspaces and C_xO IS a partial quadrant in T_xO (remark_2 |
| V2_35 | stronger | A ⇒ B only | A_stronger | A ⇒ B: B's germ (f sc-smooth O∩V → O'∩V' with sc-smooth inverse g) is an IsDiffeoGerm between a retraction RV onto O∩V and R'.restrict V' (A's isDiffeoGerm), so A's proposition_2_30_reduced/cone apply at x₁; the reduced spaces and partial cones computed with RV, R'.restrict V' equal B's (computed wi |
| V2_36 | restated | neither | equivalent | Both directions are proved outright, so the comparison is between B and the project's definitions, which agree. A's theorems say little about the text's claim: selfChart_isChart concerns X_U for U relatively open in a partial quadrant (not a general retract), and Compatible.isDiffeoGerm turns compat |
| V2_37 | stronger | A ⇒ B only | A_stronger | Same notions on both sides (T_xO = range Dr(x), E_x = minimalSubspaceWith T x, quotDim, d_O = degIndex of LocalModel.toMPolyfold); the project's reducedTangentSpaceWith is T_xO ⊓ E_x, and quotDim A (A ⊓ B) = quotDim A B, so A ⇒ B is theorem_2_31_retract applied at the level-1 lift x₁ of B's smooth p |
| V2_38 | stronger | A ⇒ B only | A_stronger | Same notions (X_C = hC.toMPolyfold hne, d_X = MPolyfold.degIndex, d_C = degIndex E C). A ⇒ B: C is relatively open in itself (V = E₀) and corollary_2_32 at U = C. B ⇒ A fails for a genuine reason on the fourth conjunct degIndexWith_le_of_germ (core of Theorem 2.31): d_C(x) ≤ d_{C'}(F x) for a germ F |
| V2_39 | restated | A ⇒ B only | A_stronger | The definitions agree: partialQuadrantAtWith T e = CeB T e and minimalSubspaceWith T e = EeB T e for every T and e (pq_eq, ms_eq, unfolding). A ⇒ B uses A: E_e ⊆ C_e is A's first conjunct, and B's cardinal codimension is A's finrank_quotient_minimalSubspaceWith (quotient finite-dimensional) plus deg |
| V2_40 | restated | neither | A_stronger | Definition item with four listed lemmas. The definitions agree and B holds outright (B_holds, A unused): for a presentation T, R.IsTameWith T ↔ IsTameWithB R T (isTameWith_iff) — (1) degIndex E C = degIndexWith T = dCB T on C ⊇ U; (2) the project's level-1 point x ∈ O₁ ∩ (E₁)_∞ is B's smooth x ∈ O w |
| V2_41 | stronger | equivalent | equivalent | Same notions: B's complB R x₁ = range(id − Dr(x)) and tangentAt R x₁ = range Dr(x) (rfl), and 'smooth x ∈ O with lift x₁' is the project's x₁ ∈ O₁ ∩ (E₁)_∞. A ⇒ B: B assumes R.IsTame (every presentation) and fixes T; A's proposition_2_35 needs only R.IsTameWith T; B's sc-subspace clause is part of I |
| V2_42 | stronger | equivalent | equivalent | Same notions on both sides (range Dr(x) = T_xO, reducedTangentSpaceWith, partialConeWith, ofSubspace/IsPartialQuadrant, d_O = degIndex of LocalModel.toMPolyfold). A ⇒ B: A is stated for a retraction R₀ tame w.r.t. the given presentation T, B for EVERY retraction R onto O; glue: range Dr(x) does not  |
| V2_43 | same | B ⇒ A only | equivalent | Definition item. The project's MPolyfold.IsTame and B's IsTameMB are the same existential except for the equivalence of atlases: the project's MAtlas.Equiv A B ('some atlas D has chart set A ∪ B') vs B's EquivB ('all charts of A ∪ B pairwise compatible'), equivalent via the project's MAtlas.equiv_if |
| V2_44 | same | neither | equivalent | Definition item; both directions hold only outright (flagged). The definitions agree on EVERY M-polyfold (B's tameness hypothesis is not needed): the project's face closure(connectedComponentIn {d_X = 1} x) with d_X(x) = 1 is B's closure(val '' connectedComponent s), s in the subtype {d_X = 1}, by M |
| V2_46 | explicit | equivalent | equivalent | Same notions: B's faces are MPolyfold.IsFace of LocalModel.toMPolyfold, A's are IsRetractFace in E₀, linked by isFace_toMPolyfold_iff (part of A). The only real difference is the extended faces: A uses the hyperplanes f_i = coordHyper T i of ONE presentation T, B (IsExtFaceB) those of ANY presentati |
| V2_47 | same | equivalent | equivalent | Same notions on both sides: B spells out IsFaceStructured (encard of the faces through x = d_O(x)) for the M-polyfold LocalModel.toMPolyfold of a tame retract, which is exactly corollary_2_41 (A ⇒ B is that theorem after unfolding). B ⇒ A: corollary_2_41 is B after `cases` on the local model; isFace |
| V2_48 | restated | equivalent | equivalent | Same mathematics, different packaging of 'the faces of V'. A (proposition_2_42) takes V = dom φ for a tame chart φ : V → O and states the local claims on the model: d_X(y) = d_C(φ y) = d_O(φ y) and the M-polyfold O is face-structured; B uses the induced structure P.subPolyfold hV on the subtype ↥V ( |
| V2_49 | restated | A ⇒ B only | A_stronger | Same vocabulary (IsFace/degIndex of LocalModel.toMPolyfold, ScRetraction, IsSubMPolyfold, subPolyfold, IsTame). A ⇒ B: B's retraction s : V* → V* onto F is the S of proposition_2_43 (S.U ⊆ R.U, F ⊆ S.U, S.retract = F), after moving F between ↥O and E₀ with isFace_toMPolyfold_iff (V2_46, not banned); |
| V2_50 | restated | neither | A_stronger | A states Prop 2.44 on the model of a tame chart φ : V → O: faces of the M-polyfold O through φx (count d_X(x); each a tame sub-M-polyfold OF O with d_F(φx)+1 = d_X(x)) and, for σ ⊆ I(φx), only the GERM of the corner: A_σ = φ⁻¹(B ∩ ⋂_{i∈σ} F_i) for some small open B is a tame sub-M-polyfold of X with |
| V2_51 | explicit | A ⇒ B only | A_stronger | Same vocabulary (IsTame, IsFace, degIndex, IsFaceStructured, IsSubMPolyfold, subPolyfold). B reads 'the interior of F = closure G' as F ∩ {d_X = 1}; the project's interior is the component G itself, and theorem_2_45_interior says the two coincide, so B's first claim is theorem_2_45_isSubMPolyfold_in |
| V2_53 | stronger | A ⇒ B only | A_stronger | Same vocabulary on both sides (MPolyfold.prod, IsLocalScDiffeo, fibredProduct, IsSubMPolyfold, subPolyfold, IsTame, degIndex). A ⇒ B: sub-M-polyfold is isSubMPolyfold_fibredProduct, the tame clause is isTame_fibredProduct + degIndex_fibredProduct_eq_snd, the last clause is proposition_2_46_of_isLoca |
| V2_54 | restated | neither | equivalent | Definition item; the substance is the comparison of definitions, which B itself asserts and which is proved outright (B_holds): doubleLevel = doubleLevelB (U_m ⊕ F_k), the levels of (U ◁ F)[i] = U × F^i are U_m ⊕ F_{m+i}, and IsStrongBundleMap / IsStrongBundleRetraction ⇔ B's IsStrongBundleMapB / Is |
| V2_55 | restated | equivalent | equivalent | Same notions. The project's IsStrongBundleRetraction and B's IsStrongBundleRetractionB agree for U relatively open (B's [1]-map is any sc-smooth lift Φ₁, the project's is shiftFiber R; they agree on U ⊕ F₁, so sc-smoothness transfers by IsScSmooth.congr), hence IsStrongBundleRetract = B's local stro |
| V2_56 | restated | A ⇒ B only | A_stronger | The definitions agree. The project's IsScSmoothSection (fst_eq on O plus Definition 2.7 in the 'every retraction onto O' form) is B's IsScSmoothSectionB (f(O) ⊆ K, (f x).1 = x, Definition 2.7 with one retraction) because O = r(U) is a retract (baseRetraction, after converting B's strong bundle retra |
| V2_57 | explicit | A ⇒ B only | A_stronger | The definitions agree (for continuous P, which B assumes). Charts: every field of StrongBundleChart is a clause of B's IsStrongBundleChartB (strong bundle retraction converted, r(U) = O definitional), with fibre continuity from A's continuous_fiber; conversely a B-chart is a project chart exactly wh |
| V2_58 | restated | A ⇒ B only | A_stronger | The notions agree where both speak: B's clauses (b) (strong bundle structures = classes of atlases of project StrongBundles), (d) (Y_{m,k} nested, = doubleLevel, oneSet = Y_{0,1}), (e) (Y[0] = toMPolyfold0 with levels Y_{m,m}, P[0] sc-smooth) and (f) (Y[1] = toMPolyfold1 with levels Y_{m,m+1}, P[1]  |
| V2_59 | restated | equivalent | equivalent | Same notions. IsSection (∀ x, P (f x) = x) is B's P ∘ f = id (funext); StrongBundle.IsScSmoothSection is literally B's 'section, sc-smooth into Y[0] = toMPolyfold0'. The project defines sc⁺-sections chart-wise (principal part in F₁ and localRepOne : O → K[1] sc-smooth in every strong bundle chart),  |
| V2_60 | same | A ⇒ B only | A_stronger | The definitions agree definitionally: pullbackSpace P f = {(z, y) / P y = f z} with Mathlib's subtype (= induced) topology, pullbackProj = (z, y) ↦ z, pullbackProj' = (z, y) ↦ y; A ⇒ B is these rfl's plus pullback_comm for P ∘ P' = f ∘ P_f. B ⇒ A fails only by scope: B states P ∘ P' = f ∘ P_f in the |
| V2_61 | explicit | neither | incomparable | A formalizes 'natural structure' as a specific atlas: proposition_2_54 says ∃ B' : StrongBundle PZ (pullbackProj P f) whose charts are exactly the pulled-back charts Φ_f(z,y) = (ψ(z), pr_F Φ(y)) (pullbackAtlas), plus construction lemmas (transition formulas, compatibility, R_g and its image K_g, par |
| V2_62 | stronger | equivalent | equivalent | B is literally the type of metrizableSpace_of_locally.{0} (Smirnov: paracompact Hausdorff + every point has an open metrizable neighbourhood ⇒ metrizable), so A ⇒ B is a projection. B ⇒ A: the other conjuncts of A are the project's proof-route forms. metrizableSpace_of_partition follows from B after |
| V3_1 | restated | neither | equivalent | Definition item in substance: the project's ScNbhdGerm has exactly the fields of B's IsScGermB (nested along incl, U m = O ∩ lvlSet C m with O open, 0 ∈ U m; lvlSet C m is definitionally B's levelB), every IsScGermB sequence is the levels of a ScNbhdGerm, the project's tangent germ has levels U(m+1) |
| V3_2 | same | neither | equivalent | Definition item in substance: B (the project's IsSc0Germ / IsSc1GermWith / IsSc1Germ / IsSckGerm / IsScSmoothGerm agree with B's notions on every germ of a partial quadrant) is proved outright. sc⁰: the project's levelMap is a level lift, and any lift agrees with levelMap on U_m. sc¹: HasFDerivWithi |
| V3_5 | explicit | neither | equivalent | The definitions now agree. At HEAD the project's StrongBundle.IsScSmoothSectionGerm asks f̂ ∘ r to be sc-smooth on SOME sc-germ of neighbourhoods G with G₀ ⊆ U of a centred compatible chart (the germ reading), as B (the text) does. B additionally asks f to be continuous on an open V ∋ x₀ with φ⁻¹(r( |
| V3_7 | explicit | neither | equivalent | Definition item in substance; B is proved outright. Under B's hypothesis g sc-smooth on U, the project's whole-U conditions IsFillerOf are the text's filling IsFillingB: (1), (2) coincide literally (rB, ρB, kB are r, ρ, fillDefect R g definitionally); Lr = scDeriv U r 0, Lk = scDeriv U k 0 satisfy B |
| V3_8 | stronger | A ⇒ B only | A_stronger | A now contains the germ form of Proposition 3.5 (IsFillingGerm.proposition_3_5, exists_kerEquiv, deriv_comp_r_eq_zero) for any derivative family Dg of the filling germ g on a germ G ⊆ U, which is exactly B's setting (g an sc-smooth section germ, section property near 0). A ⇒ B (A_to_B): B's IsFillin |
| V3_9 | restated | neither | equivalent | A is now the two bridges IsFilledVersion.isFillingGerm and IsFillingGerm.isFilledVersion (the latter assuming g sc-smooth on U); the row's canonical notion of Definition 3.6 is the germ filling IsFillingGerm, with IsFilledVersion its whole-chart special case G = ofSet U. Proved: IsFillingGerm ↔ the  |
| V3_10 | restated | neither | equivalent | Definition item: only IsBasicGerm and IsSc0ContractionGerm are listed, so A = True and both implications are vacuous; the content is B itself (the project's basic germs on C̃ = [0,∞)^k ⊕ ℝ^{n−k} ⊕ W coincide with the text's), proved outright as B_holds. Project ⇒ text: the project's B agrees with w  |
| V3_11 | stronger | A ⇒ B only | A_stronger | A now contains the text's Lemma 3.9 on level m with smallness on level m (IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le: every ε, every m, x ∈ U_{m+1} with /ιx/_m < r, for any sc⁰-contraction germ B with an sc¹ derivative family), besides D₂B(0,0)=0 (deriv_zero_snd) and the older level-0 / ½-co |
| V3_12 | stronger | A ⇒ B only | A_stronger | A now contains both statements of Proposition 3.10: proposition_3_10 (Df(0) sc-Fredholm of index dim P − dim Q) and proposition_3_10_level / proposition_3_10_full (for every m there is δ with levelDeriv Df m x Fredholm of index dim P − dim Q for x ∈ U_{m+1}, /ιx/_m < δ), for any basic germ h, sc⁺-ge |
| V3_13 | restated | neither | A_narrower | A is now four auxiliary theorems (IsScFredholmGermWholeChart.isScFredholmGerm, isScFredholmGerm_iff_germG_wholeChart, IsFillingGerm.nonempty_kerEquiv, TrivialBundle.not_isFillingGerm_evenBundleChart), re-proved outright in B_to_A; B (project IsScFredholmGerm ↔ text IsScFredholmGermB on tame bundles) |
| V3_14 | stronger | A ⇒ B only | A_stronger | Same conclusion: nested open neighbourhoods O(i) of x0 with cl_X{x in O(i) / f(x)=0} a compact subset of X_i for the level topology; A phrases it as levelVal '' K = closure with K compact in PX.Level i (= levelSet i with levelTopology i), B as closure inside levelSet i plus compactness of its preima |
| V3_15 | restated | A ⇒ B only | A_stronger | Same conclusion (A_to_B_projGerm: corollary_3_13 gives B verbatim with the project's germ notion; Level m = levelSet m with levelTopology m, 'eventually' = ∃ K, ∀ k ≥ K, the limit read as x₀). At HEAD corollary_3_13 assumes the germ reading IsScFredholmGerm (filling and sc⁺-section as germs), so the |
| V3_16 | same | neither | A_narrower | A is two auxiliary theorems (zeros of an sc-Fredholm section are smooth points, now for the germ-reading notion; whole-chart sc-Fredholm sections are germ-reading ones); the content is B, the comparison of IsScFredholmSection (germ reading at HEAD) with the text's Definition 3.14 on tame bundles. Cl |
| V3_17 | stronger | A ⇒ B only | A_stronger | Both sides use the same notions, at HEAD the germ reading of Definition 3.11 (IsScFredholmSection with IsScFredholmGerm built from IsFillingGerm/IsScPlusGerm), plus IsScPlusSection and sectionAdd. B adds the hypothesis PX.IsTame (the text's 'over a tame M-polyfold'); A's theorem_3_15 drops it (tamen |
| V3_18 | restated | A ⇒ B only | A_stronger | A = lemma_3_16 ∧ IsScFredholmGerm.sectionAdd (universes u v of the latter at 0; at HEAD the latter is the germ-reading statement). B's (1) s̃ = s on O and (2) R(r(u), s̃(u)) = s(r(u)) are lemma_3_16 (from the hypothesis) applied to the principal part ι∘ŝ of the sc⁺-section (section condition from Is |
| V3_19 | stronger | A ⇒ B only | A_stronger | A now contains Lemma 3.17 in the germ reading: IsFillingGerm.add_section (g a filling germ of f̂, ŝ sc-smooth on U with (x, ŝ(x)) ∈ K on O ⟹ g + ŝ∘r a filling germ of f̂ + ŝ) and add_section_germ (ŝ a germ), besides the whole-chart lemma_3_17/IsFillerOf.congr_left. A ⇒ B is proved from A (A_to_B, no |
| V3_20 | stronger | B false | A_narrower | A is now the conjunction of the new theorems about the text's notion as written (IsScGoodComplement: an sc-splitting E = N ⊕ P with the ε-property; IsInGoodPositionSc): the forgetful map to the project's notion, the upgrade lemmas (a closed good complement of a smooth finite-dimensional N is a good  |
| V3_21 | same | A ⇒ B only | A_stronger | A = proposition_3_22 ∧ exists_quadrantNormalForm ∧ mem_quadCone_of_vanIdx ∧ sigmaCoord_surjective (V universes at 0). A ⇒ B: B's good position (sc-complement for smooth N, closed complement otherwise, plus ε) gives the project's IsInGoodPosition (the level-0 part of an sc-splitting is an algebraic c |
| V3_22 | narrower | neither | A_stronger | A = IsScSmoothGerm.isScInftyGermAt ∧ IsScSmooth.isScInftyGermAt; B = (project HasTangentGermProperty ↔ text's) in a tame M-polyfold. Half proved using A (mpr_of_A: text ⇒ project; B's sc-complement Y is closed and an algebraic good complement, δ reset to 0 off V, B's fixed sc-smooth germ gives the p |
| V3_23 | same | neither | A_stronger | A = proposition_3_26 ∧ proposition_3_26_image (universes at 0), about the project's HasTangentGermProperty; B is the same invariance for the text's notion HasTangentGermPropertyB, with X tame. B is proved OUTRIGHT (B_holds: the data N, Y, V, δ, G, D are carried by the chart ϕ∘ψ⁻¹ = transportChart, a |
| V3_24 | narrower | neither | incomparable | A's Theorem 3.27 assumes at every point of M tangent-germ data satisfying TangentGermChart.IsRegular: (a) delta sc-smooth on the whole of V (set sense), (b) the projection pi along Y maps the retract O into C. These are extra hypotheses the project adds because the text's proof fails without them (d |
| V3_25 | restated | neither | equivalent | All listed declarations are definitions, so A = True and both directions are vacuous; the content is B itself, the vocabulary check IsSc0ContractionGerm Ct G B <-> IsSc0ContractionGermText Ct G B, proved outright (iff_text, without even using the partial-quadrant hypothesis). sc0 of B and of f = w - |
| V3_26 | explicit | A ⇒ B only | A_stronger | A => B: existence is the conjunct theorem_3_29_of_isSc0ContractionGerm of A (partial quadrant => quadrant-like; level-0 membership from the level-m one via levelMap_zero); B's uniqueness as a germ follows from the same conjunct's radius r: two solution germs delta, delta' are continuous with value 0 |
| V3_27 | restated | A ⇒ B only | A_stronger | A => B: B's sc1 hypothesis on f = w - B(a,w) gives sc1 of B (pairing with pr2 and the sc-operator (u,v) -> u - v); the conjunct theorem_3_30 of A, applied to the working form h.toContractionGerm, gives sol sc1 on germ 1; B's arbitrary solution representative delta equals sol near 0 (uniqueness of fi |
| V3_28 | restated | A ⇒ B only | A_stronger | A => B from the conjuncts lemma_3_31 and (new) isSc0ContractionGerm_next, applied to the working form h.toContractionGerm with its parameter regions N m shrunk into the V_i (i <= m) and the region {delta in O 0}, so that B's arbitrary solution germ delta is sol there and gives sol sc^j on germ 0; G^ |
| V3_29 | restated | A ⇒ B only | A_stronger | A => B: B only asks for SOME sc0-contraction germ f^(j) of class sc^{min(k-j,1)} with solution germ T^j delta, so the trivial germ f^(j)(a,w) = w - T^j delta(a) (contraction constant 0) is a witness once T^j delta is regular; A's sol_isSckGerm (j := k) for h.toContractionGerm gives sol sc^k on some  |
| V3_30 | restated | A ⇒ B only | A_stronger | A => B: A's theorem_3_33 applied to the working form h.toContractionGerm of B's sc0-contraction germ gives the canonical solution germ sol of class sc^k on germ s; B's arbitrary solution representative delta equals sol near 0 by uniqueness of fixed points in O 0 (ContractionGerm.eq_sol, continuity o |
| V3_31 | same | A ⇒ B only | A_stronger | A => B is proved entirely from A now. Clause (1): corollary_3_34 for the working form h.toContractionGerm (sc-smoothness of f = w - B gives that of B; B's arbitrary solution germ delta agrees with sol near 0 by uniqueness in O 0) gives V_{m,k} (shrunk into V_0 and the agreement region) with sol on l |
| V3_32 | restated | A ⇒ B only | A_stronger | A now contains Theorem 3.35 in the text's form (theorem_3_35_of_isSc0ContractionGerm: Definition 3.28 contraction germ on any quadrant-like C~ in a finite-dimensional P, any representative (V, delta) of the solution germ; f sc^k gives delta sc^k on a smaller germ, f sc-smooth gives delta sc-smooth o |
| V3_33 | same | neither | equivalent | The only listed declaration (IsBasicGerm) is a definition, so A = True and both directions are vacuous; the content is B, the vocabulary check (exists B, IsBasicGerm (stdQuadrant n k) G f B) <-> IsBasicGermText G f, proved outright. The project carries the contraction map B as an extra argument tied |
| V3_34 | restated | A ⇒ B only | A_stronger | A => B (substantial glue, no new mathematics): B's sc+-germ s has an R^N-component which the project's StabilityData drops; it is absorbed into the basic germ f' = f + (s_RN, 0) (same contraction map), so f + s = fsum f' with s_W = W-part of s; exists_of_scPlus (in A) gives the data S, theorem_3_38  |
| V3_35 | stronger | A ⇒ B only | A_stronger | A => B: the conjunct theorem_3_12_local of A, applied to B's basic germ h and the sc0 part of B's sc+-germ s (a partial quadrant is closed), gives nested open O(i) containing 0 in E_0 with cl(S cap O(i)) = iota_i(K_i), K_i compact in E_i; B's relatively open O(m) are O(m) cap G.U 0, and cl(S cap O(m |
| V3_36 | restated | A ⇒ B only | A_stronger | A => B from the conjunct corollary_3_41 alone. Glue: B's sc+-germ s takes values in (R^N + W)^1 while the project's StabilityData only carries the W-component s2; the R^N-component s1 is absorbed into the basic germ (h' = h + (s1, 0) is basic with the same B, and h + s = fsum h'); the sc-Fredholm sp |
| V3_37 | restated | neither | A_narrower | A = StabilityData.lemma_3_42 (toShiftedBasicData is vocabulary; no universe parameters): for the project's ONE explicit coordinate change of Theorem 3.38 (linear (split₀, fiber₀), g = pushMap₀ f = Φ_*(f + s)), for every ε > 0 there is r > 0 such that zeros x of g with /x/₀ < r have their fibre compo |
| V3_38 | restated | neither | incomparable | A = theorem_3_43_sc_smooth ∧ theorem_3_43 ∧ Sol.exists_contDiffOn_level ∧ H_contDiffOn ∧ Sol.exists_eq_add_τ ∧ exists_proj_mem_of_eq_zero (no universe parameters). A is a germ-form core statement. It takes any sc-smooth g with g¹ basic (ShiftedBasicData) and assumes (i) K' = ker Dg(0) is in good pos |
| V3_39 | same | neither | incomparable | A = ShiftedBasicData.Deriv.ker_Dg_eq ∧ snd_Dg_inr ∧ DH₀_surjective (no universe parameters), stated for the project's data 𝒟 : ShiftedBasicData (g an sc-smooth germ on G₀ whose index raise is basic on exactly the shifted germ G₁, δ = 𝒞.sol) with 𝒱 : 𝒟.Deriv. Proved: kerEquiv_of_A — in A's own settin |
| V3_40 | stronger | A ⇒ B only | A_stronger | A = IsGoodComplement.map ∧ IsInGoodPosition.map (no universe parameters). A ⇒ B by glue, using the IsGoodComplement.map conjunct: ψ = base Φ, ψ' = base Φ' are inverse sc-smooth maps U ⇄ U' with ψ(0) = 0; B's Dφ 0 equals the chosen scDeriv U ψ 0 (uniqueness at 0 ∈ U₁); S = Dψ(0) is a linear isomorphi |
| V3_41 | same | neither | incomparable | A = lemma_3_46 ∧ lemma_3_46_isInGoodPosition (no universe parameters): the linear core for arbitrary finite-dimensional P, sc-Banach W, L : P → W₀, K̃ ⊆ P — if the graph K' = {(α, Lα) / α ∈ K̃} has an algebraic good complement w.r.t. C̃ × W, then K̃ has a good complement Z w.r.t. C̃ and Z ⊕ W is a g |
| V3_42 | restated | neither | incomparable | A = theorem_3_47_sc_smooth ∧ theorem_3_47 ∧ StabilityData.scDerivGerm_pushMap₀ (no universe parameters). A ⇒ B fails on the conclusion. A only produces an algebraic good complement Y (IsCompl on level 0), but B, following Definition 3.21 of the text, requires an sc-complement (E.IsScSplitting K Y) w |
| V3_43 | same | B false | equivalent | Definition item: the decls are the definitions IsFillingGerm (the canonical germ-reading filling) and IsFillerOf, so A = True and B → A is vacuous. B asserts IsFilledVersion ↔ IsFillingB, i.e. identifies the text's filling with the project's whole-chart IsFilledVersion. The canonical notion IsFillin |
| V3_44 | same | neither | incomparable | A = IsFillerOf.remark_3_49 (no universe parameters): from a filler (IsFillerOf: (1), (2) near 0, k = [1 − ρ(r)]g sc¹ on the whole U, linearization via scDeriv U) get an open W ∋ 0 with f = g on O ∩ W and (2) on U ∩ W. Its content is just the filter step: A_direct proves A from (1), (2) alone without |
| V3_45 | same | neither | A_narrower | Definition item: A = True (all decls are definitions), B = (IsScFredholmGermTame ↔ IsFredGermB) ∧ (IsScFredholmSectionTame ↔ IsFredSectionB) for sc-smooth sections of tame bundles. At HEAD the project's notions are the germ reading. Same tame chart on both sides; the filling agrees field for field ( |
| V3_46 | restated | A ⇒ B only | A_stronger | A now contains StrongBundle.linAt_isScFredholm (germ reading): for an sc-Fredholm section at a zero x and every strong bundle chart around x, Lin(z) = D(f^ o r)(z)/TzO : TzO -> Kz (z the level-1 lift of phi(x)) is an sc-operator between the sc-subspaces TzO and Kz = rho(z)F, sc-Fredholm, of level-0  |
| V3_47 | restated | neither | incomparable | A = forall_isGoodPositionAtGerm (good position at Dg(0) for every derivative family, same chart), IsFillingGerm.ker_deriv_le_range (ker Dg(0) <= T0O), IsGoodPositionGermTame.isGoodPositionGermSc and isGoodPositionGermSc_iff (at a zero of a tame sc-Fredholm section, good position with an algebraic co |
| V3_48 | narrower | neither | incomparable | A = theorem_3_54_graph (germ reading at HEAD: hypothesis IsGoodPositionGermTame) plus seven lemmas of the proof (theorem_3_54_linear(_of_isTameWith), IsInGoodPositionIn.isInGoodPosition, scDeriv_mem_iff_of_inverse, pushforward_linearization, theorem_3_54_pushforward, scDeriv_eq_of_eqOn_nhds), univer |
| V3_49 | narrower | A ⇒ B only | A_stronger | A = lemma_3_55 ∧ lemma_3_55_core.{0} ∧ fderivWithin_mem_of_mapsTo.{0,0}. A ⇒ B was proved from the conjunct lemma_3_55_core alone (coordinates ℓ_i = (T·)_i of B's presentation, P = Y): B's τ : V → E₁ on a relatively open V ∋ 0 is pushed to E₀ and extended to the whole cone N ∩ C by a bump (σ ∘ (b·id |
| V3_50 | narrower | A ⇒ B only | A_stronger | A = theorem_3_56_of_tangentGerm (universes 0), unchanged by the germ reading: in an M-polyfold with d_X ≡ 0, a nonempty set with the regular tangent germ property of one fixed dimension n is a sub-M-polyfold whose induced structure is an n-manifold without boundary; A has no Fredholm hypothesis. A ⇒ |
| V3_51 | narrower | A ⇒ B only | A_stronger | A = theorem_3_57_of_tangentGerm (universes 0), unchanged by the germ reading: a nonempty solution set with the regular tangent germ property of one fixed dimension n is a sub-M-polyfold whose induced structure is tame and an n-dimensional manifold with corners; A has no Fredholm hypothesis. A ⇒ B is |
| V3_52 | restated | A ⇒ B only | A_stronger | A = lemma_3_59 (abstract: any family b ↦ L(b) of sc-operators X → Y over a finite-dimensional parameter space, jointly continuous on level 0, with L(0) injective and the family compactness property, is injective near 0). B is the concrete Lemma 3.59 in the setting of Theorem 3.58. A ⇒ B was proved b |
| V3_53 | restated | A ⇒ B only | A_stronger | A = lemma_3_60 (abstract: on a compact parameter set K, a family of sc-operators X → Y, jointly continuous on level m, injective on level m, with the family compactness property, has a uniform lower bound c_m). B is the concrete Lemma 3.60 in the setting of Theorem 3.58, with the O of Lemma 3.59. A  |
| V3_54 | restated | A ⇒ B only | A_stronger | A = lemma_3_61 ∧ famInv_isSc0Germ ∧ famInv_isSc1GermWith ∧ famInv_hasFDerivWithinAt ∧ famInv_isSckGerm ∧ exists_forall_norm_le_of_isCompact (no universe parameters). lemma_3_61 is stated for sc-germs at 0 (a germ Gv of relatively open neighbourhoods of 0 in C̃, levels allowed to shrink with m), B fo |
| V3_55 | same | A ⇒ B only | A_stronger | A = lemma_3_65.{0} ∧ sigmaCoord_surjective.{0} (vanIdx is vocabulary). A ⇒ B was proved from the lemma_3_65 conjunct with ℓ_i the coordinate functionals of ℝⁿ ⊕ W and P = N^⊥: the blind Σ is literally the project's vanIdx for these functionals, and only the ε-property of B's good complement is used  |
| V3_56 | restated | equivalent | equivalent | A = proposition_3_69 (no universe parameters; QuadrantNormalForm is vocabulary). A ⇒ B: B's good position (sc-complement with the ε-property) gives the project's IsInGoodPosition (algebraic complement, via levelSub at level 0); d_C on the quadrant is quadrantDeg = blind dC (degIndex_quadrant), x ∉ W |
| V3_57 | explicit | A ⇒ B only | A_stronger | A = lemma_3_70 ∧ lemma_3_70_core.{0} ∧ exists_rayDecomp.{0} ∧ exists_lipschitz_small.{0}. A ⇒ B was proved from the lemma_3_70 conjunct alone: B's τ : N → E₁ (Y-valued only on N ∩ C) is pushed to E₀ by ι₁ and set to 0 off the cone, so it is Y-valued everywhere as lemma_3_70 requires; C¹ and Dτ(0) =  |
| V3_58 | stronger | A ⇒ B only | A_stronger | A = theorem_3_72 ∧ surjective_of_image_eq ∧ degIndex_map_eq ∧ degIndex_eq_zero_iff (no universe parameters). theorem_3_72 is stated for C^j maps (j ≥ 1) and, for each j, produces its own U', V', g, so B's single C^∞ diffeomorphism is not read off directly. A ⇒ B was proved from theorem_3_72 with j = |
| V3_59 | stronger | A ⇒ B only | A_stronger | A = proposition_3_73 ∧ InvData.contDiffOn_inv (no universe parameters; InvData is vocabulary). A ⇒ B was proved from the proposition_3_73 conjunct: B's hypotheses give InvData C U f j for every j ≥ 1 (C^∞ ⇒ C^j; hypothesis (3) d_C(x) = d_C(f(x)) gives the project's weaker 'x interior ⟺ f(x) interior |
| V3_60 | same | A ⇒ B only | A_stronger | A = InvData.half_norm_le ∧ InvData.norm_sub_le ∧ InvData.injOn ∧ InvData.ball_inter_subset_image ∧ InvData.image_relOpen (no universe parameters). A ⇒ B was proved: B's hypotheses give InvData C U f 1 (C^∞ ⇒ C^1; d_C-equality ⇒ interior preservation via degIndex_eq_zero_iff); image_relOpen gives f(U |
| V3_61 | same | A ⇒ B only | A_stronger | A = type of corollary_3_75 (no universe parameters, V : Type): under InvData C U f j, f is continuous on U, g = invFunOn f U is continuous on f(U), and g∘f = id on U, f∘g = id on f(U). A ⇒ B: B's Hyp373 gives InvData C U f 1 (C^∞ ⇒ C¹; d_C-equality used only through d_C = 0 ⟺ interior, degIndex_eq_z |
| V3_62 | narrower | neither | incomparable | A = InvData.hasFDerivWithinAt_inv ∧ InvData.contDiffOn_inverse_deriv (no universe parameters). The project proves Lemma 3.77 only under InvData, i.e. Proposition 3.73's hypotheses (U convex, ‖Df(x) − 1‖ ≤ 1/2 on U, interior points preserved), from which it derives the homeomorphism and the invertibi |
| V3_63 | stronger | A ⇒ B only | A_stronger | A = theorem_3_78 ∧ ContractionData.exists_solution (no universe parameters). A ⇒ B: B's setting (ℝⁿ = Fin n → ℝ, C = quadC n k, f into Fin N → ℝ) is an instance of theorem_3_78. quadC is a partial quadrant via ℝⁿ ≅ ℝᵏ × ℝⁿ⁻ᵏ, fderivWithin f U 0 = L by unique differentiability of U, B's good position |
| V3_64 | same | A ⇒ B only | A_stronger | A = ContractionData.exists_radii ∧ Radii.norm_sub_le ∧ Radii.eq_τ (no universe parameters): for abstract normalized data (ContractionData on K × Y), admissible radii exist (ε, a, b with εa ≤ b, the region R ⊆ U and ‖DB‖ ≤ ε/(2(1+ε)) on R); on R, B is c₀-Lipschitz in both variables; and fixed points  |
| V3_65 | explicit | A ⇒ B only | A_stronger | A = Radii.mapsTo_ball ∧ Radii.exists_fixed (no universe parameters; Radii.τ is a definition, vocabulary only): for abstract normalized data (ContractionData on K × Y: convex Cp, B(0) = 0, DB(0) = 0) and ANY admissible Radii S (good constant ε, radii a, b with εa ≤ b, ‖DB‖ ≤ ε/(2(1+ε)) on the region) |
| V3_66 | stronger | A ⇒ B only | A_stronger | A = Radii.norm_τ_le ∧ norm_τ_sub_le ∧ continuousOn_τ ∧ (new) norm_τ_sub_le_global ∧ norm_τ_sub_le_eps ∧ lipschitzOnWith_τ ∧ norm_τ_sub_le_of_norm_le (no universe parameters): for abstract normalized data and any admissible Radii, /τ(k)/ ≤ ε/k//2, /τ(k) − τ(k₀)/ ≤ (1 + 2ε)/k − k₀/, τ continuous on V₀ |
| V3_67 | stronger | A ⇒ B only | A_stronger | A = Radii.hasFDerivWithinAt_τ ∧ Radii.contDiffOn_Φ ∧ Radii.contDiffOn_τ (no universe parameters): for abstract normalized data and any admissible Radii, τ has derivative Φ(k, τk) = Ring.inverse(1 − D₂B)·D₁B within V₀, Φ is C^{j−1} on the region, and τ is C^j on all of V₀. A ⇒ B: same glue as V3_65 w |
| V3_68 | narrower | neither | incomparable | A = theorem_3_19 ∧ theorem_3_19_linearization ∧ theorem_3_23 ∧ lemma_2_26 ∧ theorem_3_19_linearization_sc ∧ StrongBundle.linAt_isScFredholm (germ reading, universes 0). A => B fails on B's second clause only: B's first clause (at every zero, in every strong bundle chart, f'(x0) sc-Fredholm) now foll |
| V3_69 | narrower | A ⇒ B only | A_stronger | A = theorem_3_23_of_nearby ∧ theorem_3_23 ∧ theorem_3_54_two ∧ theorem_3_27 (universes 0), the first three now in the text's germ reading. A ⇒ B through A's theorem_3_23: B's IsSurjGoodPosAt (sc-complement good position of Lin(z) in some tame chart) gives IsGoodPositionGermTame (isGoodPositionGerm_o |
| V3_70 | explicit | A ⇒ B only | A_stronger | A = corollary_3_24 ∧ theorem_3_57 ∧ corollary_3_24_sc ∧ forall_isGoodPositionGermSc_iff (universes 0, germ reading). A assumes only IsScFredholmSection, good position in a centred tame chart at every zero (IsGoodPositionGermTame with an algebraic complement, or IsGoodPositionGermSc with the text's s |
| V3_72 | narrower | neither | incomparable | A = theorem_3_27_loc (universe 0) ∧ the four theorem_3_27_loc_* lemmas (universe 0). As in V3_24: every theorem of A assumes regular project data (IsRegular: (a) δ sc-smooth on all of V, (b) π(O) ⊆ C) at every point, B only the blind Definition 3.25 (fixed sc-smooth germ, no condition on π(O)) plus  |
| V3_73 | narrower | B false | A_narrower | B is false (not_B, rt_check OK), as its author predicted: it claims, for every Definition 3.25 datum at x ∈ M, every v₀ ∈ V and every datum at x₀ = φ⁻¹(v₀ + δ(v₀)), that k(w) = πφψ⁻¹(w + τ(w)) has an invertible linearization, is a local diffeomorphism, and that δ is an sc^∞-germ near v₀; Definition  |
| V3_74 | narrower | B false | A_narrower | B is false (not_B, rt_check OK): its claim (1) says that for every Definition 3.25 datum at every point of a tangent-germ set M of a tame M-polyfold, δ is an sc^∞-germ near every v₀ ∈ V, but Definition 3.25 controls δ only near 0. Counter-model in the file: X = ℝ² (rnPolyfold 2, tame), M = {(t³, t)} |
| V3_76 | restated | neither | incomparable | A = corollary_3_39 ∧ corollary_3_39_isConjugate ∧ compIso_eq_strongShift ∧ four general strong-bundle-isomorphism lemmas (no universe parameters). A ⇒ B fails at the hypotheses: A's corollary assumes g and s sc-smooth on the relatively open U (set sense), B only that s is an sc-smooth germ (IsScSmoo |
| V3_77 | stronger | neither | incomparable | A = theorem_3_43_closed/proj, theorem_3_47_proj/closed, theorem_3_54_graph_proj (universes 0; germ reading at HEAD, hypothesis IsGoodPositionGermTame) and three lemmas. The new IsClosed Y closes the complement gap of V3_38/V3_42: a closed complement of the smooth kernel is an sc-complement, and B's  |
| V3_80 | narrower | neither | incomparable | A = theorem_3_54_nearby (universes 0; germ reading at HEAD, hypothesis IsGoodPositionGermTame) ∧ lemma_3_55_relOpen ∧ exists_surjective_Dfs'_graph. A ⇒ B fails on the conclusion: B is claimed for every good-position datum (chart c, filler g, sc⁺ s, conjugation D) handed to it, while theorem_3_54_nea |
| V3_81 | narrower | neither | A_stronger | A = theorem_3_54_nearby_kernel.{0,0} ∧ theorem_3_54_chart_kernel ∧ graphSpace_eq_ker_Dfs' ∧ scDeriv_pushforward_at ∧ ker_scDeriv_eq_map ∧ scDeriv_mem_partialQuadrantAtWith_iff ∧ isInGoodPositionIn_of_le ∧ ker_deriv_eq_map_germ (germ reading at HEAD). A's kernel claim at the nearby zeros is made in O |
| V3_82 | narrower | A ⇒ B only | A_stronger | A = theorem_3_54_one ∧ IsGoodPositionGermFilled.isGoodPositionGerm (universes 0,0) ∧ exists_range_deriv_eq_ρ_of_normal_injective_germ, germ reading; the r2 blind B uses the project's StrongBundle.IsGoodPositionGermSc (germ reading, sc-complement) in hypothesis and conclusion. A ⇒ B (from hA.1): B's  |
| V3_84 | narrower | neither | incomparable | A = theorem_3_54_tangentGermChart_proj ∧ theorem_3_54_tangentGermChart (universes 0,0; germ reading at HEAD: hypothesis IsGoodPositionGermTame) ∧ MChart.compDiffeo_isChart ∧ TangentGermChart.π_mem_of_projectsInto (universe 0) ∧ isScInftyGermAt_of_lifts ∧ StabilityData.ker_Dfs_le_smooth. A gives the  |
| V3_85 | narrower | A ⇒ B only | A_stronger | A = theorem_3_54_two ∧ theorem_3_54 ∧ theorem_3_54_tangentGermChart_solutionSet (universes 0,0) ∧ TangentGermChart.exists_isRegular_of_locally (universe 0), germ reading; the r2 blind B (identical to V3_94's) uses the project's StrongBundle.IsGoodPositionGermSc in hypothesis and (1), and HasCornerSt |
| V3_86 | restated | A ⇒ B only | A_stronger | A = theorem_3_56 ∧ theorem_3_57 ∧ lemma_2_26 ∧ theorem_3_56_sc (universes 0; the Chapter 3 theorems in the text's germ reading). A ⇒ B: PX.boundary = ∅ ↔ IsWithoutBoundary (isWithoutBoundary_iff); B's IsLinSurjAt at a zero with d_X = 0 plus the tame germ data give IsGoodPositionGermTame (germ form o |
| V3_87 | stronger | A ⇒ B only | A_stronger | A = theorem_3_57 ∧ theorem_3_57_dim ∧ theorem_3_27_loc ∧ theorem_3_57_sc (universes 0; germ reading; solutionSetDim is vocabulary). A has no tame-bundle/tame-base hypothesis, only IsScFredholmSection and good position in a centred tame chart at every zero (IsGoodPositionGermTame, or IsGoodPositionGe |
| V3_88 | restated | A ⇒ B only | A_stronger | A = theorem_3_58_of_family ∧ contrMap358_contraction ∧ norm_sub_sub_le_of_hasFDerivWithinAt_segment.{0,0,0} ∧ fiberIsoMap_isStrongBundleIso ∧ famInv_isScSmooth_of (DerivCondition is vocabulary). Both work in the same coordinates E = B ⊕ X, F = A ⊕ Y, C = C̃ ⊕ X with the given family L(b) = P_Y Df(b, |
| V3_89 | narrower | neither | A_stronger | A = theorem_3_58 ∧ familyCompactness_derivFamOp ∧ fredholmIndex_block.{0,0,0,0} ∧ surjective_of_fredholmIndex_block.{0,0,0,0} ∧ lemma_3_59 ∧ lemma_3_60. A ⇒ B is believed to be glue plus standard sc-Fredholm facts, not proved. theorem_3_58 is in coordinates E = P ⊕ X, C = C̃ ⊕ X, F = Q ⊕ Y; B has ar |
| V3_90 | restated | A ⇒ B only | A_stronger | A = InvDataW.injOn ∧ InvDataW.hasFDerivWithinAt_inv ∧ InvDataW.contDiffOn_inv (universe 0): the Prop. 3.73 / Lemma 3.77 machinery under weak hypotheses (U convex with unique differentiability, f of class C^j, ‖Df − 1‖ ≤ 1/2, and the unique differentiability of f(U) ASSUMED; no quadrant, no d_C condi |
| V3_91 | stronger | A ⇒ B only | A_stronger | A = theorem_3_18 ∧ theorem_3_18' ∧ paramSection_eq_sectionAdd ∧ IsScFredholmSection.param ∧ isScPlusSection_paramComb ∧ IsBasicGerm.paramExtend ∧ IsConjugateToBasicGerm.paramExtend ∧ IsStrongBundleIso.paramMap ∧ prod_rn_isTame ∧ isScSmooth_smul (universes 0; paramSection and StrongBundle.pullback ar |
| V3_92 | restated | A ⇒ B only | A_stronger | A = linAt_paramSection_zero ∧ linAt_paramSection ∧ scDeriv_paramSection ∧ PullbackChartData.ofProd_mem_tangent (universes 0); at HEAD the three formulas take f an sc-Fredholm section in the germ reading (only its sc-smoothness is used), as does B, so the germ reading plays no role here. Every conjun |
| V3_94 | restated | A ⇒ B only | A_stronger | A = theorem_3_54_one' ∧ theorem_3_54' ∧ isGoodPositionGermTame_of_chart_dense ∧ theorem_3_54_two ∧ IsGoodPositionGerm.toTame ∧ theorem_3_54_one_sc_of_tame ∧ theorem_3_54_one_sc ∧ theorem_3_54_sc (universes 0), germ reading; the r2 blind B uses the project's StrongBundle.IsGoodPositionGermSc (sc-comp |
| V3_95 | explicit | A ⇒ B only | A_stronger | A = theorem_3_23' ∧ theorem_3_19' ∧ theorem_3_23_of_nearby ∧ lemma_2_26 ∧ theorem_3_23_sc (universes 0; germ reading). A ⇒ B (3.23): B's IsSurjGoodPosAt (non-centred tame chart, sc-complement) gives IsGoodPositionGermTame (isGoodPositionGerm_of_linAt_surj, IsGoodPositionGerm.toTame); theorem_3_23' g |
| V3_96 | stronger | A ⇒ B only | A_stronger | A = linAt_index_of_conjugationData ∧ isSurjLinOfIndex_of_conjugationData ∧ IsGoodPositionGerm.exists_isSurjLinOfIndex ∧ theorem_3_19_linearization_index ∧ finrank_ker_eq_fredholmIndex_of_surjective ∧ linAt_isScFredholm ∧ linAt_isScFredholm_of_isSurjLinOfIndex ∧ proposition_3_52_sc ∧ theorem_3_19_lin |
| V3_97 | stronger | neither | incomparable | A = theorem_3_54_tangentGermChart_index ∧ …_solutionSet_index ∧ theorem_3_54_two_index ∧ theorem_3_23_index ∧ theorem_3_19_index ∧ theorem_3_57_index ∧ theorem_3_54_graph_proj_conj ∧ theorem_3_54_tangentGermChart_proj_conj ∧ linAt_isScFredholm_of_isSurjLinOfIndex (germ reading, universes 0). Proved  |
| V3_98 | narrower | neither | incomparable | A = the 20 theorems of the current decls (germ reading, universes 0). A => B: B(0) (Definition 6.1 exists at every smooth point, independent of chart and chart-level sc+-section) and B(a) (constancy along the solution set) are proved from the hypothesis A (B0_of_A, Ba_of_A): B's chart-level section  |
| V3_99 | restated | neither | incomparable | A = theorem_3_54_ker_eq_tangent ∧ theorem_3_54_nearby_kernel ∧ linAt_eq_germDeriv (germ reading, universes 0). A => B fails on hypotheses and on content: B assumes d_X = 0, a non-tame IsScFredholmSection and IsLinSurjAt, while A's theorems need (f, x0) in good position in a tame chart (IsGoodPositio |
| V3_100 | explicit | A ⇒ B only | A_stronger | A = isInGoodPositionIn_of_subset ∧ isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero ∧ isGoodPositionGerm_of_isLinSurjAt ∧ IsGoodPositionGerm.isLinSurjAt ∧ isGoodPositionGerm_iff_isLinSurjAt ∧ IsLinSurjAt.linAt_surjective (universes 0, germ reading); the r2 blind B states, for a tame bundle, an I |
| V3_101 | stronger | neither | incomparable | A = theorem_3_19_of_surjective ∧ theorem_3_56_of_surjective ∧ theorem_3_56_tame (universes 0; germ reading). B's (3.56) conjunct follows from A (A_to_B_3_56 in the file: theorem_3_56_of_surjective when S ≠ ∅, the empty atlas when S = ∅, ∂X = ∅ ⇔ d_X ≡ 0, open-chart glue). Its (3.19) conjunct does no |
| V3_103 | explicit | neither | incomparable | A = eight auxiliary theorems (tame germ data are germ data; tame good position ⇒ good position / tame germ; the filled hypothesis ⇒ tame good position; identity base retraction is tame; IsTame.congr; nonempty_kerEquiv; the bundleEven example tame_atlas_no_germData_in_atlas_chart), universes 0; B = f |
| V3_105 | explicit | A ⇒ B only | A_stronger | A = theorem_3_15_tame ∧ StrongBundle.IsScFredholmGermTame.sectionAdd (universes 0); at HEAD both and B's IsScFredholmSectionTame use the germ reading of Definitions 3.50/3.51 (filling and sc⁺-section as germs, data in a tame chart). B is theorem_3_15_tame with the extra hypothesis IsTameStrongBundle |
| V3_106 | explicit | A ⇒ B only | A_stronger | A = theorem_3_18_tame ∧ PullbackChartData.ofProd_isTame ∧ IsScFredholmGermTame.param ∧ IsScFredholmSectionTame.param (universes 0); at HEAD the tame notions on both sides are the germ reading of Definitions 3.50/3.51 (filling and sc⁺-section as germs in a tame chart). B is theorem_3_18_tame with the |
| V4_1 | restated | equivalent | equivalent | A = hasCornerStructure_iff ∧ HasCornerStructure.isTame ∧ IsCornerChart.isTameRetract ∧ IsCornerChart.isScPlusRetract (universe 0); IsCornerChart/HasCornerStructure are vocabulary. B: HasCornerStructure ↔ B's corner atlas (pairwise compatible, covering charts of P on relatively open subsets of partia |
| V4_2 | same | equivalent | equivalent | A = IsCornerChart.contDiffOn_transition ∧ isRelOpenInQuadrant_overlap (universe 0). A ⇒ B: B's corner charts (any finite-dimensional sc-model with onto inclusions) are replaced by project corner charts id ∘ χ over ScBanach.const E₀ (compDiffeo with isScDiffeoQuadrant_toConst) with definitionally the |
| V4_3 | restated | equivalent | equivalent | A = finiteDimensional_lvl ∧ toBase_surjective ∧ mem_smooth_of_finiteDimensional (no universe parameters); B's uniqueness half says every inclusion E_m → E₀ of an sc-structure on a finite-dimensional E₀ is a linear homeomorphism. A ⇒ B builds that equivalence as LinearEquiv.ofBijective (injective by  |
| V4_5 | stronger | equivalent | equivalent | A = theorem_4_2 ∧ theorem_4_2_general (universe 0); B is the same equivalence (i) HasCornerStructure ↔ (ii) X₀ = X_∞, 1₀¹ sc-smooth, centred tame charts with T₀O finite-dimensional in good position, for tame X. Differences are only bookkeeping: smoothSet = univ vs ∀ x, x ∈ smoothSet; A fixes one jun |
| V4_6 | stronger | A ⇒ B only | A_stronger | A = remark_4_3_levelVal.{0} ∧ remark_4_3_isScDiffeo.{0} ∧ remark_4_3_const ∧ remark_4_3_example ∧ remark_4_3_retract_example ∧ IsLossFamily.isScSmooth ∧ exists_retract_smooth_not_scPlus_of_data ∧ mem_shift_levelSet_iff.{0} (liftOne, toLevelOne vocabulary). A ⇒ B (proved): B's clauses 1, 2, 4 from th |
| V4_8 | explicit | A ⇒ B only | A_stronger | A = exists_scPlus_deriv ∧ isCompactOperator_deriv ∧ finiteDimensional_range_of_isCompactOperator_of_idem.{0}. A ⇒ B is glue: at o₁ with ι₁o₁ ∈ O the point is smooth (lemma_4_7_i) and in U₁, A's sc⁺-operator S : E → E¹ with S.toScOperator 0 = Dr(o) yields B's level maps E_m → E_{m+1} and E_m → E_m (S |
| V4_9 | restated | equivalent | equivalent | A = type of ScRetraction.IsScPlus.mem_lvlSet_succ (r(U_m) ⊆ U_{m+1}); ScRetraction.IsScPlus and MPolyfold.IsScPlusRetractionOn are vocabulary, and B says both agree with the text's definitions. Retraction half: the project's IsScPlus R.U R (canonical lift E.liftOne ∘ r sc-smooth into E¹) is B's 'som |
| V4_10 | same | equivalent | equivalent | A = type of lemma_4_5: ∀ E C T S, T.IsScPlus → T.retract = S.retract → S.IsScPlus. B is the same statement with the equation of retracts oriented the other way (s.retract = t.retract); both directions are one-line term proofs (Eq.symm). Both use the project's ScRetraction.IsScPlus as the notion of s |
| V4_11 | same | equivalent | equivalent | A = IsScPlusRetract.isScPlus ∧ isScPlusRetract_iff_forall (IsScPlusRetract is vocabulary: ∃ R, R.retract = O ∧ R.IsScPlus). B = (project IsScPlusRetract ↔ blind IsScPlusRetractB) ∧ intrinsic-ness. The definitions agree exactly: R.IsScPlus (canonical lift E.liftOne ∘ R sc-smooth into E¹) ↔ B's Defini |
| V4_12 | explicit | equivalent | equivalent | A = lemma_4_7_i ∧ lemma_4_7_ii ∧ lemma_4_7_ii_tangentSpace. (i): A's R.retract ⊆ E.smooth is B's 'every o ∈ O lifts to every level' (mem_smooth_iff). (ii): A's lemma_4_7_ii is B's finite-dimensionality verbatim; A's tangent-space clause is stated for SOME smooth lift o₁ of o, B's for EVERY level-1 o |
| V4_13 | same | equivalent | equivalent | A = proposition_4_8: IsScRetract E C O → (IsScPlusRetract E C O ↔ O ⊆ E_∞ ∧ IsScSmoothRetractMap E C O E¹ C¹ O¹ E.liftOne). Same statement as B up to glue: IsScPlusRetract ↔ B's IsScPlusRetractB (IsScPlus.iff_exists + mem_lvlSet_succ, as in V4_9/V4_11); O ⊆ E_∞ ↔ pointwise lifts (mem_smooth_iff); A  |
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
| V4_34 | restated | equivalent | equivalent | A = proposition_4_15_2 (universe 0): a smooth finite-dimensional submanifold is IsLocallyClosed (Mathlib). B uses the text's definition literally (every a ∈ A has an open V ∋ a with every b ∈ V whose open neighbourhoods all meet A lying in A, i.e. V ∩ closure A ⊆ A). The two notions of 'locally clos |
| V4_35 | same | equivalent | equivalent | A = proposition_4_15_3 (universe 0): Subtype.val '' (subPolyfold hA.isSubMPolyfold).boundary ⊆ P.boundary for a smooth submanifold with [ParacompactSpace A]. B states the same pointwise with degeneracy indices (1 ≤ d_A(a) → 1 ≤ d_X(a)), quantifying over an arbitrary proof hA : IsSubMPolyfold A and t |
| V4_36 | same | equivalent | equivalent | A = proposition_4_15_4 (universe 0): for every junk value x₀ ∈ A¹, every point of A is smooth for the induced structure and toLevelOne x₀ : A → A¹ is sc-smooth. B: A = A_1 for the induced structure and toLevelOne a₀ is sc-smooth for every a₀. A ⇒ B: the sc-smoothness is A's; B's A = A_1 cannot be re |
| V4_38 | restated | neither | equivalent | Definition item with one listed theorem: A = type of SubmanifoldData.isGoodPositionChart_iff (universe 0), the explicit chart form 'Dt(z)E in good position to C_z inside Dr(z)E'; it is orthogonal to B, so A_to_B is B_holds (no use of A) and B_to_A re-proves A outright from tangentSpace_eq_coe_submod |
| V4_40 | same | neither | equivalent | Definition item: only IsTameSubmanifold is listed, so A = True and both implications are vacuous; the content is B itself, proved outright (B_holds). The project's IsTameSubmanifold A is ∃ hA : IsSmoothSubmanifold A, (subPolyfold hA.isSubMPolyfold).IsTame; B's text reading is ∃ hA : IsSubMPolyfold A |
| V4_41 | same | A ⇒ B only | A_stronger | A = theorem_4_18 ∧ hasCornerStructure_of_centred_isInGoodPosition ∧ IsGoodPositionAt.isInGoodPosition_of_tame (universe 0). theorem_4_18 alone is equivalent to B: A→B only needs the paracompactness of A, which B packages existentially and which holds for every subset (paracompactSpace_subtype, via m |
| V4_42 | explicit | A ⇒ B only | A_stronger | A = isGoodComplement_sup_range ∧ lemma_4_19 ∧ IsInGoodPositionIn.isInGoodPosition: general linear algebra in any sc-Banach space with a presented partial quadrant C, a bounded idempotent π with (1 − π)E ⊆ E₀ (minimal subspace at 0) and N ⊆ πE in good position to C inside πE with an ALGEBRAIC good co |
| V4_43 | explicit | A ⇒ B only | A_stronger | A = tangentSpace_eq_range_graph ∧ remark_4_20 (universe 0) ∧ lemma_3_55_relOpen ∧ IsInGoodPosition.isInGoodPositionIn_of_le. The main conjunct remark_4_20 is equivalent to B: B uses its own chart reading IsGoodPositionAtB of Definition 4.16 (verbatim the blind V4_38's), which for tame X, smooth A an |
| V4_44 | restated | neither | equivalent | Definition item: only IsGeneralPositionRetractAt, SubmanifoldData.IsGeneralPositionChart and MPolyfold.IsGeneralPositionAt are listed, so A = True and both implications are vacuous (flagged); the content is B, proved outright (B_holds): for a smooth submanifold A and a ∈ A, the project's IsGeneralPo |
| V4_46 | restated | neither | incomparable | A consists of level-0 coordinate lemmas at the corner 0 (E_0 = {λ = 0}, adding E_0-vectors preserves C and d_C, λ/_N onto ℝⁿ when N + E_0 = E, a CLOSED ALGEBRAIC complement Y ⊆ E_0 that is good, d_{N∩C} = d_C on the slice with the CONSTANT sc-structure on N); B states the text's step at the sc level |
| V4_47 | explicit | A ⇒ B only | A_stronger | A = exists_scComplement_le ∧ isGeneralPositionRetractAt_of_sup_eq_top: general sc-linear algebra (any finite-dimensional smooth N, any sc-subspace TR, M = N + TR) and its chart form for an arbitrary sc-retract Q ⊆ R.retract, R tame for T, at a smooth level-1 point y with T_yQ + E_0 = E. B is the ins |
| V4_49 | restated | A ⇒ B only | A_stronger | A = sup_minimalSubspaceWith_eq_top ∧ sup_minimalSubspaceWith_eq_top_graph ∧ theorem_4_22_chart: statements about an arbitrary sc-space with a tame retraction R (presentation T) and an sc⁺-retraction t onto Q ∋ 0 with T₀Q in general position: N + E_0 = E, a CLOSED GOOD complement Y = ker p ⊆ E_0, the |
| V4_50 | restated | neither | incomparable | Statements (2) d_X = d_A on A ∩ U and (3) general position on A ∩ U agree and are derived from A (A_to_B23, rt_check OK; paracompactness of A from metrizability). (1) and (4) differ in content: A counts the faces of the chart's MODEL RETRACT O through ψ(x) = 0 (Corollary 2.41 in a tame chart centred |
| V4_53 | restated | equivalent | equivalent | A = type of prod_rn_isTame (universe 0; fibreSet, rnPres, IsStratRegularPoint, IsStratRegularValue are vocabulary). B = (i) ℝᵐ × X with the product structure is tame for tame X ∧ (ii) the project's IsStratRegularPoint is the text's 'regular point of p_σ' in a product chart. (i) is literally A up to  |
| V4_54 | stronger | A ⇒ B only | A_stronger | Hypotheses agree (both read the misprinted (2) as general position of A at every point, Definition 4.21; /λ/ = √Σλᵢ² vs Σλᵢ² ≤ ε²; B's ∃-paracompact IsTameSubmanifold gives A's IsSmoothSubmanifold, instance and tameness). Conclusions differ in one point: A's Σ consists of stratified regular values ( |
| V4_55 | explicit | A ⇒ B only | A_stronger | A = quotDim_le_finrank_of_eq_sup ∧ remark_4_24_chart ∧ remark_4_24_codim ∧ remark_4_24 ∧ remark_4_24_not_mem_boundary (universe 0). A ⇒ B is proved entirely from A plus chart-change glue: B quantifies over EVERY tame chart and presentation for (a) and over EVERY chart (tame or not) for (b), (c), whi |
| V4_57 | restated | neither | incomparable | A = finrank_stratSub ∧ measure_image_stratCritSet (no universe parameters) is the finite-dimensional MODEL of the step: in a finite-dimensional V with onto coordinates ℓ, dim stratSub ℓ σ + #σ = dim V, and for f ∈ C^∞(O ∩ {ℓ ≥ 0}) the stratified critical values f(stratCritSet) are null for every Haa |
| V4_58 | stronger | A ⇒ B only | A_stronger | A = exists_solution_smooth ∧ theorem_3_78_smooth ∧ exists_radii ∧ Radii.contDiffOn_τ ∧ theorem_3_78 (no universe parameters). A ⇒ B: B is Theorem 3.78 for every j ∈ ℕ ∪ {∞}, j ≥ 1, in the blind coordinates; the case j = ∞ is an instance of theorem_3_78_smooth, finite j of theorem_3_78 (glue of V3_63 |
| V4_62 | restated | neither | incomparable | A = isGeneralPositionRetractAt_slice (no universe parameters) is a chart lemma: for retractions t (onto the chart model of A in ℝᵐ ⊕ E, inside id × r with r tame for T_X) and τ (sc⁺, onto the chart model of the fibre), general position of t at z plus stratified regularity plus the hypothesis hTQ (T_ |
| V4_63 | restated | neither | incomparable | A = exists_local_family (universe 0): for X tame, A ⊆ ℝᵐ × X a smooth submanifold in general position everywhere (no compactness, no (1), no tameness of A), each z₀ ∈ A has an open U and a null CV with FibreLocal at every z ∈ A ∩ U, z.1 ∉ CV (stratified regularity T_zA ∩ E_z ↠ ℝᵐ, local sc⁺-data for |
| V4_64 | stronger | B false | A_narrower | A = theorem_4_23_of_subset (universe 0): Theorem 4.23's conclusions over any parameter set S, proved with a COUNTABLE subcover of A (A is second countable). B formalizes the text's covering step literally: every choice of open neighbourhoods U(z) of the points of K = {z ∈ A : /p(z)/ ≤ ε} has a finit |
| V5_3 | restated | B ⇒ A only | equivalent | A = IsAuxNorm.nonneg ∧ IsAuxNorm.smul (universes 0); the listed IsCompleteFiberNorm/IsAuxNorm are vocabulary. The real comparison is B itself, proved outright (B_holds): the blind topology oneTopology on Y_{0,1} is definitionally the project's instance on Bd.One (topology_eq : rfl; (E.prod F.shift)  |
| V5_4 | same | A ⇒ B only | A_stronger | A = lemma_5_2 ∧ exists_le_mul_norm_liftOne ∧ IsAuxNorm.exists_norm_liftOne_le ∧ IsAuxNorm.exists_bounds ∧ lemma_5_2_literal (universes 0). lemma_5_2_literal is B itself (B's fiberNormOne c y unfolds to ‖(c.liftOne y).2‖): B_gives_lemma_5_2_literal, and A ⇒ B could be read off it; the recorded A_to_B |
| V5_5 | same | A ⇒ B only | A_stronger | A = proposition_5_3_exists ∧ continuous_gluedNorm ∧ isCompleteFiberNorm_gluedNorm ∧ gluedNorm_bounds (universes 0, chart index type also at 0). The first conjunct is B exactly (every strong bundle, no tameness, ∃ N, IsAuxNorm N), so A ⇒ B is projection. B ⇒ A fails because the other three conjuncts  |
| V5_6 | same | equivalent | equivalent | A = proposition_5_3_compare (universes 0) is literally B: for auxiliary norms N₀, N₁ of any strong bundle (no tameness) there is a continuous f : X → ℝ, f > 0, with f(P w)·N₀(w) ≤ N₁(w) ≤ f(P w)⁻¹·N₀(w) for all w ∈ Y_{0,1}. Both directions are instantiation; same setting, same instance arguments. |
| V5_7 | explicit | A ⇒ B only | A_stronger | A = IsProper.isWeaklyProper (for any continuous f) ∧ IsWeaklyProper.isCompact_solutionSet (universes 0); AuxLe/IsWeaklyProper/IsProper are vocabulary. B's definitional conjuncts hold by Iff.rfl (solSetB = solutionSet, suppB = closure{¬IsZeroAt}, NLe = AuxLe, same quantifier structure over auxiliary  |
| V5_10 | stronger | A ⇒ B only | A_stronger | Same notions on both sides (IsScFredholmSection — at HEAD the germ reading of Definition 3.14 —, IsProper, IsWeaklyProper, solutionSet = {x / IsZeroAt P f x}); A is theorem_5_5 (compact solution set => proper) and theorem_5_5_iff (proper <-> weakly proper <-> compact solution set) for an arbitrary M |
| V5_11 | same | equivalent | equivalent | Both: for an sc-Fredholm section (IsScFredholmSection, germ reading on both sides; no tameness on either side) and a zero x there are open, nested U(i) containing x such that the closure in X_0 of the zeros in U(i) is a compact subset of X_i with the project's level topology. A phrases it as 'the cl |
| V5_12 | stronger | A ⇒ B only | A_stronger | A = theorem_5_7 ∧ tendsto_smoothLevel_iff ∧ smoothLevel_topology_eq ∧ metrizableSpace_smoothLevel (universes 0). Main content agrees: for an sc-Fredholm section (IsScFredholmSection, the germ reading on both sides) with S = f⁻¹(0) compact in X₀, S ⊆ X_∞ and S is compact in X_∞; B's own inverse-limit |
| V5_13 | same | A ⇒ B only | A_stronger | A = corollary_5_8 ∧ corollary_5_8_two ∧ StrongBundle.solutionSet_sectionShift ∧ isCompact_solutionSet_level (universes 0); B (r2) = over a tame X, for sc-Fredholm f (germ reading) with compact f⁻¹(0), for every i the iterated index raise f^i (P^{i+1} = (P^i).shift, f^{i+1} = sectionShift f^i) is sc- |
| V5_14 | same | A ⇒ B only | A_stronger | A = the twelve theorems of the decls (universes 0), among them corollary_5_8_isScFredholmSection (f sc-Fredholm ⇒ f¹ sc-Fredholm on P¹ = StrongBundle.shift, germ reading, no tameness/compactness); B (r2) = for sc-Fredholm f and every i, the iterated f^i is sc-Fredholm on the iterated P^i (no tamenes |
| V5_16 | restated | neither | A_stronger | Definition item. A = AdmitsBumpFunctions.weak ∧ admitsBumpFunctionsWeak_of_dense ∧ AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth ∧ admitsBumpFunctions_of_hilbert (universe 0); AdmitsBumpFunctions, AdmitsBumpFunctionsWeak, HasBumpAt vocabulary. The definitions agree with B's by Iff.rfl (AdmitsBumpF |
| V5_17 | same | B ⇒ A only | A_narrower | Same conclusion on both sides (sc-smooth f : X -> [0,1], f(x) = 1, tsupport f ⊆ U, f = 1 near x), same setting (no tameness). The only difference is the hypothesis: A (proposition_5_30 / proposition_5_10, universe 0) assumes AdmitsBumpFunctions (a bump with f(x) != 0, the project's reading of Def. 5 |
| V5_20 | stronger | neither | incomparable | A = lemma_5_11 (universes 0): for ANY strong bundle (no tameness), assuming AdmitsBumpFunctions (bump with f(x) != 0), an auxiliary norm, smooth x and e in (Y[0])_inf over x, it gives an sc+-section s with s(x) = e, supp s ⊆ U and N(s(y)) < N(e) + eps for EVERY y. B assumes tameness of base and bund |
| V5_21 | restated | A ⇒ B only | A_stronger | A = allowableDist_le_iff ∧ TrivialBundle.not_completeSpace_allowableSections ∧ completeSpace_allowableSections_empty ∧ TrivialBundle.completeSpace_allowableSections_point (universes 0); allowableSections, sectionDistAt, allowableDist, allowableMetric vocabulary. Notions agree: Γ^{+,1}_U(P) = B's Gam |
| V5_22 | restated | A ⇒ B only | A_stronger | A = remark_5_12 ∧ IsAuxNorm.auxLe_of_sectionAdd ∧ IsInAllowableCompletion.isClosed_solutionSet_sectionAdd ∧ remark_5_12_completion ∧ remark_5_12_of_isScFredholmSection (universes 0); IsInAllowableCompletion is B's InCompletion (inCompletion_of). B: f sc-Fredholm (germ reading, as in A) with compact  |
| V5_23 | restated | A ⇒ B only | A_stronger | A = IsLinSurjAt.linAt_surjective (universes 0): at a zero y of an sc-smooth section where the linearization is onto in SOME strong bundle chart (IsLinSurjAt), it is onto in EVERY chart around y at the level-1 lift of φ'(y). B: for sc-smooth g, the project's IsTransversal g (IsLinSurjAt at every zero |
| V5_29 | explicit | neither | incomparable | A = theorem_5_13_generic (universes 0): the generic family form (for every s₀ with N(s₀) ≤ 1−ε a finite family s₀ + Σλᵢtᵢ that is allowable, transversal, with compact solution set which, if nonempty, is a tame manifold without boundary of dimension the Fredholm index, for a.e. small λ), assuming str |
| V5_30 | explicit | B ⇒ A only | A_narrower | A = theorem_5_13 ∧ StrongBundle.allowableDist_le_iff (universes 0). theorem_5_13 assumes AdmitsBumpFunctions (a bump with f(x) ≠ 0) and IsScFredholmSectionTame f (now the germ reading with tame germ data; changed in place), B assumes AdmitsBumpFunctionsWeak (literal 'not identically zero') and IsScF |
| V5_31 | restated | neither | equivalent | A = IsGeneralPositionGerm.isLinSurjAt (universes 0): general position at y gives IsLinSurjAt at y, a projection of the definition. B says that at zeros the project's IsGeneralPositionGerm equals the text's notion as B reads it (some tame strong bundle chart, a level-1 lift z, the linearization onto  |
| V5_36 | restated | neither | A_stronger | A = IsParamGP.comp ∧ isGeneralPositionGerm_paramSection_of_isParamGP ∧ isParamGP_of_isGeneralPositionGerm ∧ exists_sections_isParamGP (universes 0). B has four parts: (1) the project's IsParamGP equals the text's (i)–(ii) in a chart centred at the point; (2) (i)–(ii) are preserved under Fin.append;  |
| V5_38 | explicit | neither | incomparable | A = theorem_5_18 (universes 0): over a tame X with strong bump functions (f(x) ≠ 0), for every s₀ with N(s₀) ≤ 1−ε a finite family s₀ + Σλᵢtᵢ such that for a.e. small λ the perturbation is allowable and SolutionSetInGeneralPosition holds (transversal, (f+s, x) in general position at every zero, S co |
| V5_39 | explicit | neither | incomparable | Both have a compact solution set, an auxiliary norm, tame germ data (IsScFredholmSectionTame, the germ reading on both sides), an open U with S_{f+s} compact on Γ^{+,1}_U, and a ρ-dense set of perturbations in general position at every zero. A => B fails only on bump functions: B assumes AdmitsBumpF |
| V5_40 | stronger | neither | incomparable | A is theorem_5_19 ∧ IsGoodPositionGermTame.congr_nhds (universes 0; germ reading of Definitions 3.51/3.53 on both sides), in generic form. Assuming strong bump functions (f(x) ≠ 0) and NO tameness, it gives a finite family t_i with supports disjoint from ∂X such that, for a.e. small λ, s_λ = Σλᵢtᵢ i |
| V5_41 | restated | neither | A_narrower | A = IsGenCompactHomotopy.isCompact_solutionSet_restrict (universes 0): the restricted problems have compact solution sets. This is a corollary of the definition and says nothing about whether the definition is correct. B says the project's IsGenCompactHomotopy equals B's notion. The two definitions  |
| V5_42 | explicit | A ⇒ B only | A_stronger | A = lemma_5_23 ∧ ne_zero_of_isCompl_ker ∧ exists_isCompl_ker_of_ne_zero (universes 0): linear algebra on ARBITRARY real modules. B is the chart instance at a smooth zero: (1) a one-dimensional SMOOTH sc-complement Z of ker dt(x) in T_zO, split on every level, exists iff dt(x) ≠ 0 on T_zO; (2) a uniq |
| V5_44 | restated | neither | incomparable | A = exists_scPlusSection_linAt ∧ lemma_5_24 (universes 0). B is Lemma 5.24 in the setting of Lemma 5.23: tame strong bundle, AdmitsBumpFunctionsWeak, f with tame germ data (germ reading), x a smooth zero, Z a smooth line splitting T_zO = Z ⊕ ker dt(x), b : T_xS → Z with dt∘b = τ, and any open V ∋ x. |
| V5_45 | restated | neither | incomparable | A ⇒ B fails for two genuine reasons. (1) B assumes only AdmitsBumpFunctionsWeak (f ≢ 0), but A needs AdmitsBumpFunctions (f(x) ≠ 0), and the project has only strong ⇒ weak. (2) B reads 'an associated open neighbourhood U' universally: for EVERY open U ⊇ S_f with S_{f+s} compact for all s ∈ Γ^{+,1}_U |
| V5_46 | stronger | A ⇒ B only | A_stronger | A = isInGoodPositionIn_of_scComplement_le_reduced ∧ IsGeneralPositionGerm.isGoodPositionGerm ∧ IsGeneralPositionGerm.isGoodPositionGermTame (germ theorems at universes 0). B is pointwise: for a tame strong bundle and f with tame germ data, at a zero, IsGeneralPositionGerm ⇒ IsGoodPositionGermTame. B |
| V5_47 | restated | neither | equivalent | Definition item: only MPolyfold.IsScSmoothPartitionOfUnity and MPolyfold.AdmitsScPartitionsOfUnity are listed, so A = True and both implications are vacuous. The content is B itself, proved outright as B_holds: the project's notion (Mathlib PartitionOfUnity ι X, subordinate, every ρᵢ sc-smooth into  |
| V5_50 | same | neither | equivalent | Definition item: only HasContDiffBump and AdmitsContDiffPartitionsOfUnity are listed, so A = True and both implications are vacuous. The content is B itself, proved outright as B_holds: the project's HasContDiffBump V k (∃ f, ContDiff ℝ k f ∧ f ≠ 0 ∧ IsBounded (support f)) is B's HasCkBumpB V k (∃ f |
| V5_51 | restated | neither | incomparable | A is the type of the listed lemma closure_inter_ball_subset: O ∩ cl B(z, r/2) ⊆ O when B(z, r) lies in the open W' with C ∩ W' the domain of a retraction onto O. It has no universe parameters and says nothing about bump functions. B claims the project's LocalModel.HasBumpProperty (f(x) ≠ 0) equals t |
| V5_52 | explicit | neither | incomparable | The two sides read 'f ≠ 0' differently. A (theorem_5_34, universe 0) uses the strong reading: AdmitsBumpFunctions and LocalModel.HasBumpProperty, both with f(x) ≠ 0. B uses the literal reading of Definitions 5.29/5.33: AdmitsBumpFunctionsWeak and HasBumpPropertyWeak, both with f not identically zero |
| V5_53 | restated | A ⇒ B only | A_stronger | A is hasBumpProperty_of_quadratic ∧ proposition_5_35 ∧ admitsBumpFunctions_of_hilbert (the last at universe 0). A ⇒ B is proved using A, and the derivation has two parts. First, proposition_5_35 applies to B's Hilbert E₀ (‖v‖² = b(v, v); B's symmetry of b is unused) and gives the pointwise bump prop |
| V5_54 | restated | neither | equivalent | Definition item: only LocalModel.HasApproxProperty is listed, so A = True and both implications are vacuous. The content is B itself, proved outright as B_holds. The two definitions differ only in how the open V ⊆ O is presented. The project uses an open W ⊆ E₀ with cl_E(O ∩ W) ⊆ O and supports (tak |
| V5_55 | narrower | B false | incomparable | A is hasApproxProperty_restrict ∧ MChart.isClosed_inter_preimage, both at universe 0. hasApproxProperty_restrict gives the approximation property only for a chart restricted to an open s with cl_X(s) ⊆ dom φ. B is false (not_B, as its author predicted). It reads the text's 'the sc-smooth function f  |
| V5_56 | restated | equivalent | equivalent | A is the conjunction (universe 0) of the project's four lemmas for (ii)=>(i): exists_small_nhds, exists_approx, exists_isScSmoothMap_urysohn and admitsScPartitionsOfUnity_of_approx. B is the text's quotient construction (W, Q, f, g, γ = ĝ/Σĝ) plus conclusion (i). The project's proof is different (Ur |
| V5_57 | restated | equivalent | equivalent | Both sides use the same notions, AdmitsScPartitionsOfUnity (Definition 5.28) and LocalModel.HasApproxProperty (Definition 5.36). The only difference is how 'an atlas' is written. A (theorem_5_37, universe 0) uses a set S of charts of the structure (PX.IsChart) covering X. B uses an MAtlas A with A.E |
| V5_58 | explicit | equivalent | equivalent | A (proposition_5_38; it has no universe parameter, LocalModel lives in Type) and B make the same claim: for every local model M, if E_0 admits C^infinity partitions of unity (AdmitsContDiffPartitionsOfUnity (M.E 0) ⊤), then M.HasApproxProperty. B writes M.E.lvl 0 for the project's M.E 0. That is the |
| V5_59 | restated | equivalent | equivalent | A is mem_cZero_iff ∧ norm_cZero (universe 0). cZero, IsCoordinatewiseContDiffEmbedding and TorunczykStatement are vocabulary that B compares with its own notions. (1) Elements: mem_cZero_iff is literally B's c0SetB condition; that every function satisfying it is bounded, hence lies in ℓ^∞, is proved |
| V5_60 | same | neither | equivalent | Definition item: only IsWCG and IsReflexive are listed, so A = True and both implications are vacuous (flagged). The content is B, proved outright (B_holds): for every real Banach space V : Type, the project's IsWCG V is B's IsWCGB V. The two differ only in how 'weakly compact' is written. The proje |
| V5_61 | same | equivalent | equivalent | Both sides use the project's IsReflexive and IsWCG. A (all three theorems at universe 0) is stated for every real normed space; B, following the text's 'E a Banach space', only for complete ones. A => B is specialization. B => A has three parts. (i) A reflexive normed space is automatically complete |
| V5_63 | narrower | B ⇒ A only | A_narrower | Both sides use the same approximation property, and their Hilbert notions agree: the project asks for a continuous bilinear b with //v//^2 = b(v,v), B also asks b to be symmetric, and symmetrizing to (b + b^T)/2 makes them equal (hilbert_iff). The real difference is that corollary_5_44 takes the cit |
