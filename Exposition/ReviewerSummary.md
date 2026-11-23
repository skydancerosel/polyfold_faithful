# Reviewer summary: the first hour

Lean checks every proof. What a person has to check is that the definitions and the main statements
say what Hofer, Wysocki and Zehnder mean. The full list is [`ReviewerChecklist.md`](ReviewerChecklist.md)
(about 200 statements and 500 definition rows, in tiers). This page is the short version: the notions
everything rests on, one Lean statement for each main theorem with its verdict, and the readings we
adopted. Book references use the Springer edition (2021): number, then page. Each row id (V3.13, …)
is an entry of the comparison ([`Comparison.md`](Comparison.md), or `polyfold-beside-lean.html` in a
browser), which gives the book's statement, the Lean statement and every difference.

## 1. The machine checks

From the project folder (Lean and Mathlib `v4.33.1`; `lake exe cache get` once first):

```bash
lake build Polyfold
```

```bash
lake env lean -DmaxSynthPendingDepth=3 Polyfold/Test.lean
```

The second command prints the axioms of every theorem; each must list only `propext`,
`Classical.choice` and `Quot.sound` (or a subset): no `sorryAx`, no project axioms. The declarations
whose statements a reader has to check are collected in
[`checklist/TrustedBase.lean`](checklist/TrustedBase.lean).

## 2. The core definitions

R1–R12 refer to the readings of section 4.

| Notion | Book | Lean | Reading adopted | Rows |
|---|---|---|---|---|
| sc-Banach spaces | Def. 1.1.1, p. 5 | `Polyfold.ScBanach` | a family of Banach spaces with injective compact inclusions in place of nested subspaces; equivalent | V1.1 |
| sc¹ and sc-smooth maps | Def. 1.1.15 and the definition after it, p. 10 | `Polyfold.IsSc1`, `Polyfold.IsScSmooth` | the family of derivatives is part of the data; its uniqueness is proved | V1.13, V1.14 |
| Degeneracy index | Def. 1.3.3, p. 14; Def. 2.4.1, p. 44 | `Polyfold.degIndex`, `Polyfold.MPolyfold.degIndex` | over all charts of the maximal atlas | V1.21, V2.26 |
| sc-smooth retractions and retracts | Defs. 2.1.1, 2.1.3, pp. 21–22 | `Polyfold.ScRetraction`, `Polyfold.IsScRetract` | as in the book | V2.1, V2.2 |
| M-polyfolds | Def. 2.3.4, p. 35 | `Polyfold.MPolyfold` | one atlas represents its class | V2.12 |
| Tame retractions, tame M-polyfolds | Defs. 2.5.2, 2.5.7, pp. 53, 57 | `Polyfold.ScRetraction.IsTame`, `Polyfold.MPolyfold.IsTame` | independent of the presentation (proved) | V2.40, V2.43 |
| Strong bundles | Defs. 2.6.4, 2.6.5, pp. 67–68 | `Polyfold.StrongBundleChart`, `Polyfold.StrongBundle` | the [1]-transition condition stated | V2.57, V2.58 |
| sc⁺-sections | Def. 2.6.6, p. 68 | `Polyfold.StrongBundle.IsScPlusSection` | chart by chart, sc-smooth into `Y[1]` | V2.59 |
| sc-Fredholm germs | Def. 3.1.11 (with 3.1.4, 3.1.6), p. 96 | `Polyfold.StrongBundle.IsScFredholmGerm` | germ reading (R1) | V3.13 |
| sc-Fredholm sections; tame germ data, good position | Def. 3.1.16, p. 97; Defs. 3.6.3, 3.6.4, 3.6.6, pp. 135–136 | `Polyfold.StrongBundle.IsScFredholmSection`, `Polyfold.StrongBundle.IsScFredholmSectionTame`, `Polyfold.StrongBundle.IsGoodPositionGermTame` | germ data and good position in a tame chart (R2); the 2021 text read literally is `Polyfold.StrongBundle.IsScFredholmSection2021` | V3.16, V3.47, V3.103, V3.110 |
| Auxiliary norms; controlled compactness | Def. 5.1.1, p. 205; Def. 12.2.1, p. 570; Def. 15.3.1, p. 691; Def. 16.6.3, pp. 736–737 | `Polyfold.StrongBundle.IsAuxNorm`, `Polyfold.EpStrongBundle.IsAuxNorm`, `Polyfold.SBLocalization.ControlsCompactness`, `Polyfold.StrongPolyfoldBundle.ScSection.ControlsCompactness` | as in the book | V5.3, V12.3, V15.20, V16.75 |
| sc-smooth bump functions | Defs. 5.3.1, 5.5.2, pp. 216, 229 | `Polyfold.MPolyfold.AdmitsBumpFunctions` | read pointwise (R3) | V5.16 |
| Orientations (Chapter 6) | Defs. 6.4.2, 6.6.2, 6.6.16, pp. 246, 263, 274 | `Polyfold.FredholmOrientation`, `Polyfold.ChartPoint.Or`, `Polyfold.IsSectionOrientation` | `DET(f, x)` formed at a chart point | V6.9, V6.31, V6.60 |
| Ep-groupoids | Def. 7.1.3, p. 288 | `Polyfold.EpGroupoid` | condition (3) per point | V7.3 |
| Strong bundles over ep-groupoids; local regularity | Defs. 8.3.1, 8.4.2, pp. 375, 382 | `Polyfold.EpStrongBundle`, `Polyfold.EpStrongBundle.IsLRLocal` | (LR) as printed (R6) | V8.20, V8.48 |
| Branched ep⁺-subgroupoids | Def. 9.1.2, p. 402 (tame and oriented: Defs. 9.3.2, 9.3.6) | `Polyfold.EpGroupoid.IsBranchedEpSubgroupoid` | as in the book, paracompactness as an instance | V9.1, V9.30, V9.34 |
| Branched integration | Thms. 9.5.4, 9.5.5, Def. 9.5.6, pp. 438–441 | `Polyfold.EpGroupoid.branchedIntegral`, `Polyfold.EpGroupoid.OrientedTameStructure` | "oriented, tame" taken as a local hypothesis at the points of the support | V9.66 |
| sc-Fredholm section functors and their orientations | Def. 12.1.1, p. 569; Def. 12.5.4, p. 594 | `Polyfold.EpStrongBundle.IsScFredholmSectionFunctor`, `Polyfold.EpStrongBundle.definition_12_5_4` | orientation sets from the local linearizations | V8.26, V12.1, V12.25 |
| sc⁺-multisections, structurable ones, over `∂X` | Defs. 13.2.7, 13.3.6, 14.1.3, pp. 610, 615, 642 | `Polyfold.SBLocalization.SymmetricStructureOn`, `Polyfold.SBLocalization.IsStructurable` | index sets non-empty (R4) | V13.22, V13.30, V14.3 |
| Polyfold structures and polyfolds | Defs. 16.1.1, 16.1.3, pp. 705, 707 | `Polyfold.PolyfoldStructure`, `Polyfold.PolyfoldClass` | as in the book | V16.1, V16.4 |
| Strong polyfold bundles | Defs. 16.3.1, 16.3.4, pp. 721–723 | `Polyfold.StrongPolyfoldBundleStructure`, `Polyfold.StrongPolyfoldBundle` | local regularity as printed in Def. 8.4.2 (R6) | V16.37, V16.42 |
| Fredholm sections, sc⁺-multisections and orientations on a polyfold | Defs. 16.5.1, 16.6.1, 16.6.5, pp. 733–739 | `Polyfold.StrongPolyfoldBundle.ScPlusMultisection`, `Polyfold.StrongPolyfoldBundle.FredholmSection`, `Polyfold.StrongPolyfoldBundle.OrientationRep` | an orientation is given on one representative, with Part I's hypotheses there | V16.64, V16.73, V16.77 |
| The invariant of Theorem 16.6.6 | Thm. 16.6.6, p. 739 | `Polyfold.StrongPolyfoldBundle.theorem_16_6_6_statement`, `Polyfold.StrongPolyfoldBundle.CanonicalGermInput`, `Polyfold.StrongPolyfoldBundle.IsCanonicalSolutionSet` | the integrals over a perturbed solution set with the canonical orientation; in the model of the orientation, tame germ data and the index | V16.78, V16.82 |
| GCTs, uniformizers, polyfold constructions (Part IV) | Defs. 17.1.1, 17.1.3, 17.1.6, 17.1.8, pp. 744–747 | `Polyfold.GCT`, `Polyfold.GCT.LocalUniformizer`, `Polyfold.GCT.UniformizerConstruction`, `Polyfold.GCT.PolyfoldConstruction` | `F(α) ≠ ∅` (R11); `Ψ̂` continuous where Lemma 17.1.9 needs it (R10) | V17.1, V17.3, V17.6, V17.8 |
| sc-Fredholm section functors on a GCT | Def. 18.1.1, p. 844 | `Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.IsScFredholmSectionFunctor` | as in the book; tame germ data a separate notion | V18.4 |

## 3. The main theorems

One Lean statement per theorem, the final form (the other forms are in the comparison row). Verdicts:
*as in the book* (hypothesis for hypothesis), *hypotheses explicit* (the same mathematics, with what the
text leaves implicit named), *stronger*, *restated* (the same mathematics in another formulation),
*narrower* (more hypotheses or fewer cases; the condition is named).

| Book | Lean | Verdict | Condition or note | Row |
|---|---|---|---|---|
| Thm. 2.7.13, pp. 83–84 | `Polyfold.MPolyfold.theorem_2_7_13_book` | narrower | (2)–(4) as printed (V2.102); `Φ` onto `θ` for a centred `V`, onto `θ ∩ V^x` in general | V2.89 |
| Thm. 3.1.22, p. 100 | `Polyfold.theorem_3_1_22_book` | restated | the text's hypotheses, germ data in tame charts (R2) | V3.68 |
| Thm. 3.6.8, p. 136 | `Polyfold.theorem_3_6_8_book` | restated | tame germ data (R2); with the 2021 germ data as printed, conclusion (2) does not hold as we read it (V3.130) | V3.48, V3.94 |
| Thm. 3.6.11, p. 140 | `Polyfold.theorem_3_6_11_2021def` | stronger | adds local constancy of the dimension and the parts `S_n` | V3.87 |
| Thm. 5.3.10, p. 220 | `Polyfold.theorem_5_3_10_book_2021def` | hypotheses explicit | `X` tame; density in `ρ` read pointwise; bump functions pointwise (R3) | V5.38 |
| Thm. 5.3.15, p. 223 | `Polyfold.theorem_5_3_15` | stronger | no bump functions on the ends `X_i`; "Morse-type" read through smooth parametrizations | V5.71 |
| Thm. 6.6.18, p. 274 | `Polyfold.theorem_6_6_18` | restated | the natural orientation along paths of zeros; bump functions as in Theorem 6.6.13 | V6.61 |
| Thm. 6.7.1, p. 277 | `Polyfold.theorem_6_7_1` | restated | `X` tame with bump functions, as printed; clause (2) read as in the row | V6.76 |
| Thm. 9.5.17, p. 449 | `Polyfold.EP.theorem_9_5_17_all` | stronger | every ep-groupoid, no partitions of unity (Remark 9.5.19); the printed hypotheses: V9.68 | V9.71 |
| Thm. 9.5.18, p. 450 | `Polyfold.EP.theorem_9_5_18_all` | stronger | the same, effective form under (LUC) | V9.71 |
| Thm. 10.3.19, pp. 493–494 | `Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective` | narrower | an effective target (R9); as printed it does not hold as we read it (V10.65) | V10.66 |
| Thm. 13.5.3, p. 630 | `Polyfold.SBLocalization.theorem_13_5_3` | narrower | stated as an equivalence with "a good system exists", which is needed | V13.46 |
| Thm. 14.1.9, p. 646 | `Polyfold.SBLocalization.theorem_14_1_9` | as in the book | as printed; index sets non-empty (R4) | V14.8 |
| Thm. 15.3.9, p. 698 | `Polyfold.SBLocalization.theorem_15_3_9` | hypotheses explicit | the text's hypotheses; tame germ data inherited | V15.32 |
| Thm. 15.4.3, pp. 702–703 | `Polyfold.SBLocalization.theorem_15_4_3_all` | hypotheses explicit | the standing assumptions of §15.3; index `k` on the support; no partitions of unity | V15.36 |
| Cor. 15.4.4, p. 703 | `Polyfold.SBLocalization.corollary_15_4_4_oriented_collar_all` | hypotheses explicit | all transversal perturbations with `N(Λ) ≤ 1`; index 0 in a signed frame convention (R8); no partitions of unity | V15.37 |
| Thm. 16.4.6, p. 732 | `Polyfold.PolyfoldClass.OrientedRep.theorem_16_4_6_all` | as in the book | as printed | V16.28 |
| Thm. 16.5.7, p. 735 | `Polyfold.StrongPolyfoldBundle.theorem_16_5_7` | as in the book | as printed; Theorem 14.1.9 in every model | V16.71 |
| Thm. 16.6.6, p. 739 | `Polyfold.StrongPolyfoldBundle.theorem_16_6_6_wellDefined_unconditional` | hypotheses explicit | every admissible perturbation; no bump functions, no partitions of unity; in the model of the orientation, tame germ data and the index | V16.78 |
| Thm. 16.6.6, index 0 | `Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional` | hypotheses explicit | the same for counts of points | V16.82 |
| Thm. 17.1.18, p. 756 | `Polyfold.GCT.PolyfoldConstruction.theorem_17_1_18` | as in the book | as stated | V17.21 |
| Thm. 17.2.17, p. 783 | `Polyfold.GCT.PolyfoldConstruction.theorem_17_2_17_hyp` | narrower | `Ψ̂` continuous (R10) | V17.55 |
| Thm. 17.4.26, p. 809 | `Polyfold.GCT.PolyfoldConstruction.theorem_17_4_26` | narrower | `Ψ̂` continuous and centred (R10); faces tame as in Def. 2.5.18 | V17.91 |
| Thm. 17.6.7, p. 823 | `Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_7_book_all` | as in the book | as stated; `n = 1` in a separate form | V17.113 |
| Thm. 17.6.10, p. 824 | `Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_10_book_all` | as in the book | (LUC) of `C`, as the text | V17.116 |
| Thm. 18.1.5, p. 846 | `Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_1_5` | hypotheses explicit | tame germ data; (2) in the model | V18.13 |
| Thm. 18.6.1, pp. 860–861 | `Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction.theorem_18_6_1` | hypotheses explicit | sc-Fredholm with tame germ data; a model-free form in the row | V18.51 |
| Thm. 19.5.1, p. 886 | `Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_5_1` | stronger | without metrizability of `T`; the structure is unique | V19.31 |
| Thm. 19.6.13, p. 900 | `Polyfold.GroupoidalCategory.BasicStrongBundleConstruction.theorem_19_6_13` | stronger | `T` metrizable not needed | V19.61 |
| Thm. 19.7.29, p. 929 | `Polyfold.GroupoidalCategory.CoveringBasicConstruction.theorem_19_7_29_hyp` | restated | compatible uniformizers, as in Def. 19.6.4 (A) (reading of Def. 19.7.11) | V19.89 |

## 4. The readings

Each is a choice where the text admits more than one reading; the comparison row gives the reason, and
[`Findings.md`](Findings.md) the details.

| | Reading | Where |
|---|---|---|
| R1 | sc-smooth germs live on neighbourhoods whose levels may shrink with the level (Defs. 3.1.4, 3.1.6, 3.1.11). Whether this and the whole-chart reading agree for sections sc-smooth on `X` is an open question. | V3.13; Findings, Ch. 3, items 220, 330 |
| R2 | "Tame strong bundle" (used from Thm. 3.6.8 on, not defined in the 2021 text) as the 2014 and 2017 versions define it: the germ data of §§3.6, 6.2, 6.6, 12.5 in a tame chart. | V3.103, V3.130; Findings, Ch. 3, items 382, 388 |
| R3 | Bump functions read pointwise, `f(x) ≠ 0` (Defs. 5.3.1, 12.3.1). | V5.16, V12.10 |
| R4 | Index sets of structured multisections non-empty, as the factor `1/\|I_x\|` of Defs. 13.2.5 and 14.1.3 presumes. | V13.13, V14.3 |
| R5 | The equivalence of Def. 13.3.8, as Def. 14.6.2 and Thm. 14.6.3 use it, also compares the sections, as the step on p. 682 states. | V13.32, V14.43 |
| R6 | Local regularity of Def. 8.4.2 as printed (`IsLRLocal`) in the strong polyfold bundle structure (Def. 16.3.1); the form for maps of `W` follows from it. | V8.48, V16.37; Findings, Ch. 8, items 119, 128, 134 |
| R7 | The lateral term of Stokes' theorem on `[0, 1] × X` (Remark 6.6.19): the integral over the part of the boundary with `0 < t < 1`, a limit of cut-off integrals. | V6.62 |
| R8 | The frame convention for the 1-dimensional cobordism of index 0 (Cor. 15.4.4) in a signed form. | V15.37 |
| R9 | An effective target in Thms. 10.3.19, 10.5.7, the uniqueness sentence after Def. 16.1.2 (§§16.1–16.3) and Prop. 17.1.25. | V10.65, V10.66, V10.67, V16.3, V16.34, V17.28; Findings, Ch. 10, item 17, Ch. 16, item 1 |
| R10 | `Ψ̂` continuous in Def. 17.1.8, as Lemmas 17.1.9 and 17.2.10 use it. | V17.9, V17.47 |
| R11 | A covering family has a uniformizer at every object, `F(α) ≠ ∅` (§17.1, Prop. 17.3.4, Thm. 19.2.2). | V17.6, V17.60, V19.12 |
| R12 | Condition (v3) of Def. 19.4.1 asks for a limit in the fibre over `z`. | V19.23 |

The smaller conditions (the README's table *Where our reading needed a condition the text does not
print*): `V` centred in (2.44) and Prop. 2.7.12 (V2.89); Remark 2.4.8 (V2.33); Lemma 3.8.1 (V3.123);
`T_R` Hausdorff in Lemma 7.2.11 (V7.76); uniqueness in Prop. 9.1.11 among the decompositions the proof
builds (V9.9); sheets of one dimension in Lemmas 9.3.4, 9.4.4, 9.5.2 (V9.32, V9.42, V9.50); Prop.
11.1.6 (V11.6); tame in the sense of Def. 2.5.18 in Lemma 17.4.13 (V17.78); the continuity of Def.
12.2.1 in Lemma 18.1.8 (V18.16); Lemma 19.4.3 (V19.25); compatible uniformizers in Def. 19.7.11
(V19.73); Prop. 19.7.18, Cor. 19.7.20 (3), Thm. 19.7.25 (4b) (V19.80, V19.83, V19.86); the remark
after Lemma 19.7.19 (V19.82).

## 5. Where to look next

* [`ReviewerChecklist.md`](ReviewerChecklist.md): every statement and definition row to check, in tiers.
* [`Comparison.md`](Comparison.md) (`polyfold-beside-lean.html` in a browser): each item of the book
  beside its Lean statement, with the verdict and every difference.
* `ProofByProof.pdf`: each formal proof retold as mathematics, every step tagged with its Lean
  declaration.
* [`Findings.md`](Findings.md): the points left to the reader and the reasons for each reading.
* [`WorkedExample.md`](WorkedExample.md): the orbifold ℂ/ℤ₅ with the section `z ↦ z²`, where the
  invariant of Theorem 16.6.6 is 2/5.
* `polyfold-signoff.html`: the sign-off list, in a browser.
