# Round-trip audit of the main statements of Parts III and IV — report

Layer 1 (statements), by the method of `README.md` and the prompts of `harness/`, unchanged: a blind
writer sees only the book's statement as the comparison quotes it (`book.statement` of
`Exposition/cmp/chNN.json`, the Springer 2021 book) and writes `RoundTrip.<ID>.B`; a separate prover,
not told the verdict, tries `A → B` and `B → A`, where A is the conjunction of the types of the
theorems the comparison row lists (universes at 0); `#rt_check` rejects circular proofs. Blind
writers and provers ran as separate agents; one writer per file.

## Coverage

The items are the comparison rows of the statements of the tiers `partIII` and `partIV` of
`Exposition/checklist/mains.tsv`, mapped to rows exactly as `Exposition/checklist/build_checklist.py`
does (`thmrows`): **129 rows**, V8.48 and 128 rows of Chapters 12–19. V8.48 already had an item
(`Items/V8_48.*`, against the row as it was then, when A was the single witness `isLR_trivial`); its row
now also lists Proposition 8.4.3, so it is audited again as `Items/V8_48_r2.*` on the existing blind
statement `Blind/V8_48.lean` (field `refresh_of`). Every other item is new: `Blind/<ID>.lean`,
`Items/<ID>.lean`, `Items/<ID>.json`. All items were recompiled at commit e1d5ad6 (see "Checks").

Besides the harness fields, the provers from V14.33 on also recorded a field `main`: the comparison of
B with the one conjunct of A that states the text's claim. Many rows of Parts III and IV list, beside
the theorem, its proof steps, more general forms and worked examples; `main` separates a difference
about the theorem from a difference that comes only from these extra conjuncts.

## Results

Against the expected relation from the verdict (*same / explicit / restated* → equivalent,
*stronger* → A ⇒ B only, *narrower* → B ⇒ A only; *partial*: an *incomparable* result on a
*stronger* or *narrower* row):

| | match | partial | mismatch | unresolved | n |
|---|---|---|---|---|---|
| all items | 74 | 4 | 51 | 0 | 129 |

No item is unresolved. Of the 51 mismatches, 2 are rows marked *stronger* or *narrower* where B
and A came out equivalent, 6 differ only through extra conjuncts of the row, 12 have A more general
than the text, 11 differ in the formal statement, and 20 differ only in the blind writer's reading.
These counts include the refreshed items and the verdicts revised after the first pass (see
*Refreshed items* below); the two tables that follow are those of the first pass.

Proved directions (vacuous directions not counted): both 66, A ⇒ B only 20, B ⇒ A only 10,
neither 26; for 7 items `not_B` is proved or A ⇒ B is shown not to hold (B does not hold as the blind
writer read the text).

Provers' judgement of content, by verdict:

| | equivalent | A_stronger | A_narrower | incomparable | n |
|---|---|---|---|---|---|
| same | 45 | 9 | 3 | 1 | 58 |
| explicit | 6 | 1 | 7 | 17 | 31 |
| restated | 6 | 7 | 5 | 1 | 19 |
| stronger | 8 | 3 | 0 | 2 | 13 |
| narrower | 1 | 1 | 3 | 3 | 8 |

## Theorem 16.6.6: V16.78 and V16.82

Both rows are *explicit*; both items come out **incomparable** (mismatch), for the same reason.

- **V16.78** (the invariant from the branched integrals). A is 150 theorems; its main form is
  `theorem_16_6_6_wellDefined_unconditional`. The two statements differ in one hypothesis: every form
  of Theorem 16.6.6 in the project assumes tame germ data of the model section
  (`CanonicalGermInput o (m+1)`: `IsScFredholmSectionTame` plus the index), which the text's statement
  (∂Z = ∅, f oriented, compact solution set) does not state. With that hypothesis added to B, A ⇒ B is
  proved (`A_to_Btame`). B ⇒ the ∫ part of the main form is proved (`B_to_AmainInt`: existence for
  every admissible λ, independence of λ, dependence only on [τ]); A also states the effective
  integral ∮ and about 140 auxiliary conjuncts, which B does not. The main form is not vacuous
  (`hyps_satisfiable`, the circle section). Whether an oriented section over a polyfold with ∂Z = ∅
  always has tame germ data is not settled in the project (`UntamedCorner` has d = 0 at its corner
  point but carries no orientation structure). **In the statement.**
- **V16.82** (index 0, weighted point counts). A is 81 theorems; main forms
  `theorem_16_6_6_index_zero_*_unconditional`. The same hypothesis (`CanonicalGermInput o 0`) is the
  only gap for A ⇒ B (`main_to_B_tame` proved); B ⇒ the count part of the main form is proved
  (`B_gives_main`); A also states the effective count. The hypotheses are satisfiable
  (`OrbifoldSquare` witnesses). **In the statement.**

Both blind writers saw, while searching the vocabulary, the docstrings of `theorem_16_6_6_statement`
and `theorem_16_6_6_index_zero_polyfold_statement`; neither B follows them (B has ∫ only and no tame
germ data).

## Every mismatch

One line each. *Statement*: the project's formal statement differs from the text's. *Reading*: the
difference comes only from the blind writer's reading of the quoted statement. *Row*: only from extra
conjuncts of the row; the main conjunct agrees. *General*: A is more general than the text (fewer
hypotheses or more cases); the text's claim follows. *Verdict*: the row says *stronger* or
*narrower*; the round trip finds the two the same.

**Statement (11)**
- V8.48 (r2): the project's `IsLR` checks only strong bundle maps of all of W; the text's (LR) is the project's `IsLRLocal` (proved equal to B's notion), which implies `IsLR`; Proposition 8.4.3 holds for `IsLRLocal` (B ⇒ main proved).
- V16.78, V16.82: tame germ data in every form of Theorem 16.6.6 (above).
- V18.41: with Definition 18.1.7's printed clauses alone (no continuity of the norm) the conclusion does not hold (`not_B`, half-space bundle); the project reads "auxiliary norm" with continuity in every model.
- V19.24: with (v3) as printed (no condition |Ψ(p)| = z on the limit), (v3) does not give (v2) (`not_B`, `gluedBasic`); the project reads the limit in the fibre.
- V19.77: the project adds `IsCompatible` (every t̂ continuous); without it (2) does not hold (`not_B`, `twistBasic`); with it A ⇒ B proved.
- V19.85, V19.88, V19.89, V19.97, V19.110: `IsCompatible` added; with it A ⇒ B proved (V19.89 and V19.97 through the refreshed items).

**Reading (20)**
- V15.37, V15.49 (refreshed): B leaves out tame germ data and the sc-smooth bump functions that §15.3 assumes throughout (p. 692); with both added, B and the main forms are equivalent.
- V15.29, V15.32, V15.33, V15.34, V15.36, V18.13, V18.51: B reads "sc-Fredholm" over a tame base without tame germ data; the project reads it with them (Findings 191, Definition 3.6.3). Also: V15.29 the pointwise reading of bump functions; V15.32 dom-supp over ∂X; V15.33–34 the bump and partition hypotheses the quote leaves out; V18.51 the printed auxiliary norm.
- V15.2: B reads the section over X_∞ literally; A holds on X₁.
- V16.77: B leaves out the tameness under which Definition 16.6.5 and Theorem 12.5.7 are stated.
- V17.35, V17.42, V17.60, V17.99, V17.142, V18.24: B leaves out F(α) ≠ ∅ (a uniformizer at every object, or at the points of supp Θ), which the text presupposes; `not_B` proved for V17.42, V17.60, V17.142.
- V18.28: B leaves out the compact moduli space under which the text states Theorem 18.2.6.
- V18.52: B renders "naturally oriented" as existence of an orientation; A needs the index on the support and orients the models.
- V19.41: B leaves out the metrizability standing in §19.5.

**Row (6)**: V12.24, V12.26, V12.39 (Loc versions, uniqueness of the topology, examples), V16.28 (Stokes for every ep-groupoid), V18.40 (the construction in a covering model and its identification with the construction of p. 854), V14.8 (refreshed: ep-groupoid partitions of unity give M-polyfold partitions of unity of the object space, so B's hypothesis gives the text's); the main conjunct agrees with B.

**General (12)**: V14.25, V14.33, V14.37, V14.48 (any §14.3 data, fewer hypotheses; V14.37 states the clause "0 where no morphism arrives" as a separate lemma), V15.3 (any Λ), V17.52 (one specific structure, where B asks for some structure), V17.65, V17.81, V17.95, V17.102 (all objects of C¹, any point, any family), V19.32, V19.62 (no metrizability or `HasClassUniformizers`).

**Verdict (2)**: V19.31 (*stronger*: the formal statement drops the 2021 hypothesis that T is metrizable; the blind writer kept it, and B ⇒ A holds through the project's lemmas), V16.34 (*narrower*: the text asks for a functor on all polyfolds, which do not form a category as we read Definition 16.1.10; B is stated on representatives). The other seven rows of the first pass (V13.51, V16.11, V17.12, V17.30, V18.49, V19.75 now *restated*, V17.53 now *hypotheses explicit*) now match: the extra part follows by symmetry, from the groupoid structure, or from a lemma of the text.

**V18.40.** The row now lists Proposition 18.4.3 for the text's Λ, built in one strong bundle uniformizer (`proposition_18_4_3_text`, `proposition_18_4_3_cutoff`, `Chapter18/MultisectionConstructionText`); the main conjunct `proposition_18_4_3_cutoff` and B are the same statement (both directions proved), and A ⇒ B is proved. The construction in a covering model, which A also lists, is the same functor (`TextData.textLam_eq`).

**Partial (4)**: V15.15, V15.30, V15.51, V19.61 (incomparable on *stronger* / *narrower* rows).

## Refreshed items

Eight items were audited again on their blind statements after the project added the forms below (`Items/<ID>_r2.*`, field `refresh_of`); the counts above use the refreshed results.

- **V13.58** (Theorem 13.5.7): the summands are atomic in the sense of Definition 13.5.1 (`theorem_13_5_7_isAtomic_sum`, `Chapter13/Theorem1357Atomic`). A ⇒ B and main ⇔ B proved: match.
- **V14.8** (Theorem 14.1.9): with `EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity`, B's ep-groupoid partitions of unity give the M-polyfold partitions of unity the text and the project assume. A ⇒ B and main ⇔ B proved: *Row*.
- **V15.37, V15.49** (Corollary 15.4.4): the hypothesis on sc⁺-sections of [0,1] × X follows from bump functions (`hasScPlusSectionsThrough_cubeSEP_of_bump`), and the corollary is stated as maps on de Rham cohomology (`corollary_15_4_4_deRham`, `_eff_deRham`, `Chapter16/Corollary1544NoSections*`). B ⇒ main proved; with tame germ data and bump functions added to B, main ⇔ B: *Reading*.
- **V16.71** (Theorem 16.5.7): proved under Definition 16.1.5 (2) (`theorem_16_5_7_def_16_1_5`), through ep-groupoid partitions of unity ⇒ M-polyfold partitions of unity of the object space (`EpGroupoid.admitsScPartitionsOfUnity_of_hasScPartitionsOfUnity`). Both directions proved: match.
- **V17.33, V17.63** (Theorem 17.1.28, Proposition 17.3.6): B, the identification for every pair of uniformizers, does not hold as we read Definition 17.1.8 (`theorem_17_1_28_not_every_pair`, `proposition_17_3_6_not_every_pair`; Findings, Chapter 17, item 16); `not_B` proved. The rows are now *narrower* (the statement holds for one representative): match.
- **V19.89, V19.97** (Theorems 19.7.29, 19.8.6): P itself is the covering functor with the structure of (F, 𝓕) (`theorem_19_7_29_content`), and (5) holds for all four orbit spaces (`theorem_19_8_6_five_hyp`; point G.273); with `IsCompatible`, A ⇒ B proved: *Statement* (the compatibility reading).

## Notes

**Blind exposure.** `vocab.md` lists the project's statement definitions (`*_statement`, `*_hyp`,
`Lemma_16_2_1`, …), since they are definitions. Writers recorded what they saw: V14.37 (had
`#print`ed `proposition_14_5_4_statement`), V14.43 (took the Theorem 14.1.9 hypotheses from
`theorem_14_1_9_statement`), V15.37 / V15.49 (read the entry of `corollary_15_4_4_statement`), V16.34
(`Lemma_16_2_1`), V16.78 / V16.82 (docstrings only). The JSONs carry `blind_exposure`; none of these
results rests on the exposed text.

**Harness.** In many Part IV rows a banned theorem sits inside a statement or a definition body, not in
an abstracted `_proof_` field, so every term mentioning A reaches it. Such failures are recorded with
`#guard_msgs`, and the check runs on an `A′` copy equal to A by `rfl` or with a local variant
(`#rt_check_opaque`, `#rt_check_except`, `#rt_check_stmt`, defined in the item file); each JSON says
which.

**Checks.** Every item file was recompiled at e1d5ad6 with
`lake env lean -DmaxSynthPendingDepth=3 RoundTrip/Items/<ID>.lean` after `lake build
RoundTrip.Blind.<ID>`: no error, no `sorry`, no unrecorded `rt_check` failure. `Items/V18_40` was recompiled again after the construction of p. 854 in one uniformizer was added, and the refreshed items after their new forms.
