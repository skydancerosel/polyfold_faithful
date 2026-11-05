# Plan and status: Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*, Part I

A sequel to the formalizations of Milnor's two books (`github.com/skydancerosel/math_faithful`),
with the same pipeline: a faithful
formalization against Mathlib, an expanded exposition, and the reports that show what was checked
(verified edition with a sign-off list, proof by proof, comparison, round-trip audit).

**Text.** H. Hofer, K. Wysocki, E. Zehnder, *Polyfold and Fredholm Theory*, Ergebnisse der
Mathematik 3. Folge 72, Springer 2021. Part I, *Basic Theory in M-Polyfolds*, is the target; its
2014 preprint is arXiv 1407.3185 (*Polyfold and Fredholm Theory I*), and the examples that motivate
the sc-calculus are in arXiv 1002.3381 (*Sc-Smoothness, Retractions and New Models for Smooth
Spaces*, 2010). The cloud sessions work from the preprint texts (`Exposition/sources/`, not in
git); statement numbers and pages are to be checked against the book on the Mac, where its PDF is
kept untracked as `Polyfold/PolyfoldFredholm.pdf`. Differences between the preprint and the book
go to `Exposition/Findings.md`.

**Why Part I first.** It is the self-contained core: Banach-space analysis with one new idea
(sc-smoothness), no holomorphic curves, no groupoids, and the implicit function theorem for
sc-Fredholm sections as its headline. Everything later (ep-groupoids, polyfolds, Gromov–Witten,
SFT) rests on it. It is also settled: the book corrects the 2007–2009 papers, and the Gromov–Witten
memoir uses it as stated.

Status as of 2026-10-26, end of the first local session (see `HANDOFF.md`): **Part I, Chapters 1–5, done** (Lean, exposition, reports: V1–V5, 337 sign-off items, gaps G.1–G.53). The sc-Fredholm implicit function theorem (Theorems 3.19, 3.23, 3.54, 3.56, 3.57, Corollary 3.24) is proved with the text's hypotheses; two gaps of the text's proofs are closed by new arguments (surjectivity at the nearby zeros, also missing in the book's arXiv version; Theorem 3.27 for solution sets), and a vacuous tameness hypothesis of an earlier formalization was found and repaired. Chapter 4 (Prop 4.9 by a direct proof, Theorems 4.2, 4.18, 4.22, 4.23 with Sard vendored from the Milnor project) and Chapter 5 (Theorems 5.5–5.7, 5.13, 5.18, 5.19, 5.25, the appendix) done except what HANDOFF §2 lists. 2,708 theorems checked in `Polyfold/Test.lean`, all on the three standard axioms, no `sorry`. Next: the round-trip audit.

## 1. Headline theorems (Part I)

| # | Result (preprint numbering; book numbering to be added) | Status |
|---|---|---|
| H1 | **The sc-chain rule** (§1.3, Theorem 1.21; proof in §1.4.2): the composition of sc¹ maps is sc¹, with `T(g ∘ f) = Tg ∘ Tf`; hence sc^k and sc-smooth compose | done (`Polyfold.theorem_1_21`, `Polyfold.IsSck.comp`, `Polyfold.IsScSmooth.comp`); with it Definitions 1.1–1.15, Propositions 1.6, 1.7, 1.9, 1.10 (and the classical compact-perturbation theorem Mathlib lacks), Lemma 1.24, Props 1.16/1.18 in the base case and 1.19/Cor 1.20 for `k = 0`. Props 1.16–1.18 for all levels and 1.19/1.20 for all `k` (`Polyfold/Chapter1/Levels.lean`, 80 theorems in all), 1.19/1.20 under the stronger hypothesis that every level map `U_m → F_m` is `C^{k+1}` (the text's weaker shifted-level hypothesis is not formalized). Theorem 1.25 (boundary recognition) proved in `Chapter2/DegeneracyIndex.lean` by the §2.3 argument, for sc¹ maps |
| H2 | Sc-differentiability is strictly weaker than classical differentiability on each level, and strictly stronger than level-wise differentiability of the restrictions: the shift map on weighted Sobolev spaces is sc-smooth but not C¹ (1002.3381, §1) | planned |
| H3 | **Sc-smooth retractions** (§2.1): an sc-smooth retraction `r` has an sc-smooth retract `O = r(U)` whose tangent space `T_xO = Tr(x)(T_xU)` does not depend on `r`; sc-smooth maps between retracts have well-defined tangent maps | done (`Polyfold.proposition_2_4`, `Polyfold.theorem_2_8` the chain rule for retracts, Props 2.6, 2.10; `Chapter2/Retracts.lean`). Not done: Prop 2.2 (classical), Def 2.9 (bundle retractions) |
| H4 | **M-polyfolds** (§2.2–2.4): charts, transition maps, the tangent bundle `TX → X¹`, the degeneracy index `d_X` and its invariance, sub-M-polyfolds, tame M-polyfolds and the boundary structure | in progress: charts, atlases (maximal atlas), M-polyfolds, the level sets `X_m` and their topology (Lemma 2.15), sc-smooth maps, sub-M-polyfolds (definition), the degeneracy index with Lemma 2.23, Prop 2.24 (invariance under sc-diffeomorphisms), Cor 2.32, and Theorem 1.25 (`Chapter2/{MPolyfold,DegeneracyIndex}.lean`); §2.4–2.5 definitions (`Tame.lean`). `X¹` as an M-polyfold (`Chapter2/LevelPolyfold.lean`, Prop 1.17 for retracts), `TX` as a Hausdorff M-polyfold with sc-smooth projection `TX → X¹` (Defs 2.17–2.19, `Chapter2/TangentBundle.lean`), the tangent map `Tf : TX → TY`, `T(id) = id`, the chain rule `T(g ∘ f) = Tg ∘ Tf` and `Tf` sc-smooth (`Chapter2/TangentMap.lean`), Prop 2.21 (1), (2) and Lemma 2.26 (`Chapter2/SubMPolyfold.lean`); paracompactness of `X¹`, `TX`, `A` is an instance hypothesis (Theorem 2.16 / Prop 2.19 (3) not formalized: Smirnov; the closed case of `A` is proved). Not done: `X_m` for `m ≥ 2` (iterate), Theorem 2.16, Prop 2.19 (2) openness and (3), Prop 2.21 (3), (4), Lemma 2.29, Prop 2.30, Theorem 2.31 in general, Props 2.35–2.46 (tame), Defs 2.50–2.54 (strong bundles) |
| H5 | **Strong bundles** (§2.5) and sc-Fredholm sections (§3): the filled version, the contraction-germ normal form (basic germs), stability of the sc-Fredholm property under sc⁺-perturbations (Proposition 1.10, proof in §1.4.1) | planned |
| H6 | **The implicit function theorem** for sc-Fredholm germs (§3): the solution set of a transversal sc-Fredholm section near a zero is an sc-smooth finite-dimensional manifold of dimension the Fredholm index, with the natural sc-structure; the local compactness of solution sets | planned |
| H7 | Transversality and perturbation theory in M-polyfolds (§4–5, as far as Part I goes): sc⁺-sections, generic transversality, the solution set as a manifold with boundary and corners (tame case) | later |

## 2. Definitions (the content is here; each gets a definition-audit item)

* sc-Banach space: a Banach space `E₀` with a nested sequence `E₀ ⊃ E₁ ⊃ E₂ ⊃ …` of Banach spaces,
  each inclusion `E_{m+1} → E_m` compact, `E_∞ = ⋂ E_m` dense in every `E_m`. Formalized as an
  indexed family of Banach spaces with compact continuous linear inclusions (not as one space with a
  filtration), with the book's form recovered as a theorem.
* Level shifts `E^k`, direct sums, sc-subspaces and sc-complements, sc-operators, partial quadrants
  `C = [0,∞)^k × W`, relatively open subsets, the degeneracy index of a point of a quadrant.
* sc⁰ maps (continuous on every level), the tangent `TU = U¹ ⊕ E` of a relatively open `U`,
  sc¹ maps (the sc-tangent map `Tf : TU → TF` exists and is sc⁰), sc^k and sc-smooth maps;
  sc⁺-maps and sc⁺-sections.
* Sc-smooth retractions, sc-smooth retracts, local models `(O, C, E)`, M-polyfold charts and
  atlases, the tangent bundle of a retract and of an M-polyfold, sub-M-polyfolds, tame retractions
  and tame M-polyfolds, the degeneracy index on an M-polyfold, faces and corners.
* Strong bundles over M-polyfolds, their sc-structures `R[i]`, `sc⁺`-sections, sc-Fredholm sections
  (regularizing, with a filled version and a contraction-germ normal form), the Fredholm index.

## 3. Infrastructure missing from Mathlib, to build here

| Piece | Status |
|---|---|
| Nested Banach scales with compact inclusions; density of `E_∞`; the induced sc-structures on `E^k`, products, closed sc-subspaces | done (`Polyfold/Chapter1/ScBanach.lean`) |
| sc⁰ / sc¹ / sc^k / sc-smooth maps on relatively open subsets of partial quadrants; the tangent construction `TU`; the chain rule | done (`ScSmooth.lean`, `ChainRule.lean`, `Properties.lean`) |
| Weighted Sobolev spaces `H^{m,δ_m}(ℝ, ℝⁿ)` as an sc-Banach space, the shift map and the gluing/anti-gluing splicing (the standard examples; Mathlib has Sobolev spaces only in part) | planned; may need `H^k` built here |
| Sc-smooth retractions and retracts; the splicing core; tangent spaces of retracts | planned |
| Fredholm operators between Banach spaces (Mathlib has none: defined here with Riesz–Schauder and compact perturbation), sc-Fredholm operators, stability under sc⁺-perturbations | done (`FredholmPerturbation.lean`, `ScFredholm.lean`) |
| The sc-implicit function theorem (contraction germs, the Banach fixed point theorem level by level) | planned |

## 4. Exposition and reports

| Step | Status |
|---|---|
| `Exposition/Chapter1.md` – `Chapter3.md` (and more as Part I is covered): physical opening, complete proofs, one figure, one application, the silent assumptions made explicit | Chapter 1 to be written with the Lean |
| `Exposition/Findings.md`: gaps, hidden hypotheses and slips, each confirmed or withdrawn; differences preprint vs book marked *(book?)* | started with Chapter 1 |
| Verified edition (`Exposition/Verification.md`, sign-off page), proof by proof, comparison, round-trip audit: the same scripts as Morse, copied and adapted | after Chapter 1's Lean |
| Rules: no `sorry`; `#print axioms` in `Polyfold/Test.lean` for every theorem, only `propext`, `Classical.choice`, `Quot.sound`; temporary files as gitignored `WIP_*.lean`; cited names pass `check_names.py`; trace tags pass `check_trace.py` | |

## 5. Order of work

1. ~~Chapter 1~~ done (2026-10-24), except Theorem 1.25 (with Chapter 2); the verified-edition section is still to write.
2. The standard examples (H2): weighted Sobolev spaces as an sc-space; the shift map. This decides how much Sobolev theory must be built.
3. Chapter 2: ~~retractions, retracts~~ done; M-polyfolds in progress (the tangent bundle `TX`, `X¹` as an M-polyfold, sub-M-polyfolds); tame M-polyfolds (Props 2.35–2.46); strong bundles (Defs 2.50–2.54).
4. Chapter 3: sc-Fredholm sections and the implicit function theorem (H5, H6).
5. Reports, sign-off page, audit; then Part I's remaining chapters (H7) and, later, Part II.
