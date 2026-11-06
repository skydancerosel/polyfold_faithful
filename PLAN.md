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
6. Chapter 6 (orientations): planned 2026-11-06, §6 below. The project lead decided to finish Part I
   before Part II; until Chapter 6 is done, "Part I formalized" means Chapters 1–5.

## 6. Chapter 6: Linearizations, Orientations, and Invariants (plan, 2026-11-06)

**Text.** Preprint (arXiv 1407.3185) Chapter 6, pp. 200–237, `sources/HWZ-PartI-2014.txt` lines
8185–9775: §6.1 linearizations, §6.2 linear algebra and conventions, §6.3 the determinant of a
Fredholm operator, §6.4 classical local determinant bundles, §6.5 local orientation propagation and
orientability, §6.6 invariants of proper sc-Fredholm sections, §6.7 appendix (the proofs of
Lemma 6.5 and Proposition 6.12). The 2017 version (arXiv 1707.08941) is its Chapter 6
"Orientations" (`sources/HWZ-Book-2017.txt` lines 8669–10688, pp. 181–221); it renumbers by kind
and **rewrites §6.3–6.4** (below, finding 1). `BookConcordance.md` gets a Chapter 6 table.

### 6.1 Inventory (43 numbered items; 2017 numbers provisional until the concordance is checked)

Tiers: **A** finite-dimensional linear algebra, Mathlib only; **B** Banach-space topology of
determinant lines; **C** sc-Fredholm sections (needs Chapters 2–5); **—** not formalized (reason
given).

| Preprint | p. | Content | 2017 | Tier | Lean target (`Polyfold/Chapter6/`) |
|---|---|---|---|---|---|
| Def 6.1 | 201 | `Lin(f, x)`, the index `ind(f, x)` | Def 6.1 | C (done in part) | `StrongBundle.IsIndexAt`, `IsIndexAtLocal` exist (V3.98); add the set `Lin(f, x)` in a chart: `LinSet.lean` |
| Prop 6.2 | 201 | `ind(f, x)` constant along sc-smooth paths, `X` tame | Prop 6.1 (+ Rem 6.1) | C (done) | `proposition_6_2_local` (V3.98), paths on `ℝ` |
| Def 6.3 | 204 | `ι : λ(E*) → λ*(E)`, `ι(e*∧…)(a∧…) = det(e*ᵢ(aⱼ))` | Def 6.2 | A | `DetLine.lean`: Mathlib's `exteriorPower.pairingDual` |
| Prop 6.4 | 205 | `λ*(Φ) ∘ ι = ι ∘ λ(Φ*)` | Prop 6.2 | A | `DetLine.lean` |
| Lemma 6.5 | 206 | `Φ_E : λ(A)⊗λ*(D) → λ(B)⊗λ*(C)` of a 4-term exact sequence is independent of the choices | Lemma 6.1 (+ Lemma 6.2 naturality) | A | `ExactSequence.lean` |
| Prop 6.6 | 207 | `Ψ_E : λ(C)⊗λ(A)⊗λ*(D) → λ(B)`, explicit formula | Prop 6.3 | A | `ExactSequence.lean` |
| Def 6.7 | 208 | `det(T) = λ(ker T) ⊗ λ*(coker T)` | Def 6.3 | A | `FredholmDet.lean` |
| Def 6.8 | 208 | orientation of a Fredholm operator | Def 6.4 | A | `FredholmDet.lean` (Mathlib `Orientation`/`Module.Ray`) |
| Def 6.9 | 208 | good left-projections `Π_T`, the order `P ≤ Q` | Def 6.5 | A | `GoodProjections.lean` |
| Lemma 6.10 | 208 | `P, P' ∈ Π_T` have a common lower bound in `Π_T` | — (dropped; see finding 1) | A/B | `GoodProjections.lean`: new proof |
| Lemma 6.11 | 209 | `E(T,P): 0 → ker T → ker PT → F/R(P) → coker T → 0` exact | Prop 6.4 | A | `GoodProjections.lean` |
| Prop 6.12 | 211 | `γ^P_{QT} ∘ γ^Q_T = γ^P_T` for `P ≤ Q` (proof §6.7.2) | Prop 6.5 | A | `GoodProjections.lean` |
| Cor 6.13 | 211 | the transition `det(ST) → det(RT)` is independent of `P` | Cor 6.1 | A | `GoodProjections.lean` |
| Lemma 6.14 | 212 | the stabilization sequence `0 → ker T → ker T_φ → ℝⁿ → F/R(T) → 0` exact | Lemma 6.6 | A | `Stabilization.lean` |
| Prop 6.15 | 213 | `ι_φ : det(T) → det(T_φ)`, explicit formula with `1/det(c̄, r)` | Prop 6.7 | A | `Stabilization.lean` |
| Def 6.16 | 214 | `det(T) ⊗ det(S) → det(T ⊕ S)` | Def 6.7 | A | `Stabilization.lean` (well-definedness proved) |
| Lemma 6.17 | 214 | for `‖S − T‖ < ε`: `P ∈ Π_S`, `PS|_Y` an isomorphism | Lemma 6.7 | B | `LocalDetBundle.lean` |
| Lemma 6.18 | 215 | `⋃ {S} × ker(PS)` is a trivial vector bundle | Lemma 6.8 | B | `LocalDetBundle.lean` |
| Lemma 6.19 | 216 | `λ`, `λ*`, `⊕`, `⊗` of topological vector bundles (cited, "standard") | Lemma 6.9 | B (narrower) | only the trivial-bundle case used; general form not in Mathlib |
| Prop 6.20 | 216 | `DET(T, P, ε)` is a topological line bundle | Prop 6.8 | B | `LocalDetBundle.lean` |
| Lemma 6.21 | 216 | `(S, h) ↦ (S, γ^Q_{PS} h)` is a line bundle isomorphism (proof a sketch) | Lemma 6.10 | B (hard) | `LocalDetBundle.lean` |
| Def 6.22 | 218 | the basis `𝓑` on `DET(E,F)` | Def 6.8 | B | `DetBundle.lean`: Mathlib `VectorPrebundle` |
| Prop 6.23 | 218 | `𝓑` is a basis of a topology | Prop 6.9 | B | `DetBundle.lean` |
| Prop 6.24 | 218 | `DET(E,F)` is a topological line bundle over the Fredholm operators | Prop 6.10 | B (headline) | `DetBundle.lean`: `VectorPrebundle.toVectorBundle` |
| Lemma 6.25 | 218 | transition maps are continuous | Lemma 6.11 | B (hard) | `DetBundle.lean` (uses Lemma 6.10, Cor 6.13, Lemma 6.21) |
| Prop 6.26 | 219 | `DET(f, x)` over the convex set `Lin(f, x)` is a line bundle with exactly two orientations | Prop 6.11 | B+C | `LineBundleOrientation.lean`, `LinSet.lean` |
| Def 6.27 | 219 | orientation of `(f, x)`; the category `O_f` | Def 6.9 | C | `LinSet.lean` (with chart change) |
| Prop 6.28 | 220 | neighbourhoods `U(x)`: sc-smoothly contractible, compact local solution set, sections through `f ∘ φ` and through given points | Prop 6.12 | C | `OrientableNbhd.lean` |
| Lemma 6.29 | 222 | finitely many sc⁺-sections give property (P): `F_t` in general position at `(φ(t), 0)` for all `t` | Lemma 6.12 | C (hard) | `Propagation.lean` |
| Lemma 6.30 | 222 | the solution set of `F` near the curve is a manifold with corners; `π : S → [0,1]` a submersion | Lemma 6.13 | C (hard) | `Propagation.lean` |
| Lemma 6.31 | 223 | the sequence `E_t` (96) is exact | Lemma 6.14 | C | `Propagation.lean` |
| Prop 6.32 | 224 | the push-forward `o ↦ φ_* o` does not depend on the choices | Prop 6.13 | C (hard) | `PropagationWellDefined.lean` |
| Lemma 6.33 | 224 | adding sections does not change `φ_*` ("a simple computation") | Lemma 6.15 | C (hard) | `PropagationWellDefined.lean` |
| Lemma 6.34 | 226 | a convex homotopy of `s` does not change `φ_*` | Lemma 6.16 | C (hard) | `PropagationWellDefined.lean` |
| Thm 6.35 | 227 | local propagation exists and depends only on the endpoints in `U` | Thm 6.1 | C (hard) | `PropagationWellDefined.lean` |
| Def 6.36 | 227 | orientable neighbourhood; continuous orientation | Def 6.10 | C | `PropagationWellDefined.lean` |
| Thm 6.37 | 228 | the functor `Γ_f : P_X → O_f` ("by a covering argument") | Thm 6.2 | C (hard) | `OrientationFunctor.lean` |
| Def 6.38 | 229 | `f` orientable: `Γ_f([φ])` independent of `[φ]` | Def 6.11 | C | `OrientationFunctor.lean` |
| Def 6.39 | 229 | equivalent version: a continuous choice `y ↦ o_y` (no proof of the equivalence) | Def 6.12 | C | `OrientationFunctor.lean`, equivalence proved |
| Def 6.40 | 229 | orientation of an sc-Fredholm section | Def 6.13 | C | `OrientationFunctor.lean` |
| Thm 6.41 | 229 | proper, general position at zeros, oriented ⇒ `f⁻¹(0)` a compact manifold with corners with a natural orientation | Thm 6.3 | C | `SolutionOrientation.lean` |
| Rem 6.42 | 230 | orientation of `f̂(x, t) = f(x) + s(x, t)` on `X × [0, 1]` | Rem 6.4 | C | `SolutionOrientation.lean` |
| Thm 6.43 | 231 | the invariant `Ψ_(f,o) : H*_dR(X, ∂X) → ℝ`, `∫_S ω − ∫_∂S τ` | Thm 6.4 | — | not formalized (decision D1) |
| §6.7.1–2 | 234–237 | proofs of Lemma 6.5 and Prop 6.12 | §6.7 | A | with the statements |

Not numbered but used: the intrinsic `f'(x) = P_x ∘ Tf(x)` at a zero (in charts: `linAt`); "an
M-polyfold is locally path connected, and smooth points in one path component are joined by an
sc⁺-smooth path" (p. 201; not needed if Definitions 6.38–6.39 quantify over sc-smooth paths); "the
line bundle `DET(E,F)` is non-orientable" (p. 218; a remark, not formalized: it needs the topology
of the space of Fredholm operators).

### 6.2 What Mathlib (v4.33.1) has, and what it lacks

* **Has.** Exterior powers `⋀[R]^n M` with `ιMulti`, functoriality `exteriorPower.map`,
  `map_comp`, the basis `Module.Basis.exteriorPower` and `exteriorPower.finrank_eq`, the zero
  power `zeroEquiv`; the pairing `exteriorPower.pairingDual : ⋀^n M* → (⋀^n M)*` with
  `pairingDual_ιMulti_ιMulti = det (f j (v i))`, which is the text's `ι` of Definition 6.3 (the
  transpose matrix, same determinant). `Module.Dual`, `TensorProduct`, `Basis.det`,
  `AlternatingMap.eq_smul_basis_det`, rays and `Orientation` of modules. Fredholm operators
  `ContinuousLinearMap.IsFredholm` (strict, closed finite-codimensional range, complemented
  finite-dimensional kernel) with Fredholm packages and quasi-inverses (no index, no composition).
  Openness of invertibles (`ContinuousLinearEquiv.isOpen`), complements of finite-dimensional and
  finite-codimensional closed subspaces, the open mapping theorem. `FiberPrebundle` /
  `VectorPrebundle` with `toVectorBundle` — exactly the construction of Definition 6.22 –
  Proposition 6.24 (a topology on the total space from pretrivializations with continuous
  coordinate changes). `Convex.contractibleSpace`, `SimplyConnectedSpace.ofContractible`, covering
  maps with the lifting criterion `IsCoveringMap.existsUnique_continuousMap_lifts` (simply
  connected, locally path-connected domain).
* **Lacks.** The determinant line of a Fredholm operator and of a family; tensor products and
  exterior powers of vector bundles (Lemma 6.19 in general); orientations of line bundles and the
  orientation double cover; triviality of bundles over contractible bases; orientations of
  manifolds; integration of differential forms, Stokes' theorem on manifolds with corners, de Rham
  cohomology (Theorem 6.43).

### 6.3 What Chapters 1–5 provide

* Fredholm theory on Banach spaces: `fredholmIndex`, compact and small perturbations
  (`fredholmIndex_add_isCompactOperator`, `isFredholm_fredholmIndex_add_of_norm_lt`); sc-Fredholm
  operators (`IsScFredholm`, `isScFredholm_iff`, `IsScFredholm.fredholmIndex_lvl`).
* Linearizations in charts: `linAt` on `T_zO = R(Dr(z))` into the fibre `K_z`; `Lin(z)`
  sc-Fredholm at zeros in every chart (`StrongBundle.linAt_isScFredholm`); the chart change
  conjugates linearizations (`linAt_chart_change_sc`). The intrinsic `T_xX` has no linear structure
  in the project (gaps G.6, G.7, G.13), so `Lin(f, x)`, `DET(f, x)` and orientations are made in a
  chart and carried between charts by the conjugation.
* §6.1 already: Definition 6.1 (`StrongBundle.IsIndexAt`, `IsIndexAtLocal`, `IsIndexAt.unique`)
  and Proposition 6.2 with the text's hypotheses for paths `ℝ → X` (`proposition_6_2_local`), with
  the stabilization device of its proof on `ℝⁿ × X` (`IndexAlongPathsDevice.lean`: `paramSection`,
  `ofProd`, pull-back bundles, `linAt_ofProd_slice`) and the restriction of bundles to open sets
  (`MPolyfold.restrictOpen`, `StrongBundle.restrictOpen`). This is the device §6.5 reuses.
* Implicit function theorems: `theorem_3_23`, `theorem_3_54_two` (a `TangentGermChart`: the local
  solution set as a graph over the kernel), `theorem_3_57`; general position
  (`StrongBundle.IsGeneralPositionGerm`) and its openness along the zero set
  (`exists_isOpen_isGeneralPositionGerm`); local compactness (`theorem_3_12`); Theorem 5.18 with
  auxiliary norms and allowable sections; manifolds with corners as M-polyfolds
  (`IsManifoldWithCorners`); products `MPolyfold.prod`, `rnPolyfold n`.
* Not available: `[0, 1]` as an M-polyfold with boundary (decision D2); sc-smooth contractibility;
  sc-differential forms (§4.4, gaps G.37–G.40).

### 6.4 What must be built

1. **Determinant lines** (`DetLine.lean`): `λ(E) := ⋀[ℝ]^(finrank E) E`, `λ*(E) := (λ(E))*`,
   `λ(Φ)`, `λ*(Φ)`, the wedge of a basis and its change by `det`, the dual vector `v*`; Definition
   6.3 and Proposition 6.4.
2. **Four-term exact sequences** (`ExactSequence.lean`): `Φ_E` defined by formula (91) for one
   choice of complements and bases, then (91) proved for **every** choice (Lemma 6.5) — this is the
   form a reader can check; `Ψ_E` (Proposition 6.6); naturality under isomorphisms of sequences (the
   2017 Lemma 6.2, needed to move orientations between charts).
3. **Determinants of Fredholm operators** (`FredholmDet.lean`, `GoodProjections.lean`,
   `Stabilization.lean`): Definitions 6.7–6.9, 6.16; `P ∘ T` Fredholm with the same index for
   `P ∈ Π_T`; Lemma 6.10 by a new construction (finding 1); `E(T,P)`, `γ^P_T`, Proposition 6.12,
   Corollary 6.13; Lemma 6.14, Proposition 6.15.
4. **The determinant bundle** (`LocalDetBundle.lean`, `DetBundle.lean`): base the subtype of
   Fredholm operators in `E →L[ℝ] F`, fibre `det S` with its module topology, model fibre `ℝ`;
   the kernel bundle of `S ↦ PS` with frames `k + y(k, S)` (Lemmas 6.17, 6.18); `DET(T, P, ε)` with
   an explicit trivialization (Lemma 6.19 and Proposition 6.20 in the case used: trivial kernel
   and cokernel bundles); the continuity of `γ^Q_{PS}` in these frames (Lemma 6.21, the computational
   core: a ratio of determinants of matrices continuous in `S`); Definition 6.22 – Lemma 6.25 as a
   `VectorPrebundle`.
5. **Orientations of line bundles** (`LineBundleOrientation.lean`): an orientation as a choice of
   ray in each fibre given locally by non-vanishing continuous sections; over a nonempty convex
   base exactly two (the orientation double cover is a covering map, and Mathlib's lifting criterion
   applies to the simply connected, locally path-connected base); unique continuation along a path.
6. **Continuity of stabilization in families** (`StabilizationContinuity.lean`): if `T_τ` varies
   continuously in `Lin(f, x)` and `φ_τ : ℝᵏ → F` continuously with `T_τ ⊕ φ_τ` onto, then
   `Φ_{E_τ} : det(T_τ) → λ(ker(T_τ ⊕ φ_τ)) ⊗ λ*(ℝᵏ)` is continuous for the topology of 4. This is
   what "the data vary continuously" means in Lemmas 6.33, 6.34 and the proof of Theorem 6.35; the
   text does not state it.
7. **The sc-Fredholm layer** (`LinSet.lean`, `OrientableNbhd.lean`, `Propagation.lean`,
   `PropagationWellDefined.lean`, `OrientationFunctor.lean`, `SolutionOrientation.lean`):
   `Lin(f, x)` in a chart, its members Fredholm on level 0 of one index (sc⁺-operators are compact on
   level 0), convex; `DET(f, x)` and Definition 6.27 with the chart change; Proposition 6.28 in a
   convex chart (`r(ty)`, and the straight-line homotopy `r((1 − τ)φ₀ + τφ₁)` between paths with the
   same ends); the section `F(t, y, λ) = f(y) − R(y, f(φ(t))) + Σ λᵢ R(y, eᵢ)` of the pull-back to
   `ℝ × U × ℝᵏ`; property (P) from the implicit function theorem for `F` along the curve
   `t ↦ (t, φ(t), 0)`, whose tangent vector `(1, φ'(t), 0)` makes `F_t'` onto once `F'` is (a proof
   of Lemma 6.29 the text does not give); the continuity of `t ↦ L_t = ker F_t'(φ(t), 0)` from the
   graph chart of the solution set (on a finite-dimensional kernel, strong continuity of `Dδ` is norm
   continuity); `φ_*` by continuation in `λ(L_t) ⊗ λ*(ℝᵏ)`; Proposition 6.32, Lemmas 6.33–6.34,
   Theorem 6.35 by the text's two-parameter families and 6; the path category `P_X` (sc-smooth
   paths on `ℝ`, homotopies rel end points, composition by a flat reparametrization), Theorem 6.37
   by a Lebesgue-number argument on `[0, 1]` and `[0, 1]²`; Definitions 6.36, 6.38–6.40 and the
   equivalence 6.38 ⟺ 6.39; orientations of the solution manifold (`T_xS = ker f'(x)`, oriented
   graph charts) and Theorem 6.41 (with `s = 0`, `k = 0` the propagation along a path in `S` is the
   continuation in `TS`); Remark 6.42 on `X × ℝ`.
8. **Non-vacuity witnesses** (as `Chapter3/NonVacuity.lean`): every hypothesis that quantifies over
   charts or over orientable neighbourhoods (Definitions 6.36, 6.39, 6.40, Theorem 6.41) checked
   satisfiable on the trivial bundle `ℝⁿ × ℝⁿ → ℝⁿ` with a `C^∞` map `f` (there `Lin(f, x)` is all of
   `L(ℝⁿ, ℝⁿ)`, and `f(x) = x` is proper, transversal and oriented).

### 6.5 The hardest items, and what is already visible

Hardest, in order: (1) §6.5's propagation — Lemmas 6.29–6.30 (the implicit function theorem along a
curve with continuity of the kernels), Lemmas 6.33–6.34 (the text's proofs are sketches: "one
verifies by a simple computation", "clearly `L̃_τ` varies continuously"), Theorem 6.37 ("by a covering
argument"); (2) the continuity of `γ` in frames (Lemma 6.21, "this is trivial and follows from an
inspection") and of stabilization (item 6 of §6.4); (3) "exactly two orientations" over a contractible
base (Proposition 6.26 cites contractibility without the theorem it needs). §§6.2–6.4 are routine but
long; the risk there is bookkeeping (`Fin` concatenations, quotients, fibres as dependent types).

Found while reading for the plan (to be checked in Lean, then recorded in `Findings.md`, new section
"## Chapter 6"):

1. **Lemma 6.10.** The proof's `P''` (onto `R(P) ∩ R(P')` along an arbitrary `Z ⊕ X ⊕ X'`) need not
   satisfy `P'' ≤ P`: if `R(P) = R(P')` and `ker P ≠ ker P'`, a projection onto `R(P)` that is `≤ P`
   is `P` itself, and likewise `P'` (e.g. `F = ℝ²`, `T = id`, `P, P'` onto the `x`-axis along the
   `y`-axis and the diagonal). The lemma itself holds as we read it, with a smaller range: choose a
   closed finite-codimensional `R'' ⊂ R(P) ∩ R(P')` meeting `K = ker P + ker P'` only in `0`
   (Hahn–Banach on the finite-dimensional `K`) and a finite-dimensional complement `C ⊇ K`; the
   projection onto `R''` along `C` lies in `Π_T` and is `≤ P, P'`. The 2017 version drops the lemma,
   says the common lower bound need not exist (p. 190), and rebuilds §6.3–6.4 around a new
   Proposition 6.6 (spaces `P_H`); that remark does not hold as we read it. The preprint's route
   (Lemma 6.25 through Lemma 6.10 and Corollary 6.13) is then sound and is the one formalized.
2. **Appendix 6.7.1** (Lemma 6.5): the step "independent of the choices of the basis if and only if
   `det(τ) = det(ε)`" uses `τ` for the `σ` just introduced and states a condition where homogeneity
   is meant (possible misprint; the proof goes through with homogeneity).
3. **Proposition 6.6**: the formula's `c = c'₁ ∧ … ∧ c'_l ∧ c₁ ∧ … ∧ c_{m−n}` exchanges the names of
   the statement (`cᵢ` with `γ(cᵢ) = dᵢ`, `c'ᵢ = β(b'ᵢ)`); the order is (91)'s (possible misprint).
4. Notation: Lemma 6.14's proof "`j(e) = (0, e) = (e, r)`"; Theorem 6.35's statement does not introduce
   `f`; Definition 6.39's "`y ∈ U_∞`" for `X_∞`; Proposition 6.28 writes `s(y, t)` where §6.1 writes
   `s(t, x)` (possible misprints, harmless).
5. Unstated: Proposition 6.26's two orientations need that a line bundle over a contractible
   (paracompact) base is trivial; Proposition 6.32 – Theorem 6.35 need the continuity of the
   stabilization isomorphism (§6.4 item 6); Definitions 6.38/6.39 are called equivalent without proof.
6. §6.2 announces that sc-smooth partitions of unity are assumed from there on "to simplify the
   presentation". The plan works locally in charts (as Proposition 6.2 did) and adds no such
   hypothesis; each item will record whether it needed one.

### 6.6 Decisions (recommendations; the project lead to confirm)

* **D1. Theorem 6.43 is not formalized** (a gap, numbered from G.54): it needs sc-differential forms
  and their de Rham cohomology on M-polyfolds (§4.4, already out of scope, G.37–G.40), integration
  over oriented compact manifolds with corners and Stokes' theorem, none of which Mathlib has. What
  it rests on is formalized: the admissible perturbations of Theorem 5.18 and the orientation of
  `S_{f+s}` (Theorem 6.41).
* **D2. Paths on `ℝ`, as for Proposition 6.2 (V3.98).** The text's `[0, 1]`, `[0, 1] × X` and
  `[0, 1]² × X` (manifolds with boundary) become `ℝ`, `ℝ × X`, `ℝ² × X`, with paths read on `[0, 1]`
  and homotopies fixing the end points; a path sc-smooth on `[0, 1]` would be composed with a
  smooth `ρ : ℝ → [0, 1]` flat at `0` and `1`, which keeps the end points and the homotopy class.
  Verdict "narrower" where it applies. The alternative, `[0, 1]` as a tame M-polyfold with boundary
  (two charts on `[0, ∞)`) and its products, is a separate piece of work that would also upgrade
  V3.98; not proposed now. **Confirmed by the project lead, 2026-11-06**, with a way back kept open.
  So that a later `[0, 1]` needs only a bridge lemma and no rewrite, every path notion of Chapter 6
  is stated through `[0, 1]` alone: the propagation `φ_*` and `Γ_f([φ])` are proved to depend only
  on `φ|[0, 1]`, and homotopies `H : ℝ² → X` are asked to fix the end points only for `τ ∈ [0, 1]`.
  For the orientations themselves (propagation, `Γ_f`, orientability, Theorem 6.41) nothing is lost.
  What `ℝ` does not give directly is a parameter interval *with boundary*: the homotopy invariance
  of invariants (Theorem 6.43 (2), and later Part III), where the solution set of a homotopy on
  `X × [0, 1]` is a cobordism whose ends are its boundary over `t = 0, 1`. On `X × ℝ` one must
  instead arrange `0, 1` to be regular values of `t` on the solution set (a small perturbation and
  Sard, which is vendored), as Chapter 5 already does for Definition 5.20 (`t` read as a function
  into `ℝ` with image `[0, 1]`). **Follow-up before Part III**: `[0, 1]` as a tame M-polyfold, the
  bridge lemma, and the upgrade of V3.98 and the Chapter 6 path items.
* **D3. Numbering.** Proposition 6.2 stays V3.98 (no second sign-off item for the same theorem);
  Chapter 6 items are V6.1, V6.2, … in book order, V6.1 being Definition 6.1 with the new set
  `Lin(f, x)`. Gaps continue from G.54, findings in a new "## Chapter 6" of `Findings.md`.

### 6.7 Order of work and checkpoints

1. **Definitions first, written by the session lead** (`DetLine`, `ExactSequence`, `FredholmDet`,
   `GoodProjections`, the `DET` total space, `LinSet`): definitions are the contract, so they are not
   delegated; proofs are, to at most two Lean agents at a time.
2. **Phase A** (§6.2–6.3, Definitions 6.3–6.16): 19 items. Checkpoint: build green, `Test.lean`
   lines, commit.
3. **Phase B** (§6.4, Lemma 6.17 – Lemma 6.25, and Proposition 6.26's line-bundle part): 10 items.
   Checkpoint and commit. Phases A–B give the classical determinant line bundle of Fredholm operators
   between Banach spaces, which Mathlib does not have.
4. **Phase C** (§6.5, Definition 6.27 – Remark 6.42, with §6.4 items 5–6 and the non-vacuity
   witnesses): 16 items; the largest phase. Commit after Theorem 6.35 and after Theorem 6.41. If a
   step of the text cannot be completed as written, the weakest added hypothesis or a new argument is
   recorded, as in Chapters 3–5.
5. **Reports**: `Exposition/Chapter6.md` (STYLE.md shape; figure: the propagation of an orientation
   along a path through the kernel bundle `L_t`); `verification/ch06.md` (V6.1, …), `cmp/ch06.json`
   (with `notFormalized` for Theorem 6.43 and the remark on non-orientability), `pbp/part06.md`;
   `BookConcordance.md` Chapter 6; regenerate with `build_verification.py`, `build_signoff.py`,
   `assemble_pbp.py`, `build_proofbyproof.py`, `build_comparison.py` from the repository root.
6. **Round-trip audit** of the new non-extra items (`RoundTrip/`, as for Chapters 1–5).
7. **Counts and status** in `README.md` (Status; the "337 items" of "How to check it and sign off"),
   `HANDOFF.md`, this file. The four checks of `HANDOFF.md` §1 green at every commit.
