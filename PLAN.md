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

Status as of 2026-11-07 (see `HANDOFF.md`): **Part I, Chapters 1–6, done** (Lean, exposition, reports: V1–V6, 401 sign-off items, gaps G.1–G.69), Chapter 6 (§6 below) except Theorem 6.43 (G.54) and §6.6 (G.55). The round-trip audit is done for Chapters 1–5 (2026-11-01) and for the 60 non-extra Chapter 6 items (2026-11-07, §6.7 step 6). **Part II has begun: Chapter 7 is formalized** (waves W0–W4 of the Part II plan below; V7.1–V7.68, 68 sign-off items, gaps G.70–G.73), Propositions 7.9 and 7.10 under the hypothesis that `𝐗^R` is Hausdorff and paracompact (G.71); its reports (wave W5) and its round-trip audit are done (2026-11-07); the audit proved that `𝐗^R` need not be Hausdorff (`RoundTrip/Items/V7_40.lean`, moved the same day into `Polyfold/Chapter7/ReducedNotHausdorff.lean`). In all: 469 sign-off items, gaps G.1–G.73, 5,931 `#print axioms` lines in `Polyfold/Test.lean`, all on the three standard axioms, no `sorry`. **Chapter 8 is formalized** (2026-11-08, §II.9 below; 14 files in `Polyfold/Chapter8/`, V8.1–V8.43, gaps G.74–G.75; in all 512 sign-off items, 6,761 `#print axioms` lines), Definitions 8.2–8.3 excepted; its round-trip audit is not done. As of 2026-10-26, end of the first local session: **Part I, Chapters 1–5, done** (Lean, exposition, reports: V1–V5, 337 sign-off items, gaps G.1–G.53). The sc-Fredholm implicit function theorem (Theorems 3.19, 3.23, 3.54, 3.56, 3.57, Corollary 3.24) is proved with the text's hypotheses; two gaps of the text's proofs are closed by new arguments (surjectivity at the nearby zeros, also missing in the book's arXiv version; Theorem 3.27 for solution sets), and a vacuous tameness hypothesis of an earlier formalization was found and repaired. Chapter 4 (Prop 4.9 by a direct proof, Theorems 4.2, 4.18, 4.22, 4.23 with Sard vendored from the Milnor project) and Chapter 5 (Theorems 5.5–5.7, 5.13, 5.18, 5.19, 5.25, the appendix) done except what HANDOFF §2 lists. 2,708 theorems were then checked in `Polyfold/Test.lean`, all on the three standard axioms, no `sorry`, and the round-trip audit came next.

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
   before Part II; until Chapter 6 is done, "Part I formalized" means Chapters 1–5. Done 2026-11-07
   except Theorem 6.43 (G.54) and §6.6 (G.55): "Part I formalized" now means Chapters 1–6 with
   these two exceptions.
7. Part II: begun 2026-11-07 (Part II plan below). Chapter 7 is formalized (waves W0–W4); its
   reports and its round-trip audit are done (wave W5).

## 6. Chapter 6: Linearizations, Orientations, and Invariants (plan, 2026-11-06)

**Text.** Preprint (arXiv 1407.3185) Chapter 6, pp. 200–237, `sources/HWZ-PartI-2014.txt` lines
8185–9775: §6.1 linearizations, §6.2 linear algebra and conventions, §6.3 the determinant of a
Fredholm operator, §6.4 classical local determinant bundles, §6.5 local orientation propagation and
orientability, §6.6 invariants of proper sc-Fredholm sections, §6.7 appendix (the proofs of
Lemma 6.5 and Proposition 6.12). The 2017 version (arXiv 1707.08941) is its Chapter 6
"Orientations" (`sources/HWZ-Book-2017.txt` lines 8669–10688, pp. 181–221); it renumbers by kind
and **rewrites §6.3–6.4** (below, finding 1). `BookConcordance.md` has a Chapter 6 table (added
2026-11-07).

### 6.1 Inventory (43 numbered items; the 2017 numbers agree with `BookConcordance.md`, checked 2026-11-07)

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
5. **Reports**: `Exposition/Chapter6.md` (STYLE.md shape; written 2026-11-07 without its figure, which
   is deferred: the propagation of an orientation along a path through the kernel bundle `L_t`); `verification/ch06.md` (V6.1, …), `cmp/ch06.json`
   (with `notFormalized` for Theorem 6.43 and the remark on non-orientability), `pbp/part06.md`;
   `BookConcordance.md` Chapter 6 (done 2026-11-07); regenerate with `build_verification.py`, `build_signoff.py`,
   `assemble_pbp.py`, `build_proofbyproof.py`, `build_comparison.py` from the repository root.
6. **Round-trip audit** of the new non-extra items (`RoundTrip/`, as for Chapters 1–5).
7. **Counts and status** in `README.md` (Status; the "337 items" of "How to check it and sign off"),
   `HANDOFF.md`, this file. The four checks of `HANDOFF.md` §1 green at every commit. Done
   2026-11-07 (401 sign-off items, gaps to G.69, 4,942 `#print axioms` lines).

## Part II plan

(Plan, 2026-11-07. Status, 2026-11-07: waves W0–W4 of II.4 are done, Chapter 7 is in Lean; wave
W5, the reports and the round-trip audit, is done. The plan below is kept as written.) **Text.** Part II, "Ep-Groupoids", is Chapters
7–11 of arXiv 1707.08941 (`sources/HWZ-Book-2017.txt`: Part II opens at line 10687, Chapter 7 is lines
10704–12250, Chapter 8 starts at 12251, 9 at 13856, 10 at 15977, 11 at 18145, Part III at 20168). There
is no 2014 preprint of Part II, so numbers and pages are the 2017 text's: printed page numbers read
off the running heads (even pages "226 7 Ep-Groupoids", odd pages "7.1 … 227", the first page of a
chapter from its footer), as `BookConcordance.md` does for Chapter 6. Each kind has its own counter
(Definition 7.3 ≠ Proposition 7.3). Part I items cited by Part II carry their 2017 numbers, with the
preprint number used by the Lean name in brackets: Theorem 2.2 [2.16] = `Polyfold.theorem_2_16`,
Proposition 2.7 [2.24] = `Polyfold.proposition_2_24`, Proposition 2.15 [2.46] =
`MPolyfold.proposition_2_46`, Definition 2.19 [2.37] = `MPolyfold.IsTame`, Lemma 2.7 [2.56] (Michael;
not formalized, avoided in Part I). Lean names below are in namespace `Polyfold`.

### II.1 Overview

| Ch. | pp. | Items | Content | Needs from Part I |
|---|---|---|---|---|
| 7 Ep-Groupoids | 225–256 | 52 | groupoids whose object and morphism sets are M-polyfolds, `s, t` local sc-diffeomorphisms, a local properness; the orbit space `\|X\|`; the natural representation of `G_x`; effective and reduced ep-groupoids; topology of `\|X\|`; `X¹`; partitions of unity | Ch. 2 (M-polyfolds, local sc-diffeos, fibred products, sub-M-polyfolds, `X¹`, metrizability with Smirnov, degeneracy, tameness); Ch. 5 appendix (sc-smooth partitions of unity) |
| 8 Bundles and Covering Functors | 257–290 | 33 | tangent ep-groupoid `TX`, sc-forms, strong bundles over ep-groupoids, proper covering functors | `MPolyfold.TangentSpace`, `MPolyfold.tangentMap`, `StrongBundle`, pull-backs; §8.2 needs sc-forms (G.37–G.40) |
| 9 Branched Ep⁺-Subgroupoids | 291–332 | 59 | `Θ : X → ℚ⁺`, local branching structures, tangent and boundary, orientations, integration and Stokes | Ch. 4 (finite-dimensional submanifolds, sc⁺), Ch. 6 (orientations); M⁺-polyfolds (2017 Def 4.8, not in Part I); §9.5 needs measures and Stokes (as Thm 6.43, G.54) |
| 10 Equivalences and Localization | 333–374 | 45 | equivalences, weak fibred product, localization at equivalences, generalized maps, strong bundle versions | Ch. 7–8; Mathlib `CategoryTheory.Localization`, calculus of fractions |
| 11 Geometry up to Equivalences | 375–415 | 40 | tameness, faces, forms, branched subgroupoids, integration, bundles, coverings up to equivalence | Ch. 8–10; `MPolyfold.IsFace`, `MPolyfold.IsFaceStructured` |

Chapter 7 is the base of everything else and is planned in full below; Chapters 8–11 in II.7.

### II.2 Chapter 7 inventory (52 numbered items: 17 Def, 14 Prop, 10 Lemma, 6 Thm, 3 Cor, 2 Rem)

Difficulty: **A** easy, **B** medium, **C** hard. Files in `Polyfold/Chapter7/`. "(text)" rows are
unnumbered claims of the text that later items use.

| 2017 | p. | Content | Part I (Lean) | Mathlib | Diff. | File |
|---|---|---|---|---|---|---|
| Def 7.1 | 225 | groupoid: small category, structure maps `s, t, m, u, ι`; `\|X\| = X/∼`, `π` | — | `CategoryTheory.Groupoid`, `CategoryTheory.isIsomorphicSetoid`, `Quotient` | A | `Groupoid.lean` |
| Def 7.2 | 226 | isotropy group `G_x` | — | `CategoryTheory.Groupoid.vertexGroup`, `…vertexGroupIsomOfMap` | A | `Groupoid.lean` |
| Def 7.3 | 226 | ep-groupoid: (1) `s, t` local sc-diffeos; (2) `u, ι` sc-smooth; (3) each `x` has open `V(x)` with `t : s⁻¹(cl V(x)) → X` proper; (4) `m` sc-smooth on `X s×t X` | `MPolyfold`, `MPolyfold.IsLocalScDiffeo`, `MPolyfold.IsScSmoothMap`, `MPolyfold.fibredProduct`, `MPolyfold.isSubMPolyfold_fibredProduct`, `MPolyfold.subPolyfold`, `MPolyfold.prod`, `MPolyfold.paracompactSpace_prod` | `IsProperMap`, `Set.restrict` | B | `EpGroupoid.lean` |
| Def 7.4 | 227 | `φ̂ = t ∘ (s\|U(φ))⁻¹`; `Tφ` for `φ ∈ X_∞` | `MPolyfold.IsScDiffeoOn`, `MPolyfold.restrictOpen`, `MPolyfold.tangentMap` | — | B | `EpGroupoid.lean` |
| (text) | 227–228 | `ml(sφ) = ml(φ) = ml(tφ)`, filtration `\|X_k\|`; `d_X(sφ) = d_X(φ) = d_X(tφ)` | `MPolyfold.levelSet`, `MPolyfold.IsScSmoothOn.mapsTo_levelSet`, `MPolyfold.degIndex`, `proposition_2_24` | `Set.image` | A | `EpGroupoid.lean` |
| Def 7.5 | 228 | `d_{\|X\|}(\|x\|) = d_X(x)` | `MPolyfold.degIndex` | `Quotient.lift` | A | `EpGroupoid.lean` |
| Def 7.6 | 228 | tame: `X` tame; (text) then the morphism M-polyfold is tame | `MPolyfold.IsTame`, `MPolyfold.transportChart`, `MPolyfold.transportChart_isChart` | — | A/B | `EpGroupoid.lean` |
| Def 7.7 | 228 | category `EP`: functors sc-smooth on objects and morphisms; (text) sc-smooth on objects suffices | `MPolyfold.IsScSmoothMap.comp`, `MPolyfold.isScSmoothMap_id` | `CategoryTheory.Category` | A; B (II.6, 1) | `EpGroupoid.lean` |
| Prop 7.1 | 229 | `π` is open | `MPolyfold.IsLocalScDiffeo` | `IsOpenMap`, `IsOpenQuotientMap` | A | `Basic.lean` |
| Prop 7.2 | 229 | countable monotone neighbourhood bases in `\|X\|` | `MPolyfold.metrizableSpace` | `FirstCountableTopology` | A | `Basic.lean` |
| Prop 7.3 | 229 | `π(cl A) = cl π(A)` for `A ⊂ U(x)` | `MPolyfold.metrizableSpace` | `IsCompact.tendsto_subseq` | B | `Basic.lean` |
| Lemma 7.1 | 230 | finitely many `ψ` with `s ψ = x`, `t ψ ∈ U(x')` | `MPolyfold.IsLocalScDiffeo` | `IsProperMap.isCompact_preimage`, `Set.Finite` | B | `Basic.lean` |
| Prop 7.4 | 230 | `G_x` finite | — | `Finite` | A | `Basic.lean` |
| Thm 7.1 | 231 | natural representation: `U ⊂ V`, `Φ : G_x → Diff_sc(U)`, sc-smooth `Γ : G_x × U → X`, `Γ(g,x) = g`, `sΓ = id`, `tΓ = Φ(g)`, `Γ` onto the morphisms of `U` | `MPolyfold.IsScDiffeoOn`, `MPolyfold.IsLocalScDiffeo` | `MonoidHom`, `IsPreconnected` | C | `NaturalRep.lean` |
| (text) | 231–233 | small connected `U(x)`: morphisms of `U(x)` = `⊔_g U(g)`; `G_x ⋉ U(x)` is an ep-groupoid; `Γ` fully faithful; `Φ̂` on morphisms | `MPolyfold.prod`, discrete M-polyfold (new) | `CategoryTheory.Functor.Full`, `…Faithful`, `MulAction` | B | `NaturalRep.lean` |
| Prop 7.5 | 233 | natural representation of a finite set `Y` of isomorphic objects: a functor to sc-diffeos of disjoint connected `U(y)` | `MPolyfold.IsScDiffeoOn` | `CategoryTheory.Functor` | C | `NaturalRepFinite.lean` |
| Def 7.8 | 236 | natural representation of `Y` | — | — | A | `NaturalRepFinite.lean` |
| Prop 7.6 | 236 | `G_x\U(x) → \|U(x)\|` a homeomorphism; `G_x ⋉ U(x) → X` fully faithful | — | `MulAction.orbitRel.Quotient`, `isOpenMap_quotient_mk'_mul`, `Homeomorph` | B | `Uniformizer.lean` |
| Def 7.9 | 237 | local uniformizer | — | `CategoryTheory.Functor.FullyFaithful` | A | `Uniformizer.lean` |
| Def 7.10 | 237 | ep-subgroupoid: saturated sub-M-polyfold `A` | `MPolyfold.IsSubMPolyfold` | — | A | `SubGroupoid.lean` |
| Prop 7.7 | 238 | the full subcategory on `A` is an ep-groupoid (with the text's (1)–(4) before it) | `MPolyfold.subPolyfold`, `MPolyfold.SubData`, `MPolyfold.subPolyfold_inclusion_isScSmooth`, `MPolyfold.subPolyfold_retraction_isScSmooth`, `MPolyfold.paracompactSpace_subtype` | — | C | `SubGroupoid.lean` |
| Def 7.11 | 239 | effective; regular objects, `X_reg`; (text) `s φ` regular ⇒ `t φ` regular | — | — | A | `Effective.lean` |
| Lemma 7.2 | 239 | `X_reg` open | — | — | A | `Effective.lean` |
| Lemma 7.3 | 239 | effective ⟺ `Φ` injective on small `U(x)` | — | `MonoidHom.ker` | B | `Effective.lean` |
| Prop 7.8 | 240 | effective ⇒ `X_reg` open and dense | — | `Dense`, `Nat.card` | B | `Effective.lean` |
| Def 7.12 | 241 | `T_x` (acting trivially, normal), `X^T`, `X^R = X/∼` | — | `Subgroup.Normal`, `Quotient` | B | `Reduced.lean` (`T_x` normal: `Effective.lean`) |
| Prop 7.9 | 242 | `X^R` has a natural M-polyfold structure | `MChart`, `MAtlas`, `MChart.Compatible` | quotient topology | C | `Reduced.lean` |
| Prop 7.10 | 244 | reduced ep-groupoid `X_R`, effective; (text) its isotropy is `G_x/T_x` | — | `QuotientGroup` | C | `Reduced.lean` |
| Def 7.13 | 244 | `G_x^eff = G_x/T_x` | — | `QuotientGroup` | A | `Reduced.lean` |
| Thm 7.2 | 244 | `\|X\|` locally metrizable, regular, Hausdorff; paracompact ⇒ metrizable | `metrizableSpace_of_locally` (Smirnov) | `RegularSpace`, `T2Space`, `MetrizableSpace` | B | `OrbitTopology.lean` |
| Lemma 7.4 | 244 | `\|U(x)\|` metrizable (a `G_x`-invariant metric) | `MPolyfold.metrizableSpace` | `MetricSpace`, `Finset.sup'` | B | `OrbitTopology.lean` |
| Lemma 7.5 | 245 | countable neighbourhood bases | — | `FirstCountableTopology` | A | `OrbitTopology.lean` |
| Lemma 7.6 | 245 | `\|X\|` Hausdorff | — | `T2Space` | B | `OrbitTopology.lean` |
| Lemma 7.7 | 246 | `\|X\|` regular | `MPolyfold.metrizableSpace` | `RegularSpace` | B | `OrbitTopology.lean` |
| Cor 7.1 | 247 | second countable `\|X\|` ⇒ metrizable (Urysohn) | — | `TopologicalSpace.metrizableSpace_of_t3_secondCountable` | A | `OrbitTopology.lean` |
| Def 7.14 | 247 | component compact | — | `connectedComponent`, `IsCompact` | A | `OrbitTopology.lean` |
| Cor 7.2 | 247 | component compact `K` has an open `U ⊃ K` with `cl U` paracompact, `U` metrizable | `metrizableSpace_of_locally` | `isOpen_connectedComponent`, `LocallyConnectedSpace` | C | `OrbitTopology.lean` |
| Prop 7.11 | 247 | `X¹ = (X¹, 𝐗¹)` is an ep-groupoid; tame ⇒ tame | `MPolyfold.Level`, `MPolyfold.shift`, `MPolyfold.IsScSmoothMap.levelOne`, `theorem_2_16` | — | B | `Lift.lean` |
| Def 7.15 | 249 | ep-groupoid with paracompact orbit space (5) | — | `ParacompactSpace` | A | `Lift.lean` |
| Rem 7.1 | 249 | second countable objects ⇒ (5); (text) "not known" whether (1)–(4) ⇒ (5): not formalized | — | `SecondCountableTopology` | A | `Lift.lean` |
| Prop 7.12 | 249 | `\|X\|` paracompact ⇒ `\|X¹\|` paracompact | `metrizableSpace_of_pullback` (avoids Lemma 2.7) | — | B | `Lift.lean` |
| Thm 7.3 | 250 | continuous partitions of unity on `\|X\|`, invariant ones on `X` | — | `PartitionOfUnity.exists_isSubordinate` | A | `PartitionsOfUnity.lean` |
| Def 7.16 | 250 | ep-groupoid with sc-smooth partitions of unity | `MPolyfold.IsScSmoothPartitionOfUnity` | `PartitionOfUnity` | A | `PartitionsOfUnity.lean` |
| Rem 7.2 | 251 | no formal content | — | — | — | — |
| Thm 7.4 (= Thm 7.6, p. 255) | 251 | `\|X\|` paracompact, `X` admits sc-smooth partitions of unity ⇒ invariant ones for saturated covers | `MPolyfold.AdmitsScPartitionsOfUnity`, `isScSmoothMap_real_finsum`, `MPolyfold.IsScSmoothMap.real_add` | `LocallyFinite` | C | `PartitionsOfUnity.lean` |
| Def 7.17 | 251 | proper subsets; the properness property | — | `IsProperMap` | A | `ProperSubsets.lean` |
| Prop 7.13 | 251 | a proper subset is closed | — | — | A | `ProperSubsets.lean` |
| Prop 7.14 | 251 | `π(Q)` closed for proper `Q`; `\|X\|` paracompact: closed `A = π(Q)`, `Q` proper | — | `precise_refinement`, `exists_subset_iUnion_closure_subset` | B | `ProperSubsets.lean` |
| Thm 7.5 | 253 | = Thm 7.1, with `Φ(g) = t_g ∘ s_g⁻¹` | — | — | (7.1) | `NaturalRep.lean` |
| Lemma 7.8 | 253 | morphisms between points of `U₁` lie in the sheets `N_g` | — | `IsCompact.tendsto_subseq` | B | `NaturalRep.lean` |
| Lemma 7.9 | 254 | `U = ⋃_g t_g s_g⁻¹(U₂)` is invariant | `MPolyfold.IsScDiffeoOn` | — | B | `NaturalRep.lean` |
| Lemma 7.10 | 255 | invariant sc-smooth `f ≥ β` supported in `V(x)` | `MPolyfold.AdmitsScPartitionsOfUnity`, `isScSmoothMap_real_finsum` | — | B | `PartitionsOfUnity.lean` |
| Cor 7.3 | 256 | an atlas with Hilbert `E₀` ⇒ invariant sc-smooth partitions of unity | `MPolyfold.admitsScPartitionsOfUnity_of_hilbert`, `corollary_5_44` (Theorem 5.14 [5.43] an explicit hypothesis, `GodefroyTroyanskiWhitfieldZizlerStatement`) | — | A | `PartitionsOfUnity.lean` |

**New infrastructure** (no item of its own): `ProperMaps.lean` (proper maps between metrizable spaces
⟺ the sequential criterion every proof of the text uses; closed subsets of proper sets are proper; the
saturation `t(s⁻¹ Q')` of a closed `Q'` inside a proper set is closed), `LocConnected.lean` (retracts
and M-polyfolds are locally path connected: `r` maps segments of the convex `U ∩ C` to paths;
components are open), `Discrete.lean` (a finite discrete type as an M-polyfold with ℝ⁰ charts,
`G × U` by `MPolyfold.prod`, sc-smoothness on `G × U` ⟺ on each sheet), `LocalDiffeo.lean` (levels,
degeneracy, the transported tame atlas, level-1 versions of `IsScDiffeoOn` / `IsLocalScDiffeo`, `ℝⁿ`
admits sc-smooth partitions of unity via `SmoothPartitionOfUnity.exists_isSubordinate` and
`proposition_5_38`), `Michael.lean` (Lemma 2.7 [2.56]: a regular space whose open covers have locally
finite closed refinements is paracompact; finite unions of closed paracompact subspaces; Mathlib has
no Michael theorem).

### II.3 Design decisions (recommendations; the project lead to confirm)

* **P1. A structure of maps, with a bridge to `CategoryTheory`.** `GroupoidStr Obj Mor`: maps `src tgt :
  Mor → Obj`, `unit : Obj → Mor`, `inv : Mor → Mor`, a total `comp : Mor → Mor → Mor` with the laws
  asked on composable pairs (`src φ = tgt ψ`), i.e. Definition 7.1's five structure maps. `EpGroupoid`
  adds `PObj : MPolyfold Obj`, `PMor : MPolyfold Mor` and (1)–(4) with Part I's predicates. A bridge
  `EpGroupoid.Ob X` (type synonym) carries `CategoryTheory.Groupoid` with `Hom x y := {φ // src φ = x ∧
  tgt φ = y}`: isotropy groups are Mathlib's `vertexGroup`, conjugation `vertexGroupIsomOfMap`, and
  Props 7.5–7.6, Def 7.9 use `Functor.Full`/`Faithful`. Against `CategoryTheory` as the primary form:
  every proof of the chapter works with sequences and sheets of morphisms with moving end points,
  which live on the total space `Σ x y, x ⟶ y`; `eqToHom` bookkeeping would dominate, and the M-polyfold,
  fibred-product and sub-M-polyfold API of Part I is for plain types.
* **P2. Universes.** `Obj Mor : Type u`, one universe (Definition 7.1's "small category"; the bridge
  is a `Groupoid.{u, u}`). The models stay in `Type` (`ScBanach`). The category `EP` (Def 7.7) is a
  `LargeCategory` on bundled ep-groupoids in `Type (u+1)`; Chapter 10's weak fibred products stay in `u`.
* **P3. Properness** is Mathlib's `IsProperMap ((src ⁻¹' closure V).restrict tgt)` for some open `V ∋ x`
  (existential per point, as the text). Both spaces are metrizable (`MPolyfold.metrizableSpace`), so it
  equals "preimages of compacts are compact" (`isProperMap_iff_isCompact_preimage`) and the sequential
  criterion, proved once in `ProperMaps.lean`. Def 7.17 uses the same form.
* **P4. The orbit space** is `Quotient X.orbitSetoid` (`x ∼ y ↔ ∃ φ, src φ = x ∧ tgt φ = y`) with the
  quotient topology, proved equal to `isIsomorphicSetoid` of the bridge; `π = Quotient.mk`,
  `|X_k| = π '' levelSet k`, Prop 7.1 as `IsOpenQuotientMap π`.
* **P5. Condition (4)** is stated literally on `MPolyfold.subPolyfold (isSubMPolyfold_fibredProduct hs
  ht)`, the instances `ParacompactSpace (Mor × Mor)` and of the subtype supplied by `letI` from
  `MPolyfold.paracompactSpace_prod` and `MPolyfold.paracompactSpace_subtype`, inside one Prop-valued
  `def`; an equivalent **sheet form** (for a sheet `U(φ)` of `s`, `ψ' ↦ m((s|U(φ))⁻¹(t ψ'), ψ')` is
  sc-smooth near `ψ`) is proved and used in proofs.
* **P6. Natural representations are data**: `NaturalRep X x` with `U` open **and connected**, `Φ : G_x →
  Obj → Obj` a homomorphism into sc-diffeos of `U` (`IsScDiffeoOn` with inverse `Φ g⁻¹`), `Γ`, the
  properties of Thm 7.1; Γ sc-smooth on `G_x × U` via `Discrete.lean`, equivalently on each sheet. The
  uniqueness of `Γ` on connected `U` (two sections of `s` through `g` agree) is a lemma: Def 7.12's
  `T_x`, Lemma 7.3 and Prop 7.9 depend on it.
* **P7. Reduced groupoid.** Props 7.9–7.10 are formalized as an atlas of compatible charts `Ψ_φ` on
  `X^R`; the M-polyfold `X^R` (Definition 2.8 asks Hausdorff and paracompact) takes these two properties
  as hypotheses, discharged for effective `X` and for the witnesses (II.6, 2).
* **P8. Bookkeeping.** Lean names `definition_7_3`, `theorem_7_1`, …; restatements `theorem_7_5 :=
  theorem_7_1`, `theorem_7_6 := theorem_7_4`. Sign-off items V7.1, … in book order; gaps from G.70;
  `Findings.md` new "## Chapter 7"; `BookConcordance.md` gets a Part II section (2017 items and pages
  only). Definitions are written by the session lead first (§6.7, step 1), proofs delegated.

### II.4 Order of work for Chapter 7

| Wave | Files (all `Polyfold/Chapter7/`) | Items | Agents | Lines |
|---|---|---|---|---|
| W0 (lead; done) | `Groupoid.lean`, `EpGroupoid.lean`; the definitions of every other file | Defs 7.1–7.17, `NaturalRep`, P5 sheet form, bridge | lead, 1 session | 900 |
| W1 (done) | `ProperMaps.lean`, `LocConnected.lean`, `Discrete.lean`, `LocalDiffeo.lean`, `Michael.lean` | infrastructure; (text) p. 227–228, Def 7.6's tame `Mor` | 5 in parallel | 2,200 |
| W2 (done) | `Basic.lean`; `NaturalRep.lean`; `ProperSubsets.lean` | Props 7.1–7.4, Lemma 7.1, Def 7.7 remark; Thm 7.1 = 7.5, Lemmas 7.8–7.9, `G_x ⋉ U`; Props 7.13, 7.14 (1) | 3 (`NaturalRep` may need 2 sessions) | 2,600 |
| W3 (done) | `NaturalRepFinite.lean`; `Uniformizer.lean` + `OrbitTopology.lean`; `Effective.lean`; `SubGroupoid.lean` | Prop 7.5, Def 7.8; Prop 7.6, Def 7.9, Thm 7.2, Lemmas 7.4–7.7, Cors 7.1–7.2; Lemmas 7.2–7.3, Prop 7.8; Prop 7.7 | 4 | 3,200 |
| W4 (done) | `Reduced.lean`; `Lift.lean`; `PartitionsOfUnity.lean`; `ProperSubsets.lean` (7.14 (2), done in W2) | Props 7.9–7.10, Def 7.13; Prop 7.11–7.12, Rem 7.1; Thms 7.3–7.4, Lemma 7.10, Cor 7.3; Prop 7.14 (2) | 4 | 3,000 |
| W5 (done 2026-11-07) | `NonVacuity.lean`, then the reports | witnesses (II.5), the counterexample of II.6, 1; `Exposition/Chapter7.md`, `verification/ch07.md`, `cmp/ch07.json`, `pbp/part07.md`, concordance; round-trip audit | 1–2, then the lead | 800 |

Dependencies: W2 needs W0 and `ProperMaps`; `NaturalRep` needs `LocConnected` and `Discrete`; W3 needs
`NaturalRep`; Cor 7.2 needs `Michael`; W4's `Reduced` needs `Effective`, `PartitionsOfUnity` needs
`OrbitTopology` and `ProperSubsets`, `Lift` needs `LocalDiffeo` and `OrbitTopology`. Files of one wave
do not import each other. Checkpoint (build green, `Test.lean` lines, commit) after every wave.

### II.5 Hypotheses check (Findings, Chapter 3, item 190)

Chapter 7 states no hypothesis "for all charts". The places where a universal reading would be
vacuous or where satisfiability must be shown:

1. **Tameness** (Def 7.6, Prop 7.11, the tame `Mor`): use `MPolyfold.IsTame` (an equivalent atlas of
   tame retracts exists). "Every `IsChart` chart is modelled on a tame retract" is unsatisfiable by
   item 190's construction (a `[0, ∞)` factor with a constant retraction); `Mor`'s tame atlas is the
   transported one (`MPolyfold.transportChart`), not "all charts".
2. **Hilbert atlas** (Cor 7.3): existential, as `admitsScPartitionsOfUnity_of_hilbert` (one chart per
   point). "Every compatible chart has a Hilbert `E₀`" is unsatisfiable: `φ' = (φ, 0)` onto `O × {0} ⊂
   E ⊕ X`, `X = ScOneExample.X` (level 0 is `c₀`), `r'(u, v) = (r u, 0)`, is compatible with `φ`.
3. **Sc-smooth partitions of unity** (Def 7.16, Thm 7.4, Lemma 7.10: ∀ open cover ∃ partition):
   satisfiable; witness `rnPolyfold n` (`LocalDiffeo.lean`), and `GodefroyTroyanskiWhitfieldZizlerStatement`
   proved for `Fin n → ℝ` so that Cor 7.3's hypothesis is not empty either.
4. **Properness** (Def 7.3 (3)): per point ∃ `V(x)`; "for every neighbourhood" would fail for the pair
   groupoid of `ℤ`. Lemma: every open `V' ⊂ V(x)` also works.
5. **Effective** (Def 7.11, ∀ x ∀ g ≠ 1 ∀ nbhd ∃ ψ): satisfiable non-vacuously (ℤ/2 reflecting ℝ) and
   vacuously (trivial isotropy).
6. "`U(x)` **equipped with the natural action**" (Lemmas 7.3, 7.4, 7.10, Def 7.9, Prop 7.6): always a
   `NaturalRep` datum, which exists by Thm 7.1; never "every `U` with an action".
7. P7's hypotheses on `X^R`: satisfiable (effective `X`; the trivial-action groupoid).

Witnesses (`NonVacuity.lean`): the trivial ep-groupoid on `rnPolyfold n` (`Mor = Obj`, `s = t = id`;
tame by `rnPolyfold_isTame`), `ℤ/2 ⋉ ℝ` by reflection (effective, `X_reg = ℝ ∖ {0}`), `ℤ/3 × ℝ ⇉ ℝ`
with the trivial action (`T_x = G_x`, `X_R` trivial).

### II.6 Found while reading (to be checked in Lean, then recorded in `Findings.md`, "## Chapter 7")

1. **Def 7.7, remark (p. 228–229)**: "it is sufficient to require that the functor `f` is sc-smooth
   between the object spaces" does not hold as we read it; the proof chooses `U(φ)` with `f(U(φ)) ⊂
   U(ψ)`, i.e. uses continuity on morphisms. Example: `ℤ/3 × ℝ ⇉ ℝ` (trivial action), `f = id` on
   objects, `(g, y) ↦ (g, y)` for `y ≤ 0` and `(g², y)` for `y > 0`: a functor, sc-smooth on objects,
   not continuous on morphisms. With continuity added the remark holds.
2. **Props 7.9–7.10 (pp. 242–244)**: the proof gives charts with sc-smooth transitions but not that
   `X^R` is Hausdorff, which an M-polyfold must be; as we read it, it need not be. Take an sc-smooth
   splicing `π_t` on `ℝ × E` (Def 2.18, p. 36; the "chap" of p. 24) with `π_t = 0` for `t ≤ 0` and
   rank one for `t > 0`, `O = r(ℝ × E)`, and `ℤ/2` acting by `(t, e) ↦ (t, −e)`. In `ℤ/2 ⋉ O`, `T_y =
   ℤ/2` for `y = (t, 0)`, `t < 0`, but `T_{(0,0)} = 1`: the classes of `(1, (0,0))` and `(g, (0,0))`
   differ and cannot be separated. A Lean confirmation needs a dimension-jumping retract (not in the
   project; cost C, optional). *(2026-11-07: confirmed in Lean by the round-trip audit,
   `RoundTrip/Items/V7_40.lean`, namespace `NotB`; Remark 4.3's retract `RemarkFourThree.fam` is such a
   retract. Moved the same day into `Polyfold/Chapter7/ReducedNotHausdorff.lean`, namespace
   `Polyfold.EpGroupoid.Examples.JumpingRetract`; `Findings.md`, Chapter 7, item 107.)*
3. **Thm 7.1 / 7.5 (pp. 231, 253–254)**: "since the `N_g` are disjoint … `Φ` is a homomorphism" needs
   `U` connected (the sheet index of `Γ(g, Φ(h)y) ∘ Γ(h, y)` is only locally constant); take `U₂`
   connected, possible because M-polyfolds are locally path connected, which the text does not state.
   The same connectedness gives the uniqueness of `(Φ, Γ)` used tacitly for `T_x` (Def 7.12) and in
   Lemma 7.3.
4. **Thm 7.4, proof (pp. 255–256)**: Lemma 7.10 is applied to `(β_i ∘ π)|V(x_i)` "supported in
   `U''_i ⊂ V(x_i)`", but its hypothesis `cl U ⊂ V` holds for `W(x_i)` in the role of `V` (then `f_i` is
   supported in `W(x_i)`, possible misprint); the continuity of that cut-off uses property (4); and
   "the sum of all `h_i` is locally finite" needs `supp f_i ⊂ π⁻¹(cl V'_i)`, not stated. With these
   (and the closedness of saturations from properness) the theorem holds as we read it. Lemma 7.10's
   partition of unity "of `V(x)`" is taken for a cover of `X` (add `X ∖ cl U(x)`).
5. **Cor 7.2 (p. 247)**: "work in a connected component of `K`" needs open components (local
   connectedness of `|X|`), and "`U = ⋃ cl U(zᵢ)` is paracompact" needs Michael's lemma (Lemma 2.7);
   `U` names two sets (possible misprint).
6. Possible misprints: Lemma 7.1's proof exchanges source and target of the statement (it treats the
   inverses) and writes `V(y)` for `V(x)`; Prop 7.5's proof writes `G_{y1}` for `G_{y2}`, `Ψ_g` for `Φ_g`,
   "Let `k ≥ 3`" for `k ≥ 2`; Def 7.9 "`Ψx ◦ Gx ⋉ U(x) → X`"; Def 7.3 cites "[38], Lemma 2.8" for the
   fibred product, which is the text's Prop 2.15. Prop 7.5 is best proved by a star construction around
   `y₁` (all `U(y_j) = γ̂_j(U(y₁))`) rather than the text's induction.
7. Unstated but harmless: Prop 7.11's "(1), (2), (4) trivially" uses level-1 lifts of local
   sc-diffeomorphisms and `(X s×t X)¹ = X¹ s×t X¹` (level 1 only, no G.6 needed); Prop 7.12's proof
   (Lemma 2.7, locally finite closed unions) is replaced by `metrizableSpace_of_pullback` along `|X¹| →
   |X|`; Prop 7.14 (2) by shrinking in the normal `|X|`.

### II.7 Chapters 8–11 (coarse; items by section, `D/L/P/T/R/E` = Def/Lemma/Prop/Thm/Remark/Example)

| § | pp. | Items | Notes |
|---|---|---|---|
| 8.1 Tangent of an ep-groupoid | 257 | 15 (D1 L8 P1 T4 R1) | `TX` over `X¹` (Prop 7.11), functoriality, natural transformations |
| 8.2 Sc-differential forms | 268 | 2 (D2) | blocked: sc-forms (G.37–G.40) |
| 8.3 Strong bundles over ep-groupoids | 270 | 4 (D4) | `StrongBundle`, `StrongBundle.restrictOpen` |
| 8.4–8.5 Proper covering functors, appendix | 275 | 12 (D3 L3 P3 T2 R1) | geometric lift, local structure (uses Prop 7.5) |
| 9.1–9.2 Branched ep⁺-subgroupoids, tangent, boundary | 291 | 27 (D7 L9 P4 T1 R6) | M⁺-polyfolds (new), Ch. 4 submanifolds |
| 9.3 Orientations | 310 | 9 (D4 L1 R3 E1) | Ch. 6 finite-dimensional orientations |
| 9.4–9.5 Local branching, integration and Stokes | 315 | 23 (D6 L9 P2 T3 R3) | measures on branched manifolds, Stokes: likely "not formalized" as Thm 6.43 |
| 10.1–10.2 Equivalences, weak fibred product | 333 | 15 (D3 L2 P5 T2 R2 E1) | |
| 10.3 Localization | 347 | 16 (D6 L3 P1 T5 R1) | Mathlib `CategoryTheory.Localization`, calculus of fractions |
| 10.4–10.6 Strong bundles, localization, appendix | 357 | 14 (D6 P3 T3 R2) | proofs of Thms 10.3–10.4 in §10.6 |
| 11.1 Ep-groupoids and equivalences | 375 | 8 (D1 P3 T1 R2 E1) | faces: `MPolyfold.IsFace` |
| 11.2, 11.4 Forms, integration | 380, 396 | 12 (D2 L4 P2 T3 R1) | blocked with §8.2, §9.5 |
| 11.3, 11.5, 11.6 Branched, bundles, coverings | 389 | 20 (D5 L5 P3 T6 R1) | |

Counts are of numbered items found at the start of a line (Chapter 7 checked by hand: 52); about 177 for
Chapters 8–11, so about 229 for Part II. Of Chapters 8–11 about 37 items (§8.2, §9.4–9.5, §11.2, §11.4)
need forms, measures or Stokes; a decision like Chapter 6's D1 is due before Chapter 9.

### II.8 Size estimate

Chapter 7: about 12,700 Lean lines (W0 900, W1 2,200, W2 2,600, W3 3,200, W4 3,000, W5 800; Part I's
Chapter 2 is 15,200, Chapter 6 20,800), in about 18 agent sessions (W1 5, W2 3–4, W3 4–5, W4 4, W5 1–2)
plus 1 lead session for W0 and 2 for the reports and audit. Chapters 8–11, without the blocked
sections, roughly 25,000–35,000 lines; to be planned after Chapter 7's definitions have settled.

### II.9 Chapter 8 plan (2026-11-07)

**Text.** `sources/HWZ-Book-2017.txt` lines 12251–13855, pp. 257–290, 33 numbered items (Thm 8.1–8.6,
Lemma 8.1–8.11, Prop 8.1–8.4, Def 8.1–8.10, Rem 8.1–8.2), counted by hand.

| Item | p. | Content | Wave / file (`Polyfold/Chapter8/`) |
|---|---|---|---|
| Thm 8.1 | 258 | `T(X, 𝐗) = (TX, T𝐗)` is an ep-groupoid; tame if `X` is; `(p, p) : TX → X¹` an sc-smooth functor | W2 `TangentEp` (tame part: W3) |
| Lemma 8.1 | 259 | `(ψ, k) ∘ (φ, h) = Tm(k, h) = (ψ∘φ, Ts(ψ∘φ)⁻¹ Ts(φ) h)` | W2 `TangentEp` (sheet form, P3 below) |
| Lemmas 8.2–8.5 | 259–261 | source/target of a composite, associativity, units, inverses | W2 `TangentEp` |
| Lemma 8.6 | 262 | `s_T, t_T` surjective local sc-diffeos, structure maps sc-smooth | W2 `TangentEp`, from W1 `TangentLocal` |
| Lemma 8.7 | 262 | properness of `TX` | W2 `TangentEp` |
| Lemma 8.8 | 263 | `X` tame ⇒ `TX` tame (`Tr` tame) | W3 `TangentTame` |
| Rem 8.1 | 264 | the description by `(Tφ, a)`; `t_T ∘ (s_T|T_xX)⁻¹ = Tφ` | W2 `TangentEp` (linearity: P6) |
| Thm 8.2 | 265 | `TΦ` of an sc-smooth functor is an sc-smooth functor | W2 `TangentEp` |
| Thm 8.3 | 266 | `T : EP → EP` a functor preserving tameness | W2 `TangentEp` (P1 universes) |
| Def 8.1 | 266 | natural transformation / natural equivalence of sc-smooth functors; `≃` an equivalence relation (p. 267) | W0 lead, W2 |
| Prop 8.1 | 267 | `Tτ : TΦ → TΨ` is a natural transformation | W2 `TangentEp` |
| Thm 8.4 | 268 | `\|X\|` paracompact ⇒ `\|TX\|` paracompact | W3 `TangentOrbit` |
| Defs 8.2–8.3 | 268–270 | sc-forms on ep-groupoids, sc-de Rham complex | not formalized: sc-forms on M-polyfolds are not (G.37–G.40); new gap |
| Def 8.4 | 271 | strong bundle `(P, µ)` over an ep-groupoid | W0 lead `EpStrongBundle` |
| (text) | 271–272 | the functorial picture: `(W, 𝐗 ₛ×_P W)` an ep-groupoid, `(P, π₁)` an sc-smooth functor | W2 `EpStrongBundle` |
| Defs 8.5–8.7 | 273–275 | strong bundle maps / functors (equivalent), section functors, `Γ, Γ⁺, Fred` | W0 lead, W2 `EpStrongBundle` |
| Def 8.8 | 275 | proper covering functor | W0 lead `ProperCovering` |
| (text) | 275–276 | `d_{𝐗 ₛ×_F Y} = ½ d_{𝐗 × Y}` along the image of `𝐘` | W2 `ProperCovering` (optional) |
| Prop 8.2 | 276 | composites of proper covering functors | W2 `ProperCovering` |
| Thm 8.5, Rem 8.2 | 277 | Proper Covering I: local structure near `x`, `F⁻¹(x)` | W2 `ProperCoveringLocal` (uses Ch. 7 `NaturalRep`) |
| Def 8.9 | 279 | covering functor of finite groupoids, geometric lift into `Diff_sc` | W0 lead `GeometricLift` |
| Prop 8.3 | 281 | a geometric lift gives a proper covering functor | W3 `GeometricLift` (needs W1 `Sigma`) |
| Thm 8.6 | 283 | Proper Covering II: local model as a geometric lift | W3 `GeometricLift` |
| Def 8.10 | 285 | proper strong bundle covering functor | W0 lead, W3 |
| Lemmas 8.9–8.11 | 286–287 | counting in `F⁻¹(x)`: `#G_x = #G_{y₀} · #Θ_j`, `#Θ_j = #Θ'_j` | W1 `ProperCoveringCount` |
| Prop 8.4 | 288 | `#F⁻¹(x)` constant on components of `\|X\|`; `X → ℕ` an sc-smooth functor | W1/W2 `ProperCoveringCount` |
| (text) | 288–289 | `µ_X(Fφ) ∘ A_{sφ} = A_{tφ} ∘ µ_Y(φ)` | W3 |

**Decisions (recommendations).**

* **P1. Universes.** Part I's `TangentSpace` of `X : Type u` lives in `Type (max u 1)`, so `TX` is an
  `EpGroupoid` in `Type (max u 1)`; Theorem 8.3 is a functor `EP.{max u 1} ⥤ EP.{max u 1}`
  (`max (max u 1) 1 = max u 1`). An artifact of the formalization, recorded with the item.
* **P2. Tangents of local maps** (W1 `TangentLocal`): the tangent of an open restriction
  `T(U) ≅ p⁻¹(U) ⊆ TX` (an open embedding, sc-diffeomorphic onto its image, compatible with
  `tangentMap`), hence the tangent of a map sc-smooth on an open set, of an `IsScDiffeoOn`, and
  `IsLocalScDiffeo f ⇒ IsLocalScDiffeo (tangentMap f)` with `Tf` bijective on each fibre. The text
  uses all of this silently ("`Ts : TU(φ) → TU(x)` is a sc-diffeomorphism").
* **P3. The composition of `T𝐗`** is (8.6), `k ∘ h := (Ts|T_{p k ∘ p h}𝐗)⁻¹(Ts h)`, by choice as
  Chapter 7's `tangentMor`; condition (4) is proved in the sheet form (`IsScSmoothCompSheet`): on a
  sheet, `(Ψ, Φ') ↦ Ψ∘Φ'` is the tangent of the sc-smooth `φ' ↦ m(σ(t φ'), φ')`, so the
  identification `T(𝐗 ₛ×ₜ 𝐗) = T𝐗 ×ₜ T𝐗` is not needed (Lemma 8.1 as a formula on composable pairs).
* **P4. Global strong bundle maps** (W1 `StrongBundleMap`): Part I defines strong bundle maps only
  between local models (Def 2.22 [2.47]). Between strong bundles `B, B'` over M-polyfolds, covering
  `f`: `P' ∘ Φ = f ∘ P`, linear on the fibres, sc-smooth `Y[0] → Y'[0]`, maps `Y[1]` into `Y'[1]`
  and is sc-smooth `Y[1] → Y'[1]` (Part I's `toMPolyfold0`, `toMPolyfold1`); the double filtration
  follows (fibre linearity and levels). A reading, recorded.
* **P5. Def 8.4** on Part I's pull-back strong bundle `pullbackProj P src` over `𝐗` (Prop 2.54,
  `pullbackAtlas`): `µ : 𝐗 ₛ×_P W → W` a P4 strong bundle map covering `t`, a surjective local
  sc-diffeomorphism of the `[0]` M-polyfolds, (2), (3). The ep-groupoid of the functorial picture
  takes `𝐗 ₛ×_P W` with that M-polyfold structure.
* **P6. Linearity of `T_xX`.** Part I has no vector-space structure on the fibres `T_xX` (only
  in tangent charts). Linearity claims (Remark 8.1, G.70's "linear isomorphism") are proved in
  tangent charts if cheap, otherwise recorded with G.70.
* **P7. Def 8.9**: `D` a finite Mathlib `Groupoid` (`[Fintype D]`, finite hom-sets), `C` one object
  with isotropy a finite group `G` (`SingleObj G`); `Diff_sc` a category of bundled M-polyfolds
  (one universe) and sc-diffeomorphisms; `L_D, L_C` functors and `τ : L_D ⟶ f ⋙ L_C`.
* **P8. Disjoint unions** (W1 `SigmaPolyfold`): `Σ i, X i` of finitely many M-polyfolds, needed by
  Prop 8.3's `Y = ⊔ U(y)`, `𝐘 = ⊔ mor(y, y') × U(y)`.
* **P9. Bookkeeping.** Sign-off items V8.1, … in book order; gaps from G.74; `Findings.md` new
  "## Chapter 8" (numbering in blocks as Chapter 7: 1–99 items, 100–109 witnesses, 110– not formalized).

**Order of work.** W0 (lead): the definitions (Def 8.1, 8.4–8.10, the data of `TX`). W1 (parallel,
independent): `TangentLocal`, `SigmaPolyfold`, `StrongBundleMap`, `ProperCoveringCount` (Def 8.8 from
W0). W2: `TangentEp`, `EpStrongBundle`, `ProperCovering` (Prop 8.2), `ProperCoveringLocal`. W3:
`GeometricLift`, `TangentTame`, `TangentOrbit`, Def 8.10. W4: witnesses, then the reports. Estimate:
6,000–9,000 Lean lines.

**Found while reading** (to be checked, then recorded in `Findings.md`, "## Chapter 8"; possible
misprints unless said otherwise): (8.5) `T_{φ∘ψ}𝐗` for `T_{ψ∘φ}𝐗`; Lemma 8.2's proof ": U(ψ∘φ) → U(x)"
without `s`; Lemma 8.7's proof `Ts(φ_k)(h_k)` for `Tt(φ_k)(h_k)`; Remark 8.1 `T_yY` for `T_yX`;
Theorem 8.5 (5): the right arrow `t` and the corner `U(t(F(ψ₀)))`, as printed the square
`F ∘ s = t ∘ F` does not hold as we read it (with `s` it commutes); Theorem 8.5's proof `g ∈ G_y`,
"`G_y`-invariant" for `G_x`, and `F(z') = s(F(φ))` for `t(F(φ))`; Proposition 8.3's proof
"`F : X → Y`" for `Y → X`; Theorem 8.6's `A(ψ, z) = (f(z), F(z))` for `(f(ψ), F(z))` and `τ(t)` for
`τ(y)`; Lemma 8.10's proof "the third claim of Lemma 8.10" for Lemma 8.9.

### II.10 Chapter 9 plan (2026-11-08)

**Chapter 9, Branched Ep⁺-Subgroupoids, pp. 291–331** (text lines 13868–15800 of
`Exposition/sources/HWZ-Book-2017.txt`). Sections: §9.1 Basic Definitions (p. 291), §9.2 The Tangent
and Boundary of Θ (p. 297), §9.3 Orientations (p. 310), §9.4 Geometry of Local Branching Structures
(p. 315), §9.5 Integration and Stokes (p. 322), §9.6 Appendix (questions, pp. 330–331).

Inventory (text line numbers; pages to be checked against the page heads):
§9.1: Remark 9.1 (13883), Definition 9.1 (13903), Remark 9.2 (13922), Lemma 9.1 (13946), Definition 9.2
(13966), Lemma 9.2 (14011), Definition 9.3 (14022), Proposition 9.1 (14032), Remark 9.3 (14042).
§9.2: Proposition 9.2 (14136), Theorem 9.1 (14208), Definition 9.4 (14231), Lemma 9.3 (14241),
Remark 9.4 (14276), Lemma 9.4 (14284), Definition 9.5 (14290), Lemma 9.5 (14308), Proposition 9.3
(14386), Lemmas 9.6–9.8 (14401, 14436, 14467), Definition 9.6 (14615), Lemma 9.9 (14656), Remark 9.5
(14661), Proposition 9.4 (14711), Definition 9.7 (14757), Remarks 9.6–9.7 (14768, 14780).
§9.3: Definition 9.8 (14841), Remark 9.8 (14859), Lemma 9.10 (14877), Definitions 9.9–9.11 (14989,
15001, 15026), Remark 9.9 (15053).
§9.4: Definition 9.12 (15067), Lemmas 9.11–9.14 (15088, 15101, 15144, 15176), Definitions 9.13–9.14
(15169, 15220), Lemma 9.15 (15226), Propositions 9.5–9.6 (15287, 15378).
§9.5: Definitions 9.15–9.17 (15442, 15456, 15733), Lemma 9.16 (15449), Theorem 9.2 (15467), Lemmas
9.17–9.19 (15494, 15639, 15658), Remarks 9.10–9.12 (15628, 15705, 15771), Theorems 9.3–9.4 (15743,
15774).
In all about 64 items (17 Def, 19 Lemma, 6 Prop, 4 Thm, 12 Rem, plus §9.6's questions).

Decisions (proposed; P10.x):
* P10.1 `Θ : Obj → ℚ` with values `≥ 0` (`ℚ⁺ = ℚ_{≥0}`), "functor" = `Θ (s φ) = Θ (t φ)` for every
  morphism; support `{x | 0 < Θ x} ⊆ X_∞` (`MPolyfold.smoothSet`).
* P10.2 Submanifolds are Part I's smooth finite-dimensional submanifolds
  (`MPolyfold.IsSmoothSubmanifold`, Definition 4.4 [4.13]); "the inclusion `M_i → U(x)` is proper"
  as `IsProperMap (Subtype.val : M_i → U(x))`; a local branching structure is a structure with a
  `Fintype` index set, the sets, the weights `σ_i > 0` in `ℚ`, and the sum formula on `U(x)`.
* P10.3 Dimension: `n`-dimensional via the dimension of the tangent spaces of the `M_i` if Part I
  provides it; otherwise recorded as a gap.
* P10.4 Proposition 9.1 (natural manifold/orbifold structures on `|supp Θ|`), the M⁺-polyfold
  notions of §9.1, and everything that needs forms, measures or Stokes (§9.4–§9.5, Definition 9.8's
  orientations through forms) depend on gaps G.37–G.40/G.74; decide (as Chapter 6's D1) before
  wave W2 whether to build Lebesgue measure on finite-dimensional submanifolds or to gap §9.5.

Waves: W0 `Chapter9/Basic.lean` (Definitions 9.1–9.3, Remark 9.2 (b) example, Lemmas 9.1–9.2,
witnesses: the zero functor, a single submanifold, `ℤ/2`-symmetric pair of lines); W1 §9.2 (tangent
and boundary of `Θ`, good points, Lemmas 9.3–9.9, Propositions 9.2–9.4, Theorem 9.1); W2 §9.3
orientations; W3 §9.4–§9.5 after the decision P10.4; W4 reports.
