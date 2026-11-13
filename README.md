# Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory*, Parts I–III, in Lean 4

Part I of HWZ's book, *Basic Theory in M-Polyfolds* (the sc-calculus, retracts and M-polyfolds,
strong bundles, sc-Fredholm sections, the implicit function theorems, the Fredholm package and
orientations),
formalized against Mathlib with the same faithful layer as our formalizations of Milnor's
*Topology from the Differentiable Viewpoint* and *Morse Theory*
([`math_faithful`](https://github.com/skydancerosel/math_faithful)). Part II, *Ep-Groupoids*,
Chapters 7–11, is formalized, except part of the example of Remark 9.5.20 (its branched
subgroupoid and integrals). Part III, *Fredholm Theory in Polyfolds*, Chapters 12–16, is begun
(waves 1–7 of 13 November 2026, below). The authoritative text is the
Springer edition (Ergebnisse der Mathematik und ihrer Grenzgebiete 72, 2021): the reports cite its three-level numbers and
pages first, with the numbers of the earlier versions in parentheses (the 2014 preprint, arXiv
1407.3185, for Part I; the 2017 arXiv version, 1707.08941, for Part II). Lean names use the
2021 numbers (`theorem_3_6_8` is Theorem 3.6.8 of the Springer edition). Where an earlier or
auxiliary form of a statement is kept as well, its name says which: `_preprint` or `_2017` for
the statement of an earlier version, `_hyp` for a form with auxiliary hypotheses, `_param` for
the form a proof produces, `_2021def` for a statement in the 2021 definitions.
`Exposition/BookConcordance.md` maps the three numberings, and `Exposition/rename-2021.tsv` the
Lean names used before 9 November 2026 to the current ones.

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
3. **Check each item.** Each of the 1,099 items has a one-sentence summary and a label saying how the
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

## Status (13 November 2026): Parts I–III

* **Part I, Chapters 1–6, is formalized**, with Theorem 6.7.1 (preprint 6.43; the invariant `Ψ_(f,o)`)
  proved without hypotheses on the cobordism (below). Since the
  Part I completion wave of 12 November 2026 every gap of Chapters 1–3 is closed, and of the 78 gaps of
  Chapters 1–6 one remains open in part: families on `[0, 1]ⁿ` beyond Proposition 6.6.3 and Lemmas
  6.6.4–6.6.5 (G.65 in part; since 13 November 2026 (1′) holds for paths on `[0, 1]` and `L` is a bundle
  over `[0, 1]` for `n = 1`). Closed on 13 November 2026 (wave K): the wedge product on `Ω*_∞(X, ∂X)`,
  with the product of the mapping cone of `j^*` (the text gives none; our choice), the pull-back of forms
  on `∂X` along a general map being neither defined in the 2021 text nor used beyond Theorem 6.7.1, where
  it is formalized (G.80); and Proposition 6.6.3 (1) in its 2021 wording, `U′ ⊂ U` sc-smoothly
  contractible in `U` (G.61; the earlier reading, `U` itself contractible, was the preprint's). Three
  more have nothing to formalize: the text's open question after Proposition 4.2.3 (G.34; its settled
  sentence is proved), a remark on the literature (G.43), and preprint Theorem 5.27, which the 2021
  edition drops (G.49).
  Closed in this wave, among others: Example 1.1.3 (the weighted Sobolev spaces on `ℝ × S¹`, with
  Rellich's theorem on bounded cylinders), Proposition 2.1.2, Lemma 2.4.9, Lemmas 2.7.3, 3.8.1–3.8.3,
  3.8.9–3.8.11, 3.8.20, Theorem 3.7.1 for a general sc-splitting, Lemma 4.1.11, Theorem 5.3.15, the
  Banach-space Theorems 5.5.5, 5.5.13 and 5.5.16, Corollary 5.5.17 without hypothesis, Lemma 6.6.5 with
  `L` a smooth bundle, and the remarks on `DET(E, F)` and on the orientation bundle.
* **Part II, Chapters 7 and 8, is formalized** (ep-groupoids, orbit spaces, invariant partitions of
  unity; the tangent ep-groupoid and functor, strong bundles over ep-groupoids, proper covering
  functors). In the 2021 text the reduced ep-groupoid exists when `T_R` is Hausdorff (Theorem
  7.2.14), and `T_R` is always paracompact (proved); that `𝐗^R` need not be Hausdorff is checked in
  Lean. Since the Part II wave of 12–13 November 2026 every gap of Chapters 7 and 8 is closed. In
  Chapter 7: Corollary 7.6.6 as printed (Theorem 5.5.16 is no longer a hypothesis); Proposition
  7.2.10, Theorem 7.2.14 and Proposition 7.2.16 in their 2021 form; Theorem 7.6.7 and Corollary
  7.6.8 for every `i`, as isomorphisms in `EP` under (SLUC) or (ZHOU); and Zhou's example of
  Appendix 7.6.3 itself, on `L²(ℝ)` with `E_m = H^{m,δ_m}(ℝ)`, its non-effective part computed as
  printed (G.82, G.83). In Chapter 8: the sc-differential forms of §8.2 (Definitions 8.2.1, 8.2.2:
  `Ωᵏ_ep(X)`, the direct limit and the sc-de Rham complex) with the Poincaré lemma, Proposition
  8.2.3; Lemma 8.1.2 as printed; and Proposition 8.4.1 with `|W[1]|` as an orbit space (G.74, G.75,
  G.86, G.87). Remark 8.1.10 stays narrower: with `Tφ` the bare linear map, the map `G` is not
  injective (checked in Lean). The facts of Part I that Chapter 7
  relies on are proved for every M-polyfold: `X_∞` is dense in every `X_k`, `U ∩ X_∞` is connected
  for connected open `U`, `p : TX → X¹` is open, the tangent `Tφ` of a smooth morphism is an
  sc-isomorphism, and the orbit space has its filtration `|X_∞|` (G.8, G.70, G.72, G.73, G.85, G.90).
* **The additions and changes of the 2021 edition in Chapters 1–8 are formalized**, among them
  locally complete spaces (§2.1), the tame boundary `bX` (§2.7, Theorem 2.7.13) and the boundary
  ep-groupoid (Theorem 7.6.9), Proposition 2.3.17 for all `i`, the global Lie bracket (§4.4–4.5),
  the topology of the orientation space (Theorem 6.6.17), the rewritten §7.2 and the Zhou condition
  (§7.4, §8.1).
* **The sc-differential forms of §4.4 are formalized**, with the wedge product (a graded algebra,
  `d` a derivation) and the Poincaré Lemmas 4.4.8 and 4.5.2: Definitions 4.4.1–4.4.2 (the forms read in the charts of the Whitney sum, the direct
  limit `Ω*_∞(X)`), the exterior derivative on an M-polyfold with `d² = 0`, the sc-de Rham
  cohomology of Definition 4.4.6, the pull-back `f^*` with `f^*d = df^*`, forms on `∂X` (read as
  forms on the tame boundary `bX` that agree over `bX → X`), `j^*` with `dj^* = j^*d`, the relative
  complex `Ω*_∞(X, ∂X)` and `H*_dR(X, ∂X)`, and Theorem 4.4.7 (Stokes) for sc-forms restricted to
  finite-dimensional submanifolds with a corner structure. The formula for `dω` on p. 197 holds
  with the sign `(−1)^{ℓ+j+1}` for the text's bracket; with the printed sign it does not hold as we
  read it. The agreement of a form on `∂X` implies that of its `d` (so the forms on `∂X` are those of
  the text), and Theorem 4.4.7 holds with the sum over the faces of a face-structured submanifold
  (G.37, G.39, G.40 closed; G.80 closed on 13 November 2026 with the wedge product on `Ω*_∞(X, ∂X)`).
* **Theorem 6.7.1 (the invariant `Ψ_(f,o)` on `H*_dR(X, ∂X)`) and its case `∂X = ∅` are proved
  without hypotheses on the cobordism** (`theorem_6_7_1`, `theorem_6_7_1_noBoundary`,
  `Polyfold/Chapter6/Theorem671Final2021.lean`; restated; G.54 closed): the standing hypotheses are those of
  the text, `X` tame with sc-smooth bump functions, and the proper oriented homotopy of (2) is read as in
  R-d. Proved on 12 November 2026: the product orientation `SectionOrientation.prodFirst` of Remark 6.6.19
  (G.66 closed), the orientation `cobOr` of the cobordism `S_F` and its value `e ∧ o_{S_i}` on the two ends,
  the time vector first and with no sign (`cobordismOrientationHyp`, `isEndProductOrientation_cobOr`), and
  the closed relative form on `S_F` (`cobordismRelativeFormsInner`, built on
  inner ends, with the pull-back of forms on `∂X` along `p₁`). Proved before: the admissible sections of §6.7 (G.55 closed), the
  index parts of `S_{f+s}` as compact oriented manifolds, `Ψ` for one admissible section, well
  defined on classes, the cobordism identity, and the theorem from its two independence statements.
  The homotopies of (2), which the text does not define, are read through Remark 6.6.19 (Findings,
  Chapter 6, items 128–134).
* **Part II, Chapter 9, is formalized**, §§9.1–9.5 (branched ep⁺-subgroupoids, local branching
  structures, the tangent and the boundary, good points, orientations, the geometry of local
  branching structures, sets of measure zero and the canonical σ-algebras). The level-0 facts it
  needs are proved for every M-polyfold (local constancy of the dimension, domain invariance,
  continuity on level 1, graph charts; G.93, G.97, G.98, G.100), and Proposition 9.1.11
  (existence and uniqueness of the local dimensional decomposition, in the reading of its proof)
  and Proposition 9.1.12 hold for every ep-groupoid. The footnote to Definition 9.1.2 holds for `Θ`
  with nonempty support (for `Θ = 0` it does not hold as we read it), Lemma 9.4.3 holds as stated
  (G.104), and the boundary orientation of Definition 9.3.8 is continuous along the stratum of
  reduced codimension 1, without tameness; for a tame sheet that stratum is open and dense in `∂M`,
  a smooth submanifold of dimension `n − 1` oriented by `o_∂M`, and Part I's face orientation is
  `o_∂M` on it, which gives Figure 9.1 (G.103). Since 12 November 2026: Remark 9.1.4 and Proposition 9.1.9 hold, the
  latter with the text's groupoid `⊔M_x` and independent of the choices up to a generalized
  isomorphism; Remark 9.1.10 holds for `n`-dimensional `Θ`, the composition of the orbifold
  groupoid being sc-smooth (Mathlib has no classical orbifolds) (G.94, G.95). Example 9.3.5 has
  infinitely many orientations, six of them with integer weights (G.101). For the sheets of every
  M-polyfold, read in M-polyfold charts, Lemmas 9.4.4, 9.4.6 and 9.5.2 hold with Hausdorff null
  sets (G.105, G.106). Since 13 November 2026 the integral of an sc-differential form over an
  oriented sheet is constructed (in graph charts of the M-polyfold, over sheets covered by
  countably many of them), and Theorems 9.5.4, 9.5.5, Definition 9.5.6, (9.22) and Proposition
  9.5.13 hold for it, reading the text's "oriented, tame" as: near every point of the support an
  oriented tame structure describes the orientation (derived when there is no boundary); the unit
  circle in `ℝ²` witnesses the hypotheses (G.107). The `(n − 1)`-dimensional null sets of the
  boundaries are Hausdorff null sets in the charts (G.108). Since wave K (13 November 2026) the boundary
  measures of Theorems 9.5.15, 9.5.16 and Stokes' Theorems 9.5.17, 9.5.18 are proved as printed,
  for every `n ≥ 1` and with the text's hypotheses only (`EP.theorem_9_5_15` … `EP.theorem_9_5_18`,
  the `_dim1` forms for `n = 1`): the finiteness of the integrals over the boundary sheets, which
  the text uses tacitly, is derived near the corners from Part I's chart forms and toward the
  frontier by comparing tangent spaces (G.109 closed). Witnesses with nonempty boundary: a closed
  hemisphere (`n = 2`, also with LUC) and a closed half-circle (`n = 1`). Remark 9.5.20 is formalized
  in part: its M-polyfold with dimension jumps `0 → 3 → 0`, the `ℤ₃`-action with LUC and the
  effective isotropy `3` versus `1` of a boundary point read in `X` and in `∂X`; its `Θ` and
  integrals are not (G.110 in part, for the remark only).
* **Part II, Chapter 10, is formalized**, §§10.1–10.5 with the Appendix proofs 10.6.1–10.6.3
  (equivalences of ep-groupoids, natural equivalences, the weak fibred product, localization at the
  equivalences, the category of generalized maps and the orbit-space functor, strong bundle
  equivalences, push-forward and pull-back of sections along generalized strong bundle
  isomorphisms, the weak fibred product of strong bundles and the category `SEP(F⁻¹)`). Local
  regularity under equivalences (Propositions 10.1.9, 10.1.10, 10.1.19, 10.3.16) is proved.
  Theorems 10.3.19 and 10.5.7 do not hold as we read them (counterexamples in Lean); both hold
  when the target is effective. The Fredholm parts of Theorems 10.4.5 and 10.5.4 are proved, and
  `[D]_*` is a linear isomorphism of the section spaces. Since 12 November 2026 every gap of the
  chapter is closed: the subcategory `EP_lreg`, Remark 10.1.8 with Zhou's example of Appendix
  §10.6.3 as printed (on `ℝ ⊕ H^{m,δ_m}(ℝ)`), the triple-product structures of Theorem 10.2.2,
  the universal property of the localization (`EPLoc.isLocalization`), Propositions 10.4.6,
  10.4.7 and 10.5.6 (Definition 8.4.2 read for local strong bundle isomorphisms), (10.24) with the
  local expressions `q`, `Q`, and the converse of the strong bundle Theorem 10.3.10 (the
  isomorphisms of `SEP(F⁻¹)` are exactly the generalized strong bundle isomorphisms).
* **Part II, Chapter 11, is formalized**: the tangent functor on `EP(E⁻¹)`, the
  degeneracy index and the faces under generalized isomorphisms, with the faces as tame
  ep-groupoids and the generalized isomorphisms `[d]_F` (§11.1), the sc-differential forms up to
  equivalence (§11.2), branched
  ep⁺-subgroupoids, their tangent sections and orientations pushed forward and pulled back
  (§11.3; Theorem 11.3.9 for the generalized isomorphism itself, with the intrinsic boundary
  orientation and no added hypothesis, G.130), strong bundles up to equivalence (§11.5), and
  equivalences of proper coverings with Theorem 11.6.6 and Proposition 11.6.8 (§11.6), with
  Proposition 11.5.1 in full and the local section structures of sc⁺-multisections (Definition
  13.2.1) in Lemma 11.5.2 and Proposition 11.5.3 (G.132, G.133), and since 12 November 2026 the
  localization `PC(E⁻¹)` with `I : PC → PC(E⁻¹)` and the category of proper strong bundle
  coverings of Remark 11.6.9 with its localization (G.128, G.129, G.134, G.135 closed). The
  intersection clause of Proposition 11.1.6 does not hold as we read it (below, item 13); its
  union form is proved. Since 13 November 2026 also §11.4: generalized isomorphisms transform
  the canonical measures and their effective versions by `|f|` (Theorems 11.4.1, 11.4.2, Remark
  11.4.3), and the boundary measures, with the text's hypotheses for every `n ≥ 1` since 13
  November 2026 (Theorems 11.4.4, 11.4.5; G.131 closed).
* **Part III, Chapters 12–16, is begun** (waves 1–7, 13 November 2026; 212 files, 68,330 lines, in
  `Polyfold/Chapter12/` to `Chapter16/` and `Chapter5/P3R_*`, `P3B_*`, `P3W5TY_*`, `P3W7*`). Part I
  prerequisites: the reflexive auxiliary norms and the reflexive local compactness of §§5.1–5.2
  (Definitions 5.1.4–5.2.6, Proposition 5.1.8, Theorem 5.2.8) and the ∂-extension theorem 5.4.2,
  with weak sequential compactness in reflexive spaces. Chapter 12: sc-Fredholm section functors,
  the existence of auxiliary norms (Theorem 12.2.2), continuous partitions of unity, the good
  neighbourhood theorem, the extension of auxiliary norms from the boundary (Theorem 12.2.7 as
  printed), reflexive auxiliary norms (Theorems 12.2.11 and 12.2.13, the latter with the
  paracompactness of `|X|` named), bump functions and sc⁺-section functors (Theorems 12.3.2,
  12.3.3), the local and equivariant extension from the boundary (Proposition 12.3.7, Corollary
  12.3.8, Theorem 12.3.9), the compactness notions of §12.4 with the reflexive ones (Theorems
  12.4.2, 12.4.6), and the orientation bundle (§12.5, with Part I's hypotheses, G.140), with the
  continuity statements of Theorem 12.5.3 and Proposition 12.5.6 and Theorem 12.5.7 as printed,
  with the independence of the representative and functoriality for the data of the diagrams
  (G.192 for Chapter 10's diagram objects). Chapter 13: good systems of neighbourhoods (Theorems
  13.1.7, 13.1.8), the bi-action and Proposition 13.1.9, the support, norm, symmetric structures and
  the decorated algebra of sc⁺-multisections, structurable sc⁺-multisections (§13.3 with Proposition
  13.3.19), pull-back and push-forward along equivalences and coverings (Theorems 13.4.1, 13.4.3,
  13.4.4) and the extension from `V` with `|V| = |X|` (Proposition 13.4.2), commensurable sums, and
  atomic sc⁺-multisections (§13.5; Theorem 13.5.3 as an equivalence with the existence of a good
  system, Theorem 13.5.7). Chapter 14: good neighbourhoods with tame faces and structured
  sc⁺-multisections over `∂X`, Proposition 14.1.8 in a stronger form (no added
  hypothesis), the extension of the correspondences, z-loops with Proposition 14.4.6 as printed and
  coherent neighbourhood systems, the local extensions (Proposition 14.4.14) for the objects of
  §14.3, Proposition 14.5.4 and the structurability criterion (Theorem 14.5.5); Theorem 14.1.9 with
  tame strong bundle charts and nonempty index sets `I_x` added (the reading of the factor `1/|I_x|`,
  necessary), with a witness with `∂X ≠ ∅` (G.172, G.186); §14.6 for representatives that agree on
  the faces, with sc⁺ on the corners (G.173, G.185). Chapter 15: the
  linearization `T(f, Λ)` is well defined and a functor, with sc-Fredholm summands (Theorem 15.1.1);
  transversality, good position, tame local solution sets and the ep-groupoid `U(x)` of §15.2 with
  Part I's tame germ data (Theorems 15.2.2, 15.2.5); the compactness control, admissible
  perturbations, general position and the auxiliary norm on `[0, 1] × X` of §15.3; Theorem 15.3.7
  under the text's hypotheses; Theorem 15.3.9 with nonempty index sets from the relative local
  families of its proof, Corollary 15.3.10 (3) from it on the cylinder, Theorem 15.4.3, Corollary
  15.4.4 along the text's argument with the oriented end identities assumed, Theorem 15.4.1 at a
  chart point, and the product strong bundle (G.159, G.160, G.162, G.178–G.180, G.182, G.189–G.191,
  G.193).
  Chapter 16: polyfold structures and their metrizability, morphisms and sc-smooth maps, polyfolds,
  the invariance of bump functions, partitions of unity, tameness and the degeneracy index (§16.1);
  the tangent polyfold, the raised polyfolds, the tangent functor (a functor on effective polyfolds)
  and the de Rham complex (§16.2); strong polyfold bundles, auxiliary and reflexive auxiliary norms
  independent of the model, and sections, the zero section included (§16.3); branched suborbifolds with the naturality of the structure on
  the support, their integrals and Stokes' theorem with sc-smooth partitions of unity (§16.4,
  G.153); sc⁺-multisections over polyfolds and the Fredholm notions, Theorem 16.6.4 as printed,
  Theorem 16.5.7 with the readings of Theorem 14.1.9, and Theorem 16.6.6 with the integrals well
  defined and the independence of `λ` given the cobordisms (§§16.5–16.6, G.175, G.176, G.187,
  G.188). The
  uniqueness sentence after Definition 16.1.2, Remark 16.1.7, Lemma 16.2.1, the composite of
  Definition 16.1.10 and the uniqueness after Definition 16.3.3 do not hold as we read them (below,
  items 14 and 15) and are proved for effective polyfolds.
* About 447,000 lines of Lean in 978 files under `Polyfold/`; every theorem has its axioms printed in
  `Polyfold/Test.lean` (22,322 declarations), all on `propext`, `Classical.choice`, `Quot.sound`; no
  `sorry`, no `axiom`.
* **Every numbered item of Chapters 1–11, and of the parts of Chapters 12–16 done so far,
  is compared with its formal version** (1,192 items, each with a verdict: same, restated,
  hypothesis made explicit, stronger, narrower, extra, or nothing to formalize), with a gap list of
  what is not formalized and why (G.1–G.193). 73 items are narrower than the text, each with its
  reason (47 of them in Part III); 166 of the 193 gaps are closed, 3 have nothing to formalize,
  and 24 remain: G.65 in Part I (families on `[0, 1]ⁿ`, read on `ℝⁿ`) and G.110 in Part II (the
  example of Remark 9.5.20: its `Θ` and integrals), both in part, and twenty-two Part III gaps
  (G.140, G.153, G.159, G.160, G.162, G.172, G.173, G.175, G.176, G.178–G.180, G.182, G.185–G.193).
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
| `Exposition/ReviewerChecklist.md` | **Start here to review.** The statements and definitions a person has to check (Lean checks the rest), in five tiers: the Part I core, orientation, Part II, Part III (waves 1–7), the tame boundary. |
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
   tame charts for the germ data (the 2021 text uses "tame strong bundle" from Theorem 3.6.8 on
   without defining it, and its Definition 3.6.3 no longer says "tame"; we read the phrase as the
   preprint and the 2017 version define it, and the theorems hold for the plain 2021 notion at
   germs centred at interior points; with the 2021 notion as printed Theorem 3.6.8 (2) does not hold as we
   read it, Findings, Chapter 3, item 388, G.79); "a bump function with `f ≠ 0`" as `f(x) ≠ 0`; Definition 6.2.1
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
   misreading on our side would remove it; telling which is the reviewer's task. Theorem 3.2.3
   itself holds as printed, by another route (`theorem_3_2_3`, V3.24). How the 2021 edition
   reads at the eight points: the same at six (Theorem 3.2.3, Theorem 4.3.1, Theorem 5.5.10,
   Definition 1.1.9, Theorem 5.5.7, §5.3), although Theorem 4.3.1 is restated in its conclusion (1);
   changed at Remark 2.4.8, which now gives an example (the intersection of a 3-plane
   with `[0,∞)⁴`) that, as we read it, is not an sc-smooth retract, so the claim still has no valid
   example; fixed at Lemma 5.3.16, since Definition 5.3.13 (3) now asks `dt` onto at every smooth
   point, which supplies the hypothesis the proof of Theorem 5.3.15 (preprint 5.22) needed
   (`Exposition/BookConcordance.md`, `Findings.md`, marks "book 2021"). Also: hypotheses a proof seems
   to use without stating them, and possible misprints. Since 12 November 2026 three more printed claims do not
   hold as we read them, each with a Lean counterexample: Theorem 3.6.8 (2), p. 136, and the sub-M-polyfold
   conclusion of Theorem 3.1.22, with the 2021 germ data as printed, by a tame strong bundle over `ℝ` whose
   solution set is a closed half-line (`theorem_3_6_8_untamed_not`, V3.130; Findings, Chapter 3, item 388);
   Lemma 3.8.1, p. 145, at `P = {0}` (V3.123; item 386); and the remark that `DET(E, F)` is not orientable,
   p. 262, for finite-dimensional `E`, `F` (V6.80; Chapter 6, item 135). Also: the tameness of `X` in Theorem 5.3.10
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
    decomposition exists: read this way, the proposition holds for every branched
    ep⁺-subgroupoid of every ep-groupoid (`existsUnique_localDimDecomposition_general`,
    `Polyfold/Chapter9/GeneralCorollaries.lean`; first over `ℝᵐ`, `proposition_9_1_11_local_rn`;
    Findings, Chapter 9, items 106, 107).
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
13. **Proposition 11.1.6** (p. 524; 2017: 11.2): that two faces of a tame face structured
    ep-groupoid which meet do so in a face of each does not hold as we read it. The
    counterexample, checked in Lean, is an open subset of `[0,∞)³ ⊕ W` (a 3-manifold with boundary
    and corners for `W = 0`) in which two faces meet in an edge with a middle piece removed, two
    components (`FaceMeetExample.not_facesMeetInFaces`, `Polyfold/Chapter11/GapP2_H2FaceMeet.lean`;
    V11.6; Findings, Chapter 11, item 9). What is proved for every face structured ep-groupoid is
    that the intersection is the union of the faces of each that it contains
    (`IsEpFaceStructured.facesMeetInUnions`). Is "a union of faces" meant?
14. **The sentence after Definition 16.1.2, Remark 16.1.7 and Lemma 16.2.1** (pp. 707, 711, 716,
    with pp. 709–710; 2017: Definition 16.2, Remark 16.1, Lemma 16.3): that the generalized
    isomorphism between equivalent polyfold structures is unique, as a consequence of (ZHOU),
    does not hold as we read it. The
    trivial `ℤ/3`-ep-groupoid on `ℝ` satisfies (ZHOU) and has paracompact orbit space, so it is a
    polyfold structure on `ℝ`, and the pair of item 12 gives two generalized isomorphisms with the
    same orbit map (`PolyfoldStructure.not_uniqueness_16_1_2`, `not_remark_16_1_7`,
    `Polyfold/Chapter16/P3Z_ZhouUniquenessCheck.lean`; V16.3, V16.7; Findings, Chapter 16, items
    1, 2). Both hold for an effective target (`uniqueness_16_1_2_of_isEffective`,
    `remark_16_1_7_of_isEffective`). The same pair contradicts Lemma 16.2.1 (equal underlying maps
    give equal `𝔣` and `T𝔣`; `not_lemma_16_2_1`, V16.15; Findings, Chapter 16, item 6), whose orbit
    form `|𝔣| = |𝔤|`, `|T𝔣| = |T𝔤|` holds and is all §16.2 uses. Is an effectiveness hypothesis
    intended here as well?
15. **Definition 16.1.10 and the sentence after Definition 16.3.3** (pp. 711, 723; 2017: Definition
    16.7, after Definition 16.17): that the composite of sc-smooth maps does not depend on the
    choices, and that `f` and `F` are uniquely determined by the orbit conditions, do not hold as we
    read them, for the same cause as item 14: a non-effective isotropy acting trivially. A
    `(ℤ/3)²`-structure on `ℝ` with the trivial action gives two composites
    (`not_definition_16_1_10`, `Polyfold/Chapter16/P3W3Y_CompositionCounterexample.lean`; V16.32;
    Findings, Chapter 16, item 12), and the trivial `ℤ/3`-bundle over `ℝ` two pairs `(f, F)` that
    differ on the bases (`not_uniqueness_16_3_3`, `P3W3V_UniquenessCheck.lean`; V16.40; item 11).
    Both hold for effective polyfolds (`PSHom.Equiv.comp_of_isEffective`,
    `uniqueness_16_3_3_of_isEffective`), and the polyfold category is formalized as the category of
    effective polyfolds. Is an effectiveness hypothesis intended in Chapter 16?

## Open questions

None of these is a hypothesis of a theorem of the project; each is stated precisely in the Findings.

* Whether the text's germ reading and the stricter whole-chart reading of Definition 3.1.11 (preprint 3.11), p. 96, agree for
  sections sc-smooth on `X` (Chapter 3, item 264).
* Whether a weak bump function (Definition 5.5.2 (preprint 5.29), p. 229) gives one non-zero at a given point of a
  general M-polyfold (Chapter 5, item 163; on an sc-Banach space it does at every point, since its bump points
  are all points or none, item 180).
* The local constancy of the index along the zero set for germ data that are not tame (item 243).
* A single family `P^i` for all `i` in Corollary 5.2.5 (preprint 5.8), p. 213 (the tameness of the shifted charts
  is proved, Chapter 5, item 181).
* The text's own open question after Proposition 4.2.3 (preprint 4.15), Question 4.2.4, p. 187.

Settled since: whether germ data can always be moved to a compatible tame chart when the atlas is tame
(Chapter 3, items 199, 350–353, 379, 382): they cannot, `UntamedCorner.isScFredholmGerm2021_not_tame`
(`Polyfold/Chapter3/GapP1_UntamedBundleTheorem.lean`; item 388). The text's own question on p. 340 of Part II (2017: p. 249), whether property (5) of a
paracompact orbit space follows from properties (1)–(4) of an ep-groupoid, has a negative answer: the Čech
groupoid of a Prüfer-type surface with uncountably many charts is an ep-groupoid whose orbit space is not
paracompact (`exists_epGroupoid_not_hasParacompactOrbitSpace`, `Polyfold/Chapter7/PropertyFiveResearch.lean`;
Chapter 7, item 152).

Not formalized (by decision, see the gap list in the comparison): preprint Theorem 5.27 (in neither the 2017 nor
the 2021 text), the pull-back of forms on `∂X` along a general sc-smooth map, which the 2021 text neither defines nor
uses beyond Theorem 6.7.1 (G.80 closed; the forms on an M-polyfold, `d`, the wedge product, also on `Ω*_∞(X, ∂X)`, the
Poincaré lemmas, the pull-back, forms on `∂X`, the relative complex and Stokes' theorem are formalized), the preprint's
form of Proposition 6.6.3 (1), `U` itself contractible (the 2021 form is proved, G.61 closed), the families on
`[0, 1]ⁿ` beyond Proposition 6.6.3 and Lemmas 6.6.4–6.6.5, `L` over `[0, 1]ⁿ` for `n ≥ 2` and Remark 6.6.19 over
`[0, 1] × X` (G.65 in part), the sc-structure `W^{1+m,4}(Ω)` of the Sobolev remark after Theorem 5.5.5 for bounded domains other
than `(0, 1)` (G.51, closed for that domain). (Theorem 6.7.1 (preprint 6.43) is proved without hypotheses on the
cobordism since 12 November 2026, `theorem_6_7_1`, G.54 closed.) Not formalized either: the infinite-dimensional examples of the applications (splicings; the
weighted Sobolev scale of Example 1.1.3 is formalized). (In Chapter 7 the tangent `Tφ` of a morphism, the filtration `|X_∞|` and the density
of `X_∞` in `X_k`, gaps G.70, G.72, G.73, are now formalized; the paracompactness and
Hausdorffness of `𝐗^R`, gap G.71, are settled, see item 6 above.) In Part II: in §9.5 the branched subgroupoid `Θ`, `∮_Θ̂ df` and the
two boundary integrals of Remark 9.5.20 (its M-polyfold, the `ℤ₃`-action and the effective isotropy are formalized;
estimated at 2,340–3,790 lines, the risks being sc-smooth partitions of unity on a `c₀` scale and tameness at the
infinite-dimensional ends) (G.110 in part); the product
`f·ω` of a form with a non-constant function in `Ω*_ep(X)` ((9.22) is proved through the evaluation).
Also not formalized: Remark 9.1.10 for `Θ` of several dimensions; `W[1]` as an ep-groupoid (its orbit space
is); the wedge product on `Ω*_{ep,∞}` as a graded algebra on the type (it is a DG subalgebra of Part I's);
the side remark of Appendix 10.6.3 that Zhou's retract is homeomorphic to `ℝ² ∖ {(0, t) | t ≠ 0}`; and the
identification of `H^{m,δ}(ℝ)`, defined by lifting to `ℝ × S¹` with the same norm, with the
weak-derivative space on `ℝ`. (In Chapter 8 the forms of §8.2 and Lemma 8.1.2 as printed, gaps G.74, G.75,
are formalized since 12 November 2026.)

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
