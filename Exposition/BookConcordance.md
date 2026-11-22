# Book concordance: the 2014 preprint, the book's arXiv version and the Springer edition (Part I, Chapters 1–6; Part II, Chapters 7–8; Part III, Chapters 12–16; Part IV, Chapters 17–19)

The exposition and the formalization follow Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory
I*, in the 2014 preprint (arXiv 1407.3185, `sources/HWZ-PartI-2014.txt`); the Lean names of Part I
carry the preprint's statement numbers. Part II has no preprint, and there the Lean names carry the
2017 numbers (section "Part II" at the end); the V- and G-numbers of the reports are the project's
own. The published book (Springer 2021; text in `sources/HWZ-Book-2021.txt`, which is not in the
repository, since `sources/` is gitignored) is the authoritative version from Chapter 9 on. The report citations of Chapters 1–8
(`Findings.md`, the chapters, `verification/`, `pbp/`, `cmp/`) give the 2021 statement numbers and pages
first, with the preprint's (Part I) or the 2017 text's (Part II) in parentheses, as in "Theorem 3.5.6
(preprint 3.43), p. 126 (preprint p. 102)" or "Proposition 7.1.15 (2017: 7.5)"; a page that could not
be located in the 2021 text keeps its old number, marked "(preprint p. …)" or "(2017 p. …)". The section
"The Springer edition (2021), Chapters 1–8" below gives the correspondence. The book's arXiv version is
**arXiv 1707.08941v1 (27 July 2017)**, the only version on arXiv (text in `sources/HWZ-Book-2017.txt`),
whose Part I (Chapters 1–6) corresponds to the preprint's Part I. **Every result recorded in the
sections before "The Springer edition" is a result about the 2017 arXiv text**, whose pages and late
corrections may differ from the Springer edition's; the 2021 section records the differences.
Pages of the 2017 text are its printed page numbers (Part I starts on p. 3).

**Method.** The numbered items (Definition, Lemma, Proposition, Theorem, Corollary, Remark, Example)
were extracted from `pdftotext -layout` texts of both versions with their pages, and each preprint
item was matched to a 2017 item by the text of its statement (sequence alignment within each chapter);
every weak or missing match was then checked by hand. Chapter 6 was matched by
hand, item by item, from the statements, with the pages read off the page headers and footers of the
two texts. All 279 numbered items of the preprint's Chapters 1–6 are listed; 274 have a counterpart,
5 are absent, and the 2017 text has 40 numbered items in Chapters 1–6 without a preprint number
(listed after the tables).

**Annotation convention** (used in `Findings.md`, in `Chapter1.md`–`Chapter3.md` at the places
checked against the 2017 text, and in the module docstrings of
`Polyfold/Chapter3/`–`Chapter6/`): *(book 2017: …)* gives the result of the check
against arXiv 1707.08941: *unchanged* (the point is in the 2017 text as well), *corrected*,
*renumbered* (a citation number of the preprint carried over under the 2017 numbers), or the 2017 statement number and page, e.g.
*(book 2017: Theorem 3.13, p. 99)*. A general remark such as "statement numbers are the
preprint's" points here instead: *(book 2017: see `BookConcordance.md`)*.

## Structural differences

- **Numbering restarted.** The preprint numbers all statements of a chapter with one counter
  (Definition 3.48, Remark 3.49, Definition 3.50, …). The 2017 text has a separate counter for each
  kind of statement, so numbers collide across kinds: Definition 3.13 (the filling, p. 97) and
  Theorem 3.13 (the implicit function theorem, p. 99) are different statements. Displayed equations
  are numbered by chapter, e.g. (3.44). Citations of the preprint that name another kind of
  statement than the one presumably meant ("Proposition 3.40" for Theorem 3.40) survive with the new number and may now point at an
  existing statement of that kind with a different content (see `Findings.md`, "Numbering and pages").
- **Chapter and section titles.**

  | Preprint 2014 | pp. | arXiv 1707.08941 | pp. |
  |---|---|---|---|
  | 1 Sc-Calculus | 6–17 | 1 Sc-Calculus | 3–14 |
  | 1.4.3 Proof Lemma 1.24 | 17 | 1.4.3 Proof Lemma 1.1 | 13 |
  | 2 Differential Geometry Based on Retracts | 18–60 | 2 Retracts | 15–56 |
  | 2.6.1–2.6.3 Proofs of Proposition 2.2, Theorem 2.16, Proposition 2.19 | 54–60 | 2.6.1–2.6.3 Proofs of Proposition 2.1, Theorem 2.2, Proposition 2.5 | 49–56 |
  | 3 Basic Sc-Fredholm Theory | 61–146 | 3 Basic Sc-Fredholm Theory | 57–130 |
  | 3.1 Sc-Fredholm Sections and Some of the Main Results | 61 | 3.1 Sc-Fredholm Sections | 57 |
  | 3.8.1–3.8.3 Proofs of Proposition 3.22, Lemmas 3.46, 3.55 | 120–135 | 3.8.1–3.8.3 Proofs of Proposition 3.3, Lemmas 3.9, 3.10 | 107–119 |
  | 3.8.4 Diffeomorphisms Between Partial Quadrants in $\mathbb R^n$ | 135 | 3.8.4 Diffeomorphisms Between Partial Quadrants | 119 |
  | 4 Manifolds with Boundary with Corners | 147–168 | 4 Manifolds and Strong Retracts | 131–150 |
  | 5 The Fredholm Package for M-Polyfolds | 169–199 | 5 Fredholm Package for M-Polyfolds | 151–180 |
  | 5.4 Appendix: 5.4.1 Proof of Theorem 5.5 | 189–192 | merged into §5.2, proof of Theorem 5.1 | 155–158 |
  | 5.4.2 Notes on Partitions of Unity and Bump Functions | 192–199 | 5.5 (same title) | 173–180 |
  | — | | 5.4 Remark on Extensions of Sc⁺-Sections (new) | 172–173 |
  | 6 Linearizations, Orientations, and Invariants | 200–237 | 6 Orientations | 181–221 |
  | 6.5 Local Orientation Propagation and Orientability | 219 | 6.5 Local Orientation Propagation | 204 |
  | 6.6 Invariants Associated to Proper Sc-Fredholm Sections | 230 | 6.6 Invariants | 215 |
  | 6.7.1–6.7.2 Proofs of Lemma 6.5, Proposition 6.12 | 234–237 | 6.7.1–6.7.2 Proofs of Lemma 6.1, Proposition 6.5 | 218–221 |

  The other sections keep their titles and order. The page offset grows from 3 (Chapters 1–2) to
  16–19 (Chapters 4–6), so a preprint page does not convert by a fixed shift; use the tables.
- **Appendices.** The appendices 1.4, 2.6, 3.8 and 6.7 stay at the end of their chapters. The preprint's
  appendix 5.4 is dissolved: the proof of Theorem 5.5 (= 5.1) now follows the theorem in §5.2, the
  notes on partitions of unity are §5.5, and a new §5.4 states a ∂-extension theorem for sc⁺-sections
  (Definition 5.11, Theorem 5.9) with a sketch of proof only. The preprint restates Proposition 3.22,
  Lemma 3.46, Lemma 3.55 (Appendix 3.8) and Theorem 5.5 (Appendix 5.4.1) under their own numbers; the
  2017 text restates Proposition 3.3 without a number, but Lemmas 3.9 and 3.10 as new Lemmas 3.22
  and 3.23. Appendix 6.7 proves Lemma 6.5 (= 6.1) and Proposition 6.12 (= 6.5) in both versions
  without restating them.
- **Dropped.** Theorem 3.35 (the germ implicit function theorem over any finite-dimensional partial
  quadrant, quoted from [21], Theorem 2.7) with the paragraph introducing it; Theorem 5.25
  (perturbation into good position), Lemma 5.26 (general position implies good position; the 2017 text keeps
  its claim as one sentence without proof, p. 166) and Theorem 5.27 (cobordism between good-position
  perturbations); Lemma 6.10 (two good left-projections have a common lower bound in `Π_T`). In
  place of Lemma 6.10 the 2017 text remarks that such a lower bound need not exist in general
  (p. 190) and compares two projections with the same range instead (Lemmas 6.3–6.5, Definition
  6.6, Proposition 6.6, pp. 189–195); `Findings.md`, Chapter 6, item 4, records that this remark
  does not hold as we read it, and the preprint's route is the one formalized.
- **New.** Definition 2.18 and Lemma 2.5 (an sc-smooth splicing gives a tame retraction, p. 36);
  Proposition 2.11 (a tame retraction preserves the local faces at a corner, p. 39); M⁺-polyfolds
  (Definition 4.8, Proposition 4.4, p. 146); strong bundles with reflexive $(0,1)$-fibres, mixed
  convergence and reflexive auxiliary norms (Definitions 5.2–5.4, Lemma 5.2, Proposition 5.2,
  pp. 153–154); the reflexive local compactness property and a compactness theorem near the boundary
  (Definition 5.6, Proposition 5.3, Theorem 5.4, Remarks 5.1–5.2, pp. 159–161); the ∂-extension
  theorem of §5.4; several remarks. Six paragraphs that the preprint leaves unnumbered became
  Remarks 1.1, 2.4, 3.3, 3.4, 3.7 and 4.2. In Chapter 6: Remark 6.1 (the tameness hypothesis of
  Proposition 6.1 is probably not needed, p. 183); Lemma 6.2 (`Φ_E` is natural under isomorphisms of
  exact sequences, p. 188); and, in place of Lemma 6.10, the comparison of good left-projections
  with the same range: Lemma 6.3 (good left-projections are stable under small changes of `T` and
  `P`), Remarks 6.2 and 6.3, Lemma 6.4, Definition 6.6 (the projections `P_H` onto a fixed range
  `H`), Lemma 6.5 and Proposition 6.6 (isomorphisms between the sequences `E(T,P)` and `E(T,Q)`,
  continuous in `T`), pp. 189–195.
- **Hypotheses and wording.** "Tame" is dropped from the interior part of Chapter 3 (the filling,
  Definitions 3.4 and 3.13; sc-Fredholm germs and sections, Definitions 3.5, 3.7, 3.8, 3.14, 3.15;
  Theorems 3.1–3.3, Corollary 3.1, Proposition 3.5, Theorem 3.14) and kept for the boundary results
  (Definition 3.16, Theorems 3.5, 3.13, 3.15); Remark 3.9 (new) says that good position at interior
  points does not need tameness. Proposition 2.17 (= 2.57) assumes "regular Hausdorff" for "regular".
  Definition 2.25 (= 2.50) writes a strong bundle chart as $(\Phi,P^{-1}(V),(K,C\triangleleft F,
  E\triangleleft F))$ and asks for "a bounded linear isomorphism" on the fibres (the preprint: "a
  bounded linear operator"); Definition 3.3 follows. Some titles change (Theorems 3.14, 3.15, 5.6).
  In Chapter 6, Lemma 6.11 becomes Proposition 6.4. Proposition 6.28 (= 6.12, p. 205) has two
  neighbourhoods $U' \subset U$, its (1) reading "$U'\subset U$ is sc-smoothly contractible in $U$
  to the point $x$", and Proposition 6.32 (= 6.13, p. 209) takes its path in $U'$; Theorem 6.35
  (= 6.1) and Definition 6.36 (= 6.10, p. 212) no longer ask the neighbourhood to be contractible
  (Definition 6.10: "open path connected"), and property (∗) of Theorem 6.37 (= 6.2, p. 213) is
  asked on orientable neighbourhoods. Lemma 6.25 (= 6.11, p. 204) has no proof of its own; the
  text refers to the discussion around Propositions 6.5 and 6.6.
- **Bibliography.** Renumbered; the items cited in Chapters 1–5 include the preprint's [20] (JEMS 2007,
  "A General Fredholm Theory I") = the book's [36], [21] (GAFA 2009, "… II: Implicit Function
  Theorems") = [37], [25] (the 2010 paper, "Sc-Smoothness, Retractions and New Models for Smooth
  Spaces") = [42]; Chapter 6 cites [4] (Donaldson–Kronheimer) = [8], [8] (Floer–Hofer, coherent
  orientations) = [16], [27] ("Applications of Polyfold Theory I", whose appendix §6.2 follows) =
  [43] and [45] (Zinger, the determinant line bundle) = [75].

## Is the 2017 text a later version in substance?

Yes in its organisation and its additions (above), hardly in the parts that `Findings.md` examines.
Spot checks of statements and proofs that `Findings.md` flags:

- *Unchanged, verbatim or nearly:* the proof of Proposition 1.4 (= 1.10, pp. 11–12; the missing
  bootstrap of the regularizing step); Theorem 1.2 (= 1.25, p. 11; still no proof, "[36], Theorem
  1.19"); the appendix proof of Proposition 2.5 (1) (= 2.19, p. 54; the preimage under a pointwise
  linearization); Definition 2.25 (= 2.50, p. 47; the base map only a homeomorphism, the
  `[1]`-transition taken for granted); Corollary 3.1 (= 3.13, p. 65); Theorem 3.8 (= 3.30, p. 77; still
  "from [37], Theorem 2.3", no proof); Lemmas 3.14–3.15 (= 3.62–3.63, p. 107; still quoted from [37]);
  the proof of Theorem 3.13 (= 3.54, p. 101: "Property (4) follows from Corollary 3.5 and from the
  following lemma") with the filling, Definition 3.13 (= 3.48, p. 97), whose condition (3) is imposed at
  the point $0$ only — so the step of `Findings.md` item 100 that the text does not spell out is in the 2017 text as well.
- *Unchanged (the points raised in the notes to the authors):* the sentence
  "$F = C \oplus T(E_m)$" after Definition 1.5 (= 1.8, p. 6); Remark 2.2 (= 2.28, p. 29); the step
  "$\delta$ is a sc$^\infty$-germ near $v_0$" in the proof of Theorem 3.6 (= 3.27, p. 74), whose
  statement is also unchanged; "the finitely many such neighborhoods" in the proof of Theorem 4.4
  (= 4.23, p. 147), whose statement is also unchanged; the one-dimensional `Z` with
  $T_xX = Z \oplus \ker dt(x)$ in the proof of Theorem 5.8 (= 5.22, pp. 168–169), with no submersion
  hypothesis in Definition 5.10 or Theorem 5.8; "Clearly" before Theorem 5.11 (= 5.34, p. 175);
  "the sc-smooth function $f \circ \varphi$" for a continuous `f` in the proof of Theorem 5.12
  (= 5.37, p. 176); "$(\Gamma^{+,1}_U(P), \rho)$ is not complete" (p. 162); in Theorem 5.5 (= 5.13,
  p. 162) "$N(f(x)) \le 1$" and "the germ $(f, x)$ is in good position"; in Theorem 5.7 (= 5.19,
  p. 167) "the pair $(f, x)$ is in good position", and its proof word for word; the function
  $\sigma$ of Proposition 5.5 (= 5.30, p. 174); "it is a priori clear that $f^i$ is sc-Fredholm"
  before Corollary 5.1 (= 5.8, p. 158), with only $Y[i]$, $i = 0, 1$, defined (p. 47); Definitions
  5.7 and 5.13 (= 5.9, 5.29, pp. 161, 174), "$f \ne 0$" against "not identically zero"; Remark 4.1
  (= 4.3, p. 132), still without an example.
- *Changed:* Lemma 2.6 (= 2.40, pp. 40–41), whose proof now rests on the new Proposition 2.11 for the
  step that `Findings.md` calls the key point; the splicings (Lemma 2.5), which answer an open
  question of `Findings.md`. Theorem 5.6 (= 5.18, p. 164) now assumes `X` tame, the hypothesis the
  preprint's proof uses without stating it (`Findings.md`, Chapter 5, item 80); Theorem 5.5
  (= 5.13) still does not assume it (item 61). Definitions 3.14 and
  3.15 (= 3.50, 3.51, p. 98) drop "tame strong bundle" and "tame strong local bundle"; tameness
  enters only through the filling, Definition 3.13 (p. 97), "covering the tame retraction `r`" of
  the chart that carries the germ data. This is the reading the project chose for "tame" (germ data
  in a tame chart; `Findings.md`, Chapter 3, items 190–199).
- *Points of wording:* of the 26 or so points of spelling and of citation numbers in the preprint
  marked in `Findings.md` and the chapters, one is corrected ("sunspace", p. 69) and all the others
  are in the 2017 text as well, the citations renumbered; an unmarked spelling is corrected too
  ("kerenel" in Theorem 3.15, p. 102).
  One preprint number is left standing in the 2017 text: "In view of Lemma 3.44" (p. 115) for
  Lemma 3.7.
- *Chapter 6.* Of the twelve points of notation and omissions marked in
  `Findings.md`, Chapter 6, two are corrected: "$(f-s)'(x)$ is a sc-Fredholm operator if and only
  if $(f-s)'(x)$ is" before Definition 6.1 now has $(f-t)'(x)$ in the second place (p. 182), and
  Definition 6.39's "$y \in U_\infty$" reads "$y \in X_\infty$" (Definition 6.12, p. 213). The
  other ten are in the 2017 text as well: in §6.7.1 (pp. 218–219) "$\det(\tau)$" for $\det(\sigma)$, "$\beta(C)$"
  and the names of the two blocks of the wedge in $C$; the same exchange of names in Proposition
  6.6 (= 6.3, p. 188); "$\alpha_q$" in §6.7.2 (p. 221); "$j(e) = (0, e)$" in the proof of Lemma
  6.14 (= 6.6, p. 199); the name $\varphi$ for the isomorphism of (94) in Proposition 6.15 (= 6.7,
  p. 199); the section $f$ not introduced in Theorem 6.35 (= 6.1, p. 212); "$\psi(\beta(s))$" on
  $[1/2, 1]$ in the composition of paths (p. 213); the extension $p_1^*\omega \wedge p_2^*dt$ in the
  proof of Theorem 6.43 (= 6.4). Formula (94) (= (6.10), p. 199) and Remark 6.42
  (= 6.4, p. 214), where the project uses the sign $(-1)^{\dim\operatorname{coker}}$ (`Findings.md`,
  Chapter 6, items 50 and 95), are unchanged. Lemma 6.10 and the neighbourhoods of §6.5 change
  (above, "Dropped" and "Hypotheses and wording").

## Concordance, Chapters 1–6

Pages: "p." is the page of the statement's heading (for a section, of its title). "absent": no
counterpart in the 2017 text.
Notes record only changes met while checking the marks and the spot checks above; an empty note
does not certify that the statement is verbatim.

### Chapter 1 (preprint pp. 6–17; arXiv 1707.08941 pp. 3–14)

| Preprint 2014 | p. | arXiv 1707.08941 | p. | Note |
|---|---|---|---|---|
| Definition 1.1 | 6 | Definition 1.1 | 3 |  |
| Example 1.2 | 6 | Example 1.1 | 4 |  |
| Definition 1.3 | 7 | Definition 1.2 | 4 |  |
| Definition 1.4 | 7 | Definition 1.3 | 4 |  |
| Definition 1.5 | 7 | Definition 1.4 | 4 |  |
| Proposition 1.6 | 7 | Proposition 1.1 | 5 |  |
| Proposition 1.7 | 8 | Proposition 1.2 | 5 |  |
| Definition 1.8 | 9 | Definition 1.5 | 6 |  |
| Proposition 1.9 | 9 | Proposition 1.3 | 6 |  |
| Proposition 1.10 | 10 | Proposition 1.4 | 7 |  |
| Definition 1.11 | 10 | Definition 1.6 | 7 |  |
| Definition 1.12 | 10 | Definition 1.7 | 7 |  |
| Definition 1.13 | 10 | Definition 1.8 | 7 |  |
| Definition 1.14 | 10 | Definition 1.9 | 7 |  |
| Remark 1.15 | 11 | Remark 1.2 | 8 |  |
| Proposition 1.16 | 12 | Proposition 1.5 | 9 |  |
| Proposition 1.17 | 12 | Proposition 1.6 | 9 |  |
| Proposition 1.18 | 13 | Proposition 1.7 | 9 |  |
| Proposition 1.19 | 13 | Proposition 1.8 | 10 |  |
| Corollary 1.20 | 13 | Corollary 1.1 | 10 |  |
| Theorem 1.21 | 13 | Theorem 1.1 | 10 |  |
| Remark 1.22 | 13 | Remark 1.4 | 10 |  |
| Definition 1.23 | 14 | Definition 1.10 | 11 |  |
| Lemma 1.24 | 14 | Lemma 1.1 | 11 |  |
| Theorem 1.25 | 14 | Theorem 1.2 | 11 | still no proof ("[36], Theorem 1.19") |

### Chapter 2 (preprint pp. 18–60; arXiv 1707.08941 pp. 15–56)

| Preprint 2014 | p. | arXiv 1707.08941 | p. | Note |
|---|---|---|---|---|
| Definition 2.1 | 18 | Definition 2.1 | 15 |  |
| Proposition 2.2 | 18 | Proposition 2.1 | 15 |  |
| Definition 2.3 | 18 | Definition 2.2 | 16 |  |
| Proposition 2.4 | 19 | Proposition 2.2 | 16 |  |
| Definition 2.5 | 19 | Definition 2.3 | 16 |  |
| Proposition 2.6 | 20 | Proposition 2.3 | 17 |  |
| Definition 2.7 | 20 | Definition 2.4 | 17 |  |
| Theorem 2.8 | 21 | Theorem 2.1 | 18 |  |
| Definition 2.9 | 22 | Definition 2.5 | 19 |  |
| Proposition 2.10 | 23 | Proposition 2.4 | 20 |  |
| Definition 2.11 | 23 | Definition 2.6 | 20 |  |
| Definition 2.12 | 24 | Definition 2.7 | 21 |  |
| Definition 2.13 | 24 | Definition 2.8 | 21 |  |
| Definition 2.14 | 24 | Definition 2.9 | 21 |  |
| Lemma 2.15 | 25 | Lemma 2.1 | 22 |  |
| Theorem 2.16 | 25 | Theorem 2.2 | 22 |  |
| Definition 2.17 | 25 | Definition 2.10 | 22 |  |
| Definition 2.18 | 26 | Definition 2.11 | 22 |  |
| Proposition 2.19 | 27 | Proposition 2.5 | 23 |  |
| Definition 2.20 | 28 | Definition 2.12 | 25 |  |
| Proposition 2.21 | 28 | Proposition 2.6 | 25 |  |
| Definition 2.22 | 31 | Definition 2.13 | 27 |  |
| Lemma 2.23 | 31 | Lemma 2.2 | 27 |  |
| Proposition 2.24 | 31 | Proposition 2.7 | 27 |  |
| Definition 2.25 | 31 | Definition 2.14 | 27 |  |
| Lemma 2.26 | 31 | Lemma 2.3 | 28 |  |
| Definition 2.27 | 33 | Definition 2.15 | 29 |  |
| Remark 2.28 | 33 | Remark 2.2 | 29 |  |
| Lemma 2.29 | 33 | Lemma 2.4 | 29 |  |
| Proposition 2.30 | 35 | Proposition 2.8 | 31 |  |
| Theorem 2.31 | 35 | Theorem 2.3 | 31 |  |
| Corollary 2.32 | 37 | Corollary 2.1 | 33 |  |
| Definition 2.33 | 39 | Definition 2.16 | 35 |  |
| Definition 2.34 | 39 | Definition 2.17 | 35 |  |
| Proposition 2.35 | 41 | Proposition 2.9 | 36 |  |
| Proposition 2.36 | 41 | Proposition 2.10 | 37 |  |
| Definition 2.37 | 42 | Definition 2.19 | 38 |  |
| Definition 2.38 | 42 | Definition 2.20 | 38 |  |
| Definition 2.39 | 43 | Definition 2.21 | 39 |  |
| Lemma 2.40 | 43 | Lemma 2.6 | 40 | proof fuller (cites the new Proposition 2.11) |
| Corollary 2.41 | 44 | Corollary 2.2 | 41 |  |
| Proposition 2.42 | 44 | Proposition 2.12 | 41 |  |
| Proposition 2.43 | 44 | Proposition 2.13 | 41 |  |
| Proposition 2.44 | 46 | Proposition 2.14 | 42 |  |
| Theorem 2.45 | 46 | Theorem 2.4 | 43 |  |
| Proposition 2.46 | 46 | Proposition 2.15 | 43 |  |
| Definition 2.47 | 48 | Definition 2.22 | 44 |  |
| Definition 2.48 | 49 | Definition 2.23 | 45 |  |
| Definition 2.49 | 50 | Definition 2.24 | 46 |  |
| Definition 2.50 | 51 | Definition 2.25 | 47 | tuple written $(\Phi,P^{-1}(V),(K,C\triangleleft F,E\triangleleft F))$; fibre map "a bounded linear isomorphism" |
| Definition 2.51 | 52 | Definition 2.26 | 47 |  |
| Definition 2.52 | 53 | Definition 2.27 | 48 |  |
| Definition 2.53 | 53 | Definition 2.28 | 48 |  |
| Proposition 2.54 | 53 | Proposition 2.16 | 48 |  |
| Theorem 2.55 | 56 | Theorem 2.5 | 51 |  |
| Lemma 2.56 | 56 | Lemma 2.7 | 51 |  |
| Proposition 2.57 | 56 | Proposition 2.17 | 51 | "regular" becomes "regular Hausdorff" |

### Chapter 3 (preprint pp. 61–146; arXiv 1707.08941 pp. 57–130)

| Preprint 2014 | p. | arXiv 1707.08941 | p. | Note |
|---|---|---|---|---|
| Definition 3.1 | 62 | Definition 3.1 | 57 |  |
| Definition 3.2 | 62 | Definition 3.2 | 58 |  |
| Definition 3.3 | 63 | Definition 3.3 | 59 |  |
| Definition 3.4 | 64 | Definition 3.4 | 59 | "tame" dropped |
| Proposition 3.5 | 65 | Proposition 3.1 | 60 |  |
| Definition 3.6 | 66 | Definition 3.5 | 61 | "tame" dropped |
| Definition 3.7 | 66 | Definition 3.6 | 61 |  |
| Remark 3.8 | 67 | Remark 3.1 | 62 |  |
| Lemma 3.9 | 67 | Lemma 3.1 | 62 |  |
| Proposition 3.10 | 68 | Proposition 3.2 | 62 |  |
| Definition 3.11 | 69 | Definition 3.7 | 63 | "tame" dropped |
| Theorem 3.12 | 70 | Theorem 3.1 | 64 | "tame" dropped |
| Corollary 3.13 | 70 | Corollary 3.1 | 65 | "tame" dropped |
| Definition 3.14 | 70 | Definition 3.8 | 65 | "tame" dropped |
| Theorem 3.15 | 71 | Theorem 3.2 | 65 | "tame" dropped |
| Lemma 3.16 | 72 | Lemma 3.2 | 66 |  |
| Lemma 3.17 | 72 | Lemma 3.3 | 66 |  |
| Theorem 3.18 | 74 | Theorem 3.3 | 67 | "tame" dropped |
| Theorem 3.19 | 74 | Theorem 3.4 | 68 |  |
| Remark 3.20 | 75 | Remark 3.5 | 68 |  |
| Definition 3.21 | 76 | Definition 3.9 | 69 |  |
| Proposition 3.22 | 77 | Proposition 3.3 | 69 | restated in Appendix 3.8.1 without a number |
| Theorem 3.23 | 77 | Theorem 3.5 | 70 |  |
| Corollary 3.24 | 78 | Corollary 3.2 | 71 |  |
| Definition 3.25 | 79 | Definition 3.10 | 71 |  |
| Proposition 3.26 | 80 | Proposition 3.4 | 72 |  |
| Theorem 3.27 | 81 | Theorem 3.6 | 73 |  |
| Definition 3.28 | 85 | Definition 3.11 | 76 |  |
| Theorem 3.29 | 86 | Theorem 3.7 | 77 |  |
| Theorem 3.30 | 86 | Theorem 3.8 | 77 |  |
| Lemma 3.31 | 86 | Lemma 3.4 | 77 |  |
| Lemma 3.32 | 87 | Lemma 3.5 | 78 |  |
| Theorem 3.33 | 88 | Theorem 3.9 | 79 |  |
| Corollary 3.34 | 88 | Corollary 3.3 | 79 |  |
| Theorem 3.35 | 89 | absent | — | the closing paragraph of §3.3 and this theorem (quoted from [21], Theorem 2.7) are dropped; the proof of Theorem 3.9 (= 3.33) is followed directly by Remark 3.6 (= 3.36) |
| Remark 3.36 | 89 | Remark 3.6 | 79 |  |
| Definition 3.37 | 90 | Definition 3.12 | 80 |  |
| Theorem 3.38 | 90 | Theorem 3.10 | 80 |  |
| Corollary 3.39 | 93 | Corollary 3.4 | 83 |  |
| Theorem 3.40 | 94 | Theorem 3.11 | 84 |  |
| Corollary 3.41 | 98 | Corollary 3.5 | 87 |  |
| Lemma 3.42 | 101 | Lemma 3.6 | 90 |  |
| Theorem 3.43 | 102 | Theorem 3.12 | 90 |  |
| Lemma 3.44 | 103 | Lemma 3.7 | 91 |  |
| Lemma 3.45 | 104 | Lemma 3.8 | 92 |  |
| Lemma 3.46 | 104 | Lemma 3.9 | 93 | restated in Appendix 3.8.2 as Lemma 3.22 (p. 114) |
| Corollary 3.47 | 106 | Corollary 3.6 | 95 |  |
| Definition 3.48 | 109 | Definition 3.13 | 97 | only "tame" dropped; condition (3) still at $0$ only |
| Remark 3.49 | 109 | Remark 3.8 | 97 |  |
| Definition 3.50 | 110 | Definition 3.14 | 98 | "tame" dropped |
| Definition 3.51 | 110 | Definition 3.15 | 98 | "tame" dropped |
| Proposition 3.52 | 110 | Proposition 3.5 | 98 | restated ("Let $x\in X$ be a solution …"); "tame" dropped |
| Definition 3.53 | 111 | Definition 3.16 | 98 |  |
| Theorem 3.54 | 111 | Theorem 3.13 | 99 | proof: "Property (4) follows from Corollary 3.5" |
| Lemma 3.55 | 114 | Lemma 3.10 | 101 | restated in Appendix 3.8.3 as Lemma 3.23 (p. 117) |
| Theorem 3.56 | 115 | Theorem 3.14 | 102 | retitled "Global implicit function theorem I"; "tame" dropped |
| Theorem 3.57 | 115 | Theorem 3.15 | 102 | retitled "Global implicit function theorem II"; "tame" moved to the M-polyfold |
| Theorem 3.58 | 116 | Theorem 3.16 | 103 |  |
| Lemma 3.59 | 117 | Lemma 3.11 | 104 |  |
| Lemma 3.60 | 118 | Lemma 3.12 | 104 |  |
| Lemma 3.61 | 118 | Lemma 3.13 | 105 |  |
| Lemma 3.62 | 121 | Lemma 3.14 | 107 |  |
| Lemma 3.63 | 121 | Lemma 3.15 | 107 |  |
| Lemma 3.64 | 122 | Lemma 3.16 | 108 |  |
| Lemma 3.65 | 123 | Lemma 3.17 | 109 |  |
| Lemma 3.66 | 123 | Lemma 3.18 | 109 |  |
| Lemma 3.67 | 124 | Lemma 3.19 | 110 |  |
| Lemma 3.68 | 125 | Lemma 3.20 | 110 |  |
| Proposition 3.69 | 126 | Proposition 3.6 | 112 |  |
| Lemma 3.70 | 127 | Lemma 3.21 | 113 |  |
| Definition 3.71 | 135 | Definition 3.17 | 120 |  |
| Theorem 3.72 | 136 | Theorem 3.17 | 121 |  |
| Proposition 3.73 | 137 | Proposition 3.7 | 121 |  |
| Lemma 3.74 | 137 | Lemma 3.24 | 121 |  |
| Corollary 3.75 | 139 | Corollary 3.7 | 122 |  |
| Lemma 3.76 | 139 | Lemma 3.25 | 123 |  |
| Lemma 3.77 | 140 | Lemma 3.26 | 124 |  |
| Theorem 3.78 | 141 | Theorem 3.18 | 125 |  |
| Lemma 3.79 | 142 | Lemma 3.27 | 125 |  |
| Lemma 3.80 | 143 | Lemma 3.28 | 126 |  |
| Lemma 3.81 | 144 | Lemma 3.29 | 127 |  |
| Lemma 3.82 | 144 | Lemma 3.30 | 128 |  |

### Chapter 4 (preprint pp. 147–168; arXiv 1707.08941 pp. 131–150)

| Preprint 2014 | p. | arXiv 1707.08941 | p. | Note |
|---|---|---|---|---|
| Definition 4.1 | 147 | Definition 4.1 | 131 |  |
| Theorem 4.2 | 147 | Theorem 4.1 | 132 |  |
| Remark 4.3 | 148 | Remark 4.1 | 132 |  |
| Definition 4.4 | 148 | Definition 4.2 | 132 |  |
| Lemma 4.5 | 148 | Lemma 4.1 | 132 |  |
| Definition 4.6 | 148 | Definition 4.3 | 133 |  |
| Lemma 4.7 | 149 | Lemma 4.2 | 133 |  |
| Proposition 4.8 | 149 | Proposition 4.1 | 133 |  |
| Proposition 4.9 | 150 | Proposition 4.2 | 134 |  |
| Lemma 4.10 | 151 | Lemma 4.3 | 134 |  |
| Lemma 4.11 | 154 | Lemma 4.4 | 137 |  |
| Lemma 4.12 | 154 | Lemma 4.5 | 138 |  |
| Definition 4.13 | 157 | Definition 4.4 | 139 |  |
| Remark 4.14 | 157 | Remark 4.3 | 140 |  |
| Proposition 4.15 | 158 | Proposition 4.3 | 140 |  |
| Definition 4.16 | 159 | Definition 4.5 | 141 |  |
| Definition 4.17 | 159 | Definition 4.6 | 142 |  |
| Theorem 4.18 | 159 | Theorem 4.2 | 142 |  |
| Lemma 4.19 | 160 | Lemma 4.6 | 142 |  |
| Remark 4.20 | 161 | Remark 4.4 | 143 |  |
| Definition 4.21 | 161 | Definition 4.7 | 143 |  |
| Theorem 4.22 | 162 | Theorem 4.3 | 144 |  |
| Theorem 4.23 | 165 | Theorem 4.4 | 147 |  |
| Remark 4.24 | 165 | Remark 4.5 | 147 |  |
| Definition 4.25 | 167 | Definition 4.9 | 149 |  |
| Proposition 4.26 | 167 | Proposition 4.5 | 149 |  |
| Definition 4.27 | 168 | Definition 4.10 | 150 |  |
| Theorem 4.28 | 168 | Theorem 4.5 | 150 |  |

### Chapter 5 (preprint pp. 169–199; arXiv 1707.08941 pp. 151–180)

| Preprint 2014 | p. | arXiv 1707.08941 | p. | Note |
|---|---|---|---|---|
| Definition 5.1 | 169 | Definition 5.1 | 151 |  |
| Lemma 5.2 | 169 | Lemma 5.1 | 152 |  |
| Proposition 5.3 | 171 | Proposition 5.1 | 153 |  |
| Definition 5.4 | 171 | Definition 5.5 | 155 |  |
| Theorem 5.5 | 172 | Theorem 5.1 | 155 | proof moved from Appendix 5.4.1 into §5.2 |
| Theorem 5.6 | 172 | Theorem 5.2 | 158 |  |
| Theorem 5.7 | 172 | Theorem 5.3 | 158 |  |
| Corollary 5.8 | 173 | Corollary 5.1 | 158 |  |
| Definition 5.9 | 173 | Definition 5.7 | 161 |  |
| Proposition 5.10 | 173 | Proposition 5.4 | 161 |  |
| Lemma 5.11 | 173 | Lemma 5.3 | 161 |  |
| Remark 5.12 | 174 | Remark 5.3 | 162 |  |
| Theorem 5.13 | 174 | Theorem 5.5 | 162 |  |
| Remark 5.14 | 175 | Remark 5.4 | 163 |  |
| Definition 5.15 | 175 | Definition 5.8 | 163 |  |
| Remark 5.16 | 176 | Remark 5.5 | 164 |  |
| Definition 5.17 | 177 | Definition 5.9 | 164 |  |
| Theorem 5.18 | 177 | Theorem 5.6 | 164 | retitled "Perturbation: general position" |
| Theorem 5.19 | 180 | Theorem 5.7 | 167 |  |
| Definition 5.20 | 180 | Definition 5.10 | 167 |  |
| Remark 5.21 | 181 | Remark 5.7 | 167 |  |
| Theorem 5.22 | 181 | Theorem 5.8 | 167 |  |
| Lemma 5.23 | 182 | Lemma 5.4 | 169 |  |
| Lemma 5.24 | 182 | Lemma 5.5 | 169 |  |
| Theorem 5.25 | 186 | absent | — | dropped with Lemma 5.26 and Theorem 5.27; §5.3 ends with the proof of Theorem 5.8 (= 5.22), p. 172, and the new §5.4 follows |
| Lemma 5.26 | 187 | absent | — | see Theorem 5.25; only its claim survives, as the sentence "Clearly general position implies good position" before Remark 5.6, p. 166 |
| Theorem 5.27 | 188 | absent | — | see Theorem 5.25 |
| Definition 5.28 | 192 | Definition 5.12 | 173 |  |
| Definition 5.29 | 192 | Definition 5.13 | 174 |  |
| Proposition 5.30 | 193 | Proposition 5.5 | 174 |  |
| Definition 5.31 | 193 | Definition 5.14 | 174 |  |
| Theorem 5.32 | 193 | Theorem 5.10 | 174 |  |
| Definition 5.33 | 194 | Definition 5.15 | 175 |  |
| Theorem 5.34 | 194 | Theorem 5.11 | 175 |  |
| Proposition 5.35 | 194 | Proposition 5.6 | 175 |  |
| Definition 5.36 | 195 | Definition 5.16 | 176 |  |
| Theorem 5.37 | 195 | Theorem 5.12 | 176 |  |
| Proposition 5.38 | 197 | Proposition 5.7 | 178 |  |
| Definition 5.39 | 198 | Definition 5.17 | 178 |  |
| Theorem 5.40 | 198 | Theorem 5.13 | 178 |  |
| Definition 5.41 | 198 | Definition 5.18 | 179 |  |
| Proposition 5.42 | 198 | Proposition 5.8 | 179 |  |
| Theorem 5.43 | 198 | Theorem 5.14 | 179 |  |
| Corollary 5.44 | 199 | Corollary 5.2 | 179 |  |

### Chapter 6 (preprint pp. 200–237; arXiv 1707.08941 pp. 181–221)

| Preprint 2014 | p. | arXiv 1707.08941 | p. | Note |
|---|---|---|---|---|
| §6.1 Linearizations of Sc-Fredholm Sections | 200 | §6.1 (same title) | 181 |  |
| Definition 6.1 | 201 | Definition 6.1 | 182 | the paragraph before it now compares $(f-s)'(x)$ with $(f-t)'(x)$ |
| Proposition 6.2 | 201 | Proposition 6.1 | 183 | followed by the new Remark 6.1 |
| §6.2 Linear Algebra and Conventions | 203 | §6.2 (same title) | 184 |  |
| Definition 6.3 | 204 | Definition 6.2 | 185 |  |
| Proposition 6.4 | 205 | Proposition 6.2 | 185 |  |
| Lemma 6.5 | 206 | Lemma 6.1 | 187 | adds "Hence $\Phi_E$ is a natural isomorphism"; followed by the new Lemma 6.2; proof in §6.7.1 |
| Proposition 6.6 | 207 | Proposition 6.3 | 188 | the names of the two blocks in $c$ unchanged |
| §6.3 The Determinant of a Fredholm Operator | 207 | §6.3 (same title) | 189 |  |
| Definition 6.7 | 208 | Definition 6.3 | 189 |  |
| Definition 6.8 | 208 | Definition 6.4 | 189 |  |
| Definition 6.9 | 208 | Definition 6.5 | 189 |  |
| Lemma 6.10 | 208 | absent | — | dropped; p. 190 remarks that a common lower bound need not exist in general, and Lemmas 6.3–6.5, Definition 6.6 and Proposition 6.6 (pp. 189–195) compare two projections with the same range instead (see "Dropped") |
| Lemma 6.11 | 209 | Proposition 6.4 | 192 | now a proposition |
| Proposition 6.12 | 211 | Proposition 6.5 | 193 | proof in §6.7.2 |
| Corollary 6.13 | 211 | Corollary 6.1 | 193 |  |
| Lemma 6.14 | 212 | Lemma 6.6 | 199 | "$j(e) = (0, e)$" in the proof unchanged |
| Proposition 6.15 | 213 | Proposition 6.7 | 199 | formula (94) is (6.10) |
| Definition 6.16 | 214 | Definition 6.7 | 200 |  |
| §6.4 Classical Local Determinant Bundles | 214 | §6.4 (same title) | 200 |  |
| Lemma 6.17 | 214 | Lemma 6.7 | 201 |  |
| Lemma 6.18 | 215 | Lemma 6.8 | 201 |  |
| Lemma 6.19 | 216 | Lemma 6.9 | 202 |  |
| Proposition 6.20 | 216 | Proposition 6.8 | 202 | opens with "Let $T : E \to F$ be a Fredholm operator and $P \in \Pi_T$" |
| Lemma 6.21 | 216 | Lemma 6.10 | 202 |  |
| Definition 6.22 | 218 | Definition 6.8 | 204 |  |
| Proposition 6.23 | 218 | Proposition 6.9 | 204 |  |
| Proposition 6.24 | 218 | Proposition 6.10 | 204 |  |
| Lemma 6.25 | 218 | Lemma 6.11 | 204 | no proof of its own (the text refers to Propositions 6.5 and 6.6); the preprint's proof through a common lower bound is dropped |
| §6.5 Local Orientation Propagation and Orientability | 219 | §6.5 Local Orientation Propagation | 204 |  |
| Proposition 6.26 | 219 | Proposition 6.11 | 205 |  |
| Definition 6.27 | 219 | Definition 6.9 | 205 |  |
| Proposition 6.28 | 220 | Proposition 6.12 | 205 | two neighbourhoods $U' \subset U$; (1): "$U'\subset U$ is sc-smoothly contractible in $U$ to the point $x$" |
| Lemma 6.29 | 222 | Lemma 6.12 | 207 |  |
| Lemma 6.30 | 222 | Lemma 6.13 | 207 |  |
| Lemma 6.31 | 223 | Lemma 6.14 | 209 | the sequence (96) is (6.12) |
| Proposition 6.32 | 224 | Proposition 6.13 | 209 | "over the tame $X$"; the path in $U'$ |
| Lemma 6.33 | 224 | Lemma 6.15 | 209 |  |
| Lemma 6.34 | 226 | Lemma 6.16 | 211 |  |
| Theorem 6.35 | 227 | Theorem 6.1 | 212 | "an open sc-smoothly contractible neighborhood" becomes "an open neighborhood $\widetilde U(x)$"; $f$ still not introduced |
| Definition 6.36 | 227 | Definition 6.10 | 212 | "open contractible" becomes "open path connected" |
| Theorem 6.37 | 228 | Theorem 6.2 | 213 | (∗) asked on an orientable open neighbourhood |
| Definition 6.38 | 229 | Definition 6.11 | 213 |  |
| Definition 6.39 | 229 | Definition 6.12 | 213 | "$y \in U_\infty$" corrected to "$y \in X_\infty$" |
| Definition 6.40 | 229 | Definition 6.13 | 214 |  |
| Theorem 6.41 | 229 | Theorem 6.3 | 214 |  |
| Remark 6.42 | 230 | Remark 6.4 | 214 |  |
| §6.6 Invariants Associated to Proper Sc-Fredholm Sections | 230 | §6.6 Invariants | 215 |  |
| Theorem 6.43 | 231 | Theorem 6.4 | 215 | the case $\partial X = \emptyset$: preprint p. 233, 2017 p. 217 |
| §6.7 Appendix | 234 | §6.7 Appendix | 218 |  |
| §6.7.1 Proof of Lemma 6.5 | 234 | §6.7.1 Proof of Lemma 6.1 | 218 | wording unchanged ("$\det(\tau)$", "$\beta(C)$") |
| §6.7.2 Proof of Proposition 6.12 | 235 | §6.7.2 Proof of Proposition 6.5 | 219 | runs to p. 221, the end of the 2017 chapter (p. 222 blank, Part II from p. 223); "$\alpha_q$" unchanged |

## Numbered items of the 2017 text without a preprint number (Chapters 1–6)

| arXiv 1707.08941 | p. | Origin |
|---|---|---|
| Remark 1.1 | 8 | unnumbered paragraph of the preprint, p. 11 (continuity of $x\mapsto Df(x)$) |
| Remark 1.3 | 8 | new (the stronger notion "ssc") |
| Remark 2.1 | 19 | new (generalizations of the local models) |
| Remark 2.3 | 31 | new (tameness makes the partial cones partial quadrants) |
| Definition 2.18 | 36 | new (sc-smooth splicing) |
| Lemma 2.5 | 36 | new (a splicing gives a tame retraction) |
| Remark 2.4 | 38 | unnumbered paragraph of the preprint, p. 42 |
| Proposition 2.11 | 39 | new (local faces at a corner of a tame retract) |
| Remark 3.2 | 64 | new (on the definition of an sc-Fredholm germ) |
| Remark 3.3 | 65 | unnumbered sentence of the preprint, p. 70 |
| Remark 3.4 | 65 | unnumbered paragraph of the preprint, p. 71 |
| Remark 3.7 | 84 | unnumbered paragraph of the preprint, p. 95 |
| Remark 3.9 | 99 | new (good position at interior points needs no tameness) |
| Lemma 3.22 | 114 | restatement of Lemma 3.9 (= 3.46) in Appendix 3.8.2 |
| Lemma 3.23 | 117 | restatement of Lemma 3.10 (= 3.55) in Appendix 3.8.3 |
| Remark 4.2 | 134 | unnumbered paragraph of the preprint, p. 150 |
| Definition 4.8 | 146 | new (M⁺-polyfold structure) |
| Proposition 4.4 | 146 | new (properties of M⁺-polyfolds) |
| Definition 5.2 | 153 | new (reflexive $(0,1)$-fibres) |
| Lemma 5.2 | 153 | new |
| Definition 5.3 | 154 | new (mixed convergence) |
| Definition 5.4 | 154 | new (reflexive auxiliary norm) |
| Proposition 5.2 | 154 | new (existence of reflexive auxiliary norms) |
| Definition 5.6 | 159 | new (reflexive local compactness property) |
| Proposition 5.3 | 159 | new |
| Theorem 5.4 | 159 | new (compactness controlled near the boundary) |
| Remark 5.1 | 160 | new |
| Remark 5.2 | 161 | new |
| Remark 5.6 | 166 | new (algebraic structure in SFT) |
| Definition 5.11 | 173 | new (sc⁺-section over $\partial X$) |
| Theorem 5.9 | 173 | new (∂-extension theorem, sketch of proof) |
| Remark 6.1 | 183 | new (the tameness hypothesis of Proposition 6.1 is probably not needed) |
| Lemma 6.2 | 188 | new (naturality of $\Phi_E$ under isomorphisms of exact sequences) |
| Lemma 6.3 | 189 | new (for $T$ near $T_0$ and a projection $P$ near $P_0 \in \Pi_{T_0}$: $T$ Fredholm, $P \in \Pi_T$, same index) |
| Remark 6.2 | 190 | new (consequences of Lemma 6.3 for the lines $\det(PT)$) |
| Remark 6.3 | 190 | new (orthogonal good left-projections in Hilbert spaces) |
| Lemma 6.4 | 191 | new ($LP \le P$ and $LQ \le Q$ for a projection $L$ onto $R(P) \cap R(Q)$) |
| Definition 6.6 | 191 | new (the projections $\mathcal P_H$ onto a closed subspace $H$ of finite codimension) |
| Lemma 6.5 | 191 | new ($Q = P + Q(I - P)$ for $P, Q \in \mathcal P_H$) |
| Proposition 6.6 | 195 | new (isomorphisms between $E(T,P)$ and $E(T,Q)$ for $P, Q \in \Pi_T \cap \mathcal P_H$, continuous in $T$) |

## Part II: the 2017 numbering is the only numbering (Chapters 7–8)

Part II, *Ep-Groupoids* (Chapters 7–11), has no 2014 preprint: the preprint arXiv 1407.3185 is
Part I alone. For Part II the book's arXiv version 1707.08941 is the text, and **its statement
numbers and printed pages are the only numbering of Part II** used in the project: in
`Findings.md` ("## Chapter 7", "## Chapter 8"), `Chapter7.md`, `Chapter8.md`, the reports
(`verification/ch07.md`, V7.1–V7.68; `verification/ch08.md`, V8.1–V8.43) and the Lean docstrings.
There is nothing to concord, so this section has no preprint column; it lists the numbered items
and sections of Chapters 7 and 8 with their pages, their V-items and the Lean files of
`Polyfold/Chapter7/` and `Polyfold/Chapter8/` that formalize them, so that a reader holding the
book can find each of them. Part I results cited in Part II carry their 2017 numbers, with the preprint number of the
Lean name in brackets where it matters (for example Theorem 2.2 [2.16], `Polyfold.theorem_2_3_10`).

Pages are printed pages, read off the running heads of `sources/HWZ-Book-2017.txt` (even pages
"226 7 Ep-Groupoids", odd pages "7.1 … 227"; p. 225, the first page of the chapter, has no head),
as for Chapter 6; Chapter 7 is lines 10704–12250 of that text (Part II opens at line 10687, p. 223).
Each kind of statement has its own counter (Definition 7.3 and Proposition 7.3 are different
statements). Chapter 7 has 52 numbered items: 17 definitions, 14 propositions, 10 lemmas, 6
theorems, 3 corollaries and 2 remarks. "p." is the page of the statement's heading (for a section,
of its title). The Lean files are in `Polyfold/Chapter7/` (for Chapter 8, in `Polyfold/Chapter8/`);
the first one named holds the statement, the others the notions or witnesses it uses. The verdicts
are in the comparison, not here.

### Chapter 7 (arXiv 1707.08941 pp. 225–256)

| arXiv 1707.08941 | p. | V-item | Lean file | Note |
|---|---|---|---|---|
| §7.1 Ep-Groupoids and Basic Properties | 225 | — | — |  |
| Definition 7.1 | 225 | V7.1 | `Groupoid.lean` | groupoid, `mor(x, y)`, orbit space $\lvert X\rvert$, $\pi$ (pp. 225–226) |
| Definition 7.2 | 226 | V7.2 | `Groupoid.lean` | isotropy group $G_x$ |
| Definition 7.3 | 226 | V7.3 | `EpGroupoid.lean` | ep-groupoid (pp. 226–227); (4) cites "Lemma 2.8 in [38]", in the book Part I's Proposition 2.15 |
| Definition 7.4 | 227 | V7.5 | `EpGroupoid.lean`, `LocalDiffeo.lean` | $\hat\varphi$; $T\varphi$ only defined (point G.70) |
| Definition 7.5 | 228 | V7.7 | `EpGroupoid.lean` | induced degeneracy index; the levels before it: V7.6 |
| Definition 7.6 | 228 | V7.8 | `EpGroupoid.lean`, `LocalDiffeo.lean` | tame ep-groupoid, with the tameness of the morphism M-polyfold |
| Definition 7.7 | 228 | V7.9 | `EpGroupoid.lean`, `Groupoid.lean` | the category $\mathcal{EP}$; the remark after it (pp. 228–229): V7.10, `Basic.lean`, `NonVacuity.lean` |
| Proposition 7.1 | 229 | V7.11 | `Basic.lean` | openness of $\pi$ |
| Proposition 7.2 | 229 | V7.12 | `Basic.lean` | countable neighbourhood bases |
| Proposition 7.3 | 229 | V7.13 | `Basic.lean` | local closure relation; proof ends on p. 230 |
| Lemma 7.1 | 230 | V7.14 | `Basic.lean`, `ProperMaps.lean` |  |
| Proposition 7.4 | 230 | V7.15 | `Basic.lean` | finiteness of $G_x$; the conjugation after it: V7.16 |
| Theorem 7.1 | 231 | V7.17 | `NaturalRep.lean`, `EpGroupoid.lean` | natural representation; proved in Appendix 7.5.1 as Theorem 7.5 |
| Proposition 7.5 | 233 | V7.25 | `NaturalRepFinite.lean` | finite sets of isomorphic objects; proof pp. 234–236 |
| Definition 7.8 | 236 | V7.26 | `NaturalRepFinite.lean`, `EpGroupoid.lean` |  |
| Proposition 7.6 | 236 | V7.27 | `Uniformizer.lean` | $G_x\backslash U(x) \cong \pi(U(x))$; proof ends on p. 237 |
| Definition 7.9 | 237 | V7.28 | `Uniformizer.lean`, `EpGroupoid.lean` | local uniformizer |
| Definition 7.10 | 237 | V7.29 | `SubGroupoid.lean`, `EpGroupoid.lean` | ep-subgroupoid |
| Proposition 7.7 | 238 | V7.32 | `SubGroupoid.lean` | proof ends on p. 239 |
| §7.2 Effective and Reduced Ep-Groupoids | 239 | — | — |  |
| Definition 7.11 | 239 | V7.33 | `Effective.lean`, `EpGroupoid.lean` | effective; regular objects |
| Lemma 7.2 | 239 | V7.34 | `Effective.lean` | $X_{reg}$ open |
| Lemma 7.3 | 239 | V7.35 | `Effective.lean` | proof p. 240 |
| Proposition 7.8 | 240 | V7.36 | `Effective.lean` | $X_{reg}$ open and dense |
| Definition 7.12 | 241 | V7.38 | `Reduced.lean`, `EpGroupoid.lean` | $\mathbf X^T$, $\mathbf X^R$; the subgroup $T_x$ before it: V7.37, `Effective.lean` |
| Proposition 7.9 | 242 | V7.39 | `Reduced.lean` | $\mathbf X^R$ Hausdorff and paracompact taken as hypotheses (point G.71) |
| Proposition 7.10 | 244 | V7.40 | `Reduced.lean` | the reduced ep-groupoid $X_R$ (p. 243); hypotheses as Proposition 7.9 |
| Definition 7.13 | 244 | V7.41 | `Reduced.lean`, `Effective.lean` | $G_x^{\mathrm{eff}} = G_x/T_x$ |
| §7.3 Topological Properties of Ep-Groupoids | 244 | — | — |  |
| Theorem 7.2 | 244 | V7.42 | `OrbitTopology.lean` | $\lvert X\rvert$ locally metrizable, regular, Hausdorff |
| Lemma 7.4 | 244 | V7.43 | `OrbitTopology.lean` | proof p. 245 |
| Lemma 7.5 | 245 | V7.44 | `OrbitTopology.lean` |  |
| Lemma 7.6 | 245 | V7.45 | `OrbitTopology.lean` | proof ends on p. 246 |
| Lemma 7.7 | 246 | V7.46 | `OrbitTopology.lean` |  |
| Corollary 7.1 | 247 | V7.47 | `OrbitTopology.lean` | subsets of $\lvert X\rvert$ (p. 247): V7.48 |
| Definition 7.14 | 247 | V7.49 | `EpGroupoid.lean` | component compact |
| Corollary 7.2 | 247 | V7.51 | `OrbitTopology.lean`, `Michael.lean` |  |
| Proposition 7.11 | 247 | V7.52 | `Lift.lean`, `LocalDiffeo.lean` | index lifting; proof p. 248 |
| §7.4 Paracompact Orbit Spaces | 249 | — | — |  |
| Definition 7.15 | 249 | V7.53 | `EpGroupoid.lean`, `Lift.lean` | with the sentence before Remark 7.1; the open question there is not formalized |
| Remark 7.1 | 249 | V7.53 | — | no formal content |
| Proposition 7.12 | 249 | V7.54 | `Lift.lean` | proof ends on p. 250 |
| Theorem 7.3 | 250 | V7.55 | `PartitionsOfUnity.lean` | continuous partitions of unity |
| Definition 7.16 | 250 | V7.56 | `EpGroupoid.lean` | sc-smooth partitions of unity (pp. 250–251) |
| Remark 7.2 | 251 | V7.57 | — | no formal content |
| Theorem 7.4 | 251 | V7.58 | `PartitionsOfUnity.lean` | proved in Appendix 7.5.2 as Theorem 7.6; the proof: V7.67 |
| Definition 7.17 | 251 | V7.59 | `EpGroupoid.lean`, `ProperSubsets.lean` | proper subsets, the properness property |
| Proposition 7.13 | 251 | V7.60 | `ProperSubsets.lean` |  |
| Proposition 7.14 | 251 | V7.61 | `ProperSubsets.lean` | proof p. 252 |
| §7.5 Appendix | 253 | — | — |  |
| §7.5.1 The Natural Representation | 253 | — | — |  |
| Theorem 7.5 | 253 | V7.62 | `NaturalRep.lean` | restates Theorem 7.1; proof pp. 253–254 |
| Lemma 7.8 | 253 | V7.63 | `NaturalRep.lean` | proof p. 254 |
| Lemma 7.9 | 254 | V7.64 | `NaturalRep.lean` | proof on p. 254; Theorem 7.5 is proved by p. 254 |
| §7.5.2 Sc-Smooth Partitions of Unity | 254 | — | — |  |
| Theorem 7.6 | 255 | V7.65 | `PartitionsOfUnity.lean` | restates Theorem 7.4 |
| Lemma 7.10 | 255 | V7.66 | `PartitionsOfUnity.lean` | the proof of Theorem 7.4 follows, pp. 255–256 (V7.67) |
| Corollary 7.3 | 256 | V7.68 | `PartitionsOfUnity.lean` | the last page of the chapter |

**Unnumbered claims of Chapter 7 with a V-item of their own.**

| Claim | pp. | V-item | Lean file |
|---|---|---|---|
| properness of Definition 7.3 (3) and its sequential form, used in the proofs | 227–254 | V7.4 | `ProperMaps.lean` |
| levels and degeneracy index of $s$, $t$; the filtration of $\lvert X\rvert$ | 227–228 | V7.6 | `EpGroupoid.lean`, `LocalDiffeo.lean` |
| the remark after Definition 7.7 (sc-smoothness on objects suffices) | 228–229 | V7.10 | `Basic.lean`, `NonVacuity.lean` |
| the conjugation $G_x \to G_y$ | 230 | V7.16 | `Groupoid.lean`, `Basic.lean` |
| local path connectedness of M-polyfolds (used, not stated) | 231 | V7.18 | `LocConnected.lean` |
| the splitting $\mathbf U(x) = \bigsqcup_g \mathbf U(g)$ | 231 | V7.19 | `NaturalAction.lean`, `NaturalRep.lean` |
| the M-polyfold $G \times U$ | 232 | V7.20 | `Discrete.lean`, `NaturalAction.lean` |
| the translation groupoid $G_x \ltimes U(x)$ | 232 | V7.21 | `NaturalAction.lean`, `Groupoid.lean` |
| the functor $\Gamma$, fully faithful | 232 | V7.22 | `NaturalAction.lean` |
| the map $\hat\Phi$ on morphisms | 232–233 | V7.23 | `NaturalAction.lean` |
| uniqueness and restriction of natural representations (used, not stated) | 239–241 | V7.24 | `NaturalAction.lean`, `NaturalRep.lean` |
| the facts (1)–(4) on a sub-M-polyfold $A$ | 237–238 | V7.30 | `SubGroupoid.lean` |
| the morphisms $\mathbf A$ form a sub-M-polyfold | 238 | V7.31 | `SubGroupoid.lean` |
| the subgroup $T_x$ of elements acting trivially | 241 | V7.37 | `Effective.lean` |
| subsets of $\lvert X\rvert$ are locally metrizable, regular, Hausdorff | 247 | V7.48 | `OrbitTopology.lean` |
| Part I's Lemma 2.7 and Proposition 2.17 (Michael), used for Corollary 7.2 | 247, 249 | V7.50 | `Michael.lean` |
| the proof of Theorem 7.4 | 255–256 | V7.67 | `PartitionsOfUnity.lean` |

The sentence before Remark 7.1 is part of V7.53, the reduced ep-groupoid $X_R$ (p. 243) of V7.40
and the isotropy $G_x/T_x$ (p. 244) of V7.41. The witnesses that show the hypotheses can hold
(`NonVacuity.lean`, `ReducedNotHausdorff.lean` and the witnesses in the other files; `Findings.md`,
Chapter 7, items 100–107) have no V-item of their own. Points of Chapter 7: G.70 (Definition
7.4, $T\varphi$ as an sc-isomorphism), G.71 (Propositions 7.9–7.10, $\mathbf X^R$ Hausdorff and
paracompact; Hausdorffness fails in general, `ReducedNotHausdorff.lean`), G.72 (p. 228, $\lvert
X_\infty\rvert = \bigcap_k \lvert X_k\rvert$), G.73 (p. 227, $X_\infty$ dense in every $X_k$). `verification/ch07.md` contains no
*(book?)* mark: there is no other numbering to check against.

### Chapter 8 (arXiv 1707.08941 pp. 257–289)

Chapter 8, *Bundles and Covering Functors*, is lines 12251–13855 of `sources/HWZ-Book-2017.txt`
(Chapter 9 opens at line 13856, p. 291; p. 290 is blank). The running heads are "258 8 Bundles and
Covering Functors" on even pages and "8.1 The Tangent of an Ep-Groupoid 259" on odd pages; p. 257,
the first page of the chapter, has no head. Chapter 8 has 33 numbered items: 10 definitions, 11
lemmas, 6 theorems, 4 propositions and 2 remarks; it has no corollaries or examples. Its sections are
§§8.1–8.5, with §8.5.1 and §8.5.2 in the appendix (there is no §8.6). Definitions 8.2 and 8.3 are not
formalized and have no V-item.

| arXiv 1707.08941 | p. | V-item | Lean file | Note |
|---|---|---|---|---|
| §8.1 The Tangent of an Ep-Groupoid | 257 | — | — | the tangent data (8.1)–(8.9) (pp. 257–258): V8.1, `Basic.lean` |
| Theorem 8.1 | 258 | V8.3 | `TangentEp.lean`, `TangentTame.lean` | the tangent ep-groupoid; proved on pp. 263–264 from Lemmas 8.1–8.8 |
| Lemma 8.1 | 259 | V8.4 | `TangentEp.lean`, `TangentLocal.lean` | in the sheet form of its proof; as printed not formalized (point G.75) |
| Lemma 8.2 | 259 | V8.5 | `TangentEp.lean` | proof p. 260 |
| Lemma 8.3 | 260 | V8.6 | `TangentEp.lean` | associativity; proof p. 261 |
| Lemma 8.4 | 261 | V8.7 | `TangentEp.lean` | units |
| Lemma 8.5 | 261 | V8.8 | `TangentEp.lean` | inverses; proof ends on p. 262 |
| Lemma 8.6 | 262 | V8.9 | `TangentEp.lean`, `TangentLocal.lean` | "$m_{T\mathbf X}$ is precisely $Tm$" not formalized (point G.75) |
| Lemma 8.7 | 262 | V8.10 | `TangentEp.lean` | properness; proof ends on p. 263 |
| Lemma 8.8 | 263 | V8.11 | `TangentTame.lean` | "$Tr$ is a tame retraction" proved from the definitions |
| Remark 8.1 | 264 | V8.12 | `TangentEp.lean` | pp. 264–265; the linearity of $T\varphi$ not formalized (points G.7, G.70) |
| Theorem 8.2 | 265 | V8.13 | `TangentEp.lean` | proof ends on p. 266 |
| Theorem 8.3 | 266 | V8.14 | `TangentEp.lean` | the functor $T$, formalized as `EP.{max u 1} ⥤ EP.{max u 1}` |
| Definition 8.1 | 266 | V8.15 | `Basic.lean`, `NatTrans.lean` | pp. 266–267; $\simeq$ an equivalence relation (p. 267): V8.16 |
| Proposition 8.1 | 267 | V8.17 | `TangentEp.lean` | proof ends on p. 268 |
| Theorem 8.4 | 268 | V8.18 | `TangentOrbit.lean` | proved by metrizability; $\lvert TX\rvert$ is metrizable |
| §8.2 Sc-Differential Forms on Ep-Groupoids | 268 | — | — |  |
| Definition 8.2 | 268 | — | — | sc-differential forms (pp. 268–269); not formalized (point G.74) |
| Definition 8.3 | 270 | — | — | the sc-de Rham complex; not formalized (point G.74) |
| §8.3 Strong Bundles over Ep-Groupoids | 270 | — | — | strong bundle maps and the pull-back along $s$ (p. 270): V8.19, `StrongBundleMap.lean` |
| Definition 8.4 | 271 | V8.20 | `EpStrongBundle.lean`, `StrongBundleMap.lean` | with global strong bundle maps (a reading); $\mu(\psi,\cdot)$ (p. 271): V8.21; the functorial picture (pp. 271–272): V8.22 |
| Definition 8.5 | 273 | V8.23 | `EpStrongBundle.lean`, `StrongBundleMap.lean` |  |
| Definition 8.6 | 274 | V8.24 | `EpStrongBundle.lean` | "these are identical notions" (pp. 273–274): V8.25 |
| Definition 8.7 | 274 | V8.26 | `EpStrongBundle.lean` | section functors (pp. 274–275) |
| §8.4 Proper Covering Functors | 275 | — | — |  |
| Definition 8.8 | 275 | V8.27 | `Basic.lean`, `ProperCovering.lean` | the degeneracy remark after it (pp. 275–276): V8.28 |
| Proposition 8.2 | 276 | V8.29 | `ProperCovering.lean` | proof ends on p. 277 |
| Theorem 8.5 | 277 | V8.30 | `ProperCoveringLocal.lean`, `NonVacuity.lean` | Proper Covering I; (5) with $s$ on both vertical arrows, as printed it does not hold as we read it; proof pp. 278–279 |
| Remark 8.2 | 277 | V8.31 | `ProperCoveringLocal.lean` | pp. 277–278, between Theorem 8.5 and its proof |
| Definition 8.9 | 279 | V8.32 | `Basic.lean` | $\mathrm{Diff}_{sc}$ (p. 279); pp. 279–280; the discussion after it (pp. 280–281): V8.33, `GeometricLift.lean` |
| Proposition 8.3 | 281 | V8.35 | `GeometricLift.lean`, `SigmaPolyfold.lean` | for nonempty $D$; disjoint unions (p. 281): V8.34; proof ends on p. 282 |
| Theorem 8.6 | 283 | V8.36 | `GeometricLift.lean`, `ProperCoveringLocal.lean` | Proper Covering II; for ep-groupoids in `Type`; proof ends on p. 284 |
| Definition 8.10 | 285 | V8.37 | `EpStrongBundle.lean` | the recap before it (pp. 284–285); (3) read as a pull-back along $\mathrm{pr}_2$ |
| §8.5 Appendix | 286 | — | — |  |
| §8.5.1 Local Structure of Proper Coverings | 286 | — | — | the preliminaries before Lemma 8.9 (p. 286): V8.38, `ProperCovering.lean` |
| Lemma 8.9 | 286 | V8.39 | `ProperCovering.lean` | proof ends on p. 287 |
| Lemma 8.10 | 287 | V8.40 | `ProperCovering.lean` | classes indexed by their images in $\lvert Y\rvert$ |
| Lemma 8.11 | 287 | V8.41 | `ProperCovering.lean` |  |
| Proposition 8.4 | 288 | V8.42 | `ProperCovering.lean` | $\mathbb N$ as the trivial ep-groupoid of a discrete M-polyfold |
| §8.5.2 The Structure of Strong Bundle Coverings | 288 | — | — | pp. 288–289: V8.43, `EpStrongBundle.lean` |

**Unnumbered claims of Chapter 8 with a V-item of their own.**

| Claim | pp. | V-item | Lean file |
|---|---|---|---|
| the tangent data (8.1)–(8.9): structure maps and the composition (8.5) | 257–258 | V8.1 | `Basic.lean`, `TangentEp.lean` |
| tangents of maps defined on open sets and of local sc-diffeomorphisms (used, not stated) | 258–263 | V8.2 | `TangentLocal.lean` |
| $\simeq$ is an equivalence relation | 267 | V8.16 | `NatTrans.lean` |
| strong bundle maps between strong bundles over M-polyfolds; the pull-back along $s$ (used, not defined) | 270 | V8.19 | `StrongBundleMap.lean` |
| $\mu(\psi,\cdot) : W_x \to W_y$ a linear isomorphism | 271 | V8.21 | `EpStrongBundle.lean` |
| the functorial picture: the ep-groupoid $(W,\mathbf W)$ and the functor $(P,\pi_1)$ | 271–272 | V8.22 | `EpStrongBundle.lean` |
| Definitions 8.5 and 8.6: "these are identical notions" | 273–274 | V8.25 | `EpStrongBundle.lean` |
| the degeneracy remark after Definition 8.8 | 275–276 | V8.28 | `ProperCovering.lean` |
| the discussion after Definition 8.9 ($\tau(y)$, $\varphi_{yy'}$, the actions, equivariance) | 280–281 | V8.33 | `GeometricLift.lean` |
| disjoint unions of M-polyfolds (used, not described) | 281 | V8.34 | `SigmaPolyfold.lean` |
| §8.5.1 before Lemma 8.9: $\#\mathrm{mor}(F^{-1}(x)) = \#G_x\cdot\#F^{-1}(x)$, the classes $\Theta_j$ | 286 | V8.38 | `ProperCovering.lean` |
| §8.5.2: $y \mapsto A_y$ a natural transformation $\mu_Y \to \mu_X \circ F$ | 288–289 | V8.43 | `EpStrongBundle.lean` |

$\mathrm{Diff}_{sc}$ (p. 279) is part of V8.32. The witnesses that show the hypotheses can hold
(`NonVacuity.lean`, `NonVacuityBundle.lean` and the witnesses in the other files; `Findings.md`,
Chapter 8, items 100–105) have no V-item of their own; the counterexample to Theorem 8.5 (5) as
printed, `Polyfold.CoveringExamples.theorem_8_5_3_five_as_printed` in `NonVacuity.lean`, belongs to
V8.30. Points of Chapter 8: G.74 (Definitions 8.2 and 8.3, pp. 268–270, sc-differential forms
on ep-groupoids and the sc-de Rham complex) and G.75 (Lemma 8.1 as printed, p. 259, the
identification $T(\mathbf X\,{}_s{\times}_t\,\mathbf X) = T\mathbf X\,{}_{Ts}{\times}_{Tt}\,T\mathbf X$ with
$m_{T\mathbf X} = Tm$); G.70 (Definition 7.4, $T\varphi$) is formalized in part, by Remark 8.1.
`verification/ch08.md` contains no *(book?)* mark: there is no other numbering to check against.

## The Springer edition (2021), Chapters 1–8

The published book, Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Ergebnisse der Mathematik
und ihrer Grenzgebiete 72, Springer 2021), is available as `sources/HWZ-Book-2021.txt` (a `pdftotext
-layout` text of the Springer PDF; `sources/` is gitignored, so the book text is not in the repository
and nothing of it is quoted here beyond a few words). This section gives, for every numbered item of
the 2017 arXiv text in Chapters 1–8, its Springer counterpart, its printed page and a status; for
Chapters 1–6 the preprint number is carried along by composing with the tables above. The 2021 edition
is the authoritative one **from Chapter 9 on**; the Lean names of Chapters 1–8 keep the preprint
(Part I) and 2017 (Part II) numbers, the report citations of Chapters 1–8 give the 2021 numbers
and pages first, with the old ones in parentheses, and the tables below give the correspondence.

**Method.** The numbered items (Definition, Theorem, Lemma, Proposition, Corollary, Remark, Example) of
the 2017 and the 2021 text were extracted with their pages and aligned chapter by chapter, in order, by
the text of the statement. Every pair whose statement text agreed to less than 90 %, every item
without a partner, and a spot sample of the remaining pairs were then read in both texts; after
normalizing editorial changes ("a sc-" to "an sc-", hyphenation, citation numbers, cross-reference
numbers, renamed bound variables) the statements were compared word by word. Items restated in an
appendix before their proof (2017 Lemmas 3.22 and 3.23) and items whose heading carries a title
("Theorem 5.8 (Morse-type structure)") needed a manual pairing. Pages are printed pages, read off the
running heads and the table of contents; the chapters occupy pp. 5–20 (Ch. 1), 21–88, 89–174, 175–204,
205–236, 237–286, 287–356, 357–400 (Ch. 8). "p." is the page of the item's heading in the 2021 text.
Status: `same` = the statement is unchanged up to editorial wording (a remark in brackets records an
editorial side remark such as a moved sentence); `changed: …` = the mathematical content of the
statement differs (a hypothesis or conclusion added or dropped, a corrected index, a split); `absent` =
no counterpart as a numbered item, with the place where the content went. The comparison is of
statements, not of proofs; a `same` does not certify that the proof is unchanged. Numbered items of
other kinds (the 2017 Question 4.1 is Question 4.2.4 in 2021, p. 187) are not counted.

### Structural differences

- **Three-level numbering.** Every statement is numbered *chapter.section.item* with one counter per
  section, shared by all kinds of statements (Definition 2.3.4, Lemma 2.3.5, Proposition 2.3.6, …).
  The collisions of the 2017 numbers across kinds (Definition 3.13 and Theorem 3.13) are gone.
  Displayed equations are still numbered by chapter, e.g. (2.9), (6.31); the 2017 equation numbers
  therefore also shift.
- **Chapter pagination.** The first page of Chapter 1 is p. 5 (Chapters 1–8: 5–20, 21–88, 89–174,
  175–204, 205–236, 237–286, 287–356, 357–400).
- **New sections.** §2.2 (basic properties of sc-smooth retracts), §6.1 (an overview), §7.4
  (regularity assumptions and the Zhou condition), §8.4 (topological and regularity properties of
  strong bundles). New or new-numbered appendices: 1.4.4, 2.7.4, 3.8.2, 4.5 (with 4.5.1–4.5.3), 7.6.3–7.6.5.
  Because of the new sections the 2017 section numbers 2.2–2.6, 6.1–6.7, 7.4–7.5 and 8.4–8.5 move up
  by one in 2021.
- **New and rewritten content** (details in the lists below): locally complete spaces, local
  path-connectedness (§2.1, §2.2), the tame boundary $b X$ (§2.7.4), the proof of the sc$^1$ regularity of the
  solution germ, Theorem 3.3.3 (§3.8.2; quoted from [37] in 2017), vector fields, the Lie bracket and the Poincaré lemma (§4.4,
  §4.5), $\mathrm{proper}_{<\infty}$ (§5.2), the reduced ep-groupoid and the local unique continuation
  property (§7.2, rewritten), LUC, the Zhou condition and local regularity (§7.4), the tangent and
  Zhou's condition (Props. 8.1.16–8.1.17), the Poincaré lemma on ep-groupoids (Prop. 8.2.3),
  auxiliary norms on bundles over ep-groupoids and §8.4.
- **Conventions fixed by footnotes.** Paracompactness does not include the Hausdorff property
  (footnote to Definition 2.3.4, repeated in later chapters); "Banach space" means Banachable space
  (Remark 1.1.2).
- **Editorial.** "a sc-" becomes "an sc-" throughout; the bibliography is renumbered (2017 [36], [37],
  [42] are [54], [55], [60] in 2021); small points of wording of the 2017 text are mostly settled
  silently (those that touch a statement are recorded below).
- **Section titles.** Chapter and section titles, 2017 against 2021 (pages are the printed pages of
  each text):

| Ch. | arXiv 1707.08941 | p. | Springer 2021 | p. |
|---|---|---|---|---|
| 1 | 1 Sc-Calculus | 3 | 1 Sc-Calculus | 5 |
| 1 | 1.1 Sc-Structures and Differentiability | 3 | 1.1 (same title) | 5 |
| 1 | 1.2 Properties of Sc-Differentiability | 9 | 1.2 (same title) | 11 |
| 1 | 1.3 The Chain Rule and Boundary Recognition | 10 | 1.3 (same title) | 13 |
| 1 | 1.4 Appendix: 1.4.1 sc-Fredholm stability, 1.4.2 chain rule, 1.4.3 Proof Lemma 1.1 | 11, 11, 12, 13 | 1.4 Appendix: 1.4.1, 1.4.2, 1.4.3 Proof Lemma 1.3.4 | 15, 15, 15, 17 |
| 1 | — |  | 1.4.4 A Useful Example (new) | 17 |
| 2 | 2 Retracts | 15 | 2 Retracts | 21 |
| 2 | 2.1 Retractions and Retracts | 15 | 2.1 (same title) | 21 |
| 2 | — |  | 2.2 Some Basic Properties of Sc-Smooth Retracts (new) | 30 |
| 2 | 2.2 M-Polyfolds and Sub-M-Polyfolds | 20 | 2.3 (same title) | 33 |
| 2 | 2.3 Degeneracy Index and Boundary Geometry | 27 | 2.4 The Degeneracy Index and Boundary Geometry | 44 |
| 2 | 2.4 Tame M-polyfolds | 34 | 2.5 (same title) | 52 |
| 2 | 2.5 Strong Bundles | 44 | 2.6 (same title) | 65 |
| 2 | 2.6 Appendix: 2.6.1 Proof of Proposition 2.1, 2.6.2 Proof of Theorem 2.2, 2.6.3 Proof of Proposition 2.5 | 49, 49, 51, 53 | 2.7 Appendix: 2.7.1 Proof of Proposition 2.1.2, 2.7.2 Proof of Theorem 2.3.10, 2.7.3 Proof of Proposition 2.3.15 | 69, 69, 71, 76 |
| 2 | — |  | 2.7.4 Formalism Associated to a Boundary with Corners (new) | 78 |
| 3 | 3 Basic Sc-Fredholm Theory | 57 | 3 Basic Sc-Fredholm Theory | 89 |
| 3 | 3.1 Sc-Fredholm Sections | 57 | 3.1 (same title) | 89 |
| 3 | 3.2 Subsets with Tangent Structure | 71 | 3.2 (same title) | 104 |
| 3 | 3.3 Contraction Germs | 76 | 3.3 (same title) | 109 |
| 3 | 3.4 Stability of Basic Germs | 80 | 3.4 (same title) | 113 |
| 3 | 3.5 Geometry of Basic Germs | 84 | 3.5 The Geometry of Basic Germs | 117 |
| 3 | 3.6 Implicit Function Theorems | 97 | 3.6 (same title) | 134 |
| 3 | 3.7 Conjugation to a Basic Germ | 103 | 3.7 (same title) | 140 |
| 3 | 3.8 Appendix: 3.8.1 Proof of Proposition 3.3, 3.8.2 Proof of Lemma 3.9, 3.8.3 Proof of Lemma 3.10, 3.8.4 Diffeomorphisms Between Partial Quadrants, 3.8.5 An Implicit Function Theorem in Partial Quadrants | 107, 107, 114, 117, 119, 125 | 3.8 Appendix: 3.8.1 Proof of Proposition 3.1.25, 3.8.2 Proof of Theorem 3.3.3 (new), 3.8.3 Proof of Lemma 3.5.10, 3.8.4 Proof of Lemma 3.6.9, 3.8.5 Diffeomorphisms Between Partial Quadrants, 3.8.6 An Implicit Function Theorem in Partial Quadrants | 144, 144, 155, 158, 161, 163, 169 |
| 4 | 4 Manifolds and Strong Retracts | 131 | 4 Manifolds and Strong Retracts | 175 |
| 4 | 4.1 Characterization | 131 | 4.1 (same title) | 175 |
| 4 | 4.2 Smooth Finite Dimensional Submanifolds | 139 | 4.2 Smooth Finite-Dimensional Submanifolds | 184 |
| 4 | 4.3 Families and an Application of Sard's Theorem | 147 | 4.3 (same title) | 193 |
| 4 | 4.4 Sc-Differential Forms | 149 | 4.4 (same title) | 195 |
| 4 | — |  | 4.5 Appendix (new): 4.5.1 Definition of the Lie Bracket, 4.5.2 Proof of Proposition 4.4.5, 4.5.3 Proof of the Poincar\'e Lemma | 199, 200, 201, 202 |
| 5 | 5 Fredholm Package for M-Polyfolds | 151 | 5 The Fredholm Package for M-Polyfolds | 205 |
| 5 | 5.1 Auxiliary Norms | 151 | 5.1 (same title) | 205 |
| 5 | 5.2 Compactness Results | 155 | 5.2 (same title) | 208 |
| 5 | 5.3 Perturbation Theory and Transversality | 161 | 5.3 (same title) | 216 |
| 5 | 5.4 Remark on Extensions of Sc+-Sections | 172 | 5.4 (same title) | 228 |
| 5 | 5.5 Notes on Partitions of Unity and Bump Functions | 173 | 5.5 (same title) | 229 |
| 6 | 6 Orientations | 181 | 6 Orientations | 237 |
| 6 | — |  | 6.1 An Overview (new) | 237 |
| 6 | 6.1 Linearizations of Sc-Fredholm Sections | 181 | 6.2 (same title) | 239 |
| 6 | 6.2 Linear Algebra and Conventions | 184 | 6.3 (same title) | 241 |
| 6 | 6.3 The Determinant of a Fredholm Operator | 189 | 6.4 (same title) | 246 |
| 6 | 6.4 Classical Local Determinant Bundles | 200 | 6.5 (same title) | 258 |
| 6 | 6.5 Local Orientation Propagation | 204 | 6.6 (same title) | 262 |
| 6 | 6.6 Invariants | 215 | 6.7 (same title) | 276 |
| 6 | 6.7 Appendix: 6.7.1 Proof of Lemma 6.1, 6.7.2 Proof of Proposition 6.5 | 218, 218, 219 | 6.8 Appendix: 6.8.1 Proof of Lemma 6.3.3, 6.8.2 Proof of Proposition 6.4.11 | 279, 279, 281 |
| 7 | 7 Ep-Groupoids | 225 | 7 Ep-Groupoids | 287 |
| 7 | 7.1 Ep-Groupoids and Basic Properties | 225 | 7.1 (same title) | 287 |
| 7 | 7.2 Effective and Reduced Ep-Groupoids | 239 | 7.2 (same title) | 307 |
| 7 | 7.3 Topological Properties of Ep-Groupoids | 244 | 7.3 (same title) | 323 |
| 7 | — |  | 7.4 Regularity Assumptions and the Zhou Condition (new) | 328 |
| 7 | 7.4 Paracompact Orbit Spaces | 249 | 7.5 (same title) | 340 |
| 7 | 7.5 Appendix: 7.5.1 The Natural Representation, 7.5.2 Sc-Smooth Partitions of Unity | 253, 253, 254 | 7.6 Appendix: 7.6.1 The Natural Representation, 7.6.2 Sc-Smooth Partitions of Unity | 344, 344, 346 |
| 7 | — |  | 7.6.3 On the metrizability of $T_R$ (new), 7.6.4 Reduced Ep-Groupoids and Raising the Index (new), 7.6.5 Boundary Structure of Tame Ep-Groupoids (new) | 348, 348, 351 |
| 8 | 8 Bundles and Covering Functors | 257 | 8 Bundles and Covering Functors | 357 |
| 8 | 8.1 The Tangent of an Ep-Groupoid | 257 | 8.1 (same title) | 357 |
| 8 | 8.2 Sc-Differential Forms on Ep-Groupoids | 268 | 8.2 (same title) | 372 |
| 8 | 8.3 Strong Bundles over Ep-Groupoids | 270 | 8.3 (same title) | 374 |
| 8 | — |  | 8.4 Topological and Regularity Properties of Strong Bundles (new) | 379 |
| 8 | 8.4 Proper Covering Functors | 275 | 8.5 (same title) | 383 |
| 8 | 8.5 Appendix: 8.5.1 Local Structure of Proper Coverings, 8.5.2 The Structure of Strong Bundle Coverings | 286, 286, 288 | 8.6 Appendix: 8.6.1, 8.6.2 (same titles) | 396, 396, 399 |

### Concordance tables, Chapters 1–8

Rows follow the 2017 order; the preprint column is the number in the table of the same chapter above, "—" for 2017 items without a preprint number. Preprint items absent from the 2017 text are also absent in 2021 (Theorem 3.35, Theorem 5.25, Lemma 5.26, Theorem 5.27, Lemma 6.10); they are listed at their place. A 2017 item that appears twice in 2021 (Lemmas 3.9/3.22 as Lemma 3.5.10, Lemmas 3.10/3.23 as Lemma 3.6.9) is a restatement.

#### Chapter 1 (2021 pp. 5–20)

| Preprint 2014 | arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|---|
| Definition 1.1 | Definition 1.1 | Definition 1.1.1 | 5 | same |
| Example 1.2 | Example 1.1 | Example 1.1.3 | 6 | same |
| Definition 1.3 | Definition 1.2 | Definition 1.1.4 | 6 | same |
| Definition 1.4 | Definition 1.3 | Definition 1.1.5 | 7 | same |
| Definition 1.5 | Definition 1.4 | Definition 1.1.6 | 7 | same |
| Proposition 1.6 | Proposition 1.1 | Proposition 1.1.7 | 7 | same |
| Proposition 1.7 | Proposition 1.2 | Proposition 1.1.8 | 8 | same |
| Definition 1.8 | Definition 1.5 | Definition 1.1.9 | 8 | same |
| Proposition 1.9 | Proposition 1.3 | Proposition 1.1.10 | 9 | same |
| Proposition 1.10 | Proposition 1.4 | Proposition 1.1.11 | 9 | changed: adds the conclusion that $T+S$ has the same index |
| Definition 1.11 | Definition 1.6 | Definition 1.1.12 | 9 | same |
| Definition 1.12 | Definition 1.7 | Definition 1.1.13 | 9 | same |
| Definition 1.13 | Definition 1.8 | Definition 1.1.14 | 9 | same |
| Definition 1.14 | Definition 1.9 | Definition 1.1.15 | 10 | same |
| — | Remark 1.1 | Remark 1.1.16 | 10 | same |
| Remark 1.15 | Remark 1.2 | Remark 1.1.17 | 10 | same |
| — | Remark 1.3 | Remark 1.1.18 | 11 | same |
| Proposition 1.16 | Proposition 1.5 | Proposition 1.2.1 | 11 | same (the "in particular" sentence moved after the proof) |
| Proposition 1.17 | Proposition 1.6 | Proposition 1.2.2 | 13 | same |
| Proposition 1.18 | Proposition 1.7 | Proposition 1.2.3 | 13 | same |
| Proposition 1.19 | Proposition 1.8 | Proposition 1.2.4 | 13 | same |
| Corollary 1.20 | Corollary 1.1 | Corollary 1.2.5 | 13 | same |
| Theorem 1.21 | Theorem 1.1 | Theorem 1.3.1 | 13 | same |
| Remark 1.22 | Remark 1.4 | Remark 1.3.2 | 14 | same |
| Definition 1.23 | Definition 1.10 | Definition 1.3.3 | 14 | same |
| Lemma 1.24 | Lemma 1.1 | Lemma 1.3.4 | 14 | same |
| Theorem 1.25 | Theorem 1.2 | Theorem 1.3.5 | 14 | same |

#### Chapter 2 (2021 pp. 21–88)

| Preprint 2014 | arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|---|
| Definition 2.1 | Definition 2.1 | Definition 2.1.1 | 21 | same |
| Proposition 2.2 | Proposition 2.1 | Proposition 2.1.2 | 22 | same |
| Definition 2.3 | Definition 2.2 | Definition 2.1.3 | 22 | same |
| Proposition 2.4 | Proposition 2.2 | Proposition 2.1.11 | 26 | same |
| Definition 2.5 | Definition 2.3 | Definition 2.1.12 | 26 | same |
| Proposition 2.6 | Proposition 2.3 | Proposition 2.1.13 | 27 | changed: (3) now holds only under the hypothesis that $f\circ r$ is sc-smooth |
| Definition 2.7 | Definition 2.4 | Definition 2.1.14 | 27 | same |
| Theorem 2.8 | Theorem 2.1 | Theorem 2.1.15 | 28 | same |
| Definition 2.9 | Definition 2.5 | Definition 2.1.16 | 29 | same |
| — | Remark 2.1 | Remark 2.1.18 | 30 | same |
| Proposition 2.10 | Proposition 2.4 | Proposition 2.3.1 | 33 | same |
| Definition 2.11 | Definition 2.6 | Definition 2.3.2 | 34 | same (footnotes added: a chart around $x$ is also a chart around every $x'\in V$) |
| Definition 2.12 | Definition 2.7 | Definition 2.3.3 | 35 | same |
| Definition 2.13 | Definition 2.8 | Definition 2.3.4 | 35 | changed: footnote mark on "paracompact": by convention paracompactness does not include Hausdorffness (stated separately); adds a pointer to Theorem 2.3.10 (metrizability) |
| Definition 2.14 | Definition 2.9 | Definition 2.3.8 | 37 | same |
| Lemma 2.15 | Lemma 2.1 | Lemma 2.3.9 | 37 | same |
| Theorem 2.16 | Theorem 2.2 | Theorem 2.3.10 | 37 | same |
| Definition 2.17 | Definition 2.10 | Definition 2.3.12 | 38 | same |
| Definition 2.18 | Definition 2.11 | Definition 2.3.14 | 39 | same |
| Proposition 2.19 | Proposition 2.5 | Proposition 2.3.15 | 39 | same |
| Definition 2.20 | Definition 2.12 | Definition 2.3.18 | 42 | same |
| Proposition 2.21 | Proposition 2.6 | Proposition 2.3.19 | 42 | same |
| Definition 2.22 | Definition 2.13 | Definition 2.4.1 | 44 | same |
| Lemma 2.23 | Lemma 2.2 | Lemma 2.4.3 | 45 | same |
| Proposition 2.24 | Proposition 2.7 | Proposition 2.4.4 | 45 | same |
| Definition 2.25 | Definition 2.14 | Definition 2.4.5 | 45 | same |
| Lemma 2.26 | Lemma 2.3 | Lemma 2.4.6 | 45 | same |
| Definition 2.27 | Definition 2.15 | Definition 2.4.7 | 47 | same |
| Remark 2.28 | Remark 2.2 | Remark 2.4.8 | 47 | same |
| Lemma 2.29 | Lemma 2.4 | Lemma 2.4.9 | 48 | same |
| Proposition 2.30 | Proposition 2.8 | Proposition 2.4.10 | 49 | same |
| — | Remark 2.3 | Remark 2.4.11 | 49 | same |
| Theorem 2.31 | Theorem 2.3 | Theorem 2.4.12 | 50 | same |
| Corollary 2.32 | Corollary 2.1 | Corollary 2.4.13 | 51 | same |
| Definition 2.33 | Definition 2.16 | Definition 2.5.1 | 53 | same |
| Definition 2.34 | Definition 2.17 | Definition 2.5.2 | 53 | same |
| Proposition 2.35 | Proposition 2.9 | Proposition 2.5.3 | 54 | same |
| — | Definition 2.18 | Definition 2.5.4 | 55 | same |
| — | Lemma 2.5 | Lemma 2.5.5 | 55 | same |
| Proposition 2.36 | Proposition 2.10 | Proposition 2.5.6 | 56 | same |
| Definition 2.37 | Definition 2.19 | Definition 2.5.7 | 57 | same |
| Definition 2.38 | Definition 2.20 | Definition 2.5.8 | 57 | same |
| — | Remark 2.4 | Remark 2.5.9 | 57 | same |
| Definition 2.39 | Definition 2.21 | Definition 2.5.10 | 57 | same |
| — | Proposition 2.11 | Proposition 2.5.11 | 58 | same |
| Lemma 2.40 | Lemma 2.6 | Lemma 2.5.12 | 59 | same |
| Corollary 2.41 | Corollary 2.2 | Corollary 2.5.13 | 59 | same |
| Proposition 2.42 | Proposition 2.12 | Proposition 2.5.14 | 60 | same |
| Proposition 2.43 | Proposition 2.13 | Proposition 2.5.15 | 61 | same |
| Proposition 2.44 | Proposition 2.14 | Proposition 2.5.16 | 62 | same |
| Theorem 2.45 | Theorem 2.4 | Theorem 2.5.17 | 62 | same |
| Proposition 2.46 | Proposition 2.15 | Proposition 2.5.20 | 63 | same |
| Definition 2.47 | Definition 2.22 | Definition 2.6.1 | 65 | same |
| Definition 2.48 | Definition 2.23 | Definition 2.6.2 | 66 | same |
| Definition 2.49 | Definition 2.24 | Definition 2.6.3 | 66 | same |
| Definition 2.50 | Definition 2.25 | Definition 2.6.4 | 67 | same |
| Definition 2.51 | Definition 2.26 | Definition 2.6.5 | 68 | same |
| Definition 2.52 | Definition 2.27 | Definition 2.6.6 | 68 | same |
| Definition 2.53 | Definition 2.28 | Definition 2.6.7 | 69 | same |
| Proposition 2.54 | Proposition 2.16 | Proposition 2.6.8 | 69 | same |
| Theorem 2.55 | Theorem 2.5 | Theorem 2.7.1 | 72 | same |
| Lemma 2.56 | Lemma 2.7 | Lemma 2.7.3 | 72 | same |
| Proposition 2.57 | Proposition 2.17 | Proposition 2.7.4 | 74 | same |

#### Chapter 3 (2021 pp. 89–174)

| Preprint 2014 | arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|---|
| Definition 3.1 | Definition 3.1 | Definition 3.1.1 | 89 | same |
| Definition 3.2 | Definition 3.2 | Definition 3.1.2 | 90 | same |
| Definition 3.3 | Definition 3.3 | Definition 3.1.3 | 91 | same |
| Definition 3.4 | Definition 3.4 | Definition 3.1.4 | 91 | changed: the retraction $r$ is no longer required to be tame (2017: "covering the tame retraction") |
| Proposition 3.5 | Proposition 3.1 | Proposition 3.1.5 | 93 | same |
| Definition 3.6 | Definition 3.5 | Definition 3.1.6 | 93 | same |
| Definition 3.7 | Definition 3.6 | Definition 3.1.7 | 94 | same |
| Remark 3.8 | Remark 3.1 | Remark 3.1.8 | 94 | same |
| Lemma 3.9 | Lemma 3.1 | Lemma 3.1.9 | 94 | same |
| Proposition 3.10 | Proposition 3.2 | Proposition 3.1.10 | 95 | same |
| Definition 3.11 | Definition 3.7 | Definition 3.1.11 | 96 | same ("the pushed-forward section has a principal part which is a basic germ") |
| — | Remark 3.2 | Remark 3.1.12 | 96 | same |
| Theorem 3.12 | Theorem 3.1 | Theorem 3.1.13 | 97 | same |
| — | Remark 3.3 | Remark 3.1.14 | 97 | same |
| Corollary 3.13 | Corollary 3.1 | Corollary 3.1.15 | 97 | same |
| Definition 3.14 | Definition 3.8 | Definition 3.1.16 | 97 | same |
| — | Remark 3.4 | Remark 3.1.17 | 98 | same |
| Theorem 3.15 | Theorem 3.2 | Theorem 3.1.18 | 98 | same (adds the sentence "in other words, there is a natural map $\mathrm{Fred}(P)\times\Gamma^+(P)\to\mathrm{Fred}(P)$") |
| Lemma 3.16 | Lemma 3.2 | Lemma 3.1.19 | 99 | same |
| Lemma 3.17 | Lemma 3.3 | Lemma 3.1.20 | 99 | same |
| Theorem 3.18 | Theorem 3.3 | Theorem 3.1.21 | 100 | same |
| Theorem 3.19 | Theorem 3.4 | Theorem 3.1.22 | 100 | same |
| Remark 3.20 | Remark 3.5 | Remark 3.1.23 | 101 | same |
| Definition 3.21 | Definition 3.9 | Definition 3.1.24 | 102 | same |
| Proposition 3.22 | Proposition 3.3 | Proposition 3.1.25 | 103 | same |
| Theorem 3.23 | Theorem 3.5 | Theorem 3.1.26 | 103 | same ((1) reworded: $S(f,U)$ is a sub-M-polyfold whose induced structure is tame) |
| Corollary 3.24 | Corollary 3.2 | Corollary 3.1.27 | 104 | same |
| Definition 3.25 | Definition 3.10 | Definition 3.2.1 | 104 | same |
| Proposition 3.26 | Proposition 3.4 | Proposition 3.2.2 | 105 | same |
| Theorem 3.27 | Theorem 3.6 | Theorem 3.2.3 | 106 | same |
| Definition 3.28 | Definition 3.11 | Definition 3.3.1 | 109 | same |
| Theorem 3.29 | Theorem 3.7 | Theorem 3.3.2 | 110 | same |
| Theorem 3.30 | Theorem 3.8 | Theorem 3.3.3 | 110 | same (a proof (a modification of the original proof in [55]) is now given in Appendix 3.8.2; 2017 quotes the result from [37], Theorem 2.3) |
| Lemma 3.31 | Lemma 3.4 | Lemma 3.3.4 | 111 | same |
| Lemma 3.32 | Lemma 3.5 | Lemma 3.3.5 | 111 | same |
| Theorem 3.33 | Theorem 3.9 | Theorem 3.3.6 | 112 | same |
| Corollary 3.34 | Corollary 3.3 | Corollary 3.3.7 | 113 | same |
| Theorem 3.35 | absent | absent | — | absent in 2017 and in 2021 (see the 2017 table above) |
| Remark 3.36 | Remark 3.6 | Remark 3.3.8 | 113 | same |
| Definition 3.37 | Definition 3.12 | Definition 3.4.1 | 114 | same |
| Theorem 3.38 | Theorem 3.10 | Theorem 3.4.2 | 114 | same |
| Corollary 3.39 | Corollary 3.4 | Corollary 3.4.3 | 116 | same |
| Theorem 3.40 | Theorem 3.11 | Theorem 3.5.1 | 118 | changed: adds a conclusion: a sequence of solutions converging to $(0,0)$ on level 0 lies in $C_m$ for $k\ge k_0(m)$ and converges there on level $m$ |
| — | Remark 3.7 | Remark 3.5.2 | 118 | same |
| Corollary 3.41 | Corollary 3.5 | Corollary 3.5.3 | 122 | same |
| Lemma 3.42 | Lemma 3.6 | Lemma 3.5.5 | 126 | same |
| Theorem 3.43 | Theorem 3.12 | Theorem 3.5.6 | 126 | same |
| Lemma 3.44 | Lemma 3.7 | Lemma 3.5.8 | 127 | same |
| Lemma 3.45 | Lemma 3.8 | Lemma 3.5.9 | 128 | same |
| Lemma 3.46 | Lemma 3.9 | Lemma 3.5.10 | 129 | same |
| Corollary 3.47 | Corollary 3.6 | Theorem 3.5.11 | 131 | same (now a Theorem ("Local Germ-Solvability II"); the setting $E=\mathbb R^n\oplus W$, $C=[0,\infty)^k\oplus\mathbb R^{n-k}\oplus W$ is stated) |
| Definition 3.48 | Definition 3.13 | Definition 3.6.1 | 134 | changed: the retraction $r$ is only required to be sc-smooth (2017: "tame retraction") |
| Remark 3.49 | Remark 3.8 | Remark 3.6.2 | 135 | same |
| Definition 3.50 | Definition 3.14 | Definition 3.6.3 | 135 | same |
| Definition 3.51 | Definition 3.15 | Definition 3.6.4 | 135 | same |
| Proposition 3.52 | Proposition 3.5 | Proposition 3.6.5 | 135 | same |
| Definition 3.53 | Definition 3.16 | Definition 3.6.6 | 136 | same |
| — | Remark 3.9 | Remark 3.6.7 | 136 | same |
| Theorem 3.54 | Theorem 3.13 | Theorem 3.6.8 | 136 | same |
| Lemma 3.55 | Lemma 3.10 | Lemma 3.6.9 | 139 | same |
| Theorem 3.56 | Theorem 3.14 | Theorem 3.6.10 | 140 | same |
| Theorem 3.57 | Theorem 3.15 | Theorem 3.6.11 | 140 | same |
| Theorem 3.58 | Theorem 3.16 | Theorem 3.7.1 | 140 | same |
| Lemma 3.59 | Lemma 3.11 | Lemma 3.7.2 | 141 | same |
| Lemma 3.60 | Lemma 3.12 | Lemma 3.7.3 | 142 | same |
| Lemma 3.61 | Lemma 3.13 | Lemma 3.7.4 | 142 | same |
| Lemma 3.62 | Lemma 3.14 | Lemma 3.8.1 | 145 | same |
| Lemma 3.63 | Lemma 3.15 | Lemma 3.8.2 | 145 | same |
| Lemma 3.64 | Lemma 3.16 | Lemma 3.8.3 | 146 | same |
| Lemma 3.65 | Lemma 3.17 | Lemma 3.8.8 | 150 | same |
| Lemma 3.66 | Lemma 3.18 | Lemma 3.8.9 | 150 | same |
| Lemma 3.67 | Lemma 3.19 | Lemma 3.8.10 | 151 | same |
| Lemma 3.68 | Lemma 3.20 | Lemma 3.8.11 | 151 | same |
| Proposition 3.69 | Proposition 3.6 | Proposition 3.8.12 | 153 | same |
| Lemma 3.70 | Lemma 3.21 | Lemma 3.8.13 | 154 | same |
| — | Lemma 3.22 | Lemma 3.5.10 | 158 | same (restatement of Lemma 3.9 in Appendix 3.8.3, p. 158) |
| — | Lemma 3.23 | Lemma 3.6.9 | 161 | same (restatement of Lemma 3.10 in Appendix 3.8.4, p. 161) |
| Definition 3.71 | Definition 3.17 | Definition 3.8.14 | 164 | same |
| Theorem 3.72 | Theorem 3.17 | Theorem 3.8.15 | 165 | same |
| Proposition 3.73 | Proposition 3.7 | Proposition 3.8.17 | 165 | same |
| Lemma 3.74 | Lemma 3.24 | Lemma 3.8.18 | 165 | same |
| Corollary 3.75 | Corollary 3.7 | Corollary 3.8.19 | 167 | same |
| Lemma 3.76 | Lemma 3.25 | Lemma 3.8.20 | 167 | same |
| Lemma 3.77 | Lemma 3.26 | Lemma 3.8.21 | 168 | same |
| Theorem 3.78 | Theorem 3.18 | Theorem 3.8.22 | 169 | same |
| Lemma 3.79 | Lemma 3.27 | Lemma 3.8.23 | 170 | same |
| Lemma 3.80 | Lemma 3.28 | Lemma 3.8.24 | 170 | same |
| Lemma 3.81 | Lemma 3.29 | Lemma 3.8.25 | 171 | same |
| Lemma 3.82 | Lemma 3.30 | Lemma 3.8.26 | 172 | same |

#### Chapter 4 (2021 pp. 175–204)

| Preprint 2014 | arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|---|
| Definition 4.1 | Definition 4.1 | Definition 4.1.1 | 175 | same (reworded: a classically smooth atlas whose charts are sc-diffeomorphisms for the induced M-polyfold structure) |
| Theorem 4.2 | Theorem 4.1 | Theorem 4.1.2 | 176 | same |
| Remark 4.3 | Remark 4.1 | Remark 4.1.3 | 176 | same |
| Definition 4.4 | Definition 4.2 | Definition 4.1.4 | 176 | same |
| Lemma 4.5 | Lemma 4.1 | Lemma 4.1.5 | 177 | same |
| Definition 4.6 | Definition 4.3 | Definition 4.1.6 | 177 | same |
| Lemma 4.7 | Lemma 4.2 | Lemma 4.1.7 | 177 | same |
| Proposition 4.8 | Proposition 4.1 | Proposition 4.1.8 | 177 | same |
| Proposition 4.9 | Proposition 4.2 | Proposition 4.1.9 | 178 | same |
| — | Remark 4.2 | Remark 4.1.10 | 178 | same |
| Lemma 4.10 | Lemma 4.3 | Lemma 4.1.11 | 179 | same |
| Lemma 4.11 | Lemma 4.4 | Lemma 4.1.12 | 181 | same |
| Lemma 4.12 | Lemma 4.5 | Lemma 4.1.13 | 182 | same |
| Definition 4.13 | Definition 4.4 | Definition 4.2.1 | 184 | same |
| Remark 4.14 | Remark 4.3 | Remark 4.2.2 | 184 | same |
| Proposition 4.15 | Proposition 4.3 | Proposition 4.2.3 | 186 | same |
| Definition 4.16 | Definition 4.5 | Definition 4.2.5 | 188 | same |
| Definition 4.17 | Definition 4.6 | Definition 4.2.6 | 188 | same |
| Theorem 4.18 | Theorem 4.2 | Theorem 4.2.7 | 188 | same |
| Lemma 4.19 | Lemma 4.6 | Lemma 4.2.8 | 188 | same |
| Remark 4.20 | Remark 4.4 | Remark 4.2.9 | 189 | same |
| Definition 4.21 | Definition 4.7 | Definition 4.2.10 | 190 | same |
| Theorem 4.22 | Theorem 4.3 | Theorem 4.2.11 | 190 | changed: in (1) the local faces $F_1,\dots,F_d$ are required to contain $x$ |
| — | Definition 4.8 | Definition 4.2.12 | 192 | same |
| — | Proposition 4.4 | Proposition 4.2.13 | 192 | same |
| Theorem 4.23 | Theorem 4.4 | Theorem 4.3.1 | 193 | changed: in (1) non-emptiness of $p^{-1}(\lambda)$ dropped; $\Sigma$ is a "measurable set of full measure" (2017: "a set of full measure") |
| Remark 4.24 | Remark 4.5 | Remark 4.3.2 | 193 | same |
| Definition 4.25 | Definition 4.9 | Definition 4.4.1 | 195 | same (the direct limit $\Omega^k_\infty$ and the graded space $\Omega^*_\infty$ moved to Definitions 4.4.1-4.4.2) |
| Proposition 4.26 | Proposition 4.5 | Proposition 4.4.5 | 196 | changed: the levels of $d$ are stated as $\Omega^k(X^i)\to\Omega^{k+1}(X^{i+1})$ (2017: $\Omega^k(X^{i+1})\to\Omega^{k+1}(X^i)$, presumably meant as in 2021); $[A,B]$ is a section of $TX$ restricted to $X^2$, over $X^2$; the formula for $d$ is spelled out; proof in Appendix 4.5 |
| Definition 4.27 | Definition 4.10 | Definition 4.4.6 | 198 | same |
| Theorem 4.28 | Theorem 4.5 | Theorem 4.4.7 | 199 | same (the sentences "$N$ is not assumed face structured" and on $f^*$ dropped; the Poincar\'e lemma is stated as Lemma 4.4.8) |

#### Chapter 5 (2021 pp. 205–236)

| Preprint 2014 | arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|---|
| Definition 5.1 | Definition 5.1 | Definition 5.1.1 | 205 | same |
| Lemma 5.2 | Lemma 5.1 | Lemma 5.1.2 | 205 | same |
| Proposition 5.3 | Proposition 5.1 | Proposition 5.1.3 | 206 | same |
| — | Definition 5.2 | Definition 5.1.4 | 207 | same |
| — | Lemma 5.2 | Lemma 5.1.5 | 207 | same |
| — | Definition 5.3 | Definition 5.1.6 | 207 | same |
| — | Definition 5.4 | Definition 5.1.7 | 208 | same |
| — | Proposition 5.2 | Proposition 5.1.8 | 208 | same |
| Definition 5.4 | Definition 5.5 | Definition 5.2.1 | 209 | changed: adds (4) weakly proper$_{<\infty}$ and (5) proper$_{<\infty}$; in (2) the bound $N(s)\le1$ is required on $U$ only |
| Theorem 5.5 | Theorem 5.1 | Theorem 5.2.2 | 210 | changed: conclusion strengthened: a compact solution set implies proper$_{<\infty}$, so that all five properties are equivalent |
| Theorem 5.6 | Theorem 5.2 | Theorem 5.2.3 | 213 | same |
| Theorem 5.7 | Theorem 5.3 | Theorem 5.2.4 | 213 | same |
| Corollary 5.8 | Corollary 5.1 | Corollary 5.2.5 | 213 | same |
| — | Definition 5.6 | Definition 5.2.6 | 214 | same |
| — | Proposition 5.3 | Proposition 5.2.7 | 214 | same |
| — | Theorem 5.4 | Theorem 5.2.8 | 215 | same |
| — | Remark 5.1 | Remark 5.2.9 | 215 | same |
| — | Remark 5.2 | Remark 5.2.10 | 216 | same |
| Definition 5.9 | Definition 5.7 | Definition 5.3.1 | 216 | same |
| Proposition 5.10 | Proposition 5.4 | Proposition 5.3.2 | 216 | same |
| Lemma 5.11 | Lemma 5.3 | Lemma 5.3.3 | 217 | same |
| Remark 5.12 | Remark 5.3 | Remark 5.3.4 | 217 | same |
| Theorem 5.13 | Theorem 5.5 | Theorem 5.3.5 | 217 | changed: the solution set $S_{f+s}$ is a compact sub-M-polyfold (compactness added to the conclusion) |
| Remark 5.14 | Remark 5.4 | Remark 5.3.6 | 218 | same |
| Definition 5.15 | Definition 5.8 | Definition 5.3.7 | 218 | same |
| Remark 5.16 | Remark 5.5 | Remark 5.3.8 | 219 | same |
| Definition 5.17 | Definition 5.9 | Definition 5.3.9 | 220 | same |
| Theorem 5.18 | Theorem 5.6 | Theorem 5.3.10 | 220 | same |
| — | Remark 5.6 | Remark 5.3.11 | 222 | same |
| Theorem 5.19 | Theorem 5.7 | Theorem 5.3.12 | 222 | same |
| Definition 5.20 | Definition 5.10 | Definition 5.3.13 | 223 | changed: $t$ is an sc-smooth map with $t^{-1}(i)=X_i$ and $dt$ surjective at smooth points; the requirements that $t$ be surjective and every $X_t$ a tame M-polyfold with $f$ restricted to $X_t$ sc-Fredholm are dropped |
| Remark 5.21 | Remark 5.7 | Remark 5.3.14 | 223 | same |
| Theorem 5.22 | Theorem 5.8 | Theorem 5.3.15 | 223 | same |
| Lemma 5.23 | Lemma 5.4 | Lemma 5.3.16 | 224 | same |
| Lemma 5.24 | Lemma 5.5 | Lemma 5.3.17 | 225 | same |
| Theorem 5.25 | absent | absent | — | absent in 2017 and in 2021 (see the 2017 table above) |
| Lemma 5.26 | absent | absent | — | absent in 2017 and in 2021 (see the 2017 table above) |
| Theorem 5.27 | absent | absent | — | absent in 2017 and in 2021 (see the 2017 table above) |
| — | Definition 5.11 | Definition 5.4.1 | 228 | same |
| — | Theorem 5.9 | Theorem 5.4.2 | 228 | same |
| Definition 5.28 | Definition 5.12 | Definition 5.5.1 | 229 | same |
| Definition 5.29 | Definition 5.13 | Definition 5.5.2 | 229 | same |
| Proposition 5.30 | Proposition 5.5 | Proposition 5.5.3 | 230 | same |
| Definition 5.31 | Definition 5.14 | Definition 5.5.4 | 230 | same |
| Theorem 5.32 | Theorem 5.10 | Theorem 5.5.5 | 230 | same |
| Definition 5.33 | Definition 5.15 | Definition 5.5.6 | 231 | same |
| Theorem 5.34 | Theorem 5.11 | Theorem 5.5.7 | 231 | same |
| Proposition 5.35 | Proposition 5.6 | Proposition 5.5.8 | 231 | same |
| Definition 5.36 | Definition 5.16 | Definition 5.5.9 | 231 | same |
| Theorem 5.37 | Theorem 5.12 | Theorem 5.5.10 | 232 | same |
| Proposition 5.38 | Proposition 5.7 | Proposition 5.5.11 | 234 | same |
| Definition 5.39 | Definition 5.17 | Definition 5.5.12 | 234 | same |
| Theorem 5.40 | Theorem 5.13 | Theorem 5.5.13 | 234 | same |
| Definition 5.41 | Definition 5.18 | Definition 5.5.14 | 234 | same |
| Proposition 5.42 | Proposition 5.8 | Proposition 5.5.15 | 235 | same |
| Theorem 5.43 | Theorem 5.14 | Theorem 5.5.16 | 235 | same |
| Corollary 5.44 | Corollary 5.2 | Corollary 5.5.17 | 235 | same |

#### Chapter 6 (2021 pp. 237–286)

| Preprint 2014 | arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|---|
| Definition 6.1 | Definition 6.1 | Definition 6.2.1 | 239 | same |
| Proposition 6.2 | Proposition 6.1 | Proposition 6.2.2 | 240 | same |
| — | Remark 6.1 | Remark 6.2.3 | 240 | same |
| Definition 6.3 | Definition 6.2 | Definition 6.3.1 | 242 | same |
| Proposition 6.4 | Proposition 6.2 | Proposition 6.3.2 | 243 | same |
| Lemma 6.5 | Lemma 6.1 | Lemma 6.3.3 | 244 | same |
| — | Lemma 6.2 | Lemma 6.3.4 | 245 | same |
| Proposition 6.6 | Proposition 6.3 | Proposition 6.3.5 | 246 | same |
| Definition 6.7 | Definition 6.3 | Definition 6.4.1 | 246 | same |
| Definition 6.8 | Definition 6.4 | Definition 6.4.2 | 246 | same |
| Definition 6.9 | Definition 6.5 | Definition 6.4.3 | 247 | same |
| Lemma 6.10 | absent | absent | — | absent in 2017 and in 2021 (see the 2017 table above) |
| — | Lemma 6.3 | Lemma 6.4.4 | 247 | changed: adds $\mathrm{ind}(P\circ T)=\mathrm{ind}(T)=\mathrm{ind}(T_0)=\mathrm{ind}(P_0\circ T_0)$ to the conclusion |
| — | Remark 6.2 | Remark 6.4.5 | 247 | same |
| — | Remark 6.3 | Remark 6.4.6 | 248 | same |
| — | Lemma 6.4 | Lemma 6.4.7 | 248 | same |
| — | Definition 6.6 | Definition 6.4.8 | 248 | same |
| — | Lemma 6.5 | Lemma 6.4.9 | 249 | same |
| Lemma 6.11 | Proposition 6.4 | Proposition 6.4.10 | 249 | same |
| Proposition 6.12 | Proposition 6.5 | Proposition 6.4.11 | 251 | same |
| Corollary 6.13 | Corollary 6.1 | Corollary 6.4.12 | 251 | same |
| — | Proposition 6.6 | Proposition 6.4.13 | 253 | changed: the closed subspace $H\subset F$ of finite codimension with $\Pi_T\cap\mathcal P_H\ne\emptyset$ is now an explicit hypothesis |
| Lemma 6.14 | Lemma 6.6 | Lemma 6.4.14 | 256 | same |
| Proposition 6.15 | Proposition 6.7 | Proposition 6.4.15 | 257 | changed: hypotheses made explicit ($T$ Fredholm, $\varphi$ with $T_\varphi$ surjective); the basis is taken as $\bar c_i\in\mathbb R^n$ with $\varphi(\bar c_i)+R(T)$ a basis of $F/R(T)$ |
| Definition 6.16 | Definition 6.7 | Definition 6.4.16 | 258 | same |
| Lemma 6.17 | Lemma 6.7 | Lemma 6.5.1 | 258 | same |
| Lemma 6.18 | Lemma 6.8 | Lemma 6.5.2 | 259 | same |
| Lemma 6.19 | Lemma 6.9 | Lemma 6.5.3 | 259 | same |
| Proposition 6.20 | Proposition 6.8 | Proposition 6.5.4 | 260 | same |
| Lemma 6.21 | Lemma 6.10 | Lemma 6.5.5 | 260 | same |
| Definition 6.22 | Definition 6.8 | Definition 6.5.6 | 261 | same |
| Proposition 6.23 | Proposition 6.9 | Proposition 6.5.7 | 261 | same |
| Proposition 6.24 | Proposition 6.10 | Proposition 6.5.8 | 261 | same |
| Lemma 6.25 | Lemma 6.11 | Lemma 6.5.9 | 262 | same |
| Proposition 6.26 | Proposition 6.11 | Proposition 6.6.1 | 263 | same |
| Definition 6.27 | Definition 6.9 | Definition 6.6.2 | 263 | same |
| Proposition 6.28 | Proposition 6.12 | Proposition 6.6.3 | 263 | changed: the tameness of $X$ is stated; the sc$^+$-sections $s$, $q$ take values in $Y\times[0,1]$ |
| Lemma 6.29 | Lemma 6.12 | Lemma 6.6.4 | 265 | same |
| Lemma 6.30 | Lemma 6.13 | Lemma 6.6.5 | 265 | changed: the solution set is taken near $(t,\varphi(t),0)$ for points $(t,y,\lambda)$ (2017: $(t,y,0)$, presumably meant as in 2021) |
| Lemma 6.31 | Lemma 6.14 | Lemma 6.6.6 | 266 | same |
| Proposition 6.32 | Proposition 6.13 | Proposition 6.6.7 | 267 | same |
| Lemma 6.33 | Lemma 6.15 | Lemma 6.6.8 | 267 | changed: split in two: Lemma 6.6.8 (the extra parameters $\mu$ enter as dummy variables) and the new Lemma 6.6.9 (the extra sc$^+$-sections $\mu_j\bar s_j$) |
| Lemma 6.34 | Lemma 6.16 | Lemma 6.6.10 | 271 | same |
| Theorem 6.35 | Theorem 6.1 | Theorem 6.6.11 | 272 | same |
| Definition 6.36 | Definition 6.10 | Definition 6.6.12 | 273 | same |
| Theorem 6.37 | Theorem 6.2 | Theorem 6.6.13 | 273 | same |
| Definition 6.38 | Definition 6.11 | Definition 6.6.14 | 274 | same |
| Definition 6.39 | Definition 6.12 | Definition 6.6.15 | 274 | same |
| Definition 6.40 | Definition 6.13 | Definition 6.6.16 | 274 | same |
| Theorem 6.41 | Theorem 6.3 | Theorem 6.6.18 | 275 | same |
| Remark 6.42 | Remark 6.4 | Remark 6.6.19 | 276 | same |
| Theorem 6.43 | Theorem 6.4 | Theorem 6.7.1 | 277 | same |

#### Chapter 7 (2021 pp. 287–356)

| arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|
| Definition 7.1 | Definition 7.1.1 | 287 | same |
| Definition 7.2 | Definition 7.1.2 | 288 | same |
| Definition 7.3 | Definition 7.1.3 | 288 | same |
| Definition 7.4 | Definition 7.1.4 | 289 | same ($m_\ell$ renamed $m_I$ ("maximal index")) |
| Definition 7.5 | Definition 7.1.5 | 290 | same |
| Definition 7.6 | Definition 7.1.6 | 290 | same |
| Definition 7.7 | Definition 7.1.7 | 290 | changed: the definition is unchanged, but the remark that sc-smoothness on objects suffices now also asks for continuity (level 0) on morphisms |
| Proposition 7.1 | Proposition 7.1.8 | 291 | same |
| Proposition 7.2 | Proposition 7.1.9 | 291 | same |
| Proposition 7.3 | Proposition 7.1.10 | 292 | same |
| Lemma 7.1 | Lemma 7.1.11 | 292 | same |
| Proposition 7.4 | Proposition 7.1.12 | 293 | same |
| Theorem 7.1 | Theorem 7.1.13 | 293 | same |
| Proposition 7.5 | Proposition 7.1.15 | 297 | changed: (2) corrected to $s:U(\psi)\to U(s(\psi))$, $t:U(\psi)\to U(t(\psi))$ (2017: both to $U(y)$); adds $\psi\in U(\psi)$ and $t(\psi')=f(\psi)(s(\psi'))$ |
| Definition 7.8 | Definition 7.1.18 | 304 | same |
| Proposition 7.6 | Proposition 7.1.19 | 304 | same |
| Definition 7.9 | Definition 7.1.20 | 305 | same |
| Definition 7.10 | Definition 7.1.21 | 305 | same |
| Proposition 7.7 | Proposition 7.1.22 | 307 | same |
| Definition 7.11 | Definition 7.2.1 | 307 | same |
| Lemma 7.2 | Lemma 7.2.2 | 307 | same |
| Lemma 7.3 | Lemma 7.2.3 | 308 | same |
| Proposition 7.8 | Proposition 7.2.4 | 309 | same |
| Definition 7.12 | Definition 7.2.7 | 310 | same (adds the groupoid structure on $(X,\mathbf X^R)$) |
| Proposition 7.9 | Proposition 7.2.10 | 313 | changed: weaker conclusion: $X^R$ with the natural topology $T_R$ admits natural charts with sc-smooth transition maps; $(X^R,T_R)$ is paracompact (Prop. 7.2.12) and an M-polyfold exactly when $T_R$ is Hausdorff (Prop. 7.2.13); Remark 7.2.8 says this need not hold in general |
| Proposition 7.10 | absent | — | absent: no counterpart as stated, the content is rewritten: the reduced ep-groupoid $\mathbf X_R$ exists when $T_R$ is Hausdorff (Theorem 7.2.14, p. 318), it is effective (Proposition 7.2.16, p. 319), and $T_R$ is Hausdorff iff (LUC) iff $\mathbf X^T$ is closed (Theorem 7.2.22, p. 323) |
| Definition 7.13 | Definition 7.2.15 | 319 | same |
| Theorem 7.2 | Theorem 7.3.1 | 324 | same |
| Lemma 7.4 | Lemma 7.3.2 | 324 | same |
| Lemma 7.5 | Lemma 7.3.3 | 324 | same |
| Lemma 7.6 | Lemma 7.3.4 | 325 | same |
| Lemma 7.7 | Lemma 7.3.5 | 325 | same |
| Corollary 7.1 | Corollary 7.3.6 | 326 | same |
| Definition 7.14 | Definition 7.3.7 | 326 | same |
| Corollary 7.2 | Corollary 7.3.8 | 326 | same |
| Proposition 7.11 | Proposition 7.3.9 | 327 | same |
| Definition 7.15 | Definition 7.5.1 | 340 | same |
| Remark 7.1 | Remark 7.5.2 | 340 | same |
| Proposition 7.12 | Proposition 7.5.3 | 340 | same |
| Theorem 7.3 | Theorem 7.5.4 | 341 | same |
| Definition 7.16 | Definition 7.5.5 | 342 | same |
| Remark 7.2 | Remark 7.5.6 | 342 | same |
| Theorem 7.4 | Theorem 7.5.7 | 342 | same |
| Definition 7.17 | Definition 7.5.8 | 342 | same |
| Proposition 7.13 | Proposition 7.5.9 | 342 | same |
| Proposition 7.14 | Proposition 7.5.10 | 343 | same |
| Theorem 7.5 | Theorem 7.6.1 | 344 | same |
| Lemma 7.8 | Lemma 7.6.2 | 345 | same |
| Lemma 7.9 | Lemma 7.6.3 | 345 | same |
| Theorem 7.6 | Theorem 7.6.4 | 346 | same |
| Lemma 7.10 | Lemma 7.6.5 | 346 | same |
| Corollary 7.3 | Corollary 7.6.6 | 347 | same |

#### Chapter 8 (2021 pp. 357–400)

| arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|
| Theorem 8.1 | Theorem 8.1.1 | 359 | same (the description of $T(\mathbf X\,{}_s{\times}_t\mathbf X)$ rewritten) |
| Lemma 8.1 | Lemma 8.1.2 | 359 | same |
| Lemma 8.2 | Lemma 8.1.3 | 360 | same |
| Lemma 8.3 | Lemma 8.1.4 | 361 | same |
| Lemma 8.4 | Lemma 8.1.5 | 361 | same |
| Lemma 8.5 | Lemma 8.1.6 | 362 | same |
| Lemma 8.6 | Lemma 8.1.7 | 362 | same |
| Lemma 8.7 | Lemma 8.1.8 | 363 | same |
| Lemma 8.8 | Lemma 8.1.9 | 364 | same |
| Remark 8.1 | Remark 8.1.10 | 364 | same |
| Theorem 8.2 | Theorem 8.1.11 | 365 | same |
| Theorem 8.3 | Theorem 8.1.12 | 366 | same |
| Definition 8.1 | Definition 8.1.13 | 367 | same |
| Proposition 8.1 | Proposition 8.1.14 | 367 | same |
| Theorem 8.4 | Theorem 8.1.15 | 368 | same |
| Definition 8.2 | Definition 8.2.1 | 372 | same |
| Definition 8.3 | Definition 8.2.2 | 373 | same |
| Definition 8.4 | Definition 8.3.1 | 375 | same |
| Definition 8.5 | Definition 8.3.2 | 377 | same |
| Definition 8.6 | Definition 8.3.3 | 378 | same |
| Definition 8.7 | Definition 8.3.4 | 379 | same |
| Definition 8.8 | Definition 8.5.1 | 383 | same |
| Proposition 8.2 | Proposition 8.5.2 | 384 | same |
| Theorem 8.5 | Theorem 8.5.3 | 385 | same (statement, including (5), unchanged) |
| Remark 8.2 | Remark 8.5.4 | 386 | same |
| Definition 8.9 | Definition 8.5.5 | 388 | same |
| Proposition 8.3 | Proposition 8.5.7 | 390 | same |
| Theorem 8.6 | Theorem 8.5.8 | 392 | same (in the proof $A(\psi,z)=(f(\psi),F(z))$ (2017: $(f(z),F(z))$, presumably meant as in 2021)) |
| Definition 8.10 | Definition 8.5.9 | 394 | changed: adds (0): $\tau(F(\psi),A(w))=A(\mu(\psi,w))$, the compatibility of $A$ with the strong bundle data |
| Lemma 8.9 | Lemma 8.6.1 | 397 | same |
| Lemma 8.10 | Lemma 8.6.2 | 398 | same |
| Lemma 8.11 | Lemma 8.6.3 | 398 | same |
| Proposition 8.4 | Proposition 8.6.4 | 399 | same |

### Part III, Chapters 12–16

Part III has no preprint. The Lean names and the reports carry the 2021 numbers, with the 2017 numbers in parentheses. The tables below list, chapter by chapter in the order of the 2021 text, the numbered items of Chapters 12–16 that the Lean files formalize, with their 2017 numbers, their 2021 pages and their rows in `verification/`. The 2017 numbers were checked in the 2017 text; in particular Theorem 15.3.7 is Theorem 15.4 of 2017 (Theorem 15.6 there is the canonical orientation theorem, Theorem 15.4.1), and Theorem 15.2.5 is Theorem 15.3 of 2017. Where a Lean docstring gives another 2017 number, the last column says so. The statements were not compared word by word between 2017 and 2021, except where a row says so.

An item can have several rows, one for each part or form of it that is formalized (a sub-item, a reading, a form with the text's hypotheses). A point number in the Rows column marks an item, or a part of the form of that row, that is not formalized; "G.n closed" in the last column says that the point is settled by the declarations of the item's rows. Definitions 5.1.4–5.4.1 and Theorem 5.4.2, which Part III uses, are in the Chapter 5 table above.

Not listed are the items new in 2021 without a row of their own here (Remark 15.3.8, Lemma 16.3.2, Definition 16.6.3), the items without a number in either text and the tools: the reflexive 1-fibres, the remark after Definition 13.2.9, the locally finite commensurable sum after Definition 13.4.5, the text before Lemmas 14.2.1 and 14.3.3, the data of §§14.3–14.5, the instance of the setting of §14.4, (14.53) inside the proof of Lemma 14.5.1, the sum over $a$ in the proof of Theorem 14.1.9, the preamble of §14.6, the face good systems of §14.6, the product remark after Definition 15.3.3, the last paragraph of the proof of Corollary 15.3.10 and the parts of the proof of Corollary 15.3.10 (3), the constructions of §16.2, the remark on p. 720, the category PS, the raised polyfolds and the tangent projection, the remarks and constructions of §16.3 between numbered items, the opening of §16.5, (16.8), the claim before Definition 16.6.1 and the text before Theorem 16.6.6. They are rows V12.28, V12.40–V12.48, V13.21, V13.24, V13.56, V14.1, V14.10, V14.14, V14.38–V14.40, V14.45–V14.47, V15.10, V15.17, V15.19, V15.31, V15.39, V15.40, V15.42, V15.44, V15.46–V15.48, V15.53–V15.56, V16.14, V16.16, V16.19, V16.27, V16.29, V16.35, V16.36, V16.38, V16.40, V16.41, V16.45, V16.59, V16.60, V16.63, V16.67, V16.72, V16.75 and V16.80.

#### Chapter 12

| arXiv 2017 | Springer 2021 | p. | Rows | Note |
|---|---|---|---|---|
| Definition 12.1 | Definition 12.1.1 | 569 | V12.1, V12.2 |  |
| Definition 12.2 | Definition 12.2.1 | 570 | V12.3 |  |
| Theorem 12.1 | Theorem 12.2.2 | 570 | V12.4 |  |
| Definition 12.3 | Definition 12.2.3 | 570 | V12.5 |  |
| Definition 12.4 | Definition 12.2.4 | 571 | V12.6 |  |
| Proposition 12.1 | Proposition 12.2.5 | 571 | V12.7 |  |
| Theorem 12.2 | Theorem 12.2.6 | 571 | V12.8 |  |
| Theorem 12.3 | Theorem 12.2.7 | 574 | V12.9 |  |
| Definition 12.5 | Definition 12.2.8 | 576 | V12.29 |  |
| Remark 12.1 | Remark 12.2.9 | 576 | V12.30 |  |
| Definition 12.6 | Definition 12.2.10 | 577 | V12.31 |  |
| Theorem 12.4 | Theorem 12.2.11 | 577 | V12.32 |  |
| Remark 12.2 | Remark 12.2.12 | 577 | V12.33 |  |
| Theorem 12.5 | Theorem 12.2.13 | 578 | V12.34 |  |
| Definition 12.7 | Definition 12.3.1 | 579 | V12.10 | Lean docstring: 2017 Definition 12.6 |
| Theorem 12.6 | Theorem 12.3.2 | 579 | V12.11, V12.12 | Lean docstring: 2017 Theorem 12.4 |
| Theorem 12.7 | Theorem 12.3.3 | 581 | V12.13 | Lean docstring: 2017 Theorem 12.5 |
| Remark 12.3 | Remark 12.3.4 | 584 | V12.14 | Lean docstring: 2017 Remark 12.4 |
| Remark 12.4 | Remark 12.3.5 | 584 | V12.15 | Lean docstring: 2017 Remark 12.5 |
| Definition 12.8 | Definition 12.3.6 | 584 | V12.16 |  |
| Proposition 12.2 | Proposition 12.3.7 | 585 | V12.17 |  |
| Corollary 12.1 | Corollary 12.3.8 | 586 | V12.18 |  |
| Theorem 12.8 | Theorem 12.3.9 | 586 | V12.35 |  |
| Definition 12.9 | Definition 12.4.1 | 587 | V12.19 | Lean docstring: 2017 Definition 12.11 |
| Theorem 12.9 | Theorem 12.4.2 | 587 | V12.20 | Lean docstring: 2017 Theorem 12.6 |
| Definition 12.10 | Definition 12.4.3 | 588 | V12.36 |  |
| Lemma 12.1 | Lemma 12.4.4 | 589 | V12.21 | Lean docstring: 2017 Lemma 12.3 |
| Proposition 12.3 | Proposition 12.4.5 | 590 | V12.37 |  |
| Theorem 12.10 | Theorem 12.4.6 | 590 | V12.38 |  |
| Lemma 12.2 | Lemma 12.5.1 | 592 | V12.22 | Lin on chart-domain restrictions |
| Definition 12.11 | Definition 12.5.2 | 593 | V12.23 |  |
| Theorem 12.11 | Theorem 12.5.3 | 594 | V12.24, G.140 | tame $X$ and tame germ data; G.140 closed |
| Theorem 12.11 | Theorem 12.5.3 | 594 | V12.24 | last sentence |
| Definition 12.12 | Definition 12.5.4 | 594 | V12.25 |  |
| Definition 12.12 | Definition 12.5.4 | 594 | V12.48 | the two continuity readings agree |
| Remark 12.5 | Remark 12.5.5 | 595 | — | prose, no row |
| Proposition 12.4 | Proposition 12.5.6 | 595 | V12.26 |  |
| Proposition 12.4 | Proposition 12.5.6 | 595 | V12.26 | (⇐) with continuity |
| Theorem 12.12 | Theorem 12.5.7 | 595 | V12.39 |  |
| Theorem 12.12 | Theorem 12.5.7 | 595 | V12.39, G.158 | (2) with continuity; G.158 closed |
| Theorem 12.12 | Theorem 12.5.7 | 595 | V12.39, V12.47, G.192 | as printed, for classes of diagrams; G.158, G.192 closed |
| Theorem 12.12 | Theorem 12.5.7 | 595 | V12.39, G.140 | tame $X$ and tame germ data; G.140 closed |

#### Chapter 13

| arXiv 2017 | Springer 2021 | p. | Rows | Note |
|---|---|---|---|---|
| Lemma 13.1 | Lemma 13.1.1 | 599 | V13.1 |  |
| Definition 13.1 | Definition 13.1.2 | 600 | V13.2 |  |
| Proposition 13.1 | Proposition 13.1.3 | 600 | V13.3 |  |
| Definition 13.2 | Definition 13.1.4 | 600 | V13.4 |  |
| Definition 13.3 | Definition 13.1.5 | 601 | V13.5 |  |
| Lemma 13.2 | Lemma 13.1.6 | 602 | V13.6 |  |
| Theorem 13.1 | Theorem 13.1.7 | 602 | V13.7 |  |
| Theorem 13.2 | Theorem 13.1.8 | 604 | V13.8 |  |
| Proposition 13.2 | Proposition 13.1.9 | 607 | V13.9 |  |
| Definition 13.4 | Definition 13.2.1 | 607 | (Chapter 11) | the Lean docstrings give other 2017 numbers for §13.2 |
| Definition 13.5 | Definition 13.2.2 | 608 | V13.10 |  |
| Definition 13.6 | Definition 13.2.3 | 608 | V13.11 |  |
| Definition 13.7 | Definition 13.2.4 | 609 | V13.12 |  |
| Definition 13.8 | Definition 13.2.5 | 610 | V13.13 |  |
| Lemma 13.3 | Lemma 13.2.6 | 610 | V13.14 |  |
| Definition 13.9 | Definition 13.2.7 | 610 | V13.22 | G.142 closed |
| Definition 13.10 | Definition 13.2.8 | 611 | V13.23 | G.142 closed |
| Definition 13.11 | Definition 13.2.9 | 611 | V13.15 |  |
| Definition 13.12 | Definition 13.2.10 | 611 | V13.16 |  |
| Lemma 13.4 | Lemma 13.2.11 | 612 | V13.17 |  |
| Definition 13.13 | Definition 13.2.12 | 612 | V13.18 |  |
| Lemma 13.5 | Lemma 13.2.13 | 612 | V13.19 |  |
| Definition 13.14 | Definition 13.3.1 | 613 | V13.25 |  |
| Definition 13.15 | Definition 13.3.2 | 614 | V13.26 |  |
| Example 13.1 | Example 13.3.3 | 614 | V13.27 |  |
| Definition 13.16 | Definition 13.3.4 | 614 | V13.28 |  |
| Remark 13.1 | Remark 13.3.5 | 615 | V13.29 |  |
| Definition 13.17 | Definition 13.3.6 | 615 | V13.30 |  |
| Remark 13.2 | Remark 13.3.7 | 616 | V13.31 |  |
| Definition 13.18 | Definition 13.3.8 | 616 | V13.32 |  |
| Remark 13.3 | Remark 13.3.9 | 616 | V13.33 |  |
| Definition 13.19 | Definition 13.3.10 | 616 | V13.34 |  |
| Definition 13.20 | Definition 13.3.11 | 617 | V13.35 |  |
| Proposition 13.3 | Proposition 13.3.12 | 617 | V13.36 |  |
| Remark 13.4 | Remark 13.3.13 | 618 | V13.37 |  |
| Lemma 13.6 | Lemma 13.3.14 | 618 | V13.38 |  |
| Proposition 13.4 | Proposition 13.3.15 | 619 | V13.39, V13.40 |  |
| Remark 13.5 | Remark 13.3.16 | 619 | V13.41 |  |
| Definition 13.21 | Definition 13.3.17 | 620 | V13.42 |  |
| Corollary 13.1 | Corollary 13.3.18 | 620 | V13.43 |  |
| Proposition 13.5 | Proposition 13.3.19 | 620 | V13.50 | G.148 closed |
| Proposition 13.5 | Proposition 13.3.19 | 620 | V13.50 |  |
| Theorem 13.3 | Theorem 13.4.1 | 621 | V13.51 |  |
| Proposition 13.6 | Proposition 13.4.2 | 623 | G.163 | G.163 closed |
| Proposition 13.6 | Proposition 13.4.2 | 623 | V13.59 | G.163 closed |
| Theorem 13.4 | Theorem 13.4.3 | 625 | V13.52 |  |
| Theorem 13.5 | Theorem 13.4.4 | 626 | V13.53 |  |
| Definition 13.22 (1) | Definition 13.4.5 (1) | 628 | V13.54 |  |
| Definition 13.22 (2) | Definition 13.4.5 (2) | 628 | V13.55 |  |
| Definition 13.23 | Definition 13.5.1 | 629 | V13.44 |  |
| Definition 13.23 | Definition 13.5.1 | 629 | V13.57 |  |
| Remark 13.6 | Remark 13.5.2 | 630 | V13.45 |  |
| Theorem 13.6 | Theorem 13.5.3 | 630 | V13.46 |  |
| Theorem 13.7 | Theorem 13.5.4 | 632 | V13.47 |  |
| Theorem 13.8 | Theorem 13.5.5 | 633 | V13.48 |  |
| Theorem 13.9 | Theorem 13.5.6 | 634 | V13.49 |  |
| Theorem 13.10 | Theorem 13.5.7 | 635 | V13.58 |  |

#### Chapter 14

| arXiv 2017 | Springer 2021 | p. | Rows | Note |
|---|---|---|---|---|
| Definition 14.1 | Definition 14.1.2 | 641 | V14.2 |  |
| after Definition 14.1 | remark after Definition 14.1.2 | 641 | V14.36 | G.165 closed |
| Definition 14.2 | Definition 14.1.3 | 642 | V14.3 |  |
| Definition 14.2 | Definition 14.1.3 | 642 | V14.3, G.186 | $I_x \ne \emptyset$ in the definition; G.186 closed |
| Remark 14.2 | Proposition 14.1.4 | 642 | V14.4 |  |
| Definition 14.3 | Definition 14.1.5 | 643 | V14.5 |  |
| Theorem 14.1 | Theorem 14.1.6 | 643 | V14.6 |  |
| Definition 14.4 | Definition 14.1.7 | 644 | V14.7 |  |
| Proposition 14.1 | Proposition 14.1.8 | 645 | G.164 | G.164 closed |
| Proposition 14.1 | Proposition 14.1.8 | 645 | V14.44, G.164 | face condition named; G.164 closed |
| Proposition 14.1 | Proposition 14.1.8 | 645 | V14.44 | stronger; G.164 closed |
| Theorem 14.2 | Theorem 14.1.9 | 646 | V14.8 | as printed |
| Theorem 14.2 | Theorem 14.1.9 | 646 | V14.8, G.171 | from `AssemblyHyp`; G.171 closed |
| Theorem 14.2 | Theorem 14.1.9 | 646 | V14.8, V14.46, G.186 | `hB` from tameness; G.171, G.186 closed |
| Remark 14.3 | Remark 14.1.10 | 646 | V14.9 |  |
| Lemma 14.1 | Lemma 14.2.2 | 648 | V14.11 |  |
| Proposition 14.2 | Proposition 14.2.3 | 649 | V14.12 |  |
| Lemma 14.2 | Lemma 14.3.1 | 650 | V14.13 |  |
| Lemma 14.3 | Lemma 14.3.3 | 651 | V14.15 |  |
| Proposition 14.3 | Proposition 14.3.4 | 652 | V14.16 |  |
| Remark 14.4 | Remark 14.3.5 | 653 | V14.17 |  |
| Lemma 14.4 | Lemma 14.3.6 | 654 | V14.18 |  |
| Lemma 14.5 | Lemma 14.3.7 | 655 | V14.19 |  |
| Proposition 14.4 | Proposition 14.3.8 | 656 | V14.20 |  |
| Remark 14.5 | Remark 14.4.1 | 658 | V14.21 |  |
| Definitions 14.5, 14.6 | Definitions 14.4.2 and 14.4.3 | 659 | V14.22 |  |
| Definition 14.7 | Definition 14.4.4 | 660 | V14.23 |  |
| Lemma 14.6 | Lemma 14.4.5 | 660 | V14.24 |  |
| Proposition 14.5 | Proposition 14.4.6 | 661 | V14.25 |  |
| Proposition 14.5 | Proposition 14.4.6 | 661 | V14.25 | (2) proved; G.168 closed |
| Lemma 14.7 | Lemma 14.4.7 | 661 | V14.26 |  |
| Definition 14.8 | Definition 14.4.8 | 663 | V14.27 |  |
| Lemma 14.8 | Lemma 14.4.9 | 663 | V14.28 |  |
| Proposition 14.6 | Proposition 14.4.10 | 664 | V14.29 |  |
| Definition 14.9 | Definition 14.4.11 | 664 | V14.30 |  |
| Remark 14.6 | Remark 14.4.12 | 664 | V14.31 |  |
| Lemma 14.9 | Lemma 14.4.13 | 666 | V14.32 |  |
| Proposition 14.7 | Proposition 14.4.14 | 667 | V14.33 |  |
| Lemma 14.10 | Lemma 14.5.1 | 671 | V14.34 |  |
| Lemma 14.10 | Lemma 14.5.1, (14.53) | 671 | V14.34, V14.45 | (14.53) for the $\hat V_a$ |
| Lemma 14.11 | Lemma 14.5.2 | 672 | V14.48, G.172 | multisection form; G.172 closed |
| Lemma 14.11 | Lemma 14.5.2 | 672 | V14.38, G.172 | sum identity for the sections |
| Remark 14.7 | Remark 14.5.3 | 672 | V14.48, G.172 | G.172 closed |
| Proposition 14.8 | Proposition 14.5.4 | 673 | G.170 | statement formalized; G.170 closed |
| Proposition 14.8 | Proposition 14.5.4 | 673 | V14.37 | G.170 closed |
| Theorem 14.3 | Theorem 14.5.5 | 678 | V14.35 |  |
| §14.6 | §14.6 | 680 | V14.47, G.185 | good systems on a face; G.185 closed |
| Definition 14.10 | Definition 14.6.1 | 681 | G.173 |  |
| Definition 14.10 | Definition 14.6.1 | 681 | V14.41, G.184 | G.184 closed |
| Definition 14.10 | Definition 14.6.1 | 681 | V14.41 | corner sc⁺; G.184 closed |
| Definition 14.11 | Definition 14.6.2 | 681 | V14.42, G.173 | with the sections in the equivalence; G.173 closed |
| Definition 14.11 | Definition 14.6.2 | 681 | V14.42 |  |
| Theorem 14.4 | Theorem 14.6.3 | 682 | V14.43, G.173 | Definition 13.3.8 as printed: does not hold as we read it; G.173 closed |
| Theorem 14.4 | Theorem 14.6.3 | 682 | V14.43, G.173 | section-compatible face data |
| Theorem 14.4 | Theorem 14.6.3 | 682 | V14.43, G.173 | extension part |

#### Chapter 15

| arXiv 2017 | Springer 2021 | p. | Rows | Note |
|---|---|---|---|---|
| Theorem 15.1 | Theorem 15.1.1 | 684 | V15.2, V15.9 |  |
| Remark 15.1 | Remark 15.1.2 | 684 | V15.3 |  |
| Proposition 15.1 | Proposition 15.1.3 | 684 | V15.4 |  |
| Lemma 15.1 | Lemma 15.1.4 | 685 | V15.5 |  |
| Lemma 15.2 | Lemma 15.1.5 | 685 | V15.6 |  |
| — | Remark 15.1.6 | 686 | V15.7 | new in 2021 |
| Definition 15.1 | Definition 15.1.7 | 687 | V15.8 |  |
| Definition 15.2 | Definition 15.2.1 | 688 | V15.11 |  |
| Theorem 15.2 | Theorem 15.2.2 | 688 | V15.12 |  |
| Remark 15.2 | Remark 15.2.3 | 689 | V15.13 |  |
| Remark 15.2 | Remark 15.2.3 | 689 | V15.13 | tame; the ep-groupoid $U(x)$ |
| Definition 15.3 | Definition 15.2.4 | 689 | V15.14 |  |
| Theorem 15.3 | Theorem 15.2.5 | 690 | V15.15 |  |
| Theorem 15.3 | Theorem 15.2.5 | 690 | V15.15, V15.43 | tame |
| Remark 15.3 | Remark 15.2.6 | 690 | V15.16 |  |
| Definition 15.4 | Definition 15.3.1 | 691 | V15.20 |  |
| Remark 15.4 | Remark 15.3.2 | 692 | V15.21 |  |
| Definition 15.5 | Definition 15.3.3 | 692 | V15.22, V15.23 |  |
| after Definition 15.5 | remark after Definition 15.3.3 | 692 | V15.53–V15.57, G.160 | products; G.160 closed |
| Remark 15.5 | Remark 15.3.4 | 692 | V15.57, G.160 | G.160 closed |
| Definition 15.6 | Definition 15.3.5 | 693 | V15.24, V15.58 | along equivalences (V15.58) |
| Remark 15.6 | Remark 15.3.6 | 693 | V15.25, V15.27, V15.28 | G.161 closed |
| Remark 15.6 | Remark 15.3.6 | 693 | V15.27, V15.28 |  |
| Remark 15.6 | Remark 15.3.6 | 693 | V15.28 | tame |
| Theorem 15.4 | Theorem 15.3.7 | 694 | V15.29, V15.30; G.162 | G.162 closed |
| Theorem 15.4 | Theorem 15.3.7 | 693 | V15.29, V15.30 |  |
| Theorem 15.4 | Theorem 15.3.7 | 693 | V15.29, V15.30, V15.39 | not 2017 Theorem 15.6 |
| Theorem 15.4 | Theorem 15.3.7 | 693 | V15.29, V15.44 | text's hypotheses |
| Theorem 15.5 | Theorem 15.3.9 | 698 | V15.32; G.177–G.179 | G.177–G.179 closed |
| Theorem 15.5 | Theorem 15.3.9 | 698 | V15.32 |  |
| Theorem 15.5 | Theorem 15.3.9 | 698 | V15.32, V15.41 | step (a) |
| Theorem 15.5 | Theorem 15.3.9 | 698 | V15.32, V15.45, G.178, G.179 | text's hypotheses; witness with boundary |
| Corollary 15.1 | Corollary 15.3.10 | 699 | V15.18, V15.26, V15.33, V15.34; G.180, G.181, G.183 | G.180, G.181, G.183 closed |
| Corollary 15.1 (1) | Corollary 15.3.10 (1) | 699 | V15.33 | hypotheses of Theorem 15.3.7 |
| Corollary 15.1 (3) | Corollary 15.3.10 (3) | 699 | V15.34 | from bump functions |
| Corollary 15.1 | Corollary 15.3.10 | 699 | V15.33, V15.34, V15.40, V15.42 |  |
| Corollary 15.1 | Corollary 15.3.10 | 699 | V15.33, V15.34, V15.46–V15.48, G.180, G.189, G.190, G.193 | (1), (3); G.180, G.181, G.189, G.190, G.193 closed |
| Remark 15.7 | Remark 15.3.11 | 699 | V15.35 |  |
| before Theorem 15.6 | before Theorem 15.4.1 | 701 | V15.50 | at a chart point |
| Theorem 15.6 | Theorem 15.4.1 | 700 | V15.51, G.159 | in $\widehat{Gr}(X)$; G.159 closed |
| Theorem 15.6 | Theorem 15.4.1 | 702 | V15.51, G.159 | at a chart point |
| Definition 15.7 | Definition 15.4.2 | 700 | V15.52, G.159 | G.159 closed |
| Definition 15.7 | Definition 15.4.2 | 702 | V15.52, G.159 | pointwise |
| Theorem 15.7 | Theorem 15.4.3 | 702 | V15.36 | canonical orientation |
| Corollary 15.2 | Corollary 15.4.4 | 703 | V15.37, V15.49 | canonical orientations; `hinvC` (G.182) |
| Corollary 15.2 | Corollary 15.4.4 | 703 | V15.37, V15.49, G.182, G.191 | cylinder argument; effective; G.191 closed |
| Remark 15.8 | Remark 15.4.5 | 703 | V15.38 |  |

#### Chapter 16

| arXiv 2017 | Springer 2021 | p. | Rows | Note |
|---|---|---|---|---|
| Definition 16.1 | Definition 16.1.1 | 705 | V16.1 | 2021 adds (ZHOU) and paracompactness |
| Proposition 16.1 | remark after Definition 16.1.1 | 706 | V16.14 | numbered in 2017, prose in 2021; G.146 closed |
| Definition 16.2 | Definition 16.1.2 | 707 | V16.2, V16.3 | 2021 adds "as a consequence of (ZHOU)" |
| Definition 16.3 | Definition 16.1.3 | 707 | V16.4 |  |
| Proposition 16.2 | Proposition 16.1.4 | 708 | V16.5 |  |
| Definition 16.4 | Definition 16.1.5 | 708 | V16.6 |  |
| Definition 16.5 | Definition 16.1.6 | 710 | V16.30 |  |
| Remark 16.1 | Remark 16.1.7 | 711 | V16.7 |  |
| Definition 16.6, Remark 16.2 | Definition 16.1.8 and Remark 16.1.9 | 711 | V16.31 |  |
| Definition 16.7 | Definition 16.1.10 | 711 | V16.32 |  |
| Definition 16.8 | Definition 16.1.11 | 711 | V16.33 |  |
| Lemma 16.1 | Lemma 16.1.13 | 712 | V16.8 |  |
| Definition 16.9 | Definition 16.1.14 | 712 | V16.9 |  |
| Definition 16.11 | Definition 16.1.17 | 713 | V16.10 |  |
| Lemma 16.2 | Lemma 16.1.19 | 714 | V16.11 |  |
| Definition 16.12 | Definition 16.1.20 | 714 | V16.12 |  |
| Lemma 16.3 | Lemma 16.2.1 | 716 | V16.15 |  |
| Lemma 16.4 | Lemma 16.2.2 | 718 | V16.17 |  |
| Definition 16.14 | Definition 16.2.3 | 719 | V16.18 |  |
| Theorem 16.1 | Theorem 16.2.4 | 719 | V16.34; G.157 | G.157 closed |
| Theorem 16.1 | Theorem 16.2.4 | 719 | V16.34 |  |
| Theorem 16.1 | Theorem 16.2.4 | 719 | V16.34 | functor on effective polyfolds |
| Definition 16.15 | Definition 16.2.5 | 720 | V16.20 |  |
| Theorem 16.2 | Theorem 16.2.6 | 721 | V16.21 | pull-back |
| Definition 16.16 | Definition 16.3.1 | 721 | V16.37 |  |
| Definition 16.17 | Definition 16.3.3 | 722 | V16.39 |  |
| Definition 16.18 | Definition 16.3.4 | 723 | V16.42 |  |
| Definition 16.19 | Definition 16.3.5 | 723 | V16.43 |  |
| Definition 16.20 | Definition 16.3.6 | 724 | V16.44 |  |
| Definition 16.21 | Definition 16.3.7 | 725 | V16.46 |  |
| Definition 16.22 | Definition 16.3.8 | 726 | V16.47 |  |
| Definition 16.23 | Definition 16.3.9 | 726 | V16.48 |  |
| Proposition 16.4 | Proposition 16.3.10 | 726 | V16.49 |  |
| Remark 16.4 | Remark 16.3.11 | 727 | V16.50 |  |
| Definition 16.24 | Definition 16.3.12 | 727 | V16.51 |  |
| Definition 16.24 | Definition 16.3.12 | 727 | V16.51, V16.79 | parenthetical, pull direction |
| Definition 16.24 | Definition 16.3.12 | 727 | V16.51, V16.79 | both directions; G.166 closed |
| Definition 16.25 | Definition 16.3.13 | 727 | V16.52 |  |
| Definition 16.26 | Definition 16.3.14 | 727 | V16.53 |  |
| Definition 16.26 | Definition 16.3.14 | 727 | V16.53 | independent of the model |
| Theorem 16.3 | Theorem 16.3.15 | 727 | V16.54 |  |
| Proposition 16.5 | Proposition 16.3.16 (1) | 727 | V16.55 |  |
| Proposition 16.5 | Proposition 16.3.16 (2) | 728 | V16.56 |  |
| Proposition 16.5 | Proposition 16.3.16 (2) | 728 | V16.56 | as stated |
| Theorem 16.4 | Theorem 16.3.17 (1) | 728 | V16.57 |  |
| Theorem 16.4 | Theorem 16.3.17 (2) | 728 | V16.58 |  |
| Definition 16.27 | Definition 16.3.18 | 729 | V16.61 |  |
| Definitions 16.27, 16.28 | Definitions 16.3.18, 16.3.19 | 729 | V16.81 | zero section; G.167 closed |
| Definition 16.28 | Definition 16.3.19 | 729 | V16.62 |  |
| Definition 16.29 | Definition 16.4.1 | 730 | V16.22 |  |
| Definition 16.30 | Definition 16.4.2 | 730 | V16.23 |  |
| Proposition 16.6 | Proposition 16.4.3 | 730 | V16.24 |  |
| Proposition 16.6 | Proposition 16.4.3 | 730 | V16.24 | naturality |
| Definition 16.31 | Definition 16.4.4 | 730 | V16.25 |  |
| Definition 16.34 | Definition 16.4.5 | 731 | V16.26 |  |
| Theorem 16.5 | Theorem 16.4.6 | 732 | V16.28, G.153 | as printed from Stokes on the ep-groupoid level (Remark 9.5.19, the text's open question) |
| §16.4 (running text) | the integrals on p. 732 in dimension 0 | 732 | V16.83 | Definition 9.5.6 for $n = 0$ |
| Definition 16.35 | Definition 16.5.1 | 733 | V16.64 |  |
| Definition 16.36 | Definition 16.5.2 | 733 | V16.65 |  |
| Remark 16.5 | Remark 16.5.3 | 733 | V16.66 |  |
| Definition 16.37 | Definition 16.5.4 | 734 | V16.68 |  |
| Definition 16.38 | Definition 16.5.5 | 734 | V16.69 |  |
| Definition 16.39 | Definition 16.5.6 | 734 | V16.70 |  |
| Theorem 16.6 | Theorem 16.5.7 | 735 | V16.71 |  |
| Theorem 16.6 | Theorem 16.5.7 | 735 | V16.71 | as printed |
| Definition 16.40 | Definition 16.6.1 | 736 | V16.73 |  |
| Definition 16.41 | Definition 16.6.2 | 736 | V16.74 |  |
| Theorem 16.7 | Theorem 16.6.4 | 737 | V16.76 |  |
| Definition 16.42 | Definition 16.6.5 | 739 | V16.77 |  |
| Definition 16.42 | Definition 16.6.5 | 739 | V16.77, G.176 | independent of the representative; G.176 closed |
| Theorem 16.8 | Theorem 16.6.6 | 739 | V16.78 |  |
| Theorem 16.8 | Theorem 16.6.6 | 739 | V16.78, V16.80, G.175, G.187 | integrals well defined; general position in one model (G.187 closed) |
| Theorem 16.8 | Theorem 16.6.6 | 739 | V16.82, G.188 | Fredholm index 0 (G.188 closed) |

### Items of the 2021 text without a 2017 counterpart

Listed by section with a one-line paraphrase (the item's number and page in the 2021 text); "2017: running text" means the content is in the 2017 text but not as a numbered item.

**Chapter 1** (1 items)

- §1.1
  - Remark 1.1.2 (p. 5): Banach space means Banachable space; all complete norms are equivalent

**Chapter 2** (37 items)

- §2.1 Retractions and Retracts
  - Proposition 2.1.4 (p. 22): every point of an sc-smooth retract has neighbourhoods $V\subset W$ with $\mathrm{cl}(V)\subset W$ and the level-0 metric complete on $\mathrm{cl}(V)$ (running text in 2017)
  - Definition 2.1.5 (p. 23): locally complete Hausdorff space
  - Remark 2.1.6 (p. 23): the "global" aspect of local completeness
  - Corollary 2.1.7 (p. 23): an sc-smooth retract (level 0) is locally complete
  - Proposition 2.1.8 (p. 24): permanence of local completeness (locally closed subspaces, homeomorphic images, open subsets, locally finite closed covers)
  - Lemma 2.1.9 (p. 25): a locally complete Hausdorff space has countable neighbourhood bases
  - Proposition 2.1.10 (p. 25): a locally complete Hausdorff space is completely regular
  - Remark 2.1.17 (p. 30): the tangent of a retract and of a morphism; tangent bundle of a retract
- §2.2 Some Basic Properties of Sc-Smooth Retracts (new section)
  - Lemma 2.2.1 (p. 30): for connected relatively open $U\subset C$ every level $U_k$ is path-connected
  - Lemma 2.2.2 (p. 31): neighbourhoods $W(x)=V(x)\cap r^{-1}(V(x))$ of $x\in O$ inside $C$ and their intersection with $O$
  - Definition 2.2.3 (p. 32): locally path-connected topological space
  - Theorem 2.2.4 (p. 32): an sc-smooth retract is locally path-connected
  - Definition 2.2.5 (p. 33): almost locally contractible space
  - Proposition 2.2.6 (p. 33): an sc-smooth retract is almost locally contractible
- §2.3 M-Polyfolds and Sub-M-Polyfolds
  - Lemma 2.3.5 (p. 35): every point of an M-polyfold has arbitrarily small neighbourhoods $V$ with $\mathrm{cl}(V)\subset W$
  - Proposition 2.3.6 (p. 36): every M-polyfold is locally complete (local completeness, wording of the 2017 text before Theorem 2.2)
  - Proposition 2.3.7 (p. 36): every M-polyfold is locally path-connected
  - Remark 2.3.11 (p. 38): $TX\to X^1$ is called the tangent but is a bundle over $X^1$, not over $X$ (2017: running text)
  - Remark 2.3.13 (p. 38): identification of $T_xO$ with $\{x\}\times Dr(x)E$ (2017: running text)
  - Theorem 2.3.16 (p. 40): the tangent bundle $TX\to X^1$ of an M-polyfold is a well-defined M-polyfold bundle (2017: running text after Proposition 2.5)
  - Proposition 2.3.17 (p. 42): $(TX)^i$ is naturally identified with $T(X^i)$, also as bundles
- §2.4 The Degeneracy Index
  - Remark 2.4.2 (p. 44): the degeneracy index measures the corner complexity; the example of the diagonal in $[0,\infty)^3$
- §2.5 Tame M-polyfolds
  - Definition 2.5.18 (p. 62): a sub-M-polyfold has a tame induced structure if it has an equivalent atlas with tame models only
  - Definition 2.5.19 (p. 63): sub-M-polyfold $Y$ of a tame $X$ with retractions $r$ satisfying $r(V)=Y\cap V$ and $d_X\circ r=d_X$ (a tame sub-M-polyfold)
- §2.7 Appendix (2.7.2 and 2.7.4 Formalism Associated to a Boundary with Corners: the tame boundary $bX$)
  - Lemma 2.7.2 (p. 72): regular Hausdorff space: neighbourhoods $V(x)$ with $\mathrm{cl}(V(x))\subset U(x)$ (the T3 reformulation used for Theorem 2.7.1)
  - Proposition 2.7.5 (p. 78): refines 2017 Proposition 2.12: a neighbourhood $V$ with $d_X(y)\le d_X(x)$ and $y$ in exactly $d_X(y)$ faces of $V$, and a smaller $U(x)$ such that every face of $V$ meeting $U(x)$ contains $x$ (the last claim goes beyond what 2.5.14 states)
  - Definition 2.7.6 (p. 79): face-structured open subsets; collections $\mathcal N_X^{\mathrm{all}}\supset\mathcal N_X$
  - Proposition 2.7.7 (p. 80): $\mathcal N_{X,x}\neq\emptyset$, $\mathcal N_X$ is an open covering closed under non-empty open subsets and intersections
  - Definition 2.7.8 (p. 80): local boundary structure category $L_X$
  - Definition 2.7.9 (p. 81): boundary structure functor $F_X:L_X\to\mathrm{SET}$
  - Definition 2.7.10 (p. 81): admissible boundary triples $(x,V,\theta)$ and their equivalence; the set $bX$
  - Definition 2.7.11 (p. 82): the sets $U(x,V,\theta)\subset bX$ and the bijections to the faces $\theta$
  - Proposition 2.7.12 (p. 83): the transition maps between these bijections are homeomorphisms/sc-smooth (charts on $bX$)
  - Theorem 2.7.13 (p. 83): $bX$ has a natural metrizable topology and a natural tame M-polyfold structure; $B:bX\to X$ is sc-smooth
  - Definition 2.7.14 (p. 84): the tame boundary $B:bX\to X$ of a tame M-polyfold
  - Lemma 2.7.15 (p. 85): the sets $U(x,V,\theta)$ generate a topology $T_{bX}$ on $bX$
  - Proposition 2.7.16 (p. 85): $T_{bX}$ is metrizable

**Chapter 3** (7 items)

- §3.5 The Geometry of Basic Germs
  - Remark 3.5.4 (p. 123): recollection preceding the proof of Corollary 3.5.3
  - Remark 3.5.7 (p. 127): role of Theorem 3.5.6: after a coordinate change the solution set is a graph; Theorem 3.5.11 gives the graph for $f$ itself
- §3.8.1 Proof of Proposition 3.1.25 (cones and partial quadrants)
  - Lemma 3.8.4 (p. 147): for $N\subset E$ in good position and $N\cap C$ a closed convex cone: components of $y\in N^\perp$ vanish on indices of extreme-ray generators; $\Gamma$ is the union of the supports
  - Lemma 3.8.5 (p. 147): dichotomy: $N\subset\{0\}_\Gamma\oplus\mathbb R^{\Gamma^c}\oplus W$ (then $\dim N=1$) or $N\cap(\ldots)=\{0\}$
  - Lemma 3.8.6 (p. 148): the map $P:N\to\mathbb R^\Gamma$ is an isomorphism carrying $N\cap C$ onto the quadrant $Q_\Gamma$ (and the second case)
  - Corollary 3.8.7 (p. 149): $N$ in good position and $N\cap C$ a closed convex cone imply $N\cap C$ is a partial quadrant in $N$
- §3.8.5
  - Remark 3.8.16 (p. 165): Theorem 3.8.15 holds with $C^j$, $j\ge1$, after adjusting Proposition 3.8.17

**Chapter 4** (6 items)

- §4.4 Sc-Differential Forms
  - Definition 4.4.2 (p. 195): $\Omega^*_\infty(X)$, sc-differential forms on $X_\infty$ (2017: part of Definition 4.9)
  - Definition 4.4.3 (p. 195): sc-smooth vector fields are sections of $TX\to X^1$, defined on $X^1$
  - Lemma 4.4.4 (p. 196): raising the index of a vector field $A$ to $A^{(i)}$ on $X^i$
  - Lemma 4.4.8 (p. 199): Poincar\'e lemma for sc-differential forms on M-polyfolds (2017: "formulated and proved in [39]")
- §4.5 Appendix (new): 4.5.1 Definition of the Lie Bracket, 4.5.2 Proof of Proposition 4.4.5, 4.5.3 Proof of the Poincar\'e Lemma
  - Lemma 4.5.1 (p. 201): the Lie bracket is natural under local sc-diffeomorphisms
  - Lemma 4.5.2 (p. 202): sc-Poincar\'e lemma on a convex neighbourhood of $0$ in $[0,\infty)^n\oplus W$

**Chapter 6** (2 items)

- §6.6 Local Orientation Propagation
  - Lemma 6.6.9 (p. 269): second half of 2017 Lemma 6.15: adding sc$^+$-sections $\mu_j\bar s_j$ does not change the propagation of orientation
  - Theorem 6.6.17 (p. 275): the orientation space $O_f$ carries a unique Hausdorff topology with prescribed properties (not in 2017: its Definition 6.13 defines orientations, with no topology on $O_f$)

**Chapter 7** (46 items)

- §7.1 Ep-Groupoids and Basic Properties
  - Proposition 7.1.14 (p. 296): in the proof of the natural representation: $\Gamma(g,v)=s_g^{-1}(v)$, $\Phi(g)=t_g\circ s_g^{-1}$ on a $\Phi$-invariant neighbourhood
  - Lemma 7.1.16 (p. 300): a sequence in $\mathbf U(\psi)$ whose source or target converges in $U(s(\psi))$ or $U(t(\psi))$ has its limit in $\mathbf U(\psi)$
  - Corollary 7.1.17 (p. 301): properties (4)-(6) of the construction in Proposition 7.1.15 (equivariance of $f$ for isotropy and morphisms)
- §7.2 Effective and Reduced Ep-Groupoids (rewritten)
  - Definition 7.2.5 (p. 310): the normal subgroup $T_x\subset G_x$ of elements acting trivially near $x$
  - Lemma 7.2.6 (p. 310): $a:T_x\to G_y$, $g\mapsto\varphi g\varphi^{-1}$, is an isomorphism onto $T_y$
  - Remark 7.2.8 (p. 311): $\mathbf X^R$ is in general not an M-polyfold; it is when $T_R$ is Hausdorff
  - Lemma 7.2.9 (p. 311): $\pi:\mathbf X\to\mathbf X^R$ is open; local homeomorphisms $\mathbf U(\varphi_0)\to\mathbf U([\varphi_0])$
  - Lemma 7.2.11 (p. 315): disjoint neighbourhoods $\mathbf U(\varphi_i)$ of the equivalent morphisms with common image $\mathbf U([\varphi_0])$
  - Proposition 7.2.12 (p. 317): $(\mathbf X^R,T_R)$ is paracompact
  - Proposition 7.2.13 (p. 318): the natural charts define an M-polyfold structure on $(\mathbf X^R,T_R)$ iff $T_R$ is Hausdorff
  - Theorem 7.2.14 (p. 318): ep-groupoid criterion: if $T_R$ is Hausdorff then $(X,\mathbf X^R)$ is an ep-groupoid (replaces 2017 Proposition 7.10)
  - Proposition 7.2.16 (p. 319): the reduced ep-groupoid $\mathbf X_R$ (with $T_R$ Hausdorff) is effective
  - Proposition 7.2.17 (p. 320): $T_R$ Hausdorff iff $\mathbf X^T$ is closed in $\mathbf X$
  - Definition 7.2.18 (p. 321): local unique continuation property (LUC)
  - Remark 7.2.19 (p. 321): not every ep-groupoid has (LUC); example of Zhengyi Zhou in Appendix 7.6.3
  - Remark 7.2.20 (p. 321): the neighbourhood $U(x)$ in (LUC) can be chosen arbitrarily small
  - Proposition 7.2.21 (p. 321): (LUC) iff $\mathbf X^T$ is closed
  - Theorem 7.2.22 (p. 323): $T_R$ Hausdorff iff (LUC) iff $\mathbf X^T$ closed
  - Proposition 7.2.23 (p. 323): under (LUC) (or the two equivalent properties) the reduced ep-groupoid $\mathbf X_R$ is well defined
- §7.4 Regularity Assumptions and the Zhou Condition (new section)
  - Definition 7.4.1 (p. 328): (LUC) again (as Definition 7.2.18)
  - Proposition 7.4.2 (p. 328): (LUC) passes to larger connected invariant neighbourhoods
  - Remark 7.4.3 (p. 329): under (LUC) every connected $G_x$-invariant neighbourhood $U(x)$, small or large, has the continuation property
  - Lemma 7.4.4 (p. 329): (LUC) for $\mathbf X^i$ implies (LUC) for $\mathbf X^k$, $k\le i$
  - Definition 7.4.5 (p. 331): Zhou condition (ZHOU): $Tg=\mathrm{id}$ on $T_xX$ implies $g\in T_x$, for smooth $x$
  - Lemma 7.4.6 (p. 331): (ZHOU) with $Tg=\mathrm{id}$ on $(T_xX)_\infty$ gives $g\in T_x^\infty$
  - Definition 7.4.7 (p. 331): alternative Zhou condition (ZHOU')
  - Proposition 7.4.8 (p. 332): (ZHOU) and (ZHOU') are equivalent
  - Proposition 7.4.9 (p. 333): (ZHOU) for $\mathbf X$ implies (ZHOU) for every $\mathbf X^i$
  - Proposition 7.4.10 (p. 333): (ZHOU) implies (LUC)
  - Corollary 7.4.11 (p. 334): (ZHOU) implies (LUC) for every $\mathbf X^i$
  - Definition 7.4.12 (p. 334): strong local unique continuation property (SLUC): all $\mathbf X^i$ have (LUC)
  - Theorem 7.4.13 (p. 334): (ZHOU) implies (SLUC)
  - Definition 7.4.14 (p. 335): very strong (LUC), (VSLUC), on $X_\infty$
  - Lemma 7.4.15 (p. 335): (VSLUC) implies (LUC)
  - Proposition 7.4.16 (p. 336): (VSLUC) passes to every $\mathbf X^i$
  - Proposition 7.4.17 (p. 336): (VSLUC) implies (SLUC)
  - Proposition 7.4.18 (p. 336): (VSLUC) and (SLUC) are equivalent
  - Definition 7.4.19 (p. 337): local regularity property (LR): $|\beta(y)|=|y|$ forces $\beta$ to be given by some $g\in G_x$
  - Lemma 7.4.20 (p. 337): a locally defined sc-diffeomorphism $\beta$ with $\beta(x)=x$, $|\beta(y)|=|y|$ maps $U(x)$ onto itself
  - Definition 7.4.21 (p. 338): local regularity property (LR') for maps $\beta:U(x)\to X$
  - Proposition 7.4.22 (p. 338): (ZHOU) implies (LR)
  - Definition 7.4.23 (p. 339): strong local regularity (SLR): all $\mathbf X^i$ have (LR)
  - Theorem 7.4.24 (p. 340): (ZHOU) implies (SLR)
- §7.6 Appendix (7.6.3 On the metrizability of $T_R$, 7.6.4 Reduced Ep-Groupoids and Raising the Index, 7.6.5 Boundary Structure of Tame Ep-Groupoids)
  - Theorem 7.6.7 (p. 351): under (SLUC), $(\mathbf X^i)_R$ and $(\mathbf X_R)^i$ are identified by an sc-diffeomorphism
  - Corollary 7.6.8 (p. 351): under (ZHOU), $(\mathbf X_R)^i$ and $(\mathbf X^i)_R$ are identified
  - Theorem 7.6.9 (p. 355): a tame ep-groupoid has natural metrizable topologies on $b\mathbf X$ and the boundary structure of the tame ep-groupoid (ep-groupoid version of Theorem 2.7.13)

**Chapter 8** (9 items)

- §8.1 The Tangent of an Ep-Groupoid
  - Proposition 8.1.16 (p. 369): (ZHOU) for $\mathbf X$ implies (ZHOU) for the tangent ep-groupoid $T\mathbf X$
  - Proposition 8.1.17 (p. 371): (LUC) of $\mathbf X^1$ implies (LUC) of $T\mathbf X$; (SLUC) of $\mathbf X$ implies (SLUC) of $T\mathbf X$
- §8.2 Sc-Differential Forms on Ep-Groupoids
  - Proposition 8.2.3 (p. 373): Poincar\'e lemma for sc-differential forms on ep-groupoids (2017: promised for later)
- §8.3 Strong Bundles over Ep-Groupoids
  - Definition 8.3.5 (p. 379): auxiliary norm on a strong bundle over an ep-groupoid ($W_{0,1}$ and norms on the fibres)
- §8.4 Topological and Regularity Properties of Strong Bundles (new section)
  - Proposition 8.4.1 (p. 380): for a strong bundle over an ep-groupoid, paracompactness of $|X|$, $|W[0]|$, $|W[1]|$ are equivalent
  - Definition 8.4.2 (p. 382): local regularity property for strong bundles over ep-groupoids
  - Proposition 8.4.3 (p. 382): effective $\mathbf X$ with local regularity gives the local regularity property of the strong bundle
- §8.5 Proper Covering Functors
  - Example 8.5.6 (p. 388): a covering functor $f:D\to C$ with $C=\{x\}$, $G_x=\mathbb Z/2$ (two objects $a,b$)
- §8.5, proof of Theorem 8.5.8
  - Lemma 8.5.10 (p. 395): $B$ is a strong bundle isomorphism over $\mathbf Y$ covering the identity of $\mathbf Y$ (in §8.5, proof of Theorem 8.5.8)

**Chapter 5** has no 2021-only item; the two items that seem new, Theorem 5.3.15 and Theorem 5.5.5, are 2017 Theorems 5.8 and 5.10 (the headings carry a title).

### Summary

| Ch. | 2017 items | same | changed | absent | 2021-only | 2021 items |
|---|---|---|---|---|---|---|
| 1 | 27 | 26 | 1 | 0 | 1 | 28 |
| 2 | 63 | 61 | 2 | 0 | 37 | 100 |
| 3 | 88 | 85 | 3 | 0 | 7 | 93 |
| 4 | 31 | 28 | 3 | 0 | 6 | 37 |
| 5 | 54 | 50 | 4 | 0 | 0 | 54 |
| 6 | 51 | 45 | 6 | 0 | 2 | 53 |
| 7 | 52 | 48 | 3 | 1 | 46 | 97 |
| 8 | 33 | 32 | 1 | 0 | 9 | 42 |
| 1–8 | 399 | 375 | 23 | 1 | 108 | 504 |

The 2021 item counts are the numbered items found in the text of the chapter (Question 4.2.4 not counted); an
item restated in an appendix is counted once. The 2014 items absent from the 2017 text (5 in Chapters 3, 5 and 6) are absent in
2021 as well.

### What a reader of the 2017 statements should know

The statements changed in 2021 that touch what the Lean files formalize (2017/preprint numbers, as
in the rest of the project):

- **Proposition 1.4** (preprint 1.10): the sum $T+S$ of an sc-Fredholm operator and an sc$^+$-operator is sc-Fredholm *with the same index* (Proposition 1.1.11).
- **Proposition 2.3** (preprint 2.6): part (3) is now conditional on $f\circ r$ being sc-smooth (Proposition 2.1.13).
- **Definition 2.8** (preprint 2.13, M-polyfold): the footnote fixes that paracompactness does not include Hausdorff, so "Hausdorff paracompact" is two requirements (Definition 2.3.4).
- **Theorem 3.11** (preprint 3.40, Local Regularity and Compactness): the sequential form (solutions converging on level 0 converge on level $m$) is part of the statement (Theorem 3.5.1).
- **Definitions 3.4 and 3.13** (preprint 3.4 and 3.48, the filling): the retraction is no longer required to be tame (Definition 3.1.4), resp. need only be sc-smooth (Definition 3.6.1).
- **Theorem 4.3** (preprint 4.22): the faces $F_1,\dots,F_d$ contain $x$ (Theorem 4.2.11).
- **Theorem 4.4** (preprint 4.23, Sard for families): non-emptiness of the fibres is dropped, $\Sigma$ is a measurable set of full measure (Theorem 4.3.1).
- **Proposition 4.5** (preprint 4.26): the levels of $d$ are $\Omega^k(X^i)\to\Omega^{k+1}(X^{i+1})$ in 2021 (the 2017 levels presumably meant so).
- **Definition 5.5 and Theorem 5.1** (preprint 5.4, 5.5): two further compactness notions, proper$_{<\infty}$ and weakly proper$_{<\infty}$, and the equivalence of all five for sc-Fredholm sections (Definition 5.2.1, Theorem 5.2.2).
- **Theorem 5.5** (preprint 5.13): the solution set is a *compact* sub-M-polyfold (Theorem 5.3.5).
- **Definition 5.10** (preprint 5.20, generalized compact homotopy): the data are weaker (Definition 5.3.13).
- **Lemma 6.3, Propositions 6.6, 6.7 (preprint 6.15), 6.12 (6.28), Lemmas 6.13 (6.30), 6.15 (6.33)**: index equalities, an explicit $H$, explicit hypotheses, tameness and $Y\times[0,1]$-valued sections, a corrected solution-set condition, and the split of Lemma 6.15 into Lemmas 6.6.8 and 6.6.9.
- **Definition 7.7 and Proposition 7.5**: the remark that sc-smoothness on objects suffices needs continuity on morphisms (level 0), and part (2) of the finite-set proposition has its target corrected (Definitions 7.1.7, Proposition 7.1.15).
- **Propositions 7.9 and 7.10** (points G.71 and the Hausdorff hypothesis on $\mathbf X^R$): in 2021 $\mathbf X^R$ is an M-polyfold, and $(X,\mathbf X^R)$ an ep-groupoid, exactly when the natural topology $T_R$ is Hausdorff (Propositions 7.2.13, Theorem 7.2.14); $T_R$ is Hausdorff iff (LUC) iff $\mathbf X^T$ is closed (Theorem 7.2.22), and Remark 7.2.8 and Appendix 7.6.3 say that this fails in general. This is the hypothesis taken in `Reduced.lean`.
- **Definition 8.10**: condition (0), compatibility of $A$ with the strong bundle data, is stated (Definition 8.5.9).
- **Unchanged**: Theorem 8.5 (including part (5) as printed, V8.30), Theorem 7.1, the definitions 7.1–7.6 and 7.8–7.11, and all of Chapter 8 apart from Definition 8.10.

## The Springer edition (2021), Part IV, Chapters 17–19

Part IV (*Fredholm Theory in Groupoidal Categories*) has no preprint; the comparison is between the
2017 arXiv text (pp. 573–684) and the Springer edition (pp. 743–957), with the 2021 text as the
authoritative one. As for Chapters 1–8, nothing of the book text is quoted beyond a few words.

**Method.** The numbered items (Definition, Lemma, Proposition, Theorem, Corollary, Remark, Example)
of Chapters 17–19 were extracted from the `pdftotext -layout` texts of both versions with their pages
and aligned chapter by chapter, in order, by the text of the statement. Every pair whose statement text
agreed to less than about 85 %, and every item without a partner, was then read in both texts; for the
remaining pairs a word-by-word difference of the statements was read. Three lines of the 2021 text that
begin with an item name but are cross-references were discarded. Pages are printed pages, read off the
running heads. The 2017 text numbers each kind separately within a chapter (Definition 17.1, Remark
17.1, Lemma 17.1, …); the 2021 text has one counter per section. Status as in the tables for Chapters
1–8: `same` = the statement is unchanged up to editorial wording (a remark in brackets records an
editorial change such as a hypothesis written into the statement), `changed: …` = the mathematical
content differs, `absent` = no counterpart as a numbered item. The comparison is of statements, not of
proofs. A row-by-row list with the line numbers of the items in `sources/HWZ-Book-2021.txt` was kept
with the working notes; it is not part of the repository.

### Structural differences

- **A new section §17.4, Boundary Formalism for Tame Polyfolds** (pp. 787–811, 26 numbered items): the
  tame boundary category $bC$ of a tame polyfold $C$, its topology and its polyfold structure
  (Theorem 17.4.26). The 2017 sections 17.4–17.7 are §§17.5–17.8 in 2021. Chapters 18 and 19 keep their
  sections; §19.4 is retitled "Metrizability Criteria".
- **§17.1 expanded**: the properness property (Lemma 17.1.10 to Lemma 17.1.13), weak polyfold
  structures, the covering category and the properties (LR), (SLR), (LUC), (SLUC), (ZHOU) for a polyfold
  $(C,F,M)$ (Remark 17.1.16 to Theorem 17.1.26); 2017 Remark 17.2 is Theorem 17.1.27 with a proof.
- **§17.6**: branched integration and Stokes' theorem under (LUC) (Theorems 17.6.8–17.6.10).
- **§18.2**: the compactness notions proper and proper$_{<\infty}$ and their equivalence for sc-Fredholm
  section functors (Definition 18.2.1, Theorem 18.2.2), as in Chapter 5.
- **Chapter 19, topology of the transition sets**: in 2021 the natural topology on $M(\Psi,\Psi')$ is
  regular Hausdorff and locally metrizable (Theorem 19.3.3, Lemma 19.3.8); it is metrizable under the
  properness condition (Proposition 19.4.4) or when the natural topology $T$ on $|S|$ is metrizable
  (Corollary 19.4.8), and the polyfold results (Theorems 19.5.1, 19.5.3, 19.6.13, 19.7.29) assume $T$
  metrizable. The 2017 text states metrizability of $M(\Psi,\Psi')$ without these hypotheses (Theorem
  19.2, Proposition 19.3).
- **Chapter 19, constructions**: a transition construction is an equivalence class of transition data
  under restriction (Definitions 19.1.5, 19.1.6, 19.6.5); (ZHOU), (LUC), (LR) for basic constructions
  (Definitions 19.5.6–19.5.10); coherent data for strong bundles (Definition 19.6.15).
- **§19.7 and §19.8 rewritten**: a basic construction for a covering functor $P$ uses one transition
  construction on $B$ (Definition 19.7.11); the topological results (Lemma 19.7.12 to Theorem 19.7.25)
  precede the smooth ones (Proposition 19.7.26 to Theorem 19.7.29). §19.8 adds bundle covering pull-backs
  (Definitions 19.8.1–19.8.5, Theorem 19.8.6), a basic construction for a bundle covering square
  (Definitions 19.8.13–19.8.15) and the topology on $|E_A|$ (Definition 19.8.20, Lemma 19.8.21).
- **Appendix A, Construction Cheatsheet** (2021 pp. 959–), new: a summary of Chapter 19 with its own
  numbered items (Remark A.1.1, Theorem A.1.2, …), which are not counted here.
- **Section titles**, 2017 against 2021:

| Ch. | arXiv 1707.08941 | p. | Springer 2021 | p. |
|---|---|---|---|---|
| 17 | 17 Polyfold Theory for Categories | 573 | 17 Polyfold Theory for Categories | 743 |
| 17 | 17.1 Polyfold Structures and Categories | 573 | 17.1 (same title) | 744 |
| 17 | 17.2 Tangent Construction | 582 | 17.2 (same title) | 767 |
| 17 | 17.3 Subpolyfolds | 592 | 17.3 (same title) | 784 |
| 17 | — |  | 17.4 Boundary Formalism for Tame Polyfolds (new) | 787 |
| 17 | 17.4 Branched Ep$^+$-Subcategories | 594 | 17.5 (same title) | 812 |
| 17 | 17.5 Sc-Differential Forms and Stokes | 599 | 17.6 (same title) | 817 |
| 17 | 17.6 Strong Bundle Structures | 605 | 17.7 (same title) | 824 |
| 17 | 17.7 Proper Covering Constructions | 609 | 17.8 (same title) | 828 |
| 18 | 18 Fredholm Theory in Polyfolds | 623 | 18 Fredholm Theory in Polyfolds | 843 |
| 18 | 18.1 Basic Concepts | 624 | 18.1 (same title) | 844 |
| 18 | 18.2 Compactness Properties | 628 | 18.2 (same title) | 849 |
| 18 | 18.3 Sc$^+$-Multisection Functors | 631 | 18.3 (same title) | 851 |
| 18 | 18.4 Constructions and Extensions | 632 | 18.4 (same title) | 853 |
| 18 | 18.5 Orientations | 634 | 18.5 (same title) | 856 |
| 18 | 18.6 Perturbation Theory | 638 | 18.6 (same title) | 860 |
| 19 | 19 General Constructions | 641 | 19 General Constructions | 863 |
| 19 | 19.1 The Basic Constructions | 641 | 19.1 (same title) | 863 |
| 19 | 19.2 The Natural Topology $T$ for $\lvert S\rvert$ | 645 | 19.2 (same title) | 869 |
| 19 | 19.3 The Natural Topology for $M(\Psi,\Psi')$ | 647 | 19.3 (same title) | 872 |
| 19 | 19.4 Metrizability Criterion for $T$ | 651 | 19.4 Metrizability Criteria | 879 |
| 19 | 19.5 The Polyfold Structure for $(S,T)$ | 655 | 19.5 (same title) | 886 |
| 19 | 19.6 A Strong Bundle Version | 658 | 19.6 (same title) | 890 |
| 19 | 19.7 Covering Constructions | 665 | 19.7 (same title) | 905 |
| 19 | 19.8 Covering Constructions for Strong Bundles | 675 | 19.8 (same title) | 930 |
| — | — |  | Appendix A Construction Cheatsheet (new) | 959 |

### Concordance tables, Chapters 17–19

Rows follow the 2017 order. Where the 2021 order differs, the 2021 number shows it: 2017 Remark 17.2
is Theorem 17.1.27, Proposition 19.3 is Proposition 19.4.4, Proposition 19.8 is Proposition 19.7.26.

#### Chapter 17 (2021 pp. 743–842; arXiv 1707.08941 pp. 573–622)

| arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|
| Definition 17.1 | Definition 17.1.1 | 744 | same |
| Definition 17.2 | Definition 17.1.2 | 744 | same |
| Definition 17.3 | Definition 17.1.3 | 745 | same (2017 condition (2), $O$ paracompact, is now a footnote: an M-polyfold is paracompact by definition; (3), (4) become (2), (3)) |
| Definition 17.4 | Definition 17.1.5 | 745 | same (adds "is a morphism") |
| Definition 17.5 | Definition 17.1.6 | 746 | same |
| Remark 17.1 | Remark 17.1.7 | 746 | same |
| Definition 17.6 | Definition 17.1.8 | 747 | same |
| Lemma 17.1 | Lemma 17.1.9 | 748 | same |
| Theorem 17.1 | Theorem 17.1.14 | 753 | same (the heading carries a title) |
| Lemma 17.2 | Lemma 17.1.15 | 754 | same |
| Theorem 17.2 | Theorem 17.1.18 | 756 | changed: adds the functor $\Gamma_\Psi$, the rules $f_{\Psi',\Psi''}\circ f_{\Psi,\Psi'}=f_{\Psi,\Psi''}$, $f_{\Psi,\Psi}=1$, and the weak polyfold structures $(X_\Psi,\lvert \Gamma_\Psi\rvert )$; the 2017 conclusion that $\lvert C\rvert $ is a paracompact polyfold is not part of the statement (a polyfold structure on $\lvert C\rvert $ under (ZHOU) is Theorem 17.1.26) |
| Remark 17.2 | Theorem 17.1.27 | 759 | changed: the remark is stated as a theorem with a proof ("Canonical natural transformation") |
| Theorem 17.3 | Theorem 17.1.28 | 766 | same |
| Definition 17.7 | Definition 17.1.30 | 767 | same |
| Lemma 17.3 | Lemma 17.2.1 | 768 | same (the hypothesis that $\alpha$ has regularity at least 1 is in the statement) |
| Definition 17.8 | Definition 17.2.2 | 768 | same |
| Definition 17.9 | Definition 17.2.3 | 769 | same |
| Proposition 17.1 | Proposition 17.2.4 | 769 | same (Banachable, sc-Banachable) |
| Proposition 17.2 | Proposition 17.2.5 | 770 | same |
| Lemma 17.4 | Lemma 17.2.9 | 773 | same ($T_\Psi$ on $TO$; the level-1 hypothesis is in the statement) |
| Lemma 17.5 | Lemma 17.2.11 | 775 | same (wording of (1)) |
| Definition 17.10 | Definition 17.2.13 | 776 | changed: the natural topology is the one on $M(T\Psi_1,T\Psi_2)$ (2017: $M(\Psi_1,\Psi_2)$) |
| Proposition 17.3 | Proposition 17.2.14 | 776 | same |
| Proposition 17.4 | Proposition 17.2.15 | 781 | same |
| Proposition 17.5 | Proposition 17.2.16 | 782 | same |
| Theorem 17.4 | Theorem 17.2.17 | 783 | same |
| Remark 17.3 | Remark 17.2.18 | 784 | same |
| Definition 17.11 | Definition 17.3.1 | 784 | same |
| Definition 17.12 | Definition 17.3.2 | 784 | same |
| Remark 17.4 | Remark 17.3.3 | 784 | changed: the equivalence of the two definitions is proved (Proposition 17.3.4); the 2017 text leaves it to the reader |
| Lemma 17.6 | Lemma 17.3.5 | 786 | same |
| Proposition 17.6 | Proposition 17.3.6 | 786 | same |
| Definition 17.13 | Definition 17.3.7 | 786 | same |
| Proposition 17.7 | Proposition 17.3.8 | 787 | same |
| Definition 17.14 | Definition 17.5.1 | 812 | same |
| Proposition 17.8 | Proposition 17.5.2 | 813 | same |
| Definition 17.15 | Definition 17.5.3 | 813 | same |
| Definition 17.16 | Definition 17.5.4 | 813 | same |
| Proposition 17.9 | Proposition 17.5.5 | 814 | same |
| Definition 17.17 | Definition 17.5.6 | 815 | same |
| Proposition 17.10 | Proposition 17.5.7 | 816 | same |
| Definition 17.18 | Definition 17.5.8 | 817 | same |
| Remark 17.5 | Remark 17.5.9 | 817 | same |
| Proposition 17.11 | Proposition 17.6.1 | 818 | same |
| Definition 17.19 | Definition 17.6.2 | 819 | same |
| Definition 17.20 | Definition 17.6.3 | 820 | same |
| Theorem 17.5 | Theorem 17.6.4 | 821 | same |
| Definition 17.21 | Definition 17.6.5 | 822 | same |
| Theorem 17.6 | Theorem 17.6.6 | 822 | same |
| Theorem 17.7 | Theorem 17.6.7 | 823 | same |
| Definition 17.22 | Definition 17.7.1 | 825 | same |
| Definition 17.23 | Definition 17.7.2 | 826 | same |
| Definition 17.24 | Definition 17.7.3 | 826 | same |
| Definition 17.25 | Definition 17.7.4 | 827 | same |
| Definition 17.26 | Definition 17.8.1 | 828 | same (in (3) the $y_i$ are all of $\lvert P\rvert ^{-1}(z)$ and the union is written as disjoint) |
| Remark 17.6 | Remark 17.8.2 | 829 | same |
| Definition 17.27 | Definition 17.8.3 | 829 | same |
| Definition 17.28 | Definition 17.8.4 | 831 | same |
| Remark 17.7 | Remark 17.8.5 | 831 | same |
| Lemma 17.7 | Lemma 17.8.7 | 833 | same |
| Lemma 17.8 | Lemma 17.8.8 | 833 | same |
| Lemma 17.9 | Lemma 17.8.9 | 834 | same |
| Definition 17.29 | Definition 17.8.10 | 834 | same |
| Remark 17.8 | Remark 17.8.11 | 835 | same |
| Definition 17.30 | Definition 17.8.12 | 835 | same |
| Definition 17.31 | Definition 17.8.13 | 836 | same |
| Lemma 17.10 | Lemma 17.8.14 | 836 | same |
| Proposition 17.12 | Proposition 17.8.15 | 837 | same |
| Proposition 17.13 | Proposition 17.8.16 | 839 | same |

#### Chapter 18 (2021 pp. 843–862; arXiv 1707.08941 pp. 623–640)

| arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|
| Definition 18.1 | Definition 18.1.1 | 844 | same |
| Remark 18.1 | Remark 18.1.2 | 844 | same |
| Definition 18.2 | Definition 18.1.3 | 845 | same (the hypothesis $f(\alpha)=0$ is in the statement) |
| Definition 18.3 | Definition 18.1.4 | 845 | same |
| Theorem 18.1 | Theorem 18.1.5 | 846 | same (the heading carries a title) |
| Remark 18.2 | Remark 18.1.6 | 846 | same |
| Definition 18.4 | Definition 18.1.7 | 846 | same |
| Lemma 18.1 | Lemma 18.1.8 | 847 | same |
| Definition 18.5 | Definition 18.1.9 | 847 | same |
| Definition 18.6 | Definition 18.1.10 | 847 | same |
| Definition 18.7 | Definition 18.1.11 | 847 | same |
| Theorem 18.2 | Theorem 18.1.12 | 848 | same |
| Definition 18.8 | Definition 18.2.1 | 849 | changed: stated for sc-smooth section functors; adds (2) proper and (3) proper$_{<\infty}$ |
| Theorem 18.3 | Theorem 18.2.2 | 850 | changed: the equivalence of compact moduli space, proper and proper$_{<\infty}$ (2017: the closure condition for a given auxiliary norm) |
| Definition 18.9 | Definition 18.2.3 | 850 | changed: adds "strongly controls compactness" (every constant $0<C<\infty$) |
| Definition 18.10 | Definition 18.2.4 | 850 | same |
| Remark 18.3 | Remark 18.2.5 | 850 | same |
| Theorem 18.4 | Theorem 18.2.6 | 851 | same |
| Remark 18.4 | Remark 18.2.7 | 851 | same |
| Definition 18.11 | Definition 18.3.1 | 852 | same |
| Remark 18.5 | Remark 18.3.2 | 852 | same |
| Definition 18.12 | Definition 18.3.3 | 852 | same |
| Theorem 18.5 | Theorem 18.3.5 | 853 | same |
| Theorem 18.6 | Theorem 18.3.6 | 853 | same |
| Definition 18.13 | Definition 18.4.1 | 853 | same |
| Remark 18.6 | Remark 18.4.2 | 853 | same |
| Proposition 18.1 | Proposition 18.4.3 | 855 | same (the hypotheses on $P$, $\alpha$, $e$ are in the statement) |
| Theorem 18.7 | Theorem 18.4.4 | 855 | same (the heading carries a title) |
| Definition 18.14 | Definition 18.5.1 | 857 | same |
| Definition 18.15 | Definition 18.5.2 | 858 | same |
| Remark 18.7 | Remark 18.5.3 | 859 | same |
| Definition 18.16 | Definition 18.5.4 | 859 | same |
| Remark 18.8 | Remark 18.5.5 | 859 | same |
| Proposition 18.2 | Proposition 18.5.6 | 859 | same |
| Theorem 18.8 | Theorem 18.6.1 | 860 | changed: the multisection functor is $\Lambda:E\to\mathbb Q^+$ (2017: $\Lambda:C\to\mathbb Q^+$) |

#### Chapter 19 (2021 pp. 863–957; arXiv 1707.08941 pp. 641–684)

| arXiv 2017 | Springer 2021 | p. | Status |
|---|---|---|---|
| Definition 19.1 | Definition 19.1.1 | 863 | same |
| Definition 19.2 | Definition 19.1.2 | 864 | same |
| Definition 19.3 | Definition 19.1.3 | 865 | same |
| Remark 19.1 | Remark 19.1.4 | 865 | same |
| Definition 19.4 | Definition 19.1.6 | 867 | changed: a transition construction is an equivalence class of transition data under restriction (Definition 19.1.5) |
| Definition 19.5 | Definition 19.1.7 | 868 | same |
| Remark 19.2 | Remark 19.1.8 | 868 | same (stated for a representative) |
| Definition 19.6 | Definition 19.2.1 | 869 | same (names $T$ the natural topology) |
| Theorem 19.1 | Theorem 19.2.2 | 869 | same |
| Remark 19.3 | Remark 19.2.3 | 870 | changed: adds an example in which $T$ is not Hausdorff |
| Remark 19.4 | Remark 19.2.4 | 872 | same |
| Definition 19.7 | Definition 19.3.2 | 873 | same (stated for a representative) |
| Theorem 19.2 | Theorem 19.3.3 | 873 | changed: $T_{\Psi,\Psi'}$ is regular Hausdorff and locally metrizable (2017: metrizable); adds (6), $\bar\Psi:G\times O\to M(\Psi,\Psi)$ is a homeomorphism |
| Proposition 19.1 | Proposition 19.3.4 | 874 | same (stated for a representative; (2) on all of $V(o)$) |
| Proposition 19.2 | Proposition 19.3.5 | 875 | same |
| Remark 19.5 | Remark 19.3.6 | 875 | same (stated for a representative) |
| Proposition 19.3 | Proposition 19.4.4 | 883 | changed: the metrizability of $T_{\Psi,\Psi'}$ is now proved under the properness condition (2017: §19.3, without it) |
| Remark 19.6 | — | — | absent: the summary remark at the end of §19.3; in 2021 the transition sets are regular Hausdorff and locally metrizable (Theorem 19.3.3), and their metrizability is taken up in §19.4 (running text) |
| Definition 19.8 | Definition 19.4.1 | 879 | same ("property" becomes "condition"; $M(\Psi,\Psi')$ is called a topological space, 2017: metrizable space) |
| Proposition 19.4 | Proposition 19.4.2 | 880 | same ("property" becomes "condition") |
| Proposition 19.5 | Proposition 19.4.5 | 884 | same ("property" becomes "condition") |
| Theorem 19.3 | Theorem 19.4.6 | 885 | same |
| Proposition 19.6 | Proposition 19.4.7 | 885 | same ("property" becomes "condition") |
| Theorem 19.4 | Theorem 19.5.1 | 886 | changed: $T$ is assumed metrizable |
| Corollary 19.1 | Corollary 19.5.2 | 887 | same |
| Theorem 19.5 | Theorem 19.5.3 | 888 | changed: split into (1) properness and second countable or paracompact give a metrizable $T$, (2) the polyfold structure for metrizable $T$ |
| Remark 19.7 | Remark 19.5.4 | 888 | changed: the transition-set topologies are no longer called metrizable; $T$ is completely regular, Hausdorff and locally metrizable |
| Definition 19.9 | Definition 19.6.1 | 891 | same |
| Remark 19.8 | Remark 19.6.2 | 892 | same |
| Definition 19.10 | Definition 19.6.3 | 892 | same |
| Definition 19.11 | Definition 19.6.4 | 895 | changed: stated with maps on neighbourhoods $V(o)$ of a representative (2017: germs) |
| Definition 19.12 | Definition 19.6.6 | 896 | same |
| Definition 19.13 | Definition 19.6.7 | 897 | same |
| Theorem 19.6 | Theorem 19.6.8 | 897 | same |
| Proposition 19.7 | Proposition 19.6.9 | 898 | changed: $T$ is metrizable if and only if $\bar T$ is (2017: "if") |
| Definition 19.14 | Definition 19.6.10 | 898 | same |
| Theorem 19.7 | Theorem 19.6.11 | 898 | changed: the topologies are locally metrizable and regular Hausdorff (2017: metrizable) |
| Theorem 19.8 | Theorem 19.6.13 | 900 | changed: $T$ is assumed metrizable |
| Theorem 19.9 | — | — | absent: the content is split between Proposition 19.6.9 ($\bar T$ metrizable if and only if $T$ is) and Theorem 19.6.13 (the strong bundle structure on the transition sets, for metrizable $T$) |
| Remark 19.9 | Remark 19.6.14 | 900 | same |
| Definition 19.15 | Definition 19.7.1 | 906 | same |
| Remark 19.10 | Remark 19.7.2 | 906 | same (cross-references to Definition 17.8.1) |
| Definition 19.16 | Definition 19.7.3 | 906 | same |
| Definition 19.17 | Definition 19.7.4 | 907 | changed: on objects, the $e\in E$ with $(\hat\tau(e),\hat\Psi(e))=(o,a)$ is required to be unique |
| Lemma 19.1 | Lemma 19.7.5 | 907 | same |
| Remark 19.11 | Remark 19.7.6 | 908 | same |
| Definition 19.18 | Definition 19.7.7 | 908 | same |
| Remark 19.12 | Remark 19.7.8 | 908 | same |
| Lemma 19.2 | Lemma 19.7.10 | 909 | same |
| Definition 19.19 | Definition 19.7.11 | 910 | changed: a basic construction for $P$ is $(\hat F,\mathcal F)$ with $\mathcal F$ a transition construction on $B$ (2017: $P$-compatible transition constructions on both kinds of transition sets) |
| Proposition 19.8 | Proposition 19.7.26 | 926 | changed: $\lvert B\rvert $ is assumed metrizable; the M-polyfold structure of $M(\hat\Psi,\hat\Psi')$ is characterized by $p$; placed after the topological results |
| Lemma 19.3 | Proposition 19.7.18 | 919 | changed: $\lvert P\rvert $ is a surjective local homeomorphism (2017: continuous and open) |
| Lemma 19.4 | Corollary 19.7.20 | 921 | changed: stated as a corollary, with a connected $G$-invariant neighbourhood $O_0$ and $\hat\tau^{-1}(O_0)$ a disjoint union |
| Proposition 19.9 | Proposition 19.7.23 | 923 | same (for a finite-to-one covering functor with a basic construction, 2017: proper covering functor; "property" becomes "condition") |
| Proposition 19.10 | Proposition 19.7.24 | 924 | same (for a finite-to-one covering functor with a basic construction, 2017: proper covering functor) |
| Theorem 19.10 | Theorem 19.7.29 | 929 | changed: the hypothesis is that $\lvert B\rvert $ is metrizable (2017: properness and paracompactness for $\lvert A\rvert $ or $\lvert B\rvert $) |
| Definition 19.20 | Definition 19.8.7 | 941 | same |
| Definition 19.21 | Definition 19.8.8 | 943 | same (renamed "strong ep-bundle covering model") |
| Definition 19.22 | Definition 19.8.10 | 943 | same (the diagrams of (1)–(3) are displayed) |
| Definition 19.23 | Definition 19.8.13 | 948 | same |
| Definition 19.24 | Definition 19.8.14 | 948 | changed: one transition construction on $B$ with (1) metrizable $T_{\lvert B\rvert }$, (2) coherence, (3) a basic construction for $P$ (2017: four transition constructions with compatibilities) |
| Theorem 19.11 | Theorem 19.8.22 | 956 | changed: no separate properness and paracompactness hypothesis (the metrizability of $T_{\lvert B\rvert }$ is part of Definition 19.8.14); the conclusion is stated with proper strong bundle covering squares (the heading carries a title) |

### Items of the 2021 text in Chapters 17–19 without a 2017 counterpart

Listed by section with a one-line paraphrase (the item's number and page in the 2021 text); "2017:
running text" means that the content is in the 2017 text, but not as a numbered item.

**Chapter 17** (52 items)

- §17.1 Polyfold Structures and Categories
  - Remark 17.1.4 (p. 745): a local uniformizer gives a small full subcategory the structure of an ep-groupoid
  - Lemma 17.1.10 (p. 749): sequences in $M(\Psi,\Psi')$ over convergent sequences in $O$, $O'$ have convergent subsequences
  - Proposition 17.1.11 (p. 750): neighbourhoods $U(q)$ with $t:s^{-1}(\mathrm{cl}\,U(q))\to O'$ proper
  - Definition 17.1.12 (p. 751): the properness property of $C$ (2017: argued in the proof of Theorem 17.1)
  - Lemma 17.1.13 (p. 752): transition maps between natural source-type (target-type) charts are the identity
  - Remark 17.1.16 (p. 755): $X_\Psi$ has a paracompact orbit space; with (ZHOU), $(X_\Psi,|\Gamma_\Psi|)$ is a polyfold structure
  - Definition 17.1.17 (p. 755): weak polyfold structure $(X,\beta)$
  - Remark 17.1.19 (p. 757): the diagrams behind Theorem 17.1.18
  - Definition 17.1.20 (p. 757): the covering category $\mathrm{COV}_C$
  - Definition 17.1.21 (p. 757): the natural embedding of $\mathrm{COV}_C$ into the ep-groupoids
  - Definition 17.1.22 (p. 758): (LR), (SLR), (LUC), (SLUC), (ZHOU) for $C$
  - Proposition 17.1.23 (p. 758): (ZHOU) implies (LUC), (SLUC), (LR), (SLR)
  - Proposition 17.1.24 (p. 758): these properties then hold for every covering set
  - Proposition 17.1.25 (p. 758): under (LUC) a generalized isomorphism $h$ with $|\Gamma_{\Psi'}|\circ|h|=|\Gamma_\Psi|$ is $f_{\Psi,\Psi'}$
  - Theorem 17.1.26 (p. 759): under (ZHOU), $|C|$ carries a natural equivalence class of polyfold structures
  - Corollary 17.1.29 (p. 766): $C^1$ inherits (ZHOU), (SLUC), (SLR)
- §17.2 Tangent Construction
  - Definition 17.2.6 (p. 770): the tangent category $TC$ (2017: running text before Lemma 17.4)
  - Lemma 17.2.7 (p. 770): $TC$ is a groupoidal category
  - Remark 17.2.8 (p. 770): an alternative construction of $TC$ from $\mu_C$
  - Lemma 17.2.10 (p. 773): $T_\Psi:G\ltimes TO\to TC$ is a functor
  - Proposition 17.2.12 (p. 776): the unique topology on $M(T\Psi_1,T\Psi_2)$ making the local maps homeomorphisms onto open sets
- §17.3 Subpolyfolds
  - Proposition 17.3.4 (p. 784): Definitions 17.3.1 and 17.3.2 are equivalent
- §17.4 Boundary Formalism for Tame Polyfolds (new section), pp. 787–811: all 26 items (17.4.1–17.4.26) are new: the faces $F_{U(\bar o)}$ of good neighbourhoods (Definition 17.4.1), the tame boundary category $bC$ with its objects and morphisms (Definitions 17.4.2–17.4.4), the face stabilizers $G_\theta$ (Definition 17.4.5) the functors $\Psi_\theta$ and $\bar\Psi$ (Lemmas 17.4.6, 17.4.8, 17.4.9), Remark 17.4.7, the transition sets $M(\Psi_\theta,\Psi'_{\theta'})$ and their M-polyfold structures (Lemmas 17.4.10, 17.4.11, 17.4.13, 17.4.15, Definitions 17.4.12, 17.4.14, Theorem 17.4.16), the topology on $|bC|$ (Definition 17.4.17, Lemmas 17.4.18, 17.4.20, 17.4.22 (the map $\sigma$), Theorem 17.4.19, Corollary 17.4.21; Hausdorff, regular, paracompact: Propositions 17.4.23–17.4.25), and the polyfold structure of $bC$ (Theorem 17.4.26).
- §17.6 Sc-Differential Forms and Stokes
  - Theorem 17.6.8 (p. 823): under (LUC), the branched integral over $\hat\Theta$ with compact support is independent of the covering family
  - Theorem 17.6.9 (p. 824): under (LUC), the integral over $\partial\hat\Theta$ is well defined
  - Theorem 17.6.10 (p. 824): Effective Stokes Theorem, under (LUC)
- §17.8 Proper Covering Constructions
  - Proposition 17.8.6 (p. 832): shrinking a proper covering model to a connected one

**Chapter 18** (1 items)

- §18.3 Sc$^+$-Multisection Functors
  - Remark 18.3.4 (p. 852): structurability does not depend on the sc-smooth model (2017: sentence after Definition 18.12)

**Chapter 19** (45 items)

- §19.1 The Basic Constructions
  - Definition 19.1.5 (p. 867): equivalence of transition data by restriction
- §19.3 The Natural Topology for $M(\Psi,\Psi')$
  - Lemma 19.3.1 (p. 872): $T_{\Psi,\Psi'}$ does not depend on the representative of the transition construction
  - Proposition 19.3.7 (p. 877): $\bar\Psi:G\times O\to M(\Psi,\Psi)$ is a homeomorphism
  - Lemma 19.3.8 (p. 878): $T_{\Psi,\Psi'}$ is regular
- §19.4 Metrizability Criteria
  - Lemma 19.4.3 (p. 881): local structure of $M(\Psi,\Psi')$ over $U(o)$ under the properness condition
  - Corollary 19.4.8 (p. 885): $T$ metrizable implies every $T_{\Psi,\Psi'}$ metrizable
- §19.5 The Polyfold Structure for $(S,T)$
  - Definition 19.5.5 (p. 889): the maps $Tg$ at a smooth object
  - Definition 19.5.6 (p. 889): (ZHOU) for a basic construction
  - Proposition 19.5.7 (p. 889): (ZHOU) for $(F,\mathcal F)$ gives (ZHOU) for the polyfold
  - Definition 19.5.8 (p. 889): (LUC) for a basic construction
  - Proposition 19.5.9 (p. 890): (LUC) for $(F,\mathcal F)$ gives (LUC) for the polyfold
  - Definition 19.5.10 (p. 890): (LR) for a basic construction
  - Proposition 19.5.11 (p. 890): (ZHOU) implies (SLUC) and (SLR)
- §19.6 A Strong Bundle Version
  - Definition 19.6.5 (p. 896): a strong bundle transition construction is an equivalence class of bundle transition data
  - Lemma 19.6.12 (p. 899): the properness condition for $(F,\mathcal F)$ gives a metrizable $\bar T_{\bar\Psi,\bar\Psi'}$
  - Definition 19.6.15 (p. 902): coherent data $(\bar F,\mathcal F)$
- §19.7 Covering Constructions
  - Lemma 19.7.9 (p. 908): $p$ is surjective with finite fibres
  - Lemma 19.7.12 (p. 911): $M(\Psi,\Psi')\,{}_s\!\times_{\hat\tau}E$ is locally metrizable and regular Hausdorff
  - Proposition 19.7.13 (p. 913): the natural topology on $M(\hat\Psi,\hat\Psi')$ (the topological part of 2017 Proposition 19.8)
  - Proposition 19.7.14 (p. 914): $p:M(\hat\Psi,\hat\Psi')\to M(\Psi,\Psi')$ is a surjective local homeomorphism
  - Proposition 19.7.15 (p. 915): properties of the structural maps of $M(\hat\Psi,\hat\Psi')$
  - Definition 19.7.16 (p. 916): the collection $T_{|A|}$
  - Lemma 19.7.17 (p. 916): $T_{|A|}$ is a locally metrizable topology
  - Lemma 19.7.19 (p. 920): $y\sim y'$ if and only if $|U(y)|=|U(y')|$
  - Lemma 19.7.21 (p. 922): separation properties of the natural topologies on $|B|$ and $|A|$
  - Remark 19.7.22 (p. 923): metrizability of $|B|$ is the properness condition plus paracompactness
  - Theorem 19.7.25 (p. 925): Topological Result about $|P|$
  - Definition 19.7.27 (p. 928): the structural commutative diagrams
  - Theorem 19.7.28 (p. 928): Polyfold Results for $P$
- §19.8 Covering Constructions for Strong Bundles
  - Definition 19.8.1 (p. 932): uniformizer for a bundle covering pull-back $(P,\mu_B)$
  - Definition 19.8.2 (p. 932): uniformizer construction for $(P,\mu_B)$
  - Lemma 19.8.3 (p. 933): the elements of $M(\Gamma,\Gamma')$
  - Definition 19.8.4 (p. 934): transition construction for $(P,\mu_B)$
  - Definition 19.8.5 (p. 937): basic construction for $(P,\mu_B)$
  - Theorem 19.8.6 (p. 938): the natural functor associated to a uniformizer of $(P,\mu_B)$
  - Remark 19.8.9 (p. 943): the word "model" in "strong ep-bundle covering model"
  - Remark 19.8.11 (p. 944): how uniformizers are built in applications
  - Lemma 19.8.12 (p. 946): $\hat\Gamma$ determines $\Psi$, $\hat\Psi$, $\Gamma$
  - Definition 19.8.15 (p. 949): basic construction for a bundle covering square
  - Lemma 19.8.16 (p. 951): the canonical bijection $U_{\hat\Gamma,\hat\Gamma'}$
  - Definition 19.8.17 (p. 952): the natural strong bundle structure on $M(\hat\Gamma,\hat\Gamma')\to M(\hat\Psi,\hat\Psi')$
  - Lemma 19.8.18 (p. 953): $S$ is a local strong bundle isomorphism
  - Definition 19.8.19 (p. 954): a class of commutative diagrams of strong bundles over M-polyfolds
  - Definition 19.8.20 (p. 956): the collection $\bar T_A$
  - Lemma 19.8.21 (p. 956): $\bar T_A$ is a metrizable topology on $|E_A|$
### Summary, Chapters 17–19

| Ch. | 2017 items | same | changed | absent | 2021-only | 2021 items |
|---|---|---|---|---|---|---|
| 17 | 69 | 65 | 4 | 0 | 52 | 121 |
| 18 | 35 | 31 | 4 | 0 | 1 | 36 |
| 19 | 62 | 41 | 19 | 2 | 45 | 105 |
| 17–19 | 166 | 137 | 27 | 2 | 98 | 262 |

Of the 262 numbered items of the 2021 text, 164 have a 2017 counterpart and 98 are new (26 of them in
the new §17.4); 2 of the 166 numbered items of the 2017 text have no 2021 counterpart (Remark 19.6,
Theorem 19.9).

### What a reader of the 2017 statements should know

- **Theorem 17.2** (Theorem 17.1.18): the conclusion is a weak polyfold structure $(X_\Psi,|\Gamma_\Psi|)$
  on $|C|$ for each covering set; a polyfold structure on $|C|$ in the sense of Definition 16.1.1 is
  obtained under (ZHOU) (Theorem 17.1.26).
- **Definition 18.8 and Theorem 18.3** (Definition 18.2.1, Theorem 18.2.2): compactness of $|S_f|$,
  properness and proper$_{<\infty}$ are equivalent for sc-Fredholm section functors.
- **Chapter 19**: the transition sets $M(\Psi,\Psi')$ are regular Hausdorff and locally metrizable;
  their metrizability, and the M-polyfold and polyfold structures built on it, are stated in 2021 under
  the properness condition or for a metrizable natural topology $T$ (Theorem 19.3.3, Propositions
  19.4.4, 19.4.7, Theorems 19.5.1, 19.5.3, 19.6.13, 19.7.29, 19.8.22).
- **Changed in Chapters 17 and 18**: besides the items above, Definition 17.2.13 (the natural topology
  on $M(T\Psi_1,T\Psi_2)$), Remark 17.3.3 with the new Proposition 17.3.4, Definition 18.2.3 (strong
  control of compactness) and Theorem 18.6.1 ($\Lambda:E\to\mathbb Q^+$); the other statements of
  these two chapters are unchanged.

## Marks in the report sources

The generated files (`Comparison.md`, `Comparison.json`, `Verification.md`, `ProofByProof.md`, the
HTML and PDF outputs) are not edited; they are built from their sources. The sources
(`verification/*.md`, `pbp/*.md`, `cmp/*.json`) contain no *(book?)* mark; the seven places of
`cmp/ch03.json` that concern the 2017 text carry the annotations below:

| Source | Item | Text | Annotation |
|---|---|---|---|
| `cmp/ch03.json`, items[19].diff[1] | V3.20, Definition 3.21 | p. 77: "finite dimensional sunspace", presumably "subspace". | *(book 2017: corrected, p. 69)* |
| `cmp/ch03.json`, items[25].diff[1] | V3.26, Theorem 3.29 | p. 85: "δ₁ : V₁ → W₁ satisfying δ(0) = 0", presumably δ₁(0) = 0. | *(book 2017: unchanged, p. 77)* |
| `cmp/ch03.json`, items[30].diff[0] | V3.31, Corollary 3.34 | The citation "Proposition 3.40" presumably means Theorem 3.40, and it is not needed | *(book 2017: unchanged, renumbered: "Proposition 3.11" for Theorem 3.11, p. 79)* |
| `cmp/ch03.json`, items[59].diff[0] | V3.60, Lemma 3.74 | the notation "τ_n → τ'", "B(x⁰, r)" | *(book 2017: both unchanged, Lemma 3.24, p. 122)* |
| `cmp/ch03.json`, items[61].diff[0] | V3.62, Lemma 3.77 | The text cites "Theorem 3.73" for Proposition 3.73. | *(book 2017: unchanged, renumbered: Lemma 3.26, p. 124, cites "Theorem 3.7" for Proposition 3.7)* |
| `cmp/ch03.json`, items[64].diff[0] | V3.65, Lemma 3.80 | The maximum in c(a) is over B((1 + ε)a) ∩ C, where DB is defined | *(book 2017: unchanged, Lemma 3.28, p. 126)* |
| `cmp/ch03.json`, items[66].diff[0] | V3.67, Lemma 3.82 | The notation in (72) (item 26). | *(book 2017: unchanged, Lemma 3.30, p. 128)* |

The report generators `build_comparison.py` (`DEK`, `FOOT`) and `build_verification.py` (`INTRO`)
give the Springer numbers and pages first, with the preprint's or the 2017 text's in parentheses, and
point to `BookConcordance.md` for the correspondence. The `confirm('… for this book?')` string in
`build_signoff.py` is unrelated.
