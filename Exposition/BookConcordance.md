# Book concordance: the 2014 preprint and the book's arXiv version (Chapters 1–6; Part II, Chapter 7)

The exposition and the formalization follow Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory
I*, in the 2014 preprint (arXiv 1407.3185, `sources/HWZ-PartI-2014.txt`); every statement number
and page of Part I in `Findings.md`, the chapters and the reports is the preprint's. Part II has no
preprint, and there the 2017 numbering is the only one (section "Part II" at the end). The published book
(Springer 2021) is not available here. What is available is the book's arXiv version, **arXiv
1707.08941v1 (27 July 2017)**, the only version on arXiv (text in `sources/HWZ-Book-2017.txt`),
whose Part I (Chapters 1–6) corresponds to the preprint's Part I. It is
used below as the best available proxy for the book: **every result recorded here is a result about
the 2017 arXiv text, not about the Springer edition**, whose pages and late corrections may differ.
Pages of the 2017 text are its printed page numbers (Part I starts on p. 3).

**Method.** The numbered items (Definition, Lemma, Proposition, Theorem, Corollary, Remark, Example)
were extracted from `pdftotext -layout` texts of both versions with their pages, and each preprint
item was matched to a 2017 item by the text of its statement (sequence alignment within each chapter);
every weak or missing match was then checked by hand. Chapter 6 (added 2026-11-07) was matched by
hand, item by item, from the statements, with the pages read off the page headers and footers of the
two texts. All 279 numbered items of the preprint's Chapters 1–6 are listed; 274 have a counterpart,
5 are absent, and the 2017 text has 40 numbered items in Chapters 1–6 without a preprint number
(listed after the tables).

**Annotation convention** (used in `Findings.md`, in `Chapter1.md`–`Chapter3.md`, where the marks
*(book?)* and "check against the book" stood, and in the module docstrings of
`Polyfold/Chapter3/`–`Chapter6/`): *(book 2017: …)* gives the result of the check
against arXiv 1707.08941: *unchanged* (the slip or gap is still there), *corrected*, *renumbered* (a
citation slip carried over under the 2017 numbers), or the 2017 statement number and page, e.g.
*(book 2017: Theorem 3.13, p. 99)*. A general remark such as "statement numbers are the
preprint's" points here instead: *(book 2017: see `BookConcordance.md`)*.

## Structural differences

- **Numbering restarted.** The preprint numbers all statements of a chapter with one counter
  (Definition 3.48, Remark 3.49, Definition 3.50, …). The 2017 text has a separate counter for each
  kind of statement, so numbers collide across kinds: Definition 3.13 (the filling, p. 97) and
  Theorem 3.13 (the implicit function theorem, p. 99) are different statements. Displayed equations
  are numbered by chapter, e.g. (3.44). Citation slips of the preprint that name the wrong kind of
  statement ("Proposition 3.40" for Theorem 3.40) survive with the new number and may now point at an
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
  the point $0$ only — so the gap of `Findings.md` item 100 is in the 2017 text as well.
- *Unchanged, checked 2026-11-02 (the points of the brief to the authors):* the sentence
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
- *Typos:* of the 26 or so preprint typos and citation slips marked in `Findings.md` and the
  chapters, one is corrected ("sunspace", p. 69) and all the others are still there, the citation
  slips renumbered; a typo that was not marked is corrected too ("kerenel" in Theorem 3.15, p. 102).
  One preprint number is left standing in the 2017 text: "In view of Lemma 3.44" (p. 115) for
  Lemma 3.7.
- *Chapter 6 (checked 2026-11-07).* Of the twelve possible misprints and omissions marked in
  `Findings.md`, Chapter 6, two are corrected: "$(f-s)'(x)$ is a sc-Fredholm operator if and only
  if $(f-s)'(x)$ is" before Definition 6.1 now has $(f-t)'(x)$ in the second place (p. 182), and
  Definition 6.39's "$y \in U_\infty$" reads "$y \in X_\infty$" (Definition 6.12, p. 213). The
  other ten are still there: in §6.7.1 (pp. 218–219) "$\det(\tau)$" for $\det(\sigma)$, "$\beta(C)$"
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

## Part II: the 2017 numbering is the only numbering (Chapter 7)

Part II, *Ep-Groupoids* (Chapters 7–11), has no 2014 preprint: the preprint arXiv 1407.3185 is
Part I alone. For Part II the book's arXiv version 1707.08941 is the text, and **its statement
numbers and printed pages are the only numbering of Part II** used in the project: in
`Findings.md` ("## Chapter 7"), `Chapter7.md`, the reports (`verification/ch07.md`, V7.1–V7.68)
and the Lean docstrings. There is nothing to concord, so this section has no preprint column; it
lists the numbered items and sections of Chapter 7 with their pages, their V-items and the Lean
files of `Polyfold/Chapter7/` that formalize them, so that a reader holding the book can find each
of them. Part I results cited in Part II carry their 2017 numbers, with the preprint number of the
Lean name in brackets where it matters (for example Theorem 2.2 [2.16], `Polyfold.theorem_2_16`).

Pages are printed pages, read off the running heads of `sources/HWZ-Book-2017.txt` (even pages
"226 7 Ep-Groupoids", odd pages "7.1 … 227"; p. 225, the first page of the chapter, has no head),
as for Chapter 6; Chapter 7 is lines 10704–12250 of that text (Part II opens at line 10687, p. 223).
Each kind of statement has its own counter (Definition 7.3 and Proposition 7.3 are different
statements). Chapter 7 has 52 numbered items: 17 definitions, 14 propositions, 10 lemmas, 6
theorems, 3 corollaries and 2 remarks. "p." is the page of the statement's heading (for a section,
of its title). The Lean files are in `Polyfold/Chapter7/`; the first one named holds the statement,
the others the notions or witnesses it uses. The verdicts are in the comparison, not here.

### Chapter 7 (arXiv 1707.08941 pp. 225–256)

| arXiv 1707.08941 | p. | V-item | Lean file | Note |
|---|---|---|---|---|
| §7.1 Ep-Groupoids and Basic Properties | 225 | — | — |  |
| Definition 7.1 | 225 | V7.1 | `Groupoid.lean` | groupoid, `mor(x, y)`, orbit space $\lvert X\rvert$, $\pi$ (pp. 225–226) |
| Definition 7.2 | 226 | V7.2 | `Groupoid.lean` | isotropy group $G_x$ |
| Definition 7.3 | 226 | V7.3 | `EpGroupoid.lean` | ep-groupoid (pp. 226–227); (4) cites "Lemma 2.8 in [38]", in the book Part I's Proposition 2.15 |
| Definition 7.4 | 227 | V7.5 | `EpGroupoid.lean`, `LocalDiffeo.lean` | $\hat\varphi$; $T\varphi$ only defined (gap G.70) |
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
| Proposition 7.9 | 242 | V7.39 | `Reduced.lean` | $\mathbf X^R$ Hausdorff and paracompact taken as hypotheses (gap G.71) |
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
(`NonVacuity.lean` and the witnesses in the other files; `Findings.md`, Chapter 7, items 100–106)
have no V-item of their own. Gaps opened in Chapter 7: G.70 (Definition 7.4, $T\varphi$ as an
sc-isomorphism), G.71 (Propositions 7.9–7.10, $\mathbf X^R$ Hausdorff and paracompact), G.72
(p. 228, $\lvert X_\infty\rvert = \bigcap_k \lvert X_k\rvert$). `verification/ch07.md` contains no
*(book?)* mark: there is no other numbering to check against.

## Marks in the report sources

The generated files (`Comparison.md`, `Comparison.json`, `Verification.md`, `ProofByProof.md`, the
HTML and PDF outputs) are not edited; they inherit the marks of their sources and are rebuilt
later. In the sources, `verification/*.md` (`ch06.md` included) and `pbp/*.md` contain no *(book?)*
mark; `cmp/ch03.json` contained seven, which now carry the annotations below (checked 2026-11-07):

| Source | Item | Text with the mark | Annotation it should get |
|---|---|---|---|
| `cmp/ch03.json`, items[19].diff[1] | V3.20, Definition 3.21 | Typo p. 77: "finite dimensional sunspace" *(book?)*. | *(book 2017: corrected, p. 69)* |
| `cmp/ch03.json`, items[25].diff[1] | V3.26, Theorem 3.29 | Typo p. 85: "δ₁ : V₁ → W₁ satisfying δ(0) = 0" for δ₁(0) = 0 *(book?)*. | *(book 2017: unchanged, p. 77)* |
| `cmp/ch03.json`, items[30].diff[0] | V3.31, Corollary 3.34 | The citation "Proposition 3.40" should be Theorem 3.40, and it is not needed *(book?)* | *(book 2017: unchanged, renumbered: "Proposition 3.11" for Theorem 3.11, p. 79)* |
| `cmp/ch03.json`, items[59].diff[0] | V3.60, Lemma 3.74 | typos "τ_n → τ'", "B(x⁰, r)" *(book?)* | *(book 2017: both unchanged, Lemma 3.24, p. 122)* |
| `cmp/ch03.json`, items[61].diff[0] | V3.62, Lemma 3.77 | The text cites "Theorem 3.73" for Proposition 3.73 *(book?)*. | *(book 2017: unchanged, renumbered: Lemma 3.26, p. 124, cites "Theorem 3.7" for Proposition 3.7)* |
| `cmp/ch03.json`, items[64].diff[0] | V3.65, Lemma 3.80 | The maximum in c(a) is over B((1 + ε)a) ∩ C, where DB is defined *(book?)* | *(book 2017: unchanged, Lemma 3.28, p. 126)* |
| `cmp/ch03.json`, items[66].diff[0] | V3.67, Lemma 3.82 | Typos in (72) *(book?)* (item 26). | *(book 2017: unchanged, Lemma 3.30, p. 128)* |

Related wording in the report generators (not a mark): `build_comparison.py` (`DEK`, `FOOT`) and
`build_verification.py` (`INTRO`) said that the preprint's numbers and pages are used "until the
book's are checked"; they now keep the preprint's numbers and point to `BookConcordance.md` for the
2017 ones, since the Springer edition is still unchecked (checked 2026-11-07). The
`confirm('… for this book?')` string in `build_signoff.py` is unrelated.
