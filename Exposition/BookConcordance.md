# Book concordance: the 2014 preprint and the book's arXiv version (Chapters 1–5)

The exposition and the formalization follow Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory
I*, in the 2014 preprint (arXiv 1407.3185, `sources/HWZ-PartI-2014.txt`); every statement number
and page in `Findings.md`, the chapters and the reports is the preprint's. The published book
(Springer 2021) is not available here. What is available is the book's arXiv version, **arXiv
1707.08941v1 (27 July 2017)**, the only version on arXiv (text in `sources/HWZ-Book-2017.txt`),
whose Part I (Chapters 1–6) corresponds to the preprint's Part I. It is
used below as the best available proxy for the book: **every result recorded here is a result about
the 2017 arXiv text, not about the Springer edition**, whose pages and late corrections may differ.
Pages of the 2017 text are its printed page numbers (Part I starts on p. 3).

**Method.** The numbered items (Definition, Lemma, Proposition, Theorem, Corollary, Remark, Example)
were extracted from `pdftotext -layout` texts of both versions with their pages, and each preprint
item was matched to a 2017 item by the text of its statement (sequence alignment within each chapter);
every weak or missing match was then checked by hand. All 236 numbered items of the preprint's
Chapters 1–5 are listed; 232 have a counterpart, 4 are absent, and the 2017 text has 31 numbered
items in Chapters 1–5 without a preprint number (listed after the tables).

**Annotation convention** (used in `Findings.md` and in `Chapter1.md`–`Chapter3.md`, where the marks
*(book?)* and "check against the book" stood): *(book 2017: …)* gives the result of the check
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
  | 6 Linearizations, Orientations, and Invariants | 200– | 6 Orientations | 181– |

  The other sections keep their titles and order. The page offset grows from 3 (Chapters 1–2) to
  16–19 (Chapters 4–6), so a preprint page does not convert by a fixed shift; use the tables.
- **Appendices.** The appendices 1.4, 2.6 and 3.8 stay at the end of their chapters. The preprint's
  appendix 5.4 is dissolved: the proof of Theorem 5.5 (= 5.1) now follows the theorem in §5.2, the
  notes on partitions of unity are §5.5, and a new §5.4 states a ∂-extension theorem for sc⁺-sections
  (Definition 5.11, Theorem 5.9) with a sketch of proof only. The preprint restates Proposition 3.22,
  Lemma 3.46, Lemma 3.55 (Appendix 3.8) and Theorem 5.5 (Appendix 5.4.1) under their own numbers; the
  2017 text restates Proposition 3.3 without a number, but Lemmas 3.9 and 3.10 as new Lemmas 3.22
  and 3.23.
- **Dropped.** Theorem 3.35 (the germ implicit function theorem over any finite-dimensional partial
  quadrant, quoted from [21], Theorem 2.7) with the paragraph introducing it; Theorem 5.25
  (perturbation into good position), Lemma 5.26 (general position implies good position; the 2017 text keeps
  its claim as one sentence without proof, p. 166) and Theorem 5.27 (cobordism between good-position
  perturbations).
- **New.** Definition 2.18 and Lemma 2.5 (an sc-smooth splicing gives a tame retraction, p. 36);
  Proposition 2.11 (a tame retraction preserves the local faces at a corner, p. 39); M⁺-polyfolds
  (Definition 4.8, Proposition 4.4, p. 146); strong bundles with reflexive $(0,1)$-fibres, mixed
  convergence and reflexive auxiliary norms (Definitions 5.2–5.4, Lemma 5.2, Proposition 5.2,
  pp. 153–154); the reflexive local compactness property and a compactness theorem near the boundary
  (Definition 5.6, Proposition 5.3, Theorem 5.4, Remarks 5.1–5.2, pp. 159–161); the ∂-extension
  theorem of §5.4; several remarks. Six paragraphs that the preprint leaves unnumbered became
  Remarks 1.1, 2.4, 3.3, 3.4, 3.7 and 4.2.
- **Hypotheses and wording.** "Tame" is dropped from the interior part of Chapter 3 (the filling,
  Definitions 3.4 and 3.13; sc-Fredholm germs and sections, Definitions 3.5, 3.7, 3.8, 3.14, 3.15;
  Theorems 3.1–3.3, Corollary 3.1, Proposition 3.5, Theorem 3.14) and kept for the boundary results
  (Definition 3.16, Theorems 3.5, 3.13, 3.15); Remark 3.9 (new) says that good position at interior
  points does not need tameness. Proposition 2.17 (= 2.57) assumes "regular Hausdorff" for "regular".
  Definition 2.25 (= 2.50) writes a strong bundle chart as $(\Phi,P^{-1}(V),(K,C\triangleleft F,
  E\triangleleft F))$ and asks for "a bounded linear isomorphism" on the fibres (the preprint: "a
  bounded linear operator"); Definition 3.3 follows. Some titles change (Theorems 3.14, 3.15, 5.6).
- **Bibliography.** Renumbered; the items cited in Chapters 1–5 include the preprint's [20] (JEMS 2007,
  "A General Fredholm Theory I") = the book's [36], [21] (GAFA 2009, "… II: Implicit Function
  Theorems") = [37], [25] (the 2010 paper, "Sc-Smoothness, Retractions and New Models for Smooth
  Spaces") = [42].

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

## Concordance, Chapters 1–5

Pages: "p." is the page of the statement's heading. "absent": no counterpart in the 2017 text.
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

## Numbered items of the 2017 text without a preprint number (Chapters 1–5)

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

## Marks in the report sources

The generated files (`Comparison.md`, `Comparison.json`, `Verification.md`, `ProofByProof.md`, the
HTML and PDF outputs) are not edited; they inherit the marks of their sources and are rebuilt
later. In the sources, `verification/*.md` and `pbp/*.md` contain no *(book?)* mark; `cmp/ch03.json`
contains seven, which should read:

| Source | Item | Text with the mark | Annotation it should get |
|---|---|---|---|
| `cmp/ch03.json`, items[19].diff[1] | V3.20, Definition 3.21 | Typo p. 77: "finite dimensional sunspace" *(book?)*. | *(book 2017: corrected, p. 69)* |
| `cmp/ch03.json`, items[25].diff[1] | V3.26, Theorem 3.29 | Typo p. 85: "δ₁ : V₁ → W₁ satisfying δ(0) = 0" for δ₁(0) = 0 *(book?)*. | *(book 2017: unchanged, p. 77)* |
| `cmp/ch03.json`, items[30].diff[0] | V3.31, Corollary 3.34 | The citation "Proposition 3.40" should be Theorem 3.40, and it is not needed *(book?)* | *(book 2017: unchanged, renumbered: "Proposition 3.11" for Theorem 3.11, p. 79)* |
| `cmp/ch03.json`, items[59].diff[0] | V3.60, Lemma 3.74 | typos "τ_n → τ'", "B(x⁰, r)" *(book?)* | *(book 2017: both unchanged, Lemma 3.24, p. 122)* |
| `cmp/ch03.json`, items[61].diff[0] | V3.62, Lemma 3.77 | The text cites "Theorem 3.73" for Proposition 3.73 *(book?)*. | *(book 2017: unchanged, renumbered: Lemma 3.26, p. 124, cites "Theorem 3.7" for Proposition 3.7)* |
| `cmp/ch03.json`, items[64].diff[0] | V3.65, Lemma 3.80 | The maximum in c(a) is over B((1 + ε)a) ∩ C, where DB is defined *(book?)* | *(book 2017: unchanged, Lemma 3.28, p. 126)* |
| `cmp/ch03.json`, items[66].diff[0] | V3.67, Lemma 3.82 | Typos in (72) *(book?)* (item 26). | *(book 2017: unchanged, Lemma 3.30, p. 128)* |

Related wording in the report generators (not a mark, not edited): `build_comparison.py` (`DEK`,
`FOOT`) and `build_verification.py` (line 44) say that the preprint's numbers and pages are used
"until the book's are checked". With this file the 2017 numbers are known; the wording could point
to `BookConcordance.md` (and keep the preprint's numbers, since the Springer edition is still
unchecked). The `confirm('… for this book?')` string in `build_signoff.py` is unrelated.
