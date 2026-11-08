# Findings: gaps, hidden hypotheses and slips in HWZ, *Polyfold and Fredholm Theory*, Part I

Collected while writing the exposition and the Lean files. Each item names where it was found
(page numbers of the 2014 preprint, arXiv 1407.3185, unless stated; "2010 paper" is arXiv
1002.3381). These feed the formalization plan and, later, the verified edition and the
comparison edition. Items that may read differently in the published book (Springer 2021), which
corrects the preprint, were marked *(book?)*. The Springer PDF is not available; every such mark has
been checked against the book's arXiv version, arXiv 1707.08941v1 (July 2017; its Part I, Chapters
1–6, is the preprint's Part I), as the best available proxy, **not** against the Springer edition,
and replaced by an annotation *(book 2017: …)*: *unchanged* (the slip or gap is still there),
*corrected*, *renumbered* (a citation slip carried over under the book's numbers), or the 2017
statement number and page (e.g. *(book 2017: Theorem 3.13, p. 99)*; pages are those of arXiv
1707.08941). Changes made after July 2017 are not covered. Statement numbers below are the
preprint's; the book numbers each kind of statement separately *(book 2017: see `BookConcordance.md`)*.

**About the text.** The sources are `pdftotext` extractions of the arXiv preprints. Sub- and
superscripts are flattened or displaced (a primed symbol `U 0` for $U'$, `Rk` for $\mathbb R^k$,
an integral sign printed as `Z`), fractions are split over lines, and a `−` can land on the wrong
operand. A formula that seems to have a wrong sign or a missing exponent is therefore treated as
a defect of the extraction unless the surrounding text is unambiguous; such items are marked
*(text?)* below.

## §1.1 Sc-structures (Chapter 1; Lean `Polyfold/Chapter1/`)

- p. 6, Definition 1.1: "a decreasing sequence of Banach spaces" leaves implicit that each $E_m$
  carries its own norm and that the inclusions are continuous (they are, being compact). The
  formalization uses an indexed family with injective compact inclusions and recovers the
  subspace picture; nothing in Chapter 1 uses more.
- pp. 6–7, Example 1.2: "one sees that the sequence defines a sc-structure" needs (i) the
  inclusion $E_{m+1}\subset E_m$, which uses $\delta_m\le\delta_{m+1}$; (ii) for compactness, a
  tail estimate that uses $\delta_{m+1}>\delta_m$ strictly, Rellich–Kondrachov on
  $(-N,N)\times S^1$ and a diagonal argument; (iii) for density, cut-offs and the density of
  $C_c^\infty$ in $H^m$; (iv) completeness of the weighted spaces (Proposition 1.C of the
  exposition). The weighted spaces are defined only in words.
- p. 7, Definition 1.5: of the conditions "closed" and "$(F\cap E_m)$ is an sc-structure", the
  closedness of $F\cap E_m$ in $E_m$ and the compactness of the inclusions are automatic; only
  the density of $F\cap E_\infty$ in $F\cap E_m$ is a condition (Lemma 2.A). Not a gap, a
  simplification the formalization uses.
- p. 7, sc-complement: "on every level $m$ we have a topological direct sum $E_m = F_m\oplus G_m$"
  silently includes $F_m+G_m = E_m$, which does not follow from $F+G = E$; and $G$ must be
  closed (it is, as $G_0$ is a Banach space). Equivalent to the existence of an sc-projection
  (Lemma 2.B); the proof of Proposition 1.6 uses this equivalence ("it is a sc-projection")
  without stating it.
- p. 8, Proposition 1.6: the continuity of $P$ on $E_m$ is asserted ("induces a continuous map
  from $E_m$ to $E_m$"); it needs $|Px|_m\le\sum\|\lambda_i\|\,|x|_0|e_i|_m$ and the continuity of
  $E_m\to E_0$.
- pp. 8–9, Proposition 1.7: the text asserts that $(E/A)_\infty$ "consists of all elements of
  the form $x+A_\infty$ with $x\in E_\infty$". Only the trivial inclusion $\supset$ is needed
  for the density claim. The equality is true but needs a Mittag-Leffler argument using the
  completeness of the $A_j$ and the density of $A_\infty$ (Lemma 2.C of the exposition). Also
  "$E_m/A_m = \{(x+A)\cap E_m\mid x\in E\}$" conflates the class $x+A_m$ with a subset of $E_m$;
  the identification $E_m/A_m\to E/A$, $x+A_m\mapsto x+A$, is injective because $A_m = A\cap E_m$.
- p. 9, after Definition 1.8: "$F = C\oplus T(E_m)$" should read $F_m = C\oplus T(E_m)$ *(book 2017: unchanged, p. 6, after Definition 1.5)* *(book 2021: unchanged, p. 9, after Definition 1.1.9)*.
  (Machine-checked in the round-trip audit: read literally in $F_0$, the formula for
  $T = \mathrm{id}$ forces every inclusion $E_m\to E_0$ to be onto, hence every sc-Banach space to
  be finite-dimensional; refuted with $E_m = \ell^2$ and inclusions $\mathrm{diag}(2^{-k})$,
  `RoundTrip/Items/V1_7.lean` and `V1_29.lean`, `not_B`.)
  Not stated: $T:E_m\to F_m$ is Fredholm on every level with kernel $K$, image $Y_m$ and the same
  index (Lemma 2.D).
- p. 9, Proposition 1.9: the step "$c = 0$" uses $C\cap T(E_0) = 0$, i.e. that $F_0 = C\oplus Y$
  is direct; fine, but implicit.
- pp. 14–15, proof of Proposition 1.10: (i) "since $T$ is regularizing, we conclude that
  $e\in E_m$": the hypothesis gives $Te = y-Se$ with $Se\in F_1$ only, so $e\in E_1$; one must
  bootstrap ($Se\in F_2$, $e\in E_2$, …). (ii) Condition (3) of Definition 1.8, that
  $T+S:X\to Y$ is an sc-*isomorphism*, is not verified; it needs the open mapping theorem on each
  level. (iii) The statement does not record that the index is preserved; it is, by the classical
  theorem on level $0$. (iv) The classical facts used (closed range, compact perturbation
  preserves the Fredholm property) are not cited; the exposition cites Kato IV.5.26.
- p. 10, Definition 1.11: "closed convex" is a consequence of the model $[0,\infty)^n\oplus W$,
  not an extra condition. That $C\cap E_k$ is a partial quadrant in $E^k$ (used constantly: $TC
  = C^1\oplus E$) is never stated (Lemma 3.A(2)).
- p. 10, Definition 1.12: "$f(U_m)\subset V_m$" with $V$ undefined; $V = U'$ *(book 2017: unchanged, Definition 1.7, p. 7)* *(book 2021: corrected, Definition 1.1.13, p. 9: the target sc-triple is now written with $V$ as its first entry; its third entry, the ambient space, is also printed $V$, a possible misprint)*.
- p. 10, Definition 1.13: $TC = C^1\oplus E$ is said to be a partial quadrant in $TE$; this needs
  a reordering of summands, $TE\cong\mathbb R^n\oplus(W^1\oplus\mathbb R^n\oplus W)$ (Lemma 3.B).
- pp. 10–11, Definition 1.14: the operator $Df(x)$ is unique only because $E_1$ is dense in $E_0$
  (axiom (2) of Definition 1.1) and the quadrant has non-empty interior; without uniqueness "the
  tangent map $Tf$" in condition (3) is not defined. Not mentioned (Lemmas 3.D–3.E). For the
  partial cones of Remark 1.15 the non-empty interior is exactly what saves this.
- p. 11: "if we equip it with the compact open topology it will be continuous" — true, and
  equivalent to condition (3) at level $0$ (Lemma 3.F); the remark that "the sc$^1$-maps between
  finite dimensional Banach spaces are the familiar $C^1$-maps" is true with one-sided derivatives
  at boundary points of the quadrant. The notion "$C^k$ on a relatively open subset of a partial
  quadrant", used throughout §1.2, is never defined; the exposition fixes it (Definition 3.C) and
  proves uniqueness of derivatives there. The text's sentence before, that $x\mapsto Df(x)$ is "in
  general" *not* continuous for the operator norm, has no example in the Lean project: round-trip
  items V1.13 and V1.34 find it the only part of the remarks after Definition 1.14 that the project
  does not give (the compact-open continuity and "sc$^1$ = $C^1$ in finite dimensions" follow,
  `RoundTrip/Items/V1_13.lean`, `A_to_Bbc`). The standard example, the shift map (2010 paper,
  Example 1.7; exposition §6), whose derivative contains the translations, is not formalized.

## §1.2 Properties of sc-differentiability (proofs in the 2010 paper, §2.1)

- p. 12, Proposition 1.16: the symbol $Df(x)$ in condition (2) is used for all $m$ as if it were
  one operator; that the extensions at different levels agree needs the density of $E_m$ in
  $E_{m-1}$ (Lemma 3.H). The 2010 paper (Proposition 2.1) calls the direction "(1),(2) imply
  sc$^1$" clear; this is the point it hides.
- 2010 paper, Proposition 2.1, proof: the step "$f:U_{m+1}\to F_m$ is differentiable" uses the
  integral identity $f(x+h)-f(x) = \int_0^1Df(x+\tau h)h\,d\tau$ in $F_m$; it is established in
  $F_0$ (from the $C^1$ property of $f:U_1\to F_0$) and holds in $F_m$ because the integrand is
  continuous into $F_m$ and the inclusion commutes with the integral — not said. The segment
  $x+\tau h$ must lie in $U_{m+1}$: convexity of $C$ and relative openness. "The integrand
  converges uniformly in $\tau$" needs the joint continuity of $(y,k)\mapsto Df(y)k$ spelled out,
  and the conclusion for the full sequence needs the subsequence principle.
- 2010 paper, Proposition 2.2 (= 1.17): the inductive step uses $T(U^1) = (TU)^1$ and that the
  derivative of $f:U^1\to V^1$ is the restriction of $Df$ — the latter by uniqueness.
- 2010 paper, Proposition 2.3 (= 1.18): the map $\Gamma$ is introduced as "linear in $h$ and
  continuous"; its boundedness as a $(k+1)$-linear map and the identification of
  $D_x^k[f(x+\delta x)-f(x)]$ with an integral of $\Gamma$ need differentiation under the integral
  sign (continuity of the $x$-derivatives jointly in $(t,x)$), not mentioned. The reduction "it
  suffices to show $f:U_k\to F_0$ is $C^k$" uses Proposition 2.2 $m$ times.
- 2010 paper, Proposition 2.4 (= 1.19): the inductive statement $(\mathrm S_k)$ carries index
  constraints $j+l-1\le n_i\le k$; the case $j = 0$ (the map $x\mapsto f(x)$, $U^{k+1}\to F^l$)
  needs $l\le k+1$, which is not written. The verification "one checks that the new indices satisfy
  the required inequalities" is done in the exposition. The derivatives $d^jf(x)$ at different
  levels are tacitly identified (compatibility by uniqueness). **Proved in Lean under the text's
  hypothesis** (2026-10-25): `Polyfold.proposition_1_19_text` and `Polyfold.corollary_1_20_text`
  in `Chapter1/LevelsWeak.lean`; the elementary maps of $(\mathrm S_k)$ are `Polyfold.ElemData`,
  the compatibility of the $d^jf(x)$ is the field `IsDerivTower.toBase`. The upper bound
  $n_i\le k$ of $(\mathrm S_k)$ is not needed: only $j+l-1\le n_i$, $j+l\le p$ (the level of the
  base point) and $j\le k$ enter.
- p. 13, Corollary 1.20 and Proposition 1.18 together: sc-smooth implies $f:U_l\to\mathbb R^N$ is
  $C^l$, while $C^{l+1}$ on $U_l$ for all $l$ implies sc-smooth. The two conditions differ by one
  order; neither text claims they coincide. (Recorded so that no one "simplifies" the corollary
  to an equivalence.)

## §1.3–1.4 Chain rule, degeneracy index, boundary recognition

- p. 15, proof of Theorem 1.21: (i) "$tf(x+h)+(1-t)f(x)\in V_1$" needs the convexity of $D$ and
  the continuity of $f:U_1\to F_1$. (ii) Proposition 1.18 is quoted to make $g:V_1\to G_0$ of
  class $C^1$; this is not needed — the segment integral follows from Definition 1.14 (2),(3)
  for $g$ directly, so the chain rule rests on the definition and the compactness axiom alone.
  (iii) "converges to 0 as $|h|_1\to0$ uniformly in $t$" (twice) is the joint continuity of
  $(y,k)\mapsto Dg(y)k$ at $(f(x),0)$, resp. at $(f(x),Df(x)k)$, with the subsequence principle
  for the second integral. (iv) "$T(g\circ f) = Tg\circ Tf$" needs the uniqueness of
  $D(g\circ f)(x)$. (v) In display (1) of the preprint the integrand carries the factor
  $1/|h|_1$ inside; harmless.
- p. 17, proof of Lemma 1.24: (i) "$S(\{0\}^k\oplus W)\subset\{0\}^{k'}\oplus W'$ and since $S$ is
  an isomorphism, we obtain equality" — for infinite-dimensional $W$ the inclusion alone does not
  give equality; one needs the same argument for $S^{-1}$ (or the codimension comparison). The
  same remark applies to "$S(E_x)\subset E'_y$ … we obtain $S(E_x) = E'_y$". (ii) "$x+tu\in
  [0,\infty)\oplus W$" should be $[0,\infty)^k\oplus W$ *(text?)*. (iii) The proof uses only that
  $S$ is a linear isomorphism of level $0$ carrying one quadrant onto the other: the degeneracy
  index does not depend on the sc-structure.
- p. 14, Theorem 1.25: no proof; "a more general result is given in [20], Theorem 1.19". In the
  2010 paper the retract version is Theorem 1.19 (Boundary Recognition); whether [20] in the
  preprint's bibliography is the 2010 paper or the 2007 JEMS paper is to be checked *(book 2017:
  Theorem 1.2, p. 11, "[36], Theorem 1.19"; the book's [36], like the preprint's own [20], is the
  2007 JEMS paper "A General Fredholm Theory I"; the 2010 paper is the book's [42])* *(book 2021: unchanged, Theorem 1.3.5, p. 14, "[54], Theorem 1.19": [54] is the 2007 JEMS paper, the 2010 paper is [60]; a new sentence points to Section 2.4 for retracts)*.
  The proof (exposition §5) needs: the chain rule, to make $Df(x)$ a linear isomorphism of level
  $0$ at a smooth point; the density in $C$ of smooth points with the same degeneracy index; and
  the upper semicontinuity of $d_C$ (Lemma 5.A). Only the sc$^1$ property of $f$ and $f^{-1}$ is
  used. The notion "germ of a local sc-diffeomorphism" is not defined in Chapter 1.
- p. 14, after Definition 1.23: "points with $d_C(x) = 0$ are interior points" — interior in
  $E_0$; on higher levels $C_m$ has the same interior points relative to $E_m$.

## The shift map (2010 paper, §1.1 Example 1.7 and §4.1; exposition §6)

- 2010 paper, p. 7: the shift map "is clearly not differentiable in the classical sense". The
  exposition proves it (Proposition 6.E): for $u\in E_m$ with a jump in $\partial_s^mu$ the
  difference quotients in $E_m$ grow like $R^{-1/2}$; for the step, $\|u(\cdot+R)-u\|_{L^2} =
  \sqrt{2R}$ exactly, and for the tent $\|u(\cdot+R)-u-Ru'\|_{L^2} = \sqrt2R^{3/2}$ (checked
  numerically by `fig1-shift.py`).
- 2010 paper, Proposition 4.1, proof: "$e^{\delta_mR}<9$" and "$<10\varepsilon$" are loose
  constants (the natural ones are $2$ and $6\varepsilon$); the final reduction to $(0,0,u_0)$
  uses $\tau_a u-\tau_{a_0}u_0 = \tau_{a_0}(\tau_{a-a_0}u-u_0)$ and the bound
  $|\tau_{a_0}|\le e^{\delta_m|R_0|}$ on level $m$, not written. The sentence "$|(R,\vartheta)\ast u
  -u_0|_m\le e^{\delta_m|c|}\cdot|u-v|_m+\dots$" has an undefined $c$ *(text?)*.
- 2010 paper, Proposition 4.2, proof: the expression "$\Phi(R_1,\vartheta_1,u)-u-R_1\cdot u_s+
  \vartheta_1\cdot u_t$" should read $-R_1u_s-\vartheta_1u_t$ throughout *(text?)*; the identity
  $\tau_bu-u-b\cdot\nabla u = \int_0^1[\tau_{\theta b}(b\cdot\nabla u)-b\cdot\nabla u]\,d\theta$ is
  extended from $C_c^\infty$ to $E_1$ by "letting $n\to\infty$", which needs both sides to be
  continuous linear maps $E_1\to E_0$. The compactness argument for the term $\tau_bv-v$ is
  complete.
- 2010 paper, Proposition 4.2, induction: the claim that $(a,u,h)\mapsto(a,h_1\cdots h_{|\alpha|}
  D^\alpha u)$ "is clearly sc$^\infty$" is Proposition 1.19 applied to a map that is a bounded
  polynomial on every level. The exposition gives this step and outlines the rest of the
  induction, which is not reproved.

## Numbering and pages *(book 2017: see `BookConcordance.md`)*

- All statement numbers above are the preprint's (Definitions 1.1–1.15, Propositions 1.6–1.10
  and 1.16–1.19, Corollary 1.20, Theorem 1.21, Remark 1.22, Definition 1.23, Lemma 1.24,
  Theorem 1.25); the preprint's Chapter 1 occupies pp. 6–17, §1.1 pp. 6–11, §1.2 pp. 12–13,
  §1.3 pp. 13–14, §1.4 pp. 14–17. The book is expected to renumber and to have fixed some of the
  slips above; each item marked for the book has been re-checked there *(book 2017: renumbered,
  Chapter 1 = pp. 3–14, see `BookConcordance.md`; the marked slips of Chapter 1 are unchanged)* *(book 2021: renumbered with three-level numbers, Chapter 1 = pp. 5–19; of the marked slips of Chapter 1 Definition 1.1.13 is corrected, the others are unchanged)*.
- **What the 2017 version changes** (checked against arXiv 1707.08941v1, July 2017, the book's
  arXiv version, as a proxy for the Springer edition, which was not available; the statement map
  and the structural differences are in `BookConcordance.md`). The 2017 text is a revision, not a
  reprint: every kind of statement has its own counter (Definition 3.13 and Theorem 3.13 coexist),
  Chapter 2 is retitled "Retracts" and Chapter 4 "Manifolds and Strong Retracts", the appendix §5.4
  is dissolved (the proof of Theorem 5.5 moves into §5.2, the notes on partitions of unity become
  §5.5, a new §5.4 states a ∂-extension theorem for sc⁺-sections with a sketch of proof), Theorem 3.35,
  Theorems 5.25, 5.27 and Lemma 5.26 are dropped, and there is new material: Definition 2.18 and
  Lemma 2.5 (splicings give tame retractions), Proposition 2.11 (a corner retraction preserves the
  local faces), M⁺-polyfolds (Definition 4.8, Proposition 4.4), reflexive auxiliary norms and a
  compactness theorem near the boundary (§§5.1–5.2), and several new remarks. "Tame" is dropped
  from the interior part of Chapter 3 (the filling, sc-Fredholm germs and sections, Theorems 3.1–3.3
  = 3.12, 3.15, 3.18) and kept for the boundary results; Proposition 2.17 (= 2.57) now assumes
  "regular Hausdorff"; Definition 2.25 (= 2.50) asks for a "bounded linear isomorphism" on the
  fibres. **Of the 22 specific marks of this file, one slip is corrected** ("sunspace", p. 69),
  **two questions are answered by new material** (splicings are tame, Lemma 2.5; the key step of
  Lemma 2.40, Proposition 2.11), **and 19 are unchanged**: all the other typos (Chapter 1 p. 6 and
  Definition 1.7; Proposition 2.1 "ψ(0) = x", Theorem 2.1 "(O'',C',E'')", Definition 2.5
  "p'∘Φ = p", Definition 2.24 "K(0)"; p. 77 "δ₁ … δ(0) = 0"; Theorem 3.10 "(V, 0)", the proof of
  Theorem 3.12 "δ(a) = 0", Lemma 3.7 "P'∘g(0)", the appendix proofs of Lemmas 3.9, 3.24, 3.26, 3.28,
  3.30, Definition 3.17), and the gaps (Theorem 1.2 still without proof; Proposition 2.5 (1)'s
  appendix proof; Definition 2.25's base homeomorphism and `[1]`-transition; Corollary 3.1). The
  proof of Proposition 1.4 (= 1.10, pp. 11–12) is verbatim the preprint's, with the same missing
  bootstrap; Theorem 3.8 (= 3.30) and Lemmas 3.14–3.15 (= 3.62–3.63) are still quoted from [37]
  (= the preprint's [21]). **Citation slips survive the renumbering, some now pointing at a
  different statement**: "Proposition 3.11" for Theorem 3.11 (p. 79), "Corollary 3.2" for
  Proposition 3.2 (p. 84; the book's Corollary 3.2 is the boundary implicit function theorem
  corollary), "Theorem 3.7" for Proposition 3.7 (p. 124), "Theorem 2.7" for Lemma 2.7 (p. 55; the
  preprint's "Theorem 2.56", so a slip of the source, not of the extraction), and in the proof of
  Theorem 3.13 "Theorem 3.6" for the preprint's Corollary 3.47 (= Corollary 3.6; the book's Theorem
  3.6 is the preprint's Theorem 3.27); one preprint number is left standing: "Lemma 3.44" for
  Lemma 3.7 in the appendix proof of Lemma 3.9 (p. 115). **The gap of item 100 of Chapter 3 is
  unchanged**: the book's Theorem 3.13 (= 3.54, p. 99) still proves property (4) with "Property (4)
  follows from Corollary 3.5 and from the following lemma" (p. 101; Corollary 3.5 = 3.41, p. 87,
  gives the surjectivity of the filled `Df(a, w)` at the nearby zeros, the lemma is Lemma 3.10 =
  3.55), and the filling, Definition 3.13 (= 3.48, p. 97, only "tame" dropped), still imposes
  condition (3), the isomorphism `ker Dr(0) → ker ρ(0)`, at the point `0` only. So the surjectivity
  of `f'(y)` at the nearby zeros has the same gap in the 2017 text as in the preprint.

## From the Lean proofs of Chapter 1 (2026-10-24)

- §1.4.1, proof of Proposition 1.10: "`y = (T + S)e`, so by Proposition 1.9 `e ∈ E_m`" needs a
  bootstrap: `Se` is only one level up, so the regularizing step must be iterated `m` times
  (`Polyfold.ScPlus.regularizing_add`); the same for `K_m = K_{m+1}`.
- §1.4.1 opens with the compact perturbation theorem for Fredholm operators, quoted as classical;
  Mathlib has no Fredholm operators, so it is proved here (`Polyfold/Chapter1/FredholmPerturbation.lean`,
  Riesz–Schauder through Riesz's lemma and quasi-inverses).
- §1.4.2, proof of the chain rule: the first integral representation is unnecessary (boundedness of
  `Dg(f(x))` suffices), and the step placing the segment from `f(x)` to `f(x+h)` in `V₁` uses the
  convexity of the quadrant and the openness of `V₁`, neither of which the text mentions. The
  formal proof replaces the integrals by the one-dimensional mean value inequality.
- Lemma 1.24: the equality `k = k'` of the numbers of quadrant directions is not needed for the
  index to be well defined; it follows from the lemma at `x = 0` (`Polyfold.lemma_1_24_dim`).
- Proposition 1.7 holds for every closed subspace `A`, not only for sc-subspaces.
- Theorem 1.25 (boundary recognition) is stated with a reference to another paper ("[20],
  Theorem 1.19", a retract version). It is proved, for sc¹ germs (stronger than the text's
  sc-smooth ones), in `Polyfold/Chapter2/DegeneracyIndex.lean` (`Polyfold.theorem_1_25`), by the
  argument of §2.3 for the identity retraction; level-1 points suffice where the exposition uses
  smooth points. *(book 2017: unchanged; the book does not give the quadrant proof either:
  Theorem 1.2, p. 11, still refers to "[36], Theorem 1.19")* *(book 2021: unchanged, Theorem 1.3.5, p. 14, has no proof and cites "[54], Theorem 1.19", but now points to Section 2.4, where Corollary 2.4.13, p. 51, gives the quadrant case)*.

## From the Lean proofs of Chapter 1, continued (Levels.lean)

- Proposition 1.16, converse direction: that the derivatives `Df(x)` taken on different levels are
  restrictions of one operator is asserted implicitly; it is needed and proved
  (`Polyfold.IsSc1Levels.toBase_apply`).
- Propositions 1.19–1.20 in `Levels.lean` are formalized under the stronger hypothesis that every
  level map `U_m → F_m` is `C^{k+1}` (`Polyfold.proposition_1_19`, `corollary_1_20`,
  `corollary_1_20_base`, `IsScSmooth.of_contDiffOn_finiteDimensional`). **Withdrawn as a gap
  (2026-10-25):** the text's hypothesis (`f : U_{m+l} → F_m` of class `C^{l+1}` for all `m` and
  `l ≤ k`) is sufficient and is now proved as stated, `Polyfold.proposition_1_19_text`, with
  Corollary 1.20 as stated (`C^{l+1}` on `U_l` for `l ≤ k`, `Polyfold.corollary_1_20_text`) and the
  exposition's "`C^{l+1}` on `U_l` for every `l` implies sc-smooth"
  (`Polyfold.IsScSmooth.of_contDiffOn_levels_finiteDimensional_text`), all in
  `Chapter1/LevelsWeak.lean`, by the `(S_k)` induction of the 2010 paper.

## Chapter 1: consistency of exposition, Lean and reports (2026-10-24)

The report build found statements of `Exposition/Chapter1.md` without a Lean counterpart. They are
now proved, except as listed at the end; `Chapter1.md` names the declarations in its paragraphs
"*Checked by machine*", and the reports have the items V1.28–V1.36.

- Proposition 1.10 and Lemma 2.D (the index): `ind(T + S) = ind(T)`
  (`Polyfold.proposition_1_10_index`) and every level map of an sc-Fredholm operator is Fredholm of
  index `ind(T)` (`Polyfold.ScFredholmSplitting.fredholmIndex_lvl`,
  `Polyfold.proposition_1_10_index_lvl`). Mathlib has Fredholm operators but no index; the index,
  its additivity and its invariance under small and compact perturbations are built in
  `Polyfold/Chapter1/FredholmIndex.lean` (`Polyfold.fredholmIndex_add_isCompactOperator`, by local
  constancy along `u + tk`, not by Kato's argument). The text itself never states that the index
  is preserved.
- Lemma 1.A(2)–(3) (p. 6, "precisely one sc-structure"): for indexed families, "precisely one" is
  read as "the inclusions form an sc-isomorphism with the constant structure"
  (`Polyfold.ScBanach.isoConstOfFiniteDimensional`), and "the constant structure fails (1)" as "an
  onto inclusion forces finite dimension" (`Polyfold.ScScale.finiteDimensional_of_surjective_incl`).
- Lemma 2.B (sc-splittings = sc-projections, used in the proof of Proposition 1.6):
  `Polyfold.ScBanach.isScSplitting_iff_exists_scProj`; idempotence on level 0 suffices
  (`Polyfold.ScOperator.idem_lvl`).
- Lemma 2.C (p. 9, the smooth points of a quotient): `Polyfold.ScBanach.exists_smooth_mem_coset`,
  `Polyfold.ScBanach.mk_mem_quotient_smooth_iff`. The formal construction bounds all inclusions
  `E_j → E_i` (`i ≤ j`) by `∏_{i<j} max(1, ‖E_{i+1} → E_i‖)`, which avoids comparing the levels
  `J + k` and `j` in a dependent type.
- Lemmas 3.A(2) and 3.B (`C¹` a partial quadrant in `E¹`, `T(U, C, E)` a tuple) were already proved
  with Chapter 2 (`Polyfold.IsPartialQuadrant.shift`, `Polyfold.IsPartialQuadrant.tangentSet`); the
  earlier reports called them not formalized.
- Lemma 3.F (p. 11, compact-open continuity): an equivalence with joint continuity
  (`Polyfold.continuousOn_apply_iff_uniformOnCompact`).
- p. 11, "sc¹ maps between finite dimensional Banach spaces are the familiar `C¹` maps": proved on
  every sc-domain, in particular on relatively open subsets of quadrants, with Mathlib's `C¹`
  within `U` (`Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant`,
  `Polyfold.isSc1_iff_fderivWithin_const`): at a boundary point the derivative is the one along
  `U`, i.e. the one-sided derivative, unique because the quadrant has interior. The earlier Lean
  version was for open sets only.
- Still not formalized, and so marked in the exposition: Example 1.2 and Proposition 1.C (no
  weighted Sobolev spaces or Rellich–Kondrachov in Mathlib), the application §6 (the shift map),
  hence the negative half of the remark after Definition 1.14 (`x ↦ Df(x)` need not be norm
  continuous; proved since 2026-11-01 by a sequence-space example, follow-up item 1 below) and the
  last sentence of Lemma 3.F; Remark 1.15 (partial cones). (Proposition 1.19
  and Corollary 1.20 under the text's hypotheses, listed here on 2026-10-24, were formalized on
  2026-10-25; see the next section.)

## From the Lean proofs of Chapter 1, Proposition 1.19 under the text's hypothesis (2026-10-25,
LevelsWeak.lean)

- The text's hypothesis of Proposition 1.19 (`f : U_{m+l} → F_m` of class `C^{l+1}` for all
  `m ≥ 0`, `0 ≤ l ≤ k`) suffices for sc^{k+1}: `Polyfold.proposition_1_19_text`. No additional
  hypothesis is needed beyond `IsScDomain E U` (as everywhere in Chapter 1) and `f` sc⁰ (which the
  text's `f : U → V` presupposes). Corollary 1.20 as stated: `Polyfold.corollary_1_20_text`.
- The induction cannot be run on the hypothesis itself: if `f` satisfies the hypothesis with `k`,
  the tangent map `Tf` does **not** in general satisfy it with `k − 1` (its second component
  `(x, h) ↦ Df(x)h : U_{m+l+1} × E_{m+l} → F_m` is only `C^l`, one order short, since `Df(x)h` for
  `h ∈ E_{m+l}` is the derivative of the `C^{l+1}` map `f : U_{m+l} → F_m`). This is why the
  2010 paper's inductive statement `(S_k)` carries the explicit description of the components of
  `T^{k+1}f` as the "elementary maps" `(x, h₁, …, h_j) ↦ d^j f(x)(h₁, …, h_j)` on mixed levels;
  the Lean proof follows it (`Polyfold.ElemData`, `ElemData.isSck`).
- What `(S_k)` needs about the derivatives is exactly: `d^i f(x)` exists as a continuous
  `i`-linear map on `E_{m+l}` into `F_m` for `i ≤ l + 1`, is differentiable in `x` for `i ≤ l`
  with derivative `d^{i+1}f(x)`, and these maps for different `(m, l)` are restrictions of one
  base-level map (`Polyfold.IsDerivTower`). The last point is the text's tacit identification of
  `d^j f(x)` across levels; it is proved from the chain rule for compositions with the inclusions
  (`iteratedFDerivWithin_comp_left/right`), `Polyfold.isDerivTower_of_contDiffOn_levels`.
- The index conditions of `(S_k)` are `j + l − 1 ≤ n_i` and (implicitly) `j + l ≤ k + 1` for the
  base-point level; the upper bound `n_i ≤ k` of `(S_k)` plays no role (the Lean `ElemData.Good`
  has `m + i ≤ p`, `m + i ≤ n_a + 1`, `i ≤ k`).
- The sc¹ step for an elementary map is Proposition 1.16's level criterion (`IsSc1Levels`): the
  derivative (3.5) of the exposition exists one level down because `d^{i+1}f` and `d^i f` exist
  one level down; it uses the derivative of the evaluation `(A, h) ↦ A h` of multilinear maps
  (`Polyfold.hasFDerivAt_cmm_eval`, not in Mathlib in this form).
- Organization: `Chapter1/LevelsWeak.lean` imports `Chapter2/StrongBundle.lean` for the pairing
  of sc^k maps (`IsSck.scPair`) and the sc-smoothness of sc-operators (`ScOperator.isScSmooth`),
  Chapter-1 facts that live in Chapter 2 files.

## Chapter 1: follow-ups of the round-trip audit (2026-11-01)

Numbering: the earlier Chapter 1 entries are unnumbered; the follow-ups of the round-trip audit
(`RoundTrip/`) are numbered from 1.

1. **The remark after Definition 1.14, "in general `x ↦ Df(x)` is not continuous into `L(E₀, F₀)`
   with the operator norm", is now proved by an example (round-trip items V1.13, V1.34).**
   `Polyfold.exists_isSc1_not_continuousOn_deriv` (`Chapter1/ScOneNotNormContinuous.lean`): there
   are sc-Banach spaces `E`, `F`, a relatively open `U` in a partial quadrant `C ⊆ E` (here
   `U = C = E₀`) and an sc¹ map `f : U → F` such that for **every** derivative family `D` of `f`,
   `x ↦ D x` is not continuous on `U₁` into `L(E₀, F₀)` with the operator norm. The text gives no
   example. The one built here: `X` (`Polyfold.ScOneExample.X`), the sequences with
   `(k+1)^m x_k → 0`, `|x|_m = sup_k (k+1)^m |x_k|`, every level represented by `c₀ = C₀(ℕ, ℝ)` in
   the coordinates `(k+1)^m x_k`, so that `X_{m+1} → X_m` is `diag(1/(k+1))` — compact as a norm
   limit of finite-rank truncations, and the finitely supported sequences are smooth points dense
   in every level; it is the project's first infinite-dimensional sc-Banach space. Then
   `E = ℝ ⊕ X`, `F = X`, `f(t, x)_k = cos(kt) x_k`. `ScOneExample.isSc1With`: `f` is sc¹ with
   `Df(t, x)(τ, ξ)_k = −k sin(kt) x_k τ + cos(kt) ξ_k` for `(t, x) ∈ E₁` — the factor `k` of the
   `t`-derivative is absorbed by one level, and the remainder is `o(|τ| + |ξ|₁)` on level `0`
   because the multipliers `(k+1)⁻¹((cos(k(t+τ)) − cos(kt))/τ + k sin(kt))` are bounded by `2` and
   tend to `0` for each `k`, while the tail of `(k+1)x_k ∈ c₀` is small. Every level map of `f`
   and `Tf` is the same formula, because diagonal operators commute with the weights.
   `ScOneExample.not_continuousAt_D`: `(π/(n+1), 0) → 0` in `E₁`, but
   `‖Df(π/(n+1), 0) − Df(0, 0)‖ ≥ |cos(π) − cos(0)| = 2` (test on the unit vector `e_{n+1}`); and
   the derivative of an sc¹ map is unique on `E₁` (`IsSc1With.eq_of_uniqueDiffWithinAt`), which
   gives the statement for every `D`. Not proved: that `f` is sc-smooth (all its iterated tangent
   maps are of the same diagonal kind, so it is). The text's own instances of the phenomenon (the
   shift map on weighted Sobolev spaces, §6 of the exposition) still need Sobolev spaces.

## From the Lean proofs of Chapter 2 (2026-10-24)

- Lemma 2.29 / Theorem 2.31: "the closure of `(T^R_xO)_∞` is `T^R_xO`" is asserted without proof;
  it is needed because sc¹-differentiability is only along `E₁`. Proved for kernels of finite-rank
  operators; the smoothness of the point `x` is never needed in §2.3, level 1 suffices.
- Definitions 2.13–2.14: the independence of sc-smoothness from the chart, and its well-definedness
  over an equivalence class of atlases, need the locality of sc-smoothness and a gluing through the
  chain rule (`Polyfold.IsScSmooth.of_locally`, `Polyfold.MChart.compatible_of_locally`); the text
  says "independent of the choice" without argument.
- Definition 2.14 presupposes that `f` is continuous (charts with `f(V) ⊆ V'` must exist).
- Theorem 2.8 "follows from Theorem 1.21" also needs `r' ∘ f ∘ r = f ∘ r` and the restriction of
  sc^k maps to smaller domains, both unstated.
- Proposition 2.21: the paracompactness of a sub-M-polyfold `A` is not addressed (it needs
  Theorem 2.16). Now proved for every subset of an M-polyfold
  (`Polyfold.MPolyfold.paracompactSpace_subtype`, item 9 of the §2.4–§2.5 list below).
- Theorem 1.25 is deferred to "[20], Theorem 1.19", but its proof is exactly the argument of §2.3
  (`Polyfold.theorem_1_25`, for sc¹ maps; proved).
- Typos *(book 2017: all three unchanged, Theorem 2.1, p. 18; Proposition 2.3, p. 17; Lemma 2.6,
  p. 41)* *(book 2021: two unchanged, Theorem 2.1.15, p. 28, and Lemma 2.5.12, p. 59; one corrected, the proof of Proposition 2.1.13, p. 27, now has `→ E'`)*: Theorem 2.8 writes `(O'', C', E'')` for `(O'', C'', E'')`; Proposition 2.6 writes
  `f ∘ r ∘ s : V → F` for `→ E'`; Lemma 2.40 mixes `X` and `O`.

## Chapter 2 (Differential geometry based on retracts; exposition `Chapter2.md`)

Page numbers are the preprint's (§2.1 pp. 18–22, §2.2 pp. 23–31, §2.3 pp. 31–38, §2.4 pp. 38–47,
§2.5 pp. 48–53, appendix §2.6 pp. 54–60). Statement numbers 2.1–2.57 are the preprint's *(book 2017: see `BookConcordance.md`)*.

- p. 18, Proposition 2.2: "$\psi(0) = x$" should be $\psi(x) = 0$ ($\psi:V\to W$ with $x\in V$,
  $0\in W$) *(text?)* *(book 2017: unchanged, Proposition 2.1, p. 15)* *(book 2021: unchanged, Proposition 2.1.2, p. 22)*. In the appendix proof (pp. 54–55) the remainder estimate (22) is
  stated for a fixed base point but used uniformly in $x\in B(\delta)$; it needs the mean value
  inequality with (19). The constants ($\tfrac13$ in (19), $\tfrac43$ in (24)) are correct; the
  exposition uses $\tfrac14$ and concludes $|b|\le\tfrac78|b|$ instead.
- p. 19, Proposition 2.4: "$r'\circ r = r$" needs $O\subset U'$ for the composition to be defined,
  and the sc-smoothness of $r:U\to U\cap U'$ (locality). Not said. The proof is otherwise complete.
- p. 21, Theorem 2.8: "$(O'',C',E'')$" should be $(O'',C'',E'')$ *(text?)* *(book 2017: unchanged, Theorem 2.1, p. 18)* *(book 2021: unchanged, Theorem 2.1.15, p. 28)*.
- p. 22, Definition 2.9: the bundle-map condition "$p'\circ\Phi = p$" should read
  $p'\circ\Phi = a\circ p$ *(book 2017: unchanged, Definition 2.5, p. 19)* *(book 2021: unchanged, Definition 2.1.16, p. 29)*.
- p. 24, Definition 2.14: "the definition does not depend on the choice of charts" — by Theorem
  2.8; also $f$ must be continuous for charts with $f(V)\subset V'$ to exist.
- p. 25: "this definition [of level $m$] is independent of the choice of a chart" — needs that the
  transition maps composed with a retraction are $\mathrm{sc}^0$ (Lemma 2.A of the exposition); that
  $\mathcal B$ is a basis of a topology on $X_m$ (Lemma 2.B) is asserted without proof.
- p. 25, Theorem 2.16: the topology on $X_\infty$ is never defined; the metric at the end of the
  proof (p. 57) induces the initial topology of the inclusions $X_\infty\to X_m$, which is what the
  exposition takes as the definition.
- p. 57, proof of Theorem 2.16: Proposition 2.57 requires the ambient space to be regular; the
  regularity of $X_m$ (for $m\ge1$, whose topology is finer than that of $X$) is not shown. The
  exposition proves it from the metrizability of $X$ (shrink a chart neighbourhood in $X$ first).
  "Since $U^j_m$ is metrizable, it is also paracompact" is Stone's theorem, not cited. "Theorem
  2.56" is Lemma 2.56 *(text?)*. The Lean proof needs neither regularity nor Lemma 2.56 and
  Proposition 2.57: it pulls back a partition of unity of $X$ (item 9 of the §2.4–§2.5 list below).
- p. 26, Definition 2.18: that the relation on tuples is an equivalence relation and that the
  transition maps $T(\varphi\circ\psi^{-1})(\psi(x))$ are linear homeomorphisms (sc-isomorphisms at
  smooth points) is not stated; it is the chain rule for retracts (Lemma 2.C of the exposition).
- p. 58, proof of Proposition 2.19(1): "$W'_i = [T(\varphi_i\circ\varphi^{-1})(\varphi(x))]^{-1}(W_i)$"
  takes the preimage under the *linearization at one point*, which is a linear map on a fibre, not a
  map on $TO_i$; the preimage must be under the map $T(\varphi_i\circ\varphi^{-1})$ on the open set
  $T\varphi(TV\cap TV_i)$ (that this set is open in $TO$ is also needed). *(book 2017: unchanged,
  Appendix 2.6.3, proof of Proposition 2.5 (1), p. 54)* *(book 2021: unchanged, Appendix 2.7.3, proof of Proposition 2.3.15 (1), p. 76)*
- p. 59, proof of Proposition 2.19(2): "$\pi:TO\to O_1$ … is continuous and open" — openness is not
  formal, because the fibres $T_xO$ vary with $x$; it follows from the $\mathrm{sc}^0$ property of
  $Tr$ (exposition §8.3). Also "$X^1$" is used for $X_1$ *(text?)*.
- p. 30, Proposition 2.21(3): "$T_aO = Ds(a)\circ Dr(a)+(I-Ds(a))Dr(a)E$": $Ds(a)$ stands for
  $D(s\circ r)(a)$, and that the splitting is an *sc*-splitting (not just algebraic) needs that
  $Dt(a)$ is an sc-projection at the smooth point $a$ (Lemma 2.B of Chapter 1). The chart of $A$ is
  constructed with the same quadrant $C$ as the chart of $X$; this is what Lemma 2.26 uses.
- p. 31, Definition 2.22: "smooth charts" means all charts of the sc-smooth atlas. The chart
  index genuinely depends on the chart (the diagonal of $[0,\infty)^2$ has chart index $2$ and
  $d_O = 1$ at the origin), which is why a minimum is taken; not illustrated in the text.
- p. 33, proof of Lemma 2.29(1): "the closure of $(T^R_xO)_\infty$ is equal to $T^R_xO$" — the
  intersection $T_xO\cap E_x$ of two sc-subspaces is not automatically an sc-subspace; it is here
  because $E_x$ is the kernel of finitely many continuous functionals (Lemma 3.A(1) of the
  exposition). Similarly (2) needs that the smooth points of $C_xO = T_xO\cap C_x$ are dense (Lemma
  3.A(2)); "since $C_xO$ is closed, the result follows" covers only one inclusion.
- p. 34, proof of Lemma 2.29(3): "$h^\pm = Dr(x)k^\pm$ … by (2), $h^\pm\in C_xO$" — $k^\pm$ is on
  level $0$, so $t\mapsto r(x+tk^\pm)$ is not an sc-smooth path and (2) does not apply directly; one
  approximates $k^\pm$ by smooth vectors of $C_x$ and uses closedness.
- p. 36, proof of Theorem 2.31: the map $T:T_xO\to\mathbb R^d\oplus T^R_xO$ is called "a sc-linear
  isomorphism"; this needs the representatives $\hat v^j$ to be smooth (not arranged in the text) and
  $T^R_xO$ to be an sc-subspace (Lemma 3.A(1)). The statement "$\dim(T_xO/T^R_xO)$ is preserved under
  germs of sc-diffeomorphisms" is Proposition 2.30, which rests on Lemma 2.29 — so the whole chain
  Lemma 2.29 → Prop. 2.30 → Thm. 2.31 → Cor. 2.32 → Theorem 1.25 depends on Lemma 3.A.
- p. 38, Corollary 2.32: "trivially $d_{C'}(f(x_k))\le d_{C'}(f(x))$ for large $k$" is the upper
  semicontinuity of $d_{C'}$ (Lemma 5.A(1) of Chapter 1); the step $d_{X_C}(x_k) = d_{X_{C'}}(f(x_k))$
  is Proposition 2.24 applied at $x_k$ (where $f$ is still a germ of sc-diffeomorphism for large $k$).
- Theorem 1.25 (Chapter 1, p. 14) follows from Proposition 2.24 and Corollary 2.32 (exposition
  §3.3); this is presumably the intended "more general result". The 2010 paper's Theorem 1.19 proves
  it under the extra conditions (2),(3) of its Definition 1.13 (an sc-complement of $T_xO$ inside
  $\{0\}\oplus W$; density of smooth points of equal index), which the 2014 preprint drops from the
  definition of a retract; the 2014 route through Theorem 2.31 needs neither. *(book 2017: unchanged:
  the preprint's definition of a retract, Definitions 2.1–2.2, pp. 15–16, without the 2010 extra
  conditions; Theorem 1.2, p. 11, has no proof and still refers to "[36], Theorem 1.19"; the 2014
  route is there as Proposition 2.7, Theorem 2.3 and Corollary 2.1, pp. 27–33)* *(book 2021: unchanged: Definitions 2.1.1 and 2.1.3, pp. 21–22, without the 2010 conditions; Theorem 1.3.5, p. 14, without proof, citing "[54], Theorem 1.19" and now pointing to Section 2.4; the 2014 route is Proposition 2.4.4, Theorem 2.4.12 and Corollary 2.4.13, pp. 45–52)*
- p. 39: "the set $\{e\in C : d_C(e) = 1\}$ has exactly $k$ connected components" and "each
  component lies in a smallest subspace $f_i$" are asserted; they need the convexity of the pieces
  $A_i$, their finite clopen decomposition, and that $A_i$ spans $E_i$ (Lemma 4.A of the exposition).
- p. 40, proof of Proposition 2.35: "the first $d$ coordinates of $r(x+\tau y)$ vanish" uses, besides
  $d_C(r(x+\tau y)) = d$, the semicontinuity $I(r(x+\tau y))\subset I(x)$ for small $\tau$ (continuity
  of $r$ at the fixed point $x$); and the derivative "$\frac{d}{d\tau}r(x+\tau y)|_{\tau = 0} = Dr(x)y$"
  is taken with the smooth increment $y$ first, then extended to level $0$ by density. Not said.
- p. 43, Lemma 2.40: the proof is a sketch. The key point — that $r$ maps points of $U\cap f_i$ near
  a point of $O\cap f_i$ *into* $f_i$ (and not into another face through that point) — is not
  addressed; condition (1) of tameness alone only says the number of vanishing coordinates is
  preserved. The exposition proves it (Lemmas 4.B, 4.C) using condition (2) through Proposition 2.35
  ($\lambda_j\circ Dr(u) = \lambda_j$ for $j\in I(u)$). Also "connected components of $\{d = 1\}$ are
  closures" needs that closures of distinct components are disjoint and relatively open in $f_i\cap O$
  (Lemma 4.C(4)). *(book 2017: fuller: a new Proposition 2.11, p. 39, proves in the model, from
  tameness condition (2), that $r$ maps the component of $U\cap E_i$ through a corner point $(0,v)$
  into itself — the key point above — and the proof of Lemma 2.6 (= 2.40), pp. 40–41, cites it; the
  disjointness and relative openness of the closures of distinct components is still not argued)* *(book 2021: unchanged from 2017, Proposition 2.5.11, p. 58, and the proof of Lemma 2.5.12, p. 59; the disjointness and relative openness are still not argued)*
- p. 44, Proposition 2.42: "$d_V(y) = d_X(y)$" needs that a tame chart realizes the minimum in
  Definition 2.22 (Proposition 2.36 with Proposition 2.24); and the global statement "at most
  $d_X(x)$ faces" needs that distinct global faces through $x$ contain distinct local faces.
- pp. 44–45, Proposition 2.43: "we find an open neighbourhood $U_{(a,w)}$ … such that
  $r(0,b_2,\dots,b_k,v)$ has the first coordinate vanishing" is the unproved face-preservation above
  (Lemma 4.C). "We find an open neighbourhood $V$ of $O$ in $f_1\cap C$" should be a neighbourhood
  of $F$ *(text?)*. "The last statement … is obvious" ($d_F = d_O-1$) is (4.2) applied to both
  retracts. That the model $(F,C\cap f_1,f_1)$ is compatible with the sub-M-polyfold structure of
  Proposition 2.21 is not mentioned.
- p. 46, Propositions 2.44 and 2.45: stated without proof. "The interior of a face" is not
  defined; the exposition reads it as $F\cap\{d_X = 1\}$ and proves this equals the component $G$
  with $F = \overline G$. The identification of the germ of $F_1\cap F_2$ with a face of the tame
  M-polyfold $F_1$ (needed for Proposition 2.44) uses Lemma 4.C(4) in $f_1$.
- p. 47, Proposition 2.46: "$\pi_2:X_f\times_gY\to X$, $(x,y)\to y$" — the target is $Y$ *(text?)*;
  "since $X\times Y$ is tame, $d_{X\times Y}(x,y) = d_X(x)+d_Y(y)$" — additivity holds for tame
  M-polyfolds (Lemma 4.D of the exposition), in general only $\le$. That the chart
  $\Phi(x',y') = \varphi'(y')$ defines the *same* structure as the sub-M-polyfold structure of
  Proposition 2.21 is not addressed (it does, because $\pi_2$ is an sc-diffeomorphism for that structure).
  Confirmed in Lean, items 15–16 of the §2.4–§2.5 list below.
- p. 50, Definition 2.49: "$K(0)$, $K(1)$" for $K[0]$, $K[1]$ *(text?)* *(book 2017: unchanged, Definition 2.24, p. 46)* *(book 2021: corrected, Definition 2.6.3, p. 66, writes $K[0]$, $K[1]$)*. The remark that an
  $\mathrm{sc}^+$-section is one whose principal part is sc-smooth into $F^1$ is not made explicit.
- p. 52, after Definition 2.51: "the M-polyfold $Y$" — $Y$ has not been given an M-polyfold
  structure; the one meant is $Y[0]$ (whose level-$0$ topology agrees with the given one). The
  topology of $Y[1]$ is the one induced by the charts, as for $X_m$.
- p. 53, Proposition 2.54: "the easy proof is left to the reader" (with a reference to [20],
  Proposition 4.11). The exposition gives it; the pulled-back retraction is
  $R_g(w,h) = (r_Z(w),\Gamma(g(r_Z(w)),h))$, whose idempotence uses that $\Gamma(o,\cdot)$ is a
  projection for $o\in O$. Paracompactness of $f^*Y$ uses the metrizability of $Y[0]$ and $Z$.
- p. 48: the double filtration is indexed by $0\le k\le m+1$; that $(U\triangleleft F)[1] = U\oplus F^1$
  is a relatively open subset of a partial quadrant (so that "sc-smooth" makes sense) is Lemma 1.B of
  Chapter 1. Not said.
- 2010 paper, p. 29: "a computation shows that $\pi_a\circ\pi_a = \pi_a$" — immediate from the
  characterization of $\pi_ah$ as the unique solution of $\oplus_a\eta = \oplus_ah$, $\ominus_a\eta = 0$,
  once Theorem 1.27 (that $\boxdot_a$ is an isomorphism) is known. The explicit formula for $\eta^+$
  (p. 29 and p. 72) was re-derived in the exposition (§6) and is correct.
- New in the exposition (§6, Lemma 6.A): every splicing $r(v,f) = (v,\pi_vf)$ is a *tame*
  retraction (condition (2) with $A = \{0\}\oplus\ker\pi_v$, using $\pi_v\circ D_v\pi_v(f) = 0$ at fixed
  points). Neither preprint states this; *(book 2017: the book does: a new Definition 2.18 (sc-smooth
  splicing) and Lemma 2.5, p. 36, prove that $r(a,e) = (a,\pi_a e)$ is a tame retraction, with the
  complement $\{(0,\ell)\mid\pi_a\ell = 0\}$; this makes the splicing cores of SFT tame without
  further argument)* *(book 2021: unchanged, Definition 2.5.4 and Lemma 2.5.5, p. 55)*.
- Numbering and pages *(book 2017: see `BookConcordance.md`)*: all numbers above are the preprint's (Definitions 2.1, 2.3, 2.5,
  2.7, 2.9, 2.11–2.14, 2.17, 2.18, 2.20, 2.22, 2.25, 2.27, 2.33, 2.34, 2.37–2.39, 2.47–2.53;
  Propositions 2.2, 2.4, 2.6, 2.10, 2.19, 2.21, 2.24, 2.30, 2.35, 2.36, 2.42–2.44, 2.46, 2.54, 2.57;
  Theorems 2.8, 2.16, 2.31, 2.45, 2.55; Lemmas 2.15, 2.23, 2.26, 2.29, 2.40, 2.56; Corollaries 2.32,
  2.41; Remark 2.28). The exposition's own lemmas are lettered (1.A–1.B, 2.A–2.D, 3.A, 4.A–4.D,
  5.A–5.B, 6.A).

## From the Lean proofs of Chapter 2, continued (the tangent bundle, X¹, sub-M-polyfolds)

- Proposition 2.57 (used for the paracompactness of `X_m` and `TX`) needs the space to be *regular*;
  the text has only Hausdorff and locally metrizable, which do not imply regularity (the K-topology
  on `ℝ` is a counterexample). Regularity of `X_m` does hold, through the continuous injection
  `X_m → X` into the regular space `X`, but needs an argument. The Lean proof of Theorem 2.16 does
  not need it: it avoids Lemma 2.56 and Proposition 2.57 (item 9 of the next list).
- The paracompactness of `X_m` does not need Smirnov's theorem (only its metrizability does); the
  text's route uses Lemma 2.56, Proposition 2.57 and closed subsets of metrizable spaces.
- Definition 2.17 and the formula `Tφ' ∘ (Tφ)⁻¹ = T(φ' ∘ φ⁻¹)` silently use the chain rule on a
  smaller retract than `φ(V ∩ V')`, and the independence of `Tf` from the retract on which it is
  computed (`Polyfold.retractTangentMap_inter_isOpen`, locality of the tangent map).
- Proposition 2.21: the compatibility argument "`(ψ' ∘ ψ⁻¹) ∘ s'' = (φ' ∘ φ⁻¹) ∘ s''`" is the
  restriction of an sc-smooth retract map to a smaller source (`Polyfold.IsScSmoothRetractMap.mono_source`);
  the text does not say which topology `A` carries (the subspace topology is taken). Paracompactness
  of `X¹`, `TX` and of a sub-M-polyfold `A` was first carried as an instance hypothesis; it is now
  discharged (`Polyfold.MPolyfold.paracompactSpace_level`, `Polyfold.MPolyfold.paracompactSpace_tangentSpace`,
  `Polyfold.MPolyfold.paracompactSpace_subtype`, item 9 of the next list).

## From the Lean proofs of Chapter 2, §2.4–§2.5 and Theorem 2.16 (2026-10-24)

Found while formalizing the tame M-polyfolds (`Polyfold/Chapter2/TameRetracts.lean`). Statement
numbers are the preprint's *(book 2017: see `BookConcordance.md`)*.

1. **Proposition 2.35 needs only condition (2) of tameness.** The text derives `Dr(x)E_x ⊆ E_x`
   from condition (1) (`d_C(r(x + τy)) = d_C(x + τy)`); the sign argument (`r(x + τv) ∈ C` for
   `v ∈ E_x`, `|τ|` small) gives it for *every* sc-smooth retraction at every point of `O₁`
   (`Polyfold.ScRetraction.scDeriv_mapsTo_minimalSubspace`). Condition (1) is used later, in
   Proposition 2.36 and Lemma 2.40. Confirmed in Lean (`Polyfold.proposition_2_35`).
2. **Lemma 2.40 (face preservation) needs condition (2) through Proposition 2.35** — confirmed.
   Condition (1) only fixes the *number* of vanishing coordinates of `r(z)`; that `r` maps points
   of `f_i` near `f_i ∩ O` into `f_i` (and not into another face through the same corner) is the
   ray lemma `Polyfold.ray_zeroSet` (exposition Lemma 4.B): differentiate `λ_j(r(x + τy)) = 0` at
   `τ = 0` and use `λ_j ∘ Dr(x) = λ_j` for `j ∈ I(x)` (`Polyfold.coord_scDeriv_eq`). With it the
   proof of the exposition goes through as written (`Polyfold.local_face_structure`,
   `Polyfold.lemma_2_40`, `Polyfold.corollary_2_41`).
3. **Proposition 2.36 holds in the stronger form "a tame chart realizes `d_X`"**: for a chart
   `φ : V → O` of an arbitrary M-polyfold whose model has a tame retraction, `d_X(y) = d_C(φ(y))`
   for *every* `y ∈ V` (`Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith`), by the
   text's argument (Theorem 2.31 at smooth points, approximation by `r(a, w_j)` and Lemma 2.23
   elsewhere). This is what Proposition 2.42's "`d_V(y) = d_X(y)`" uses.
4. **Exposition §4.3, proof of Proposition 2.43: "`|P₁z − e|₀ ≤ |z − e|₀`" is false for a general
   norm on `E₀`** (it holds for an ℓ¹- or max-norm in the model `ℝᵏ ⊕ W`, not for the norm of `E₀`
   transported by an arbitrary sc-isomorphism `T`). The fix is to take the neighbourhood
   `U* = ⋃_e B_e ∩ P₁⁻¹(B_e)` (`Polyfold.proposition_2_43`). Also Lemma 4.C(3) is needed for points
   of `f_i ∩ B` outside `O` (`r(e') ∈ closure F̂(e)` for all `e' ∈ f_i ∩ B`), which its proof gives
   unchanged.
5. **§2.4 is formalized completely** except the general (non-tame) equality case of Theorem 2.31,
   which Proposition 2.36 does not need (item 17). Proved: Propositions 2.35, 2.36 (all
   statements, item 17), Lemma 2.40, Corollary 2.41, Proposition 2.42, Proposition 2.43 (all
   statements, item 12), Proposition 2.44 (both sentences, item 18), Theorem 2.45 (all statements,
   items 13–14), Proposition 2.46 (items 15–16).

6. **Definition 2.50: the base homeomorphism `φ : V → O` must be a chart of `X`.** The text only
   asks `φ` to be a homeomorphism onto the retract `O`; read literally, the strong bundle atlas would
   induce its own M-polyfold structure on `X`. The Lean definition (`Polyfold.StrongBundleChart`)
   asks `φ` to be a chart of the given structure. "Bounded linear on the fibres" needs only
   linearity: continuity follows from `Φ` being a homeomorphism
   (`Polyfold.StrongBundleChart.continuous_fiber`). *(book 2017: unchanged in substance,
   Definition 2.25, p. 47: `φ` is still only a homeomorphism onto `O`; the fibre condition now
   reads "a bounded linear isomorphism")* *(book 2021: unchanged, Definition 2.6.4, pp. 67–68)*
7. **Lemmas 5.A–5.B of the exposition confirmed** (`Polyfold.IsStrongBundleRetraction.fiber_idem`,
   `Polyfold.IsStrongBundleRetract.isScRetract_one`, `Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst`):
   `K[1]` is the image of `R` on `(U ◁ F)[1]`, which uses that `R` preserves the double filtration at
   `(m, k) = (0, 1)`. That `U ◁ F` is relatively open in the partial quadrant `C ⊕ F` of `E ⊕ F`
   (needed for "sc-smooth" to make sense on `(U ◁ F)[i]`) is `Polyfold.IsRelOpenInQuadrant.prod_univ`.
8. **Proposition 2.54 confirmed** (`Polyfold.proposition_2_54`; "the easy proof is left to the
   reader"). The pulled-back retraction `R_g(w, h) = (r'(w), Γ(g(r'(w)), h))` of the exposition is a
   strong bundle retraction with image `{(w, h) | w ∈ O', (g(w), h) ∈ K}`
   (`Polyfold.isStrongBundleRetract_pullback`), the charts `Φ_f(z, y) = (ψ(z), pr_F Φ(y))` are
   strong bundle charts (`Polyfold.PullbackChartData.toChart`) and any two are compatible
   (`Polyfold.PullbackChartData.compatible_toChart`, through the formula
   `(w, h) ↦ (ψ₂ψ₁⁻¹(w), pr_F(Φ₂Φ₁⁻¹)(g₁(w), h))`). Not said in the text: `f*Y` must be paracompact
   (Definition 2.51); it is, as a subspace of the metrizable `Z × Y` (Theorem 2.16 for `Z` and for
   `Y[0]`, `Polyfold.paracompactSpace_pullbackSpace`). The M-polyfold `Y[1]` is item 19.
9. **Theorem 2.16 holds with the text's hypotheses; no hypothesis added.** The text's proof (pp.
   55–57) goes through Lemma 2.56 and Proposition 2.57, which need `X_m` to be *regular*; the text
   does not check this (it is true, since `X_m → X` is continuous and `X` is regular — see the
   earlier item). The Lean proof (`Polyfold.theorem_2_16`) avoids Lemma 2.56 and Proposition 2.57
   altogether: a partition of unity of the paracompact Hausdorff space `X` subordinate to a chart
   cover, pulled back to `X_m`, gives a metric directly (`Polyfold.metrizableSpace_of_pullback`, a
   locally finite sum of cone metrics `|ρ_i(x) − ρ_i(y)| + min(ρ_i(x), ρ_i(y))·min(d_i(x, y), 1)`),
   and paracompactness then follows from Stone's theorem. The same argument proves Smirnov's
   theorem (Theorem 2.55, `Polyfold.metrizableSpace_of_locally`), which Mathlib lacks, and
   Proposition 2.19 (3) (`Polyfold.proposition_2_19_3`, pulling back along `TX → X¹ → X`). The
   topology of `X_∞` is taken to be the initial topology of the inclusions `X_∞ → X_m`
   (`Polyfold.MPolyfold.smoothLevel_topology_eq`). With these results the paracompactness
   hypotheses carried so far are discharged: `Polyfold.MPolyfold.paracompactSpace_level`,
   `Polyfold.MPolyfold.paracompactSpace_tangentSpace`, and for sub-M-polyfolds
   `Polyfold.MPolyfold.paracompactSpace_subtype` (Proposition 2.21's open point).
10. **Proposition 2.21 (3)–(4) confirmed in a chart** (`Polyfold.proposition_2_21_3`,
   `Polyfold.proposition_2_21_4`): with `t = s ∘ r`, `P = Dr(a)`, `Q = Dt(a)` one has `PQ = Q = QP`
   (from `r ∘ t = t = t ∘ r`), so `T_aO = QE ⊕ (P − Q)E` with both summands sc-subspaces (ranges of
   the commuting sc-projections `Q`, `P − Q` at the smooth point `a`) and the sum direct on every
   level; `Ts(a)T_aO = Q(PE) = QE = T_aA`. The text's `Ds(a)` stands for `D(s ∘ r)(a)` (as noted
   earlier). The transport of the splitting to `T_aX` by `Tφ(a)` is not formalized (the fibres of
   `TX` carry no sc-structure in the Lean project).

11. **Definition 2.50, the `[1]`-transition.** For `(Φ' ∘ Φ⁻¹)[1]` to make sense as a map
   `Φ(P⁻¹(V ∩ V'))[1] → Φ'(P⁻¹(V ∩ V'))[1]`, the transition must send points whose fibre component
   lies in `F₁` to points whose fibre component lies in `F'₁`; the text takes this for granted (it is
   also what makes the double filtration `Y_{m,k}` chart-independent). The Lean definition
   (`Polyfold.StrongBundleChart.Compatible`) states it explicitly; it holds for pulled-back charts.
   *(book 2017: unchanged, Definition 2.25, p. 47)* *(book 2021: unchanged, Definition 2.6.4, p. 68)*

12. **Proposition 2.43, "`F` is tame and `d_F = d_O − 1`", confirmed; no hypothesis added**
   (`Polyfold.proposition_2_43_tameModel`, `Polyfold.LocalModel.proposition_2_43_isTame`, in
   `Polyfold/Chapter2/TameFaces.lean`). The extended face is modelled on `ℝᵏ ⊕ W` itself through
   the sc-operators `ι = T⁻¹ ∘ (insert 0 at i)`, `π = (delete i) ∘ T` (`Polyfold.faceIncl`,
   `Polyfold.faceProj`), and the tame retraction is `r' = π ∘ r ∘ ι` on `ι⁻¹(U*)`. For tameness
   (2) the complement can be taken to be `(1 − Dr'(x))E'` directly: Proposition 2.35 for `r` gives
   `λ_{j'} ∘ Dr(ιx) = λ_{j'}` for the coordinates `j' ≠ i` vanishing at `x`, hence
   `λ'_j ∘ Dr'(x) = λ'_j`; the exposition's intersection `f_1 = T_xF ⊕ A` is not needed. The chart
   `π : F → π(F)` is compatible with the sub-M-polyfold structure of Proposition 2.21 (the
   transition maps are `ι` and `π`), and `F` is paracompact because faces are closed. Along the
   way: the minimal subspace `E_x` does not depend on the presentation of `C`
   (`Polyfold.minimalSubspaceWith_eq`, the argument of Lemma 1.24), so tameness for one
   presentation is tameness (`Polyfold.ScRetraction.IsTameWith.isTame`); Definition 2.34 is
   presentation independent, which the text uses tacitly.
13. **Theorem 2.45, "`G` is a sub-M-polyfold", confirmed** (`Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_interior`),
   through a local criterion the text uses without stating it: `A` is a sub-M-polyfold if near
   each point `φ(A)` agrees on an open set with an sc-smooth retract contained in `O`
   (`Polyfold.MPolyfold.isSubMPolyfold_of_local`; the retraction is `φ⁻¹ ∘ s ∘ φ` on
   `φ⁻¹(B ∩ s⁻¹(B))`, which must be shrunk so that `s` maps it into itself — the text's "transport
   by `φ⁻¹`" omits this).
14. **Theorem 2.45, face-structured case, confirmed** (`Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_face`,
   `Polyfold.MPolyfold.theorem_2_45_isTame_face`: every face is a tame sub-M-polyfold with
   `d_X(i(x)) = d_F(x) + 1`). The exposition's "each global face through `x` contains exactly one
   local face" is a counting argument that the Lean proof makes explicit
   (`Polyfold.MPolyfold.exists_localFace_of_isFaceStructured`): the map `i ↦ F_i` from `I(φ(x))`
   to the faces through `x` is onto (Lemma 4.C), and face-structuredness (`#faces = d_X(x) =
   #I(φ(x))`) makes it injective; then the points of `G` near `x` all lie in the one local
   component `F̂_j`, and `φ(F) ∩ B = closure(F̂_j) ∩ O ∩ B`. The tame charts of `F` are
   `π ∘ φ` onto the restriction of `r'` (item 12) to `ι⁻¹(B)`; tameness passes to restrictions
   (`Polyfold.ScRetraction.IsTameWith.restrict`). Proposition 2.44's first sentence is
   `Polyfold.MPolyfold.proposition_2_44`.

15. **Proposition 2.46 and exposition Lemma 4.D confirmed; no hypothesis added**
   (`Polyfold/Chapter2/FibredProduct.lean`: `Polyfold.MPolyfold.prod`,
   `Polyfold.MPolyfold.degIndex_prod_le`, `Polyfold.MPolyfold.isTame_prod`,
   `Polyfold.MPolyfold.proposition_2_46`, `Polyfold.MPolyfold.proposition_2_46_of_isLocalScDiffeo`).
   "Local sc-diffeomorphism" is read as "each point has an open neighbourhood mapped
   sc-diffeomorphically onto an open set" (`Polyfold.MPolyfold.IsLocalScDiffeo`). The product of
   tame retractions is tame for the product presentation `E ⊕ E' ≅ ℝⁿ⁺ⁿ' ⊕ (W ⊕ W')`
   (`Polyfold.ScRetraction.IsTameWith.prod`), hence tame (item 12, presentation independence).
   **Exposition §4.4, proof of Proposition 2.46: the inverse of `π₂` is not
   "`i⁻¹ ∘ R` composed with `y' ↦ (x, y')`"** — a constant map is sc⁰ only when its value is a
   smooth point, so `y' ↦ (x, y')` is not sc-smooth for a general `x`. The inverse is
   `y' ↦ i⁻¹R((f|_U)⁻¹(g(y')), y')` (`Polyfold.MPolyfold.isScDiffeoOn_snd_fibredProduct`), which
   has the same values since `R(x', y')` does not depend on `x'`.
16. **Proposition 2.46, last statement: tameness is needed only for `d_{X×Y} = d_X + d_Y`.** If `f`
   and `g` are both local sc-diffeomorphisms, `d_{X ₓ×_g Y}(x, y) = d_X(x) = d_Y(y)` holds for
   arbitrary `X`, `Y` (Proposition 2.24 along `π₁` and `π₂`,
   `Polyfold.MPolyfold.degIndex_fibredProduct_eq_fst`, `_snd`); the identification with
   `½ d_{X × Y}(x, y)` uses Lemma 4.D for tame `X`, `Y` (in general only `d_{X×Y} ≤ d_X + d_Y`).
   The fibred product is paracompact since it is closed in the metrizable `X × Y` (Theorem 2.16);
   the text does not mention it.

## Chapter 2: consistency of exposition, Lean and reports (2026-10-24)

The Chapter 2 reports (`Exposition/cmp/ch02.json`, `Exposition/verification/ch02.md` with V2.1–V2.63,
`Exposition/pbp/part02.md`, Part II of `ProofByProof.md`) were written against the Lean files of
`Polyfold/Chapter2/` up to `FibredProduct.lean`, and brought up to date with `PartialCone.lean`,
`CornerGerms.lean` and `StrongBundleOne.lean` (items 17–19 below) in an addendum: the rows V2.42
(Proposition 2.36), V2.50 (Proposition 2.44, both sentences), V2.58 (Definition 2.51 with $Y[1]$,
$P[1]$, $Y_{m,k}$) and V2.59 (Definition 2.52) were updated, V2.64 ($Y[1]$ as a space, the inclusion
$Y[1]\to Y[0]$) was added, and the three corresponding gaps were removed from the comparison (its
Chapter 2 gaps are now G.4–G.15). `Exposition/Chapter2.md` now names the declarations
in a paragraph "*Checked by machine*" (or "*Not checked by machine*") after each statement, and its
closing paragraph "**Checked by machine.**" summarizes what is and is not formalized.

- Corrected in the exposition: the neighbourhood $U^*$ in the proof of Proposition 2.43 (item 4
  above: the union of the balls $B_e$ intersected with their preimages under $P_1$); the shrinking
  in the proof of Theorem 2.45 (item 13); the inverse of $\pi_2$ in the proof of Proposition 2.46
  (item 15), and there also that $d = d_X = d_Y$ needs no tameness (item 16) and that the fibred
  product is paracompact; the condition on the $[1]$-transition in Definition 2.50 (item 11) is
  now stated in the prose.
- Stale notes removed or updated: Theorem 2.16 needs no added hypothesis and no regularity
  (item 9); the paracompactness of sub-M-polyfolds, `X¹` and `TX` is proved, not assumed;
  Proposition 2.46 and Lemma 4.D are proved (items 15–16).
- Still not formalized, and so marked in the exposition and listed as gaps in the comparison:
  Proposition 2.2; Definition 2.9 (bundle retractions; the bundle structure of $TO\to O^1$); $X_m$
  as an M-polyfold for $m\ge2$; the vector space and sc-structures of $T_xX$ (so Proposition 2.21 (3)
  only in a chart); the openness of $p : TX\to X_1$ in Proposition 2.19 (2); Remark 2.28's negative
  claim (probably false, item 50); Lemma 2.29 in its path formulation (its sign arguments are
  formalized); the second statement of Theorem 2.31 in general (for tame retracts its conclusion,
  Proposition 2.36's partial quadrant, is proved: item 17); the intrinsic description of extended
  faces; Definition 2.38 in $T_xX$; strong bundle isomorphisms and the category $\mathcal{SBR}$;
  Lemma 2.56 and Proposition 2.57 (not needed); the application §6 (Lemma 6.A).
- Lean docstrings that described earlier states: **corrected** (2026-10-24, docstrings and comments
  only, no statement or proof changed). In `Polyfold/Chapter2/`: `MPolyfold.lean` (Theorem 2.16 is
  `theorem_2_16` in `Metrizable.lean`, no added hypothesis; `X_m` as an M-polyfold is proved for
  `m = 1` in `LevelPolyfold.lean`, `m ≥ 2` is G.6; `TX`, Proposition 2.19 and Proposition 2.21 (3),
  (4) in a chart are located; G.7, G.8 named); `LevelPolyfold.lean`, `TangentBundle.lean`,
  `SubMPolyfold.lean` (the paracompactness of `X¹`, `TX`, `A` is still an instance argument of
  `MPolyfold.shift`, `tangentPolyfold`, `subPolyfold`, since these files precede `Metrizable.lean`,
  but it is proved there with no added hypothesis — the instances
  `MPolyfold.paracompactSpace_level`, `MPolyfold.paracompactSpace_tangentSpace` fill it in
  automatically, `MPolyfold.paracompactSpace_subtype` is supplied with `haveI`; Proposition 2.21
  (3), (4) are `proposition_2_21_3`, `proposition_2_21_4` in a chart, their transport to `T_aX`
  G.7); `Tame.lean` (independence of `T`: `minimalSubspaceWith_eq`, `IsTameWith.isTame`; the
  sc-isomorphism: `prodQuadrantIso`, `K[i]` retracts by Lemma 5.B; Propositions 2.35–2.46, Lemma
  2.40, Corollary 2.41, Theorem 2.45, Definitions 2.50–2.54 located file by file; G.12–G.14 named);
  `DegeneracyIndex.lean` (the general Theorem 2.31 is `theorem_2_31` / `theorem_2_31_retract`; its
  second statement in general is G.11, its conclusion for tame retracts is
  `proposition_2_36_partialCone`). Also: `Retracts.lean` (the tangent local model, "not constructed
  here", is `LocalModel.tangent` in `TangentBundle.lean`), the headings "Not formalized" of
  `TameRetracts.lean` and `StrongBundle.lean` (whose items are proved elsewhere) renamed, and the
  remaining genuine gaps in `Boundary.lean`, `TangentBundle.lean`, `Metrizable.lean` and
  `StrongBundle.lean` given their numbers (G.7, G.8, G.10, G.11, G.14).

17. **Proposition 2.36, "`T_x^R O` is an sc-subspace and `C_xO` is a partial quadrant in `T_xO`",
   confirmed for tame retracts without the general Theorem 2.31** (`Polyfold.proposition_2_36_partialCone`,
   `Polyfold/Chapter2/PartialCone.lean`). For a tame retraction the vectors `v̂^j` of the proof of
   Theorem 2.31 can be written down: `v̂^j = Dr(x)T⁻¹(e_{i_j}, 0)` is smooth (`Dr(x)` is an
   sc-operator at a smooth point) and `λ_{i_k}(v̂^j) = δ_{jk}` by Proposition 2.35, so no density
   argument is needed to choose them smooth; the sc-isomorphism `S : T_xO ≅ ℝᵈ ⊕ T_x^R O` is
   `Polyfold.splitIso`. That `T_x^R O` is an sc-subspace (exposition Lemma 3.A (1)) follows from
   `Dr(x)E_x ⊆ E_x`: for `u ∈ T_x^R O ∩ E_m` with `T u = (a, w)`, the smooth points
   `Dr(x)T⁻¹(a, w')`, `w' ∈ W_∞`, lie in `T_x^R O` and converge to `Dr(x)u = u` in `E_m`.

18. **Proposition 2.44, second sentence, confirmed** (stated without proof in the text;
   `Polyfold.MPolyfold.proposition_2_44_corner`, `Polyfold/Chapter2/CornerGerms.lean`). The face
   germs at `x` are the faces `F_i`, `i ∈ I(φ(x))`, of a tame chart; for `σ ⊆ I(φ(x))` the set
   `A = φ⁻¹(B ∩ ⋂_{i∈σ} F_i)` (`B` a small open set) is a tame sub-M-polyfold with
   `d_A + #σ = d_X` on `A`. Instead of the exposition's induction on `#σ` (which needs the
   identification of the germ of `F_1 ∩ F_2` with a face of `F_1`), all coordinates of `σ` are
   removed at once: Lemma 4.C(3) for each `i ∈ σ` shows that `r` maps points of `f_σ ∩ C` near
   `φ(x)` into `f_σ` (`Polyfold.corner_retraction`), and the tame model is
   `π_σ ∘ r ∘ ι_σ` on `ℝ^{n−#σ} ⊕ W` (`Polyfold.corner_tameModel`), proved as in item 12.

19. **After Definition 2.51: the M-polyfold `Y[1]`, `P[1]` and the chart independence of `Y_{m,k}`
   confirmed** (`Polyfold/Chapter2/StrongBundleOne.lean`: `Polyfold.StrongBundle.toMPolyfold1`,
   `Polyfold.StrongBundle.isScSmoothMap_proj1`, `Polyfold.StrongBundle.mem_doubleLevel_iff`), and
   Definition 2.52's "sc⁺-section = sc-smooth into `Y[1]`" agrees with the chart-wise definition
   (`Polyfold.StrongBundle.isScPlusSection_iff`). The chart independence of `Y_{0,1}` (hence the
   very definition of the set `Y[1]`) and of `Y_{m, m+1}` uses exactly the `F₁`-condition on the
   `[1]`-transition of item 11; for `k ≤ m` it follows from the `[0]`-transition alone.
   Paracompactness of `Y[1]` (needed for an M-polyfold, not mentioned in the text) follows as in
   Theorem 2.16: `Y[1]` is metrizable (`Polyfold.StrongBundle.metrizableSpace_one`).

## Chapter 2: follow-ups of the round-trip audit (strong bundle charts and atlases, 2026-11-01)

Numbering: Chapter 2 items 40–49 are follow-ups of the round-trip audit (`RoundTrip/`, items V2.58
and V5.4); Lean `Polyfold/Chapter2/StrongBundleRestrict.lean`,
`Polyfold/Chapter3/StrongBundleMaximalAtlas.lean`, `Polyfold/Chapter5/AuxNormLiteral.lean`.
Items 50–59 are round-trip audit findings (`RoundTrip/REPORT.md`, items V2.33 and V2.61) that are
recorded here only; nothing in the project was changed for them.

40. **Definition 2.51: equivalence of strong bundle atlases is an equivalence relation — now
   proved; the text's "an equivalence class of strong bundle atlases" presupposes it without
   comment.** Definition 2.50 calls two atlases equivalent if their union is an atlas; the
   project had the relation (`Polyfold.StrongBundleAtlas.Equiv`) but no property of it.
   Transitivity rests on the **locality of compatibility** of strong bundle charts
   (`Polyfold.StrongBundleChart.compatible_of_locally`, the analogue of
   `Polyfold.MChart.compatible_of_locally`): near a point of `Φ(P⁻¹(V ∩ V''))` the transition
   `Φ'' ∘ Φ⁻¹` factors as `(Φ'' ∘ Φ'⁻¹) ∘ (Φ' ∘ Φ⁻¹)` through a chart `Φ'` of the middle atlas,
   on `[0]` and on `[1]` (Theorem 2.8 and the locality of sc-smoothness between retracts), and
   the `F₁`-condition of item 11 passes through `Φ'`. Proved:
   `Polyfold.StrongBundleAtlas.equiv_iff` (equivalence = pairwise compatibility),
   `StrongBundleAtlas.Equiv.refl`, `.symm`, `.trans` and `Polyfold.StrongBundleAtlas.equivalence`,
   for every `P : Y → X` — no continuity of `P` is needed, since the overlaps are open in `K`
   through the base chart: `Φ(P⁻¹(t)) = K ∩ (W × F)` for `t ⊆ V` open with `φ(t) = O ∩ W`
   (`Polyfold.StrongBundleChart.image_preimage_eq`, `isScRetract_overlap'`,
   `isScRetract_overlap_one'`). Round-trip item V2.58 (a).
41. **Definitions 2.12–2.13: the same gap for M-polyfold atlases, now closed.** The project had
   `Polyfold.MAtlas.Equiv.refl` and `.symm` but not transitivity; the round-trip audit proved it
   as glue (`RoundTrip/Items/V2_12.lean`, `equiv_trans`, item V2.12). It follows from
   `MChart.compatible_of_locally`, already used for `MPolyfold.isChart_congr`; now in the project
   as `Polyfold.MAtlas.Equiv.trans` and `Polyfold.MAtlas.equivalence`.
42. **Strong bundle charts can be restricted to an open subset of the base — now formalized (the
   text uses it silently, e.g. in Lemma 5.2, item 44).** `Polyfold.StrongBundleChart.restrict`:
   for a strong bundle chart `(Φ, P⁻¹(V), K, U ◁ F)` and an open `s ⊆ V`, the chart
   `(Φ|P⁻¹(s), P⁻¹(s), K_s, U_s ◁ F)` over `φ|s` (`MChart.restrict`), with the retraction `R`
   restricted to `U_s = {u ∈ U | r(u) ∈ φ(s)} = U ∩ r⁻¹(W)` (`φ(s) = O ∩ W`; `restrict_U`, the
   domain does not depend on `W`; `Polyfold.IsStrongBundleRetraction.restrict`) and
   `K_s = {(u, h) ∈ K | u ∈ φ(s)}` (`restrict_K`); `Φ` and `|·|₁` are unchanged
   (`restrict_apply`, `liftOne_restrict`). Compatibility passes to restrictions
   (`StrongBundleChart.Compatible.restrict_left`, `restrict_right`, `restrict`), so the
   restriction of a strong bundle chart of `P` is one (`Polyfold.StrongBundle.IsChart.restrict`).
   This is the round-trip auditor's construction (`RoundTrip/Items/V5_4.lean`, adapted from the
   re-centred charts of `Recentre.lean`), moved into the project in the `s ⊆ V` form. Not
   provided: a restriction whose retraction domain lies inside a given open `W ∋ 0` of `E`, as
   the remark "the strong bundle chart can be restricted to `U ∩ W`" in
   `Polyfold/Chapter3/StrongBundleSections.lean` (Definition 3.6) has it — `U ∩ W` is not
   invariant under `r` in general; the variant `U ∩ r⁻¹(W) ∩ W` is `ScRetraction.restrictIn` of
   `Recentre.lean`, used there only for re-centred charts.
43. **"A strong bundle chart of `P`" depends only on the strong bundle structure — now proved.**
   `Polyfold.StrongBundle.IsChart` (compatibility with the charts of the representing atlas;
   Definitions 3.3–3.11, Lemma 5.2, ...) is the text's "chart of some atlas of the class":
   `Polyfold.StrongBundle.isChart_iff_exists_equiv`, through the maximal atlas
   `Polyfold.StrongBundle.maximalAtlas` (`maximalAtlas_equiv`); two charts of `P` are compatible
   (`Polyfold.StrongBundle.IsChart.compatible`), and equivalent atlases have the same charts
   (`Polyfold.StrongBundle.isChart_congr`, the analogue of `MPolyfold.isChart_congr`). So the
   notions defined through `B.IsChart` do not depend on the representing atlas; those defined
   with the charts of `B.atlas` itself (`StrongBundle.doubleLevel`, `oneSet`,
   `IsScPlusSection`, the atlases of `Y[0]`, `Y[1]`) are not shown invariant here.
44. **Lemma 5.2 in the text's literal form — now proved.** `Polyfold.lemma_5_2` states (ii) with a
   neighbourhood `V ⊆ dom φ` of `x` on which the bounds `a·N(w) ≤ |h|₁ ≤ A·N(w)` hold (the text's
   proof only gives them "for `P(w)` close to `x`"), while the text has them on the domain `V` of
   the chart `Φ : Y|V → K`. `Polyfold.lemma_5_2_literal` is the text's form, from `lemma_5_2` by
   restricting the chart to the neighbourhood (item 42). Round-trip item V5.4 (its other
   conjuncts, about `exists_le_mul_norm_liftOne` and the bounds in every chart, are unchanged).

Round-trip audit findings (2026-11-01).

50. **Remark 2.28, "`C_xO` is in general not a partial quadrant in `T_xO`", is false: `C_xO` is a
    partial quadrant in `T_xO` at every smooth point of every sc-smooth retract — proved.** The text
    (p. 33) asserts the negative claim without an example *(book 2017: unchanged, Remark 2.2, p. 29)* *(book 2021: rewritten, Remark 2.4.8, pp. 47–48: the claim is kept and now illustrated by `O = H ∩ [0,∞)⁴`, `H` a 3-plane, a cone with four extreme rays; the text does not show that this `O` is an sc-smooth retract, and by this item it is not one, so as we read it the claim still does not hold)* and proves the positive statement only for tame retracts (Proposition
    2.36, item 17). `Polyfold.remark_2_28_isPartialQuadrant`: for every sc-smooth retraction `r` in
    `C = T⁻¹([0,∞)ⁿ ⊕ W)` and smooth `x ∈ O`, `T_xO` and `T_x^R O` are sc-subspaces
    (`ScRetraction.isScSubspace_reducedTangentSpaceWith`: the density step of
    `proposition_2_36_partialCone` never used tameness) and `C_xO = T_xO ∩ C_x` is a partial
    quadrant in `T_xO` with its induced sc-structure; no tameness. The argument: `Dr(x)` maps `C_x`
    into `C_x` (`ScRetraction.scDeriv_mapsTo_partialQuadrant`) and `E_x` into `E_x`, so
    `C_xO = Dr(x)(C_x)` (`partialConeWith_eq_image_scDeriv`), and modulo `T_x^R O` it is the column
    cone of the nonnegative idempotent matrix `M = Λ ∘ Dr(x) ∘ σ` on `ℝ^{I(x)}` (`coneMatrix`,
    `coneMatrix_idem`, `coneMatrix_mapsTo_orthant`). **Flor's theorem**, proved in the needed case
    (`Polyfold.flor_nonnegRange_simplicial`: the cone `range M ∩ [0,∞)^ι` of a nonnegative idempotent
    is generated by linearly independent columns — minimal column supports, generation by descent on
    the support, independence through a private index of each minimal support), makes the quotient
    cone simplicial (`remark_2_28_quotient_simplicial`), and the sc-isomorphism
    `T_xO ≅ ℝ^r ⊕ T_x^R O` of Theorem 2.31's proof carries `C_xO` onto `[0,∞)^r ⊕ T_x^R O`. The
    quadrant's dimension is `r = rank M = dim(T_xO/T_x^R O) ≤ d_C(x)`, with equality in the tame case;
    for a non-tame retraction only `r = d_C(x)` can fail, not the partial-quadrant property — which
    may be what the remark meant, but not what it says. Found by the round-trip audit (V2.33, where
    the blind statement's `¬B` is now proved, `RoundTrip/Items/V2_33.lean`); Lean:
    `Polyfold/Chapter2/PartialConeQuadrant.lean`.
51. **Proposition 2.54's "natural": that `P' : f*Y → Y` is a strong bundle map is not
   formalized.** The text (p. 53): the pull-back `P_f : f*Y → Z` "carries a natural structure of
   a strong M-polyfold bundle" *(book 2017: Proposition 2.16, p. 48)*. The project has the atlas
   of pulled-back charts `Φ_f` (`Polyfold.proposition_2_54`, `pullbackAtlas`, item 8) and the
   fibrewise linear structure of `Y` (`pullbackFiberEquiv_add`, `_smul`), but no statement that
   `P'` is sc-smooth on `[0]` and `[1]` (round-trip item V2.61). Believed routine: in the charts
   `Φ_f`, `Φ` it is `(w, h) ↦ (g(w), h)` on `K_g`, `g = φ ∘ f ∘ ψ⁻¹`; it needs chart work on
   `Y[0]`, `Y[1]` and the M-polyfolds of `f*Y`. Not done.

## Chapter 3 (sc-Fredholm theory; Lean `Polyfold/Chapter3/`)

*Numbering.* The items of this section are numbered in blocks, one block per line of work, so
that agents working at the same time do not collide; the gaps in the numbering are unused
numbers, not deleted items. 1–31: germs, the germ implicit function theorem, good position and
the quadrant theorems of the appendix (§3.3, §3.2/3.8.1, 3.8.4, 3.8.5); 40–50: sections of strong
bundles, Theorems 3.12/3.15, Proposition 3.10, the filler, and the linear part of the global
implicit function theorem (Proposition 3.52, Lemma 3.55, Definition 3.53); 60–79: the basic class
and local solvability (§3.4–§3.5, Lemma 3.61); 80–89: the tangent germ property (Definition 3.25,
Theorem 3.27) and the first assembly of Theorem 3.54; 90–99: the assembly of Theorem 3.54 at the
centre. Blocks opened on 2026-10-25 (local session): 100–109: Theorem 3.54 (1) at the nearby zeros
in the chart at `x₀` (the kernel and the perturbation argument); 110–119: the linearization of a
section at a zero in a chart and its chart independence; 120–129: Corollary 3.39 and the sharper
Proposition 3.52; 130–139: good complements with a projection into the quadrant (`IsRegular` (b));
140–149: found while writing the exposition of §§3.4–3.5 and the application (Chapter3.md §5, §8);
150–159: the regularity of the solution germ away from the centre (`IsRegular` (a)), the assembly
of Theorems 3.19, 3.23, 3.24, 3.54, 3.56, 3.57, and the answer to "does the sc-Fredholm IFT hold
with the text's hypotheses?" (`SolutionGermRecentre.lean`, `GlobalIFTTheorems.lean`); 160–169:
Theorem 3.18 (parametrized perturbations, `ParamPerturbation.lean`); 170–179: Chapter 3 polish
(statements weaker than their docstrings: the dimension of the solution set as the Fredholm index,
the index along the solution set, "`ker f'(y) = T_yS`", good position and surjectivity when
`∂X = ∅`, the converse in item 100; `GlobalIFTIndex.lean`); 180–189: Theorem 3.54 (1)
with the text's hypotheses (the surjectivity of `f'(y)` at the nearby zeros,
`GlobalIFTNearbyOnto*.lean`); 190–199: the tameness hypothesis repaired (`TameGerms.lean`, the
tame germ data of Definitions 3.50, 3.51, 3.53); 200–209: non-vacuity witnesses for the §3.6
theorems (`NonVacuity.lean`); 210–219: follow-ups of the round-trip audit (`GoodPositionSc.lean`:
good position with the text's sc-complement, Theorem 3.54 (1) in the text's form; items 215–217:
Lemma 3.9 with smallness on level `m`, Lemma 3.81's estimate on all of `V₀`); 220–229: round-trip
audit findings recorded here only (germs versus the whole chart in §3.1, the level-`m` and
sc-Fredholm statements of Proposition 3.10 and §3.6, one germ for all `k` in Theorem 3.35).

Found while formalizing §3.3 (contraction germs and the germ implicit function theorem) in
`ContractionGerm.lean` and `GermIFT.lean`. Statement numbers are the preprint's *(book 2017: see
`BookConcordance.md`)*.

1. **Theorem 3.30 has no proof in the text** (p. 86: "the following regularity result from [21],
   theorem 2.3, which is the hard part of the regularity theory"). The Lean proof
   (`Polyfold.ContractionGerm.hasFDerivWithinAt_sol`, `Polyfold.theorem_3_30`) is: at a parameter
   `a₀` with `(a₀, δ(a₀)) ∈ U₂` the candidate derivative `A = (1 − D₂B)⁻¹D₁B` exists on level `1`
   (Lemma 3.9 on level `1` gives `‖D₂B‖ ≤ 1/2`), so `δ(a₀) + Ah` is an `E₁`-increment of size
   `O(|h|)`; the sc¹-remainder of `B` is `o(|h|)` and the `1/2`-contraction on level `0` gives
   `|δ(a₀ + h) − δ(a₀) − Ah|₀ ≤ 2·o(|h|)`. This proves that `δ` is sc¹ **on the re-indexed germ
   `V_m = N(m+1) ∩ C̃`**, not on the germ `(N m ∩ C̃)_m` on which `δ` was constructed: at points
   with `(a₀, δ(a₀)) ∈ U₁ ∖ U₂` the argument does not apply (`Ah ∉ W₁`), and whether `δ` is
   differentiable there is neither needed nor addressed. Re-indexing a germ is legitimate only
   because `C̃` is finite-dimensional (all levels of `C̃` coincide, so `(U_{m+1})_m` is again a germ
   of relatively open neighbourhoods), which the text does not remark; for a germ in an
   infinite-dimensional sc-Banach space `(U_{m+1})_m` is not a germ (`U_{m+1}` is open in `C_{m+1}`,
   not in `C_m`).
2. **The germ shrinks with `k` in Theorem 3.33, Corollary 3.34, Theorem 3.35.** Each induction step
   of Theorem 3.33 applies Theorem 3.30 once more and so shifts the germ again: `δ` is sc^k on
   `(N(m + s_k) ∩ C̃)_m` with `s_k` growing with `k` (`Polyfold.theorem_3_33`). The proof gives
   `s_k = 2^k − 1` explicitly: the step `j → j + 1` uses the stage `j` twice, for `f` (shift `s`)
   and for `f⁽¹⁾` (shift `s'`), and returns `s + s' + 1` (`ContractionGerm.isSckGerm_succ_of_next`,
   `ContractionGerm.sol_isSckGerm`), so `s_0 = 0`, `s_{j+1} = 2s_j + 1`; the statement keeps
   `∃ s`. Consequently "if `f`
   is sc-smooth so is its solution germ" (Theorem 3.35, last sentence; Corollary 3.34's "in
   particular, `δ` is sc-smooth at the smooth point `0`") holds in the sense of Corollary 3.34 —
   for every `k` on a neighbourhood germ `V_{·,k}` depending on `k` (`Polyfold.theorem_3_33_smooth`,
   `Polyfold.corollary_3_34`, `Polyfold.theorem_3_35_smooth`) — and **not** as "sc^k for all `k` on
   one fixed sequence `(V_m)`" (`Polyfold.IsScSmoothGerm`), which the method does not give. The
   text's germs are "up to shrinking" ("the size of the sets `U_m` does not matter", Definition 3.1),
   so there the two readings agree; with a germ as a fixed sequence of sets they do not. **The
   shrinking may not be intrinsic**: in the toy example of `Chapter3.md` §3 (the figure;
   `B(a, w) = aw + β(a)`, `β(a)_k = a e^{−k/a}`, on `[0,∞) ⊕ W` with `|w|_m² = Σ e^{2mk}|w_k|²`)
   the solution germ `δ(a) = β(a)/(1 − a)` is sc-smooth on the original germ `N(m) ∩ C̃`, while
   the proof certifies sc^k only on `N(m + 2^k − 1) ∩ C̃`. Whether some contraction germ really
   needs a shrinking germ is not decided. *(Revised in item 222: one fixed germ on which `δ` is sc^k
   for every `k` does exist, a diagonal of the `k`-dependent ones; in the project since item 250,
   `corollary_3_34_isScSmoothGerm`.)*
3. **Lemma 3.31, "from the uniqueness we conclude that `δ⁽¹⁾ = Tδ`"** (p. 87). Uniqueness of the
   fixed point holds only in the contraction region, so `Tδ(v, b) = (δ(v), Dδ(v)b)` must lie in it:
   the region of `f⁽¹⁾` on level `m` has to be of the form `(N' × ℝⁿ) × (K_{m+1} × W_m)`, unbounded
   in the tangent directions `b, w` (where `B⁽¹⁾` is affine). Definition 3.28's balls cannot express
   this, which is why the Lean working form `Polyfold.ContractionGerm` carries explicit regions
   `N m`, `O m ⊇ K m` and `Polyfold.ContractionGerm.next` builds those of `f⁽¹⁾` from them.
   Moreover `Dδ(v) = (1 − D₂B(v, δ(v)))⁻¹D₁B(v, δ(v))` needs the level-`1` operators, i.e.
   `(v, δ(v)) ∈ U₂`: the parameter region of `f⁽¹⁾` is `N(2+s) × ℝⁿ` (`Polyfold.ContractionGerm.next_sol`).
4. **Lemma 3.31, "as one verifies by comparing the tangent map `Tf` with the map `f⁽¹⁾`"** is the
   chain rule for germs: `B⁽¹⁾ = (pr₁ ∘ TB ∘ σ, pr₂ ∘ TB ∘ Γ)` with the reshuffle
   `σ(v, b, u, w) = ((v, u), (b, w))` and `Γ(v, b, u, w) = ((v, δ(v)), (b, w))`, where
   `v ↦ δ(v) ∈ W₁` is the **shifted** solution germ (Proposition 1.17, which the text states for
   relatively open sets, is needed for germs: `Polyfold.IsSckGerm.shift`). The class of `B⁽¹⁾` is
   `min(k−1, j)` as the text says (`Polyfold.ContractionGerm.lemma_3_31`).
5. **Lemma 3.32 is reorganised.** The text iterates `f⁽¹⁾` to `f⁽ʲ⁾` and proves Theorem 3.33 by
   contradiction. In Lean the induction is on `j` with the statement quantified over all contraction
   germs (the parameter space of `f⁽¹⁾` is `ℝⁿ ⊕ ℝⁿ`, its fibre `TW`): if `δ` is sc^j then `f⁽¹⁾` is
   sc^j (item 4, `k − 1 ≥ j`), so its solution germ `Tδ` is sc^j by the induction hypothesis, and
   `δ` is sc¹ by Theorem 3.30, hence sc^{j+1} (`Polyfold.ContractionGerm.sol_isSckGerm`). The
   iterated germs `f⁽ʲ⁾` are not constructed.
6. **Lemma 3.9 for sc¹ germs.** Lemma 3.9 is stated for sc-smooth `B`, but Theorem 3.30 and Lemma
   3.31 use its estimate `‖D₂B(a, w)‖_m ≤ ε` for `B` merely sc¹ (Lemma 3.31 for `f` of class sc^k,
   `k ≥ 1`, and `δ` of class sc^j). Its proof needs the differentiability of `B : U_{m+1} → W_m`
   (Proposition 1.16, "recalling Proposition 1.17" in the text), proved for germs in
   `GermLevels.lean` (`Polyfold.IsSc1GermWith.hasFDerivWithinAt_level`); the estimate is
   `Polyfold.ContractionGerm.norm_levelDeriv_snd_le` with the constant `1/2`. The density
   argument ("it is sufficient to verify the estimate for `ζ ∈ W_{m+1}`") is as in the text.
7. **Definition 3.28, "for all `(a, w), (a, w')` on level `m` sufficiently close to `(0, 0)`"**
   presupposes that these points lie in the domain `U_m` of the germ; the Lean form
   `Polyfold.IsSc0ContractionGerm` asks for `r > 0` with the estimate on `{|a| < r} × {|w|_m < r}`
   **and** these points in `U_m`. The passage from the balls to the working regions (the
   construction in the proof of Theorem 3.29 — the "parametrized version of Banach fixed point
   theorem") needs radii decreasing fast enough for `K_{m+1} → K_m` and a continuity radius for
   `|B_m(a, 0)|_m` (`Polyfold.IsSc0ContractionGerm.toContractionGerm`).
8. **Corollary 3.34 (2)** ("`δ : V_{m,k} → W_m` is of class `C^k`") uses Proposition 1.18 for germs;
   the text cites Propositions 1.17 and 1.18, stated for relatively open sets. Proved for germs
   (`Polyfold.IsSckGerm.contDiffOn_levels`, with the sets `V_{m,k} = N(m+k+s_k) ∩ C̃`). The citation
   of "Proposition 3.40" in that sentence (p. 88) should be Theorem 3.40 *(book 2017: unchanged,
   renumbered: "Proposition 3.11" for Theorem 3.11, before Corollary 3.3, p. 79)* *(book 2021: corrected, before Corollary 3.3.7, p. 113, cites Theorem 3.5.1)*.
9. **Theorem 3.35** is the same proof for any finite-dimensional partial quadrant `C̃`; in Lean the
   whole of §3.3 is proved for any convex `C̃ ∋ 0` with nonempty interior in a finite-dimensional
   `P` (`Polyfold.IsQuadrantLike (const P) C̃`), and Theorem 3.35 is the specialisation
   (`Polyfold.theorem_3_35`, with `Polyfold.IsPartialQuadrant`).
10. Typos *(book 2017: unchanged: the first on p. 77; the second renumbered, p. 84 "Corollary 3.2" for
    Proposition 3.2, and the book's Corollary 3.2 is another statement; the statement of Theorem 3.7
    (= 3.29) is unchanged)* *(book 2021: the first unchanged, p. 110; the second corrected, §3.5, p. 117, which cites Proposition 3.1.10; Theorem 3.3.2, p. 110, unchanged)*: p. 85, "a continuous map `δ₁ : V₁ → W₁` satisfying `δ(0) = 0`" for `δ₁(0) = 0`;
    p. 94 (§3.5, first paragraph) "Corollary 3.10" for Proposition 3.10; Theorem 3.29's statement
    "a uniquely determined sc⁰-solution germ" leaves the uniqueness region implicit (Remark 3.36
    makes it explicit: `|w|₀ ≤ τ₀`; in Lean `O 0`, `Polyfold.theorem_3_29`).
11. *(Superseded by items 40–45: Definitions 3.3, 3.6, 3.11, 3.14 and Theorem 3.15 are now
    formalized in `StrongBundleSections.lean`, the global Theorem 3.12 and Corollary 3.13 in
    `SectionCompactness.lean` (`Polyfold.theorem_3_12`, `corollary_3_13`,
    `corollary_3_13_section`). The item records the state when §3.3 was formalized.)*
    **Theorem 3.12, Corollary 3.13, Definition 3.14, Theorem 3.15, Lemmas 3.16–3.17 are global
    statements** about sc-Fredholm germs and sections of tame strong bundles over M-polyfolds
    (Definitions 2.50–2.52, 3.3–3.6, 3.11), whose definitions are not formalized (Chapter 2 §2.5 is
    definitions only, without strong bundle charts). What is formalized (`LocalCompactness.lean`) is
    the local content of Theorem 3.12 and Corollary 3.13, which is Theorem 3.40 of §3.5 together with
    a compactness argument: `Polyfold.theorem_3_40_compactness`, `theorem_3_40_regularity`,
    `theorem_3_12_local` (for a basic germ, Definition 3.7 = `Polyfold.IsBasicGerm`, plus an
    sc⁺-germ), `corollary_3_13_local`. Definition 3.14, Theorem 3.15 and Lemma 3.17 are **not**
    formalized; the latter two need fillers (Definition 3.4, with the linearization condition (3)),
    the extension `s̃ = s ∘ r` of an sc⁺-section (Lemma 3.16) and the bookkeeping of
    Definition 3.11 (`(g + s̃) − (s̃ + t₀) = g − t₀`), on top of strong bundle charts.
12. **Theorem 3.12's compactness is not in Theorem 3.40**, of which the text says Theorem 3.12 is "an
    immediate consequence": Theorem 3.40 states only the regularity `cl(S ∩ O(m)) ⊆ C_m`.
    Compactness of `cl(S ∩ O(i))` in `E_i` needs, besides, that the solutions in `O(i)` lift to
    level `i + 1` with `|w|_{i+1}` bounded (so that their `W_i`-parts are precompact, by the
    compactness of `W_{i+1} → W_i`), that the solution set is closed, and that the level-`i` lift is
    continuous for the level-`0` topology (the "convergence upgrade" in the proof of Theorem 3.40).
    The sets `O(i)` are then the balls of radius `τ_{i+1}`, one level ahead of the text's `O(i)`
    (`Polyfold.IsSc0ContractionGerm.isCompact_lift_image`).
13. **The induction step of Theorem 3.40 ("the induction step is now clear and the further details
    are left to the reader", p. 98)** is not a repetition of the level-`1` step: the estimate
    `|P ∘ s(a, w)|_{m+1} ≤ τ'_{m+1}/4` needs `(a, w)` small on level `m` (`s : U_m → W_{m+1}` is
    continuous on level `m`), while `O(m+1)` controls only `|a|₀, |w|₀`. For a solution, smallness
    on level `m` follows from the continuity at `0` of the level-`m` lift
    `(a, w) ↦ (a, δ_m(a, P∘s(a, w)))` for the level-`0` topology, which is the same continuity that
    gives the convergence upgrade; so existence, bound and continuity of the lifts must be proved
    together by induction (`Polyfold.IsSc0ContractionGerm.exists_lift`). The text's `(1₃)`, with
    `|w|₀ ≤ τ₁`, is correct for `m = 1` only because `s` is sc⁺ on level `0`.
14. **Hypotheses of Theorem 3.40 actually used**: of `f = h + s` only the `W`-component matters, and
    of it only that `B` is sc⁰ with the contraction estimates of Definition 3.7 (not sc-smooth),
    that `s` is sc⁰ into `W¹` (the sc⁺ property level by level) with `s(0) = 0`, and that `C̃` is
    closed (true for partial quadrants; needed for the solution set to be closed in `E₀`, the text
    takes closures in `C₀`). The `ℝᴺ`-component of `f` only shrinks the solution set. The contraction
    radius on level `m + 1` must be chosen so that the level-`0` image of the level-`(m+1)` ball
    lies in the level-`0` contraction ball (the text's `τ'_1 < τ_0/c_1`), so that the level-`(m+1)`
    fixed point and the given solution agree by the level-`0` uniqueness (the text's (43)).
15. **Corollary 3.13** says "if `f(x_k) = 0` and `x_k → x` in `X₀`, then `x_k ∈ X_m` for `k` large and
    `x_k → x` in `X_m`" for the germ `(f, x₀)`; the local statement at `x₀` gives this for `x = x₀`
    (`Polyfold.corollary_3_13_local`, with `x_k → 0`), or for `x` in the neighbourhood `O(m)` of
    Theorem 3.12 — for an arbitrary limit `x` it needs the germ property at `x` (for an sc-Fredholm
    section, Definition 3.14, at every smooth point) *(book 2017: unchanged, Corollary 3.1, p. 65)* *(book 2021: corrected, Corollary 3.1.15, p. 97, takes the limit to be the centre `x₀`)*.
16. The "parametrized version of Banach's fixed point theorem" (proofs of Theorems 3.29 and 3.40):
    `Polyfold.exists_fixedPoint_continuousOn` (continuity of the fixed point in the parameter from
    the uniform contraction constant and the continuity of the map in the parameter), stated and
    proved since Mathlib has `ContractingWith.fixedPoint` without the parameter dependence.
17. **Definition 3.4 (filling), Lemmas 3.16–3.17** are formalized for the principal parts of the
    sections (`Polyfold.IsFillerOf`, `Polyfold.lemma_3_16`, `Polyfold.lemma_3_17` in
    `Filler.lean`): conditions (1)–(3) of Definition 3.4, with the map `y ↦ [1 − ρ(r(y))]g(y)`
    required sc¹ so that the linearization in (3) exists (the text presupposes it), and Lemma 3.17
    as "the three conditions pass from `(f, g)` to `(f + s, g + s ∘ r)`", which is what the text's
    proof checks ((1) and (2) from Lemma 3.16, (3) because the two maps agree on `U`, so their
    linearizations at `0` agree by the uniqueness of derivatives on `U₁`). **Weaker than the text**:
    the regularity statements (`g` an sc-smooth section, `s̃ = s ∘ r` an sc⁺-section, Lemma 3.16,
    hence `g + s̃` sc-smooth) are not included — they need the pairing and sum rules of the
    sc-calculus for maps on sets, available so far for germs only (`Polyfold.IsSckGerm.pair`).
    *Resolved at the level of Theorem 3.15*: the sum rule on sets was added
    (`Polyfold.IsScSmooth.add`, item 42), and `Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd`
    proves `s̃ = ŝ₁ ∘ r` sc-smooth into `F¹` and `g + s̃` sc-smooth on `U` before applying
    `lemma_3_17`, so nothing of Lemmas 3.16–3.17 is missing where they are used; `lemma_3_17`
    itself remains the statement about the three filler conditions.
    Lemma 3.16 (2), `R(r(u), s̃(u)) = s(r(u))`, is "`R` fixes `K`" and uses that an sc⁺-section is
    a section (`(x, s(x)) ∈ K` on `O`), the hypothesis `hsK`. The text's "`ρ(u) : F → F` is a bounded
    linear operator" is linearity from Definition 2.47 and continuity from `R` being sc⁰ on level
    `0` (`Polyfold.StrongRetr.ρCLM`).

Found while formalizing §3.2 and Appendix 3.8.1 (good position, Proposition 3.22) in
`GoodPosition.lean`.

18. **Proposition 3.22 is proved without the extreme-ray lemmas.** The text's proof (Appendix
    3.8.1) rests on Lemma 3.62 (Krein–Milman for closed convex cones) and Lemma 3.63 (a cone with
    nonempty interior is a quadrant iff it has `dim N` extreme rays), both cited from [21] without
    proof, and on Lemmas 3.64, 3.66–3.68. The Lean proof (`Polyfold.exists_quadrantNormalForm`,
    `Polyfold.proposition_3_22`) keeps the text's two cases (Lemma 3.68: `Ñ ∩ (ℝ^{Σᶜ} ⊕ W) = {0}`
    or `Ñ ⊆ ℝ^{Σᶜ} ⊕ W`) but needs only Lemma 3.65 (`N^⊥ ⊆ ℝ^{Σᶜ} ⊕ W`, `Polyfold.lemma_3_65`)
    and the resulting surjectivity of `Q : N → ℝ^Σ` (`Polyfold.sigmaCoord_surjective`): in the
    first case `N ∩ C = {x ∈ N | x_i ≥ 0 for i ∈ Σ}` is shown directly by a segment argument
    (`Polyfold.mem_quadCone_of_vanIdx`: the first point of `N ∩ C` on the segment from such an `x`
    to an interior point is nonzero, hence has positive coordinates outside `Σ`, so it was not the
    first) and `N ≅ ℝ^Σ × ker Q` carries `N ∩ C` onto `[0,∞)^Σ × ker Q`; in the second case
    (`Σ = ∅`) a line argument gives `dim N = 1` (`Polyfold.quadrantNormalForm_of_vanIdx_empty`).
    The case `N ∩ C = N` (all coordinates vanish on `N`, e.g. `N ⊆ W`), not singled out by the
    text's case distinction, is treated separately (`k = 0`).
19. **Definition 3.21 asks for an sc-complement; only the algebraic splitting `E₀ = N ⊕ P` is
    used.** Neither the sc-structure nor the closedness of the good complement enters
    Proposition 3.22, Lemma 3.45, Lemma 3.65 or Proposition 3.69; the Lean
    `Polyfold.IsGoodComplement` requires `IsCompl N P` only (the text's remark after Definition
    3.21 already allows a "merely topological complement"). Lemma 3.66 (`Ñ` in good position with
    complement `(N ∩ W) ⊕ N^⊥`) is not needed. Typo p. 77: "finite dimensional sunspace" *(book 2017: corrected, p. 69)* *(book 2021: corrected, p. 102)*.
    *(Revised in item 210: this holds for good position as a hypothesis; as a conclusion
    (Theorem 3.54 (1)) the algebraic notion is weaker than the text's, and the sc-complement is
    now proved there, `GoodPositionSc.lean`.)*
20. **Proposition 3.69** is stated in the model `E = ℝⁿ ⊕ W`, `C = [0,∞)ⁿ ⊕ W`, as in the text;
    (2) `d_{N∩C}(x) = dim N − dim(N ∩ W)` is formalized additively
    (`Polyfold.proposition_3_69`), with `N ∩ W = ker(pr_{ℝⁿ} ∘ ι_N)`. The proof is read off the
    normal form: for `x ∈ N ∩ C ∖ N ∩ W` the vanishing coordinates of `e(x) ∈ ℝᵏ` are those of `x`
    (the coordinates outside `Σ` are positive), and on `N ∩ W` the `ℝᵏ`-component of `e` vanishes
    with `k = dim N − dim(N ∩ W)`. The text's proof uses the explicit basis `e^j = (a^j, b^j, w^j)`
    with `b^j_i > 0` of the complement `Ñ`; in Lean this is the right inverse `g` of `Q`.
21. **Lemma 3.45** is stated for `Tϕ(0)` with `Tϕ(0)C = C'`; it holds for any continuous linear
    isomorphism `S : E₀ → E'₀` with `S(C) = C'`, with `ε' = ε/(‖S‖‖S⁻¹‖ + 1)`
    (`Polyfold.IsGoodComplement.map`, `Polyfold.IsInGoodPosition.map`; the interior condition is
    transported along the homeomorphism `N ≅ S(N)`).

Found while formalizing Appendix 3.8.5 (Theorem 3.78, the implicit function theorem in partial
quadrants) in `QuadrantIFT.lean`.

22. **Theorem 3.78 (1) omits `f(k + τ(k)) = 0`, and (3) omits `k + y ∈ U`.** The first is the
    content of the theorem (the text's `τ(k) = B(k, τ(k))`), the second is needed for `f(k + y)` to
    be defined; both are included in `Polyfold.theorem_3_78`. The theorem is proved for a
    finite-dimensional `V` in place of `ℝⁿ`, `f` into any normed space, and `C^j` in Mathlib's sense
    (equal to Definition 3.71 on relatively open subsets of partial quadrants by
    `Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant`).
23. **Theorem 3.78 uses only the convexity of `C` and the nonemptiness of its interior**, not the
    partial quadrant structure (`Polyfold.ContractionData.exists_solution` is stated for a convex
    `C`); the quadrant enters only through the good position hypothesis, which is what makes
    `k + y ∈ C` for `k ∈ K ∩ C`, `|y| ≤ ε|k|` (Lemma 3.80) and gives `K ∩ C` a nonempty interior
    in `K` (needed for `Dτ(0)` to be meaningful).
24. **Lemma 3.82's induction (`f ↦ f⁽¹⁾`, "on a possibly smaller neighbourhood `V` of `0`") is
    replaced by bootstrapping the derivative formula** `Dτ(k) = (1 − D₂B(k, τ k))⁻¹ D₁B(k, τ k)`:
    the right-hand side is `Φ ∘ (id, τ)` with `Φ` of class `C^{j−1}` on the region `R` of Lemma
    3.79 (inversion is smooth on units), so `τ ∈ C^i` implies `τ ∈ C^{i+1}` for `i < j`
    (`Polyfold.Radii.contDiffOn_τ`), and `τ` is `C^j` on the whole `V₀ = {k ∈ K ∩ C | |k| < a}`
    without shrinking.
25. **Lemma 3.81's estimate `|τ(k) − τ(k₀)| ≤ ε|k − k₀|`** uses the point `(k, τ(k₀))`, which lies
    in the domain only when `|τ(k₀)| ≤ ε|k|`, i.e. for `k` not too small relative to `k₀` (for
    `k₀ ≠ 0` and `k → 0` it fails). The Lean proof (`Polyfold.Radii.norm_τ_sub_le`) treats the case
    `|k₀| > 2|k|` through `|τ(k)| + |τ(k₀)| ≤ (ε/2)(|k| + |k₀|)` and gets the Lipschitz constant
    `1 + 2ε`. Since the fixed-point sets `X_k = B̄_Y(ε|k|)` depend on `k`, the parametrized Banach
    fixed point theorem of Theorems 3.29/3.40 (`Polyfold.exists_fixedPoint_continuousOn`, fixed
    set) does not apply and the continuity is proved by hand, as in the text.
26. Typos in Appendix 3.8.5 *(book 2017: all unchanged, Lemma 3.30 (= 3.82), p. 128, and Lemma 3.28
    (= 3.80), p. 126)* *(book 2021: all unchanged, Lemma 3.8.26, p. 172, and Lemma 3.8.24, p. 170)*: (72) in Lemma 3.82, "`D₁B(k₀, τ(k₀))`" and
    "`D₂B(k, τ(k₀))`" for `D₁B(k, τ(k))`, `D₂B(k, τ(k))`; "`τ ↦ Dτ(k)` is continuous" for
    `k ↦ Dτ(k)`; Lemma 3.80 "`c(a) := (1 + ε) max_{x ∈ B((1+ε)a)} |DB(x)|`" where the maximum is
    over `B((1+ε)a) ∩ C` (where `DB` is defined).

Found while formalizing Appendix 3.8.4 (Theorem 3.72, the quadrant inverse function theorem) in
`QuadrantInverse.lean`.

27. **Theorem 3.72's hypothesis (2), `d_C(x) = d_C(f(x))`, is used only through "`x` is an interior
    point iff `f(x)` is"** (`d_C = 0` on both sides, `Polyfold.degIndex_eq_zero_iff`): the openness
    argument of Lemma 3.74 needs the classical inverse function theorem at interior points and
    that `f` carries interior points to interior points, nothing else about the corner structure
    (`Polyfold.InvData.interior_iff`, `Polyfold.proposition_3_73`, `Polyfold.theorem_3_72`). The
    partial quadrant enters only as a closed convex set with nonempty interior. Some hypothesis
    of this kind is needed: `f(x, y) = (x, y + x²)` on `C = [0,∞)²` is smooth, `f(C) ⊆ C`,
    `f(0) = 0` and `Df(0) = 1` (so (1) holds), but `f(C) = {(a, b) | a ≥ 0, b ≥ a²}` is not a
    neighbourhood of `0` in `C` (it misses `(a, a²/2)`, `a > 0`); (2) fails at the boundary
    points `(x, 0)`, `x > 0`, which are mapped to the interior points `(x, x²)`.
28. **Lemma 3.77 carries the hypotheses "`V = f(U)` relatively open, `f : U → V` a homeomorphism,
    `Df(x)` invertible"**, all consequences of Proposition 3.73's hypotheses (`‖Df − 1‖ ≤ 1/2` makes
    `Df(x) = 1 − (1 − Df(x))` a unit); the regularity of the inverse is proved by bootstrapping
    `Dg = [Df]⁻¹ ∘ g` (`Polyfold.InvData.contDiffOn_inv`) instead of the iterated tangent maps of
    Lemma 3.76 (Definition 3.71 is Mathlib's `ContDiffOn` on relatively open subsets of partial
    quadrants). In Lemma 3.74 the Cauchy-sequence step is replaced by the compactness of
    `f(B̄(x', 2r) ∩ C)` (`B̄(x', 2r) ∩ C ⊆ U` is compact in finite dimensions), which also gives the
    density step; the interior starting point `x₀` of the segment must be chosen with
    `f(x₀) ∈ B(y', r)`, which the text does not say.
29. **"`Df(0)` is an isomorphism, from `ℝⁿ = C − C` and `Df(0)C = C`"**: surjectivity needs only an
    interior point of `C` (`Polyfold.surjective_of_image_eq`), injectivity is finite
    dimensionality. The hypotheses `0 ∈ U`, `f(0) = 0` of Proposition 3.73 are not used there
    (`Polyfold.InvData` has neither); the degeneracy index is carried by `Df(0)⁻¹` because
    `Df(0)⁻¹ C = C` (`Polyfold.degIndex_map_eq`, Lemma 1.24 for the presentation `T ∘ S`).
30. Typos in Appendix 3.8.4 *(book 2017: all unchanged: Lemma 3.24 (= 3.74), p. 122; Lemma 3.26
    (= 3.77), p. 124, renumbered, now citing "Theorem 3.7" for Proposition 3.7, while the book's
    Theorem 3.7 is the existence theorem for contraction germs; Definition 3.17 (= 3.71), p. 120)* *(book 2021: three unchanged, the proof of Lemma 3.8.18, p. 166, and Definition 3.8.14, p. 164; one corrected, Lemma 3.8.21, p. 168, cites Proposition 3.8.17)*:
    Lemma 3.74's proof "`{y ∈ B(x⁰, r) ∩ C | d_C(y) = 0} ⊆ V`"
    for `B(y⁰, r)`; "`τ_n → τ'`" for `τ*`; Lemma 3.77 cites "Theorem 3.73" for Proposition 3.73;
    Definition 3.71 "`T f(x, h) = f(x), Df(x)h)`" misses a parenthesis.

Found while formalizing Lemma 3.70 (Appendix 3.8.1) in `GoodPositionGraph.lean`.

31. **Lemma 3.70's two cases (`dim N = 1`, `dim N ≥ 2`) and the directional-derivative argument**
    are replaced by a ray decomposition of `N ∩ C` read off the normal form of Proposition 3.22
    (`Polyfold.exists_rayDecomp`: nonzero `u_i ∈ N ∩ C`, the text's basis `e^j` of `Ñ`, such that
    every `v ∈ N ∩ C ∖ N ∩ W` has `v − s u_i ∈ N ∩ C` with `s|u_i| ≤ c|v|`) and a mean value
    estimate: `(v + τ(v))_j = (w + τ(w))_j + s(u_i)_j + (τ(v) − τ(w))_j ≥ 0 + s b − s‖ℓ_j‖‖u_i‖η > 0`
    for `j ∉ Σ`, `w = v − s u_i` (`Polyfold.lemma_3_70_core`, `Polyfold.lemma_3_70`). The
    smallness of `τ` is needed on the segment `[v − s u_i, v] ⊆ B(0, (1 + c)|v|)`, which fixes the
    "close to `0`" of the statement as `|v| < ρ/(1 + c)`. The level `Y₁` of the values of `τ` plays
    no role. The lemma excludes the points of `N ∩ W`, where `d_{N ∩ C}` is given by Proposition
    3.69 (2).

Found while formalizing §3.1 for sections of strong bundles over M-polyfolds (Definitions 3.3,
3.6, 3.11, 3.14 and Theorem 3.15) in `StrongBundleSections.lean`.

40. **Tameness is not used in Definitions 3.3–3.14 or in Theorem 3.15.** The text states
    Definition 3.14 and Theorem 3.15 for a *tame* strong bundle (over a tame M-polyfold); nothing
    in the definitions of a filled version, of an sc-Fredholm germ or in the proof of Theorem 3.15
    uses the tameness of the retractions. `Polyfold.StrongBundle.IsScFredholmSection` and
    `Polyfold.theorem_3_15` are stated for any strong bundle (`Polyfold.StrongBundle`), hence for
    tame ones. Tameness enters only with the boundary behaviour (good position, §3.6).
41. **"A strong bundle chart" in Definitions 3.3, 3.6 and 3.11 must mean a chart compatible with
    the atlas, not a member of it** (`Polyfold.StrongBundle.IsChart`): a chart of the atlas need
    not be centred (`φ(x₀) = 0`), and the notions must not depend on the atlas within its
    equivalence class. The price is that the local representatives of the sections have to be
    sc-smooth in every compatible chart: for an sc-smooth section this is Definition 2.14 as it
    stands (`Polyfold.StrongBundle.IsScSmoothSection.isScSmoothRetractMap`); for an sc⁺-section
    (sc-smooth into `Y[1]`, `Polyfold.StrongBundle.IsScPlusSection` is stated in the charts of the
    atlas) it is the change of chart `(Φ ∘ Φ'⁻¹)[1]` on `K[1]`, which is exactly the compatibility
    on `[1]` required in Definition 2.50 (`Polyfold.StrongBundle.IsScPlusSection.isScSmoothRetractMap_one`,
    together with the locality of sc-smoothness between retracts). This is the first place where
    the `[1]`-compatibility of Definition 2.50 is actually needed.
42. **Proof of Theorem 3.15, "`f + s` is an sc-smooth section which is also regularizing".** Both
    clauses are silent in the text. Sc-smoothness is the sum rule of the sc-calculus in a chart
    (`Polyfold.IsScSmooth.add`: pairing followed by the sc-operator `F ⊕ F → F`, not stated in
    Chapter 1), applied to `z ↦ (z, f̂(z) + ŝ(z))`, which lands in `K` because `K[1] ⊆ K` and the
    fibres of `K = {(u, h) | u ∈ O, ρ(u)h = h}` are linear (`Polyfold.StrongBundleChart.add_mem_K`);
    continuity of `f + s` is read off the same representative
    (`Polyfold.StrongBundle.IsScSmoothSection.sectionAdd`). Regularizing: `s(x) ∈ Y_{m,m+1}` for
    `x ∈ X_m` because the representative `O → K[1]` of `s` preserves the levels
    (`Polyfold.StrongBundle.IsScPlusSection.snd_mem_range`), and `Y_{m,m+1}` is closed under the
    fibrewise subtraction `f(x) = (f + s)(x) − s(x)` (`Φ` is linear on the fibres;
    `Polyfold.StrongBundle.regularizing_sectionAdd`). The sum `f + s` itself needs the vector space
    structure of the fibres `P⁻¹(x)` (`Polyfold.sectionAdd`); in a chart `(f + s)^ = f̂ + ŝ`
    (`Polyfold.StrongBundleChart.principal_sectionAdd`).
43. **Definition 3.11 as formalized** (`Polyfold.StrongBundle.IsScFredholmGerm`): the filled
    version `g` is sc-smooth on the whole `U` of the chart (the text's germ "near `0`" is recovered
    by shrinking the chart), a local sc⁺-section is a map `s : U → F₁` sc-smooth into `F¹`, and
    "`Ψ ∘ (g − s) ∘ ψ⁻¹` is a basic germ" is `(Ψ(u, g(u) − s(u)))₂ = h(ψ(u))` for `u ∈ U` near
    `0`, with `Ψ` a strong bundle isomorphism `U ◁ F → U' ◁ F'` (strong bundle maps both ways,
    `Polyfold.IsStrongBundleIso`), `ψ(0) = 0`, `U'` relatively open in `C̃ ⊕ W` (`C̃` a partial
    quadrant of a finite-dimensional space) and `h` a basic germ on a germ of neighbourhoods
    `G ⊆ U'` (`Polyfold.IsConjugateToBasicGerm`). The text's `C' = Tψ(0)C` (proof of Theorem 3.54)
    is not imposed. In the proof of Theorem 3.15 the identity `(g + t̃) − (t̃ + t₀) = g − t₀` holds
    on `U` only (`t̃ = t ∘ r` with `ι t̃₁ = t̃` needs `r(u) ∈ O`), which is why the conjugation
    condition is stated for `u ∈ U` (`Polyfold.IsConjugateToBasicGerm.congr`); the filler
    condition (1) of Lemma 3.17 likewise only involves `f̂` on `O` (`Polyfold.IsFillerOf.congr_left`).
    *(Shrinking the chart does not recover a germ whose levels shrink with `m`; the project's
    notion is stricter than the text's: items 220–221; the text's germ reading and the reduction
    to it, items 260–264.)*

Found while formalizing Theorem 3.12 and Corollary 3.13 for sections of strong bundles over
M-polyfolds in `SectionCompactness.lean`.

44. **Theorem 3.12, "an immediate consequence of Theorem 3.40".** Of the hypotheses "`f` an
    sc-smooth section of the tame strong bundle" only `P ∘ f = id` is used
    (`Polyfold.theorem_3_12`); the regularity enters through the filled version `g` of Definition
    3.11, tameness not at all. The passage from the local statement (`theorem_3_12_local_subset`,
    Theorem 3.40 for any subset of the solution set) to the M-polyfold needs: (i) the
    identification of the zeros of `f` near `x₀` with those of `h + t`, `t = Ψ[1]_*(s)`, through
    the chart, the filler ((1) and (2) of Definition 3.4) and the fibre maps of `Ψ`, which are
    linear bijections (`Polyfold.IsStrongBundleIso.snd_eq_zero_iff`); (ii) `t` is an sc⁺-germ
    because `Ψ[1]` is sc-smooth (Definition 2.47) and `t(0) = 0` from `s(0) = g(0) = f̂(0) = 0`;
    (iii) the `E₀`-closure of the solution set must stay inside the chart and inside the
    neighbourhood where the filler and conjugation identities hold: the `O(i)` of Theorem 3.40 are
    intersected with a small ball (the closure of a subset of the solution set stays compact);
    (iv) the closure consists of zeros of `g` in `U`, hence lies in `O` by condition (2) of the
    filler (`Polyfold.eq_of_mem_closure_of_continuousOn`); (v) the `X₀`-closure of a subset of a
    chart domain can leave the domain, so the compactness in `E₀` is used first to see that it
    does not; (vi) "a compact subset of `X_i`" needs the inverse chart `O_i → X_i` to be
    continuous for the level topology of `X_i`, i.e. the sc⁰ transition maps on level `i`
    (`Polyfold.MPolyfold.continuousOn_levelChartSymm`, the paragraph after Definition 2.14 for
    every `m`, formalized so far for `m = 1` only). The statement is formalized as
    `closure {x ∈ O(i) | f(x) = 0} = ι_i(K_i)` with `K_i ⊆ X_i` compact.
45. **Corollary 3.13, "`x_k → x` in `X_m`".** For the base point `x = x₀` of the germ
    (`Polyfold.corollary_3_13`) and for an sc-Fredholm section with any limit `x` of zeros
    (`Polyfold.corollary_3_13_section`; the limit is a zero since the principal part is
    continuous, and a smooth point since `f` is regularizing — cf. item 15). The convergence in
    `X_m` is stated for lifts `y_k ∈ X_m` of the `x_k` (`k` large) converging to the lift of `x`.
    Since `X_m` is not known to be first countable (its metrizability is Theorem 2.16, which the
    Lean proof does not use), the convergence is proved from the compactness of Theorem 3.12 by a
    cluster-point argument (`Polyfold.tendsto_of_isCompact_of_tendsto_map`: a sequence in a
    compact set whose image under the continuous injection `X_m → X` converges, converges), not
    by extracting subsequences as in the local proof.

Found while formalizing Lemma 3.9 and Proposition 3.10 in `BasicGermLinearization.lean`.

46. **Proposition 3.10, "`Df(0)` is an sc⁺-perturbation of the operator (32)".** The verification
    that `S = Df(0) − T₀` is an sc⁺-operator is not in the text. It needs: the `ℝᴺ`-component of
    `Df(0)` is sc⁺ because `ℝᴺ` has all levels equal; `D₁B(0)` is sc⁺ because
    `D₁B(0)δa = DB(0)(δa, 0)` with `(δa, 0)` a smooth point and `DB(0)` an sc-operator (so the
    values lie in `W_∞`), and its level maps `E_m → W_{m+1}` are continuous because they factor
    through `DB(0)_{m+1} : E_{m+1} → W_{m+1}` and `δa ↦ (δa, 0)` (no finite dimensionality of
    `ℝⁿ` is needed for this); `Ds(0)` is sc⁺ because an sc⁺-germ is sc¹ into `W¹`, so `Ds(0)`
    is an sc-operator `E → (ℝᴺ ⊕ W)¹`; and `D₂B(0) = 0` by Lemma 3.9. The silent step behind
    the first two: the finite-rank terms of `Df(0)` (the `ℝᴺ`-component `(1 − P)Df(0)` and the
    term `D₁B(0)` through `ℝⁿ`) are sc⁺ because `Dh(0)` is an sc-operator at the smooth point `0`
    (the remark after Proposition 1.16); the text writes `Df(0)` as an sc⁺-perturbation of (32)
    without saying so. In Lean the operator `S`
    is built level by level (`Polyfold.proposition_3_10_scPlus`) and
    `Polyfold.proposition_3_10` is `Df(0) = T₀ + S` with Proposition 1.10 and its index statement
    (`proposition_1_10_index`). The derivative of `h` at `0` is an sc-operator by
    `Polyfold.IsSc1GermWith.isScOperator_deriv_zero` (the remark after Proposition 1.16, for
    germs, at the smooth point `0`); the identity `Df(0) = Dh(0) + ιDs(0)` and
    `pr_W Dh(0) = pr_W − DB(0)` use the uniqueness of derivatives within `U₁` and the density of
    `E₁` in `E₀`. The hypotheses are: `h` a basic germ, `s` sc¹ into `(ℝᴺ ⊕ W)¹`, and `f = h + s`
    sc¹ (the text: sc-smooth). **Lemma 3.9 is proved at `(0, 0)` only**
    (`Polyfold.IsSc0ContractionGerm.deriv_zero_snd`, from the difference quotients along
    `t ↦ (0, tζ)`, `ζ ∈ W₁`, and density), which is what Proposition 3.10's first statement
    needs; the second statement of Proposition 3.10 (`Df(a, w)` Fredholm of index `n − N` on level
    `m` for `(a, w)` small) is **not formalized** (it needs Lemma 3.9 near `(0, 0)`, available in
    `ContractionGerm.lean` for the working form of a contraction germ with `ε = 1/2`).

Found while formalizing §3.4 (Theorem 3.38, weak stability of basic germs) in `BasicClass.lean`.

60. **The coordinate change of Theorem 3.38 is linear.** The sc-diffeomorphism `ϕ` of the
    statement is `ψ(a, w) = ((a, (1 − P₁)w), P₁w)` and the fibre map is
    `Ψ(δa, δw) = ((δa, (1 − P₂)δw), L⁻¹P₂δw)`, both linear sc-isomorphisms built from the
    sc-splittings `W = C ⊕ X = R ⊕ Z` of `1 + A`, `A = D₂s(0)`. In Lean the strong bundle
    isomorphism is therefore not a general `IsStrongBundleIso` but the pair of sc-operators
    `Polyfold.StabilityData.split`/`glue` (base, inverse to each other) and
    `Polyfold.StabilityData.fiber`/`fiberInv` (fibre); the push-forward
    `(Φ_*(f + s))¹ = Ψ ∘ (f + s)¹ ∘ ψ⁻¹` is `Polyfold.StabilityData.pushMap`, a basic germ with
    contraction map `B̂ = L⁻¹P₂(B − S) ∘ ψ⁻¹` (`Polyfold.StabilityData.pushB`,
    `Polyfold.theorem_3_38`). The text's `τ : Z → C` (so that the new finite-dimensional target
    is `ℝᴺ ⊕ C`) is not applied: the new target is `(ℝᴺ ⊕ Z) ⊕ X¹`, the new source
    `(C̃ ⊕ C) ⊕ X¹`. A consequence for §3.5: since `ψ` is linear, the solution sets of `f + s`
    and of its push-forward correspond under a linear map
    (`Polyfold.StabilityData.pushMap_eq_zero_iff`), and good position is carried by Lemma 3.45
    in its linear form.
61. **"The index raise by 1" is a change of sc-structure.** The new germ is a germ on the shifted
    spaces: parameters `(a, c) ∈ C̃ ⊕ C`, fibre `X¹` with levels `X_{m+1}`
    (`Polyfold.StabilityData.E'`), and its germ of neighbourhoods is `ψ(U_{m+1})`
    (`Polyfold.StabilityData.pushGerm`). The sc-smoothness of `(f + s)¹` on the shifted germ is
    Proposition 1.17 for germs (`Polyfold.IsSckGerm.shift`), and `f + s` is sc-smooth by the
    pairing and operator rules (`Polyfold.StabilityData.fsum_isScSmoothGerm`); the text says
    nothing about either.
62. **"`S` is an arbitrarily small contraction on every level `m ≥ 1`"** (p. 91) needs more than
    `D₂S(0, 0) = 0`: on level `m + 1` the map `s : U_{m+1} → W_{m+1}` is `C¹` with derivative
    continuous in the operator norm (Proposition 1.16 for germs, the compact-open lemma
    `Polyfold.IsSc1GermWith.continuousOn_levelDeriv_clm`), so that `‖D₂S(a, w)‖_{m+1} ≤ ε` for
    `(a, w)` small on level `m + 1`, and then the mean value inequality on a ball in `W_{m+1}`
    for fixed `a` (`Polyfold.scPlusRemainder_contraction`). The partial derivative in `a` of `S`
    does not vanish and plays no role. The operator `A = D₂s(0)` is an sc⁺-operator because its
    level maps are the level operators of Proposition 1.16 at the smooth point `0`
    (`Polyfold.scPlusOfDeriv`).
63. **Hypotheses of Theorem 3.38 actually used.** Of the sc⁺-section `s` only its `W`-component
    enters the contraction normal form (the `ℝᴺ`-component is carried along in the new
    finite-dimensional component); `s` must be sc-smooth into `W¹` for the push-forward to be
    sc-smooth. Of the basic germ `f` the contraction map `B` is used only through Definition 3.7
    (sc⁰ with the contraction estimates). "`1 + A` is a sc⁺-perturbation of the identity and hence
    sc-Fredholm by Proposition 1.10. Because `A` is level wise compact, the index `ind(1 + A)` is
    equal to `0`" is Proposition 1.10 applied to the identity (`Polyfold.isScFredholm_id`, the
    trivial splitting) and `ind(1 + A) = ind(1) = 0` (`Polyfold.proposition_1_10_index`,
    `Polyfold.scIndex_id`); the equality `dim C = dim Z` (hence `n − N = n' − N'`) is
    `Polyfold.StabilityData.finrank_Cs_eq_finrank_Zs`. Corollary 3.39 (composition with a given
    conjugation to a basic germ) is not formalized in `BasicClass.lean`.

Found while formalizing §3.5 (Lemma 3.42, Theorem 3.43, Lemmas 3.44, 3.46, Corollary 3.47) in
`LocalSolvability.lean`.

64. **Lemma 3.46 without the intermediate complement `Y₀`.** The text (Appendix 3.8.2) picks a good
    complement `Y'` of `K' = {(α, Dδ(0)α)}` in `ℝⁿ' ⊕ W`, a complement `Y₀` of `Y' ∩ W` in `Y'`,
    and projects `Y₀` to `ℝⁿ'`. In Lean (`Polyfold.lemma_3_46`) one takes `Z' := pr_{ℝⁿ'}(Y')`,
    which already satisfies `ℝⁿ' = K̃ + Z'`, chooses `Z ⊆ Z'` with `ℝⁿ' = K̃ ⊕ Z` and a linear
    right inverse `ρ : Z' → Y'` of the projection; the good-complement estimate for `(K̃, Z)` with
    constant `ε' = ε/(‖ρ‖ + 1)` follows from the one for `(K', Y')` applied to `(α, Dδ(0)α)` and
    `ρ(z)`. `Z ⊕ W` is then a good complement of `K'` (`Polyfold.lemma_3_46_isInGoodPosition`
    records the good position of `K̃`).
65. **Lemma 3.42 enters Theorem 3.43 as a hypothesis.** Theorem 3.43 is stated in the text for
    `g = Φ_*(f + s)`, and its proof uses Lemma 3.42 ("solutions of `g = 0` near `0` on level `0`
    lie on level `1` and are small there"), whose proof is Theorem 3.40 for `f + s`. In Lean
    `Polyfold.theorem_3_43` is stated for an abstract sc-smooth germ `g` whose index-raised germ
    `g¹` is basic (`Polyfold.ShiftedBasicData`) with this regularity as the explicit hypothesis
    `hreg` (for every `ε > 0` there is `r > 0`: a zero `x` of `g` with `|x|₀ < r` has `x₂ = ι(w₁)`
    with `|w₁|₁ < ε`). For the push-forward of Theorem 3.38 the hypothesis is
    `Polyfold.StabilityData.lemma_3_42`, proved from the lifts of Theorem 3.40
    (`Polyfold.IsSc0ContractionGerm.exists_lift` at level `1`), their continuity at `0`, and the
    linearity of `ψ` on level `1`.
66. **A gap in the proof of Theorem 3.43 (3): the `K'`-component of a solution lies in `C'`.** The
    text writes a solution `x = (a, w)` as `a = k + z` with `k ∈ K̃`, `z ∈ Z` and applies the
    uniqueness clause of Theorem 3.78 to conclude `z = σ(k)`; that clause needs `k ∈ C̃`, which is
    not verified. It holds because `z` is small compared with `k`: from `H(a) = 0`, `H(0) = 0`,
    `DH(0)k = 0` one gets `|DH(0)z| = o(|a|)`, and `DH(0)` is injective on `Z`, so `|z| ≤ ε|k|`
    for `a` close to `0`, and then the good-complement property of `(K̃, Z)` gives `k ∈ C̃` from
    `k + z = a ∈ C̃` (`Polyfold.exists_proj_mem_of_eq_zero`, stated for any map differentiable
    at `0` on a partial quadrant).
67. **"The map `H` restricted to `U'_i` is of class `C^{i−1}`."** `H(a) = pr_{ℝᴺ}(g(a, δ(a)))` is
    `C^j` on a neighbourhood of `0` in `C̃` because `δ` is `C^j` into `W_{2j}` (Corollary 3.34 (2)
    for the index-raised germ, whose solution germ on level `m` takes values in `W_{m+1}`) and
    `g : U_{2j} → ℝᴺ ⊕ W_j` is `C^j` (Proposition 1.18 for germs,
    `Polyfold.IsSckGerm.contDiffOn_levels`); see `Polyfold.ShiftedBasicData.H_contDiffOn`. The
    text's `U'_i` is an `i`-dependent neighbourhood; in Lean a single `C¹`-neighbourhood `V₁`
    carries the kernel and the derivative (`Polyfold.ShiftedBasicData.Deriv`).
68. **Lemma 3.44, "recalling from Lemma 3.9 that `D₂B(0) = 0`".** Lemma 3.9 gives `D₂B(0) = 0` for
    the basic germ `g¹`, i.e. on level `1` (`Polyfold.IsSc0ContractionGerm.deriv_zero_snd`); the
    kernel of `Dg(0)` is computed on level `0`. The identity `pr_W Dg(0)(0, ζ) = ζ` for all
    `ζ ∈ W₀` follows from the one for `ζ ∈ W₁` by the density of `W₁` in `W₀`
    (`Polyfold.ShiftedBasicData.Deriv.snd_Dg_inr`), after which
    `ker Dg(0) = {(α, Dδ(0)α) | α ∈ ker DH(0)}` is the chain rule for `a ↦ g(a, δ(a))`
    (`Polyfold.ShiftedBasicData.Deriv.ker_Dg_eq`).
69. **Corollary 3.47 does not need Theorem 3.72 and Lemma 3.70.** The text transports the solution
    set of `g = Φ_*(f + s)` back to `f + s` with the sc-diffeomorphism `ϕ` and justifies the good
    position of `ker D(f + s)(0)` and the form of the zero set with the degeneracy index
    (Lemma 3.70, Theorem 3.72). Since `ϕ` is linear (Finding 60), `ker D(f + s)(0) = ψ⁻¹(K')`,
    its good complement is `ψ⁻¹(Y')` (Lemma 3.45 in its linear form,
    `Polyfold.IsGoodComplement.map`), `V = ψ⁻¹(V')` and `σ = ψ⁻¹ ∘ τ ∘ ψ` on the kernels; the
    derivative `Dg(0)` is `Ψ ∘ D(f + s)(0) ∘ ψ⁻¹` (`Polyfold.StabilityData.scDerivGerm_pushMap₀`),
    so surjectivity and the kernels correspond (`Polyfold.theorem_3_47`). The finite
    dimensionality of `ker D(f + s)(0)`, needed to transport good position
    (`Polyfold.IsInGoodPosition.map`), comes from Lemma 3.44.
70. **Theorem 3.43 (1), "`τ` is sc-smooth"** (`Polyfold.ShiftedBasicData.Sol.exists_contDiffOn_level`,
    the last clause of `Polyfold.theorem_3_43_sc_smooth` and of `Polyfold.theorem_3_47_sc_smooth`;
    `Polyfold.theorem_3_43`, `Polyfold.theorem_3_47` are the statements without it): for every `k ≥ 1`
    there are a relatively open neighbourhood `V_k ⊆ V` of `0` in `K' ∩ C'` and a `C^k`-map
    `τ_k : V_k → E_k = ℝⁿ' ⊕ W_k` with `ι_k ∘ τ_k = τ` on `V_k`. The text's "`τ` is sc-smooth"
    is read in this level-wise sense (Corollary 3.34 (2), Proposition 1.19 for maps from
    finite-dimensional spaces). The proof applies Theorem 3.78 to the `C^k`-map `H` on `U'_k ∩ V₁`
    (Finding 67) and identifies the `C^k` solution `σ_k` with `σ` near `0` through the uniqueness
    clause (3) of Theorem 3.78 (this needs `σ` continuous at `0` with `σ(0) = 0`, so that
    `|σ(y)| ≤ σ_k` and `y + σ(y) ∈ U'_k` for `y` small); the `W`-component `ι(δ(a)) − L(πy)`,
    `a = πy + σ(πy)`, lifts to `W_k` through the `C^k` lift `δ' : U'_k → W_{2k}` of `δ` and
    `L = ι_{2k} ∘ Dδ'(0)`, which follows from the uniqueness of the derivative of `ι ∘ δ` at `0`.
    The text says nothing about why the solutions produced by Theorem 3.78 for the different
    `k` coincide.
71. **Corollary 3.41 as formalized** (`Polyfold.StabilityData.corollary_3_41`, in
    `SolutionLinearization.lean`), with three simplifications of the text's proof. (a) The
    hypothesis "`f(a, w) = 0`" is used only to bring the point to level `1`: the Fredholm property
    with index `n − N` (`Polyfold.StabilityData.exists_isFredholm_Dfs'`) and the triviality of
    `ker Df(x) ∩ N` for a closed complement `N` of `ker Df(0)`
    (`Polyfold.StabilityData.exists_ker_Dfs'_inf_eq_bot`) hold for *every* `x ∈ U₁` small on
    level `1`, so `Df(x)` is a surjective Fredholm operator of index `n − N` for all such `x`;
    for zeros `x` small on level `0` the level-`1` lift is small by the continuity at `0` of the
    lifts of Theorem 3.40 (`Polyfold.IsSc0ContractionGerm.exists_lift`), and the text's detour
    through "bounded on level `2`, hence convergent on level `1` by the compact embedding
    `W₂ → W₁`" is not needed. (b) "`‖D₂B(a, w)‖ ≤ ε` if `(a, w)` is sufficiently small in `E₀`"
    (Lemma 3.9) is used for `(a, w) ∈ E₁` small on level `1`
    (`Polyfold.IsSc0ContractionGerm.exists_norm_deriv_snd_le`): `B` is differentiable only as a
    map `U₁ → W₀`, so the difference quotient along `t ↦ (a, w + tζ)` needs the curve in `U₁`;
    the contraction estimate itself is the level-`0` one of Definition 3.28. (c) The Fredholm
    property and the index of `Df(x)` are obtained directly, without restricting to `N`:
    `Df(x) = Df(0) + S(x) + K(x)` with `S(x)(α, ζ) = (0, −D₂B(x)ζ)` of norm `≤ ε` and `K(x)`
    compact (the finite-rank parts through `ℝⁿ` and `ℝᴺ`, and `ι(Ds(x) − Ds(0))` through the
    compact inclusion `W₁ → W₀`; `Polyfold.StabilityData.Kop_isCompactOperator`), so
    `Df(0) + S(x)` is Fredholm of the same index by the Neumann series
    (`Polyfold.isFredholm_add_of_norm_lt`, the quasi-inverse `(1 + vS)⁻¹v`) and then `K(x)` does
    not change the index (Kato IV.5.26, `Polyfold.fredholmIndex_add_isCompactOperator`);
    surjectivity follows from `dim ker Df(x) ≤ dim ker Df(0) = n − N = ind Df(x)`
    (`Polyfold.HasFiniteIndex.surjective_of_finrank_ker_le`) instead of "`Df(x)|N` has index
    `0` and is injective". In the compactness argument the Neumann series
    `ζ_k = Σ (D₂B(x_k))ˡ z_k` is replaced by `|ζ_k − z_k| = |D₂B(x_k)ζ_k| ≤ ε_k → 0`. `Df(0)` is
    Fredholm of index `n − N` by Proposition 3.10 for the basic germ `h`
    (`Polyfold.proposition_3_10_basic_level_zero`) plus the compact `ι ∘ Ds(0)`, which avoids
    the sc⁺-operator form of `Ds(0)`.

Found while formalizing Lemma 3.61 (`InverseFamily.lean`), quoted by the text from [25,
Proposition 4.8] without proof.

72. **Lemma 3.61, the proof** (`Polyfold.lemma_3_61`, for germs: `V` is a germ of relatively open
    neighbourhoods of `0` in the partial quadrant `C̃ ⊆ G` and `V ⊕ E` the product germ
    `Polyfold.ScNbhdGerm.prodFull`). Hypothesis (i) is built into the data `L : G → ScIso E F`,
    (ii) is `IsScSmoothGerm (V ⊕ E) Φ`, `Φ(v, h) = L(v)h`, and (iii) is the uniform lower bound on
    `V₀`. The sc⁰ part is the estimate
    `|L(v)⁻¹k − L(v₀)⁻¹k₀|_m ≤ c_m⁻¹(|k − k₀|_m + |(L(v₀) − L(v))h₀|_m)`, `h₀ = L(v₀)⁻¹k₀`
    (`Polyfold.famInv_isSc0Germ`). The sc¹ part needs an argument not visible in the statement:
    with `Λ(v, k) = L(v)⁻¹k`, `h = Λ(v, k)` and `w = DΛ(v, k)(δv, δk) = L(v)⁻¹(δk − D₁Φ(v, h)δv)`,
    `Λ(v', k') − Λ(v, k) − w = L(v')⁻¹[(L(v) − L(v'))w] − L(v')⁻¹r` with
    `r = Φ(v', h) − Φ(v, h) − D₁Φ(v, h)δv = o(|δv|)` (the remainder of `Φ` along the direction
    `(δv, 0)`, with the base point `h` fixed, so that only the finite-dimensional variable moves);
    the term `(L(v) − L(v'))w` is `o(|(δv, δk)|₁)` **because the increment is measured on level
    `1`**: `w/|(δv, δk)|₁` lies in the compact set `DΛ(v, k)(ι(B₁))`, `ι : F₁ → F₀` being compact,
    and `(L(v) − L(v'))u → 0` uniformly for `u` in a compact set by the joint continuity of `Φ`
    (`Polyfold.exists_forall_norm_le_of_isCompact`, `Polyfold.famInv_hasFDerivWithinAt`). The
    operator-norm continuity of `v ↦ L(v)`, which is not assumed, is thus replaced by strong
    continuity plus the compactness of the inclusion `F₁ → F₀`; the differentiability of `Λ` as a
    map `(V ⊕ F)₀ → E₀` would need the norm continuity and is not claimed. The tangent map is
    `TΛ((v, k), (δv, δk)) = (Λ(v, k), Λ(v, δk − (TΦ((v, Λ(v, k)), (δv, 0)))₂))`, a composition of
    `Λ`, `TΦ` and sc-operators, which gives sc⁰ of `TΛ` (`Polyfold.famInv_tangent_isSc0`) and the
    induction `Φ` sc^{k+1} ⇒ `Λ` sc^{k+1} from `Λ` sc^k and `TΦ` sc^k
    (`Polyfold.famInv_isSckGerm`); the sc¹ part uses no quadrant hypothesis, the induction uses
    the composition rules for germs on quadrant-like sets (`C̃` a partial quadrant).
73. **Lemmas 3.59 and 3.60 in abstract form; what remains of Theorem 3.58.** The two lemmas are
    sequence arguments about the family `L(b) = P ∘ Df(b)|X`, and all they use of the
    compactness property (2) of Theorem 3.58 is: if `b_j → b`, `(h_j)` is bounded in `X_m` and
    `L(b_j)h_j → 0` in `Y_m`, then `(h_j)` has a convergent subsequence in `X_m`
    (`Polyfold.FamilyCompactness`; for `L = P ∘ Df|X` this follows from (2) because
    `Df(b_j)h_j − L(b_j)h_j = (1 − P)Df(b_j)h_j` lies in the finite-dimensional smooth space `A`
    and is bounded on every level). With this property, the joint continuity of `(b, h) ↦ L(b)h`
    on each level (the sc-smoothness of `(b, x) ↦ P ∘ Df(b)x`) and the injectivity of `L(0)`,
    `Polyfold.lemma_3_59` gives the injectivity of `L(b)` for `b` near `0` and
    `Polyfold.lemma_3_60` the uniform lower bounds on a compact set of parameters where the
    `L(b)_m` are injective. The text's intermediate step "`P ∘ Df(b)|X` is an injective
    sc-Fredholm operator of index `0`, hence an sc-isomorphism" (from hypothesis (1) and the
    Fredholm property of `P`) is not needed for Lemma 3.60 as formalized, only for turning the
    lower bounds into the sc-isomorphisms required by Lemma 3.61. Not formalized: the setup of
    Theorem 3.58 (the sc-splitting `E = B ⊕ X` as coordinates `ℝⁿ ⊕ X`, the finite-dimensional
    sc-complement `A` of `Y = Df(0)X`, the index computation `ind(P ∘ Df(b)|X) = 0`), the strong
    bundle map `Φ((b, x), (c, y)) = ((b, x), (c, L(b)⁻¹y))` (Lemma 3.61 gives its
    sc-smoothness), and the contraction estimate for `H(b, x) = x − L(b)⁻¹P h(b, x)` from
    condition (3), which needs the integral form of the mean value inequality
    `h(b, x) − h(b, x') = ∫₀¹ D₂f(b, tx + (1 − t)x')(x − x') dt` in `F_m` for `x, x' ∈ X_{m+1}`
    (the derivative bound (3) is in the level-`m` norm of `x − x'`, so the usual mean value
    inequality on level `m + 1` does not give the estimate) and the density of `X_{m+1}` in `X_m`.
74. **Theorem 3.58 as formalized** (`Polyfold.theorem_3_58` in `BasicGermCriterionIndex.lean`, on
    top of `Polyfold.theorem_3_58_of_family` in `BasicGermCriterionProof.lean`; this completes the
    list of Finding 73). The theorem is stated in the coordinates of the text's proof
    ("we may assume that `B = ℝⁿ`, `E = ℝⁿ ⊕ X`, `C = [0,∞)ᵏ ⊕ ℝⁿ⁻ᵏ ⊕ X`, `A = ℝᴺ`"): `U` is a
    relatively open neighbourhood of `0` in the partial quadrant `C̃ ⊕ X` of `ℝⁿ ⊕ X`,
    `f : U → ℝᴺ ⊕ Y` is sc-smooth, and the hypotheses are (1) `Df(b, 0)` sc-Fredholm with index
    independent of `b` at the smooth points `(b, 0) ∈ U`, `b ∈ C̃` (the text asks this at every
    smooth point of `U`; only these points are used), (2) `P ∘ Df(0)|X : X → Y` bijective (the
    coordinate form of "`B` contains `ker Df(0)`" and "`Y = Df(0)X`") and the compactness property
    `Polyfold.CompactnessCondition`, read with the smallness of `b` uniform in the level `m`
    (`∃ r > 0, ∀ m, …`, the order of the quantifiers in the text; Lemma 3.60 needs the property on
    every level on one fixed neighbourhood), (3) `Polyfold.DerivCondition`, the estimate of the
    text with both `(b, 0)` and `(b, x)` in `U` and `|x|_m < r`. The conclusion is explicit: an
    open neighbourhood `Vo` of `0` in `ℝⁿ` and the family `L(b) = P ∘ D₂f(b, 0)|X` of
    sc-isomorphisms such that `k = Φ_*(f − f(0))` is a basic germ on `O(U ∩ (Vo ⊕ X), 0)` with
    contraction map `H(b, x) = x − L(b)⁻¹Ph(b, x)`, the fibre map
    `Φ((b, x), (c, y)) = ((b, x), (c, L(b)⁻¹y))` is a strong bundle isomorphism covering the
    identity (`IsStrongBundleIso`), and `f − f(0)` is conjugated near `0` to a basic germ
    (`IsConjugateToBasicGerm`, with the neighbourhood `U ∩ (Vo ⊕ X)` as its domain: "replacing
    `U` by a smaller one"). Four points of the proof are not in the text. (a) The mean value
    inequality `|P[D₂f(b, 0)(x − x') − h(b, x) + h(b, x')]|_m ≤ ε|x − x'|_m` for `x, x' ∈ X_{m+1}`
    small on level `m`: the text writes the integral `∫₀¹ P[D₂f(b, 0) − D₂f(b, tx + (1 − t)x')](x − x') dt`
    in `F_m`; here the one-dimensional mean value inequality for
    `t ↦ h(b, x' + t(x − x')) − L(b)(x' + t(x − x'))` on `[0, 1]`, whose derivative is bounded by
    `ε|x − x'|_m` by (3) (`Polyfold.norm_sub_sub_le_of_hasFDerivWithinAt_segment`; the usual
    mean value inequality for `h(b, ·) : X_{m+1} → F_m` would give the bound in the norm of
    `X_{m+1}`). The extension to `x, x' ∈ X_m` is a sequence argument with the continuity of
    `H_m` on `U'_m` ("the map `H` is sc-smooth, therefore using the density of `X_{m+1}` in
    `X_m`"). (b) The strong bundle map `Φ` must be sc-smooth on `U' ◁ (ℝᴺ ⊕ Y)` and on
    `(U' ◁ (ℝᴺ ⊕ Y))[1]` (Definition 2.47); the second is Lemma 3.61 for the shifted family
    `L(b) : X¹ → Y¹`, whose sc-smoothness hypothesis is Proposition 1.17 for
    `(b, h) ↦ L(b)h` — the text's "if we raise the index by one, then the map ... is also
    sc-smooth by Proposition 1.17" — and the lift of `(c, L(b)⁻¹ιy₁)` to `F'₁` is `(c, L(b)⁻¹y₁)`
    (`Polyfold.shiftFiber_fiberIsoMap`). Lemma 3.61 is applied on the set `O ⊕ Y` through the
    germ `ofSet (O ⊕ Y)`, which needs the converse of `IsSck.isSckGerm`
    (`Polyfold.IsSckGerm.isSck_ofSet`: a germ on `ofSet U` is an sc^k map on `U`), not previously
    available. (c) "`P ∘ Df(b)|X` is an injective sc-Fredholm operator of index `0`, hence an
    sc-isomorphism" (from (1) and the sc-Fredholm property of `P`) is here, on every level `m`,
    the block computation `ind Df(b, 0) = n + ind L(b)_m − N` (`Polyfold.fredholmIndex_block`:
    `Df(b, 0)_m` differs from `inr ∘ L(b)_m ∘ pr_X` by the finite-rank operator
    `(p, x) ↦ Df(b, 0)(p, 0) + (pr_{ℝᴺ}Df(b, 0)(0, x), 0)`, which does not change the index, Kato
    IV.5.26; `ind(inr ∘ L ∘ pr_X) = n + ind L − N` by the additivity `Polyfold.linIndex_comp`),
    `ind Df(0) = n − N` from the bijectivity of `L(0)` on level `0`, so `ind L(b)_m = 0` and the
    injective `L(b)_m` is surjective (`Polyfold.surjective_of_fredholmIndex_block`); the
    continuity of `L(b)_m⁻¹` is the open mapping theorem (`ContinuousLinearEquiv.ofBijective`).
    Neither the sc-Fredholm property of `P` nor the composition rule for sc-Fredholm operators is
    needed. (d) In Lemma 3.59 "`Df(b_j)h_j = z_j` is a bounded sequence in `A`, in fact on every
    level since `A` is a smooth subspace" and in Lemma 3.60 "`Df(b_j)h_j = P ∘ Df(b_j)h_j = y_j`"
    (the `A`-component is dropped): the boundedness of the `A`-component `pr_{ℝᴺ}Df(b_j, 0)(0, h_j)`
    comes from a uniform bound `‖Df(b, 0)(0, ·)‖ ≤ M` for `b` near the limit, a consequence of the
    joint continuity of `(b, h) ↦ Df(b, 0)(0, h)` at `(b₀, 0)` (`Polyfold.exists_bound_of_continuousOn_clm`),
    valid for `j` large, so condition (2) is applied to a tail of the sequences
    (`Polyfold.familyCompactness_derivFamOp`). The surjectivity of `Df(0)|X` onto `Y` on the
    higher levels (the text's "injective and surjective sc-operator `Df(0)|X : X → Y`", by
    Proposition 1.9) is not needed: the index computation at `b = 0` uses level `0` only.

Found while formalizing Proposition 3.5 and the matrix of `Dg(0)` in `FillerLinearAlgebra.lean`
and `FillerLinearization.lean`.

47. **The matrix of `Dg(0)` and Proposition 3.5.** The text's two identities
    `ρ(0)Tf(0) = Tf(0)` and `(1 − ρ(0))Dg(0)Dr(0) = 0` ("by linearization at `y = 0`, using
    `g(0) = 0`") need the derivative of `y ↦ ρ(r(y))g(y)` at `0`, which is `ρ(0)Dg(0)`: the chain
    rule for `(u, k) ↦ (R(u, k))₂` composed with `y ↦ (r(y), g(y))`, where `D(R(·)₂)(0, 0)(h, k) =
    ρ(0)k` because `k ↦ ρ(0)k` is linear and `ρ(u)0 = 0` (`Polyfold.StrongRetr.scDeriv_fiber_zero`;
    both directional derivatives are computed on the dense level `1` and extended by continuity).
    `g(0) = 0` is used for the point `(r(0), g(0)) = (0, 0)`, and `r(0) = 0` holds since `0 ∈ O`.
    `(1 − ρ(0))Dg(0)Dr(0) = 0` (`Polyfold.IsFillerOf.deriv_comp_r_eq_zero`) needs `f = g` on `O`
    near `0`, `ρ(x)f(x) = f(x)` on `O` (`f` a section of `K → O`, hypothesis `hfK`) and the
    continuity of `r` at `0`; so property (3) of the filler is `(1 − ρ(0))Dg(0)|_{ker Dr(0)} :
    ker Dr(0) ≅ ker ρ(0)` (`IsFillerOf.exists_kerEquiv`). Proposition 3.5 is then the linear
    algebra of an operator `L = [[A, B], [0, C]]` with `C` a topological isomorphism
    (`Polyfold.proposition_3_5`, `Polyfold.IsFillerOf.proposition_3_5`): instead of the text's
    composition formula and the additivity of the index, the Lean proof exhibits `ker A ≃ ker L`
    and `coker A ≃ coker L` (`fillerRestrict_kerEquiv`, `fillerRestrict_cokerEquiv`; both rest on
    the injectivity and surjectivity of `C`), so the index equality holds with no finiteness
    assumption, and transfers the closedness of the ranges through `range A = range L ∩ range q`
    and `range L = M⁻¹(range A)` for the continuous `M(y) = y − L C⁻¹(1 − q)y` — this is where
    "topological" in (3) is used. `Tf(0)` is formalized as `Dg(0)|_{range Dr(0)}`; that it is the
    restriction of `D(f ∘ r)(0) = Dg(0)Dr(0)` to `T₀O = range Dr(0)` is
    `IsFillerOf.scDeriv_section_comp_r`. Remark 3.49 is `IsFillerOf.remark_3_49`. The chain rule
    at a point of `DegeneracyIndex.lean` (`scDeriv_comp_apply`) is stated for `g : E' → E` only;
    the general form is `Polyfold.scDeriv_comp_apply'`.

48. **Proposition 3.52, "`Tf(x) : T_xX → Y_x` is an sc-Fredholm operator".** Formalized in the
    chart of Definition 3.11 as `Polyfold.proposition_3_52` (bundle form) and
    `Polyfold.proposition_3_52_local` (chart form): `Dg(0) : E → F` and
    `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` (`fillerRestrict`) are Fredholm operators on level `0` with
    `ind Tf(0) = ind Dg(0) = n − N`, `n − N` the index of the conjugating basic germ. Only the
    level-`0` Fredholm property is recorded: the text's sc-Fredholm property of `Tf(x)` needs
    `T₀O = Dr(0)E` and `K₀ = ρ(0)F` as sc-Banach spaces and `Tf(0)` as an sc-operator between them
    (the sc-splitting `E = T₀O ⊕ ker Dr(0)` of Proposition 2.35), which is not set up. The proof
    has three steps the text passes over. (a) The derivative of the conjugation
    `Ψ(u, (g − s)(u)) = (ψ(u), h(ψ(u)))` ("near `0`"): the identity holds on a neighbourhood `N₁`,
    the chain rule for the germ `h ∘ ψ` needs the germ of neighbourhoods on which `ψ` maps into the
    germ of `h` (`Polyfold.ScNbhdGerm.preimage`, the silent shrinking of germs), and the
    derivative of `u ↦ Γ(u)(g − s)(u)` at `0` is `Γ(0)D(g − s)(0)` because `(g − s)(0) = 0` and
    `Γ(u, ·)` is linear (`IsStrongBundleMap.scDeriv_fiber_zero`); `Dψ(0)` and `Γ(0)` are
    isomorphisms with inverses `Dψ'(0)`, `Γ'(0)` (chain rule for `ψ' ∘ ψ = id`), so
    `D(g − s)(0) = Γ(0)⁻¹Dh(0)Dψ(0)` is Fredholm of the index of `Dh(0)`
    (`Polyfold.isFredholm_equiv_comp_equiv`, `IsConjugateToBasicGerm.scDeriv_isFredholm`).
    (b) `Dg(0) = D(g − s)(0) + ιDs(0)` uses the uniqueness of the derivative within `U₁` (the
    density of `E₁`), and `ιDs(0)` is compact as the level-`0` map of the sc⁺-operator `Ds(0)`
    (Proposition 1.10 in its classical form `fredholmIndex_add_isCompactOperator`). (c) The
    conclusion for `Tf(0)` is Proposition 3.5 (`IsFillerOf.proposition_3_5`), which needs
    `g(0) = 0`: this is `f(x₀) = 0` through condition (1) of the filler, and
    `(g − s)(0) = 0` is `s(0) = g(0)` of Definition 3.11. Proposition 3.10 is used for the basic
    germ alone (`proposition_3_10_basic`, `s = 0`); for the sc⁺-perturbation the text's
    `D(h + t)(0)` of the proof of Theorem 3.54 is instead obtained from (b).

49. **Lemma 3.55 (Appendix 3.8.3), "`Y = Y₀` is a topological complement of `N_v`".** Formalized as
    `Polyfold.lemma_3_55` (model `ℝⁿ ⊕ W`) and `Polyfold.lemma_3_55_core` (in coordinates): for
    `v ∈ N ∩ C` near `0`, `v + τ(v) ∈ C` and `Y` is a good complement (`IsGoodComplement`: the
    algebraic splitting (2) together with the constant `γ_v` of (3)) of `N_v = {n + Dτ(v)n}` with
    respect to the partial quadrant `C_{v + τ(v)}` (`partialQuadrantAtWith`). **Added hypothesis:
    `Y` closed.** The step "`Dτ(v)n ∈ Y` for all `n ∈ N`" needs `Y` closed (the derivative of a
    map into `Y` has values in the closure of `Y`; `Polyfold.fderivWithin_mem_of_mapsTo`, via the
    tangent cone of `N ∩ C` at `v`, which spans a dense subspace), which is implicit in the text's
    "topological complement". Three further points. (a) The constant `γ_v` can be chosen
    independently of `v`: `γ_v = ε₀/4` with `ε₀ = min(ε, 1)` on the neighbourhood where
    `‖Dτ(v)‖ ≤ ε₀/4`, since then `γ_v(1 + ε₀/4) + ε₀/4 ≤ ε₀` (the text's `γ_v(1 + ε) + ε < γ`).
    (b) The case `v ∉ N ∩ W` needs neither the normal form (a), (b) of the text nor the cases
    `dim N = 1`, `dim N > 1`: if `ℓ_i(v) = 0` then `i ∈ Σ`, so `ℓ_i` vanishes on `Y` (Lemma 3.65),
    and `ℓ_i(v + τ(v)) = 0 ↔ ℓ_i(v) = 0` (Lemma 3.70); hence `ℓ_i(h + y) = ℓ_i(h)` for every
    coordinate `i` entering the definition of `C_x`, and (3) holds with any `γ_v`. (c) The text's
    "`v + τ(v) ∈ C₁`" and "`τ : V → Y₁`": as in Lemma 3.70 the sc-level plays no role, and (1) is
    `v + τ(v) ∈ C`.

50. **Definition 3.53 and the linear part of Theorem 3.54.** Definition 3.53 is formalized in the
    chart of Definition 3.11 (`Polyfold.IsGoodPositionAt`): `Tf̃(0) = Dg(0)|_{T₀O} : T₀O → K₀` is
    onto and `ker Tf̃(0)` is in good position to the partial cone `C₀O = T₀O ∩ C` *inside* `T₀O`
    (`Polyfold.IsInGoodPositionIn`, Definition 3.21 with `E₀` replaced by the subspace `T₀O`).
    (a) The text's case distinction "`d_X(x) ≥ 1`" in (2) is dropped: at an interior point the
    partial cone is the whole tangent space and (2) holds trivially. (b) "`ker Tf̃(0) ⊕ {0} =
    ker Dg(0)` by the properties of the filler" is `IsFillerOf.ker_deriv_le_range` /
    `map_ker_fillerRestrict`: `ker Dg(0) ⊆ T₀O` because `(1 − ρ(0))Dg(0)` is injective on
    `ker Dr(0)` (property (3)) and `(1 − ρ(0))Dg(0)Dr(0) = 0`. (c) "`Z ⊕ ker Dr(0)` is a good
    complement of `ker Tf̃(0)` in `E`" (`IsInGoodPositionIn.isInGoodPosition`) needs the splitting
    `E = T₀O ⊕ ker Dr(0)` to be topological: for `p = z + k` with `|p| ≤ ε'|n|` one has
    `z = Dr(0)p`, so `|z| ≤ ‖Dr(0)‖ε'|n| ≤ ε|n|` with `ε' = ε/(‖Dr(0)‖ + 1)`; `ker Dr(0) ⊆ E_x`
    (Proposition 2.35) is used only in the form "the `ℝⁿ`-coordinates of `k` vanish, so
    `n + z + k ∈ C ↔ n + z ∈ C`". Tameness enters the whole argument only through this inclusion
    `(1 − Dr(0))E ⊆ E₀`, which is a hypothesis of `theorem_3_54_linear` and is derived from
    Proposition 2.35 for a tame `ScRetraction` in `theorem_3_54_linear_of_isTameWith`. (d) The
    text's "`C' = Tψ(0)C`" is not part of the data of a conjugation to a basic germ (Finding 43);
    it is proved (`Polyfold.scDeriv_mem_iff_of_inverse`) from the one-sided sign argument of Lemma
    2.29 for `ψ` and `ψ⁻¹`, since `C_0 = C` at the corner. (e) "`Ψ_*(g) = h + t`, `D(h + t)(0)`
    is sc-Fredholm by Propositions 3.10 and 1.10, surjective, with kernel `N'` in good position":
    the push-forward `Ψ_*(g)(u') = (Ψ(ψ⁻¹(u'), g(ψ⁻¹(u'))))₂` is linearized by the chain rule,
    `D(Ψ_*g)(0) = Γ(0)Dg(0)Dψ(0)⁻¹`, so the Fredholm property, surjectivity and the good position of
    the kernel are transported from `Dg(0)` (`theorem_3_54_pushforward`). The remaining steps of
    Theorem 3.54 — Theorem 3.47 for `h + t`, Corollary 3.41 and Lemma 3.55 for the nearby zeros,
    Theorem 3.27 for the manifold structure — are not formalized here.

Found while formalizing §3.2 (Definition 3.25, Proposition 3.26, Theorem 3.27: the tangent germ
property) in `TangentGerm.lean`.

80. **"sc^∞-germ" in Definition 3.25 (ii) is read with `k`-dependent neighbourhoods.**
    `Polyfold.IsScInftyGermAt D δ`: for every level `m` and every `k` there is a relatively open
    neighbourhood `V_{m,k}` of `0` in `D = N ∩ C` with `δ(V_{m,k}) ⊆ Y_m` and `δ : V_{m,k} → Y_m`
    of class `C^k`. This is the only reading that the germ implicit function theorem delivers
    (Corollary 3.34, item 2; Theorem 3.47 (1), item 70): the solution germ is sc^k on a germ
    shrunk by `s_k` levels. The text's "δ : O(N ∩ C, 0) → (Y, 0) is a sc^∞-germ" on one fixed
    nested sequence (`Polyfold.IsScSmoothGerm` on an `ScNbhdGerm`) implies it
    (`IsScSmoothGerm.isScInftyGermAt`, Proposition 1.18 for germs), as does set-sense
    sc-smoothness on a fixed `V` (`IsScSmooth.isScInftyGermAt`), so `theorem_3_27` covers both
    readings. The text's remark after Definition 3.25 ("there exists a nested sequence `(V_m)`
    ... `δ(V_m) ⊆ Y_m` ... `Tδ` is again of class sc¹") describes the fixed-germ reading.
81. **Definition 3.25 presupposes that the good complement `Y` is closed** ("`N` possesses a good
    complement `Y` so that `E = N ⊕ Y`", an sc-complement in Definition 3.21). It is needed for
    the projection `π : E → N` along `Y` ("the sc-projection `π : N ⊕ Y → N`" of Theorem 3.27 (2))
    to be continuous; added as the field `isClosed_Y` of `Polyfold.MPolyfold.TangentGermChart`
    (`TangentGermChart.π` is `Submodule.projectionOntoL` for the topological complement obtained
    from `Y` closed and `N` finite-dimensional). Cf. the same added hypothesis in Lemma 3.55
    (item 49).
82. **The step "δ is an sc^∞-germ near every `v₀ ∈ V`" of the proof of Theorem 3.27 fails as
    stated** *(book 2017: unchanged, proof of Theorem 3.6, p. 74)* *(book 2021: unchanged, proof of Theorem 3.2.3, p. 107)*. The text linearizes `w ↦ π ∘ ϕ ∘ ψ⁻¹(w + τ(w))` at `w = 0` and asserts that
    `h ↦ π ∘ T(ϕ ∘ ψ⁻¹)(0)h` is a linear isomorphism `N' → N`. Injectivity needs the tangent space
    of the graph of `δ` at `v₀ + δ(v₀)` to be the graph of `Dδ(v₀)`, i.e. `δ` differentiable at
    `v₀`, which is known only near `0`; without it the claim is false. Example: `X = ℝ²`
    (`d_X ≡ 0`, tame), `M` a smooth embedded curve through `0` with horizontal tangent at `0` and
    a vertical tangent at `x₀ = (2, 4)`, e.g. `M = graph g` with `g(s) = s²` near `0` and
    `g(s) = 4 + (s − 2)^{1/3}` near `2`. `M` has the `1`-dimensional tangent germ property: at
    `x₀` use the chart rotated by `90°` (`M` is the graph of `w ↦ w³` over the vertical line). But
    with the chart `ϕ = id` at `x = 0`, `N` the `x`-axis, `Y` the `y`-axis, `V = ℝ`, `δ = g`,
    all conditions of Definition 3.25 (2) hold, `δ` is smooth at `0` with `δ'(0) = 0`, and `δ` is
    not differentiable at `v₀ = 2`. So "`v ↦ ϕ⁻¹(v + δ(v))` is an injective sc-smooth map whose
    image is `M ∩ U`" is false, and the chart `y ↦ π ∘ ϕ(y)` of Theorem 3.27 (2) on all of
    `M ∩ U` is not smoothly compatible with the chart at `x₀` (the transition map is `w ↦ 2 + w³`,
    a smooth homeomorphism whose inverse is not smooth). The statement survives after shrinking
    `U` to where `δ` is sc-smooth; the corrected argument for the points `v₀` near `0` (where
    `δ` is `C¹`) is: `Dα(0) a = Dα(0)a + Dδ(v₀)Dα(0)a` forces injectivity, then the inverse
    `β = π' ∘ ψ ∘ ϕ⁻¹ ∘ (1 + δ)` of `α` is `C¹` with `Dβ = (Dα ∘ β)⁻¹`, and bootstrapping gives
    `β ∈ C^k` near `v₀` on `k`-dependent neighbourhoods — but not sc-smoothness on a fixed
    neighbourhood, which the retraction of Definition 2.20 needs. In Lean the sc-smoothness of
    `δ` on `V` in the set sense is therefore a hypothesis: condition (a) of
    `Polyfold.MPolyfold.TangentGermChart.IsRegular`. (Machine-checked in the round-trip audit:
    `RoundTrip/Items/V3_73.lean` and `V3_74.lean`, `not_B`, with `M = {(t³, t)} ⊆ ℝ²` and, at
    `(1, 1)`, the datum `N = ℝ(3, 1)`, `Y = ℝ(0, 1)`, `δ(v) = (∛(1 + v₁) − 1 − v₁/3)(0, 1)`, which
    is not differentiable at `v₀ = −(1/3)(3, 1)`.)
83. **"The subset `Σ = {v + y ∈ C | v ∈ V, y ∈ Y}` is relatively open in `C`" is false in
    general**, so the retraction `t : Σ ∩ O → Σ ∩ O`, `t(v + w) = v + δ(v)` of the proof of
    Theorem 3.27 need not be defined on a neighbourhood of `0` in `O`. Example: `E = ℝ³`,
    `C = [0, ∞)³`, `N = ℝ(1, 1, 1)`, `Y = {x + y − z = 0}`. `Y` is a good complement
    (`n + p ∈ C ⟺ n ∈ C` for `|p| ≤ ε|n|`), `N ∩ C` is a ray, and `π(x, y, z) = (x + y − z)(1, 1, 1)`,
    so `πz ∈ C ⟺ x + y ≥ z`: `Σ` is relatively closed in `C` and not open at `(1, 0, 1)`, and with
    `O = C`, `δ = 0` (`M = N ∩ C`) points `(ε, 0, ε + ε²) ∉ Σ` approach `0`. The sub-M-polyfold
    property of `M` holds nevertheless (project along `{x + y + z = 0}`), because a good complement
    `Y'` with `π'(C) ⊆ N ∩ C` always exists: in the normal form of Proposition 3.22, `N ∩ C` is
    `{ℓ_i ≥ 0, i ∈ Σ}` with `Q = (ℓ_i)_{i ∈ Σ} : N → ℝ^Σ` onto; `π'(z) := e⁻¹((ℓ_i(z))_{i ∈ Σ}, ρ(z))`
    (`ρ` any linear retraction onto `ker Q`) is a projection onto `N` with `π'(C) ⊆ N ∩ C`, and
    `ker π'` is a good complement (for `i ∈ Σ`, `ℓ_i(p) = 0` on `ker π'`; for `i ∉ Σ`,
    `ℓ_i ≥ c|n|` on `N ∩ C`). But `ϕ(M ∩ U)` then has to be re-written as a graph over `N` along
    `Y'`, through the quadrant inverse function theorem (Theorem 3.72) for
    `v ↦ v + π'δ(v)` (its degeneracy-index hypothesis holds because `ℓ_i ∘ π' = ℓ_i` and `ℓ_i`
    vanishes on `Y` for `i ∈ Σ`, Lemma 3.65), and the regularity problem of item 82 reappears
    for the inverse. In Lean the condition `π(O) ⊆ C` is the hypothesis (b) of `IsRegular`
    (`TangentGermChart.π_mem`); with it `Σ ∩ O = O ∩ π⁻¹(V)` is relatively open in `O`
    (`TangentGermChart.Sig_eq`).
84. **Theorem 3.27 as formalized** (`Polyfold.theorem_3_27`, `theorem_3_27_isSubMPolyfold`,
    `theorem_3_27_isChart`, `theorem_3_27_isTame`, `theorem_3_27_isManifoldWithCorners`): under
    `IsRegular` at every point (items 82–83), `M` is a sub-M-polyfold with the text's retraction
    `s = ϕ⁻¹ ∘ t ∘ ϕ` on `U₀ = ϕ⁻¹(Σ ∩ O)` (sc-smooth because `t ∘ R = Γ ∘ π ∘ R` for a retraction
    `R` onto `Σ ∩ O`, with `Γ = ι + δ : V → E` sc-smooth — the inclusion `ι : N → E` of a smooth
    finite-dimensional subspace is sc-smooth, `isScSmooth_subtype_val`, its level maps being
    the linear lifts `N → E_m`; the text says nothing about either), the charts `y ↦ π ∘ ϕ(y)` on
    `M ∩ U₀` with model `(V, N ∩ C, N)` are charts of the induced structure of Proposition 2.21
    (compatibility with the charts `ϕ'|_{W ∩ M}` of Proposition 2.21: the transition maps are
    `ϕ' ∘ ϕ⁻¹ ∘ Γ` and `π ∘ ϕ ∘ ϕ'⁻¹`), pairwise compatible by locality, and form an atlas
    equivalent to the induced one, with tame models (the identity retraction of `V`). "Manifold
    with boundary with corners" (Chapter 4) is here `MPolyfold.IsManifoldWithCorners`: an
    equivalent atlas of charts modelled on relatively open subsets of partial quadrants of
    `n`-dimensional spaces; their transition maps are classically smooth by
    `isScSmooth_iff_contDiffOn_const`. Tameness of `X` is not used in the proof (only that the
    chart models are tame retracts, a field of the data); the text's "Since `O` is a tame
    retract, there exist ... a tame sc-smooth retraction `r`" is Proposition 2.10 (1) for any
    retract. The degeneracy index of `M` is `d_M(y) = d_{N ∩ C}(π ∘ ϕ(y))` since the chart
    `π ∘ ϕ` has a tame model (`theorem_3_27_degIndex`, Proposition 2.36); Lemma 3.70
    (`d_{N ∩ C}(v) = d_C(v + δ(v))`, hence `= d_X(y)`, for `v ∉ N ∩ W` near `0`) is proved in the
    model `E = ℝⁿ ⊕ W` only (`lemma_3_70`) and not yet transported to a general presentation of
    `C`.

Found while assembling Theorem 3.54 (the graph description of the solution set) in
`GlobalIFT.lean`.

85. **"Ψ_*(g) = h + t, t = Ψ_*(s) an sc⁺-section `U' → F'`" and the data of Theorem 3.38.** The
    push-forward `t(u') = Ψ[1](ψ⁻¹u', s(ψ⁻¹u'))₂` has an `ℝᴺ`-component, while the data `𝒮` of
    Theorems 3.38/3.47 (`Polyfold.StabilityData`) carry only the `W`-component of the
    sc⁺-germ (item 63). The `ℝᴺ`-component is absorbed into the basic germ: `h' = h + (t_{ℝᴺ}, 0)`
    is again a basic germ with the same contraction `B` (Definition 3.7 constrains only the
    `W`-component: `(h'(x))₂ = (h(x))₂ = w − B(x)`), and `𝒮.fsum h' = h' + ι t_W = h + ι t`
    (`theorem_3_54_graph`, with the two components as sc-operators `ScBanach.qPartOp`,
    `ScBanach.wPartOp`). The text's "D(h + t)(0) is sc-Fredholm by Propositions 3.10 and 1.10,
    surjective, with kernel in good position" is `theorem_3_54_pushforward` for `Ψ_*(g)`; since
    `Ψ_*(g) = h + ι t` holds only on a neighbourhood of `0` (where the identities of the filler and
    of the conjugation hold), the derivatives are identified by the uniqueness of the derivative
    within the quadrant on level `1` and the density of `E₁` (`scDeriv_eq_of_eqOn_nhds`). The
    data `𝒮` are built by `StabilityData.exists_of_scPlus` (`1 + D₂t_W(0)` is sc-Fredholm by
    Proposition 1.10).
86. **The neighbourhood `V` of `x` in Theorem 3.54 (3)** (`ψ ∘ ϕ({y ∈ V | f(y) = 0}) =
    {v + σ(v) | v ∈ V'}`) is not specified in the text. It must be small enough that (i) the
    identities `f̃ = g` on `O` (Definition 3.4 (1)), "zeros of `g` lie in `O`" ((2)) and
    `Ψ(u, (g − s)(u))₂ = h(ψ(u))` hold on `ϕ(V)`, (ii) `ψ ∘ ϕ(V)` lies in the neighbourhood `U''`
    of Theorem 3.47 (3) where every zero of `h + t` is on the graph, and (iii) `ψ⁻¹` maps the
    graph points back into (i); `V'` is shrunk to `V₀ ∩ (1 + σ)⁻¹(U'' ∩ W')` (relatively open since
    `σ` is continuous, `σ(0) = 0`). Then `ψ ∘ ϕ` is injective on `V` and `f(y) = 0 ⟺ (h + t)(ψϕ(y)) = 0`
    for `y ∈ V` (`theorem_3_54_graph`). Tameness of the bundle enters only through
    `(1 − Dr(0))E ⊆ E₀` (item 50), assumed for the base retractions of all strong bundle charts
    (`htame`; the project has no "tame strong bundle" notion yet).
87. **What remains of Theorem 3.54 and of Theorems 3.19, 3.23, 3.24, 3.56, 3.57** (and why).
    (a) Theorem 3.54 (1), good position at the nearby zeros: Corollary 3.41 (now in
    `SolutionLinearization.lean`, concurrent work) gives surjectivity of `D(h + t)(x)` at zeros
    `x` near `0` in the chart at `x₀`; Lemma 3.55 gives the good position of
    `N_v = {n + Dσ(v)n}` (which is `ker D(h + t)(v + σ(v))`, by `N_v ⊆ ker` from differentiating
    `(h + t)(v + σ(v)) = 0` and `dim ker = ind = dim N_v`) to `C'_{v + σ(v)}` — but with the
    **added hypothesis `Y` closed**, which `theorem_3_47` does not record for its complement
    (it is `ψ⁻¹(Z ⊕ W)`, closed, but hidden in the existential). Definition 3.53 at the zero `y`
    is stated in a chart *centred at `y`* (`IsGoodPositionGerm f y`); transporting the good
    position of `ker D(h + t)(x')` from the chart at `x₀` to a chart centred at `y`, and to
    `T_yX`, is the recentring problem (Definition 2.38 in `T_xX`, gap G.13), not done.
    (b) Theorem 3.54 (2), the manifold structure, needs the `d`-dimensional tangent germ property
    of `S` (Definition 3.25) at every point: at `x₀`, the chart `ψ ∘ ϕ` (onto the retract `ψ(O)`,
    whose tameness is the invariance of tameness under the sc-diffeomorphism `ψ`, not
    formalized) with `N' = ker D(h + t)(0)`, `Y'`, `V'`, `σ` — where (ii) needs `σ` as an
    sc^∞-germ (Theorem 3.43 (1), not yet formalized, item 70; `theorem_3_47` gives `C¹`) — and at
    the other points of `S` the same data re-centred, (a) again. Then Theorem 3.27 applies, under
    its regularity conditions `IsRegular` (items 82–83), which the text's proof also needs.
    Formalized: `theorem_3_57_of_tangentGerm`, `theorem_3_56_of_tangentGerm` (Theorem 3.27 for the
    solution set; the `∂X = ∅` case with `d_S = 0` from Lemma 2.26). Theorems 3.19, 3.23 and
    Corollary 3.24 are the same statements for one zero / all zeros ("immediate consequences of
    Theorem 3.54"); their first claim in Theorem 3.19, "`f'(x₀)` is sc-Fredholm", is
    Proposition 3.52 (`proposition_3_52`). Theorem 3.23's "`S(f, U)` consists of smooth points"
    is `IsScFredholmSection.mem_smoothSet_of_isZeroAt` (regularizing).

Found while completing Theorem 3.54 (1) in the chart at `x₀` (`GlobalIFTFull.lean`,
`LocalSolvabilityClosed.lean`) and Proposition 3.26 (`TangentGerm.lean`).

90. **Proposition 3.26 as formalized** (`Polyfold.proposition_3_26`, `proposition_3_26_image`):
    for an sc-diffeomorphism `ψ : X → X'` with inverse `ψ'` (`IsScDiffeoOn` on `univ`) and
    `ψ(M) = M'`, `M'` has the `n`-dimensional tangent germ property iff `M` has it. The data of
    Definition 3.25 (2) at `ψ(x)` are the chart `ϕ ∘ ψ⁻¹` of Proposition 2.24 (`transportChart`)
    with the same `N`, `Y`, `V`, `δ` (`MPolyfold.TangentGermChart.transport`); `ψ(M) ⊆ X'_∞`
    because sc-smooth maps preserve the levels (`IsScSmoothOn.mapsTo_levelSet`). The text's first
    sentence "from `X' = ψ(X)` we conclude that `X'` is tame" is not needed: the tameness required
    by Definition 3.25 is that of the retract `(O, C, E)` of the chart, which is unchanged.
91. **Theorem 3.54, property (4) at the nearby zeros ("`f'(y)` is surjective and `ker f'(y)` is in
    good position, from Corollary 3.41 and Lemma 3.55"), is proved in the chart at `x₀` only**
    (`Polyfold.theorem_3_54_nearby`): for every zero `y` near `x₀`, with
    `z = ψ ∘ ϕ(y) = v + σ(v)`, `D(h + t)(z) : E'₀ → F'₀` is a surjective Fredholm operator of
    index `n − N` (Corollary 3.41, `StabilityData.exists_surjective_Dfs'_graph`), `z ∈ C'`, and
    the tangent space `N_v = {n + Dσ(v)n}` of the graph is in good position to `C'_z` with the
    closed good complement `Y` (Lemma 3.55, `lemma_3_55_relOpen`). Two steps separate this from
    Definition 3.53 at `y` (`IsGoodPositionGerm f y`). (a) `N_v = ker D(h + t)(z)`: the text
    passes from Lemma 3.55 (about `N_v`) to "`ker f'(y)` is in good position" without comment;
    `N_v ⊆ ker D(h + t)(z)` is the derivative of `(h + t)(v + σ(v)) = 0` along `N ∩ C'`, which
    needs `σ` of class `C¹` into `Y'₁` (`h + t` is differentiable on level `1` only) — the
    `C¹`-lift `σ₁` of Theorem 3.47 (1) (`theorem_3_47_sc_smooth`, item 70) — and then
    `dim N_v = dim ker D(h + t)(0) = ind = dim ker D(h + t)(z)`; not formalized. (b) The
    surjectivity of `f'(y) : T_yX → Y_y` does **not** follow from the surjectivity of `Dg(z₀)`,
    `z₀ = ϕ(y)`, for the filler `g` at `x₀`: Proposition 3.5 at `z₀` needs condition (3) of
    Definition 3.4 at `z₀` ("`(1 − ρ(r(u)))Dg(u)` restricted to `ker Dr(u)` is an isomorphism
    onto `ker ρ(r(u))`"), which the definition imposes at `u = 0` only and which does not
    propagate to nearby points (`u ↦ Dg(u)` is continuous for the strong operator topology, not
    in norm). The text's "proceeding as above we can construct a map `σ`" therefore re-centres
    at `y` with the filler of the sc-Fredholm germ `(f, y)` (Definition 3.14 (3)), and the
    passage from the chart at `x₀` to that chart needs the chart-independence of the
    linearization `f'(y) : T_yX → Y_y` (defined in Definition 3.4 through a filler) and of the
    good position of its kernel to `C_yX` (Definition 2.38, gap G.13 of Chapter 2): not
    formalized.
92. **Lemma 3.55 is applied to `σ : V' → Y'` on the relatively open `V' ⊆ N' ∩ C'` of Theorem
    3.47, not on all of `N' ∩ C'`** as the lemma is stated (`lemma_3_55`, `lemma_3_55_core`:
    `τ : N ∩ C → Y` of class `C¹` on the whole cone). In `lemma_3_55_relOpen` the map is extended
    to the cone by `σ ∘ Φ`, `Φ(v) = b(v) v` for a smooth bump `b` equal to `1` near `0` and to
    `0` outside a ball contained in `V'` (so `Φ` maps the cone, which is closed under nonnegative
    scaling, into `V'`); the extension agrees with `σ` near `0`, and its derivatives within the
    cone at the points near `0` are those of `σ` within `V'` (`fderivWithin_inter`). The
    conclusion "`N_v` is in good position to `C_z`" also needs the interior of `N_v ∩ C_z` in
    `N_v` to be nonempty, which Lemma 3.55 does not state: `n ↦ n + Dσ(v)n` carries the interior
    of `N ∩ C` into `C ⊆ C_z` as soon as `‖Dσ(v)‖ ≤ ε`, the good-complement constant of
    `(N, Y)`, which holds near `0` by the continuity of `Dσ` and `Dσ(0) = 0`. The general
    presentation `T` of `C'` enters only through the coordinate functionals `x ↦ (Tx)_i`
    (`coordCLMWith`), with which `C' = {ℓ_i ≥ 0}` and `C'_z = {ℓ_i ≥ 0 for ℓ_i(z) = 0}`.
93. **The closedness of the good complement `Y'` of Theorem 3.47 is recorded**
    (`Polyfold.theorem_3_43_closed`, `theorem_3_47_closed`): `Y' = Z ⊕ W` is closed and so is its
    image under the linear homeomorphism `ψ⁻¹` of Theorem 3.38; `theorem_3_47_sc_smooth` hides
    `Y` in an existential, and both Lemma 3.55 (item 49) and Definition 3.25 (item 81) need the
    closedness at the nearby zeros. `theorem_3_54_graph` now also records `Y` closed, the zeros
    `v + σ(v)` and the `C^k`-lifts `σ_k` of Theorem 3.47 (1) on `V_k ⊆ V'`.
94. **The data of Definition 3.25 (2) for the solution set at `x₀`, except the chart**
    (`SolutionGermRegularity.lean`, recorded in `theorem_3_54_graph`). (a) "`σ` is an sc^∞-germ"
    (Theorem 3.47 (1)) in the `k`-dependent reading of Definition 3.25 (ii) follows from the
    level-wise `C^k`-lifts `σ_k : V_k → E'_k` of `theorem_3_47_sc_smooth`
    (`isScInftyGermAt_of_lifts`: on `V_j`, `j = max(m, k) + 1`, compose `σ_j` with the inclusion
    `E'_j → E'_m`). (b) The kernel `N' = ker D(h + t)(0)` is a smooth subspace
    (`StabilityData.ker_Dfs_le_smooth`), which Definition 3.25 (2) requires and the text does not
    comment on: the `W`-component of the kernel equation reads `w = D₁B(0)a − ι Ds(0)(a, w)`
    (Lemma 3.9, `D₂B(0) = 0`), `D₁B(0)a ∈ W_∞` since `DB(0)` is an sc-operator and `a ∈ ℝⁿ` is
    smooth, and `Ds(0)` raises the level by one, so `w ∈ W_m` gives `w ∈ W_{m+1}`. What is still
    missing for Theorem 3.54 (2) at `x₀` is the chart `ψ ∘ ϕ` of Definition 3.25 (2) with its tame
    model `(ψ(O), C', E')`: the invariance of tameness under the sc-diffeomorphism `ψ` (condition
    (1) of Definition 2.34 by Theorem 1.25, `theorem_1_25`; condition (2) by transporting the
    sc-splitting `E = T_xO ⊕ A` with the sc-isomorphism `Dψ(x)` and `Dψ(x)E_x ⊆ E'_{ψ(x)}`), and
    at the other zeros `y ∈ S` the re-centring of this chart at `ψ ∘ ϕ(y)` (Finding 87 (a)); then
    Theorem 3.27 applies under `IsRegular` (items 82–83), i.e. `σ` sc-smooth on `V'` in the set
    sense and `π(ψ(O)) ⊆ C'`, both of which are hypotheses beyond the text.
95. **Tameness is carried by sc-diffeomorphisms** (`Chapter2/TameInvariance.lean`,
    `IsScDiffeoQuadrant.isTameRetract_image`): for a tame retraction `r : U → U` onto `O` and an
    sc-diffeomorphism `ψ : U → U'` between relatively open subsets of partial quadrants,
    `(ψ(O), C', E')` is a tame retract with the retraction `ψ ∘ r ∘ ψ⁻¹`. The text uses this
    silently (the chart `ψ ∘ ϕ` of the proof of Theorem 3.54 must be a chart of a tame M-polyfold
    for Definition 3.25; "`X' = ψ(X)` is tame" in the proof of Proposition 3.26). Condition (1)
    of Definition 2.34 is Theorem 1.25; condition (2) needs, at a smooth point `y = ψ(x)`, that
    `Dψ(x)` is an sc-isomorphism (`IsSc1With.scOperator_deriv`, true at smooth points only),
    which carries sc-subspaces and sc-splittings (`IsScSubspace.map`, `IsScSplitting.map`, with
    the level maps `scIsoLevel`), and that `Dψ(x)E_x ⊆ E'_y` (the one-sided sign argument,
    `IsSc1With.mapsTo_minimalSubspace`); the derivative of the transported retraction is
    `Dψ(x) Dr(x) Dψ'(y)` by the chain rule (`scDeriv_transport`).
96. **Theorem 3.54 (2) at the centre `x₀`** (`theorem_3_54_tangentGermChart`,
    `GlobalIFTCenter.lean`): the solution set `S = {y ∈ V | f(y) = 0}` has the data of
    Definition 3.25 (2) at `x₀` with `n = dim ker D(h + t)(0)`: the chart `ψ ∘ ϕ`
    (`MChart.compDiffeo`, a chart of the structure since its transition maps are
    `(ϕ' ∘ ϕ⁻¹) ∘ ψ⁻¹` and `ψ ∘ (ϕ ∘ ϕ'⁻¹)`), its model `(ψ(O), C', E')` tame by item 95, and
    `N`, `Y`, `V'`, `σ` from `theorem_3_54_graph` (items 93–94). The chart is taken on the whole
    domain `V` of `ϕ`, with `S` the solution set in the neighbourhood `V` of Theorem 3.54 (3)
    (the text's `S` is also the solution set *in `V`*), so no restriction of the retract is
    needed. Two things separate this from Theorem 3.54 (2) (and hence from Theorems 3.19, 3.23,
    3.24, 3.56, 3.57, which are `theorem_3_57_of_tangentGerm`/`theorem_3_56_of_tangentGerm` once
    the tangent germ property is known): the data at the other points `y ∈ S` (the re-centring
    at `ψ ∘ ϕ(y)`, items 87 (a), 91, 94), and the regularity conditions `IsRegular` under which
    Theorem 3.27 is proved (items 82–83), which the text's hypotheses do not give.

Found while formalizing Theorem 3.54 (1) at the nearby zeros in the chart at `x₀`
(`GlobalIFTNearbyGraph.lean`, `GlobalIFTNearbyKernel.lean`, `GlobalIFTNearbySurj.lean`,
2026-10-25).

100. **Theorem 3.54 (1) at the zeros `y ≠ x₀`: the surjectivity of `f'(y)` does not follow from
     Corollary 3.41 and Lemma 3.55, and is proved only under an added hypothesis.**  In the
     chart `c` at `x₀` with the filler `g`, at a zero `z₀ = ϕ(y)` of `g` near `0` the intrinsic
     linearization is `Tf̃(z₀) = Dg(z₀)|_{T_{z₀}O} : T_{z₀}O → K_{z₀}` (`linAt`, item 111).
     Corollary 3.41 gives the surjectivity of the filled `Dg(z₀) : E → F`.  With respect to the
     splittings `E = T_{z₀}O ⊕ ker Dr(z₀)`, `F = K_{z₀} ⊕ ker ρ(z₀)`,
     `Dg(z₀) = [[A, B], [0, C]]` with `A = Tf̃(z₀)` (the lower left block vanishes at a zero:
     `ρ(z₀)Dg(z₀)Dr(z₀) = Dg(z₀)Dr(z₀)`, `rho_scDeriv_comp_r`); `Dg(z₀)` onto gives `C` onto
     and `b ↦ [Bb]` an isomorphism `ker C ≅ coker A`, so **`Tf̃(z₀)` is onto iff
     `C(z₀) = (1 − ρ(z₀))Dg(z₀)|_{ker Dr(z₀)}` is injective** — condition (3) of Definition 3.4 at
     `z₀`, which the definition imposes at `0` only and which does not propagate (`u ↦ Dg(u)` is
     strongly, not norm, continuous; strongly continuous families of surjections may pass from an
     isomorphism to a non-injective operator).  The text's "(4) follows from Corollary 3.41 and
     Lemma 3.55" therefore has a gap for the surjectivity of `f'(y)`; the proof of Proposition
     6.2 (index stability) uses the same step ("`F'(λ, t, φ(t))` is surjective" for the intrinsic
     linearization, from the IFT for the filled one).  Equivalently: `ind Dg(z₀) = dim K` at all
     nearby zeros, `ind Dg(z₀) = ind A + ind C = dim ker A`, and `ind(f, y) = ind A =
     dim K − dim coker A`, so `coker Tf̃(z₀) = 0` is exactly the local constancy
     `ind(f, y) = ind(f, x₀)` along the solution set.  Formalized: `theorem_3_54_one` proves
     Theorem 3.54 (1) (`IsGoodPositionGerm f y` for all zeros `y` in an open `Vx ∋ x₀`) for an
     sc-Fredholm section under the **added hypothesis** `IsGoodPositionGermFilled`: the filler at
     `x₀` satisfies (3) at the zeros of `g` in `O` near `0` (as the "almost canonical" fillers
     of the applications do); the surjectivity step is Proposition 3.5 (1) at `z₀`
     (`exists_range_scDeriv_eq_ρ_of_normal_injective`), the chart independence is
     `isGoodPositionGerm_of_chart_dense` (item 117).  The kernel part needs no added hypothesis
     (`theorem_3_54_nearby_kernel`, items 101–104).
101. **`N_v = ker D(h + t)(z)`** (`StabilityData.graphSpace_eq_ker_Dfs'`; item 91 (a)).  The
     inclusion `N_v = {n + Dσ(v)n} ⊆ ker D(h + t)(v + σ(v))` is the derivative of
     `(h + t)(w + σ(w)) = 0` along `V'` at `v`, which needs the lifted graph map
     `Γ₁ = lift_K + σ₁ : V₁ → E₁` (`σ₁` the `C¹`-lift of Theorem 3.47 (1), `K` smooth so that it
     lifts linearly to `E₁`, `finLift`) because `h + t` is differentiable on level `1` only; the
     chain rule is applied within `V₁ ∩ Γ₁⁻¹(O_{G,1})` and the derivative is unique within `V₁`
     (`uniqueDiffWithinAt_relOpen_cone`).  Equality by the dimension count
     `dim N_v = dim K` (`n ↦ n + Dσ(v)n` is injective because `Dσ(v)` takes values in the
     complement `Yc`) `= ind D(h + t)(0) = ind D(h + t)(z) = dim ker D(h + t)(z)`, both operators
     being surjective (Corollary 3.41, `finrank_ker_eq_fredholmIndex_of_surjective`).
102. **`ker Dg(z₀) ⊆ T_{z₀}O` at a nearby zero is the tangency of the solution set to `O`**, not a
     filler property.  At `0` it is condition (3) of the filler (`IsFillerOf.ker_deriv_le_range`);
     at `z₀ ≠ 0` (3) is not available.  Instead: every graph point `w + σ(w)` is `ψ(u)` for a zero
     `u ∈ O` of `g` (condition (2) of Definition 3.4), so the transported retraction
     `r' = ψ ∘ r ∘ ψ⁻¹` (`IsScDiffeoQuadrant.transport`) fixes the graph points, and
     differentiating `r' ∘ Γ = Γ` along `V₁` at `v` (`scDeriv_apply_toBase_deriv_eq_of_fixed`)
     gives `Dr'(z) = 1` on `N_v`; with `Dr'(z) = Dψ(z₀)Dr(z₀)Dψ⁻¹(z)` (`scDeriv_transport`,
     item 95) and `ker Dg(z₀) = Dψ⁻¹(z)(N_v)` (item 104) this is `Dr(z₀) = 1` on `ker Dg(z₀)`.
103. **Good position of `ker Dg(z₀)` inside `T_{z₀}O`** (`theorem_3_54_chart_kernel` (d)):
     Lemma 3.55 gives the good position of `N_v` to `C'_z` in `E'` (item 92); the linear
     isomorphism `Dψ⁻¹(z) : E' → E` carries `C'_z` onto `C_{z₀}` (the one-sided sign argument
     `IsSc1With.mapsTo_partialQuadrant` for `ψ⁻¹` at `z` and for `ψ` at `z₀`,
     `scDeriv_mem_partialQuadrantAtWith_iff`; at the centre this is "`C' = Tψ(0)C`", item 50) and
     `N_v` onto `ker Dg(z₀)` (Lemma 3.45, `IsInGoodPosition.map`); a good complement `P` of
     `ker Dg(z₀)` in `E` restricts to the good complement `P ∩ T_{z₀}O` in `T_{z₀}O` with the
     same constant, because `ker Dg(z₀) ⊆ T_{z₀}O` (`IsInGoodPosition.isInGoodPositionIn_of_le`).
     This is condition (2) of Definition 3.53 at `y` in the chart at `x₀`; `theorem_3_54_one`
     transports it to the chart centred at `y` through `isGoodPositionGerm_of_chart_dense`.
104. **The chain rule for the push-forward at a nearby zero.**  `Ψ_*(g) = κ ∘ ψ⁻¹` with
     `κ(u) = (Ψ(u, g(u)))₂`; at a zero `z₀ ∈ U₁` of `g`, `Dκ(z₀) = Γ(z₀)Dg(z₀)` because the fibre
     derivative of a strong bundle map at `(z₀, 0)` is its fibre map (`scDeriv_fiber_at`,
     `scDeriv_fiber_comp_at`: the base direction drops out as `Γ(u)0 = 0`; this generalizes
     `scDeriv_fiber_zero` from `0` to `z₀`, cf. `scDeriv_fiber_of_vanishing`, item 112).  Hence
     `D(Ψ_*g)(z) = Γ(z₀) ∘ Dg(z₀) ∘ Dψ⁻¹(z)` and `ker Dg(z₀) = Dψ⁻¹(z)(ker D(Ψ_*g)(z))`
     (`scDeriv_pushforward_at`, `ker_scDeriv_eq_map`).  The derivative families chosen for
     `Ψ_*(g)` on `U'` and for `h + t = 𝒮.fsum h'` on the germ `G` agree at `z` because the two
     maps agree on `U' ∩ W'` (`scDeriv_eq_of_eqOn_nhds_at`: uniqueness within the quadrant on
     level `1`, then density of `E₁`); the text writes `Ψ_*(g) = h + t` as an identity.
105. **The perturbation argument of Proposition 6.2 for `Tf̃(z₀)`, and what it gives.**  The
     text's trick (parameters `λ`, section `F(λ, u) = g(u) + Σ λ_i s_i(u)`, IFT for the extended
     problem) can be set up in the chart at `x₀` without any new bundle isomorphism: for a
     finite-dimensional `Λ₀ ⊆ F_∞` of smooth vectors, `ẽ(λ, u) = ρ(r(u))(λ₁(π_K ψ(u)) + ĵ(λ₂))`
     with `λ₁ ∈ Hom(K, Λ₀)`, `λ₂ ∈ M`, is an sc⁺-germ (`ρ(r(u))` applied to a vector of a fixed
     finite-dimensional smooth subspace, lifted by `finLift`; the factor `λ₁(π_K ψ u)` through
     the sc-operator `(λ, u') ↦ (λ₁, π_K u')` and the bilinear evaluation `Hom(K, Λ₀) × K → Λ₀`,
     sc-smooth by Corollary 1.20), its zeros lie in `ℝ × O` (`ρ(r(u))ẽ = ẽ`, condition (2)), and
     the push-forward `F̃ = (h + t) ∘ pr + ι ê` is of the form basic germ + sc⁺-germ on
     `(Λ × Pn) ⊕ W`.  Two points the text does not address.  (a) **Good position at the corner
     fails for the naive extension**: `ker DF̃(0) ⊇ Λ × K`, and `ℝ × K` is in good position to
     `ℝ × C'` (Definition 3.21) only if `K` projects onto all boundary coordinates — for
     `n = (1, 0)` and a complement vector `p = (0, y)`, `n + p ∈ ℝ × C'` forces `y ∈ C'`, so a
     good complement must have its `E'`-component in `E'_0 = {ℓ_i = 0 ∀i}` and `K + E'_0 = E'`.
     Fix: tilt the kernel by directions `M ⊆ T_0(ψ(O)) ∩ E'_∞` with `K ∩ M = 0`,
     `K + M + E'_0 = E'` (they exist since `T_0O + E_0 = E` by tameness and `Dψ(0)E_0 ⊆ E'_0`),
     using `ĵ(m) = Dg(0)Dψ⁻¹(0)m ∈ ρ(0)F_∞`; then `ker DF̃(0) = {(λ, δw) | δw + λ₂ ∈ K}` has the
     complement `Λ₁ × M × Y'` with `Y' ⊆ E'_0` a complement of `(K ⊕ M) ∩ E'_0` in `E'_0`, and the
     `ε`-condition of Definition 3.21 holds for every `ε` (the complement's quadrant coordinates
     vanish).  (b) **The functional must be uniform in the zero**: `λ₁(π_K ψ(u))` with
     `π_K(v + σ(v)) = v` replaces the text-style `λ ℓ(u)` with `ℓ(z₀) = 1`, whose extended
     problem would depend on `z₀`.  Conclusion of the argument (not formalized): for each
     finite-dimensional `Λ₀ ⊆ F_∞` there is a neighbourhood `V(Λ₀)` of `x₀` with
     `ρ(z₀)Λ₀ ⊆ range Tf̃(z₀)` at every zero in `V(Λ₀)` (`T_{(0,z)}S̃ = ker DF̃(0, z)` by item
     101 for the extended problem, `ker DF̃(0, z) → Λ` onto, tangency to `ℝ × O` by item 102).
106. **The perturbation argument does not close the gap of item 100, because its neighbourhood
     depends on `Λ₀`.**  The assembly at a fixed zero `y` (`isGoodPositionGerm_of_chart_dense`:
     `range Tf̃(z₀)` is closed, so a dense subset `ρ(z₀)F_∞` suffices) needs `ρ(z₀)k̂ ∈
     range Tf̃(z₀)` for **all** smooth `k̂` at that `y`, while item 105 gives it for `k̂ ∈ Λ₀`
     only when `y ∈ V(Λ₀)`, and `V(Λ₀)` comes from Theorem 3.47 for the `Λ₀`-extended problem,
     with no control in `Λ₀` (one would have to show that the radii of Theorems 3.40/3.43/3.47
     for the extended problem can be chosen independent of the finite-dimensional parameter
     space, which the black-box statements do not provide; `coker Tf̃(z₀)` is
     finite-dimensional by Proposition 3.52 at `y` and spanned by smooth vectors, but the
     spanning set depends on `y`).  Since `coker Tf̃(z₀) = 0` is equivalent to the index stability
     of Proposition 6.2 (item 100), whose proof in the text has the same gap, the status of
     Theorem 3.54 (1) at the nearby zeros with the text's Definition 3.4 is: **the kernel
     statements hold; the surjectivity of `f'(y)` is proved under condition (3) of the filler at
     the nearby zeros, and is open otherwise.**

107. **The linear algebra of the λ-extension is formalized** (`GlobalIFTNearbyPerturb.lean`),
     the rest of the perturbation argument is not.  `mem_lineality_of_goodComplement_prod` and
     `sup_lineality_eq_top_of_goodComplement_prod` are the obstruction of item 105 (a): a good
     complement of `ℝ × N` with respect to `ℝ × C` (any cone `C` with `0 ∈ C`, closed under
     nonnegative scaling) projects into the lineality space `C ∩ (−C)`, so `ℝ × N` is in good
     position only if `N + (C ∩ −C) = V`; in particular the kernel `ℝ × K` of the naive extension
     (parameters multiplying `ℓ(u)k̂` with `ℓ(0) = 0`) is **not** in good position at the corner
     unless `K` surjects onto the boundary coordinates, and Theorem 3.47 does not apply.
     `isInGoodPosition_extendedKernel` is the fix: in `(Λ × Pn) ⊕ W` the tilted kernel
     `Ñ = {((λ, a), w) | (a, w) + j(λ) ∈ K}` is in good position to `(Λ × C̃) ⊕ W` for every
     linear `j : Λ → Pn ⊕ W` with `K ∩ j(Λ) = 0`, `(K ⊔ j(Λ)) ⊕ Y' = Pn ⊕ W` with `Y'` in the
     lineality space, and `K ⊔ j(Λ)` meeting the interior of `C̃ ⊕ W`; the good complement is
     `Λ_c × Y'` (`Λ_c` a complement of `ker j`) and the `ε`-condition of Definition 3.21 holds for
     every `ε` — the precise content of the text's "has a complement contained in `T^R`" in the
     proof of Proposition 6.2.  Not formalized (items 105–106): the extended basic germ and its
     sc⁺-perturbation on `(Λ × Pn) ⊕ W`, its derivative at the zeros `(0, v + σ(v))`, Theorem
     3.47 for it, and the tangency argument giving `ρ(z₀)Λ₀ ⊆ range Tf̃(z₀)` on a neighbourhood
     `V(Λ₀)` of `x₀`; since that neighbourhood depends on `Λ₀`, the formalization was stopped
     here (item 106).

Found while formalizing the linearization of a section at a zero in charts and its chart
independence (`LinearizationCharts.lean`, 2026-10-25), the local form of gap G.13 that Definition
3.53 needs at a zero which is not the centre of the chart.

110. **Definition 3.53 presupposes the chart independence of `f'(x)` and of good position, which
     the text does not prove.** Definition 3.53 is stated in `T_xX` with `f'(x) : T_xX → Y_x` and
     the partial cone `C_xX` of Definition 2.38; Definition 2.38 appeals to Proposition 2.30 for
     `T^R_xX` and `C_xX`, but `f'(x)` is defined (before Definition 3.4) only at the centre of a
     chart, as `D(f̃ ∘ r)(0)|_{T₀O}`, and identified with `Dg(0)|_{T₀O}` for a filler `g`;
     neither its independence of the chart nor that of the two conditions of Definition 3.53 is
     shown. The proof of Theorem 3.54 uses both at the zeros `y ≠ x₀` ("proceeding as above",
     item 91 (b)). Formalized: `Polyfold.linAt_chart_change`, and
     `Polyfold.StrongBundle.linAt_chart_independence`: for two strong bundle charts of `P` around a
     zero `y`, the linearizations `Lin(z) : T_zO → K_z` and `Lin'(z') : T_{z'}O' → K'_{z'}` are
     conjugate by isomorphisms `A`, `Γ`, so they are simultaneously surjective, simultaneously
     Fredholm with the same index, and their kernels are simultaneously in good position to the
     partial cones `C_zO`, `C_{z'}O'` (the conjugation algebra: `surjective_iff_of_conj`,
     `isFredholm_iff_of_conj`, `ker_eq_map_of_conj`, `dense_image_of_conj`,
     `IsInGoodPositionIn.transport`).
111. **The linearization at a zero in an arbitrary chart needs no filler** (`Polyfold.linAt`,
     `rho_scDeriv_comp_r`, `linAt_eq_scDeriv`, `IsFilledVersion.fillerRestrict_eq_linAt`):
     `Lin(z) = D(f̂ ∘ r)(z)|_{T_zO}`, `T_zO = Dr(z)E`, is defined at every level-`1` point `z` of
     the retract of every chart. At a zero its values lie in `K_z = ρ(z)F` (the text's
     "`ρ(0)Tf(0) = Tf(0)`", at any zero: the derivative of `(u, k) ↦ ρ(u)k` at `(z, 0)` is
     `(h, k) ↦ ρ(z)k`, `scDeriv_fiber_of_vanishing`, the generalization of
     `StrongRetr.scDeriv_fiber_zero` from `0` to `z`); `K_z` is the fibre `{k | (z, k) ∈ K}`
     (`mem_rangeS_ρCLM_iff`). For every `g` agreeing with `f̂` on `O` near `z`,
     `D(f̂ ∘ r)(z) = Dg(z)Dr(z)` (`scDeriv_comp_r_eq_of_eventuallyEq`, the text's
     "`Tg(0) = Tf(0)` on `T₀O`" at any point), so `Lin(z) = Dg(z)` on `T_zO`; at a centre this is
     `Tf̃(0) = fillerRestrict` of Proposition 3.5. At `z ≠ 0` the full `Dg(z) : E → F` is not
     related to `Lin(z)` (condition (3) of Definition 3.4 holds at `0` only, item 91 (b)); in
     particular `ker Dg(z)` need not lie in `T_zO`, and the relevant kernel is
     `ker Dg(z) ∩ T_zO = ker Lin(z)`.
112. **Only the fibre derivative survives at a zero.** The transition of strong bundle charts is
     `Θ(x, h) = Φ'Φ⁻¹(x, h) = (τ(x), Γ(x)h)`, `τ = φ' ∘ φ⁻¹`, with `Γ(x)` linear on the fibre
     `K_x` (`StrongBundleChart.transition_fst`, `transition_snd_add`, `transition_snd_smul`).
     Differentiating `f̂'(τ(r(u))) = Θ(r(u), f̂(r(u)))₂` at `z` gives a base-direction term, the
     derivative of `x ↦ Γ(x)f̂(z)`, and the fibre term `Γ(z)D(f̂ ∘ r)(z)`; the first vanishes
     because `f̂(z) = 0` (formally: `Θ(x, 0) = (τ(x), 0)` near `z`, so the map
     `(u, k) ↦ Θ(R(u, k))₂` vanishes on the zero section and `scDeriv_fiber_of_vanishing`
     applies). Hence `Γ(z) ∘ Lin(z) = Lin'(z') ∘ A` with `A = D(τ ∘ r)(z)|_{T_zO}`. The text
     does not state this; it is also why the linearization is chart independent only at zeros.
113. **`Γ(z)` is a topological isomorphism `K_z ≅ K'_{z'}`**
     (`StrongBundleChart.transitionFiberCLM`): it needs `Φ⁻¹` linear on the fibres of `K`
     (`symm_add`, `symm_smul`: `Φ` is a fibrewise linear bijection of `P⁻¹(x)` onto `K_{φ(x)}`)
     and continuous (`Φ` is a homeomorphism); the inverse is the fibre map of the reverse
     transition (`transition_transition`). The text's "bounded linear on the fibres"
     (Definition 2.50) is a condition on `Φ` only.
114. **Proposition 2.30 for the partial cone is applied on the overlap retracts.** The base
     transition `τ` is a germ of sc-diffeomorphisms between `φ(V ∩ V') = O ∩ W` and
     `φ'(V ∩ V') = O' ∩ W'` with the restricted retractions `r|_{U ∩ r⁻¹(W)}` of Proposition
     2.10 (1) (`ScRetraction.IsDiffeoGerm` built from the compatibility of the base charts); the
     derivative of the restricted retraction at `z` is `Dr(z)` (`scDeriv_eq_of_eqOn_relOpen`,
     uniqueness of the derivative on a smaller relatively open domain), so `proposition_2_30_cone`
     gives `A(T_zO ∩ C_z) = T_{z'}O' ∩ C'_{z'}` for the formalized partial cone `partialConeWith`
     of Definition 2.27, and `IsDiffeoGerm.deriv_inv_deriv`/`deriv_deriv_inv` the inverse
     `D(τ' ∘ r'_{W'})(z')`. Good position inside `T_zO` is stated with the partial quadrant
     `C_z = partialQuadrantAtWith T z` (only points of `T_zO` are tested, so this is good
     position to `C_zO`); at a centre `C_0 = C` (`partialQuadrantAtWith_zero`).
115. **Good position inside a subspace is carried by an isomorphism of the subspaces**
     (`Polyfold.IsInGoodPositionIn.transport`, `isInGoodPositionIn_transport_iff`): with the
     constant `ε' = ε/(‖A‖‖A⁻¹‖ + 1)` of Lemma 3.45 (`IsGoodComplement.map`) and the interior
     condition through the homeomorphism `N ≅ A(N)` (no finite dimensionality needed). The
     Fredholm part of the conjugation algebra (`isFredholm_iff_of_conj`, through
     `isFredholm_equiv_comp_equiv`) needs the completeness of `T_zO` and `K_z`, which holds
     because they are the ranges of the idempotents `Dr(z)` and `ρ(z)` (closed).
116. **Hypotheses of the chart change** (`linAt_chart_change`): of the compatibility of
     Definition 2.50 only the sc-smoothness of `Θ = Φ' ∘ Φ⁻¹` on `[0]` is used — not `[1]`, and
     not the reverse transition. For two strong bundle charts of `P` (`StrongBundle.IsChart`) it
     holds because both are charts of the M-polyfold `Y[0]`
     (`StrongBundle.IsChart.transition_isScSmoothRetractMap`, by the locality of compatibility
     `MPolyfold.IsChart.compatible`), and the base charts are compatible because both are charts
     of `X`; so no compatibility hypothesis is added. The points `z`, `z'` need only be on level
     `1` (as in `proposition_2_30_cone`); the text has smooth points. Tameness is not used. The
     section is assumed sc-smooth (its principal parts are then sc-smooth in every strong bundle
     chart of `P`, `IsScSmoothSection.isScSmoothRetractMap`), as in Definition 3.14 (1).
117. **Definition 3.53 at a zero from a non-centred chart**
     (`Polyfold.StrongBundle.isGoodPositionGerm_of_chart_dense`, `_of_chart`, `_of_linAt`,
     `_of_linAt_surj`): if `(f, y)` is an sc-Fredholm germ with
     `f(y) = 0` and, in some strong bundle chart `c` of `P` around `y` (e.g. the chart centred at
     `x₀`, with `g` its filler, which agrees with `f̂` near `φ(y)` for `y` near `x₀` by
     `Filter.Eventually.eventually_nhds`), the range of `Dg(z)|_{T_zO}` contains `ρ(z)F_∞` and
     `ker Dg(z) ∩ T_zO` is in good position to `C_{φ(y)}` inside `T_zO`, then
     `StrongBundle.IsGoodPositionGerm f y` holds in the chart `c'` centred at `y` given by
     Definition 3.11. Two steps beyond the chart change: (a) the kernel condition of
     `IsGoodPositionAt` is about `ker Dg'(0)` for the filler `g'` of `c'`, which is
     `ker Tf̃'(0) ⊕ 0` by condition (3) at the centre (`IsFillerOf.ker_deriv_le_range`, the text's
     "`ker Tf̃(0) ⊕ {0} = ker Dg(0)`"); (b) the surjectivity of `Tf̃'(0)` needs only a dense
     subset of `K_z` in the range of `Lin(z)`: the range of `Tf̃'(0)` is closed (Proposition 3.52
     in `c'`, `proposition_3_52_local`) and contains the dense image under `Γ` of `ρ(z)F_∞`
     (`F_∞` is dense in `F` and `ρ(z)` is a continuous projection onto `K_z`). Not done here: the
     two hypotheses in the chart at `x₀` at `z₀ = φ(y)`, i.e. the passage from the conclusions
     of `theorem_3_54_nearby` in the push-forward chart `ψ ∘ ϕ` (about `D(h + t)(z')` on `E'` and
     the tangent space `N_v` of the graph) to `Dg(z₀)|_{T_{z₀}O}` (block 100–109).

Found while redoing the sharper Proposition 3.52 (`FredholmGermIndex.lean`, 2026-10-26).

120. **Proposition 3.52: the index of `Tf(x)` is the index `n − N` of the conjugating basic germ,
     for the specific conjugation data** (`Polyfold.proposition_3_52_index`,
     `proposition_3_52_local_index`, `ConjugationData.scDeriv_isFredholm_index`).
     `proposition_3_52` states the index as "`n − N` for some natural numbers `n`, `N`", which
     every integer is (comparison row V3.46). The witnesses of `IsConjugateToBasicGerm` (an
     existential proposition) are now the structure `Polyfold.ConjugationData`, with the
     parameter space `Pn = ℝⁿ` and the finite-dimensional target `Q = ℝᴺ` of the basic germ named
     (`isConjugateToBasicGerm_iff_nonempty`). For **every** conjugation `d` of `g − s` to a basic
     germ `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`, `ind Tf(x₀) = ind Dg(0) = ind D(g − s)(0) =
     dim d.Pn − dim d.Q`, and such data exist. In particular the number `n − N` is the same for all
     conjugations of one germ (`ConjugationData.index_eq`; the text's "the Fredholm index is
     invariant under strong bundle isomorphisms" after Theorem 3.38, for the conjugations of one
     germ). No hypothesis added. The old statements are kept (they are consumed by `GlobalIFT.lean`
     and others) and the new theorems stand next to them; the proofs are those of
     `FredholmGermLinearization.lean` with the dimensions carried along. The half-done
     `patches/prop_3_52_sharpen.patch`, which changed the consumed statements, was redone this way
     and removed.

Found while formalizing Corollary 3.39 (`BasicClassComposition.lean`, 2026-10-26).

121. **Corollary 3.39 as formalized** (`Polyfold.corollary_3_39`,
     `corollary_3_39_isConjugate`). Hypotheses: `g : U → F` sc-smooth (the text's "sc-germ";
     used only so that `(g + s)¹` takes values on level `1`) and conjugated to a basic germ
     (`IsConjugateToBasicGerm`, read as the text's "equivalent by a strong bundle isomorphism `Φ`
     to the basic germ `Φ_* g`"; `g(0) = 0` follows), `s : U → F¹` sc-smooth with `s(0) = 0` (the
     text's `s : O(C, 0) → (F, 0)`). Conclusion: `(g + s)¹ = levelMap (g + ιs) 1 : U¹ → F¹` is
     conjugated to a basic germ on the shifted structures `E¹ ◁ F¹`, by the explicit composite
     `Γ = Λ ∘ Φ¹` (`ConjugationData.compIso`, inverse `Φ'¹ ∘ Λ⁻¹`): `Φ¹` the index raise of the
     given conjugation `Φ`, `Λ = (split, fiber)` the coordinate change of Theorem 3.38 for the
     data `𝒮` built from `t_W`, `t = Φ[1]_* s` (`ConjugationData.pushPlus`). The basic germ is
     `𝒮.pushMap h'` with `h' = h + (t_{ℝᴺ}, 0)` (`ConjugationData.absorb`, Finding 85), its
     contraction `𝒮.pushB B`. The text's `Γ = Ψ ∘ Φ` followed by the index raise is the same map:
     `Λ₀ ∘ Φ` (level-`0` operators `split₀`, `fiber₀`) is a strong bundle isomorphism and
     `(Λ₀ ∘ Φ)¹ = Λ ∘ Φ¹` on `U¹ ⊕ F¹` (`ConjugationData.compIso_eq_strongShift`, from
     `strongShift_linIso₀` and `IsStrongBundleMap.strongShift_comp`). No hypothesis added beyond
     the reading of "sc-germ" and of the equivalence; the text's "strong bundle map `Ψ`" is a
     strong bundle isomorphism (`StabilityData.linIso_isStrongBundleIso`), as
     `IsConjugateToBasicGerm` requires. The text's `τ : Z → C` is not applied (Finding 60).
122. **The index raise of a strong bundle isomorphism is a strong bundle isomorphism of the
     shifted structures** (`Polyfold.strongShift`, `IsStrongBundleMap.shift`,
     `IsStrongBundleIso.shift`), used silently by the text whenever it writes `((Ψ ∘ Φ)_*(·))¹`.
     For `Ψ : U ◁ F → U' ◁ F'` the level-`1` map `Ψ¹` satisfies Definition 2.47 for
     `U¹ ◁ F¹ → U'¹ ◁ F'¹`: the filtration `(U¹ ◁ F¹)_{m,k} = U_{m+1} ⊕ F_{k+1}` is preserved
     because `k + 1 ≤ (m + 1) + 1`, and the two sc-smoothness axioms are Proposition 1.17
     (`IsScSmooth.shift`) because `(U¹ ◁ F¹)[0]` is the shift of `(U ◁ F)[0]` and `(U¹ ◁ F¹)[1]`
     (levels `E_{m+1} ⊕ F_{m+2}`) the shift of `(U ◁ F)[1]`; on `[1]` one checks
     `(Ψ¹)[1] = (Ψ[1])¹` on level `1`. No hypothesis beyond `U` relatively open in a partial
     quadrant. Theorem 3.38's linear change `Λ` could be stated as an `IsStrongBundleIso` between
     the shifted structures as the types stand (`StabilityData.linIso_isStrongBundleIso`, for
     every relatively open `U` in `(C̃ ⊕ W)¹`, target `ψ(U) = glue⁻¹(U)` relatively open in
     `(C̃ ⊕ C) ⊕ X¹`); no weaker form was needed. Its axioms reduce to the sc-smoothness of the
     sc-operators `split ⊕ fiber` on `[0]` and `split ⊕ fiber¹` on `[1]`
     (`ScOperator.isStrongBundleIso_prodMap`, for any pair of sc-operators with inverses).
123. **Composition and push-forwards** (`IsStrongBundleMap.comp`, `IsStrongBundleIso.comp`,
     `IsStrongBundleIso.pushforward_comp`). The composition of strong bundle isomorphisms
     (covering sc-diffeomorphisms; the base map of the composite is the composite of the base
     maps, `IsStrongBundleMap.base_comp`) is one, with `(Λ ∘ Φ)[1] = Λ[1] ∘ Φ[1]` on `U ⊕ F₁`
     (`shiftFiber_comp`), and `(Λ ∘ Φ)_* g = Λ_*(Φ_* g)` on the target of `Λ` for every `g`. In
     Corollary 3.39 `Γ_* = Λ_* ∘ Φ¹_*`, and the text's "clearly `Φ_*(g + s) = h + t`" holds only
     near `0`, where the conjugation identity holds (`corollary_3_39`: `Φ_*(g + s) = 𝒮.fsum h'`
     on `ϕ(U ∩ N)` for a neighbourhood `N` of `0`). The identity
     `(Γ(u, (g + s)¹(u)))₂ = 𝒮.pushMap h'(γ(u))` is checked on level `0` through the injective
     inclusion `F'₁ → F'₀` (`ι Ψ¹ = Ψ ι`, `toBase_strongShift`), for `u ∈ U¹` so small that
     `ϕ¹(u)` lies in the level-`1` part of the germ of `h` (continuity of `ϕ` on level `1`).

Found while choosing the good complement of the solution set so that its projection maps the
partial quadrant into itself (`GoodComplementProjection.lean`; the `_proj` theorems in
`LocalSolvabilityClosed.lean`, `GlobalIFT.lean`, `GlobalIFTCenter.lean`, 2026-10-26).

130. **Condition (b) of `IsRegular` is not a restriction for the solution set of an sc-Fredholm
     section: the good complement can be chosen** (`Polyfold.theorem_3_54_tangentGermChart_proj`).
     The step of the proof of Theorem 3.27 that fails in general (item 83) is "the subset
     `Σ = {v + y ∈ C | v ∈ V, y ∈ Y}` is relatively open in `C`", on which the retraction
     `t(v + w) = v + δ(v)` is defined. `Σ` is relatively open as soon as the projection `π` onto
     `N` along `Y` maps the retract `O` into `C` (then `Σ ∩ O = O ∩ π⁻¹(V)`,
     `TangentGermChart.Sig_eq`), and it need not be for an arbitrary good complement (item 83:
     `C = [0,∞)³`, `N = ℝ(1,1,1)`, `Y = {x + y − z = 0}`). Definition 3.25 lets `Y` be any good
     complement, so for an arbitrary subset `M` with the tangent germ property the repair needs a
     re-graphing of `ϕ(M ∩ U)` over `N` along a better complement (item 83, not done; `π(O) ⊆ C`
     stays a hypothesis of `theorem_3_27`). For the solution set `S` at `x₀` the complement is
     not given but produced by the proof of Theorem 3.54 (Corollary 3.47, Theorem 3.43,
     Lemma 3.46, Theorem 3.78), and every step of that chain works with a complement that has
     the projection property (items 131–133). So the claim "`Σ` is relatively open" is repaired
     by choosing `Y` in Theorem 3.43, not by changing the proof of Theorem 3.27:
     `theorem_3_54_tangentGermChart_proj` gives the `TangentGermChart` of
     `theorem_3_54_tangentGermChart` (chart `ψ ∘ ϕ` onto `ψ(O) ⊆ C'`) with `π(ψ(O)) ⊆ C'`.
     Together with condition (a) (`σ` sc-smooth on `V'` in the set sense, item 82) this is
     `IsRegular` (`TangentGermChart.isRegular_of_projectsInto`). Condition (a) and the data at
     the other points of `S` (items 87 (a), 96) are still missing.
131. **The finite-dimensional lemma of item 83, and a case the sketch there misses**
     (`Polyfold.exists_goodComplement_projectsInto`, `exists_proj_goodComplement`, in coordinates
     `exists_proj_quadCone`): a finite-dimensional `N` in good position to a partial quadrant `C`
     in an sc-Banach space `E` has a closed good complement `Y = ker π` with `π(C) ⊆ N ∩ C` for the
     projection `π` onto `N` along `Y` (`ProjectsInto C N Y`). Construction: a set `S` of
     coordinates (`exists_coordSet`) with `Q_S = (ℓ_i)_{i ∈ S} : N → ℝ^S` onto,
     `N ∩ C = {n ∈ N | ℓ_i(n) ≥ 0, i ∈ S}` and `ℓ_i > 0` on `N ∩ C ∖ {0}` for `i ∉ S`; a continuous
     projection `p_N : E₀ → N` (Hahn–Banach, `Submodule.ClosedComplemented.of_finiteDimensional`)
     and a right inverse `g` of `Q_S`; `π(z) = p_N(z) + g(ℓ_S(z − p_N(z)))`. Then `π = id` on `N`
     and `ℓ_i ∘ π = ℓ_i` for `i ∈ S`, so `π(C) ⊆ N ∩ C`. On `ker π` the coordinates in `S` vanish,
     and for `i ∉ S`, `ℓ_i(n) ≥ c|n|` on `N ∩ C` (compactness of the unit sphere of `N`,
     `exists_coord_ge`), so `|p| ≤ ε'|n|` with `ε' ≤ c/(‖ℓ_i‖ + 1)` gives the good-complement
     estimate; `Y` is closed as a kernel. Item 83 takes `S = Σ` (the indices vanishing at some
     nonzero point of `N ∩ C`). This works when `Σ ≠ ∅` (the first case of the normal form,
     `mem_quadCone_of_vanIdx`) and when `N ∩ C = N` (by Lemma 3.65, in good position this case
     occurs only for `N = 0` or `C = E`). It fails in the remaining case `Σ = ∅`, `N ∩ C ≠ N`
     (the second case of the normal form: `N` a line, `N ∩ C` a half-line on which all
     coordinates are positive). There `ℝ^Σ = 0`, the formula of item 83 reduces to an arbitrary
     projection `ρ`, and `ρ(C) ⊆ C` fails in general: for `C = [0,∞)²`, `N = ℝ(1,1)`, the line
     `ℝ(1,2)` is a good complement, and the projection along it maps `(0,1)` to `−(1,1)`. In that
     case one coordinate `j₀` is kept, `S = {j₀}`, `π(z) = (ℓ_{j₀}(z)/ℓ_{j₀}(y))y`.
     `N ∩ C = {ℓ_{j₀} ≥ 0}` then follows from the segment argument of `mem_quadCone_of_vanIdx`,
     which holds for any `S` with the positivity property outside `S`
     (`mem_quadCone_of_coordSet`).
132. **Theorem 3.43 works with any good complement of `K̃`, and the projection property passes
     to `Z ⊕ W`** (`Polyfold.IsGoodComplement.prod_top_graph`,
     `ShiftedBasicData.exists_sol_of_goodComplement`, `ProjectsInto.prod_top_graph`,
     `ShiftedBasicData.exists_sol_proj`, `Polyfold.theorem_3_43_proj`). In the text's proof the
     complement `Z` of `K̃ = ker DH(0)` comes from a good complement `Y'` of `K'` (Lemma 3.46).
     Nothing downstream needs that origin: Theorem 3.78 takes any good complement of `K̃`, and
     for *every* good complement `Z` of `K̃` (constant `ε`), `Z ⊕ W` is a good complement of
     `K' = {(α, Lα) | α ∈ K̃}` with constant `ε/(1 + ‖L‖)` (the second half of the proof of
     `lemma_3_46`). Lemma 3.46 is needed only for the good position of `K̃`. So the data `Sol`
     of the proof exist with a prescribed `Z`. With the `Z` of item 131, the projection along
     `Z ⊕ W` onto `K'` is `(a, w) ↦ (π_Z a, Lπ_Z a)`, and `C' = C̃ ⊕ W` constrains only the first
     component, so it maps `C'` into `K' ∩ C'`. This gives `theorem_3_43_proj`, which is
     `theorem_3_43_closed` with the conjunct `ProjectsInto (C̃ ⊕ W) K' Y`.
133. **Propagation to Corollary 3.47 and Theorem 3.54** (`Polyfold.theorem_3_47_proj`,
     `theorem_3_54_graph_proj`, `theorem_3_54_tangentGermChart_proj`). In Corollary 3.47,
     Theorem 3.43 is applied to the conjugated germ in `E'' = (ℝⁿ' ⊕ ℝᴺ') ⊕ X` with the partial
     quadrant `(C̃ ⊕ ℝᴺ') ⊕ X` (the finite-dimensional factor `ℝᴺ'` of Theorem 3.38 is free).
     The linear coordinate change `ψ⁻¹` of Theorem 3.38 maps it onto `C̃ ⊕ W`, so `ProjectsInto`
     is carried by `ψ⁻¹` together with the good complement (`ProjectsInto.mapL`, as
     `IsGoodComplement.map` for Lemma 3.45). In Theorem 3.54 the shrinking of `V'` leaves `Y`
     unchanged. For the chart `ψ ∘ ϕ`, `ψ(O) ⊆ C'`, so `π(ψ(O)) ⊆ C'`
     (`TangentGermChart.π_mem_of_projectsInto`). The long proofs of `theorem_3_47_closed`,
     `theorem_3_54_graph` and `theorem_3_54_tangentGermChart` now prove the `_proj` versions (the
     new conjunct carried along), and the old theorems, with unchanged statements, are their
     corollaries.

Found while writing the exposition of §§3.4–3.5 and the application (`Chapter3.md` §5, §8;
2026-10-25). Statement numbers and pages are the preprint's *(book 2017: see `BookConcordance.md`)*.

140. **The toy contraction germ of `Chapter3.md` §0/§3 is a basic germ but not the local model of
     an sc-Fredholm section.** For `B(a, w) = aw + β(a)`, `β(a)_k = a e^{−k/a}`, on `[0,∞) ⊕ W` with
     `|w|_m² = Σ e^{2mk}|w_k|²`, the vector `β(a)` lies in `W_m` exactly when `m < 1/a`; the zero
     `(a, δ(a))`, `δ(a) = β(a)/(1 − a)`, at `a = 0.3` lies on level 3 and not on level 4. So the
     section `w ↦ w − B(a, w)` is not regularizing, and the forcing `a ↦ β(a)` is not sc⁺ on any
     neighbourhood of `0`. This qualifies the remark of p. 90 that basic germs are "the local
     models" of sc-Fredholm germs: a basic germ alone need not come from an sc-Fredholm section,
     whose zeros are smooth points (Definition 3.14, regularizing). The application of §8 uses the
     smoothed forcing `a(e^{−k/a − k²})_k`, which is sc-smooth on an open set.
141. **Shrinking of the parameter regions with the level is forced by the formalism; the further
     shift `s_k = 2^k − 1` of item 2 is an artefact of the proof.** In the example of `Chapter3.md`
     §8 the solution germ `δ` is sc-smooth on all of `[0, ½)` in the set sense, yet every working
     form of its contraction germ (`ContractionGerm`, Definition 3.28 with explicit regions) must
     have parameter regions `N(m)` shrinking with `m` (numerically `N(m) ⊆ [0, 0.381)` for `m = 8`,
     `[0, 0.201)` for `m = 12`, `[0, 0.054)` for `m = 30`, roughly `1/(m − 2√m)`), because the
     contraction estimate on level `m` fails for larger `a`. So a germ of neighbourhoods shrinking
     with the level is unavoidable in Definition 3.28, while the additional `2^k − 1` levels lost
     in `theorem_3_33` are not needed in this example (cf. item 2's toy example).
142. Typos found while writing §5 *(book 2017: all four unchanged: Theorem 3.10, p. 80; proof of
     Theorem 3.12, p. 91; Lemma 3.7, p. 92; Appendix 3.8.2, proof of Lemma 3.9 (restated there as
     Lemma 3.22), p. 116)* *(book 2021: two unchanged, Theorem 3.4.2, p. 114, and Appendix 3.8.2, proof of Lemma 3.5.10, p. 160; two corrected, the proof of Theorem 3.5.6, p. 127, has `δ(0) = 0`, and the proof of Lemma 3.5.8, p. 128, has `P' ∘ Dg(0)`)*: p. 90 (Theorem 3.38), "`ϕ : (U, 0) → (V, 0)`" for
     `(U', 0)` (the isomorphism `Φ` covers a map onto `U'`); p. 102 (proof of Theorem 3.43),
     "`δ(a) = 0`" for `δ(0) = 0`; p. 103 (Lemma 3.44), "`P' ∘ g(0)(α, Dδ(0)α)`" for
     `P' ∘ Dg(0)(α, Dδ(0)α)`; p. 131 (Appendix 3.8.2, proof of Lemma 3.46), "we have proved that
     `Z ⊕ Y = ℝ^{n'} ⊕ W'`" for `K' ⊕ Y = ℝ^{n'} ⊕ W'`.


Found while proving condition (a) of `IsRegular` for the solution set by re-centring, and
assembling Theorems 3.19, 3.23, 3.24, 3.54, 3.56, 3.57 (`SolutionGermRecentre.lean`,
`GlobalIFTTheorems.lean`, 2026-10-26).

150. **The re-centring argument, and what it repairs in the proof of Theorem 3.27 for solution
     sets** (`Polyfold.recentre_contDiffOn_levels`). The text's step "δ is an sc^∞-germ near every
     `v₀ ∈ V`" (p. 84) fails for an arbitrary set with the tangent germ property (item 82: `δ` need
     not be differentiable at `v₀`). For two graph descriptions of the same set `S` — in the chart
     `χ₁` the graph of `σ₁ : V₁ → Y₁` over `K₁` with `σ₁` of class **`C¹` on all of `V₁`**, and in
     the chart `χ₂` centred at `y = χ₁⁻¹(v₀ + σ₁(v₀))` the graph of `σ₂ : V₂ → Y₂` over `K₂` with
     `σ₂(0) = 0`, `Dσ₂(0) = 0` and **`C^k`-lifts `σ_{2,k} : V_{2,k} → E_{2,k}` at `0`** (Theorem
     3.47 (1)) — the argument goes through, with four modifications of the text's sketch.
     (a) The transition `T = χ₁ ∘ χ₂⁻¹` is only an sc-smooth map between the overlap retracts
     (`MPolyfold.IsChart.compatible`), so `w ↦ T(w + σ₂(w))` is handled as `(T ∘ r₂) ∘ Γ_{2,j}` with
     a retraction `r₂` onto the overlap and the lift `Γ_{2,j} = ι_j + σ_{2,j}` into `E_{2,j}`: by
     Proposition 1.18 it is `C^k` into `E_{1,m}` for `j = m + k + 2`, on a neighbourhood of `0`
     depending on `(m, k)`. (b) The linearization `Dβ(0)` of `β = π₁ ∘ T ∘ (1 + σ₂)` is **injective**
     because `T ∘ Γ₂ = Γ₁ ∘ β` can be differentiated at `0` — `σ₁` is `C¹` at `v₀` on level `0`,
     `Γ₂` into level `1` through the lift — giving `D(T ∘ r₂)(0) n = Dβ(0)n + Dσ₁(v₀)Dβ(0)n`; if
     `Dβ(0)n = 0` the chain rule for `(T⁻¹ ∘ r₁) ∘ (T ∘ r₂) = r₂` on level `1` gives `Dr₂(0)n = 0`,
     while `Dr₂(0)n = n` since `K₂` is the tangent space of the graph of `σ₂` at `0`, which lies in
     the retract (`scDeriv_apply_toBase_deriv_eq_of_fixed`, item 102). (c) **Surjectivity of
     `Dβ(0)` does not follow from the symmetric argument**, which would differentiate
     `T⁻¹ ∘ Γ₁ = Γ₂ ∘ α` at `v₀` and needs `σ₁` of class `C¹` **into level `1`** at `v₀` (`T⁻¹` is
     differentiable from level `1` to level `0` only), available only near `0`. It is obtained from
     the dimension count `dim K₁ ≤ dim K₂`: `β` is a `C¹`-map of a `dim K₂`-dimensional space whose
     image, `β(A) = {v ∈ Bs | α(v) ∈ A}` for the continuous inverse `α = π₂ ∘ T⁻¹ ∘ Γ₁`, is a
     nonempty relatively open subset of the cone `K₁ ∩ C₁`, hence has interior in `K₁`; Sard's
     lemma in fixed dimension (`finrank_le_of_interior_image_nonempty`, from Mathlib's
     `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` after composing with a linear surjection
     `K₁ → K₂`) gives `dim K₁ ≤ dim K₂`. Together with (b), `Dβ(0)` is an isomorphism and
     `dim K₁ = dim K₂`. (d) The regularity of `β⁻¹ = α` is **not** the quadrant inverse function
     theorem (Theorem 3.72 needs `d_C(x) = d_C(β(x))`, the intrinsic degeneracy index of `S`, not
     available): it is Lemma 3.77 / Proposition 3.73 with the hypotheses their proofs use
     (`InvDataW`: convexity, `‖Dβ̂ − 1‖ ≤ ½` for `β̂ = Dβ(0)⁻¹ ∘ β` on a small convex neighbourhood,
     and unique differentiability of the image, which holds because `β` is a homeomorphism between
     relatively open subsets of convex cones; `exists_contDiffOn_inverse`). Then
     `σ₁ = ((1 − π₁) ∘ T ∘ (1 + σ₂)) ∘ α` is `C^k` into `E_{1,m}` near `v₀`. The neighbourhood of
     `v₀` depends on `(m, k)`, which is harmless: sc-smoothness in the set sense on `V''` is the
     `C^∞`-property of each level map, a local property (`contDiffOn_of_locally_contDiffOn`,
     `IsScSmooth.of_contDiffOn_levels`).
151. **Condition (a) of `IsRegular` for the solution set, and the hypothesis it needs**
     (`MPolyfold.TangentGermChart.exists_isRegular_of_locally`, `Polyfold.theorem_3_54_two`). If
     the data `D` of Definition 3.25 (2) for `M` at `x` satisfy `π(O) ⊆ C` (condition (b), which
     the solution set has by the choice of the complement, items 130–133) and **every point of `M`
     near `x` has data of Definition 3.25 (2) of some dimension**, then `D` can be shrunk — the
     chart restricted to an open `s ∋ x`, `V` replaced by a relatively open `V' ∋ 0` with
     `ϕ(M ∩ s) = Γ(V')`, same `N`, `Y`, `δ` (`TangentGermChart.shrink`, `exists_shrinkData`) — to
     regular data (`IsRegular`): the re-centring lemma at every `v₀ ∈ V'` with the data at
     `y = ϕ⁻¹(v₀ + δ(v₀))`, whose `C^k`-lifts come from Definition 3.25 (ii) in the reading
     `IsScInftyGermAt` (`TangentGermChart.exists_lift`). The `C¹`-property of `δ` on `V'` comes from
     Definition 3.25 (ii) at `0` (`IsScInftyGermAt.contDiffOn_one`), so `V'` lies in that
     neighbourhood. For the solution set the hypothesis "data at the nearby points" is Theorem
     3.54 (1): every zero near `x₀` in good position (then `theorem_3_54_tangentGermChart_proj` at
     those zeros gives the data). So **Theorem 3.54 (2) is proved from Theorem 3.54 (1)**, exactly
     as the text's "proceeding as above we can construct a map `σ`" intends, and the regularity
     condition (a) of Theorem 3.27, which item 82 showed to be an added hypothesis for general
     sets, is a theorem for solution sets. Used silently by the text and proved here: an open
     subset of a tame retract is a tame retract (`IsTameRetract.inter_isOpen`,
     `ScRetraction.restrict_isTame`: Proposition 2.10 (1) with the degeneracy index condition
     inherited and the derivative of the restricted retraction unchanged, `scDeriv_eq_of_eqOn_relOpen`),
     needed because the chart `ψ ∘ ϕ` has to be restricted to the neighbourhood `V` of Theorem 3.54
     so that the solution set in the chart domain is `S ∩ V` (`MChart.isTameRetract_image`,
     `theorem_3_54_tangentGermChart_solutionSet`).
152. **The dimension of the solution set is locally constant but Theorem 3.27 fixes it.** A
     by-product of item 150 (c): any two data of Definition 3.25 (2) for the same set, one centred
     at a point of the other's domain, have the same dimension (`dim K₁ = dim K₂`), so the
     dimension `d(x) = dim ker f'(x)` of the solution set is locally constant along `S`
     (`theorem_3_54_two`: every datum of Definition 3.25 (2) at a point of the chart domain has
     dimension `d`). The text's Theorem 3.57 says "a manifold with boundary with corners" without
     a dimension; `theorem_3_27` is stated for a fixed `n` (item 84). Formalized:
     `MPolyfold.IsManifoldWithCornersLoc` (an equivalent atlas of finite-dimensional corner charts,
     no fixed dimension) and `theorem_3_27_loc` (Theorem 3.27 for data of any dimension at each
     point; the same proof: `theorem_3_27_isSubMPolyfold` is pointwise and the atlas of the charts
     `π ∘ ϕ` does not use `n`), used in `theorem_3_57`; and the decomposition `S = ⋃ₙ Sₙ`
     (`solutionSetDim`, `theorem_3_57_dim`): `Sₙ = {x ∈ S | S has data of dimension n at x}` is
     open and closed in `S` (`Sₙ = S ∩ Uₙ` for the union `Uₙ` of the regular chart domains of
     dimension `n`, `solutionSetDimOpen`), the `Sₙ` are pairwise disjoint, and each nonempty `Sₙ`
     is a sub-M-polyfold whose induced structure is tame and that of an `n`-dimensional manifold
     with boundary with corners (`theorem_3_27` for `M = Sₙ`, the regular data for `S` at `x ∈ Sₙ`
     being data for `Sₙ` since `Sₙ ∩ s = S ∩ s` on the chart domain `s`).
153. **Theorem 3.54 as formalized** (`Polyfold.theorem_3_54`, `theorem_3_54_two`,
     `theorem_3_54_tangentGermChart_solutionSet`). (1) "At every point `y ∈ S` the germ `(f, y)` is
     in good position": `theorem_3_54_one`, under the **added hypothesis** `IsGoodPositionGermFilled`
     (condition (3) of Definition 3.4 at the zeros near `0` for the filler at `x₀`; items 100–107):
     the kernel part needs no added hypothesis (`theorem_3_54_nearby_kernel`), the surjectivity of
     `f'(y)` is open without it. (2) "`S` is a sub-M-polyfold and the induced structure is that of
     a manifold with boundary with corners": `theorem_3_54_two` proves the regular tangent germ
     data (`TangentGermChart` with `IsRegular`) of the global solution set at `x₀`, on a chart whose
     source lies in any prescribed neighbourhood in which the zeros are in good position, with the
     local constancy of the dimension; Theorem 3.27 then applies to the local solution set
     (`theorem_3_23_of_nearby`). Hypothesis of `theorem_3_54_two`: `f` a section of a strong bundle
     with tame base retractions, `f(x₀) = 0`, `(f, x₀)` in good position, **and every zero in an
     open `Vx₀ ∋ x₀` in good position** — the conclusion of (1); `theorem_3_54` combines (1) and (2)
     under `IsGoodPositionGermFilled`. (3), the graph description `ψ ∘ ϕ(S ∩ V) = {v + σ(v)}`:
     `theorem_3_54_graph_proj` (items 85–86, 130–133). (4), the kernel and good position at the
     nearby zeros in the chart at `x₀`: `theorem_3_54_nearby_kernel` (items 100–104). The text's
     `V` is the `Vx` of (3), further shrunk in (2) to the chart source `s` of item 151.
154. **Theorem 3.19 as formalized** (`Polyfold.theorem_3_19`, `theorem_3_19_linearization`).
     Hypotheses: `d_X ≡ 0` (`IsWithoutBoundary`), `f` an sc-Fredholm section of a strong bundle with
     tame base retractions, `f(x₀) = 0`, and `(f, x₀)` in good position **with the filler condition
     at the nearby zeros** (`IsGoodPositionGermFilled`, the added hypothesis of item 153 (1)).
     Conclusions: `f'(x₀)` is a Fredholm operator in the chart (`theorem_3_19_linearization` =
     `proposition_3_52`; its index is `proposition_3_52_index`); an open `U ∋ x₀` such that every
     zero in `U` is in good position (in particular `f'(y)` is surjective), `S(f, U)` consists of
     smooth points, is a sub-M-polyfold of `X` whose induced structure is that of a `d`-dimensional
     manifold with `d_S ≡ 0` (`IsWithoutBoundary` of `subPolyfold`, Lemma 2.26). Two readings and two
     omissions. (a) The text's hypothesis is "`f'(x₀)` surjective", good position being "an empty
     condition if `d_X(x) = 0`" (Corollary 3.24): in the formalization good position of the kernel
     is stated with respect to the partial quadrant `C` of the chart, and the reduction to
     surjectivity when `d_X ≡ 0` (a chart of a boundaryless M-polyfold may still be modelled in a
     partial quadrant whose boundary the retract avoids; `IsInGoodPosition` with `C = E` is
     automatic for a finite-dimensional `N`, but the chart's `C` need not be `E`) is not formalized;
     the hypothesis is `IsGoodPositionGerm` as in the boundary case (the reduction is formalized
     later, item 173). (b) "Whose dimension agrees with the Fredholm index":
     `d = dim ker D(h + t)(0)` and `ind D(h + t)(0) = dim Pn − dim Q = ind f'(x₀)`
     (`proposition_3_52_index`) for the same conjugation data, but `theorem_3_54_graph_proj` does
     not expose that its `Pn`, `Q` are those of the given conjugation; not formalized here (done
     later, item 170). (c) "`ker f'(y) = T_yS(f, U)`": in the chart at `x₀`,
     `ker D(h + t)(z) = N_v = graph Dσ(v)` is the tangent space of the graph (item 101,
     `theorem_3_54_nearby_kernel`); the identification with `T_yS` as a subspace of `T_yX`
     (Definition 2.38, gap G.13) is not formalized (the chart form is item 172).
155. **Theorem 3.23 and Corollary 3.24 as formalized** (`Polyfold.theorem_3_23_of_nearby`,
     `theorem_3_23`, `corollary_3_24`). Theorem 3.23: an sc-Fredholm section of a strong bundle
     with tame base retractions, a zero `x` with `(f, x)` in good position; conclusion: an open
     `U ∋ x` such that `S(f, U) = {y ∈ U | f(y) = 0}` consists of smooth points
     (`IsScFredholmSection.mem_smoothSet_of_isZeroAt`, regularizing), is a sub-M-polyfold of `X`
     (`IsSubMPolyfold`), and the induced structure of Proposition 2.21 (`subPolyfold`) is tame and
     equivalent to that of a `d`-dimensional manifold with boundary with corners
     (`IsManifoldWithCorners d`), `d = dim ker f'(x)`. Proved in two forms: `theorem_3_23_of_nearby`
     with the explicit hypothesis "every zero in an open `Vx₀ ∋ x` is in good position" (then
     `U ⊆ Vx₀`), and `theorem_3_23` under `IsGoodPositionGermFilled` (item 153 (1)). The proof is
     item 151 at every `y ∈ S(f, U)`: the regular data at `y` for the global solution set
     (`theorem_3_54_two` at `y`, inside `U`) have dimension `d` by the local constancy at `x`, and
     are data for `S(f, U)` after restriction (`TangentGermChart.shrink` with `M' = S(f, U)`); then
     `theorem_3_27`. "A uniquely determined structure as a smooth manifold with boundary with
     corners ... the same as the one defined in Proposition 2.21": the structure is the induced one
     of Proposition 2.21, with the equivalent atlas of the charts `π ∘ ϕ`; uniqueness is not
     stated separately (it is the equivalence of atlases). Corollary 3.24 is Theorem 3.57 (same
     statement, `corollary_3_24 := theorem_3_57`): with good position at **every** zero, which is
     the text's hypothesis, nothing is added.
156. **Theorems 3.56 and 3.57 as formalized, with the text's hypotheses** (`Polyfold.theorem_3_57`,
     `theorem_3_56`). Hypotheses of `theorem_3_57`: `f` an sc-Fredholm section
     (`IsScFredholmSection`) of a strong bundle whose charts have tame base retractions (`htame`,
     "tame strong bundle", item 86), `(f, x)` in good position (`IsGoodPositionGerm`, Definition
     3.53 in the chart form) at every zero `x`, and `S = solutionSet P f` nonempty (Theorem 3.27
     needs a point for the junk value of the chart inverses; for `S = ∅` the statement is empty).
     Conclusion: `S` is a sub-M-polyfold of `X`, its induced structure is tame and that of a
     manifold with boundary with corners of locally constant dimension (`IsManifoldWithCornersLoc`,
     item 152), and at every `x ∈ S` the data of Definition 3.25 (2) are regular with locally
     constant dimension. `theorem_3_56` (`d_X ≡ 0`): the same with `IsWithoutBoundary` for the
     induced structure (Lemma 2.26); its hypothesis "`f'(x)` surjective at every zero" is read as
     `IsGoodPositionGerm` (item 154 (a)). **No hypothesis is added** in either: the global
     hypothesis "good position at every zero" supplies at every `x₀` the nearby good position that
     item 151 needs, so the gap of Theorem 3.54 (1) (items 100–107) does not enter the global
     theorems. The fixed-dimension form is `theorem_3_57_dim` (item 152).
157. **Does the sc-Fredholm implicit function theorem hold with the text's hypotheses?** The
     answer from what is proved (this block and items 82–87, 91–96, 100–107, 130–133):
     * **The global theorems hold with the text's hypotheses.** Theorem 3.57 / Corollary 3.24
       (`theorem_3_57`, `corollary_3_24`) and Theorem 3.56 (`theorem_3_56`): an sc-Fredholm
       section of a tame strong bundle with `(f, x)` in good position at every zero has a solution
       set which is a sub-M-polyfold with tame induced structure equivalent to a manifold with
       boundary with corners (of locally constant dimension; of dimension `n` on each part `Sₙ`,
       `theorem_3_57_dim`). Two steps of the text's proof had to be replaced: the regularity of
       the solution germ away from the centre (the proof of Theorem 3.27 for general sets is wrong
       there, item 82; for solution sets it is repaired by re-centring with the `C¹`-property of
       `σ` on `V'` and the lifts at the nearby zero, item 150), and the relative openness of `Σ`
       (false for an arbitrary good complement, item 83; repaired by the choice of the complement,
       items 130–133).
     * **The local Theorem 3.54 (2), and Theorems 3.19, 3.23, hold under one added hypothesis**:
       that the zeros near `x₀` are in good position, which is Theorem 3.54 (1). Theorem 3.54 (1)
       is proved (`theorem_3_54_one`) under condition (3) of Definition 3.4 (the filler is "normal"
       in the directions transverse to the retract) at the zeros of the filler near `0`, not only
       at `0` (`IsGoodPositionGermFilled`), which is equivalent to the local constancy of the
       Fredholm index `ind(f, y) = ind(f, x₀)` along the solution set (item 100), i.e. to
       Proposition 6.2. The kernel part of (1) (`ker f'(y)` in good position) holds with the text's
       hypotheses (`theorem_3_54_nearby_kernel`); the surjectivity of `f'(y)` does not follow from
       Corollary 3.41 and Lemma 3.55 as the text says, and is **open** with Definition 3.4 as
       stated (items 100, 105–106: the perturbation argument of Proposition 6.2 gives
       `ρ(z₀)Λ₀ ⊆ range Tf̃(z₀)` on a neighbourhood depending on the finite-dimensional `Λ₀`).
     * **The gap is also in the book's arXiv version** (arXiv 1707.08941, *Polyfold and Fredholm
       Theory*, Theorem 3.13 = Theorem 3.54): its proof says "Property (4) follows from Corollary
       3.5 and from the following lemma" (Lemma 3.10 = Lemma 3.55), line 4976 of the extracted text
       `book.txt`, with Definition 3.13 (the filler, (3) imposed at `0` only) unchanged; the same
       step, with the same hypotheses, as in the 2014 preprint.
     * *Outcome of the parallel mathematical investigation (whether the surjectivity of `f'(y)` at
       the nearby zeros can be proved with Definition 3.4 as stated, or needs the added condition):*
       **the surjectivity holds with Definition 3.4 as stated** (items 180–189, 2026-10-26).
       `theorem_3_54_one'` proves Theorem 3.54 (1) with the text's hypotheses, and
       `theorem_3_54'`, `theorem_3_23'`, `theorem_3_19'` the local theorems; the added condition
       `IsGoodPositionGermFilled` is no longer needed (the old theorems are kept next to the new
       ones). The proof is not the text's: for a fixed zero `y` and a fixed smooth `λ`, the
       perturbed equation `g(u) + μ ρ(r(u)) λ = 0` is solved along a one-sided `C¹`-curve through
       `z₀ = ϕ(y)` by an implicit function theorem **at `z₀`** (Theorem 3.30 for a `λ`-extended
       contraction germ applied at the centre `x₀`, with parameter regions independent of `λ`,
       and the one-sided finite-dimensional implicit function theorem at `θ(z₀)`); the curve lies
       in `O` by condition (2) of Definition 3.4, so its velocity is tangent to `O` and
       `Tf̃(z₀) ξ = −ρ(z₀) λ`, which gives `ρ(z₀) F_∞ ⊆ range Tf̃(z₀)` and, with the closed range of
       Proposition 3.52 at `y`, the surjectivity. **The text's argument is incomplete but its
       statement is true.** In particular the Fredholm index is locally constant along the
       solution set (item 188), which repairs the same step of the proof of Proposition 6.2.
158. **Proposition 3.73 / Lemma 3.77 with the hypotheses their proofs use** (`Polyfold.InvDataW`,
     `InvDataW.contDiffOn_inv`). The proofs of Lemma 3.74 (the bi-Lipschitz estimate), Lemma 3.77
     (`Dg = [Df ∘ g]⁻¹`) and the bootstrapping of Proposition 3.73 use of the partial quadrant only:
     `U` convex, `‖Df − 1‖ ≤ ½` on `U`, unique differentiability of `U`, and unique
     differentiability of the image `f(U)`; the hypothesis `d_C(x) = d_C(f(x))` enters only through
     the relative openness of `f(U)` (Lemma 3.74, `InvData.image_relOpen`). In the re-centring the
     relative openness of `β(U)` is known for another reason (`β` is a homeomorphism onto a
     relatively open subset of the cone), while `d_C(x) = d_C(β(x))` would be the intrinsic
     degeneracy index of the solution set (Lemma 3.70 transported, item 84), not available. The
     restated `InvDataW` isolates this; `InvData` (`QuadrantInverse.lean`) is unchanged.
159. **Sard's lemma in fixed dimension replaces the symmetric differentiation**
     (`Polyfold.finrank_le_of_interior_image_nonempty`, item 150 (c)). The text's proof of Theorem
     3.27 obtains the isomorphism `N' → N` by linearizing `π ∘ ϕ ∘ ψ⁻¹ ∘ (1 + τ)`; implicitly it
     would also linearize the inverse `π' ∘ ψ ∘ ϕ⁻¹ ∘ (1 + δ)` at `v₀`, which is where `δ` must be
     differentiable into level `1` at `v₀` — true near the centre (Theorem 3.47 (1)), not known at
     `v₀`. The dimension count through the measure of the image (a `C¹`-image of a
     lower-dimensional set has measure zero; a nonempty relatively open subset of a convex cone with
     interior has positive measure) is the replacement, and gives at the same time the local
     constancy of the dimension (item 152). It uses the finite dimensionality of both kernels, the
     convexity of the cones `N ∩ C` (Proposition 3.22) and the interior point of `N ∩ C` from good
     position (Definition 3.21).

Found while formalizing Theorem 3.18 (parametrized perturbations; book 2017: Theorem 3.3, p. 67),
the verification the text calls "readily verified" and the linearization used after Theorem 3.19
(`ParamPerturbation.lean`, 2026-10-26).

160. **Theorem 3.18 as formalized, with no added hypothesis** (`Polyfold.theorem_3_18`). For a
     strong bundle `B : P : Y → X`, an sc-Fredholm section `f` and sc⁺-sections `s₁, …, sₙ`
     (`Γ⁺(P)`, Definition 2.52, global sections), `paramSection f s : (r, x) ↦ f(x) + Σ rᵢ sᵢ(x)`
     (computed in the fibre `P⁻¹(x)` and read in the fibre of `π*Y` over `(r, x)`) is an
     sc-Fredholm section of `B.pullback`, the pull-back `π*P → ℝⁿ × X` along `π(r, x) = x` with
     the natural structure of Proposition 2.54 (all pulled-back charts, `pullbackAtlas`). The
     proof is the text's: `F = f̃ + s̃` fibrewise (`paramSection_eq_sectionAdd`), `f̃` sc-Fredholm
     (item 161), `s̃` sc⁺ (item 162), Theorem 3.15. **Tameness is not used**, as for Theorem 3.15
     (the book drops "tame" in both); since Definition 3.14 is stated for tame bundles, the text
     needs `π*P` tame when `P` is, which holds: `ℝⁿ × X` is tame when `X` is (`prod_rn_isTame`,
     exposition Lemma 4.D with `ℝⁿ` tame). The paracompactness of `ℝⁿ × X` and of `π*Y`
     (Definitions 2.13, 2.51) are instance arguments, proved by `MPolyfold.paracompactSpace_prod`
     and `paracompactSpace_pullbackSpace` (Theorem 2.16): not added hypotheses
     (`Polyfold.theorem_3_18'` states the theorem without them).
161. **"`f̃(r, x) = ((r, x), f(x))` is a sc-Fredholm section as is readily verified"**
     (`StrongBundle.IsScFredholmSection.param`, `StrongBundle.IsScFredholmGerm.param`). The
     verification needs objects the text does not construct: (a) `ℝⁿ` as an M-polyfold
     (`rnPolyfold`, constant sc-structure) and its translation charts `r ↦ r − r₀`
     (`rnChart`): Definition 3.11 asks for a chart centred at the smooth point `(r₀, x)`, and the
     product `id × φ` is centred only when `r₀ = 0`; (b) the product chart pulled back to `π*Y`
     with the retraction `1 × r` of `ℝⁿ × U` (`PullbackChartData.ofProd`), a chart of `π*P`
     because charts pulled back from charts compatible with the atlas of `P` are compatible with
     the pulled-back atlas (`PullbackChartData.isChart_toChart`); (c) the filler conditions
     (1)–(3) for `(a, u) ↦ g(u)` (`ofProd_isFillerOf`): (1), (2) are those of `g` because
     `ρ'(r'(a, u)) = ρ(r(u))` (it uses `φ(φ⁻¹(r(u))) = r(u)` on `O`), and (3) because
     `ker D(1 × r)(0) = 0 × ker Dr(0)`, `ρ'(0) = ρ(0)` (from `r(0) = 0`) and
     `[1 − ρ'(r'(a, u))]g(u)` does not depend on `a`; (d) the **`ℝⁿ`-extension of the basic germ**
     (item 163). The sc⁺-section to subtract is `(a, u) ↦ t₀(u)`. Regularity: `(r, x)` is on level
     `m` iff `x` is (`prod_rn_mem_levelSet_iff`), and `f̃` is regularizing because `f` is, tested in
     the pulled-back charts (`regularizing_paramLift`).
162. **"`s̃(r, x) = ((r, x), Σ rᵢ sᵢ(x))` is a sc⁺-section of the pull back bundle"** (no proof in the
     text; `StrongBundle.isScPlusSection_paramComb`). The atlas of `π*P` contains the charts pulled
     back through *every* chart `ψ` of `ℝⁿ × X`, not only product charts, so the principal part
     `w ↦ Σ λᵢ(w) ŝᵢ(g(w))`, `λ(w) = (ψ⁻¹(w))₁`, `g = φ ∘ π ∘ ψ⁻¹`, must be shown sc-smooth into `F¹`
     for an arbitrary `ψ`: `λ` is the projection `ℝⁿ × X → ℝⁿ` read in `ψ` (`isScSmoothMap_fst`,
     `isScSmooth_chart_coord`), and the product with an sc-smooth scalar function needs **the
     product rule for a scalar factor**, which Chapter 1 does not state: scalar multiplication
     `ℝ ⊕ F → F` is sc-smooth, being continuous bilinear on every level (`isScSmooth_smul`, by
     Proposition 1.19; `IsScSmooth.smul`), together with finite sums (`IsScSmooth.finsetSum`).
163. **The `ℝⁿ`-extension of a basic germ is a basic germ, and the product with the identity is a
     strong bundle isomorphism** (`IsBasicGerm.paramExtend`, `IsStrongBundleIso.paramMap`,
     `IsConjugateToBasicGerm.paramExtend`, for any finite-dimensional `Λ`). If `k` is conjugated to
     the basic germ `h(a, w) = (h₁(a, w), w − B(a, w))` on `C̃ ⊕ W` by `Ψ`, then `(λ, u) ↦ k(u)` is
     conjugated to `h'((a, λ), w) = h(a, w)` on `(C̃ × Λ) ⊕ W` by
     `Ψ''((λ, u), k) = (((ψ(u))₁, λ), (ψ(u))₂), Γ(u, k))`: the product `1_Λ × Ψ` (a strong bundle map
     on `[0]` and `[1]` by the reassociation sc-operators and the product rule for sc-smooth maps)
     followed by a linear reassociation (`ScOperator.isStrongBundleIso_prodMap`), composed by
     `IsStrongBundleIso.comp`. The new parameter space is `Pn × Λ` with the partial quadrant
     `C̃ × Λ` (`IsPartialQuadrant.const_prod_univ`; the order of the factors is immaterial). The
     new germ of neighbourhoods `U''_m = {((a, λ), w) | (a, w) ∈ U_m}` is unbounded in `λ`, which
     Definition 3.1 allows (only relatively open neighbourhoods of `0`, nested); the contraction
     estimate of Definition 3.28 holds with the same radius since `B'((a, λ), w) = B(a, w)` and
     `|a| ≤ |(a, λ)|`. The text's `Ψ'(r, u, k) = (r − r₀, Ψ(u, k))` has the translation inside;
     here it sits in the chart (item 161 (a)), so `Ψ''` has none.
164. **The text's sketch of the germ of `F` is what Theorem 3.15 produces.** The filled version
     `(r, u) ↦ g(u) + Σ rᵢ s̃ᵢ(u)` (`s̃ᵢ = ŝᵢ ∘ r`, Lemma 3.16), the sc⁺-section
     `t₀(u) + Σ rᵢ s̃ᵢ(u)` and the conjugation of `g − t₀` are the germ data of `f̃` (item 161)
     combined with `s̃` by `StrongBundle.IsScFredholmGerm.sectionAdd`, whose principal part in the
     product chart is `(a, u) ↦ Σ (a + r₀)ᵢ ŝᵢ(u)` (`ofProd_principal_paramComb`); the principal
     part of `F` is `(a, u) ↦ f̂(u) + Σ (a + r₀)ᵢ ŝᵢ(u)` (`ofProd_principal_paramSection`), the
     text's `(r, u) ↦ f̂(u) + Σ rᵢ ŝᵢ(u)` with `r = a + r₀`.
165. **The linearization of `F`** (after Theorem 3.19: "the linearization of `f̃` at `(0, x₀)` is
     `(h, u) ↦ f'(x₀)u + Σ hᵢ eᵢ`"; `scDeriv_paramSection`, `linAt_paramSection`,
     `linAt_paramSection_zero`). In the product chart at `(r₀, x)`,
     `D(F̂ ∘ (1 × r))(0)(δa, δu) = D(Ĝ ∘ r)(0) δu + Σ δaᵢ ŝᵢ(0)` with `Ĝ = f̂ + Σ r₀ᵢ ŝᵢ` (the
     product rule at `a = 0`; `T₀(ℝⁿ × O) ⊆ ℝⁿ × T₀O`, `ofProd_mem_tangent`). At `r₀ = 0` this is the
     text's formula in the chart form `linAt` (`Lin_F(0)(δa, δu) = Lin_f(0)δu + Σ δaᵢ ŝᵢ(0)`); at a
     general `(r₀, x)` the first term is the linearization of `f + Σ r₀ᵢ sᵢ`, not `f'(x)`. The
     formula is the derivative at the centre of the chart and does not use `F(r₀, x) = 0`; its
     chart independence at zeros is `StrongBundle.linAt_chart_independence` (item 111).
166. Typos and notation in the passage (pp. 73–75): "a parametrized version of Proposition 3.15"
     for Theorem 3.15; after Theorem 3.19, "Taking the sc¹-sections `sᵢ` satisfying `sᵢ(x₀) = eᵢ`"
     — Theorem 3.18 needs sc⁺-sections, which the preceding paragraph provides — and `ℝᵏ ⊕ X` for
     `ℝᵏ × X`; the symbol `f̃` is used for `((r, x), f(x))` before Theorem 3.18 and for
     `f(x) + Σ rᵢ sᵢ(x)` after Theorem 3.19.
167. **Pull-backs of sections** (`StrongBundle.IsScSmoothSection.pullback`): the pull-back
     `z ↦ (z, σ(π(z)))` of an sc-smooth section along an sc-smooth `π : Z → X` is an sc-smooth
     section of `π*P` (its representative in a pulled-back chart is `w ↦ (w, σ̂(g(w)))`). The
     text uses this for `f̃` without comment; Proposition 2.54 is stated as an existence
     (`proposition_2_54`) and is made a structure here (`StrongBundle.pullback`).

Found while proving Theorem 3.54 (1) with the text's hypotheses (the surjectivity of `f'(y)` at
the nearby zeros; `GlobalIFTNearbyOntoLemmas.lean`, `GlobalIFTNearbyOntoGerm.lean`,
`GlobalIFTNearbyOntoCurve.lean`, `GlobalIFTNearbyOntoXi.lean`, `GlobalIFTNearbyOnto.lean`,
2026-10-26), after the mathematical investigation of the gap of item 100.

180. **Theorem 3.54 (1) holds with the text's hypotheses** (`Polyfold.theorem_3_54_one'`): for an
     sc-Fredholm section `f` of a strong bundle whose charts have tame base retractions, with
     `f(x₀) = 0` and `(f, x₀)` in good position (Definition 3.53), there is an open `Vx ∋ x₀` such
     that `(f, y)` is in good position — `f'(y)` surjective and `ker f'(y)` in good position to
     `C_yX` — at every zero `y ∈ Vx`. The added hypothesis `IsGoodPositionGermFilled` of
     `theorem_3_54_one` (condition (3) of Definition 3.4 at the nearby zeros, item 100) is not
     needed; the theorems `theorem_3_54'`, `theorem_3_23'`, `theorem_3_19'` restate Theorems 3.54,
     3.23 and 3.19 with the text's hypotheses (the old statements are kept). The case `d = 0` is
     separate: the zero set near `x₀` is the graph over `V' ⊆ ker D(h + t)(0) = 0`, so the only
     zero in `Vx` is `x₀` itself, where good position is the hypothesis. Where the hypotheses enter:
     tameness and good position at `x₀` through Corollary 3.41, Lemma 3.55 (the data of
     `theorem_3_54_chart_kernel`) and the interior direction of the partial quadrant at boundary
     zeros (item 185); the sc-Fredholm germ at `y` only for the closed range of `f'(y)`
     (Proposition 3.52 at `y`, inside `isGoodPositionGerm_of_chart_dense`, item 117).
181. **The argument, and why it has no uniformity problem** (`theorem_3_54_chart_onto`, in the
     chart `c` at `x₀` with the filler `g`). Fix a zero `z₀ = ϕ(y)` of `g` near `0` and a smooth
     `λ ∈ F_∞`. One solves `g(u) + μ ρ(r(u)) λ = 0` along a one-sided curve `u : [0, μ₀) → U`,
     `u(0) = z₀`, right differentiable at `0` into `E₁` with velocity `ξ`. By condition (2) of
     Definition 3.4 the curve lies in `O` (`StrongRetr.mem_O_of_perturbed_zero`: `ρ(r(u))² = ρ(r(u))`
     gives `ρ(r(u)) g(u) = g(u)`), so differentiating `r(u(μ)) = u(μ)` gives `Dr(z₀) ξ = ξ`, i.e.
     `ξ ∈ T_{z₀}O`, and differentiating `g(u(μ)) = −μ ρ(r(u(μ))) λ` (the right derivative of
     `μ ↦ μ k(μ)` is `k(0)` for `k` continuous, `hasDerivWithinAt_smul_right_of_continuousWithinAt`)
     gives `Dg(z₀) ξ = −ρ(z₀) λ`. Hence `ρ(z₀) F_∞ ⊆ Dg(z₀)(T_{z₀}O) = range Tf̃(z₀)` (item 111),
     which is what `isGoodPositionGerm_of_chart_dense` needs. The curve is obtained from an implicit
     function theorem **at the nearby zero**, not at `x₀`: in the normal form of Theorem 3.38
     (`G = Θ_*(g)` with `G¹ = (G₁, w − B(a, w))` basic on the index-raised structure, the
     `ShiftedBasicData` of `StabilityData.toShiftedBasicData`), the `W`-equation
     `w = B(a, w) − μ P ê_λ(a, w)` is solved by Theorem 3.30 for the `λ`-extended contraction germ
     (item 182), whose regions in `a` are those of `B` and **do not depend on `λ`** — only the
     `μ`-intervals do, and an arbitrarily short interval suffices — and the finite-dimensional
     equation `H_λ(μ, a) = 0` is solved at `(0, a₀)` by the one-sided implicit function theorem
     (item 185). The set of zeros to which this applies is cut out by conditions on `z₀` involving
     `G`, `g`, `r`, `ρ`, `Ψ` alone (item 186). This is what the perturbation argument of
     Proposition 6.2 (items 105–106) could not provide: there Theorem 3.47 was applied at `x₀` to
     the `Λ₀`-extended problem, and the resulting neighbourhood depends on `Λ₀`.
182. **The `λ`-extended contraction germ** (`ShiftedBasicData.perturbContraction`, Lemma 3 of the
     argument). `B_μ(a, w) = B(a, w) − μ P e(a, w)` on `O((ℝ × C̃) ⊕ W¹, 0)` is given directly in
     the working form `ContractionGerm` with the regions `(−μ_m, μ_m) × {‖a‖ < ν_m}`,
     `{‖w‖_{m+1} < ρ_m}`, `{‖w‖_{m+1} ≤ ρ_m/2}`: the `1/4`-contraction regions of `B`
     (`ShiftedBasicData.Radii`, from Definition 3.28 with `ε = 1/4` and `‖B(a, 0)‖ ≤ ρ_m/8` by the
     continuity of `B` at `0`; they exist below any prescribed radii, `exists_radii`), and
     `μ_m c_m ≤ 1/4`, `μ_m c_m ≤ ρ_m/8` for the bounds `c_m` of `P e` (item 183), so that `B_μ` is a
     `1/2`-contraction mapping the closed balls into themselves. The construction
     `IsSc0ContractionGerm.toContractionGerm` is **not** used for `B_μ`: its radii in `a` would
     depend on `λ`, and the finite-dimensional step needs `a₀` in the level-`3` region for every
     `λ`. Theorem 3.30 (`perturbContraction_isSc1GermWith`) then gives `δ_μ` sc¹ on the re-indexed
     germ, hence `C¹` into `W₂` on `(−μ_3, μ_3) × ({‖a‖ < ν_3} ∩ C̃)` (Proposition 1.16 on level
     `1`), and `δ_μ(0, a)` is the fixed point of `B(a, ·)` by uniqueness
     (`perturbContraction_sol_zero`), so the nearby zero `(a₀, w₀)` lies on the solution germ. The
     sc-smoothness of `B_μ` is the germ calculus with the scalar multiplication of Proposition
     1.19 (`isScSmooth_smul`, `IsScSmooth.smul` of `ParamPerturbation.lean`).
183. **Lemma 2, the bounds of `ê_λ`** (`xiMap`, `exists_xi_bounds`, `exists_xi_radii_bounds`). The
     perturbation `ê_λ(u') = Γ_Θ(θ⁻¹u') ρ(r(θ⁻¹u')) λ` is the restriction `κ = λ₁` of the joint
     map `Ξ(y, κ) = fiber(Ψ[1](ψ⁻¹(glue y), (R[1](r(ψ⁻¹(glue y)), κ))_F))_{F'}` on
     `ψ(U) ⊕ F¹`, which is sc-smooth into the index-raised target (a composition of the strong
     bundle maps `R[1]`, `Ψ[1]` of Definition 2.47 with sc-smooth maps and the linear `glue`,
     `fiber` of Theorem 3.38) and linear in `κ`. By Proposition 1.18, `Ξ_m` is `C¹` from level
     `m+1` to level `m+1` — from shifted level `m` to shifted level `m`; this is where the index
     raise of Theorem 3.38 is used — so on a fixed ball `{‖a‖, ‖w‖_{m+1}, ‖κ‖_{m+2} < δ_m}` it is
     bounded by `1` and `M_m`-Lipschitz in `w` (continuity of `Ξ_m` and of its derivative at `0`,
     mean value inequality). The note's argument "`D_{u'}Ξ(u', λ)` is linear in `λ`" is replaced by
     the **scaling** `Ξ_m(y, κ) = (2|κ|/δ_m) Ξ_m(y, (δ_m/2|κ|) κ)`, which needs only the linearity
     of `Ξ` itself: `c_m(λ) = (2|λ|_{m+2}/δ_m)(M_m + 1)`. The radii `δ_m` depend on `Ξ` only, and
     the regions of item 182 are taken with `ν_m, ρ_m ≤ δ_m`.
184. **Lemma 4 reorganised: the dimension count replaces the block elimination.** The note
     identifies `D_aH(a₀)` as onto by eliminating the `W`-block with `(1 − D₂B(z))⁻¹`, which needs
     `‖D₂B(z)‖ ≤ 1/2` on the level where `DG(z)` is known to be onto — the level-`1` surjectivity
     of `DG(z)`, i.e. Corollary 3.41 on the shifted structure. Formalized instead
     (`ShiftedBasicData.surjective_DH_and_ker_eq`): `G̃(μ, a) = (g + μ ι e)(a, δ_μ(μ, a))` is `C¹`
     on the solution region with vanishing `W`-component (`curveMap_snd`, `curveDeriv_snd`), its
     derivative at `(0, a₀)` is `Dg(z) ∘ (α, ι Dδ(0, a₀)(dμ, α)) + dμ · ι e(z)`
     (`hasFDerivWithinAt_curveMap`, the chain rule with Theorem 3.30), so
     `Dg(z)(α, Lα) = (M₀ α, 0)` with `L = ι D_aδ(0, a₀)` and `M₀ = D_aH(0, a₀)`
     (`Dg'_graph`); hence the graph of `L` over `ker M₀` lies in `ker Dg(z)`, and
     `dim ker M₀ ≤ dim ker Dg(z) = n − N` (Corollary 3.41 on level `0`, transported) gives
     `rank M₀ ≥ N`, i.e. `M₀` onto, and `ker Dg(z) = {(α, Lα) : α ∈ ker M₀}` by dimension. Only the
     level-`0` surjectivity of `DG(z)` is used.
185. **Lemmas 5 and 6** (`exists_inward_of_isInGoodPosition`, `exists_curve_of_inward`,
     `inward_add_smul`). Lemma 5 needs `N ≠ 0` (for `N = 0` good position is an empty condition):
     with `C_z = {ℓ_i ≥ 0, i active}`, a relative interior point `y` of `N ∩ C_z` has `ℓ_i(y) > 0`
     for every active `i` — if `ℓ_i(y) = 0`, then `ℓ_i` vanishes on `N` (`y ± tu ∈ C_z`), then on a
     good complement `P` (scale a nonzero `n₀ ∈ N ∩ C_z` so that `‖p‖ ≤ ε‖n₀‖`; `n₀ ± p ∈ C_z`),
     so `ℓ_i = 0` on `N ⊕ P = E`, absurd — and then `z + t(y + ζ) ∈ C` for small `t ≥ 0`, `ζ`. The
     note's argument through the good complement is the same contradiction. The inward direction
     is formulated as this cone condition rather than as "`v ∈ int C_z`", which transports along
     the linear `split` to the finite-dimensional factor. Lemma 6 is the contraction
     `ζ ↦ ζ − S H(μ, a₀ + μ α₀ + ζ)` on the ball of radius `cμ` in `Z = range S`, `S` a right
     inverse of `D_aH(0, a₀)` (mean value inequality with the continuity of `DH` at `(0, a₀)`;
     `H(μ, a₀ + μ α₀) = o(μ)` from the differentiability of `H` at `(0, a₀)` in the direction
     `(1, α₀)`); the fixed point is `o(μ)`, so `a(μ) = a₀ + μ α₀ + o(μ)`. The tilting
     `α₀ = a₁ + s v₁` of the kernel direction keeps it inward (`inward_add_smul`).
186. **The level bookkeeping** (note §6, item 2) and the conditions on the zero. `δ_μ` is `C¹`
     into `W₂` on `(−μ_3, μ_3) × ({‖a‖ < ν_3} ∩ C̃)`; `g` and `e` are differentiated from level `1`
     to level `0` (so `H` is `C¹` on that region); the curve `u'(μ) = (a(μ), δ_μ(μ, a(μ)))` is right
     differentiable into `E'₂`; `ψ⁻¹` is `C¹` from level `2` to level `1`, so `u = ψ⁻¹ ∘ glue ∘ u'`
     is right differentiable into `E₁`; `g` and `r` are `C¹` from level `1` to level `0`. The
     conditions (3.3) of the note on the zero `z₀`, all satisfied on a neighbourhood `N₄` of `0`
     determined by the data at `x₀`: `z = split(ψ z₀)` has `‖a₀‖ < ν_3` and, by Lemma 3.42,
     `‖w₀‖₁ < ρ_0`; `‖v‖ < ρ₂` for the radius `ρ₂` of Lemma 3.55 (`lemma_3_55_relOpen`, which gives
     the good position of `ker D(h + t)(x₁) = N_v` to `C'_{ψ z₀}` needed for Lemma 5); and
     `ψ z₀ ∈ W'` where `Ψ_*(g) = h + t`. Along the curve, `glue(ι u'(μ)) ∈ W'` and `u(μ) ∈ N₁`
     (condition (2) of the filler) hold for small `μ` by continuity.
187. **Corollary 3.39 is not used.** The note normalizes `g` by Corollary 3.39 applied to `g − t₀`
     and then needs (K2)–(K4) for `G` on the shifted structure. Here the normal form is
     `StabilityData.toShiftedBasicData` (Theorem 3.38 for `h' + t_W`, the data of
     `theorem_3_54_chart_graph`), and the facts at the nearby zero — `D(h + t)(x₁)` onto Fredholm
     of index `n − N`, `N_v = ker D(h + t)(x₁)` in good position — are those of
     `theorem_3_54_chart_kernel` on `E'`, transported through the linear `split₀`/`glue₀`/`fiber₀`
     (`StabilityData.scDerivGerm_pushMap₀_at`: `Dg(y) = Ψ ∘ D(h + t)(ψ⁻¹y) ∘ ψ⁻¹` at every
     `y ∈ ψ(U₁)`; `ker_fiber₀_comp_glue₀`). Since item 184 uses the surjectivity of `DG(z)` on
     level `0` only, nothing on the shifted structure beyond the basic germ `G¹` is needed.
188. **The index is locally constant along the solution set** (note §4.2, Proposition 6.2 along a
     solution set). From items 100 and 180: `coker Tf̃(z₀) = 0` at every zero near `x₀` is
     equivalent to `ind f'(y) = ind f'(x₀)` (`ind Dg(z₀) = d` at all nearby zeros by Corollary 3.41,
     `ind Dg(z₀) = ind A + ind C = dim ker A` with `A = Tf̃(z₀)`, `ind f'(y) = ind A`). In Lean this
     is available piecewise: `f'(y)` in the chart centred at `y` is conjugate to
     `Dg(z₀)|_{T_{z₀}O}` in the chart at `x₀` with the same index (`linAt_chart_independence`), the
     latter is onto (`theorem_3_54_chart_onto` with the closed range) with kernel
     `ker Dg(z₀) = Dψ⁻¹(N_v)` of dimension `d = dim ker D(h + t)(0)` (`theorem_3_54_chart_kernel`),
     so `ind f'(y) = d = ind f'(x₀)`. Not stated as a single theorem here (it would repeat the
     closed-range step of `isGoodPositionGerm_of_chart_dense` with the kernel dimension carried
     along); stated later through the dimension of the solution set
     (`theorem_3_54_index_locally_constant`, item 171). Consequently the dimension-jumping examples (a retract whose tangent dimension jumps
     by `1` with a bundle whose rank jumps by `2`) carry no sc-Fredholm section vanishing there with
     a solution set of positive dimension through the jump (note §4.3, §5).
189. **Conclusion for item 157.** Theorem 3.54 (1), and hence Theorems 3.19 and 3.23 (with 3.54
     (2) through `theorem_3_54_two`), hold **with the text's hypotheses**; the text's argument "(4)
     follows from Corollary 3.41 and Lemma 3.55" is incomplete (item 100: it gives the surjectivity
     of the filled derivative only), but the statement is true, by the implicit function theorem at
     the nearby zero of items 181–186. No hypothesis is added anywhere in `GlobalIFTNearbyOnto*.lean`
     (`theorem_3_54_one'` has exactly the hypotheses of `theorem_3_54_nearby_kernel`:
     `IsScFredholmSection`, `IsGoodPositionGerm f x₀`, `IsZeroAt`, tame base retractions). The
     proof of Proposition 6.2 in the text uses the same step; with Theorem 3.54 (1) it is repaired
     along solution sets (item 188), and in general under the proviso of item 157 (good position of
     the extended germ, the tilting of items 105 (a), 107).

Found while checking the Chapter 3 statements against their docstrings and the text
(`GlobalIFTIndex.lean`, `theorem_3_54_graph_proj_conj` in `GlobalIFT.lean`,
`theorem_3_54_tangentGermChart_proj_conj` in `GlobalIFTCenter.lean`; 2026-10-26).

170. **"The dimension agrees with the Fredholm index" (Theorem 3.19; gap G.30), and
     "`d = dim ker f'(x)`" (proof of Theorem 3.54)** (`Polyfold.theorem_3_54_tangentGermChart_index`,
     `theorem_3_54_two_index`, `theorem_3_23_index`, `theorem_3_19_index`, `theorem_3_57_index`,
     `StrongBundle.IsSurjLinOfIndex`). The dimension of the tangent germ data of the solution set
     at `x₀` was existential in `theorem_3_54_tangentGermChart(_proj)`, `theorem_3_54_two`,
     `theorem_3_23(_of_nearby)`, `theorem_3_19`. It is `d = dim K`, `K = ker D(h + t)(0)`, and
     `D(h + t)(0)` is surjective and Fredholm of index `n − N` (`StabilityData.isFredholm_Dfs`), so
     `d = n − N` for the conjugation `(ℝⁿ, ℝᴺ)` used in the proof of Theorem 3.54; and `n − N` is the
     index of `Tf̃(0) = f'(x₀)` for the **same** conjugation (`proposition_3_52_local_index`, item
     120). The conjugation is obtained by destructuring the existential `IsGoodPositionGerm`, so
     the long proofs of `theorem_3_54_graph_proj` and `theorem_3_54_tangentGermChart_proj` now
     prove `_conj` versions that expose the data of Definition 3.53 in the chart (filled version,
     sc⁺-section, `IsGoodPositionAt`, `ConjugationData dc`) with `dim K = dim dc.Pn − dim dc.Q`; the
     old statements are their corollaries. The index is then carried to every chart around `x₀`
     by `linAt_chart_independence` (`StrongBundle.linAt_index_of_conjugationData`), giving the
     chart-intrinsic statement `IsSurjLinOfIndex f x₀ d`: in every strong bundle chart around `x₀`,
     at the level-`1` point over `ϕ(x₀)`, `Lin(z) : T_zO → K_z` is onto and Fredholm with
     `ind Lin(z) = dim ker Lin(z) = d`. Two technical points: at the centre, `Lin(0)` takes values in
     `ρ(ι 0)F` and `Tf̃(0)` in `ρ(0)F`, which are equal subspaces but different Lean types
     (`exists_rangeS_ρCLM_equiv`); and `dim ker = ind` uses the surjectivity of good position
     (`finrank_ker_eq_fredholmIndex_of_surjective`, moved to `GlobalIFT.lean`). Only the level-`0`
     index is formalized (as in `proposition_3_52`). No hypothesis is added.
171. **The index is locally constant along the solution set** (`Polyfold.theorem_3_54_index_locally_constant`,
     `theorem_3_54_index`, `isSurjLinOfIndex_of_forall_dim`; item 188 recorded this as "not stated as
     a single theorem"). On an open `Vx ∋ x₀`, every zero `y` has `IsSurjLinOfIndex f y d` with the
     same `d`, so `ind f'(y) = ind f'(x₀)` — Proposition 6.2's index stability along the solution
     set. The proof does not repeat the kernel computation sketched in item 188; it combines three
     results: the zeros near `x₀` are in good position (Theorem 3.54 (1), `theorem_3_54_one'`); at
     each of them the tangent germ data have dimension `ind f'(y)` (item 170, applied at `y`); and
     every datum of Definition 3.25 (2) at a point of the chart domain of the regular data at `x₀`
     has the same dimension (`theorem_3_54_two`, from the re-centring and Sard's lemma, items 150,
     152, 159). So "dimension locally constant" and "dimension = index" give "index locally
     constant".
172. **"`ker f'(y) = T_yS(f, U)`" in a chart** (Theorem 3.19 (3), Theorem 3.54 (4);
     `Polyfold.theorem_3_54_ker_eq_tangent`). In the strong bundle chart `c` at `x₀` and the
     conjugating sc-diffeomorphism `ψ` of the proof of Theorem 3.54, at every zero `y` near `x₀`
     with `ψ(ϕ(y)) = v + σ(v)` and the level-`1` point `z` over `ϕ(y)`:
     `Dψ(z)(ker Lin(z)) = N_v = {n + Dσ(v)n | n ∈ K}`, the tangent space at `v` of the graph
     `{w + σ(w)}` which is the solution set in the chart `ψ ∘ ϕ` of its tangent germ data. The proof
     uses items 101–104 (`ker Dg(z) = Dψ⁻¹(ψ z)(ker D(h + t)(ψ z))`, `ker D(h + t)(ψ z) = N_v`,
     `ker Dg(z) ⊆ T_zO`) and `Lin(z) = Dg(z)` on `T_zO` (`linAt_eq_scDeriv`). The intrinsic
     `T_yS ⊆ T_yX` (Definition 2.38) is not formalized (gap G.13); the chart form is the statement.
173. **"Good position = surjectivity when `∂X = ∅`"** (`Polyfold.isInGoodPositionIn_of_subset`,
     `StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero`,
     `StrongBundle.isGoodPositionGerm_of_isLinSurjAt`, `StrongBundle.isGoodPositionGerm_iff_isLinSurjAt`;
     `theorem_3_19_of_surjective`, `theorem_3_56_of_surjective`; item 154 (a)). Definition 3.53 is
     stated in the chart of Definition 3.11 with the chart's partial quadrant `C`, which need not be
     the whole space when `d_X(y) = 0`. In a **tame** chart `d_C(ϕ(y)) = d_X(y)`
     (`degIndex_eq_chartDegIndex_of_isTameRetract`, the strong form of Proposition 2.36), so
     `d_X(y) = 0` means that no half-line coordinate of the presentation vanishes at `ϕ(y)`, the
     partial quadrant `C_{ϕ(y)}` is the whole space, the partial cone `T_zO ∩ C_{ϕ(y)}` is `T_zO`, and
     every subspace of `T_zO` is in good position inside `T_zO` (any algebraic complement, any
     `ε`). Hence for an sc-Fredholm germ at a zero with `d_X(y) = 0` good position is the
     surjectivity of `f'(y)` (`StrongBundle.IsLinSurjAt`: `Lin(z)` maps onto `K_z` in some chart, hence
     in every chart). Theorems 3.19 and 3.56 are now also stated with the text's hypothesis "`f'(x)`
     surjective". Tameness of the strong bundle (the standing hypothesis `htame` of §3.6) is used
     for `d_C(ϕ(y)) = d_X(y)`; in a non-tame chart `d_C(ϕ(y))` can exceed `d_X(y)`, and the cone
     would have to be transported from a chart realizing `d_X(y)` (Proposition 2.30), which is
     not done. Also added: Theorem 3.56 with the tameness of the induced structure and the regular
     data at every zero (`theorem_3_56_tame`; `theorem_3_56` states only the manifold structure and
     "without boundary"), and Theorem 3.19 with tameness (`theorem_3_19_index`).
174. **Item 100's "iff", and the filler condition of `IsGoodPositionGermFilled` is not an extra
     assumption** (`Polyfold.normal_injective_of_exists_range_scDeriv_eq_ρ`,
     `exists_range_scDeriv_eq_ρ_iff_normal_injective`, `isGoodPositionGermFilled_of_isGoodPositionGerm`).
     The converse direction of item 100: at a point `z₀` of the retract with
     `ker Dg(z₀) ⊆ T_{z₀}O`, if `Tf̃(z₀)` maps onto `K_{z₀}` then `C(z₀) = (1 − ρ(z₀))Dg(z₀)|_{ker Dr(z₀)}`
     is injective (for `b ∈ ker Dr(z₀)` with `Dg(z₀)b ∈ K_{z₀}`, pick `a ∈ T_{z₀}O` with
     `Dg(z₀)a = Dg(z₀)b`; then `a − b ∈ ker Dg(z₀) ⊆ T_{z₀}O`, so `b ∈ T_{z₀}O ∩ ker Dr(z₀) = 0`);
     the surjectivity of `Dg(z₀)` is not needed for this direction. With
     `exists_range_scDeriv_eq_ρ_of_normal_injective` this is the equivalence "`Tf̃(z₀)` onto ⟺
     condition (3) of Definition 3.4 at `z₀`" (under `Dg(z₀)` onto and `ker Dg(z₀) ⊆ T_{z₀}O`). With
     Theorem 3.54 (1) (`theorem_3_54_one'`) and `ker Dg(z₀) ⊆ T_{z₀}O` at the nearby zeros (item 102)
     it gives `isGoodPositionGermFilled_of_isGoodPositionGerm`: the filler of
     `theorem_3_54_nearby_kernel` satisfies condition (3) at every zero of `g` in `O` near `0`. So
     the added hypothesis of `theorem_3_54_one`, `theorem_3_54`, `theorem_3_23`, `theorem_3_19`
     holds whenever `(f, x₀)` is in good position (for a tame strong bundle): it was never a
     restriction, but proving that needs the surjectivity of item 180.
175. **Docstrings corrected** (no change of statements): the "not formalized / what remains"
     paragraphs of `GlobalIFT.lean`, `GlobalIFTFull.lean`, `GlobalIFTCenter.lean`,
     `GlobalIFTTheorems.lean` and `GlobalIFTNearbySurj.lean` predated the assembled theorems and now
     point to `GlobalIFTTheorems.lean`, `SolutionGermRecentre.lean`, `LinearizationCharts.lean`,
     `GlobalIFTNearby*.lean` and `GlobalIFTIndex.lean`; `TangentGerm.lean` repeated the sketch of
     item 83 with the case `Σ = ∅` that item 131 shows it misses (now: the lemma
     `exists_goodComplement_projectsInto` with the kept coordinate). Names cited in backticks that do
     not exist were replaced by the real ones: `scDeriv_eq_scDerivGerm_of_eqOn` →
     `scDeriv_eq_of_eqOn_nhds` (`GlobalIFT.lean`), `not_isGoodComplement_prod_of_not_le` →
     `mem_lineality_of_goodComplement_prod`, `sup_lineality_eq_top_of_goodComplement_prod`
     (`GlobalIFTNearbyPerturb.lean`), `range_toBase_deriv_le_range_scDeriv_of_fixed` →
     `scDeriv_apply_toBase_deriv_eq_of_fixed` (`GlobalIFTNearbyGraph.lean`), `next_B_isSckGerm` →
     `nextB_isSckGerm` (`GermIFT.lean`), `ShiftedBasicData.ker_Dg_eq_map`, `surjective_DH` →
     `ShiftedBasicData.surjective_DH_and_ker_eq` (`GlobalIFTNearbyOntoCurve.lean`),
     `ShiftedBasicData.eW` → `perturbEW` (`GlobalIFTNearbyOntoGerm.lean`), `exists_ehat_bounds` →
     `exists_xi_radii_bounds` (`GlobalIFTNearbyOntoXi.lean`), `ScNbhdGerm.univ` → `ScNbhdGerm.full`
     (`Germ.lean`); `theorem_3_54_index_locally_constant`, announced in `GlobalIFTNearbyOnto.lean`,
     now exists (item 171). Checked by resolving every backticked identifier with an underscore or
     a dot in the docstrings of `Chapter3/*.lean` against the environment (excluding the
     subscript notation `X_m`, file names, and `ParamPerturbation.lean`, not touched here).

Found while repairing the tameness hypothesis of the §3.6 theorems (`TameGerms.lean` and the
statements of `GlobalIFT*.lean`, `LinearizationCharts.lean`, `ParamPerturbation.lean`;
2026-10-26).

190. **The hypothesis `htame` of the §3.6 theorems was unsatisfiable, so every theorem assuming it
     was vacuous.** The implicit function theorems of §3.6 were stated with
     `htame : ∀ c : StrongBundleChart PX P, B.IsChart c → (c.isRetraction.baseRetraction c.relOpen).IsTame`,
     "the base retraction of **every** strong bundle chart compatible with the atlas is tame"
     (item 86). This is false for every strong bundle over a nonempty base. Compatibility
     (Definition 2.50, `StrongBundleChart.Compatible`) constrains only the transition maps between
     the retracts `K`, not the retraction whose image `K` is. Given a compatible chart
     `(φ, U, R, Φ)` with model `(O, C, E)` and `R(u, h) = (r(u), Γ(u, h))`, put `E' = ℝ ⊕ E`,
     `C' = [0, ∞) × C`, `U' = [0, ∞) × U`, `R'((a, u), h) = ((1, r(u)), Γ(u, h))`, `φ' = (1, φ)`
     onto `O' = {1} × O`, `Φ' = (1, Φ)` onto `K' = {1} × K`. Then `R'` is a strong bundle
     retraction, `Φ'` a strong bundle chart, and its transition maps with any chart `c''` are those
     of `c` composed with the affine maps `(a, u, h) ↦ (u, h)` and `(u, h) ↦ (1, u, h)` (which preserve
     the fibre and its levels), so `c'` is compatible with every chart `c` is compatible with. But
     `r'(a, u) = (1, r(u))` violates condition (1) of Definition 2.34: for `u ∈ O`,
     `d_{C'}(0, u) = 1 + d_C(u) ≠ d_C(u) = d_{C'}(1, u) = d_{C'}(r'(0, u))`. So `htame` fails as soon
     as the atlas has a chart with `O ≠ ∅`. (Chapter 5 item 61 gave a simpler instance with the same
     `K` and a larger non-tame `U`; it needs a boundary in `C`, this construction does not.) **Only
     the retraction-level half is machine-checked** (`TameVacuity.lean`,
     `ScRetraction.halfLineConst_prod_not_isTame`: for every sc-retraction `r` of a nonempty `U`,
     the product of the constant retraction `(a, w) ↦ (1, 0)` of `[0, ∞) ⊕ W` with `r` is a
     retraction onto `{(1, 0)} × r(U)` which is not tame; `W` is an arbitrary sc-Banach space,
     present only to have the presented quadrant `quadrant 1 W 0`). Building the chart `c'` and
     checking the six conditions of `Compatible` (on `[0]` and `[1]`) is sc-calculus for affine
     maps of the size of `Chapter4/Recentre.lean` (several hundred lines) and is not done. The statements that contained `htame` (39 in Chapter 3, 6 in Chapter 5) were therefore
     vacuously true: `theorem_3_54_graph(_proj)(_conj)`, `theorem_3_54_tangentGermChart(_proj)(_conj)`,
     `theorem_3_54_nearby`, `theorem_3_54_nearby_kernel`, `theorem_3_54_one`, `theorem_3_54_one'`,
     `theorem_3_54_tangentGermChart_solutionSet`, `theorem_3_54_two`, `theorem_3_54`, `theorem_3_54'`,
     `theorem_3_23_of_nearby`, `theorem_3_23`, `theorem_3_23'`, `theorem_3_19`, `theorem_3_19'`,
     `corollary_3_24`, `theorem_3_56`, `theorem_3_57`, `theorem_3_57_dim`,
     `theorem_3_54_tangentGermChart_index`, `theorem_3_54_tangentGermChart_solutionSet_index`,
     `theorem_3_54_two_index`, `isSurjLinOfIndex_of_forall_dim`, `theorem_3_54_index_locally_constant`,
     `theorem_3_54_index`, `theorem_3_23_index`, `theorem_3_19_index`, `theorem_3_19_of_surjective`,
     `theorem_3_57_index`, `theorem_3_56_tame`, `theorem_3_56_of_surjective`,
     `theorem_3_54_ker_eq_tangent`, `isGoodPositionGermFilled_of_isGoodPositionGerm`,
     `StrongBundle.isGoodPositionGerm_of_isLinSurjAt`, `StrongBundle.isGoodPositionGerm_iff_isLinSurjAt`,
     and the Chapter 5 statements of Chapter 5 items 74–79. The claims of items 153–157, 170–174,
     180–189 and Chapter 5 items 60–72 that these theorems hold "with the text's hypotheses" were
     void until this repair. The proofs were sound: they used `htame` only at specific charts (item
     191), so the repair is a change of statements, not of arguments.
191. **The repair, and why it is the text's meaning.** The proofs used `htame c hc` only for the
     chart `c` of the germ data at `x₀` (`(1 − Dr(0))E ⊆ E₀`, Proposition 2.35, in
     `theorem_3_54_graph_proj_conj`, `theorem_3_54_nearby_kernel`, `theorem_3_54_one`,
     `theorem_3_54_one'`), for the chart `ψ ∘ ϕ` built from it (`ψ(O)` tame,
     `theorem_3_54_tangentGermChart_proj_conj`), and for the chart in which `f'(y)` is onto
     (`isGoodPositionGerm_of_isLinSurjAt`, item 194). The text asks for exactly this. Definition
     3.50 (the recall of Definition 3.11 at the start of §3.6) requires the chart of an sc-Fredholm
     germ of a tame strong bundle to have a tame local bundle ("where `K → O` is a tame strong local
     bundle"); the proof of Proposition 3.52 starts "there exists a tame strong bundle chart"; and
     before Definition 2.51, "a tame strong bundle retraction is one for which the retraction `r`
     is tame". The new predicates (`TameGerms.lean`): `StrongBundle.IsTameChart B c` (`B.IsChart c`
     and the base retraction tame); `IsScFredholmGermTame` (Definition 3.50: the data of
     `IsScFredholmGerm` in a tame chart); `IsGoodPositionGermTame` (Definition 3.53 in a tame
     chart); `IsScFredholmSectionTame` (Definition 3.51, Definition 3.14 for a tame strong bundle:
     an `IsScFredholmSection` with tame germ data at every smooth point; a structure extending
     `IsScFredholmSection`); forgetful lemmas to the untamed forms. The theorems take
     `hg : IsGoodPositionGermTame f x₀` in place of `hg : IsGoodPositionGerm f x₀` and `htame`, and,
     where they conclude the good position of the nearby zeros, `hf : IsScFredholmSectionTame f`
     in place of `hf : IsScFredholmSection f`; the conclusions "`(f, y)` in good position" are
     `IsGoodPositionGermTame f y`, and the charts produced by the `_conj`, `_graph`, `_nearby`,
     `_ker_eq_tangent` theorems are `IsTameChart`. Definition 3.11 itself (stated for a strong
     bundle over a tame M-polyfold), Theorems 3.12, 3.15, 3.18, Proposition 3.52 and the chart
     independence of the linearization do not need tameness and keep
     `IsScFredholmGerm`/`IsScFredholmSection`.
192. **The restated theorems** (all names kept; old hypotheses → new). (a) `hg : IsGoodPositionGerm f x₀`
     and `htame` → `hg : IsGoodPositionGermTame f x₀`, the section hypothesis unchanged
     (`IsSection P f` or `IsScSmoothSection`): `theorem_3_54_graph_proj_conj`,
     `theorem_3_54_graph_proj`, `theorem_3_54_graph`, `theorem_3_54_nearby`,
     `theorem_3_54_nearby_kernel`, `theorem_3_54_ker_eq_tangent` (the chart `c` of the conclusion now
     `IsTameChart`), `theorem_3_54_tangentGermChart_proj_conj` (chart `IsTameChart`),
     `theorem_3_54_tangentGermChart_proj`, `theorem_3_54_tangentGermChart`,
     `theorem_3_54_tangentGermChart_solutionSet`, `theorem_3_54_tangentGermChart_index`,
     `theorem_3_54_tangentGermChart_solutionSet_index`, `isSurjLinOfIndex_of_forall_dim`; with
     `hall : ∀ y ∈ Vx₀, IsZeroAt P f y → IsGoodPositionGerm f y` → `… → IsGoodPositionGermTame f y`:
     `theorem_3_54_two`, `theorem_3_54_two_index`, `theorem_3_23_of_nearby` (`hf` stays
     `IsScFredholmSection`). (b) `hf : IsScFredholmSection f`, `hg : IsGoodPositionGerm f x₀`, `htame`
     → `hf : IsScFredholmSectionTame f`, `hg : IsGoodPositionGermTame f x₀`, conclusions in tame
     charts: `theorem_3_54_one'`, `theorem_3_54'`, `theorem_3_23'`, `theorem_3_19'`,
     `theorem_3_54_index_locally_constant`, `theorem_3_54_index`, `theorem_3_23_index`,
     `theorem_3_19_index`, `isGoodPositionGermFilled_of_isGoodPositionGerm`. (c) `hf`, `htame` →
     `hf : IsScFredholmSectionTame f` with `hg : IsGoodPositionGermFilled f x₀` (now in a tame chart,
     item 196): `theorem_3_54_one`, `theorem_3_54`, `theorem_3_23`, `theorem_3_19`. (d) The global
     theorems: `htame` and `hall : ∀ x, IsZeroAt P f x → IsGoodPositionGerm f x` →
     `hall : ∀ x, IsZeroAt P f x → IsGoodPositionGermTame f x`, `hf : IsScFredholmSection f` kept
     (good position in a tame chart at every zero is all they use): `theorem_3_57`, `corollary_3_24`,
     `theorem_3_56`, `theorem_3_57_dim`, `theorem_3_57_index`, `theorem_3_56_tame`. (e) The text's
     "`f'(x)` surjective": `theorem_3_19_of_surjective`, `theorem_3_56_of_surjective` take
     `hf : IsScFredholmSectionTame f` and no `htame`; `StrongBundle.isGoodPositionGerm_of_isLinSurjAt`
     (`hf : IsScFredholmSectionTame f`, conclusion `IsGoodPositionGermTame f y`) and
     `StrongBundle.isGoodPositionGerm_iff_isLinSurjAt` (`IsGoodPositionGermTame f y ↔ IsLinSurjAt f y`).
     `isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero` already had the specific-chart form
     (`htame : (c.isRetraction.baseRetraction c.relOpen).IsTame`) and is unchanged.
193. **Good position does not depend on the chart of the germ data**
     (`StrongBundle.isGoodPositionAt_of_chart_dense`, `StrongBundle.IsGoodPositionGerm.toTame`). The
     good position at a nearby zero `y` is proved in the chart at `x₀` and carried by
     `isGoodPositionGerm_of_chart_dense` to the chart of the germ data at `y`; but that lemma took its
     target chart from the existential in `IsScFredholmGerm f y`, so it could not say that the chart
     is tame. `isGoodPositionAt_of_chart_dense` proves the good position in **every** chart carrying
     germ data at `y` (`isGoodPositionGerm_of_chart_dense` is now its corollary), and
     `IsGoodPositionGerm.toTame` reads a good position given in any chart in the tame chart of
     `IsScFredholmGermTame f y` (in the chart of the good position `Tf̃(0)` is onto `K₀ ⊇ ρ(0)F_∞`,
     `ker Dg(0) ⊆ T₀O`, and `C_0 = C`). This is the chart independence of Definition 3.53 (the local
     form of gap G.13) for the whole datum of Definition 3.11.
194. **"Good position = surjectivity when `d_X = 0`" used the tameness of an arbitrary chart.**
     `isGoodPositionGerm_of_isLinSurjAt` took the chart from `IsLinSurjAt f y` (some chart in which
     `f'(y)` is onto) and needed `d_C(ϕ(y)) = d_X(y)` there (item 173). Now the surjectivity is
     carried to the tame chart of the germ data at `y` (`StrongBundle.IsLinSurjAt.linAt_surjective`,
     moved unchanged from `Chapter5/Transversality.lean` to `GlobalIFTIndex.lean`), the lemma is
     applied there, and the conclusion is `IsGoodPositionGermTame`.
195. **Theorems 3.15 and 3.18 for tame germ data** (`theorem_3_15_tame`,
     `StrongBundle.IsScFredholmGermTame.sectionAdd`, `PullbackChartData.ofProd_isTame`,
     `StrongBundle.IsScFredholmGermTame.param`, `StrongBundle.IsScFredholmSectionTame.param`,
     `theorem_3_18_tame`). The proof of Theorem 3.15 keeps the chart, so tame germ data stay tame.
     For Theorem 3.18 the germ of `f̃` at `(r₀, x)` is taken in the product chart
     `(r ↦ r − r₀) × φ` with base retraction `1 × r` on `ℝⁿ × U` (`PullbackChartData.ofProd`): the
     factor `ℝⁿ` is free (the identity retraction of the whole space, `ScRetraction.id_isTame`), so
     `d(a, u) = d_C(u)`, the minimal subspaces and the tangent spaces are products, and `1 × r` is
     tame when `r` is (`ScRetraction.IsTameWith.prod`, exposition Lemma 4.D). Hence
     `F(r, x) = f(x) + Σ rᵢ sᵢ(x)` has tame germ data on `ℝⁿ × X` (Definition 3.51 for `π*P`)
     whenever `f` has, which is what Theorem 5.13 needs in place of `PullbacksHaveTameCharts`
     (Chapter 5 item 75). Item 160's "`π*P` is tame when `P` is" (`prod_rn_isTame`) concerns the base
     `ℝⁿ × X`; this item concerns the charts of the germ data.
196. **`IsGoodPositionGermFilled` is now stated in a tame chart** (the data of Definition 3.53 with
     the filler condition of item 100, in a chart with `IsTameChart`), with
     `IsGoodPositionGermFilled.isGoodPositionGermTame`; `isGoodPositionGermFilled_of_isGoodPositionGerm`
     (item 174) produces it from `IsGoodPositionGermTame` (the chart of `theorem_3_54_nearby_kernel`
     is the tame chart at `x₀`).
197. **The audit of hypotheses that quantify over all compatible charts.** Searched in `Polyfold/`
     for `∀ c : StrongBundleChart …, B.IsChart c → …`, `∀ φ : MChart X, P.IsChart φ → …`,
     `∀ R : ScRetraction …` and `∈ … atlas.charts →`. Unsatisfiable, repaired: `htame` (Chapter 3,
     item 192) and `htame`, `htameP`, `StrongBundle.PullbacksHaveTameCharts` (Chapter 5, items
     74–76; the definition is removed). Satisfiable, kept: the definition of sc-smooth maps between
     M-polyfolds (`MPolyfold.IsScSmoothMap`, "in all compatible charts", chart independent because
     the transition maps are sc-smooth); `StrongBundle.IsSurjLinOfIndex` (a conclusion, obtained in
     every chart through `linAt_chart_independence`); `isScSmoothMap_toLevelOne_iff`
     (`Chapter4/ScPlus.lean`: every compatible chart's model is an sc⁺-retract, an iff with an
     intrinsic condition that holds e.g. for finite-dimensional `X`); the chart-free forms
     `MPolyfold.isGoodPositionAt_iff_forall`, `isGeneralPositionAt_iff_forall`
     (`Chapter4/Submanifolds.lean`, iffs with the one-chart condition); `StrongBundle.doubleLevel`
     and `StrongBundle.IsScSmoothSection` (`∀ c ∈ B.atlas.charts`, a fixed atlas); and
     `IsScSmoothRetractMap` (`∀ R : ScRetraction`, all sc-retractions onto a fixed retract, the
     text's Definition 2.8). The tameness hypotheses of Chapters 2 and 4 (`MPolyfold.IsTame`: an
     equivalent atlas of tame charts; `IsTameRetract`: some tame retraction; local names `htame` for
     the tameness of one chart) are existential and satisfiable.
198. **The new hypotheses are satisfiable** (`StrongBundle.isTameChart_of_eqOn_id`,
     `ScRetraction.IsTame.congr`): a compatible strong bundle chart whose base retraction is the
     identity of `U` (`O = U`, relatively open in the partial quadrant) is tame, since Definition
     2.34 depends only on `U` and the values of `r` on `U`, and the identity retraction is tame
     (`ScRetraction.id_isTame`). Over an M-polyfold modelled on relatively open subsets of partial
     quadrants (a manifold with boundary with corners, an sc-Banach space) such charts exist —
     where `htame` failed as well (item 190).
199. **Not done**: the chart-level machine-checked form of item 190 for a general strong bundle
     (the compatible strong bundle chart `(1, φ)` with the non-tame base retraction of
     `ScRetraction.halfLineConst_prod_not_isTame`; done for the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ`
     in item 202); and the
     statement that in a strong bundle with an atlas of tame charts every sc-Fredholm germ has germ
     data in a tame chart (Definition 3.11 ⟹ Definition 3.50; it would need the re-centring of a
     tame chart of the atlas at the point and the transport of the filler and the conjugation to
     it; the text builds the tame chart into Definition 3.50, and so do the restated theorems).
     *(2026-11-02: the re-centring strategy is refuted — a filling is bound to its chart — and the
     implication is open; the first part is still not done; items 350–354.)*

Found while checking that the hypotheses of the §3.6 theorems can hold (`NonVacuity.lean`,
2026-10-31; not in the text).

200. **The hypotheses of Theorem 3.57 (and so of Theorems 3.54, 3.56, Corollary 3.24) are
     satisfiable, by a complete example** (`Polyfold.TrivialBundle.hypotheses_theorem_3_57_graphSection`,
     `theorem_3_57_trivialBundle`, `theorem_3_57_example`). Item 198 shows that tame charts
     exist; this item checks the whole hypothesis set on a concrete strong bundle. For the trivial
     strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` (constant sc-structures, translation charts with the identity
     strong bundle retraction, the fibre structure transported from `ℝᵏ`) and a `C^∞` map
     `φ : ℝⁿ → ℝᵏ`, the section `x ↦ (x, φ(x))` is sc-Fredholm (`IsScFredholmSection`) with
     tame germ data at every point (`IsScFredholmSectionTame`). It is in good position in a
     tame chart (`IsGoodPositionGermTame`) at every point where `Dφ` is onto. The germ data at
     `x₀` are: the principal part `g(u) = φ(u + x₀)` as its own filled version; the constant
     sc⁺-section `φ(x₀)`; and `g − φ(x₀)` conjugated to the basic germ `h(a, w) = (g(a) − φ(x₀), w)`
     with `W = 0`, `B = 0` (`isConjugateToBasicGerm_of_contDiff`). So when `0` is a regular value
     of `φ` and `φ⁻¹(0) ≠ ∅`, `theorem_3_57` applies, and its conclusion is the regular value
     theorem for `φ⁻¹(0)`; the instance `φ(x, y) = x` on `ℝ²` is `theorem_3_57_example`. The
     example has no boundary (`C = ℝⁿ`) and finite-dimensional fibres. It shows that the
     hypotheses are consistent; it does not exercise the corner case (good position at
     `d_X(x) ≥ 1`, done in item 201) or the infinite-dimensional contraction part of a basic germ
     (a witness with `W ≠ 0` is not done).
201. **The hypotheses are satisfiable with boundary: good position at boundary zeros**
     (`NonVacuityCorner.lean`: `Polyfold.HalfSpaceBundle.hypotheses_theorem_3_57_halfSpace`,
     `theorem_3_57_halfSpace`, `theorem_3_57_halfSpace_example`). The base is the half-space
     `H = [0, ∞) × ℝᵐ` (the M-polyfold of the partial quadrant `quadrant 1 ℝᵐ`), the bundle
     `H × ℝᵏ → H`, and the section `x ↦ (x, φ(x))` for a `C^∞` map `φ : ℝ ⊕ ℝᵐ → ℝᵏ`. The charts
     centred at the points of `H` are the re-centred charts of `Chapter4/Recentre.lean`: `C_x = H`
     at a boundary point and `C_x = ℝ ⊕ ℝᵐ` at an interior one. They are tame, since the
     retraction stays the identity. Conjugation to a basic germ is over the partial quadrant
     `C_x` (`isConjugateToBasicGerm_halfSpace`). Definition 3.53 at a boundary zero `x` holds when
     `Dφ(x)` is onto and `ker Dφ(x) ⊄ {v₁ = 0}`, i.e. `0` is also a regular value of `φ|∂H`.
     A complement of `ker Dφ(x) ∩ {v₁ = 0}` inside `{v₁ = 0}` is then a good complement
     (`isInGoodPositionIn_halfSpace`). So `theorem_3_57` gives the regular value theorem for
     manifolds with boundary. The instance `φ(a, y) = y` on `[0, ∞) × ℝ` has solution set the
     half-line `[0, ∞) × {0}`, with the boundary zero `(0, 0)`. The transversality condition is
     the one the classical theorem needs: for `φ(a, y) = a` the kernel at the zeros is the
     boundary line, which is not in good position (no good complement), and the theorem does not
     apply. Two general lemmas came out of this: every strong bundle chart is compatible with
     itself (`StrongBundleChart.compatible_self`), and the sc-derivative is the classical
     derivative where the latter exists (`scDeriv_eq_of_hasFDerivAt`).
202. **The old hypothesis `htame` fails for the witness bundle, machine-checked**
     (`TameVacuityChart.lean`: `Polyfold.TrivialBundle.not_forall_isTame_of_isChart`,
     `htame_fails_repaired_holds`). For the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ` of item 200, the chart
     of item 190 is a strong bundle chart compatible with the atlas: the model `(ℝ ⊕ ℝ⁰) ⊕ ℝⁿ`
     with the partial quadrant `[0, ∞) × ℝⁿ`, the retraction `r(a, u) = (1, u)` onto `{1} × ℝⁿ`,
     the chart `x ↦ (1, x)` and `R((a, u), h) = ((1, u), h)` (`oddBundleChart`,
     `oddBundleChart_compatible`). Its transitions with the translation charts are affine. Its
     base retraction is not tame (`ScRetraction.halfLineConst_prod_not_isTame`). So
     `∀ c, B.IsChart c → (base retraction of c).IsTame` is false for this bundle, while the
     graph section of any surjective linear map meets the repaired hypotheses (item 200). The
     bundle therefore separates the two forms: the old theorems said nothing about it, and the
     repaired ones apply. For a general strong bundle the compatibility of `(1, φ)` is still not
     formalized (item 199).

Follow-ups of the round-trip audit (`RoundTrip/`, items V3.20, V3.82, V3.85, V4.38): good position
with the text's sc-complement (`GoodPositionSc.lean`, 2026-11-01).

210. **Item 19 revised: the sc-structure of the good complement matters for the conclusions, and
     is now proved there.** Item 19 says that neither the sc-structure nor the closedness of the
     good complement enters the proofs, so the project's `IsGoodComplement` asks only for the
     algebraic splitting `E₀ = N ⊕ P`. That stays true of good position as a *hypothesis*
     (Proposition 3.22, Lemmas 3.45, 3.65, Proposition 3.69 and the §3.6 theorems use only the
     algebraic splitting). It is not true of good position as a *conclusion*: Theorem 3.54 (1)
     ("at every zero `y` near `x` the germ `(f, y)` is in good position") was proved with an
     algebraic good complement only (`theorem_3_54_one'`, `IsGoodPositionGermTame`). That is less
     than the text claims, since an algebraic good complement need not be closed (round-trip item
     V3.20: in any infinite-dimensional `E` with `C = E₀`, `N = ℝv` and `P = ker ψ` for a
     discontinuous functional `ψ` with `ψ(v) ≠ 0`; machine-checked for an `ℓ²` scale in
     `RoundTrip/Items/V3_20.lean`, `not_B`). The text's notions are now project definitions:
     `Polyfold.IsScGoodComplement E C N P` (`E = N ⊕ P` an sc-splitting, `ScBanach.IsScSplitting`,
     with the constant `ε`) and `Polyfold.IsInGoodPositionSc E C N` (Definition 3.21 as written),
     with the forgetful `IsScGoodComplement.toIsGoodComplement` and
     `IsInGoodPositionSc.toIsInGoodPosition`. Their forms inside a subspace `T` are
     `IsScGoodComplementIn` and `IsInGoodPositionScIn`: `P ⊆ T` is an sc-subspace and
     `T_m = N_m ⊕ P_m` on every level. For `T = E₀` these are the previous two
     (`isInGoodPositionScIn_top_iff`), and the cone `T ∩ C` (the text's `C₀O = T₀O ∩ C`) gives the
     same notion as `C` (`isInGoodPositionScIn_inter_iff`). Theorem 3.54 (1) in the text's form is
     item 213.
211. **A closed good complement of a smooth `N` is an sc-complement**
     (`IsGoodComplement.isScGoodComplementIn`, `IsInGoodPosition.isInGoodPositionScIn`; for
     `T = E₀`, `IsGoodComplement.isScGoodComplement` and `IsInGoodPosition.isInGoodPositionSc`).
     Let `T` be an sc-subspace and `N ⊆ T` finite-dimensional with `N ⊆ E_∞`. If `Y` is a closed
     good complement of `N` in `E`, then `Y ∩ T` is a good sc-complement of `N` inside `T` with
     the same `ε`. Let `π` be the projection onto `N` along `Y` (continuous, as `Y` is closed and
     `N` finite-dimensional) and `lift_m : N → E_m` the lift (`finSmoothLift`). Then
     `x = lift_m(πx) + (x − lift_m(πx))` splits `T_m = N_m ⊕ (Y ∩ T)_m`. The map
     `x ↦ x − lift_m(πx)` sends the smooth points of `T_m` (dense, as `T` is an sc-subspace) to
     smooth points of `(Y ∩ T)_m` and fixes `(Y ∩ T)_m`, so those are dense. On a partial quadrant
     every `N` in good position has a closed good complement
     (`exists_goodComplement_projectsInto`, item 83). So a smooth `N` in good position with an
     algebraic complement is in good position with an sc-complement inside every sc-subspace
     `T ⊇ N`. Two dictionaries follow. For smooth `N`, the text's good complements are the
     project's closed ones (`isScGoodComplement_iff`; round-trip item V3.20: "the text's good
     complement = the project's + closed"). On a partial quadrant, Definition 3.21 as written is
     `IsInGoodPosition` together with `N ⊆ E_∞` (`isInGoodPositionSc_iff`). **Not done:** the same
     upgrade from good position inside `T` only (`IsInGoodPositionIn`, cone `T ∩ C`). The argument
     needs a closed good complement, which `exists_goodComplement_projectsInto` provides in `E`
     for a partial quadrant, not inside `T`. In the application good position in `E` comes from
     the transport lemma (item 212).
212. **Definition 3.53 with the sc-complement, and the upgrade at a zero**
     (`Polyfold.IsGoodPositionAtSc`, `StrongBundle.IsGoodPositionGermSc`,
     `StrongBundle.IsGoodPositionGermTame.isGoodPositionGermSc`, `isGoodPositionGermSc_iff`).
     `IsGoodPositionGermSc` is `IsGoodPositionGermTame` with the kernel condition in the text's
     form (`IsInGoodPositionScIn` inside `T₀O`). At a zero `y` of an sc-Fredholm section with tame
     germ data the two notions agree. The proof works in the tame chart centred at `y` that
     `theorem_3_54_nearby_kernel` gives when applied at `y` itself. (a) `ker Dg(0) =
     Dψ'(0)(ker D(h + t)(0))` is finite-dimensional and **smooth**: the kernel of the basic germ's
     linearization is smooth, and at a smooth point the derivative of an sc¹ map sends smooth
     vectors to smooth vectors (`IsSc1.scDeriv_mem_smooth`, because the tangent map is sc⁰).
     (b) `T₀O = Dr(0)E` is an sc-subspace and `(1 − Dr(0))E ⊆ E₀` (Proposition 2.35, tame
     retraction). (c) `ker Dg(0)` is in good position to `C` in `E` (the transport lemma
     `IsInGoodPositionIn.isInGoodPosition`). (d) Item 211 gives the sc-complement inside `T₀O`. In
     the text the kernel is smooth because `f'(y)` is sc-Fredholm (Proposition 3.52); the project's
     `proposition_3_52` proves the level-`0` Fredholm property only, so here smoothness comes from
     the conjugation to a basic germ.
213. **Theorem 3.54 (1) with the text's notion of good position** (`theorem_3_54_one_sc`,
     `theorem_3_54_one_sc_of_tame`; with (2), `theorem_3_54_sc`; Theorem 3.23, `theorem_3_23_sc`).
     Let `f` be an sc-Fredholm section with tame germ data, `f(x₀) = 0`, and `(f, x₀)` in good
     position. Then there is an open `Vx ∋ x₀` such that at every zero `y ∈ Vx` the germ `(f, y)`
     is in good position with an sc-complement (`IsGoodPositionGermSc`). The hypothesis may be the
     algebraic form (`theorem_3_54_one_sc_of_tame`) or the sc form (`theorem_3_54_one_sc`). The
     proof is `theorem_3_54_one'` followed by item 212; no hypothesis is added. The conclusion the
     round-trip audit reached for items V3.82 and V3.85 only through glue in `RoundTrip/` is now a
     project theorem. The global theorems with the hypothesis "every zero is in good position" in
     the text's sense are `theorem_3_57_sc`, `corollary_3_24_sc` and `theorem_3_56_sc`; they
     follow from the forgetful lemma. For an sc-Fredholm section with tame germ data that
     hypothesis is the project's (`forall_isGoodPositionGermSc_iff`).
214. **Choices, and what is not done.** (a) Condition (2) of Definition 3.53 is stated without
     the case distinction `d_X(x) ≥ 1`, as in the project's `IsGoodPositionAt`. As a conclusion
     this is stronger than the text's. As a hypothesis it is stronger too, but
     `theorem_3_54_one_sc_of_tame` takes the weaker algebraic form. The round-trip glue
     `isGoodPositionGermTame_of_sc` (V3.82, the case `d_X(x) = 0`) shows that the text's
     case-distinguished form gives `IsGoodPositionGermTame`. It is not moved into the project, so
     a version of Theorem 3.54 (1) whose hypothesis carries the case distinction is not stated.
     (b) "`T = N ⊕ P` is an sc-splitting of `T`" is written in `E` (`IsScGoodComplementIn`: `N`,
     `P` sc-subspaces of `E` inside `T`, levelwise complements in `T_m = T ∩ E_m`). The
     equivalence with `IsScSplitting` in the sc-Banach space `E.ofSubspace hT` is not formalized;
     for `T = E₀` it is `isScGoodComplementIn_top_iff`. (c) The remark after Definition 3.21 (a
     topological complement for a non-smooth `N`) is not given its own definition; on a partial
     quadrant a closed good complement always exists (`exists_goodComplement_projectsInto`).
     (d) The other §3.6 theorems that conclude good position (`theorem_3_19'`, the Chapter 5
     theorems) are not restated with the sc form; each restatement is
     `IsGoodPositionGermTame.isGoodPositionGermSc` at the zeros.

Follow-ups of the round-trip audit, continued (`RoundTrip/`, items V3.11, V3.66): Lemma 3.9 and
Lemma 3.81 as stated (additions to `SolutionLinearization.lean` and `QuadrantIFT.lean`,
2026-11-01).

215. **Lemma 3.9 holds as stated: smallness on level `m` suffices for the level-`m` estimate
     (revises item 71 (b)).** The text: for every `ε > 0` and `m`, `|D₂B(a, w)ζ|_m ≤ ε|ζ|_m` for
     `ζ ∈ W_m` and `(a, w) ∈ E_{m+1}` close to `(0, 0)` in `E_m`. The project had two partial
     forms: `ContractionGerm.norm_levelDeriv_snd_le` (every level, but only the constant `1/2`, for
     `w` in the contraction regions of the working form) and
     `IsSc0ContractionGerm.exists_norm_deriv_snd_le` (every `ε`, but level `0` only and `x ∈ U₁`
     small on level `1`). Its docstring and item 71 (b) said that smallness on level `1` is
     needed because the curve `t ↦ x + t(0, ζ)` must stay in `U₁`, where `B` is differentiable.
     The curve must stay in `U₁`, but for `ζ ∈ W₁` it does so for small `t ≥ 0` whatever `|x|₁`
     is, since `U₁` is relatively open in `C̃ ⊕ W₁`; the contraction estimate of Definition 3.28 is
     applied on level `0`, at points `(a, ιw + tιζ)` that are small on level `0` when `x` is.
     Proved now: `IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le` (the text's statement: for
     every `ε` and `m` an `r > 0` with `|D₂B(x)ζ|_m ≤ ε|ζ|_m` for `x ∈ U_{m+1}`, `|ιx|_m < r`,
     `D₂B(x)ζ` the level-`m` operator `levelDeriv DB m x (0, ζ)`; it uses Proposition 1.16 for
     germs, `IsSc1GermWith.hasFDerivWithinAt_level`, and so the hypothesis that `C̃` is
     quadrant-like) and `IsSc0ContractionGerm.exists_norm_deriv_snd_le_base` (level `0`, `x ∈ U₁`
     with `|ιx|₀ < r`, no quadrant hypothesis). As in item 6, `B` is an sc⁰-contraction germ which
     is sc¹, not sc-smooth. This is the round-trip auditor's proof (item V3.11,
     `RoundTrip/Items/V3_11.lean`, `level_bound`, written for the blind basic germ), adapted to
     `IsSc0ContractionGerm`; the docstring of `exists_norm_deriv_snd_le` is corrected.
216. **Lemma 3.81's estimate holds on all of `V₀`, even with the constant `ε/(1 + ε)` (revises
     item 25).** Item 25 says that the text's argument for `|τ(k) − τ(k₀)| ≤ ε|k − k₀|` uses the
     point `(k, τ(k₀))`, which lies in the region `R` only when `|τ(k₀)| ≤ ε|k|`, and the Lean
     proof (`Polyfold.Radii.norm_τ_sub_le`) bounded the other case crudely, getting the constant
     `1 + 2ε`. The other case is the same argument with `k` and `k₀` exchanged: if `|k₀| > 2|k|`
     then `|k| < 2|k₀|`, so `|τ(k)| ≤ ε|k|/2 ≤ ε|k₀|` and `(k₀, τ(k)) ∈ R`. In either case
     `|τ(k) − τ(k₀)| ≤ (1/2)|τ(k) − τ(k₀)| + c₀|k − k₀|` with `c₀ = ε/(2(1 + ε))` the bound on
     `‖DB‖` over `R`, so `|τ(k) − τ(k₀)| ≤ ε/(1 + ε)·|k − k₀|` for all `k, k₀ ∈ V₀`
     (`Radii.norm_τ_sub_le_global`, with the case lemma `Radii.norm_τ_sub_le_of_norm_le`). This
     gives the text's constant `ε` (`Radii.norm_τ_sub_le_eps`) and `Radii.lipschitzOnWith_τ`. So the
     text's statement is true on all of `V₀`; its proof only omits the case distinction. The
     project's remark that the text's estimate holds only for `k` near `k₀` was too pessimistic.
     Round-trip item V3.66 (`RoundTrip/Items/V3_66.lean`, `lip`); the module docstring of
     `QuadrantIFT.lean` and the docstring of `norm_τ_sub_le` are corrected.
217. **What is unchanged.** The older forms are kept, with corrected docstrings, because other
     proofs use them: `exists_norm_deriv_snd_le` (smallness on level `1`) in Corollary 3.41
     (item 71, `StabilityData.exists_isFredholm_Dfs'`), and `norm_τ_sub_le` (constant `1 + 2ε`)
     in `continuousOn_τ` and Lemma 3.82. Those uses were not re-examined with the stronger forms.
     The second statement of Proposition 3.10 (`Df(a, w)` Fredholm of index `n − N` on level `m`
     for `(a, w)` small, item 46) is still not formalized; the form of Lemma 3.9 it needs, at points
     near `(0, 0)` on every level with an arbitrary `ε`, is now available.

Round-trip audit findings (`RoundTrip/REPORT.md`, 2026-11-01), recorded here only: nothing in the
project was changed for them.

220. **Definitions 3.3, 3.6, 3.11, 3.14 (and 3.50–3.51) live on the whole `U` of a chart, while the
     text's germs may have levels that shrink with `m`.** The text: an sc-germ of neighbourhoods is
     any decreasing `U₀ ⊃ U₁ ⊃ ⋯`, `U_m` relatively open in `C ∩ E_m` (Definition 3.1, p. 62);
     Definitions 3.3–3.14 (pp. 63–70) ask for sc-smooth germs *(book 2017: Definitions 3.1, 3.3,
     3.5, 3.7, 3.8)*. The project works on the levels `U ∩ E_m`
     (`StrongBundle.IsScSmoothSectionGerm`, `IsFilledVersion`, `IsFillerOf` with `[1 − ρ(r)]g` sc¹
     on `U`, the sc⁺-section and conjugation in `IsScFredholmGerm`). Round-trip items V3.5, V3.9,
     V3.13, V3.16, V3.19, V3.43, V3.45, V3.103 locate the difference here: project ⇒ text is proved
     in a common chart (`proj_to_B` in `RoundTrip/Items/V3_5.lean`, `V3_9.lean`; `B_fwd` in
     `V3_45.lean`), text ⇒ project is not, and "filled version = filling" on a given `U` is false
     (`V3_43.lean`, `not_B`: a step function, a smooth germ on `(−∞, 1)`).
221. **The converse fails for germs with shrinking levels; the docstrings calling the whole-`U`
     reading "no restriction" are wrong.** A function `C^k` on `(−1/k, 1/k)` for every `k`, `C^∞` on
     no neighbourhood of `0`, is an sc-smooth germ in the constant scale `ℝ` but sc-smooth on no
     open `U ∋ 0`; shrinking the chart never makes the levels shrink (the auditors' example, not
     machine-checked). So the formal theorems are narrower where these notions are hypotheses
     (Theorems 3.15, 3.19, 3.54–3.57, Chapter 5) and stronger where they are conclusions (Theorems
     3.15, 3.18). The module docstring of `Chapter3/StrongBundleSections.lean` ("no restriction
     since the strong bundle chart can be restricted to `U ∩ W`"), that of `IsFilledVersion` and
     item 43 overlook this (corrected 2026-11-01). Open: whether this separates sc-Fredholm
     sections (shrinking germs do occur, items 141, 222). *(Now: the example is machine-checked
     (`Chapter3/GermVsChart.lean`), the text's germ reading of Definition 3.11 is formalized, and
     the project's notion is exactly the germ reading with `g`, `s` sc-smooth on the whole `U`;
     whether this separates sc-Fredholm sections is still open, with the obstruction located on
     level `0`: items 260–266.)* *(2026-11-01: phase 2 switched Definition 3.11 and everything built
     on it to the text's germ reading (items 330–334), so the theorems no longer depend on the
     answer; the notions that were narrower as hypotheses are now the text's.)*
222. **Corollary 3.34 and Theorem 3.35, "`δ` is sc-smooth", hold on one germ for all `k` (revises
     item 2); Lemma 3.31's `f⁽¹⁾` satisfies Definition 3.28.** Round-trip items V3.31, V3.32
     (`RoundTrip/Items/V3_31.lean`, `V3_32.lean`, `A_to_B`): from `theorem_3_33_smooth`,
     `theorem_3_35_smooth`, `δ` is sc^k for every `k` on the diagonal germ
     `V'_m = V_m ∩ N(m + Σ_{j≤m} s_j) ∩ {δ ∈ O₀}`, by the locality lemma `isSckGerm_of_levels` (sc^k
     on `G'` follows from sc^j, for every `j`, on germs containing `G'` on the levels `≥ j`). Item
     V3.28 (`V3_28.lean`, `A_to_B`): `f⁽¹⁾` is an sc⁰-contraction germ of Definition 3.28 on a germ
     of neighbourhoods (`nextG 0`), by Lemma 3.9 on level `m` with any `ε` (item 215); the project's
     `ContractionGerm.next` is only a `1/2`-contraction (item 3). Neither result is in the project.
     *(Both moved into the project since: items 250–252, `Chapter3/GermIFTSmooth.lean`.)*
223. **Proposition 3.10, second statement, still not formalized; the audit outlines the proof.** The
     text (p. 68): `Df(a, w) : ℝⁿ ⊕ W_m → ℝᴺ ⊕ W_m` is Fredholm of index `n − N` for
     `(a, w) ∈ E_{m+1}` small in `E_m` (items 46, 217). Round-trip item V3.12: the first statement
     follows from `proposition_3_10` (`RoundTrip/Items/V3_12.lean`, `A_to_B1`); at points `x ≠ 0`
     the project has only `StabilityData.exists_isFredholm_Dfs'` (level `0`, `x` small on level `1`,
     the germs of Theorem 3.38). Believed true: on level `m`, `Df(x)` is `(a, w) ↦ (0, w)` plus
     finite rank, minus `D₂B(x)` (small by Lemma 3.9 on level `m`, item 215), plus the compact
     `ιDs(x)`; Corollary 3.41's argument redone on level `m`.
224. **sc-Fredholmness on all levels is not formalized; most §3.6 mismatches of the audit are this
     gap.** The text: `Tf(x)` and `f'(x₀)` are sc-Fredholm (Proposition 3.52, p. 110; Theorem 3.19,
     p. 74), and indices along the solution set are sc-indices (Theorem 3.54, Proposition 6.2). The
     project has the level-`0` Fredholm property and index in every chart (items 48, 170, 171),
     which gives the text's level-`0` parts (round-trip items V3.46, V3.68, V3.96–V3.101;
     `RoundTrip/Items/V3_96.lean`, `A_to_B_level0`). Missing: `T_zO`, `K_z` as sc-subspaces,
     `Lin(z)` as an sc-operator, the level-`m` Fredholm property (item 223); the other mismatches
     are tameness readings (items 190–199). Corollary 3.24's sc-complement of the kernel (V3.100)
     has been proved since (items 212–213); Corollary 5.8 has the same gap (Chapter 5 item 21).

**230–239: sc-Fredholm theory on all levels (2026-11-01).**

230. **Proposition 3.10, second statement, proved on every level `m` (revises items 46, 217,
     223).** The text (p. 68): for `f = h + s`, `h` a basic germ and `s` an sc⁺-germ,
     `Df(a, w) : ℝⁿ ⊕ W_m → ℝᴺ ⊕ W_m` is Fredholm of index `n − N` for `(a, w) ∈ E_{m+1}` small in
     `E_m`. `Polyfold.proposition_3_10_level` (`Chapter3/BasicGermLinearizationLevel.lean`): with
     the hypotheses of `proposition_3_10` (`IsBasicGerm Ct G h B`; `s` sc¹ into `(ℝᴺ ⊕ W)¹` with
     derivative `Ds`; `f = h + ι s` sc¹ with derivative `Df`) and `C̃` quadrant-like
     (`IsQuadrantLike`, which partial quadrants are), for every `m` there is `δ > 0` such that for
     every `x ∈ U_{m+1}` with `|ιx|_m < δ` the level-`m` operator `Df(x)_m = levelDeriv Df m x` (the
     bounded `L : E_m → F_m` with `ι_m L v = Df(x₁) ι_m v`, `x₁ ∈ U₁` the image of `x`) is
     Fredholm with `fredholmIndex = dim ℝⁿ − dim ℝᴺ`. The size of `x` on level `m + 1` is not
     restricted, and `f(0) = 0` is not used. Both statements together:
     `proposition_3_10_full`. The text's proof goes through as written:
     `Df(x)_m = T₀ + S(x) + K(x)` (`IsBasicGerm.levelDeriv_add_eq`) with `T₀(δa, δw) = (0, δw)`
     (the operator (32) on level `m`, Fredholm of index `n − N` by `IsScFredholm.fredholmIndex_lvl`),
     `S(x)(δa, δw) = (0, −D₂B(x)_m δw)` of norm `≤ ε` by Lemma 3.9 on level `m` (item 215), and
     `K(x)` the `ℝᴺ`-component and `−D₁B(x)_m` (finite rank) plus `ι_m pr_W Ds(x)_m` (compact
     through `W_{m+1} → W_m`; `IsBasicGerm.isCompactOperator_levelK`); then the stability of the
     index under small perturbations (`isFredholm_fredholmIndex_add_of_norm_lt`, `ε` chosen against
     a quasi-inverse of `T₀` on level `m`; a Neumann series argument) and under compact ones.
     The one identity the text uses silently is the `W`-component
     `pr_W Df(x)_m = pr_W − DB(x)_m + ι_m pr_W Ds(x)_m` (`IsBasicGerm.snd_levelDeriv_add`): it holds
     on level `0` at `x₁` by the uniqueness of derivatives within `U₁` and the density of `E₁` in
     `E₀`, and lifts to level `m` by the injectivity of `ι_m`. With the audit's glue (`B_to_proj`,
     `isPartialQuadrant_CtB` in `RoundTrip/Items/V3_12.lean`) the theorem gives clause (ii) of the
     blind statement of round-trip item V3.12 (`RoundTrip/Blind/V3_12.lean`); this was checked in
     a scratch file, not added to `RoundTrip/`. It is a level-wise statement, as in the text; for
     `x ∈ U_{m+1}`, `Df(x)` has level operators only on levels `≤ m`, so no sc-Fredholm claim at
     `x ≠ 0` is made.
233. **A criterion: an sc-operator is sc-Fredholm iff it is Fredholm on level `0` and
     regularizing.** `Polyfold.isScFredholm_of_isRegularizing`, `Polyfold.isScFredholm_iff`
     (`Chapter1/ScFredholmCriterion.lean`): for an sc-operator `T : E → F`, Definition 1.8 holds iff
     `T₀ : E₀ → F₀` is Fredholm and `T` is regularizing (`ScOperator.IsRegularizing`: `e ∈ E₀`,
     `Te ∈ F_m` ⟹ `e ∈ E_m`; the converse direction is Proposition 1.9,
     `IsScFredholm.isRegularizing`); every `T_m` is then Fredholm of the level-`0` index
     (`isScFredholm_of_isRegularizing_index`). Not stated in the text: it is the construction of
     §1.4.1 (proof of Proposition 1.10) with the two properties of `T + S` used there as
     hypotheses — the kernel is smooth (regularizing), `T(E_m) = Y ∩ F_m` (regularizing) so the
     smooth points of the range are dense on every level, and a complement of the range spanned by
     smooth points exists (`F_∞` dense, `F₀/Y` finite-dimensional). Also
     `Polyfold.isScOperator_of_mapsTo`: a bounded `T₀` with `T₀(E_m) ⊆ F_m` for all `m` is an
     sc-operator (the continuity on `E_m` asked by Definition 1.3 is the closed graph theorem).
     The criterion is the tool for the text's "is sc-Fredholm" claims about operators built from
     sc-Fredholm ones by conjugation and restriction (items 235, 236), which it makes without
     argument.
234. **Proposition 3.5 in sc form needs condition (3) of the filler on level `0` only.**
     `Polyfold.ScOperator.restrict` (for sc-subspaces `A ⊆ E`, `B ⊆ F` with `T(A) ⊆ B`, the
     restriction as an sc-operator between the induced sc-Banach spaces of Definition 1.5),
     `Polyfold.IsScFredholm.restrict`: the restriction of an sc-Fredholm `T` is sc-Fredholm, with
     the level-`0` index on every level, as soon as it is Fredholm on level `0` (`A_m = A ∩ E_m`, so
     the restriction inherits the regularity of `T`). For a filler with `g(0) = 0` and `Dg(0)`
     sc-Fredholm, `Polyfold.IsFillerOf.proposition_3_5_sc`
     (`Chapter3/FredholmGermLinearizationSc.lean`): `T₀O = Dr(0)E` and `K₀ = ρ(0)F` are
     sc-subspaces and `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` is sc-Fredholm of index `ind Dg(0)` on
     every level. Only the direction "`Dg(0)` sc-Fredholm ⟹ `Tf(0)` sc-Fredholm" is proved (the one
     Proposition 3.52 uses), and it uses condition (3) of Definition 3.4 on level `0`, as the text
     states it: the higher levels of `Tf(0)` come from the regularity of `Dg(0)`, not from the
     filler. So Propositions 3.5 and 3.52 do not meet the difficulty recorded for Corollary 5.8
     (`Chapter5/Compactness.lean`, Chapter 5 item 21: condition (3) on level `1` does not follow
     from level `0` for a general operator). Remark, not formalized: at a zero, condition (3) on
     every level does follow from level `0` when `Dg(0)` is sc-Fredholm. For `y ∈ ker ρ(0) ∩ F_m`
     and `v ∈ ker Dr(0)` with `(1 − ρ(0))Dg(0)v = y`, write `ρ(0)Dg(0)v = Tf(0)t + c` with `c` in a
     complement of the range of `Tf(0)` spanned by smooth points (it exists since `Tf(0)` is
     sc-Fredholm); then `Dg(0)(v − t) = c + y ∈ F_m`, so `v − t ∈ E_m` (regularity of `Dg(0)`), so
     `t = −Dr(0)(v − t) ∈ E_m` and `v ∈ E_m`.
235. **Proposition 3.52 in sc form (round-trip items V3.46, V3.68; revises items 48 and 224).**
     `Polyfold.proposition_3_52_local_sc` (chart form, for conjugation data `d` of `g − s`) and
     `Polyfold.proposition_3_52_sc` (bundle form): in the strong bundle chart of Definition 3.11
     centred at a zero `x₀` of a section with an sc-Fredholm germ at `x₀`, `Dg(0) : E → F` is an
     sc-operator and sc-Fredholm, `T₀O = Dr(0)E` and `K₀ = ρ(0)F` are sc-subspaces, and
     `Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` (`ScOperator.restrict`, whose level-`0` map is
     `fillerRestrict`) is sc-Fredholm; on every level both are Fredholm of index
     `dim d.Pn − dim d.Q` for every conjugation `d`. The proof is the text's: `D(g − s)(0)`
     sc-Fredholm, `Dg(0)` by Proposition 1.10 (`proposition_1_10`, `proposition_1_10_index`),
     `Tf(x₀)` by Proposition 3.5 (item 234). Two steps the text leaves out. (a) "`D(g − s)(0)` is
     sc-Fredholm by Proposition 3.10": Proposition 3.10 is about the basic germ `h`; the conjugate
     `Dk(0) = Γ(0)⁻¹Dh(0)Dψ(0)` is sc-Fredholm by the criterion of item 233, because `Γ(0)`
     preserves the levels (the filtration condition of Definition 2.47 at the smooth point `0`),
     `Dh(0)` is regularizing (Propositions 3.10, 1.9) and `Dψ(0)⁻¹ = Dψ'(0)` is an sc-operator
     (`Polyfold.ConjugationData.scDeriv_isRegularizing`, `ConjugationData.scDeriv_isScFredholm`).
     (b) The sc-structures of `T₀O` and `K₀`: `Dr(0)` is an sc-operator projection (`r` sc-smooth,
     `0` smooth; Lemma 2.B), and `ρ(0)` maps `F_m` into `F_m` (Definition 2.47), is bounded there
     by the closed graph theorem and is a projection because `0 ∈ O`
     (`StrongRetr.isScSubspace_range_scDeriv_r`, `StrongRetr.isScSubspace_range_ρCLM`). No
     hypothesis beyond the text's was needed; tameness is not used. Not proved: the statement in
     every strong bundle chart around `x₀` and at a lift `z` of `φ(x₀)` in a non-centred chart (the
     blind statements of V3.46 and V3.96 quantify over all charts, with `D(f̂ ∘ r)(z)|_{T_zO}`);
     the chart independence of the linearization is known on level `0` only
     (`StrongBundle.linAt_chart_independence`).
236. **Theorem 3.19, "`f'(x₀)` is sc-Fredholm" (round-trip item V3.96, revises item 224).**
     `Polyfold.theorem_3_19_linearization_sc`: for an sc-Fredholm section and a zero `x₀` in good
     position, in the chart of Definition 3.53 centred at `x₀`, `Dg(0)` and
     `f'(x₀) = Tf(x₀) : T₀O → K₀` are sc-Fredholm operators with the indices of item 235, and
     `Tf(x₀)` is onto on every level (onto on level `0` by good position, then on every level by
     its regularity, `ScOperator.IsRegularizing.surjective`). The level-`0` statements
     (`theorem_3_19_linearization`, `theorem_3_19_linearization_index`) are unchanged. Of the gap of
     item 224 what remains is the chart independence of item 235 and the sc-Fredholm property of
     `f'(y)` at the nearby zeros `y` in the chart at `x₀` (Theorem 3.54, Proposition 6.2), which
     the text infers from the same proposition at `y`. (Both are now proved, item 239.)
237. **At a zero, condition (3) of a filler holds on every level when `Dg(0)` is sc-Fredholm (the
     remark of item 234, now formalized).** `Polyfold.IsFillerOf.filler_condition_three_sc`
     (`Chapter3/LinearizationChartsSc.lean`): for a filler `g` of `f` (a section of `K → O`) with
     `g(0) = 0` and `Dg(0)` an sc-Fredholm sc-operator, `ker Dr(0)` and `ker ρ(0)` are sc-subspaces
     (`StrongRetr.isScSubspace_ker_scDeriv_r`, `StrongRetr.isScSubspace_ker_ρCLM`: complements of
     the sc-projections `Dr(0)`, `ρ(0)`, Lemma 2.B) and `(1 − ρ(0))Dg(0)` restricts to an
     **sc-isomorphism** `ker Dr(0) → ker ρ(0)` between the induced sc-Banach spaces (`ScIso`, built
     by `Polyfold.ScIso.ofBijective` from bijectivity on every level). The elementwise statement is
     `IsFillerOf.mem_range_toBase_of_scDeriv_r_eq_zero` (`v ∈ ker Dr(0)`, `(1 − ρ(0))Dg(0)v ∈ F_m` ⟹
     `v ∈ E_m`), with item 234's proof; the complement of the range of `Tf(0)` spanned by smooth
     points is `Polyfold.ScOperator.exists_sub_mem_smooth` (for `T₀` Fredholm, every `w ∈ F₀` is
     `T₀e + c` with `c ∈ F_∞`; the density argument of item 233). The text states condition (3) on
     level `0` only (Definition 3.4); at a zero with `Dg(0)` sc-Fredholm this loses nothing. Away
     from the centre of the chart nothing is claimed (condition (3) is a condition at `0`).
238. **The converse of Proposition 3.5 in sc form holds with condition (3) on every level, and fails
     with condition (3) on level `0` only.** `Polyfold.IsFillerOf.proposition_3_5_sc_converse`: for
     a filler `g` with `g(0) = 0`, `Dg(0)` an sc-operator, `Tf(0) : T₀O → K₀`
     (`ScOperator.restrict`) sc-Fredholm, and the level-`m` maps of `(1 − ρ(0))Dg(0)|_{ker Dr(0)}`
     onto `ker ρ(0) ∩ F_m` for every `m`, `Dg(0)` is sc-Fredholm and every level map of `Dg(0)` is
     Fredholm with the index of `Tf(0)`. Proof: Fredholm on level `0` by Proposition 3.5;
     regularizing from the triangular form (for `Dg(0)e ∈ F_m` the `ker Dr(0)`-part `v = e − Dr(0)e`
     has `(1 − ρ(0))Dg(0)v = (1 − ρ(0))Dg(0)e ∈ F_m`, so `v ∈ E_m` by the hypothesis and the
     injectivity on level `0`; then `Tf(0)Dr(0)e ∈ F_m` and `Dr(0)e ∈ E_m` because `Tf(0)` is
     regularizing); the criterion of item 233. With item 237:
     `Polyfold.IsFillerOf.proposition_3_5_sc_iff` (`Dg(0)` sc-Fredholm ⟺ `Tf(0)` sc-Fredholm and
     condition (3) on every level). The hypothesis on the higher levels is needed. Counterexample
     (not formalized; it needs a weighted `ℓ²` sc-space and the spectral theory of the shift):
     `E = F` with `E_m = ℓ²` weighted by `2^{nm}`, `R ≡ 0` (so `O = {0}`, `K = {(0, 0)}`,
     `T₀O = K₀ = 0`, `Tf(0) : 0 → 0` sc-Fredholm), `g = 1 + λS` with `S` the forward shift and
     `0 < λ < 1`. Then `g` fills `f = 0` (condition (3) on level `0` is the invertibility of
     `1 + λS` on `ℓ²`), but on `E_m` the operator `S` is `2^m` times an isometry, so for `λ2^m > 1`
     the operator `1 + λS` is injective with range of codimension `1`: `Dg(0)` is not sc-Fredholm
     and condition (3) fails on level `m`. The text's Proposition 3.5 (2) is a level-`0` statement,
     and Propositions 3.52 and Theorem 3.19 use only the direction of item 234, so nothing in the
     text depends on the converse.
239. **The linearization of an sc-Fredholm section at a zero is sc-Fredholm in every strong bundle
     chart (round-trip items V3.46, V3.96; revises items 224, 235, 236).**
     `Polyfold.StrongBundle.linAt_isScFredholm`: for an sc-Fredholm section `f`, a zero `y` and
     **any** strong bundle chart `c` of `P` around `y`, at the level-`1` point `z` over `φ(y)`
     (smooth: `IsScFredholmSection.mem_smoothSet_of_isZeroAt`), `D(f̂ ∘ r)(z)` is an sc-operator,
     `T_zO = Dr(z)E` and `K_z = ρ(z)F` are sc-subspaces
     (`StrongRetr.isScSubspace_range_scDeriv_r_at`,
     `StrongRetr.isScSubspace_range_ρCLM_of_mem_smooth`: the arguments of item 235 at a smooth point
     instead of `0`), and `Lin(z) = D(f̂ ∘ r)(z)|_{T_zO} : T_zO → K_z` (`ScOperator.restrict`,
     level-`0` map `linAt`) is sc-Fredholm; every level map is Fredholm of index
     `dim d.Pn − dim d.Q` for every datum of Definition 3.11 at `y` and every conjugation `d` in it.
     This is the chart-intrinsic reading of Proposition 3.52 and of Theorem 3.19's "`f'(x₀)` is
     sc-Fredholm" (the "every chart" reading of the blind statements V3.46, V3.96, without their
     tameness hypothesis; the glue to the blind files, `K_z = {h | (z, h) ∈ K}` by
     `mem_rangeS_ρCLM_iff`, was not written). The proof is the transport the text leaves out:
     `Polyfold.linAt_chart_change_sc` realises the level-`0` conjugation of `linAt_chart_change` by
     bounded operators on the ambient spaces, `a = D(τ ∘ r)(z)` with inverse `a' = D(τ' ∘ r')(z')`
     on the tangent spaces and the fibre transition `γ = Γ(z)` with inverse `γ'` on the fibres,
     `D(f̂' ∘ r')(z') ∘ a = γ ∘ D(f̂ ∘ r)(z)`, and shows that they preserve the levels at smooth
     points: `a`, `a'` as derivatives of sc-smooth maps at smooth points, `γ` because the transition
     `Θ = Φ' ∘ Φ⁻¹` is sc⁰ on `[0]` (it maps `E_m ⊕ F_m` into `E'_m ⊕ F'_m`; neither `[1]` nor
     tameness is used). In the chart `c₁` of a germ datum at `y`, `Dg₁(0)` is sc-Fredholm and
     `Tf₁(0)` Fredholm (items 235, 48); `Lin(z)` is Fredholm on level `0` by the conjugation, and
     regularizing because `Lin(z)e ∈ F_m` gives `Dg₁(0)(ae) = γ Lin(z)e ∈ F₁_m`, so `ae ∈ E₁_m` and
     `e = a'(ae) ∈ E_m` (`Polyfold.StrongBundle.linAt_sc_of_germ`); then the criterion of item 233.
     Only the transition `c → c₁` and the base transition back are used. Corollaries:
     `Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex` (at a zero with
     `IsSurjLinOfIndex f y d`, `Lin(z)` is onto on every level and of index `d` on every level, in
     every chart) and `Polyfold.theorem_3_54_index_locally_constant_sc` (the sc form of
     `theorem_3_54_index_locally_constant`: near a zero `x₀` in good position, for an sc-Fredholm
     section with tame germ data, at every zero `y`, in every chart, `Lin(z)` is sc-Fredholm, onto
     on every level, of the same index `d`). With this the gap of item 224 is closed for the
     linearization at zeros: the sc-Fredholm property holds in every chart at every zero, including
     the zeros near `x₀` in the chart at `x₀`. Not proved: the local constancy of the index without
     good position (round-trip item V3.98 (b) in general) and Proposition 6.2 along paths (V3.98
     (a)).

**240–249: the index along the zero set (2026-11-01).**

240. **The Fredholm index is locally constant along the zero set without good position, for
     sections with tame germ data on an M-polyfold admitting bump functions (round-trip item
     V3.98 (b); revises the last sentence of item 239).**
     `Polyfold.index_locally_constant_of_admitsBumpFunctions` and
     `Polyfold.theorem_3_54_index_locally_constant_general` (`Chapter3/IndexLocallyConstant.lean`):
     let `X` admit sc-smooth bump functions (Definition 5.9) and `f` be an sc-Fredholm section with
     tame germ data (Definition 3.51), `f(x₀) = 0`. Then there are an open `V ∋ x₀` and `i ∈ ℤ` such
     that at every zero `y ∈ V` (in particular at `x₀`), in **every** strong bundle chart around
     `y`, `Lin(z) : T_zO → K_z` is Fredholm of index `i` (`StrongBundle.IsLinOfIndex`, the
     `IsSurjLinOfIndex` of item 170 without the surjectivity), and in the sc form sc-Fredholm of
     index `i` on every level (`linAt_isScFredholm`, item 239). Neither good position nor the
     surjectivity of `f'(x₀)` is assumed. Against the text: Theorem 3.54 and Proposition 6.2 are
     stated for an sc-Fredholm section of a tame strong bundle; here "tame" is read as tame germ
     data (Definition 3.51, items 190–199), and the bump functions are the hypothesis of §5.3
     (automatic for M-polyfolds built on sc-Hilbert spaces,
     `MPolyfold.admitsBumpFunctions_of_hilbert`); the auxiliary norm the construction uses exists
     for every strong bundle (`proposition_5_3_exists`). The blind statement V3.98 (b) assumes
     neither tameness nor bump functions; with them it is proved (the glue to the blind file's
     `ChartLinScFredholm`, `K_z = {h | (z, h) ∈ K}` by `mem_rangeS_ρCLM_iff`, is not written).
     V3.98 (a), Proposition 6.2 along sc-smooth paths, is not treated.
241. **The proof is the text's device for Proposition 6.2, and one family of sections suffices
     (items 100, 105–106 revisited).** At `x₀`, finitely many allowable sc⁺-sections `s₁, …, s_k`
     put the parametrized section `F(λ, y) = f(y) + Σ λᵢ sᵢ(y)` of Theorem 3.18 into general
     position at `(0, x₀)` (`exists_sections_isParamGP`,
     `isGeneralPositionGerm_paramSection_of_isParamGP`: the spanning sections of Lemma 5.11 for the
     surjectivity and the tilting sections for the kernel condition at the corner, the two points
     of items 105 (a) and 107 which the text's proof of Proposition 6.2 does not address); general
     position is good position in a tame chart (Lemma 5.26); Theorem 3.54 (1) and the dimension
     count (`theorem_3_54_index_locally_constant`, item 171) make the index of `F` constant, say
     `d`, along its solution set near `(0, x₀)`; at `(0, y)` with `f(y) = 0` the index of `F` is
     `k + ind f'(y)`, so `ind f'(y) = d − k` for every zero `y` near `x₀`. The `Λ₀`-dependence of
     item 106 is harmless here: it obstructs the surjectivity of `f'(y)` at the nearby zeros (all
     smooth vectors must lie in the range), while the index is read off from one family of
     sections chosen at `x₀`. Tameness enters only through the kernel condition of good position at
     the corner (the presentation of the partial quadrant of a tame chart), bump functions only
     through Lemma 5.11.
242. **The index of the parametrized section at `(0, y)` is `k + ind f'(y)`**
     (`Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex`): in the product chart
     `(r ↦ r) × φ₁` over the chart `c₁` of the germ datum at `y`, `T₀(ℝᵏ × O₁) = ℝᵏ × T₀O₁`
     (`ofProd_scDeriv_r`, `ofProd_mem_tangent`), the fibre over `(0, 0)` is `K₁`
     (`mem_K_ofProd_zero_iff`), and `Lin_F(0)(δa, δu) = Lin_f(0)δu + Σ δaᵢ ŝᵢ(0)`
     (`linAt_paramSection_zero`); for `M(a, u) = Lu + Ea` on `ℝᵏ × T` with `L`, `M` Fredholm,
     `ind M = ind L + k` (`Polyfold.fredholmIndex_eq_of_param`: `E ∘ pr₁` has finite rank,
     `ind (L ∘ pr₂) = ind L + ind pr₂` and `ind pr₂ = k`, `Polyfold.linIndex_snd`). The index in
     `c₁` is carried to every chart by `linAt_index_of_conjugationData`
     (`StrongBundle.isLinOfIndex_of_conjugationData`).
243. **With the text's hypotheses alone (no bump functions, no tame germ data) the local constancy
     of the index remains open; the exact missing step.** In the chart `c` at `x₀` with the filled
     version `g`, at a zero `z = φ(y)` near `0` (a smooth point): (i) `Dg(z) : E → F` is Fredholm
     of index `n − N` on level `0` — `Γ(z)Dg(z) = D(h + t)(ψ(z))Dψ(z)` with `t = Ψ_*(s)` sc⁺
     (`scDeriv_pushforward_at`, item 104) and Proposition 3.10, second statement, on level `0`
     (item 230) at `ψ(z) ∈ U'₁` small on level `0` (not formalized in this generality; the
     formalized instances live inside the good-position machinery, items 101, 170); (ii)
     `Lin(z) : T_zO → K_z` is Fredholm (the germ at `y`, item 239); (iii)
     `Dg(z) = [[Lin(z), B], [0, C(z)]]` for `E = T_zO ⊕ ker Dr(z)`, `F = K_z ⊕ ker ρ(z)`
     (`rho_scDeriv_comp_r` at `z`), so `C(z) = (1 − ρ(z))Dg(z)|_{ker Dr(z)} : ker Dr(z) → ker ρ(z)`
     is Fredholm with `ind Dg(z) = ind Lin(z) + ind C(z)`. Hence `ind f'(y) = ind f'(x₀)` **iff**
     `ind C(z) = 0`. Condition (3) of Definition 3.4 makes `C(0)` an isomorphism, at `z = 0` only;
     `z ↦ C(z)` (through `z ↦ Dg(z)`, `Dr(z)`, `ρ(z)`) is continuous in the strong operator
     topology only (`ScOneNotNormContinuous.lean`), and a strongly continuous family of Fredholm
     operators can change its index (on `ℓ²`, `S_t = 1` on the coordinates `< 1/t` and the shift
     on the coordinates `≥ 1/t` for `t > 0`, `S_0 = 1`: isometries of index `−1` converging
     strongly to the identity). Condition (2) of Definition 3.4 says that `z` is an isolated zero of
     `(1 − ρ(z))g` on the fibre `r⁻¹(z)`, whose linearization at `z` is `C(z)`; without an
     sc-structure on `C(z)` no implicit function theorem excludes `ind C(z) > 0`, and nothing
     excludes `ind C(z) < 0`. So the text's claim is proved under the hypotheses of its own proof
     (item 241); no counterexample is known either. In the dimension-jump example of item 188 —
     the retract `{(t, s e_t)}` (tangent dimension `2` for `t ≠ 0`, `1` at `0`) with fibres of rank
     `2` for `t ≠ 0` and `0` at `t = 0`, and the section `f(t, s e_t) = s e'_t` vanishing on the
     `t`-axis — `ind Lin` is `0` at `(t, 0)`, `t ≠ 0`, and `1` at `(0, 0)`; a filler at the centre
     would therefore need `ind C(t) = 1` at the zeros `(t, 0)`, `t ≠ 0`, and whether some filler
     with `g − s` basic exists there (the germ property at the centre) is the open point. Noted in
     passing: a section conjugate to a basic germ at `0` need not be an sc-Fredholm germ at the
     nearby zeros (`f(a, w) = w − aTw` on `ℝ ⊕ W`, `T` an sc-operator with `‖T‖_m ≈ 2^m`: a basic
     germ at `0`, but `Df(a, 0)` is not Fredholm on the levels `m` with `|a| 2^m ≥ 1`), so the
     germ property at every zero is a genuine constraint, not a consequence of the germ at `x₀`.
     *(2026-11-02: revisited in item 343 — under tame germ data the local constancy is the text's
     device with bump functions added, whose removal is a localization not done, and the example of
     item 188 is excluded by Theorem 3.54 (1); without tame germ data the question stays open.)*
244. **`IsLinOfIndex` versus `IsSurjLinOfIndex`.** `StrongBundle.IsLinOfIndex f y i` is the
     chart-intrinsic "`f'(y)` is Fredholm of index `i`" (every chart around `y`, every level-`1`
     point over `φ(y)`, every bounded `L : T_zO → K_z` with `L = Lin(z)`); `IsSurjLinOfIndex f y d`
     implies it (`IsSurjLinOfIndex.isLinOfIndex`), and for an sc-Fredholm section it holds with
     `i = dim Pn − dim Q` for every germ datum at `y` (`isLinOfIndex_of_conjugationData`). The
     level-`0` index is the sc-index on every level (item 239), which is how
     `theorem_3_54_index_locally_constant_general` states the sc form.

**250–259: more results of the round-trip audit moved into the project (2026-11-01).**

250. **Corollary 3.34 and Theorem 3.35, "`δ` is sc-smooth": one germ for all `k`, now in the
     project (round-trip items V3.31, V3.32; revises items 2 and 222).** `Polyfold.isSckGerm_of_levels`
     (`Chapter3/GermIFTSmooth.lean`, the audit's locality lemma): `f` is an sc^k-germ on `G'` as
     soon as for every `j` it is an sc^j-germ on some germ `G_j` with `G'_{m+j} ⊆ (G_j)_{m+j}` for
     all `m` — the `j`-th tangent germ of `f` on `G'` only involves the levels `≥ j` of `G'`;
     `isScSmoothGerm_of_levels` for every `k`. For a working-form contraction germ whose solution
     `δ` is sc^k on `germ s_k = (N(m + s_k) ∩ C̃)_m` for each `k` (`theorem_3_33_smooth`), the
     diagonal germ `V_m = N(m + t_m) ∩ C̃`, `t_m = Σ_{j ≤ m} s_j` (`ContractionGerm.germDiag`,
     `ContractionGerm.diagShift`), lies on level `m + j` in `germ s_j`, so `δ` is an sc-smooth germ
     on it (`ContractionGerm.isScSmoothGerm_germDiag`) and a solution germ there. Hence
     `Polyfold.corollary_3_34_isScSmoothGerm` (`C̃` quadrant-like) and
     `Polyfold.theorem_3_35_isScSmoothGerm` (`C̃` a partial quadrant): if the sc⁰-contraction germ
     is sc-smooth, its solution germ is sc^k for every `k` on **one** germ (`IsScSmoothGerm`), as the
     text says. With `s_k = 2^k − 1` (item 2) the diagonal shift is `t_m = 2^{m+1} − m − 2`: the
     germ shrinks fast with the level, which is harmless for a germ. So item 2's "**not** as 'sc^k
     for all `k` on one fixed sequence `(V_m)`', which the method does not give" is superseded:
     the method gives it after a diagonal re-indexing. What remains unproved is the stronger
     statement on one germ of the form `germ s` (a fixed shift), which nothing uses. The
     `k`-dependent theorems `theorem_3_33_smooth`, `corollary_3_34`, `theorem_3_35_smooth` are kept;
     their docstrings and the module docstrings of `GermIFT.lean`, `ContractionGerm.lean` and
     `TangentGerm.lean` now point to the one-germ statements.
251. **Theorem 3.35 in the text's form: any representative of the solution germ, hypotheses on `f`
     (round-trip items V3.31, V3.32).** `Polyfold.theorem_3_35_of_isSc0ContractionGerm`: for an
     sc⁰-contraction germ `f = w − B(a, w)` of Definition 3.28 on a quadrant-like `C̃` (in
     particular a finite-dimensional partial quadrant) and **any** `(V, δ)` with `δ` sc⁰ on `V`,
     `δ(0) = 0` and `f(a, δ(a)) = 0` on `V₀`: (1) if `f` is sc^k, `δ` is an sc^k-germ on some germ
     `V' ⊆ V`; (2) if `f` is sc-smooth, `δ` is an sc-smooth germ on one germ `V' ⊆ V`. This is the
     blind statement of V3.32 (with `ℝⁿ` generalized to a finite-dimensional `P`) and the "in
     particular" of V3.31. The project had only `theorem_3_33_of_isSc0ContractionGerm` (one sc^k
     representative exists). Supporting lemmas: `Polyfold.isSckGerm_contractionMap_iff` (`f` is
     sc^k iff `B` is: the text's hypotheses are on `f`, the project's working-form theorems on `B`)
     and `IsSc0ContractionGerm.exists_eq_sol` (a representative agrees with the constructed `sol`
     on `V₀ ∩ N₀ ∩ u` for an open `u ∋ 0`, by uniqueness of the fixed point in `O₀`; the condition
     `(a, δ(a)) ∈ U₀` of a solution germ is not needed for this).
252. **Lemma 3.31, "`f⁽¹⁾` is an sc⁰-contraction germ", holds in the sense of Definition 3.28
     (round-trip item V3.28; complements items 3 and 215).**
     `Polyfold.ContractionGerm.isSc0ContractionGerm_next`: if a working-form contraction germ `𝒞`
     also satisfies Definition 3.28 (`IsSc0ContractionGerm Ct 𝒞.G 𝒞.B`, e.g.
     `𝒞 = h.toContractionGerm`) and `B` is sc¹ with derivative `DB`, then `f⁽¹⁾ = next s` satisfies
     Definition 3.28 on its germ `nextG s`, for every `s`: an `ε`-contraction near `0` for every
     `ε > 0` on every level. The project's `ContractionGerm.next` (item 3) records only a
     `1/2`-contraction on explicit regions, which is all that the proof of Theorem 3.33 uses. On
     level `m`, the first component of `B⁽¹⁾` is Definition 3.28 for `B` on level `m + 1`; the second,
     `w ↦ DB(v, δ(v))(b, w)`, is an `ε`-contraction by Lemma 3.9 on level `m`
     (`IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le`, item 215), since `δ_{m+1}(v)` is small
     on level `m` for `v` small (continuity of `δ_m` at `0`). Taken from the audit's `A_to_B` of
     V3.28, which proved it for its blind `B⁽¹⁾` with its own copy of the level-`m` Lemma 3.9; the
     project's copy (item 215) is used here.

**260–269: germs versus the whole chart (2026-11-01).**

Found while taking up the open question of item 221 — does the difference between the text's
germs (Definitions 3.1–3.2, levels that may shrink with `m`) and the project's whole-chart data
separate sc-Fredholm sections? — in `Chapter3/GermVsChart.lean`.

260. **The example of item 221 is machine-checked: an sc-smooth germ with shrinking levels which
     is sc-smooth on no neighbourhood** (`Polyfold.exists_isScSmoothGerm_not_isScSmooth`). The
     function `f(x) = Σ_n c_n (x − a_n)^{n+1}|x − a_n|`, `a_n = 1/(n+2)`, `c_n = (4(n+2))^{−(n+2)}`
     (`GermVsChart.f`), is `C^k` on `U_k = (−1/(k+2), 1/(k+2))` for every `k`
     (`GermVsChart.contDiffOn_f`: the terms `n ≤ k` are `C^∞` on `U_k`, their singular points
     `a_n ≥ 1/(k+2)` lying outside, and the tail `n ≥ k+1` is `C^{k+2}` on `(−1, 1)` by a set
     version of `contDiff_tsum`, `GermVsChart.contDiffOn_tsum_of_isOpen`, with the bounds
     `|(c_n H_{n+1})^{(l)}| ≤ 2^{−(n+2)}`, `l ≤ n+1`), and `C^{n+2}` on no open set containing
     `a_n` (`GermVsChart.not_contDiffOn_f`; `(x−a)^k|x−a|` is `C^k` with `k`-th derivative
     `(k+1)!|x−a|`, so not `C^{k+1}` near `a`, `GermVsChart.not_contDiffOn_H`). In the constant
     scale `ℝ`, `f` is an sc-smooth germ on `(U_m)` (`GermVsChart.isScSmoothGerm_f`: sc^j on the
     open `U_j` by Proposition 1.19, hence an sc^j-germ on `ofSet U_j`, and the locality lemma
     `isScSmoothGerm_of_levels` of item 250 since `U_{m+j} ⊆ U_j`) but sc-smooth on no open
     `U ∋ 0` (`GermVsChart.not_isScSmooth_f`: sc^{n+2} on `U` gives `C^{n+2}` on `U` by
     Proposition 1.18, `IsSck.contDiffOn_base`, and `U` contains some `a_n`). Restricting a chart
     on level `0` never produces shrinking levels, so the text's germs are not the project's
     whole-chart data up to restriction, as item 221 said.
261. **Definition 3.11 in the text's germ reading** (`StrongBundle.IsScFredholmGermG`, with
     `Polyfold.IsFillingGerm` for Definitions 3.4/3.6 and `Polyfold.IsScPlusGerm` for "local
     sc⁺-section"). `IsFillingGerm`: `g` an sc-smooth germ on a germ of neighbourhoods `G` with
     `G₀ ⊆ U`; (1) `f̂ = g` on `O` near `0`; (2) `g(y) = ρ(r(y))g(y)` near `0` forces `y ∈ O`; (3) a
     derivative family `Dk` of the sc¹-germ `[1 − ρ(r(·))]g` on `G` whose `Dk(0)` restricts to a
     continuous linear equivalence `ker Dr(0) ≃ ker ρ(0)` (`Dk(0)` is unique,
     `IsSc1GermWith.eq_of_uniqueDiffWithinAt`). `IsScPlusGerm`: an sc-smooth germ into `F¹` on a
     germ inside `U`. The strong bundle isomorphism `Ψ : U ◁ F → U' ◁ F'` and the basic germ `h`
     are as in `IsConjugateToBasicGerm` (on the whole `U`): an isomorphism on a relatively open
     `U₀ ⊆ U` is the same thing after restricting the chart on level `0`
     (`StrongBundleChart.restrict`); only shrinking levels escape restriction. Cleaned from the
     audit's blind definitions (`RoundTrip/Blind/V3_13.lean`, `IsFillingB`, `IsScPlusGermB`;
     `V3_43.lean`, `IsFillingB`); the audit's `ConjBasicB` (standard quadrant, literal push-forward)
     is transport glue (item V3.13) and is not kept. Tameness of the chart is not imposed, as in
     `IsScFredholmGerm`.
262. **Project ⇒ text, and the reduction: the project's notion is exactly the germ reading with `g`
     and `s` sc-smooth on the whole `U`** (`StrongBundle.IsScFredholmGerm.isScFredholmGermG`,
     `IsFilledVersion.isFillingGerm` — the audit's `proj_to_parts`, `proj_to_B` — and
     `StrongBundle.isScFredholmGerm_iff_germG_wholeChart`). Text ⇒ project under the whole-chart
     hypothesis is `IsFillingGerm.isFilledVersion` (the audit's `B_to_proj`): `[1 − ρ(r(·))]g` is
     sc¹ on `U` by the chain rule (`fillDefect_isScSmooth`), and its linearization at `0` is the
     germ's `Dk(0)` by uniqueness. So for a section sc-smooth on `X` the two readings of Definition
     3.11 differ exactly in the regularity of the filling `g` and of the sc⁺-section `s` on
     `U ∩ E_m` away from the shrinking germ `G_m`, and in nothing else.
263. **For a trivial retraction the filling is harmless: the question is about `s` alone.**
     `Polyfold.isStrongBundleRetraction_id_of_relOpen` (the identity of `U ◁ F` is a strong bundle
     retraction for every relatively open `U`), `Polyfold.isFilledVersion_id` (for `R = id` a map
     sc-smooth on `U` is its own filled version: (1), (2) are trivial, `[1 − ρ(r(·))]g = 0`, both
     kernels of (3) are `0`), `Polyfold.exists_wholeChart_filledVersion_of_id`: for `R = id` and
     `f̂` sc-smooth on `U`, the text's data `(g̃, s, Ψ, h)` can be replaced by `(f̂, s, Ψ, h)` with
     the whole-chart filled version `f̂` (condition (1) gives `f̂ = g̃` near `0`, so `g̃ − s = f̂ − s`
     near `0`, `IsConjugateToBasicGerm.congr_nhds`). A section sc-smooth on `X` has `f̂` sc-smooth
     on `O = r(U)` (`IsScSmoothSection.isScSmoothRetractMap`), hence on `U` when `O = U`. For a
     general retraction the normal component `[1 − ρ(r(·))]g̃` of a germ filling may be irregular
     on `U ∩ E_m` outside `G_m`; the whole-chart candidate `f̂∘r + [1 − ρ(r(·))]L(· − r(·))`,
     `L = Dg̃(0)`, satisfies (1) and (3), but (2) (zeros of `[1 − ρ(r(·))]g` near `0` lie in `O`)
     does not follow from (3) without an inverse function theorem on level `0`, which the
     sc-calculus does not provide. So for non-trivial retractions the filling is a second place
     where the readings may differ (not formalized).
264. **The main question stays open; where the obstruction sits.** Question: for a section `f`
     sc-smooth on `X` (Definition 3.14 (1)), does `IsScFredholmGermG f x₀` imply
     `IsScFredholmGerm f x₀` (after changing the chart, `g`, `s`, `Ψ`, `h` as needed)? Settled in
     neither direction. The analysis (for `R = id`, item 263): with the whole-chart sc⁺-section
     `s := f̂(0) + Ds̃(0)` (the `1`-jet at `0` of the germ `s̃`; `Ds̃(0) : E → F¹` is an sc⁺-operator)
     and the text's conjugation, `Ψ₂(f̂ − s)∘ψ⁻¹ = h + T` near `0` with `T = Ψ₂(s̃ − s)∘ψ⁻¹` an
     sc⁺-germ, `T(0) = 0`, `DT(0) = 0`, and the `W`-component is `w − (B − T₂)`. On every level
     `m ≥ 1`, `T₂` is `C¹` from `G_m` to `W_m` (sc¹ into `W¹` is `C¹` from level `m` to level `m − 1`
     of `W¹`; Proposition 1.16 for germs, `GermLevels.lean`) with `D₂T₂(0) = 0`, so `B − T₂` is an
     `ε`-contraction near `0` on level `m`: the contraction normal form survives on the levels
     `≥ 1`. On level `0`, `T₂ : G₀ → W₁ ⊂ W₀` is merely continuous and `B − T₂` need not be
     Lipschitz-small in `W₀`; this is exactly why Theorem 3.38 raises the index by one
     (`theorem_3_38`, `corollary_3_39`: `(h + T)¹` is a basic germ on the shifted structure). Hence
     **trading the germ `s̃` for a whole-chart `s` costs one level**: `(f̂ − s)¹` is conjugate to a
     basic germ on `E¹`, `F¹` (`corollary_3_39_isConjugate` applied to `h`, `T`; not assembled in
     Lean), and what remains is a level-`0` statement — whether some whole-chart sc⁺ `s` makes
     `f̂ − s` conjugate to a basic germ on level `0` too. Lipschitz-smallness of `T₂` on level `0`
     is not a conjugation invariant (`ψ` is only a homeomorphism on level `0`), so neither a bridge
     nor a counter-example follows from it. Whole-chart data force nothing visible beyond
     "`f̂ − s` is sc-smooth on `U`", which is automatic for `s` whole-chart and `f` sc-smooth on
     `X`: no invariant separating the two readings was found. In finite dimensions (constant
     scales) the readings agree (`s ≡ f̂(0)`, `Ψ = id`, `h = f̂ − f̂(0)` with `W = 0` is a basic germ),
     so a separating example, if there is one, is infinite-dimensional and must defeat every
     choice of `s`, `Ψ`, `h`. Precise open problem: *is every sc-smooth germ `k : O(C, 0) → F`
     with `k = s̃ + Ψ⁻¹hψ` near `0` (`s̃` an sc⁺-germ, `h` basic) also of the form `s + Ψ'⁻¹h'ψ'`
     with `s` sc⁺ on a fixed relatively open neighbourhood on all levels?* *(2026-11-01: phase 2
     switched the canonical notions and theorems to the germ reading, the whole-chart ones kept as
     `…WholeChart` (items 330–334); the question stays open but no theorem depends on the answer.)*
265. **Downstream: the text's theorems under the germ reading, and what the project's proofs use
     of the whole chart.** The uses of `IsFilledVersion.isScSmooth` and of the whole-`U`
     sc⁺-section `s` in the consumers of `IsScFredholmGerm` are of three kinds: (a) at the centre
     `0` only — `Dg(0)`, `D(g − s)(0)` (`FredholmGermLinearization.lean`,
     `FredholmGermLinearizationSc.lean`, `FredholmGermIndex.lean`, `GoodPositionGerm.lean`:
     `hfill.isScSmooth` feeds Proposition 3.5 and the sc-Fredholm criterion at `0`); (b)
     continuity or sc⁰ of `g`, `g − s` on level `0` near `0` (`SectionCompactness.lean`,
     `Chapter5/Compactness.lean`); (c) sc¹ of `g` at nearby zeros `z ∈ U₁` of the same chart
     (`linAt_eq_scDeriv … hfill.isScSmooth.isSc1 hzO` in `GlobalIFTIndex.lean`,
     `LinearizationCharts.lean`, `TameGerms.lean`). Germ data supply (a) and (b) directly (on
     `G₀`, `G₁`) and (c) for `z ∈ G₁`; whether the neighbourhoods of `0` in which (c) is invoked can
     be taken inside `G₁` is to be checked site by site in phase 2 (they are neighbourhoods of `0`
     on level `1` or level `0`, never all of `U`). Theorem 3.15 (`theorem_3_15`): the absorption
     `(g + t̃, s + t̃)`, `t̃ = ŝ∘r` whole-chart since `s ∈ Γ⁺(P)` is global; the same proof gives
     `IsScFredholmGermG` for `f + s` (not written). Theorems 3.12/3.13: local compactness from the
     basic germ near `0` and the regularizing property, with (b) and conditions (1), (2) near `0`
     — germ data suffice. Proposition 3.52 and the linearization clause of Theorem 3.19: (a).
     Theorems 3.19, 3.54, 3.56, 3.57 (`GlobalIFTTheorems.lean`, `GlobalIFTIndex.lean`,
     `IndexLocallyConstant.lean`): the germ IFT for `h` (already on germs) plus (a)–(c). No step of
     the project's proofs uses the regularity of `g` or `s` on `U ∩ E_m` away from a neighbourhood
     of `0`, so the text's theorems are expected to survive the germ reading; what changes is the
     hypothesis class of Definition 3.14 (larger under the germ reading) and the conclusions of
     Theorems 3.15, 3.18 (weaker), as item 221 says.
266. **Phase-2 estimate (porting the project to the germ reading, should no bridge be found).**
     (i) Replace `IsScFredholmGerm` by `IsScFredholmGermG` in `IsScFredholmSection` and in the tame
     variant `IsScFredholmGermTame` (`TameGerms.lean`); (ii) Theorem 3.15
     (`IsScFredholmGerm.sectionAdd`): re-prove for `IsFillingGerm`, `IsScPlusGerm` (a germ plus a
     whole-chart map is a germ on the same `G`; Lemma 3.17 for germs: (1)–(3) are near `0` and
     `[1 − ρ(r(·))](g + t̃) = [1 − ρ(r(·))]g` on `G`; about 150 lines); (iii) the consumers of item
     265, about twenty sites in eight files, each `hfill.isScSmooth` becoming "sc-smooth germ on
     `G`" with `G₀`, `G₁` in place of `U`, `U₁`, and the nearby-zero arguments (c) restricted to
     `G₁`; the lemmas `linAt_eq_scDeriv`, `IsFillerOf.proposition_3_5` and the linearization
     files need germ versions (the derivative calculus for germs of `Germ.lean`, `GermLevels.lean`
     is available); (iv) Chapter 5 follows (iii) through `theorem_3_15` and the germ data at zeros.
     Rough total: three to five days of Lean. Until then the honest state is the present one:
     project ⇒ text proved, text ⇒ project reduced to the open item 264, and the formal theorems
     narrower in their hypotheses than the text's by exactly the whole-chart regularity of `g`
     and `s` (item 262).

**270–299: Definition 3.11 on germs (phase 2, 2026-11-01).**

Found while restating Definition 3.11 in the text's germ reading (item 261): the filling `g` and
the sc⁺-section `s` are sc-smooth germs on germs `G_g`, `G_s` of neighbourhoods of `0` in `C`,
the strong bundle isomorphism `Ψ` and the basic germ `h` are kept.

270. **The arithmetic of sc-smooth germs is the one of sc-operators composed with pairings**
     (`IsSc1GermWith.add`, `neg`, `sub`, `smul`, `operator_comp`, `IsSckGerm.add`, `neg`, `sub`,
     `smul`, `IsScSmoothGerm.add`, `neg`, `sub`, `smul`, `operator_comp`, the `_inter` versions on
     `G₁ ∩ G₂`, `Chapter3/GermCalculus.lean`). The text forms `g + s`, `g − s` and `[1 − ρ(r(y))]g(y)`
     for germs without comment. Proved: for sc¹-germs with derivative families `Df`, `Dg` on `G`,
     `f + g` is an sc¹-germ with the family `Df + Dg` (likewise `−Df`, `Df − Dg`, `c • Df`,
     `T ∘ Df` for an sc-operator `T`), and sc^k, sc-smooth follow; for germs on two germs `G₁`,
     `G₂` the sum lives on `G₁ ∩ G₂` (`ScNbhdGerm.inter`). The derivative families are the
     explicit ones; any other family agrees with them on `G₁` (`IsSc1GermWith.congr_deriv` in one
     direction, `eq_of_uniqueDiffWithinAt` in the other). The sc^k and sc-smooth versions need
     `C` quadrant-like, as `IsSckGerm.congr` does; the sc¹ versions with families need nothing.
     Two small sc-operators were added for this (`ScOperator.negOp`, `ScOperator.smulOp`); the
     sum operator is `ScOperator.addOp` of `Chapter1/LevelsWeak.lean`.
271. **Composition with a whole-chart map needs the chain rule with the outer map on a set, and that
     chain rule holds with no base-point condition** (`IsSc1With.comp_germ`, `IsSck.comp_germ`,
     `IsScSmooth.comp_germ`, `IsSc1With.hasFDerivWithinAt_comp_germ`; the inner version
     `IsSckGerm.comp_preimage`, `IsScSmoothGerm.comp_preimage`, `IsSc1GermWith.comp_preimage`).
     The text applies the whole-chart maps `R`, `Ψ`, `r`, `ψ⁻¹` to germs ("the usual
     calculus"). The germ chain rule of `Germ.lean` composes two germs *at `0`*, but `R` and
     `Ψ` are applied at `(r(y), g(y))` and `(u, k(u))`, which is `0` only when `g(0) = 0` and
     `0 ∈ O` — and `IsFillingGerm` assumes neither. Rather than translating, the chain rule is
     re-proved with the outer map `φ` sc¹ on an sc-domain `V` (its level sets `V_m`) and the inner
     map an sc¹-germ `f` on `G` with `f(G₀) ⊆ V`: `φ ∘ f` is an sc¹-germ on `G` with the family
     `Dφ(f(x)) ∘ Df(x)` at every `x ∈ G₁`, the proof being that of
     `IsSc1GermWith.hasFDerivWithinAt_comp` verbatim with `V_m` for the outer germ. The inner
     version (`g ∘ ψ`, `ψ` whole-chart with `ψ(0) = 0`) is the germ chain rule on the germ
     `ofSet V ∩ ψ⁻¹(G)` (`ScNbhdGerm.preimage`), with the family `Dg(ψ(x)) ∘ Dψ(x)`. The pairing
     `y ↦ (y, f(y))` is `IsSckGerm.pair_id`, `IsSc1GermWith.pair_id` (family `(1, Df(x))`).
272. **The fill defect `[1 − ρ(r(·))]g` of a germ is a germ, with the derivative family
     `Dg(x) − D(R₂)(r(x), g(x)) ∘ (Dr(x), Dg(x))`; at `0` this is `(1 − ρ(0))Dg(0)`**
     (`fillDefect_isScSmoothGerm`, `fillDefect_isSc1GermWith`, `fillDefectDeriv`,
     `fillDefectDeriv_zero`, `fillDefect_deriv_zero_eq` in `GermCalculus.lean`;
     `fillDefectDeriv_zero_eq`, `fillDefect_deriv_zero_eq_rho`, `IsFillingGerm.exists_kerEquiv`
     in `Chapter3/GermCalculusParam.lean`). Condition (3) of Definition 3.4 presupposes that
     `y ↦ [1 − ρ(r(y))]g(y)` is sc¹ for a germ `g` (item 261 took a derivative family `Dk` as part
     of `IsFillingGerm`). Proved: for `g` an sc-smooth germ on `G` with `G₀ ⊆ U` the fill defect
     is an sc-smooth germ on the same `G` (it is `g − R₂ ∘ (r, g)`, items 270–271: `r` is a germ
     on `G` by restriction of the whole-chart `r`, `R₂ = pr_F ∘ R` is sc-smooth on `U ⊕ F`), with
     the explicit family above; every derivative family `Dk` of the fill defect on `G` has
     `Dk(0) = fillDefectDeriv … 0` (uniqueness at `0`), and when `g(0) = 0`, `0 ∈ O`, this is
     `Dg(0) − ρ(0)Dg(0)` by `StrongRetr.scDeriv_fiber_zero` — the germ form of
     `IsFillerOf.scDeriv_sub_eq` — so condition (3) reads "`(1 − ρ(0))Dg(0)` restricts to an
     isomorphism `ker Dr(0) → ker ρ(0)`" for any derivative family `Dg` of `g` on any germ
     (`IsFillingGerm.exists_kerEquiv`, the germ form of `IsFillerOf.exists_kerEquiv`). The
     `ρ(0)`-form lives in the higher file because `scDeriv_fiber_zero` does
     (`FillerLinearization.lean`), which `GermCalculus.lean` must stay below. The germ forms of
     `deriv_comp_r_eq_zero` (`(1 − ρ(0))Dg(0)Dr(0) = 0`, for `f̂` a section of `K → O`:
     `IsFillingGerm.deriv_comp_r_eq_zero`, linearizing `[1 − ρ(r(·))]g ∘ r = 0` near `0` along
     the germ `r⁻¹(G₁)` of item 271) and of **Proposition 3.5** (`IsFillingGerm.proposition_3_5`:
     `Dg(0)|_{Dr(0)E} : Dr(0)E → ρ(0)F` is surjective, Fredholm, iff `Dg(0)` is, with the same
     index, for any derivative family `Dg` of `g` on any germ `G₁ ⊆ U`) are the whole-chart proofs
     with `fillDefect_deriv_zero_eq_rho` in place of `scDeriv_sub_eq`.
273. **Lemma 3.17 holds for germs: the filling germ `g` of `f̂` and a section `ŝ` of `K → O` give the
     filling germ `g + ŝ∘r` of `f̂ + ŝ`, on the same germ `G` with the same `Dk`**
     (`IsFillingGerm.add_section` for `ŝ` sc-smooth on `U`, as in Theorem 3.15;
     `IsFillingGerm.add_section_germ` for `ŝ` itself an sc-smooth germ on a germ `G_s`, the filling
     then on `G ∩ r⁻¹(G_s)`). The text's proof (conditions (1), (2) from Lemma 3.16, and
     `[1 − ρ(r(y))](g(y) + ŝ(r(y))) = [1 − ρ(r(y))]g(y)`) goes through unchanged: the identity holds
     on `U`, hence on `G₀`, so the derivative family `Dk` of the fill defect of `g` is one of the fill
     defect of `g + ŝ∘r` (`IsSc1GermWith.congr`), and `ŝ∘r` is a germ on `G` by item 271. In the
     germ-section version the identity needs `(x, ŝ(x)) ∈ K` only for `x ∈ O ∩ (G_s)₀`, and
     condition (2) near `0` uses that `(G ∩ r⁻¹(G_s))₀` is a neighbourhood of `0` in `U`; this is
     the germ form of Lemma 3.17 that item 279 left open, and the sc⁺-germ `ŝ₁∘r + t₀` of
     `IsScFredholmGerm.sectionAdd` is `IsScSmoothGerm.add_inter` with `comp_preimage` (the lemmas
     are generic in the target scale, so they apply with `F¹`).
274. **The push-forward of a germ by a strong bundle isomorphism is a germ on `ψ'⁻¹(G)`, with
     `D(Ψ_*k)(0) = Γ(0) Dk(0) Dψ'(0)`; and the product germ `ℝⁿ × G` carries the filling of
     Theorem 3.18** (`IsStrongBundleMap.fiber_comp_isScSmoothGerm`, `fiber_comp_isSc1GermWith`,
     `fiberCompDeriv`, `IsStrongBundleMap.pushforward_isScSmoothGerm`, `pushforward_isSc1GermWith`,
     `pushforwardDeriv`, `pushforwardDeriv_zero` in `GermCalculus.lean`;
     `IsStrongBundleIso.pullGerm`, `IsStrongBundleIso.pushforward_isScSmoothGerm`,
     `pushforward_isSc1GermWith`, `pushforwardDeriv_zero`, `fiberCompDeriv_zero_eq`,
     `pushforwardDeriv_zero_eq`, `ScNbhdGerm.univProd`, `IsQuadrantLike.univ_prod`,
     `IsSckGerm.univProd`, `IsScSmoothGerm.univProd`, `IsSc1GermWith.univProd`,
     `PullbackChartData.ofProd_isFillingGerm` in `GermCalculusParam.lean`). Definition 3.11 forms
     `Ψ_*(g) = Ψ ∘ (u, g(u)) ∘ ψ⁻¹` for a germ `g` and Theorem 3.18 regards `(a, u) ↦ g(u)` as a
     filling in the product chart, both without comment. Proved: for `k` an sc-smooth germ on
     `G ⊆ U`, `u ↦ (Ψ(u, k(u)))₂` is an sc-smooth germ on `G` (item 271 with `pr_{F'} ∘ Ψ`) and
     the `pushforward` of `GoodPositionGerm.lean` is an sc-smooth germ on the germ `ψ'⁻¹(G) ⊆ U'`
     (`pullGerm`, the preimage germ along the whole-chart `ψ' = ψ⁻¹`, `ψ'(0) = 0` from
     `ψ(0) = 0`), with the family `D[(Ψ(·, k(·)))₂](ψ'(x)) ∘ Dψ'(x)` and, for `k(0) = 0`, the value
     `Γ(0) ∘ Dk(0) ∘ Dψ'(0)` at `0` (`Γ(0) = fiberCLM`, by `IsStrongBundleMap.scDeriv_fiber_zero`),
     the form of `IsStrongBundleIso.pushforward_linearization` with `Dk(0)` for `scDeriv U g 0`
     and `Dψ'(0) = scDeriv U' ψ' 0` for `S.symm`. This is the "push-forward of a germ" that item
     277 took as a hypothesis; the sc⁺-version with `Ψ[1] = shiftFiber Ψ` (sc-smooth on `U ⊕ F¹`,
     `isScSmooth_one`) is the same two lemmas in the scale `E ⊕ F¹` and is not written out. For
     Theorem 3.18, the germ `Λ × G` in `Λ ⊕ E` (constant structure on `Λ`) with levels
     `Λ × G_m` is a germ around `0` in `Λ × C`, `(a, u) ↦ g(u)` is a germ on it (the germ chain rule
     with the sc-operator `pr₂`, family `Dg(u) ∘ pr₂`), and a filling germ of `f̂` in a chart `c`
     gives the filling germ `(a, u) ↦ g(u)` of `(a, u) ↦ f̂(u)` in the product chart
     `(r ↦ r − r₀) × φ` of `ofProd_isFillerOf`, on `ℝⁿ × G`: the fill defect in the product chart
     is the pull-back along `pr₂` of the one of `c` on `ℝⁿ × U` (`r(a, u) = (a, r(u))`), so its
     derivative family is `Dk(u) ∘ pr₂` and condition (3) is the kernel identification
     `ker D(1 × r)(0) = 0 × ker Dr(0)`, `ρ'(0) = ρ(0)` of the whole-chart proof, without the
     uniqueness argument that proof needs. `GermCalculus.lean` imports only `GermFilling`,
     `GermLevels` and Chapter 1–2 files (importable by `StrongBundleSections` and
     `FillerLinearization`); `GermCalculusParam.lean` imports `ParamPerturbation` and
     `GoodPositionGerm`.
275. **A basic germ restricts to every smaller germ; the contraction field needs no condition, the
     smoothness field uses the quadrant** (`IsSc0ContractionGerm.mono`, `IsBasicGerm.mono`,
     `IsBasicGerm.inter`, `ScNbhdGerm.exists_ball_paramProd`, `Chapter3/BasicGermShrink.lean`).
     Definitions 3.7 and 3.28 are stated on "a germ"; the text uses without comment that a basic
     germ stays basic on a smaller germ (same `h`, same `B`). Field by field: `h(0) = 0` and
     `P∘h = w − B` restrict trivially; Definition 3.28 asks that the points `(a, w)`, `a ∈ C̃`,
     `|a|, |w|_m < r`, lie in `U_m` — on a smaller germ this holds after shrinking `r`, since every
     level of a germ is a relatively open neighbourhood of `0` in `C̃ ⊕ W_m`, so it passes to
     **every** sub-germ; the sc-smoothness of `h` passes by `IsScSmoothGerm.mono`, which uses the
     uniqueness of derivatives, i.e. `C̃` quadrant-like. That is a sufficient condition (not shown
     necessary) and costs nothing in Definition 3.11, where `C̃` is a partial quadrant
     (`ConjugationData.quadrant`).
276. **The G″ design: the conjugation of Definition 3.11 can always be taken with the basic germ on
     the germ of the points that `ψ'` maps into `G_g ∩ G_s`** (`ConjugationData.shrinkGerm`,
     `ConjugationData.shrink`, `basic_shrinkGerm`, `levelMap_mem_of_mem_shrinkGerm`,
     `levelMap_mem_inter_of_mem_shrinkGerm`, `mem_of_levelMap_base_mem`,
     `IsConjugateToBasicGerm.exists_conjugationData_mapsToGerm`). The text does not relate the germ
     `G` of the basic germ to `G_g`, `G_s`, and nothing forces `ψ'(G_m) ⊆ (G_g)_m`. For conjugation
     data `d` and a germ `G'` on the `E`-side, `G″_m = {x ∈ G_m | ψ'_m(x) ∈ G'_m}` is the preimage
     germ `G.preimage G'` along the sc⁰-germ `ψ'|_G` (`baseInv_isSc0Germ`: `ψ'` is sc-smooth on the
     whole `U'` because `Ψ` is an isomorphism of the whole local bundles; `ψ'(0) = 0` needs
     `0 ∈ U`); `G ∩ G.preimage G' = G.preimage G'` (`ScNbhdGerm.inter_preimage_U`), so no
     intersection is needed. `d.shrink` has the same `Ψ`, `h`, `B` and conjugation identity, only
     the germ changes, and `x ∈ G″_m ⇒ ψ'_m(x) ∈ (G_g)_m ∩ (G_s)_m` for `G' = G_g ∩ G_s`; read on the
     `E`-side, `u ∈ U_m` with `ψ_m(u) ∈ G″_m` lies in `G'_m`. `BasicGermShrink.lean` imports only
     `FredholmGermIndex` (importable by `GoodPositionGerm` and `GlobalIFT`).
277. **Corollary 3.41 on `G″`: the nearby solutions are points where `g` and `s` are sc¹**
     (`ConjugationData.corollary_3_41_of_subset_shrinkGerm`, `corollary_3_41_shrink`,
     `exists_stabilityData_shrinkGerm`, `Chapter3/BasicGermShrinkIFT.lean`). For data `𝒮` of
     Theorem 3.38 with `𝒮.G ⊆ G″` and any basic germ `f` on `𝒮.G` (in the consumers
     `f = h + (t_{ℝᴺ}, 0)`, item 85) with `D(f + s)(0)` onto, every zero `x` with `|x|₀ < r` is
     `ι x₁`, `x₁ ∈ 𝒮.G₁`, `D(f + s)(x₁)` onto Fredholm of index `n − N`, **and `ψ'₁(x₁) ∈ G'₁`,
     `ι ψ'₁(x₁) = ψ'(x)`**. Why it works: `corollary_3_41` takes `x₁` to be the lift of Theorem 3.40,
     which lies in the basic germ's `G₁` because it is small on level `1` and the contraction field
     puts a level-`1` ball inside `G₁` (item 275); on `G″` that ball is inside `G″₁`. The radius `r`
     is the one of the data on `G″`. The data on `G″` exist when the push-forward `t` of the
     sc⁺-section is an sc-smooth germ on `G″` (taken as hypothesis in
     `exists_stabilityData_shrinkGerm`; the push-forward of a germ, the germ form of
     `ConjugationData.pushPlus`, is germ calculus, not proved here).
278. **Verdict on the consumers: the G″ design covers every site checked.** (a)
     `StabilityData.corollary_3_41`, `exists_surjective_Dfs'_graph` (`GlobalIFTFull.lean`): the
     produced `x₁` lies in `𝒮.G₁` (item 277). (b) `theorem_3_54_chart_kernel`
     (`GlobalIFTNearbyKernel.lean`): it produces `z₀₁ ∈ U₁` with `ψ₁(z₀₁) = x₁ ∈ 𝒮.G₁`; with
     `ψ'(𝒮.G_m) ⊆ G'_m` the point `z₀₁` lies in `G'₁` — machine-checked by applying the theorem as
     stated in a scratch file (not kept; the argument `z₀₁ = ψ'₁(ψ₁(z₀₁)) = ψ'₁(x₁)` is
     `mem_of_levelMap_base_mem` in the project). (c) The curve of `GlobalIFTNearbyOnto.lean`,
     `u(μ) = ψ'₁(ι glue₀(cv(μ)))` with `glue₀(cv(μ)) ∈ 𝒮.G₂`: `u(μ) ∈ G'₁` for every `μ`
     (`levelMap_inclK_mem_of_subset_shrinkGerm`), so `g` is differentiated within `(G_g)₁` along
     it (checked by reading, not run). (d) `scDeriv_pushforward_at` (`GlobalIFTNearbyGraph.lean`),
     applied at `u₁ = z₀₁`: as (b). (e) The level-`1` points of `GlobalIFTIndex.lean`,
     `GlobalIFTNearbySurj.lean` and `isGoodPositionAt_of_chart_dense` are the `z₀₁` of (b) (the
     lift of a zero is unique). No site differentiates `g` at a level-`1` point other than the lift
     of a nearby zero; the level-`0` identities (filler (1), (2), the conjugation) hold on
     neighbourhoods of `0` and are unaffected. The design needs: `𝒮` built on `G″` (`𝒮.G = G″`),
     and the level-`0` neighbourhood `N₂` with `ψ(U ∩ N₂) ⊆ G″₀` (fine: `G″₀` is relatively open
     and `ψ` continuous). Its limit: a point small on level `0` only is not in `G″₁` in general; the
     design relies on the lifts of zeros being small on level `1` (Theorem 3.40).
279. **Theorem 3.15 in the germ reading: the conjugation part is a congruence and keeps `G″`; the
     rest is germ calculus** (`ConjugationData.congr`, `ConjugationData.shrinkGerm_congr`).
     Conjugation data of `k` are conjugation data of every `k'` equal to `k` on `U` near `0`, with the
     same `Ψ`, `h`, `B` and the same germ `G″`. In `IsScFredholmGerm.sectionAdd`,
     `(g + ŝ∘r) − (ŝ₁∘r + t₀) = g − t₀`; the new filling is a germ on `G_g` and the new sc⁺-section a
     germ on `G_s` (`ŝ∘r` is whole-chart), so the same `G″` serves. Not proved here: that
     `g + ŝ∘r` is a filling germ and `ŝ₁∘r + t₀` an sc⁺-germ (addition of germs and the germ form of
     Lemma 3.17).
280. **Definition 3.53 in the germ reading is a condition on the operator `Dg(0)`, and `Dg(0)` of a
     germ is the same for every germ and every derivative family** (`IsGoodPositionAtGerm`,
     `isGoodPositionAt_iff_germ`, `IsGoodPositionAt.isGoodPositionAtGerm`,
     `IsSc1GermWith.deriv_zero_eq`, `IsSc1GermWith.deriv_zero_eq_scDeriv`,
     `IsGoodPositionAtGerm.of_isSc1GermWith`, `Chapter3/GoodPositionGermG.lean`). The project's
     `IsGoodPositionAt hU hR h0 g` reads `scDeriv U g 0`, which for a filling germ `g` that is not
     sc¹ on `U` is the junk value of the chosen derivative; the text's `f'(x)` is defined through the
     filler at the centre only. The germ form takes the operator `Dg₀ : E₀ → F₀` as parameter
     (conditions (1), (2) verbatim with `Dg₀` for `scDeriv U g 0`); the project's notion is the case
     `Dg₀ = scDeriv U g 0` (an `Iff`, both fields unchanged). Proved: two derivative families of `g` on
     two germs agree at `0` (uniqueness at `0` within `(G₁ ∩ G₂)₁`, `C` quadrant-like), and equal
     `scDeriv U g 0` when `g` is sc¹ on `U`; so "good position at `Dg(0)` for some family on some
     germ" and "for every family on every germ" agree, and the choice of `Dg` is harmless.
281. **The kernel of the linearization and the linear part of Theorem 3.54 hold for filling germs
     with the whole-chart proofs** (`IsFillingGerm.ker_deriv_le_range`,
     `IsFillingGerm.map_ker_fillerRestrict`, `theorem_3_54_linear_germ`,
     `theorem_3_54_linear_of_isTameWith_germ`). The text's "`ker Tf̃(0) ⊕ {0} = ker Dg(0)` by the
     properties of the filler" and "hence, by Proposition 3.5, `Dg(0)` is surjective" use the filler
     at `0` only. Proved, for a filling germ `g` and any derivative family `Dg` on a germ `G₁ ⊆ U`:
     `ker Dg(0) ⊆ T₀O`, `ker Tf̃(0) = ker Dg(0)`, and, with the germ in good position at `Dg(0)` and
     `(1 − Dr(0))E ⊆ E₀`, `Dg(0)` onto and `ker Dg(0)` in good position to `C` in `E`. The proofs are
     the old ones with the germ forms of condition (3) and of `ρ(0)Dg(0)Dr(0) = Dg(0)Dr(0)` and
     Proposition 3.5 (item 272) in place of the `IsFillerOf` lemmas; `G₁ ⊆ U` is used only for the
     latter. `r` stays whole-chart, so `scDeriv U (r R) 0` is a genuine derivative.
282. **The push-forward step of Theorem 3.54 holds for a filling germ; its one input from
     Proposition 3.52 is the Fredholm property of `Dg(0)`** (`IsStrongBundleIso.exists_fiber_base_equiv`,
     `IsStrongBundleIso.pushforward_linearization_germ`, `pushforward_surjective_germ`,
     `pushforward_ker_isInGoodPosition_germ`, `pushforward_isFredholm_germ`,
     `theorem_3_54_pushforward_germ`). Proved: for `g` an sc-smooth germ on `G₁ ⊆ U` with a family
     `Dg`, `g(0) = 0`, and any strong bundle isomorphism `Ψ` with `ψ(0) = 0`, `Ψ_*(g) = h + t` is an
     sc-smooth germ on `ψ'⁻¹(G₁)` with the family `pushforwardDeriv` (item 274), vanishes at `0`, and
     `D(Ψ_*g)(0) = Γ(0) ∘ Dg(0) ∘ Dψ(0)⁻¹` with `Γ(0)`, `Dψ(0)` isomorphisms (`Dψ(0)` carries `C` onto
     `C'`); hence surjectivity, the Fredholm property and (for `ker Dg(0)` finite-dimensional, Lemma
     3.45) good position of the kernel pass to `h + t`. `theorem_3_54_pushforward_germ` takes
     `IsFredholm (Dg 0)` as hypothesis instead of the data `s`, conjugation of the old statement: in
     the germ reading that is Proposition 3.52 for germs (`proposition_3_52_local_germ`, item 289),
     written at the same time in a file this one does not import; combining them is a one-line
     application. The isomorphisms are whole-chart objects (`Ψ` is an isomorphism of the whole local
     bundles), so no germ calculus is needed for them.
283. **Definition 3.53 for sections in the germ reading; project ⇒ text, and the same reduction as
     for Definition 3.11** (`StrongBundle.IsGoodPositionGermG`,
     `StrongBundle.IsGoodPositionGermG.isScFredholmGermG`,
     `StrongBundle.IsGoodPositionGerm.isGoodPositionGermG`,
     `StrongBundle.IsGoodPositionGermG.forall_isGoodPositionAtGerm`,
     `StrongBundle.isGoodPositionGerm_iff_germG_wholeChart`, `theorem_3_54_pushforward_section_germ`).
     `IsGoodPositionGermG f x₀` is the data of `IsScFredholmGermG` (item 261) and a derivative family
     `Dg` of `g` on a germ `G ⊆ U` with the germ in good position at `Dg(0)`. Proved: it implies
     `IsScFredholmGermG`; the project's `IsGoodPositionGerm` implies it (germ `ofSet U`,
     `Dg = scDeriv U g`); the project's notion is exactly the germ reading with `g`, `s` sc-smooth on
     the whole `U` (the analogue of item 262); and the `∀`-form (good position at `Dg(0)` for every
     family on every germ) follows by item 280, so the definition is satisfiable whenever the old
     one is and is not weakened by the existential. The section form of Theorem 3.54's push-forward
     step states the Fredholm and kernel parts under `IsFredholm (Dg 0) → …` (item 282).
284. **The bridge `Lin(z) = Dg(z)` for a germ needs `z ∈ G₁` and `r(0) = 0`** (`scDeriv_comp_r_eq_germ`,
     `linAt_eq_germDeriv`, `IsFillingGerm.fillerRestrict_eq_linAt`,
     `StrongBundle.linAt_eq_germDeriv_chart`, `Chapter3/LinearizationChartsG.lean`). The old bridge
     (`scDeriv_comp_r_eq_of_eventuallyEq`) needed `g` sc¹ on the whole `U` and held at every level-`1`
     point `z` of the retract. For a germ `g` on `G₁` the derivative `Dg(z)` exists only for
     `z ∈ (G₁)₁`, and the chain rule for `g ∘ r` is the inner one of item 271 on the germ `r⁻¹(G₁)`,
     which is defined when `r(0) = 0`, i.e. `0 ∈ O`. Proved under these two hypotheses (`r(z) = z`
     puts `z` in `r⁻¹(G₁)`): `D(f̂ ∘ r)(z) = Dg(z) ∘ Dr(z)` and `Lin(z) = Dg(z)` on `T_zO` for `g`
     agreeing with `f̂` on `O` near `ι z`; at `z = 0` this is `Tf̃(0) = Lin(0)` for a filling germ. Both
     hypotheses hold where the consumers use the bridge: the chart is centred at a point of the
     solution set and `z` is the level-`1` lift of a nearby zero (item 278 (e)).
285. **The assembly of Definition 3.53 from a non-centred chart in the germ reading; with `Lin(z)`
     onto `K_z` no Proposition 3.52 is needed** (`StrongBundle.isInGoodPositionIn_ker_germ_of_linAt`,
     `isGoodPositionAtGerm_of_linAt_surj`, `isGoodPositionAtGerm_of_linAt_dense`,
     `isGoodPositionAtGerm_of_chart`, `isGoodPositionAtGerm_of_chart_dense`,
     `isGoodPositionGermG_of_linAt_surj`, `isGoodPositionGermG_of_chart`). In the old file the
     variants with surjectivity onto `K_z` (`isGoodPositionGerm_of_chart`, `_of_linAt_surj`) were
     derived from the dense one and so went through the closed range of `Tf̃'(0)`, i.e. Proposition
     3.52 in the centred chart. Proved directly: if `Lin(z)` is onto `K_z`, then
     `Lin'(0) = Γ ∘ Lin(z) ∘ A⁻¹` (`linAt_chart_change`) is onto `K'_0`, and `Lin'(0) = Dg'(0)` on
     `T₀O'` (item 284); the kernel is transported as before, with `ker Dg'(0) ⊆ T₀O'` from item 281.
     So the section-level forms from `IsScFredholmGermG` to `IsGoodPositionGermG` (`_of_linAt_surj`,
     the form Chapter 5 uses, and `_of_chart`, the form the reading of good position in a tame chart
     needs, where `z = 0` and `K_0` is the whole target) hold with no Fredholm input. The dense forms
     are proved at chart level with `IsFredholm (Dg'(0))` as hypothesis; their section-level forms
     (`isGoodPositionGerm_of_chart_dense`, `isGoodPositionGerm_of_linAt` in the germ reading) are not
     stated here: they are these plus `proposition_3_52_local_germ` (item 289).
287. **The conjugation step of Proposition 3.52, `Γ(0)Dk(0) = Dh(0)Dψ(0)`, needs `k = g − ιs` only
     as an sc¹-germ, and no shrinking of the basic germ**
     (`IsStrongBundleIso.fiberCLM_comp_deriv_zero_eq_germ`,
     `IsStrongBundleIso.deriv_zero_isFredholm_germ`,
     `IsConjugateToBasicGerm.scDeriv_isFredholm_germ`,
     `ConjugationData.scDeriv_isFredholm_index_germ`, `ConjugationData.index_eq_germ`,
     `ConjugationData.scDeriv_isRegularizing_germ`, `ConjugationData.scDeriv_isScFredholm_germ`;
     `Chapter3/FredholmGermLinearizationG.lean`, `FredholmGermIndexG.lean`,
     `FredholmGermLinearizationScG.lean`). The old proof
     (`IsConjugateToBasicGerm.scDeriv_isFredholm`) made `u ↦ (Ψ(u, k(u)))₂` sc-smooth on `U` from
     `k` sc-smooth on `U` and compared its `scDeriv` with that of `h ∘ ψ`. On germs: `(Ψ(·, k(·)))₂`
     is an sc¹-germ on `G_k` by the outer chain rule (item 271), with derivative `Γ(0) ∘ Dk(0)` at
     `0` (`fiberCompDeriv_zero_eq`); `h ∘ ψ` is one on `ψ⁻¹(G_h)` inside the neighbourhood of the
     conjugation identity; the two derivative families agree at `0` on `G_k ∩ ψ⁻¹(G_h)` (uniqueness
     on a germ in a quadrant-like `C`). Everything happens at the point `0`, so the G″ design (item
     276) is not needed here. Proved, for every derivative family `Dk` of `k` on every germ `G_k ⊆
     U`: `Dk(0)` is Fredholm of index `dim Pn − dim Q` for every conjugation `d` (the index does not
     depend on `d`), regularizing, and sc-Fredholm (`Dk(0)` is an sc-operator as the derivative of
     an sc¹-germ at the smooth point `0`, `IsSc1GermWith.isScOperator_deriv_zero`).
288. **`Dg(0) = D(g − ιs)(0) + ιDs(0)` on germs is algebra at `0`, and `(G_s)₀ ⊆ U` is never used**
     (`IsSc1GermWith.sub_toBase_shift`, `IsSc1GermWith.deriv_zero_eq_add_scPlus`). The text's step
     "`Dg(0)` is sc-Fredholm by Proposition 1.10 (`Ds(0)` is sc⁺)": `g − ιs` is an sc¹-germ on `G_g
     ∩ G_s` with the explicit family `Dg − ι ∘ Ds`, so the decomposition is the identity `Dg(0) =
     (Dg(0) − ιDs(0)) + ιDs(0)`; `Ds(0)` is an sc⁺-operator because `s` is an sc¹-germ into `F¹`
     (the old proof needed `s` sc¹ on `U` and `0` smooth). `g − ιs` lives on `G_g ∩ G_s ⊆ G_g ⊆ U`,
     so the inclusion `(G_s)₀ ⊆ U` of `IsScPlusGerm` is not needed, and of `s` only the sc¹-germ
     property into `F¹` is used.
289. **Proposition 3.52 (level `0`, with the index, and in sc form) and Proposition 3.5 in sc form
     hold in the germ reading of Definition 3.11 with the text's hypotheses**
     (`proposition_3_52_local_germ`, `proposition_3_52_germ`, `proposition_3_52_local_index_germ`,
     `proposition_3_52_index_germ`, `IsFillingGerm.proposition_3_5_sc`,
     `proposition_3_52_local_sc_germ`, `proposition_3_52_sc_germ`). The section-level statements
     take `B.IsScFredholmGermG f x₀` and expose, instead of the old `IsFilledVersion` and `scDeriv
     c.U g 0` (a junk value for a germ), the filling germ (`IsFillingGerm`), its germ `G` with `G₀ ⊆
     U` and `IsScSmoothGerm G g`, the family `Dg = scDerivGerm G g` with `IsSc1GermWith G g Dg`, and
     the statements about `Dg(0)`: `Dg(0)` and `Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` are Fredholm
     (sc-Fredholm) with `ind = dim d.Pn − dim d.Q` on every level for every conjugation `d`. The
     chart-level statements hold for every derivative family `Dg` on every germ `G ⊆ U` (and every
     `Ds`); `Dg(0)` is the same for all of them. The old whole-chart statement is the special case
     `G = G_s = ofSet U` (`proposition_3_52_local_of_germ`; at section level
     `IsScFredholmGerm.isScFredholmGermG` feeds the germ versions). Not done here: the
     identification of `Dg(0)Dr(0)` with the chart linearization `linAt` of the principal part (the
     old `IsFilledVersion.fillerRestrict_eq_linAt`, used by Chapter 5).
290. **The sc clause of Theorem 3.19 ("`f'(x₀)` is sc-Fredholm") in the germ reading uses only
     condition (1) of Definition 3.53** (`theorem_3_19_linearization_sc_local_germ`,
     `theorem_3_19_linearization_sc_germ`). Proved: if in the chart of the germ data `Tf(x₀)` is
     onto on level `0` (for `Dg(0)`, any derivative family of the filling germ), then `Dg(0)` and
     `Tf(x₀)` are sc-Fredholm, `Tf(x₀)` is onto on every level (it is regularizing), with the index
     `dim d.Pn − dim d.Q` on every level. The hypothesis is stated inline (the data of
     `IsScFredholmGermG` plus `∃ G Dg, G₀ ⊆ U ∧ IsSc1GermWith G g Dg ∧ (Tf(0) onto)`); it is the
     `surj` field of the germ good position `IsGoodPositionAtGerm` (`GoodPositionGermG.lean`,
     written in parallel), so `StrongBundle.IsGoodPositionGermG f x₀` implies it by projection. The
     kernel condition (2) is not used, as in `theorem_3_19_linearization_sc`.
291. **Theorem 3.12 in the germ reading: the old proof used `g` only on level `0` near `0`, and `t₀`
     only through the sc⁰-germ `t = Ψ[1]_*(t₀)`** (`theorem_3_12_germ`, `corollary_3_13_germ`,
     `Chapter3/SectionCompactnessG.lean`). The text's statement is about its sc-Fredholm germ, so
     the germ version (hypothesis `B.IsScFredholmGermG f x₀`) is the faithful one. `theorem_3_12`
     built `t` as a section sc-smooth on all of `U'` from `t₀` sc-smooth on `U`, but used (a) its
     sc⁰-germ on the basic germ's `G` (the input of Theorem 3.40), and (b) the continuity of `g` on
     `U` at the `E₀`-limits `ψ'(u')`, `u' ∈ closure A`, of the zeros. Germ reading: (a) `t` is an
     sc⁰-germ on `G″ = ψ'⁻¹(G_s) ⊆ G` (germ composition with the whole-chart `ψ'` and `Ψ[1]`), the
     basic germ restricts to `G″` (`IsBasicGerm.mono`, item 275), and Theorem 3.40 is applied on
     `G″`; (b) the level-`0` neighbourhood `N₁` of the filler and conjugation identities is also
     chosen inside the open `O_g` with `(G_g)₀ = O_g ∩ C`, so the limit points lie in `U ∩ N₁ ⊆
     (G_g)₀`, where `g` is continuous (level `0` of the sc⁰-germ `g`). Nothing of `g` away from a
     level-`0` neighbourhood of `0`, and no level `≥ 1` of `G_g` or `G_s` beyond what the sc⁰-germ
     `t` needs, is used. No hypothesis is added.
292. **Theorem 3.54 (3) in the chart holds for germ data: the push-forward sc⁺-germ and the data of
     Theorem 3.38 live on the shrunk germ `G″`, and `D(h + t)(0) = D(Ψ_*g)(0)` is the uniqueness of
     the derivative within `G″₁`** (`theorem_3_54_chart_graph_germ`, `GlobalIFTNearbyGraphG.lean`).
     The old `theorem_3_54_chart_graph` used the whole-chart `g` and `t₀` in four places: (a) the
     push-forward `t = Ψ[1]_*(t₀)` was sc-smooth on all of `U'` and then restricted to the basic
     germ's `G`; (b) `Ψ_*(g)` was sc-smooth on `U'`, so that `D(Ψ_*g)(0)` could be compared with
     `D(h + t)(0)` on `U'₁`; (c) `Dg(0)` Fredholm came from `proposition_3_52_local` inside
     `theorem_3_54_pushforward`; (d) everything else is level `0` near `0` (conditions (1)–(2) of
     the filling, the conjugation identity on `U ∩ N₁`). Proved for `g` a filling germ sc-smooth
     on `G_g` with a derivative family `Dg`, `t₀` an sc⁺-germ on `G_s`, good position at `Dg(0)`,
     and the basic germ on a germ `G` with `ψ'_m(G_m) ⊆ (G_g)_m ∩ (G_s)_m` (`G ⊆ G″`, item 276):
     (a) `t₀ ∘ ψ'` is a germ on `ψ'⁻¹(G_s) ⊇ G` (inner chain rule, item 271) and the whole-chart
     `Ψ[1]` is composed on the outside (item 271 again), so `t` is an sc-smooth germ on `G` and the
     data `𝒮` of Theorem 3.38 are built on `G` itself (`𝒮.G = G`); (b) `Ψ_*(g)` is an sc¹-germ on
     `ψ'⁻¹(G_g) ⊇ G` with the family `pushforwardDeriv` (item 274), and `scDeriv_eq_of_eqOn_nhds`
     is applied with both sets equal to `G₁`; (c) `proposition_3_52_local_germ` (item 289) and
     `theorem_3_54_pushforward_germ` (item 282); (d) unchanged. The conclusion is that of the old
     theorem with `theorem_3_47_proj` (closed good complement with `ProjectsInto`) and
     `𝒮.Dfs h' = pushforwardDeriv … 0` added. No hypothesis is added.
293. **The section-level graph description, Theorem 3.54 (2) at the centre, and Corollary 3.41 and
     Lemma 3.55 along the graph have, in the germ reading, literally the old conclusions**
     (`theorem_3_54_graph_proj_conj_germ`, `theorem_3_54_graph_proj_germ`, `theorem_3_54_graph_germ`,
     `GlobalIFTG.lean`; `theorem_3_54_nearby_germ`, `GlobalIFTFullG.lean`;
     `theorem_3_54_tangentGermChart_proj_conj_germ`, `theorem_3_54_tangentGermChart_proj_germ`,
     `theorem_3_54_tangentGermChart_germ`, `GlobalIFTCenterG.lean`). The glue from
     `IsGoodPositionGermTameG`: `G_g` and `Dg = scDerivGerm G_g g` from the filling germ, `G_s` from
     the sc⁺-germ, conjugation data `d` and `d.shrink (G_g ∩ G_s)` (item 276), the chart theorem of
     item 292 on `G″`, and `Vx = ϕ⁻¹(N₂)` with `ψ(U ∩ N₂) ⊆ G″₀`. The `_conj` form exposes the germ
     data (`IsFillingGerm`, `IsScPlusGerm`, a germ `G` with a derivative family `Dg`,
     `IsGoodPositionAtGerm` at `Dg(0)`, the conjugation data `dc`) and
     `dim K = dim dc.Pn − dim dc.Q`. The old proofs of (2) at the centre and of the nearby
     statement are repeated verbatim: they work on the `E'`-side (`MChart.compDiffeo`, Theorem
     3.47, Corollary 3.41, Lemma 3.55) and never touch `g` or `s`. The input `(1 − Dr(0))E ⊆ E₀`
     of a tame chart centred at a zero is factored out (`StrongBundle.IsTameChart.range_id_sub_scDeriv_le`).
294. **The chain rule for the push-forward at a nearby zero is an identity of the explicit
     derivative family, valid for every family `Dg`** (`levelMap_pairMap_id_at`,
     `IsStrongBundleMap.fiberCompDeriv_at`, `IsStrongBundleIso.pushforwardDeriv_at`,
     `IsStrongBundleIso.ker_deriv_eq_map_germ`). The old `scDeriv_pushforward_at` and
     `ker_scDeriv_eq_map` needed `g` sc-smooth on `U` so that `scDeriv U g u₁` was the derivative.
     In the germ form, `pushforwardDeriv U U' Ψ ψ' g Dg (ψ₁ u₁) = Γ(u₁) ∘ Dg(u₁) ∘ Dψ'(ψ₁ u₁)` at
     every level-`1` zero `u₁` of `g` holds for any `Dg` — the level-`1` point of `(1, g)` over `ι u₁`
     is `(u₁, 0)`, and `scDeriv_fiber_at` gives `Γ(u₁)` — and `ker Dg(u₁) = Dψ'(ψ u₁)(ker D(Ψ_*g)(ψ u₁))`
     follows by the injectivity of `Γ(u₁)`. That `pushforwardDeriv` is the derivative family of
     `Ψ_*(g)` is item 274; so the content "`g` is sc¹ at `u₁`" sits only in `IsSc1GermWith G_g g Dg`
     and `u₁ ∈ (G_g)₁`.
295. **Theorem 3.54 (1), the kernel at the nearby zeros, in the germ reading: the only new input is
     `z₀₁ = ψ'₁(x₁) ∈ (G_g)₁`** (`theorem_3_54_chart_kernel_germ`, `GlobalIFTNearbyKernelG.lean`;
     `theorem_3_54_nearby_kernel_germ`, `GlobalIFTNearbySurjG.lean`). The old proof used the
     whole-chart `g` three times: `Ψ_*(g)` sc-smooth on `U'` for `D(Ψ_*g)(x₁) = D(h + t)(x₁)`,
     `ker_scDeriv_eq_map`, and `scDeriv_pushforward_at` for the surjectivity of `Dg(z₀₁)`. The first
     is the uniqueness of the derivative within `𝒮.G₁` for the family `pushforwardDeriv` restricted
     to `𝒮.G ⊆ ψ'⁻¹(G_g)`, the other two are item 294. The hypothesis `ψ'_m(𝒮.G_m) ⊆ (G_g)_m` is the
     G″ property of item 277, satisfied by the data of item 292; the conclusion adds `z₀₁ ∈ (G_g)₁`
     and states (b)–(d) for `Dg(z₀₁)`. This proves item 278 (b) in the project.
296. **Theorem 3.54 (1) under the filler condition (3), germ reading: the condition is imposed at
     the level-`1` points of `G_g` only, and the chart independence at `y` needs Proposition 3.52
     for germs** (`StrongBundle.IsGoodPositionGermFilledG`,
     `IsGoodPositionGermFilled.isGoodPositionGermFilledG`,
     `exists_range_deriv_eq_ρ_of_normal_injective_germ`,
     `StrongBundle.isGoodPositionGermTameG_of_chart_dense`,
     `StrongBundle.IsScFredholmSectionG.mem_smoothSet_of_isZeroAt`, `theorem_3_54_one_germ`). The
     old `IsGoodPositionGermFilled` asked `(1 − ρ(z₀))Dg(z₁)` injective on `ker Dr(z₁)` at every
     level-`1` point over `O ∩ N`; the germ form asks it for `z₁ ∈ G₁` and the family `Dg`, which is
     where the nearby zeros of item 295 lie. The surjectivity `ρ(z₀)F ⊆ Dg(z₀₁)(T_{z₀}O)` from
     condition (3) uses `D(f̂ ∘ r)(z) = Dg(z) ∘ Dr(z)` for the germ (item 284, which needs `r(0) = 0`).
     The transport to the tame chart centred at `y` (`isGoodPositionAtGerm_of_chart_dense`, item
     285) requires `Dg'(0)` Fredholm there, which is Proposition 3.52 for germs (item 289) applied to
     the tame germ data of `IsScFredholmSectionTameG` at `y`; the old route through
     `IsGoodPositionGerm.toTame` is not used (cf. item 301 for the Fredholm-free route at the
     centre). The germ `G` of the condition and the germ `G_g` of `hfill.germ` may differ; the proof
     intersects them. No hypothesis is added beyond the one the old theorem adds (items 100–107).
297. **The main theorems 3.54, 3.23, 3.19, 3.56, 3.57 and Corollary 3.24 hold in the germ reading
     with the old conclusions** (`GlobalIFTTheoremsG.lean`:
     `theorem_3_54_tangentGermChart_solutionSet_germ`, `theorem_3_54_two_germ`, `theorem_3_54_germ`,
     `theorem_3_23_of_nearby_germ`, `theorem_3_23_germ`, `theorem_3_19_linearization_germ`,
     `theorem_3_19_germ`, `theorem_3_57_germ`, `corollary_3_24_germ`, `theorem_3_56_germ`,
     `theorem_3_57_dim_germ`). Hypotheses: `IsScFredholmSectionG` (3.23 of nearby, 3.19
     linearization, 3.56, 3.57, 3.24, 3.57 dim), `IsScFredholmSectionTameG` with
     `IsGoodPositionGermFilledG` (3.54, 3.23, 3.19), `IsGoodPositionGermTameG` at the zeros (3.54 (2),
     3.56, 3.57), `IsGoodPositionGermG` (3.19 linearization, whose conclusion is Proposition 3.52 for
     germs with `Dg(0)` in place of `scDeriv U g 0`). The proofs are the old ones: the assembly
     (re-centring, `exists_isRegular_of_locally`, Theorems 3.27 and 3.27 loc) takes place on the
     `E'`-side and in `X`. The whole-chart statements are unchanged and imply the germ ones
     through `TameGermsG.lean` and item 296; the forms with the text's hypotheses (no
     `IsGoodPositionGermFilledG`) are item 298.
298. **Theorem 3.54 (1) with the text's hypotheses holds in the germ reading: the curve of the
     perturbation argument lies in the germ of the filling** (`theorem_3_54_chart_onto_germ`,
     `theorem_3_54_one'_germ`, `theorem_3_54'_germ`, `theorem_3_23'_germ`, `theorem_3_19'_germ`,
     `GlobalIFTNearbyOntoG.lean`). The old `theorem_3_54_chart_onto` differentiates `g` along the
     curve `u(μ) = ψ'₁(ι glue(u'(μ)))` of zeros of `g + μ ρ(r(·)) k` through `z₀`, where `u'(μ)`
     lies on level `2` of the germ `𝒮.G` of Theorem 3.40, and it used `g` sc¹ on all of `U₁`. In the
     germ reading `u(μ) ∈ (G_g)₁`: `ι glue(u'(μ)) ∈ 𝒮.G₁` (`ScNbhdGerm.inclK_mem`) and `ψ'₁` maps
     `𝒮.G₁ ⊆ G″₁` into `(G_g)₁` (the G″ property, item 277); `g ∘ u` is then differentiable at
     `μ = 0` by the chain rule within `(G_g)₁`, with derivative `Dg(z₀₁)ξ₀` for the family `Dg`.
     The normal form, its contraction regions, the inward direction and the perturbed curve
     (`GlobalIFTNearbyOnto*.lean`) are constructions on the `E'`-side and are unchanged; the
     filler condition (2) on `U ∩ N₂` is level `0`. The section-level assembly is that of item
     296 with `theorem_3_54_chart_onto_germ` in place of condition (3) (for `d = 0` the only zero
     near `x₀` is `x₀`). So Theorems 3.54 (1)–(2), 3.23 and 3.19 hold in the germ reading with the
     text's hypotheses and no added hypothesis. This proves item 278 (c) in the project.
299. **What the germ reading of Theorem 3.54 still lacks (not done in this round).** (a)
     `GlobalIFTIndex.lean` (`theorem_3_54_ker_eq_tangent`,
     `isGoodPositionGermFilled_of_isGoodPositionGerm`, the index forms `theorem_3_54_index`,
     `theorem_3_23_index`, `theorem_3_19_index`, `theorem_3_57_index`, `theorem_3_56_tame`, and
     `IsSurjLinOfIndex`/`IsLinSurjAt` with `isGoodPositionGerm_iff_isLinSurjAt`): they use
     `proposition_3_52_local_index` and `linAt_index_of_conjugationData` with whole-chart `g`, `s`,
     and `theorem_3_54_nearby_kernel` with `scDeriv U g z`; the germ forms need
     `proposition_3_52_local_index_germ` (`FredholmGermIndexG.lean`), the bridge `Lin(z) = Dg(z)`
     of item 284 at the nearby zeros `z₀₁ ∈ (G_g)₁` of item 295, and
     `theorem_3_54_nearby_kernel_germ`. (b) `LinearizationChartsSc.lean`, `GoodPositionSc.lean`,
     `IndexLocallyConstant.lean`: the sc forms (item 290) and the index along the zero set. The old
     statements are unchanged, and the old ⇒ germ direction is available throughout
     (`TameGermsG.lean`, `IsGoodPositionGermFilled.isGoodPositionGermFilledG`).

**300–309: Definition 3.11 on germs, Theorems 3.15 and 3.18 (phase 2, 2026-11-01).**

Theorems 3.15 and 3.18 for sections that are sc-Fredholm in the text's germ reading
(`StrongBundle.IsScFredholmSectionG`, `IsScFredholmSectionTameG`, `TameGermsG.lean`), in
`Chapter3/FredholmSectionsG.lean`, `TameGermsAddG.lean`, `ParamPerturbationG.lean` and
`NonVacuityG.lean`. The old whole-chart statements are unchanged.

300. **Theorem 3.15 holds in the germ reading with the text's proof; the only germ input is the sum
     of a germ and a whole-chart map** (`IsFillingGerm.congr`,
     `StrongBundle.sectionAdd_chartData_germ`, `StrongBundle.IsScFredholmGermG.sectionAdd`,
     `StrongBundle.regularizing_sectionAdd_germ`, `theorem_3_15_germ`,
     `StrongBundle.IsScFredholmGerm.sectionAdd_germG`). The text keeps the chart
     and takes the filling `g + s̃`, `s̃ = ŝ ∘ r`, the sc⁺-section `s̃ + t₀`, and the conjugation of
     `(g + s̃) − (s̃ + t₀) = g − t₀`. Proved, for germ data `(g, t₀)` (`g` a filling germ on `G_g`,
     `t₀` an sc⁺-germ on `G_{t₀}`): in the same chart `g + ŝ ∘ r` is a filling germ of the principal
     part of `f + s` on the same `G_g` (Lemma 3.17 for germs, item 273, applied to the whole-chart
     section `ŝ ∘ r`, with `r ∘ r = r` on `U` and a congruence lemma for filling germs),
     `ŝ₁ ∘ r + t₀` is an sc⁺-germ on the same `G_{t₀}`, its value at `0` is `g(0) + ŝ(r(0))`, and the
     conjugation is the old one (`IsConjugateToBasicGerm.congr`, item 279). `ŝ ∘ r` is sc-smooth on
     the whole `U` because `s` is an sc⁺-section of the bundle, so the germ-`ŝ` form of Lemma 3.17
     (`add_section_germ`) is not needed. Items (2) (regularizing) and (1) (sc-smooth) of Definition
     3.14 are statements about sections; the old proofs used only that `f` is sc-smooth and
     regularizing and are repeated with the germ-reading hypothesis. No hypothesis is added. This
     completes what item 279 left open.
301. **Good position can be read in the tame chart of the germ data with no Proposition 3.52, and
     Theorem 3.15 keeps tame germ data** (`StrongBundle.IsGoodPositionGermG.toTame`,
     `StrongBundle.IsScFredholmGermTameG.sectionAdd`, `theorem_3_15_tame_germ`). The old
     `IsGoodPositionGerm.toTame` went through `isGoodPositionAt_of_chart_dense` (range of `Dg₁(0)`
     containing `ρ(0)F_∞`), which needs the closed range in the target chart. In the germ form the
     chart `c₁` of the good position is centred at the zero `y`, so the point of the non-centred
     assembly is `z = 0`, which lies in every germ, and `r(0) = 0` holds; condition (1) of good
     position in `c₁` says that `Dg₁(0)` maps `T₀O₁` onto `ρ(0)F`, which is all of `K₀` (`(0, k) ∈ K`
     gives `k = ρ(0)k`). So the `_surj` assembly of item 285 (`isGoodPositionAtGerm_of_chart`)
     applies directly, without Fredholm input. Proved: good position in the germ reading in some
     centred chart plus tame germ data in the germ reading give good position in the germ reading in
     the tame chart (`IsGoodPositionGermTameG`, at `Dg(0)` for the family `scDerivGerm G g` of the
     tame chart's filling germ, hence for every family, item 280). The chart step of item 300 does
     not change the chart, so it keeps its tameness; Theorem 3.15 for tame germ data in the germ
     reading follows.
302. **Theorem 3.18 in the germ reading: the product germ `ℝⁿ × G`, and "readily verified" holds for
     germs** (`StrongBundle.IsScFredholmGermG.param`, `StrongBundle.regularizing_paramLift_germ`,
     `StrongBundle.IsScFredholmSectionG.param`, `theorem_3_18_germ`, `theorem_3_18_germ'`,
     `StrongBundle.IsScFredholmGermTameG.param`, `StrongBundle.IsScFredholmSectionTameG.param`,
     `theorem_3_18_tame_germ`). In the product chart `(r ↦ r − r₀) × φ` the germ data of
     `f̃ = f ∘ π` at `(r₀, x)` are: the filling germ `(a, u) ↦ g(u)` on `ℝⁿ × G_g`
     (`PullbackChartData.ofProd_isFillingGerm`, item 274), the sc⁺-germ `(a, u) ↦ t₀(u)` on
     `ℝⁿ × G_{t₀}` (`ScNbhdGerm.univProd`, `IsScSmoothGerm.univProd`), and the old conjugation to the
     `ℝⁿ`-extension of the basic germ (`IsConjugateToBasicGerm.paramExtend`): it is about `g − t₀`
     on `U`, and `1_{ℝⁿ} × Ψ` and the extended basic germ are whole-chart objects, so no germ
     calculus enters it. The product germ is unbounded in the `ℝⁿ`-direction on every level, which
     Definition 3.1 allows. Then `F = f̃ + s̃` and Theorem 3.15 in the germ reading (item 300) give
     Theorem 3.18 in the germ reading; the tame form uses the tameness of the product chart of a tame
     chart (`ofProd_isTame`, unchanged) and item 301. No hypothesis is added.
303. **The linearization of the parametrized section (after Theorem 3.19) involves no germ data**
     (`scDeriv_paramSection_of_isScSmoothSection`, `scDeriv_paramSection_germ`,
     `linAt_paramSection_germ`, `linAt_paramSection_zero_germ`). The old `scDeriv_paramSection` and
     its `linAt` forms took an sc-Fredholm section, but used only that `f` is sc-smooth: the
     derivative is that of the whole-chart map `F̂ ∘ (1 × r)` at the centre. Proved for every
     sc-smooth section `f`; the germ-reading forms (hypothesis `IsScFredholmSectionG`) are
     instances. The identification of `Lin_f(0)` with `Dg(0)` for a filling germ `g` is the bridge of
     item 284, at the centre `z = 0`.
304. **The non-vacuity witnesses satisfy the germ-reading notions** (`Chapter3/NonVacuityG.lean`:
     `TrivialBundle.isScFredholmSectionG_graphSection`, `isScFredholmSectionTameG_graphSection`,
     `isGoodPositionGermTameG_graphSection`, `hypotheses_theorem_3_57_graphSection_germ`,
     `hypotheses_theorem_3_57_linear_germ`, `htame_fails_repaired_holds_germ`, and the
     `HalfSpaceBundle` forms with `hypotheses_theorem_3_57_halfSpace_germ`). The witnesses of
     `NonVacuity.lean`, `NonVacuityCorner.lean` and `TameVacuityChart.lean` build whole-chart germ
     data, and whole-chart data are germ data (`TameGermsG.lean`). So the germ-reading hypotheses of
     Theorem 3.57 (sc-Fredholm in the germ reading, good position in a tame chart at every zero, the
     boundary included) are satisfiable, and the old hypothesis `htame` still fails for a bundle
     meeting them. These are one-line corollaries; no new example is constructed.

**310–319: Definition 3.11 on germs, the index statements (phase 2, 2026-11-01).**

The index statements of §3.6 and the sc forms of the linearization, for sections that are
sc-Fredholm in the text's germ reading, in `Chapter3/GlobalIFTIndexG.lean`,
`LinearizationChartsScG.lean` and `IndexLocallyConstantG.lean`. The old whole-chart statements are
unchanged.

310. **Proposition 3.52 in every chart and the index of `f'(x₀)` hold in the germ reading; the only
     germ inputs are at the centre of the chart of the germ datum**
     (`StrongBundle.linAt_index_of_conjugationData_germ`,
     `StrongBundle.isSurjLinOfIndex_of_conjugationData_germ`,
     `StrongBundle.IsGoodPositionGermG.exists_isSurjLinOfIndex`,
     `theorem_3_19_linearization_index_germ`). The old proofs used `proposition_3_52_local_index`
     for a filled version on the whole `U` and `IsFilledVersion.fillerRestrict_eq_linAt`. Proved
     for a filling germ `g` with a derivative family `Dg` on a germ `G ⊆ U` and an sc⁺-germ: in
     the centred chart `Tf̃(0) = Dg(0)|_{T₀O}` is Fredholm of index `dim Pn − dim Q`
     (`proposition_3_52_local_index_germ`, item 289), `Tf̃(0) = Lin(0)` (item 284 at `z = 0`, which
     lies in every germ), and `linAt_chart_independence`, which is about `linAt` only, carries the
     Fredholm property, the index and (under good position at `Dg(0)`) the surjectivity to every
     chart. `StrongBundle.IsSurjLinOfIndex`, `IsLinSurjAt` and `IsLinSurjAt.linAt_surjective` are
     statements about the derivative of the whole-chart map `f̂ ∘ r` and need no germ form. Where
     the old conclusions exposed `IsFilledVersion` and `scDeriv U g 0`, the germ forms expose the
     filling germ, `G`, `Dg` and `Dg(0)`.
311. **"Dimension = index", the local constancy of the index along the solution set, and the main
     theorems with the index hold in the germ reading with the old conclusions**
     (`theorem_3_54_tangentGermChart_index_germ`,
     `theorem_3_54_tangentGermChart_solutionSet_index_germ`, `theorem_3_54_two_index_germ`,
     `isSurjLinOfIndex_of_forall_dim_germ`, `theorem_3_54_index_locally_constant_germ`,
     `theorem_3_54_index_germ`, `theorem_3_23_index_germ`, `theorem_3_19_index_germ`,
     `theorem_3_19_of_surjective_germ`, `theorem_3_57_index_germ`, `theorem_3_56_tame_germ`,
     `theorem_3_56_of_surjective_germ`). Hypotheses: `IsScFredholmSectionTameG` and
     `IsGoodPositionGermTameG` (3.54, 3.23, 3.19, the local constancy), `IsScFredholmSectionG` with
     good position in a tame chart at every zero (3.56, 3.57), `IsLinSurjAt` for the "surjective"
     forms. The dimension `d` of the tangent germ data at `x₀` is `dim Pn − dim Q` for the
     conjugation in the chart of Definition 3.53 (`theorem_3_54_tangentGermChart_proj_conj_germ`),
     so item 310 gives `IsSurjLinOfIndex f x₀ d`; the rest of each proof is the old one with
     `theorem_3_54_one'_germ`, `theorem_3_54_two_germ` and `theorem_3_57_germ` (items 297–298), on
     the `E'`-side and in `X`. No hypothesis is added: Theorems 3.19, 3.23 and 3.54 with the text's
     hypotheses carry "whose dimension agrees with the Fredholm index" in the germ reading.
312. **"Good position = surjectivity" when `d_X(y) = 0` holds in the germ reading, without
     Proposition 3.52** (`StrongBundle.IsGoodPositionGermG.isLinSurjAt`,
     `StrongBundle.isGoodPositionGermG_of_linAt_surj_of_degIndex_eq_zero`,
     `StrongBundle.isGoodPositionGermG_of_isLinSurjAt`,
     `StrongBundle.isGoodPositionGermG_iff_isLinSurjAt`). Good position at `Dg(0)` gives `Lin(0)`
     onto `K₀`, since `Lin(0) = Dg(0)` on `T₀O` (item 284 at the point `0` of the germ).
     Conversely, in the tame chart of the germ data the partial quadrant `C_{ϕ(y)}` is the whole
     space, the kernel condition is void, and the `_surj` assembly of item 285 gives Definition
     3.53 in the germ reading with no Fredholm input; item 301 reads it in the tame chart. These
     are the germ twins of two of the four `GlobalIFTIndex.lean` statements that Chapter 5 uses
     (item 322); the other two are `theorem_3_54_index_germ` and `theorem_3_56_of_surjective_germ`
     (item 311).
313. **"`ker f'(y) = T_yS`" in a chart, and the filler condition of `IsGoodPositionGermFilledG`,
     follow from good position in the germ reading** (`theorem_3_54_ker_eq_tangent_germ`,
     `isGoodPositionGermFilledG_of_isGoodPositionGermG`,
     `normal_injective_of_exists_range_deriv_eq_ρ_germ`,
     `exists_range_deriv_eq_ρ_iff_normal_injective_germ`). The old proofs used
     `Lin(z) = scDeriv U g z` at the level-`1` lifts `z` of the nearby zeros. In the germ reading
     the bridge `Lin(z) = Dg(z)` (item 284) needs `z ∈ (G_g)₁`. For the kernel this is the point
     `z₀₁ ∈ (G_g)₁` of `theorem_3_54_nearby_kernel_germ` (item 295, the G″ design). For the filler
     condition, `z₁ ∈ G₁` is part of the condition of `IsGoodPositionGermFilledG` (item 296), so
     the bridge applies at every point the condition quantifies over. Finding 100's equivalence is
     linear algebra in the operator `Dg(z)` and holds for germs as stated. So the added hypothesis
     of `theorem_3_54_germ`, `theorem_3_23_germ` and `theorem_3_19_germ` follows from the text's
     hypotheses in the germ reading, as it did for whole-chart data (Finding 174).
314. **Condition (3) of a filler on every level, the converse of Proposition 3.5 in sc form, and
     "`Lin(z)` is sc-Fredholm in every chart" hold in the germ reading**
     (`IsFillingGerm.mem_range_toBase_of_scDeriv_r_eq_zero`,
     `IsFillingGerm.filler_condition_three_sc`, `IsFillingGerm.proposition_3_5_sc_converse`,
     `IsFillingGerm.proposition_3_5_sc_iff`, `StrongBundle.linAt_sc_of_germ_germ`,
     `StrongBundle.linAt_isScFredholm_germ`,
     `StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex_germ`,
     `theorem_3_54_index_locally_constant_sc_germ`, `LinearizationChartsScG.lean`). The
     `IsFillerOf` statements of items 237–238 are about the point `0` of the chart; for a filling
     germ they hold with `Dg(0)` in place of `scDeriv U g 0` and the same proofs (Proposition 3.5
     and the kernel isomorphism for filling germs; `IsFillingGerm.proposition_3_5_sc`, item 289).
     The transport of item 239 from the chart of the germ datum to any chart is about `linAt` and
     is unchanged; the germ datum enters only through Proposition 3.52 in sc form for germs at its
     centre. The index on every level is `dim d.Pn − dim d.Q` for every germ datum in the germ
     reading at the zero.
315. **The index is locally constant along the zero set in the germ reading (round-trip item V3.98
     (b)); good position of the parametrized section suffices, general position is not needed**
     (`StrongBundle.isLinOfIndex_of_conjugationData_germ`,
     `StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex_germ`,
     `exists_spanning_sections_germ`, `isLinSurjAt_paramSection_zero_of_spanning_germ`,
     `spanning_of_isLinSurjAt_germ`, `exists_sections_isParamGP_germ`,
     `isGoodPositionGermTameG_paramSection_of_isParamGP`,
     `index_locally_constant_of_admitsBumpFunctions_germ`,
     `theorem_3_54_index_locally_constant_general_germ`, `IndexLocallyConstantG.lean`). The old
     proof (items 240–244) puts `F(λ, y) = f(y) + Σ λᵢ sᵢ(y)` into general position at `(0, x₀)`
     (Definition 5.17) and uses Lemma 5.26. Its Chapter 5 steps take the whole-chart notions, so
     germ copies are made in the Chapter 3 file. The spanning sections need `Lin(0)` of closed
     range and finite codimension, which in the germ reading is Proposition 3.52 for germs with
     `Tf̃(0) = Lin(0)` (the one place that item 322 (a) lists); the tilting sections of (ii) use
     only that `f` is sc-smooth. The general position of `F` needs
     `ker F'(0, y) = T_{(0, y)}S̃` (`exists_isGeneralPositionGerm_iff`,
     `exists_tangentSpace_eq_linKer`), which is not redone. The index argument uses only the good
     position of `F` at `(0, x₀)`, which is the first half of the old proof
     (`isGoodPositionGermTameG_paramSection_of_isParamGP`, through items 285 and 301). Proved, with
     the hypotheses `PX.AdmitsBumpFunctions` and `IsScFredholmSectionTameG`: there are an open
     `V ∋ x₀` and `i ∈ ℤ` with `f'(y)` Fredholm of index `i` in every chart at every zero `y ∈ V`,
     and sc-Fredholm of index `i` on every level.
316. **What item 299 listed is done; what remains of the germ reading of the index statements.**
     Done: every declaration of `GlobalIFTIndex.lean`, `LinearizationChartsSc.lean` and
     `IndexLocallyConstant.lean` that opens germ data or takes the sc-Fredholm or good-position
     notions has a germ twin (items 310–315). Not done: the general position of the parametrized
     section in the germ reading (`isGeneralPositionGerm_paramSection_of_isParamGP`, with
     `exists_isGeneralPositionGerm_iff` and `exists_tangentSpace_eq_linKer` below it) and the rest
     of Chapter 5. The Chapter 5 copies of item 315 duplicate their originals until stage 2
     replaces the originals' proofs.

**320–329: Definition 3.11 on germs, good position in sc form and the Chapter 5 interface (phase 2,
2026-11-01).**

Definition 3.53 with the text's sc-complement and the theorems stated with it, in the text's germ
reading (`Chapter3/GoodPositionScG.lean`), and the check that Chapter 5 can switch to the germ
reading (`Chapter3/Chapter5BridgeG.lean`). The old statements are unchanged.

320. **Definition 3.53 with the text's sc-complement holds at every zero in the germ reading, with
     the old proof** (`IsGoodPositionAtScGerm`, `isGoodPositionAtSc_iff_germ`,
     `IsGoodPositionAtScGerm.of_isSc1GermWith`, `StrongBundle.IsGoodPositionGermScG`,
     `StrongBundle.IsGoodPositionGermSc.isGoodPositionGermScG`,
     `StrongBundle.IsGoodPositionGermTameG.isGoodPositionGermScG`,
     `StrongBundle.isGoodPositionGermScG_iff`). The text asks for an sc-complement of `ker f'(x)`
     (Definition 3.21 as written); the project's upgrade from an algebraic to an sc-complement
     (items 210–214) needed `ker Dg(0)` to consist of smooth vectors. In the germ reading the chart
     notion is parametrised by `Dg₀ = Dg(0)`, as in item 280, and the section notion asks for a
     derivative family `Dg` on some germ `G ⊆ U`. Proved: at a zero `y` of an sc-Fredholm section
     with tame germ data in the germ reading, good position in a tame chart gives good position
     with an sc-complement in the same chart. `ker Dg(0) = Dψ'(0)(ker D(h + t)(0))` comes from
     `theorem_3_54_nearby_kernel_germ` applied at `y` itself (`z₀₁ = 0`, `x₁ = 0`), and `Ψ'` is
     sc-smooth on all of `U'` in the germ reading (only the filling and the sc⁺-section are germs),
     so `Dψ'(0)` preserves smooth vectors as before. No hypothesis is added.
321. **Theorems 3.54 (1)–(2), 3.23, 3.56, 3.57 and Corollary 3.24 with the text's notion of good
     position hold in the germ reading** (`theorem_3_54_one_sc_of_tame_germ`,
     `theorem_3_54_one_sc_germ`, `theorem_3_54_sc_germ`, `theorem_3_23_sc_germ`,
     `forall_isGoodPositionGermScG_iff`, `theorem_3_57_sc_germ`, `corollary_3_24_sc_germ`,
     `theorem_3_56_sc_germ`). These combine items 297–298 (the germ-reading theorems with the
     algebraic complement) with item 320. Every zero near `x₀` is in good position in the text's
     sense, and "every zero in good position" in the text's sense is the hypothesis of the
     germ-reading global theorems.
322. **Outside `GlobalIFTIndex.lean`, every Chapter 3 statement that Chapter 5 uses has a germ
     twin of the same shape, except Proposition 3.52 and the filler bridge** (the coverage table of the phase 2 notes, built from
     the compiled Chapter 5 terms; `corollary_3_13_section_germ` added). Of the Chapter 3
     declarations used in Chapter 5 whose statements mention the sc-Fredholm or good-position
     notions, 18 have germ twins with the same type after the notions are renamed, either
     syntactically or up to proof arguments. `corollary_3_13_section` had no twin; it now has
     one, also of the same type. The exceptions are `proposition_3_52` and
     `IsFilledVersion.fillerRestrict_eq_linAt`. Their germ twins expose the germ `G`, the family
     `Dg` and `Dg(0)` in place of `scDeriv U g 0`, as the germ reading requires; both are used
     only in `exists_spanning_sections`.
     The four `GlobalIFTIndex.lean` statements used in Chapter 5 (`IsGoodPositionGerm.isLinSurjAt`,
     `isGoodPositionGerm_of_isLinSurjAt`, `theorem_3_54_index`, `theorem_3_56_of_surjective`) are
     outside this item.
323. **Four Chapter 5 proofs open the germ data; each needs a local change, checked against the
     germ notions** (`StrongBundle.IsGoodPositionGermTameG.congr_nhds`; scratch checks of the other
     three). (a) `exists_spanning_sections`: the extra `G`, `Dg` of Proposition 3.52 (item 322).
     (b) `exists_nbhd_isCompact_closure_bdd` (the local step of Theorem 5.5): `t₀` is continuous
     only on `(G_s)₀`, so the neighbourhood is cut with the open set of that germ (edits at five
     places).
     (c) `corollary_5_8_chart` (Corollary 5.8, "`f¹` is sc-Fredholm"): the statement changes. In
     the germ reading `s¹` is an sc⁺-germ on the shifted germ (Proposition 1.17 for germs), which
     is the text's setting. The level-`1` conjugation needs a germ form of
     `IsConjugateToBasicGerm.shift` whose hypothesis is that `g − s` is an sc⁰-germ, used only
     eventually near `0`. (d) The germ invariance of good position (`congr_nhds`, used in Theorem
     5.19) is proved in Chapter 3 with the same statement. Other Chapter 5 proofs open only the
     chart prefix of the germ data, which the germ notions share. No change is made to Chapter 5
     in this round.

**330–339: Definition 3.11 on germs, the switch (phase 2, 2026-11-01).**

The canonical names now denote the text's germ reading of Definition 3.11 and of everything built
on it; the project's original whole-chart notions and theorems keep their statements under the
names `…WholeChart` / `…_wholeChart`. Chapter 5 compiles against the germ reading. The rename map
(298 declarations) is `stage2_renames.tsv` of the phase 2 notes.

330. **The eight notions were switched in place.** `StrongBundle.IsScFredholmGerm` (Definition
     3.11), `IsScFredholmSection` (3.14), `IsScFredholmGermTame` (3.50), `IsScFredholmSectionTame`
     (3.51), `IsGoodPositionGerm` (3.53), `IsGoodPositionGermTame`, `IsGoodPositionGermFilled` and
     `IsGoodPositionGermSc` are the former `…G` notions of the `*G.lean` files (items 270–329): the
     filling `g` is an sc-smooth germ (`IsFillingGerm`) and the sc⁺-section `s` an sc⁺-germ
     (`IsScPlusGerm`) on germs of neighbourhoods whose levels may shrink; the strong bundle
     isomorphism and the basic germ are as before. The former notions are
     `StrongBundle.IsScFredholmGermWholeChart`, `IsScFredholmSectionWholeChart`, …, with `g`, `s`
     sc-smooth on the whole chart domain `U` (items 220–221, 260–266); their docstrings and the
     module docstring of `StrongBundleSections.lean` say so. The bridges "project ⇒ text" read
     `IsScFredholmGermWholeChart.isScFredholmGerm`, `IsScFredholmSectionWholeChart.isScFredholmSection`,
     etc. (one for each notion). Nothing was reproved: a renaming, applied by script in two passes
     (old → `WholeChart`, then `G` → canonical) to `Chapter3/`, `Chapter4/` and `Test.lean`.
331. **142 theorems swapped with their germ twins; 34 of the twins have a different shape.** For
     every Chapter 3 theorem `X` with a germ twin `X_germ` (or `…G_…`) of stage 1, the old `X` is
     now `X_wholeChart` and the twin is `X`: `theorem_3_12`, `corollary_3_13(_section)`,
     `theorem_3_15(_tame)`, `theorem_3_18(_tame, ')`, `theorem_3_19` and its variants,
     `theorem_3_23` and variants, `corollary_3_24`, `proposition_3_52` and variants,
     `theorem_3_54` and all its chart, graph, kernel, onto, nearby, index, `sc` and
     tangent-germ-chart forms, `theorem_3_56`, `theorem_3_57` and variants, the linearization
     lemmas (`linAt_paramSection`, `linAt_isScFredholm`, `isGoodPositionGerm_of_linAt_surj`,
     `isGoodPositionGerm_of_isLinSurjAt`, `IsGoodPositionGerm.isLinSurjAt`, …), the non-vacuity
     checks of `NonVacuity.lean` / `NonVacuityCorner.lean` / `TameVacuityChart.lean` and the index
     statements of `GlobalIFTIndex.lean` / `IndexLocallyConstant.lean`. A machine check
     (`Expr.eqv` after renaming the notions) found 108 pairs with literally the same statement and
     34 whose germ statement differs: `proposition_3_52` with its `_local`, `_index`,
     `_local_index`, `_sc`, `_local_sc` forms, `theorem_3_19_linearization` (`_index`, `_sc`),
     `theorem_3_54_chart_graph/kernel/onto`, `theorem_3_54_linear(_of_isTameWith)`,
     `theorem_3_54_pushforward(_section)`, `theorem_3_54_nearby_kernel`,
     `theorem_3_54_graph_proj_conj`, `theorem_3_54_tangentGermChart_proj_conj`,
     `linAt_isScFredholm(_of_isSurjLinOfIndex)`, `linAt_sc_of_germ`,
     `isGoodPositionGerm_of_chart`, `IsGoodPositionGerm.exists_isSurjLinOfIndex`,
     `isLinOfIndex_of_conjugationData`, `isSurjLinOfIndex_of_conjugationData`,
     `linAt_index_of_conjugationData`, `ConjugationData.index_eq`,
     `ConjugationData.scDeriv_isFredholm_index/_isRegularizing/_isScFredholm`,
     `IsConjugateToBasicGerm.scDeriv_isFredholm`, and
     `IsStrongBundleIso.pushforward_linearization/_surjective/_ker_isInGoodPosition`. In each of
     these the germ side carries the germ `G`, the derivative family `Dg` (with `Dg 0` for
     `scDeriv U g 0`) or `IsFillingGerm` in place of `IsFilledVersion`, as the germ reading
     requires (items 280–286, 310–315); they were swapped all the same, since the canonical name
     is meant to state the text's hypotheses, and the whole-chart forms remain under
     `_wholeChart`. Of the 34 only `proposition_3_52` is used by Chapter 5 (item 333). Not
     swapped: the four germ copies of Chapter 5 lemmas in `IndexLocallyConstantG.lean`
     (`exists_spanning_sections_germ`, `isLinSurjAt_paramSection_zero_of_spanning_germ`,
     `spanning_of_isLinSurjAt_germ`, `exists_sections_isParamGP_germ`; they would collide with
     Chapter 5's own names, which are now the germ statements themselves), and the stage 0
     calculus lemmas whose `_germ` suffix means "for germs" with no Definition 3.11 twin
     (`IsSc1With.comp_germ`, `IsFillingGerm.add_section_germ`, `proposition_3_52_local_of_germ`,
     `theorem_3_19_linearization_sc_local_germ`, …).
332. **Every phase-2 name still resolves** (`Chapter3/GermReadingAliases.lean`): the eight `…G`
     notions as `abbrev`s and 145 `alias`es (`theorem_3_54_germ := theorem_3_54`,
     `StrongBundle.IsGoodPositionGermG.isLinSurjAt := …`, generated from the rename map), each
     with the docstring "Phase-2 name of …". The old whole-chart names that now denote the germ
     reading need no alias. The one cited name that would have disappeared,
     `StrongBundle.IsGoodPositionGermFilled.isGoodPositionGerm` (the whole-chart lemma had no
     germ twin), was given its germ form (`GlobalIFTNearbySurjG.lean`, from
     `IsGoodPositionGermFilled.isGoodPositionGermTame`). `IsScFredholmSection.mem_smoothSet_of_isZeroAt`
     (a zero of a regularizing section is a smooth point) moved from `GlobalIFTNearbySurjG.lean`
     to `TameGermsG.lean`, where Chapter 5 reaches it; `Chapter5BridgeG.lean` uses it instead of
     repeating the induction.
333. **Chapter 5 holds under the text's reading of Definition 3.11.** Chapter 5 was not renamed:
     its hypotheses `IsScFredholmSection`, `IsScFredholmSectionTame`, `IsGoodPositionGermTame`, …
     now are the germ notions, and its proofs compile with four local changes (item 323):
     (a) `exists_spanning_sections` (`Transversality.lean`) opens the germ `G` and the derivative
     family `Dg` of `proposition_3_52` and uses `Dg 0` and
     `IsFillingGerm.fillerRestrict_eq_linAt`; (b) `exists_nbhd_isCompact_closure_bdd`
     (`Compactness.lean`, the local step of Theorem 5.5) cuts its neighbourhood with the open set
     `O_s` on which the sc⁺-germ `t₀` is continuous into `F₁` (five edits, statement unchanged);
     (c) `corollary_5_8_chart` (Corollary 5.8 for `i = 1`) **changes its statement**: the filled
     version becomes the filling germ `g` (`IsFillingGerm`), `s` an sc⁺-germ, and `s¹` an
     sc⁺-germ on the shifted germ `G_s¹` (instead of sc-smooth on all of `U¹`); its level-`1`
     conjugation comes from the new `IsConjugateToBasicGerm.shift_germ` (`g − s` an sc⁰-germ on
     `G_g ∩ G_s`, used only near `0`); (d) the Chapter 5 copy of
     `StrongBundle.IsGoodPositionGermTame.congr_nhds` was removed, the Chapter 3 germ form of
     item 323 (`Chapter5BridgeG.lean`) taking its name and its one use (Theorem 5.19). The other
     Chapter 5 proofs open only the chart prefix of the germ data. New imports: `Compactness.lean`
     ← `SectionCompactnessG`, `Chapter5BridgeG`, `GermCalculus`, `GermLevels`;
     `BumpFunctions.lean` ← `ParamPerturbationG`; `Transversality.lean` ← `GlobalIFTIndexG`,
     `FredholmGermLinearizationG`, `LinearizationChartsG`. So Theorems 5.5, 5.7, 5.18, 5.19 and
     the rest of Chapter 5 now carry the text's hypotheses; every `#print axioms` of `Test.lean`
     is standard.
334. **The expositions cite the canonical names; the trace tags were repointed.** The
     `Polyfold.…` names cited in `Verification.md`, `Findings.md`, `Chapter3.md`, `Chapter5.md`
     and `Comparison.md` all resolve (the phase-2 names through item 332). In
     `ProofByProof.md` and its sources `pbp/part0*.md`, 99 distinct tags (176 occurrences in
     `ProofByProof.md`) now point at the file where the canonical name lives
     (`⟦Chapter3/GlobalIFTTheoremsG · theorem_3_54⟧` for the former
     `⟦Chapter3/GlobalIFTTheorems · theorem_3_54⟧`, and `theorem_3_54` for the former
     `theorem_3_54_germ`); the prose next to them was not rewritten, so where it describes a
     whole-chart proof the tag now names the germ-reading theorem of the same statement
     (the whole-chart theorem is the `_wholeChart` declaration of the file the prose names).
     Not done: `RoundTrip/` (the audit library, not a default target) was not renamed; its items
     that cite the old canonical names now see the germ statements.

**340–349: the index along the zero set and along paths (2026-11-02).**

Definition 6.1 (the index of the sc-Fredholm germ `(f, x)` at a smooth point which need not be a
zero) and Proposition 6.2 (its stability along sc-smooth paths, p. 201–203), in
`Chapter3/IndexAlongPaths.lean`; and the status of item 243 (the local constancy of the index
along the zero set with the text's hypotheses alone).

340. **Definition 6.1 is formalized and well defined, without compact operators**
     (`StrongBundle.IsIndexAt`, `StrongBundle.IsLinOfIndex.unique`,
     `StrongBundle.isLinOfIndex_sectionAdd_of_isZeroAt`, `StrongBundle.IsIndexAt.unique`,
     `StrongBundle.isIndexAt_of_isZeroAt`, `StrongBundle.IsIndexAt.isLinOfIndex_of_isZeroAt`,
     `StrongBundle.exists_isIndexAt`). `IsIndexAt f x i`: there is an sc⁺-section `s` of `P` with
     `f + s` vanishing at `x` and `(f + s)'(x)` Fredholm of index `i` in every chart
     (`IsLinOfIndex`, item 244); the text's `f − s` with `s(x) = f(x)` is `f + (−s)`. The text's
     "all have the same Fredholm index" rests on Proposition 1.10 (`(t − s)'(x)` is level-wise
     compact); the project has no "`Lin(z)` of an sc⁺-section is compact" lemma, and the
     independence of `s` is proved from the germ data instead: at a zero `x` of the sc-Fredholm
     section `f`, `f'(x)` has index `dim Pn − dim Q` for the conjugation data `dc` of its germ
     datum, and Theorem 3.15 gives germ data of `f + s` in the same chart whose conjugation data
     are `dc` up to the values on `U` (`sectionAdd_chartData_germ`, `ConjugationData.congr`), so
     `(f + s)'(x)` has the same index when `s(x) = 0`; for two sections `s, s'` of Definition 6.1,
     `s' − s` vanishes at `x` and `(f + s) + (s' − s) = f + s'`. The uniqueness of the index in
     `IsLinOfIndex` at a zero uses that `Lin(z)` is a bounded operator into `K_z`
     (`linAt_isScFredholm`), so the universal quantification is not vacuous. At a zero, `ind(f, x)`
     is the index of `f'(x)` (`s = 0`). With bump functions `ind(f, x)` exists at every smooth
     point: Lemma 5.11 gives `s₀` with `s₀(x) = f(x)` (a smooth point of `Y`,
     `IsScSmoothMap.mapsTo_levelSet`), `s = −s₀`, and Proposition 3.52 for the germ data of
     `f + s` at `x`. Two readings are fixed: the sc⁺-section is global on `X` (the text's is
     local; with bump functions the two agree by Lemma 5.11), and the sentence "`(f − s)'(x)` is
     a sc-Fredholm operator if and only if `(f − s)'(x)` is" (p. 201) reads `(f − t)'(x)` on one
     side.
341. **Proposition 6.2, the local form: along the zero set of `f + s`, and along paths through
     it** (`isIndexAt_locally_constant_of_isZeroAt_sectionAdd`,
     `isIndexAt_eventually_const_of_path`, `isIndexAt_const_of_forall_eventually`,
     `isIndexAt_const_of_path`). For `X` admitting bump
     functions, `f` with tame germ data (Definition 3.51) and any sc⁺-section `s` with
     `(f + s)(x₀) = 0`: `ind(f, y)` is one integer at all zeros `y` of `f + s` near `x₀`
     (`theorem_3_15_tame` and item 315). Hence for a path `φ` continuous at `t₀` along which
     `f + s` vanishes near `t₀`, `t ↦ ind(f, φ(t))` is constant near `t₀`; and on a preconnected
     parameter space, if every `t` has such an `s_t`, `ind(f, φ(t))` is one integer for all `t`
     (the index function is locally constant by `IsIndexAt.unique`;
     `IsLocallyConstant.apply_eq_of_isPreconnected`). Only the continuity of the path enters
     here; its sc-smoothness is needed for the sections `s_t` (item 342). For the text's `[0, 1]`
     this is the whole proposition once the sections exist.
342. **The text's device on `ℝ × X`, and what remains of Proposition 6.2 (round-trip item V3.98
     (a))** (`MPolyfold.admitsBumpFunctions_prod_rn`, `MPolyfold.IsScSmoothMap.mul`,
     `isScSmoothMap_rn_real_of_contDiff`, `tsupport_prod_mul_subset`,
     `isLinOfIndex_paramLift_sectionAdd_eventually_const`,
     `proposition_6_2_of_sections_of_slice`). The text fixes `t₀`, takes a locally
     defined sc⁺-section `s(t, x)` of the pull-back to `[0, 1] × X` with `s(t, φ(t)) = f(φ(t))`
     near `t₀`, stabilizes `f − s` by finitely many sc⁺-sections and applies the implicit
     function theorem; the last two steps are the local constancy along the zero set (item 315)
     on `ℝ × X`. Proved: `ℝⁿ × X` admits bump functions when `X` does (products `β₁(r) β₂(x)` of
     a `C^∞` bump of `ℝⁿ` and a bump of `X`, `tsupport ⊆ supp β₁ × supp β₂`), and for an
     sc⁺-section `S` of `π*P` with `f̃ + S` vanishing along the graph `t ↦ (t, φ(t))` near `t₀`
     (`f̃ = f ∘ π`, Theorem 3.18), the index of `(f̃ + S)'(t, φ(t))` in every chart of `π*P` is
     one integer for `t` near `t₀`. Not proved, and stated as the two hypotheses that close the
     proposition: (E) the section `S(t, x) = −β(x) R(x, Φ(f(φ(t)))₂)` in a strong bundle chart
     around `φ(t₀)`, cut off by a bump `β` (and by a bump in `t` where `φ(t)` leaves the chart),
     is an sc⁺-section of `π*P`: through `isScPlusSection_cutoffSection` in the product chart
     `PullbackChartData.ofProd`, which needs the sc-smoothness of `t ↦ Φ(f(φ(t)))₂` into `F¹`
     (a curve of smooth points from the constant sc-structure of `ℝ`; an sc-smooth map `ℝ → F`
     is `C^∞` into every `F_m`, a fact the project does not have) and the `[1]`-sc-smoothness of
     the bundle retraction; (S) the slice relation
     `ind (f̃ + S)'(t, φ(t)) = ind (f + S(t, ·))'(φ(t)) + 1`: the slice `S(t, ·)` is an
     sc⁺-section of `P`, and in the product chart
     `Lin_{f̃+S}(0, 0)(δa, δu) = Lin_{f + S(t,·)}(0) δu + δa ∂ₜŜ(0, 0)`, so
     `fredholmIndex_eq_of_param` with `k = 1` applies — the analogue of
     `isLinOfIndex_of_paramSection_isLinOfIndex` (item 242) for a `t`-dependent section, whose
     proof (`linAt_paramSection_zero`) is written for `f(x) + Σ λᵢ sᵢ(x)` only. Given (E) and (S),
     `isLinOfIndex_paramLift_sectionAdd_eventually_const` and
     `isIndexAt_const_of_forall_eventually` give Proposition 6.2 for every sc-smooth path on a
     preconnected parameter set; `proposition_6_2_of_sections_of_slice` states this reduction
     formally, with (E) and (S) as hypotheses on `ℝ × X` and the conclusion
     `∃ i, ∀ t, ind(f, φ(t)) = i` for `φ : ℝ → X`. **Both steps are closed in items 345–346,
     and Proposition 6.2 is proved (item 347).** The hypotheses are
     those of item 240 (tame germ data, bump functions); the text assumes a tame M-polyfold and
     uses locally defined sections (item 343). Verdict for V3.98 (a): partial.
343. **Item 243 revisited: the index along the zero set with the text's hypotheses.** (i) *The
     hypotheses of the text.* Theorem 3.54 and Proposition 6.2 are stated for a tame strong bundle,
     read as tame germ data (Definition 3.51, items 190–199); the text does not assume bump
     functions, and its proof of Proposition 6.2 says so ("we do not need a sc-smooth partition of
     unity"): the stabilizing sections are `R(·, e)` in a chart, defined on the chart domain only.
     The bump functions of items 240 and 315 are an artifact of the project's global sections
     (`IsScPlusSection` on `X`, Theorem 3.18 on `ℝᵏ × X`): `exists_spanning_sections_germ` and
     `exists_sections_isParamGP_germ` cut the local sections off with Lemma 5.11. Dropping them
     needs the same device on the open chart domain `V`: the restriction of `P` to `V` (the
     pull-back along the inclusion, as `restrictSection` does for sub-M-polyfolds in
     `Chapter5/Homotopy.lean`), the sections `R(·, eᵢ)` as sc⁺-sections of `P|V` without cut-off,
     Theorem 3.18 and the local constancy along the zero set on `ℝᵏ × V`, and the transport of
     `IsLinOfIndex` between `P` and `P|V` (`StrongBundleChart.restrict`). None of this is
     formalized; nothing in it is in doubt mathematically. So, under the text's hypotheses, the
     local constancy of the index along the zero set is the text's own argument, formalized with
     one extra hypothesis. (ii) *Tameness.* The device uses tame germ data at the corner only
     (the good position of the kernel of the stabilized section, item 241) and through Theorem
     3.54 (1)–(2) for the stabilized section. Without tame germ data the question is beyond the
     text, and non-tame charts are pathological there: the retract `O = {0} × W` of
     `C = [0, ∞) × W` (`r(s, w) = (0, w)`) is compatible with the chart `W` of the same
     M-polyfold, so a germ datum at a point with `d_X = 0` may sit at a boundary point of its
     chart (`d_C(0) = 1`), where the kernel condition of good position fails. The exact gap is
     unchanged: `ind f'(y) = ind f'(x₀)` iff the normal block `C(z)` of the filling at the nearby
     zero has index `0` (item 243). (iii) *The candidate counterexample of items 188 and 243 is
     excluded under the text's hypotheses.* The retract `{(t, s e_t)}` with fibres of rank `2` for
     `t ≠ 0` and `0` at `t = 0`, and the section `f(t, s e_t) = s e'_t`, has `ind Lin = 1` at
     `(0, 0)` and `0` at `(t, 0)`, `t ≠ 0`. Its chart has no boundary (`C = E`), hence is tame
     (`d_C ≡ 0`, and `T_zO = Dr(z)E` has the sc-complement `ker Dr(z)`, Proposition 2.21 (3)), and
     `(f, (0, 0))` is in good position (`Lin(0, 0) : ℝ → 0` is onto, the kernel condition is void).
     If `f` were an sc-Fredholm section with tame germ data, Theorem 3.54 (1) with the text's
     hypotheses (round-trip item V3.94, `theorem_3_54`, items 180–189 and 321) would make
     `Lin(t, 0)` onto the two-dimensional `K_{(t,0)} = span(e'_t, e''_t)` for small `t`; but
     `Lin(t, 0)(δt, δs e_t) = δs e'_t` has rank `1`. So `f` has no germ datum in a tame chart at
     the centre: the example refutes neither Theorem 3.54 nor Proposition 6.2, and whether it has
     germ data in a non-tame chart at `(0, 0)` is the only question left about it. (The example is
     not formalized; the argument applies the formal Theorem 3.54 (1) by hand.) *Verdict for item
     243.* Under the text's hypotheses (tame germ data, no bump functions) the index is locally
     constant along the zero set by the text's device, formalized with the extra hypothesis of
     bump functions, whose removal is a localization not done; no candidate counterexample
     remains. Beyond the text (no tame germ data) the question is open, with the gap
     `ind C(z) = 0`.
344. **Bookkeeping.** New files `Chapter3/IndexAlongPaths.lean` (imports `IndexLocallyConstantG`)
     and `Chapter3/IndexAlongPathsDevice.lean` (imports `IndexAlongPaths`), registered in this
     order in `Polyfold.lean`, with `Test.lean` sections; every `#print axioms` is standard.
     Comparison: see item 348 (V3.98 (a) is proved); Definition 6.1 (§6.1, p. 200–201) has no row
     and could get one ("stronger": the independence of `s` without Proposition 1.10, and the
     existence of `ind(f, x)` at every smooth point under bump functions).
345. **(E) is closed: the text's sc⁺-section along the path**
     (`exists_isScPlusSection_pullback_of_path`, `isScSmoothMap_rn_of_contDiff`,
     `exists_contDiff_eq_id_near_mapsTo`, `Chapter3/IndexAlongPathsDevice.lean`). For an
     sc-smooth section `f` (sc-Fredholm is not needed), an sc-smooth path `φ : ℝⁿ → X` and `t₀`,
     there is an sc⁺-section `S` of `π*P` on `ℝⁿ × X` with `f̃ + S = 0` along the graph
     `t ↦ (t, φ(t))` near `t₀`. The lemma asked for in item 342, "an sc-smooth curve of smooth
     points `ℝ → F` is sc-smooth into `F¹`", is true and needs no new analysis: the chart
     representative `t ↦ Φ(f(ψ(t)))` of `f ∘ ψ` is sc-smooth from the constant structure `ℝⁿ` into
     `E ⊕ F`, Proposition 1.17 (`IsScSmooth.shift`, in the project since Chapter 1) makes it
     sc-smooth from `(ℝⁿ)¹` into `(E ⊕ F)¹`, and `(ℝⁿ)¹ = ℝⁿ`, `(E ⊕ F)¹ = E¹ ⊕ F¹` hold by
     definition (`rfl`); its `F¹`-component `ê₁` is the lifted curve. The section is the text's
     `s(t, x) = R(x, f(φ(t)))` with a sign, in the product chart `(r ↦ r − t₀) × φ_c` over a
     strong bundle chart `c` around `φ(t₀)`: `τ(a, u) = −R[1](u, ê₁(a + t₀))₂`, sc-smooth
     `ℝⁿ × O → K[1]` by the `[1]`-sc-smoothness of the bundle retraction
     (`IsStrongBundleMap.isScSmooth_one`), with values in `K[1]` because `R(u, ·)₂` is linear and
     `R(u, h) ∈ K`; the cut-off `S = cutoffSection pc β τ` with `β(t, x) = β₂(x)`, a bump of `X`
     equal to `1` near `φ(t₀)` with support in `dom φ_c` (`proposition_5_30`,
     `isScPlusSection_cutoffSection`). Two devices of the formalization: the path is first
     precomposed with a `C^∞` map `σ : ℝⁿ → ℝⁿ` equal to the identity near `t₀` with values in
     `φ⁻¹(dom φ_c)` (`σ(t) = t₀ + b(t − t₀)(t − t₀)` for a `ContDiffBump`), so that the curve
     `t ↦ Φ(f(φ(σ(t))))` is defined on all of `ℝⁿ` and `S` is global on `ℝⁿ × X` — the text's
     section is local in `t` as well; and `C^∞` self-maps of `ℝⁿ` are sc-smooth maps of the
     M-polyfold `ℝⁿ`. Along the graph, `Φ(S(t, φ(t)))₂ = −R(φ_c(φ(t)), Φ(f(φ(t)))₂)₂ =
     −Φ(f(φ(t)))₂` since `Φ(f(φ(t))) ∈ K` (`ρ_eq_self_of_mem_K`), so `f̃ + S` vanishes at
     `(t, φ(t))` for `t` near `t₀` (`σ(t) = t` and `β₂(φ(t)) = 1`). Bump functions enter only
     through the cut-off; the text has no cut-off because its section is local.
346. **(S) is closed: the slice relation** (`pullbackSlice`, `IsSection.pullbackSlice`,
     `isZeroAt_pullback_iff_pullbackSlice`, `pullbackSlice_sectionAdd_paramLift`,
     `StrongBundle.IsScPlusSection.pullbackSlice`, `PullbackChartData.r_ofProd`,
     `ScBanach.prodSndLeftOp`, `StrongBundle.linAt_ofProd_slice`,
     `StrongBundle.isLinOfIndex_pullbackSlice_of_isLinOfIndex`,
     `StrongBundle.isIndexAt_of_pullback_isLinOfIndex`). The slice `S(t, ·)` of a section of
     `π*P` (`π : ℝⁿ × X → X`), read in `Y`, is a section of `P`; `G(t, x) = 0` iff the slice
     vanishes; the slice of `f̃ + S` is `f + S(t, ·)` (the fibre of `π*Y` over `(t, x)` is
     `P⁻¹(x)`, `pullbackFiberEquiv`). **The slice of an sc⁺-section of `π*P` is an sc⁺-section of
     `P`**: for a chart `c` of the atlas of `P`, the product chart `(r ↦ r − t) × φ_c` is a chart
     of the atlas of `π*P` (`pullbackAtlas`), and the local representative of `S(t, ·)` in `c` is
     that of `S` in the product chart composed with the sc-operator `u ↦ (0, u)` and projected to
     `E ⊕ F¹`. **The linearization on the slice direction**: in the product chart at `(t, x)`,
     `Lin_G(0)(0, δu) = Lin_{G(t,·)}(0) δu` — the chain rule of Theorem 1.21
     (`scDeriv_comp_apply'`) for `H ∘ ι`, `H = Ĝ ∘ (1 × r)`, `ι(u) = (0, u)` an sc-operator whose
     derivative is itself (`ScOperator.scDeriv_eq`), and `H ∘ ι = Ĝ(t, ·) ∘ r` since
     `r_{pc}(a, u) = (a, r(u))` and `φ_{pc}⁻¹(0, v) = (t, φ_c⁻¹(v))`. **The index**: if `G` is an
     sc-Fredholm section of `π*P` whose slice `g = G(t, ·)` is an sc-Fredholm section of `P` with
     `g(x) = 0`, and `G'(t, x)` is Fredholm of index `i` in every chart, then `g'(x)` is Fredholm
     of index `i − n` in every chart: the proof of item 242 with `Lin_G(0)(δa, δu) =
     Lin_g(0) δu + Lin_G(0)(δa, 0)` (linearity and the slice identity) in place of
     `linAt_paramSection_zero`, `fredholmIndex_eq_of_param` with the finite-rank part
     `δa ↦ Lin_G(0)(δa, 0)`, and the chart independence through the germ datum of `g` at `x`.
     For `G = f̃ + S` with `f` sc-Fredholm and `S` sc⁺ (`n = 1`): at a zero `(t, x)` of `f̃ + S`
     where `(f̃ + S)'(t, x)` has index `i`, `ind(f, x) = i − 1` (Definition 6.1 through the slice
     `S(t, ·)`), which is the hypothesis (S) of `proposition_6_2_of_sections_of_slice`.
347. **Proposition 6.2 is proved** (`proposition_6_2`, `proposition_6_2'`; round-trip item V3.98
     (a)). Let `X` admit sc-smooth bump functions, `f` be an sc-Fredholm section with tame germ
     data (Definition 3.51) and `φ : ℝ → X` an sc-smooth path (`(rnPolyfold 1).IsScSmoothMap`;
     smooth points are automatic). Then there is `i ∈ ℤ` with `ind(f, φ(t)) = i` (Definition 6.1,
     `IsIndexAt`) for every `t`; by `IsIndexAt.unique`, `ind(f, φ(0)) = ind(f, φ(1))`. The proof
     is the text's: for each `t₀` the section `S` of item 345, the local constancy of the index of
     `f̃ + S` along its zero set on `ℝ × X` (Theorems 3.18 and 3.15 for tame germ data, item 315
     with the bump functions of `admitsBumpFunctions_prod_rn`), the index count of item 346, and
     the preconnectedness of `ℝ` (`isIndexAt_const_of_forall_eventually`). Against the text:
     (i) the path is `ℝ → X`, not `[0, 1] → X` — `ℝ × X` is the product of Theorem 3.18 and no
     boundary enters, and the text's "tame M-polyfold `[0, 1] × X`" is not used; a path on
     `[0, 1]` that extends sc-smoothly to `ℝ` is covered, a path sc-smooth on `[0, 1]` only in the
     sense of M-polyfolds with boundary is not (the reparametrization of item 345 shows that only
     a neighbourhood of each `t₀` matters, so an open interval would do as well); (ii) the
     hypotheses are those of item 240: tame germ data in place of "tame strong bundle", and bump
     functions, which the text does not assume ("we do not need a sc-smooth partition of unity")
     — they are used for the stabilizing sections (Lemma 5.11) and for the cut-off of the section
     along the path, both globalizations of the text's locally defined sections (item 343 (i));
     (iii) Definition 6.1 is proved well defined without Proposition 1.10 (item 340); (iv) the
     two points the text's proof does not address (item 241: the tilting sections for the kernel
     condition at a corner, and the uniformity in the zero) are those of the zero-set case.
348. **Comparison and bookkeeping for Proposition 6.2.** Suggested verdict for V3.98 (a):
     "narrower" with the chips "+bump functions", "paths on `ℝ`", "Definition 6.1 well defined",
     and the diff: Proposition 6.2 is proved (`proposition_6_2`) by the text's device — the
     sc⁺-section along the path, the stabilization and the implicit function theorem (through the
     local constancy along the zero set, V3.98 (b)) and the index count — with tame germ data and
     bump functions, for sc-smooth paths `ℝ → X`; Definition 6.1 (`IsIndexAt`) is formalized and
     well defined. V3.97 and V3.85 are unchanged. No gap entry changes: the extra hypothesis is the
     bump functions of item 240, and item 343 records what their removal would take.
349. **Follow-up: the bump functions are removed** (items 360–366): Proposition 6.2 is proved with
     the text's hypotheses (tame germ data, no bump functions) for Definition 6.1 read with a
     *locally defined* sc⁺-section (`IsIndexAtLocal`, `proposition_6_2_local`), and the local
     constancy of the index along the zero set (item 343 (i), V3.98 (b)) is proved without bump
     functions (`index_locally_constant_tame`), by the localization that item 343 describes: the
     restriction of `P` to a chart domain (`StrongBundle.restrictOpen`), the sections `R(·, e)`
     without cut-off, Theorem 3.18 on `ℝᵏ × V`, and the transport of `IsLinOfIndex` through the
     germ datum.

**350–359: tame germ data from a tame atlas (2026-11-02).** (`Chapter3/TameGermData.lean`;
comparison items V3.13, V3.45, V3.103; settles the strategy and sharpens the question of item 199.)

350. **Condition (3) of Definition 3.4 is a condition on the chart.**
     `IsFillingGerm.nonempty_kerEquiv`: a filling germ `g` of `f̂` in a chart whose strong bundle
     retraction is `R = (r, ρ)` gives a topological linear isomorphism `ker Dr(0) ≃ ker ρ(0)` (the
     witness of condition (3), the linearization of `y ↦ [1 − ρ(r(y))]g(y)` on `ker Dr(0)`). These
     are the normal space of `O = r(U)` in `E` at `0` and the normal space of the fibre
     `K₀ = ρ(0)F` in `F`; both depend on the chart only. `not_isFillingGerm_of_ker`: in a chart
     with `ker Dr(0) ≠ 0` and `ker ρ(0) = 0` no map `g` is a filling germ of any `f̂`. So "the
     principal part has a filling" is not a property of the section alone, and germ data cannot in
     general be moved from one chart to another; Definition 3.11 is an existential over charts for
     this reason.
351. **A compatible tame chart of the trivial bundle in which no section has germ data**
     (`TrivialBundle.evenBundleChart`, for the bundle `ℝⁿ × ℝᵏ → ℝⁿ` of `NonVacuity.lean`): the
     model `ℝ ⊕ ℝⁿ` without boundary, the base retraction `r(a, u) = (0, u)` (`TrivialBundle.Reven`,
     the product of the constant retraction `zeroRetr` of `ℝ` onto `0` with the identity of
     `ℝⁿ`), the chart `x ↦ (0, x)` onto the retract `{0} × ℝⁿ`, and `R((a, u), h) = ((0, u), h)`;
     centred at `0`. It is compatible with the translation charts (`isChart_evenBundleChart`; the
     transitions `((0, x), v) ↦ (x − a, v)` and `(x, v) ↦ ((0, x + a), v)`, as for the non-tame
     chart of item 202 with `[0, ∞)` replaced by `ℝ` and `1` by `0`), and it is **tame**
     (`Reven_isTame`, `isTameChart_evenBundleChart`: the degeneracy index of `ℝ ⊕ ℝⁿ` is `0`
     everywhere, `ℝ ⊕ 0` is an sc-complement of `T_xO = 0 ⊕ ℝⁿ` inside `E_x = E`; tame for the
     product presentation by `ScRetraction.IsTameWith.prod`, hence for all presentations by
     `IsTameWith.isTame`). But `ker Dr(0) = ℝ ⊕ 0 ≠ 0` while `ρ(0) = 1`, so
     `not_isFillingGerm_evenBundleChart`: **no `g` fills the principal part of any section in this
     chart**. Re-centring it at `(0, x₀)` translates the base only (`StrongBundleChart.recentre`)
     and gives the same retraction, so the obstruction is the same at every point (said, not
     formalized).
352. **A strong bundle with a tame atlas, an sc-Fredholm section with tame germ data, and no germ
     data in the atlas chart** (`TrivialBundle.bundleEven n k`,
     `tame_atlas_no_germData_in_atlas_chart`): the trivial bundle with the one-chart atlas
     `{evenBundleChart}`. Every chart of the atlas is tame (`bundleEven_atlas_isTameChart`); the
     translation charts are compatible with it and tame (`isChart_chart_even`,
     `isTameChart_chart_even`); the graph section `x ↦ (x, φ(x))` of a `C^∞` map `φ : ℝⁿ → ℝᵏ` is
     an sc-Fredholm section with tame germ data (`isScFredholmSectionTame_graphSection_even`,
     Definitions 3.14 and 3.51 in the germ reading; the germ data are those of item 200, in the
     compatible chart `chart x₀`, not in the atlas chart); and in every chart of the atlas no map
     fills the principal part of any section.
353. **Verdict on item 199 (Definition 3.11 ⟹ Definition 3.50 when the atlas is tame).**
     (i) The strategy proposed there — re-centre a tame chart of the atlas at `x₀` and transport
     the filling, the sc⁺-germ and the conjugation to it — is refuted: by item 350 the re-centred
     atlas chart need not admit any filling, and item 352 is an instance. (ii) Definition 3.50 must
     be read as the project reads it (`StrongBundle.IsScFredholmGermTame`: the data of Definition
     3.11 in **some** chart that is compatible with the atlas and tame); the reading "in the
     (re-centred) chart of the given tame atlas" would make every section of `bundleEven`
     non-Fredholm. The text's "there exists a strong bundle chart" in Definitions 3.11 and 3.50 is
     therefore essential, not a convenience. (iii) The implication itself — germ data in some
     compatible chart ⟹ germ data in some compatible tame chart, when the atlas is tame — is
     **open**; item 352 is not a counterexample (the graph section has tame germ data in a
     translation chart). What a proof needs: from the chart `c` of the germ data (base retraction
     not tame) a compatible tame chart `c'` centred at `x₀` with `ker Dr'(0) ≅ ker ρ'(0)`, and a
     filling of `f̂'` built in `c'`. The transition `c' ∘ c⁻¹` is an sc-diffeomorphism of the
     retracts `K → K'` only, while the filling lives on `U ◁ F` off `K`, so it cannot be pushed
     forward; the natural ansatz `g'(y') = Γ(τ'(r'(y'))) g(τ'(r'(y')) + L(y' − r'(y')))` with
     `L : ker Dr'(0) ≅ ker Dr(0)` needs the normal bundles `(1 − ρ(u))F` over `O` and
     `(1 − ρ'(u'))F'` over `O'` to be isomorphic as bundles near `0` and condition (2) to be
     re-proved; the sc⁺-germ and the conjugation transport as soon as the filling does (the
     conjugation composes with the extended transition). A counterexample would need a bundle in
     which every compatible tame chart centred at `x₀` violates condition (3) for every `g` while
     some non-tame compatible chart carries germ data; the compatible charts are too many to be
     controlled by the normal-space invariant alone (for infinite-dimensional normal spaces
     `ℝ ⊕ N ≅ N` is possible, so the construction of item 351 does not obstruct). Neither a proof
     nor a counterexample is known here. The theorems of §3.6 are unaffected: they assume
     `IsScFredholmSectionTame` (tame germ data), which is what the text assumes.
354. **The first part of item 199** (the chart `(1, φ)` with base retraction `(a, u) ↦ (1, r(u))`
     for a general strong bundle) is still not done: its compatibility needs the transitions
     `((1, u), h) ↦ T(u, h)` as sc-smooth retract maps for an arbitrary chart, i.e. the composition
     of `IsScSmoothRetractMap` with the linear projection and injection in general; what is checked
     is the trivial-bundle instance (item 202) and its tame counterpart (item 351).
355. **Bookkeeping.** New file `Chapter3/TameGermData.lean` (imports `TameVacuityChart`,
     `NonVacuityCorner`, `NonVacuityG`), registered after `NonVacuityG` in `Polyfold.lean`, with a
     `Test.lean` section; every `#print axioms` is standard. Comparison: V3.103 keeps "explicit";
     replace its sentence "That germ data in some chart (V3.13) can be moved to a tame chart when
     the atlas consists of tame charts (Definition 3.11 ⟹ Definition 3.50) is not formalized" by:
     "Whether germ data in some chart (V3.13) can be moved to some compatible tame chart when the
     atlas consists of tame charts (Definition 3.11 ⟹ Definition 3.50) is open; it cannot be done
     by re-centring a chart of the tame atlas: whether a filling exists in a chart depends on the
     chart (`ker Dr(0) ≅ ker ρ(0)` is necessary, `IsFillingGerm.nonempty_kerEquiv`), and the
     trivial bundle with the one-chart tame atlas `{evenBundleChart}` has sc-Fredholm sections
     with tame germ data in compatible charts but none in the atlas chart
     (`tame_atlas_no_germData_in_atlas_chart`; Findings, Chapter 3, items 350–353)", with a chip
     "filler chart-bound". V3.13: add to the diff "The existential over charts is essential: a
     filling in one chart gives none in another unless the normal spaces match (items 350–352)".
     V3.45 unchanged. No gap entry changes.

**360–369: Proposition 6.2 without bump functions (2026-11-02).** (`Chapter3/RestrictOpen.lean`,
`RestrictOpenGerms.lean`, `IndexLocallyConstantLocal.lean`, `IndexAlongPathsLocal.lean`; round-trip
item V3.98; removes the bump functions of items 240, 315, 341–343 and 347, by the localization
announced in item 343 (i).)

360. **The restriction of a strong bundle to an open subset is constructed**
     (`MChart.restrictTo`, `MPolyfold.restrictOpen`, `StrongBundleChart.restrictTo`,
     `StrongBundle.restrictOpen`, `StrongBundleChart.restrictInter`). The text restricts `P` to
     chart domains without comment ("in a chart, `s(y) = R(y, f(x))`"; the proof of Proposition
     6.2). Formalized: for an open `V ⊆ X`, the M-polyfold structure of the subtype `V` whose atlas
     consists of all charts of `X` with source inside `V`, transported (compatibility and the
     cover from `MChart.restrict`, `IsChart.restrict`), and the strong bundle `P|V = ι*P` on the
     pull-back `ι*Y = {(v, y) | P(y) = v}` of Definition 2.53 (as in Definition 5.20,
     `restrictSection`), whose atlas consists of all strong bundle charts of `P` with base domain
     inside `V`, transported (same `F`, `U`, `R`, `K`, `Φ ∘ ι`; the compatibility transports since
     the overlaps and transition maps are those of the charts of `P`, `Compatible.restrictTo`).
     Every chart of `P` restricts to a chart of `P|V` (`restrictInter`, `StrongBundleChart.restrict`
     to `dom φ ∩ V`); the levels of `V` are the traces of the levels of `X`
     (`mem_levelSet_restrictOpen_iff`); an sc-smooth map with values in `V` is sc-smooth into `V`
     (`IsScSmoothMap.codRestrict_restrictOpen`); `f|V` is sc-smooth, sc⁺, regularizing when `f`
     is (`IsScSmoothSection.restrictOpen`, `IsScPlusSection.restrictOpen`,
     `regularizing_restrictOpen`, through `mem_doubleLevel_iff`). Choices: the paracompactness of
     `V` and of `ι*Y` are instance arguments (Theorem 2.16, `paracompactSpace_subtype`,
     `paracompactSpace_pullbackSpace`), and `V` is assumed nonempty (`[Nonempty V]`, for the junk
     values of the transported inverse charts).
361. **Germ data restrict** (`IsFillingGerm.of_subset`, `IsScPlusGerm.of_subset`,
     `ConjugationData.ofSubset`, `IsConjugateToBasicGerm.of_subset`,
     `StrongBundleChart.germData_restrictInter`, `IsTameChart.restrictInter`,
     `IsScFredholmGerm.restrictOpen`, `IsScFredholmGermTame.restrictOpen`,
     `IsScFredholmSection.restrictOpen`, `IsScFredholmSectionTame.restrictOpen`). The data of
     Definition 3.11 in a chart centred at `x` on a relatively open `U` restrict to every
     relatively open `U₀ ⊆ U` containing `0`: the germs of the filling and of the sc⁺-section are
     intersected with `U₀` (`IsScSmoothGerm.mono`, `IsSc1GermWith.mono`); the derivative of `r` at
     `0` and `ρ(0)` do not change (`scDeriv_eq_of_eqOn_relOpen`), so the kernel isomorphism of
     condition (3) is the same; the strong bundle isomorphism `Ψ` of the conjugation is restricted
     to `U₀ ◁ F → ψ(U₀) ◁ F'` with `ψ(U₀) = U' ∩ ψ'⁻¹(U₀)` relatively open by the continuity of
     `ψ'`, and the basic germ is shrunk to `G ∩ ψ'⁻¹(U₀)` (`ConjugationData.shrinkGerm`, item 266)
     with the same `Pn`, `Q`, `h`, `B`. Hence an sc-Fredholm section with tame germ data on `P`
     restricts to one on `P|V` (the chart of the germ datum at `x ∈ V` is restricted to
     `dom φ ∩ V`, whose base retraction is tame by `ScRetraction.restrict_isTame`). This is the
     "restriction of the chart on level `0`" that the germ reading of Definition 3.11 promised
     (item 260) but had not used.
362. **The index is the same on `P` and on `P|V`** (`isLinOfIndex_restrictOpen_of_conjugationData`,
     `IsLinOfIndex.restrictOpen`, `IsLinOfIndex.of_restrictOpen`, `IsIndexAt.restrictOpen`,
     `IsIndexAt.restrictOpen_of_subset`, `IsLinOfIndex.restrictOpen_of_subset`). At a zero `x ∈ V`
     of an sc-Fredholm section `f`, `f'(x)` is Fredholm of index `i` in every chart of `P` iff
     `(f|V)'(x)` is in every chart of `P|V`. The transport does not compare the charts of `P|V`
     with those of `P` (a chart of `P|V` need not come from a chart of `P`): the index is
     `dim Pn − dim Q` for the germ datum in either bundle (`isLinOfIndex_of_conjugationData`, with
     the restricted conjugation data of item 361, whose `Pn`, `Q` are unchanged), and
     `IsLinOfIndex.unique` identifies it with `i`. The same argument restricts a section of
     `P|V` to `P|W`, `W ⊆ V`, where the common chart `c|dom φ ∩ W` and `linAt_congr` compare the
     two linearizations.
363. **Theorem 3.54 along the zero set, and Lemma 5.11, without bump functions** (round-trip item
     V3.98 (b); `StrongBundle.HasScPlusSectionsThrough`,
     `MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`,
     `StrongBundle.hasScPlusSectionsThrough_of_chart`, `exists_spanning_sections_of_sections`,
     `exists_sections_isParamGP_of_sections`, `index_locally_constant_of_sections`,
     `index_locally_constant_tame`, `theorem_3_54_index_locally_constant_general_tame`). The bump
     functions of items 240 and 315 enter only through Lemma 5.11, as sc⁺-sections through given
     smooth fibre points; `HasScPlusSectionsThrough` is that conclusion (without the support and
     the norm bound, which the index argument does not use), and the three proofs of
     `IndexLocallyConstantG.lean` are repeated with it in place of the bump functions. A strong
     bundle with a chart of its atlas over the whole base has such sections without any cut-off —
     the text's `R(·, e)` (the proof of Lemma 5.11 with `β = 1`) — and the restriction `P|V` to
     a chart domain has such a chart. Hence, **for an sc-Fredholm section `f` with tame germ data
     of any strong bundle and a zero `x₀`, the index of `f'(y)` is one integer at all zeros `y`
     near `x₀`, in every chart** (`index_locally_constant_tame`): the text's device on `P|V`,
     `V = dom φ_c`, with the index transported back by item 362. This settles item 343 (i): the
     local constancy along the zero set holds with the text's hypotheses alone; the gap
     `ind C(z) = 0` of item 243 remains only beyond the text (no tame germ data).
364. **Definition 6.1 with a locally defined sc⁺-section** (`StrongBundle.IsIndexAtLocal`,
     `IsIndexAt.isIndexAtLocal`, `IsIndexAtLocal.unique`, `isIndexAtLocal_of_isZeroAt`,
     `StrongBundle.exists_isIndexAtLocal`, `isIndexAtLocal_const_of_forall_eventually`,
     `sectionRestrict`). The text's section `s` of Definition 6.1 is local ("a local sc⁺-section
     `s` with `s(x) = f(x)`"); item 340 read it as a global section, which without bump functions
     is a priori stronger. `IsIndexAtLocal f x i`: there is an open `V ∋ x` and an sc⁺-section `s`
     of `P|V` with `(f|V + s)(x) = 0` and `(f|V + s)'(x)` Fredholm of index `i` in every chart of
     `P|V` (`IsIndexAt` on `P|V`). It is well defined: two local sections on `V`, `V'` restrict to
     `V ∩ V'` (item 362), where `IsIndexAt.unique` (Theorem 3.15 and the germ data on `P|V ∩ V'`)
     applies; it exists at every smooth point without bump functions (the section `−R(·, f(x))`
     on the chart domain, `hasScPlusSectionsThrough_of_chart`, and the germ data of `f + s` on
     `P|V`); a global section gives a local one (`V = X`); at a zero it is the index of `f'(x)`.
     The converse under bump functions is item 367.
365. **Proposition 6.2 is proved with the text's hypotheses** (`proposition_6_2_local`,
     `proposition_6_2_local'`, `isIndexAtLocal_eventually_const_of_path`,
     `exists_isScPlusSection_pullback_of_path_of_bump`,
     `exists_isScPlusSection_pullback_of_path_of_chart`,
     `hasScPlusSectionsThrough_pullback_rn_of_chart`,
     `isLinOfIndex_paramLift_sectionAdd_eventually_const_of_sections`; round-trip item V3.98 (a)).
     Let `f` be an sc-Fredholm section with tame germ data (Definition 3.51) of a strong bundle
     `P : Y → X` — **no bump functions** — and `φ : ℝ → X` an sc-smooth path. Then `ind(f, φ(t))`
     (Definition 6.1 with local sections) is one integer for all `t`, and any two values of the
     index at `φ(0)`, `φ(1)` agree. The proof is that of items 345–347 run on `P|V`, `V` the
     domain of a chart around `φ(t₀)`, exactly as the text does it: the path reparametrized into
     `V` (item 345), the section along the path `−R(·, f(φ(t)))` in the product chart **without
     cut-off** (`β = 1`: the product chart of `c|V` has base domain `ℝ × V`), the stabilizing
     sections `R(·, eᵢ)` on `ℝ × V` in the product chart (item 363), the local constancy of the
     index of `f̃ + S` along its zero set (`index_locally_constant_of_sections` on `π*(P|V)`), the
     slice relation (S) of item 346 (unchanged, applied on `P|V`), and the preconnectedness of
     `ℝ`. The hypotheses beyond the text: tame germ data in place of "tame strong bundle" (the
     project's reading of Definition 3.51, items 190–199), and paths on `ℝ` rather than `[0, 1]`
     (item 347 (i)); the bump functions are gone. Both `proposition_6_2` (global sections, bump
     functions) and `proposition_6_2_local` are kept.
366. **Bookkeeping and comparison.** New files, in this order after
     `Chapter3/IndexAlongPathsDevice` and `Chapter5/Homotopy` in `Polyfold.lean`:
     `Chapter3/RestrictOpen.lean` (imports `IndexAlongPathsDevice`, `StrongBundleMaximalAtlas`,
     `Chapter5/Homotopy`), `Chapter3/RestrictOpenGerms.lean` (imports `RestrictOpen`,
     `SectionCompactness`), `Chapter3/IndexLocallyConstantLocal.lean`,
     `Chapter3/IndexAlongPathsLocal.lean`, `Chapter3/IndexAlongPathsLocalBump.lean`; every
     `#print axioms` is standard. Suggested verdicts: V3.98 (a): "narrower" with the chips
     "paths on `ℝ`", "Definition 6.1 local section", and the diff "Proposition 6.2 is proved with
     the text's hypotheses (tame germ data, no bump functions) for Definition 6.1 read with a
     locally defined sc⁺-section (`proposition_6_2_local`), by the text's device on the
     restriction of `P` to a chart domain; the local and the global reading of Definition 6.1
     agree under bump functions (`isIndexAtLocal_iff_isIndexAt`), and with bump functions the
     proposition holds for global sections (`proposition_6_2`)"; drop the chip "+bump
     functions". V3.98 (b): the local constancy along the zero set holds with the text's
     hypotheses (`index_locally_constant_tame`); drop "+bump functions". Item 343 (i): the
     localization is done. V3.94 (Theorem 3.54) and V5.x (Lemma 5.11) unchanged. No gap entry
     changes.
367. **Under bump functions the two readings of Definition 6.1 agree**
     (`StrongBundle.cutoffSection_mem_oneSet_of_isChart`,
     `StrongBundle.isScPlusSection_cutoffSection_of_isChart`,
     `StrongBundle.IsIndexAtLocal.isIndexAt`, `StrongBundle.isIndexAtLocal_iff_isIndexAt`;
     `Chapter3/IndexAlongPathsLocalBump.lean`). For `X` admitting sc-smooth bump functions and an
     sc-Fredholm section `f`, `IsIndexAtLocal f x i ↔ IsIndexAt f x i`: the local section `s` on
     `V` is restricted to `W = dom φ ∩ V` (`φ` a chart around `x`), read in the chart as
     `τ : O → F¹`, and cut off by a bump `β` supported in `W` and equal to `1` near `x` (the
     cut-off of Lemma 5.11 in a chart of `P` that need not be in the atlas, through `oneChartOf`);
     `f + βτ` vanishes at `x`, and its linearization at `x` has the index of `(f|W + s)'(x)` since
     the two sections agree where `β = 1` (`linAt_congr` in the chart restricted to that set, and
     the germ datum of `f + βτ` at `x` for the chart independence). So Definition 6.1 of item 340
     (global section) and of item 364 (local section) are the same notion whenever Chapter 5's
     hypotheses hold, and only the local one is available without them.

## Chapter 4 (Manifolds with boundary with corners; Lean `Polyfold/Chapter4/`)

*Numbering.* The items of this section are numbered in blocks, one block per work package, so that
agents working at the same time do not collide; the gaps in the numbering are unused numbers, not
deleted items. 1–19: WP 4.1, the infrastructure of Chapter 4 (sc⁺-maps, Definitions 4.4 and 4.6,
Lemmas 4.5 and 4.7, Proposition 4.8, Remark 4.3, re-centring of charts and strong bundle charts);
20–39: WP 4.2 (Proposition 4.9 with Lemmas 4.11 and 4.12); 40–49: WP 4.3 (Lemma 4.10); 50–59:
WP 4.4 (Definition 4.1 and Theorem 4.2); 60–79: WP 4.5 (submanifolds, Definitions 4.13–4.21,
Theorem 4.18); 80–99: WP 4.6 (Theorem 4.22); 100–119: WP 4.7 (Sard and Theorem 4.23); 120–129: found
while writing the exposition (`Chapter4.md`, §4.4 of the preprint); 130–139: round-trip audit
findings recorded here only (Theorem 4.22's local faces); 140–149: Remark 4.3's example
(`Chapter4/RemarkFourThreeExample.lean`, `Chapter4/RemarkFourThreeFamily.lean`). Statement
numbers and pages are the preprint's *(book 2017: see `BookConcordance.md`)*.

Found while formalizing §4.1 in `Chapter4/ScPlus.lean` and `Chapter4/Recentre.lean` (2026-10-26).

1. **Charts centred at a point are used but never constructed, and they exist only at smooth
   points, with the partial quadrant `C` replaced by `C_e`.** Theorem 4.2 (ii) asks that every
   `x ∈ X` lie in a tame chart with `ψ(x) = 0`; the proof of Theorem 4.18 and Lemma 5.11 use charts
   and strong bundle charts centred at a given point *(book 2017: Theorems 4.1, 4.2, Lemma 5.3)* *(book 2021: unchanged, Theorem 4.1.2, p. 176; proof of Theorem 4.2.7, p. 188; proof of Lemma 5.3.3, p. 217)*. The
   text never says how such a chart is obtained from a chart `φ : V → O ⊆ C` of the atlas. The
   construction (`Polyfold.MChart.recentre`, `MPolyfold.exists_centredChart`,
   `MPolyfold.IsTame.exists_centredChart`) needs three things the text does not mention.
   (a) The point must be smooth: the translation `v ↦ v − e`, `e = φ(x)`, is sc⁰ only if `e ∈ E_∞`
   (`isScSmooth_sub_const`). In Theorem 4.2 (ii) every point is smooth (`X₀ = X_∞`), so the
   statement is meaningful there; for a general tame M-polyfold the centred tame chart exists at the
   points of `X_∞`. (b) `C − e` is not a partial quadrant unless `e ∈ C ∩ −C`; the model must be
   taken in the partial quadrant `C_e` of Definition 2.33, which is translation invariant
   (`C_e − e = C_e`, `image_sub_partialQuadrantAtWith`) but agrees with `C` only on the
   neighbourhood `G(e) = {λ_i > 0 for λ_i(e) > 0}` (`recentreNbhd_inter_eq`). The chart must
   therefore be restricted to `V ∩ φ⁻¹(G(e))` before it is translated (`MChart.restrict`, then
   `MChart.compDiffeo` with the sc-diffeomorphism `isScDiffeoQuadrant_translate`). (c) Tameness
   survives: on `G(e)`, `d_{C_e}(v − e) = d_C(v)` (`degIndex_sub_recentre`), the minimal subspaces
   `E_{v−e}` and the cones `C_{v−e}` of `C_e` are those of `v` in `C`
   (`minimalSubspaceWith_recentreIso`, `partialQuadrantAtWith_recentreIso`), and the translated
   retraction `r(u + e) − e` of a tame retraction restricted to `U ∩ r⁻¹(G) ∩ G` is tame
   (`ScRetraction.restrictIn_isTame`, `isTameRetract_recentre`). The re-centred chart is a chart of
   the M-polyfold (`MChart.recentre_isChart`). For strong bundle charts only the base is translated,
   `R_e(u, h) = (r(u + e) − e, Γ(u + e, h))`, `Φ_e = (Φ₁ − e, Φ₂)` (`StrongBundleChart.recentre`); it
   is a strong bundle chart of `P` (`StrongBundle.IsChart.recentre`) because `(e, 0)` is a smooth
   vector of both `E ⊕ F` and `E ⊕ F¹`, so the transition maps on `[0]` and `[1]` are the old ones
   composed with sc-smooth translations, and the conditions on the `F₁`-components carry over
   (`StrongBundleChart.Compatible.recentre`). No hypothesis is added beyond `x ∈ X_∞`.
2. **Definition 2.33 asserts without proof that `C_e` is a partial quadrant** *(book 2017:
   Definition 2.16)* *(book 2021: unchanged, Definition 2.5.1, p. 53)*. It is: reordering the half-line coordinates as `ℝ^{I(e)} ⊕ (ℝ^{rest} ⊕ W)`
   gives a presentation `T_e` of `C_e` (`recentreIso`, `partialQuadrantAtWith_eq_preimage`,
   `isPartialQuadrant_partialQuadrantAtWith`); the coordinates not vanishing at `e` become part of
   the linear factor. This is what item 1 (b) needs.
3. **"Sc⁺-map" is used but not defined, and the step "`Dr(o)` is an sc⁺-operator" is not
   justified** (proof of Lemma 4.7 (ii), p. 149 *(book 2017: Lemma 4.2; not checked against the
   2017 text, which is not available here)* *(book 2021: unchanged, Lemma 4.1.7 (2), p. 177)*). Definition 4.4 defines sc⁺ only for retractions and
   Definition 1.4 only for operators. The formalization defines sc⁺-maps on any `U` (`IsScPlus`: the
   lift `U → F¹` is sc-smooth) and proves the step as `IsScPlus.exists_scPlus_deriv`: at a smooth
   point the derivative of the lift `r¹ : U → E¹` is an sc-operator `E → E¹` (Proposition 1.16's
   remark), and `Dr(o) = ι ∘ Dr¹(o)` by the chain rule and the uniqueness of the derivative on a
   relatively open subset of a partial quadrant; it is then compact on every level
   (`IsScPlus.isCompactOperator_deriv`). The finite dimension of `Dr(o)E` uses that a compact
   projection has finite-dimensional range (Riesz; `finiteDimensional_range_of_isCompactOperator_of_idem`),
   which the text takes for granted. The composition rules are implicit too: Lemma 4.5 uses
   sc⁺ ∘ sc-smooth (`IsScPlus.comp_isScSmooth`); sc-smooth ∘ sc⁺ (`IsScSmooth.comp_isScPlus`) needs
   Proposition 1.17 for the outer map. In Definition 4.4 the condition `r(U_m) ⊆ U_{m+1}` is
   implied by the sc-smoothness of `r : U → U¹` (`IsScPlus.mem_range_succ`). No hypothesis is
   added.
4. **Proposition 4.8 and its chart form** *(book 2017: Proposition 4.1)* *(book 2021: unchanged, Proposition 4.1.8, p. 178)*. The proof is complete as
   written (`Polyfold.proposition_4_8`, with `1₀¹ = ScBanach.liftOne` as a map from `(O, C, E)` to
   `(O¹, C¹, E¹)`); in (⇐) the hypothesis `O₀ = O_∞` is used only to define `1₀¹` (`O ⊆ E₁` would
   do), and `O = O_∞` is then recovered from Lemma 4.7 (i). Theorem 4.2 (ii) uses the M-polyfold
   form, which the text does not state: for a chart `φ : V → O`, `O` is an sc⁺-retract iff
   `V ⊆ X_∞` and `1₀¹ : V → X¹` is sc-smooth (`MPolyfold.proposition_4_8_chart`, through the charts
   `(V₁, φ, (O₁, C₁, E¹))` of `X¹`, in which `1₀¹` is the lift `O → O¹`); and "`X₀ = X_∞` and
   `1₀¹ : X → X¹` sc-smooth" holds iff every chart of `X` is modelled on an sc⁺-retract
   (`MPolyfold.isScSmoothMap_toLevelOne_iff`). Slip: the proof ends "the lemma is proved".
5. **Remark 4.3** *(book 2017: unchanged, Remark 4.1, p. 132)* *(book 2021: misprint unchanged, Remark 4.1.3, p. 176, "`= X_i`"; an example of `X¹ ≠ X` is now given, the space of Subsection 1.4.4 with a dimension jump, see gap G.31)*. "`1₁⁰ : X¹ → X` is always sc-smooth" is
   `MPolyfold.remark_4_3_levelVal` (in charts it is the sc-operator `ι : E¹ → E`), and "if `1₀¹` is
   sc-smooth it is an sc-diffeomorphism" is `MPolyfold.remark_4_3_isScDiffeo`. "It is possible that
   `X¹ ≠ X` as M-polyfolds" is stated without an example and is **not formalized**. The sentence
   "`(X¹)_m = X_{m+1} = X_i` as sets" uses the identification of the levels of the M-polyfold `X¹`
   with those of `X`, which is not formalized (gap G.6), and "`= X_i`" is a misprint, presumably for `X₀` (if `X₀ = X_∞` all
   levels agree). "A finite-dimensional space with the constant structure has `X = X¹`" holds
   definitionally, `(ℝⁿ)¹ = ℝⁿ`, and every retract in `ℝⁿ` is an sc⁺-retract
   (`Polyfold.remark_4_3_const`).
6. **"A finite-dimensional space has exactly one sc-structure, the constant one" needs the density
   axiom** (Definition 1.1, remark; used in Definition 4.1, whose charts take values in
   finite-dimensional spaces). With condition (2) of Definition 1.1 (`E_∞` dense in every level) all
   inclusions `E_m → E₀` are onto: their ranges are finite-dimensional, hence closed, and contain
   the dense set `E_∞` (`ScBanach.toBase_surjective`), so `E ≅ E₀` with the constant structure
   (`ScBanach.scIsoConst`). Condition (1) alone does not suffice: `E₀ = ℝ`, `E_m = 0` for `m ≥ 1` is
   a scale with compact injective inclusions whose levels differ. Nothing is added; the remark is
   proved as stated.
7. Typos *(book?: the 2017 text is not available here)*: p. 148 (proof of Lemma 4.5, preprint line
   6086), "onto `s(V) = 0`" for `s(V) = O`; p. 150 (proof of Proposition 4.9, line 6170),
   "`p : E = T₀O ∩ Y → T₀O`" for `E = T₀O ⊕ Y` (the substance of the definition `p = Dt(0)` there is
   WP 4.2's); p. 149 (proof of Proposition 4.8), "the lemma is proved" for the proposition; p. 148
   (Remark 4.3), "`= X_i` as sets" (item 5).

Found while formalizing Proposition 4.9 with Lemmas 4.11 and 4.12 in `Chapter4/ScPlusGraph.lean`
(2026-10-26).

20. **Proposition 4.9: `p = Dt(0)` is not the projection along `Y`** (p. 150, lines 6147–6172
    *(book 2017: Proposition 4.2)*). The statement writes "`p = Dt(0) : E = T₀O ⊕ Y → T₀O` the
    sc-projection". `Dt(0)` is a projection onto `T₀O` (it is idempotent, `Dt(0) ∘ Dt(0) = Dt(0)`,
    with range `T₀O`), but along its kernel `ker Dt(0)`, and nothing in the hypotheses relates
    `ker Dt(0)` to the good complement `Y`, which is only assumed to be *a* good complement of
    `T₀O`. The proof uses both readings: `(1 − p)Dt(0) = 0` (Lemma 4.11, (76)) is true for any
    projection onto `T₀O`, but Lemma 4.12 decomposes `t(a + δ(a)) = p t(a + δ(a)) + δ(a)` with
    `δ(a) ∈ Y`, which needs `p` to be the projection along `Y`, and the solution set of
    `f(u) = (1 − p)(u − t(u))`, a section of `U ◁ Y`, needs `(1 − p)E = Y`. The formalization takes
    `p` to be **the projection along `Y`**, as two hypotheses of `Polyfold.proposition_4_9`
    (`p n = n` for `n ∈ N`, `p y = 0` for `y ∈ Y`), and proves what the text's arguments use:
    `(1 − p) ∘ Dt(0) = 0` and `Dt(0) = 1` on `N` on every level (`GraphData.qL_lvlDeriv_zero`,
    `GraphData.lvlDeriv_zero_of_mem_N`). (The misprint `E = T₀O ∩ Y` of line 6170 is item 7.)
21. **The good complement `Y` must be closed** (added hypothesis `hYc : IsClosed Y` of
    `proposition_4_9`, the same addition as Findings Chapter 3, items 81 and 93). The text asks for
    "a good complement `Y` of `T₀O`, so that `E = T₀O ⊕ Y`"; Definition 3.21 asks for an
    sc-complement, the remark after it allows "merely a topological complement", and the
    formalized `IsGoodComplement` records only the algebraic splitting. The projection `p` along
    `Y` is continuous iff `Y` is closed (`N` is finite-dimensional); nothing in Proposition 4.9
    works without a continuous `p`.
22. **The text's route through Lemma 4.10 and Corollary 3.47 does not give the conclusion.**
    Corollary 3.47 (`theorem_3_47`, `theorem_3_47_closed`; Findings Chapter 3, items 2, 80, 82)
    describes the solution set as the graph of `δ : V → Y'` where (a) `Y'` is the complement
    produced by Theorem 3.47 (`ψ⁻¹(Z ⊕ W)`), not the prescribed `Y`, so `δ` takes values in a
    different complement than Proposition 4.9's `Y` and `p` is a different projection; and (b) `δ`
    is sc-smooth only as a *germ*: it is `C^k` into `E_m` on a neighbourhood `V_{m,k}` depending
    on `m` and `k` (the shrinking `s_k = 2^k − 1` of the Germ-IFT, Finding 2). Proposition 4.9
    claims an sc-diffeomorphism `p : U₀ → V` between fixed open sets, whose inverse
    `a ↦ a + δ(a)` must be sc-smooth on the fixed `V`; the last paragraph of the proof
    ("having the sc-smooth map `a ↦ a + δ(a)` as its inverse") asserts exactly the property that
    Corollary 3.47 does not provide. Lemma 4.10 itself is correct (WP 4.3) but is not what the
    conclusion rests on. **The formalization gives a direct proof**, in which the sc⁺ property of
    `t` replaces the sc-Fredholm theory: `t : U_{k+1} → E_{k+1}` is `C¹` with
    `Dt(x) ∈ L(E_{k+1}, E_{k+1})` continuous in the operator norm (Proposition 1.16 for the lift
    `t¹ : U → E¹`, `ScRetraction.IsScPlus.hasFDerivWithinAt_lvlMap`, `continuousOn_lvlDeriv`), so
    the mean value estimate `‖(t z' − t z) − Dt(u₀)(z' − z)‖_{k+1} ≤ θ‖z' − z‖_{k+1}` holds on
    `C_{k+1} ∩ B(u₀, r)` for every `θ > 0` (`ScRetraction.IsScPlus.exists_mvt`; the text's
    integrals (77) and in Lemma 4.12 are this mean value inequality, taken on the convex set
    `C_{k+1} ∩ B(u₀, r) ⊆ U_{k+1}` since `U_{k+1}` need not be convex). Items 23–27 describe the
    steps.
23. **Lemma 4.11, generalized and used for uniqueness** *(book 2017: Lemma 4.4)*. What is needed,
    and proved, is: two points `u, u'` of `O` with `‖u‖₁, ‖u'‖₁ < r` and `p(u) = p(u')` coincide
    (`GraphData.exists_contraction_radius`: `‖(1 − p)(u' − u)‖₁ ≤ ‖1 − p‖θ‖u' − u‖₁` from
    `u = t(u)`, `u' = t(u')`, the mean value estimate at `0` and `(1 − p)Dt(0) = 0`;
    `GraphData.eq_of_p_eq`: then `u' − u = (1 − p)(u' − u)` forces `u' = u`). The text's version,
    "`y = δ(a)` for small solutions of `f = 0`", presupposes the `δ` of Corollary 3.47. The step
    "`|y|₁` is small if `a` and `y` are small on level `0`, since `t` is sc⁺" is where the sc⁺
    property converts level-`0` smallness into level-`1` smallness; it reappears as the choice of
    `W` (item 26).
24. **Lemma 4.12 as an existence statement** *(book 2017: Lemma 4.5)*. The text proves
    `a + δ(a) ∈ O` for the `δ` of Corollary 3.47; the formalization constructs the point
    (`GraphData.exists_graph_point`): for `a ∈ N ∩ C` with `‖a‖₁ < ρ`, the map
    `Φ_a(y) = (1 − p)t(a + y)` is a contraction of the complete set
    `B_a = {y ∈ Y₁ | ‖y‖₁ ≤ ε'‖a‖₁}` into itself (`ε' = ε/(‖ι₁‖‖lift_N‖ + 1)` with `ε` the good
    complement constant, so that `|y|₀ ≤ ε|a|₀` and `a + y ∈ C` for `y ∈ B_a`, a point to be
    checked since `t` is defined on `U ⊆ C` only; the contraction constant is `‖1 − p‖θ ≤ 1/2`
    and `Φ_a(B_a) ⊆ B_a` needs `‖1 − p‖θ(1 + ε') ≤ ε'`), and its fixed point `y` gives
    `u = a + y` with `(1 − p)(t(u) − u) = 0`, i.e. `t(u) − u ∈ N`. Then the text's argument: with
    `w = t(u)`, `t(w) = t(u)` and `Dt(0)(w − u) = w − u`, the mean value estimate gives
    `‖w − u‖₁ ≤ θ‖w − u‖₁`, so `t(u) = u` and `u ∈ O`. The text's "`|a(τ)|₁ ≤ ε₁` if `|a|₀ < ε`
    and `ε` is sufficiently small" needs the level-`1` continuity of `t` at `0` for the point
    `w = t(u)` (the radius `r' ≤ δ` of the proof). (Round-trip item V4.22: the text's form — for a
    given solution germ `δ` of `(1 − p)(id − t)(a + δ(a)) = 0`, the points `a + δ(a)` with
    `|a|₀ < ε` lie in `O` — is true and proved outright from the text's setting,
    `RoundTrip/Items/V4_22.lean`, `B_holds`; the project's existence lemma does not give it without
    the uniqueness of Lemma 4.11, and it is not in the project.)
25. **`p(O ∩ W) ⊆ C` is never checked.** The conclusion `p : U₀ → V` with `V ⊆ T₀O ∩ C` needs
    `p(u) ∈ C` for `u ∈ O` near `0`, which is not automatic (`p` is a linear projection, `C` a
    quadrant). It follows from the contraction estimate at `u' = u`, `u = 0`:
    `‖(1 − p)u‖₁ ≤ ‖1 − p‖θ‖u‖₁`, hence `|(1 − p)u|₀ ≤ ε|p(u)|₀` when
    `2‖ι₁‖(‖1 − p‖θ)‖lift_N‖ ≤ ε`, and the good complement property then gives
    `p(u) ∈ C ↔ p(u) + (1 − p)u = u ∈ C` (`GraphData.p_mem_C`). This is the third constraint on
    `θ` (`GraphData.exists_nbhd`).
26. **The neighbourhoods.** The text's `U₀ = {a + δ(a) | a ∈ V}` is "an open set in `O`"; here
    `U₀ = O ∩ W` with `W = B₀(0, δ₀) ∩ p⁻¹(V')` open in `E₀`, `V = V' ∩ C` with
    `V' = {a ∈ N | ‖a‖₁ < ρ'}` open in `N`, and `Γ : V → O ∩ W`, `Γ(V) = O ∩ W`, `p ∘ Γ = 1`,
    `Γ ∘ p = 1` (`GraphData.Nbhd`, `exists_nbhd`). The points of `O ∩ W` satisfy `‖u‖₁ < r` because
    `u = t(u)` and `t : U → E₁` is continuous at `0` (sc⁰ of the lift); this is what makes the
    level-`1` uniqueness and existence statements usable on a neighbourhood that is open on level
    `0`, as the statement requires.
27. **Regularity on the fixed `V`: the frame formula and the `C^k`-bootstrap.** (i) `Γ` is
    continuous into every level `E_m` on `V`: `Γ₁` is Lipschitz by the contraction estimate
    (`‖u' − u‖₁ ≤ 2‖lift_N‖|a' − a|`), and `Γ_{m+1} = t ∘ Γ_m` with `t : U_m → E_{m+1}` continuous
    (`Nbhd.continuousOn_Γ_lvl`). (ii) `Γ` is differentiable into every `E_{m}` at every `a ∈ V`
    with `DΓ(a) = Dt(Γ(a))|_N ∘ (p ∘ Dt(Γ(a))|_N)⁻¹` (`Nbhd.hasFDerivWithinAt_Γ_lvl`): the
    abstract statement is `hasFDerivWithinAt_of_projection` — for a map `s` with the mean value
    estimate at `u₀` and continuous linear `q`, `B` with `q ∘ B = 1`, `(1 − Bq) ∘ Ds(u₀) = 0`,
    every continuous right inverse `Γ` of `q` with values in `{s = 1}` has `DΓ(q(u₀)) = B`.
    Here `s = t` on level `m`, `q = p`, and `B = B_{u₀}` is the inverse of `p|_{T_{u₀}O}`, which
    exists because `A(u₀) = p ∘ Dt(u₀)|_N` is invertible (`A(u₀) = 1 + O(θ₀)`,
    `GraphData.A_injective`) and `T_{u₀}O ∩ Y = 0` (`GraphData.eq_zero_of_mem_Y_of_scDeriv_eq`:
    for `v ∈ T_{u₀}O ∩ Y`, `v = (1 − p)v = (1 − p)(Dt(u₀) − Dt(0))v` on level `1`). The mean
    value estimate is applied at `u₀ = Γ(a)`, not at `0`, with the projection `1 − B_{u₀}p` onto
    `Y` along `T_{u₀}O` in place of `1 − p`: this is why the regularity holds at every point of
    the fixed `V` and not only near `0`. (iii) `C^k ⇒ C^{k+1}`: if `Γ` is `C^k` into every level
    then `a ↦ A(Γ(a))`, `a ↦ A(Γ(a))⁻¹` and `a ↦ Dt(Γ(a))|_N ∈ L(N, E_{j+1})` are `C^k`, because
    derivatives of `t` are only applied to vectors of the finite-dimensional smooth `N` and
    `(x, w) ↦ Dt(x)w` is `C^k` as a map `U_{j+k+1} × E_{j+k+1} → E_{j+1}` (Proposition 1.18 for
    the tangent map of the lift `t¹`, `GraphData.contDiffOn_lvlDeriv_apply`); the extra levels
    are absorbed by `Γ` being `C^k` into *every* level (`Nbhd.contDiffOn_Γ_lvl`,
    `contDiffOn_lvlDeriv_Γ`, `contDiffOn_A_Γ`, `contDiffOn_M_Γ`). So the level loss of `Tt` does
    not accumulate, and `IsScSmooth.of_contDiffOn_levels` (Proposition 1.19) gives `Γ` sc-smooth
    on `V` (`Nbhd.isScSmooth_Γ`). This replaces the germ-only regularity of Corollary 3.47
    (item 22 (b)).
28. **The statement as formalized and its remaining hypotheses.** `Polyfold.proposition_4_9`:
    for `t` an sc⁺-retraction onto `O ∋ 0`, `N = T₀O` (the hypothesis `(N : Set E) = T₀O` with
    `T₀O` of Definition 2.17; `[FiniteDimensional ℝ N]` is a hypothesis only to form the
    sc-Banach space `N`, and is Lemma 4.7 (ii), `finiteDimensional_tangentSpace_zero`), `N` in
    good position to `C`, `Y` a closed good complement, `p` the projection along `Y`: there are
    `W`, `V`, `Γ` as in item 26 with `Γ` sc-smooth on `V`, `Γ(a) − a ∈ Y`, `Γ(0) = 0`, and `p`,
    `Γ` sc-smooth between the retracts `(O ∩ W, C, E)` and `(V, N ∩ C, N)` in the sense of
    Definition 2.7 (`IsScSmoothRetractMap`), mutually inverse — the sc-diffeomorphism of the
    statement; `(V, N ∩ C, N)` is a local model (`IsRelOpenInQuadrant`, through Proposition 3.22
    for `N ∩ C`). No hypothesis is added beyond `Y` closed. The naive shortcut, inverting `p ∘ t`
    on the finite-dimensional quadrant `N ∩ C` by Proposition 3.73, is not available: `p ∘ t`
    need not map a neighbourhood of `0` in `N ∩ C` onto a neighbourhood of `0` (plan, §0.2:
    `E = ℝ³`, `C = [0, ∞)² × ℝ`, `O = {(a, a₂²)}`, `t(x) = Γ(x₁ + (x₃ − x₂²)², x₂)`, where
    `p ∘ t` maps the quadrant onto `{x₁ ≥ x₂⁴}`). Typos: line 6140 "the the relatively open
    subset"; the letter `U` is used both for the domain of `t` and for the neighbourhood `U₀` of
    `0` in `O` (statement and last paragraph of the proof).

Found while formalizing Definition 4.1 and Theorem 4.2 in `Chapter4/Characterization.lean`
(2026-10-26).

50. **Definition 4.1 allows charts of several dimensions; the constant sc-structure is no
    restriction** (p. 147 *(book 2017: Definition 4.1)*). The charts `(V, φ, (U, C, ℝⁿ))` may have
    different `n`, so the definition (`MPolyfold.HasCornerStructure`: an atlas of corner charts
    `MChart.IsCornerChart`, equivalent to the atlas of `X`) is not `IsManifoldWithCorners n` of
    Theorem 3.27, which fixes `n`; that is the special case of a corner structure all of whose
    charts have dimension `n` (`MPolyfold.isManifoldWithCorners_iff`). The corner charts are
    modelled on `ScBanach.const V`, as the text says ("with the constant sc-structure"); nothing is
    lost by this: a chart onto a relatively open subset of a partial quadrant in any sc-Banach
    space with finite-dimensional `E₀` is, with the same map, a corner chart for the constant
    structure (`MChart.exists_isCornerChart_of_finiteDimensional`, through `ScBanach.scIsoConst`,
    item 6), so `HasCornerStructure` is equivalent to the condition `IsManifoldWithCornersLoc` of
    `GlobalIFTTheorems.lean` (`MPolyfold.hasCornerStructure_iff_finiteDimensional`). That the
    dimension is locally constant (invariance of dimension for the transition maps) is neither
    said nor needed, and is not formalized. "`φ : V → U` is an sc-diffeomorphism" and
    "sc-smoothly compatible charts" are read as compatibility with the M-polyfold structure of
    `X` (equivalence of atlases, as in Definition 2.37 for tameness); the definition is local
    (`MPolyfold.hasCornerStructure_iff`).
51. **The transition maps are `C^∞`, with one-sided derivatives at the boundary**
    (`MChart.IsCornerChart.contDiffOn_transition`): the text's "and therefore are classically
    smooth maps, i.e., of class `C^∞`" is sc-smooth = `C^∞` on relatively open subsets of partial
    quadrants in finite dimensions (`isScSmooth_iff_contDiffOn_const`, Chapter 1), applied on the
    overlap `χ(V ∩ V')`, which is relatively open (`MChart.isRelOpenInQuadrant_overlap`). "The
    atlas defines the structure of a smooth manifold with boundary with corners" is not formalized
    beyond this (the classical notion is not in the project; Mathlib's `ModelWithCorners` has one
    model space, here the partial quadrants vary from chart to chart).
52. **Theorem 4.2 does not use tameness** (p. 147 *(book 2017: Theorem 4.1)*). Neither the
    hypothesis "`X` tame" nor the word "tame" in (ii) enters the proof of (ii) ⇒ (i):
    Propositions 4.8 and 4.9 apply to every chart whose model is an sc⁺-retract with `T₀O`
    finite-dimensional and in good position (`MPolyfold.hasCornerStructure_of_centred`). And (i)
    makes `X` tame, its corner charts being modelled on the tame retracts `(U, C, ℝⁿ)` with the
    identity retraction (`MPolyfold.HasCornerStructure.isTame`). So the equivalence holds for every
    M-polyfold (`MPolyfold.theorem_4_2_general`), and (ii) with or without "tame" are equivalent;
    `MPolyfold.theorem_4_2` is the text's statement, with the hypothesis unused.
53. **(i) ⇒ (ii) proves only the first half of (ii).** The proof checks "`U = U_∞` and
    `1₀¹ : U → U¹` is sc-smooth" in a corner chart and concludes (ii); it does not produce the
    chart with `ψ(x) = 0`, nor `T₀O` finite-dimensional and in good position. (a) The centred chart
    is the corner chart re-centred at `x` (item 1): `φ − φ(x)` on `φ⁻¹(G(φ(x)))`, modelled on a
    relatively open subset of the partial quadrant `C_{φ(x)}` — not of `C` — in the same
    finite-dimensional space (`MChart.IsCornerChart.exists_centred`); the re-centring needs
    `φ(x)` smooth, which holds because all levels of a finite-dimensional sc-space agree
    (`ScBanach.mem_smooth_of_finiteDimensional`, item 6). (b) Its tangent space at `0` is the whole
    space, `T₀U = E` for the identity retraction (`tangentSpace_relOpen`), finite-dimensional, and
    `E` is in good position to `C` with the good complement `0`, the interior of a partial
    quadrant being nonempty (`isInGoodPosition_top`); the chart is tame
    (`MChart.IsCornerChart.exists_centred_tame`). (c) "`X₀ = X_∞` and `1₀¹ : X → X¹` sc-smooth"
    follows from the chart statements by Proposition 4.8 in each chart, every corner model being an
    sc⁺-retract (`remark_4_3_const`), and the locality of sc-smoothness
    (`MPolyfold.isScSmoothMap_toLevelOne_of_cover`).
54. **(ii) ⇒ (i) needs no added hypothesis: the closed good complement is chosen.** The proof
    applies Proposition 4.9, which (as formalized, items 20–21) needs `p` to be the projection onto
    `T₀O` along a *closed* good complement `Y`. In Theorem 4.2 no complement is prescribed, so one
    can be chosen: the normal form of Proposition 3.22 gives a continuous projection `π` onto
    `T₀O` whose kernel is a good complement, closed, with even `π(C) ⊆ C`
    (`exists_proj_goodComplement`). With this `Y` the issue `p = Dt(0)` of item 20 does not arise,
    and Theorem 4.2 is proved as stated (`CornerChartData`, `exists_cornerChartData`). The step
    "it follows that `O₀ = O_∞` and `1₀¹ : O → O¹` is sc-smooth; by Proposition 4.8 the sc-retract
    `(O, C, E)` is an sc⁺-retract" is the chart form of Proposition 4.8 (item 4,
    `MPolyfold.isScSmoothMap_toLevelOne_iff`).
55. **The compatibility of the charts `p ∘ ψ` is not argued.** "Carrying out this construction
    around every point `x ∈ X`, we obtain a smoothly compatible atlas" (p. 157): (i) requires the
    charts `p ∘ ψ` to be compatible with the M-polyfold structure of `X` and with each other. For
    a chart `φ'` of `X` the transition maps are `(φ' ∘ ψ⁻¹) ∘ Γ` and `p ∘ (ψ ∘ φ'⁻¹)`; they are
    sc-smooth between the overlap retracts by the chain rule (Theorem 2.8) because `p` and its
    inverse `Γ` are sc-smooth *between the retracts* `(O ∩ W, C, E)` and `(V, T₀O ∩ C, T₀O)`
    (Definition 2.7), which is what `proposition_4_9` provides (`MChart.compRetract`,
    `MChart.compRetract_isChart`; `MChart.compDiffeo` of Chapter 3 covers only sc-diffeomorphisms
    of relatively open sets, and `p` is not one). Two charts `p ∘ ψ` are then compatible by the
    locality of compatibility (`MPolyfold.IsChart.compatible`), and their atlas is equivalent to
    that of `X` (`MPolyfold.hasCornerStructure_iff`) — the pattern of `theorem_3_27_isChart` /
    `theorem_3_27_atlas_equiv`. The chart itself is `CornerChartData.chart`, `p ∘ ψ` on
    `ψ⁻¹(W)` with inverse `ψ⁻¹ ∘ Γ` (`MPolyfold.theorem_4_2_chart`). Its model
    `(V, T₀O ∩ C, T₀O)` lives in the finite-dimensional space `T₀O`, not in `ℝⁿ`, as Definition
    4.1's "(or in a finite-dimensional vector space `E`)" allows; `T₀O ∩ C` is a partial quadrant
    by Proposition 3.22.
56. Typos and slips *(book?: not checked against the 2017 text)*: p. 147, line 6030,
    "compatatible"; p. 156, line 6404, "sbset"; line 6409, "sc-diffeomorphsim"; "tame sc-smooth
    polyfold chart" (lines 6054, 6399) for M-polyfold chart; in the last paragraph of the proof
    the letter `V` denotes both the domain of `ψ` in `X` and the neighbourhood of `0` in
    `T₀O ∩ C` ("`V₀ = ψ⁻¹(O') ⊂ V`, the composition `V₀ → O' → V` is a sc-diffeomorphism onto the
    finite-dimensional model `(V, T₀O ∩ C, T₀O)`"), and the neighbourhood called `U` in
    Proposition 4.9 is called `O'` there.
57. **Lemma 4.10 is not formalized** (p. 151, lines 6188–6278 *(book 2017: Lemma 4.3)* *(book 2021: unchanged, Lemma 4.1.11, pp. 179–180: slips (a), (c), (d), (f), (g) as before; in (b) the sc⁺-operators are now `Dt(u)` and `p`)*; WP 4.3,
    items 40–49 are left free for it). It is no longer used: Proposition 4.9, the only place the
    text applies it, is proved directly (items 22–27), and Theorem 4.2 rests on Proposition 4.9.
    What the statement needs and the project does not have: the trivial strong bundle `U ◁ Y → U`
    as a `StrongBundle` over the M-polyfold `U` (total space `U × Y`, fibrewise vector space
    structures, a one-chart strong bundle atlas), `Y` and `W = Y ∩ F` as sc-subspaces
    (`ScBanach.ofSubspace`), the sc-isomorphism `E ≅ (T₀O ⊕ B) ⊕ W` onto a parameter product, and
    at every smooth `u` the re-centred strong bundle chart (item 1), the trivial filler, the
    sc⁺-section `s(v) = f(u) + (1 − p)[t(u) − t(u + v)]` and the strong bundle isomorphism
    `(u + v, b + w) ↦ (v, b + w)` conjugating `g − s = (1 − p)v` to the basic germ
    `(a + b, w) ↦ (b, w)` with contraction part `0`. Read against the text, the proof has these
    slips and gaps: (a) line 6196, `Df(u)h = h − (p(h) − (1 − p)Dt(u)h)` should read
    `h − (p(h) + (1 − p)Dt(u)h)`; (b) lines 6198–6199, "since `Df(u)` is a sc⁺-operator" should be
    `Dt(u)`, and "the operator `Df(0)`" is presumably `Df(u)`; moreover `Df(u) = (1 − p)(1 − Dt(u))`
    maps `E` into `Y`, so it is sc-Fredholm as the composition of `1 − Dt(u) : E → E` (Proposition
    1.10) with the surjection `1 − p : E → Y` of finite-dimensional kernel `T₀O`, not as "a
    perturbation of the identity"; (c) line 6231, "`L(T₀O) = B' ⊕ W'`" should be `L(Y) = B' ⊕ W'`;
    (d) line 6216, the algebraic complement `B` of `W = Y ∩ F` in `Y` must be chosen inside
    `Y_∞`, otherwise `Y = B ⊕ W` is not an sc-splitting (a finite-dimensional sc-subspace
    consists of smooth points; possible because `W` has finite codimension in `Y` and `Y_∞` is
    dense in `Y`); (e) line 6236, "`T₀O ⊕ B` is in good position to `C` because it has a
    sc-complement contained in `C`" omits the other half of Definition 3.21, that `(T₀O ⊕ B) ∩ C`
    has nonempty interior in `T₀O ⊕ B` (true: the projection along `W ⊆ C` maps `C` onto
    `(T₀O ⊕ B) ∩ C` and is open); (f) the passage to the smooth point `u` ("the map `v ↦ u + v`
    ... maps an open neighborhood of `0` in `C_u` to an open neighborhood of `u` in `C`") is the
    re-centring of item 1, and `Y` itself must be an sc-subspace for `U ◁ Y` to be a strong
    bundle (true: `Y` is closed, item 21, and `(1 − p)` maps the dense `E_∞` onto a dense subset of
    every `Y_m` since `T₀O ⊆ E_∞`); (g) line 6165, "there exists `ε₀ > 0`" and then `ε` in the
    inequality.

Found while formalizing §4.2 (Definition 4.13 to Definition 4.21) in `Chapter4/Submanifolds.lean`
(2026-10-26).

60. **Definition 4.13 as formalized** *(book 2017: Definition 4.4)*. `MPolyfold.IsSmoothSubmanifold`:
    every `a ∈ A` has an open `V ∋ a` and `s` with `MPolyfold.IsScPlusRetractionOn s V` (Definition
    4.4 on an open subset of an M-polyfold: `s` sc-smooth on `V`, `s(V) ⊆ V`, `s ∘ s = s`,
    `s(V) ⊆ X₁` and `1₀¹ ∘ s : V → X¹` sc-smooth) and `s(V) = A ∩ V`; the data are
    `MPolyfold.SubmanifoldData`.  An sc⁺-retraction is an sc-smooth retraction, so `A` is a
    sub-M-polyfold (`IsSmoothSubmanifold.isSubMPolyfold`, `SubmanifoldData.toSubData`) and carries
    the induced structure `subPolyfold` of Proposition 2.21.  The text never reads the sc⁺
    condition in charts; the whole section rests on it: for a chart `φ` of `X` and
    `W = V ∩ dom φ ∩ s⁻¹(V ∩ dom φ)` (the set of the proof of Proposition 2.21), the lift
    `1₀¹ ∘ (φ ∘ s ∘ φ⁻¹) : φ(W) → E¹` is sc-smooth between the retracts `φ(W)` and `O₁`
    (`SubmanifoldData.isScSmoothRetractMap_lift`, the condition "`1₀¹ ∘ s` sc-smooth" read in the
    chart `φ` and the level chart `(V₁, φ, (O₁, C₁, E¹))` of `X¹`), so that
    `t = (φ ∘ s ∘ φ⁻¹) ∘ r`, on `U ∩ r⁻¹(G)` with `φ(W) = O ∩ G`, is an **sc⁺-retraction onto
    `φ(W ∩ A)`** (`SubmanifoldData.exists_chartRetraction`): the model of every induced chart of
    `A` is an sc⁺-retract (`SubmanifoldData.isScPlusRetract_image`).  No hypothesis is added.
61. **Remark 4.14** *(book 2017: Remark 4.3)*. "`T_aA = Ts(a)(T_aX)`; `Ts(a)` is an sc⁺-operator,
    hence level-wise compact, so `T_aA` is finite-dimensional" presupposes the linear and
    sc-structure of `T_aX` (gap G.7).  In a chart (`SubmanifoldData.remark_4_14`): the tangent
    space `T_z(φ(W ∩ A))` of the chart model of `A` is the image of `T_zO` under the tangent map of
    `ρ = φ ∘ s ∘ φ⁻¹ : φ(W) → φ(W)` (Proposition 2.21 (4) for `ρ`, with `T_z(φ(W)) = T_zO` by the
    germ property `tangentSpace_inter_isOpen`), it lies in `T_zO`, and it is finite-dimensional
    because it is `Dt(z)E` for the sc⁺-retraction `t` of item 60 (Lemma 4.7 (ii): the sc⁺-operator
    is `Dt(z)`, not `Ts(a)`); `z` is smooth (Lemma 4.7 (i) for `t`).  The last sentences ("near
    points with `d_X(a) = 0` `A` is a manifold in the classical sense; the same if `T_aA` is in good
    position") are forward references to Theorem 4.18: at a point with `d_X(a) = 0` the good
    position is automatic, `C_aX = T_aX` and any complement is good
    (`isGoodPositionAt_of_degIndex_eq_zero`), and if `d_X = 0` on all of `A` the induced structure
    has a corner structure **without tameness of `X`** (`hasCornerStructure_of_degIndex_eq_zero`,
    in the chart re-centred at a point of index `0`, whose partial quadrant is the whole space).
    The local form "near such points" (for the open piece `A ∩ {d_X = 0}`) is not formalized.
    (Round-trip item V4.32: it follows by applying `hasCornerStructure_of_degIndex_eq_zero` to
    `A ∩ {d_X < 1}`, `RoundTrip/Items/V4_32.lean`, `A_to_B1`; the second claim, a corner structure
    near a point where `T_aA` is in good position without tameness of `X`, is a local Theorem 4.18
    that the project does not have.)
62. **Proposition 4.15 (1) and (4)** *(book 2017: Proposition 4.3)*. (1) "Since a sc⁺-retraction
    `s` has its image in `X_∞`" is Lemma 4.7 (i), which is about retracts in sc-Banach spaces; on
    `X` it holds through the chart retraction `t` of item 60 (`IsSmoothSubmanifold.subset_smoothSet`).
    The text does not distinguish `A ⊆ X_∞` from `A = A_∞` for the induced structure; the latter
    holds because the levels of the induced structure are the traces of those of `X`
    (`mem_levelSet_subPolyfold_iff`; `proposition_4_15_1`).  (4) "The postulated sc⁺-retraction is
    the identity on the retract `A`, and `A = A_∞`, so `1₀¹ : A → A¹` is sc-smooth" skips the
    argument: `1₀¹ : A → A¹` is sc-smooth because every point of `A` lies in an induced chart whose
    model `φ(W ∩ A)` is an sc⁺-retract (item 60), and Proposition 4.8 holds in each such chart
    (`isScSmoothMap_toLevelOne_of_cover`; `proposition_4_15_4`).  Paracompactness of `A` is the
    instance argument `[ParacompactSpace A]` of `subPolyfold` (proved for every subset by
    `MPolyfold.paracompactSpace_subtype`); no hypothesis is added.
63. **Proposition 4.15 (2): the definition of "locally closed" is garbled** (p. 158, lines
    6463–6466): "every point `a ∈ A` possesses an open neighborhood `V(a)` having the property that a
    point `b ∈ V(a)` belongs to `A`, if `U ∩ A ≠ ∅` for all open neighborhoods `U` of `b`" (the
    letter `U` is free, and "`U ∩ A ≠ ∅` for all `U ∋ b`" means `b ∈ cl(A)`).  Read as "`V(a) ∩ cl(A) ⊆ A`",
    it is condition (4) of Mathlib's `isLocallyClosed_tfae`, equivalent to `IsLocallyClosed A`
    (the intersection of an open and a closed set), which is what is proved
    (`proposition_4_15_2`).  The proof's sequence `a_k → b` needs `X` metrizable (Theorem 2.16);
    the formalization uses the filter `𝓝[A ∩ V] b` instead.
64. **Proposition 4.15 (3)** is Lemma 2.26 (`d_A(a) ≤ d_X(a)`; `proposition_4_15_3`:
    `Subtype.val '' ∂A ⊆ ∂X`).  The text's argument "if `d_X(a) = 0`, a neighbourhood of `a` is
    sc-diffeomorphic to a retract `(O, E, E)`" needs the chart re-centred at `a` (Finding 1): a chart
    with `d_C(φ(a)) = 0` is modelled on `(O, C, E)`, and only `C_{φ(a)}` is the whole space.  Typo:
    "`d_A(x) ≥ 1`" for `d_A(a) ≥ 1` (lines 6473, 6487).
65. **The open question (p. 159, lines 6497–6510) is not formalized.**  It asks whether a
    sub-M-polyfold `A` with `A = A_∞` and `dim T_aA` finite and locally constant is a smooth
    finite-dimensional submanifold, i.e. whether `1₀¹ : A → A¹` is then sc-smooth, and whether the
    "T" `{(x, 0) | −1 < x < 1} ∪ {(0, y) | 0 ≤ y < 1}` is homeomorphic to a retract `O = O_∞` of an
    sc-Banach space.  Its last sentence ("from our previous discussion this is impossible if we
    require `O` to be an sc⁺-retract") is, for a retract `(O, E, E)` without boundary, the statement
    that an sc⁺-retract in `E` is a manifold (`hasCornerStructure_of_degIndex_eq_zero` for `A = O`,
    item 61) together with the fact that the "T" is not a topological manifold (not formalized).
66. **Definitions 4.16 and 4.21 in charts, and their chart independence** *(book 2017: Definitions
    4.5, 4.7)*.  Both are stated in `T_aX`, which has no linear structure here (gap G.7).  They are
    formalized as conditions in a chart (`SubmanifoldData.IsGoodPositionChart`,
    `SubmanifoldData.IsGeneralPositionChart`; on retracts `IsGoodPositionRetractAt`,
    `IsGeneralPositionRetractAt`) for the data of Definition 4.13, a chart `φ`, a presentation `T`
    of the partial quadrant and the level-`1` point `z` over `φ(a)`: `T_z(φ(W ∩ A))` is in good
    position to `C_z` inside `T_zO` (`IsInGoodPositionIn`), resp. has in `T_zO` an sc-complement
    `B ⊆ T_zO ∩ E_z = T_z^R O` (an sc-subspace with `(T_zO)_m = (T_zA)_m ⊕ B_m` on every level).
    The explicit form of the brief, "`range D(φ ∘ s ∘ φ⁻¹ ∘ r)(φ(a))` in good position inside
    `T_{φ(a)}O` to `C_{φ(a)}`", is `SubmanifoldData.isGoodPositionChart_iff`.  The M-polyfold
    notions `MPolyfold.IsGoodPositionAt`, `MPolyfold.IsGeneralPositionAt` ask for one choice; the
    text implies, without proof, that the choice does not matter, and this is proved
    (`IsGoodPositionAt.isGoodPositionChart`, `isGoodPositionAt_iff_forall`, and the same for general
    position): the transition `τ = φ' ∘ φ⁻¹` is a germ of sc-diffeomorphisms between the overlap
    retracts carrying `φ(H ∩ A)` onto `φ'(H ∩ A)`; `D(τ ∘ r)(z)` maps `T_zO` isomorphically onto
    `T_{z'}O'`, the partial cones onto each other and `T_z^R` onto `T_{z'}^R` (Proposition 2.30),
    and `T_zA` onto `T_{z'}A` (`scDeriv_mem_tangentSpace_of_subset`: the derivative of a map between
    retracts maps tangent spaces of sub-retracts into each other).  Good position inside a subspace
    is transported by Lemma 3.45 (`IsInGoodPositionIn.transport`); the sc-complement is transported
    level by level, which needs the point to be smooth (`D(τ ∘ r)(z)` is then an sc-operator), true
    on `A`.  The tangent space of a retract depends only on its germ (`tangentSpace_inter_isOpen`),
    which takes care of the different sets `W` and of the overlaps.  Neither definition nor its
    chart independence needs `X` tame (Definition 4.16 assumes it so that `C_aX` is a partial
    quadrant, Proposition 2.36; the chart form uses `C_z` and does not need that).
67. **Definition 4.17** *(book 2017: Definition 4.6)* is `MPolyfold.IsTameSubmanifold`: the induced
    structure `subPolyfold` (which depends only on `A`) is tame.
68. **Theorem 4.18: the route through Theorem 4.2 and the steps the text skips** *(book 2017:
    Theorem 4.2, p. 142)* *(book 2021: unchanged, renumbered, Theorem 4.2.7, pp. 188–189: "Proposition 4.1.2" for Theorem 4.1.2; `V(a) = ϕ⁻¹(V₀) ∩ A` as before)*.  `MPolyfold.theorem_4_18`: `X` tame, `A` a smooth finite-dimensional
    submanifold in good position at every point ⇒ the induced structure has a corner structure
    (`HasCornerStructure`, Definition 4.1) and `A` is tame.  As the text says ("based on
    Proposition 4.2", meaning Theorem 4.2), the proof applies Theorem 4.2 (ii) ⇒ (i) to the
    M-polyfold `A` (`hasCornerStructure_of_centred_isInGoodPosition` through
    `hasCornerStructure_of_centred`): `A = A_∞` and `1₀¹` sc-smooth (Proposition 4.15 (4)), and at
    every `a` the induced chart from a tame chart `ψ` of `X` centred at `a`, whose model `ψ(W ∩ A)`
    has `T₀ = Dt(0)E` finite-dimensional and in good position to `C` in `E`
    (`IsGoodPositionAt.isInGoodPosition_of_tame`: the chart condition in `ψ`, by chart
    independence, and Lemma 4.19 with `π = Dr(0)`).  What the text skips: (a) the chart
    `ϕ : (V, a) → (O, 0)` exists only after re-centring at the smooth point `a`, with `C` replaced by
    `C_{φ(a)}` (Finding 1; `IsTame.exists_centredChart`); (b) "taking `V` and `U` small, we may
    assume `V = ϕ⁻¹(O)`": what is needed is `s(W) ⊆ W ⊆ dom ϕ`, i.e. the set `W` of Proposition 2.21,
    and `r` restricted to `U ∩ r⁻¹(G)`, `ϕ(W) = O ∩ G`, so that `ϕ ∘ s ∘ ϕ⁻¹ ∘ r` is defined (item
    60); (c) "it is a sc⁺-retraction since `s` is" needs the sc⁺ condition read in charts (item 60);
    (d) "`p = Dt(0)`": `p` must be the projection along a closed good complement (Findings 20–21);
    Theorem 4.2's proof chooses it by the normal form (Finding 54), not as the text's `Y ⊕ Z`;
    (e) the compatibility of the charts `p ∘ ϕ` is not argued (as in Theorem 4.2, Finding 55).
    Tameness of `X` enters only through Lemma 4.19.  No hypothesis is added.  Slip: "`V(a) = ϕ⁻¹(V₀) ∩ A`"
    (line 6596) should be `(p ∘ ϕ)⁻¹(V₀) ∩ A` (or `ϕ⁻¹(V₁) ∩ A`): `V₀ ⊆ N ∩ C` is not a subset of `O`.
69. **Lemma 4.19: "`z ∈ Z ⊂ C`" does not give the converse direction** *(book 2017: Lemma 4.6)* *(book 2021: unchanged, Lemma 4.2.8, p. 188)*.
    The proof (lines 6563–6566) concludes `n + y ∈ C` from `n + y + z ∈ C` "since `z ∈ Z ⊂ C`"; this
    needs `−z ∈ C`, i.e. `Z ⊆ C ∩ (−C)` (in `C = [0, ∞)`, `z = 1`, `n + y = −1/2` is a
    counterexample to the inference from `z ∈ C`).  It holds because the sc-complement of
    Proposition 2.35 at the corner `0` lies in the minimal subspace `E₀ = {λ_i = 0, i ∈ I(0)}`, a
    linear subspace contained in `C`; the formalization uses exactly `(1 − Dr(0))E ⊆ E₀`
    (`lemma_4_19`, `isGoodComplement_sup_range`: adding `k ∈ E₀` does not change membership in
    `C`).  The text's norm `|(y, z)|₀ = |y|₀ + |z|₀` on `Y ⊕ Z` is not the norm of `E` used in
    Definition 3.21; the two are comparable because `y = π(y + z)` for the bounded projection
    `π = Dr(0)`, and the formalization uses the constant `ε/(‖π‖ + 1)`.  Also "`N` is in good
    position to `C₀ = T₀O ∩ C`" is good position inside `T₀O` (`IsInGoodPositionIn`), and
    `C₀ = Tϕ(a)(C_aX)` uses `C_0 = C` at the corner of the centred chart
    (`partialQuadrantAtWith_zero`).  The good position part of the lemma is
    `IsInGoodPositionIn.isInGoodPosition` (`GoodPositionGerm.lean`).
70. **Remark 4.20** *(book 2017: Remark 4.4)* *(book 2021: unchanged, Remark 4.2.9, p. 189, "Theorem 4.1.9" for Proposition 4.1.9; "and open" corrected)*. `MPolyfold.remark_4_20`: for tame `X`, good position
    at `a` gives an open `U ∋ a` with good position at every point of `U ∩ A`.  The text states it
    without "tame" (Definition 4.16 is for tame `X`; tameness is used through Lemma 4.19).  "Since
    the tangent spaces of `A` move only slowly, Lemma 3.55 implies" is made precise: in a tame chart
    centred at `a`, with the closed good complement `Y = ker π` of the normal form
    (`exists_proj_goodComplement`; Lemma 3.55 needs `Y` closed), Proposition 4.9 for the
    sc⁺-retraction `t` gives the graph `Γ = id + σ`, `σ = (1 − π) ∘ Γ : V → Y` of class `C¹` with
    `σ(0) = 0`, `Dσ(0) = 0` (`DΓ(0)N ⊆ T₀A = N`); the tangent space at `Γ(v)` is
    `DΓ(v)N = {n + Dσ(v)n}` (`tangentSpace_eq_range_graph`, with `p ∘ DΓ(v) = 1`), which Lemma 3.55
    (`lemma_3_55_relOpen`) puts in good position to `C_{Γ(v)}` in `E` for small `|v|`; good position
    in `E` gives good position inside `T_{Γ(v)}O` (`IsInGoodPosition.isInGoodPositionIn_of_le`, the
    good complement `Y ∩ T_{Γ(v)}O` by the modular law).  Typos: "Theorem 4.9" for Proposition 4.9,
    "there exists and open neighborhood" for "an open" (lines 6605–6607).
71. **Definition 4.21** cites Definition 2.38 for `T_a^R X` (correct).  The "sc-complement in
    `T_aX`" is taken for the sc-structure induced on `T_zO` (an sc-subspace of `E` at a smooth
    point): `B` an sc-subspace of `E` with `(T_zO)_m = (T_zA)_m ⊕ B_m` for every `m`
    (`IsGeneralPositionRetractAt`).  `T_zA`, finite-dimensional and smooth, is automatically an
    sc-subspace (Proposition 1.6).  Definition 4.21 does not assume `X` tame and neither does the
    formalization.
72. Typos and slips in §4.2 *(book?: not checked against the 2017 text)*: line 6479,
    "`T_aA = Ts(s)(T_aX)`" for `Ts(a)(T_aX)`; lines 6473, 6487, "`d_A(x)`" for `d_A(a)` (item 64);
    lines 6463–6466, the definition of "locally closed" (item 63); line 6539, "Proposition 4.2" for
    Theorem 4.2; line 6591, "`p = Dt(0)`" (item 68 (d)); line 6596, "`V(a) = ϕ⁻¹(V₀) ∩ A`"
    (item 68); lines 6565, "`z ∈ Z ⊂ C`" (item 69); lines 6605–6607, "and open", "Theorem 4.9"
    (item 70).

Found while formalizing Theorem 4.22 and Remark 4.24 in `Chapter4/LocalStructure.lean`
(2026-10-26).

80. **Theorem 4.22 as formalized** *(book 2017: Theorem 4.3; not checked against the 2017
    text)* *(book 2021: unchanged, Theorem 4.2.11, p. 190)*; statement (4) is item 89. `MPolyfold.theorem_4_22`: for a tame M-polyfold `X`, a smooth
    finite-dimensional submanifold `A` (Definition 4.13; the statement says only "smooth
    submanifold") and `x ∈ A` at
    which `A` is in general position (Definition 4.21; the statement's "assuming that `T_xA` has in
    `T_xX` an sc-complement contained in `T_x^R X`" repeats the definition), there are a tame chart
    `ψ` with `ψ(x) = 0` and an open `U ∋ x` in its domain with (1) `d_X(x) = n`, the number of
    half-line coordinates of the partial quadrant of `ψ`, all of which vanish at `0`, and `x` lies in
    exactly `d_X(x)` faces of the chart model (Corollary 2.41); (2) `d_X(a) = d_A(a)` on `A ∩ U`,
    `d_A` for the induced structure of Proposition 2.21; (3) general position at every point of
    `A ∩ U`.  **No hypothesis is added.**  The chart form is `theorem_4_22_chart`.  The chart
    "`x = 0 ∈ O`, `C = [0, ∞)ⁿ ⊕ W`, `n = d_O(0)`" of the proof is the tame chart re-centred at the
    smooth point `x` (item 1; `IsTame.exists_centredChart`): only after re-centring do all
    half-line coordinates vanish at `0`, so that `{0} ⊕ W` is the minimal subspace `E_0` and
    `T₀^R O = T₀O ∩ ({0} ⊕ W)`.
81. **The citation "By Definition 2.27, `T₀^R O = T₀O ∩ ({0} ⊕ W)`" (line 6647) is correct**, not a
    slip: Definition 2.27 defines `T_x^R O = T_xO ∩ E_x` for a retract, and the proof works in the
    retract `O` of a chart; Definition 2.38 (cited by Definition 4.21, item 71) is the M-polyfold
    version, defined through charts.  (The plan's risk list had this as a misprint.)  What the line
    uses without saying is that at the corner `0` of the centred chart `E_0 = {0} ⊕ W` (every
    coordinate vanishes at `0`; `mem_minimalSubspaceWith_zero`), and that `E_0 ⊆ E_a` for every `a`
    (`minimalSubspaceWith_zero_le`), which is how `W ∩ T_aO ⊆ T_a^R O` in (3) is justified.
82. **The good complement `Y ⊆ W` must be closed, and is chosen, not constructed as `Ã ⊕ Z`.**
    The text obtains "`T₀A` has in `E` an sc-complement `Y` contained in `W`" from
    `E = T₀O ⊕ Z = T₀A ⊕ Ã ⊕ Z` (`Ã` the complement of Definition 4.21, `Z = (1 − Dr(0))E ⊆ W` by
    tameness, Proposition 2.35); only `T₀A + W = E` is used afterwards
    (`sup_minimalSubspaceWith_eq_top`).  Proposition 4.9 needs a *closed* good complement (item 21);
    the formalization takes any closed complement of `T₀A` inside the closed subspace
    `E_0 = {0} ⊕ W` (`exists_isClosed_isCompl_le`: `Y = E_0 ∩ ker q`, `q` a continuous projection
    onto `T₀A ∩ E_0`).  "Moreover, `T₀A` is in good position to `C`, and `Y` is a good complement"
    is not argued: `Y` is good with every `ε` because adding a vector of `E_0` changes no coordinate
    (`isGoodComplement_of_le_zero`), and `T₀A ∩ C` has interior points in `T₀A` because the
    coordinates map `T₀A` onto `ℝⁿ` (`coordsOn_surjective`, `interior_nonempty_of_sup_eq_top`).
83. **The auxiliary splitting `T₀A = N ⊕ (T₀A ∩ W)` is replaced by coordinates.**  The text writes
    "We denote by `N ⊂ T_aA` a sc-complement of `T₀A ∩ W` in `T₀A`" (line 6658; `T_aA` for `T₀A`,
    and the letter `N` is later the normal-form subspace of other proofs), derives `E = N ⊕ W`,
    `C = (C ∩ N) ⊕ W`, `C = (T₀A ∩ C) ⊕ Y`, and represents points of `T₀A ∩ C` as
    `(n, m) ∈ (N ∩ C) ⊕ (T₀A ∩ W)`.  What is needed is a presentation of the partial quadrant
    `T₀A ∩ C` of `T₀A` in which its degeneracy index counts the vanishing coordinates `λ_i`; the
    formalization uses `v ↦ (λ(v), v − s(λ(v)))`, `s` a linear section of `λ|_{T₀A}`
    (`degIndex_slice`: `d_{T₀A ∩ C}(v) = d_C(v)`).  Proposition 3.22 is then not needed.
84. **(2): which chart realizes `d_A`.**  "`p : A → (T₀A ∩ C) ∩ V` is a sc-diffeomorphism from the
    M-polyfold `A` and we conclude, by Proposition 2.24, that `d_A(a) = d_{T₀A ∩ C}(p(a))`": the
    sc-diffeomorphism is the corner chart `p ∘ ψ` of `A` (Theorem 4.2's `CornerChartData` for the
    chart of `A` induced by `ψ`, with the projection along `Y ⊆ E_0`); it is a chart of the induced
    structure (Finding 55) and is modelled on `(V, T₀A ∩ C, T₀A)` with the identity retraction,
    which is tame, so it realizes `d_A` (`degIndex_eq_chartDegIndex_of_isTameRetract`) — that, and
    not Proposition 2.24 (invariance under sc-diffeomorphisms of M-polyfolds), is the step.  "The
    diffeomorphism `p` maps `A ∩ F_σ` to `(T₀A)_σ ∩ C` ... This implies that
    `d_{T₀A ∩ C}(p(a)) = d_C(a)`" is the coordinate count: `a − p(a) = δ(p(a)) ∈ Y ⊆ {0} ⊕ W`, so
    `λ(a) = λ(p(a))` (`degIndexWith_add_of_mem_zero`).  "In view of Proposition 2.36,
    `d_C(a) = d_O(a)`", and `d_O(a) = d_X(a)` because the chart is tame
    (`degIndex_eq_chartDegIndex_of_isTameRetract`).  Slips: the target "`(T₀A ∩ C) ∩ V`" is `V`
    (`V ⊆ T₀A ∩ C`); `U` is used before it is defined; "proposition 2.36" (lower case); Proposition
    4.9 is applied to the sc⁺ chart retraction `t = ψ ∘ s ∘ ψ⁻¹ ∘ r` (item 60), which the text does
    not mention; "`δ(0) = 0` and `Dδ(0) = 0`" hold (as in item 70) but are not used.
85. **(3): two steps are not argued.**  (a) "By means of the particular form of the map
    `α : h ↦ h + Dδ(v)h`, also `T_aA + W = E`" needs `Dδ(v)h ∈ W`, i.e. that the derivative of the
    `Y`-valued `δ` takes values in `Y ⊆ W`; the formalization gets it from `p ∘ DΓ(v) = 1` on
    `T₀A` (`tangentSpace_eq_range_graph`) and `ker p = Y` (`sup_minimalSubspaceWith_eq_top_graph`);
    also "`T_aA` is the image of `α`" is the tangent space along the graph of Proposition 4.9
    (`tangentSpace_eq_range_graph`, item 70).  (b) From `T_aO = T_aA + T_a^R O` the text concludes
    "implying that `T_aA` has in `T_aO` a sc-complement which is contained in `T_a^R O`".  This needs
    `T_a^R O` to be an sc-subspace (Proposition 2.36, for tame retracts at smooth points:
    `proposition_2_36_partialCone`) and an sc-complement of the finite-dimensional smooth
    `T_aA ∩ T_a^R O` *inside* `T_a^R O` with the level-wise splitting; `exists_scComplement_le`
    constructs it as `T_a^R O ∩ G`, `G` the sc-complement of `T_aA ∩ T_a^R O` in `E` of
    Proposition 1.6, the density of smooth points coming from the sc-projection of Lemma 2.B.
86. **(1) is a statement about the chart, not about `A`.**  "There are precisely `d = d_X(x)` many
    local faces `F_1, …, F_d` contained in `U`" is Proposition 2.44 (first sentence) / Corollary 2.41
    in the centred tame chart; the faces of the chart model are closed subsets of `O`, not contained
    in a small `U`, and "local faces" are germs at `x` (Proposition 2.44).  The formalization states
    `d_X(x) = n` for the centred chart (the local faces being `F_i = O ∩ {λ_i = 0}`) and the face
    count of Corollary 2.41 for the model; `A` plays no role.
87. **Remark 4.24** *(book 2017: Remark 4.5)*.  "By Proposition 2.36, the codimension of `T_x^R X`
    is equal to `d_X(x)`" holds for tame `X` at smooth `x` (`MPolyfold.remark_4_24_codim`, in a tame
    chart, with `d_X(x) = d_C(φ(x))`); both conditions are implicit (in Theorem 4.23 `X` is tame and
    `A_λ ⊆ X_∞`).  "`x ∈ A_λ` can only belong to a corner if `d_X(x) ≤ dim(A_λ)`" holds for every
    smooth finite-dimensional submanifold in general position at `x`, independently of Theorem 4.23
    (`MPolyfold.remark_4_24`: `d_X(a) ≤ dim T_aA`, since `T_aX = T_aA + T_a^R X`;
    `quotDim_le_finrank_of_eq_sup`); "zero-dimensional `A_λ` lie in `X ∖ ∂X`" is
    `MPolyfold.remark_4_24_not_mem_boundary`.  The `Σ` of Theorem 4.23 is not formalized here.
88. Typos and slips in the statement and proof of Theorem 4.22 *(book?: not checked against the
    2017 text)*: line 6658, "`N ⊂ T_aA`" for `N ⊂ T₀A`; line 6684, the target "`(T₀A ∩ C) ∩ V`" of
    `p` (item 84); line 6705, "proposition 2.36"; lines 6619–6621, the statement omits
    "finite-dimensional" in "smooth submanifold" and repeats Definition 4.21 ("assuming that ...",
    item 80).
89. **Theorem 4.22 (4) has no proof in the text; it is proved, with no added hypothesis**
    (`MPolyfold.theorem_4_22` (4), `MPolyfold.theorem_4_22_four_of_chart`,
    `theorem_4_22_four_chart`).  The text: "in view of the arguments in the proof of Proposition
    2.43, the sets `F_σ` are tame M-polyfolds.  Moreover, `A ∩ F_σ` are smooth submanifolds of
    `F_σ`.  The previous arguments, but now applied to `A ∩ F_σ` conclude the proof."  What is
    missing: (a) Proposition 2.43 is about one face; for intersections of faces it is the second
    sentence of Proposition 2.44, itself without proof in the text, proved in `CornerGerms.lean`
    (`corner_retraction`, `corner_tameModel`, `proposition_2_44_corner`; the plan's risk list said
    that intersections were not yet shown to be tame — they were); here these are applied in the
    centred chart and restricted to an open `G`.  (b) "`A ∩ F_σ` are smooth submanifolds of `F_σ`"
    needs an sc⁺-retraction *in the M-polyfold `F_σ`*.  It is built as
    `t_σ = Γ ∘ κ_σ ∘ p ∘ t` (`exists_scPlus_retraction_corner`; `κ_σ` kills the coordinates in `σ`
    on `T₀A`, through a linear section of `λ|_{T₀A}`, `killOn`; `Γ(v) − v ∈ Y ⊆ {0} ⊕ W` changes no
    coordinate, so `Γ ∘ κ_σ ∘ p` maps `A` near `0` onto `A ∩ f_σ`), transported to the face model
    `π_σ ∘ t_σ ∘ ι_σ` on `[0, ∞)^{n − #σ} ⊕ W` (`exists_cornerModel_retraction`), and turned into an
    sc⁺-retraction on an open subset of `F_σ` through its face chart `π_σ ∘ ψ` by a general fact the
    text does not state: an sc⁺-retraction in a chart is an sc⁺-retraction on an open subset of the
    M-polyfold (`MPolyfold.isScPlusRetractionOn_of_chart`, Definition 4.4 read in the charts of
    `X` and `X¹`).  (c) General position in `F_σ` ("the previous arguments"): `T_y(A ∩ F_σ)`
    contains `T_yA ∩ f_σ` (`Dt_σ(y)` fixes it, by the chain rule), and `T_yA + E_0 = E` from (3)
    shows that the coordinates outside `σ` map `T_yA ∩ f_σ` onto `ℝ^{n − #σ}`; in the face model
    this is `T_{y'}π_σ(A ∩ F_σ) + E'_0 = E'`, and the argument of (3)
    (`isGeneralPositionRetractAt_of_sup_eq_top`) applies.  (d) "tame smooth submanifold": the
    tameness of `A ∩ F_σ` is Theorem 4.18 in the tame M-polyfold `F_σ`, which needs good position at
    every point; **general position implies good position**
    (`IsGeneralPositionRetractAt.isGoodPositionRetractAt`: the complement lies in `E_z`, hence is a
    good complement, and `codim T_z^R O = d_C(z)` makes the coordinates `λ_i`, `i ∈ I(z)`, map
    `T_zA` onto `ℝ^{I(z)}`), a step the text never states.  (e) `F_σ` is a germ: it is taken as
    `ψ⁻¹(G ∩ ⋂_{i ∈ σ} F_i)` (`MChart.cornerPreimage`), `F_i` the faces of the chart model through
    `0`, with `G` inside the domain of the submanifold chart, so that `F_σ ⊆ U` (the text's
    "contained in `U`") and `A ∩ F_σ` is exactly the retract of `t_σ`; `G` depends on `σ`.
90. **Not formalized in Theorem 4.22**: the dimension count `dim(A ∩ F_σ) = dim A − #σ`, which the
    statement does not contain but the proof of Theorem 4.23 uses (lines 6769–6771); the
    identification of the local faces `F_i` of the chart model with (germs of) global faces of `X`
    (Theorem 2.45 in the face-structured case). See also item 130.

Found while formalizing §4.3 (Sard's theorem and Theorem 4.23) in `Vendor/MilnorSard/*`,
`Chapter4/FamiliesLocal.lean` and `Chapter4/Families.lean` (2026-10-26).

100. **Sard's theorem is vendored from the Milnor project, not imported.**  Theorem 4.23 uses "Sard's
     theorem" for `C^∞` maps between finite-dimensional spaces of arbitrary dimensions; Mathlib has
     only the equidimensional case (`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`)
     and the case `dim E < dim F` (`ContDiffOn.dense_compl_image_of_dimH_lt_finrank`).  The Milnor
     project (`math_faithful`) proves the full theorem (Milnor's proof by induction on the
     dimension, with the Hausdorff-dimension estimate in place of the cube count).  Its import
     closure — `Milnor/Chapter1/InverseFunction.lean` and
     `Milnor/Chapter3/{Basic,Straighten,Step1,Step2,Step3,Sard}.lean`, about 1,380 lines, Mathlib
     only, same Mathlib revision and toolchain — is copied into `Polyfold/Vendor/MilnorSard/` (commit
     `53704ad` of the source files, recorded in each file's header), with the namespace renamed
     (`Milnor.sard` becomes `Polyfold.MilnorSard.sard`) and the imports redirected; no statement or
     proof is changed.
     `lakefile.toml` and `lake-manifest.json` are unchanged (a `require` of the Milnor package would
     make lake rewrite the manifest, which the broken `git` on the development machine makes
     unsafe, and the project advertises no Milnor dependency).  The results used are
     `Polyfold.MilnorSard.sard` (`μ (f '' critSet f U) = 0` for `f` `C^∞` on an open `U ⊆ E`,
     `E`, `F` finite-dimensional real normed spaces in the same universe, `μ` any Haar measure on
     `F`, `critSet f U` the points of `U` where `Df(x)` is not onto) and
     `Polyfold.MilnorSard.dense_compl_image_critSet`.
101. **Theorem 4.23 as formalized** *(book 2017: Theorem 4.4; not checked against the 2017
     text)* *(book 2021: unchanged, Theorem 4.3.1 (2), p. 193)*.  `Polyfold.theorem_4_23`: `X` a tame M-polyfold, `A ⊆ ℝᵐ × X` a smooth
     finite-dimensional submanifold (Definition 4.13) of the product M-polyfold
     `(rnPolyfold m).prod PX` (the text's `ℝᵐ ⊕ X` "with the product charts"; tame by
     `prod_rn_isTame`), with tame induced structure and compact closure, `ε > 0`, (1) for
     `|λ| ≤ ε` (`|λ|² = Σ λ_i²`) the fibre `A ∩ P⁻¹(λ)` compact and non-empty, (2) `A` in general
     position at every point.  Conclusion: there is `Σ ⊆ {|λ| < ε}` with `{|λ| < ε} ∖ Σ` a
     Lebesgue null set, every `λ ∈ Σ` a stratified regular value of `p = P|_A` (item 102), and for
     `λ ∈ Σ` the fibre `A_λ` is compact, a smooth finite-dimensional submanifold of `X` in general
     position at each of its points, and its induced structure has a corner structure
     (Definition 4.1, "a smooth compact manifold with boundary with corners") and is tame.
     `Polyfold.theorem_4_23_of_subset` is the same for any parameter set `S` in place of the ball.
     **No hypothesis is added.**  Not used: the tameness of the induced structure of `A`, the
     non-emptiness in (1) and `ε > 0` (the conclusion holds for every `S`); (1) is used only for the
     compactness of `A_λ`, the image of `A ∩ P⁻¹(λ)` under the projection to `X`.
     Hypothesis (2) is misprinted (lines 6767–6768, "there exists a sc-complement `T_zA` in `T_zZ`
     which is contained in `T_z^R Z`"); it is read as Definition 4.21, as in the proof.
102. **"Regular value" is the stratified notion of the proof, stated in a chart.**  The statement
     says "regular values of `p`"; the proof uses regular values of all the `p_σ : A ∩ F_σ° → ℝᵐ`,
     i.e. at each point `z` the derivative of `p` restricted to the tangent space of the stratum
     through `z` is onto.  `Polyfold.IsStratRegularPoint`: in a product chart
     `(r ↦ r − a) × φ`, the projection to `ℝᵐ` maps `T_zA ∩ E_z` onto `ℝᵐ`
     (`E_z = ℝᵐ × (E_X)_{φ(z₂)}`), for some choice of data, chart, presentation and lift (as for
     Definitions 4.16 and 4.21); `Polyfold.IsStratRegularValue`.  The naive notion
     (`Dp(z) : T_zA → ℝᵐ` onto) does not give the conclusions at `λ`: in `ℝ × [0, ∞)` let
     `A = {(x, x) | 0 ≤ x < 1} ∪ (−1, 1) × {5}`, `ε = 1/2`; `A` satisfies all hypotheses (at
     `(0, 0)`, `T_zA = ℝ(1, 1)` has the complement `ℝ × {0} = T_z^R Z`), `Dp` is onto at every
     point, but `A_0 = {0, 5}` is zero-dimensional and meets `∂X`, so it is not in general position
     (Remark 4.24); `(0, 0)` is a stratified critical point (`T_z(A ∩ F) = 0`).  The chart
     independence of `IsStratRegularPoint` (true by the transport argument of item 66, since the
     transition maps of product charts are `id × τ` up to translation) is **not formalized**.
103. **The covering step of the proof is wrong; repaired by a countable subcover** *(book 2017:
     unchanged, proof of Theorem 4.4, p. 147)* *(book 2021: unchanged, proof of Theorem 4.3.1, p. 193)*.  "We cover the
     set `{z ∈ A | |p(z)| ≤ ε}` with the finitely many such neighborhoods `U(z₁), …, U(z_k)`" (line
     6773): this set need not be compact, so no finite subcover need exist.  Example (plan, risk
     8): in `ℝ × ℝ`, `A = (−2ε, 2ε) × {2} ∪ {(ε(1 − x), x) | 0 < x < 1}` has compact closure and
     compact non-empty fibres over `|λ| ≤ ε`, but `{z ∈ A | |p(z)| ≤ ε}` contains the open segment,
     which accumulates at `(ε, 0) ∉ A`.  The repair (`theorem_4_23_of_subset`): `A` is second
     countable (`cl(A)` is compact in the metrizable `ℝᵐ × X`, Theorem 2.16, hence separable), so
     countably many of the neighbourhoods `U(z)` of the local step (`exists_local_family`) cover
     `A`, and `Σ = S ∖ ⋃_i CV(z_i)` is still of full measure.  Some countability is necessary: an
     uncountable discrete `A` (each point a component) can have critical values of positive
     measure; here it comes from the compactness of `cl(A)`, which the text assumes.
     (Machine-checked in the round-trip audit: `RoundTrip/Items/V4_64.lean`, `not_B`, with `X = ℝ`,
     `m = 1`, `ε = 1`, `A = (−2, 2) × {0} ∪ (0, 2) × {1}`, which satisfies the hypotheses of Theorem
     4.23, while `{z ∈ A | |p(z)| ≤ 1}` has an open cover by sets `U(z)` without a finite subcover.)
104. **Sard on the strata, in the chart of Theorem 4.22** (`Polyfold.measure_image_stratCritSet`,
     `exists_local_family`).  In the product chart centred at `z₀`, `A` is the graph `Γ(V)` over a
     relatively open `V` of the partial quadrant `{ℓ ≥ 0}` of `N = T₀A` (`ℓ` the coordinates of the
     tame chart, onto `ℝⁿ`), and `p` is `f = P ∘ χ⁻¹ ∘ Γ`, `C^∞` on `V`.  The open strata
     `A ∩ F_σ°` are the open subsets `{ℓ_i = 0 (i ∈ σ), ℓ_j > 0 (j ∉ σ)}` of the subspaces
     `{ℓ_i = 0, i ∈ σ}` of dimension `dim A − #σ` (`Polyfold.finrank_stratSub`: the dimension count
     the proof takes from Theorem 4.22 — "By Theorem 4.23, the intersection `A ∩ F_σ°` is a smooth
     manifold without boundary having dimension `dim(A) − #σ`" — which Theorem 4.22 does not
     state, item 90), and Sard's theorem (item 100) applies to `f` on each of them.  The critical
     values of all the `p_σ` in one chart are `f(stratCritSet)` (`Polyfold.stratCritSet`).
105. **The fibre over a regular value: the steps the text skips.**  (a) "Smooth submanifold"
     (Definition 4.13) needs an **sc⁺-retraction onto `A_λ`**, which the text does not construct.
     In the product chart it is `τ(e) = (Γ(ρ(p(t(c, e)))))₂` (`Polyfold.exists_slice_retraction`;
     `t` the sc⁺ chart retraction of `A`, `p` the projection of Proposition 4.9, `c = λ − λ₀`),
     where `ρ` is a `C^∞` retraction of a relatively open subset of `{ℓ ≥ 0}` onto the fibre
     `f⁻¹(λ)` (`Polyfold.exists_fibre_retraction`); `isScPlusRetractionOn_of_chart` makes it an
     sc⁺-retraction on an open subset of `X`.  (b) `ρ` needs the **implicit function theorem at
     corner points**, with the kernel `K = ker Df(v₀)` in good position to the partial quadrant
     `C_{v₀}`: this holds because `Df(v₀)` restricted to the stratum is onto — the argument of
     Lemma 5.26, not given here (`Polyfold.exists_goodComplement_stratSub`: `K` has a closed good
     complement inside the stratum subspace; `K ∩ C_{v₀}` has interior points since `ℓ` is onto).
     (c) Theorem 3.78 gives a `C^j` solution for one `j`, with `j`-dependent radii in its
     statement; the `C^∞` solution needed here is `Polyfold.theorem_3_78_smooth`
     (`ContractionData.exists_solution_smooth`: the contraction radii of Lemmas 3.79–3.80 do not
     depend on `j`, so one fixed point map is `C^j` for every `j`).  (d) "smooth compact manifold
     with boundary with corners": Theorem 4.18 for `A_λ ⊆ X` (`X` tame), with good position from
     general position (`IsGeneralPositionRetractAt.isGoodPositionRetractAt`); it gives the corner
     structure of Definition 4.1 and tameness of `A_λ`.
106. **General position of `A_λ`: the text's argument made precise**
     (`Polyfold.isGeneralPositionRetractAt_slice`).  The text: "`T_{z'}(A ∩ F_σ°) =
     T_{z'}(({λ} × A_λ) ∩ F_σ°) ⊕ ξ_{z'}` with `Tp_σ(z')` mapping `ξ_{z'}` onto `ℝᵐ` ... in view of
     the assumption (2) ... `T_{z'}({λ} × A_λ)` has a sc-complement in `T_{z'}^R X`".  In the
     chart: `T_xA_λ` contains the second components of the vectors of `T_zA` with vanishing first
     component (`Dρ(v₀) = 1` on `ker Df(v₀)`, by the chain rule through `τ`); for `w ∈ T_xX`
     write `(0, w) = a + b` with `a ∈ T_zA`, `b ∈ T_z^R Z = ℝᵐ × T_x^R X` (general position of `A`
     at `z` itself, hypothesis (2)), and correct `a` by `a₂ ∈ T_zA ∩ E_z` with the same first
     component (stratified regularity): `w = (a − a₂)₂ + (b + a₂)₂ ∈ T_xA_λ + T_x^R X`; the
     sc-complement inside `T_x^R X` is `exists_scComplement_le`.  The regularity at the stratum is
     exactly what makes `a₂` lie in `E_z`.
107. Typos and slips in §4.3 *(book?: not checked against the 2017 text)*: line 6785 "By Theorem
     4.23" for Theorem 4.22; line 6777 "`F_δ`" for `F_σ`; lines 6767–6768, hypothesis (2)
     (item 101); lines 6752–6753, "a set of full measure `Σ ⊂ {|λ| < ε}` ... having full measure in
     `B^m(ε)`" (said twice); line 6795 "regular values for all the maps in (1)" (the maps `p_σ`;
     there is no list (1)); the statement's "smooth submanifold" omits "finite-dimensional";
     Remark 4.24 is placed between the statement and the proof of Theorem 4.23 and refers to its
     `Σ` (with Theorem 4.23 formalized, Remark 4.24 applies to `A_λ`, `λ ∈ Σ`, through
     `MPolyfold.remark_4_24` and the general position of `A_λ`; not stated separately).
108. **Not formalized in Theorem 4.23**: the chart independence of the stratified regularity
     (item 102); the converse "stratified regular ⇒ the `λ` is in `Σ`" (the theorem produces `Σ`
     inside the regular values, with null complement, which is what the text claims); the
     identification of the strata `A ∩ F_σ°` with global faces of `X` (item 90).

Found while writing the exposition of Chapter 4 (`Chapter4.md`, 2026-10-26). §4.4 (sc-differential
forms and de Rham cohomology, preprint lines ≈6830–6911) is not formalized (`Chapter4.md` §9: it
needs `⊕ᵏTX` as an M-polyfold, a linear `T_xX` (G.7), `X^i` for `i ≥ 2` (G.6) and integration on
manifolds with corners); these items concern the text only *(book 2017: not checked)* *(book 2021: rewritten, §4.4, pp. 195–199: `d` now runs `Ω^k(X^i) → Ω^{k+1}(X^{i+1})` (item 120 corrected); `d² = 0` and the relative `d ∘ d = 0` still asserted (item 121); forms on `∂X` motivated by local faces, not defined (item 122); Stokes, Theorem 4.4.7, now with `∫_N`, still without proof (item 123); `Ω^k_∞` and `Ω^*_∞` now distinguished (item 124); the Lie bracket is proved in Appendix 4.5, pp. 200–202)*.

120. **The direction of the exterior derivative.** The text writes `d : Ω^k(X^{i+1}) → Ω^{k+1}(X^i)`;
     since Proposition 4.26 puts the Lie bracket of sc-smooth vector fields on `X¹` (one level is
     lost in differentiating), the arrow must run `Ω^k(X^i) → Ω^{k+1}(X^{i+1})`.
121. **`d ∘ d = 0` and `d j* = j* d` are asserted without proof**, and the relative complex's
     `d ∘ d = 0` ("one easily verifies") rests on both.
122. **Forms on `∂X` are never defined**: `∂X` is not an M-polyfold, only a union of faces, so the
     relative complex needs forms on the faces and compatibility on their intersections.
123. **Theorem 4.28 (Stokes) has no proof in the text**, and its formula writes `∫_M dω` for `∫_N dω`.
124. Notation and typos in §4.4: `Ω*_∞` is used both for the limit of the `k`-forms and for their
     sum; the cohomology is called `H*_sc` in Definition 4.27 and `H*_dR` for the relative complex;
     "s sc-differential", an unclosed parenthesis, "The general the theory".
125. **Remark 4.3, "`X¹ ≠ X` is possible".** An example would have to be a retract `O = O_∞` that is
     not an sc⁺-retract (Proposition 4.8), e.g. one with an infinite-dimensional tangent space, if
     such a retract exists; the text gives no example and none is known to the project (item 5).
     (Round-trip item V4.6: this is the only clause of Remark 4.3 that the project does not give;
     the others follow from `remark_4_3_levelVal`, `remark_4_3_isScDiffeo`, `remark_4_3_const`,
     `RoundTrip/Items/V4_6.lean`, `A_to_B_rest`.) *(2026-11-02: an example is formalized,
     `Polyfold.remark_4_3_example`, with a retraction that loses a level in its first derivative;
     items 140–146.)*

Round-trip audit findings (`RoundTrip/REPORT.md`, 2026-11-01), recorded here only.

130. **Theorem 4.22 (1) and (4): the project's local faces are faces of the chart model, the text's
     are faces of a neighbourhood `U`.** The text (p. 162): an open `U ∋ x` with "precisely
     `d = d_X(x)` many local faces `F_1, …, F_d` contained in `U`", and `F_σ = ⋂_{i∈σ} F_i` in (4)
     *(book 2017: Theorem 4.3)*. `MPolyfold.theorem_4_22` (items 80, 89 (e)) counts the faces
     through `0` of the model retract of a tame chart `ψ` centred at `x` and takes
     `F_σ = ψ⁻¹(G ∩ ⋂_{i∈σ} F_i)` with `G` depending on `σ`. Round-trip item V4.50: (2) and (3)
     follow (`RoundTrip/Items/V4_50.lean`, `A_to_B23`); (1) and (4) for the faces of `U` itself
     (closures in `U` of the components of `U ∩ {d_X = 1}`, all through `x`) need a local face
     theorem for small neighbourhoods, identifying them with `ψ⁻¹` of the retract faces. Believed
     true for tame `X`; not in the project (cf. item 90).

**140–149: Remark 4.3's example (2026-11-02).** (`Chapter4/RemarkFourThreeExample.lean`,
`Chapter4/RemarkFourThreeFamily.lean`; comparison item V4.6, gap G.31; revises items 5, 125.)

140. **An sc-smoothness criterion with one level of loss.** The project's sufficient conditions for
     sc-smoothness (Proposition 1.19, Corollary 1.20, sc-operators, and their composites) all
     produce maps whose level maps `U_m → F_m` are `C¹`. New: `Polyfold.IsLossFamily L` for level
     operators `L(p)_m : Z_m → W_m` with a finite-dimensional parameter `p ∈ V`: compatible with
     the inclusions, `(p, z) ↦ L(p)_m z` continuous on `V × Z_m` (no continuity of `p ↦ L(p)_m` in
     the operator norm), and `p ↦ L(p)_m ∘ ι ∈ L(Z_{m+1}, W_m)` of class `C^∞`.
     `Polyfold.IsLossFamily.isScSmooth`: `(p, z) ↦ L(p) z` is sc-smooth on `V ⊕ Z`. Proof by
     induction on `k` (`isSck_lossFamMap`): the map is sc¹ (`IsLossFamily.isSc1With`, derivative
     `(π, ζ) ↦ ∂_pA_0(p)[π]z + L(p)ζ`), its tangent map is the map of the tangent family
     `L̃(p, π)(z, ζ) = (L(p)z, ∂_pA(p)[π]z + L(p)ζ)` on `V × V` after the reordering sc-isomorphism
     `famSwap` (`tangentMapWith_lossFamMap_eq`), and `L̃` is again a loss family
     (`IsLossFamily.tangent`). Not in the text. Only one level of loss is allowed: maps whose
     `j`-th derivative costs `j` levels (e.g. `(t, x) ↦ (cos(kt)x_k)_k` of
     `Chapter1/ScOneNotNormContinuous.lean`, which fails the hypothesis) are not covered.
141. **Why the example needs loss (not formalized).** By Proposition 4.8 in charts
     (`MPolyfold.isScSmoothMap_toLevelOne_iff`, item 4) an example is an sc-retract `O = r(U)` with
     `O = O_∞` that is not an sc⁺-retract. If `r : U₀ → E₀` is `C¹` (Fréchet) and `O ⊆ E₁`, then
     `T_oO = Dr(o)E₀` is finite-dimensional for every `o ∈ O`: `O` is a `C¹` submanifold of `E₀`
     modelled on `T_oO`, and `O ⊆ ⋃ₙ cl₀{x ∈ E₁ : |x|₁ ≤ n}`, a countable union of compact subsets
     of `E₀` (compact inclusion), so by Baire some nonempty open subset of `O` has compact
     closure, which forces finite-dimensional models; the model is locally constant. If moreover
     `r : U₁ → E₁` is `C¹`, the topologies of `O ⊆ E₀` and `O ⊆ E₁` agree near `o` (both are read
     by the same injective map `x ↦ Dr(o)(x − o)` into the finite-dimensional `T_oO`). So an
     example cannot come from a retraction with `C¹` level maps; the retraction must lose a level
     in its first derivative, as the splicings of HWZ do (`t`-derivatives of `π_t` cost one level).
     This is an argument, not a Lean proof.
142. **The reduction.** For a loss family of projections (`L(p)₀² = L(p)₀`) on `V ⊕ Z`,
     `r(p, z) = (p, L(p)z)` is an sc-smooth retraction (`IsLossFamily.retraction`); if the ranges
     of the `L(p)₀` are smooth points, `O = O_∞` (`IsLossFamily.retract_subset_smooth`); if the
     lift `O → E₁` is discontinuous, `O` is not an sc⁺-retract (`IsLossFamily.not_isScPlusRetract`).
     `Polyfold.RemarkFourThreeData V Z` collects the hypotheses and
     `exists_retract_smooth_not_scPlus_of_data` gives an sc-retract `O = O_∞` that is not an
     sc⁺-retract. The data are supplied in item 144 and the M-polyfold in item 145. Why sparse
     indices: on the weighted space `X` of `ScOneNotNormContinuous.lean` (`|x|_m = sup (i+1)^m|x_i|`)
     the moving vector must pass between coordinates of comparable weight (otherwise the level-`m`
     operators are unbounded), so one level gains at most a geometric factor per step; the
     transitions must then be polynomially fast, and `Σ_k δ_k < ∞` with durations `δ_k ≈ k^{-2}`
     requires the gain per step to be geometric in `k`, which `n_k = 2^k` provides. Consecutive
     indices `n_k = k` cannot work (Cauchy–Schwarz: `Σ δ_k < ∞` and `Σ 1/(δ_k (k+1)) < ∞` are
     incompatible).
143. **What changes for the text.** Remark 4.3's "`X¹ ≠ X` is possible although the underlying
     sets agree" is **proved** (item 145), with an example the text does not give; it needs an
     sc-smooth retraction whose first derivative loses a level (item 141), and its sc-smoothness
     rests on the new criterion of item 140, not on the text's Proposition 1.19. Status:
     **settled**.
144. **The family (`Chapter4/RemarkFourThreeFamily.lean`).** On `X`, with `n_k = 2^k` (`nk`),
     nodes `1/(k+1)` (`node`) and angles `θ_k(t) = π/2·σ((k+1)(k+2)(1/(k+1) − t))` (`σ` = Mathlib's
     `Real.smoothTransition`, so `θ_k = 0` for `t ≥ 1/(k+1)` and `π/2` for `t ≤ 1/(k+2)`), the
     coefficients `b_k = sin θ_{k−1} cos θ_k` (`RemarkFourThree.bb`) vanish except
     `b_k = cos θ_k`, `b_{k+1} = sin θ_k` at the active block `k = ⌊1/t⌋ − 1`
     (`bb_eq_zero_of_pos`, `bb_kt`, `bb_kt_succ`), and all vanish for `t ≤ 0`.
     `RemarkFourThree.fam t m = Σ_k blk k t m` (a `tsum` with two nonzero terms; on level `m` the
     entries carry the weight ratios `((a+1)/(b+1))^m ≤ 2^m`, `elemL`) is on level `0` the
     projection onto `b_k e_{n_k} + b_{k+1} e_{n_{k+1}}` (`fam_of_pos`). Proved:
     `isLossFamily_fam` — compatibility with the inclusions (`toBase_fam`), the uniform bound
     `‖L(t)_m‖ ≤ 3 + 2^m` (`norm_fam_le`), strong continuity from the bound and norm continuity
     after the dense inclusion (`continuous_apply_of_bound`, an `ε/3` argument), and
     `t ↦ L(t)_m ∘ ι ∈ L(X_{m+1}, X_m)` of class `C^∞` (`contDiff_fam_comp`, Mathlib's
     `contDiff_tsum`: `j` derivatives of block `k` are bounded by `K4_j (k+3)^{2j}` through
     `DerivBound`, Leibniz's rule and `exists_bound_iteratedFDeriv` for the flat transition,
     while one level of loss gains `(2 + 2^m)2^{-k}`); `fam_idem` (every `L(t)₀` is a
     projection); `fam_mem_smooth` (finitely supported ranges); `not_continuousOn_liftOne` (the
     points `o_k = (1/(k+1), (1/(k+1))e_{n_k})` lie in `O` (`fam_node_smul_δv`), tend to `0` in
     `E₀`, and their level-`1` coordinates `(2^k+1)/(k+1) e_{n_k}` have norm `≥ 1`).
     `RemarkFourThree.remarkFourThreeData : RemarkFourThreeData ℝ X`. The family follows the
     sketch of the previous version of item 142 without change; no step failed.
145. **The M-polyfold.** `retractPolyfold hO o₀` is the M-polyfold of an sc-retract `O` with the
     single chart `O → O` (`retractChart`). `retractPolyfold_smooth_not_toLevelOne`: if
     `O ⊆ E_∞` and `O` is not an sc⁺-retract, every point of this M-polyfold is smooth
     (`X₀ = X_∞`) and `1₀¹ : X → X¹` is not sc-smooth, for every junk value
     (`MPolyfold.isScSmoothMap_toLevelOne_iff`). `Polyfold.remark_4_3_example`: there is an
     M-polyfold with `X₀ = X_∞` and `1₀¹` not sc-smooth (so, by `remark_4_3_isScDiffeo`, not an
     sc-diffeomorphism: `X¹ ≠ X` as M-polyfolds); `Polyfold.remark_4_3_retract_example` is the
     retract form. In this example `X` and `X¹` even have different topologies on the same set
     (`o_k → 0` in `X`, not in `X¹`).
146. **Choices.** "`X¹ ≠ X` as M-polyfolds" is read as "`1₀¹` is not sc-smooth"; the
     M-polyfold is built from one chart, so it is a retract, not a general M-polyfold, which is
     all the remark needs. The parameter space is `ℝ` with `C = ℝ ⊕ X` (no boundary). The
     instances of `c₀ →L[ℝ] c₀` need `maxSynthPendingDepth 3`, as `Test.lean` does. The
     argument of item 141 (why a retraction with `C¹` level maps cannot give an example) remains
     unformalized; it is not needed for the example.

## Chapter 5 (The Fredholm package for M-polyfolds; Lean `Polyfold/Chapter5/`)

*Numbering.* The items of this section are numbered in blocks, one block per work package, so that
agents working at the same time do not collide; the gaps in the numbering are unused numbers, not
deleted items. 1–19: WP 5.1, auxiliary norms (Definition 5.1, Lemma 5.2, Proposition 5.3;
`Chapter5/AuxNorm.lean`); 20–39: WP 5.2, compactness (Definition 5.4, Theorems 5.5–5.7, Corollary
5.8, Remark 5.12); 40–59: WP 5.3, bump functions and sc⁺-sections (Definitions 5.9, 5.29, 5.33,
Propositions 5.10, 5.30, 5.35, Theorem 5.34, Lemma 5.11; `Chapter5/BumpFunctions.lean`); 60–79:
WP 5.5, transversality (Definitions 5.15, 5.17, Lemma 5.26, Theorem 5.13;
`Chapter5/Transversality.lean`); 80–99: WP 5.6, general and good position (Theorems 5.18, 5.19,
5.25; `Chapter5/GeneralPosition.lean`); 100–109: WP 5.7, homotopies (Definition 5.20, Lemmas 5.23,
5.24; Theorems 5.22, 5.27 not formalized; `Chapter5/Homotopy.lean`); 110–129: WP 5.8,
partitions of unity (Definitions 5.28, 5.31, 5.36, 5.39, 5.41, Theorem 5.37, Propositions 5.38,
5.42, Corollary 5.44; `Chapter5/PartitionsOfUnity.lean`); 130–139: follow-ups of the round-trip
audit (Remark 5.12 as stated, `Chapter5/SolutionSetClosed.lean`). Statement numbers and pages are
the preprint's *(book 2017: see `BookConcordance.md`)*.

Found while formalizing §5.1 in `Chapter5/AuxNorm.lean` (2026-10-26).

1. **The fibres of `Y_{0,1}` carry no linear or normed structure in the text, and "complete norm"
   is read as "the fibre with `N` is complete"** *(book 2017: Definition 5.1)*. Definition 5.1 (1)
   presupposes that the fibres `(Y_{0,1})_x` are vector spaces on which `N` can be a norm; §5.1
   only says "the fibers `Y_x` have the structure of Banach spaces". The formalization defines
   `(Y_{0,1})_x` as the subspace of `P⁻¹(x)` of the points in `Y_{0,1}` (`StrongBundle.oneFiber`; a
   subspace because the strong bundle charts are linear on the fibres and `F₁ ⊆ F` is a subspace),
   and reads (1) as: `N` is a norm on it and every `N`-Cauchy sequence converges
   (`StrongBundle.IsCompleteFiberNorm`). The text's `|h|₁` is the `F₁`-norm of the fibre component
   of `Φ[1](w)` (`StrongBundle.liftOneFiber`, an injective linear map `(Y_{0,1})_x → F₁`); it
   depends on the chart, but the norms of two charts are equivalent on each fibre, and even locally
   uniformly in the base point (`StrongBundle.exists_norm_liftOne_le_mul`). The fibre is complete
   for `|·|₁` because its image in `F₁` is the slice `{h | (φ(x), h) ∈ K[1]}`, the fixed point set
   of the continuous map `h ↦ R[1](φ(x), h)` (`isClosed_slice`, `complete_liftOneFiber`); the text
   takes this for granted.
2. **Lemma 5.2 needs the charts `Φ[1]` of `Y[1]` for every strong bundle chart, and "(ii) ⇒ (i) is
   obvious" needs that they are homeomorphisms** *(book 2017: Lemma 5.1)*. (ii) quantifies over
   "a strong bundle isomorphism `Φ : Y|V → K`", i.e. over all strong bundle charts compatible with
   the atlas, while `StrongBundleOne.lean` gave the charts `Φ[1] : P⁻¹(V)[1] → K[1]` of `Y[1]` only
   for the charts of the atlas. `StrongBundle.oneChartOf` builds them for every compatible chart,
   with `isChart_oneChartOf` (they are charts of the M-polyfold `Y[1]`: the transition maps are the
   `[1]`-transitions of Definition 2.50) and `mem_oneSet_iff_of_isChart`. In "(ii) ⇒ (i)" the
   bounds give `Φ[1](w_k) → (φ(x), 0)`, and `w_k → 0_x` in `Y_{0,1}` follows from the continuity
   of `Φ[1]⁻¹` on `K[1]`; in "(i) ⇒ (ii)" the set "`|p − q|₀ + |h|₁ < ε`" is a neighbourhood of
   `0_x` in `Y_{0,1}` by the continuity of `Φ[1]`.
3. **Lemma 5.2: the bounds hold only near `x`, and the contradiction argument needs no
   metrizability.** (ii) asks for `c·N(w) ≤ |h|₁ ≤ C·N(w)` for all `w ∈ P⁻¹(V)`, `V` the domain of
   `Φ`; the proof gives them "for `P(w)` close to `x`". The formalization (`Polyfold.lemma_5_2`)
   takes `V` to be a neighbourhood of `x` inside the domain on which the bounds hold, and
   `w ∈ P⁻¹(V) ∩ Y_{0,1}` (`N` and `|h|₁` are defined only there). The upper bound
   `N(w) ≤ (2/ε)|h|₁` is `StrongBundle.exists_le_mul_norm_liftOne` (for any `g` continuous at `0_x`
   and positively homogeneous on the fibres); the lower bound, by contradiction with sequences
   `|h_k|₁ = 1`, `N(w_k) → 0`, is `IsAuxNorm.exists_norm_liftOne_le`, with the neighbourhoods
   `φ⁻¹(B(φ(x), 1/(k + 1)))`, whose points converge to `x` because `φ⁻¹` is continuous on `O`.
   "(i) ⇒ (ii)" holds in every strong bundle chart around `x` (`IsAuxNorm.exists_bounds`), which
   the comparison of Proposition 5.3 uses (two auxiliary norms compared in the same chart). The
   constants `0 < c < C` can always be arranged (`c` can be decreased).
4. **Proposition 5.3, existence: the "partition of unity argument"** *(book 2017: Proposition 5.1)*.
   `Polyfold.proposition_5_3_exists`: `N(w) = Σᵢ ρᵢ(P(w))·|Φᵢ[1](w)|₁` over the charts of the
   atlas, `(ρᵢ)` a partition of unity of `X` subordinate to their domains (`X` paracompact and
   Hausdorff, hence normal; `PartitionOfUnity.exists_isSubordinate`). The steps the text omits:
   `N` is continuous on `Y[1]` (each term vanishes off the closed set `P⁻¹(supp ρᵢ)`, contained in
   the open domain of `Φᵢ[1]`, and the sum is locally finite: `continuous_gluedNorm`); `N` is a norm
   on each fibre and the fibre is complete (`isCompleteFiberNorm_gluedNorm`: near `x` only
   finitely many `ρᵢ` are non-zero, all with `x` in the domain of `Φᵢ`, and their norms are
   uniformly comparable with the norm of one chart around `x`, `exists_uniform_comparison`); the
   bounds of Lemma 5.2 (ii) (`gluedNorm_bounds`), after which Lemma 5.2 gives condition (2).
5. **Proposition 5.3, comparison: "the local compatibility implies the existence of `f`".**
   `Polyfold.proposition_5_3_compare`: Lemma 5.2 "(i) ⇒ (ii)" for `N₀` and `N₁` in one chart
   around `y` gives `r_y > 0` with `r_y N₀ ≤ N₁` and `r_y N₁ ≤ N₀` on the fibres over a
   neighbourhood of `y`; for each point the admissible `r` form a convex set, so the local
   constants glue to a continuous `f : X → (0, ∞)` with values in these sets (a partition of unity
   argument, `exists_continuous_forall_mem_convex_of_local_const`); then `f N₀ ≤ N₁ ≤ f⁻¹ N₀`. In
   the statement, `N₀(h)` and `N₁(h)` stand for `N₀(w)` and `N₁(w)`.
6. **Tameness is not used in §5.1.** The section places the strong bundle over a tame M-polyfold,
   but Lemma 5.2 is stated without tameness, and none of Definition 5.1, Lemma 5.2, Proposition 5.3
   uses it. The comparison with the auxiliary norms of [21] ("our definition is more general than
   the earlier one") is not formalized.

Found while formalizing §5.2 and Appendix 5.4.1 in `Chapter5/Compactness.lean` (2026-10-26).

20. **Theorem 5.7 uses Corollary 3.13 at an arbitrary limit, not Theorem 5.6; `X_∞` has no
    topology in the text** *(book 2017: Theorems 5.2, 5.3)*. The step "`x_k → x` in `X₀`, hence
    `x_k → x` on every level, by Theorem 5.6" needs the convergence of a given sequence of zeros at
    its limit, which is Corollary 3.13 at the point `x`; Corollary 3.13 is stated for a germ `(f, x₀)`
    and the limit `x₀` of the germ (Chapter 3, item 15), so it applies once one knows that the limit
    of zeros is a zero (continuity of the principal part) and a smooth point (regularizing), where
    `(f, x)` is an sc-Fredholm germ (`corollary_3_13_section`). "`X_∞` is a metric space" presupposes
    a topology on `X_∞`, which the text never defines; the formalization uses the initial topology
    of the inclusions `X_∞ → X_m` (`MPolyfold.smoothLevel_topology_eq`, metrizable by Theorem 2.16),
    for which convergence is convergence on every level (`MPolyfold.tendsto_smoothLevel_iff`).
    Theorem 5.7 (`Polyfold.theorem_5_7`) and the compact solution set on every level
    (`Polyfold.isCompact_solutionSet_level`) then follow by sequences. Theorem 5.6
    (`Polyfold.theorem_5_6`) is `theorem_3_12` at a zero. Tameness is not used in Theorems 5.5–5.7.
21. **Corollary 5.8: "it is a priori clear that `f^i` is sc-Fredholm" is not clear, and the bundle
    `P^i : Y^i → X^i` is not defined** *(book 2017: unchanged, Corollary 5.1, p. 158; "tame" dropped;
    only `Y[i]`, `i = 0, 1`, defined, p. 47)* *(book 2021: unchanged, Corollary 5.2.5, p. 213; only `Y[i]`, `i = 0, 1`, defined, p. 68)*. The text defines `Y[i]` for
    `i = 0, 1` (after Definition 2.51), not `Y^i`; the natural `Y¹` is `Y_{1,1} = (Y[0])¹` over
    `X¹ = X₁`, with the fibrewise linear structure on `P⁻¹(x) ∩ Y_{1,1}` and the charts `Φ¹`. This
    shifted strong bundle is not built in the project. What is formalized (`Polyfold.corollary_5_8_chart`):
    the compact solution set in `X₁` (indeed in every `X_i`), and, at every smooth point, the data of
    Definition 3.11 for `f` with `(g − s)¹ : U¹ → F¹` conjugated to the basic germ `h¹` by the index
    raise `Ψ¹` (`IsConjugateToBasicGerm.shift`) and `s¹` an sc⁺-section of `U¹ ◁ F¹`. The shift of a
    basic germ is a basic germ (`IsBasicGerm.shift`), with `C̃` a partial quadrant (needed for
    Proposition 1.17 for germs; it is part of Definition 3.11). For `i ≥ 2` the iteration needs the
    level sets of `X¹` to be those of `X` shifted by one (gap G.6). (Round-trip items V5.13, V5.14:
    the compactness half follows from the project, `RoundTrip/Items/V5_13.lean`,
    `A_gives_B_compact`; "`f^i` is sc-Fredholm" for every `i` is missing mathematics, including
    condition (3) on level `i` (item 22) — the sc-level gap of Chapter 3 item 224.)
    *(2026-11-02: superseded. The shifted strong bundle `P¹ : Y¹ → X¹` is built
    (`StrongBundle.shift`) and Corollary 5.8 is proved for `i = 1` (`Polyfold.corollary_5_8`), for
    `i = 2` (`corollary_5_8_two`) and by iteration for every fixed `i`, with the text's hypotheses
    and without tameness; see items 140–146.)*
22. **The filler condition (3) on level `1` does not follow from condition (3) on level `0`.**
    For `f¹` to have the filled version `g¹`, the map `L = (1 − ρ(0))Dg(0)` must be a topological
    isomorphism `ker Dr(0) ∩ E₁ → ker ρ(0) ∩ F₁`, while Definition 3.4 (3) only gives it on level
    `0`. An sc-operator can be bijective on level `0` and not onto on level `1`: on
    `E_m = {x : |x|_m² = Σ_k e^{2mk} x_k² < ∞}` the right shift `T` has `|T|_m = e^m`, `1 − T/2` is
    invertible on `E₀`, and `(1 − T/2)⁻¹e₀ = Σ_n 2^{−n}e_n ∉ E₁` (since `e²/4 > 1`). For an
    sc-Fredholm germ the level-`1` condition holds, by an argument the text does not give: (a) by
    Lemma 3.17, subtracting the sc⁺-section `y ↦ R(y, f̂(0))` (`f̂(0) ∈ F_∞` at a smooth point)
    reduces to `g(0) = 0` without changing `L`; (b) `Dg(0)` is regularizing (`Dg(0)ξ ∈ F₁ ⇒ ξ ∈ E₁`):
    `Dg(0) − Ds(0)` is conjugated to `Dh(0)` by `Γ(0)` and `Dψ(0)` (because `(g − s)(0) = 0`), `Ds(0)`
    maps into `F₁`, and `Dh(0)(a, w)_W = w − D_aB(0)a` with `D_aB(0)a ∈ W_∞` and `D_wB(0) = 0` (the
    contraction estimate holds with every `ε`); (c) for `k ∈ ker ρ(0) ∩ F₁` and `κ = L⁻¹k`, the
    linearization `A = ρ(0)Dg(0)|_{T₀O}` is Fredholm, so `im A + ρ(0)F₁ = ρ(0)F₀` and there is
    `t ∈ T₀O` with `Dg(0)(t + κ) ∈ F₁`; then `t + κ ∈ E₁` and `κ = (1 − Dr(0))(t + κ) ∈ E₁`. This
    argument is not formalized. *(2026-11-02: formalized in the form of item 144 —
    `IsFillingGerm.mem_range_toBase_of_fillDefect`, `IsFillingGerm.germ_shift` — where the reduction
    to a zero subtracts `Γ(z, −g(0))` composed with `r`, so that the fill defect, and with it `L`,
    does not change; see items 140–146.)*
23. **Theorem 5.5 uses the uniform `(0, 1)` fibre bound of the conjugating isomorphism silently**
    *(book 2017: Theorem 5.1)*. "Without loss of generality ... `f = h + t`" replaces the bound
    `N(f(x)) ≤ 1` on `X` by a bound `|(h + t)(a, w)|₁ ≤ c` in the coordinates of the basic germ. This
    needs: Lemma 5.2 in the chart of the germ (`|Φ[1](w)₂|₁ ≤ A·N(w)` near the point,
    `StrongBundle.IsAuxNorm.exists_norm_liftOne_le` of `AuxNorm.lean`, which holds in every
    compatible chart), and a bound `|Ψ[1](u, k)₂|₁ ≤ M|k|₁` for `u` near `0`
    (`IsStrongBundleMap.exists_fiber_bound_one`, from the continuity of `Ψ[1]` at `(0, 0)` and the
    linearity of the fibre maps). Subtracting the sc⁺-section `s` before the conjugation
    (`|g(u) − s(u)|₁ ≤ A + |s(0)|₁ + 1` near `0`) makes the text's `t = Ψ_*s` and its estimates (83)
    and (85) unnecessary, and gives a neighbourhood independent of the bound `c`
    (`IsSc0ContractionGerm.exists_isCompact_bdd`, `IsBasicGerm.exists_isCompact_bdd`); `C̃` must be
    closed, as in Theorem 3.40.
24. **Theorem 5.5: the way back from local coordinates and the covering are left implicit.** The set
    `{(a, w) ∈ U | |(h + t)(a, w)|₁ ≤ c}` of the appendix lives in the domain `U` of the filled
    version, which contains points that are not in the retract `O ≅ V ⊆ X`; for its closure to say
    anything about `cl_X{x | N(f(x)) ≤ 1}`, the closure of the image of `{x ∈ V | N(f(x)) ≤ 1}`
    must lie in `O`. It does, since `O` is the fixed point set of the retraction `r` in `U`, after
    cutting the compact set on the side of the basic germ down to a closed ball inside `U'`
    (`exists_nbhd_isCompact_closure_bdd`). The last sentence ("since the solution set of `f` is
    compact, the proof ... is complete") stands for: finitely many such neighbourhoods cover
    `f⁻¹(0)`, and the closure of a finite union is the union of the closures (`Polyfold.theorem_5_5`).
    The local statement holds at every smooth point where `(f, x)` is an sc-Fredholm germ, not only
    at zeros.
25. **Slips in the proof of Theorem 5.5** (Appendix 5.4.1, lines 7769–7891): "`z' = h(a, w)`" for
    `(h + t)(a, w)`; "`ℝⁿ ⊕ Y₁`" for `ℝᴺ ⊕ W₁`; "in view of (2) and (3)" for (84) and (86); in `Σ`,
    "`a ∈ ℝⁿ`" for `a ∈ C̃` (`B` is defined on `C̃ ⊕ W` only); the dangling clause after (86); "the
    closed ball in `Y₀`" for `W₀`; in (89), `z = z' − ((1 − P)h + t)(a, w)` mixes the `ℝᴺ`- and
    `W`-components (it is `P z' − P t(a, w)`; then (85) is not needed). In the extracted text (90)
    reads `τ/4` for `τ'/4` (possibly a displaced prime). The theorem is stated for a tame `X` in
    §5.2 and for any `X` in the appendix; tameness is not used.
26. **Definition 5.4: the conventions made explicit** *(book 2017: Definition 5.5)*. "`N(f(x)) = ∞`
    if `f(x)` does not have biregularity `(0, 1)`" is `StrongBundle.AuxLe`; the support of `s` is
    the closure of `{s ≠ 0}`. "Obviously proper implies weakly proper" uses that `{f = s}` is closed
    (`f`, `s` continuous, `Y` Hausdorff) and that a solution of `f(x) = s(x)` outside `U` is a zero
    of `f` (`s = 0` there), hence lies in `U` after all; then `N(f(x)) = N(s(x)) ≤ 1`
    (`StrongBundle.IsProper.isWeaklyProper`, for a continuous `f`). With Theorem 5.5,
    `Polyfold.theorem_5_5_iff`.
27. **Remark 5.12: the completion is not constructed, and closedness is not discussed**
    *(book 2017: Remark 5.3)*. Of a section `s` in the completion of `Γ^{+,1}_U` the argument only
    uses that `s = 0` outside `U` and `N(s(x)) ≤ 1` (both survive uniform limits for
    `ρ(s, s') = sup N(s(x) − s'(x))`); then the solutions of `f + s = 0` lie in
    `{x ∈ U | N(f(x)) ≤ 1}` (`N(f(x)) = N(−s(x))`), whose closure is compact (`Polyfold.remark_5_12`,
    no sc⁺ property used). The solution set itself is compact only if it is closed, i.e. essentially
    if the limit section is continuous, which the remark does not address. The clause "adapted to
    `N`, in the sense that `N(f(x)) ≤ 1` for `x ∈ U`, has the properties stipulated in the
    properness result" is garbled; it is read as "`cl{x ∈ U | N(f(x)) ≤ 1}` is compact".

Found while formalizing the start of §5.3 and Appendix 5.4.2 in `Chapter5/BumpFunctions.lean`
(2026-10-26).

40. **Sc-smooth functions need `ℝ` as an M-polyfold.** "Sc-smooth map `f : X → ℝ`" (Definitions
    5.9, 5.29, 5.33) is Definition 2.14 with target the M-polyfold `ℝ` (constant sc-structure,
    identity chart), which the project did not have: `Polyfold.realPolyfold`. Sc-smoothness of a
    map between M-polyfolds can be checked in one pair of charts around each point, continuity
    included (`MPolyfold.isScSmoothMap_of_local`); this is what makes "extend by `0`" work in
    Theorem 5.34 and Lemma 5.11.
41. **Definition 5.9 "`f ≠ 0`" against Definition 5.29 "not identically zero"** *(book 2017:
    unchanged, Definitions 5.7, 5.13, pp. 161, 174)* *(book 2021: unchanged, Definitions 5.3.1, 5.5.2, pp. 216, 229)*. The two definitions of "admits sc-smooth bump functions" differ:
    Definition 5.29 asks for an `f` that is not identically zero with support in `U(x)`;
    Proposition 5.30's proof starts from "a sc-smooth bump function `g` having support in `U(x)` and
    satisfying `g(0) = 1`", i.e. it needs `g(x) ≠ 0` at the given point. On an M-polyfold there are
    no translations, and even on an sc-Banach space the translation by a vector that is not smooth
    does not preserve the levels, so a bump that is non-zero somewhere in `U(x)` cannot be moved to
    `x`. The formalization reads Definition 5.9 (and Definition 5.33) as `f(x) ≠ 0`
    (`MPolyfold.AdmitsBumpFunctions`, `LocalModel.HasBumpProperty`), keeps Definition 5.29 as
    written (`MPolyfold.AdmitsBumpFunctionsWeak`, implied by the first:
    `AdmitsBumpFunctions.weak`), and assumes the first in Proposition 5.30, Theorem 5.34 and Lemma
    5.11. Whether the weak reading implies the strong one is not settled here. (Round-trip items
    V5.16, V5.17, V5.20, V5.44, V5.51: both project notions are the text's literal and pointwise
    ones (`Iff.rfl`), and this one word is the only obstacle to deriving the text's Proposition
    5.30, Lemmas 5.11, 5.24 and, with the text's misprints corrected (e.g. item 62), Theorems 5.13,
    5.18, 5.19, 5.25, 5.34 from the project's; with the pointwise reading they follow, e.g.
    `RoundTrip/Items/V5_44.lean`, `A_to_BStrong`.) *(2026-11-02: the weak reading gives the
    pointwise one at the smooth points of an sc-Banach space, both hold on Hilbert models, and the
    question is open only at non-smooth points; items 160–163.)*
42. **Proposition 5.30: the function `σ` is misprinted** *(book 2017: unchanged, Proposition 5.5,
    p. 174)* *(book 2021: unchanged, Proposition 5.5.3, p. 230)*. "`σ(s) = 0`
    for `s ≤ 1` and `σ(s) = 1` for `s ≥ 1`" is not a function, and `f = σ ∘ g` needs `g(x) = 1`.
    The formalization (`Polyfold.proposition_5_30`, `proposition_5_10`) takes `f = τ(3g/g(x) − 1)`,
    `τ` the smooth transition (`0` on `(−∞, 0]`, `1` on `[1, ∞)`): `f(x) = 1`, `f ≡ 1` where
    `g/g(x) > 2/3` (a neighbourhood of `x`), `0 ≤ f ≤ 1`, and `f ≠ 0` only where `g ≠ 0`. The
    composition of an sc-smooth function with a `C^∞` function `ℝ → ℝ` is sc-smooth
    (`MPolyfold.IsScSmoothMap.comp_contDiff`).
43. **Theorem 5.34 ("Clearly"): the extension of a local bump need not be continuous** *(book
    2017: unchanged, Theorem 5.11, p. 175)* *(book 2021: unchanged, Theorem 5.5.7, p. 231)*. For "⇐", a bump `f₀` of a chart `φ : V → O` with `supp_O(f₀) ⊆ U(x)` and
    `cl_E(U(x)) ⊆ O` gives `f = f₀ ∘ φ` on `V`, extended by `0`; but `cl_X({f ≠ 0})` may leave `V`:
    for `X = E` with `E₀` a Hilbert space, `V` the open unit ball and the chart
    `φ(u) = u/(1 − |u|₀²)` onto `O = E`, `U(x) = O` satisfies `cl_E(U(x)) ⊆ O` and `f₀ ≡ 1` is
    admissible, while `f` is `1` on `V` and `0` outside. The repair (`Polyfold.theorem_5_34`):
    choose `U₁ ∋ x` with `cl_X(U₁) ⊆ U ∩ V` (`X` is regular) and the local bump in a small ball
    `B(φ(x), r/2)` with `B(φ(x), r) ∩ O ⊆ φ(U₁)`; then `supp(f) ⊆ cl_X(U₁) ⊆ U`, and `f` is
    sc-smooth (it vanishes on the open set `X ∖ supp(f)`). The small ball is admissible in
    Definition 5.33 because a retract is closed near each of its points
    (`closure_inter_ball_subset`: `O ∩ cl(B(z, r/2))` lies in the fixed point set of the retraction,
    which is continuous on its domain `C ∩ W' ⊇ C ∩ B(z, r)`, and `C` is closed). The text's "atlas"
    is read as a family of charts of `X` covering `X`; "⇒" holds for every chart.
44. **Proposition 5.35: "Hilbert space", and why the translation is allowed** *(book 2017:
    Proposition 5.6)*. "`E₀` is a Hilbert space" is formalized as: the norm of `E₀` comes from a
    continuous bilinear form, `‖v‖² = b(v, v)` (`Polyfold.proposition_5_35`); an
    `InnerProductSpace` instance on `E₀` would be a second normed structure on the type, not
    definitionally equal to the one of the sc-scale, so Mathlib's `ContDiffBump` for inner product
    spaces is not used. The proof needs only a continuous quadratic form dominating `κ‖v‖²`
    (`LocalModel.hasBumpProperty_of_quadratic`, which covers spaces isomorphic to a Hilbert space):
    `f(v) = τ(1 − b(v − x, v − x)/ρ)`. "Translating" is legitimate because `f` is `C^∞` on `E₀`
    itself, hence sc-smooth by Corollary 1.20 from the base level
    (`IsScSmooth.of_contDiffOn_finiteDimensional`); for a merely sc-smooth function the translation
    by a non-smooth `x ∈ O` is not covered by the chain rule (it is not an sc-smooth map). Composing
    with any retraction onto `O` gives an sc-smooth function on `O`. The remark before Definition
    5.9 ("this is the case if `X` is built on sc-Hilbert spaces") is
    `MPolyfold.admitsBumpFunctions_of_hilbert`.
45. **The product of an sc-smooth function and an sc⁺-section, and sums of sc⁺-sections, are used
    but not stated.** Lemma 5.11's "`s(y) = β(y)t(y)` is a sc⁺-section" and the finite
    combinations `Σ λᵢsᵢ` of Theorems 5.13 and 5.18 need: `f·s ∈ Γ⁺(P)` for `f` sc-smooth and
    `s ∈ Γ⁺(P)` (`StrongBundle.IsScPlusSection.smul_left`: in a chart `(f·s)^ = (f ∘ φ⁻¹)·ŝ`, by the
    product rule `IsScSmooth.smul`), `s₁ + s₂ ∈ Γ⁺(P)` (`IsScPlusSection.add`), finite sums
    (`isScPlusSection_sectionSum`) and the zero section (`isScPlusSection_fiberZero`).
46. **Lemma 5.11: the bound holds at every point, and neither tameness nor a centred chart is
    needed** *(book 2017: Lemma 5.3)*. (a) The statement's "`N(s(x)) < N(e) + ε`" is trivial at `x`
    (`s(x) = e`); what §5.3 needs (for `Γ^{+,1}_U`) and the proof gives is `N(s(y)) < N(e) + ε` for
    all `y` (`Polyfold.lemma_5_11`). In the proof `ε` is reused for the radius (`β` is supported in
    "`O' ∩ {|y|₀ < ε}`", where `δ` is meant), and "`W|Q`" stands for `Y|Q`. (b) The proof's
    `t(y) = R(y, ẽ)` is an sc⁺-section of `K → O` because `ẽ ∈ F_∞` (`e` is smooth): the constant
    `ẽ₁ ∈ (F¹)_∞` is sc-smooth into `F¹`, and `R[1]` is sc-smooth. (c) "`s = β·t` has the required
    properties" needs the product rule (item 45) and the extension by `0` of a section defined on
    the chart domain: `StrongBundle.isScPlusSection_cutoffSection` (sc⁺ through `Φ[1]` on the chart
    domain, the zero section off `supp(β)`, and these two open sets cover `X`). (d) The bound: `β`
    is chosen with support in `U` and in the open set `{N(t(y)) < N(e) + ε}` (continuity of `N` on
    `Y[1]` and of `t` into `Y[1]`), and `N(β(y)t(y)) = β(y)N(t(y)) ≤ N(t(y))` because `0 ≤ β ≤ 1`
    and `N` is a norm on the fibres. (e) Not needed: tameness of `P` and `X`, the normality of `X`
    ("Since `X` is metrizable, it is a normal space"; the support condition comes from Proposition
    5.30), and a chart centred at `x` (any chart of the atlas around `x` works; centring only turns
    `|φ(y) − φ(x)|₀` into `|y|₀`). The hypothesis "`x` smooth" is kept as in the text; it follows
    from `e` smooth. The bump function hypothesis is Definition 5.9, read as in item 41.
47. **`Γ^{+,1}_U(P)` and its metric.** `StrongBundle.allowableSections`: the `s ∈ Γ⁺(P)` with
    `supp(s) ⊆ U` and `N(s(x)) ≤ 1` for all `x`; the condition is meaningful at every point because
    sc⁺-sections take values in `Y_{0,1}` (`IsScPlusSection.mem_oneSet`). The uniform distance
    `ρ(s, s') = sup N(s(x) − s'(x))` and the remark that `(Γ^{+,1}_U(P), ρ)` is not complete *(book 2017: unchanged,
    p. 162)* *(book 2021: unchanged, p. 217)* are not formalized. (Round-trip item V5.21: `allowableSections` is the text's set (`allowable_eq`), and
    `ρ` is a metric on it for every auxiliary norm, proved from the fibre-norm axioms in
    `RoundTrip/Items/V5_21.lean`, `B2_holds`; not moved into the project. The non-completeness is
    not proved: it needs a concrete bundle and a `ρ`-Cauchy sequence of sc⁺-sections whose limit is
    not sc⁺.) *(2026-11-02: the metric is in the project (`StrongBundle.allowableMetric`), the
    non-completeness is proved for the trivial bundle `ℝ × ℝ → ℝ`, and "not complete" turns out to
    need a hypothesis; items 150–153.)*
48. **Not formalized in WP 5.3**: Definition 5.31 and Theorem 5.32 (Bonic–Frampton, the smoothness
    of the `Lᵖ`-norm, cited from [9]), the remark on `W^{1,4}` and `W^{1,3/2}` (Sobolev spaces,
    gap G.1), and the open question whether sc-smooth bump functions give sc-smooth partitions of
    unity.

Found while formalizing §5.3 (Definitions 5.15, 5.17, Lemma 5.26, Theorem 5.13) in
`Chapter5/Transversality.lean` (2026-10-26).

60. **Theorem 5.13 as formalized** *(book 2017: unchanged, Theorem 5.5, p. 162)* *(book 2021: unchanged, Theorem 5.3.5, pp. 217–218)*. `Polyfold.theorem_5_13_generic`
    (the generic form) and `Polyfold.theorem_5_13` (the text's dense-set form). Hypotheses: `X`
    without boundary (`d_X ≡ 0`, `IsWithoutBoundary`), `X` admits sc-smooth bump functions
    (Definition 5.9 read as `f(x) ≠ 0`, item 41), `f` sc-Fredholm with compact solution set, `N`
    an auxiliary norm, and the tameness hypotheses of item 61. Conclusion: an open `U ⊇ S_f` such
    that (1) for every allowable `s ∈ Γ^{+,1}_U(P)` (`StrongBundle.allowableSections`, item 47)
    `S_{f+s}` is compact, and (2) *generic form*: for every sc⁺-section `s₀` with `supp(s₀) ⊆ U`
    and `N(s₀(x)) ≤ 1 − ε` there are finitely many allowable sc⁺-sections `t₁, …, t_m`, a
    `δ > 0` and a Lebesgue null set `CV ⊆ ℝᵐ` such that for every `λ` with `|λ| < δ`
    (maximum norm) and `λ ∉ CV`: `s_λ = s₀ + Σ λᵢ tᵢ` is allowable, `f + s_λ` is transversal to
    the zero section (Definition 5.15), `S_{f+s_λ}` is compact and, if non-empty, a
    sub-M-polyfold whose induced structure is tame, that of a manifold without boundary of
    locally constant dimension, with regular tangent germ data at every zero of dimension the
    Fredholm index of `(f + s_λ)'(y)` (`StrongBundle.SolutionSetIsManifold`, the conclusion of
    `theorem_3_56_of_surjective`); *dense form*: for every allowable `s'` and `ε > 0` an allowable
    `s` with `N(s(x) − s'(x)) ≤ ε` for all `x` (`StrongBundle.sectionDistAt`, the pointwise form
    of the text's `ρ`) and the same properties. "Generic" is thus made precise as "for every `λ`
    outside a null set of the ball", and the text's "dense subset `O`" as the pointwise density.
    The metric space `(Γ^{+,1}_U(P), ρ)` is not built; `Remark 5.14` and `Remark 5.16` are not
    formalized.
61. **The tameness hypotheses** *(book 2017: Theorem 5.5)* *(book 2021: unchanged, §5.3, p. 216; Theorem 5.3.5, p. 217)*. Theorem 5.13 does not assume
    tameness, but §5.3 opens with "`P : Y → X` a tame strong M-polyfold bundle", and the proof
    uses Theorems 3.18, 3.19 and 3.54, which the project proves for strong bundles whose
    compatible charts have tame base retractions (`htame`, Chapter 3 items 86, 173). The
    formalization takes `htame` for `P` and, since the implicit function theorem is applied to the
    parametrized section `F` of Theorem 3.18 on `ℝᵏ × X`, also for the pull-back bundles
    `π*P → ℝᵏ × X` for every `k` (`StrongBundle.PullbacksHaveTameCharts`), a hypothesis the text
    does not state (tameness of `π*P` is not discussed; `ℝᵏ × X` is tame when `X` is,
    `prod_rn_isTame`, but the base retraction of an arbitrary compatible chart of `π*P` is not
    constrained by that). **The hypothesis `htame` over all compatible charts is very strong**: a
    strong bundle chart `(φ, U, R, Φ)` can be re-equipped with another sc-smooth retraction `r'`
    of `U` onto the same `O` (`R'(u, h) = R(r'(u), h)`, same `K`, same `Φ`), which is again a
    compatible strong bundle chart, and `r'` need not satisfy condition (1) of Definition 2.34
    (`d_C(r'(u)) = d_C(u)` on `U`). For instance, for `X = ℝ` and the trivial bundle, the chart
    `x ↦ (1, x)` with model `O' = {1} × ℝ ⊆ C' = [0, ∞) × ℝ`, `U' = C'`, `r'(a, x) = (1, x)` is
    compatible with the chart `id` and `d_{C'}(r'(0, 5)) = 0 ≠ 1 = d_{C'}(0, 5)`. So `htame` (and
    `PullbacksHaveTameCharts`) can fail for any strong bundle; the natural weaker reading, that the
    chart of Definition 3.11 at each point can be chosen with a tame base retraction (or that the
    charts of a tame strong bundle atlas are tame), would require restating the §3.6 theorems,
    which is not done here (not verified in Lean).
62. **Slips in the statement and proof of Theorem 5.13** (lines 7138–7220). "`N(f(x)) ≤ 1` for
    all `x ∈ X`" is `N(s(x)) ≤ 1`; "the germ `(f, x)` is in good position" is `(f + s, x)`; in
    the proof, `|s₀'(x) − δs₀'(x)|₁` is `N(s₀'(x) − δs₀'(x))`; "`N(s₀(y) + s(λ₀, y)) ≤ 1 − ε/2`"
    should be `≤ 1` (with `δ = 1 − ε/2`, `N(s₀) ≤ 1 − ε/2` and `N(s(λ₀, ·)) ≤ ε/2`); "`W`" in
    the pull-back bundles stands for `π*Y`; "`U ⊂ {λ | |λ| < δ₀} ⊕ X`" is a subset of the
    product. `|λ|` is read as the maximum norm (`‖λ‖` on `Fin m → ℝ`).
63. **The omitted step: for small `λ` every zero of `F(λ, ·)` lies in the neighbourhood where
    `F'` is onto** (`exists_pos_forall_mem_of_isCompact`, the last part of the proof of
    `theorem_5_13_generic`). The text passes from the open neighbourhood `U` of `{0} × S_{f+s₀}`
    to "`U ⊂ {|λ| < δ₀} ⊕ X`" without argument. It needs: for `|λ| ≤ δ₁` the perturbation
    `s₀ + Σ λᵢ tᵢ` is allowable (`N ≤ (1 − ε/2) + m|λ|`, `auxLe_paramSlice`), so by Remark 5.12
    the zeros of `F` over `|λ| ≤ δ₁` lie in the compact `cl{x ∈ U | N(f(x)) ≤ 1}` of Theorem
    5.5, hence form a compact set `Z` (closed, as `F` is continuous); the projection of the
    compact `Z ∖ U` to `ℝᵐ` is closed and misses `0`, which gives `δ₀`.
64. **"It is easily verified that `f + s₀ + s(λ₀, ·)` is transversal"** (lines 7212–7214,
    `isLinSurjAt_paramSlice_of_ker_fst`, `exists_null_isLinSurjAt_paramSlice_near`). The
    linear algebra (`surjective_of_forall_exists_ker_fst`): with `Lin_F(0)(a, u) = Lin_{g_λ}(0)u +
    Σ aᵢ t̂ᵢ(0)` in the product chart (`linAt_paramSection`), `Lin_F(0)` onto and the projection
    `ker Lin_F(0) → ℝᵐ` onto give `Lin_{g_λ}(0)` onto. "λ₀ a regular value of `S̃ → ℝᵐ`" is used
    through the regular tangent germ chart `D` of Theorem 3.54 (2) at a zero of `F`: the
    parametrization `D.φ⁻¹ ∘ Γ` of `S̃` near the point and the `C^∞` map `q = p ∘ D.φ⁻¹ ∘ Γ` on
    the model `V ⊆ N ∩ C`; at a zero over a regular value the derivative of `gmap = ψ ∘ D.φ⁻¹ ∘ Γ`
    (`ψ` the product chart centred at the zero) has `q = pr₁ ∘ gmap + λ` and values in
    `T₀O ∩ ker Lin_F(0)` (chain rule for `F̂ ∘ r ∘ gmap = 0`), so `ker Lin_F(0)` projects onto
    `ℝᵐ`. Only "regular value ⟹ transversal" is needed and proved; the text's "⟺" (the
    converse needs `T_zS̃ = ker F'(z)`, Theorem 3.54 (4), or the dimension count) is not
    formalized. The text's "`T S̃ = ker F'`" is avoided: `range D(gmap) ⊆ ker Lin_F` suffices.
65. **Sard's theorem is applied in the stratified form** (`measure_image_stratCritSet` of
    `Chapter4/FamiliesLocal.lean`, Chapter 4 item 104), on the model `V ⊆ N ∩ C` of the tangent
    germ chart, which is relatively open in a partial quadrant of `N`. Since `∂X = ∅` the points
    of `V` over the zeros are interior points of `N ∩ C` and classical Sard would do, but proving
    this needs the degeneracy index of the induced structure (Lemma 2.26, `theorem_3_27_degIndex`);
    the stratified form makes this unnecessary: regularity on the stratum through `v` already
    gives the surjectivity of `pr₁ ∘ D(gmap)(v)` on that stratum, and
    `D(gmap)(v)(stratum) ⊆ ker Lin_F(0)`.
66. **"We find finitely many allowable sc⁺-sections `s¹_x, …, s^{k_x}_x` such that the range of
    `(f + s₀)'(x)` together with the sections span `Y_x`"** (`exists_spanning_sections`). The
    text does not say how. `Lin(0) : T₀O → K₀` is Fredholm (Proposition 3.52), so its range is
    closed, topologically complemented and of finite codimension in `K₀ = ρ(0)F`; the smooth
    vectors `ρ(0)F_∞ ⊆ K₀ ∩ F_∞` are dense in `K₀` (`ρ(0)` is continuous and preserves the
    levels at the smooth point `0`), so finitely many smooth vectors span a complement
    (`exists_fin_mem_of_dense_of_closedComplemented`); each is `Φ(e)₂` for a smooth point `e` of
    the fibre over `x`, and Lemma 5.11 gives an sc⁺-section through `e` with support in `U` and
    `N(s(y)) < N(e) + 1` for all `y` (item 46), which is rescaled by `1/(N(e) + 1)` to be
    allowable. The density of the smooth vectors is the point the text omits.
67. **"We can carry out the above construction for every `x` ... and obtain a finite open cover
    ... we list all of them as `t₁, …, t_m`"** (the finite subcover and the union of the families,
    `theorem_5_13_generic`, `isLinSurjAt_paramSection_zero_of_comp`). The neighbourhood `U(x)`
    is `{y | (0, y) ∈ V_x}` for the open `V_x` of Theorem 3.54 (1) for the parametrized section
    `F_x` on `ℝ^{k_x} × X` (`exists_isOpen_isLinSurjAt_zero_near`); the compact `S_{f+s₀}` is
    covered by finitely many `U(xᵢ)`, the families are united by an equivalence
    `Σᵢ Fin(k_{xᵢ}) ≃ Fin m`, and the transversality of `F_{xᵢ}` at `(0, y)` gives that of `F`
    (a linear combination over a subfamily is one over the family, `exists_sum_comp_eq`). The
    text's "by construction, its linearization at every `(0, x)` with `x ∈ S_{f+s₀}` is
    surjective" is this step.
68. **The implicit function theorem is applied on `ℝᵐ × X`**: "the interior case, Theorem 3.19"
    needs `∂(ℝᵐ × X) = ∅`, which follows from `∂X = ∅` by exposition Lemma 4.D
    (`isWithoutBoundary_prod_rn`, `d_{ℝᵐ × X} ≤ d_{ℝᵐ} + d_X`, `rnPolyfold_degIndex`), and good
    position at the zeros `(0, y)` of `F`, which is surjectivity when `d = 0` (Chapter 3 item
    173). Theorem 3.54 (1) is used twice: for each `F_x` (item 67) and for `F`
    (`exists_isOpen_goodPosition_of_isLinSurjAt`, the open `V ⊇ {0} × S_{f+s₀}` of zeros in good
    position); Theorem 3.54 (2) (`theorem_3_54_index`) gives the charts of `S̃` for the Sard
    step. `S̃` itself is not built as a manifold: the Sard step is local, on finitely many charts
    covering the compact `Z₀ = {(λ, y) | |λ| ≤ δ/2, F(λ, y) = 0}`, and the null sets are united.
69. **"The solution set `S_{f+s}` is compact" (for the sections of `Γ^{+,1}_U`)** is Remark 5.12
    together with the closedness of the solution set: `f + s` is sc-Fredholm for `s ∈ Γ⁺(P)`
    (Theorem 3.15), hence continuous, and in the metrizable `X` a limit of zeros is a zero
    (`isClosed_solutionSet`, from `IsScSmoothSection.isZeroAt_of_tendsto`). The text's first
    clause ("for sections `s ∈ Γ⁺(P)` having `supp(s) ⊂ U` and `N ≤ 1`") is exactly the
    allowable sections.
70. **Definition 5.15 and its chart independence** *(book 2017: Definition 5.8)*.
    `StrongBundle.IsTransversal g`: `IsLinSurjAt` at every zero (`Lin(z) : T_zO → K_z` onto in a
    chart, Chapter 3 item 173); `StrongBundle.IsLinSurjAt.linAt_surjective`: then onto in every
    chart (`linAt_chart_independence`). "`g'(x) : T_xX → Y_x`" is read in charts (gap G.7).
71. **Definition 5.17 in a chart; its chart independence is not formalized** *(book 2017:
    Definition 5.9)*. `StrongBundle.IsGeneralPositionGerm f y`: in a strong bundle chart around
    `y`, `Lin(z)` onto, and for every presentation `T` of the partial quadrant an sc-subspace
    `B ⊆ T^R_zO = T_zO ∩ E_z` (`reducedTangentSpaceWith`) with `(T_zO)_m = (ker Lin(z))_m ⊕ B_m`
    on every level (the form of Definition 4.21, `IsGeneralPositionRetractAt`). The transport
    to another chart by `A = D(τ ∘ r)(z)` (Proposition 2.30 for `T^R`, `proposition_2_30_reduced`,
    and `ker Lin'(z') = A(ker Lin(z))`) is not done: `linAt_chart_change` exposes `A` only through
    the conjugation identity and the cones, not as the derivative of the transition.
72. **Lemma 5.26 ("clearly general position implies good position")** *(book 2017: no longer a
    lemma; the sentence "Clearly general position implies good position", p. 166, before Remark 5.6)* *(book 2021: unchanged, p. 222, before Remark 5.3.11)*
    (`StrongBundle.IsGeneralPositionGerm.isGoodPositionGerm`). The text omits the interior
    condition of Definition 3.21 and argues in basic germ coordinates. In the chart: an
    sc-complement `B ⊆ T^R_zO` of `ker Lin(z)` in `T_zO` is a good complement (adding a vector
    of `E_z` does not change membership in `C_z`), and `ker Lin(z) ∩ C_zO` has non-empty
    interior because the coordinates `λᵢ`, `i ∈ I(z)`, map `T_zO` onto `ℝ^{I(z)}`
    (`dim T_zO/T^R_zO = d_C(z)`, Proposition 2.36, which needs the chart tame) and vanish on `B`
    (`isInGoodPositionIn_of_scComplement_le_reduced`, the argument of
    `IsGeneralPositionRetractAt.isGoodPositionRetractAt`); Definition 3.53 is then assembled by
    `isGoodPositionGerm_of_linAt_surj` (Chapter 3). Tameness of the chart (`htame`) and `(f, y)`
    an sc-Fredholm germ are the hypotheses used.
73. **Not done in WP 5.5**: the openness of general position along the solution set (needed for
    Theorems 5.18 and 5.25: in a tame chart general position is `ker Lin(z) + E_z = E`, `E_z ⊇
    E_x` near `x`, and `ker Lin(z_v)` is the graph of `Dσ(v)` by `theorem_3_54_ker_eq_tangent`, so
    the condition is open by the continuity of `v ↦ Dσ(v)` on the finite-dimensional kernel); the
    chart independence of Definition 5.17 (item 71); the converse direction of item 64; `ρ` as a
    metric; Remarks 5.14 and 5.16.


Found while repairing the tameness hypotheses of Theorem 5.13 (Chapter 3 items 190–199;
`Chapter5/Transversality.lean`, 2026-10-26).

74. **Item 61 understated the problem: `htame` and `PullbacksHaveTameCharts` are unsatisfiable**
    (Chapter 3 item 190). Not only can they fail: every strong bundle over a nonempty base has a
    compatible chart with a non-tame base retraction (the chart `(1, φ)` with `r'(a, u) = (1, r(u))`
    on `[0, ∞) × U`; argument not machine-checked), and the same holds for `π*P`. So
    `theorem_5_13_generic`, `theorem_5_13`, `StrongBundle.IsGeneralPositionGerm.isGoodPositionGerm`
    (Lemma 5.26), `exists_isOpen_goodPosition_of_isLinSurjAt`, `exists_isOpen_isLinSurjAt_zero_near`
    and `exists_null_isLinSurjAt_paramSlice_near` were vacuous as stated; item 60's account of
    Theorem 5.13 holds for the restated theorems below.
75. **Theorem 5.13 restated** (`theorem_5_13_generic`, `theorem_5_13`): `hf : IsScFredholmSection f`,
    `htame`, `htameP : PullbacksHaveTameCharts` → `hf : IsScFredholmSectionTame f` (Definition 3.51,
    the tame strong bundle §5.3 assumes); conclusions unchanged. The parametrized sections
    `F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` on `ℝᵏ × X` get tame germ data from `theorem_3_18_tame` (the
    product chart of a tame chart is tame, Chapter 3 item 195), and `g = f + s₀` and `f + s_λ` from
    `theorem_3_15_tame`. The lemmas `exists_isOpen_isLinSurjAt_zero_near`,
    `exists_isOpen_goodPosition_of_isLinSurjAt` (conclusion `IsGoodPositionGermTame`) and
    `exists_null_isLinSurjAt_paramSlice_near` (hypothesis `IsGoodPositionGermTame`) take
    `hgF : IsScFredholmSectionTame g` in place of `hgF : IsScFredholmSection g` and `htameP`.
    `StrongBundle.PullbacksHaveTameCharts` is removed. No hypothesis beyond the text's tame strong
    bundle remains.
76. **Definition 5.17 in a tame chart; Lemma 5.26 restated** (`StrongBundle.IsGeneralPositionGerm`,
    `IsGeneralPositionGerm.isGoodPositionGerm`, `IsGeneralPositionGerm.isGoodPositionGermTame`).
    Definition 5.17 was "in some compatible chart" and Lemma 5.26 used `htame` at that chart, for the
    count `dim T_zO/T^R_zO = d_C(z)` (Proposition 2.36), which holds in tame charts only. The
    definition now asks for a tame chart (`IsTameChart`; the text states it for a tame strong bundle,
    and the reduced tangent space `T^R_xX` of Definition 2.38 is that of a tame M-polyfold); Lemma
    5.26 is `hf : IsScFredholmSection f`, `IsGeneralPositionGerm f y` ⟹ `IsGoodPositionGerm f y`
    with no `htame`, and `isGoodPositionGermTame` gives the good position in the tame chart of the
    germ data for `hf : IsScFredholmSectionTame f`. Definition 5.15 (`IsTransversal`, "`f'(x)` onto
    in some chart") had no such hypothesis and is unchanged.
77. **`StrongBundle.IsLinSurjAt.linAt_surjective` moved to `Chapter3/GlobalIFTIndex.lean`** (unchanged:
    the surjectivity of `f'(y)` in one chart gives it in every chart), because Chapter 3 now needs it
    (Chapter 3 item 194).
78. **The audit for Chapter 5** (Chapter 3 item 197): no other hypothesis of `Chapter5/*.lean`
    quantifies over all compatible charts (the `∀ (c : StrongBundleChart PX P)` in
    `BumpFunctions.lean` are local `have`s about given charts).

Found while formalizing Theorems 5.18, 5.19, 5.25 in `Chapter5/GeneralPosition.lean` (WP 5.6,
2026-10-26).

80. **Theorem 5.18 as formalized** *(book 2017: corrected, Theorem 5.6, p. 164, assumes `X` tame)* *(book 2021: corrected, Theorem 5.3.10, p. 220, assumes `X` tame)*. `Polyfold.theorem_5_18` (generic
    form), `Polyfold.theorem_5_18_dense` (the text's dense form), `Polyfold.theorem_5_18_of_family`
    (from a family with the text's properties (i)–(ii)). Hypotheses: `X` **tame** (added; the proof
    uses Theorems 4.22 and 4.23, plan risk 15), `X` admits sc-smooth bump functions (Definition 5.9
    read as `f(x) ≠ 0`), `f` an sc-Fredholm section with tame germ data (`IsScFredholmSectionTame`,
    Definition 3.51; Chapter 3 items 190–199) and compact solution set, `N` an auxiliary norm.
    Conclusion: an open `U ⊇ S_f` with `S_{f+s}` compact for every allowable `s`, and for every
    sc⁺-section `s₀` with `supp(s₀) ⊆ U`, `N(s₀) ≤ 1 − ε`, finitely many allowable `t₁, …, t_m`,
    `δ > 0` and a Lebesgue null set `CV` such that for `|λ| < δ`, `λ ∉ CV`, the perturbation
    `s₀ + Σ λᵢ tᵢ` is allowable and `f + s₀ + Σ λᵢ tᵢ` satisfies
    `StrongBundle.SolutionSetInGeneralPosition`: transversal (Definition 5.15), `(f + s, x)` in
    general position (Definition 5.17) at every zero, `S_{f+s}` compact, a smooth finite-dimensional
    submanifold (Definition 4.13) in general position at each point (Definition 4.21), with induced
    structure a manifold with boundary with corners (Definition 4.1) and tame, and
    `d_{S_{f+s}} = d_X` on `S_{f+s}`. The dense form reads "dense" with the pointwise distance
    `sectionDistAt` (as item 60); the metric space `(Γ^{+,1}_U(P), ρ)` is not built.
81. **The parametrized solution set must be a smooth submanifold in the sense of Definition 4.13,
    and the text never shows it** (plan risk 15). "Hence we can apply Theorem 4.23" needs
    `S̃ ⊆ ℝᵐ × X` with local sc⁺-retractions; the implicit function theorem gives only the tangent
    germ data of Definition 3.25. **Bridge lemma** (`TangentGermChart.exists_scPlusRetraction`,
    `exists_isScPlusRetractionOn`, `MPolyfold.isSmoothSubmanifold_of_isRegular`,
    `StrongBundle.isSmoothSubmanifold_solutionSet_inter`): for regular data (`IsRegular`, which
    `theorem_3_54_two` provides at zeros whose neighbours are in good position), the retraction
    `τ = Γ ∘ π ∘ r` of the proof of Theorem 3.27 (with a retraction `r` onto the chart model) is an
    sc⁺-retraction: `π ∘ r` is sc-smooth into the finite-dimensional `N`, and an sc-smooth map on a
    finite-dimensional space with the constant structure is sc⁺ (`isScPlus_of_isScSmooth_const`:
    all levels of the domain coincide). So the zeros of a section in an open set where they are all
    in good position form a smooth submanifold in the sense of Definition 4.13.
82. **"`T_yS = ker f'(y)`" for the tangent spaces of Definition 4.13, and the chart independence
    of Definition 5.17** (resolves item 71). `exists_tangentSpace_eq_linKer`: near a zero in good
    position, in every strong bundle chart, the tangent space of the chart image of the solution
    set equals `ker Lin(z)`. `⊆` is the chain rule (`tangentSpace_subset_linKer`, the solution set
    is a sub-retract of the zero set); `⊇` is a dimension count: `dim ker Lin(z) = d` in every chart
    (`IsSurjLinOfIndex`, `theorem_3_54_index`), and the tangent space contains `d` independent
    vectors `DΓ(v)bᵢ` in the chart of the bridge retraction (`exists_linearIndependent_tangentSpace`),
    carried to every chart by the transition maps (`HasIndepTangent.transport`,
    `chart_change_of_transport`). Consequently (`exists_isGeneralPositionGerm_iff`), at the zeros near
    a zero in good position, **Definition 5.17 holds iff the solution set is in general position in
    the sense of Definition 4.21**, and both are chart independent.
83. **Openness of general position along the solution set** (item 73; used without proof in
    Theorems 5.18 and 5.25: "the properties (i)–(ii) hold for all `(λ, y) ∈ S̃`", and "in view of
    Theorem 3.54 ... in general position"). `exists_isOpen_isGeneralPositionGerm`, for `X` tame:
    item 82 turns general position of `f` into general position of the submanifold `S_f ∩ V`, which
    is open along it by Theorem 4.22 (3) (`theorem_4_22`), and back. The route of item 73 (the
    continuity of `v ↦ Dσ(v)` on the graph) is not needed. `IsGeneralPositionAt.congr_nhds`:
    Definition 4.21 depends only on the germ of the submanifold.
84. **Properties (i)–(ii) and the construction of the sections** (`StrongBundleChart.IsParamGP`,
    `exists_sections_isParamGP`, `isGeneralPositionGerm_paramSection_of_isParamGP`,
    `isParamGP_of_isGeneralPositionGerm`, `IsParamGP.comp`). (i)–(ii) are read in a tame chart
    centred at `x`: `Lin_g(0)(T₀O) + span{t̂ᵢ(0)} = K₀`, and every `w ∈ T₀O` is `u + e`, `e ∈ E_0`,
    with `Lin_g(0)u + Σ aᵢ t̂ᵢ(0) = 0` for some `a`. The text's "a linear subspace `L` complementing
    `T^R_xX`" must consist of smooth vectors, since the sections through the points of `f'(x)L` are
    those of Lemma 5.11, which needs smooth points of the fibre: the coordinates `λ_{I(0)}` map
    `T₀O` onto `ℝ^{I(0)}` (Proposition 2.36) and already map its dense smooth vectors onto it, so
    smooth `lᵢ` with `λ(lᵢ) = eᵢ` exist, and `Lin_g(0)lᵢ` is smooth (`Lin` is an sc-operator at the
    smooth point). "At this point the combined system of sections already satisfies (i) and (ii)" —
    i.e. `(F, (0, x))` is in general position — needs two steps: the algebraic complement of
    `ker F'(0, x)` inside `ℝᵐ ⊕ T^R` gives good position of `F` (with the interior condition of
    Definition 3.21), and then `ker F'(0, x) = T S̃` (item 82) is finite-dimensional and smooth, so
    the sc-complement inside `T^R` exists (`exists_scComplement_le`). "Adding more sections" keeps
    (i)–(ii) (linear algebra), and they hold at the nearby `(0, y)` by item 83.
85. **Other slips in the statement and proof of Theorem 5.18** (lines 7254–7341). The proof says
    "we follow the ideas of the proof of Theorem 5.22 in [21]" (a reference to the paper's own
    numbering); `S̃ = {(λ, y) | |λ| < 2ε and y ∈ X}` omits the equation `F(λ, y) = 0`; "a smooth
    manifold with boundary with corners containing `{0} × S_f`" is the submanifold
    `S̃ ∩ W ∩ {|λ| < δ}` of item 81, whose closure is compact by Theorem 5.5 and Remark 5.12 (the
    text's "`p⁻¹({|λ| ≤ ε})` is compact" is the omitted step of item 63); Theorem 4.23 is used in
    the countable-cover form of Chapter 4 item 103 (`theorem_4_23_of_subset`); "`T_zS_λ` has a
    sc-complement contained in `T^R_xX`" is Definition 4.21 for `S_λ`, and the general position of
    the section `(f + s_λ, x)` (Definition 5.17, the statement's claim) needs item 82 again, after
    the good position of `(f + s_λ, x)` (`isGoodPositionGermTame_of_isGeneralPositionAt`, from the
    transversality of the Sard step of Theorem 5.13 and `T S_λ ⊆ ker`). "Replacing `f + s₀` by
    `f` and `N` by `cN`" is not needed: the proof keeps `s₀`.
86. **Theorem 5.25 as formalized** *(book 2017: absent)* *(book 2021: absent)* (`Polyfold.theorem_5_25`): `X` tame
    with bump functions, `f` proper (`IsProper`, Definition 5.4) with tame germ data, `N` an
    auxiliary norm: an open `U ⊇ S_f` with `S_{f+s}` compact for allowable `s`, and an allowable
    `s` with `(f + s, x)` in good position (in a tame chart) at every zero and the conclusions of
    item 80 (in particular the corner structure). Proof: Theorem 5.18 with `s₀ = 0`, a parameter
    outside the null set (the ball has positive measure), Lemma 5.26. Slips (plan risk 18): "in view
    of Theorem 3.54 ... in general position" needs item 83 (3.54 is about good position); "`x ∈ S_f`"
    is `x ∈ S_{f+s₀}`; "Theorem 5.22 [20]" is a garbled reference.
87. **Theorem 5.19 as formalized** *(book 2017: unchanged, Theorem 5.7, p. 167)* *(book 2021: unchanged, Theorem 5.3.12, p. 222)* (`Polyfold.theorem_5_19`, generic
    form): bump functions, `f` with tame germ data and compact solution set, `(f, x)` in good
    position at the zeros on `∂X`. Conclusion: `U` as before, finitely many allowable `tᵢ` with
    `supp(tᵢ) ∩ ∂X = ∅`, `δ > 0`, a null set `CV`, such that for `|λ| < δ`, `λ ∉ CV`,
    `s_λ = Σ λᵢ tᵢ` is allowable and vanishes on the open neighbourhood `X ∖ supp(s_λ)` of `∂X`
    (the text's "`s(x) = 0` near `∂X`"; "arbitrarily small" as `λ → 0`), `f + s_λ` is transversal,
    in good position at every zero, with compact solution set, a sub-M-polyfold with the structure of
    a manifold with boundary with corners (Theorem 3.57). The text's tameness of `X` is not used.
    "For every `x ∈ S_{f+s}` the pair `(f, x)` is in good position" is `(f + s, x)` (plan risk 16).
88. **Theorem 5.19: the parametrized section is in general not in good position at the boundary
    zeros, so "as before" does not apply** (not verified in Lean). At a zero `(0, x)`, `x ∈ ∂X`,
    where all `tᵢ` vanish, `ker F'(0, x) = ℝᵐ × ker f'(x)`. If `ℝᵐ × K` had a good complement `Y`
    in `ℝᵐ × T_xX` for the cone `ℝᵐ × C_x` (Definition 3.21 with constant `ε`), then for `(a, 0)`
    with `|a|` large and any `y ∈ Y` with `‖y‖ ≤ ε|a|`, `(a, y₂) ∈ ℝᵐ × C_x`; so the second
    components of `Y` lie in `C_x ∩ −C_x = E_x` and `K + E_x ⊇ T_xX` — a general position condition
    which good position does not imply (e.g. `K = ℝ(1, 1)` in the corner `[0, ∞)²` is in good but not
    in general position). So Theorem 3.54 cannot be applied to `F` at these points. The proof here
    avoids it: the sections are supported off `∂X ∪ cl V₁` (`V₁` a neighbourhood of `S_f ∩ ∂X` on
    whose closure the zeros of `f` are in good position, `theorem_3_54_one'`); on `V₁`,
    `f + s_λ = f` and the good position is that of `f` (`IsGoodPositionGermTame.congr_nhds`: good
    position depends only on the germ of the section); off `V₁` the zeros are interior points
    (`d = 0`), where good position is surjectivity and the implicit function theorem and the Sard
    step of Theorem 5.13 apply to `F`.
89. **Not done in WP 5.6**: the metric space `(Γ^{+,1}_U(P), ρ)` (density is pointwise, as in item
    60); a dense form of Theorem 5.19; Remark 5.21 and Theorems 5.22, 5.27 (items 100–104).

Found while formalizing Definition 5.20 and Lemmas 5.23, 5.24 in `Chapter5/Homotopy.lean`
(WP 5.7, 2026-10-26).

100. **Definition 5.20 as formalized** *(book 2017: Definition 5.10)*
    (`StrongBundle.IsGenCompactHomotopy`). "Tame strong bundle" is read as `X` tame with `f` having
    tame germ data (`IsScFredholmSectionTame`, Definition 3.51, as in Chapter 3 items 190–199);
    "`t : X → [0, 1]` sc-smooth surjective" as an sc-smooth `t : X → ℝ` with `t(X) = [0, 1]`;
    "`X_t` is a tame M-polyfold" as "`t⁻¹(τ)` is a sub-M-polyfold (Definition 2.19) whose induced
    structure (Proposition 2.21) is tame"; "`f_t = f|X_t` is an sc-Fredholm section of `Y|X_t`" as:
    the section `a ↦ (a, f(a))` (`restrictSection`) of the pull-back `ι*Y` along the inclusion
    `ι : X_t → X` (Proposition 2.54, `StrongBundle.pullback`; `ι` sc-smooth by Proposition 2.21)
    has tame germ data. The text does not say what `Y|X_t` is; the pull-back is the only strong
    bundle structure available. "`(f|Xᵢ, P|Yᵢ) = (fᵢ, Pᵢ)`" is an identification of given problems
    with the restrictions, which in type theory needs an isomorphism of strong bundles (Remark 5.21
    says so); the formalization takes the restrictions to `X₀ = t⁻¹(0)` and `X₁ = t⁻¹(1)` as the end
    problems, and Remark 5.21 is not formalized. The text's hypothesis that the end problems have
    compact solution sets is a consequence
    (`IsGenCompactHomotopy.isCompact_solutionSet_restrict`: `S_{f|X_t} = S_f ∩ X_t`, closed in
    the compact `S_f`). (Round-trip item V5.41: the project's notion is the text's for a bundle with
    an equivalent strong bundle atlas whose base retractions are tame, `RoundTrip/Items/V5_41.lean`,
    `B_of_project`, `B_iff_tame`; that every strong bundle over a tame `X` has one is believed true,
    by rebuilding the charts over tame base retractions, but not constructed.)
101. **Lemma 5.23 and the hidden hypothesis of Theorem 5.22** *(book 2017: unchanged, Lemma 5.4,
     Theorem 5.8, pp. 168–169)* *(book 2021: corrected, Definition 5.3.13 (3), p. 223, now asks `dt(x)` onto at every smooth `x`, which gives the `Z` of the proof of Theorem 5.3.15, p. 224)*
    (`lemma_5_23`, `ne_zero_of_isCompl_ker`, `exists_isCompl_ker_of_ne_zero`). The proof of
    Theorem 5.22 says: "since `x` is a smooth point, we find a one-dimensional smooth linear
    sc-subspace `Z ⊂ T_xX` such that `T_xX = Z ⊕ ker(dt(x))`". Such a `Z` exists if and only if
    `dt(x) ≠ 0` on `T_xX`: for `dt(x) = 0`, `ker dt(x) = T_xX` and the only complement is `0`
    (`ne_zero_of_isCompl_ker`), and then `b_τ` with `dt(x) ∘ b_τ = τ` exists only for `τ = 0`. The
    theorem does not assume that `t` is a submersion at the critical points of `t|S` (nor at all),
    so this is a **hidden hypothesis** of Theorem 5.22 (plan risk 17). With `dt(x) ≠ 0`, `Z` can
    be spanned by a vector of any spanning set (`exists_isCompl_ker_of_ne_zero`, e.g. the dense
    smooth vectors), and Lemma 5.23 is linear algebra (`lemma_5_23`, under `ℓ ≠ 0`); "sc-operator"
    is automatic since `T_xS` is finite-dimensional and `Z` smooth. (Machine-checked in the
    round-trip audit: `RoundTrip/Items/V5_42.lean`, `not_BLiteral`: without `dt(x) ≠ 0` the first
    sentence fails for the trivial bundle `ℝ¹ × ℝ⁰ → ℝ¹`, the zero section and `t = 0`. The same
    file corrects the example above: `exists_isCompl_ker_of_ne_zero` needs `D` to span `T`
    algebraically, which the dense smooth vectors do not in infinite dimensions; the smooth `Z`
    comes instead from continuity and density, `exists_splits`.)
102. **Lemma 5.24 as formalized; the graph is not needed** *(book 2017: Lemma 5.5)*
    (`exists_scPlusSection_linAt`, `lemma_5_24`, with `scDeriv_smul_apply`,
    `scDeriv_clm_sub_apply`, `chartLinCutoff`, `isScSmoothMap_chartLinCutoff`,
    `principal_sectionSmul`, `sectionSupport_sectionSmul_subset`). The linearization `s'(x)` is read
    in a strong bundle chart (`linAt`), `T_xS` as a finite-dimensional subspace `K ⊆ T_zO` (the
    text's `T_xS = ker f'(x)`, finite-dimensional by Proposition 3.52), `b_τ` as a linear
    `b : K → T_zO`, and "the operator `f'(x) ∘ b_τ` has a one-dimensional image spanned by some
    smooth point `e ∈ Y_x`" is a hypothesis (`Lin_f(z)(b v) ∈ ℝ·Φ(e)₂` for a smooth point `e` of
    the fibre; the text's justification "the image of any vector in `T_xS` belongs to `Y_∞`" is not
    formalized). The text's construction uses the local graph `q ↦ q + δ(q)` of `S` over `T_xS` and
    a complement `V`; it is not needed: with `Lin_f(z)(b v) = λ(v)·Φ(e)₂`, a continuous linear
    functional `ℓ` on the model space extending `−λ` (Hahn–Banach on the finite-dimensional `K`)
    and the section `s = g·sₑ`, `sₑ` the sc⁺-section through `e` of Lemma 5.11 and
    `g = β·ℓ(φ(·) − φ(x))` with a bump function `β ≡ 1` near `x`, one has `s(x) = 0` and
    `Lin_s(z)v = ℓ(v)·Φ(e)₂` on `T_zO` (product rule; `Dr(z) = 1` on `T_zO`). The text's case
    distinction ("if this operator is the zero operator we can take `s = 0`") is not needed, and
    the text's `j : L → ℝ` with `ker(s'(0)|T_xS) = ker(f'(x) ∘ b_τ)` is replaced by `ℓ`. The
    section has `supp(s) ⊆ U` for any prescribed open `U ∋ x` ("sufficiently small support").
103. **Theorem 5.22 (Morse-type structure) is not formalized** *(book 2017: Theorem 5.8)* *(book 2021: partly corrected, Theorem 5.3.15, pp. 223–228: (5.12) now has `T*_yS_λ`; the other slips listed unchanged; the hidden hypothesis of item 101 is now in Definition 5.3.13 (3))*. It
    needs finite-dimensional Morse theory on manifolds with boundary, the section
    `(λ, y) ↦ d(t|S_λ)(y)` of the cotangent bundle of the solution set, a parametric Sard theorem,
    and the family of embeddings `Φ_λ : S → S̃`, `Φ_λ(S) = {λ} × S_λ`, which is an Ehresmann-type
    trivialization (a family version of the implicit function theorem on a manifold with boundary),
    not "the classical standard implicit function theorem"; none of this is in Mathlib or the
    project, and the statement needs the hidden hypothesis of item 101. Slips noted: "`∂X = X₀ X₁`"
    means `∂X = X₀ ⊔ X₁`; "`T_yS_λ`" in (79) and "`T*_yM_λ`" are `T*_yS_λ`; `ℝᵈ` and `ℝᵐ` are used
    for the same parameter space; "(f, x) is in good position for all `x`" in the proof should be
    "general position" (the hypothesis just achieved); "Theorem 5.22 in [21]" and "[20]" refer to
    the papers' numbering. The linear algebra of (80)–(81) is what Lemmas 5.23 and 5.24 provide.
104. **Theorem 5.27 (cobordism between good position perturbations) is not formalized** *(book
    2017: absent)* *(book 2021: absent)*: the text states it with "the proof is left to the reader".

Found while formalizing the rest of Appendix 5.4.2 in `Chapter5/PartitionsOfUnity.lean`
(2026-10-26).

110. **Definitions 5.28 and 5.36: the readings** *(book 2017: Definitions 5.12, 5.16)*. A partition
     of unity is Mathlib's `PartitionOfUnity ι X` (continuous `ρᵢ ≥ 0`, locally finite supports,
     `Σᵢ ρᵢ = 1`), subordinate to `(Uᵢ)` when `cl{ρᵢ ≠ 0} ⊆ Uᵢ`, with sc-smooth `ρᵢ`
     (`MPolyfold.IsScSmoothPartitionOfUnity`); "for every open covering" quantifies over index
     types in the universe of `X` (`MPolyfold.AdmitsScPartitionsOfUnity`). In Definition 5.36
     (`LocalModel.HasApproxProperty`) the open `V ⊆ O` is `O ∩ W` with `W` open in `E₀`,
     `cl_C(V)` is the closure in `E₀` (`C` is closed), and the supports of `f` and `g` are taken
     in `O` (the closure of `{f ≠ 0}` in `O`).
111. **Theorem 5.37 "(i) ⇒ (ii)": `cl_X(W) ⊆ U` does not follow from `cl_C(V) ⊆ O`, and `f ∘ φ` is
     only continuous** *(book 2017: unchanged, Theorem 5.12, p. 176)* *(book 2021: unchanged, Theorem 5.5.10, p. 232)*. The proof calls `f ∘ φ` "sc-smooth" (`f` is
     the continuous function of Definition 5.36) and asserts `cl_X(φ⁻¹(V)) ⊆ U`. Counterexample:
     `X = E` with `E₀` a Hilbert space, `U` the open unit ball, the sc-diffeomorphism
     `φ(u) = u/(1 − |u|₀²)` onto `O = E` (inverse `v ↦ 2v/(1 + (1 + 4|v|₀²)^{1/2})`; both are a
     `C^∞` function of `|·|₀²` times the identity, hence sc-smooth), `V = O`, `f ≡ 1`: then
     `cl_C(V) ⊆ O`, `W = U`, `cl_X(W) ⊄ U`, the extension `g` of `f ∘ φ` by `0` is the indicator
     of the open ball (not continuous) and `U₀ = {g < ε/2}` is not open. Repair
     (`Polyfold.hasApproxProperty_restrict`, `Polyfold.theorem_5_37`): since (ii) asks only for
     *an* atlas, take the charts restricted to open `s` with `cl_X(s) ⊆ dom φ`; then for closed
     `A ⊆ φ(s)` the set `φ⁻¹(A)` is closed in `X` (`MChart.isClosed_inter_preimage`), so `g`
     vanishes off the closed set `φ⁻¹(cl V) ⊆ s` and is continuous. Whether under (i) *every*
     chart has the approximation property is not settled here: it needs approximations on the
     open set `dom φ`, for instance from partitions of unity on open subsets of `X` (an exhaustion
     of `dom φ` by closed shells, using metrizability, Theorem 2.16), which the text does not
     provide. Simplifications: the set `W̃ = {g > ε/4}` is not needed (the sets `U_x`, `x ∈ φ⁻¹(V)`,
     need only lie in `φ⁻¹(V)`, since subordinate means `supp β_x ⊆ U_x`), and the estimate gives
     `|g − ĝ| ≤ ε/2` (`PartitionOfUnity.abs_sub_finsum_mul_le`). (Machine-checked in the round-trip
     audit: read literally, "the sc-smooth function `f ∘ φ`" fails on the one-chart M-polyfold `ℝ`,
     which admits sc-smooth partitions of unity, with `f = min(|x|, 1)`;
     `RoundTrip/Items/V5_55.lean`, `not_B`.)
112. **Theorem 5.37 "(ii) ⇒ (i)": the refinement, the closure in `O`, and the extension by `0`.**
     (a) "A refinement `(W_λ)_{λ ∈ Λ}` with the same index set, `W_λ ⊆ V_λ` and
     `cl_X(W_λ) ⊆ U_{τ(λ)}`" does not exist in general (the cover `{X}`, `X` not inside one chart
     domain). (b) Hypothesis (ii) is applied to `(f'_λ, φ(W_λ), 1/2)` without ensuring
     `cl_C(φ(W_λ)) ⊆ O`, which `cl_X(W_λ) ⊆ U` does not give (the inverse of the chart of item 111).
     (c) The extension of `g_λ ∘ φ` by `0` is continuous only because `cl_X(W_λ) ⊆ dom φ` (as in
     item 111). The formalization (`Polyfold.exists_isScSmoothMap_urysohn`,
     `Polyfold.admitsScPartitionsOfUnity_of_approx`): small neighbourhoods `N` with
     `cl_X(N) ⊆ dom φ` and `φ(N)` inside half a ball contained in the domain of a retraction onto
     `O` (`MChart.exists_small_nhds`, with `closure_inter_ball_subset` of `BumpFunctions.lean`),
     the approximation property transported to `X` (`LocalModel.HasApproxProperty.exists_approx`),
     and the text's estimate `ĝ_x ≥ 1/2` where `f_x = 1`, give **sc-smooth Urysohn functions**
     `F = τ(4 Σ ĝ_x − 1)` for disjoint closed sets; then Mathlib's
     `BumpCovering.exists_isSubordinate_of_prop` produces a bump covering indexed by `Λ` with
     sc-smooth functions, and `BumpCovering.toPartitionOfUnity` (`ρᵢ = fᵢ ∏_{j < i}(1 − f_j)`,
     locally a finite product) replaces the quotient `ĝ_λ / Σ ĝ`. Needed and not stated: locally
     finite sums and finite products of sc-smooth functions are sc-smooth
     (`isScSmoothMap_real_finsum`, `isScSmoothMap_real_finsetProd`), and a function supported in a
     chart domain and sc-smooth in the chart is sc-smooth (`isScSmoothMap_real_of_chart`).
     Metrizability, used twice in the text, is not needed (paracompact Hausdorff spaces are
     normal).
113. **Proposition 5.38 is not "an immediate consequence of Theorem 5.37"** *(book 2017:
     Proposition 5.7)* *(book 2021: unchanged, Proposition 5.5.11, p. 234)*. Theorem 5.37 produces some atlas with the property, not the given local
     model, and applying "(i) ⇒ (ii)" to the M-polyfold `O` needs sc-smooth partitions of unity on
     `O`, i.e. on the domain of a retraction, a relatively open subset of `C` (partitions of unity
     on open subsets). The formalization (`Polyfold.proposition_5_38`) reads "the sc-Banach space
     admits smooth partitions of unity" as "`E₀` admits `C^∞` partitions of unity"
     (`AdmitsContDiffPartitionsOfUnity`) and repeats the argument of "(i) ⇒ (ii)" in `E₀`:
     `A = {x ∈ O | f(x) ≥ ε/2}` is closed in `E₀` because `cl(V) ⊆ O`, so `E₀ ∖ A` and balls
     `B(x, r_x) ⊆ W` (`x ∈ V`, `f` varying by `< ε/2` on `O ∩ B`) cover `E₀`; `g = Σ β_x f(x)` is
     `C^∞` on `E₀`, hence sc-smooth (Corollary 1.20), and composed with any retraction.
114. **Definitions 5.31, 5.39, 5.41: the readings** *(book 2017: Definitions 5.14, 5.17, 5.18)*.
     `HasContDiffBump V k`: a `C^k` `f ≠ 0` with bounded support. `c₀(Γ)` (`Polyfold.cZero`) is
     the subspace of `ℓ^∞(Γ)` of functions tending to `0` along the cofinite filter, equivalent to
     the text's "`{γ | |f(γ)| > ε}` finite for every `ε > 0`" (`mem_cZero_iff`); the norm is the
     supremum (`norm_cZero`; the text's "max" is attained for `f ≠ 0`). "Homeomorphic embedding" is
     `Topology.IsEmbedding` (`IsCoordinatewiseContDiffEmbedding`). WCG (`IsWCG`): a set `K`
     compact in `WeakSpace ℝ V` with `cl(span K) = V`. "Reflexive", used in Proposition 5.42 but
     not defined in the text, is the surjectivity of `V → V''` (`IsReflexive`).
115. **Proposition 5.42: both cases are formalized; Kakutani's theorem is in Mathlib in another
     form** *(book 2017: Proposition 5.8)* *(book 2021: unchanged, Proposition 5.5.15, p. 235)*. (i) The weak compactness of the unit ball of a reflexive
     space is `NormedSpace.isCompact_closure_of_isBounded` (Banach–Alaoglu in `V''` and the
     embedding of `V` with its weak topology into `V''` with its weak-* topology): the weak closure
     of the ball is weakly compact, and its span is `V` (the text's "Clearly `E = span(B)`", here
     `span_closedBall_eq_top`) (`Polyfold.proposition_5_42_reflexive`). (ii) The text's `{0} ∪
     {xₙ/n}` for a dense sequence of the unit ball (index range missing, "`(xₙ)_{n≥}`") is replaced by
     a dense sequence `(yₙ)` of `V` scaled by `1/((n + 1)(|yₙ| + 1))`: a null sequence with its
     limit is compact, hence weakly compact, and its span contains every `yₙ`
     (`Polyfold.proposition_5_42_separable`).
116. **Corollary 5.44: the proof's two references are off, and "Hilbert ⇒ reflexive" is proved**
     *(book 2017: Corollary 5.2)* *(book 2021: unchanged, Corollary 5.5.17, p. 235)*. (a) Theorem 5.43 enters as the explicit hypothesis
     `GodefroyTroyanskiWhitfieldZizlerStatement (E₀) ∞` (`Polyfold.corollary_5_44`). (b) "Hilbert"
     is `‖v‖² = b(v, v)` for a continuous bilinear `b`, as in Proposition 5.35 (item 44); "a
     Hilbert space is reflexive" is proved (`isReflexive_of_hilbert`: the parallelogram law gives an
     inner product with the same norm, `InnerProductSpace.ofNorm`, and every `φ ∈ V''` is `J(y)` for
     the Riesz representative `y` of `x ↦ φ(⟨x, ·⟩)`), then Proposition 5.42 (i). (c) What Theorem
     5.43 needs is a classical `C^∞`-bump on `E₀` (`τ(1 − |v|²)`, `hasContDiffBump_of_hilbert`),
     not the sc-smooth bump functions the text recalls. (d) "it admits sc-smooth partition of
     unity" should be "`E₀` admits `C^∞` partitions of unity", and "in view of Theorem 5.37" should
     be "in view of Proposition 5.38" (item 113). With Theorem 5.37: an M-polyfold built on
     sc-Hilbert spaces admits sc-smooth partitions of unity under the same hypothesis in the charts
     (`MPolyfold.admitsScPartitionsOfUnity_of_hilbert`).
117. **Cited theorems not formalized: 5.32, 5.40, 5.43** *(book 2017: Theorems 5.10, 5.13, 5.14)*.
     Theorem 5.32 (Bonic–Frampton: smoothness of the `p`-th power of the `Lᵖ`-norm, [9] Theorem 1),
     Theorem 5.40 (Toruńczyk: `C^k` partitions of unity iff a coordinate-wise `C^k` homeomorphic
     embedding into some `c₀(Γ)`, [9] Theorem 30) and Theorem 5.43 (Godefroy–Troyanski–Whitfield–
     Zizler [12]: a WCG space with a `C^k`-bump function admits `C^k` partitions of unity, [9]
     Theorem 31) are deep Banach space geometry, and nothing on the main line uses partitions of
     unity (the transversality theorems use bump functions, whose Hilbert case, Proposition 5.35,
     is elementary). Theorem 5.40 is recorded as the statement `TorunczykStatement V k` (not used),
     Theorem 5.43 as `GodefroyTroyanskiWhitfieldZizlerStatement V k`, the explicit hypothesis of
     Corollary 5.44; Theorem 5.32 is used only in the remarks of item 118 and is not stated.
118. **The `Lᵖ` and Sobolev remarks are not formalized** (lines 7962–7979): "we deduce immediately
     for the Sobolev spaces `W^{k,p}(Ω)` that the usual norms have the same differentiability as
     `|·|_{Lᵖ}`", the bump function `β(|x|ᵖ)` of `Lᵖ`, and the remark that `W^{1,4}(Ω)` with
     `E_m = W^{1+m,4}(Ω)` admits sc-smooth bump functions while for `W^{1,3/2}(Ω)` the
     straightforward one is only sc¹ (with the open question whether an sc-smooth bump exists). They
     need Sobolev spaces and their sc-structures (gap G.1) and Theorem 5.32. In the extracted text
     "`E_m = (W^{1+m,4}(Ω)`" has an unbalanced parenthesis.
119. **Partitions of unity give bump functions** (the easy direction of the open problem stated
     after Definition 5.29): `MPolyfold.AdmitsScPartitionsOfUnity.admitsBumpFunctions` (for
     `x ∈ U`, the function attached to `U` of a partition of unity subordinate to `{U, X ∖ {x}}` is
     `1` at `x`), with bump functions in the sense of Definition 5.9 read as `f(x) ≠ 0` (item 41).
     The converse, open in the text, is not addressed.
120. **Slips in Appendix 5.4.2 after Proposition 5.35** (lines 7890–8197): "Fry and McManusi" (and
     "Epostiones" in [9]), "Godefry" in [12] (Godefroy); Theorem 5.32 "(1) If is an even integer"
     (`p` missing, also in (2)); in the proof of Theorem 5.37 the final estimate writes `β₀(x)g(y)`
     for `β₀(y)g(y)` and `β_{x_i}(z)` for `β_{x_i}(y)`, "for all `y ∈ U`" for all `y ∈ X`, and
     "`f|Q_λ ≡ 1`" for `f_λ|Q_λ ≡ 1`; hypothesis (ii) is used with "`< 1/2`" while Definition 5.36
     gives "`≤ ε`" (enough: `ĝ_λ ≥ 1/2 > 0` on `Q_λ`); Proposition 5.42: "compact. in the weak
     topology"; Corollary 5.44: "has the smooth approximation property" for the sc-smooth one.

Follow-ups of the round-trip audit (`RoundTrip/`, item V5.22): Remark 5.12 as stated
(`Chapter5/SolutionSetClosed.lean`, 2026-11-01).

130. **Remark 5.12 as stated is now proved: for every `s` in the completion of `Γ^{+,1}_U(P)`
     the solution set of `f + s = 0` is closed, hence compact (revises item 27).** Item 27: the
     remark's argument gives `S_{f+s} ⊆ {x ∈ U | N(f(x)) ≤ 1}` and so a compact closure
     (`Polyfold.remark_5_12`), but the closedness of `S_{f+s}` is not discussed in the text and was
     left open in the project. The points of the completion are now represented by sections:
     `StrongBundle.IsInAllowableCompletion N U s` says that `s` is a section with values in
     `Y_{0,1}` and that for every `ε > 0` some allowable `s' ∈ StrongBundle.allowableSections N U`
     has `N(s(x) − s'(x)) ≤ ε` for all `x` (the difference taken in the fibre `(Y_{0,1})_x`,
     `StrongBundle.sectionOneVec`). The allowable sections satisfy it
     (`StrongBundle.isInAllowableCompletion_of_mem`). Proved: such an `s` vanishes off `U` and has
     `N(s) ≤ 1` (`IsInAllowableCompletion.isZeroAt_of_not_mem`, `.auxLe_one`), the hypotheses of
     `remark_5_12`; for a continuous section `f`, the solution set of `f + s` is closed
     (`IsInAllowableCompletion.isClosed_solutionSet_sectionAdd`); hence the remark as stated,
     `Polyfold.remark_5_12_completion` (`U ⊇ f⁻¹(0)` with `cl{x ∈ U | N(f(x)) ≤ 1}` compact) and
     `Polyfold.remark_5_12_of_isScFredholmSection` (`f` sc-Fredholm with compact solution set,
     `U` the neighbourhood of Theorem 5.5). The closedness is a chart argument. Near a limit
     point `x` of `S_{f+s}`, in a strong bundle chart `Φ` of the atlas, Lemma 5.2's bound
     `|Φ[1](w)₂|₁ ≤ A·N(w)` turns `ρ(s, s') ≤ ε` into `|Φ(s(y))₂ − Φ(s'(y))₂|₀ ≤ ‖ι‖Aε` near `x`.
     The map `y ↦ Φ(f(y))₂ + Φ(s'(y))₂` is continuous (`s'` is sc⁺) and is `≤ ‖ι‖Aε` at the zeros
     of `f + s` near `x`, hence at `x`; so `|Φ(f(x))₂ + Φ(s(x))₂|₀ ≤ 2‖ι‖Aε` for every `ε`, and
     `f(x) + s(x) = 0`. Only the continuity of `f` is used. This is the round-trip auditor's proof
     (item V5.22, `RoundTrip/Items/V5_22.lean`, `isClosed_solSet`) moved into the project; the
     docstrings of `remark_5_12` and of `Compactness.lean` now point to it.
131. **Choices, and what is not done.** (a) "The completion" is read through its representation
     by sections (uniform `N`-limits of allowable sections). That every `ρ`-Cauchy sequence of
     allowable sections has such a limit (by the completeness of the fibres, Definition 5.1 (1))
     is not formalized, and neither is the metric space `(Γ^{+,1}_U(P), ρ)` itself (item 89).
     (b) `remark_5_12` keeps its statement (any section vanishing off `U` with `N(s) ≤ 1`, compact
     closure): Theorems 5.13, 5.18, 5.19 use it in that form for sc⁺-sections, whose solution sets
     are closed by `isClosed_solutionSet` (item 69). The new theorems are corollaries, so the
     change is local to the new file. (c) The proof shows in effect that near each point the
     principal part of `s` in a chart is a uniform limit in `F₀` of continuous maps; the
     continuity of `s` is not stated as a separate lemma.

**140–149: Corollary 5.8 on the shifted strong bundle (2026-11-02).** (`Chapter5/StrongBundleShift.lean`,
`Chapter5/Corollary58.lean`; round-trip item V5.14, HANDOFF item 9; revises items 21, 22.)

140. **The shifted strong bundle `P¹ : Y¹ → X¹` is constructed (revises item 21).** The text uses
     `P^i : Y^i → X^i` in Corollary 5.8 without defining it. `Polyfold.StrongBundle.shift` is a
     strong bundle over the M-polyfold `X¹` (`MPolyfold.shift`) in the sense of Definition 2.51:
     total space `StrongBundle.ShiftSpace` = `Y_{1,1}` = the level `Y[0]_1` of the M-polyfold `Y[0]`
     with its level topology (Hausdorff and paracompact by Theorem 2.16 for `Y[0]`), projection
     `StrongBundle.shiftProj` (`P¹ = P|_{Y_{1,1}}`, continuous and surjective), fibres
     `P⁻¹(x) ∩ Y_{1,1}` (`shiftFiberSubmodule`, a linear subspace: in a chart it is the preimage of
     `F₁` under the linear fibre map), and the atlas of the **index raises of the strong bundle
     charts** `StrongBundleChart.shift`: base chart the level chart `φ¹ : V₁ → O₁`, fibre model `F¹`,
     retraction `R¹ = strongShift R` on `U¹ ◁ F¹` (`IsStrongBundleRetraction.shift`, with
     `R¹(U¹ ◁ F¹) = K_{1,1}` and `r¹(U¹) = O¹`), bundle chart the level chart of `Φ` in `Y[0]`.
     `StrongBundleChart.Compatible.shift`: compatible charts have compatible index raises — on `[0]`
     by `levelChart_compatible`, on `[1]` because `(Φ'¹ ∘ (Φ¹)⁻¹)[1]` is the level-`1` map of
     `(Φ' ∘ Φ⁻¹)[1]` (Proposition 1.17 for retracts), and the `F₁`-condition of Definition 2.50
     because `[1]` of the transition is sc⁰ (it maps `E₁ ⊕ F₂` into `E'₁ ⊕ F'₂`). The Banachable
     fibres come from a general fact proved here, `StrongBundleChart.isBanachable_fiber`: through a
     chart, `P⁻¹(x) ≅ K_{φ(x)} = {h | Γ(φ(x), h) = h}`, a closed subspace of `F₀`
     (`StrongBundleChart.fiberCLE`). Checks: `StrongBundle.mem_shift_doubleLevel_iff`
     (`(Y¹)_{m,k} = Y_{m+1,k+1}`), `StrongBundle.isChart_shift_toMPolyfold0_iff` (the M-polyfold
     `Y¹[0]` is `Y[0]¹`), `StrongBundle.isChart_shift` (the index raise of every chart of `P` is a
     chart of `P¹`).
141. **The reading of `Y^1`.** `Y¹ = Y_{1,1}` with `(Y¹)_{m,k} = Y_{m+1,k+1}`, the convention of
     `E¹` and of `(U ◁ F)¹ = U¹ ◁ F¹`; not `Y_{0,1} = Y[1]` and not `Y_{1,2}`. It is forced by
     "`f^i` is the section obtained by raising the index": an sc-smooth section maps `X₁` into
     `Y_{1,1}` (and in general not into `Y_{1,2}`), so `f¹ = f|_{X₁}` is a section of `Y_{1,1} → X₁`.
     The fibre `P¹⁻¹(x)` carries the topology of `F₁` (from `Y¹`), not the subspace topology of
     `P⁻¹(x)`.
142. **Raising the index of sc-smooth maps, and the levels of `X¹` (part of gap G.6).**
     `MPolyfold.IsScSmoothMap.levelOne`: an sc-smooth map `f : X → Z` between M-polyfolds induces an
     sc-smooth `f₁ : X¹ → Z¹` (continuity and the chart condition from the level-`1` maps of the
     local representatives, Proposition 1.17 for retracts). `MPolyfold.mem_shift_levelSet_iff`,
     `mem_shift_smoothSet_iff`: `(X¹)_m = X_{m+1}`, `(X¹)_∞ = X_∞` as sets (the topologies of
     `(X¹)_m` and `X_{m+1}` are not compared).
143. **Corollary 5.8 for `i = 1` is proved: `f¹` is an sc-Fredholm section of `P¹ : Y¹ → X¹` with
     compact solution set (revises items 21, 22; gap G.41).** `Polyfold.corollary_5_8`: for an
     sc-Fredholm `f` (Definition 3.14, the text's germ reading of Definition 3.11) with compact
     solution set, `B.shift.IsScFredholmSection (B.sectionShift f)` and the solution set of `f¹` is
     compact in `X¹`; `Polyfold.corollary_5_8_isScFredholmSection` (no compactness hypothesis) is the
     sc-Fredholm part. The parts: `f¹` sc-smooth (`StrongBundle.IsScSmoothSection.shift`),
     regularizing (`regularizing_sectionShift`, from `(X¹)_m = X_{m+1}` and
     `(Y¹)_{m,m+1} = Y_{m+1,m+2}`), and an sc-Fredholm germ at every smooth point of `X¹`
     (`Polyfold.isScFredholmGerm_sectionShift`): from a datum `(g, s)` of `f` in a chart `Φ`
     centred at the point, the datum `(g¹, s¹)` in the index raise `Φ¹` — the principal part of `f¹`
     is the level-`1` map of that of `f` (`principal_sectionShift`), `g¹` is a filling germ
     (`StrongBundleChart.shift_isFillingGerm`: conditions (1), (2) by `shift_filling_eq_on`,
     `shift_filling_mem_of_fixed`; the rest is item 144), `s¹` is an sc⁺-germ on the shifted germ,
     and `g¹ − s¹ = (g − s)₁` near `0` is conjugated to a basic germ by the index raise of the
     conjugation (`IsConjugateToBasicGerm.shift_germ`). No hypothesis beyond the text's is added;
     tameness is not used. `Polyfold.corollary_5_8_data` keeps the unpacked data in the shifted chart.
144. **Condition (3) of the filling on level `1` (the content of "it is a priori clear"): proved
     (revises item 22, which gave the argument on paper).** `IsFillingGerm.mem_range_toBase_of_fillDefect`:
     for every datum `(g, s)` of Definition 3.11 (filling germ `g` of `f̂` on `G ⊆ U` with fill
     defect `k = [1 − ρ(r)]g` and derivative family `Dk`, `s` an sc⁺-germ with `s(0) = g(0)`, `g − s`
     conjugated to a basic germ), `v ∈ ker Dr(0)` and `Dk(0)v ∈ F_m` imply `v ∈ E_m`, for every
     `m` — at the centre of the datum, not only at a zero. Proof (no global sc⁺-section, no bump
     function): `g(0) = ι s(0)` is a smooth point of `F` (`IsScSmoothGerm.toBase_zero_mem_smooth`);
     `ŝ(z) = Γ(z, −g(0))` is sc-smooth on `U` (`isScSmooth_const_of_smooth`) and a section of
     `K → O`, so by Lemma 3.17 (`IsFillingGerm.add_section`) `g' = g + ŝ ∘ r` fills `f̂ + ŝ` with the
     **same** fill defect, and `g'(0) = g(0) − Γ(0, g(0)) = 0`; with the sc⁺-germ
     `s' = s + Γ¹(r(·), −s(0))`, `g' − s' = g − s` on `U`, so Proposition 3.52 in sc form
     (`proposition_3_52_local_sc`, with Proposition 1.10) makes `Dg'(0)` sc-Fredholm;
     `Dk(0) = (1 − ρ(0))Dg'(0)` (`fillDefect_deriv_zero_eq_rho`), and the case of a zero (Chapter 3
     item 237, `IsFillingGerm.mem_range_toBase_of_scDeriv_r_eq_zero`) applies. On level `1`:
     `IsFillingGerm.germ_shift` — the fill defect of `g¹` is the level-`1` map of `k` (an sc¹-germ
     with family `(Dk)₁`, `IsSc1GermWith.shift`), `ι Dr¹(0) = Dr(0)ι` (`toBase_scDeriv_r_shift`,
     uniqueness of the derivative of `r¹ = r₁` on the shifted germ), `ι ρ¹(0) = ρ(0)ι`
     (`toBase_ρCLM_shift`), and `Dk¹(0) = Dk(0)|_{E₁}` is a bijection `ker Dr¹(0) → ker ρ¹(0)`
     (injective by condition (3) on level `0`, onto by the regularity above with `m = 1`), a
     topological isomorphism by the open mapping theorem (`ContinuousLinearEquiv.ofBijective`).
     The "constant section" form `R(y, f̂(0))` of item 22 (a), with `r` inserted so that the fill
     defect does not change, is what is used; the variant `t = ρ(r)s` mentioned on paper earlier is
     not needed.
145. **Tameness is not shifted.** The text assumes `X` tame; nothing proved here uses it. The tame
     variants (`IsScFredholmSectionTame` for `f¹`) are not stated: `ScRetraction.IsTame` quantifies
     over all presentations of the partial quadrant `C¹ ⊆ E¹`, which are not all index raises of
     presentations of `C`; the tameness of `r¹` needs the presentation independence of the
     degeneracy index and of `E_x` for `C¹` and that `A ∩ E₁` is an sc-complement of `T_xO¹` when
     `A` is one of `T_xO` (the sc-splitting shifts). Not done; no counterexample either.
     (2026-11-07) Chapter 7 settles this only for M-polyfold tameness: `MPolyfold.IsTame.levelOne`
     (`Polyfold/Chapter7/Lift.lean`) proves that the index lift `X¹` of a tame M-polyfold is tame,
     through a step showing that `r¹` is tame with respect to every presentation of `C¹` (the
     degeneracy index, `E_x ∩ E₁` and the sc-complement `A ∩ E₁`, then
     `ScRetraction.IsTameWith.isTame`), while the tame variants for `f¹` (`IsScFredholmSectionTame`
     for the shifted section) remain not stated (Chapter 7, items 81, 115).
146. **`i ≥ 2` by iteration.** `StrongBundle.shift` applies to `P¹` itself, and Corollary 5.8 for
     `i = 1` applies to the sc-Fredholm `f¹` with its compact solution set:
     `Polyfold.corollary_5_8_two` (`f² = (f¹)¹` is an sc-Fredholm section of `P² = (P¹)¹` with
     compact solution set). Every fixed `i` is obtained in the same way; a uniform family `P^i`
     indexed by `i` (a dependent type of strong bundles) and the identification of `(X¹)¹` with
     `X²` as topological spaces (the sets agree by `mem_shift_levelSet_iff`) are not formalized.

**150–159: the allowable sections are not complete (2026-11-02).** (`Chapter5/AllowableSectionsMetric.lean`;
comparison item V5.21, gap G.42; revises items 47, 89, 131 (a).)

150. **`(Γ^{+,1}_U(P), ρ)` is a metric space.** `StrongBundle.allowableDist B N U s s'` is
     `ρ(s, s') = sup_x N(s(x) − s'(x))`, the supremum of the existing pointwise distance
     `StrongBundle.sectionDistAt`. For an auxiliary norm `N`: the supremum is finite,
     `ρ ≤ 2` (`allowableDist_le_two`, from `N(s(x) − s'(x)) ≤ N(s(x)) + N(s'(x))` and
     `N(s(x)) ≤ 1`); `ρ(s, s) = 0`, symmetry and the triangle inequality come from the fibre
     norms (Definition 5.1 (1): `N(−v) = N(v)`, subadditivity), and `ρ(s, s') = 0 ⇒ s = s'` from
     "`N` vanishes only at `0_x`" (`allowableDist_self`, `allowableDist_comm`,
     `allowableDist_triangle`, `eq_of_allowableDist_eq_zero`). `StrongBundle.allowableMetric U hN`
     is the `MetricSpace` structure; `StrongBundle.AllowableSpace U hN` is `Γ^{+,1}_U(P)` as a type
     carrying it (a type synonym: `X → Y` carries the product topology). The project's density
     statements (`N(s(x) − s'(x)) ≤ ε` for all `x`, items 60, 89) are `ρ(s, s') ≤ ε`
     (`allowableDist_le_iff`). The round-trip proof of the metric axioms (item 47,
     `RoundTrip/Items/V5_21.lean`) is now in the project in this form. Only the continuity-free
     axioms of `N` are used (Definition 5.1 (1)); (2) and the continuity of `N` are not needed.
151. **"Not complete" is proved for the trivial bundle `ℝ × ℝ → ℝ`.** With
     `TrivialBundle.bundle 1 1` (the bundle of `Chapter3/NonVacuity.lean`), the fibre norm
     `N(x, v) = |v|` (`TrivialBundle.fibNorm`, an auxiliary norm: `isAuxNorm_fibNorm`, including
     the condition on `Y[1]`'s generated topology) and `U = ℝ`:
     `TrivialBundle.not_completeSpace_allowableSections`. The sections
     `s_j(x) = (x, √(x² + 1/(j+1)²)/(2√(1 + x²)))` are allowable (graphs of `C^∞` maps are sc⁺,
     `isScPlusSection_graphSection`; `N ≤ 1/2`) and `ρ(s_i, s_j) ≤ (ε_i + ε_j)/2`; a `ρ`-limit `s`
     would have fibre part `|x|/(2√(1 + x²))` (pointwise limits), which is not differentiable at
     `0`, but the fibre part of any sc⁺-section of the trivial bundle is `C¹`
     (`differentiable_snd_of_isScPlusSection`, from Proposition 1.18 in the chart `Φ = id`).
152. **The text's "not complete" is false without a hypothesis.** `(Γ^{+,1}_U(P), ρ)` is complete
     when `U = ∅` (it is `{0}`: `StrongBundle.completeSpace_allowableSections_empty`, any bundle,
     any auxiliary norm) and over a point with finite-dimensional fibre
     (`TrivialBundle.completeSpace_allowableSections_point`: `X = ℝ⁰`, fibre `ℝᵏ`, any `U`;
     `Γ^{+,1}_U(P)` is the closed unit ball of `ℝᵏ`, or `{0}` if `U = ∅`). In the text's setting
     (`U` a neighbourhood of the solution set of an sc-Fredholm section, in an M-polyfold that
     admits sc-smooth bump functions) one expects non-completeness as soon as `U` contains a
     non-isolated point over which `Y_{0,1}` is nonzero, by the same mechanism (bump functions
     times a non-smooth uniform limit); this general statement is **not formalized**. Suggested
     reading: "not complete in general".
153. **Not done.** The general sufficient condition of item 152; the identification of the
     metric completion of `(Γ^{+,1}_U(P), ρ)` with the section representation used in Remark 5.12
     (item 131 (a): that every `ρ`-Cauchy sequence has a uniform `N`-limit section is still not
     formalized).

**160–169: weak versus pointwise bump functions (2026-11-02).** (`Chapter5/BumpWeakPointwise.lean`;
comparison items V5.16, V5.17, V5.51; sharpens item 41.)

160. **Bump points.** `MPolyfold.HasBumpAt PX x`: for every open `U ∋ x` there is an sc-smooth
     `f : X → ℝ` with `f(x) ≠ 0` and `supp(f) ⊆ U`. The pointwise reading of Definition 5.9
     (`AdmitsBumpFunctions`, item 41) is "every point is a bump point"
     (`admitsBumpFunctions_iff_forall_hasBumpAt`, `Iff.rfl`); the weak reading (Definition 5.29 as
     written, `AdmitsBumpFunctionsWeak`) follows from "the bump points are dense"
     (`admitsBumpFunctionsWeak_of_dense`: a bump at a bump point `y ∈ U` is not identically zero
     and has support in `U`). The converse — weak ⟹ the bump points are dense — holds by a
     nested-neighbourhoods argument: in a chart `φ`, open sets `V₀ ⊇ cl V₁ ⊇ V₁ ⊇ …` inside `U`
     with `f_n` supported in `V_n` and non-zero on `V_{n+1}`, `diam φ(V_n) → 0`, and Cantor's
     theorem in `E₀` (a retract is closed near its points, `closure_inter_ball_subset`) gives a
     point of `⋂ V_n`, which is a bump point; **not formalized**. So the two readings are:
     pointwise = every point is a bump point, weak = the bump points are dense. The set of bump
     points is invariant under sc-diffeomorphisms of `X`.
161. **On an sc-Banach space the weak reading gives all smooth points**
     (`MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth`,
     `…exists_bump_of_mem_smooth`), for `E` as the M-polyfold `scPolyfold E` with the identity
     chart `scChart E` (model `(E, E, E)`; `isScSmoothMap_scPolyfold_iff`: the sc-smooth functions
     of the M-polyfold `E` are the sc-smooth maps `E → ℝ` on `univ`). Given `x ∈ E_∞` and
     `B(x, ε) ⊆ U`: a bump `f ≢ 0` with support in `B(x, ε/2)` is non-zero on a non-empty open set,
     which contains a smooth point `y` (`E_∞` is dense); `a = y − x` is smooth, so `v ↦ f(v + a)`
     is sc-smooth (`isScSmooth_add_const`, `Chapter4/Recentre.lean`), non-zero at `x`, with support
     in `B(x, ε/2) − a ⊆ B(x, ε) ⊆ U`. Point (b) of item 41 by machine: translation by `a ∉ E_m`
     is not even sc⁰ (`not_isSc0_add_const`, `not_isScSmooth_add_const`: it sends `0 ∈ E_m`
     outside `E_m`), so the argument stops at `E_∞`. For charts whose models are open subsets of
     `E` without boundary the same argument works locally; for a general retract `O` there is no
     translation, and nothing beyond item 160 is proved.
162. **Hilbert models: both readings hold at every point** (already in the project:
     `MPolyfold.admitsBumpFunctions_of_hilbert`, Proposition 5.35 in the charts and Theorem 5.34;
     the weak form by `AdmitsBumpFunctions.weak`). The bump `v ↦ τ(1 − b(v − x, v − x)/ρ)` is `C^∞`
     on `E₀`, hence sc-smooth, at every `x`, smooth or not. For M-polyfolds built on sc-Hilbert
     spaces the question of item 41 does not arise — the text's own remark before Definition 5.9.
163. **The open question, precisely.** Is there an sc-Banach space `E` (or an M-polyfold `X`) and
     a point `x ∉ E_∞` (necessarily non-smooth, by item 161) such that every sc-smooth
     `f : E → ℝ` with support in some neighbourhood of `x` vanishes at `x`, while the bump points
     are dense (for instance all of `E_∞`)? Equivalently: can the set of bump points be dense
     without being everything? What is known: an sc-smooth `f` is `C^k` on `E_{m+k}` but only
     continuous on `E₀`; for `X = E` the bump points form an `E_∞`-translation-invariant set, so
     they contain `E_∞` as soon as they meet it (item 161); a candidate must have `E₀` without
     `C¹` bump functions (otherwise `β(‖v − x‖²)`-type bumps exist at every point, item 162 and
     `LocalModel.hasBumpProperty_of_quadratic`), e.g. an `ℓ¹`-type scale, but the required `f` is
     only `C¹` on `E_1` on the `E_1`-unbounded set `E_1 ∩ B_0(x, ε)`, so the classical obstructions
     to `C¹` bumps do not apply directly. Neither a counterexample nor a proof is known here. The
     formalization keeps the pointwise reading as the hypothesis of Propositions 5.10/5.30, Lemma
     5.11 and Theorem 5.34 (item 41), now knowing that it is automatic at the smooth points of a
     linear model and everywhere on Hilbert models.
164. **Bookkeeping.** New file `Chapter5/BumpWeakPointwise.lean` (imports `BumpFunctions`,
     `Chapter4/Recentre`), registered after `AllowableSectionsMetric` in `Polyfold.lean`, with a
     `Test.lean` section; every `#print axioms` is standard. Comparison: V5.16 keeps "restated",
     with the chips "weak ⇐ bump points dense" and "weak ⇒ pointwise at smooth points (sc-Banach
     space)", and the diff "Whether the weak reading suffices is open at non-smooth points: on an
     sc-Banach space the weak reading gives a bump at every smooth point
     (`AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth`), on Hilbert models both readings hold
     everywhere (`admitsBumpFunctions_of_hilbert`), and the weak reading is the density of the bump
     points (`HasBumpAt`; one direction formalized) (Findings, Chapter 5, items 160–163)". V5.17
     and V5.51 unchanged. No gap entry changes.

## Chapter 6 (Linearizations, orientations and invariants; Lean `Polyfold/Chapter6/`)

*Numbering.* The items of this section are numbered in blocks, one block per phase of the work, so
that agents working at the same time do not collide; the gaps in the numbering are unused numbers,
not deleted items. 1–19: §§6.2–6.3 and Appendix 6.7, determinant lines, exact sequences, good
left-projections and stabilization (Definitions 6.3, 6.7–6.9, 6.16, Propositions 6.4, 6.6, 6.12,
6.15, Lemmas 6.5, 6.10, 6.11, 6.14, Corollary 6.13; `Chapter6/DetLine.lean` to
`Chapter6/DirectSumDet.lean`); 20–39: §6.4 and Proposition 6.26, the determinant bundle
(`LocalDetBundle`, `DetBundle`, `LineBundleOrientation`); 40–69: Definition 6.1 and §6.5 from
Definition 6.27 to Definition 6.36, the local propagation (`LinSet` to `ContinuousOrientation`);
70–89: Theorem 6.37 and Definitions 6.38–6.40 (`ChartTransfer` to `OrientationFunctor`); 90–99:
Theorem 6.41 and Remark 6.42 (`SolutionOrientation`, `ProductOrientation`); 100–109: not
formalized (Theorem 6.43, §6.6). Proposition 6.2 is Chapter 3's (comparison item V3.98; Chapter 3,
items 340–369). Statement numbers and pages are the preprint's *(book 2017: see
`BookConcordance.md`)*.

Found while formalizing §§6.2–6.3 and Appendix 6.7 (2026-11-06).

1. **Lemma 6.5 is read as "(91) holds for every choice", and the step "if and only if
   `det(τ) = det(ε)`" of §6.7.1 as homogeneity** *(book 2017: Lemma 6.1, p. 187; §6.7.1, pp.
   218–219)* *(book 2021: unchanged, Lemma 6.3.3, p. 244; Appendix 6.8.1, pp. 280–281, the same wording)*. "The definition of `Φ_E` does not depend on the choices" is formalized as: the
   linear map `FourTermExact.phi`, defined by (91) for one choice (`canonicalChoice`), satisfies
   (91) for every choice (`lemma_6_5`). This is the form every later computation uses: each
   evaluation of `γ^P_T` in §6.3 and §6.7.2 makes its own choices. The proof follows §6.7.1
   (`Choice.exists_smul_source_value`). In §6.7.1 the bases of `A` are changed by a map named `σ`
   and the factor is then written `det(τ)` (possible misprint, `τ` for `σ`); "the vector … is
   independent of the choices of the basis if and only if `det(τ) = det(ε)`" states a condition
   where what is needed is that both sides of (91) scale by the same factor `det(σ)/det(ε)`, and
   the proof goes through with that. In the last step the corrections are chosen in "`β(C)`",
   which is read as `β(B)` (possible misprint), and they are combinations of the `β`-images, not
   of the `γ`-preimages: the names of the two blocks of the wedge in `C` are exchanged there with
   respect to the first part of the proof (possible misprint). The 2017 text has the same wording.
2. **Proposition 6.6 exchanges the names of the two blocks of the wedge in `C`** *(book 2017:
   Proposition 6.3, p. 188)* *(book 2021: unchanged, Proposition 6.3.5, p. 246)*. The statement writes the basis of `C` with the `β`-images first and
   the `γ`-preimages second, under the names that (91) gives the other way round; the order meant
   is (91)'s, `γ`-preimages first (possible misprint). `proposition_6_6` is stated in the order of
   (91). The 2017 text has the same wording.
3. **`Π_T` is not empty, which the text uses without stating it** *(book 2017: Definition 6.5, p.
   189)* *(book 2021: unchanged, Definition 6.4.3, p. 247)*. From Lemma 6.11 on, constructions start with "`P ∈ Π_T`". For `T` Fredholm the
   projection onto `R(T)` along a finite-dimensional complement is good
   (`exists_isGoodLeftProj`). The remarks after Definition 6.9 (`P` Fredholm of index `0`, `P T`
   Fredholm of index `ind T`, `R(P) ∩ R(P')` of finite codimension) are formalized as stated
   (`IsGoodLeftProj.isFredholm`, `IsGoodLeftProj.fredholmIndex_comp`,
   `IsGoodLeftProj.finiteDimensional_quotient_inf`).
4. **Lemma 6.10: the projection of the text's proof is not below `P` and `P'` as we read it; the
   lemma holds by another construction, without `T` Fredholm; the 2017 remark that a common lower
   bound need not exist does not hold as we read it** *(book 2017: dropped; the remark on p. 190
   before Remark 6.3, and the new Lemmas 6.3–6.5, Definition 6.6, Proposition 6.6)* *(book 2021: unchanged, the remark before Remark 6.4.6, p. 248; Lemma 6.10 absent, as in 2017)*. The text's
   `P''` projects onto `R(P) ∩ R(P')` along a complement `Z ⊕ X ⊕ X'`, and `P'' = P''P` needs
   `ker P ⊆ ker P''`. On `ℝ²` with `T = 1`, `P` the projection onto the `x`-axis along the
   `y`-axis and `P'` the one along the diagonal, `R(P) ∩ R(P')` is the `x`-axis and a projection
   onto it below both would equal both (`lemma_6_10_text_reading`). The lemma holds with a
   smaller range: for `K = ker P + ker P'` (finite-dimensional), a closed finite-codimensional `N`
   with `N ∩ K = 0` (Hahn–Banach), `R'' = R(P) ∩ R(P') ∩ N` and a closed complement `C ⊇ K` of
   `R''`, the projection onto `R''` along `C` lies in `Π_T` and below `P` and `P'`; `T` need not
   be Fredholm (`lemma_6_10`). The 2017 version replaces the lemma by the remark that for `P, Q ∈
   Π_T` there need not be `L ∈ Π_T` with `L ≤ P`, `L ≤ Q`, and rebuilds §§6.3–6.4 around the
   projections `P_H` onto a fixed range; with the order `P ≤ Q` iff `P = PQ = QP` of both versions
   such an `L` always exists, as we read it. The preprint's route to Lemma 6.25 (a common lower
   bound, Corollary 6.13, Lemma 6.21) is therefore sound and is the one formalized.
5. **`γ^P_T` is read with the identification `F/R(P) = F/R(PT)`** *(book 2017: Proposition 6.4,
   p. 192)*. `Φ_{E(T,P)}` takes values in `λ(ker PT) ⊗ λ*(F/R(P))`; "recalling `R(P) = R(PT)`" is
   read as the identification of `λ*(F/R(P))` with `λ*(F/R(PT))` by the identity of `F`
   (`gammaProj`). In Proposition 6.12 and Corollary 6.13 the operators `P(QT)` and `PT` are equal
   but their kernels are different types, so the statements carry the identification
   `det(P(QT)) = det(PT)` (`linDetEquivOfEq`); this is bookkeeping, not a change of content.
6. **Proposition 6.12: the spanning step of §6.7.2 is proved directly in `F`** *(book 2017:
   Proposition 6.5, p. 193; §6.7.2, pp. 219–221)*. The step "the classes of `d₁, …, d_l, T b₁, …`
   span `ker Q̃`" is proved as: if `Q g = 0`, then `g` is a combination of the `dᵢ` plus `T x`
   with `x ∈ ker(QT)` (`mem_span_append_of_ker`); the classes `[T b̃]` and `[Q T b̃]` in `F/R(P)`
   then differ by elements of the span of `[d]`, `[T b]`, which does not change the wedge
   (`wedge_append_add_right`).
7. **§6.7.2 names the final wedge `α_q`, read as `α^P`** *(book 2017: §6.7.2, the same name)* *(book 2021: corrected, Appendix 6.8.2, p. 283, names the wedge `α^P` throughout)*.
   The wedge introduced as `α^P` is called `α_q` a few lines later (possible misprint).
8. **Lemma 6.14: "`j(e) = (0, e)`" in the proof is read as `(e, 0)`** *(book 2017: Lemma 6.6,
   p. 199, the same wording)* *(book 2021: corrected to `j(e) = (e, 0)`, proof of Lemma 6.4.14, p. 256)*. The sequence defines `j(e) = (e, 0)`; the proof's
   `j(e) = (0, e) = (e, r)` is read with `(e, 0)` (possible misprint). "`[φ(r)] = R(T)`" means
   that the class of `φ(r)` in `F/R(T)` is zero.
9. **Proposition 6.15: two facts the text notices are proved, and the isomorphism of (94) is called
   `φ`** *(book 2017: Proposition 6.7, p. 199)* *(book 2021: corrected, Proposition 6.4.15, p. 257, names the isomorphism `σ`, no longer `φ`)*. That the `rᵢ = π(b̄ᵢ)` and the `c̄ⱼ` together
   form a basis of `ℝⁿ` follows from the exactness at `ℝⁿ` (`isCompl_range_stabPi_span`), and
   the identity `m + l = n`, needed to form `det(c̄, r)`, is a hypothesis of `proposition_6_15`
   that always holds (`stab_card_eq`). The statement opens with "the chosen isomorphism
   `φ : λ*(ℝⁿ) → λ*({0})`", which is the `ψ` of (94); `φ` is already the stabilizing map
   (possible misprint; the same in 2017).
10. **Not formalized in §§6.2–6.3** *(book 2017: Definition 6.3, p. 189; after Proposition 6.7,
    p. 200)*. The alternative determinant `λ(ker T) ⊗ λ(coker(T)*)` mentioned after Definition 6.7
    and its identification with Definition 6.7 (gap G.57), and the identification (95) with the
    maps `V ⊗ λ(ℝⁿ) → V`, `V ⊗ λ*(ℝⁿ) → V` after Proposition 6.15 (gap G.58). Neither is used by
    the formalized statements of the chapter, which use (94) only.
11. **Definition 6.16 is a definition by a formula in bases; "natural" is read as the formula for
    every choice** *(book 2017: Definition 6.7, p. 200)*. `directSumDet` is defined by the formula
    for one choice of bases, and `definition_6_16` shows that it satisfies the formula for every
    choice (`directSumVec_eq_smul`), as for Lemma 6.5.

Found while formalizing §6.4 and Proposition 6.26 (2026-11-06).

20. **Lemma 6.17 does not use that `T` is Fredholm** *(book 2017: Lemma 6.7, p. 201)*. For a
    bounded `T`, `P ∈ Π_T` and a topological complement `Y` of `ker(PT)` (an algebraic complement
    with a continuous projection, `Submodule.IsTopCompl`), `P ∈ Π_S` and `PS|_Y` is an isomorphism
    onto `R(P)` for `S` near `T` (`lemma_6_17`); the Fredholm hypothesis is not needed.
21. **Lemma 6.18 is stated concretely** *(book 2017: Lemma 6.8, p. 201)*. "Is a trivial vector
    bundle" is formalized as: `(S, k) ↦ (S, k + y(k, S))` is continuous, maps `ker(PT)` onto
    `ker(PS)`, and is inverted by the continuous projection onto `ker(PT)` along `Y`
    (`LocalDetChart.lemma_6_18`).
22. **Lemma 6.19 is used only for trivial bundles, and Proposition 6.20 is proved with explicit
    frames** *(book 2017: Lemma 6.9, Proposition 6.8, p. 202)*. Mathlib has no exterior powers or
    tensor products of vector bundles, and the general Lemma 6.19 is not formalized (gap G.59).
    The bundles it is applied to are trivial; `DET(T, P, ε)` is given the frame
    `ω(S) = (k₁(S) ∧ … ∧ kₙ(S)) ⊗ (e₁ ∧ … ∧ e_l)*` (`LocalDetChart.frame`), and "in a natural way"
    is read as: the frames of two charts with the same `P` differ by a continuous nowhere-zero
    factor (`proposition_6_20`).
23. **Lemma 6.21 is stated for two charts, and the text's sketch is the proof** *(book 2017:
    Lemma 6.10, p. 202)*. Lemma 6.25 compares charts with different centres and radii, so
    `lemma_6_21` is stated on the common ball of any two charts. The text's "this is trivial and
    follows from an inspection" is carried out by extending the kernel sections of `PS` to
    sections spanning `ker(QS)`, as the sketch says.
24. **`DET(E,F)` is built as a Mathlib vector prebundle** *(book 2017: Definition 6.8,
    Propositions 6.9, 6.10, Lemma 6.11, p. 204)*. The charts `γ_(T,P,ε)`, read in their frames, are
    the pretrivializations of `detPrebundle`; its topology and its `FiberBundle` and
    `VectorBundle` instances are Mathlib's. Definition 6.22 and Proposition 6.23 become: the
    collection `𝓑` is a basis of that topology (`detBasis`, `proposition_6_23`); Proposition 6.24
    and Lemma 6.25 are as stated (`proposition_6_24`, `lemma_6_25`).
25. **Proposition 6.26 cites contractibility without the theorem it needs** *(book 2017:
    Proposition 6.11, p. 205)* *(book 2021: unchanged, Proposition 6.6.1, p. 263)*. "Consequently has two possible orientations since the base space
    is contractible" needs that a line bundle over such a base is orientable. The proof formalized
    is the standard one: the rays of the fibres form a two-sheeted covering (`OrCover`,
    `isCoveringMap_orCover`), an orientation is a continuous section of it, and the lifting
    criterion applies over a simply connected, locally path-connected base
    (`exists_lineOrientation_apply_eq`, `exists_two_lineOrientation`); a nonempty convex set of
    Fredholm operators is such a base. `proposition_6_26` is stated for every nonempty convex set.
26. **Not formalized in §6.4** *(book 2017: p. 204, and §6.5, p. 205)*. The remark that `DET(E,F)`
    is not orientable, and the classical case with which §6.5 opens (the determinant line bundle
    of a classical Fredholm map over a contractible `U`), are not formalized (gap G.60).

Found while formalizing Definition 6.1 and §6.5, Definitions 6.27–6.36 (2026-11-07).

40. **Definition 6.1 is made in a chart point, with global sc⁺-sections, and "sc-Fredholm" is
    proved on level `0`** *(book 2017: Definition 6.1, p. 182)*. `T_xX` and `Y_x` carry no linear
    structure in the project (gaps G.6, G.7, G.13), so `Lin(f, x)` is made at a chart point
    `(c, z)`: operators `T_zO → K_z` (`ChartPoint.linSet`). The text's `f − s` with `s(x) = f(x)` is
    `f + s` with `(f + s)(x) = 0` (`sectionAdd`). The sections are global; one through `−f(x)`
    exists under `HasScPlusSectionsThrough` (`ChartPoint.linSet_nonempty`), which bump functions
    give (`MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`). The members are shown Fredholm
    on level `0` with the index `ind(f, x)` (`ChartPoint.exists_index_linSet`), which is what the
    determinant lines use; that they are sc-Fredholm on every level is not stated (gap G.64).
41. **The paragraph before Definition 6.1 compares `(f − s)'(x)` with itself** *(book 2017: corrected
    to `(f − t)'(x)`, before Definition 6.1, p. 182)* *(book 2021: corrected as in 2017, before Definition 6.2.1, p. 239)*. "`(f − s)'(x)` is a sc-Fredholm operator if and only if `(f − s)'(x)`
    is" is read with `(f − t)'(x)` in the second place (possible misprint).
42. **The facts on paths recalled on p. 201 are not formalized** *(book 2017: before Proposition
    6.1, p. 183)* *(book 2021: unchanged, before Proposition 6.2.2, p. 240; local path-connectedness is now proved, Theorem 2.2.4, p. 32, Proposition 2.3.7, p. 36)*. That an M-polyfold is locally path connected and that two smooth points in one
    path component are joined by an sc⁺-smooth path is formalized only locally, inside a chart
    (`exists_nhds_scPath`); "in the same path component" (Definitions 6.27, 6.38) is read as
    "joined by an sc-smooth path" (gap G.56).
43. **The partitions of unity assumed from §6.2 on are replaced by bump functions** *(book 2017:
    §6.2)*. §6.2 announces sc-smooth partitions of unity "to simplify the presentation"; the
    formalization assumes sc-smooth bump functions (`MPolyfold.AdmitsBumpFunctions`), which
    partitions of unity give (Chapter 5, comparison item V5.49), and uses them only for global
    sc⁺-sections. The paracompactness instances on `ℝⁿ × X` and on the pull-back bundles hold
    (`MPolyfold.paracompactSpace_prod`, `paracompactSpace_pullbackSpace`).
44. **Definition 6.27: the category `𝒪_f` is read as types and bijections** *(book 2017: Definition
    6.9, p. 205)*. `Or_x^f` is the type of orientations of `DET(f, x)` at a chart point
    (`ChartPoint.Or`), with exactly two elements (`ChartPoint.exists_two_or`); on the tensor
    products no negation is set up, so `{o_x, −o_x}` is stated as "exactly two". The morphisms are
    bijections; between two two-element types there are exactly two, each determined by one value
    (`nonempty_equiv_of_two`, `equiv_eq_of_apply_eq_of_two`).
45. **Proposition 6.28 (1) is not established for `U` as we read it; (1′) is proved instead**
    *(book 2017: Proposition 6.12, p. 205, with a `U′ ⊂ U` and (1) "`U′ ⊂ U` is sc-smoothly
    contractible in `U` to the point `x`", close to the reading (1′))* *(book 2021: unchanged from 2017, Proposition 6.6.3 (1) and its proof, pp. 263–264)*. The contraction `r̂(t, y) = r(ty)` contracts
    `O = r(V)` for a convex `V`; for `U = r(V')` it needs `r(V') ⊆ V'`, which is not stated, and a
    convex domain of the retraction is not available in general. What the proof of Theorem 6.35
    uses is (1′): two sc-smooth paths in `U` with the same end points are sc-smoothly homotopic,
    with the end points fixed, in a larger region `W` where (3) holds. `proposition_6_28` proves
    (1′) with `W = O ∩ B_δ`, `U = O ∩ B_δ'` and `r(B_δ') ⊆ B_δ`, by
    `Φ(τ, t) = r((1 − ρ(τ)) φ(γ₀(σ(t))) + ρ(τ) φ(γ₁(σ(t))))` in the chart, with `σ` the identity
    near `[0, 1]` and taking values where both paths lie in `U` (the paths lie in `U` only on
    `[0, 1]`; `exists_contDiff_eq_id_near_Icc_mapsTo`) (gap G.61).
46. **Proposition 6.28: the sections are global, (3) is stated for families, and the smoothness of
    `x` is not used** *(book 2017: Proposition 6.12, p. 205)*. The sections of (3) and (4) are
    global sc⁺-sections of `ℝⁿ × X → Y`, made with bump functions, in place of sections over
    `U × [0, 1]` after "assuming `X = U`"; (3) is stated for sc-smooth families `Φ : ℝⁿ → X`, as
    the homotopies of Theorem 6.35 need, and its section depends on `q ∈ [0, 1]ⁿ` only through
    `Φ(q)` (`exists_isScPlusSection_pullback_of_family`). The construction does not use that `x` is
    smooth, nor that `X` is tame.
47. **Lemma 6.29 has no proof in the text; the general position of `F` is proved, the slice form of
    (P) is not stated** *(book 2017: Lemma 6.12, p. 207)* *(book 2021: unchanged, Lemma 6.6.4, p. 265)*. The text's proof is the sentence "using
    the results from the transversality theory". `lemma_6_29` follows the proof of Theorem 5.18,
    under its hypotheses: `X` tame, bump functions, tame germ data. Its conclusion is the general
    position of `F` at the points `(t, φ(t), 0)`, which the text derives from (P) and which Lemmas
    6.30 and 6.31 use. (P) itself, the general position of each slice `F_t` on `X × ℝᵏ`, is not
    stated (gap G.63); as we read it, it follows, since the tangent vectors of the family of zeros
    lie in `ker F'` and `ℝⁿ` has no boundary, but this chart computation is not carried out.
48. **Lemma 6.30 is formalized as a continuous family of kernels** *(book 2017: Lemma 6.13, p.
    207)*. Near a zero in good position the kernel is the tangent space of the solution set
    (Theorem 3.54), the range of the derivative of an sc-retraction, so the kernels along a
    continuous family of zeros form a continuous family of subspaces of the model space
    (`exists_subspaceFamily_linKer`). The manifold statements (the solution set as a manifold with
    boundary with corners near `(t, φ(t), 0)`, the map `π`, `L` as a smooth bundle) are not
    formalized (gap G.62); the continuation of orientations does not need them.
49. **Lemma 6.31: `ker F_t'` is read as the kernel of `F'` cut by `σ = 0`, and `c` is onto by the
    general position of `F`** *(book 2017: Lemma 6.14, p. 209)*. In the product chart the
    linearization of the slice is `(v, λ) ↦ T v + φ λ`, and `ker F'(0, (q, z)) ∩ {σ = 0}` is the
    image of `ker(T ⊕ φ)` (`linKer_inf_ker_sliceProj_eq_map`). The text has `c` onto by (P); here
    `F'` is onto by `lemma_6_29`, and the `ℝⁿ`-directions are absorbed because the derivative of the
    curve of zeros lies in `ker F'` (`fderiv_mem_linKer`, `surjective_coprod_of_isLinSurjAt`).
    With this, (96) is the stabilization sequence of `T` and `φ` (`lemma_6_31`).
50. **Formula (94): `Φ_E` does not vary continuously where `dim coker T` changes parity, as we read
    it; the propagation uses `(−1)^{dim coker T} Φ_E`** *(book 2017: Proposition 6.7, p. 199, and
    §6.5)* *(book 2021: unchanged, Proposition 6.4.15, p. 257, and §6.6)*. In a local determinant chart with projection `P`, the coordinate of `ι_ψ(x)` in
    `det(S ⊕ ψ)` is `(−1)^{k · dim F/R(P) + dim coker S} D(S, ψ)` times that of `x`, with `D`
    continuous and nowhere zero (`coord_stabIota`); the first exponent is constant on a chart, the
    second is not. So along a norm-continuous family `T_q` with continuous stabilizations, the rays
    `Φ_E(o(T_q))` of `λ(ker(T_q ⊕ φ_q))` carried from a continuous orientation `o` need not form an
    orientation: `not_isLineOrientation_stabRay_uncorrected` is an instance with `E = F = ℝ`,
    `k = 1`, `T_q = q/(1 + |q|)`, `φ(r) = r₀`. Lemmas 6.33, 6.34 and the homotopy argument before
    Theorem 6.35 use that these orientations vary continuously with the parameter. With
    `α(T) = (−1)^{dim coker T}` (`stabSign`) the rays `α(T_q) Φ_E(o(T_q))` do form an orientation
    (`isLineOrientation_stabRay`), and the push-forward uses `α Φ_E` at both end points
    (`IsStabKernels.push`). On each operator `α(T) Φ_E` carries the text's orientation or its
    opposite; for given end-point operators the two push-forwards differ by `α(T_a) α(T_b)`.
51. **Lemma 6.33: the homotopy of the text's proof is not needed** *(book 2017: Lemma 6.15, p.
    209)*. "One verifies by a simple computation" is `detEquiv_stabIota_append`: with the appended
    sections last (`appendStab`), the stabilization isomorphism of `(φ, ψ)` is that of `φ` followed
    by `w ↦ (w, 0) ∧ ℓ₁ ∧ … ∧ ℓ_d`, exactly, with no sign. The comparison is made directly between
    `T ⊕ φ` and `T ⊕ (φ, ψ)`, at the end points by Proposition 6.15 and along the family by
    `isLineOrientation_wedgeExt` (`propagate_append`, `IsStabKernels.push_append`).
52. **Proposition 6.32: Lemmas 6.33 and 6.34 are combined over one square** *(book 2017:
    Proposition 6.13, Lemmas 6.15, 6.16, pp. 209–211)*. For two data along the same path,
    `S^τ = (1 − τ) S⁰ + τ S¹` with the sections `(1 − τ) ŝ⁰ⱼ + τ ŝ¹ⱼ` (`ŝⁱⱼ = sⁱⱼ` for `j < kⁱ`, `0`
    otherwise), followed by the sections of Lemma 6.29 on the square. At `τ = 0` the sections `s⁰`
    are the first `k⁰` of the family and at `τ = 1` the sections `s¹` are the first `k¹`, so Lemma
    6.33 applies on both edges without reordering (`IsStabKernels.push_eq_of_prefix`); along the
    edges `t = 0, 1` the operators are affine in `τ` (`linAt_principal_combo`), hence continuous.
53. **Theorem 6.35 does not introduce `f`; contractibility is replaced by (1′), and the proof needs a
    reparametrization** *(book 2017: unchanged as to `f`, Theorem 6.1, p. 212, which drops "sc-smoothly
    contractible")* *(book 2021: unchanged, Theorem 6.6.11, p. 272)*. The statement names the bundle and the
    point but not the section (possible omission); it is read for an sc-Fredholm section with tame
    germ data, under the standing hypotheses (`theorem_6_35`: `X` tame, bump functions). The
    homotopy of (1′) meets its edge conditions only for `t ∈ [0, 1]`, while a push-forward datum
    asks for zeros of `f + S` for `t` near `[0, 1]`; the proof passes through `γᵢ ∘ κ`, `κ` the
    smooth transition function, with three homotopies whose edges are exact for all `t`
    (`push_eq_of_homotopy`). The neighbourhood is not shown to be sc-smoothly contractible (gap
    G.61).
54. **Definition 6.36 is read over a pair `V ⊆ U`** *(book 2017: Definition 6.10, p. 212, "open path
    connected", without "contractible")*. Since
    Proposition 6.28 gives (1′), an orientable neighbourhood is `U` with the local propagation
    property and an open `V ∋ x` whose smooth points are joined by sc-smooth paths in `U`
    (`exists_nhds_scPath`); the continuous orientations live over `V_∞` and are preserved by the
    push-forwards along paths in `U` (`IsContinuousOrientation`). "An orientable neighborhood has
    precisely two continuous orientations" is `exists_two_isContinuousOrientation`.
55. **The composition of paths on p. 228 writes `ψ(β(s))` on `[1/2, 1]`, read as `ψ(β(s) − 1)`**
    *(book 2017: before Theorem 6.2, p. 213, the same wording)* *(book 2021: corrected to `ψ(β(s) − 1)`, before Theorem 6.6.13, p. 273)*. With `β([1/2, 1]) = [1, 2]`,
    `ψ(β(s))` leaves `[0, 1]`; the second piece is read as `ψ(β(s) − 1)` (possible misprint).
    `concatPath` is such a concatenation, with `β = κ(3s)` on `[0, 1/2]` and `κ(3s − 2) + 1` on
    `[1/2, 1]`.

Found while formalizing Theorem 6.37 and Definitions 6.38–6.40 (2026-11-07).

70. **`Or_x^f` is chart-free in the text; it is made in a chart point and identified between
    charts, and the local propagation is shown to be independent of the chart** *(book 2017: §6.5,
    p. 205, and Theorem 6.2, p. 213)*. The proof of Theorem 6.37 carries an orientation along
    orientable neighbourhoods of different points of a path, which may lie in different charts; the
    text takes `T_xX`, `Y_x`, `Lin(f, x)` and `Or_x^f` to be the same whichever chart is used. Here
    two chart points at `x` are related by the derivative `A` of the base transition and the fibre
    part `Γ` of the strong bundle transition (`ChartPoint.transferT`, `ChartPoint.transferK`, with
    the cocycle rules), `L ↦ Γ L A⁻¹` maps `Lin_p(f, x)` onto `Lin_{p'}(f, x)`
    (`ChartPoint.mem_linSet_transfer_iff`), and `ChartPoint.orTransfer` identifies the two sets
    `Or_x^f`. The push-forward then agrees in the two charts (`IsPush.transfer`,
    `HasLocalPropagation.push_compat`), by the naturality of the stabilization isomorphism
    (`stabRayEquiv_conjDet`) and of continuation (`SubspaceFamily.cont_map`). `Or_x^f` itself is
    read in a chosen chart (`Orx`, `toChartOr`).
71. **Homotopy classes: the edge conditions hold only on `[0, 1]`, so transitivity needs a
    reparametrization; the identities are the constant paths** *(book 2017: before Theorem 6.2,
    pp. 212–213)*. Paths are maps `ℝ → X` and homotopies maps `ℝ² → X` whose edge conditions are imposed
    for parameters in `[0, 1]` (decision D2). Two homotopies glued in `τ` need not agree off
    `[0, 1]`, so `ScHomotopic.trans` first reparametrizes all paths and homotopies by `κ` in `t`.
    The text does not name the identities of `PX`; they are the classes of the constant paths. The
    reversed paths give inverses, so `PX` is a groupoid (`PathCat.groupoid`).
72. **Theorem 6.37: the covering argument is a dyadic subdivision, (∗) is asked on every open set
    with the local propagation property, and uniqueness uses only composition and (∗)** *(book
    2017: Theorem 6.2, p. 213)*. The transport along a path is the composite of the push-forwards
    along its `2ᴺ` dyadic pieces for any `N` at which every piece lies in a good set (Lebesgue
    number lemma); homotopy invariance is the same on the square (`LocalTransport`,
    `transport_eq_of_isScHomotopyRel`). (∗) is formalized for every chart, every open `U` with the
    local propagation property in it and every push-forward along a path in `U`
    (`IsStarProperty`); the sc-smooth contractibility of `U` is not asked (gap G.61), and the
    uniqueness needs (∗) only on a family of such sets covering `X_∞`
    (`orFunctorMap_unique_of_cover`). "Uniquely determined functor" is read for the maps on
    morphisms (on objects there is no choice), and `𝒪_f` as types and bijections (`orFunctor`).
    The theorem uses the standing hypotheses of Theorem 6.35 and sc⁺-sections through every smooth
    fibre point (so that every `Or_x^f` has two elements), which bump functions give.
73. **Definitions 6.38 and 6.39 are called equivalent without proof; the equivalence is proved, with
    "the same path component" read as "joined by an sc-smooth path"** *(book 2017: Definitions
    6.11, 6.12, p. 213)* *(book 2021: unchanged, Definitions 6.6.14, 6.6.15, p. 274)*. For points not joined by an sc-smooth path there is nothing to check in
    Definition 6.38 (`IsOrientableSection`). Both definitions are shown equivalent to the existence
    of `y ↦ o_y` with `Γ_f([φ]) o_x = o_y` for all `[φ]` (`isOrientableSection_iff_exists`,
    `isOrientableSection'_iff_exists`), hence to each other (`isOrientableSection_iff`). From 6.39
    to 6.38 the transport along a path is computed on dyadic pieces inside orientable
    neighbourhoods (`LocalTransport.transport_apply_eq_of_local`); from 6.38 to 6.39 a base point is
    chosen in each class of points joined by sc-smooth paths.
74. **Definition 6.39 writes "`y ∈ U_∞`" before any `U` is introduced** *(book 2017: corrected
    to `y ∈ X_∞`, Definition 6.12, p. 213)* *(book 2021: corrected as in 2017, Definition 6.6.15, p. 274)*. It is read as `y ∈ X_∞` (possible misprint).
75. **Definition 6.40: orientations are the families preserved by `Γ_f`** *(book 2017: Definition
    6.13, p. 214)*. With the orientable neighbourhoods of item 54, an orientation of `f` is a map
    `y ↦ o_y` with `Γ_f([φ]) o_x = o_y` for all `[φ]` (`isSectionOrientation_iff`); `f` has one iff
    it is orientable (`exists_isSectionOrientation_iff`), two that agree at a point agree on the
    points joined to it by sc-smooth paths, and there are exactly two on each such class
    (`IsSectionOrientation.apply_eq_iff`, `IsSectionOrientation.exists_two`).

Found while formalizing Theorem 6.41 and Remark 6.42 (2026-11-07).

90. **Theorem 6.41: the first assertion comes from Chapters 4 and 5; "proper" is used only through
    the compactness of `S`** *(book 2017: Theorem 6.3, p. 214)*. "We already know from the
    transversality discussion" is `theorem_6_41_solutionSet`: for `X` tame and `f` with tame germ
    data in general position (Definition 5.17) at every zero, `S` is compact, a smooth submanifold
    in general position with the induced structure of a tame manifold with boundary with corners
    (the conclusions of Theorem 5.18), using Lemma 4.19 for good position
    (`MPolyfold.IsGeneralPositionAt.isGoodPositionAt`). Of "proper" (`StrongBundle.IsProper`)
    only the compactness of the solution set is used; for sc-Fredholm sections the two are
    equivalent (Chapter 5, comparison item V5.10), so nothing of the hypothesis is lost.
91. **"`T_xS` is oriented by `o_f(x)`" and "the local prolongation … is the Fredholm one" are read
    in a chart, along the paths of zeros** *(book 2017: Theorem 6.3, p. 214)*. At a zero, `f'(x)`
    (the linearization of `f + s` with `s = 0`) lies in `Lin(f, x)` and is onto, and
    `det f'(x) ≅ λ(ker f'(x))`, with `ker f'(x) = T_xS` in the chart
    (`tangentSpace_solutionSet_eq_linKer`); `ChartPoint.tangentOr` is the resulting orientation of
    `λ(T_xS)`. The second sentence is read as: along every sc-smooth path of zeros in an orientable
    neighbourhood, the kernels form a continuous family `Λ` (Lemma 6.30, `tangentFamily`) and the
    tangent orientations of an orientation of `f` form an orientation of `λ(Λ)`
    (`isLineOrientation_tangentOr`). The Fredholm side is the push-forward for the datum `S = 0`,
    `k = 0`, which along a path of zeros is continuation between tangent orientations
    (`isStabKernels_zero`, `IsStabKernels.orRay_eq_tangentOr`); intermediate points are reached by
    the paths `s ↦ γ(t κ(s))`, which stay in `γ([0, t])` for all `s ∈ ℝ`.
92. **Theorem 6.41: the orientation of `S` as a manifold and its chart independence are not
    formalized** *(book 2017: Theorem 6.3, p. 214)*. "A natural orientation" is formalized as the
    tangent orientations with their continuity along paths of zeros in a chart (`theorem_6_41`);
    an orientation of `S` as an abstract finite-dimensional manifold, of its tangent bundle in the
    charts of the induced structure (gap G.67), and the compatibility of the tangent orientations
    read in two charts at the same zero (gap G.68) are not formalized.
93. **The paragraph after Theorem 6.41 is not formalized** *(book 2017: after Theorem 6.3, p.
    214)*. For `f` not generic, a small sc⁺-perturbation `s` supported near the zero set, the
    orientation of `S_{f+s}` coming from `o_f`, and the identification of `det((f + s)'(x))` with a
    fibre of `DET(f, x)` (`Lin(f + s, x) = Lin(f, x)` for an sc⁺-section `s`) are not formalized
    (gap G.69).
95. **Remark 6.42: the map `h ↦ h̃` is not continuous in `L` where the parity of `dim coker L`
    changes, as we read it; the sign `(−1)^{dim coker L}` is used** *(book 2017: Remark 6.4, p.
    214)* *(book 2021: corrected, as we read it: Remark 6.6.19, p. 276, wedges `e` first, so `h ↦ h̃` is `w ↦ e ∧ w` in local charts and no parity sign arises)*. For `L̃ = L ⊕ 0 : E × ℝ → F`, `h ↦ h̃ = (a₁ ∧ … ∧ aₙ ∧ e) ⊗ (b₁ ∧ … ∧ b_l)*` is an
    isomorphism `det(L) ≅ det(L̃)` (`extDet`, `extDet_wedge_tmul`), and in local determinant charts
    its coordinate is `(−1)^{dim F/R(P) + dim coker L}` times a continuous nowhere-zero function
    (`coord_extDet`). Over the convex set `Lin(f, x)`, where `dim coker L` can change parity, the
    orientation of `DET(f̂, (x, t))` defined by `h̃` at one `L` could therefore differ from the one
    defined at another. With `extDetN = (−1)^{dim coker L} · extDet` (the sign `stabSign` of item 50)
    the coordinate is continuous up to a sign constant on a chart (`coord_extDetN`), continuous
    orientations pull back (`LineOrientation.extPull`), and an orientation `o` of `DET(f, x)` gives
    exactly one orientation `ô` of `DET(f̂, (t, x))` with `ô(L̂)` the image of `o(L)` for every
    `L ∈ Lin(f, x)` (`ChartPoint.existsUnique_prodOr`, `ChartPoint.prodOr`). The two maps agree when
    `L` is onto (`extDetN_eq_of_surjective`). This is the same kind of sign as formula (94), item 50.
96. **Remark 6.42: readings** *(book 2017: Remark 6.4, p. 214)*. `X × [0, 1]` is read as `ℝ¹ × X`
    (decision D2), with the parameter first; `s` is an sc⁺-section `S` of the pull-back `π*P`, and
    `f̂ = f̃ + S` with `f̃(t, x) = f(x)`. `Lin(f̂, (t, x))` is read in the product chart point
    `ChartPoint.prodPt`, where `T_{(t,z)} = ℝ¹ × T_zO` and the fibre is `K_z`; the text's
    `L̃(a, b) = La` puts the `ℝ`-factor second and is read as `L̂ = Γ⁻¹ (L ⊕ 0) A` with `A` the swap
    of the factors (`ChartPoint.prodLin`), and `L̂ ∈ Lin(f̂, (t, x))` for every `L ∈ Lin(f, x)`
    (`ChartPoint.prodLin_mem_linSet`, through the `t`-constant lift `constLift`). The remark needs
    only an orientation of `DET(f, x)` at the one point and `Lin(f, x)` nonempty, not an orientation
    of `f`.
97. **Remark 6.42 beyond a point is not formalized** *(book 2017: Remark 6.4, p. 214)*. That
    `(t, y) ↦ ô` is an orientation of `f̂` in the sense of Definition 6.40 (continuity over the
    orientable neighbourhoods of `ℝ¹ × X`, independence of the chart of the pull-back bundle), built
    from an orientation of `f`, is not formalized (gap G.66).

Not formalized (2026-11-07).

100. **Theorem 6.43 is not formalized** *(book 2017: Theorem 6.4, p. 215, and the case `∂X = ∅`, p.
     217)*. The map `Ψ_(f,o) : H*_dR(X, ∂X) → ℝ`, its proof (pp. 231–233) and the case `∂X = ∅`
     (p. 233) need the sc-differential forms and their cohomology of §4.4, which are not
     formalized (gaps G.37–G.40), integration over oriented compact manifolds with boundary with
     corners and Stokes' theorem, which Mathlib does not have (decision D1, gap G.54). What the
     theorem rests on is formalized: the perturbations of Theorem 5.18 (Chapter 5) and the
     tangent orientations of Theorem 6.41 (items 90–93).
101. **§6.6: the sections "admissible for the pair `(N, U)`" are not formalized** *(book 2017: §6.6,
     p. 215)*. The paragraph recalls Theorem 5.18 (formalized in Chapter 5, comparison items
     V5.38, V5.39) and the orientation of `S_{f+s}` (item 93); the notion it defines is used only
     in Theorem 6.43 (gap G.55).
102. **Not formalized: the facts used with paths on `[0, 1]`** *(book 2017: §6.5)*. Paths,
     homotopies and families sc-smooth on `[0, 1]`, `[0, 1]²`, `[0, 1]ⁿ` only, and `X × [0, 1]`
     as an M-polyfold with boundary, are read on `ℝ`, `ℝ²`, `ℝⁿ` and `ℝⁿ × X` (decision D2), as
     for Proposition 6.2 in Chapter 3; a path that does not extend sc-smoothly to `ℝ` is not
     covered (gap G.65).
103. **The proof of Theorem 6.43 extends `ω` as `ω̄ = p₁*ω ∧ p₂*dt`** *(book 2017: unchanged,
     proof of Theorem 6.4)* *(book 2021: unchanged, proof of Theorem 6.7.1, p. 278)*. To show that (97) does not depend on the admissible section, the
     proof (p. 232) introduces `ω̄ = p₁*ω ∧ p₂*dt` on `X × [0, 1]` with `ω̄|∂X×[0,1] = dτ̄`,
     `dτ̄ = p₁*(dτ) ∧ p₂*dt`, and applies Stokes' theorem on `S_F`. As we read it, the
     computation needs `p₁*ω` and `p₁*τ` themselves: `p₂*dt` restricts to zero on `X × {0}` and
     `X × {1}`, where the integrals over `S₀` and `S₁` are to appear, and `p₁*ω ∧ p₂*dt` has
     degree one more than `dim ∂S_F` (possible misprint). Not formalized (gap G.54); noted in
     `Exposition/Chapter6.md`, §7.

## Chapter 7 (Ep-groupoids; Lean `Polyfold/Chapter7/`)

*Numbering.* The items of this section are numbered in blocks, one block per part of the chapter,
so that agents working at the same time do not collide; the gaps in the numbering are unused
numbers, not deleted items. 1–19: §7.1 up to Proposition 7.4, groupoids, ep-groupoids and their
first properties (Definitions 7.1–7.7, Propositions 7.1–7.4, Lemma 7.1; `Chapter7/Groupoid.lean`,
`EpGroupoid.lean`, `ProperMaps.lean`, `LocalDiffeo.lean`, `Basic.lean`); 20–39: natural
representations and local uniformizers (Theorems 7.1, 7.5, pp. 231–233, Proposition 7.5,
Definitions 7.8, 7.9, Proposition 7.6, Lemmas 7.8, 7.9 of Appendix 7.5.1; `LocConnected.lean`,
`Discrete.lean`, `NaturalRep.lean`, `NaturalAction.lean`, `NaturalRepFinite.lean`,
`Uniformizer.lean`); 40–49: ep-subgroupoids (Definition 7.10, Proposition 7.7; `SubGroupoid.lean`);
50–69: §7.2, effective and reduced ep-groupoids (Definitions 7.11–7.13, Lemmas 7.2, 7.3,
Propositions 7.8–7.10; `Effective.lean`, `Reduced.lean`); 70–79: §7.3 up to Corollary 7.2, the
topology of `|X|` (Theorem 7.2, Lemmas 7.4–7.7, Corollaries 7.1, 7.2, Definition 7.14;
`OrbitTopology.lean`, `Michael.lean`); 80–89: index lifts and paracompact orbit spaces
(Propositions 7.11, 7.12, Definition 7.15, Remark 7.1; `Lift.lean`); 90–99: §7.4 and Appendix
7.5.2, partitions of unity and proper subsets (Theorems 7.3, 7.4, 7.6, Definitions 7.16, 7.17,
Remark 7.2, Propositions 7.13, 7.14, Lemma 7.10, Corollary 7.3; `ProperSubsets.lean`,
`PartitionsOfUnity.lean`); 100–109: witnesses, counterexamples and the check of the hypotheses
(`NonVacuity.lean` and the witnesses of the other files); 110–119: not formalized, and the gaps of
Part I taken up here. Part II has no 2014 preprint: statement numbers and pages are the 2017
text's (pp. 225–256); Part I results are cited by their 2017 numbers. The comparison items are
`Exposition/verification/ch07.md` (V7.1–V7.68).

Found while formalizing §7.1 up to Proposition 7.4 (2026-11-07).

1. **Definition 7.1 is read as a structure of maps; the composition is total** *(Definition 7.1,
   pp. 225–226)*. A groupoid is `GroupoidStr Obj Mor`: maps `src`, `tgt`, `comp`, `unit`, `inv`
   with the laws of (1)–(4) required on composable pairs only; `comp φ ψ` of a non-composable
   pair is a junk value, never used. `mor(x, y)`, the relation `x ∼ y` (`Isomorphic`,
   `orbitSetoid`), `|X|` (`OrbitSpace`) and `π` are as in the text; the saturation `π⁻¹(π(A))`
   used from Definition 7.10 on is `saturation`, with `isSaturated_iff`. Not in the text: the
   bridge `GroupoidStr.Ob` to Mathlib's `CategoryTheory.Groupoid` and `GroupoidFunctor.toFunctor`,
   so that "full" and "faithful" (p. 232, Proposition 7.6) are Mathlib's `Functor.Full`,
   `Functor.Faithful`.
2. **The isotropy group has the text's multiplication** *(Definition 7.2, p. 226)*. `Isotropy x`
   is the group of `φ : x → x` with `g * h = g ∘ h`, which is the text's. Mathlib's vertex group
   `x ⟶ x` multiplies in the other order: `isotropyEquivVertexGroup` identifies `G_x` with its
   opposite group, and `isotropyEquivAut` with `Aut x`.
3. **Definition 7.3 (3) is read existentially, with Mathlib's proper maps** *(Definition 7.3 (3),
   p. 227)*. "Every point `x` possesses an open neighbourhood `V(x)` such that
   `t : s⁻¹(cl_X(V(x))) → X` is proper" is `exists_isProperMap`: for each `x` there is such a `V`,
   and "proper" is `IsProperMap` of the restriction (`domRestrict`). The text's proofs use the
   sequential form ("after perhaps taking a subsequence"; Proposition 7.3, Lemma 7.1,
   Propositions 7.7, 7.11, 7.13, Lemma 7.8); it is equivalent here (`isProperMap_iff_exists_tendsto_subseq`, `isProperMap_domRestrict_iff`,
   `MPolyfold.isProperMap_domRestrict_iff_isCompact_preimage`), since M-polyfolds are metrizable
   (Theorem 2.2). Two facts the text uses without comment are proved: properness passes to every
   smaller open `V' ⊆ V(x)` (`isProperMap_domRestrict_closure_mono`, `HasPropernessProperty.mono`),
   and it cannot be asked of every neighbourhood (item 103).
4. **Definition 7.3 (4): the fibred product, and the citation "Lemma 2.8 in [38]"** *(Definition
   7.3 (4), p. 227)*. The text makes `𝐗 ₛ×ₜ 𝐗` an M-polyfold "in view of Lemma 2.8 in [38]", the
   paper *A General Fredholm Theory III* (bibliography, entry [38]); this is an external citation,
   not a misprint. Its statement in the book is Part I's Proposition 2.15, which the formalization
   uses (`MPolyfold.isSubMPolyfold_fibredProduct`, `MPolyfold.subPolyfold`): (4) is `IsScSmoothComp`,
   sc-smoothness of `m` on that sub-M-polyfold of `𝐗 × 𝐗`. The proofs use the equivalent sheet form
   `IsScSmoothCompSheet` (for every sheet `σ` of `s`, `ψ ↦ m(σ(t ψ), ψ)` is sc-smooth), proved
   equivalent in `isScSmoothComp_iff_sheet`.
5. **`φ̂` and Definition 7.4; `Tφ` is only defined** *(p. 227, Definition 7.4)* *(book 2021: before Definition 7.1.4, p. 289: the `∘` for `:` corrected; `T_{t(φ)}` without `X` unchanged, checked on the printed page)*. The open sets
   `𝐔(φ)`, `U(x)`, `U(y)` on which `s` and `t` are sc-diffeomorphisms are `Sheet` (`exists_sheet`,
   `sheetAt`), and `φ̂ = t ∘ (s|𝐔(φ))⁻¹ : U(x) → U(y)` is `hat`, an sc-diffeomorphism
   (`isScDiffeoOn_hat`) with `φ̂(x) = y` (`hat_src`). `Tφ := Tφ̂(x)` is `tangentMor`, a definition
   only: that it is well defined (`Ts` injective on `T_φ𝐗`), equal to `Tφ̂(s(φ))`, bijective, a
   bounded linear isomorphism on level `0` for `φ ∈ 𝐗₁`, and an sc-operator for smooth `φ` is not
   formalized; the linearity needs the linear structure of `T_xX` (gap G.7) and is deferred to
   Chapter 8 (gap G.70). In the extracted text the display reads "`φ̂ = t ∘ (s|𝐔(φ))⁻¹ ∘ U(x) →
   U(y)`", `∘` for `:` (possible misprint; the same slip as in Definition 7.9, item 28), and
   "`Tφ : T_{s(φ)}X → T_{t(φ)}`" lacks the `X` (possible misprint or extraction artefact; check
   against the printed page).
6. **Levels, the degeneracy index, and the filtration of `|X|`** *(pp. 227–228, Definition 7.5)*.
   `s` and `t` preserve the levels (`mem_levelSet_src_iff`, `mem_levelSet_tgt_iff`), so
   `ml(x) = ml(φ) = ml(y)` (`MPolyfold.maxLevel`, `MPolyfold.IsLocalScDiffeo.maxLevel_eq`), and
   `d_X(s φ) = d_𝐗(φ) = d_X(t φ)` by Part I's Proposition 2.7 (`MPolyfold.IsLocalScDiffeo.degIndex_eq`,
   `degIndex_src`, `degIndex_tgt`); `d_|X|` of Definition 7.5 is `degIndexOrbit`, well defined by
   `degIndexOrbit_π`. The sets `|X_k| = π(X_k)` are `orbitLevel k`; the set `|X_∞|` and the identity
   `|X_∞| = ⋂_k |X_k|` (immediate, as `ml` is constant on classes) are not stated (gap G.72). The
   density of `X_∞` in every `X_k` (p. 227) is item 116 (gap G.73).
7. **Definition 7.6 and the tameness of `𝐗`** *(Definition 7.6 and the paragraph after it, p.
   228)*. "`X` is a tame M-polyfold" is `MPolyfold.IsTame`, the existence of an equivalent tame
   atlas (Definition 2.19). The claim that `𝐗` is then tame is proved by transporting tame charts
   along the local sc-diffeomorphism `s` (`MPolyfold.IsScDiffeoOn.exists_tame_chart`,
   `MPolyfold.IsLocalScDiffeo.isTame`; the converse for surjective maps is
   `MPolyfold.IsLocalScDiffeo.isTame_iff_of_surjective`). Read as "every chart is modelled on a
   tame retract" the definition would be unsatisfiable (item 106, point 1).
8. **Definition 7.7: the category `EP`** *(Definition 7.7, p. 228)*. Morphisms are `EpFunctor`s:
   `GroupoidFunctor`s (maps on objects and morphisms commuting with `s`, `t`, `m`, `u`) that are
   sc-smooth on both spaces. That a functor commutes with `ι` is derived (`GroupoidFunctor.mor_inv`);
   identities and composites (`EpFunctor.id`, `EpFunctor.comp`) make `EP` a category, and functors
   induce continuous maps of orbit spaces (`GroupoidFunctor.orbitMap`).
9. **The remark after Definition 7.7 does not hold as we read it; it holds for functors continuous
   on morphisms** *(pp. 228–229)* *(book 2021: corrected, the remark after Definition 7.1.7, p. 291, now asks continuity on morphisms)*. The text says that sc-smoothness of `f` on objects suffices,
   because `f(γ) = (s|𝐔(ψ))⁻¹(f(s(γ)))` on `𝐔(φ)`, given neighbourhoods with
   `f(𝐔(φ)) ⊆ 𝐔(ψ)`. Such neighbourhoods need `f` to be continuous on morphisms, and without that
   the claim fails: on the ep-groupoid of `ℤ/3` acting trivially on `ℝ`, the functor that is the
   identity on objects and sends `(g, y)` to `(g, y)` for `y ≤ 0` and to `(g², y)` for `y > 0` is a
   functor, sc-smooth on objects, not continuous on morphisms
   (`Examples.remark_definition_7_7_counterexample`, item 104). With continuity the argument goes
   through, and needs only a sheet `𝐔(ψ)` of `s` at `ψ = f(φ)` and `𝐔(φ) = f⁻¹(𝐔(ψ))`
   (`isScSmoothMap_mor_of_continuous`, `isScSmoothMap_mor_iff_continuous`, `EpFunctor.ofContinuous`;
   the formula is `mor_eq_srcInv_obj_src`).
10. **Propositions 7.1 and 7.2: the proofs** *(p. 229)*. Proposition 7.1 is proved through the
    saturation: `π⁻¹(π(U)) = t(s⁻¹(U))` is open since `t` is an open map
    (`proposition_7_1`; also `proposition_7_1_isOpenQuotientMap`, `proposition_7_1_map_nhds`); the
    text argues point by point with the same sheets. Proposition 7.2 uses the metrizability of `X`
    (Theorem 2.2, `MPolyfold.metrizableSpace`): balls of radius `1/(k + 1)` give a monotone
    countable basis, read as Mathlib's `HasAntitoneBasis` (`proposition_7_2_of_hasAntitoneBasis`,
    `proposition_7_2`, `proposition_7_2_firstCountableTopology`).
11. **Proposition 7.3 is proved without sequences, for every `A ⊆ cl U`** *(Proposition 7.3, pp.
    229–230)*. For `U` with the properness property, `π(cl A) = cl π(A)` holds for every
    `A ⊆ cl_X(U)` (`proposition_7_3_of_isProperMap`), from the closedness of the proper map
    `t : s⁻¹(cl U) → X` (`isClosed_image_preimage_of_isProperMap_domRestrict`); the statement for
    `A ⊆ U` is `proposition_7_3`. The text's sequence argument is the same fact.
12. **Lemma 7.1: the proof works with the inverses; misprints** *(Lemma 7.1, p. 230)* *(book 2021: Lemma 7.1.11, p. 292: the exchange of `s` and `t` and "`V(y)`" unchanged; "`s(ψ) ∈ s⁻¹(…)`" corrected to `s(ψ) ∈ cl_X(U(x′))`)*. The
    statement counts the `ψ` with `s(ψ) = x`, `t(ψ) ∈ U(x₀)` (`lemma_7_1`); the proof takes
    `ψ_n : s(ψ_n) → x` with `s(ψ_n) ∈ U(x₀)`, the inverses of those, with `s` and `t` exchanged
    (possible misprint; both forms are proved, the proof's as `lemma_7_1_swap`, and they are
    equivalent by `ι`). In the proof, "`t : V(ψ) → V(y)`" is meant for `V(x)`, and the limit
    satisfies "`s(ψ) ∈ s⁻¹(cl_X(U(x₀)))`" where `ψ ∈ s⁻¹(cl_X(U(x₀)))`, i.e. `s(ψ) ∈ cl_X(U(x₀))`,
    is meant (possible misprints; for the parentheses see item 96). The openness of `U(x₀)` and
    `x₀ ∈ U(x₀)` are not used (`_hU`, `_hx₀`). The finiteness is proved without sequences: the
    fibre over `x` of the proper map is compact and discrete, as `t` is a local homeomorphism
    (`finite_setOf_mem_of_isProperMap_domRestrict`,
    `IsProperMap.finite_preimage_singleton_of_isLocallyInjective`).
13. **Proposition 7.4 and the conjugation `G_x → G_y`** *(Proposition 7.4 and the paragraph after
    it, p. 230)*. `G_x` is finite by Lemma 7.1 with `x₀ = x` (`proposition_7_4`, an instance; the
    abstract form is `MPolyfold.finite_isotropy_of_isLocalScDiffeo`). The isomorphism
    `g ↦ φ ∘ g ∘ φ⁻¹` is `conjIsotropy` (`nonempty_isotropy_mulEquiv`, `nat_card_isotropy_eq`);
    "there is no canonical identification" is made precise: two choices of `φ` give isomorphisms
    that differ by an inner automorphism of `G_y` (`isotropyConj_eq_isotropyConj_conj`).

Found while formalizing the natural representations and local uniformizers (2026-11-07).

20. **Theorem 7.1 is read as the datum `NaturalRep`, with `U` connected** *(Theorem 7.1, p. 231)*.
    `NaturalRep x` holds `U` open, connected, containing `x`, `Φ` and `Γ` with (1)–(3); the theorem
    is `theorem_7_1`: for every open `V ∋ x` there is one with `U ⊆ V`. The statement does not say
    "connected", but the text chooses "the connected open neighborhood `U(x)`" two paragraphs later
    (p. 231), and connectedness is what makes `Φ` a homomorphism with `Φ(1) = id`: two sections of
    `s` through the same morphism agree on a connected set (`eqOn_sections_of_isPreconnected`).
    `Φ(g) ∈ Diff_sc(U)` is read as an sc-diffeomorphism of `U` with inverse `Φ(g⁻¹)`
    (`isScDiffeoOn_Φ`, `Φ_mul`), and "`Γ : G × U → 𝐗` sc-smooth" per sheet, `y ↦ Γ(g, y)`
    sc-smooth for each `g` (`isScSmoothOn_Γ`), which is sc-smoothness on `G × U` (item 23). (3) is
    `existsUnique_Γ`, with the bijection `NaturalRep.bijOn_Γ`.
21. **Local path connectedness of M-polyfolds is proved** *(used on p. 231, in Lemma 7.9 and in
    Corollary 7.2)*. The text takes connected neighbourhoods `U(x)`, `U₂` and open connected
    components for granted. An sc-retract `O = r(U)` is locally path connected: a point `p ∈ O`
    near `o` is joined to `o` inside `O ∩ W` by the path `τ ↦ r(o + τ(p − o))`
    (`ScRetraction.exists_ball_joinedIn`, `IsScRetract.locallyPathConnectedSpace`); hence so is
    every M-polyfold
    (`MPolyfold.locallyPathConnectedSpace`, `MPolyfold.locallyConnectedSpace`,
    `MPolyfold.hasBasis_isOpen_isConnected`, `MPolyfold.isOpen_connectedComponent`) and every
    quotient of one (`MPolyfold.locallyPathConnectedSpace_quotient`). This is the first of the two
    facts of gap G.56 (item 114).
22. **The discussion on pp. 231–233 is formalized** *(pp. 231–233)* *(book 2021: the composability condition with `Φ(h)(y)` unchanged, after Theorem 7.1.13, p. 294)*. The splitting
    `𝐔(x) = ⊔_g 𝐔(g)` into the connected open sets `𝐔(g) = Γ(g, U)` with `s, t : 𝐔(g) → U`
    sc-diffeomorphisms (`NaturalRep.pairwise_disjoint_image_Γ`, `NaturalRep.iUnion_image_Γ`,
    `NaturalRep.connectedComponentIn_morOn`, `NaturalRep.isScDiffeoOn_src_image`,
    `NaturalRep.isScDiffeoOn_tgt_image`); "`𝐔(x)` fits into an arbitrarily small open neighbourhood
    of `G_x`" is Lemma 7.8 with any open `N_g ∋ g` followed by Theorem 7.1 with `V = U₁`
    (`lemma_7_8`, `theorem_7_1`). The translation groupoid `G_x ⋉ U(x)` is an ep-groupoid built from
    the data `(Φ, Γ)` alone (`NaturalRep.translationEpGroupoid`), with the properness for every `V`
    (`NaturalRep.translation_isProperMap`), "using the proof of Theorem 7.1" not being needed. The
    functor `Γ` is a functor because `U` is connected (`NaturalRep.Γ_mul`, `NaturalRep.Γ_one`,
    `NaturalRep.Γ_inv`), full and faithful by (3) (`NaturalRep.full`, `NaturalRep.faithful`), an
    `EpFunctor` (`NaturalRep.epFunctor`), with image the full subcategory on `U`. `Φ̂` is defined by
    the text's formula (`NaturalRep.Φhat`, `NaturalRep.Φhat_Γ`); it is a homomorphism of
    sc-diffeomorphisms of `𝐔(x)` with the two commutative diagrams (`NaturalRep.Φhat_mul`,
    `NaturalRep.Φhat_one`, `NaturalRep.src_Φhat`, `NaturalRep.tgt_Φhat`, `NaturalRep.image_Φhat`,
    `NaturalRep.isScDiffeoOn_Φhat`). One possible misprint (p. 232, added 2026-11-07 from the
    comparison): the composability condition reads "`y = s(g, y) = t(h, z) = Φ(h)(y)`", where
    `Φ(h)(z)` is meant.
23. **`G × U` as an M-polyfold** *(p. 232)*. "The finite disjoint union of copies of the
    M-polyfold `U`" is the product of `U` with the discrete M-polyfold on `G`
    (`discretePolyfold`, `discreteChart`); a map on `G × U` is sc-smooth iff it is on every slice
    (`isScSmoothOn_univ_prod_discrete_iff`, `isScSmoothMap_prod_discrete_iff`). The source and target
    of `G ⋉ U` are local sc-diffeomorphisms, `t` through the shear `(g, y) ↦ (g, Φ(g)(y))`
    (`NaturalRep.shearHomeomorph`).
24. **Uniqueness and restriction of natural representations** *(used on pp. 239–241: "`U(x)` can be
    chosen arbitrarily small", "adapting restrictions" in Lemma 7.3)*. Two natural representations
    at `x` agree on the connected component of `x` in `U ∩ U'` (`NaturalRep.Γ_eqOn`,
    `NaturalRep.Φ_eqOn`), and a natural representation restricts to every `G_x`-invariant connected
    open neighbourhood (`NaturalRep.restrict`, `NaturalRep.restrictInter`,
    `exists_naturalRep_restrict`, `exists_naturalRep_shrink`). The text uses both without
    statement.
25. **Proposition 7.5 is proved by a star construction, without induction or shrinking**
    *(Proposition 7.5, pp. 233–236)*. The functor `f` with its properties is the datum
    `NaturalRepFinite Y V` (Definition 7.8). Instead of the text's induction on `k`, which shrinks
    the neighbourhoods at each step, the formalization fixes a natural representation at one object
    `x` (which need not lie in `Y`), chooses morphisms `x → y` for `y ∈ Y` and transports it along
    them (`NatRepFinite.transportRep`, `NatRepFinite.Star`, `NatRepFinite.exists_star`); (1) holds
    with the transported natural representations. `V` is read as a neighbourhood of the set `Y`
    (`proposition_7_5_of_mem_nhdsSet`; the open form `proposition_7_5`), and `Y = ∅` is allowed
    (`NatRepFinite.emptyNaturalRepFinite`).
26. **Possible misprints in the proof of Proposition 7.5** *(pp. 234–236)* *(book 2021: proof of Proposition 7.1.15, pp. 297–300: the four slips of p. 234, `Ψ_g` and "k = 1" corrected; the other six unchanged)*. p. 234: "unique
    `g ∈ G_x`" for `G_{y₁}`; two morphisms both named `φ` (`φ : u → z` and `φ : u' → z'`; a lost
    prime is possible, an extraction artefact); "Fixing `g ∈ G_{y1}`" for `G_{y2}`; the garbled
    sentence "It is also which implies". p. 235: "`𝐔(γ_g) := Ψ_g(𝐔(γ₁))`" for `Φ_g`; "images
    `𝐔(ψ_g)`" for `𝐔(γ_g)`; "`φ = Γ(g, s(φ)) ∘ ψ`" for `Γ(g, t(ψ)) ∘ ψ`; "Let `k ≥ 3`" for
    `k ≥ 2`; "as in the case `k = 1`" where the two-object case `k = 2` is meant;
    "`s : 𝐔'(φ) → U'(y_i)`" with `φ` for `γ`; "`y : 𝐔(δ_j) → U(y_j)`" for `t`. p. 236: "`g ∈ G_{y_i}`"
    for `G_{y_j}`. None affects the argument, which is replaced by item 25.
27. **Proposition 7.6: the openness of `σ` is not needed** *(Proposition 7.6, pp. 236–237)*. The
    proof follows the text (injectivity by Theorem 7.1 (3), openness of `|U(x)|` by Proposition
    7.1). The image of an open `Q ⊆ G_x\U(x)` is `π(σ⁻¹(Q))` with `σ⁻¹(Q)` open in `U(x)`, so `τ`
    into `|X|` is a continuous injective open map, an open embedding onto `π(U(x))`
    (`NaturalRep.isOpenEmbedding_orbitQuotientMap`, `proposition_7_6`); the second form is
    `proposition_7_6_fullyFaithful` and `proposition_7_6_orbitMap`.
28. **Definition 7.9 and the claims after it** *(Definition 7.9, p. 237)* *(book 2021: both corrected, Definition 7.1.20, p. 305)*. "`Ψx ◦ Gx ⋉ U(x) → X`"
    is read as `Ψ_x : G_x ⋉ U(x) → X` (possible misprint), and "a a local uniformizer" doubles the
    article (possible misprint). `LocalUniformizer` has `Ψ_x` the inclusion on objects, full and
    faithful, inducing a homeomorphism onto `π(U(x))`; "embedding" is not a separate field: the
    injectivity on objects and morphisms that the text notes afterwards follows
    (`LocalUniformizer.injective_obj`, `LocalUniformizer.injective_mor`), and for the uniformizers
    built from natural representations `Ψ_x` is an open embedding on both spaces
    (`NaturalRep.isOpenEmbedding_functor_obj`, `NaturalRep.isOpenEmbedding_functor_mor`). Existence
    is proved inside every open `V ∋ x` (`exists_localUniformizer`).
29. **The proof of Theorem 7.5 (= Theorem 7.1)** *(Theorem 7.5, pp. 253–254)* *(book 2021: "`G_x`" for `G_{x₀}` unchanged, Theorem 7.6.1, p. 344)*. `theorem_7_5` is
    `theorem_7_1` (the text restates Theorem 7.1 in Appendix 7.5.1), proved along the text with
    Lemmas 7.8 and 7.9 (`NatRepConstruction.exists_sheets`, `NatRepConstruction.Sheets.mkRep`).
    Readings: the neighbourhood is started at `U₀ := V ∩ ⋂_g s(N_g)`, so that `U ⊆ V`, which the
    text's proof does not address; only `s_g` has to be an sc-diffeomorphism onto `U₀`; the
    disjointness of the `N_g` is used only for the uniqueness in (3); "contractible" `N^t_g`, `N^s_g`
    is not needed. In the statement, "`Φ : G_x → Diff_sc(U)`" in the sentence after the bullets is
    meant for `G_{x₀}` (possible misprint).
30. **Lemma 7.8** *(Lemma 7.8, pp. 253–254)* *(book 2021: corrected, Lemma 7.6.2, p. 345)*. The indirect argument is run along a countable basis
    of `x₀`; properness applies once `s(h_k)`, `t(h_k)` lie in a neighbourhood with the properness
    property, i.e. for large `k`. The lemma holds for any open `N_g ∋ g` and any neighbourhood `U₀`
    (`lemma_7_8`). "By the properness assumption of ep-polyfolds" is meant for ep-groupoids
    (possible misprint).
31. **Lemma 7.9: `U₂` connected** *(Lemma 7.9, p. 254)*. `U₂` is chosen connected, by item 21
    (the text does not say so); then `U = ⋃_g t_g s_g⁻¹(U₂)` is connected as each piece contains
    `x₀` (`NatRepConstruction.Sheets.isConnected_unionHat`), which the homomorphism property needs.
    The invariance and `U ⊆ U₁` are `lemma_7_9`; the continuity of the composition used for
    `Φ(gh) = Φ(g)Φ(h)` comes from (4) in sheet form (`NatRepConstruction.Sheets.eqOn_σ_mul`,
    `NatRepConstruction.Sheets.hat_mul`, `NatRepConstruction.Sheets.hat_one`).

Found while formalizing the ep-subgroupoids (2026-11-07).

40. **Definition 7.10 and the facts (1)–(4) of a sub-M-polyfold** *(Definition 7.10 and pp.
    237–238)*. Definition 7.10 is `IsEpSubgroupoid` (sub-M-polyfold and saturated). The four facts
    recalled from Part I's Proposition 2.6 are used in their forms (1) and (2) (`subObjPolyfold`,
    `isScSmoothMap_val_subObj`, `isScSmoothOn_retractInto_subObj`); the tangent facts (3) and (4) are
    not restated, as `T_aA` and `T_aX` carry no linear structure here (gap G.7); in a chart they are
    Part I's `proposition_2_21_3`, `proposition_2_21_4`.
41. **The morphisms `𝐀` and the retraction `𝐫`** *(p. 238)* *(book 2021: the claim `t(𝐫(ψ)) ∈ U(a)` unchanged, before Proposition 7.1.22, p. 306)*. For saturated `A`, `𝐀 = s⁻¹(A) =
    t⁻¹(A)` (`morOn_eq_preimage_src`, `morOn_eq_preimage_tgt`, `src_mem_of_tgt_mem_of_isSaturated`),
    the preimage of a sub-M-polyfold under a local sc-diffeomorphism, hence a sub-M-polyfold
    (`isSubMPolyfold_preimage_src`, `isSubMPolyfold_morOn`); the text's `𝐫 = (s|𝐔(φ))⁻¹ ∘ r ∘ s` is
    that construction. The extracted text has "`s(𝐫(ψ)) = r(s(ψ)) ∈ A` and `t(𝐫(ψ)) ∈ U(a)`, so that
    `𝐫(ψ) ∈ 𝐔(a)`": the second claim need not hold (`t(𝐫(ψ))` lies near `t(φ)`, not near `a`) and is
    not used, since `𝐫(ψ) ∈ 𝐀` follows from `s(𝐫(ψ)) ∈ A` and saturation (possible misprint or
    extraction artefact; check against the printed page).
42. **Proposition 7.7: steps the text leaves out** *(Proposition 7.7, pp. 238–239)*. (i) A map that
    is sc-smooth into `X` and takes values in the sub-M-polyfold `A` is sc-smooth into `A` (a private
    lemma of `SubGroupoid.lean`); this is what "restrictions of sc-smooth maps" needs. (ii) The
    fibred product of `𝐀` includes sc-smoothly into that of `𝐗`, which (4) for `A` needs
    (`isScSmoothComp_fullSub`). (iii)
    `A` and `𝐀` must be paracompact for the project's M-polyfolds; the text does not address it
    (`instParacompactSpaceMorOn`, scoped). (iv) The properness: any `V(a)` with the properness
    property works, the `G_a`-invariance of `U(a)` is not used, and the subsequence is taken by the
    sequential criterion (`exists_isProperMap_fullSub`). Not in the text: the inclusion is a fully
    faithful functor (`subEpFunctor`, `subEpFunctor_full`, `subEpFunctor_faithful`). The conclusion is
    `proposition_7_7`, with `subEpGroupoid`.

Found while formalizing §7.2 (2026-11-07).

50. **Definition 7.11 and the regular objects** *(Definition 7.11 and the sentence after it, p.
    239)*. `IsEffective` is the text's condition (every open neighbourhood of `g ≠ 1_x` contains `ψ`
    with `s(ψ) ≠ t(ψ)`); regular objects are `GroupoidStr.IsRegular`, `X_reg` is `regularSet`. The
    sentence "if `s(φ)` is regular, so is `t(φ)`" is `isRegular_tgt_of_isRegular_src`, by the
    conjugation of item 13; `X_reg` is saturated (`isSaturated_regularSet`).
51. **Lemma 7.2 uses `Γ(1, a) = 1_a`** *(Lemma 7.2, p. 239)*. For `a ∈ U(x)` the morphisms
    `a → a` are `Γ(g, a)` with `Φ(g)(a) = a`; that `G_x = {1}` gives `G_a = {1_a}` needs
    `Γ(1, a) = 1_a`, which holds because `U` is connected (item 20). The lemma holds for every
    natural representation (`NaturalRep.subset_regularSet`, `lemma_7_2`).
52. **Lemma 7.3: "adapting restrictions" through uniqueness** *(Lemma 7.3, pp. 239–240)*. (2) is
    read with "injective" as "trivial kernel" (`NaturalRep.injective_Φ_iff`,
    `NaturalRep.kerΦ_eq_bot_iff`). (1) ⇒ (2) holds for every natural representation and is proved
    without sequences (`IsEffective.eq_one`, `isEffective_iff_forall_naturalRep`). (2) ⇒ (1): the
    text's "adapting restrictions" is read through the uniqueness of item 24, applied once with
    `V = {y ∈ U₀ | Γ₀(g, y) ∈ 𝐔(g)}`. The equivalence is `lemma_7_3`.
53. **Proposition 7.8: the minimum is taken over the open set itself; the converse holds**
    *(Proposition 7.8, pp. 240–241)*. The text minimizes `#G_x` over `U(x₀)`; the formalization
    minimizes over the given open set, so `U(x₀)` is not needed, and identifies `G_a` with the
    stabilizer of `a` in `G_x` (`NaturalRep.stabilizerEquivIsotropy`, the text's `H`). The converse,
    not in the text, also holds: `X` is effective iff `X_reg` is dense
    (`isEffective_of_dense_regularSet`, `isEffective_iff_dense_regularSet`).
54. **The subgroup `T_x`** *(p. 241)* *(book 2021: the parenthesis corrected, p. 309; `T_x` is now Definition 7.2.5, and `φ T_x φ⁻¹ = T_y` is Lemma 7.2.6, p. 310)*. "`g` acts trivially" is `ActsTrivially` (there is a natural
    representation with `Φ(g) = id`), `T_x` is `trivialSet` and `trivialSubgroup`. The kernel of `Φ`
    depends on `U(x)` (sc-smooth maps are not analytic); the text's "we can choose `U(x)` so small
    that the kernel is `T_x`" is proved in the form: there is a neighbourhood `N` of `x` such that
    `ker Φ = T_x` for every natural representation inside `N` (`exists_mem_nhds_trivialSet_iff`,
    `exists_naturalRep_kerΦ_eq`). Not in the text: the intrinsic form `g ∈ T_x` iff `s = t` near `g`
    in `𝐗` (`mem_trivialSet_iff_eventually`); `T_x` is a normal subgroup (`trivialSubgroup_normal`),
    trivial for all `x` iff `X` is effective (`isEffective_iff_trivialSubgroup_eq_bot`). Needed for
    Definition 7.12 and not stated: `φ T_x φ⁻¹ = T_y` for `φ : x → y`
    (`isotropyConj_mem_trivialSet`, `map_isotropyConj_trivialSubgroup`). "`Diff_sc(U(x)`" lacks a
    parenthesis (possible misprint or extraction artefact; check against the printed page).
55. **Definition 7.12: `∼` is an equivalence relation; "the subset `𝐗^R`"** *(Definition 7.12, p.
    241)* *(book 2021: corrected, Definition 7.2.7, p. 310)*. `∼` is an equivalence relation because `T_x` is a subgroup (`reducedSetoid`). Equivalent
    forms: `φ = φ' ∘ k` with `k ∈ 𝐗^T`, and `𝐗^T` is the interior of `{s = t}`
    (`nonEffectivePart_eq_interior`); the left form `k ∘ φ` (`reducedRel_comp_left`). `𝐗^R` is called
    "the subset of reduced morphisms"; it is a quotient of `𝐗`, as the next sentence says
    ("the collection of all equivalence classes") (possible misprint). `𝐗^R` is `ReducedMor`.
56. **Proposition 7.9 takes `𝐗^R` Hausdorff and paracompact as hypotheses** *(Proposition 7.9, pp.
    242–243)* *(book 2021: corrected, Theorem 7.2.14, p. 318, assumes `T_R` Hausdorff; paracompactness is Proposition 7.2.12, p. 317)*. An M-polyfold is a paracompact Hausdorff space (Definition 2.8). The proof gives the
    quotient topology, the openness of the projection (`isOpenMap_reducedπ`), the charts
    `Ψ_φ = ψ ∘ σ ∘ s` on `π(dom ψ)` (`reducedChart`) and their sc-smooth transitions
    `ψ₂ ∘ σ₂ ∘ s ∘ ψ₁⁻¹` (`reducedChart_compatible`), all without hypotheses; but, as we read it,
    neither Hausdorffness nor paracompactness, and `𝐗^R` need not be Hausdorff (item 107: `ℤ/2`
    acting on the dimension-jumping retract of Part I's Remark 4.3). So `reducedPolyfold`, and
    `proposition_7_9`, take `[T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]` (gap G.71).
    Small sheets are not needed. The hypotheses are satisfiable (item 60).
57. **Possible misprints in the proof of Proposition 7.9** *(pp. 242–243)* *(book 2021: rewritten as Lemma 7.2.9, Proposition 7.2.10 and the proof of Theorem 7.2.14, pp. 311–318; the first three now print the intended symbols, the garbled sentence is gone)*. "`ψ' = (s|𝐔(ψ))⁻¹(s(ψ))`"
    for `(s|𝐔(ψ))⁻¹(s(ψ'))` (a displaced prime is possible, an extraction artefact);
    "`𝐔(φ) ⊂ Ψ_{φ₀}(𝐔([φ₀]) ∩ 𝐔([ψ₀]))`" for `Ψ_{φ₀}⁻¹(…)` (a lost superscript is possible, an
    extraction artefact); "such that `T_x` agrees with the kernel of the `G_{s(φ)}`-action" for
    `T_{s(φ)}`; the garbled sentence "which show that the source and target maps are smoothness of
    the natural maps can be reduced" (p. 243).
58. **Proposition 7.10: the conditions of Definition 7.3 for `X_R`** *(p. 243, Proposition 7.10, p.
    244)* *(book 2021: rewritten, proof of Theorem 7.2.14, pp. 318–319, for `T_R` Hausdorff: properness proved, (4) left to the reader; effectiveness is Proposition 7.2.16, p. 319)*. `X_R` is `reducedEpGroupoid`, with `reductionFunctor : X → X_R`. (1): on a sheet,
    `s, t` of `𝐗^R` are `s_X ∘ (π|𝐔)⁻¹`, `t_X ∘ (π|𝐔)⁻¹`. (3), "proved similarly": `t ∘ π = t_X` with
    `π` a continuous surjection (Mathlib's `isProperMap_of_comp_of_surj`, `exists_isProperMap_reduced`).
    (4), "reduced by our local charts", in the sheet form, with `κ = σ₂ ∘ s ∘ σ'` the inverse of `s` on
    an open set of `𝐗`, a step the text leaves implicit (`isScSmoothCompSheet_reduced`). The text
    obtains the continuity of `δ` from (4) applied to inverses; the formalization uses the left form
    `Γ(g, t ψ') ∘ ψ'` (`NaturalRep.isScSmoothOn_comp_Γ_tgt`). Effectiveness is proved from the
    intrinsic `T_x` of item 54 instead of a point with `Φ(g)(a) ≠ a` (`isEffective_reducedEpGroupoid`).
    The conclusion is `proposition_7_10`.
59. **The isotropy of `X_R` and Definition 7.13** *(p. 244, Definition 7.13)* *(book 2021: "For and object" corrected, Definition 7.2.15, p. 319)*. `[1_x] = T_x` is
    `ker_reducedIsotropyHom`, and the isotropy of `X_R` at `x` is `G_x/T_x`
    (`surjective_reducedIsotropyHom`, `quotientTrivialSubgroupEquiv`). `G_x^eff` is `EffIsotropy`, the
    quotient by the normal closure of `T_x`, which is `T_x` (`normalClosure_trivialSet`,
    `effIsotropyEquiv`, `effIsotropyEquivReduced`). "For and object" (Definition 7.13) (possible
    misprint).
60. **The hypotheses on `𝐗^R` are satisfiable; for non-effective `X` they are not shown to hold**
    *(not in the text)* *(book 2021: Proposition 7.2.17 and Theorem 7.2.22, pp. 320–323: `T_R` Hausdorff iff `𝐗^T` closed iff (LUC); by it item 102 has `T_R` Hausdorff, item 107 not)*. For effective `X` the projection `𝐗 → 𝐗^R` is a homeomorphism
    (`reducedHomeomorph`), so `𝐗^R` is Hausdorff, paracompact and regular
    (`t2Space_reducedMor_of_isEffective`, `paracompactSpace_reducedMor_of_isEffective`,
    `t3Space_reducedMor_of_isEffective`) and `X_R ≅ X` (`reductionIso`); this covers the trivial
    ep-groupoid of every M-polyfold (`t2Space_reducedMor_trivial`,
    `paracompactSpace_reducedMor_trivial`). Paracompactness follows from regularity of `𝐗^R` when `𝐗`
    is second countable (`paracompactSpace_reducedMor_of_t3`). No non-effective witness is given:
    for the trivial `ℤ/3`-action (item 102) Hausdorffness of `𝐗^R` is not proved, and Hausdorff with
    `𝐗` second countable is not shown to suffice (a locally metrizable, second countable Hausdorff
    space need not be regular, the `K`-topology on `ℝ`). For the non-effective `ℤ/2 ⋉ O` of item
    107, `𝐗^R` is not Hausdorff (added 2026-11-07, after the round-trip audit).

Found while formalizing §7.3 up to Corollary 7.2 (2026-11-07).

70. **Theorem 7.2** *(Theorem 7.2, p. 244)*. "Locally metrizable" is read as: every point has an
    open neighbourhood that is metrizable in the subspace topology (`theorem_7_2`). The metrizability
    of a paracompact `|X|` is proved by Smirnov's theorem in the form of Part I
    (`metrizableSpace_of_locally`, `theorem_7_2_metrizable`), as the text indicates.
71. **Lemma 7.4: the metric `ρ̂`** *(Lemma 7.4, pp. 244–245)*. The text's invariant metric
    `ρ(y, y') = max_g d(g ∗ y, g ∗ y')` and the quotient metric are used; `ρ̂([y], [y'])` is computed
    as `min_h ρ(y, h ∗ y')`, equal to the text's expression by invariance, and the topology is
    checked through Mathlib's `MetricSpace.ofDistTopology` (`metrizableSpace_orbitRel_quotient_naturalRep`,
    `lemma_7_4_naturalRep`, `lemma_7_4`). With Proposition 7.6 this gives the metrizability of
    `|U(x)|`, the text's "in fact one can take `|U(x)|`".
72. **Lemmas 7.5–7.7: the order of proof** *(pp. 245–246)*. Lemma 7.5 is Proposition 7.2
    (`lemma_7_5`; the text derives it from Lemma 7.4). Lemma 7.7 is proved with a closed
    neighbourhood basis and Proposition 7.3 (`lemma_7_7`), and Lemma 7.6 from Lemma 7.7 and the
    closedness of points (`t1Space_orbitSpace`, Proposition 7.14 (1) for `{x}`; `lemma_7_6`); the text
    proves Lemma 7.6 directly.
73. **Corollary 7.1 and subsets of `|X|`** *(Corollary 7.1 and the sentence before Definition 7.14, p. 247)*. Corollary 7.1 is
    Urysohn's theorem (`corollary_7_1`). The sentence before Definition 7.14, that a subset of `|X|`
    is again locally metrizable, regular and Hausdorff, is `exists_metrizable_nhds_subtype` and
    Mathlib's instances; a paracompact subset is metrizable
    (`metrizableSpace_of_paracompactSpace_subtype`).
74. **Corollary 7.2: from compact pieces to a component compact `K`; `U` names two sets**
    *(Definition 7.14, Corollary 7.2, p. 247)* *(book 2021: absent, proof of Corollary 7.3.8, pp. 326–327: the printed page writes `Ū` for the union of closures, a bar the extraction drops, so the 2017 reading was probably an extraction artefact)*. Definition 7.14 is `IsComponentCompact`. "We work in a
    connected component of `K` and may assume … `K` compact" needs that the components of `|X|` are
    open (local connectedness of `|X|`, `locallyPathConnectedSpace_orbitSpace`, from item 21) and a
    step the text does not give: the neighbourhoods found in the components form a locally finite
    family of closed paracompact sets, whose union is paracompact (`paracompactSpace_iUnion`). The
    finite union of closed paracompact sets is paracompact by Michael's theorem (item 75), which the
    text does not cite (`paracompactSpace_biUnion_of_finite`). The compact case is
    `corollary_7_2_of_isCompact` (with `cl U` inside a given open `W ⊇ K`), the general one
    `corollary_7_2`. In the proof `U` denotes both `⋃ cl_|X|(U(z_i))` and `⋃ U(z_i)` (possible
    misprint). No other possible misprint was found on pp. 244–247.
75. **Michael's theorem and the paracompact unions** *(Part I, Lemma 2.7 and Proposition 2.17, used
    for Corollary 7.2 and on the text's route to Proposition 7.12)*. Part I left Lemma 2.7 (Michael)
    and Proposition 2.17 unformalized, as not needed (gap G.15). They are now proved
    (`lemma_2_56`, `proposition_2_57`, `michael_tfae`, `paracompactSpace_of_closed_refinement`,
    `exists_closed_precise_refinement`), with the unions used here (`paracompactSpace_iUnion`,
    `paracompactSpace_iUnion_of_finite`, `paracompactSpace_union`,
    `paracompactSpace_of_isClosed_subset`). Both are proved for regular spaces; the Hausdorff
    property, which the 2017 text assumes, is not used.

Found while formalizing the index lifts and paracompact orbit spaces (2026-11-07).

80. **Proposition 7.11: "(1), (2) and (4) trivially"** *(Proposition 7.11, pp. 247–248)* *(book 2021: unchanged, Proposition 7.3.9, p. 327)*. `X¹` is
    `liftOne`. The structure maps of `X¹` are the restrictions to level `1`; that `m(φ, ψ)` lies on
    level `1` uses `ml(t(φ ∘ ψ)) = ml(φ)` (item 6, `comp_mem_levelSet`); `liftComp` of a
    non-composable pair is a junk value. (1) is the level-`1` lift of a local sc-diffeomorphism
    (`MPolyfold.IsLocalScDiffeo.levelOne`), (2) Part I's `MPolyfold.IsScSmoothMap.levelOne`. For (4)
    the "trivially" uses, as we read it, `(𝐗 ₛ×ₜ 𝐗)¹ = 𝐗¹ ₛ×ₜ 𝐗¹` as M-polyfolds, which is not proved;
    it is avoided through the sheet form (`isScSmoothCompSheet_lift`, `isScSmoothComp_lift`). (3)
    follows the text, with "`(t(φ_k))` belongs to a compact subset of `X₁`" replaced by "`t(φ_k)`
    converges in `X₁`" and without the text's step (b) (`exists_isProperMap_lift`). The conclusion is
    `proposition_7_11`.
81. **Proposition 7.11: the tameness of `X¹` is proved** *(Proposition 7.11, p. 247, "If `X` is tame
    so is `X¹`")* *(book 2021: unchanged, Proposition 7.3.9, pp. 327–328, which now calls it trivial without an argument)*. The text gives no argument. As we read it, the claim needs that the index lift of
    a tame retraction is tame, which Part I left open (Chapter 5, item 145). It is proved
    (`MPolyfold.IsTame.levelOne`, `isTame_liftOne`): for a presentation `T : E ≅ ℝⁿ ⊕ W` of `C`, the
    shifted presentation of `C¹` has the same `ℝⁿ`-coordinates, so `d_{C¹} = d_C` on `C¹` and
    `E_x` for it is `E_x ∩ E₁`; `Dr¹(x) = Dr(x)|E₁` has range `T_xO ∩ E₁`; an sc-complement `A` of
    `T_xO` gives the sc-complement `A ∩ E₁` of `T_xO¹`. Part I's presentation independence
    (`ScRetraction.IsTameWith.isTame`) then gives tameness for every presentation of `C¹`, and the
    level charts of tame charts form a tame atlas of `X¹`.
82. **Definition 7.15, the sentence before Remark 7.1, and Remark 7.1** *(p. 249)*. Definition 7.15
    is `HasParacompactOrbitSpace`, Mathlib's `ParacompactSpace` without Hausdorff, as the text
    stipulates. "In case `X` has a second countable topology we have already seen that (1)–(4) imply
    (5)" is read with `X` the object space: `|X|` is then second countable (`π` is open), metrizable
    by Corollary 7.1, hence paracompact (`remark_7_1`); also for `|X|` second countable
    (`hasParacompactOrbitSpace_of_secondCountableTopology`). "It is presently not known whether the
    property (5) is a consequence of the properties (1)–(4)" is an open question, recorded without a
    gap (item 113). Remark 7.1 itself, on the requirement of [38], has no formal content.
83. **Proposition 7.12 by metrizability; `|X¹| → |X|`** *(Proposition 7.12, pp. 249–250)*. The text
    writes `|X₁|` for the orbit space of `X¹` and treats it as the subset `π(X₁)` of `|X|`. Here `|X¹|`
    keeps its quotient topology, and `orbitIncl : |X¹| → |X|` is a continuous injection onto
    `π(X₁)` (`continuous_orbitIncl`, `orbitIncl_injective`, `range_orbitIncl`). The text's route
    (Lemma 2.7, a locally finite closed refinement, Michael's union of closed paracompact sets) is
    replaced by Smirnov's theorem pulled back along `orbitIncl` (`metrizableSpace_of_pullback`): every
    point of `|X|` has the neighbourhood `π(U(x))` whose preimage is metrizable
    (`NaturalRep.metrizableSpace_preimage_orbitIncl`), so `|X¹|` is metrizable
    (`metrizableSpace_liftOne_orbitSpace`), hence paracompact (`proposition_7_12`), a stronger
    conclusion. "`U(x)₁` has the natural `G_x`-action" is read as the restricted action only
    (`NaturalRep.liftMulAction`): `U(x)₁` need not be connected in `X¹`, so it is not a natural
    representation of `X¹`. The regularity of `|X¹|` is not needed on this route.

Found while formalizing §7.4 and Appendix 7.5.2 (2026-11-07).

90. **Theorem 7.3 needs `|X|` normal: paracompact and Hausdorff** *(Theorem 7.3, p. 250)*. "Due to
    paracompactness … a partition of unity" needs `|X|` normal; Definition 7.15 does not require
    Hausdorff, which comes from Lemma 7.6 (`lemma_7_6`). Index types are arbitrary; the second part
    gives the conclusions of Definition 7.16 except sc-smoothness, the invariance read as
    `β_λ(s φ) = β_λ(t φ)` (`theorem_7_3`, `orbitPullback`, `orbitPullback_isSubordinate`).
91. **Definition 7.16 and Remark 7.2** *(Definition 7.16, pp. 250–251; Remark 7.2, p. 251)*.
    `HasScPartitionsOfUnity`: for every saturated open cover indexed by a type in the universe of
    `X`, a subordinate partition of unity sc-smooth in the sense of Part I
    (`MPolyfold.IsScSmoothPartitionOfUnity`), with `supp` read as `tsupport`, (1) a saturated open
    neighbourhood meeting finitely many supports, (2) `β_λ(s φ) = β_λ(t φ)`. Remark 7.2 has no formal
    content; the sc-Hilbert case it mentions is Part I's
    `MPolyfold.admitsScPartitionsOfUnity_of_hilbert` (Corollary 7.3, item 95).
92. **Definition 7.17, Propositions 7.13, 7.14** *(pp. 251–252)* *(book 2021: the notation unchanged, proof of Proposition 7.5.10 (2), p. 343)*. Definition 7.17 is
    `IsProperSubset` and `HasPropernessProperty`. Proposition 7.13 is proved by the compactness of
    the preimage (`proposition_7_13`), Proposition 7.14 (1) through the closedness of the saturation
    (`isClosed_saturation_of_isProperSubset`, `proposition_7_14_one`). (2) is proved with only the
    paracompactness of `|X|` (`proposition_7_14_two`): a precise locally finite refinement
    (`precise_refinement_set`) replaces Lemma 2.7, no regularity is used, the representatives are
    chosen by `Quotient.out`, and any neighbourhood with the properness property serves
    (`exists_hasPropernessProperty_subset`, `isProperSubset_iUnion_of_locallyFinite`). In the proof of
    (2), "`cl_X(U_{x_{z_i}})`" stands for `cl_X(U(x_{z_i}))` (possible misprint, notation).
93. **Lemma 7.10: the cover of `X`, and a stronger statement** *(Lemma 7.10, p. 255)*. "`V(x)` admits
    the natural `G_x`-action" is a natural representation with `V(x) = R.U`. The partition of unity
    "of `V(x)`" is taken for a cover of `X`, since the hypothesis is that `X`, not `V(x)`, admits
    sc-smooth partitions of unity: the text's cover of `V(x)` is completed by `X ∖ cl U(x)` and
    coarsened to the two sets `U(x)` and `X ∖ supp β`. The conclusion adds `tsupport f ⊆ cl U(x)`,
    which the proof gives and Theorem 7.4 needs (item 94); the hypothesis that `U(x)` contains `x` is
    not used and is omitted (stronger); the paracompactness of `|X|` and the continuity of `β` are
    kept but not used (`lemma_7_10`, `_hpara`, `_hβ`).
94. **The proof of Theorem 7.4** *(pp. 255–256)* *(book 2021: both points unchanged, Lemma 7.6.5 and the proof of Theorem 7.5.7, pp. 346–347)*. Properties (1)–(3) are
    `exists_invariant_nhds_of_isOpen`; (4) follows from (1) and is not a further choice
    (`mem_of_π_mem_image_of_invariant`, `saturation_diff_inter_eq_empty`). Four points, all of which
    stand: Lemma 7.10 is applied with `W(x_i)` in the role of `V(x)` and `U''_i` in the role of
    `U(x)`, where the text's "approximate `(β_i ∘ π)|V(x_i)` using Lemma 7.10" reads as `V(x_i)` in the
    role of `V(x)` (possible misprint); the continuity of the cut-off `(β_i ∘ π)|V(x_i)` extended by
    `0` uses (4); "the sum of all `h_i` is locally finite" needs `supp f_i ⊆ π⁻¹(cl V'_i)`, which the
    lemma as stated does not give and its proof does (item 93); the sc-smoothness of `h_i` uses that
    saturations of proper sets are closed (`isClosed_saturation_of_isProperSubset`). "We average"
    needs no second average, `f_i` being invariant; the extension to the saturation is
    `orbitExtension`. The normalization `(h_i/h)` and the return from the index set of the refinement
    to `Λ`, which the text leaves implicit, are replaced by Mathlib's
    `BumpCovering.exists_isSubordinate_of_prop`, as in Part I's Theorem 5.12
    (`admitsScPartitionsOfUnity_of_approx`), with the text's construction as the Urysohn input
    (`exists_isScSmoothMap_orbit_urysohn`). The theorem is `theorem_7_4`.
95. **Theorem 7.6 (= Theorem 7.4) and Corollary 7.3** *(p. 255; Corollary 7.3, p. 256)*.
    `theorem_7_6` is `theorem_7_4` (the text restates the theorem in Appendix 7.5.2). In Corollary
    7.3, "an atlas consisting of charts whose local models have Hilbert spaces `E₀`" is existential,
    one chart per point, as in Part I; "Hilbert" is `‖v‖² = b(v, v)` for a continuous bilinear `b`.
    The theorem of Godefroy–Troyanski–Whitfield–Zizler (Part I's Theorem 5.14) is an explicit
    hypothesis, `GodefroyTroyanskiWhitfieldZizlerStatement`, as in Part I (gap G.53); the text's
    references Proposition 5.6, Theorem 5.12 and Corollary 5.2 are the ingredients of
    `MPolyfold.admitsScPartitionsOfUnity_of_hilbert`. The corollary is `corollary_7_3`.
96. **Unbalanced parentheses** *(pp. 230, 248, 256)* *(book 2021: all unchanged, checked on the printed pages: Lemma 7.1.11, p. 292; (7.19), p. 327; proof of Theorem 7.5.7, p. 347)*. "`t : s⁻¹(cl_X(U(x₀)) → X`" in the statement
    and the proof of Lemma 7.1 (p. 230), "`s⁻¹(cl_{X₁}(W(x)) → X₁`" twice in the proof of
    Proposition 7.11, display (7.5) (p. 248), and "`t : s⁻¹(cl_X(V(x)) → X`" in property (2) of the
    proof of Theorem 7.4 (p. 256) each lack a closing parenthesis (possible misprints). The
    statement of Definition 7.3 (3) has the balanced form.

Found while checking that the hypotheses can hold (`NonVacuity.lean` and the witnesses of the other
files, 2026-11-07; not in the text).

100. **Action ep-groupoids** (`Examples.actionEpGroupoid`). A finite discrete group `K` acting on an
     M-polyfold `U` by sc-smooth maps gives an ep-groupoid with morphisms `K × U`, `s(g, y) = y`,
     `t(g, y) = g · y`. Its isotropy is the stabilizer (`Examples.isotropyEquivStabilizer`), its
     orbit space the orbit space of the action (`Examples.actionOrbitHomeomorph`); every subset is
     proper iff closed (`Examples.isProperSubset_action_iff`), every open set has the properness
     property (`Examples.hasPropernessProperty_action`), and the orbit space is paracompact for second
     countable `U` (`Examples.hasParacompactOrbitSpace_action`).
101. **An effective ep-groupoid with non-trivial isotropy** (`Examples.reflectionEpGroupoid`). `ℤˣ`
     acting on `ℝ` by `x ↦ ±x`: effective (`Examples.isEffective_reflection_nonvacuous`) with
     `G_0 ≅ ℤˣ` (`Examples.reflectionIsotropyZeroEquiv`), so Definition 7.11 is not vacuous;
     `X_reg = {x ≠ 0}` (`Examples.regularSet_reflection`), `T_0 = 1`
     (`Examples.trivialSubgroup_reflection`); tame (`Examples.isTame_reflection`) with paracompact
     orbit space (`Examples.hasParacompactOrbitSpace_reflection`).
102. **A non-effective ep-groupoid** (`Examples.trivialZ3EpGroupoid`). `ℤ/3` acting trivially on
     `ℝ`: `G_x ≅ ℤ/3` (`Examples.trivialZ3IsotropyEquiv`), `T_x = G_x`
     (`Examples.trivialSubgroup_trivialZ3`, `Examples.trivialZ3TrivialSubgroupEquiv`), not effective
     (`Examples.not_isEffective_trivialZ3`), `X_reg = ∅` (`Examples.regularSet_trivialZ3`).
103. **The properness of Definition 7.3 (3) cannot be asked of every neighbourhood**
     (`Examples.pairEpGroupoid`). The pair groupoid of `ℤ` (one morphism between any two integers,
     discrete topologies) is an ep-groupoid (`Examples.pair_isProperMap`), but `t : s⁻¹(cl V) → X` is
     not proper for `V = ℤ` (`Examples.pair_not_isProperMap_univ`, `Examples.pair_exists_not_isProperMap`),
     so the reading "for every open `V ∋ x`" fails (`Examples.pair_not_forall_isProperMap`); every open
     `V' ⊆ V(x)` works (item 3).
104. **The counterexample to the remark after Definition 7.7** *(book 2021: corrected, the remark after Definition 7.1.7, p. 291, assumes continuity on morphisms, which this functor lacks)* (`Examples.remarkFunctor`). On the
     ep-groupoid of item 102, the functor of item 9 is a functor
     (`Examples.remarkFunctor_obj`, `Examples.remarkFunctor_mor`), sc-smooth on objects
     (`Examples.isScSmoothMap_remarkFunctor_obj`), not continuous and not sc-smooth on morphisms
     (`Examples.not_continuous_remarkFunctor_mor`, `Examples.not_isScSmoothMap_remarkFunctor_mor`),
     and not an `EpFunctor` (`Examples.not_exists_epFunctor_remarkFunctor`).
105. **The trivial ep-groupoid of an M-polyfold** (`EpGroupoid.lean`, `SubGroupoid.lean`,
     `PartitionsOfUnity.lean`, `LocalDiffeo.lean`). Every M-polyfold `P` gives the ep-groupoid
     `trivial P` with only identities: tame for tame `P` (`isTame_trivial`, `isTame_trivial_rn`),
     effective (`isEffective_trivial`), `X_reg = X` (`regularSet_trivial`), every closed set proper
     (`isProperSubset_trivial`, `hasPropernessProperty_trivial`), `|X| ≅ X`
     (`trivialOrbitHomeomorph`), paracompact orbit space (`hasParacompactOrbitSpace_trivial`), with
     natural representations (`trivialNaturalRep`, `actsTrivially_trivial`, `trivialNaturalRepFinite`)
     and ep-subgroupoids (`isEpSubgroupoid_trivial`, `isEpSubgroupoid_of_isOpen`,
     `isEpSubgroupoid_saturation`). On `ℝⁿ` it satisfies the hypotheses of Theorems 7.4, 7.6 and of
     Corollary 7.3 (`theorem_7_4_hypotheses_rn`, `hasScPartitionsOfUnity_trivial_rn_of_theorem_7_4`,
     `corollary_7_3_hypotheses_rn`, `rnPolyfold_admitsScPartitionsOfUnity`,
     `rnPolyfold_one_hilbert_hypothesis`).
106. **Hypotheses check (PLAN II.5): every hypothesis that quantifies over charts or
     neighbourhoods is satisfiable** *(2026-11-07)*. (1) Tameness (Definitions 7.6, Proposition
     7.11) is existential, a tame atlas (`MPolyfold.IsTame`), transported to `𝐗` by item 7; "every
     chart is modelled on a tame retract" is unsatisfiable by the construction of Chapter 3, item 190
     (a `[0, ∞)` factor with a constant retraction); witness `isTame_trivial_rn`,
     `Examples.isTame_reflection`. (2) The Hilbert atlas of Corollary 7.3 is
     existential, one chart per point; "every compatible chart has a Hilbert `E₀`" would be
     unsatisfiable, since `(φ, 0)` into `E ⊕ X'`, with `X'` an sc-Banach space whose level `0` is
     `c₀`, is compatible with `φ`; witness `rnPolyfold_one_hilbert_hypothesis`, `corollary_7_3_hypotheses_rn`.
     (3) Sc-smooth partitions of unity of the object M-polyfold (Theorems 7.4, 7.6, Lemma 7.10):
     witness `rnPolyfold_admitsScPartitionsOfUnity`, `theorem_7_4_hypotheses_rn`. (4) Properness
     (Definition 7.3 (3)) is existential per point; the universal form fails (item 103); every
     smaller open neighbourhood works (`HasPropernessProperty.mono`). (5) Effectiveness (Definition
     7.11, Lemma 7.3, Proposition 7.8) is satisfiable non-vacuously (item 101) and vacuously (item
     105), and fails for item 102. (6) "`U(x)` equipped with the natural `G_x`-action" (Proposition
     7.6, Lemmas 7.4, 7.10, Theorem 7.4) is a `NaturalRep` datum, which exists inside every
     neighbourhood (`theorem_7_1`); no hypothesis "for every `U(x)` with the natural action" is
     made. (7) `[T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]` of Propositions 7.9, 7.10 are
     satisfiable (item 60). The other hypotheses (`HasParacompactOrbitSpace`,
     `SecondCountableTopology Obj`, `SecondCountableTopology X.OrbitSpace`, component compact `K`)
     hold for the trivial ep-groupoid of `ℝⁿ` (`hasParacompactOrbitSpace_trivial`,
     `trivialOrbitHomeomorph`). No hypothesis of the form "for all compatible charts" is made in
     Chapter 7.
107. **`𝐗^R` need not be Hausdorff; Propositions 7.9 and 7.10 need the hypothesis** *(book 2021: corrected, Theorem 7.2.14, p. 318, assumes `T_R` Hausdorff; Theorem 7.2.22, p. 323; Zhou's example, Appendix 7.6.3, p. 348, is of the same kind)*
     (`Examples.exists_not_t2Space_reducedMor`, `ReducedNotHausdorff.lean`; Propositions 7.9, 7.10,
     pp. 242–244). `O` is the sc-retract of Part I's Remark 4.3 example (`RemarkFourThree.fam`), a
     point over each `t ≤ 0` and a line over each `t > 0`, with its one chart; `ℤ/2 = ℤˣ` acts by
     `(t, z) ↦ (t, ±z)`, the restriction of an sc-operator (`JumpingRetract.isScSmoothMap_smul`),
     and `JumpingRetract.X = ℤ/2 ⋉ O` is `actionEpGroupoid`. Over `t < 0` both elements act
     trivially, so `(−1, (t, 0)) ∈ 𝐗^T`; at `(0, 0)` the points `(1/(k+1), (1/(k+1)) e_{n_k}) → 0`
     of `O` are moved by `−1`, so `(−1, (0, 0)) ∉ 𝐗^T` (`not_mem_nonEffectivePart`). The classes of
     `(±1, (−1/(n+1), 0))` coincide and converge to both `[(−1, 0)] ≠ [(1, 0)]`:
     `JumpingRetract.not_t2Space_reducedMor`. So, as we read them, Propositions 7.9 and 7.10 need
     `𝐗^R` Hausdorff, which the text does not state; with `𝐗^R` Hausdorff and paracompact the
     project's statements give the text's (`RoundTrip/Items/V7_40.lean`, `A_to_B_of_hyp`). This is
     the splicing example of PLAN II.6, 2; the round-trip audit proved it (`RoundTrip/Items/V7_40.lean`,
     namespace `NotB`; its blind formalizer of V7.39 found the example independently), and it was
     moved into the project unchanged on 2026-11-07. It settles the Hausdorff half of gap G.71.

Not formalized (2026-11-07).

110. **`Tφ` as an sc-isomorphism** *(p. 227, Definition 7.4)*. `tangentMor` is defined, but its
     properties (well defined, `= Tφ̂(s(φ))`, bijective, a bounded linear isomorphism on level `0` for
     `φ ∈ 𝐗₁`, an sc-operator for smooth `φ`) are not formalized; the linearity needs the linear
     structure of the tangent spaces (gap G.7). Not used in Chapter 7; deferred to Chapter 8
     (gap G.70).
111. **`𝐗^R` Hausdorff and paracompact** *(Propositions 7.9, 7.10, pp. 242–244)* *(book 2021: corrected, Theorem 7.2.14, p. 318, assumes `T_R` Hausdorff, and Proposition 7.2.12, p. 317, proves `T_R` paracompact; as we read it, its Lemma 7.2.11 (3) needs `T_R` Hausdorff)*. Taken as
     hypotheses (item 56); discharged for effective `X` and for the trivial ep-groupoid (item 60).
     Hausdorffness does not hold in general (item 107, formalized 2026-11-07 after the round-trip
     audit), so this half of the gap is settled negatively. Not formalized: whether `𝐗^R` is
     paracompact when it is Hausdorff, and whether Hausdorff with `𝐗` second countable suffices for
     paracompactness (gap G.71).
112. **The filtration of `|X|`** *(p. 228)*. `|X_k|` is `orbitLevel k`; the set `|X_∞|` and the
     identity `|X_∞| = ⋂_k |X_k|` are not stated (gap G.72). The density of `X_∞` in `X_k` is item
     116 (gap G.73).
113. **Not formalized, without a gap** *(pp. 227, 249, 251)*. The comparison with the classical
     properness of `(s, t)` (p. 227) and Remark 7.2 (p. 251) have no formal content; Remark 7.1 (p.
     249) has none. "It is presently not known whether the property (5) is a consequence of the
     properties (1)–(4)" (p. 249) is an open question of the text; unlike Part I's open question
     after Proposition 4.15 (gap G.34) it is not given a gap, since nothing in the chapter depends on
     it.
114. **Gaps of Part I taken up in Chapter 7.** G.15 (Lemma 2.7 and Proposition 2.17 of Part I,
     closed locally finite refinements): now formalized (`lemma_2_56`, `proposition_2_57`,
     `michael_tfae`; item 75). G.56, its first fact (an M-polyfold is locally path connected): now
     formalized (`MPolyfold.locallyPathConnectedSpace`; item 21); the second fact (smooth points in one
     path component are joined by an sc⁺-smooth path) is not. G.53 (Theorem 5.14 of Part I) remains
     an explicit hypothesis; it holds for finite-dimensional spaces
     (`godefroyTroyanskiWhitfieldZizlerStatement_of_finiteDimensional`).
115. **Chapter 5, item 145 and Proposition 7.11.** `MPolyfold.IsTame.levelOne` (item 81) proves the
     tameness of the index lift of a tame M-polyfold, and with it the tameness of the lifted chart
     retraction `r¹` with respect to every presentation of `C¹`; the tame variants for `f¹`
     (`IsScFredholmSectionTame` for the shifted section) remain not stated. Recorded at the end of
     Chapter 5, item 145.
116. **The density of `X_∞` in `X_k`** *(p. 227: "The set `X∞` is dense in every space `Xk`")* *(book 2021: unchanged, after Definition 7.1.4, p. 289)*. The
     text states it without proof. Part I proves the density only for sc-Banach spaces
     (`ScBanach.denseRange_incl`, `denseRange_inclK`), and its text does not state it for
     M-polyfolds or retracts. For a retract `O = r(U)` it follows from the continuity of `r` on level
     `k` and the density of `U_∞` in `U_k`; for `U` open in a partial quadrant `C` this needs `C ∩
     E_∞` dense in `C ∩ E_k`. Not formalized (gap G.73; Chapter 7 uses the filtration, never the
     density). Found by the round-trip audit (2026-11-07): V7.6's blind statement asserts the
     density, and `A_to_B_of_density` (`RoundTrip/Items/V7_6.lean`) shows it is the only
     difference. Before the audit, item 112 and V7.6 said the density was Part I's; that was
     an oversight of this report, corrected here.

## Chapter 8 (Bundles and covering functors; Lean `Polyfold/Chapter8/`)

*Numbering.* The items of this section are numbered in blocks, one block per part of the chapter, so
that agents working at the same time do not collide; the gaps in the numbering are unused numbers,
not deleted items. 1–19: §8.1 up to Proposition 8.1, the tangent ep-groupoid, the tangent functor
and natural transformations (Theorems 8.1–8.3, Lemmas 8.1–8.8, Remark 8.1, Definition 8.1,
Proposition 8.1; `Chapter8/Basic.lean`, `TangentLocal.lean`, `TangentEp.lean`, `TangentTame.lean`,
`NatTrans.lean`); 20–29: Theorem 8.4, the orbit space of the tangent (`TangentOrbit.lean`); 30–49:
§8.3, strong bundles over ep-groupoids (Definitions 8.4–8.7; `StrongBundleMap.lean`,
`EpStrongBundle.lean`); 50–69: §8.4 up to Theorem 8.6, proper covering functors and geometric lifts
(Definitions 8.8, 8.9, Proposition 8.2, Theorem 8.5, Remark 8.2, Proposition 8.3, Theorem 8.6;
`ProperCovering.lean`, `ProperCoveringLocal.lean`, `SigmaPolyfold.lean`, `GeometricLift.lean`);
70–79: Definition 8.10 and Appendix 8.5 (Lemmas 8.9–8.11, Proposition 8.4, §8.5.2;
`ProperCovering.lean`, `EpStrongBundle.lean`); 100–109: witnesses and the check of the hypotheses
(`NonVacuity.lean`, `NonVacuityBundle.lean` and the witnesses of the other files); 110–119: not
formalized, and the gaps of Part I and Chapter 7 taken up here. Part II has no 2014 preprint:
statement numbers and pages are the 2017 text's (pp. 257–289); Part I results are cited by their
2017 numbers. The comparison items are `Exposition/verification/ch08.md` (V8.1–V8.43).

Found while formalizing §8.1 up to Proposition 8.1 (2026-11-07).

1. **The tangent data; the composition (8.5) is defined by choice** *((8.1)–(8.9), pp. 257–258)* *(book 2021: corrected, (8.5) now writes `T_{ψ∘φ}𝐗`, p. 358)*.
   The objects and morphisms of `T(X, 𝐗)` are Part I's tangent M-polyfolds `TX`, `T𝐗`
   (`MPolyfold.TangentSpace`); `s_T = Ts`, `t_T = Tt`, `u_T = Tu`, `ι_T = Tι` are `tSrc`, `tTgt`,
   `tUnit`, `tInv`, and `p` is `tBase`. The composition is total, with the junk value `h` off
   composable pairs, as Chapter 7's `GroupoidStr.comp`; on a composable pair, `Ts(k) = Tt(h)`, it is
   chosen as a vector over `p(k) ∘ p(h)` with `Ts(k ∘ h) = Ts(h)` (`tComp`, `tComp_spec`,
   `tBase_tComp`, `tSrc_tComp`). The choice is unique: `s` being a local sc-diffeomorphism, `Ts` is
   injective on every fibre `T_φ𝐗` and maps it onto `T_{s(φ)}X` (`tangent_ext`, `exists_tSrc_eq`),
   which is what the text's `Ts(ψ ∘ φ)⁻¹` in (8.5) uses; `tComp_eq` is (8.5) in this form. The units
   are `Tu`, and (8.8), `u_T(a) = (1_x, Ts(1_x)⁻¹a)`, is `tUnit_eq`. (8.5) writes `T_{φ∘ψ}𝐗` for
   `T_{ψ∘φ}𝐗` (possible misprint).

2. **Universes** *(Theorems 8.1, 8.3, 8.6; the functorial picture, p. 271)*. Part I's `TangentSpace`
   of `X : Type u` lives in `Type (max u 1)`; so do `TX`, `T𝐗` and `|TX|`, and the tangent functor
   of Theorem 8.3 is `EP.{max u 1} ⥤ EP.{max u 1}` (`tangentFunctor`, `theorem_8_3`). An
   `EpGroupoid` has its objects and morphisms in one universe, so from the functorial picture on,
   the total space `W` of a strong bundle lives in the universe of the objects and morphisms of `X`
   (item 33). Definition 8.9 takes `D` and `G` in `Type` and `Diff_sc` with the M-polyfolds of one
   universe, so Theorem 8.6 is stated for ep-groupoids whose objects and morphisms are in `Type`
   (item 60). These restrictions come from the formalization, not from the text.

3. **Tangents of maps defined on open sets** *(used in (8.5), (8.8) and in the proofs of Lemmas 8.1,
   8.2, 8.4, 8.6, 8.7, pp. 258–263)*. The proofs differentiate maps defined only on open sets, such
   as `(s|U(ψ))⁻¹` and the map `α` of Lemma 8.2, while Part I defines `Tf` only for globally
   sc-smooth `f`. `TU` for an open `U` is read as `p⁻¹(U)` (`tangentPreimage`,
   `isOpen_tangentPreimage`), which is the tangent of the open sub-M-polyfold `U`
   (`isScDiffeoOn_tangentMap_subtypeVal`, for `U ≠ ∅`). The tangent of a map sc-smooth on `U` is
   built from the charts, as Part I builds `Tf` (`tangentMapOn`), with the chain rule
   (`tangentMapOn_comp`), agreement with Part I's tangent for globally sc-smooth maps
   (`tangentMapOn_eq_tangentMap`) and sc-smoothness (`tangentMapOn_isScSmoothOn`). The tangent of an
   sc-diffeomorphism between open sets is one (`IsScDiffeoOn.tangentMap`), and the tangent of a
   local sc-diffeomorphism is a local sc-diffeomorphism, bijective on the fibres and surjective if
   the map is (`IsLocalScDiffeo.tangentMap`, `IsLocalScDiffeo.bijOn_tangentFiber`,
   `IsLocalScDiffeo.surjective_tangentMap`); this is Lemma 8.6's "by construction". Off `p⁻¹(U)` the
   tangent takes a junk value in `TY`, which is nonempty because a nonempty M-polyfold has points on
   level `1` (`MPolyfold.exists_mem_levelSet_one`, `nonempty_tangentSpace`); the text needs none of
   this. Not in the text (V8.2).

4. **Fibre injectivity in place of differentiating identities** *(Lemmas 8.3–8.5, Theorem 8.2,
   Proposition 8.1, pp. 260–268)*. Two vectors of `T𝐗` with the same base point and the same image
   under `Ts` are equal (`tangent_ext`). Associativity (Lemma 8.3), the unit and inverse laws
   (Lemmas 8.4, 8.5), the compatibility of `TΦ` with the composition (Theorem 8.2) and the
   naturality of `Tτ` (Proposition 8.1) are proved this way: the base points are computed in `𝐗` and
   the values of `Ts` by Part I's chain rule for `s ∘ u = id`, `s ∘ ι = t`, `s ∘ 𝚽 = Φ ∘ s` and `s ∘
   τ = Φ`, instead of differentiating the identities as the text does. The only differentiation that
   remains is `t_T(Ψ ∘ Φ) = t_T(Ψ)` in Lemma 8.2 (item 6). The statements are the text's.

5. **Lemma 8.1 in the form its proof uses** *(Lemma 8.1, p. 259)* *(book 2021: corrected, proof of Lemma 8.1.2, p. 359, now `s|U(ψ ∘ φ)`)*. The statement identifies `T(𝐗 ₛ×ₜ
   𝐗)` with `T𝐗 _{Ts}×_{Tt} T𝐗` and the composition of `T𝐗` with `Tm` on it. This identification of
   the tangent of the fibred product with the fibred product of the tangents is not formalized (gap
   G.75, item 111). `lemma_8_1` is the form of the proof: for a sheet `s : W → V` with inverse `σ`,
   the text's `F(φ') = (s|U(ψ))⁻¹(t(φ'))` is `σ(t(φ'))`, `g(φ') = m(σ(t φ'), φ')` is sc-smooth on
   `t⁻¹(V)` (Chapter 7's sheet form, `isScSmoothCompSheet`), `k = Tσ(Tt(h))`
   (`tangentMapOn_srcInv_tSrc`) and `k ∘ h = Tg(h)` (`tComp_eq_tangentMapOn`). The proof writes
   `s|U(φ ∘ ψ)` for `s|U(ψ ∘ φ)` (possible misprint).

6. **Lemmas 8.2 and 8.4: the proofs** *(pp. 259–261)* *(book 2021: proof of Lemma 8.1.3, p. 360: "`= =`" and the missing map `s` unchanged; `T t)φ)(h)` corrected)*. In Lemma 8.2 the target is computed as in the
   text: `k ∘ h = Tg(h)` on a sheet (item 5), and `t ∘ g = t ∘ σ ∘ t` on `t⁻¹(V)` (the text's `α ∘ s
   = t ∘ (s|U(ψ))⁻¹ ∘ t`), so `Tt(k ∘ h) = T(t ∘ σ ∘ t)(h) = Tt(k)` (`tTgt_tangentMapOn`,
   `lemma_8_2`). In Lemma 8.4, `Tt(1_q) = q` is the chain rule for `t ∘ u = id`, rather than the
   text's `t ∘ (s|U(1_x))⁻¹ = id` near `x` (`tTgt_tUnit`, `lemma_8_4`). Possible misprints in the
   proof of Lemma 8.2: "`= =`", "`: U(ψ ∘ φ) → U(x)`" without the map `s`, and "`T t)φ)(h)`" with an
   unbalanced parenthesis.

7. **Lemmas 8.6 and 8.7** *(pp. 262–263)* *(book 2021: corrected, proof of Lemma 8.1.8, p. 363, now `Tt(φ_k)(h_k)`)*. Lemma 8.6: `s_T`, `t_T` are local sc-diffeomorphisms "by
   construction" (item 3), surjective since `s`, `t` are (`isLocalScDiffeo_tSrc`, `surjective_tSrc`
   and the same for `t`); condition (4) is proved in Chapter 7's sheet form
   (`isScSmoothCompSheet_tangent`: near a point, `Ψ ↦ σ_T(t_T Ψ) ∘ Ψ` is `Tg` for a sheet of `s`)
   and from it on the fibred product (`isScSmoothComp_tangent`, through `isScSmoothComp_iff_sheet`),
   not through "`m_{T𝐗}` is precisely `Tm`" (item 111). Lemma 8.7 (`lemma_8_7`): `V' = p⁻¹(V)` for
   `V` as in Definition 7.3 (3) for `X`; the step "`φ_k → φ` in `𝐗¹`" is not needed, since
   convergence in `𝐗` puts `φ_k` in a sheet `U(φ)` of `t`, on `p⁻¹(U(φ))` the inverse of `Tt` is
   continuous, and so `(φ_k, h_k)` converges; properness is checked by the sequential criterion
   (`TX`, `T𝐗` are metrizable). The proof writes `t(φ_k, h_k) = Ts(φ_k)(h_k)` for `Tt(φ_k)(h_k)`
   (possible misprint).

8. **Lemma 8.8: `Tr` is a tame retraction** *(Lemma 8.8, p. 263)* *(book 2021: unchanged, Lemma 8.1.9, p. 364)*. The proof asserts without
   argument that `Tr` is a tame retraction for a tame retraction `r`; Part I does not state it. It
   is proved from Part I's Definition 2.17 (`ScRetraction.IsTame.tangentRetraction`,
   `IsTameRetract.tangent`, `MPolyfold.IsTame.tangent`, `lemma_8_8`). For the presentation
   `ScIso.tangentPres` of `TC = C¹ ⊕ E`, whose `ℝⁿ`-coordinates at `(a, b)` are those of `a`:
   condition (1) is condition (1) for `r` at `a`, since `d_{TC}(a, b) = d_C(a)`
   (`degIndex_tangentSet`) and `Tr(a, b) = (r(a), Dr(a)b)`; for condition (2) at a smooth point `(a,
   b)`, with `A` the sc-complement of `T_aO` given by the tameness of `r`, the complement is `A' =
   (A ∩ E₁) ⊕ A`. The proof uses three facts about `L = D(Tr)(a, b)`: `L` is a projection (`Tr ∘ Tr
   = Tr`), its first row is `(Dr(a), 0)` (`ScRetraction.scDeriv_tangentRetraction_fst`), and `L(0,
   l) = (0, Dr(a)l)` (`ScRetraction.scDeriv_tangentRetraction_inr`); the second derivative of `r`,
   which enters `L`, is not needed. Tameness for every presentation follows from the one
   presentation by Part I's Lemma 1.1 (`ScRetraction.IsTameWith.isTame`). The text's "tame chart" is
   read as a chart modelled on a tame retract (`MPolyfold.IsTame.exists_chart`).

9. **Theorem 8.1** *(Theorem 8.1, p. 258; proof pp. 263–264)*. `theorem_8_1` records that
   `tangentEpGroupoid` has the M-polyfolds `TX`, `T𝐗` and the text's structure maps, with the base
   point and the source of a composite; the conditions of Definition 7.3 are Lemmas 8.2–8.7 (items
   4–7), and the tameness sentence is `theorem_8_1_tame` (Lemma 8.8, item 8). `(X, 𝐗)¹` is Chapter
   7's `liftOne`, and the projection `(p, 𝐩)` is the sc-smooth functor `tangentProjFunctor`; its
   compatibility with the composition ("This is obvious") is `tBase_tComp`.

10. **Remark 8.1: `Tφ` labelled by `φ`; linearity not formalized** *(Remark 8.1, pp. 264–265)* *(book 2021: unchanged, Remark 8.1.10, pp. 364–365: `T_yY` twice, and the linearization "at `φ`")*. `Tφ`
    is Chapter 7's `tangentMor` (Definition 7.4, `Tt ∘ (Ts|T_φ𝐗)⁻¹`); it is well defined, `Tφ(Ts(h))
    = Tt(h)` (`tangentMor_tSrc`), and functorial, `T(ψ ∘ φ) = Tψ ∘ Tφ` (`tangentMor_comp`). In `G(φ,
    h) = (Tφ, Ts(h))` the first entry is read as `Tφ` labelled by `φ`: as a bare map `G` need not be
    injective, since distinct morphisms can have the same `Tφ` (for `ℤ/3` acting trivially on `ℝ`,
    Chapter 7, item 102, the three morphisms at a point all have `Tφ = id`; not formalized). With
    the label, `G` (`remarkG`) is a bijection onto the pairs `(φ, a)`, `φ ∈ 𝐗₁`, `a ∈ T_{s(φ)}X`,
    compatible with the compositions (`remark_8_1`). Not formalized: that `Tφ` is a linear
    isomorphism and is the tangent of `φ̂ = t ∘ (s|U(φ))⁻¹` at `x` (item 112), the M-polyfold
    structure transported along `G`, and the triples `(a, Tφ, b)` (item 113). Possible misprints:
    "`Tφ : T_xX → T_yY`" for `T_yX`, twice on p. 264 (and once in Definition 8.2, item 110), and
    "the linearization of `t ∘ (s|U(φ))⁻¹` at `φ`" (p. 265) for "at `x`", the point where this map
    is defined and where p. 264 takes its tangent.

11. **Theorems 8.2 and 8.3** *(pp. 265–266)*. `EpFunctor.tangent` is `(TΦ, T𝚽)`; its compatibility
    with sources, targets and the composition is proved by fibre injectivity (item 4), and the
    units, which the proof does not check, are proved as well (`theorem_8_2`). Theorem 8.3 is
    `EP.tangent` and the functor `tangentFunctor` (item 2), whose functor laws are Part I's chain
    rule (`MPolyfold.tangentMap_comp`, `MPolyfold.tangentMap_id`); its tameness sentence is
    `theorem_8_3_tame`.

12. **Definition 8.1 and "`≃` is an equivalence relation"** *(Definition 8.1, p. 266; p. 267)* *(book 2021: unchanged, Definition 8.1.13, p. 367)*.
    `EpNatTrans` (an sc-smooth `τ : X → 𝐘` with `τ(x) : F(x) → G(x)` and the naturality square) and
    `EpFunctor.NaturallyEquivalent` are the text's. The claim that `≃` is an equivalence relation,
    stated without proof, is `naturallyEquivalent_equivalence` (`EpNatTrans.refl`,
    `EpNatTrans.symm`, `EpNatTrans.trans`). The one point that is not groupoid algebra is the
    sc-smoothness of `x ↦ τ'(x) ∘ τ(x)`, from Chapter 7's sheet form of Definition 7.3 (4)
    (`EpNatTrans.isScSmoothMap_comp_app`): near `x₀`, `τ'(x) = σ(t τ(x))` for a sheet of `s` with
    inverse `σ`, so `τ'(x) ∘ τ(x) = m(σ(t ψ), ψ)` at `ψ = τ(x)`. The inverse `x ↦ τ(x)⁻¹` is
    sc-smooth since `ι` is. Not in the text: whiskering (`EpNatTrans.whiskerLeft`,
    `EpNatTrans.whiskerRight`, `NaturallyEquivalent.comp_left`, `NaturallyEquivalent.comp_right`).

13. **Proposition 8.1** *(pp. 267–268)* *(book 2021: unchanged, proof of Proposition 8.1.14, pp. 367–368)*. `EpNatTrans.tangent`, `proposition_8_1`: `Tτ` is sc-smooth
    `TX → T𝐘`, `Tτ(a)` is a morphism `TΦ(a) → TΨ(a)` by the chain rule for `s ∘ τ = Φ`, `t ∘ τ = Ψ`,
    and the naturality follows from fibre injectivity (item 4) instead of differentiating the
    naturality square. Possible misprints in the proof: "`Tτ(x₀(h))`" for `Tτ(x₀)(h)` (p. 267), and
    the lower arrow of the last diagram labelled `Tτ(x₀)h` for `Tτ(x₀')h'` (p. 268; possibly an
    artefact of the text extraction).

Found while formalizing Theorem 8.4 (2026-11-07).

20. **Theorem 8.4 by metrizability; the conclusion is stronger** *(Theorem 8.4 and its proof, p.
    268)*. The text covers `|X¹|` by the sets `|U(x_z)¹|`, takes a subordinate locally finite closed
    refinement (Part I's Lemma 2.7), shows that the preimages `Ã_z ⊆ |TX|` are closed and
    paracompact, and concludes with the regularity of `|TX|` and Part I's Proposition 2.17. The
    proof here follows that of Proposition 7.12 (Chapter 7, item 83): `|X¹|` is metrizable, every
    point of it has the open neighbourhood `|U(x)₁|`, whose preimage under `|p| : |TX| → |X¹|`
    (`tangentOrbitProj`, `continuous_tangentOrbitProj`) is `|TU(x)|`
    (`NaturalRep.image_tangentU_eq_preimage`) and is metrizable
    (`NaturalRep.metrizableSpace_image_tangentU`); Part I's `metrizableSpace_of_pullback` (Smirnov's
    theorem) then makes `|TX|` metrizable (`metrizableSpace_tangent_orbitSpace`), hence paracompact
    (`theorem_8_4`). The step shared with the text is the metrizability of `|TU(x_z)|`; neither the
    regularity of `|TX|` nor Proposition 2.17 is used.

21. **`TU(x)`, the action of `G_x`, and the open embedding** *(proof of Theorem 8.4, p. 268)* *(book 2021: proof of Theorem 8.1.15, pp. 368–369, unchanged; "parcompact" corrected in the statement, p. 368)*.
    `TU(x)` is read as `p⁻¹(U(x)) ⊆ TX` (`NaturalRep.tangentU`), and the bundle action of `G_x` as
    `g ↦ TΦ(g)`, the tangent maps of the natural action (`NaturalRep.tΦ`,
    `NaturalRep.isScDiffeoOn_tΦ`, `NaturalRep.tangentMulAction`), with `TΓ` (`NaturalRep.tΓ`). The
    sc-isomorphism of `TU(x)` with a local bundle model `TO → O¹` is not used: `TU(x)` is metrizable
    as a subspace of `TX` (Part I's Proposition 2.5 (3)), and `G_x\TU(x)` by the metric `ρ̂` of
    Lemma 7.4, repeated privately in `TangentOrbit.lean` for a finite group acting by homeomorphisms
    on a metrizable space, since Chapter 7's versions are private. The linearity of the action on
    the fibres is not formalized (gap G.7). That `G_x\TU(x) → |TX|` is an open embedding onto
    `|TU(x)|` is left implicit in the text and is proved (`NaturalRep.tangent_π_eq_iff`,
    `NaturalRep.isOpenEmbedding_tangentOrbitQuotientMap`,
    `NaturalRep.range_tangentOrbitQuotientMap`): a morphism `k : v → w` of `TX` between vectors over
    `U(x)` lies over `p(k) = Γ(g, s(p k))` (Theorem 7.1 (3)), and `k = TΓ(g)(v)` by fibre
    injectivity (item 4). `|TU(x)| = |p|⁻¹(|U(x)₁|)` uses the surjectivity of `Ts` on the fibres
    (`exists_tSrc_eq`). The statement writes "parcompact" for "paracompact" (possible misprint).

Found while formalizing §8.3 (2026-11-07).

30. **Strong bundle maps between strong bundles over M-polyfolds are a reading** *(used in
    Definitions 8.4–8.6, 8.10, pp. 270–285; Part I's Definitions 2.22, 2.25)*. Part I defines strong
    bundle maps only between local models (Definition 2.22) and treats the transition maps of a
    strong bundle atlas in Definition 2.25. The global notion used throughout §8.3 is
    `StrongBundle.IsStrongBundleMap B B' f Φ`: `P' ∘ Φ = f ∘ P`; `Φ` linear on the fibres
    (`fiberRestrict`); `Φ : Y[0] → Y'[0]` sc-smooth; `Φ(Y_{0,1}) ⊆ Y'_{0,1}` with `Y[1] → Y'[1]`
    sc-smooth. In the charts the last two conditions say that the local representatives `K[i] →
    K'[i]` are sc-smooth, as Definition 2.25 asks of transition maps. The preservation of the double
    filtration, part of Definition 2.22, is not assumed but follows
    (`IsStrongBundleMap.mapsTo_doubleLevel`), and so do the boundedness of the fibre maps
    (`IsStrongBundleMap.fiberMap`) and the sc-smoothness of the base map, `f = P' ∘ Φ ∘ 0`
    (`IsStrongBundleMap.isScSmoothMap_base`). A strong bundle isomorphism is a pair of inverse
    strong bundle maps (`StrongBundle.IsStrongBundleIso`). Strong bundle maps defined over open
    subsets of the base are not formalized (item 113).

31. **The pull-back along `s`** *(p. 270; Part I's Proposition 2.16)*. `𝐗 ₛ×_P W` is Part I's
    pull-back `pullbackSpace P X.src` with its strong bundle structure (`StrongBundle.pullback`);
    its paracompactness, which Part I's definition of a strong bundle requires, is an instance
    argument, supplied by `StrongBundle.paracompactSpace_pullback`. Added here: the atlas of the
    pull-back (`StrongBundle.pullback_atlas`), its universal property on `[0]`
    (`StrongBundle.isScSmoothOn_to_pullback_iff`, `StrongBundle.isScSmoothMap_pullbackPair`) and on
    `[1]` (`StrongBundle.pullbackProj'One`, `StrongBundle.isScSmoothMap_to_pullback_one`), and the
    fact that over a sheet of the local sc-diffeomorphism `s` the projection to `W` is an
    sc-diffeomorphism (`StrongBundle.isScDiffeoOn_pullbackProj'`,
    `StrongBundle.isLocalScDiffeo_pullbackProj'`); its inverse `w ↦ (σ(P w), w)` takes a junk value
    off `P⁻¹(V)`.

32. **Definition 8.4 and the fibre maps `μ(ψ, ·)`** *(Definition 8.4 and p. 271)*. `EpStrongBundle X
    B`: a structure map `μ` on Part I's pull-back, a strong bundle map covering `t` in the sense of
    item 30 (which contains `P ∘ μ = t ∘ π₁` and the fibrewise linearity), a surjective local
    sc-diffeomorphism of the `[0]`-M-polyfolds, with (2) and (3); the conditions `s(ψ) = P(w)` are
    carried by the points of the pull-back. The surjectivity in (1) follows from (2), `μ(1_x, w) =
    w`, and is kept as in the text. The claim after the definition that `μ(ψ, ·) : W_x → W_y` is a
    linear isomorphism is proved in the stronger form of a topological linear isomorphism with
    inverse `μ(ψ⁻¹, ·)` (`EpStrongBundle.fiberMorEquiv`, `μ_inv_μ`, `μ_μ_inv`); `μ` is continuous
    (`continuous_μ`).

33. **The functorial picture: "we can define the ep-groupoid"** *(pp. 271–272)* *(book 2021: unchanged, after Definition 8.3.1, p. 376)*. Asserted without
    proof; Definition 7.3 is proved for `(W, 𝐖)`, `𝐖 = 𝐗 ₛ×_P W` (`EpStrongBundle.toEpGroupoid`):
    (1) `s_𝐖` is the pull-back projection along the local sc-diffeomorphism `s` (item 31), and `t_𝐖
    = μ` is one by Definition 8.4 (1); (2) the units and inverses are sc-smooth by the universal
    property of the pull-back; (3) holds with `V = P⁻¹(V(P w))`, by sequences, from the properness
    of `X`, the continuity of `μ` and `w = μ(ψ⁻¹, μ(ψ, w))` (`exists_isProperMap_tgt`); (4) is
    proved in the sheet form, through a sheet of `s` and condition (4) for `X`
    (`isScSmoothCompSheet_toGroupoidStr`). The groupoid laws use Definition 8.4 (2), (3); the
    composition is total, with the junk value `(γ, w)` off composable pairs (`morComp`). `s_𝐖`,
    `t_𝐖` are strong bundle maps covering `s`, `t` (`isStrongBundleMap_src`,
    `isStrongBundleMap_tgt`), `(P, π₁)` is an sc-smooth functor (`projFunctor`), and `|P|` is
    continuous and surjective (`continuous_orbitMap_projFunctor`,
    `surjective_orbitMap_projFunctor`). From here on `W` lives in the universe of the objects and
    morphisms of `X` (item 2).

34. **Definitions 8.5, 8.6 and "these are identical notions"** *(pp. 273–274)*. Definition 8.5 is
    `EpStrongBundle.IsMap`. In Definition 8.6, "linear on the fibers", "covers `ϕ`" and "induces
    strong bundle maps `W → W'` and `𝐖 → 𝐖'`" are read together as two conditions
    `IsStrongBundleMap` (`IsStrongBundleFunctor`): on objects, for `P`, `P'`, covering `ϕ` on
    objects, which contains `P' ∘ Φ = ϕ ∘ P`; and on morphisms, for the pull-backs `𝐖 → 𝐗`, `𝐖' →
    𝐗'`, covering `ϕ` on morphisms. The text's claim that the two notions are identical, and that
    the functor is recovered from the strong bundle map, is proved: `isMap_iff_strongBundleFunctor`,
    with the unique functor `Φ(γ, w) = (ϕ(γ), Φ(w))` (`IsMap.liftFunctor`,
    `IsStrongBundleFunctor.eq_liftFunctor`). The `[1]`-smoothness of the lifted morphism map needs
    the universal property of the pull-back on level `[1]` (item 31) and the fibrewise linearity of
    maps of pull-backs (`isLinearMap_fiberRestrict_pullbackMap`).

35. **Definition 8.7: "the vector space `Γ(P, μ)`"** *(Definition 8.7, pp. 274–275)*. The section
    functors are `IsScSmoothSectionFunctor`, `IsScPlusSectionFunctor`, `IsScFredholmSectionFunctor`,
    with the sets `sectionFunctors`, `plusSectionFunctors`, `fredholmSectionFunctors`; (3) uses Part
    I's Definition 3.8 in its germ reading. "Vector space" and "subspace" are read as closure under
    Part I's fibrewise zero section, sums and constant multiples (`fiberZero_mem_sectionFunctors`,
    `sectionAdd_mem_sectionFunctors`, `sectionSmul_mem_sectionFunctors`, and the same for `Γ⁺`, with
    `plusSectionFunctors_subset`); no `Module` structure is built. The sum of two sc-smooth sections
    and the constant multiples of one, which Part I does not state, are proved in the charts
    (`StrongBundle.IsScSmoothSection.sectionAdd_of_isScSmoothSection`,
    `StrongBundle.IsScSmoothSection.sectionSmul_const`).

Found while formalizing §8.4 up to Theorem 8.6 (2026-11-07).

50. **Definition 8.8** *(p. 275)*. `EpFunctor.IsProperCovering`: (1) `F` is surjective and a local
    sc-diffeomorphism on objects; (2) every fibre `F⁻¹(x)` is finite, and an open `U(x) ∋ x` has
    `F⁻¹(U(x))` the union of mutually disjoint `U(y) ∋ y`, `y ∈ F⁻¹(x)`, with `F : U(y) → U(x)`
    sc-diffeomorphisms whose inverses `σ(y)` are part of the data; (3) `L_F = (F, s) : 𝐘 → 𝐗 ₛ×_F Y`
    (`fibredMap`) is an sc-diffeomorphism onto Part I's fibred-product sub-M-polyfold of `𝐗 × Y`
    (`MPolyfold.isSubMPolyfold_fibredProduct`, Part I's Proposition 2.15), as in Definition 7.3 (4).

51. **The degeneracy remark after Definition 8.8 needs tameness** *(pp. 275–276)* *(book 2021: unchanged, after Definition 8.5.1, p. 384)*. The text computes
    `d_{𝐗 ₛ×_F Y}(F(φ), s(φ)) = ½ d_{𝐗 × Y}(F(φ), s(φ))` through `d_{𝐗 × Y} = d_𝐗 + d_Y`. The first
    equality, `d_𝐘(φ) = d_{𝐗 ₛ×_F Y}(L_F(φ))` (`IsProperCovering.degIndex_fibredMap`), and
    `d_𝐗(F(φ)) = d_𝐘(φ)` (`IsProperCovering.degIndex_mor`) hold in general, by Part I's Proposition
    2.7 (`proposition_2_24`). The product formula is available in Part I's formalization for tame
    factors (`MPolyfold.isTame_prod`) and in general only as `d_{X × Y} ≤ d_X + d_Y`
    (`MPolyfold.degIndex_prod_le`; section "From the Lean proofs of Chapter 2, §2.4–§2.5 and Theorem
    2.16" above, items 15, 16), and Part I's Proposition 2.15 states its formula `d = ½ d_{X × Y}`
    for tame `X`, `Y`. So `d_{𝐗 × Y}(F(φ), s(φ)) = 2 d_𝐘(φ)` and `d_{𝐗 ₛ×_F Y} = ½ d_{𝐗 × Y}` along
    the image of `L_F` are stated for tame `X` and `Y` (`IsProperCovering.degIndex_prod_fibredMap`;
    `𝐗` is then tame, `s` being a local sc-diffeomorphism), and in general as `≤`
    (`IsProperCovering.degIndex_prod_fibredMap_le`). As we read it, the remark needs `X` and `Y`
    tame, which the text does not state; whether the equality holds without tameness is not settled
    here.

52. **Proposition 8.2** *(pp. 276–277)* *(book 2021: corrected, proof of Proposition 8.5.2, p. 385)*. `IsProperCovering.proposition_8_2`. Condition (2), "follows
    easily", is proved by shrinking `U(x)` of `F` to a `U₀` with `(F|U(y))⁻¹(U₀) ⊆ U'(y)` for the
    evenly covered neighbourhoods `U'(y)` of `H`, `y ∈ F⁻¹(x)`, a finite intersection
    (`IsProperCovering.evenlyCovered_comp`). Condition (3) goes through the text's `K̃`, `L̃`
    (`IsProperCovering.isScDiffeo_fibredMap_comp`); their sc-smoothness, as maps between
    sub-M-polyfolds of products, uses Part I's Proposition 2.6 (2) (a map into a sub-M-polyfold is
    sc-smooth as soon as it is sc-smooth into the ambient M-polyfold), proved again privately in
    `ProperCovering.lean`, as in Chapter 7's `SubGroupoid.lean`. "fo" for "for" in the proof (p.
    276; possible misprint).

53. **Theorem 8.5: the chart and "sufficiently small"** *(Theorem 8.5, p. 277)*. The data of the
    theorem form a `ProperCoveringChart`: a natural representation `R : X.NaturalRep x` (Chapter 7's
    structure: `U(x)` open and connected, with the natural `G_x`-action), sets `U(y)` for `y ∈
    F⁻¹(x)` and `𝐔(ψ₀)` for the morphisms `ψ₀` between points of `F⁻¹(x)` (`Y.morOn (F⁻¹(x))`), and
    (0)–(5) as fields. "Disjoint union of connected open neighbourhoods" means: each set open,
    connected and containing its centre, the sets pairwise disjoint, with the given union; that they
    are then the connected components is `ProperCoveringChart.connectedComponentIn_U`,
    `ProperCoveringChart.connectedComponentIn_sheet`. `𝐔(φ)` for `φ ∈ 𝐔(x)` is read as the connected
    component of `𝐔(x)` containing `φ`; by Remark 8.2 (a) `F(ψ₀) ∈ 𝐔(x)`, and (1) is Chapter 7's
    description of `𝐔(x)` by the sheets `Γ(g, U(x))`. "`s : 𝐔(ψ₀) → U(y)` is an sc-diffeomorphism"
    is Part I's `IsScDiffeoOn`, with an inverse. "Sufficiently small" is proved in two forms: charts
    with `U(x)` inside every open `V ∋ x` (`theorem_8_5`), and one open `W ∋ x` that works for every
    natural representation on a connected `U(x) ⊆ W` (`theorem_8_5_of_naturalRep`); the proof uses
    only `U(x) ⊆ U'(x)` for `U'(x)` as in Definition 8.8 (2).

54. **Theorem 8.5 (5) does not hold as printed, as we read it** *(Theorem 8.5 (5), p. 277)* *(book 2021: unchanged, Theorem 8.5.3 (5), p. 386)*. As
    printed, the left vertical arrow of the square is `s : 𝐔(ψ₀) → U(s(ψ₀))`, the bottom arrow `F`,
    the right vertical arrow `t` and its lower right corner `U(t(F(ψ₀)))`. With `t` the square says
    `F(s(ψ)) = t(F(ψ))` for `ψ ∈ 𝐔(ψ₀)`. A functor gives `F(s(ψ)) = s(F(ψ))`, and `F(ψ) = Γ(g, F(s
    ψ))` with `g = F(ψ₀)` has `t(F(ψ)) = Φ(g)(F(s ψ))`, which differs from `F(s ψ)` wherever `Φ(g)`
    does not fix `F(s ψ)`. Example (checked in Lean, `CoveringExamples.theorem_8_5_five_as_printed`,
    for every chart of Theorem 8.5 at `0`; charts exist by
    `theorem_8_5_five_as_printed_nonvacuous`): the identity functor of `ℤ/2 ⋉ ℝ`, `ℤ/2` acting by `z
    ↦ ±z`, is a proper covering functor (`EpFunctor.isProperCovering_id`); at `x = 0`, with
    `ψ₀ = (−1, 0)` and `ψ = (−1, z) ∈ 𝐔(ψ₀)`, `F(s(ψ)) = z` and `t(F(ψ)) = −z`. The square is
    formalized with `s` on both vertical arrows (`ProperCoveringChart.comm_src`; the corner
    `U(s(F(ψ₀))) = U(x)` is the same set, since `s(F(ψ₀)) = t(F(ψ₀)) = x`), together with the
    companion square with `t` on both (`ProperCoveringChart.comm_tgt`: `F(t(ψ)) = t(F(ψ))` over `F :
    U(t ψ₀) → U(x)`). The right arrow `t` is therefore a possible misprint for `s`. "Of
    sc-diffeomorphisms": the left arrows are (3), the top arrow (4), the bottom arrows (0), and the
    right arrows `s, t : 𝐔(F(ψ₀)) → U(x)` are `ProperCoveringChart.isScDiffeoOn_src_sheetF`,
    `ProperCoveringChart.isScDiffeoOn_tgt_sheetF`.

55. **Theorem 8.5: the route of the proof, and possible misprints** *(proof, pp. 278–279)* *(book 2021: proof of Theorem 8.5.3, pp. 386–387: `g ∈ G_y` unchanged; `G_y`-invariant, `s(F(φ))`, "admitting admitting" and, in the statement, "morphismsm" (p. 385) corrected)*. The text
    decomposes the morphisms of `𝐘` near `F⁻¹(x)` by sheets and natural representations of the
    groups `G_y` in `Y`, and does not invoke Definition 8.8 (3). Here (3) does that work: `L_F` is a
    bijection with continuous inverse; for `ψ₀ : y → y'` with `g = F(ψ₀)`, `τ(z) = L_F⁻¹(Γ(g, F(z)),
    z)` on `U(y) = U'(y) ∩ F⁻¹(U(x))`, and `𝐔(ψ₀) = τ(U(y))` (`ProperCoveringLocal.Data`,
    `ProperCoveringLocal.exists_data`, `Data.toChart`). `τ` is a continuous section of `s`, hence
    sc-smooth (`ProperCoveringLocal.isScSmoothOn_of_section`); `t ∘ τ` maps `U(y)` into `U(y')`
    because `U(y)` is connected and `F⁻¹(U(x))` is the disjoint union of the open `U(y'')`
    (`Data.tgt_τ_mem`, the counterpart of the text's claim that `ψ̂` maps `U(y)` onto `U(y')`); and
    `F = Γ(g, ·) ∘ F ∘ s` on `𝐔(ψ₀)` is the text's formula for (4). The finiteness of `F⁻¹(x)` and
    Definition 8.8 (1) are not needed. Possible misprints in the proof (p. 278): "there exists `g ∈
    G_y` for which `F(φ) = Γ(g, F(z))`" for `g ∈ G_x`, `Γ` being the natural representation of
    `G_x`; "`U(x)` is a `G_y`-invariant subset" for `G_x`-invariant; "`F(z') = s(F(φ))`" for
    `t(F(φ))`, with `φ : z → z'`; "admitting admitting". In the statement, (2) has "morphismsm" (p.
    277).

56. **Remark 8.2** *(pp. 277–278)*. (a) is `remark_8_2_a`: a morphism between points of `F⁻¹(x)` is
    mapped into `G_x` (`isotropyMor`). (b), "everything is determined by `U(x)`", is read as: two
    charts with the same `U(x)` have the same `Φ` and `Γ` on `U(x)` (on a connected `U(x)`, `Γ(g,
    ·)` is the continuous section of `s` through `g`, Chapter 7's `NaturalRep.Γ_eqOn`), the same
    `U(y)` and the same `𝐔(ψ₀)` (`remark_8_2_b`). Its remarks on the naturality of Theorem 7.1's
    construction and on the main point of the proof have no further formal content.

57. **Definition 8.9 and the discussion after it** *(pp. 279–281)*. `Diff_sc` is `MPolyfoldCat`
    (bundled M-polyfolds of one universe) with the sc-diffeomorphisms `ScDiffeo` (Part I's
    `IsScDiffeoOn` on `univ`, with an inverse). The category `C` with one object is `SingleObj G`
    for a group `G`, its automorphism group, and `D` a Mathlib `Groupoid`, both in `Type`; then `C
    ₛ×_f D = G × D` (`coveringMap`, `IsCoveringFunctor`, `GeometricLift`). The finiteness of
    Definition 8.9 ("finitely many objects and morphisms") is not part of `IsCoveringFunctor` and
    `GeometricLift`; it is carried as the instance arguments `[Fintype D] [∀ a b, Fintype (a ⟶ b)]
    [Fintype G]` of the results that use it (Proposition 8.3, Theorem 8.6). `D = ∅` is allowed, as
    in the text (`isCoveringFunctor_of_isEmpty`; item 59). In the discussion after the definition,
    `U(x) = L_C(⋆)` is `GeometricLift.Ux`, `τ(y)` is `GeometricLift.τy`, `φ_{yy'}(ψ) = L_D(ψ)` is
    `GeometricLift.φ`, with `φ_{yy''}(ψ ∘ γ) = φ_{y'y''}(ψ) ∘ φ_{yy'}(γ)` (`GeometricLift.φ_comp`,
    `GeometricLift.φ_id`, `GeometricLift.φ_inv_φ`); the actions of `G_y` on `U(y)` and of `G_x` on
    `U(x)` (`GeometricLift.smul_def`, `GeometricLift.smul_def'`, `GeometricLift.isScSmoothMap_smul`)
    and the equivariance `τ(y)(h ∗ z) = f(h) ∗ τ(y)(z)` (`GeometricLift.τ_equivariant`) are proved.
    Functoriality is stated with Mathlib's `γ ≫ ψ` for the text's `ψ ∘ γ`; `G_y` is Mathlib's monoid
    `End y`, with `h * k = k ≫ h`, the text's `h ∘ k`; the action of `G_x = G` on `U(x)` is a left
    action through the composition of `SingleObj G`.

58. **Disjoint unions of M-polyfolds** *(p. 281, proof of Proposition 8.3)* *(book 2021: unchanged, proof of Proposition 8.5.7, p. 390)*. "`Y = ⊔ U(y)` possesses
    a natural M-polyfold structure" is not described in the text; it is read as the structure whose
    charts are those of the summands, transported along `Sigma.mk i` (`MChart.pushforward`,
    `MPolyfold.sigmaChart`, `MPolyfold.sigma`). Charts of different summands have disjoint domains,
    and Part I's compatibility of charts then asks for the sc-smoothness of maps between empty
    retracts, which holds (`MChart.compatible_of_disjoint`), so no condition is added. The index
    type is arbitrary; paracompactness is proved summand by summand, without metrizability
    (`paracompactSpace_sigma`). The transported chart is extended by `0` off its image, so no
    summand needs to be nonempty. Sc-smoothness, local sc-diffeomorphisms, the degeneracy index and
    tameness are summand-wise (`MPolyfold.isScSmoothMap_sigma_iff`,
    `MPolyfold.isLocalScDiffeo_sigma_iff`, `MPolyfold.degIndex_sigma`,
    `MPolyfold.isTame_sigma_iff`); products distribute over the union
    (`MPolyfold.isScDiffeoOn_sigmaProdDistrib`), and `G × X ≅ ⊔_G X` for discrete `G`
    (`isScDiffeoOn_prod_discrete_sigma`).

59. **Proposition 8.3: `D` nonempty, and the other readings** *(Proposition 8.3, pp. 281–283)* *(book 2021: unchanged, Definition 8.5.5, p. 388, and Proposition 8.5.7, pp. 390–391)*.
    Definition 8.9 allows `D = ∅`: the map `ψ ↦ (f(ψ), s(ψ))` is then a bijection of empty sets
    (`isCoveringFunctor_of_isEmpty`). Then `Y = ∅` while `U(x)` is arbitrary, and `F` is surjective
    on objects (Definition 8.8 (1)) only if `U(x) = ∅` (`geometricLiftFunctor_surjective_iff`). The
    text does not say so; `proposition_8_3` assumes `[Nonempty D]`, used for the surjectivity only.
    The hypothesis holds in Theorem 8.6, where `D` is on `F⁻¹(x)` (`EpFunctor.nonempty_fiberCat`).
    Further readings: the finiteness of Definition 8.9 enters as instance arguments (finitely many
    morphisms make `t : 𝐘 → Y` proper, finitely many objects make the fibres finite, a finite `G`
    makes `G ⋉ U(x)` an ep-groupoid); `X = G_x ⋉ U(x)` is Chapter 7's action ep-groupoid
    (`EpGroupoid.Examples.actionEpGroupoid`), `G` with a discrete topology (an instance argument,
    satisfiable by `⊥`) and lifted by `ULift` to the universe of `U(x)`, since the translation
    groupoid takes its group and its space in one universe; `mor(y, y') × U(y)` is modelled as `⊔_{ψ
    : y → y'} U(y)` (item 58); the composition of `Y` is total, `(ψ, z') ∘ (γ, z) = (ψ ∘ γ, z)`,
    with a junk value off composable pairs. The "one verifies" is carried out: the composition is
    sc-smooth in the sheet form, the summand index of `σ(t ψ)` being locally constant
    (`GeometricLift.isScSmoothCompSheet_y`), and properness holds with `V = Y`, `t` being proper
    (`GeometricLift.isProperMap_yTgt`); Definition 8.8 (2) holds with `U(x)` the whole object space
    of `X`. The text deduces that (8.16) is an sc-diffeomorphism from "bijection and local
    sc-diffeomorphism"; the sc-smoothness of the inverse is proved directly
    (`GeometricLift.fibredInv`, `GeometricLift.isScSmoothMap_fibredInv`). The proof's "the map `F :
    X → Y`" is read as `F : Y → X` (possible misprint).

60. **Theorem 8.6: readings and possible misprints** *(Theorem 8.6 and its proof, pp. 283–285)* *(book 2021: Theorem 8.5.8, pp. 392–393: "exists exists" and `A(ψ, z) = (f(z), F(z))` corrected; `τ(t)` unchanged)*. The
    theorem is stated for ep-groupoids whose objects and morphisms are in `Type`, since Definition
    8.9 is (item 2). `C`, the full subcategory on `x`, is `SingleObj G_x`; `D` is the full
    subcategory on `F⁻¹(x)` (`GroupoidStr.FullOb`, `EpFunctor.FiberCat`), its finiteness, from
    Definition 8.8, entering as local instances (`EpFunctor.fintypeFiberCat`) and `D ≠ ∅` coming
    from the surjectivity of `F`. "A sufficiently small `U(x)` as in Theorem 8.5" is any chart of
    Theorem 8.5 (a `ProperCoveringChart`); charts exist inside every open `V ∋ x` (part (b) of
    `theorem_8_6`), and part (c) holds for every chart. "A geometric lift `A : K → L`" is read as a
    geometric lift together with the proper covering functor `A` that Proposition 8.3 associates
    with it (`ProperCoveringChart.geometricLift`). The morphisms of `D` are the morphisms `ψ₀`
    themselves, so "`ψ : y → y'` where `ψ ∈ 𝐔(ψ₀)`" is read as `ψ = ψ₀`: `L_D(ψ₀) = t ∘ (s|𝐔(ψ₀))⁻¹`
    and `Ψ(ψ₀, z) = (s|𝐔(ψ₀))⁻¹(z)`. Both "one verifies" are carried out through `F`: on the sheets
    `F(σ_ψ(z)) = Γ(f(ψ), F(z))` (Theorem 8.5 (1), (4)), so `τ(y') ∘ L_D(ψ) = Φ(f(ψ)) ∘ τ(y)`, and
    the functoriality of `L_D` follows from that of `Φ` and the injectivity of `F` on each `U(y)`;
    that `Ψ` preserves compositions and units uses the unique lifting of Definition 8.8 (3). "Fully
    faithful open embedding" is `EpFunctor.IsFullyFaithfulOpenEmbedding`: full and faithful on the
    underlying groupoids, and an injective local sc-diffeomorphism on objects and on morphisms; "the
    image is the full subcategory on `U(x)`" is `range Φ.obj = U(x)` and `range Φ.mor = {φ | s(φ),
    t(φ) ∈ U(x)}` (`ProperCoveringChart.range_Φ_obj`, `ProperCoveringChart.range_Φ_mor`), and
    likewise for `Ψ` and `F⁻¹(U(x))`. Possible misprints: "there exists exists" (p. 283); "`τ(t) :
    L_D(y) → L_C ∘ f(y)`" for `τ(y)` (p. 284); "`A(ψ, z) = (f(z), F(z))`" for `(f(ψ), F(z))` (p.
    284), as in Proposition 8.3's `F(ψ, z) = (f(ψ), τ(y)(z))`.

Found while formalizing Definition 8.10 and Appendix 8.5 (2026-11-07).

70. **Definition 8.10** *(p. 285)*. `EpStrongBundle.IsProperStrongBundleCovering EW EV F A`. `A` is
    taken in the functorial picture, as a strong bundle functor covering `F` (Definition 8.6;
    equivalently its object map is a strong bundle map of Definition 8.5, item 34). "A local strong
    bundle isomorphism" is: every `y` has open `U ∋ y` and `U'` with `A : W|U → V|U'` a strong
    bundle isomorphism covering `F : U → U'`; "`A : W|U(y) → V|U(x)` is a strong bundle isomorphism"
    is `StrongBundle.IsStrongBundleIsoOn` (`F : U(y) → U(x)` an sc-diffeomorphism and `A : P⁻¹(U(y))
    → Q⁻¹(U(x))` an sc-diffeomorphism on `[0]` and on `[1]`; the inverse is then linear on the
    fibres, `IsStrongBundleIsoOn.fiberEquiv`). The finiteness of `F⁻¹(x)` in (2) is that of
    Definition 8.8 (2) and is not repeated. In (3) the text does not say which strong bundle
    structure `𝐕 ₛ×_A W → 𝐗 ₛ×_F Y` carries; it is read as the pull-back of `P : W → Y` along `pr₂ :
    𝐗 ₛ×_F Y → Y` (`EpFunctor.fibredSnd`), on Part I's fibred-product sub-M-polyfold. Its points
    `((φ, y), w)` with `P(w) = y` correspond to the text's `((φ, v), w)` with `v = A(w)`
    (`EpStrongBundle.fibredBundleEquiv`); under this correspondence the map of (3) is
    `EpStrongBundle.fibredLift` and the projection is the text's `((φ, v), w) ↦ (φ, P(w))`
    (`pullbackProj_fibredBundleEquiv`). "Strong bundle isomorphism" is
    `StrongBundle.IsStrongBundleIso`. The closing sentence, "all structural statements about proper
    covering functors between ep-groupoids lift to the strong bundle situation", is not formalized
    beyond §8.5.2 (items 75, 113).

71. **§8.5.1: cardinalities, and the classes indexed by their images in `|Y|`** *(pp. 285–286)*.
    `mor(F⁻¹(x))` is `Y.morOn (F⁻¹(x))`, and `#` is the cardinality of finite sets (`Set.ncard`,
    `Nat.card`): the fibres are finite (Definition 8.8 (2)), the isotropy groups are (Proposition
    7.4), hence so is `mor(F⁻¹(x))` (`IsProperCovering.finite_morOn_fiber`). The bijection
    `mor(F⁻¹(x)) → G_x × F⁻¹(x)` comes from Definition 8.8 (3)
    (`IsProperCovering.bijective_fibredMap`, `IsProperCovering.existsUnique_lift`,
    `IsProperCovering.morOnFiberEquiv`). The isomorphism classes `Θ_1, …, Θ_q` of `F⁻¹(x)` are
    indexed by their images in `|Y|`: `Θ_c = F⁻¹(x) ∩ π⁻¹(c)` (`fiberClass`, `fiberIndex`,
    `fiberClasses`); the statements about `Θ_c` hold for every `c`, with `Θ_c = ∅` for `c ∉
    π(F⁻¹(x))`. With this indexing, the correspondence `Θ_j ↔ Θ'_j` of Lemma 8.10 is "the same
    index" (item 73).

72. **Lemma 8.9** *(pp. 286–287)* *(book 2021: unchanged, proof of Lemma 8.6.1, now (8.24), p. 397)*. The set `{ψ ∈ mor(F⁻¹(x)) | s(ψ), t(ψ) ∈ Θ_j}` is `mor(Θ_j)`
    (`morOn_fiberClass_eq`); restricting the bijection of item 71 to (8.17) uses that `t(ψ) ∈ Θ_j`
    is automatic for `s(ψ) ∈ Θ_j` and `t(ψ) ∈ F⁻¹(x)` (`IsProperCovering.morOnClassEquiv`). The
    third claim divides by `#Θ_j ≥ 1` (`IsProperCovering.lemma_8_9`). (8.17) writes "`ψ → (Fψ),
    s(ψ))`", with an unbalanced parenthesis, for `ψ ↦ (F(ψ), s(ψ))` (possible misprint).

73. **Lemmas 8.10 and 8.11** *(p. 287)* *(book 2021: unchanged, Lemmas 8.6.2, 8.6.3, p. 398; the citation now reads Lemma 8.6.2 for Lemma 8.6.1)*. For isomorphic `x, x'` the index sets agree
    (`IsProperCovering.fiberIndex_eq`), by the lifting of a morphism `x → x'` to morphisms out of
    `F⁻¹(x)` (Definition 8.8 (3), `IsProperCovering.exists_isomorphic_of_isomorphic`);
    `IsProperCovering.lemma_8_10` states the correspondence by index,
    `IsProperCovering.lemma_8_10_equiv` as a bijection between the sets of classes. Lemma 8.11
    divides by `#G_{y₀} ≥ 1` (`IsProperCovering.lemma_8_11`,
    `IsProperCovering.ncard_fiber_eq_of_isomorphic`). Possible misprints: after Lemma 8.10, "Using
    the third claim of Lemma 8.10, we infer that `#Θ_j = #G_x / #G_{y₀}`": Lemma 8.10 has no third
    claim, and the third claim of Lemma 8.9, `#G_x = #G_{y₀} · #Θ_j`, is meant; in Lemma 8.11,
    `#F⁻¹(x) = ∑_{i=1}^q #Θ_j = ∑_{i=1}^q #Θ'_j` sums over `i` with summands indexed by `j`.

74. **Proposition 8.4** *(p. 288)*. Only the local constancy of `x ↦ #F⁻¹(x)` is used
    (`IsProperCovering.eventually_ncard_fiber_eq`, `IsProperCovering.isLocallyConstant_ncard_fiber`:
    by Definition 8.8 (2), `y ↦ (F|U(y))⁻¹(x')` is a bijection `F⁻¹(x) → F⁻¹(x')` for `x' ∈ U(x)`),
    not the text's "the structure of isomorphism classes stays the same". The function descends to
    `|X|` by Lemma 8.11 (`IsProperCovering.fiberCardOrbit`), is locally constant there in the
    quotient topology (`IsProperCovering.isLocallyConstant_fiberCardOrbit`), hence constant on
    connected components (`IsProperCovering.proposition_8_4`). The text's `ℕ = {1, 2, …}` is Lean's
    `ℕ`, as the trivial ep-groupoid of the discrete M-polyfold (`EpGroupoid.trivial`,
    `discretePolyfold`); the values are `≥ 1` (`IsProperCovering.one_le_ncard_fiber`). The functor
    sends a morphism `φ` to the identity of `#F⁻¹(s φ) = #F⁻¹(t φ)`
    (`IsProperCovering.fiberCardFunctor`).

75. **§8.5.2** *(pp. 288–289)*. `A(φ, w) = (F(φ), A_{s(φ)}(w))` is
    `IsProperStrongBundleCovering.mor_val`, and the `A_y` are topological linear isomorphisms by
    Definition 8.10 (1) (`IsProperStrongBundleCovering.fiberEquiv`). The natural transformation `μ_Y
    → μ_X ∘ F` of functors into `Ban` is stated as its naturality identity `μ_X(F(φ)) ∘ A_{s(φ)} =
    A_{t(φ)} ∘ μ_Y(φ)` (`EpStrongBundle.section_8_5_2`), the fibres `Q⁻¹(F(s φ))` and `Q⁻¹(s(F φ))`
    being identified through their values in `V`; the category `Ban` is not formalized. Only the
    strong bundle functor part of Definition 8.10 enters the identity
    (`IsStrongBundleFunctor.μ_comm`).

Found while checking that the hypotheses can hold (`NonVacuity.lean`, `NonVacuityBundle.lean` and
the witnesses of the other files, 2026-11-07; not in the text).

100. **Covering functors** (`CoveringExamples.isCoveringFunctor_id`,
     `CoveringExamples.not_isCoveringFunctor_one`). The identity of `SingleObj G` is a covering
     functor for every group `G`; for nontrivial `G` the functor sending every morphism to `1` is
     not, so Definition 8.9 is not vacuous in either direction. The empty groupoid gives a covering
     functor (`isCoveringFunctor_of_isEmpty`; item 59).

101. **A geometric lift, and Proposition 8.3 applied** (`CoveringExamples.reflectionLift`,
     `CoveringExamples.isProperCovering_reflectionLift`). `ℤ/2 = ℤˣ` acting on `ℝ`
     (`CoveringExamples.rCat`) by `y ↦ ±y` (`CoveringExamples.reflectionDiffeo`,
     `CoveringExamples.reflectionHom`) is a geometric lift of the identity of `SingleObj ℤˣ`, with
     `L_D = L_C` and `τ = 1`; Proposition 8.3 makes it a proper covering functor onto the
     translation groupoid `ℤ/2 ⋉ ℝ`, with non-trivial isotropy at `0`. Its fibres `F⁻¹(x)` have one
     point.

102. **Identities and trivial strong bundles** (`NonVacuityBundle.lean`). The identity functor of
     every ep-groupoid is a proper covering functor (`EpFunctor.isProperCovering_id`, with
     `EpFunctor.isScDiffeoOn_fibredMap_id`). Every strong bundle over an M-polyfold is a strong
     bundle over the trivial ep-groupoid of the M-polyfold, with `μ(z, w) = w`
     (`EpStrongBundle.trivial`, Definition 8.4); the identity is a strong bundle map and a strong
     bundle functor (`EpStrongBundle.isMap_id`, `EpStrongBundle.isStrongBundleFunctor_id`,
     Definitions 8.5, 8.6), and the identity of every strong bundle over an ep-groupoid is a proper
     strong bundle covering functor (`EpStrongBundle.isProperStrongBundleCovering_id`, with
     `EpStrongBundle.isStrongBundleIso_fibredLift_id` for (3), on the reading of item 70). Over the
     trivial ep-groupoid every section is functorial (`EpStrongBundle.isFunctorialSection_trivial`),
     so `Γ`, `Γ⁺`, `Fred` are Part I's sc-smooth, sc⁺- and sc-Fredholm sections
     (`EpStrongBundle.mem_sectionFunctors_trivial`,
     `EpStrongBundle.mem_plusSectionFunctors_trivial`,
     `EpStrongBundle.mem_fredholmSectionFunctors_trivial`). The witnesses use that maps of
     pull-backs `(z, y) ↦ (g(z), Φ(y))` are strong bundle maps
     (`StrongBundle.isStrongBundleMap_pullbackMap`).

103. **A strong bundle over an ep-groupoid in `Type`** (`TrivialBundle.epBundle`). Part I's trivial
     strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ`: its functorial picture is an
     ep-groupoid (`TrivialBundle.epBundleEpGroupoid`), its identity is a proper strong bundle
     covering functor (`TrivialBundle.epBundle_isProperStrongBundleCovering`,
     `TrivialBundle.epBundle_isMap_id`), `0 ∈ Γ⁺`
     (`TrivialBundle.fiberZero_mem_plusSectionFunctors_epBundle`), and for a `C^∞` map `φ : ℝⁿ → ℝᵏ`
     the graph section `x ↦ (x, φ(x))` lies in `Γ` and in `Fred`
     (`TrivialBundle.graphSection_mem_sectionFunctors_epBundle`,
     `TrivialBundle.graphSection_mem_fredholmSectionFunctors_epBundle`, from Part I's results on
     graph sections, germ reading).

104. **Tangent witnesses** (`TangentTame.lean`, `TangentOrbit.lean`). The tangent of the trivial
     ep-groupoid of `ℝⁿ` is tame (`EpGroupoid.isTame_tangentEpGroupoid_trivial_rn`, Lemma 8.8), and
     the tangent of the trivial ep-groupoid of any M-polyfold has a paracompact orbit space
     (`EpGroupoid.hasParacompactOrbitSpace_tangent_trivial`, Theorem 8.4).

105. **Hypotheses check: every hypothesis is satisfiable; what the witnesses do not exercise**
     *(2026-11-07)*. (1) Tameness (Theorems 8.1, 8.3, Lemma 8.8, the degeneracy remark) is
     existential, a tame atlas, as in Chapter 7 (Chapter 7, item 106); witnesses
     `EpGroupoid.isTame_trivial_rn`, `EpGroupoid.isTame_tangentEpGroupoid_trivial_rn`; the tame `X`,
     `Y` of `IsProperCovering.degIndex_prod_fibredMap` are satisfiable by the identity of the
     trivial ep-groupoid of `ℝⁿ` (not stated as a lemma). (2) `HasParacompactOrbitSpace` (Theorem
     8.4): `EpGroupoid.hasParacompactOrbitSpace_trivial`, item 104. (3) "A sufficiently small `U(x)`
     with the natural `G_x`-action" (Theorems 8.5, 8.6) is a `ProperCoveringChart` datum; charts
     exist inside every open `V ∋ x` (`theorem_8_5`), so part (c) of `theorem_8_6`, which quantifies
     over all charts at `x`, is not vacuous; no hypothesis "for every `U(x)`" is made elsewhere. (4)
     Proper covering functors (Definition 8.8; Propositions 8.2, 8.4, Theorems 8.5, 8.6, Lemmas
     8.9–8.11): items 101, 102. (5) A covering functor with a geometric lift and `D` nonempty
     (Proposition 8.3): item 101. (6) Strong bundles over ep-groupoids, section functors and proper
     strong bundle covering functors (Definitions 8.4–8.7, 8.10, §8.5.2): items 102, 103. No
     hypothesis of the form "for all compatible charts" is made in Chapter 8. Not exercised: every
     proper covering functor constructed has one-point fibres `F⁻¹(x)` (identities, and the functor
     of item 101, whose `D` has one object), so the even coverings of Definitions 8.8 (2), 8.10 (2)
     are met with one sheet and the counting of Appendix 8.5 only with `q = 1`, `#Θ_1 = 1`; no
     proper strong bundle covering functor other than identities is constructed; `Γ⁺` is witnessed
     by the zero section only.

Not formalized (2026-11-07).

110. **Definitions 8.2, 8.3: sc-differential forms on ep-groupoids and the sc-de Rham complex**
     *(§8.2, pp. 268–270)* *(book 2021: Definitions 8.2.1, 8.2.2, pp. 372–373; both possible misprints unchanged)*. Not formalized. They need the Whitney sums `⊕^k TX` as M-polyfolds, the
     linear structure of `T_xX` (gap G.7), linear maps `Tφ` (gap G.70, item 112), the M-polyfolds
     `X^i` for `i ≥ 2` (gap G.6) and the sc-differential forms, the Lie bracket and the exterior
     derivative of Part I's §4.4, which are not formalized either (gaps G.37–G.39); Stokes's theorem
     (gap G.40) is not used in §8.2. New gap G.74. Like Part I's §4.4 in `ch04.md`, the two
     definitions have no V-item. Possible misprints: Definition 8.2 writes "`Tφ : T_xX → T_yY`" for
     `T_yX` (p. 269), as in Remark 8.1 (item 10); in the argument that `dω` is compatible with
     morphisms (p. 269), "`x = s(φ) ∈ U(x₀) ∩ X₁` and `y = t(φ₀)`" has `t(φ₀)` for `t(φ)`, the
     target of the morphism `φ` whose tangent `Tφ : T_xX → T_yX` follows.

111. **Lemma 8.1 as printed** *(Lemma 8.1, p. 259; the proof of Lemma 8.6, p. 262)*. The
     identification `T(𝐗 ₛ×ₜ 𝐗) = T𝐗 _{Ts}×_{Tt} T𝐗` and `m_{T𝐗} = Tm` on it are not formalized (new
     gap G.75). The sheet form (item 5) is what the proofs of Lemmas 8.1, 8.2 and 8.6 use, and
     condition (4) of Definition 7.3 for `T𝐗` is proved without the identification (item 7), so
     nothing in the chapter depends on the gap.

112. **Gap G.70 in part: `Tφ` well defined and functorial** *(Remark 8.1, pp. 264–265; Chapter 7,
     Definition 7.4)*. Chapter 7 left all properties of `tangentMor` unformalized (Chapter 7, item
     110; gap G.70). Now formalized: `Tφ` is well defined, `Tφ(Ts(h)) = Tt(h)` for every `h ∈ T_φ𝐗`
     (`tangentMor_tSrc`), and functorial, `T(ψ ∘ φ) = Tψ ∘ Tφ` for `φ ∈ 𝐗₁` (`tangentMor_comp`), and
     the pairs `(Tφ, a)` of Remark 8.1 describe `T𝐗` (item 10). Still not formalized: that `Tφ` is
     bijective and linear (the linearity needs gap G.7), that `Tφ = Tφ̂(s(φ))`, a bounded linear
     isomorphism on level `0` and an sc-operator for smooth `φ`. A dated sentence is added to G.70.

113. **Not formalized, without a gap** *(pp. 264–289)*. Remark 8.1: the M-polyfold structure
     transported along `G`, and the description by triples `(a, Tφ, b)`. The proof of Theorem 8.4:
     the sc-isomorphism of `TU(x_z)` with a local bundle model `TO → O¹` and the linearity of the
     bundle action of `G_{x_z}` (not needed by the proof here, item 21; the linearity needs gap
     G.7). Remark 8.2 (b): the remarks on the naturality of Theorem 7.1's construction (item 56).
     Strong bundle maps over open subsets of the base (item 30). The closing sentence of Definition
     8.10 (item 70), the phrase "the structure of isomorphism classes stays the same" before
     Proposition 8.4 (item 74), and the category `Ban` of §8.5.2 (item 75). None of these is used
     elsewhere in the chapter, so none is given a gap.

114. **Gaps of Part I and Chapter 7 taken up in Chapter 8.** G.70 (Chapter 7, `Tφ` as an
     sc-isomorphism): in part (item 112). G.7 (the linear structure of `T_xX`) remains open; it now
     also stands behind the linearity claims of Remark 8.1 and of the action in the proof of Theorem
     8.4, and behind Definitions 8.2, 8.3. G.6 and G.37–G.39 are needed for Definitions 8.2, 8.3
     (gap G.74) and remain open. No other gap of Part I or Chapter 7 is used in the chapter.
