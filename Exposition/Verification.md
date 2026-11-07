# Polyfold Theory, verified: the machine-checked edition

*A companion to the expanded exposition of Part I of H. Hofer, K. Wysocki and E. Zehnder's* Polyfold
and Fredholm Theory *(Springer 2021; the 2014 preprint arXiv 1407.3185 is the text in hand, and its
numbering and pages are used, marked as such; the numbers and pages of the book's arXiv version,
1707.08941, are in `Exposition/BookConcordance.md`, and the Springer edition is not checked). That exposition is
written to be read; this edition is written to be checked. It records, chapter by chapter, exactly
which statements of the text have been verified by the Lean 4 proof assistant against the Mathlib
library, what each verified statement says when read back in ordinary language, which hypotheses the
text left silent, where the formal statement or proof departs from the text's, and what remains
unverified and why. Nothing here needs to be read in Lean; every checked statement is restated in
prose, and the Lean names are given only so that the claims can be audited.*

**Where to start.** The project has three parts:

- the expanded exposition (`Exposition/Chapter1.md`, …), the book for reading;
- *Polyfold Theory, Checked*, the Lean formalization (`Polyfold/`) and the reports on it;
- the sign-off page, the list of statements a reader is asked to confirm.

This edition is the way into the second part. Its reports each answer one question:

- **What is proved?** This edition: every checked result in plain language, with all its
  hypotheses, and the list of statements to sign off.
- **How is it proved?** *Polyfold Theory, proof by proof* (`Exposition/ProofByProof.md`): the formal
  proofs retold as mathematics, with a trace tag on each step naming the Lean declaration that
  carries it.
- **How does it differ from the text?** *Polyfold Theory beside Lean*, the comparison
  (`Exposition/polyfold-beside-lean.html`): each result of the book beside the checked statement, with
  a verdict (the same, restated, hypotheses made explicit, stronger, narrower) and the differences.

A result has the same number, V1.5 say, in this edition, the comparison and the sign-off page.

---

## 0. Summary

| Chapter | HWZ | Content | Status | Lean lines |
|:--|:--|:--|:--|--:|
| Chapter 1 | Ch. 1, §§1.1–1.4 | sc-Banach spaces, sc-operators and sc-Fredholm operators, sc-differentiability and its relation to classical differentiability, the chain rule, the degeneracy index | **verified** | 6,895 |
| Chapter 2 | Ch. 2 | sc-smooth retractions and retracts, M-polyfolds, the degeneracy index, tame M-polyfolds, strong bundles | **verified except Proposition 2.2 and Lemma 2.29 as stated; Remark 2.28's negative claim is false** | 15,187 |
| Chapter 3 | Ch. 3 | sc-Fredholm sections and the implicit function theorem | **partly verified** | 54,808 |
| Chapter 4 | Ch. 4, §§4.1–4.4 | manifolds with boundary with corners: sc⁺-retracts and the characterization, smooth finite-dimensional submanifolds, families and Sard's theorem (vendored) | **verified except Lemma 4.10 and §4.4** | 12,083 |
| Chapter 5 | Ch. 5, §§5.1–5.4 | the Fredholm package for M-polyfolds: auxiliary norms, compactness, sc⁺-sections and bump functions, transversality, general and good position, homotopies, partitions of unity | **verified except Theorems 5.22, 5.27 and the cited Theorems 5.32, 5.40, 5.43** | 12,100 |
| Chapter 6 | Ch. 6, §§6.1–6.5, 6.7 | linearizations and orientations: determinant lines and exact sequences, the determinant of a Fredholm operator, good left-projections, stabilization, the determinant line bundle, the propagation of orientations along paths, orientable and oriented sc-Fredholm sections, the orientation of the solution set | **verified except Proposition 6.28 (1), the global parts of Theorem 6.41 and Remark 6.42, and Theorem 6.43** | 20,793 |

Total: 121,866 lines of Lean in 202 files under `Polyfold/` (`wc -l`, excluding unfinished `WIP_` files). Toolchain: Lean v4.33.1, Mathlib v4.33.1. To reproduce: `lake build`, then `lake env lean -DmaxSynthPendingDepth=3 Polyfold/Test.lean`, which prints the axioms of every main theorem. Edition of 7 November 2026.

---

## 1. How to read a verified statement

**The statements are the contract.** A machine-checked proof guarantees that the *stated* theorem
follows from Lean's axioms. It guarantees nothing about whether the statement is the one the authors
meant. The reader's job, and the only mathematical judgement this document asks for, is to read
each prose restatement and confirm that it says what the text means. Where the restatement is
weaker or stronger than the text, or uses a different but equivalent definition, this is flagged as
a **Deviation**.

**The setting.** An sc-Banach space is formalized as an indexed family of real Banach spaces $E_m$,
$m \ge 0$, with injective compact continuous linear inclusions $E_{m+1} \to E_m$ and the smooth
points dense in every level; the text's subspace picture $E_0 \supset E_1 \supset \cdots$ is
recovered by identifying $E_m$ with its image in $E_0$, and "$x \in E_m$" for $x \in E_0$ means
that $x$ is in that image. A map $f : U \to F$ on a subset $U \subseteq E_0$ is a total function
$E_0 \to F_0$ whose values off $U$ play no role; its level maps $f_m : U_m \to F_m$ are determined
by the injectivity of the inclusions. "Relatively open in a partial quadrant" enters most theorems
only through its consequences on each level, that $U_m$ is the intersection of an open and a convex
set and has unique differentiability at each of its points (an *sc-domain*); whenever the text's
hypothesis is replaced by this weaker one the item says so.

**Classical differentiability.** $C^k$ on a relatively open subset of a partial quadrant means
Mathlib's $C^k$ *within the set*, with derivatives within the set; on these sets derivatives are
unique, so the notion agrees with the exposition's Definition 3.C.

**Axioms.** Every verified theorem depends only on the three standard axioms of Lean's Mathlib
(`propext`, `Classical.choice`, `Quot.sound`), as `Polyfold/Test.lean` prints; there is no `sorry`.

---

## 2. Chapter 1 (HWZ §§1.1–1.4): verified

Chapter 1 of Part I (preprint pp. 6–17) sets up the sc-calculus: sc-Banach spaces, sc-operators,
sc-subspaces and quotients (Definitions 1.1–1.5, Propositions 1.6–1.7), sc-Fredholm operators and
their stability under $\mathrm{sc}^+$-perturbations (Definition 1.8, Propositions 1.9–1.10), partial
quadrants, $\mathrm{sc}^0$, $\mathrm{sc}^1$, $\mathrm{sc}^k$ and sc-smooth maps (Definitions
1.11–1.15), the relation between sc-differentiability and classical differentiability on the levels
(Propositions 1.16–1.19, Corollary 1.20), the chain rule (Theorem 1.21), the degeneracy index of a
partial quadrant (Definition 1.23, Lemma 1.24) and boundary recognition (Theorem 1.25). Every
numbered statement is verified, Proposition 1.19 and Corollary 1.20 under the text's own
hypothesis ($C^{l+1}$ from $U_{m+l}$ to $F_m$ for $l \le k$), by the 2010 paper's induction
$(\mathrm S_k)$ on elementary maps (V1.37–V1.39). One is verified in a stronger form: Theorem 1.25,
which the text quotes from another paper, is proved here for $\mathrm{sc}^1$ germs. Example 1.2, the weighted Sobolev spaces, is not formalized (Mathlib has no Sobolev spaces).
The remarks of the text that the exposition turns into lemmas are verified as well (V1.28–V1.36):
the invariance of the index under $\mathrm{sc}^+$-perturbations and on every level, the uniqueness
of the sc-structure in finite dimensions, sc-splittings as sc-projections, the smooth points of a
quotient, the compact-open continuity of $Df$, sc¹ = $C^1$ in finite dimensions on quadrants with
boundary, and the level shift and tangent of a tuple.
The setting throughout: an sc-Banach space is an indexed family of real Banach spaces $E_m$ with
injective compact continuous linear inclusions $E_{m+1} \to E_m$ and dense smooth points; $\iota_m
: E_m \to E_0$ is the composite inclusion, and "$x \in E_m$" for $x \in E_0$ means $x \in
\iota_m(E_m)$. A map $f : U \to F$, $U \subseteq E_0$, is a total function $E_0 \to F_0$ whose
values off $U$ do not matter, with level maps $f_m : U_m \to F_m$ determined by the injectivity of
$\iota_m$. The text's hypothesis "$U$ relatively open in a partial quadrant $C$ of $E$" is, in most
theorems, weakened to the *sc-domain* condition it implies: each $U_m$ is the intersection of an
open and a convex subset of $E_m$ and has unique differentiability at each of its points. Where a
theorem is stated for sc-domains the text's hypothesis is a special case. The infrastructure that
Mathlib lacked and that is built here, the Riesz–Schauder theorem and the stability of Fredholm
operators under compact perturbations (used without citation in §1.4.1), the compact-open lemma
behind §1.2, and sc-domains, has its own items (V1.24–V1.27); so has the machinery of the proof of
Proposition 1.19 under the text's hypothesis, the derivative tower, the elementary maps with the
induction $(\mathrm S_k)$, and the sum rule for $\mathrm{sc}^k$ maps (V1.37–V1.39).

**V1.1 (sc-Banach spaces, sums and shifts; `Polyfold.ScScale`, `Polyfold.ScScale.toBase`,
`Polyfold.ScScale.smooth`, `Polyfold.ScScale.smoothLvl`, `Polyfold.ScBanach`,
`Polyfold.ScBanach.denseRange_inclK`, `Polyfold.ScBanach.const`, `Polyfold.ScBanach.prod`,
`Polyfold.ScBanach.prod_smoothLvl`, `Polyfold.ScBanach.shift`, `Polyfold.ScBanach.shift_smoothLvl`,
`Polyfold.ScBanach.shiftK`, `Polyfold.ScBanach.lvlSet`).** A *scale* consists of real Banach spaces
$E_m$, $m \in \mathbb N$, and injective compact continuous linear maps $E_{m+1} \to E_m$; $\iota_m :
E_m \to E_0$ is the composite, $E_\infty \subseteq E_0$ the subspace of points that lie in
$\iota_m(E_m)$ for every $m$, and $E_\infty \cap E_m := \iota_m^{-1}(E_\infty)$. An *sc-Banach
space* is a scale in which $E_\infty \cap E_m$ is dense in $E_m$ for every $m$. Consequences: the
image of $E_{m+k}$ in $E_m$ is dense. Constructions: for a finite-dimensional normed space $V$ the
constant family $E_m = V$, with identity inclusions, is an sc-Banach space all of whose points are
smooth; for sc-Banach spaces $E$, $F$, the family $E_m \times F_m$ with the product inclusions is an
sc-Banach space $E \oplus F$ whose smooth points at level $m$ are the pairs of smooth points; the
family $E_{m+1}$ with the inclusions of $E$ is an sc-Banach space $E^1$ whose smooth points at level
$m$ are those of $E$ at level $m + 1$; $E^k$ is the $k$-fold iterate. For $U \subseteq E_0$, the
level set $U_m := \iota_m^{-1}(U) \subseteq E_m$. *Book:* Definition 1.1, p. 6: a decreasing
sequence of Banach spaces $E = E_0 \supset E_1 \supset \cdots$ with compact inclusions and
$E_\infty = \bigcap E_m$ dense in every $E_m$; the constant structure on a finite-dimensional
space; $(E \oplus F)_m = E_m \oplus F_m$; the filtration $A_m = A \cap E_m$ of a subset and the
shift $A^k$. *Hidden hypotheses:* the inclusions are injective (implicit in "$\subset$") and
continuous (part of compactness). *Deviation (restated):* the $E_m$ are separate Banach spaces, not
subsets of one space; the two pictures are equivalent and nothing in Chapter 1 uses more than the
family. The text's remarks that a finite-dimensional space has *only* the constant structure and
that the constant family on an infinite-dimensional space is not an sc-structure are V1.31.

**V1.2 (sc-operators and sc-isomorphisms; `Polyfold.ScOperator`, `Polyfold.ScOperator.ext_base`,
`Polyfold.IsScOperator`, `Polyfold.ScOperator.isScOperator`, `Polyfold.IsScOperator.toScOperator`,
`Polyfold.ScOperator.comp`, `Polyfold.ScOperator.mapsTo_smoothLvl`, `Polyfold.ScIso`,
`Polyfold.ScIso.symm`, `Polyfold.ScIso.trans`, `Polyfold.isScOperator_of_mapsTo`,
`Polyfold.ScIso.ofBijective`).** An *sc-operator* $T : E \to F$ between sc-Banach spaces is a family
of continuous linear maps $T_m : E_m \to F_m$ with $\iota^F_m T_{m+1} = T_m \iota^E_m$; the family
is determined by $T_0$, and a continuous linear $T_0 : E_0 \to F_0$ *is an sc-operator* exactly when
for each $m$ some continuous linear $T_m : E_m \to F_m$ satisfies $\iota_m T_m = T_0 \iota_m$ (the
two formulations correspond). Sc-operators compose, add, and map smooth points to smooth points. An
*sc-isomorphism* is a family of continuous linear equivalences $E_m \simeq F_m$ commuting with the
inclusions; inverses and composites are sc-isomorphisms. A continuous linear $T_0 : E_0 \to F_0$
with $T_0(E_m) \subseteq F_m$ for every $m$ is an sc-operator (the continuity of $T_0 : E_m \to F_m$
is the closed graph theorem), and an sc-operator bijective on every level is an sc-isomorphism (the
open mapping theorem). *Book:* Definition 1.3, p. 7. *Hidden hypotheses:* none. *Deviation
(restated):* the level maps are data, with the text's predicate on the base map recovered as
`Polyfold.IsScOperator`; the continuity of the inverse of a bijective sc-operator on each level,
which the text's definition of an sc-isomorphism demands, is built into the formal notion, and
derived from the open mapping theorem separately (`Polyfold.ScIso.ofBijective`); the continuity on
the levels asked by Definition 1.3 is automatic for a bounded $T_0$ that maps $E_m$ into $F_m$
(Findings, Chapter 3, item 233).

**V1.3 (sc⁺-operators; `Polyfold.ScPlus`, `Polyfold.ScBanach.shiftIncl`,
`Polyfold.ScPlus.toScOperator`, `Polyfold.ScPlus.isCompactOperator`,
`Polyfold.ScPlus.toScOperator_mem_range_toBase_succ`).** An *$\mathrm{sc}^+$-operator* $E \to F$ is
an sc-operator $E \to F^1$, i.e. continuous linear $S_m : E_m \to F_{m+1}$ commuting with the
inclusions. Composed with the inclusion $F^1 \to F$ (an sc-operator) it is an sc-operator $E \to F$
whose level-$m$ map $E_m \to F_m$ is compact for every $m$, and which raises the level: $x \in
\iota_m(E_m)$ implies $S_0 x \in \iota_{m+1}(F_{m+1})$. *Book:* Definition 1.4, p. 7, and the remark
that follows it: an sc-operator $S$ with $S(E_m) \subset F_{m+1}$ and $S : E \to F^1$ an sc-operator
is sc-compact. *Hidden hypotheses:* none; the condition $S(E_m) \subset F_{m+1}$ is contained in
"$S : E \to F^1$ is an sc-operator" and is dropped.

**V1.4 (sc-subspaces and sc-splittings; `Polyfold.ScBanach.levelSub`,
`Polyfold.ScBanach.isClosed_levelSub`, `Polyfold.ScBanach.IsScSubspace`,
`Polyfold.ScBanach.ofSubspaceScale`, `Polyfold.ScBanach.ofSubspace`,
`Polyfold.ScBanach.IsScSplitting`, `Polyfold.ScBanach.IsScSplitting.closedComplemented`,
`Polyfold.ScBanach.IsScSplitting.symm`).** For a subspace $A \subseteq E_0$ let $A_m :=
\iota_m^{-1}(A) \subseteq E_m$, closed if $A$ is. $A$ is an *sc-subspace* if $A$ is closed and
$A_m$ is contained in the closure of $A_m \cap E_\infty$ for every $m$. A closed $A$ with the
levels $A_m$ and the restricted inclusions is a scale (the restricted inclusions are compact), and
an sc-subspace is in this way an sc-Banach space. $E = F \oplus G$ is an *sc-splitting* if $F$ and
$G$ are sc-subspaces and $F_m$, $G_m$ are complementary subspaces of $E_m$ for every $m$; then $F_m$
is closed complemented in $E_m$, and the splitting is symmetric in $F$ and $G$. *Book:* Definition
1.5, p. 7: $F$ closed with $(F \cap E_m)$ an sc-structure; an sc-complement $G$ with $(G \cap E_m)$
an sc-structure and $E_m = F_m \oplus G_m$ a topological direct sum on every level. *Hidden
hypotheses:* none. *Deviation (restated):* the closedness of $F_m$ in $E_m$ and the compactness of
$F_{m+1} \to F_m$ are automatic and are not conditions; "topological direct sum" is read as
complementary closed subspaces, the continuity of the projections following from the closed graph
theorem (`Polyfold.ScBanach.IsScSplitting.closedComplemented`).

**V1.5 (Proposition 1.6; `Polyfold.ScBanach.proposition_1_6_iff`,
`Polyfold.ScBanach.proposition_1_6`).** Let $E$ be an sc-Banach space and $F \subseteq E_0$ a
finite-dimensional subspace. $F$ is an sc-subspace if and only if $F \le E_\infty$; and if $F \le
E_\infty$ there is a subspace $G \subseteq E_0$ such that $E = F \oplus G$ is an sc-splitting.
*Book:* p. 7, the same. *Hidden hypotheses:* none. *Proof:* as in the text, with a continuous
projection $E_0 \to F$ from Mathlib (Hahn–Banach), lifted to each level through $F_m \cong F$.

**V1.6 (Proposition 1.7; `Polyfold.ScBanach.quotientScale`, `Polyfold.ScBanach.quotient`,
`Polyfold.ScBanach.quotientMap`, `Polyfold.ScBanach.proposition_1_7`).** Let $E$ be an sc-Banach
space and $A \subseteq E_0$ a closed subspace. The quotient Banach spaces $E_m/A_m$, with the
inclusions $E_{m+1}/A_{m+1} \to E_m/A_m$ induced by $\iota$ (injective and compact), and with the
smooth points dense on every level, form an sc-Banach space $E/A$, and the quotient maps $E_m \to
E_m/A_m$ form an sc-operator $E \to E/A$. As a statement: there exist an sc-Banach space $Q$ and an
sc-operator $q : E \to Q$ with every $q_m$ surjective and $\ker q_m = A_m$. *Book:* p. 8, for an
sc-subspace $A$: $E/A$ with the filtration $E_m/A_m$ is an sc-Banach space, where $E_m/A_m$ is
identified with $\{(x + A) \cap E_m : x \in E\}$. *Hidden hypotheses:* none. *Deviation
(stronger):* only closedness of $A$ is used, not that $A$ is an sc-subspace. The text's
identification of $E_m/A_m$ with a subset of $E/A$ is the injectivity of the induced inclusion,
which holds because $A_m$ is the full preimage of $A$. The text's description of $(E/A)_\infty$ as
the classes of points of $E_\infty$ is V1.33; only the trivial inclusion is used here.

**V1.7 (sc-Fredholm operators and the index; `Polyfold.ScFredholmSplitting`,
`Polyfold.IsScFredholm`, `Polyfold.ScFredholmSplitting.index`, `Polyfold.scIndex`,
`Polyfold.ScFredholmSplitting.index_eq`, `Polyfold.ScFredholmSplitting.K_le_smooth`,
`Polyfold.ScFredholmSplitting.ker_lvl`, `Polyfold.ScFredholmSplitting.range_lvl`,
`Polyfold.ScFredholmSplitting.isFredholm`).** An *sc-Fredholm splitting* of an sc-operator $T : E
\to F$ is given by subspaces $K, X \subseteq E_0$ and $C, Y \subseteq F_0$ such that $E = K \oplus
X$ and $F = C \oplus Y$ are sc-splittings, $K = \ker T_0$, $Y = \operatorname{range} T_0$, $K$ and
$C$ are finite-dimensional, and for every $m$ the map $T_m$ is a bijection of $X_m$ onto $Y_m$.
$T$ is *sc-Fredholm* if a splitting exists. The index $\dim K - \dim C$ of a splitting equals $\dim
\ker T_0 - \dim(F_0/\operatorname{range} T_0)$, hence does not depend on the splitting. Moreover
$K \le E_\infty$; $\ker T_m = K_m$ and $\operatorname{range} T_m = Y_m$; and every $T_m : E_m \to
F_m$ is a Fredholm operator in Mathlib's sense (finite-dimensional kernel, closed range of finite
codimension, strict, with closed complemented kernel). *Book:* Definition 1.8, p. 9, with the
remarks that $K \subset E_\infty$, $T(X_m) = Y_m$, $E_m = K \oplus X_m$ and "$F = C \oplus T(E_m)$"
(read $F_m$), and $\operatorname{ind}(T) = \dim K - \dim C$. *Hidden hypotheses:* none. *Deviation
(restated):* condition (3), "$T : X \to Y$ is an sc-isomorphism", is taken as the bijectivity of
$T_m : X_m \to Y_m$ for every $m$; the continuity of the inverses is automatic by the open mapping
theorem on the closed subspaces $X_m$, $Y_m$. The independence of the index from the splitting and
the level-wise Fredholm property are not stated in the text.

**V1.8 (Proposition 1.9; `Polyfold.proposition_1_9`, `Polyfold.ScOperator.IsRegularizing`,
`Polyfold.IsScFredholm.isRegularizing`, `Polyfold.isScFredholm_iff`).** Let $T : E \to F$ be an
sc-operator with an sc-Fredholm splitting, $e \in E_0$ and $m \in \mathbb N$. If
$T_0 e \in \iota_m(F_m)$ then $e \in \iota_m(E_m)$. As a property of sc-operators
(`Polyfold.ScOperator.IsRegularizing`): every sc-Fredholm operator is regularizing. Conversely, an
sc-operator $T$ with $T_0$ Fredholm that is regularizing is sc-Fredholm (V1.9); so $T$ is
sc-Fredholm if and only if $T_0 : E_0 \to F_0$ is Fredholm and $T$ is regularizing. *Book:* p. 9,
the same ("an sc-Fredholm operator is regularizing"). *Hidden hypotheses:* none; the step "$c = 0$"
uses $C \cap Y = 0$ on level $0$, as in the text. The converse is not stated in the text; it is the
tool for the text's unargued “is sc-Fredholm” for operators obtained by conjugation and restriction
in Chapter 3 (V3.8, V3.46, V3.96; Findings, Chapter 3, item 233).

**V1.9 (Proposition 1.10; `Polyfold.proposition_1_10`, `Polyfold.ScPlus.regularizing_add`,
`Polyfold.isScFredholm_of_isRegularizing`, `Polyfold.isScFredholm_of_isRegularizing_index`).** Let
$E$, $F$ be sc-Banach spaces, $T : E \to F$ an sc-Fredholm operator and $S : E \to F$ an
$\mathrm{sc}^+$-operator. Then $T + S$ (with $S$ read as an sc-operator $E \to F$) is sc-Fredholm.
Along the way, $T + S$ is regularizing in the sense of V1.8. *Book:* p. 10, the same; the proof is
in §1.4.1, pp. 14–15. *Hidden hypotheses:* none. *Proof:* the text's, with three additions. The
opening claim that $T + S : E_m \to F_m$ is Fredholm is the classical compact-perturbation theorem,
proved here since Mathlib lacks it (V1.24–V1.25). The step "$y = (T+S)e$, so by Proposition 1.9
$e \in E_m$" needs a bootstrap, since $Se$ is only one level up: $Te = y - Se \in F_1$ gives
$e \in E_1$, then $Se \in F_2$, and so on $m$ times; the same bootstrap gives $K_m = K_{m+1}$. The
complement $C$ is the range of a linear right inverse of $F_0 \to F_0/Y$ with values in $F_\infty$
rather than the span of a lifted basis, and condition (3) of Definition 1.8 for $T + S$, which the
text does not verify, is proved as the bijectivity of $(T + S)_m : X_m \to Y_m$. The text does not
assert that the index is preserved; it is, and this is V1.30. The construction uses only two
properties of $T + S$, that it is Fredholm on level $0$ and regularizing; with these as hypotheses
it is proved as a criterion: an sc-operator that is Fredholm on level $0$ and regularizing is
sc-Fredholm, and every level map is then Fredholm of the level-$0$ index (not stated in the text).

**V1.10 (partial quadrants and tuples; `Polyfold.quadrant`, `Polyfold.quadrant_convex`,
`Polyfold.quadrant_isClosed`, `Polyfold.lvlSet_quadrant`, `Polyfold.IsPartialQuadrant`,
`Polyfold.IsPartialQuadrant.convex`, `Polyfold.IsPartialQuadrant.isClosed`,
`Polyfold.IsPartialQuadrant.uniqueDiffWithinAt_lvlSet`, `Polyfold.isPartialQuadrant_univ`,
`Polyfold.IsRelOpenInQuadrant`).** In the sc-Banach space $\mathbb R^n \oplus W$ (with $\mathbb
R^n$ constant) the *quadrant* on level $m$ is $\{(a, w) : a_i \ge 0 \text{ for all } i\}$; it is
closed and convex with non-empty interior, and the level sets of the level-$0$ quadrant are the
level quadrants. $C \subseteq E_0$ is a *partial quadrant* if there are $n$, an sc-Banach space $W$
and an sc-isomorphism $T : E \to \mathbb R^n \oplus W$ with $C = T_0^{-1}(\text{quadrant})$. Then
every $C_m$ is closed, convex, with non-empty interior in $E_m$, and $C_m$ has unique
differentiability (in Mathlib's sense) at each of its points; $E_0$ itself is a partial quadrant
($n = 0$). $(U, C, E)$ is a *tuple*, i.e. $U$ is a *relatively open subset of the partial quadrant
$C$*, if $C$ is a partial quadrant and $U = O \cap C$ with $O \subseteq E_0$ open. *Book:*
Definition 1.11, p. 10, and the sentence after it. *Hidden hypotheses:* none; "closed convex" is
derived from the model. *Deviation:* none in the definition. The text's tacit use of $C_k$ as a
partial quadrant in $E^k$ is V1.36 (for $k = 1$, and by iteration).

**V1.11 (sc⁰ maps; `Polyfold.levelMap`, `Polyfold.IsSc0`, `Polyfold.IsSc0.levelMap_mapsTo`,
`Polyfold.IsSc0.continuousOn_base`, `Polyfold.IsSc0.congr`, `Polyfold.IsSc0.mono`,
`Polyfold.IsSc0.comp`, `Polyfold.isSc0_id`, `Polyfold.ScOperator.isSc0`).** For $f : E_0 \to F_0$
the *level map* $f_m : E_m \to F_m$ sends $x$ to the unique $y \in F_m$ with $\iota_m y = f(\iota_m
x)$, when such $y$ exists (and to a junk value otherwise). $f$ is *$\mathrm{sc}^0$ on $U \subseteq
E_0$* if for every $m$ and $x \in U_m$ the point $f(\iota_m x)$ lies in $\iota_m(F_m)$, and $f_m$ is
continuous on $U_m$. Then $f$ is continuous on $U$; if $f(U) \subseteq V$ then $f_m(U_m) \subseteq
V_m$; the property depends only on the values of $f$ on $U$ and passes to subsets of $U$; the
composition of an $\mathrm{sc}^0$ map on $U$ with values in $V$ and an $\mathrm{sc}^0$ map on $V$ is
$\mathrm{sc}^0$ on $U$; the identity and every sc-operator are $\mathrm{sc}^0$, the latter with level
maps $T_m$. *Book:* Definition 1.12, p. 10: $f(U_m) \subset V_m$ (meaning $U'_m$) and $f : U_m \to
U'_m$ continuous for all $m$. *Hidden hypotheses:* none. *Deviation (restated):* maps are total
functions on $E_0$, and the target tuple enters only through $f(U) \subseteq U'$.

**V1.12 (the tangent; `Polyfold.ScBanach.tangent`, `Polyfold.ScBanach.tangentSet`,
`Polyfold.ScBanach.lvlSet_tangentSet`, `Polyfold.ScBanach.tangentSet_mono`,
`Polyfold.IsScDomain.tangentSet`, `Polyfold.ScBanach.shift_tangentSet`).** The *tangent* of an
sc-Banach space $E$ is $TE := E^1 \oplus E$, with levels $E_{m+1} \times E_m$. For $U \subseteq
E_0$, $TU \subseteq (TE)_0 = E_1 \times E_0$ is $\{(x, h) : x \in U_1\}$, with level-$m$ part
$U_{m+1} \times E_m$; $U \subseteq V$ implies $TU \subseteq TV$. If $U$ is an sc-domain (V1.27),
$TU$ is an sc-domain in $TE$; and the level-$1$ part of $TU$ is $T(U_1)$ in $T(E^1) = (TE)^1$.
*Book:* Definition 1.13, p. 10: $T(U, C, E) = (U^1 \oplus E, C^1 \oplus E, E^1 \oplus E)$, "again a
tuple". *Hidden hypotheses:* none. *Deviation:* none; that $TC$ is a partial quadrant in $TE$, so
that $T(U, C, E)$ is again a tuple, is V1.36, while the proofs of §§1.2–1.3 propagate the
sc-domain property (V1.27) instead.

**V1.13 (sc¹ maps and the tangent map; `Polyfold.tangentMapWith`, `Polyfold.IsSc1With`,
`Polyfold.IsSc1`, `Polyfold.scDeriv`, `Polyfold.tangentMap`,
`Polyfold.IsSc1With.eq_of_uniqueDiffWithinAt`, `Polyfold.IsSc1.scDeriv_eqOn`,
`Polyfold.IsSc1.tangentMap_eqOn`, `Polyfold.IsSc1.congr`, `Polyfold.IsSc1With.continuousOn_deriv`,
`Polyfold.IsSc1With.exists_delta_deriv`, `Polyfold.exists_isSc1_not_continuousOn_deriv`,
`Polyfold.ScOneExample.isSc1With`, `Polyfold.ScOneExample.not_continuousAt_D`).** Let
$f : E_0 \to F_0$, $U \subseteq E_0$ and $D : E_1 \to \mathcal L(E_0, F_0)$ a family of bounded
operators. The tangent map $T_Df : (TE)_0 \to (TF)_0$ is $(x, h) \mapsto (f_1(x), D(x)h)$. $f$ is
*$\mathrm{sc}^1$ on $U$ with derivatives $D$* if (1) $f$ is $\mathrm{sc}^0$ on $U$; (2) for every
$x \in U_1$, the map $f \circ \iota_1 : E_1 \to F_0$ has derivative $D(x) \circ \iota_1$ at $x$
within $U_1$; (3) $T_Df$ is $\mathrm{sc}^0$ on $TU$. $f$ is *$\mathrm{sc}^1$ on $U$* if some $D$
makes it so; `Polyfold.scDeriv` is a chosen such $D$ (junk if none exists) and `Polyfold.tangentMap`
the tangent map built from it. If $D$ and $D'$ both satisfy (2) at a point $x \in U_1$ where $U_1$
has unique differentiability, then $D(x) = D'(x)$, because $E_1$ has dense image in $E_0$; hence on
an sc-domain the chosen derivative agrees on $U_1$ with any admissible one, and the tangent map on
$TU$. The property depends only on the values of $f$ on $U$. Level $0$ of condition (3) is the
continuity of $(x, h) \mapsto D(x)h$ on $U_1 \times E_0$, and it implies: for $x \in U_1$, a compact
$K \subseteq E_0$ and $c > 0$ there is $\delta > 0$ with $\|D(x')w - D(x)w\| \le c$ for all
$x' \in U_1$ with $\|x' - x\|_1 < \delta$ and all $w \in K$ (continuity of $x \mapsto D(x)$ in the
compact-open topology). It need not be norm continuous: on $E = \mathbb R \oplus X$, with $X$ the
sc-Banach space whose level $m$ consists of the real sequences with $(k+1)^m x_k \to 0$, normed by
$\sup_k (k+1)^m|x_k|$ (every level a copy of $c_0$, the inclusions $\mathrm{diag}(1/(k+1))$), the
map $f(t, x)_k = \cos(kt)x_k$ is $\mathrm{sc}^1$ with
$Df(t, x)(\tau, \xi)_k = -k\sin(kt)x_k\tau + \cos(kt)\xi_k$, and for every derivative family $D$ of
$f$ the map $x \mapsto D(x)$ is not continuous on $E_1$ into $\mathcal L(E_0, X_0)$ with the
operator norm: $(\pi/(n+1), 0) \to 0$ in $E_1$, but $\|Df(\pi/(n+1), 0) - Df(0, 0)\| \ge 2$. *Book:*
Definition 1.14, pp. 10–11, with conditions (1)–(3) as stated, and the remarks that
$x \mapsto Df(x)$ is continuous for the compact-open but not in general for the norm topology, and
that sc¹ maps between finite-dimensional spaces are the $C^1$ maps. *Hidden hypotheses:* the
uniqueness of $Df(x)$, without which "the tangent map" is undefined; it holds because $E_1$ is dense
in $E_0$ and $U_1$ has unique differentiability (true for relatively open subsets of partial
quadrants, V1.10). *Deviation (hypotheses explicit):* the derivative family is an explicit parameter
of `Polyfold.IsSc1With`, with `Polyfold.IsSc1` the text's notion. The compact-open remark is V1.34,
its negative half the example above, which the text does not give (Findings, Chapter 1, follow-up
item 1), and the finite-dimensional remark is V1.35 (on relatively open subsets of quadrants, with
boundary; the open case is also in `Polyfold/Test.lean`,
`isSc1_iff_contDiffOn_of_finiteDimensional`).

**V1.14 (sc^k and sc-smooth maps; `Polyfold.IsSck`, `Polyfold.IsScSmooth`, `Polyfold.IsSck.of_succ`,
`Polyfold.IsSck.of_le`, `Polyfold.isScSmooth_iff`, `Polyfold.IsSck.congr`).** By recursion: $f$ is
$\mathrm{sc}^0$ on $U$ in the sense of V1.11; $f$ is $\mathrm{sc}^{k+1}$ on $U$ if it is
$\mathrm{sc}^1$ on $U$ and its tangent map (built from the chosen derivative) is $\mathrm{sc}^k$ on
$TU \subseteq (TE)_0$ as a map into $(TF)_0$. $f$ is *sc-smooth* on $U$ if it is $\mathrm{sc}^k$ for
every $k$. Then $\mathrm{sc}^{k+1}$ implies $\mathrm{sc}^k$, and $\mathrm{sc}^l$ for $l \le k$; $f$
is sc-smooth iff it is $\mathrm{sc}^1$ with sc-smooth tangent map; on an sc-domain, $\mathrm{sc}^k$
depends only on the values on $U$. *Book:* p. 11, the inductive definition after Definition 1.14
(numbered 1.15 here, as in the Lean files; the preprint's Remark 1.15 on partial cones is not
formalized). *Hidden hypotheses:* none beyond V1.13.

**V1.15 (Proposition 1.16; `Polyfold.IsSc1Levels`, `Polyfold.IsSc1Levels.continuousOn_clm`,
`Polyfold.IsSc1Levels.contDiffOn`, `Polyfold.IsSc1Levels.toBase_apply`,
`Polyfold.IsSc1Levels.isSc1With`, `Polyfold.IsSc1With.isSc1Levels`, `Polyfold.proposition_1_16`,
`Polyfold.IsSc1With.contDiffOn_base`, `Polyfold.IsSc1With.scOperator_deriv`).** Let $U$ be an
sc-domain in $E$ and $f$ $\mathrm{sc}^0$ on $U$. Then $f$ is $\mathrm{sc}^1$ on $U$ if and only if
there is a family $D_m(x) \in \mathcal L(E_m, F_m)$, $m \in \mathbb N$, $x \in U_{m+1}$, such that
for every $m$: (a) $f_m \circ \iota : U_{m+1} \to F_m$ has derivative $D_m(x) \circ \iota$ at every
$x \in U_{m+1}$ within $U_{m+1}$; (b) $(x, h) \mapsto D_m(x)h$ is continuous on $U_{m+1} \times
E_m$. For any such family, $x \mapsto D_m(x) \circ \iota$ is continuous $U_{m+1} \to \mathcal
L(E_{m+1}, F_m)$ in the operator norm, so $f : U_{m+1} \to F_m$ is $C^1$ within $U_{m+1}$; and
$\iota_m D_m(x) = D_0(\iota x) \iota_m$, so all $D_m(x)$ are restrictions of the single operator
$Df(x) := D_0(x)$. In the direction "sc¹ ⇒ levels" the family is the level operators of V1.26; in
particular $f \circ \iota_1 : U_1 \to F_0$ is $C^1$. If $f$ is $\mathrm{sc}^1$ with derivatives $Df$
and $x \in U_1$ is a smooth point, $Df(x) : E_0 \to F_0$ is an sc-operator. *Book:* p. 12: an
$\mathrm{sc}^0$ map on a relatively open subset of a partial quadrant is $\mathrm{sc}^1$ iff (1) for
$m \ge 1$, $f : U_m \to F_{m-1}$ is $C^1$ with $df : U_m \to \mathcal L(E_m, F_{m-1})$ continuous and
(2) $df(x)$ extends to a bounded $Df(x) : E_{m-1} \to F_{m-1}$ with $(x, h) \mapsto Df(x)h$
continuous on $U_m \oplus E_{m-1}$; in particular $Df(x)$ is an sc-operator at smooth points.
*Hidden hypotheses:* the compatibility of the extensions $Df(x)$ across levels, which the text's
notation assumes and the direction (⇐) needs (Lemma 3.H of the exposition); it is proved. *Deviation
(restated):* the extensions form an explicit family; the $C^1$ property and the norm continuity of
$df$ are consequences of (a)–(b) rather than part of the condition; the hypothesis on $U$ is the
weaker sc-domain condition.

**V1.16 (Proposition 1.17; `Polyfold.IsSc0.shift`, `Polyfold.IsSc1With.shift`, `Polyfold.IsSck.shift`,
`Polyfold.IsScSmooth.shift`, `Polyfold.IsScDomain.shift`).** Let $U$ be an sc-domain in $E$ and $f$
$\mathrm{sc}^k$ on $U$. Then the level-$1$ map $f_1 : E_1 \to F_1$ is $\mathrm{sc}^k$ on $U_1$ as a
map between the shifted sc-Banach spaces $E^1$ and $F^1$ (whose level sets of $U_1$ are the
$U_{m+1}$). For $k = 0$ no hypothesis on $U$ is needed; for an $\mathrm{sc}^1$ map with derivatives
$Df$, the derivatives of $f_1$ are the level-$1$ operators $Df(x) : E_1 \to F_1$, $x \in U_2$;
sc-smooth maps lift to sc-smooth maps; and $U_1$ is an sc-domain in $E^1$. *Book:* p. 12: if $f :
U \to V$ is $\mathrm{sc}^k$ between relatively open subsets of partial quadrants then $f : U^1 \to
V^1$ is $\mathrm{sc}^k$. *Hidden hypotheses:* none. *Deviation:* none; the target $V$ plays no role
and the hypothesis on $U$ is weaker.

**V1.17 (Proposition 1.18; `Polyfold.IsSck.contDiffOn_levels'`, `Polyfold.IsSck.contDiffOn_levels`,
`Polyfold.IsSck.contDiffOn_levels_of_le`, `Polyfold.IsSck.contDiffOn_base`,
`Polyfold.IsScSmooth.contDiffOn_levels`).** Let $U$ be an sc-domain in $E$ and $f$ $\mathrm{sc}^k$
on $U$. Then for every $m$, the map $f_m \circ \iota : U_{m+k} \to F_m$ is $C^k$ within $U_{m+k}$;
for $l \le k$, $f_m \circ \iota : U_{m+l} \to F_m$ is $C^l$; in particular $f \circ \iota_k : U_k
\to F_0$ is $C^k$. If $f$ is sc-smooth, $f : U_{m+k} \to F_m$ is $C^k$ for all $m$ and $k$. *Book:*
p. 13, the same for $f : U \to V$ between relatively open subsets of partial quadrants. *Hidden
hypotheses:* the meaning of "$C^k$" on a relatively open subset of a quadrant, never defined in the
text: here Mathlib's $C^k$ within the set, with unique derivatives on these sets. *Deviation:*
none in the statement. *Proof:* a direct induction on $k$ over all sc-domains, with a compatible
level-lowering operator $\rho : E_{m+k} \to E_m$ as parameter, and the compact-open lemma (V1.26)
applied to the second component of the level tangent map; the 2010 paper's multilinear maps
$\Gamma(x)$ and its differentiation under the integral sign are not used.

**V1.18 (Proposition 1.19; `Polyfold.proposition_1_19_text`,
`Polyfold.IsScSmooth.of_contDiffOn_levels_text`, `Polyfold.proposition_1_19_zero`,
`Polyfold.proposition_1_19`, `Polyfold.IsScSmooth.of_contDiffOn_levels`).** Let $U$ be an
sc-domain in $E$ and $f$ $\mathrm{sc}^0$ on $U$. If for every $m \ge 0$ and $0 \le l \le k$ the
map $f_m \circ \iota : U_{m+l} \to F_m$ (the level-$m$ map restricted along the inclusion $E_{m+l}
\to E_m$) is $C^{l+1}$ within $U_{m+l}$, then $f$ is $\mathrm{sc}^{k+1}$ on $U$; if this holds for
every $l$, then $f$ is sc-smooth. Also proved, under the stronger hypothesis that every level map
$f_m : U_m \to F_m$ is $C^{k+1}$ within $U_m$: $f$ is $\mathrm{sc}^{k+1}$; for $k = 0$, where the
two hypotheses agree, $f$ is $\mathrm{sc}^1$ with $Df(x)$ the derivative of $f : U_0 \to F_0$
within $U$ at $\iota_1 x$; and if $f$ maps $U_m$ into $F_m$ for every $m$ and every $f_m$ is
$C^\infty$, then $f$ is sc-smooth. *Book:* p. 13: if $f : U_{m+l} \to F_m$ is $C^{l+1}$ for all
$m \ge 0$ and $0 \le l \le k$, then $f$ is $\mathrm{sc}^{k+1}$. *Hidden hypotheses:* none
("$f$ induces a map $U_{m+l} \to F_m$" is the $\mathrm{sc}^0$ hypothesis). *Deviation:* none; the
sc-smooth statement is a direct consequence. *Proof:* the 2010 paper's (Proposition 2.4): $f$ is
the elementary map with no vectors, and every elementary map with $j$ vectors and $j + s \le k + 1$
is $\mathrm{sc}^s$ (V1.38), with the derivatives $d^jf(x)$ supplied by the derivative tower of $f$
(V1.37). The induction cannot be run on the hypothesis itself: if $f$ satisfies it with $k$, then
$Tf$ in general does not satisfy it with $k - 1$, since its second component $(x, h) \mapsto
Df(x)h : U_{m+l+1} \times E_{m+l} \to F_m$ is only $C^l$. Under the stronger hypothesis the level
maps of $Tf$ are $C^k$ and the induction is immediate.

**V1.19 (Corollary 1.20; `Polyfold.corollary_1_20_text`,
`Polyfold.IsScSmooth.of_contDiffOn_levels_finiteDimensional_text`,
`Polyfold.IsScSmooth.of_contDiffOn_finiteDimensional`, `Polyfold.corollary_1_20_zero`,
`Polyfold.corollary_1_20`, `Polyfold.corollary_1_20_base`).** Let $U$ be an sc-domain in $E$, $V$
a finite-dimensional normed space with its constant sc-structure and $f : E_0 \to V$. If for some
$k$ and all $0 \le l \le k$ the map $f \circ \iota_l : U_l \to V$ is $C^{l+1}$ within $U_l$, then
$f$ is $\mathrm{sc}^{k+1}$ on $U$. If $f \circ \iota_l$ is $C^{l+1}$ within $U_l$ for every $l$,
then $f$ is sc-smooth; if $f$ is $C^\infty$ within $U$, then $f$ is sc-smooth. Also proved, under
the stronger hypothesis: if $f \circ \iota_m$ is $C^{k+1}$ within $U_m$ for every $m$, in
particular if $f$ is $C^{k+1}$ within $U$, then $f$ is $\mathrm{sc}^{k+1}$; for $k = 0$ this is the
text's hypothesis. *Book:* p. 13: if $f : U_l \to \mathbb R^N$ is $C^{l+1}$ for $0 \le l \le k$
then $f$ is $\mathrm{sc}^{k+1}$. *Hidden hypotheses:* none; no $\mathrm{sc}^0$ hypothesis is
needed, since $f \circ \iota_m$ is the continuous $f \circ \iota_0$ composed with an inclusion.
*Deviation:* none ($\mathbb R^N$ is any finite-dimensional space); the two sc-smooth statements are
the exposition's additions. *Proof:* Proposition 1.19 (V1.18) for the constant structure, the
hypothesis on $U_{m+l} \to V$ being the restriction of the one on $U_l$.

**V1.20 (Theorem 1.21, the chain rule; `Polyfold.IsSc1With.hasFDerivWithinAt_comp`,
`Polyfold.IsSc1With.comp`, `Polyfold.theorem_1_21'`, `Polyfold.theorem_1_21`, `Polyfold.IsSck.comp`,
`Polyfold.IsSck.comp_of_isRelOpenInQuadrant`, `Polyfold.IsScSmooth.comp`).** Let $U \subseteq C
\subseteq E$ and $V \subseteq D \subseteq F$ be relatively open subsets of partial quadrants, $G$
an sc-Banach space, $f : E_0 \to F_0$ $\mathrm{sc}^1$ on $U$ with $f(U) \subseteq V$, and $g : F_0
\to G_0$ $\mathrm{sc}^1$ on $V$. Then $g \circ f$ is $\mathrm{sc}^1$ on $U$, and $T(g \circ f) = Tg
\circ Tf$ on $TU$. More precisely: if $g$ is $\mathrm{sc}^1$ on $V$ with derivatives $Dg$, $f$ is
$\mathrm{sc}^1$ on $U$ with derivatives $Df$, $f(U) \subseteq V$, and $V_1$ is the intersection of
an open and a convex set, then $g \circ f$ is $\mathrm{sc}^1$ on $U$ with derivatives $x \mapsto
Dg(f_1(x)) \circ Df(x)$, with no hypothesis on $U$; and $g \circ f \circ \iota_1$ has this derivative
at every $x \in U_1$ within $U_1$. Iterated: if $U$, $V$ are sc-domains (in particular relatively
open subsets of partial quadrants), $f$ $\mathrm{sc}^k$ on $U$ with $f(U) \subseteq V$ and $g$
$\mathrm{sc}^k$ on $V$, then $g \circ f$ is $\mathrm{sc}^k$ on $U$; sc-smooth maps compose to
sc-smooth maps. *Book:* p. 13, with a third tuple $W \subset Q \subset G$ for the target of $g$;
the proof is §1.4.2, pp. 15–16. *Hidden hypotheses:* the segment from $f(x)$ to $f(x+h)$ lies in
$V_1$ for $|h|_1$ small, which uses the convexity of $D_1$, the openness of $V_1$ in $D_1$ and the
continuity of $f : U_1 \to F_1$; the uniqueness of $D(g \circ f)(x)$ behind "$T(g \circ f) = Tg
\circ Tf$". *Deviation:* none in the statement; $W \subset Q \subset G$ plays no role. *Proof:* the
text's two integrals are replaced by the mean value inequality for $t \mapsto g(y_t) - t\,Dg(f(x))
(f(x+h) - f(x))$ on $[0, 1]$; the first integral is not needed since $Dg(f(x))$ is bounded on
$F_0$; the uniform convergence on the compact closure of $\{Df(x)h/|h|_1\}$ is Mathlib's
`IsCompact.eventually_forall_of_forall_eventually` rather than a subsequence argument. The text's
appeal to Proposition 1.18 is not used.

**V1.21 (Definition 1.23; `Polyfold.quadrantDeg`, `Polyfold.degIndexWith`, `Polyfold.degIndex`,
`Polyfold.degIndex_eq`, `Polyfold.degIndex_quadrant`).** For $p = (a, w) \in \mathbb R^n \oplus W$
let $\#(p)$ be the number of $i$ with $a_i = 0$; for an sc-isomorphism $T : E \to \mathbb R^n \oplus
W$ presenting a partial quadrant $C$ let $d_T(x) := \#(T_0 x)$. The *degeneracy index* $d_C : E_0
\to \mathbb N$ is $d_T$ for a chosen presentation $T$ of $C$ (and $0$ if $C$ is not a partial
quadrant); for every presentation $T$ and every $x \in C$, $d_C(x) = d_T(x)$. On the quadrant
itself $d(p) = \#(p)$. *Book:* p. 14: $d_C(x) = \#\{i : a_i = 0\}$ where $T(x) = (a_1, \dots, a_k,
w)$; interior points, boundary points and corners. *Hidden hypotheses:* none. *Deviation:* none;
$d_C$ is total on $E_0$ with junk values off $C$, and the classification into interior, boundary
and corner points is terminology.

**V1.22 (Lemma 1.24; `Polyfold.quadrantDeg_eq_of_equiv`, `Polyfold.lemma_1_24`,
`Polyfold.lemma_1_24_dim`).** Let $T : E \to \mathbb R^n \oplus W$ and $T' : E \to \mathbb R^{n'}
\oplus W'$ be sc-isomorphisms with $C = T_0^{-1}(Q_n) = T_0'^{-1}(Q_{n'})$. Then $d_T(x) =
d_{T'}(x)$ for every $x \in C$, and $n = n'$. Core: if $S : \mathbb R^n \times W_0 \to \mathbb
R^{n'} \times W'_0$ is a continuous linear equivalence with $q \in Q_n \iff Sq \in Q_{n'}$, then
$\#(p) = \#(Sp)$ for every $p \in Q_n$. *Book:* p. 14, "$d_C$ does not depend on the choice of
$T$", proof on p. 17. *Hidden hypotheses:* none; the proof uses only linear algebra on level $0$.
*Proof:* the text's, except that $k = k'$ is not proved first but derived from the lemma at $x =
0$; the codimension of $E_x$ is $\dim(V/E_x) = \#I(x)$ with $E_x = \ker((b, v) \mapsto (b_i)_{i \in
I(x)})$, and "$S(E_x) \subset E'_y$ hence equality" is completed by the same inclusion for $S^{-1}$.

**V1.23 (Theorem 1.25, boundary recognition; `Polyfold.theorem_1_25`, `Polyfold.theorem_1_25_lvl1`,
`Polyfold.degIndexWith_le_of_germ`, `Polyfold.eventually_degIndexWith_le`,
`Polyfold.exists_tendsto_lvl1_degIndexWith`, `Polyfold.IsSc1With.mapsTo_minimalSubspace`).** Let $U
\subseteq C \subseteq E$ and $U' \subseteq C' \subseteq E'$ be relatively open subsets of partial
quadrants, $f : E_0 \to E'_0$ $\mathrm{sc}^1$ on $U$ with $f(U) \subseteq U'$, $g : E'_0 \to E_0$
$\mathrm{sc}^1$ on $U'$ with $g(U') \subseteq U$, $g(f(x)) = x$ for $x \in U$ and $f(g(y)) = y$ for
$y \in U'$. Then $d_C(x) = d_{C'}(f(x))$ for every $x \in U$. Ingredients: $d_{C'}$ is upper
semicontinuous ($d_{C'}(y') \le d_{C'}(y)$ for $y'$ near $y$); every $x \in C$ is a limit of points
of $C$ on level $1$ with the same index; and for $x \in U_1$ the derivative $Df(x)$ maps $E_x :=
\{v : (T_0 v)_i = 0 \text{ whenever } (T_0 x)_i = 0\}$ into $E'_{f(x)}$, from which $d_C(x) \le
d_{C'}(f(x))$ follows by comparing codimensions through the chain rule. *Book:* p. 14: for tuples
$(U, C, E)$, $(U', C', E')$ and a germ $f : (U, x) \to (U', x')$ of a local sc-diffeomorphism,
$d_C(x) = d_{C'}(f(x))$; no proof, a reference to "[20], Theorem 1.19". *Hidden hypotheses:* the
notion "germ of a local sc-diffeomorphism", undefined in Chapter 1, read as an $\mathrm{sc}^1$ map
$f : U \to U'$ with $\mathrm{sc}^1$ inverse $g : U' \to U$ on relatively open neighbourhoods $U$,
$U'$ of $x$, $f(x)$ (which may be shrunk at will). *Deviation (stronger):* only $\mathrm{sc}^1$ is
required of $f$ and $g$, where the text has sc-smooth. *Proof:* the argument of §2.3 (Lemma 2.29,
Theorem 2.31, Corollary 2.32) for the identity retraction, with level-$1$ points in place of smooth
points; the Lean file is `Polyfold/Chapter2/DegeneracyIndex.lean`.

**V1.24 (Fredholm operators between Banach spaces, Riesz–Schauder;
`Polyfold.isStrictMap_of_isClosed_range`, `Polyfold.isFredholm_of_banach`,
`Polyfold.isCompactOperator_of_finiteDimensional_range`, `Polyfold.finiteDimensional_ker_one_add`,
`Polyfold.isClosed_range_one_add`, `Polyfold.coFG_range_one_add`, `Polyfold.isFredholm_one_add`).**
Let $E$, $F$ be real Banach spaces. A continuous linear $u : E \to F$ with closed range is a strict
map; if moreover $\ker u$ is finite-dimensional and $\operatorname{range} u$ has finite
codimension, $u$ is a Fredholm operator in Mathlib's sense. A continuous linear map of finite rank
is a compact operator. For a compact operator $c : E \to E$: $\ker(1 + c)$ is finite-dimensional,
$\operatorname{range}(1 + c)$ is closed and of finite codimension, and $1 + c$ is Fredholm. *Book:*
not stated; used in §1.4.1, p. 14 ("$T + S : E_m \to F_m$ is Fredholm", "its image $Y$ is
closed"). *Deviation (not in the book):* infrastructure Mathlib v4.33.1 lacks.

**V1.25 (compact perturbations of Fredholm operators;
`Polyfold.isFredholm_add_isCompactOperator`).** Let $E$, $F$ be real Banach spaces, $u : E \to F$
Fredholm and $k : E \to F$ compact. Then $u + k$ is Fredholm. *Book:* not stated; the first line of
§1.4.1. *Deviation (not in the book):* infrastructure; the invariance of the index, which the
exposition records (Kato IV.5.26) and the text does not, is V1.28.

**V1.26 (the compact-open lemma and the level operators;
`Polyfold.exists_delta_of_continuousOn`, `Polyfold.continuousOn_clm_comp_of_isCompactOperator`,
`Polyfold.contDiffOn_clm_comp_of_isCompactOperator`, `Polyfold.levelDeriv`,
`Polyfold.IsSc1With.exists_levelDeriv`, `Polyfold.IsSc1With.toBase_levelDeriv`,
`Polyfold.IsSc1With.levelMap_tangentMapWith`, `Polyfold.IsSc1With.continuousOn_levelDeriv`,
`Polyfold.IsSc1With.continuousOn_levelDeriv_clm`, `Polyfold.IsSc1With.hasFDerivWithinAt_level`,
`Polyfold.IsSc1With.contDiffOn_level`, `Polyfold.IsSc1With.levelDeriv_eq`).** *Compact-open lemma.*
Let $X$, $Y$, $Y'$, $Z$ be real normed spaces, $\iota : Y' \to Y$ a compact operator and $A : X \to
\mathcal L(Y, Z)$. If $(x, y) \mapsto A(x)y$ is continuous on $s \times Y$, then $x \mapsto A(x)
\circ \iota$ is continuous on $s$ into $\mathcal L(Y', Z)$ with the operator norm; if $s$ is the
intersection of an open and a convex set with unique differentiability at every point and $(x, y)
\mapsto A(x)y$ is $C^k$ within $s \times Y$, then $x \mapsto A(x) \circ \iota$ is $C^k$ within $s$.
*Level operators.* Let $f$ be $\mathrm{sc}^1$ on $U$ with derivatives $Df$, $m \in \mathbb N$ and $x
\in U_{m+1}$. There is a unique continuous linear $Df(x) : E_m \to F_m$ (written `levelDeriv`) with
$\iota_m \circ Df(x) = Df(\iota x) \circ \iota_m$, namely the second component of the level-$m$
tangent map, which is $(x, h) \mapsto (f_{m+1}(x), Df(x)h)$ on $U_{m+1} \times E_m$; $(x, h) \mapsto
Df(x)h$ is continuous on $U_{m+1} \times E_m$; $x \mapsto Df(x) \circ \iota$ is continuous $U_{m+1}
\to \mathcal L(E_{m+1}, F_m)$. If $U$ is an sc-domain, $f_m \circ \iota : U_{m+1} \to F_m$ has
derivative $Df(x) \circ \iota$ at $x$ within $U_{m+1}$, hence is $C^1$ within $U_{m+1}$; and if
$f_m : U_m \to F_m$ has derivative $L$ at $\iota x$ within $U_m$, then $L = Df(x)$. *Book:* not
stated as such; the compactness argument of the 2010 paper's Propositions 2.1–2.3 (quoted in §1.2)
and its integral identity $f(x+h) - f(x) = \int_0^1 Df(x + \tau h)h\,d\tau$. *Deviation (not in the
book):* the $C^k$ case of the lemma, proved by induction with the mean value inequality, replaces
the multilinear maps $\Gamma(x)$ and the differentiation under the integral sign of the 2010
paper; the integral identity is formed as a Bochner integral in $F_m$ and identified with $f(x+h) -
f(x)$ by the fundamental theorem of calculus for the $C^1$ map $f : U_1 \to F_0$.

**V1.27 (sc-domains; `Polyfold.IsScDomain`, `Polyfold.IsRelOpenInQuadrant.isScDomain`,
`Polyfold.IsScDomain.tangentSet`, `Polyfold.IsScDomain.shift`).** $U \subseteq E_0$ is an
*sc-domain* if for every $m$ the level set $U_m$ is the intersection of an open and a convex subset
of $E_m$, and $U_m$ has unique differentiability at each of its points. A relatively open subset of
a partial quadrant is an sc-domain; if $U$ is an sc-domain, so are $TU$ in $TE$ and $U_1$ in $E^1$.
*Book:* not stated; the text works with tuples $(U, C, E)$ and asserts that $T(U, C, E)$ is a tuple.
*Deviation (not in the book):* the level-wise regularity that the proofs of §§1.2–1.3 use, stable
under the tangent construction and the level shift, stated in place of the tuple.

**V1.28 (the Fredholm index and its invariance; `Polyfold.linIndex`, `Polyfold.HasFiniteIndex`,
`Polyfold.linIndex_comp`, `Polyfold.linIndex_eq_zero_of_finiteRange_sub_id`,
`Polyfold.HasFiniteIndex.of_bijective_add_and_linIndex`,
`Polyfold.HasFiniteIndex.of_comp_of_comp`, `Polyfold.fredholmIndex`,
`Polyfold.IsFredholm.hasFiniteIndex`, `Polyfold.fredholmIndex_add_of_norm_lt`,
`Polyfold.fredholmIndex_add_isCompactOperator`).** For a linear map $u : E \to F$ over a field let
$\operatorname{ind}(u) := \dim\ker u - \dim(F/\operatorname{range}u) \in \mathbb Z$, meaningful when
both dimensions are finite ("finite index"). If $u$ and $v : F \to G$ have finite index, so has $v
\circ u$, and $\operatorname{ind}(v \circ u) = \operatorname{ind}(u) + \operatorname{ind}(v)$. If $a$
is bijective and $r$ has finite rank, $a + r$ has finite index $0$ (in particular $1 + r$). If $v
\circ u$ and $u \circ v$ have finite index, so has $u$. For real Banach spaces $E$, $F$: a Fredholm
operator $u : E \to F$ has finite index, and $\operatorname{ind}(u)$ is its *Fredholm index*. If $v
: F \to E$ is a quasi-inverse of $u$ ($vu - 1$ and $uv - 1$ have finite rank) and $\|v\|\,\|s\| < 1$,
then $u + s$ has finite index and $\operatorname{ind}(u + s) = \operatorname{ind}(u)$. If $u$ is
Fredholm and $k : E \to F$ is compact, then $\operatorname{ind}(u + k) = \operatorname{ind}(u)$.
*Book:* not stated; the classical fact behind the exposition's (F2) (Kato IV.5.26), which the text's
§1.4.1 would need to conclude that the index is preserved. *Deviation (not in the book):*
infrastructure Mathlib v4.33.1 lacks (it has Fredholm operators but no index). *Proof:*
additivity by rank–nullity along the exact sequence $0 \to \ker u \to \ker vu \to \operatorname{range}
u \cap \ker v \to F/\operatorname{range}u \to G/\operatorname{range}vu \to G/\operatorname{range}v
\to 0$; small perturbations through $v(u + s) = (1 + vs) + (vu - 1)$ and $(u+s)v = (1 + sv) + (uv -
1)$, where $1 + vs$, $1 + sv$ are invertible by the Neumann series; compact perturbations by the local
constancy of $t \mapsto \operatorname{ind}(u + tk)$ on $\mathbb R$ (each $u + t_0k$ is Fredholm by
V1.25), not by Kato's argument.

**V1.29 (Lemma 2.D, the level operators of an sc-Fredholm operator;
`Polyfold.ScFredholmSplitting.C_le_smooth`, `Polyfold.ScBanach.finrank_levelSub_of_le_smooth`,
`Polyfold.ScFredholmSplitting.fredholmIndex_lvl`, `Polyfold.IsScFredholm.fredholmIndex_lvl`,
`Polyfold.scIndex_eq_fredholmIndex`).** Let $T : E \to F$ be an sc-operator with an sc-Fredholm
splitting $(K, X, C, Y)$ (V1.7). Then $C \le F_\infty$ (and $K \le E_\infty$, V1.7); a subspace $A \le
E_\infty$ has $\dim A_m = \dim A$ for every $m$; and for every $m$ the level map $T_m : E_m \to F_m$
is a Fredholm operator with $\operatorname{ind}(T_m) = \dim K - \dim C$. Hence for an sc-Fredholm
$T$, $\operatorname{ind}(T_m) = \operatorname{ind}(T) := \dim\ker T_0 - \dim(F_0/\operatorname{range}
T_0)$ for every $m$; the latter is the Fredholm index of $T_0$. *Book:* p. 9, after Definition 1.8:
$K \subset E_\infty$, $T(X_m) = Y_m$, $E_m = K \oplus X_m$, "$F = C \oplus T(E_m)$"; the level-wise
index is not stated. *Hidden hypotheses:* none. *Deviation (stronger):* the Fredholm property and
the index on every level are added (the exposition's Lemma 2.D). *Proof:* $\ker T_m = K_m \cong K$
and $F_m/\operatorname{range}T_m = F_m/Y_m \cong C_m \cong C$, the isomorphisms $A_m \cong A$ coming
from $A \le E_\infty$.

**V1.30 (Proposition 1.10, the index; `Polyfold.proposition_1_10_index`,
`Polyfold.proposition_1_10_index_lvl`).** Let $T : E \to F$ be sc-Fredholm and $S : E \to F$ an
$\mathrm{sc}^+$-operator. Then $\operatorname{ind}(T + S) = \operatorname{ind}(T)$, the index being
$\dim\ker(\cdot)_0 - \dim\operatorname{coker}(\cdot)_0$; and for every $m$ the level map $(T + S)_m :
E_m \to F_m$ is Fredholm of index $\operatorname{ind}(T)$. *Book:* p. 10, Proposition 1.10 states
only that $T + S$ is sc-Fredholm (V1.9). *Hidden hypotheses:* none. *Deviation (stronger):* the
index statement is the exposition's addition. *Proof:* on level $0$, $T_0$ is Fredholm (V1.7) and
$S_0$ compact (V1.3), so V1.28 applies; on level $m$, V1.29 for the sc-Fredholm operator $T + S$
(V1.9).

**V1.31 (finite-dimensional spaces; `Polyfold.ScBanach.smooth_eq_top_of_finiteDimensional`,
`Polyfold.ScBanach.toBase_bijective_of_finiteDimensional`,
`Polyfold.ScBanach.isoConstOfFiniteDimensional`,
`Polyfold.ScScale.finiteDimensional_of_surjective_incl`).** Let $E$ be an sc-Banach space with $E_0$
finite-dimensional. Then every point of $E_0$ is smooth, every $\iota_m : E_m \to E_0$ is bijective,
and the maps $\iota_m$ form an sc-isomorphism of $E$ onto $E_0$ with its constant structure. For a
scale $E$ (no density assumed) and any $m$: if the inclusion $E_{m+1} \to E_m$ is surjective, then
$E_m$ is finite-dimensional. *Book:* p. 6, after Definition 1.1: a finite-dimensional Banach space has
precisely one sc-structure, the constant one; on an infinite-dimensional space the constant
structure is not an sc-structure, because the inclusions are not compact. *Hidden hypotheses:* none.
*Deviation (restated):* "precisely one" is read, for the indexed families of V1.1, as "sc-isomorphic
to the constant structure by the inclusions" (so the level norms are all equivalent), and "the
constant structure fails (1)" as "an onto inclusion forces finite dimension". *Proof:* $E_\infty$ is
a dense, hence (finite dimension) closed, hence full subspace of $E_0$; an onto compact inclusion is
an isomorphism (open mapping theorem), so the identity of $E_m$ is compact.

**V1.32 (sc-splittings are sc-projections; `Polyfold.ScBanach.IsScSplitting.isTopCompl`,
`Polyfold.ScBanach.IsScSplitting.scProj`, `Polyfold.ScBanach.IsScSplitting.scProj_idem`,
`Polyfold.ScBanach.IsScSplitting.range_scProj`, `Polyfold.ScBanach.IsScSplitting.ker_scProj`,
`Polyfold.ScOperator.idem_lvl`, `Polyfold.ScOperator.levelSub_range_eq`,
`Polyfold.ScBanach.isScSplitting_of_idem`, `Polyfold.ScBanach.isScSplitting_iff_exists_scProj`).** Let
$A, B \subseteq E_0$. If $E = A \oplus B$ is an sc-splitting, then on every level $A_m$, $B_m$ are
topological complements, and the continuous projections of $E_m$ onto $A_m$ along $B_m$ form an
sc-operator $P : E \to E$ with $P_m^2 = P_m$, $P_m(E_m) = A_m$ and $\ker P_m = B_m$. Conversely, if $P
: E \to E$ is an sc-operator with $P_0^2 = P_0$, then $P_m^2 = P_m$ and $(P_0(E_0))_m = P_m(E_m)$ for
every $m$, and $E = P_0(E_0) \oplus \ker P_0$ is an sc-splitting. Hence $E = A \oplus B$ is an
sc-splitting iff some sc-operator $P$ with $P_0^2 = P_0$ has range $A$ and kernel $B$. *Book:* pp.
7–8: the definition of an sc-splitting, and in the proof of Proposition 1.6 the step "since $P \circ
P = P$, it is a sc-projection" with $G := (1 - P)(E)$. *Hidden hypotheses:* none. *Deviation
(hypotheses explicit):* the equivalence the text uses is stated and proved (the exposition's Lemma
2.B); $\ker P_0$ is the text's $(1 - P)(E)$. The formal Proposition 1.6 (V1.5) does not depend on it.

**V1.33 (the smooth points of a quotient; `Polyfold.ScBanach.exists_smooth_mem_coset`,
`Polyfold.ScBanach.mk_mem_quotient_smooth_iff`).** Let $A$ be an sc-subspace of $E$ and $x \in E_0$.
If for every $j$ there is $y_j \in E_j$ with $\iota_j y_j - x \in A$, then there is $y \in E_\infty$
with $y - x \in A$. Equivalently: the class of $x$ is a smooth point of the quotient $E/A$ (V1.6) if
and only if $x + A$ contains a smooth point of $E$. *Book:* p. 9, in the proof of Proposition 1.7:
"$(E/A)_\infty$ consists of all elements of the form $x + A_\infty$ with $x \in E_\infty$".
*Hidden hypotheses:* that $A$ is an sc-subspace (the density of $A_\infty$ in every $A_j$) is used;
the text has it. *Deviation:* none. *Proof:* a Mittag-Leffler construction (the exposition's Lemma
2.C), with $\prod_{i<j}\max(1, \|E_{i+1} \to E_i\|)$ bounding all the inclusions $E_j \to E_i$, $i \le
j$.

**V1.34 (continuity of $Df$ for the compact-open topology;
`Polyfold.continuousOn_apply_iff_uniformOnCompact`, `Polyfold.IsSc1With.deriv_uniformOnCompact`,
`Polyfold.exists_isSc1_not_continuousOn_deriv`).** Let $X$ be a metric space, $Y$, $Z$ real normed
spaces, $s \subseteq X$ and $A : X \to \mathcal L(Y, Z)$. Then $(x, h) \mapsto A(x)h$ is continuous
on $s \times Y$ if and only if for every $x \in s$, every compact $K \subseteq Y$ and every
$\varepsilon > 0$ there is a neighbourhood of $x$ in $s$ on which $\|A(x')w - A(x)w\| < \varepsilon$
for all $w \in K$. Applied to an $\mathrm{sc}^1$ map with derivatives $Df$: $x \mapsto Df(x)$ is
continuous on $U_1$ for the topology of uniform convergence on compact subsets of $E_0$. There is an
$\mathrm{sc}^1$ map on a relatively open subset of a partial quadrant for which no derivative family
is continuous on $U_1$ into $\mathcal L(E_0, F_0)$ with the operator norm (the example of V1.13).
*Book:* p. 11: $x \mapsto Df(x)$ is in general not continuous for the operator norm, but it is
continuous for the compact-open topology. *Hidden hypotheses:* none. *Deviation (restated):* the
compact-open topology on $\mathcal L(Y, Z)$ is written out as uniform convergence on compact sets,
and the remark becomes an equivalence with level $0$ of condition (3) of Definition 1.14 (the
exposition's Lemma 3.F). The negative half of the remark is proved by a sequence-space example
(V1.13), not by the shift map of the exposition's §6, which needs weighted Sobolev spaces.

**V1.35 (finite dimensions: sc¹ is $C^1$, also at the boundary; `Polyfold.ScBanach.lvlSet_const`,
`Polyfold.isSc1_iff_contDiffOn_const`, `Polyfold.isSc1_iff_fderivWithin_const`,
`Polyfold.isScSmooth_iff_contDiffOn_const`, `Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant`,
`Polyfold.isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant`).** Let $V$, $W$ be finite-dimensional
real normed spaces with their constant sc-structures, $f : V \to W$ and $U \subseteq V$ an sc-domain
(V1.27), for instance a relatively open subset of a partial quadrant of $V$. Then $f$ is
$\mathrm{sc}^1$ on $U$ if and only if $f$ is $C^1$ within $U$; equivalently, $f$ is differentiable
within $U$ at every point of $U$ and the derivative within $U$, $x \mapsto \mathrm{fderivWithin}\,f\,U\,x$,
is continuous on $U$. And $f$ is sc-smooth on $U$ if and only if it is $C^\infty$ within $U$. *Book:*
p. 11: "the $\mathrm{sc}^1$-maps between finite dimensional Banach spaces are the familiar
$C^1$-maps". *Hidden hypotheses:* the meaning of $C^1$ at boundary points of a quadrant, never
defined in the text; here the derivative within $U$, which at a boundary point is the one-sided
derivative along $U$ and is unique because the quadrant has non-empty interior. *Deviation
(hypotheses explicit):* none beyond this; by V1.31 every sc-structure on a finite-dimensional space
is the constant one up to sc-isomorphism. *Proof:* Propositions 1.16 and 1.19 at $k = 0$ (V1.15,
V1.18) for the levels of the constant structure, which all equal $U$.

**V1.36 (level shifts and tangents of tuples; `Polyfold.ScIso.shift`,
`Polyfold.IsPartialQuadrant.shift`, `Polyfold.IsRelOpenInQuadrant.shift`,
`Polyfold.tangentQuadrantIso`, `Polyfold.IsPartialQuadrant.tangentSet`,
`Polyfold.IsRelOpenInQuadrant.tangentSet`, `Polyfold.ScBanach.shift_tangentSet`).** Let $C$ be a
partial quadrant in $E$, presented by an sc-isomorphism $T : E \to \mathbb R^n \oplus W$. Then $C_1$
is a partial quadrant in $E^1$, presented by the level shift $T^1 : E^1 \to \mathbb R^n \oplus W^1$;
and $TC = \{(x, h) \in E_1 \times E_0 : x \in C_1\}$ is a partial quadrant in $TE$, presented by
$(x, h) \mapsto (a, (w, T_0h))$ where $T_1x = (a, w)$, an sc-isomorphism $TE \to \mathbb R^n \oplus
(W^1 \oplus (\mathbb R^n \oplus W))$. If $U$ is relatively open in $C$, then $U_1$ is relatively open
in $C_1$ and $TU$ in $TC$; and the level-$1$ part of $TU$ is $T(U_1)$. *Book:* p. 10, after
Definition 1.13: "$T(U, C, E)$ is a tuple consisting again of a relatively open subset $TU$ in the
partial quadrant $TC$"; the corresponding fact for $C^1 \subset E^1$ is used without being stated.
*Hidden hypotheses:* none. *Deviation:* none; $C^k$ for $k \ge 2$ is the iterate. These are the
exposition's Lemmas 3.A(2) and 3.B, proved in the Chapter 2 files
(`Polyfold/Chapter2/LevelPolyfold.lean`, `Polyfold/Chapter2/TangentBundle.lean`).

**V1.37 (the derivative tower; `Polyfold.IsDerivTower`, `Polyfold.levelDerivTower`,
`Polyfold.baseDerivTower`, `Polyfold.contDiffOn_levels_min`, `Polyfold.levelDerivTower_toBase`,
`Polyfold.baseDerivTower_toBase`, `Polyfold.isDerivTower_of_contDiffOn_levels`,
`Polyfold.IsDerivTower.eq_of_toBase`).** A derivative tower of order $k + 1$ for $f : E_0 \to F_0$
on $U$ consists of maps $\Phi_i : E_0 \times E_0^i \to F_0$ with $\Phi_0(x) = f(x)$ and, for $x \in
U_{m+l}$, continuous $i$-linear maps $\Psi_{i,m,l}(x) : E_{m+l}^i \to F_m$, for $i \le l + 1$ and $i
\le k + 1$, such that (a) $\iota_m \Psi_{i,m,l}(x)(h_1, \dots, h_i) = \Phi_i(\iota_{m+l} x)(\iota_{m+l}
h_1, \dots, \iota_{m+l} h_i)$; (b) $\Psi_{i,m,l}$ is continuous on $U_{m+l}$ into the space of
continuous $i$-linear maps; (c) for $i \le l$ and $i \le k$, $\Psi_{i,m,l}$ is differentiable within
$U_{m+l}$ at every point, with derivative $\xi \mapsto \Psi_{i+1,m,l}(x)(\xi, \cdot)$. If $U$ is an
sc-domain, $f$ is $\mathrm{sc}^0$ on $U$ and $f_m \circ \iota : U_{m+l} \to F_m$ is $C^{l+1}$ within
$U_{m+l}$ for all $m$ and $l \le k$, then the iterated derivatives within the level sets,
$\Psi_{i,m,l} := d^i(f_m \circ \iota)$ on $U_{m+l}$ and $\Phi_i$ the $i$-th derivative of $f : U_{i-1}
\to F_0$ at lifts to $E_{i-1}$, form a derivative tower of order $k + 1$. In a tower, two values
$\Psi_{i,m,l}(x)(h)$, $\Psi_{i,m,l'}(x')(h')$ with the same images in $E_0$ are equal. *Book:* not
stated; the 2010 paper's proof of Proposition 2.4 (pp. 51–53) writes one symbol $d^jf(x)$ for the
derivatives on all level pairs. *Hidden hypotheses:* the compatibility (a) is the identification the
text makes tacitly. *Deviation (not in the book):* a tool of the formalization. *Proof:* (a) from
the chain rule for iterated derivatives within a set composed on the left and on the right with
continuous linear maps (the inclusions), and the uniqueness of derivatives on the level sets; for
$l > k$ the hypothesis is used with order $k + 1$, restricted from $U_{m+k}$.

**V1.38 (elementary maps and the induction $(\mathrm S_k)$; `Polyfold.ElemData`,
`Polyfold.ElemData.Good`, `Polyfold.ElemData.dom`, `Polyfold.ElemData.map`,
`Polyfold.ElemData.map_toBase`, `Polyfold.ElemData.levelMap_eq`, `Polyfold.ElemData.isSc0`,
`Polyfold.ElemData.deriv`, `Polyfold.ElemData.hasFDerivWithinAt_level`,
`Polyfold.ElemData.continuousOn_deriv`, `Polyfold.ElemData.isSc1Levels`,
`Polyfold.ElemData.isSc1With`, `Polyfold.ElemData.shiftData`, `Polyfold.ElemData.derivData`,
`Polyfold.ElemData.slotData`, `Polyfold.ElemData.tangentMap_eqOn`, `Polyfold.ElemData.isSck`,
`Polyfold.ElemData.base`, `Polyfold.ScBanach.shiftAdd`, `Polyfold.ScBanach.shiftAddZeroIso`,
`Polyfold.ScBanach.shiftAddShiftIso`).** Fix a derivative tower of order $k + 1$ for $f$ on $U$
(V1.37), and write $E^p$ for the sc-Banach space with levels $(E^p)_l = E_{p+l}$ ($E \cong E^0$
and $(E^p)^1 \cong E^{p+1}$ as sc-Banach spaces). Elementary data on an sc-Banach space $X$ are an
sc-operator $\pi_0 : X \to E^p$, sc-operators $\pi_a : X \to E^{n_a}$ ($1 \le a \le i$) and a number
$m$; the elementary map is $g(z) = \Phi_i(\pi_0 z)(\pi_1 z, \dots, \pi_i z)$, a map $X \to F^m$, on
$W := \pi_0^{-1}(U_p)$. Assume $m + i \le p$, $m + i \le n_a + 1$ for all $a$, and $i \le k$. Then
$g$ is $\mathrm{sc}^0$ on $W$, its level-$l$ map being $\Psi_i$ on level $(m + l, i - 1)$ at the
slots. If $W$ is an sc-domain, $g$ is $\mathrm{sc}^1$ with
$$Dg(z)\zeta = d^{i+1}f(\pi_0 z)(\pi_0\zeta, \pi_1 z, \dots, \pi_i z) + \sum_{a=1}^i d^if(\pi_0
z)(\pi_1 z, \dots, \pi_a\zeta, \dots, \pi_i z),$$
and, if moreover $i + 1 \le k$, its tangent map on $TW$ is $(g', g_0 + \sum_a g_a)$, through $(F^m)^1 \cong F^{m+1}$ in the first
component, with $g'$ the
elementary map of the data $(\pi_0, \pi_a)$ taken on the first factor of $TX = X^1 \oplus X$ (levels
$p + 1$, $n_a + 1$, $m + 1$), $g_0$ the one with $i + 1$ vectors $(\pi_0\text{ on the second
factor}, \pi_a \text{ on the first})$ and target shift $m$, and $g_a$ the one with $\pi_a$ moved to
the second factor; all satisfy the three conditions. Finally, if $W$ is an sc-domain and $i + s \le
k + 1$, then $g$ is $\mathrm{sc}^s$ on $W$. *Book:* 2010 paper, Proposition 2.4, pp. 51–53, the
inductive statement $(\mathrm S_k)$: the components of $T^{k+1}f$ are linear combinations of
$d^jf(x)(h_1, \dots, h_j)$ on $U^{k+1} \oplus E^{n_1} \oplus \cdots \oplus E^{n_j} \to F^l$ with $j + l
- 1 \le n_i \le k$, each $\mathrm{sc}^1$ with the derivative (11), and those of $T^{k+2}f$ are again
of this form. *Hidden hypotheses:* the base-point condition $j + l \le k + 1$, which the text
derives from its bounds. *Deviation (not in the book):* the induction runs on $s$ over all
elementary maps on all $X$, not on the description of $T^{k+1}f$; the upper bound $n_i \le k$ is not
needed, and its consequences $j + l \le p$ and $j \le k$ are conditions of their own. *Proof:*
$\mathrm{sc}^1$ by the level criterion of Proposition 1.16 (V1.15): $Dg$ exists one level down
because $d^{i+1}f$ and $d^if$ do, by the derivative of the multilinear evaluation (V1.39);
$\mathrm{sc}^{s+1}$ from the tangent map, the pairing, the sum rule (V1.39) and the induction
hypothesis.

**V1.39 (sums of $\mathrm{sc}^k$ maps and the derivative of multilinear evaluation;
`Polyfold.IsSck.zero`, `Polyfold.IsSck.add`, `Polyfold.IsSck.sum`, `Polyfold.hasFDerivAt_cmm_eval`).**
Let $W$ be an sc-domain in $X$. The constant map $0$ is $\mathrm{sc}^k$ on $W$; if $g_1$, $g_2$ are
$\mathrm{sc}^k$ on $W$, so is $g_1 + g_2$; a finite sum of $\mathrm{sc}^k$ maps is $\mathrm{sc}^k$.
For continuous multilinear maps $A : \prod_a M_a \to Z$ between normed spaces, the evaluation $(A, h)
\mapsto A(h)$ is differentiable at every $(A, h)$ with derivative $(B, \eta) \mapsto B(h) + \sum_a
A(h_1, \dots, \eta_a, \dots)$. *Book:* not stated; the 2010 paper's proof of Proposition 2.4 uses
both (the terms of $\pi \circ T^{k+1}f$ treated one at a time, and the derivative (11)).
*Hidden hypotheses:* none. *Deviation (not in the book):* tools; only sums, not scalar multiples,
are needed. *Proof:* $g_1 + g_2$ is the sc-smooth addition $Y \oplus Y \to Y$ composed with the
pairing $(g_1, g_2)$ (`Polyfold.IsSck.scPair`), by the chain rule (V1.20); the sum by induction.

### What is not verified in this chapter

- pp. 6–7, Example 1.2: the weighted Sobolev spaces $H^{m,\delta_m}(\mathbb R \times S^1)$ as an
  sc-structure on $L^2$. Mathlib has no weighted Sobolev spaces and no Rellich–Kondrachov theorem;
  the exposition proves it (Proposition 1.C). Planned, with the shift map of the 2010 paper
  (exposition §6), as the project's step H2.
- p. 11, Remark 1.15: partial cones. Not formalized, as in the exposition.
- p. 11, after Definition 1.14: the text's own instance of a derivative that is not norm continuous,
  the shift map of the exposition's §6, needs the weighted Sobolev spaces of Example 1.2. The remark
  itself is verified, the negative half by a sequence-space example (V1.13, V1.34), the positive
  half by V1.34.

---

## 3. Chapter 2 (HWZ §§2.1–2.6): verified except Proposition 2.2 and Lemma 2.29 as stated; Remark 2.28's negative claim is false

Chapter 2 of Part I (preprint pp. 18–60) builds differential geometry on the images of sc-smooth
retractions. §2.1 defines retractions and retracts, proves that the tangent $TO = Tr(TU)$ does not
depend on the retraction (Proposition 2.4), defines sc-smooth maps between retracts and proves the
chain rule (Definitions 2.1–2.7, Proposition 2.6, Theorem 2.8). §2.2 glues retracts into
M-polyfolds, gives them a filtration $X_m$ and a tangent bundle $TX$, proves metrizability (Theorem
2.16, Proposition 2.19) and treats sub-M-polyfolds (Definitions 2.11–2.20, Proposition 2.21). §2.3
transports the degeneracy index to M-polyfolds and compares it with the tangent space (Definitions
2.22–2.27, Lemmas 2.23, 2.26, 2.29, Propositions 2.24, 2.30, Theorem 2.31, Corollary 2.32). §2.4
introduces tame retracts and the faces of tame M-polyfolds (Definitions 2.33–2.39, Propositions
2.35–2.46, with the products of M-polyfolds that Proposition 2.46 uses), §2.5 strong bundles
(Definitions 2.47–2.53, Proposition 2.54), and the appendix §2.6 proves Proposition 2.2, Theorem
2.16 and Proposition 2.19 with Smirnov's theorem (Theorem 2.55), Lemma 2.56 and Proposition 2.57.
Verified: every definition except 2.9 and 2.38 (which are given only in the forms the theory uses)
and every numbered result of §§2.1–2.3 and §2.5, with these exceptions: Proposition 2.2 (the
classical submanifold statement, motivation only), Lemma 2.29 in its path formulation (its content,
the sign arguments, is verified and Proposition 2.30 is proved from it), the openness of
$p : TX \to X_1$ in Proposition 2.19(2). The second statement of Theorem 2.31 (equality makes $C_xO$
a partial quadrant) is verified without its hypothesis, and **Remark 2.28's claim that $C_xO$ is in
general not a partial quadrant in $T_xO$ is false**: it is one at every smooth point of every
sc-smooth retract (V2.33), by Flor's theorem on nonnegative idempotent matrices, proved in the
needed case. Every numbered result of §2.4 is verified: Propositions 2.35, 2.36 (with "$C_xO$ is a
partial quadrant", which holds for every retract, V2.33), Lemma 2.40, Corollary 2.41, Propositions
2.42, 2.43 (the retraction onto a face, and the face as a tame sub-M-polyfold with $d_F = d_O - 1$),
2.44 (both sentences, the intersections of local faces included), Theorem 2.45 and Proposition 2.46
(fibred products, with the products of M-polyfolds it uses). In §2.5 the M-polyfold $Y[1]$, the
sc-smoothness of $P[1]$ and the chart-independence of $Y_{m,k}$ are verified, and the chart-wise
definition of sc⁺-sections is shown to be the text's; equivalence of atlases, of M-polyfolds and of
strong bundles, is an equivalence relation (V2.11, V2.57), strong bundle charts restrict to open
subsets of the base (V2.57), and the charts of a strong bundle depend only on its class of atlases
(V2.58). **Theorem 2.16 holds with the text's hypotheses**: the formal proof adds none, avoids Lemma
2.56 and Proposition 2.57 (which need a regularity of $X_m$ that the text does not check) and proves
Smirnov's theorem, which Mathlib lacks, in a pull-back form. Several statements are proved in a
stronger form: Propositions 2.30, 2.35 and Theorem 2.31 at points on level $1$ and for sc¹ germs,
Proposition 2.35 from condition (2) of tameness alone, Corollary 2.32 for every relatively open
subset of a partial quadrant, and Proposition 2.36's $d_O = d_C$ in the form "a tame chart realizes
$d_X$" for every M-polyfold.

The setting. Sc-Banach spaces and maps are those of Chapter 1. A *retraction* is a total map
$r : E_0 \to E_0$ with an explicit domain $U$; an *M-polyfold* is a Hausdorff paracompact space with
one sc-smooth atlas representing its class, and every notion is defined through the maximal atlas
of all charts compatible with it. Sc-smoothness between retracts quantifies over all retractions
onto the source (equivalent to the text's "one"). Where the text computes in the model
$C = [0, \infty)^k \oplus W$, the formal statements use a presentation $T : E \cong \mathbb R^n \oplus
W$ of $C$ and the coordinate functionals $\lambda_i = (T\,\cdot)_i$; the subspaces $E_x$, the cones
$C_x$ and tameness are defined through $T$. The tangent bundle $TX$ is a quotient of tuples
$(x, \varphi, h)$ with its topology and charts; its fibres $T_xX$ are sets, identified with
$T_{\varphi(x)}O$ by the charts, with no linear structure of their own. Theorem 1.25 of Chapter 1
(V1.23) is proved in `Polyfold/Chapter2/DegeneracyIndex.lean` by the argument of §2.3.

**V2.1 (sc-smooth retractions; `Polyfold.ScRetraction`, `Polyfold.ScRetraction.retract`,
`Polyfold.ScRetraction.mem_retract_iff`, `Polyfold.ScRetraction.apply_eq_self_of_mem_retract`,
`Polyfold.ScRetraction.lvlSet_retract_subset`, `Polyfold.ScRetraction.scDeriv_comp_self`).** Let $C$
be a partial quadrant in $E$. An *sc-smooth retraction* on $C$ consists of a set $U \subseteq E_0$
relatively open in $C$ and a map $r : E_0 \to E_0$ with $r(U) \subseteq U$, $r$ sc-smooth on $U$
and $r(r(x)) = r(x)$ for $x \in U$. Its *retract* is $O = r(U)$; $O \subseteq U$, $x \in O$ iff
$x \in U$ and $r(x) = x$, and $O_m \subseteq U_m$. For $x \in O_1$, $Dr(x) \circ Dr(x) = Dr(x)$.
*Book:* Definition 2.1, p. 18, and the remark after Definition 2.3, p. 19. *Hidden hypotheses:*
none. *Deviation:* none; the values of $r$ off $U$ play no role.

**V2.2 (sc-smooth retracts; `Polyfold.IsScRetract`, `Polyfold.ScRetraction.isScRetract`,
`Polyfold.ScRetraction.id`, `Polyfold.IsRelOpenInQuadrant.isScRetract`, `Polyfold.LocalModel`).**
$(O, C, E)$ is an *sc-smooth retract* if $O = r(U)$ for an sc-smooth retraction on $C$. A relatively
open $U \subseteq C$ is a retract ($r = \mathrm{id}$). A *local model* is a triple $(E, C, O)$ with
$C$ a partial quadrant and $O$ a retract in $C$. *Book:* Definition 2.3, p. 18. *Hidden
hypotheses:* none.

**V2.3 (Proposition 2.4; `Polyfold.proposition_2_4`,
`Polyfold.ScRetraction.comp_eq_self_of_retract_subset`,
`Polyfold.ScRetraction.tangent_subset_of_retract_subset`, `Polyfold.ScRetraction.tangent`,
`Polyfold.ScRetraction.mem_tangent_iff`).** For sc-smooth retractions $r$ on $U$ and $r'$ on $U'$,
both relatively open in $C$, with $r(U) = r'(U')$: $Tr(TU) = Tr'(TU')$. If only $r(U) \subseteq
r'(U')$, then $r' \circ r = r$ on $U$ and $Tr(TU) \subseteq Tr'(TU')$. A point $p$ lies in $Tr(TU)$
iff $p \in TU$ and $Tr(p) = p$. *Book:* Proposition 2.4, p. 19. *Hidden hypotheses:* the
composition $r' \circ r$ is defined because $O \subseteq U'$. *Proof:* as in the text, by Theorem
1.21 applied to $r' \circ r = r$.

**V2.4 (Definition 2.5, the tangent of a retract; `Polyfold.retractTangent`,
`Polyfold.retractTangent_eq`, `Polyfold.ScRetraction.mem_tangent_iff_exists`,
`Polyfold.ScRetraction.mem_tangent_iff_mem_range`, `Polyfold.tangentSpace`,
`Polyfold.tangentSpace_eq_range`, `Polyfold.tangentSpace_eq_coe_submodule`).** For a retract $O$,
$TO \subseteq E_1 \times E_0$ is $Tr(TU)$ for any retraction $r$ onto $O$ (V2.3);
$TO = \{(r(x), Dr(x)h) : x \in U_1, h \in E_0\}$, and for $x \in O_1$, $(x, h) \in TO$ iff $h$ is in
the range of $Dr(x)$. The tangent space $T_xO = \{h : (x, h) \in TO\}$ is this range, a closed
subspace of $E_0$. *Book:* Definition 2.5, p. 19, and Definition 2.17, p. 25 (the fibre $T_xO$).
*Hidden hypotheses:* none. *Deviation (restated):* $TO$ is defined for every subset $O$ by a choice
of retraction, and is empty if $O$ is not a retract.

**V2.5 (Proposition 2.6; `Polyfold.proposition_2_6_1`, `Polyfold.proposition_2_6_2`,
`Polyfold.proposition_2_6_3`, `Polyfold.ScRetraction.comp_comp_eqOn`).** Let $r$ on $U$ and $s$ on
$V$ be retractions onto the same $O$ and $f : E_0 \to E'_0$. (1) If $f \circ r$ is sc-smooth on $U$,
then $f \circ s$ is sc-smooth on $V$. (2) Then $T(f \circ r) = T(f \circ s)$ on $Tr(TU)$. (3) If
$f \circ r$ is sc-smooth and $f$ maps $O$ into the retract $O' = r'(U')$, then $T(f \circ r)$ maps
$Tr(TU)$ into $Tr'(TU')$. *Book:* Proposition 2.6, p. 20. *Hidden hypotheses:* in (3), $f(O)
\subseteq O'$ (contained in "$f : O \to O'$"). *Proof:* as in the text, with $f \circ r \circ s = f
\circ s$ and $\rho \circ f \circ r = f \circ r$ and Theorem 1.21.

**V2.6 (Definition 2.7, sc-smooth maps between retracts; `Polyfold.IsScSmoothRetractMap`,
`Polyfold.isScSmoothRetractMap_iff_exists`, `Polyfold.retractTangentMap`,
`Polyfold.retractTangentMap_eqOn`, `Polyfold.IsScSmoothRetractMap.tangentMap_mapsTo`,
`Polyfold.retractTangentMap_apply`, `Polyfold.IsScSmoothRetractMap.continuousOn`,
`Polyfold.IsScSmoothRetractMap.mem_range_toBase`).** $f$ is *sc-smooth from $(O, C, E)$ to $(O', C',
E')$* if $f(O) \subseteq O'$ and $f \circ r$ is sc-smooth on $U$ for every sc-smooth retraction $r$
on $C$ with $r(U) = O$; for a retract $O$ this holds iff $f(O) \subseteq O'$ and $f \circ r$ is
sc-smooth for one such $r$. The tangent map $Tf$ is $T(f \circ r)$ for a chosen $r$; on $TO$ it
equals $T(f \circ r)$ for every $r$ onto $O$, maps $TO$ into $TO'$ when $O, O'$ are retracts, and
$Tf(x, h) = (f(x), D(f \circ r)(x)h)$. Such an $f$ is continuous on $O$ and maps points of $O$ on
level $m$ to points on level $m$. *Book:* Definition 2.7, pp. 20–21. *Hidden hypotheses:* none.
*Deviation (restated):* the definition quantifies over all retractions and contains $f(O) \subseteq
O'$; the text's form is `Polyfold.isScSmoothRetractMap_iff_exists`.

**V2.7 (Theorem 2.8, the chain rule for retracts; `Polyfold.theorem_2_8`,
`Polyfold.IsScSmoothRetractMap.comp`, `Polyfold.retractTangentMap_comp`,
`Polyfold.isScSmoothRetractMap_id`, `Polyfold.ScRetraction.isScSmoothRetractMap`,
`Polyfold.IsScSmoothRetractMap.congr`).** Let $(O, C, E)$ and $(O', C', E')$ be retracts, $f$
sc-smooth from $O$ to $O'$ and $g$ sc-smooth from $O'$ to $(O'', C'', E'')$. Then $g \circ f$ is
sc-smooth from $O$ to $O''$ and $T(g \circ f) = Tg \circ Tf$ on $TO$. The identity is sc-smooth, a
retraction is sc-smooth as a map $(U, C, E) \to (O, C, E)$, and sc-smoothness depends only on the
values on $O$. *Book:* Theorem 2.8, p. 21, which writes $(O'', C', E'')$ for $(O'', C'', E'')$.
*Hidden hypotheses:* $r' \circ f \circ r = f \circ r$, which needs $f(O) \subseteq O'$. *Proof:* the
text gives none ("follows from Theorem 1.21"); $(g \circ f) \circ r = (g \circ r') \circ (f \circ r)$
on $U$ and Theorem 1.21.

**V2.8 (the tangent functor on retracts; `Polyfold.IsPartialQuadrant.tangentSet`,
`Polyfold.IsRelOpenInQuadrant.tangentSet`, `Polyfold.ScRetraction.tangentRetraction`,
`Polyfold.ScRetraction.tangentRetraction_retract`, `Polyfold.IsScRetract.tangentSet`,
`Polyfold.LocalModel.tangent`, `Polyfold.IsScSmoothRetractMap.tangent`,
`Polyfold.retractTangentMap_id`, `Polyfold.retractTangent_inter_isOpen`,
`Polyfold.retractTangentMap_inter_isOpen`).** $TC$ is a partial quadrant in $TE$ and $TU$ is
relatively open in $TC$; $Tr$ is an sc-smooth retraction on $TU$ with retract $TO$, so $(TO, TC,
TE)$ is a retract. If $f$ is sc-smooth between the retracts $O$ and $O'$, then $Tf$ is sc-smooth from
$(TO, TC, TE)$ to $(TO', TC', TE')$; $T$ of a map equal to the identity on $O$ is the identity on
$TO$. For $W \subseteq E_0$ open: $T(O \cap W) = TO \cap (W_1 \times E_0)$, and $Tf$ computed on
$(O \cap W, C, E)$ equals $Tf$ computed on $(O, C, E)$ there. *Book:* p. 21, after Theorem 2.8 ($T$
a functor $\mathcal R \to \mathcal R$), and p. 22, after Definition 2.9 ($Tr$ a bundle retraction).
*Hidden hypotheses:* the locality of $Tf$ under restriction to open subsets, used in Definitions
2.17–2.18. *Deviation (restated):* the bundle structure (the category $\mathcal{BR}$) is not
formalized.

**V2.9 (Proposition 2.10; `Polyfold.proposition_2_10_1`, `Polyfold.proposition_2_10_2`,
`Polyfold.ScRetraction.restrict`, `Polyfold.ScRetraction.restrict_retract`,
`Polyfold.IsScSmoothRetractMap.restrict`, `Polyfold.IsScSmoothRetractMap.of_locally`,
`Polyfold.LocalModel.restrict`).** (1) If $(O, C, E)$ is a retract and $W \subseteq E_0$ is open,
$(O \cap W, C, E)$ is a retract (with $r$ restricted to $U \cap r^{-1}(W)$). (2) If $(V, C, E)$ is a
retract and $s$ is sc-smooth from $(V, C, E)$ to itself with $s \circ s = s$ on $V$, then $(s(V), C,
E)$ is a retract, with the retraction $s \circ r$. Sc-smooth maps between retracts restrict to $O
\cap W$, and are sc-smooth as soon as every point of $O$ has an open neighbourhood $W$ with $f$
sc-smooth on $O \cap W$. *Book:* Proposition 2.10, p. 23. *Hidden hypotheses:* the restriction of an
sc-smooth map to a smaller relatively open set is sc-smooth (V2.63). *Deviation
(restated):* an open subset of $O$ is written $O \cap W$.

**V2.10 (Definition 2.11, charts; `Polyfold.MChart`, `Polyfold.MChart.overlap`,
`Polyfold.MChart.isScRetract_overlap`, `Polyfold.MChart.transition`, `Polyfold.MChart.Compatible`,
`Polyfold.MChart.compatible_self`, `Polyfold.MChart.Compatible.restrict`,
`Polyfold.MChart.compatible_of_locally`).** A *chart* on a space $X$ is a local model $(O, C, E)$ and
a partial equivalence $\varphi$ between $X$ and $E_0$ with open source $V$ and target $O$, continuous
on $V$, with inverse continuous on $O$. The overlap $\varphi(V \cap V')$ is a retract. Two charts are
*compatible* if $\psi \circ \varphi^{-1}$ is sc-smooth from $(\varphi(V \cap V'), C, E)$ to
$(\psi(V \cap V'), C', E')$ and $\varphi \circ \psi^{-1}$ back. A chart is compatible with itself,
compatibility passes to restrictions, and two charts each compatible with every chart of a family
covering $V \cap V'$ are compatible. *Book:* Definition 2.11, pp. 23–24. *Hidden hypotheses:* none.
*Deviation (restated):* the chart is a partial equivalence; the last statement, the locality of
compatibility, is not in the text and is what makes the maximal atlas (V2.12) work.

**V2.11 (Definition 2.12, atlases; `Polyfold.MAtlas`, `Polyfold.MAtlas.Equiv`,
`Polyfold.MAtlas.equiv_iff`, `Polyfold.MAtlas.Equiv.refl`, `Polyfold.MAtlas.Equiv.symm`,
`Polyfold.MAtlas.Equiv.trans`, `Polyfold.MAtlas.equivalence`).** An *atlas* is a set of pairwise
compatible charts whose sources cover $X$; two atlases are *equivalent* if their union is an atlas,
equivalently if every chart of one is compatible with every chart of the other; the relation is an
equivalence relation. *Book:* Definition 2.12, p. 24. *Hidden hypotheses:* none; the transitivity of
the equivalence, which “an equivalence class of atlases” (Definition 2.13) presupposes, is not
discussed in the text and is proved from the locality of compatibility (Findings, Chapter 2, item
41).

**V2.12 (Definition 2.13, M-polyfolds; `Polyfold.MPolyfold`, `Polyfold.MPolyfold.IsChart`,
`Polyfold.MPolyfold.IsChart.compatible`, `Polyfold.MPolyfold.IsChart.restrict`,
`Polyfold.MPolyfold.isChart_congr`, `Polyfold.MPolyfold.exists_isChart_mem_source`,
`Polyfold.LocalModel.toMPolyfold`).** An *M-polyfold* structure on a Hausdorff paracompact space $X$
is an atlas. The *charts of the structure* are all charts compatible with every chart of this atlas;
any two are compatible, restrictions of charts are charts, every point lies in the source of one, and
equivalent atlases give the same charts. A nonempty retract $O$ is an M-polyfold with the chart
$\mathrm{id}$. *Book:* Definition 2.13, p. 24. *Hidden hypotheses:* charts compatible with an atlas
are compatible with each other (the text does not discuss it; it needs V2.10). *Deviation
(restated):* one atlas represents its equivalence class.

**V2.13 (Definition 2.14, sc-smooth maps between M-polyfolds; `Polyfold.MPolyfold.IsScSmoothOn`,
`Polyfold.MPolyfold.IsScSmoothMap`, `Polyfold.MPolyfold.IsScSmoothOn.of_exists_charts`,
`Polyfold.MPolyfold.isScSmoothMap_id`, `Polyfold.MPolyfold.IsScSmoothOn.comp`,
`Polyfold.MPolyfold.IsScSmoothMap.comp`).** $f : X \to Y$ is *sc-smooth on the open set $U$* if it is
continuous on $U$ and, for all charts $\varphi$ of $X$, $\psi$ of $Y$ and every open $V \subseteq U
\cap \operatorname{dom}\varphi$ with $f(V) \subseteq \operatorname{dom}\psi$, the map $\psi \circ f
\circ \varphi^{-1}$ is sc-smooth from $(\varphi(V), C, E)$ to $(O', C', E')$; $f$ is sc-smooth if it
is sc-smooth on $X$. It suffices that every $x \in U$ has one such pair of charts and one such $V
\ni x$. The identity is sc-smooth; if $f$ is sc-smooth on $U$ with $f(U) \subseteq U'$ and $g$ on
$U'$, then $g \circ f$ is sc-smooth on $U$. *Book:* Definition 2.14, p. 24, and "the definition does
not depend on the choice of charts". *Hidden hypotheses:* $f$ continuous (for charts with $f(V)
\subseteq V'$ to exist around every point). *Deviation (hypotheses explicit):* continuity is part of
the definition; maps on open subsets are included.

**V2.14 (the filtration $X_m$; `Polyfold.MPolyfold.levelSet`, `Polyfold.MPolyfold.mem_levelSet_iff`,
`Polyfold.MPolyfold.levelSet_zero`, `Polyfold.MPolyfold.levelSet_succ_subset`,
`Polyfold.MPolyfold.smoothSet`, `Polyfold.MPolyfold.levelTopology`, `Polyfold.MPolyfold.Level`,
`Polyfold.MPolyfold.continuous_levelVal`, `Polyfold.MPolyfold.isEmbedding_levelLift`).** $X_m$ is
the set of points $x$ with $\varphi(x) \in \iota_m(E_m)$ for some chart $\varphi$ of the structure
around $x$; then this holds for every chart around $x$. $X_0 = X$, $X_{m+1} \subseteq X_m$, $X_\infty
= \bigcap_m X_m$. $X_m$ carries the topology generated by the sets $\{x \in V : \varphi(x) \in W\}$,
$\varphi$ a chart, $W \subseteq E_m$ open (in terms of the lift of $\varphi(x)$ to $E_m$). The
inclusion $X_m \to X$ is continuous, $X_m$ is Hausdorff (`Polyfold.MPolyfold.instT2SpaceLevel`), and on $V_m = V \cap X_m$ the lift of
$\varphi$ to $E_m$ is a topological embedding. *Book:* p. 25, the paragraph after Definition 2.14.
*Hidden hypotheses:* that the level is independent of the chart needs that transition maps are
$\mathrm{sc}^0$ on the overlap retracts (the text: "of course"). *Deviation (restated):* the
topology is the one generated by the text's family; that the family is a basis is not proved.

**V2.15 (Lemma 2.15; `Polyfold.lemma_2_15`, `Polyfold.MPolyfold.levelIncl`).** The inclusion $X_{m+1}
\to X_m$ is continuous for every $m$. *Book:* Lemma 2.15, p. 25. *Hidden hypotheses:* none.

**V2.16 (the M-polyfold $X^1$; `Polyfold.ScRetraction.shift`, `Polyfold.ScRetraction.shift_retract`,
`Polyfold.IsScRetract.shift`, `Polyfold.LocalModel.shift`, `Polyfold.IsScSmoothRetractMap.shift`,
`Polyfold.MPolyfold.levelChart`, `Polyfold.MPolyfold.levelChart_compatible`,
`Polyfold.MPolyfold.levelAtlas`, `Polyfold.MPolyfold.shift`, `Polyfold.MPolyfold.shift_isChart`,
`Polyfold.MPolyfold.mem_shift_levelSet_iff`).**
A retraction $r$ on $U$ induces an sc-smooth retraction on $U_1 \subseteq C_1 \subseteq E^1$ with
retract $O_1$, so $(O_1, C_1, E^1)$ is a retract; an sc-smooth map between retracts induces an
sc-smooth map between their level-$1$ parts (Proposition 1.17 for retracts). For every chart
$\varphi$ of $X$, $(V_1, \varphi, (O_1, C_1, E^1))$ is a chart of $X_1$; any two are compatible, they
form an atlas, and $X_1$ with it is an M-polyfold $X^1$. *Book:* p. 25 ("$(V_m, \varphi, (O_m, C_m,
E_m))$ is a chart on $X_m$ … the collection of such charts is an atlas on $X_m$"). *Hidden
hypotheses:* the paracompactness of $X_1$ (Theorem 2.16), an instance argument supplied by V2.17.
The levels of $X^1$ are those of $X$ shifted by one, as sets: $(X^1)_m = X_{m+1}$. *Deviation (narrower):* $m = 1$ only;
for $m \ge 2$ the iterate $(X^1)^1 \cdots$ has the points of $X_m$, but that its topology and charts are those of $X_m$ is not
formalized (gap G.6; the set identity was added in a fourth addendum, Findings, Chapter 5, item 142).

**V2.17 (Theorem 2.16; `Polyfold.theorem_2_16`, `Polyfold.MPolyfold.metrizableSpace`,
`Polyfold.MPolyfold.metrizableSpace_level`, `Polyfold.MPolyfold.paracompactSpace_level`,
`Polyfold.MPolyfold.SmoothLevel`, `Polyfold.MPolyfold.smoothLevel_topology_eq`,
`Polyfold.MPolyfold.metrizableSpace_smoothLevel`, `Polyfold.MPolyfold.paracompactSpace_subtype`).**
Let $X$ be an M-polyfold. Then $X$ is metrizable; for every $m$, the level $X_m$ with the topology of
V2.14 is metrizable and paracompact; and $X_\infty$, with the initial topology of the inclusions
$X_\infty \to X_m$ ($m \ge 0$), is metrizable. Every subset of $X$ is paracompact. *Book:* Theorem
2.16, p. 25, proof pp. 57–58. *Hidden hypotheses:* the topology of $X_\infty$, which the text does
not define. *Deviation (hypotheses explicit):* **no hypothesis is added.** *Proof:* not the text's.
The text needs $X_m$ regular for Proposition 2.57 and does not check it. Here a partition of unity of
the paracompact Hausdorff $X$ subordinate to the chart domains is pulled back to $X_m$ along the
continuous inclusion; with the metrizable chart domains $V_m \cong O_m$ it gives an explicit metric
(V2.62). Paracompactness of $X_m$ follows by Stone's theorem; $X_\infty$ embeds in $\prod_m X_m$.

**V2.18 (Definition 2.17, tangent vectors in charts; `Polyfold.MPolyfold.TangentPre`,
`Polyfold.MPolyfold.TangentPre.transport`, `Polyfold.MPolyfold.TangentPre.transport_self`,
`Polyfold.MPolyfold.TangentPre.transport_mem`, `Polyfold.MPolyfold.TangentPre.transport_transport`,
`Polyfold.MPolyfold.TangentPre.Rel`, `Polyfold.MPolyfold.TangentPre.Rel.symm`,
`Polyfold.MPolyfold.TangentPre.Rel.trans`, `Polyfold.MPolyfold.TangentPre.setoid`).** A tangent
tuple is $(x, \varphi, h)$ with $x \in X_1$, $\varphi$ a chart of the structure around $x$ and
$(\varphi(x), h) \in TO$. Its transport to a chart $\psi$ around $x$ is $T(\psi \circ \varphi^{-1})
(\varphi(x), h)$, computed on the overlap retract; it lies in $TO'$ over $\psi(x)$, transport to
$\varphi$ is the identity, and transport to $\psi$ followed by transport to $\chi$ is transport to
$\chi$. Two tuples are equivalent if their points agree and the transport of the first to the chart
of the second is the second; this is an equivalence relation. *Book:* Definition 2.17, pp. 25–26.
*Hidden hypotheses:* that the relation is an equivalence relation (the text does not check it); it
needs Theorem 2.8 on the triple overlap and the locality of $Tf$ (V2.8). *Deviation (restated):*
none in substance.

**V2.19 (Definition 2.18, the tangent space $TX$; `Polyfold.MPolyfold.TangentSpace`,
`Polyfold.MPolyfold.tangentProj`, `Polyfold.MPolyfold.tangentFiber`,
`Polyfold.MPolyfold.tangentChartSet`, `Polyfold.MPolyfold.tangentChartMap`,
`Polyfold.MPolyfold.tangentChartMap_mk_self`, `Polyfold.MPolyfold.tangentChartMap_injOn`,
`Polyfold.MPolyfold.tangentChartMap_mk_ofVec`, `Polyfold.MPolyfold.tangentChartMap_mk_ofVec_of_mem`,
`Polyfold.MPolyfold.tangentBasis`).** $TX$ is the set of equivalence classes of tangent tuples, with
$p : TX \to X_1$, $[(x, \varphi, h)] \mapsto x$, and $T_xX = p^{-1}(x)$. For a chart $\varphi$,
$TV = p^{-1}(V_1)$ and $T\varphi : TV \to TO$ sends a class to its transport to $\varphi$; $T\varphi
[(x, \varphi, h)] = (\varphi(x), h)$, $T\varphi$ is injective on $TV$ with inverse $a \mapsto
[(\varphi^{-1}(a_1), \varphi, a_2)]$ on $TO$, and $T\psi \circ (T\varphi)^{-1} = T(\psi \circ
\varphi^{-1})$ on $T(\varphi(V \cap V'))$. $TX$ carries the topology generated by the sets $\{\alpha
\in TV : T\varphi(\alpha) \in W\}$, $W$ open. *Book:* Definition 2.18 and the paragraphs after it,
pp. 26–27. *Hidden hypotheses:* none. *Deviation (narrower):* the vector space, Banach and
sc-Banach structures of $T_xX$ are not formalized.

**V2.20 (Proposition 2.19; `Polyfold.MPolyfold.continuous_tangentProj`,
`Polyfold.MPolyfold.continuous_levelVal_tangentProj`, `Polyfold.MPolyfold.isOpen_tangentChartSet`,
`Polyfold.MPolyfold.metrizableSpace_tangentSpace`, `Polyfold.MPolyfold.paracompactSpace_tangentSpace`,
`Polyfold.proposition_2_19_3`).** (1) $TX$ is Hausdorff (the instance
`Polyfold.MPolyfold.instT2SpaceTangentSpace`). (2) $p : TX \to X_1$ is continuous, and so is $TX \to X$;
each $TV$ is open. (3) $TX$ is metrizable and paracompact. *Book:* Proposition 2.19, p. 27, proof
pp. 58–60. *Hidden hypotheses:* none for (3). *Deviation (narrower):* the openness of $p$ in (2) is
not proved; the basis property in (1) is not needed. *Proof:* (3) as for Theorem 2.16, pulling a
partition of unity of $X$ back along $TX \to X_1 \to X$; the charts $TV \cong TO$ are metrizable.

**V2.21 ($TX$ as an M-polyfold; `Polyfold.MPolyfold.tangentChart`,
`Polyfold.MPolyfold.tangentChart_overlap`, `Polyfold.MPolyfold.tangentChart_transition`,
`Polyfold.MPolyfold.tangentChart_compatible`, `Polyfold.MPolyfold.tangentAtlas`,
`Polyfold.MPolyfold.tangentPolyfold`, `Polyfold.MPolyfold.isScSmoothRetractMap_tangent_fst`,
`Polyfold.MPolyfold.tangentProj_isScSmooth`).** For a chart $\varphi$ of $X$, $(TV, T\varphi, (TO, TC,
TE))$ is a chart of $TX$, with $T\varphi(TV \cap TV') = T(\varphi(V \cap V'))$ and transition map
$T(\varphi' \circ \varphi^{-1})$ (formula (5)); these charts are pairwise compatible, form an atlas,
and make $TX$ an M-polyfold. The projection $TO \to O_1$ is sc-smooth from $(TO, TC, TE)$ to
$(O_1, C_1, E^1)$, and $p : TX \to X^1$ is sc-smooth. *Book:* p. 27, after Proposition 2.19. *Hidden
hypotheses:* the paracompactness of $TX$ and $X_1$ (instance arguments, supplied by V2.20 and
V2.17). *Deviation (narrower):* "sc-smooth M-polyfold bundle" is read as "$p$ is sc-smooth"; the
fibrewise linear structure is not formalized.

**V2.22 (tangent maps of sc-smooth maps between M-polyfolds; `Polyfold.MPolyfold.tangentMap`,
`Polyfold.MPolyfold.tangentMap_mk`, `Polyfold.MPolyfold.levelVal_tangentProj_tangentMap`,
`Polyfold.MPolyfold.tangentMap_mapsTo_fiber`, `Polyfold.MPolyfold.tangentChartMap_tangentMap`,
`Polyfold.MPolyfold.tangentMap_id`, `Polyfold.MPolyfold.tangentMap_comp`,
`Polyfold.MPolyfold.continuous_tangentMap`, `Polyfold.MPolyfold.tangentMap_isScSmooth`,
`Polyfold.MPolyfold.IsScSmoothMap.mapsTo_levelSet`).** An sc-smooth $f : X \to Y$ maps $X_m$ into
$Y_m$. Its tangent map $Tf : TX \to TY$, $[(x, \varphi, h)] \mapsto [(f(x), \psi, T(\psi \circ f
\circ \varphi^{-1})(\varphi(x), h)_2)]$, is independent of the chart $\psi$ around $f(x)$ and of the
representative; $p \circ Tf = f \circ p$, $Tf(T_xX) \subseteq T_{f(x)}Y$, $T\psi \circ Tf = T(\psi
\circ f \circ \varphi^{-1}) \circ T\varphi$ in charts, $T(\mathrm{id}) = \mathrm{id}$, $T(g \circ f)
= Tg \circ Tf$, and $Tf$ is continuous and sc-smooth $TX \to TY$. *Book:* not stated; the text uses
$Tf$ for M-polyfolds from §2.3 on (Proposition 2.21(4), Definition 2.38). *Deviation (not in the
book):* the construction the text leaves implicit.

**V2.23 (Definition 2.20, sub-M-polyfolds; `Polyfold.MPolyfold.IsSubMPolyfold`,
`Polyfold.MPolyfold.isSubMPolyfold_univ`).** $A \subseteq X$ is a *sub-M-polyfold* if every $a \in A$
has an open $V \ni a$ and a map $r$ with $r(V) \subseteq V$, $r$ sc-smooth on $V$, $r \circ r = r$ on
$V$ and $r(V) = A \cap V$. *Book:* Definition 2.20, p. 28. *Hidden hypotheses:* none.

**V2.24 (Proposition 2.21 (1), (2); `Polyfold.MPolyfold.SubData`, `Polyfold.MPolyfold.SubData.shrink`,
`Polyfold.MPolyfold.SubData.image_shrink`, `Polyfold.MPolyfold.SubData.rho_isScSmooth`,
`Polyfold.MPolyfold.SubData.isScRetract_image`, `Polyfold.MPolyfold.subChart`,
`Polyfold.MPolyfold.subChart_compatible`, `Polyfold.MPolyfold.subAtlas`,
`Polyfold.MPolyfold.subPolyfold`, `Polyfold.MPolyfold.subPolyfold_inclusion_isScSmooth`,
`Polyfold.MPolyfold.subPolyfold_retraction_isScSmooth`, `Polyfold.IsScSmoothRetractMap.mono_source`,
`Polyfold.MPolyfold.paracompactSpace_of_isClosed`).** Let $A$ be a sub-M-polyfold with the subspace
topology. For data $(V, r)$ at a point and a chart $\varphi$, the set $W = (V \cap \operatorname{dom}
\varphi) \cap r^{-1}(V \cap \operatorname{dom}\varphi)$ is open with $r(W) \subseteq W$ and $r(W) =
W \cap A$; $\rho = \varphi \circ r \circ \varphi^{-1}$ is sc-smooth and idempotent on $\varphi(W)$, so
$\varphi(W \cap A)$ is a retract and $\varphi$ restricted to $W \cap A$ is a chart of $A$ with model
$(\varphi(W \cap A), C, E)$. Any two such charts are compatible; they form an atlas, and $A$ is an
M-polyfold. (1) The inclusion $A \to X$ is sc-smooth. (2) For every data $(V, r)$, the map $i^{-1}
\circ r$ is sc-smooth on $V$. A closed subset of $X$ is paracompact. *Book:* Proposition 2.21 (1),
(2), pp. 28–30. *Hidden hypotheses:* the topology of $A$ (the subspace topology; then (1)'s
homeomorphism is by construction) and the paracompactness of $A$, an instance argument of the
structure, supplied for every $A$ by `Polyfold.MPolyfold.paracompactSpace_subtype` (V2.17).
*Deviation (hypotheses explicit):* none otherwise.

**V2.25 (Proposition 2.21 (3), (4), in a chart; `Polyfold.ScRetraction.compRetraction`,
`Polyfold.ScRetraction.compRetraction_retract`, `Polyfold.proposition_2_21_3`,
`Polyfold.proposition_2_21_4`).** Let $r$ be a retraction onto $O$, $s$ sc-smooth from $(O, C, E)$ to
itself with $s \circ s = s$, $t = s \circ r$ (a retraction onto $s(O)$) and $a \in s(O)_1$. If $a$
is smooth: $T_aO = Dr(a)E_0$, $T_a s(O) = Dt(a)E_0 \subseteq T_aO$, the subspaces $Dt(a)E_0$ and
$(Dr(a) - Dt(a))E_0$ are sc-subspaces of $E$, and on every level $m$ their level-$m$ parts are
disjoint with sum the level-$m$ part of $T_aO$. For every $a \in s(O)_1$: $s$ is sc-smooth from $O$
to $s(O)$ and $Ts$ maps $T_aO$ onto $T_a s(O)$. *Book:* Proposition 2.21 (3), (4), p. 30, proved in
coordinates with "$T_aO = Ds(a)Dr(a)E \oplus (I - Ds(a))Dr(a)E$". *Hidden hypotheses:* $Ds(a)$ means
$Dt(a)$; the splitting is an sc-splitting because $Dr(a)$, $Dt(a)$ are commuting sc-projections with
$Dr(a)Dt(a) = Dt(a) = Dt(a)Dr(a)$. *Deviation (narrower):* in a chart only, as the text proves it;
the transport to $T_aX$ is not formalized (no sc-structure on the fibres of $TX$).

**V2.26 (Definition 2.22, the degeneracy index; `Polyfold.MPolyfold.chartDegIndex`,
`Polyfold.MPolyfold.degIndex`, `Polyfold.MPolyfold.degIndex_le`,
`Polyfold.MPolyfold.exists_isChart_degIndex_eq`, `Polyfold.MPolyfold.eventually_chartDegIndex_le`).**
For a chart $\varphi$ around $x$, $d(x, \varphi) = d_C(\varphi(x))$; $d_X(x)$ is the least $d(x,
\varphi)$ over the charts of the structure around $x$. The minimum is attained, $d_X(x) \le d(x,
\varphi)$ for every such chart, and $d(\cdot, \varphi)$ is upper semicontinuous on the source of
$\varphi$. *Book:* Definition 2.22, p. 31 ("smooth charts"). *Hidden hypotheses:* none.
*Deviation (restated):* "smooth charts" are the charts of the maximal atlas.

**V2.27 (Lemma 2.23; `Polyfold.lemma_2_23`, `Polyfold.eventually_degIndexWith_le`,
`Polyfold.MPolyfold.isOpen_setOf_degIndex_lt`, `Polyfold.MPolyfold.isClosed_setOf_le_degIndex`).**
For every $x \in X$, $d_X(y) \le d_X(x)$ for all $y$ near $x$; hence $\{d_X < k\}$ is open and $\{d_X
\ge k\}$ closed. The degeneracy index $d_C$ of a partial quadrant is upper semicontinuous. *Book:*
Lemma 2.23, p. 31 ("evident"). *Hidden hypotheses:* none.

**V2.28 (Proposition 2.24; `Polyfold.MPolyfold.IsScDiffeoOn`, `Polyfold.proposition_2_24`,
`Polyfold.MPolyfold.transportChart`, `Polyfold.MPolyfold.transportChart_isChart`,
`Polyfold.MPolyfold.degIndex_le_of_isScDiffeoOn`).** Let $U \subseteq X$, $V \subseteq Y$ be open,
$f$ sc-smooth on $U$ with $f(U) \subseteq V$ and $g$ sc-smooth on $V$ with $g(V) \subseteq U$,
inverse to each other. Then $d_X(x) = d_Y(f(x))$ for every $x \in U$. For a chart $\psi$ of $Y$, the
map $\psi \circ f$ on $U \cap f^{-1}(\operatorname{dom}\psi)$ is a chart of the structure of $X$.
*Book:* Proposition 2.24, p. 31 ("from the definitions one deduces immediately"). *Hidden
hypotheses:* none. *Deviation (restated):* a germ is represented by an sc-diffeomorphism of open
sets.

**V2.29 (Definition 2.25, the boundary; `Polyfold.MPolyfold.boundary`,
`Polyfold.MPolyfold.IsWithoutBoundary`, `Polyfold.MPolyfold.isWithoutBoundary_iff`,
`Polyfold.MPolyfold.isClosed_boundary`, `Polyfold.MPolyfold.isOpen_interior`,
`Polyfold.MPolyfold.corners`, `Polyfold.MPolyfold.isClosed_corners`,
`Polyfold.MPolyfold.IsScDiffeoOn.mem_boundary_iff`).** $\partial X = \{d_X \ge 1\}$; $X$ is without
boundary iff $d_X \equiv 0$ iff $\partial X = \emptyset$. $\partial X$ and $\{d_X \ge 2\}$ are closed,
$\{d_X = 0\}$ is open, and sc-diffeomorphisms of open sets preserve $\partial X$. *Book:* Definition
2.25, p. 31. *Hidden hypotheses:* none.

**V2.30 (Lemma 2.26; `Polyfold.lemma_2_26`).** For a sub-M-polyfold $A$ with the structure of V2.24,
$d_A(a) \le d_X(a)$ for every $a \in A$. *Book:* Lemma 2.26, pp. 31–32. *Hidden hypotheses:* the
paracompactness of $A$, as in V2.24.

**V2.31 (the subspaces $E_x$ and the cones $C_x$; `Polyfold.minimalSubspaceWith`,
`Polyfold.mem_minimalSubspaceWith`, `Polyfold.isClosed_minimalSubspaceWith`,
`Polyfold.finrank_quotient_minimalSubspaceWith`, `Polyfold.partialQuadrantAtWith`,
`Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith`, `Polyfold.isClosed_partialQuadrantAtWith`,
`Polyfold.exists_tendsto_lvl1_degIndexWith`, `Polyfold.exists_tendsto_smooth_degIndexWith`,
`Polyfold.ScBanach.subset_closure_ker_inter_range_toBase`,
`Polyfold.partialQuadrantAtWith_subset_closure`).** Let $T : E \cong \mathbb R^n \oplus W$ present
$C$. $E_x = \{v : (Tv)_i = 0 \text{ whenever } (Tx)_i = 0\}$ is a closed subspace of $E_0$ with
$\dim(E_0/E_x) = d_C(x)$; $C_x = \{v : (Tv)_i \ge 0 \text{ whenever } (Tx)_i = 0\}$ is closed and
convex and contains $E_x$. Every $x \in C$ is a limit of points of level $1$ (and of smooth points)
with the same index and in $C$. The level-$1$ points of the kernel of any continuous linear map into
a finite-dimensional space are dense in it, and the level-$1$ points of $C_x$ are dense in $C_x$.
*Book:* p. 32 ($E_i$, $E_I$, $I(x)$, $E_x$, $H_i$, $C_x$ in the model $\mathbb R^k \oplus W$).
*Hidden hypotheses:* the densities, which the text uses without proof ("the closure of $(T^R_xO)_\infty$
is $T^R_xO$"). *Deviation (restated):* defined through a presentation of $C$.

**V2.32 (Definition 2.27; `Polyfold.reducedTangentSpaceWith`, `Polyfold.partialConeWith`,
`Polyfold.quotDim`, `Polyfold.quotDim_inf_minimalSubspace_le`,
`Polyfold.quotDim_reducedTangentSpaceWith_le`).** For a retraction $r$, a presentation $T$ and $x \in
O_1$: $T^R_xO = Dr(x)E_0 \cap E_x$ and $C_xO = Dr(x)E_0 \cap C_x$. For subspaces $A, B$,
$\dim(A/(A \cap B))$ is the natural number $\operatorname{quotDim}(A, B)$; $\dim(T_xO/T^R_xO) \le
d_C(x)$. *Book:* Definition 2.27, p. 33. *Hidden hypotheses:* none. *Deviation (stronger):* defined
at every $x \in O_1$, not only at smooth points.

**V2.33 (Remark 2.28; `Polyfold.reducedTangentSpaceWith_subset_partialConeWith`,
`Polyfold.remark_2_28_isPartialQuadrant`, `Polyfold.remark_2_28_partialConeWith`,
`Polyfold.flor_nonnegRange_simplicial`, `Polyfold.remark_2_28_quotient_simplicial`,
`Polyfold.ScRetraction.isScSubspace_reducedTangentSpaceWith`,
`Polyfold.partialConeWith_eq_image_scDeriv`).** $T^R_xO \subseteq C_xO \subseteq T_xO$. Moreover,
for every sc-smooth retraction $r$ in $C = T^{-1}([0, \infty)^n \oplus W)$ and every smooth
$x \in O$ (no tameness), $T_xO$ and $T^R_xO$ are sc-subspaces of $E$ and $C_xO$ is a partial
quadrant in the sc-Banach space $T_xO$ (with the sc-structure induced from $E$), of dimension
$r = \operatorname{rank} M = \dim(T_xO/T^R_xO) \le d_C(x)$, where $M$ is the matrix of $Dr(x)$ on
$E/E_x \cong \mathbb R^{I(x)}$. The core is Flor's theorem in the needed case: for a linear $M$ on
$\mathbb R^\iota$ with $M^2 = M$ mapping the orthant into itself, the cone
$\operatorname{range} M \cap [0, \infty)^\iota$ is the set of nonnegative combinations of linearly
independent columns of $M$. *Book:* Remark 2.28, p. 33: the inclusions, and “naively one might
expect that $C_xO$ is a partial quadrant in $T_xO$. However, this is in general not the case”,
without an example. *Hidden hypotheses:* none. *Deviation (stronger):* **the remark's negative claim
does not hold in our formal reading** (checked in Lean); the remark may mean the narrower point
below. *Proof:* $Dr(x)$ maps $C_x$ and $E_x$ into
themselves (the sign arguments of Lemma 2.29), so $C_xO = Dr(x)(C_x)$; modulo $T^R_xO$ it is the
column cone of the nonnegative idempotent matrix $M$, simplicial by Flor's theorem (minimal column
supports, generation by descent on the support, independence through a private index of each minimal
support); the sc-isomorphism $T_xO \cong \mathbb R^r \oplus T^R_xO$ of the proof of Theorem 2.31
(V2.42) carries $C_xO$ onto $[0, \infty)^r \oplus T^R_xO$. What can fail for a non-tame retract is
only $r = d_C(x)$ (Theorem 2.31), which the text proves for tame retracts (Proposition 2.36, V2.42)
(Findings, Chapter 2, item 50; round-trip item V2.33).

**V2.34 (the sign arguments; `Polyfold.IsSc1With.deriv_mem_minimalSubspace_of_lvl1`,
`Polyfold.IsSc1With.mapsTo_minimalSubspace`, `Polyfold.IsSc1With.deriv_mem_partialQuadrant_of_lvl1`,
`Polyfold.IsSc1With.mapsTo_partialQuadrant`, `Polyfold.eventually_add_smul_mem_lvlSet`,
`Polyfold.eventually_add_smul_mem_lvlSet_of_cone`,
`Polyfold.ScRetraction.scDeriv_mapsTo_minimalSubspace`).** Let $f$ be sc¹ on $U$, relatively open in
$C$ (presented by $T$), with values in $C'$ (presented by $T'$), and $x \in U_1$. For $v \in E_1$
with $\iota_1 v \in E_x$: $x + tv \in U_1$ for $|t|$ small and $Df(x)v \in E'_{f(x)}$; hence $Df(x)$
maps $E_x$ into $E'_{f(x)}$. For $v \in E_1$ with $\iota_1 v \in C_x$: $x + tv \in U_1$ for small
$t \ge 0$ and $Df(x)v \in C'_{f(x)}$; hence $Df(x)$ maps $C_x$ into $C'_{f(x)}$. For a retraction
$r$ and $x \in O_1$, $Dr(x)$ maps $E_x$ into $E_x$. *Book:* the proofs of Lemma 2.29, pp. 33–35,
and Proposition 2.35, p. 40. *Deviation (not in the book):* the derivative-level content of Lemma
2.29, isolated; Lemma 2.29 itself, about sc-smooth paths, is not formalized. *Proof:* the function
$t \mapsto (T'f(x + tv))_j$ is $\ge 0$ near $0$ and vanishes at $0$; its derivative at $0$ vanishes
(two-sided) or is $\ge 0$ (one-sided).

**V2.35 (Proposition 2.30; `Polyfold.ScRetraction.IsDiffeoGerm`,
`Polyfold.IsScSmoothRetractMap.isDiffeoGerm`, `Polyfold.ScRetraction.IsDiffeoGerm.deriv_inv_deriv`,
`Polyfold.ScRetraction.IsDiffeoGerm.deriv_deriv_inv`, `Polyfold.proposition_2_30_reduced`,
`Polyfold.proposition_2_30_cone`).** A *germ of sc-diffeomorphisms* between the retracts $O = r(U)$
and $O' = r'(U')$ is a pair $F, G$ with $F \circ r$, $G \circ r'$ sc¹, $F(O) \subseteq O'$, $G(O')
\subseteq O$, $G \circ F = \mathrm{id}$ on $O$ and $F \circ G = \mathrm{id}$ on $O'$; an sc-smooth
map between retracts with an sc-smooth inverse is one. For $x \in O_1$ and $y = (F \circ r)_1(x)$:
$D(G \circ r')(y) \circ D(F \circ r)(x) = Dr(x)$, $D(F \circ r)(x) \circ D(G \circ r')(y) =
Dr'(y)$, and, with $Tf(x) = D(F \circ r)(x)$, $Tf(x)(T^R_xO) = T^R_yO'$ and $Tf(x)(C_xO) = C_yO'$.
*Book:* Proposition 2.30, p. 35 (smooth $x$, sc-smooth germs; deduced from Lemma 2.29). *Hidden
hypotheses:* none. *Deviation (stronger):* level-$1$ points and sc¹ germs. *Proof:* from the sign
arguments (V2.34) and the two derivative identities, not from Lemma 2.29.

**V2.36 (a retract as an M-polyfold; `Polyfold.LocalModel.selfChart`,
`Polyfold.LocalModel.toMPolyfold`, `Polyfold.IsRelOpenInQuadrant.toMPolyfold`,
`Polyfold.IsRelOpenInQuadrant.selfChart_isChart`, `Polyfold.MChart.Compatible.isDiffeoGerm`).** A
nonempty retract $O$, and a nonempty relatively open $U \subseteq C$, is an M-polyfold on the subtype
with the single chart $\mathrm{id}$. Two compatible charts give a germ of sc-diffeomorphisms (in the
sense of V2.35) between the overlap retracts, with the restricted retractions. *Book:* p. 35, before
Theorem 2.31. *Deviation (restated):* the text's $d_O(x) = \min d_{C'}(\varphi(x))$ over germs into
retracts is Definition 2.22 for this structure.

**V2.37 (Theorem 2.31, first statement; `Polyfold.theorem_2_31`, `Polyfold.theorem_2_31_retract`,
`Polyfold.ScRetraction.IsDiffeoGerm.quotDim_le`, `Polyfold.MPolyfold.quotDim_le_chartDegIndex`,
`Polyfold.ScRetraction.scDeriv_restrict`, `Polyfold.degIndexWith_le_of_germ`,
`Polyfold.remark_2_28_isPartialQuadrant`).** Let $X$ be an M-polyfold, $\varphi$ a chart of the
structure around $x$ with $\varphi(x) = \iota_1 z$ on level $1$, $r$ a retraction onto the model $O$
and $T$ a presentation of $C$. Then $\dim(T_zO/T^R_zO) \le d_X(x)$. For a retract $O$ itself as an
M-polyfold and $x \in O_1$: $\dim(T_xO/T^R_xO) \le d_O(x)$. Along a germ of sc-diffeomorphisms $F$
between retracts, $\dim(T_xO/T^R_xO) \le d_{C'}(F(x))$. *Book:* Theorem 2.31, p. 35 (a retract, a
smooth $x$). *Hidden hypotheses:* none. *Deviation (stronger):* every M-polyfold, every chart,
points on level $1$. The second statement of the theorem (equality makes $C_xO$ a partial quadrant)
holds without its hypothesis: $C_xO$ is a partial quadrant at every smooth point of every retract
(V2.33). *Proof:* for every chart $\psi$ around $x$, $D(\psi \circ \varphi^{-1})$ induces
$T_zO/T^R_zO \cong T_yO'/T^R_yO'$, which embeds in $E'/E'_y$ of dimension $d_{C'}(\psi(x))$; the
text instead reduces to a chart realizing $d_O(x)$.

**V2.38 (Corollary 2.32; `Polyfold.corollary_2_32`, `Polyfold.IsRelOpenInQuadrant.degIndex_le`,
`Polyfold.IsRelOpenInQuadrant.degIndex_le_degIndex_of_lvl1`, `Polyfold.degIndexWith_le_of_germ`).**
For a nonempty relatively open subset $U$ of a partial quadrant $C$, viewed as the M-polyfold $X_U$,
$d_{X_U}(x) = d_C(x)$ for every $x \in U$. *Book:* Corollary 2.32, p. 37 ($U = C$). *Hidden
hypotheses:* the semicontinuity of $d_{C'}$ and Proposition 2.24 at the approximating points.
*Deviation (stronger):* every relatively open $U$; level-$1$ approximants suffice. Theorem 1.25
(V1.23, `Polyfold.theorem_1_25`) is proved in the same file by the same argument.

**V2.39 (Definition 2.33; `Polyfold.partialQuadrantAtWith`, `Polyfold.minimalSubspaceWith`,
`Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith`, `Polyfold.convex_partialQuadrantAtWith`,
`Polyfold.finrank_quotient_minimalSubspaceWith`, `Polyfold.minimalSubspaceWith_le`,
`Polyfold.minimalSubspaceWith_eq`).** For a presentation $T$ of $C$ and $e \in C$: the partial
quadrant $C_e$ and the minimal subspace $E_e$ of V2.31, with $E_e \subseteq C_e$, $C_e$ convex and
$\dim(E_0/E_e) = d_C(e)$. For two presentations $T$, $T'$ of the same $C$, the two subspaces $E_e$
agree. *Book:* Definition 2.33, p. 39, through the extended faces. *Hidden hypotheses:* none.
*Deviation (restated):* through a presentation, of which $E_e$ is independent (the argument of Lemma
1.24); the intrinsic description by extended faces (p. 39) is not formalized.

**V2.40 (Definition 2.34, tame retractions; `Polyfold.ScRetraction.IsTameWith`,
`Polyfold.ScRetraction.IsTame`, `Polyfold.IsTameRetract`, `Polyfold.IsTameRetract.isScRetract`,
`Polyfold.ScRetraction.id_isTame`, `Polyfold.ScRetraction.IsTameWith.isTame`,
`Polyfold.ScRetraction.IsTameWith.restrict`).** A retraction $r$ is *tame for $T$* if (1)
$d_C(r(x)) = d_C(x)$ for $x \in U$ and (2) for every smooth $x \in O_1$ there is a subspace $A \le
E_x$ such that $E = Dr(x)E_0 \oplus A$ is an sc-splitting. $r$ is *tame* if it is tame for every
presentation of $C$; tameness for one presentation implies it. A *tame retract* is the retract of a
tame retraction. Identities of relatively open subsets are tame, and the restriction of a tame
retraction to $U \cap r^{-1}(V)$, $V$ open, is tame. *Book:* Definition 2.34, pp. 39–40. *Hidden
hypotheses:* that the definition does not depend on the presentation, which the text uses tacitly.
*Deviation (restated):* none in substance.

**V2.41 (Proposition 2.35; `Polyfold.proposition_2_35`,
`Polyfold.ScRetraction.scDeriv_mapsTo_minimalSubspace`, `Polyfold.ScRetraction.isScOperator_scDeriv`,
`Polyfold.ScRetraction.isScSplitting_range_scDeriv`, `Polyfold.coord_scDeriv_eq`).** Let $r$ be tame
for $T$ and $x \in O_1$ smooth. Then $(1 - Dr(x))E_0 \le E_x$, and $E = Dr(x)E_0 \oplus (1 -
Dr(x))E_0$ is an sc-splitting; equivalently $\lambda_j(Dr(x)v) = \lambda_j(v)$ for $j \in I(x)$ and
all $v$. *Book:* Proposition 2.35, p. 41, with the discussion on p. 40. *Hidden hypotheses:* none.
*Deviation (stronger):* only condition (2) of tameness is used; $Dr(x)E_x \subseteq E_x$ holds for
every retraction (V2.34), where the text uses condition (1).

**V2.42 (Proposition 2.36; `Polyfold.proposition_2_36`, `Polyfold.proposition_2_36_degIndex`,
`Polyfold.quotDim_reducedTangentSpaceWith_eq`,
`Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith`,
`Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract`,
`Polyfold.LocalModel.degIndex_toMPolyfold_of_isTameWith`,
`Polyfold.quotDim_eq_finrank_quotient_of_isCompl`, `Polyfold.proposition_2_36_partialCone`,
`Polyfold.splitIso`, `Polyfold.isPartialQuadrant_ofSubspace`).** Let $r$ be tame for $T$. (13) At a
smooth $x \in O_1$, $\dim(T_xO/T^R_xO) = d_O(x) = d_C(x)$, where $d_O$ is the index of the
M-polyfold $O$; moreover $T_xO$ and $T^R_xO$ are sc-subspaces of $E$, and $C_xO = T_xO \cap C_x$ is
a partial quadrant in the sc-Banach space $T_xO$ (with the sc-structure induced from $E$). (14)
$d_O(x) = d_C(x)$ for every $x \in O$. More generally, a chart $\varphi$ of any M-polyfold whose
model is a tame retract satisfies $d_X(y) = d_C(\varphi(y))$ for every $y$ in its source. For
sc-subspaces $B \le A$ with $B = A \cap \bigcap_j \ker \ell_j$ and smooth $e_j \in A$ with
$\ell_i(e_j) = \delta_{ij}$, the map $v \mapsto ((\ell_j v)_j, v - \sum_j \ell_j(v)e_j)$ is an
sc-isomorphism $A \cong \mathbb R^d \oplus B$, and $\{v \in A : \ell_j(v) \ge 0\ \forall j\}$ is a
partial quadrant in $A$. *Book:* Proposition 2.36, p. 41. *Hidden hypotheses:* none. *Deviation
(stronger):* the chart form, which Proposition 2.42 needs; $T^R_xO$ is an sc-subspace, where the
text says a Banach space. *Proof:* (13), (14) as in the text: $E_x = T^R_xO \oplus A$ gives
$\dim(T_xO/T^R_xO) = d_C(x)$, Theorem 2.31 gives $\le d_X$; a general point is approximated by
smooth points $r(T^{-1}(a, w_j))$ of the same index, with Lemma 2.23. The partial quadrant not from
the equality case of Theorem 2.31, as in the text, but directly (it holds without tameness, V2.33;
what tameness adds is the dimension $d_O(x)$ of the quadrant): the smooth vectors
$\hat e_j = Dr(x)T^{-1}(e_{i_j}, 0)$ satisfy $\lambda_{i_k}(\hat e_j) = \delta_{jk}$ by Proposition
2.35, and the splitting applies to $A = T_xO$, $B = T^R_xO$; $T^R_xO$ is an sc-subspace because the
smooth points $Dr(x)T^{-1}(a, w')$, $w' \in W_\infty$, lie in it ($Dr(x)E_x \subseteq E_x$) and
approximate $u$, $Tu = (a, w)$, on every level.

**V2.43 (Definition 2.37; `Polyfold.MPolyfold.IsTame`, `Polyfold.MPolyfold.isChart_of_mem_equiv`,
`Polyfold.MPolyfold.IsTame.exists_chart`).** $X$ is *tame* if some atlas equivalent to its atlas
consists of charts with tame models; then every point lies in a chart of the structure whose model is
a tame retract. *Book:* Definition 2.37, p. 42. *Hidden hypotheses:* none.

**V2.44 (Definition 2.39; `Polyfold.MPolyfold.IsFace`, `Polyfold.MPolyfold.IsFaceStructured`,
`Polyfold.MPolyfold.IsFace.isClosed`, `Polyfold.MPolyfold.IsFace.subset_boundary`).** A *face* is the
closure of the connected component in $\{d_X = 1\}$ of a point with $d_X = 1$; $X$ is
*face-structured* if every $x$ lies in exactly $d_X(x)$ faces. Faces are closed and contained in
$\partial X$. *Book:* Definition 2.39, p. 43. *Hidden hypotheses:* none.

**V2.45 (the local geometry of faces; `Polyfold.subset_coordHyper_of_isPreconnected`,
`Polyfold.IsSc1With.apply_deriv_eq_zero_of_ray`, `Polyfold.ray_zeroSet`,
`Polyfold.local_face_structure`, `Polyfold.eventually_zeroSet_subset`,
`Polyfold.convex_ball_inter_zeroSet_eq`, `Polyfold.ScRetraction.faceStratum`,
`Polyfold.coordHyper`).** With $\lambda_i = (T\,\cdot)_i$, $I(z) = \{i : \lambda_i(z) = 0\}$ and $f_i =
\{\lambda_i = 0\}$: (a) a preconnected subset of $\{z \in C : d_C(z) = 1\}$ containing a point of
$f_i$ lies in $f_i$; (b) if $r$ is tame for $T$, $x \in O_1$ smooth, $i \in I(x)$, $\lambda_i(y) = 0$
and $\lambda_l(y) > 0$ for the other $l \in I(x)$, then for all small $\tau > 0$, $x + \tau y \in
U$, $I(x + \tau y) = \{i\}$ and $I(r(x + \tau y)) = \{i\}$; (c) for $e \in O$ with $\lambda_i(e) = 0$
there are $\varepsilon > 0$ and $p \in S = \{z \in O : d_C(z) = 1\}$ with $\lambda_i(p) = 0$ such that
$B = B_\varepsilon(e) \cap C \subseteq U$, $I(z) \subseteq I(e)$ and $I(r(z)) \subseteq I(e)$ on $B$,
$r$ maps the points of $B$ with $I = \{i\}$ into the component of $S$ through $p$, and maps $f_i \cap
B$ into its closure. *Book:* the proof of Lemma 2.40, p. 43 (a sketch). *Deviation (not in the
book):* the exposition's Lemmas 4.A–4.C; (b) uses tameness condition (2) through Proposition 2.35.

**V2.46 (Lemma 2.40; `Polyfold.ScRetraction.IsRetractFace`, `Polyfold.lemma_2_40`,
`Polyfold.lemma_2_40_injective`, `Polyfold.closure_connectedComponentIn_faceStratum`,
`Polyfold.connectedComponentIn_coordHyper_eq`, `Polyfold.LocalModel.isFace_toMPolyfold_iff`,
`Polyfold.subset_of_relClopen_of_isPreconnected`).** Let $r$ be tame for $T$. A *face of the
retract* is $\overline{\hat F} \cap O$ for a connected component $\hat F$ of $S$. Then $G$ is a face
of the retract iff $G$ is the connected component of $f_i \cap O$ through some $e \in O$ with
$\lambda_i(e) = 0$; and for $x \in O$ with $\lambda_i(x) = 0$, equal components of $f_i \cap O$ and
$f_j \cap O$ through $x$ force $i = j$. The faces of the M-polyfold $O$ are exactly the faces of the
retract. *Book:* Lemma 2.40, p. 43. *Hidden hypotheses:* the face preservation of V2.45, which the
text's sketch does not address. *Deviation (hypotheses explicit):* extended faces are the
coordinate hyperplanes of a presentation.

**V2.47 (Corollary 2.41; `Polyfold.corollary_2_41`, `Polyfold.corollary_2_41_retract`,
`Polyfold.LocalModel.isFaceStructured_toMPolyfold`).** For a nonempty tame retract $O$, the
M-polyfold $O$ is face-structured: every $x \in O$ lies in exactly $d_O(x)$ faces. *Book:* Corollary
2.41, p. 44. *Hidden hypotheses:* none.

**V2.48 (Proposition 2.42; `Polyfold.proposition_2_42`, `Polyfold.MPolyfold.faces_encard_le`,
`Polyfold.MPolyfold.IsTame.exists_chart`).** Let $X$ be tame and $x \in X$. There is a chart
$\varphi : V \to O$ of the structure around $x$ such that for all $y \in V$, $d_X(y) =
d_C(\varphi(y))$ and $d_O(\varphi(y)) = d_X(y)$, and the M-polyfold $O$ is face-structured. Globally,
$x$ lies in at most $d_X(x)$ faces of $X$. *Book:* Proposition 2.42, p. 44. *Hidden hypotheses:* "$d_V
= d_X$" needs that a tame chart realizes $d_X$ (V2.42). *Deviation (restated):* the neighbourhood
$V$ is represented by the M-polyfold $O$.

**V2.49 (Proposition 2.43; `Polyfold.proposition_2_43`, `Polyfold.killCoord`,
`Polyfold.killCoord_mem`, `Polyfold.killCoord_eq_self`, `Polyfold.LocalModel.isSubMPolyfold_of_isFace`,
`Polyfold.faceIncl`, `Polyfold.faceProj`, `Polyfold.degIndexWith_eq_quadrantDeg_faceProj_add_one`,
`Polyfold.proposition_2_43_tameModel`, `Polyfold.MPolyfold.faceChart`,
`Polyfold.MPolyfold.faceChart_compatible_subChart`, `Polyfold.LocalModel.proposition_2_43_isTame`).**
Let $r$ be tame for $T$ and $F$ a face of the retract. (a) $F \subseteq f_i$ for some $i$, and
there is an sc-smooth retraction $s$ on a set $U^*$ with $F \subseteq U^* \subseteq U$, $U^*$
relatively open in $C$, with retract $F$ and $s = r \circ P_i$ on $U^*$, where $P_i$ is the
sc-projection onto $f_i$ killing the $i$-th coordinate; every face of the M-polyfold $O$ is a
sub-M-polyfold of $O$. (b) With the sc-operators $\iota : \mathbb R^k \oplus W \to E$ (insert a zero
$i$-th coordinate, onto $f_i$) and $\pi : E \to \mathbb R^k \oplus W$ (delete it), $\pi \circ \iota =
1$, $\iota \circ \pi = 1$ on $f_i$ and $d_C(y) = d_{C'}(\pi y) + 1$ on $f_i$ ($C' = [0, \infty)^k
\oplus W$); $r' = \pi \circ r \circ \iota$ is a tame retraction of $C'$ onto $\pi(F)$, and
$d_{C'}(\pi y) + 1 = d_C(y)$ for $y \in F$. (c) For a face $F$ of a nonempty tame retract $O$, with
its sub-M-polyfold structure, $F$ is a tame M-polyfold and $d_F(x) + 1 = d_O(x)$ for $x \in F$; the
chart $\pi : F \to \pi(F)$ is compatible with the sub-charts of Proposition 2.21. *Book:* Proposition
2.43, pp. 44–45. *Hidden hypotheses:* the face preservation of V2.45; the paracompactness of $F$
(faces are closed). *Deviation (restated):* the tame model lives on $\mathbb R^k \oplus W$ through
$\iota$, $\pi$ instead of the sc-subspace $f_1$; tameness (2) of $r'$ is proved with the complement
$(1 - Dr'(x))E'$ by Proposition 2.35, not by intersecting with $f_1$. $U^*$ is a union of balls
intersected with their $P_i$-preimages, since $P_i$ need not be norm-decreasing. *No hypothesis is
added.*

**V2.50 (Proposition 2.44; `Polyfold.MPolyfold.proposition_2_44`,
`Polyfold.proposition_2_42`, `Polyfold.LocalModel.proposition_2_43_isTame`,
`Polyfold.MPolyfold.proposition_2_44_corner`, `Polyfold.corner_retraction`,
`Polyfold.corner_tameModel`, `Polyfold.cornerIncl`, `Polyfold.cornerProj`, `Polyfold.cornerKill`,
`Polyfold.degIndexWith_eq_quadrantDeg_cornerProj_add_card`).** Let $X$ be tame and $x \in X$. There
is a chart $\varphi : V \to O$ of the structure around $x$, with a tame retraction $r$ onto $O$ (tame
for a presentation $T$), such that $\varphi(x)$ lies in exactly $d_X(x)$ faces of the M-polyfold $O$
(the local faces), and every face $F$ of $O$ is a sub-M-polyfold of $O$ which, with the induced
structure, is tame with $d_F(\varphi(x)) + 1 = d_X(x)$ when $\varphi(x) \in F$. For every $\sigma
\subseteq I(\varphi(x))$ (a set of $\#\sigma$ face germs at $x$) there are pairwise distinct faces
$F_i \ni \varphi(x)$ of the retract, $F_i \subseteq f_i$ ($i \in \sigma$), and an open $B \ni
\varphi(x)$ such that $A = \{y \in V : \varphi(y) \in B,\ \varphi(y) \in F_i\ \forall i \in
\sigma\}$ is a sub-M-polyfold of $X$, tame with its induced structure, with $d_A(y) + \#\sigma =
d_X(y)$ for all $y \in A$. The ingredients: the corner $f_\sigma = \bigcap_{i \in \sigma} f_i$ is
modelled on $\mathbb R^{n - \#\sigma} \oplus W$ through sc-operators $\iota_\sigma$, $\pi_\sigma$, with
$d_C(y) = d_{C'}(\pi_\sigma y) + \#\sigma$ on $f_\sigma$; near a point $o \in O$ with $\sigma \subseteq
I(o)$, $r \circ P_\sigma$ ($P_\sigma = \iota_\sigma\pi_\sigma$) is an sc-smooth retraction onto $O \cap V
\cap f_\sigma = O \cap V \cap \bigcap_{i\in\sigma}F_i$; and $\pi_\sigma \circ r \circ \iota_\sigma$ is a tame
retraction of $[0, \infty)^{n - \#\sigma} \oplus W$ onto its image under $\pi_\sigma$. *Book:*
Proposition 2.44, p. 46 (stated without proof). *Hidden hypotheses:* none. *Deviation (restated):*
local faces are the faces of the M-polyfold $O \cong V$, face germs at $x$ are the faces $F_i$, $i
\in I(\varphi(x))$, "the germ $F^\sigma_x$" is represented by the set $A$, and "codimension
$\#\sigma$" is the number of quadrant coordinates removed in the tame model; the index identity holds
on all of $A$. *Proof:* not by the exposition's induction on $\#\sigma$ but at once: Lemma 4.C for
each $i \in \sigma$ shows that $r$ maps points of $C \cap f_\sigma$ near $\varphi(x)$ into
$f_\sigma$; then as in Proposition 2.43 and Theorem 2.45.

**V2.51 (Theorem 2.45; `Polyfold.MPolyfold.theorem_2_45_interior`,
`Polyfold.MPolyfold.isSubMPolyfold_of_local`, `Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_interior`,
`Polyfold.MPolyfold.exists_localFace_of_isFaceStructured`,
`Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_face`, `Polyfold.MPolyfold.theorem_2_45_isTame_face`,
`Polyfold.MPolyfold.isTame_of_forall_exists_chart`).** Let $X$ be tame, $G$ the connected component
of $\{d_X = 1\}$ through a point and $F = \overline G$ the face. (a) $F \cap \{d_X = 1\} = G$, and
$G$ is a sub-M-polyfold of $X$. (b) If $X$ is face-structured, every face $F$ agrees near each of its
points, in a tame chart, with a face of the model retract; $F$ is a sub-M-polyfold of $X$, tame with
its induced structure, and $d_X(x) = d_F(x) + 1$ for $x \in F$. (A subset $A$ is a sub-M-polyfold as
soon as near each point $\varphi(A)$ agrees on an open set with an sc-smooth retract contained in
$O$; $X$ is tame as soon as every point lies in a chart of the structure with a tame model.) *Book:*
Theorem 2.45, p. 46 (stated without proof). *Hidden hypotheses:* the meaning of "the interior of a
face", here $F \cap \{d_X = 1\}$. *Deviation (hypotheses explicit):* the counting argument behind
"each global face through $x$ contains exactly one local face" (onto by Lemma 4.C, injective by
face-structuredness) is made explicit. The theorem's face counts are V2.48 and the definition of
face-structured (V2.44).

**V2.52 (products of M-polyfolds, exposition Lemma 4.D; `Polyfold.IsPartialQuadrant.prod`,
`Polyfold.prod_eq_prodPresentation`, `Polyfold.degIndex_prod`,
`Polyfold.minimalSubspaceWith_prodPresentation`, `Polyfold.ScRetraction.prod`,
`Polyfold.IsScRetract.prod`, `Polyfold.ScRetraction.IsTameWith.prod`, `Polyfold.MChart.prod`,
`Polyfold.MChart.Compatible.prod`, `Polyfold.MPolyfold.paracompactSpace_prod`,
`Polyfold.MPolyfold.prod`, `Polyfold.MPolyfold.degIndex_prod_le`, `Polyfold.MPolyfold.isTame_prod`,
`Polyfold.MPolyfold.isScSmoothMap_fst`, `Polyfold.MPolyfold.isScSmoothMap_snd`,
`Polyfold.MPolyfold.IsScSmoothOn.prodMk`).** For partial quadrants $C \subseteq E$, $C' \subseteq
E'$, $C \times C'$ is a partial quadrant of $E \oplus E'$, presented by $E \oplus E' \cong \mathbb
R^{n+n'} \oplus (W \oplus W')$, with $d_{C \times C'}(x, x') = d_C(x) + d_{C'}(x')$ and minimal
subspace $E_x \oplus E'_{x'}$; products of sc-smooth (tame) retractions are sc-smooth (tame)
retractions. For M-polyfolds $X$, $Y$ the space $X \times Y$ is paracompact and the product charts
are an atlas of an M-polyfold structure; $d_{X \times Y}(x, y) \le d_X(x) + d_Y(y)$, and if $X$, $Y$
are tame, $X \times Y$ is tame with equality. The projections are sc-smooth and the pairing of
sc-smooth maps is sc-smooth. *Book:* used without statement in the proof of Proposition 2.46, p. 47
("$d_{X\times Y} = d_X + d_Y$"). *Hidden hypotheses:* the additivity needs tameness; in general only
the inequality holds. Paracompactness of $X \times Y$ is Theorem 2.16. *Deviation (extra):* not
stated in the text; the exposition's Lemma 4.D.

**V2.53 (Proposition 2.46; `Polyfold.MPolyfold.IsLocalScDiffeo`, `Polyfold.MPolyfold.fibredProduct`,
`Polyfold.MPolyfold.fibredSubDataL`, `Polyfold.MPolyfold.isSubMPolyfold_fibredProduct`,
`Polyfold.MPolyfold.isScDiffeoOn_snd_fibredProduct`,
`Polyfold.MPolyfold.isScDiffeoOn_fst_fibredProduct`,
`Polyfold.MPolyfold.degIndex_fibredProduct_eq_snd`, `Polyfold.MPolyfold.degIndex_fibredProduct_eq_fst`,
`Polyfold.MPolyfold.isTame_fibredProduct`, `Polyfold.MPolyfold.proposition_2_46`,
`Polyfold.MPolyfold.proposition_2_46_of_isLocalScDiffeo`).** Let $f : X \to Z$ be a local
sc-diffeomorphism (every point has an open neighbourhood that $f$ maps sc-diffeomorphically onto an
open subset of $Z$) and $g : Y \to Z$ sc-smooth. Then $X {}_f\times_g Y = \{(x, y) : f(x) = g(y)\}$
is closed in $X \times Y$, hence paracompact, and a sub-M-polyfold of $X \times Y$, near each point
the retract of $R(x', y') = ((f|_U)^{-1}(g(y')), y')$; $d_{X {}_f\times_g Y}(x, y) = d_Y(y)$; if $Y$
is tame, so is the fibred product. If $g$ is also a local sc-diffeomorphism, then
$d_{X {}_f\times_g Y}(x, y) = d_X(x) = d_Y(y)$, and if moreover $X$ and $Y$ are tame,
$2\,d_{X {}_f\times_g Y}(x, y) = d_{X \times Y}(x, y)$. *Book:* Proposition 2.46, pp. 46–47.
*Hidden hypotheses:* the meaning of "local sc-diffeomorphism"; the paracompactness of the fibred
product. The text's $\pi_2 : X {}_f\times_g Y \to X$ has target $Y$. *Deviation (stronger):*
$d = d_Y$, and $d = d_X = d_Y$ in the last statement, hold without tameness (Proposition 2.24 along
$\pi_2$, $\pi_1$); tameness is used only for $d_{X \times Y} = d_X + d_Y$ (V2.52). The inverse of
$\pi_2$ near $(x, y)$ is $y' \mapsto ((f|_U)^{-1}(g(y')), y')$; the exposition's factorization through
the constant-in-$x$ map $y' \mapsto (x, y')$ is not sc-smooth unless $x$ is a smooth point. *No
hypothesis is added.*

**V2.54 (Definition 2.47; `Polyfold.doubleLevel`, `Polyfold.shiftFiber`,
`Polyfold.IsStrongBundleMap`, `Polyfold.IsStrongBundleRetraction`,
`Polyfold.IsPartialQuadrant.prod_univ`, `Polyfold.IsRelOpenInQuadrant.prod_univ`,
`Polyfold.IsStrongBundleRetraction.baseRetraction`, `Polyfold.IsStrongBundleRetraction.fiber_idem`,
`Polyfold.IsStrongBundleRetraction.toScRetraction`,
`Polyfold.IsStrongBundleRetraction.toScRetractionOne`).** $C \times F_0$ is a partial quadrant in $E
\oplus F$ and $U \times F_0$ is relatively open in it. A *strong bundle map* on $U \triangleleft F$
is $\Phi : E_0 \times F_0 \to E'_0 \times F'_0$ mapping $U \times F_0$ into $U' \times F'_0$, whose
first component does not depend on $h$ and second is linear in $h$ for $u \in U$, mapping $U_m
\oplus F_k$ into $U'_m \oplus F'_k$ for $k \le m + 1$, sc-smooth on $U \times F_0$ for $E \oplus F$,
and whose induced map on $U \times F_1$ (fibre component lifted to $F'_1$) is sc-smooth for $E \oplus
F^1$. A *strong bundle retraction* is one with $R \circ R = R$ on $U \times F_0$. Then $r(u) = R(u,
0)_1$ is an sc-smooth retraction on $U$, $\Gamma(u, \cdot)$ is a projection for $u \in O$, and $R$ is
an sc-smooth retraction on $(U \triangleleft F)[0]$ and $[1]$. *Book:* Definition 2.47 and the remarks
after it, pp. 48–49. *Hidden hypotheses:* $U \triangleleft F$ relatively open in a partial quadrant
(for "sc-smooth" to make sense). *Deviation (restated):* strong bundle isomorphisms are not defined
separately.

**V2.55 (Definition 2.48 and $K[i]$; `Polyfold.IsStrongBundleRetract`, `Polyfold.strongLevel`,
`Polyfold.strongLevelShift`, `Polyfold.strongShiftOne`,
`Polyfold.IsStrongBundleRetraction.mem_image_iff`,
`Polyfold.IsStrongBundleRetraction.toScRetractionOne_retract`,
`Polyfold.IsStrongBundleRetract.isScRetract`, `Polyfold.IsStrongBundleRetract.isScRetract_one`,
`Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst`,
`Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst_one`,
`Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_shiftIncl`).** $K$ is a *local strong bundle
retract* over $C$ if $K = R(U \times F_0)$ for a strong bundle retraction on a relatively open $U
\subseteq C$; then $K = \{(u, h) : u \in O, \Gamma(u, h) = h\}$. $K_{m,k}$ and $K[1] = \{(u, h) \in
E_0 \times F_1 : (u, \iota_1 h) \in K\}$ are defined level by level; $K$ is a retract in $(C \times
F_0, E \oplus F)$, $K[1]$ (the image of $R$ on $(U \triangleleft F)[1]$) a retract in $(C \times F_0,
E \oplus F^1)$, and the projections $K[i] \to O$ and the inclusion $K[1] \to K[0]$ are sc-smooth.
*Book:* Definition 2.48 and pp. 49–50. *Hidden hypotheses:* that $R$ preserves the double filtration
at $(0, 1)$, for $K[1] = R((U \triangleleft F)[1])$. *Deviation (restated):* none in substance.

**V2.56 (Definition 2.49; `Polyfold.IsScSmoothSection`, `Polyfold.IsScPlusSection`,
`Polyfold.IsScPlusSection.mem`, `Polyfold.IsScPlusSection.isScSmoothSection`).** An *sc-smooth
section* of $p : K \to O$ is $f$ with $f(x)_1 = x$ on $O$, sc-smooth from $(O, C, E)$ to $(K, C
\times F_0, E \oplus F)$; an *sc⁺-section* is $f : E_0 \to E_0 \times F_1$ with $f(x)_1 = x$ on $O$,
sc-smooth into $(K[1], C \times F_0, E \oplus F^1)$. An sc⁺-section is an sc-smooth section. *Book:*
Definition 2.49, p. 50 ($K(0)$, $K(1)$ for $K[0]$, $K[1]$). *Deviation (restated):* the category
$\mathcal{SBR}$ is not formalized.

**V2.57 (Definition 2.50; `Polyfold.IsBanachable`, `Polyfold.StrongBundleChart`,
`Polyfold.StrongBundleChart.K`, `Polyfold.StrongBundleChart.continuous_fiber`,
`Polyfold.StrongBundleChart.Compatible`, `Polyfold.StrongBundleChart.Compatible.symm`,
`Polyfold.StrongBundleAtlas`, `Polyfold.StrongBundleAtlas.Equiv`,
`Polyfold.StrongBundleChart.compatible_of_locally`, `Polyfold.StrongBundleAtlas.equiv_iff`,
`Polyfold.StrongBundleAtlas.Equiv.trans`, `Polyfold.StrongBundleAtlas.equivalence`,
`Polyfold.IsStrongBundleRetraction.restrict`, `Polyfold.StrongBundleChart.restrict`,
`Polyfold.StrongBundleChart.Compatible.restrict`).** For $P : Y \to X$ with linear structures on the
fibres: a *strong bundle chart* is a chart $\varphi$ of the M-polyfold $X$, an sc-Banach space $F$,
a strong bundle retraction $R$ on a relatively open $U \subseteq C$ with base retract $O$, and a
homeomorphism $\Phi : P^{-1}(V) \to K = R(U \times F_0)$ with $\Phi(y)_1 = \varphi(P(y))$ and linear
on each fibre (hence continuous on fibres). Two charts are *compatible* if $\Phi' \circ \Phi^{-1}$
and $\Phi \circ \Phi'^{-1}$ are sc-smooth between the overlaps on $[0]$ and, through the lift to
$F_1$, on $[1]$, and carry fibre components in $F_1$ to fibre components in $F'_1$. Atlases and
their equivalence as in V2.11; two atlases are equivalent iff every chart of one is compatible with
every chart of the other, and the relation is an equivalence relation (it rests on the locality of
compatibility: near a point of the overlap a transition factors through a chart of the middle atlas,
on $[0]$ and on $[1]$). A strong bundle chart restricts to every open $s \subseteq V$ (retraction
domain $U \cap r^{-1}(W)$ for $\varphi(s) = O \cap W$,
$K_s = \{(u, h) \in K \mid u \in \varphi(s)\}$, $\Phi$ unchanged), and restrictions of compatible
charts are compatible. A space is *Banachable* if it is linearly homeomorphic to a Banach space.
*Book:* Definition 2.50, pp. 51–52. *Hidden hypotheses:* $\varphi$ a chart of $X$ (the text: a
homeomorphism onto $O$); the $[1]$-transition condition. *Deviation (hypotheses explicit):* both
stated. The transitivity of the equivalence, which “an equivalence class of strong bundle atlases”
(Definition 2.51) presupposes, and the restriction of charts, which the text uses silently (Lemma
5.2), are proved (Findings, Chapter 2, items 40, 42); a restriction whose retraction domain lies
inside a given open $W \ni 0$ of $E$ is not, since $U \cap W$ need not be invariant under $r$.

**V2.58 (Definition 2.51, strong bundles, $Y[0]$, $Y[1]$, $P[0]$, $P[1]$; `Polyfold.StrongBundle`,
`Polyfold.StrongBundleChart.toMChart`, `Polyfold.StrongBundleChart.Compatible.toMChart`,
`Polyfold.StrongBundle.atlas0`, `Polyfold.StrongBundle.toMPolyfold0`,
`Polyfold.StrongBundle.isScSmoothMap_proj`, `Polyfold.StrongBundle.doubleLevel`,
`Polyfold.StrongBundle.mem_doubleLevel_iff`, `Polyfold.StrongBundle.oneChart`,
`Polyfold.StrongBundle.oneChart_compatible`, `Polyfold.StrongBundle.atlas1`,
`Polyfold.StrongBundle.toMPolyfold1`, `Polyfold.StrongBundle.isScSmoothMap_proj1`,
`Polyfold.StrongBundle.maximalAtlas`, `Polyfold.StrongBundle.maximalAtlas_equiv`,
`Polyfold.StrongBundle.isChart_iff_exists_equiv`, `Polyfold.StrongBundle.isChart_congr`,
`Polyfold.StrongBundle.IsChart.compatible`, `Polyfold.StrongBundle.IsChart.restrict`).** A *strong
bundle* is a continuous surjection $P : Y \to X$, $Y$ Hausdorff paracompact, with Banachable fibres
and a strong bundle atlas. The charts $\Phi$ form an sc-smooth atlas of $Y$ (the M-polyfold $Y[0]$),
and $P : Y[0] \to X$ is sc-smooth. $Y_{m,k}$ ($k \le m + 1$) is the set of $y$ with
$\Phi(y) \in E_m \times F_k$ in the charts of the atlas around $y$; one chart around $y$ suffices.
The charts $\Phi[1] : y \mapsto (\Phi(y)_1, \Phi(y)_2$ lifted to $F_1)$, defined on $Y_{0,1}$ with
the topology they generate and onto the retracts $K[1]$, are pairwise compatible, their transition
maps being the $[1]$-transitions of Definition 2.50, and make $Y[1]$ an M-polyfold;
$P[1] : Y[1] \to X$ is sc-smooth. The charts of the strong bundle (compatible with the atlas) are
those of the maximal atlas, which is equivalent to the given one: a chart is one iff it belongs to
some atlas of the class, any two are compatible, restrictions of charts are charts, and equivalent
atlases have the same charts. *Book:* Definition 2.51 and the remarks after it, p. 52. *Hidden
hypotheses:* the paracompactness of $Y[1]$ (proved, V2.64); for the chart-independence of
$Y_{m,m+1}$ and of $Y_{0,1}$, the $F_1$-condition on the $[1]$-transition (V2.57). *Deviation
(restated):* $Y[1]$ carries the topology generated by the charts $\Phi[1]$, as $X_m$ in §2.2; the
charts are those induced by the given atlas. The notions defined through the charts compatible with
the atlas depend only on the class; those defined with the charts of the given atlas itself
($Y_{m,k}$, $Y[1]$ and its atlas, sc⁺-sections) are not shown invariant (Findings, Chapter 2, item
43).

**V2.59 (Definition 2.52; `Polyfold.IsSection`, `Polyfold.StrongBundle.IsScSmoothSection`,
`Polyfold.StrongBundle.localRepOne`, `Polyfold.StrongBundle.IsScPlusSection`).** A *section* is $f$
with $P \circ f = \mathrm{id}$; it is *sc-smooth* if it is sc-smooth $X \to Y[0]$, and an
*sc⁺-section* if in every chart of the atlas its fibre values lie in $F_1$ and its local
representative, lifted to $E_0 \times F_1$, is sc-smooth from $O$ into $K[1]$. *Book:* Definition
2.52, p. 53. *Deviation (restated):* sc⁺ is defined chart by chart; this is equivalent to the
text's definition: $f$ is an sc⁺-section iff $P \circ f = \mathrm{id}$ and $f = \iota \circ g$ for an
sc-smooth $g : X \to Y[1]$, $\iota : Y[1] \to Y$ the inclusion
(`Polyfold.StrongBundle.isScPlusSection_iff`).

**V2.60 (Definition 2.53; `Polyfold.pullbackSpace`, `Polyfold.pullbackProj`,
`Polyfold.pullbackProj'`, `Polyfold.pullback_comm`, `Polyfold.continuous_pullbackProj`,
`Polyfold.isClosed_pullbackSpace`).** $f^*Y = \{(z, y) : P(y) = f(z)\}$ with the projections $P_f$,
$P'$; $P \circ P' = f \circ P_f$; $P_f$ is continuous, and $f^*Y$ is closed in $Z \times Y$ when $X$
is Hausdorff and $P$, $f$ are continuous. *Book:* Definition 2.53, p. 53. *Hidden hypotheses:*
none.

**V2.61 (Proposition 2.54; `Polyfold.proposition_2_54`, `Polyfold.pullbackAtlas`,
`Polyfold.PullbackChartData`, `Polyfold.PullbackChartData.toChart`,
`Polyfold.PullbackChartData.transition_eqOn`, `Polyfold.PullbackChartData.transition_isScSmooth`,
`Polyfold.PullbackChartData.transitionOne_isScSmooth`,
`Polyfold.PullbackChartData.compatible_toChart`, `Polyfold.paracompactSpace_pullbackSpace`,
`Polyfold.pullbackFiberCLE`, `Polyfold.pullbackRetraction`,
`Polyfold.isStrongBundleRetraction_pullback`, `Polyfold.pullback_image`,
`Polyfold.isStrongBundleRetract_pullback`).** Let $P : Y \to X$ be a strong bundle and $f : Z \to X$
sc-smooth. Then $f^*Y$ is paracompact, and $P_f : f^*Y \to Z$ is a strong bundle whose atlas
consists of the pulled-back charts: for a strong bundle chart $\Phi$ over $\varphi$ and a chart
$\psi$ of $Z$ with $f(\operatorname{dom}\psi) \subseteq \operatorname{dom}\varphi$ and
$g = \varphi \circ f \circ \psi^{-1}$, the chart $\Phi_f(z, y) = (\psi(z), \mathrm{pr}_F\Phi(y))$
onto $K_g = \{(w, h) : w \in O_Z, (g(w), h) \in K\}$, the image of the strong bundle retraction
$R_g(w, h) = (r_Z(w), \Gamma(g(r_Z(w)), h))$. Its fibres are $P_f^{-1}(z) \cong P^{-1}(f(z))$ (a
linear homeomorphism). Transition maps of pulled-back charts are
$(w, h) \mapsto (\psi_2\psi_1^{-1}(w), \mathrm{pr}_F(\Phi_2\Phi_1^{-1})(g_1(w), h))$ and are
sc-smooth on $[0]$ and $[1]$. *Book:* Proposition 2.54, p. 53 ("the easy proof is left to the
reader"). *Hidden hypotheses:* $f^*Y$ paracompact (required by Definition 2.51, not mentioned);
proved from Theorem 2.16 for $Z$ and $Y[0]$. *Deviation (hypotheses explicit):* "natural structure"
is the atlas of all pulled-back charts. That the projection $P' : f^*Y \to Y$ is a strong bundle map
(sc-smooth on $[0]$ and $[1]$), which “natural” presumably also says, is not formalized (Findings,
Chapter 2, item 51).

**V2.62 (Theorem 2.55, Smirnov's theorem; `Polyfold.metrizableSpace_of_locally`,
`Polyfold.metrizableSpace_of_partition`, `Polyfold.metrizableSpace_of_pullback`,
`Polyfold.cone_triangle`, `Polyfold.truncDist`, `Polyfold.paracompactSpace_of_metrizableSpace`).** A
paracompact Hausdorff space in which every point has a metrizable open neighbourhood is metrizable.
More generally, a space $Y$ with open metrizable subspaces $V_i$ and a locally finite family of
continuous $\rho_i \ge 0$ with $\operatorname{supp}\rho_i \subseteq V_i$, not all vanishing at any
point, is metrizable, with the metric $\sum_i |\rho_i(x) - \rho_i(y)| + \min(\rho_i(x), \rho_i(y))
\min(d_i(x, y), 1)$; and if $\pi : Y \to X$ is continuous into a paracompact Hausdorff $X$ whose
points have open neighbourhoods $U$ with $\pi^{-1}(U)$ metrizable, $Y$ is metrizable. Metrizable
spaces are paracompact. *Book:* Theorem 2.55, p. 56, quoted from Smirnov. *Deviation (stronger):*
proved, in the pull-back form used for $X_m$ and $TX$.

**V2.63 (restriction and locality of sc^k maps; `Polyfold.IsSck.of_subset`,
`Polyfold.IsScSmooth.of_subset`, `Polyfold.IsSc1.tangentMap_eqOn_of_subset`,
`Polyfold.IsSc1.of_locally`, `Polyfold.IsSck.of_locally`, `Polyfold.IsScSmooth.of_locally`,
`Polyfold.IsScSmooth.congr`).** On sc-domains: an $\mathrm{sc}^k$ map restricts to $\mathrm{sc}^k$ on
every smaller sc-domain, with the same tangent map there; a map that is $\mathrm{sc}^1$ (resp.
$\mathrm{sc}^k$, sc-smooth) on $U \cap W$ for an open $W$ around each point of $U$ is $\mathrm{sc}^1$
(resp. $\mathrm{sc}^k$, sc-smooth) on $U$; sc-smoothness depends only on the values on $U$. *Book:*
used without statement in §2.1–§2.2 (Propositions 2.4, 2.10, Definitions 2.13–2.14). *Deviation (not
in the book):* infrastructure the text uses silently.

**V2.64 (the space $Y[1]$ and the inclusion $Y[1] \to Y[0]$; `Polyfold.StrongBundle.oneSet`,
`Polyfold.StrongBundle.mem_oneSet_iff`, `Polyfold.StrongBundle.One`,
`Polyfold.StrongBundle.continuous_oneVal`, `Polyfold.StrongBundle.metrizableSpace_one`,
`Polyfold.StrongBundle.paracompactSpace_one`, `Polyfold.StrongBundle.isScSmoothMap_oneVal`).** For a
strong bundle $P : Y \to X$, $Y_{0,1}$ is the set of points whose fibre component lies in $F_1$ in
every chart of the atlas around them, and one such chart suffices. With the topology generated by the
charts $\Phi[1]$ (V2.58), the inclusion $Y[1] \to Y$ is continuous, so $Y[1]$ is Hausdorff; $Y[1]$ is
metrizable, hence paracompact; and the inclusion $Y[1] \to Y[0]$ is sc-smooth (in the charts
$\Phi[1]$, $\Phi$ it is $(u, h) \mapsto (u, \iota h)$). *Book:* not stated; the text takes $Y[1]$ to
be an M-polyfold on $Y_{0,1}$ (p. 52). *Hidden hypotheses:* paracompactness of $Y[1]$, required by
Definition 2.13. *Deviation (not in the book):* proved; metrizability by the pull-back form of
Smirnov's theorem over the paracompact base (V2.62), as in Theorem 2.16.

### What is not verified in this chapter

- p. 18, Proposition 2.2 (classical $C^\infty$ retractions have submanifold images): motivation
  only; not attempted (the exposition proves it, §8.1).
- p. 22, Definition 2.9 (sc-smooth bundle retractions, the categories $\mathcal R$, $\mathcal{BR}$):
  not formalized as a definition; its instances ($Tr$, strong bundle retractions) are.
- p. 25, $X_m$ as an M-polyfold for $m \ge 2$: only $X^1$ is constructed (V2.16); the iterate $(X^1)^1 \cdots$ has the
  points of $X_m$, its topology is not compared with that of $X_m$; Theorem 2.16 is proved for every $m$.
- pp. 26–30, the vector space, Banach and sc-Banach structures of $T_xX$, and Proposition 2.21 (3),
  (4) in $T_aX$ rather than in a chart: not formalized.
- p. 27, Proposition 2.19 (2), openness of $p : TX \to X_1$: not proved (not used).
- pp. 33–35, Lemma 2.29 in its path formulation, and $T_xO = C_xO - C_xO$: not formalized; the sign
  arguments are V2.34.
- p. 39, the intrinsic description of extended faces ($k$ components of $\{d_C = 1\}$, minimal
  subspaces, independence of the presentation): the formalization works in a presentation.
- p. 42, Definition 2.38 ($T^R_xX$, $C_xX$ in $T_xX$): only the local form, its invariance and the
  partial quadrant $C_oO$ (in a tame chart V2.42, in any chart V2.33); not the transport to $T_xX$
  or $d_{C_xX}(0_x) = d_X(x)$.
- pp. 48–51, strong bundle isomorphisms, the category $\mathcal{SBR}$ and the functors
  $\mathrm{forget}[i]$: not formalized.
- p. 53, Proposition 2.54: that the projection $P' : f^*Y \to Y$ of the pull-back is a strong bundle
  map; the pulled-back atlas is V2.61.
- p. 56, Lemma 2.56 and Proposition 2.57: not needed, since the proofs of Theorem 2.16 and
  Proposition 2.19 (3) avoid them.

---

## 4. Chapter 3 (HWZ §§3.1–3.8): partly verified

Chapter 3 of Part I (preprint pp. 61–146) develops sc-Fredholm theory. §3.1 defines germs, sections
of strong bundles, fillers, basic germs, sc-Fredholm germs and sections, proves local compactness
(Theorem 3.12) and the stability under sc⁺-perturbations (Theorem 3.15), and states the implicit
function theorems (Theorems 3.19, 3.23), with good position (Definition 3.21, Proposition 3.22). §3.2
introduces the tangent germ property and shows that it makes a subset a sub-M-polyfold (Definition
3.25, Proposition 3.26, Theorem 3.27). §3.3 proves the germ implicit function theorem (Definition
3.28, Theorems 3.29–3.35). §3.4 proves that basic germs are stable under sc⁺-perturbations (Theorem
3.38). §3.5 proves local regularity and compactness (Theorem 3.40) and local solvability (Corollary
3.41, Theorem 3.43, Corollary 3.47). §3.6 states and proves the implicit function theorem for
sc-Fredholm sections (Proposition 3.52, Definition 3.53, Theorem 3.54, Lemma 3.55) and its global
forms (Theorems 3.56, 3.57). §3.7 gives a criterion for being conjugate to a basic germ (Theorem
3.58, Lemmas 3.59–3.61). The appendix §3.8 proves Proposition 3.22, Lemma 3.46, Lemma 3.55, and
the inverse and implicit function theorems in partial quadrants (Theorems 3.72, 3.78).

What is verified. **The germ implicit function theorem (Theorem 3.33) holds with the text's
hypotheses**, and so do Corollary 3.34 and Theorem 3.35: the solution germ is sc^k on the germ of
neighbourhoods shrunk by $2^k - 1$ levels, and sc-smooth on one diagonal germ, which shrinks fast
with the level (V3.31, V3.32). **The implicit function theorems also hold with the text's
hypotheses, local and global**: Theorems 3.54, 3.23 and 3.19 (V3.94, V3.95), Theorem 3.57, Corollary
3.24 and Theorem 3.56 (V3.87, V3.70, V3.86), once three steps of the text's proof are replaced. The
surjectivity of $f'(y)$ at the zeros $y$ near a given zero, which the text derives from Corollary
3.41 and which does not follow from it (V3.82; the same step stands in the book's arXiv version), is
proved by a new argument, an implicit function theorem at the nearby zero for a perturbed equation
(V3.93); the regularity of the solution germ away from the centre is proved by re-centring (V3.73,
V3.74); and the relative openness of the set $\Sigma$ in the proof of Theorem 3.27 by the choice of
the good complement (V3.75, V3.77). With them: the dimension of the solution set is the Fredholm
index (V3.96, V3.97), the index is locally constant along the solution set (V3.98; also without good
position, with the text's hypotheses: tame germ data and no bump functions), and so, with the
text's hypotheses, is the index of Definition 6.1 (read with the text's locally defined
sc⁺-sections) along sc-smooth paths $\mathbb R \to X$, the text's Proposition 6.2 for paths on
$\mathbb R$ (V3.98), $\ker f'(y)$ is the tangent space of the solution
set in a chart (V3.99), and good
position is the surjectivity of $f'(y)$ at zeros with $d_X(y) = 0$, so that Theorems 3.19 and 3.56
hold with the text's hypothesis "$f'(x)$ surjective" (V3.100, V3.101). The forms first proved under
an added filler condition at the nearby zeros (V3.68, V3.69, V3.82, V3.85) are kept; that condition
follows from good position (V3.102), and with Definition 3.4 as stated the text's argument gives the
kernel half of Theorem 3.54 (1) (V3.81) but not the surjectivity. All these statements are the
repaired ones. They were first proved under the hypothesis that the base retraction of every strong
bundle chart compatible with the atlas is tame, which no strong bundle over a nonempty base
satisfies (V3.104, where only the half of the argument that concerns retractions is
machine-checked), so those first statements were vacuous; they now assume what the text's
Definitions 3.50, 3.51 and 3.53 ask, germ data and good position in a chart whose base retraction is
tame, and conclude good position in such charts (V3.103, V3.107). Also verified: every definition of
§§3.1–3.6 (Definitions 3.1–3.4, 3.6, 3.7, 3.11, 3.14, 3.21, 3.25, 3.28, 3.37, 3.48, 3.50, 3.51,
3.53; since the switch of Definition 3.11 to the text's germ reading, the fillings, the local
sc⁺-sections and every notion built on them are germs whose levels may shrink with $m$, as in the
text, V3.7, V3.9, V3.13, and so, since a fourth addendum, is Definition 3.3, V3.5); Proposition 3.5,
also in sc form (V3.8); Lemma 3.9 as stated (V3.11);
Proposition 3.10, both statements, the second on every level (V3.12); Theorems 3.12 (with fewer
hypotheses), 3.15 (without tameness), Corollary 3.13; Theorem 3.18 (without tameness), with the
linearization of the perturbed section (V3.91, V3.92); Lemmas 3.16, 3.17; Proposition 3.22 (without
the extreme-ray lemmas); Proposition 3.26; Theorem 3.27 under two added regularity conditions, each
with a counterexample to the step of the text's proof it replaces (for solution sets both are
theorems); Theorems 3.29, 3.30, Lemmas 3.31, 3.32 (as one induction), Theorem 3.38 (with a linear
coordinate change), Corollary 3.39, Theorem 3.40 (with compact closures), Corollary 3.41, Lemmas
3.42, 3.44–3.46; Theorem 3.43 and Corollary 3.47 (their clause (1), "the solution map is an
sc-smooth germ", in the level-wise sense: $C^k$ into level $k$ on a neighbourhood depending on $k$);
Remark 3.49; Proposition 3.52 in charts, as an sc-Fredholm operator with the index $n - N$ of the
conjugating basic germ on every level, in every chart (V3.46, V3.96); Lemma 3.81 as stated (V3.66);
Lemma 3.55 (with the added hypothesis that the good complement is closed); Theorem 3.54 as described
above, with its graph description; Theorem 3.58 in the coordinates of its proof; Lemmas 3.59 and
3.60 (in an abstract form, with their hypotheses derived in Theorem 3.58) and Lemma 3.61; and the
appendix except Lemmas 3.62–3.64, 3.66–3.68, 3.76, which the formal proofs avoid. Not verified:
Proposition 3.52 on $T_xX$ itself, which carries no linear structure here; $\ker f'(y) = T_yS$ with
$T_yS$ a subspace of $T_yX$ (it is verified in a chart); Proposition 6.2 for paths sc-smooth on
$[0, 1]$ only (the project has no M-polyfold $[0, 1]$); the passage from an atlas
of tame charts to tame germ data (Definition 3.11 $\Rightarrow$ Definition 3.50), which is open. Remarks 3.8 and 3.20 compare the definitions with the earlier paper [21] and
make no claim to verify. Items V3.68–V3.90 were added after the first edition of this section (the
Lean formalized after it); the earlier items whose content changed with them (V3.13, V3.23, V3.24,
V3.34, V3.38, V3.42, V3.46–V3.54, V3.59, V3.62) are updated in place. Items V3.91–V3.102 were added
in a second addendum (Theorem 3.18, Theorem 3.54 (1) with the text's hypotheses, the index of the
solution set, the kernel as tangent space, good position at interior zeros); the items whose content
changed with them (V3.46, V3.47, V3.68, V3.69, V3.81–V3.87) are updated in place. Items
V3.103–V3.107 were added after the repair of the tameness hypothesis (Findings, Chapter 3, items
190–199: the tame germ notions, the non-tame retraction behind the vacuity, Theorems 3.15 and 3.18
for tame germ data, good position in any chart of the germ data); the items whose statements changed
with it (V3.45, V3.47, V3.48, V3.68–V3.70, V3.80–V3.82, V3.84–V3.87, V3.94, V3.95, V3.97–V3.102) are
updated in place. A third addendum (sc-Fredholm theory on all levels, the one-germ form of Theorem
3.35, Lemmas 3.9 and 3.81 as stated, good position with the text's sc-complement, the index without
good position, and the difference between the text's germs and the formal definitions on the whole
chart) updated V3.5, V3.7–V3.9, V3.11–V3.13, V3.16, V3.19, V3.20, V3.22, V3.28, V3.31, V3.32, V3.43,
V3.45–V3.47, V3.66, V3.68, V3.70, V3.86, V3.87, V3.94–V3.98 and V3.103 in place. The switch of
Definition 3.11 and of everything built on it to the text's germ reading (phase 2: the canonical
notions and theorems are the germ reading, the project's earlier whole-chart ones are kept as
`…WholeChart`, `…_wholeChart`; Findings, Chapter 3, items 330–334) updated V3.5, V3.7–V3.9, V3.13,
V3.16, V3.17, V3.19, V3.43, V3.45–V3.47, V3.68, V3.78, V3.79, V3.81, V3.82, V3.91, V3.93, V3.96,
V3.98, V3.102, V3.103, V3.105 and V3.107 in place. A fourth addendum (2026-11-02: Definition 3.3 in
the germ reading, Definition 6.1 and Proposition 6.2, germ data and the charts of a tame atlas;
Findings, Chapter 3, items 340–355) updated V3.5, V3.13, V3.98 and V3.103 in place. A fifth
addendum (2026-11-02: the restriction of a strong bundle to an open set, the index along the zero set
and Proposition 6.2 without bump functions, Definition 6.1 with the text's local sections; Findings,
Chapter 3, items 349, 360–367) updated V3.68 and V3.98 in place.

The setting. Germs are fixed sequences of sets (Definition 3.1), and the calculus of germs —
restriction, chain rule, pairing, Propositions 1.16–1.18 for germs — is proved, not assumed. The
finite-dimensional parameter spaces $\mathbb R^n$, $\mathbb R^N$ are arbitrary finite-dimensional
normed spaces $P$, $Q$, and the parameter set $\widetilde C$ a convex set containing $0$ with
nonempty interior, which is closed or a partial quadrant where a theorem needs it. A "strong bundle
chart" in Definitions 3.3, 3.6, 3.11 is a chart compatible with the atlas. The fillings and the
local sc⁺-sections of Definition 3.11 are, as in the text, germs on sc-germs of neighbourhoods whose
levels may shrink with $m$ (the text's germ reading, since phase 2; V3.7, V3.9, V3.13); the
project's earlier notions, with these data on the whole $U$ of the chart (levels $U \cap E_m$), are
stricter and are kept under the names `…WholeChart`. The sc-smooth section germs of Definition 3.3,
which no theorem assumes, are germs in the same sense since a fourth addendum (V3.5; Findings,
Chapter 3, items 220–221, 330). Tameness of
the strong bundle is nowhere used in §3.1. It enters §3.6 as the text's Definitions 3.50, 3.51 and
3.53 put it: the germ data of $f$ at a point, and its good position, lie in a strong bundle chart
whose base retraction is tame (V3.103; "tame germ data" and "good position in a tame chart" below).
It is used, for the chart at the zero $x_0$, through Proposition 2.35, $(1 - Dr(0))E \subseteq E_0$,
and, for the tangent germ property of the solution set, through the tameness of the model of the
chart $\psi \circ \varphi$ (V3.71). The reading first formalized, that the base retractions of all
charts compatible with the atlas are tame, cannot be met (V3.104, the retraction-level half
machine-checked). Classical regularity in the appendix is Mathlib's $C^k$ within the set, which on
relatively open subsets of partial quadrants is the text's Definition 3.71. Findings referred to
below are those of `Exposition/Findings.md`, "Chapter 3".

**V3.1 (Definition 3.1, sc-germs of neighbourhoods; `Polyfold.ScNbhdGerm`, `Polyfold.ScNbhdGerm.tangent`,
`Polyfold.ScNbhdGerm.ofSet`, `Polyfold.IsQuadrantLike`, `Polyfold.IsPartialQuadrant.isQuadrantLike`).**
An sc-germ of neighbourhoods around $0$ in $C \subseteq E_0$ is a family $U_m \subseteq E_m$, each of the form
$O \cap C_m$ with $O$ open in $E_m$, containing $0$, with $\iota U_{m+1} \subseteq U_m$. Its tangent germ has
levels $U_{m+1} \times E_m$. A relatively open $U \ni 0$ in $C$ gives the germ $U_m = U \cap E_m$. $C$ is
quadrant-like if $0 \in C$ and every $C_m$ is convex with nonempty interior; partial quadrants are.
*Book:* Definition 3.1, p. 62. *Hidden hypotheses:* none. *Deviation (restated):* a germ is a fixed
sequence, not a class up to shrinking; the text's "the size of the sets $U_m$ does not matter" is
not built in, and the theorems say on which germ they hold. $(U_{m+1})_m$ is a germ only when all
levels coincide (finite-dimensional $E$).

**V3.2 (Definition 3.2, sc^k-germs; `Polyfold.IsSc0Germ`, `Polyfold.IsSc1GermWith`, `Polyfold.IsSc1Germ`,
`Polyfold.IsSckGerm`, `Polyfold.IsScSmoothGerm`, `Polyfold.IsSck.isSckGerm`).** $f$ is an sc⁰-germ on $(U_m)$
if $f(U_m) \subseteq F_m$ and $f : U_m \to F_m$ is continuous for every $m$; sc¹ if moreover, for a family of
bounded $Df(x) : E_0 \to F_0$, $x \in U_1$, $f$ is differentiable within $U_1$ at $x$ (increments in $E_1$,
remainder in $F_0$) with derivative $Df(x)$, and the tangent map $(x, h) \mapsto (f(x), Df(x)h)$ is an
sc⁰-germ on the tangent germ; sc^{k+1} if sc¹ with sc^k tangent map; sc-smooth if sc^k for all $k$. An
sc^k map on a relatively open $U \ni 0$ is an sc^k-germ on $(U \cap E_m)$. *Book:* Definition 3.2,
pp. 62–63. *Hidden hypotheses:* for quadrant-like $C$ the derivative is unique on $U_1$.
*Deviation:* none.

**V3.3 (the calculus of germs; `Polyfold.IsSckGerm.congr`, `Polyfold.IsSckGerm.mono`,
`Polyfold.ScNbhdGerm.MapsToGerm`, `Polyfold.IsSckGerm.comp`, `Polyfold.IsSc1Germ.comp`,
`Polyfold.ScOperator.isScSmoothGerm`, `Polyfold.IsSckGerm.pair`, `Polyfold.ScNbhdGerm.preimage`).** For
quadrant-like sets: sc^k-germs depend only on their values on $U_0$ and restrict to smaller germs; if
$f$ is an sc^k-germ on $(U_m)$, $g$ an sc^k-germ on $(V_m)$ and $f(U_m) \subseteq V_m$ for every $m$, then
$g \circ f$ is an sc^k-germ, with $T(g \circ f) = Tg \circ Tf$ on the tangent germ (k = 1); sc-operators are
sc-smooth germs on every germ; pairings of sc^k-germs are sc^k-germs; for an sc⁰-germ $f$ with
$f(0) = 0$ and a germ $G'$ around $0$ there is a germ inside $(U_m)$ on which $f$ maps into $G'$ level by
level. *Book:* not stated; used throughout §§3.3–3.6. *Hidden hypotheses:* the level-wise inclusion
$f(U_m) \subseteq V_m$ for compositions. *Deviation (not in the book).*

**V3.4 (Propositions 1.16–1.18 for germs; `Polyfold.IsSc1GermWith.exists_levelDeriv`,
`Polyfold.IsSc1GermWith.continuousOn_levelDeriv_clm`, `Polyfold.IsSc1GermWith.hasFDerivWithinAt_level`,
`Polyfold.ScNbhdGerm.shift`, `Polyfold.IsSckGerm.shift`, `Polyfold.IsSckGerm.contDiffOn_levels`).** For an
sc¹-germ with derivative family $D$ and $x \in U_{m+1}$, $D(x)$ restricts to bounded operators $E_m \to F_m$,
continuous in $x$ in the operator norm on $U_{m+1}$, and $f : U_{m+1} \to F_m$ is differentiable within
$U_{m+1}$ with these derivatives. $(U_{m+1})_m$ is a germ in $E^1$ around $0 \in C^1$, and an sc^k-germ on
$(U_m)$ is an sc^k-germ $(U_{m+1})_m \to F^1$. An sc^k-germ is $C^k$ from $U_{m+k}$ to $F_m$. *Book:* not
stated for germs; the text applies Propositions 1.16–1.18 to germs (Lemma 3.9: "recalling Proposition
1.17", which is 1.16; Lemma 3.31; Corollary 3.34). *Hidden hypotheses:* none. *Deviation (not in the
book):* the germ versions, with the proofs of Chapter 1.

**V3.5 (Definition 3.3, sc-smooth section germs; `Polyfold.StrongBundle.IsScSmoothSectionGerm`,
`Polyfold.StrongBundle.IsChart`, `Polyfold.StrongBundle.IsScSmoothSection.isScSmoothSectionGerm`,
`Polyfold.StrongBundle.isChart_congr`).** $(f, x_0)$ is an sc-smooth section germ of the strong
bundle $P : Y \to X$ if $x_0$ is smooth and in some strong bundle chart compatible with the atlas,
centred at $x_0$, the principal part $\mathbf f$ of $f$ satisfies: $\mathbf f \circ r$ is an
sc-smooth germ on some sc-germ of neighbourhoods $G$ of $0$ with $G_0 \subseteq U$. An sc-smooth
section is an sc-smooth section germ at every smooth point that has a centred chart (with the germ
$U \cap E_m$). *Book:* Definition 3.3, p. 63. *Hidden hypotheses:* "a strong bundle
chart" means a chart compatible with the atlas (a chart of the atlas need not be centred); the
notion does not depend on the atlas within its class (`Polyfold.StrongBundle.isChart_congr`, V2.58).
*Deviation (hypotheses explicit):* the chart, as just said. Since a fourth addendum the germ is the
text's: $\mathbf f \circ r$ is an sc-smooth germ on some sc-germ of neighbourhoods $G$ with $G_0
\subseteq U$, whose levels may shrink with $m$, as for Definitions 3.4, 3.6 and 3.11 since phase 2.
Until then it was required on the whole $U$ of the chart, which is stricter (a function $C^k$ on
$(-1/k, 1/k)$ for every $k$ is an sc-smooth germ in the constant scale $\mathbb R$ and sc-smooth on
no neighbourhood of $0$, `Polyfold.exists_isScSmoothGerm_not_isScSmooth`), and the item was
"narrower". No theorem assumes the definition (Findings, Chapter 3, items 220–221, 260).

**V3.6 (the section algebra and the sum rule; `Polyfold.IsScSmooth.add`, `Polyfold.sectionAdd`,
`Polyfold.StrongBundleChart.principal_sectionAdd`, `Polyfold.StrongBundleChart.isZeroAt_iff`,
`Polyfold.StrongBundleChart.add_mem_K`, `Polyfold.StrongBundle.IsScSmoothSection.isScSmoothRetractMap`,
`Polyfold.StrongBundle.IsScPlusSection.isScSmoothRetractMap_one`).** Sums, differences and negatives of
sc-smooth maps on relatively open subsets of partial quadrants are sc-smooth. The fibrewise sum $f + s$
of sections is a section, with principal part $\mathbf f + \mathbf s$ in every chart; $f(x) = 0$ iff $\mathbf
f(\varphi(x)) = 0$; the fibres of $K$ over $O$ are linear. In every strong bundle chart compatible with the
atlas, the representative $z \mapsto (z, \mathbf f(z))$ of an sc-smooth section is sc-smooth $O \to K$, and
the representative $z \mapsto (z, \mathbf s_1(z))$ of an sc⁺-section is sc-smooth $O \to K[1]$. *Book:* not
stated; used in Theorems 3.12, 3.15. *Hidden hypotheses:* the compatibility on $[1]$ of Definition
2.50 (its first use). *Deviation (not in the book).*

**V3.7 (Definition 3.4, fillers; `Polyfold.IsFillingGerm`, `Polyfold.fillDefect`,
`Polyfold.fillDefect_isScSmoothGerm`, `Polyfold.IsFillerOf`, `Polyfold.StrongRetr.r`,
`Polyfold.StrongRetr.ρ`, `Polyfold.StrongRetr.ρCLM`).** For a strong bundle retraction
$R(u, h) = (r(u), \rho(u)h)$ on $U \triangleleft F$ with $O = r(U)$, $0 \in U$: $g$ is a filling of $f$
if $g$ is an sc-smooth germ on an sc-germ of neighbourhoods $G$ with $G_0 \subseteq U$ and (1) $f = g$
on $O$ near $0$; (2) a point $y \in U$ near $0$ with $g(y) = \rho(r(y))g(y)$ lies in $O$; (3)
$y \mapsto [1 - \rho(r(y))]g(y)$ is an sc¹-germ on $G$ with a derivative family $Dk$, and $Dk(0)$
restricts to a topological linear isomorphism $\ker Dr(0) \to \ker\rho(0)$. ($\rho(u)$ is a bounded
operator, $\rho(x)$ a projection for $x \in O$.) *Book:* Definition 3.4, p. 64. *Hidden hypotheses:*
the map in (3) is differentiable at $0$ (true for every sc-smooth germ $g$, and $Dk(0)$ is unique).
*Deviation (hypotheses explicit):* stated for the principal parts; tameness unused. Since the switch
of Definition 3.11 to the text's germ reading (phase 2) $g$ and the map in (3) are germs whose levels
may shrink with $m$; the stricter whole-chart filler (`Polyfold.IsFillerOf`, the map in (3) sc¹ on
all of $U$, the sc-smoothness of $g$ on $U$ added in Definition 3.6) is kept for the whole-chart
notions (Findings, Chapter 3, items 220–221, 261, 330). Formerly "narrower", for the whole-chart
reading.

**V3.8 (Proposition 3.5 and the matrix of $Dg(0)$; `Polyfold.IsFillerOf.proposition_3_5`,
`Polyfold.proposition_3_5`, `Polyfold.fillerRestrict`, `Polyfold.fillerRestrict_kerEquiv`,
`Polyfold.fillerRestrict_cokerEquiv`, `Polyfold.StrongRetr.scDeriv_fiber_zero`,
`Polyfold.IsFillerOf.deriv_comp_r_eq_zero`, `Polyfold.IsFillerOf.scDeriv_section_comp_r`,
`Polyfold.IsScFredholm.restrict`, `Polyfold.IsFillerOf.proposition_3_5_sc`,
`Polyfold.IsFillerOf.filler_condition_three_sc`, `Polyfold.IsFillerOf.proposition_3_5_sc_converse`,
`Polyfold.IsFillerOf.proposition_3_5_sc_iff`).** Let $g$ be sc-smooth on $U$ and fill the section
$f$ of $K \to O$, with $g(0) = 0$. Then $D(\rho(r(\cdot))g)(0) = \rho(0)Dg(0)$,
$(1 - \rho(0))Dg(0)Dr(0) = 0$, $D(f \circ r)(0) = Dg(0)Dr(0)$; and $Tf(0) := Dg(0)$ restricted to
$Dr(0)E \to \rho(0)F$ is surjective iff $Dg(0)$ is, Fredholm iff $Dg(0)$ is, and has the same index
($\dim\ker - \dim\mathrm{coker}$). The linear algebra holds for any idempotents $p$, $q$ and $L$
with $(1 - q)Lp = 0$ and $(1 - q)L : \ker p \to \ker q$ a topological isomorphism. In sc form: if
$Dg(0)$ is an sc-Fredholm sc-operator, then $Dr(0)E$, $\rho(0)F$, $\ker Dr(0)$ and $\ker\rho(0)$ are
sc-subspaces, $Tf(0) : Dr(0)E \to \rho(0)F$ is sc-Fredholm with the index of $Dg(0)$ on every level,
and $(1 - \rho(0))Dg(0) : \ker Dr(0) \to \ker\rho(0)$ is an sc-isomorphism (condition (3) on every
level); for $Dg(0)$ an sc-operator, $Dg(0)$ is sc-Fredholm iff $Tf(0)$ is sc-Fredholm and condition
(3) holds on every level. *Book:* the paragraph after Definition 3.4 and Proposition 3.5, pp. 64–65.
*Hidden hypotheses:* $(u, h) \mapsto \rho(u)h$ differentiable at $(0, 0)$; $g(0) = 0$. *Deviation
(stronger):* the index equality without any finiteness assumption, via isomorphisms of kernels and
cokernels instead of the text's factorization. The text's target "$(1 - D\rho(0))F$" is
$(1 - \rho(0))F$. The sc form needs condition (3) only on level $0$, as the text states it (the
higher levels of $Tf(0)$ come from the regularity of $Dg(0)$); its converse needs condition (3) on
every level and fails with level $0$ alone (an example with the shift on a weighted $\ell^2$, not
formalized; Findings, Chapter 3, items 234, 237, 238). The same holds for a filling germ (V3.7), with
$Dg(0)$ the value at $0$ of any derivative family of $g$ (`Polyfold.IsFillingGerm.proposition_3_5`,
`Polyfold.IsFillingGerm.proposition_3_5_sc`, `Polyfold.IsFillingGerm.proposition_3_5_sc_iff`; Findings,
Chapter 3, items 272, 289, 314).

**V3.9 (Definition 3.6, filled versions; `Polyfold.IsFillingGerm`, `Polyfold.IsFilledVersion`,
`Polyfold.IsFilledVersion.isFillingGerm`, `Polyfold.IsFillingGerm.isFilledVersion`).** A filling of the
principal part $\mathbf f$ (V3.7) is an sc-smooth germ $g$ on an sc-germ of neighbourhoods inside $U$,
whose levels may shrink with $m$, filling $\mathbf f$ near $0$; the centred chart is that of Definition
3.11 (V3.13). *Book:* Definition 3.6, p. 66. *Hidden hypotheses:* none. *Deviation (restated):* the
datum in a given chart, for the principal parts; the chart is quantified in Definition 3.11. The
project's earlier filled version (`Polyfold.IsFilledVersion`), $g$ sc-smooth on all of $U$, is
stricter for germs whose levels shrink with $m$ (round-trip items V3.9, V3.43); it is exactly a
filling sc-smooth on all of $U$ (`IsFilledVersion.isFillingGerm`, `IsFillingGerm.isFilledVersion`;
Findings, Chapter 3, items 220–221, 260–262, 330). Formerly "narrower", for the whole-chart
reading.

**V3.10 (Definition 3.7, basic germs; `Polyfold.IsBasicGerm`, `Polyfold.IsSc0ContractionGerm`).** For a
finite-dimensional $P$, a set $\widetilde C \subseteq P$, a finite-dimensional $Q$ and a germ $G$ around $0$ in
$\widetilde C \oplus W$: $f$ is a basic germ with contraction map $B$ if $f$ is an sc-smooth germ on $G$ with
$f(0) = 0$, the $W$-component of $f(a, w)$ is $w - B(a, w)$ on $U_0$, and $B$ is an sc⁰-contraction germ
(V3.25). *Book:* Definition 3.7, p. 66 (Remark 3.8: historical). *Hidden hypotheses:* the points of the
contraction estimate lie in $U_m$. *Deviation (restated):* $\mathbb R^n$, $\mathbb R^N$ replaced by
finite-dimensional spaces.

**V3.11 (Lemma 3.9; `Polyfold.ContractionGerm.norm_levelDeriv_snd_le`,
`Polyfold.IsSc0ContractionGerm.deriv_zero_snd`,
`Polyfold.IsSc0ContractionGerm.exists_norm_deriv_snd_le`,
`Polyfold.IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le`).** For an sc⁰-contraction germ $B$
that is an sc¹-germ: (a) in the working form, $\|D_2B(a, w)\|_{L(W_m)} \le \tfrac12$ at points
$(a, w) \in U_{m+1}$ with $a \in N(m+1) \cap \widetilde C$, $w \in O(m+1)$, $\iota w \in O(m)$; (b)
$D_2B(0, 0) = 0$; (c) for every $\varepsilon > 0$ there is $r > 0$ with
$|D_2B(x)\zeta|_0 \le \varepsilon|\zeta|_0$ for $x \in U_1$, $|x|_1 < r$, $\zeta \in W_0$; (d) as
stated, for $\widetilde C$ quadrant-like: for every $\varepsilon > 0$ and $m$ there is $r > 0$ with
$|D_2B(x)\zeta|_m \le \varepsilon|\zeta|_m$ for $\zeta \in W_m$ at every $x \in U_{m+1}$ with
$|x|_m < r$. *Book:* Lemma 3.9, p. 67 (every $\varepsilon$, every level, $(a, w) \in E_{m+1}$ small
in $E_m$; $B$ sc-smooth). *Hidden hypotheses:* differentiability of $B : U_{m+1} \to W_m$
(Proposition 1.16 for germs, V3.4). *Deviation (stronger):* sc¹ suffices, and the general statement
is proved as stated (d); smallness on level $m + 1$ is not needed, since the contraction estimate of
Definition 3.28 is applied at points small on level $0$ (Findings, Chapter 3, item 215). Formerly
"narrower", when only (a)–(c) were proved.

**V3.12 (Proposition 3.10; `Polyfold.proposition_3_10`, `Polyfold.proposition_3_10_scPlus`,
`Polyfold.IsSc1GermWith.isScOperator_deriv_zero`, `Polyfold.ScBanach.scIndex_projWOp`,
`Polyfold.StabilityData.exists_isFredholm_Dfs'`, `Polyfold.proposition_3_10_level`,
`Polyfold.proposition_3_10_full`, `Polyfold.IsBasicGerm.levelDeriv_add_eq`,
`Polyfold.IsBasicGerm.snd_levelDeriv_add`).** Let $\widetilde C$ be a partial quadrant, $h$ a basic
germ, $s$ an sc¹-germ into $(Q \oplus W)^1$ and $f = h + \iota s$ an sc¹-germ with derivative family
$Df$. Then $Df(0)$ is an sc-operator, sc-Fredholm of index $\dim P - \dim Q$: it is $T_0 + S$ with
$T_0(\delta a, \delta w) = (0, \delta w)$ and $S$ an sc⁺-operator. For the data of Theorem 3.38,
$D(h + s)(x) : E_0 \to F_0$ is Fredholm of index $\dim P - \dim Q$ for every $x \in U_1$ small on
level $1$. On every level (the second statement): for every $m$ there is $\delta > 0$ such that at
every $x \in U_{m+1}$ with $|x|_m < \delta$ the level-$m$ operator
$Df(x)_m : P \oplus W_m \to Q \oplus W_m$ is Fredholm of index $\dim P - \dim Q$ ($\widetilde C$
quadrant-like); $f(0) = 0$ is not used. *Book:* Proposition 3.10, p. 68. *Hidden hypotheses:* the
finite-rank terms are sc⁺ because $Dh(0)$ is an sc-operator at the smooth point $0$. *Deviation
(stronger):* both statements as in the text, with $s$ and $f$ only sc¹ and $f(0) = 0$ unused. The
second statement by the text's proof on level $m$: $Df(x)_m = T_0 + S(x) + K(x)$ with
$\|S(x)\| \le \varepsilon$ by Lemma 3.9 on level $m$ (V3.11) and $K(x)$ compact; the $W$-component
of $Df(x)_m$, which the text uses silently, follows from the uniqueness of derivatives within $U_1$
(Findings, Chapter 3, item 230). Formerly "narrower", the second statement on level $0$ only.

**V3.13 (Definition 3.11, sc-Fredholm germs; `Polyfold.StrongBundle.IsScFredholmGerm`,
`Polyfold.IsFillingGerm`, `Polyfold.IsScPlusGerm`, `Polyfold.IsConjugateToBasicGerm`,
`Polyfold.IsStrongBundleIso`, `Polyfold.StrongBundle.IsScFredholmGermWholeChart`,
`Polyfold.StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm`,
`Polyfold.StrongBundle.isScFredholmGerm_iff_germG_wholeChart`).** $(f, x_0)$ is an sc-Fredholm
germ if $x_0$ is smooth and in a strong bundle chart of $P$ centred at $x_0$ the principal part has
a filling $g$ (V3.9: an sc-smooth germ on a germ of neighbourhoods inside $U$), there is an
sc⁺-germ $s$ (`IsScPlusGerm`: $s : E_0 \to F_1$ an sc-smooth germ into $F^1$ on a germ inside $U$)
with $\iota s(0) = g(0)$, and $k = g - \iota s$ is conjugated to a basic germ: strong bundle maps
$\Psi : U \triangleleft F \to U' \triangleleft F'$ and $\Psi'$ back, inverse to each other, with
base map $\psi$, $\psi(0) = 0$, $U'$ relatively open in $\widetilde C \oplus W$ ($\widetilde C$ a
partial quadrant of a finite-dimensional space), a basic germ $h$ on a germ inside $U'$, and
$(\Psi(u, k(u)))_2 = h(\psi(u))$ for $u \in U$ near $0$. *Book:* Definition 3.11, p. 69. *Hidden
hypotheses:* none. *Deviation (restated):* the identity is required for $u \in U$; tameness unused;
$C' = T\psi(0)C$ not imposed (it is proved, V3.48). The witnesses of the conjugation are also
available as data (`Polyfold.ConjugationData`, V3.46). Since the switch to the text's germ reading
(phase 2) the filling and the sc⁺-section are germs whose levels may shrink with $m$; $\Psi$ on all
of $U$ is no restriction (on a relatively open $U_0 \subseteq U$ it is the same after restricting
the chart on level $0$). The project's earlier notion, with $g$, $s$ sc-smooth on the whole $U$
(`IsScFredholmGermWholeChart`), implies this one and is exactly this one with $g$, $s$ sc-smooth on
$U$; whether the two agree for sections sc-smooth on $X$ is open, and no theorem depends on it
(Findings, Chapter 3, items 220–221, 261–264, 330). The existential over charts is essential: a
filling in a chart gives a topological isomorphism $\ker Dr(0) \cong \ker\rho(0)$, a condition on
the chart (`Polyfold.IsFillingGerm.nonempty_kerEquiv`), so a filling in one chart gives none in
another unless these normal spaces match; a compatible tame chart of the trivial bundle carries no
filling of any section (`Polyfold.TrivialBundle.not_isFillingGerm_evenBundleChart`; Findings,
Chapter 3, items 350–352).

**V3.14 (Theorem 3.12; `Polyfold.theorem_3_12`, `Polyfold.theorem_3_12_local_subset`,
`Polyfold.MPolyfold.continuousOn_levelChartSymm`).** Let $f$ be a section of a strong bundle $P : Y \to X$
($P \circ f = \mathrm{id}$) with $(f, x_0)$ an sc-Fredholm germ and $f(x_0) = 0$. There are open sets $O(0)
\supseteq O(1) \supseteq \cdots$ of $X$ containing $x_0$ such that for every $i$ the closure in $X$ of $\{x \in O(i)
\mid f(x) = 0\}$ is the image of a compact subset of $X_i$, with the level topology, under the inclusion
$X_i \to X$. *Book:* Theorem 3.12, p. 70 (sc-smooth section of a tame strong bundle). *Hidden
hypotheses:* none beyond those used. *Deviation (stronger):* only $P \circ f = \mathrm{id}$ of the section
is used; no tameness. *Proof:* the local form (Theorem 3.40 for any subset of the solution set),
transported through chart, filler and conjugation, with the inverse chart $O_i \to X_i$ continuous for
the level topology.

**V3.15 (Corollary 3.13; `Polyfold.corollary_3_13`, `Polyfold.corollary_3_13_section`,
`Polyfold.tendsto_of_isCompact_of_tendsto_map`).** (a) Under the hypotheses of V3.14, if $f(x_k) = 0$ and
$x_k \to x_0$ in $X$, then for every $m$ there are $y_k \in X_m$ with $\iota y_k = x_k$ for $k$ large and $y_k
\to y_0$ in $X_m$, $\iota y_0 = x_0$. (b) If $f$ is an sc-Fredholm section and $x_k \to x$ are zeros, then $x$ is
a zero and a smooth point, and the same holds at $x$. *Book:* Corollary 3.13, p. 70. *Hidden
hypotheses:* the germ property at the limit. *Deviation (restated):* the text's arbitrary limit $x$ is
covered for $x = x_0$ and, for sc-Fredholm sections, for every $x$.

**V3.16 (Definition 3.14, sc-Fredholm sections; `Polyfold.StrongBundle.IsScFredholmSection`,
`Polyfold.StrongBundle.IsScFredholmSectionWholeChart`,
`Polyfold.StrongBundle.IsScFredholmSectionWholeChart.isScFredholmSection`).** $f$ is an sc-Fredholm
section of the strong bundle $P$ if it is sc-smooth, regularizing ($x \in X_m$, $f(x) \in Y_{m,m+1}$
imply $x \in X_{m+1}$) and an sc-Fredholm germ (V3.13) at every smooth point. *Book:* Definition 3.14,
p. 70. *Hidden hypotheses:* none. *Deviation:* none; the bundle need not be tame. Clause (3) is the
text's germ reading since phase 2; the project's earlier whole-chart notion
(`IsScFredholmSectionWholeChart`), stricter, implies it (Findings, Chapter 3, items 220–221, 330).
Formerly "restated", for the whole-chart reading.

**V3.17 (Theorem 3.15; `Polyfold.theorem_3_15`, `Polyfold.StrongBundle.IsScSmoothSection.sectionAdd`,
`Polyfold.StrongBundle.regularizing_sectionAdd`, `Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd`).** If
$f$ is an sc-Fredholm section and $s$ an sc⁺-section of a strong bundle, the fibrewise sum $f + s$ is an
sc-Fredholm section. *Book:* Theorem 3.15, p. 71 (tame bundle). *Hidden hypotheses:* the sum rule; the
[1]-compatibility of charts (V3.6). *Deviation (stronger):* no tameness. In the germ reading of
Definition 3.11 (V3.13), with the text's proof: $\tilde t = \hat s \circ r$ is sc-smooth on the whole
$U$, and a germ plus a whole-chart map is a germ on the same germ (V3.19; Findings, Chapter 3, item
300); the whole-chart form is `Polyfold.theorem_3_15_wholeChart`.

**V3.18 (Lemma 3.16; `Polyfold.lemma_3_16`).** For a section $s$ of $K \to O$: $s(r(x)) = s(x)$ for $x \in O$, and
$\rho(r(u))s(r(u)) = s(r(u))$, $R(r(u), s(r(u))) = (r(u), s(r(u)))$ for $u \in U$. *Book:* Lemma 3.16, p. 72.
*Hidden hypotheses:* $s$ takes values in $K$. *Deviation (restated):* the sc⁺-regularity of $s \circ r$ is
proved inside Theorem 3.15 (V3.17).

**V3.19 (Lemma 3.17; `Polyfold.IsFillingGerm.add_section_germ`, `Polyfold.IsFillingGerm.add_section`,
`Polyfold.lemma_3_17`).** If $g$ is a filling of $\mathbf f$ (V3.7) and $s$ a section of $K \to O$, then
$g + s \circ r$ is a filling of $\mathbf f + s$, with the same derivative family in (3): for $s$
sc-smooth on $U$, on the same germ; for $s$ an sc-smooth germ on $G_s$, on $G \cap r^{-1}(G_s)$.
*Book:* Lemma 3.17, p. 72. *Hidden hypotheses:* none. *Deviation (stronger):* the regularity of
$g + s \circ r$ is part of the conclusion, and of $s$ only the sc-smoothness is used, not that it is
sc⁺. This is the text's statement for fillings that are germs, proved in the project since the switch
to the germ reading (phase 2); the whole-chart `Polyfold.lemma_3_17` (fillers in the sense of
`IsFillerOf`, any section $s$, the regularity left to Theorem 3.15) neither implies it nor follows from
it (round-trip item V3.19; Findings, Chapter 3, items 220–221, 273). Formerly "restated".

**V3.20 (Definition 3.21, good position; `Polyfold.IsGoodComplement`, `Polyfold.IsInGoodPosition`,
`Polyfold.IsScGoodComplement`, `Polyfold.IsInGoodPositionSc`,
`Polyfold.IsInGoodPosition.isInGoodPositionSc`, `Polyfold.isScGoodComplement_iff`,
`Polyfold.isInGoodPositionSc_iff`).** A subspace $P$ is a good complement of $N$ with respect to $C$
if $E_0 = N \oplus P$ (algebraically) and for some $\varepsilon > 0$, $n \in N$, $p \in P$,
$|p|_0 \le \varepsilon|n|_0$ imply ($n \in C \iff n + p \in C$). $N$ is in good position to $C$ if
$N \cap C$ has nonempty interior in $N$ and $N$ has a good complement. Definition 3.21 as written
(`IsScGoodComplement`: $E = N \oplus P$ an sc-splitting with the constant $\varepsilon$;
`IsInGoodPositionSc`) implies this; on a partial quadrant a smooth finite-dimensional $N$ in good
position is in good position with an sc-complement, also inside any sc-subspace $T \supseteq N$, and
for smooth $N$ the text's good complements are the project's closed ones. *Book:* Definition 3.21,
pp. 76–77 (an sc-complement, or a topological one). *Hidden hypotheses:* none. *Deviation
(stronger):* only the algebraic splitting is required, as a hypothesis. As a conclusion the
algebraic form is weaker (an algebraic good complement need not be closed, round-trip item V3.20),
so the text's form is formalized as well and proved where the theorems conclude good position
(V3.47, V3.94; Findings, Chapter 3, items 210, 211).

**V3.21 (Proposition 3.22; `Polyfold.proposition_3_22`, `Polyfold.exists_quadrantNormalForm`).** If the
finite-dimensional subspace $N$ is in good position to the partial quadrant $C$, then $N \cap C$ is a
partial quadrant in $N$. More precisely, for $C = \{\ell_i \ge 0\}$ with continuous functionals jointly onto
$\mathbb R^n$, there is a linear isomorphism $e : N \to \mathbb R^k \times N_0$ carrying $N \cap C$ onto $[0,
\infty)^k \times N_0$, with $k = \dim N - \dim(N \cap W)$ and the degeneracy counts preserved off $N \cap W$.
*Book:* Proposition 3.22, p. 77, proof pp. 120–126. *Hidden hypotheses:* none. *Deviation:* none in the
statement. *Proof:* a segment argument and Lemma 3.65 instead of the extreme-ray Lemmas 3.62–3.64,
3.66–3.68.

**V3.22 (Definition 3.25, the tangent germ property; `Polyfold.MPolyfold.TangentGermChart`,
`Polyfold.MPolyfold.HasTangentGermProperty`, `Polyfold.IsScInftyGermAt`).** $M \subseteq X$ has the
$n$-dimensional tangent germ property if $M \subseteq X_\infty$ and every $x \in M$ has: a chart
$\varphi : (U, x) \to (O, 0)$ of $X$ onto a tame retract $(O, C, E)$; an $n$-dimensional smooth
$N \subseteq E$ in good position to $C$ with a good complement $Y$ that is **closed**; a relatively
open $V \ni 0$ in $N \cap C$; and a continuous $\delta : V \to E$ with values in $Y$, such that
$\varphi(M \cap U) = \{v + \delta(v) \mid v \in V\}$, $\delta(0) = 0$, $D\delta(0) = 0$, and for
every $m$, $k$ there is a relatively open $V_{m,k} \ni 0$ in $N \cap C$ with
$\delta(V_{m,k}) \subseteq E_m$ and $\delta : V_{m,k} \to E_m$ of class $C^k$. *Book:* Definition
3.25, p. 79. *Hidden hypotheses:* $Y$ closed (the text's sc-complement is). *Deviation (narrower):*
the added closedness; "sc^∞-germ" read with $k$-dependent neighbourhoods, which the fixed-germ and
the set-sense readings imply (`Polyfold.IsScSmoothGerm.isScInftyGermAt`,
`Polyfold.IsScSmooth.isScInftyGermAt`). The germ implicit function theorem gives the fixed-germ
reading as well (V3.31, V3.32); Theorem 3.43 (1) is proved in the $k$-dependent one (V3.38).

**V3.23 (Proposition 3.26; `Polyfold.proposition_3_26`, `Polyfold.proposition_3_26_image`,
`Polyfold.MPolyfold.TangentGermChart.transport`).** Let $\psi : X \to X'$ be an sc-diffeomorphism of
M-polyfolds (sc-smooth on all of $X$, with an sc-smooth inverse $\psi'$ on all of $X'$) and $\psi(M) =
M'$. Then $M'$ has the $n$-dimensional tangent germ property (V3.22) if and only if $M$ has it; the data
at $\psi(x)$ are the chart $\varphi \circ \psi^{-1}$ with the same $N$, $Y$, $V$, $\delta$. *Book:*
Proposition 3.26, p. 80. *Hidden hypotheses:* none. *Deviation:* none (the tameness of $X$ is not used).
The text's "$X' = \psi(X)$ is tame" is not needed here; that tameness is carried by sc-diffeomorphisms
is V3.71.

**V3.24 (Theorem 3.27; `Polyfold.theorem_3_27`, `Polyfold.theorem_3_27_isSubMPolyfold`,
`Polyfold.MPolyfold.TangentGermChart.IsRegular`, `Polyfold.MPolyfold.theorem_3_27_isChart`,
`Polyfold.MPolyfold.theorem_3_27_isTame`, `Polyfold.MPolyfold.theorem_3_27_isManifoldWithCorners`,
`Polyfold.MPolyfold.theorem_3_27_degIndex`).** Let $M \ne \emptyset$ be a subset of an M-polyfold $X$
such that every point of $M$ has data of Definition 3.25 (V3.22) that are *regular*: (a) $\delta$ is
sc-smooth on $V$ as a map on a set, and (b) the projection $\pi$ along $Y$ maps $O$ into $C$. Then $M$
is a sub-M-polyfold of $X$; its induced M-polyfold structure (Proposition 2.21) is tame and has an
equivalent atlas of charts on relatively open subsets of $n$-dimensional partial quadrants; each map $y
\mapsto \pi\varphi(y)$ on $M \cap \varphi^{-1}(\Sigma \cap O)$, modelled on $(V, N \cap C, N)$, is a
chart of the induced structure containing $x$; and $d_M(y) = d_{N \cap C}(\pi\varphi(y))$ there. *Book:*
Theorem 3.27, p. 81, proof pp. 81–84. *Hidden hypotheses:* (a) and (b); the text's proof asserts both
and each fails in an example (a smooth curve with a vertical tangent written over the horizontal axis;
$C = [0, \infty)^3$, $N = \mathbb R(1, 1, 1)$, $Y = \{x + y - z = 0\}$). *Deviation (narrower):* the two
added conditions; $X$ need not be tame; the relation $d_{N \cap C} = d_X$ via Lemma 3.70 is not
transported to a general presentation of $C$. For the solution set of an sc-Fredholm section both
conditions are theorems (V3.74, V3.77, V3.85); for any set with the tangent germ property, (a) follows
from (b) after shrinking the data (V3.74). With a dimension that may vary from point to point: V3.72.

**V3.25 (Definition 3.28, sc⁰-contraction germs; `Polyfold.IsSc0ContractionGerm`, `Polyfold.ContractionGerm`,
`Polyfold.IsSc0ContractionGerm.toContractionGerm`).** For a germ $G$ around $0$ in $\widetilde C \oplus W$: $B$ is
an sc⁰-contraction germ if $B$ is an sc⁰-germ, $B(0, 0) = 0$, and for every $\varepsilon > 0$ and $m$ there is
$r > 0$ such that the points $(a, w)$ with $a \in \widetilde C$, $|a| < r$, $|w|_m < r$ lie in $U_m$ and $|B(a, w) -
B(a, w')|_m \le \varepsilon|w - w'|_m$ for such $(a, w)$, $(a, w')$. Every such $B$ has a working form: open
$N(0) \supseteq N(1) \supseteq \cdots \ni 0$ in $P$ and $0 \in K(m) \subseteq O(m) \subseteq W_m$ ($K$ closed, $O$ open, $\iota
K(m+1) \subseteq K(m)$) with $\{a\} \times O(m) \subseteq U_m$, $B_m(a, \cdot)$ a $\tfrac12$-contraction on $O(m)$ mapping
$K(m)$ into itself, for $a \in N(m) \cap \widetilde C$. *Book:* Definition 3.28, p. 85. *Hidden hypotheses:* the
points lie in $U_m$. *Deviation (restated):* explicit regions, needed for Lemma 3.31.

**V3.26 (Theorem 3.29; `Polyfold.theorem_3_29`, `Polyfold.theorem_3_29_of_isSc0ContractionGerm`,
`Polyfold.exists_fixedPoint_continuousOn`).** For a contraction germ in working form with quadrant-like
$\widetilde C$: the level-$0$ fixed point $\delta(a)$ of $B(a, \cdot)$ is an sc⁰-germ on $V_m = N(m) \cap \widetilde C$
with $\delta(0) = 0$, $(a, \delta_m(a)) \in U_m$ for $a \in V_m$, $B(a, \delta(a)) = \delta(a)$ on $V_0$, and every
$w \in O(0)$ with $B(a, w) = w$, $a \in V_0$, equals $\delta(a)$. From Definition 3.28 directly: the same, with
uniqueness among small solutions. The parametrized Banach fixed point theorem: for $\tfrac12$-contractions
$g_l$ of a nonempty closed $K$ in a complete metric space, continuous in $l$ pointwise, the fixed point is
continuous in $l$ and unique in $K$. *Book:* Theorem 3.29, p. 86. *Hidden hypotheses:* the uniqueness
region. *Deviation (hypotheses explicit).*

**V3.27 (Theorem 3.30; `Polyfold.theorem_3_30`, `Polyfold.ContractionGerm.isSc1GermWith_sol`).** If $B$ is an
sc¹-germ, the solution germ $\delta$ is a solution germ and an sc¹-germ on $V_m = N(m+1) \cap \widetilde C$ (the
germ shifted by one level), with $D\delta(a) = (1 - D_2B(a, \delta(a)))^{-1}D_1B(a, \delta(a))$. *Book:* Theorem
3.30, p. 86, quoted from [21] without proof. *Hidden hypotheses:* none. *Deviation (restated):* sc¹ on
the shifted germ; a germ only because $\widetilde C$ is finite-dimensional. *Proof:* supplied; it needs
$(a_0, \delta(a_0)) \in U_2$, hence the shift.

**V3.28 (Lemma 3.31; `Polyfold.ContractionGerm.lemma_3_31`, `Polyfold.ContractionGerm.next`,
`Polyfold.ContractionGerm.isSc0ContractionGerm_next`).** If $B$ is sc^{k+1} with derivative family
$D$ and $\delta$ is sc^j on $(N(m+s) \cap \widetilde C)_m$, then
$f^{(1)}(v, b, u, w) = (u - B(v, u), w - DB(v, \delta(v))(b, w))$, in working form with parameter
set $\widetilde C \times P$, fibre $TW$ and regions $N(m+2+s) \times P$, $O(m+1) \times W_m$,
$K(m+1) \times W_m$, is a contraction germ of class sc^{min(k, j)} whose solution germ is
$(v, b) \mapsto (\delta(v), D\delta(v)b)$ on $(N(2+s) \cap \widetilde C) \times P$. If the working
form also satisfies Definition 3.28 and $B$ is sc¹, then $f^{(1)}$ satisfies Definition 3.28 on its
germ, for every $s$ (an $\varepsilon$-contraction near $0$ for every $\varepsilon > 0$ on every
level), by Lemma 3.9 on level $m$ (V3.11). *Book:* Lemma 3.31, pp. 86–87. *Hidden hypotheses:*
uniqueness of the fixed point only in a region unbounded in the tangent directions; the shifted
solution germ (Proposition 1.17 for germs). *Deviation (restated):* the working form records a
$\tfrac12$-contraction on explicit regions, all the proof of Theorem 3.33 uses; the text's
"$f^{(1)}$ is an sc⁰-contraction germ" in the sense of Definition 3.28 is proved separately
(Findings, Chapter 3, item 252).

**V3.29 (Lemma 3.32, as an induction; `Polyfold.ContractionGerm.sol_isSckGerm`,
`Polyfold.ContractionGerm.isSckGerm_succ_of_next`).** For every contraction germ over any finite-dimensional
parameter space: if $B$ is sc^k and $j \le k$, then $\delta$ is an sc^j-germ on $(N(m+s) \cap \widetilde C)_m$ for
some $s$; the step from $j$ to $j+1$ turns shifts $s$ (for $\delta$) and $s'$ (for $T\delta$) into $s + s' + 1$.
*Book:* Lemma 3.32, p. 87 (the iterated germs $f^{(j)}$ with solution $T^j\delta$). *Hidden hypotheses:*
none. *Deviation (restated):* the $f^{(j)}$ are not constructed; one induction quantified over all
contraction germs.

**V3.30 (Theorem 3.33, the germ implicit function theorem; `Polyfold.theorem_3_33`,
`Polyfold.theorem_3_33_smooth`, `Polyfold.theorem_3_33_of_isSc0ContractionGerm`).** If $B$ is an sc^k-germ, there
is $s$ such that the solution germ $\delta$ is a solution germ and an sc^k-germ on $(N(m+s) \cap \widetilde C)_m$;
the proof gives $s = 2^k - 1$. If $B$ is sc-smooth, this holds for every $k$ (with $s$ depending on $k$).
From Definition 3.28 with balls: there is an sc^k solution germ. *Book:* Theorem 3.33, p. 88. *Hidden
hypotheses:* **none; the theorem holds with the text's hypotheses**. *Deviation (restated):* the germ on
which $\delta$ is sc^k shrinks with $k$; in the text's up-to-shrinking reading this is the theorem.

**V3.31 (Corollary 3.34; `Polyfold.corollary_3_34`, `Polyfold.corollary_3_34_isScSmoothGerm`,
`Polyfold.isSckGerm_of_levels`).** If $B$ is an sc-smooth germ, then for all $m$, $k$ there is a
relatively open $V \ni 0$ in $\widetilde C$ with $\delta(V) \subseteq W_m$ and $\delta : V \to W_m$
of class $C^k$. The last sentence on one germ: $\delta$ is an sc-smooth germ (sc^k for every $k$ on
the same sequence of sets) on a diagonal germ $V_m = N(m + t_m) \cap \widetilde C$,
$t_m = \sum_{j \le m} s_j$, and a solution germ there. *Book:* Corollary 3.34, p. 88. *Hidden
hypotheses:* Proposition 1.18 for germs. *Deviation:* none; its last sentence ("$\delta$ is
sc-smooth at $0$") holds on one germ: sc^j involves only the levels $\ge j$ of a germ
(`Polyfold.isSckGerm_of_levels`), so the $k$-dependent germs of Theorem 3.33 can be replaced by one
diagonal germ, which shrinks fast with the level (Findings, Chapter 3, item 250).

**V3.32 (Theorem 3.35; `Polyfold.theorem_3_35`, `Polyfold.theorem_3_35_smooth`,
`Polyfold.theorem_3_35_isScSmoothGerm`, `Polyfold.theorem_3_35_of_isSc0ContractionGerm`,
`Polyfold.isSckGerm_contractionMap_iff`).** For $\widetilde C$ a partial quadrant in a
finite-dimensional $P$: if $B$ is sc^k, $\delta$ is sc^k on $(N(m+s) \cap \widetilde C)_m$ for some
$s$; if $B$ is sc-smooth, then for every $k$ there is such an $s$, and $\delta$ is an sc-smooth germ
on one germ $N(m + t_m) \cap \widetilde C$. In the text's form: for an sc⁰-contraction germ
$f = w - B(a, w)$ of Definition 3.28 on a quadrant-like $\widetilde C$ and any representative
$(V, \delta)$ of its solution germ, if $f$ is sc^k then $\delta$ is sc^k on a germ $V' \subseteq V$,
and if $f$ is sc-smooth then $\delta$ is an sc-smooth germ on one germ $V' \subseteq V$. *Book:*
Theorem 3.35, p. 89. *Hidden hypotheses:* none. *Deviation (restated):* the conclusion holds on a
smaller germ $V' \subseteq V$, as for Theorem 3.33 (V3.30); the hypotheses are on $f$ ($f$ is sc^k
iff $B$ is); $\mathbb R^n$ is generalized to a quadrant-like $\widetilde C$ in a finite-dimensional
$P$ (Findings, Chapter 3, items 250, 251). Before the third addendum "sc-smooth" held only for every
$k$ on a germ depending on $k$.

**V3.33 (Definition 3.37, the basic class; `Polyfold.IsBasicGerm`).** As V3.10. *Book:* Definition 3.37, p. 90.
*Hidden hypotheses:* none. *Deviation:* none.

**V3.34 (Theorem 3.38; `Polyfold.theorem_3_38`, `Polyfold.StabilityData`,
`Polyfold.StabilityData.exists_of_scPlus`, `Polyfold.StabilityData.pushMap`,
`Polyfold.StabilityData.pushB_isSc0ContractionGerm`, `Polyfold.scPlusRemainder_contraction`,
`Polyfold.StabilityData.pushMap_eq_zero_iff`, `Polyfold.StabilityData.finrank_Cs_eq_finrank_Zs`).** Let
$f$ be a basic germ on $G$ with contraction $B$, $s$ an sc-smooth germ into $W^1$ with $s(0) = 0$ (the
$W$-component of an sc⁺-germ), and $W = C \oplus X = R \oplus Z$ an sc-Fredholm splitting of $1 +
D_2s(0)$ (it exists, Proposition 1.10). With $P_1 : W \to X$, $P_2 : W \to R$ the projections and $L =
(1 + D_2s(0))|_X$, the linear maps $\psi(a, w) = ((a, (1 - P_1)w), P_1w)$ and $\Psi(q, w) = ((q, (1 -
P_2)w), L^{-1}P_2w)$ carry $f + \iota s$ to the germ $\Psi \circ (f + \iota s) \circ \psi^{-1}$ on the
index-raised spaces $(P \oplus C) \oplus X^1 \to (Q \oplus Z) \oplus X^1$, with germ $\psi(U_{m+1})$,
which is a basic germ with contraction map $L^{-1}P_2(B - S)$, $S = s - D_2s(0)$; its zeros correspond
to those of $f + \iota s$; and $\dim C = \dim Z$. *Book:* Theorem 3.38, pp. 90–93. *Hidden hypotheses:*
the operator-norm continuity of the level derivatives of $s$ (for "$S$ is an arbitrarily small
contraction"). *Deviation (restated):* a linear coordinate change; only the $W$-component of $s$; the
text's $\tau : Z \to C$ not applied. The coordinate change is a strong bundle isomorphism of the
index-raised structures (`Polyfold.StabilityData.linIso_isStrongBundleIso`, V3.76).

**V3.35 (Theorem 3.40; `Polyfold.theorem_3_40_compactness`, `Polyfold.theorem_3_40_regularity`,
`Polyfold.IsSc0ContractionGerm.exists_lift`, `Polyfold.theorem_3_12_local`).** Let $B$ be an sc⁰-contraction germ
on $G$ around $0$ in $\widetilde C \oplus W$ with $\widetilde C$ **closed**, $\mathbf s$ an sc⁰-germ into $W^1$ with
$\mathbf s(0) = 0$, and $S$ any set of solutions in $U_0$ of $w = B(a, w) - \iota\mathbf s(a, w)$. There are open
$O(0) \supseteq O(1) \supseteq \cdots \ni 0$ in $E_0$ and compact $K_i \subseteq E_i$ with $\mathrm{cl}_{E_0}(S \cap O(i)) = \iota_i(K_i)$;
in particular these closures lie in $E_i$. For a basic germ $h$ and an sc⁰-germ $s$ into $(Q \oplus W)^1$ with
$s(0) = 0$, the closures of $\{h + \iota s = 0\} \cap O(i)$ are compact subsets of $E_i$. *Book:* Theorem 3.40,
p. 94, proof pp. 95–98. *Hidden hypotheses:* $\widetilde C$ closed (automatic for a partial quadrant).
*Deviation (stronger):* compact closures; $B$ only sc⁰ with the contraction estimate, $\mathbf s$ only sc⁰
into $W^1$.

**V3.36 (Corollary 3.41; `Polyfold.StabilityData.corollary_3_41`, `Polyfold.StabilityData.exists_isFredholm_Dfs'`,
`Polyfold.StabilityData.exists_ker_Dfs'_inf_eq_bot`, `Polyfold.isFredholm_add_of_norm_lt`,
`Polyfold.HasFiniteIndex.surjective_of_finrank_ker_le`).** For the data of V3.34 with $D(f + \iota s)(0)$
surjective: there is $r > 0$ such that every zero $x$ of $f + \iota s$ in $U_0$ with $|x|_0 < r$ is $\iota(x_1)$ for some
$x_1 \in U_1$, and $D(f + \iota s)(x_1) : E_0 \to F_0$ is a surjective Fredholm operator of index $\dim P - \dim Q$.
*Book:* Corollary 3.41, p. 98. *Hidden hypotheses:* none. *Deviation (restated):* the $\mathbb R^N$-component
of the sc⁺-map is absorbed into the basic germ. *Proof:* the Fredholm property holds at every $x \in U_1$
small on level $1$ (small plus compact perturbation of $D(f + \iota s)(0)$); surjectivity from $\dim\ker \le
\mathrm{ind}$.

**V3.37 (Lemma 3.42; `Polyfold.StabilityData.lemma_3_42`).** For the push-forward $g = \Phi_*(f + \iota s)$ of
V3.34 (on level $0$): for every $\varepsilon > 0$ there is $r > 0$ such that every zero $x'$ of $g$ in $\psi(U_0)$ with
$|x'|_0 < r$ has its $X$-component $\iota(w_1)$ with $w_1 \in X_1$, $|w_1|_1 < \varepsilon$. *Book:* Lemma 3.42, p.
101. *Hidden hypotheses:* none. *Deviation (restated):* the form Theorem 3.43 uses; $w' = \delta(a')$ is
derived there.

**V3.38 (Theorem 3.43; `Polyfold.theorem_3_43_sc_smooth`, `Polyfold.theorem_3_43`,
`Polyfold.ShiftedBasicData`, `Polyfold.ShiftedBasicData.Sol.exists_contDiffOn_level`,
`Polyfold.exists_proj_mem_of_eq_zero`).** Let $\widetilde C$ be a partial quadrant, $g$ an sc-smooth
germ on $G$ with $g(0) = 0$ whose index-raised germ is a basic germ, with $Dg(0)$ surjective, $K' = \ker
Dg(0)$ in good position to $\widetilde C \oplus W$, and such that for every $\varepsilon > 0$ there is
$r > 0$ with every zero $x$ of $g$ in $U_0$, $|x|_0 < r$, having $W$-component $\iota(w_1)$, $|w_1|_1 <
\varepsilon$. Then there are a good complement $Y$ of $K'$, a relatively open $V \ni 0$ in $K' \cap
(\widetilde C \oplus W)$ and $\tau : K' \to P \times W_0$ with values in $Y$ and $W$-components on level
$1$, $C^1$ on $V$, $\tau(0) = 0$, $D\tau(0) = 0$, such that $y + \tau(y) \in U_0$ and $g(y + \tau(y)) =
0$ for $y \in V$; for every $k \ge 1$ a relatively open $V_k \subseteq V$ containing $0$ and a $C^k$ map
$\tau_k : V_k \to E_k$ with $\iota_k\tau_k = \tau$ on $V_k$; and an open $U'' \ni 0$ in which every zero
of $g$ in $U_0$ is $y + \tau(y)$ with $y \in V$. *Book:* Theorem 3.43, p. 102. *Hidden hypotheses:* the
regularity of Lemma 3.42 (made a hypothesis); the projection of a solution to $\widetilde K$ lies in
$\widetilde C$ (a gap in the text, proved); that the solutions given by Theorem 3.78 at the different
regularities $k$ coincide near $0$ (uniqueness clause). *Deviation (restated):* clause (1), "$\tau$ is
an sc-smooth germ", in the level-wise sense with $k$-dependent neighbourhoods. With $Y$ closed and its
projection onto $K'$ mapping $\widetilde C \oplus W$ into itself: V3.77.

**V3.39 (Lemma 3.44; `Polyfold.ShiftedBasicData.Deriv.ker_Dg_eq`).** In the setting of V3.38, $\ker Dg(0) =
\{(\alpha, D\delta(0)\alpha) \mid \alpha \in \ker DH(0)\}$, $H(a) = \mathrm{pr}_Q\,g(a, \delta(a))$. *Book:* Lemma 3.44, p.
103. *Hidden hypotheses:* $D_2B(0) = 0$ on level $0$, by density from level $1$. *Deviation:* none.

**V3.40 (Lemma 3.45; `Polyfold.IsGoodComplement.map`, `Polyfold.IsInGoodPosition.map`).** A continuous linear
isomorphism $S : E_0 \to E'_0$ with $x \in C \iff Sx \in C'$ carries a good complement $P$ of $N$ to a good complement
$S(P)$ of $S(N)$ (constant $\varepsilon/(\|S\|\|S^{-1}\| + 1)$), and good position to good position. *Book:* Lemma
3.45, p. 104 (for $T\varphi(0)$). *Hidden hypotheses:* none. *Deviation (stronger):* any such $S$.

**V3.41 (Lemma 3.46; `Polyfold.lemma_3_46`, `Polyfold.lemma_3_46_isInGoodPosition`).** If $K' = \{(\alpha, L\alpha) \mid
\alpha \in \widetilde K\}$ has a good complement with respect to $\widetilde C \oplus W$, then $\widetilde K$ has a good
complement $Z$ with respect to $\widetilde C$ such that $Z \times W$ is a good complement of $K'$; good position of
$K'$ gives good position of $\widetilde K$. *Book:* Lemma 3.46, p. 104, proof pp. 129–132. *Hidden
hypotheses:* none. *Deviation:* none (the proof avoids the intermediate complement $Y_0$).

**V3.42 (Corollary 3.47; `Polyfold.theorem_3_47_sc_smooth`, `Polyfold.theorem_3_47`).** For $\widetilde
C$ a partial quadrant, a basic germ $f$ and the data of V3.34 with $D(f + \iota s)(0)$ surjective and
kernel $K$ in good position to $\widetilde C \oplus W$: there are a good complement $Y$ of $K$, a
relatively open $V \ni 0$ in $K \cap (\widetilde C \oplus W)$, and $\sigma$ with values in $Y$ and
$W$-components on level $1$, $C^1$ on $V$, $\sigma(0) = 0$, $D\sigma(0) = 0$, with $v + \sigma(v) \in
U_0$ a zero for $v \in V$; for every $k \ge 1$ a $C^k$ lift $\sigma_k : V_k \to E_k$ of $\sigma$ on a
relatively open $V_k \subseteq V$ containing $0$; and an open $U'' \ni 0$ in which every zero in $U_0$
is of this form. *Book:* Corollary 3.47, p. 106. *Hidden hypotheses:* none. *Deviation (restated):* (1)
level-wise, as in V3.38. *Proof:* Theorem 3.43 for the push-forward, transported back linearly; Lemma
3.70 and Theorem 3.72 are not needed. With $Y$ closed and its projection onto $K$ mapping $\widetilde C
\oplus W$ into itself: V3.77.

**V3.43 (Definition 3.48; `Polyfold.IsFillingGerm`, `Polyfold.IsFillerOf`).** As V3.7. *Book:*
Definition 3.48, p. 109. *Hidden hypotheses:* none. *Deviation:* none. Since the switch to the text's
germ reading (phase 2) the filling is the germ notion of V3.7; the stricter whole-chart filler
(`IsFillerOf`, with `IsFilledVersion`), for which "filled version = filling" on a given $U$ is false
(round-trip item V3.43), is kept (Findings, Chapter 3, items 220–221, 330). Formerly "narrower", for
the whole-chart reading.

**V3.44 (Remark 3.49; `Polyfold.IsFillerOf.remark_3_49`).** For a filler there is an open $W \ni 0$ with $f = g$ on
$O \cap W$ and, for $y \in U \cap W$, $g(y) = \rho(r(y))g(y)$ only if $y \in O$. *Book:* Remark 3.49, p. 109.
*Hidden hypotheses:* none. *Deviation:* none.

**V3.45 (Definitions 3.50, 3.51; `Polyfold.StrongBundle.IsScFredholmGerm`,
`Polyfold.StrongBundle.IsScFredholmSection`, `Polyfold.StrongBundle.IsScFredholmGermTame`,
`Polyfold.StrongBundle.IsScFredholmSectionTame`,
`Polyfold.StrongBundle.IsScFredholmGermTameWholeChart`).** As V3.13 and V3.16, with the chart of the
germ data tame: V3.103. *Book:* Definitions 3.50, 3.51, p. 110 (for a tame strong bundle; the chart
of Definition 3.50 has a tame local strong bundle $K \to O$). *Hidden hypotheses:* none.
*Deviation:* none. The forms with a tame chart (V3.103) are the ones the theorems of §3.6 use; since
the switch to the text's germ reading (phase 2) they take the filling and the sc⁺-section as germs,
as the text does, and the earlier whole-chart forms (`…WholeChart`), which imply them (round-trip
item V3.45), are kept (Findings, Chapter 3, items 220–221, 330). The forms of V3.13 and V3.16 drop
the tameness, which §3.1 does not need. Formerly "narrower", for the whole-chart reading.

**V3.46 (Proposition 3.52; `Polyfold.proposition_3_52_index`,
`Polyfold.proposition_3_52_local_index`, `Polyfold.ConjugationData`,
`Polyfold.ConjugationData.scDeriv_isFredholm_index`, `Polyfold.ConjugationData.index_eq`,
`Polyfold.proposition_3_52`, `Polyfold.proposition_3_52_local`, `Polyfold.proposition_3_52_sc`,
`Polyfold.proposition_3_52_local_sc`, `Polyfold.ConjugationData.scDeriv_isScFredholm`,
`Polyfold.StrongBundle.linAt_isScFredholm`).** Let $f$ be a section of a strong bundle with
$(f, x_0)$ an sc-Fredholm germ and $f(x_0) = 0$. In the strong bundle chart of Definition 3.11
centred at $x_0$, with the filling germ $g$ (a derivative family $Dg$ on a germ inside $U$) and the
local sc⁺-germ $s$ for which $g - s$ is conjugated to a basic germ, $Dg(0) : E_0 \to F_0$ and
$Tf(x_0) := Dg(0)|_{Dr(0)E_0} : Dr(0)E_0 \to \rho(0)F_0$ are Fredholm operators, and for **every**
conjugation of $g - s$ to a basic germ $h : O(\widetilde C \oplus W, 0) \to \mathbb R^N \oplus W$,
$\widetilde C \subseteq \mathbb R^n$, both have index $n - N$ (`ConjugationData`: the witnesses of a
conjugation, Definition 3.11, as data). In particular $n - N$ is the same for all conjugations of
one germ: for $k$ sc-smooth with $k(0) = 0$ and any conjugation of $k$ to a basic germ, $Dk(0)$ is
Fredholm of index $n - N$. They are sc-Fredholm operators: $Dg(0) : E \to F$ is an sc-operator,
$T_0O = Dr(0)E$ and $K_0 = \rho(0)F$ are sc-subspaces, and $Tf(x_0) : T_0O \to K_0$ is sc-Fredholm,
both of index $n - N$ on every level; for an sc-Fredholm section the same holds in every strong
bundle chart around a zero $y$, at the point $z$ over $y$, for $\mathrm{Lin}(z) : T_zO \to K_z$.
*Book:* Proposition 3.52, p. 110 ($Tf(x) : T_xX \to Y_x$ is sc-Fredholm); the index $n - N$ is used
in the proof of Theorem 3.54. *Hidden hypotheses:* none. *Deviation (restated):* in charts ($T_xX$
carries no linear structure here, Chapter 2). The hypothesis is the text's since the switch to the
germ reading (phase 2): the filling and the sc⁺-section are germs (V3.13), and $Dg(0)$ is the value
at $0$ of any derivative family of the filling germ; the forms for germ data on the whole chart are
the `_wholeChart` declarations of the same names (Findings, Chapter 3, items 220–221, 289, 310, 331).
Formerly "narrower", for that hypothesis. The sc-Fredholm property, first proved on level $0$ only,
follows the text's argument with two steps it leaves out:
$D(g - s)(0) = \Gamma(0)^{-1}Dh(0)D\psi(0)$ is sc-Fredholm by the criterion of V1.8, and $T_0O$,
$K_0$ are sc-subspaces (Definition 2.47 at the smooth point $0$, the closed graph theorem); in other
charts the levels are transported by the chart change at smooth points (Findings, Chapter 3, items
235, 239). The first version (`Polyfold.proposition_3_52`, kept for its consumers) states the index
as "$n - N$ for some natural numbers $n$, $N$", which carries no information;
`proposition_3_52_index` identifies $n$ and $N$ with the dimensions of the conjugating basic germ
(Findings, Chapter 3, item 120). In every other strong bundle chart around $x_0$ the linearization
is Fredholm of the same index (V3.96).

**V3.47 (Definition 3.53; `Polyfold.IsGoodPositionAtGerm`, `Polyfold.IsGoodPositionAt`,
`Polyfold.IsInGoodPositionIn`, `Polyfold.StrongBundle.IsGoodPositionGerm`,
`Polyfold.StrongBundle.IsGoodPositionGerm.forall_isGoodPositionAtGerm`, `Polyfold.IsScGoodComplementIn`,
`Polyfold.IsInGoodPositionScIn`, `Polyfold.IsGoodPositionAtScGerm`, `Polyfold.IsGoodPositionAtSc`,
`Polyfold.StrongBundle.IsGoodPositionGermSc`,
`Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGermSc`,
`Polyfold.StrongBundle.isGoodPositionGermSc_iff`).** In a chart centred at the zero, with the filling
germ $g$ and $Dg(0)$ the value at $0$ of a derivative family of $g$ (the same for all): the germ is in
good position if $Tf(0) = Dg(0)|_{T_0O} : T_0O \to K_0$ is onto and
$\ker Dg(0)$ is in good position to $T_0O \cap C$ inside $T_0O$ (interior of $\ker Dg(0) \cap C$ in
$\ker Dg(0)$ nonempty, a good complement inside $T_0O$). For a section, $(f, x_0)$ is in good
position if it has the data of Definition 3.11 at $x_0$ with the germ in good position in that
chart. With the text's sc-complement (`IsGoodPositionAtSc`; for a section `IsGoodPositionGermSc`, in
a tame chart) the kernel has a good sc-complement inside $T_0O$ ($T_m = N_m \oplus P_m$ on every
level); at a zero of an sc-Fredholm section with tame germ data the two forms agree. *Book:*
Definition 3.53, p. 111. *Hidden hypotheses:* none. *Deviation (restated):* in a chart rather than
in $T_xX$; no case distinction $d_X(x) \ge 1$, which is recovered as a theorem for tame germ data:
at a zero with $d_X = 0$ good position in a tame chart is the surjectivity of the linearization
(V3.100). At a zero the linearization and the two conditions do not depend on the chart (V3.78);
Definition 3.53 at a zero from a chart not centred there is V3.79, and in any chart of the germ data
V3.107. The form in a tame chart, which the theorems of §3.6 assume and conclude, is V3.103. The
germ data are the text's since the switch to the germ reading (phase 2, V3.13); the whole-chart forms
are `IsGoodPositionGermWholeChart`, `IsGoodPositionGermScWholeChart` (Findings, Chapter 3, items
220–221, 280, 320, 330); that "an sc-splitting
of $T_0O$", written in $E$, is an sc-splitting of the sc-Banach space $T_0O$ is not formalized (item
214).

**V3.48 (Theorem 3.54, the graph description of the solution set; `Polyfold.theorem_3_54_graph`,
`Polyfold.theorem_3_54_linear`, `Polyfold.theorem_3_54_pushforward`,
`Polyfold.scDeriv_mem_iff_of_inverse`).** Let $f$ be a section of a strong bundle, with $f(x_0) = 0$ and
$(f, x_0)$ in good position in a tame chart (V3.103). Then there are: a tame strong bundle chart $\varphi$
centred at $x_0$ (compatible with the atlas, with tame base retraction); an sc-smooth $\psi$ on its $U$ with
$\psi(0) = 0$ into a relatively open $U'$ of $\widetilde C \oplus W$ ($\widetilde C$ a partial
quadrant), with an sc-smooth inverse $\psi'$ on $U'$; the data of Theorem 3.38 and a basic germ $h'$
with $D(h' + \iota t)(0)$ surjective and kernel $K$ in good position, $K$ a smooth subspace; a closed
good complement $Y$ of $K$; a relatively open $V' \ni 0$ in $K \cap (\widetilde C \oplus W)$; $\sigma$
with values in $Y$ and $W$-components on level $1$, $C^1$ on $V'$, $\sigma(0) = 0$, $D\sigma(0) = 0$,
such that every $v + \sigma(v)$, $v \in V'$, is a zero of $h' + \iota t$ in its germ, and for every $k
\ge 1$ a $C^k$-lift $\sigma_k : V_k \to E'_k$ of $\sigma$ on a relatively open $V_k \ni 0$, $V_k
\subseteq V'$ (Theorem 3.47 (1)); and an open $V_x \ni x_0$ in the chart domain on which $\psi\varphi$
is injective, $f(y) = 0 \iff (h' + \iota t)(\psi\varphi(y)) = 0$, and $\psi\varphi(\{y \in V_x \mid f(y)
= 0\}) = \{v + \sigma(v) \mid v \in V'\}$. On the way: in the chart, $Dg(0)$ is surjective with kernel
in good position to $C$ in $E$, $x \in C \iff D\psi(0)x \in C'$, and $D(\Psi_*g)(0) =
\Gamma(0)Dg(0)D\psi(0)^{-1}$ is surjective Fredholm with kernel in good position. *Book:* Theorem 3.54, p.
111, the step (3) of its proof, pp. 113–114. *Hidden hypotheses:* the tameness of the chart at $x_0$, used
only as $(1 - Dr(0))E \subseteq E_0$; the neighbourhood $V$ made explicit; the kernel is smooth (the text:
without comment).
*Deviation (narrower):* only the graph description (3) of the proof; conclusions (1) and (2) of the
theorem are V3.82 and V3.85, the choice of $Y$ with the projection property V3.77.

**V3.49 (Lemma 3.55; `Polyfold.lemma_3_55`, `Polyfold.lemma_3_55_core`).** In $E = \mathbb R^n \oplus
W$, $C = [0, \infty)^n \oplus W$: let $N$ be finite-dimensional in good position with good complement
$Y$, **$Y$ closed**, and $\tau : N \to E$ with values in $Y$, $C^1$ on $N \cap C$, $\tau(0) = 0$,
$D\tau(0) = 0$. There is $\rho > 0$ such that for $v \in N \cap C$ with $|v| < \rho$: $v + \tau(v) \in
C$, and $Y$ is a good complement of $N_v = \{n + D\tau(v)n \mid n \in N\}$ with respect to the partial
quadrant $C_{v + \tau(v)}$ (so $E_0 = N_v \oplus Y$, both closed, with the good-complement constant
independent of $v$). The core holds for any $C$ cut out by coordinate functionals. *Book:* Lemma 3.55, p.
114, proof pp. 132–135. *Hidden hypotheses:* $Y$ closed (needed for $D\tau(v)n \in Y$). *Deviation
(narrower):* the added closedness; $\tau$ given on all of $N \cap C$. The form used in Theorem 3.54 —
for a relatively open $V \subseteq N \cap C$ and any presentation of $C$, with the good position of
$N_v$ — is `Polyfold.lemma_3_55_relOpen` (V3.80).

**V3.50 (Theorem 3.56 from the tangent germ property; `Polyfold.theorem_3_56_of_tangentGerm`).** If $X$
has no boundary and the nonempty zero set $S$ of $f$ has at every point regular data of Definition 3.25
(V3.24), then $S$ is a sub-M-polyfold whose induced structure is an $n$-dimensional manifold with
corners without boundary. *Book:* Theorem 3.56, p. 115. *Hidden hypotheses:* the regularity conditions
of V3.24. *Deviation (narrower):* assumes the tangent germ property of $S$, which the text derives from
Theorem 3.54. The theorem with the text's hypotheses is V3.86.

**V3.51 (Theorem 3.57 from the tangent germ property; `Polyfold.theorem_3_57_of_tangentGerm`).** If the
nonempty zero set $S$ of $f$ has at every point regular data of Definition 3.25, then $S$ is a
sub-M-polyfold whose induced structure is tame and an $n$-dimensional manifold with boundary with
corners. *Book:* Theorem 3.57, p. 115. *Hidden hypotheses:* as V3.50. *Deviation (narrower):* as V3.50.
The theorem with the text's hypotheses is V3.87.

**V3.52 (Lemma 3.59, abstract form; `Polyfold.lemma_3_59`, `Polyfold.FamilyCompactness`).** Let $b
\mapsto L(b)$ be a family of sc-operators $X \to Y$, $b$ in a finite-dimensional space, with $(b, h)
\mapsto L(b)h$ continuous on $O \times X_0$ for a set $O \ni 0$, $L(0)$ injective on $X_0$, and the
compactness property on level $0$: if $b_j \to b$ in $O$, $(h_j)$ is bounded in $X_0$ and $L(b_j)h_j \to
0$, then $(h_j)$ has a convergent subsequence. Then $L(b)$ is injective on $X_0$ for $b \in O$ near $0$.
*Book:* Lemma 3.59, p. 117 (for $L(b) = P_Y \circ Df(b)|_X$ in the setting of Theorem 3.58). *Hidden
hypotheses:* none. *Deviation (restated):* for an abstract family; in the proof of Theorem 3.58 its
hypotheses are derived from those of the theorem for $L(b) = P_Y \circ Df(b, 0)|_X$
(`Polyfold.familyCompactness_derivFamOp`, `Polyfold.continuousOn_derivFamOp`, V3.89).

**V3.53 (Lemma 3.60, abstract form; `Polyfold.lemma_3_60`).** For a compact set $K$ of parameters, a
family of sc-operators $L(b)$ with $(b, h) \mapsto L(b)_mh$ continuous on $K \times X_m$, every
$L(b)_m$, $b \in K$, injective, and the compactness property on level $m$: there is $c_m > 0$ with
$c_m|h|_m \le |L(b)h|_m$ for all $b \in K$, $h \in X_m$. *Book:* Lemma 3.60, p. 118. *Hidden
hypotheses:* none. *Deviation (restated):* abstract form; the injectivity on level $m$ is a hypothesis,
which in Theorem 3.58 comes from level $0$ (`Polyfold.ScOperator.injective_lvl`, V3.89).

**V3.54 (Lemma 3.61; `Polyfold.lemma_3_61`).** Let $V$ be a germ of relatively open neighbourhoods of
$0$ in a partial quadrant $\widetilde C$ of a finite-dimensional $G$, and $L(v) : E \to F$
sc-isomorphisms such that $(v, h) \mapsto L(v)h$ is an sc-smooth germ on $V \oplus E$ (levels $V_m
\times E_m$) and for every $m$ there is $c_m > 0$ with $c_m|h|_m \le |L(v)h|_m$ for $v \in V_0$, $h \in
E_m$. Then $(v, k) \mapsto L(v)^{-1}k$ is an sc-smooth germ on $V \oplus F$. *Book:* Lemma 3.61, p. 118,
quoted from [25] without proof. *Hidden hypotheses:* none (no operator-norm continuity of $v \mapsto
L(v)$). *Deviation (restated):* for germs. *Proof:* supplied; the differentiability uses the compactness
of $F_1 \to F_0$. Used in Theorem 3.58 in set form (`Polyfold.famInv_isScSmooth_of`, V3.88).

**V3.55 (Lemma 3.65; `Polyfold.lemma_3_65`).** For functionals $\ell_i$ cutting out $C$, a good complement $P$ of
$N$ (constant $\varepsilon$) satisfies $\ell_i(p) = 0$ for $p \in P$ and every $i$ vanishing at some nonzero point of
$N \cap C$. *Book:* Lemma 3.65, p. 123. *Hidden hypotheses:* none. *Deviation:* none.

**V3.56 (Proposition 3.69; `Polyfold.proposition_3_69`).** For $N$ finite-dimensional in good position to $C =
[0, \infty)^n \oplus W$ in $\mathbb R^n \oplus W$ and $x \in N \cap C$: $d_{N \cap C}(x) = d_C(x)$ if $x \notin N \cap W$, and
$d_{N \cap C}(x) + \dim(N \cap W) = \dim N$ if $x \in N \cap W$. *Book:* Proposition 3.69, p. 126. *Hidden
hypotheses:* none. *Deviation (restated):* (2) additively.

**V3.57 (Lemma 3.70; `Polyfold.lemma_3_70`).** For $N$ in good position to $C = [0, \infty)^n \oplus W$ with good
complement $Y$ and $\tau : N \to E$ with values in $Y$, $C^1$ on $N \cap C$, $\tau(0) = 0$, $D\tau(0) = 0$: there is
$\rho > 0$ such that for $v \in N \cap C$, $|v| < \rho$, $v + \tau(v) \in C$, and $d_{N \cap C}(v) = d_C(v + \tau(v))$ if $v
\notin N \cap W$. *Book:* Lemma 3.70, p. 127. *Hidden hypotheses:* none. *Deviation (hypotheses explicit):*
"close to $0$" made explicit.

**V3.58 (Theorem 3.72; `Polyfold.theorem_3_72`).** For $C$ a partial quadrant in a finite-dimensional $V$, $U$ a
relatively open neighbourhood of $0$ in $C$ and $f$ of class $C^j$, $j \ge 1$, on $U$ with $f(U) \subseteq C$, $f(0) =
0$, $Df(0)C = C$ and $d_C(x) = d_C(f(x))$ on $U$: there are relatively open $U' \subseteq U$ and $V'$ containing
$0$ with $f(U') = V'$, $f$ injective on $U'$, and an inverse $g$ of class $C^j$ on $V'$. *Book:* Theorem 3.72,
p. 136 (smooth). *Hidden hypotheses:* none. *Deviation (stronger):* $C^j$; the degeneracy hypothesis used
only as "interior iff interior".

**V3.59 (Proposition 3.73; `Polyfold.proposition_3_73`, `Polyfold.InvData`).** For $U$ relatively open
and convex in $C$, $f : U \to C$ of class $C^j$, $j \ge 1$, $\|Df - 1\| \le \tfrac12$ on $U$, and $x$
interior iff $f(x)$ interior: $f(U)$ is relatively open in $C$, $f$ is injective on $U$, with an inverse
of class $C^j$ on $f(U)$. *Book:* Proposition 3.73, p. 137. *Hidden hypotheses:* none. *Deviation
(stronger):* $0 \in U$, $f(0) = 0$ not needed; (3) weakened. With the hypotheses its proof uses, without
the partial quadrant: V3.90.

**V3.60 (Lemma 3.74; `Polyfold.InvData.injOn`, `Polyfold.InvData.ball_inter_subset_image`,
`Polyfold.InvData.image_relOpen`).** Under the hypotheses of V3.59: $\tfrac12|x - x'| \le |f(x) - f(x')| \le
\tfrac32|x - x'|$, $f$ is injective, $B(x', 3r) \cap C \subseteq U$ implies $B(f(x'), r) \cap C \subseteq f(U)$, and $f(U)$ is
relatively open in $C$. *Book:* Lemma 3.74, p. 137. *Hidden hypotheses:* the interior starting point
with $f(x_0) \in B(y', r)$. *Deviation:* none in the statement (openness of $f$ on subsets not stated
separately).

**V3.61 (Corollary 3.75; `Polyfold.corollary_3_75`).** Under the hypotheses of V3.59, $f : U \to f(U)$ is a
homeomorphism. *Book:* Corollary 3.75, p. 139. *Hidden hypotheses:* none. *Deviation:* none.

**V3.62 (Lemma 3.77; `Polyfold.InvData.hasFDerivWithinAt_inv`).** Under the hypotheses of V3.59 the
inverse is differentiable within $f(U)$ with $Dg(y) = [Df(g(y))]^{-1}$. *Book:* Lemma 3.77, p. 140 (for
any homeomorphism $f : U \to V$ with $V$ relatively open and $Df$ invertible). *Hidden hypotheses:*
none. *Deviation (narrower):* under the hypotheses of Proposition 3.73, which imply the lemma's. With
the hypotheses its proof uses, without the partial quadrant: V3.90.

**V3.63 (Theorem 3.78; `Polyfold.theorem_3_78`, `Polyfold.ContractionData.exists_solution`).** For a partial
quadrant $C$ in a finite-dimensional $V$, $U$ a relatively open neighbourhood of $0$ in $C$, $f : U \to F$ of
class $C^j$, $j \ge 1$, $f(0) = 0$, $Df(0)$ onto, $K = \ker Df(0)$ in good position with good complement $Y$:
there are a relatively open $V' \ni 0$ in $K \cap C$, $\tau : K \to Y$ of class $C^j$ on $V'$, $\varepsilon, \sigma > 0$
with (1) $\tau(0) = 0$, $D\tau(0) = 0$, $k + \tau(k) \in U$ and $f(k + \tau(k)) = 0$ for $k \in V'$; (2) $|\tau(k)| \le \sigma$
for $k \in V'$, $|k| \le \varepsilon$; (3) $k \in V'$, $|k| \le \varepsilon$, $y \in Y$, $|y| \le \sigma$, $k + y \in U$, $f(k + y) =
0$ imply $y = \tau(k)$. *Book:* Theorem 3.78, p. 141. *Hidden hypotheses:* $f(k + \tau(k)) = 0$ and $k + y \in U$,
omitted in the text. *Deviation (stronger):* the two clauses; $F$ any normed space; only convexity and
interior of $C$ used.

**V3.64 (Lemma 3.79; `Polyfold.ContractionData.exists_radii`, `Polyfold.Radii.eq_τ`).** In the normalized data
there are $\varepsilon, a, b > 0$, $\varepsilon a \le b$, with the region $R = \{|k| \le a, |y| \le b\} \cap C \subseteq U$ and $\|DB\|
\le \varepsilon/(2(1 + \varepsilon))$ on $R$; a fixed point $y$ of $B(k, \cdot)$ with $(k, y) \in R$ is $\tau(k)$. *Book:*
Lemma 3.79, p. 142. *Hidden hypotheses:* none. *Deviation:* none.

**V3.65 (Lemma 3.80; `Polyfold.Radii.mapsTo_ball`).** $B(k, \cdot)$ maps $\{|y| \le \varepsilon|k|\}$ into itself for $k \in
K \cap C$, $|k| < a$, and has a fixed point there. *Book:* Lemma 3.80, p. 143. *Hidden hypotheses:* the
maximum is over $B \cap C$. *Deviation (hypotheses explicit).*

**V3.66 (Lemma 3.81; `Polyfold.Radii.norm_τ_sub_le`, `Polyfold.Radii.norm_τ_sub_le_global`,
`Polyfold.Radii.norm_τ_sub_le_eps`, `Polyfold.Radii.lipschitzOnWith_τ`).**
$|\tau(k)| \le \varepsilon|k|/2$, $\tau$ is continuous, and
$|\tau(k) - \tau(k_0)| \le \frac{\varepsilon}{1 + \varepsilon}|k - k_0| \le \varepsilon|k - k_0|$
for all $k, k_0 \in V_0$ (an older form with the constant $1 + 2\varepsilon$ is kept for the proofs
that use it). *Book:* Lemma 3.81, p. 144 (constant $\varepsilon$). *Hidden hypotheses:* none.
*Deviation (stronger):* the sharper constant $\varepsilon/(1 + \varepsilon)$. The text's argument
uses the point $(k, \tau(k_0))$, which lies in the region of the contraction when $|k_0| \le 2|k|$;
otherwise $|k| < 2|k_0|$ and the same argument with $k$ and $k_0$ exchanged applies, a case
distinction the text omits (Findings, Chapter 3, item 216). Formerly "narrower", with the constant
$1 + 2\varepsilon$.

**V3.67 (Lemma 3.82; `Polyfold.Radii.contDiffOn_τ`).** $\tau$ is differentiable on $V_0 = \{k \in K \cap C : |k| < a\}$
with $D\tau(k) = (1 - D_2B(k, \tau(k)))^{-1}D_1B(k, \tau(k))$ and of class $C^j$ on $V_0$. *Book:* Lemma 3.82, p. 144
("on a possibly smaller neighbourhood"). *Hidden hypotheses:* none. *Deviation (stronger):* no shrinking.

**V3.68 (Theorem 3.19, the implicit function theorem, interior case, first form;
`Polyfold.theorem_3_19`, `Polyfold.theorem_3_19_linearization`,
`Polyfold.MPolyfold.IsWithoutBoundary`, `Polyfold.theorem_3_19_linearization_sc`,
`Polyfold.StrongBundle.linAt_isScFredholm`).** Let $X$ be an
M-polyfold with $d_X \equiv 0$, $f$ an sc-Fredholm section (V3.16) of a strong bundle $P : Y \to X$
with tame germ data (V3.103), $f(x_0) = 0$, and let $(f, x_0)$ be in good position in a tame chart
(V3.47, V3.103) **with a filler that satisfies condition (3) of Definition 3.4 at the zeros of the
filler near $0$** (V3.82). Then there are an open $U \ni x_0$ and $d \in \mathbb N$ such that every
zero $y \in U$ is a smooth point with $(f, y)$ in good position in a tame chart (in particular
$f'(y)$ is onto), and $S(f, U) = \{y \in U \mid f(y) = 0\}$ is a sub-M-polyfold of $X$ whose induced
structure (Proposition 2.21) is equivalent to that of a $d$-dimensional manifold with boundary with
corners and has degeneracy index $0$ at every point. The first clause: for an sc-Fredholm section
and a zero $x_0$ in good position, in the chart of Definition 3.11 centred at $x_0$, $Dg(0)$ and
$f'(x_0) = Tf(x_0) = Dg(0)|_{T_0O} : T_0O \to K_0$ are sc-Fredholm operators with the same index
$n - N$ on every level, and $Tf(x_0)$ is onto on every level
(`Polyfold.theorem_3_19_linearization_sc`; Proposition 3.52 in sc form, V3.46); with no chart singled
out, in every strong bundle chart around $x_0$ the linearization $\mathrm{Lin}(z) : T_zO \to K_z$ is
an sc-Fredholm operator with the same index on every level (`Polyfold.StrongBundle.linAt_isScFredholm`,
V3.96). *Book:* Theorem 3.19, p. 74
("$f'(x_0)$ surjective"; the local solution set is a manifold of dimension the Fredholm index,
$f'(y)$ onto and $\ker f'(y) = T_yS(f, U)$). *Hidden hypotheses:* tameness of the bundle, read as
Definitions 3.50, 3.51 and 3.53 read it: germ data and good position in charts with tame base
retraction (V3.103; the reading "every chart compatible with the atlas has a tame base retraction",
under which this item was first proved, cannot be met, V3.104). *Deviation (narrower):* (i) the
filler condition at the nearby zeros, through Theorem 3.54 (1) (V3.82), which was an added
hypothesis when this form was proved and is now a theorem: it holds whenever $(f, x_0)$ is in good
position in a tame chart (V3.102), so this form has the text's hypotheses after all, and
`Polyfold.theorem_3_19'` states it without the condition (V3.95); (ii) the hypothesis "$f'(x_0)$
surjective" is read as good position (Definition 3.53 in the chart form), which at $d_X = 0$ is the
same (V3.100; the form with "$f'(x_0)$ surjective" is V3.101); (iii) $d$ is existentially quantified
here; "the dimension agrees with the Fredholm index" is V3.97; (iv) "$\ker f'(y) = T_yS$" in the
chart is V3.99; (v) $f'(x_0)$ in charts (V3.46); its sc-Fredholm property, first proved only on
level $0$, holds on every level. *Proof:* Theorem 3.23 (V3.69) and Lemma 2.26 ($d_S \le d_X = 0$).

**V3.69 (Theorem 3.23, the implicit function theorem, boundary case; `Polyfold.theorem_3_23_of_nearby`,
`Polyfold.theorem_3_23`, `Polyfold.MPolyfold.subPolyfold`,
`Polyfold.MPolyfold.IsManifoldWithCorners`).** Let $f$ be an sc-Fredholm section of a strong bundle,
$f(x) = 0$, $(f, x)$ in good position in a tame chart (V3.47, V3.103), and let every zero in an open
$V_{x_0} \ni x$ be in good position in a tame chart. Then there are an open $U$ with $x \in U \subseteq
V_{x_0}$ and $d \in \mathbb N$ such that every zero in $U$ is a smooth point and $S(f, U) = \{y \in U
\mid f(y) = 0\}$ is a sub-M-polyfold of $X$ whose induced structure (Proposition 2.21) is tame and
equivalent to that of a $d$-dimensional manifold with boundary with corners (an equivalent atlas of
charts on relatively open subsets of $d$-dimensional partial quadrants). For $f$ with tame germ data
(V3.103) and the filler condition of V3.82 at $x$ in place of the nearby good position
(`Polyfold.theorem_3_23`): the same, and every zero in $U$ is in good position in a tame chart. *Book:* Theorem 3.23, p. 77 ($f'(x)$ surjective with kernel in good position;
$S(f, U)$ consists of smooth points and is a tame sub-M-polyfold with a uniquely determined structure of
a manifold with boundary with corners, the induced one). *Hidden hypotheses:* tameness as in V3.68.
*Deviation (narrower):* the good position of the nearby zeros (Theorem 3.54 (1)) is a hypothesis of the
first form, the filler condition at the nearby zeros (V3.82) of the second; both are now theorems (V3.94,
V3.102), and the form with the text's hypotheses is V3.95, with the dimension as the Fredholm index V3.97;
$d$ is existentially quantified here; "uniquely determined" is the equivalence of atlases, not stated
separately. *Proof:* regular data of Definition
3.25 at every point of $S(f, U)$, of the same dimension by the local constancy (V3.85, V3.74), then
Theorem 3.27 (V3.24).

**V3.70 (Corollary 3.24; `Polyfold.corollary_3_24`, `Polyfold.corollary_3_24_sc`,
`Polyfold.forall_isGoodPositionGermSc_iff`).** Let $f$ be an sc-Fredholm section of a strong bundle
such that $(f, x)$ is in good position in a tame chart (V3.103) at every zero $x$, and let
$S = \{x \in X \mid f(x) = 0\}$ be nonempty. Then $S$ is a sub-M-polyfold of $X$ whose induced
structure is tame and equivalent to that of a manifold with boundary with corners of locally
constant dimension (V3.72). The same with good position in the text's sense (sc-complement, V3.47)
at every zero, which for an sc-Fredholm section with tame germ data is the same hypothesis
(`corollary_3_24_sc`). *Book:* Corollary 3.24, p. 78. *Hidden hypotheses:* tameness as in V3.68;
$S \ne \emptyset$ (for $S = \emptyset$ the formal charts have no values; the statement is then
empty). *Deviation (hypotheses explicit):* **no hypothesis added**; the text names no dimension, the
formal one is locally constant. It is Theorem 3.57 (V3.87) without its last clause.

**V3.71 (tameness is carried by sc-diffeomorphisms and by open subsets; `Polyfold.IsScDiffeoQuadrant`,
`Polyfold.IsScDiffeoQuadrant.transport`, `Polyfold.IsScDiffeoQuadrant.scDeriv_transport`,
`Polyfold.IsScSubspace.map`, `Polyfold.IsScSplitting.map`,
`Polyfold.IsScDiffeoQuadrant.isTame_transport`, `Polyfold.IsScDiffeoQuadrant.isTameRetract_image`,
`Polyfold.ScRetraction.restrict_isTame`, `Polyfold.IsTameRetract.inter_isOpen`,
`Polyfold.MChart.isTameRetract_image`).** Let $\psi : U \to U'$ be an sc-diffeomorphism between
relatively open subsets of partial quadrants ($\psi$ sc-smooth on $U$, $\psi'$ sc-smooth on $U'$,
mapping $U$ and $U'$ into each other, inverse to each other) and $r : U \to U$ a tame sc-smooth
retraction onto $O$ whose domain is $U$. Then $r' = \psi \circ r \circ \psi'$ is a tame retraction of
$U'$ onto $\psi(O)$, so $(\psi(O), C', E')$ is a tame retract; on the way $d_{C'}(\psi(x)) = d_C(x)$
(Theorem 1.25), $Dr'(y) = D\psi(x)Dr(x)D\psi'(y)$ at the level-$1$ points $y = \psi(x)$ with $x \in O$, and an sc-operator with
an sc-operator inverse carries sc-subspaces and sc-splittings. The restriction of a tame retraction to
$U \cap r^{-1}(W)$, $W$ open, is tame; an open subset $O \cap W$ of a tame retract is a tame retract;
the model $\varphi(s)$ of a chart restricted to an open $s$ of its domain is tame if the model of
$\varphi$ is. *Book:* used without statement in the proof of Proposition 3.26 ("$X' = \psi(X)$ is tame", p. 80)
and in the proof of Theorem 3.54 (the chart $\psi \circ \varphi$ of a tame M-polyfold, p. 114). *Hidden
hypotheses:* condition (2) of Definition 2.34 is transported at smooth points, where $D\psi(x)$ is an
sc-isomorphism, with $D\psi(x)E_x \subseteq E'_{\psi(x)}$ (the one-sided sign argument). *Deviation (not
in the book).*

**V3.72 (Theorem 3.27 with locally constant dimension; `Polyfold.theorem_3_27_loc`,
`Polyfold.MPolyfold.IsManifoldWithCornersLoc`, `Polyfold.MPolyfold.theorem_3_27_loc_isSubMPolyfold`,
`Polyfold.MPolyfold.theorem_3_27_loc_isTame`,
`Polyfold.MPolyfold.theorem_3_27_loc_isManifoldWithCornersLoc`,
`Polyfold.MPolyfold.theorem_3_27_loc_atlas_equiv`).** Let $M \ne \emptyset$ be a subset of an M-polyfold
$X$ such that every point of $M$ has regular data of Definition 3.25 (V3.22, conditions (a), (b) of
V3.24) of some dimension, which may depend on the point. Then $M$ is a sub-M-polyfold of $X$, its
induced structure is tame, and the charts $y \mapsto \pi\varphi(y)$ of all these data form an atlas
equivalent to the induced one, consisting of charts on relatively open subsets of partial quadrants of
finite-dimensional spaces (`IsManifoldWithCornersLoc`: a manifold with boundary with corners of locally
constant dimension); each of these charts is a chart of the induced structure containing its point.
*Book:* Theorem 3.27, p. 81 (for a fixed dimension $n$). *Hidden hypotheses:* (a), (b) of V3.24.
*Deviation (narrower):* the conditions (a), (b); the dimension may vary from point to point (same proof
as V3.24).

**V3.73 (the re-centring lemma; `Polyfold.recentre_contDiffOn_levels`,
`Polyfold.finrank_le_of_interior_image_nonempty`, `Polyfold.exists_contDiffOn_inverse`).** Let $\chi_1$,
$\chi_2$ be charts of an M-polyfold $X$ and $S \subseteq X$. Suppose that $\chi_1(S \cap V_{x_1}) = \{v +
\sigma_1(v) \mid v \in V_1\}$ for an open $V_{x_1}$ in the domain of $\chi_1$, where $K_1$ is a
finite-dimensional smooth subspace in good position to $C_1$ with a closed complement $Y_1$, $V_1$ is
relatively open in $K_1 \cap C_1$, and $\sigma_1$ has values in $Y_1$ and is of class $C^1$ on all of
$V_1$; that $\chi_2$ is centred at a point $y \in V_{x_1} \cap V_{x_2}$ and $\chi_2(S \cap
V_{x_2})$ is the graph of $\sigma_2$ over a relatively open $V_2 \ni 0$ in $K_2 \cap C_2$ (the same
conditions on $K_2$, $Y_2$), with $\sigma_2$ continuous, $\sigma_2(0) = 0$, $D\sigma_2(0) = 0$ and
$C^k$-lifts $\sigma_{2,k} : V_{2,k} \to E_{2,k}$ on relatively open neighbourhoods of $0$ for every $k
\ge 1$; and that $\chi_1(y) = v_0 + \sigma_1(v_0)$, $v_0 \in V_1$. Then $\dim K_1 = \dim K_2$, and for
all $m$, $k$ there is a relatively open $B' \ni v_0$ in $K_1 \cap C_1$, $B' \subseteq V_1$, on which
$\sigma_1$ takes values in $E_{1,m}$ and is of class $C^k$ into $E_{1,m}$. On the way: a map
differentiable on a set whose image has nonempty interior does not lower the dimension (Sard's lemma in
fixed dimension); and a $C^k$ map between relatively open subsets of convex sets with nonempty interior
in finite-dimensional spaces, with a continuous left inverse on its relatively open image and an
invertible derivative at a point, has a $C^k$ inverse near the image of that point. *Book:* the step
"$\delta$ is an sc$^\infty$-germ near every point $v_0 \in V$" of the proof of Theorem 3.27, p. 84.
*Hidden hypotheses:* $\sigma_1$ differentiable at $v_0$ (here $C^1$ on $V_1$; without it the step fails,
V3.24); $Y_1$, $Y_2$ closed; the lifts at $0$ (Theorem 3.47 (1), V3.42). *Deviation (narrower):* for two
graph descriptions of one set, with $\sigma_1$ of class $C^1$ on $V_1$. *Proof:* the linearization of
$\beta = \pi_1 \circ \chi_1\chi_2^{-1} \circ (1 + \sigma_2)$ at $0$ is injective by the chain rule for
the transition and its inverse on level $1$ and the tangency of the graph of $\sigma_2$ to the retract;
it is onto by the dimension count, not by the symmetric chain rule (which would need $\sigma_1$
differentiable into level $1$ at $v_0$); the inverse is $C^k$ by V3.90, not by Theorem 3.72 (which would
need $d_C(x) = d_C(\beta(x))$).

**V3.74 (condition (a) of `IsRegular` by re-centring;
`Polyfold.MPolyfold.TangentGermChart.exists_isRegular_of_locally`,
`Polyfold.MPolyfold.TangentGermChart.shrink`, `Polyfold.MPolyfold.TangentGermChart.exists_shrinkData`,
`Polyfold.MPolyfold.TangentGermChart.shrink_isRegular`,
`Polyfold.MPolyfold.TangentGermChart.exists_lift`).** Let $D$ be data of Definition 3.25 (V3.22) of
dimension $n$ for $M \subseteq X$ at $x$ with $\pi(O) \subseteq C$ (condition (b) of V3.24), and let
every point of $M$ in an open $U \ni x$ have data of Definition 3.25 of some dimension. Then $M$ has at
$x$ regular data (conditions (a) and (b) of V3.24) of dimension $n$ whose chart domain lies in $U$, and
every datum of Definition 3.25 for $M$ at a point of $M$ in that domain has dimension $n$. (The proof
shrinks $D$ — the chart restricted to an open subset, $V$ to a relatively open $V'$ inside the
neighbourhood of $0$ on which $\delta$ is $C^1$, the same $N$, $Y$, $\delta$ — and applies V3.73 at
every $v_0 \in V'$; the statement exports only the existence of the regular data.) *Book:* the proof of
Theorem 3.27, p. 84; the proof of Theorem 3.54, p. 115 ("proceeding as above"). *Hidden hypotheses:* the
data at the nearby points. *Deviation (narrower):* condition (b) is a hypothesis. Read off the statement
(not a separate Lean theorem): every point of a set with the $n$-dimensional tangent germ property has
data, so *for such a set, data at $x$ that satisfy (b) can be shrunk to regular data*; condition (a) of
V3.24 follows from (b). For the solution set of an sc-Fredholm section (b) holds by the choice of the
good complement (V3.75, V3.84).

**V3.75 (good complements whose projection maps the partial quadrant into itself;
`Polyfold.ProjectsInto`, `Polyfold.exists_goodComplement_projectsInto`,
`Polyfold.exists_proj_goodComplement`, `Polyfold.exists_proj_quadCone`, `Polyfold.ProjectsInto.mapL`).**
`ProjectsInto C N Y` means: $z \in C$, $k \in N$, $z - k \in Y$ imply $k \in C$; for $E_0 = N \oplus Y$
the projection onto $N$ along $Y$ maps $C$ into $N \cap C$. If the finite-dimensional subspace $N$ is in
good position to the partial quadrant $C$ of the sc-Banach space $E$, there is a continuous projection
$\pi : E_0 \to N$ with $\pi(C) \subseteq N \cap C$ whose kernel $Y$ is a good complement of $N$; $Y$ is
closed and `ProjectsInto C N Y` holds. The property is carried by continuous linear isomorphisms $S$
with $x \in C \iff Sx \in C'$. *Book:* not stated; the proof of Theorem 3.27 (p. 83) asserts that
$\Sigma = \{v + y \in C \mid v \in V, y \in Y\}$ is relatively open in $C$, which fails for an arbitrary
good complement (V3.24) and holds when $\pi(O) \subseteq C$. *Hidden hypotheses:* none. *Deviation (not
in the book):* the construction keeps the coordinates of a set $S$ of indices; when no coordinate
vanishes at a nonzero point of $N \cap C$ and $N \cap C \ne N$, one coordinate is kept (the natural
choice $S = \Sigma$ fails there: for $C = [0, \infty)^2$, $N = \mathbb R(1, 1)$, the projection along
the good complement $\mathbb R(1, 2)$ maps $(0, 1)$ to $-(1, 1)$).

**V3.76 (Corollary 3.39; `Polyfold.corollary_3_39`, `Polyfold.corollary_3_39_isConjugate`,
`Polyfold.ConjugationData.compIso_eq_strongShift`, `Polyfold.IsStrongBundleIso.shift`,
`Polyfold.IsStrongBundleIso.comp`, `Polyfold.IsStrongBundleIso.pushforward_comp`,
`Polyfold.StabilityData.linIso_isStrongBundleIso`, `Polyfold.ScOperator.isStrongBundleIso_prodMap`).**
Let $U$ be relatively open in a partial quadrant of $E$ with $0 \in U$, $g : U \to F$ sc-smooth and
conjugated to a basic germ (V3.13), and $s : U \to F_1$ sc-smooth into $F^1$ with $s(0) = 0$. Then the
level-$1$ map $(g + \iota s)^1 : U_1 \to F_1$ is conjugated to a basic germ on the shifted structures
$E^1 \triangleleft F^1$. Explicitly, for a conjugation $\Phi$ of $g$ to the basic germ $h$, with $t =
\Phi[1]_*s$ ($t(0) = 0$) and $h' = h + (t_{\mathbb R^N}, 0)$, there are the data of Theorem 3.38 (V3.34)
for $t_W$ such that: $h'$ is a basic germ and $\Phi_*(g + s) = h + t$ near $0$; the composite $\Gamma =
\Lambda \circ \Phi^1$ of the index raise of $\Phi$ and the linear coordinate change $\Lambda$ of Theorem
3.38 is a strong bundle isomorphism of the shifted structures onto a relatively open subset of
$(\widetilde C \oplus C) \oplus X^1$, with base map vanishing at $0$ and $\Gamma_* = \Lambda_* \circ
\Phi^1_*$; and $(\Gamma(u, (g + s)^1(u)))_2 = (\Lambda_*(h + t))^1(\gamma(u))$ for $u \in U_1$ near $0$,
a basic germ. The text's form "$\Gamma = \Psi \circ \Phi$, then raise the index" is the same map
(`compIso_eq_strongShift`). On the way: a pair of sc-isomorphisms, the index raise of a strong bundle
isomorphism and a composition of strong bundle isomorphisms are strong bundle isomorphisms, and
push-forwards compose. *Book:* Corollary 3.39, p. 93. *Hidden hypotheses:* the index raise of a strong
bundle isomorphism is one (used silently). *Deviation (restated):* "sc-germ" read as sc-smooth on $U$,
$s$ as an sc⁺-map on all of $U$ with $s(0) = 0$; the conclusion is a conjugation of $(g + s)^1$ on the
shifted structures; the text's "strong bundle map $\Psi$" is an isomorphism; the $\mathbb R^N$-component
of $t$ is absorbed into $h$; the text's $\tau : Z \to C$ is not applied.

**V3.77 (Theorems 3.43, 3.47 and 3.54 (3) with a closed good complement whose projection maps the
quadrant into itself; `Polyfold.theorem_3_43_closed`, `Polyfold.theorem_3_43_proj`,
`Polyfold.theorem_3_47_proj`, `Polyfold.theorem_3_47_closed`, `Polyfold.theorem_3_54_graph_proj`,
`Polyfold.IsGoodComplement.prod_top_graph`, `Polyfold.ShiftedBasicData.exists_sol_of_goodComplement`).**
The conclusions of V3.38, V3.42 and V3.48 hold with a good complement $Y$ that is closed and satisfies
`ProjectsInto` (V3.75) for the partial quadrant ($\widetilde C \oplus W$, resp. $C' = \widetilde C
\oplus W$): the projection onto the kernel along $Y$ maps the partial quadrant into the kernel's cone.
In Theorem 3.43, $Y = Z \oplus W$ for a good complement $Z$ of $\widetilde K$ chosen by V3.75: every
good complement $Z$ of $\widetilde K$ gives the good complement $Z \oplus W$ of $K' = \{(\alpha,
L\alpha)\}$ (constant $\varepsilon/(\|L\| + 1)$), the data of the proof exist for a prescribed $Z$, and
the projection property passes from $(\widetilde K, Z)$ to $(K', Z \oplus W)$; in Corollary 3.47 both
properties are carried by the linear homeomorphism of Theorem 3.38; in Theorem 3.54 (3) the shrinking of
$V'$ leaves $Y$ unchanged. *Book:* Theorem 3.43, p. 102; Corollary 3.47, p. 106; Theorem 3.54, step (3)
of the proof, p. 114. *Hidden hypotheses:* none. *Deviation (stronger):* two additional conclusions; the
closedness is the text's (its $Y'$ is an sc-complement), the projection property is not in the text and
is what makes condition (b) of Theorem 3.27 hold for the solution set (V3.84).

**V3.78 (the linearization at a zero in charts, and its chart independence; `Polyfold.linAt`,
`Polyfold.rho_scDeriv_comp_r`, `Polyfold.linAt_eq_scDeriv`,
`Polyfold.IsFilledVersion.fillerRestrict_eq_linAt`, `Polyfold.linAt_eq_germDeriv`,
`Polyfold.IsFillingGerm.fillerRestrict_eq_linAt`, `Polyfold.linAt_chart_change`,
`Polyfold.StrongBundle.linAt_chart_independence`, `Polyfold.IsInGoodPositionIn.transport`).** In a
strong bundle chart (retraction $r$ on $U$ onto $O$, fibre projections $\rho$, principal part $\mathbf
f$), $\mathrm{Lin}(z) = D(\mathbf f \circ r)(z)|_{T_zO}$, $T_zO = Dr(z)E$, at every level-$1$ point $z$
of the retract. At a zero its values lie in $K_z = \rho(z)F$; it equals $Dg(z)$ on $T_zO$ for every $g$
sc¹ on $U$ agreeing with $\mathbf f$ on $O$ near $z$, and for every sc¹-germ $g$ agreeing with $\mathbf
f$ near $z$ with $z$ in its germ ($Dg(z)$ the value of its derivative family; Findings, Chapter 3,
item 284); at a centred zero it is the $Tf(0)$ of Proposition 3.5 (V3.8), also for a filling germ. For strong bundle charts $c$, $c'$ whose transition is sc-smooth on $[0]$, a section with
sc-smooth principal parts in both, and a zero $y$ in both domains with level-$1$ points $z$, $z'$ over
$\varphi(y)$, $\varphi'(y)$: there are topological linear isomorphisms $A : T_zO \to T_{z'}O'$ and
$\Gamma : K_z \to K'_{z'}$ with $\Gamma \circ \mathrm{Lin}(z) = \mathrm{Lin}'(z') \circ A$ and, on
$T_zO$, $x \in C_z \iff Ax \in C'_{z'}$ (the partial quadrants at the two points). Hence for two strong
bundle charts of $P$ and an sc-smooth section, $\mathrm{Lin}(z)$ and $\mathrm{Lin}'(z')$ are
simultaneously onto, simultaneously Fredholm with the same index, and their kernels are simultaneously
in good position to the partial quadrants inside $T_zO$, $T_{z'}O'$ (good position inside a subspace is
carried by isomorphisms respecting the cones). *Book:* Definition 3.53 (p. 111) presupposes it;
Definition 2.38 (p. 42) asserts the chart independence of $T^R_xX$, $C_xX$ by Proposition 2.30; nothing
is said about $f'(x)$. *Hidden hypotheses:* the point is a zero (away from zeros the linearization is
not chart independent). *Deviation (not in the book):* the chart form of what gap G.13 leaves open; of
the compatibility of Definition 2.50 only the sc-smoothness of the transition on $[0]$ is used;
level-$1$ points suffice; no tameness.

**V3.79 (Definition 3.53 at a zero, from a chart not centred there;
`Polyfold.StrongBundle.isGoodPositionGermTame_of_chart_dense`,
`Polyfold.StrongBundle.isGoodPositionGerm_of_chart`,
`Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj`,
`Polyfold.StrongBundle.isGoodPositionAtGerm_of_chart_dense`).** Let $f$ be an sc-smooth section, $y$ a
zero with tame germ data (V3.103), $c$ a strong bundle chart of $P$ with $y$ in its domain (not
necessarily centred), $z$ a level-$1$ point over $\varphi(y)$, and $g$ an sc¹-germ on a germ $G$ of
$c$ with derivative family $Dg$ and $z \in G_1$, agreeing with $\mathbf f$ on $O$ near $\varphi(y)$.
If the range of $Dg(z)|_{T_zO}$ contains $\rho(z)k$ for every smooth $k \in F_\infty$, and
$\ker Dg(z) \cap T_zO$ is in good position to $C_{\varphi(y)}$ inside $T_zO$, then $(f, y)$ is in good
position in a tame chart (V3.47, V3.103). Variants: with all of $K_z$ in the range, for an
sc-Fredholm germ, in the chart centred at $y$ of Definition 3.11; with the hypotheses on
$\mathrm{Lin}(z)$ (V3.78). *Book:* the proof of Theorem 3.54, p. 115 ("proceeding as above", at a
nearby zero). *Hidden hypotheses:* the kernel hypothesis is on $\ker Dg(z) \cap T_zO$, not on
$\ker Dg(z)$ (condition (3) of the filler holds at its centre only); $z$ lies in the germ of $g$.
*Deviation (not in the book):* a dense part of $K_z$ in the range suffices, since the range of the
linearization in the chart of the germ data is closed (Proposition 3.52, V3.46), which is why the
dense form is stated for tame germ data. In the germ reading since phase 2; the whole-chart forms
are `Polyfold.StrongBundle.isGoodPositionGerm_of_chart_dense`,
`Polyfold.StrongBundle.isGoodPositionGerm_of_linAt` and the `_wholeChart` declarations (Findings,
Chapter 3, items 285, 301, 313).

**V3.80 (property (4) of the proof of Theorem 3.54 in the chart at $x_0$: Corollary 3.41 and Lemma 3.55
on the graph; `Polyfold.theorem_3_54_nearby`, `Polyfold.lemma_3_55_relOpen`,
`Polyfold.StabilityData.exists_surjective_Dfs'_graph`).** In the data of V3.48, for a section $f$ of a
strong bundle with $f(x_0) = 0$ and $(f, x_0)$ in good position in a tame chart (V3.103), there are a
presentation $T$ of $C' = \widetilde C \oplus W$ and an open $V_{x,1} \ni x_0$ such that for every
zero $y \in V_{x,1}$, with $\psi\varphi(y) = v + \sigma(v)$, $v \in V'$: $v + \sigma(v)$ lies on level
$1$ and $D(h + t)$ there is a surjective Fredholm operator of index $n - N$ ($n = \dim\mathbb R^n$, $N =
\dim\mathbb R^N$ of the basic germ); $v + \sigma(v) \in C'$; and $Y$ is a good complement of $N_v = \{k +
D\sigma(v)k \mid k \in K\}$ with respect to the partial quadrant $C'_{v + \sigma(v)}$, and $N_v$ is in
good position to it. Lemma 3.55 is proved in the form used: for $N$ in good position to $C$ (any
presentation) with closed good complement $Y$, $V$ relatively open in $N \cap C$, $\sigma : V \to Y$ of
class $C^1$ on $V$ with $\sigma(0) = 0$, $D\sigma(0) = 0$, for $v \in V$ near $0$: $v + \sigma(v) \in
C$, $Y$ is a good complement of $N_v$ with respect to $C_{v + \sigma(v)}$, and $N_v$ is in good position
to it. *Book:* the proof of Theorem 3.54, property (4), p. 114; Lemma 3.55, p. 114. *Hidden hypotheses:*
$Y$ closed (V3.49); that $N_v \cap C_z$ has interior in $N_v$, which Lemma 3.55 does not state.
*Deviation (narrower):* in the chart at $x_0$, for the tangent space $N_v$ of the graph; its
identification with the kernel at $y$ is V3.81.

**V3.81 (Theorem 3.54 (1) at the nearby zeros, the kernel; `Polyfold.theorem_3_54_nearby_kernel`,
`Polyfold.theorem_3_54_chart_kernel`, `Polyfold.StabilityData.graphSpace_eq_ker_Dfs'`,
`Polyfold.IsStrongBundleIso.ker_scDeriv_eq_map`, `Polyfold.scDeriv_mem_partialQuadrantAtWith_iff`,
`Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le`, `Polyfold.IsStrongBundleIso.ker_deriv_eq_map_germ`).**
Let $f$ be a section of a strong bundle,
$f(x_0) = 0$, $(f, x_0)$ in good position in a tame chart (V3.103). In a tame chart centred at $x_0$
(filling germ $g$ with a derivative family $Dg$, conjugation covering $\psi$ with inverse $\psi'$, the
germ $h + t$ with kernel $K$,
closed good complement, graph $\sigma : V' \to Y$) there is an open $V_{x,2} \ni x_0$ such that for
every zero $y \in V_{x,2}$, with $z_0 = \varphi(y)$, $\psi(z_0) = v + \sigma(v)$ and level-$1$ points
$z_{0,1}$ over $z_0$, which lies in the germ of $g$, $x_1$ over $v + \sigma(v)$: $\mathbf f = g$ on $O$ near $z_0$ and $g(z_0) = 0$;
$D(h + t)(x_1)$ is a surjective Fredholm operator of index $n - N$; $N_v = \ker D(h + t)(x_1)$;
$D(\Psi_*g)(x_1) = D(h + t)(x_1)$ and $\ker Dg(z_{0,1}) = D\psi'(x_1)(N_v)$; $Dg(z_{0,1})$ is onto;
$\ker Dg(z_{0,1}) \subseteq T_{z_0}O$; and $\ker Dg(z_{0,1})$ is in good position to $C_{z_0}$ inside
$T_{z_0}O$. *Book:* Theorem 3.54 (1), the kernel half, "from Corollary 3.41 and Lemma 3.55", p. 114.
*Hidden hypotheses:* the $C^1$-lift of $\sigma$ into level $1$ (Theorem 3.47 (1)) for $N_v \subseteq
\ker D(h + t)$; $\ker Dg(z_0) \subseteq T_{z_0}O$ comes from the tangency of the solution set to $O$,
not from the filler (whose condition (3) holds at $0$ only). *Deviation (narrower):* in the chart at
$x_0$; **no added hypothesis**; the surjectivity of $f'(y)$ is not part of it (V3.93, V3.94). In the
germ reading $z_{0,1}$ lies in the germ of the filling because the basic germ is taken on the points
that $\psi'$ maps into the germs of $g$ and $s$ (Findings, Chapter 3, items 276–278, 295).

**V3.82 (Theorem 3.54 (1) under the filler condition at the nearby zeros; `Polyfold.theorem_3_54_one`,
`Polyfold.StrongBundle.IsGoodPositionGermFilled`,
`Polyfold.exists_range_deriv_eq_ρ_of_normal_injective_germ`).** `IsGoodPositionGermFilled` at $x_0$: $x_0$
is smooth and there are the data of Definition 3.53 at $x_0$ in a tame chart (V3.47, V3.103: a centred
chart with tame base retraction, a filling germ $g$ with a derivative family $Dg$ on a germ $G$, a
local sc⁺-germ $s$ with $g - s$ conjugated to a basic germ, the germ in good position) and an
open $N \ni 0$ such that at every level-$1$ point $z_1 \in G_1$ with $z_1 \in O \cap N$ and $g(z_1) = 0$,
$Dr(z_1)b = 0$ and $\rho(z_1)Dg(z_1)b = Dg(z_1)b$ imply $b = 0$: condition (3) of Definition 3.4, the
injectivity of $(1 - \rho)Dg$ on $\ker Dr$, at the zeros of $g$ near $0$. Theorem: if $f$ is an
sc-Fredholm section with tame germ data (V3.103), $f(x_0) = 0$, and $(f, x_0)$ is in good position in this
strengthened sense, there is an open $V_x \ni x_0$ such that $(f, y)$ is in good position in a tame chart
(V3.47, V3.103) at every zero $y \in V_x$. The step it needs: at a zero $z$ of a filler with
$Dg(z)$ onto and condition (3) at $z$, $\rho(z)F \subseteq Dg(z)(T_zO)$ (Proposition 3.5 (1) at $z$).
*Book:* Theorem 3.54 (1), p. 111, proof p. 114. *Hidden hypotheses:* the filler condition at the
nearby zeros, added when this form was proved; it is a consequence of good position (V3.102), so the
form has the text's hypotheses after all. *Deviation (narrower):* the condition is a hypothesis of the
statement. Definition 3.4 imposes (3) at $0$ only (so does the 2017 version, Definition 3.13
there), and then the text's argument does not give the surjectivity of $f'(y)$: with respect to $E = T_{z_0}O \oplus \ker Dr(z_0)$, $F = K_{z_0} \oplus
\ker\rho(z_0)$, $Dg(z_0)$ is block triangular and $Tf(z_0)$ is onto iff the block $(1 -
\rho(z_0))Dg(z_0)|_{\ker Dr(z_0)}$ is injective, which is the local constancy of the index along the
solution set (Findings, Chapter 3, items 100, 157); both directions are formalized (V3.102). The
surjectivity holds with Definition 3.4 as stated, by an implicit function theorem at the nearby zero
(V3.93), and Theorem 3.54 (1) with the text's hypotheses is V3.94.

**V3.83 (the parameter extension of the proof of Proposition 6.2: the obstruction and the tilted kernel;
`Polyfold.mem_lineality_of_goodComplement_prod`, `Polyfold.sup_lineality_eq_top_of_goodComplement_prod`,
`Polyfold.isInGoodPosition_extendedKernel`).** (a) Let $C \subseteq V$ be closed under nonnegative
scaling with $0 \in C$ and $N \subseteq V$ a subspace. For every good complement of $\mathbb R \times N$
with respect to $\mathbb R \times C$, the $V$-components of its vectors lie in the lineality space $C
\cap (-C)$; so $\mathbb R \times N$ is in good position only if $N + (C \cap -C) = V$. (b) Let $K$, $Y'$
be subspaces of $\mathbb R^n \oplus W$ and $j : \Lambda \to \mathbb R^n \oplus W$ linear, $\Lambda$
finite-dimensional, with $K \cap j(\Lambda) = 0$, $(K + j(\Lambda)) \oplus Y' = \mathbb R^n \oplus W$,
$Y'$ in the lineality space of $\widetilde C \oplus W$ ($v + y \in \widetilde C \oplus W \iff v \in
\widetilde C \oplus W$ for $y \in Y'$), and $K + j(\Lambda)$ meeting the interior of $\widetilde C
\oplus W$. Then $\{((\lambda, a), w) \mid (a, w) + j(\lambda) \in K\}$ is in good position to $(\Lambda
\times \widetilde C) \oplus W$. *Book:* not in Chapter 3; the linear algebra of the perturbation
argument of the text's Proposition 6.2, tried for the surjectivity of V3.82. *Hidden hypotheses:* none.
*Deviation (not in the book):* the rest of the argument is not formalized; it would give the
surjectivity only on a neighbourhood depending on $\Lambda$ (Findings, Chapter 3, item 106). The
surjectivity is proved by another argument, with one perturbation direction at a time and the implicit
function theorem at the nearby zero (V3.93).

**V3.84 (Theorem 3.54 (2) at the centre: the data of Definition 3.25 for the solution set at $x_0$;
`Polyfold.theorem_3_54_tangentGermChart_proj`, `Polyfold.theorem_3_54_tangentGermChart`,
`Polyfold.MChart.compDiffeo`, `Polyfold.MChart.compDiffeo_isChart`, `Polyfold.isScInftyGermAt_of_lifts`,
`Polyfold.StabilityData.ker_Dfs_le_smooth`,
`Polyfold.MPolyfold.TangentGermChart.π_mem_of_projectsInto`).** Let $f$ be a section of a strong bundle,
$f(x_0) = 0$, $(f, x_0)$ in good position in a tame chart (V3.103). Then there are an
open $V_x \ni x_0$ and $d \in \mathbb N$ such that $\{y \in V_x \mid f(y) = 0\}$ has at $x_0$ data of
Definition 3.25 of dimension $d$ (V3.22) with $\pi(O) \subseteq C$ (condition (b) of V3.24). The data:
the chart $\psi \circ \varphi$ onto $\psi(O)$ (for a chart $\varphi$ of $X$ and an sc-diffeomorphism
$\psi$ between relatively open subsets of partial quadrants whose domain contains the retract $O$ of
$\varphi$, $\psi \circ \varphi$ is a chart of $X$ when $\psi(O)$ is a retract), whose model is a tame
retract by V3.71; $N = \ker D(h + t)(0)$, a smooth subspace; the closed good complement with the
projection property and the map $\sigma$ of V3.77; $\sigma$ is an sc$^\infty$-germ in the sense of V3.22
because it has $C^k$-lifts into level $k$ for every $k$. *Book:* the proof of Theorem 3.54, p. 115 ("$S$
possesses the $d$-dimensional tangent germ property", $d = \dim\ker f'(x)$). *Hidden hypotheses:* the
kernel is a smooth subspace (the text takes it so without comment); $\psi(O)$ is tame (V3.71).
*Deviation (narrower):* at $x_0$ only (the other points: V3.85); $d$ is existentially quantified here
(the proof takes $d = \dim\ker D(h + t)(0)$); that $d$ is the Fredholm index of $f'(x_0)$ is V3.97.

**V3.85 (Theorem 3.54 (2), and Theorem 3.54; `Polyfold.theorem_3_54_two`, `Polyfold.theorem_3_54`,
`Polyfold.theorem_3_54_tangentGermChart_solutionSet`).** Let $f$ be a section of a strong bundle,
$f(x_0) = 0$, $(f, x_0)$ in good position in a tame chart (V3.103). (i) The solution set $S =
\{f = 0\}$ has at $x_0$ data of Definition 3.25 with $\pi(O) \subseteq C$. (ii) If moreover every zero
in an open $V_{x_0} \ni x_0$ is in good position in a tame chart, there are $d \in \mathbb N$ and regular
data (V3.24) of dimension $d$ for $S$ at $x_0$ whose chart domain lies in $V_{x_0}$, and every datum of
Definition 3.25 for $S$ at a point of $S$ in that domain has dimension $d$. (iii) Theorem 3.54, first form:
if $f$ is an sc-Fredholm section with tame germ data and $(f, x_0)$ is in good position with the filler
condition of V3.82 (in a tame chart), there is an open $V_x \ni x_0$ such that every zero in $V_x$ is in
good position in a tame chart, and (ii) holds with $V_{x_0} = V_x$. *Book:* Theorem 3.54 (1), (2), p. 111. *Hidden hypotheses:* tameness as in V3.68. *Deviation
(narrower):* (2) is proved from (1), with the nearby good position as a hypothesis; (1) under
the filler condition of V3.82, which follows from good position (V3.102). With the text's hypotheses:
V3.94; with the dimension as the index and its local constancy: V3.97, V3.98. "$S$ is a sub-M-polyfold with the structure of a manifold with boundary with
corners" follows from (ii) by Theorem 3.27 (V3.69). The regularity conditions (a), (b) of Theorem 3.27,
hypotheses for general sets (V3.24), are theorems for the solution set (V3.74, V3.77).

**V3.86 (Theorem 3.56; `Polyfold.theorem_3_56`, `Polyfold.theorem_3_56_sc`).** Let $X$ be an
M-polyfold with $d_X \equiv 0$, $f$ an sc-Fredholm section of a strong bundle, with $(f, x)$ in good
position in a tame chart (V3.103) at every zero $x$, and $S = \{f = 0\}$ nonempty. Then $S$ is a
sub-M-polyfold of $X$ whose induced structure is equivalent to that of a manifold with boundary with
corners of locally constant dimension and has degeneracy index $0$ at every point (a manifold
without boundary). The same with good position in the text's sense (sc-complement, V3.47) at every
zero, which for an sc-Fredholm section with tame germ data is the same hypothesis
(`theorem_3_56_sc`). *Book:* Theorem 3.56, p. 115 ($f'(x)$ surjective at every zero). *Hidden
hypotheses:* as V3.70. *Deviation (restated):* the hypothesis "$f'(x)$ surjective" is read as good
position, which by the text's Definition 3.53 is surjectivity at points with $d_X(x) = 0$; in the
chart form the kernel condition is stated for the chart's partial quadrant, and that it is void when
$d_X(x) = 0$ is V3.100; the form with "$f'(x)$ surjective" is V3.101. No other hypothesis is added.
The tameness of the induced structure is in V3.87 and V3.101.

**V3.87 (Theorem 3.57; `Polyfold.theorem_3_57`, `Polyfold.theorem_3_57_dim`,
`Polyfold.solutionSetDim`, `Polyfold.theorem_3_57_sc`).** Let $f$ be an sc-Fredholm section of a
strong bundle, with $(f, x)$ in good position in a tame chart (V3.103) at every zero $x$. If
$S = \{f = 0\}$ is nonempty, $S$ is a sub-M-polyfold of $X$, its induced structure is tame and
equivalent to that of a manifold with boundary with corners of locally constant dimension, and at
every $x \in S$ there are regular data of Definition 3.25 of a dimension $d(x)$ such that every
datum at a point of $S$ in their chart domain has dimension $d(x)$. Moreover $S$ is the disjoint
union of the sets $S_n$ of points at which $S$ has data of dimension $n$, each $S_n$ is open and
closed in $S$, and each nonempty $S_n$ is a sub-M-polyfold whose induced structure is tame and
equivalent to that of an $n$-dimensional manifold with boundary with corners. The same with good
position in the text's sense (sc-complement, V3.47) at every zero, which for an sc-Fredholm section
with tame germ data is the same hypothesis (`theorem_3_57_sc`). *Book:* Theorem 3.57, p. 115.
*Hidden hypotheses:* as V3.70. *Deviation (stronger):* **the text's hypotheses**; the local
constancy of the dimension and the parts $S_n$ are not in the text. Two steps of the text's proof
are replaced: the regularity of the solution germ away from the centre (V3.73, V3.74) and the
relative openness of $\Sigma$ (V3.75, V3.77). The dimension $d(x)$ is the Fredholm index of $f'(y)$
at the zeros near $x$ (V3.97).

**V3.88 (Theorem 3.58, given the family of sc-isomorphisms; `Polyfold.theorem_3_58_of_family`,
`Polyfold.DerivCondition`, `Polyfold.contrMap358_contraction`,
`Polyfold.norm_sub_sub_le_of_hasFDerivWithinAt_segment`, `Polyfold.fiberIsoMap_isStrongBundleIso`,
`Polyfold.famInv_isScSmooth_of`).** In the coordinates of the text's proof — $E = \mathbb R^n \oplus X$
($\mathbb R^n$ any finite-dimensional space with a partial quadrant $\widetilde C$), $C = \widetilde C
\oplus X$, $F = \mathbb R^N \oplus Y$ — let $U$ be relatively open in $C$ with $0 \in U$ and $f : U \to
F$ sc-smooth; let $V_o \ni 0$ be open in $\mathbb R^n$ with $(b, 0) \in U$ for $b \in V_o \cap
\widetilde C$, and $L(b) : X \to Y$ sc-isomorphisms with $L(b)h = (Df(b, 0)(0, h))_Y$ on level $0$ and
lower bounds $c_m|h|_m \le |L(b)h|_m$ for $b \in V_o \cap \widetilde C$, $h \in X_m$, every $m$; and let
condition (3) hold (`DerivCondition`: for all $m$ and $\varepsilon > 0$ there is $r > 0$ with $|[D_2f(b, 0) -
D_2f(b, x)]h|_m \le \varepsilon|h|_m$ for $b \in \widetilde C$, $|b| < r$, $x \in X_{m+1}$, $|x|_m < r$,
$(b, 0), (b, x) \in U$, $h \in X_m$). Then on $U' = U \cap (V_o \oplus X)$: $k(b, x) = ((f(b, x) -
f(0))_{\mathbb R^N}, L(b)^{-1}(f(b, x) - f(0))_Y)$ is a basic germ with contraction map $H(b, x) = x -
L(b)^{-1}(f(b, x) - f(0))_Y$; $\Phi((b, x), (c, y)) = ((b, x), (c, L(b)^{-1}y))$ is a strong bundle
isomorphism $U' \triangleleft (\mathbb R^N \oplus Y) \to U' \triangleleft (\mathbb R^N \oplus X)$
covering the identity; and $f - f(0)$ is conjugated to a basic germ. *Book:* the second half of the
proof of Theorem 3.58, pp. 118–120. *Hidden hypotheses:* the mean value inequality along a segment with
the derivative bound in the weaker norm of $X_m$ (the text's integral; Findings, Chapter 3, item 73).
*Deviation (restated):* in the coordinates of the proof; the sc-smoothness of $(b, y) \mapsto
L(b)^{-1}y$ is Lemma 3.61 (V3.54) in set form.

**V3.89 (Theorem 3.58, the basic germ criterion; `Polyfold.theorem_3_58`,
`Polyfold.CompactnessCondition`, `Polyfold.familyCompactness_derivFamOp`,
`Polyfold.fredholmIndex_block`, `Polyfold.surjective_of_fredholmIndex_block`, `Polyfold.derivFamOp`).**
In the coordinates of V3.88, let $U$ be relatively open in $\widetilde C \oplus X$ with $0 \in U$ and $f
: U \to \mathbb R^N \oplus Y$ sc-smooth with: (1) at every $(b, 0) \in U$, $b \in \widetilde C$, $Df(b,
0)$ is sc-Fredholm with the sc-index of $Df(0)$; (2) $h \mapsto (Df(0)(0, h))_Y$ is bijective on level
$0$, and the compactness condition holds (`CompactnessCondition`: there is $r > 0$ such that for every
$m$, if $b_j \to b_0$ in $\widetilde C$ with $(b_j, 0) \in U$ and $|b_0| < r$, $(\eta_j)$ is bounded in
$X_m$ and $Df(b_j, 0)(0, \eta_j) = y_j + z_j$ with $y_j \to 0$ in $F_m$ and $(z_j)$ bounded in
$F_{m+1}$, then $(\eta_j)$ has a convergent subsequence in $X_m$); (3) `DerivCondition` (V3.88). Then
there are an open $V_o \ni 0$ in $\mathbb R^n$ and sc-isomorphisms $L(b) : X \to Y$ with $L(b)h = (Df(b,
0)(0, h))_Y$ for $b \in V_o \cap \widetilde C$, for which the conclusions of V3.88 hold; in particular
$f - f(0)$ is conjugated near $0$ to a basic germ. On the way: Lemmas 3.59, 3.60 for this family, with
their hypotheses derived from (2) (V3.52, V3.53); the index of a block operator, $\mathrm{ind}\,T =
\dim\mathbb R^n + \mathrm{ind}\,L - \dim\mathbb R^N$ for $T : \mathbb R^n \oplus X \to \mathbb R^N
\oplus Y$ Fredholm with block $L$ of finite index, and an injective block is onto when $\mathrm{ind}\,T
= \dim\mathbb R^n - \dim\mathbb R^N$. *Book:* Theorem 3.58, p. 116, proof pp. 116–120. *Hidden
hypotheses:* the smallness of $b$ in (2) uniform in the level $m$. *Deviation (narrower):* in the
coordinates of the proof; the reduction of a general sc-splitting $E = B \oplus X$, $F = A \oplus Y$ to
them is not formalized; (1) is needed only at the points $(b, 0)$; the text's "$B \supseteq \ker Df(0)$
and $Y = Df(0)X$" is replaced by the bijectivity it implies.

**V3.90 (Proposition 3.73 and Lemma 3.77 with the hypotheses their proofs use; `Polyfold.InvDataW`,
`Polyfold.InvDataW.injOn`, `Polyfold.InvDataW.hasFDerivWithinAt_inv`,
`Polyfold.InvDataW.contDiffOn_inv`).** Let $U$ be a convex subset of a finite-dimensional normed space
$V$ with unique differentiability at its points, $f : V \to V$ of class $C^j$ ($j \ge 1$) on $U$ with
$\|Df(x) - 1\| \le \tfrac12$ for $x \in U$, and let $f(U)$ have unique differentiability. Then $f$ is
injective on $U$ ($\tfrac12|x - x'| \le |f(x) - f(x')|$), its inverse $g$ is differentiable within
$f(U)$ with $Dg(y) = [Df(g(y))]^{-1}$, and $g$ is of class $C^j$ on $f(U)$. *Book:* Proposition 3.73, p.
137; Lemma 3.77, p. 140. *Hidden hypotheses:* none. *Deviation (restated):* no partial quadrant; the
hypothesis "$x$ interior iff $f(x)$ interior" of V3.59 is replaced by the unique differentiability of
$f(U)$, which is what the bootstrapping uses; the relative openness of $f(U)$ is not concluded. Used in
the re-centring (V3.73), where $f(U)$ is relatively open in a cone for another reason.

**V3.91 (Theorem 3.18, parametrized perturbations; `Polyfold.theorem_3_18`, `Polyfold.theorem_3_18'`,
`Polyfold.paramSection`, `Polyfold.paramSection_eq_sectionAdd`, `Polyfold.StrongBundle.pullback`,
`Polyfold.StrongBundle.IsScFredholmSection.param`, `Polyfold.StrongBundle.isScPlusSection_paramComb`,
`Polyfold.IsBasicGerm.paramExtend`, `Polyfold.IsConjugateToBasicGerm.paramExtend`, `Polyfold.rnPolyfold`,
`Polyfold.prod_rn_isTame`).** Let $P : Y \to X$ be a strong bundle over an M-polyfold ($X$, $Y$
Hausdorff and paracompact, as throughout), $f$ an sc-Fredholm section (V3.16) and $s_1, \dots, s_n$
sc⁺-sections of $P$ (Definition 2.52). Let $\mathbb R^n$ carry its M-polyfold structure with the constant
sc-structure and the charts $r \mapsto r - r_0$, $\mathbb R^n \times X$ the product M-polyfold, $\pi(r, x)
= x$, and $\pi^*P : \pi^*Y \to \mathbb R^n \times X$ the pull-back strong bundle with the natural structure
of Proposition 2.54 (the atlas of all charts pulled back from charts of $P$ through charts of $\mathbb R^n
\times X$). Then $F(r, x) = f(x) + \sum_i r_is_i(x)$, computed in the fibre $P^{-1}(x)$ and read in the
fibre of $\pi^*Y$ over $(r, x)$, is an sc-Fredholm section of $\pi^*P$. The paracompactness of $\mathbb R^n
\times X$ and of $\pi^*Y$, instance arguments of `theorem_3_18`, is supplied by Theorem 2.16 in
`theorem_3_18'`. On the way: $\tilde f(r, x) = f(x)$ is an sc-Fredholm section of $\pi^*P$ — in the product
chart $(r \mapsto r - r_0) \times \varphi$, centred at $(r_0, x)$, the filling germ is $(a, u) \mapsto
g(u)$ on $\mathbb R^n \times G$ (filler conditions (1)–(3) from those of $g$), the sc⁺-germ
$(a, u) \mapsto t_0(u)$, and the
conjugation is the product of the given one with the identity of $\mathbb R^n$, onto the
$\mathbb R^n$-extension $((a, \lambda), w) \mapsto h(a, w)$ of the basic germ, again a basic germ; $\tilde
s(r, x) = \sum_ir_is_i(x)$ is an sc⁺-section (the product rule with a scalar factor, from Proposition 1.19);
$F = \tilde f + \tilde s$ fibrewise, and Theorem 3.15 (V3.17) applies; $\mathbb R^n \times X$ is tame when $X$
is. *Book:* Theorem 3.18, p. 74 (for a tame strong bundle; "$\tilde f$ ... is a sc-Fredholm section as is
readily verified", p. 73). *Hidden hypotheses:* the translation charts of $\mathbb R^n$ (a chart centred at
$(r_0, x)$ is needed for the germ there), the strong bundle structure of $\pi^*P$, the scalar product rule.
*Deviation (stronger):* tameness is not used, as for Theorem 3.15.

**V3.92 (the linearization of the parametrized section; `Polyfold.linAt_paramSection_zero`,
`Polyfold.linAt_paramSection`, `Polyfold.scDeriv_paramSection`, `Polyfold.PullbackChartData.ofProd`).**
In the setting of V3.91, let $c$ be a strong bundle chart of $P$ compatible with the atlas, with $0$ in its
retract $O$, and consider the product chart of $\pi^*P$ through $(r \mapsto r - r_0) \times c$, with the
retraction $1 \times r$. At its centre: $D(\hat F \circ (1 \times r))(0)(\delta a, \delta u) = D(\hat G
\circ r)(0)\delta u + \sum_i \delta a_i\hat s_i(0)$, $\hat G = \hat f + \sum_i r_{0,i}\hat s_i$; in the chart
form of the linearization (V3.78), on $T_0(\mathbb R^n \times O) \subseteq \mathbb R^n \times T_0O$:
$\mathrm{Lin}_F(0)(\delta a, \delta u) = \mathrm{Lin}_{f + \sum r_{0,i}s_i}(0)\delta u + \sum_i\delta
a_i\hat s_i(0)$; and at $r_0 = 0$: $\mathrm{Lin}_F(0)(\delta r, \xi) = \mathrm{Lin}_f(0)\xi + \sum_i\delta
r_i\hat s_i(0)$. *Book:* after Theorem 3.19, p. 75 ("the linearization of $\tilde f$ at $(0, x_0)$ is
$(h, u) \mapsto f'(x_0)u + \sum h_ie_i$"). *Hidden hypotheses:* none (the formula does not use $F = 0$
at the point). *Deviation (restated):* in the chart form (Definition 3.53 is formalized in charts); at
$(r_0, x)$ with $r_0 \ne 0$ the first term is the linearization of $f + \sum r_{0,i}s_i$; the text's
"sc¹-sections $s_i$" are sc⁺ here, as Theorem 3.18 needs.

**V3.93 (Theorem 3.54 (1), the surjectivity at the nearby zeros, in the chart at $x_0$;
`Polyfold.theorem_3_54_chart_onto`, `Polyfold.StrongRetr.mem_O_of_perturbed_zero`,
`Polyfold.exists_inward_of_isInGoodPosition`, `Polyfold.inward_add_smul`, `Polyfold.exists_curve_of_inward`,
`Polyfold.ShiftedBasicData.exists_radii`, `Polyfold.ShiftedBasicData.perturbContraction`,
`Polyfold.ShiftedBasicData.perturbContraction_isSc1GermWith`, `Polyfold.xiMap`,
`Polyfold.exists_xi_radii_bounds`, `Polyfold.ShiftedBasicData.surjective_DH_and_ker_eq`,
`Polyfold.ShiftedBasicData.exists_perturbed_curve`).** In the data of V3.48 at a zero $x_0$ in good
position — the strong bundle chart centred at $x_0$ with retraction $(r, \rho)$ on $U$ onto $O$, the filling
germ $g$, the conjugation $\Psi$ covering $\psi$ of $g - s$ to a basic germ, $h' + \iota t$ with kernel $K
= \ker D(h' + \iota t)(0)$ in good position, the closed good complement, the $C^1$ map $\sigma$ on $V'$
with its lifts, and an open $N_2 \ni 0$ on which $\psi$ maps the zeros of $g$ in $O$ onto the graph of
$\sigma$ — assume condition (2) of Definition 3.4 on $N_2$ and $K \ne 0$. Then there is an open $N_4
\subseteq N_2$ containing $0$ such that for every zero $z_0 \in O \cap N_4$ of $g$, every level-$1$ point
over $z_0$ and every smooth $k \in F_\infty$, $\rho(z_0)k = Dg(z_0)x$ for some $x \in T_{z_0}O = Dr(z_0)E$.
On the way: (a) a zero of $g + \mu\rho(r(\cdot))k$ at which condition (2) holds lies in $O$; (b) a nonzero
finite-dimensional subspace in good position to the partial quadrant $C_z$ at $z \in C$ contains a vector
$v$ with $z + t(v + \zeta) \in C$ for $t \in [0, t_0]$, $|\zeta| < \eta$, and such inward vectors stay
inward after adding any vector and rescaling; (c) for $\widetilde C$ convex and $H$ of class $C^1$ on
$\Omega \cap (\mathbb R \times \widetilde C)$ with $H(0, a_0) = 0$, $D_aH(0, a_0)$ onto and an inward
$\alpha_0$ with $DH(0, a_0)(1, \alpha_0) = 0$, there is a curve $a(\mu)$, $0 \le \mu < \mu_0$, $a(0) =
a_0$, with right derivative $\alpha_0$ at $0$ and $H(\mu, a(\mu)) = 0$; (d) for the normal form of Theorem
3.38 (a basic germ $(G_1, w - B)$ on the shifted structure) there are $\tfrac14$-contraction regions of $B$
below any prescribed radii, and $B - \mu P\hat e$ is a contraction germ in the working form on $(-\mu_m,
\mu_m) \times \{|a| < \nu_m\}$ with the same regions in $a$ for every perturbation $\hat e$ with given
bounds, its solution germ sc¹ (Theorem 3.30); (e) the push-forward $\hat e_k = \Xi(\cdot, k)$ of $u \mapsto
\rho(r(u))k$ to the normal form, with $\Xi$ sc-smooth into the index-raised target and linear in $k$, is
bounded with its Lipschitz constant on the contraction regions by $c_m = 2|k|_{m+2}(M_m + 1)/\delta_m$,
$\delta_m$, $M_m$ independent of $k$; (f) at a zero $(a_0, w_0)$ of the normal form with $|a_0| < \nu_3$,
$|w_0|_1 < \rho_0$ and a kernel of dimension $n - N$, $D_aH(0, a_0)$ is onto for $H$ the
$\mathbb R^N$-component of $(G + \mu\hat e)(a, \delta_\mu(\mu, a))$, the kernel is the graph of $D_a\delta_\mu(0,
a_0)$ over $\ker D_aH(0, a_0)$, and there is a curve of zeros of $G + \mu\hat e$ through it, right
differentiable at $0$ into level $2$. *Book:* the proof of Theorem 3.54, property (4), p. 114 (from
Corollary 3.41 and Lemma 3.55). *Hidden hypotheses:* none added. *Deviation (not in the book):* a new
argument (Findings, Chapter 3, items 180–187): the text's argument gives the surjectivity of the filled
$Dg(z_0)$ only (V3.82). The neighbourhood $N_4$ is determined by $g$, $r$, $\rho$, $\Psi$ and the normal form,
not by $k$; Corollary 3.39 is not used. In the germ reading the curve of zeros lies in the germ of the
filling, so $g$ is differentiated within its germ (Findings, Chapter 3, items 276–278, 298).

**V3.94 (Theorem 3.54 (1), and Theorem 3.54, with the text's hypotheses;
`Polyfold.theorem_3_54_one'`, `Polyfold.theorem_3_54'`, `Polyfold.theorem_3_54_one_sc_of_tame`,
`Polyfold.theorem_3_54_one_sc`, `Polyfold.theorem_3_54_sc`).** Let $f$ be an sc-Fredholm section of
a strong bundle with tame germ data (V3.103), $f(x_0) = 0$, and $(f, x_0)$ in good position in a
tame chart (V3.47, V3.103). Then there is an open $V_x \ni x_0$ such that $(f, y)$ is in good
position in a tame chart at every zero $y \in V_x$; in particular $f'(y)$ is onto
(`theorem_3_54_one'`). Moreover (`theorem_3_54'`) there are $d \in \mathbb N$ and regular data of
Definition 3.25 (V3.24) of dimension $d$ for $S = \{f = 0\}$ at $x_0$ whose chart domain lies in
$V_x$, and every datum of Definition 3.25 for $S$ at a point of $S$ in that domain has dimension
$d$. With the text's notion of good position (sc-complement, V3.47) in the conclusion, from either
form at $x_0$: every zero $y \in V_x$ is in good position with an sc-complement. *Book:* Theorem
3.54 (1), (2), p. 111. *Hidden hypotheses:* tameness as in V3.68. *Deviation (restated):* no
hypothesis added; (2) as regular tangent germ data with locally constant dimension (the manifold
structure of the local solution set is V3.95); the proof of the surjectivity in (1) is V3.93,
through Definition 3.53 from a chart not centred at $y$ (V3.79), read in the tame chart of the germ
data at $y$ (V3.107); for $\dim K = 0$ the only zero near $x_0$ is $x_0$. The project's good
position asks only for an algebraic good complement (V3.20), less than the text's as a conclusion;
the sc form follows at each zero (Findings, Chapter 3, items 210, 213).

**V3.95 (Theorems 3.23 and 3.19 with the text's hypotheses; `Polyfold.theorem_3_23'`,
`Polyfold.theorem_3_19'`, `Polyfold.theorem_3_23_sc`).** Let $f$ be an sc-Fredholm section of a
strong bundle with tame germ data (V3.103), $f(x) = 0$ and $(f, x)$ in good position in a tame
chart. Then there are an open $U \ni x$ and $d \in \mathbb N$ such that every zero in $U$ is in good
position in a tame chart and a smooth point, and $S(f, U) = \{y \in U \mid f(y) = 0\}$ is a
sub-M-polyfold whose induced structure is tame and equivalent to that of a $d$-dimensional manifold
with boundary with corners (`theorem_3_23'`). If moreover $d_X \equiv 0$, the induced structure also
has degeneracy index $0$ everywhere (`theorem_3_19'`). Theorem 3.23 with the text's notion of good
position (sc-complement, V3.47) at $x$ and at every zero in $U$: `theorem_3_23_sc`. *Book:* Theorem
3.23, p. 77; Theorem 3.19, p. 74. *Hidden hypotheses:* tameness as in V3.68. *Deviation (hypotheses
explicit):* no hypothesis added. For Theorem 3.19 the hypothesis "$f'(x_0)$ surjective" is read as
good position, the same at $d_X = 0$ (V3.100, V3.101); "the dimension agrees with the Fredholm
index" is V3.97, "$\ker f'(y) = T_yS$" V3.99; "uniquely determined" is the equivalence of atlases.

**V3.96 (the index of the linearization at a zero, in every chart;
`Polyfold.StrongBundle.IsSurjLinOfIndex`, `Polyfold.StrongBundle.linAt_index_of_conjugationData`,
`Polyfold.StrongBundle.isSurjLinOfIndex_of_conjugationData`,
`Polyfold.StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex`,
`Polyfold.theorem_3_19_linearization_index`, `Polyfold.StrongBundle.linAt_isScFredholm`,
`Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex`,
`Polyfold.proposition_3_52_sc`, `Polyfold.theorem_3_19_linearization_sc`).** `IsSurjLinOfIndex f y d`: in every strong bundle chart
compatible with the atlas whose domain contains $y$, at the level-$1$ point $z$ over $\varphi(y)$,
the linearization $\mathrm{Lin}(z) : T_zO \to K_z$ (V3.78) is surjective and Fredholm with
$\mathrm{ind}\,\mathrm{Lin}(z) = \dim\ker\mathrm{Lin}(z) = d$. Theorem: let $f$ be an sc-smooth
section, $x_0$ a zero, $c$ the strong bundle chart of Definition 3.11 centred at $x_0$ with filling
germ $g$, sc⁺-germ $s$, $s(0) = g(0)$, and conjugation data of $g - s$ to a basic germ
$h : O(\widetilde C \oplus W, 0) \to \mathbb R^N \oplus W$, $\widetilde C \subseteq \mathbb R^n$.
Then in every strong bundle chart around $x_0$ the linearization at the point over $x_0$ is Fredholm
of index $n - N$, and it is onto if the germ is in good position in $c$. Hence at a zero in good
position `IsSurjLinOfIndex f x_0 d` holds with $d = n - N$ for every conjugation in the chart of
Definition 3.53. For an sc-Fredholm section and a zero $x_0$ in good position, in the chart of
Definition 3.53, $Dg(0)$ and $Tf(x_0) = Dg(0)|_{T_0O}$ are Fredholm, $Tf(x_0)$ is onto, and for
every conjugation $\mathrm{ind}\,Dg(0) = \mathrm{ind}\,Tf(x_0) = \dim\ker Tf(x_0) = n - N$. In sc
form: for an sc-Fredholm section, a zero $y$ and any strong bundle chart around $y$, at the point
$z$ over $\varphi(y)$ (a smooth point), $T_zO = Dr(z)E$ and $K_z = \rho(z)F$ are sc-subspaces and
$\mathrm{Lin}(z) : T_zO \to K_z$ is an sc-Fredholm operator of index $n - N$ on every level; under
`IsSurjLinOfIndex f y d` it is onto on every level, of index $d$ on every level; in the chart of
Definition 3.53, $Dg(0)$ and $f'(x_0)$ are sc-Fredholm and $f'(x_0)$ is onto on every level. *Book:*
Proposition 3.52, p. 110, and the first clause of Theorem 3.19, p. 74. *Hidden hypotheses:* none.
*Deviation (stronger):* in charts ($T_xX$ carries no linear structure here, Chapter 2); in every chart
by the chart independence at zeros (V3.78), which the text does not state, realised on all levels by
the chart change at smooth points (Findings, Chapter 3, items 236, 239); the index on every level,
and the surjectivity on every level at a zero in good position, go beyond the text's statement. The
hypothesis is the text's since the switch to the germ reading (phase 2): Proposition 3.52 enters at
the centre of the chart of the germ datum, where $\mathrm{Lin}(0) = Dg(0)$ on $T_0O$ for the filling
germ (Findings, Chapter 3, items 284, 310, 314, 330). `theorem_3_19_linearization_sc` gives the conclusions in the chart at $x_0$, and
`linAt_isScFredholm_of_isSurjLinOfIndex` with `IsGoodPositionGerm.exists_isSurjLinOfIndex` in every
chart. The sc-Fredholm property was first
proved on level $0$ only; formerly "narrower", for the whole-chart hypothesis.

**V3.97 (the dimension of the solution set is the Fredholm index;
`Polyfold.theorem_3_54_tangentGermChart_index`, `Polyfold.theorem_3_54_two_index`,
`Polyfold.theorem_3_23_index`, `Polyfold.theorem_3_19_index`, `Polyfold.theorem_3_57_index`,
`Polyfold.theorem_3_54_graph_proj_conj`, `Polyfold.theorem_3_54_tangentGermChart_proj_conj`,
`Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex`).** Let $f$ be an sc-smooth section
of a strong bundle, $f(x_0) = 0$, $(f, x_0)$ in good position in a tame chart (V3.103). (i) The data
of Definition 3.25 at $x_0$ of V3.84 have a dimension $d$ with `IsSurjLinOfIndex f x_0 d` (V3.96):
$d = n - N$ for the conjugation in the chart from which $\psi\varphi$ is built. (ii) The regular
data of V3.85 (ii) have such a dimension. (iii) For $f$ sc-Fredholm with tame germ data there are an
open $U \ni x_0$ and $d$ such that every zero $y \in U$ is in good position in a tame chart with
`IsSurjLinOfIndex f y d`, the zeros in $U$ are smooth points, and $S(f, U)$ is a sub-M-polyfold
whose induced structure is tame and equivalent to that of a $d$-dimensional manifold with boundary
with corners (`theorem_3_23_index`); if $d_X \equiv 0$, also of degeneracy index $0$ everywhere
(`theorem_3_19_index`). (iv) Under the hypotheses of V3.87 (good position in a tame chart at every
zero, $S \ne \emptyset$): $S$ is a sub-M-polyfold with tame induced structure, a manifold with
boundary with corners of locally constant dimension, and at every $x \in S$ there are regular data
of a dimension $d$ such that every datum at a point of $S$ in their chart domain has dimension $d$
and `IsSurjLinOfIndex f y d` holds at every zero $y$ of that domain (`theorem_3_57_index`). For an
sc-Fredholm section, at a zero with `IsSurjLinOfIndex f y d`, $\mathrm{Lin}(z)$ is moreover
sc-Fredholm and onto on every level, of index $d$ on every level, in every chart (V3.96). *Book:*
Theorem 3.19, p. 74 ("whose dimension agrees with the Fredholm index"); the proof of Theorem 3.54,
p. 115 ($d = \dim\ker f'(x)$). *Hidden hypotheses:* tameness as in V3.68. *Deviation (stronger):*
the index at every zero near the point and in every chart; the text states no dimension in Theorems
3.23, 3.57.

**V3.98 (the Fredholm index along the solution set and along paths, Definition 6.1, Proposition
6.2; `Polyfold.theorem_3_54_index_locally_constant`, `Polyfold.theorem_3_54_index`,
`Polyfold.isSurjLinOfIndex_of_forall_dim`, `Polyfold.theorem_3_54_index_locally_constant_sc`,
`Polyfold.StrongBundle.linAt_isScFredholm`, `Polyfold.index_locally_constant_tame`,
`Polyfold.theorem_3_54_index_locally_constant_general_tame`,
`Polyfold.index_locally_constant_of_admitsBumpFunctions`,
`Polyfold.theorem_3_54_index_locally_constant_general`, `Polyfold.StrongBundle.IsLinOfIndex`,
`Polyfold.StrongBundle.restrictOpen`, `Polyfold.StrongBundle.IsIndexAtLocal`,
`Polyfold.StrongBundle.IsIndexAtLocal.unique`, `Polyfold.StrongBundle.exists_isIndexAtLocal`,
`Polyfold.StrongBundle.IsIndexAt`, `Polyfold.StrongBundle.IsIndexAt.unique`,
`Polyfold.StrongBundle.exists_isIndexAt`, `Polyfold.StrongBundle.isIndexAtLocal_iff_isIndexAt`,
`Polyfold.exists_isScPlusSection_pullback_of_path`,
`Polyfold.StrongBundle.isIndexAt_of_pullback_isLinOfIndex`, `Polyfold.proposition_6_2_local`,
`Polyfold.proposition_6_2_local'`, `Polyfold.proposition_6_2`).** Let $f$ be an sc-Fredholm section
of a strong bundle with tame germ data (V3.103), $f(x_0) = 0$, $(f, x_0)$ in good position in a tame
chart. Then there are an open $V_x \ni x_0$ and $d$ such that `IsSurjLinOfIndex f y d` holds at every
zero $y \in V_x$: $f'(y)$ is onto with $\mathrm{ind}\,f'(y) = \dim\ker f'(y) = d = \mathrm{ind}\,f'(x_0)$
(`theorem_3_54_index_locally_constant`). Theorem 3.54 with the index (`theorem_3_54_index`):
moreover every zero in $V_x$ is in good position in a tame chart, and $S$ has at $x_0$ regular data
of dimension $d$ whose chart domain is $V_x$, every datum at a point of $S$ in $V_x$ having
dimension $d$. On the way: at a zero in good position in a tame chart at which every datum of
Definition 3.25 for $S$ has dimension $d$, `IsSurjLinOfIndex f y d` ($f$ sc-smooth). In sc form, at
every zero in $V_x$ and in every chart, $\mathrm{Lin}(z)$ is sc-Fredholm, onto on every level, of
index $d$ on every level (`theorem_3_54_index_locally_constant_sc`); at any zero of an sc-Fredholm
section, in every chart, $\mathrm{Lin}(z)$ is sc-Fredholm with the same index on every level
(`linAt_isScFredholm`). Without good position, with the text's hypotheses: if $f$ is an sc-Fredholm
section with tame germ data and $f(x_0) = 0$, there are an open $V \ni x_0$ and $i \in \mathbb Z$ such
that at every zero $y \in V$, in every strong bundle chart, $f'(y)$ is Fredholm of index $i$
(`IsLinOfIndex f y i`; `index_locally_constant_tame`) and $\mathrm{Lin}(z)$ is sc-Fredholm of index
$i$ on every level (`theorem_3_54_index_locally_constant_general_tame`); no bump functions are
assumed (the first forms, for $X$ admitting sc-smooth bump functions, Definition 5.9:
`index_locally_constant_of_admitsBumpFunctions`, `theorem_3_54_index_locally_constant_general`).
**Definition 6.1**, with the text's locally defined section: an sc-Fredholm section $f$ has index $i$
at a smooth point $x$ (`IsIndexAtLocal f x i`) if for some open $V \ni x$ and some sc⁺-section $s$ of
the restriction $P|V$ of $P$ to $V$ (`StrongBundle.restrictOpen`: the strong bundle over the
M-polyfold $V$ whose atlas consists of the charts of $P$ with base domain inside $V$),
$(f|_V + s)(x) = 0$ and $(f|_V + s)'(x)$ is Fredholm of index $i$ in every strong bundle chart of
$P|V$; the index is unique, at a zero it is the index of $f'(x)$, and it exists at every smooth point.
With an sc⁺-section on all of $X$ in place of $s$ (`IsIndexAt f x i`) the index is unique as well and
implies the local one; if $X$ admits sc-smooth bump functions it exists at every smooth point and the
two readings agree (`isIndexAtLocal_iff_isIndexAt`). **Proposition 6.2**: if $f$ is an sc-Fredholm
section with tame germ data, then for every sc-smooth path $\varphi : \mathbb R \to X$ the index
$\mathrm{ind}(f, \varphi(t))$ (local reading) is the same for all $t$ (`proposition_6_2_local`), and
any two values of the index at $\varphi(0)$ and $\varphi(1)$ agree (`proposition_6_2_local'`); if $X$
admits sc-smooth bump functions, the same holds for the global reading (`proposition_6_2`). *Book:*
Definition 6.1, pp. 200–201; Proposition 6.2, p. 201 (over a tame M-polyfold, the index is constant
along sc-smooth paths $[0, 1] \to X$ of smooth points; the proof: "we do not need a sc-smooth
partition of unity", p. 202), whose proof uses the step of V3.82; in Chapter 3 the statement along
the solution set is implicit in Theorem 3.54 (1). *Hidden hypotheses:* tameness as in V3.68; for
Definition 6.1, the text's local sc⁺-section $s$ with $s(x) = f(x)$ is a section of the restriction of
the bundle to an open neighbourhood of $x$ ($-s$ here), a construction the text uses without comment.
*Deviation (narrower):* the path is defined on $\mathbb R$, not on $[0, 1]$ ($\mathbb R \times X$ is
the product of Theorem 3.18 and has no boundary, and the text's tame M-polyfold $[0, 1] \times X$ is
not used): a path on $[0, 1]$ that extends sc-smoothly to $\mathbb R$ is covered, a path sc-smooth on
$[0, 1]$ only is not, and the project has no M-polyfold $[0, 1]$. This is the only narrowing left;
the hypotheses on $f$ are the text's, in the reading of tameness of V3.103 (as in V3.94), and no bump
functions are assumed. *Proof:* Proposition 6.2 is proved by the text's device, run on the
restriction $P|V$ to the domain $V$ of a chart around $\varphi(t_0)$, where the text's sections need
no cut-off — for each $t_0$ an sc⁺-section $S$ of the pull-back to $\mathbb R \times V$ with
$\tilde f + S = 0$ along the graph of the path near $t_0$ (the text's $R(x, f(\varphi(t)))$ in the
chart), the local constancy of the index of $\tilde f + S$ along its zero set, the count
$\mathrm{ind}(\tilde f + S)'(t, x) = \mathrm{ind}(f, x) + 1$ through the slice $S(t, \cdot)$, and the
connectedness of $\mathbb R$; the earlier form for M-polyfolds with bump functions cuts the sections
off instead (Findings, Chapter 3, items 340–349, 360–367). The local constancy along the zero set
without good position is the same device: sc⁺-sections $R(\cdot, e_i)$ on $P|V$ put the parametrized
section of Theorem 3.18 into general position at $(0, x_0)$, its index is constant along its solution
set, at $(0, y)$ it is $k + \mathrm{ind}\,f'(y)$, and the index at a zero is the same for $P$ and
$P|V$, through the germ datum (items 240–242, 360–363). Definition 6.1 is well defined because two
local sections are compared on the intersection of their domains; its independence of $s$ is proved
from the germ data and Theorem 3.15, not by the text's appeal to Proposition 1.10; and it exists at
every smooth point through the section $-R(\cdot, f(x))$ on a chart domain (items 340, 364). Under
bump functions a local section is cut off to a global one with the same index (item 367). The
candidate counterexample of items 188 and 243 is excluded by Theorem 3.54 (1). Without tame germ data
the local constancy is open: it amounts to the index $0$ of the block
$(1 - \rho(z))Dg(z)|_{\ker Dr(z)}$ of the filling at the nearby zeros, which condition (3) of
Definition 3.4 gives at $z = 0$ only (items 243, 343).

**V3.99 ($\ker f'(y) = T_yS$ in a chart; `Polyfold.theorem_3_54_ker_eq_tangent`).** Let $f$ be an
sc-smooth section of a strong bundle, $f(x_0) = 0$, $(f, x_0)$ in good position in a tame chart (V3.103).
Then there are a tame strong bundle chart $c$ centred at $x_0$ (as in Definition 3.53), the
conjugating sc-diffeomorphism $\psi : U \to U' \subseteq C'$ (inverse $\psi'$, $\psi(0) = 0$), the
finite-dimensional $K = \ker D(h + t)(0)$, the solution graph $\sigma : V' \to E'$ over a relatively open
$V' \ni 0$ of $K \cap C'$ ($C^1$, $\sigma(0) = 0$, $D\sigma(0) = 0$), an open $V_x \ni x_0$ with
$\psi\varphi(\{y \in V_x \mid f(y) = 0\}) = \{v + \sigma(v) \mid v \in V'\}$, and an open $V_{x,2} \subseteq V_x$
containing $x_0$, such that for every zero $y \in V_{x,2}$, with $\psi(\varphi(y)) = v + \sigma(v)$, $v \in
V'$, and every level-$1$ point $z$ over $\varphi(y)$: $D\psi(z)$ maps the kernel of $\mathrm{Lin}(z) : T_zO \to
K_z$ onto $N_v = \{n + D\sigma(v)n \mid n \in K\}$, the tangent space at $v$ of the graph. *Book:* Theorem
3.19, p. 74 ("$\ker f'(y) = T_yS(f, U)$ is the tangent space"). *Hidden hypotheses:* tameness as in V3.68.
*Deviation (restated):* in the chart $\psi\varphi$ of the tangent germ data, the kernel of the linearization
in the chart $c$; $T_yS$ as a subspace of $T_yX$ is not formalized (Chapter 2, gap G.13).

**V3.100 (good position is surjectivity at a zero with $d_X = 0$; `Polyfold.StrongBundle.IsLinSurjAt`,
`Polyfold.isInGoodPositionIn_of_subset`,
`Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero`,
`Polyfold.StrongBundle.isGoodPositionGerm_of_isLinSurjAt`, `Polyfold.StrongBundle.IsGoodPositionGerm.isLinSurjAt`,
`Polyfold.StrongBundle.isGoodPositionGerm_iff_isLinSurjAt`, `Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective`).**
`IsLinSurjAt f y` ("$f'(y)$ is surjective"): in some strong bundle chart compatible with the atlas whose
domain contains $y$, at a level-$1$ point $z$ over $\varphi(y)$, $\mathrm{Lin}(z)$ maps onto the fibre $K_z =
\{k \mid (\varphi(y), k) \in K\}$; then, at a zero, it does so in every such chart and at every level-$1$
point over $\varphi(y)$ (V3.78). Let $f$ be an sc-Fredholm section of a strong bundle with tame germ data
(V3.103) and $y$ a zero with $d_X(y) = 0$. Then $(f, y)$ is in good position in a tame chart if and only if
`IsLinSurjAt f y`. On the way: a subspace $N \subseteq T$ is in good position inside $T$ to every cone
containing $T$; in a chart with tame base retraction around a zero $y$ with $d_X(y) = 0$ at which $(f, y)$
is an sc-Fredholm germ, if the linearization is onto there, $(f, y)$ is in good position, since
$d_C(\varphi(y)) = d_X(y) = 0$ makes the partial quadrant at $\varphi(y)$ the whole space; the surjectivity
is carried to the tame chart of the germ data at $y$, and the good position read there (V3.107). *Book:* the remark after Theorem 3.54, p. 111 (for $\partial X = \emptyset$
good position just means surjectivity), and Corollary 3.24 ("an empty condition if $d_X(x) = 0$", p. 79).
*Hidden hypotheses:* the chart is tame, for $d_C = d_X$ (in a non-tame chart $d_C(\varphi(y))$ can exceed
$d_X(y)$). *Deviation (hypotheses explicit).*

**V3.101 (Theorems 3.19 and 3.56 with "$f'(x)$ surjective", and Theorem 3.56 with tameness;
`Polyfold.theorem_3_19_of_surjective`, `Polyfold.theorem_3_56_of_surjective`,
`Polyfold.theorem_3_56_tame`).** Let $X$ be an M-polyfold with $d_X \equiv 0$ and $f$ an sc-Fredholm section
of a strong bundle. (i) If $f$ has tame germ data (V3.103), $f(x_0) = 0$ and `IsLinSurjAt f x_0`
(V3.100), the conclusions of `theorem_3_19_index` hold (V3.97 (iii)): an open $U \ni x_0$ and $d$ with every
zero $y \in U$ in good position in a tame chart, `IsSurjLinOfIndex f y d`, the zeros in $U$ smooth, and
$S(f, U)$ a sub-M-polyfold whose induced structure is tame, a $d$-dimensional manifold with degeneracy
index $0$ everywhere. (ii) If $(f, x)$ is in good position in a tame chart at every zero
(`theorem_3_56_tame`), or $f$ has tame germ data and `IsLinSurjAt f x` at every zero
(`theorem_3_56_of_surjective`), and $S \ne \emptyset$, then $S$ is a sub-M-polyfold whose induced structure is tame, a manifold of locally constant
dimension with degeneracy index $0$ everywhere, with regular data of Definition 3.25 at every zero of a
dimension $d$ constant near it and equal to the Fredholm index at the zeros of the chart domain. *Book:*
Theorem 3.19, p. 74; Theorem 3.56, p. 115.
*Hidden hypotheses:* tameness as in V3.68; $S \ne \emptyset$ as in V3.70. *Deviation (stronger):* the text's
hypotheses; the tameness of the induced structure and the index are added conclusions.

**V3.102 (the filler condition at the nearby zeros follows from good position;
`Polyfold.normal_injective_of_exists_range_deriv_eq_ρ_germ`,
`Polyfold.exists_range_deriv_eq_ρ_iff_normal_injective_germ`,
`Polyfold.isGoodPositionGermFilled_of_isGoodPositionGerm`).** (a) Let $U$ be relatively open in a partial
quadrant, $R$ a strong bundle retraction on $U \triangleleft F$, $g$ an sc¹-germ with derivative family
$Dg$, and $z$ a level-$1$ point in its germ
over a point $z_0$ of the retract $O$ with $\ker Dg(z) \subseteq T_{z_0}O$. If for every $k \in F$ there is
$x \in T_{z_0}O$ with $Dg(z)x = \rho(z_0)k$, then $Dr(z)b = 0$ and $\rho(z_0)Dg(z)b = Dg(z)b$ imply $b = 0$:
condition (3) of Definition 3.4 at $z_0$. (b) If moreover $\mathbf f \circ r$ is sc¹, $\mathbf f$
is a section of $K$ on $O$ with $\mathbf f(z_0) = 0$, $\mathbf f = g$ on $O$ near $z_0$, and $Dg(z)$ is
onto, the two conditions are equivalent. (c) For an sc-Fredholm section with tame germ data (V3.103) and a
zero $x_0$ in good position in a tame chart, $(f, x_0)$ is in good position in a tame chart with the filler
condition at the nearby zeros (`IsGoodPositionGermFilled`, V3.82). *Book:* not in the text
(Definition 3.4 (3), p. 64, at $0$ only). *Hidden hypotheses:* none. *Deviation (not in the book):* (c)
uses V3.94 and the tangency $\ker Dg(z_0) \subseteq T_{z_0}O$ of V3.81; it shows that the added hypothesis
of V3.68, V3.69, V3.82, V3.85 is satisfied whenever the text's hypotheses are.

**V3.103 (Definitions 3.50, 3.51 and 3.53 in a tame chart; `Polyfold.StrongBundle.IsTameChart`,
`Polyfold.StrongBundle.IsScFredholmGermTame`, `Polyfold.StrongBundle.IsGoodPositionGermTame`,
`Polyfold.StrongBundle.IsScFredholmSectionTame`,
`Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm`,
`Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm`,
`Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame`,
`Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame`,
`Polyfold.StrongBundle.isTameChart_of_eqOn_id`, `Polyfold.ScRetraction.IsTame.congr`,
`Polyfold.IsFillingGerm.nonempty_kerEquiv`, `Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart`).** A strong
bundle chart of $P$ is *tame* (`IsTameChart`) if it is compatible with the atlas and its base
retraction $r : U \to U$ is tame (Definition 2.34). `IsScFredholmGermTame f x` (Definition 3.50,
"tame germ data at $x$"): $x$ is a smooth point and there are the data of Definition 3.11 (V3.13: a
strong bundle chart centred at $x$, a filling germ $g$ of the principal part, a local sc⁺-germ $s$
with $s(0) = g(0)$, and $g - s$ conjugated near $0$ to a basic germ; the text's germ reading) in a
tame chart.
`IsGoodPositionGermTame f x` ("good position in a tame chart"): the same data with the germ in good
position in that chart (Definition 3.53 in the chart form of V3.47). `IsScFredholmSectionTame f`
(Definition 3.51, "tame germ data"): $f$ is an sc-Fredholm section (V3.16) with tame germ data at
every smooth point. Each of these implies the form without tameness (V3.13, V3.47), good position in
a tame chart gives tame germ data, and the strengthened good position of V3.82 is stated in a tame
chart and implies good position in it. A retraction agreeing on its domain with a tame retraction is
tame; hence a compatible chart whose base retraction is the identity of $U$ (the retract $O = U$
relatively open in the partial quadrant) is tame, so the hypotheses can be met. *Book:* Definition
3.50, p. 110 (a strong bundle chart around $x$ "where $K \to O$ is a tame strong local bundle", as
in Definition 3.6, p. 66); Definition 3.51, p. 110, and Definition 3.53, p. 111 (for a tame strong
bundle); a strong bundle retraction is tame when its $r$ is (p. 49); the proof of Proposition 3.52
starts from "a tame strong bundle chart" (p. 110). *Hidden hypotheses:* none. *Deviation
(hypotheses explicit):* these are the hypotheses of the implicit function theorems of §3.6 (V3.48, V3.68–V3.70,
V3.80–V3.82, V3.84–V3.87, V3.94–V3.102), in place of the reading of "tame strong bundle" as the
tameness of the base retraction of every compatible chart, under which they were first proved and
which cannot be met (V3.104). Whether germ data in some chart (V3.13) can be moved to some
compatible tame chart when the atlas consists of tame charts is open; it cannot be done by
re-centring a chart of the tame atlas, since whether a filling exists in a chart depends on the
chart: the trivial bundle with a one-chart tame atlas has sc-Fredholm sections with tame germ data
in compatible charts and no germ data in the chart of the atlas (Findings, Chapter 3, items 350–353).
The text builds the tame chart into Definition 3.50, and so do the theorems. Since the switch to the text's germ reading (phase 2) the three
notions carry the text's germ data (V3.13, V3.45); the earlier whole-chart forms are
`IsScFredholmGermTameWholeChart`, `IsGoodPositionGermTameWholeChart`,
`IsScFredholmSectionTameWholeChart`, and the non-vacuity witnesses satisfy both readings (Findings,
Chapter 3, items 220–221, 304, 330). For Definition 3.53 the comparison is that of V3.47. Formerly
"restated", for the whole-chart reading (round-trip item V3.103).

**V3.104 (a retraction onto a product with a point that is not tame: the earlier tameness hypothesis is
unsatisfiable; `Polyfold.ScRetraction.halfLineConst_prod_not_isTame`, `Polyfold.ScRetraction.halfLineConst`,
`Polyfold.ScRetraction.halfLineConst_retract`, `Polyfold.halfLineSc`).** Let $W$ be an sc-Banach space and
$c$ the constant retraction $(a, w) \mapsto (1, 0)$ of the partial quadrant $[0, \infty) \oplus W$ of
$\mathbb R \oplus W$ (sc-smooth, $(1, 0)$ being a smooth point), with retract $\{(1, 0)\}$. For every
sc-smooth retraction $r$ of a nonempty relatively open subset $U$ of a partial quadrant $C$, the product
retraction $c \times r$ of $([0, \infty) \oplus W) \times U$, whose retract is $\{(1, 0)\} \times r(U)$, is
not tame: at $((0, 0), u)$ with $u \in r(U)$ the degeneracy index is $1 + d_C(u)$, at its image $((1, 0),
u)$ it is $d_C(u)$, against condition (1) of Definition 2.34. *Book:* not in the text (Definition 2.34,
pp. 39–40; Definition 2.50, pp. 51–52). *Hidden hypotheses:* none. *Deviation (not in the book):* the
retraction-level half of the argument (Findings, Chapter 3, item 190) that the hypothesis under which
the theorems of §3.6 were first proved, "the base retraction of every strong bundle chart compatible with
the atlas is tame", fails for every strong bundle over a nonempty base: from a compatible chart $(\varphi,
U, R, \Phi)$, the chart $(1, \varphi)$ onto $\{1\} \times O$ with base retraction $(a, u) \mapsto (1, r(u))$
on $[0, \infty) \times U$ (the retraction above, with $W = 0$) has the transition maps of the first chart
composed with affine maps, hence is compatible with every chart the first one is. That chart and its
compatibility are not formalized (see "What is not verified"); so the earlier statements, vacuous by this
argument, are replaced by those with tame germ data (V3.103).

**V3.105 (Theorem 3.15 for tame germ data; `Polyfold.theorem_3_15_tame`,
`Polyfold.StrongBundle.IsScFredholmGermTame.sectionAdd`).** If $f$ is an sc-Fredholm section with tame germ
data (V3.103) and $s$ an sc⁺-section, then $f + s$ is an sc-Fredholm section with tame germ data: at every
smooth point the germ data of $f + s$ are taken in the tame chart of those of $f$ (filling germ $g + \hat
s \circ r$, sc⁺-germ $\hat s_1 \circ r + t_0$, the same conjugation, as in V3.17). *Book:* Theorem 3.15,
p. 71, recalled after Definition 3.51, p. 110, for the tame strong bundle of §3.6. *Hidden hypotheses:* none. *Deviation (hypotheses explicit):* Theorem 3.15 for the
tame reading of Definitions 3.50, 3.51; the proof of V3.17 does not change the chart.

**V3.106 (Theorem 3.18 for tame germ data; `Polyfold.theorem_3_18_tame`,
`Polyfold.PullbackChartData.ofProd_isTame`, `Polyfold.StrongBundle.IsScFredholmGermTame.param`,
`Polyfold.StrongBundle.IsScFredholmSectionTame.param`).** In the setting of V3.91, if $f$ is an
sc-Fredholm section with tame germ data (V3.103) and $s_1, \dots, s_n$ are sc⁺-sections, then $F(r, x) =
f(x) + \sum_i r_is_i(x)$ is an sc-Fredholm section of $\pi^*P$ with tame germ data. On the way: the product
chart $(r \mapsto r - r_0) \times c$ of a strong bundle chart $c$ of $P$ (V3.92) has the base retraction $1
\times r$ on $\mathbb R^n \times U$, which is tame when $r$ is ($\mathbb R^n$ carries the identity
retraction of the whole space, so $d(a, u) = d_C(u)$, and the minimal subspaces and tangent spaces are
products); so $\tilde f(r, x) = f(x)$ has germ data at every smooth $(r_0, x)$ in the tame product chart,
and V3.105 adds $\tilde s$. *Book:* Theorem 3.18, p. 74 (for a tame strong bundle). *Hidden hypotheses:*
none. *Deviation (hypotheses explicit):* the tame form of V3.91, which is what the implicit function
theorems of §3.6 need when applied to $F$; the tameness of the base $\mathbb R^n \times X$
(`prod_rn_isTame`, V3.91) is a different statement.

**V3.107 (good position in any chart of the germ data;
`Polyfold.StrongBundle.isGoodPositionAtGerm_of_chart`,
`Polyfold.StrongBundle.isGoodPositionAtGerm_of_chart_dense`,
`Polyfold.StrongBundle.IsGoodPositionGerm.toTame`).** (a) Let $f$ be an sc-smooth section, $y$ a zero,
$c$ a strong bundle chart of $P$ around $y$ (not necessarily centred), $z$ a level-$1$ point over
$\varphi(y)$, and $g$ an sc¹-germ agreeing with $\mathbf f$ on $O$ near $\varphi(y)$, with $z$ in its
germ, such that $Dg(z)$ maps $T_zO$ onto $K_z$ and $\ker Dg(z) \cap T_zO$ is in good position to
$C_{\varphi(y)}$ inside $T_zO$. Then for **every** datum of Definition 3.11 at $y$ (a strong bundle chart
$c'$ compatible with the atlas and centred at $y$, a filling germ $g'$ with a derivative family $Dg'$)
the germ is in good position in $c'$ at $Dg'(0)$; with only $\rho(z)k$ in the range for every smooth
$k \in F_\infty$ (the hypotheses of V3.79), the same when $Dg'(0)$ is Fredholm. (b) If $(f, y)$,
$f(y) = 0$, is in good position in some chart (V3.47) and has tame germ data at $y$ (V3.103), it is in
good position in that tame chart. *Book:* Definition 3.53, p. 111, presupposes that good position does
not depend on the chart; the proof of Theorem 3.54, p. 115 ("proceeding as above"). *Hidden
hypotheses:* none. *Deviation (not in the book):* V3.79 gives the good position in the chart that
Definition 3.11 provides at $y$; (a) gives it in every chart carrying germ data at $y$. (b) applies (a)
at $z = 0$ in the chart of the given good position, centred at $y$, where $0$ lies in every germ,
$Tf(0)$ maps onto $K_0$, $\ker Dg(0) \subseteq T_0O$ and $C_0 = C$; in the germ reading no Fredholm
input is needed (Findings, Chapter 3, item 301). This is how the good position of the nearby zeros in
Theorem 3.54 (1) (V3.94) and the good position from surjectivity (V3.100) are obtained in tame charts.
The whole-chart form of (a) is `Polyfold.StrongBundle.isGoodPositionAt_of_chart_dense`.

### What is not verified in this chapter

- pp. 111–114, Theorem 3.54 (1): nothing of the statement; the proof is not the text's (V3.93), and the
  first forms under the filler condition at the nearby zeros (V3.68, V3.69, V3.82, V3.85) are kept beside
  the forms with the text's hypotheses (V3.94, V3.95). Of the perturbation argument of the text's
  Proposition 6.2, used for the surjectivity at the nearby zeros, only the linear algebra is formalized
  (V3.83); for the index it is formalized (V3.98).
- p. 201 (Chapter 6), Proposition 6.2 for paths sc-smooth on $[0, 1]$ only: it is verified with the
  text's hypotheses (tame germ data, no bump functions, Definition 6.1 with local sections) for paths
  on $\mathbb R$ (V3.98); a path on $[0, 1]$ that does not extend sc-smoothly to $\mathbb R$ is not
  covered, the project having no M-polyfold $[0, 1]$. Without tame germ data the local constancy of the
  index at the zeros is open (Findings, Chapter 3, items 243, 343).
- p. 74, Theorem 3.19: "$\ker f'(y) = T_yS(f, U)$" with $T_yS$ a subspace of $T_yX$; it is verified in the
  chart of the tangent germ data (V3.99).
- p. 89, Remark 3.36 in quantitative form: its content is V3.26 and V3.31.
- p. 110, Proposition 3.52 on $T_xX \to Y_x$ itself: verified in charts, as an sc-Fredholm operator
  $T_zO \to K_z$ in every chart (V3.46, V3.96); $T_xX$ carries no linear structure here (Chapter 2).
- pp. 116–120, Theorem 3.58 for a general sc-splitting $E = B \oplus X$, $F = A \oplus Y$: verified in the
  coordinates of the text's proof (V3.89).
- pp. 121–125, Lemmas 3.62–3.64, 3.66–3.68 and p. 139, Lemma 3.76: superseded by the formal proofs of
  Proposition 3.22 and Proposition 3.73, not formalized.
- p. 135, Definition 3.71: Mathlib's $C^k$ within the set is used, equal to it on these sets.
- Lemma 3.70 in a general presentation of $C$ (hence $d_M = d_X$ in Theorem 3.27); Lemma 3.55 is verified in
  the model, in coordinates, and for a general presentation of $C$ (V3.49, V3.80).
- Theorem 3.27 for a set whose data do not satisfy condition (b) of V3.24 (it would need a re-graphing along
  another complement); for solution sets (b) holds by the choice of the complement (V3.77, V3.84).
- The linearization $f'(x) : T_xX \to Y_x$ and good position in $T_xX$ (Definition 2.38, gap G.13 of
  Chapter 2): Definition 3.53 is verified in charts, with its chart independence at zeros (V3.78).
- The chart-level half of the argument that the earlier hypothesis "the base retraction of every compatible
  strong bundle chart is tame" cannot be met (Findings, Chapter 3, items 190, 199): that the strong bundle
  chart $(1, \varphi)$ with base retraction $(a, u) \mapsto (1, r(u))$ on $[0, \infty) \times U$ is a chart
  compatible with every chart $(\varphi, U, R, \Phi)$ is (sc-calculus for affine maps, not done). Only the
  non-tameness of its base retraction is verified (V3.104); the theorems no longer use the hypothesis.
- Definition 3.11 $\Rightarrow$ Definition 3.50 (Findings, Chapter 3, items 199, 353): whether in a strong
  bundle whose atlas consists of tame charts every sc-Fredholm germ has germ data in some compatible tame
  chart is open. Re-centring a tame chart of the atlas does not do it: a filling needs $\ker Dr(0) \cong
  \ker\rho(0)$ in its chart, and a one-chart tame atlas of the trivial bundle carries no germ data at all
  (V3.103). The text builds the tame chart into Definition 3.50, and the theorems of §3.6 assume tame germ
  data.
- §3.1: Definitions 3.4, 3.6, 3.11, 3.14 (and 3.48, 3.50, 3.51, 3.53) are in the text's germ reading
  since phase 2 (V3.7, V3.9, V3.13, V3.16, V3.43, V3.45, V3.47), and Definition 3.3 since the fourth
  addendum (V3.5). Whether the text's germ reading and the
  project's earlier whole-chart reading of Definition 3.11 agree for sections sc-smooth on $X$ is
  open; no theorem depends on it (Findings, Chapter 3, items 220–221, 264, 330).

---

## 5. Chapter 4 (HWZ §§4.1–4.4): verified except Lemma 4.10 and §4.4

Chapter 4 of Part I (preprint pp. 147–168) asks when an M-polyfold is an ordinary manifold with
boundary with corners. §4.1 defines a compatible manifold structure with corners (Definition 4.1),
states the characterization (Theorem 4.2: $X_0 = X_\infty$, $1_0^1 : X \to X^1$ sc-smooth, and centred tame
charts whose tangent space at the centre is finite-dimensional and in good position), and prepares
its proof: Remark 4.3, sc⁺-retractions and sc⁺-retracts (Definitions 4.4, 4.6, Lemmas 4.5, 4.7,
Proposition 4.8), and the description of an sc⁺-retract near a point as a graph over its tangent space
(Proposition 4.9, with Lemmas 4.10–4.12). §4.2 defines smooth finite-dimensional submanifolds (Definition
4.13, Remark 4.14, Proposition 4.15, an open question), good position and tameness of submanifolds
(Definitions 4.16, 4.17), proves that a submanifold in good position is a tame manifold with corners
(Theorem 4.18, Lemma 4.19, Remark 4.20), defines general position (Definition 4.21) and describes a
submanifold near a point of general position (Theorem 4.22). §4.3 proves, with Sard's theorem, that the
fibres of a family $A \subseteq \mathbb R^m \times X$ over almost every parameter are compact manifolds with corners
in general position (Theorem 4.23, Remark 4.24). §4.4 sketches sc-differential forms, de Rham cohomology
and Stokes' theorem (Definitions 4.25, 4.27, Proposition 4.26, Theorem 4.28).

What is verified. **Theorems 4.2, 4.18, 4.22 and 4.23 hold with the text's hypotheses**, and Theorem 4.2
holds without its tameness hypothesis (V4.5). Every numbered statement of §§4.1–4.3 is verified except
Lemma 4.10, which is no longer used: Definition 4.1 (V4.1–V4.4), Theorem 4.2 (V4.5, V4.27, V4.28), Remark
4.3, with an example for "$X^1 \ne X$ is possible", which the text does not give (V4.6), Definitions 4.4, 4.6 and
Lemmas 4.5, 4.7 (V4.9–V4.12),
Proposition 4.8 with its chart form (V4.13, V4.14), Proposition 4.9 with Lemmas 4.11 and 4.12 (V4.20–V4.25),
Definition 4.13 (V4.29), Remark 4.14 in a chart (V4.31, V4.32), Proposition 4.15 (V4.33–V4.36), Definitions
4.16, 4.17, 4.21 in charts with their chart independence (V4.38–V4.40, V4.44, V4.45), Theorem 4.18, Lemma 4.19,
Remark 4.20 (V4.41–V4.43), Theorem 4.22 (1)–(4) (V4.49–V4.52), Theorem 4.23 (V4.54, V4.63, V4.64) and Remark
4.24 (V4.55). Four places of the text needed more than a reading. (a) Proposition 4.9 is proved with two
hypotheses the text leaves implicit — the good complement $Y$ is closed, and $p$ is the projection along $Y$,
not $Dt(0)$ — and by a direct argument, because the text's route through Lemma 4.10 and Corollary 3.47
yields the graph map only as a germ over a complement of its own choosing (V4.20); where Proposition 4.9 is
applied the closed complement is chosen, so Theorems 4.2, 4.18, 4.22, 4.23 need nothing extra. (b) One step
of Lemma 4.19 is false ("$z \in Z \subset C$" does not give $n + y \in C$) and is repaired (V4.42). (c) Theorem
4.22 (4) has no proof in the text and is proved (V4.51, V4.52). (d) In Theorem 4.23 "regular value" is the
stratified notion of the proof — every stratified regular value is a regular value, and with ordinary
regular values the conclusion fails at the value — and the finite cover of the proof does not exist in
general; a countable one is used (V4.53, V4.54, V4.64). Proved although the text does not construct or state
it: charts and strong bundle charts centred at a smooth point (V4.15–V4.18), the sc⁺-retraction onto the
fibre $A_\lambda$ and its general position (V4.61, V4.62), Theorem 3.78 in $C^\infty$ form (V4.58), and Sard's
theorem in all dimensions (V4.56, vendored from our Milnor project, `math_faithful`). Not verified:
Lemma 4.10, §4.4, the open question after Proposition 4.15, and the chart independence of stratified regularity (see
the list at the end of this section). A fourth addendum (2026-11-02; Findings, items 140–146) added the example of Remark
4.3 to V4.6.

The setting. An sc⁺-map is a map whose values lie in $F_1$ and whose lift into $F^1$ is sc-smooth (V4.7); the
text uses the word for maps and defines it only for retractions. $T_xX$ carries no linear structure in the
formalization (gap G.7 of Chapter 2), so every condition the text states in $T_aX$ — the tangent space of a
submanifold, good and general position, stratified regularity — is stated in a chart and, except for
stratified regularity, proved independent of the chart. A chart "with $\psi(x) = 0$" is a chart re-centred at
the smooth point $x$, modelled in the partial quadrant $C_{\varphi(x)}$ of Definition 2.33 (V4.17). The map $1_0^1 :
X \to X^1$ is defined on $X_1$, with an arbitrary value off $X_1$ that plays no role. Tameness of $X$ enters
§4.2 only through Lemma 4.19 (Theorem 4.18, Remark 4.20), the tame centred chart of Theorem 4.22 and
Proposition 2.36 (general position implies good position, V4.48). Findings referred to below are those of
`Exposition/Findings.md`, "Chapter 4".

**V4.1 (Definition 4.1, corner charts and corner structures; `Polyfold.MChart.IsCornerChart`,
`Polyfold.MPolyfold.HasCornerStructure`, `Polyfold.MPolyfold.hasCornerStructure_iff`,
`Polyfold.MPolyfold.HasCornerStructure.isTame`, `Polyfold.MChart.IsCornerChart.isTameRetract`,
`Polyfold.MChart.IsCornerChart.isScPlusRetract`).** A chart of $X$ is a *corner chart* if its local model is
$(U, C, V)$ with $V$ a finite-dimensional real normed space carrying the constant sc-structure, $C$ a partial
quadrant in $V$, $U$ relatively open in $C$, and the identity retraction. $X$ has a *corner structure* if it
has an atlas of corner charts equivalent to its atlas; equivalently, every point of $X$ lies in a corner
chart that is a chart of the M-polyfold structure. The dimension of $V$ may vary from chart to chart. The
model of a corner chart is a tame retract and an sc⁺-retract, and an M-polyfold with a corner structure is
tame. *Book:* Definition 4.1, p. 147. *Hidden hypotheses:* "sc-smoothly compatible charts" with "$\varphi$ an
sc-diffeomorphism" is read as compatibility with the atlas of $X$ (equivalence of atlases, as for tameness).
*Deviation (restated):* the classical manifold structure with corners is represented by the atlas of corner
charts; local constancy of the dimension is neither stated by the text nor formalized.

**V4.2 (Definition 4.1, the transition maps are $C^\infty$; `Polyfold.MChart.IsCornerChart.contDiffOn_transition`,
`Polyfold.MChart.isRelOpenInQuadrant_overlap`).** For compatible corner charts $\chi$, $\chi'$ the overlap $\chi(V
\cap V')$ is relatively open in the partial quadrant of $\chi$, and the transition map $\chi' \circ \chi^{-1}$ is of
class $C^\infty$ on it (derivatives within the set, one-sided at the boundary). *Book:* Definition 4.1, p. 147,
the paragraph after the definition. *Hidden hypotheses:* none. *Deviation:* "the atlas defines the structure
of a smooth manifold with boundary with corners" is not formalized beyond this (Mathlib's manifolds with
corners have a single model space).

**V4.3 (finite-dimensional sc-Banach spaces; `Polyfold.ScBanach.finiteDimensional_lvl`,
`Polyfold.ScBanach.toBase_surjective`, `Polyfold.ScBanach.scIsoConst`,
`Polyfold.ScBanach.mem_smooth_of_finiteDimensional`).** If $E_0$ is finite-dimensional, every level $E_m$ is
finite-dimensional, every inclusion $E_m \to E_0$ is onto, $E$ is sc-isomorphic to $E_0$ with the constant
structure (the level maps being the inclusions), and every point of $E_0$ is smooth. *Book:* §1.1, p. 6, after
Definition 1.1 ("a finite-dimensional Banach space has precisely one sc-structure"), used in Definition 4.1.
*Hidden hypotheses:* the density of $E_\infty$ in every level (Definition 1.1 (2)) is what makes the
inclusions onto; compact injective inclusions alone do not ($E_0 = \mathbb R$, $E_m = 0$ for $m \ge 1$).
*Deviation (restated):* "one sc-structure" as an sc-isomorphism onto the constant structure.

**V4.4 (Definition 4.1 with arbitrary finite-dimensional models, and the manifolds with corners of Chapter 3;
`Polyfold.MChart.exists_isCornerChart_of_finiteDimensional`,
`Polyfold.IsRelOpenInQuadrant.isScDiffeoQuadrant_toConst`,
`Polyfold.MPolyfold.hasCornerStructure_iff_finiteDimensional`, `Polyfold.MPolyfold.isManifoldWithCorners_iff`,
`Polyfold.MPolyfold.IsManifoldWithCorners.hasCornerStructure`).** A chart of $X$ onto a relatively open subset of
a partial quadrant in an sc-Banach space with finite-dimensional $E_0$ is, with the same map and domain, a
corner chart for the constant structure on $E_0$, of the same dimension. Hence $X$ has a corner structure iff
it has an equivalent atlas of charts onto relatively open subsets of partial quadrants in sc-Banach spaces
with finite-dimensional $E_0$ (the manifolds with corners of locally constant dimension of Theorem 3.27). The
manifolds with corners of dimension $n$ of Theorem 3.27 are exactly the corner structures all of whose
corner charts have dimension $n$. *Book:* Definition 4.1, p. 147 ("or in a finite-dimensional vector space");
the relation to Chapter 3 is not stated. *Hidden hypotheses:* none. *Deviation (not in the book).*

**V4.5 (Theorem 4.2, the characterization; `Polyfold.MPolyfold.theorem_4_2`,
`Polyfold.MPolyfold.theorem_4_2_general`).** Let $X$ be an M-polyfold and $x_0 \in X_1$ the junk value of $1_0^1$
off $X_1$. The following are equivalent. (i) $X$ has a corner structure (V4.1). (ii) Every point of $X$ is
smooth, $1_0^1 : X \to X^1$ is sc-smooth, and every $x \in X$ lies in a chart $\psi$ of $X$ with $\psi(x) = 0$
whose model $(O, C, E)$ is a tame retract and whose tangent space $N = T_0O$ (Definition 2.17) is
finite-dimensional and in good position to $C$ (Definition 3.21). `theorem_4_2` is the text's form, with the
hypothesis "$X$ tame". *Book:* Theorem 4.2, p. 147; proof pp. 156–157. *Hidden hypotheses:* the chart with
$\psi(x) = 0$ is a re-centred chart (V4.17). *Deviation (stronger):* the tameness of $X$ is not used, and (i)
implies it (V4.1). *Proof:* V4.27, V4.28.

**V4.6 (Remark 4.3; `Polyfold.ScBanach.liftOne`, `Polyfold.MPolyfold.toLevelOne`,
`Polyfold.MPolyfold.remark_4_3_levelVal`, `Polyfold.MPolyfold.remark_4_3_isScDiffeo`,
`Polyfold.remark_4_3_const`, `Polyfold.remark_4_3_example`, `Polyfold.remark_4_3_retract_example`,
`Polyfold.IsLossFamily.isScSmooth`, `Polyfold.exists_retract_smooth_not_scPlus_of_data`,
`Polyfold.MPolyfold.mem_shift_levelSet_iff`).** The inclusion $1_1^0 : X^1 \to X$ is always sc-smooth; in the charts $(V_1,
\varphi, (O_1, C_1, E^1))$ and $\varphi$ it is the sc-operator $\iota : E^1 \to E$. If every point of $X$ lies in
$X_1$ and $1_0^1 : X \to X^1$ is sc-smooth, then $1_0^1$ is an sc-diffeomorphism with inverse $1_1^0$. For a
finite-dimensional $V$ with the constant structure, $V^1 = V$ as sc-Banach spaces, the lift $V \to V^1$ is the
identity, and every sc-smooth retract in $V$ is an sc⁺-retract. The levels of $X^1$ are those of $X$ shifted by
one, as sets: $(X^1)_m = X_{m+1}$. **The example:** there is an M-polyfold all of whose points are smooth ($X_0 =
X_\infty$) for which $1_0^1 : X \to X^1$ is not sc-smooth, so $X^1 \ne X$ as M-polyfolds. It is a retract $O \subseteq
\mathbb R \oplus X$, $X$ the weighted sequence space of V1.13 ($|x|_m = \sup_k (k+1)^m|x_k|$), with a single chart: the
image of $r(t, z) = (t, L(t)z)$, $L(t)$ the projection onto $\cos\theta\,e_{n_k} + \sin\theta\,e_{n_{k+1}}$ ($n_k =
2^k$), the angle $\theta$ turning from $0$ to $\pi/2$ with flat ends while $t$ runs through $[1/(k+2), 1/(k+1)]$, and $L(t)
= 0$ for $t \le 0$. Its points are smooth, and the lift $O \to E_1$ is discontinuous at $0$, so $O$ is not an
sc⁺-retract (Proposition 4.8). The sc-smoothness of $r$ comes from a criterion proved for it: for level operators
$L(p)_m : Z_m \to W_m$ depending on a finite-dimensional parameter $p$, compatible with the inclusions, with $(p, z) \mapsto
L(p)_mz$ continuous and $p \mapsto L(p)_m$ of class $C^\infty$ as a map into the operators $Z_{m+1} \to W_m$ (one level of
loss), $(p, z) \mapsto L(p)z$ is sc-smooth. *Book:* Remark 4.3, p. 148. *Hidden hypotheses:* $1_0^1$ is defined on $X_1$ (the
text: when $X_0 = X_\infty$). *Deviation (stronger):* the sc-diffeomorphism clause needs only $X = X_1$, not $X_0 =
X_\infty$; "$X^1 \ne X$ is possible" has an example, which the text does not give, and in it $X$ and $X^1$ even have different
topologies on the same set. "$X^1 \ne X$" is read as "$1_0^1$ is not sc-smooth", equivalently "the identity is not an
sc-diffeomorphism". An example needs a retraction that loses a level in its first derivative, as the splicings of HWZ do (a
retraction with $C^1$ level maps gives none: an argument, not formalized), so its sc-smoothness does not follow from
Proposition 1.19. "$(X^1)_m = X_{m+1} = X_i$" misprints $X_0$; the topologies of the iterated levels are gap G.6 (Findings,
items 5, 125, 140–146). Formerly "narrower", for the missing example (gap G.31, now closed).

**V4.7 (sc⁺-maps; `Polyfold.IsScPlus`, `Polyfold.IsScPlus.mem_range_succ`, `Polyfold.IsScPlus.iff_exists`,
`Polyfold.IsScPlus.isScSmooth`, `Polyfold.IsScPlus.comp_isScSmooth`, `Polyfold.IsScSmooth.comp_isScPlus`,
`Polyfold.ScPlus.isScPlus`).** A map $f$ on $U \subseteq E_0$ is *sc⁺* if $f(U) \subseteq F_1$ and the lift $U \to F^1$,
$x \mapsto f(x) \in F_1$, is sc-smooth. Then $f(U_m) \subseteq F_{m+1}$ for every $m$. On an sc-domain $U$: $f$ is sc⁺
iff some sc-smooth $g : U \to F^1$ has $\iota \circ g = f$ on $U$; an sc⁺-map is sc-smooth; $g \circ f$ is sc⁺ if $g$ is
sc⁺ on an sc-domain $V$ and $f$ is sc-smooth with $f(U) \subseteq V$; $g \circ f$ is sc⁺ if $f$ is sc⁺ with $f(U) \subseteq
V$ and $g$ is sc-smooth on $V$ (through Proposition 1.17 for $g$); an sc⁺-operator is an sc⁺-map. *Book:* not
defined (Definition 4.4 is for retractions; the proof of Lemma 4.7 says "$r$ is a sc⁺-map"). *Hidden
hypotheses:* $U$, $V$ sc-domains for the composition rules. *Deviation (not in the book).*

**V4.8 (the derivative of an sc⁺-map; `Polyfold.IsScPlus.exists_scPlus_deriv`,
`Polyfold.IsScPlus.isCompactOperator_deriv`, `Polyfold.finiteDimensional_range_of_isCompactOperator_of_idem`).**
Let $f$ be sc⁺ on an sc-domain $U$ and $x \in U_1$ a smooth point. There is an sc⁺-operator $S : E \to F$ whose
level-$0$ operator is $Df(x)$; $Df(x) : E_0 \to F_0$ is compact, and so is every level operator of $S$. A compact
continuous linear projection $P = P \circ P$ of a normed space has finite-dimensional range. *Book:* proof of
Lemma 4.7 (ii), p. 149 ("a sc⁺-operator, since $r$ is a sc⁺-map ... must be finite-dimensional").
*Hidden hypotheses:* $x$ smooth; the range of a compact projection is finite-dimensional by Riesz's theorem.
*Deviation (hypotheses explicit).*

**V4.9 (Definition 4.4, sc⁺-retractions; `Polyfold.ScRetraction.IsScPlus`,
`Polyfold.ScRetraction.IsScPlus.mem_lvlSet_succ`, `Polyfold.MPolyfold.IsScPlusRetractionOn`).** An sc-smooth
retraction $r : U \to U$ is an *sc⁺-retraction* if it is an sc⁺-map on $U$ (V4.7); then $r(U_m) \subseteq U_{m+1}$ for
every $m$. On an open $V$ of an M-polyfold: $s$ is an sc⁺-retraction on $V$ if $s$ is sc-smooth on $V$, $s(V)
\subseteq V$, $s \circ s = s$ on $V$, $s(V) \subseteq X_1$, and $1_0^1 \circ s : V \to X^1$ is sc-smooth (for every junk
value). *Book:* Definition 4.4, p. 148. *Hidden hypotheses:* in the M-polyfold form, $s(V) \subseteq X_1$, so that
"$r : V \to V^1$" makes sense. *Deviation (restated):* $r(U_m) \subseteq U_{m+1}$ is derived, not assumed.

**V4.10 (Lemma 4.5; `Polyfold.lemma_4_5`).** If $t$ is an sc⁺-retraction and $s$ an sc-smooth retraction
(possibly of another relatively open subset of $C$) with the same retract, then $s$ is an sc⁺-retraction.
*Book:* Lemma 4.5, p. 148. *Hidden hypotheses:* none. *Proof:* the text's, $s = t \circ s$ and sc⁺ ∘ sc-smooth
is sc⁺.

**V4.11 (Definition 4.6, sc⁺-retracts; `Polyfold.IsScPlusRetract`, `Polyfold.IsScPlusRetract.isScPlus`,
`Polyfold.isScPlusRetract_iff_forall`).** $(O, C, E)$ is an *sc⁺-retract* if $O$ is the retract of an sc⁺-retraction
of a relatively open $U \subseteq C$; then every sc-smooth retraction onto $O$ is sc⁺, and $O$ is an sc⁺-retract iff it
is a retract all of whose retractions are sc⁺. *Book:* Definition 4.6 and the remark after it, pp. 148–149.
*Hidden hypotheses:* none.

**V4.12 (Lemma 4.7; `Polyfold.lemma_4_7_i`, `Polyfold.lemma_4_7_ii`, `Polyfold.lemma_4_7_ii_tangentSpace`).**
Let $r$ be an sc⁺-retraction onto $O$. (i) $O \subseteq E_\infty$. (ii) For every level-$1$ point $o$ with $\iota(o) \in O$
the range of $Dr(o)$ is finite-dimensional; every $o \in O$ has a smooth lift $o_1 \in E_1$, and $T_{o_1}O =
Dr(o_1)E_0$ is a finite-dimensional linear subspace. *Book:* Lemma 4.7, p. 149. *Hidden hypotheses:* none.
*Deviation (hypotheses explicit):* the tangent space of Definition 2.17 is indexed by level-$1$ points; the step
"$Dr(o)$ is an sc⁺-operator" is V4.8.

**V4.13 (Proposition 4.8; `Polyfold.proposition_4_8`).** An sc-smooth retract $(O, C, E)$ is an sc⁺-retract iff
$O \subseteq E_\infty$ and the lift $1_0^1$ is sc-smooth from $(O, C, E)$ to $(O_1, C_1, E^1)$ in the sense of
Definition 2.7. *Book:* Proposition 4.8, p. 149. *Hidden hypotheses:* none. *Deviation:* none (the proof ends
"the lemma is proved").

**V4.14 (Proposition 4.8 in charts; `Polyfold.MPolyfold.levelChart_toLevelOne`,
`Polyfold.MPolyfold.proposition_4_8_chart`, `Polyfold.MPolyfold.isScSmoothMap_toLevelOne_iff`,
`Polyfold.MPolyfold.isScSmoothMap_toLevelOne_of_cover`).** In the charts $\varphi$ of $X$ and $(V_1, \varphi, (O_1, C_1,
E^1))$ of $X^1$ the map $1_0^1$ is the lift $O \to O_1$. For a chart $\varphi : V \to O$ of $X$: the model is an
sc⁺-retract iff $V \subseteq X_\infty$ and $1_0^1$ is sc-smooth on $V$. Hence "every point smooth and $1_0^1$
sc-smooth" holds iff every chart of $X$ is modelled on an sc⁺-retract, iff every point lies in some chart so
modelled. *Book:* not stated; used in the proofs of Theorem 4.2 and Proposition 4.15 (4). *Hidden
hypotheses:* none. *Deviation (not in the book).*

**V4.15 (the partial quadrant $C_e$ and the neighbourhood $G(e)$; `Polyfold.recentreNbhd`, `Polyfold.recentreIso`,
`Polyfold.isPartialQuadrant_partialQuadrantAtWith`, `Polyfold.image_sub_partialQuadrantAtWith`,
`Polyfold.recentreNbhd_inter_eq`, `Polyfold.degIndex_sub_recentre`, `Polyfold.minimalSubspaceWith_recentreIso`,
`Polyfold.partialQuadrantAtWith_recentreIso`).** Let $T$ present $C$ with coordinates $\lambda_1, \dots, \lambda_n$ and let $e
\in E_0$. $G(e) = \{v : \lambda_i(v) > 0$ whenever $\lambda_i(e) \ne 0\}$ is open and, for $e \in C$, contains $e$. $C_e$ is a
partial quadrant, presented by reordering the coordinates as $\mathbb R^{I(e)} \oplus (\mathbb R^{\text{rest}} \oplus W)$;
$C_e - e = C_e$; $G(e) \cap C = G(e) \cap C_e$; and for $v \in G(e)$ the vanishing coordinates of $v - e$ for this
presentation are those of $v$, so that $d_{C_e}(v - e) = d_C(v)$ ($v \in C$) and the minimal subspace and the partial
quadrant of $v - e$ are $E_v$ and $C_v$. *Book:* Definition 2.33, p. 39, asserts without proof that $C_e$ is a
partial quadrant; the rest is not in the text. *Hidden hypotheses:* none. *Deviation (not in the book).*

**V4.16 (translations and re-centred retracts; `Polyfold.isScSmooth_add_const`, `Polyfold.isScSmooth_sub_const`,
`Polyfold.relOpen_translate`, `Polyfold.isScDiffeoQuadrant_translate`, `Polyfold.ScRetraction.restrictIn`,
`Polyfold.ScRetraction.restrictIn_isTame`, `Polyfold.isScRetract_recentre`, `Polyfold.isTameRetract_recentre`).**
Translation by a smooth vector is sc-smooth on every sc-domain. For $e$ smooth and $U$ relatively open in $C$ with $U
\subseteq G(e)$, the translate $U - e$ is relatively open in $C_e$ and $v \mapsto v - e$ is an sc-diffeomorphism $U \to U - e$.
The restriction of a retraction $r$ to $U \cap r^{-1}(W) \cap W$ ($W$ open) is a retraction onto $r(U) \cap W$, tame if $r$
is. For a retract (tame retract) $(O, C, E)$ and a smooth $e \in E_0$, $((O \cap G(e)) - e, C_e, E)$ is a retract (tame
retract), with the retraction $u \mapsto r(u + e) - e$. *Book:* not in the text. *Hidden hypotheses:* $e$ smooth —
translation by $e$ preserves every level only then. *Deviation (not in the book).*

**V4.17 (charts centred at a smooth point; `Polyfold.MChart.recentre`, `Polyfold.MChart.recentre_isChart`,
`Polyfold.MChart.recentre_apply_self`, `Polyfold.MChart.isTameRetract_recentre`,
`Polyfold.MChart.chartDegIndex_recentre`, `Polyfold.MPolyfold.exists_centredChart`,
`Polyfold.MPolyfold.IsTame.exists_centredChart`).** For a chart $\varphi : V \to O \subseteq C$ of $X$, a presentation of $C$
and a smooth $e$, the chart $\varphi_e = \varphi - e$ on $V \cap \varphi^{-1}(G(e))$, modelled on $((O \cap G(e)) - e, C_e, E)$, is a chart
of $X$, with $\varphi_e(x) = 0$ when $\varphi(x) = e$, the same degeneracy index as $\varphi$ on its domain, and a tame model
when $\varphi$ has one. So every smooth point $x$ of the domain of a chart $\varphi$ lies in a chart $\chi$ of $X$ with
domain inside that of $\varphi$ and $\chi(x) = 0$; in a tame M-polyfold every smooth point lies in a tame chart
centred at it. *Book:* used without construction in Theorem 4.2 (ii), the proofs of Theorems 4.18 and 4.22, and
Lemma 5.11. *Hidden hypotheses:* $x$ smooth; the model lies in $C_{\varphi(x)}$, not in $C$. *Deviation (not in the
book).*

**V4.18 (strong bundle charts centred at a smooth point; `Polyfold.StrongBundleChart.recentre`,
`Polyfold.StrongBundleChart.Compatible.recentre`, `Polyfold.StrongBundle.IsChart.recentre`,
`Polyfold.StrongBundle.IsChart.exists_centred`).** For a strong bundle chart $c$ over $\varphi$, a presentation and a
smooth $e$, the chart $c_e$ over $\varphi_e$ with bundle retraction $R_e(u, h) = (r(u + e) - e, \Gamma(u + e, h))$ and
$\Phi_e(y) = (\Phi(y)_1 - e, \Phi(y)_2)$ is compatible with every chart $c$ is compatible with (the projection being
continuous), and is a chart of the strong bundle. Every smooth point of the base in the domain of a strong bundle
chart lies in a strong bundle chart centred at it, with smaller domains. *Book:* used in Lemma 5.11. *Hidden
hypotheses:* $e$ smooth; $(e, 0)$ is then smooth in $E \oplus F$ and $E \oplus F^1$. *Deviation (not in the book).*

**V4.19 (the level data of an sc⁺-retraction and the mean value estimate; `Polyfold.ScRetraction.lvlMap`,
`Polyfold.ScRetraction.lvlDeriv`, `Polyfold.ScRetraction.IsScPlus.hasFDerivWithinAt_lvlMap`,
`Polyfold.ScRetraction.IsScPlus.continuousOn_lvlDeriv`, `Polyfold.ScRetraction.IsScPlus.exists_mvt`,
`Polyfold.exists_norm_sub_sub_le_of_hasFDerivWithinAt`).** Let $t$ be an sc⁺-retraction and $k \ge 0$. Then $t :
U_{k+1} \to E_{k+1}$ is differentiable within $U_{k+1}$, with derivative $Dt(x) \in \mathcal L(E_{k+1})$ continuous in $x$ in
the operator norm. For $u_0 \in U_{k+1}$ and $\theta > 0$ there is $r > 0$ with $C_{k+1} \cap B(u_0, r) \subseteq U_{k+1}$,
$\|Dt(z) - Dt(u_0)\| \le \theta$ there, and $|t(z') - t(z) - Dt(u_0)(z' - z)|_{k+1} \le \theta|z' - z|_{k+1}$ for $z, z' \in C_{k+1} \cap
B(u_0, r)$. *Book:* (76)–(77) and the estimates in the proofs of Lemmas 4.11 and 4.12, pp. 154–155. *Hidden
hypotheses:* the mean value inequality is taken on the convex set $C_{k+1} \cap B(u_0, r)$, since $U_{k+1}$ need not be
convex. *Deviation (restated):* the text's integrals are the mean value inequality.

**V4.20 (Proposition 4.9; `Polyfold.proposition_4_9`, `Polyfold.finiteDimensional_tangentSpace_zero`,
`Polyfold.GraphData`).** Let $t : U \to U$ be an sc⁺-retraction onto $O \ni 0$, $N = T_0O$ (finite-dimensional by Lemma
4.7), in good position to $C$, $Y$ a good complement of $N$, **$Y$ closed**, and $p : E_0 \to N$ continuous linear with
$p = 1$ on $N$ and $p = 0$ on $Y$ (**the projection along $Y$**). There are an open $W \ni 0$ in $E_0$, a relatively open
$V \ni 0$ in the partial quadrant $N \cap C$ of $N$ (constant structure) and $\Gamma : N \to E_0$, sc-smooth on $V$, with
$p \circ \Gamma = 1$ on $V$, $\Gamma(a) - a \in Y$, $\Gamma(V) = O \cap W$, $\Gamma \circ p = 1$ on $O \cap W$, $\Gamma(0) = 0$, and $p$, $\Gamma$
sc-smooth between the retracts $(O \cap W, C, E)$ and $(V, N \cap C, N)$: $p : O \cap W \to V$ is an sc-diffeomorphism with
inverse $\Gamma$. *Book:* Proposition 4.9, p. 150; proof pp. 150–156. *Hidden hypotheses:* $Y$ closed (Definition 3.21
asks for an sc-complement, which is closed; the formal good complement records only the splitting), and $p$ the
projection along $Y$: the text writes $p = Dt(0)$, a projection along $\ker Dt(0)$, which nothing relates to $Y$,
while Lemma 4.12 needs the projection along $Y$ (Findings, items 20, 21). *Deviation (hypotheses explicit):* the
conclusion is stated on fixed sets, with $\Gamma$ sc-smooth on the fixed $V$. *Proof:* not the text's. The text
applies Corollary 3.47 to the section $\mathbf f(u) = (1 - p)(u - t(u))$ (Lemma 4.10), which gives a graph over a
complement of its own choosing, sc-smooth only as a germ (Findings, item 22); the formal proof is direct
(V4.21–V4.25).

**V4.21 (Lemma 4.11, uniqueness; `Polyfold.GraphData.qL_lvlDeriv_zero`, `Polyfold.GraphData.lvlDeriv_zero_of_mem_N`,
`Polyfold.GraphData.exists_contraction_radius`, `Polyfold.GraphData.eq_of_p_eq`).** In the data of V4.20, on every
level $k + 1$: $(1 - p)Dt(0) = 0$ and $Dt(0) = 1$ on $N$; for $\theta > 0$ there is $r > 0$ for which the estimates of V4.19
hold at $u_0 = 0$ and $|(1 - p)(u' - u)|_{k+1} \le \|1 - p\|\theta|u' - u|_{k+1}$ for $u, u' \in O_{k+1}$ with $|u|_{k+1},
|u'|_{k+1} < r$; and two points $u, u'$ with $p(u) = p(u')$ and $|(1 - p)(u' - u)| \le c|u' - u|$, $c < 1$, coincide.
*Book:* Lemma 4.11, p. 154: small solutions $a + y$ of $\mathbf f = 0$ have $y = \delta(a)$. *Hidden hypotheses:* none.
*Deviation (restated):* uniqueness among points of $O$, without the $\delta$ of Corollary 3.47.

**V4.22 (Lemma 4.12, existence; `Polyfold.GraphData.eps'`, `Polyfold.GraphData.exists_graph_point`).** Let $\varepsilon$ be
the constant of the good complement $Y$ and $\varepsilon' = \varepsilon/(\|\iota_1\|\|\mathrm{lift}_N\| + 1)$. If the
estimates of V4.21 hold on $C_1 \cap B(0, r)$ with $\theta < 1$, $\|1 - p\|\theta < 1$ and $\|1 - p\|\theta(1 + \varepsilon') \le \varepsilon'$,
there is $\rho > 0$ such that every $a \in N \cap C$ with $|a|_1 < \rho$ has a $u \in O_1$ with $p(u) = a$, $u - a \in Y$,
$|u - a|_1 \le \varepsilon'|a|_1$ and $|u|_1 < r$. *Book:* Lemma 4.12, pp. 154–155: $a + \delta(a) \in O$ for small $a$.
*Hidden hypotheses:* none. *Deviation (restated):* the point is constructed as the fixed point of $y \mapsto (1 -
p)t(a + y)$ on $\{y \in Y_1 : |y|_1 \le \varepsilon'|a|_1\}$, where $a + y \in C$ by the good complement property; then the
text's argument $a_1 = a$ shows $t(u) = u$.

**V4.23 ($p(O \cap W) \subseteq C$ and the neighbourhoods; `Polyfold.GraphData.p_mem_C`, `Polyfold.GraphData.Nbhd`,
`Polyfold.GraphData.exists_nbhd`, `Polyfold.GraphData.Nbhd.image_V`, `Polyfold.GraphData.Nbhd.injOn_p`).** (a) If $u
\in O_1$ satisfies $|(1 - p)u|_1 \le \kappa|u|_1$ with $0 \le \kappa \le 1/2$ and $2\|\iota_1\|\kappa\|\mathrm{lift}_N\| \le \varepsilon$, then
$p(u) \in C$. (b) For every $\theta_0 > 0$ there are $r > 0$, an open $W = B_0(0, \delta_0) \cap p^{-1}(V')$, an open $V' =
\{a : |a|_1 < \rho'\}$ of $N$ and $\Gamma$ on $V = V' \cap C$ with $\Gamma(V) \subseteq O \cap W$, $p \circ \Gamma = 1$, $\Gamma(a) - a \in Y$, $|\Gamma(a)|_1 <
r$, $p(O \cap W) \subseteq V$, $\Gamma \circ p = 1$ on $O \cap W$, $\|Dt(z) - Dt(0)\|_{\mathcal L(E_1)} \le \theta_0$ on $C_1 \cap B(0, r)$,
and $|(1 - p)(u' - u)|_1 \le \frac12|u' - u|_1$ on $O_1 \cap B_1(0, r)$; then $\Gamma(V) = O \cap W$ and $p$ is injective on
$O \cap W$. *Book:* the last paragraph of the proof of Proposition 4.9, p. 156 ("$V = \{a \in T_0O \cap C : |a|_0 <
\varepsilon\}$"). *Hidden hypotheses:* $p(u) \in C$ for $u \in O$ near $0$, which the text never checks (Findings, item 25).
*Deviation (not in the book):* the neighbourhoods are open on level $0$ and controlled on level $1$ through the
continuity of $t : U \to E_1$ at $0$.

**V4.24 (the regularity of $\Gamma$: continuity and the frame formula; `Polyfold.GraphData.Nbhd.norm_Γ_lvl_one_sub_le`,
`Polyfold.GraphData.Nbhd.continuousOn_Γ_lvl`, `Polyfold.norm_sub_le_of_projection`,
`Polyfold.hasFDerivWithinAt_of_projection`, `Polyfold.GraphData.A_injective`,
`Polyfold.GraphData.eq_zero_of_mem_Y_of_scDeriv_eq`, `Polyfold.GraphData.scDeriv_sub_frame`,
`Polyfold.GraphData.Nbhd.hasFDerivWithinAt_Γ_lvl`).** With the data of V4.23: $|\Gamma(a') - \Gamma(a)|_1 \le
2\|\mathrm{lift}_N\||a' - a|$, and $\Gamma$ is continuous into every level $E_m$ on $V$. If $\|Dt(u) - Dt(0)\|_{\mathcal L(E_1)} \le
\theta_0$ with $\theta_0$ small (`FrameSmall`), then $A(u) = p \circ Dt(u)|_N$ is invertible, $T_uO \cap Y = 0$ and $(1 -
B_up)Dt(u) = 0$ for the frame $B_u = Dt(u)|_N \circ A(u)^{-1}$; and $\Gamma$ is differentiable into every level $E_{k+1}$ on
$V$ with $D\Gamma(a) = Dt(\Gamma(a))|_N \circ (p \circ Dt(\Gamma(a))|_N)^{-1}$. The abstract step: if $s$ satisfies the mean value
estimate at $u_0$ on a set $S$, $q \circ B = 1$, $(1 - Bq)Ds(u_0) = 0$ and $\theta\|1 - Bq\| \le 1/2$, then fixed points $u, u'$
of $s$ in $S$ satisfy $|u' - u| \le 2\|B\||q(u' - u)|$, and every continuous right inverse of $q$ with values in the
fixed points has derivative $B$ at $q(u_0)$. *Book:* not in the text (Corollary 3.47 gives $\delta$ as an sc-smooth
germ). *Hidden hypotheses:* none. *Deviation (not in the book).*

**V4.25 (the $C^k$-bootstrap and the sc-diffeomorphism; `Polyfold.GraphData.contDiffOn_lvlDeriv_apply`,
`Polyfold.GraphData.Nbhd.contDiffOn_Γ_lvl`, `Polyfold.GraphData.Nbhd.isScSmooth_Γ`,
`Polyfold.GraphData.Nbhd.V_isRelOpenInQuadrant`, `Polyfold.GraphData.Nbhd.p_isScSmoothRetractMap`,
`Polyfold.GraphData.Nbhd.Γ_isScSmoothRetractMap`).** $(x, w) \mapsto Dt_{j+1}(x)w$ is $C^k$ on $U_{j+k+1} \times E_{j+k+1}$
(Proposition 1.18 for the tangent map of the lift); $\Gamma$ is $C^k$ into every $E_{j+1}$ on $V$ for every $k$, hence
$C^\infty$ into every level and sc-smooth on $V$ (Proposition 1.19); $(V, N \cap C, N)$ is a local model; $p$ and $\Gamma$
are sc-smooth between the retracts $(O \cap W, C, E)$ and $(V, N \cap C, N)$. *Book:* the last sentence of the proof
of Proposition 4.9, p. 156 ("having the sc-smooth map $a \mapsto a + \delta(a)$ as its inverse"). *Hidden hypotheses:*
none. *Deviation (not in the book):* derivatives of $t$ are applied only to vectors of the smooth
finite-dimensional $N$, so the level loss of $Tt$ does not accumulate.

**V4.26 (charts composed with an sc-diffeomorphism between retracts; `Polyfold.MChart.compRetract`,
`Polyfold.MChart.compRetract_isChart`).** For a chart $\varphi$ onto $(O, C, E)$ and mutually inverse $f$, $g$ that are
sc-smooth between $(O, C, E)$ and a retract $(O', C', E')$ (Definition 2.7), $f \circ \varphi$ is a chart onto $(O', C', E')$,
and a chart of the M-polyfold whenever $\varphi$ is. *Book:* not stated; "we obtain a smoothly compatible atlas",
p. 157. *Hidden hypotheses:* none. *Deviation (not in the book).*

**V4.27 (Theorem 4.2, (i) ⇒ (ii); `Polyfold.MChart.IsCornerChart.mem_smooth`,
`Polyfold.MChart.IsCornerChart.exists_centred`, `Polyfold.MChart.IsCornerChart.exists_centred_tame`,
`Polyfold.tangentSpace_relOpen`, `Polyfold.isInGoodPosition_top`).** Every point of a corner chart is smooth for its
model. A point $x$ in the domain of a corner chart $\chi$ of $X$ lies in a chart $\psi$ of $X$ with $\psi(x) = 0$, modelled on a
relatively open subset of the partial quadrant $C_{\chi(x)}$ in the same finite-dimensional space; this model is a tame
retract (identity retraction), its tangent space at $0$ is the whole space, and the whole space is in good position to
any partial quadrant (complement $0$). Together with V4.14 and V4.1, (i) implies (ii). *Book:* proof of Theorem 4.2,
p. 156. *Hidden hypotheses:* the centred chart, the tangent space at its centre and its good position, which the
text's proof does not address (Findings, item 53). *Deviation (hypotheses explicit).*

**V4.28 (Theorem 4.2, (ii) ⇒ (i); `Polyfold.exists_proj_goodComplement`, `Polyfold.CornerChartData`,
`Polyfold.exists_cornerChartData`, `Polyfold.CornerChartData.chart`, `Polyfold.CornerChartData.chart_isCornerChart`,
`Polyfold.CornerChartData.chart_isChart`, `Polyfold.MPolyfold.theorem_4_2_chart`,
`Polyfold.MPolyfold.hasCornerStructure_of_centred`).** If every point is smooth and $1_0^1$ is sc-smooth, then for every
chart $\psi$ of $X$ with $\psi(x) = 0$ whose tangent space $N = T_0O$ is finite-dimensional and in good position to $C$ there
are a closed good complement $Y$ of $N$, the projection $p$ along it, and $W$, $V$, $\Gamma$ of Proposition 4.9; the chart $p
\circ \psi$ on $\psi^{-1}(W)$, modelled on $(V, N \cap C, N)$, is a corner chart and a chart of $X$, with $x$ in its domain and
$(p \circ \psi)(x) = 0$. If every point has such a chart $\psi$ (tame or not), $X$ has a corner structure. *Book:* proof of
Theorem 4.2, pp. 156–157. *Hidden hypotheses:* none; the closed good complement is chosen by the normal form of
Proposition 3.22, and the compatibility of the charts $p \circ \psi$, not argued in the text, is V4.26 (Findings, items
54, 55). *Deviation (hypotheses explicit).*

**V4.29 (Definition 4.13, smooth finite-dimensional submanifolds; `Polyfold.MPolyfold.IsSmoothSubmanifold`,
`Polyfold.MPolyfold.SubmanifoldData`, `Polyfold.MPolyfold.isSmoothSubmanifold_iff`,
`Polyfold.MPolyfold.SubmanifoldData.toSubData`, `Polyfold.MPolyfold.IsSmoothSubmanifold.isSubMPolyfold`).** $A
\subseteq X$ is a *smooth finite-dimensional submanifold* if every $a \in A$ has an open $V \ni a$ and an sc⁺-retraction $s$ on
$V$ (V4.9) with $s(V) = A \cap V$. Such an $A$ is a sub-M-polyfold (Definition 2.20) and carries the induced structure of
Proposition 2.21. *Book:* Definition 4.13, p. 157. *Hidden hypotheses:* none.

**V4.30 (the sc⁺-retraction in a chart; `Polyfold.MPolyfold.SubmanifoldData.isScSmoothRetractMap_lift`,
`Polyfold.MPolyfold.SubmanifoldData.exists_chartRetraction`, `Polyfold.MPolyfold.SubmanifoldData.isScPlusRetract_image`,
`Polyfold.MPolyfold.SubmanifoldData.apply_mem_smooth`).** Let $(V, s)$ be data of Definition 4.13, $\varphi$ a chart of $X$ and
$W = V \cap \operatorname{dom}\varphi \cap s^{-1}(V \cap \operatorname{dom}\varphi)$. The lift of $\varphi \circ s \circ \varphi^{-1}$ to $E^1$ is sc-smooth from
$(\varphi(W), C, E)$ to $(O_1, C_1, E^1)$. For every retraction $r$ onto $O$ there is an open $G$ with $\varphi(W) = O \cap G$ and
an sc⁺-retraction $t$ on $U \cap r^{-1}(G)$, equal to $\varphi \circ s \circ \varphi^{-1} \circ r$ there, onto $\varphi(W \cap A)$. So
$\varphi(W \cap A)$ is an sc⁺-retract, and $\varphi(a)$ is smooth for $a \in A \cap V \cap \operatorname{dom}\varphi$. *Book:* proof of
Theorem 4.18, pp. 160–161 ("taking $V$ and $U$ small, we may assume $V = \varphi^{-1}(O)$ ... it is a sc⁺-retraction since
$s$ is"). *Hidden hypotheses:* the set $W$ of Proposition 2.21 in place of "$V = \varphi^{-1}(O)$", and the sc⁺ condition
read in the charts of $X$ and $X^1$ (Findings, item 60). *Deviation (hypotheses explicit).*

**V4.31 (Remark 4.14 in a chart; `Polyfold.MPolyfold.SubmanifoldData.remark_4_14`).** At $a \in A \cap V \cap
\operatorname{dom}\varphi$ and the level-$1$ point $z$ over $\varphi(a)$: $z$ is smooth; the tangent map of $\rho = \varphi \circ s \circ
\varphi^{-1}$ at $z$ maps $T_zO$ onto the tangent space $T_z(\varphi(W \cap A))$; this tangent space lies in $T_zO$; and it is a
finite-dimensional linear subspace. *Book:* Remark 4.14, p. 157 ("$T_aA = Ts(a)(T_aX)$ ... finite-dimensional").
*Hidden hypotheses:* $T_aX$ is read in a chart (gap G.7). *Deviation (restated):* the sc⁺-operator is $Dt(z)$ for the
chart retraction $t$ of V4.30, not $Ts(a)$.

**V4.32 (Remark 4.14 at points with $d_X = 0$; `Polyfold.isInGoodPosition_univ`,
`Polyfold.partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero`, `Polyfold.MPolyfold.isGoodPositionAt_of_degIndex_eq_zero`,
`Polyfold.MPolyfold.hasCornerStructure_of_degIndex_eq_zero`).** Every subspace is in good position to the whole space;
at a point $e \in C$ with $d_C(e) = 0$, $C_e$ is the whole space. If $a \in A$ and $d_X(a) = 0$, $A$ is in good position at
$a$ (Definition 4.16, V4.38). If $d_X = 0$ on all of $A$, the induced structure on $A$ has a corner structure; $X$ need
not be tame. *Book:* Remark 4.14, p. 157 ("near points $a \in A$ satisfying $d_X(a) = 0$, necessarily smooth
finite-dimensional manifolds in the classical sense"). *Hidden hypotheses:* none. *Deviation (narrower):* the local
form, for the open piece $A \cap \{d_X = 0\}$ of an arbitrary $A$, is not formalized (gap G.33).

**V4.33 (Proposition 4.15 (1); `Polyfold.MPolyfold.IsSmoothSubmanifold.subset_smoothSet`,
`Polyfold.MPolyfold.IsSmoothSubmanifold.mem_levelSet_subPolyfold_iff`,
`Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_1`).** $A \subseteq X_\infty$; the levels of the induced structure
are the traces of the levels of $X$; every point of $A$ is smooth for the induced structure. *Book:* Proposition 4.15
(1), p. 158. *Hidden hypotheses:* none. *Deviation (hypotheses explicit):* "$A \subseteq X_\infty$" and "$A = A_\infty$ for the
induced structure" are separated; the proof goes through the chart retraction of V4.30 and Lemma 4.7 (i).

**V4.34 (Proposition 4.15 (2); `Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_2`).** $A$ is locally closed in
$X$: the intersection of an open and a closed set (equivalently, every $a \in A$ has an open $V$ with $V \cap \overline A
\subseteq A$). *Book:* Proposition 4.15 (2), p. 158, with a garbled definition of "locally closed" (the letter $U$ used
twice). *Hidden hypotheses:* none. *Deviation (restated):* Mathlib's notion; a filter replaces the text's sequence, so
no metrizability is needed.

**V4.35 (Proposition 4.15 (3); `Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_3`).** The boundary $\{d_A \ge
1\}$ of $A$ with its induced structure lies in $\partial X = \{d_X \ge 1\}$. *Book:* Proposition 4.15 (3), p. 158. *Hidden
hypotheses:* none. *Proof:* $d_A \le d_X$ (Lemma 2.26).

**V4.36 (Proposition 4.15 (4); `Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_4`).** For the induced structure
on $A$, every point is smooth and $1_0^1 : A \to A^1$ is sc-smooth (for any junk value). *Book:* Proposition 4.15 (4), p.
158. *Hidden hypotheses:* none. *Proof:* every point of $A$ lies in an induced chart whose model $\varphi(W \cap A)$ is an
sc⁺-retract (V4.30), and V4.14 applies; the text says only that the sc⁺-retraction "is the identity on the retract $A$".

**V4.37 (tangent spaces of sub-retracts; `Polyfold.tangentSpace_inter_isOpen`, `Polyfold.tangentSpace_subset_of_subset`,
`Polyfold.scDeriv_mem_tangentSpace_of_subset`).** For a retract $Q$ and an open $K$, $T_z(Q \cap K) = T_zQ$ at points of $Q
\cap K$. For retracts $Q \subseteq O = r(U)$, $T_zQ \subseteq T_zO$. If $F \circ r$ is sc-smooth and $F$ maps the retract $Q \subseteq O$
into a retract $Q'$, then $D(F \circ r)(z)$ maps $T_zQ$ into $T_{F(z)}Q'$. *Book:* not stated. *Hidden hypotheses:* none.
*Deviation (not in the book).*

**V4.38 (Definition 4.16 in a chart; `Polyfold.IsGoodPositionRetractAt`,
`Polyfold.MPolyfold.SubmanifoldData.IsGoodPositionChart`, `Polyfold.MPolyfold.IsGoodPositionAt`,
`Polyfold.MPolyfold.SubmanifoldData.isGoodPositionChart_iff`).** For retracts $Q \subseteq O$, a presentation $T$ and a
level-$1$ point $z$: $T_zQ$ is in good position to $C_z$ inside $T_zO$ ($T_zQ \subseteq T_zO$, $T_zQ \cap C_z$ has interior
points in $T_zQ$, and $T_zQ$ has a complement $P \subseteq T_zO$ in $T_zO$ with a constant $\varepsilon$ as in Definition 3.21). $A$
is *in good position at $a \in A$* if this holds for $Q = \varphi(W \cap A)$ and the model $O$ of some chart $\varphi$ at $a$, some
data of Definition 4.13 at $a$, some presentation and the level-$1$ point over $\varphi(a)$. For retractions $r$ onto $O$
and $t$ onto $\varphi(W \cap A)$ the condition says that $Dt(z)E$ is in good position to $C_z$ inside $Dr(z)E$. *Book:*
Definition 4.16, p. 159. *Hidden hypotheses:* the chart form (gap G.7); the chart form needs no tameness. *Deviation
(restated).*

**V4.39 (the chart independence of Definition 4.16; `Polyfold.IsGoodPositionRetractAt.transport`,
`Polyfold.MPolyfold.chart_change_of_transport`, `Polyfold.MPolyfold.isGoodPositionRetractAt_chart_change`,
`Polyfold.MPolyfold.IsGoodPositionAt.isGoodPositionChart`, `Polyfold.MPolyfold.isGoodPositionAt_iff_forall`).** Good
position of a sub-retract is carried by a germ of sc-diffeomorphisms between retracts that maps the sub-retracts into
each other. Hence if $A$ is in good position at $a$, the chart condition holds for every data of Definition 4.13 at $a$,
every chart at $a$, every presentation and the level-$1$ point over the image of $a$; and good position at $a$ is
equivalent to the condition for all of them. *Book:* implicit in Definition 4.16. *Hidden hypotheses:* none.
*Deviation (not in the book).*

**V4.40 (Definition 4.17; `Polyfold.MPolyfold.IsTameSubmanifold`).** $A$ is a *tame* submanifold if it is a smooth
finite-dimensional submanifold whose induced M-polyfold structure is tame. *Book:* Definition 4.17, p. 159. *Hidden
hypotheses:* none.

**V4.41 (Theorem 4.18; `Polyfold.MPolyfold.theorem_4_18`,
`Polyfold.MPolyfold.hasCornerStructure_of_centred_isInGoodPosition`,
`Polyfold.MPolyfold.IsGoodPositionAt.isInGoodPosition_of_tame`).** Let $X$ be tame and $A$ a smooth finite-dimensional
submanifold in good position at every point. Then the induced structure on $A$ has a corner structure (Definition 4.1)
and $A$ is tame. More generally, the induced structure has a corner structure as soon as every $a \in A$ lies in a chart
$\psi$ of $X$ with $\psi(a) = 0$ in which $T_0(\psi(W \cap A))$ is in good position to $C$ in $E$; and good position at $a$ gives
this in every tame chart centred at $a$. *Book:* Theorem 4.18, p. 159; proof pp. 160–161. *Hidden hypotheses:* none.
*Proof:* the text's route through Theorem 4.2, with the steps it skips: the centred chart (V4.17), the chart retraction
(V4.30), the closed complement (V4.28) and the compatibility of the charts $p \circ \psi$ (V4.26); tameness of $X$ enters only
through Lemma 4.19.

**V4.42 (Lemma 4.19; `Polyfold.isGoodComplement_sup_range`, `Polyfold.lemma_4_19`,
`Polyfold.IsInGoodPositionIn.isInGoodPosition`).** Let $T$ present $C$, $\pi$ a bounded idempotent with $(1 - \pi)E_0 \subseteq
E_0^{\min}$, the minimal subspace at $0$ ($\{\lambda = 0\}$), and $N$ in good position to $C$ inside $\pi E_0$. Then $N$ is in good
position to $C$ in $E_0$, and for every good complement $Y$ of $N$ inside $\pi E_0$ with constant $\varepsilon$, $Y \oplus (1 - \pi)E_0$
is a good complement of $N$ in $E_0$, with constant $\varepsilon/(\|\pi\| + 1)$. *Book:* Lemma 4.19, p. 160. *Hidden
hypotheses:* $(1 - \pi)E_0$ lies in the minimal subspace at the corner $0$ of the centred chart (Proposition 2.35), not
merely in $C$. *Deviation (hypotheses explicit):* the text concludes $n + y \in C$ from $n + y + z \in C$ "since $z \in Z \subset
C$", which is false ($C = [0, \infty)$, $z = 1$, $n + y = -\frac12$); it holds because $Z \subseteq C \cap (-C)$. The text's norm
$|y|_0 + |z|_0$ is replaced by the constant $\varepsilon/(\|\pi\| + 1)$ (Findings, item 69).

**V4.43 (Remark 4.20; `Polyfold.tangentSpace_eq_range_graph`, `Polyfold.lemma_3_55_relOpen`,
`Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le`, `Polyfold.MPolyfold.remark_4_20`).** If the retract $Q$ is the
image of an sc-diffeomorphism $\Gamma$ from $(V, N \cap C, N)$ with inverse $p$, then at $v \in V$ and the level-$1$ point $y$ over
$\Gamma(v)$, $T_yQ = D\Gamma(v)N$ and $p \circ D\Gamma(v) = 1$. For $X$ tame and $A$ in good position at $a$, there is an open $U \ni
a$ such that $A$ is in good position at every point of $U \cap A$. *Book:* Remark 4.20, p. 161, without "tame".
*Hidden hypotheses:* $X$ tame (Definition 4.16 is stated for tame $X$; Lemma 4.19 is used). *Deviation (hypotheses
explicit):* "the tangent spaces move only slowly" is $D\sigma(0) = 0$ for $\Gamma = 1 + \sigma$, and Lemma 3.55 is applied
with the closed complement of the normal form.

**V4.44 (Definition 4.21 in a chart; `Polyfold.IsGeneralPositionRetractAt`,
`Polyfold.MPolyfold.SubmanifoldData.IsGeneralPositionChart`, `Polyfold.MPolyfold.IsGeneralPositionAt`).** For retracts $Q
\subseteq O$, a presentation $T$ and a level-$1$ point $z$: there is an sc-subspace $B \subseteq T_zO \cap E_z$ with $(T_zO)_m =
(T_zQ)_m \oplus B_m$ on every level $m$ ($T_zO \cap E_z = T^R_zO$). $A$ is *in general position at $a \in A$* if this holds for $Q
= \varphi(W \cap A)$ and the model of some chart at $a$, some data, presentation and lift. *Book:* Definition 4.21, p. 161.
*Hidden hypotheses:* the sc-structure of $T_zO$ is the one induced from $E$ at the smooth point; the chart form (gap
G.7). *Deviation (restated).*

**V4.45 (the chart independence of Definition 4.21; `Polyfold.IsGeneralPositionRetractAt.transport`,
`Polyfold.MPolyfold.isGeneralPositionRetractAt_chart_change`,
`Polyfold.MPolyfold.IsGeneralPositionAt.isGeneralPositionChart`, `Polyfold.MPolyfold.isGeneralPositionAt_iff_forall`).**
General position of a sub-retract is carried by a germ of sc-diffeomorphisms at a smooth point; hence general position
at $a$ holds in every chart, for every data, presentation and lift, and is equivalent to the condition for all of them.
*Book:* implicit in Definition 4.21. *Hidden hypotheses:* the point is smooth (true on $A$). *Deviation (not in the
book).*

**V4.46 (linear algebra at the corner of a centred chart; `Polyfold.mem_minimalSubspaceWith_zero`,
`Polyfold.minimalSubspaceWith_zero_le`, `Polyfold.add_mem_iff_of_mem_zero`, `Polyfold.degIndexWith_add_of_mem_zero`,
`Polyfold.coordsOn_surjective`, `Polyfold.exists_isClosed_isCompl_le`, `Polyfold.exists_goodComplement_le_zero`,
`Polyfold.degIndex_slice`).** For $C = T^{-1}([0, \infty)^n \oplus W)$: the minimal subspace at $0$ is $E_0^{\min} = \{\lambda = 0\}$ and
lies in every $E_x$; adding a vector of $E_0^{\min}$ changes neither membership in $C$ nor the degeneracy index. For a
finite-dimensional $N$ with $N + E_0^{\min} = E_0$: $\lambda|_N$ is onto $\mathbb R^n$, $N$ is in good position to $C$ with a closed good
complement $Y \subseteq E_0^{\min}$, and $d_{N \cap C}(v) = d_C(v)$ for $v \in N \cap C$. A finite-dimensional $N$ and a closed $K$ with $N + K$
the whole space give a closed complement of $N$ inside $K$. *Book:* proof of Theorem 4.22, pp. 162–163 ("$T_0A$ has in
$E$ an sc-complement $Y$ contained in $W$"). *Hidden hypotheses:* $Y$ closed. *Deviation (restated):* the text's
splitting $T_0A = N \oplus (T_0A \cap W)$ is replaced by the coordinates $\lambda|_{T_0A}$ (Findings, items 82, 83).

**V4.47 (Lemma 7.A of the exposition, and general position from $T_yQ + E_0^{\min} = E_0$;
`Polyfold.exists_scComplement_le`, `Polyfold.isGeneralPositionRetractAt_of_sup_eq_top`).** (a) For $N \subseteq E_\infty$
finite-dimensional, an sc-subspace $R$ and $M = N + R$, there is an sc-subspace $B \subseteq R$ with $M_m = N_m \oplus B_m$ on every level.
(b) For $r$ tame, a retract $Q \subseteq O$, a smooth $y \in Q_1$ with $T_yQ$ finite-dimensional, contained in $E_\infty$ and $T_yQ +
E_0^{\min} = E_0$, the retract $Q$ is in general position at $y$ in $O$. *Book:* proof of Theorem 4.22 (3), p. 164 ("$T_aO
= T_aA + T^R_aO$, implying that $T_aA$ has in $T_aO$ a sc-complement contained in $T^R_aO$"). *Hidden hypotheses:*
$T^R_yO$ an sc-subspace (Proposition 2.36, for tame retracts). *Deviation (hypotheses explicit).*

**V4.48 (general position implies good position; `Polyfold.IsGeneralPositionRetractAt.isGoodPositionRetractAt`).** For
$r$ tame and a smooth $z \in O_1$, if $Q$ is in general position at $z$ in $O$, it is in good position at $z$. *Book:* not
stated; needed for the tameness in Theorem 4.22 (4) and for Theorem 4.23. *Hidden hypotheses:* none. *Deviation (not in
the book).*

**V4.49 (Theorem 4.22 in a tame chart centred at the point; `Polyfold.sup_minimalSubspaceWith_eq_top`,
`Polyfold.sup_minimalSubspaceWith_eq_top_graph`, `Polyfold.theorem_4_22_chart`).** Let $r$ be tame onto $O \ni 0$, $t$ an
sc⁺-retraction onto $Q \subseteq O$ with $0 \in Q$, and $N = T_0Q$, with $Q$ in general position at $0$. Then $N + E_0^{\min} = E_0$, $N$
is in good position to $C$, $N$ has a closed good complement $Y \subseteq E_0^{\min}$ with a projection $p$ whose kernel is exactly
$Y$, and the data $W$, $V$, $\Gamma$ of Proposition 4.9 exist for this $Y$, with (2) $d_{N \cap C}(v) = d_C(\Gamma(v))$ on $V$ and (3)
general position of $Q$ at every level-$1$ point over $Q \cap W$. *Book:* proof of Theorem 4.22, pp. 162–164. *Hidden
hypotheses:* none. *Deviation (restated):* $T_yQ + E_0^{\min} = E_0$ along the graph comes from $p \circ D\Gamma(v) = 1$ and $\ker p
= Y$ (the text: "by means of the particular form of the map $\alpha$").

**V4.50 (Theorem 4.22, local structure in general position; `Polyfold.MPolyfold.theorem_4_22`).** Let $X$ be tame, $A$ a smooth
finite-dimensional submanifold, in general position at $x \in A$. There are a chart $\psi$ of $X$ with $\psi(x) = 0$, a tame
retraction $r$ onto its model for a presentation $T$ with $n$ half-line coordinates, and an open $U \ni x$ inside the domain of
$\psi$ with: (1) $d_X(x) = n$, and $\psi(x)$ lies in exactly $d_X(x)$ faces of the M-polyfold $O$; (2) $d_X(a) = d_A(a)$ for
$a \in A \cap U$ ($d_A$ for the induced structure); (3) $A$ is in general position at every point of $A \cap U$; (4) for every
$\sigma \subseteq \{1, \dots, n\}$ there are faces $F_i \ni 0$ of the retract ($i \in \sigma$, $F_i$ in the coordinate hyperplane
$\lambda_i = 0$) and an open $G \ni 0$ such that $F_\sigma = \psi^{-1}(G \cap \bigcap_{i \in \sigma}F_i)$ contains $x$, lies in
$U$, and is a tame sub-M-polyfold with $d_{F_\sigma} + \#\sigma = d_X$ on it, and $A \cap F_\sigma$ is a smooth finite-dimensional
submanifold of $F_\sigma$, in general position in $F_\sigma$ at each of its points, and tame. *Book:* Theorem 4.22, p. 162; proof
pp. 162–164. *Hidden hypotheses:* the chart is re-centred at $x$; "smooth submanifold" is finite-dimensional. *Deviation
(restated):* (1) is a statement about the chart model (local faces are not identified with global faces, gap G.35); $F_\sigma$ is
a germ, taken inside $U$; (4), without proof in the text, is V4.51, V4.52. (1) and (4) differ from the text's in content, not only
in form: the text's local faces are faces of the neighbourhood $U$ itself (the closures in $U$ of the components of
$U \cap \{d_X = 1\}$, all through $x$), the formal ones faces of the model retract of the chart; (2) and (3) are the text's.
Identifying the two needs a local face theorem for small neighbourhoods, believed true for tame $X$ and not formalized (Findings,
Chapter 4, items 90, 130; round-trip item V4.50).

**V4.51 (Theorem 4.22 (4) in the chart; `Polyfold.killOn`, `Polyfold.exists_scPlus_retraction_corner`,
`Polyfold.exists_cornerModel_retraction`, `Polyfold.theorem_4_22_four_chart`).** In the situation of V4.49, for $\sigma \subseteq \{1,
\dots, n\}$ and an open $B \ni 0$: with $\kappa_\sigma(v) = v - s(\lambda(v)1_\sigma)$ ($s$ a linear section of $\lambda|_N$) there are an open $G
\ni 0$, $G \subseteq W \cap B$, and an sc⁺-retraction $t_\sigma = \Gamma \circ \kappa_\sigma \circ p \circ t$ onto $Q \cap G \cap f_\sigma$, $f_\sigma = \{\lambda_i =
0, i \in \sigma\}$, whose tangent spaces contain $T_yQ \cap f_\sigma$. A retraction onto a subset of $f_\sigma$ has a corner model on
$[0, \infty)^{n - \#\sigma} \oplus W$, sc⁺ if the retraction is. For every open $B_0 \ni 0$ there are faces $F_i \ni 0$ ($i \in \sigma$) and
an open $G \ni 0$, $G \subseteq W \cap B_0$, such that $O \cap G \cap f_\sigma$ is the retract of a retraction whose corner model is tame
with $d_{C'}(\pi_\sigma y) + \#\sigma = d_C(y)$, $Q \cap G \cap f_\sigma$ and its corner model are sc⁺-retracts, and the corner model of $Q \cap
G \cap f_\sigma$ is in general position at each of its level-$1$ points. *Book:* not in the text ("the previous arguments, but
now applied to $A \cap F_\sigma$, conclude the proof"). *Hidden hypotheses:* none. *Deviation (not in the book).*

**V4.52 (sc⁺-retractions in a chart, and Theorem 4.22 (4) for one $\sigma$;
`Polyfold.MPolyfold.isScPlusRetractionOn_of_chart`, `Polyfold.MChart.cornerPreimage`,
`Polyfold.MPolyfold.theorem_4_22_four_of_chart`).** For a chart $\chi$ of $X$ and an sc⁺-retraction $\tau$ of its model with
$\tau(U) \subseteq O$, $\chi^{-1} \circ \tau \circ \chi$ is an sc⁺-retraction on the open set $\chi^{-1}(\tau.U)$ with image $\chi^{-1}(\tau(U))$.
In a tame chart $\psi$ centred at $x$ with the data of V4.49 for the chart retraction of $A$, for every $\sigma$ there are faces
$F_i \ni 0$ and an open $G \ni 0$ such that $\psi^{-1}(G \cap \bigcap_{i \in \sigma}F_i)$ contains $x$, lies in the open set $W$ of the
submanifold chart, and has the properties (4) of V4.50. *Book:* not in the text. *Hidden hypotheses:* none.
*Deviation (not in the book).*

**V4.53 (the family $\mathbb R^m \times X$ and stratified regular points; `Polyfold.prod_rn_isTame`, `Polyfold.fibreSet`,
`Polyfold.rnPres`, `Polyfold.IsStratRegularPoint`, `Polyfold.IsStratRegularValue`).** For tame $X$, $\mathbb R^m \times X$ with the
product charts is tame. The fibre of $A \subseteq \mathbb R^m \times X$ over $\lambda$ is $A_\lambda = \{x : (\lambda, x) \in A\}$. A point $z \in A$ is a
*stratified regular point* if, for some data of Definition 4.13 at $z$, some $a \in \mathbb R^m$, some chart $\varphi$ of $X$ at $z_2$,
some presentation $T$ of its partial quadrant and the level-$1$ point $y$ over the image of $z$ in the product chart $(r
\mapsto r - a) \times \varphi$, every $\mu \in \mathbb R^m$ is the first component of a tangent vector $v$ of the chart model of $A$ at $y$ with
$v_2 \in E_{\varphi(z_2)}$ (the projection maps $T_zA \cap E_z$, the tangent space of the stratum through $z$, onto $\mathbb R^m$); $\lambda$
is a *stratified regular value* if every $z \in A$ over $\lambda$ is a stratified regular point. *Book:* §4.3, p. 164, and the
proof of Theorem 4.23, p. 166 ("regular values of $p_\sigma$"). *Hidden hypotheses:* the chart form (gap G.7).
*Deviation (restated):* the chart independence is not formalized (gap G.36).

**V4.54 (Theorem 4.23; `Polyfold.theorem_4_23`).** Let $X$ be tame and $A$ a smooth finite-dimensional submanifold of
$\mathbb R^m \times X$ with tame induced structure and compact closure, $\varepsilon > 0$, and suppose (1) for $|\lambda| \le \varepsilon$ ($|\lambda|^2 =
\sum\lambda_i^2$) the set $A \cap \{z_1 = \lambda\}$ is compact and non-empty, (2) $A$ is in general position at every point. Then there is
$\Sigma \subseteq \{|\lambda| < \varepsilon\}$ whose complement in $\{|\lambda| < \varepsilon\}$ is Lebesgue-null, consisting of stratified regular values,
such that for $\lambda \in \Sigma$ the fibre $A_\lambda$ is compact, a smooth finite-dimensional submanifold of $X$, in general position at
each of its points, and its induced structure has a corner structure and is tame. *Book:* Theorem 4.23, p. 165; proof
pp. 165–166. *Hidden hypotheses:* hypothesis (2), misprinted in the text ("there exists a sc-complement $T_zA$ in $T_zZ$"),
is Definition 4.21. *Deviation (stronger):* $\Sigma$ consists of stratified regular values, which are regular values; the
tameness of $A$, the non-emptiness in (1) and $\varepsilon > 0$ are not used, and $A_\lambda$ is moreover tame. With ordinary regular
values the conclusion fails at the value: in $\mathbb R \times [0, \infty)$, $A = \{(x, x) : 0 \le x < 1\} \cup (-1, 1) \times \{5\}$ satisfies
the hypotheses, $Dp$ is onto everywhere, and $A_0 = \{0, 5\}$ meets $\partial X$ (Findings, item 102).

**V4.55 (Remark 4.24; `Polyfold.quotDim_le_finrank_of_eq_sup`, `Polyfold.remark_4_24_chart`,
`Polyfold.MPolyfold.remark_4_24_codim`, `Polyfold.MPolyfold.remark_4_24`,
`Polyfold.MPolyfold.remark_4_24_not_mem_boundary`).** For tame $X$ and smooth $x$, in a tame chart at $x$ the reduced tangent
space has codimension $d_X(x)$ in the tangent space. If $A$ is in general position at $a$, then $d_X(a) \le \dim T_aA$ (in any
tame chart at $a$); in particular a submanifold in general position with $T_aA = 0$ does not meet $\partial X$ at $a$. *Book:*
Remark 4.24, p. 165. *Hidden hypotheses:* $X$ tame and $x$ smooth for the codimension. *Deviation (hypotheses
explicit):* stated for any submanifold in general position, not only for the $A_\lambda$ of Theorem 4.23 (to which it applies by
V4.54).

**V4.56 (Sard's theorem, vendored; `Polyfold.MilnorSard.Sard.critSet`, `Polyfold.MilnorSard.Sard.sardStatement`,
`Polyfold.MilnorSard.sard`, `Polyfold.MilnorSard.dense_compl_image_critSet`).** Let $E$, $F$ be finite-dimensional real
normed spaces (in the same universe), $F$ with its Borel σ-algebra and a Haar measure $\mu$, $U \subseteq E$ open and $f$ of class
$C^\infty$ on $U$. Then $\mu(f(\mathrm{Crit})) = 0$, where $\mathrm{Crit}$ is the set of points of $U$ at which $Df$ is not onto, and the
complement of $f(\mathrm{Crit})$ is dense. *Book:* "Sard's theorem", proof of Theorem 4.23, p. 166, without statement.
*Hidden hypotheses:* Mathlib has only the cases $\dim E \le \dim F$; the general case is Milnor's induction, copied from the
Milnor project (`math_faithful`) with only the namespace changed (Findings, item 100). *Deviation (not in the book).*

**V4.57 (the strata and Sard's theorem on them; `Polyfold.quadC`, `Polyfold.stratSub`, `Polyfold.zeroSetOf`,
`Polyfold.finrank_stratSub`, `Polyfold.stratCritSet`, `Polyfold.measure_image_stratCritSet`).** Let $V$ be finite-dimensional
with linear coordinates $\ell : V \to \mathbb R^n$ and $C = \{\ell \ge 0\}$. The stratum subspace of $\sigma$ is $\{\ell_i = 0, i \in \sigma\}$, of
dimension $\dim V - \#\sigma$ when $\ell$ is onto; $\sigma(v) = \{i : \ell_i(v) = 0\}$. For $f$ of class $C^\infty$ on $U = O \cap C$ ($O$ open)
into a finite-dimensional $F$, the stratified critical points are the $v \in U$ at which $Df(v)$ restricted to the stratum
subspace of $\sigma(v)$ is not onto, and their image is null for every Haar measure. *Book:* proof of Theorem 4.23, pp.
165–166 ("$A \cap F_\sigma^\circ$ is a smooth manifold ... of dimension $\dim(A) - \#\sigma$"; "Using Sard's theorem we find a subset
$\Sigma_\sigma$ ... having full measure"). *Hidden hypotheses:* the dimension count, which Theorem 4.22 does not state (the text
cites "Theorem 4.23" for it). *Deviation (restated):* in the model space $T_0A$ of the chart.

**V4.58 (Theorem 3.78 in $C^\infty$ form; `Polyfold.ContractionData.exists_solution_smooth`,
`Polyfold.theorem_3_78_smooth`).** Under the hypotheses of Theorem 3.78 (V3.63) with $f$ of class $C^\infty$, one solution $\tau$
is $C^\infty$ on $V'$, with the other conclusions of V3.63 (including the uniqueness clause). *Book:* Theorem 3.78, p. 141,
states one $j$; the proof of Theorem 4.23 needs $C^\infty$. *Hidden hypotheses:* none. *Deviation (stronger):* the
contraction radii of Lemmas 3.79, 3.80 and the fixed point do not depend on $j$.

**V4.59 (the kernel at a stratified regular point is in good position; `Polyfold.quadAt`,
`Polyfold.isPartialQuadrant_quadAt`, `Polyfold.exists_goodComplement_stratSub`).** For $\ell$ onto, $\{\ell_i \ge 0, i \in \sigma\}$ is a
partial quadrant. If $K + \{\ell_i = 0, i \in \sigma\} = V$, then $K$ is in good position to $\{\ell_i \ge 0, i \in \sigma\}$ with a closed good
complement inside the stratum subspace. *Book:* not in the text here; the argument of Lemma 5.26. *Hidden hypotheses:*
none. *Deviation (not in the book).*

**V4.60 (a retraction onto the fibre over a stratified regular point; `Polyfold.exists_fibre_retraction`).** For $\ell$ onto,
$f$ of class $C^\infty$ on $O \cap C$ and $v_0 \in O \cap C$ not stratified-critical, there are an open $O' \ni v_0$, $O' \subseteq O$, and a
map $\rho$, $C^\infty$ on $O' \cap C$, mapping $O' \cap C$ into itself and into $f^{-1}(f(v_0))$, equal to the identity on $O' \cap C
\cap f^{-1}(f(v_0))$, with $D\rho(v_0)$ of range $\ker Df(v_0)$ and equal to the identity there. *Book:* "for $\lambda \in \Sigma$ ... $A_\lambda$ is
a smooth compact manifold with boundary with corners", p. 166, in the model. *Hidden hypotheses:* none. *Deviation (not
in the book):* the implicit function theorem at corner points (V4.58 with V4.59).

**V4.61 (the sc⁺-retraction onto $A_\lambda$; `Polyfold.isScSmooth_slice`, `Polyfold.scDeriv_slice`,
`Polyfold.exists_slice_retraction`).** In the model $\mathbb R^m \oplus E$ of a product chart, let $t$ be an sc⁺-retraction
described near a point as the graph $\Gamma : V \to t(U) \cap W$ with inverse $p$ (Proposition 4.9), and $\rho$ a $C^\infty$ retraction of
$O' \cap (\mathbb R^m \times C)$ onto the points $v$ with $\Gamma(v)_1 = c$. Then $\tau(e) = (\Gamma(\rho(p(t(c, e)))))_2$ is an sc⁺-retraction of
$E$ (partial quadrant $C$) onto $\{e : (c, e) \in t(U) \cap W, p(c, e) \in O'\}$; if $D\rho(v_0) = 1$ on $\{h : (D\Gamma(v_0)h)_1 = 0\}$, the
tangent space of its retract at the point over $\Gamma(v_0)_2$ contains $(D\Gamma(v_0)h)_2$ for all such $h$. The slice $e \mapsto (c, e)$
is sc-smooth with derivative $h \mapsto (0, h)$. *Book:* not constructed (Definition 4.13 requires it). *Hidden hypotheses:*
none. *Deviation (not in the book).*

**V4.62 (general position of $A_\lambda$; `Polyfold.isGeneralPositionRetractAt_slice`).** In a product chart with $r_X$ tame: if
the chart model of $A$ is in general position at $z = (c, y)$, the projection maps the tangent space of the stratum $T_zA \cap E_z$
onto $\mathbb R^m$, and $\tau$ is an sc⁺-retraction onto $Q \subseteq O$ whose tangent space at the smooth $y$ contains the second components
of the tangent vectors of $A$ at $z$ with first component $0$, then $Q$ is in general position at $y$. *Book:* proof of Theorem
4.23, p. 166 ("in view of the assumption (2) ... $T_{z'}(\{\lambda\} \times A_\lambda)$ has a sc-complement in $T^R_{z'}X$"). *Hidden
hypotheses:* stratified regularity at $z$ itself. *Deviation (restated).*

**V4.63 (the local step of Theorem 4.23; `Polyfold.FibreLocal`, `Polyfold.exists_local_family`).** Let $X$ be tame and $A
\subseteq \mathbb R^m \times X$ a smooth finite-dimensional submanifold in general position at every point. Every $z_0 \in A$ has an open
neighbourhood $U$ and a Lebesgue-null $\mathrm{CV} \subseteq \mathbb R^m$ such that at every $z \in A \cap U$ with $z_1 \notin \mathrm{CV}$: $z$ is a
stratified regular point, $A_{z_1}$ is near $z_2$ the image of an sc⁺-retraction on an open subset of $X$, and $A_{z_1}$ is in
general position and in good position at $z_2$. *Book:* proof of Theorem 4.23, pp. 165–166, in one $U(z)$. *Hidden
hypotheses:* none. *Deviation (restated):* in the product chart of a tame chart of $X$ centred at $z_{0,2}$, through V4.49,
V4.57, V4.60–V4.62.

**V4.64 (the countable cover: Theorem 4.23 for any parameter set; `Polyfold.theorem_4_23_of_subset`).** For $X$ tame, $A \subseteq
\mathbb R^m \times X$ a smooth finite-dimensional submanifold with compact closure, in general position at every point, and any $S \subseteq
\mathbb R^m$, there is $\Sigma \subseteq S$ with $S \setminus \Sigma$ Lebesgue-null such that every $\lambda \in \Sigma$ is a stratified regular value and the
conclusions of V4.63 hold at every point of $A_\lambda$. *Book:* proof of Theorem 4.23, p. 165 ("We cover the set $\{z \in A : |p(z)|
\le \varepsilon\}$ with the finitely many such neighborhoods"). *Hidden hypotheses:* none. *Deviation (stronger):* any $S$; the text's
set need not be compact and need not have a finite subcover (in $\mathbb R \times \mathbb R$, $A = (-2\varepsilon, 2\varepsilon) \times \{2\} \cup \{(\varepsilon(1 -
x), x) : 0 < x < 1\}$); $A$ is second countable, its closure being compact in the metrizable $\mathbb R^m \times X$, and countably many
neighbourhoods cover it (Findings, item 103).

### What is not verified in this chapter

- p. 151, Lemma 4.10 (the section $u \mapsto (1 - p)(u - t(u))$ of $U \triangleleft Y$ is sc-Fredholm): not formalized, because no
  longer used — Proposition 4.9 is proved directly (V4.20). It would need $U \triangleleft Y$ as a strong bundle, $Y$ and $Y \cap F$ as
  sc-subspaces, and at each smooth point the re-centred strong bundle chart, filler and conjugation (gap G.32).
- pp. 167–168, §4.4 in full: Definitions 4.25, 4.27, Proposition 4.26, the exterior derivative and the relative
  complex, Theorem 4.28. It needs $\oplus^kTX$ as an M-polyfold and a linear $T_xX$ (gap G.7), the M-polyfolds $X^i$ for $i \ge 2$
  (gap G.6), and integration on manifolds with corners of varying dimension, which Mathlib lacks; Proposition 4.26 is quoted
  from another paper, $d^2 = 0$ is asserted, and Theorem 4.28 has no proof in the text (gaps G.37–G.40).
- p. 159, the open question after Proposition 4.15: a question, not a statement. Its last sentence, for a retract without
  boundary, is V4.32 with $A = O$; that the "T" is not a topological manifold is not formalized (gap G.34).
- p. 148, Remark 4.3: why an example of "$X^1 \ne X$" needs a retraction whose first derivative loses a level (one whose level
  maps are $C^1$ gives none, by a Baire category argument): not formalized; the example itself is verified (V4.6; Findings,
  item 141).
- The chart independence of stratified regularity (V4.53): true by the transport argument of V4.39, since the transition
  maps of product charts are $\mathrm{id} \times \tau$ up to translation, but not formalized; Theorem 4.23 states it for some chart
  (gap G.36).
- p. 157, Remark 4.14, the local form "near points with $d_X(a) = 0$ $A$ is a classical manifold" for the open piece $A \cap \{d_X =
  0\}$ of an arbitrary $A$: verified when $d_X = 0$ on all of $A$ (V4.32), not for the piece (gap G.33).
- p. 162, Theorem 4.22 (1) and (4) for the local faces of the neighbourhood $U$ itself: the identification of the faces of the
  chart model with (germs of) global faces of $X$, a local face theorem for small neighbourhoods; (1) and (4) are verified for the
  chart (V4.50) (gap G.35; Findings, Chapter 4, item 130).
- Definition 4.1: the classical manifold structure beyond the $C^\infty$ property of the transition maps, and the local
  constancy of the dimension (V4.1, V4.2).
- Definitions 4.16, 4.21 and Remark 4.14 in $T_aX$: verified in charts, with chart independence (V4.38, V4.39, V4.44, V4.45),
  since $T_aX$ carries no linear structure here (gap G.7 of Chapter 2).

---

## 6. Chapter 5 (HWZ §§5.1–5.4): verified except Theorems 5.22, 5.27 and the cited Theorems 5.32, 5.40, 5.43

Chapter 5 of Part I (preprint pp. 169–199) is the Fredholm package for M-polyfolds. §5.1 introduces auxiliary norms
on the part $Y_{0,1}$ of biregularity $(0, 1)$ of a strong bundle (Definition 5.1, Lemma 5.2, Proposition 5.3). §5.2
defines compact solution sets, weakly proper and proper sections (Definition 5.4) and proves that the three agree for
sc-Fredholm sections (Theorem 5.5, proof in Appendix 5.4.1), that solution sets are locally compact on every level
(Theorem 5.6) and compact in $X_\infty$ (Theorem 5.7), and that the shifted sections are sc-Fredholm (Corollary 5.8).
§5.3 builds sc⁺-sections from sc-smooth bump functions (Definition 5.9, Proposition 5.10, Lemma 5.11), introduces the
allowable sections $\Gamma^{+,1}_U(P)$ (Remark 5.12), and proves the perturbation theorems: transversality when $\partial X =
\emptyset$ (Theorem 5.13, Definition 5.15), general position (Definition 5.17, Theorem 5.18), good position relative to the
boundary (Theorem 5.19), the Morse-type structure of homotopies (Definition 5.20, Theorem 5.22 with Lemmas 5.23, 5.24),
perturbation into good position (Theorem 5.25, Lemma 5.26) and cobordisms (Theorem 5.27). Appendix 5.4.2 discusses
sc-smooth bump functions and partitions of unity (Definitions 5.28–5.41, Theorems 5.32–5.43, Corollary 5.44).

What is verified. **Theorems 5.5, 5.6, 5.7, 5.13, 5.18, 5.19, 5.25, 5.34, 5.37 hold**, with the readings recorded
below, and so do Lemmas 5.2, 5.11, 5.23, 5.24, 5.26, Propositions 5.3, 5.10, 5.30, 5.35, 5.38, 5.42, Remark 5.12,
Corollary 5.8 (for each fixed $i$) and Corollary 5.44 (with Theorem 5.43 as an explicit hypothesis). Every definition of the chapter is formalized:
Definitions 5.1 (V5.3), 5.4 (V5.7), 5.9 and 5.29 (V5.16), 5.15 (V5.23), 5.17 (V5.31), 5.20 (V5.41), 5.28 (V5.47),
5.31 (V5.50), 5.33 (V5.51), 5.36 (V5.54), 5.39 (V5.59), 5.41 (V5.60). Corollary 5.8 is verified on the shifted strong
bundle $P^1 : Y^1 \to X^1$, which the text uses without defining it, and by iteration for every fixed $i$, with the
filler condition on level $1$ that its "it is a priori clear" hides (V5.13, V5.14). Theorems 5.5–5.7, Corollary 5.8 and
Lemma 5.11 need no tameness (V5.10–V5.14, V5.20). Several places of the text needed more than a reading. (a) *Tameness.* The §3.6 implicit function
theorems are proved for sections whose germ data lie in a tame strong bundle chart (Definitions 3.50, 3.51; Chapter 3,
Findings 190–199); Theorems 5.13, 5.18, 5.19, 5.25 take $f$ with tame germ data, the reading of the tame strong bundle
with which §5.3 opens, and nothing else (Findings 74–78). Theorem 5.18 also assumes $X$ tame, which its proof uses
through Theorems 4.22 and 4.23 (V5.38). (b) *"Generic" and "dense".* The perturbations are $s_0 + \sum\lambda_it_i$ for
$\lambda$ outside a Lebesgue null set of a small ball (V5.29, V5.38), and density is the bound $\rho(s, s') = \sup_x
N(s(x) - s'(x)) \le \varepsilon$ in the metric space of $\rho$ (V5.21, V5.30, V5.39). (c) *Omitted steps proved.* The spanning sections
(V5.24), the compactness that keeps the zeros of small perturbations near $\{0\} \times S_{f+s_0}$ (V5.27), the
parametrized solution set as a smooth submanifold in the sense of Definition 4.13 (V5.32), $T_yS = \ker f'(y)$ and with it
the chart independence of Definition 5.17 (V5.33, V5.34), the openness of general position (V5.35), and the properties
(i)–(ii) of the proof of Theorem 5.18 (V5.36). (d) *Repairs.* Definition 5.9 is read with $f(x) \ne 0$ (V5.16), which
the weak reading gives at the smooth points of an sc-Banach space (V5.16); "$(\Gamma^{+,1}_U(P), \rho)$ is not complete"
is false without a hypothesis and is proved in general, by an example (V5.21); the
function $\sigma$ of Proposition 5.30 is misprinted (V5.17); the extension by $0$ in Theorem 5.34 and both directions of
Theorem 5.37 need smaller charts (V5.52, V5.55, V5.56); Proposition 5.38 is not "an immediate consequence of Theorem 5.37"
(V5.58). (e) *Theorem 5.19* is proved without applying the implicit function theorem to the parametrized section at the
boundary zeros, where it is in general not in good position (V5.40; Finding 88, on paper). (f) *Lemma 5.23* exposes a
hidden hypothesis of Theorem 5.22, $dt(x) \ne 0$ (V5.42). Not verified: Theorems 5.22 and 5.27, Remarks 5.14, 5.16,
5.21, the cited Theorems 5.32, 5.40, 5.43, the Sobolev remark and a dense form of Theorem 5.19 (see the list at the end of
this section). A fourth addendum (2026-11-02: the shifted strong bundle and Corollary 5.8, the metric $\rho$, weak against
pointwise bump functions; Findings, items 140–164) updated V5.13, V5.14, V5.16, V5.21, V5.22 and V5.30 in place.

The setting. A section of $P : Y \to X$ is a map $s : X \to Y$ with $P \circ s = \mathrm{id}$; its support is the closure of
$\{s \ne 0\}$. $X$ and $Y$ are paracompact Hausdorff spaces, as for every M-polyfold of the project. $Y_{0,1}$ is the
M-polyfold $Y[1]$ of §2.5, an auxiliary norm is a function on it, and "$N(y) \le r$" for a point $y$ of $Y$ includes $y \in
Y_{0,1}$ (the text's convention $N(y) = \infty$ off $Y_{0,1}$). The linearization $f'(x) : T_xX \to Y_x$ is read in a strong
bundle chart, as the operator $\mathrm{Lin}(z) : T_zO \to K_z$ of Chapter 3, because $T_xX$ carries no linear structure here
(gap G.7 of Chapter 2); transversality is chart independent (Chapter 3), and general position is shown chart independent
at the zeros near a zero in good position (V5.34). In the perturbation theorems $|\lambda|$ is the maximum norm on $\mathbb
R^m$, and "the solution set is a manifold" is stated for a non-empty solution set (the empty set is trivially one).
Findings referred to below are those of `Exposition/Findings.md`, "Chapter 5".

**V5.1 (the charts $\Phi[1]$ for every strong bundle chart; `Polyfold.StrongBundle.oneChartOf`,
`Polyfold.StrongBundle.isChart_oneChartOf`, `Polyfold.StrongBundle.oneChartOf_compatible`,
`Polyfold.StrongBundle.mem_oneSet_iff_of_isChart`).** For every strong bundle chart $\Phi$ of $P$ compatible with the atlas
(not only those of the atlas), a point $y$ in its domain lies in $Y_{0,1}$ iff the fibre component of $\Phi(y)$ lies in $F_1$;
the map $\Phi[1] : P^{-1}(V) \cap Y_{0,1} \to K[1]$ is a chart of the M-polyfold $Y[1]$, and the charts $\Phi[1]$ of a
compatible chart and of a chart of the atlas are compatible. *Book:* §5.1, p. 169, and Lemma 5.2 (ii), which quantifies
over strong bundle isomorphisms $\Phi : Y|V \to K$. *Hidden hypotheses:* none. *Deviation:* none; Chapter 2 built
$\Phi[1]$ only for the charts of the atlas (Findings, item 2).

**V5.2 (the fibre $(Y_{0,1})_x$ and its chart norm $|\cdot|_1$; `Polyfold.StrongBundle.oneFiber`,
`Polyfold.StrongBundle.toOne`, `Polyfold.StrongBundle.zeroOne`, `Polyfold.StrongBundle.liftOneFiber`,
`Polyfold.StrongBundle.liftOneFiber_injective`, `Polyfold.StrongBundle.mem_range_liftOneFiber`,
`Polyfold.StrongBundle.isClosed_slice`, `Polyfold.StrongBundle.complete_liftOneFiber`,
`Polyfold.StrongBundle.exists_norm_liftOne_le_mul`).** The points of the fibre $P^{-1}(x)$ that lie in $Y_{0,1}$ form a linear
subspace $(Y_{0,1})_x$; its zero is the point $0_x$ of $Y[1]$. In a strong bundle chart around $x$ the fibre component of
$\Phi[1]$ is an injective linear map $(Y_{0,1})_x \to F_1$ onto the slice $\{h \in F_1 \mid (\varphi(x), h) \in K[1]\}$, which is
closed in $F_1$, so $(Y_{0,1})_x$ is complete for $|h|_1$. The norms $|\cdot|_1$ of two charts around $x$ are comparable, with one
constant, on the fibres over a neighbourhood of $x$. *Book:* §5.1, p. 169 ("the fibers $Y_x$ have the structure of Banach
spaces"; $|h|_1$ in Lemma 5.2). *Hidden hypotheses:* none. *Deviation (restated):* the text takes the linear and Banach
structure of the fibres of $Y_{0,1}$ for granted; it is constructed, and $|h|_1$ depends on the chart up to equivalence
(Findings, item 1).

**V5.3 (Definition 5.1, auxiliary norms; `Polyfold.StrongBundle.IsCompleteFiberNorm`, `Polyfold.StrongBundle.IsAuxNorm`,
`Polyfold.StrongBundle.IsAuxNorm.nonneg`, `Polyfold.StrongBundle.IsAuxNorm.smul`).** An auxiliary norm is a continuous
$N : Y[1] \to \mathbb R$ such that (1) on every fibre $(Y_{0,1})_x$, $N$ is a norm ($N(v) = 0 \Rightarrow v = 0$, $N(tv) = |t|N(v)$, the
triangle inequality) for which every Cauchy sequence converges, and (2) if $P(w_k) \to x$ in $X$ and $N(w_k) \to 0$, then $w_k
\to 0_x$ in $Y[1]$. It is non-negative and homogeneous. *Book:* Definition 5.1, p. 169. *Hidden hypotheses:* none.
*Deviation (restated):* "complete norm" is read as a norm on $(Y_{0,1})_x$ with complete normed space; the topology of
$Y_{0,1}$ is that of $Y[1]$ (Findings, item 1).

**V5.4 (Lemma 5.2; `Polyfold.lemma_5_2`, `Polyfold.StrongBundle.exists_le_mul_norm_liftOne`,
`Polyfold.StrongBundle.IsAuxNorm.exists_norm_liftOne_le`, `Polyfold.StrongBundle.IsAuxNorm.exists_bounds`, `Polyfold.lemma_5_2_literal`).**
Let $N : Y[1] \to \mathbb R$ be continuous and a complete norm on every fibre. Then $N$ is an auxiliary norm iff every $x \in X$ lies in the
domain of a strong bundle chart $\Phi$ with an open neighbourhood $V \subseteq \operatorname{dom}\varphi$ of $x$ and constants $0 < a < A$
such that $a\,N(w) \le |h|_1 \le A\,N(w)$ for all $w \in Y_{0,1}$ with $P(w) \in V$, $\Phi(w) = (p, h)$. For an auxiliary norm such bounds
hold in *every* strong bundle chart around $x$; in the text's literal form (`lemma_5_2_literal`) the bounds hold for all $w \in Y_{0,1}$
over the whole domain of the chart, obtained by restricting the chart to the neighbourhood (V2.57); the upper bound $g(w) \le C|h|_1$ holds
for every $g$ continuous at $0_x$ and homogeneous on the fibres near $x$. *Book:* Lemma 5.2, p. 169; proof pp. 169–170. *Hidden hypotheses:*
the proof gives the bounds near $x$ only; on all of $P^{-1}(V)$ for the domain $V$ of $\Phi$ they hold after restricting the chart, which
the text does silently. *Deviation:* none for `lemma_5_2_literal`; the first form has $V$ a neighbourhood of $x$ on which the bounds hold;
the contradiction argument needs no metrizability (Findings, items 2, 3; Chapter 2, items 42, 44). Formerly "restated", before the literal
form was proved.

**V5.5 (Proposition 5.3, existence; `Polyfold.proposition_5_3_exists`, `Polyfold.StrongBundle.gluedNorm`,
`Polyfold.StrongBundle.continuous_gluedNorm`, `Polyfold.StrongBundle.isCompleteFiberNorm_gluedNorm`,
`Polyfold.StrongBundle.gluedNorm_bounds`).** Every strong bundle has an auxiliary norm: for the charts $\Phi_i$ of the atlas and a
partition of unity $(\rho_i)$ subordinate to their domains, $N(w) = \sum_i\rho_i(P(w))\,|\Phi_i[1](w)_2|_1$ is continuous on $Y[1]$, a
complete norm on every fibre, and comparable near each point with the norm $|\cdot|_1$ of any chart there. *Book:* Proposition
5.3, p. 171. *Hidden hypotheses:* none. *Deviation:* none; the text's proof is one sentence (Findings, item 4).

**V5.6 (Proposition 5.3, comparison; `Polyfold.proposition_5_3_compare`).** For auxiliary norms $N_0$, $N_1$ there is a
continuous $f : X \to (0, \infty)$ with $f(x)N_0(w) \le N_1(w) \le f(x)^{-1}N_0(w)$ for every $w \in Y_{0,1}$ over $x$. *Book:*
Proposition 5.3, p. 171. *Hidden hypotheses:* none. *Deviation:* none; the statement's $N_0(h)$ is $N_0(w)$ (Findings, item 5).

**V5.7 (Definition 5.4; `Polyfold.StrongBundle.AuxLe`, `Polyfold.StrongBundle.IsWeaklyProper`,
`Polyfold.StrongBundle.IsProper`, `Polyfold.StrongBundle.IsProper.isWeaklyProper`,
`Polyfold.StrongBundle.IsWeaklyProper.isCompact_solutionSet`).** A section $f$ has a compact solution set if $f^{-1}(0)$ is
compact in $X$; it is weakly proper if moreover for every auxiliary norm $N$ there is an open $U \supseteq f^{-1}(0)$ such that $\{f
= s\}$ is compact for every sc⁺-section $s$ with support in $U$ and $N(s(y)) \le 1$ for all $y$; it is proper if moreover for
every $N$ there is an open $U \supseteq f^{-1}(0)$ with $\operatorname{cl}_X\{x \in U \mid N(f(x)) \le 1\}$ compact, where $N(f(x)) \le 1$
includes $f(x) \in Y_{0,1}$. A continuous proper section is weakly proper, and a weakly proper section has a compact solution
set. *Book:* Definition 5.4, p. 171. *Hidden hypotheses:* "proper implies weakly proper" needs $f$ continuous (so that $\{f
= s\}$ is closed). *Deviation:* none (Findings, item 26).

**V5.8 (Theorem 5.5, the local form for basic germs; `Polyfold.IsSc0ContractionGerm.exists_isCompact_bdd`,
`Polyfold.IsBasicGerm.exists_isCompact_bdd`).** Let $f$ be a basic germ on $\tilde C \oplus W$ with $P \circ f(a, w) = w - B(a,
w)$, $\tilde C$ closed. There is an open $O \ni 0$, independent of $c$, such that for every $c$ the points $x$ of $U_0 \cap O$ with
$f(x) \in \mathbb R^N \oplus W_1$ and $|f(x)|_1 \le c$ lie in a compact subset of $E_0$, namely the image of $\{(a, z) \mid a \in \tilde C,
|a|_0 \le \rho, z \in K_c, |z|_0 \le r/8\}$ under $(a, z) \mapsto (a, \delta(a, z))$, with $K_c$ a compact set containing the
level-$1$ ball of radius $c$ and $\delta$ the parametrized fixed point of $w \mapsto B(a, w) - z$. *Book:* Appendix 5.4.1, pp.
189–192, (82)–(90). *Hidden hypotheses:* $\tilde C$ closed, as in Theorem 3.40. *Deviation (restated):* only the level-$0$
contraction is used, and the neighbourhood does not depend on the bound (Findings, items 23, 25).

**V5.9 (Theorem 5.5, the local step; `Polyfold.IsStrongBundleMap.exists_fiber_bound_one`,
`Polyfold.exists_nbhd_isCompact_closure_bdd`).** A strong bundle map $\Psi$ has a uniform $(0, 1)$ fibre bound near each point,
$|\Psi[1](u, k)_2|_1 \le M|k|_1$ for $|u - u_0|_0 < \delta$. If $(f, x_0)$ is an sc-Fredholm germ, then in the strong bundle chart
$\Phi$ of the germ there is an open $V \ni x_0$ such that for every $C$ the closure in $X$ of $\{x \in V \mid \Phi(f(x))_2 \in F_1,
|\Phi(f(x))_2|_1 \le C\}$ is compact. *Book:* Appendix 5.4.1, pp. 189–192 ("without loss of generality $f = h + t$", "it
suffices to find in local coordinates"). *Hidden hypotheses:* the uniform fibre bound of the conjugating isomorphism.
*Deviation (stronger):* $x_0$ need not be a zero; subtracting the sc⁺-part before the conjugation replaces the text's $t$
and its estimates (83), (85), and the closure is pulled back to $X$ because the retract is the fixed point set of the
retraction (Findings, items 23, 24).

**V5.10 (Theorem 5.5; `Polyfold.theorem_5_5`, `Polyfold.theorem_5_5_iff`).** Let $f$ be an sc-Fredholm section of a strong
bundle over an M-polyfold $X$. If $f$ has a compact solution set, $f$ is proper; and for $f$ the properties proper, weakly
proper and having a compact solution set are equivalent. *Book:* Theorem 5.5, p. 172; proof Appendix 5.4.1, pp. 189–192.
*Hidden hypotheses:* none. *Deviation (stronger):* $X$ need not be tame (the appendix states the theorem without
tameness); the finite cover of $f^{-1}(0)$ and the closure of a finite union are made explicit (Findings, items 24, 25).

**V5.11 (Theorem 5.6; `Polyfold.theorem_5_6`).** Let $f$ be an sc-Fredholm section and $f(x) = 0$. There are open
neighbourhoods $x \in U(i + 1) \subseteq U(i)$ of $x$ in $X$ such that for every $i$ the closure in $X$ of $\{y \in U(i) \mid f(y) = 0\}$
is the image of a compact subset of $X_i$ (with its level topology). *Book:* Theorem 5.6, p. 172. *Hidden hypotheses:*
none. *Deviation:* none; it is Theorem 3.12 at a zero, which is a smooth point where $(f, x)$ is an sc-Fredholm germ.

**V5.12 (Theorem 5.7; `Polyfold.theorem_5_7`, `Polyfold.MPolyfold.tendsto_smoothLevel_iff`,
`Polyfold.MPolyfold.smoothLevel_topology_eq`, `Polyfold.MPolyfold.metrizableSpace_smoothLevel`).** $X_\infty$ carries the initial
topology of the inclusions $X_\infty \to X_m$; it is metrizable, and a sequence converges in it iff it converges on every level.
If $f$ is an sc-Fredholm section whose solution set $S$ is compact in $X$, then $S \subseteq X_\infty$ and $S$ is a compact subset of
$X_\infty$. *Book:* Theorem 5.7, p. 172. *Hidden hypotheses:* the topology of $X_\infty$, which the text does not define.
*Deviation (stronger):* $X$ need not be tame. The convergence on every level of a sequence of zeros is Corollary 3.13 at its
limit, not Theorem 5.6 as the text says (Findings, item 20).

**V5.13 (Corollary 5.8; `Polyfold.corollary_5_8`, `Polyfold.corollary_5_8_two`,
`Polyfold.StrongBundle.solutionSet_sectionShift`, `Polyfold.isCompact_solutionSet_level`).** Let $f$ be an sc-Fredholm
section of $P : Y \to X$ (Definition 3.14, in the text's germ reading of Definition 3.11) whose solution set is compact.
Then $f^1 = f|_{X_1}$ is an sc-Fredholm section of the shifted strong bundle $P^1 : Y^1 \to X^1$ (V5.14) and its solution
set is compact in $X^1$; $f^2 = (f^1)^1$ is an sc-Fredholm section of $P^2 = (P^1)^1$ with compact solution set; and for
every $i$ the zeros of $f$ in $X_i$ form a compact subset of $X_i$. *Book:* Corollary 5.8, p. 173 (over a tame $X$, for
every $i$). *Hidden hypotheses:* the bundle $P^i$, which the text does not define, is the iterated shift $P^i =
(P^{i-1})^1$. *Deviation:* none; the first statement holds for every strong bundle, so every fixed $i$ follows by
iterating it ($i = 2$ is stated); one statement for a family indexed by $i$ is not formalized, and the base $(X^1)^1$ of
$P^2$ has the points of $X_2$, its topology not compared with that of $X_2$ (gap G.6). Tameness is not used; the conclusion
is Definition 3.14 for $f^i$, not tame germ data, which would need tame charts of $P^1$ (Findings, items 140–146). Formerly
"narrower": only the compactness half was verified (gap G.41, now closed for each fixed $i$).

**V5.14 (Corollary 5.8: the shifted strong bundle, and $f^1$ sc-Fredholm on it; `Polyfold.StrongBundle.shift`,
`Polyfold.StrongBundleChart.shift`, `Polyfold.StrongBundleChart.Compatible.shift`,
`Polyfold.StrongBundle.mem_shift_doubleLevel_iff`, `Polyfold.StrongBundle.sectionShift`,
`Polyfold.StrongBundle.regularizing_sectionShift`, `Polyfold.ScNbhdGerm.shiftParam`, `Polyfold.IsSc0ContractionGerm.shift`,
`Polyfold.IsBasicGerm.shift`, `Polyfold.IsConjugateToBasicGerm.shift`, `Polyfold.IsConjugateToBasicGerm.shift_germ`,
`Polyfold.IsFillingGerm.mem_range_toBase_of_fillDefect`, `Polyfold.IsFillingGerm.germ_shift`,
`Polyfold.isScFredholmGerm_sectionShift`, `Polyfold.corollary_5_8_isScFredholmSection`, `Polyfold.corollary_5_8_chart`).**
*The shifted strong bundle.* $P^1 : Y^1 \to X^1$ is a strong bundle over the M-polyfold $X^1$ (Definition 2.51): its total
space is $Y_{1,1}$, the level $1$ of the M-polyfold $Y[0]$ with its level topology; $P^1$ is the restriction of $P$; the
fibre over $x$ is $P^{-1}(x) \cap Y_{1,1}$, a linear subspace, carrying the topology of $F_1$; and the atlas consists of the
index raises $\Phi^1$ of the strong bundle charts $\Phi$ of $P$ (base chart the level chart $\varphi^1$, fibre model $F^1$,
retraction $R$ restricted to $U^1 \triangleleft F^1$), compatible charts having compatible index raises. Its double
levels are $(Y^1)_{m,k} = Y_{m+1,k+1}$. *$f^1$ is sc-Fredholm.* For every sc-Fredholm section $f$ (no compactness needed),
$f^1 = f|_{X_1}$ is an sc-Fredholm section of $P^1$: it is sc-smooth, regularizing, and at every smooth point of $X^1$ it has
the data of Definition 3.11 in the index raise $\Phi^1$ of the chart $\Phi$ of a datum $(g, s)$ of $f$ there. The principal
part of $f^1$ is the level-$1$ map of that of $f$; $g^1$ is a filling germ of it, including condition (3) of Definition 3.4
on level $1$, which comes from a regularity statement at the centre of every datum of Definition 3.11: $v \in \ker Dr(0)$
and $Dk(0)v \in F_m$ imply $v \in E_m$, $k$ the fill defect. *In a chart.* The level shift
$f^1$ of a basic germ $f$ on $\tilde C \oplus W$, $\tilde C$ a partial quadrant, is a basic germ on $\tilde C \oplus W^1$ with $B^1$ in place of
$B$; if a principal part $k$ is conjugated to a basic germ $h$ by $\Psi$, then $k^1$ is conjugated to $h^1$ by the index raise $\Psi^1$.
Hence for an sc-Fredholm section with compact solution set: the zeros in $X_1$ form a compact subset of $X_1$, and at every
smooth point $x$, in the chart $\Phi$ centred at $x$ of the germ $(f, x)$ with filling germ $g$ and sc⁺-germ $s$ (the text's germ
reading of Definition 3.11), the level-$1$ germ $(g - s)^1$ is conjugated to a basic germ (by the germ form of the index raise, which
uses $g - s$ only near $0$) and $s^1$ is an sc⁺-germ on the shifted germ of $s$. *Book:* Corollary 5.8, p. 173
("it is a priori clear that $f^i$ is sc-Fredholm", as a section of $P^i : Y^i \to X^i$). *Hidden hypotheses:* the bundle
$Y^1 \to X^1$, which the text does not define ($Y[i]$ is defined for $i = 0, 1$ only): $Y^1 = Y_{1,1}$, the convention of
$E^1$, forced by "$f^i$ is obtained by raising the index" (an sc-smooth section maps $X_1$ into $Y_{1,1}$, in general not
into $Y_{1,2}$); $\tilde C$ a partial quadrant. *Deviation:* none; "it is a priori clear" hides condition (3) of the
filling on level $1$, which does not follow from level $0$ alone (an sc-operator can be bijective on level $0$ and not onto
on level $1$); it is proved for the data of Definition 3.11 by reducing to $g(0) = 0$ with Lemma 3.17 (subtracting the
section $z \mapsto \Gamma(z, -g(0))$, which leaves the fill defect unchanged) and applying Proposition 3.52 in sc form. No
hypothesis beyond the text's is added; tameness is not used, and the tame form (germ data in tame charts of $P^1$) is not
stated (Findings, items 22, 140–146). Formerly "narrower": the bundle was not built and the filler on level $1$ not verified
(gap G.41, now closed for each fixed $i$). In the text's germ reading of Definition 3.11 (phase 2; Findings, Chapter 3,
item 333) $s^1$ is an sc⁺-germ on the shifted germ; in the whole-chart reading it was sc⁺ on all of $U^1$.

**V5.15 ($\mathbb R$ as an M-polyfold; sc-smooth functions; `Polyfold.realPolyfold`, `Polyfold.realChart`,
`Polyfold.isChart_realChart`, `Polyfold.MPolyfold.isScSmoothMap_of_local`, `Polyfold.MPolyfold.IsScSmoothMap.real_chart`,
`Polyfold.isScSmoothMap_real_of_local`, `Polyfold.isScSmoothMap_real_const`, `Polyfold.isScSmoothMap_real_of_contDiff`,
`Polyfold.MPolyfold.IsScSmoothMap.comp_contDiff`).** $\mathbb R$ with the constant sc-structure and the single chart $\mathrm{id}$ is
an M-polyfold, and an sc-smooth function on $X$ is an sc-smooth map $X \to \mathbb R$ (Definition 2.14). Sc-smoothness of a map
between M-polyfolds can be checked in one pair of charts around each point (continuity included); an sc-smooth function
read in a chart is sc-smooth on the retract; constants are sc-smooth, and $\sigma \circ f$ is sc-smooth for $\sigma : \mathbb R \to \mathbb R$ of
class $C^\infty$. *Book:* Definitions 5.9, 5.29, 5.33 ("sc-smooth map $f : X \to \mathbb R$"). *Hidden hypotheses:* none.
*Deviation (not in the book):* the M-polyfold $\mathbb R$ is presupposed by the text (Findings, item 40).

**V5.16 (Definitions 5.9 and 5.29; `Polyfold.MPolyfold.AdmitsBumpFunctions`, `Polyfold.MPolyfold.AdmitsBumpFunctionsWeak`,
`Polyfold.MPolyfold.AdmitsBumpFunctions.weak`, `Polyfold.MPolyfold.HasBumpAt`,
`Polyfold.MPolyfold.admitsBumpFunctionsWeak_of_dense`, `Polyfold.MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth`,
`Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert`).** $X$ admits sc-smooth bump functions if for every $x$ and every open $U \ni x$
there is an sc-smooth $f : X \to \mathbb R$ with $f(x) \ne 0$ and $\operatorname{supp} f \subseteq U$. Definition 5.29 as written ("$f$ not
identically zero") is a separate notion, implied by the first. A point $x$ is a *bump point* if every open $U \ni x$
carries an sc-smooth $f$ with $f(x) \ne 0$ and $\operatorname{supp} f \subseteq U$: the first notion says that every point is
a bump point, and the second follows if the bump points are dense. On an sc-Banach space $E$ (as an M-polyfold with the
identity chart) the second notion makes every smooth point a bump point; on M-polyfolds built on sc-Hilbert spaces the
first notion holds. *Book:* Definition 5.9, p. 173; Definition 5.29, p. 192. *Hidden hypotheses:* none. *Deviation
(restated):* "$f \ne 0$" is read as $f(x) \ne 0$, the reading Proposition 5.30's proof uses. Whether the weak reading implies
it is open only at non-smooth points: at a smooth point of an sc-Banach space a bump that is non-zero near $x$ is translated
to $x$ by a smooth vector, and translation by a non-smooth vector does not preserve the levels; that the weak reading is
exactly the density of the bump points is argued, one direction formalized (Findings, items 41, 160–163).

**V5.17 (Propositions 5.10 and 5.30; `Polyfold.proposition_5_30`, `Polyfold.proposition_5_10`).** If $X$ admits sc-smooth bump
functions, then for every $x$ and open $U \ni x$ there is an sc-smooth $f : X \to [0, 1]$ with $f(x) = 1$, $\operatorname{supp} f \subseteq U$, and $f
\equiv 1$ on a neighbourhood of $x$. *Book:* Proposition 5.10, p. 173; Proposition 5.30, p. 193. *Hidden hypotheses:*
Definition 5.9 in the reading of V5.16. *Deviation:* none; the text's $\sigma$ ("$0$ for $s \le 1$ and $1$ for $s \ge 1$") is
misprinted and $g(x) = 1$ is not given; the proof uses $f = \tau(3g/g(x) - 1)$ with a smooth transition $\tau$ (Findings,
item 42).

**V5.18 (the sc-calculus of sections: $\Gamma^+(P)$, supports, $f \cdot s$ and sums; `Polyfold.sectionSupport`,
`Polyfold.sectionSmul`, `Polyfold.sectionSum`, `Polyfold.StrongBundle.scPlusSections`,
`Polyfold.StrongBundle.IsScPlusSection.mem_oneSet`, `Polyfold.StrongBundle.isScPlusSection_fiberZero`,
`Polyfold.StrongBundle.IsScPlusSection.smul_left`, `Polyfold.StrongBundle.IsScPlusSection.add`,
`Polyfold.StrongBundle.isScPlusSection_sectionSum`).** $\Gamma^+(P)$ is the set of sc⁺-sections (Definition 2.52); their values lie
in $Y_{0,1}$. The zero section is an sc⁺-section; for an sc-smooth function $f$ and an sc⁺-section $s$, $f \cdot s$ (fibrewise) is an
sc⁺-section; sums and finite sums of sc⁺-sections are sc⁺-sections. *Book:* §5.3, p. 173 ($\Gamma^+(P)$); used in the proof of
Lemma 5.11 ("$s(y) = \beta(y)t(y)$ is a sc⁺-section") and in the finite combinations $\sum\lambda_is_i$ of Theorems 5.13, 5.18.
*Hidden hypotheses:* none. *Deviation (not in the book):* the text uses these rules without stating them; in a chart $(f \cdot
s)^\wedge = (f \circ \varphi^{-1}) \cdot \hat s$ and the product rule of the sc-calculus applies (Findings, item 45).

**V5.19 (local sc⁺-sections cut off and extended by $0$; `Polyfold.StrongBundle.cutoffSection`,
`Polyfold.StrongBundle.isScPlusSection_cutoffSection`).** Let $\Phi$ be a strong bundle chart of the atlas, $\tau : O \to F_1$ such that
$z \mapsto (z, \tau(z))$ is sc-smooth $O \to K[1]$, and $\beta : X \to \mathbb R$ sc-smooth with $\operatorname{supp}\beta \subseteq \operatorname{dom}\varphi$. Then $y \mapsto
\Phi^{-1}(\varphi(y), \beta(y)\tau(\varphi(y)))$ on $\operatorname{dom}\varphi$, $0_y$ outside, is an sc⁺-section. *Book:* proof of Lemma 5.11, p. 174 ("if we
construct $s$ with support in $Q'$ we can extend it by $0$"). *Hidden hypotheses:* none. *Deviation (not in the book):* the
extension by $0$ is proved (Findings, item 46 (c)).

**V5.20 (Lemma 5.11; `Polyfold.lemma_5_11`).** Let $X$ admit sc-smooth bump functions and $N$ be an auxiliary norm. For a
smooth point $x$, a smooth point $e$ of $Y$ with $P(e) = x$, $\varepsilon > 0$ and an open $U \ni x$, there is an sc⁺-section $s$ with $s(x) =
e$, $\operatorname{supp} s \subseteq U$ and $N(s(y)) < N(e) + \varepsilon$ **for all $y$**. *Book:* Lemma 5.11, p. 173; proof p. 174. *Hidden
hypotheses:* Definition 5.9 in the reading of V5.16. *Deviation (stronger):* the bound holds at every point (the text's
bound at $x$ is trivial; the proof gives the uniform one, which §5.3 needs); tameness of $P$ and $X$, normality of $X$ and a
chart centred at $x$ are not needed (Findings, item 46).

**V5.21 ($\Gamma^{+,1}_U(P)$ and the metric $\rho$; `Polyfold.StrongBundle.allowableSections`,
`Polyfold.StrongBundle.sectionDistAt`, `Polyfold.StrongBundle.allowableDist`, `Polyfold.StrongBundle.allowableMetric`,
`Polyfold.StrongBundle.allowableDist_le_iff`, `Polyfold.TrivialBundle.not_completeSpace_allowableSections`,
`Polyfold.StrongBundle.completeSpace_allowableSections_empty`,
`Polyfold.TrivialBundle.completeSpace_allowableSections_point`).** For an auxiliary norm $N$ and an open $U$, $\Gamma^{+,1}_U(P)$ is the set of sc⁺-sections $s$ with
$\operatorname{supp} s \subseteq U$ and $N(s(x)) \le 1$ for all $x$ (the allowable sections). For two sc⁺-sections $N(s(x) - s'(x))$ is the norm of
the difference in the fibre $(Y_{0,1})_x$. The uniform distance $\rho(s, s') = \sup_xN(s(x) - s'(x))$ is finite
($\rho \le 2$) and, for an auxiliary norm, a metric on $\Gamma^{+,1}_U(P)$; $\rho(s, s') \le \varepsilon$ iff $N(s(x) - s'(x))
\le \varepsilon$ for all $x$. For the trivial bundle $\mathbb R \times \mathbb R \to \mathbb R$ with $N(x, v) = |v|$ and $U =
\mathbb R$ the metric space is not complete; for $U = \emptyset$ (any bundle) and over a point with fibre $\mathbb R^k$ (any $U$)
it is complete. *Book:* §5.3, p. 174 ("a metric space ... not complete"). *Hidden hypotheses:* none for the metric.
*Deviation (restated):* the text's "not complete" is false without a hypothesis (the cases $U = \emptyset$ and a point base)
and is read as "not complete in general", proved by the example: $s_j(x) = (x, \sqrt{x^2 + 1/(j+1)^2}/(2\sqrt{1 + x^2}))$ is a
$\rho$-Cauchy sequence of allowable sections whose pointwise limit has the fibre part $|x|/(2\sqrt{1 + x^2})$, not
differentiable at $0$, while the fibre part of an sc⁺-section of the trivial bundle is $C^1$. Non-completeness in the
text's setting ($U$ containing a non-isolated point over which $Y_{0,1} \ne 0$) is expected by the same mechanism and not
formalized (Findings, items 47, 150–153).

**V5.22 (Remark 5.12; `Polyfold.remark_5_12`, `Polyfold.StrongBundle.IsAuxNorm.auxLe_of_sectionAdd`,
`Polyfold.StrongBundle.IsInAllowableCompletion`, `Polyfold.remark_5_12_completion`, `Polyfold.remark_5_12_of_isScFredholmSection`).** Let
$f$ have its solution set inside the open $U$ with $\operatorname{cl}\{x \in U \mid N(f(x)) \le 1\}$ compact. If a section $s$ vanishes
outside $U$ and has $N(s(x)) \le 1$ everywhere — as the uniform limits of allowable sections do — then the solutions of $f + s = 0$ lie in
$\{x \in U \mid N(f(x)) \le 1\}$, and their closure is compact. As stated (`remark_5_12_completion`): with the points of the completion
represented by sections $s$ with values in $Y_{0,1}$ that are uniform $N$-limits of allowable sections (`IsInAllowableCompletion`), for $f$
continuous the solution set of $f + s = 0$ is closed, hence compact; for $f$ sc-Fredholm with compact solution set, with the $U$ of Theorem
5.5 (`remark_5_12_of_isScFredholmSection`). *Book:* Remark 5.12, p. 174. *Hidden hypotheses:* none. *Deviation (restated):* the completion
of $\Gamma^{+,1}_U$ is represented by sections, uniform $N$-limits of allowable sections; the metric space itself is V5.21, and
that every $\rho$-Cauchy sequence has such a limit section is not formalized (Findings, items 131, 153). The closedness of the solution set, which the remark does not discuss, is
proved by a chart argument: Lemma 5.2's bound turns $N(s - s') \le \varepsilon$ into a level-$0$ bound in a chart, and $f + s'$ is
continuous for allowable $s'$; "adapted to $N$" is read as the properness of V5.7 (Findings, items 27, 130, 131).

**V5.23 (Definition 5.15; `Polyfold.StrongBundle.IsTransversal`, `Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective`).** A
section $g$ is transversal to the zero section if at every zero $x$ the linearization is onto, in a strong bundle chart around
$x$; it is then onto in every such chart. *Book:* Definition 5.15, p. 175. *Hidden hypotheses:* none. *Deviation
(restated):* $g'(x) : T_xX \to Y_x$ is read in charts (gap G.7 of Chapter 2) (Findings, item 70).

**V5.24 (spanning sections at a zero; `Polyfold.exists_fin_mem_of_dense_of_closedComplemented`,
`Polyfold.exists_spanning_sections`).** If $R$ is a closed, complemented subspace of finite codimension of a Banach space $K$ and
$D$ a dense subspace, finitely many vectors of $D$ span a complement of $R$. Hence, if $X$ admits sc-smooth bump functions, $N$ is
an auxiliary norm, $g$ is sc-Fredholm and $g(y) = 0$, then for every open $U \ni y$ there are finitely many allowable
sc⁺-sections $s_1, \dots, s_k$ supported in $U$ and a strong bundle chart centred at $y$ in which $\mathrm{Lin}(0)(T_0O) +
\operatorname{span}\{\hat s_i(0)\} = K_0$. *Book:* proof of Theorem 5.13, p. 175 ("we find finitely many allowable sc⁺-sections such that the
range of $(f + s_0)'(x)$ together with the sections span $Y_x$"). *Hidden hypotheses:* none. *Deviation (not in the
book):* the text does not say how; the density of the smooth vectors in $K_0$ is the point (Findings, item 66).

**V5.25 (the parametrized section and its slices; `Polyfold.paramSlice`, `Polyfold.isZeroAt_paramSection_iff`,
`Polyfold.isScFredholmSection_paramSlice`, `Polyfold.isScPlusSection_paramSlice`, `Polyfold.sectionSupport_paramSlice_subset`,
`Polyfold.auxLe_paramSlice`).** For a section $g$ and sections $t_1, \dots, t_m$, the slice $g + \sum\lambda_it_i$ of $F(\lambda, y) = g(y) +
\sum\lambda_it_i(y)$ (Theorem 3.18) is a section of $P$, and $(\lambda, y)$ is a zero of $F$ iff $y$ is a zero of the slice. For $g$
sc-Fredholm and $t_i$ sc⁺ the slices are sc-Fredholm; slices of sc⁺-sections are sc⁺ with support in the union of the supports;
and if $N(s_0) \le 1 - \varepsilon$, $N(t_i) \le 1$ and $m|\lambda| \le \varepsilon$, then $N(s_0 + \sum\lambda_it_i) \le 1$. *Book:* proof of Theorem 5.13, p. 176
("there is a number $\delta_0 > 0$ such that $|\lambda| < \delta_0$ implies $N(\sum\lambda_jt_j(y)) < \varepsilon/2$"). *Hidden hypotheses:* none.
*Deviation (not in the book):* bookkeeping the text leaves implicit.

**V5.26 ("regular value $\Leftrightarrow$ transversal" and transversality of $F$ at $(0, y)$;
`Polyfold.surjective_of_forall_exists_ker_fst`, `Polyfold.forall_exists_ker_fst_of_surjective`,
`Polyfold.isLinSurjAt_paramSlice_of_ker_fst`, `Polyfold.isLinSurjAt_paramSection_zero_of_spanning`,
`Polyfold.isLinSurjAt_paramSection_zero_of_comp`).** For $M(a, u) = Lu + \sum a_ie_i$ onto, the projection $\ker M \to \mathbb R^m$ is onto iff $L$
is onto. Consequently, if the linearization of $F$ at a zero $(\lambda, y)$ is onto and the kernel of $\mathrm{Lin}_F(0)$ in the product
chart $(r \mapsto r - \lambda) \times \Phi$ projects onto $\mathbb R^m$, the slice $g + \sum\lambda_it_i$ is transversal at $y$. Conversely, if the range of
$\mathrm{Lin}_g(0)$ and the $\hat t_i(0)$ span $K_0$ in a chart centred at the zero $y$ of $g$, $F$ is transversal at $(0, y)$, and adding sections
keeps this. *Book:* proof of Theorem 5.13, pp. 175–176 ("the linearization at $(0, x)$ is surjective"; "it is easily
verified that $f + s_0 + s(\lambda_0, \cdot)$ is transversal"). *Hidden hypotheses:* none. *Deviation (not in the book):* only
"regular value $\Rightarrow$ transversal" is needed and proved for slices; the text's "$\Leftrightarrow$" for $\tilde S$ is not formalized
(Findings, items 64, 67).

**V5.27 (the openness steps and the omitted compactness step; `Polyfold.isWithoutBoundary_prod_rn`,
`Polyfold.isClosed_solutionSet`, `Polyfold.exists_isOpen_isLinSurjAt_zero_near`,
`Polyfold.exists_isOpen_goodPosition_of_isLinSurjAt`, `Polyfold.exists_pos_forall_mem_of_isCompact`).** If $\partial X = \emptyset$ then
$\partial(\mathbb R^m \times X) = \emptyset$; the solution set of an sc-smooth section is closed. For $\partial X = \emptyset$ and $g$ with tame germ data: if $F$ is
transversal at $(0, x)$, it is transversal at $(0, y)$ for the zeros $y$ of $g$ near $x$; if $F$ is transversal at every $(0, y)$,
$y \in S_g$, there is an open $V \supseteq \{0\} \times S_g$ all of whose zeros of $F$ are in good position in a tame chart. If $Z \subseteq \mathbb R^m \times
X$ is compact and the open $V$ contains $Z \cap \{\lambda = 0\}$, then $V$ contains $Z \cap \{|\lambda| < \delta\}$ for some $\delta > 0$. *Book:* proof
of Theorem 5.13, pp. 175–176 ("in view of the interior case of the implicit function theorem, Theorem 3.19"; "$U \subset
\{|\lambda| < \delta_0\} \oplus X$"). *Hidden hypotheses:* tame germ data, the reading of the tame strong bundle of §5.3 (Findings,
item 75). *Deviation (not in the book):* the passage to $|\lambda| < \delta_0$ is the omitted step, proved with Remark 5.12
(Findings, items 63, 68).

**V5.28 (the Sard step; `Polyfold.exists_null_isLinSurjAt_paramSlice_near`).** Let $g$ have tame germ data, $t_i$ be
sc⁺-sections, and $z_0$ a zero of $F(\lambda, y) = g(y) + \sum\lambda_it_i(y)$ in good position in a tame chart. There are an open $W \ni z_0$
and a Lebesgue null set $CV \subseteq \mathbb R^m$ such that for every zero $(\lambda, y) \in W$ of $F$ with $\lambda \notin CV$ the slice $g + \sum\lambda_it_i$ is
transversal at $y$. *Book:* proof of Theorem 5.13, p. 176 ("taking a regular value $\lambda_0$ for the projection $\tilde S \to \mathbb
R^m$"). *Hidden hypotheses:* none. *Deviation (not in the book):* $\tilde S$ is not built as a manifold; Sard's theorem is
applied in its stratified form on the model of the regular tangent germ chart of Theorem 3.54 (2), which avoids showing that
the points over the zeros are interior (Findings, items 64, 65).

**V5.29 (Theorem 5.13, generic form; `Polyfold.theorem_5_13_generic`, `Polyfold.StrongBundle.SolutionSetIsManifold`).** Let
$\partial X = \emptyset$, $X$ admit sc-smooth bump functions, $f$ be an sc-Fredholm section with tame germ data and compact solution set,
and $N$ an auxiliary norm. There is an open $U \supseteq S_f$ such that (1) $S_{f+s}$ is compact for every $s \in \Gamma^{+,1}_U(P)$, and (2) for
every sc⁺-section $s_0$ with $\operatorname{supp}s_0 \subseteq U$ and $N(s_0(x)) \le 1 - \varepsilon$ ($\varepsilon > 0$) there are allowable $t_1, \dots, t_m \in
\Gamma^{+,1}_U(P)$, $\delta > 0$ and a Lebesgue null set $CV \subseteq \mathbb R^m$ such that for every $\lambda$ with $|\lambda| < \delta$, $\lambda \notin CV$: $s_\lambda = s_0
+ \sum\lambda_it_i$ is allowable, $f + s_\lambda$ is transversal, $S_{f+s_\lambda}$ is compact and, if non-empty, a sub-M-polyfold whose
induced structure is tame and that of a manifold without boundary of locally constant dimension, with regular tangent germ
data at every zero of dimension the Fredholm index of $(f + s_\lambda)'(y)$. *Book:* Theorem 5.13, pp. 174–175; proof pp.
175–176. *Hidden hypotheses:* $f$ with tame germ data (Definition 3.51), the reading of §5.3's tame strong bundle; the
statement's "$N(f(x)) \le 1$" is $N(s(x)) \le 1$ and "$(f, x)$ in good position" is $(f + s, x)$. *Deviation (restated):* the
dense set of the text is described as the parameters off a null set of a ball (Findings, items 60, 62, 74, 75).

**V5.30 (Theorem 5.13, the text's dense form; `Polyfold.theorem_5_13`, `Polyfold.StrongBundle.allowableDist_le_iff`).** Under the hypotheses of V5.29 there is an open $U
\supseteq S_f$ such that $S_{f+s}$ is compact for every $s \in \Gamma^{+,1}_U(P)$, and for every allowable $s'$ and $\varepsilon > 0$ there is an
allowable $s$ with $N(s(x) - s'(x)) \le \varepsilon$ for all $x$ such that $f + s$ is transversal and $S_{f+s}$ is compact and, if
non-empty, a manifold without boundary as in V5.29. *Book:* Theorem 5.13, pp. 174–175. *Hidden hypotheses:* as in
V5.29. *Deviation (restated):* density in $(\Gamma^{+,1}_U(P), \rho)$ (V5.21) is the bound $\rho(s, s') \le \varepsilon$, stated
pointwise and equivalent to it; the text's
"$N(s_0(y) + s(\lambda_0, y)) \le 1 - \varepsilon/2$" is $\le 1$ (Findings, items 60, 62).

**V5.31 (Definition 5.17, in a tame chart; `Polyfold.StrongBundle.IsGeneralPositionGerm`,
`Polyfold.StrongBundleChart.linKer`, `Polyfold.StrongBundle.IsGeneralPositionGerm.isLinSurjAt`).** $(f, y)$ with $f(y) = 0$ is in
general position if in some tame strong bundle chart around $y$, at the level-$1$ point $z$ over $\varphi(y)$, $\mathrm{Lin}(z) : T_zO \to K_z$
is onto, and for every presentation $T$ of the partial quadrant the kernel of $\mathrm{Lin}(z)$ has an sc-complement in $T_zO$
contained in $T^R_zO = T_zO \cap E_z$: an sc-subspace $B$ with $(T_zO)_m = (\ker\mathrm{Lin}(z))_m \oplus B_m$ on every level. General
position includes transversality at $y$. *Book:* Definition 5.17, p. 177. *Hidden hypotheses:* the chart is tame (the
reduced tangent space of Definition 2.38 is that of a tame M-polyfold). *Deviation (restated):* stated in a chart (gap G.7
of Chapter 2); chart independence at the zeros near a zero in good position is V5.34 (Findings, items 71, 76, 82).

**V5.32 (the bridge lemma: solution sets as smooth submanifolds; `Polyfold.isScPlus_of_isScSmooth_const`,
`Polyfold.MPolyfold.TangentGermChart.exists_scPlusRetraction`, `Polyfold.MPolyfold.TangentGermChart.exists_isScPlusRetractionOn`,
`Polyfold.MPolyfold.isSmoothSubmanifold_of_isRegular`, `Polyfold.StrongBundle.isSmoothSubmanifold_solutionSet_inter`).** An
sc-smooth map on a finite-dimensional space with the constant structure is sc⁺. For regular tangent germ data of Definition
3.25 (2), the retraction $\tau = \Gamma \circ \pi \circ r$ of the proof of Theorem 3.27 is an sc⁺-retraction, so a set with regular tangent
germ data at every point is a smooth finite-dimensional submanifold (Definition 4.13). In particular, if every zero of a
section in the open $W$ is in good position in a tame chart, $S_f \cap W$ is a smooth finite-dimensional submanifold. *Book:*
proof of Theorem 5.18, p. 179 ("hence we can apply Theorem 4.23"). *Hidden hypotheses:* none. *Deviation (not in the
book):* the text never verifies Definition 4.13 for solution sets (Findings, item 81).

**V5.33 ($T_yS = \ker f'(y)$; `Polyfold.tangentSpace_subset_linKer`,
`Polyfold.MPolyfold.TangentGermChart.exists_linearIndependent_tangentSpace`, `Polyfold.HasIndepTangent.transport`,
`Polyfold.exists_tangentSpace_eq_linKer`).** In a strong bundle chart the tangent space of a retract on which the principal part
vanishes lies in $\ker\mathrm{Lin}(z)$. For $f$ with tame germ data and $(f, x_0)$ in good position in a tame chart there is an open $V
\ni x_0$ whose zeros are all in good position such that at every zero $y \in V$, in every strong bundle chart around $y$ and for
every open $G \ni y$ in its domain with $\varphi(G \cap S_f \cap V)$ a retract, the tangent space of that retract at the point over $\varphi(y)$
equals $\ker\mathrm{Lin}(z)$. *Book:* used in the proofs of Theorems 5.18 and 5.25 ("$T_zS_\lambda$ has a sc-complement contained in
$T^R_xX$"); Lemma 5.24 ("$T_xS = \ker f'(x)$"). *Hidden hypotheses:* none. *Deviation (not in the book):* "$\supseteq$" is a dimension
count, $d$ independent tangent vectors of the bridge retraction carried to every chart (Findings, item 82).

**V5.34 (Definition 5.17 is Definition 4.21 for the solution set; `Polyfold.exists_isGeneralPositionGerm_iff`,
`Polyfold.isGoodPositionGermTame_of_isGeneralPositionAt`).** For $f$ with tame germ data and $(f, x_0)$ a zero in good position
in a tame chart there is an open $V \ni x_0$ such that every zero in $V$ is in good position, $S_f \cap V$ is a smooth finite-dimensional
submanifold, and at every zero $y \in V$, $(f, y)$ is in general position (Definition 5.17) iff $S_f \cap V$ is in general position at
$y$ (Definition 4.21); both are then independent of the chart. If $f'(y)$ is onto and a smooth submanifold $A \subseteq S_f$ is in
general position at $y$, then $(f, y)$ is in good position in a tame chart. *Book:* Definition 5.17, p. 177, and the proofs
of Theorems 5.18, 5.25. *Hidden hypotheses:* none. *Deviation (not in the book):* the chart independence of Definition
5.17 holds near zeros in good position (Findings, items 82, 85).

**V5.35 (openness of general position; `Polyfold.exists_isOpen_isGeneralPositionGerm`,
`Polyfold.MPolyfold.IsGeneralPositionAt.congr_nhds`).** Definition 4.21 depends only on the germ of the submanifold. For $X$
tame, $f$ with tame germ data and $(f, x_0)$ in general position at the zero $x_0$, there is an open $W \ni x_0$ such that $S_f \cap W$ is a
smooth finite-dimensional submanifold and at every zero $y \in W$, $(f, y)$ is in good and in general position and $S_f \cap W$ is in
general position at $y$. *Book:* proof of Theorem 5.18, p. 178 ("they will also hold at $(0, y)$ for $y \in S_f$ close to $x$";
"the properties (i)–(ii) hold for all $(\lambda, y) \in \tilde S$"). *Hidden hypotheses:* $X$ tame. *Deviation (not in the book):*
used without proof in the text; proved through V5.34 and Theorem 4.22 (3) (Findings, item 83).

**V5.36 (properties (i)–(ii) of the proof of Theorem 5.18; `Polyfold.StrongBundleChart.IsParamGP`,
`Polyfold.StrongBundleChart.IsParamGP.comp`, `Polyfold.isGeneralPositionGerm_paramSection_of_isParamGP`,
`Polyfold.isParamGP_of_isGeneralPositionGerm`, `Polyfold.exists_sections_isParamGP`).** In a chart centred at $y$, (i) is
$\mathrm{Lin}_g(0)(T_0O) + \operatorname{span}\{\hat t_i(0)\} = K_0$ and (ii) is: every $w \in T_0O$ is $u + e$ with $e \in E_0$ and $\mathrm{Lin}_g(0)u + \sum a_i\hat t_i(0)
= 0$ for some $a$. Adding sections keeps (i)–(ii). For $g$ with tame germ data and a tame chart centred at the zero $y$, (i)–(ii)
hold iff $F$ is in general position at $(0, y)$ (Definition 5.17). If $X$ admits sc-smooth bump functions and $N$ is an
auxiliary norm, finitely many allowable sc⁺-sections supported in any given open $U \ni y$ achieve (i)–(ii). *Book:* proof of
Theorem 5.18, p. 178. *Hidden hypotheses:* none. *Deviation (restated):* the complement $L$ of $T^R_xX$ is spanned by smooth
vectors, so that Lemma 5.11 applies; (i)–(ii) give good position of $F$ first, and then, with $\ker F' = T\tilde S$, general position
(Findings, item 84).

**V5.37 (Theorem 5.18 from a family; `Polyfold.theorem_5_18_of_family`,
`Polyfold.StrongBundle.SolutionSetInGeneralPosition`).** Let $X$ be tame, $f$ an sc-Fredholm section with tame germ data and
compact solution set, $N$ an auxiliary norm. There is an open $U \supseteq S_f$ such that $S_{f+s}$ is compact for every $s \in \Gamma^{+,1}_U(P)$,
and for every sc⁺-section $s_0$ with $\operatorname{supp}s_0 \subseteq U$, $N(s_0) \le 1 - \varepsilon$, and every family of allowable $t_1, \dots, t_m$ for which
$F(\lambda, y) = f(y) + s_0(y) + \sum\lambda_it_i(y)$ is in general position at every $(0, x)$, $x \in S_{f+s_0}$, there are $\delta > 0$ and a null set
$CV$ such that for $|\lambda| < \delta$, $\lambda \notin CV$, $s_\lambda = s_0 + \sum\lambda_it_i$ is allowable and $f + s_\lambda$ is transversal, in general
position at every zero, and $S_{f+s_\lambda}$ is compact, a smooth finite-dimensional submanifold in general position at each
point, whose induced structure has a corner structure and is tame, with $d_{S_{f+s_\lambda}} = d_X$ on it. *Book:* Theorem 5.18, p.
177; proof pp. 178–179. *Hidden hypotheses:* as in V5.38. *Deviation (not in the book):* the theorem with the family as a
hypothesis; Theorem 4.23 is used in its countable-cover form (Findings, item 85).

**V5.38 (Theorem 5.18, generic form; `Polyfold.theorem_5_18`).** Let $X$ be tame and admit sc-smooth bump functions, $f$ an
sc-Fredholm section with tame germ data and compact solution set, $N$ an auxiliary norm. There is an open $U \supseteq S_f$ such
that (1) $S_{f+s}$ is compact for every $s \in \Gamma^{+,1}_U(P)$, and (2) for every sc⁺-section $s_0$ with $\operatorname{supp}s_0 \subseteq U$ and $N(s_0(x))
\le 1 - \varepsilon$ there are allowable $t_1, \dots, t_m$, $\delta > 0$ and a Lebesgue null set $CV$ such that for every $\lambda$ with $|\lambda| < \delta$,
$\lambda \notin CV$, $s_\lambda = s_0 + \sum\lambda_it_i$ is allowable and $f + s_\lambda$ has all the conclusions of V5.37. *Book:* Theorem 5.18, p. 177;
proof pp. 177–179. *Hidden hypotheses:* $X$ tame (the proof uses Theorems 4.22 and 4.23; the opening of §5.3 places the
discussion over a tame strong bundle); $f$ with tame germ data. *Deviation (restated):* the dense set is described as the
parameters off a null set, as in V5.29; "replacing $f + s_0$ by $f$" is not needed (Findings, items 80, 85).

**V5.39 (Theorem 5.18, the text's dense form; `Polyfold.theorem_5_18_dense`).** Under the hypotheses of V5.38 there is an open
$U \supseteq S_f$ such that $S_{f+s}$ is compact for every $s \in \Gamma^{+,1}_U(P)$, and for every allowable $s'$ and $\varepsilon > 0$ an allowable $s$
with $N(s(x) - s'(x)) \le \varepsilon$ for all $x$ such that $f + s$ is transversal, $(f + s, x)$ is in general position at every $x \in
S_{f+s}$, and $S_{f+s}$ is a compact smooth submanifold in general position with a tame corner structure and $d_{S_{f+s}} = d_X$.
*Book:* Theorem 5.18, p. 177. *Hidden hypotheses:* as in V5.38. *Deviation (restated):* density as in V5.30 (Findings,
item 80).

**V5.40 (Theorem 5.19, generic form; `Polyfold.theorem_5_19`, `Polyfold.StrongBundle.IsGoodPositionGermTame.congr_nhds`).** Good
position depends only on the germ of the section. Let $X$ admit sc-smooth bump functions, $f$ be an sc-Fredholm section with
tame germ data and compact solution set, $N$ an auxiliary norm, and $(f, x)$ in good position in a tame chart at every zero $x
\in \partial X$. There is an open $U \supseteq S_f$ with $S_{f+s}$ compact for every $s \in \Gamma^{+,1}_U(P)$, and there are allowable $t_1, \dots, t_m$ with
supports disjoint from $\partial X$, $\delta > 0$ and a null set $CV$ such that for $|\lambda| < \delta$, $\lambda \notin CV$, $s_\lambda = \sum\lambda_it_i$ is allowable,
vanishes on the neighbourhood $X \setminus \operatorname{supp}s_\lambda$ of $\partial X$, $f + s_\lambda$ is transversal and in good position at every zero, and
$S_{f+s_\lambda}$ is compact and, if non-empty, a sub-M-polyfold whose induced structure is tame and a manifold with boundary with
corners. *Book:* Theorem 5.19, p. 180. *Hidden hypotheses:* none. *Deviation (stronger):* $X$ need not be tame;
"arbitrarily small" is $\lambda \to 0$; "$(f, x)$ in good position" is $(f + s, x)$. The text's "as before" would apply the implicit
function theorem to $F$ at the boundary zeros, where $F$ is in general not in good position (gap G.46, on paper); the proof
uses it only at interior points and keeps $f + s = f$ near the boundary zeros. No dense form (gap G.45) (Findings, items
87, 88).

**V5.41 (Definition 5.20; `Polyfold.restrictSection`, `Polyfold.StrongBundle.IsGenCompactHomotopy`,
`Polyfold.StrongBundle.IsGenCompactHomotopy.isCompact_solutionSet_restrict`).** $(f, t)$ is a generalized compact homotopy if
$X$ is tame, $f$ is an sc-Fredholm section with tame germ data and compact solution set, $t : X \to \mathbb R$ is sc-smooth with $t(X) = [0,
1]$, and for every $\tau \in [0, 1]$ the fibre $X_\tau = t^{-1}(\tau)$ is a sub-M-polyfold with tame induced structure on which the
restriction $f|X_\tau$ — the section $a \mapsto (a, f(a))$ of the pull-back of $P$ along the inclusion — is an sc-Fredholm section with
tame germ data. The restrictions then have compact solution sets. *Book:* Definition 5.20, pp. 180–181. *Hidden
hypotheses:* none. *Deviation (restated):* $Y|X_\tau$ is the pull-back bundle (Proposition 2.54); the end problems are the
restrictions to $t^{-1}(0)$, $t^{-1}(1)$, and the identification up to isomorphism (Remark 5.21) is not formalized (gap G.47;
Findings, item 100).

**V5.42 (Lemma 5.23; `Polyfold.lemma_5_23`, `Polyfold.ne_zero_of_isCompl_ker`, `Polyfold.exists_isCompl_ker_of_ne_zero`).** Let
$\ell : T \to \mathbb R$ be linear and non-zero and $Z$ a complement of $\ker\ell$. For every linear $\tau : S \to \mathbb R$ there is a unique linear $b : S \to Z$ with
$\ell \circ b = \tau$, and $\ell \circ (b + a) = \tau$ whenever $\ell \circ b = \tau$ and $a$ takes values in $\ker\ell$. A non-zero complement of $\ker\ell$ exists only
if $\ell \ne 0$, and then it can be spanned by a vector of any spanning set. *Book:* Lemma 5.23, p. 182, and the sentence before
it ("since $x$ is a smooth point, we find a one-dimensional smooth linear sc-subspace $Z$ with $T_xX = Z \oplus \ker dt(x)$").
*Hidden hypotheses:* $dt(x) \ne 0$, which Theorem 5.22 does not assume. *Deviation (explicit):* linear algebra; the hidden
hypothesis is exposed (Findings, item 101).

**V5.43 (the product rule at a level-$1$ point; `Polyfold.scDeriv_smul_apply`, `Polyfold.scDeriv_clm_sub_apply`,
`Polyfold.chartLinCutoff`, `Polyfold.isScSmoothMap_chartLinCutoff`).** For sc-smooth $a : U \to \mathbb R$ and $w : U \to F$, $D(a \cdot w)(z)v =
Da(z)v \cdot w(z) + a(z) \cdot Dw(z)v$; $D(\ell(\rho(\cdot) - p))(z) = \ell \circ D\rho(z)$; and $g = \beta \cdot \ell(\varphi(\cdot) - \varphi(x))$ on $\operatorname{dom}\varphi$, $0$
outside, is sc-smooth when $\beta$ is and $\operatorname{supp}\beta \subseteq \operatorname{dom}\varphi$. *Book:* proof of Lemma 5.24, pp. 182–183. *Hidden hypotheses:*
none. *Deviation (not in the book):* tools for V5.44.

**V5.44 (Lemma 5.24; `Polyfold.exists_scPlusSection_linAt`, `Polyfold.lemma_5_24`).** Let $X$ admit sc-smooth bump functions,
$\Phi$ a strong bundle chart around the smooth point $x$, $z$ the level-$1$ point over $\varphi(x)$, and $e$ a smooth point of the fibre over
$x$. For every continuous linear $\ell$ on the model space and open $U \ni x$ there is an sc⁺-section $s$ with $s(x) = 0$, $\operatorname{supp} s
\subseteq U$ and $\mathrm{Lin}_s(z)v = \ell(v)\Phi(e)_2$ on $T_zO$. Hence, for a section $f$, a finite-dimensional $K \subseteq T_zO$ and a linear $b : K \to
T_zO$ with $\mathrm{Lin}_f(z)(bv) \in \mathbb R\,\Phi(e)_2$ for all $v$, there is an sc⁺-section $s$ with $s(x) = 0$, $\operatorname{supp}s \subseteq U$ and $\mathrm{Lin}_f(z)(bv)
+ \mathrm{Lin}_s(z)v = 0$ for $v \in K$. *Book:* Lemma 5.24, pp. 182–183. *Hidden hypotheses:* that $f'(x) \circ b_\tau$ has its image in
the line of a smooth point $e$ is a hypothesis (the text's justification, "the image of any vector in $T_xS$ belongs to
$Y_\infty$", is not formalized). *Deviation (restated):* $s'(x)$ is read in a chart, $T_xS$ as a finite-dimensional $K$; the graph
of $S$ over $T_xS$ and the case distinction are not needed (Findings, item 102).

**V5.45 (Theorem 5.25; `Polyfold.theorem_5_25`).** Let $X$ be tame and admit sc-smooth bump functions, $f$ a proper
sc-Fredholm section with tame germ data, $N$ an auxiliary norm. There is an open $U \supseteq S_f$ with $S_{f+s}$ compact for every $s \in
\Gamma^{+,1}_U(P)$, and an $s \in \Gamma^{+,1}_U(P)$ such that $(f + s, x)$ is in good position in a tame chart at every $x \in S_{f+s}$, and $f + s$ has
the conclusions of V5.37; in particular $S_{f+s}$ has a corner structure. *Book:* Theorem 5.25, pp. 186–187; proof pp.
187–188. *Hidden hypotheses:* $f$ with tame germ data. *Deviation (restated):* $U$ is the neighbourhood the proof
produces (that of Theorem 5.18), not an arbitrary one with the compactness property; the text's "in view of Theorem 3.54
... in general position" is V5.35, and "$x \in S_f$" is $x \in S_{f+s_0}$ (Findings, item 86).

**V5.46 (Lemma 5.26; `Polyfold.isInGoodPositionIn_of_scComplement_le_reduced`,
`Polyfold.StrongBundle.IsGeneralPositionGerm.isGoodPositionGerm`,
`Polyfold.StrongBundle.IsGeneralPositionGerm.isGoodPositionGermTame`).** In a tame retract, a subspace $N$ of $T_zO$ with an
algebraic complement $B \subseteq T^R_zO$ is in good position to the partial cone, with good complement $B$ and $N \cap C_z$ of non-empty
interior in $N$. Hence for an sc-Fredholm section $f$, a zero $y$ with $(f, y)$ in general position (Definition 5.17) is in good
position (Definition 3.53), and in the tame chart of the germ data when $f$ has tame germ data. *Book:* Lemma 5.26, p. 187;
"clearly general position implies good position", p. 179. *Hidden hypotheses:* none beyond the tame chart of Definition
5.17. *Deviation (stronger):* $X$ need not be tame; the interior condition of Definition 3.21, which the text omits, is proved
(Findings, items 72, 76).

**V5.47 (Definition 5.28; `Polyfold.MPolyfold.IsScSmoothPartitionOfUnity`, `Polyfold.MPolyfold.AdmitsScPartitionsOfUnity`).**
$X$ admits sc-smooth partitions of unity if for every open cover $(U_i)_{i \in \iota}$ (with $\iota$ in the universe of $X$) there is a
partition of unity $(\rho_i)$ — continuous, $\rho_i \ge 0$, locally finite supports, $\sum\rho_i = 1$ — with $\operatorname{supp}\rho_i \subseteq U_i$ and every $\rho_i$
sc-smooth. *Book:* Definition 5.28, p. 192. *Hidden hypotheses:* none. *Deviation (restated):* the index type is
restricted to the universe of $X$, which loses nothing (every cover can be indexed by subsets of $X$) (Findings, item 110).

**V5.48 (sc-smooth functions: algebra, local finiteness, extension by $0$; `Polyfold.MPolyfold.IsScSmoothMap.real_add`,
`Polyfold.MPolyfold.IsScSmoothMap.real_sub`, `Polyfold.MPolyfold.IsScSmoothMap.real_mul`, `Polyfold.isScSmoothMap_real_finsetSum`,
`Polyfold.isScSmoothMap_real_finsetProd`, `Polyfold.isScSmoothMap_real_finsum`, `Polyfold.isScSmoothMap_real_of_eventuallyEq`,
`Polyfold.isScSmoothMap_real_of_chart`).** Sums, differences, products, finite sums and finite products of sc-smooth functions
are sc-smooth; so is a locally finite sum; a function that near every point agrees with an sc-smooth function is sc-smooth; a
function supported in the domain of a chart whose representative is sc-smooth on the retract is sc-smooth on $X$. *Book:*
proof of Theorem 5.37, pp. 195–197. *Hidden hypotheses:* none. *Deviation (not in the book):* used and not stated
(Findings, item 112).

**V5.49 (partitions of unity give bump functions; `Polyfold.MPolyfold.AdmitsScPartitionsOfUnity.admitsBumpFunctions`).** If $X$
admits sc-smooth partitions of unity, it admits sc-smooth bump functions (Definition 5.9 in the reading of V5.16). *Book:*
§5.4.2, p. 192 (the open problem whether the converse holds). *Hidden hypotheses:* none. *Deviation (not in the book):* the
easy direction, which the text implies; the converse is not addressed (Findings, item 119).

**V5.50 (Definition 5.31; `Polyfold.HasContDiffBump`, `Polyfold.AdmitsContDiffPartitionsOfUnity`).** A Banach space admits a
$C^k$-bump function ($k \in \mathbb N \cup \{\infty\}$) if some $C^k$ function $V \to \mathbb R$, not identically zero, has bounded support; it admits
$C^k$ partitions of unity if every open cover has a subordinate partition of unity of $C^k$ functions. *Book:* Definition
5.31, p. 193; partitions of unity of Banach spaces, pp. 192, 197–198. *Hidden hypotheses:* none. *Deviation:* none
(Findings, item 114).

**V5.51 (Definition 5.33; `Polyfold.LocalModel.HasBumpProperty`, `Polyfold.closure_inter_ball_subset`).** A local model $(O, C,
E)$ has the sc-smooth bump function property if for every $x \in O$ and open $W \ni x$ of $E_0$ with $\operatorname{cl}_E(O \cap W) \subseteq O$ there is an
sc-smooth $f : O \to \mathbb R$ with $f(x) \ne 0$ and support (in $O$) inside $W$. A retract is closed near each of its points: $O \cap
\operatorname{cl}B(z, r/2) \subseteq O$ when $B(z, r)$ lies in the open set of the domain of a retraction onto $O$. *Book:* Definition 5.33, p. 194.
*Hidden hypotheses:* none. *Deviation (restated):* "$f \ne 0$" is read as $f(x) \ne 0$, as in V5.16 (Findings, items 41,
43).

**V5.52 (Theorem 5.34; `Polyfold.theorem_5_34`).** $X$ admits sc-smooth bump functions iff some family of charts of $X$
covering $X$ has local models with the sc-smooth bump function property. *Book:* Theorem 5.34, p. 194 ("clearly").
*Hidden hypotheses:* none. *Deviation (explicit):* the extension by $0$ of a local bump can fail to be continuous (a chart
of the unit ball onto the whole space); the proof takes the local bump in a small ball whose preimage has closure inside the
chart domain; "atlas" is read as a covering family of charts (Findings, item 43).

**V5.53 (Proposition 5.35 and M-polyfolds on sc-Hilbert spaces; `Polyfold.LocalModel.hasBumpProperty_of_quadratic`,
`Polyfold.proposition_5_35`, `Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert`).** If $\kappa\|v\|^2 \le b(v, v)$ for a continuous
bilinear $b$ on $E_0$ and some $\kappa > 0$ — in particular if $E_0$ is a Hilbert space, $\|v\|^2 = b(v, v)$ — the local model $(O, C, E)$
has the sc-smooth bump function property. An M-polyfold covered by charts on sc-Hilbert spaces admits sc-smooth bump
functions. *Book:* Proposition 5.35, p. 194; §5.3, p. 173 ("for example, the case if $X$ is built on sc-Hilbert spaces").
*Hidden hypotheses:* none. *Deviation (restated):* "Hilbert space" is a norm given by a continuous bilinear form, not a
second normed structure; translation by a non-smooth point is legitimate because the bump is $C^\infty$ on $E_0$ (Findings,
item 44).

**V5.54 (Definition 5.36; `Polyfold.LocalModel.HasApproxProperty`).** A local model $(O, C, E)$ has the sc-smooth
approximation property if for every open $W$ of $E_0$ with $\operatorname{cl}(O \cap W) \subseteq O$, every continuous $f : O \to [0, 1]$ with support (in
$O$) inside $W$ and every $\varepsilon > 0$ there is an sc-smooth $g : O \to [0, 1]$ with support inside $W$ and $|f - g| \le \varepsilon$ on $O$. *Book:*
Definition 5.36, p. 195. *Hidden hypotheses:* none. *Deviation (restated):* $V = O \cap W$ and the closure is taken in
$E_0$ ($C$ is closed) (Findings, item 110).

**V5.55 (Theorem 5.37 "(i) $\Rightarrow$ (ii)"; `Polyfold.hasApproxProperty_restrict`, `Polyfold.MChart.isClosed_inter_preimage`).**
If $\operatorname{cl}_X(s)$ lies in the domain of a chart $\varphi$, then $\varphi^{-1}(A)$ is closed in $X$ for closed $A \subseteq \varphi(s)$. If $X$ admits sc-smooth
partitions of unity, every chart restricted to an open $s$ with $\operatorname{cl}_X(s) \subseteq \operatorname{dom}\varphi$ has a local model with the sc-smooth
approximation property. *Book:* proof of Theorem 5.37, pp. 195–196. *Hidden hypotheses:* none. *Deviation (narrower):*
the text claims the property for the charts of any atlas; its step "$\operatorname{cl}_X(\varphi^{-1}(V)) \subseteq U$" fails (the chart of the unit ball
onto the whole space), so the restricted charts are used; whether every chart has the property is not settled (Findings,
item 111).

**V5.56 (Theorem 5.37 "(ii) $\Rightarrow$ (i)"; `Polyfold.MChart.exists_small_nhds`, `Polyfold.LocalModel.HasApproxProperty.exists_approx`,
`Polyfold.exists_isScSmoothMap_urysohn`, `Polyfold.admitsScPartitionsOfUnity_of_approx`).** Every point of a chart domain has
arbitrarily small open neighbourhoods $N$ with $\operatorname{cl}_X(N) \subseteq \operatorname{dom}\varphi$ and $\operatorname{cl}(\varphi(N)) \subseteq O$; the approximation property
transports to continuous functions supported in such $N$. If a family of charts covering $X$ has local models with the
approximation property, then disjoint closed sets of $X$ are separated by sc-smooth Urysohn functions $X \to [0, 1]$, and $X$ admits
sc-smooth partitions of unity. *Book:* proof of Theorem 5.37, pp. 196–197. *Hidden hypotheses:* none. *Deviation
(restated):* the refinement "with the same index set" does not exist in general and the closure condition is not arranged
in the text; the proof goes through Urysohn functions and Mathlib's bump coverings; metrizability is not used (Findings,
item 112).

**V5.57 (Theorem 5.37; `Polyfold.theorem_5_37`).** $X$ admits sc-smooth partitions of unity subordinate to any open cover iff
some family of charts of $X$ covering $X$ has local models with the sc-smooth approximation property. *Book:* Theorem 5.37,
p. 195. *Hidden hypotheses:* none. *Deviation (restated):* "atlas" is a covering family of charts; for "(i) $\Rightarrow$ (ii)" it is
the family of V5.55 (Findings, items 111, 112).

**V5.58 (Proposition 5.38; `Polyfold.proposition_5_38`).** If $E_0$ admits $C^\infty$ partitions of unity, every local model $(O, C, E)$
has the sc-smooth approximation property. *Book:* Proposition 5.38, p. 197. *Hidden hypotheses:* "the sc-Banach space
admits smooth partitions of unity" is read for $E_0$. *Deviation (explicit):* not "an immediate consequence of Theorem 5.37"
(which yields some atlas, and would need partitions of unity on an open subset of $C$); the argument of "(i) $\Rightarrow$ (ii)" is
repeated in $E_0$ (Findings, item 113).

**V5.59 (Definition 5.39 and the statement of Theorem 5.40; `Polyfold.cZero`, `Polyfold.mem_cZero_iff`, `Polyfold.norm_cZero`,
`Polyfold.IsCoordinatewiseContDiffEmbedding`, `Polyfold.TorunczykStatement`).** $c_0(\Gamma)$ is the closed subspace of $\ell^\infty(\Gamma)$ of
the functions tending to $0$ along the cofinite filter, equivalently those with $\{\gamma \mid |f(\gamma)| > \varepsilon\}$ finite for every $\varepsilon > 0$,
with the supremum norm; a homeomorphic embedding into $c_0(\Gamma)$ is coordinate-wise $C^k$ if every coordinate is $C^k$. Theorem
5.40 is recorded as a statement, not proved and not used. *Book:* Definition 5.39, Theorem 5.40, p. 198. *Hidden
hypotheses:* none. *Deviation (restated):* the text's "max" norm is the supremum (attained for $f \ne 0$) (gap G.52;
Findings, items 114, 117).

**V5.60 (Definition 5.41; `Polyfold.IsWCG`, `Polyfold.IsReflexive`).** A Banach space is weakly compactly generated if some set
compact in the weak topology has dense linear span; it is reflexive if the canonical map into the bidual is onto. *Book:*
Definition 5.41, p. 198 (reflexivity is used in Proposition 5.42, not defined). *Hidden hypotheses:* none. *Deviation:*
none (Findings, item 114).

**V5.61 (Proposition 5.42; `Polyfold.proposition_5_42_reflexive`, `Polyfold.proposition_5_42_separable`,
`Polyfold.span_closedBall_eq_top`).** (i) A reflexive Banach space is WCG; (ii) a separable Banach space is WCG. *Book:*
Proposition 5.42, p. 198. *Hidden hypotheses:* none. *Deviation:* none; Kakutani's theorem is Mathlib's Banach–Alaoglu
argument, and in (ii) a dense sequence of the space, suitably scaled, replaces the text's $\{0\} \cup \{x_n/n\}$ (Findings, item 115).

**V5.62 (the statement of Theorem 5.43, and Hilbert spaces; `Polyfold.GodefroyTroyanskiWhitfieldZizlerStatement`,
`Polyfold.hasContDiffBump_of_hilbert`, `Polyfold.isReflexive_of_hilbert`).** Theorem 5.43 is recorded as a statement: a WCG
space with a $C^k$-bump function admits $C^k$ partitions of unity. A Banach space whose norm comes from a continuous bilinear
form has a $C^\infty$-bump function and, if complete, is reflexive. *Book:* Theorem 5.43, p. 198; proof of Corollary 5.44, p.
199 ("a Hilbert space is reflexive"). *Hidden hypotheses:* none. *Deviation:* Theorem 5.43 is not proved (gap G.53)
(Findings, items 116, 117).

**V5.63 (Corollary 5.44; `Polyfold.corollary_5_44`, `Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert`).** If $E_0$ is a
Hilbert space ($\|v\|^2 = b(v, v)$) and Theorem 5.43 holds for $E_0$ and $k = \infty$, the local model $(O, C, E)$ has the sc-smooth
approximation property. An M-polyfold covered by charts on such spaces admits sc-smooth partitions of unity. *Book:*
Corollary 5.44, p. 199. *Hidden hypotheses:* Theorem 5.43 for $E_0$ (cited, not proved). *Deviation (narrower):* Theorem 5.43
is an explicit hypothesis; the proof's "in view of Theorem 5.37" is Proposition 5.38, and the bump Theorem 5.43 needs is the
classical $C^\infty$ one (Findings, item 116).

### What is not verified in this chapter

- p. 173, Corollary 5.8 as one statement for all $i$: it is verified for each fixed $i$ by iterating the shift ($i = 1, 2$ stated;
  V5.13, V5.14); a family $P^i$ indexed by $i$, the identification of the iterated base $(X^1)^1$ with $X_2$ as a topological
  space (the sets agree; gap G.6), and the tame form of the conclusion (the tameness of the index raises of tame charts) are not
  formalized (Findings, items 145, 146).
- p. 174, the non-completeness of $(\Gamma^{+,1}_U(P), \rho)$ in the text's setting: it is proved for the trivial bundle over $\mathbb R$,
  and it fails for $U = \emptyset$ and over a point (V5.21); a general sufficient condition is not formalized, and neither is the
  identification of the completion of Remark 5.12 with the uniform $N$-limits of allowable sections (V5.22) (Findings, items
  152, 153).
- p. 173 and p. 192, Definitions 5.9 and 5.29: whether the weak reading gives a bump function non-zero at a non-smooth point
  (V5.16; Findings, item 163).
- p. 175, Remark 5.14, and p. 176, Remark 5.16: comments on [21] and a sketch of the homotopy argument "once we have finished
  our general discussion of the boundary case"; not formalized (gaps G.43, G.44).
- p. 180, a dense form of Theorem 5.19: the generic form gives perturbations $\sum\lambda_it_i$ with $\lambda$ arbitrarily small (V5.40), not
  density around a given allowable $s'$ (gap G.45).
- p. 180, Finding 88: at a zero $(0, x)$, $x \in \partial X$, where all $t_i$ vanish, the parametrized section is in good position only if $\ker
  f'(x) + E_x \supseteq T_xX$, a general position condition that good position does not imply; checked on paper only. The proof of
  Theorem 5.19 avoids the point (V5.40) (gap G.46).
- p. 181, Remark 5.21 (end problems up to isomorphism): not formalized; Definition 5.20 takes the restrictions as the end
  problems (V5.41) (gap G.47).
- p. 181, Theorem 5.22 (Morse-type structure): needs finite-dimensional Morse theory on manifolds with boundary, the
  cotangent bundle of the solution set, a parametric Sard theorem and a trivialization $\Phi_\lambda : S \to S_\lambda$ of the family, and the
  hidden hypothesis $dt(x) \ne 0$ of V5.42; Lemmas 5.23 and 5.24 are verified (V5.42–V5.44) (gap G.48).
- p. 188, Theorem 5.27 (cobordism between good position perturbations): its proof is left to the reader (gap G.49).
- p. 193, Theorem 5.32 (Bonic–Frampton, cited from [9]): not stated (gap G.50).
- pp. 193–194, the $L^p$ and Sobolev remark: the norms of $W^{k,p}(\Omega)$, the bump function of $L^p$, $W^{1,4}(\Omega)$ against
  $W^{1,3/2}(\Omega)$ and the question it raises; it needs Sobolev spaces and their sc-structures (gap G.1) and Theorem 5.32 (gap
  G.51).
- p. 198, Theorems 5.40 (Toruńczyk) and 5.43 (Godefroy–Troyanski–Whitfield–Zizler), cited from [9], [12]: recorded as
  statements (V5.59, V5.62), not proved; Theorem 5.43 is an explicit hypothesis of Corollary 5.44 (V5.63) (gaps G.52, G.53).
- Definitions 5.15 and 5.17 in $T_xX$: verified in charts (V5.23, V5.31), with chart independence for Definition 5.17 at the
  zeros near a zero in good position (V5.34), since $T_xX$ carries no linear structure here (gap G.7 of Chapter 2).

---

## 7. Chapter 6 (HWZ §§6.1–6.7): verified except Proposition 6.28 (1), the global parts of Theorem 6.41 and Remark 6.42, and Theorem 6.43

Chapter 6 of Part I (preprint pp. 200–237) builds the orientation theory of sc-Fredholm sections. §6.1 defines the space
$\mathrm{Lin}(f, x)$ of linearizations at a smooth point (Definition 6.1) and the index; Proposition 6.2, the stability of
the index along paths, was verified with Chapter 3 (V3.98). §6.2 fixes the conventions for determinant lines
$\lambda(E) = \Lambda^{\max}E$: the isomorphism $\iota : \lambda(E^*) \to \lambda^*(E)$ (Definition 6.3, Proposition 6.4) and the
isomorphism $\Phi_E$ of a four-term exact sequence, formula (91) (Lemma 6.5, Proposition 6.6). §6.3 defines the
determinant $\det(T) = \lambda(\ker T) \otimes \lambda^*(\operatorname{coker} T)$ of a Fredholm operator and its orientations
(Definitions 6.7, 6.8), the good left-projections $\Pi_T$ (Definition 6.9, Lemma 6.10), the isomorphisms $\gamma^P_T :
\det(T) \to \det(PT)$ (Lemma 6.11, Proposition 6.12, Corollary 6.13), the stabilization $T_\varphi$ with formula (94)
(Lemma 6.14, Proposition 6.15) and the direct sum convention (Definition 6.16). §6.4 builds the local determinant bundles
$\mathrm{DET}(T, P, \varepsilon)$ (Lemmas 6.17–6.19, Proposition 6.20, Lemma 6.21) and the determinant line bundle
$\mathrm{DET}(E, F)$ over the Fredholm operators (Definition 6.22, Propositions 6.23, 6.24, Lemma 6.25). §6.5 restricts
it to $\mathrm{Lin}(f, x)$ (Proposition 6.26, Definition 6.27), propagates orientations along sc-smooth paths in small
neighbourhoods (Proposition 6.28, Lemmas 6.29–6.31, Proposition 6.32 with Lemmas 6.33, 6.34, Theorem 6.35, Definition
6.36), globalizes the propagation to a functor $\Gamma_f$ on the path category (Theorem 6.37), defines orientability and
orientations of sc-Fredholm sections (Definitions 6.38–6.40), and orients the solution set (Theorem 6.41) and the
sections $f + s$ over $X \times [0, 1]$ (Remark 6.42). §6.6 states the invariant $\Psi_{(f,o)}$ (Theorem 6.43).
Appendix 6.7 proves Lemma 6.5 (§6.7.1) and Proposition 6.12 (§6.7.2).

What is verified. **Theorems 6.35 and 6.37 hold**, with the readings recorded below, and so do Propositions 6.4, 6.6,
6.12, 6.15, 6.20, 6.23, 6.24, 6.26, 6.32, Proposition 6.28 with (1′) in place of (1), Lemmas 6.5, 6.10, 6.11, 6.14, 6.17,
6.18, 6.21, 6.25, 6.31, 6.33, 6.34, Lemma 6.29 in the form the text uses afterwards, the kernel statement of Lemma 6.30,
Corollary 6.13, the equivalence of Definitions 6.38 and 6.39, Theorem 6.41 in the form of tangent orientations that
vary continuously along the paths of zeros in a chart, and Remark 6.42 at a point. Every definition of the chapter
is formalized: Definitions 6.1 (V6.1), 6.3 (V6.3), 6.7 (V6.8), 6.8 (V6.9), 6.9 (V6.10), 6.16 (V6.19), 6.22 (V6.25), 6.27
(V6.31), 6.36 (V6.50), 6.38 (V6.58), 6.39 (V6.59), 6.40 (V6.60). Several places of the text needed more than a reading.
(a) *Lemma 6.10.* The projection of the text's proof does not lie below the two given projections, as we read it (an
example on $\mathbb R^2$); the lemma holds by another construction, without the hypothesis that $T$ is Fredholm (V6.11).
The 2017 version drops the lemma and remarks that a common lower bound need not exist; with the order of Definition 6.9
it always exists, so the preprint's route to Lemma 6.25 is the one formalized. (b) *Signs.* The isomorphism $\Phi_E$ of
formula (94) does not vary continuously in the topology of $\mathrm{DET}$ where $\dim\operatorname{coker} T$ changes
parity, as we read it, so the orientations it carries along a family need not be continuous (an example, V6.40); the
propagation uses $(-1)^{\dim\operatorname{coker}T}\Phi_E$ at both end points (V6.41). The map $h \mapsto \tilde h$ of
Remark 6.42 has the same property, and the same sign is used there (V6.62). (c) *Contractibility.* Proposition 6.28 (1),
the sc-smooth contractibility of the neighbourhood, is not established by its proof as we read it; what Theorem 6.35 uses
is (1′), two paths with the same end points are homotopic in a larger region where (3) holds, and that is proved (V6.32,
V6.48). (d) *The chart-free objects.* $T_xX$, $Y_x$, $\mathrm{Lin}(f, x)$ and $\mathrm{Or}^f_x$ are made in a chart point
and identified between charts by explicit transition maps, and the local propagation is shown to be independent of the
chart (V6.53, V6.54). (e) *Omitted proofs.* The orientability of a line bundle over a convex set (V6.29), the
general position of Lemma 6.29 (V6.33), the "simple computation" of Lemma 6.33 (V6.45), the covering argument of
Theorem 6.37 (V6.56) and the equivalence of Definitions 6.38 and 6.39, stated without proof (V6.59), are proved. Not
verified: Theorem 6.43 and the notion of an admissible section of §6.6, Proposition 6.28 (1), the orientation of the
solution set as an abstract manifold and the perturbation paragraph after Theorem 6.41, the global part of Remark 6.42,
the general Lemma 6.19, several remarks, and the facts on paths recalled on p. 201 (see the list at the end of this
section).

The setting. $X$ and $Y$ are paracompact Hausdorff spaces, as for every M-polyfold of the project, and from §6.5 on $X$ is
tame and $f$ is an sc-Fredholm section with tame germ data (Definition 3.51), the reading of Chapter 5. The linearization
$(f - s)'(x) : T_xX \to Y_x$ is read in a strong bundle chart, at a *chart point* $(c, z)$ of $x$, as the operator $T_zO =
Dr(z)E \to K_z = \rho(z)F$ on level $0$, because $T_xX$ carries no linear structure here (gaps G.6, G.7, G.13); the text's
$f - s$ with $s(x) = f(x)$ is $f + s$ with $(f + s)(x) = 0$. The sc⁺-sections are global, made with sc-smooth bump
functions: the text assumes sc-smooth partitions of unity from §6.2 on (p. 203), and these give bump functions (V5.49)
(Findings, item 43).
Paths, homotopies and families are maps on $\mathbb R$, $\mathbb R^2$, $\mathbb R^n$ of which only $[0, 1]$, $[0, 1]^2$,
$[0, 1]^n$ matters (decision D2, as for Proposition 6.2 in V3.98), and $X \times [0, 1]$ is read as $\mathbb R^n \times X$
with the pull-back $\pi^*P$ of the bundle along the projection. An orientation of a line is a ray (Mathlib's `Module.Ray`),
and an orientation of a topological line bundle is a choice of rays given near every point by a continuous nowhere-zero
section. Findings referred to below are those of `Exposition/Findings.md`, "Chapter 6".

**V6.1 (Definition 6.1, the space $\mathrm{Lin}(f, x)$; `Polyfold.ChartPoint`, `Polyfold.ChartPoint.T`,
`Polyfold.ChartPoint.K`, `Polyfold.ChartPoint.IsScPlusOp`, `Polyfold.ChartPoint.linSet`,
`Polyfold.ChartPoint.mem_linSet_iff`, `Polyfold.ChartPoint.exists_isScPlusOp_linAt_eq`,
`Polyfold.ChartPoint.linSet_nonempty`, `Polyfold.ChartPoint.isScPlusOp_sub_of_mem_linSet`,
`Polyfold.ChartPoint.isFredholm_isIndexAt_of_mem_linSet`, `Polyfold.ChartPoint.exists_index_linSet`,
`Polyfold.ChartPoint.fredholmIndex_of_mem_linSet`, `Polyfold.ChartPoint.convex_linSet`,
`Polyfold.MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`).** At a chart point $p = (c, z)$ of a smooth point $x$,
$\mathrm{Lin}(f, x)$ is the set of operators $(f + s)'(x) + a : T_zO \to K_z$ for an sc⁺-section $s$ with $(f + s)(x) = 0$
and an sc⁺-operator $a$; for one such $s$ it is $(f + s)'(x)$ plus the sc⁺-operators. Two such sections give
linearizations that differ by an sc⁺-operator; the members of $\mathrm{Lin}(f, x)$ are Fredholm on level $0$, all of the
index $\mathrm{ind}(f, x)$ of V3.98; $\mathrm{Lin}(f, x)$ is convex, and it is not empty when $P$ has sc⁺-sections through
the smooth points of its fibres, which bump functions give. *Book:* §6.1, pp. 200–201 (the sections $s$ and the
paragraph before the definition), Definition 6.1, p. 201, and p. 219 (convexity); the index and Proposition 6.2 are
V3.98. *Hidden hypotheses:* an sc⁺-section through $f(x)$; the text constructs a local one in a chart, the project uses
global ones (`HasScPlusSectionsThrough`), which exist under the standing bump functions. *Deviation (restated):* made in
a chart point; global sections; "sc-Fredholm" is proved on level $0$, which is what the determinant lines use, and not on
every level (gap G.64). The paragraph before the definition compares $(f - s)'(x)$ with itself where $(f - t)'(x)$ is
meant (possible misprint) (Findings, items 40, 41).

**V6.2 (the determinant lines $\lambda(E)$, $\lambda^*(E)$ and the maps $\lambda(\Phi)$; `Polyfold.maxPow`,
`Polyfold.maxPowDual`, `Polyfold.finrank_maxPow`, `Polyfold.wedge`, `Polyfold.wedge_eq_det_smul`,
`Polyfold.wedge_append_basis_left`, `Polyfold.wedge_append_basis_right`, `Polyfold.wedge_append_add_left`,
`Polyfold.wedge_append_add_right`, `Polyfold.dualVec`, `Polyfold.dualVec_self`, `Polyfold.eq_dualVec_of_apply_eq_one`,
`Polyfold.maxPowMap`, `Polyfold.maxPowMap_wedge`, `Polyfold.maxPowMap_comp`, `Polyfold.maxPowMap_ne_zero_iff`,
`Polyfold.maxPowDualMap`).** $\lambda(E)$ is the top exterior power of a finite-dimensional real space and $\lambda^*(E)$
its dual, both lines; a change of basis multiplies the wedge by the determinant, also in one block of a two-block wedge,
and adding to one block vectors of the span of the other does not change the wedge. For $v \ne 0$ in a line, $v^*$ is the
functional with $v^*(v) = 1$. For $\dim E = \dim F$, $\lambda(\Phi)(a_1 \wedge \dots \wedge a_n) = \Phi a_1 \wedge \dots
\wedge \Phi a_n$, with $\lambda(\Psi\Phi) = \lambda(\Psi)\lambda(\Phi)$, nonzero iff $\Phi$ is bijective; $\lambda^*(\Phi)$ is
its dual. *Book:* §6.2, pp. 203–204. *Hidden hypotheses:* none. *Deviation:* none.

**V6.3 (Definition 6.3; `Polyfold.iotaDual`, `Polyfold.iotaDual_wedge_wedge`, `Polyfold.iotaDual_wedge_dualBasis`,
`Polyfold.iotaDual_ne_zero`).** $\iota : \lambda(E^*) \to \lambda^*(E)$, $\iota(e_1^* \wedge \dots \wedge e_n^*)(a_1 \wedge \dots
\wedge a_n) = \det(e_i^*(a_j))$, is a nonzero map of lines, and for a basis and its dual basis $\iota(e_1^* \wedge \dots
\wedge e_n^*) = (e_1 \wedge \dots \wedge e_n)^*$. *Book:* Definition 6.3, p. 204. *Hidden hypotheses:* none.
*Deviation:* none; the convention $\lambda(\{0\}^*) = \mathbb R$ is the zeroth exterior power, and the text's matrix is the
transpose of Mathlib's, with the same determinant.

**V6.4 (Proposition 6.4; `Polyfold.proposition_6_4`).** For an isomorphism $\Phi : E \to F$ of finite-dimensional spaces,
$\lambda^*(\Phi) \circ \iota = \iota \circ \lambda(\Phi^*)$. *Book:* Proposition 6.4, p. 205. *Hidden hypotheses:* none.
*Deviation:* none.

**V6.5 (four-term exact sequences and the isomorphism $\Phi_E$ of (91); `Polyfold.FourTermExact`,
`Polyfold.FourTermExact.Choice`, `Polyfold.FourTermExact.Choice.value`, `Polyfold.FourTermExact.canonicalChoice`,
`Polyfold.FourTermExact.phi`, `Polyfold.FourTermExact.phi_ne_zero`, `Polyfold.FourTermExact.phiEquiv`).** For an exact
sequence $0 \to A \to B \to C \to D \to 0$ of finite-dimensional spaces, a *choice* is the data of (91): complements $Z$ of
$\alpha(A)$ in $B$ and $V$ of $\beta(B)$ in $C$, bases of $A$, $D$, $Z$, and the $\gamma$-preimages in $V$ of the basis of
$D$; $\Phi_E : \lambda(A) \otimes \lambda^*(D) \to \lambda(B) \otimes \lambda^*(C)$ is the linear map given by (91) for one
choice, an isomorphism of lines. *Book:* §6.2, p. 206, formula (91) with its two ordering conventions. *Hidden
hypotheses:* none. *Deviation:* none.

**V6.6 (Lemma 6.5; `Polyfold.FourTermExact.lemma_6_5`).** Formula (91) holds for every choice: $\Phi_E$, defined from one
choice, maps $(a_1 \wedge \dots \wedge a_n) \otimes (d_1 \wedge \dots \wedge d_l)^*$ to the right-hand side of (91) computed
with any other choice. *Book:* Lemma 6.5, p. 206; proof in §6.7.1 (V6.63). *Hidden hypotheses:* none. *Deviation
(restated):* "does not depend on the choices" is read as this, the strongest form and the one every later computation
of $\gamma^P_T$ uses (Findings, item 1).

**V6.7 (Proposition 6.6; `Polyfold.contractDual`, `Polyfold.FourTermExact.psi`, `Polyfold.FourTermExact.proposition_6_6`).**
With $\bar\iota(v \otimes b \otimes \varphi) = \varphi(v)\, b$ and $\Psi_E(c \otimes h) = \bar\iota(c \otimes \Phi_E(h))$,
$\Psi_E$ maps the wedge of the basis of $C$ of (91), tensored with $(a_1 \wedge \dots \wedge a_n) \otimes (d_1 \wedge \dots
\wedge d_l)^*$, to $\alpha(a_1) \wedge \dots \wedge \alpha(a_n) \wedge b'_1 \wedge \dots \wedge b'_{m-n}$. *Book:* (92) and
Proposition 6.6, p. 207. *Hidden hypotheses:* none. *Deviation (restated):* the wedge in $C$ is taken in the order of
(91); the statement exchanges the names of its two blocks (possible misprint) (Findings, item 2).

**V6.8 (Definition 6.7; `Polyfold.linDet`, `Polyfold.fredholmDet`, `Polyfold.finrank_fredholmDet`,
`Polyfold.linDetEquivOfEq`).** $\det(T) = \lambda(\ker T) \otimes \lambda^*(F / R(T))$, a line for $T$ Fredholm; equal
operators have identified determinants. *Book:* Definition 6.7, p. 208. *Hidden hypotheses:* none. *Deviation:* none;
the alternative definition $\lambda(\ker T) \otimes \lambda(\operatorname{coker}(T)^*)$ mentioned after it is not
formalized (gap G.57).

**V6.9 (Definition 6.8; `Polyfold.FredholmOrientation`, `Polyfold.nonempty_fredholmOrientation`,
`Polyfold.exists_two_fredholmOrientation`).** An orientation of $T$ is a ray of $\det(T)$; a Fredholm operator has exactly
two. *Book:* Definition 6.8, p. 208. *Hidden hypotheses:* none. *Deviation:* none.

**V6.10 (Definition 6.9 and the facts after it; `Polyfold.IsGoodLeftProj`, `Polyfold.goodLeftProjs`, `Polyfold.ProjLE`,
`Polyfold.ProjLE.refl`, `Polyfold.ProjLE.antisymm`, `Polyfold.ProjLE.trans`, `Polyfold.IsGoodLeftProj.isFredholm`,
`Polyfold.IsGoodLeftProj.fredholmIndex_eq_zero`, `Polyfold.IsGoodLeftProj.isFredholm_comp`,
`Polyfold.IsGoodLeftProj.fredholmIndex_comp`, `Polyfold.IsGoodLeftProj.finiteDimensional_quotient_inf`,
`Polyfold.exists_isGoodLeftProj`).** A good left-projection for $T$ is a bounded projection $P$ with $\dim F/R(P) < \infty$
and $R(PT) = R(P)$; $P \le Q$ iff $P = PQ = QP$ is a partial order. A good left-projection is Fredholm of index $0$, $PT$
is Fredholm with $\mathrm{ind}(PT) = \mathrm{ind}(T)$, $R(P) \cap R(P')$ has finite codimension, and $\Pi_T$ is not empty
for $T$ Fredholm. *Book:* Definition 6.9 and the paragraphs after it, p. 208. *Hidden hypotheses:* none; that $\Pi_T \ne
\emptyset$ is used from Lemma 6.11 on and is not stated. *Deviation:* none (Findings, item 3).

**V6.11 (Lemma 6.10; `Polyfold.lemma_6_10`, `Polyfold.lemma_6_10_text_reading`).** For $P, P' \in \Pi_T$ there is $P'' \in
\Pi_T$ with $P'' \le P$ and $P'' \le P'$, for any bounded $T$. On $\mathbb R^2$ with $T = 1$ there are $P, P' \in \Pi_T$
such that no projection with range $R(P) \cap R(P')$ lies below both. *Book:* Lemma 6.10, p. 208, proof pp. 208–209.
*Hidden hypotheses:* none. *Deviation (stronger):* $T$ need not be Fredholm, and the construction differs from the
text's: the text's $P''$ has range $R(P) \cap R(P')$, and as we read it $P'' = P''P$ does not hold for it in general; the
formalized $P''$ projects onto $R(P) \cap R(P') \cap N$, for a closed finite-codimensional $N$ meeting $\ker P + \ker P'$
only in $0$, along a complement containing $\ker P + \ker P'$ (Findings, item 4).

**V6.12 (Lemma 6.11; `Polyfold.projSeqJ`, `Polyfold.projSeqPhi`, `Polyfold.projSeqPi`, `Polyfold.lemma_6_11`,
`Polyfold.projSeq`).** For $P \in \Pi_T$ the sequence $0 \to \ker T \to \ker(PT) \to F/R(P) \to \operatorname{coker} T \to 0$,
with the inclusion, $x \mapsto Tx + R(P)$ and $y + R(P) \mapsto (I - P)y + R(T)$, is exact. *Book:* Lemma 6.11, p. 209.
*Hidden hypotheses:* none. *Deviation:* none.

**V6.13 (the isomorphism $\gamma^P_T$; `Polyfold.gammaProj`, `Polyfold.gammaProj_tmul`, `Polyfold.gammaProj_wedge_tmul`).**
$\gamma^P_T : \det(T) \to \det(PT)$ is $\Phi_{E(T,P)}$ followed by the identification of $\lambda^*(F/R(P))$ with
$\lambda^*(F/R(PT))$; on wedges it is given by (91), for any choice. *Book:* p. 210. *Hidden hypotheses:* none.
*Deviation:* none; "recalling $R(P) = R(PT)$" is read as this identification (Findings, item 5).

**V6.14 (Proposition 6.12; `Polyfold.proposition_6_12`, `Polyfold.IsGoodLeftProj.of_projLE`,
`Polyfold.comp_comp_eq_of_projLE`).** For $P \le Q$ in $\Pi_T$, $QT$ is Fredholm, $P \in \Pi_{QT}$, and $\gamma^P_{QT} \circ
\gamma^Q_T = \gamma^P_T$, up to the identification $\det(P(QT)) = \det(PT)$ of the equal operators $PQT = PT$. *Book:*
Proposition 6.12, p. 211; proof in §6.7.2 (V6.64). *Hidden hypotheses:* none. *Deviation:* none.

**V6.15 (Corollary 6.13; `Polyfold.corollary_6_13`).** For $P \le S$ and $P \le R$ in $\Pi_T$, $(\gamma^P_{RT})^{-1} \circ
\gamma^P_{ST} = \gamma^R_T \circ (\gamma^S_T)^{-1}$, so the left side does not depend on $P$. *Book:* Corollary 6.13, p.
211. *Hidden hypotheses:* none. *Deviation:* none.

**V6.16 (the stabilization and Lemma 6.14; `Polyfold.stabJ`, `Polyfold.stabPi`, `Polyfold.stabClass`,
`Polyfold.lemma_6_14`, `Polyfold.stabSeq`, `Polyfold.exists_surjective_coprod`).** For $T$ Fredholm and $\varphi :
\mathbb R^n \to F$ with $T_\varphi(e, r) = Te + \varphi r$ onto, the sequence $0 \to \ker T \to \ker T_\varphi \to \mathbb R^n
\to F/R(T) \to 0$, with $j(e) = (e, 0)$, $\pi(e, r) = r$ and $[\varphi](r) = \varphi(r) + R(T)$, is exact; a stabilizing
$\varphi$ exists for every Fredholm $T$. *Book:* pp. 211–212 and Lemma 6.14, p. 212. *Hidden hypotheses:* none.
*Deviation:* none; the proof writes $j(e) = (0, e)$ for $(e, 0)$ (possible misprint) (Findings, item 8).

**V6.17 (formula (94); `Polyfold.stdWedge`, `Polyfold.stabOne`, `Polyfold.stabPsi`, `Polyfold.stabPsi_dualVec`).**
$\psi : \lambda^*(\mathbb R^n) \to \lambda^*(\{0\})$, $(e_1 \wedge \dots \wedge e_n)^* \mapsto 1^*$ for the standard basis,
satisfies $\psi((c_1 \wedge \dots \wedge c_n)^*) = \det[c_1, \dots, c_n]^{-1}\, 1^*$ for every basis. *Book:* formula (94),
p. 212. *Hidden hypotheses:* none. *Deviation:* none.

**V6.18 (Proposition 6.15; `Polyfold.stabIota`, `Polyfold.stabIota_bijective`, `Polyfold.stab_card_eq`,
`Polyfold.isCompl_range_stabPi_span`, `Polyfold.proposition_6_15`).** $\iota_\varphi = (1 \otimes \psi) \circ \Phi_E :
\det(T) \to \det(T_\varphi)$ is an isomorphism, and for a basis $a$ of $\ker T$, $\bar c_1, \dots, \bar c_m$ with
$[\varphi](\bar c_i)$ a basis of $F/R(T)$ and $\bar b_i = (b_i, r_i)$ completing $(a, 0)$ to a basis of $\ker T_\varphi$,
$\iota_\varphi(h) = \det(\bar c, r)^{-1}\, ((a_1, 0) \wedge \dots \wedge (a_k, 0) \wedge \bar b_1 \wedge \dots \wedge \bar
b_l) \otimes 1^*$; the $r_i$ and $\bar c_j$ form a basis of $\mathbb R^n$. *Book:* Proposition 6.15, p. 213. *Hidden
hypotheses:* none. *Deviation (restated):* the identity $m + l = n$, needed to form $\det(\bar c, r)$, is a hypothesis of
the statement and is proved to hold always; that the $r_i$ and $\bar c_j$ form a basis, which the text notices, is
proved; the statement calls $\psi$ "$\varphi$" (possible misprint). The identification (95) and the maps $V \otimes
\lambda(\mathbb R^n) \to V$, $V \otimes \lambda^*(\mathbb R^n) \to V$ after the proposition are not formalized (gap G.58)
(Findings, items 9, 10).

**V6.19 (Definition 6.16; `Polyfold.kerInl`, `Polyfold.kerInr`, `Polyfold.cokerInl`, `Polyfold.cokerInr`,
`Polyfold.kerProdEquiv`, `Polyfold.cokerProdEquiv`, `Polyfold.finrank_ker_prodMap`, `Polyfold.finrank_coker_prodMap`,
`Polyfold.isFredholm_prodMap`, `Polyfold.directSumVec`, `Polyfold.directSumDet`, `Polyfold.directSumVec_eq_smul`,
`Polyfold.definition_6_16`, `Polyfold.directSumDet_bijective`).** $T \oplus S$ is Fredholm, with $\ker(T \oplus S) \cong
\ker T \times \ker S$ and $\operatorname{coker}(T \oplus S) \cong \operatorname{coker} T \times \operatorname{coker} S$, and
$\det(T) \otimes \det(S) \to \det(T \oplus S)$, $h \otimes h' \mapsto (a \wedge a') \otimes (d \wedge d')^*$, is an isomorphism
satisfying the formula for every choice of bases. *Book:* Definition 6.16, p. 214. *Hidden hypotheses:* none.
*Deviation:* none; "natural" is read as the formula for every choice, as in Lemma 6.5 (Findings, item 11).

**V6.20 (Lemma 6.17; `Polyfold.FredholmOp`, `Polyfold.projRestrict`, `Polyfold.lemma_6_17`).** For a bounded $T$, $P \in
\Pi_T$ and a topological complement $Y$ of $\ker(PT)$, there is $\varepsilon > 0$ such that for $\|S - T\| < \varepsilon$,
$P \in \Pi_S$ and $PS|_Y : Y \to R(P)$ is a topological isomorphism. *Book:* Lemma 6.17, p. 214. *Hidden hypotheses:*
none. *Deviation (stronger):* the hypothesis that $T$ is Fredholm is not used; a topological complement is an
algebraic complement with a continuous projection (Findings, item 20).

**V6.21 (Lemma 6.18; `Polyfold.LocalDetChart`, `Polyfold.LocalDetChart.ySol`, `Polyfold.LocalDetChart.kerMap`,
`Polyfold.LocalDetChart.kerProj`, `Polyfold.LocalDetChart.lemma_6_18`).** A *local determinant chart* is the data $(T,
P, Y, \varepsilon)$ of Lemma 6.17 with its conclusions. The solution $y(k, S) = -(PS|_Y)^{-1}PSk$ is continuous in $(k,
S)$, and $(S, k) \mapsto (S, k + y(k, S))$ is a continuous map onto $\bigcup_{\|S - T\| < \varepsilon}\{S\} \times
\ker(PS)$, inverted by the continuous projection onto $\ker(PT)$ along $Y$. *Book:* Lemma 6.18, p. 215. *Hidden
hypotheses:* none. *Deviation (restated):* "is a trivial vector bundle" is stated as this trivialization and its
inverse (Findings, item 21).

**V6.22 (Lemma 6.19 in the case used, and Proposition 6.20; `Polyfold.LocalDetChart.kerFrame`,
`Polyfold.LocalDetChart.frame`, `Polyfold.LocalDetChart.frame_ne_zero`, `Polyfold.proposition_6_20`).** Over the ball of
a local determinant chart, $\omega(S) = (k_1(S) \wedge \dots \wedge k_n(S)) \otimes (e_1 \wedge \dots \wedge e_l)^*$, with
$k_i(S) = k_i + y(k_i, S)$ and a constant basis $e$ of $F/R(P) = F/R(PS)$, is a nowhere-zero frame of
$\mathrm{DET}(T, P, \varepsilon)$, and the frames of two charts with the same $P$ differ by a continuous nowhere-zero
factor. *Book:* Lemma 6.19 and Proposition 6.20, p. 216. *Hidden hypotheses:* none. *Deviation (narrower):* Lemma 6.19
(exterior powers, duals, sums and tensor products of topological vector bundles) is not formalized in general (gap
G.59); it is applied only to trivial bundles, and Proposition 6.20 is proved with the explicit frames; "in a natural way"
is read as the relation between frames (Findings, item 22).

**V6.23 (Lemma 6.21; `Polyfold.LocalDetChart.gammaProj_frame_eq`, `Polyfold.lemma_6_21`).** For $Q \le P$, $\gamma^Q_{PS}$
maps the $P$-frame at $S$ to a continuous nowhere-zero multiple of the $Q$-frame, on the common ball of any two local
determinant charts. *Book:* Lemma 6.21, p. 216, sketch pp. 216–217. *Hidden hypotheses:* none. *Deviation (stronger):*
two charts with different centres and radii, the form Lemma 6.25 uses; the text's sketch (extend the kernel sections of
$PS$ to sections spanning $\ker(QS)$) is the proof (Findings, item 23).

**V6.24 ($\mathrm{DET}(E, F)$ and the charts $\gamma_{(T,P,\varepsilon)}$; `Polyfold.DetFiber`,
`Polyfold.LocalDetChart.pretriv`, `Polyfold.LocalDetChart.coord`, `Polyfold.exists_localDetChart`,
`Polyfold.detPrebundle`).** The fibre over a Fredholm $S$ is $\det(S)$; a local determinant chart gives the
pretrivialization $(S, h) \mapsto (S, \omega(S)^*(\gamma^P_S h))$ with model fibre $\mathbb R$; every Fredholm operator is
the centre of one; together they form a Mathlib vector prebundle, whose topology and bundle structure are those of
$\mathrm{DET}(E, F)$. *Book:* p. 217. *Hidden hypotheses:* none. *Deviation (restated):* $\gamma_{(T,P,\varepsilon)}$ is
read in the frame of Proposition 6.20 (Findings, item 24).

**V6.25 (Definition 6.22; `Polyfold.detBasis`).** $\mathcal B$ is the collection of sets lying over the ball of some
chart whose image in $\text{ball} \times \mathbb R$ is open. *Book:* Definition 6.22, p. 218. *Hidden hypotheses:* none.
*Deviation:* none.

**V6.26 (Proposition 6.23; `Polyfold.proposition_6_23`).** $\mathcal B$ is a basis of the topology of the prebundle, so
the topology it generates is that one. *Book:* Proposition 6.23, p. 218. *Hidden hypotheses:* none. *Deviation:* none.

**V6.27 (Proposition 6.24; `Polyfold.proposition_6_24`).** $\mathrm{DET}(E, F)$ is a topological vector bundle with model
fibre $\mathbb R$, and every $\gamma_{(T,P,\varepsilon)}$, read in its frame, is a trivialization. *Book:* Proposition
6.24, p. 218. *Hidden hypotheses:* none. *Deviation:* none.

**V6.28 (Lemma 6.25; `Polyfold.lemma_6_25`, `Polyfold.lemma_6_25_local`).** The transition between two charts is $(S, t)
\mapsto (S, g(S)t)$ with $g$ continuous and nowhere zero on the common ball. *Book:* Lemma 6.25, p. 218. *Hidden
hypotheses:* none. *Deviation:* none; the proof is the text's, a common lower bound $Q \le P, P'$ (Lemma 6.10, V6.11),
Corollary 6.13 and Lemma 6.21.

**V6.29 (orientations of line bundles; `Polyfold.IsLineOrientation`, `Polyfold.LineOrientation`,
`Polyfold.LineOrientation.eq_of_apply_eq`, `Polyfold.OrCover`, `Polyfold.isCoveringMap_orCover`,
`Polyfold.exists_lineOrientation_apply_eq`, `Polyfold.exists_two_lineOrientation`).** For a topological line bundle,
two orientations that agree on one fibre agree over a preconnected base; over a simply connected, locally path-connected
base every orientation of one fibre extends, and over a nonempty such base there are exactly two orientations; the rays
of the fibres form a two-sheeted covering. *Book:* the reason given in Proposition 6.26 ("since the base space is
contractible", p. 219) and the opening of §6.5, p. 219. *Hidden hypotheses:* none. *Deviation (not in the book):* the
text cites contractibility without the theorem it needs; the proof is the lifting criterion for the orientation double
cover, and nonempty convex sets of normed spaces are simply connected and locally path-connected (Findings, item 25).

**V6.30 (Proposition 6.26; `Polyfold.fredholmIncl`, `Polyfold.DetOn`, `Polyfold.proposition_6_26`).** Over a nonempty
convex set $C$ of Fredholm operators, the restriction $\mathrm{DET}(E, F)|_C$ is a topological line bundle with exactly
two orientations. *Book:* Proposition 6.26, p. 219, for $C = \mathrm{Lin}(f, x)$. *Hidden hypotheses:* none.
*Deviation (stronger):* any nonempty convex $C$; $\mathrm{Lin}(f, x)$ is one (V6.1) (Findings, item 25).

**V6.31 (Definition 6.27; `Polyfold.ChartPoint.isFredholm_of_mem_linSet`, `Polyfold.ChartPoint.detLin`,
`Polyfold.ChartPoint.Or`, `Polyfold.ChartPoint.exists_two_or`, `Polyfold.ChartPoint.orEquivRay`,
`Polyfold.nonempty_equiv_of_two`, `Polyfold.equiv_eq_of_apply_eq_of_two`).** At a chart point, $\mathrm{DET}(f, x)$ is
the pull-back of $\mathrm{DET}(T_zO, K_z)$ to $\mathrm{Lin}(f, x)$ and $\mathrm{Or}^f_x$ is the set of its orientations,
with exactly two elements; for each $L \in \mathrm{Lin}(f, x)$, $o \mapsto o(L)$ is a bijection onto the two orientations
of $\det(L)$. Between two two-element sets there are bijections, and one value determines a bijection. *Book:*
Definition 6.27, pp. 219–220. *Hidden hypotheses:* none. *Deviation (restated):* made in a chart point (V6.53 compares
charts); the category $\mathcal O_f$ is read through its objects, with bijections as morphisms, and $\{o_x, -o_x\}$ as
"exactly two elements" (Findings, item 44).

**V6.32 (Proposition 6.28; `Polyfold.IsScHomotopyRel`, `Polyfold.pt1`, `Polyfold.pt2`,
`Polyfold.exists_contDiff_eq_id_near_Icc_mapsTo`, `Polyfold.exists_isScSmoothMap_eq_one_nhdsSet`,
`Polyfold.exists_nhds_isCompact_zeros`, `Polyfold.exists_isScPlusSection_pullback_of_mapsTo_of_bump`,
`Polyfold.exists_isScPlusSection_pullback_of_family`, `Polyfold.hasScPlusSectionsThrough_pullback_rn_of_bump`,
`Polyfold.proposition_6_28`, `Polyfold.MPolyfold.paracompactSpace_prod`, `Polyfold.paracompactSpace_pullbackSpace`).**
With sc-smooth bump functions, every smooth $x$ has open $U \subseteq W$ in the domain of one chart of the atlas with
(1′) any two sc-smooth paths in $U$ with the same end points are sc-smoothly homotopic in $W$ with the end points fixed;
(2) $\{y \in \mathrm{cl}(U) \mid f(y) = 0\}$ is compact; (3) for every sc-smooth family $\Phi : \mathbb R^n \to X$ with
$\Phi([0, 1]^n) \subseteq W$ there is an sc⁺-section $S$ of $\pi^*P \to \mathbb R^n \times X$ with $(f + S)(q, \Phi(q)) = 0$
for $q$ near $[0, 1]^n$, depending on $q \in [0, 1]^n$ only through $\Phi(q)$; (4) $\pi^*P$ has sc⁺-sections through all
smooth fibre points. *Book:* Proposition 6.28, p. 220, proof pp. 220–221. *Hidden hypotheses:* bump functions, for the
global sections of (3) and (4) (the text assumes partitions of unity from §6.2 on and works in a chart after "assuming
$X = U$"); the paracompactness of $\mathbb R^n \times X$ and of $\pi^*P$, which holds. *Deviation (narrower):* (1′) in
place of (1): the contraction $r(ty)$ of the proof contracts $r(V)$ for a convex $V$, but for $U = r(V')$ it needs
$r(V') \subseteq V'$, which is not stated, and as we read it (1) is not established for $U$ (gap G.61); (3) is stated for
families, as Theorem 6.35 needs it for homotopies; the smoothness of $x$ is not used (Findings, items 45, 46).

**V6.33 (Lemma 6.29; `Polyfold.isZeroAt_paramSection_zero`,
`Polyfold.exists_sections_isGeneralPositionGerm_of_isCompact`, `Polyfold.lemma_6_29`).** Over a tame $X$ with bump
functions, for $f$ with tame germ data, an sc-smooth $\Phi : \mathbb R^n \to X$ and an sc⁺-section $S$ of $\pi^*P$ with
$(f + S)(q, \Phi(q)) = 0$ near $[0, 1]^n$, there are finitely many sc⁺-sections $s_1, \dots, s_k$ of $\pi^*P$ such that
$F(\lambda, (q, y)) = f(y) + S(q, y) + \sum\lambda_is_i(q, y)$ is in general position at $(0, (q, \Phi(q)))$ for all $q$
near $[0, 1]^n$. *Book:* the section $F$, p. 221, Lemma 6.29 and the paragraph after it, p. 222. *Hidden hypotheses:*
$X$ tame, bump functions, tame germ data (the standing hypotheses of §6.5 and of Theorem 5.18). *Deviation (narrower):*
the text gives no proof ("using the results from the transversality theory"); the one formalized is that of Theorem
5.18. The conclusion is the general position of $F$ at the points $(t, \varphi(t), 0)$, which the text derives from (P)
and which Lemmas 6.30, 6.31 use; (P) itself, the general position of each slice $F_t$, is not stated (gap G.63)
(Findings, item 47).

**V6.34 (the kernels of Lemma 6.30; `Polyfold.StrongBundle.IsSurjLinOfIndex.finrank_linKer`,
`Polyfold.exists_local_frame_linKer`, `Polyfold.exists_subspaceFamily_linKer`, `Polyfold.hasFDerivAt_scDeriv_rn`,
`Polyfold.fderiv_mem_linKer`).** For an sc-Fredholm section with tame germ data and a continuous family $y_q$ of zeros in
good position, read in one chart at continuously varying level-$1$ points, the kernels of the linearizations form a
continuous family of subspaces of the model space, of dimension the index; the derivative of an sc-smooth family of
zeros $\mathbb R^n \to X$, read in a chart, lies in the kernel of the linearization. *Book:* Lemma 6.30, p. 222.
*Hidden hypotheses:* none beyond the standing ones. *Deviation (narrower):* the bundle $L$ is a continuous family of
subspaces; that the solution set is a manifold with boundary with corners near $(t, \varphi(t), 0)$, the map $\pi$, and
the smooth structure of $L$ are not formalized (gap G.62) (Findings, item 48).

**V6.35 (continuous families of subspaces and their determinant lines; `Polyfold.SubspaceFamily`,
`Polyfold.SubspaceFamily.det`, `Polyfold.SubspaceFamily.Frame.pretriv`,
`Polyfold.SubspaceFamily.Frame.coordChange_continuousOn`, `Polyfold.SubspaceFamily.comp`,
`Polyfold.LineOrientation.comp`, `Polyfold.SubspaceFamily.transport`, `Polyfold.SubspaceFamily.transport_eq`,
`Polyfold.SubspaceFamily.transport_injective`, `Polyfold.SubspaceFamily.transport_comp`).** A family of $n$-dimensional
subspaces of a normed space, spanned near every point by a continuous frame, has the line bundle $b \mapsto \lambda(L_b)$
with the frames as trivializations; families and orientations restrict along continuous maps, and over $[0, 1]$ an
orientation of $\lambda(L_0)$ is continued to $\lambda(L_1)$, injectively, and over a simply connected, locally
path-connected base the continuation along a path depends only on its end points. *Book:* pp. 222–223 (the bundles $L$,
$\lambda(L)$ and "an orientation of the lines … determines by continuation an orientation of all the other lines"), and
the bundles $\tilde L$ of pp. 224–227. *Hidden hypotheses:* none. *Deviation (restated):* "vector bundle" is read as a
family of subspaces of one model space with continuous local frames.

**V6.36 (continuous families of kernels and their images; `Polyfold.exists_subspaceFamily_ker`,
`Polyfold.SubspaceFamily.exists_map`, `Polyfold.SubspaceFamily.isLineOrientation_map`,
`Polyfold.SubspaceFamily.exists_inf_ker`).** The kernels of a norm-continuous family of surjective Fredholm operators
over a connected base form a continuous family of subspaces; so do the images of a continuous family under a jointly
continuous family of linear maps injective on its members, and orientations are carried along; cutting a continuous
family by the kernel of a fixed $\ell$ onto on every member gives one. *Book:* the continuity statements of pp. 223–226
("as $\tau$ varies, the bundle varies continuously"). *Hidden hypotheses:* none. *Deviation (not in the book):*
"varies continuously" is read in the operator norm, and for maps into a model space as joint continuity.

**V6.37 (the stabilized section in a product chart; `Polyfold.PullbackChartData.ofProd_scDeriv_r_apply`,
`Polyfold.PullbackChartData.ofProd_mem_tangent_iff`, `Polyfold.PullbackChartData.mem_K_ofProd_iff`,
`Polyfold.StrongBundle.scDeriv_ofProd_slice_apply`, `Polyfold.StrongBundle.scDeriv_paramSection_apply`,
`Polyfold.StrongBundleChart.paramDerivAt`, `Polyfold.StrongBundle.scDeriv_paramSection_ofProd_ofProd`,
`Polyfold.sliceProj`, `Polyfold.sliceIncl`, `Polyfold.linKer_inf_ker_sliceProj_eq_map`, `Polyfold.exists_sliceOps`,
`Polyfold.mem_linSet_sectionAdd_pullbackSlice`, `Polyfold.surjective_coprod_of_isLinSurjAt`,
`Polyfold.exists_sliceKernel`).** In the product chart $(\lambda \mapsto \lambda) \times ((q \mapsto q) \times \varphi)$ at
$(0, (q, z))$, the linearization of $F$ is $(\lambda, (\sigma, v)) \mapsto D(\hat g_q \circ r)(z)v + \sum\lambda_i\hat
s_i(q, \cdot)(z) + D_q\sigma$, with $g_q = f + S(q, \cdot)$; its kernel cut by $\sigma = 0$ is the image of $\ker(T \oplus
\varphi)$, with $T = g_q'(x) \in \mathrm{Lin}(f, x)$ and $\varphi(\lambda) = \sum\lambda_i s_i(q, x)$; and $T \oplus \varphi$ is
onto when $F$ is in general position at $(0, (q, \Phi(q)))$. *Book:* $F$, p. 221, $F_t$, $L_t$ and (96), pp.
222–223. *Hidden hypotheses:* none. *Deviation (restated):* $\ker F_t'(\varphi(t), 0)$ is read as the kernel of the
linearization of the whole $F$ cut by $\sigma = 0$ (Findings, item 49).

**V6.38 (Lemma 6.31; `Polyfold.lemma_6_31`).** With the operators of V6.37, the sequence (96) $0 \to \ker T \to \ker(T
\oplus \varphi) \to \mathbb R^k \to K_z/R(T) \to 0$ is the stabilization sequence of $T$ and $\varphi$ (V6.16), hence exact.
*Book:* (96) and Lemma 6.31, p. 223. *Hidden hypotheses:* none. *Deviation (restated):* the text has $c$ onto by (P);
here it is onto by the general position of $F$ (V6.33) and the derivative of the family of zeros, which absorbs the
$\mathbb R^n$-directions (`Polyfold.fderiv_mem_linKer`) (Findings, item 49).

**V6.39 (continuation and the isomorphisms $\Phi_{E_t}$; `Polyfold.SubspaceFamily.cont`, `Polyfold.SubspaceFamily.cont_eq`,
`Polyfold.SubspaceFamily.cont_self`, `Polyfold.SubspaceFamily.cont_trans`, `Polyfold.SubspaceFamily.contEquiv`,
`Polyfold.SubspaceFamily.cont_comp`, `Polyfold.SubspaceFamily.cont_eq_transport`, `Polyfold.detEquivOfSurjective`,
`Polyfold.stabRayEquiv`, `Polyfold.propagate`, `Polyfold.propagate_self`, `Polyfold.propagate_trans`,
`Polyfold.propagate_comp`).** Over a simply connected, locally path-connected base the continuation of a ray of
$\lambda(L_{q_0})$ to $\lambda(L_{q_1})$ is a bijection, compatible with composition and pull-back, and along $[0, 1]$ it is
the continuation of V6.35. For a stabilization $T \oplus \varphi$ onto and an identification of its kernel with $L$, the
rays of $\det(T)$ and of $\lambda(L)$ correspond ($\iota_\varphi$ of V6.18 and $\det(T \oplus \varphi) \cong \lambda(\ker(T
\oplus \varphi))$); $\Phi_{E_0}$, continuation and $\Phi_{E_1}^{-1}$ compose to a bijection of the rays of $\det(T_0)$ and
$\det(T_1)$. *Book:* pp. 223–224, after Lemma 6.31. *Hidden hypotheses:* none. *Deviation (restated):* over any simply
connected, locally path-connected base, so that one statement serves the paths and the squares; the fixed
identification $\lambda^*(\mathbb R^k) \cong \lambda^*(\{0\})$ of (94) occurs at both ends.

**V6.40 (the stabilization sign; `Polyfold.coord_stabIota`, `Polyfold.stabD`, `Polyfold.continuousOn_stabD`,
`Polyfold.stabD_ne_zero`, `Polyfold.stabSign`, `Polyfold.isLineOrientation_stabRay`,
`Polyfold.not_isLineOrientation_stabRay_uncorrected`).** In a local determinant chart with the projection $P$, the chart
coordinate of $\iota_\psi(x) \in \det(S \oplus \psi)$ is $(-1)^{k\dim F/R(P) + \dim\operatorname{coker} S}D(S, \psi)$ times
that of $x$, with $D$ continuous and nowhere zero near the centre. For a continuous orientation $o$ of $\mathrm{DET}$, a
norm-continuous family $T_q$ and a continuous stabilization $\varphi_q$ with $T_q \oplus \varphi_q$ onto, the rays
$(-1)^{\dim\operatorname{coker}T_q}\,\Phi(o(T_q))$ of $\lambda(\ker(T_q \oplus \varphi_q))$ form an orientation; without the
sign they need not ($E = F = \mathbb R$, $k = 1$, $T_q = q/(1 + |q|)$, $\varphi(r) = r_0$). *Book:* formula
(94), p. 212, as it is used in the continuity statements of pp. 223–226. *Hidden hypotheses:* none. *Deviation
(restated):* as we read it, the orientations carried by $\Phi_E$ of (94) along a continuous family are not continuous
where $\dim\operatorname{coker}T$ changes parity; the propagation uses the sign-normalized $(-1)^{\dim\operatorname{coker}
T}\Phi_E$, which on each operator carries the text's orientation or its opposite (Findings, item 50).

**V6.41 (the push-forward along stabilized kernels; `Polyfold.chartPt`, `Polyfold.ChartPoint.stabT`,
`Polyfold.ChartPoint.stabT_mem_linSet`, `Polyfold.ChartPoint.stabPhi`, `Polyfold.ChartPoint.stabPhi_finAppend`,
`Polyfold.stabSign_inv`, `Polyfold.toPerm_stabSign_symm`, `Polyfold.isFredholm_stabCoprod`, `Polyfold.IsStabKernels`,
`Polyfold.IsStabKernels.comp`, `Polyfold.IsStabKernels.push`, `Polyfold.IsStabKernels.push_congr`,
`Polyfold.IsStabKernels.orRay`, `Polyfold.IsStabKernels.push_eq_orRay`, `Polyfold.IsStabKernels.cont_orRay_path`,
`Polyfold.IsStabKernels.push_comp`, `Polyfold.IsStabKernels.push_trans`).** At a chart point, $T = (f + S)'(x) \in
\mathrm{Lin}(f, x)$ and $\varphi(\lambda) = \sum\lambda_i\hat s_i(x)$. A family of *stabilized kernels* is a continuous
family $\Lambda$, over a parameter space, of the subspaces $\ker(T_q \oplus \varphi_q)$ of $E_0 \times \mathbb R^k$ at points
$y(q)$, read in one chart; its push-forward $\varphi_* : \mathrm{Or}^f_{x_0} \to \mathrm{Or}^f_{x_1}$ between the end points
is $o \mapsto o(T_a) \mapsto (-1)^{\dim\operatorname{coker}T_a}\Phi_{E_a}(o(T_a))$, continued to $\lambda(\Lambda_b)$, and
carried back in the same way at $T_b$. It depends only on the data, is compatible with pull-back and with
concatenation, and along a path with continuously varying data continuation carries the rays read at one parameter to
those read at the next. *Book:* the push-forward $o_1 = \varphi_*o_0$, p. 224. *Hidden hypotheses:* none. *Deviation
(restated):* the sign of V6.40 at both end points; for given end-point operators the result differs from the text's by
$(-1)^{\dim\operatorname{coker}T_a + \dim\operatorname{coker}T_b}$; the sections enter pointwise, and the continuity in the
parameter is that of $\Lambda$ (Findings, item 50).

**V6.42 (Lemma 6.30 for the push-forward: the stabilized kernels exist; `Polyfold.exists_continuousOn_lift_chart`,
`Polyfold.exists_isStabKernels`).** For an sc-smooth $\Phi : \mathbb R^n \to X$ with $\Phi([0, 1]^n)$ in the domain of a
chart, an sc⁺-section $S$ with $f + S = 0$ along $\Phi$ near $[0, 1]^n$ and sc⁺-sections $s_1, \dots, s_k$ as in V6.33, the
stabilized kernels of the slices form a continuous family over $[0, 1]^n$. *Book:* Lemma 6.30, p. 222, and the bundle
$L$ after it. *Hidden hypotheses:* none beyond the standing ones. *Deviation (narrower):* as V6.34 (gap G.62); the
family is the tangent spaces of the solution set (V6.34) cut by $\{dt = 0\}$ (V6.36) and identified with $\ker(T_q \oplus
\varphi_q)$ (V6.37).

**V6.43 (push-forward data along paths; `Polyfold.pt1_mem_Icc`, `Polyfold.exists_lift_of_smooth`, `Polyfold.chartPtOf`,
`Polyfold.isZeroAt_sectionAdd_reparamSection`, `Polyfold.IsStabKernels.push_eq_of_eq`, `Polyfold.IsPush`,
`Polyfold.isPush_reparam`, `Polyfold.IsPush.split`, `Polyfold.exists_isPush`).** $e$ is a push-forward along an sc-smooth
path $\gamma$ in a chart if there are global sc⁺-sections $S, s_1, \dots, s_k$ of $\pi^*P \to \mathbb R \times X$ with $(f +
S)(t, \gamma(t)) = 0$ near $[0, 1]$ and a family of stabilized kernels of their slices along $\gamma$ whose push-forward is
$e$. A push-forward along $\gamma$ is the composite of push-forwards along its two halves, and along every sc-smooth path
in a set with property (3) of Proposition 6.28 there is one. *Book:* p. 224 (the choices of $s(\cdot, t)$ and $s_1, \dots,
s_k$ along the path). *Hidden hypotheses:* none. *Deviation (restated):* global sections of the pull-back in place of
sections over $U \times [0, 1]$; property (P) is used only to construct a push-forward.

**V6.44 (Proposition 6.32; `Polyfold.IsStabKernels.congr_data`, `Polyfold.IsStabKernels.push_congr_data`,
`Polyfold.IsStabKernels.push_eq_of_prefix`, `Polyfold.isZeroAt_sectionAdd_combo`, `Polyfold.linAt_principal_combo`,
`Polyfold.continuous_principal_pullbackSlice`, `Polyfold.proposition_6_32`).** Two push-forwards along the same sc-smooth
path in the domain of a chart agree. *Book:* Proposition 6.32, p. 224, proof pp. 224–226. *Hidden hypotheses:* the
standing ones of §6.5 ($X$ tame, bump functions, tame germ data). *Deviation (restated):* "does not depend on the
choices" is read as the agreement of any two data; the homotopy of Lemma 6.34 and the added sections of Lemma 6.33 are
combined over one square, $S^\tau = (1 - \tau)S^0 + \tau S^1$ with the two families of sections interpolated and the
sections of Lemma 6.29 on the square appended, so that Lemma 6.33 applies on both edges without reordering (Findings,
item 52).

**V6.45 (Lemma 6.33; `Polyfold.wedgeExt`, `Polyfold.wedgeExt_wedge`, `Polyfold.wedgeExt_congr`,
`Polyfold.wedgeExt_bijective`, `Polyfold.appendStab`, `Polyfold.kerAppend`, `Polyfold.detEquiv_stabIota_append`,
`Polyfold.SubspaceFamily.exists_continuous_lifts`, `Polyfold.isLineOrientation_wedgeExt`, `Polyfold.kerEquivMap`,
`Polyfold.stabRayEquiv_append`, `Polyfold.propagate_append`, `Polyfold.IsStabKernels.push_append`).** Appending
sc⁺-sections $\bar s_1, \dots, \bar s_d$ after $s_1, \dots, s_k$ does not change the push-forward: the stabilization
isomorphism of $(\varphi, \psi)$ is that of $\varphi$ followed by $w \mapsto (w, 0) \wedge \ell_1 \wedge \dots \wedge \ell_d$, for
any $\ell_j \in \ker(T \oplus (\varphi, \psi))$ with $\psi$-coordinates the standard basis, and this map carries continuous
orientations along the family. *Book:* Lemma 6.33, p. 224, proof p. 225 ("one verifies by a simple computation").
*Hidden hypotheses:* none. *Deviation (restated):* the homotopy $\tilde F(\tau, \cdot)$ of the text's proof is not needed;
with the appended sections last the two isomorphisms agree exactly, with no sign (Findings, item 51).

**V6.46 (sections over parameter families; `Polyfold.reparamSection`, `Polyfold.pullbackSlice_reparamSection`,
`Polyfold.rnProdMapOp`, `Polyfold.StrongBundle.isScPlusSection_of_local`, `Polyfold.StrongBundle.IsScPlusSection.reparam`,
`Polyfold.StrongBundle.isGeneralPositionGerm_paramSection_of_comp`).** For $g$ affine, $(q, y) \mapsto S(g(q), y)$ is
again an sc⁺-section of the pull-back; sc⁺-sections may be checked in one chart around each point; adding sections keeps
the general position of $F$ at $(0, y)$. *Book:* pp. 224–226 (the sections $s(y, \tau, t)$ over a square, and "adding more
sc⁺-sections", Lemma 6.33, p. 224; the remark that after "adding more sections" the properties still hold is in the proof of
Theorem 5.18, p. 178). *Hidden hypotheses:* none. *Deviation:* none.

**V6.47 (Lemma 6.34; `Polyfold.IsStabKernels.push_square`, `Polyfold.sqEdge`, `Polyfold.sqPath`).** For a family of
stabilized kernels over the square $[0, 1]^2$ with the end points $x_0$, $x_1$ fixed and the end-point operators varying
continuously, the push-forwards along the edges $\tau = 0$ and $\tau = 1$ agree. *Book:* Lemma 6.34, p. 226. *Hidden
hypotheses:* none. *Deviation (restated):* the convex homotopy $s^\tau$ of the lemma is part of the square of V6.44; the
continuity of the end-point orientations along $\tau$ is that of V6.40, with the sign.

**V6.48 (Theorem 6.35; `Polyfold.push_eq_of_homotopy`, `Polyfold.HasLocalPropagation`, `Polyfold.theorem_6_35`).** Over
a tame $X$ with bump functions, for $f$ with tame germ data, every smooth point $x$ has an open $U \ni x$ and a chart $c$
such that push-forwards exist along the sc-smooth paths in $U$ and depend only on their end points. *Book:* the homotopy
argument, pp. 226–227, and Theorem 6.35, p. 227. *Hidden hypotheses:* the section $f$, which the statement does not
introduce (an sc-Fredholm section, with tame germ data); bump functions. *Deviation (narrower):* $U$ is not shown to be
sc-smoothly contractible (gap G.61); what the proof uses is (1′) of V6.32. Since the homotopy of (1′) meets its edge
conditions only on $[0, 1]$ while a push-forward datum needs $f + S = 0$ near $[0, 1]$, the proof passes through the
reparametrized paths $\gamma_i \circ \kappa$, with three homotopies whose edges are exact (Findings, item 53).

**V6.49 (sc-smooth paths in a chart and their concatenation; `Polyfold.MPolyfold.isScSmoothMap_of_eventuallyEq`,
`Polyfold.pt1_apply`, `Polyfold.contDiff_pt1_comp`, `Polyfold.exists_nhds_scPath`, `Polyfold.concatPath`,
`Polyfold.concatPath_of_le`, `Polyfold.concatPath_of_gt`, `Polyfold.isScSmoothMap_concatPath`, `Polyfold.concatPath_zero`,
`Polyfold.concatPath_one`, `Polyfold.concatPath_half₁`, `Polyfold.concatPath_half₂`, `Polyfold.isScSmoothMap_reparam`,
`Polyfold.HasLocalPropagation.eq_trans`).** For an open $U$ in the domain of a chart and $x \in U$ there is an open $V \ni
x$ in $U$ whose smooth points are pairwise joined by sc-smooth paths in $U$. The concatenation, $\gamma_1(\kappa(3s))$ for
$s \le 1/2$ and $\gamma_2(\kappa(3s - 2))$ for $s > 1/2$ with $\kappa$ the smooth transition function, is sc-smooth, with
the right end points and halves; reparametrizing by a $C^\infty$ map keeps sc-smoothness; push-forwards compose along
concatenations. *Book:* the paths after Theorem 6.35, p. 227, and the concatenation, p. 228. *Hidden hypotheses:* none.
*Deviation (narrower):* paths are joined only locally, inside a chart; the global facts recalled on p. 201 (local path
connectedness, sc⁺-smooth paths within a path component) are not formalized (gap G.56).

**V6.50 (Definition 6.36; `Polyfold.IsContinuousOrientation`, `Polyfold.exists_two_isContinuousOrientation`,
`Polyfold.exists_orientableNbhd`, `Polyfold.IsOrientableNbhd`, `Polyfold.exists_isOrientableNbhd`).** An orientable
neighbourhood of $(f, x)$ is a pair $V \subseteq U$: $U$ open with the local propagation property in a chart, $V \ni x$ open
with any two smooth points joined by an sc-smooth path in $U$; a continuous orientation is a choice $y \mapsto o_y$ on
$V_\infty$ carried into itself by the push-forwards along paths in $U$; there are exactly two, and every smooth point has
an orientable neighbourhood. *Book:* the paragraph after Theorem 6.35 and Definition 6.36, p. 227. *Hidden
hypotheses:* the standing ones of §6.5. *Deviation (restated):* the pair $V \subseteq U$ in place of an open contractible
$U$, since Proposition 6.28 gives (1′) (gap G.61) (Findings, item 54).

**V6.51 (reparametrization homotopies; `Polyfold.mem_smoothSet_of_isScSmoothMap`, `Polyfold.contDiff_pt2_comp`,
`Polyfold.isScHomotopyRel_reparam`, `Polyfold.reparam_mem`, `Polyfold.leftHalf`, `Polyfold.rightHalf`,
`Polyfold.halvesReparam`, `Polyfold.concatPath_halves`).** For a $C^\infty$ $\theta$ with $\theta(0) = 0$, $\theta(1) = 1$,
$\gamma \circ \theta$ is sc-smoothly homotopic to $\gamma$ with the end points fixed, inside every set containing $\gamma([0,
1])$ when $\theta([0, 1]) \subseteq [0, 1]$; the concatenation of the two halves of $\gamma$ is such a reparametrization.
*Book:* the homotopy classes $[\varphi]$, p. 227, and their composition, p. 228. *Hidden hypotheses:* none.
*Deviation:* none; these are tools for V6.52 and V6.56.

**V6.52 (the path category $PX$; `Polyfold.smoothTransition_half`, `Polyfold.isScSmoothMap_const_of_mem_smoothSet`,
`Polyfold.isScSmoothMap_ite`, `Polyfold.isScSmoothMap_ite₃`, `Polyfold.concatPath_of_le_two_thirds`,
`Polyfold.concatPath_of_one_third_le`, `Polyfold.ScHomotopic`, `Polyfold.ScHomotopic.refl`, `Polyfold.ScHomotopic.symm`,
`Polyfold.ScHomotopic.trans`, `Polyfold.isScHomotopyRel_triHomotopy`, `Polyfold.assocReparam`, `Polyfold.ScPath`,
`Polyfold.ScPath.source_mem_smoothSet`, `Polyfold.ScPath.target_mem_smoothSet`, `Polyfold.ScPath.const`,
`Polyfold.ScPath.concat`, `Polyfold.ScPath.reverse`, `Polyfold.ScPath.concat_congr`, `Polyfold.ScPath.const_concat`,
`Polyfold.ScPath.concat_const`, `Polyfold.ScPath.concat_assoc`, `Polyfold.ScPath.concat_reverse`,
`Polyfold.ScPath.reverse_concat`, `Polyfold.ScPathClass`, `Polyfold.ScPathClass.comp`, `Polyfold.PathCat`,
`Polyfold.PathCat.category`, `Polyfold.PathCat.groupoid`, `Polyfold.PathCat.homMk`, `Polyfold.PathCat.comp_mk`,
`Polyfold.PathCat.id_eq_mk`, `Polyfold.PathCat.mk_eq_mk_iff`, `Polyfold.PathCat.exists_eq_mk`,
`Polyfold.PathCat.inv_mk`).** Sc-smooth homotopy with the end points fixed is an equivalence relation on the sc-smooth
paths between two points; concatenation is well defined on classes, associative, with the classes of the constant paths
as units and the reversed paths as inverses; the smooth points with these classes form a category, indeed a groupoid.
*Book:* the classes $[\varphi]$, their composition and the category $PX$, pp. 227–228. *Hidden hypotheses:* none.
*Deviation (restated):* the edge conditions of a homotopy hold only on $[0, 1]$, so transitivity is proved after
reparametrizing by $\kappa$; the identities, which the text does not name, are the classes of the constant paths; the
composition's second piece $\psi(\beta(s))$ is read as $\psi(\beta(s) - 1)$ (possible misprint); Mathlib's $[\varphi] \gg
[\psi]$ is the text's $[\psi] * [\varphi]$ (Findings, items 55, 71).

**V6.53 (transferring orientations between chart points; `Polyfold.conjKerEquiv`, `Polyfold.conjCokerEquiv`,
`Polyfold.conjDet`, `Polyfold.conjDet_wedge_tmul`, `Polyfold.conjDet_trans`, `Polyfold.conjDet_congr`,
`Polyfold.conjDet_refl`, `Polyfold.IsGoodLeftProj.conj`, `Polyfold.gammaProj_conjDet`, `Polyfold.coord_conjDet_coordInv`,
`Polyfold.isLineOrientation_conj`, `Polyfold.LineOrientation.conj`, `Polyfold.LineOrientation.conj_apply`,
`Polyfold.LineOrientation.conj_refl`, `Polyfold.LineOrientation.conj_trans`, `Polyfold.LineOrientation.conj_congr`,
`Polyfold.ChartPoint.baseDeriv`, `Polyfold.ChartPoint.baseDeriv_self`, `Polyfold.ChartPoint.baseDeriv_trans`,
`Polyfold.ChartPoint.isScOperator_baseDeriv`, `Polyfold.ChartPoint.fiberMap`, `Polyfold.ChartPoint.fiberMap_self`,
`Polyfold.ChartPoint.fiberMap_trans`, `Polyfold.ChartPoint.isScOperator_fiberMap`, `Polyfold.ChartPoint.transferT`,
`Polyfold.ChartPoint.transferK`, `Polyfold.ChartPoint.transferT_self_apply`, `Polyfold.ChartPoint.transferT_trans_apply`,
`Polyfold.ChartPoint.scDeriv_principal_baseDeriv`, `Polyfold.ChartPoint.IsScPlusOp.conj`,
`Polyfold.ChartPoint.mem_linSet_transfer_iff`, `Polyfold.ChartPoint.orTransfer`, `Polyfold.ChartPoint.orTransfer_apply`,
`Polyfold.ChartPoint.orTransfer_self`, `Polyfold.ChartPoint.orTransfer_trans`).** For isomorphisms $A$, $\Gamma$ with $S'A =
\Gamma S$, $\det(S) \cong \det(S')$ by $A$ on kernels and $\Gamma$ on cokernels, compatible with composition and with the
$\gamma^P$, and continuous orientations of $\mathrm{DET}$ are carried along. For two chart points at $x$, $A$ is the
derivative at $z$ of the base transition and $\Gamma$ the fibre part of the strong bundle transition, with the cocycle
rules; $L \in \mathrm{Lin}_p(f, x)$ iff $\Gamma L A^{-1} \in \mathrm{Lin}_{p'}(f, x)$, and the induced bijection
$\mathrm{Or}^f_x(p) \cong \mathrm{Or}^f_x(p')$ satisfies the cocycle rules. *Book:* p. 219 ($T_xX$, $Y_x$ and
$\mathrm{Lin}(f, x)$ as intrinsic objects) and the proof of Theorem 6.37, p. 228. *Hidden hypotheses:* none.
*Deviation (not in the book):* the text treats these objects as chart-free; the identification between charts is made
explicit (Findings, item 70).

**V6.54 (the push-forward does not depend on the chart; `Polyfold.stabSign_conj`, `Polyfold.coprod_conj`,
`Polyfold.ker_coprod_conj`, `Polyfold.surjective_coprod_conj`, `Polyfold.conj_stab_key`, `Polyfold.stabRayEquiv_conjDet`,
`Polyfold.SubspaceFamily.cont_map`, `Polyfold.ChartPoint.fiberMap_principal`, `Polyfold.ChartPoint.conj_of_linAt`,
`Polyfold.ChartPoint.conj_of_principal`, `Polyfold.continuous_baseDeriv`, `Polyfold.IsStabKernels.exists_transfer`,
`Polyfold.IsStabKernels.orRay_transfer`, `Polyfold.IsPush.transfer`, `Polyfold.HasLocalPropagation.push_compat`).** The
stabilization isomorphism and the sign are natural under conjugation, and continuation is natural under jointly
continuous families of injective linear maps. A family of stabilized kernels in one chart is carried by the derivative of
the base transition to one in a second chart, with the same sections; a push-forward in one chart, conjugated by the
transfer of V6.53 at the end points, is a push-forward in the other; so the local propagations of two charts agree.
*Book:* pp. 222–228 (the push-forward, and the orientable neighbourhoods of the proof of Theorem 6.37). *Hidden
hypotheses:* none. *Deviation (not in the book):* the text does not compare charts (Findings, item 70).

**V6.55 ($\mathrm{Or}^f_x$ in a chosen chart; `Polyfold.orChart`, `Polyfold.isChart_orChart`, `Polyfold.mem_orChart`,
`Polyfold.Orx`, `Polyfold.toChartOr`, `Polyfold.toChartOr_orChart`, `Polyfold.toChartOr_trans`, `Polyfold.exists_two_orx`,
`Polyfold.restrictOr`).** $\mathrm{Or}^f_x$ is the set of orientations read in a chosen chart of the atlas at $x$; it has
two elements, and it is identified with the orientations read in any other chart at $x$ by the transfer of V6.53,
compatibly with composition. *Book:* Definition 6.27 and the objects of Theorem 6.37, pp. 220, 228. *Hidden
hypotheses:* none. *Deviation (restated):* a chosen chart stands for the text's chart-free $\mathrm{Or}^f_x$ (Findings,
item 70).

**V6.56 (transport along paths from local push-forwards; `Polyfold.LocalTransport`,
`Polyfold.LocalTransport.push_eq_refl`, `Polyfold.LocalTransport.push_eq_push`, `Polyfold.LocalTransport.push_congr`,
`Polyfold.LocalTransport.transportN`, `Polyfold.LocalTransport.transportN_eq_push`, `Polyfold.LocalTransport.IsFine`,
`Polyfold.LocalTransport.transportN_eq_of_isFine`, `Polyfold.LocalTransport.IsLebesgueNumber`,
`Polyfold.LocalTransport.exists_isLebesgueNumber`, `Polyfold.LocalTransport.isFine_of_isLebesgueNumber`,
`Polyfold.LocalTransport.transport`, `Polyfold.LocalTransport.transport_eq_push`, `Polyfold.LocalTransport.transport_congr`,
`Polyfold.LocalTransport.transport_const`, `Polyfold.LocalTransport.transport_halves`,
`Polyfold.LocalTransport.transportN_square`, `Polyfold.LocalTransport.exists_isSqLebesgueNumber`,
`Polyfold.LocalTransport.transport_eq_of_isScHomotopyRel`, `Polyfold.LocalTransport.transport_reparam`,
`Polyfold.LocalTransport.transport_concatPath`, `Polyfold.LocalTransport.transport_unique`,
`Polyfold.equiv_paste_squares`, `Polyfold.vSeg`, `Polyfold.hSeg`, `Polyfold.dSeg`).** From local data (good open sets
covering $X_\infty$ and push-forwards along paths in a good set, compatible with concatenation and independent of the good
set) the transport along an sc-smooth path is the composite of the push-forwards along its $2^N$ dyadic pieces, for any
$N$ at which every piece lies in a good set (such $N$ exist by the Lebesgue number lemma). It is the push-forward on a
path in a good set, homotopy invariant, compatible with concatenation and reparametrization, the identity on constant
paths, and the only family with these properties. *Book:* the proof of Theorem 6.37, p. 228 ("using the compactness
of $[0, 1]$ and a finite covering", "by a covering argument", "it is obvious that $\Gamma_f$ is unique"). *Hidden
hypotheses:* none. *Deviation (restated):* dyadic subdivisions of $[0, 1]$ and of $[0, 1]^2$ in place of arbitrary finite
coverings (Findings, item 72).

**V6.57 (Theorem 6.37; `Polyfold.IsPropagationNbhd`, `Polyfold.orPush`, `Polyfold.orPush_eq`, `Polyfold.orPush_compat`,
`Polyfold.orPush_trans`, `Polyfold.IsStarPropertyOn`, `Polyfold.IsStarProperty`, `Polyfold.orLocalTransport`,
`Polyfold.orLocalTransport_transport_eq`, `Polyfold.LocalTransport.restrict`,
`Polyfold.LocalTransport.transport_apply_eq_of_local`, `Polyfold.orFunctorMap`, `Polyfold.orFunctorMap_mk`,
`Polyfold.orFunctorMap_id`, `Polyfold.orFunctorMap_comp`, `Polyfold.orFunctor`, `Polyfold.orFunctorMap_isStarProperty`,
`Polyfold.orFunctorMap_unique_of_cover`, `Polyfold.orFunctorMap_unique`, `Polyfold.theorem_6_37`).** Over a tame $X$ with
bump functions, for $f$ with tame germ data and $P$ with sc⁺-sections through the smooth fibre points, there is exactly
one family of bijections $\Gamma_f([\varphi]) : \mathrm{Or}^f_x \to \mathrm{Or}^f_y$ on the morphisms of $PX$ that takes
identities to identities, compositions to composites, and has property (∗): for every chart $c$, every open $U$ with the
local propagation property in $c$ and every sc-smooth path $\varphi$ in $U$, $\Gamma_f([\varphi])$ is every push-forward
along $\varphi$ in $c$, read through $\mathrm{Or}^f$ of the chosen charts. It is a functor $PX \to$ Type, $x \mapsto
\mathrm{Or}^f_x$, and the uniqueness needs (∗) only on a family of such open sets covering $X_\infty$. *Book:* Theorem
6.37 and its proof, p. 228. *Hidden hypotheses:* the standing ones of §6.5, and sc⁺-sections through every smooth fibre
point, so that every $\mathrm{Or}^f_x$ has two elements (implied by bump functions). *Deviation (restated):* (∗) is asked
for every open set with the local propagation property, not only for sc-smoothly contractible ones (gap G.61); $\mathcal
O_f$ is read as types and bijections; "uniquely determined" is read for the maps on morphisms (Findings, item 72).

**V6.58 (Definition 6.38; `Polyfold.scPathSetoid`, `Polyfold.IsOrientableSection`,
`Polyfold.isOrientableSection_iff_exists`).** $f$ is orientable if $\Gamma_f([\varphi]) = \Gamma_f([\psi])$ for any two
morphisms $x \to y$ of $PX$; equivalently there is $y \mapsto o_y$ with $\Gamma_f([\varphi])o_x = o_y$ for every $[\varphi] :
x \to y$. *Book:* Definition 6.38, p. 229. *Hidden hypotheses:* none. *Deviation (restated):* "smooth points in the same
path component" is read as smooth points joined by an sc-smooth path (Findings, item 73).

**V6.59 (Definition 6.39 and its equivalence with Definition 6.38; `Polyfold.IsOrientableSection'`,
`Polyfold.isOrientableSection'_iff_exists`, `Polyfold.isOrientableSection_iff`).** $f$ is orientable in the sense of
Definition 6.39 if there is $y \mapsto o_y$ on $X_\infty$ such that every smooth point has an orientable neighbourhood over
which it is a continuous orientation; this holds iff there is $y \mapsto o_y$ with $\Gamma_f([\varphi])o_x = o_y$ for all
$[\varphi]$, so Definitions 6.38 and 6.39 are equivalent. *Book:* Definition 6.39, p. 229 ("an equivalent version").
*Hidden hypotheses:* none. *Deviation (stronger):* the equivalence, stated without proof, is proved; the definition's
"$y \in U_\infty$", before any $U$ is introduced, is read as $y \in X_\infty$ (possible misprint) (Findings, items 73, 74).

**V6.60 (Definition 6.40; `Polyfold.IsSectionOrientation`, `Polyfold.isSectionOrientation_iff`,
`Polyfold.exists_isSectionOrientation_iff`, `Polyfold.IsSectionOrientation.apply_eq_iff`,
`Polyfold.IsSectionOrientation.exists_two`).** An orientation of $f$ is a map $y \mapsto o_y$ on $X_\infty$ whose restriction
to every orientable neighbourhood of every smooth point is a continuous orientation; equivalently $\Gamma_f([\varphi])o_x =
o_y$ for all $[\varphi] : x \to y$. $f$ has an orientation iff it is orientable; two orientations that agree at a point
agree on the smooth points joined to it by sc-smooth paths, and there are exactly two on each such class. *Book:*
Definition 6.40, p. 229. *Hidden hypotheses:* none. *Deviation (restated):* an orientable neighbourhood is the pair of
V6.50 (Findings, item 75).

**V6.61 (Theorem 6.41, the natural orientation of the solution set; `Polyfold.theorem_6_41_solutionSet`,
`Polyfold.MPolyfold.IsGeneralPositionAt.isGoodPositionAt`, `Polyfold.tangentSpace_solutionSet_eq_linKer`,
`Polyfold.ChartPoint.linZero`, `Polyfold.ChartPoint.linZero_mem_linSet`, `Polyfold.ChartPoint.linZero_surjective`,
`Polyfold.ChartPoint.map_ker_linZero`, `Polyfold.ChartPoint.tangentOr`, `Polyfold.tangentOrAt`,
`Polyfold.stabSign_of_surjective`, `Polyfold.stabRayEquiv_zero`, `Polyfold.ChartPoint.stabRayEquiv_eq_tangentOr`,
`Polyfold.IsStabKernels.orRay_eq_tangentOr`, `Polyfold.isStabKernels_zero`, `Polyfold.SubspaceFamily.congrL`,
`Polyfold.exists_tangentFamily`, `Polyfold.tangentFamily`, `Polyfold.tangentFamily_L`, `Polyfold.cont_tangentOr`,
`Polyfold.isLineOrientation_tangentOr`, `Polyfold.isLineOrientation_tangentOr_of_isSectionOrientation`,
`Polyfold.theorem_6_41`).** Over a tame $X$, for a proper sc-Fredholm section $f$ with tame germ data in general position
(Definition 5.17) at every zero, the solution set $S$ is compact, a smooth submanifold in general position with the
induced structure of a tame manifold with boundary with corners (the conclusions of Theorem 5.18), and $T_xS = \ker
f'(x)$, read in a chart. At a zero, $f'(x)$ lies in $\mathrm{Lin}(f, x)$ and is onto, so an element $o_x$ of
$\mathrm{Or}^f_x$ gives a ray of $\det f'(x) \cong \lambda(\ker f'(x)) = \lambda(T_xS)$, the *tangent orientation*. For an
orientation $o$ of $f$ (Definition 6.40) and every sc-smooth path $\gamma$ of zeros in an orientable neighbourhood $V
\subseteq U$, the kernels $\ker f'(\gamma_q)$ form a continuous family of subspaces, and the tangent orientations of $o$
form an orientation of its line bundle. The Fredholm side is the push-forward for the datum $S = 0$, $k = 0$, which along
a path of zeros is the continuation between tangent orientations. *Book:* Theorem 6.41 and its proof, p. 229; the
paragraph after it on $S_{f+s}$, pp. 229–230. *Hidden hypotheses:* tame germ data (the standing hypothesis of Chapter
5); the orientation $o$ exists iff $f$ is orientable (V6.60). "Proper" is the text's hypothesis
(`StrongBundle.IsProper`); the proof uses only the compactness of $S$, which for sc-Fredholm sections is equivalent to it
(V5.10). *Deviation (narrower):* "a natural orientation" is
read as the tangent orientations with their continuity along the sc-smooth paths of zeros in a chart, and "the local
prolongation of the orientation on $S$ is the Fredholm one" as the identity of continuation and push-forward along such
paths. Not formalized: an orientation of $S$ as an abstract manifold (gap G.67), the compatibility of the tangent
orientations read in two charts at one point (gap G.68), and the perturbation paragraph after the theorem, with $S_{f+s}$
and $\mathrm{Lin}(f + s, x) = \mathrm{Lin}(f, x)$ (gap G.69) (Findings, items 90–93).

**V6.62 (Remark 6.42, at a point; `Polyfold.extOp`, `Polyfold.isFredholm_extOp`, `Polyfold.finrank_ker_extOp`,
`Polyfold.extE`, `Polyfold.range_extOp`, `Polyfold.extCoker`, `Polyfold.extDet`, `Polyfold.extDet_wedge_tmul`,
`Polyfold.extDetN`, `Polyfold.extDetN_eq_of_surjective`, `Polyfold.coord_extDet`, `Polyfold.coord_extDetN`,
`Polyfold.isLineOrientation_extPull`, `Polyfold.LineOrientation.extPull`, `Polyfold.extConjOp`, `Polyfold.extConjDet`,
`Polyfold.existsUnique_extConjOr`, `Polyfold.ChartPoint.prodPt`, `Polyfold.ChartPoint.mem_prodPt_T_iff`,
`Polyfold.ChartPoint.mem_prodPt_K_iff`, `Polyfold.ChartPoint.prodT`, `Polyfold.ChartPoint.prodK`,
`Polyfold.ChartPoint.prodLin`, `Polyfold.ChartPoint.IsScPlusOp.prodPt`, `Polyfold.constLift`,
`Polyfold.ChartPoint.prodLin_mem_linSet`, `Polyfold.ChartPoint.existsUnique_prodOr`, `Polyfold.ChartPoint.prodOr`,
`Polyfold.ChartPoint.prodOr_apply`, `Polyfold.ChartPoint.prodOr_injective`).** For Fredholm $L$, $\tilde L = L \oplus 0 :
E \times \mathbb R \to F$ is Fredholm with $\ker\tilde L = \ker L \times \mathbb R$ and $\operatorname{coker}\tilde L =
\operatorname{coker} L$, and $h \mapsto \tilde h$, $(a_1 \wedge \dots \wedge a_n) \otimes d^* \mapsto ((a_1, 0) \wedge \dots
\wedge (a_n, 0) \wedge e) \otimes d^*$ with $e = (0, 1)$, is an isomorphism $\det(L) \cong \det(\tilde L)$; in local
determinant charts its coordinate is $(-1)^{\dim F/R(P) + \dim\operatorname{coker}L}$ times a continuous nowhere-zero
function, and $(-1)^{\dim\operatorname{coker}L}\,h \mapsto \tilde h$ pulls continuous orientations back along $L \mapsto
\tilde L$. In charts: for an sc-Fredholm $f$, an sc⁺-section $S$ of $\pi^*P \to \mathbb R \times X$, $\hat f = \tilde f + S$
with $\tilde f(t, y) = f(y)$, and the product chart point $(t, z)$, the operator $\hat L(\sigma, v) = Lv$ lies in
$\mathrm{Lin}(\hat f, (t, x))$ for every $L \in \mathrm{Lin}(f, x)$, and an orientation $o$ of $\mathrm{DET}(f, x)$ gives
exactly one orientation $\hat o$ of $\mathrm{DET}(\hat f, (t, x))$ with $\hat o(\hat L)$ the image of $o(L)$ for **every**
$L$; $o \mapsto \hat o$ is injective. *Book:* Remark 6.42, p. 230. *Hidden hypotheses:* $x$ smooth and $\mathrm{Lin}(f,
x)$ nonempty (implied by bump functions, V6.1); only the orientation of $\mathrm{DET}(f, x)$ at the one point is used.
*Deviation (narrower):* at a point. As we read it, the literal $h \mapsto \tilde h$ is not continuous in $L$ where the
parity of $\dim\operatorname{coker}L$ changes, so the orientation of $\mathrm{DET}(\hat f, (t, x))$ it defines could
depend on the choice of $L$; the sign $(-1)^{\dim\operatorname{coker}L}$ (the sign of V6.40) is used, which agrees with
the text's map when $L$ is onto. $X \times [0, 1]$ is read as $\mathbb R \times X$ (decision D2), with the parameter first,
so $\tilde L(a, b) = La$ is conjugated by the swap of the factors. That $(t, y) \mapsto \hat o$ is an orientation of $\hat
f$ in the sense of Definition 6.40, built from an orientation of $f$, is not formalized (gap G.66) (Findings, items
95–97).

**V6.63 (Appendix 6.7.1, the proof of Lemma 6.5; `Polyfold.FourTermExact.Choice.exists_smul_source_value`,
`Polyfold.FourTermExact.Choice.wedgeC`).** For two choices of (91) the right-hand sides are related as the sources are: a
change of the basis of $Z$ multiplies both wedges by its determinant, a change of the bases of $A$ and $D$ multiplies both
sides by the same factor, and a change of complements adds to the basis of $Z$ vectors of $\alpha(A)$ and to the
$\gamma$-preimages vectors of $\beta(B)$, which leaves the wedges unchanged. *Book:* §6.7.1, pp. 234–235. *Hidden
hypotheses:* none. *Deviation (restated):* the step "independent of the choices of the basis if and only if $\det(\tau)
= \det(\varepsilon)$" is read as the homogeneity of (91) in the bases of $A$ and $D$, $\tau$ being the $\sigma$ just
introduced; the corrections $p_i$ lie in $\beta(B)$ (written $\beta(C)$) and are combinations of the $\beta$-images,
whose names are exchanged with those of the $\gamma$-preimages in the last step (possible misprints) (Findings, item 1).

**V6.64 (Appendix 6.7.2, the proof of Proposition 6.12; `Polyfold.mem_span_append_of_ker`,
`Polyfold.gammaProj_wedge_tmul`, `Polyfold.comp_comp_eq_of_projLE`).** For $P \le Q$ in $\Pi_T$: if $Qg = 0$, then $g$ is a
combination of the vectors $d_i$ plus $Tx$ with $x \in \ker(QT)$, so the classes of $d_i$ and $Tb_j$ span what the text
calls $\ker\tilde Q$; the classes $[T\tilde b]$ and $[QT\tilde b]$ in $F/R(P)$ differ by elements of that span, which does
not change the wedge. *Book:* §6.7.2, pp. 235–237. *Hidden hypotheses:* none. *Deviation (restated):* the spanning is
proved directly in $F$; the name $\alpha_q$ in the last part is read as $\alpha^P$ (possible misprint) (Findings, items 6,
7).

### What is not verified in this chapter

- p. 201, the facts recalled before Proposition 6.2: an M-polyfold is locally path connected, and two smooth points in
  one path component are joined by an sc⁺-smooth path. Only the local form inside a chart is formalized (V6.49), and
  "in the same path component" (Definitions 6.27, 6.38) is read as "joined by an sc-smooth path" (V6.58) (gap G.56;
  Findings, item 42).
- p. 201, the members of $\mathrm{Lin}(f, x)$ as sc-Fredholm operators on every level: they are shown Fredholm on level
  $0$, with the index $\mathrm{ind}(f, x)$, which is what the determinant lines use (V6.1) (gap G.64).
- p. 208, the alternative definition $\det(T) = \lambda(\ker T) \otimes \lambda(\operatorname{coker}(T)^*)$ and its
  identification with Definition 6.7 (gap G.57).
- p. 213, the identification (95) and the maps $V \otimes \lambda(\mathbb R^n) \to V$, $V \otimes \lambda^*(\mathbb R^n) \to V$ after
  Proposition 6.15; the formalized statements use only (94) (V6.17, V6.18) (gap G.58).
- p. 216, Lemma 6.19 in general (exterior powers, duals, sums and tensor products of finite-dimensional topological vector
  bundles); it is applied only to trivial bundles, and Proposition 6.20 is proved with explicit frames (V6.22) (gap G.59).
- pp. 218–219, the remark that $\mathrm{DET}(E, F)$ is not orientable, and the classical case at the opening of §6.5 (the
  determinant line bundle of a classical Fredholm section over a contractible $U$) (gap G.60; Findings, item 26).
- p. 220, Proposition 6.28 (1), the sc-smooth contractibility of $U$, and with it the word "contractible" in Theorem 6.35,
  Definition 6.36 and property (∗) of Theorem 6.37: (1′) is proved instead and is what the proofs use (V6.32, V6.48, V6.50,
  V6.57) (gap G.61).
- p. 222, Lemma 6.30 as a statement about manifolds: the solution set as a manifold with boundary with corners near $(t,
  \varphi(t), 0)$, the map $\pi$ and the smooth vector bundle $L$; the kernels are formalized as a continuous family of
  subspaces (V6.34, V6.42) (gap G.62).
- p. 222, property (P) of Lemma 6.29 for the slices $F_t$; the general position of $F$ at the points $(t, \varphi(t), 0)$,
  which the text derives from it, is proved (V6.33) (gap G.63).
- §6.5, paths, homotopies and families sc-smooth on $[0, 1]$, $[0, 1]^2$, $[0, 1]^n$ only, and $X \times [0, 1]$ as an
  M-polyfold with boundary: they are read on $\mathbb R$, $\mathbb R^2$, $\mathbb R^n$ and $\mathbb R^n \times X$ (decision D2), as for
  Proposition 6.2 in Chapter 3; a path that does not extend sc-smoothly to $\mathbb R$ is not covered (gap G.65; Findings,
  item 102).
- p. 229, Theorem 6.41, the orientation of $S$ as an orientation of the abstract finite-dimensional manifold $S$ (of its
  tangent bundle in the charts of the induced structure); what is verified is the tangent orientation at each zero and its
  continuity along the sc-smooth paths of zeros in a chart (V6.61) (gap G.67).
- p. 229, Theorem 6.41, the compatibility of the tangent orientations read in two charts at the same zero (V6.61) (gap
  G.68).
- pp. 229–230, the paragraph after Theorem 6.41: for $f$ not generic, a small sc⁺-perturbation $s$ supported near the zero
  set, the orientation of $S_{f+s}$ from $o_f$, and $\mathrm{Lin}(f + s, x) = \mathrm{Lin}(f, x)$ for the orientation of
  $\det((f + s)'(x))$ from $\mathrm{DET}(f, x)$ (gap G.69).
- p. 230, Remark 6.42 beyond a point: that $(t, y) \mapsto \hat o$ is an orientation of $\hat f$ in the sense of Definition
  6.40 (continuity over the orientable neighbourhoods of $\mathbb R \times X$, independence of the chart of the pull-back
  bundle), built from an orientation of $f$; the remark is verified at a point (V6.62) (gap G.66).
- p. 230, §6.6, the sections "admissible for the pair $(N, U)$"; the facts recalled there are Theorem 5.18 (V5.38, V5.39)
  and the orientation of $S_{f+s}$ (V6.61) (gap G.55).
- p. 231, Theorem 6.43 (the invariant $\Psi_{(f,o)}$ on $H^*_{dR}(X, \partial X)$), with its proof, pp. 231–233, and the case
  $\partial X = \emptyset$, p. 233: it needs the sc-differential forms and their cohomology of §4.4 (gaps G.37–G.40), integration
  over oriented compact manifolds with boundary with corners and Stokes' theorem, and the proper sc⁺-homotopy of Remark 5.16
  (gap G.44); not formalized (decision D1) (gap G.54). In the proof, the extension $p_1^*\omega \wedge p_2^*dt$ of $\omega$
  is read as $p_1^*\omega$ (possible misprint; Findings, item 103).
- §6.1 and §6.5, $T_xX$, $Y_x$, $\mathrm{Lin}(f, x)$ and $\mathrm{Or}^f_x$ as chart-free objects: they are made in chart points
  and identified between charts (V6.53–V6.55), since $T_xX$ carries no linear structure here (gaps G.6, G.7, G.13).

---

## 8. Sign-off

The statements below are the ones the reader is asked to confirm say what HWZ mean. Each is a summary of the V-item it names; the standing hypotheses of that item are not repeated.

1. (V1.1) An sc-Banach space is a sequence of Banach spaces $E_0 \supset E_1 \supset \cdots$ with compact inclusions and $E_\infty$ dense in every $E_m$, taken as an indexed family with injective compact inclusions; finite-dimensional spaces carry the constant structure, sums have levels $E_m \oplus F_m$, and $E^k$ has levels $E_{k+m}$.
2. (V1.2) An sc-operator is a linear map continuous $E_m \to F_m$ on every level, given by its level maps; an sc-isomorphism is one that is a continuous linear equivalence on every level.
3. (V1.3) An sc⁺-operator is an sc-operator $E \to F^1$; it is compact $E_m \to F_m$ on every level.
4. (V1.4) An sc-subspace is a closed subspace whose smooth points are dense in each $F \cap E_m$; an sc-splitting $E = F \oplus G$ consists of two sc-subspaces with $F_m$ and $G_m$ complementary on every level.
5. (V1.5) A finite-dimensional subspace is an sc-subspace iff it lies in $E_\infty$, and then has an sc-complement.
6. (V1.6) For a closed subspace $A$ of an sc-Banach space $E$, the quotients $E_m/A_m$ form an sc-Banach space $E/A$ with the quotient map an sc-operator whose level kernels are the $A_m$.
7. (V1.7) An sc-Fredholm operator is an sc-operator with sc-splittings $E = \ker T \oplus X$, $F = C \oplus \operatorname{range} T$, $\ker T$ and $C$ finite-dimensional, and $T$ bijective $X_m \to \operatorname{range}(T)_m$ on every level; its index $\dim\ker T - \dim C$ is $\dim\ker T_0 - \dim\operatorname{coker} T_0$, and each $T_m$ is Fredholm.
8. (V1.8) An sc-Fredholm operator is regularizing: $T e \in F_m$ implies $e \in E_m$; conversely, an sc-operator that is Fredholm on level $0$ and regularizing is sc-Fredholm.
9. (V1.9) The sum of an sc-Fredholm operator and an sc⁺-operator is sc-Fredholm.
10. (V1.10) A partial quadrant is a set $C = T^{-1}([0,\infty)^n \oplus W)$ for an sc-isomorphism $T : E \to \mathbb R^n \oplus W$; a tuple $(U, C, E)$ has $U = O \cap C$ with $O$ open.
11. (V1.11) A map is sc⁰ on $U$ if it maps $U_m$ into $F_m$ continuously for every $m$.
12. (V1.12) The tangent $TE$ is $E^1 \oplus E$ and $TU = U^1 \oplus E$, with levels $U_{m+1} \times E_m$.
13. (V1.13) A map is sc¹ on $U$ if it is sc⁰, differentiable from $U_1$ into $F_0$ at every point of $U_1$ with a derivative $Df(x)$ bounded on $E_0$, and $(x, h) \mapsto (f(x), Df(x)h)$ is sc⁰ on $TU$; $Df(x)$ is unique on relatively open subsets of partial quadrants; $x \mapsto Df(x)$ need not be norm continuous (an example on a weighted $c_0$ scale).
14. (V1.14) $f$ is sc^{k+1} if it is sc¹ with sc^k tangent map, and sc-smooth if sc^k for all $k$.
15. (V1.15) An sc⁰ map on an sc-domain is sc¹ iff on every level $f : U_{m+1} \to F_m$ is differentiable with a derivative extending to a bounded $Df(x) : E_m \to F_m$ that depends jointly continuously on $(x, h) \in U_{m+1} \times E_m$; then $f : U_{m+1} \to F_m$ is $C^1$, and $Df(x)$ is an sc-operator at smooth points.
16. (V1.16) If $f$ is sc^k on $U$ then $f : U^1 \to F^1$ is sc^k.
17. (V1.17) If $f$ is sc^k then $f : U_{m+k} \to F_m$ is $C^k$, and $f : U_{m+l} \to F_m$ is $C^l$ for $l \le k$.
18. (V1.18) If $f : U_{m+l} \to F_m$ is $C^{l+1}$ for all $m \ge 0$ and $0 \le l \le k$, then $f$ is sc^{k+1}, as in the text; if this holds for every $l$, $f$ is sc-smooth.
19. (V1.19) A map into $\mathbb R^N$ that is $C^{l+1}$ on $U_l$ for $0 \le l \le k$ is sc^{k+1}, as in the text; one that is $C^{l+1}$ on every $U_l$, or $C^\infty$ on $U$, is sc-smooth.
20. (V1.20) The composition of sc¹ maps between relatively open subsets of partial quadrants is sc¹ with $T(g \circ f) = Tg \circ Tf$; sc^k and sc-smooth maps compose likewise.
21. (V1.21) The degeneracy index $d_C(x)$ is the number of vanishing half-line coordinates of $T(x)$.
22. (V1.22) $d_C$ does not depend on the presentation $T$, and neither does the number $n$ of half-line factors.
23. (V1.23) An sc¹ map with sc¹ inverse between relatively open subsets of partial quadrants preserves the degeneracy index at every point.
24. (V1.24) For a compact operator $c$ on a Banach space, $1 + c$ is Fredholm (Riesz–Schauder); a continuous linear map with finite-dimensional kernel and closed range of finite codimension is Fredholm.
25. (V1.25) A compact perturbation of a Fredholm operator between Banach spaces is Fredholm.
26. (V1.26) If $(x, y) \mapsto A(x)y$ is $C^k$ on $s \times Y$ and $\iota : Y' \to Y$ is compact, then $x \mapsto A(x) \circ \iota$ is $C^k$ into $\mathcal L(Y', Z)$; for an sc¹ map the level operators $Df(x) : E_m \to F_m$ exist for $x \in U_{m+1}$ and are the derivatives of $f : U_{m+1} \to F_m$.
27. (V1.27) An sc-domain has level sets that are open-in-convex with unique differentiability; relatively open subsets of partial quadrants are sc-domains, and $T$ and the level shift preserve the property.
28. (V1.28) The index $\dim\ker - \dim\operatorname{coker}$ is additive under composition, and the Fredholm index between Banach spaces is invariant under small and under compact perturbations.
29. (V1.29) Every level map $T_m$ of an sc-Fredholm operator is Fredholm of index $\operatorname{ind}(T) = \dim K - \dim C$.
30. (V1.30) For $T$ sc-Fredholm and $S$ sc⁺, $\operatorname{ind}(T + S) = \operatorname{ind}(T)$, on every level.
31. (V1.31) An sc-structure on a finite-dimensional space is sc-isomorphic, through its inclusions, to the constant one; an onto inclusion $E_{m+1} \to E_m$ forces $E_m$ finite-dimensional.
32. (V1.32) $E = A \oplus B$ is an sc-splitting iff some idempotent sc-operator has range $A$ and kernel $B$.
33. (V1.33) For an sc-subspace $A$, a class $x + A$ meeting every $E_j$ contains a smooth point: the smooth points of $E/A$ are the classes of smooth points.
34. (V1.34) $(x, h) \mapsto A(x)h$ is jointly continuous iff $x \mapsto A(x)$ is continuous for uniform convergence on compact sets; so $Df$ is compact-open continuous on $U_1$, and not in general norm continuous (V1.13).
35. (V1.35) Between finite-dimensional spaces, on relatively open subsets of quadrants, sc¹ is $C^1$ within $U$ (one-sided derivatives at the boundary) and sc-smooth is $C^\infty$.
36. (V1.36) $C_1$ is a partial quadrant in $E^1$ and $TC$ one in $TE$; $U_1$ and $TU$ are relatively open in them.
37. (V1.37) If $f : U_{m+l} \to F_m$ is $C^{l+1}$ for all $m$ and $l \le k$, the derivatives $d^if(x)$ on $E_{m+l}$ into $F_m$ ($i \le l + 1$, $i \le k + 1$) are restrictions of one base-level map, continuous in $x$, and differentiable in $x$ with derivative $d^{i+1}f(x)$ for $i \le l$, $i \le k$.
38. (V1.38) An elementary map $z \mapsto d^if(\pi_0 z)(\pi_1 z, \dots, \pi_i z)$ with $\pi_0 : X \to E^p$, $\pi_a : X \to E^{n_a}$, into $F^m$, with $m + i \le p$, $m + i \le n_a + 1$, $i \le k$ and an sc-domain as domain, is sc^s for $i + s \le k + 1$; its tangent map is a pair of elementary maps and sums of them.
39. (V1.39) Sums of sc^k maps on an sc-domain are sc^k; the evaluation of continuous multilinear maps has the product-rule derivative.
40. (V2.1) An sc-smooth retraction is an sc-smooth $r : U \to U$, $U$ relatively open in a partial quadrant, with $r \circ r = r$; its retract $O = r(U)$ is its fixed-point set, and $Dr(x)$ is a projection for $x \in O_1$.
41. (V2.2) $(O, C, E)$ is a retract if $O = r(U)$ for such an $r$.
42. (V2.3) Two retractions onto the same $O$ have the same tangent image $Tr(TU) = Tr'(TU')$.
43. (V2.4) $TO = Tr(TU) = \{(r(x), Dr(x)h)\}$, and $T_xO$ is the range of the projection $Dr(x)$.
44. (V2.5) Sc-smoothness of $f \circ r$ and $T(f \circ r)$ on $TO$ do not depend on the retraction $r$ onto $O$, and $T(f \circ r)$ maps $TO$ into $TO'$.
45. (V2.6) $f : O \to O'$ is sc-smooth if $f(O) \subseteq O'$ and $f \circ r$ is sc-smooth for a (every) retraction onto $O$; $Tf = T(f \circ r)|_{TO}$.
46. (V2.7) Sc-smooth maps between retracts compose, with $T(g \circ f) = Tg \circ Tf$.
47. (V2.8) $(TO, TC, TE)$ is a retract with retraction $Tr$, and $Tf$ is sc-smooth between tangents.
48. (V2.9) Open subsets of retracts, and images of idempotent sc-smooth maps on retracts, are retracts.
49. (V2.10) A chart is a homeomorphism of an open set onto a retract; charts are compatible when both transition maps are sc-smooth between the overlap retracts.
50. (V2.11) An atlas is a set of pairwise compatible charts covering $X$; atlases are equivalent when their union is an atlas, and this is an equivalence relation.
51. (V2.12) An M-polyfold is a Hausdorff paracompact space with an atlas, its charts being all charts compatible with it.
52. (V2.13) $f$ is sc-smooth if it is continuous and all its coordinate representations are sc-smooth between retracts; one pair of charts per point suffices.
53. (V2.14) $X_m$ consists of the points that lie on level $m$ in one (every) chart, with the topology generated by the chart preimages of open subsets of $O_m$.
54. (V2.15) The inclusions $X_{m+1} \to X_m$ are continuous.
55. (V2.16) The level charts $(V_1, \varphi, (O_1, C_1, E^1))$ make $X_1$ an M-polyfold.
56. (V2.17) For every M-polyfold, $X$ and every $X_m$ are metrizable, $X_m$ is paracompact, and $X_\infty$ (initial topology of the inclusions) is metrizable; no hypothesis beyond the text's.
57. (V2.18) Tangent tuples $(x, \varphi, h)$ are equivalent when one is the transport of the other by $T$ of the transition map; this is an equivalence relation.
58. (V2.19) $TX$ is the set of classes, with $p : TX \to X_1$ and the bijections $T\varphi : TV \to TO$.
59. (V2.20) $TX$ is Hausdorff, metrizable and paracompact, and $p$ is continuous (openness of $p$ not verified).
60. (V2.21) The charts $(TV, T\varphi, (TO, TC, TE))$ make $TX$ an M-polyfold, with transition maps $T(\varphi' \circ \varphi^{-1})$, and $p : TX \to X^1$ is sc-smooth.
61. (V2.22) An sc-smooth $f : X \to Y$ has a well-defined sc-smooth tangent map $Tf : TX \to TY$ covering $f$, with $T(g \circ f) = Tg \circ Tf$.
62. (V2.23) A sub-M-polyfold is locally the image of an sc-smooth retraction of an open set.
63. (V2.24) A sub-M-polyfold, with the subspace topology, is an M-polyfold for which the inclusion and the maps $i^{-1} \circ r$ are sc-smooth.
64. (V2.25) In a chart, at a smooth $a$, $T_aO = Dt(a)E \oplus (Dr(a) - Dt(a))E$ is an sc-splitting with $Dt(a)E = T_aA$, and $Ts$ maps $T_aO$ onto $T_aA$.
65. (V2.26) $d_X(x)$ is the least $d_C(\varphi(x))$ over the charts $\varphi$ around $x$.
66. (V2.27) $d_X$ is upper semicontinuous.
67. (V2.28) Sc-diffeomorphisms between open sets preserve $d_X$.
68. (V2.29) $\partial X = \{d_X \ge 1\}$ is closed; $X$ is without boundary iff $d_X \equiv 0$.
69. (V2.30) On a sub-M-polyfold $A$, $d_A \le d_X$.
70. (V2.31) $E_x$ is the closed subspace cut out by the coordinates vanishing at $x$, of codimension $d_C(x)$; $C_x$ the cone on which they are $\ge 0$.
71. (V2.32) $T^R_xO = T_xO \cap E_x$ and $C_xO = T_xO \cap C_x$, defined at every $x \in O_1$.
72. (V2.33) $T^R_xO \subseteq C_xO \subseteq T_xO$, and $C_xO$ is a partial quadrant in $T_xO$ at every smooth point of every sc-smooth retract: the remark's claim that in general it is not is false.
73. (V2.34) For an sc¹ map between quadrants, $Df(x)(E_x) \subseteq E'_{f(x)}$ and $Df(x)(C_x) \subseteq C'_{f(x)}$ at every level-$1$ point.
74. (V2.35) A germ of sc¹-diffeomorphisms between retracts maps $T^R_xO$ onto $T^R_yO'$ and $C_xO$ onto $C_yO'$, at every level-$1$ point.
75. (V2.36) A nonempty retract, and a nonempty relatively open subset of a partial quadrant, is an M-polyfold with the chart $\mathrm{id}$.
76. (V2.37) $\dim(T_xO/T^R_xO) \le d_X(x)$ in every chart of every M-polyfold at points on level $1$; the second statement holds without its hypothesis (V2.33).
77. (V2.38) On a relatively open subset of a partial quadrant, the degeneracy index of the M-polyfold equals $d_C$.
78. (V2.39) $C_e$ and $E_e$ are the cone and the subspace cut out by the coordinates vanishing at $e$, in a presentation of $C$.
79. (V2.40) A retraction is tame if it preserves $d_C$ and, at smooth points of $O$, $T_xO$ has an sc-complement inside $E_x$ (for every presentation of $C$).
80. (V2.41) For a tame $r$ at a smooth $x \in O$, $(1 - Dr(x))E \subseteq E_x$ is an sc-complement of $T_xO$; only the second tameness condition is used.
81. (V2.42) For a tame retract, $\dim(T_xO/T^R_xO) = d_O(x)$ at smooth points, where $T^R_xO$ is an sc-subspace and $C_xO$ a partial quadrant in $T_xO$, and $d_O = d_C$ everywhere; a tame chart of any M-polyfold realizes $d_X$.
82. (V2.43) A tame M-polyfold has an equivalent atlas of charts with tame models.
83. (V2.44) A face is the closure of a component of $\{d_X = 1\}$; face-structured means every $x$ lies in exactly $d_X(x)$ faces.
84. (V2.45) Near a point of a tame retract, the retraction maps points of a coordinate hyperplane $f_i$ into the closure of a single component of $\{d_C = 1\} \cap O \cap f_i$.
85. (V2.46) The faces of a tame retract are the components of the sets $f_i \cap O$, distinct for distinct $i$ through a common point.
86. (V2.47) A tame retract is face-structured.
87. (V2.48) In a tame M-polyfold each point has a tame chart realizing $d_X$ whose model is face-structured, and lies in at most $d_X(x)$ global faces.
88. (V2.49) A face of a tame retract is the retract of $r \circ P_i$ on a neighbourhood of the face, hence a sub-M-polyfold, and with its induced structure it is tame with $d_F = d_O - 1$.
89. (V2.50) Every point of a tame M-polyfold lies in exactly $d_X(x)$ local faces, each tame with $d_F(x) = d_X(x) - 1$; the intersection of $\#\sigma$ of them is, near $x$, a tame sub-M-polyfold $A$ with $d_A = d_X - \#\sigma$.
90. (V2.51) In a tame M-polyfold the interior $F \cap \{d_X = 1\}$ of a face is a component $G$ and a sub-M-polyfold; if $X$ is face-structured, every face is a tame sub-M-polyfold with $d_X = d_F + 1$.
91. (V2.52) $X \times Y$ is an M-polyfold with the product charts, $d_{X\times Y} \le d_X + d_Y$, with equality and $X \times Y$ tame when $X$ and $Y$ are tame.
92. (V2.53) For a local sc-diffeomorphism $f$ and an sc-smooth $g$ the fibred product is a sub-M-polyfold of $X \times Y$ with $d = d_Y$, tame if $Y$ is; if both are local sc-diffeomorphisms, $d = d_X = d_Y$, and $2d = d_{X\times Y}$ for tame $X$, $Y$.
93. (V2.54) A strong bundle map preserves the double filtration, is linear in the fibre and sc-smooth on $[0]$ and $[1]$; a strong bundle retraction is an idempotent one, covering an sc-smooth retraction.
94. (V2.55) A local strong bundle retract $K = R(U \triangleleft F)$ and its part $K[1]$ are sc-smooth retracts, with sc-smooth projections to $O$.
95. (V2.56) Sections of $K$ are sc-smooth into $K[0]$, sc⁺ into $K[1]$; sc⁺ implies sc-smooth.
96. (V2.57) A strong bundle chart is a fibrewise linear homeomorphism $P^{-1}(V) \to K$ over a chart of $X$; compatibility means sc-smooth transitions on $[0]$ and $[1]$; equivalence of strong bundle atlases is an equivalence relation, and charts restrict to open subsets of the base.
97. (V2.58) A strong bundle is $P : Y \to X$ with a strong bundle atlas; $Y[0]$ and $Y[1]$ are M-polyfolds, $P[0]$ and $P[1]$ are sc-smooth, and one chart decides whether $y \in Y_{m,k}$; the charts compatible with the atlas depend only on its class.
98. (V2.59) Sections of a strong bundle are sc-smooth into $Y[0]$, sc⁺ in the charts $\Phi[1]$, which is the same as sc-smooth into $Y[1]$.
99. (V2.60) The pull-back $f^*Y$ is the fibre product of $P$ and $f$.
100. (V2.61) The pull-back of a strong bundle along an sc-smooth map is a strong bundle, with the pulled-back charts and retractions $R_g$.
101. (V2.62) A paracompact Hausdorff locally metrizable space is metrizable (Smirnov), proved in a pull-back form.
102. (V2.63) Sc^k-smoothness restricts to smaller domains and is a local property.
103. (V2.64) $Y[1]$ is Hausdorff and paracompact (metrizable), and the inclusion $Y[1] \to Y[0]$ is sc-smooth.
104. (V3.1) A germ of neighbourhoods is a nested sequence of relatively open neighbourhoods $U_m$ of $0$ in $C_m$, with tangent germ $(U_{m+1} \times E_m)_m$; a germ is a fixed sequence of sets.
105. (V3.2) sc⁰-, sc¹-, sc^k- and sc-smooth germs are the notions of Chapter 1 with $U \cap E_m$ replaced by $U_m$.
106. (V3.3) Germs restrict, compose (when the inner germ maps $U_m$ into $V_m$ level by level), pair, and sc-operators are sc-smooth germs.
107. (V3.4) Propositions 1.16–1.18 hold for germs.
108. (V3.5) An sc-smooth section germ is a section whose principal part composed with $r$ is an sc-smooth germ, on some germ of neighbourhoods inside $U$, in some centred strong bundle chart compatible with the atlas.
109. (V3.6) Sums of sections have sums of principal parts; sc⁺-sections have sc-smooth representatives $O \to K[1]$ in every compatible chart.
110. (V3.7) A filling is an sc-smooth germ satisfying (1)–(3) of Definition 3.4 near $0$, the map in (3) an sc¹-germ (the text's germ reading).
111. (V3.8) For a filler with $g(0) = 0$, $Tf(0) = Dg(0)|_{Dr(0)E}$ is onto iff $Dg(0)$ is, Fredholm iff $Dg(0)$ is, with the same index; if $Dg(0)$ is sc-Fredholm, so is $Tf(0)$, and condition (3) holds on every level.
112. (V3.9) A filled version is a filling of the principal part in the chart of Definition 3.11, an sc-smooth germ whose levels may shrink with $m$.
113. (V3.10) A basic germ is an sc-smooth germ with $f(0) = 0$ whose $W$-component is $w - B(a, w)$ with $B$ an sc⁰-contraction germ.
114. (V3.11) For sc¹ sc⁰-contraction germs, Lemma 3.9 as stated: $|D_2B(x)\zeta|_m \le \varepsilon|\zeta|_m$ for $x \in U_{m+1}$ small on level $m$, for every $\varepsilon$ and $m$; and $D_2B(0, 0) = 0$.
115. (V3.12) $D(h + s)(0)$ is sc-Fredholm of index $n - N$ for a basic germ $h$ and an sc⁺-germ $s$, and on every level $m$, $D(h + s)(x)$ is Fredholm of index $n - N$ for $x \in U_{m+1}$ small on level $m$.
116. (V3.13) An sc-Fredholm germ has a filling germ $g$ and an sc⁺-germ $s$, $s(0) = g(0)$, with $g - s$ conjugated to a basic germ near $0$ (the text's germ reading).
117. (V3.14) Near a zero of an sc-Fredholm germ, the closures of the zeros in $O(i)$ are compact subsets of $X_i$.
118. (V3.15) Zeros converging to the base point (or, for sc-Fredholm sections, to any point) converge on every level.
119. (V3.16) An sc-Fredholm section is sc-smooth, regularizing and an sc-Fredholm germ at every smooth point.
120. (V3.17) An sc-Fredholm section plus an sc⁺-section is sc-Fredholm, for any strong bundle.
121. (V3.18) $s \circ r$ agrees with $s$ on $O$ and $R$ fixes $(r(u), s(r(u)))$.
122. (V3.19) $g + s \circ r$ is a filling germ of $f + s$ when $g$ is one of $f$, for $s$ an sc-smooth section of $K$ (a germ suffices).
123. (V3.20) Good position: $N \cap C$ has interior in $N$ and an algebraic complement satisfies the $\varepsilon$-condition; the text's sc-complement form is also formalized and holds for smooth $N$ on a partial quadrant.
124. (V3.21) If $N$ is in good position to $C$, then $N \cap C$ is a partial quadrant in $N$.
125. (V3.22) The tangent germ property, with $Y$ closed and "sc^∞-germ" read with $k$-dependent neighbourhoods.
126. (V3.23) The tangent germ property is invariant under sc-diffeomorphisms.
127. (V3.24) Under the regularity conditions (a) $\delta$ sc-smooth on $V$, (b) $\pi(O) \subseteq C$, a set with the tangent germ property is a sub-M-polyfold, tame, with corner charts $\pi\varphi$; without (a), (b) the text's proof fails in examples.
128. (V3.25) An sc⁰-contraction germ has the contraction estimate on small balls on every level, and a working form with explicit regions.
129. (V3.26) The solution germ exists, is sc⁰, and is unique in the contraction region.
130. (V3.27) If $B$ is sc¹, the solution germ is sc¹ on the germ shifted by one level.
131. (V3.28) $f^{(1)}$ is a contraction germ of class sc^{min(k, j)} with solution germ $T\delta$; it satisfies Definition 3.28.
132. (V3.29) If $B$ is sc^k, the solution germ is sc^j on some shifted germ for every $j \le k$.
133. (V3.30) If $B$ is sc^k, the solution germ is sc^k on the germ shifted by $2^k - 1$ levels; the text's hypotheses suffice.
134. (V3.31) If $B$ is sc-smooth, $\delta$ is $C^k$ into $W_m$ on a neighbourhood $V_{m,k}$ of $0$; $\delta$ is an sc-smooth germ on one germ.
135. (V3.32) For a quadrant-like $\widetilde C$, any representative of the solution germ of an sc^k (sc-smooth) contraction germ is sc^k (an sc-smooth germ) on a smaller germ.
136. (V3.33) The basic class is Definition 3.7.
137. (V3.34) A linear coordinate change makes the index-raised push-forward of a basic germ plus an sc⁺-germ a basic germ, with $n - N$ unchanged.
138. (V3.35) The solutions near $0$ of a contraction germ plus an sc⁺-germ have compact closures on every level, for closed $\widetilde C$.
139. (V3.36) Zeros of $h + s$ near $0$ lie on level $1$, where the linearization is surjective Fredholm of index $n - N$.
140. (V3.37) Zeros of the push-forward near $0$ have their $X$-component small on level $1$.
141. (V3.38) Under Lemma 3.42's regularity, the zeros of $g$ near $0$ form the graph of a $C^1$ map $\tau$ over $\ker Dg(0) \cap C'$ into a good complement, $\tau(0) = 0$, $D\tau(0) = 0$, and $\tau$ is $C^k$ into level $k$ near $0$ for every $k$.
142. (V3.39) $\ker Dg(0)$ is the graph of $D\delta(0)$ over $\ker DH(0)$.
143. (V3.40) Linear isomorphisms carrying $C$ onto $C'$ carry good complements and good position.
144. (V3.41) $\ker DH(0)$ has a good complement $Z$ with $Z \times W$ a good complement of $K'$.
145. (V3.42) The zeros of $f + s$ near $0$ form the graph of a $C^1$ map $\sigma$ over $\ker D(f + s)(0) \cap C$, $\sigma(0) = 0$, $D\sigma(0) = 0$, $C^k$ into level $k$ near $0$ for every $k$.
146. (V3.43) Definition 3.48 is Definition 3.4.
147. (V3.44) After shrinking, (1) and (2) of the filler hold on all of $O \cap W$, $U \cap W$.
148. (V3.45) Definitions 3.50, 3.51 are Definitions 3.11, 3.14 for a tame strong bundle; the theorems of §3.6 use them with the chart of the germ data tame (V3.103).
149. (V3.46) In a centred chart, $Dg(0)$ and $Tf(x_0)$ are sc-Fredholm with index $n - N$ on every level, the dimensions of any basic germ to which $g - s$ is conjugated; at a zero of an sc-Fredholm section the linearization is sc-Fredholm in every chart.
150. (V3.47) Good position of the germ: $Tf(0)$ onto and $\ker Dg(0)$ in good position to $T_0O \cap C$ in $T_0O$, in a centred chart; also with the text's sc-complement, the same at zeros of sc-Fredholm sections with tame germ data.
151. (V3.48) Near a zero in good position in a tame chart, the zero set is carried injectively by $\psi\varphi$ onto the graph of a $C^1$ map $\sigma$ over $\ker D(h + t)(0) \cap C'$, with $Y$ closed, the kernel smooth, and $C^k$-lifts of $\sigma$ into level $k$.
152. (V3.49) Along the graph of $\tau$ near $0$, $Y$ (closed) stays a good complement of $N_v$ with respect to $C_{v + \tau(v)}$; also for $\tau$ on a relatively open $V$ and any presentation of $C$.
153. (V3.50) Without boundary, a zero set with the regular tangent germ property is a manifold without boundary.
154. (V3.51) A zero set with the regular tangent germ property is a tame sub-M-polyfold and a manifold with boundary with corners.
155. (V3.52) Injectivity of $L(0)$ and the compactness property make $L(b)$ injective for $b$ near $0$; in Theorem 3.58 both hypotheses follow from its condition (2).
156. (V3.53) On a compact parameter set with injective $L(b)_m$ there is a uniform lower bound $c_m$.
157. (V3.54) $(v, k) \mapsto L(v)^{-1}k$ is an sc-smooth germ under uniform lower bounds $c_m$.
158. (V3.55) A good complement has vanishing coordinates in $\Sigma$.
159. (V3.56) $d_{N \cap C} = d_C$ off $N \cap W$, and $d_{N \cap C} + \dim(N \cap W) = \dim N$ on it.
160. (V3.57) $d_{N \cap C}(v) = d_C(v + \tau(v))$ for $v \notin N \cap W$ near $0$.
161. (V3.58) The quadrant inverse function theorem holds for $C^j$ maps.
162. (V3.59) A $C^j$ map with $\|Df - 1\| \le \tfrac12$ preserving interior points is a $C^j$-diffeomorphism onto a relatively open set.
163. (V3.60) Such a map is bi-Lipschitz, injective, and has relatively open image.
164. (V3.61) Such a map is a homeomorphism onto its image.
165. (V3.62) Its inverse has derivative $[Df(g(y))]^{-1}$.
166. (V3.63) The implicit function theorem in partial quadrants, with $f(k + \tau(k)) = 0$ and $k + y \in U$.
167. (V3.64) There is a region on which $B(k, \cdot)$ is a $\tfrac12$-contraction and fixed points are unique.
168. (V3.65) $B(k, \cdot)$ maps $\{|y| \le \varepsilon|k|\}$ into itself.
169. (V3.66) $\tau$ is continuous with $|\tau(k)| \le \varepsilon|k|/2$, Lipschitz with constant $\varepsilon/(1 + \varepsilon) \le \varepsilon$ on all of $V_0$.
170. (V3.67) $\tau$ is $C^j$ on the whole $V_0$, with the derivative formula.
171. (V3.68) Under the filler condition at the nearby zeros (a consequence of good position, V3.102), near a zero in good position in a tame chart of an sc-Fredholm section with tame germ data over an M-polyfold without boundary the zeros are smooth points in good position in tame charts and form a manifold without boundary; the forms with the text's hypotheses, the index and the kernel are V3.95, V3.97, V3.99, V3.101.
172. (V3.69) Near a zero in good position in a tame chart whose nearby zeros are in good position in tame charts (or, for tame germ data, under the filler condition of V3.82), the local solution set consists of smooth points and is a tame sub-M-polyfold equivalent to a $d$-dimensional manifold with boundary with corners.
173. (V3.70) With good position in a tame chart at every zero ($S \ne \emptyset$), the solution set is a sub-M-polyfold with tame induced structure, a manifold with boundary with corners of locally constant dimension; no hypothesis is added.
174. (V3.71) The image of a tame retract under an sc-diffeomorphism, and an open subset of a tame retract, are tame retracts.
175. (V3.72) A nonempty set with regular data of Definition 3.25 of some dimension at every point is a sub-M-polyfold, tame, with an atlas of finite-dimensional corner charts $\pi\varphi$.
176. (V3.73) Two graph descriptions of one set, the first $C^1$ and the second centred at a point of it with $C^k$-lifts at $0$, have the same dimension, and the first is $C^k$ into every level near that point.
177. (V3.74) Data of Definition 3.25 with $\pi(O) \subseteq C$, at a point whose neighbours all have data, can be shrunk to regular data, and the dimension is locally constant.
178. (V3.75) A finite-dimensional subspace in good position has a closed good complement along which the projection maps the partial quadrant into itself.
179. (V3.76) If $g$ is conjugated to a basic germ and $s$ is an sc⁺-map with $s(0) = 0$, then $(g + s)^1$ is conjugated to a basic germ, by $\Lambda \circ \Phi^1$.
180. (V3.77) Theorems 3.43, 3.47 and the graph description of Theorem 3.54 hold with a closed good complement whose projection maps the partial quadrant into itself.
181. (V3.78) At a zero, the linearizations in two strong bundle charts are conjugate by isomorphisms respecting the partial quadrants: surjectivity, Fredholm index and good position of the kernel do not depend on the chart.
182. (V3.79) Surjectivity onto a dense part of $K_z$ and good position of $\ker Dg(z) \cap T_zO$, in a chart not centred at the zero $y$ ($z$ in the germ of $g$), give good position of $(f, y)$ in a tame chart, for tame germ data.
183. (V3.80) In the chart at $x_0$, at the zeros near $x_0$, $D(h + t)$ is surjective Fredholm of index $n - N$ and the tangent space $N_v$ of the graph is in good position with complement $Y$.
184. (V3.81) In the chart at $x_0$, at the zeros near $x_0$, $\ker Dg(z_0) = D\psi^{-1}(N_v)$ lies in $T_{z_0}O$ and is in good position there; no hypothesis is added.
185. (V3.82) For tame germ data, if the filler in the tame chart at $x_0$ also satisfies condition (3) of Definition 3.4 at its zeros near $0$, every zero near $x_0$ is in good position in a tame chart; the text's argument needs that condition, which holds whenever $(f, x_0)$ is in good position (V3.102).
186. (V3.83) A good complement of $\mathbb R \times N$ projects into the lineality space; the tilted kernel of the parameter extension is in good position.
187. (V3.84) At a zero $x_0$ in good position in a tame chart, the solution set near $x_0$ has data of Definition 3.25 at $x_0$ in the chart $\psi\varphi$, with $\pi(O) \subseteq C$.
188. (V3.85) If $x_0$ and the zeros near it are in good position in tame charts, the solution set has regular data at $x_0$ of a dimension $d$ that every nearby datum shares; Theorem 3.54 (1)–(2) under the filler condition of V3.82.
189. (V3.86) Over an M-polyfold without boundary, with good position in a tame chart at every zero, the solution set is a manifold without boundary of locally constant dimension.
190. (V3.87) With good position in a tame chart at every zero (the text's hypotheses), the solution set is a sub-M-polyfold with tame induced structure, a manifold with boundary with corners of locally constant dimension, the disjoint union of its open and closed parts $S_n$ of dimension $n$.
191. (V3.88) Given sc-isomorphisms $L(b) = P_Y Df(b, 0)|_X$ with uniform lower bounds and condition (3), $\Phi_*(f - f(0))$ is a basic germ with contraction $x - L(b)^{-1}P_Y(f - f(0))$.
192. (V3.89) Under conditions (1)–(3) of Theorem 3.58, in the coordinates of its proof, $f - f(0)$ is conjugated near $0$ to a basic germ.
193. (V3.90) A $C^j$ map with $\|Df - 1\| \le \tfrac12$ on a convex set, whose image has unique differentiability, has a $C^j$ inverse with $Dg = [Df \circ g]^{-1}$.
194. (V3.91) For a strong bundle (tameness not needed), an sc-Fredholm section $f$ and sc⁺-sections $s_i$, $(r, x) \mapsto f(x) + \sum r_is_i(x)$ is an sc-Fredholm section of the pull-back bundle over $\mathbb R^n \times X$.
195. (V3.92) In the product chart at $(0, x)$ the linearization of the perturbed section is $(\delta r, \xi) \mapsto f'(x)\xi + \sum\delta r_is_i(x)$ (chart form); at $(r_0, x)$ the first term is that of $f + \sum r_{0,i}s_i$.
196. (V3.93) In the chart at a zero $x_0$ in good position, at every zero $z_0$ of the filler near $0$ and for every smooth $k$, $\rho(z_0)k = Dg(z_0)x$ for some $x \in T_{z_0}O$, by a curve of zeros of $g + \mu\rho(r(\cdot))k$ through $z_0$ from an implicit function theorem at $z_0$.
197. (V3.94) With the text's hypotheses (tame germ data, good position in a tame chart), every zero near a zero in good position is in good position in a tame chart, and the solution set has there regular data of a dimension that every nearby datum shares; also with good position in the text's sense (sc-complement) in the conclusion.
198. (V3.95) With the text's hypotheses (tame germ data, good position in a tame chart), the local solution set near a zero in good position consists of smooth points in good position in tame charts and is a tame sub-M-polyfold, a $d$-dimensional manifold with boundary with corners, without boundary if $d_X \equiv 0$.
199. (V3.96) At a zero, the linearization in every chart is sc-Fredholm of the index $n - N$ of any conjugating basic germ on every level, and onto on every level with $\dim\ker = n - N$ if the germ is in good position.
200. (V3.97) The dimension of the solution set near a zero in good position in a tame chart is the Fredholm index, $\dim\ker f'(y) = \mathrm{ind}\,f'(y)$, at every zero near it and in every chart; also in Theorems 3.23, 3.19, 3.57.
201. (V3.98) For tame germ data, near a zero in good position in a tame chart, every zero $y$ has $f'(y)$ onto with $\mathrm{ind}\,f'(y) = \mathrm{ind}\,f'(x_0)$: the index is locally constant along the solution set; for tame germ data, without bump functions, the index is locally constant along the zero set without good position, the index of Definition 6.1 with a locally defined sc⁺-section is well defined and exists at every smooth point, and it is constant along every sc-smooth path $\mathbb R \to X$ (Proposition 6.2); under bump functions the local and the global reading of Definition 6.1 agree.
202. (V3.99) At the zeros near $x_0$, $D\psi$ maps $\ker f'(y)$, read in the chart at $x_0$, onto the tangent space of the solution graph.
203. (V3.100) For an sc-Fredholm section with tame germ data and a zero $y$ with $d_X(y) = 0$, $(f, y)$ is in good position in a tame chart if and only if $f'(y)$ is onto.
204. (V3.101) Over an M-polyfold without boundary, Theorems 3.19 and 3.56 hold for tame germ data with the hypothesis "$f'(x)$ surjective", with tame induced structure and the dimension the index.
205. (V3.102) At a point of the retract with $\ker Dg \subseteq T_{z_0}O$, $\rho(z_0)F \subseteq Dg(T_{z_0}O)$ implies condition (3) of the filler there (and conversely when $Dg$ is onto); so the filler condition at the nearby zeros holds whenever $f$ has tame germ data and $(f, x_0)$ is in good position in a tame chart.
206. (V3.103) The theorems of §3.6 assume, as Definitions 3.50, 3.51 and 3.53 do, germ data and good position in a strong bundle chart whose base retraction is tame; compatible charts whose base retraction is the identity of $U$ are tame, so the hypotheses can be met.
207. (V3.104) The product of the constant retraction onto $(1, 0)$ of $[0, \infty) \oplus W$ with any sc-smooth retraction of a nonempty set is not tame: the degeneracy index drops by one under it.
208. (V3.105) If $f$ is an sc-Fredholm section with tame germ data and $s$ an sc⁺-section, $f + s$ has tame germ data, in the same charts.
209. (V3.106) If $f$ has tame germ data, $(r, x) \mapsto f(x) + \sum r_is_i(x)$ is an sc-Fredholm section of $\pi^*P$ with tame germ data: the product chart of a tame chart is tame.
210. (V3.107) The good position of $(f, y)$ obtained in one chart holds in every chart carrying germ data at $y$, in particular in the tame one.
211. (V4.1) A corner chart is a chart onto a relatively open subset of a partial quadrant in a finite-dimensional space with the constant structure; a corner structure is an equivalent atlas of corner charts, of possibly varying dimension, and makes $X$ tame.
212. (V4.2) The transition maps between compatible corner charts are $C^\infty$ on their relatively open overlaps.
213. (V4.3) An sc-Banach space with finite-dimensional $E_0$ has all levels equal and is sc-isomorphic to $E_0$ with the constant structure; all its points are smooth.
214. (V4.4) Corner structures are the atlases of charts onto relatively open subsets of partial quadrants in sc-Banach spaces with finite-dimensional $E_0$; those of fixed dimension $n$ are the manifolds with corners of Theorem 3.27.
215. (V4.5) An M-polyfold, tame or not, has a corner structure iff all its points are smooth, $1_0^1$ is sc-smooth, and every point is the centre of a tame chart whose $T_0O$ is finite-dimensional and in good position.
216. (V4.6) $1_1^0 : X^1 \to X$ is sc-smooth; if $X = X_1$ and $1_0^1$ is sc-smooth it is an sc-diffeomorphism; some M-polyfold with $X_0 = X_\infty$ has $1_0^1$ not sc-smooth; a finite-dimensional space with the constant structure has $V^1 = V$, and all its retracts are sc⁺-retracts.
217. (V4.7) An sc⁺-map is a map with sc-smooth lift into $F^1$; it raises levels, is sc-smooth, and is preserved by composition with sc-smooth maps on either side.
218. (V4.8) At a smooth point the derivative of an sc⁺-map is an sc⁺-operator, compact on every level; a compact projection has finite-dimensional range.
219. (V4.9) An sc⁺-retraction is an sc-smooth retraction that is an sc⁺-map (on an open subset of an M-polyfold: with values in $X_1$ and $1_0^1 \circ s$ sc-smooth).
220. (V4.10) A retraction with the same retract as an sc⁺-retraction is an sc⁺-retraction.
221. (V4.11) An sc⁺-retract is the retract of some, equivalently of every, retraction, which is sc⁺.
222. (V4.12) The retract of an sc⁺-retraction consists of smooth points and its tangent spaces are finite-dimensional.
223. (V4.13) A retract is an sc⁺-retract iff it consists of smooth points and the lift $O \to O^1$ is sc-smooth between retracts.
224. (V4.14) A chart's model is an sc⁺-retract iff its domain is smooth and $1_0^1$ is sc-smooth on it; "$X_0 = X_\infty$ and $1_0^1$ sc-smooth" iff every chart's model is an sc⁺-retract.
225. (V4.15) $C_e$ is a partial quadrant with $C_e - e = C_e$; near $e$ it agrees with $C$, and re-centring preserves degeneracy indices, minimal subspaces and the cones $C_v$.
226. (V4.16) Translation by a smooth $e$ is an sc-diffeomorphism from relatively open subsets of $C$ near $e$ onto relatively open subsets of $C_e$, and carries retracts (tame retracts) to retracts (tame retracts).
227. (V4.17) Every smooth point of a chart's domain is the centre of a re-centred chart of $X$, tame if the original is.
228. (V4.18) Re-centring a strong bundle chart in the base gives a strong bundle chart; every smooth point of the base is the centre of one.
229. (V4.19) An sc⁺-retraction is $C^1$ on every level $k + 1$ with operator-norm-continuous derivative, and satisfies the mean value estimate with any constant $\theta$ on small balls of $C_{k+1}$.
230. (V4.20) For an sc⁺-retraction onto $O \ni 0$ with $T_0O$ in good position, a closed good complement $Y$ and the projection $p$ along $Y$, $p$ is an sc-diffeomorphism from $O \cap W$ onto a relatively open $V \ni 0$ of $T_0O \cap C$, with inverse $\Gamma$, $\Gamma(a) - a \in Y$.
231. (V4.21) Near $0$, $(1 - p)$ contracts differences of points of $O$ on level $k + 1$, so two such points with the same projection coincide.
232. (V4.22) For small $a \in N \cap C$ there is a point $u \in O$ with $p(u) = a$, $u - a \in Y$ small on level $1$.
233. (V4.23) Projections of points of $O$ near $0$ lie in $C$, and the neighbourhoods $W$, $V$ and the inverse $\Gamma$ exist with the required level-$1$ control.
234. (V4.24) $\Gamma$ is Lipschitz on level $1$, continuous into every level, and differentiable into every level with the frame formula $D\Gamma(a) = Dt(\Gamma(a))|_N(p\,Dt(\Gamma(a))|_N)^{-1}$.
235. (V4.25) $\Gamma$ is $C^\infty$ into every level, hence sc-smooth on the fixed $V$; $p$ and $\Gamma$ are sc-smooth between the retracts.
236. (V4.26) A chart composed with an sc-diffeomorphism between retracts is a chart of the M-polyfold.
237. (V4.27) Corner charts re-centre to tame centred charts whose $T_0O$ is the whole finite-dimensional space, in good position; so (i) implies (ii).
238. (V4.28) Under (ii), $p \circ \psi$ (with a closed good complement) is a corner chart of $X$ at every point; so (ii) implies (i).
239. (V4.29) A smooth finite-dimensional submanifold is locally the image of an sc⁺-retraction on an open set; it is a sub-M-polyfold.
240. (V4.30) In every chart, $\varphi \circ s \circ \varphi^{-1} \circ r$ is an sc⁺-retraction onto the chart image of $A$, whose points are smooth.
241. (V4.31) In a chart, $T_aA$ is the image of $T_aX$ under the tangent map of $s$, lies in $T_aX$, and is finite-dimensional.
242. (V4.32) At points with $d_X = 0$ a submanifold is in good position; if $d_X = 0$ on all of $A$, $A$ has a corner structure, without tameness of $X$.
243. (V4.33) $A \subseteq X_\infty$, and all points of $A$ are smooth for its induced structure.
244. (V4.34) $A$ is locally closed in $X$.
245. (V4.35) $\partial A \subseteq \partial X$.
246. (V4.36) $1_0^1 : A \to A^1$ is sc-smooth for the induced structure.
247. (V4.37) Tangent spaces of retracts are germs, are monotone under inclusion of retracts, and are mapped into each other by derivatives of maps between retracts.
248. (V4.38) Good position of $A$ at $a$ means, in a chart, that $T_zA$ is in good position to $C_z$ inside $T_zO$.
249. (V4.39) Good position of $A$ at $a$ does not depend on the chart, the data of Definition 4.13 or the presentation.
250. (V4.40) A tame submanifold is one whose induced M-polyfold structure is tame.
251. (V4.41) A smooth finite-dimensional submanifold of a tame M-polyfold, in good position everywhere, has a corner structure and is tame.
252. (V4.42) In a tame centred chart, good position inside $T_0O$ gives good position in $E$, with good complement $Y \oplus (1 - \pi)E$ and constant $\varepsilon/(\|\pi\| + 1)$.
253. (V4.43) For tame $X$, good position at a point holds at all nearby points of $A$.
254. (V4.44) General position of $A$ at $a$ means, in a chart, an sc-complement of $T_zA$ in $T_zO$ inside $T^R_zO$, level by level.
255. (V4.45) General position does not depend on the chart, the data or the presentation.
256. (V4.46) At the corner of a centred chart, $N + E_0^{\min} = E_0$ gives onto coordinates, good position with a closed complement in $E_0^{\min}$, and $d_{N \cap C} = d_C$ on $N \cap C$.
257. (V4.47) A finite-dimensional smooth $N$ has in $N + R$ an sc-complement inside the sc-subspace $R$; $T_yQ + E_0^{\min} = E_0$ gives general position at $y$.
258. (V4.48) In a tame retract, general position at a smooth point implies good position.
259. (V4.49) In a tame centred chart, general position at the centre gives the graph description with $Y \subseteq E_0^{\min}$, equal degeneracy indices along the graph, and general position along it.
260. (V4.50) Theorem 4.22 (1)–(4) holds in a tame chart centred at a point of general position, with $F_\sigma$ a germ inside $U$; (1) and (4) for the faces of the chart model, not of $U$ itself.
261. (V4.51) $\Gamma \circ \kappa_\sigma \circ p \circ t$ is an sc⁺-retraction onto $A \cap F_\sigma$ in the chart; its corner model is sc⁺ and in general position in the face model.
262. (V4.52) An sc⁺-retraction in a chart is an sc⁺-retraction on an open subset of $X$; $A \cap F_\sigma$ is a tame submanifold of the tame $F_\sigma$, in general position in it.
263. (V4.53) A stratified regular point is one where the projection maps the tangent space of the stratum through it onto $\mathbb R^m$, in some product chart.
264. (V4.54) Theorem 4.23: almost every $\lambda$ with $|\lambda| < \varepsilon$ is a stratified regular value whose fibre is a compact submanifold in general position with a tame corner structure.
265. (V4.55) In a tame chart $\operatorname{codim}T^R_xX = d_X(x)$; general position at $a$ gives $d_X(a) \le \dim T_aA$, and a zero-dimensional submanifold in general position avoids $\partial X$.
266. (V4.56) Sard: the critical values of a $C^\infty$ map between finite-dimensional spaces form a Haar-null set.
267. (V4.57) The strata of $\{\ell \ge 0\}$ have dimension $\dim V - \#\sigma$, and the stratified critical values of a $C^\infty$ map form a null set.
268. (V4.58) Theorem 3.78 for $C^\infty$ data has a $C^\infty$ solution.
269. (V4.59) At a stratified regular point the kernel of $Df$ is in good position to the local partial quadrant, with a closed complement in the stratum.
270. (V4.60) Near a stratified regular point the fibre of $f$ is the image of a $C^\infty$ retraction whose derivative at the point is the identity on $\ker Df$.
271. (V4.61) $e \mapsto (\Gamma(\rho(p(t(c, e)))))_2$ is an sc⁺-retraction onto the chart image of $A_c$, whose tangent space contains the vertical tangent vectors of $A$.
272. (V4.62) General position of $A$ and stratified regularity at $z$ give general position of the fibre at $z_2$.
273. (V4.63) Every point of $A$ has a neighbourhood and a null set of parameters off which the conclusions of Theorem 4.23 hold locally.
274. (V4.64) Countably many such neighbourhoods cover $A$, so for any parameter set the good parameters have null complement.
275. (V5.1) Every strong bundle chart compatible with the atlas reads $Y_{0,1}$ by the fibre component in $F_1$, and its $\Phi[1]$ is a chart of $Y[1]$.
276. (V5.2) The points of $P^{-1}(x)$ in $Y_{0,1}$ form a linear subspace, complete for the chart norm $|\cdot|_1$; the norms of two charts are locally uniformly comparable.
277. (V5.3) An auxiliary norm is a continuous function on $Y[1]$, a complete norm on every fibre, with $P(w_k) \to x$ and $N(w_k) \to 0$ forcing $w_k \to 0_x$.
278. (V5.4) A continuous fibrewise complete norm is auxiliary iff near every point it is two-sided comparable with $|h|_1$ in some strong bundle chart, also literally on the whole domain of the chart; auxiliary norms are so in every chart.
279. (V5.5) Every strong bundle has an auxiliary norm, glued from the chart norms by a partition of unity.
280. (V5.6) Two auxiliary norms are comparable by a continuous positive function $f$: $fN_0 \le N_1 \le f^{-1}N_0$.
281. (V5.7) Compact solution set, weakly proper and proper are as in the text, with $N = \infty$ off $Y_{0,1}$; for continuous $f$ proper implies weakly proper implies compact solution set.
282. (V5.8) Near $0$, the points where a basic germ (on a closed $\tilde C$) has level-$1$ norm $\le c$ lie in a compact set, on a neighbourhood independent of $c$.
283. (V5.9) Strong bundle maps have locally uniform $(0, 1)$ fibre bounds; at an sc-Fredholm germ the points with $|\Phi(f(x))_2|_1 \le C$ near $x_0$ have compact closure, for every $C$.
284. (V5.10) An sc-Fredholm section with compact solution set is proper, without tameness; proper, weakly proper and compact solution set are equivalent for sc-Fredholm sections.
285. (V5.11) At a zero of an sc-Fredholm section there are nested neighbourhoods $U(i)$ with $\operatorname{cl}\{y \in U(i) \mid f(y) = 0\}$ compact in $X_i$.
286. (V5.12) With the initial topology of the inclusions, $X_\infty$ is metrizable, and a compact solution set of an sc-Fredholm section is compact in $X_\infty$, without tameness.
287. (V5.13) For an sc-Fredholm section with compact solution set, $f^1$ is an sc-Fredholm section of $P^1$ with compact solution set, and so is $f^2$ of $P^2$; the solution set is compact in every $X_i$.
288. (V5.14) $P^1 : Y_{1,1} \to X^1$ with the index raises of the strong bundle charts is a strong bundle, and for every sc-Fredholm section $f$, $f^1$ is an sc-Fredholm section of it, the filler condition on level $1$ included.
289. (V5.15) $\mathbb R$ with the constant structure is an M-polyfold; sc-smoothness of maps is checked in local charts; $C^\infty$ functions of sc-smooth functions are sc-smooth.
290. (V5.16) Admitting sc-smooth bump functions means a bump with $f(x) \ne 0$ inside every neighbourhood of $x$; Definition 5.29 as written is weaker, follows from the density of such points, and gives them at the smooth points of an sc-Banach space.
291. (V5.17) With bump functions, every $x$ has an sc-smooth $f : X \to [0, 1]$ supported in a given neighbourhood, equal to $1$ near $x$.
292. (V5.18) The zero section, products of sc-smooth functions and sc⁺-sections, and finite sums of sc⁺-sections are sc⁺-sections; sc⁺-sections take values in $Y_{0,1}$.
293. (V5.19) A local sc⁺-section of a chart of the atlas, cut off by an sc-smooth function supported in the chart domain and extended by $0$, is an sc⁺-section.
294. (V5.20) With bump functions and an auxiliary norm, every smooth $e$ over a smooth $x$ is the value at $x$ of an sc⁺-section supported in $U$ with $N(s(y)) < N(e) + \varepsilon$ everywhere.
295. (V5.21) $\Gamma^{+,1}_U(P)$ is the set of sc⁺-sections supported in $U$ with $N \le 1$; $\rho = \sup_xN(s(x) - s'(x))$ is a metric on it, not complete for the trivial bundle over $\mathbb R$, complete for $U = \emptyset$.
296. (V5.22) A section vanishing off an adapted $U$ with $N(s) \le 1$ has the zeros of $f + s$ in $\{x \in U \mid N(f(x)) \le 1\}$, with compact closure; for $s$ in the completion (uniform $N$-limits of allowable sections) the solution set of $f + s$ is closed, hence compact.
297. (V5.23) Transversality to the zero section is surjectivity of the linearization at every zero, in some and then every chart.
298. (V5.24) At a zero of an sc-Fredholm section, finitely many allowable sc⁺-sections supported in a given $U$ span a complement of the range of the linearization.
299. (V5.25) The slices $g + \sum\lambda_it_i$ carry the zeros of $F$, are sc-Fredholm, and stay allowable for $m|\lambda| \le \varepsilon$ when $N(s_0) \le 1 - \varepsilon$.
300. (V5.26) A slice over a parameter where $\ker\mathrm{Lin}_F$ projects onto $\mathbb R^m$ is transversal; spanning sections make $F$ transversal at $(0, y)$, also after adding sections.
301. (V5.27) $\mathbb R^m \times X$ has no boundary if $X$ has none; transversality of $F$ spreads to nearby zeros and gives good position on an open $V \supseteq \{0\} \times S_g$, which contains the zeros over small $\lambda$.
302. (V5.28) Near a zero of $F$ in good position, the slices are transversal at their zeros over all $\lambda$ off a null set.
303. (V5.29) Theorem 5.13: for $\partial X = \emptyset$, $f$ with tame germ data, there is $U$ such that allowable perturbations have compact solution sets and $s_0 + \sum\lambda_it_i$ is transversal with a manifold solution set for small $\lambda$ off a null set.
304. (V5.30) Theorem 5.13, dense form: such good allowable perturbations exist within $\rho$-distance $\varepsilon$ of every allowable $s'$.
305. (V5.31) General position of $(f, y)$: in a tame chart, $\mathrm{Lin}(z)$ onto and its kernel with an sc-complement inside $T^R_zO$, for every presentation.
306. (V5.32) Regular tangent germ data give sc⁺-retractions, so solution sets in good position are smooth finite-dimensional submanifolds (Definition 4.13).
307. (V5.33) Near a zero in good position, the tangent space of the solution set equals $\ker\mathrm{Lin}(z)$ in every chart.
308. (V5.34) Near a zero in good position, general position of $(f, y)$ is general position of the solution set at $y$, and is chart independent.
309. (V5.35) For $X$ tame, general position of $(f, x_0)$ persists at the nearby zeros, with the solution set a submanifold in general position there.
310. (V5.36) Properties (i)–(ii) are general position of $F$ at $(0, y)$, survive added sections, and are achieved by finitely many allowable sections.
311. (V5.37) For $X$ tame, a family with $F$ in general position along $\{0\} \times S_{f+s_0}$ gives, for small $\lambda$ off a null set, $f + s_\lambda$ with all the conclusions of Theorem 5.18.
312. (V5.38) Theorem 5.18, generic form, for $X$ tame with bump functions and $f$ with tame germ data.
313. (V5.39) Theorem 5.18, dense form: perturbations in general position exist within $\rho$-distance $\varepsilon$ of every allowable $s'$.
314. (V5.40) Theorem 5.19: with good position at the boundary zeros, small $\sum\lambda_it_i$ vanishing near $\partial X$ give transversality and good position everywhere, a compact manifold with corners.
315. (V5.41) A generalized compact homotopy is a tame $X$, $f$ with tame germ data and compact solution set, and $t$ onto $[0, 1]$ with tame fibres on which $f$ restricts to sc-Fredholm sections of the pull-backs.
316. (V5.42) Lemma 5.23 is linear algebra, and the one-dimensional complement $Z$ of $\ker dt(x)$ exists iff $dt(x) \ne 0$.
317. (V5.43) The product rule and the affine chain rule hold at level-$1$ points; $\beta \cdot \ell(\varphi(\cdot) - \varphi(x))$ is sc-smooth.
318. (V5.44) Lemma 5.24: for $\mathrm{Lin}_f(z) \circ b$ with values in the line of a smooth $e$, an sc⁺-section vanishing at $x$ with small support cancels it on $K$.
319. (V5.45) Theorem 5.25: for $X$ tame and $f$ proper with tame germ data, some allowable $s$ puts $f + s$ in good position at every zero.
320. (V5.46) Lemma 5.26: general position implies good position, with the interior condition, without tameness of $X$.
321. (V5.47) Admitting sc-smooth partitions of unity: every open cover has a subordinate partition of unity of sc-smooth functions.
322. (V5.48) Sums, products, locally finite sums and chart-supported extensions by $0$ of sc-smooth functions are sc-smooth.
323. (V5.49) Sc-smooth partitions of unity give sc-smooth bump functions.
324. (V5.50) $C^k$-bump functions and $C^k$ partitions of unity of a Banach space are as in the text.
325. (V5.51) The sc-smooth bump function property of a local model, with $f(x) \ne 0$; a retract is closed near each of its points.
326. (V5.52) Theorem 5.34: bump functions on $X$ iff a covering family of charts with the local bump property.
327. (V5.53) A local model on a Hilbert $E_0$ (or a norm dominated by a continuous quadratic form) has the bump property; M-polyfolds on sc-Hilbert spaces admit bump functions.
328. (V5.54) The sc-smooth approximation property of a local model, with $V = O \cap W$ and closures in $E_0$.
329. (V5.55) With sc-smooth partitions of unity, charts restricted to sets with closure in the chart domain have the approximation property.
330. (V5.56) A covering family of charts with the approximation property gives sc-smooth Urysohn functions and sc-smooth partitions of unity.
331. (V5.57) Theorem 5.37: sc-smooth partitions of unity iff a covering family of charts with the approximation property.
332. (V5.58) If $E_0$ admits $C^\infty$ partitions of unity, every local model on $E$ has the approximation property.
333. (V5.59) $c_0(\Gamma)$ and coordinate-wise $C^k$ embeddings are as in the text; Theorem 5.40 is only stated.
334. (V5.60) WCG: a weakly compact set with dense span; reflexive: the bidual map is onto.
335. (V5.61) Reflexive and separable Banach spaces are WCG.
336. (V5.62) Theorem 5.43 is only stated; Hilbert spaces have $C^\infty$-bump functions and are reflexive.
337. (V5.63) Corollary 5.44 holds with Theorem 5.43 for $E_0$ as an explicit hypothesis.
338. (V6.1) At a chart point, $\mathrm{Lin}(f, x)$ is $(f + s)'(x)$ plus the sc⁺-operators; its members are Fredholm on level $0$ of one index, and it is convex and, with sections through $f(x)$, nonempty.
339. (V6.2) $\lambda(E)$ and $\lambda^*(E)$ are lines; wedges change by determinants; $\lambda(\Phi)$ is functorial and nonzero iff $\Phi$ is bijective.
340. (V6.3) $\iota : \lambda(E^*) \to \lambda^*(E)$ is given by $\det(e_i^*(a_j))$ and maps the dual-basis wedge to $(e_1 \wedge \dots \wedge e_n)^*$.
341. (V6.4) $\lambda^*(\Phi) \circ \iota = \iota \circ \lambda(\Phi^*)$ for an isomorphism $\Phi$.
342. (V6.5) $\Phi_E$ of a four-term exact sequence is the isomorphism of lines given by (91) for one choice.
343. (V6.6) Formula (91) holds for every choice.
344. (V6.7) $\Psi_E$ maps the wedge of the basis of $C$, in the order of (91), and $a \otimes d^*$ to the wedge of the basis of $B$.
345. (V6.8) $\det(T) = \lambda(\ker T) \otimes \lambda^*(\operatorname{coker} T)$ is a line for $T$ Fredholm.
346. (V6.9) An orientation of $T$ is a ray of $\det(T)$; there are exactly two.
347. (V6.10) Good left-projections are as in Definition 6.9, $\le$ is a partial order, the remarks after the definition hold, and $\Pi_T \ne \emptyset$ for $T$ Fredholm.
348. (V6.11) Two good left-projections have a common lower bound in $\Pi_T$, for any bounded $T$; the text's candidate need not be one.
349. (V6.12) The sequence $E(T, P)$ is exact.
350. (V6.13) $\gamma^P_T = \Phi_{E(T,P)}$ is an isomorphism $\det(T) \to \det(PT)$ given on wedges by (91).
351. (V6.14) For $P \le Q$, $\gamma^P_{QT} \circ \gamma^Q_T = \gamma^P_T$.
352. (V6.15) $(\gamma^P_{RT})^{-1} \circ \gamma^P_{ST} = \gamma^R_T \circ (\gamma^S_T)^{-1}$ for $P \le S, R$.
353. (V6.16) The stabilization sequence of $T_\varphi$ is exact, and stabilizations exist.
354. (V6.17) $\psi((c_1 \wedge \dots \wedge c_n)^*) = \det[c]^{-1}1^*$.
355. (V6.18) $\iota_\varphi$ is an isomorphism given by the formula of Proposition 6.15, and $m + l = n$ always holds.
356. (V6.19) $T \oplus S$ is Fredholm and $\det(T) \otimes \det(S) \to \det(T \oplus S)$ is the isomorphism given by the formula for every choice.
357. (V6.20) Lemma 6.17 holds, without the hypothesis that $T$ is Fredholm.
358. (V6.21) The kernels $\ker(PS)$ near $T$ are trivialized continuously by $k \mapsto k + y(k, S)$, with continuous inverse.
359. (V6.22) The frames $\omega(S)$ are nowhere zero, and the frames of two charts with the same $P$ differ by a continuous nowhere-zero factor.
360. (V6.23) $\gamma^Q_{PS}$ maps the $P$-frame to a continuous nowhere-zero multiple of the $Q$-frame, for any two charts.
361. (V6.24) The charts $\gamma_{(T,P,\varepsilon)}$, read in frames, form a vector prebundle with fibres $\det(S)$.
362. (V6.25) $\mathcal B$ is the collection of Definition 6.22, read in the frames.
363. (V6.26) $\mathcal B$ is a basis of the topology of $\mathrm{DET}(E, F)$.
364. (V6.27) $\mathrm{DET}(E, F)$ is a topological line bundle, trivialized by the $\gamma_{(T,P,\varepsilon)}$.
365. (V6.28) The transition maps are multiplications by continuous nowhere-zero functions.
366. (V6.29) A line bundle over a nonempty simply connected, locally path-connected base has exactly two orientations.
367. (V6.30) $\mathrm{DET}(E, F)$ over a nonempty convex set of Fredholm operators is a line bundle with exactly two orientations.
368. (V6.31) $\mathrm{Or}^f_x$, the orientations of $\mathrm{DET}(f, x)$, has exactly two elements, each determined by its value at one $L$.
369. (V6.32) Proposition 6.28 holds with (1′) in place of (1), with global sections over $\mathbb R^n \times X$.
370. (V6.33) Finitely many sc⁺-sections put $F$ in general position at all points $(0, (q, \Phi(q)))$, $q$ near $[0, 1]^n$.
371. (V6.34) The kernels of the linearizations along a continuous family of zeros in good position form a continuous family of subspaces.
372. (V6.35) Continuous families of subspaces have determinant line bundles, and orientations are continued along $[0, 1]$.
373. (V6.36) Kernels, images and cuts of continuous families are continuous families, with their orientations.
374. (V6.37) In the product chart the slice kernel is $\ker(T \oplus \varphi)$ with $T \in \mathrm{Lin}(f, x)$, and $T \oplus \varphi$ is onto.
375. (V6.38) The sequence (96) is exact.
376. (V6.39) Continuation and the stabilization isomorphisms compose to a bijection of the rays at the two ends.
377. (V6.40) With the sign $(-1)^{\dim\operatorname{coker}T}$ the orientations carried by $\Phi_E$ along a family are continuous; without it they need not be.
378. (V6.41) The push-forward along stabilized kernels is defined with that sign and is compatible with pull-back and concatenation.
379. (V6.42) With the sections of Lemma 6.29 the stabilized kernels along a family form a continuous family.
380. (V6.43) Push-forwards along sc-smooth paths exist in the sets of Proposition 6.28 and split along halves.
381. (V6.44) Two push-forwards along the same path agree.
382. (V6.45) Appending sections does not change the push-forward.
383. (V6.46) Affine reparametrizations keep sc⁺-sections, and adding sections keeps general position.
384. (V6.47) Push-forwards along the two edges of a square of stabilized kernels with fixed end points agree.
385. (V6.48) Every smooth point has an open neighbourhood on which push-forwards exist and depend only on the end points.
386. (V6.49) Nearby smooth points are joined by sc-smooth paths in a chart, and concatenations are sc-smooth.
387. (V6.50) An orientable neighbourhood (a pair $V \subseteq U$) has exactly two continuous orientations, and every smooth point has one.
388. (V6.51) Reparametrizations of a path are homotopic to it with the end points fixed.
389. (V6.52) The sc-smooth homotopy classes of paths form a groupoid $PX$ on the smooth points.
390. (V6.53) Two chart points at $x$ identify $\mathrm{Lin}(f, x)$ and $\mathrm{Or}^f_x$, with the cocycle rules.
391. (V6.54) Under this identification the local propagations of two charts agree.
392. (V6.55) $\mathrm{Or}^f_x$ read in a chosen chart has two elements and is identified with that of any chart at $x$.
393. (V6.56) Local push-forwards give a transport along paths, homotopy invariant, functorial, and unique.
394. (V6.57) There is exactly one functor $\Gamma_f$ on $PX$ with property (∗).
395. (V6.58) Orientability in the sense of Definition 6.38 is the existence of a family $o_y$ preserved by $\Gamma_f$.
396. (V6.59) Definitions 6.38 and 6.39 are equivalent.
397. (V6.60) Orientations of $f$ are the families preserved by $\Gamma_f$; they exist iff $f$ is orientable, two on each class.
398. (V6.61) For a proper $f$ in general position at its zeros, $S$ is a compact manifold with boundary with corners, and the tangent orientations $o_x$ of $T_xS = \ker f'(x)$ vary continuously along the sc-smooth paths of zeros in a chart.
399. (V6.62) An orientation of $\mathrm{DET}(f, x)$ gives exactly one orientation of $\mathrm{DET}(\hat f, (t, x))$, by $h \mapsto \tilde h$ with the sign $(-1)^{\dim\operatorname{coker}L}$, independent of $L$.
400. (V6.63) The proof of Lemma 6.5 in §6.7.1 goes through, with homogeneity in the bases of $A$ and $D$.
401. (V6.64) The proof of Proposition 6.12 in §6.7.2 goes through, with the spanning proved directly in $F$.
