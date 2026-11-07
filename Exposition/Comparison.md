# Polyfold Theory beside Lean

*Every result of the book beside the statement the machine actually checked. The left column is Hofer, Wysocki and Zehnder, in their own terms, with the numbering and pages of the 2014 preprint (arXiv 1407.3185); the corresponding numbers and pages of the book’s arXiv version (1707.08941) are in Exposition/BookConcordance.md (the Springer edition is not checked). The right column is the formal statement, with the hypotheses the text leaves to the reader written out. Click a declaration to see the Lean it names.*

Left: the statement as the book states it. Right: the statement proved in Lean, with the hypotheses written out. Each declaration is given with its file and line.

## Chapter 1

*HWZ Chapter 1 §§1.1–1.4, preprint pp. 6–17: sc-Banach spaces, sc-operators, sc-Fredholm operators, sc-differentiability, the chain rule, the degeneracy index*

### V1.1. Sc-structures, sc-Banach spaces, sums and level shifts

*restated* · indexed family, not nested subspaces · injectivity of the inclusions a field · only one structure in finite dim. (V1.31)

**HWZ (§1.1, Definition 1.1, p. 6).** An *sc-structure* on a Banach space $E$ is a decreasing sequence of Banach spaces $E = E_0 \supset E_1 \supset E_2 \supset \cdots$ such that (1) every inclusion $E_{m+1} \to E_m$ is compact and (2) $E_\infty = \bigcap_m E_m$ is dense in every $E_m$. A Banach space with an sc-structure is an *sc-Banach space*; points of $E_\infty$ are *smooth*, points of $E_m$ have *regularity $m$*. A finite-dimensional space has exactly one sc-structure, the constant one. A subset $A$ inherits the filtration $A_m = A \cap E_m$, and $A^k$ is $A_k$ with the filtration $(A^k)_m = A_{k+m}$. The direct sum $E \oplus F$ has levels $E_m \oplus F_m$.

*Example 1.2, the weighted Sobolev spaces $H^{m,\delta_m}(\mathbb R \times S^1)$, is not formalized (G.1).*

**Proved in Lean.** A *scale* is an indexed family of real Banach spaces $E_m$, $m \in \mathbb N$, with injective compact continuous linear inclusions $E_{m+1} \to E_m$; the composite $E_m \to E_0$ is written $\iota_m$, and $E_\infty \subseteq E_0$ is the subspace of points that lift to every level, $E_\infty \cap E_m$ its preimage in $E_m$. An *sc-Banach space* is a scale in which $E_\infty \cap E_m$ is dense in $E_m$ for every $m$; then the image of $E_{m+k}$ is dense in $E_m$. For a finite-dimensional space $V$ the constant family $E_m = V$ with identity inclusions is an sc-Banach space, all of whose points are smooth. For sc-Banach spaces $E$, $F$ the family $E_m \times F_m$ with the product inclusions is an sc-Banach space $E \oplus F$, whose smooth points are the pairs of smooth points; the family $E_{m+1}$ is an sc-Banach space $E^1$, with smooth points those of $E$ seen in $E_1$, and $E^k$ is the $k$-fold iterate. For $U \subseteq E_0$ the level set $U_m \subseteq E_m$ is the preimage of $U$ under $\iota_m$.

- `Polyfold.ScScale` — Polyfold/Chapter1/ScBanach.lean, line 84
- `Polyfold.ScScale.toBase` — Polyfold/Chapter1/ScBanach.lean, line 104
- `Polyfold.ScScale.smooth` — Polyfold/Chapter1/ScBanach.lean, line 135
- `Polyfold.ScScale.smoothLvl` — Polyfold/Chapter1/ScBanach.lean, line 141
- `Polyfold.ScBanach` — Polyfold/Chapter1/ScBanach.lean, line 171
- `Polyfold.ScBanach.denseRange_inclK` — Polyfold/Chapter1/ScBanach.lean, line 181
- `Polyfold.ScBanach.const` — Polyfold/Chapter1/ScBanach.lean, line 213
- `Polyfold.ScBanach.constScale_smoothLvl` — Polyfold/Chapter1/ScBanach.lean, line 206
- `Polyfold.ScBanach.prod` — Polyfold/Chapter1/ScBanach.lean, line 267
- `Polyfold.ScBanach.prod_smoothLvl` — Polyfold/Chapter1/ScBanach.lean, line 279
- `Polyfold.ScBanach.shift` — Polyfold/Chapter1/ScBanach.lean, line 315
- `Polyfold.ScBanach.shift_smoothLvl` — Polyfold/Chapter1/ScBanach.lean, line 326
- `Polyfold.ScBanach.shiftK` — Polyfold/Chapter1/ScBanach.lean, line 330
- `Polyfold.ScBanach.lvlSet` — Polyfold/Chapter1/ScSmooth.lean, line 72

*What differs.*
- The text's $E_m$ are subsets of one space $E$; the formal scale is a family of separate Banach spaces with injective compact inclusions, and "$x \in E_m$" for $x \in E_0$ means $x \in \iota_m(E_m)$. The two pictures are equivalent, and nothing in Chapter 1 uses more than the family.
- Injectivity of the inclusions, implicit in "$E_{m+1} \subset E_m$", is a field of the structure; continuity is part of being a compact operator in Mathlib's sense.
- Condition (2) is taken exactly as stated, density of $E_\infty \cap E_m$ in every $E_m$. The weaker "$E_{m+1}$ is dense in $E_m$" is derived, not assumed.
- That a finite-dimensional space has *only* the constant structure, and that the constant sequence on an infinite-dimensional space is not an sc-structure, are proved separately (V1.31).

### V1.2. Sc-operators and sc-isomorphisms

*restated* · the level maps are the data · `IsScOperator` is the text's form · continuity on the levels is automatic

**HWZ (§1.1, Definition 1.3, p. 7).** A linear map $T : E \to F$ between sc-Banach spaces is an *sc-operator* if $T(E_m) \subset F_m$ and the induced $T : E_m \to F_m$ is continuous for every $m$. A *linear sc-isomorphism* is a bijective sc-operator whose inverse is an sc-operator.

**Proved in Lean.** An *sc-operator* $T : E \to F$ is a family of continuous linear maps $T_m : E_m \to F_m$ commuting with the inclusions, $\iota^F_m \circ T_{m+1} = T_m \circ \iota^E_m$. The family is determined by its base map $T_0$, and a continuous linear $T_0 : E_0 \to F_0$ *is an sc-operator* when for every $m$ there is a continuous linear $T_m : E_m \to F_m$ with $\iota_m T_m = T_0 \iota_m$; the two notions correspond. Sc-operators compose and add, and map smooth points to smooth points. An *sc-isomorphism* is a family of continuous linear equivalences $E_m \simeq F_m$ commuting with the inclusions; its inverse and composites are sc-isomorphisms. A continuous linear $T_0 : E_0 \to F_0$ with $T_0(E_m) \subseteq F_m$ for every $m$ is an sc-operator (the continuity of $T_0 : E_m \to F_m$ is the closed graph theorem), and an sc-operator bijective on every level is an sc-isomorphism (the open mapping theorem).

- `Polyfold.ScOperator` — Polyfold/Chapter1/ScBanach.lean, line 341
- `Polyfold.ScOperator.ext_base` — Polyfold/Chapter1/ScBanach.lean, line 359
- `Polyfold.IsScOperator` — Polyfold/Chapter1/ScBanach.lean, line 405
- `Polyfold.ScOperator.isScOperator` — Polyfold/Chapter1/ScBanach.lean, line 408
- `Polyfold.IsScOperator.toScOperator` — Polyfold/Chapter1/ScBanach.lean, line 412
- `Polyfold.ScOperator.comp` — Polyfold/Chapter1/ScBanach.lean, line 375
- `Polyfold.ScOperator.mapsTo_smoothLvl` — Polyfold/Chapter1/ScBanach.lean, line 393
- `Polyfold.ScIso` — Polyfold/Chapter1/ScBanach.lean, line 429
- `Polyfold.ScIso.symm` — Polyfold/Chapter1/ScBanach.lean, line 449
- `Polyfold.ScIso.trans` — Polyfold/Chapter1/ScBanach.lean, line 459
- `Polyfold.isScOperator_of_mapsTo` — Polyfold/Chapter1/ScFredholmCriterion.lean, line 228
- `Polyfold.ScIso.ofBijective` — Polyfold/Chapter3/LinearizationChartsSc.lean, line 204

*What differs.*
- In the family picture an sc-operator carries its level maps as data; the text's "one linear map $T$ mapping $E_m$ into $F_m$ continuously" is the predicate `IsScOperator` on the base map, and the two are interchangeable (`ScOperator.isScOperator`, `IsScOperator.toScOperator`).
- An sc-isomorphism is given by level-wise continuous linear equivalences; that the inverse of a bijective sc-operator is continuous on each level (the open mapping theorem) is built into this definition, and proved separately (`ScIso.ofBijective`). Likewise the continuity of $T : E_m \to F_m$ asked by Definition 1.3 is automatic for a bounded $T_0$ that maps $E_m$ into $F_m$ (`isScOperator_of_mapsTo`, the closed graph theorem; Findings, Chapter 3, item 233). Updated in the third addendum of this page.

### V1.3. Sc⁺-operators are sc-compact

*as in the book* · the first condition is the second · sc-compactness proved

**HWZ (§1.1, Definition 1.4, p. 7).** An sc-operator $S : E \to F$ is an *$\mathrm{sc}^+$-operator* if $S(E_m) \subset F_{m+1}$ and $S : E \to F^1$ is an sc-operator. Since the inclusion $F_{m+1} \to F_m$ is compact, an $\mathrm{sc}^+$-operator is *sc-compact*: $S : E_m \to F_m$ is compact for every $m$.

**Proved in Lean.** An *$\mathrm{sc}^+$-operator* $E \to F$ is an sc-operator $E \to F^1$ into the level shift, i.e. a family of continuous linear maps $S_m : E_m \to F_{m+1}$ commuting with the inclusions. Composing with the inclusion $F^1 \to F$ (itself an sc-operator) gives the underlying sc-operator $E \to F$, whose level-$m$ map $E_m \to F_m$ is a compact operator for every $m$; in particular $S$ raises the level, $x \in \iota_m(E_m) \Rightarrow S_0x \in \iota_{m+1}(F_{m+1})$.

- `Polyfold.ScPlus` — Polyfold/Chapter1/ScBanach.lean, line 479
- `Polyfold.ScBanach.shiftIncl` — Polyfold/Chapter1/ScBanach.lean, line 484
- `Polyfold.ScPlus.toScOperator` — Polyfold/Chapter1/ScBanach.lean, line 495
- `Polyfold.ScPlus.isCompactOperator` — Polyfold/Chapter1/ScBanach.lean, line 501
- `Polyfold.ScPlus.toScOperator_mem_range_toBase_succ` — Polyfold/Chapter1/ScFredholm.lean, line 89

*What differs.*
- Of the text's two conditions, "$S(E_m) \subset F_{m+1}$" is contained in "$S : E \to F^1$ is an sc-operator", so the formal definition keeps the latter alone; the text's remark that $S$ is then sc-compact is a proved lemma.

### V1.4. Sc-subspaces, sc-complements, sc-splittings

*restated* · compactness of $F_{m+1} \to F_m$ automatic · topological sum from `IsCompl` + closedness

**HWZ (§1.1, Definition 1.5, p. 7).** A subspace $F$ of an sc-Banach space $E$ is an *sc-subspace* if $F$ is closed and $F_m = F \cap E_m$ defines an sc-structure on $F$. An sc-subspace $F$ has an *sc-complement* if there is an algebraic complement $G$ such that $G_m = G \cap E_m$ is an sc-structure on $G$ and $E_m = F_m \oplus G_m$ is a topological direct sum on every level; $E = F \oplus G$ is then an *sc-splitting*.

**Proved in Lean.** For a subspace $A \subseteq E_0$ its level-$m$ part $A_m \subseteq E_m$ is the preimage of $A$ under $\iota_m$; it is closed when $A$ is. $A$ is an *sc-subspace* if $A$ is closed and, for every $m$, $A_m$ lies in the closure of $A_m \cap E_\infty$ (the smooth points of $A$ are dense in every level). A closed $A$ with the induced filtration is a scale, with the restricted inclusions compact, and an sc-subspace is an sc-Banach space with this filtration. $E = F \oplus G$ is an *sc-splitting* if $F$ and $G$ are sc-subspaces and $F_m$, $G_m$ are complementary subspaces of $E_m$ for every $m$; then $F_m$ is closed complemented in $E_m$ (the sum is topological), and the splitting is symmetric.

- `Polyfold.ScBanach.levelSub` — Polyfold/Chapter1/ScBanach.lean, line 513
- `Polyfold.ScBanach.isClosed_levelSub` — Polyfold/Chapter1/ScBanach.lean, line 525
- `Polyfold.ScBanach.IsScSubspace` — Polyfold/Chapter1/ScBanach.lean, line 531
- `Polyfold.ScBanach.ofSubspaceScale` — Polyfold/Chapter1/ScBanach.lean, line 539
- `Polyfold.ScBanach.ofSubspace` — Polyfold/Chapter1/ScBanach.lean, line 584
- `Polyfold.ScBanach.IsScSplitting` — Polyfold/Chapter1/ScBanach.lean, line 598
- `Polyfold.ScBanach.IsScSplitting.closedComplemented` — Polyfold/Chapter1/ScBanach.lean, line 601
- `Polyfold.ScBanach.IsScSplitting.symm` — Polyfold/Chapter1/ScBanach.lean, line 606

*What differs.*
- Of the conditions in "$(F_m)$ is an sc-structure on $F$", the closedness of $F_m$ in $E_m$ and the compactness of $F_{m+1} \to F_m$ follow from the closedness of $F$ (restriction of a compact operator), so `IsScSubspace` asks only for closedness and the density of $F \cap E_\infty$ in each $F_m$; the sc-Banach space $F$ is then built (`ScBanach.ofSubspace`).
- "Topological direct sum $E_m = F_m \oplus G_m$" is read as: $F_m$ and $G_m$ are complementary closed subspaces of $E_m$; by the closed graph theorem the sum is then topological, which is recorded as a consequence (`IsScSplitting.closedComplemented`). The text's "$G$ an algebraic complement with $(G_m)$ an sc-structure" is the requirement that $G$ be an sc-subspace.

### V1.5. Finite-dimensional sc-subspaces

*as in the book* · proof: a continuous projection onto $F$

**HWZ (§1.1, Proposition 1.6, p. 7).** A finite-dimensional subspace $F$ of an sc-Banach space $E$ is an sc-subspace if and only if $F \subset E_\infty$. A finite-dimensional sc-subspace always has an sc-complement.

**Proved in Lean.** Let $E$ be an sc-Banach space and $F \subseteq E_0$ a finite-dimensional subspace. Then $F$ is an sc-subspace if and only if $F \le E_\infty$. If $F \le E_\infty$, there is a subspace $G \subseteq E_0$ with $E = F \oplus G$ an sc-splitting.

- `Polyfold.ScBanach.proposition_1_6_iff` — Polyfold/Chapter1/ScBanach.lean, line 613
- `Polyfold.ScBanach.proposition_1_6` — Polyfold/Chapter1/ScBanach.lean, line 680

*What differs.*
- The proof follows the text: a continuous projection $p : E_0 \to F$ (Mathlib's closed complementation of finite-dimensional subspaces, i.e. Hahn–Banach) is lifted to each level through $F_m \cong F$, $G = \ker p$, and the density of $G \cap E_\infty$ in $G_m$ comes from $g = (1 - P_m)g$ with $P_m$ the level projection, exactly as on p. 8.

### V1.6. Quotients of sc-Banach spaces

*stronger* · any closed $A$, not only sc-subspaces · $(E/A)_\infty$ identified in V1.33

**HWZ (§1.1, Proposition 1.7, p. 8).** If $E$ is an sc-Banach space and $A \subset E$ an sc-subspace, then $E/A$ with the filtration $E_m/A_m$ is an sc-Banach space, where $E_m/A_m = \{(x + A) \cap E_m : x \in E\}$.

**Proved in Lean.** Let $E$ be an sc-Banach space and $A \subseteq E_0$ a *closed* subspace. The family of quotient Banach spaces $E_m / A_m$, with the inclusions $E_{m+1}/A_{m+1} \to E_m/A_m$ induced by $\iota$, is an sc-Banach space $E/A$ (the induced maps are injective and compact, and the smooth points are dense on every level), and the quotient maps $E_m \to E_m/A_m$ form an sc-operator $E \to E/A$. As a statement: there are an sc-Banach space $Q$ and an sc-operator $q : E \to Q$ with every $q_m$ surjective and $\ker q_m = A_m$.

- `Polyfold.ScBanach.quotientScale` — Polyfold/Chapter1/ScBanach.lean, line 752
- `Polyfold.ScBanach.quotient` — Polyfold/Chapter1/ScBanach.lean, line 768
- `Polyfold.ScBanach.quotientMap` — Polyfold/Chapter1/ScBanach.lean, line 781
- `Polyfold.ScBanach.proposition_1_7` — Polyfold/Chapter1/ScBanach.lean, line 787

*What differs.*
- The text assumes $A$ is an sc-subspace; the proof uses only that $A$ is closed, and so does the formal statement (`ScBanach.quotient` takes `IsClosed A`).
- The levels $E_m/A_m$ are the abstract quotients; the text's identification of $E_m/A_m$ with a subset of $E/A$ is the injectivity of the induced inclusion, which holds because $A_m$ is the full preimage of $A$.
- The text's description of $(E/A)_\infty$ as the classes of points of $E_\infty$ (p. 9) is proved separately, with the Mittag-Leffler argument it needs (V1.33).

### V1.7. Sc-Fredholm operators and their index

*restated* · (3) read as bijections $X_m \to Y_m$ · index independent of the splitting · Fredholm on every level

**HWZ (§1.1, Definition 1.8, p. 9).** An sc-operator $T : E \to F$ is *sc-Fredholm* if there are sc-splittings $E = K \oplus X$ and $F = C \oplus Y$ with (1) $K = \ker T$ finite-dimensional, (2) $C$ finite-dimensional and $Y = T(E)$, (3) $T : X \to Y$ an sc-isomorphism. Then $K \subset E_\infty$, $T(X_m) = Y_m$, $E_m = K \oplus X_m$ and $F = C \oplus T(E_m)$. The index is $\operatorname{ind}(T) = \dim K - \dim C$.

**Proved in Lean.** An *sc-Fredholm splitting* of an sc-operator $T : E \to F$ consists of subspaces $K, X \subseteq E_0$ and $C, Y \subseteq F_0$ with $E = K \oplus X$ and $F = C \oplus Y$ sc-splittings, $K = \ker T_0$, $Y = \operatorname{range} T_0$, $K$ and $C$ finite-dimensional, and $T_m$ a bijection of $X_m$ onto $Y_m$ for every $m$. $T$ is *sc-Fredholm* if it has such a splitting. Its *index* $\dim K - \dim C$ equals $\dim \ker T_0 - \dim(F_0/\operatorname{range} T_0)$, so it does not depend on the splitting. Consequences: $K \le E_\infty$; $\ker T_m = K_m$ and $\operatorname{range} T_m = Y_m$ on every level; and every $T_m : E_m \to F_m$ is a Fredholm operator in Mathlib's sense.

- `Polyfold.ScFredholmSplitting` — Polyfold/Chapter1/ScFredholm.lean, line 106
- `Polyfold.IsScFredholm` — Polyfold/Chapter1/ScFredholm.lean, line 124
- `Polyfold.ScFredholmSplitting.index` — Polyfold/Chapter1/ScFredholm.lean, line 127
- `Polyfold.scIndex` — Polyfold/Chapter1/ScFredholm.lean, line 131
- `Polyfold.ScFredholmSplitting.index_eq` — Polyfold/Chapter1/ScFredholm.lean, line 140
- `Polyfold.ScFredholmSplitting.K_le_smooth` — Polyfold/Chapter1/ScFredholm.lean, line 148
- `Polyfold.ScFredholmSplitting.ker_lvl` — Polyfold/Chapter1/ScFredholm.lean, line 152
- `Polyfold.ScFredholmSplitting.range_lvl` — Polyfold/Chapter1/ScFredholm.lean, line 155
- `Polyfold.ScFredholmSplitting.isFredholm` — Polyfold/Chapter1/ScFredholm.lean, line 161

*What differs.*
- Condition (3), "$T : X \to Y$ is an sc-isomorphism", is taken as: $T_m$ restricts to a bijection $X_m \to Y_m$ for every $m$. The continuity of the inverses is automatic (open mapping theorem between the closed subspaces $X_m$, $Y_m$), so nothing is lost.
- The text's "$F = C \oplus T(E_m)$" (a slip for $F_m$) is the level-$m$ part of the splitting $F = C \oplus Y$ together with $\operatorname{range} T_m = Y_m$.
- The index is defined by the splitting as in the text and shown equal to $\dim\ker T_0 - \dim\operatorname{coker} T_0$, which the text does not state; the level-wise Fredholm property, the first line of §1.4.1, is a lemma.

### V1.8. Sc-Fredholm operators are regularizing

*as in the book* · the text's proof · converse: $T_0$ Fredholm and regularizing

**HWZ (§1.1, Proposition 1.9, p. 9).** An sc-Fredholm operator $T : E \to F$ is regularizing: if $e \in E$ and $T(e) \in F_m$, then $e \in E_m$.

**Proved in Lean.** Let $T : E \to F$ be an sc-operator with an sc-Fredholm splitting, $e \in E_0$ and $m \in \mathbb N$. If $T_0 e \in \iota_m(F_m)$, then $e \in \iota_m(E_m)$. As a property: an sc-Fredholm operator is *regularizing* (`ScOperator.IsRegularizing`). Conversely, an sc-operator $T$ with $T_0$ Fredholm and $T$ regularizing is sc-Fredholm (V1.9); so $T$ is sc-Fredholm if and only if $T_0 : E_0 \to F_0$ is Fredholm and $T$ is regularizing.

- `Polyfold.proposition_1_9` — Polyfold/Chapter1/ScFredholm.lean, line 184
- `Polyfold.ScOperator.IsRegularizing` — Polyfold/Chapter1/ScFredholmCriterion.lean, line 69
- `Polyfold.IsScFredholm.isRegularizing` — Polyfold/Chapter1/ScFredholmCriterion.lean, line 92
- `Polyfold.isScFredholm_iff` — Polyfold/Chapter1/ScFredholmCriterion.lean, line 217

*What differs.*
- The hypothesis is the data of Definition 1.8 (a splitting) rather than its existence; the two are interchangeable, since the conclusion does not mention the splitting.
- The converse, not stated in the text: together with “$T_0$ Fredholm”, being regularizing characterizes the sc-Fredholm operators (`isScFredholm_iff`). It is the construction of §1.4.1 with the two properties used there as hypotheses (V1.9), and the tool for the text's unargued “is sc-Fredholm” for operators obtained by conjugation and restriction in Chapter 3 (V3.8, V3.46, V3.96; Findings, Chapter 3, item 233). Updated in the third addendum of this page.

### V1.9. Compact perturbation of sc-Fredholm operators

*as in the book* · needs a bootstrap the text omits · index preserved: V1.30 · the construction as a criterion (V1.8)

**HWZ (§1.1, Proposition 1.10, p. 10 (proof §1.4.1, pp. 14–15)).** Let $E$ and $F$ be sc-Banach spaces. If $T : E \to F$ is sc-Fredholm and $S : E \to F$ is an $\mathrm{sc}^+$-operator, then $T + S$ is sc-Fredholm.

**Proved in Lean.** Let $T : E \to F$ be an sc-Fredholm operator and $S : E \to F$ an $\mathrm{sc}^+$-operator. Then the sc-operator $T + S$ (with $S$ read as an sc-operator $E \to F$) is sc-Fredholm. Along the way: $T + S$ is regularizing, and every level map $(T+S)_m$ is a Fredholm operator. The construction is also proved as a criterion: an sc-operator that is Fredholm on level $0$ and regularizing is sc-Fredholm, and every level map is then Fredholm of the level-$0$ index.

- `Polyfold.proposition_1_10` — Polyfold/Chapter1/ScFredholm.lean, line 226
- `Polyfold.ScPlus.regularizing_add` — Polyfold/Chapter1/ScFredholm.lean, line 208
- `Polyfold.isScFredholm_of_isRegularizing` — Polyfold/Chapter1/ScFredholmCriterion.lean, line 105
- `Polyfold.isScFredholm_of_isRegularizing_index` — Polyfold/Chapter1/ScFredholmCriterion.lean, line 210

*What differs.*
- §1.4.1 says "since $T$ is regularizing, $e \in E_m$"; the hypothesis gives only $Te = y - Se \in F_1$, so the regularizing step must be iterated $m$ times (`ScPlus.regularizing_add`). The same bootstrap gives $K_m = K_{m+1}$.
- The complement $C$ is built from a linear right inverse of $F_0 \to F_0/Y$ with values in the smooth points rather than from a lifted basis; condition (3) of Definition 1.8, which the text does not verify, is proved as the bijectivity of $(T+S)_m : X_m \to Y_m$.
- The classical fact that opens §1.4.1, a compact perturbation of a Fredholm operator is Fredholm, is not in Mathlib and is proved here (V1.25). The text does not record that the index is preserved; the formalization proves it separately (V1.30).
- §1.4.1 uses two properties of $T + S$ only: it is Fredholm on level $0$, and it is regularizing (so its kernel lies in $E_\infty$, it maps $E_m$ onto $Y \cap F_m$, and its range has a complement spanned by smooth points). With these as hypotheses the construction is a criterion for sc-Fredholm operators (`isScFredholm_of_isRegularizing`), not stated in the text (Findings, Chapter 3, item 233). Updated in the third addendum of this page.

### V1.10. Partial quadrants and the tuples $(U, C, E)$

*as in the book* · closed and convex derived, not assumed · $C^1$ a partial quadrant in $E^1$: V1.36

**HWZ (§1.1, Definition 1.11, p. 10).** A *partial quadrant* in an sc-Banach space $E$ is a closed convex subset $C \subset E$ such that there is an sc-isomorphism $T : E \to \mathbb R^n \oplus W$ with $T(C) = [0,\infty)^n \oplus W$. One considers tuples $(U, C, E)$ with $U$ a relatively open subset of the partial quadrant $C$.

**Proved in Lean.** The *quadrant* of $\mathbb R^n \oplus W$ (with $\mathbb R^n$ carrying its constant structure) is, on every level, the set of $(a, w)$ with all $a_i \ge 0$; it is closed and convex with non-empty interior, and its level sets are the quadrants of the levels. $C \subseteq E_0$ is a *partial quadrant* if $C = T_0^{-1}(\text{quadrant})$ for some $n$, some sc-Banach space $W$ and some sc-isomorphism $T : E \to \mathbb R^n \oplus W$. Then every level set $C_m$ is closed and convex with non-empty interior in $E_m$ and has unique differentiability at each of its points; the whole space is a partial quadrant ($n = 0$). $(U, C, E)$ is a *tuple* if $C$ is a partial quadrant and $U = O \cap C$ for an open $O \subseteq E_0$.

- `Polyfold.quadrant` — Polyfold/Chapter1/ScSmooth.lean, line 394
- `Polyfold.quadrant_convex` — Polyfold/Chapter1/ScSmooth.lean, line 397
- `Polyfold.quadrant_isClosed` — Polyfold/Chapter1/ScSmooth.lean, line 401
- `Polyfold.lvlSet_quadrant` — Polyfold/Chapter1/ScSmooth.lean, line 418
- `Polyfold.IsPartialQuadrant` — Polyfold/Chapter1/ScSmooth.lean, line 427
- `Polyfold.IsPartialQuadrant.convex` — Polyfold/Chapter1/ScSmooth.lean, line 458
- `Polyfold.IsPartialQuadrant.isClosed` — Polyfold/Chapter1/ScSmooth.lean, line 460
- `Polyfold.IsPartialQuadrant.uniqueDiffWithinAt_lvlSet` — Polyfold/Chapter1/ScSmooth.lean, line 462
- `Polyfold.isPartialQuadrant_univ` — Polyfold/Chapter1/ScSmooth.lean, line 469
- `Polyfold.IsRelOpenInQuadrant` — Polyfold/Chapter1/ScSmooth.lean, line 478

*What differs.*
- "Closed convex" is a consequence of $C = T^{-1}([0,\infty)^n \oplus W)$ and is proved rather than assumed; since $T_0$ is a bijection, $T(C) = Q$ and $C = T^{-1}(Q)$ say the same.
- The text uses constantly, without stating it, that $C_k$ is a partial quadrant in $E^k$ (so that $TC = C^1 \oplus E$ makes sense); this is proved with Chapter 2 (V1.36). What the proofs of §§1.2–1.3 need from the tuple is carried by the level-wise notion of an sc-domain (V1.27).

### V1.11. Sc⁰ maps

*restated* · total maps $E_0 \to F_0$ · target enters only as $f(U) \subseteq U'$ · the text's $V$ is $U'$

**HWZ (§1.1, Definition 1.12, p. 10).** For tuples $(U, C, E)$ and $(U', C', E')$, a map $f : U \to U'$ is *$\mathrm{sc}^0$* (sc-continuous) if $f(U_m) \subset U'_m$ and the induced maps $f : U_m \to U'_m$ are continuous for all $m \ge 0$.

**Proved in Lean.** For $f : E_0 \to F_0$ the level map $f_m : E_m \to F_m$ sends $x$ to the unique $y$ with $\iota_m y = f(\iota_m x)$ when it exists (a junk value otherwise). $f$ is *$\mathrm{sc}^0$ on $U \subseteq E_0$* if for every $m$ and every $x \in U_m$, $f(\iota_m x) \in \iota_m(F_m)$, and $f_m$ is continuous on $U_m$. Then $f$ is continuous on $U$; if moreover $f(U) \subseteq V$ then $f_m(U_m) \subseteq V_m$; $\mathrm{sc}^0$ depends only on the values of $f$ on $U$, passes to subsets, and the composition of $\mathrm{sc}^0$ maps is $\mathrm{sc}^0$. The identity and every sc-operator are $\mathrm{sc}^0$, with level maps the $T_m$.

- `Polyfold.levelMap` — Polyfold/Chapter1/ScSmooth.lean, line 147
- `Polyfold.IsSc0` — Polyfold/Chapter1/ScSmooth.lean, line 164
- `Polyfold.IsSc0.levelMap_mapsTo` — Polyfold/Chapter1/ScSmooth.lean, line 176
- `Polyfold.IsSc0.continuousOn_base` — Polyfold/Chapter1/ScSmooth.lean, line 181
- `Polyfold.IsSc0.congr` — Polyfold/Chapter1/ScSmooth.lean, line 194
- `Polyfold.IsSc0.comp` — Polyfold/Chapter1/ScSmooth.lean, line 206
- `Polyfold.isSc0_id` — Polyfold/Chapter1/ScSmooth.lean, line 218
- `Polyfold.ScOperator.isSc0` — Polyfold/Chapter1/ScSmooth.lean, line 223

*What differs.*
- Maps are total functions $E_0 \to F_0$ and only their values on $U$ matter; the target tuple plays no role in the definition beyond $f(U) \subseteq U'$, so it is not an argument of `IsSc0` (the text's own definition writes "$f(U_m) \subset V_m$" with $V$ meaning $U'$).
- The level map $f_m$ is defined through the injectivity of $\iota_m$, and the condition "$f(U_m) \subset F_m$" is the first field of `IsSc0`.

### V1.12. The tangent of a tuple

*as in the book* · $TC$ a partial quadrant in $TE$: V1.36 · sc-domains propagate instead

**HWZ (§1.1, Definition 1.13, p. 10).** The *tangent* of $(U, C, E)$ is the tuple $T(U, C, E) = (TU, TC, TE)$ with $TU = U^1 \oplus E$, $TC = C^1 \oplus E$, $TE = E^1 \oplus E$. It is again a tuple: $TU$ is relatively open in the partial quadrant $TC$ of the sc-Banach space $TE$.

**Proved in Lean.** The *tangent* $TE$ of an sc-Banach space is $E^1 \oplus E$, the sc-Banach space with levels $E_{m+1} \times E_m$; for $U \subseteq E_0$, $TU \subseteq (TE)_0 = E_1 \times E_0$ is the set of $(x, h)$ with $x \in U_1$, and its level-$m$ part is $U_{m+1} \times E_m$. $TU$ is monotone in $U$. If $U$ is an sc-domain (open-in-convex levels with unique differentiability, V1.27) so is $TU$ in $TE$, and $T(U^1) = (TU)^1$.

- `Polyfold.ScBanach.tangent` — Polyfold/Chapter1/ScSmooth.lean, line 104
- `Polyfold.ScBanach.tangentSet` — Polyfold/Chapter1/ScSmooth.lean, line 116
- `Polyfold.ScBanach.lvlSet_tangentSet` — Polyfold/Chapter1/ScSmooth.lean, line 132
- `Polyfold.IsScDomain.tangentSet` — Polyfold/Chapter1/ScSmooth.lean, line 504
- `Polyfold.ScBanach.shift_tangentSet` — Polyfold/Chapter1/Levels.lean, line 320

*What differs.*
- $TU$ and $TE$ are the text's. That $TC = C^1 \oplus E$ is a partial quadrant in $TE$, i.e. that $T(U, C, E)$ is again a tuple (which needs an sc-isomorphism $(\mathbb R^n \oplus W)^1 \oplus (\mathbb R^n \oplus W) \cong \mathbb R^n \oplus W'$), is proved with Chapter 2 (V1.36). The proofs of §§1.2–1.3 carry instead the level-wise regularity `IsScDomain`, which $T$ preserves, and this is all the chain rule and §1.2 need.

### V1.13. Sc¹ maps and the tangent map

*hypotheses explicit* · the family $Df$ is explicit · uniqueness of $Df(x)$ proved · finite dim. and compact-open: V1.34–V1.35 · not norm continuous: a $c_0$ example

**HWZ (§1.1, Definition 1.14, pp. 10–11).** $f : U \to U'$ is *$\mathrm{sc}^1$* if (1) $f$ is $\mathrm{sc}^0$; (2) for every $x \in U_1$ there is a bounded linear $Df(x) : E_0 \to F_0$ with $|f(x+h) - f(x) - Df(x)h|_0 / |h|_1 \to 0$ as $|h|_1 \to 0$, $h \in E_1$, $x + h \in U_1$; (3) the *tangent map* $Tf : TU \to TU'$, $Tf(x, h) = (f(x), Df(x)h)$, is $\mathrm{sc}^0$. In general $x \mapsto Df(x)$ is not continuous into $\mathcal L(E_0, F_0)$ with the operator norm, but it is with the compact-open topology; the $\mathrm{sc}^1$ maps between finite-dimensional spaces are the $C^1$ maps.

*The text writes $Df(x)$ as if it were unique.*

**Proved in Lean.** For a family $D : E_1 \to \mathcal L(E_0, F_0)$ the tangent map $T_Df : TE \to TF$ is $(x, h) \mapsto (f_1(x), D(x)h)$. $f$ is *$\mathrm{sc}^1$ on $U$ with derivatives $D$* if (1) $f$ is $\mathrm{sc}^0$ on $U$; (2) for every $x \in U_1$ the map $f \circ \iota_1 : E_1 \to F_0$ has derivative $D(x) \circ \iota_1$ at $x$ within $U_1$ (Mathlib's `HasFDerivWithinAt`); (3) $T_Df$ is $\mathrm{sc}^0$ on $TU$. $f$ is *$\mathrm{sc}^1$ on $U$* if such a $D$ exists; `scDeriv` is a chosen one, and `tangentMap` the tangent map built from it. If $U_1$ has unique differentiability at $x \in U_1$, any two derivative families satisfying (2) agree at $x$ (the inclusion $E_1 \to E_0$ has dense range); on an sc-domain the chosen derivative therefore agrees with any admissible one on $U_1$, and the tangent map on $TU$. Being $\mathrm{sc}^1$ depends only on the values on $U$. Level $0$ of (3) says $(x, h) \mapsto D(x)h$ is continuous on $U_1 \times E_0$, and this gives uniform continuity of $D$ on compact subsets of $E_0$; for maps between finite-dimensional spaces on an open set, $\mathrm{sc}^1$ is $C^1$. The derivative need not be norm continuous: on $E = \mathbb R \oplus X$, with $X$ the sc-Banach space whose level $m$ consists of the sequences with $(k+1)^m x_k \to 0$, normed by $\sup_k (k+1)^m|x_k|$, the map $f(t, x)_k = \cos(kt)x_k$ is $\mathrm{sc}^1$ into $X$, and for every derivative family $D$ of $f$, $x \mapsto D(x)$ is not continuous on $E_1$ into $\mathcal L(E_0, X_0)$ with the operator norm.

- `Polyfold.tangentMapWith` — Polyfold/Chapter1/ScSmooth.lean, line 234
- `Polyfold.IsSc1With` — Polyfold/Chapter1/ScSmooth.lean, line 241
- `Polyfold.IsSc1` — Polyfold/Chapter1/ScSmooth.lean, line 249
- `Polyfold.scDeriv` — Polyfold/Chapter1/ScSmooth.lean, line 253
- `Polyfold.tangentMap` — Polyfold/Chapter1/ScSmooth.lean, line 257
- `Polyfold.IsSc1With.eq_of_uniqueDiffWithinAt` — Polyfold/Chapter1/ScSmooth.lean, line 289
- `Polyfold.IsSc1.scDeriv_eqOn` — Polyfold/Chapter1/ScSmooth.lean, line 321
- `Polyfold.IsSc1.tangentMap_eqOn` — Polyfold/Chapter1/ScSmooth.lean, line 328
- `Polyfold.IsSc1.congr` — Polyfold/Chapter1/ScSmooth.lean, line 335
- `Polyfold.IsSc1With.continuousOn_deriv` — Polyfold/Chapter1/ScSmooth.lean, line 272
- `Polyfold.IsSc1With.exists_delta_deriv` — Polyfold/Chapter1/Properties.lean, line 69
- `isSc1_iff_contDiffOn_of_finiteDimensional` — Polyfold/Test.lean, line 124
- `Polyfold.exists_isSc1_not_continuousOn_deriv` — Polyfold/Chapter1/ScOneNotNormContinuous.lean, line 690
- `Polyfold.ScOneExample.isSc1With` — Polyfold/Chapter1/ScOneNotNormContinuous.lean, line 587
- `Polyfold.ScOneExample.not_continuousAt_D` — Polyfold/Chapter1/ScOneNotNormContinuous.lean, line 648

*What differs.*
- Condition (2) is Mathlib's differentiability of $f : U_1 \to F_0$ at $x$ within $U_1$, with derivative $Df(x)|_{E_1}$; the limit over $h \in E_1$ with $x + h \in U_1$ is exactly this.
- The text speaks of "the" operator $Df(x)$ and "the" tangent map; both need $Df(x)$ to be unique, which the text does not discuss. The formal definition takes the family $D$ as an explicit parameter (`IsSc1With`), proves uniqueness on $U_1$ where $U_1$ has unique differentiability (relatively open subsets of partial quadrants have it, V1.10) using the density of $E_1$ in $E_0$, and defines `tangentMap` through a choice that is then shown immaterial.
- The remark on the compact-open topology is formalized here as the uniform continuity of $x \mapsto Df(x)$ on compact sets of $E_0$, and as an equivalence with level $0$ of (3) in V1.34; the remark on finite dimensions is proved on open sets in `Polyfold/Test.lean` and on relatively open subsets of quadrants, with boundary, in V1.35. That $x \mapsto Df(x)$ need not be norm continuous is proved by an example, which the text does not give: $f(t, x)_k = \cos(kt)x_k$ on $\mathbb R \oplus X$, $X$ the weighted $c_0$ scale (the project's first infinite-dimensional sc-Banach space); the factor $k$ of the $t$-derivative is absorbed by one level, $(\pi/(n+1), 0) \to 0$ in $E_1$, but $\|Df(\pi/(n+1), 0) - Df(0, 0)\| \ge 2$, and the derivative is unique on $E_1$, so no derivative family is norm continuous (Findings, Chapter 1, follow-up item 1; formerly G.3). Updated in the third addendum of this page.

### V1.14. Sc^k and sc-smooth maps

*as in the book* · $Tf$ built from the chosen derivative

**HWZ (§1.1, Definition 1.15, p. 11 (unnumbered in the preprint)).** Inductively, an $\mathrm{sc}^0$ map $f$ is $\mathrm{sc}^2$ if it is $\mathrm{sc}^1$ and $Tf : TU \to TV$ is $\mathrm{sc}^1$; then $T^2f = T(Tf)$ is $\mathrm{sc}^0$, and $f$ is $\mathrm{sc}^3$ if $T^2f$ is $\mathrm{sc}^1$, and so on. $f$ is $\mathrm{sc}^\infty$, or *sc-smooth*, if it is $\mathrm{sc}^k$ for all $k \ge 0$.

*The preprint's numbered Remark 1.15 (partial cones) is not formalized; the inductive definition that precedes it is numbered 1.15 here, as the Lean files do.*

**Proved in Lean.** $f$ is *$\mathrm{sc}^k$ on $U$* by recursion on $k$: $\mathrm{sc}^0$ means $\mathrm{sc}^0$; $\mathrm{sc}^{k+1}$ means $\mathrm{sc}^1$ on $U$ with the tangent map $Tf$ (built from the chosen derivative) $\mathrm{sc}^k$ on $TU \subseteq TE$. $f$ is *sc-smooth* if it is $\mathrm{sc}^k$ for every $k$. Then $\mathrm{sc}^{k+1}$ implies $\mathrm{sc}^k$ (and $\mathrm{sc}^l$ for $l \le k$); $f$ is sc-smooth iff it is $\mathrm{sc}^1$ with sc-smooth tangent map; on an sc-domain, $\mathrm{sc}^k$ depends only on the values on $U$.

- `Polyfold.IsSck` — Polyfold/Chapter1/ScSmooth.lean, line 344
- `Polyfold.IsScSmooth` — Polyfold/Chapter1/ScSmooth.lean, line 349
- `Polyfold.IsSck.of_succ` — Polyfold/Chapter1/ScSmooth.lean, line 366
- `Polyfold.IsSck.of_le` — Polyfold/Chapter1/ScSmooth.lean, line 371
- `Polyfold.isScSmooth_iff` — Polyfold/Chapter1/ScSmooth.lean, line 384
- `Polyfold.IsSck.congr` — Polyfold/Chapter1/ChainRule.lean, line 298

*What differs.*
- The recursion uses the tangent map built from the chosen derivative `scDeriv`; on relatively open subsets of partial quadrants the choice does not matter (V1.13), so the notion is the text's.

### V1.15. Sc¹ in terms of the levels

*restated* · the extensions $Df(x)$ an explicit family · their compatibility across levels proved · on any sc-domain

**HWZ (§1.2, Proposition 1.16, p. 12).** Let $U$ be relatively open in a partial quadrant of $E$ and $F$ an sc-Banach space. An $\mathrm{sc}^0$ map $f : U \to F$ is $\mathrm{sc}^1$ if and only if (1) for every $m \ge 1$, $f : U_m \to F_{m-1}$ is $C^1$, so that $df : U_m \to \mathcal L(E_m, F_{m-1})$ is continuous; and (2) for every $m \ge 1$ and $x \in U_m$, $df(x)$ extends to a bounded $Df(x) : E_{m-1} \to F_{m-1}$ with $(x, h) \mapsto Df(x)h$ continuous on $U_m \oplus E_{m-1}$. In particular, at a smooth point $x \in U_\infty$ of an $\mathrm{sc}^1$ map, $Df(x) : E \to F$ is an sc-operator.

**Proved in Lean.** Let $U$ be an sc-domain in $E$ and $f$ $\mathrm{sc}^0$ on $U$. Then $f$ is $\mathrm{sc}^1$ on $U$ if and only if there is a family of operators $D_m(x) \in \mathcal L(E_m, F_m)$, $x \in U_{m+1}$, such that for every $m$: $f_m \circ \iota : U_{m+1} \to F_m$ is differentiable within $U_{m+1}$ at every $x \in U_{m+1}$ with derivative $D_m(x) \circ \iota$, and $(x, h) \mapsto D_m(x)h$ is continuous on $U_{m+1} \times E_m$. For such a family, $x \mapsto D_m(x) \circ \iota$ is continuous $U_{m+1} \to \mathcal L(E_{m+1}, F_m)$ in the operator norm, so $f : U_{m+1} \to F_m$ is $C^1$; and $\iota_m \circ D_m(x) = D_0(\iota x) \circ \iota_m$, so the $D_m(x)$ are the restrictions of one operator $Df(x) = D_0(x)$. For an $\mathrm{sc}^1$ map with derivatives $Df$, the family is given by the *level operators* $Df(x) : E_m \to F_m$ (V1.26). At a point $x \in U_1$ that is smooth, $Df(x) : E_0 \to F_0$ is an sc-operator.

- `Polyfold.IsSc1Levels` — Polyfold/Chapter1/Levels.lean, line 644
- `Polyfold.IsSc1Levels.continuousOn_clm` — Polyfold/Chapter1/Levels.lean, line 656
- `Polyfold.IsSc1Levels.contDiffOn` — Polyfold/Chapter1/Levels.lean, line 662
- `Polyfold.IsSc1Levels.toBase_apply` — Polyfold/Chapter1/Levels.lean, line 674
- `Polyfold.IsSc1Levels.isSc1With` — Polyfold/Chapter1/Levels.lean, line 704
- `Polyfold.IsSc1With.isSc1Levels` — Polyfold/Chapter1/Levels.lean, line 734
- `Polyfold.proposition_1_16` — Polyfold/Chapter1/Levels.lean, line 744
- `Polyfold.IsSc1With.contDiffOn_base` — Polyfold/Chapter1/Properties.lean, line 120
- `Polyfold.IsSc1With.scOperator_deriv` — Polyfold/Chapter1/Properties.lean, line 130

*What differs.*
- The text's one symbol $Df(x)$ for the extensions on all levels becomes an explicit family $D_m(x)$; that they are restrictions of a single operator (Lemma 3.H of the exposition), which the text does not state and which the direction (⇐), called "clear" in the 2010 paper, needs, is proved (`IsSc1Levels.toBase_apply`).
- The text's (1), the $C^1$ property and the continuity of $df$ in the operator norm, is a consequence of the formal conditions rather than part of them; it is proved for both directions (`IsSc1Levels.contDiffOn`, `IsSc1Levels.continuousOn_clm`, and for an $\mathrm{sc}^1$ map directly in V1.26).
- The hypothesis "$U$ relatively open in a partial quadrant" is weakened to `IsScDomain` (V1.27), which is all the proof uses. The "in particular" is proved as stated, for the derivative family of Definition 1.14 at a smooth point of $U_1$.

### V1.16. Lifting the index: sc^k on $U^1$

*as in the book* · no hypothesis on the target · on any sc-domain

**HWZ (§1.2, Proposition 1.17, p. 12).** Let $U$ and $V$ be relatively open subsets of partial quadrants in sc-Banach spaces and $f : U \to V$ an $\mathrm{sc}^k$ map. Then $f : U^1 \to V^1$ is also $\mathrm{sc}^k$.

**Proved in Lean.** Let $U$ be an sc-domain in $E$ and $f$ $\mathrm{sc}^k$ on $U$. Then the level-$1$ map $f_1 : E_1 \to F_1$ is $\mathrm{sc}^k$ on $U^1 = U_1$ as a map between the shifted spaces $E^1$ and $F^1$. For $k = 0$ no hypothesis on $U$ is needed; for $\mathrm{sc}^1$ with derivatives $Df$ the derivatives of $f_1$ are the level-$1$ operators $Df(x) : E_1 \to F_1$, $x \in U_2$; and sc-smooth maps lift to sc-smooth maps.

- `Polyfold.IsSc0.shift` — Polyfold/Chapter1/Levels.lean, line 364
- `Polyfold.IsSc1With.shift` — Polyfold/Chapter1/Levels.lean, line 752
- `Polyfold.IsSck.shift` — Polyfold/Chapter1/Levels.lean, line 769
- `Polyfold.IsScSmooth.shift` — Polyfold/Chapter1/Levels.lean, line 789
- `Polyfold.IsScDomain.shift` — Polyfold/Chapter1/Levels.lean, line 377

*What differs.*
- The target $V$ plays no role (the formal map goes into $F^1$; values in $V^1$ follow from $f(U) \subseteq V$). The hypothesis on $U$ is the weaker `IsScDomain`.
- The induction uses $T(U^1) = (TU)^1$ and that the tangent map of $f_1$ is the level-$1$ map of $Tf$, which rests on the uniqueness of derivatives (V1.13).

### V1.17. Sc^k maps are $C^k$ from $U_{m+k}$ to $F_m$

*as in the book* · $C^k$ within the set, in Mathlib's sense · proved for all levels at once

**HWZ (§1.2, Proposition 1.18, p. 13).** Let $U$ and $V$ be relatively open subsets of partial quadrants in sc-Banach spaces. If $f : U \to V$ is $\mathrm{sc}^k$, then for every $m \ge 0$ the map $f : U_{m+k} \to V_m$ is of class $C^k$; moreover $f : U_{m+l} \to V_m$ is $C^l$ for every $0 \le l \le k$.

**Proved in Lean.** Let $U$ be an sc-domain in $E$ and $f$ $\mathrm{sc}^k$ on $U$. Then for every $m$ the map $f_m \circ \iota : U_{m+k} \to F_m$ is $C^k$ within $U_{m+k}$ (Mathlib's `ContDiffOn`), and $f_m \circ \iota : U_{m+l} \to F_m$ is $C^l$ for $l \le k$; in particular $f \circ \iota_k : U_k \to F_0$ is $C^k$. An sc-smooth map is $C^k$ from $U_{m+k}$ to $F_m$ for all $m$, $k$.

- `Polyfold.IsSck.contDiffOn_levels'` — Polyfold/Chapter1/Levels.lean, line 802
- `Polyfold.IsSck.contDiffOn_levels` — Polyfold/Chapter1/Levels.lean, line 856
- `Polyfold.IsSck.contDiffOn_levels_of_le` — Polyfold/Chapter1/Levels.lean, line 862
- `Polyfold.IsSck.contDiffOn_base` — Polyfold/Chapter1/Levels.lean, line 868
- `Polyfold.IsScSmooth.contDiffOn_levels` — Polyfold/Chapter1/Levels.lean, line 874

*What differs.*
- "Of class $C^k$" on a relatively open subset of a quadrant, which the text never defines, is Mathlib's $C^k$ within the set; on these sets derivatives are unique.
- The 2010 paper proves the case $m = 0$ and lifts it with Proposition 1.17; the formal proof treats a general level directly, with a compatible level-lowering operator $\rho : E_{m+k} \to E_m$ as a parameter, and uses the compact-open lemma (V1.26) in place of the multilinear maps $\Gamma(x)$ and differentiation under the integral sign.

### V1.18. Sc^{k+1} from classical smoothness on the levels

*as in the book* · as stated, the text's hypothesis · by the induction $(\mathrm S_k)$ (V1.38) · stronger-hypothesis version kept

**HWZ (§1.2, Proposition 1.19, p. 13).** Let $U$ be relatively open in a partial quadrant of $E$ and $F$ an sc-Banach space. Assume that for every $m \ge 0$ and $0 \le l \le k$ the map $f : U \to F$ induces a map $f : U_{m+l} \to F_m$ of class $C^{l+1}$. Then $f$ is $\mathrm{sc}^{k+1}$.

**Proved in Lean.** Let $U$ be an sc-domain in $E$ and $f$ $\mathrm{sc}^0$ on $U$. If for every $m \ge 0$ and $0 \le l \le k$ the map $f_m \circ \iota : U_{m+l} \to F_m$ is $C^{l+1}$ within $U_{m+l}$, then $f$ is $\mathrm{sc}^{k+1}$ on $U$; if this holds for every $l$, then $f$ is sc-smooth. Also proved, under the stronger hypothesis that every level map $f_m : U_m \to F_m$ is $C^{k+1}$: $f$ is $\mathrm{sc}^{k+1}$; for $k = 0$, where the two hypotheses agree, with $Df(x)$ the derivative of $f : U_0 \to F_0$ at $x$; and if every $f_m$ is $C^\infty$, $f$ is sc-smooth.

- `Polyfold.proposition_1_19_text` — Polyfold/Chapter1/LevelsWeak.lean, line 949
- `Polyfold.IsScSmooth.of_contDiffOn_levels_text` — Polyfold/Chapter1/LevelsWeak.lean, line 973
- `Polyfold.proposition_1_19_zero` — Polyfold/Chapter1/Properties.lean, line 165
- `Polyfold.proposition_1_19` — Polyfold/Chapter1/Levels.lean, line 884
- `Polyfold.IsScSmooth.of_contDiffOn_levels` — Polyfold/Chapter1/Levels.lean, line 943

*What differs.*
- "$f$ induces a map $f : U_{m+l} \to F_m$" is the $\mathrm{sc}^0$ hypothesis (the values on $U_m$ lie in $F_m$; continuity then follows from the case $l = 0$); "of class $C^{l+1}$" is Mathlib's $C^{l+1}$ within $U_{m+l}$, as in V1.17. The text's relatively open subset of a partial quadrant is a special case of an sc-domain (V1.27).
- The proof is the 2010 paper's induction $(\mathrm S_k)$ on the elementary maps $(x, h_1, \dots, h_j) \mapsto d^jf(x)(h_1, \dots, h_j)$ on mixed levels (V1.37, V1.38), with $f$ the elementary map with $j = 0$. It cannot be run on the hypothesis itself: if $f$ satisfies it with $k$, then $Tf$ in general does not satisfy it with $k - 1$, its second component $(x, h) \mapsto Df(x)h : U_{m+l+1} \times E_{m+l} \to F_m$ being only $C^l$.
- The earlier version under the stronger hypothesis "$f : U_m \to F_m$ is $C^{k+1}$ for every $m$" (`proposition_1_19`, `IsScSmooth.of_contDiffOn_levels`) is kept: there the level maps of $Tf$ are $C^k$ and the induction needs no $(\mathrm S_k)$. For $k = 0$ the two hypotheses agree (`proposition_1_19_zero`).

### V1.19. Maps into $\mathbb R^N$

*as in the book* · as stated, the text's hypothesis · $\mathbb R^N$ read as any finite-dim. $V$ · stronger-hypothesis version kept

**HWZ (§1.2, Corollary 1.20, p. 13).** Let $U$ be relatively open in a partial quadrant of an sc-Banach space and $f : U \to \mathbb R^N$. If for some $k$ and all $0 \le l \le k$ the map $f : U_l \to \mathbb R^N$ is $C^{l+1}$, then $f$ is $\mathrm{sc}^{k+1}$.

**Proved in Lean.** Let $U$ be an sc-domain in $E$, $V$ a finite-dimensional normed space with its constant sc-structure and $f : E_0 \to V$. If for some $k$ and all $0 \le l \le k$ the map $f \circ \iota_l : U_l \to V$ is $C^{l+1}$ within $U_l$, then $f$ is $\mathrm{sc}^{k+1}$ on $U$. If $f \circ \iota_l$ is $C^{l+1}$ within $U_l$ for every $l$, then $f$ is sc-smooth; if $f$ is $C^\infty$ within $U$, then $f$ is sc-smooth. Also proved, under the stronger hypothesis: if $f \circ \iota_m$ is $C^{k+1}$ within $U_m$ for every $m$, in particular if $f$ is $C^{k+1}$ within $U$, then $f$ is $\mathrm{sc}^{k+1}$; for $k = 0$ this is the text's hypothesis.

- `Polyfold.corollary_1_20_text` — Polyfold/Chapter1/LevelsWeak.lean, line 984
- `Polyfold.IsScSmooth.of_contDiffOn_levels_finiteDimensional_text` — Polyfold/Chapter1/LevelsWeak.lean, line 1005
- `Polyfold.IsScSmooth.of_contDiffOn_finiteDimensional` — Polyfold/Chapter1/Levels.lean, line 954
- `Polyfold.corollary_1_20_zero` — Polyfold/Chapter1/Properties.lean, line 233
- `Polyfold.corollary_1_20` — Polyfold/Chapter1/Levels.lean, line 919
- `Polyfold.corollary_1_20_base` — Polyfold/Chapter1/Levels.lean, line 932

*What differs.*
- The corollary is Proposition 1.19 (V1.18) for the constant structure: $f : U_{m+l} \to V$ is the restriction of the $C^{l+1}$ map $f : U_l \to V$, and $f$ is $\mathrm{sc}^0$ because each $f : U_m \to V$ is the continuous $f : U_0 \to V$ composed with the inclusion, so no $\mathrm{sc}^0$ hypothesis is needed. $\mathbb R^N$ is any finite-dimensional normed space.
- The two sc-smooth statements are the exposition's ("$C^{l+1}$ on $U_l$ for every $l$", and "$C^\infty$ on $U_0$"), not the text's; the second gives the bump functions the theory uses. The earlier versions under the stronger hypothesis $C^{k+1}$ on every $U_m$ (`corollary_1_20`, `corollary_1_20_base`) are kept.

### V1.20. The chain rule

*as in the book* · $W \subset Q \subset G$ plays no role · proved by the mean value inequality · sc^k and sc-smooth versions proved

**HWZ (§1.3, Theorem 1.21, p. 13 (proof §1.4.2, pp. 15–16)).** Let $U \subset C \subset E$, $V \subset D \subset F$ and $W \subset Q \subset G$ be relatively open subsets of partial quadrants in sc-Banach spaces and $f : U \to V$, $g : V \to W$ be $\mathrm{sc}^1$. Then $g \circ f : U \to W$ is $\mathrm{sc}^1$ and $T(g \circ f) = Tg \circ Tf$.

*Remark 1.22: differentiability is guaranteed only with the loss of one level, yet the composition loses only one; the compactness of $E_{m+1} \to E_m$ saves the day.*

**Proved in Lean.** Let $U \subseteq C \subseteq E$ and $V \subseteq D \subseteq F$ be relatively open subsets of partial quadrants, $f$ $\mathrm{sc}^1$ on $U$ with $f(U) \subseteq V$, and $g$ $\mathrm{sc}^1$ on $V$ (with values in any sc-Banach space $G$). Then $g \circ f$ is $\mathrm{sc}^1$ on $U$ and $T(g \circ f) = Tg \circ Tf$ on $TU$. With derivatives made explicit: if $g$ is $\mathrm{sc}^1$ with derivatives $Dg$ and $f$ with derivatives $Df$, and $V_1$ is the intersection of an open and a convex set, then $g \circ f$ is $\mathrm{sc}^1$ with derivatives $x \mapsto Dg(f_1(x)) \circ Df(x)$; this existence part needs no hypothesis on $U$. Iterated: the composition of $\mathrm{sc}^k$ maps between sc-domains (in particular between relatively open subsets of partial quadrants) is $\mathrm{sc}^k$, and sc-smooth maps compose to sc-smooth maps.

- `Polyfold.IsSc1With.hasFDerivWithinAt_comp` — Polyfold/Chapter1/ChainRule.lean, line 125
- `Polyfold.IsSc1With.comp` — Polyfold/Chapter1/ChainRule.lean, line 256
- `Polyfold.theorem_1_21'` — Polyfold/Chapter1/ChainRule.lean, line 269
- `Polyfold.theorem_1_21` — Polyfold/Chapter1/ChainRule.lean, line 281
- `Polyfold.IsSck.comp` — Polyfold/Chapter1/ChainRule.lean, line 306
- `Polyfold.IsSck.comp_of_isRelOpenInQuadrant` — Polyfold/Chapter1/ChainRule.lean, line 323
- `Polyfold.IsScSmooth.comp` — Polyfold/Chapter1/ChainRule.lean, line 317

*What differs.*
- The text's third tuple $W \subset Q \subset G$ is not needed and is dropped; $T(g \circ f) = Tg \circ Tf$ is an equality of maps on $TU$, which for the chosen derivatives rests on the uniqueness of $D(g \circ f)(x)$ on $U_1$ (so the quadrant structure of $U$ enters only there).
- The two integrals of §1.4.2 are replaced by the one-variable mean value inequality for $t \mapsto g(y_t) - t\,Dg(f(x))(f(x+h) - f(x))$ on $[0, 1]$, and the first integral is not needed at all since $Dg(f(x))$ is bounded on $F_0$. The step "$y_t \in V_1$ for $|h|_1$ small" uses that $V_1$ is open-in-convex and that $f : U_1 \to F_1$ is continuous, which the text does not say; the uniform convergence on the compact set $\overline{Df(x)(\iota B_1)}$ is `IsCompact.eventually_forall_of_forall_eventually` instead of the subsequence argument.
- The text's "$f : U_1 \to F$ is $C^1$ by Proposition 1.18" is not used.

### V1.21. The degeneracy index of a partial quadrant

*as in the book* · defined through a chosen presentation · defined on all of $E_0$ (junk off $C$)

**HWZ (§1.3, Definition 1.23, p. 14).** Let $C$ be a partial quadrant in $E$ and $T : E \to \mathbb R^k \oplus W$ an sc-isomorphism with $T(C) = [0,\infty)^k \oplus W$. For $x \in C$ with $T(x) = (a_1, \dots, a_k, w)$ put $d_C(x) = \#\{i : a_i = 0\}$. The map $d_C : C \to \mathbb N_0$ is the *degeneracy index*; points with $d_C = 0$ are interior, with $d_C = 1$ boundary points, with $d_C \ge 2$ corners.

**Proved in Lean.** For $p = (a, w) \in \mathbb R^n \oplus W$ let $\#(p)$ be the number of indices $i$ with $a_i = 0$, and for a presentation $T : E \cong \mathbb R^n \oplus W$ of a partial quadrant let $d_T(x) = \#(T_0 x)$. The *degeneracy index* $d_C(x)$ of $x \in E_0$ is $d_T(x)$ for an arbitrarily chosen presentation $T$ of $C$ (and $0$ if $C$ is not a partial quadrant); by Lemma 1.24 it equals $d_T(x)$ for every presentation $T$ and every $x \in C$. On the quadrant $[0,\infty)^n \oplus W$ itself, $d(p) = \#(p)$.

- `Polyfold.quadrantDeg` — Polyfold/Chapter1/Degeneracy.lean, line 60
- `Polyfold.degIndexWith` — Polyfold/Chapter1/Degeneracy.lean, line 65
- `Polyfold.degIndex` — Polyfold/Chapter1/Degeneracy.lean, line 226
- `Polyfold.degIndex_eq` — Polyfold/Chapter1/Degeneracy.lean, line 229
- `Polyfold.degIndex_quadrant` — Polyfold/Chapter1/Degeneracy.lean, line 237

*What differs.*
- The text defines $d_C$ on $C$ through a fixed $T$ and then shows independence; the formal $d_C$ is a total function on $E_0$ defined through a chosen presentation, with the independence theorem (`degIndex_eq`) making it the text's on $C$. The classification into interior, boundary and corner points is terminology, not formalized in Chapter 1 (Chapter 2 defines the boundary of an M-polyfold).

### V1.22. The degeneracy index does not depend on the presentation

*as in the book* · only level $0$ and linear algebra are used · $k = k'$ derived from the lemma at $x = 0$

**HWZ (§1.3, Lemma 1.24, p. 14 (proof §1.4.3, p. 17)).** The map $d_C$ does not depend on the choice of the linear sc-isomorphism $T$.

**Proved in Lean.** Let $T : E \cong \mathbb R^n \oplus W$ and $T' : E \cong \mathbb R^{n'} \oplus W'$ be sc-isomorphisms with $C = T_0^{-1}(Q_n) = T_0'^{-1}(Q_{n'})$. Then $d_T(x) = d_{T'}(x)$ for every $x \in C$, and $n = n'$. Core form: a continuous linear equivalence $S : \mathbb R^n \times W_0 \to \mathbb R^{n'} \times W'_0$ carrying the quadrant onto the quadrant preserves the number of vanishing half-line coordinates at every point of the quadrant.

- `Polyfold.quadrantDeg_eq_of_equiv` — Polyfold/Chapter1/Degeneracy.lean, line 158
- `Polyfold.lemma_1_24` — Polyfold/Chapter1/Degeneracy.lean, line 184
- `Polyfold.lemma_1_24_dim` — Polyfold/Chapter1/Degeneracy.lean, line 204

*What differs.*
- The core statement is proved for any continuous linear equivalence of the base levels carrying one quadrant onto the other; the sc-structure plays no role, as the exposition observes.
- The text first proves $k = k'$ and then the index equality; the formal proof does not need $k = k'$ and derives it afterwards as the index of the origin. The codimension of $E_x$ is made precise as $\dim(V/E_x) = \#I(x)$, with $E_x$ the kernel of $(b, v) \mapsto (b_i)_{i \in I(x)}$, and $S$ induces an isomorphism of the quotients; the text's "since $S$ is an isomorphism, equality" is the symmetric inclusion for $S^{-1}$.

### V1.23. Boundary recognition

*stronger* · sc¹ suffices, the text has sc-smooth · germ = sc¹ map with sc¹ inverse on $U$, $U'$ · proved, not cited; by the §2.3 argument

**HWZ (§1.3, Theorem 1.25, p. 14).** Given tuples $(U, C, E)$ and $(U', C', E')$ and a germ $f : (U, x) \to (U', x')$ of a local sc-diffeomorphism with $x' = f(x)$, then $d_C(x) = d_{C'}(f(x))$. (The text cites [20], Theorem 1.19, for the proof of a more general result; sc-smooth diffeomorphisms recognize boundary points and corners, homeomorphisms only boundaries.)

**Proved in Lean.** Let $U \subseteq C \subseteq E$ and $U' \subseteq C' \subseteq E'$ be relatively open subsets of partial quadrants, $f : E_0 \to E'_0$ $\mathrm{sc}^1$ on $U$ with $f(U) \subseteq U'$, $g : E'_0 \to E_0$ $\mathrm{sc}^1$ on $U'$ with $g(U') \subseteq U$, $g \circ f = \mathrm{id}$ on $U$ and $f \circ g = \mathrm{id}$ on $U'$. Then $d_C(x) = d_{C'}(f(x))$ for every $x \in U$. At points $x \in U_1$ this is proved directly; a general $x \in U$ is approximated by level-$1$ points of $U$ with the same index, and $d_{C'}$ is upper semicontinuous.

- `Polyfold.theorem_1_25` — Polyfold/Chapter2/DegeneracyIndex.lean, line 572
- `Polyfold.theorem_1_25_lvl1` — Polyfold/Chapter2/DegeneracyIndex.lean, line 535
- `Polyfold.degIndexWith_le_of_germ` — Polyfold/Chapter2/DegeneracyIndex.lean, line 424
- `Polyfold.eventually_degIndexWith_le` — Polyfold/Chapter2/DegeneracyIndex.lean, line 164
- `Polyfold.exists_tendsto_lvl1_degIndexWith` — Polyfold/Chapter2/DegeneracyIndex.lean, line 183
- `Polyfold.IsSc1With.mapsTo_minimalSubspace` — Polyfold/Chapter2/DegeneracyIndex.lean, line 357

*What differs.*
- The text's "germ of a local sc-diffeomorphism" is undefined in Chapter 1; it is read as an $\mathrm{sc}^1$ map $f : U \to U'$ with an $\mathrm{sc}^1$ inverse $g : U' \to U$, where $U$ and $U'$ may be taken as small as one likes (relatively open neighbourhoods of $x$ and $f(x)$). Only $\mathrm{sc}^1$ is needed, where the text has sc-smooth: the statement is stronger.
- The text gives no proof. The formal proof is the argument of §2.3 (Lemma 2.29, Theorem 2.31, Corollary 2.32) specialized to the identity retraction: for $x \in U_1$ and $v \in E_x \cap E_1$ the sign argument gives $Df(x)v \in E'_{f(x)}$, density extends this to $E_x$, and the codimensions $\dim(E/E_x) = d_C(x)$, $\dim(E'/E'_{f(x)}) = d_{C'}(f(x))$ compare through the chain rule; general points are reached by approximation with level-$1$ points of the same index (smooth points are not needed) and the upper semicontinuity of the index. The file sits in Chapter 2 because it uses the retraction vocabulary.

### V1.24. Fredholm operators between Banach spaces, and Riesz–Schauder

*not in the book* · Mathlib v4.33.1 has no Riesz–Schauder · finite codimension via Riesz's lemma

**HWZ (§1.4.1, p. 14 (quoted as classical)).** The proof of Proposition 1.10 opens with "since $S : E_m \to F_m$ is compact for every level, the operator $T + S : E_m \to F_m$ is Fredholm for every $m$", and later uses that the image of a Fredholm operator is closed. The classical theory of Fredholm operators and compact perturbations is taken for granted.

**Proved in Lean.** For real Banach spaces $E$, $F$: a continuous linear map with closed range is a strict map (open mapping theorem), and one with finite-dimensional kernel, closed range and range of finite codimension is Fredholm in Mathlib's sense (the remaining conditions, strictness and complementedness of the kernel, are automatic). A finite-rank operator is compact. **Riesz–Schauder:** for a compact operator $c$ on $E$, $1 + c$ has finite-dimensional kernel, closed range and range of finite codimension, hence is Fredholm.

- `Polyfold.isStrictMap_of_isClosed_range` — Polyfold/Chapter1/FredholmPerturbation.lean, line 62
- `Polyfold.isFredholm_of_banach` — Polyfold/Chapter1/FredholmPerturbation.lean, line 73
- `Polyfold.isCompactOperator_of_finiteDimensional_range` — Polyfold/Chapter1/FredholmPerturbation.lean, line 84
- `Polyfold.finiteDimensional_ker_one_add` — Polyfold/Chapter1/FredholmPerturbation.lean, line 103
- `Polyfold.isClosed_range_one_add` — Polyfold/Chapter1/FredholmPerturbation.lean, line 181
- `Polyfold.coFG_range_one_add` — Polyfold/Chapter1/FredholmPerturbation.lean, line 292
- `Polyfold.isFredholm_one_add` — Polyfold/Chapter1/FredholmPerturbation.lean, line 333

*What differs.*
- No counterpart as a statement: Mathlib has the notion of a Fredholm operator (with quasi-inverses) but not the theorem that $1 + \text{compact}$ is Fredholm, nor that compact perturbations preserve the property. Both are proved here, the finite codimension of the range by a chain of closed subspaces and Riesz's lemma.

### V1.25. Compact perturbations of Fredholm operators

*not in the book* · via a quasi-inverse of $u$ · the index: V1.28

**HWZ (§1.4.1, p. 14 (quoted as classical)).** "The operator $T + S : E_m \to F_m$ is Fredholm for every $m$" because $S$ is compact on every level: the stability of Fredholm operators under compact perturbations, used without citation.

**Proved in Lean.** Let $E$, $F$ be real Banach spaces, $u : E \to F$ a Fredholm operator and $k : E \to F$ a compact operator. Then $u + k$ is Fredholm.

- `Polyfold.isFredholm_add_isCompactOperator` — Polyfold/Chapter1/FredholmPerturbation.lean, line 354

*What differs.*
- Proved from Riesz–Schauder with a quasi-inverse $v$ of $u$: $v(u + k) = 1 + c_1$ and $(u + k)v = 1 + c_2$ with $c_1$, $c_2$ compact. The invariance of the index, which the exposition states (Kato IV.5.26) and the text does not, is V1.28.

### V1.26. The compact-open lemma and the level operators $Df(x) : E_m \to F_m$

*not in the book* · replaces the 2010 paper's $\Gamma(x)$ · Bochner integral formed in $F_m$

**HWZ (2010 paper, Propositions 2.1–2.3 (the compactness argument), p. 12).** The proofs of Propositions 1.16–1.18 in the 2010 paper rest on one argument: for unit vectors $h_n$ of $E_{m+1}$ a subsequence converges in $E_m$ (compactness of the inclusion), so the continuity of $(x, h) \mapsto Df(x)h$ on $U_{m+1} \times E_m$ gives the continuity of $x \mapsto Df(x)$ into $\mathcal L(E_{m+1}, F_m)$; and on the integral identity $f(x + h) - f(x) = \int_0^1 Df(x + \tau h)h\,d\tau$.

**Proved in Lean.** **Compact-open lemma.** Let $s \subseteq X$ be the intersection of an open and a convex set with unique differentiability at each point, $\iota : Y' \to Y$ a compact operator and $A : X \to \mathcal L(Y, Z)$ with $(x, y) \mapsto A(x)y$ of class $C^k$ on $s \times Y$. Then $x \mapsto A(x) \circ \iota$ is $C^k$ on $s$ into $\mathcal L(Y', Z)$; for $k = 0$, continuity on $s \times Y$ suffices and no hypothesis on $s$ is needed. **Level operators.** For an $\mathrm{sc}^1$ map with derivatives $Df$ and $x \in U_{m+1}$ there is a unique continuous linear $Df(x) : E_m \to F_m$ with $\iota_m \circ Df(x) = Df(\iota x) \circ \iota_m$ (the second component of the level-$m$ tangent map); $(x, h) \mapsto Df(x)h$ is continuous on $U_{m+1} \times E_m$, $x \mapsto Df(x) \circ \iota$ is continuous $U_{m+1} \to \mathcal L(E_{m+1}, F_m)$, and on an sc-domain $f_m \circ \iota : U_{m+1} \to F_m$ is differentiable within $U_{m+1}$ with derivative $Df(x) \circ \iota$, hence $C^1$; if $f_m : U_m \to F_m$ is differentiable at $x$ its derivative is $Df(x)$.

- `Polyfold.exists_delta_of_continuousOn` — Polyfold/Chapter1/Levels.lean, line 117
- `Polyfold.continuousOn_clm_comp_of_isCompactOperator` — Polyfold/Chapter1/Levels.lean, line 144
- `Polyfold.contDiffOn_clm_comp_of_isCompactOperator` — Polyfold/Chapter1/Levels.lean, line 170
- `Polyfold.levelDeriv` — Polyfold/Chapter1/Levels.lean, line 389
- `Polyfold.IsSc1With.exists_levelDeriv` — Polyfold/Chapter1/Levels.lean, line 409
- `Polyfold.IsSc1With.toBase_levelDeriv` — Polyfold/Chapter1/Levels.lean, line 432
- `Polyfold.IsSc1With.levelMap_tangentMapWith` — Polyfold/Chapter1/Levels.lean, line 439
- `Polyfold.IsSc1With.continuousOn_levelDeriv` — Polyfold/Chapter1/Levels.lean, line 455
- `Polyfold.IsSc1With.continuousOn_levelDeriv_clm` — Polyfold/Chapter1/Levels.lean, line 468
- `Polyfold.IsSc1With.hasFDerivWithinAt_level` — Polyfold/Chapter1/Levels.lean, line 483
- `Polyfold.IsSc1With.contDiffOn_level` — Polyfold/Chapter1/Levels.lean, line 592
- `Polyfold.IsSc1With.levelDeriv_eq` — Polyfold/Chapter1/Levels.lean, line 604

*What differs.*
- No counterpart as a statement: the lemma isolates the one analytic mechanism behind §1.2 and its $C^k$ version (by induction with the mean value inequality) replaces the multilinear maps $\Gamma(x)(h_1, \dots, h_k, h)$ and the differentiation under the integral sign of the 2010 paper's Proposition 2.3.
- The integral identity is formed as a Bochner integral in $F_m$ directly and identified with $f(x+h) - f(x)$ through the fundamental theorem of calculus for the $C^1$ map $f : U_1 \to F_0$; the 2010 paper forms it in $F_0$ and notes that the integrand is continuous into $F_m$.

### V1.27. Sc-domains: what the proofs use of a tuple

*not in the book* · the hypothesis that iterates under $T$ · weaker than the text's tuple

**HWZ (§1.1, pp. 10–11 (the tuples $(U, C, E)$)).** Every statement of §§1.2–1.3 is made for $U$ relatively open in a partial quadrant $C$ of $E$, and the tangent construction is said to produce again such a tuple.

**Proved in Lean.** $U \subseteq E_0$ is an *sc-domain* if, for every $m$, the level set $U_m$ is the intersection of an open and a convex subset of $E_m$ and has unique differentiability at each of its points. A relatively open subset of a partial quadrant is an sc-domain; if $U$ is an sc-domain then so are $TU$ in $TE$ and $U^1 = U_1$ in $E^1$.

- `Polyfold.IsScDomain` — Polyfold/Chapter1/ScSmooth.lean, line 487
- `Polyfold.IsRelOpenInQuadrant.isScDomain` — Polyfold/Chapter1/ScSmooth.lean, line 491
- `Polyfold.IsScDomain.tangentSet` — Polyfold/Chapter1/ScSmooth.lean, line 504
- `Polyfold.IsScDomain.shift` — Polyfold/Chapter1/Levels.lean, line 377

*What differs.*
- No counterpart as a statement: the text iterates its definitions on tuples and asserts that $T(U, C, E)$ is a tuple; the formalization iterates on sc-domains, for which the stability under $T$ is a two-line proof, and every theorem of §§1.2–1.3 is stated for sc-domains, hence in particular for the text's tuples.

### V1.28. The Fredholm index and its invariance under compact perturbations

*not in the book* · not in Mathlib · additivity under composition · homotopy $u + tk$, not Kato's proof

**HWZ (§1.4.1, p. 14 (quoted as classical)).** Not stated. The proof of Proposition 1.10 uses that $T + S : E_m \to F_m$ is Fredholm; that its index is that of $T$ is the classical invariance of the index under compact perturbations, which the text does not invoke.

**Proved in Lean.** For a linear map $u$ over a field, $\operatorname{ind}(u) = \dim\ker u - \dim(F/\operatorname{range}u)$; if $u$, $v$ have finite-dimensional kernel and cokernel, so has $v \circ u$ and $\operatorname{ind}(v\circ u) = \operatorname{ind}(u) + \operatorname{ind}(v)$; a bijection plus a finite-rank map, in particular $1$ plus a finite-rank map, has index $0$. For real Banach spaces, a Fredholm operator has finite-dimensional kernel and cokernel; if $v$ is a quasi-inverse of $u$ ($vu - 1$, $uv - 1$ of finite rank) and $\|v\|\|s\| < 1$, then $u + s$ has finite-dimensional kernel and cokernel and $\operatorname{ind}(u + s) = \operatorname{ind}(u)$; if $u$ is Fredholm and $k$ compact, $\operatorname{ind}(u + k) = \operatorname{ind}(u)$.

- `Polyfold.linIndex` — Polyfold/Chapter1/FredholmIndex.lean, line 93
- `Polyfold.HasFiniteIndex` — Polyfold/Chapter1/FredholmIndex.lean, line 97
- `Polyfold.linIndex_comp` — Polyfold/Chapter1/FredholmIndex.lean, line 218
- `Polyfold.linIndex_eq_zero_of_finiteRange_sub_id` — Polyfold/Chapter1/FredholmIndex.lean, line 306
- `Polyfold.HasFiniteIndex.of_bijective_add_and_linIndex` — Polyfold/Chapter1/FredholmIndex.lean, line 313
- `Polyfold.fredholmIndex` — Polyfold/Chapter1/FredholmIndex.lean, line 351
- `Polyfold.IsFredholm.hasFiniteIndex` — Polyfold/Chapter1/FredholmIndex.lean, line 355
- `Polyfold.fredholmIndex_add_of_norm_lt` — Polyfold/Chapter1/FredholmIndex.lean, line 401
- `Polyfold.fredholmIndex_add_isCompactOperator` — Polyfold/Chapter1/FredholmIndex.lean, line 439

*What differs.*
- Infrastructure Mathlib v4.33.1 lacks: Mathlib has Fredholm operators but no index. The exposition cites Kato IV.5.26 for the invariance; the formal proof shows first that the index is locally constant (a small perturbation $u + s$ satisfies $v(u+s) = (1 + vs) + (vu - 1)$, a bijection by the Neumann series plus a finite-rank map) and then that $t \mapsto \operatorname{ind}(u + tk)$ is locally constant, hence constant, on $\mathbb R$.

### V1.29. The level operators of an sc-Fredholm operator

*stronger* · the index on every level · $C \subset F_\infty$ made explicit

**HWZ (§1.1, Definition 1.8, p. 9).** After the definition: $K \subset E_\infty$, $T(X_m) = Y_m$, $E_m = K \oplus X_m$ and "$F = C \oplus T(E_m)$" for all $m$; the index is $\dim K - \dim C$. That $T : E_m \to F_m$ is Fredholm with this index on every level is not stated.

**Proved in Lean.** Let $T$ have an sc-Fredholm splitting $(K, X, C, Y)$. Then $K \le E_\infty$ and $C \le F_\infty$; a subspace $A \le E_\infty$ has $\dim A_m = \dim A$; and for every $m$ the level map $T_m : E_m \to F_m$ is Fredholm with $\dim\ker T_m - \dim(F_m/\operatorname{range}T_m) = \dim K - \dim C$, which is the index $\dim\ker T_0 - \dim(F_0/\operatorname{range}T_0)$ of $T$.

- `Polyfold.ScFredholmSplitting.C_le_smooth` — Polyfold/Chapter1/FredholmIndex.lean, line 480
- `Polyfold.ScBanach.finrank_levelSub_of_le_smooth` — Polyfold/Chapter1/FredholmIndex.lean, line 468
- `Polyfold.ScFredholmSplitting.fredholmIndex_lvl` — Polyfold/Chapter1/FredholmIndex.lean, line 488
- `Polyfold.IsScFredholm.fredholmIndex_lvl` — Polyfold/Chapter1/FredholmIndex.lean, line 498
- `Polyfold.scIndex_eq_fredholmIndex` — Polyfold/Chapter1/FredholmIndex.lean, line 505

*What differs.*
- The text records the splittings on every level but not the index of $T_m$; the formal statement (the exposition's Lemma 2.D) adds that every $T_m$ is Fredholm of index $\operatorname{ind}(T)$, using $\ker T_m = K_m \cong K$ and $F_m/\operatorname{range}T_m = F_m/Y_m \cong C_m \cong C$ (V1.7).

### V1.30. Compact perturbation preserves the index

*stronger* · index not in the text · every level

**HWZ (§1.1, Proposition 1.10, p. 10 (proof §1.4.1, pp. 14–15)).** If $T : E \to F$ is sc-Fredholm and $S : E \to F$ is an $\mathrm{sc}^+$-operator, then $T + S$ is sc-Fredholm. (The index of $T + S$ is not mentioned.)

**Proved in Lean.** Let $T : E \to F$ be an sc-Fredholm operator and $S : E \to F$ an $\mathrm{sc}^+$-operator. Then $\operatorname{ind}(T + S) = \operatorname{ind}(T)$, with $\operatorname{ind} = \dim\ker(\cdot)_0 - \dim\operatorname{coker}(\cdot)_0$; and for every $m$ the level map $(T+S)_m : E_m \to F_m$ is Fredholm of index $\operatorname{ind}(T)$.

- `Polyfold.proposition_1_10_index` — Polyfold/Chapter1/FredholmIndex.lean, line 509
- `Polyfold.proposition_1_10_index_lvl` — Polyfold/Chapter1/FredholmIndex.lean, line 517

*What differs.*
- The text proves only that $T + S$ is sc-Fredholm (V1.9). The equality of indices, which the exposition adds, is proved on level $0$ by V1.28 ($S_0$ is compact) and transported to every level by V1.29 applied to $T + S$.

### V1.31. Finite-dimensional spaces carry only the constant structure

*restated* · "precisely one" as an sc-isomorphism · an onto inclusion forces finite dimension

**HWZ (§1.1, after Definition 1.1, p. 6).** A finite-dimensional Banach space has precisely one sc-structure, the constant one $E_m = E$; on an infinite-dimensional space the constant structure is not an sc-structure, because property (1) fails.

**Proved in Lean.** Let $E$ be an sc-Banach space with $E_0$ finite-dimensional. Then every point of $E_0$ is smooth, every inclusion $\iota_m : E_m \to E_0$ is bijective, and the $\iota_m$ form an sc-isomorphism of $E$ onto $E_0$ with the constant structure. For any scale, if one inclusion $E_{m+1} \to E_m$ is surjective then $E_m$ is finite-dimensional.

- `Polyfold.ScBanach.smooth_eq_top_of_finiteDimensional` — Polyfold/Chapter1/ExpositionLemmas.lean, line 94
- `Polyfold.ScBanach.toBase_bijective_of_finiteDimensional` — Polyfold/Chapter1/ExpositionLemmas.lean, line 100
- `Polyfold.ScBanach.isoConstOfFiniteDimensional` — Polyfold/Chapter1/ExpositionLemmas.lean, line 109
- `Polyfold.ScScale.finiteDimensional_of_surjective_incl` — Polyfold/Chapter1/ExpositionLemmas.lean, line 73

*What differs.*
- With sc-Banach spaces as families, "$E_m = E$" becomes "$\iota_m$ is bijective", and "precisely one structure" becomes: the identity of $E_0$ extends to an sc-isomorphism with the constant structure, so all the level norms are equivalent. "The constant structure is not an sc-structure" becomes: an onto inclusion forces finite dimension (open mapping theorem, then the identity is compact).

### V1.32. Sc-splittings are sc-projections

*hypotheses explicit* · used, not stated, in the text · $\ker P$ for $(1 - P)(E)$

**HWZ (§1.1, Definition 1.5 and the proof of Proposition 1.6, pp. 7–8).** An sc-splitting $E = F \oplus G$ is a topological direct sum $E_m = F_m \oplus G_m$ on every level. In the proof of Proposition 1.6: the map $P$ with $P \circ P = P$, continuous on every $E_m$, "is a sc-projection", and $G := (1 - P)(E)$ is then an sc-complement.

**Proved in Lean.** If $E = A \oplus B$ is an sc-splitting, the projections of $E_m$ onto $A_m$ along $B_m$ are continuous and form an sc-operator $P$ with $P_m^2 = P_m$, $P_m(E_m) = A_m$ and $\ker P_m = B_m$ for every $m$. Conversely, if $P : E \to E$ is an sc-operator with $P_0^2 = P_0$, then $P_m^2 = P_m$ and $P(E)_m = P_m(E_m)$ for every $m$, and $E = P(E) \oplus \ker P$ is an sc-splitting. So $E = A \oplus B$ is an sc-splitting iff there is an sc-operator $P$ with $P^2 = P$, $P(E) = A$, $\ker P = B$.

- `Polyfold.ScBanach.IsScSplitting.isTopCompl` — Polyfold/Chapter1/ExpositionLemmas.lean, line 126
- `Polyfold.ScBanach.IsScSplitting.scProj` — Polyfold/Chapter1/ExpositionLemmas.lean, line 134
- `Polyfold.ScBanach.IsScSplitting.scProj_idem` — Polyfold/Chapter1/ExpositionLemmas.lean, line 154
- `Polyfold.ScBanach.IsScSplitting.range_scProj` — Polyfold/Chapter1/ExpositionLemmas.lean, line 159
- `Polyfold.ScBanach.IsScSplitting.ker_scProj` — Polyfold/Chapter1/ExpositionLemmas.lean, line 167
- `Polyfold.ScOperator.idem_lvl` — Polyfold/Chapter1/ExpositionLemmas.lean, line 175
- `Polyfold.ScOperator.levelSub_range_eq` — Polyfold/Chapter1/ExpositionLemmas.lean, line 180
- `Polyfold.ScBanach.isScSplitting_of_idem` — Polyfold/Chapter1/ExpositionLemmas.lean, line 196
- `Polyfold.ScBanach.isScSplitting_iff_exists_scProj` — Polyfold/Chapter1/ExpositionLemmas.lean, line 234

*What differs.*
- The text uses the equivalence in the proof of Proposition 1.6 without stating it (the exposition's Lemma 2.B). The formal proof of Proposition 1.6 (V1.5) builds the complement directly and does not depend on this item. The complement is written $\ker P$, the same subspace as the text's $(1 - P)(E)$.

### V1.33. The smooth points of a quotient

*as in the book* · Mittag-Leffler argument the text omits · needs $A$ an sc-subspace

**HWZ (§1.1, Proposition 1.7, p. 9).** In the proof: "$(E/A)_\infty = \bigcap_j (E_j/A_j)$ consists of all elements of the form $x + A_\infty$ with $x \in E_\infty$."

**Proved in Lean.** Let $A$ be an sc-subspace of $E$ and $x \in E_0$. If for every $j$ some point of $E_j$ differs from $x$ by an element of $A$, then some smooth point of $E$ differs from $x$ by an element of $A$. Equivalently, the class of $x$ is a smooth point of the quotient $E/A$ if and only if $x + A$ contains a smooth point of $E$.

- `Polyfold.ScBanach.exists_smooth_mem_coset` — Polyfold/Chapter1/ExpositionLemmas.lean, line 293
- `Polyfold.ScBanach.mk_mem_quotient_smooth_iff` — Polyfold/Chapter1/ExpositionLemmas.lean, line 363

*What differs.*
- The text asserts the equality without proof; only the inclusion "$\supseteq$" is needed for Proposition 1.7 (V1.6). The converse is the exposition's Lemma 2.C: correct the choices $x_j \in (x + A) \cap E_j$ by smooth elements of $A$ so that the corrections form a series converging on every level (density of $A_\infty$ in every $A_j$, completeness, and a bound for the norms of the inclusions).

### V1.34. Continuity of $Df$ for the compact-open topology

*restated* · compact-open = uniform on compacta · an equivalence with level $0$ of (3) · the negative remark: an example (V1.13)

**HWZ (§1.1, after Definition 1.14, p. 11).** The map $U_1 \to \mathcal L(E_0, F_0)$, $x \mapsto Df(x)$, will in general not be continuous for the operator norm, but it is continuous for the compact-open topology.

**Proved in Lean.** Let $X$ be a metric space, $Y$, $Z$ real normed spaces, $s \subseteq X$ and $A : X \to \mathcal L(Y, Z)$. Then $(x, h) \mapsto A(x)h$ is continuous on $s \times Y$ if and only if, for every $x \in s$, every compact $K \subseteq Y$ and every $\varepsilon > 0$, $\|A(x')w - A(x)w\| < \varepsilon$ for all $w \in K$ and all $x' \in s$ near $x$. In particular, for $f$ $\mathrm{sc}^1$ on $U$ with derivatives $Df$, $x \mapsto Df(x)$ is continuous on $U_1$ in this sense. The negative half holds by an example (V1.13): there is an $\mathrm{sc}^1$ map $f$ on a relatively open $U$ in a partial quadrant such that, for every derivative family $D$ of $f$, $x \mapsto D(x)$ is not continuous on $U_1$ into $\mathcal L(E_0, F_0)$ with the operator norm.

- `Polyfold.continuousOn_apply_iff_uniformOnCompact` — Polyfold/Chapter1/ExpositionLemmas.lean, line 390
- `Polyfold.IsSc1With.deriv_uniformOnCompact` — Polyfold/Chapter1/ExpositionLemmas.lean, line 440
- `Polyfold.exists_isSc1_not_continuousOn_deriv` — Polyfold/Chapter1/ScOneNotNormContinuous.lean, line 690

*What differs.*
- The compact-open topology on $\mathcal L(Y, Z)$ is written out as uniform convergence on compact sets, and the remark is strengthened to an equivalence (the exposition's Lemma 3.F): it is exactly level $0$ of condition (3) of Definition 1.14. That norm continuity fails in general is proved by a sequence-space example (V1.13; formerly G.3), not by the shift map of the exposition (§6), which needs weighted Sobolev spaces (G.1). Updated in the third addendum of this page.

### V1.35. In finite dimensions sc¹ is $C^1$, also at the boundary

*hypotheses explicit* · on quadrants, with boundary · one-sided = within $U$ · also sc-smooth = $C^\infty$

**HWZ (§1.1, after Definition 1.14, p. 11).** The $\mathrm{sc}^1$-maps between finite-dimensional Banach spaces are the familiar $C^1$-maps.

**Proved in Lean.** Let $V$, $W$ be finite-dimensional real normed spaces with their constant sc-structures, $f : V \to W$, and $U \subseteq V$ an sc-domain, in particular a relatively open subset of a partial quadrant of $V$. Then $f$ is $\mathrm{sc}^1$ on $U$ iff $f$ is $C^1$ within $U$, i.e. differentiable within $U$ at every point of $U$ with $x \mapsto \mathrm{fderivWithin}\,f\,U\,x$ continuous on $U$; and $f$ is sc-smooth on $U$ iff it is $C^\infty$ within $U$.

- `Polyfold.ScBanach.lvlSet_const` — Polyfold/Chapter1/ExpositionLemmas.lean, line 456
- `Polyfold.isSc1_iff_contDiffOn_const` — Polyfold/Chapter1/ExpositionLemmas.lean, line 467
- `Polyfold.isSc1_iff_fderivWithin_const` — Polyfold/Chapter1/ExpositionLemmas.lean, line 481
- `Polyfold.isScSmooth_iff_contDiffOn_const` — Polyfold/Chapter1/ExpositionLemmas.lean, line 492
- `Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant` — Polyfold/Chapter1/ExpositionLemmas.lean, line 506
- `Polyfold.isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant` — Polyfold/Chapter1/ExpositionLemmas.lean, line 512
- `isSc1_iff_contDiffOn_of_finiteDimensional` — Polyfold/Test.lean, line 124

*What differs.*
- The text does not say what $C^1$ means at boundary points of a quadrant; the formal statement uses Mathlib's $C^1$ within $U$, whose derivative at a boundary point is the derivative along $U$ (the one-sided derivative), unique because the quadrant has interior. Any sc-structure on a finite-dimensional space is the constant one up to sc-isomorphism (V1.31).

### V1.36. Level shifts and tangents of tuples are tuples

*as in the book* · proved with Chapter 2 · the reassociation of summands made explicit

**HWZ (§1.1, Definitions 1.11 and 1.13, p. 10).** "$T(U, C, E)$ is a tuple consisting again of a relatively open subset $TU$ in the partial quadrant $TC$ in the sc-Banach space $TE$"; tacitly, $C^1 = C \cap E_1$ is a partial quadrant in $E^1$ and $U^1$ is relatively open in it.

**Proved in Lean.** If $C$ is a partial quadrant in $E$, presented by $T : E \to \mathbb R^n \oplus W$, then $C_1$ is a partial quadrant in $E^1$ (presented by the level shift of $T$) and $TC = \{(x, h) : x \in C_1\}$ is a partial quadrant in $TE$, presented by $T_1 \times T_0$ followed by the reassociation onto $\mathbb R^n \oplus (W^1 \oplus (\mathbb R^n \oplus W))$. If $U$ is relatively open in $C$, then $U_1$ is relatively open in $C_1$ and $TU$ in $TC$; and $(TU)_1 = T(U_1)$.

- `Polyfold.ScIso.shift` — Polyfold/Chapter2/LevelPolyfold.lean, line 74
- `Polyfold.IsPartialQuadrant.shift` — Polyfold/Chapter2/LevelPolyfold.lean, line 79
- `Polyfold.IsRelOpenInQuadrant.shift` — Polyfold/Chapter2/LevelPolyfold.lean, line 87
- `Polyfold.tangentQuadrantIso` — Polyfold/Chapter2/TangentBundle.lean, line 112
- `Polyfold.IsPartialQuadrant.tangentSet` — Polyfold/Chapter2/TangentBundle.lean, line 120
- `Polyfold.IsRelOpenInQuadrant.tangentSet` — Polyfold/Chapter2/TangentBundle.lean, line 135
- `Polyfold.ScBanach.shift_tangentSet` — Polyfold/Chapter1/Levels.lean, line 320

*What differs.*
- The text asserts both facts; the formal proofs (the exposition's Lemmas 3.A(2) and 3.B) live in the Chapter 2 files, where retracts first need them. The statement for $C^k$ is the $k$-fold iterate. The proofs of §§1.2–1.3 do not use these facts but the sc-domain property (V1.27).

### V1.37. The derivative tower: one $d^jf(x)$ on all levels

*not in the book* · the text's tacit identification, proved · chain rule with the inclusions

**HWZ (2010 paper, Proposition 2.4, pp. 51–53 (the derivatives $d^jf(x)$)).** The proof of Proposition 1.19 in the 2010 paper writes $d^jf(x)$ for the $j$-th derivative of $f$ on whichever level pair $U_{m+l} \to F_m$ the argument needs, with one symbol for all of them: the derivatives taken with a finer domain level or a coarser target level are tacitly identified.

**Proved in Lean.** A *derivative tower* of order $k + 1$ for $f : E_0 \to F_0$ on $U$ consists of base-level maps $\Phi_i(x)(h_1, \dots, h_i)$ with $\Phi_0 = f$ and, for $x \in U_{m+l}$, continuous $i$-linear maps $\Psi_{i,m,l}(x)$ on $E_{m+l}$ with values in $F_m$ ($i \le l + 1$, $i \le k + 1$) such that: $\Psi_{i,m,l}(x)(h)$ seen in $F_0$ is $\Phi_i$ at the images of $x$ and $h$ in $E_0$; $\Psi_{i,m,l}$ is continuous on $U_{m+l}$; and for $i \le l$, $i \le k$ it is differentiable within $U_{m+l}$ with derivative $\xi \mapsto \Psi_{i+1,m,l}(x)(\xi, \cdot)$. If $U$ is an sc-domain, $f$ is $\mathrm{sc}^0$ and $f : U_{m+l} \to F_m$ is $C^{l+1}$ within $U_{m+l}$ for all $m$ and $l \le k$, then the iterated derivatives within the level sets form a derivative tower of order $k + 1$. Two values of a tower with the same images in $E_0$ agree.

- `Polyfold.IsDerivTower` — Polyfold/Chapter1/LevelsWeak.lean, line 322
- `Polyfold.levelDerivTower` — Polyfold/Chapter1/LevelsWeak.lean, line 336
- `Polyfold.baseDerivTower` — Polyfold/Chapter1/LevelsWeak.lean, line 342
- `Polyfold.contDiffOn_levels_min` — Polyfold/Chapter1/LevelsWeak.lean, line 348
- `Polyfold.levelDerivTower_toBase` — Polyfold/Chapter1/LevelsWeak.lean, line 368
- `Polyfold.baseDerivTower_toBase` — Polyfold/Chapter1/LevelsWeak.lean, line 405
- `Polyfold.isDerivTower_of_contDiffOn_levels` — Polyfold/Chapter1/LevelsWeak.lean, line 419
- `Polyfold.IsDerivTower.eq_of_toBase` — Polyfold/Chapter1/LevelsWeak.lean, line 450

*What differs.*
- No counterpart as a statement. The tower records exactly what $(\mathrm S_k)$ uses of the hypothesis of Proposition 1.19: $d^if(x)$ exists and is continuous on $E_{m+l}$ into $F_m$ for $i \le l + 1$, and is differentiable with derivative $d^{i+1}f(x)$ for $i \le l$.
- The compatibility across levels is proved from the chain rule for compositions with continuous linear maps (the inclusions), applied to Mathlib's iterated derivative within a set, which is unique on the sc-domain's level sets. For $l > k$ the hypothesis is used with order $k + 1$, by restriction from $U_{m+k}$.

### V1.38. Elementary maps and the induction $(\mathrm S_k)$

*not in the book* · induction on $s$ over all elementary maps · the bound $n_i \le k$ not needed · slots are sc-operators $X \to E^n$

**HWZ (2010 paper, Proposition 2.4, pp. 51–53 (the statement $(\mathrm S_k)$)).** $(\mathrm S_k)$: if $f : U_{m+l} \to F_m$ is $C^{l+1}$ for all $m \ge 0$ and $0 \le l \le k$, then $f$ is $\mathrm{sc}^{k+1}$, and every component $\pi \circ T^{k+1}f : T^{k+1}U \to F^l$ is a linear combination of maps $\Gamma : U^{k+1} \oplus E^{n_1} \oplus \cdots \oplus E^{n_j} \to F^l$, $\Gamma(x, h_1, \dots, h_j) = d^jf(x)(h_1, \dots, h_j)$, with $j + l - 1 \le n_i \le k$. Each such $\Gamma$ is $\mathrm{sc}^1$ with derivative $d^{j+1}f(x)(\delta x, h) + \sum_i d^jf(x)(h_1, \dots, \delta h_i, \dots, h_j)$, and the components of $T^{k+2}f$ are again of this form.

**Proved in Lean.** *Elementary data* on an sc-Banach space $X$: an sc-operator $\pi_0 : X \to E^p$ (the base point), sc-operators $\pi_a : X \to E^{n_a}$, $a = 1, \dots, i$ (the vectors), and a target shift $m$; the *elementary map* is $z \mapsto d^if(\pi_0 z)(\pi_1 z, \dots, \pi_i z) : X \to F^m$ on $\pi_0^{-1}(U_p)$, with $d^if$ from a derivative tower of order $k + 1$ (V1.37). Under the conditions $m + i \le p$, $m + i \le n_a + 1$ and $i \le k$: the elementary map is $\mathrm{sc}^0$; it is $\mathrm{sc}^1$, by the level criterion of Proposition 1.16 (V1.15), with derivative $(\delta z) \mapsto d^{i+1}f(\pi_0 z)(\pi_0\delta z, \pi z) + \sum_a d^if(\pi_0 z)(\pi z \text{ with } \pi_a z := \pi_a\delta z)$; on $TX$ its tangent map is the pair of an elementary map of type $(p + 1, m + 1; n_a + 1)$ and the sum of an elementary map with $i + 1$ vectors and $i$ elementary maps with $i$ vectors, all satisfying the conditions (the one with $i + 1$ vectors provided $i + 1 \le k$). Hence, if the domain $\pi_0^{-1}(U_p)$ is an sc-domain and $i + s \le k + 1$, the elementary map is $\mathrm{sc}^s$. The shifts $E^p$ have $(E^p)_l = E_{p+l}$, with $E \cong E^0$ and $(E^p)^1 \cong E^{p+1}$.

- `Polyfold.ElemData` — Polyfold/Chapter1/LevelsWeak.lean, line 467
- `Polyfold.ElemData.Good` — Polyfold/Chapter1/LevelsWeak.lean, line 483
- `Polyfold.ElemData.dom` — Polyfold/Chapter1/LevelsWeak.lean, line 489
- `Polyfold.ElemData.map` — Polyfold/Chapter1/LevelsWeak.lean, line 492
- `Polyfold.ElemData.map_toBase` — Polyfold/Chapter1/LevelsWeak.lean, line 532
- `Polyfold.ElemData.levelMap_eq` — Polyfold/Chapter1/LevelsWeak.lean, line 552
- `Polyfold.ElemData.isSc0` — Polyfold/Chapter1/LevelsWeak.lean, line 584
- `Polyfold.ElemData.deriv` — Polyfold/Chapter1/LevelsWeak.lean, line 629
- `Polyfold.ElemData.deriv_apply` — Polyfold/Chapter1/LevelsWeak.lean, line 641
- `Polyfold.ElemData.hasFDerivWithinAt_level` — Polyfold/Chapter1/LevelsWeak.lean, line 679
- `Polyfold.ElemData.continuousOn_deriv` — Polyfold/Chapter1/LevelsWeak.lean, line 719
- `Polyfold.ElemData.isSc1Levels` — Polyfold/Chapter1/LevelsWeak.lean, line 740
- `Polyfold.ElemData.isSc1With` — Polyfold/Chapter1/LevelsWeak.lean, line 746
- `Polyfold.ElemData.shiftData` — Polyfold/Chapter1/LevelsWeak.lean, line 809
- `Polyfold.ElemData.derivData` — Polyfold/Chapter1/LevelsWeak.lean, line 813
- `Polyfold.ElemData.slotData` — Polyfold/Chapter1/LevelsWeak.lean, line 818
- `Polyfold.ElemData.Good.shiftData` — Polyfold/Chapter1/LevelsWeak.lean, line 823
- `Polyfold.ElemData.Good.derivData` — Polyfold/Chapter1/LevelsWeak.lean, line 828
- `Polyfold.ElemData.Good.slotData` — Polyfold/Chapter1/LevelsWeak.lean, line 836
- `Polyfold.ElemData.tangentSet_dom` — Polyfold/Chapter1/LevelsWeak.lean, line 845
- `Polyfold.ElemData.tangentMap_eqOn` — Polyfold/Chapter1/LevelsWeak.lean, line 854
- `Polyfold.ElemData.isSck` — Polyfold/Chapter1/LevelsWeak.lean, line 900
- `Polyfold.ElemData.base` — Polyfold/Chapter1/LevelsWeak.lean, line 935
- `Polyfold.ScBanach.shiftAdd` — Polyfold/Chapter1/LevelsWeak.lean, line 174
- `Polyfold.ScBanach.shiftAddZeroIso` — Polyfold/Chapter1/LevelsWeak.lean, line 185
- `Polyfold.ScBanach.shiftAddShiftIso` — Polyfold/Chapter1/LevelsWeak.lean, line 197
- `Polyfold.ScOperator.tangentX` — Polyfold/Chapter1/LevelsWeak.lean, line 774
- `Polyfold.ScOperator.tangentH` — Polyfold/Chapter1/LevelsWeak.lean, line 779

*What differs.*
- The 2010 paper's $(\mathrm S_k)$ describes the components of $T^{k+1}f$; the formal induction runs instead on $s$, over all elementary maps on all sc-Banach spaces $X$ at once: an elementary map is $\mathrm{sc}^{s+1}$ because it is $\mathrm{sc}^1$ and its tangent map is the pair of an elementary map and a sum of elementary maps, all $\mathrm{sc}^s$ by the induction hypothesis. Proposition 1.19 (V1.18) is the case $i = 0$, $p = m = 0$, $X = E$. The text's $\Gamma$ is the case $X = E^{k+1} \oplus E^{n_1} \oplus \cdots \oplus E^{n_j}$ with the projections as $\pi_0, \pi_1, \dots, \pi_j$.
- The index conditions are $m + i \le p$ (the text's $j + l \le k + 1$, which the text derives from its bounds), $m + i \le n_a + 1$ (the text's $j + l - 1 \le n_i$) and $i \le k$; the upper bound $n_i \le k$ of $(\mathrm S_k)$ plays no role. That the new indices satisfy the conditions ("one checks" in the 2010 paper) is checked for each of the three kinds of terms.
- The sums in the tangent map are handled by the sum rule for $\mathrm{sc}^k$ maps and the Leibniz rule by the derivative of the multilinear evaluation (V1.39).

### V1.39. Sums of sc^k maps; the derivative of multilinear evaluation

*not in the book* · sum = addition after the pairing · Leibniz rule for $(A, h) \mapsto A h$

**HWZ (2010 paper, Proposition 2.4, pp. 52–53 (the terms of $T^{k+1}f$ and the derivative (11))).** The proof of Proposition 1.19 in the 2010 paper shows that $T^{k+1}f$ is $\mathrm{sc}^1$ by showing that "any of the terms" of its components is, i.e. uses that a sum of $\mathrm{sc}^1$ maps is $\mathrm{sc}^1$; and it obtains the derivative (11) of $(x, h_1, \dots, h_j) \mapsto d^jf(x)(h_1, \dots, h_j)$ by the product rule, without stating either.

**Proved in Lean.** On an sc-domain, the constant map $0$ is $\mathrm{sc}^k$, the sum of two $\mathrm{sc}^k$ maps is $\mathrm{sc}^k$ and so is any finite sum. The evaluation $(A, h) \mapsto A(h_1, \dots, h_n)$ of continuous multilinear maps is differentiable at every $(A, h)$ with derivative $(B, \eta) \mapsto B(h) + \sum_a A(h \text{ with } h_a := \eta_a)$.

- `Polyfold.IsSck.scPair` — Polyfold/Chapter2/StrongBundle.lean, line 156
- `Polyfold.IsSck.zero` — Polyfold/Chapter1/LevelsWeak.lean, line 244
- `Polyfold.IsSck.add` — Polyfold/Chapter1/LevelsWeak.lean, line 248
- `Polyfold.IsSck.sum` — Polyfold/Chapter1/LevelsWeak.lean, line 254
- `Polyfold.hasFDerivAt_cmm_eval` — Polyfold/Chapter1/LevelsWeak.lean, line 279

*What differs.*
- The sum $g_1 + g_2$ is the composite of the pairing $(g_1, g_2)$, which is $\mathrm{sc}^k$ (one direction of the exposition's Lemma 3.G(3), proved in the Chapter 2 files), with the sc-operator $(y_1, y_2) \mapsto y_1 + y_2$, which is sc-smooth, so the chain rule (V1.20) applies. Scalar multiples, the rest of "linear combinations", are not needed.
- The derivative of the evaluation is written through Mathlib's derivative of a continuous multilinear map in its arguments and the linearity in $A$; Mathlib has no lemma in this form.

## Chapter 2

*HWZ Chapter 2 §§2.1–2.6, preprint pp. 18–60: sc-smooth retractions and retracts, M-polyfolds, the degeneracy index, tame M-polyfolds and their faces, fibred products, strong bundles*

### V2.1. Sc-smooth retractions

*as in the book* · total map, values off $U$ ignored

**HWZ (§2.1, Definition 2.1, p. 18).** For a tuple $(U, C, E)$, $U$ relatively open in the partial quadrant $C$ of $E$, an sc-smooth map $r : U \to U$ with $r \circ r = r$ is an *sc-smooth retraction* on $U$. After Definition 2.3: for $x \in U_1$ the chain rule gives $Dr(r(x)) \circ Dr(x) = Dr(x)$, so for $x \in O_1$, $Dr(x)$ is a projection.

**Proved in Lean.** An *sc-smooth retraction* on $C$ is a set $U \subseteq E_0$ relatively open in the partial quadrant $C$ and a map $r : E_0 \to E_0$ (only its values on $U$ matter) with $r(U) \subseteq U$, $r$ sc-smooth on $U$ and $r(r(x)) = r(x)$ for $x \in U$. Its retract is $O = r(U)$; $O \subseteq U$, $O$ is the fixed-point set of $r$ in $U$, and for $x \in O_1$ the derivative satisfies $Dr(x) \circ Dr(x) = Dr(x)$.

- `Polyfold.ScRetraction` — Polyfold/Chapter2/Retracts.lean, line 260
- `Polyfold.ScRetraction.retract` — Polyfold/Chapter2/Retracts.lean, line 281
- `Polyfold.ScRetraction.mem_retract_iff` — Polyfold/Chapter2/Retracts.lean, line 293
- `Polyfold.ScRetraction.apply_eq_self_of_mem_retract` — Polyfold/Chapter2/Retracts.lean, line 289
- `Polyfold.ScRetraction.lvlSet_retract_subset` — Polyfold/Chapter2/Retracts.lean, line 303
- `Polyfold.ScRetraction.scDeriv_comp_self` — Polyfold/Chapter2/Retracts.lean, line 358

*What differs.*
- The retraction is a total map $E_0 \to E_0$ with $r(U) \subseteq U$ as a field; only its values on $U$ enter any statement.
- The remark that $Dr(x)$ is a projection for $x \in O_1$ is `ScRetraction.scDeriv_comp_self`, by the chain rule applied to $r \circ r = r$.

### V2.2. Sc-smooth retracts

*as in the book*

**HWZ (§2.1, Definition 2.3, p. 18).** A tuple $(O, C, E)$ is an *sc-smooth retract* if $O = r(U)$ for an sc-smooth retraction $r : U \to U$ on a relatively open subset $U$ of the partial quadrant $C$.

**Proved in Lean.** $(O, C, E)$ is an sc-smooth retract if $O$ is the retract $r(U)$ of some sc-smooth retraction on $C$. Every relatively open $U \subseteq C$ is a retract, with $r = \mathrm{id}$. A *local model* is a triple $(E, C, O)$ with $C$ a partial quadrant and $(O, C, E)$ a retract.

- `Polyfold.IsScRetract` — Polyfold/Chapter2/Retracts.lean, line 390
- `Polyfold.ScRetraction.isScRetract` — Polyfold/Chapter2/Retracts.lean, line 393
- `Polyfold.ScRetraction.id` — Polyfold/Chapter2/Retracts.lean, line 424
- `Polyfold.IsRelOpenInQuadrant.isScRetract` — Polyfold/Chapter2/Retracts.lean, line 432
- `Polyfold.LocalModel` — Polyfold/Chapter2/Retracts.lean, line 842

*What differs.*
- As in the text. The local model packages the triple used by M-polyfold charts.

### V2.3. Proposition 2.4: the tangent of a retract does not depend on the retraction

*as in the book* · proved from $r(U) \subseteq r'(U')$

**HWZ (§2.1, Proposition 2.4, p. 19).** If $r : U \to U$ and $r' : U' \to U'$ are sc-smooth retractions on relatively open subsets of $C$ with $r(U) = r'(U') = O$, then $Tr(TU) = Tr'(TU')$.

**Proved in Lean.** For sc-smooth retractions $r$ on $U$ and $r'$ on $U'$ (both relatively open in $C$) with the same retract, $Tr(TU) = Tr'(TU')$. More precisely, $r(U) \subseteq r'(U')$ already gives $r' \circ r = r$ on $U$ and $Tr(TU) \subseteq Tr'(TU')$. $TO = Tr(TU)$ is the fixed-point set of $Tr$ in $TU$.

- `Polyfold.proposition_2_4` — Polyfold/Chapter2/Retracts.lean, line 464
- `Polyfold.ScRetraction.comp_eq_self_of_retract_subset` — Polyfold/Chapter2/Retracts.lean, line 440
- `Polyfold.ScRetraction.tangent_subset_of_retract_subset` — Polyfold/Chapter2/Retracts.lean, line 445
- `Polyfold.ScRetraction.tangent` — Polyfold/Chapter2/Retracts.lean, line 309
- `Polyfold.ScRetraction.mem_tangent_iff` — Polyfold/Chapter2/Retracts.lean, line 323

*What differs.*
- As in the text. The inclusion is proved under the weaker hypothesis $r(U) \subseteq r'(U')$ and applied twice.
- The text's step \"$Tr'(x, h) = (x, h)$\" is the fixed-point description of $Tr(TU)$, proved separately (`ScRetraction.mem_tangent_iff`).

### V2.4. Definition 2.5: the tangent $TO$ of a retract

*as in the book* · junk value $\emptyset$ off retracts

**HWZ (§2.1, Definition 2.5, p. 19).** The tangent of $(O, C, E)$ is $T(O, C, E) = (TO, TC, TE)$ with $TC = C^1 \oplus E$, $TE = E^1 \oplus E$ and $TO := Tr(TU)$ for any retraction $r$ onto $O$; explicitly $TO = \{(r(x), Dr(x)h) : x \in U_1, h \in E\}$. Definition 2.17: for $x \in O_1$, $T_xO = p^{-1}(x)$, the image of the projection $Dr(x)$.

**Proved in Lean.** $TO \subseteq E_1 \times E_0$ is $Tr(TU)$ for a chosen retraction onto $O$, and equals $Tr'(TU')$ for every other one; $TO = \{(r(x), Dr(x)h) : x \in U_1, h \in E_0\}$, and for $x \in O_1$, $(x, h) \in TO$ iff $h \in Dr(x)(E_0)$. The fibre $T_xO = \{h : (x, h) \in TO\}$ is the range of $Dr(x)$, a closed subspace of $E_0$.

- `Polyfold.retractTangent` — Polyfold/Chapter2/Retracts.lean, line 473
- `Polyfold.retractTangent_eq` — Polyfold/Chapter2/Retracts.lean, line 476
- `Polyfold.ScRetraction.mem_tangent_iff_exists` — Polyfold/Chapter2/Retracts.lean, line 378
- `Polyfold.ScRetraction.mem_tangent_iff_mem_range` — Polyfold/Chapter2/Retracts.lean, line 369
- `Polyfold.tangentSpace` — Polyfold/Chapter2/Retracts.lean, line 484
- `Polyfold.tangentSpace_eq_range` — Polyfold/Chapter2/Retracts.lean, line 488
- `Polyfold.tangentSpace_eq_coe_submodule` — Polyfold/Chapter2/Retracts.lean, line 496

*What differs.*
- `retractTangent E C O` is defined for every set $O$ (empty when $O$ is not a retract), by a choice of retraction; Proposition 2.4 makes the choice irrelevant (`retractTangent_eq`).
- That $TC$ is a partial quadrant in $TE$ and $TU$ relatively open in it is V2.8 (and V1.36).

### V2.5. Proposition 2.6: sc-smoothness on a retract is independent of the retraction

*hypotheses explicit* · (3) needs $f(O) \subseteq O'$

**HWZ (§2.1, Proposition 2.6, p. 20).** Let $f : O \to O'$ and $r : U \to U$, $s : V \to V$ two retractions onto $O$. (1) $f \circ r$ is sc-smooth iff $f \circ s$ is. (2) If so, $T(f \circ r) = T(f \circ s)$ on $TO$. (3) $T(f \circ r)$ maps $TO$ into $TO'$.

**Proved in Lean.** For retractions $r$, $s$ onto the same $O$: (1) if $f \circ r$ is sc-smooth on $U$ then $f \circ s$ is sc-smooth on $V$; (2) then $T(f \circ r) = T(f \circ s)$ on $Tr(TU)$; (3) if $f \circ r$ is sc-smooth and $f$ maps $O$ into the retract $O' = r'(U')$, then $T(f \circ r)$ maps $Tr(TU)$ into $Tr'(TU')$.

- `Polyfold.proposition_2_6_1` — Polyfold/Chapter2/Retracts.lean, line 516
- `Polyfold.proposition_2_6_2` — Polyfold/Chapter2/Retracts.lean, line 523
- `Polyfold.proposition_2_6_3` — Polyfold/Chapter2/Retracts.lean, line 540
- `Polyfold.ScRetraction.comp_comp_eqOn` — Polyfold/Chapter2/Retracts.lean, line 510

*What differs.*
- (1) is stated in one direction; the other is the same theorem with $r$ and $s$ exchanged.
- (3) assumes $f(O) \subseteq O'$, which the text's \"$f : O \to O'$\" contains.

### V2.6. Definition 2.7: sc-smooth maps between retracts and the tangent map

*restated* · "every $r$" instead of "one $r$" · $f(O) \subseteq O'$ a field

**HWZ (§2.1, Definition 2.7, pp. 20–21).** $f : O \to O'$ is *sc-smooth* if $f \circ r : U \to E'$ is sc-smooth for a retraction $r$ onto $O$; $Tf := T(f \circ r)|_{TO}$, which maps $TO$ into $TO'$ and does not depend on $r$. For $o \in O_1$, $Tf(o) : T_oO \to T_{f(o)}O'$ is the linearization.

**Proved in Lean.** $f : E_0 \to E'_0$ is sc-smooth between the retracts $(O, C, E)$ and $(O', C', E')$ if $f(O) \subseteq O'$ and $f \circ r$ is sc-smooth on $U$ for *every* retraction $r$ onto $O$; for an actual retract this is equivalent to the text's \"for one $r$\". $Tf$ is $T(f \circ r)$ for a chosen $r$; on $TO$ it equals $T(f \circ r)$ for every $r$ onto $O$, maps $TO$ into $TO'$, and $Tf(x, h) = (f(x), D(f \circ r)(x)h)$. Sc-smooth maps between retracts are continuous on $O$ and preserve the levels.

- `Polyfold.IsScSmoothRetractMap` — Polyfold/Chapter2/Retracts.lean, line 558
- `Polyfold.isScSmoothRetractMap_iff_exists` — Polyfold/Chapter2/Retracts.lean, line 565
- `Polyfold.retractTangentMap` — Polyfold/Chapter2/Retracts.lean, line 579
- `Polyfold.retractTangentMap_eqOn` — Polyfold/Chapter2/Retracts.lean, line 583
- `Polyfold.IsScSmoothRetractMap.tangentMap_mapsTo` — Polyfold/Chapter2/Retracts.lean, line 595
- `Polyfold.retractTangentMap_apply` — Polyfold/Chapter2/Retracts.lean, line 607
- `Polyfold.IsScSmoothRetractMap.continuousOn` — Polyfold/Chapter2/Retracts.lean, line 701
- `Polyfold.IsScSmoothRetractMap.mem_range_toBase` — Polyfold/Chapter2/Retracts.lean, line 709

*What differs.*
- The definition quantifies over all retractions onto $O$ and includes $f(O) \subseteq O'$; `isScSmoothRetractMap_iff_exists` recovers the text's form for a retract.
- The linearization $Tf(o)$ is the second component of $Tf(o, \cdot)$; it is not given a separate name.

### V2.7. Theorem 2.8: the chain rule for retracts

*hypotheses explicit* · $O$, $O'$ retracts

**HWZ (§2.1, Theorem 2.8, p. 21).** If $f : O \to O'$ and $g : O' \to O''$ are sc-smooth maps between sc-smooth retracts, then $g \circ f$ is sc-smooth and $T(g \circ f) = Tg \circ Tf$ (the text writes $(O'', C', E'')$ for $(O'', C'', E'')$).

**Proved in Lean.** Let $(O, C, E)$ and $(O', C', E')$ be retracts, $f$ sc-smooth $(O, C, E) \to (O', C', E')$ and $g$ sc-smooth $(O', C', E') \to (O'', C'', E'')$. Then $g \circ f$ is sc-smooth and $T(g \circ f) = Tg \circ Tf$ on $TO$. The identity, a retraction $U \to O$ and the inclusion $O \to U$ are sc-smooth, and sc-smoothness depends only on $f|_O$.

- `Polyfold.theorem_2_8` — Polyfold/Chapter2/Retracts.lean, line 665
- `Polyfold.IsScSmoothRetractMap.comp` — Polyfold/Chapter2/Retracts.lean, line 623
- `Polyfold.retractTangentMap_comp` — Polyfold/Chapter2/Retracts.lean, line 637
- `Polyfold.isScSmoothRetractMap_id` — Polyfold/Chapter2/Retracts.lean, line 674
- `Polyfold.ScRetraction.isScSmoothRetractMap` — Polyfold/Chapter2/Retracts.lean, line 679
- `Polyfold.IsScSmoothRetractMap.congr` — Polyfold/Chapter2/Retracts.lean, line 693

*What differs.*
- The source and middle sets are assumed to be retracts (the text's standing hypothesis); $O''$ need not be.
- The text gives no proof (\"follows from Theorem 1.21\"); the proof writes $(g \circ f) \circ r = (g \circ r') \circ (f \circ r)$ on $U$, which uses $r' \circ f \circ r = f \circ r$, and applies Theorem 1.21.

### V2.8. The tangent functor on retracts

*restated* · bundle structure not formalized · locality of $Tf$ proved

**HWZ (§2.1, after Theorem 2.8 and Definition 2.9, pp. 21–22).** $T$ is a functor $\mathcal R \to \mathcal R$: $(TO, TC, TE)$ is again a retract, $Tf : (TO, TC, TE) \to (TO', TC', TE')$, $Tf(x, h) = (f(x), Df(x)h)$, and $T(g \circ f) = Tg \circ Tf$. If $r$ is a retraction, $Tr : TU \to TU$ is a (bundle) retraction.

**Proved in Lean.** $TC$ is a partial quadrant in $TE$ and $TU$ is relatively open in $TC$; $Tr : TU \to TU$ is an sc-smooth retraction with image $TO$, so $(TO, TC, TE)$ is an sc-smooth retract. If $f$ is sc-smooth between retracts, so is $Tf : (TO, TC, TE) \to (TO', TC', TE')$; $T(\mathrm{id}) = \mathrm{id}$ on $TO$, and the chain rule is V2.7. $T(O \cap W) = TO \cap (W_1 \times E_0)$ for $W$ open, and $Tf$ computed on $O \cap W$ is $Tf$ computed on $O$.

- `Polyfold.IsPartialQuadrant.tangentSet` — Polyfold/Chapter2/TangentBundle.lean, line 120
- `Polyfold.IsRelOpenInQuadrant.tangentSet` — Polyfold/Chapter2/TangentBundle.lean, line 135
- `Polyfold.ScRetraction.tangentRetraction` — Polyfold/Chapter2/TangentBundle.lean, line 149
- `Polyfold.ScRetraction.tangentRetraction_retract` — Polyfold/Chapter2/TangentBundle.lean, line 164
- `Polyfold.IsScRetract.tangentSet` — Polyfold/Chapter2/TangentBundle.lean, line 169
- `Polyfold.LocalModel.tangent` — Polyfold/Chapter2/TangentBundle.lean, line 175
- `Polyfold.IsScSmoothRetractMap.tangent` — Polyfold/Chapter2/TangentBundle.lean, line 286
- `Polyfold.retractTangentMap_id` — Polyfold/Chapter2/TangentBundle.lean, line 255
- `Polyfold.retractTangent_inter_isOpen` — Polyfold/Chapter2/TangentBundle.lean, line 198
- `Polyfold.retractTangentMap_inter_isOpen` — Polyfold/Chapter2/TangentBundle.lean, line 266

*What differs.*
- The functor is stated as the two facts that make it one: $T$ sends retracts to retracts and sc-smooth maps to sc-smooth maps; functoriality is Theorem 2.8.
- The bundle structure of $TO \to O^1$ (Definition 2.9's category $\mathcal{BR}$) is not formalized (G.5); the fibrewise linearity of $Tf$ is the linearity of the derivative.
- The locality of $Tf$ under restriction to open subsets, used silently in Definitions 2.17–2.18, is proved here.

### V2.9. Proposition 2.10: open subsets and images of retractions are retracts

*restated* · $O' = O \cap W$, $W$ open in $E_0$

**HWZ (§2.2, Proposition 2.10, p. 23).** (1) An open subset $O'$ of a retract $O$ is a retract. (2) If $V \subseteq O$ is open and $s : V \to V$ is sc-smooth with $s \circ s = s$, then $s(V)$ is a retract.

**Proved in Lean.** (1) If $(O, C, E)$ is a retract and $W \subseteq E_0$ is open, $(O \cap W, C, E)$ is a retract, with the restriction of $r$ to $U \cap r^{-1}(W)$. (2) If $(V, C, E)$ is a retract and $s$ is sc-smooth $(V, C, E) \to (V, C, E)$ with $s \circ s = s$ on $V$, then $(s(V), C, E)$ is a retract, with the retraction $s \circ r$. Sc-smooth maps between retracts restrict to open subsets of the source, and sc-smoothness between retracts is a local property.

- `Polyfold.proposition_2_10_1` — Polyfold/Chapter2/Retracts.lean, line 765
- `Polyfold.proposition_2_10_2` — Polyfold/Chapter2/Retracts.lean, line 772
- `Polyfold.ScRetraction.restrict` — Polyfold/Chapter2/Retracts.lean, line 737
- `Polyfold.ScRetraction.restrict_retract` — Polyfold/Chapter2/Retracts.lean, line 754
- `Polyfold.IsScSmoothRetractMap.restrict` — Polyfold/Chapter2/Retracts.lean, line 791
- `Polyfold.IsScSmoothRetractMap.of_locally` — Polyfold/Chapter2/Retracts.lean, line 812
- `Polyfold.LocalModel.restrict` — Polyfold/Chapter2/Retracts.lean, line 854

*What differs.*
- \"An open subset $O'$ of $O$\" is written $O \cap W$ with $W$ open in $E_0$ (the subspace topology).
- In (2), $V$ is a retract by (1) in the text; here it is assumed to be one, which is how (2) is applied.
- The locality of sc-smoothness between retracts is not in the text; Definitions 2.13–2.14 need it (V2.12).

### V2.10. Definition 2.11: charts and their compatibility

*restated* · chart as a partial equivalence

**HWZ (§2.2, Definition 2.11, pp. 23–24).** A chart around $x$ in a space $X$ is $(V, \varphi, (O, C, E))$ with $V$ an open neighbourhood of $x$, $(O, C, E)$ an sc-smooth retract and $\varphi : V \to O$ a homeomorphism. Two charts are sc-smoothly compatible if $\psi \circ \varphi^{-1} : \varphi(V \cap V') \to \psi(V \cap V')$ and its inverse are sc-smooth (Definition 2.7); $\varphi(V \cap V')$ is a retract by Proposition 2.10(1).

**Proved in Lean.** A chart on $X$ is a local model $(O, C, E)$ and a partial equivalence $\varphi : X \rightharpoonup E_0$ with open source $V$, target $O$, continuous on $V$ with inverse continuous on $O$. The overlap $\varphi(V \cap V')$ is a retract; two charts are compatible if $\psi \circ \varphi^{-1}$ is sc-smooth from $(\varphi(V \cap V'), C, E)$ to $(\psi(V \cap V'), C', E')$ and $\varphi \circ \psi^{-1}$ back. A chart is compatible with itself and with its restrictions; compatibility is local: two charts compatible with every chart of a family covering $V \cap V'$ are compatible.

- `Polyfold.MChart` — Polyfold/Chapter2/MPolyfold.lean, line 92
- `Polyfold.MChart.overlap` — Polyfold/Chapter2/MPolyfold.lean, line 182
- `Polyfold.MChart.isScRetract_overlap` — Polyfold/Chapter2/MPolyfold.lean, line 186
- `Polyfold.MChart.transition` — Polyfold/Chapter2/MPolyfold.lean, line 193
- `Polyfold.MChart.Compatible` — Polyfold/Chapter2/MPolyfold.lean, line 205
- `Polyfold.MChart.compatible_self` — Polyfold/Chapter2/MPolyfold.lean, line 220
- `Polyfold.MChart.Compatible.restrict` — Polyfold/Chapter2/MPolyfold.lean, line 283
- `Polyfold.MChart.compatible_of_locally` — Polyfold/Chapter2/MPolyfold.lean, line 295

*What differs.*
- The chart is a partial equivalence $X \rightharpoonup E_0$; its inverse is a total function whose values off $O$ do not matter.
- `MChart.compatible_of_locally` (chain rule plus locality) is not in the text; it makes the maximal atlas of V2.12 an atlas.

### V2.11. Definition 2.12: sc-smooth atlases and their equivalence

*as in the book* · transitivity proved

**HWZ (§2.2, Definition 2.12, p. 24).** An sc-smooth atlas is a set of pairwise compatible charts covering $X$; two atlases are equivalent if their union is an atlas.

**Proved in Lean.** An atlas is a set of pairwise compatible charts whose sources cover $X$. Two atlases are equivalent iff their union is an atlas iff every chart of one is compatible with every chart of the other; the relation is an equivalence relation.

- `Polyfold.MAtlas` — Polyfold/Chapter2/MPolyfold.lean, line 361
- `Polyfold.MAtlas.Equiv` — Polyfold/Chapter2/MPolyfold.lean, line 371
- `Polyfold.MAtlas.equiv_iff` — Polyfold/Chapter2/MPolyfold.lean, line 374
- `Polyfold.MAtlas.Equiv.refl` — Polyfold/Chapter2/MPolyfold.lean, line 389
- `Polyfold.MAtlas.Equiv.symm` — Polyfold/Chapter2/MPolyfold.lean, line 391
- `Polyfold.MAtlas.Equiv.trans` — Polyfold/Chapter2/StrongBundleRestrict.lean, line 77
- `Polyfold.MAtlas.equivalence` — Polyfold/Chapter2/StrongBundleRestrict.lean, line 84

*What differs.*
- As in the text. Transitivity, which the “equivalence class” of Definition 2.13 presupposes without comment, is proved from the locality of compatibility (`MAtlas.Equiv.trans`; Findings, Chapter 2, item 41); the maximal atlas of V2.12 had made it unnecessary for the later notions. Updated in the third addendum of this page.

### V2.12. Definition 2.13: M-polyfolds

*restated* · one atlas represents its class · maximal atlas used throughout

**HWZ (§2.2, Definition 2.13, p. 24).** An M-polyfold is a Hausdorff paracompact topological space with an equivalence class of sc-smooth atlases.

**Proved in Lean.** An M-polyfold structure on a Hausdorff paracompact space $X$ is an sc-smooth atlas. Its *charts* are all charts compatible with that atlas (the maximal atlas); any two of them are compatible, restrictions of charts are charts, every point lies in a chart, and equivalent atlases have the same charts. A nonempty retract $(O, C, E)$ is an M-polyfold with the single chart $\mathrm{id}$.

- `Polyfold.MPolyfold` — Polyfold/Chapter2/MPolyfold.lean, line 399
- `Polyfold.MPolyfold.IsChart` — Polyfold/Chapter2/MPolyfold.lean, line 408
- `Polyfold.MPolyfold.IsChart.compatible` — Polyfold/Chapter2/MPolyfold.lean, line 414
- `Polyfold.MPolyfold.IsChart.restrict` — Polyfold/Chapter2/MPolyfold.lean, line 420
- `Polyfold.MPolyfold.isChart_congr` — Polyfold/Chapter2/MPolyfold.lean, line 425
- `Polyfold.MPolyfold.exists_isChart_mem_source` — Polyfold/Chapter2/MPolyfold.lean, line 437
- `Polyfold.LocalModel.toMPolyfold` — Polyfold/Chapter2/MPolyfold.lean, line 707

*What differs.*
- An equivalence class of atlases is represented by one atlas; every later notion is defined through the maximal atlas `IsChart`, which depends only on the class (`isChart_congr`).
- That charts compatible with an atlas are compatible with each other needs the locality of compatibility (V2.10); the text does not discuss it.

### V2.13. Definition 2.14: sc-smooth maps between M-polyfolds

*hypotheses explicit* · continuity a field · on open subsets $U$

**HWZ (§2.2, Definition 2.14, p. 24).** $f : X \to Y$ is sc-smooth if for charts $\varphi$ around $x$ and $\varphi'$ around $f(x)$ with $f(V) \subseteq V'$, $\varphi' \circ f \circ \varphi^{-1} : O \to O'$ is sc-smooth (Definition 2.7); \"the definition does not depend on the choice of charts\".

**Proved in Lean.** $f$ is sc-smooth on an open $U \subseteq X$ if it is continuous on $U$ and for all charts $\varphi$ of $X$, $\psi$ of $Y$ and every open $V \subseteq U \cap \operatorname{dom}\varphi$ with $f(V) \subseteq \operatorname{dom}\psi$, $\psi \circ f \circ \varphi^{-1}$ is sc-smooth from $(\varphi(V), C, E)$ into $(O', C', E')$; sc-smooth means sc-smooth on $X$. It suffices to check one pair of charts around each point (the text's independence of charts). The identity is sc-smooth and compositions of sc-smooth maps are sc-smooth.

- `Polyfold.MPolyfold.IsScSmoothOn` — Polyfold/Chapter2/MPolyfold.lean, line 533
- `Polyfold.MPolyfold.IsScSmoothMap` — Polyfold/Chapter2/MPolyfold.lean, line 542
- `Polyfold.MPolyfold.IsScSmoothOn.of_exists_charts` — Polyfold/Chapter2/LevelPolyfold.lean, line 190
- `Polyfold.MPolyfold.isScSmoothMap_id` — Polyfold/Chapter2/MPolyfold.lean, line 564
- `Polyfold.MPolyfold.IsScSmoothOn.comp` — Polyfold/Chapter2/MPolyfold.lean, line 591
- `Polyfold.MPolyfold.IsScSmoothMap.comp` — Polyfold/Chapter2/MPolyfold.lean, line 650

*What differs.*
- Continuity of $f$ is a field: the text's charts with $f(V) \subseteq V'$ exist around every point only if $f$ is continuous.
- The definition quantifies over all charts and all open $V$; `IsScSmoothOn.of_exists_charts` is the text's remark that one pair of charts per point suffices.
- Maps on open subsets are included because germs and sub-M-polyfolds need them.

### V2.14. The filtration $X_m$ of an M-polyfold

*restated* · topology generated, basis not proved

**HWZ (§2.2, after Definition 2.14, p. 25).** $x$ is on level $m$ if $\varphi(x) \in O_m$ for a chart around $x$ (\"independent of the choice of a chart\"); $X_m$ is the set of such points, topologized by the basis of sets $\varphi^{-1}(W)$, $W$ open in $O_m$; $X = X_0 \supset X_1 \supset \cdots \supset X_\infty = \bigcap X_m$.

**Proved in Lean.** $X_m$ is the set of $x$ with $\varphi(x) \in \iota_m(E_m)$ for some chart $\varphi$ around $x$, and then for every chart around $x$. $X_0 = X$, $X_{m+1} \subseteq X_m$, $X_\infty = \bigcap_m X_m$. $X_m$ carries the topology generated by the sets $\{x \in V : \varphi(x) \in W\}$, $W$ open in $E_m$; with it the inclusion $X_m \to X$ is continuous, $X_m$ is Hausdorff, and $x \mapsto \varphi(x)$ embeds $V_m = V \cap X_m$ into $E_m$.

- `Polyfold.MPolyfold.levelSet` — Polyfold/Chapter2/MPolyfold.lean, line 445
- `Polyfold.MPolyfold.mem_levelSet_iff` — Polyfold/Chapter2/MPolyfold.lean, line 450
- `Polyfold.MPolyfold.levelSet_zero` — Polyfold/Chapter2/MPolyfold.lean, line 460
- `Polyfold.MPolyfold.levelSet_succ_subset` — Polyfold/Chapter2/MPolyfold.lean, line 466
- `Polyfold.MPolyfold.smoothSet` — Polyfold/Chapter2/MPolyfold.lean, line 474
- `Polyfold.MPolyfold.levelTopology` — Polyfold/Chapter2/MPolyfold.lean, line 499
- `Polyfold.MPolyfold.Level` — Polyfold/Chapter2/LevelPolyfold.lean, line 265
- `Polyfold.MPolyfold.continuous_levelVal` — Polyfold/Chapter2/LevelPolyfold.lean, line 294
- `Polyfold.MPolyfold.isEmbedding_levelLift` — Polyfold/Chapter2/Metrizable.lean, line 449

*What differs.*
- The topology is the one *generated* by the text's family; that the family is a basis (closed under finite intersections) is not needed and not proved.
- \"$\varphi : V_m \to O_m$ is a homeomorphism\" is `MPolyfold.isEmbedding_levelLift`.

### V2.15. Lemma 2.15: the inclusions $X_{m+1} \to X_m$ are continuous

*as in the book*

**HWZ (§2.2, Lemma 2.15, p. 25).** The inclusion $i : X_{m+1} \to X_m$ is continuous for every $m \ge 0$.

**Proved in Lean.** For every $m$, the inclusion $X_{m+1} \to X_m$ is continuous for the topologies of V2.14.

- `Polyfold.lemma_2_15` — Polyfold/Chapter2/MPolyfold.lean, line 507
- `Polyfold.MPolyfold.levelIncl` — Polyfold/Chapter2/MPolyfold.lean, line 503

*What differs.*
- As in the text: the preimage of a generating set $\varphi^{-1}(W)$ is the generating set $\varphi^{-1}(\mathrm{incl}_m^{-1}(W))$.

### V2.16. The level $X^1$ is an M-polyfold

*narrower* · $m = 1$ only

**HWZ (§2.2, after Definition 2.14, p. 25).** $(V_m, \varphi, (O_m, C_m, E_m))$ is a chart on $X_m$; any two such charts are sc-smoothly compatible, and they form an atlas on $X_m$.

**Proved in Lean.** For $m = 1$: a retraction $r$ on $U$ restricts to an sc-smooth retraction of $U^1 \subseteq C^1 \subseteq E^1$ with retract $O^1$, and an sc-smooth map between retracts induces an sc-smooth map $O^1 \to O'^1$. For every chart $\varphi$ of $X$, $(V_1, \varphi, (O^1, C^1, E^1))$ is a chart of $X_1$; any two are compatible; they form an atlas, and with it $X_1$ is an M-polyfold $X^1$ (its paracompactness is Theorem 2.16, V2.17).

- `Polyfold.ScRetraction.shift` — Polyfold/Chapter2/LevelPolyfold.lean, line 93
- `Polyfold.ScRetraction.shift_retract` — Polyfold/Chapter2/LevelPolyfold.lean, line 112
- `Polyfold.IsScRetract.shift` — Polyfold/Chapter2/LevelPolyfold.lean, line 125
- `Polyfold.LocalModel.shift` — Polyfold/Chapter2/LevelPolyfold.lean, line 131
- `Polyfold.IsScSmoothRetractMap.shift` — Polyfold/Chapter2/LevelPolyfold.lean, line 162
- `Polyfold.MPolyfold.levelChart` — Polyfold/Chapter2/LevelPolyfold.lean, line 347
- `Polyfold.MPolyfold.levelChart_compatible` — Polyfold/Chapter2/LevelPolyfold.lean, line 469
- `Polyfold.MPolyfold.levelAtlas` — Polyfold/Chapter2/LevelPolyfold.lean, line 490
- `Polyfold.MPolyfold.shift` — Polyfold/Chapter2/LevelPolyfold.lean, line 503
- `Polyfold.MPolyfold.shift_isChart` — Polyfold/Chapter2/LevelPolyfold.lean, line 506
- `Polyfold.MPolyfold.mem_shift_levelSet_iff` — Polyfold/Chapter5/StrongBundleShift.lean, line 304

*What differs.*
- Only $X_1$ is made an M-polyfold; $X_m$ for $m \ge 2$ is reached as the iterate $(X^1)^1 \cdots$. Its points are those of $X_m$: $(X^1)_m = X_{m+1}$ as sets (`MPolyfold.mem_shift_levelSet_iff`, fourth addendum of this page); that its topology and charts are those of $X_m$ (V2.14) is not formalized (G.6).
- The text's \"by Proposition 1.17\" is `IsScSmoothRetractMap.shift`, Proposition 1.17 for retracts.
- `MPolyfold.shift` takes $X_1$ paracompact as an instance argument, which Theorem 2.16 now supplies (`MPolyfold.paracompactSpace_level`).

### V2.17. Theorem 2.16: $X$, $X_m$ and $X_\infty$ are metrizable

*hypotheses explicit* · no added hypothesis · topology of $X_\infty$ defined · Smirnov via pulled-back partitions

**HWZ (§2.2, Theorem 2.16, p. 25 (proof §2.6.2, pp. 56–58)).** For every $m \ge 0$ the space $X_m$ is metrizable, in particular paracompact; $X_\infty$ is metrizable. The proof uses Smirnov's theorem (2.55), Lemma 2.56 and Proposition 2.57.

**Proved in Lean.** For an M-polyfold $X$: $X$ is metrizable; every level $X_m$ (topology of V2.14) is metrizable and paracompact; $X_\infty$, with the initial topology of the inclusions $X_\infty \to X_m$, is metrizable. Every subset of $X$, in particular every sub-M-polyfold, is paracompact.

- `Polyfold.theorem_2_16` — Polyfold/Chapter2/Metrizable.lean, line 560
- `Polyfold.MPolyfold.metrizableSpace` — Polyfold/Chapter2/Metrizable.lean, line 442
- `Polyfold.MPolyfold.metrizableSpace_level` — Polyfold/Chapter2/Metrizable.lean, line 520
- `Polyfold.MPolyfold.paracompactSpace_level` — Polyfold/Chapter2/Metrizable.lean, line 526
- `Polyfold.MPolyfold.SmoothLevel` — Polyfold/Chapter2/Metrizable.lean, line 531
- `Polyfold.MPolyfold.smoothLevel_topology_eq` — Polyfold/Chapter2/Metrizable.lean, line 542
- `Polyfold.MPolyfold.metrizableSpace_smoothLevel` — Polyfold/Chapter2/Metrizable.lean, line 551
- `Polyfold.MPolyfold.paracompactSpace_subtype` — Polyfold/Chapter2/Metrizable.lean, line 569

*What differs.*
- No hypothesis is added. The text's route needs $X_m$ regular for Proposition 2.57 and does not check it; the formal proof avoids Lemma 2.56 and Proposition 2.57 altogether.
- Proof: a partition of unity of the paracompact Hausdorff $X$, subordinate to the chart domains and pulled back to $X_m$ along the continuous inclusion, gives an explicit metric (`metrizableSpace_of_pullback`); paracompactness follows by Stone's theorem.
- The text never defines the topology of $X_\infty$; it is taken to be the initial topology of the inclusions, which is what the text's metric $\sum 2^{-m} d_m/(1 + d_m)$ induces.

### V2.18. Definition 2.17: tangent vectors in a chart

*restated* · equivalence relation proved · transport via the chain rule

**HWZ (§2.2, Definition 2.17, pp. 25–26).** For $x \in O_1$, $T_xO = p^{-1}(x)$, the image of $Dr(x)$. Tuples $(x, V, \varphi, (O, C, E), h)$ with $x \in X_1$, $\varphi$ a chart around $x$ and $h \in T_{\varphi(x)}O$ are equivalent, $(x, \varphi, h) \sim (x', \psi, h')$, if $x = x'$ and $T(\varphi \circ \psi^{-1})(\psi(x))h' = h$.

**Proved in Lean.** A tangent tuple is $(x, \varphi, h)$ with $x \in X_1$, $\varphi$ a chart of the structure around $x$ and $(\varphi(x), h) \in TO$. Its transport to another chart $\psi$ around $x$ is $T(\psi \circ \varphi^{-1})(\varphi(x), h)$, computed on the overlap retract; transporting to $\varphi$ itself does nothing, transports land in $TO'$ over $\psi(x)$, and transporting to $\psi$ and then to $\chi$ is transporting to $\chi$. Two tuples are equivalent if their points agree and the transport of the first to the chart of the second is the second; this is an equivalence relation.

- `Polyfold.MPolyfold.TangentPre` — Polyfold/Chapter2/TangentBundle.lean, line 355
- `Polyfold.MPolyfold.TangentPre.transport` — Polyfold/Chapter2/TangentBundle.lean, line 399
- `Polyfold.MPolyfold.TangentPre.transport_self` — Polyfold/Chapter2/TangentBundle.lean, line 403
- `Polyfold.MPolyfold.TangentPre.transport_mem` — Polyfold/Chapter2/TangentBundle.lean, line 411
- `Polyfold.MPolyfold.TangentPre.transport_transport` — Polyfold/Chapter2/TangentBundle.lean, line 443
- `Polyfold.MPolyfold.TangentPre.Rel` — Polyfold/Chapter2/TangentBundle.lean, line 502
- `Polyfold.MPolyfold.TangentPre.Rel.symm` — Polyfold/Chapter2/TangentBundle.lean, line 512
- `Polyfold.MPolyfold.TangentPre.Rel.trans` — Polyfold/Chapter2/TangentBundle.lean, line 518
- `Polyfold.MPolyfold.TangentPre.setoid` — Polyfold/Chapter2/TangentBundle.lean, line 522

*What differs.*
- The text does not check that the relation is an equivalence relation; it is, by the chain rule on the triple overlap and the locality of $Tf$ (`TangentPre.transport_transport`).
- The relation is written with the transport in the direction $\varphi \to \psi$, $T(\psi \circ \varphi^{-1})(\varphi(x), h) = (\psi(x), h')$; it is the text's relation read from the other side.

### V2.19. Definition 2.18: the tangent space $TX$

*narrower* · no vector space on $T_xX$

**HWZ (§2.2, Definition 2.18, pp. 26–27).** $TX$ is the set of equivalence classes $[(x, \varphi, h)]$, $T_xX$ the classes over $x \in X_1$, a vector space; $TV$ is the set of classes over $V$ and $T\varphi : TV \to TO$, $[(x, \varphi, h)] \mapsto (\varphi(x), h)$, is linear on fibres. $TX$ is topologized by the sets $(T\varphi)^{-1}(W)$, $W$ open in $TO$.

**Proved in Lean.** $TX$ is the quotient of the tangent tuples by the equivalence of V2.18, with the projection $p : TX \to X_1$ and the fibres $T_xX = p^{-1}(x)$. For a chart $\varphi$, $TV = p^{-1}(V_1)$ and $T\varphi : TV \to TO$ sends a class to its transport to $\varphi$; $T\varphi[(x, \varphi, h)] = (\varphi(x), h)$, $T\varphi$ is injective on $TV$ with inverse $a \mapsto [(\varphi^{-1}(a), \varphi, a_2)]$, and $T\psi \circ (T\varphi)^{-1} = T(\psi \circ \varphi^{-1})$ on $T(\varphi(V \cap V'))$. The topology is generated by the sets $\{\alpha \in TV : T\varphi(\alpha) \in W\}$.

- `Polyfold.MPolyfold.TangentSpace` — Polyfold/Chapter2/TangentBundle.lean, line 530
- `Polyfold.MPolyfold.tangentProj` — Polyfold/Chapter2/TangentBundle.lean, line 560
- `Polyfold.MPolyfold.tangentFiber` — Polyfold/Chapter2/TangentBundle.lean, line 567
- `Polyfold.MPolyfold.tangentChartSet` — Polyfold/Chapter2/TangentBundle.lean, line 579
- `Polyfold.MPolyfold.tangentChartMap` — Polyfold/Chapter2/TangentBundle.lean, line 586
- `Polyfold.MPolyfold.tangentChartMap_mk_self` — Polyfold/Chapter2/TangentBundle.lean, line 600
- `Polyfold.MPolyfold.tangentChartMap_injOn` — Polyfold/Chapter2/TangentBundle.lean, line 617
- `Polyfold.MPolyfold.tangentChartMap_mk_ofVec` — Polyfold/Chapter2/TangentBundle.lean, line 665
- `Polyfold.MPolyfold.tangentChartMap_mk_ofVec_of_mem` — Polyfold/Chapter2/TangentBundle.lean, line 682
- `Polyfold.MPolyfold.tangentBasis` — Polyfold/Chapter2/TangentBundle.lean, line 719

*What differs.*
- The vector space structure of $T_xX$ and its Banach (resp. sc-Banach) structure are not formalized (G.7); $T_xX$ is a set, identified with $T_{\varphi(x)}O$ by $T\varphi$.
- The topology is the one generated by the text's family; that it is a basis is not needed.

### V2.20. Proposition 2.19: $TX$ is Hausdorff and metrizable; $p$ is continuous

*narrower* · openness of $p$ not proved · (3) no added hypothesis

**HWZ (§2.2, Proposition 2.19, p. 27 (proof §2.6.3, pp. 58–60)).** (1) The family $\mathcal B$ is a basis of a Hausdorff topology on $TX$. (2) $p : TX \to X_1$ is continuous and open. (3) $TX$ is metrizable, hence paracompact.

**Proved in Lean.** (1) $TX$ is Hausdorff. (2) $p : TX \to X_1$ is continuous; so is $TX \to X$. (3) $TX$ is metrizable and paracompact. The sets $TV$ are open in $TX$.

- `Polyfold.MPolyfold.continuous_tangentProj` — Polyfold/Chapter2/TangentBundle.lean, line 738
- `Polyfold.MPolyfold.continuous_levelVal_tangentProj` — Polyfold/Chapter2/TangentBundle.lean, line 755
- `Polyfold.MPolyfold.isOpen_tangentChartSet` — Polyfold/Chapter2/TangentBundle.lean, line 733
- `Polyfold.MPolyfold.metrizableSpace_tangentSpace` — Polyfold/Chapter2/Metrizable.lean, line 574
- `Polyfold.MPolyfold.paracompactSpace_tangentSpace` — Polyfold/Chapter2/Metrizable.lean, line 586
- `Polyfold.proposition_2_19_3` — Polyfold/Chapter2/Metrizable.lean, line 591

*What differs.*
- (1): Hausdorffness is an instance (`T2Space P.TangentSpace`); the basis property is not needed.
- (2): openness of $p$ is not proved (it is not used); continuity is. The exposition's proof of openness (§8.3) is not formalized (G.8).
- (3) is proved like Theorem 2.16, pulling a partition of unity of $X$ back along $TX \to X_1 \to X$; the text's argument via Proposition 2.57 is not used.

### V2.21. $TX$ is an M-polyfold and $p : TX \to X^1$ is sc-smooth

*narrower* · bundle structure not formalized

**HWZ (§2.2, after Proposition 2.19, p. 27).** $T\varphi : TV \to TO$ is a homeomorphism; $T\varphi' \circ (T\varphi)^{-1} = T(\varphi' \circ \varphi^{-1})$ (formula (5)) is sc-smooth; the charts $(TV, T\varphi, (TO, TC, TE))$ form an atlas, $TX$ is an M-polyfold, and $p : TX \to X_1$ is an sc-smooth M-polyfold bundle.

**Proved in Lean.** For a chart $\varphi$ of $X$, $(TV, T\varphi, (TO, TC, TE))$ is a chart of $TX$; $T\varphi(TV \cap TV') = T(\varphi(V \cap V'))$ and $T\varphi' \circ (T\varphi)^{-1} = T(\varphi' \circ \varphi^{-1})$ there (formula (5)); any two such charts are compatible, they form an atlas, and $TX$ is an M-polyfold. The projection $TO \to O^1$ is sc-smooth between retracts, and $p : TX \to X^1$ is sc-smooth.

- `Polyfold.MPolyfold.tangentChart` — Polyfold/Chapter2/TangentBundle.lean, line 804
- `Polyfold.MPolyfold.tangentChart_overlap` — Polyfold/Chapter2/TangentBundle.lean, line 887
- `Polyfold.MPolyfold.tangentChart_transition` — Polyfold/Chapter2/TangentBundle.lean, line 910
- `Polyfold.MPolyfold.tangentChart_compatible` — Polyfold/Chapter2/TangentBundle.lean, line 923
- `Polyfold.MPolyfold.tangentAtlas` — Polyfold/Chapter2/TangentBundle.lean, line 939
- `Polyfold.MPolyfold.tangentPolyfold` — Polyfold/Chapter2/TangentBundle.lean, line 951
- `Polyfold.MPolyfold.isScSmoothRetractMap_tangent_fst` — Polyfold/Chapter2/TangentBundle.lean, line 962
- `Polyfold.MPolyfold.tangentProj_isScSmooth` — Polyfold/Chapter2/TangentBundle.lean, line 978

*What differs.*
- \"Sc-smooth M-polyfold bundle\" is read as: $p$ is sc-smooth; the fibrewise linear structure is not formalized (G.7).
- `tangentPolyfold` and `tangentProj_isScSmooth` take the paracompactness of $TX$ and $X_1$ as instance arguments, supplied by V2.17 and V2.20.

### V2.22. The tangent map $Tf : TX \to TY$ and the chain rule

*not in the book* · defined only implicitly in the text

**HWZ (§2.2–§2.3, the tangent functor on M-polyfolds (used in Proposition 2.21(4), Definition 2.38), p. 21).** The text uses $Tf$ for sc-smooth maps between M-polyfolds (Proposition 2.21(4), Definition 2.38) without defining it; it defines $Tf$ between retracts and calls $T$ a functor.

**Proved in Lean.** For $f : X \to Y$ sc-smooth, $Tf[(x, \varphi, h)] := [(f(x), \psi, T(\psi \circ f \circ \varphi^{-1})(\varphi(x), h)_2)]$ for a chart $\psi$ around $f(x)$ is well defined (independent of $\psi$ and of the representative); $p \circ Tf = f \circ p$, $Tf(T_xX) \subseteq T_{f(x)}Y$, in charts $T\psi \circ Tf = T(\psi \circ f \circ \varphi^{-1}) \circ T\varphi$; $T(\mathrm{id}) = \mathrm{id}$, $T(g \circ f) = Tg \circ Tf$, and $Tf$ is continuous and sc-smooth $TX \to TY$. Sc-smooth maps preserve the levels $X_m$.

- `Polyfold.MPolyfold.tangentMap` — Polyfold/Chapter2/TangentMap.lean, line 328
- `Polyfold.MPolyfold.tangentMap_mk` — Polyfold/Chapter2/TangentMap.lean, line 334
- `Polyfold.MPolyfold.levelVal_tangentProj_tangentMap` — Polyfold/Chapter2/TangentMap.lean, line 340
- `Polyfold.MPolyfold.tangentMap_mapsTo_fiber` — Polyfold/Chapter2/TangentMap.lean, line 361
- `Polyfold.MPolyfold.tangentChartMap_tangentMap` — Polyfold/Chapter2/TangentMap.lean, line 348
- `Polyfold.MPolyfold.tangentMap_id` — Polyfold/Chapter2/TangentMap.lean, line 375
- `Polyfold.MPolyfold.tangentMap_comp` — Polyfold/Chapter2/TangentMap.lean, line 393
- `Polyfold.MPolyfold.continuous_tangentMap` — Polyfold/Chapter2/TangentMap.lean, line 441
- `Polyfold.MPolyfold.tangentMap_isScSmooth` — Polyfold/Chapter2/TangentMap.lean, line 503
- `Polyfold.MPolyfold.IsScSmoothMap.mapsTo_levelSet` — Polyfold/Chapter2/TangentMap.lean, line 136

*What differs.*
- Not stated in the text; it is the tangent functor of §2.1 transported to M-polyfolds, and the text uses it from §2.3 on.
- Only maps sc-smooth on all of $X$ are treated.

### V2.23. Definition 2.20: sub-M-polyfolds

*as in the book*

**HWZ (§2.2, Definition 2.20, p. 28).** $A \subseteq X$ is a sub-M-polyfold if every $a \in A$ has an open neighbourhood $V$ and an sc-smooth retraction $r : V \to V$ with $r(V) = A \cap V$.

**Proved in Lean.** $A \subseteq X$ is a sub-M-polyfold if every $a \in A$ has an open $V \ni a$ and a map $r$ with $r(V) \subseteq V$, $r$ sc-smooth on $V$ (Definition 2.14), $r \circ r = r$ on $V$ and $r(V) = A \cap V$. $X$ is a sub-M-polyfold of itself.

- `Polyfold.MPolyfold.IsSubMPolyfold` — Polyfold/Chapter2/MPolyfold.lean, line 660
- `Polyfold.MPolyfold.isSubMPolyfold_univ` — Polyfold/Chapter2/MPolyfold.lean, line 665

*What differs.*
- As in the text, with \"sc-smooth retraction $V \to V$\" read through Definition 2.14 on the open set $V$.

### V2.24. Proposition 2.21 (1), (2): the M-polyfold structure of a sub-M-polyfold

*hypotheses explicit* · subspace topology on $A$ · paracompactness: instance argument

**HWZ (§2.2, Proposition 2.21 (1), (2), pp. 28–30).** A sub-M-polyfold $A$ has a natural M-polyfold structure for which (1) the inclusion $i : A \to X$ is sc-smooth and a homeomorphism onto its image; (2) for every sc-smooth retraction $r : V \to V$ with $r(V) = A \cap V$, $i^{-1} \circ r : V \to A$ is sc-smooth.

**Proved in Lean.** Let $A$ be a sub-M-polyfold with the subspace topology. For a chart $\varphi$ of $X$ and data $(V, r)$ at a point, $W = V \cap \operatorname{dom}\varphi \cap r^{-1}(V \cap \operatorname{dom}\varphi)$ is open with $r(W) \subseteq W$, $r(W) = W \cap A$; $\rho = \varphi \circ r \circ \varphi^{-1}$ is sc-smooth and idempotent on $\varphi(W)$, so $\varphi(W \cap A)$ is a retract and $(\varphi|_{W \cap A}, (\varphi(W \cap A), C, E))$ is a chart of $A$. Any two such charts are compatible; they form an atlas and make $A$ an M-polyfold. (1) $i$ is sc-smooth (a homeomorphism onto its image by the choice of topology). (2) For any data $(V, r)$, $i^{-1} \circ r$ is sc-smooth on $V$. $A$ is paracompact (V2.17); for closed $A$ this is elementary.

- `Polyfold.MPolyfold.SubData` — Polyfold/Chapter2/SubMPolyfold.lean, line 93
- `Polyfold.MPolyfold.SubData.shrink` — Polyfold/Chapter2/SubMPolyfold.lean, line 120
- `Polyfold.MPolyfold.SubData.image_shrink` — Polyfold/Chapter2/SubMPolyfold.lean, line 138
- `Polyfold.MPolyfold.SubData.rho_isScSmooth` — Polyfold/Chapter2/SubMPolyfold.lean, line 150
- `Polyfold.MPolyfold.SubData.isScRetract_image` — Polyfold/Chapter2/SubMPolyfold.lean, line 175
- `Polyfold.MPolyfold.subChart` — Polyfold/Chapter2/SubMPolyfold.lean, line 204
- `Polyfold.MPolyfold.subChart_compatible` — Polyfold/Chapter2/SubMPolyfold.lean, line 265
- `Polyfold.MPolyfold.subAtlas` — Polyfold/Chapter2/SubMPolyfold.lean, line 310
- `Polyfold.MPolyfold.subPolyfold` — Polyfold/Chapter2/SubMPolyfold.lean, line 329
- `Polyfold.MPolyfold.subPolyfold_inclusion_isScSmooth` — Polyfold/Chapter2/SubMPolyfold.lean, line 338
- `Polyfold.MPolyfold.subPolyfold_retraction_isScSmooth` — Polyfold/Chapter2/SubMPolyfold.lean, line 364
- `Polyfold.IsScSmoothRetractMap.mono_source` — Polyfold/Chapter2/SubMPolyfold.lean, line 72
- `Polyfold.MPolyfold.paracompactSpace_of_isClosed` — Polyfold/Chapter2/SubMPolyfold.lean, line 323

*What differs.*
- The text does not say which topology $A$ carries; the subspace topology is taken, so (1)'s homeomorphism is by construction.
- `subPolyfold` takes `[ParacompactSpace A]` as an instance argument; it is discharged by `MPolyfold.paracompactSpace_subtype` (V2.17), which the text uses implicitly through Theorem 2.16.
- The compatibility argument $(\psi' \circ \psi^{-1}) \circ s'' = (\varphi' \circ \varphi^{-1}) \circ s''$ is `IsScSmoothRetractMap.mono_source`.

### V2.25. Proposition 2.21 (3), (4): the tangent space of a sub-M-polyfold, in a chart

*narrower* · in a chart only · $Ds(a)$ read as $D(s \circ r)(a)$

**HWZ (§2.2, Proposition 2.21 (3), (4), p. 30).** (3) At a smooth $a \in A$, $T_aA$ has an sc-complement in $T_aX$. (4) For a retraction $s : W \to W$ onto $W \cap A$, the induced map $W \to A$ is sc-smooth and $Ts(a)T_aX = T_aA$. Proof in coordinates: $t = s \circ r$, $T_aA = Dt(a)E$, $T_aO = Ds(a)Dr(a)E \oplus (I - Ds(a))Dr(a)E$.

**Proved in Lean.** In a chart: let $O = r(U)$, $s$ sc-smooth $(O, C, E) \to (O, C, E)$ with $s \circ s = s$, $t = s \circ r$ (a retraction onto $s(O)$), and $a \in s(O)_1$ smooth. Then $T_aO = Dr(a)E$, $T_a s(O) = Dt(a)E \subseteq T_aO$, both $Dt(a)E$ and $(Dr(a) - Dt(a))E$ are sc-subspaces of $E$, and on every level their level parts are disjoint with sum the level part of $T_aO$ (an sc-splitting $T_aO = T_aA \oplus (Dr(a) - Dt(a))E$). (4) $s : O \to s(O)$ is sc-smooth and $Ts$ maps $T_aO$ onto $T_a s(O)$ (for $a \in s(O)_1$).

- `Polyfold.ScRetraction.compRetraction` — Polyfold/Chapter2/Metrizable.lean, line 622
- `Polyfold.ScRetraction.compRetraction_retract` — Polyfold/Chapter2/Metrizable.lean, line 635
- `Polyfold.proposition_2_21_3` — Polyfold/Chapter2/Metrizable.lean, line 648
- `Polyfold.proposition_2_21_4` — Polyfold/Chapter2/Metrizable.lean, line 770

*What differs.*
- Stated and proved in a chart, as the text proves it; the transport to $T_aX$ by $T\varphi(a)$ is not formalized, since the fibres of $TX$ carry no sc-structure here (G.7).
- The text's $Ds(a)$ is $Dt(a) = D(s \circ r)(a)$; the sc-complement is $(Dr(a) - Dt(a))E$. The key identities $Dr(a)Dt(a) = Dt(a) = Dt(a)Dr(a)$ come from $r \circ t = t = t \circ r$.
- (4) holds at every $a \in s(O)_1$, smoothness is not needed.

### V2.26. Definition 2.22: the degeneracy index $d_X$

*restated* · all charts of the maximal atlas

**HWZ (§2.3, Definition 2.22, p. 31).** For a chart $\varphi$ around $x$, $d(x, \varphi) = d_C(\varphi(x))$; $d_X(x)$ is the minimum of $d(x, \varphi)$ over all smooth charts around $x$.

**Proved in Lean.** $d(x, \varphi) = d_C(\varphi(x))$ for a chart $\varphi$ around $x$; $d_X(x)$ is the infimum of $d(x, \varphi)$ over the charts of the structure (the maximal atlas) around $x$. It is attained, and $d_X(x) \le d(x, \varphi)$ for every chart; $d(\cdot, \varphi)$ is upper semicontinuous on the source of $\varphi$.

- `Polyfold.MPolyfold.chartDegIndex` — Polyfold/Chapter2/DegeneracyIndex.lean, line 644
- `Polyfold.MPolyfold.degIndex` — Polyfold/Chapter2/DegeneracyIndex.lean, line 648
- `Polyfold.MPolyfold.degIndex_le` — Polyfold/Chapter2/DegeneracyIndex.lean, line 651
- `Polyfold.MPolyfold.exists_isChart_degIndex_eq` — Polyfold/Chapter2/DegeneracyIndex.lean, line 656
- `Polyfold.MPolyfold.eventually_chartDegIndex_le` — Polyfold/Chapter2/DegeneracyIndex.lean, line 666

*What differs.*
- \"Smooth charts\" is read as the charts of the sc-smooth structure; the minimum is over the maximal atlas, so it depends only on the equivalence class.

### V2.27. Lemma 2.23: upper semicontinuity of $d_X$

*as in the book*

**HWZ (§2.3, Lemma 2.23, p. 31).** Every $x \in X$ has an open neighbourhood $U(x)$ with $d_X(y) \le d_X(x)$ for $y \in U(x)$.

**Proved in Lean.** For every $x$, $d_X(y) \le d_X(x)$ for all $y$ in a neighbourhood of $x$. Consequently $\{d_X < k\}$ is open and $\{d_X \ge k\}$ closed for every $k$.

- `Polyfold.lemma_2_23` — Polyfold/Chapter2/DegeneracyIndex.lean, line 677
- `Polyfold.eventually_degIndexWith_le` — Polyfold/Chapter2/DegeneracyIndex.lean, line 164
- `Polyfold.MPolyfold.isOpen_setOf_degIndex_lt` — Polyfold/Chapter2/Boundary.lean, line 94
- `Polyfold.MPolyfold.isClosed_setOf_le_degIndex` — Polyfold/Chapter2/Boundary.lean, line 100

*What differs.*
- As in the text (\"evident\"): a chart realizing $d_X(x)$ and the semicontinuity of $d_C$.

### V2.28. Proposition 2.24: $d_X$ is invariant under sc-diffeomorphism germs

*restated* · germ = sc-diffeomorphism of open sets

**HWZ (§2.3, Proposition 2.24, p. 31).** If $f : (U, x) \to (V, f(x))$ is a germ of sc-diffeomorphisms between M-polyfolds, then $d_X(x) = d_Y(f(x))$.

**Proved in Lean.** Let $U \subseteq X$, $V \subseteq Y$ be open, $f$ sc-smooth on $U$ with $f(U) \subseteq V$, $g$ sc-smooth on $V$ with $g(V) \subseteq U$, inverse to each other. Then $d_X(x) = d_Y(f(x))$ for $x \in U$. For a chart $\psi$ of $Y$, $\psi \circ f$ on $U \cap f^{-1}(\operatorname{dom}\psi)$ is a chart of $X$, with $d(x, \psi \circ f) = d(f(x), \psi)$.

- `Polyfold.MPolyfold.IsScDiffeoOn` — Polyfold/Chapter2/DegeneracyIndex.lean, line 707
- `Polyfold.proposition_2_24` — Polyfold/Chapter2/DegeneracyIndex.lean, line 840
- `Polyfold.MPolyfold.transportChart` — Polyfold/Chapter2/DegeneracyIndex.lean, line 746
- `Polyfold.MPolyfold.transportChart_isChart` — Polyfold/Chapter2/DegeneracyIndex.lean, line 784
- `Polyfold.MPolyfold.degIndex_le_of_isScDiffeoOn` — Polyfold/Chapter2/DegeneracyIndex.lean, line 832

*What differs.*
- A germ is represented by an sc-diffeomorphism between open neighbourhoods.
- The text's \"deduced immediately from the definitions\" is the construction of the transported chart and the proof that it belongs to the maximal atlas.

### V2.29. Definition 2.25: the boundary $\partial X$

*as in the book*

**HWZ (§2.3, Definition 2.25, p. 31).** $\partial X = \{x : d_X(x) \ge 1\}$ is the boundary; $X$ is without boundary if $d_X \equiv 0$.

**Proved in Lean.** $\partial X = \{d_X \ge 1\}$; $X$ is without boundary iff $d_X \equiv 0$ iff $\partial X = \emptyset$. $\partial X$ and the corners $\{d_X \ge 2\}$ are closed, the interior $\{d_X = 0\}$ is open, and sc-diffeomorphism germs preserve $\partial X$.

- `Polyfold.MPolyfold.boundary` — Polyfold/Chapter2/DegeneracyIndex.lean, line 684
- `Polyfold.MPolyfold.IsWithoutBoundary` — Polyfold/Chapter2/DegeneracyIndex.lean, line 687
- `Polyfold.MPolyfold.isWithoutBoundary_iff` — Polyfold/Chapter2/DegeneracyIndex.lean, line 689
- `Polyfold.MPolyfold.isClosed_boundary` — Polyfold/Chapter2/Boundary.lean, line 107
- `Polyfold.MPolyfold.isOpen_interior` — Polyfold/Chapter2/Boundary.lean, line 110
- `Polyfold.MPolyfold.corners` — Polyfold/Chapter2/Boundary.lean, line 118
- `Polyfold.MPolyfold.isClosed_corners` — Polyfold/Chapter2/Boundary.lean, line 120
- `Polyfold.MPolyfold.IsScDiffeoOn.mem_boundary_iff` — Polyfold/Chapter2/Boundary.lean, line 139

*What differs.*
- As in the text; the closedness statements and the invariance are consequences of V2.27 and V2.28 recorded for later use.

### V2.30. Lemma 2.26: $d_A \le d_X$ on a sub-M-polyfold

*hypotheses explicit* · paracompactness: instance argument

**HWZ (§2.3, Lemma 2.26, pp. 31–32).** If $A$ is a sub-M-polyfold of $X$, then $d_A(a) \le d_X(a)$ for all $a \in A$.

**Proved in Lean.** For a sub-M-polyfold $A$ with the structure of V2.24, $d_A(a) \le d_X(a)$ for every $a \in A$: the chart of $A$ built from a chart of $X$ realizing $d_X(a)$ has the same quadrant $C$ and the same image point.

- `Polyfold.lemma_2_26` — Polyfold/Chapter2/SubMPolyfold.lean, line 394

*What differs.*
- As in the text. The statement carries `[ParacompactSpace A]` (through `subPolyfold`), discharged by `MPolyfold.paracompactSpace_subtype`.

### V2.31. The subspaces $E_x$ and $\dim(E/E_x) = d_C(x)$

*restated* · through a presentation $T$

**HWZ (§2.3, p. 32).** For $C = [0, \infty)^k \oplus W$: $E_i = \{a_i = 0\}$, $E_I = \bigcap_{i \in I} E_i$, $I(x) = \{i : x \in E_i\}$, $E_x = E_{I(x)}$, $H_i = \{a_i \ge 0\}$ and $C_x = \bigcap_{i \in I(x)} H_i$.

**Proved in Lean.** For a presentation $T : E \cong \mathbb R^n \oplus W$ of $C$: $E_x = \{v : (Tv)_i = 0 \text{ whenever } (Tx)_i = 0\}$, a closed subspace with $\dim(E_0/E_x) = d_C(x)$; $C_x = \{v : (Tv)_i \ge 0 \text{ whenever } (Tx)_i = 0\}$ is closed and convex, with $E_x \subseteq C_x$. Points of $C$ of the same index on level $1$ (resp. smooth) accumulate at every $x \in C$; the level-$1$ points of $C_x$ and of the kernel of any finite-rank map are dense.

- `Polyfold.minimalSubspaceWith` — Polyfold/Chapter2/DegeneracyIndex.lean, line 129
- `Polyfold.mem_minimalSubspaceWith` — Polyfold/Chapter2/DegeneracyIndex.lean, line 133
- `Polyfold.isClosed_minimalSubspaceWith` — Polyfold/Chapter2/DegeneracyIndex.lean, line 143
- `Polyfold.finrank_quotient_minimalSubspaceWith` — Polyfold/Chapter2/DegeneracyIndex.lean, line 148
- `Polyfold.partialQuadrantAtWith` — Polyfold/Chapter2/Tame.lean, line 99
- `Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith` — Polyfold/Chapter2/Tame.lean, line 103
- `Polyfold.isClosed_partialQuadrantAtWith` — Polyfold/Chapter2/Boundary.lean, line 154
- `Polyfold.exists_tendsto_lvl1_degIndexWith` — Polyfold/Chapter2/DegeneracyIndex.lean, line 183
- `Polyfold.exists_tendsto_smooth_degIndexWith` — Polyfold/Chapter2/TameRetracts.lean, line 227
- `Polyfold.ScBanach.subset_closure_ker_inter_range_toBase` — Polyfold/Chapter2/DegeneracyIndex.lean, line 312
- `Polyfold.partialQuadrantAtWith_subset_closure` — Polyfold/Chapter2/Boundary.lean, line 165

*What differs.*
- Defined through a presentation of $C$, transported from the model; the text works in the model $E = \mathbb R^k \oplus W$.
- The densities are the content of the exposition's Lemma 3.A on level $1$, which is what the proofs of §2.3 use.

### V2.32. Definition 2.27: the reduced tangent space and the partial cone

*stronger* · defined at level-$1$ points · through a presentation $T$

**HWZ (§2.3, Definition 2.27, p. 33).** For a retract $(O, C, E)$ and a smooth $x \in O$: $C_xO := T_xO \cap C_x$ and $T^R_xO := T_xO \cap E_x$.

**Proved in Lean.** For a retraction $r$, a presentation $T$ of $C$ and $x \in O_1$: $T^R_xO = Dr(x)(E_0) \cap E_x$ (a subspace) and $C_xO = Dr(x)(E_0) \cap C_x$; $\dim(T_xO/T^R_xO)$ is the natural number $\dim(A/(A \cap B))$ for $A = T_xO$, $B = E_x$, and it is at most $d_C(x)$.

- `Polyfold.reducedTangentSpaceWith` — Polyfold/Chapter2/Tame.lean, line 182
- `Polyfold.partialConeWith` — Polyfold/Chapter2/Tame.lean, line 187
- `Polyfold.quotDim` — Polyfold/Chapter2/Boundary.lean, line 491
- `Polyfold.quotDim_inf_minimalSubspace_le` — Polyfold/Chapter2/Boundary.lean, line 503
- `Polyfold.quotDim_reducedTangentSpaceWith_le` — Polyfold/Chapter2/Boundary.lean, line 536

*What differs.*
- Defined at every $x \in O_1$, not only at smooth points; the statements of §2.3 hold there.
- Defined through a presentation of $C$, which is how the text computes.

### V2.33. Remark 2.28: $T^R_xO \subseteq C_xO \subseteq T_xO$

*stronger* · the negative claim is false (proved) · partial quadrant without tameness · Flor's theorem, the needed case

**HWZ (§2.3, Remark 2.28, p. 33).** $T^R_xO \subset C_xO \subset T_xO$; naively one might expect $C_xO$ to be a partial quadrant in $T_xO$, which in general is not the case.

**Proved in Lean.** $T^R_xO \subseteq C_xO$, and $C_xO \subseteq T_xO$ by definition. **The negative claim is false**: at every smooth point $x$ of every sc-smooth retract (no tameness), $T_xO$ and $T^R_xO$ are sc-subspaces of $E$ and $C_xO$ is a partial quadrant in the sc-Banach space $T_xO$ (with the sc-structure induced from $E$), of dimension $\operatorname{rank} M = \dim(T_xO/T^R_xO) \le d_C(x)$, $M$ the matrix of $Dr(x)$ on $E/E_x \cong \mathbb R^{I(x)}$. The core is Flor's theorem in the needed case: for a nonnegative idempotent matrix $M$, the cone $\operatorname{range} M \cap [0, \infty)^\iota$ is generated by linearly independent columns of $M$.

- `Polyfold.reducedTangentSpaceWith_subset_partialConeWith` — Polyfold/Chapter2/Tame.lean, line 192
- `Polyfold.remark_2_28_isPartialQuadrant` — Polyfold/Chapter2/PartialConeQuadrant.lean, line 655
- `Polyfold.remark_2_28_partialConeWith` — Polyfold/Chapter2/PartialConeQuadrant.lean, line 760
- `Polyfold.flor_nonnegRange_simplicial` — Polyfold/Chapter2/PartialConeQuadrant.lean, line 375
- `Polyfold.remark_2_28_quotient_simplicial` — Polyfold/Chapter2/PartialConeQuadrant.lean, line 565
- `Polyfold.ScRetraction.isScSubspace_reducedTangentSpaceWith` — Polyfold/Chapter2/PartialConeQuadrant.lean, line 589
- `Polyfold.partialConeWith_eq_image_scDeriv` — Polyfold/Chapter2/PartialConeQuadrant.lean, line 417

*What differs.*
- The inclusions as in the text.
- **The remark's negative claim does not hold in our reading (checked in Lean).** The remark asserts, without an example, that $C_xO$ is in general not a partial quadrant in $T_xO$; in our formalization it is one at every smooth point of every sc-smooth retract. $Dr(x)$ maps $C_x$ and $E_x$ into themselves, so $C_xO = Dr(x)(C_x)$, and modulo $T^R_xO$ it is the column cone of the nonnegative idempotent matrix $M$ of $Dr(x)$ on $E/E_x$; by Flor's theorem this cone is simplicial, and the sc-isomorphism $T_xO \cong \mathbb R^r \oplus T^R_xO$ of the proof of Theorem 2.31 carries $C_xO$ onto $[0, \infty)^r \oplus T^R_xO$. What can fail for a non-tame retract is only $r = d_C(x)$ (Theorem 2.31), which may well be what the remark means (Findings, Chapter 2, item 50; round-trip item V2.33, whose blind statement is proved false; formerly G.9).
- The verdict “stronger” records that the positive statement is proved for every retract, where the text proves it for tame ones (Proposition 2.36, V2.42) and asserts that it fails in general; formerly “as in the book” for the inclusions alone. Updated in the third addendum of this page.

### V2.34. The sign arguments (the content of Lemma 2.29)

*not in the book* · replaces the path formulation

**HWZ (§2.3, proof of Lemma 2.29, pp. 33–35).** For an sc-smooth path $\alpha$ in $O$ through $x$, the derivative of $\alpha_i \ge 0$ with $\alpha_i(0) = 0$ vanishes (two-sided paths) or is $\ge 0$ (one-sided paths); with $Dr(x)\dot\alpha(0) = \dot\alpha(0)$ this gives Lemma 2.29 (1), (2).

**Proved in Lean.** Let $f$ be sc¹ on $U$ (relatively open in $C$) with values in $C'$ and $x \in U_1$. Two-sided: for $v \in E_1 \cap E_x$, $Df(x)v \in E'_{f(x)}$, and by density $Df(x)(E_x) \subseteq E'_{f(x)}$. One-sided: for $v \in E_1 \cap C_x$, $Df(x)v \in C'_{f(x)}$, and $Df(x)(C_x) \subseteq C'_{f(x)}$. For a retraction, $Dr(x)E_x \subseteq E_x$ at every $x \in O_1$.

- `Polyfold.IsSc1With.deriv_mem_minimalSubspace_of_lvl1` — Polyfold/Chapter2/DegeneracyIndex.lean, line 264
- `Polyfold.IsSc1With.mapsTo_minimalSubspace` — Polyfold/Chapter2/DegeneracyIndex.lean, line 357
- `Polyfold.IsSc1With.deriv_mem_partialQuadrant_of_lvl1` — Polyfold/Chapter2/Boundary.lean, line 250
- `Polyfold.IsSc1With.mapsTo_partialQuadrant` — Polyfold/Chapter2/Boundary.lean, line 288
- `Polyfold.eventually_add_smul_mem_lvlSet` — Polyfold/Chapter2/DegeneracyIndex.lean, line 226
- `Polyfold.eventually_add_smul_mem_lvlSet_of_cone` — Polyfold/Chapter2/Boundary.lean, line 195
- `Polyfold.ScRetraction.scDeriv_mapsTo_minimalSubspace` — Polyfold/Chapter2/TameRetracts.lean, line 126

*What differs.*
- Lemma 2.29 itself, in its path formulation, is not formalized (G.10). Its derivative-level content, which is all Proposition 2.30 and Theorem 2.31 use, is formalized directly, for sc¹ maps and level-$1$ points.
- The text's \"the closure of $(T^R_xO)_\infty$ is $T^R_xO$\" becomes the density of level-$1$ points of $E_x$ and $C_x$ (V2.31).

### V2.35. Proposition 2.30: invariance of $T^R_xO$ and $C_xO$

*stronger* · level-$1$ points, sc¹ germs · not via Lemma 2.29

**HWZ (§2.3, Proposition 2.30, p. 35).** If $f : (O, x) \to (O', f(x))$ is a germ of sc-diffeomorphism between retracts, $x \in O_\infty$, then $Tf(x)T^R_xO = T^R_yO'$ and $Tf(x)C_xO = C_yO'$, $y = f(x)$.

**Proved in Lean.** Let $r$, $r'$ be retractions onto $O$, $O'$, and $F$, $G$ maps with $F \circ r$, $G \circ r'$ sc¹, $F(O) \subseteq O'$, $G(O') \subseteq O$, inverse to each other on $O$, $O'$ (a germ of sc-diffeomorphisms; every sc-smooth map between retracts with sc-smooth inverse is one). For $x \in O_1$ and $y = (F \circ r)(x)$, with $Tf(x) = D(F \circ r)(x)$: $Tf(x)(T^R_xO) = T^R_yO'$ and $Tf(x)(C_xO) = C_yO'$. Moreover $D(G \circ r')(y) \circ D(F \circ r)(x) = Dr(x)$, $D(F \circ r)(x) \circ D(G \circ r')(y) = Dr'(y)$.

- `Polyfold.ScRetraction.IsDiffeoGerm` — Polyfold/Chapter2/Boundary.lean, line 322
- `Polyfold.IsScSmoothRetractMap.isDiffeoGerm` — Polyfold/Chapter2/Boundary.lean, line 354
- `Polyfold.ScRetraction.IsDiffeoGerm.deriv_inv_deriv` — Polyfold/Chapter2/Boundary.lean, line 380
- `Polyfold.ScRetraction.IsDiffeoGerm.deriv_deriv_inv` — Polyfold/Chapter2/Boundary.lean, line 390
- `Polyfold.proposition_2_30_reduced` — Polyfold/Chapter2/Boundary.lean, line 426
- `Polyfold.proposition_2_30_cone` — Polyfold/Chapter2/Boundary.lean, line 457

*What differs.*
- Proved at every $x \in O_1$ and for germs that are only sc¹; the text has smooth $x$ and sc-smooth germs.
- Proved from the sign arguments (V2.34) and the two derivative identities, not from Lemma 2.29.

### V2.36. A retract is an M-polyfold

*restated* · $d_O$ by Definition 2.22

**HWZ (§2.3, before Theorem 2.31, p. 35).** A retract $(O, C, E)$ is an M-polyfold, and $d_O(x) = \min d_{C'}(\varphi(x))$ over germs of sc-diffeomorphisms $\varphi : (O, x) \to (O', \varphi(x))$ into retracts.

**Proved in Lean.** A nonempty retract $O$ is an M-polyfold on the subtype $O$ with the single chart $\mathrm{id}$; so is a nonempty relatively open $U \subseteq C$ (the text's $X_C$ for $U = C$). Its degeneracy index is Definition 2.22 for this structure; two compatible charts give a germ of sc-diffeomorphisms between overlap retracts.

- `Polyfold.LocalModel.selfChart` — Polyfold/Chapter2/MPolyfold.lean, line 678
- `Polyfold.LocalModel.toMPolyfold` — Polyfold/Chapter2/MPolyfold.lean, line 707
- `Polyfold.IsRelOpenInQuadrant.toMPolyfold` — Polyfold/Chapter2/MPolyfold.lean, line 716
- `Polyfold.IsRelOpenInQuadrant.selfChart_isChart` — Polyfold/Chapter2/DegeneracyIndex.lean, line 858
- `Polyfold.MChart.Compatible.isDiffeoGerm` — Polyfold/Chapter2/Boundary.lean, line 656

*What differs.*
- The text's description of $d_O$ as a minimum over germs into retracts is replaced by Definition 2.22 for the atlas $\{\mathrm{id}\}$, whose charts are such germs restricted to open subsets.
- The text's paracompactness of $O$ (as a metric space) is part of the M-polyfold structure on the subtype.

### V2.37. Theorem 2.31: $\dim(T_xO/T^R_xO) \le d_O(x)$

*stronger* · every M-polyfold, level-$1$ points · second statement without its hypothesis

**HWZ (§2.3, Theorem 2.31, p. 35 (first statement)).** For a retract $(O, C, E)$ and a smooth $x \in O$, $\dim(T_xO/T^R_xO) \le d_O(x)$.

**Proved in Lean.** For every M-polyfold $X$, every chart $\varphi$ around $x$ with $\varphi(x)$ on level $1$, every retraction $r$ onto the model $O$ and every presentation of $C$: $\dim(T_{\varphi(x)}O/T^R_{\varphi(x)}O) \le d_X(x)$. In the text's form, for a retract $O$ as an M-polyfold and $x \in O_1$: $\dim(T_xO/T^R_xO) \le d_O(x)$. The core: along a germ of sc-diffeomorphisms $F$ between retracts, $\dim(T_xO/T^R_xO) \le d_{C'}(F(x))$. The second statement holds without the equality: $C_xO$ is a partial quadrant in $T_xO$ at every smooth $x$ (V2.33).

- `Polyfold.theorem_2_31` — Polyfold/Chapter2/Boundary.lean, line 715
- `Polyfold.theorem_2_31_retract` — Polyfold/Chapter2/Boundary.lean, line 731
- `Polyfold.ScRetraction.IsDiffeoGerm.quotDim_le` — Polyfold/Chapter2/Boundary.lean, line 572
- `Polyfold.MPolyfold.quotDim_le_chartDegIndex` — Polyfold/Chapter2/Boundary.lean, line 686
- `Polyfold.ScRetraction.scDeriv_restrict` — Polyfold/Chapter2/Boundary.lean, line 544
- `Polyfold.degIndexWith_le_of_germ` — Polyfold/Chapter2/DegeneracyIndex.lean, line 424
- `Polyfold.remark_2_28_isPartialQuadrant` — Polyfold/Chapter2/PartialConeQuadrant.lean, line 655

*What differs.*
- Stated for every chart of every M-polyfold and for points on level $1$; the text's statement is `theorem_2_31_retract`.
- The proof does not reduce to a chart realizing $d_O(x)$, as the text does: for every other chart $\psi$, $D(\psi \circ \varphi^{-1})$ induces $T_xO/T^R_xO \cong T_yO'/T^R_yO'$, which embeds in $E'/E'_y$ of dimension $d_{C'}(y)$.
- The second statement (equality makes $C_xO$ a partial quadrant) holds without its hypothesis: $C_xO$ is a partial quadrant at every smooth point of every retract (V2.33; formerly G.11). Updated in the third addendum of this page.
- For tame retracts the conclusion of the second statement, $C_xO$ a partial quadrant, is proved directly (V2.42).

### V2.38. Corollary 2.32: $d_{X_C} = d_C$

*stronger* · any relatively open $U \subseteq C$ · level-$1$ approximation

**HWZ (§2.3, Corollary 2.32, p. 37).** For a partial quadrant $C$, viewed as the M-polyfold $X_C$, $d_C = d_{X_C}$.

**Proved in Lean.** For a nonempty relatively open subset $U$ of a partial quadrant $C$, viewed as the M-polyfold $X_U$ (chart $\mathrm{id}$), $d_{X_U}(x) = d_C(x)$ for every $x \in U$. The inequality $d_C \le d_{X_U}$ is proved at level-$1$ points from the core of Theorem 2.31 and extended by approximation with level-$1$ points of the same index and Lemma 2.23.

- `Polyfold.corollary_2_32` — Polyfold/Chapter2/DegeneracyIndex.lean, line 939
- `Polyfold.IsRelOpenInQuadrant.degIndex_le` — Polyfold/Chapter2/DegeneracyIndex.lean, line 863
- `Polyfold.IsRelOpenInQuadrant.degIndex_le_degIndex_of_lvl1` — Polyfold/Chapter2/DegeneracyIndex.lean, line 868
- `Polyfold.degIndexWith_le_of_germ` — Polyfold/Chapter2/DegeneracyIndex.lean, line 424

*What differs.*
- Proved for every relatively open $U \subseteq C$; $U = C$ is the text's case.
- Smooth points are not needed: level-$1$ points $T^{-1}(a, w')$, $w' \in W_1$, of the same index suffice.
- Theorem 1.25 (boundary recognition, Chapter 1, V1.23) is proved in the same file, `Chapter2/DegeneracyIndex.lean`, by this argument (`theorem_1_25`).

### V2.39. Definition 2.33: $C_e$ and $E_e$

*restated* · through a presentation, independent of it

**HWZ (§2.4, Definition 2.33, p. 39).** $C_e := \bigcap_{f \in \mathcal F(e)} H_f$ and $E_e := \bigcap_{f \in \mathcal F(e)} f$; $E_e \subset C_e \subset E$, $E_e$ has codimension $d_C(e)$.

**Proved in Lean.** For a presentation $T$ of $C$: $C_e = \{v : (Tv)_i \ge 0 \text{ for } (Te)_i = 0\}$ and $E_e = \{v : (Tv)_i = 0 \text{ for } (Te)_i = 0\}$, convex resp. a closed subspace, $E_e \subseteq C_e$, $\dim(E_0/E_e) = d_C(e)$. $E_e$ is the same for every presentation of $C$.

- `Polyfold.partialQuadrantAtWith` — Polyfold/Chapter2/Tame.lean, line 99
- `Polyfold.minimalSubspaceWith` — Polyfold/Chapter2/DegeneracyIndex.lean, line 129
- `Polyfold.minimalSubspaceWith_subset_partialQuadrantAtWith` — Polyfold/Chapter2/Tame.lean, line 103
- `Polyfold.convex_partialQuadrantAtWith` — Polyfold/Chapter2/Tame.lean, line 108
- `Polyfold.finrank_quotient_minimalSubspaceWith` — Polyfold/Chapter2/DegeneracyIndex.lean, line 148
- `Polyfold.minimalSubspaceWith_le` — Polyfold/Chapter2/TameFaces.lean, line 113
- `Polyfold.minimalSubspaceWith_eq` — Polyfold/Chapter2/TameFaces.lean, line 133

*What differs.*
- Defined through a presentation (the intrinsic description of the text is G.12); the same objects as V2.31.
- $E_e$ does not depend on the presentation: for two presentations $T$, $T'$ of the same $C$ and $e \in C$, the two subspaces agree (`minimalSubspaceWith_eq`, the argument of Lemma 1.24).

### V2.40. Definition 2.34: tame retractions and tame retracts

*restated* · presentation-independent (proved)

**HWZ (§2.4, Definition 2.34, pp. 39–40).** An sc-smooth retraction $r : U \to U$ is tame if (1) $d_C(r(x)) = d_C(x)$ on $U$ and (2) at every smooth $x \in O$ there is an sc-subspace $A \subset E_x$ with $E = T_xO \oplus A$. A tame retract is the image of a tame retraction.

**Proved in Lean.** $r$ is tame for the presentation $T$ if (1) $d_C(r(x)) = d_C(x)$ for $x \in U$ and (2) for every smooth $x \in O_1$ there is $A \le E_x$ with $E = Dr(x)E \oplus A$ an sc-splitting (both summands sc-subspaces, complementary on every level). $r$ is tame if it is tame for every presentation of $C$, equivalently for one; a tame retract is the retract of a tame retraction. The identity of a relatively open $U \subseteq C$ is tame, and restrictions of tame retractions to $U \cap r^{-1}(V)$, $V$ open, are tame.

- `Polyfold.ScRetraction.IsTameWith` — Polyfold/Chapter2/Tame.lean, line 122
- `Polyfold.ScRetraction.IsTame` — Polyfold/Chapter2/Tame.lean, line 131
- `Polyfold.IsTameRetract` — Polyfold/Chapter2/Tame.lean, line 137
- `Polyfold.IsTameRetract.isScRetract` — Polyfold/Chapter2/Tame.lean, line 140
- `Polyfold.ScRetraction.id_isTame` — Polyfold/Chapter2/Tame.lean, line 146
- `Polyfold.ScRetraction.IsTameWith.isTame` — Polyfold/Chapter2/TameFaces.lean, line 141
- `Polyfold.ScRetraction.IsTameWith.restrict` — Polyfold/Chapter2/TameFaces.lean, line 152

*What differs.*
- `IsTame` asks tameness for every presentation of $C$; tameness for one presentation implies it (`IsTameWith.isTame`, from the independence of $E_x$), so the definition is the text's. The theorems of §2.4 assume tameness for the presentation they compute in.
- Tameness passes to the restrictions $r|_{U \cap r^{-1}(V)}$, $V$ open (`IsTameWith.restrict`).
- \"$E = T_xO \oplus A$\" is an sc-splitting, as an sc-complement must be.

### V2.41. Proposition 2.35: $(1 - Dr(x))E \subseteq E_x$

*stronger* · only condition (2) used

**HWZ (§2.4, Proposition 2.35, p. 41 (discussion pp. 40–41)).** For a tame retraction and a smooth $x \in O$, $(1 - Dr(x))E \subseteq E_x$, so in condition (2) one can take $A = (1 - Dr(x))E$.

**Proved in Lean.** Let $r$ be tame for $T$ and $x \in O_1$ smooth. Then $(1 - Dr(x))E \le E_x$ and $E = Dr(x)E \oplus (1 - Dr(x))E$ is an sc-splitting. In coordinates, $\lambda_j \circ Dr(x) = \lambda_j$ for $j \in I(x)$.

- `Polyfold.proposition_2_35` — Polyfold/Chapter2/TameRetracts.lean, line 176
- `Polyfold.ScRetraction.scDeriv_mapsTo_minimalSubspace` — Polyfold/Chapter2/TameRetracts.lean, line 126
- `Polyfold.ScRetraction.isScOperator_scDeriv` — Polyfold/Chapter2/TameRetracts.lean, line 136
- `Polyfold.ScRetraction.isScSplitting_range_scDeriv` — Polyfold/Chapter2/TameRetracts.lean, line 141
- `Polyfold.coord_scDeriv_eq` — Polyfold/Chapter2/TameRetracts.lean, line 559

*What differs.*
- Only condition (2) of tameness is used. The text derives $Dr(x)E_x \subseteq E_x$ from condition (1); the sign argument gives it for every sc-smooth retraction at every point of $O_1$.
- The sc-splitting is that of the sc-projection $Dr(x)$ at the smooth point $x$.

### V2.42. Proposition 2.36: $d_O = d_C$, $T^R_xO$ an sc-subspace, $C_xO$ a partial quadrant

*stronger* · tame charts realize $d_X$ · $T^R_xO$ an sc-subspace · partial quadrant without Theorem 2.31

**HWZ (§2.4, Proposition 2.36, p. 41).** For a tame retract and smooth $x$: $T^R_xO$ has codimension $d_O(x)$, $\dim(T_xO/T^R_xO) = d_O(x)$ (13), and $C_xO$ is a partial quadrant in $T_xO$; for every $x \in O$, $d_O(x) = d_C(x)$ (14).

**Proved in Lean.** Let $r$ be tame for $T$. (13) At a smooth $x \in O_1$: $\dim(T_xO/T^R_xO) = d_O(x) = d_C(x)$; moreover $T_xO$ and $T^R_xO$ are sc-subspaces of $E$, and $C_xO = T_xO \cap C_x$ is a partial quadrant in the sc-Banach space $T_xO$ (with the sc-structure induced from $E$). (14) For every $x \in O$: $d_O(x) = d_C(x)$, $O$ with its single chart. More generally, a chart $\varphi$ of any M-polyfold whose model is a tame retract realizes the degeneracy index: $d_X(y) = d_C(\varphi(y))$ for every $y$ in its domain.

- `Polyfold.proposition_2_36` — Polyfold/Chapter2/TameRetracts.lean, line 386
- `Polyfold.proposition_2_36_degIndex` — Polyfold/Chapter2/TameRetracts.lean, line 378
- `Polyfold.quotDim_reducedTangentSpaceWith_eq` — Polyfold/Chapter2/TameRetracts.lean, line 204
- `Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith` — Polyfold/Chapter2/TameRetracts.lean, line 290
- `Polyfold.MPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract` — Polyfold/Chapter2/TameRetracts.lean, line 348
- `Polyfold.LocalModel.degIndex_toMPolyfold_of_isTameWith` — Polyfold/Chapter2/TameRetracts.lean, line 367
- `Polyfold.quotDim_eq_finrank_quotient_of_isCompl` — Polyfold/Chapter2/TameRetracts.lean, line 102
- `Polyfold.proposition_2_36_partialCone` — Polyfold/Chapter2/PartialCone.lean, line 193
- `Polyfold.splitIso` — Polyfold/Chapter2/PartialCone.lean, line 141
- `Polyfold.isPartialQuadrant_ofSubspace` — Polyfold/Chapter2/PartialCone.lean, line 159

*What differs.*
- (13) and (14) as in the text; the general form for charts of any M-polyfold is what Proposition 2.42's \"$d_V(y) = d_X(y)$\" needs.
- The approximants $r(a, w_j)$, $w_j \in W_\infty$, are taken through the presentation (`exists_tendsto_smooth_degIndexWith`).
- The text deduces "$C_xO$ is a partial quadrant" from the equality case of Theorem 2.31 (G.11; since proved without the equality, V2.33); here it is proved directly. The smooth vectors $\hat e_j = Dr(x)T^{-1}(e_{i_j}, 0)$ satisfy $\lambda_{i_k}(\hat e_j) = \delta_{jk}$ by Proposition 2.35, and $v \mapsto ((\lambda_{i_j}v)_j, v - \sum_j \lambda_{i_j}(v)\hat e_j)$ is an sc-isomorphism $T_xO \cong \mathbb R^d \oplus T^R_xO$ carrying $C_xO$ onto $[0, \infty)^d \oplus T^R_xO$ (`splitIso`).
- The text calls $T^R_xO$ a Banach space; it is proved to be an sc-subspace (the exposition's Lemma 3.A (1) in this case), which the sc-isomorphism needs: $Dr(x)T^{-1}(a, w')$, $w' \in W_\infty$, are smooth points of $T^R_xO$ converging to $u$ on level $m$. Both the sc-subspace property of $T^R_xO$ and the partial quadrant hold without tameness (V2.33); what tameness adds is that the quadrant has dimension $d_O(x) = d_C(x)$. Updated in the third addendum of this page.

### V2.43. Definition 2.37: tame M-polyfolds

*as in the book*

**HWZ (§2.4, Definition 2.37, p. 42).** A tame M-polyfold is an M-polyfold with an equivalent atlas whose charts are all modelled on tame sc-smooth retracts.

**Proved in Lean.** $X$ is tame if some atlas equivalent to its atlas consists of charts modelled on tame retracts; then every point lies in a chart of the structure with a tame model.

- `Polyfold.MPolyfold.IsTame` — Polyfold/Chapter2/Tame.lean, line 211
- `Polyfold.MPolyfold.isChart_of_mem_equiv` — Polyfold/Chapter2/TameRetracts.lean, line 1202
- `Polyfold.MPolyfold.IsTame.exists_chart` — Polyfold/Chapter2/TameRetracts.lean, line 1208

*What differs.*
- As in the text.

### V2.44. Definition 2.39: faces and face-structured M-polyfolds

*as in the book* · defined for every M-polyfold

**HWZ (§2.4, Definition 2.39, p. 43).** A face of a tame M-polyfold is the closure of a connected component of $\{d_X = 1\}$; $X$ is face-structured if every $x$ lies in exactly $d_X(x)$ faces.

**Proved in Lean.** $F$ is a face of $X$ if $F = \overline{G}$ for the connected component $G$ in $\{d_X = 1\}$ of a point with $d_X = 1$; $X$ is face-structured if $\#\{F : F \text{ a face}, x \in F\} = d_X(x)$ for every $x$ (cardinality in $\mathbb N \cup \{\infty\}$). Faces are closed and lie in $\partial X$.

- `Polyfold.MPolyfold.IsFace` — Polyfold/Chapter2/Tame.lean, line 216
- `Polyfold.MPolyfold.IsFaceStructured` — Polyfold/Chapter2/Tame.lean, line 220
- `Polyfold.MPolyfold.IsFace.isClosed` — Polyfold/Chapter2/Tame.lean, line 224
- `Polyfold.MPolyfold.IsFace.subset_boundary` — Polyfold/Chapter2/Boundary.lean, line 126

*What differs.*
- Defined for every M-polyfold; the theorems about faces assume tameness, as the text does.

### V2.45. The local geometry of faces (exposition Lemmas 4.A–4.C)

*not in the book* · supplies the steps the text skips · uses tameness (2) via Prop. 2.35

**HWZ (§2.4, proof of Lemma 2.40, p. 43).** \"There exists an index $i$ such that $\hat F$ must lie in $\{a_i = 0\}$\"; the retraction maps points near a face into the same face (\"using this argument repeatedly, we can connect any two points in $Q$\").

**Proved in Lean.** Let $r$ be tame for $T$. (a) A preconnected subset of $\{z \in C : d_C(z) = 1\}$ meeting $f_i$ lies in $f_i$. (b) Rays stay in their face: for smooth $x \in O$, $i \in I(x)$ and $y$ with $\lambda_i(y) = 0$, $\lambda_l(y) > 0$ for the other $l \in I(x)$, for small $\tau > 0$, $I(x + \tau y) = \{i\}$ and $I(r(x + \tau y)) = \{i\}$. (c) Local structure: for $e \in f_i \cap O$ there are $\varepsilon > 0$ and a component $\hat F(e)$ of $S = \{z \in O : d_C(z) = 1\}$ in $f_i$ such that on $B = B_\varepsilon(e) \cap C$: $B \subseteq U$, $I(z), I(r(z)) \subseteq I(e)$, $r$ maps $\{z \in B : I(z) = \{i\}\}$ into $\hat F(e)$, and $f_i \cap B$ is mapped into $\overline{\hat F(e)}$.

- `Polyfold.subset_coordHyper_of_isPreconnected` — Polyfold/Chapter2/TameRetracts.lean, line 454
- `Polyfold.IsSc1With.apply_deriv_eq_zero_of_ray` — Polyfold/Chapter2/TameRetracts.lean, line 512
- `Polyfold.ray_zeroSet` — Polyfold/Chapter2/TameRetracts.lean, line 579
- `Polyfold.local_face_structure` — Polyfold/Chapter2/TameRetracts.lean, line 772
- `Polyfold.eventually_zeroSet_subset` — Polyfold/Chapter2/TameRetracts.lean, line 424
- `Polyfold.convex_ball_inter_zeroSet_eq` — Polyfold/Chapter2/TameRetracts.lean, line 738
- `Polyfold.ScRetraction.faceStratum` — Polyfold/Chapter2/TameRetracts.lean, line 702
- `Polyfold.coordHyper` — Polyfold/Chapter2/TameRetracts.lean, line 418

*What differs.*
- Not stated in the text; these are the exposition's Lemmas 4.A–4.C, which supply the step that the retraction maps points of $f_i$ near $f_i \cap O$ into $f_i$.
- (b) needs tameness condition (2) through Proposition 2.35 ($\lambda_j \circ Dr(x) = \lambda_j$); condition (1) alone fixes only the number of vanishing coordinates.

### V2.46. Lemma 2.40: faces of a tame retract

*hypotheses explicit* · extended faces $f_i = \{\lambda_i = 0\}$ · faces handled in $E_0$

**HWZ (§2.4, Lemma 2.40, p. 43).** For a tame retract $(O, C, E)$, the faces of $O$ are the connected components of the sets $f \cap O$, $f$ an extended face; the components of $f \cap O$ and $f' \cap O$ through $x$ agree iff $f = f'$.

**Proved in Lean.** Let $r$ be tame for $T$, and call a face of the retract a set $\overline{\hat F} \cap O$, $\hat F$ a connected component of $S = \{z \in O : d_C(z) = 1\}$. Then $G$ is a face iff $G$ is the connected component of $f_i \cap O$ through some $e \in O$ with $\lambda_i(e) = 0$. For $x \in O$ with $\lambda_i(x) = 0$, if the components of $f_i \cap O$ and $f_j \cap O$ through $x$ coincide then $i = j$. These are the faces of the M-polyfold $O$.

- `Polyfold.ScRetraction.IsRetractFace` — Polyfold/Chapter2/TameRetracts.lean, line 974
- `Polyfold.lemma_2_40` — Polyfold/Chapter2/TameRetracts.lean, line 1064
- `Polyfold.lemma_2_40_injective` — Polyfold/Chapter2/TameRetracts.lean, line 1079
- `Polyfold.closure_connectedComponentIn_faceStratum` — Polyfold/Chapter2/TameRetracts.lean, line 1012
- `Polyfold.connectedComponentIn_coordHyper_eq` — Polyfold/Chapter2/TameRetracts.lean, line 1047
- `Polyfold.LocalModel.isFace_toMPolyfold_iff` — Polyfold/Chapter2/TameRetracts.lean, line 1134
- `Polyfold.subset_of_relClopen_of_isPreconnected` — Polyfold/Chapter2/TameRetracts.lean, line 914

*What differs.*
- Extended faces are the coordinate hyperplanes of a presentation; faces are handled in $E_0$ and transferred to the M-polyfold $O$ by `isFace_toMPolyfold_iff` (using $d_O = d_C$, V2.42).
- The text's proof is a sketch; the formal proof follows the exposition (Lemma 4.C, V2.45).

### V2.47. Corollary 2.41: a tame retract is face-structured

*as in the book*

**HWZ (§2.4, Corollary 2.41, p. 44).** If $(O, C, E)$ is a tame retract, every $x \in O$ lies in precisely $d_O(x)$ faces.

**Proved in Lean.** For a tame retract $O$ (nonempty), the M-polyfold $O$ is face-structured: every $x \in O$ lies in exactly $d_O(x)$ faces. In $E_0$: $x$ lies in exactly $d_C(x)$ faces of the retract.

- `Polyfold.corollary_2_41` — Polyfold/Chapter2/TameRetracts.lean, line 1187
- `Polyfold.corollary_2_41_retract` — Polyfold/Chapter2/TameRetracts.lean, line 1095
- `Polyfold.LocalModel.isFaceStructured_toMPolyfold` — Polyfold/Chapter2/TameRetracts.lean, line 1158

*What differs.*
- As in the text; the faces through $x$ are the components of $f_i \cap O$, $i \in I(x)$, distinct for distinct $i$ by Lemma 2.40.

### V2.48. Proposition 2.42: local face count in a tame M-polyfold

*restated* · $V$ represented by $O \cong V$

**HWZ (§2.4, Proposition 2.42, p. 44).** In a tame M-polyfold every $x$ has an open neighbourhood $V$ such that each $y \in V$ lies in precisely $d_X(y)$ faces of $V$ and $d_V(y) = d_X(y)$; globally $x$ lies in at most $d_X(x)$ faces.

**Proved in Lean.** Let $X$ be tame and $x \in X$. There is a chart $\varphi : V \to O$ around $x$ with tame model such that $d_X(y) = d_C(\varphi(y))$ and $d_O(\varphi(y)) = d_X(y)$ for all $y \in V$, and the M-polyfold $O$ is face-structured. Globally, $x$ lies in at most $d_X(x)$ faces of $X$.

- `Polyfold.proposition_2_42` — Polyfold/Chapter2/TameRetracts.lean, line 1308
- `Polyfold.MPolyfold.faces_encard_le` — Polyfold/Chapter2/TameRetracts.lean, line 1222
- `Polyfold.MPolyfold.IsTame.exists_chart` — Polyfold/Chapter2/TameRetracts.lean, line 1208

*What differs.*
- The neighbourhood $V$ is represented by the M-polyfold $O$ it is sc-diffeomorphic to through $\varphi$; its faces are those of $O$.
- \"$d_V(y) = d_X(y)$\" uses that a tame chart realizes $d_X$ (V2.42), which the text does not say.

### V2.49. Proposition 2.43: faces of a tame retract are tame sub-M-polyfolds

*restated* · tame model on $\mathbb R^k \oplus W$ · $U^*$ from balls and $P_i$-preimages · no hypothesis added

**HWZ (§2.4, Proposition 2.43, pp. 44–45).** For a tame retraction $r$ onto $O$ and a face $F$ of $O$: there are an open neighbourhood $V^*$ of $F$ in $U$ and an sc-smooth retraction $s : V^* \to V^*$ onto $F$; $s$ restricted to $V = O \cap V^*$ makes $F$ a sub-M-polyfold of $O$. $F$ is tame and $d_F(x) = d_O(x) - 1$ for $x \in F$.

**Proved in Lean.** Let $r$ be tame for $T$ and $F$ a face of the retract, $F \subseteq f_i$. (a) There is an sc-smooth retraction $S$ on $U^* \subseteq U$, relatively open in $C$ with $F \subseteq U^*$, with retract $F$ and $S = r \circ P_i$, $P_i$ the sc-projection onto $f_i$; every face of the M-polyfold $O$ is a sub-M-polyfold of $O$. (b) With the sc-operators $\iota : \mathbb R^k \oplus W \to f_i$ (insert a zero coordinate) and $\pi : E \to \mathbb R^k \oplus W$ (delete it), $r' = \pi \circ r \circ \iota$ on $\iota^{-1}(U^*)$ is a tame retraction of $[0, \infty)^k \oplus W$ onto $\pi(F)$, and $d_{C'}(\pi y) + 1 = d_C(y)$ on $F$. (c) A face $F$ of a tame retract $O$, with its sub-M-polyfold structure, is a tame M-polyfold and $d_F(x) + 1 = d_O(x)$ for $x \in F$.

- `Polyfold.proposition_2_43` — Polyfold/Chapter2/TameRetracts.lean, line 1394
- `Polyfold.killCoord` — Polyfold/Chapter2/TameRetracts.lean, line 1352
- `Polyfold.killCoord_mem` — Polyfold/Chapter2/TameRetracts.lean, line 1373
- `Polyfold.killCoord_eq_self` — Polyfold/Chapter2/TameRetracts.lean, line 1363
- `Polyfold.LocalModel.isSubMPolyfold_of_isFace` — Polyfold/Chapter2/TameRetracts.lean, line 1474
- `Polyfold.faceIncl` — Polyfold/Chapter2/TameFaces.lean, line 223
- `Polyfold.faceProj` — Polyfold/Chapter2/TameFaces.lean, line 227
- `Polyfold.degIndexWith_eq_quadrantDeg_faceProj_add_one` — Polyfold/Chapter2/TameFaces.lean, line 279
- `Polyfold.proposition_2_43_tameModel` — Polyfold/Chapter2/TameFaces.lean, line 315
- `Polyfold.MPolyfold.faceChart` — Polyfold/Chapter2/TameFaces.lean, line 451
- `Polyfold.MPolyfold.faceChart_compatible_subChart` — Polyfold/Chapter2/TameFaces.lean, line 492
- `Polyfold.LocalModel.proposition_2_43_isTame` — Polyfold/Chapter2/TameFaces.lean, line 568

*What differs.*
- The text's model $(F, C \cap f_1, f_1)$ uses the sc-subspace $f_1$; here the extended face is modelled on $\mathbb R^k \oplus W$ through $\iota$, $\pi$, and the retraction is $\pi \circ r \circ \iota$ rather than $r|_{U^* \cap f_1}$ (they correspond under $\iota$). Tameness (2) of $r'$ is proved with the complement $(1 - Dr'(x))E'$, by Proposition 2.35 for $r$, not by intersecting with $f_1$.
- $U^*$ is the union of the balls $B_e$ intersected with their preimages under $P_i$, because $P_i$ need not be norm-decreasing for the norm of $E_0$ (the exposition's \"$|P_1z - e|_0 \le |z - e|_0$\" is false in general).
- \"$r(0, b_2, \dots, b_k, v)$ has the first coordinate vanishing\" is the local structure lemma (V2.45). $d_F = d_O - 1$ is stated as $d_F + 1 = d_O$; $F$ is paracompact because faces are closed.

### V2.50. Proposition 2.44: local faces and their intersections are tame

*restated* · face germs = faces of a tame chart · $d_A + \#\sigma = d_X$ on all of $A$ · corners at once, no induction

**HWZ (§2.4, Proposition 2.44, p. 46).** In a tame M-polyfold every point $x$ has $d_X(x)$ local faces containing $x$; they are tame M-polyfolds with $d_F(x) = d_X(x) - 1$. The intersection $F^\sigma$ of the local faces of $\sigma \subseteq \mathcal F_x$ is a tame M-polyfold of codimension $\#\sigma$ with $d_{F^\sigma}(x) = d_X(x) - \#\sigma$ (stated without proof).

**Proved in Lean.** Let $X$ be tame and $x \in X$. There is a chart $\varphi : V \to O$ of the structure around $x$, with a tame retraction onto $O$, such that the point $\varphi(x)$ lies in exactly $d_X(x)$ faces of the M-polyfold $O$, and every face $F$ of $O$ is a sub-M-polyfold of $O$ which, with its induced structure, is tame, with $d_F(\varphi(x)) + 1 = d_X(x)$ when $\varphi(x) \in F$. For every set $\sigma$ of face germs at $x$, i.e. $\sigma \subseteq I(\varphi(x))$, there are pairwise distinct faces $F_i \ni \varphi(x)$ of the retract ($i \in \sigma$, $F_i$ in the $i$-th coordinate hyperplane) and an open $B \ni \varphi(x)$ such that $A = \{y \in V : \varphi(y) \in B,\ \varphi(y) \in F_i\ \forall i \in \sigma\}$ (whose germ at $x$ is $F^\sigma_x$) is a sub-M-polyfold of $X$, tame with its induced structure, and $d_A(y) + \#\sigma = d_X(y)$ for all $y \in A$.

- `Polyfold.MPolyfold.proposition_2_44` — Polyfold/Chapter2/TameFaces.lean, line 1065
- `Polyfold.proposition_2_42` — Polyfold/Chapter2/TameRetracts.lean, line 1308
- `Polyfold.LocalModel.proposition_2_43_isTame` — Polyfold/Chapter2/TameFaces.lean, line 568
- `Polyfold.MPolyfold.proposition_2_44_corner` — Polyfold/Chapter2/CornerGerms.lean, line 470
- `Polyfold.corner_retraction` — Polyfold/Chapter2/CornerGerms.lean, line 239
- `Polyfold.corner_tameModel` — Polyfold/Chapter2/CornerGerms.lean, line 343
- `Polyfold.cornerIncl` — Polyfold/Chapter2/CornerGerms.lean, line 127
- `Polyfold.cornerProj` — Polyfold/Chapter2/CornerGerms.lean, line 131
- `Polyfold.cornerKill` — Polyfold/Chapter2/CornerGerms.lean, line 220
- `Polyfold.degIndexWith_eq_quadrantDeg_cornerProj_add_card` — Polyfold/Chapter2/CornerGerms.lean, line 180

*What differs.*
- "Local faces" are the faces of the M-polyfold $O$ of a tame chart, as in Proposition 2.42; the face germs at $x$ are the faces $F_i$, $i \in I(\varphi(x))$, and "$F^\sigma_x$ is the germ of a sub-M-polyfold" is witnessed by the set $A$ itself. Face germs are not defined as germs.
- "Codimension $\#\sigma$" is the number of quadrant coordinates removed in the tame model $\pi_\sigma(\varphi(A)) \subseteq [0, \infty)^{n - \#\sigma} \oplus W$; $d_A + \#\sigma = d_X$ holds on all of $A$, not only at $x$.
- The text gives no proof; the exposition argues by induction on $\#\sigma$. The formal proof removes all coordinates of $\sigma$ at once: Lemma 4.C for each $i \in \sigma$ makes $r \circ P_\sigma$ a retraction onto $O \cap B \cap f_\sigma$ near $\varphi(x)$ (`corner_retraction`), with the tame model $\pi_\sigma \circ r \circ \iota_\sigma$ (`corner_tameModel`), as in Proposition 2.43.

### V2.51. Theorem 2.45: interiors of faces and faces of face-structured M-polyfolds

*hypotheses explicit* · "interior" = $F \cap \{d_X = 1\}$ · counting argument made explicit

**HWZ (§2.4, Theorem 2.45, p. 46).** The interior of a face $F$ in a tame M-polyfold is an sc-smooth sub-M-polyfold of $X$. If $X$ is face-structured, every face is a sub-M-polyfold, its induced structure is tame, and $i : F \to X$ satisfies $d_X(i(x)) = d_F(x) + 1$. Every point has a neighbourhood $U$ in which each $y$ lies in exactly $d_X(y)$ faces of $U$; if $X$ is face-structured, each $x$ lies in exactly $d_X(x)$ faces of $X$ (stated without proof).

**Proved in Lean.** Let $X$ be tame, $G$ the connected component of $\{d_X = 1\}$ through a point, $F = \overline G$. (a) $F \cap \{d_X = 1\} = G$ (the interior of the face), and $G$ is a sub-M-polyfold of $X$. (b) If $X$ is face-structured, every face $F$ agrees near each of its points, in a tame chart, with a face of the model retract; $F$ is a sub-M-polyfold of $X$, tame with its induced structure, and $d_X(x) = d_F(x) + 1$ for $x \in F$. A local criterion: $A$ is a sub-M-polyfold if near each point $\varphi(A)$ agrees on an open set with an sc-smooth retract contained in $O$. The face counts of the theorem are Proposition 2.42 and the definition of face-structured.

- `Polyfold.MPolyfold.theorem_2_45_interior` — Polyfold/Chapter2/TameRetracts.lean, line 1581
- `Polyfold.MPolyfold.isSubMPolyfold_of_local` — Polyfold/Chapter2/TameFaces.lean, line 624
- `Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_interior` — Polyfold/Chapter2/TameFaces.lean, line 741
- `Polyfold.MPolyfold.exists_localFace_of_isFaceStructured` — Polyfold/Chapter2/TameFaces.lean, line 822
- `Polyfold.MPolyfold.theorem_2_45_isSubMPolyfold_face` — Polyfold/Chapter2/TameFaces.lean, line 973
- `Polyfold.MPolyfold.theorem_2_45_isTame_face` — Polyfold/Chapter2/TameFaces.lean, line 995
- `Polyfold.MPolyfold.isTame_of_forall_exists_chart` — Polyfold/Chapter2/TameFaces.lean, line 536

*What differs.*
- \"The interior of a face\" is not defined in the text; it is read as $F \cap \{d_X = 1\}$, which equals $G$.
- The text has no proof. In the face-structured case, \"each global face through $x$ contains exactly one local face\" is a counting argument: the map from $I(\varphi x)$ to the faces through $x$ is onto (Lemma 4.C) and, by face-structuredness, injective.
- The retraction near a point is $\varphi^{-1} \circ s \circ \varphi$ on $\varphi^{-1}(B \cap s^{-1}(B))$, shrunk so that $s$ maps it into itself; the exposition's \"transport by $\varphi^{-1}$\" omits this.

### V2.52. Products of M-polyfolds (exposition Lemma 4.D)

*not in the book* · used silently in the text · additivity needs tameness; in general $\le$

**HWZ (§2.4, proof of Proposition 2.46, p. 47).** Used without statement in Proposition 2.46: $X \times Y$ is an M-polyfold (with the product charts) and $d_{X \times Y}(x, y) = d_X(x) + d_Y(y)$.

**Proved in Lean.** For partial quadrants $C \subseteq E$, $C' \subseteq E'$, $C \times C'$ is a partial quadrant of $E \oplus E'$ with the product presentation $E \oplus E' \cong \mathbb R^{n+n'} \oplus (W \oplus W')$ and $d_{C \times C'}(x, x') = d_C(x) + d_{C'}(x')$; products of sc-smooth retractions are sc-smooth retractions, of tame ones tame. For M-polyfolds $X$, $Y$: $X \times Y$ is paracompact, and the product charts form an atlas of an M-polyfold structure on $X \times Y$; $d_{X \times Y}(x, y) \le d_X(x) + d_Y(y)$, with equality, and $X \times Y$ tame, if $X$ and $Y$ are tame. The projections are sc-smooth and the pairing of sc-smooth maps is sc-smooth.

- `Polyfold.IsPartialQuadrant.prod` — Polyfold/Chapter2/FibredProduct.lean, line 160
- `Polyfold.prod_eq_prodPresentation` — Polyfold/Chapter2/FibredProduct.lean, line 143
- `Polyfold.degIndex_prod` — Polyfold/Chapter2/FibredProduct.lean, line 179
- `Polyfold.minimalSubspaceWith_prodPresentation` — Polyfold/Chapter2/FibredProduct.lean, line 188
- `Polyfold.ScRetraction.prod` — Polyfold/Chapter2/FibredProduct.lean, line 279
- `Polyfold.IsScRetract.prod` — Polyfold/Chapter2/FibredProduct.lean, line 300
- `Polyfold.ScRetraction.IsTameWith.prod` — Polyfold/Chapter2/FibredProduct.lean, line 357
- `Polyfold.MChart.prod` — Polyfold/Chapter2/FibredProduct.lean, line 407
- `Polyfold.MChart.Compatible.prod` — Polyfold/Chapter2/FibredProduct.lean, line 434
- `Polyfold.MPolyfold.paracompactSpace_prod` — Polyfold/Chapter2/FibredProduct.lean, line 455
- `Polyfold.MPolyfold.prod` — Polyfold/Chapter2/FibredProduct.lean, line 461
- `Polyfold.MPolyfold.degIndex_prod_le` — Polyfold/Chapter2/FibredProduct.lean, line 489
- `Polyfold.MPolyfold.isTame_prod` — Polyfold/Chapter2/FibredProduct.lean, line 498
- `Polyfold.MPolyfold.isScSmoothMap_fst` — Polyfold/Chapter2/FibredProduct.lean, line 526
- `Polyfold.MPolyfold.isScSmoothMap_snd` — Polyfold/Chapter2/FibredProduct.lean, line 539
- `Polyfold.MPolyfold.IsScSmoothOn.prodMk` — Polyfold/Chapter2/FibredProduct.lean, line 555

*What differs.*
- Not stated in the text; this is the exposition's Lemma 4.D. The text's \"$d_{X \times Y} = d_X + d_Y$\" is proved for tame $X$, $Y$; in general only the inequality, from the product charts.
- Paracompactness of $X \times Y$ comes from Theorem 2.16 ($X$, $Y$ metrizable).

### V2.53. Proposition 2.46: fibred products

*stronger* · $d = d_Y$ (and $d_X = d_Y$) without tameness · inverse of $\pi_2$ corrected

**HWZ (§2.4, Proposition 2.46, pp. 46–47).** For a local sc-diffeomorphism $f : X \to Z$ and an sc-smooth $g : Y \to Z$, $X {}_f\times_g Y$ is a sub-M-polyfold of $X \times Y$; if $Y$ is tame, so is the fibred product, with $d(x, y) = d_Y(y)$; with both maps local sc-diffeomorphisms and both spaces tame, $d = \frac12 d_{X \times Y} = d_X(x) = d_Y(y)$.

**Proved in Lean.** Let $f : X \to Z$ be a local sc-diffeomorphism (each point has an open neighbourhood mapped sc-diffeomorphically onto an open set) and $g : Y \to Z$ sc-smooth. The fibred product $\{(x, y) : f(x) = g(y)\}$ is closed in $X \times Y$, hence paracompact, and a sub-M-polyfold of $X \times Y$; $d_{X {}_f\times_g Y}(x, y) = d_Y(y)$; if $Y$ is tame, the fibred product is tame. If $g$ is also a local sc-diffeomorphism, $d_{X {}_f\times_g Y}(x, y) = d_X(x) = d_Y(y)$, and if moreover $X$ and $Y$ are tame, $2\,d_{X {}_f\times_g Y}(x, y) = d_{X \times Y}(x, y)$.

- `Polyfold.MPolyfold.IsLocalScDiffeo` — Polyfold/Chapter2/FibredProduct.lean, line 590
- `Polyfold.MPolyfold.fibredProduct` — Polyfold/Chapter2/FibredProduct.lean, line 601
- `Polyfold.MPolyfold.fibredSubDataL` — Polyfold/Chapter2/FibredProduct.lean, line 612
- `Polyfold.MPolyfold.isSubMPolyfold_fibredProduct` — Polyfold/Chapter2/FibredProduct.lean, line 672
- `Polyfold.MPolyfold.isScDiffeoOn_snd_fibredProduct` — Polyfold/Chapter2/FibredProduct.lean, line 714
- `Polyfold.MPolyfold.isScDiffeoOn_fst_fibredProduct` — Polyfold/Chapter2/FibredProduct.lean, line 747
- `Polyfold.MPolyfold.degIndex_fibredProduct_eq_snd` — Polyfold/Chapter2/FibredProduct.lean, line 780
- `Polyfold.MPolyfold.degIndex_fibredProduct_eq_fst` — Polyfold/Chapter2/FibredProduct.lean, line 788
- `Polyfold.MPolyfold.isTame_fibredProduct` — Polyfold/Chapter2/FibredProduct.lean, line 796
- `Polyfold.MPolyfold.proposition_2_46` — Polyfold/Chapter2/FibredProduct.lean, line 821
- `Polyfold.MPolyfold.proposition_2_46_of_isLocalScDiffeo` — Polyfold/Chapter2/FibredProduct.lean, line 835

*What differs.*
- $d_{X {}_f\times_g Y} = d_Y \circ \pi_2$, and in the last statement $d = d_X = d_Y$, hold for arbitrary $X$, $Y$ (Proposition 2.24 along $\pi_2$, $\pi_1$); tameness is used only for $d_{X \times Y} = d_X + d_Y$ (V2.52), stated as $2d = d_{X \times Y}$.
- The inverse of $\pi_2$ near $(x, y)$ is $y' \mapsto ((f|_U)^{-1}(g(y')), y')$; the exposition's factorization through $y' \mapsto (x, y')$ is not sc-smooth unless $x$ is a smooth point (Findings, Chapter 2, item 15).
- The text's $\pi_2 : X {}_f\times_g Y \to X$ is read with target $Y$; paracompactness of the fibred product, which the text does not mention, comes from its being closed in the metrizable $X \times Y$.

### V2.54. Definition 2.47: $U \triangleleft F$, strong bundle maps and retractions

*restated* · $[1]$ via `shiftFiber` · isomorphisms not defined

**HWZ (§2.5, Definition 2.47, p. 48).** $U \triangleleft F$ is $U \times F$ with the double filtration $U_m \oplus F_k$, $0 \le k \le m + 1$, and $(U \triangleleft F)[i]$ with levels $U_m \oplus F_{m+i}$. A strong bundle map $\Phi(u, h) = (\varphi(u), \Gamma(u, h))$, $\Gamma$ linear in $h$, preserves the double filtration and is sc-smooth $(U \triangleleft F)[i] \to (U' \triangleleft F')[i]$, $i = 0, 1$; a strong bundle retraction is one with $R \circ R = R$; $R(u, h) = (r(u), \Gamma(u, h))$ with $r$ an sc-smooth retraction.

**Proved in Lean.** $\Phi : E_0 \times F_0 \to E'_0 \times F'_0$ is a strong bundle map on $U \triangleleft F$ if it maps $U \times F$ into $U' \times F'$, its first component does not depend on $h$, its second is linear in $h$ for $u \in U$, it maps $U_m \oplus F_k$ into $U'_m \oplus F'_k$ for $k \le m + 1$, and it is sc-smooth on $U \times F_0$ for $E \oplus F$ and (through the lift of the fibre component to $F'_1$) on $U \times F_1$ for $E \oplus F^1$. A strong bundle retraction is one with $R \circ R = R$; its base $r(u) = R(u, 0)_1$ is an sc-smooth retraction on $U$, $\Gamma(u, \cdot)$ is a projection for $u \in O$, and $R$ is an sc-smooth retraction on $(U \triangleleft F)[0]$ and on $(U \triangleleft F)[1]$. $C \times F$ is a partial quadrant in $E \oplus F$ and $U \times F$ is relatively open in it.

- `Polyfold.doubleLevel` — Polyfold/Chapter2/Tame.lean, line 237
- `Polyfold.shiftFiber` — Polyfold/Chapter2/Tame.lean, line 245
- `Polyfold.IsStrongBundleMap` — Polyfold/Chapter2/Tame.lean, line 252
- `Polyfold.IsStrongBundleRetraction` — Polyfold/Chapter2/Tame.lean, line 267
- `Polyfold.IsPartialQuadrant.prod_univ` — Polyfold/Chapter2/StrongBundle.lean, line 216
- `Polyfold.IsRelOpenInQuadrant.prod_univ` — Polyfold/Chapter2/StrongBundle.lean, line 229
- `Polyfold.IsStrongBundleRetraction.baseRetraction` — Polyfold/Chapter2/StrongBundle.lean, line 253
- `Polyfold.IsStrongBundleRetraction.fiber_idem` — Polyfold/Chapter2/StrongBundle.lean, line 282
- `Polyfold.IsStrongBundleRetraction.toScRetraction` — Polyfold/Chapter2/StrongBundle.lean, line 310
- `Polyfold.IsStrongBundleRetraction.toScRetractionOne` — Polyfold/Chapter2/StrongBundle.lean, line 333

*What differs.*
- Sc-smoothness on $[1]$ is that of the induced map $U \oplus F_1 \to U' \oplus F'_1$; \"preserves the double filtration\" is read level by level.
- Strong bundle isomorphisms are not defined separately (G.14); the remarks after the definition ($r$ a retraction, $\Gamma(u, \cdot)$ a projection) are the exposition's Lemma 5.A, proved here.

### V2.55. Definition 2.48: local strong bundle retracts and $K[i]$

*restated* · $K[1]$ as a subset of $E_0 \times F_1$

**HWZ (§2.5, Definition 2.48 and the remarks after it, pp. 49–50).** A local strong bundle retract is $K = R(U \triangleleft F)$ for a strong bundle retraction, $p : K \to O$; $K_{m,k} = \{(u, h) \in O_m \oplus F_k : \Gamma(u, h) = h\}$, $K[i] = K_{0,i}$ with the filtration $K_{m,m+i}$; the projections $p : K[i] \to O$ are sc-smooth.

**Proved in Lean.** $K \subseteq E_0 \times F_0$ is a local strong bundle retract over $C$ if $K = R(U \times F_0)$ for a strong bundle retraction on some relatively open $U \subseteq C$; then $K = \{(u, h) : u \in O, \Gamma(u, h) = h\}$. Its double filtration $K_{m,k}$ and $K[1] = \{(u, h) \in E_0 \times F_1 : (u, h) \in K\}$ are defined level by level. $K$ is an sc-smooth retract in $(C \times F, E \oplus F)$ and $K[1]$ one in $(C \times F, E \oplus F^1)$, $K[1]$ being the image of $R$ on $(U \triangleleft F)[1]$; $p : K[i] \to O$ and the inclusion $K[1] \to K[0]$ are sc-smooth.

- `Polyfold.IsStrongBundleRetract` — Polyfold/Chapter2/Tame.lean, line 273
- `Polyfold.strongLevel` — Polyfold/Chapter2/Tame.lean, line 279
- `Polyfold.strongLevelShift` — Polyfold/Chapter2/Tame.lean, line 283
- `Polyfold.strongShiftOne` — Polyfold/Chapter2/Tame.lean, line 287
- `Polyfold.IsStrongBundleRetraction.mem_image_iff` — Polyfold/Chapter2/StrongBundle.lean, line 294
- `Polyfold.IsStrongBundleRetraction.toScRetractionOne_retract` — Polyfold/Chapter2/StrongBundle.lean, line 353
- `Polyfold.IsStrongBundleRetract.isScRetract` — Polyfold/Chapter2/StrongBundle.lean, line 383
- `Polyfold.IsStrongBundleRetract.isScRetract_one` — Polyfold/Chapter2/StrongBundle.lean, line 389
- `Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst` — Polyfold/Chapter2/StrongBundle.lean, line 412
- `Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_fst_one` — Polyfold/Chapter2/StrongBundle.lean, line 421
- `Polyfold.IsStrongBundleRetract.isScSmoothRetractMap_shiftIncl` — Polyfold/Chapter2/StrongBundle.lean, line 430

*What differs.*
- $K[1]$ is a subset of $(E \oplus F^1)_0 = E_0 \times F_1$. The text's \"$p$ is sc-smooth\" is proved, with \"sc-smooth bundle map\" read as sc-smooth.
- That $K[1]$ is the image of $R$ on $(U \triangleleft F)[1]$ uses that $R$ preserves the double filtration at $(m, k) = (0, 1)$ (exposition Lemma 5.B).

### V2.56. Definition 2.49: sections of a local strong bundle retract

*restated* · the category $\mathcal{SBR}$: G.14

**HWZ (§2.5, Definition 2.49, p. 50).** A section of $p : K \to O$ is $f : O \to K$ with $p \circ f = 1_O$; sc-smooth if it is sc-smooth into $K[0]$, sc⁺-smooth if sc-smooth into $K[1]$ (the text writes $K(0)$, $K(1)$); $f(x) = (x, \mathbf f(x))$ with the principal part $\mathbf f$.

**Proved in Lean.** An sc-smooth section is $f$ with $f(x)_1 = x$ on $O$ and $f$ sc-smooth from $(O, C, E)$ to $(K, C \times F, E \oplus F)$; an sc⁺-section is $f : E_0 \to E_0 \times F_1$ with $f(x)_1 = x$ on $O$, sc-smooth into $(K[1], C \times F, E \oplus F^1)$. An sc⁺-section is an sc-smooth section.

- `Polyfold.IsScSmoothSection` — Polyfold/Chapter2/Tame.lean, line 296
- `Polyfold.IsScPlusSection` — Polyfold/Chapter2/Tame.lean, line 303
- `Polyfold.IsScPlusSection.mem` — Polyfold/Chapter2/Tame.lean, line 309
- `Polyfold.IsScPlusSection.isScSmoothSection` — Polyfold/Chapter2/StrongBundle.lean, line 443

*What differs.*
- The principal part is not named separately; an sc⁺-section takes its fibre values in $F_1$ by type.
- The category $\mathcal{SBR}$ and the forgetful functors are not formalized (G.14).

### V2.57. Definition 2.50: strong bundle charts, compatibility, atlases

*hypotheses explicit* · $\varphi$ a chart of $X$ · $[1]$-transition condition stated · equivalence relation; charts restrict

**HWZ (§2.5, Definition 2.50, pp. 51–52).** For $P : Y \to X$ (Y paracompact Hausdorff, fibres Banachable), a strong bundle chart $(\Phi, P^{-1}(V), K, U \triangleleft F)$: $K = R(U \triangleleft F)$, $V$ open with a homeomorphism $\varphi : V \to O$, $\Phi : P^{-1}(V) \to K$ a homeomorphism covering $\varphi$, bounded linear on fibres. Charts are compatible if $(\Phi' \circ \Phi^{-1})[i]$ are sc-diffeomorphisms, $i = 0, 1$; atlases and their equivalence.

**Proved in Lean.** A strong bundle chart consists of a chart $\varphi$ *of the M-polyfold $X$*, an sc-Banach space $F$, a strong bundle retraction $R$ on a relatively open $U \subseteq C$ whose base retract is $O$, and a homeomorphism $\Phi : P^{-1}(V) \to K = R(U \times F_0)$ with $\Phi(y)_1 = \varphi(P(y))$, linear on each fibre $P^{-1}(x)$ (continuity on fibres follows). Two charts are compatible if $\Phi' \circ \Phi^{-1}$ and $\Phi \circ \Phi'^{-1}$ are sc-smooth between the overlap retracts on $[0]$ and, through the lift to $F_1$, on $[1]$, and map fibre components in $F_1$ to fibre components in $F'_1$. Atlases: pairwise compatible charts covering $Y$; equivalence: the union is an atlas. Equivalence of strong bundle atlases is an equivalence relation, and two atlases are equivalent iff every chart of one is compatible with every chart of the other; this rests on the locality of compatibility. A strong bundle chart restricts to every open $s \subseteq V$ (retraction domain $U \cap r^{-1}(W)$ for $\varphi(s) = O \cap W$, $K_s = \{(u, h) \in K \mid u \in \varphi(s)\}$, $\Phi$ unchanged), and restrictions of compatible charts are compatible.

- `Polyfold.IsBanachable` — Polyfold/Chapter2/StrongBundle.lean, line 571
- `Polyfold.StrongBundleChart` — Polyfold/Chapter2/StrongBundle.lean, line 588
- `Polyfold.StrongBundleChart.K` — Polyfold/Chapter2/StrongBundle.lean, line 618
- `Polyfold.StrongBundleChart.continuous_fiber` — Polyfold/Chapter2/StrongBundle.lean, line 649
- `Polyfold.StrongBundleChart.Compatible` — Polyfold/Chapter2/StrongBundle.lean, line 669
- `Polyfold.StrongBundleChart.Compatible.symm` — Polyfold/Chapter2/StrongBundle.lean, line 685
- `Polyfold.StrongBundleAtlas` — Polyfold/Chapter2/StrongBundle.lean, line 707
- `Polyfold.StrongBundleAtlas.Equiv` — Polyfold/Chapter2/StrongBundle.lean, line 714
- `Polyfold.StrongBundleChart.compatible_of_locally` — Polyfold/Chapter2/StrongBundleRestrict.lean, line 438
- `Polyfold.StrongBundleAtlas.equiv_iff` — Polyfold/Chapter2/StrongBundleRestrict.lean, line 643
- `Polyfold.StrongBundleAtlas.Equiv.trans` — Polyfold/Chapter2/StrongBundleRestrict.lean, line 670
- `Polyfold.StrongBundleAtlas.equivalence` — Polyfold/Chapter2/StrongBundleRestrict.lean, line 679
- `Polyfold.IsStrongBundleRetraction.restrict` — Polyfold/Chapter2/StrongBundleRestrict.lean, line 98
- `Polyfold.StrongBundleChart.restrict` — Polyfold/Chapter2/StrongBundleRestrict.lean, line 521
- `Polyfold.StrongBundleChart.Compatible.restrict` — Polyfold/Chapter2/StrongBundleRestrict.lean, line 628

*What differs.*
- The base homeomorphism $\varphi$ is required to be a chart of $X$; the text asks only for a homeomorphism onto $O$, under which the strong bundle atlas would define its own structure on $X$.
- \"Bounded linear on the fibres\" needs only linearity: continuity follows from $\Phi$ being a homeomorphism (`continuous_fiber`).
- For $(\Phi' \circ \Phi^{-1})[1]$ to be defined, the transition must map fibre components in $F_1$ to $F'_1$; the text takes this for granted, the definition states it.
- The “equivalence class of strong bundle atlases” of Definition 2.51 presupposes that the equivalence is transitive. It is: near a point of the overlap the transition $\Phi'' \circ \Phi^{-1}$ factors through a chart $\Phi'$ of the middle atlas, on $[0]$ and on $[1]$, and the $F_1$-condition passes through $\Phi'$; no continuity of $P$ is needed (Findings, Chapter 2, item 40). The restriction of a strong bundle chart to an open subset of the base, which the text uses silently (e.g. in Lemma 5.2, V5.4), is formalized; a restriction whose retraction domain lies inside a given open $W \ni 0$ of $E$ is not, since $U \cap W$ need not be invariant under $r$ (item 42). Updated in the third addendum of this page.

### V2.58. Definition 2.51: strong bundles; $Y[0]$, $Y[1]$, $P[0]$, $P[1]$ and $Y_{m,k}$

*restated* · $Y[1]$ topologized by the charts $\Phi[1]$ · one chart decides $Y_{m,k}$ · charts depend only on the class

**HWZ (§2.5, Definition 2.51 and the remarks after it, p. 52).** A strong bundle over $X$ is $P : Y \to X$ (continuous surjection, $Y$ paracompact Hausdorff) with an equivalence class of strong bundle atlases. The charts induce a double filtration $Y_{m,k}$ and M-polyfolds $Y[i]$, $Y[i]_m = Y_{m,m+i}$; $P[i] : Y[i] \to X$ are sc-smooth.

**Proved in Lean.** A strong bundle is a continuous surjection $P : Y \to X$ ($Y$ Hausdorff paracompact) with Banachable fibres and a strong bundle atlas. The charts $\Phi$ form an sc-smooth atlas of $Y$, making it the M-polyfold $Y[0]$, and $P[0] : Y[0] \to X$ is sc-smooth. $Y_{m,k}$ ($k \le m + 1$) is defined by $\Phi(y) \in E_m \times F_k$ in all charts around $y$, and one chart suffices. $Y[1]$ is the set $Y_{0,1}$ with the topology generated by the charts $\Phi[1] : y \mapsto (\Phi(y)_1, \Phi(y)_2$ lifted to $F_1)$; these charts, onto the retracts $K[1]$, are pairwise compatible, their transition maps being the $[1]$-transitions, and make $Y[1]$ an M-polyfold; $P[1] : Y[1] \to X$ is sc-smooth. The charts of the strong bundle (`StrongBundle.IsChart`: compatible with the atlas) are those of the maximal atlas, which is equivalent to the given one: a chart is one iff it belongs to some atlas of the class, any two are compatible, restrictions of charts are charts, and equivalent atlases have the same charts.

- `Polyfold.StrongBundle` — Polyfold/Chapter2/StrongBundle.lean, line 720
- `Polyfold.StrongBundleChart.toMChart` — Polyfold/Chapter2/StrongBundle.lean, line 638
- `Polyfold.StrongBundleChart.Compatible.toMChart` — Polyfold/Chapter2/StrongBundle.lean, line 689
- `Polyfold.StrongBundle.atlas0` — Polyfold/Chapter2/StrongBundle.lean, line 734
- `Polyfold.StrongBundle.toMPolyfold0` — Polyfold/Chapter2/StrongBundle.lean, line 744
- `Polyfold.StrongBundle.isScSmoothMap_proj` — Polyfold/Chapter2/StrongBundle.lean, line 752
- `Polyfold.StrongBundle.doubleLevel` — Polyfold/Chapter2/StrongBundle.lean, line 774
- `Polyfold.StrongBundle.mem_doubleLevel_iff` — Polyfold/Chapter2/StrongBundleOne.lean, line 495
- `Polyfold.StrongBundle.oneChart` — Polyfold/Chapter2/StrongBundleOne.lean, line 200
- `Polyfold.StrongBundle.oneChart_compatible` — Polyfold/Chapter2/StrongBundleOne.lean, line 315
- `Polyfold.StrongBundle.atlas1` — Polyfold/Chapter2/StrongBundleOne.lean, line 331
- `Polyfold.StrongBundle.toMPolyfold1` — Polyfold/Chapter2/StrongBundleOne.lean, line 365
- `Polyfold.StrongBundle.isScSmoothMap_proj1` — Polyfold/Chapter2/StrongBundleOne.lean, line 373
- `Polyfold.StrongBundle.maximalAtlas` — Polyfold/Chapter3/StrongBundleMaximalAtlas.lean, line 69
- `Polyfold.StrongBundle.maximalAtlas_equiv` — Polyfold/Chapter3/StrongBundleMaximalAtlas.lean, line 78
- `Polyfold.StrongBundle.isChart_iff_exists_equiv` — Polyfold/Chapter3/StrongBundleMaximalAtlas.lean, line 84
- `Polyfold.StrongBundle.isChart_congr` — Polyfold/Chapter3/StrongBundleMaximalAtlas.lean, line 94
- `Polyfold.StrongBundle.IsChart.compatible` — Polyfold/Chapter3/StrongBundleMaximalAtlas.lean, line 55
- `Polyfold.StrongBundle.IsChart.restrict` — Polyfold/Chapter3/StrongBundleMaximalAtlas.lean, line 62

*What differs.*
- $Y[0]$ (the text's "the M-polyfold $Y$") and $Y[1]$ are constructed with the charts induced by the given atlas; the equivalence class of atlases is represented by one atlas, as for M-polyfolds. The notions defined through the charts compatible with the atlas therefore depend only on the class (`isChart_congr`, `isChart_iff_exists_equiv`; Findings, Chapter 2, item 43); those defined with the charts of the given atlas itself ($Y_{m,k}$, $Y[1]$ and its atlas, sc$^+$-sections) are not shown invariant. Updated in the third addendum of this page.
- $Y[1]$ is the subset $Y_{0,1}$ with the topology generated by the sets $\Phi[1]^{-1}(W)$, as for $X_m$ in §2.2; its paracompactness, required of an M-polyfold and not mentioned in the text, follows from metrizability (V2.64).
- Chart independence of $Y_{m,k}$: for $k \le m$ it follows from the $[0]$-transition; for $k = m + 1$, and for the set $Y_{0,1}$ itself, it uses the condition that the $[1]$-transition carries fibre components in $F_1$ to $F'_1$, made explicit in Definition 2.50 (V2.57).

### V2.59. Definition 2.52: sections of a strong bundle

*restated* · sc⁺ chart by chart = sc-smooth into $Y[1]$

**HWZ (§2.5, Definition 2.52, p. 53).** A section is $f : X \to Y$ with $P \circ f = 1_X$; sc-smooth if sc-smooth into $Y[0]$, sc⁺ if sc-smooth into $Y[1]$.

**Proved in Lean.** A section is $f$ with $P \circ f = \mathrm{id}$; it is sc-smooth if it is sc-smooth $X \to Y[0]$ (Definition 2.14); it is an sc⁺-section if in every strong bundle chart of the atlas its fibre values lie in $F_1$ and its representative $z \mapsto \Phi(f(\varphi^{-1}(z)))$, lifted to $E_0 \times F_1$, is sc-smooth from $O$ into $K[1]$. This holds iff $f$ is a section and $f = \iota \circ g$ for an sc-smooth $g : X \to Y[1]$, $\iota : Y[1] \to Y$ the inclusion.

- `Polyfold.IsSection` — Polyfold/Chapter2/StrongBundle.lean, line 727
- `Polyfold.StrongBundle.IsScSmoothSection` — Polyfold/Chapter2/StrongBundle.lean, line 780
- `Polyfold.StrongBundle.localRepOne` — Polyfold/Chapter2/StrongBundle.lean, line 785
- `Polyfold.StrongBundle.IsScPlusSection` — Polyfold/Chapter2/StrongBundle.lean, line 792
- `Polyfold.StrongBundle.isScPlusSection_iff` — Polyfold/Chapter2/StrongBundleOne.lean, line 413

*What differs.*
- Sc⁺-sections are defined chart by chart through $\Phi[1]$; `isScPlusSection_iff` proves that this is the text's "sc-smooth as a map into $Y[1]$", the section being a map into the type $Y[1]$ followed by the inclusion.

### V2.60. Definition 2.53: the pull-back bundle

*as in the book*

**HWZ (§2.5, Definition 2.53, p. 53).** For a strong bundle $P : Y \to X$ and an sc-smooth $f : Z \to X$, $f^*Y = \{(z, y) : P(y) = f(z)\}$, $P_f(z, y) = z$, $P'(z, y) = y$, and $P \circ P' = f \circ P_f$.

**Proved in Lean.** $f^*Y = \{(z, y) \in Z \times Y : P(y) = f(z)\}$ with $P_f$, $P'$ the projections; $P \circ P' = f \circ P_f$; $P_f$ is continuous, and $f^*Y$ is closed in $Z \times Y$ when $X$ is Hausdorff and $P$, $f$ are continuous.

- `Polyfold.pullbackSpace` — Polyfold/Chapter2/StrongBundle.lean, line 804
- `Polyfold.pullbackProj` — Polyfold/Chapter2/StrongBundle.lean, line 808
- `Polyfold.pullbackProj'` — Polyfold/Chapter2/StrongBundle.lean, line 811
- `Polyfold.pullback_comm` — Polyfold/Chapter2/StrongBundle.lean, line 814
- `Polyfold.continuous_pullbackProj` — Polyfold/Chapter2/StrongBundle.lean, line 817
- `Polyfold.isClosed_pullbackSpace` — Polyfold/Chapter2/StrongBundle.lean, line 822

*What differs.*
- As in the text, for any maps $P$, $f$.

### V2.61. Proposition 2.54: the pull-back of a strong bundle is a strong bundle

*hypotheses explicit* · paracompactness of $f^*Y$ proved · atlas of all pulled-back charts

**HWZ (§2.5, Proposition 2.54, p. 53).** $P_f : f^*Y \to Z$ carries a natural structure of a strong bundle over $Z$ (\"the easy proof is left to the reader\").

**Proved in Lean.** For a strong bundle $P : Y \to X$ and an sc-smooth $f : Z \to X$: $f^*Y$ is paracompact (it is metrizable, $Z$ and $Y[0]$ being metrizable by Theorem 2.16), $P_f$ is a continuous surjection, its fibres $P_f^{-1}(z) \cong P^{-1}(f(z))$ are Banachable, and the pulled-back charts $\Phi_f(z, y) = (\psi(z), \mathrm{pr}_F\Phi(y))$, with the strong bundle retractions $R_g(w, h) = (r_Z(w), \Gamma(g(r_Z(w)), h))$, $g = \varphi \circ f \circ \psi^{-1}$, form a strong bundle atlas; so $P_f$ is a strong bundle with this atlas. Locally: $R_g$ is a strong bundle retraction with image $\{(w, h) : w \in O_Z, (g(w), h) \in K\}$; the transition maps of pulled-back charts are $(w, h) \mapsto (\psi_2\psi_1^{-1}(w), \mathrm{pr}_F(\Phi_2\Phi_1^{-1})(g_1(w), h))$, sc-smooth on $[0]$ and $[1]$.

- `Polyfold.proposition_2_54` — Polyfold/Chapter2/StrongBundlePullback.lean, line 595
- `Polyfold.pullbackAtlas` — Polyfold/Chapter2/StrongBundlePullback.lean, line 562
- `Polyfold.PullbackChartData` — Polyfold/Chapter2/StrongBundlePullback.lean, line 140
- `Polyfold.PullbackChartData.toChart` — Polyfold/Chapter2/StrongBundlePullback.lean, line 211
- `Polyfold.PullbackChartData.transition_eqOn` — Polyfold/Chapter2/StrongBundlePullback.lean, line 358
- `Polyfold.PullbackChartData.transition_isScSmooth` — Polyfold/Chapter2/StrongBundlePullback.lean, line 410
- `Polyfold.PullbackChartData.transitionOne_isScSmooth` — Polyfold/Chapter2/StrongBundlePullback.lean, line 469
- `Polyfold.PullbackChartData.compatible_toChart` — Polyfold/Chapter2/StrongBundlePullback.lean, line 526
- `Polyfold.paracompactSpace_pullbackSpace` — Polyfold/Chapter2/StrongBundlePullback.lean, line 555
- `Polyfold.pullbackFiberCLE` — Polyfold/Chapter2/StrongBundlePullback.lean, line 539
- `Polyfold.pullbackRetraction` — Polyfold/Chapter2/StrongBundle.lean, line 458
- `Polyfold.isStrongBundleRetraction_pullback` — Polyfold/Chapter2/StrongBundle.lean, line 478
- `Polyfold.pullback_image` — Polyfold/Chapter2/StrongBundle.lean, line 538
- `Polyfold.isStrongBundleRetract_pullback` — Polyfold/Chapter2/StrongBundle.lean, line 559

*What differs.*
- \"Natural structure\" is the atlas of all pulled-back charts; any two are compatible, so it involves no choice.
- The paracompactness of $f^*Y$, required by Definition 2.51 and not mentioned in the text, is proved from Theorem 2.16 for $Z$ and $Y[0]$.
- “Natural” presumably also says that $P' : f^*Y \to Y$ is a strong bundle map (sc-smooth on $[0]$ and $[1]$); that is not formalized. In the charts $\Phi_f$, $\Phi$ it is $(w, h) \mapsto (g(w), h)$ on $K_g$ (Findings, Chapter 2, item 51; round-trip item V2.61). Recorded in the third addendum of this page.

### V2.62. Theorem 2.55: Smirnov's metrization theorem

*stronger* · proved, not quoted · pull-back form

**HWZ (§2.6.2, Theorem 2.55, p. 56).** A paracompact Hausdorff space in which every point has a metrizable open neighbourhood is metrizable (quoted from Smirnov).

**Proved in Lean.** A paracompact Hausdorff space in which every point has a metrizable open neighbourhood is metrizable. More generally: a space $Y$ with open metrizable $V_i$ and a locally finite family of continuous $\rho_i \ge 0$, $\operatorname{supp}\rho_i \subseteq V_i$, not all zero at any point, is metrizable, with the metric $\sum_i |\rho_i(x) - \rho_i(y)| + \min(\rho_i(x), \rho_i(y)) \min(d_i(x, y), 1)$; and if $\pi : Y \to X$ is continuous into a paracompact Hausdorff $X$ and every point of $X$ has an open $U$ with $\pi^{-1}(U)$ metrizable, $Y$ is metrizable. Metrizable spaces are paracompact (Stone, from Mathlib).

- `Polyfold.metrizableSpace_of_locally` — Polyfold/Chapter2/Metrizable.lean, line 385
- `Polyfold.metrizableSpace_of_partition` — Polyfold/Chapter2/Metrizable.lean, line 206
- `Polyfold.metrizableSpace_of_pullback` — Polyfold/Chapter2/Metrizable.lean, line 368
- `Polyfold.cone_triangle` — Polyfold/Chapter2/Metrizable.lean, line 87
- `Polyfold.truncDist` — Polyfold/Chapter2/Metrizable.lean, line 134
- `Polyfold.paracompactSpace_of_metrizableSpace` — Polyfold/Chapter2/Metrizable.lean, line 391

*What differs.*
- Quoted in the text; proved here (Mathlib does not have it), in the stronger pull-back form that Theorem 2.16 and Proposition 2.19(3) use.

### V2.63. Restriction and locality of sc$^k$ maps

*not in the book* · used silently in the text

**HWZ (§2.1–§2.2, used in Propositions 2.4, 2.10 and Definitions 2.13–2.14, p. 19).** Used without statement: an sc-smooth map restricted to a smaller relatively open set is sc-smooth (e.g. \"$r : U \to U \cap U'$ is sc-smooth\"), and sc-smoothness is a local property.

**Proved in Lean.** On sc-domains: an $\mathrm{sc}^k$ (sc-smooth) map on $U$ is $\mathrm{sc}^k$ (sc-smooth) on every smaller sc-domain $U'$, with the same tangent map on $TU'$; a map that is $\mathrm{sc}^1$, $\mathrm{sc}^k$ or sc-smooth on $U \cap W$ for an open $W$ around each point of $U$ is so on $U$; sc-smoothness depends only on the values on $U$.

- `Polyfold.IsSck.of_subset` — Polyfold/Chapter2/Retracts.lean, line 112
- `Polyfold.IsScSmooth.of_subset` — Polyfold/Chapter2/Retracts.lean, line 120
- `Polyfold.IsSc1.tangentMap_eqOn_of_subset` — Polyfold/Chapter2/Retracts.lean, line 107
- `Polyfold.IsSc1.of_locally` — Polyfold/Chapter2/Retracts.lean, line 187
- `Polyfold.IsSck.of_locally` — Polyfold/Chapter2/Retracts.lean, line 229
- `Polyfold.IsScSmooth.of_locally` — Polyfold/Chapter2/Retracts.lean, line 247
- `Polyfold.IsScSmooth.congr` — Polyfold/Chapter2/Retracts.lean, line 123

*What differs.*
- Not stated in the text. The restriction needs the uniqueness of derivatives on the smaller domain, because the tangent map is built from a chosen derivative; the locality glues the local derivatives into one family.

### V2.64. The space $Y[1]$ and the inclusion $Y[1] \to Y[0]$

*not in the book* · not in the text · paracompact by Smirnov

**HWZ (§2.5, after Definition 2.51, p. 52).** Not stated: the text takes $Y[1]$ to be an M-polyfold on the set $Y_{0,1}$ without discussing its topology, its paracompactness or its inclusion into $Y[0]$.

**Proved in Lean.** $Y_{0,1}$ is the set of points whose fibre component lies in $F_1$ in one, equivalently every, chart of the atlas around them. With the topology generated by the charts $\Phi[1]$, the inclusion $Y[1] \to Y$ is continuous, so $Y[1]$ is Hausdorff; $Y[1]$ is metrizable, hence paracompact; and the inclusion $Y[1] \to Y[0]$ is sc-smooth (in the charts it is $(u, h) \mapsto (u, \iota h)$).

- `Polyfold.StrongBundle.oneSet` — Polyfold/Chapter2/StrongBundleOne.lean, line 91
- `Polyfold.StrongBundle.mem_oneSet_iff` — Polyfold/Chapter2/StrongBundleOne.lean, line 96
- `Polyfold.StrongBundle.One` — Polyfold/Chapter2/StrongBundleOne.lean, line 105
- `Polyfold.StrongBundle.continuous_oneVal` — Polyfold/Chapter2/StrongBundleOne.lean, line 132
- `Polyfold.StrongBundle.metrizableSpace_one` — Polyfold/Chapter2/StrongBundleOne.lean, line 343
- `Polyfold.StrongBundle.paracompactSpace_one` — Polyfold/Chapter2/StrongBundleOne.lean, line 359
- `Polyfold.StrongBundle.isScSmoothMap_oneVal` — Polyfold/Chapter2/StrongBundleOne.lean, line 394

*What differs.*
- Not stated in the text. Paracompactness is needed for $Y[1]$ to be an M-polyfold (Definition 2.13); it follows, as in Theorem 2.16, from the pull-back form of Smirnov's theorem over the paracompact base (V2.62).
- The sc-smooth inclusion $Y[1] \to Y[0]$ is the global form of $K[1] \to K[0]$ (V2.55).

## Chapter 3

*HWZ Chapter 3: sc-Fredholm sections and the implicit function theorem*

### V3.1. Definition 3.1: sc-germs of neighbourhoods

*restated* · a germ is a fixed sequence of sets

**HWZ (§3.1, Definition 3.1, p. 62).** An sc-germ of neighbourhoods $\mathcal O(C, 0)$ around $0$ in a partial quadrant $C \subseteq E$ is a decreasing sequence $U_0 \supset U_1 \supset \cdots$ with $U_m$ a relatively open neighbourhood of $0$ in $C_m = C \cap E_m$; its tangent $T\mathcal O(C, 0)$ is $U_1 \oplus E_0 \supset U_2 \oplus E_1 \supset \cdots$. A relatively open $U \ni 0$ with $U_m = U \cap E_m$ is an example; \"the size of the sets $U_m$ does not matter\".

**Proved in Lean.** An `ScNbhdGerm E C` is a family of sets $U_m \subseteq E_m$, each of the form $O \cap C_m$ with $O$ open and $0 \in U_m$, nested along the inclusions $E_{m+1} \to E_m$. Its tangent germ has levels $U_{m+1} \times E_m$; `ofSet` is the text's example $U_m = U \cap E_m$. The theorems on germs ask $C$ to be *quadrant-like* (every $C_m$ convex with nonempty interior, $0 \in C$), which every partial quadrant is; then derivatives on $U_1$ are unique.

- `Polyfold.ScNbhdGerm` — Polyfold/Chapter3/Germ.lean, line 123
- `Polyfold.ScNbhdGerm.tangent` — Polyfold/Chapter3/Germ.lean, line 165
- `Polyfold.ScNbhdGerm.ofSet` — Polyfold/Chapter3/Germ.lean, line 181
- `Polyfold.IsQuadrantLike` — Polyfold/Chapter3/Germ.lean, line 65
- `Polyfold.IsPartialQuadrant.isQuadrantLike` — Polyfold/Chapter3/Germ.lean, line 70
- `Polyfold.ScNbhdGerm.uniqueDiffWithinAt` — Polyfold/Chapter3/Germ.lean, line 153

*What differs.*
- A germ is a fixed sequence of sets, not a class \"up to shrinking\". The text's remark that the size of the $U_m$ does not matter is therefore not built in; where it matters (Theorems 3.30, 3.33–3.35) the formal statements say on which germ they hold (V3.27, V3.30–V3.32).
- The re-indexed sequence $(U_{m+1})_m$ is a germ only when all levels coincide (a finite-dimensional parameter space); the text does not remark this, and the germ implicit function theorem uses it once per derivative.

### V3.2. Definition 3.2: sc$^k$-germs

*as in the book*

**HWZ (§3.1, Definition 3.2, pp. 62–63).** An sc$^0$-germ $f : \mathcal O(C, 0) \to F$ is a continuous $f : U_0 \to F$ with $f(U_m) \subseteq F_m$ and $f : U_m \to F_m$ continuous. It is sc$^1$ if for $x \in U_1$ there is a bounded $Df(x) : E_0 \to F_0$ with $|f(x + h) - f(x) - Df(x)h|_0 / |h|_1 \to 0$ ($h \in E_1$, $x + h \in U_1$) and $Tf(x, h) = (f(x), Df(x)h)$ is an sc$^0$-germ on $T\mathcal O(C, 0)$; sc$^k$ inductively, sc-smooth if sc$^k$ for all $k$.

**Proved in Lean.** `IsSc0Germ`, `IsSc1GermWith` (with a given derivative family), `IsSc1Germ`, `IsSckGerm`, `IsScSmoothGerm` are the notions of Definitions 1.12–1.15 with $U \cap E_m$ replaced by $U_m$. An sc$^k$ map on a relatively open $U \ni 0$ is an sc$^k$-germ on `ofSet U`.

- `Polyfold.IsSc0Germ` — Polyfold/Chapter3/Germ.lean, line 237
- `Polyfold.IsSc1GermWith` — Polyfold/Chapter3/Germ.lean, line 314
- `Polyfold.IsSc1Germ` — Polyfold/Chapter3/Germ.lean, line 322
- `Polyfold.IsSckGerm` — Polyfold/Chapter3/Germ.lean, line 447
- `Polyfold.IsScSmoothGerm` — Polyfold/Chapter3/Germ.lean, line 452
- `Polyfold.IsSck.isSckGerm` — Polyfold/Chapter3/Germ.lean, line 532
- `Polyfold.IsScSmooth.isScSmoothGerm` — Polyfold/Chapter3/Germ.lean, line 545

*What differs.*
- As in the text, with the derivative family chosen (as in Chapter 1); it is unique on $U_1$ for quadrant-like $C$ (`IsSc1GermWith.eq_of_uniqueDiffWithinAt`).

### V3.3. The calculus of germs

*not in the book* · not stated in the text · composition needs level-wise maps-to

**HWZ (§3.1–§3.3, used without statement (proofs of Lemma 3.31, Theorems 3.33, 3.38), p. 62).** Not stated: the text restricts, composes and pairs germs and applies sc-operators to them as it does with maps on open sets.

**Proved in Lean.** (1) sc$^k$-germs depend only on the values on $U_0$ and restrict to smaller germs; (2) the chain rule: if $f$ is an sc$^k$-germ on $G$, $g$ an sc$^k$-germ on $G'$ and $f$ maps $U_m$ into $U'_m$ for every $m$, then $g \circ f$ is an sc$^k$-germ and $T(g \circ f) = Tg \circ Tf$ on $TG$; (3) sc-operators are sc-smooth germs on every germ; (4) the pairing of two sc$^k$-germs is an sc$^k$-germ; (5) the germ $\{x \in G_0 : f(x) \in G'\}$ on which an sc$^0$-germ maps into a given germ.

- `Polyfold.IsSckGerm.congr` — Polyfold/Chapter3/Germ.lean, line 491
- `Polyfold.IsSckGerm.mono` — Polyfold/Chapter3/Germ.lean, line 499
- `Polyfold.ScNbhdGerm.MapsToGerm` — Polyfold/Chapter3/Germ.lean, line 224
- `Polyfold.IsSckGerm.comp` — Polyfold/Chapter3/Germ.lean, line 755
- `Polyfold.IsSc1Germ.comp` — Polyfold/Chapter3/Germ.lean, line 743
- `Polyfold.ScOperator.isScSmoothGerm` — Polyfold/Chapter3/Germ.lean, line 807
- `Polyfold.IsSckGerm.pair` — Polyfold/Chapter3/Germ.lean, line 866
- `Polyfold.ScNbhdGerm.preimage` — Polyfold/Chapter3/GermFilling.lean, line 77

*What differs.*
- The chain rule needs the inner germ to map $U_m$ into the domain $U'_m$ of the outer one on every level (`ScNbhdGerm.MapsToGerm`); for maps on open sets this is $f(U) \subseteq V$. The shrinking of germs that the text performs with \"near $0$\" is `ScNbhdGerm.preimage`.

### V3.4. Propositions 1.16–1.18 for germs

*not in the book* · germ versions of Chapter 1

**HWZ (§3.1, proof of Lemma 3.9 ("recalling Proposition 1.17"), Lemma 3.31, Corollary 3.34, p. 67).** Not stated: Propositions 1.16–1.18 are stated in Chapter 1 for relatively open sets; the proofs of Lemma 3.9, Lemma 3.31 and Corollary 3.34 apply them to germs.

**Proved in Lean.** For an sc$^1$-germ $f$ with derivative family $D$: $Df(x)$, $x \in U_{m+1}$, restricts to bounded level operators $E_m \to F_m$, jointly continuous in $(x, h)$ (also in operator norm), and $f : U_{m+1} \to F_m$ is differentiable within $U_{m+1}$ with these derivatives (1.16); the shifted sequence $(U_{m+1})_m$ is a germ in $E^1$ and an sc$^k$-germ on $G$ is an sc$^k$-germ $G^1 \to F^1$ (1.17); an sc$^k$-germ is $C^k$ from $U_{m+k}$ to $F_m$ (1.18).

- `Polyfold.IsSc1GermWith.exists_levelDeriv` — Polyfold/Chapter3/GermLevels.lean, line 90
- `Polyfold.IsSc1GermWith.continuousOn_levelDeriv` — Polyfold/Chapter3/GermLevels.lean, line 134
- `Polyfold.IsSc1GermWith.continuousOn_levelDeriv_clm` — Polyfold/Chapter3/GermLevels.lean, line 140
- `Polyfold.IsSc1GermWith.hasFDerivWithinAt_level` — Polyfold/Chapter3/GermLevels.lean, line 148
- `Polyfold.ScNbhdGerm.shift` — Polyfold/Chapter3/GermLevels.lean, line 257
- `Polyfold.IsSckGerm.shift` — Polyfold/Chapter3/GermLevels.lean, line 311
- `Polyfold.IsSckGerm.contDiffOn_levels` — Polyfold/Chapter3/GermLevels.lean, line 398

*What differs.*
- The proofs are those of Chapter 1 with $U \cap E_m$ replaced by $U_m$. The text's \"recalling Proposition 1.17\" in Lemma 3.9 is Proposition 1.16 for germs.

### V3.5. Definition 3.3: sc-smooth section germs

*hypotheses explicit* · chart compatible with the atlas

**HWZ (§3.1, Definition 3.3, p. 63).** An sc-smooth section germ $(f, x_0)$ of $P : Y \to X$ is a continuous section $f : V \to P^{-1}(V)$ near the smooth point $x_0$ such that in a strong bundle chart with $\varphi(x_0) = 0$ the principal part $\mathbf f$ of $\Phi \circ f \circ \varphi^{-1} : O \to K$ has $\mathbf f \circ r : \mathcal O(C, 0) \to F$ an sc-smooth germ.

**Proved in Lean.** `StrongBundle.IsScSmoothSectionGerm f x₀`: $x_0$ smooth, and for some strong bundle chart compatible with the atlas (`StrongBundle.IsChart`) with $\varphi(x_0) = 0$, $\mathbf f \circ r$ is an sc-smooth germ on some sc-germ of neighbourhoods $G$ with $G_0 \subseteq U$, whose levels may shrink with $m$ (the text’s germ reading). An sc-smooth section is an sc-smooth section germ at every smooth point with a centred chart (with the germ $U \cap E_m$).

- `Polyfold.StrongBundle.IsScSmoothSectionGerm` — Polyfold/Chapter3/StrongBundleSections.lean, line 702
- `Polyfold.StrongBundle.IsChart` — Polyfold/Chapter3/StrongBundleSections.lean, line 345
- `Polyfold.StrongBundle.IsScSmoothSection.isScSmoothSectionGerm` — Polyfold/Chapter3/StrongBundleSections.lean, line 712
- `Polyfold.StrongBundleChart.principal` — Polyfold/Chapter3/StrongBundleSections.lean, line 246
- `Polyfold.StrongBundle.isChart_congr` — Polyfold/Chapter3/StrongBundleMaximalAtlas.lean, line 94
- `Polyfold.exists_isScSmoothGerm_not_isScSmooth` — Polyfold/Chapter3/GermVsChart.lean, line 531

*What differs.*
- \"A strong bundle chart\" is read as a chart compatible with the atlas, not a member of it: a chart of the atlas need not be centred at $x_0$, and the notion must not depend on the atlas within its class (Findings, Chapter 3, item 41). That it does not is proved: equivalent atlases have the same compatible charts (`isChart_congr`; V2.58, Findings, Chapter 2, item 43). Updated in the third addendum of this page.
- Continuity of $f$ near $x_0$ is not a separate field: it follows near $x_0$ from the continuity of $\mathbf f \circ r$ on level $0$ of the germ.
- **Germs.** Since the fourth addendum of this page the definition is in the text’s germ reading: $\mathbf f \circ r$ is an sc-smooth germ on some sc-germ of neighbourhoods inside $U$, whose levels may shrink with $m$, as for Definitions 3.4, 3.6 and 3.11 since phase 2. Before, it was required on the whole $U$ of the chart (levels $U \cap E_m$), which is stricter: a function $C^k$ on $(-1/k, 1/k)$ for every $k$ is an sc-smooth germ in the constant scale $\mathbb R$ and sc-smooth on no neighbourhood of $0$ (`exists_isScSmoothGerm_not_isScSmooth`). No theorem assumes the definition. Hence “hypotheses explicit” again (“narrower” from the third addendum until the fourth) (Findings, Chapter 3, items 220–221, 260; round-trip item V3.5).

### V3.6. The section algebra and the sum rule

*not in the book* · not stated in the text · first use of the [1]-compatibility

**HWZ (§3.1, used in Theorems 3.12, 3.15 ("$f + s$ is an sc-smooth section"), p. 71).** Not stated: the fibrewise sum of sections, principal parts in a chart, the sum rule of the sc-calculus, and the sc-smoothness of the local representatives of sc$^+$-sections in a chart that is not in the atlas.

**Proved in Lean.** The fibrewise sum $f + s$ is a section with principal part $\mathbf f + \mathbf s$ in every chart; $f(x) = 0$ iff $\mathbf f(\varphi(x)) = 0$; the fibres of $K$ are linear. Sums, differences and negatives of sc-smooth maps on relatively open subsets of partial quadrants are sc-smooth. In every strong bundle chart compatible with the atlas, $z \mapsto (z, \mathbf f(z))$ is sc-smooth $O \to K$ for an sc-smooth section and $z \mapsto (z, \mathbf s_1(z))$ is sc-smooth $O \to K[1]$ for an sc$^+$-section.

- `Polyfold.IsScSmooth.add` — Polyfold/Chapter3/StrongBundleSections.lean, line 149
- `Polyfold.IsScSmooth.sub` — Polyfold/Chapter3/StrongBundleSections.lean, line 161
- `Polyfold.sectionAdd` — Polyfold/Chapter3/StrongBundleSections.lean, line 213
- `Polyfold.IsSection.sectionAdd` — Polyfold/Chapter3/StrongBundleSections.lean, line 229
- `Polyfold.StrongBundleChart.principal_sectionAdd` — Polyfold/Chapter3/StrongBundleSections.lean, line 287
- `Polyfold.StrongBundleChart.isZeroAt_iff` — Polyfold/Chapter3/StrongBundleSections.lean, line 295
- `Polyfold.StrongBundleChart.add_mem_K` — Polyfold/Chapter3/StrongBundleSections.lean, line 318
- `Polyfold.StrongBundle.IsScSmoothSection.isScSmoothRetractMap` — Polyfold/Chapter3/StrongBundleSections.lean, line 360
- `Polyfold.StrongBundle.IsScPlusSection.isScSmoothRetractMap_one` — Polyfold/Chapter3/StrongBundleSections.lean, line 395

*What differs.*
- For an sc$^+$-section in a chart outside the atlas the sc-smoothness of the representative is the change of chart $(\Phi \circ \Phi'^{-1})[1]$, i.e. the compatibility on $[1]$ of Definition 2.50; this is its first use (Findings, Chapter 3, item 41).
- The sum rule is pairing followed by the sc-operator $F \oplus F \to F$.

### V3.7. Definition 3.4: fillers

*hypotheses explicit* · sc¹ of the map in (3) required · principal parts only

**HWZ (§3.1, Definition 3.4, p. 64).** For a tame strong local bundle $K = R(U \triangleleft F) \to O$, $R(u, h) = (r(u), \rho(u)h)$, $r(0) = 0$, an sc-smooth section germ $(f, 0)$ has a filling $(g, 0)$ (an sc-smooth section germ of $U \triangleleft F \to U$) if (1) $f = g$ on $O$ near $0$; (2) $g(y) = \rho(r(y))g(y)$ for $y \in U$ near $0$ forces $y \in O$; (3) the linearization of $y \mapsto [1 - \rho(r(y))]g(y)$ at $0$, restricted to $\ker Dr(0)$, is a topological isomorphism onto $\ker\rho(0)$.

**Proved in Lean.** `IsFillingGerm` for the principal parts $f, g : E_0 \to F_0$ (the text’s germ reading, also Definition 3.6, V3.9): $g$ is an sc-smooth germ on an sc-germ of neighbourhoods $G$ with $G_0 \subseteq U$; (1) and (2) near $0$; (3) the map $y \mapsto [1 - \rho(r(y))]g(y)$ (`fillDefect`) is an sc$^1$-germ on $G$ with a derivative family $Dk$, and $Dk(0)$ induces a continuous linear equivalence $\ker Dr(0) \simeq \ker\rho(0)$. Here $r(u) = (R(u, 0))_1$, $\rho(u)h = (R(u, h))_2$, with $R(u, h) = (r(u), \rho(u)h)$, $r \circ r = r$, $\rho(x)$ a projection for $x \in O$, and $\rho(u)$ a bounded operator. The whole-chart form `IsFillerOf` asks the map in (3) to be sc$^1$ on all of $U$ and says nothing about the regularity of $g$.

- `Polyfold.IsFillingGerm` — Polyfold/Chapter3/GermFilling.lean, line 143
- `Polyfold.fillDefect` — Polyfold/Chapter3/GermFilling.lean, line 131
- `Polyfold.fillDefect_isScSmoothGerm` — Polyfold/Chapter3/GermCalculus.lean, line 606
- `Polyfold.IsFillerOf` — Polyfold/Chapter3/Filler.lean, line 158
- `Polyfold.StrongRetr.r` — Polyfold/Chapter3/Filler.lean, line 78
- `Polyfold.StrongRetr.ρ` — Polyfold/Chapter3/Filler.lean, line 81
- `Polyfold.StrongRetr.apply_eq` — Polyfold/Chapter3/Filler.lean, line 86
- `Polyfold.StrongRetr.ρ_ρ` — Polyfold/Chapter3/Filler.lean, line 114
- `Polyfold.StrongRetr.ρCLM` — Polyfold/Chapter3/Filler.lean, line 139

*What differs.*
- Condition (3) presupposes that $y \mapsto [1 - \rho(r(y))]g(y)$ is differentiable at $0$; it is required to be an sc$^1$-germ with a derivative family, which holds for every sc-smooth germ $g$ (`fillDefect_isScSmoothGerm`); the value of the family at $0$ is unique (Findings, Chapter 3, items 261, 272).
- The sc-smoothness of $g$ is part of the filling, as in the text (“$(g, 0)$ an sc-smooth section germ”); tameness of the retraction is not used.
- **Germs.** Since the switch to the text’s germ reading (phase 2) $g$ and the map in (3) are germs whose levels may shrink with $m$ (`IsFillingGerm`); the stricter whole-chart filler (`IsFillerOf`, with $g$ sc-smooth on all of $U$ added in `IsFilledVersion`) is kept for the `…WholeChart` notions. Hence “hypotheses explicit” again (“narrower” in the third addendum) (Findings, Chapter 3, items 220–221, 261, 330; round-trip items V3.7, V3.19). On the text’s domain of definition, tame strong local bundles, it is not broader: tameness is simply not used.

### V3.8. Proposition 3.5: the filler and the linearization

*stronger* · index equality without finiteness · $Tf(0)$ is $Dg(0)$ on $Dr(0)E$ · sc form: filler (3) on level 0 suffices · sc converse needs (3) on every level

**HWZ (§3.1, the paragraph after Definition 3.4 and Proposition 3.5, pp. 64–65).** If $f$ has the filling $g$ and $f(0) = 0$, then in the splittings $E = Dr(0)E \oplus \ker Dr(0)$, $F = \rho(0)F \oplus \ker\rho(0)$, $Dg(0) = \begin{pmatrix} Tf(0) & * \\ 0 & C \end{pmatrix}$ with $C$ an isomorphism, and (1) $Tf(0) : Dr(0)E \to \rho(0)F$ is onto iff $Dg(0)$ is; (2) $Tf(0)$ is Fredholm iff $Dg(0)$ is, with equal index.

**Proved in Lean.** For a filler $g$ of $f$ with $g$ sc-smooth, $g(0) = 0$ and $f$ a section of $K \to O$: $D(\rho(r(\cdot))g)(0) = \rho(0)Dg(0)$, $(1 - \rho(0))Dg(0)Dr(0) = 0$, $D(f \circ r)(0) = Dg(0)Dr(0)$; and $Tf(0) := Dg(0)|_{Dr(0)E} : Dr(0)E \to \rho(0)F$ is onto iff $Dg(0)$ is, Fredholm iff $Dg(0)$ is, and $\mathrm{ind}\,Tf(0) = \mathrm{ind}\,Dg(0)$. The linear algebra holds for any idempotents $p, q$ and $L$ with $(1 - q)Lp = 0$ and $(1 - q)L : \ker p \to \ker q$ a topological isomorphism. In sc form: if $Dg(0)$ is an sc-Fredholm sc-operator, then $Dr(0)E$, $\rho(0)F$, $\ker Dr(0)$ and $\ker\rho(0)$ are sc-subspaces, $Tf(0) : Dr(0)E \to \rho(0)F$ is sc-Fredholm, of index $\mathrm{ind}\,Dg(0)$ on every level, and $(1 - \rho(0))Dg(0) : \ker Dr(0) \to \ker\rho(0)$ is an sc-isomorphism (condition (3) of the filler on every level). Conversely, for $Dg(0)$ an sc-operator: $Dg(0)$ is sc-Fredholm if and only if $Tf(0)$ is sc-Fredholm and condition (3) holds on every level. The same for a filling germ (V3.7), with $Dg(0)$ the value at $0$ of any derivative family of $g$ on any germ (`IsFillingGerm.proposition_3_5`, `IsFillingGerm.proposition_3_5_sc`, `IsFillingGerm.proposition_3_5_sc_iff`).

- `Polyfold.IsFillerOf.proposition_3_5` — Polyfold/Chapter3/FillerLinearization.lean, line 341
- `Polyfold.proposition_3_5` — Polyfold/Chapter3/FillerLinearAlgebra.lean, line 346
- `Polyfold.fillerRestrict` — Polyfold/Chapter3/FillerLinearAlgebra.lean, line 64
- `Polyfold.fillerRestrict_kerEquiv` — Polyfold/Chapter3/FillerLinearAlgebra.lean, line 185
- `Polyfold.fillerRestrict_cokerEquiv` — Polyfold/Chapter3/FillerLinearAlgebra.lean, line 209
- `Polyfold.StrongRetr.scDeriv_fiber_zero` — Polyfold/Chapter3/FillerLinearization.lean, line 122
- `Polyfold.IsFillerOf.deriv_comp_r_eq_zero` — Polyfold/Chapter3/FillerLinearization.lean, line 273
- `Polyfold.IsFillerOf.exists_kerEquiv` — Polyfold/Chapter3/FillerLinearization.lean, line 320
- `Polyfold.IsFillerOf.scDeriv_section_comp_r` — Polyfold/Chapter3/FillerLinearization.lean, line 357
- `Polyfold.IsScFredholm.restrict` — Polyfold/Chapter1/ScFredholmCriterion.lean, line 307
- `Polyfold.IsFillerOf.proposition_3_5_sc` — Polyfold/Chapter3/FredholmGermLinearizationSc.lean, line 319
- `Polyfold.IsFillerOf.filler_condition_three_sc` — Polyfold/Chapter3/LinearizationChartsSc.lean, line 351
- `Polyfold.IsFillerOf.proposition_3_5_sc_converse` — Polyfold/Chapter3/LinearizationChartsSc.lean, line 412
- `Polyfold.IsFillerOf.proposition_3_5_sc_iff` — Polyfold/Chapter3/LinearizationChartsSc.lean, line 481
- `Polyfold.IsFillingGerm.proposition_3_5` — Polyfold/Chapter3/GermFillerLinearization.lean, line 148
- `Polyfold.IsFillingGerm.exists_kerEquiv` — Polyfold/Chapter3/GermFillerLinearization.lean, line 62
- `Polyfold.IsFillingGerm.deriv_comp_r_eq_zero` — Polyfold/Chapter3/GermFillerLinearization.lean, line 81
- `Polyfold.IsFillingGerm.proposition_3_5_sc` — Polyfold/Chapter3/FredholmGermLinearizationScG.lean, line 145
- `Polyfold.IsFillingGerm.filler_condition_three_sc` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 128
- `Polyfold.IsFillingGerm.proposition_3_5_sc_converse` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 184
- `Polyfold.IsFillingGerm.proposition_3_5_sc_iff` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 251

*What differs.*
- The proof exhibits $\ker Tf(0) \simeq \ker Dg(0)$ and $\mathrm{coker}\,Tf(0) \simeq \mathrm{coker}\,Dg(0)$ directly instead of the text's factorization and additivity of the index, so the index equality holds as $\dim\ker - \dim\mathrm{coker}$ with no finiteness assumption; closedness of the ranges transfers through the continuous $y \mapsto y - LC^{-1}(1 - q)y$, which is where \"topological\" in (3) is used.
- The text's \"by linearization at $y = 0$\" needs $(u, h) \mapsto \rho(u)h$ differentiable and $g(0) = 0$; the target \"$(1 - D\rho(0))F$\" is $(1 - \rho(0))F$ (Findings, Chapter 3, item 47).
- Proposition 3.5 (2) is a level-$0$ statement. Its sc form in the direction Proposition 3.52 uses (“$Dg(0)$ sc-Fredholm ⟹ $Tf(0)$ sc-Fredholm”) needs condition (3) of the filler on level $0$ only, as the text states it: the higher levels of $Tf(0)$ come from the regularity of $Dg(0)$ (`IsScFredholm.restrict`), and condition (3) on every level then follows at the zero. The converse in sc form needs condition (3) on every level as a hypothesis; with level $0$ only it fails (an example on a weighted $\ell^2$ with the shift, Findings, Chapter 3, item 238, not formalized). Nothing in the text uses the converse (Findings, Chapter 3, items 234, 237, 238). Updated in the third addendum of this page.
- For filling germs (the text’s reading of Definition 3.4) the proofs are the same, with the derivative family of the fill defect in place of the derivative on $U$ (Findings, Chapter 3, items 272, 289, 314). Updated after the switch of Definition 3.11 to the text’s germ reading (phase 2).

### V3.9. Definition 3.6: filled versions

*restated* · local data; the chart in Def. 3.11

**HWZ (§3.1, Definition 3.6, p. 66).** $(f, x_0)$ has a filling if in a strong bundle chart with $\varphi(x_0) = 0$ the section germ $\Phi \circ f \circ \varphi^{-1} : O \to K$ has a filling $g : U \to U \triangleleft F$ near $0$; $(g, 0)$ is a filled version.

**Proved in Lean.** `IsFillingGerm fb g` (V3.7): $g$ is an sc-smooth germ on an sc-germ of neighbourhoods $G$, $G_0 \subseteq U$, whose levels may shrink with $m$, and fills the principal part $\mathbf f$ near $0$; the centred chart is that of Definition 3.11 (V3.13). The whole-chart form `IsFilledVersion` ($g$ sc-smooth on all of $U$, filling in the sense of `IsFillerOf`) is a filling (`IsFilledVersion.isFillingGerm`), and a filling sc-smooth on all of $U$ is a filled version (`IsFillingGerm.isFilledVersion`).

- `Polyfold.IsFillingGerm` — Polyfold/Chapter3/GermFilling.lean, line 143
- `Polyfold.IsFilledVersion` — Polyfold/Chapter3/StrongBundleSections.lean, line 514
- `Polyfold.IsFilledVersion.isFillingGerm` — Polyfold/Chapter3/GermFillingChart.lean, line 41
- `Polyfold.IsFillingGerm.isFilledVersion` — Polyfold/Chapter3/GermFillingChart.lean, line 65

*What differs.*
- The text asks for a filling of the section germ in some strong bundle chart centred at $x_0$; the formal notion is the datum in a given chart, for the principal parts, and the centred chart is quantified in Definition 3.11 (V3.13).
- **Germs.** Since the switch to the text’s germ reading (phase 2) the filling is a germ (`IsFillingGerm`). The earlier filled version, sc-smooth on all of $U$, is stricter (round-trip items V3.9, V3.43) and is kept as `IsFilledVersion`, exactly the fillings sc-smooth on $U$. Hence “restated” again (“narrower” in the third addendum) (Findings, Chapter 3, items 220–221, 260–262, 330).

### V3.10. Definition 3.7: basic germs

*restated* · finite-dimensional $P$, $Q$ · points of the balls lie in $U_m$

**HWZ (§3.1, Definition 3.7, p. 66).** A basic germ is an sc-smooth germ $f : \mathcal O([0, \infty)^k \oplus \mathbb R^{n-k} \oplus W, 0) \to \mathbb R^N \oplus W$ with $f(0) = 0$ and $P_W \circ f(a, w) = w - B(a, w)$, $B(0, 0) = 0$, $|B(a, w) - B(a, w')|_m \le \varepsilon|w - w'|_m$ for $(a, w), (a, w')$ close enough to $(0, 0)$ on level $m$, for every $\varepsilon > 0$, $m \ge 0$.

**Proved in Lean.** `IsBasicGerm C̃ G f B`: $f$ an sc-smooth germ on the germ $G$ around $0$ in $\widetilde C \oplus W$ with $f(0) = 0$, whose $W$-component is $w - B(a, w)$ on $U_0$, with $B$ an sc$^0$-contraction germ (V3.25: $B$ sc$^0$, $B(0, 0) = 0$, and the contraction estimate on balls whose points lie in $U_m$). $\widetilde C$ is a quadrant-like subset of a finite-dimensional $P$, $\mathbb R^N$ any finite-dimensional $Q$.

- `Polyfold.IsBasicGerm` — Polyfold/Chapter3/LocalCompactness.lean, line 139
- `Polyfold.IsSc0ContractionGerm` — Polyfold/Chapter3/ContractionGerm.lean, line 143

*What differs.*
- \"Close enough on level $m$\" presupposes that the points lie in the domain $U_m$; this is required. The theorems that use basic germs add \"$\widetilde C$ closed\" or \"a partial quadrant\" where needed.
- Remark 3.8 (in [21] $f(0) = 0$ was not required) is a historical remark and makes no claim.

### V3.11. Lemma 3.9: the fibre derivative of $B$ is small

*stronger* · sc¹ suffices · every $\varepsilon$, every level $m$

**HWZ (§3.1, Lemma 3.9, p. 67).** For $B$ as in Definition 3.7, every $\varepsilon > 0$ and $m \ge 0$: $|D_2B(a, w)\zeta|_m \le \varepsilon|\zeta|_m$ for $\zeta \in W_m$ if $(a, w) \in E_{m+1}$ is close enough to $(0, 0)$ in $E_m$; in particular $D_2B(0, 0) = 0$.

**Proved in Lean.** Four formal forms: (a) on level $m$, for an sc$^1$-germ $B$ in the working form of a contraction germ, $\|D_2B(a, w)\|_{L(W_m)} \le \tfrac12$ at points $(a, w) \in U_{m+1}$ with $a \in N(m+1)$, $w \in O(m+1)$, $\iota w \in O(m)$; (b) $D_2B(0, 0) = 0$ for an sc$^1$ sc$^0$-contraction germ; (c) on level $0$ with arbitrary $\varepsilon$: $|D_2B(x)\zeta|_0 \le \varepsilon|\zeta|_0$ for $x \in U_1$ small on level $1$. (d) **as stated**: for $B$ an sc$^1$ sc$^0$-contraction germ on a quadrant-like $\widetilde C$, for every $\varepsilon > 0$ and every $m$ there is $r > 0$ with $|D_2B(x)\zeta|_m \le \varepsilon|\zeta|_m$ for $\zeta \in W_m$ at every $x \in U_{m+1}$ with $|x|_m < r$.

- `Polyfold.ContractionGerm.norm_levelDeriv_snd_le` — Polyfold/Chapter3/ContractionGerm.lean, line 392
- `Polyfold.IsSc0ContractionGerm.deriv_zero_snd` — Polyfold/Chapter3/BasicGermLinearization.lean, line 107
- `Polyfold.IsSc0ContractionGerm.exists_norm_deriv_snd_le` — Polyfold/Chapter3/SolutionLinearization.lean, line 180
- `Polyfold.IsSc0ContractionGerm.exists_norm_levelDeriv_snd_le` — Polyfold/Chapter3/SolutionLinearization.lean, line 411

*What differs.*
- Stronger in regularity: $B$ sc$^1$ suffices (Theorem 3.30 and Lemma 3.31 apply the lemma to sc$^1$ and sc$^k$ germs).
- The general statement (every $\varepsilon$, every level $m$, points of $E_{m+1}$ small in $E_m$) is proved as stated, from the contraction estimate of Definition 3.28 applied at points small on level $0$; smallness on level $m + 1$ is not needed (Findings, Chapter 3, item 215). It is what Proposition 3.10 on level $m$ (V3.12) and Lemma 3.31 in the sense of Definition 3.28 (V3.28) use. The constant $\tfrac12$ on level $m$ in the working form, the value at $(0, 0)$ and the level-$0$ form are kept for the theorems that use them. Formerly narrower (the general statement not formalized). Updated in the third addendum of this page.

### V3.12. Proposition 3.10: the linearization of a basic germ plus an sc$^+$-germ

*stronger* · second statement on every level $m$ · sc$^1$ suffices; $f(0) = 0$ not used

**HWZ (§3.1, Proposition 3.10, p. 68).** If $f = h + s$ with $h$ a basic germ and $s$ an sc$^+$-germ, $f(0) = 0$, then $Df(0) : \mathbb R^n \oplus W \to \mathbb R^N \oplus W$ is sc-Fredholm of index $n - N$; and for every $m$, $Df(a, w)$ on level $m$ is Fredholm of index $n - N$ for $(a, w) \in E_{m+1}$ small in $E_m$.

**Proved in Lean.** For a basic germ $h$, an $s$ sc$^1$ into $(\mathbb R^N \oplus W)^1$ and $f = h + s$ sc$^1$: $Df(0)$ is an sc-operator, sc-Fredholm of index $\dim P - \dim Q$; it is $T_0 + S$ with $T_0(\delta a, \delta w) = (0, \delta w)$ (sc-Fredholm of index $n - N$) and an sc$^+$-operator $S$ built level by level. For the data of Theorem 3.38 and $x \in U_1$ small on level $1$, $D(h + s)(x) : E_0 \to F_0$ is Fredholm of index $n - N$. **On every level** (the second statement): for every $m$ there is $\delta > 0$ such that at every $x \in U_{m+1}$ with $|x|_m < \delta$ the level-$m$ operator $Df(x)_m : \mathbb R^n \oplus W_m \to \mathbb R^N \oplus W_m$ is Fredholm of index $\dim P - \dim Q$, for $\widetilde C$ quadrant-like (partial quadrants are); $f(0) = 0$ is not used.

- `Polyfold.proposition_3_10` — Polyfold/Chapter3/BasicGermLinearization.lean, line 381
- `Polyfold.proposition_3_10_scPlus` — Polyfold/Chapter3/BasicGermLinearization.lean, line 325
- `Polyfold.IsSc1GermWith.isScOperator_deriv_zero` — Polyfold/Chapter3/BasicGermLinearization.lean, line 75
- `Polyfold.ScBanach.projWOp` — Polyfold/Chapter3/BasicGermLinearization.lean, line 206
- `Polyfold.ScBanach.scIndex_projWOp` — Polyfold/Chapter3/BasicGermLinearization.lean, line 299
- `Polyfold.proposition_3_10_basic` — Polyfold/Chapter3/FredholmGermLinearization.lean, line 282
- `Polyfold.StabilityData.exists_isFredholm_Dfs'` — Polyfold/Chapter3/SolutionLinearization.lean, line 742
- `Polyfold.proposition_3_10_level` — Polyfold/Chapter3/BasicGermLinearizationLevel.lean, line 236
- `Polyfold.proposition_3_10_full` — Polyfold/Chapter3/BasicGermLinearizationLevel.lean, line 276
- `Polyfold.IsBasicGerm.levelDeriv_add_eq` — Polyfold/Chapter3/BasicGermLinearizationLevel.lean, line 184
- `Polyfold.IsBasicGerm.snd_levelDeriv_add` — Polyfold/Chapter3/BasicGermLinearizationLevel.lean, line 135

*What differs.*
- First statement as in the text, with $s$ only sc$^1$ into $F^1$ and $f$ only sc$^1$. The verification that $Df(0) - T_0$ is sc$^+$ (finite-rank terms through $\mathbb R^n$ and $\mathbb R^N$ with smooth values because $Dh(0)$ is an sc-operator at the smooth point $0$) is not in the text (Findings, Chapter 3, item 46).
- Second statement: on every level $m$, at the points of $U_{m+1}$ small in $E_m$, as in the text, by the text's proof: $Df(x)_m = T_0 + S(x) + K(x)$ with $\|S(x)\| \le \varepsilon$ by Lemma 3.9 on level $m$ (V3.11) and $K(x)$ compact (finite rank, and $\iota\,\mathrm{pr}_W Ds(x)$ through $W_{m+1} \to W_m$). The one identity the text uses silently, the $W$-component of $Df(x)_m$, is proved from the uniqueness of derivatives within $U_1$ (Findings, Chapter 3, item 230). With both statements as in the text under weaker hypotheses ($s$ and $f$ only sc$^1$, $f(0) = 0$ unused) the verdict is “stronger”; formerly narrower, the second statement on level $0$ only (G.21). Updated in the third addendum of this page.

### V3.13. Definition 3.11: sc-Fredholm germs

*restated* · no tameness · $C' = T\psi(0)C$ not imposed

**HWZ (§3.1, Definition 3.11, p. 69).** $(f, x_0)$ is an sc-Fredholm germ if it has a filled version $(g, 0)$ and a local sc$^+$-section $s$ with $s(0) = g(0)$ such that $g - s$ is conjugated to a basic germ: a strong bundle isomorphism $\Psi : U \triangleleft F \to U' \triangleleft F'$ covering an sc-diffeomorphism $\psi$ with $\Psi \circ (g - s) \circ \psi^{-1}$ a basic germ.

**Proved in Lean.** `StrongBundle.IsScFredholmGerm f x₀` (the text’s germ reading): in a strong bundle chart of $P$ centred at $x_0$, a filling $g$ (`IsFillingGerm`, an sc-smooth germ on a germ of neighbourhoods inside $U$, V3.9), a local sc$^+$-section $s$ (`IsScPlusGerm`: $s : E_0 \to F_1$ an sc-smooth germ into $F^1$ on a germ inside $U$) with $\iota s(0) = g(0)$, and `IsConjugateToBasicGerm` for $u \mapsto g(u) - \iota s(u)$: strong bundle maps $\Psi, \Psi'$ inverse to each other (`IsStrongBundleIso`), $\psi(0) = 0$, $U'$ relatively open in $\widetilde C \oplus W$ ($\widetilde C$ a partial quadrant of a finite-dimensional space), a basic germ $h$ on a germ inside $U'$, and $(\Psi(u, g(u) - s(u)))_2 = h(\psi(u))$ for $u \in U$ near $0$.

- `Polyfold.StrongBundle.IsScFredholmGerm` — Polyfold/Chapter3/GermFillingChart.lean, line 192
- `Polyfold.IsFillingGerm` — Polyfold/Chapter3/GermFilling.lean, line 143
- `Polyfold.IsScPlusGerm` — Polyfold/Chapter3/GermFilling.lean, line 159
- `Polyfold.IsConjugateToBasicGerm` — Polyfold/Chapter3/StrongBundleSections.lean, line 537
- `Polyfold.IsStrongBundleIso` — Polyfold/Chapter3/StrongBundleSections.lean, line 523
- `Polyfold.StrongBundle.IsScFredholmGermWholeChart` — Polyfold/Chapter3/StrongBundleSections.lean, line 731
- `Polyfold.StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm` — Polyfold/Chapter3/GermFillingChart.lean, line 204
- `Polyfold.StrongBundle.isScFredholmGerm_iff_germG_wholeChart` — Polyfold/Chapter3/GermFillingChart.lean, line 215
- `Polyfold.IsFillingGerm.nonempty_kerEquiv` — Polyfold/Chapter3/TameGermData.lean, line 91
- `Polyfold.TrivialBundle.not_isFillingGerm_evenBundleChart` — Polyfold/Chapter3/TameGermData.lean, line 416

*What differs.*
- The conjugation identity is required for $u \in U$ near $0$ (Theorem 3.15's identity $(g + \tilde t) - (\tilde t + t_0) = g - t_0$ holds on $U$ only). The text's $C' = T\psi(0)C$ (used in Theorem 3.54) is not part of the data; it is proved (V3.48).
- The index statement after the definition is V3.46 (Proposition 3.52, in the chart).
- The witnesses of the conjugation are also available as a structure, `ConjugationData`, so that the dimensions of the basic germ can be named (V3.46).
- **Germs.** Since the switch to the text’s germ reading (phase 2) the filling and the sc$^+$-section are germs whose levels may shrink with $m$; $\Psi$ is a strong bundle isomorphism on all of $U$, which is no restriction (on a relatively open $U_0 \subseteq U$ it is the same after restricting the chart on level $0$). The project’s earlier notion, with $g$ and $s$ sc-smooth on the whole $U$, is `IsScFredholmGermWholeChart`: it implies the germ reading and is exactly the germ reading with $g$, $s$ sc-smooth on $U$ (`isScFredholmGerm_iff_germG_wholeChart`). Whether the two agree for sections sc-smooth on $X$ is open, and no theorem depends on it (Findings, Chapter 3, items 220–221, 261–264, 330). What remains is the formulation above and the untamed chart (formerly also the stricter germ side, third addendum).
- The existential over charts is essential: a filling in a chart gives a topological isomorphism $\ker Dr(0) \cong \ker\rho(0)$ (`IsFillingGerm.nonempty_kerEquiv`), a condition on the chart, so a filling in one chart gives none in another unless these normal spaces match; a compatible tame chart of the trivial bundle carries no filling of any section (`TrivialBundle.not_isFillingGerm_evenBundleChart`) (Findings, Chapter 3, items 350–352). Added in the fourth addendum of this page.

### V3.14. Theorem 3.12: local compactness for sc-Fredholm germs

*stronger* · only $P \circ f = \mathrm{id}$ used · no tameness

**HWZ (§3.1, Theorem 3.12, p. 70 ("an immediate consequence of Theorem 3.40")).** Let $f$ be an sc-smooth section of the tame strong bundle $P : Y \to X$ and $(f, x_0)$ an sc-Fredholm germ with $f(x_0) = 0$. There are nested open neighbourhoods $O(0) \supset O(1) \supset \cdots$ of $x_0$ in $X_0$ such that $\mathrm{cl}_{X_0}\{x \in O(i) \mid f(x) = 0\}$ is a compact subset of $X_i$.

**Proved in Lean.** For a section $f$ ($P \circ f = \mathrm{id}$) of any strong bundle with $(f, x_0)$ an sc-Fredholm germ and $f(x_0) = 0$: nested open $O(i) \ni x_0$ such that the closure in $X$ of $\{x \in O(i) \mid f(x) = 0\}$ is the image of a compact subset of $X_i$ (level topology) under the inclusion $X_i \to X$.

- `Polyfold.theorem_3_12` — Polyfold/Chapter3/SectionCompactnessG.lean, line 61
- `Polyfold.theorem_3_12_local_subset` — Polyfold/Chapter3/SectionCompactness.lean, line 276
- `Polyfold.IsStrongBundleIso.snd_eq_zero_iff` — Polyfold/Chapter3/SectionCompactness.lean, line 146
- `Polyfold.MPolyfold.continuousOn_levelChartSymm` — Polyfold/Chapter3/SectionCompactness.lean, line 224
- `Polyfold.eq_of_mem_closure_of_continuousOn` — Polyfold/Chapter3/SectionCompactness.lean, line 165

*What differs.*
- Of \"$f$ an sc-smooth section of the tame strong bundle\" only $P \circ f = \mathrm{id}$ is used; regularity enters through the filling germ (germ reading, V3.13); tameness not at all.
- \"Immediate consequence of Theorem 3.40\" hides: the correspondence of zeros through chart, filler and the fibre maps of $\Psi$; the push-forward $t$ of the sc$^+$-section is an sc$^+$-germ with $t(0) = 0$; shrinking so that $E_0$-closures stay inside the chart and the region of the identities; and the continuity of the inverse chart $O_i \to X_i$ for the level topology (Findings, Chapter 3, items 12, 44).

### V3.15. Corollary 3.13: convergence on every level

*restated* · limit $x_0$, or any limit for sections

**HWZ (§3.1, Corollary 3.13, p. 70).** Under the hypotheses of Theorem 3.12, if $f(x_k) = 0$ and $x_k \to x$ in $X_0$, then for every $m$, $x_k \in X_m$ for $k$ large and $x_k \to x$ in $X_m$.

**Proved in Lean.** (a) If $f(x_k) = 0$ and $x_k \to x_0$ (the base point of the germ), then for every $m$ there are lifts $y_k \in X_m$ of the $x_k$, $k$ large, converging in $X_m$ to the lift of $x_0$. (b) For an sc-Fredholm section and any limit $x$ of zeros: $x$ is a zero and a smooth point, and the same conclusion holds at $x$.

- `Polyfold.corollary_3_13` — Polyfold/Chapter3/SectionCompactnessG.lean, line 319
- `Polyfold.corollary_3_13_section` — Polyfold/Chapter3/Chapter5BridgeG.lean, line 61
- `Polyfold.tendsto_of_isCompact_of_tendsto_map` — Polyfold/Chapter3/SectionCompactness.lean, line 177
- `Polyfold.corollary_3_13_local` — Polyfold/Chapter3/LocalCompactness.lean, line 614

*What differs.*
- As stated, the corollary concerns an arbitrary limit $x$ while the hypothesis is about the germ at $x_0$; it is proved for $x = x_0$, and for any limit when $f$ is an sc-Fredholm section, which provides the germ property at $x$ (Findings, Chapter 3, items 15, 45).
- $X_m$ is not known to be first countable here, so convergence is proved by a cluster-point argument in the compact set of Theorem 3.12.

### V3.16. Definition 3.14: sc-Fredholm sections

*as in the book* · tameness not assumed

**HWZ (§3.1, Definition 3.14, p. 70).** A section $f$ of the tame strong bundle $P : Y \to X$ is sc-Fredholm if (1) it is sc-smooth; (2) regularizing: $x \in X_m$, $f(x) \in Y_{m,m+1}$ imply $x \in X_{m+1}$; (3) $(f, x)$ is an sc-Fredholm germ at every smooth point $x$.

**Proved in Lean.** `StrongBundle.IsScFredholmSection f`: (1)–(3) for a section of any strong bundle, clause (3) in the germ reading of V3.13. A zero of a regularizing section is a smooth point.

- `Polyfold.StrongBundle.IsScFredholmSection` — Polyfold/Chapter3/TameGermsG.lean, line 54
- `Polyfold.StrongBundle.IsScFredholmSection.mem_smoothSet_of_isZeroAt` — Polyfold/Chapter3/TameGermsG.lean, line 66
- `Polyfold.StrongBundle.IsScFredholmSectionWholeChart` — Polyfold/Chapter3/StrongBundleSections.lean, line 746
- `Polyfold.StrongBundle.IsScFredholmSectionWholeChart.isScFredholmSection` — Polyfold/Chapter3/TameGermsG.lean, line 60

*What differs.*
- As in the text; the bundle is not required to be tame, which plays no role in the definition (Findings, Chapter 3, item 40).
- **Germs.** Clause (3) is the germ notion of V3.13, the text’s germ reading since the switch (phase 2); the earlier whole-chart notion, stricter, is `IsScFredholmSectionWholeChart` and implies this one (`IsScFredholmSectionWholeChart.isScFredholmSection`). Hence “as in the book” again (“restated” in the third addendum) (Findings, Chapter 3, items 220–221, 330).

### V3.17. Theorem 3.15: stability under sc$^+$-perturbations

*stronger* · no tameness

**HWZ (§3.1, Theorem 3.15, p. 71 (proof pp. 72–73)).** If $P : Y \to X$ is a strong bundle over a tame M-polyfold, $f \in \mathrm{Fred}(P)$ and $s \in \Gamma^+(P)$, then $f + s \in \mathrm{Fred}(P)$.

**Proved in Lean.** For any strong bundle: if $f$ is an sc-Fredholm section and $s$ an sc$^+$-section, the fibrewise sum $f + s$ is an sc-Fredholm section: sc-smooth (sum rule in the charts), regularizing ($Y_{m,m+1}$ is closed under fibrewise subtraction and $s$ takes values in $Y_{m,m+1}$ over $X_m$), and an sc-Fredholm germ at every smooth point (filling germ $g + \tilde t$ on the germ of $g$, sc$^+$-germ $\tilde t + t_0$ on the germ of $t_0$, the same conjugation).

- `Polyfold.theorem_3_15` — Polyfold/Chapter3/FredholmSectionsG.lean, line 204
- `Polyfold.StrongBundle.IsScSmoothSection.sectionAdd` — Polyfold/Chapter3/StrongBundleSections.lean, line 678
- `Polyfold.StrongBundle.regularizing_sectionAdd` — Polyfold/Chapter3/FredholmSectionsG.lean, line 168
- `Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd` — Polyfold/Chapter3/FredholmSectionsG.lean, line 158

*What differs.*
- Tameness is not used (Findings, Chapter 3, item 40).
- The text's \"$f + s$ is an sc-smooth section which is also regularizing\" is two proofs here (Findings, Chapter 3, item 42).
- In the germ reading of Definition 3.11 (V3.13), with the text’s proof: $\tilde t = \hat s \circ r$ is sc-smooth on the whole $U$ because $s$ is a global sc$^+$-section, and a germ plus a whole-chart map is a germ on the same germ (Lemma 3.17 for germs, V3.19); the whole-chart form is `theorem_3_15_wholeChart` (Findings, Chapter 3, item 300). Updated after the switch of Definition 3.11 to the text’s germ reading (phase 2).

### V3.18. Lemma 3.16: the extension $\tilde s = s \circ r$

*restated* · regularity proved where used

**HWZ (§3.1, Lemma 3.16, p. 72).** An sc$^+$-section $s : O \to K$ extends to the sc$^+$-section $\tilde s(u) = s(r(u))$ of $U \triangleleft F \to U$ with (1) $\tilde s = s$ on $O$; (2) $R(r(u), \tilde s(u)) = s(r(u))$.

**Proved in Lean.** For a section $s$ of $K \to O$ ($(x, s(x)) \in K$ on $O$): $s(r(x)) = s(x)$ on $O$, and $\rho(r(u))s(r(u)) = s(r(u))$, $R(r(u), s(r(u))) = (r(u), s(r(u)))$ for $u \in U$. That $s \circ r$ is sc-smooth into $F^1$ is proved inside Theorem 3.15.

- `Polyfold.lemma_3_16` — Polyfold/Chapter3/Filler.lean, line 174
- `Polyfold.StrongBundle.IsScFredholmGerm.sectionAdd` — Polyfold/Chapter3/FredholmSectionsG.lean, line 158

*What differs.*
- (2) is \"$R$ fixes the points of $K$\" and uses that an sc$^+$-section is a section. The sc$^+$ regularity of $\tilde s$ is supplied in the proof of Theorem 3.15, where it is needed (Findings, Chapter 3, item 17).

### V3.19. Lemma 3.17: fillers are stable under sc$^+$-sections

*stronger* · regularity included · $s$ sc-smooth suffices

**HWZ (§3.1, Lemma 3.17, p. 72).** If the sc-smooth section $f : O \to K$ has the filler $g$ and $s : O \to K$ is an sc$^+$-section, then $f + s$ has the filler $g + \tilde s$.

**Proved in Lean.** If $g$ is a filling of $\mathbf f$ (`IsFillingGerm`, V3.7) and $s$ is a section of $K \to O$, then $g + s \circ r$ is a filling of $\mathbf f + s$, with the same derivative family in (3): for $s$ sc-smooth on $U$ on the same germ (`IsFillingGerm.add_section`), and for $s$ an sc-smooth germ on $G \cap r^{-1}(G_s)$ (`IsFillingGerm.add_section_germ`); (3) because $[1 - \rho(r(y))](g + s \circ r)(y) = [1 - \rho(r(y))]g(y)$. For whole-chart fillers (`IsFillerOf`, no regularity of $g$) and any section $s$: `lemma_3_17`.

- `Polyfold.IsFillingGerm.add_section_germ` — Polyfold/Chapter3/GermCalculus.lean, line 706
- `Polyfold.IsFillingGerm.add_section` — Polyfold/Chapter3/GermCalculus.lean, line 677
- `Polyfold.lemma_3_17` — Polyfold/Chapter3/Filler.lean, line 189
- `Polyfold.IsFillerOf.congr_left` — Polyfold/Chapter3/StrongBundleSections.lean, line 561

*What differs.*
- The regularity of $g + \tilde s$ (“follow immediately”) is part of the conclusion: $s \circ r$ is a germ by the chain rule with the whole-chart $r$, and a sum of germs is a germ on the intersection (Findings, Chapter 3, items 270, 271, 273). Of $s$ only the sc-smoothness is used, not that it is sc$^+$.
- **Germs.** Since the switch to the text’s germ reading (phase 2) the lemma is the text’s, for fillings that are germs, and proved in the project; the round-trip audit had found it true outside the project. The whole-chart `lemma_3_17` (fillers in the sense of `IsFillerOf`, the regularity left to Theorem 3.15) neither implies it nor follows from it (round-trip item V3.19; Findings, Chapter 3, items 220–221, 273). Hence “stronger” (formerly “restated”).

### V3.20. Definition 3.21: good position

*stronger* · algebraic complement suffices · the text's sc-complement form too

**HWZ (§3.1, Definition 3.21, pp. 76–77).** A finite-dimensional sc-subspace $N \subseteq E$ is in good position to the partial quadrant $C$ if $N \cap C$ has nonempty interior in $N$ and $N$ has an sc-complement $P$ (a good complement) with: for some $\varepsilon > 0$, $|p|_0 \le \varepsilon|n|_0$ implies ($n \in C \iff n + p \in C$). A merely topological complement is allowed for non-smooth $N$.

**Proved in Lean.** `IsGoodComplement E C N P`: $E_0 = N \oplus P$ algebraically and the $\varepsilon$-condition; `IsInGoodPosition E C N`: $N \cap C$ has nonempty interior in $N$ and $N$ has a good complement. $N$ finite-dimensional is a separate instance argument. Definition 3.21 as written: `IsScGoodComplement` ($E = N \oplus P$ an sc-splitting, with the constant $\varepsilon$) and `IsInGoodPositionSc`; each implies the project's form. On a partial quadrant a smooth finite-dimensional $N$ in good position (algebraic complement) is in good position with an sc-complement, also inside any sc-subspace $T \supseteq N$; for smooth $N$ the text's good complements are the project's closed ones, and Definition 3.21 as written is the project's good position together with $N \subseteq E_\infty$.

- `Polyfold.IsGoodComplement` — Polyfold/Chapter3/GoodPosition.lean, line 615
- `Polyfold.IsInGoodPosition` — Polyfold/Chapter3/GoodPosition.lean, line 622
- `Polyfold.IsScGoodComplement` — Polyfold/Chapter3/GoodPositionSc.lean, line 116
- `Polyfold.IsInGoodPositionSc` — Polyfold/Chapter3/GoodPositionSc.lean, line 123
- `Polyfold.IsInGoodPositionSc.toIsInGoodPosition` — Polyfold/Chapter3/GoodPositionSc.lean, line 150
- `Polyfold.IsGoodComplement.isScGoodComplementIn` — Polyfold/Chapter3/GoodPositionSc.lean, line 257
- `Polyfold.IsInGoodPosition.isInGoodPositionSc` — Polyfold/Chapter3/GoodPositionSc.lean, line 349
- `Polyfold.isScGoodComplement_iff` — Polyfold/Chapter3/GoodPositionSc.lean, line 331
- `Polyfold.isInGoodPositionSc_iff` — Polyfold/Chapter3/GoodPositionSc.lean, line 356

*What differs.*
- Only the algebraic splitting is required: neither the sc-structure nor the closedness of $P$ enters Proposition 3.22, Lemmas 3.45, 3.65 or Proposition 3.69 (Findings, Chapter 3, item 19). Where closedness is needed (Lemma 3.55, Definition 3.25) it is added there.
- Typo p. 77: \"finite dimensional sunspace\" *(book 2017: corrected, p. 69)*.
- As a *conclusion* the algebraic form is weaker than the text's: an algebraic good complement need not be closed (round-trip item V3.20: $C = E_0$ infinite-dimensional, $P$ the kernel of a discontinuous functional; not in the project). The text's definition is therefore formalized as well, and on a partial quadrant the two agree for smooth $N$: a closed good complement of a smooth $N$ is an sc-complement (the projection along $N$ acts on every level), and a closed good complement always exists there (Findings, Chapter 3, items 210, 211). The theorems that conclude good position are given in the sc form in V3.94, V3.95. Updated in the third addendum of this page.

### V3.21. Proposition 3.22: $N \cap C$ is a partial quadrant

*as in the book* · no extreme-ray lemmas

**HWZ (§3.1, Proposition 3.22, p. 77 (proof §3.8.1, pp. 120–126)).** If the finite-dimensional sc-subspace $N$ is in good position to the partial quadrant $C$, then $N \cap C$ is a partial quadrant in $N$.

**Proved in Lean.** For $N$ finite-dimensional in good position to the partial quadrant $C$: $N \cap C$ is a partial quadrant in $N$ (constant sc-structure). The core: for continuous functionals $\ell_1, \dots, \ell_n$ jointly onto $\mathbb R^n$ with $C = \{\ell_i \ge 0\}$, a linear isomorphism $e : N \to \mathbb R^k \times N_0$ with $N \cap C = e^{-1}([0, \infty)^k \times N_0)$, $k = \dim N - \dim(N \cap W)$.

- `Polyfold.proposition_3_22` — Polyfold/Chapter3/GoodPosition.lean, line 682
- `Polyfold.exists_quadrantNormalForm` — Polyfold/Chapter3/GoodPosition.lean, line 556
- `Polyfold.QuadrantNormalForm` — Polyfold/Chapter3/GoodPosition.lean, line 305
- `Polyfold.mem_quadCone_of_vanIdx` — Polyfold/Chapter3/GoodPosition.lean, line 199
- `Polyfold.sigmaCoord_surjective` — Polyfold/Chapter3/GoodPosition.lean, line 161

*What differs.*
- The statement is the text's. The proof keeps the text's case distinction but replaces Lemmas 3.62–3.64 (Krein–Milman for cones, extreme-ray counts, cited from [21]) and 3.66–3.68 by a segment argument and the surjectivity of $Q : N \to \mathbb R^\Sigma$ from Lemma 3.65; the case $N \cap C = N$ is treated separately (Findings, Chapter 3, item 18).

### V3.22. Definition 3.25: the $n$-dimensional tangent germ property

*narrower* · added: $Y$ closed · sc$^\infty$ with $k$-dependent sets

**HWZ (§3.2, Definition 3.25, p. 79).** $M \subseteq X$ (tame) has the $n$-dimensional tangent germ property if $M \subseteq X_\infty$ and every $x \in M$ has a chart $\varphi : (U, x) \to (O, 0)$ onto a tame retract $(O, C, E)$, an $n$-dimensional smooth $N \subseteq E$ in good position to $C$ with good complement $Y$, $E = N \oplus Y$, a relatively open $V \ni 0$ in $N \cap C$ and a continuous $\delta : V \to Y$ with (i) $\varphi(M \cap U) = \{v + \delta(v)\}$, (ii) $\delta : \mathcal O(N \cap C, 0) \to (Y, 0)$ an sc$^\infty$-germ, $\delta(0) = 0$, $D\delta(0) = 0$.

**Proved in Lean.** `MPolyfold.TangentGermChart M x n`: the data of (2), with $Y$ **closed**, and (ii) read as `IsScInftyGermAt`: for every $m$ and $k$ a relatively open $V_{m,k} \ni 0$ in $N \cap C$ with $\delta(V_{m,k}) \subseteq E_m$ and $\delta : V_{m,k} \to E_m$ of class $C^k$. `MPolyfold.HasTangentGermProperty M n`: $M \subseteq X_\infty$ and the data at every point. Both other readings of \"sc$^\infty$-germ\" (one fixed germ; sc-smooth on $V$) imply this one.

- `Polyfold.MPolyfold.TangentGermChart` — Polyfold/Chapter3/TangentGerm.lean, line 226
- `Polyfold.MPolyfold.HasTangentGermProperty` — Polyfold/Chapter3/TangentGerm.lean, line 258
- `Polyfold.IsScInftyGermAt` — Polyfold/Chapter3/TangentGerm.lean, line 118
- `Polyfold.IsScSmoothGerm.isScInftyGermAt` — Polyfold/Chapter3/TangentGerm.lean, line 125
- `Polyfold.IsScSmooth.isScInftyGermAt` — Polyfold/Chapter3/TangentGerm.lean, line 138
- `Polyfold.MPolyfold.TangentGermChart.π` — Polyfold/Chapter3/TangentGerm.lean, line 286

*What differs.*
- **Added hypothesis: the good complement $Y$ is closed**, needed for the projection $\pi : E \to N$ along $Y$ to be continuous (Findings, Chapter 3, item 81); the text's sc-complement is closed.
- \"sc$^\infty$-germ\" is read with $k$-dependent neighbourhoods, the reading in which Theorem 3.43 (1) is proved (V3.38) and the weakest of the three (Findings, Chapter 3, item 80); Corollary 3.34 now also holds on one germ (V3.31, third addendum).

### V3.23. Proposition 3.26: invariance of the tangent germ property

*as in the book* · tameness of $X$ not needed

**HWZ (§3.2, Proposition 3.26, p. 80).** For a pair $(X, M)$ with $X$ a tame M-polyfold, and an sc-diffeomorphism $\psi : X \to X'$ with $\psi(M) = M'$: $M'$ has the $n$-dimensional tangent germ property iff $M$ has it.

**Proved in Lean.** For an sc-diffeomorphism $\psi : X \to X'$ of M-polyfolds with inverse $\psi'$ (sc-smooth both ways on all of $X$, $X'$) and $\psi(M) = M'$: $M'$ has the $n$-dimensional tangent germ property iff $M$ has it. The data at $\psi(x)$ are the transported chart $\varphi \circ \psi^{-1}$ with the same $N$, $Y$, $V$, $\delta$; $\psi(M) \subseteq X'_\infty$ because sc-smooth maps preserve the levels.

- `Polyfold.proposition_3_26` — Polyfold/Chapter3/TangentGerm.lean, line 843
- `Polyfold.proposition_3_26_image` — Polyfold/Chapter3/TangentGerm.lean, line 825
- `Polyfold.MPolyfold.TangentGermChart.transport` — Polyfold/Chapter3/TangentGerm.lean, line 773

*What differs.*
- As in the text, for Definition 3.25 as formalized (V3.22, $Y$ closed); the tameness of $X$ is not used (the chart models are tame retracts as part of the data).
- The text's first sentence, that $X' = \psi(X)$ is tame, is not needed here; that tameness is carried by sc-diffeomorphisms is V3.71.

### V3.24. Theorem 3.27: subsets with the tangent germ property are sub-M-polyfolds

*narrower* · added: $\delta$ sc-smooth on $V$ · added: $\pi(O) \subseteq C$ · two counterexamples

**HWZ (§3.2, Theorem 3.27, p. 81 (proof pp. 81–84)).** If $X$ is a tame M-polyfold and $M \subseteq X$ has the $n$-dimensional tangent germ property, then (1) $M$ is a sub-M-polyfold whose induced structure is tame and sc-smoothly equivalent to a smooth manifold with boundary with corners; (2) with the data of Definition 3.25, $y \mapsto \pi \circ \varphi(y)$ is a smooth chart of $M$ around $x$.

**Proved in Lean.** Let $M \ne \emptyset$ have at every point data of Definition 3.25 satisfying `IsRegular`: (a) $\delta$ is sc-smooth on $V$ (set sense), (b) $\pi(O) \subseteq C$. Then $M$ is a sub-M-polyfold (retraction $s = \varphi^{-1} \circ t \circ \varphi$, $t(v + w) = v + \delta(v)$); its induced structure is tame and has an equivalent atlas of $n$-dimensional corner charts; every $y \mapsto \pi\varphi(y)$ is a chart of the induced structure, modelled on $(V, N \cap C, N)$; and $d_M(y) = d_{N \cap C}(\pi\varphi(y))$.

- `Polyfold.theorem_3_27` — Polyfold/Chapter3/TangentGerm.lean, line 728
- `Polyfold.theorem_3_27_isSubMPolyfold` — Polyfold/Chapter3/TangentGerm.lean, line 450
- `Polyfold.MPolyfold.TangentGermChart.IsRegular` — Polyfold/Chapter3/TangentGerm.lean, line 324
- `Polyfold.MPolyfold.TangentGermChart.chart` — Polyfold/Chapter3/TangentGerm.lean, line 499
- `Polyfold.MPolyfold.theorem_3_27_isChart` — Polyfold/Chapter3/TangentGerm.lean, line 649
- `Polyfold.MPolyfold.theorem_3_27_isTame` — Polyfold/Chapter3/TangentGerm.lean, line 690
- `Polyfold.MPolyfold.theorem_3_27_isManifoldWithCorners` — Polyfold/Chapter3/TangentGerm.lean, line 699
- `Polyfold.MPolyfold.IsManifoldWithCorners` — Polyfold/Chapter3/TangentGerm.lean, line 467
- `Polyfold.MPolyfold.theorem_3_27_degIndex` — Polyfold/Chapter3/TangentGerm.lean, line 711
- `Polyfold.isScSmooth_subtype_val` — Polyfold/Chapter3/TangentGerm.lean, line 195

*What differs.*
- **Two added hypotheses (`IsRegular`), each with a counterexample to the text's step.** (a) \"$\delta$ is an sc$^\infty$-germ near every $v_0 \in V$\" needs $\delta$ differentiable at $v_0$: a smooth curve in $\mathbb R^2$ with a vertical tangent at $(2, 4)$, written over the $x$-axis, satisfies Definition 3.25 at $0$ with $\delta$ not differentiable at $2$, and the chart $\pi\varphi$ is then not smoothly compatible (Findings, Chapter 3, item 82). (b) \"$\Sigma = \{v + y \in C\}$ is relatively open in $C$\" is false for $C = [0, \infty)^3$, $N = \mathbb R(1, 1, 1)$, $Y = \{x + y - z = 0\}$ (item 83).
- Tameness of $X$ is not used (only that the chart models are tame retracts). \"Manifold with boundary with corners\" (Chapter 4) is `IsManifoldWithCorners`: an equivalent atlas of charts on relatively open subsets of $n$-dimensional partial quadrants. The relation $d_{N \cap C}(v) = d_X(y)$ via Lemma 3.70 is proved in the model $\mathbb R^n \oplus W$ only (item 84).
- For the solution set of an sc-Fredholm section both conditions are theorems: (a) by re-centring (V3.73, V3.74), (b) by the choice of the good complement (V3.75, V3.77); read off the statement of V3.74, (a) follows from (b) after shrinking the data for any set with the tangent germ property. With a dimension that may vary from point to point: V3.72.

### V3.25. Definition 3.28: sc$^0$-contraction germs and their working form

*restated* · explicit regions for the induction · any convex $\widetilde C$

**HWZ (§3.3, Definition 3.28, p. 85).** An sc$^0$-germ $f : \mathcal O(\widetilde C \oplus W, 0) \to (W, 0)$ is an sc$^0$-contraction germ if $f(a, w) = w - B(a, w)$ and for every $\varepsilon > 0$, $m \ge 0$, $|B(a, w) - B(a, w')|_m \le \varepsilon|w - w'|_m$ for $(a, w), (a, w')$ on level $m$ sufficiently close to $(0, 0)$.

**Proved in Lean.** `IsSc0ContractionGerm C̃ G B`: $B$ an sc$^0$-germ on $G$, $B(0, 0) = 0$, and for every $\varepsilon$, $m$ an $r > 0$ with the estimate for $a \in \widetilde C$, $|a| < r$, $|w|_m, |w'|_m < r$, these points lying in $U_m$. The working form `ContractionGerm`: the same data with explicit regions $N(m) \subseteq P$ open, $K(m) \subseteq O(m) \subseteq W_m$ ($K$ closed, $O$ open) on which $B_m(a, \cdot)$ is a $\tfrac12$-contraction ($O$) mapping $K$ into itself; every contraction germ has one.

- `Polyfold.IsSc0ContractionGerm` — Polyfold/Chapter3/ContractionGerm.lean, line 143
- `Polyfold.ContractionGerm` — Polyfold/Chapter3/ContractionGerm.lean, line 158
- `Polyfold.IsSc0ContractionGerm.toContractionGerm` — Polyfold/Chapter3/GermIFT.lean, line 623
- `Polyfold.contractionMap` — Polyfold/Chapter3/ContractionGerm.lean, line 151

*What differs.*
- The balls of the definition cannot express the regions of $f^{(1)}$ in Lemma 3.31, which are unbounded in the tangent directions; the working form carries explicit regions (Findings, Chapter 3, items 3, 7).
- §3.3 is proved for any convex $\widetilde C \ni 0$ with nonempty interior in a finite-dimensional $P$ (item 9).

### V3.26. Theorem 3.29: existence of the solution germ

*hypotheses explicit* · uniqueness region explicit

**HWZ (§3.3, Theorem 3.29, p. 86).** An sc$^0$-contraction germ $f : \mathcal O(\widetilde C \oplus W, 0) \to (W, 0)$ admits a uniquely determined sc$^0$-solution germ $\delta : \mathcal O(\widetilde C, 0) \to (W, 0)$ with $f(a, \delta(a)) = 0$; proof by \"the parametrized version of Banach's fixed point theorem\".

**Proved in Lean.** In the working form, $\delta$ (the level-$0$ fixed point) is an sc$^0$-germ on $V_m = N(m) \cap \widetilde C$ with $\delta(0) = 0$, $(a, \delta_m(a)) \in U_m$ and $B(a, \delta(a)) = \delta(a)$, and every solution $w \in O(0)$ of $w = B(a, w)$, $a \in V_0$, equals $\delta(a)$. From Definition 3.28 directly: the same with uniqueness in a ball. The parametrized fixed point theorem: the fixed point of a family of $\tfrac12$-contractions of a closed set, continuous in the parameter pointwise, is continuous in the parameter.

- `Polyfold.theorem_3_29` — Polyfold/Chapter3/ContractionGerm.lean, line 352
- `Polyfold.theorem_3_29_of_isSc0ContractionGerm` — Polyfold/Chapter3/GermIFT.lean, line 681
- `Polyfold.ContractionGerm.sol` — Polyfold/Chapter3/ContractionGerm.lean, line 267
- `Polyfold.ContractionGerm.incl_fixLvl` — Polyfold/Chapter3/ContractionGerm.lean, line 245
- `Polyfold.ContractionGerm.eq_sol` — Polyfold/Chapter3/ContractionGerm.lean, line 291
- `Polyfold.exists_fixedPoint_continuousOn` — Polyfold/Chapter3/LocalCompactness.lean, line 90

*What differs.*
- \"Uniquely determined\" holds in the contraction region $O(0)$ (the text's Remark 3.36: $|w|_0 \le \tau_0$).
- The parametrized Banach fixed point theorem, which the text invokes without statement, is proved (Mathlib has the theorem without the parameter). Typo p. 85: \"$\delta_1 : V_1 \to W_1$ satisfying $\delta(0) = 0$\" for $\delta_1(0) = 0$ *(book 2017: unchanged, p. 77)*.

### V3.27. Theorem 3.30: the solution germ is sc$^1$

*restated* · sc¹ on the germ shifted by one level · proof supplied

**HWZ (§3.3, Theorem 3.30, p. 86 (cited from [21, Theorem 2.3], no proof)).** If the sc$^0$-contraction germ $f : \mathcal O(\widetilde C \oplus W, 0) \to (W, 0)$ is of class sc$^1$, its solution germ $\delta$ is of class sc$^1$.

**Proved in Lean.** If $B$ is an sc$^1$-germ, then $\delta$ is a solution germ and an sc$^1$-germ **on the re-indexed germ** $V_m = N(m+1) \cap \widetilde C$, with derivative $D\delta(a) = (1 - D_2B(a, \delta(a)))^{-1}D_1B(a, \delta(a))$.

- `Polyfold.theorem_3_30` — Polyfold/Chapter3/ContractionGerm.lean, line 761
- `Polyfold.ContractionGerm.isSc1GermWith_sol` — Polyfold/Chapter3/ContractionGerm.lean, line 734
- `Polyfold.ContractionGerm.hasFDerivWithinAt_sol` — Polyfold/Chapter3/ContractionGerm.lean, line 558
- `Polyfold.ContractionGerm.Aop` — Polyfold/Chapter3/ContractionGerm.lean, line 483
- `Polyfold.ContractionGerm.Lop_Aop` — Polyfold/Chapter3/ContractionGerm.lean, line 514
- `Polyfold.ContractionGerm.continuousOn_Aop` — Polyfold/Chapter3/ContractionGerm.lean, line 686

*What differs.*
- The text gives no proof. The formal proof needs $(a_0, \delta(a_0)) \in U_2$ (level-$1$ operators, so that the increment $A h$ lies in $W_1$), hence holds on the germ shifted by one level; legitimate as a germ only because $\widetilde C$ is finite-dimensional (Findings, Chapter 3, item 1). In the text's \"up to shrinking\" reading this is \"$\delta$ is sc$^1$\".

### V3.28. Lemma 3.31: the contraction germ $f^{(1)}$

*restated* · regions unbounded in tangent directions · Definition 3.28 for $f^{(1)}$ proved

**HWZ (§3.3, Lemma 3.31, pp. 86–87).** If $f = w - B(a, w)$ is an sc$^0$-contraction germ of class sc$^k$, $k \ge 1$, with solution germ $\delta$ of class sc$^j$, then $f^{(1)}(v, b, u, w) = (u - B(v, u), w - DB(v, \delta(v))(b, w))$ is an sc$^0$-contraction germ of class sc$^{\min(k-1, j)}$ with solution germ $T\delta$ (\"from the uniqueness\").

**Proved in Lean.** If $B$ is sc$^{k+1}$ and $\delta$ is sc$^j$ on $\mathrm{germ}(s) = (N(m+s) \cap \widetilde C)_m$, then $f^{(1)}$, in working form with parameter space $P \times P \supseteq \widetilde C \times P$, fibre $TW$ and regions $N(m+2+s) \times P$, $O(m+1) \times W_m$, $K(m+1) \times W_m$, is a contraction germ of class sc$^{\min(k, j)}$ whose solution germ is $T\delta(v, b) = (\delta(v), D\delta(v)b)$ on $(N(2+s) \cap \widetilde C) \times P$. Its map is $(\mathrm{pr}_1 \circ TB \circ \sigma, \mathrm{pr}_2 \circ TB \circ \Gamma)$ with $\sigma$ a reshuffle and $\Gamma(v, b, u, w) = ((v, \delta(v)), (b, w))$. If the working form also satisfies Definition 3.28 (as the one built from an sc$^0$-contraction germ does) and $B$ is sc$^1$, then $f^{(1)}$ is an sc$^0$-contraction germ in the sense of Definition 3.28 on its germ, for every $s$: an $\varepsilon$-contraction near $0$ for every $\varepsilon > 0$ on every level.

- `Polyfold.ContractionGerm.lemma_3_31` — Polyfold/Chapter3/GermIFT.lean, line 400
- `Polyfold.ContractionGerm.next` — Polyfold/Chapter3/GermIFT.lean, line 323
- `Polyfold.ContractionGerm.nextB` — Polyfold/Chapter3/GermIFT.lean, line 209
- `Polyfold.ContractionGerm.nextB_isSckGerm` — Polyfold/Chapter3/GermIFT.lean, line 276
- `Polyfold.ContractionGerm.next_sol` — Polyfold/Chapter3/GermIFT.lean, line 374
- `Polyfold.tangentShuffle` — Polyfold/Chapter3/GermIFT.lean, line 93
- `Polyfold.ContractionGerm.isSc0ContractionGerm_next` — Polyfold/Chapter3/GermIFTSmooth.lean, line 357

*What differs.*
- Uniqueness holds only in the contraction region, which must contain $T\delta(v, b)$ for every $b$: the regions are unbounded in $b$, $w$ (Findings, Chapter 3, item 3). \"As one verifies by comparing $Tf$ with $f^{(1)}$\" is the chain rule for germs with the shifted solution germ $v \mapsto \delta(v) \in W_1$ (Proposition 1.17 for germs, item 4). The parameter region $N(2+s)$ comes from $D\delta(v)$ needing $v \in N(2)$.
- The text's “$f^{(1)}$ is an sc$^0$-contraction germ” in the sense of Definition 3.28 is proved separately (`isSc0ContractionGerm_next`): on level $m$ its first component is Definition 3.28 for $B$ on level $m + 1$, its second needs Lemma 3.9 on level $m$ with any $\varepsilon$ (V3.11). The working form records only a $\tfrac12$-contraction on the explicit regions, which is all the proof of Theorem 3.33 uses (Findings, Chapter 3, item 252). Updated in the third addendum of this page.

### V3.29. Lemma 3.32: the iterated contraction germs

*restated* · no iterated germs $f^{(j)}$

**HWZ (§3.3, Lemma 3.32, p. 87).** Given an sc$^0$-contraction germ $f$ of class sc$^k$ and a solution germ $\delta$ of class sc$^j$, $j \le k$, there is an sc$^0$-contraction germ $f^{(j)}$ of class sc$^{\min(k-j, 1)}$ with solution germ $T^j\delta$.

**Proved in Lean.** As one induction over all contraction germs (any finite-dimensional parameter space): if $B$ is sc$^k$ and $j \le k$, the solution germ $\delta$ is an sc$^j$-germ on $\mathrm{germ}(s)$ for some $s$. The step $j \to j+1$: $\delta$ sc$^j$, so $f^{(1)}$ is sc$^j$, so $T\delta$ is sc$^j$ (the induction hypothesis for $f^{(1)}$), and $\delta$ is sc$^1$ (Theorem 3.30); then $\delta$ is sc$^{j+1}$ on $\mathrm{germ}(s + s' + 1)$.

- `Polyfold.ContractionGerm.sol_isSckGerm` — Polyfold/Chapter3/GermIFT.lean, line 456
- `Polyfold.ContractionGerm.isSckGerm_succ_of_next` — Polyfold/Chapter3/GermIFT.lean, line 419

*What differs.*
- The iterated germs $f^{(j)}$ are not constructed; the content of the lemma (its step $j \to j+1$) is the induction step (Findings, Chapter 3, item 5).

### V3.30. Theorem 3.33: the germ implicit function theorem

*restated* · the text's hypotheses · sc^k on a germ shrunk by $2^k - 1$

**HWZ (§3.3, Theorem 3.33, p. 88).** If $f : \mathcal O(\widetilde C \oplus W, 0) \to (W, 0)$ is an sc$^0$-contraction germ of class sc$^k$, its solution germ $\delta$, $f(v, \delta(v)) = 0$, is of class sc$^k$.

**Proved in Lean.** If $B$ is an sc$^k$-germ, there is $s$ such that $\delta$ is a solution germ and an sc$^k$-germ **on the shrunken germ** $\mathrm{germ}(s) = (N(m+s) \cap \widetilde C)_m$; the proof gives $s = 2^k - 1$. The same from Definition 3.28 with balls.

- `Polyfold.theorem_3_33` — Polyfold/Chapter3/GermIFT.lean, line 482
- `Polyfold.theorem_3_33_smooth` — Polyfold/Chapter3/GermIFT.lean, line 490
- `Polyfold.theorem_3_33_of_isSc0ContractionGerm` — Polyfold/Chapter3/GermIFT.lean, line 703

*What differs.*
- **Proved with the text's hypotheses.** The germ shrinks with $k$: each induction step uses the previous stage twice, so $s_{j+1} = 2s_j + 1$ (Findings, Chapter 3, item 2). In the text's reading, where germs are up to shrinking, this is the theorem; with a germ as a fixed sequence of sets the conclusion holds on $\mathrm{germ}(2^k - 1)$, not on the germ of construction.
- The statement keeps \"there is $s$\"; $s = 2^k - 1$ is read off the proof. Whether the shrinking is intrinsic is not decided: in the toy model of the exposition the solution germ is sc-smooth on the original germ.

### V3.31. Corollary 3.34: $C^k$ on $k$-dependent neighbourhoods

*as in the book* · $V_{m,k}$ depends on $k$, as stated · sc-smooth on one germ

**HWZ (§3.3, Corollary 3.34, p. 88).** If the sc$^0$-contraction germ $f$ is sc-smooth, then for all $m, k \ge 0$ there is a relatively open $V_{m,k} \ni 0$ in $\widetilde C$ with (1) $\delta(V_{m,k}) \subseteq W_m$, (2) $\delta : V_{m,k} \to W_m$ of class $C^k$. In particular $\delta$ is sc-smooth at the smooth point $0$.

**Proved in Lean.** If $B$ is an sc-smooth germ, then for every $m$ and $k$ there is a relatively open $V \ni 0$ in $\widetilde C$ (namely $N(m+k+s) \cap \widetilde C$) with $\delta(V) \subseteq W_m$ and the level-$m$ map of $\delta$ of class $C^k$ on $V$. The last sentence on one germ: the solution germ is an sc-smooth germ (sc$^k$ for every $k$ on the same sequence of sets) on a diagonal germ $V_m = N(m + t_m) \cap \widetilde C$, $t_m = \sum_{j \le m} s_j$, and a solution germ there.

- `Polyfold.corollary_3_34` — Polyfold/Chapter3/GermIFT.lean, line 505
- `Polyfold.IsSckGerm.contDiffOn_levels` — Polyfold/Chapter3/GermLevels.lean, line 398
- `Polyfold.corollary_3_34_isScSmoothGerm` — Polyfold/Chapter3/GermIFTSmooth.lean, line 208
- `Polyfold.isSckGerm_of_levels` — Polyfold/Chapter3/GermIFTSmooth.lean, line 113

*What differs.*
- As in the text, with $V_{m,k}$ depending on $k$. The last sentence holds on one germ: sc$^j$ involves only the levels $\ge j$ of a germ (`isSckGerm_of_levels`), so the $k$-dependent germs $\mathrm{germ}(s_k)$ of Theorem 3.33 can be replaced by one diagonal germ, which shrinks fast with the level ($t_m = 2^{m+1} - m - 2$ for $s_k = 2^k - 1$) but is a germ of neighbourhoods (Findings, Chapter 3, item 250; formerly “in this sense only”, updated in the third addendum of this page). The citation \"Proposition 3.40\" should be Theorem 3.40, and it is not needed *(book 2017: unchanged, renumbered: "Proposition 3.11" for Theorem 3.11, p. 79)* (Findings, Chapter 3, item 8).

### V3.32. Theorem 3.35: the germ implicit function theorem on a partial quadrant

*restated* · sc-smooth on one germ · hypotheses on $f$, any representative · on a smaller germ $V' \subseteq V$

**HWZ (§3.3, Theorem 3.35, p. 89).** Let $\widetilde C$ be a finite-dimensional partial quadrant in $\mathbb R^n$. An sc$^0$-contraction germ of class sc$^k$ has a solution germ of class sc$^k$; if $f$ is sc-smooth so is its solution germ.

**Proved in Lean.** For $\widetilde C$ a partial quadrant in a finite-dimensional $P$: if $B$ is sc$^k$ there is $s$ with $\delta$ sc$^k$ on $\mathrm{germ}(s)$; if $B$ is sc-smooth, $\delta$ is an sc-smooth germ (sc$^k$ for every $k$) on **one** germ $N(m + t_m) \cap \widetilde C$ (earlier form: for every $k$ an $s$ with $\delta$ sc$^k$ on $\mathrm{germ}(s)$). In the text's form: for an sc$^0$-contraction germ $f = w - B(a, w)$ of Definition 3.28 on a quadrant-like $\widetilde C$ and **any** representative $(V, \delta)$ of its solution germ ($\delta$ sc$^0$, $\delta(0) = 0$, $f(a, \delta(a)) = 0$ on $V_0$): if $f$ is sc$^k$, $\delta$ is sc$^k$ on a germ $V' \subseteq V$; if $f$ is sc-smooth, $\delta$ is an sc-smooth germ on one germ $V' \subseteq V$.

- `Polyfold.theorem_3_35` — Polyfold/Chapter3/GermIFT.lean, line 519
- `Polyfold.theorem_3_35_smooth` — Polyfold/Chapter3/GermIFT.lean, line 528
- `Polyfold.theorem_3_35_isScSmoothGerm` — Polyfold/Chapter3/GermIFTSmooth.lean, line 220
- `Polyfold.theorem_3_35_of_isSc0ContractionGerm` — Polyfold/Chapter3/GermIFTSmooth.lean, line 303
- `Polyfold.isSckGerm_contractionMap_iff` — Polyfold/Chapter3/GermIFTSmooth.lean, line 239

*What differs.*
- The last sentence is proved as `IsScSmoothGerm` on one germ (the diagonal germ of V3.31); before the third addendum of this page only for every $k$ on a germ depending on $k$ (Findings, Chapter 3, items 2, 250).
- In the text's form the hypotheses are on $f$ ($f$ is sc$^k$ iff $B$ is, `isSckGerm_contractionMap_iff`) and any representative of the solution germ is allowed (it agrees with the constructed one near $0$, by the uniqueness of Theorem 3.29); the conclusion holds on a smaller germ $V' \subseteq V$, as for Theorem 3.33 (V3.30), and $\mathbb R^n$ is generalized to a quadrant-like $\widetilde C$ in a finite-dimensional $P$ (Findings, Chapter 3, item 251). Updated in the third addendum of this page.

### V3.33. Definition 3.37: the basic class

*as in the book*

**HWZ (§3.4, Definition 3.37, p. 90).** A basic germ $f : \mathcal O([0, \infty)^k \oplus \mathbb R^{n-k} \oplus W, 0) \to (\mathbb R^N \oplus W, 0)$ is an sc-smooth germ such that $P_W \circ f$ is an sc$^0$-contraction germ; $\mathfrak C_{\mathrm{basic}}$ is the class of basic germs.

**Proved in Lean.** Definition 3.7 restated: `IsBasicGerm` (V3.10).

- `Polyfold.IsBasicGerm` — Polyfold/Chapter3/LocalCompactness.lean, line 139

*What differs.*
- Same notion as Definition 3.7.

### V3.34. Theorem 3.38: weak stability of basic germs

*restated* · linear coordinate change · $W$-component of $s$ only

**HWZ (§3.4, Theorem 3.38, p. 90 (proof pp. 90–93)).** For a basic germ $f$ and the principal part $s$ of an sc$^+$-section with $s(0) = 0$ there is a strong bundle isomorphism $\Phi : U \triangleleft (\mathbb R^N \oplus W) \to U' \triangleleft (\mathbb R^{N'} \oplus W')$ covering an sc-diffeomorphism $\varphi$ such that $(\Phi_*(f + s))^1$ (levels raised by one) is a basic germ; $n - N = n' - N'$.

**Proved in Lean.** Given $f$ basic with contraction $B$ and the data `StabilityData` (the $W$-component $s$ of the sc$^+$-germ, $s(0) = 0$, and an sc-Fredholm splitting $W = C \oplus X = R \oplus Z$ of $1 + D_2s(0)$, which exists by Proposition 1.10): with the **linear** base change $\psi(a, w) = ((a, (1 - P_1)w), P_1w)$ and fibre change $\Psi(q, w) = ((q, (1 - P_2)w), L^{-1}P_2w)$, the germ $(\Phi_*(f + s))^1 = \Psi \circ (f + s)^1 \circ \psi^{-1}$ on $\psi(U_{m+1})$ is a basic germ with contraction $\hat B = L^{-1}P_2(B - S)$; zeros correspond under $\psi$; and $\dim C = \dim Z$.

- `Polyfold.theorem_3_38` — Polyfold/Chapter3/BasicClass.lean, line 1035
- `Polyfold.StabilityData` — Polyfold/Chapter3/BasicClass.lean, line 416
- `Polyfold.StabilityData.exists_of_scPlus` — Polyfold/Chapter3/BasicClass.lean, line 1264
- `Polyfold.StabilityData.split` — Polyfold/Chapter3/BasicClass.lean, line 647
- `Polyfold.StabilityData.fiber` — Polyfold/Chapter3/BasicClass.lean, line 678
- `Polyfold.StabilityData.pushMap` — Polyfold/Chapter3/BasicClass.lean, line 804
- `Polyfold.StabilityData.pushB_isSc0ContractionGerm` — Polyfold/Chapter3/BasicClass.lean, line 935
- `Polyfold.scPlusRemainder_contraction` — Polyfold/Chapter3/BasicClass.lean, line 332
- `Polyfold.StabilityData.pushMap_eq_zero_iff` — Polyfold/Chapter3/BasicClass.lean, line 1046
- `Polyfold.StabilityData.finrank_Cs_eq_finrank_Zs` — Polyfold/Chapter3/BasicClass.lean, line 1065

*What differs.*
- The coordinate change is linear, so a pair of sc-isomorphisms replaces a general strong bundle isomorphism; the text's $\tau : Z \to C$ is not applied (new target $(Q \oplus Z) \oplus X^1$). The index raise is a change of sc-structure (Proposition 1.17 for germs) (Findings, Chapter 3, items 60–61).
- \"$S$ is an arbitrarily small contraction on every level $m \ge 1$\" needs the operator-norm continuity of the derivative of $s$ on level $m + 1$ and the mean value inequality (item 62). Only the $W$-component of $s$ enters; $B$ is used only through Definition 3.7 (item 63).
- The linear coordinate change is a strong bundle isomorphism of the index-raised structures (`StabilityData.linIso_isStrongBundleIso`, V3.76).

### V3.35. Theorem 3.40: local regularity and compactness

*stronger* · compact closures · closed $\widetilde C$ (true for quadrants) · only $B$ sc⁰ used

**HWZ (§3.5, Theorem 3.40, p. 94 (proof pp. 95–98)).** Let $f = h + s : U \to \mathbb R^N \oplus W$, $h$ a basic germ, $s$ an sc$^+$-germ with $s(0) = 0$, $S = \{f = 0\}$. There are relatively open neighbourhoods $U \supset O(0) \supset O(1) \supset \cdots$ of $0$ on level $0$ with $\mathrm{cl}_{C_0}(S \cap O(m)) \subseteq C_m$.

**Proved in Lean.** Let $B$ be an sc$^0$-contraction germ on $\widetilde C \oplus W$ with **$\widetilde C$ closed**, $\mathbf s$ sc$^0$ into $W^1$ with $\mathbf s(0) = 0$, and $S$ any set of solutions of $w = B(a, w) - \mathbf s(a, w)$ in $U_0$. There are nested open $O(i) \ni 0$ in $E_0$ with $\mathrm{cl}_{E_0}(S \cap O(i)) = \iota_i(K_i)$ for compact $K_i \subseteq E_i$; in particular $\mathrm{cl}(S \cap O(i)) \subseteq E_i$. For a basic germ plus an sc$^+$-germ this gives the local Theorem 3.12.

- `Polyfold.theorem_3_40_compactness` — Polyfold/Chapter3/LocalCompactness.lean, line 516
- `Polyfold.theorem_3_40_regularity` — Polyfold/Chapter3/LocalCompactness.lean, line 571
- `Polyfold.IsSc0ContractionGerm.exists_lift` — Polyfold/Chapter3/LocalCompactness.lean, line 365
- `Polyfold.IsSc0ContractionGerm.isCompact_lift_image` — Polyfold/Chapter3/LocalCompactness.lean, line 483
- `Polyfold.theorem_3_12_local` — Polyfold/Chapter3/LocalCompactness.lean, line 588

*What differs.*
- Stronger: the closures are compact in $E_i$, which Theorem 3.12 needs and Theorem 3.40 does not state (Findings, Chapter 3, item 12). Weaker hypotheses: of $f$ only the $W$-component, with $B$ sc$^0$ and the contraction estimate, and $\mathbf s$ sc$^0$ into $W^1$ (item 14).
- **$\widetilde C$ closed** is a hypothesis because the theorem is proved for convex $\widetilde C$; it holds for partial quadrants. The induction left to the reader needs existence, bound and continuity of the lifts together (item 13); the $O(i)$ are one level ahead of the text's.

### V3.36. Corollary 3.41: the linearization at nearby solutions

*restated* · $\mathbb R^N$-part of $s$ in $h$ · Fredholm at all small $x \in U_1$

**HWZ (§3.5, Corollary 3.41, p. 98 (proof pp. 98–100)).** For $f = h + s : U \to \mathbb R^N \oplus W$, $h$ basic, $s$ an sc$^+$-map, $s(0) = 0$, $Df(0)$ surjective: there is $U' \subseteq U$ relatively open on level $0$ such that (1) solutions in $U'$ are on level $1$; (2) at such solutions $Df(a, w) : E \to F$ is a surjective Fredholm operator of index $n - N$.

**Proved in Lean.** For the data of Theorem 3.38 ($f := h$ basic, $s$ the $W$-component of the sc$^+$-germ) with $D(h + s)(0)$ surjective: there is $r > 0$ such that every zero $x$ of $h + s$ in $U_0$ with $|x|_0 < r$ is $\iota(x_1)$ with $x_1 \in U_1$, and $D(h + s)(x_1) : E_0 \to F_0$ is a surjective Fredholm operator of index $\dim P - \dim Q$.

- `Polyfold.StabilityData.corollary_3_41` — Polyfold/Chapter3/SolutionLinearization.lean, line 947
- `Polyfold.StabilityData.exists_isFredholm_Dfs'` — Polyfold/Chapter3/SolutionLinearization.lean, line 742
- `Polyfold.StabilityData.exists_ker_Dfs'_inf_eq_bot` — Polyfold/Chapter3/SolutionLinearization.lean, line 835
- `Polyfold.isFredholm_add_of_norm_lt` — Polyfold/Chapter3/SolutionLinearization.lean, line 64
- `Polyfold.HasFiniteIndex.surjective_of_finrank_ker_le` — Polyfold/Chapter3/SolutionLinearization.lean, line 155
- `Polyfold.StabilityData.Kop_isCompactOperator` — Polyfold/Chapter3/SolutionLinearization.lean, line 665

*What differs.*
- The $\mathbb R^N$-component of the sc$^+$-map is absorbed into $h$ (as in Theorem 3.54, Findings item 85). The Fredholm property with index holds at every $x \in U_1$ small on level $1$, not only at solutions; $Df(x) = Df(0) + S(x) + K(x)$ with $\|S(x)\| \le \varepsilon$ and $K(x)$ compact; surjectivity from $\dim\ker \le n - N = \mathrm{ind}$; the detour through level $2$ is not needed (item 71).

### V3.37. Lemma 3.42: solutions of the push-forward are on level 1

*restated* · the form Theorem 3.43 uses

**HWZ (§3.5, Lemma 3.42, p. 101).** (In the setting after Theorem 3.38, $g = \Phi_*f$, $\delta$ the solution germ of $P' \circ g^1$.) There are $\varepsilon'_0, \tau'_0$ such that a solution $(a', w')$ of $g = 0$ with $|a'|_0 \le \varepsilon'_0$, $|w'|_0 \le \tau'_0$ has $w' = \delta(a')$, and $|\delta(a')|_0 \le \tau'_0$ if $|a'|_0 \le \varepsilon'_0$.

**Proved in Lean.** For every $\varepsilon > 0$ there is $r > 0$ such that every zero $x'$ of $g = \Phi_*(f + s)$ in $\psi(U)$ with $|x'|_0 < r$ has its $X$-component on level $1$ with $|\cdot|_1 < \varepsilon$.

- `Polyfold.StabilityData.lemma_3_42` — Polyfold/Chapter3/LocalSolvability.lean, line 1264
- `Polyfold.StabilityData.toShiftedBasicData` — Polyfold/Chapter3/LocalSolvability.lean, line 1246

*What differs.*
- The formal statement is the regularity Theorem 3.43's proof uses (solutions near $0$ lie on level $1$ and are small there), proved from the lifts of Theorem 3.40 and the linearity of $\psi$; the identification $w' = \delta(a')$ is made inside Theorem 3.43 (Findings, Chapter 3, item 65).

### V3.38. Theorem 3.43: local germ-solvability I

*restated* · (1) as $C^k$ into $E_k$ on $V_k$ · Lemma 3.42 as hypothesis

**HWZ (§3.5, Theorem 3.43, p. 102 (proof pp. 102–106)).** Let $f = h + s$ with $Df(0)$ surjective and $K = \ker Df(0)$ in good position to $C$, $g = \Phi_*(f)$. Then $K' = \ker Dg(0)$ is in good position to $C'$, there are a good complement $Y'$ and a $C^1$ map $\tau : V \to Y'_1$, $V$ relatively open in $K' \cap C'$, with (1) $\tau$ an sc-smooth germ; (2) $\tau(0) = 0$, $D\tau(0) = 0$; (3) after shrinking $U$, $\varphi(\{f = 0\}) = \{g = 0\} = \{y + \tau(y) \mid y \in V\}$.

**Proved in Lean.** For an sc-smooth germ $g$ with $g(0) = 0$ whose index-raised germ $g^1$ is basic (`ShiftedBasicData`), $\widetilde C$ a partial quadrant, $Dg(0)$ onto, $K' = \ker Dg(0)$ in good position, and the regularity hypothesis of Lemma 3.42: there are a good complement $Y = Z \oplus W$, $V$ relatively open in $K' \cap C'$ and $\tau : V \to Y$ of class $C^1$ with values on level $1$, $\tau(0) = 0$, $D\tau(0) = 0$, every $y + \tau(y)$ a zero in $U$, every zero in $U$ near $0$ of this form; and (1) for every $k \ge 1$ a relatively open $V_k \subseteq V$ containing $0$ and a $C^k$ map $\tau_k : V_k \to E_k$ with $\iota_k\tau_k = \tau$ on $V_k$.

- `Polyfold.theorem_3_43_sc_smooth` — Polyfold/Chapter3/LocalSolvability.lean, line 1192
- `Polyfold.theorem_3_43` — Polyfold/Chapter3/LocalSolvability.lean, line 1218
- `Polyfold.ShiftedBasicData` — Polyfold/Chapter3/LocalSolvability.lean, line 315
- `Polyfold.ShiftedBasicData.Sol.exists_contDiffOn_level` — Polyfold/Chapter3/LocalSolvability.lean, line 866
- `Polyfold.ShiftedBasicData.H_contDiffOn` — Polyfold/Chapter3/LocalSolvability.lean, line 410
- `Polyfold.ShiftedBasicData.Sol.τ` — Polyfold/Chapter3/LocalSolvability.lean, line 777
- `Polyfold.ShiftedBasicData.Sol.exists_eq_add_τ` — Polyfold/Chapter3/LocalSolvability.lean, line 1075
- `Polyfold.exists_proj_mem_of_eq_zero` — Polyfold/Chapter3/LocalSolvability.lean, line 257

*What differs.*
- (1), \"$\tau$ is an sc-smooth germ\", is proved level-wise with $k$-dependent neighbourhoods (the reading of V3.22 and Corollary 3.34): $C^k$ into $E_k$ on $V_k$. The proof applies Theorem 3.78 to $H$ at regularity $k$ and identifies its solution with the $C^1$ one by the uniqueness clause, which the text does not discuss (Findings, Chapter 3, item 70). `theorem_3_43` is the statement without (1). Lemma 3.42 enters as the explicit hypothesis `hreg`, proved for the push-forward of Theorem 3.38 in V3.37 (item 65).
- A gap in the text's proof of (3) is filled: the $\widetilde K$-component of a solution lies in $\widetilde C$, because $|z| \le \varepsilon|k|$ near $0$ (item 66). $H$ is $C^j$ near $0$ by Corollary 3.34 for $g^1$ and Proposition 1.18 for germs (item 67).
- With the good complement closed and its projection onto $K'$ mapping $\widetilde C \oplus W$ into itself: V3.77.

### V3.39. Lemma 3.44: the kernel of $Dg(0)$ is a graph

*as in the book*

**HWZ (§3.5, Lemma 3.44, p. 103).** The map $\alpha \mapsto (\alpha, D\delta(0)\alpha)$ induces a linear isomorphism $\widetilde K = \ker DH(0) \to \ker Dg(0) = K'$, $H(a) = (1 - P') \circ g(a, \delta(a))$.

**Proved in Lean.** In the data of Theorem 3.43: $\ker Dg(0) = \{(\alpha, D\delta(0)\alpha) \mid \alpha \in \ker DH(0)\}$; the $W$-component of $Dg(0)(0, \zeta)$ is $\zeta$ for every $\zeta \in W_0$; and $DH(0)$ is onto when $Dg(0)$ is.

- `Polyfold.ShiftedBasicData.Deriv.ker_Dg_eq` — Polyfold/Chapter3/LocalSolvability.lean, line 634
- `Polyfold.ShiftedBasicData.Deriv.snd_Dg_inr` — Polyfold/Chapter3/LocalSolvability.lean, line 569
- `Polyfold.ShiftedBasicData.Deriv.DH₀_surjective` — Polyfold/Chapter3/LocalSolvability.lean, line 666

*What differs.*
- \"Recalling from Lemma 3.9 that $D_2B(0) = 0$\": Lemma 3.9 gives it for $g^1$ on level $1$; the level-$0$ identity follows by density of $W_1$ in $W_0$ (Findings, Chapter 3, item 68).

### V3.40. Lemma 3.45: good position under linear isomorphisms

*stronger* · any linear iso with $S(C) = C'$

**HWZ (§3.5, Lemma 3.45, p. 104).** The complement $(K')^\perp = T\varphi(0)(K^\perp)$ is a good complement of $K' = T\varphi(0)K$ in $E'$.

**Proved in Lean.** For any continuous linear isomorphism $S : E_0 \to E'_0$ with $x \in C \iff Sx \in C'$: $S$ carries a good complement $P$ of $N$ to a good complement $S(P)$ of $S(N)$, with $\varepsilon' = \varepsilon/(\|S\|\|S^{-1}\| + 1)$, and good position to good position.

- `Polyfold.IsGoodComplement.map` — Polyfold/Chapter3/GoodPosition.lean, line 694
- `Polyfold.IsInGoodPosition.map` — Polyfold/Chapter3/GoodPosition.lean, line 734

*What differs.*
- Stated for any linear isomorphism carrying $C$ onto $C'$ (Findings, Chapter 3, item 21); since the coordinate change of Theorem 3.38 is linear, this is the form used.

### V3.41. Lemma 3.46: good position of $\ker DH(0)$

*as in the book* · no intermediate complement $Y_0$

**HWZ (§3.5, Lemma 3.46, p. 104 (proof §3.8.2, pp. 129–132)).** $\widetilde K = \ker DH(0) \subseteq \mathbb R^{n'}$ is in good position to $\widetilde C$, and there is a good complement $Z$ of $\widetilde K$ in $\mathbb R^{n'}$ such that $Z \oplus W'$ is a good complement of $K' = \ker Dg(0)$.

**Proved in Lean.** If $K' = \{(\alpha, L\alpha) \mid \alpha \in \widetilde K\}$ has the good complement $Y'$ with respect to $\widetilde C \oplus W$, there is a good complement $Z$ of $\widetilde K$ with respect to $\widetilde C$ such that $Z \times W$ is a good complement of $K'$; and if $K'$ is in good position, so is $\widetilde K$.

- `Polyfold.lemma_3_46` — Polyfold/Chapter3/LocalSolvability.lean, line 59
- `Polyfold.lemma_3_46_isInGoodPosition` — Polyfold/Chapter3/LocalSolvability.lean, line 178

*What differs.*
- The proof takes $Z' = \mathrm{pr}(Y')$ and a right inverse of the projection; the text's intermediate complement $Y_0$ is not needed (Findings, Chapter 3, item 64).

### V3.42. Corollary 3.47: local germ-solvability for $f + s$

*restated* · (1) as $C^k$ into $E_k$ on $V_k$ · no Theorem 3.72 / Lemma 3.70 needed

**HWZ (§3.5, Corollary 3.47, p. 106 (proof pp. 106–108)).** Under the hypotheses of Theorem 3.43 there are a good complement $Y$ of $K$ and a $C^1$ map $\sigma : V \to Y_1$, $V$ relatively open in $K \cap C$, with (1) $\sigma$ an sc-smooth germ; (2) $\sigma(0) = 0$, $D\sigma(0) = 0$; (3) $\{x \in U \mid f(x) = 0\} = \{v + \sigma(v) \mid v \in V\}$ after shrinking $U$.

**Proved in Lean.** For a basic germ $f$ and the data of Theorem 3.38 with $D(f + s)(0)$ surjective and kernel $K$ in good position to $\widetilde C \oplus W$: a good complement $Y$ of $K$, $V$ relatively open in $K \cap C$, $\sigma : V \to Y$ of class $C^1$ with values on level $1$, $\sigma(0) = 0$, $D\sigma(0) = 0$, every $v + \sigma(v)$ a zero of $f + s$ in $U_0$, an open $U'' \ni 0$ in which every zero is of this form; and (1) for every $k \ge 1$ a relatively open $V_k \subseteq V$ containing $0$ and a $C^k$ lift $\sigma_k : V_k \to E_k$ of $\sigma$.

- `Polyfold.theorem_3_47_sc_smooth` — Polyfold/Chapter3/LocalSolvability.lean, line 1372
- `Polyfold.theorem_3_47` — Polyfold/Chapter3/LocalSolvability.lean, line 1572
- `Polyfold.StabilityData.scDerivGerm_pushMap₀` — Polyfold/Chapter3/LocalSolvability.lean, line 1330
- `Polyfold.StabilityData.toShiftedBasicData` — Polyfold/Chapter3/LocalSolvability.lean, line 1246

*What differs.*
- (1) in the level-wise sense of V3.38 (Findings, Chapter 3, item 70); `theorem_3_47` is the statement without (1), the form Theorem 3.54 uses so far.
- Because $\psi$ is linear, the transport back is linear algebra ($K = \psi^{-1}(K')$, $Y = \psi^{-1}(Y')$, $\sigma = \psi^{-1}\tau\psi$); the text's degeneracy-index argument with Lemma 3.70 and Theorem 3.72 is not needed (item 69).
- With the good complement closed and its projection onto $K$ mapping $\widetilde C \oplus W$ into itself: V3.77.

### V3.43. Definition 3.48: filling (restated)

*as in the book*

**HWZ (§3.6, Definition 3.48, p. 109).** Definition 3.4 restated for a tame strong local bundle $K \to O$.

**Proved in Lean.** `IsFillingGerm` (V3.7; the whole-chart form is `IsFillerOf`).

- `Polyfold.IsFillingGerm` — Polyfold/Chapter3/GermFilling.lean, line 143
- `Polyfold.IsFillerOf` — Polyfold/Chapter3/Filler.lean, line 158

*What differs.*
- Same notion as Definition 3.4.
- **Germs.** Since the switch to the text’s germ reading (phase 2) the filling is the germ notion `IsFillingGerm` (V3.7). The stricter whole-chart filler, for which “filled version = filling” on a given $U$ is false (round-trip item V3.43, a counterexample built from a step function, machine-checked there), is `IsFillerOf` with `IsFilledVersion`. Hence “as in the book” again (“narrower” in the third addendum) (Findings, Chapter 3, items 220–221, 330).

### V3.44. Remark 3.49: shrinking $O$

*as in the book*

**HWZ (§3.6, Remark 3.49, p. 109).** By replacing $O$ by a smaller set one may assume in Definition 3.48 that (1) holds on all of $O$ and (2) for all $y \in U$.

**Proved in Lean.** For a filler: there is an open $W \ni 0$ with $f = g$ on $O \cap W$ and $g(y) = \rho(r(y))g(y)$, $y \in U \cap W$, implying $y \in O$.

- `Polyfold.IsFillerOf.remark_3_49` — Polyfold/Chapter3/FillerLinearization.lean, line 399

*What differs.*
- As in the text.

### V3.45. Definitions 3.50 and 3.51: sc-Fredholm germs and sections of a tame strong bundle (restated)

*as in the book* · tame chart: V3.103

**HWZ (§3.6, Definitions 3.50, 3.51, p. 110).** Definition 3.11 restated for the tame strong bundle, with the chart of the germ data “where $K \to O$ is a tame strong local bundle” (3.50); Definition 3.14 without the clause \"$f$ is sc-smooth\", part of the standing hypothesis (3.51).

**Proved in Lean.** `StrongBundle.IsScFredholmGerm` (V3.13), `StrongBundle.IsScFredholmSection` (V3.16), without tameness; with the chart of the germ data tame, as the theorems of §3.6 use them, `StrongBundle.IsScFredholmGermTame`, `StrongBundle.IsScFredholmSectionTame` (V3.103). All four in the text’s germ reading (V3.13); the whole-chart forms are `…WholeChart`.

- `Polyfold.StrongBundle.IsScFredholmGerm` — Polyfold/Chapter3/GermFillingChart.lean, line 192
- `Polyfold.StrongBundle.IsScFredholmSection` — Polyfold/Chapter3/TameGermsG.lean, line 54
- `Polyfold.StrongBundle.IsScFredholmGermTame` — Polyfold/Chapter3/TameGermsG.lean, line 78
- `Polyfold.StrongBundle.IsScFredholmSectionTame` — Polyfold/Chapter3/TameGermsG.lean, line 142
- `Polyfold.StrongBundle.IsScFredholmGermTameWholeChart` — Polyfold/Chapter3/TameGerms.lean, line 144

*What differs.*
- The tame forms (V3.103) are the text’s notions; the forms of V3.13 and V3.16 drop the tameness of the chart, which §3.1 does not need. Updated after the repair of the tameness hypothesis (Findings, Chapter 3, item 191).
- **Germs.** Since the switch to the text’s germ reading (phase 2) the four notions take the filling and the sc$^+$-section as germs whose levels may shrink with $m$ (`IsFillingGerm`, `IsScPlusGerm`); the earlier whole-chart forms (`IsScFredholmGermTameWholeChart`, …), which imply them (round-trip item V3.45), are kept. Hence “as in the book” again (“narrower” in the third addendum) (Findings, Chapter 3, items 220–221, 330).

### V3.46. Proposition 3.52: the linearization at a zero is Fredholm of index $n - N$

*restated* · sc-Fredholm, in every chart · index $n - N$ for every conjugation

**HWZ (§3.6, Proposition 3.52, p. 110).** If $f$ is an sc-Fredholm section of the tame strong bundle $P : Y \to X$ and $f(x) = 0$, then $Tf(x) : T_xX \to Y_x$ is an sc-Fredholm operator (of the index $n - N$ of the basic germ, as the proof of Theorem 3.54 uses).

**Proved in Lean.** For a section $f$ with $(f, x_0)$ an sc-Fredholm germ and $f(x_0) = 0$: in the chart of Definition 3.11 centred at $x_0$, with the filling germ $g$ (a derivative family $Dg$ on a germ $G \subseteq U$) and the local sc$^+$-germ $s$, $Dg(0) : E \to F$ is an sc-Fredholm operator, $T_0O = Dr(0)E$ and $K_0 = \rho(0)F$ are sc-subspaces, and $Tf(x_0) = Dg(0)|_{T_0O} : T_0O \to K_0$ is an sc-Fredholm operator; for **every** conjugation of $g - s$ to a basic germ $h : O(\widetilde C \oplus W, 0) \to \mathbb R^N \oplus W$, $\widetilde C \subseteq \mathbb R^n$ (`ConjugationData`), both are Fredholm of index $n - N$ on every level. In particular $n - N$ does not depend on the conjugation. For an sc-Fredholm section the same holds in **every** strong bundle chart around a zero $y$: at the point $z$ over $y$, $T_zO = Dr(z)E$ and $K_z = \rho(z)F$ are sc-subspaces and $\mathrm{Lin}(z) : T_zO \to K_z$ is sc-Fredholm, of index $n - N$ on every level.

- `Polyfold.proposition_3_52_index` — Polyfold/Chapter3/FredholmGermIndexG.lean, line 136
- `Polyfold.proposition_3_52_local_index` — Polyfold/Chapter3/FredholmGermIndexG.lean, line 84
- `Polyfold.ConjugationData` — Polyfold/Chapter3/FredholmGermIndex.lean, line 73
- `Polyfold.ConjugationData.scDeriv_isFredholm_index` — Polyfold/Chapter3/FredholmGermIndexG.lean, line 51
- `Polyfold.ConjugationData.index_eq` — Polyfold/Chapter3/FredholmGermIndexG.lean, line 61
- `Polyfold.proposition_3_52` — Polyfold/Chapter3/FredholmGermLinearizationG.lean, line 383
- `Polyfold.proposition_3_52_local` — Polyfold/Chapter3/FredholmGermLinearizationG.lean, line 288
- `Polyfold.isFredholm_equiv_comp_equiv` — Polyfold/Chapter3/FredholmGermLinearization.lean, line 236
- `Polyfold.proposition_3_10_basic_level_zero` — Polyfold/Chapter3/FredholmGermLinearization.lean, line 302
- `Polyfold.proposition_3_52_sc` — Polyfold/Chapter3/FredholmGermLinearizationScG.lean, line 292
- `Polyfold.proposition_3_52_local_sc` — Polyfold/Chapter3/FredholmGermLinearizationScG.lean, line 193
- `Polyfold.ConjugationData.scDeriv_isScFredholm` — Polyfold/Chapter3/FredholmGermLinearizationScG.lean, line 112
- `Polyfold.StrongBundle.linAt_isScFredholm` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 400

*What differs.*
- Proved in sc form, in charts: $T_0O$, $K_0$ (and $T_zO$, $K_z$ in any chart) with the induced sc-structures stand for $T_xX$, $Y_x$, which carry no linear structure here (G.7). Two steps the text leaves out: that $D(g - s)(0) = \Gamma(0)^{-1}Dh(0)D\psi(0)$, the conjugate of the basic germ's linearization, is sc-Fredholm (the criterion of V1.8: $\Gamma(0)$ preserves the levels and $Dh(0)$ is regularizing), and the sc-structures of $T_0O$, $K_0$ (Definition 2.47 at the smooth point $0$, the closed graph theorem). No tameness is assumed. In other charts the levels are transported by the chart change at smooth points (Findings, Chapter 3, items 235, 239). Formerly level $0$ only (G.22, Findings item 48); updated in the third addendum of this page.
- The first formal statement (`proposition_3_52`, kept for the theorems that use it) gives the index as “$n - N$ for some $n, N \in \mathbb N$”, which every integer satisfies. `proposition_3_52_index` names the conjugation data and identifies $n$, $N$ with the dimensions of the conjugating basic germ, for every conjugation (Findings, Chapter 3, item 120). Updated after the first edition of this page.
- In every other strong bundle chart around $x_0$ the linearization is Fredholm of the same index, and onto at a zero in good position (V3.96). Updated in the second addendum of this page.
- **Germs.** The hypothesis is the text’s since the switch to the germ reading (phase 2): an sc-Fredholm germ whose filling and sc$^+$-section are germs whose levels may shrink with $m$ (V3.13); $Dg(0)$ is the value at $0$ of a derivative family of the filling germ, the same for every family on every germ. The forms for germ data on the whole chart are the `_wholeChart` declarations of the same names (Findings, Chapter 3, items 220–221, 289, 310, 331). Hence “restated” (formerly “narrower”, for that hypothesis): what remains is the reading in charts.

### V3.47. Definition 3.53: good position of an sc-Fredholm germ

*restated* · in the chart · no case distinction $d_X \ge 1$ · sc-complement form: the same at zeros

**HWZ (§3.6, Definition 3.53, p. 111).** An sc-Fredholm germ $(f, x)$ of a tame strong bundle with $f(x) = 0$ is in good position if (1) $f'(x) : T_xX \to Y_x$ is surjective and (2) if $d_X(x) \ge 1$, $\ker f'(x)$ is in good position to the partial cone $C_xX$ in $T_xX$.

**Proved in Lean.** In the chart of Definition 3.11 (`IsGoodPositionAtGerm`, at $Dg(0)$ for a derivative family $Dg$ of the filling germ $g$): $Tf(0) = Dg(0)|_{T_0O} : T_0O \to K_0$ is onto and $\ker Dg(0)$ is in good position to $C_0O = T_0O \cap C$ inside $T_0O$ (`IsInGoodPositionIn`); `IsGoodPositionAt` is the case of a whole-chart filled version. For a section (`StrongBundle.IsGoodPositionGerm f x₀`): the data of Definition 3.11 at $x_0$ with the germ in good position in that chart. With the text’s sc-complement (`IsGoodPositionAtScGerm`; for a section `StrongBundle.IsGoodPositionGermSc`, in a tame chart): the kernel has a good sc-complement inside $T_0O$ ($T_m = N_m \oplus P_m$ on every level). At a zero of an sc-Fredholm section with tame germ data the two forms agree.

- `Polyfold.IsGoodPositionAtGerm` — Polyfold/Chapter3/GoodPositionGermG.lean, line 177
- `Polyfold.IsGoodPositionAt` — Polyfold/Chapter3/GoodPositionGerm.lean, line 273
- `Polyfold.IsInGoodPositionIn` — Polyfold/Chapter3/GoodPositionGerm.lean, line 116
- `Polyfold.StrongBundle.IsGoodPositionGerm` — Polyfold/Chapter3/GoodPositionGermG.lean, line 489
- `Polyfold.StrongBundle.IsGoodPositionGerm.forall_isGoodPositionAtGerm` — Polyfold/Chapter3/GoodPositionGermG.lean, line 523
- `Polyfold.IsFillingGerm.ker_deriv_le_range` — Polyfold/Chapter3/GoodPositionGermG.lean, line 118
- `Polyfold.IsScGoodComplementIn` — Polyfold/Chapter3/GoodPositionSc.lean, line 168
- `Polyfold.IsInGoodPositionScIn` — Polyfold/Chapter3/GoodPositionSc.lean, line 181
- `Polyfold.IsGoodPositionAtScGerm` — Polyfold/Chapter3/GoodPositionScG.lean, line 82
- `Polyfold.IsGoodPositionAtSc` — Polyfold/Chapter3/GoodPositionSc.lean, line 401
- `Polyfold.StrongBundle.IsGoodPositionGermSc` — Polyfold/Chapter3/GoodPositionScG.lean, line 145
- `Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGermSc` — Polyfold/Chapter3/GoodPositionScG.lean, line 191
- `Polyfold.StrongBundle.isGoodPositionGermSc_iff` — Polyfold/Chapter3/GoodPositionScG.lean, line 247

*What differs.*
- Stated in a chart centred at $x$, not in $T_xX$ (the transport of $C_xX$ to $T_xX$ is not formalized, Chapter 2 gap). The case distinction $d_X(x) \ge 1$ is dropped: at an interior point (2) holds trivially (Findings, Chapter 3, item 50), and for tame germ data good position in a tame chart at a zero with $d_X = 0$ is the surjectivity of the linearization (V3.100).
- At a zero, the linearization and the two conditions do not depend on the chart (V3.78); Definition 3.53 at a zero from a chart not centred there is V3.79, in any chart of the germ data V3.107. The form in a tame chart (`StrongBundle.IsGoodPositionGermTame`), which the theorems of §3.6 assume and conclude, is V3.103.
- The sc form needs the kernel smooth and a closed good complement in $E$. At a zero $\ker Dg(0)$ is the image under $D\psi'(0)$ of the basic germ's smooth kernel, and the good position of the kernel in $E$ comes from the transport from $T_0O$, so V3.20 applies (Findings, Chapter 3, item 212). “$T = N \oplus P$ an sc-splitting of $T$” is written in $E$; its equivalence with an sc-splitting of the sc-Banach space $T_0O$ is not formalized, nor is the upgrade from good position inside $T$ alone (items 211, 214). Updated in the third addendum of this page.
- **Germs.** Since the switch to the text’s germ reading (phase 2) the germ data are the text’s (V3.13), and the condition in the chart is read at $Dg(0)$, the value at $0$ of any derivative family of the filling germ (the same for all, `IsGoodPositionGerm.forall_isGoodPositionAtGerm`); the whole-chart forms are `IsGoodPositionGermWholeChart`, `IsGoodPositionGermScWholeChart` (Findings, Chapter 3, items 220–221, 280, 320, 330).

### V3.48. Theorem 3.54: the solution set as a graph (part (3) of the proof)

*narrower* · the graph description (3) · tame chart at $x_0$ · (1), (2): V3.82, V3.85

**HWZ (§3.6, Theorem 3.54, p. 111 (proof pp. 111–115)).** Let $f$ be an sc-Fredholm section of a tame strong bundle with $f(x) = 0$ and $(f, x)$ in good position. There is an open $V \ni x$ such that $S = \{y \in V \mid f(y) = 0\}$ has: (1) at every $y \in S$, $(f, y)$ is in good position; (2) $S$ is a sub-M-polyfold whose induced structure is equivalent to a smooth manifold with boundary with corners. The proof shows (3): $\psi\varphi(S) = \{v + \sigma(v) \mid v \in V'\}$ for the $\sigma$ of Corollary 3.47 applied to $\Psi_*(g) = h + t$.

**Proved in Lean.** For a section $f$ of a strong bundle, $f(x_0) = 0$ and $(f, x_0)$ in good position in a tame chart (V3.103): a tame chart $\varphi$ centred at $x_0$, the conjugating sc-diffeomorphism $\psi$ with its inverse, a basic germ $h' = h + (t_{\mathbb R^N}, 0)$ with the data of Theorem 3.38 and $D(h + t)(0)$ surjective with kernel $K$ in good position, $K$ a smooth subspace; a **closed** good complement $Y$; $V'$ relatively open in $K \cap C'$, $\sigma : V' \to Y$ $C^1$ with values on level $1$, $\sigma(0) = 0$, $D\sigma(0) = 0$, every $v + \sigma(v)$ a zero of $h + t$, and $C^k$-lifts $\sigma_k : V_k \to E'_k$ near $0$ for every $k$ (Theorem 3.47 (1)); and an open $V_x \ni x_0$ on which $\psi\varphi$ is injective, $f(y) = 0 \iff (h + t)(\psi\varphi(y)) = 0$, and $\psi\varphi(\{y \in V_x \mid f(y) = 0\}) = \{v + \sigma(v) \mid v \in V'\}$.

- `Polyfold.theorem_3_54_graph` — Polyfold/Chapter3/GlobalIFTG.lean, line 281
- `Polyfold.theorem_3_54_linear` — Polyfold/Chapter3/GoodPositionGermG.lean, line 236
- `Polyfold.theorem_3_54_linear_of_isTameWith` — Polyfold/Chapter3/GoodPositionGermG.lean, line 254
- `Polyfold.IsInGoodPositionIn.isInGoodPosition` — Polyfold/Chapter3/GoodPositionGerm.lean, line 139
- `Polyfold.scDeriv_mem_iff_of_inverse` — Polyfold/Chapter3/GoodPositionGerm.lean, line 358
- `Polyfold.IsStrongBundleIso.pushforward_linearization` — Polyfold/Chapter3/GoodPositionGermG.lean, line 342
- `Polyfold.theorem_3_54_pushforward` — Polyfold/Chapter3/GoodPositionGermG.lean, line 436
- `Polyfold.scDeriv_eq_of_eqOn_nhds` — Polyfold/Chapter3/GlobalIFT.lean, line 131

*What differs.*
- This row is the graph description (3) of the proof. Conclusions (1) and (2) of the theorem are formalized since the first edition of this page: V3.82 (under an added hypothesis) and V3.85; the choice of $Y$ with the projection property is V3.77.
- Tameness enters through $(1 - Dr(0))E \subseteq E_0$ (Proposition 2.35), for the base retraction of the chart at $x_0$; the text's $C' = T\psi(0)C$ is proved by the sign argument; the $\mathbb R^N$-component of $t$ is absorbed into $h$; $D(h + t)(0)$ is identified with $D(\Psi_*g)(0)$ by uniqueness on level $1$; the unspecified $V$ is made explicit (items 50, 85, 86). The closedness of $Y$, the smoothness of $K$ and the lifts of $\sigma$ are recorded for Definition 3.25 (items 93, 94).
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).

### V3.49. Lemma 3.55: good position along a graph

*narrower* · added: $Y$ closed · $\tau$ on all of $N \cap C$ (here) · uniform $\gamma$

**HWZ (§3.6, Lemma 3.55, p. 114 (proof §3.8.3, pp. 132–135)).** $C \subseteq E$ a partial quadrant, $N$ a finite-dimensional smooth subspace in good position with good complement $Y$, $V \subseteq N \cap C$ relatively open, $\tau : V \to Y_1$ of class $C^1$ with $\tau(0) = 0$, $D\tau(0) = 0$. Then for $v$ in a relatively open $V' \ni 0$: (1) $v + \tau(v) \in C_1$; (2) $Y$ is a topological complement of $N_v = \{n + D\tau(v)n\}$; (3) there is $\gamma_v > 0$ with $n \in C_x \iff n + y \in C_x$ for $n \in N_v$, $y \in Y$, $|y|_0 \le \gamma_v|n|_0$, $x = v + \tau(v)$.

**Proved in Lean.** In the model $E = \mathbb R^n \oplus W$, $C = [0, \infty)^n \oplus W$ (in coordinates for any $C$ cut out by functionals): for $N$ in good position with **closed** good complement $Y$ and $\tau : N \to E$ with values in $Y$, $C^1$ on $N \cap C$, $\tau(0) = 0$, $D\tau(0) = 0$: there is $\rho > 0$ such that for $v \in N \cap C$, $|v| < \rho$: $v + \tau(v) \in C$ and $Y$ is a good complement of $N_v$ with respect to $C_{v + \tau(v)}$ (so $E_0 = N_v \oplus Y$, both closed), with a constant independent of $v$.

- `Polyfold.lemma_3_55` — Polyfold/Chapter3/GoodPositionOpen.lean, line 260
- `Polyfold.lemma_3_55_core` — Polyfold/Chapter3/GoodPositionOpen.lean, line 153
- `Polyfold.fderivWithin_mem_of_mapsTo` — Polyfold/Chapter3/GoodPositionOpen.lean, line 87
- `Polyfold.graphSpace` — Polyfold/Chapter3/GoodPositionOpen.lean, line 111

*What differs.*
- **Added hypothesis: $Y$ closed**, needed for \"$D\tau(v)n \in Y$\" (the text's topological complement is closed) (Findings, Chapter 3, item 49).
- $\tau$ is a map on all of $N \cap C$ (the text: on a neighbourhood $V$). The form used in Theorem 3.54 — $\sigma$ on a relatively open $V \subseteq N \cap C$, any presentation of $C$, and the good position of $N_v$ — is `lemma_3_55_relOpen` (V3.80): $\sigma$ is extended to the cone by a bump. The sc-level of the values plays no role ((1) is $v + \tau(v) \in C$). The constant $\gamma_v$ can be chosen uniformly; the case $v \notin N \cap W$ needs no normal form.

### V3.50. Theorem 3.56: the global implicit function theorem, $\partial X = \emptyset$ (from the tangent germ property)

*narrower* · assumes the tangent germ property of $S$

**HWZ (§3.6, Theorem 3.56, p. 115).** If $P : Y \to X$ is a tame strong bundle over an M-polyfold with $\partial X = \emptyset$ and $f$ an sc-Fredholm section with surjective linearization at every point of $S = \{f = 0\}$, then $S$ is a sub-M-polyfold whose induced structure is equivalent to a smooth manifold without boundary.

**Proved in Lean.** If $X$ is without boundary and $S = \{f = 0\} \ne \emptyset$ has at every point the regular data of Definition 3.25 (V3.22, `IsRegular`), then $S$ is a sub-M-polyfold whose induced structure is that of an $n$-dimensional manifold with corners and is without boundary.

- `Polyfold.theorem_3_56_of_tangentGerm` — Polyfold/Chapter3/GlobalIFT.lean, line 742
- `Polyfold.solutionSet` — Polyfold/Chapter3/GlobalIFT.lean, line 716

*What differs.*
- Formalized here is the second step of the text's proof: from the tangent germ property of $S$ to the manifold structure (Theorem 3.27, with $d_S = 0$ by Lemma 2.26). The theorem with the text's hypotheses, through Theorem 3.54 at every zero, is V3.86.

### V3.51. Theorem 3.57: the global implicit function theorem, boundary case (from the tangent germ property)

*narrower* · assumes the tangent germ property of $S$

**HWZ (§3.6, Theorem 3.57, p. 115).** If $P : Y \to X$ is a tame strong bundle and $f$ an sc-Fredholm section such that at every $x \in S = \{f = 0\}$ the linearization is surjective with kernel in good position to $C_xX$, then $S$ is a sub-M-polyfold whose induced structure is equivalent to a smooth manifold with boundary with corners.

**Proved in Lean.** If $S = \{f = 0\} \ne \emptyset$ has at every point the regular data of Definition 3.25, then $S$ is a sub-M-polyfold whose induced structure is tame and that of an $n$-dimensional manifold with boundary with corners.

- `Polyfold.theorem_3_57_of_tangentGerm` — Polyfold/Chapter3/GlobalIFT.lean, line 729

*What differs.*
- As V3.50: the step from the tangent germ property. The theorem with the text's hypotheses is V3.87.

### V3.52. Lemma 3.59: injectivity of $P_Y Df(b)$ on $X$ near $0$ (abstract form)

*restated* · abstract family $L(b)$ · hypotheses derived in V3.89

**HWZ (§3.7, Lemma 3.59, p. 117).** In the setting of Theorem 3.58 ($Y = Df(0)X$, $P_Y$ the projection along a finite-dimensional complement $A$), there is a relatively open neighbourhood $O$ of $0$ in $B \cap C$ such that $P_Y \circ Df(b) : X \to Y$ has trivial kernel for $b \in O$.

**Proved in Lean.** For a family $b \mapsto L(b)$ of sc-operators $X \to Y$ with $(b, h) \mapsto L(b)h$ continuous on $O \times X_0$ ($O \ni 0$), $L(0)$ injective on $X_0$, and the compactness property on level $0$ (`FamilyCompactness`: $b_j \to b$, $h_j$ bounded, $L(b_j)h_j \to 0$ imply a convergent subsequence of $h_j$): $L(b)$ is injective on $X_0$ for $b \in O$ near $0$.

- `Polyfold.lemma_3_59` — Polyfold/Chapter3/BasicGermCriterion.lean, line 49
- `Polyfold.FamilyCompactness` — Polyfold/Chapter3/BasicGermCriterion.lean, line 39

*What differs.*
- Formalized for an abstract family with the compactness property that condition (2) of Theorem 3.58 gives for $L = P_Y \circ Df|_X$ (the difference $(1 - P_Y)Df(b_j)h_j$ lies in the finite-dimensional $A$). In the proof of Theorem 3.58 these hypotheses are derived from the theorem's (`familyCompactness_derivFamOp`, `continuousOn_derivFamOp`; V3.89; Findings, Chapter 3, item 73).

### V3.53. Lemma 3.60: uniform lower bounds (abstract form)

*restated* · abstract family · injectivity on level $m$ assumed

**HWZ (§3.7, Lemma 3.60, p. 118).** For a relatively open $\widetilde O \ni 0$ in $C \cap B$ with compact closure in $O$ (Lemma 3.59), for every $m$ there is $c_m > 0$ with $|P_Y \circ Df(b)h|_m \ge c_m|h|_m$ for $b \in \widetilde O$, $h \in X_m$.

**Proved in Lean.** For a compact $K$, a family of sc-operators $L(b)$ with $(b, h) \mapsto L(b)_mh$ continuous on $K \times X_m$, every $L(b)_m$ ($b \in K$) injective, and the compactness property on level $m$: there is $c_m > 0$ with $c_m|h|_m \le |L(b)h|_m$ for $b \in K$, $h \in X_m$.

- `Polyfold.lemma_3_60` — Polyfold/Chapter3/BasicGermCriterion.lean, line 93

*What differs.*
- The injectivity of every $L(b)_m$ on $K$ is a hypothesis; in the proof of Theorem 3.58 it comes from Lemma 3.59 on level $0$ and `ScOperator.injective_lvl` (V3.89). The step “injective sc-Fredholm of index $0$, hence an sc-isomorphism” is the block index computation there (Findings, Chapter 3, item 73).

### V3.54. Lemma 3.61: the inverse of a family of sc-isomorphisms

*restated* · germ version · proof supplied

**HWZ (§3.7, Lemma 3.61, p. 118 (quoted from [25, Proposition 4.8], no proof)).** Let $V$ be relatively open in a partial quadrant of a finite-dimensional $G$, $v \mapsto L(v)$ a family of sc-isomorphisms $E \to F$ with $(v, h) \mapsto L(v)h$ sc-smooth and $|L(v)h|_m \ge c_m|h|_m$ for $v \in V$, $h \in E_m$. Then $(v, k) \mapsto L(v)^{-1}k$ is sc-smooth. Operator-norm continuity of $v \mapsto L(v)$ is not assumed.

**Proved in Lean.** For a germ $V$ of relatively open neighbourhoods of $0$ in a partial quadrant $\widetilde C$ of a finite-dimensional $G$ and sc-isomorphisms $L(v) : E \to F$ such that $\Phi(v, h) = L(v)h$ is an sc-smooth germ on $V \oplus E$ and $c_m\|h\| \le \|L(v)_mh\|$ for $v \in V_0$: $\Lambda(v, k) = L(v)^{-1}k$ is an sc-smooth germ on $V \oplus F$, with derivative $D\Lambda(v, k)(\delta v, \delta k) = L(v)^{-1}(\delta k - D_1\Phi(v, L(v)^{-1}k)\delta v)$.

- `Polyfold.lemma_3_61` — Polyfold/Chapter3/InverseFamily.lean, line 644
- `Polyfold.famInv_isSc0Germ` — Polyfold/Chapter3/InverseFamily.lean, line 100
- `Polyfold.famInv_isSc1GermWith` — Polyfold/Chapter3/InverseFamily.lean, line 464
- `Polyfold.famInv_hasFDerivWithinAt` — Polyfold/Chapter3/InverseFamily.lean, line 219
- `Polyfold.famInv_isSckGerm` — Polyfold/Chapter3/InverseFamily.lean, line 518
- `Polyfold.ScNbhdGerm.prodFull` — Polyfold/Chapter3/InverseFamily.lean, line 41
- `Polyfold.exists_forall_norm_le_of_isCompact` — Polyfold/Chapter3/InverseFamily.lean, line 158

*What differs.*
- Formalized for germs ($V$ a germ around $0$, $V \oplus E$ the product germ), the form Theorem 3.58 uses. The text gives no proof; the differentiability uses the remainder of $\Phi$ along $(\delta v, 0)$ and the compactness of $F_1 \to F_0$ in place of the operator-norm continuity, which is not assumed (Findings, Chapter 3, item 72).
- Used in set form in the proof of Theorem 3.58 (`famInv_isScSmooth_of`, V3.88).

### V3.55. Lemma 3.65: good complements avoid the vanishing coordinates

*as in the book* · any functionals cutting out $C$

**HWZ (§3.8.1, Lemma 3.65, p. 123).** $N^\perp \subseteq \mathbb R^\Sigma \oplus W$ (the text's notation), i.e. a good complement has vanishing coordinates $i \in \Sigma$, where $\Sigma$ is the set of indices vanishing at some nonzero point of $N \cap C$.

**Proved in Lean.** For functionals $\ell_i$ cutting out $C$ and a good complement $P$ of $N$: $\ell_i(p) = 0$ for $p \in P$ and $i \in \Sigma$. Consequence: $Q = (\ell_i)_{i \in \Sigma} : N \to \mathbb R^\Sigma$ is onto.

- `Polyfold.lemma_3_65` — Polyfold/Chapter3/GoodPosition.lean, line 124
- `Polyfold.vanIdx` — Polyfold/Chapter3/GoodPosition.lean, line 108
- `Polyfold.sigmaCoord_surjective` — Polyfold/Chapter3/GoodPosition.lean, line 161

*What differs.*
- As in the text (its $\mathbb R^\Sigma \oplus W$ is the set where the coordinates in $\Sigma$ vanish), for any family of functionals cutting out $C$.

### V3.56. Proposition 3.69: the degeneracy index of $N \cap C$

*restated* · (2) stated additively

**HWZ (§3.8.1, Proposition 3.69, p. 126).** For $N$ smooth, finite-dimensional, in good position to $C = [0, \infty)^n \oplus W$ in $E = \mathbb R^n \oplus W$, and $x \in N \cap C$: (1) $d_{N \cap C}(x) = d_C(x)$ if $x \notin N \cap W$; (2) $d_{N \cap C}(x) = \dim N - \dim(N \cap W)$ if $x \in N \cap W$.

**Proved in Lean.** In the model: (1) as stated; (2) as $d_{N \cap C}(x) + \dim(N \cap W) = \dim N$, with $N \cap W$ the kernel of $N \to \mathbb R^n$.

- `Polyfold.proposition_3_69` — Polyfold/Chapter3/GoodPosition.lean, line 761
- `Polyfold.QuadrantNormalForm` — Polyfold/Chapter3/GoodPosition.lean, line 305

*What differs.*
- (2) additively (natural-number subtraction avoided); proof read off the normal form of Proposition 3.22 (Findings, Chapter 3, item 20).

### V3.57. Lemma 3.70: the degeneracy index along a graph

*hypotheses explicit* · "close to 0" made explicit

**HWZ (§3.8.1, Lemma 3.70, p. 127).** For $N$ in good position to $C = [0, \infty)^n \oplus W$ with good complement $Y$ and $\tau : N \cap C \to Y_1$ of class $C^1$, $\tau(0) = 0$, $D\tau(0) = 0$: $d_{N \cap C}(v) = d_C(v + \tau(v))$ for $v \in N \cap C \setminus N \cap W$ close to $0$.

**Proved in Lean.** In the model: there is $\rho > 0$ such that for $v \in N \cap C$, $|v| < \rho$: $v + \tau(v) \in C$, and if $v \notin N \cap W$, $d_{N \cap C}(v) = d_C(v + \tau(v))$. The core, in coordinates: the vanishing coordinates of $v + \tau(v)$ are those of $v$.

- `Polyfold.lemma_3_70` — Polyfold/Chapter3/GoodPositionGraph.lean, line 292
- `Polyfold.lemma_3_70_core` — Polyfold/Chapter3/GoodPositionGraph.lean, line 174
- `Polyfold.exists_rayDecomp` — Polyfold/Chapter3/GoodPositionGraph.lean, line 83
- `Polyfold.exists_lipschitz_small` — Polyfold/Chapter3/GoodPositionGraph.lean, line 145

*What differs.*
- \"Close to $0$\" is $|v| < \rho/(1 + c)$ (smallness along a segment); the two cases $\dim N = 1$, $\dim N \ge 2$ are unified by a ray decomposition and a mean value estimate; the level $Y_1$ plays no role (Findings, Chapter 3, item 31).

### V3.58. Theorem 3.72: the quadrant inverse function theorem

*stronger* · $C^j$ for each $j$ · (2) used only as interior ⟺ interior

**HWZ (§3.8.4, Theorem 3.72, p. 136).** $C \subseteq \mathbb R^n$ a partial quadrant, $U \subseteq C$ a relatively open neighbourhood of $0$, $f : U \to \mathbb R^n$ smooth with $f(U) \subseteq C$, (1) $f(0) = 0$, $Df(0)C = C$; (2) $d_C(x) = d_C(f(x))$. Then $f$ is a diffeomorphism between relatively open neighbourhoods $U'$, $V'$ of $0$ in $C$.

**Proved in Lean.** For $C$ a partial quadrant in a finite-dimensional $V$ and $f$ of class $C^j$, $j \ge 1$, with (1), (2): relatively open $U' \subseteq U$, $V'$ containing $0$ with $f(U') = V'$, $f$ injective on $U'$, and an inverse $g$ of class $C^j$ on $V'$.

- `Polyfold.theorem_3_72` — Polyfold/Chapter3/QuadrantInverse.lean, line 530
- `Polyfold.surjective_of_image_eq` — Polyfold/Chapter3/QuadrantInverse.lean, line 506
- `Polyfold.degIndex_map_eq` — Polyfold/Chapter3/QuadrantInverse.lean, line 155
- `Polyfold.degIndex_eq_zero_iff` — Polyfold/Chapter3/QuadrantInverse.lean, line 121

*What differs.*
- For $C^j$, each $j \ge 1$ (smooth = all $j$). Hypothesis (2) is used only through \"$x$ interior iff $f(x)$ interior\" (Findings, Chapter 3, item 27). \"$Df(0)$ is an isomorphism from $\mathbb R^n = C - C$\": surjectivity needs only an interior point of $C$ (item 29).

### V3.59. Proposition 3.73: the normalized inverse function theorem

*stronger* · no $0 \in U$, $f(0) = 0$ · (3) as interior ⟺ interior

**HWZ (§3.8.4, Proposition 3.73, p. 137).** $U \subseteq C$ relatively open, convex, $0 \in U$, $f : U \to C$ smooth with (1) $f(0) = 0$, (2) $|Df(x) - 1| \le \tfrac12$, (3) $d_C(x) = d_C(f(x))$. Then $V = f(U)$ is relatively open in $C$ and $f : U \to V$ is a diffeomorphism.

**Proved in Lean.** Under `InvData` ($U$ relatively open and convex in $C$, $f : U \to C$ of class $C^j$, $\|Df - 1\| \le \tfrac12$, $f$ preserving interior points): $f(U)$ is relatively open in $C$, $f$ is injective on $U$, with an inverse of class $C^j$ on $f(U)$.

- `Polyfold.proposition_3_73` — Polyfold/Chapter3/QuadrantInverse.lean, line 483
- `Polyfold.InvData` — Polyfold/Chapter3/QuadrantInverse.lean, line 177
- `Polyfold.InvData.contDiffOn_inv` — Polyfold/Chapter3/QuadrantInverse.lean, line 461

*What differs.*
- $0 \in U$ and $f(0) = 0$ are not used; (3) only through interior points (Findings, Chapter 3, items 27, 29). Regularity of the inverse by bootstrapping $Dg = [Df]^{-1} \circ g$ instead of Lemma 3.76 (item 28).
- With the hypotheses its proof uses, without the partial quadrant (the unique differentiability of $f(U)$ in place of the interior condition): V3.90.

### V3.60. Lemma 3.74: bi-Lipschitz estimate and openness

*as in the book* · compactness instead of Cauchy sequence

**HWZ (§3.8.4, Lemma 3.74, p. 137 (proof pp. 137–139)).** Under the assumptions of Proposition 3.73, $V = f(U)$ is relatively open and $f : U \to V$ open, with $\tfrac12|x - x'| \le |f(x) - f(x')| \le \tfrac32|x - x'|$.

**Proved in Lean.** Under `InvData`: the two estimates (70), injectivity, $B(f(x'), r) \cap C \subseteq f(U)$ when $B(x', 3r) \cap C \subseteq U$, and $f(U)$ relatively open in $C$.

- `Polyfold.InvData.half_norm_le` — Polyfold/Chapter3/QuadrantInverse.lean, line 225
- `Polyfold.InvData.norm_sub_le` — Polyfold/Chapter3/QuadrantInverse.lean, line 234
- `Polyfold.InvData.injOn` — Polyfold/Chapter3/QuadrantInverse.lean, line 242
- `Polyfold.InvData.ball_inter_subset_image` — Polyfold/Chapter3/QuadrantInverse.lean, line 280
- `Polyfold.InvData.image_relOpen` — Polyfold/Chapter3/QuadrantInverse.lean, line 373

*What differs.*
- The Cauchy-sequence step is replaced by the compactness of $f(\bar B(x', 2r) \cap C)$; the interior starting point must be chosen with $f(x_0) \in B(y', r)$; typos \"$\tau_n \to \tau'$\", \"$B(x^0, r)$\" *(book 2017: both unchanged, Lemma 3.24, p. 122)* (Findings, Chapter 3, items 28, 30). Openness of $f$ on all relatively open subsets is not stated separately.

### V3.61. Corollary 3.75: $f$ is a homeomorphism

*as in the book*

**HWZ (§3.8.4, Corollary 3.75, p. 139).** Under the assumptions of Proposition 3.73, $f : U \to V$ is a homeomorphism between relatively open subsets of $C$.

**Proved in Lean.** Under `InvData`: $f$ continuous on $U$, its inverse continuous on $f(U)$, inverse to each other.

- `Polyfold.corollary_3_75` — Polyfold/Chapter3/QuadrantInverse.lean, line 492

*What differs.*
- As in the text ($V$ relatively open by V3.60).

### V3.62. Lemma 3.77: the inverse is $C^1$

*narrower* · under the hypotheses of Prop. 3.73

**HWZ (§3.8.4, Lemma 3.77, p. 140).** $U$ relatively open in $C$, $f : U \to C$ smooth with $V = f(U)$ relatively open, $f : U \to V$ a homeomorphism, $Df(x)$ invertible. Then $g = f^{-1}$ is $C^1$ with $Dg(y) = [Df(g(y))]^{-1}$.

**Proved in Lean.** Under `InvData`: the inverse is differentiable within $f(U)$ with $Dg(y) = [Df(g(y))]^{-1}$; it is of class $C^j$ by bootstrapping.

- `Polyfold.InvData.hasFDerivWithinAt_inv` — Polyfold/Chapter3/QuadrantInverse.lean, line 423
- `Polyfold.InvData.contDiffOn_inverse_deriv` — Polyfold/Chapter3/QuadrantInverse.lean, line 447

*What differs.*
- Proved under the hypotheses of Proposition 3.73, of which the lemma's three extra hypotheses are consequences; the general form (any homeomorphism with invertible derivative) is not stated (Findings, Chapter 3, item 28). The text cites \"Theorem 3.73\" for Proposition 3.73 *(book 2017: unchanged, renumbered: Lemma 3.26, p. 124, cites "Theorem 3.7" for Proposition 3.7)*.
- With the hypotheses its proof uses, without the partial quadrant: V3.90.

### V3.63. Theorem 3.78: the implicit function theorem in partial quadrants

*stronger* · two added conclusions/conditions · convex $C$ suffices · no shrinking of $V$

**HWZ (§3.8.5, Theorem 3.78, p. 141).** $U$ a relatively open neighbourhood of $0$ in $C = [0, \infty)^k \oplus \mathbb R^{n-k}$, $f : U \to \mathbb R^N$ of class $C^j$, $f(0) = 0$, $Df(0)$ onto, $K = \ker Df(0)$ in good position with good complement $Y$. Then there are $V$ open in $K \cap C$, a $C^j$ map $\tau : V \to Y$ and $\varepsilon, \sigma > 0$ with (1) $\tau(0) = 0$, $D\tau(0) = 0$, $k + \tau(k) \in U$; (2) $|\tau(k)| \le \sigma$ for $|k| \le \varepsilon$; (3) $f(k + y) = 0$, $|k| \le \varepsilon$, $|y| \le \sigma$ imply $y = \tau(k)$.

**Proved in Lean.** For a partial quadrant $C$ in a finite-dimensional $V$, $f : U \to F$ ($F$ any normed space) of class $C^j$, $j \ge 1$, with the hypotheses: $V'$ relatively open in $K \cap C$, $\tau : K \to Y$ of class $C^j$ on $V'$ with (1) $\tau(0) = 0$, $D\tau(0) = 0$, **$k + \tau(k) \in U$ and $f(k + \tau(k)) = 0$**; (2); (3) for $y \in Y$ with **$k + y \in U$**.

- `Polyfold.theorem_3_78` — Polyfold/Chapter3/QuadrantIFT.lean, line 648
- `Polyfold.ContractionData.exists_solution` — Polyfold/Chapter3/QuadrantIFT.lean, line 601
- `Polyfold.ContractionData` — Polyfold/Chapter3/QuadrantIFT.lean, line 91
- `Polyfold.Radii` — Polyfold/Chapter3/QuadrantIFT.lean, line 106

*What differs.*
- **Two clauses the text omits are included**: $f(k + \tau(k)) = 0$ in (1) (the content of the theorem) and $k + y \in U$ in (3) (needed for $f(k + y)$ to be defined) (Findings, Chapter 3, item 22).
- Only the convexity of $C$ and its nonempty interior are used (normalized form), the quadrant entering through good position (item 23); $\tau$ is $C^j$ on the whole $V_0$ without shrinking (item 24).

### V3.64. Lemma 3.79: the contraction region

*as in the book*

**HWZ (§3.8.5, Lemma 3.79, p. 142).** There are $a, b > 0$ such that on $(B_K(a) \oplus B_Y(b)) \cap C \subseteq U$ the map $B(k, \cdot)$ is a $\tfrac12$-contraction; so $f(k, y) = f(k, y')$ forces $y = y'$.

**Proved in Lean.** In the normalized data: constants $\varepsilon$, $a$, $b$ with $\varepsilon a \le b$, the region $R = \{|k| \le a, |y| \le b\} \cap C \subseteq U$ with $\|DB\| \le \varepsilon/(2(1 + \varepsilon))$ on it; the mean value inequality on $R$; a fixed point $y$ with $(k, y) \in R$ is $\tau(k)$.

- `Polyfold.ContractionData.exists_radii` — Polyfold/Chapter3/QuadrantIFT.lean, line 154
- `Polyfold.Radii.norm_sub_le` — Polyfold/Chapter3/QuadrantIFT.lean, line 263
- `Polyfold.Radii.eq_τ` — Polyfold/Chapter3/QuadrantIFT.lean, line 368

*What differs.*
- As in the text, with the constant $c_0 = \varepsilon/(2(1 + \varepsilon))$.

### V3.65. Lemma 3.80: the fixed point set $X_k$

*hypotheses explicit* · max over $B \cap C$

**HWZ (§3.8.5, Lemma 3.80, p. 143).** Replacing $a$ by a smaller number, $|B(k, y)| \le \varepsilon|k|$ for $|y| \le \varepsilon|k|$, so $B(k, \cdot)$ maps $X_k = \bar B_Y(\varepsilon|k|)$ into itself and has a unique fixed point $\tau(k)$; with $c(a) = (1 + \varepsilon)\max_{B((1+\varepsilon)a)}|DB|$.

**Proved in Lean.** $B(k, \cdot)$ maps $X_k = \{|y| \le \varepsilon|k|\}$ into itself for $k \in V_0 = \{k \in K \cap C : |k| < a\}$, and has a fixed point $\tau(k) \in X_k$ (Banach).

- `Polyfold.Radii.mapsTo_ball` — Polyfold/Chapter3/QuadrantIFT.lean, line 291
- `Polyfold.Radii.exists_fixed` — Polyfold/Chapter3/QuadrantIFT.lean, line 308
- `Polyfold.Radii.τ` — Polyfold/Chapter3/QuadrantIFT.lean, line 332

*What differs.*
- The maximum in $c(a)$ is over $B((1 + \varepsilon)a) \cap C$, where $DB$ is defined *(book 2017: unchanged, Lemma 3.28, p. 126)* (Findings, Chapter 3, item 26).

### V3.66. Lemma 3.81: continuity of $\tau$

*stronger* · constant $\varepsilon/(1+\varepsilon)$ · a missing case distinction

**HWZ (§3.8.5, Lemma 3.81, p. 144).** $\tau : B_K(a) \cap C \to B_Y(b)$ is continuous and satisfies $|\tau(k)| \le \varepsilon|k|/2$ and $|\tau(k) - \tau(k_0)| \le \varepsilon|k - k_0|$.

**Proved in Lean.** $|\tau(k)| \le \varepsilon|k|/2$ and $\tau$ is continuous on $V_0$; for all $k, k_0 \in V_0$, $|\tau(k) - \tau(k_0)| \le \frac{\varepsilon}{1 + \varepsilon}|k - k_0| \le \varepsilon|k - k_0|$, so $\tau$ is $\frac{\varepsilon}{1 + \varepsilon}$-Lipschitz on $V_0$. (An older form with the constant $1 + 2\varepsilon$ is kept for the proofs that use it.)

- `Polyfold.Radii.norm_τ_le` — Polyfold/Chapter3/QuadrantIFT.lean, line 349
- `Polyfold.Radii.norm_τ_sub_le` — Polyfold/Chapter3/QuadrantIFT.lean, line 378
- `Polyfold.Radii.continuousOn_τ` — Polyfold/Chapter3/QuadrantIFT.lean, line 462
- `Polyfold.Radii.norm_τ_sub_le_global` — Polyfold/Chapter3/QuadrantIFT.lean, line 435
- `Polyfold.Radii.norm_τ_sub_le_eps` — Polyfold/Chapter3/QuadrantIFT.lean, line 447
- `Polyfold.Radii.lipschitzOnWith_τ` — Polyfold/Chapter3/QuadrantIFT.lean, line 456
- `Polyfold.Radii.norm_τ_sub_le_of_norm_le` — Polyfold/Chapter3/QuadrantIFT.lean, line 408

*What differs.*
- The text's constant $\varepsilon$ holds on all of $V_0$; its proof omits a case distinction. It uses the point $(k, \tau(k_0))$, which lies in the region of the contraction when $|k_0| \le 2|k|$; otherwise $|k| < 2|k_0|$ and the same argument with $k$ and $k_0$ exchanged applies. Either way $|\tau(k) - \tau(k_0)| \le \tfrac12|\tau(k) - \tau(k_0)| + c_0|k - k_0|$ with $c_0 = \varepsilon/(2(1 + \varepsilon))$, which gives the sharper constant $\varepsilon/(1 + \varepsilon)$ (Findings, Chapter 3, item 216; revises item 25, which had only $1 + 2\varepsilon$). The older estimate is kept for `continuousOn_τ` and Lemma 3.82 (item 217). Formerly narrower; updated in the third addendum of this page.

### V3.67. Lemma 3.82: $\tau$ is of class $C^j$

*stronger* · no shrinking

**HWZ (§3.8.5, Lemma 3.82, p. 144).** If $f$ is of class $C^j$, $j \ge 1$, then $\tau$ is of class $C^j$ on a possibly smaller neighbourhood of $0$, with $D\tau(k) = (1 - D_2B(k, \tau(k)))^{-1}D_1B(k, \tau(k))$.

**Proved in Lean.** $\tau$ is differentiable within $V_0$ with $D\tau(k) = \Phi(k, \tau(k))$, $\Phi = (1 - D_2B)^{-1}D_1B$ of class $C^{j-1}$ on $R$, and $\tau$ is $C^j$ on all of $V_0$.

- `Polyfold.Radii.hasFDerivWithinAt_τ` — Polyfold/Chapter3/QuadrantIFT.lean, line 514
- `Polyfold.Radii.contDiffOn_Φ` — Polyfold/Chapter3/QuadrantIFT.lean, line 560
- `Polyfold.Radii.contDiffOn_τ` — Polyfold/Chapter3/QuadrantIFT.lean, line 578

*What differs.*
- The iteration $f \mapsto f^{(1)}$ is replaced by bootstrapping the derivative formula, with no shrinking (Findings, Chapter 3, item 24). Typos in (72) *(book 2017: unchanged, Lemma 3.30, p. 128)* (item 26).

### V3.68. Theorem 3.19: the implicit function theorem, interior case (first form)

*narrower* · filler (3) nearby: now a theorem · surjective read as good position · $d$ and kernel: V3.97, V3.99 · repaired: tame charts (V3.103) · $f'(x_0)$ sc-Fredholm, onto on all levels

**HWZ (§3.1, Theorem 3.19, p. 74).** Let $X$ be an M-polyfold with $d_X \equiv 0$, $f$ an sc-Fredholm section of a strong bundle and $f(x_0) = 0$. Then $f'(x_0) : T_{x_0}X \to Y_{x_0}$ is sc-Fredholm. If it is surjective, there is an open $U \ni x_0$ such that $S(f, U) = \{y \in U \mid f(y) = 0\}$ is a sub-M-polyfold whose induced structure is that of a smooth manifold of dimension the Fredholm index, $f'(y)$ is surjective at every $y \in S(f, U)$, and $\ker f'(y) = T_yS(f, U)$.

**Proved in Lean.** Let $d_X \equiv 0$, $f$ an sc-Fredholm section with tame germ data (V3.103), $f(x_0) = 0$, and $(f, x_0)$ in good position in a tame chart **with a filler satisfying condition (3) of Definition 3.4 at its zeros near $0$** (`IsGoodPositionGermFilled`, V3.82). Then there are an open $U \ni x_0$ and $d \in \mathbb N$ such that every zero in $U$ is a smooth point with $(f, y)$ in good position in a tame chart, and $S(f, U)$ is a sub-M-polyfold whose induced structure is equivalent to a $d$-dimensional manifold with boundary with corners with degeneracy index $0$ everywhere. First clause: in the chart at $x_0$, $Dg(0)$ and $f'(x_0) = Tf(x_0) : T_0O \to K_0$ are sc-Fredholm operators and $Tf(x_0)$ is onto on every level (Proposition 3.52, V3.46); in every strong bundle chart around $x_0$, $\mathrm{Lin}(z) : T_zO \to K_z$ is sc-Fredholm with the same index on every level (`StrongBundle.linAt_isScFredholm`, V3.96).

- `Polyfold.theorem_3_19` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 209
- `Polyfold.theorem_3_19_linearization` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 186
- `Polyfold.theorem_3_23` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 166
- `Polyfold.lemma_2_26` — Polyfold/Chapter2/SubMPolyfold.lean, line 394
- `Polyfold.MPolyfold.IsWithoutBoundary` — Polyfold/Chapter2/DegeneracyIndex.lean, line 687
- `Polyfold.theorem_3_19_linearization_sc` — Polyfold/Chapter3/FredholmGermLinearizationScG.lean, line 339
- `Polyfold.StrongBundle.linAt_isScFredholm` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 400

*What differs.*
- **The filler condition at the nearby zeros**, through Theorem 3.54 (1) (V3.82), was an added hypothesis when this form was proved; it holds whenever $(f, x_0)$ is in good position (V3.102), and the form with the text's hypotheses is V3.95 (Findings, Chapter 3, items 154, 174, 180).
- The text's hypothesis “$f'(x_0)$ surjective” is read here as good position (Definition 3.53 in the chart form); at $d_X = 0$ the two are the same (V3.100), and the form with “$f'(x_0)$ surjective” is V3.101.
- The dimension $d$ is existentially quantified here; “the dimension agrees with the Fredholm index” is V3.97 and “$\ker f'(y) = T_yS$” in the chart V3.99. The proof is Theorem 3.23 (V3.69) and Lemma 2.26, $d_S \le d_X = 0$. Added after the first edition of this page; updated in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).
- The first clause, “$f'(x_0)$ is sc-Fredholm”, is proved on every level: in the chart at $x_0$ by Propositions 3.10, 1.10 and 3.5 in sc form, and $Tf(x_0)$ is onto on every level because it is onto on level $0$ and regularizing (Findings, Chapter 3, items 235, 236); formerly level $0$ only. Updated in the third addendum of this page. The section-level sc form `theorem_3_19_linearization_sc` takes the text's sc-Fredholm section (germ reading). The clause with no chart singled out: in every strong bundle chart around $x_0$, $\mathrm{Lin}(z) : T_zO \to K_z$ is an sc-Fredholm operator with the same index on every level (`StrongBundle.linAt_isScFredholm`, V3.96); cited here since the fifth addendum of this page.

### V3.69. Theorem 3.23: the implicit function theorem, boundary case

*narrower* · nearby good position assumed · or: filler (3) at nearby zeros · text's hypotheses: V3.95 · repaired: tame charts (V3.103)

**HWZ (§3.1, Theorem 3.23, p. 77).** Let $f$ be an sc-Fredholm section of a tame strong bundle, $f(x) = 0$, $f'(x)$ surjective with kernel in good position to $C_xX$. Then there is an open $U \ni x$ such that $S(f, U)$ consists of smooth points and is a tame sub-M-polyfold of $X$, with a uniquely determined structure of a smooth manifold with boundary with corners, the induced one of Proposition 2.21.

**Proved in Lean.** Let $f$ be an sc-Fredholm section, $f(x) = 0$, $(f, x)$ in good position in a tame chart (V3.103), and let every zero in an open $V_{x_0} \ni x$ be in good position in a tame chart. Then there are an open $U$, $x \in U \subseteq V_{x_0}$, and $d \in \mathbb N$ such that every zero in $U$ is a smooth point and $S(f, U)$ is a sub-M-polyfold whose induced structure (Proposition 2.21) is tame and equivalent to that of a $d$-dimensional manifold with boundary with corners. `theorem_3_23`: the same for tame germ data under `IsGoodPositionGermFilled` at $x$ (V3.82) instead of the nearby good position, and then every zero in $U$ is in good position in a tame chart.

- `Polyfold.theorem_3_23_of_nearby` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 124
- `Polyfold.theorem_3_23` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 166
- `Polyfold.theorem_3_54_two` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 83
- `Polyfold.theorem_3_27` — Polyfold/Chapter3/TangentGerm.lean, line 728
- `Polyfold.MPolyfold.subPolyfold` — Polyfold/Chapter2/SubMPolyfold.lean, line 329
- `Polyfold.MPolyfold.IsManifoldWithCorners` — Polyfold/Chapter3/TangentGerm.lean, line 467

*What differs.*
- Hypotheses of these two forms: the good position of the zeros near $x$ (which is Theorem 3.54 (1), now a theorem, V3.94), or the filler condition at the nearby zeros (V3.82, a consequence of good position, V3.102). The form with the text's hypotheses is V3.95, with the dimension as the Fredholm index V3.97 (Findings, Chapter 3, items 153, 155, 170, 180).
- Tameness of the bundle is read as Definitions 3.50, 3.51, 3.53 read it: germ data and good position in tame charts (V3.103). The dimension $d$ is existentially quantified; the identification $d = \dim\ker f'(x)$ is in the proof. “Uniquely determined” is the equivalence of the atlas of the charts $\pi\varphi$ with the induced one, not stated separately. Added after the first edition of this page; updated in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).

### V3.70. Corollary 3.24: the solution set when every zero is in good position

*hypotheses explicit* · the text's hypotheses · good position in tame charts · $S \ne \emptyset$

**HWZ (§3.1, Corollary 3.24, p. 78).** If at every zero $x$ of the sc-Fredholm section $f$ of a tame strong bundle $f'(x)$ is surjective with kernel in good position to $C_xX$, then the solution set $S = \{f = 0\}$ is a sub-M-polyfold whose induced structure is tame and that of a smooth manifold with boundary with corners.

**Proved in Lean.** Let $f$ be an sc-Fredholm section with $(f, x)$ in good position in a tame chart (V3.103) at every zero $x$, and $S = \{f = 0\} \ne \emptyset$. Then $S$ is a sub-M-polyfold of $X$ whose induced structure is tame and equivalent to a manifold with boundary with corners of locally constant dimension (`IsManifoldWithCornersLoc`, V3.72). The same with good position in the text's sense (sc-complement, V3.47) at every zero, which for an sc-Fredholm section with tame germ data is the same hypothesis (`corollary_3_24_sc`).

- `Polyfold.corollary_3_24` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 257
- `Polyfold.theorem_3_57` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 232
- `Polyfold.MPolyfold.IsManifoldWithCornersLoc` — Polyfold/Chapter3/GlobalIFTTheorems.lean, line 125
- `Polyfold.corollary_3_24_sc` — Polyfold/Chapter3/GoodPositionScG.lean, line 340
- `Polyfold.forall_isGoodPositionGermSc_iff` — Polyfold/Chapter3/GoodPositionScG.lean, line 315

*What differs.*
- **No hypothesis is added** (Findings, Chapter 3, items 156, 157): the global hypothesis, good position at every zero, supplies at every point the nearby good position that the local theorems need. “Tame strong bundle” is read as Definitions 3.50, 3.53 read it, good position in a tame chart (V3.103); $S \ne \emptyset$ is needed by the formal charts (for $S = \emptyset$ the statement is empty). The text names no dimension; the formal one is locally constant (V3.87). Added after the first edition of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).
- Corollary 3.24 with the text's notion of good position is `corollary_3_24_sc`; for an sc-Fredholm section with tame germ data that hypothesis is equivalent to the project's (`forall_isGoodPositionGermSc_iff`; Findings, Chapter 3, item 213). Updated in the third addendum of this page.

### V3.71. Tameness is carried by sc-diffeomorphisms and by open subsets

*not in the book* · used silently by the text

**HWZ (§3.2, proof of Proposition 3.26, p. 80; §3.6, proof of Theorem 3.54, p. 114).** Used without statement: in the proof of Proposition 3.26, “$X' = \psi(X)$ is tame”; in the proof of Theorem 3.54, the chart $\psi \circ \varphi$ onto $\psi(O)$ is a chart of the tame M-polyfold $X$.

**Proved in Lean.** For an sc-diffeomorphism $\psi : U \to U'$ between relatively open subsets of partial quadrants and a tame retraction $r : U \to U$ onto $O$, $\psi \circ r \circ \psi^{-1}$ is a tame retraction of $U'$ onto $\psi(O)$, so $(\psi(O), C', E')$ is a tame retract; on the way $d_{C'} \circ \psi = d_C$, $Dr'(\psi(x)) = D\psi(x)Dr(x)D\psi^{-1}(\psi(x))$, and sc-isomorphisms carry sc-subspaces and sc-splittings. The restriction of a tame retraction to an open subset is tame; an open subset of a tame retract, and the model of a chart restricted to an open set, are tame retracts.

- `Polyfold.IsScDiffeoQuadrant` — Polyfold/Chapter2/TameInvariance.lean, line 156
- `Polyfold.IsScDiffeoQuadrant.transport` — Polyfold/Chapter2/TameInvariance.lean, line 177
- `Polyfold.IsScDiffeoQuadrant.scDeriv_transport` — Polyfold/Chapter2/TameInvariance.lean, line 229
- `Polyfold.IsScSubspace.map` — Polyfold/Chapter2/TameInvariance.lean, line 103
- `Polyfold.IsScSplitting.map` — Polyfold/Chapter2/TameInvariance.lean, line 132
- `Polyfold.IsScDiffeoQuadrant.isTame_transport` — Polyfold/Chapter2/TameInvariance.lean, line 325
- `Polyfold.IsScDiffeoQuadrant.isTameRetract_image` — Polyfold/Chapter2/TameInvariance.lean, line 334
- `Polyfold.ScRetraction.restrict_isTame` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 936
- `Polyfold.IsTameRetract.inter_isOpen` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 956
- `Polyfold.MChart.isTameRetract_image` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 971

*What differs.*
- Condition (1) of Definition 2.34 is Theorem 1.25; condition (2) is transported at the smooth points, where $D\psi(x)$ is an sc-isomorphism, using $D\psi(x)E_x \subseteq E'_{\psi(x)}$ (the one-sided sign argument) (Findings, Chapter 3, items 95, 151). Added after the first edition of this page.

### V3.72. Theorem 3.27 with locally constant dimension

*narrower* · added: `IsRegular` (as V3.24) · dimension may vary

**HWZ (§3.2, Theorem 3.27, p. 81).** Theorem 3.27 for a fixed dimension $n$: a subset with the $n$-dimensional tangent germ property is a sub-M-polyfold whose induced structure is tame and equivalent to an $n$-dimensional manifold with boundary with corners, with the charts $\pi \circ \varphi$.

**Proved in Lean.** If $M \ne \emptyset$ has at every point regular data of Definition 3.25 (`IsRegular`, V3.24) of some dimension, which may depend on the point, then $M$ is a sub-M-polyfold, its induced structure is tame, and the charts $\pi\varphi$ of all these data form an equivalent atlas of charts on relatively open subsets of partial quadrants of finite-dimensional spaces (`IsManifoldWithCornersLoc`); each of them is a chart of the induced structure containing its point.

- `Polyfold.theorem_3_27_loc` — Polyfold/Chapter3/GlobalIFTTheorems.lean, line 217
- `Polyfold.MPolyfold.IsManifoldWithCornersLoc` — Polyfold/Chapter3/GlobalIFTTheorems.lean, line 125
- `Polyfold.MPolyfold.theorem_3_27_loc_isSubMPolyfold` — Polyfold/Chapter3/GlobalIFTTheorems.lean, line 138
- `Polyfold.MPolyfold.theorem_3_27_loc_isTame` — Polyfold/Chapter3/GlobalIFTTheorems.lean, line 194
- `Polyfold.MPolyfold.theorem_3_27_loc_isManifoldWithCornersLoc` — Polyfold/Chapter3/GlobalIFTTheorems.lean, line 203
- `Polyfold.MPolyfold.theorem_3_27_loc_atlas_equiv` — Polyfold/Chapter3/GlobalIFTTheorems.lean, line 186

*What differs.*
- The regularity conditions of V3.24 are hypotheses, as there. The dimension may vary from point to point (the solution set of Theorem 3.57 has locally constant, not constant, dimension; Findings, Chapter 3, item 152); the proof is that of V3.24. Added after the first edition of this page.

### V3.73. The re-centring lemma

*narrower* · $\sigma_1$ $C^1$ on $V_1$ assumed · onto by Sard, not by symmetry · no Theorem 3.72

**HWZ (§3.2, proof of Theorem 3.27, p. 84).** In the proof of Theorem 3.27: $\delta$ is an sc$^\infty$-germ near every $v_0 \in V$. With the data $(\psi, N', Y', V', \tau)$ at $x_0 = \varphi^{-1}(v_0 + \delta(v_0))$, the map $w \mapsto \pi\varphi\psi^{-1}(w + \tau(w))$ has an invertible linearization at $0$, so it is a local diffeomorphism and $\delta$ is regular near $v_0$.

**Proved in Lean.** For two graph descriptions of one set $S$ — in a chart $\chi_1$ the graph of $\sigma_1 : V_1 \to Y_1$ over $K_1$ with $\sigma_1$ of class $C^1$ on all of $V_1$, in a chart $\chi_2$ centred at $y = \chi_1^{-1}(v_0 + \sigma_1(v_0))$ the graph of $\sigma_2$ over $K_2$ with $\sigma_2(0) = 0$, $D\sigma_2(0) = 0$ and $C^k$-lifts into level $k$ near $0$ ($K_i$ finite-dimensional, smooth, in good position, $Y_i$ closed complements) — $\dim K_1 = \dim K_2$, and for all $m$, $k$, $\sigma_1$ is $C^k$ into $E_{1,m}$ on a relatively open neighbourhood of $v_0$.

- `Polyfold.recentre_contDiffOn_levels` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 496
- `Polyfold.finrank_le_of_interior_image_nonempty` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 266
- `Polyfold.exists_contDiffOn_inverse` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 359
- `Polyfold.InvDataW.contDiffOn_inv` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 220
- `Polyfold.scDeriv_apply_toBase_deriv_eq_of_fixed` — Polyfold/Chapter3/GlobalIFTNearbyGraph.lean, line 399

*What differs.*
- The text's step needs $\delta$ differentiable at $v_0$, which fails for general sets (V3.24, first counterexample); here $\sigma_1$ is $C^1$ on $V_1$, which V3.74 arranges by shrinking (Findings, Chapter 3, items 82, 150).
- The linearization of $\beta = \pi_1 \circ \chi_1\chi_2^{-1} \circ (1 + \sigma_2)$ at $0$ is injective by the chain rule for the transition and its inverse on level $1$ and the tangency of the graph to the retract; its surjectivity comes from the dimension count by Sard's lemma in fixed dimension, since the symmetric argument would need $\sigma_1$ differentiable into level $1$ at $v_0$ (item 159). The inverse $\beta^{-1}$ is $C^k$ by Lemma 3.77 with weak hypotheses (V3.90), not by Theorem 3.72, which would need $d_C(x) = d_C(\beta(x))$. Added after the first edition of this page.

### V3.74. Condition (a) of the regularity conditions by re-centring

*narrower* · condition (b) assumed · (a) follows from (b) · dimension locally constant

**HWZ (§3.2, proof of Theorem 3.27, p. 84; §3.6, proof of Theorem 3.54, p. 115).** The proof of Theorem 3.27 shows that $\delta$ is an sc$^\infty$-germ near every point of $V$ (so that the charts $\pi\varphi$ are compatible); the proof of Theorem 3.54 constructs the data at every zero “proceeding as above”.

**Proved in Lean.** Let $D$ be data of Definition 3.25 of dimension $n$ for $M$ at $x$ with $\pi(O) \subseteq C$ (condition (b)), and let every point of $M$ in an open $U \ni x$ have data of Definition 3.25 of some dimension. Then $M$ has at $x$ regular data (`IsRegular`) of dimension $n$ with chart domain in $U$, and every datum of Definition 3.25 at a point of $M$ in that domain has dimension $n$. (The proof shrinks $D$ — same $N$, $Y$, $\delta$ — and applies V3.73 at every point.)

- `Polyfold.MPolyfold.TangentGermChart.exists_isRegular_of_locally` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 1152
- `Polyfold.MPolyfold.TangentGermChart.shrink` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 993
- `Polyfold.MPolyfold.TangentGermChart.exists_shrinkData` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 1053
- `Polyfold.MPolyfold.TangentGermChart.shrink_isRegular` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 1043
- `Polyfold.MPolyfold.TangentGermChart.exists_lift` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 1120

*What differs.*
- Condition (b), $\pi(O) \subseteq C$, is a hypothesis. Read off the statement (not a separate Lean theorem): every point of a set with the tangent germ property has data, so for such a set data satisfying (b) can be shrunk to regular data; condition (a) of V3.24 is then not an independent hypothesis. For the solution set (b) holds by the choice of the good complement (V3.75, V3.77; Findings, Chapter 3, items 151, 152). Added after the first edition of this page.

### V3.75. Good complements whose projection maps the partial quadrant into itself

*not in the book* · repairs “$\Sigma$ relatively open” · a case the obvious choice misses

**HWZ (§3.2, proof of Theorem 3.27, p. 83).** In the proof of Theorem 3.27 the set $\Sigma = \{v + y \in C \mid v \in V, y \in Y\}$ is asserted to be relatively open in $C$; the retraction $t(v + w) = v + \delta(v)$ is defined on it.

**Proved in Lean.** If the finite-dimensional $N$ is in good position to the partial quadrant $C$ of $E$, there is a continuous projection $\pi : E_0 \to N$ with $\pi(C) \subseteq N \cap C$ whose kernel $Y$ is a good complement of $N$; $Y$ is closed and `ProjectsInto C N Y` ($z \in C$, $k \in N$, $z - k \in Y$ imply $k \in C$). The property is carried by continuous linear isomorphisms respecting the cones.

- `Polyfold.ProjectsInto` — Polyfold/Chapter3/GoodComplementProjection.lean, line 79
- `Polyfold.exists_goodComplement_projectsInto` — Polyfold/Chapter3/GoodComplementProjection.lean, line 425
- `Polyfold.exists_proj_goodComplement` — Polyfold/Chapter3/GoodComplementProjection.lean, line 408
- `Polyfold.exists_proj_quadCone` — Polyfold/Chapter3/GoodComplementProjection.lean, line 317
- `Polyfold.exists_coordSet` — Polyfold/Chapter3/GoodComplementProjection.lean, line 230
- `Polyfold.ProjectsInto.mapL` — Polyfold/Chapter3/GoodComplementProjection.lean, line 115

*What differs.*
- The text's claim fails for an arbitrary good complement (V3.24, second counterexample) and holds when $\pi(O) \subseteq C$; for the solution set the complement is chosen so (V3.77). The construction keeps the coordinates of a set $S$ of indices; when no coordinate vanishes at a nonzero point of $N \cap C$ and $N \cap C \ne N$ one coordinate is kept: for $C = [0, \infty)^2$, $N = \mathbb R(1, 1)$ the projection along the good complement $\mathbb R(1, 2)$ maps $(0, 1)$ to $-(1, 1)$ (Findings, Chapter 3, items 130, 131). Added after the first edition of this page.

### V3.76. Corollary 3.39: composition with a given conjugation

*restated* · on the shifted structures · $\Psi$ is an isomorphism · index raise of an iso: proved

**HWZ (§3.4, Corollary 3.39, p. 93).** If the sc-germ $g$ is equivalent by a strong bundle isomorphism $\Phi$ to a basic germ and $s$ is an sc$^+$-germ, there is a strong bundle map $\Psi$ such that $((\Psi \circ \Phi)_*(g + s))^1$ is a basic germ.

**Proved in Lean.** Let $g : U \to F$ be sc-smooth and conjugated to a basic germ $h$ (conjugation data $\Phi$, V3.13, V3.46), and $s : U \to F_1$ sc-smooth into $F^1$ with $s(0) = 0$. With $t = \Phi[1]_*s$ and $h' = h + (t_{\mathbb R^N}, 0)$ there are data of Theorem 3.38 for $t_W$ such that $\Phi_*(g + s) = h + t$ near $0$, $\Gamma = \Lambda \circ \Phi^1$ is a strong bundle isomorphism of the shifted structures $E^1 \triangleleft F^1$ with $\Gamma_* = \Lambda_* \circ \Phi^1_*$, and $(\Gamma(u, (g + s)^1(u)))_2 = (\Lambda_*(h + t))^1(\gamma(u))$ near $0$, a basic germ; so $(g + s)^1$ is conjugated to a basic germ. Also $\Gamma = (\Lambda_0 \circ \Phi)^1$.

- `Polyfold.corollary_3_39` — Polyfold/Chapter3/BasicClassComposition.lean, line 590
- `Polyfold.corollary_3_39_isConjugate` — Polyfold/Chapter3/BasicClassComposition.lean, line 779
- `Polyfold.ConjugationData.compIso_eq_strongShift` — Polyfold/Chapter3/BasicClassComposition.lean, line 558
- `Polyfold.IsStrongBundleIso.shift` — Polyfold/Chapter3/BasicClassComposition.lean, line 265
- `Polyfold.IsStrongBundleIso.comp` — Polyfold/Chapter3/BasicClassComposition.lean, line 356
- `Polyfold.IsStrongBundleIso.pushforward_comp` — Polyfold/Chapter3/BasicClassComposition.lean, line 369
- `Polyfold.StabilityData.linIso_isStrongBundleIso` — Polyfold/Chapter3/BasicClassComposition.lean, line 448
- `Polyfold.ScOperator.isStrongBundleIso_prodMap` — Polyfold/Chapter3/BasicClassComposition.lean, line 132

*What differs.*
- “Sc-germ” is read as sc-smooth on $U$ and the sc$^+$-germ $s$ as an sc-smooth map into $F^1$ on $U$ with $s(0) = 0$; the conclusion is a conjugation of the level-$1$ map $(g + s)^1$ on the shifted structures. The text's “strong bundle map $\Psi$” is an isomorphism (the linear change of Theorem 3.38); the index raise of a strong bundle isomorphism is one (used silently by the text); $\Phi_*(g + s) = h + t$ holds near $0$ only, with the $\mathbb R^N$-component of $t$ absorbed into $h$; the text's $\tau : Z \to C$ is not applied (Findings, Chapter 3, items 121–123). Added after the first edition of this page.

### V3.77. Theorems 3.43, 3.47 and 3.54 (3) with a closed good complement projecting into the quadrant

*stronger* · $Y$ closed · projection maps $C'$ into $C'$

**HWZ (§3.5, Theorem 3.43 and Corollary 3.47, pp. 102, 106; §3.6, proof of Theorem 3.54, p. 114).** Theorem 3.43 and Corollary 3.47 (local solvability) with a good complement $Y$ of the kernel; Theorem 3.54, step (3): the solution set near $x$ is the graph of $\sigma$ over $\ker D(h + t)(0) \cap C'$.

**Proved in Lean.** The conclusions of V3.38, V3.42 and V3.48 hold with a good complement $Y$ that is closed and satisfies `ProjectsInto` for the partial quadrant (V3.75). In Theorem 3.43, $Y = Z \oplus W$ for a good complement $Z$ of $\widetilde K$ chosen by V3.75: every good complement $Z$ of $\widetilde K$ gives the good complement $Z \oplus W$ of $K'$ (constant $\varepsilon/(\|L\| + 1)$) and the data of the proof exist for a prescribed $Z$; in Corollary 3.47 both properties are carried by the linear homeomorphism of Theorem 3.38.

- `Polyfold.theorem_3_43_closed` — Polyfold/Chapter3/LocalSolvabilityClosed.lean, line 48
- `Polyfold.theorem_3_43_proj` — Polyfold/Chapter3/GoodComplementProjection.lean, line 559
- `Polyfold.theorem_3_47_proj` — Polyfold/Chapter3/LocalSolvabilityClosed.lean, line 89
- `Polyfold.theorem_3_47_closed` — Polyfold/Chapter3/LocalSolvabilityClosed.lean, line 298
- `Polyfold.theorem_3_54_graph_proj` — Polyfold/Chapter3/GlobalIFTG.lean, line 229
- `Polyfold.IsGoodComplement.prod_top_graph` — Polyfold/Chapter3/GoodComplementProjection.lean, line 449
- `Polyfold.ProjectsInto.prod_top_graph` — Polyfold/Chapter3/GoodComplementProjection.lean, line 494
- `Polyfold.ShiftedBasicData.exists_sol_of_goodComplement` — Polyfold/Chapter3/GoodComplementProjection.lean, line 516

*What differs.*
- Two additional conclusions. The closedness is the text's (its $Y'$ is an sc-complement) and is needed by Lemma 3.55 and Definition 3.25 at the nearby zeros; the projection property is not in the text and gives condition (b) of Theorem 3.27 for the solution set (V3.84; Findings, Chapter 3, items 93, 132, 133). Added after the first edition of this page.

### V3.78. The linearization at a zero in charts, and its chart independence

*not in the book* · presupposed by the text · at zeros only · transition smooth on $[0]$ only

**HWZ (§3.6, Definition 3.53, p. 111; §2.4, Definition 2.38, p. 42).** Definition 3.53 is stated with $f'(x) : T_xX \to Y_x$ and the partial cone $C_xX$; Definition 2.38 asserts that $T^R_xX$ and $C_xX$ do not depend on the chart (Proposition 2.30). The linearization is defined at the centre of a chart, through a filler.

**Proved in Lean.** In a strong bundle chart, $\mathrm{Lin}(z) = D(\mathbf f \circ r)(z)|_{T_zO}$ at every level-$1$ point $z$ of the retract; at a zero it takes values in $K_z = \rho(z)F$ and equals $Dg(z)$ on $T_zO$ for every $g$ sc$^1$ on $U$ agreeing with $\mathbf f$ near $z$, and for every sc$^1$-germ $g$ agreeing with $\mathbf f$ near $z$ with $z$ in its germ, $Dg(z)$ the value of its derivative family (`linAt_eq_germDeriv`; at a centre: $Tf(0)$ of Proposition 3.5, also for a filling germ). For two strong bundle charts of $P$ and an sc-smooth section, at a zero $y$ with level-$1$ points $z$, $z'$ over $\varphi(y)$, $\varphi'(y)$: isomorphisms $A : T_zO \to T_{z'}O'$, $\Gamma : K_z \to K'_{z'}$ with $\Gamma\,\mathrm{Lin}(z) = \mathrm{Lin}'(z')A$ and $A$ respecting the partial quadrants; so surjectivity, the Fredholm property and index, and the good position of the kernel do not depend on the chart.

- `Polyfold.linAt` — Polyfold/Chapter3/LinearizationCharts.lean, line 531
- `Polyfold.rho_scDeriv_comp_r` — Polyfold/Chapter3/LinearizationCharts.lean, line 551
- `Polyfold.linAt_eq_scDeriv` — Polyfold/Chapter3/LinearizationCharts.lean, line 612
- `Polyfold.IsFilledVersion.fillerRestrict_eq_linAt` — Polyfold/Chapter3/LinearizationCharts.lean, line 644
- `Polyfold.linAt_eq_germDeriv` — Polyfold/Chapter3/LinearizationChartsG.lean, line 130
- `Polyfold.IsFillingGerm.fillerRestrict_eq_linAt` — Polyfold/Chapter3/LinearizationChartsG.lean, line 144
- `Polyfold.linAt_chart_change` — Polyfold/Chapter3/LinearizationCharts.lean, line 891
- `Polyfold.StrongBundle.linAt_chart_independence` — Polyfold/Chapter3/LinearizationCharts.lean, line 1500
- `Polyfold.IsInGoodPositionIn.transport` — Polyfold/Chapter3/LinearizationCharts.lean, line 293
- `Polyfold.scDeriv_fiber_of_vanishing` — Polyfold/Chapter3/LinearizationCharts.lean, line 442

*What differs.*
- The text does not prove the chart independence of $f'(x)$ or of good position; this is its chart form at zeros (what gap G.13 of Chapter 2 leaves open). Only the fibre derivative of the transition survives at a zero, so away from zeros the linearization is not chart independent. Of Definition 2.50 only the sc-smoothness of the transition on $[0]$ is used; level-$1$ points suffice; no tameness (Findings, Chapter 3, items 110–116). Added after the first edition of this page.
- For filling germs (the germ reading of Definition 3.11) $Dg(z)$ is meaningful only for $z$ in the germ; the consumers use it at the centre and at the level-$1$ lifts of nearby zeros, which lie in the germ (Findings, Chapter 3, items 278, 284). Updated after the switch of Definition 3.11 to the text’s germ reading (phase 2).

### V3.79. Definition 3.53 at a zero, from a chart not centred there

*not in the book* · dense range suffices · kernel: $\ker Dg(z) \cap T_zO$

**HWZ (§3.6, proof of Theorem 3.54, p. 115).** In the proof of Theorem 3.54: at every zero $y$ near $x$, $f'(y)$ is surjective with kernel in good position, “so that, proceeding as above”, the construction can be repeated at $y$.

**Proved in Lean.** Let $f$ be an sc-smooth section, $y$ a zero with tame germ data (V3.103), $c$ a strong bundle chart of $P$ around $y$ (not necessarily centred), $z$ a level-$1$ point over $\varphi(y)$, $g$ an sc$^1$-germ on a germ $G$ of $c$ with derivative family $Dg$ and $z \in G_1$, agreeing with $\mathbf f$ on $O$ near $\varphi(y)$. If $\rho(z)k \in Dg(z)(T_zO)$ for every smooth $k$ and $\ker Dg(z) \cap T_zO$ is in good position to $C_{\varphi(y)}$ inside $T_zO$, then $(f, y)$ is in good position in a tame chart (`isGoodPositionGermTame_of_chart_dense`); with all of $K_z$ in the range, for an sc-Fredholm germ, in the chart of Definition 3.11 (`isGoodPositionGerm_of_chart`); the same with the hypotheses on $\mathrm{Lin}(z)$ (`isGoodPositionGerm_of_linAt_surj`).

- `Polyfold.StrongBundle.isGoodPositionGermTame_of_chart_dense` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 122
- `Polyfold.StrongBundle.isGoodPositionGerm_of_chart` — Polyfold/Chapter3/LinearizationChartsG.lean, line 560
- `Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj` — Polyfold/Chapter3/LinearizationChartsG.lean, line 535
- `Polyfold.StrongBundle.isGoodPositionAtGerm_of_chart_dense` — Polyfold/Chapter3/LinearizationChartsG.lean, line 501

*What differs.*
- The hypothesis is on $\ker Dg(z) \cap T_zO$, not on $\ker Dg(z)$: condition (3) of the filler holds at its centre only, so $\ker Dg(z)$ need not lie in $T_zO$. A dense part of $K_z$ in the range suffices because the range of the linearization in the centred chart is closed (Proposition 3.52) (Findings, Chapter 3, items 111, 117). Added after the first edition of this page.
- In the germ reading of Definition 3.11 the point $z$ must lie in the germ of $g$; the dense form needs the closed range in the target chart, which Proposition 3.52 for germs gives in the tame chart of the germ data, so it is stated there. The whole-chart forms are `isGoodPositionGerm_of_chart_dense`, `isGoodPositionGerm_of_linAt` and the `_wholeChart` declarations (Findings, Chapter 3, items 285, 301, 313). Updated after the switch of Definition 3.11 to the text’s germ reading (phase 2).

### V3.80. Theorem 3.54, property (4) in the chart at $x_0$: Corollary 3.41 and Lemma 3.55 on the graph

*narrower* · in the chart at $x_0$ · about $N_v$, not $\ker f'(y)$ · $Y$ closed (as V3.49) · repaired: tame charts (V3.103)

**HWZ (§3.6, proof of Theorem 3.54, property (4), and Lemma 3.55, p. 114).** For every zero $y \in V$, with $\psi\varphi(y) = v + \sigma(v)$, the kernel of $f'(y)$ is in good position and $f'(y)$ is surjective; this follows from Corollary 3.41 and Lemma 3.55.

**Proved in Lean.** In the data of V3.48 (a section, $(f, x_0)$ in good position in a tame chart) there are a presentation $T$ of $C'$ and an open $V_{x,1} \ni x_0$ such that for every zero $y \in V_{x,1}$ with $\psi\varphi(y) = v + \sigma(v)$: $v + \sigma(v)$ lies on level $1$ and $D(h + t)$ there is surjective Fredholm of index $n - N$; $v + \sigma(v) \in C'$; and $Y$ is a good complement of $N_v = \{k + D\sigma(v)k\}$ with respect to $C'_{v + \sigma(v)}$, with $N_v$ in good position. Lemma 3.55 for $\sigma$ on a relatively open $V \subseteq N \cap C$, any presentation of $C$, closed $Y$.

- `Polyfold.theorem_3_54_nearby` — Polyfold/Chapter3/GlobalIFTFullG.lean, line 43
- `Polyfold.lemma_3_55_relOpen` — Polyfold/Chapter3/GlobalIFTFull.lean, line 118
- `Polyfold.StabilityData.exists_surjective_Dfs'_graph` — Polyfold/Chapter3/GlobalIFTFull.lean, line 284
- `Polyfold.coordCLMWith` — Polyfold/Chapter3/GlobalIFTFull.lean, line 85

*What differs.*
- A step of the proof: in the chart at $x_0$ and for the tangent space $N_v$ of the graph; its identification with the kernel at $y$ is V3.81, the passage to Definition 3.53 at $y$ is V3.79, V3.82. Lemma 3.55 is applied to $\sigma$ on a relatively open $V'$, extended to the cone by a bump; that $N_v \cap C_z$ has interior in $N_v$, which Lemma 3.55 does not state, holds once $\|D\sigma(v)\|$ is small (Findings, Chapter 3, items 91, 92). Added after the first edition of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).

### V3.81. Theorem 3.54 (1) at the nearby zeros: the kernel

*narrower* · no added hypothesis · the kernel half of (1) · in the chart at $x_0$ · repaired: tame charts (V3.103)

**HWZ (§3.6, Theorem 3.54 (1), the kernel, pp. 111, 114).** At every zero $y$ near $x$, $\ker f'(y)$ is in good position to the partial cone $C_yX$ (from Corollary 3.41 and Lemma 3.55).

**Proved in Lean.** For a section $f$ of a strong bundle, $f(x_0) = 0$ and $(f, x_0)$ in good position in a tame chart (V3.103): in a tame chart centred at $x_0$ (filling germ $g$ with a derivative family $Dg$, conjugation covering $\psi$, the germ $h + t$ with kernel $K$, graph $\sigma$) there is an open $V_{x,2} \ni x_0$ such that at every zero $y \in V_{x,2}$, $z_0 = \varphi(y)$, whose level-$1$ lift lies in the germ of $g$: $N_v = \ker D(h + t)$ at $v + \sigma(v) = \psi(z_0)$; $\ker Dg(z_0) = D\psi^{-1}(N_v)$; $Dg(z_0)$ is onto; $\ker Dg(z_0) \subseteq T_{z_0}O$; and $\ker Dg(z_0)$ is in good position to $C_{z_0}$ inside $T_{z_0}O$.

- `Polyfold.theorem_3_54_nearby_kernel` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 160
- `Polyfold.theorem_3_54_chart_kernel` — Polyfold/Chapter3/GlobalIFTNearbyKernelG.lean, line 63
- `Polyfold.StabilityData.graphSpace_eq_ker_Dfs'` — Polyfold/Chapter3/GlobalIFTNearbyGraph.lean, line 633
- `Polyfold.IsStrongBundleIso.scDeriv_pushforward_at` — Polyfold/Chapter3/GlobalIFTNearbyGraph.lean, line 266
- `Polyfold.IsStrongBundleIso.ker_scDeriv_eq_map` — Polyfold/Chapter3/GlobalIFTNearbyGraph.lean, line 332
- `Polyfold.scDeriv_mem_partialQuadrantAtWith_iff` — Polyfold/Chapter3/GlobalIFTNearbyGraph.lean, line 365
- `Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le` — Polyfold/Chapter3/GlobalIFTNearbyGraph.lean, line 518
- `Polyfold.IsStrongBundleIso.ker_deriv_eq_map_germ` — Polyfold/Chapter3/GlobalIFTNearbyGraphG.lean, line 112

*What differs.*
- The kernel half of (1), in the chart at $x_0$, with the text's hypotheses. Two steps the text does not mention: $N_v \subseteq \ker D(h + t)$ needs the $C^1$-lift of $\sigma$ into level $1$ (Theorem 3.47 (1)), equality follows from a dimension count; and $\ker Dg(z_0) \subseteq T_{z_0}O$ comes from the tangency of the solution set to $O$, not from the filler, whose condition (3) holds at $0$ only (Findings, Chapter 3, items 101–104). The surjectivity half is V3.93. Added after the first edition of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).
- In the germ reading the level-$1$ lift of $z_0$ lies in the germ of the filling because the basic germ is taken on the points that $\psi^{-1}$ maps into the germs of $g$ and $s$ (Findings, Chapter 3, items 276–278, 295). Updated after the switch of Definition 3.11 to the text’s germ reading (phase 2).

### V3.82. Theorem 3.54 (1) under the filler condition at the nearby zeros (first form)

*narrower* · filler (3) nearby: now a theorem · text's argument incomplete · gap also in the 2017 text · repaired: tame charts (V3.103)

**HWZ (§3.6, Theorem 3.54 (1), p. 111 (proof p. 114)).** At every zero $y$ near $x$, the sc-Fredholm germ $(f, y)$ is in good position: $f'(y)$ is surjective and its kernel is in good position (from Corollary 3.41 and Lemma 3.55).

**Proved in Lean.** Let $f$ be an sc-Fredholm section with tame germ data (V3.103), $f(x_0) = 0$, and $(f, x_0)$ in good position in a tame chart **with a filler $g$ that satisfies condition (3) of Definition 3.4 at its zeros near $0$** (`IsGoodPositionGermFilled`: at every level-$1$ zero $z_1$ of $g$ in $O \cap N$ lying in the germ of $g$, for its derivative family $Dg$, $Dr(z_1)b = 0$ and $\rho(z_1)Dg(z_1)b = Dg(z_1)b$ imply $b = 0$). Then there is an open $V_x \ni x_0$ such that $(f, y)$ is in good position in a tame chart at every zero $y \in V_x$. Step: at a zero $z$ with $Dg(z)$ onto and condition (3) at $z$, $\rho(z)F \subseteq Dg(z)(T_zO)$.

- `Polyfold.theorem_3_54_one` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 396
- `Polyfold.StrongBundle.IsGoodPositionGermFilled` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 343
- `Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGerm` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 366
- `Polyfold.exists_range_deriv_eq_ρ_of_normal_injective_germ` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 68

*What differs.*
- **The hypothesis of this form.** Definition 3.4 imposes condition (3) at $0$ only, and the text's argument does not give the surjectivity of $f'(y)$: in the block form of $Dg(z_0)$ with respect to $T_{z_0}O \oplus \ker Dr(z_0)$ and $K_{z_0} \oplus \ker\rho(z_0)$, $Tf(z_0)$ is onto iff the block $(1 - \rho(z_0))Dg(z_0)|_{\ker Dr(z_0)}$ is injective, i.e. iff the index is locally constant along the solution set; both directions are formalized (V3.102). The same step is in the book's arXiv version (Theorem 3.13 there). The condition at the nearby zeros, added when this form was proved, holds whenever $(f, x_0)$ is in good position (V3.102): the surjectivity is true with Definition 3.4 as stated, by an implicit function theorem at the nearby zero (V3.93), and Theorem 3.54 (1) with the text's hypotheses is V3.94 (Findings, Chapter 3, items 100, 157, 174, 180–189).
- The kernel half needs no added hypothesis (V3.81); the passage to the chart centred at $y$ is V3.79. Added after the first edition of this page; updated in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).

### V3.83. The parameter extension of the proof of Proposition 6.2: obstruction and tilted kernel

*not in the book* · linear algebra only · naive extension fails at corners

**HWZ (no counterpart in Chapter 3 (the perturbation argument of Proposition 6.2)).** Not in Chapter 3. The proof of Proposition 6.2 (index stability) extends the section by finitely many parameters, $F(\lambda, u) = g(u) + \sum\lambda_is_i(u)$, and applies the implicit function theorem to the extended problem.

**Proved in Lean.** (a) For a cone $C \ni 0$ closed under nonnegative scaling, the $V$-components of a good complement of $\mathbb R \times N$ with respect to $\mathbb R \times C$ lie in $C \cap (-C)$, so $\mathbb R \times N$ is in good position only if $N + (C \cap -C) = V$. (b) For $K \cap j(\Lambda) = 0$, $(K + j(\Lambda)) \oplus Y' = \mathbb R^n \oplus W$ with $Y'$ in the lineality space of $\widetilde C \oplus W$ and $K + j(\Lambda)$ meeting its interior, the tilted kernel $\{((\lambda, a), w) \mid (a, w) + j(\lambda) \in K\}$ is in good position to $(\Lambda \times \widetilde C) \oplus W$.

- `Polyfold.mem_lineality_of_goodComplement_prod` — Polyfold/Chapter3/GlobalIFTNearbyPerturb.lean, line 76
- `Polyfold.sup_lineality_eq_top_of_goodComplement_prod` — Polyfold/Chapter3/GlobalIFTNearbyPerturb.lean, line 111
- `Polyfold.extendedKernel` — Polyfold/Chapter3/GlobalIFTNearbyPerturb.lean, line 152
- `Polyfold.isInGoodPosition_extendedKernel` — Polyfold/Chapter3/GlobalIFTNearbyPerturb.lean, line 181

*What differs.*
- Tried for the surjectivity of V3.82 without the added hypothesis. The naive extension is not in good position at a corner unless $K$ surjects onto the boundary coordinates; the tilted kernel is. The rest of the argument is not formalized, and it would give the surjectivity only on a neighbourhood depending on the parameter space $\Lambda$ (Findings, Chapter 3, items 105–107). The surjectivity is proved by another argument, one perturbation direction at a time with the implicit function theorem at the nearby zero (V3.93). Added after the first edition of this page.

### V3.84. Theorem 3.54 (2) at the centre: the data of Definition 3.25 at $x_0$

*narrower* · at $x_0$ only · kernel smooth: proved · $d$ = index: V3.97 · repaired: tame charts (V3.103)

**HWZ (§3.6, proof of Theorem 3.54, p. 115).** Consequently, with $d = \dim\ker f'(x)$, the solution set $S \subseteq V$ has the $d$-dimensional tangent germ property, and Theorem 3.27 applies.

**Proved in Lean.** For a section $f$ of a strong bundle, $f(x_0) = 0$ and $(f, x_0)$ in good position in a tame chart (V3.103): there are an open $V_x \ni x_0$ and $d$ such that $\{y \in V_x \mid f(y) = 0\}$ has at $x_0$ data of Definition 3.25 of dimension $d$ with $\pi(O) \subseteq C$: the chart $\psi \circ \varphi$ onto the tame retract $\psi(O)$, $N = \ker D(h + t)(0)$ (smooth), the closed projecting good complement and $\sigma$ of V3.77; $\sigma$ is an sc$^\infty$-germ because of its lifts.

- `Polyfold.theorem_3_54_tangentGermChart_proj` — Polyfold/Chapter3/GlobalIFTCenterG.lean, line 125
- `Polyfold.theorem_3_54_tangentGermChart` — Polyfold/Chapter3/GlobalIFTCenterG.lean, line 136
- `Polyfold.MChart.compDiffeo` — Polyfold/Chapter3/GlobalIFTCenter.lean, line 89
- `Polyfold.MChart.compDiffeo_isChart` — Polyfold/Chapter3/GlobalIFTCenter.lean, line 136
- `Polyfold.MPolyfold.TangentGermChart.π_mem_of_projectsInto` — Polyfold/Chapter3/GlobalIFTCenter.lean, line 177
- `Polyfold.isScInftyGermAt_of_lifts` — Polyfold/Chapter3/SolutionGermRegularity.lean, line 52
- `Polyfold.StabilityData.ker_Dfs_le_smooth` — Polyfold/Chapter3/SolutionGermRegularity.lean, line 85

*What differs.*
- At $x_0$; the data at the other points are V3.85. The kernel is a smooth subspace (the text takes it so without comment); the model $\psi(O)$ is tame by V3.71; condition (b) of Theorem 3.27 holds by the choice of the complement. The statement quantifies $d$ existentially; the proof takes $d = \dim\ker D(h + t)(0)$, which is the Fredholm index of $f'(x_0)$ (V3.97; Findings, Chapter 3, items 94–96, 130, 170). Added after the first edition of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).

### V3.85. Theorem 3.54 (1)–(2): good position near $x_0$ and the regular tangent germ data

*narrower* · (2) from (1) · (1): text's hypotheses in V3.94 · `IsRegular` proved, not assumed · repaired: tame charts (V3.103)

**HWZ (§3.6, Theorem 3.54 (1), (2), p. 111).** Let $f$ be an sc-Fredholm section of a tame strong bundle, $f(x) = 0$, $(f, x)$ in good position. There is an open $V \ni x$ such that $S = \{y \in V \mid f(y) = 0\}$ satisfies: (1) $(f, y)$ is in good position at every $y \in S$; (2) $S$ is a sub-M-polyfold whose induced structure is equivalent to a smooth manifold with boundary with corners.

**Proved in Lean.** For a section $f$ of a strong bundle, $f(x_0) = 0$, $(f, x_0)$ in good position in a tame chart (V3.103), and every zero in an open $V_{x_0} \ni x_0$ in good position in a tame chart: there are $d$ and regular data (`IsRegular`) of dimension $d$ for $S = \{f = 0\}$ at $x_0$ with chart domain in $V_{x_0}$, and every datum of Definition 3.25 for $S$ at a point of $S$ in that domain has dimension $d$. `theorem_3_54`: for an sc-Fredholm section with tame germ data under `IsGoodPositionGermFilled` (V3.82), an open $V_x \ni x_0$ in which every zero is in good position in a tame chart, and the above with $V_{x_0} = V_x$.

- `Polyfold.theorem_3_54_two` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 83
- `Polyfold.theorem_3_54` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 108
- `Polyfold.theorem_3_54_tangentGermChart_solutionSet` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 58
- `Polyfold.MPolyfold.TangentGermChart.exists_isRegular_of_locally` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 1152

*What differs.*
- (2) is proved from (1), with the nearby good position as a hypothesis; `theorem_3_54` proves (1) under the filler condition of V3.82, which follows from good position (V3.102); Theorem 3.54 with the text's hypotheses is V3.94, with the index V3.98. The manifold structure follows by Theorem 3.27 (V3.69). The regularity conditions of Theorem 3.27, hypotheses for general sets (V3.24), are theorems for the solution set (V3.74, V3.77); the dimension is locally constant (Findings, Chapter 3, items 151–153). Added after the first edition of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).

### V3.86. Theorem 3.56: the global implicit function theorem, $\partial X = \emptyset$

*restated* · the text's hypotheses · surjective = good position: V3.100 · repaired: tame charts (V3.103)

**HWZ (§3.6, Theorem 3.56, p. 115).** If $P : Y \to X$ is a tame strong bundle over an M-polyfold with $\partial X = \emptyset$ and $f$ an sc-Fredholm section with surjective linearization at every point of $S = \{f = 0\}$, then $S$ is a sub-M-polyfold whose induced structure is equivalent to a smooth manifold without boundary.

**Proved in Lean.** Let $d_X \equiv 0$, $f$ an sc-Fredholm section with $(f, x)$ in good position in a tame chart (V3.103) at every zero $x$, and $S \ne \emptyset$. Then $S$ is a sub-M-polyfold whose induced structure is equivalent to a manifold with boundary with corners of locally constant dimension and has degeneracy index $0$ everywhere. The same with good position in the text's sense (sc-complement, V3.47) at every zero, which for an sc-Fredholm section with tame germ data is the same hypothesis (`theorem_3_56_sc`).

- `Polyfold.theorem_3_56` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 272
- `Polyfold.theorem_3_57` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 232
- `Polyfold.lemma_2_26` — Polyfold/Chapter2/SubMPolyfold.lean, line 394
- `Polyfold.theorem_3_56_sc` — Polyfold/Chapter3/GoodPositionScG.lean, line 352

*What differs.*
- The hypothesis “$f'(x)$ surjective” is read as good position, which by the text's Definition 3.53 is surjectivity at points with $d_X(x) = 0$; in the chart form the kernel condition is stated for the chart's partial quadrant, and that it is void at $d_X = 0$ is V3.100; the form with “$f'(x)$ surjective” and the tameness of the induced structure is V3.101 (Findings, Chapter 3, items 154 (a), 156, 173). No other hypothesis is added. The statement keeps the manifold structure and $d_S \equiv 0$; the tameness of the induced structure is in V3.87. Added after the first edition of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).
- Theorem 3.56 with the text's notion of good position is `theorem_3_56_sc`; for an sc-Fredholm section with tame germ data that hypothesis is equivalent to the project's (`forall_isGoodPositionGermSc_iff`; Findings, Chapter 3, item 213). Updated in the third addendum of this page.

### V3.87. Theorem 3.57: the global implicit function theorem, boundary case

*stronger* · the text's hypotheses · dimension locally constant · parts $S_n$ of fixed dimension · repaired: tame charts (V3.103)

**HWZ (§3.6, Theorem 3.57, p. 115).** If $P : Y \to X$ is a tame strong bundle and $f$ an sc-Fredholm section such that at every $x \in S = \{f = 0\}$ the linearization is surjective with kernel in good position to $C_xX$, then $S$ is a sub-M-polyfold whose induced structure is tame and equivalent to a smooth manifold with boundary with corners.

**Proved in Lean.** Let $f$ be an sc-Fredholm section with $(f, x)$ in good position in a tame chart (V3.103) at every zero $x$. If $S \ne \emptyset$, $S$ is a sub-M-polyfold, its induced structure is tame and equivalent to a manifold with boundary with corners of locally constant dimension, and at every $x \in S$ there are regular data of Definition 3.25 of a dimension $d(x)$ shared by every datum at the points of $S$ in their chart domain. Moreover $S$ is the disjoint union of the parts $S_n$ of dimension $n$, each open and closed in $S$, and each nonempty $S_n$ is a sub-M-polyfold with tame induced structure equivalent to an $n$-dimensional manifold with boundary with corners. The same with good position in the text's sense (sc-complement, V3.47) at every zero, which for an sc-Fredholm section with tame germ data is the same hypothesis (`theorem_3_57_sc`).

- `Polyfold.theorem_3_57` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 232
- `Polyfold.theorem_3_57_dim` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 291
- `Polyfold.solutionSetDim` — Polyfold/Chapter3/GlobalIFTTheorems.lean, line 491
- `Polyfold.theorem_3_27_loc` — Polyfold/Chapter3/GlobalIFTTheorems.lean, line 217
- `Polyfold.theorem_3_57_sc` — Polyfold/Chapter3/GoodPositionScG.lean, line 325

*What differs.*
- **No hypothesis is added**: good position at every zero supplies the nearby good position at every point, so the gap of Theorem 3.54 (1) does not enter. Two steps of the text's proof are replaced: the regularity of the solution germ away from the centre (re-centring, V3.73, V3.74) and the relative openness of $\Sigma$ (choice of the complement, V3.75, V3.77). “Tame strong bundle” is read as good position in tame charts (V3.103); $S \ne \emptyset$ for the formal charts. The text names no dimension; the formal statement adds its local constancy and the parts $S_n$ (Findings, Chapter 3, items 152, 156, 157). The dimension is the Fredholm index at the zeros near each point (V3.97). Added after the first edition of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).
- Theorem 3.57 with the text's notion of good position is `theorem_3_57_sc`; for an sc-Fredholm section with tame germ data that hypothesis is equivalent to the project's (`forall_isGoodPositionGermSc_iff`; Findings, Chapter 3, item 213). Updated in the third addendum of this page.

### V3.88. Theorem 3.58, given the family of sc-isomorphisms

*restated* · in the coordinates of the proof · mean value bound in $X_m$

**HWZ (§3.7, proof of Theorem 3.58, pp. 118–120).** Second half of the proof of Theorem 3.58: with $L(b) = P_Y \circ Df(b)|_X$ sc-isomorphisms with uniform lower bounds (Lemmas 3.59–3.61), the strong bundle isomorphism $\Phi((b, x), (c, y)) = ((b, x), (c, L(b)^{-1}y))$ makes $\Phi_*(f - f(0))$ a basic germ, the contraction estimate coming from condition (3).

**Proved in Lean.** In coordinates $E = \mathbb R^n \oplus X$, $C = \widetilde C \oplus X$, $F = \mathbb R^N \oplus Y$: for $f$ sc-smooth on $U$, an open $V_o \ni 0$ with $(b, 0) \in U$ for $b \in V_o \cap \widetilde C$, sc-isomorphisms $L(b)$ with $L(b)h = (Df(b, 0)(0, h))_Y$ and lower bounds $c_m$ on $V_o \cap \widetilde C$, and condition (3) (`DerivCondition`): on $U' = U \cap (V_o \oplus X)$ the push-forward $k = \Phi_*(f - f(0))$ is a basic germ with contraction $H(b, x) = x - L(b)^{-1}(f(b, x) - f(0))_Y$, $\Phi$ is a strong bundle isomorphism covering the identity, and $f - f(0)$ is conjugated to a basic germ.

- `Polyfold.theorem_3_58_of_family` — Polyfold/Chapter3/BasicGermCriterionProof.lean, line 649
- `Polyfold.DerivCondition` — Polyfold/Chapter3/BasicGermCriterionProof.lean, line 123
- `Polyfold.contrMap358_contraction` — Polyfold/Chapter3/BasicGermCriterionProof.lean, line 207
- `Polyfold.norm_sub_sub_le_of_hasFDerivWithinAt_segment` — Polyfold/Chapter3/BasicGermCriterionProof.lean, line 73
- `Polyfold.fiberIsoMap_isStrongBundleIso` — Polyfold/Chapter3/BasicGermCriterionProof.lean, line 533
- `Polyfold.famInv_isScSmooth_of` — Polyfold/Chapter3/BasicGermCriterionProof.lean, line 594

*What differs.*
- In the coordinates of the text's proof. The contraction estimate uses the mean value inequality along a segment with the derivative bound in the weaker norm of $X_m$ (the text's integral formula), first for $x, x' \in X_{m+1}$, then by density; the sc-smoothness of $(b, y) \mapsto L(b)^{-1}y$ is Lemma 3.61 in set form (Findings, Chapter 3, item 73). Added after the first edition of this page.

### V3.89. Theorem 3.58: the basic germ criterion

*narrower* · in the coordinates of the proof · (1) only at the points $(b, 0)$ · smallness in (2) uniform in $m$

**HWZ (§3.7, Theorem 3.58, p. 116 (proof pp. 116–120)).** Under (1) $Df(x)$ sc-Fredholm of constant index at smooth points, (2) a splitting $E = B \oplus X$ with $B \supseteq \ker Df(0)$, $Y = Df(0)X$ and a compactness condition, (3) a uniform estimate on $D_2f$: $f - f(0)$ is conjugated near $0$ to a basic germ.

**Proved in Lean.** In coordinates $E = \mathbb R^n \oplus X$, $C = \widetilde C \oplus X$, $F = \mathbb R^N \oplus Y$: let $f$ be sc-smooth on $U$ with (1) $Df(b, 0)$ sc-Fredholm with the sc-index of $Df(0)$ at every $(b, 0) \in U$, $b \in \widetilde C$; (2) $h \mapsto (Df(0)(0, h))_Y$ bijective on level $0$ and `CompactnessCondition`; (3) `DerivCondition`. Then there are an open $V_o \ni 0$ and sc-isomorphisms $L(b) = P_Y Df(b, 0)|_X$ for $b \in V_o \cap \widetilde C$ with the conclusions of V3.88: $f - f(0)$ is conjugated to a basic germ.

- `Polyfold.theorem_3_58` — Polyfold/Chapter3/BasicGermCriterionIndex.lean, line 417
- `Polyfold.CompactnessCondition` — Polyfold/Chapter3/BasicGermCriterionIndex.lean, line 310
- `Polyfold.familyCompactness_derivFamOp` — Polyfold/Chapter3/BasicGermCriterionIndex.lean, line 324
- `Polyfold.fredholmIndex_block` — Polyfold/Chapter3/BasicGermCriterionIndex.lean, line 139
- `Polyfold.surjective_of_fredholmIndex_block` — Polyfold/Chapter3/BasicGermCriterionIndex.lean, line 178
- `Polyfold.derivFamOp` — Polyfold/Chapter3/BasicGermCriterionIndex.lean, line 266
- `Polyfold.lemma_3_59` — Polyfold/Chapter3/BasicGermCriterion.lean, line 49
- `Polyfold.lemma_3_60` — Polyfold/Chapter3/BasicGermCriterion.lean, line 93

*What differs.*
- Proved in the coordinates of the text's proof; the reduction of a general sc-splitting $E = B \oplus X$, $F = A \oplus Y$ to them is not formalized. Condition (1) is used only at the points $(b, 0)$ (weaker than the text's); “$B \supseteq \ker Df(0)$, $Y = Df(0)X$” is replaced by the bijectivity it implies; the smallness of $b$ in the compactness condition is read as uniform in the level. The text's “injective sc-Fredholm of index $0$, hence an sc-isomorphism” is the block index formula $\mathrm{ind}\,T = \dim\mathbb R^n + \mathrm{ind}\,L - \dim\mathbb R^N$ on every level; Lemmas 3.59, 3.60 are applied with their hypotheses derived from (2) (Findings, Chapter 3, item 73). Added after the first edition of this page.

### V3.90. Proposition 3.73 and Lemma 3.77 with the hypotheses their proofs use

*restated* · no partial quadrant · image: unique differentiability

**HWZ (§3.8.4, Proposition 3.73 and Lemma 3.77, pp. 137, 140).** For $U$ relatively open and convex in a partial quadrant $C \subseteq \mathbb R^n$, $f : U \to C$ smooth with $\|Df - 1\| \le \tfrac12$, $f(0) = 0$ and $d_C(x) = d_C(f(x))$: $f(U)$ is relatively open and $f : U \to f(U)$ is a smooth diffeomorphism (Lemma 3.77: the inverse is differentiable with $Dg = [Df \circ g]^{-1}$).

**Proved in Lean.** For $U$ convex in a finite-dimensional $V$ with unique differentiability, $f$ of class $C^j$ ($j \ge 1$) on $U$ with $\|Df(x) - 1\| \le \tfrac12$, and $f(U)$ with unique differentiability: $f$ is injective on $U$, its inverse is differentiable within $f(U)$ with $Dg(y) = [Df(g(y))]^{-1}$, and of class $C^j$ on $f(U)$.

- `Polyfold.InvDataW` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 103
- `Polyfold.InvDataW.injOn` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 141
- `Polyfold.InvDataW.hasFDerivWithinAt_inv` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 182
- `Polyfold.InvDataW.contDiffOn_inv` — Polyfold/Chapter3/SolutionGermRecentre.lean, line 220

*What differs.*
- The partial quadrant is not used; the condition on the degeneracy index (in V3.59: interior points to interior points) is replaced by the unique differentiability of $f(U)$, which is what the bootstrapping uses; the relative openness of $f(U)$ is not concluded. Needed for the re-centring (V3.73), where $f(U)$ is relatively open in a cone for another reason (Findings, Chapter 3, item 158). Added after the first edition of this page.

### V3.91. Theorem 3.18: parametrized perturbations

*stronger* · no tameness · “readily verified”: proved · translation charts of $\mathbb R^n$

**HWZ (§3.1, Theorem 3.18, p. 74).** Let $P : Y \to X$ be a tame strong bundle and $f$ an sc-Fredholm section. If $s_1, \dots, s_n \in \Gamma^+(P)$, then $(r, x) \mapsto f(x) + \sum_i r_is_i(x)$ defines an sc-Fredholm section of the pull-back bundle $\pi^*(P) : \pi^*Y \to \mathbb R^n \times X$.

**Proved in Lean.** For any strong bundle $P : Y \to X$, an sc-Fredholm section $f$ and sc$^+$-sections $s_1, \dots, s_n$: with $\mathbb R^n$ the M-polyfold with the constant sc-structure and the translation charts, $\pi(r, x) = x$, and $\pi^*P$ the pull-back strong bundle with the natural structure of Proposition 2.54, $F(r, x) = f(x) + \sum_i r_is_i(x)$ (computed in $P^{-1}(x)$) is an sc-Fredholm section of $\pi^*P$. The paracompactness of $\mathbb R^n \times X$ and $\pi^*Y$ is supplied by Theorem 2.16 (`theorem_3_18'`). On the way: $\tilde f = f \circ \pi$ is sc-Fredholm (product chart, the $\mathbb R^n$-extension of the basic germ), $\tilde s$ is sc$^+$ (scalar product rule), $F = \tilde f + \tilde s$, Theorem 3.15; $\mathbb R^n \times X$ is tame when $X$ is.

- `Polyfold.theorem_3_18` — Polyfold/Chapter3/ParamPerturbationG.lean, line 141
- `Polyfold.theorem_3_18'` — Polyfold/Chapter3/ParamPerturbationG.lean, line 152
- `Polyfold.paramSection` — Polyfold/Chapter3/ParamPerturbation.lean, line 746
- `Polyfold.paramSection_eq_sectionAdd` — Polyfold/Chapter3/ParamPerturbation.lean, line 766
- `Polyfold.StrongBundle.pullback` — Polyfold/Chapter3/ParamPerturbation.lean, line 599
- `Polyfold.StrongBundle.IsScFredholmSection.param` — Polyfold/Chapter3/ParamPerturbationG.lean, line 124
- `Polyfold.StrongBundle.isScPlusSection_paramComb` — Polyfold/Chapter3/ParamPerturbation.lean, line 822
- `Polyfold.IsBasicGerm.paramExtend` — Polyfold/Chapter3/ParamPerturbation.lean, line 505
- `Polyfold.IsConjugateToBasicGerm.paramExtend` — Polyfold/Chapter3/ParamPerturbation.lean, line 543
- `Polyfold.IsStrongBundleIso.paramMap` — Polyfold/Chapter3/ParamPerturbation.lean, line 411
- `Polyfold.prod_rn_isTame` — Polyfold/Chapter3/ParamPerturbation.lean, line 267
- `Polyfold.isScSmooth_smul` — Polyfold/Chapter3/ParamPerturbation.lean, line 280

*What differs.*
- Tameness is not used, as for Theorem 3.15; $\pi^*P$ is tame when $P$ is. The text's “readily verified” needs objects it does not construct: $\mathbb R^n$ as an M-polyfold with charts centred at every $r_0$, the product chart pulled back to $\pi^*Y$, the filler conditions for $(a, u) \mapsto g(u)$, and the $\mathbb R^n$-extension of the basic germ; that $\tilde s$ is sc$^+$ needs the product rule with a scalar factor, which Chapter 1 does not state (Findings, Chapter 3, items 160–164, 167). Added in the second addendum of this page.

### V3.92. The linearization of the parametrized section

*restated* · chart form · at $(r_0, x)$: $f + \sum r_{0,i}s_i$

**HWZ (§3.1, after Theorem 3.19, p. 75).** The linearization of $\tilde f(r, x) = f(x) + \sum_i r_is_i(x)$ at $(0, x_0)$ is $(h, u) \mapsto f'(x_0)u + \sum_i h_ie_i$, $e_i = s_i(x_0)$.

**Proved in Lean.** In the product chart $(r \mapsto r - r_0) \times c$ of $\pi^*P$, $c$ a strong bundle chart of $P$ with $0$ in its retract, at the centre: $D(\hat F \circ (1 \times r))(0)(\delta a, \delta u) = D(\hat G \circ r)(0)\delta u + \sum_i\delta a_i\hat s_i(0)$, $\hat G = \hat f + \sum_i r_{0,i}\hat s_i$; in the chart form of the linearization, $\mathrm{Lin}_F(0)(\delta a, \delta u) = \mathrm{Lin}_{f + \sum r_{0,i}s_i}(0)\delta u + \sum_i\delta a_i\hat s_i(0)$, and at $r_0 = 0$, $\mathrm{Lin}_F(0)(\delta r, \xi) = \mathrm{Lin}_f(0)\xi + \sum_i\delta r_i\hat s_i(0)$.

- `Polyfold.linAt_paramSection_zero` — Polyfold/Chapter3/ParamPerturbationG.lean, line 396
- `Polyfold.linAt_paramSection` — Polyfold/Chapter3/ParamPerturbationG.lean, line 374
- `Polyfold.scDeriv_paramSection` — Polyfold/Chapter3/ParamPerturbationG.lean, line 358
- `Polyfold.PullbackChartData.ofProd` — Polyfold/Chapter3/ParamPerturbation.lean, line 887
- `Polyfold.PullbackChartData.ofProd_mem_tangent` — Polyfold/Chapter3/ParamPerturbation.lean, line 1413

*What differs.*
- Stated in the chart form of the linearization (Definition 3.53 is formalized in charts). At $(r_0, x)$ with $r_0 \ne 0$ the first term is the linearization of $f + \sum r_{0,i}s_i$, not $f'(x)$; the formula does not use $F(r_0, x) = 0$. The text's “sc$^1$-sections $s_i$” must be sc$^+$ for Theorem 3.18 (Findings, Chapter 3, items 165, 166). Added in the second addendum of this page.

### V3.93. Theorem 3.54 (1): the surjectivity at the nearby zeros, in the chart at $x_0$

*not in the book* · a new argument · $N_4$ independent of $k$ · no added hypothesis

**HWZ (§3.6, proof of Theorem 3.54, property (4), p. 114).** For every zero $y$ near $x$ the linearization $f'(y)$ is surjective; “property (4) follows from Corollary 3.41 and from Lemma 3.55”.

**Proved in Lean.** In the data of V3.48 at a zero $x_0$ in good position (chart centred at $x_0$, filling germ $g$, conjugation $\Psi$ covering $\psi$, $h' + \iota t$ with kernel $K \ne 0$, the graph $\sigma$ over $V'$, an open $N_2 \ni 0$ on which $\psi$ maps the zeros of $g$ in $O$ onto the graph), with condition (2) of Definition 3.4 on $N_2$: there is an open $N_4 \subseteq N_2$ containing $0$ such that for every zero $z_0 \in O \cap N_4$ of $g$ and every smooth $k$, $\rho(z_0)k = Dg(z_0)x$ for some $x \in T_{z_0}O$. The curve $u(\mu)$ of zeros of $g + \mu\rho(r(\cdot))k$ through $z_0$ lies in $O$ (condition (2)) and in the germ of $g$; it comes from Theorem 3.30 at the centre for the $k$-extended contraction germ of the normal form of Theorem 3.38, whose regions in $a$ do not depend on $k$, and from a one-sided finite-dimensional implicit function theorem at $\theta(z_0)$ along an inward direction given by good position.

- `Polyfold.theorem_3_54_chart_onto` — Polyfold/Chapter3/GlobalIFTNearbyOntoG.lean, line 60
- `Polyfold.StrongRetr.mem_O_of_perturbed_zero` — Polyfold/Chapter3/GlobalIFTNearbyOntoLemmas.lean, line 610
- `Polyfold.exists_inward_of_isInGoodPosition` — Polyfold/Chapter3/GlobalIFTNearbyOntoLemmas.lean, line 84
- `Polyfold.inward_add_smul` — Polyfold/Chapter3/GlobalIFTNearbyOntoLemmas.lean, line 243
- `Polyfold.exists_curve_of_inward` — Polyfold/Chapter3/GlobalIFTNearbyOntoLemmas.lean, line 305
- `Polyfold.hasDerivWithinAt_smul_right_of_continuousWithinAt` — Polyfold/Chapter3/GlobalIFTNearbyOntoLemmas.lean, line 577
- `Polyfold.ShiftedBasicData.exists_radii` — Polyfold/Chapter3/GlobalIFTNearbyOntoGerm.lean, line 214
- `Polyfold.ShiftedBasicData.perturbContraction` — Polyfold/Chapter3/GlobalIFTNearbyOntoGerm.lean, line 474
- `Polyfold.ShiftedBasicData.perturbContraction_isSc1GermWith` — Polyfold/Chapter3/GlobalIFTNearbyOntoGerm.lean, line 594
- `Polyfold.xiMap` — Polyfold/Chapter3/GlobalIFTNearbyOntoXi.lean, line 81
- `Polyfold.exists_xi_radii_bounds` — Polyfold/Chapter3/GlobalIFTNearbyOntoXi.lean, line 412
- `Polyfold.ShiftedBasicData.surjective_DH_and_ker_eq` — Polyfold/Chapter3/GlobalIFTNearbyOntoCurve.lean, line 339
- `Polyfold.ShiftedBasicData.exists_perturbed_curve` — Polyfold/Chapter3/GlobalIFTNearbyOntoCurve.lean, line 380

*What differs.*
- Not the text's argument, which gives the surjectivity of the filled $Dg(z_0)$ only (V3.82). The perturbation argument of the text's Proposition 6.2 applies the implicit function theorem at $x_0$ to a problem depending on the perturbation, with a neighbourhood depending on it (V3.83); here the finite-dimensional implicit function theorem is applied at the nearby zero, and Theorem 3.30 at the centre to a germ whose $a$-regions are $k$-independent, so $N_4$ is determined by $g$, $r$, $\rho$, $\Psi$ and the normal form. The surjectivity of $D_aH$ at the nearby zero comes from a dimension count on level $0$, not from eliminating the $W$-block; Corollary 3.39 is not used (Findings, Chapter 3, items 180–187). Added in the second addendum of this page.
- In the germ reading the curve lies in the germ of the filling: its points come from the germ of the basic germ taken on the points that $\psi^{-1}$ maps into the germs of $g$ and $s$, so $g$ is differentiated within its germ (Findings, Chapter 3, items 276–278, 298). Updated after the switch of Definition 3.11 to the text’s germ reading (phase 2).

### V3.94. Theorem 3.54 (1)–(2) with the text's hypotheses

*restated* · the text's hypotheses · (2) as regular data · proof of (1): V3.93 · repaired: tame charts (V3.103) · conclusion with the sc-complement

**HWZ (§3.6, Theorem 3.54 (1), (2), p. 111).** Let $f$ be an sc-Fredholm section of a tame strong bundle, $f(x) = 0$, $(f, x)$ in good position. There is an open $V \ni x$ such that $S = \{y \in V \mid f(y) = 0\}$ satisfies: (1) $(f, y)$ is in good position at every $y \in S$; (2) $S$ is a sub-M-polyfold whose induced structure is equivalent to a smooth manifold with boundary with corners.

**Proved in Lean.** For an sc-Fredholm section with tame germ data (V3.103), $f(x_0) = 0$, $(f, x_0)$ in good position in a tame chart: an open $V_x \ni x_0$ such that $(f, y)$ is in good position in a tame chart at every zero $y \in V_x$ (`theorem_3_54_one'`), and $d$ with regular data of Definition 3.25 of dimension $d$ for $S$ at $x_0$ with chart domain in $V_x$, every datum at a point of $S$ in that domain having dimension $d$ (`theorem_3_54'`). With the text's notion of good position (sc-complement, V3.47) in the conclusion, from either form at $x_0$: every zero $y \in V_x$ is in good position with an sc-complement (`theorem_3_54_one_sc_of_tame`, `theorem_3_54_one_sc`; with (2), `theorem_3_54_sc`).

- `Polyfold.theorem_3_54_one'` — Polyfold/Chapter3/GlobalIFTNearbyOntoG.lean, line 508
- `Polyfold.theorem_3_54'` — Polyfold/Chapter3/GlobalIFTNearbyOntoG.lean, line 615
- `Polyfold.StrongBundle.isGoodPositionGermTame_of_chart_dense` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 122
- `Polyfold.theorem_3_54_two` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 83
- `Polyfold.StrongBundle.IsGoodPositionGerm.toTame` — Polyfold/Chapter3/TameGermsAddG.lean, line 69
- `Polyfold.theorem_3_54_one_sc_of_tame` — Polyfold/Chapter3/GoodPositionScG.lean, line 262
- `Polyfold.theorem_3_54_one_sc` — Polyfold/Chapter3/GoodPositionScG.lean, line 274
- `Polyfold.theorem_3_54_sc` — Polyfold/Chapter3/GoodPositionScG.lean, line 285

*What differs.*
- **No hypothesis is added.** (2) is stated as regular tangent germ data with locally constant dimension, from which Theorem 3.27 gives the manifold structure of the local solution set (V3.95). The surjectivity in (1) is V3.93, carried to the chart centred at $y$ through V3.79 and read in the tame chart of the germ data at $y$ (V3.107); the kernel half is V3.81; for $\dim K = 0$ the only zero near $x_0$ is $x_0$. The text's statement is true, its proof incomplete; the same holds for the book's arXiv version (Findings, Chapter 3, items 157, 180, 189). Added in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).
- The project's good position asks only for an algebraic good complement (V3.20), which as a conclusion is less than the text's; the sc form of (1) follows at each zero by the upgrade of V3.47, with no hypothesis added (Findings, Chapter 3, items 210, 213). The case distinction $d_X(x) \ge 1$ of Definition 3.53 (2) is not made, which makes hypothesis and conclusion stronger (item 214). Updated in the third addendum of this page.

### V3.95. Theorems 3.23 and 3.19 with the text's hypotheses

*hypotheses explicit* · the text's hypotheses · index: V3.97; kernel: V3.99 · repaired: tame charts (V3.103)

**HWZ (§3.1, Theorems 3.19, 3.23, pp. 74, 77).** (3.23) For an sc-Fredholm section of a tame strong bundle and a zero $x$ with $f'(x)$ onto and kernel in good position to $C_xX$, there is an open $U \ni x$ such that $S(f, U)$ consists of smooth points and is a tame sub-M-polyfold with a uniquely determined structure of a manifold with boundary with corners. (3.19) For $d_X \equiv 0$ and $f'(x_0)$ onto, $S(f, U)$ is a smooth manifold.

**Proved in Lean.** For an sc-Fredholm section with tame germ data (V3.103), $f(x) = 0$, $(f, x)$ in good position in a tame chart: an open $U \ni x$ and $d$ such that every zero in $U$ is in good position in a tame chart and a smooth point, and $S(f, U)$ is a sub-M-polyfold with tame induced structure equivalent to a $d$-dimensional manifold with boundary with corners (`theorem_3_23'`); if $d_X \equiv 0$, with degeneracy index $0$ everywhere (`theorem_3_19'`). Theorem 3.23 with the text's notion of good position (sc-complement, V3.47) at $x$ and, in the conclusion, at every zero in $U$: `theorem_3_23_sc`.

- `Polyfold.theorem_3_23'` — Polyfold/Chapter3/GlobalIFTNearbyOntoG.lean, line 631
- `Polyfold.theorem_3_19'` — Polyfold/Chapter3/GlobalIFTNearbyOntoG.lean, line 650
- `Polyfold.theorem_3_23_of_nearby` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 124
- `Polyfold.lemma_2_26` — Polyfold/Chapter2/SubMPolyfold.lean, line 394
- `Polyfold.theorem_3_23_sc` — Polyfold/Chapter3/GoodPositionScG.lean, line 299

*What differs.*
- No hypothesis is added; “tame strong bundle” is read as Definitions 3.50, 3.51, 3.53 read it, germ data and good position in tame charts (V3.103). For Theorem 3.19 “$f'(x_0)$ surjective” is read as good position, the same at $d_X = 0$ (V3.100, V3.101). The dimension as the Fredholm index is V3.97, $\ker f'(y) = T_yS$ in the chart V3.99; “uniquely determined” is the equivalence of atlases. Added in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).
- The form of Theorem 3.23 with the text's good complement in hypothesis and conclusion is `theorem_3_23_sc` (Findings, Chapter 3, item 213). Updated in the third addendum of this page.

### V3.96. The index of the linearization at a zero, in every chart

*stronger* · sc-Fredholm on every level, in charts · every chart, at every zero

**HWZ (§3.6, Proposition 3.52, p. 110; Theorem 3.19, p. 74).** If $f$ is an sc-Fredholm section and $f(x) = 0$, then $Tf(x) : T_xX \to Y_x$ is an sc-Fredholm operator (Proposition 3.52); “the linearization $f'(x_0)$ is a sc-Fredholm operator” (Theorem 3.19).

**Proved in Lean.** `IsSurjLinOfIndex f y d`: in every strong bundle chart around $y$, at the level-$1$ point over $\varphi(y)$, $\mathrm{Lin}(z) : T_zO \to K_z$ is onto, Fredholm, $\mathrm{ind} = \dim\ker = d$. For an sc-smooth section and the chart of Definition 3.11 at a zero $x_0$ with conjugation data of $g - s$ to a basic germ $O(\widetilde C \oplus W, 0) \to \mathbb R^N \oplus W$, $\widetilde C \subseteq \mathbb R^n$: in every chart around $x_0$ the linearization is Fredholm of index $n - N$, onto if the germ is in good position; so `IsSurjLinOfIndex f x_0 (n − N)` at a zero in good position. For an sc-Fredholm section in good position, in the chart of Definition 3.53: $\mathrm{ind}\,Dg(0) = \mathrm{ind}\,Tf(x_0) = \dim\ker Tf(x_0) = n - N$ for every conjugation. In sc form: for an sc-Fredholm section, a zero $y$ and **any** strong bundle chart around $y$, at the level-$1$ point $z$ over $\varphi(y)$ (a smooth point), $T_zO = Dr(z)E$ and $K_z = \rho(z)F$ are sc-subspaces and $\mathrm{Lin}(z) : T_zO \to K_z$ is an sc-Fredholm operator, Fredholm on every level of the index $n - N$ of every conjugation of every germ datum at $y$; under `IsSurjLinOfIndex f y d` it is onto on every level, of index $d$ on every level. In the chart of Definition 3.53 at a zero in good position, $Dg(0)$ and $f'(x_0) = Tf(x_0)$ are sc-Fredholm and $Tf(x_0)$ is onto on every level.

- `Polyfold.StrongBundle.IsSurjLinOfIndex` — Polyfold/Chapter3/GlobalIFTIndex.lean, line 239
- `Polyfold.StrongBundle.linAt_index_of_conjugationData` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 160
- `Polyfold.StrongBundle.isSurjLinOfIndex_of_conjugationData` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 220
- `Polyfold.StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 246
- `Polyfold.theorem_3_19_linearization_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 371
- `Polyfold.finrank_ker_eq_fredholmIndex_of_surjective` — Polyfold/Chapter3/GlobalIFT.lean, line 162
- `Polyfold.StrongBundle.linAt_isScFredholm` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 400
- `Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 461
- `Polyfold.proposition_3_52_sc` — Polyfold/Chapter3/FredholmGermLinearizationScG.lean, line 292
- `Polyfold.theorem_3_19_linearization_sc` — Polyfold/Chapter3/FredholmGermLinearizationScG.lean, line 339

*What differs.*
- Proved in sc form, in every chart: the level-$0$ conjugation between the linearizations in two charts (V3.78) is realised by bounded operators on the ambient spaces that preserve the levels at smooth points (derivatives of the sc-smooth transition maps, and the fibre part of the strong bundle transition, sc$^0$ on $Y[0]$), so the regularity of the linearization in the chart of the germ (V3.46) passes to every chart; then the criterion of V1.8. Tameness is not used. $T_xX$ itself carries no linear structure here (G.7), so the operator is read in charts. The passage to every chart is the chart independence at zeros, which the text does not state (Findings, Chapter 3, items 170, 236, 239). Added in the second addendum of this page with the level-$0$ Fredholm property only (G.22); updated in the third addendum.
- **Germs.** The hypothesis is the text’s since the switch to the germ reading (phase 2): the germ data of the sc-Fredholm section are germs whose levels may shrink with $m$ (V3.13, V3.16), and Proposition 3.52 enters at the centre of the chart of the germ datum, where $\mathrm{Lin}(0) = Dg(0)$ on $T_0O$ for the filling germ (Findings, Chapter 3, items 284, 310, 314, 330). `theorem_3_19_linearization_sc` gives the conclusions in the chart at $x_0$, and `linAt_isScFredholm_of_isSurjLinOfIndex` with `IsGoodPositionGerm.exists_isSurjLinOfIndex` in every chart. Hence “stronger” (formerly “narrower”, for the hypothesis): the index on every level, and the surjectivity on every level at a zero in good position, in every chart, go beyond the text’s statement.

### V3.97. The dimension of the solution set is the Fredholm index

*stronger* · at every zero, in every chart · also Theorems 3.23, 3.57 · repaired: tame charts (V3.103)

**HWZ (§3.1, Theorem 3.19, p. 74; §3.6, proof of Theorem 3.54, p. 115).** The solution set $S(f, U)$ has the structure of a smooth manifold “whose dimension agrees with the Fredholm index” (Theorem 3.19); with $d = \dim\ker f'(x)$ the solution set has the $d$-dimensional tangent germ property (proof of Theorem 3.54).

**Proved in Lean.** For an sc-smooth section and a zero $x_0$ in good position in a tame chart (V3.103): the data of Definition 3.25 at $x_0$ have a dimension $d$ with `IsSurjLinOfIndex f x_0 d`, also the regular data of Theorem 3.54 (2). For an sc-Fredholm section with tame germ data: an open $U \ni x_0$ and $d$ with every zero $y \in U$ in good position in a tame chart, `IsSurjLinOfIndex f y d`, and $S(f, U)$ a tame $d$-dimensional manifold with boundary with corners (`theorem_3_23_index`; without boundary if $d_X \equiv 0$, `theorem_3_19_index`); under the hypotheses of Theorem 3.57, regular data at every zero whose dimension is the index at the zeros of their chart domain (`theorem_3_57_index`). For an sc-Fredholm section, at a zero $y$ with `IsSurjLinOfIndex f y d`, in every chart $\mathrm{Lin}(z)$ is moreover sc-Fredholm and onto on every level, of index $d$ on every level.

- `Polyfold.theorem_3_54_tangentGermChart_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 434
- `Polyfold.theorem_3_54_tangentGermChart_solutionSet_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 448
- `Polyfold.theorem_3_54_two_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 472
- `Polyfold.theorem_3_23_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 547
- `Polyfold.theorem_3_19_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 595
- `Polyfold.theorem_3_57_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 633
- `Polyfold.theorem_3_54_graph_proj_conj` — Polyfold/Chapter3/GlobalIFTG.lean, line 89
- `Polyfold.theorem_3_54_tangentGermChart_proj_conj` — Polyfold/Chapter3/GlobalIFTCenterG.lean, line 47
- `Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 461

*What differs.*
- $d = \dim\ker D(h + t)(0) = n - N$ for the conjugation from which the chart of the tangent germ data is built, and $n - N$ is the index of $f'(x_0)$ for the same conjugation (Proposition 3.52); the proofs of Theorem 3.54 had to expose that conjugation (`_conj` forms). The index is stated at every zero near the point and in every chart; the text states no dimension in Theorems 3.23 and 3.57 (Findings, Chapter 3, item 170). Added in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).
- That $d$ is the index on every level of $f'(y)$ as an sc-Fredholm operator, in every chart, is V3.96 (Findings, Chapter 3, item 239). Updated in the third addendum of this page.

### V3.98. The Fredholm index along the solution set and along paths (Definition 6.1, Proposition 6.2)

*narrower* · paths on $\mathbb R$ · Definition 6.1 local section · Definition 6.1 well defined, no Prop. 1.10 · repaired: tame charts (V3.103) · sc-index, every level, every chart

**HWZ (Definition 6.1, pp. 200–201; Proposition 6.2, p. 201).** Definition 6.1: at a smooth point $x$, $\mathrm{ind}(f, x)$ is the Fredholm index of $(f - s)'(x)$ for a local sc$^+$-section $s$ with $s(x) = f(x)$; it does not depend on $s$. Proposition 6.2: over a tame M-polyfold, if $x_0$, $x_1$ are smooth points connected by an sc-smooth path $\varphi : [0, 1] \to X$, then $\mathrm{ind}(f, x_0) = \mathrm{ind}(f, x_1)$. In Chapter 3 the statement along the solution set is implicit in Theorem 3.54 (1).

**Proved in Lean.** For an sc-Fredholm section with tame germ data (V3.103), $f(x_0) = 0$, $(f, x_0)$ in good position in a tame chart: an open $V_x \ni x_0$ and $d$ with `IsSurjLinOfIndex f y d` at every zero $y \in V_x$, so $\mathrm{ind}\,f'(y) = \dim\ker f'(y) = \mathrm{ind}\,f'(x_0)$. With Theorem 3.54: every zero in $V_x$ in good position in a tame chart, and regular data of dimension $d$ at $x_0$ with chart domain $V_x$. In sc form: at every zero $y \in V_x$, in **every** strong bundle chart around $y$, $\mathrm{Lin}(z) : T_zO \to K_z$ is sc-Fredholm, onto on every level and of index $d$ on every level; at any zero of an sc-Fredholm section, in every chart, $\mathrm{Lin}(z)$ is sc-Fredholm with the same index on every level (`StrongBundle.linAt_isScFredholm`). **Without good position, with the text’s hypotheses**: if $f$ is an sc-Fredholm section with tame germ data and $f(x_0) = 0$, there are an open $V \ni x_0$ and $i \in \mathbb Z$ such that at every zero $y \in V$, in every strong bundle chart around $y$, $f'(y)$ is Fredholm of index $i$ (`IsLinOfIndex`; `index_locally_constant_tame`), and in sc form $\mathrm{Lin}(z)$ is sc-Fredholm of index $i$ on every level (`theorem_3_54_index_locally_constant_general_tame`); neither good position, nor surjectivity at $x_0$, nor bump functions are assumed (the first forms, for $X$ admitting sc-smooth bump functions (Definition 5.9): `index_locally_constant_of_admitsBumpFunctions`, `theorem_3_54_index_locally_constant_general`). **Definition 6.1** (`StrongBundle.IsIndexAtLocal f x i`, with the text’s locally defined section): there are an open $V \ni x$ and an sc$^+$-section $s$ of the restriction $P|V$ (`StrongBundle.restrictOpen`) with $(f|_V + s)(x) = 0$ and $(f|_V + s)'(x)$ Fredholm of index $i$ in every strong bundle chart of $P|V$; for an sc-Fredholm section the index is unique (`IsIndexAtLocal.unique`), at a zero it is the index of $f'(x)$, and it exists at every smooth point (`exists_isIndexAtLocal`). The reading with an sc$^+$-section on all of $X$ (`StrongBundle.IsIndexAt`; unique, `IsIndexAt.unique`; existing at every smooth point if $X$ admits bump functions, `exists_isIndexAt`) implies it, and is the same notion when $X$ admits sc-smooth bump functions (`isIndexAtLocal_iff_isIndexAt`). **Proposition 6.2** (`proposition_6_2_local`): if $f$ is an sc-Fredholm section with tame germ data, then for every sc-smooth path $\varphi : \mathbb R \to X$ there is $i$ with $\mathrm{ind}(f, \varphi(t)) = i$ for all $t$, and any two values of the index at $\varphi(0)$ and $\varphi(1)$ agree (`proposition_6_2_local'`); if $X$ admits sc-smooth bump functions, the same holds for the global reading (`proposition_6_2`).

- `Polyfold.theorem_3_54_index_locally_constant` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 508
- `Polyfold.theorem_3_54_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 526
- `Polyfold.isSurjLinOfIndex_of_forall_dim` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 492
- `Polyfold.theorem_3_54_index_locally_constant_sc` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 504
- `Polyfold.StrongBundle.linAt_isScFredholm` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 400
- `Polyfold.index_locally_constant_of_admitsBumpFunctions` — Polyfold/Chapter3/IndexLocallyConstantG.lean, line 861
- `Polyfold.theorem_3_54_index_locally_constant_general` — Polyfold/Chapter3/IndexLocallyConstantG.lean, line 896
- `Polyfold.index_locally_constant_tame` — Polyfold/Chapter3/IndexLocallyConstantLocal.lean, line 505
- `Polyfold.theorem_3_54_index_locally_constant_general_tame` — Polyfold/Chapter3/IndexLocallyConstantLocal.lean, line 533
- `Polyfold.StrongBundle.IsLinOfIndex` — Polyfold/Chapter3/IndexLocallyConstant.lean, line 151
- `Polyfold.StrongBundle.isLinOfIndex_of_paramSection_isLinOfIndex` — Polyfold/Chapter3/IndexLocallyConstantG.lean, line 109
- `Polyfold.StrongBundle.IsIndexAt` — Polyfold/Chapter3/IndexAlongPaths.lean, line 236
- `Polyfold.StrongBundle.IsIndexAt.unique` — Polyfold/Chapter3/IndexAlongPaths.lean, line 305
- `Polyfold.StrongBundle.exists_isIndexAt` — Polyfold/Chapter3/IndexAlongPaths.lean, line 343
- `Polyfold.exists_isScPlusSection_pullback_of_path` — Polyfold/Chapter3/IndexAlongPathsDevice.lean, line 507
- `Polyfold.StrongBundle.isIndexAt_of_pullback_isLinOfIndex` — Polyfold/Chapter3/IndexAlongPathsDevice.lean, line 421
- `Polyfold.proposition_6_2` — Polyfold/Chapter3/IndexAlongPathsDevice.lean, line 685
- `Polyfold.StrongBundle.restrictOpen` — Polyfold/Chapter3/RestrictOpen.lean, line 451
- `Polyfold.StrongBundle.IsIndexAtLocal` — Polyfold/Chapter3/IndexAlongPathsLocal.lean, line 340
- `Polyfold.StrongBundle.IsIndexAtLocal.unique` — Polyfold/Chapter3/IndexAlongPathsLocal.lean, line 361
- `Polyfold.StrongBundle.exists_isIndexAtLocal` — Polyfold/Chapter3/IndexAlongPathsLocal.lean, line 392
- `Polyfold.StrongBundle.isIndexAtLocal_iff_isIndexAt` — Polyfold/Chapter3/IndexAlongPathsLocalBump.lean, line 283
- `Polyfold.proposition_6_2_local` — Polyfold/Chapter3/IndexAlongPathsLocal.lean, line 762
- `Polyfold.proposition_6_2_local'` — Polyfold/Chapter3/IndexAlongPathsLocal.lean, line 770

*What differs.*
- **Proposition 6.2 is proved with the text’s hypotheses** (fifth addendum of this page; in the fourth, with bump functions), by the text’s device run on the restriction $P|V$ of $P$ to the domain $V$ of a strong bundle chart around $\varphi(t_0)$ (`StrongBundle.restrictOpen`), for each $t_0$: an sc$^+$-section $S$ of the pull-back to $\mathbb R \times V$ with $\tilde f + S = 0$ along the graph of the path near $t_0$ (the text’s $s(t, x) = R(x, f(\varphi(t)))$ in the chart, with no cut-off, since the chart covers $V$), the local constancy of the index of $\tilde f + S$ along its zero set (stabilizing sections $R(\cdot, e_i)$ in the product chart, again without cut-off, and the implicit function theorem), the index count $\mathrm{ind}(\tilde f + S)'(t, x) = \mathrm{ind}(f, x) + 1$ through the slice $S(t, \cdot)$ (`isIndexAt_of_pullback_isLinOfIndex`), and the connectedness of $\mathbb R$ (`proposition_6_2_local`). No bump functions are assumed (“we do not need a sc-smooth partition of unity”, p. 202); tame germ data are the project’s reading of the text’s tameness (V3.103), as in V3.94, where they are no narrowing. With bump functions the proposition holds for the global reading of Definition 6.1 as well (`proposition_6_2`, the form of the fourth addendum, whose section along the path is cut off by a bump; `exists_isScPlusSection_pullback_of_path`) (Findings, Chapter 3, items 340–349, 360–367).
- **Why still “narrower”.** The path is $\varphi : \mathbb R \to X$, not $[0, 1] \to X$: $\mathbb R \times X$ is the product of Theorem 3.18 and has no boundary, and the text’s tame M-polyfold $[0, 1] \times X$ is not used. A path on $[0, 1]$ that extends sc-smoothly to $\mathbb R$ is covered; a path sc-smooth on $[0, 1]$ only, in the sense of M-polyfolds with boundary, is not, and the project has no M-polyfold $[0, 1]$. This is the one narrowing left: the bump functions are gone, Definition 6.1 has the text’s local sections, and the hypotheses on $f$ are the text’s in the project’s reading of tameness.
- Definition 6.1 has no row of its own. It is `IsIndexAtLocal`: the text’s locally defined sc$^+$-section is a section of the restriction $P|V$ to an open $V \ni x$ — the restriction of a strong bundle to an open set, which the text uses without comment, is constructed (`StrongBundle.restrictOpen`, whose atlas consists of the charts of $P$ inside $V$) — and the text’s $f - s$, $s(x) = f(x)$, is written $f + s$, $(f + s)(x) = 0$. It is well defined, two local sections being compared on the intersection of their domains (`IsIndexAtLocal.unique`), and it exists at every smooth point without bump functions, through the section $-R(\cdot, f(x))$ on a chart domain (`exists_isIndexAtLocal`). The global reading `IsIndexAt` of the fourth addendum implies it, and when $X$ admits bump functions the two agree, the local section being cut off (`isIndexAtLocal_iff_isIndexAt`). The independence of $s$ is proved from the germ data and Theorem 3.15, without the text’s appeal to Proposition 1.10, for which the project has no lemma that the linearization of an sc$^+$-section is compact (Findings, Chapter 3, items 340, 364, 367).
- Along the solution set the formal proof combines the good position of the nearby zeros (V3.94), the local constancy of the dimension (V3.85) and dimension = index at each zero (V3.97); the text’s proof of Proposition 6.2 uses the step of V3.82 for an extended section, which along solution sets is repaired by V3.93 (Findings, Chapter 3, items 171, 188). Added in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).
- The sc form (the index of $f'(y)$ as an sc-Fredholm operator, on every level, in every chart) is proved as well; that $\mathrm{Lin}(z)$ is sc-Fredholm at every zero in every chart, with the level-$0$ index on every level, is `StrongBundle.linAt_isScFredholm` (V3.96), cited here since the fifth addendum. **The local constancy without good position holds with the text’s hypotheses** (tame germ data, no bump functions; `index_locally_constant_tame`, in sc form `theorem_3_54_index_locally_constant_general_tame`), by the text’s device for Proposition 6.2 on the restriction $P|V$ to a chart domain: finitely many sc$^+$-sections $R(\cdot, e_i)$, which on $P|V$ need no cut-off, put the parametrized section of Theorem 3.18 into general position at $(0, x_0)$, its index is constant along its solution set (the case above), at $(0, y)$ it is $k + \operatorname{ind} f'(y)$, and the index at a zero is the same for $P$ and $P|V$, through the germ datum (Findings, Chapter 3, items 240–242, 360–363). The first proof, for M-polyfolds admitting bump functions (Lemma 5.11 for the sections), is kept (`index_locally_constant_of_admitsBumpFunctions`). The candidate counterexample of items 188 and 243 is excluded under tame germ data by Theorem 3.54 (1). Without tame germ data the question is open: $\operatorname{ind} f'(y) = \operatorname{ind} f'(x_0)$ iff the block $C(z) = (1 - \rho(z))Dg(z)|_{\ker Dr(z)}$ of the filling has index $0$, which condition (3) of Definition 3.4 gives at $z = 0$ only (items 243, 343). Updated in the third, fourth and fifth addenda of this page.

### V3.99. $\ker f'(y) = T_yS$ in a chart

*restated* · in the chart $\psi\varphi$ · $T_yS \subseteq T_yX$: G.13 · repaired: tame charts (V3.103)

**HWZ (§3.1, Theorem 3.19, p. 74).** $U$ can be chosen such that for $y \in S(f, U)$ the linearization $f'(y)$ is surjective and $\ker f'(y) = T_yS(f, U)$ is the tangent space.

**Proved in Lean.** For an sc-smooth section and a zero $x_0$ in good position in a tame chart (V3.103): in a tame chart $c$ centred at $x_0$ (as in Definition 3.53), with the conjugating sc-diffeomorphism $\psi$, $K = \ker D(h + t)(0)$ and the solution graph $\sigma : V' \to E'$ ($C^1$, $\sigma(0) = 0$, $D\sigma(0) = 0$) with $\psi\varphi(\{y \in V_x \mid f(y) = 0\}) = \{v + \sigma(v)\}$, there is an open $V_{x,2} \ni x_0$ such that at every zero $y \in V_{x,2}$ with $\psi\varphi(y) = v + \sigma(v)$ and every level-$1$ point $z$ over $\varphi(y)$, $D\psi(z)$ maps $\ker\mathrm{Lin}(z)$ onto $N_v = \{n + D\sigma(v)n \mid n \in K\}$.

- `Polyfold.theorem_3_54_ker_eq_tangent` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 708
- `Polyfold.theorem_3_54_nearby_kernel` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 160
- `Polyfold.linAt_eq_germDeriv` — Polyfold/Chapter3/LinearizationChartsG.lean, line 130

*What differs.*
- In the chart of the tangent germ data, where $N_v$ is the tangent space of the solution set; $T_yS$ as a subspace of $T_yX$ needs the linear structure of $T_yX$ (Definition 2.38, Chapter 2 gap G.13) and is not formalized. The surjectivity of $f'(y)$ is V3.94 (Findings, Chapter 3, item 172). Added in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).

### V3.100. Good position is surjectivity at a zero with $d_X = 0$

*hypotheses explicit* · tame chart needed · pointwise, at $d_X(y) = 0$

**HWZ (§3.6, after Theorem 3.54, p. 111; Corollary 3.24, p. 79).** “In case $\partial X = \emptyset$, the requirement that $(f, x)$ is in good position just means that $f'(x)$ is surjective”; the kernel condition is “an empty condition if $d_X(x) = 0$” (Corollary 3.24).

**Proved in Lean.** `IsLinSurjAt f y`: in some strong bundle chart around $y$, at a level-$1$ point over $\varphi(y)$, $\mathrm{Lin}(z)$ maps onto the fibre $K_z$; at a zero it then does so in every chart (`IsLinSurjAt.linAt_surjective`). For an sc-Fredholm section with tame germ data (V3.103) and a zero $y$ with $d_X(y) = 0$: $(f, y)$ is in good position in a tame chart iff `IsLinSurjAt f y`. On the way: a subspace of $T$ is in good position inside $T$ to any cone containing $T$; in the tame chart of the germ data at $y$, $d_C(\varphi(y)) = d_X(y) = 0$, so the partial quadrant at $\varphi(y)$ is the whole space, and the good position is read there (V3.107).

- `Polyfold.StrongBundle.IsLinSurjAt` — Polyfold/Chapter3/GlobalIFTIndex.lean, line 254
- `Polyfold.isInGoodPositionIn_of_subset` — Polyfold/Chapter3/GlobalIFTIndex.lean, line 132
- `Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 311
- `Polyfold.StrongBundle.isGoodPositionGerm_of_isLinSurjAt` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 343
- `Polyfold.StrongBundle.IsGoodPositionGerm.isLinSurjAt` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 289
- `Polyfold.StrongBundle.isGoodPositionGerm_iff_isLinSurjAt` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 358
- `Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective` — Polyfold/Chapter3/GlobalIFTIndex.lean, line 263

*What differs.*
- Definition 3.53 is stated in the chart of Definition 3.11 with the chart's partial quadrant, which need not be the whole space where $d_X = 0$; in a tame chart $d_C = d_X$ (Proposition 2.36). In a non-tame chart $d_C(\varphi(y))$ can exceed $d_X(y)$ (Findings, Chapter 3, item 173). Added in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first stated for “a strong bundle whose charts have tame base retractions” (`htame`), which cannot be met (V3.104), and with the surjectivity read in an arbitrary chart, which needed that chart tame; the surjectivity is now carried to the tame chart of the germ data (Findings, Chapter 3, items 190, 194).

### V3.101. Theorems 3.19 and 3.56 with “$f'(x)$ surjective”

*stronger* · “$f'(x)$ surjective” · tame, with the index · repaired: tame charts (V3.103)

**HWZ (§3.1, Theorem 3.19, p. 74; §3.6, Theorem 3.56, p. 115).** (3.19) $d_X \equiv 0$, $f(x_0) = 0$, $f'(x_0)$ surjective: the local solution set is a smooth manifold of dimension the Fredholm index. (3.56) $\partial X = \emptyset$ and $f'(x)$ surjective at every zero: $S$ is a sub-M-polyfold whose induced structure is equivalent to a smooth manifold without boundary.

**Proved in Lean.** For $d_X \equiv 0$ and an sc-Fredholm section: if $f$ has tame germ data (V3.103), $f(x_0) = 0$ and `IsLinSurjAt f x_0`, the conclusions of `theorem_3_19_index` (V3.97); if $f$ has tame germ data and `IsLinSurjAt f x` at every zero (`theorem_3_56_of_surjective`), or $(f, x)$ is in good position in a tame chart at every zero (`theorem_3_56_tame`), and $S \ne \emptyset$, $S$ is a sub-M-polyfold with tame induced structure, a manifold of locally constant dimension without boundary, with regular data at every zero whose dimension is the Fredholm index at the zeros of their chart domain.

- `Polyfold.theorem_3_19_of_surjective` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 615
- `Polyfold.theorem_3_56_of_surjective` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 679
- `Polyfold.theorem_3_56_tame` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 656

*What differs.*
- The text's hypotheses; the tameness of the induced structure and the index are added conclusions; $S \ne \emptyset$ for the formal charts (Findings, Chapter 3, item 173). Added in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).

### V3.102. The filler condition at the nearby zeros follows from good position

*not in the book* · the hypothesis of V3.82 holds · the converse of item 100

**HWZ (no counterpart in the text (Definition 3.4 (3), p. 64)).** Not in the text. Definition 3.4 (3) asks that $(1 - \rho(0))Dg(0)$ be an isomorphism $\ker Dr(0) \to \ker\rho(0)$, at $0$ only.

**Proved in Lean.** (a) For $Dg(z)$ the value at $z$ of a derivative family of a germ $g$ with $z$ in its germ, at a level-$1$ point $z$ over a point $z_0$ of the retract with $\ker Dg(z) \subseteq T_{z_0}O$: if $\rho(z_0)k \in Dg(z)(T_{z_0}O)$ for all $k$, then $(1 - \rho(z_0))Dg(z)$ is injective on $\ker Dr(z)$. (b) If moreover $Dg(z)$ is onto and $g$ fills $\mathbf f$ near $z_0$ with $\mathbf f(z_0) = 0$, the two conditions are equivalent. (c) For an sc-Fredholm section with tame germ data (V3.103) and a zero $x_0$ in good position in a tame chart, `IsGoodPositionGermFilled f x_0` holds (in a tame chart).

- `Polyfold.normal_injective_of_exists_range_deriv_eq_ρ_germ` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 96
- `Polyfold.exists_range_deriv_eq_ρ_iff_normal_injective_germ` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 119
- `Polyfold.isGoodPositionGermFilled_of_isGoodPositionGerm` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 806
- `Polyfold.exists_range_deriv_eq_ρ_of_normal_injective_germ` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 68

*What differs.*
- (c) uses Theorem 3.54 (1) with the text's hypotheses (V3.94) and the tangency of the kernel (V3.81): the added hypothesis of the first forms V3.68, V3.69, V3.82, V3.85 is satisfied whenever the text's hypotheses are (Findings, Chapter 3, item 174). Added in the second addendum of this page.
- Updated after the repair of the tameness hypothesis: first proved with “the base retraction of every strong bundle chart compatible with the atlas is tame” (`htame`), which no strong bundle over a nonempty base satisfies (V3.104), so that form was vacuous; now with the hypotheses of V3.103 (Findings, Chapter 3, items 190–192).

### V3.103. Definitions 3.50, 3.51 and 3.53 in a tame chart

*hypotheses explicit* · the hypotheses of §3.6 · tame chart of the germ data · satisfiable · filler chart-bound

**HWZ (§3.6, Definitions 3.50, 3.51, p. 110; Definition 3.53, p. 111).** (3.50) For an sc-smooth section $f$ of the tame strong bundle $P : Y \to X$ and a smooth point $x$: $(f, x)$ is an sc-Fredholm germ if there is a strong bundle chart $\Phi : \Phi^{-1}(V) \to K$ around $x$ covering $\varphi : (V, x) \to (O, 0)$, “where $K \to O$ is a tame strong local bundle”, in which the local section has a filling $g$ near $0$ and a local sc$^+$-section $s$ with $s(0) = g(0)$ and $g - s$ conjugated near $0$ to a basic germ. (3.51) An sc-smooth section of the tame strong bundle is sc-Fredholm if it is regularizing and an sc-Fredholm germ at every smooth point. (3.53) Good position is defined for an sc-Fredholm germ of a tame strong bundle. A strong bundle retraction is tame when its base retraction $r$ is (p. 49).

**Proved in Lean.** `StrongBundle.IsTameChart`: a strong bundle chart compatible with the atlas whose base retraction $r : U \to U$ is tame (Definition 2.34). `IsScFredholmGermTame f x` (“tame germ data”): $x$ smooth and the data of Definition 3.11 in the text’s germ reading (V3.13) in a tame chart. `IsGoodPositionGermTame f x`: the same data with the germ in good position in that chart (V3.47). `IsScFredholmSectionTame f`: an sc-Fredholm section (V3.16) with tame germ data at every smooth point. Each implies the form without tameness; good position in a tame chart gives tame germ data; `IsGoodPositionGermFilled` (V3.82) is stated in a tame chart. A retraction agreeing on its domain with a tame one is tame, so a compatible chart whose base retraction is the identity of $U$ is tame.

- `Polyfold.StrongBundle.IsTameChart` — Polyfold/Chapter3/TameGerms.lean, line 128
- `Polyfold.StrongBundle.IsScFredholmGermTame` — Polyfold/Chapter3/TameGermsG.lean, line 78
- `Polyfold.StrongBundle.IsGoodPositionGermTame` — Polyfold/Chapter3/TameGermsG.lean, line 104
- `Polyfold.StrongBundle.IsScFredholmSectionTame` — Polyfold/Chapter3/TameGermsG.lean, line 142
- `Polyfold.StrongBundle.IsScFredholmGermTame.isScFredholmGerm` — Polyfold/Chapter3/TameGermsG.lean, line 87
- `Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGerm` — Polyfold/Chapter3/TameGermsG.lean, line 116
- `Polyfold.StrongBundle.IsGoodPositionGermTame.isScFredholmGermTame` — Polyfold/Chapter3/TameGermsG.lean, line 122
- `Polyfold.StrongBundle.IsGoodPositionGermFilled.isGoodPositionGermTame` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 360
- `Polyfold.StrongBundle.isTameChart_of_eqOn_id` — Polyfold/Chapter3/TameGerms.lean, line 263
- `Polyfold.ScRetraction.IsTame.congr` — Polyfold/Chapter3/TameGerms.lean, line 85
- `Polyfold.IsFillingGerm.nonempty_kerEquiv` — Polyfold/Chapter3/TameGermData.lean, line 91
- `Polyfold.TrivialBundle.tame_atlas_no_germData_in_atlas_chart` — Polyfold/Chapter3/TameGermData.lean, line 502

*What differs.*
- These are the hypotheses of the implicit function theorems of §3.6 (V3.48, V3.68–V3.70, V3.80–V3.82, V3.84–V3.87, V3.94–V3.102). They were first proved with “tame strong bundle” read as: the base retraction of **every** strong bundle chart compatible with the atlas is tame. No strong bundle over a nonempty base satisfies that (V3.104), so those first statements were vacuous; the proofs used the tameness only for particular charts, and the repair changed the statements, not the arguments (Findings, Chapter 3, items 190–192, 198).
- Whether germ data in some chart (V3.13) can be moved to some compatible tame chart when the atlas consists of tame charts (Definition 3.11 $\Rightarrow$ Definition 3.50) is open. It cannot be done by re-centring a chart of the tame atlas: whether a filling exists in a chart depends on the chart ($\ker Dr(0) \cong \ker\rho(0)$ is necessary, `IsFillingGerm.nonempty_kerEquiv`), and the trivial bundle with the one-chart tame atlas of `evenBundleChart` has sc-Fredholm sections with tame germ data in compatible charts but none in the atlas chart (`tame_atlas_no_germData_in_atlas_chart`). The text builds the tame chart into Definition 3.50, and so do the theorems (Findings, Chapter 3, items 199, 350–353). Updated in the fourth addendum of this page.
- **Germs.** Since the switch to the text’s germ reading (phase 2) the three notions carry the germ data of the text (V3.13, V3.45); the earlier whole-chart forms are `IsScFredholmGermTameWholeChart`, `IsGoodPositionGermTameWholeChart`, `IsScFredholmSectionTameWholeChart`, and the non-vacuity witnesses satisfy both readings (Findings, Chapter 3, items 220–221, 304, 330). For Definition 3.53 the comparison is that of V3.47. Hence “hypotheses explicit” again (“restated” in the third addendum).

### V3.104. A non-tame retraction onto a product with a point: the earlier tameness hypothesis cannot be met

*not in the book* · the vacuity, retraction-level half · chart-level half not formalized

**HWZ (no counterpart in the text (Definitions 2.34, 2.50, pp. 39–40, 51–52)).** Not in the text. Definition 2.34 (1) asks a tame retraction to preserve the degeneracy index, $d_C(r(x)) = d_C(x)$; Definition 2.50 asks of compatible strong bundle charts only that their transition maps be sc-smooth.

**Proved in Lean.** For an sc-Banach space $W$, the constant retraction $c : (a, w) \mapsto (1, 0)$ of the partial quadrant $[0, \infty) \oplus W$ of $\mathbb R \oplus W$ (sc-smooth, with retract $\{(1, 0)\}$), and every sc-smooth retraction $r$ of a nonempty relatively open $U$ in a partial quadrant $C$: the product retraction $c \times r$, with retract $\{(1, 0)\} \times r(U)$, is not tame. At $((0, 0), u)$, $u \in r(U)$, the degeneracy index is $1 + d_C(u)$, at its image $((1, 0), u)$ it is $d_C(u)$.

- `Polyfold.ScRetraction.halfLineConst_prod_not_isTame` — Polyfold/Chapter3/TameVacuity.lean, line 102
- `Polyfold.ScRetraction.halfLineConst` — Polyfold/Chapter3/TameVacuity.lean, line 70
- `Polyfold.ScRetraction.halfLineConst_retract` — Polyfold/Chapter3/TameVacuity.lean, line 88
- `Polyfold.halfLineSc` — Polyfold/Chapter3/TameVacuity.lean, line 53

*What differs.*
- The retraction-level half of the argument that the hypothesis under which the theorems of §3.6 were first proved, “the base retraction of every compatible strong bundle chart is tame”, fails for every strong bundle over a nonempty base: from a compatible chart $(\varphi, U, R, \Phi)$, the chart $(1, \varphi)$ onto $\{1\} \times O$ with base retraction $(a, u) \mapsto (1, r(u))$ on $[0, \infty) \times U$ (the retraction above with $W = 0$) has the transition maps of the first composed with affine maps, hence is compatible with every chart the first one is. That chart and its compatibility are not formalized (sc-calculus for affine maps). So the earlier statements were vacuous, and they are replaced by those with the hypotheses of V3.103 (Findings, Chapter 3, items 190, 199). Added after the repair of the tameness hypothesis.

### V3.105. Theorem 3.15 for tame germ data

*hypotheses explicit* · the chart is kept

**HWZ (§3.1, Theorem 3.15, p. 71; recalled after Definition 3.51, p. 110).** If $f$ is an sc-Fredholm section of the tame strong bundle and $s$ an sc$^+$-section, then $f + s$ is an sc-Fredholm section.

**Proved in Lean.** If $f$ is an sc-Fredholm section with tame germ data (V3.103) and $s$ an sc$^+$-section, then $f + s$ is an sc-Fredholm section with tame germ data: at every smooth point the germ data of $f + s$ lie in the tame chart of those of $f$ (filling germ $g + \hat s \circ r$, sc$^+$-germ $\hat s_1 \circ r + t_0$, the same conjugation; V3.17).

- `Polyfold.theorem_3_15_tame` — Polyfold/Chapter3/TameGermsAddG.lean, line 115
- `Polyfold.StrongBundle.IsScFredholmGermTame.sectionAdd` — Polyfold/Chapter3/TameGermsAddG.lean, line 101

*What differs.*
- Theorem 3.15 for the tame reading of Definitions 3.50, 3.51 (V3.103); the proof of V3.17 does not change the chart (Findings, Chapter 3, item 195). Added after the repair of the tameness hypothesis.

### V3.106. Theorem 3.18 for tame germ data

*hypotheses explicit* · product of tame charts is tame

**HWZ (§3.1, Theorem 3.18, p. 74).** Let $P : Y \to X$ be a tame strong bundle and $f$ an sc-Fredholm section. If $s_1, \dots, s_n \in \Gamma^+(P)$, then $(r, x) \mapsto f(x) + \sum_i r_is_i(x)$ is an sc-Fredholm section of the pull-back bundle $\pi^*(P) \to \mathbb R^n \times X$.

**Proved in Lean.** In the setting of V3.91: if $f$ is an sc-Fredholm section with tame germ data (V3.103) and $s_1, \dots, s_n$ are sc$^+$-sections, then $F(r, x) = f(x) + \sum_i r_is_i(x)$ is an sc-Fredholm section of $\pi^*P$ with tame germ data. On the way: the product chart $(r \mapsto r - r_0) \times c$ (V3.92), with base retraction $1 \times r$ on $\mathbb R^n \times U$, is tame when $r$ is ($\mathbb R^n$ carries the identity retraction, so $d(a, u) = d_C(u)$, and minimal subspaces and tangent spaces are products); so $\tilde f$ has germ data in the tame product charts, and V3.105 adds $\tilde s$.

- `Polyfold.theorem_3_18_tame` — Polyfold/Chapter3/ParamPerturbationG.lean, line 209
- `Polyfold.PullbackChartData.ofProd_isTame` — Polyfold/Chapter3/ParamPerturbation.lean, line 1183
- `Polyfold.StrongBundle.IsScFredholmGermTame.param` — Polyfold/Chapter3/ParamPerturbationG.lean, line 173
- `Polyfold.StrongBundle.IsScFredholmSectionTame.param` — Polyfold/Chapter3/ParamPerturbationG.lean, line 195

*What differs.*
- The tame form of V3.91, which is what the implicit function theorems of §3.6 need when applied to $F$; the tameness of the base $\mathbb R^n \times X$ (`prod_rn_isTame`, V3.91) is a different statement (Findings, Chapter 3, item 195). Added after the repair of the tameness hypothesis.

### V3.107. Good position in any chart of the germ data

*not in the book* · every chart of the germ data · the chart independence of Def. 3.53

**HWZ (§3.6, Definition 3.53, p. 111; proof of Theorem 3.54, p. 115).** Definition 3.53 defines good position through $f'(x) : T_xX \to Y_x$ and $C_xX$, presupposing that it does not depend on the chart; the proof of Theorem 3.54 concludes good position at the nearby zeros “proceeding as above”.

**Proved in Lean.** (a) In the setting of V3.79 (a zero $y$, a chart $c$ around $y$ not necessarily centred, an sc$^1$-germ $g$ agreeing with $\mathbf f$ on $O$ near $\varphi(y)$ with $z$ in its germ, $Dg(z)$ mapping $T_zO$ onto $K_z$, $\ker Dg(z) \cap T_zO$ in good position to $C_{\varphi(y)}$ inside $T_zO$): for **every** datum of Definition 3.11 at $y$ (a compatible chart $c'$ centred at $y$, a filling germ $g'$ with a derivative family $Dg'$), the germ is in good position in $c'$ at $Dg'(0)$; with only $\rho(z)k$ in the range for every smooth $k$, under the hypothesis that $Dg'(0)$ is Fredholm. (b) If $(f, y)$, $f(y) = 0$, is in good position in some chart and has tame germ data, it is in good position in that tame chart.

- `Polyfold.StrongBundle.isGoodPositionAtGerm_of_chart` — Polyfold/Chapter3/LinearizationChartsG.lean, line 470
- `Polyfold.StrongBundle.isGoodPositionAtGerm_of_chart_dense` — Polyfold/Chapter3/LinearizationChartsG.lean, line 501
- `Polyfold.StrongBundle.IsGoodPositionGerm.toTame` — Polyfold/Chapter3/TameGermsAddG.lean, line 69

*What differs.*
- V3.79 gives the good position in the chart that Definition 3.11 provides at $y$; (a) gives it in every chart carrying germ data, and (b) applies (a) at $z = 0$ in the chart of the given good position. This is how the good position of the nearby zeros (V3.94) and the good position from surjectivity (V3.100) are obtained in tame charts (Findings, Chapter 3, items 193, 194). Added after the repair of the tameness hypothesis.
- In the germ reading (b) needs no Fredholm input: in the chart of the given good position, centred at $y$, (a) applies at $z = 0$, which lies in every germ, and $K_0$ is the whole target, so the form with all of $K_z$ in the range suffices. The whole-chart form of (a) is `isGoodPositionAt_of_chart_dense` (Findings, Chapter 3, item 301). Updated after the switch of Definition 3.11 to the text’s germ reading (phase 2).

## Chapter 4

*HWZ Chapter 4 §§4.1–4.4, preprint pp. 147–168: manifolds with boundary with corners — sc⁺-retracts and the characterization, smooth finite-dimensional submanifolds, families and Sard’s theorem*

### V4.1. Definition 4.1: corner charts and corner structures

*restated* · compatibility = equivalence of atlases · dimension may vary

**HWZ (§4.1, Definition 4.1, p. 147).** An M-polyfold $X$ has a compatible smooth manifold structure with boundary with corners if it admits an atlas of sc-smoothly compatible charts $(V, \varphi, (U, C, \mathbb R^n))$, $\varphi : V \to U$ an sc-diffeomorphism from an open $V \subseteq X$ onto a relatively open subset $U$ of a partial quadrant $C$ in $\mathbb R^n$ (or in a finite-dimensional vector space).

**Proved in Lean.** A corner chart (`MChart.IsCornerChart`) is a chart whose model is $(U, C, V)$ with $V$ finite-dimensional, the constant sc-structure, $U$ relatively open in the partial quadrant $C$, and the identity retraction. `HasCornerStructure`: an atlas of corner charts equivalent to the atlas of $X$; equivalently every point lies in a corner chart that is a chart of $X$. The dimension may vary. Corner models are tame retracts and sc⁺-retracts; a corner structure makes $X$ tame.

- `Polyfold.MChart.IsCornerChart` — Polyfold/Chapter4/Characterization.lean, line 237
- `Polyfold.MPolyfold.HasCornerStructure` — Polyfold/Chapter4/Characterization.lean, line 288
- `Polyfold.MPolyfold.hasCornerStructure_iff` — Polyfold/Chapter4/Characterization.lean, line 296
- `Polyfold.MPolyfold.HasCornerStructure.isTame` — Polyfold/Chapter4/Characterization.lean, line 314
- `Polyfold.MChart.IsCornerChart.isTameRetract` — Polyfold/Chapter4/Characterization.lean, line 262
- `Polyfold.MChart.IsCornerChart.isScPlusRetract` — Polyfold/Chapter4/Characterization.lean, line 267

*What differs.*
- "Sc-smoothly compatible" and "$\varphi$ an sc-diffeomorphism" are read as compatibility with the atlas of $X$, as for tameness (Findings, Chapter 4, item 50).
- The classical manifold structure is represented by the corner atlas; local constancy of the dimension is neither stated nor formalized.

### V4.2. Definition 4.1: the transition maps are $C^\infty$

*as in the book*

**HWZ (§4.1, after Definition 4.1, p. 147).** The transition maps between the charts are sc-diffeomorphisms between relatively open subsets of partial quadrants in finite-dimensional spaces, and therefore classically smooth, of class $C^\infty$; the atlas defines the structure of a smooth manifold with boundary with corners.

**Proved in Lean.** For compatible corner charts $\chi$, $\chi'$ the overlap $\chi(V \cap V')$ is relatively open and the transition map $\chi' \circ \chi^{-1}$ is $C^\infty$ on it (derivatives within the set).

- `Polyfold.MChart.IsCornerChart.contDiffOn_transition` — Polyfold/Chapter4/Characterization.lean, line 346
- `Polyfold.MChart.isRelOpenInQuadrant_overlap` — Polyfold/Chapter4/Characterization.lean, line 332

*What differs.*
- "The atlas defines the structure of a smooth manifold with boundary with corners" is not formalized beyond the $C^\infty$ transitions: Mathlib's manifolds with corners have one model space, here the quadrants vary (Findings, item 51).

### V4.3. Finite-dimensional sc-Banach spaces have the constant structure

*restated* · needs the density axiom

**HWZ (§1.1, after Definition 1.1, p. 6 (used in Definition 4.1)).** A finite-dimensional Banach space $E$ has precisely one sc-structure, namely the constant structure $E_m = E$.

**Proved in Lean.** If $E_0$ is finite-dimensional, every level is finite-dimensional, every inclusion $E_m \to E_0$ is onto, $E$ is sc-isomorphic to $E_0$ with the constant structure through the inclusions, and every point is smooth.

- `Polyfold.ScBanach.finiteDimensional_lvl` — Polyfold/Chapter4/ScPlus.lean, line 374
- `Polyfold.ScBanach.toBase_surjective` — Polyfold/Chapter4/ScPlus.lean, line 379
- `Polyfold.ScBanach.scIsoConst` — Polyfold/Chapter4/ScPlus.lean, line 396
- `Polyfold.ScBanach.mem_smooth_of_finiteDimensional` — Polyfold/Chapter4/Characterization.lean, line 109

*What differs.*
- The density of $E_\infty$ (Definition 1.1 (2)) makes the inclusions onto; compact injective inclusions alone do not ($E_0 = \mathbb R$, $E_m = 0$ for $m \ge 1$; Findings, item 6).

### V4.4. Definition 4.1 with arbitrary finite-dimensional models; Chapter 3's manifolds with corners

*not in the book* · links Definition 4.1 to Theorem 3.27

**HWZ (§4.1, Definition 4.1, p. 147 ("or in a finite-dimensional vector space")).** Not in the text. Definition 4.1 allows a finite-dimensional vector space $E$ in place of $\mathbb R^n$; its relation to the manifolds with corners of Theorem 3.27 is not discussed.

**Proved in Lean.** A chart onto a relatively open subset of a partial quadrant in an sc-Banach space with finite-dimensional $E_0$ is, with the same map, a corner chart for the constant structure, of the same dimension. So `HasCornerStructure` is the condition of Theorem 3.27 with locally constant dimension, and the manifolds with corners of dimension $n$ are the corner structures with all charts of dimension $n$.

- `Polyfold.MChart.exists_isCornerChart_of_finiteDimensional` — Polyfold/Chapter4/Characterization.lean, line 416
- `Polyfold.IsRelOpenInQuadrant.isScDiffeoQuadrant_toConst` — Polyfold/Chapter4/Characterization.lean, line 390
- `Polyfold.MPolyfold.hasCornerStructure_iff_finiteDimensional` — Polyfold/Chapter4/Characterization.lean, line 445
- `Polyfold.MPolyfold.isManifoldWithCorners_iff` — Polyfold/Chapter4/Characterization.lean, line 462
- `Polyfold.MPolyfold.IsManifoldWithCorners.hasCornerStructure` — Polyfold/Chapter4/Characterization.lean, line 483

*What differs.*
- The constant structure in Definition 4.1 is no restriction (V4.3).

### V4.5. Theorem 4.2: the characterization

*stronger* · tameness of $X$ not used · (i) implies $X$ tame

**HWZ (§4.1, Theorem 4.2, p. 147 (proof pp. 156–157)).** For a tame M-polyfold $X$ the following are equivalent. (i) $X$ has a compatible smooth manifold structure with boundary with corners. (ii) $X_0 = X_\infty$ and $1_0^1 : X \to X^1$ is sc-smooth; every $x$ lies in a tame chart $(V, \psi, (O, C, E))$ with $\psi(x) = 0$ whose tangent space $T_0O$ is finite-dimensional and in good position to $C$.

**Proved in Lean.** For every M-polyfold $X$ (and any junk value of $1_0^1$ off $X_1$): `HasCornerStructure` iff all points are smooth, `toLevelOne` is sc-smooth, and every $x$ lies in a chart $\psi$ of $X$ with $\psi(x) = 0$, tame model, and $N = T_0O$ finite-dimensional and in good position to $C$. `theorem_4_2` adds the text's unused hypothesis "$X$ tame".

- `Polyfold.MPolyfold.theorem_4_2` — Polyfold/Chapter4/Characterization.lean, line 796
- `Polyfold.MPolyfold.theorem_4_2_general` — Polyfold/Chapter4/Characterization.lean, line 769

*What differs.*
- The charts with $\psi(x) = 0$ are re-centred charts (V4.17); proof: V4.27, V4.28 (Findings, items 52–55).

### V4.6. Remark 4.3: $1_1^0$, $1_0^1$, and the constant structure

*stronger* · “$X^1 \ne X$”: an example (G.31) · $X = X_1$ in place of $X_0 = X_\infty$ · even the topologies of $X$, $X^1$ differ

**HWZ (§4.1, Remark 4.3, p. 148).** If $X_0 = X_\infty$, $1_0^1 : X \to X^1$ has the inverse $1_1^0$, which is always sc-smooth; so if $1_0^1$ is sc-smooth it is an sc-diffeomorphism. It is possible that $X^1 \ne X$ as M-polyfolds although the underlying sets agree. A finite-dimensional space with the constant structure has $X = X^1$.

**Proved in Lean.** $1_1^0 : X^1 \to X$ is sc-smooth (in charts the sc-operator $\iota : E^1 \to E$). If $X = X_1$ as sets and $1_0^1$ is sc-smooth, it is an sc-diffeomorphism with inverse $1_1^0$. For a finite-dimensional $V$: $(\mathrm{const}\,V)^1 = \mathrm{const}\,V$, the lift is the identity, every retract is an sc⁺-retract. **The example** (`remark_4_3_example`): an M-polyfold with $X_0 = X_\infty$ for which $1_0^1 : X \to X^1$ is not sc-smooth, so $X^1 \ne X$ as M-polyfolds; it is a retract $O = O_\infty \subseteq \mathbb R \oplus X$ that is not an sc⁺-retract (`remark_4_3_retract_example`), the image of the retraction $(t, z) \mapsto (t, L(t)z)$ of moving rank-one projections on a weighted sequence space, sc-smooth by a criterion for parameter families of level operators with one level of loss (`IsLossFamily.isScSmooth`). $(X^1)_m = X_{m+1}$ as sets (`MPolyfold.mem_shift_levelSet_iff`).

- `Polyfold.ScBanach.liftOne` — Polyfold/Chapter4/ScPlus.lean, line 83
- `Polyfold.MPolyfold.toLevelOne` — Polyfold/Chapter4/ScPlus.lean, line 436
- `Polyfold.MPolyfold.remark_4_3_levelVal` — Polyfold/Chapter4/ScPlus.lean, line 466
- `Polyfold.MPolyfold.remark_4_3_isScDiffeo` — Polyfold/Chapter4/ScPlus.lean, line 480
- `Polyfold.remark_4_3_const` — Polyfold/Chapter4/ScPlus.lean, line 410
- `Polyfold.remark_4_3_example` — Polyfold/Chapter4/RemarkFourThreeFamily.lean, line 922
- `Polyfold.remark_4_3_retract_example` — Polyfold/Chapter4/RemarkFourThreeFamily.lean, line 856
- `Polyfold.IsLossFamily.isScSmooth` — Polyfold/Chapter4/RemarkFourThreeExample.lean, line 312
- `Polyfold.exists_retract_smooth_not_scPlus_of_data` — Polyfold/Chapter4/RemarkFourThreeExample.lean, line 386
- `Polyfold.MPolyfold.mem_shift_levelSet_iff` — Polyfold/Chapter5/StrongBundleShift.lean, line 304

*What differs.*
- “It is possible that $X^1 \ne X$ as M-polyfolds although the sets agree” is proved by an example the text does not give (fourth addendum of this page; formerly gap G.31). By Proposition 4.8 an example is a retract $O = O_\infty$ that is not an sc⁺-retract; it cannot come from a retraction whose level maps are $C^1$ (an argument, not formalized), so its retraction loses a level in its first derivative, as the splicings of HWZ do, and its sc-smoothness rests on a criterion with loss proved for it, not on Proposition 1.19. In the example $X$ and $X^1$ even have different topologies on the same set (Findings, Chapter 4, items 140–146).
- “$X^1 \ne X$” is read as “$1_0^1$ is not sc-smooth”, equivalently (by `remark_4_3_isScDiffeo`) “the identity is not an sc-diffeomorphism $X \to X^1$”. The sc-diffeomorphism clause needs only $X = X_1$, not $X_0 = X_\infty$. “$(X^1)_m = X_{m+1} = X_i$” misprints $X_0$; $(X^1)_m = X_{m+1}$ holds as sets, the topologies of the iterated levels being gap G.6 (Findings, Chapter 4, items 5, 125). Hence “stronger” (formerly “narrower”, for the missing example).

### V4.7. sc⁺-maps and their calculus

*not in the book* · the text uses it undefined

**HWZ (§4.1, proof of Lemma 4.7, p. 149 ("$r$ is a sc⁺-map")).** Not in the text. Definition 4.4 defines sc⁺ for retractions and Definition 1.4 for operators; the proof of Lemma 4.7 calls a retraction "a sc⁺-map", and Lemma 4.5 composes sc⁺ with sc-smooth maps without comment.

**Proved in Lean.** `IsScPlus U f`: $f(U) \subseteq F_1$ and the lift $U \to F^1$ is sc-smooth. Then $f(U_m) \subseteq F_{m+1}$; on an sc-domain, $f$ is sc⁺ iff it has an sc-smooth lift into $F^1$, sc⁺ implies sc-smooth, sc⁺ ∘ sc-smooth and sc-smooth ∘ sc⁺ are sc⁺ (the latter through Proposition 1.17), and sc⁺-operators are sc⁺-maps.

- `Polyfold.IsScPlus` — Polyfold/Chapter4/ScPlus.lean, line 104
- `Polyfold.IsScPlus.mem_range_succ` — Polyfold/Chapter4/ScPlus.lean, line 117
- `Polyfold.IsScPlus.iff_exists` — Polyfold/Chapter4/ScPlus.lean, line 125
- `Polyfold.IsScPlus.isScSmooth` — Polyfold/Chapter4/ScPlus.lean, line 136
- `Polyfold.IsScPlus.comp_isScSmooth` — Polyfold/Chapter4/ScPlus.lean, line 155
- `Polyfold.IsScSmooth.comp_isScPlus` — Polyfold/Chapter4/ScPlus.lean, line 165
- `Polyfold.ScPlus.isScPlus` — Polyfold/Chapter4/ScPlus.lean, line 181

*What differs.*
- Findings, item 3.

### V4.8. The derivative of an sc⁺-map is an sc⁺-operator

*hypotheses explicit* · $x$ smooth · Riesz for compact projections

**HWZ (§4.1, proof of Lemma 4.7 (ii), p. 149).** "$Dr(o)$ is a sc⁺-operator, since $r$ is a sc⁺-map. Consequently $Dr(o)$ is a compact operator between every level," and the image of the projection $Dr(o)$ must be finite-dimensional.

**Proved in Lean.** For $f$ sc⁺ on an sc-domain and a smooth $x \in U_1$ there is an sc⁺-operator $S$ with level-$0$ operator $Df(x)$; $Df(x)$ and every level operator of $S$ are compact. A compact continuous linear projection has finite-dimensional range.

- `Polyfold.IsScPlus.exists_scPlus_deriv` — Polyfold/Chapter4/ScPlus.lean, line 190
- `Polyfold.IsScPlus.isCompactOperator_deriv` — Polyfold/Chapter4/ScPlus.lean, line 218
- `Polyfold.finiteDimensional_range_of_isCompactOperator_of_idem` — Polyfold/Chapter4/ScPlus.lean, line 235

*What differs.*
- The chain rule for $f = \iota \circ f^1$ and the uniqueness of the derivative on an sc-domain give $Df(x) = \iota \circ Df^1(x)$ (Findings, item 3).

### V4.9. Definition 4.4: sc⁺-retractions

*restated* · $r(U_m) \subseteq U_{m+1}$ derived

**HWZ (§4.1, Definition 4.4, p. 148).** An sc-smooth retraction $r : U \to U$ is an sc⁺-retraction if $r(U_m) \subseteq U_{m+1}$ for all $m$ and $r : U \to U^1$ is sc-smooth; on an open $V \subseteq X$, if $r : V \to V^1$ is sc-smooth.

**Proved in Lean.** `ScRetraction.IsScPlus`: the retraction is an sc⁺-map on $U$; $r(U_m) \subseteq U_{m+1}$ follows. On an open $V$ of an M-polyfold: $s$ sc-smooth on $V$, $s(V) \subseteq V$, $s \circ s = s$, $s(V) \subseteq X_1$, and $1_0^1 \circ s$ sc-smooth for every junk value.

- `Polyfold.ScRetraction.IsScPlus` — Polyfold/Chapter4/ScPlus.lean, line 263
- `Polyfold.ScRetraction.IsScPlus.mem_lvlSet_succ` — Polyfold/Chapter4/ScPlus.lean, line 266
- `Polyfold.MPolyfold.IsScPlusRetractionOn` — Polyfold/Chapter4/ScPlus.lean, line 587

*What differs.*
- In the M-polyfold form $s(V) \subseteq X_1$ is part of the definition, so that "$r : V \to V^1$" makes sense.

### V4.10. Lemma 4.5

*as in the book*

**HWZ (§4.1, Lemma 4.5, p. 148).** If $t : U \to U$ is an sc⁺-retraction onto $O$, every sc-smooth retraction $s : V \to V$ of a relatively open $V \subseteq C$ with $s(V) = O$ is an sc⁺-retraction.

**Proved in Lean.** If $t$ is an sc⁺-retraction and $s$ an sc-smooth retraction with the same retract, $s$ is an sc⁺-retraction ($s = t \circ s$).

- `Polyfold.lemma_4_5` — Polyfold/Chapter4/ScPlus.lean, line 275

*What differs.*
- The proof writes "$s(V) = 0$" for $s(V) = O$ (Findings, item 7).

### V4.11. Definition 4.6: sc⁺-retracts

*as in the book*

**HWZ (§4.1, Definition 4.6 and the remark after it, pp. 148–149).** $(O, C, E)$ is an sc⁺-retract if there are a relatively open $U \subseteq C$ and an sc⁺-retraction $t : U \to U$ onto $O$; by Lemma 4.5 this is intrinsic.

**Proved in Lean.** `IsScPlusRetract E C O`; every sc-smooth retraction onto an sc⁺-retract is sc⁺, and $O$ is an sc⁺-retract iff it is a retract all of whose retractions are sc⁺.

- `Polyfold.IsScPlusRetract` — Polyfold/Chapter4/ScPlus.lean, line 284
- `Polyfold.IsScPlusRetract.isScPlus` — Polyfold/Chapter4/ScPlus.lean, line 294
- `Polyfold.isScPlusRetract_iff_forall` — Polyfold/Chapter4/ScPlus.lean, line 299

### V4.12. Lemma 4.7: sc⁺-retracts are smooth with finite-dimensional tangent spaces

*hypotheses explicit* · tangent spaces at level-$1$ points

**HWZ (§4.1, Lemma 4.7, p. 149).** If $r$ is an sc⁺-retraction onto $O$: (i) $O = O_\infty$; (ii) at every $o \in O$, $T_oO = Dr(o)E$ is finite-dimensional.

**Proved in Lean.** (i) $O \subseteq E_\infty$. (ii) For a level-$1$ point $o$ over a point of $O$, the range of $Dr(o)$ is finite-dimensional; every point of $O$ has a smooth lift $o_1$ with $T_{o_1}O = Dr(o_1)E_0$ finite-dimensional.

- `Polyfold.lemma_4_7_i` — Polyfold/Chapter4/ScPlus.lean, line 305
- `Polyfold.lemma_4_7_ii` — Polyfold/Chapter4/ScPlus.lean, line 322
- `Polyfold.lemma_4_7_ii_tangentSpace` — Polyfold/Chapter4/ScPlus.lean, line 334

*What differs.*
- The step "$Dr(o)$ is an sc⁺-operator" is V4.8.

### V4.13. Proposition 4.8: sc⁺-retracts

*as in the book*

**HWZ (§4.1, Proposition 4.8, p. 149).** An sc-smooth retract $(O, C, E)$ is an sc⁺-retract iff $O_0 = O_\infty$ and $1_0^1 : O \to O^1$ is sc-smooth.

**Proved in Lean.** `IsScPlusRetract E C O` iff $O \subseteq E_\infty$ and the lift `liftOne` is sc-smooth from $(O, C, E)$ to $(O_1, C_1, E^1)$ (Definition 2.7).

- `Polyfold.proposition_4_8` — Polyfold/Chapter4/ScPlus.lean, line 348

*What differs.*
- The proof ends "the lemma is proved"; in (⇐) only $O \subseteq E_1$ is used (Findings, item 4).

### V4.14. Proposition 4.8 for the charts of an M-polyfold

*not in the book* · the chart form of Proposition 4.8

**HWZ (§4.1, proof of Theorem 4.2, p. 156 ("it follows that $O_0 = O_\infty$ and $1_0^1 : O \to O^1$ is sc-smooth")).** Not in the text. The proof of Theorem 4.2 passes from "$X_0 = X_\infty$ and $1_0^1 : X \to X^1$ sc-smooth" to the same property of the model of a chart.

**Proved in Lean.** In the charts $\varphi$ and $(V_1, \varphi, (O_1, C_1, E^1))$, $1_0^1$ is the lift $O \to O_1$. The model of a chart is an sc⁺-retract iff its domain is smooth and $1_0^1$ is sc-smooth on it; so "$X_0 = X_\infty$, $1_0^1$ sc-smooth" holds iff every chart (equivalently, a cover by charts) is modelled on sc⁺-retracts.

- `Polyfold.MPolyfold.levelChart_toLevelOne` — Polyfold/Chapter4/ScPlus.lean, line 450
- `Polyfold.MPolyfold.proposition_4_8_chart` — Polyfold/Chapter4/ScPlus.lean, line 505
- `Polyfold.MPolyfold.isScSmoothMap_toLevelOne_iff` — Polyfold/Chapter4/ScPlus.lean, line 555
- `Polyfold.MPolyfold.isScSmoothMap_toLevelOne_of_cover` — Polyfold/Chapter4/Characterization.lean, line 502

*What differs.*
- Used in Theorem 4.2 and Proposition 4.15 (4) (Findings, item 4).

### V4.15. The partial quadrant $C_e$ and the neighbourhood $G(e)$

*not in the book* · proves Definition 2.33’s claim

**HWZ (§2.3, Definition 2.33, p. 39 (used in §4.1)).** Not in the text. Definition 2.33 asserts without proof that $C_e$ is a partial quadrant; that $C_e - e = C_e$ and that $C_e$ agrees with $C$ near $e$ are not stated.

**Proved in Lean.** $G(e) = \{v : \lambda_i(v) > 0$ whenever $\lambda_i(e) \ne 0\}$ is open and contains $e \in C$; $C_e$ is a partial quadrant (reordered coordinates); $C_e - e = C_e$; $G(e) \cap C = G(e) \cap C_e$; for $v \in G(e)$ re-centring keeps $d$, the minimal subspace $E_v$ and the cone $C_v$.

- `Polyfold.recentreNbhd` — Polyfold/Chapter4/Recentre.lean, line 86
- `Polyfold.recentreIso` — Polyfold/Chapter4/Recentre.lean, line 200
- `Polyfold.isPartialQuadrant_partialQuadrantAtWith` — Polyfold/Chapter4/Recentre.lean, line 225
- `Polyfold.image_sub_partialQuadrantAtWith` — Polyfold/Chapter4/Recentre.lean, line 129
- `Polyfold.recentreNbhd_inter_eq` — Polyfold/Chapter4/Recentre.lean, line 101
- `Polyfold.degIndex_sub_recentre` — Polyfold/Chapter4/Recentre.lean, line 258
- `Polyfold.minimalSubspaceWith_recentreIso` — Polyfold/Chapter4/Recentre.lean, line 267
- `Polyfold.partialQuadrantAtWith_recentreIso` — Polyfold/Chapter4/Recentre.lean, line 284

*What differs.*
- Findings, items 1 (b), (c), 2.

### V4.16. Translations by smooth vectors and re-centred retracts

*not in the book* · $e$ must be smooth

**HWZ (not in the text (§4.1), p. 147).** Not in the text. Charts "with $\psi(x) = 0$" are used in Theorems 4.2, 4.18, 4.22 and Lemma 5.11; translating a chart requires this.

**Proved in Lean.** Translation by $a \in E_\infty$ is sc-smooth; for $U \subseteq G(e) \cap C$ relatively open and $e$ smooth, $v \mapsto v - e$ is an sc-diffeomorphism onto the relatively open $U - e \subseteq C_e$; restricting $r$ to $U \cap r^{-1}(W) \cap W$ keeps tameness; $((O \cap G(e)) - e, C_e, E)$ is a (tame) retract when $(O, C, E)$ is.

- `Polyfold.isScSmooth_add_const` — Polyfold/Chapter4/Recentre.lean, line 310
- `Polyfold.isScSmooth_sub_const` — Polyfold/Chapter4/Recentre.lean, line 320
- `Polyfold.relOpen_translate` — Polyfold/Chapter4/Recentre.lean, line 328
- `Polyfold.isScDiffeoQuadrant_translate` — Polyfold/Chapter4/Recentre.lean, line 350
- `Polyfold.ScRetraction.restrictIn` — Polyfold/Chapter4/Recentre.lean, line 373
- `Polyfold.ScRetraction.restrictIn_isTame` — Polyfold/Chapter4/Recentre.lean, line 421
- `Polyfold.isScRetract_recentre` — Polyfold/Chapter4/Recentre.lean, line 436
- `Polyfold.isTameRetract_recentre` — Polyfold/Chapter4/Recentre.lean, line 450

*What differs.*
- Translation by $e$ preserves every level only for smooth $e$ (Findings, item 1 (a)).

### V4.17. Charts centred at a smooth point

*not in the book* · only at smooth points · model in $C_{\varphi(x)}$

**HWZ (§4.1, Theorem 4.2 (ii), p. 147; proofs of Theorems 4.18, 4.22).** Not in the text. Theorem 4.2 (ii) and the proofs of Theorems 4.18, 4.22 use charts with $\psi(x) = 0$; the text never says how they are obtained from the atlas.

**Proved in Lean.** `MChart.recentre`: $\varphi_e = \varphi - e$ on $V \cap \varphi^{-1}(G(e))$, modelled on $((O \cap G(e)) - e, C_e, E)$, is a chart of $X$ with $\varphi_e(x) = 0$ for $\varphi(x) = e$, the same degeneracy index, and a tame model if $\varphi$ has one. Every smooth point of a chart domain is the centre of such a chart; in a tame $X$ of a tame one.

- `Polyfold.MChart.recentre` — Polyfold/Chapter4/Recentre.lean, line 494
- `Polyfold.MChart.recentre_isChart` — Polyfold/Chapter4/Recentre.lean, line 537
- `Polyfold.MChart.recentre_apply_self` — Polyfold/Chapter4/Recentre.lean, line 530
- `Polyfold.MChart.isTameRetract_recentre` — Polyfold/Chapter4/Recentre.lean, line 544
- `Polyfold.MChart.chartDegIndex_recentre` — Polyfold/Chapter4/Recentre.lean, line 552
- `Polyfold.MPolyfold.exists_centredChart` — Polyfold/Chapter4/Recentre.lean, line 1080
- `Polyfold.MPolyfold.IsTame.exists_centredChart` — Polyfold/Chapter4/Recentre.lean, line 1096

*What differs.*
- Findings, item 1.

### V4.18. Strong bundle charts centred at a smooth point

*not in the book* · only the base is translated

**HWZ (§5.1, Lemma 5.11, p. 173 (uses them)).** Not in the text. Lemma 5.11 uses a strong bundle chart centred at a given point.

**Proved in Lean.** Over $\varphi_e$: $R_e(u, h) = (r(u + e) - e, \Gamma(u + e, h))$, $\Phi_e(y) = (\Phi(y)_1 - e, \Phi(y)_2)$; $c_e$ is compatible with every chart $c$ is compatible with (continuous projection) and is a strong bundle chart; every smooth point of the base is the centre of one.

- `Polyfold.StrongBundleChart.recentre` — Polyfold/Chapter4/Recentre.lean, line 806
- `Polyfold.StrongBundleChart.Compatible.recentre` — Polyfold/Chapter4/Recentre.lean, line 934
- `Polyfold.StrongBundle.IsChart.recentre` — Polyfold/Chapter4/Recentre.lean, line 1057
- `Polyfold.StrongBundle.IsChart.exists_centred` — Polyfold/Chapter4/Recentre.lean, line 1110

*What differs.*
- $(e, 0)$ is smooth in $E \oplus F$ and $E \oplus F^1$, so the compatibility on $[0]$ and $[1]$ is kept (Findings, item 1).

### V4.19. The mean value estimate for an sc⁺-retraction

*restated* · on the convex $C_{k+1} \cap B(u_0, r)$

**HWZ (§4.1, proofs of Lemmas 4.11, 4.12, (76)–(77), pp. 154–155).** Since $t$ is sc⁺, $u \mapsto (1 - p)t(u)$ is $C^1$ between the $1$-levels; $\|(1 - p)Dt(u)\|_{\mathcal L(E_1)} \le 1/2$ for $|u|_1 < \varepsilon_1$, and the differences of $t$ are written as integrals of $Dt$ along segments.

**Proved in Lean.** For every $k$, $t : U_{k+1} \to E_{k+1}$ is differentiable with $Dt(x) \in \mathcal L(E_{k+1})$ continuous in the operator norm; for $u_0 \in U_{k+1}$ and $\theta > 0$ there is $r > 0$ with $C_{k+1} \cap B(u_0, r) \subseteq U_{k+1}$, $\|Dt(z) - Dt(u_0)\| \le \theta$, and $|t(z') - t(z) - Dt(u_0)(z' - z)|_{k+1} \le \theta|z' - z|_{k+1}$ there.

- `Polyfold.ScRetraction.lvlMap` — Polyfold/Chapter4/ScPlusGraph.lean, line 150
- `Polyfold.ScRetraction.lvlDeriv` — Polyfold/Chapter4/ScPlusGraph.lean, line 154
- `Polyfold.ScRetraction.IsScPlus.hasFDerivWithinAt_lvlMap` — Polyfold/Chapter4/ScPlusGraph.lean, line 170
- `Polyfold.ScRetraction.IsScPlus.continuousOn_lvlDeriv` — Polyfold/Chapter4/ScPlusGraph.lean, line 177
- `Polyfold.ScRetraction.IsScPlus.exists_mvt` — Polyfold/Chapter4/ScPlusGraph.lean, line 280
- `Polyfold.exists_norm_sub_sub_le_of_hasFDerivWithinAt` — Polyfold/Chapter4/ScPlusGraph.lean, line 107

*What differs.*
- $U_{k+1}$ need not be convex; the integrals are the mean value inequality on $C_{k+1} \cap B$ (Findings, item 22).

### V4.20. Proposition 4.9: an sc⁺-retract is a graph over its tangent space

*hypotheses explicit* · $Y$ closed · $p$ the projection along $Y$ · direct proof, not via Lemma 4.10

**HWZ (§4.1, Proposition 4.9, p. 150 (proof pp. 150–156)).** Let $t : U \to U$ be an sc⁺-retraction onto $O \ni 0$ with $T_0O$ in good position to $C$, $Y$ a good complement, $E = T_0O \oplus Y$, and $p = Dt(0) : E \to T_0O$ "the sc-projection". There are open neighbourhoods $U$ of $0$ in $O$ and $V$ of $0$ in $T_0O \cap C$ such that $p : U \to V$ is an sc-diffeomorphism; $(V, T_0O \cap C, T_0O)$ is a local model.

**Proved in Lean.** For $N = T_0O$ in good position, $Y$ a **closed** good complement and $p$ the projection **along $Y$** ($p = 1$ on $N$, $0$ on $Y$): there are $W$ open in $E_0$, $V$ relatively open in $N \cap C$ and $\Gamma$ sc-smooth on $V$ with $p \circ \Gamma = 1$, $\Gamma(a) - a \in Y$, $\Gamma(V) = O \cap W$, $\Gamma \circ p = 1$ on $O \cap W$, $\Gamma(0) = 0$, and $p$, $\Gamma$ sc-smooth between $(O \cap W, C, E)$ and $(V, N \cap C, N)$.

- `Polyfold.proposition_4_9` — Polyfold/Chapter4/ScPlusGraph.lean, line 1600
- `Polyfold.finiteDimensional_tangentSpace_zero` — Polyfold/Chapter4/ScPlusGraph.lean, line 1582
- `Polyfold.GraphData` — Polyfold/Chapter4/ScPlusGraph.lean, line 325

*What differs.*
- $Dt(0)$ projects along its own kernel, which nothing relates to $Y$; Lemma 4.12 needs the projection along $Y$ (Findings, item 20). $Y$ closed: Definition 3.21 asks for an sc-complement, the formal good complement records only the splitting (item 21).
- The text's route (Lemma 4.10, Corollary 3.47) gives the graph only as a germ over a complement of its own choice; the proof is direct, V4.21–V4.25 (item 22). Where the proposition is applied, the closed complement is chosen.

### V4.21. Lemma 4.11: uniqueness

*restated* · uniqueness among points of $O$

**HWZ (§4.1, Lemma 4.11, p. 154).** Let $\mathbf f(a + y) = 0$ with $|a|_0, |y|_0 < \varepsilon$; if $\varepsilon$ is small, $y = \delta(a)$.

**Proved in Lean.** On every level $k + 1$: $(1 - p)Dt(0) = 0$ and $Dt(0) = 1$ on $N$; near $0$, $|(1 - p)(u' - u)|_{k+1} \le \|1 - p\|\theta|u' - u|_{k+1}$ for $u, u' \in O_{k+1}$; two such points with $p(u) = p(u')$ coincide.

- `Polyfold.GraphData.qL_lvlDeriv_zero` — Polyfold/Chapter4/ScPlusGraph.lean, line 466
- `Polyfold.GraphData.lvlDeriv_zero_of_mem_N` — Polyfold/Chapter4/ScPlusGraph.lean, line 471
- `Polyfold.GraphData.exists_contraction_radius` — Polyfold/Chapter4/ScPlusGraph.lean, line 520
- `Polyfold.GraphData.eq_of_p_eq` — Polyfold/Chapter4/ScPlusGraph.lean, line 546

*What differs.*
- The text's statement presupposes the $\delta$ of Corollary 3.47 (Findings, item 23).

### V4.22. Lemma 4.12: existence

*restated* · the point is constructed

**HWZ (§4.1, Lemma 4.12, pp. 154–155).** Let $\mathbf f(a + \delta(a)) = 0$ and $|a|_0 < \varepsilon$; if $\varepsilon$ is small, $a + \delta(a) \in O$.

**Proved in Lean.** With $\varepsilon' = \varepsilon/(\|\iota_1\|\|\mathrm{lift}_N\| + 1)$ and the constants of V4.21 small: every $a \in N \cap C$ with $|a|_1 < \rho$ has $u \in O_1$ with $p(u) = a$, $u - a \in Y$, $|u - a|_1 \le \varepsilon'|a|_1$, $|u|_1 < r$.

- `Polyfold.GraphData.eps'` — Polyfold/Chapter4/ScPlusGraph.lean, line 492
- `Polyfold.GraphData.exists_graph_point` — Polyfold/Chapter4/ScPlusGraph.lean, line 570

*What differs.*
- $u = a + y$, $y$ the fixed point of $y \mapsto (1 - p)t(a + y)$ on $\{y \in Y_1 : |y|_1 \le \varepsilon'|a|_1\}$, where $a + y \in C$; then the text's argument gives $t(u) = u$ (Findings, item 24).

### V4.23. Proposition 4.9: $p(O \cap W) \subseteq C$ and the neighbourhoods

*not in the book* · $p(O \cap W) \subseteq C$ not in the text

**HWZ (§4.1, end of the proof of Proposition 4.9, p. 156).** Not in the text. The text sets $V = \{a \in T_0O \cap C : |a|_0 < \varepsilon\}$ and $U = \{a + \delta(a) : a \in V\}$, "an open set in $O$"; that $p$ maps points of $O$ near $0$ into $C$ is not checked.

**Proved in Lean.** (a) $u \in O_1$ with $|(1 - p)u|_1 \le \kappa|u|_1$, $\kappa \le 1/2$, $2\|\iota_1\|\kappa\|\mathrm{lift}_N\| \le \varepsilon$ has $p(u) \in C$. (b) For every $\theta_0 > 0$: $W = B_0(0, \delta_0) \cap p^{-1}(V')$, $V = V' \cap C$, $\Gamma$ with $\Gamma(V) = O \cap W$, $p \circ \Gamma = 1$, $\Gamma \circ p = 1$ on $O \cap W$, level-$1$ bounds, $\|Dt - Dt(0)\| \le \theta_0$ near $0$.

- `Polyfold.GraphData.p_mem_C` — Polyfold/Chapter4/ScPlusGraph.lean, line 706
- `Polyfold.GraphData.Nbhd` — Polyfold/Chapter4/ScPlusGraph.lean, line 741
- `Polyfold.GraphData.exists_nbhd` — Polyfold/Chapter4/ScPlusGraph.lean, line 803
- `Polyfold.GraphData.Nbhd.image_V` — Polyfold/Chapter4/ScPlusGraph.lean, line 782
- `Polyfold.GraphData.Nbhd.injOn_p` — Polyfold/Chapter4/ScPlusGraph.lean, line 795

*What differs.*
- Open on level $0$, controlled on level $1$ through the continuity of $t : U \to E_1$ at $0$ (Findings, items 25, 26).

### V4.24. Proposition 4.9: continuity of $\Gamma$ and the frame formula

*not in the book* · estimate at $\Gamma(a)$, not at $0$

**HWZ (§4.1, proof of Proposition 4.9, p. 156).** Not in the text. The text takes the regularity of $a \mapsto a + \delta(a)$ from Corollary 3.47, which gives it only as a germ.

**Proved in Lean.** $\Gamma$ is Lipschitz on level $1$ and continuous into every level. For $\|Dt(u) - Dt(0)\|$ small, $A(u) = p \circ Dt(u)|_N$ is invertible and $T_uO \cap Y = 0$; $\Gamma$ is differentiable into every level with $D\Gamma(a) = Dt(\Gamma(a))|_N \circ (p \circ Dt(\Gamma(a))|_N)^{-1}$. Abstractly: a continuous right inverse of $q$ with values in the fixed points of $s$ has derivative $B$ when $(1 - Bq)Ds(u_0) = 0$.

- `Polyfold.GraphData.Nbhd.norm_Γ_lvl_one_sub_le` — Polyfold/Chapter4/ScPlusGraph.lean, line 1312
- `Polyfold.GraphData.Nbhd.continuousOn_Γ_lvl` — Polyfold/Chapter4/ScPlusGraph.lean, line 1348
- `Polyfold.norm_sub_le_of_projection` — Polyfold/Chapter4/ScPlusGraph.lean, line 972
- `Polyfold.hasFDerivWithinAt_of_projection` — Polyfold/Chapter4/ScPlusGraph.lean, line 1000
- `Polyfold.GraphData.A_injective` — Polyfold/Chapter4/ScPlusGraph.lean, line 1113
- `Polyfold.GraphData.eq_zero_of_mem_Y_of_scDeriv_eq` — Polyfold/Chapter4/ScPlusGraph.lean, line 1169
- `Polyfold.GraphData.scDeriv_sub_frame` — Polyfold/Chapter4/ScPlusGraph.lean, line 1201
- `Polyfold.GraphData.Nbhd.hasFDerivWithinAt_Γ_lvl` — Polyfold/Chapter4/ScPlusGraph.lean, line 1370

*What differs.*
- The mean value estimate is used at $u_0 = \Gamma(a)$ with $1 - B_{u_0}p$, which is why the regularity holds on the fixed $V$ (Findings, item 27).

### V4.25. Proposition 4.9: the $C^k$-bootstrap and the sc-diffeomorphism

*not in the book* · level loss does not accumulate

**HWZ (§4.1, end of the proof of Proposition 4.9, p. 156).** Not in the text. "The map $p$ ... is a sc-diffeomorphism ... having the sc-smooth map $a \mapsto a + \delta(a)$ as its inverse."

**Proved in Lean.** $(x, w) \mapsto Dt_{j+1}(x)w$ is $C^k$ on $U_{j+k+1} \times E_{j+k+1}$; $\Gamma$ is $C^k$ into every level for every $k$, hence sc-smooth on $V$ (Proposition 1.19); $(V, N \cap C, N)$ is a local model; $p$, $\Gamma$ are sc-smooth between the retracts.

- `Polyfold.GraphData.contDiffOn_lvlDeriv_apply` — Polyfold/Chapter4/ScPlusGraph.lean, line 1425
- `Polyfold.GraphData.Nbhd.contDiffOn_Γ_lvl` — Polyfold/Chapter4/ScPlusGraph.lean, line 1498
- `Polyfold.GraphData.Nbhd.isScSmooth_Γ` — Polyfold/Chapter4/ScPlusGraph.lean, line 1532
- `Polyfold.GraphData.Nbhd.V_isRelOpenInQuadrant` — Polyfold/Chapter4/ScPlusGraph.lean, line 1250
- `Polyfold.GraphData.Nbhd.p_isScSmoothRetractMap` — Polyfold/Chapter4/ScPlusGraph.lean, line 1558
- `Polyfold.GraphData.Nbhd.Γ_isScSmoothRetractMap` — Polyfold/Chapter4/ScPlusGraph.lean, line 1566

*What differs.*
- Derivatives of $t$ meet only the smooth finite-dimensional $N$ (Findings, item 27).

### V4.26. Charts composed with an sc-diffeomorphism between retracts

*not in the book* · the compatibility the text skips

**HWZ (§4.1, proof of Theorem 4.2, p. 157).** Not in the text. "Carrying out this construction around every point $x \in X$, we obtain a smoothly compatible atlas."

**Proved in Lean.** For a chart $\varphi$ onto $(O, C, E)$ and mutually inverse maps $f$, $g$ sc-smooth between $(O, C, E)$ and $(O', C', E')$, $f \circ \varphi$ is a chart onto $(O', C', E')$, a chart of the M-polyfold when $\varphi$ is.

- `Polyfold.MChart.compRetract` — Polyfold/Chapter4/Characterization.lean, line 162
- `Polyfold.MChart.compRetract_isChart` — Polyfold/Chapter4/Characterization.lean, line 200

*What differs.*
- Findings, item 55.

### V4.27. Theorem 4.2, (i) ⇒ (ii)

*hypotheses explicit* · the centred chart is constructed

**HWZ (§4.1, proof of Theorem 4.2, p. 156).** The identity of $U$ is a tame retraction, $U = U_\infty$ and $1_0^1 : U \to U^1$ is sc-smooth; so $X_0 = X_\infty$, $1_0^1$ is sc-smooth "and the statement (ii) follows".

**Proved in Lean.** Points of corner charts are smooth. Every $x$ in a corner chart lies in a chart $\psi$ of $X$ with $\psi(x) = 0$, modelled on a relatively open subset of $C_{\chi(x)}$: tame (identity retraction), $T_0O$ the whole space, in good position (complement $0$).

- `Polyfold.MChart.IsCornerChart.mem_smooth` — Polyfold/Chapter4/Characterization.lean, line 273
- `Polyfold.MChart.IsCornerChart.exists_centred` — Polyfold/Chapter4/Characterization.lean, line 550
- `Polyfold.MChart.IsCornerChart.exists_centred_tame` — Polyfold/Chapter4/Characterization.lean, line 570
- `Polyfold.tangentSpace_relOpen` — Polyfold/Chapter4/Characterization.lean, line 121
- `Polyfold.isInGoodPosition_top` — Polyfold/Chapter4/Characterization.lean, line 135

*What differs.*
- The text's proof does not produce the chart with $\psi(x) = 0$, nor $T_0O$ and its good position (Findings, item 53).

### V4.28. Theorem 4.2, (ii) ⇒ (i)

*hypotheses explicit* · closed complement chosen · tameness of the charts unused

**HWZ (§4.1, proof of Theorem 4.2, pp. 156–157).** By Proposition 4.8 the model of $\psi$ is an sc⁺-retract; Proposition 4.9 gives the sc-diffeomorphism $p : O' \to V$, and $p \circ \psi$ is a chart onto $(V, T_0O \cap C, T_0O)$; these charts form a smoothly compatible atlas.

**Proved in Lean.** If all points are smooth and $1_0^1$ is sc-smooth: for a chart $\psi$ with $\psi(x) = 0$ and $N = T_0O$ finite-dimensional, in good position, there are a closed good complement, the projection $p$ along it, and the chart $p \circ \psi$ on $\psi^{-1}(W)$, a corner chart of $X$ with $(p \circ \psi)(x) = 0$; such charts at every point give a corner structure.

- `Polyfold.exists_proj_goodComplement` — Polyfold/Chapter3/GoodComplementProjection.lean, line 408
- `Polyfold.CornerChartData` — Polyfold/Chapter4/Characterization.lean, line 600
- `Polyfold.exists_cornerChartData` — Polyfold/Chapter4/Characterization.lean, line 690
- `Polyfold.CornerChartData.chart` — Polyfold/Chapter4/Characterization.lean, line 647
- `Polyfold.CornerChartData.chart_isCornerChart` — Polyfold/Chapter4/Characterization.lean, line 664
- `Polyfold.CornerChartData.chart_isChart` — Polyfold/Chapter4/Characterization.lean, line 669
- `Polyfold.MPolyfold.theorem_4_2_chart` — Polyfold/Chapter4/Characterization.lean, line 723
- `Polyfold.MPolyfold.hasCornerStructure_of_centred` — Polyfold/Chapter4/Characterization.lean, line 742

*What differs.*
- The closed good complement is chosen by Proposition 3.22's normal form, so nothing is added (Findings, item 54); the compatibility is V4.26.

### V4.29. Definition 4.13: smooth finite-dimensional submanifolds

*as in the book*

**HWZ (§4.2, Definition 4.13, p. 157).** $A \subseteq X$ is a smooth finite-dimensional submanifold if every $a \in A$ has an open $V \ni a$ and an sc⁺-retraction $s : V \to V$ onto $s(V) = A \cap V$.

**Proved in Lean.** `IsSmoothSubmanifold A`: every $a \in A$ has an open $V \ni a$ and an sc⁺-retraction on $V$ (V4.9) with $s(V) = A \cap V$. $A$ is a sub-M-polyfold with the induced structure.

- `Polyfold.MPolyfold.IsSmoothSubmanifold` — Polyfold/Chapter4/Submanifolds.lean, line 751
- `Polyfold.MPolyfold.SubmanifoldData` — Polyfold/Chapter4/Submanifolds.lean, line 738
- `Polyfold.MPolyfold.isSmoothSubmanifold_iff` — Polyfold/Chapter4/Submanifolds.lean, line 757
- `Polyfold.MPolyfold.SubmanifoldData.toSubData` — Polyfold/Chapter4/Submanifolds.lean, line 772
- `Polyfold.MPolyfold.IsSmoothSubmanifold.isSubMPolyfold` — Polyfold/Chapter4/Submanifolds.lean, line 941

*What differs.*
- Findings, item 60.

### V4.30. The sc⁺-retraction of a submanifold in a chart

*hypotheses explicit* · the set $W$ of Proposition 2.21 · sc⁺ read in charts of $X$, $X^1$

**HWZ (§4.2, proof of Theorem 4.18, pp. 160–161).** "Taking $V$ and $U$ small, we may assume $V = \varphi^{-1}(O)$"; $t = \varphi \circ s \circ \varphi^{-1} \circ r$ is a retraction, "a sc⁺-retraction since $s$ is a sc⁺-retraction", onto $\varphi(A \cap V)$.

**Proved in Lean.** For $W = V \cap \operatorname{dom}\varphi \cap s^{-1}(V \cap \operatorname{dom}\varphi)$: the lift of $\varphi \circ s \circ \varphi^{-1}$ to $E^1$ is sc-smooth on $\varphi(W)$; for every retraction $r$ onto $O$ there is an sc⁺-retraction $t = \varphi \circ s \circ \varphi^{-1} \circ r$ on $U \cap r^{-1}(G)$ onto $\varphi(W \cap A)$; so $\varphi(W \cap A)$ is an sc⁺-retract of smooth points.

- `Polyfold.MPolyfold.SubmanifoldData.isScSmoothRetractMap_lift` — Polyfold/Chapter4/Submanifolds.lean, line 800
- `Polyfold.MPolyfold.SubmanifoldData.exists_chartRetraction` — Polyfold/Chapter4/Submanifolds.lean, line 823
- `Polyfold.MPolyfold.SubmanifoldData.isScPlusRetract_image` — Polyfold/Chapter4/Submanifolds.lean, line 855
- `Polyfold.MPolyfold.SubmanifoldData.apply_mem_smooth` — Polyfold/Chapter4/Submanifolds.lean, line 863

*What differs.*
- Findings, item 60.

### V4.31. Remark 4.14 in a chart

*restated* · $T_aX$ read in a chart (G.7)

**HWZ (§4.2, Remark 4.14, p. 157).** $s(V) \subseteq X_\infty$; $T_aA = Ts(a)(T_aX)$ is the image of the sc⁺-operator $Ts(a)$, hence finite-dimensional.

**Proved in Lean.** At $a \in A \cap V \cap \operatorname{dom}\varphi$ and $z$ over $\varphi(a)$: $z$ is smooth; the tangent map of $\varphi \circ s \circ \varphi^{-1}$ maps $T_zO$ onto $T_z(\varphi(W \cap A))$; $T_z(\varphi(W \cap A)) \subseteq T_zO$ and is finite-dimensional.

- `Polyfold.MPolyfold.SubmanifoldData.remark_4_14` — Polyfold/Chapter4/Submanifolds.lean, line 877

*What differs.*
- The sc⁺-operator is $Dt(z)$ for the chart retraction of V4.30, not $Ts(a)$ (Findings, item 61).

### V4.32. Remark 4.14: points with $d_X = 0$

*narrower* · local form: G.33

**HWZ (§4.2, Remark 4.14, p. 157).** Near points $a \in A$ with $d_X(a) = 0$, $A$ is a smooth finite-dimensional manifold in the classical sense; the same where $T_aA$ is in good position.

**Proved in Lean.** Every subspace is in good position to the whole space; $C_e = E$ where $d_C(e) = 0$; at $a \in A$ with $d_X(a) = 0$, $A$ is in good position; if $d_X = 0$ on all of $A$, $A$ has a corner structure (no tameness of $X$).

- `Polyfold.isInGoodPosition_univ` — Polyfold/Chapter4/Submanifolds.lean, line 531
- `Polyfold.partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero` — Polyfold/Chapter4/Submanifolds.lean, line 539
- `Polyfold.MPolyfold.isGoodPositionAt_of_degIndex_eq_zero` — Polyfold/Chapter4/Submanifolds.lean, line 1499
- `Polyfold.MPolyfold.hasCornerStructure_of_degIndex_eq_zero` — Polyfold/Chapter4/Submanifolds.lean, line 1530

*What differs.*
- The local form, for the open piece $A \cap \{d_X = 0\}$, is not formalized (G.33); the case of good position is Theorem 4.18 (V4.41).

### V4.33. Proposition 4.15 (1)

*hypotheses explicit* · two statements separated

**HWZ (§4.2, Proposition 4.15 (1), p. 158).** $A \subseteq X_\infty$, and $A$ inherits the M-polyfold structure of $X$; $A$ has a tangent space at every point and $d_A$ is defined.

**Proved in Lean.** $A \subseteq X_\infty$; the levels of the induced structure are the traces of those of $X$; every point of $A$ is smooth for the induced structure.

- `Polyfold.MPolyfold.IsSmoothSubmanifold.subset_smoothSet` — Polyfold/Chapter4/Submanifolds.lean, line 953
- `Polyfold.MPolyfold.IsSmoothSubmanifold.mem_levelSet_subPolyfold_iff` — Polyfold/Chapter4/Submanifolds.lean, line 965
- `Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_1` — Polyfold/Chapter4/Submanifolds.lean, line 995

*What differs.*
- "A sc⁺-retraction $s$ has its image in $X_\infty$" is Lemma 4.7 (i) through the chart retraction (Findings, item 62).

### V4.34. Proposition 4.15 (2): $A$ is locally closed

*restated* · the text’s definition is garbled

**HWZ (§4.2, Proposition 4.15 (2), p. 158).** $A$ is locally closed in $X$ (defined as: every $a$ has an open $V(a)$ such that $b \in V(a)$ belongs to $A$ if $U \cap A \ne \emptyset$ for all open $U \ni b$).

**Proved in Lean.** `IsLocallyClosed A` (Mathlib: an intersection of an open and a closed set).

- `Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_2` — Polyfold/Chapter4/Submanifolds.lean, line 1007

*What differs.*
- Read as $V(a) \cap \overline A \subseteq A$; a filter replaces the sequence, so no metrizability is needed (Findings, item 63).

### V4.35. Proposition 4.15 (3): $\partial A \subseteq \partial X$

*as in the book*

**HWZ (§4.2, Proposition 4.15 (3), p. 158).** $\partial A = \{a \in A : d_A(a) \ge 1\} \subseteq \partial X$.

**Proved in Lean.** The boundary of the induced M-polyfold $A$ lies in $\partial X$ (by $d_A \le d_X$, Lemma 2.26).

- `Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_3` — Polyfold/Chapter4/Submanifolds.lean, line 1030

*What differs.*
- Typo "$d_A(x)$" for $d_A(a)$ (Findings, item 64).

### V4.36. Proposition 4.15 (4): $1_0^1 : A \to A^1$ is sc-smooth

*as in the book*

**HWZ (§4.2, Proposition 4.15 (4), p. 158).** $1_0^1 : A \to A^1$ is sc-smooth.

**Proved in Lean.** For the induced structure: every point of $A$ is smooth and `toLevelOne` is sc-smooth (any junk value).

- `Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_4` — Polyfold/Chapter4/Submanifolds.lean, line 981

*What differs.*
- The text: "the postulated sc⁺-retraction is the identity on the retract $A$"; the proof uses V4.30 and V4.14 (Findings, item 62).

### V4.37. Tangent spaces of sub-retracts

*not in the book*

**HWZ (not in the text (§4.2), p. 159).** Not in the text. Used implicitly whenever $T_aA$ is compared with $T_aX$ or carried from one chart to another.

**Proved in Lean.** $T_z(Q \cap K) = T_zQ$ for open $K$; $T_zQ \subseteq T_zO$ for retracts $Q \subseteq O$; $D(F \circ r)(z)$ maps $T_zQ$ into $T_{F(z)}Q'$ when $F(Q) \subseteq Q'$.

- `Polyfold.tangentSpace_inter_isOpen` — Polyfold/Chapter4/Submanifolds.lean, line 129
- `Polyfold.tangentSpace_subset_of_subset` — Polyfold/Chapter4/Submanifolds.lean, line 145
- `Polyfold.scDeriv_mem_tangentSpace_of_subset` — Polyfold/Chapter4/Submanifolds.lean, line 171

### V4.38. Definition 4.16: good position, in a chart

*restated* · in a chart (G.7) · tameness not needed

**HWZ (§4.2, Definition 4.16, p. 159).** A smooth finite-dimensional submanifold $A$ of a tame $X$ is in good position at $a$ if $T_aA$ is in good position to the partial quadrant $C_aX$ in $T_aX$.

**Proved in Lean.** `IsGoodPositionRetractAt`: $T_zQ$ in good position to $C_z$ inside $T_zO$. `IsGoodPositionAt A a`: this for $Q = \varphi(W \cap A)$ in some chart, data, presentation and lift; explicitly, $Dt(z)E$ in good position to $C_z$ inside $Dr(z)E$.

- `Polyfold.IsGoodPositionRetractAt` — Polyfold/Chapter4/Submanifolds.lean, line 222
- `Polyfold.MPolyfold.SubmanifoldData.IsGoodPositionChart` — Polyfold/Chapter4/Submanifolds.lean, line 1230
- `Polyfold.MPolyfold.IsGoodPositionAt` — Polyfold/Chapter4/Submanifolds.lean, line 1242
- `Polyfold.MPolyfold.SubmanifoldData.isGoodPositionChart_iff` — Polyfold/Chapter4/Submanifolds.lean, line 1293

*What differs.*
- Findings, item 66.

### V4.39. Definition 4.16 does not depend on the chart

*not in the book* · Lemma 6.B of the exposition

**HWZ (§4.2, Definition 4.16, p. 159 (implicit)).** Not in the text. Definition 4.16 is stated in $T_aX$; that a chart form does not depend on the chart is taken for granted.

**Proved in Lean.** Good position of a sub-retract is carried by germs of sc-diffeomorphisms; good position at $a$ holds for every data, chart, presentation and lift, and is equivalent to the condition for all of them.

- `Polyfold.IsGoodPositionRetractAt.transport` — Polyfold/Chapter4/Submanifolds.lean, line 247
- `Polyfold.MPolyfold.chart_change_of_transport` — Polyfold/Chapter4/Submanifolds.lean, line 1065
- `Polyfold.MPolyfold.isGoodPositionRetractAt_chart_change` — Polyfold/Chapter4/Submanifolds.lean, line 1177
- `Polyfold.MPolyfold.IsGoodPositionAt.isGoodPositionChart` — Polyfold/Chapter4/Submanifolds.lean, line 1255
- `Polyfold.MPolyfold.isGoodPositionAt_iff_forall` — Polyfold/Chapter4/Submanifolds.lean, line 1274

*What differs.*
- Through Proposition 2.30 and Lemma 3.45 (Findings, item 66).

### V4.40. Definition 4.17: tame submanifolds

*as in the book*

**HWZ (§4.2, Definition 4.17, p. 159).** A smooth finite-dimensional submanifold is tame if, with its induced M-polyfold structure, it is tame.

**Proved in Lean.** `IsTameSubmanifold A`: a smooth finite-dimensional submanifold whose induced structure is tame.

- `Polyfold.MPolyfold.IsTameSubmanifold` — Polyfold/Chapter4/Submanifolds.lean, line 1390

### V4.41. Theorem 4.18: submanifolds in good position are manifolds with corners

*as in the book* · through Theorem 4.2

**HWZ (§4.2, Theorem 4.18, p. 159 (proof pp. 160–161)).** Let $X$ be tame and $A \subseteq X$ a smooth finite-dimensional submanifold in good position at every point. Then the induced structure on $A$ is equivalent to a smooth manifold with boundary with corners; in particular $A$ is tame.

**Proved in Lean.** For $X$ tame and `IsSmoothSubmanifold A` with `IsGoodPositionAt A a` for all $a \in A$: the induced structure has `HasCornerStructure` and `IsTameSubmanifold A`.

- `Polyfold.MPolyfold.theorem_4_18` — Polyfold/Chapter4/Submanifolds.lean, line 1485
- `Polyfold.MPolyfold.hasCornerStructure_of_centred_isInGoodPosition` — Polyfold/Chapter4/Submanifolds.lean, line 1400
- `Polyfold.MPolyfold.IsGoodPositionAt.isInGoodPosition_of_tame` — Polyfold/Chapter4/Submanifolds.lean, line 1441

*What differs.*
- The proof cites "Proposition 4.2", takes $p = Dt(0)$, assumes "$V = \varphi^{-1}(O)$" and writes $\varphi^{-1}(V_0) \cap A$ for $(p \circ \varphi)^{-1}(V_0) \cap A$; the formal proof supplies the centred chart, the chart retraction, the closed complement and the compatibility (Findings, item 68).

### V4.42. Lemma 4.19

*hypotheses explicit* · the step “$z \in Z \subset C$” is false

**HWZ (§4.2, Lemma 4.19, p. 160).** $N = T\varphi(a)(T_aA)$ is in good position to $C$, and $Y \oplus Z$ is a good complement ($Z \subseteq C$ the sc-complement of $T_0O$ of Proposition 2.35).

**Proved in Lean.** For a bounded idempotent $\pi$ with $(1 - \pi)E_0$ in the minimal subspace at $0$ and $N$ in good position to $C$ inside $\pi E_0$: $N$ is in good position to $C$, and $Y \oplus (1 - \pi)E_0$ is a good complement for every good complement $Y$ inside $\pi E_0$, with constant $\varepsilon/(\|\pi\| + 1)$.

- `Polyfold.isGoodComplement_sup_range` — Polyfold/Chapter4/Submanifolds.lean, line 648
- `Polyfold.lemma_4_19` — Polyfold/Chapter4/Submanifolds.lean, line 713
- `Polyfold.IsInGoodPositionIn.isInGoodPosition` — Polyfold/Chapter3/GoodPositionGerm.lean, line 139

*What differs.*
- $n + y \in C$ from $n + y + z \in C$ needs $-z \in C$ ($C = [0, \infty)$, $z = 1$, $n + y = -\frac12$); true because $Z \subseteq E_0 \subseteq C \cap (-C)$ at the corner of the centred chart (Findings, item 69).

### V4.43. Remark 4.20: good position is an open condition

*hypotheses explicit* · $X$ tame

**HWZ (§4.2, Remark 4.20, p. 161).** If $A$ is in good position at $a$, there is an open $V(a) \subseteq X$ such that $A$ is in good position at every $b \in V(a) \cap A$ (Proposition 4.9 and Lemma 3.55: "the tangent spaces of $A$ move only slowly").

**Proved in Lean.** For $X$ tame: there is an open $U \ni a$ with `IsGoodPositionAt A b` for all $b \in U \cap A$. Along the graph of Proposition 4.9, $T_yQ = D\Gamma(v)N$ and $p \circ D\Gamma(v) = 1$.

- `Polyfold.tangentSpace_eq_range_graph` — Polyfold/Chapter4/Submanifolds.lean, line 579
- `Polyfold.MPolyfold.remark_4_20` — Polyfold/Chapter4/Submanifolds.lean, line 1560
- `Polyfold.lemma_3_55_relOpen` — Polyfold/Chapter3/GlobalIFTFull.lean, line 118
- `Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le` — Polyfold/Chapter3/GlobalIFTNearbyGraph.lean, line 518

*What differs.*
- Definition 4.16 is for tame $X$; "move only slowly" is $D\sigma(0) = 0$ for $\Gamma = 1 + \sigma$; typos "Theorem 4.9", "and open" (Findings, item 70).

### V4.44. Definition 4.21: general position, in a chart

*restated* · in a chart (G.7)

**HWZ (§4.2, Definition 4.21, p. 161).** $A$ is in general position at $a$ if $T_aA$ has in $T_aX$ an sc-complement contained in $T^R_aX$ (Definition 2.38).

**Proved in Lean.** `IsGeneralPositionRetractAt`: an sc-subspace $B \subseteq T_zO \cap E_z$ with $(T_zO)_m = (T_zQ)_m \oplus B_m$ on every level. `IsGeneralPositionAt A a`: this for $Q = \varphi(W \cap A)$ in some chart, data, presentation and lift.

- `Polyfold.IsGeneralPositionRetractAt` — Polyfold/Chapter4/Submanifolds.lean, line 344
- `Polyfold.MPolyfold.SubmanifoldData.IsGeneralPositionChart` — Polyfold/Chapter4/Submanifolds.lean, line 1329
- `Polyfold.MPolyfold.IsGeneralPositionAt` — Polyfold/Chapter4/Submanifolds.lean, line 1341

*What differs.*
- The sc-structure of $T_zO$ is the one induced from $E$ at the smooth point (Findings, item 71).

### V4.45. Definition 4.21 does not depend on the chart

*not in the book* · needs the point smooth

**HWZ (§4.2, Definition 4.21, p. 161 (implicit)).** Not in the text. Definition 4.21 is stated in $T_aX$; chart independence is taken for granted.

**Proved in Lean.** General position of a sub-retract is carried by germs of sc-diffeomorphisms at smooth points; general position at $a$ holds for every data, chart, presentation and lift.

- `Polyfold.IsGeneralPositionRetractAt.transport` — Polyfold/Chapter4/Submanifolds.lean, line 366
- `Polyfold.MPolyfold.isGeneralPositionRetractAt_chart_change` — Polyfold/Chapter4/Submanifolds.lean, line 1199
- `Polyfold.MPolyfold.IsGeneralPositionAt.isGeneralPositionChart` — Polyfold/Chapter4/Submanifolds.lean, line 1350
- `Polyfold.MPolyfold.isGeneralPositionAt_iff_forall` — Polyfold/Chapter4/Submanifolds.lean, line 1369

*What differs.*
- Through Proposition 2.30 (Findings, item 66).

### V4.46. Theorem 4.22: linear algebra at the corner of a centred chart

*restated* · $Y$ closed · coordinates replace $N \oplus (T_0A \cap W)$

**HWZ (§4.2, proof of Theorem 4.22, pp. 162–163).** $E = T_0O \oplus Z = T_0A \oplus \widetilde A \oplus Z$, so $T_0A$ has an sc-complement $Y \subseteq W$; with $T_0A = N \oplus (T_0A \cap W)$, $E = N \oplus W$, $C = (T_0A \cap C) \oplus Y$, and $T_0A \cap C$ is a partial quadrant (Proposition 3.22).

**Proved in Lean.** At the corner: $E_0^{\min} = \{\lambda = 0\} \subseteq E_x$; adding vectors of it changes neither $C$ nor $d$. For finite-dimensional $N$ with $N + E_0^{\min} = E_0$: $\lambda|_N$ onto, good position with a closed good complement $Y \subseteq E_0^{\min}$, and $d_{N \cap C} = d_C$ on $N \cap C$.

- `Polyfold.mem_minimalSubspaceWith_zero` — Polyfold/Chapter4/LocalStructure.lean, line 173
- `Polyfold.minimalSubspaceWith_zero_le` — Polyfold/Chapter4/LocalStructure.lean, line 183
- `Polyfold.add_mem_iff_of_mem_zero` — Polyfold/Chapter4/LocalStructure.lean, line 202
- `Polyfold.degIndexWith_add_of_mem_zero` — Polyfold/Chapter4/LocalStructure.lean, line 195
- `Polyfold.coordsOn_surjective` — Polyfold/Chapter4/LocalStructure.lean, line 218
- `Polyfold.exists_isClosed_isCompl_le` — Polyfold/Chapter4/LocalStructure.lean, line 123
- `Polyfold.exists_goodComplement_le_zero` — Polyfold/Chapter4/LocalStructure.lean, line 260
- `Polyfold.degIndex_slice` — Polyfold/Chapter4/LocalStructure.lean, line 272

*What differs.*
- Only $T_0A + W = E$ is used; Proposition 4.9 needs $Y$ closed (Findings, items 82, 83).

### V4.47. Theorem 4.22 (3): an sc-complement inside $T^R_yO$

*hypotheses explicit* · $T^R_yO$ an sc-subspace (Prop. 2.36)

**HWZ (§4.2, proof of Theorem 4.22 (3), p. 164).** $T_aO = T_aA + (W \cap T_aO) = T_aA + T^R_aO$, "implying that $T_aA$ has in $T_aO$ a sc-complement which is contained in $T^R_aO$".

**Proved in Lean.** (a) A finite-dimensional smooth $N$ has in $N + R$ an sc-complement inside the sc-subspace $R$. (b) For $r$ tame and $y$ smooth, $T_yQ + E_0^{\min} = E_0$ gives general position of $Q$ at $y$.

- `Polyfold.exists_scComplement_le` — Polyfold/Chapter4/LocalStructure.lean, line 327
- `Polyfold.isGeneralPositionRetractAt_of_sup_eq_top` — Polyfold/Chapter4/LocalStructure.lean, line 421

*What differs.*
- Lemma 7.A of the exposition (Findings, item 85 (b)).

### V4.48. General position implies good position

*not in the book* · Lemma 7.B of the exposition

**HWZ (not in the text (§4.2), p. 162).** Not in the text. Needed for "$A \cap F_\sigma$ is tame" in Theorem 4.22 (4) and for the corner structure in Theorem 4.23.

**Proved in Lean.** For $r$ tame and a smooth $z \in O_1$: general position of $Q$ at $z$ implies good position at $z$.

- `Polyfold.IsGeneralPositionRetractAt.isGoodPositionRetractAt` — Polyfold/Chapter4/LocalStructure.lean, line 642

*What differs.*
- Findings, item 89 (d).

### V4.49. Theorem 4.22 in a tame centred chart

*restated* · $D\Gamma(v)h - h \in Y$

**HWZ (§4.2, proof of Theorem 4.22, pp. 162–164).** In the tame chart with $x = 0$: $A$ is the graph $\{v + \delta(v)\}$ over $V \subseteq T_0A \cap C$ (Proposition 4.9); $d_A(a) = d_{T_0A \cap C}(p(a)) = d_C(a) = d_O(a)$; and "by means of the particular form of the map $\alpha$" $T_aA + W = E$, giving (3).

**Proved in Lean.** For $r$ tame, $t$ sc⁺ onto $Q \ni 0$, general position at $0$: $N + E_0^{\min} = E_0$, $N$ in good position, a closed good complement $Y \subseteq E_0^{\min}$ with $\ker p = Y$, the data of Proposition 4.9, $d_{N \cap C}(v) = d_C(\Gamma(v))$ on $V$, and general position along $Q \cap W$.

- `Polyfold.sup_minimalSubspaceWith_eq_top` — Polyfold/Chapter4/LocalStructure.lean, line 463
- `Polyfold.sup_minimalSubspaceWith_eq_top_graph` — Polyfold/Chapter4/LocalStructure.lean, line 498
- `Polyfold.theorem_4_22_chart` — Polyfold/Chapter4/LocalStructure.lean, line 542

*What differs.*
- "The particular form of $\alpha$" is $p \circ D\Gamma(v) = 1$ with $\ker p = Y \subseteq E_0^{\min}$ (Findings, items 84, 85).

### V4.50. Theorem 4.22: local structure in general position

*restated* · (4) proved; the text has no proof · (1) about the chart model

**HWZ (§4.2, Theorem 4.22, p. 162 (proof pp. 162–164)).** Let $A$ be a smooth submanifold of the tame $X$, in general position at $x$. There is an open $U \ni x$ with (1) precisely $d = d_X(x)$ local faces $F_1, \dots, F_d$ in $U$; (2) $d_X(a) = d_A(a)$ on $A \cap U$; (3) general position on $A \cap U$; (4) for $\sigma \subseteq \{1, \dots, d\}$, $F_\sigma$ is a tame M-polyfold and $A \cap F_\sigma$ a tame smooth submanifold of $F_\sigma$ in general position in $F_\sigma$.

**Proved in Lean.** A tame chart $\psi$ with $\psi(x) = 0$ ($n$ half-line coordinates) and an open $U \ni x$ with: (1) $d_X(x) = n$ and $\psi(x)$ in exactly $d_X(x)$ faces of $O$; (2) $d_A = d_X$ on $A \cap U$; (3) general position on $U \cap A$; (4) for every $\sigma$, faces $F_i \ni 0$, open $G \ni 0$, $F_\sigma = \psi^{-1}(G \cap \bigcap F_i) \subseteq U$ a tame sub-M-polyfold with $d_{F_\sigma} + \#\sigma = d_X$, $A \cap F_\sigma$ a tame submanifold of $F_\sigma$ in general position.

- `Polyfold.MPolyfold.theorem_4_22` — Polyfold/Chapter4/LocalStructure.lean, line 1541

*What differs.*
- (1) does not identify the local faces of the chart with global faces (G.35); $F_\sigma$ is a germ inside $U$ (Findings, items 80, 86, 89). The dimension count $\dim(A \cap F_\sigma) = \dim A - \#\sigma$, used later, is V4.57.
- (1) and (4) differ in content, not only in form. The formal statement counts the faces through $0$ of the model retract of a tame chart $\psi$ centred at $x$ and takes $F_\sigma = \psi^{-1}(G \cap \bigcap_{i \in \sigma} F_i)$ with $G$ depending on $\sigma$; the text's local faces are faces of the neighbourhood $U$ itself (the closures in $U$ of the components of $U \cap \{d_X = 1\}$, all through $x$). (2) and (3) are the text's (round-trip item V4.50).
- Identifying the two kinds of faces needs a local face theorem for small neighbourhoods, which identifies the faces of $U$ with the $\psi$-preimages of the faces of the model retract; it is believed true for tame $X$ and not formalized (Findings, Chapter 4, items 90, 130; G.35). Recorded in the third addendum of this page.

### V4.51. Theorem 4.22 (4) in the chart: the sc⁺-retraction onto $A \cap F_\sigma$

*not in the book* · no argument in the text

**HWZ (§4.2, end of the proof of Theorem 4.22, p. 164).** Not in the text. "The previous arguments, but now applied to $A \cap F_\sigma$ conclude the proof."

**Proved in Lean.** $t_\sigma = \Gamma \circ \kappa_\sigma \circ p \circ t$ ($\kappa_\sigma$ kills the coordinates in $\sigma$ on $N$) is an sc⁺-retraction onto $Q \cap G \cap f_\sigma$ with $T_yQ \cap f_\sigma$ tangent to it; its corner model on $[0, \infty)^{n - \#\sigma} \oplus W$ is sc⁺, lies in a tame corner model of $O \cap G \cap f_\sigma$, and is in general position there.

- `Polyfold.killOn` — Polyfold/Chapter4/LocalStructure.lean, line 734
- `Polyfold.exists_scPlus_retraction_corner` — Polyfold/Chapter4/LocalStructure.lean, line 797
- `Polyfold.exists_cornerModel_retraction` — Polyfold/Chapter4/LocalStructure.lean, line 982
- `Polyfold.theorem_4_22_four_chart` — Polyfold/Chapter4/LocalStructure.lean, line 1060

*What differs.*
- Findings, item 89 (b), (c).

### V4.52. sc⁺-retractions in a chart; Theorem 4.22 (4) for one $\sigma$

*not in the book* · the converse of V4.30

**HWZ (§4.2, end of the proof of Theorem 4.22, p. 164).** Not in the text. "$A \cap F_\sigma$ are smooth submanifolds of $F_\sigma$" needs an sc⁺-retraction in the M-polyfold $F_\sigma$.

**Proved in Lean.** For a chart $\chi$ and an sc⁺-retraction $\tau$ of its model with values in $O$, $\chi^{-1} \circ \tau \circ \chi$ is an sc⁺-retraction on the open $\chi^{-1}(\tau.U)$. In a tame centred chart, for each $\sigma$, $F_\sigma = \psi^{-1}(G \cap \bigcap F_i)$ has the properties (4).

- `Polyfold.MPolyfold.isScPlusRetractionOn_of_chart` — Polyfold/Chapter4/LocalStructure.lean, line 1227
- `Polyfold.MChart.cornerPreimage` — Polyfold/Chapter4/LocalStructure.lean, line 1315
- `Polyfold.MPolyfold.theorem_4_22_four_of_chart` — Polyfold/Chapter4/LocalStructure.lean, line 1332

*What differs.*
- Tameness of $A \cap F_\sigma$ is Theorem 4.18 in $F_\sigma$ with V4.48 (Findings, item 89 (d), (e)).

### V4.53. The family $\mathbb R^m \times X$ and stratified regular points

*restated* · in a chart; independence: G.36

**HWZ (§4.3, p. 164, and the proof of Theorem 4.23, p. 166).** $Z = \mathbb R^m \oplus X$ with the product charts is tame; $P(\lambda, x) = \lambda$; the proof uses regular values of the maps $p_\sigma : A \cap F_\sigma^\circ \to \mathbb R^m$.

**Proved in Lean.** $\mathbb R^m \times X$ is tame for tame $X$; `fibreSet A λ` $= \{x : (\lambda, x) \in A\}$. `IsStratRegularPoint`: in some product chart, the projection maps $T_zA \cap E_z$ (the stratum's tangent space) onto $\mathbb R^m$; `IsStratRegularValue`: every point of $A$ over $\lambda$ is one.

- `Polyfold.prod_rn_isTame` — Polyfold/Chapter3/ParamPerturbation.lean, line 267
- `Polyfold.fibreSet` — Polyfold/Chapter4/Families.lean, line 528
- `Polyfold.rnPres` — Polyfold/Chapter4/Families.lean, line 532
- `Polyfold.IsStratRegularPoint` — Polyfold/Chapter4/Families.lean, line 552
- `Polyfold.IsStratRegularValue` — Polyfold/Chapter4/Families.lean, line 565

*What differs.*
- "Regular value of every $p_\sigma$" at a point is regularity on the stratum through it (Findings, item 102).

### V4.54. Theorem 4.23: families and Sard's theorem

*stronger* · stratified regular values · countable cover · $A_\lambda$ also tame

**HWZ (§4.3, Theorem 4.23, p. 165 (proof pp. 165–166)).** Let $A \subseteq Z$ be a smooth submanifold with tame induced structure and compact closure, $p = P|_A$, $\varepsilon > 0$ with (1) $p^{-1}(\lambda)$ compact and non-empty for $|\lambda| \le \varepsilon$, (2) "for $z \in A$ there exists a sc-complement $T_zA$ in $T_zZ$ contained in $T^R_zZ$". Then there is $\Sigma \subseteq \{|\lambda| < \varepsilon\}$ of full measure of regular values of $p$ such that for $\lambda \in \Sigma$, $A_\lambda$ is a smooth compact manifold with boundary with corners in general position.

**Proved in Lean.** With (2) read as general position at every point: there is $\Sigma \subseteq \{|\lambda| < \varepsilon\}$ with Lebesgue-null complement, of stratified regular values, such that each $A_\lambda$, $\lambda \in \Sigma$, is compact, a smooth finite-dimensional submanifold of $X$ in general position, with a corner structure, tame.

- `Polyfold.theorem_4_23` — Polyfold/Chapter4/Families.lean, line 940

*What differs.*
- Stratified regular values are regular values. With ordinary regular values the conclusion fails at the value: $A = \{(x, x) : 0 \le x < 1\} \cup (-1, 1) \times \{5\}$ in $\mathbb R \times [0, \infty)$, $A_0 = \{0, 5\}$ meets $\partial X$ (Findings, items 101, 102).
- Not used: the tameness of $A$, the non-emptiness in (1), $\varepsilon > 0$. The finite cover of the proof is replaced by a countable one (V4.64).

### V4.55. Remark 4.24

*hypotheses explicit* · for any submanifold in general position

**HWZ (§4.3, Remark 4.24, p. 165).** By Proposition 2.36 the codimension of $T^R_xX$ is $d_X(x)$; so for $\lambda \in \Sigma$ a point of $A_\lambda$ can lie in a corner only if $d_X(x) \le \dim A_\lambda$; zero-dimensional $A_\lambda$ lie in $X \setminus \partial X$.

**Proved in Lean.** For tame $X$ and smooth $x$, in a tame chart $\operatorname{codim} T^R_zO = d_X(x)$; general position at $a$ gives $d_X(a) \le \dim T_aA$; with $T_aA = 0$, $a \notin \partial X$.

- `Polyfold.quotDim_le_finrank_of_eq_sup` — Polyfold/Chapter4/LocalStructure.lean, line 593
- `Polyfold.remark_4_24_chart` — Polyfold/Chapter4/LocalStructure.lean, line 613
- `Polyfold.MPolyfold.remark_4_24_codim` — Polyfold/Chapter4/LocalStructure.lean, line 1676
- `Polyfold.MPolyfold.remark_4_24` — Polyfold/Chapter4/LocalStructure.lean, line 1700
- `Polyfold.MPolyfold.remark_4_24_not_mem_boundary` — Polyfold/Chapter4/LocalStructure.lean, line 1723

*What differs.*
- Applies to the $A_\lambda$ of Theorem 4.23 through V4.54 (Findings, item 87).

### V4.56. Sard's theorem (vendored from the Milnor project)

*not in the book* · Mathlib has only $\dim E \le \dim F$

**HWZ (§4.3, proof of Theorem 4.23, p. 166 ("Using Sard's theorem")).** Not in the text. The proof applies "Sard's theorem" to maps $A \cap F_\sigma^\circ \to \mathbb R^m$ of arbitrary dimensions, without statement.

**Proved in Lean.** For $E$, $F$ finite-dimensional, $\mu$ a Haar measure on $F$, $U \subseteq E$ open and $f$ $C^\infty$ on $U$: $\mu(f(\mathrm{Crit})) = 0$, $\mathrm{Crit}$ the points where $Df$ is not onto; the complement of the critical values is dense.

- `Polyfold.MilnorSard.Sard.critSet` — Polyfold/Vendor/MilnorSard/Basic.lean, line 60
- `Polyfold.MilnorSard.Sard.sardStatement` — Polyfold/Vendor/MilnorSard/Sard.lean, line 58
- `Polyfold.MilnorSard.sard` — Polyfold/Vendor/MilnorSard/Sard.lean, line 121
- `Polyfold.MilnorSard.dense_compl_image_critSet` — Polyfold/Vendor/MilnorSard/Sard.lean, line 127

*What differs.*
- Copied from the Milnor project with the namespace renamed; no statement or proof changed (Findings, item 100).

### V4.57. The strata, their dimension, and Sard on the strata

*restated* · the dimension count is proved

**HWZ (§4.3, proof of Theorem 4.23, pp. 165–166).** "By Theorem 4.23, the intersection $A \cap F_\sigma^\circ$ is a smooth manifold without boundary having dimension $\dim(A) - \#\sigma$"; Sard gives sets $\Sigma_\sigma$ of full measure of regular values of $p_\sigma$, and $\Sigma = \bigcap_\sigma\Sigma_\sigma$.

**Proved in Lean.** In a finite-dimensional $V$ with onto coordinates $\ell$: the stratum subspace of $\sigma$ has dimension $\dim V - \#\sigma$; for $f$ $C^\infty$ on $O \cap \{\ell \ge 0\}$ the image of the stratified critical points ($Df$ not onto on the stratum through the point) is null for every Haar measure.

- `Polyfold.quadC` — Polyfold/Chapter4/FamiliesLocal.lean, line 73
- `Polyfold.stratSub` — Polyfold/Chapter4/FamiliesLocal.lean, line 77
- `Polyfold.zeroSetOf` — Polyfold/Chapter4/FamiliesLocal.lean, line 88
- `Polyfold.finrank_stratSub` — Polyfold/Chapter4/FamiliesLocal.lean, line 98
- `Polyfold.stratCritSet` — Polyfold/Chapter4/FamiliesLocal.lean, line 129
- `Polyfold.measure_image_stratCritSet` — Polyfold/Chapter4/FamiliesLocal.lean, line 140

*What differs.*
- The text cites "Theorem 4.23" for Theorem 4.22, which does not state the dimension count (Findings, items 90, 104).

### V4.58. Theorem 3.78 in $C^\infty$ form

*stronger* · radii independent of $j$

**HWZ (§3.8, Theorem 3.78, p. 141 (used in §4.3)).** Theorem 3.78 (implicit function theorem in partial quadrants) for $f$ of class $C^j$, with a $C^j$ solution.

**Proved in Lean.** For $f$ of class $C^\infty$, one solution $\tau$ is $C^\infty$, with all the other conclusions of V3.63.

- `Polyfold.ContractionData.exists_solution_smooth` — Polyfold/Chapter4/FamiliesLocal.lean, line 209
- `Polyfold.theorem_3_78_smooth` — Polyfold/Chapter4/FamiliesLocal.lean, line 252
- `Polyfold.ContractionData.exists_radii` — Polyfold/Chapter3/QuadrantIFT.lean, line 154
- `Polyfold.Radii.contDiffOn_τ` — Polyfold/Chapter3/QuadrantIFT.lean, line 578
- `Polyfold.theorem_3_78` — Polyfold/Chapter3/QuadrantIFT.lean, line 648

*What differs.*
- The contraction radii of Lemmas 3.79, 3.80 and the fixed point do not depend on $j$ (Findings, item 105 (c)).

### V4.59. The kernel at a stratified regular point is in good position

*not in the book* · Lemma 5.26’s argument

**HWZ (§4.3, proof of Theorem 4.23, p. 166 (the argument of Lemma 5.26)).** Not in the text. "$A_\lambda$ is a smooth compact manifold with boundary with corners" needs the implicit function theorem at corner points with the kernel in good position.

**Proved in Lean.** If $K + \{\ell_i = 0, i \in \sigma\} = V$ ($\ell$ onto), $K$ is in good position to the partial quadrant $\{\ell_i \ge 0, i \in \sigma\}$ with a closed good complement inside the stratum subspace.

- `Polyfold.quadAt` — Polyfold/Chapter4/FamiliesLocal.lean, line 404
- `Polyfold.isPartialQuadrant_quadAt` — Polyfold/Chapter4/FamiliesLocal.lean, line 441
- `Polyfold.exists_goodComplement_stratSub` — Polyfold/Chapter4/FamiliesLocal.lean, line 481

*What differs.*
- Findings, item 105 (b).

### V4.60. A retraction onto the fibre over a stratified regular point

*not in the book* · IFT at corners

**HWZ (§4.3, proof of Theorem 4.23, p. 166).** Not in the text. The fibres over regular values are asserted to be manifolds with boundary with corners.

**Proved in Lean.** For $f$ $C^\infty$ on $O \cap \{\ell \ge 0\}$ and $v_0$ not stratified-critical: a $C^\infty$ retraction $\rho$ of $O' \cap \{\ell \ge 0\}$ onto its intersection with $f^{-1}(f(v_0))$, with $D\rho(v_0)$ of range $\ker Df(v_0)$, the identity there.

- `Polyfold.exists_fibre_retraction` — Polyfold/Chapter4/FamiliesLocal.lean, line 531

*What differs.*
- From V4.58 and V4.59 for $w \mapsto f(v_0 + w) - f(v_0)$ on $C_{v_0}$ near $0$ (Findings, item 105).

### V4.61. The sc⁺-retraction onto the fibre $A_\lambda$

*not in the book* · not constructed in the text

**HWZ (§4.3, proof of Theorem 4.23, p. 166).** Not in the text. "$A_\lambda \cap U(z)$ is a smooth submanifold of $X$" (Definition 4.13 requires an sc⁺-retraction onto it).

**Proved in Lean.** $\tau(e) = (\Gamma(\rho(p(t(c, e)))))_2$ is an sc⁺-retraction of $E$ onto $\{e : (c, e) \in t(U) \cap W, p(c, e) \in O'\}$; its tangent space at the point over $\Gamma(v_0)_2$ contains the second components of the vertical tangent vectors of $A$. The slice $e \mapsto (c, e)$ is sc-smooth.

- `Polyfold.isScSmooth_slice` — Polyfold/Chapter4/Families.lean, line 102
- `Polyfold.scDeriv_slice` — Polyfold/Chapter4/Families.lean, line 113
- `Polyfold.exists_slice_retraction` — Polyfold/Chapter4/Families.lean, line 168

*What differs.*
- Findings, item 105 (a).

### V4.62. General position of the fibre $A_\lambda$

*restated* · regularity on the stratum is used

**HWZ (§4.3, proof of Theorem 4.23, p. 166).** "$T_{z'}(A \cap F_\sigma^\circ) = T_{z'}((\{\lambda\} \times A_\lambda) \cap F_\sigma^\circ) \oplus \xi_{z'}$ ... in view of the assumption (2) ... $T_{z'}(\{\lambda\} \times A_\lambda)$ has a sc-complement in $T^R_{z'}X$."

**Proved in Lean.** If the chart model of $A$ is in general position at $z = (c, y)$, $T_zA \cap E_z$ projects onto $\mathbb R^m$, and $\tau$ is an sc⁺-retraction whose tangent space at $y$ contains the vertical tangent vectors of $A$, then $\tau$'s retract is in general position at $y$.

- `Polyfold.isGeneralPositionRetractAt_slice` — Polyfold/Chapter4/Families.lean, line 424

*What differs.*
- $(0, w) = a + b$, corrected by $a_2 \in T_zA \cap E_z$ with the same first component (Findings, item 106).

### V4.63. The local step of Theorem 4.23

*restated* · in the product chart of a centred chart

**HWZ (§4.3, proof of Theorem 4.23, pp. 165–166).** Near $z$, Theorem 4.22 gives $U(z)$; the regular values of the $p_\sigma$ have full measure, and over them $A_\lambda \cap U(z)$ is a smooth submanifold in general position.

**Proved in Lean.** Every $z_0 \in A$ has an open $U$ and a null $\mathrm{CV} \subseteq \mathbb R^m$ such that at every $z \in A \cap U$ with $z_1 \notin \mathrm{CV}$: $z$ is stratified regular, $A_{z_1}$ is near $z_2$ the image of an sc⁺-retraction on an open set, in general and in good position at $z_2$.

- `Polyfold.FibreLocal` — Polyfold/Chapter4/Families.lean, line 572
- `Polyfold.exists_local_family` — Polyfold/Chapter4/Families.lean, line 593

*What differs.*
- The text cites "By Theorem 4.23" for Theorem 4.22 (Findings, item 107).

### V4.64. The countable cover: Theorem 4.23 for any parameter set

*stronger* · finite cover need not exist · any parameter set $S$

**HWZ (§4.3, proof of Theorem 4.23, p. 165).** "We cover the set $\{z \in A : |p(z)| \le \varepsilon\}$ with the finitely many such neighborhoods $U(z_1), \dots, U(z_k)$."

**Proved in Lean.** For $A$ with compact closure, in general position everywhere, and any $S \subseteq \mathbb R^m$: there is $\Sigma \subseteq S$ with $S \setminus \Sigma$ null, consisting of stratified regular values, with the local conclusions at every point of $A_\lambda$.

- `Polyfold.theorem_4_23_of_subset` — Polyfold/Chapter4/Families.lean, line 888

*What differs.*
- The set need not be compact: $A = (-2\varepsilon, 2\varepsilon) \times \{2\} \cup \{(\varepsilon(1 - x), x) : 0 < x < 1\}$; $A$ is second countable (compact closure in the metrizable $\mathbb R^m \times X$), and a countable subcover suffices (Findings, item 103).

## Chapter 5

*HWZ Chapter 5 §§5.1–5.4, preprint pp. 169–199: the Fredholm package for M-polyfolds — auxiliary norms, compactness, sc⁺-sections and bump functions, transversality, general and good position, homotopies, partitions of unity*

### V5.1. The charts $\Phi[1]$ for every strong bundle chart

*not in the book* · every compatible chart

**HWZ (§5.1, p. 169; Lemma 5.2 (ii)).** Lemma 5.2 (ii) quantifies over "a strong bundle isomorphism $\Phi : Y|V \to K$" and reads $|h|_1$ for $\Phi(w) = (p, h)$, $w \in Y_{0,1}$.

**Proved in Lean.** For every strong bundle chart $\Phi$ compatible with the atlas: $y \in Y_{0,1}$ iff $\Phi(y)_2 \in F_1$; $\Phi[1]$ (`oneChartOf`) is a chart of the M-polyfold $Y[1]$, compatible with the charts $\Phi'[1]$ of the atlas.

- `Polyfold.StrongBundle.oneChartOf` — Polyfold/Chapter5/AuxNorm.lean, line 182
- `Polyfold.StrongBundle.isChart_oneChartOf` — Polyfold/Chapter5/AuxNorm.lean, line 337
- `Polyfold.StrongBundle.oneChartOf_compatible` — Polyfold/Chapter5/AuxNorm.lean, line 320
- `Polyfold.StrongBundle.mem_oneSet_iff_of_isChart` — Polyfold/Chapter5/AuxNorm.lean, line 120

*What differs.*
- Chapter 2 built $\Phi[1]$ only for the charts of the atlas; Lemma 5.2 (ii) and its "(ii) ⇒ (i)" need it for every compatible chart (Findings, Chapter 5, item 2).

### V5.2. The fibre $(Y_{0,1})_x$ and its chart norm $|\cdot|_1$

*not in the book* · fibre built, not assumed · $|h|_1$ depends on the chart

**HWZ (§5.1, p. 169).** "The fibers $Y_x := P^{-1}(x)$ have the structure of Banach spaces"; $|h|_1$ is the norm of the fibre component in Lemma 5.2.

**Proved in Lean.** `oneFiber x`: the points of $P^{-1}(x)$ in $Y_{0,1}$, a linear subspace, with zero $0_x$ (`zeroOne`). In a chart around $x$, `liftOneFiber` is an injective linear map $(Y_{0,1})_x \to F_1$ onto the closed slice $\{h \mid (\varphi(x), h) \in K[1]\}$, so the fibre is complete for $|\cdot|_1$; the norms of two charts are locally uniformly comparable.

- `Polyfold.StrongBundle.oneFiber` — Polyfold/Chapter5/AuxNorm.lean, line 361
- `Polyfold.StrongBundle.toOne` — Polyfold/Chapter5/AuxNorm.lean, line 385
- `Polyfold.StrongBundle.zeroOne` — Polyfold/Chapter5/AuxNorm.lean, line 399
- `Polyfold.StrongBundle.liftOneFiber` — Polyfold/Chapter5/AuxNorm.lean, line 437
- `Polyfold.StrongBundle.liftOneFiber_injective` — Polyfold/Chapter5/AuxNorm.lean, line 458
- `Polyfold.StrongBundle.mem_range_liftOneFiber` — Polyfold/Chapter5/AuxNorm.lean, line 480
- `Polyfold.StrongBundle.isClosed_slice` — Polyfold/Chapter5/AuxNorm.lean, line 511
- `Polyfold.StrongBundle.complete_liftOneFiber` — Polyfold/Chapter5/AuxNorm.lean, line 534
- `Polyfold.StrongBundle.exists_norm_liftOne_le_mul` — Polyfold/Chapter5/AuxNorm.lean, line 828

*What differs.*
- The text takes the linear and Banach structure of the fibres of $Y_{0,1}$ for granted; completeness comes from the slice being a fixed point set (Findings, Chapter 5, item 1).

### V5.3. Definition 5.1: auxiliary norms

*restated* · complete norm on $(Y_{0,1})_x$

**HWZ (§5.1, Definition 5.1, p. 169).** An auxiliary norm is a continuous $N : Y_{0,1} \to \mathbb R$ such that (1) its restriction to a fibre is a complete norm; (2) if $P(w_k) \to x$ and $N(w_k) \to 0$, then $w_k \to 0_x$ in $Y_{0,1}$.

**Proved in Lean.** `IsAuxNorm N`: $N : Y[1] \to \mathbb R$ continuous; on each fibre $(Y_{0,1})_x$ a norm whose Cauchy sequences converge (`IsCompleteFiberNorm`); and condition (2) with sequences, in the topology of $Y[1]$. Non-negative and homogeneous.

- `Polyfold.StrongBundle.IsCompleteFiberNorm` — Polyfold/Chapter5/AuxNorm.lean, line 565
- `Polyfold.StrongBundle.IsAuxNorm` — Polyfold/Chapter5/AuxNorm.lean, line 577
- `Polyfold.StrongBundle.IsAuxNorm.nonneg` — Polyfold/Chapter5/AuxNorm.lean, line 600
- `Polyfold.StrongBundle.IsAuxNorm.smul` — Polyfold/Chapter5/AuxNorm.lean, line 603

*What differs.*
- "Complete norm" is read as a norm on $(Y_{0,1})_x$ with complete normed space (Findings, Chapter 5, item 1).

### V5.4. Lemma 5.2: local comparison

*as in the book* · also literally, on the chart's domain · every chart in (i) ⇒ (ii)

**HWZ (§5.1, Lemma 5.2, p. 169 (proof pp. 169–170)).** For a continuous $N$ which fibrewise is a complete norm: $N$ is auxiliary iff every $x$ has a strong bundle isomorphism $\Phi : Y|V \to K$ and $0 < c < C$ with $cN(w) \le |h|_1 \le CN(w)$ for all $w \in P^{-1}(V)$, $\Phi(w) = (p, h)$.

**Proved in Lean.** `lemma_5_2`: the same equivalence, with $V \subseteq \operatorname{dom}\varphi$ an open neighbourhood of $x$ on which the bounds hold for $w \in Y_{0,1}$. For an auxiliary norm the bounds hold in every chart around $x$ (`IsAuxNorm.exists_bounds`); the upper bound holds for any $g$ continuous at $0_x$ and fibrewise homogeneous. `lemma_5_2_literal`: the text's form, with the bounds for all $w \in Y_{0,1}$ over the whole base domain of the chart (the chart restricted to the neighbourhood, V2.57).

- `Polyfold.lemma_5_2` — Polyfold/Chapter5/AuxNorm.lean, line 780
- `Polyfold.StrongBundle.exists_le_mul_norm_liftOne` — Polyfold/Chapter5/AuxNorm.lean, line 616
- `Polyfold.StrongBundle.IsAuxNorm.exists_norm_liftOne_le` — Polyfold/Chapter5/AuxNorm.lean, line 687
- `Polyfold.StrongBundle.IsAuxNorm.exists_bounds` — Polyfold/Chapter5/AuxNorm.lean, line 759
- `Polyfold.lemma_5_2_literal` — Polyfold/Chapter5/AuxNormLiteral.lean, line 48

*What differs.*
- The proof gives the bounds only "for $P(w)$ close to $x$"; $V$ is that neighbourhood (Findings, Chapter 5, item 3). The text's literal form, with the bounds on the whole domain of the chart, follows by restricting the chart to that neighbourhood (`lemma_5_2_literal`; Findings, Chapter 2, items 42, 44). Formerly “restated”; updated in the third addendum of this page.
- "(ii) ⇒ (i) is obvious" needs $\Phi[1]$ a homeomorphism onto $K[1]$ (V5.1); no metrizability is used (Findings, Chapter 5, items 2, 3).

### V5.5. Proposition 5.3: existence of auxiliary norms

*as in the book* · the glued norm

**HWZ (§5.1, Proposition 5.3, p. 171).** Every strong bundle has an auxiliary norm ("a partition of unity argument using the paracompactness of $X$, pulling back by strong bundle maps the standard norm $|\cdot|_1$").

**Proved in Lean.** `proposition_5_3_exists`: the glued norm $\sum_i\rho_i(P(w))|\Phi_i[1](w)_2|_1$ over the atlas is continuous on $Y[1]$, a complete norm on every fibre and locally comparable with every chart norm; Lemma 5.2 concludes.

- `Polyfold.proposition_5_3_exists` — Polyfold/Chapter5/AuxNorm.lean, line 1023
- `Polyfold.StrongBundle.gluedNorm` — Polyfold/Chapter5/AuxNorm.lean, line 902
- `Polyfold.StrongBundle.continuous_gluedNorm` — Polyfold/Chapter5/AuxNorm.lean, line 921
- `Polyfold.StrongBundle.isCompleteFiberNorm_gluedNorm` — Polyfold/Chapter5/AuxNorm.lean, line 972
- `Polyfold.StrongBundle.gluedNorm_bounds` — Polyfold/Chapter5/AuxNorm.lean, line 940

*What differs.*
- The one-sentence proof is carried out: local finiteness, fibrewise completeness, uniform comparison of finitely many charts (Findings, Chapter 5, item 4).

### V5.6. Proposition 5.3: comparison of auxiliary norms

*as in the book* · local constants glued

**HWZ (§5.1, Proposition 5.3, p. 171).** For auxiliary norms $N_0$, $N_1$ there is a continuous $f : X \to (0, \infty)$ with $f(x)N_0(h) \le N_1(h) \le f(x)^{-1}N_0(h)$ on $P^{-1}(x) \subseteq Y_{0,1}$.

**Proved in Lean.** `proposition_5_3_compare`: a continuous $f > 0$ with $f(P(w))N_0(w) \le N_1(w) \le f(P(w))^{-1}N_0(w)$ for all $w \in Y[1]$.

- `Polyfold.proposition_5_3_compare` — Polyfold/Chapter5/AuxNorm.lean, line 1045

*What differs.*
- "The local compatibility implies the existence of $f$": local constants from Lemma 5.2 in one chart, glued by a partition of unity (convex sets of admissible constants) (Findings, Chapter 5, item 5).

### V5.7. Definition 5.4: compact solution set, weakly proper, proper

*hypotheses explicit* · $f$ continuous for "proper ⇒ weakly proper"

**HWZ (§5.2, Definition 5.4, p. 171).** (1) $f^{-1}(0)$ compact; (2) weakly proper: moreover for every $N$ an open $U \supseteq f^{-1}(0)$ with $\{f = s\}$ compact for every sc⁺-section $s$ supported in $U$ with $N(s) \le 1$; (3) proper: moreover $\operatorname{cl}_{X_0}\{x \in U \mid N(f(x)) \le 1\}$ compact, $N(f(x)) = \infty$ off $Y_{0,1}$. "Obviously proper implies weakly proper, which in turn implies compactness."

**Proved in Lean.** `IsWeaklyProper`, `IsProper` as in the text, with `AuxLe` for "$N(y) \le r$, $y \in Y_{0,1}$". For a continuous $f$: proper ⇒ weakly proper (`IsProper.isWeaklyProper`) ⇒ compact solution set.

- `Polyfold.StrongBundle.AuxLe` — Polyfold/Chapter5/Compactness.lean, line 859
- `Polyfold.StrongBundle.IsWeaklyProper` — Polyfold/Chapter5/Compactness.lean, line 866
- `Polyfold.StrongBundle.IsProper` — Polyfold/Chapter5/Compactness.lean, line 875
- `Polyfold.StrongBundle.IsProper.isWeaklyProper` — Polyfold/Chapter5/Compactness.lean, line 955
- `Polyfold.StrongBundle.IsWeaklyProper.isCompact_solutionSet` — Polyfold/Chapter5/Compactness.lean, line 973

*What differs.*
- "Obviously" uses that $\{f = s\}$ is closed and that a solution outside $U$ is a zero of $f$ (Findings, Chapter 5, item 26).

### V5.8. Theorem 5.5, the local form for basic germs

*not in the book* · $\tilde C$ closed · neighbourhood independent of $c$

**HWZ (§5.4.1, proof of Theorem 5.5, pp. 189–192).** In basic germ coordinates, $z = w - B(a, w)$ with $|z|_1 \le 3c$, $|z|_0 < \tau/2$ gives $w = \delta(a, z)$; by the compactness of $E_1 \to E_0$, sequences have convergent subsequences ((82)–(90)).

**Proved in Lean.** `IsBasicGerm.exists_isCompact_bdd` ($\tilde C$ closed): an open $O \ni 0$, independent of $c$, such that the points of $U_0 \cap O$ with $|f(x)|_1 \le c$ lie in the compact image of $\{a \in \tilde C, |a| \le \rho\} \times K_c$ under $(a, z) \mapsto (a, \delta(a, z))$.

- `Polyfold.IsSc0ContractionGerm.exists_isCompact_bdd` — Polyfold/Chapter5/Compactness.lean, line 537
- `Polyfold.IsBasicGerm.exists_isCompact_bdd` — Polyfold/Chapter5/Compactness.lean, line 601

*What differs.*
- The appendix writes $a \in \mathbb R^n$ for $a \in \tilde C$, "$\mathbb R^n \oplus Y_1$" for $\mathbb R^N \oplus W_1$, and (89) mixes components (Findings, Chapter 5, item 25).

### V5.9. Theorem 5.5, the local step on the M-polyfold

*not in the book* · uniform $(0, 1)$ fibre bound · $x_0$ need not be a zero

**HWZ (§5.4.1, proof of Theorem 5.5, pp. 189–192).** "Without loss of generality" $f = h + t$ in local coordinates; "it suffices to find in local coordinates an open neighbourhood $U$ of $0$" with $\operatorname{cl}\{(a, w) \in U \mid |(h + t)(a, w)|_1 \le c\}$ compact.

**Proved in Lean.** `IsStrongBundleMap.exists_fiber_bound_one`: $|\Psi[1](u, k)_2|_1 \le M|k|_1$ near $u_0$. `exists_nbhd_isCompact_closure_bdd`: for an sc-Fredholm germ $(f, x_0)$, in its chart, an open $V \ni x_0$ with $\operatorname{cl}_X\{x \in V \mid |\Phi(f(x))_2|_1 \le C\}$ compact for every $C$.

- `Polyfold.IsStrongBundleMap.exists_fiber_bound_one` — Polyfold/Chapter5/Compactness.lean, line 645
- `Polyfold.exists_nbhd_isCompact_closure_bdd` — Polyfold/Chapter5/Compactness.lean, line 695

*What differs.*
- The uniform fibre bound of the conjugating isomorphism is used silently; subtracting the sc⁺-part first makes $t$, (83) and (85) unnecessary (Findings, Chapter 5, item 23).
- The way back from the filled domain $U$ to $X$ uses that the retract is the fixed point set of $r$ (Findings, Chapter 5, item 24).

### V5.10. Theorem 5.5: compact solution set implies proper

*stronger* · no tameness · finite cover explicit

**HWZ (§5.2, Theorem 5.5, p. 172 (proof §5.4.1, pp. 189–192)).** Over a tame $X$, an sc-Fredholm section with compact solution set is proper; for sc-Fredholm sections proper, weakly proper and compact solution set are equivalent.

**Proved in Lean.** `theorem_5_5`: compact solution set ⇒ `IsProper f`, for any $X$. `theorem_5_5_iff`: the three properties are equivalent for sc-Fredholm sections.

- `Polyfold.theorem_5_5` — Polyfold/Chapter5/Compactness.lean, line 920
- `Polyfold.theorem_5_5_iff` — Polyfold/Chapter5/Compactness.lean, line 978

*What differs.*
- Tameness is not used (the appendix restates the theorem without it); the last sentence of the proof is a finite cover of $f^{-1}(0)$ and the closure of a finite union (Findings, Chapter 5, items 24, 25).

### V5.11. Theorem 5.6: local compactness

*as in the book* · Theorem 3.12 at a zero

**HWZ (§5.2, Theorem 5.6, p. 172).** For an sc-Fredholm $f$ and $f(x) = 0$ there are open $x \in U(i + 1) \subseteq U(i) \subseteq X_0$ with $\operatorname{cl}_{X_0}\{y \in U(i) \mid f(y) = 0\}$ a compact subset of $X_i$.

**Proved in Lean.** `theorem_5_6`: open nested $U(i) \ni x$ with $\operatorname{cl}_X\{y \in U(i) \mid f(y) = 0\}$ the image of a compact subset of $X_i$ (level topology).

- `Polyfold.theorem_5_6` — Polyfold/Chapter5/Compactness.lean, line 162

*What differs.*
- A zero is a smooth point where $(f, x)$ is an sc-Fredholm germ, so Theorem 3.12 applies.

### V5.12. Theorem 5.7: compactness in $X_\infty$

*stronger* · no tameness · topology of $X_\infty$ supplied

**HWZ (§5.2, Theorem 5.7, p. 172).** Over a tame $X$, if $S = f^{-1}(0)$ is compact in $X_0$, it is a compact subset of $X_\infty$ ("$X_\infty$ is a metric space"; "from Theorem 5.6 we conclude that $x_k \to x$ on every level").

**Proved in Lean.** `theorem_5_7`: $S \subseteq X_\infty$ and $\{x \in X_\infty \mid x \in S\}$ is compact, $X_\infty$ with the initial topology of $X_\infty \to X_m$ (metrizable; convergence = convergence on every level).

- `Polyfold.theorem_5_7` — Polyfold/Chapter5/Compactness.lean, line 215
- `Polyfold.MPolyfold.tendsto_smoothLevel_iff` — Polyfold/Chapter5/Compactness.lean, line 202
- `Polyfold.MPolyfold.smoothLevel_topology_eq` — Polyfold/Chapter2/Metrizable.lean, line 542
- `Polyfold.MPolyfold.metrizableSpace_smoothLevel` — Polyfold/Chapter2/Metrizable.lean, line 551

*What differs.*
- The convergence on every level is Corollary 3.13 at the limit, not Theorem 5.6; the text never defines the topology of $X_\infty$ (Findings, Chapter 5, item 20).

### V5.13. Corollary 5.8: $f^i$ sc-Fredholm on $P^i$, with compact solution set

*stronger* · $P^i$ read as the iterate of $P^1$ · $i = 1, 2$ stated, each $i$ by iteration · tameness not used

**HWZ (§5.2, Corollary 5.8, p. 173).** Over a tame $X$, if $f^{-1}(0)$ is compact, then $f^i$ is an sc-Fredholm section of $P^i : Y^i \to X^i$ with compact solution set.

**Proved in Lean.** `corollary_5_8`: if $f$ is an sc-Fredholm section of $P$ (Definition 3.14, the text’s germ reading) with compact solution set, then $f^1 = f|_{X_1}$ is an sc-Fredholm section of the shifted strong bundle $P^1 : Y^1 \to X^1$ (V5.14) with compact solution set in $X^1$. `corollary_5_8_two`: the same for $f^2 = (f^1)^1$ on $P^2 = (P^1)^1$; since `corollary_5_8` holds for every strong bundle, every fixed $i$ follows by iterating it. `isCompact_solutionSet_level`: for every $i$ the zeros of $f$ in $X_i$ form a compact subset of $X_i$.

- `Polyfold.corollary_5_8` — Polyfold/Chapter5/Corollary58.lean, line 546
- `Polyfold.corollary_5_8_two` — Polyfold/Chapter5/Corollary58.lean, line 557
- `Polyfold.StrongBundle.solutionSet_sectionShift` — Polyfold/Chapter5/StrongBundleShift.lean, line 994
- `Polyfold.isCompact_solutionSet_level` — Polyfold/Chapter5/Compactness.lean, line 242

*What differs.*
- $P^i : Y^i \to X^i$ is not defined in the text; it is read as the iterated shift $P^i = (P^{i-1})^1$ (V5.14). `corollary_5_8` is stated for every strong bundle, so it applies to $P^1$, $P^2$, …, and every fixed $i$ is obtained by iterating it ($i = 2$ is `corollary_5_8_two`); one statement for a family $P^i$ indexed by $i$ is not formalized. The base of $P^2$ is $(X^1)^1$, whose points are those of $X_2$; its topology is not compared with that of $X_2$ (gap G.6). The compact solution set is also proved on every level $X_i$ directly.
- Tameness of $X$ is not used; the conclusion is Definition 3.14 for $f^i$, not tame germ data, which would need the tameness of the index raises of tame charts (not proved; Findings, Chapter 5, item 145). Hence “stronger”: the strong bundle need not be tame, as in V5.10, and the round-trip audit confirms A ⇒ B, not B ⇒ A (refreshed 2026-11-02; “same” in the fourth addendum, “narrower” before it, when only the compactness half was proved) (Findings, Chapter 5, items 140–146; gap G.41).

### V5.14. Corollary 5.8: the shifted strong bundle $P^1$, and $f^1$ sc-Fredholm on it

*stronger* · $P^1 : Y_{1,1} \to X^1$ built · filler condition (3) on level 1 proved · no tameness; tame form not stated

**HWZ (§5.2, Corollary 5.8, p. 173).** "It is a priori clear that $f^i$ is sc-Fredholm", as a section of $P^i : Y^i \to X^i$.

**Proved in Lean.** `StrongBundle.shift`: the shifted strong bundle $P^1 : Y^1 \to X^1$ (Definition 2.51): total space $Y_{1,1}$ with its level topology, $P^1 = P|_{Y_{1,1}}$, fibres $P^{-1}(x) \cap Y_{1,1}$ (linear subspaces, with the topology of $F_1$), and the atlas of the index raises $\Phi^1$ of the strong bundle charts, compatible charts having compatible index raises; $(Y^1)_{m,k} = Y_{m+1,k+1}$. `corollary_5_8_isScFredholmSection`: for an sc-Fredholm section $f$, $f^1 = f|_{X_1}$ is an sc-Fredholm section of $P^1$ — sc-smooth, regularizing, and an sc-Fredholm germ at every smooth point of $X^1$ (`isScFredholmGerm_sectionShift`), with the datum $(g^1, s^1)$ in the index raise $\Phi^1$ of the chart of a datum $(g, s)$ of $f$: the principal part of $f^1$ is the level-$1$ map of that of $f$, $g^1$ is a filling germ of it, including condition (3) of Definition 3.4 on level $1$ (`IsFillingGerm.germ_shift`, from `IsFillingGerm.mem_range_toBase_of_fillDefect`: at the centre of every datum, $v \in \ker Dr(0)$ and $Dk(0)v \in F_m$ give $v \in E_m$), $s^1$ is an sc⁺-germ on the shifted germ, and $g^1 - s^1 = (g - s)_1$ near $0$ is conjugated to a basic germ by the index raise of the conjugation (`IsConjugateToBasicGerm.shift_germ`, with `IsBasicGerm.shift`). The chart-level form `corollary_5_8_chart` is kept.

- `Polyfold.StrongBundle.shift` — Polyfold/Chapter5/StrongBundleShift.lean, line 877
- `Polyfold.StrongBundleChart.shift` — Polyfold/Chapter5/StrongBundleShift.lean, line 630
- `Polyfold.StrongBundleChart.Compatible.shift` — Polyfold/Chapter5/StrongBundleShift.lean, line 815
- `Polyfold.StrongBundle.mem_shift_doubleLevel_iff` — Polyfold/Chapter5/StrongBundleShift.lean, line 918
- `Polyfold.StrongBundle.sectionShift` — Polyfold/Chapter5/StrongBundleShift.lean, line 940
- `Polyfold.StrongBundle.regularizing_sectionShift` — Polyfold/Chapter5/StrongBundleShift.lean, line 1002
- `Polyfold.ScNbhdGerm.shiftParam` — Polyfold/Chapter5/Compactness.lean, line 266
- `Polyfold.IsSc0ContractionGerm.shift` — Polyfold/Chapter5/Compactness.lean, line 284
- `Polyfold.IsBasicGerm.shift` — Polyfold/Chapter5/Compactness.lean, line 306
- `Polyfold.IsConjugateToBasicGerm.shift` — Polyfold/Chapter5/Compactness.lean, line 343
- `Polyfold.IsConjugateToBasicGerm.shift_germ` — Polyfold/Chapter5/Compactness.lean, line 404
- `Polyfold.IsFillingGerm.mem_range_toBase_of_fillDefect` — Polyfold/Chapter5/Corollary58.lean, line 99
- `Polyfold.IsFillingGerm.germ_shift` — Polyfold/Chapter5/Corollary58.lean, line 245
- `Polyfold.isScFredholmGerm_sectionShift` — Polyfold/Chapter5/Corollary58.lean, line 494
- `Polyfold.corollary_5_8_isScFredholmSection` — Polyfold/Chapter5/Corollary58.lean, line 536
- `Polyfold.corollary_5_8_chart` — Polyfold/Chapter5/Compactness.lean, line 482

*What differs.*
- $Y^i \to X^i$ is never defined in the text (it defines $Y[i]$ for $i = 0, 1$). $Y^1$ is read as $Y_{1,1}$ with $(Y^1)_{m,k} = Y_{m+1,k+1}$, the convention of $E^1$ and of $(U \triangleleft F)^1 = U^1 \triangleleft F^1$; it is forced by “$f^i$ is obtained by raising the index”: an sc-smooth section maps $X_1$ into $Y_{1,1}$, in general not into $Y_{1,2}$. The fibre of $P^1$ carries the topology of $F_1$, not that of the fibre of $P$; it is a Banach space because a fibre of a strong bundle is, through a chart, a closed subspace of its fibre model (`StrongBundleChart.isBanachable_fiber`) (Findings, Chapter 5, items 140, 141).
- “It is a priori clear” hides condition (3) of the filling on level $1$ ($\ker Dr^1(0) \to \ker\rho^1(0)$ a topological isomorphism), which does not follow from level $0$ alone: an sc-operator can be bijective on level $0$ and not onto on level $1$. It holds for the data of Definition 3.11: subtracting the section $z \mapsto \Gamma(z, -g(0))$ reduces to $g(0) = 0$ with the same fill defect (Lemma 3.17), Proposition 3.52 in sc form makes $Dg(0)$ sc-Fredholm, and its regularity gives the surjectivity on level $1$; the open mapping theorem does the rest (Findings, Chapter 5, items 22, 144). No hypothesis beyond the text’s is added.
- Tameness is not used. The tame form (germ data of $f^1$ in tame charts of $P^1$) is not stated: the tameness of the index raise of a tame chart is not proved, and no counterexample is known (Findings, Chapter 5, item 145). $i \ge 2$ by iteration: V5.13. Hence “stronger”: the strong bundle need not be tame, as in V5.10, and the round-trip audit confirms A ⇒ B, not B ⇒ A (refreshed 2026-11-02; “same” in the fourth addendum, “narrower” before it: no $Y^1 \to X^1$, no filler on level $1$) (Findings, Chapter 5, items 140–146; gap G.41).
- In the text’s germ reading of Definition 3.11 (phase 2) $s^1$ is an sc⁺-germ on the shifted germ of $s$, and the level-$1$ conjugation uses $g - s$ only near $0$ (Findings, Chapter 3, item 333).

### V5.15. $\mathbb R$ as an M-polyfold; sc-smooth functions

*not in the book* · presupposed by the text

**HWZ (§5.3, Definition 5.9, p. 173; §5.4.2).** "A sc-smooth map $f : X \to \mathbb R$" (Definitions 5.9, 5.29, 5.33).

**Proved in Lean.** `realPolyfold` ($\mathbb R$, constant structure, chart $\mathrm{id}$). Sc-smoothness is local in charts (`isScSmoothMap_of_local`); constants and $\sigma \circ f$ for $C^\infty$ $\sigma$ are sc-smooth.

- `Polyfold.realPolyfold` — Polyfold/Chapter5/BumpFunctions.lean, line 150
- `Polyfold.realChart` — Polyfold/Chapter5/BumpFunctions.lean, line 134
- `Polyfold.isChart_realChart` — Polyfold/Chapter5/BumpFunctions.lean, line 158
- `Polyfold.MPolyfold.isScSmoothMap_of_local` — Polyfold/Chapter5/BumpFunctions.lean, line 172
- `Polyfold.MPolyfold.IsScSmoothMap.real_chart` — Polyfold/Chapter5/BumpFunctions.lean, line 195
- `Polyfold.isScSmoothMap_real_of_local` — Polyfold/Chapter5/BumpFunctions.lean, line 205
- `Polyfold.isScSmoothMap_real_const` — Polyfold/Chapter5/BumpFunctions.lean, line 214
- `Polyfold.isScSmoothMap_real_of_contDiff` — Polyfold/Chapter5/BumpFunctions.lean, line 223
- `Polyfold.MPolyfold.IsScSmoothMap.comp_contDiff` — Polyfold/Chapter5/BumpFunctions.lean, line 232

*What differs.*
- The M-polyfold $\mathbb R$ is needed for "sc-smooth function" to mean Definition 2.14 (Findings, Chapter 5, item 40).

### V5.16. Definitions 5.9 and 5.29: sc-smooth bump functions

*restated* · $f \ne 0$ read as $f(x) \ne 0$ · weak ⇐ bump points dense · weak ⇒ pointwise at smooth points of $E$

**HWZ (§5.3, Definition 5.9, p. 173; §5.4.2, Definition 5.29, p. 192).** Definition 5.9: for every $x$ and open $U(x)$ an sc-smooth $f : X \to \mathbb R$ with $f \ne 0$ and $\operatorname{supp}(f) \subseteq U(x)$. Definition 5.29: $f$ "not identically zero".

**Proved in Lean.** `AdmitsBumpFunctions`: $f(x) \ne 0$ and $\operatorname{supp} f \subseteq U$. `AdmitsBumpFunctionsWeak`: Definition 5.29 as written, implied by the first. `HasBumpAt`: $x$ is a bump point if every open $U \ni x$ carries an sc-smooth $f$ with $f(x) \ne 0$ and $\operatorname{supp} f \subseteq U$; the pointwise reading is “every point is a bump point”, and the weak reading follows from “the bump points are dense” (`admitsBumpFunctionsWeak_of_dense`). On an sc-Banach space the weak reading gives a bump point at every smooth point (`AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth`); on M-polyfolds built on sc-Hilbert spaces the pointwise reading holds (`admitsBumpFunctions_of_hilbert`).

- `Polyfold.MPolyfold.AdmitsBumpFunctions` — Polyfold/Chapter5/BumpFunctions.lean, line 248
- `Polyfold.MPolyfold.AdmitsBumpFunctionsWeak` — Polyfold/Chapter5/BumpFunctions.lean, line 254
- `Polyfold.MPolyfold.AdmitsBumpFunctions.weak` — Polyfold/Chapter5/BumpFunctions.lean, line 261
- `Polyfold.MPolyfold.HasBumpAt` — Polyfold/Chapter5/BumpWeakPointwise.lean, line 72
- `Polyfold.MPolyfold.admitsBumpFunctionsWeak_of_dense` — Polyfold/Chapter5/BumpWeakPointwise.lean, line 87
- `Polyfold.MPolyfold.AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth` — Polyfold/Chapter5/BumpWeakPointwise.lean, line 179
- `Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert` — Polyfold/Chapter5/BumpFunctions.lean, line 510

*What differs.*
- Proposition 5.30's proof needs $g(x) \ne 0$; without translations a bump cannot be moved to $x$. Whether the weak reading suffices is open at non-smooth points: on an sc-Banach space the weak reading gives a bump at every smooth point (`AdmitsBumpFunctionsWeak.hasBumpAt_of_mem_smooth`; translation by a non-smooth vector does not preserve the levels), on Hilbert models both readings hold everywhere (`admitsBumpFunctions_of_hilbert`), and the weak reading is the density of the bump points (`HasBumpAt`; one direction formalized) (Findings, Chapter 5, items 41, 160–163). Updated in the fourth addendum of this page.

### V5.17. Propositions 5.10 and 5.30

*as in the book* · $\sigma$ misprinted

**HWZ (§5.3, Proposition 5.10, p. 173; §5.4.2, Proposition 5.30, p. 193).** With sc-smooth bump functions, for every $x$ and $U(x)$ an sc-smooth $f : X \to [0, 1]$ with $f(x) = 1$, $\operatorname{supp}(f) \subseteq U(x)$, and $f \equiv 1$ near $x$.

**Proved in Lean.** `proposition_5_30`, `proposition_5_10`: the statement, from Definition 5.9 as read in V5.16.

- `Polyfold.proposition_5_30` — Polyfold/Chapter5/BumpFunctions.lean, line 271
- `Polyfold.proposition_5_10` — Polyfold/Chapter5/BumpFunctions.lean, line 300

*What differs.*
- The text's $\sigma$ ("$0$ for $s \le 1$ and $1$ for $s \ge 1$") is not a function and $g(x) = 1$ is not given; $f = \tau(3g/g(x) - 1)$ (Findings, Chapter 5, item 42).

### V5.18. The sc-calculus of sections: $f \cdot s$ and sums

*not in the book* · used, not stated

**HWZ (§5.3, p. 173; proof of Lemma 5.11).** $\Gamma^+(P)$; "the sc⁺-section $s(y) = \beta(y)t(y)$"; the finite combinations $\sum\lambda_is_i$ of Theorems 5.13 and 5.18.

**Proved in Lean.** `IsScPlusSection.smul_left`: $f \cdot s$ is sc⁺ for $f$ sc-smooth and $s$ sc⁺; `IsScPlusSection.add`, `isScPlusSection_sectionSum`; the zero section is sc⁺; sc⁺-sections take values in $Y_{0,1}$.

- `Polyfold.sectionSupport` — Polyfold/Chapter5/BumpFunctions.lean, line 540
- `Polyfold.sectionSmul` — Polyfold/Chapter5/BumpFunctions.lean, line 546
- `Polyfold.sectionSum` — Polyfold/Chapter5/BumpFunctions.lean, line 552
- `Polyfold.StrongBundle.scPlusSections` — Polyfold/Chapter5/BumpFunctions.lean, line 611
- `Polyfold.StrongBundle.IsScPlusSection.mem_oneSet` — Polyfold/Chapter5/BumpFunctions.lean, line 624
- `Polyfold.StrongBundle.isScPlusSection_fiberZero` — Polyfold/Chapter5/BumpFunctions.lean, line 641
- `Polyfold.StrongBundle.IsScPlusSection.smul_left` — Polyfold/Chapter5/BumpFunctions.lean, line 656
- `Polyfold.StrongBundle.IsScPlusSection.add` — Polyfold/Chapter5/BumpFunctions.lean, line 691
- `Polyfold.StrongBundle.isScPlusSection_sectionSum` — Polyfold/Chapter5/BumpFunctions.lean, line 740

*What differs.*
- In a chart $(f \cdot s)^\wedge = (f \circ \varphi^{-1}) \cdot \hat s$ and the product rule of the sc-calculus applies (Findings, Chapter 5, item 45).

### V5.19. Local sc⁺-sections cut off and extended by $0$

*not in the book* · extension by $0$ proved

**HWZ (§5.3, proof of Lemma 5.11, p. 174).** "If we construct $s \in \Gamma^+(W|Q)$ with support in $Q'$ we can extend it by $0$ to $X$."

**Proved in Lean.** `isScPlusSection_cutoffSection`: for a chart of the atlas, $\tau$ with $z \mapsto (z, \tau(z))$ sc-smooth into $K[1]$ and $\beta$ sc-smooth with $\operatorname{supp}\beta \subseteq \operatorname{dom}\varphi$, the section $\Phi^{-1}(\varphi(y), \beta(y)\tau(\varphi(y)))$, $0$ outside, is sc⁺.

- `Polyfold.StrongBundle.cutoffSection` — Polyfold/Chapter5/BumpFunctions.lean, line 779
- `Polyfold.StrongBundle.isScPlusSection_cutoffSection` — Polyfold/Chapter5/BumpFunctions.lean, line 850

*What differs.*
- The two open sets $\operatorname{dom}\varphi$ and $X \setminus \operatorname{supp}\beta$ cover $X$ (Findings, Chapter 5, item 46 (c)).

### V5.20. Lemma 5.11: existence of sc⁺-sections

*stronger* · bound at every point · no tameness, no centred chart

**HWZ (§5.3, Lemma 5.11, p. 173 (proof p. 174)).** For a tame strong bundle over a tame $X$ with sc-smooth bump functions, an auxiliary norm $N$, smooth $x$, smooth $e \in Y_x$, $\varepsilon > 0$ and open $U \ni x$: an $s \in \Gamma^+(P)$ with $s(x) = e$, $\operatorname{supp}(s) \subseteq U$, $N(s(x)) < N(e) + \varepsilon$.

**Proved in Lean.** `lemma_5_11`: with bump functions (V5.16) and an auxiliary norm, an sc⁺-section with $s(x) = e$, $\operatorname{supp}s \subseteq U$ and $N(s(y)) < N(e) + \varepsilon$ for **all** $y$; no tameness.

- `Polyfold.lemma_5_11` — Polyfold/Chapter5/BumpFunctions.lean, line 907

*What differs.*
- The bound at $x$ is trivial; the proof gives, and §5.3 needs, the uniform bound. Normality of $X$ and a centred chart are not needed (Findings, Chapter 5, item 46).

### V5.21. $\Gamma^{+,1}_U(P)$, the allowable sections, and the metric $\rho$

*restated* · “not complete” read as “in general” · not complete over $\mathbb R$ (an example) · complete for $U = \emptyset$

**HWZ (§5.3, p. 174).** $\Gamma^{+,1}_U(P)$: the $s \in \Gamma^+(P)$ with $\operatorname{supp}(s) \subseteq U$ and $N(s(x)) \le 1$ for all $x$, a metric space for $\rho(s, s') = \sup_xN(s(x) - s'(x))$, not complete.

**Proved in Lean.** `allowableSections N U`; `sectionDistAt`: $N(s(x) - s'(x))$ in the fibre $(Y_{0,1})_x$. `allowableDist`: $\rho(s, s') = \sup_xN(s(x) - s'(x))$, finite ($\rho \le 2$); for an auxiliary norm $N$ a metric on $\Gamma^{+,1}_U(P)$ (`allowableMetric`), with $\rho(s, s') \le \varepsilon$ iff $N(s(x) - s'(x)) \le \varepsilon$ for all $x$. Not complete for the trivial bundle $\mathbb R \times \mathbb R \to \mathbb R$ with $N(x, v) = |v|$ and $U = \mathbb R$ (`TrivialBundle.not_completeSpace_allowableSections`); complete for $U = \emptyset$, for every bundle and auxiliary norm (`completeSpace_allowableSections_empty`), and over a point with fibre $\mathbb R^k$ (`TrivialBundle.completeSpace_allowableSections_point`).

- `Polyfold.StrongBundle.allowableSections` — Polyfold/Chapter5/BumpFunctions.lean, line 616
- `Polyfold.StrongBundle.sectionDistAt` — Polyfold/Chapter5/Transversality.lean, line 1786
- `Polyfold.StrongBundle.allowableDist` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 110
- `Polyfold.StrongBundle.allowableMetric` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 184
- `Polyfold.StrongBundle.allowableDist_le_iff` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 142
- `Polyfold.TrivialBundle.not_completeSpace_allowableSections` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 491
- `Polyfold.StrongBundle.completeSpace_allowableSections_empty` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 223
- `Polyfold.TrivialBundle.completeSpace_allowableSections_point` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 556

*What differs.*
- The text’s “$(\Gamma^{+,1}_U(P), \rho)$ is not complete” is false without a hypothesis: for $U = \emptyset$ the space is a point, and over a point with finite-dimensional fibre it is the closed unit ball of $\mathbb R^k$. It is read as “not complete in general” and proved by an example: the allowable sections $s_j(x) = (x, \sqrt{x^2 + 1/(j+1)^2}/(2\sqrt{1 + x^2}))$ form a $\rho$-Cauchy sequence whose pointwise limit has fibre part $|x|/(2\sqrt{1 + x^2})$, not differentiable at $0$, while the fibre part of an sc⁺-section of the trivial bundle is $C^1$. That non-completeness holds whenever $U$ contains a non-isolated point over which $Y_{0,1}$ is nonzero (the text’s setting) is expected by the same mechanism and not formalized (Findings, Chapter 5, items 150–153; gap G.42).
- Only Definition 5.1 (1) is used for the metric axioms (symmetry and subadditivity of the fibre norms, $N$ vanishing only at $0_x$); the density statements of Theorems 5.13 and 5.18 are $\rho(s, s') \le \varepsilon$ (`allowableDist_le_iff`; V5.30, V5.39). Hence still “restated”; before the fourth addendum of this page $\rho$ was used pointwise only and the metric space was not formalized (Findings, Chapter 5, item 47).

### V5.22. Remark 5.12

*restated* · compact: closedness proved · completion as uniform $N$-limits

**HWZ (§5.3, Remark 5.12, p. 174).** If $s$ is in the completion of $\Gamma^{+,1}_U(P)$, the solution set of $f + s = 0$ is still compact, provided $f$ has a compact solution set and $U$ is adapted to $N$.

**Proved in Lean.** `remark_5_12`: if $\operatorname{cl}\{x \in U \mid N(f(x)) \le 1\}$ is compact and $s$ vanishes off $U$ with $N(s) \le 1$, the zeros of $f + s$ lie in $\{x \in U \mid N(f(x)) \le 1\}$, with compact closure. As stated (`remark_5_12_completion`): with the points of the completion represented by sections $s$ with values in $Y_{0,1}$ that are uniform $N$-limits of allowable sections (`IsInAllowableCompletion`), for $f$ continuous and $U \supseteq f^{-1}(0)$ with $\operatorname{cl}\{x \in U \mid N(f(x)) \le 1\}$ compact, the solution set of $f + s$ is closed, hence compact; for $f$ sc-Fredholm with compact solution set, with the $U$ of Theorem 5.5 (`remark_5_12_of_isScFredholmSection`).

- `Polyfold.remark_5_12` — Polyfold/Chapter5/Compactness.lean, line 993
- `Polyfold.StrongBundle.IsAuxNorm.auxLe_of_sectionAdd` — Polyfold/Chapter5/Compactness.lean, line 885
- `Polyfold.StrongBundle.IsInAllowableCompletion` — Polyfold/Chapter5/SolutionSetClosed.lean, line 85
- `Polyfold.StrongBundle.IsInAllowableCompletion.isClosed_solutionSet_sectionAdd` — Polyfold/Chapter5/SolutionSetClosed.lean, line 157
- `Polyfold.remark_5_12_completion` — Polyfold/Chapter5/SolutionSetClosed.lean, line 268
- `Polyfold.remark_5_12_of_isScFredholmSection` — Polyfold/Chapter5/SolutionSetClosed.lean, line 285

*What differs.*
- The closedness of the solution set, which the remark does not discuss, is proved for every $s$ in the completion by a chart argument: Lemma 5.2's bound turns $N(s - s') \le \varepsilon$ into a level-$0$ bound in a chart, and $f + s'$ is continuous for allowable $s'$ (Findings, Chapter 5, item 130; before, only the compact closure, item 27). “Adapted” is read as properness. The completion is represented by sections, uniform $N$-limits of allowable sections; the metric space $(\Gamma^{+,1}_U(P), \rho)$ is V5.21 (fourth addendum), and that every $\rho$-Cauchy sequence has such a limit section is not formalized (items 131, 153). Updated in the third addendum of this page.

### V5.23. Definition 5.15: transversal to the zero section

*restated* · read in charts

**HWZ (§5.3, Definition 5.15, p. 175).** $g$ is transversal to the zero section if at every $x$ with $g(x) = 0$ the linearization $g'(x) : T_xX \to Y_x$ is surjective.

**Proved in Lean.** `IsTransversal g`: `IsLinSurjAt` at every zero ($\mathrm{Lin}(z) : T_zO \to K_z$ onto in a chart), hence onto in every chart.

- `Polyfold.StrongBundle.IsTransversal` — Polyfold/Chapter5/Transversality.lean, line 362
- `Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective` — Polyfold/Chapter3/GlobalIFTIndex.lean, line 263

*What differs.*
- $T_xX$ has no linear structure here (gap G.7 of Chapter 2) (Findings, Chapter 5, item 70).

### V5.24. Spanning sc⁺-sections at a zero

*not in the book* · density of smooth vectors

**HWZ (§5.3, proof of Theorem 5.13, p. 175).** "For every $x \in S_{f+s_0}$ we find finitely many allowable sc⁺-sections $s^1_x, \dots, s^{k_x}_x$ such that the range of $(f + s_0)'(x)$ together with the sections span $Y_x$."

**Proved in Lean.** `exists_spanning_sections`: at a zero $y$ of an sc-Fredholm $g$, for every open $U \ni y$, finitely many allowable sc⁺-sections supported in $U$ and a chart centred at $y$ with $\mathrm{Lin}(0)(T_0O) + \operatorname{span}\{\hat s_i(0)\} = K_0$.

- `Polyfold.exists_fin_mem_of_dense_of_closedComplemented` — Polyfold/Chapter5/Transversality.lean, line 177
- `Polyfold.exists_spanning_sections` — Polyfold/Chapter5/Transversality.lean, line 509

*What differs.*
- The text does not say how: finitely many smooth vectors of the dense $\rho(0)F_\infty$ span a complement of the closed finite-codimensional range, and Lemma 5.11 realizes them (Findings, Chapter 5, item 66).

### V5.25. The parametrized section and its slices

*not in the book* · $|\lambda|$ the maximum norm

**HWZ (§5.3, proof of Theorem 5.13, pp. 175–176).** $(\lambda, y) \mapsto f(y) + s_0(y) + \sum\lambda_jt_j(y)$ is sc-Fredholm (Theorem 3.18); "there is a number $\delta_0 > 0$ such that $|\lambda| < \delta_0$ implies $N(\sum\lambda_jt_j(y)) < \varepsilon/2$".

**Proved in Lean.** `paramSlice`: the slice $g + \sum\lambda_it_i$; zeros of $F$ are zeros of slices; slices are sc-Fredholm (Theorem 3.15) and, of sc⁺-sections, sc⁺; `auxLe_paramSlice`: $N(s_0 + \sum\lambda_it_i) \le 1$ for $m|\lambda| \le \varepsilon$.

- `Polyfold.paramSlice` — Polyfold/Chapter5/Transversality.lean, line 627
- `Polyfold.isZeroAt_paramSection_iff` — Polyfold/Chapter5/Transversality.lean, line 647
- `Polyfold.isScFredholmSection_paramSlice` — Polyfold/Chapter5/Transversality.lean, line 686
- `Polyfold.isScPlusSection_paramSlice` — Polyfold/Chapter5/Transversality.lean, line 1204
- `Polyfold.sectionSupport_paramSlice_subset` — Polyfold/Chapter5/Transversality.lean, line 1213
- `Polyfold.auxLe_paramSlice` — Polyfold/Chapter5/Transversality.lean, line 1227

*What differs.*
- The text's "$N(s_0(y) + s(\lambda_0, y)) \le 1 - \varepsilon/2$" is $\le 1$ (Findings, Chapter 5, item 62).

### V5.26. "Regular value ⇔ transversal"; $F$ transversal at $(0, y)$

*not in the book* · only ⇒ needed

**HWZ (§5.3, proof of Theorem 5.13, pp. 175–176).** "The linearization at the point $(0, x)$ is surjective"; "taking a regular value $\lambda_0$ for the projection $\tilde S \to \mathbb R^m$ it is easily verified that $f + s_0 + s(\lambda_0, \cdot)$ is transversal".

**Proved in Lean.** `surjective_of_forall_exists_ker_fst` (and its converse): for $M(a, u) = Lu + \sum a_ie_i$ onto, $\ker M \to \mathbb R^m$ onto iff $L$ onto. `isLinSurjAt_paramSlice_of_ker_fst`: a slice is transversal where $\ker\mathrm{Lin}_F$ projects onto $\mathbb R^m$. Spanning sections make $F$ transversal at $(0, y)$, also after adding sections.

- `Polyfold.surjective_of_forall_exists_ker_fst` — Polyfold/Chapter5/Transversality.lean, line 156
- `Polyfold.forall_exists_ker_fst_of_surjective` — Polyfold/Chapter5/Transversality.lean, line 167
- `Polyfold.isLinSurjAt_paramSlice_of_ker_fst` — Polyfold/Chapter5/Transversality.lean, line 784
- `Polyfold.isLinSurjAt_paramSection_zero_of_spanning` — Polyfold/Chapter5/Transversality.lean, line 893
- `Polyfold.isLinSurjAt_paramSection_zero_of_comp` — Polyfold/Chapter5/Transversality.lean, line 1005

*What differs.*
- The text's "⇔" for $\tilde S$ needs $T\tilde S = \ker F'$; only "regular value ⇒ transversal" is used, and $\operatorname{range}D(\mathrm{gmap}) \subseteq \ker\mathrm{Lin}_F$ suffices (Findings, Chapter 5, items 64, 67).

### V5.27. The openness steps and the omitted compactness step

*not in the book* · omitted step proved · tame germ data

**HWZ (§5.3, proof of Theorem 5.13, pp. 175–176).** "In view of the interior case of the implicit function theorem, Theorem 3.19, there exists an open neighborhood $U(x)$"; "by the implicit function theorem we find an open neighborhood $U \subset \{|\lambda| < \delta_0\} \oplus X$ of $\{0\} \times S_{f+s_0}$".

**Proved in Lean.** $\partial(\mathbb R^m \times X) = \emptyset$; solution sets are closed; transversality of $F$ at $(0, x)$ spreads to nearby $(0, y)$; an open $V \supseteq \{0\} \times S_g$ of zeros of $F$ in good position (tame germ data); `exists_pos_forall_mem_of_isCompact`: $V$ contains the zeros over $|\lambda| < \delta$.

- `Polyfold.isWithoutBoundary_prod_rn` — Polyfold/Chapter5/Transversality.lean, line 944
- `Polyfold.isClosed_solutionSet` — Polyfold/Chapter5/Transversality.lean, line 956
- `Polyfold.exists_isOpen_isLinSurjAt_zero_near` — Polyfold/Chapter5/Transversality.lean, line 1103
- `Polyfold.exists_isOpen_goodPosition_of_isLinSurjAt` — Polyfold/Chapter5/Transversality.lean, line 1064
- `Polyfold.exists_pos_forall_mem_of_isCompact` — Polyfold/Chapter5/Transversality.lean, line 1130

*What differs.*
- The passage to $|\lambda| < \delta_0$ needs the compactness of the zeros over $|\lambda| \le \delta_1$ (Remark 5.12) (Findings, Chapter 5, item 63).
- The §3.6 theorems are applied to $F$ on $\mathbb R^m \times X$ with tame germ data from Theorem 3.18 (Findings, Chapter 5, items 68, 75).

### V5.28. The Sard step

*not in the book* · stratified Sard · $\tilde S$ not built

**HWZ (§5.3, proof of Theorem 5.13, p. 176).** "$\tilde S := F^{-1}(0)$ is a smooth manifold"; "taking a regular value $\lambda_0$ for the projection $\tilde S \to \mathbb R^m$".

**Proved in Lean.** `exists_null_isLinSurjAt_paramSlice_near`: at a zero $z_0$ of $F$ in good position (tame chart), an open $W \ni z_0$ and a null set $CV$ such that the slices over $\lambda \notin CV$ are transversal at their zeros in $W$.

- `Polyfold.exists_null_isLinSurjAt_paramSlice_near` — Polyfold/Chapter5/Transversality.lean, line 1299

*What differs.*
- Sard is applied on the model of the regular tangent germ chart of Theorem 3.54 (2), stratum by stratum, so interior points need not be identified (Findings, Chapter 5, item 65).

### V5.29. Theorem 5.13, generic form

*hypotheses explicit* · tame germ data · generic = off a null set

**HWZ (§5.3, Theorem 5.13, pp. 174–175 (proof pp. 175–176)).** $\partial X = \emptyset$, bump functions, $f$ sc-Fredholm with compact solution set, $N$ auxiliary: an open $U \supseteq S$ with $S_{f+s}$ compact for $s \in \Gamma^+(P)$, $\operatorname{supp}(s) \subseteq U$, "$N(f(x)) \le 1$", and a dense $O \subseteq (\Gamma^{+,1}_U(P), \rho)$ with $f + s$ transversal for $s \in O$, "the germ $(f, x)$ in good position", $S_{f+s}$ a compact manifold without boundary.

**Proved in Lean.** `theorem_5_13_generic` ($f$ with tame germ data): $U$ with $S_{f+s}$ compact for allowable $s$; for $s_0$ with $\operatorname{supp}s_0 \subseteq U$, $N(s_0) \le 1 - \varepsilon$: allowable $t_1, \dots, t_m$, $\delta$, a null $CV$, and for $|\lambda| < \delta$, $\lambda \notin CV$: $s_0 + \sum\lambda_it_i$ allowable, $f + s_\lambda$ transversal, $S_{f+s_\lambda}$ compact and, if non-empty, a tame manifold without boundary of dimension the index (`SolutionSetIsManifold`).

- `Polyfold.theorem_5_13_generic` — Polyfold/Chapter5/Transversality.lean, line 1591
- `Polyfold.StrongBundle.SolutionSetIsManifold` — Polyfold/Chapter5/Transversality.lean, line 1553

*What differs.*
- "$N(f(x)) \le 1$" is $N(s(x)) \le 1$; "$(f, x)$ in good position" is $(f + s, x)$ (Findings, Chapter 5, item 62).
- $f$ has tame germ data (Definition 3.51), the reading of §5.3's tame strong bundle; earlier statements with every chart tame were vacuous (Findings, Chapter 5, items 74, 75).

### V5.30. Theorem 5.13, the text's dense form

*hypotheses explicit* · density = $\rho(s, s') \le \varepsilon$

**HWZ (§5.3, Theorem 5.13, pp. 174–175).** "There exists a dense subset $O$ of the metric space $(\Gamma^{+,1}_U(P), \rho)$ such that for every $s \in O$" $f + s$ is transversal and $S_{f+s}$ is a compact manifold without boundary.

**Proved in Lean.** `theorem_5_13`: for every allowable $s'$ and $\varepsilon > 0$ an allowable $s$ with $N(s(x) - s'(x)) \le \varepsilon$ for all $x$, $f + s$ transversal, $S_{f+s}$ compact and, if non-empty, a manifold without boundary.

- `Polyfold.theorem_5_13` — Polyfold/Chapter5/Transversality.lean, line 1806
- `Polyfold.StrongBundle.allowableDist_le_iff` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 142

*What differs.*
- The pointwise bound is $\rho(s, s') \le \varepsilon$ (`allowableDist_le_iff`), so this is density in the metric space of V5.21, built in the fourth addendum of this page (before, the metric space was not built) (Findings, Chapter 5, items 60, 150).

### V5.31. Definition 5.17: general position, in a tame chart

*restated* · in a tame chart · chart independence: V5.34

**HWZ (§5.3, Definition 5.17, p. 177).** $(f, x)$, $f(x) = 0$, is in general position if $f'(x) : T_xX \to Y_x$ is surjective and $\ker f'(x)$ has an sc-complement contained in $T^R_xX$.

**Proved in Lean.** `IsGeneralPositionGerm f y`: in a tame strong bundle chart around $y$, $\mathrm{Lin}(z)$ onto $K_z$, and for every presentation $T$ an sc-subspace $B \subseteq T^R_zO$ with $(T_zO)_m = (\ker\mathrm{Lin}(z))_m \oplus B_m$ on every level.

- `Polyfold.StrongBundle.IsGeneralPositionGerm` — Polyfold/Chapter5/Transversality.lean, line 380
- `Polyfold.StrongBundleChart.linKer` — Polyfold/Chapter5/Transversality.lean, line 366
- `Polyfold.StrongBundle.IsGeneralPositionGerm.isLinSurjAt` — Polyfold/Chapter5/Transversality.lean, line 395

*What differs.*
- $T^R_xX$ is the reduced tangent space of a tame M-polyfold, so the chart is tame (Findings, Chapter 5, item 76); chart independence near zeros in good position is V5.34 (Findings, Chapter 5, item 82).

### V5.32. The bridge lemma: solution sets as smooth submanifolds

*not in the book* · Definition 4.13 verified

**HWZ (§5.3, proof of Theorem 5.18, p. 179).** "$\tilde S \subset \mathbb R^m \oplus X$ is a smooth submanifold with boundary with corners ... Hence we can apply Theorem 4.23."

**Proved in Lean.** Regular tangent germ data (Definition 3.25 (2)) give the sc⁺-retraction $\tau = \Gamma \circ \pi \circ r$ (`exists_scPlusRetraction`), so `isSmoothSubmanifold_of_isRegular`; `isSmoothSubmanifold_solutionSet_inter`: the zeros in an open $W$ all in good position form a smooth finite-dimensional submanifold (Definition 4.13).

- `Polyfold.isScPlus_of_isScSmooth_const` — Polyfold/Chapter5/GeneralPosition.lean, line 95
- `Polyfold.MPolyfold.TangentGermChart.exists_scPlusRetraction` — Polyfold/Chapter5/GeneralPosition.lean, line 149
- `Polyfold.MPolyfold.TangentGermChart.exists_isScPlusRetractionOn` — Polyfold/Chapter5/GeneralPosition.lean, line 284
- `Polyfold.MPolyfold.isSmoothSubmanifold_of_isRegular` — Polyfold/Chapter5/GeneralPosition.lean, line 307
- `Polyfold.StrongBundle.isSmoothSubmanifold_solutionSet_inter` — Polyfold/Chapter5/GeneralPosition.lean, line 422

*What differs.*
- The implicit function theorem gives tangent germ data, not the sc⁺-retractions of Definition 4.13 that Theorem 4.23 needs (Findings, Chapter 5, item 81).

### V5.33. $T_yS = \ker f'(y)$

*not in the book* · dimension count

**HWZ (§5.3, proofs of Theorems 5.18, 5.25, Lemma 5.24, p. 179).** "$T_zS_\lambda$ has a sc-complement contained in $T^R_xX$"; "in view of $T_xS = \ker(f'(x))$".

**Proved in Lean.** `tangentSpace_subset_linKer`: tangent spaces of retracts where the principal part vanishes lie in $\ker\mathrm{Lin}(z)$. `exists_tangentSpace_eq_linKer`: near a zero in good position, in every chart, the tangent space of the chart image of the solution set is $\ker\mathrm{Lin}(z)$.

- `Polyfold.tangentSpace_subset_linKer` — Polyfold/Chapter5/GeneralPosition.lean, line 451
- `Polyfold.MPolyfold.TangentGermChart.exists_linearIndependent_tangentSpace` — Polyfold/Chapter5/GeneralPosition.lean, line 226
- `Polyfold.HasIndepTangent.transport` — Polyfold/Chapter5/GeneralPosition.lean, line 378
- `Polyfold.exists_tangentSpace_eq_linKer` — Polyfold/Chapter5/GeneralPosition.lean, line 508

*What differs.*
- "⊇": $\dim\ker\mathrm{Lin}(z) = d$ in every chart, and $d$ independent tangent vectors of the bridge retraction carried by chart changes (Findings, Chapter 5, item 82).

### V5.34. Definition 5.17 = Definition 4.21 for the solution set

*not in the book* · chart independence of 5.17

**HWZ (§5.3, Definition 5.17, p. 177; proof of Theorem 5.18).** General position of the section (Definition 5.17) and of the solution set (Definition 4.21, "for every $x \in S_\lambda$ ... the tangent space has a sc-complement contained in $T^R_xX$") are used interchangeably.

**Proved in Lean.** `exists_isGeneralPositionGerm_iff`: near a zero in good position, $(f, y)$ is in general position iff $S_f \cap V$ is in general position at $y$, chart independently. `isGoodPositionGermTame_of_isGeneralPositionAt`: $f'(y)$ onto and a submanifold $A \subseteq S_f$ in general position at $y$ give good position.

- `Polyfold.exists_isGeneralPositionGerm_iff` — Polyfold/Chapter5/GeneralPosition.lean, line 715
- `Polyfold.isGoodPositionGermTame_of_isGeneralPositionAt` — Polyfold/Chapter5/GeneralPosition.lean, line 653

*What differs.*
- Resolves the chart independence of Definition 5.17 left open in Findings, Chapter 5, item 71 (Findings, Chapter 5, items 82, 85).

### V5.35. Openness of general position

*not in the book* · used without proof · $X$ tame

**HWZ (§5.3, proof of Theorem 5.18, pp. 178–179).** "If for a section the properties (i)–(ii) hold at the specific $(0, x)$, then they will also hold at $(0, y)$ for $y \in S_f$ close to $x$"; "the properties (i)–(ii) hold for all $(\lambda, y) \in \tilde S$".

**Proved in Lean.** `exists_isOpen_isGeneralPositionGerm` ($X$ tame): general position at a zero $x_0$ gives an open $W \ni x_0$ with $S_f \cap W$ a smooth submanifold and good and general position at all zeros of $W$. Definition 4.21 is local (`IsGeneralPositionAt.congr_nhds`).

- `Polyfold.exists_isOpen_isGeneralPositionGerm` — Polyfold/Chapter5/GeneralPosition.lean, line 787
- `Polyfold.MPolyfold.IsGeneralPositionAt.congr_nhds` — Polyfold/Chapter5/GeneralPosition.lean, line 318

*What differs.*
- Proved through V5.34 and Theorem 4.22 (3) (Findings, Chapter 5, item 83).

### V5.36. Properties (i)–(ii) of the proof of Theorem 5.18

*restated* · $L$ spanned by smooth vectors

**HWZ (§5.3, proof of Theorem 5.18, p. 178).** (i) $F'(0, x)$ is surjective; (ii) $\ker F'(0, x)$ is transversal to $\mathbb R^m \oplus T^R_xX$. "Adding more sections, the properties (i)–(ii) will still hold"; "we take a linear subspace $L$ complementing $T^R_xX$ in $T_xX$ and add sections, which at $x$ span the image $f'(x)L$."

**Proved in Lean.** `IsParamGP` in a chart centred at $y$; `IsParamGP.comp` (adding sections); (i)–(ii) ⇔ general position of $F$ at $(0, y)$ in a tame chart; `exists_sections_isParamGP`: finitely many allowable sections supported in $U$ achieve them.

- `Polyfold.StrongBundleChart.IsParamGP` — Polyfold/Chapter5/GeneralPosition.lean, line 1111
- `Polyfold.StrongBundleChart.IsParamGP.comp` — Polyfold/Chapter5/GeneralPosition.lean, line 1125
- `Polyfold.isGeneralPositionGerm_paramSection_of_isParamGP` — Polyfold/Chapter5/GeneralPosition.lean, line 1197
- `Polyfold.isParamGP_of_isGeneralPositionGerm` — Polyfold/Chapter5/GeneralPosition.lean, line 1363
- `Polyfold.exists_sections_isParamGP` — Polyfold/Chapter5/GeneralPosition.lean, line 1528

*What differs.*
- $L$ must consist of smooth vectors for Lemma 5.11 to apply; "(i)–(ii) ⇒ general position" needs good position of $F$ first, then $\ker F' = T\tilde S$ (Findings, Chapter 5, item 84).

### V5.37. Theorem 5.18 from a family with (i)–(ii)

*not in the book* · Theorem 4.23, countable form

**HWZ (§5.3, proof of Theorem 5.18, pp. 178–179).** "Since $S_f$ is compact and since, by construction, the section is in general position at every point $(0, x)$, we can apply the implicit function theorem ... Hence we can apply Theorem 4.23."

**Proved in Lean.** `theorem_5_18_of_family` ($X$ tame, $f$ with tame germ data): for every $s_0$ and every allowable family with $F$ in general position at all $(0, x)$, $x \in S_{f+s_0}$: for small $\lambda$ off a null set, $f + s_\lambda$ satisfies `SolutionSetInGeneralPosition` (transversal, general position at every zero, $S$ compact, a submanifold in general position, tame corner structure, $d_S = d_X$).

- `Polyfold.theorem_5_18_of_family` — Polyfold/Chapter5/GeneralPosition.lean, line 864
- `Polyfold.StrongBundle.SolutionSetInGeneralPosition` — Polyfold/Chapter5/GeneralPosition.lean, line 827

*What differs.*
- $\tilde S$ omits the equation $F = 0$ in the text; "$p^{-1}(\{|\lambda| \le \varepsilon\})$ is compact" is the omitted step of V5.27 (Findings, Chapter 5, item 85).

### V5.38. Theorem 5.18: perturbation into general position

*hypotheses explicit* · $X$ tame · tame germ data · generic = off a null set

**HWZ (§5.3, Theorem 5.18, p. 177 (proof pp. 177–179)).** Bump functions, $f$ sc-Fredholm with compact solution set, $N$ auxiliary: an open $U \supseteq S$ with $S_{f+s}$ compact for $s \in \Gamma^{+,1}_U(P)$, and a dense $O \subseteq (\Gamma^{+,1}_U(P), \rho)$ such that for $s \in O$, $(f + s, x)$ is in general position at every $x \in S_{f+s}$; $S_{f+s}$ is a compact manifold with boundary with corners, $d_{S_{f+s}} = d_X$.

**Proved in Lean.** `theorem_5_18` ($X$ tame, $f$ with tame germ data): $U$ as in the text; for every $s_0$ with $N(s_0) \le 1 - \varepsilon$, allowable $t_1, \dots, t_m$, $\delta$ and a null set $CV$ with `SolutionSetInGeneralPosition` for $f + s_0 + \sum\lambda_it_i$, $|\lambda| < \delta$, $\lambda \notin CV$.

- `Polyfold.theorem_5_18` — Polyfold/Chapter5/GeneralPosition.lean, line 1779

*What differs.*
- $X$ tame: the proof uses Theorems 4.22 and 4.23; §5.3 opens with a tame strong bundle (Findings, Chapter 5, item 80).
- "Replacing $f + s_0$ by $f$ and $N$ by $cN$" is not needed; the proof keeps $s_0$ (Findings, Chapter 5, item 85).

### V5.39. Theorem 5.18, the text's dense form

*hypotheses explicit* · $X$ tame · density = $\rho(s, s') \le \varepsilon$

**HWZ (§5.3, Theorem 5.18, p. 177).** "There exists a dense subset $O$ of the metric space $(\Gamma^{+,1}_U(P), \rho)$ such that, for every $s \in O$," $(f + s, x)$ is in general position at every zero.

**Proved in Lean.** `theorem_5_18_dense`: for every allowable $s'$ and $\varepsilon > 0$ an allowable $s$ with $N(s - s') \le \varepsilon$ pointwise and `SolutionSetInGeneralPosition` for $f + s$.

- `Polyfold.theorem_5_18_dense` — Polyfold/Chapter5/GeneralPosition.lean, line 1968

*What differs.*
- As V5.30, with Theorem 5.18 in place of Theorem 5.13 (Findings, Chapter 5, item 80).

### V5.40. Theorem 5.19: perturbation into good position, relative to $\partial X$

*stronger* · no tameness of $X$ · generic form only · IFT for $F$ off $\partial X$

**HWZ (§5.3, Theorem 5.19, p. 180).** Over a tame $X$ with bump functions, $f$ sc-Fredholm with compact solution set, $(f, x)$ in good position at the zeros on $\partial X$: $U$ with $S_{f+s}$ compact for $s \in \Gamma^{+,1}_U(P)$, and an arbitrarily small $s \in \Gamma^{+,1}_U(P)$ with $s = 0$ near $\partial X$, $f + s$ transversal, "$(f, x)$" in good position at every $x \in S_{f+s}$, $S_{f+s}$ a compact manifold with boundary with corners.

**Proved in Lean.** `theorem_5_19` ($f$ with tame germ data): allowable $t_i$ with supports disjoint from $\partial X$, $\delta$, a null $CV$; for $|\lambda| < \delta$, $\lambda \notin CV$: $\sum\lambda_it_i$ allowable, $0$ near $\partial X$, $f + s_\lambda$ transversal and in good position at every zero, $S_{f+s_\lambda}$ compact, a tame manifold with corners. Good position depends only on the germ (`IsGoodPositionGermTame.congr_nhds`).

- `Polyfold.theorem_5_19` — Polyfold/Chapter5/GeneralPosition.lean, line 2119
- `Polyfold.StrongBundle.IsGoodPositionGermTame.congr_nhds` — Polyfold/Chapter3/Chapter5BridgeG.lean, line 77

*What differs.*
- "$(f, x)$ in good position" is $(f + s, x)$ (Findings, Chapter 5, item 87).
- "As before" would apply the implicit function theorem to $F$ at boundary zeros, where $F$ is in general not in good position (gap G.46, on paper); the proof keeps $f + s = f$ near them (Findings, Chapter 5, item 88).
- No dense form (gap G.45).

### V5.41. Definition 5.20: generalized compact homotopy

*restated* · $Y|X_t$ = pull-back · ends = restrictions

**HWZ (§5.3, Definition 5.20, pp. 180–181).** A tame strong bundle $P : Y \to X$, an sc-Fredholm $f$ with compact solution set and an sc-smooth surjective $t : X \to [0, 1]$ with tame M-polyfolds $X_t$, $f_t = f|X_t$ sc-Fredholm sections of $Y|X_t$, and $(f|X_i, P|Y_i) = (f_i, P_i)$.

**Proved in Lean.** `IsGenCompactHomotopy f t`: $X$ tame, $f$ with tame germ data and compact solution set, $t$ sc-smooth with $t(X) = [0, 1]$, every $t^{-1}(\tau)$ a sub-M-polyfold with tame induced structure on which `restrictSection` (a section of the pull-back) has tame germ data. The restricted problems have compact solution sets.

- `Polyfold.restrictSection` — Polyfold/Chapter5/Homotopy.lean, line 205
- `Polyfold.StrongBundle.IsGenCompactHomotopy` — Polyfold/Chapter5/Homotopy.lean, line 233
- `Polyfold.StrongBundle.IsGenCompactHomotopy.isCompact_solutionSet_restrict` — Polyfold/Chapter5/Homotopy.lean, line 252

*What differs.*
- The text does not say what $Y|X_t$ is; the pull-back (Proposition 2.54) is the strong bundle available. Remark 5.21 is not formalized (gap G.47; Findings, Chapter 5, item 100).

### V5.42. Lemma 5.23, and the hidden hypothesis of Theorem 5.22

*hypotheses explicit* · needs $dt(x) \ne 0$

**HWZ (§5.3, Lemma 5.23, p. 182).** "Since $x$ is a smooth point, we find a one-dimensional smooth linear sc-subspace $Z \subset T_xX$ such that $T_xX = Z \oplus \ker(dt(x))$." For $\tau \in T^*_xS$ there is a unique sc-operator $b_\tau : T_xS \to Z$ with $dt(x) \circ b_\tau = \tau$, and $dt(x) \circ (b_\tau + a) = \tau$ for $a : T_xS \to \ker dt(x)$.

**Proved in Lean.** `lemma_5_23` (for $\ell \ne 0$, $Z$ a complement of $\ker\ell$): existence and uniqueness of $b$, and the second claim. `ne_zero_of_isCompl_ker`: a non-zero complement exists only if $\ell \ne 0$; `exists_isCompl_ker_of_ne_zero`: then one spanned by a vector of any spanning set.

- `Polyfold.lemma_5_23` — Polyfold/Chapter5/Homotopy.lean, line 106
- `Polyfold.ne_zero_of_isCompl_ker` — Polyfold/Chapter5/Homotopy.lean, line 150
- `Polyfold.exists_isCompl_ker_of_ne_zero` — Polyfold/Chapter5/Homotopy.lean, line 162

*What differs.*
- At a critical point of $t|S$ with $dt(x) = 0$ no such $Z$ exists; Theorem 5.22 does not assume $t$ submersive there (Findings, Chapter 5, item 101).

### V5.43. The product rule at a level-$1$ point

*not in the book* · tools for Lemma 5.24

**HWZ (§5.3, proof of Lemma 5.24, pp. 182–183).** "$s'(0)(\delta k + \delta l) = j(\delta l)e$" for the section built from $\beta$ and $j$.

**Proved in Lean.** `scDeriv_smul_apply`: $D(a \cdot w)(z)v = Da(z)v \cdot w(z) + a(z)Dw(z)v$; `scDeriv_clm_sub_apply`: $D(\ell(\rho(\cdot) - p))(z) = \ell \circ D\rho(z)$; `chartLinCutoff` $\beta \cdot \ell(\varphi(\cdot) - \varphi(x))$ is sc-smooth.

- `Polyfold.scDeriv_smul_apply` — Polyfold/Chapter5/Homotopy.lean, line 276
- `Polyfold.scDeriv_clm_sub_apply` — Polyfold/Chapter5/Homotopy.lean, line 302
- `Polyfold.chartLinCutoff` — Polyfold/Chapter5/Homotopy.lean, line 337
- `Polyfold.isScSmoothMap_chartLinCutoff` — Polyfold/Chapter5/Homotopy.lean, line 346

*What differs.*
- Calculus the text uses without statement.

### V5.44. Lemma 5.24

*restated* · image in a smooth line: hypothesis · no graph needed

**HWZ (§5.3, Lemma 5.24, pp. 182–183).** For $\tau \in T^*_xS$ there is an sc⁺-section $s$ with small support around $x$, $s(x) = 0$ and $f'(x) \circ b_\tau + (s'(x)|T_xS) = 0$.

**Proved in Lean.** `exists_scPlusSection_linAt`: an sc⁺-section with $s(x) = 0$, small support and $\mathrm{Lin}_s(z)v = \ell(v)\Phi(e)_2$ on $T_zO$. `lemma_5_24`: for finite-dimensional $K \subseteq T_zO$ and $b : K \to T_zO$ with $\mathrm{Lin}_f(z)(bv) \in \mathbb R\Phi(e)_2$, an $s$ with $\mathrm{Lin}_f(z)(bv) + \mathrm{Lin}_s(z)v = 0$ on $K$.

- `Polyfold.exists_scPlusSection_linAt` — Polyfold/Chapter5/Homotopy.lean, line 415
- `Polyfold.lemma_5_24` — Polyfold/Chapter5/Homotopy.lean, line 527

*What differs.*
- "The image of any vector in $T_xS$ belongs to $Y_\infty$" is not formalized; it becomes the hypothesis on $e$. The graph of $S$ and the case "the operator is zero" are not needed (Findings, Chapter 5, item 102).

### V5.45. Theorem 5.25: perturbation into good position

*restated* · $U$ produced, not given · tame germ data

**HWZ (§5.3, Theorem 5.25, pp. 186–187 (proof pp. 187–188)).** Over a tame $X$ with bump functions, $f$ proper sc-Fredholm, $N$ auxiliary and "an associated open neighborhood $U$" with $S_{f+s}$ compact for $s \in \Gamma^{+,1}_U(P)$: some $s \in \Gamma^{+,1}_U(P)$ puts $(f + s, x)$ in good position at every $x \in S_{f+s}$; $S_{f+s}$ is a manifold with boundary with corners.

**Proved in Lean.** `theorem_5_25` ($f$ with tame germ data): an open $U \supseteq S_f$ with $S_{f+s}$ compact for allowable $s$, and an allowable $s$ with $(f + s, x)$ in good position in a tame chart at every zero and `SolutionSetInGeneralPosition` for $f + s$.

- `Polyfold.theorem_5_25` — Polyfold/Chapter5/GeneralPosition.lean, line 1914

*What differs.*
- "In view of Theorem 3.54 ... in general position" is the openness of V5.35; "$x \in S_f$" is $x \in S_{f+s_0}$; "Theorem 5.22 [20]" is a garbled reference (Findings, Chapter 5, item 86).

### V5.46. Lemma 5.26: general position implies good position

*stronger* · interior condition proved · no tameness of $X$

**HWZ (§5.3, Lemma 5.26, p. 187).** For an sc-Fredholm section over a tame $X$: if $f$ is in general position, then $f$ is in good position ("clearly general position implies good position", p. 179).

**Proved in Lean.** `isInGoodPositionIn_of_scComplement_le_reduced`: in a tame retract a subspace with a complement inside $T^R_zO$ is in good position, interior condition included. `IsGeneralPositionGerm.isGoodPositionGerm`: general position (in a tame chart) ⇒ good position; `.isGoodPositionGermTame` in the tame chart of the germ data.

- `Polyfold.isInGoodPositionIn_of_scComplement_le_reduced` — Polyfold/Chapter5/Transversality.lean, line 288
- `Polyfold.StrongBundle.IsGeneralPositionGerm.isGoodPositionGerm` — Polyfold/Chapter5/Transversality.lean, line 409
- `Polyfold.StrongBundle.IsGeneralPositionGerm.isGoodPositionGermTame` — Polyfold/Chapter5/Transversality.lean, line 435

*What differs.*
- The text omits the interior condition of Definition 3.21; the count $\dim T_zO/T^R_zO = d_C(z)$ (Proposition 2.36) needs the chart tame (Findings, Chapter 5, items 72, 76).

### V5.47. Definition 5.28: sc-smooth partitions of unity

*restated* · index type in the universe of $X$

**HWZ (§5.4.2, Definition 5.28, p. 192).** $X$ admits sc-smooth partitions of unity if for every open covering there is a subordinate sc-smooth partition of unity.

**Proved in Lean.** `AdmitsScPartitionsOfUnity`: for every open cover $(U_i)_{i \in \iota}$ ($\iota$ in the universe of $X$) a Mathlib `PartitionOfUnity` with $\operatorname{supp}\rho_i \subseteq U_i$ and every $\rho_i$ sc-smooth.

- `Polyfold.MPolyfold.IsScSmoothPartitionOfUnity` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 358
- `Polyfold.MPolyfold.AdmitsScPartitionsOfUnity` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 365

*What differs.*
- Every cover can be indexed by subsets of $X$, so nothing is lost (Findings, Chapter 5, item 110).

### V5.48. Sc-smooth functions: algebra, local finiteness, extension by $0$

*not in the book* · used, not stated

**HWZ (§5.4.2, proof of Theorem 5.37, pp. 195–197).** "$\hat g = \sum\beta_xg(x)$", "$\gamma_\lambda = \hat g_\lambda/\sum\hat g$", and "extended by $0$" — used as sc-smooth.

**Proved in Lean.** Sums, differences, products, finite sums and products, locally finite sums of sc-smooth functions are sc-smooth; sc-smoothness is local; a function supported in a chart domain with sc-smooth representative is sc-smooth (`isScSmoothMap_real_of_chart`).

- `Polyfold.MPolyfold.IsScSmoothMap.real_add` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 201
- `Polyfold.MPolyfold.IsScSmoothMap.real_sub` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 221
- `Polyfold.MPolyfold.IsScSmoothMap.real_mul` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 211
- `Polyfold.isScSmoothMap_real_finsetSum` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 231
- `Polyfold.isScSmoothMap_real_finsetProd` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 247
- `Polyfold.isScSmoothMap_real_finsum` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 263
- `Polyfold.isScSmoothMap_real_of_eventuallyEq` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 187
- `Polyfold.isScSmoothMap_real_of_chart` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 272

*What differs.*
- Needed for Theorem 5.37 and not stated in the text (Findings, Chapter 5, item 112).

### V5.49. Partitions of unity give bump functions

*not in the book* · the easy direction

**HWZ (§5.4.2, p. 192).** "Currently it is an open problem whether the existence of sc-smooth partitions of unity on M-polyfolds $X$ is equivalent to the existence of sc-smooth bump functions."

**Proved in Lean.** `AdmitsScPartitionsOfUnity.admitsBumpFunctions`: sc-smooth partitions of unity give bump functions in the sense of V5.16.

- `Polyfold.MPolyfold.AdmitsScPartitionsOfUnity.admitsBumpFunctions` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 1116

*What differs.*
- The converse, open in the text, is not addressed (Findings, Chapter 5, item 119).

### V5.50. Definition 5.31: $C^k$-bump functions

*as in the book*

**HWZ (§5.4.2, Definition 5.31, p. 193).** A Banach space $E$ admits a $C^k$-bump function if some $C^k$ function $f : E \to \mathbb R$, not identically zero, has bounded support ($k \in \{0, 1, \dots\} \cup \{\infty\}$).

**Proved in Lean.** `HasContDiffBump V k`; `AdmitsContDiffPartitionsOfUnity V k`: every open cover has a subordinate $C^k$ partition of unity.

- `Polyfold.HasContDiffBump` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 779
- `Polyfold.AdmitsContDiffPartitionsOfUnity` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 772

*What differs.*
- As in the text (Findings, Chapter 5, item 114).

### V5.51. Definition 5.33: the sc-smooth bump function property

*restated* · $f \ne 0$ read as $f(x) \ne 0$

**HWZ (§5.4.2, Definition 5.33, p. 194).** $(O, C, E)$ has the property if for every $x \in O$ and open $U(x) \subseteq O$ with $\operatorname{cl}_E(U(x)) \subseteq O$ there is an sc-smooth $f : O \to \mathbb R$ with $f \ne 0$ and $\operatorname{supp}(f) \subseteq U(x)$.

**Proved in Lean.** `LocalModel.HasBumpProperty`: for $x \in O$ and open $W \ni x$ with $\operatorname{cl}(O \cap W) \subseteq O$, an sc-smooth $f$ on $O$ with $f(x) \ne 0$ and support in $O$ inside $W$. `closure_inter_ball_subset`: a retract is closed near its points.

- `Polyfold.LocalModel.HasBumpProperty` — Polyfold/Chapter5/BumpFunctions.lean, line 316
- `Polyfold.closure_inter_ball_subset` — Polyfold/Chapter5/BumpFunctions.lean, line 325

*What differs.*
- Read as Definition 5.9 (V5.16), so that Theorem 5.34 compares the same notions (Findings, Chapter 5, items 41, 43).

### V5.52. Theorem 5.34

*hypotheses explicit* · support repaired

**HWZ (§5.4.2, Theorem 5.34, p. 194).** "Clearly": $X$ admits sc-smooth bump functions iff it admits an sc-smooth atlas whose local models have the sc-smooth bump function property.

**Proved in Lean.** `theorem_5_34`: bump functions on $X$ iff some family of charts of $X$ covering $X$ has local models with the bump property.

- `Polyfold.theorem_5_34` — Polyfold/Chapter5/BumpFunctions.lean, line 367

*What differs.*
- The extension by $0$ of a local bump need not be continuous ($\varphi(u) = u/(1 - |u|_0^2)$ on the unit ball); the bump is taken in a small ball with closure inside the chart domain (Findings, Chapter 5, item 43).

### V5.53. Proposition 5.35; M-polyfolds on sc-Hilbert spaces

*restated* · Hilbert = norm of a bilinear form

**HWZ (§5.4.2, Proposition 5.35, p. 194; §5.3, p. 173).** If $E_0$ is a Hilbert space, $(O, C, E)$ has the sc-bump function property ($\beta(\|x\|^2)$, scaling, translating, composing with the retraction). "This is, for example, the case if $X$ is built on sc-Hilbert spaces."

**Proved in Lean.** `proposition_5_35`: $\|v\|^2 = b(v, v)$ for a continuous bilinear $b$; `hasBumpProperty_of_quadratic`: $\kappa\|v\|^2 \le b(v, v)$ suffices; `admitsBumpFunctions_of_hilbert` for M-polyfolds covered by such charts.

- `Polyfold.LocalModel.hasBumpProperty_of_quadratic` — Polyfold/Chapter5/BumpFunctions.lean, line 460
- `Polyfold.proposition_5_35` — Polyfold/Chapter5/BumpFunctions.lean, line 502
- `Polyfold.MPolyfold.admitsBumpFunctions_of_hilbert` — Polyfold/Chapter5/BumpFunctions.lean, line 510

*What differs.*
- An inner product structure on $E_0$ would be a second normed structure; translation by a non-smooth point is legitimate because the bump is $C^\infty$ on $E_0$ (Findings, Chapter 5, item 44).

### V5.54. Definition 5.36: the sc-smooth approximation property

*restated* · $V = O \cap W$

**HWZ (§5.4.2, Definition 5.36, p. 195).** For $V \subseteq O$ open with $\operatorname{cl}_C(V) \subseteq O$, continuous $f : O \to [0, 1]$ supported in $V$ and $\varepsilon > 0$ there is an sc-smooth $g : O \to [0, 1]$ supported in $V$ with $|f - g| \le \varepsilon$.

**Proved in Lean.** `LocalModel.HasApproxProperty`: the same with $V = O \cap W$, $W$ open in $E_0$, closures in $E_0$, supports taken in $O$.

- `Polyfold.LocalModel.HasApproxProperty` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 376

*What differs.*
- $C$ is closed, so $\operatorname{cl}_C = \operatorname{cl}_{E_0}$ on subsets of $C$ (Findings, Chapter 5, item 110).

### V5.55. Theorem 5.37 "(i) ⇒ (ii)"

*narrower* · restricted charts · every chart: open

**HWZ (§5.4.2, proof of Theorem 5.37, pp. 195–196).** For an atlas of charts $\varphi : U \to O$, "the sc-smooth function $f \circ \varphi$" extended by $0$ is supported in $W = \varphi^{-1}(V)$ "satisfying $\operatorname{cl}_X(W) \subseteq U$", and is approximated by $\sum\beta_xg(x)$.

**Proved in Lean.** `hasApproxProperty_restrict`: with sc-smooth partitions of unity, every chart restricted to an open $s$ with $\operatorname{cl}_X(s) \subseteq \operatorname{dom}\varphi$ has the approximation property. `MChart.isClosed_inter_preimage`: $\varphi^{-1}(A)$ closed for closed $A \subseteq \varphi(s)$.

- `Polyfold.hasApproxProperty_restrict` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 626
- `Polyfold.MChart.isClosed_inter_preimage` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 393

*What differs.*
- $\operatorname{cl}_X(W) \subseteq U$ does not follow from $\operatorname{cl}_C(V) \subseteq O$, and $f \circ \varphi$ is only continuous; whether every chart has the property is not settled (Findings, Chapter 5, item 111).

### V5.56. Theorem 5.37 "(ii) ⇒ (i)"

*restated* · through Urysohn functions · no metrizability

**HWZ (§5.4.2, proof of Theorem 5.37, pp. 196–197).** A refinement $(W_\lambda)$ "with the same index set" and $\operatorname{cl}_X(W_\lambda) \subseteq U_{\tau(\lambda)}$, $f_\lambda = 1$ on $Q_\lambda$, $g_\lambda$ with $|f_\lambda \circ \varphi^{-1} - g_\lambda| < 1/2$, $\gamma_\lambda = \hat g_\lambda/\sum\hat g$.

**Proved in Lean.** `exists_isScSmoothMap_urysohn`: a covering family of charts with the approximation property gives sc-smooth Urysohn functions $F = \tau(4\sum\hat g_x - 1)$; `admitsScPartitionsOfUnity_of_approx`: then sc-smooth partitions of unity (Mathlib bump coverings).

- `Polyfold.MChart.exists_small_nhds` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 412
- `Polyfold.LocalModel.HasApproxProperty.exists_approx` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 442
- `Polyfold.exists_isScSmoothMap_urysohn` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 513
- `Polyfold.admitsScPartitionsOfUnity_of_approx` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 597

*What differs.*
- The refinement with the same index set does not exist in general (the cover $\{X\}$); $\operatorname{cl}_C(\varphi(W_\lambda)) \subseteq O$ is not arranged in the text (Findings, Chapter 5, item 112).

### V5.57. Theorem 5.37

*restated* · "atlas" = covering family

**HWZ (§5.4.2, Theorem 5.37, p. 195).** (i) $X$ admits sc-smooth partitions of unity subordinate to any open cover iff (ii) $X$ admits an atlas consisting of local models having the sc-smooth approximation property.

**Proved in Lean.** `theorem_5_37`: (i) iff some family of charts of $X$ covering $X$ has local models with the approximation property.

- `Polyfold.theorem_5_37` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 742

*What differs.*
- For "(i) ⇒ (ii)" the family is that of the restricted charts (V5.55) (Findings, Chapter 5, items 111, 112).

### V5.58. Proposition 5.38

*hypotheses explicit* · $C^\infty$ partitions of unity of $E_0$ · not via Theorem 5.37

**HWZ (§5.4.2, Proposition 5.38, p. 197).** "An immediate consequence of Theorem 5.37": if the sc-Banach space admits smooth partitions of unity, a local model $(O, C, E)$ has the sc-smooth approximation property.

**Proved in Lean.** `proposition_5_38`: if $E_0$ admits $C^\infty$ partitions of unity, $(O, C, E)$ has the approximation property.

- `Polyfold.proposition_5_38` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 793

*What differs.*
- Theorem 5.37 gives some atlas, not the given model; the argument of "(i) ⇒ (ii)" is repeated in $E_0$ (Findings, Chapter 5, item 113).

### V5.59. Definition 5.39; Theorem 5.40 as a statement

*restated* · max = sup · Theorem 5.40 not proved

**HWZ (§5.4.2, Definition 5.39, Theorem 5.40, p. 198).** $c_0(\Gamma)$: $f : \Gamma \to \mathbb R$ with $\{\gamma \mid |f(\gamma)| > \varepsilon\}$ finite for every $\varepsilon$, norm $\max_\gamma|f(\gamma)|$; coordinate-wise $C^k$ homeomorphic embeddings. Theorem 5.40 (Toruńczyk): $C^k$ partitions of unity iff such an embedding into some $c_0(\Gamma)$.

**Proved in Lean.** `cZero Γ` (a subspace of $\ell^\infty(\Gamma)$, `mem_cZero_iff`, `norm_cZero`); `IsCoordinatewiseContDiffEmbedding`; `TorunczykStatement` records Theorem 5.40, not proved, not used.

- `Polyfold.cZero` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 874
- `Polyfold.mem_cZero_iff` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 887
- `Polyfold.norm_cZero` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 900
- `Polyfold.IsCoordinatewiseContDiffEmbedding` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 908
- `Polyfold.TorunczykStatement` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 915

*What differs.*
- Theorem 5.40 is gap G.52 (Findings, Chapter 5, items 114, 117).

### V5.60. Definition 5.41: WCG spaces

*as in the book* · reflexive defined

**HWZ (§5.4.2, Definition 5.41, p. 198).** $E$ is weakly compactly generated if there is a weakly compact $K$ with $E = \operatorname{cl}_E(\operatorname{span}K)$.

**Proved in Lean.** `IsWCG`: a set compact in `WeakSpace` with dense span. `IsReflexive`: $V \to V''$ onto.

- `Polyfold.IsWCG` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 930
- `Polyfold.IsReflexive` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 934

*What differs.*
- "Reflexive", used in Proposition 5.42, is not defined in the text (Findings, Chapter 5, item 114).

### V5.61. Proposition 5.42

*as in the book* · Kakutani via Banach–Alaoglu

**HWZ (§5.4.2, Proposition 5.42, p. 198).** (i) A reflexive $E$ is WCG; (ii) a separable $E$ is WCG.

**Proved in Lean.** `proposition_5_42_reflexive`, `proposition_5_42_separable`.

- `Polyfold.proposition_5_42_reflexive` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 953
- `Polyfold.proposition_5_42_separable` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 980
- `Polyfold.span_closedBall_eq_top` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 938

*What differs.*
- In (ii) a dense sequence of $V$ scaled by $1/((n + 1)(|y_n| + 1))$ replaces "$\{0\} \cup \{x_n/n\}$" (index range missing in the text) (Findings, Chapter 5, item 115).

### V5.62. Theorem 5.43 as a statement; Hilbert spaces

*not in the book* · Theorem 5.43 not proved

**HWZ (§5.4.2, Theorem 5.43, p. 198; proof of Corollary 5.44, p. 199).** Theorem 5.43 ([12]): a WCG space with a $C^k$-bump function admits $C^k$ partitions of unity. "A Hilbert space is reflexive and hence a WCG-space."

**Proved in Lean.** `GodefroyTroyanskiWhitfieldZizlerStatement V k` records Theorem 5.43 (not proved). `hasContDiffBump_of_hilbert`: a $C^\infty$-bump $\tau(1 - b(v, v))$; `isReflexive_of_hilbert`: complete and $\|v\|^2 = b(v, v)$ ⇒ reflexive.

- `Polyfold.GodefroyTroyanskiWhitfieldZizlerStatement` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 1072
- `Polyfold.hasContDiffBump_of_hilbert` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 1020
- `Polyfold.isReflexive_of_hilbert` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 1040

*What differs.*
- Theorem 5.43 is gap G.53 (Findings, Chapter 5, items 116, 117).

### V5.63. Corollary 5.44

*narrower* · Theorem 5.43 a hypothesis

**HWZ (§5.4.2, Corollary 5.44, p. 199).** If $E_0$ is a Hilbert space, $(O, C, E)$ has the sc-smooth approximation property ("a Hilbert space is reflexive and hence a WCG-space ... from Theorem 5.43 ... in view of Theorem 5.37").

**Proved in Lean.** `corollary_5_44`: $\|v\|^2 = b(v, v)$ and Theorem 5.43 for $E_0$, $k = \infty$, as a hypothesis ⇒ the approximation property; `admitsScPartitionsOfUnity_of_hilbert` for M-polyfolds covered by such charts.

- `Polyfold.corollary_5_44` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 1083
- `Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 1101

*What differs.*
- "In view of Theorem 5.37" is Proposition 5.38; the bump Theorem 5.43 needs is the classical $C^\infty$ one (Findings, Chapter 5, item 116).

## Chapter 6

*HWZ Chapter 6 §§6.1–6.7, preprint pp. 200–237: linearizations, the determinant of Fredholm operators and its orientation, the determinant bundle, local propagation and orientations of sc-Fredholm sections, the orientation of the solution set, the product with [0, 1]; Theorem 6.43 is not formalized*

### V6.1. Definition 6.1: the space $\mathrm{Lin}(f, x)$ of linearizations

*restated* · made at a chart point · global sc⁺-sections · Fredholm on level $0$ only

**HWZ (§6.1, Definition 6.1, p. 201 (with pp. 200–201, 219)).** For an sc-Fredholm section $f$ and a smooth point $x$, $\mathrm{Lin}(f, x) = \{(f - s)'(x) + a \mid a : T_xX \to Y_x$ an sc⁺-operator$\}$, where $s$ is a local sc⁺-section with $s(x) = f(x)$, made in a strong bundle chart as $s(y) = R(y, f(x))$. Its members differ by sc⁺-operators and are sc-Fredholm of one index $\mathrm{ind}(f, x)$; §6.5 adds that $\mathrm{Lin}(f, x)$ is convex (p. 219).

**Proved in Lean.** At a chart point $p = (c, z)$ of $x$ (`ChartPoint`, with the spaces $T_zO$ and $K_z$ as `ChartPoint.T`, `ChartPoint.K`), `ChartPoint.linSet` is the set of operators $(f + s)'(x) + a : T_zO \to K_z$ for an sc⁺-section $s$ with $(f + s)(x) = 0$ and an sc⁺-operator $a$ (`ChartPoint.IsScPlusOp`); for one such $s$ it is $(f + s)'(x)$ plus the sc⁺-operators (`ChartPoint.mem_linSet_iff`). Two such sections give linearizations that differ by an sc⁺-operator; the members are Fredholm on level $0$, all of the index $\mathrm{ind}(f, x)$ of V3.98 (`ChartPoint.exists_index_linSet`, `ChartPoint.fredholmIndex_of_mem_linSet`); `linSet` is convex, and it is not empty when $P$ has sc⁺-sections through the smooth points of its fibres (`StrongBundle.HasScPlusSectionsThrough`), which bump functions give.

- `Polyfold.ChartPoint` — Polyfold/Chapter6/LinSet.lean, line 109
- `Polyfold.ChartPoint.T` — Polyfold/Chapter6/LinSet.lean, line 129
- `Polyfold.ChartPoint.K` — Polyfold/Chapter6/LinSet.lean, line 132
- `Polyfold.ChartPoint.IsScPlusOp` — Polyfold/Chapter6/LinSet.lean, line 143
- `Polyfold.ChartPoint.linSet` — Polyfold/Chapter6/LinSet.lean, line 153
- `Polyfold.ChartPoint.mem_linSet_iff` — Polyfold/Chapter6/LinSet.lean, line 309
- `Polyfold.ChartPoint.exists_isScPlusOp_linAt_eq` — Polyfold/Chapter6/LinSet.lean, line 260
- `Polyfold.ChartPoint.linSet_nonempty` — Polyfold/Chapter6/LinSet.lean, line 323
- `Polyfold.ChartPoint.isScPlusOp_sub_of_mem_linSet` — Polyfold/Chapter6/LinSet.lean, line 348
- `Polyfold.ChartPoint.isFredholm_isIndexAt_of_mem_linSet` — Polyfold/Chapter6/LinSet.lean, line 362
- `Polyfold.ChartPoint.exists_index_linSet` — Polyfold/Chapter6/LinSet.lean, line 388
- `Polyfold.ChartPoint.fredholmIndex_of_mem_linSet` — Polyfold/Chapter6/LinSet.lean, line 397
- `Polyfold.ChartPoint.convex_linSet` — Polyfold/Chapter6/LinSet.lean, line 404
- `Polyfold.MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough` — Polyfold/Chapter3/IndexLocallyConstantLocal.lean, line 82

*What differs.*
- $T_xX$ and $Y_x$ carry no linear structure in the project (gaps G.6, G.7, G.13), so $\mathrm{Lin}(f, x)$ is made at a chart point; chart points are compared in V6.53–V6.55. The text's $f - s$ with $s(x) = f(x)$ is $f + s$ with $(f + s)(x) = 0$ (Findings, Chapter 6, item 40).
- The text constructs a local section through $f(x)$ in a chart; the project uses global ones, which exist under the standing bump functions (the text assumes sc-smooth partitions of unity from §6.2 on, and these give bump functions, V5.49) (Findings, Chapter 6, items 40, 43).
- "Sc-Fredholm" is proved on level $0$, which is what the determinant lines use, and not on every level (gap G.64).
- The paragraph before the definition compares $(f - s)'(x)$ with itself where $(f - t)'(x)$ is meant (possible misprint) (Findings, Chapter 6, item 41).

### V6.2. The determinant lines $\lambda(E)$, $\lambda^*(E)$ and the maps $\lambda(\Phi)$

*as in the book* · two-block wedges for (91)

**HWZ (§6.2, pp. 203–204).** $\lambda(E) = \Lambda^{\max}E$ and $\lambda^*(E) = (\lambda(E))^*$. For $\Phi : E \to F$ between spaces of the same dimension, $\lambda(\Phi)(a_1 \wedge \dots \wedge a_n) = \Phi(a_1) \wedge \dots \wedge \Phi(a_n)$, nontrivial iff $\Phi$ is an isomorphism, with $\lambda(\Psi \circ \Phi) = \lambda(\Psi) \circ \lambda(\Phi)$; $\lambda^*(\Phi)$ is the dual of $\lambda(\Phi)$. The dual vector $v^*$ of $v \ne 0$ in a line is fixed by $v^*(v) = 1$ (p. 204).

**Proved in Lean.** `maxPow E`, the top exterior power of a finite-dimensional real space, is a line (`finrank_maxPow`), and `maxPowDual E` is its dual. A change of basis multiplies the `wedge` by the determinant (`wedge_eq_det_smul`), also in one block of a two-block wedge (`wedge_append_basis_left`, `wedge_append_basis_right`), and adding to one block vectors of the span of the other does not change the wedge (`wedge_append_add_left`, `wedge_append_add_right`). `dualVec v` is the functional with $v^*(v) = 1$. For $\dim E = \dim F$, `maxPowMap` is $\lambda(\Phi)$ on wedges (`maxPowMap_wedge`), with $\lambda(\Psi\Phi) = \lambda(\Psi)\lambda(\Phi)$ (`maxPowMap_comp`), nonzero iff $\Phi$ is bijective (`maxPowMap_ne_zero_iff`); `maxPowDualMap` is its dual.

- `Polyfold.maxPow` — Polyfold/Chapter6/DetLine.lean, line 72
- `Polyfold.maxPowDual` — Polyfold/Chapter6/DetLine.lean, line 76
- `Polyfold.finrank_maxPow` — Polyfold/Chapter6/DetLine.lean, line 79
- `Polyfold.wedge` — Polyfold/Chapter6/DetLine.lean, line 162
- `Polyfold.wedge_eq_det_smul` — Polyfold/Chapter6/DetLine.lean, line 205
- `Polyfold.wedge_append_basis_left` — Polyfold/Chapter6/DetLine.lean, line 461
- `Polyfold.wedge_append_basis_right` — Polyfold/Chapter6/DetLine.lean, line 472
- `Polyfold.wedge_append_add_left` — Polyfold/Chapter6/DetLine.lean, line 499
- `Polyfold.wedge_append_add_right` — Polyfold/Chapter6/DetLine.lean, line 483
- `Polyfold.dualVec` — Polyfold/Chapter6/DetLine.lean, line 102
- `Polyfold.dualVec_self` — Polyfold/Chapter6/DetLine.lean, line 110
- `Polyfold.eq_dualVec_of_apply_eq_one` — Polyfold/Chapter6/DetLine.lean, line 140
- `Polyfold.maxPowMap` — Polyfold/Chapter6/DetLine.lean, line 530
- `Polyfold.maxPowMap_wedge` — Polyfold/Chapter6/DetLine.lean, line 534
- `Polyfold.maxPowMap_comp` — Polyfold/Chapter6/DetLine.lean, line 544
- `Polyfold.maxPowMap_ne_zero_iff` — Polyfold/Chapter6/DetLine.lean, line 562
- `Polyfold.maxPowDualMap` — Polyfold/Chapter6/DetLine.lean, line 589

*What differs.*
- As in the text; the facts on two-block wedges are the tools of every later computation with (91).

### V6.3. Definition 6.3: the isomorphism $\iota : \lambda(E^*) \to \lambda^*(E)$

*as in the book* · $n = 0$: the zeroth power

**HWZ (§6.2, Definition 6.3, p. 204).** $\iota(e_1^* \wedge \dots \wedge e_n^*)(a_1 \wedge \dots \wedge a_n) = \det(e_i^*(a_j))$, $n = \dim E$, with $\lambda(\{0\}^*) = \mathbb R$ for $n = 0$. For a basis and its dual basis, $\iota(e_1^* \wedge \dots \wedge e_n^*) = (e_1 \wedge \dots \wedge e_n)^*$.

**Proved in Lean.** `iotaDual`: a nonzero linear map of lines $\lambda(E^*) \to \lambda^*(E)$ (`iotaDual_ne_zero`) with the value $\det(e_i^*(a_j))$ on wedges (`iotaDual_wedge_wedge`), and $\iota(e_1^* \wedge \dots \wedge e_n^*) = (e_1 \wedge \dots \wedge e_n)^*$ for a basis and its dual basis (`iotaDual_wedge_dualBasis`).

- `Polyfold.iotaDual` — Polyfold/Chapter6/DetLine.lean, line 601
- `Polyfold.iotaDual_wedge_wedge` — Polyfold/Chapter6/DetLine.lean, line 606
- `Polyfold.iotaDual_wedge_dualBasis` — Polyfold/Chapter6/DetLine.lean, line 617
- `Polyfold.iotaDual_ne_zero` — Polyfold/Chapter6/DetLine.lean, line 629

*What differs.*
- As in the text; the convention $\lambda(\{0\}^*) = \mathbb R$ is the zeroth exterior power, and the text's matrix $(e_i^*(a_j))$ is the transpose of Mathlib's, with the same determinant.

### V6.4. Proposition 6.4

*as in the book*

**HWZ (§6.2, Proposition 6.4, p. 205).** For an isomorphism $\Phi : E \to F$ of finite-dimensional spaces, the square with $\lambda(\Phi^*) : \lambda(F^*) \to \lambda(E^*)$, $\lambda^*(\Phi) : \lambda^*(F) \to \lambda^*(E)$ and the two maps $\iota$ commutes: $\lambda^*(\Phi) \circ \iota = \iota \circ \lambda(\Phi^*)$.

**Proved in Lean.** `proposition_6_4`: $\lambda^*(\Phi) \circ \iota = \iota \circ \lambda(\Phi^*)$.

- `Polyfold.proposition_6_4` — Polyfold/Chapter6/DetLine.lean, line 691

*What differs.*
- As in the text.

### V6.5. Four-term exact sequences and the isomorphism $\Phi_E$ of (91)

*as in the book* · defined from one choice

**HWZ (§6.2, p. 206, formula (91)).** For an exact sequence $0 \to A \xrightarrow{\alpha} B \xrightarrow{\beta} C \xrightarrow{\gamma} D \to 0$ of finite-dimensional spaces, choose $B = \alpha(A) \oplus Z$, $C = \beta(B) \oplus V$, bases $a$ of $A$, $d$ of $D$, $b'$ of $Z$, $c_i \in V$ with $\gamma(c_i) = d_i$ and $c'_i = \beta(b'_i)$. Then $\Phi_E((a_1 \wedge \dots \wedge a_n) \otimes (d_1 \wedge \dots \wedge d_l)^*) = (\alpha(a_1) \wedge \dots \wedge \alpha(a_n) \wedge b'_1 \wedge \dots \wedge b'_{m-n}) \otimes (c_1 \wedge \dots \wedge c_l \wedge c'_1 \wedge \dots \wedge c'_{m-n})^*$, with the two conventions on the order of the vectors.

**Proved in Lean.** `FourTermExact`: the exact sequence. A `FourTermExact.Choice` is the data of (91) (the complements $Z$ of $\alpha(A)$ and $V$ of $\beta(B)$, bases of $A$, $D$, $Z$, and the $\gamma$-preimages in $V$ of the basis of $D$), and `Choice.value` is the right-hand side of (91). `FourTermExact.phi`: the linear map $\lambda(A) \otimes \lambda^*(D) \to \lambda(B) \otimes \lambda^*(C)$ given by (91) for one choice (`canonicalChoice`), nonzero (`phi_ne_zero`), an isomorphism of lines (`phiEquiv`).

- `Polyfold.FourTermExact` — Polyfold/Chapter6/ExactSequence.lean, line 101
- `Polyfold.FourTermExact.Choice` — Polyfold/Chapter6/ExactSequence.lean, line 160
- `Polyfold.FourTermExact.Choice.value` — Polyfold/Chapter6/ExactSequence.lean, line 223
- `Polyfold.FourTermExact.canonicalChoice` — Polyfold/Chapter6/ExactSequence.lean, line 367
- `Polyfold.FourTermExact.phi` — Polyfold/Chapter6/ExactSequence.lean, line 405
- `Polyfold.FourTermExact.phi_ne_zero` — Polyfold/Chapter6/ExactSequence.lean, line 420
- `Polyfold.FourTermExact.phiEquiv` — Polyfold/Chapter6/ExactSequence.lean, line 445

*What differs.*
- As in the text; that the definition does not depend on the choice is Lemma 6.5 (V6.6).

### V6.6. Lemma 6.5: $\Phi_E$ does not depend on the choices

*restated* · (91) holds for every choice

**HWZ (§6.2, Lemma 6.5, p. 206 (proof §6.7.1, pp. 234–235)).** With the two ordering conventions, the definition of $\Phi_E$ does not depend on the choices.

**Proved in Lean.** `FourTermExact.lemma_6_5`: $\Phi_E$, defined from one choice, maps $(a_1 \wedge \dots \wedge a_n) \otimes (d_1 \wedge \dots \wedge d_l)^*$ to the right-hand side of (91) computed with any other choice, for all bases $a$ of $A$ and $d$ of $D$.

- `Polyfold.FourTermExact.lemma_6_5` — Polyfold/Chapter6/ExactSequence.lean, line 413

*What differs.*
- "Does not depend on the choices" is read as (91) holding for every choice, the strongest form and the one every later computation of $\gamma^P_T$ uses, each with its own choices. The proof follows §6.7.1 (V6.63) (Findings, Chapter 6, item 1).

### V6.7. Proposition 6.6: the isomorphism $\Psi_E$

*restated* · the wedge in $C$ in the order of (91)

**HWZ (§6.2, (92) and Proposition 6.6, p. 207).** $\Psi_E : \lambda(C) \otimes \lambda(A) \otimes \lambda^*(D) \to \lambda(B)$ is $c \otimes h \mapsto \bar\iota(c \otimes \Phi_E(h))$, with $\bar\iota(v \otimes b \otimes v^*) = b$. With the bases of (91) and $c = c'_1 \wedge \dots \wedge c'_l \wedge c_1 \wedge \dots \wedge c_{m-n}$, $\Psi_E(c \otimes a \otimes d^*) = b_1 \wedge \dots \wedge b_n \wedge b'_1 \wedge \dots \wedge b'_{m-n}$.

**Proved in Lean.** `contractDual`: $\bar\iota(v \otimes b \otimes \varphi) = \varphi(v)\,b$; `FourTermExact.psi`: $\Psi_E(c \otimes h) = \bar\iota(c \otimes \Phi_E(h))$. `FourTermExact.proposition_6_6`: $\Psi_E$ maps the wedge of the basis of $C$ of (91), the $\gamma$-preimages first, tensored with $(a_1 \wedge \dots \wedge a_n) \otimes (d_1 \wedge \dots \wedge d_l)^*$, to $\alpha(a_1) \wedge \dots \wedge \alpha(a_n) \wedge b'_1 \wedge \dots \wedge b'_{m-n}$.

- `Polyfold.contractDual` — Polyfold/Chapter6/ExactSequence.lean, line 567
- `Polyfold.FourTermExact.psi` — Polyfold/Chapter6/ExactSequence.lean, line 585
- `Polyfold.FourTermExact.proposition_6_6` — Polyfold/Chapter6/ExactSequence.lean, line 591

*What differs.*
- The statement writes the basis of $C$ with the names of its two blocks exchanged with respect to (91) (possible misprint); the order meant is (91)'s, the $\gamma$-preimages first, and the formal statement uses it (Findings, Chapter 6, item 2).

### V6.8. Definition 6.7: the determinant $\det(T)$

*as in the book* · alternative definition: gap G.57

**HWZ (§6.3, Definition 6.7, p. 208).** For a bounded Fredholm operator $T : E \to F$ between real Banach spaces, $\det(T) = \lambda(\ker T) \otimes \lambda^*(\operatorname{coker} T)$, a line. Some authors use $\lambda(\ker T) \otimes \lambda(\operatorname{coker}(T)^*)$; the two are naturally isomorphic given a convention identifying $\lambda^*(A)$ and $\lambda(A^*)$.

**Proved in Lean.** `linDet`, `fredholmDet`: $\det(T) = \lambda(\ker T) \otimes \lambda^*(F/R(T))$, a line for $T$ Fredholm (`finrank_fredholmDet`); equal operators have identified determinants (`linDetEquivOfEq`).

- `Polyfold.linDet` — Polyfold/Chapter6/FredholmDet.lean, line 50
- `Polyfold.fredholmDet` — Polyfold/Chapter6/FredholmDet.lean, line 133
- `Polyfold.finrank_fredholmDet` — Polyfold/Chapter6/FredholmDet.lean, line 136
- `Polyfold.linDetEquivOfEq` — Polyfold/Chapter6/FredholmDet.lean, line 60

*What differs.*
- As in the text; the alternative definition and its identification with Definition 6.7 are not formalized and not used (gap G.57; Findings, Chapter 6, item 10).

### V6.9. Definition 6.8: orientations of a Fredholm operator

*as in the book* · orientation = ray

**HWZ (§6.3, Definition 6.8, p. 208).** An orientation of a Fredholm operator $T : E \to F$ is an orientation of the line $\det(T)$.

**Proved in Lean.** `FredholmOrientation T`: a ray of $\det(T)$ (Mathlib's `Module.Ray`); a Fredholm operator has one (`nonempty_fredholmOrientation`), and exactly two (`exists_two_fredholmOrientation`).

- `Polyfold.FredholmOrientation` — Polyfold/Chapter6/FredholmDet.lean, line 144
- `Polyfold.nonempty_fredholmOrientation` — Polyfold/Chapter6/FredholmDet.lean, line 147
- `Polyfold.exists_two_fredholmOrientation` — Polyfold/Chapter6/FredholmDet.lean, line 154

*What differs.*
- As in the text.

### V6.10. Definition 6.9: good left-projections and their order

*as in the book* · $\Pi_T \ne \emptyset$ proved

**HWZ (§6.3, Definition 6.9 and the paragraphs after it, p. 208).** A good left-projection for a Fredholm $T : E \to F$ is a bounded projection $P : F \to F$ with (1) $\dim F/R(P) < \infty$ and (2) $R(P \circ T) = R(P)$; $\Pi_T$ is their set. Then $P$ is Fredholm of index $0$, $PT$ is Fredholm with $\mathrm{ind}(PT) = \mathrm{ind}(T)$, $P \le Q$ iff $P = PQ = QP$ is a partial order on $\Pi_T$, and $R(P) \cap R(P')$ has finite codimension.

**Proved in Lean.** `IsGoodLeftProj T P`, `goodLeftProjs T`; `ProjLE` is reflexive, antisymmetric and transitive (`ProjLE.refl`, `ProjLE.antisymm`, `ProjLE.trans`). A good left-projection is Fredholm of index $0$ (`IsGoodLeftProj.isFredholm`, `IsGoodLeftProj.fredholmIndex_eq_zero`), $PT$ is Fredholm with $\mathrm{ind}(PT) = \mathrm{ind}(T)$ (`IsGoodLeftProj.isFredholm_comp`, `IsGoodLeftProj.fredholmIndex_comp`), $F/(R(P) \cap R(P'))$ is finite-dimensional (`IsGoodLeftProj.finiteDimensional_quotient_inf`), and $\Pi_T$ is not empty for $T$ Fredholm (`exists_isGoodLeftProj`).

- `Polyfold.IsGoodLeftProj` — Polyfold/Chapter6/GoodProjections.lean, line 67
- `Polyfold.goodLeftProjs` — Polyfold/Chapter6/GoodProjections.lean, line 77
- `Polyfold.ProjLE` — Polyfold/Chapter6/GoodProjections.lean, line 80
- `Polyfold.ProjLE.refl` — Polyfold/Chapter6/GoodProjections.lean, line 84
- `Polyfold.ProjLE.antisymm` — Polyfold/Chapter6/GoodProjections.lean, line 88
- `Polyfold.ProjLE.trans` — Polyfold/Chapter6/GoodProjections.lean, line 93
- `Polyfold.IsGoodLeftProj.isFredholm` — Polyfold/Chapter6/GoodProjections.lean, line 137
- `Polyfold.IsGoodLeftProj.fredholmIndex_eq_zero` — Polyfold/Chapter6/GoodProjections.lean, line 142
- `Polyfold.IsGoodLeftProj.isFredholm_comp` — Polyfold/Chapter6/GoodProjections.lean, line 150
- `Polyfold.IsGoodLeftProj.fredholmIndex_comp` — Polyfold/Chapter6/GoodProjections.lean, line 158
- `Polyfold.IsGoodLeftProj.finiteDimensional_quotient_inf` — Polyfold/Chapter6/GoodProjections.lean, line 167
- `Polyfold.exists_isGoodLeftProj` — Polyfold/Chapter6/GoodProjections.lean, line 177

*What differs.*
- As in the text. That $\Pi_T \ne \emptyset$, used from Lemma 6.11 on, is not stated there; for $T$ Fredholm the projection onto $R(T)$ along a finite-dimensional complement is good (Findings, Chapter 6, item 3).

### V6.11. Lemma 6.10: a common lower bound in $\Pi_T$

*stronger* · $T$ need not be Fredholm · another construction

**HWZ (§6.3, Lemma 6.10, p. 208 (proof pp. 208–209)).** For $P, P' \in \Pi_T$ there is $P'' \in \Pi_T$ with $P'' \le P$ and $P'' \le P'$. The proof takes topological complements $X$, $X'$ of $R(P) \cap R(P')$ in $R(P)$, $R(P')$, a topological complement $Z$ of $X \oplus X' \oplus (R(P) \cap R(P'))$ in $F$, and $P''$ the projection onto $R(P) \cap R(P')$ along $Z \oplus X \oplus X'$.

**Proved in Lean.** `lemma_6_10`: for any bounded $T$, not necessarily Fredholm, and $P, P' \in \Pi_T$, some $P'' \in \Pi_T$ with $P'' \le P$ and $P'' \le P'$. `lemma_6_10_text_reading`: on $\mathbb R^2$ with $T = 1$ there are $P, P' \in \Pi_T$ such that no projection with range $R(P) \cap R(P')$ lies below both.

- `Polyfold.lemma_6_10` — Polyfold/Chapter6/GoodProjections.lean, line 225
- `Polyfold.lemma_6_10_text_reading` — Polyfold/Chapter6/GoodProjections.lean, line 259

*What differs.*
- As we read it, $P'' = P''P$ does not hold for the text's $P''$ in general, since it needs $\ker P \subseteq \ker P''$: for $P$ the projection of $\mathbb R^2$ onto the $x$-axis along the $y$-axis and $P'$ the one along the diagonal, a projection onto $R(P) \cap R(P')$ below both would equal both. The formalized $P''$ projects onto $R(P) \cap R(P') \cap N$, for a closed finite-codimensional $N$ meeting $\ker P + \ker P'$ only in $0$ (Hahn–Banach), along a closed complement containing $\ker P + \ker P'$ (Findings, Chapter 6, item 4).
- The 2017 version drops the lemma and remarks that such a lower bound need not exist; with the order $P \le Q$ iff $P = PQ = QP$ it always exists, as we read it, so the preprint's route to Lemma 6.25 is the one formalized (Findings, Chapter 6, item 4).

### V6.12. Lemma 6.11: the exact sequence $E(T, P)$

*as in the book*

**HWZ (§6.3, Lemma 6.11, p. 209).** For $P \in \Pi_T$ the sequence $0 \to \ker T \to \ker(PT) \to F/R(P) \to \operatorname{coker} T \to 0$, with the inclusion $j^P_T$, $\Phi^P_T(x) = Tx + R(P)$ and $\pi^P_T(f + R(P)) = (I - P)f + R(T)$, is exact.

**Proved in Lean.** `projSeqJ`, `projSeqPhi`, `projSeqPi`: the three maps; `lemma_6_11`: the sequence is exact, and `projSeq` is it as a four-term exact sequence.

- `Polyfold.projSeqJ` — Polyfold/Chapter6/ProjectionSequence.lean, line 70
- `Polyfold.projSeqPhi` — Polyfold/Chapter6/ProjectionSequence.lean, line 75
- `Polyfold.projSeqPi` — Polyfold/Chapter6/ProjectionSequence.lean, line 84
- `Polyfold.lemma_6_11` — Polyfold/Chapter6/ProjectionSequence.lean, line 99
- `Polyfold.projSeq` — Polyfold/Chapter6/ProjectionSequence.lean, line 165

*What differs.*
- As in the text.

### V6.13. The isomorphism $\gamma^P_T : \det(T) \to \det(PT)$

*as in the book* · $F/R(P) = F/R(PT)$ made explicit

**HWZ (§6.3, p. 210).** From $E(T, P)$, "recalling $R(P) = R(PT)$", $\Phi_{E(T,P)}$ is an isomorphism $\det(T) \to \det(PT)$, renamed $\gamma^P_T$.

**Proved in Lean.** `gammaProj`: $\Phi_{E(T,P)}$ followed by the identification of $\lambda^*(F/R(P))$ with $\lambda^*(F/R(PT))$ by the identity of $F$; on wedges it is given by (91), for any choice (`gammaProj_tmul`, `gammaProj_wedge_tmul`).

- `Polyfold.gammaProj` — Polyfold/Chapter6/ProjectionSequence.lean, line 191
- `Polyfold.gammaProj_tmul` — Polyfold/Chapter6/ProjectionSequence.lean, line 204
- `Polyfold.gammaProj_wedge_tmul` — Polyfold/Chapter6/ProjectionSequence.lean, line 221

*What differs.*
- "Recalling $R(P) = R(PT)$" is read as this identification. In Proposition 6.12 and Corollary 6.13 the equal operators $P(QT)$ and $PT$ have kernels of different types, so the statements carry the identification $\det(P(QT)) = \det(PT)$ (`linDetEquivOfEq`), bookkeeping, not a change of content (Findings, Chapter 6, item 5).

### V6.14. Proposition 6.12: $\gamma^P_{QT} \circ \gamma^Q_T = \gamma^P_T$

*as in the book* · up to $\det(PQT) = \det(PT)$

**HWZ (§6.3, Proposition 6.12, p. 211 (proof §6.7.2, pp. 235–237)).** For a Fredholm $T$ and $Q, P \in \Pi_T$ with $P \le Q$, $QT$ is Fredholm, $P \in \Pi_{QT}$, and $\gamma^P_{QT} \circ \gamma^Q_T = \gamma^P_T$.

**Proved in Lean.** `proposition_6_12`: the same, up to the identification $\det(P(QT)) = \det(PT)$ of the equal operators $PQT = PT$ (`comp_comp_eq_of_projLE`); $P \in \Pi_{QT}$ is `IsGoodLeftProj.of_projLE`.

- `Polyfold.proposition_6_12` — Polyfold/Chapter6/ProjectionSequence.lean, line 321
- `Polyfold.IsGoodLeftProj.of_projLE` — Polyfold/Chapter6/ProjectionSequence.lean, line 258
- `Polyfold.comp_comp_eq_of_projLE` — Polyfold/Chapter6/ProjectionSequence.lean, line 253

*What differs.*
- As in the text; the proof is that of §6.7.2 (V6.64) (Findings, Chapter 6, items 5, 6).

### V6.15. Corollary 6.13

*as in the book*

**HWZ (§6.3, Corollary 6.13, p. 211).** For $P, R, S \in \Pi_T$ with $P \le R$ and $P \le S$, the map $h \mapsto (\gamma^P_{RT})^{-1} \circ \gamma^P_{ST}(h)$, $\det(ST) \to \det(RT)$, does not depend on $P$, and it equals $\gamma^R_T \circ (\gamma^S_T)^{-1}$.

**Proved in Lean.** `corollary_6_13`: $(\gamma^P_{RT})^{-1} \circ \gamma^P_{ST} = \gamma^R_T \circ (\gamma^S_T)^{-1}$ for every such $P$, so the left side does not depend on $P$.

- `Polyfold.corollary_6_13` — Polyfold/Chapter6/ProjectionSequence.lean, line 548

*What differs.*
- As in the text.

### V6.16. The stabilization $T_\varphi$ and Lemma 6.14

*as in the book* · stabilizations exist

**HWZ (§6.3, pp. 211–212, Lemma 6.14, p. 212).** For $T$ Fredholm and a linear $\varphi : \mathbb R^n \to F$ with $T_\varphi(e, r) = Te + \varphi(r)$ onto, the sequence $0 \to \ker T \to \ker T_\varphi \to \mathbb R^n \to F/R(T) \to 0$ with $j(e) = (e, 0)$, $\pi(e, r) = r$ and $[\varphi](r) = \varphi(r) + R(T)$ is exact.

**Proved in Lean.** `stabJ`, `stabPi`, `stabClass`: the maps; `lemma_6_14`: the sequence is exact, and `stabSeq` is it as a four-term exact sequence; `exists_surjective_coprod`: every Fredholm $T$ has a stabilizing $\varphi$.

- `Polyfold.stabJ` — Polyfold/Chapter6/Stabilization.lean, line 101
- `Polyfold.stabPi` — Polyfold/Chapter6/Stabilization.lean, line 108
- `Polyfold.stabClass` — Polyfold/Chapter6/Stabilization.lean, line 114
- `Polyfold.lemma_6_14` — Polyfold/Chapter6/Stabilization.lean, line 197
- `Polyfold.stabSeq` — Polyfold/Chapter6/Stabilization.lean, line 205
- `Polyfold.exists_surjective_coprod` — Polyfold/Chapter6/Stabilization.lean, line 220

*What differs.*
- As in the text; the proof writes $j(e) = (0, e)$ for $(e, 0)$ (possible misprint) (Findings, Chapter 6, item 8).

### V6.17. Formula (94): the isomorphism $\psi : \lambda^*(\mathbb R^n) \to \lambda^*(\{0\})$

*as in the book*

**HWZ (§6.3, formula (94), p. 212).** $\psi((e_1 \wedge \dots \wedge e_n)^*) = 1^*$ for the standard basis; then $\psi((c_1 \wedge \dots \wedge c_n)^*) = \det([c_1, \dots, c_n])^{-1}\,1^*$ for every basis $c$ of $\mathbb R^n$.

**Proved in Lean.** `stdWedge` (the wedge of the standard basis), `stabOne` ($1^* \in \lambda^*(\{0\})$) and `stabPsi`; `stabPsi_dualVec`: formula (94) for every basis.

- `Polyfold.stdWedge` — Polyfold/Chapter6/Stabilization.lean, line 260
- `Polyfold.stabOne` — Polyfold/Chapter6/Stabilization.lean, line 264
- `Polyfold.stabPsi` — Polyfold/Chapter6/Stabilization.lean, line 270
- `Polyfold.stabPsi_dualVec` — Polyfold/Chapter6/Stabilization.lean, line 295

*What differs.*
- As in the text.

### V6.18. Proposition 6.15: the isomorphism $\iota_\varphi : \det(T) \to \det(T_\varphi)$

*restated* · $m + l = n$ proved · (95): gap G.58

**HWZ (§6.3, Proposition 6.15, p. 213).** With (94), $\iota_\varphi$ is given as follows: for a basis $a$ of $\ker T$, $\bar d_i = \varphi(\bar c_i) + R(T)$ a basis of $F/R(T)$ and $\bar b_j = (b_j, r_j)$ completing $(a_i, 0)$ to a basis of $\ker T_\varphi$, the $r_j$ and $\bar c_i$ form a basis of $\mathbb R^n$, and $\iota_\varphi(h) = \det(\bar c_1, \dots, \bar c_m, r_1, \dots, r_l)^{-1}((a_1, 0) \wedge \dots \wedge (a_k, 0) \wedge \bar b_1 \wedge \dots \wedge \bar b_l) \otimes 1^*$.

**Proved in Lean.** `stabIota`: $\iota_\varphi = (1 \otimes \psi) \circ \Phi_E$, an isomorphism (`stabIota_bijective`). `proposition_6_15`: the formula, under the hypothesis $m + l = n$ needed to form $\det(\bar c, r)$, which always holds (`stab_card_eq`); the $r_j$ and $\bar c_i$ form a basis of $\mathbb R^n$ (`isCompl_range_stabPi_span`).

- `Polyfold.stabIota` — Polyfold/Chapter6/Stabilization.lean, line 338
- `Polyfold.stabIota_bijective` — Polyfold/Chapter6/Stabilization.lean, line 357
- `Polyfold.stab_card_eq` — Polyfold/Chapter6/Stabilization.lean, line 368
- `Polyfold.isCompl_range_stabPi_span` — Polyfold/Chapter6/Stabilization.lean, line 387
- `Polyfold.proposition_6_15` — Polyfold/Chapter6/Stabilization.lean, line 421

*What differs.*
- The two facts the text notices, $m + l = n$ and the basis of $\mathbb R^n$, are proved. The statement calls $\psi$ "$\varphi$", already the name of the stabilizing map (possible misprint) (Findings, Chapter 6, item 9).
- The identification (95) and the maps $V \otimes \lambda(\mathbb R^n) \to V$, $V \otimes \lambda^*(\mathbb R^n) \to V$ after the proposition are not formalized; the formal statements use (94) only (gap G.58; Findings, Chapter 6, item 10).

### V6.19. Definition 6.16: the direct sum convention

*as in the book* · "natural" = the formula for every choice

**HWZ (§6.3, Definition 6.16, p. 214).** For Fredholm $T : E \to F$ and $S : E' \to F'$, $T \oplus S$ is Fredholm, and the natural isomorphism $\det(T) \otimes \det(S) \to \det(T \oplus S)$ maps $h \otimes h'$, $h = a \otimes d^*$, $h' = a' \otimes d'^*$, to $(a_1 \wedge \dots \wedge a_n \wedge a'_1 \wedge \dots \wedge a'_{n'}) \otimes (d_1 \wedge \dots \wedge d_l \wedge d'_1 \wedge \dots \wedge d'_{l'})^*$.

**Proved in Lean.** $\ker(T \oplus S) \cong \ker T \times \ker S$ and $\operatorname{coker}(T \oplus S) \cong \operatorname{coker} T \times \operatorname{coker} S$ (`kerProdEquiv`, `cokerProdEquiv`, from `kerInl`, `kerInr`, `cokerInl`, `cokerInr`, with `finrank_ker_prodMap`, `finrank_coker_prodMap`), so $T \oplus S$ is Fredholm (`isFredholm_prodMap`). `directSumDet`, defined by the formula for one choice of bases (`directSumVec`), satisfies it for every choice (`directSumVec_eq_smul`, `definition_6_16`) and is an isomorphism (`directSumDet_bijective`).

- `Polyfold.kerInl` — Polyfold/Chapter6/DirectSumDet.lean, line 101
- `Polyfold.kerInr` — Polyfold/Chapter6/DirectSumDet.lean, line 107
- `Polyfold.cokerInl` — Polyfold/Chapter6/DirectSumDet.lean, line 113
- `Polyfold.cokerInr` — Polyfold/Chapter6/DirectSumDet.lean, line 120
- `Polyfold.kerProdEquiv` — Polyfold/Chapter6/DirectSumDet.lean, line 194
- `Polyfold.cokerProdEquiv` — Polyfold/Chapter6/DirectSumDet.lean, line 200
- `Polyfold.finrank_ker_prodMap` — Polyfold/Chapter6/DirectSumDet.lean, line 208
- `Polyfold.finrank_coker_prodMap` — Polyfold/Chapter6/DirectSumDet.lean, line 217
- `Polyfold.isFredholm_prodMap` — Polyfold/Chapter6/DirectSumDet.lean, line 228
- `Polyfold.directSumVec` — Polyfold/Chapter6/DirectSumDet.lean, line 258
- `Polyfold.directSumDet` — Polyfold/Chapter6/DirectSumDet.lean, line 274
- `Polyfold.directSumVec_eq_smul` — Polyfold/Chapter6/DirectSumDet.lean, line 293
- `Polyfold.definition_6_16` — Polyfold/Chapter6/DirectSumDet.lean, line 338
- `Polyfold.directSumDet_bijective` — Polyfold/Chapter6/DirectSumDet.lean, line 376

*What differs.*
- "Natural" is read as the formula for every choice of bases, as for Lemma 6.5 (Findings, Chapter 6, item 11).

### V6.20. Lemma 6.17

*stronger* · $T$ need not be Fredholm

**HWZ (§6.4, Lemma 6.17, p. 214).** For a Fredholm $T$, $P \in \Pi_T$ and a topological complement $Y$ of $\ker(PT)$ in $E$ there is $\varepsilon > 0$ such that for $\|S - T\| < \varepsilon$: (1) $P \in \Pi_S$; (2) $PS|_Y : Y \to R(P)$ is a topological isomorphism.

**Proved in Lean.** `lemma_6_17`: the same for any bounded $T$, with $Y$ a topological complement in the sense of Mathlib's `Submodule.IsTopCompl` (an algebraic complement with a continuous projection); `projRestrict P S Y` is $PS|_Y$, and `FredholmOp` is the space of Fredholm operators.

- `Polyfold.FredholmOp` — Polyfold/Chapter6/LocalDetBundle.lean, line 66
- `Polyfold.projRestrict` — Polyfold/Chapter6/LocalDetBundle.lean, line 69
- `Polyfold.lemma_6_17` — Polyfold/Chapter6/LocalDetBundle.lean, line 129

*What differs.*
- The hypothesis that $T$ is Fredholm is not used (Findings, Chapter 6, item 20).

### V6.21. Lemma 6.18: the kernels $\ker(PS)$ form a trivial bundle

*restated* · "trivial bundle" made concrete

**HWZ (§6.4, Lemma 6.18, p. 215).** With $y(k, S) = -(PS|_Y)^{-1}PSk$, continuous in $(k, S)$, the space $\bigcup_{\|S - T\| < \varepsilon}\{S\} \times \ker(PS)$ with its projection "has the structure of a trivial vector bundle": $(S, k) \mapsto (S, k + y(k, S))$ is a continuous bijection from $\{\|S - T\| < \varepsilon\} \times \ker(PT)$, with inverse $(S, k + y) \mapsto (S, k)$.

**Proved in Lean.** `LocalDetChart`: the data $(T, P, Y, \varepsilon)$ of Lemma 6.17 with its conclusions; `LocalDetChart.ySol` is $y(k, S)$. `LocalDetChart.lemma_6_18`: `kerMap`, $(S, k) \mapsto (S, k + y(k, S))$, is continuous and maps $\ker(PT)$ onto $\bigcup_S\{S\} \times \ker(PS)$, and it is inverted by the continuous projection `kerProj` onto $\ker(PT)$ along $Y$.

- `Polyfold.LocalDetChart` — Polyfold/Chapter6/LocalDetBundle.lean, line 180
- `Polyfold.LocalDetChart.ySol` — Polyfold/Chapter6/LocalDetBundle.lean, line 216
- `Polyfold.LocalDetChart.kerMap` — Polyfold/Chapter6/LocalDetBundle.lean, line 220
- `Polyfold.LocalDetChart.kerProj` — Polyfold/Chapter6/LocalDetBundle.lean, line 223
- `Polyfold.LocalDetChart.lemma_6_18` — Polyfold/Chapter6/LocalDetBundle.lean, line 317

*What differs.*
- "Is a trivial vector bundle" is stated as this trivialization and its continuous inverse (Findings, Chapter 6, item 21).

### V6.22. Lemma 6.19 in the case used, and Proposition 6.20: $\mathrm{DET}(T, P, \varepsilon)$

*narrower* · Lemma 6.19 for trivial bundles only · explicit frames

**HWZ (§6.4, Lemma 6.19 and Proposition 6.20, p. 216).** Lemma 6.19, a standard lemma: for finite-dimensional topological vector bundles $E$, $F$, the bundles $\lambda(E)$, $\lambda^*(F)$, $E \oplus F$ and $E \otimes F$ are topological vector bundles in a natural way. Proposition 6.20, deduced from it: $\mathrm{DET}(T, P, \varepsilon) = \bigcup_{\|S - T\| < \varepsilon}\{S\} \times \det(PS)$ has in a natural way the structure of a topological line bundle.

**Proved in Lean.** Over the ball of a local determinant chart, `LocalDetChart.frame` $\omega(S) = (k_1(S) \wedge \dots \wedge k_n(S)) \otimes (e_1 \wedge \dots \wedge e_l)^*$, with $k_i(S) = k_i + y(k_i, S)$ (`kerFrame`) and a constant basis $e$ of $F/R(P) = F/R(PS)$, is nowhere zero (`LocalDetChart.frame_ne_zero`). `proposition_6_20`: the frames of two charts with the same $P$ differ by a continuous nowhere-zero factor.

- `Polyfold.LocalDetChart.kerFrame` — Polyfold/Chapter6/LocalDetBundle.lean, line 366
- `Polyfold.LocalDetChart.frame` — Polyfold/Chapter6/LocalDetBundle.lean, line 379
- `Polyfold.LocalDetChart.frame_ne_zero` — Polyfold/Chapter6/LocalDetBundle.lean, line 428
- `Polyfold.proposition_6_20` — Polyfold/Chapter6/LocalDetBundle.lean, line 524

*What differs.*
- Lemma 6.19 is not formalized in general (Mathlib has no exterior powers or tensor products of vector bundles; gap G.59). The bundles it is applied to are trivial, and Proposition 6.20 is proved with the explicit frames; "in a natural way" is read as the relation between the frames of two charts (Findings, Chapter 6, item 22).

### V6.23. Lemma 6.21

*stronger* · two charts, any centres and radii

**HWZ (§6.4, Lemma 6.21, p. 216 (sketch pp. 216–217)).** For $Q \le P$ in $\Pi_T$, $(S, h) \mapsto (S, \gamma^Q_{PS}(h))$, $\mathrm{DET}(T, P, \varepsilon) \to \mathrm{DET}(T, Q, \varepsilon)$, is a topological line bundle isomorphism; "this is trivial", and the sketch extends continuous sections spanning $\ker(PS)$ to sections spanning $\ker(QS)$.

**Proved in Lean.** `LocalDetChart.gammaProj_frame_eq`, `lemma_6_21`: on the common ball of any two local determinant charts with projections $Q \le P$, $\gamma^Q_{PS}$ maps the $P$-frame at $S$ to a continuous nowhere-zero multiple of the $Q$-frame.

- `Polyfold.LocalDetChart.gammaProj_frame_eq` — Polyfold/Chapter6/LocalDetBundle.lean, line 760
- `Polyfold.lemma_6_21` — Polyfold/Chapter6/LocalDetBundle.lean, line 824

*What differs.*
- Stated for two charts with different centres and radii, the form Lemma 6.25 uses; the text's sketch, extending the kernel sections of $PS$ to sections spanning $\ker(QS)$, is the proof (Findings, Chapter 6, item 23).

### V6.24. $\mathrm{DET}(E, F)$ and the charts $\gamma_{(T,P,\varepsilon)}$

*restated* · a Mathlib vector prebundle · charts read in frames

**HWZ (§6.4, p. 217).** $\mathrm{DET}(E, F) = \bigcup_S\{S\} \times \det(S)$ over the Fredholm operators $S$. For a Fredholm $T$, Proposition 6.20 gives $\varepsilon > 0$ and $P \in \Pi_T$ with $\gamma_{(T,P,\varepsilon)} : (S, h) \mapsto (S, \gamma^P_S(h))$ a fibrewise linear bijection from $\mathrm{DET}(E, F)$ over the ball onto $\mathrm{DET}(T, P, \varepsilon)$.

**Proved in Lean.** `DetFiber`: the fibre $\det(S)$ over a Fredholm $S$. `LocalDetChart.pretriv`: the pretrivialization $(S, h) \mapsto (S, \omega(S)^*(\gamma^P_S h))$ with model fibre $\mathbb R$ (`LocalDetChart.coord`); every Fredholm operator is the centre of a chart (`exists_localDetChart`); `detPrebundle`: the Mathlib vector prebundle these charts form, whose topology and bundle structure are those of $\mathrm{DET}(E, F)$.

- `Polyfold.DetFiber` — Polyfold/Chapter6/DetBundle.lean, line 71
- `Polyfold.LocalDetChart.pretriv` — Polyfold/Chapter6/DetBundle.lean, line 141
- `Polyfold.LocalDetChart.coord` — Polyfold/Chapter6/DetBundle.lean, line 102
- `Polyfold.exists_localDetChart` — Polyfold/Chapter6/DetBundle.lean, line 182
- `Polyfold.detPrebundle` — Polyfold/Chapter6/DetBundle.lean, line 273

*What differs.*
- $\gamma_{(T,P,\varepsilon)}$ is read in the frame of Proposition 6.20 (Findings, Chapter 6, item 24).

### V6.25. Definition 6.22: the collection $\mathcal B$

*as in the book*

**HWZ (§6.4, Definition 6.22, p. 218).** $\mathcal B$ is the collection of the subsets $B$ of $\mathrm{DET}(E, F)$ for which some $\gamma_{(T,P,\varepsilon)}(B)$ is open in $\mathrm{DET}(T, P, \varepsilon)$.

**Proved in Lean.** `detBasis`: the sets lying over the ball of some chart whose image in ball $\times\,\mathbb R$ is open.

- `Polyfold.detBasis` — Polyfold/Chapter6/DetBundle.lean, line 309

*What differs.*
- As in the text, with the charts read in their frames (V6.24) (Findings, Chapter 6, item 24).

### V6.26. Proposition 6.23

*as in the book*

**HWZ (§6.4, Proposition 6.23, p. 218).** The collection $\mathcal B$ is a basis for a topology on $\mathrm{DET}(E, F)$.

**Proved in Lean.** `proposition_6_23`: $\mathcal B$ is a basis of the topology of the prebundle of V6.24, so the topology it generates is that one.

- `Polyfold.proposition_6_23` — Polyfold/Chapter6/DetBundle.lean, line 314

*What differs.*
- As in the text (Findings, Chapter 6, item 24).

### V6.27. Proposition 6.24

*as in the book*

**HWZ (§6.4, Proposition 6.24, p. 218).** $\mathrm{DET}(E, F)$, with its linear structure on the fibres and the topology of $\mathcal B$, is a topological line bundle, and the maps $\gamma_{(T,P,\varepsilon)}$ are topological bundle isomorphisms.

**Proved in Lean.** `proposition_6_24`: $\mathrm{DET}(E, F)$ is a topological vector bundle with model fibre $\mathbb R$ (Mathlib's `VectorBundle`), and every $\gamma_{(T,P,\varepsilon)}$, read in its frame, is a trivialization.

- `Polyfold.proposition_6_24` — Polyfold/Chapter6/DetBundle.lean, line 337

*What differs.*
- As in the text (Findings, Chapter 6, item 24).

### V6.28. Lemma 6.25: the transition maps

*as in the book*

**HWZ (§6.4, Lemma 6.25, p. 218).** $\gamma_{(T',P',\varepsilon')} \circ \gamma_{(T,P,\varepsilon)}^{-1}$ is a topological isomorphism of line bundles: for $Q \le P$, $Q \le P'$ it is $(S, h) \mapsto (S, (\gamma^Q_{P'S})^{-1} \circ \gamma^Q_{PS}(h))$ by Corollary 6.13, continuous by Lemma 6.21.

**Proved in Lean.** `lemma_6_25`: the transition between two charts is $(S, t) \mapsto (S, g(S)t)$ with $g$ continuous and nowhere zero on the common ball; `lemma_6_25_local`: the same near a base point $S_0$.

- `Polyfold.lemma_6_25` — Polyfold/Chapter6/DetBundle.lean, line 259
- `Polyfold.lemma_6_25_local` — Polyfold/Chapter6/DetBundle.lean, line 214

*What differs.*
- The proof is the text's: a common lower bound $Q \le P, P'$ (Lemma 6.10, V6.11), Corollary 6.13 and Lemma 6.21 (Findings, Chapter 6, items 4, 24).

### V6.29. Orientations of line bundles over simply connected bases

*not in the book* · the theorem contractibility needs · lifting criterion

**HWZ (§6.5, Proposition 6.26 and the opening of §6.5, p. 219).** Proposition 6.26: $\mathrm{DET}(f, x)$ has two possible orientations "since the base space is contractible". The opening of §6.5: over a contractible $U$ the determinant line bundle of a classical Fredholm section has precisely two orientations, the orientation of one line determining that of all the others.

**Proved in Lean.** `IsLineOrientation`, `LineOrientation`: a choice of rays of the fibres given near every point by a continuous nowhere-zero section. Two orientations that agree on one fibre agree over a preconnected base (`LineOrientation.eq_of_apply_eq`); the rays of the fibres form a two-sheeted covering (`OrCover`, `isCoveringMap_orCover`); over a simply connected, locally path-connected base every orientation of one fibre extends (`exists_lineOrientation_apply_eq`), and over a nonempty such base there are exactly two orientations (`exists_two_lineOrientation`).

- `Polyfold.IsLineOrientation` — Polyfold/Chapter6/LineBundleOrientation.lean, line 59
- `Polyfold.LineOrientation` — Polyfold/Chapter6/LineBundleOrientation.lean, line 66
- `Polyfold.LineOrientation.eq_of_apply_eq` — Polyfold/Chapter6/LineBundleOrientation.lean, line 171
- `Polyfold.OrCover` — Polyfold/Chapter6/LineBundleOrientation.lean, line 330
- `Polyfold.isCoveringMap_orCover` — Polyfold/Chapter6/LineBundleOrientation.lean, line 337
- `Polyfold.exists_lineOrientation_apply_eq` — Polyfold/Chapter6/LineBundleOrientation.lean, line 350
- `Polyfold.exists_two_lineOrientation` — Polyfold/Chapter6/LineBundleOrientation.lean, line 380

*What differs.*
- The text cites contractibility without the theorem it needs. The proof is the lifting criterion for the orientation double cover; nonempty convex sets of normed spaces are simply connected and locally path-connected (Findings, Chapter 6, item 25).

### V6.30. Proposition 6.26: $\mathrm{DET}$ over a convex set of Fredholm operators

*stronger* · any nonempty convex $C$

**HWZ (§6.5, Proposition 6.26, p. 219).** $\mathrm{DET}(f, x) = \bigcup_{L \in \mathrm{Lin}(f,x)}\{L\} \times \det(L)$ has in a natural way the structure of a topological line bundle over $\mathrm{Lin}(f, x)$, and two possible orientations, the base being convex, hence contractible.

**Proved in Lean.** `proposition_6_26`: for every nonempty convex set $C$ of Fredholm operators, the restriction `DetOn C` of $\mathrm{DET}(E, F)$ along the inclusion `fredholmIncl` is a topological line bundle with exactly two orientations.

- `Polyfold.fredholmIncl` — Polyfold/Chapter6/DetBundle.lean, line 345
- `Polyfold.DetOn` — Polyfold/Chapter6/DetBundle.lean, line 350
- `Polyfold.proposition_6_26` — Polyfold/Chapter6/DetBundle.lean, line 356

*What differs.*
- Stated for any nonempty convex $C$; $\mathrm{Lin}(f, x)$ is one (V6.1, V6.31) (Findings, Chapter 6, item 25).

### V6.31. Definition 6.27: $\mathrm{DET}(f, x)$, $\mathrm{Or}^f_x$ and the category $\mathcal O_f$

*restated* · made at a chart point · $\mathcal O_f$: types and bijections

**HWZ (§6.5, Definition 6.27, pp. 219–220).** An orientation of $(f, x)$, $x$ smooth, is a choice of one of the two orientations of $\mathrm{DET}(f, x)$. The objects of a category are the sets $\mathrm{Or}^f_x = \{o_x, -o_x\}$; for smooth $x$, $y$ in the same path component the morphisms are the two bijections $\pm o_x \mapsto \pm o_y$ and $\pm o_x \mapsto \mp o_y$.

**Proved in Lean.** At a chart point the members of $\mathrm{Lin}(f, x)$ are Fredholm (`ChartPoint.isFredholm_of_mem_linSet`); `ChartPoint.detLin` is the pull-back of $\mathrm{DET}(T_zO, K_z)$ to $\mathrm{Lin}(f, x)$ and `ChartPoint.Or` the type of its orientations, with exactly two elements (`ChartPoint.exists_two_or`); for $L \in \mathrm{Lin}(f, x)$, $o \mapsto o(L)$ is a bijection onto the two orientations of $\det(L)$ (`ChartPoint.orEquivRay`). Between two two-element types there are bijections, and one value determines a bijection (`nonempty_equiv_of_two`, `equiv_eq_of_apply_eq_of_two`).

- `Polyfold.ChartPoint.isFredholm_of_mem_linSet` — Polyfold/Chapter6/LinOrientation.lean, line 52
- `Polyfold.ChartPoint.detLin` — Polyfold/Chapter6/LinOrientation.lean, line 58
- `Polyfold.ChartPoint.Or` — Polyfold/Chapter6/LinOrientation.lean, line 63
- `Polyfold.ChartPoint.exists_two_or` — Polyfold/Chapter6/LinOrientation.lean, line 67
- `Polyfold.ChartPoint.orEquivRay` — Polyfold/Chapter6/LinOrientation.lean, line 75
- `Polyfold.nonempty_equiv_of_two` — Polyfold/Chapter6/OrientationFunctor.lean, line 134
- `Polyfold.equiv_eq_of_apply_eq_of_two` — Polyfold/Chapter6/OrientationFunctor.lean, line 153

*What differs.*
- Made at a chart point; V6.53–V6.55 compare chart points. On the tensor products no negation is set up, so $\{o_x, -o_x\}$ is stated as "exactly two elements"; the morphisms are bijections (Findings, Chapter 6, items 44, 70).

### V6.32. Proposition 6.28: the neighbourhoods $U(x)$

*narrower* · (1′) in place of (1): gap G.61 · global sections, bump functions · (3) for families $\mathbb R^n \to X$

**HWZ (§6.5, Proposition 6.28, p. 220 (proof pp. 220–221)).** For an sc-Fredholm section $f$, every smooth $x$ has an open $U$ with (1) $U$ sc-smoothly contractible; (2) $\{y \in \operatorname{cl}_X(U) \mid f(y) = 0\}$ compact; (3) for every sc-smooth path $\varphi : [0, 1] \to U$ an sc⁺-section $s : U \times [0, 1] \to Y$ with $s(\varphi(t), t) = f(\varphi(t))$; (4) for $t_0 \in [0, 1]$, $y_0 \in U_\infty$ and a smooth $e_0 \in Y_{y_0}$ an sc⁺-section $q$ with $q(y_0, t_0) = e_0$. The proof contracts $U = r(V')$, $V'$ convex, by $(t, y) \mapsto r(ty)$.

**Proved in Lean.** `proposition_6_28` (bump functions): open $U \subseteq W$ in the domain of one chart of the atlas with (1′) any two sc-smooth paths in $U$ with the same end points are sc-smoothly homotopic in $W$ with the end points fixed (`IsScHomotopyRel`); (2) $\{y \in \operatorname{cl}(U) \mid f(y) = 0\}$ compact (`exists_nhds_isCompact_zeros`); (3) for every sc-smooth family $\Phi : \mathbb R^n \to X$ with $\Phi([0, 1]^n) \subseteq W$ an sc⁺-section $S$ of $\pi^*P \to \mathbb R^n \times X$ with $(f + S)(q, \Phi(q)) = 0$ for $q$ near $[0, 1]^n$, depending on $q \in [0, 1]^n$ only through $\Phi(q)$ (`exists_isScPlusSection_pullback_of_family`); (4) $\pi^*P$ has sc⁺-sections through all smooth fibre points (`hasScPlusSectionsThrough_pullback_rn_of_bump`). $\mathbb R^n \times X$ and $\pi^*P$ are paracompact (`MPolyfold.paracompactSpace_prod`, `paracompactSpace_pullbackSpace`).

- `Polyfold.IsScHomotopyRel` — Polyfold/Chapter6/OrientableNbhd.lean, line 276
- `Polyfold.pt1` — Polyfold/Chapter6/OrientableNbhd.lean, line 267
- `Polyfold.pt2` — Polyfold/Chapter6/OrientableNbhd.lean, line 270
- `Polyfold.exists_contDiff_eq_id_near_Icc_mapsTo` — Polyfold/Chapter6/OrientableNbhd.lean, line 140
- `Polyfold.exists_isScSmoothMap_eq_one_nhdsSet` — Polyfold/Chapter6/OrientableNbhd.lean, line 179
- `Polyfold.exists_nhds_isCompact_zeros` — Polyfold/Chapter6/OrientableNbhd.lean, line 249
- `Polyfold.exists_isScPlusSection_pullback_of_mapsTo_of_bump` — Polyfold/Chapter6/OrientableNbhd.lean, line 297
- `Polyfold.exists_isScPlusSection_pullback_of_family` — Polyfold/Chapter6/OrientableNbhd.lean, line 479
- `Polyfold.hasScPlusSectionsThrough_pullback_rn_of_bump` — Polyfold/Chapter6/OrientableNbhd.lean, line 511
- `Polyfold.proposition_6_28` — Polyfold/Chapter6/OrientableNbhd.lean, line 529
- `Polyfold.MPolyfold.paracompactSpace_prod` — Polyfold/Chapter2/FibredProduct.lean, line 455
- `Polyfold.paracompactSpace_pullbackSpace` — Polyfold/Chapter2/StrongBundlePullback.lean, line 555

*What differs.*
- As we read it, (1) is not established for $U$ by the proof: $r(ty)$ contracts $r(V)$ for a convex $V$, but for $U = r(V')$ it needs $r(V') \subseteq V'$, which is not stated. What Theorem 6.35 uses is (1′), proved with $W = O \cap B_\delta$, $U = O \cap B_{\delta'}$, $r(B_{\delta'}) \subseteq B_\delta$ and the homotopy $\Phi(\tau, t) = r((1 - \rho(\tau))\varphi(\gamma_0(t)) + \rho(\tau)\varphi(\gamma_1(t)))$ in the chart (gap G.61; Findings, Chapter 6, item 45).
- The sections of (3) and (4) are global sc⁺-sections of the pull-back, made with bump functions, in place of sections over $U \times [0, 1]$ after "assuming $X = U$" (the text assumes partitions of unity from §6.2 on); (3) is stated for families, as the homotopies of Theorem 6.35 need it. Neither the smoothness of $x$ nor the tameness of $X$ is used (Findings, Chapter 6, items 43, 46).
- Paths and families are maps on $\mathbb R$, $\mathbb R^n$ of which only $[0, 1]$, $[0, 1]^n$ matters, and $U \times [0, 1]$ is read through $\mathbb R^n \times X$ (decision D2; gap G.65).

### V6.33. Lemma 6.29: the sections $s_1, \dots, s_k$

*narrower* · $X$ tame, tame germ data · general position of $F$, not (P) · the proof of Theorem 5.18

**HWZ (§6.5, the section $F$, p. 221; Lemma 6.29 and the paragraph after it, p. 222).** With $s(\varphi(t), t) = f(\varphi(t))$ and $F(t, y, \lambda) = f(y) - s(y, t) + \sum\lambda_is_i(y, t)$ on $[0, 1] \times X \times \mathbb R^k$, there are finitely many sc⁺-sections $s_1, \dots, s_k$ with (P): for every fixed $t$, $F_t$ is at $(\varphi(t), 0)$ in general position to the boundary of $X \times \mathbb R^k$. (P) implies that $F$ is in general position at all $(t, \varphi(t), 0)$. The choice is made "using the results from the transversality theory".

**Proved in Lean.** `lemma_6_29` ($X$ tame, bump functions, $f$ with tame germ data): for an sc-smooth $\Phi : \mathbb R^n \to X$ and an sc⁺-section $S$ of $\pi^*P$ with $(f + S)(q, \Phi(q)) = 0$ for $q$ near $[0, 1]^n$, finitely many sc⁺-sections $s_1, \dots, s_k$ of $\pi^*P$ such that $F(\lambda, (q, y)) = f(y) + S(q, y) + \sum\lambda_is_i(q, y)$ is in general position at $(0, (q, \Phi(q)))$ for all $q$ near $[0, 1]^n$ (`exists_sections_isGeneralPositionGerm_of_isCompact`; the points $(0, (q, \Phi(q)))$ are zeros of $F$, `isZeroAt_paramSection_zero`).

- `Polyfold.isZeroAt_paramSection_zero` — Polyfold/Chapter6/Lemma629.lean, line 81
- `Polyfold.exists_sections_isGeneralPositionGerm_of_isCompact` — Polyfold/Chapter6/Lemma629.lean, line 102
- `Polyfold.lemma_6_29` — Polyfold/Chapter6/Lemma629.lean, line 203

*What differs.*
- The text gives no proof; the one formalized is that of Theorem 5.18 (V5.38), under its hypotheses, which are the standing ones of §6.5 (Findings, Chapter 6, item 47).
- The conclusion is the general position of $F$ at the points $(t, \varphi(t), 0)$, which the text derives from (P) and which Lemmas 6.30, 6.31 use. (P) itself, the general position of each slice $F_t$, is not stated; as we read it, it follows, since the tangent vectors of the family of zeros lie in $\ker F'$ and $\mathbb R^n$ has no boundary (gap G.63; Findings, Chapter 6, item 47).

### V6.34. Lemma 6.30: the kernels along a family of zeros

*narrower* · a continuous family of kernels · manifold statements: gap G.62

**HWZ (§6.5, Lemma 6.30, p. 222).** The solution set $S$ of $F = 0$ near $(t, \varphi(t), 0)$ is a smooth manifold with boundary with corners containing $\{(t, \varphi(t), 0)\}$; by (P) the projection $\pi : S \to [0, 1]$ is a submersion, and its fibres $S_t$ are manifolds with boundary with corners. $L_t = T_{(\varphi(t),0)}S_t = \ker F_t'(\varphi(t), 0)$, and $L$ is a smooth vector bundle over $[0, 1]$.

**Proved in Lean.** For an sc-Fredholm section with tame germ data and a continuous family $y_q$ of zeros in good position, read in one chart at continuously varying level-$1$ points, the kernels of the linearizations form a continuous family of subspaces of the model space (`exists_subspaceFamily_linKer`, from local frames, `exists_local_frame_linKer`), of dimension the index (`StrongBundle.IsSurjLinOfIndex.finrank_linKer`). The derivative of an sc-smooth family of zeros $\mathbb R^n \to X$, read in a chart, lies in the kernel of the linearization (`hasFDerivAt_scDeriv_rn`, `fderiv_mem_linKer`).

- `Polyfold.StrongBundle.IsSurjLinOfIndex.finrank_linKer` — Polyfold/Chapter6/KernelFamily.lean, line 57
- `Polyfold.exists_local_frame_linKer` — Polyfold/Chapter6/KernelFamily.lean, line 94
- `Polyfold.exists_subspaceFamily_linKer` — Polyfold/Chapter6/KernelFamily.lean, line 166
- `Polyfold.hasFDerivAt_scDeriv_rn` — Polyfold/Chapter6/KernelFamily.lean, line 197
- `Polyfold.fderiv_mem_linKer` — Polyfold/Chapter6/KernelFamily.lean, line 217

*What differs.*
- The bundle $L$ is a continuous family of subspaces: near a zero in good position the kernel is the tangent space of the solution set (Theorem 3.54), the range of the derivative of an sc-retraction. The solution set as a manifold with boundary with corners near $(t, \varphi(t), 0)$, the map $\pi$ and the smooth structure of $L$ are not formalized; the continuation of orientations does not need them (gap G.62; Findings, Chapter 6, item 48).

### V6.35. Continuous families of subspaces and their determinant lines

*restated* · "vector bundle" = family of subspaces

**HWZ (§6.5, pp. 222–223; the bundles $\tilde L$, pp. 224–227).** $L = \bigcup_{t \in [0,1]}\{t\} \times L_t$ and $\lambda(L) = \bigcup_t\{t\} \times \lambda(L_t)$ over $[0, 1]$; an orientation of one line $\lambda(L_t)$ determines, by continuation, those of all the others, in particular one of $\lambda(L_0)$ determines one of $\lambda(L_1)$. The bundles $\tilde L$ over $[0, 1]^2$ are used in the same way.

**Proved in Lean.** `SubspaceFamily`: a family of $n$-dimensional subspaces of a normed space spanned near every point by a continuous frame; `SubspaceFamily.det`: the line bundle $b \mapsto \lambda(L_b)$, with the frames as trivializations (`SubspaceFamily.Frame.pretriv`, `SubspaceFamily.Frame.coordChange_continuousOn`). Families and orientations restrict along continuous maps (`SubspaceFamily.comp`, `LineOrientation.comp`); over $[0, 1]$ an orientation of $\lambda(L_0)$ is continued to $\lambda(L_1)$ (`SubspaceFamily.transport`, `SubspaceFamily.transport_eq`), injectively (`SubspaceFamily.transport_injective`), and over a simply connected, locally path-connected base the continuation along a path depends only on its end points (`SubspaceFamily.transport_comp`).

- `Polyfold.SubspaceFamily` — Polyfold/Chapter6/SubspaceBundle.lean, line 61
- `Polyfold.SubspaceFamily.det` — Polyfold/Chapter6/SubspaceBundle.lean, line 78
- `Polyfold.SubspaceFamily.Frame.pretriv` — Polyfold/Chapter6/SubspaceBundle.lean, line 154
- `Polyfold.SubspaceFamily.Frame.coordChange_continuousOn` — Polyfold/Chapter6/SubspaceBundle.lean, line 248
- `Polyfold.SubspaceFamily.comp` — Polyfold/Chapter6/SubspaceBundle.lean, line 323
- `Polyfold.LineOrientation.comp` — Polyfold/Chapter6/SubspaceBundle.lean, line 352
- `Polyfold.SubspaceFamily.transport` — Polyfold/Chapter6/SubspaceBundle.lean, line 374
- `Polyfold.SubspaceFamily.transport_eq` — Polyfold/Chapter6/SubspaceBundle.lean, line 380
- `Polyfold.SubspaceFamily.transport_injective` — Polyfold/Chapter6/SubspaceBundle.lean, line 390
- `Polyfold.SubspaceFamily.transport_comp` — Polyfold/Chapter6/SubspaceBundle.lean, line 403

*What differs.*
- "Vector bundle" is read as a family of subspaces of one model space with continuous local frames; the smooth structure of $L$ is not used (gap G.62).

### V6.36. Kernels, images and cuts of continuous families

*not in the book* · "varies continuously" made precise

**HWZ (§6.5, the continuity statements of pp. 223–226).** The proofs of Lemmas 6.33, 6.34 and of Theorem 6.35 use that "as $\tau$ varies, the bundle varies continuously", and that the data of the exact sequences at the end points vary continuously.

**Proved in Lean.** `exists_subspaceFamily_ker`: the kernels of a norm-continuous family of surjective Fredholm operators over a connected base form a continuous family of subspaces. `SubspaceFamily.exists_map`, `SubspaceFamily.isLineOrientation_map`: so do the images of a continuous family under a jointly continuous family of linear maps injective on its members, and orientations are carried along. `SubspaceFamily.exists_inf_ker`: cutting a continuous family by the kernel of a fixed $\ell$ that is onto on every member gives one.

- `Polyfold.exists_subspaceFamily_ker` — Polyfold/Chapter6/StabilizationContinuity.lean, line 128
- `Polyfold.SubspaceFamily.exists_map` — Polyfold/Chapter6/StabilizationContinuity.lean, line 170
- `Polyfold.SubspaceFamily.isLineOrientation_map` — Polyfold/Chapter6/StabilizationContinuity.lean, line 192
- `Polyfold.SubspaceFamily.exists_inf_ker` — Polyfold/Chapter6/StabilizationContinuity.lean, line 244

*What differs.*
- "Varies continuously" is read in the operator norm, and for maps into a model space as joint continuity.

### V6.37. The stabilized section in a product chart

*restated* · $\ker F_t'$ = $\ker F'$ cut by $\sigma = 0$

**HWZ (§6.5, $F$, p. 221; $F_t$, $L_t$ and (96), pp. 222–223).** $F_t(y, \lambda) = F(t, y, \lambda)$ on $X \times \mathbb R^k$, $L_t = \ker F_t'(\varphi(t), 0)$, and the exact sequence (96) relates $\ker((f - s(\cdot, t))'(\varphi(t)))$, $\ker F_t'(\varphi(t), 0)$, $\mathbb R^k$ and $Y_{\varphi(t)}/R((f - s(\cdot, t))'(\varphi(t)))$.

**Proved in Lean.** In the product chart $(\lambda \mapsto \lambda) \times ((q \mapsto q) \times \varphi)$ at $(0, (q, z))$ the linearization of $F$ is $(\lambda, (\sigma, v)) \mapsto D(\hat g_q \circ r)(z)v + \sum\lambda_i\hat s_i(q, \cdot)(z) + D_q\sigma$, with $g_q = f + S(q, \cdot)$ (`StrongBundle.scDeriv_paramSection_ofProd_ofProd`, with the chart lemmas `PullbackChartData.ofProd_scDeriv_r_apply`, `StrongBundle.scDeriv_ofProd_slice_apply`, `StrongBundleChart.paramDerivAt`). Its kernel cut by $\sigma = 0$ (`sliceProj`, `sliceIncl`) is the image of $\ker(T \oplus \varphi)$, with $T = g_q'(x) \in \mathrm{Lin}(f, x)$ (`mem_linSet_sectionAdd_pullbackSlice`) and $\varphi(\lambda) = \sum\lambda_is_i(q, x)$ (`linKer_inf_ker_sliceProj_eq_map`, `exists_sliceOps`, `exists_sliceKernel`); $T \oplus \varphi$ is onto when $F$ is in general position at $(0, (q, \Phi(q)))$ (`surjective_coprod_of_isLinSurjAt`).

- `Polyfold.PullbackChartData.ofProd_scDeriv_r_apply` — Polyfold/Chapter6/ParamKernel.lean, line 96
- `Polyfold.PullbackChartData.ofProd_mem_tangent_iff` — Polyfold/Chapter6/ParamKernel.lean, line 120
- `Polyfold.PullbackChartData.mem_K_ofProd_iff` — Polyfold/Chapter6/ParamKernel.lean, line 136
- `Polyfold.StrongBundle.scDeriv_ofProd_slice_apply` — Polyfold/Chapter6/ParamKernel.lean, line 164
- `Polyfold.StrongBundle.scDeriv_paramSection_apply` — Polyfold/Chapter6/ParamKernel.lean, line 225
- `Polyfold.StrongBundleChart.paramDerivAt` — Polyfold/Chapter6/ParamKernel.lean, line 375
- `Polyfold.StrongBundle.scDeriv_paramSection_ofProd_ofProd` — Polyfold/Chapter6/ParamKernel.lean, line 390
- `Polyfold.sliceProj` — Polyfold/Chapter6/ParamKernel.lean, line 450
- `Polyfold.sliceIncl` — Polyfold/Chapter6/ParamKernel.lean, line 461
- `Polyfold.linKer_inf_ker_sliceProj_eq_map` — Polyfold/Chapter6/ParamKernel.lean, line 503
- `Polyfold.exists_sliceOps` — Polyfold/Chapter6/ParamKernel.lean, line 566
- `Polyfold.mem_linSet_sectionAdd_pullbackSlice` — Polyfold/Chapter6/ParamKernel.lean, line 595
- `Polyfold.surjective_coprod_of_isLinSurjAt` — Polyfold/Chapter6/ParamKernel.lean, line 627
- `Polyfold.exists_sliceKernel` — Polyfold/Chapter6/ParamKernel.lean, line 745

*What differs.*
- $\ker F_t'(\varphi(t), 0)$ is read as the kernel of the linearization of the whole $F$ cut by $\sigma = 0$; in the product chart the linearization of the slice is $(v, \lambda) \mapsto Tv + \varphi\lambda$ (Findings, Chapter 6, item 49).

### V6.38. Lemma 6.31: the sequence (96) is exact

*restated* · $c$ onto by general position of $F$

**HWZ (§6.5, (96) and Lemma 6.31, p. 223).** The sequence (96), $0 \to \ker((f - s(\cdot, t))'(\varphi(t))) \to \ker F_t'(\varphi(t), 0) \to \mathbb R^k \to Y_{\varphi(t)}/R((f - s(\cdot, t))'(\varphi(t))) \to 0$, with $j$ the inclusion, $p$ the projection onto $\mathbb R^k$ and $c(\lambda) = \sum\lambda_is_i(t, \varphi(t)) + R(\cdot)$, is exact; $c$ is onto by property (P).

**Proved in Lean.** `lemma_6_31`: with the operators of V6.37, (96) $0 \to \ker T \to \ker(T \oplus \varphi) \to \mathbb R^k \to K_z/R(T) \to 0$ is the stabilization sequence of $T$ and $\varphi$ (V6.16), hence exact.

- `Polyfold.lemma_6_31` — Polyfold/Chapter6/ParamKernel.lean, line 797

*What differs.*
- The text has $c$ onto by (P); here $T \oplus \varphi$ is onto by the general position of $F$ (V6.33), and the $\mathbb R^n$-directions are absorbed because the derivative of the family of zeros lies in $\ker F'$ (`fderiv_mem_linKer`) (Findings, Chapter 6, item 49).

### V6.39. Continuation and the isomorphisms $\Phi_{E_t}$

*restated* · one statement for paths and squares

**HWZ (§6.5, pp. 223–224, after Lemma 6.31).** $\Phi_{E_t} : \det((f - s(\cdot, t))'(\varphi(t))) \to \lambda(L_t) \otimes \lambda^*(\mathbb R^k)$. An orientation $o_0$ of $\mathrm{DET}(f, \varphi(0))$ orients $\det((f - s(\cdot, 0))'(\varphi(0)))$; $\Phi_{E_0}$ turns it into an orientation of $\lambda(L_0) \otimes \lambda^*(\mathbb R^k)$, continuation extends it to $t = 1$, and $(\Phi_{E_1})^{-1}$ gives an orientation of $\det((f - s(\cdot, 1))'(\varphi(1)))$, hence $o_1$.

**Proved in Lean.** `SubspaceFamily.cont`: over a simply connected, locally path-connected base, the continuation of a ray of $\lambda(L_{q_0})$ to $\lambda(L_{q_1})$, a bijection (`SubspaceFamily.contEquiv`, `cont_eq`), compatible with composition and pull-back (`cont_self`, `cont_trans`, `cont_comp`), and along $[0, 1]$ the continuation of V6.35 (`cont_eq_transport`). For a stabilization $T \oplus \varphi$ onto and an identification of its kernel with $L$, the rays of $\det(T)$ and of $\lambda(L)$ correspond (`stabRayEquiv`, through $\iota_\varphi$ of V6.18 and $\det(T \oplus \varphi) \cong \lambda(\ker(T \oplus \varphi))$, `detEquivOfSurjective`); `propagate`: $\Phi_{E_0}$, continuation and $\Phi_{E_1}^{-1}$ composed, a bijection of the rays of $\det(T_0)$ and $\det(T_1)$ (`propagate_self`, `propagate_trans`, `propagate_comp`).

- `Polyfold.SubspaceFamily.cont` — Polyfold/Chapter6/Continuation.lean, line 63
- `Polyfold.SubspaceFamily.cont_eq` — Polyfold/Chapter6/Continuation.lean, line 67
- `Polyfold.SubspaceFamily.cont_self` — Polyfold/Chapter6/Continuation.lean, line 74
- `Polyfold.SubspaceFamily.cont_trans` — Polyfold/Chapter6/Continuation.lean, line 78
- `Polyfold.SubspaceFamily.contEquiv` — Polyfold/Chapter6/Continuation.lean, line 84
- `Polyfold.SubspaceFamily.cont_comp` — Polyfold/Chapter6/Continuation.lean, line 96
- `Polyfold.SubspaceFamily.cont_eq_transport` — Polyfold/Chapter6/Continuation.lean, line 106
- `Polyfold.detEquivOfSurjective` — Polyfold/Chapter6/Continuation.lean, line 156
- `Polyfold.stabRayEquiv` — Polyfold/Chapter6/Continuation.lean, line 179
- `Polyfold.propagate` — Polyfold/Chapter6/Continuation.lean, line 200
- `Polyfold.propagate_self` — Polyfold/Chapter6/Continuation.lean, line 211
- `Polyfold.propagate_trans` — Polyfold/Chapter6/Continuation.lean, line 221
- `Polyfold.propagate_comp` — Polyfold/Chapter6/Continuation.lean, line 242

*What differs.*
- Over any simply connected, locally path-connected base, so that one statement serves the paths and the squares; the fixed identification $\lambda^*(\mathbb R^k) \cong \lambda^*(\{0\})$ of (94) is used at both ends.

### V6.40. The stabilization sign $(-1)^{\dim\operatorname{coker}T}$

*restated* · sign $(-1)^{\dim\operatorname{coker}T}$ · an example without the sign

**HWZ (§6.3, formula (94), p. 212, as it is used on pp. 223–226).** The orientations carried by $\Phi_{E_t}$ along $t$, and those of the bundles $\tilde L_\tau$ along $\tau$, are used as varying continuously with the parameter (Lemmas 6.33, 6.34 and the homotopy argument before Theorem 6.35).

**Proved in Lean.** `coord_stabIota`: in a local determinant chart with projection $P$, the chart coordinate of $\iota_\psi(x) \in \det(S \oplus \psi)$ is $(-1)^{k\dim F/R(P) + \dim\operatorname{coker} S}D(S, \psi)$ times that of $x$, with $D$ (`stabD`) continuous and nowhere zero near the centre (`continuousOn_stabD`, `stabD_ne_zero`). `isLineOrientation_stabRay`: for a continuous orientation $o$ of $\mathrm{DET}$, a norm-continuous family $T_q$ and a continuous stabilization $\varphi_q$ with $T_q \oplus \varphi_q$ onto, the rays $(-1)^{\dim\operatorname{coker} T_q}\,\Phi(o(T_q))$ (`stabSign`) of $\lambda(\ker(T_q \oplus \varphi_q))$ form an orientation. `not_isLineOrientation_stabRay_uncorrected`: without the sign they need not ($E = F = \mathbb R$, $k = 1$, $T_q = q/(1 + |q|)$, $\varphi(r) = r_0$).

- `Polyfold.coord_stabIota` — Polyfold/Chapter6/StabilizationContinuity.lean, line 942
- `Polyfold.stabD` — Polyfold/Chapter6/StabilizationContinuity.lean, line 665
- `Polyfold.continuousOn_stabD` — Polyfold/Chapter6/StabilizationContinuity.lean, line 1172
- `Polyfold.stabD_ne_zero` — Polyfold/Chapter6/StabilizationContinuity.lean, line 721
- `Polyfold.stabSign` — Polyfold/Chapter6/StabilizationContinuity.lean, line 1009
- `Polyfold.isLineOrientation_stabRay` — Polyfold/Chapter6/StabilizationContinuity.lean, line 1371
- `Polyfold.not_isLineOrientation_stabRay_uncorrected` — Polyfold/Chapter6/StabilizationContinuity.lean, line 2060

*What differs.*
- As we read it, the orientations carried by $\Phi_E$ of (94) along a continuous family are not continuous where $\dim\operatorname{coker} T$ changes parity: the first exponent is constant on a chart, the second is not. The propagation uses the sign-normalized $(-1)^{\dim\operatorname{coker} T}\Phi_E$, which on each operator carries the text's orientation or its opposite (Findings, Chapter 6, item 50).

### V6.41. The push-forward $o_1 = \varphi_*o_0$ along stabilized kernels

*restated* · the sign at both end points · sections enter pointwise

**HWZ (§6.5, the push-forward, p. 224).** The orientation $o_1$ of $\mathrm{DET}(f, \varphi(1))$ obtained from $o_0$ by $\Phi_{E_0}$, continuation and $(\Phi_{E_1})^{-1}$ is the push-forward orientation $o_1 = \varphi_*o_0$; a priori it might depend on the choices of $s(y, t)$ and $s_1, \dots, s_k$.

**Proved in Lean.** At a chart point, `ChartPoint.stabT` is $T = (f + S)'(x) \in \mathrm{Lin}(f, x)$ (`ChartPoint.stabT_mem_linSet`) and `ChartPoint.stabPhi` is $\varphi(\lambda) = \sum\lambda_i\hat s_i(x)$. `IsStabKernels`: a continuous family $\Lambda$, over a parameter space, of the subspaces $\ker(T_q \oplus \varphi_q)$ of $E_0 \times \mathbb R^k$ at points $y(q)$, read in one chart. `IsStabKernels.push`: $\mathrm{Or}^f_{x_0} \to \mathrm{Or}^f_{x_1}$, $o \mapsto o(T_a) \mapsto (-1)^{\dim\operatorname{coker} T_a}\Phi_{E_a}(o(T_a))$, continued to $\lambda(\Lambda_b)$ and carried back in the same way at $T_b$. It depends only on the data (`IsStabKernels.push_congr`), is compatible with pull-back (`IsStabKernels.comp`, `IsStabKernels.push_comp`) and with concatenation (`IsStabKernels.push_trans`), and along a path with continuously varying data continuation carries the rays read at one parameter to those read at the next (`IsStabKernels.orRay`, `IsStabKernels.push_eq_orRay`, `IsStabKernels.cont_orRay_path`).

- `Polyfold.chartPt` — Polyfold/Chapter6/Propagation.lean, line 75
- `Polyfold.ChartPoint.stabT` — Polyfold/Chapter6/Propagation.lean, line 85
- `Polyfold.ChartPoint.stabT_mem_linSet` — Polyfold/Chapter6/Propagation.lean, line 97
- `Polyfold.ChartPoint.stabPhi` — Polyfold/Chapter6/Propagation.lean, line 112
- `Polyfold.ChartPoint.stabPhi_finAppend` — Polyfold/Chapter6/Propagation.lean, line 123
- `Polyfold.stabSign_inv` — Polyfold/Chapter6/Propagation.lean, line 143
- `Polyfold.toPerm_stabSign_symm` — Polyfold/Chapter6/Propagation.lean, line 147
- `Polyfold.isFredholm_stabCoprod` — Polyfold/Chapter6/Propagation.lean, line 181
- `Polyfold.IsStabKernels` — Polyfold/Chapter6/Propagation.lean, line 322
- `Polyfold.IsStabKernels.comp` — Polyfold/Chapter6/Propagation.lean, line 349
- `Polyfold.IsStabKernels.push` — Polyfold/Chapter6/Propagation.lean, line 365
- `Polyfold.IsStabKernels.push_congr` — Polyfold/Chapter6/Propagation.lean, line 394
- `Polyfold.IsStabKernels.orRay` — Polyfold/Chapter6/Propagation.lean, line 419
- `Polyfold.IsStabKernels.push_eq_orRay` — Polyfold/Chapter6/Propagation.lean, line 436
- `Polyfold.IsStabKernels.cont_orRay_path` — Polyfold/Chapter6/Propagation.lean, line 449
- `Polyfold.IsStabKernels.push_comp` — Polyfold/Chapter6/Propagation.lean, line 512
- `Polyfold.IsStabKernels.push_trans` — Polyfold/Chapter6/Propagation.lean, line 526

*What differs.*
- The sign of V6.40 is used at both end points; for given end-point operators the result differs from the text's by $(-1)^{\dim\operatorname{coker} T_a + \dim\operatorname{coker} T_b}$. The sections enter pointwise, and the continuity in the parameter is that of $\Lambda$ (Findings, Chapter 6, item 50).

### V6.42. Lemma 6.30 for the push-forward: the stabilized kernels exist

*narrower* · manifold statements: gap G.62

**HWZ (§6.5, Lemma 6.30 and the bundle $L$ after it, pp. 222–223).** Along the path the kernels $L_t = \ker F_t'(\varphi(t), 0)$, tangent spaces of the solution manifold $S_t$ of Lemma 6.30, form the smooth vector bundle $L$ over $[0, 1]$.

**Proved in Lean.** `exists_isStabKernels`: for an sc-smooth $\Phi : \mathbb R^n \to X$ with $\Phi([0, 1]^n)$ in the domain of a chart, an sc⁺-section $S$ with $f + S = 0$ along $\Phi$ near $[0, 1]^n$ and sc⁺-sections $s_1, \dots, s_k$ as in V6.33, the stabilized kernels of the slices form a continuous family over $[0, 1]^n$ (`IsStabKernels`), the points read through continuous lifts into the chart (`exists_continuousOn_lift_chart`).

- `Polyfold.exists_continuousOn_lift_chart` — Polyfold/Chapter6/StabKernelsExist.lean, line 57
- `Polyfold.exists_isStabKernels` — Polyfold/Chapter6/StabKernelsExist.lean, line 88

*What differs.*
- As V6.34 (gap G.62): the family is the tangent spaces of the solution set (V6.34) cut by $\{dt = 0\}$ (V6.36) and identified with $\ker(T_q \oplus \varphi_q)$ (V6.37) (Findings, Chapter 6, item 48).

### V6.43. Push-forward data along paths

*restated* · global sections of the pull-back · (P) used only to construct

**HWZ (§6.5, the choices along the path, pp. 221, 224).** Along an sc-smooth $\varphi : [0, 1] \to X$, "assuming $X = U$", one chooses by Proposition 6.28 an sc⁺-section $s$ with $s(\varphi(t), t) = f(\varphi(t))$, adds sections $s_1, \dots, s_k$ on $X \times [0, 1]$ with (P), and builds the push-forward from these choices.

**Proved in Lean.** `IsPush`: $e$ is a push-forward along an sc-smooth path $\gamma$ in a chart if there are global sc⁺-sections $S, s_1, \dots, s_k$ of $\pi^*P \to \mathbb R \times X$ with $(f + S)(t, \gamma(t)) = 0$ for $t$ near $[0, 1]$ (`isZeroAt_sectionAdd_reparamSection`) and a family of stabilized kernels of their slices along $\gamma$ whose push-forward is $e$. A push-forward along $\gamma$ is the composite of push-forwards along its two halves (`IsPush.split`, `isPush_reparam`), and along every sc-smooth path in a set with property (3) of Proposition 6.28 there is one (`exists_isPush`).

- `Polyfold.pt1_mem_Icc` — Polyfold/Chapter6/PushData.lean, line 64
- `Polyfold.exists_lift_of_smooth` — Polyfold/Chapter6/PushData.lean, line 72
- `Polyfold.chartPtOf` — Polyfold/Chapter6/PushData.lean, line 78
- `Polyfold.isZeroAt_sectionAdd_reparamSection` — Polyfold/Chapter6/PushData.lean, line 88
- `Polyfold.IsStabKernels.push_eq_of_eq` — Polyfold/Chapter6/PushData.lean, line 115
- `Polyfold.IsPush` — Polyfold/Chapter6/PushData.lean, line 139
- `Polyfold.isPush_reparam` — Polyfold/Chapter6/PushData.lean, line 161
- `Polyfold.IsPush.split` — Polyfold/Chapter6/PushData.lean, line 202
- `Polyfold.exists_isPush` — Polyfold/Chapter6/PushData.lean, line 257

*What differs.*
- Global sections of the pull-back in place of sections over $U \times [0, 1]$; property (P) is used only to construct a push-forward (Findings, Chapter 6, item 46).

### V6.44. Proposition 6.32: the push-forward does not depend on the choices

*restated* · one square for Lemmas 6.33, 6.34

**HWZ (§6.5, Proposition 6.32, p. 224 (proof pp. 224–226)).** For $U$ as in Proposition 6.28 and an sc-smooth $\varphi : [0, 1] \to U$, $o \mapsto \varphi_*o$ does not depend on the choices as long as the hypotheses of Lemma 6.29 hold. The proof adds sections to both data so that they have the same number and (P) holds along a convex homotopy, and applies Lemmas 6.33 and 6.34.

**Proved in Lean.** `proposition_6_32` ($X$ tame, bump functions, $f$ with tame germ data): two push-forwards (`IsPush`) along the same sc-smooth path in the domain of a chart agree. The proof uses one square: $S^\tau = (1 - \tau)S^0 + \tau S^1$ with the two families of sections interpolated (`isZeroAt_sectionAdd_combo`, `linAt_principal_combo`, `continuous_principal_pullbackSlice`) and the sections of Lemma 6.29 on the square appended (`IsStabKernels.push_eq_of_prefix`, `IsStabKernels.congr_data`, `IsStabKernels.push_congr_data`).

- `Polyfold.IsStabKernels.congr_data` — Polyfold/Chapter6/PropagationWellDefined.lean, line 91
- `Polyfold.IsStabKernels.push_congr_data` — Polyfold/Chapter6/PropagationWellDefined.lean, line 101
- `Polyfold.IsStabKernels.push_eq_of_prefix` — Polyfold/Chapter6/PropagationWellDefined.lean, line 114
- `Polyfold.isZeroAt_sectionAdd_combo` — Polyfold/Chapter6/PropagationWellDefined.lean, line 184
- `Polyfold.linAt_principal_combo` — Polyfold/Chapter6/PropagationWellDefined.lean, line 283
- `Polyfold.continuous_principal_pullbackSlice` — Polyfold/Chapter6/PropagationWellDefined.lean, line 317
- `Polyfold.proposition_6_32` — Polyfold/Chapter6/PropagationWellDefined.lean, line 390

*What differs.*
- "Does not depend on the choices" is read as the agreement of any two data. Lemmas 6.33 and 6.34 are combined over one square: at $\tau = 0$ the sections $s^0$ are the first $k^0$ of the family and at $\tau = 1$ the sections $s^1$ are the first $k^1$, so Lemma 6.33 applies on both edges without reordering; along the edges $t = 0, 1$ the operators are affine in $\tau$, hence continuous (Findings, Chapter 6, item 52).

### V6.45. Lemma 6.33: adding sections does not change the push-forward

*restated* · no homotopy needed · exact, with no sign

**HWZ (§6.5, Lemma 6.33, p. 224 (proof p. 225)).** If $F$ has property (P), the section $F(t, y, \lambda) + \sum\mu_j\bar s_j(y, t)$ on $[0, 1] \times X \times \mathbb R^{k+l}$ defines the same propagation along $\varphi$. The proof passes through the homotopy $\tilde F(\tau, \cdot)$, and at $\tau = 0$ "one verifies by a simple computation" that $\tilde L_0 = L \oplus ([0, 1] \times \mathbb R^l)$ defines the same propagation.

**Proved in Lean.** `detEquiv_stabIota_append`: with the appended sections last (`appendStab`, `kerAppend`), the stabilization isomorphism of $(\varphi, \psi)$ is that of $\varphi$ followed by `wedgeExt`, $w \mapsto (w, 0) \wedge \ell_1 \wedge \dots \wedge \ell_d$, for any $\ell_j \in \ker(T \oplus (\varphi, \psi))$ with $\psi$-coordinates the standard basis (`wedgeExt_wedge`, `wedgeExt_congr`, `wedgeExt_bijective`); this map carries continuous orientations along the family (`isLineOrientation_wedgeExt`, with `SubspaceFamily.exists_continuous_lifts`, `kerEquivMap`). Hence appending sections does not change the push-forward (`stabRayEquiv_append`, `propagate_append`, `IsStabKernels.push_append`).

- `Polyfold.wedgeExt` — Polyfold/Chapter6/AddSections.lean, line 54
- `Polyfold.wedgeExt_wedge` — Polyfold/Chapter6/AddSections.lean, line 61
- `Polyfold.wedgeExt_congr` — Polyfold/Chapter6/AddSections.lean, line 79
- `Polyfold.wedgeExt_bijective` — Polyfold/Chapter6/AddSections.lean, line 153
- `Polyfold.appendStab` — Polyfold/Chapter6/AddSections.lean, line 252
- `Polyfold.kerAppend` — Polyfold/Chapter6/AddSections.lean, line 276
- `Polyfold.detEquiv_stabIota_append` — Polyfold/Chapter6/AddSections.lean, line 515
- `Polyfold.SubspaceFamily.exists_continuous_lifts` — Polyfold/Chapter6/AddSections.lean, line 552
- `Polyfold.isLineOrientation_wedgeExt` — Polyfold/Chapter6/AddSections.lean, line 611
- `Polyfold.kerEquivMap` — Polyfold/Chapter6/AddSections.lean, line 720
- `Polyfold.stabRayEquiv_append` — Polyfold/Chapter6/AddSections.lean, line 770
- `Polyfold.propagate_append` — Polyfold/Chapter6/AddSections.lean, line 828
- `Polyfold.IsStabKernels.push_append` — Polyfold/Chapter6/Propagation.lean, line 543

*What differs.*
- The homotopy $\tilde F(\tau, \cdot)$ of the text's proof is not needed: with the appended sections last the two isomorphisms agree exactly, with no sign. The comparison is made directly between $T \oplus \varphi$ and $T \oplus (\varphi, \psi)$, at the end points by Proposition 6.15 and along the family by `isLineOrientation_wedgeExt` (Findings, Chapter 6, item 51).

### V6.46. Sections over parameter families

*as in the book*

**HWZ (§6.5, pp. 224–226).** The added sections $\bar s_j(y, t)$ of Lemma 6.33 (p. 224) and the sections $s(y, \tau, t)$, $s_i(y, \tau, t)$ over a square (p. 226) are used as sc⁺-sections over the products, and adding sections is taken to keep the general position (said in the proof of Theorem 5.18, p. 178).

**Proved in Lean.** `reparamSection`: for $g$ affine, $(q, y) \mapsto S(g(q), y)$ is again an sc⁺-section of the pull-back (`StrongBundle.IsScPlusSection.reparam`, `pullbackSlice_reparamSection`, `rnProdMapOp`); `StrongBundle.isScPlusSection_of_local`: sc⁺-sections may be checked in one chart around each point; `StrongBundle.isGeneralPositionGerm_paramSection_of_comp`: adding sections keeps the general position of $F$ at $(0, y)$.

- `Polyfold.reparamSection` — Polyfold/Chapter6/FamilySections.lean, line 37
- `Polyfold.pullbackSlice_reparamSection` — Polyfold/Chapter6/FamilySections.lean, line 46
- `Polyfold.rnProdMapOp` — Polyfold/Chapter6/FamilySections.lean, line 53
- `Polyfold.StrongBundle.isScPlusSection_of_local` — Polyfold/Chapter6/FamilySections.lean, line 61
- `Polyfold.StrongBundle.IsScPlusSection.reparam` — Polyfold/Chapter6/FamilySections.lean, line 82
- `Polyfold.StrongBundle.isGeneralPositionGerm_paramSection_of_comp` — Polyfold/Chapter6/FamilySections.lean, line 142

*What differs.*
- As the text uses them; these are the tools of V6.43–V6.45.

### V6.47. Lemma 6.34: the convex homotopy of the sections $s$

*restated* · part of the square of V6.44

**HWZ (§6.5, Lemma 6.34, p. 226).** For sc⁺-sections $s^0$, $s^1$ with $s^i(\varphi(t), t) = f(\varphi(t))$, $s^\tau = \tau s^1 + (1 - \tau)s^0$ and sections $s^\tau_1, \dots, s^\tau_k$ with (P) for every $\tau$, the propagation along $\varphi$ is the same for every $\tau$; at $t = 0, 1$ the linearizations vary continuously in $\mathrm{DET}(f, \varphi(0))$ and $\mathrm{DET}(f, \varphi(1))$.

**Proved in Lean.** `IsStabKernels.push_square`: for a family of stabilized kernels over the square $[0, 1]^2$ with the end points $x_0$, $x_1$ fixed and the end-point operators varying continuously, the push-forwards along the edges $\tau = 0$ and $\tau = 1$ (`sqEdge`, `sqPath`) agree.

- `Polyfold.IsStabKernels.push_square` — Polyfold/Chapter6/Propagation.lean, line 641
- `Polyfold.sqEdge` — Polyfold/Chapter6/PropagationWellDefined.lean, line 360
- `Polyfold.sqPath` — Polyfold/Chapter6/PropagationWellDefined.lean, line 367

*What differs.*
- The convex homotopy $s^\tau$ of the lemma is part of the square of V6.44; the continuity of the end-point orientations along $\tau$ is that of V6.40, with the sign (Findings, Chapter 6, items 50, 52).

### V6.48. Theorem 6.35: local propagation

*narrower* · the section $f$ supplied · contractibility: gap G.61 · (1′) and a reparametrization

**HWZ (§6.5, the homotopy argument, pp. 226–227, and Theorem 6.35, p. 227).** For a strong bundle over a tame $X$ and a smooth $x$ there is an open sc-smoothly contractible $U(x)$ such that along every sc-smooth path $\varphi : [0, 1] \to U$ there is a well-defined propagation $o \mapsto \varphi_*o$ of orientations of $\mathrm{DET}(f, \varphi(0))$, and $\varphi_{0*}o = \varphi_{1*}o$ for two such paths with the same end points. The proof homotopes $\varphi_0$ to $\varphi_1$ in $U$, using that $U$ is sc-smoothly contractible.

**Proved in Lean.** `theorem_6_35` ($X$ tame, bump functions, $f$ with tame germ data): every smooth $x$ has an open $U \ni x$ and a chart $c$ of the atlas with `HasLocalPropagation`: push-forwards exist along the sc-smooth paths in $U$ with smooth end points and depend only on their end points. `push_eq_of_homotopy`: push-forwards along two paths related by an sc-smooth homotopy with fixed end points agree.

- `Polyfold.push_eq_of_homotopy` — Polyfold/Chapter6/PropagationWellDefined.lean, line 601
- `Polyfold.HasLocalPropagation` — Polyfold/Chapter6/PropagationWellDefined.lean, line 719
- `Polyfold.theorem_6_35` — Polyfold/Chapter6/PropagationWellDefined.lean, line 740

*What differs.*
- The statement does not introduce the section $f$ (possible omission); it is read for an sc-Fredholm section with tame germ data, under the standing hypotheses (Findings, Chapter 6, item 53).
- $U$ is not shown to be sc-smoothly contractible (gap G.61); what the proof uses is (1′) of V6.32. Since the homotopy of (1′) meets its edge conditions only on $[0, 1]$, while a push-forward datum needs $f + S = 0$ near $[0, 1]$, the proof passes through the reparametrized paths $\gamma_i \circ \kappa$, with three homotopies whose edges are exact (Findings, Chapter 6, item 53).

### V6.49. Sc-smooth paths in a chart and their concatenation

*narrower* · paths joined only inside a chart · p. 201 facts: gap G.56

**HWZ (§6.5, the paths after Theorem 6.35, p. 227, and the concatenation, p. 228).** For $y \in U$ one takes an sc-smooth path $\varphi : [0, 1] \to U$ from $x$ to $y$. The composition of paths is $\varphi(\beta(s))$ for $s \in [0, 1/2]$ and $\psi(\beta(s))$ for $s \in [1/2, 1]$, for a smooth $\beta$ with $\beta([0, 1/2]) = [0, 1]$, $\beta([1/2, 1]) = [1, 2]$, constant near $1/2$. On p. 201 the text recalls that an M-polyfold is locally path connected and that smooth points of one path component are joined by an sc⁺-smooth path.

**Proved in Lean.** `exists_nhds_scPath`: for an open $U$ in the domain of a chart and $x \in U$ there is an open $V \ni x$ in $U$ whose smooth points are pairwise joined by sc-smooth paths in $U$. `concatPath`: $\gamma_1(\kappa(3s))$ for $s \le 1/2$ and $\gamma_2(\kappa(3s - 2))$ for $s > 1/2$, $\kappa$ the smooth transition function, is sc-smooth (`isScSmoothMap_concatPath`), with the right end points and halves (`concatPath_zero`, `concatPath_one`, `concatPath_half₁`, `concatPath_half₂`); reparametrizing by a $C^\infty$ map keeps sc-smoothness (`isScSmoothMap_reparam`); push-forwards compose along concatenations (`HasLocalPropagation.eq_trans`).

- `Polyfold.MPolyfold.isScSmoothMap_of_eventuallyEq` — Polyfold/Chapter6/ScPaths.lean, line 54
- `Polyfold.pt1_apply` — Polyfold/Chapter6/ScPaths.lean, line 72
- `Polyfold.contDiff_pt1_comp` — Polyfold/Chapter6/ScPaths.lean, line 75
- `Polyfold.exists_nhds_scPath` — Polyfold/Chapter6/ScPaths.lean, line 84
- `Polyfold.concatPath` — Polyfold/Chapter6/ScPaths.lean, line 177
- `Polyfold.concatPath_of_le` — Polyfold/Chapter6/ScPaths.lean, line 186
- `Polyfold.concatPath_of_gt` — Polyfold/Chapter6/ScPaths.lean, line 191
- `Polyfold.isScSmoothMap_concatPath` — Polyfold/Chapter6/ScPaths.lean, line 196
- `Polyfold.concatPath_zero` — Polyfold/Chapter6/ScPaths.lean, line 236
- `Polyfold.concatPath_one` — Polyfold/Chapter6/ScPaths.lean, line 240
- `Polyfold.concatPath_half₁` — Polyfold/Chapter6/ScPaths.lean, line 256
- `Polyfold.concatPath_half₂` — Polyfold/Chapter6/ScPaths.lean, line 262
- `Polyfold.isScSmoothMap_reparam` — Polyfold/Chapter6/ScPaths.lean, line 275
- `Polyfold.HasLocalPropagation.eq_trans` — Polyfold/Chapter6/ContinuousOrientation.lean, line 59

*What differs.*
- Paths are joined only locally, inside a chart; the global facts recalled on p. 201 (local path connectedness, sc⁺-smooth paths within a path component) are not formalized (gap G.56; Findings, Chapter 6, item 42).

### V6.50. Definition 6.36: orientable neighbourhoods and continuous orientations

*restated* · a pair $V \subseteq U$

**HWZ (§6.5, the paragraph after Theorem 6.35 and Definition 6.36, p. 227).** Fixing $o_x$, $o_y = \varphi_*o_x$ for a path $\varphi$ in $U$ from $x$ to $y$ does not depend on the path, and $\psi_*o_{y_1} = o_{y_2}$ for paths in $U$. An open contractible $U(x)$ on which the local propagation can be carried out is an orientable neighbourhood of $(f, x)$; a choice of orientations of $\mathrm{DET}(f, y)$, $y \in U_\infty$, with the propagation property is a continuous orientation, and an orientable neighbourhood has precisely two.

**Proved in Lean.** `IsOrientableNbhd`: a pair $V \subseteq U$, $U$ open with the local propagation property in a chart, $V \ni x$ open with any two smooth points joined by an sc-smooth path in $U$; every smooth point has one (`exists_orientableNbhd`, `exists_isOrientableNbhd`). `IsContinuousOrientation`: a choice $y \mapsto o_y$ on $V_\infty$ carried into itself by the push-forwards along paths in $U$; there are exactly two (`exists_two_isContinuousOrientation`).

- `Polyfold.IsContinuousOrientation` — Polyfold/Chapter6/ContinuousOrientation.lean, line 126
- `Polyfold.exists_two_isContinuousOrientation` — Polyfold/Chapter6/ContinuousOrientation.lean, line 141
- `Polyfold.exists_orientableNbhd` — Polyfold/Chapter6/ContinuousOrientation.lean, line 201
- `Polyfold.IsOrientableNbhd` — Polyfold/Chapter6/SectionOrientation.lean, line 100
- `Polyfold.exists_isOrientableNbhd` — Polyfold/Chapter6/SectionOrientation.lean, line 112

*What differs.*
- The pair $V \subseteq U$ replaces an open contractible $U$, since Proposition 6.28 gives (1′) (gap G.61; Findings, Chapter 6, item 54).

### V6.51. Reparametrization homotopies

*as in the book*

**HWZ (§6.5, the homotopy classes $[\varphi]$, pp. 227–228).** $[\varphi]$ is the sc-smooth homotopy class of $\varphi : [0, 1] \to X$ with the end points fixed, with source $\varphi(0)$ and target $\varphi(1)$; the composition of classes is defined through a reparametrization $\beta$.

**Proved in Lean.** `isScHomotopyRel_reparam`: for a $C^\infty$ $\theta$ with $\theta(0) = 0$ and $\theta(1) = 1$, $\gamma \circ \theta$ is sc-smoothly homotopic to $\gamma$ with the end points fixed, inside every set containing $\gamma([0, 1])$ when $\theta([0, 1]) \subseteq [0, 1]$ (`reparam_mem`); the concatenation of the two halves of $\gamma$ is such a reparametrization (`leftHalf`, `rightHalf`, `halvesReparam`, `concatPath_halves`).

- `Polyfold.mem_smoothSet_of_isScSmoothMap` — Polyfold/Chapter6/ScHomotopy.lean, line 47
- `Polyfold.contDiff_pt2_comp` — Polyfold/Chapter6/ScHomotopy.lean, line 52
- `Polyfold.isScHomotopyRel_reparam` — Polyfold/Chapter6/ScHomotopy.lean, line 62
- `Polyfold.reparam_mem` — Polyfold/Chapter6/ScHomotopy.lean, line 83
- `Polyfold.leftHalf` — Polyfold/Chapter6/ScHomotopy.lean, line 98
- `Polyfold.rightHalf` — Polyfold/Chapter6/ScHomotopy.lean, line 101
- `Polyfold.halvesReparam` — Polyfold/Chapter6/ScHomotopy.lean, line 137
- `Polyfold.concatPath_halves` — Polyfold/Chapter6/ScHomotopy.lean, line 165

*What differs.*
- As the text uses them; these are the tools of V6.52 and V6.56.

### V6.52. The path category $PX$

*restated* · a groupoid · identities: the constant paths · second piece read as $\psi(\beta(s) - 1)$

**HWZ (§6.5, the classes $[\varphi]$, their composition and the category $PX$, pp. 227–228).** For $t([\varphi]) = s([\psi])$, $[\psi] * [\varphi]$ is the class of $\gamma$, equal to $\varphi(\beta(s))$ on $[0, 1/2]$ and $\psi(\beta(s))$ on $[1/2, 1]$; this gives a category $PX$ whose objects are the smooth points of $X$ and whose morphisms $x \to y$ are the classes with source $x$ and target $y$.

**Proved in Lean.** `ScHomotopic`: sc-smooth homotopy with the end points fixed, an equivalence relation on the sc-smooth paths `ScPath` between two points (`ScHomotopic.refl`, `ScHomotopic.symm`, `ScHomotopic.trans`). `ScPath.concat` is well defined on classes (`ScPath.concat_congr`), associative (`ScPath.concat_assoc`, via `assocReparam`, `isScHomotopyRel_triHomotopy`), with the classes of the constant paths as units (`ScPath.const_concat`, `ScPath.concat_const`) and the reversed paths as inverses (`ScPath.concat_reverse`, `ScPath.reverse_concat`). `PathCat`: the smooth points with the classes `ScPathClass` form a category (`PathCat.category`), indeed a groupoid (`PathCat.groupoid`).

- `Polyfold.smoothTransition_half` — Polyfold/Chapter6/PathCategory.lean, line 80
- `Polyfold.isScSmoothMap_const_of_mem_smoothSet` — Polyfold/Chapter6/PathCategory.lean, line 87
- `Polyfold.isScSmoothMap_ite` — Polyfold/Chapter6/PathCategory.lean, line 99
- `Polyfold.isScSmoothMap_ite₃` — Polyfold/Chapter6/PathCategory.lean, line 118
- `Polyfold.concatPath_of_le_two_thirds` — Polyfold/Chapter6/PathCategory.lean, line 155
- `Polyfold.concatPath_of_one_third_le` — Polyfold/Chapter6/PathCategory.lean, line 165
- `Polyfold.ScHomotopic` — Polyfold/Chapter6/PathCategory.lean, line 180
- `Polyfold.ScHomotopic.refl` — Polyfold/Chapter6/PathCategory.lean, line 284
- `Polyfold.ScHomotopic.symm` — Polyfold/Chapter6/PathCategory.lean, line 288
- `Polyfold.ScHomotopic.trans` — Polyfold/Chapter6/PathCategory.lean, line 296
- `Polyfold.isScHomotopyRel_triHomotopy` — Polyfold/Chapter6/PathCategory.lean, line 410
- `Polyfold.assocReparam` — Polyfold/Chapter6/PathCategory.lean, line 455
- `Polyfold.ScPath` — Polyfold/Chapter6/PathCategory.lean, line 688
- `Polyfold.ScPath.source_mem_smoothSet` — Polyfold/Chapter6/PathCategory.lean, line 703
- `Polyfold.ScPath.target_mem_smoothSet` — Polyfold/Chapter6/PathCategory.lean, line 707
- `Polyfold.ScPath.const` — Polyfold/Chapter6/PathCategory.lean, line 725
- `Polyfold.ScPath.concat` — Polyfold/Chapter6/PathCategory.lean, line 733
- `Polyfold.ScPath.reverse` — Polyfold/Chapter6/PathCategory.lean, line 742
- `Polyfold.ScPath.concat_congr` — Polyfold/Chapter6/PathCategory.lean, line 750
- `Polyfold.ScPath.const_concat` — Polyfold/Chapter6/PathCategory.lean, line 758
- `Polyfold.ScPath.concat_const` — Polyfold/Chapter6/PathCategory.lean, line 773
- `Polyfold.ScPath.concat_assoc` — Polyfold/Chapter6/PathCategory.lean, line 787
- `Polyfold.ScPath.concat_reverse` — Polyfold/Chapter6/PathCategory.lean, line 803
- `Polyfold.ScPath.reverse_concat` — Polyfold/Chapter6/PathCategory.lean, line 808
- `Polyfold.ScPathClass` — Polyfold/Chapter6/PathCategory.lean, line 817
- `Polyfold.ScPathClass.comp` — Polyfold/Chapter6/PathCategory.lean, line 824
- `Polyfold.PathCat` — Polyfold/Chapter6/PathCategory.lean, line 845
- `Polyfold.PathCat.category` — Polyfold/Chapter6/PathCategory.lean, line 857
- `Polyfold.PathCat.groupoid` — Polyfold/Chapter6/PathCategory.lean, line 889
- `Polyfold.PathCat.homMk` — Polyfold/Chapter6/PathCategory.lean, line 868
- `Polyfold.PathCat.comp_mk` — Polyfold/Chapter6/PathCategory.lean, line 871
- `Polyfold.PathCat.id_eq_mk` — Polyfold/Chapter6/PathCategory.lean, line 875
- `Polyfold.PathCat.mk_eq_mk_iff` — Polyfold/Chapter6/PathCategory.lean, line 878
- `Polyfold.PathCat.exists_eq_mk` — Polyfold/Chapter6/PathCategory.lean, line 883
- `Polyfold.PathCat.inv_mk` — Polyfold/Chapter6/PathCategory.lean, line 898

*What differs.*
- The edge conditions of a homotopy hold only on $[0, 1]$ (decision D2), so transitivity is proved after reparametrizing by $\kappa$; the identities, which the text does not name, are the classes of the constant paths (Findings, Chapter 6, item 71).
- With $\beta([1/2, 1]) = [1, 2]$ the second piece $\psi(\beta(s))$ leaves $[0, 1]$; it is read as $\psi(\beta(s) - 1)$ (possible misprint). Mathlib's $[\varphi] \gg [\psi]$ is the text's $[\psi] * [\varphi]$ (Findings, Chapter 6, item 55).

### V6.53. Transferring orientations between chart points

*not in the book* · chart-free objects compared in charts

**HWZ (§6.5, p. 219, and the proof of Theorem 6.37, p. 228).** $T_xX$, $Y_x$ and $\mathrm{Lin}(f, x) \subseteq \mathcal L(T_xX, Y_x)$, with the metric of the operator norm, are used as intrinsic objects (p. 219); the proof of Theorem 6.37 carries orientations along orientable neighbourhoods of different points of a path.

**Proved in Lean.** `conjDet`: for isomorphisms $A$, $\Gamma$ with $S'A = \Gamma S$, $\det(S) \cong \det(S')$ by $A$ on kernels and $\Gamma$ on cokernels (`conjKerEquiv`, `conjCokerEquiv`, `conjDet_wedge_tmul`), compatible with composition (`conjDet_refl`, `conjDet_trans`, `conjDet_congr`) and with the $\gamma^P$ (`IsGoodLeftProj.conj`, `gammaProj_conjDet`, `coord_conjDet_coordInv`); continuous orientations of $\mathrm{DET}$ are carried along (`isLineOrientation_conj`, `LineOrientation.conj`). For two chart points at $x$, $A$ is the derivative at $z$ of the base transition (`ChartPoint.baseDeriv`) and $\Gamma$ the fibre part of the strong bundle transition (`ChartPoint.fiberMap`), with the cocycle rules (`ChartPoint.transferT`, `ChartPoint.transferK`); $L \in \mathrm{Lin}_p(f, x)$ iff $\Gamma LA^{-1} \in \mathrm{Lin}_{p'}(f, x)$ (`ChartPoint.mem_linSet_transfer_iff`), and the induced bijection $\mathrm{Or}^f_x(p) \cong \mathrm{Or}^f_x(p')$ (`ChartPoint.orTransfer`) satisfies the cocycle rules (`ChartPoint.orTransfer_self`, `ChartPoint.orTransfer_trans`).

- `Polyfold.conjKerEquiv` — Polyfold/Chapter6/ChartTransfer.lean, line 87
- `Polyfold.conjCokerEquiv` — Polyfold/Chapter6/ChartTransfer.lean, line 121
- `Polyfold.conjDet` — Polyfold/Chapter6/ChartTransfer.lean, line 132
- `Polyfold.conjDet_wedge_tmul` — Polyfold/Chapter6/ChartTransfer.lean, line 138
- `Polyfold.conjDet_trans` — Polyfold/Chapter6/ChartTransfer.lean, line 171
- `Polyfold.conjDet_congr` — Polyfold/Chapter6/ChartTransfer.lean, line 188
- `Polyfold.conjDet_refl` — Polyfold/Chapter6/ChartTransfer.lean, line 196
- `Polyfold.IsGoodLeftProj.conj` — Polyfold/Chapter6/ChartTransfer.lean, line 238
- `Polyfold.gammaProj_conjDet` — Polyfold/Chapter6/ChartTransfer.lean, line 257
- `Polyfold.coord_conjDet_coordInv` — Polyfold/Chapter6/ChartTransfer.lean, line 367
- `Polyfold.isLineOrientation_conj` — Polyfold/Chapter6/ChartTransfer.lean, line 472
- `Polyfold.LineOrientation.conj` — Polyfold/Chapter6/ChartTransfer.lean, line 587
- `Polyfold.LineOrientation.conj_apply` — Polyfold/Chapter6/ChartTransfer.lean, line 604
- `Polyfold.LineOrientation.conj_refl` — Polyfold/Chapter6/ChartTransfer.lean, line 612
- `Polyfold.LineOrientation.conj_trans` — Polyfold/Chapter6/ChartTransfer.lean, line 637
- `Polyfold.LineOrientation.conj_congr` — Polyfold/Chapter6/ChartTransfer.lean, line 660
- `Polyfold.ChartPoint.baseDeriv` — Polyfold/Chapter6/ChartTransfer.lean, line 762
- `Polyfold.ChartPoint.baseDeriv_self` — Polyfold/Chapter6/ChartTransfer.lean, line 766
- `Polyfold.ChartPoint.baseDeriv_trans` — Polyfold/Chapter6/ChartTransfer.lean, line 779
- `Polyfold.ChartPoint.isScOperator_baseDeriv` — Polyfold/Chapter6/ChartTransfer.lean, line 845
- `Polyfold.ChartPoint.fiberMap` — Polyfold/Chapter6/ChartTransfer.lean, line 857
- `Polyfold.ChartPoint.fiberMap_self` — Polyfold/Chapter6/ChartTransfer.lean, line 886
- `Polyfold.ChartPoint.fiberMap_trans` — Polyfold/Chapter6/ChartTransfer.lean, line 893
- `Polyfold.ChartPoint.isScOperator_fiberMap` — Polyfold/Chapter6/ChartTransfer.lean, line 989
- `Polyfold.ChartPoint.transferT` — Polyfold/Chapter6/ChartTransfer.lean, line 907
- `Polyfold.ChartPoint.transferK` — Polyfold/Chapter6/ChartTransfer.lean, line 913
- `Polyfold.ChartPoint.transferT_self_apply` — Polyfold/Chapter6/ChartTransfer.lean, line 929
- `Polyfold.ChartPoint.transferT_trans_apply` — Polyfold/Chapter6/ChartTransfer.lean, line 939
- `Polyfold.ChartPoint.scDeriv_principal_baseDeriv` — Polyfold/Chapter6/ChartTransfer.lean, line 1009
- `Polyfold.ChartPoint.IsScPlusOp.conj` — Polyfold/Chapter6/ChartTransfer.lean, line 1115
- `Polyfold.ChartPoint.mem_linSet_transfer_iff` — Polyfold/Chapter6/ChartTransfer.lean, line 1157
- `Polyfold.ChartPoint.orTransfer` — Polyfold/Chapter6/ChartTransfer.lean, line 1205
- `Polyfold.ChartPoint.orTransfer_apply` — Polyfold/Chapter6/ChartTransfer.lean, line 1216
- `Polyfold.ChartPoint.orTransfer_self` — Polyfold/Chapter6/ChartTransfer.lean, line 1224
- `Polyfold.ChartPoint.orTransfer_trans` — Polyfold/Chapter6/ChartTransfer.lean, line 1234

*What differs.*
- The text treats $T_xX$, $Y_x$, $\mathrm{Lin}(f, x)$ and $\mathrm{Or}^f_x$ as chart-free; here $T_xX$ has no linear structure (gaps G.6, G.7, G.13), and the identification between charts is made explicit (Findings, Chapter 6, item 70).

### V6.54. The push-forward does not depend on the chart

*not in the book* · the text does not compare charts

**HWZ (§6.5, the push-forward and the proof of Theorem 6.37, pp. 222–228).** The push-forward is built in one strong bundle chart; the proof of Theorem 6.37 uses orientable neighbourhoods of different points of a path, which may lie in different charts.

**Proved in Lean.** The stabilization isomorphism and the sign are natural under conjugation (`stabSign_conj`, `coprod_conj`, `ker_coprod_conj`, `surjective_coprod_conj`, `conj_stab_key`, `stabRayEquiv_conjDet`), and continuation is natural under jointly continuous families of injective linear maps (`SubspaceFamily.cont_map`). A family of stabilized kernels in one chart is carried by the derivative of the base transition (`continuous_baseDeriv`) to one in a second chart, with the same sections (`IsStabKernels.exists_transfer`, `IsStabKernels.orRay_transfer`, with `ChartPoint.fiberMap_principal`, `ChartPoint.conj_of_linAt`, `ChartPoint.conj_of_principal`); a push-forward in one chart, conjugated by the transfer of V6.53 at the end points, is a push-forward in the other (`IsPush.transfer`), so the local propagations of two charts agree (`HasLocalPropagation.push_compat`).

- `Polyfold.stabSign_conj` — Polyfold/Chapter6/PushTransfer.lean, line 71
- `Polyfold.coprod_conj` — Polyfold/Chapter6/PushTransfer.lean, line 76
- `Polyfold.ker_coprod_conj` — Polyfold/Chapter6/PushTransfer.lean, line 86
- `Polyfold.surjective_coprod_conj` — Polyfold/Chapter6/PushTransfer.lean, line 108
- `Polyfold.conj_stab_key` — Polyfold/Chapter6/PushTransfer.lean, line 119
- `Polyfold.stabRayEquiv_conjDet` — Polyfold/Chapter6/PushTransfer.lean, line 212
- `Polyfold.SubspaceFamily.cont_map` — Polyfold/Chapter6/PushTransfer.lean, line 285
- `Polyfold.ChartPoint.fiberMap_principal` — Polyfold/Chapter6/PushTransfer.lean, line 313
- `Polyfold.ChartPoint.conj_of_linAt` — Polyfold/Chapter6/PushTransfer.lean, line 325
- `Polyfold.ChartPoint.conj_of_principal` — Polyfold/Chapter6/PushTransfer.lean, line 335
- `Polyfold.continuous_baseDeriv` — Polyfold/Chapter6/PushTransfer.lean, line 365
- `Polyfold.IsStabKernels.exists_transfer` — Polyfold/Chapter6/PushTransfer.lean, line 399
- `Polyfold.IsStabKernels.orRay_transfer` — Polyfold/Chapter6/PushTransfer.lean, line 458
- `Polyfold.IsPush.transfer` — Polyfold/Chapter6/PushTransfer.lean, line 536
- `Polyfold.HasLocalPropagation.push_compat` — Polyfold/Chapter6/PushTransfer.lean, line 606

*What differs.*
- Needed for Theorem 6.37; the text does not compare charts (Findings, Chapter 6, item 70).

### V6.55. $\mathrm{Or}^f_x$ in a chosen chart

*restated* · a chosen chart

**HWZ (§6.5, Definition 6.27 and the objects of Theorem 6.37, pp. 220, 228).** $\mathrm{Or}^f_x$, the set of the two orientations of $\mathrm{DET}(f, x)$, is the object that $\Gamma_f$ assigns to the smooth point $x$.

**Proved in Lean.** `orChart x`: a chosen chart of the atlas at $x$ (`isChart_orChart`, `mem_orChart`); `Orx`: the orientations read in it, with two elements (`exists_two_orx`); `toChartOr`: their identification with the orientations read in any other chart at $x$ by the transfer of V6.53, compatible with composition (`toChartOr_orChart`, `toChartOr_trans`); `restrictOr`: a family $y \mapsto o_y$ read in the chart of an orientable neighbourhood.

- `Polyfold.orChart` — Polyfold/Chapter6/SectionOrientation.lean, line 62
- `Polyfold.isChart_orChart` — Polyfold/Chapter6/SectionOrientation.lean, line 64
- `Polyfold.mem_orChart` — Polyfold/Chapter6/SectionOrientation.lean, line 67
- `Polyfold.Orx` — Polyfold/Chapter6/SectionOrientation.lean, line 73
- `Polyfold.toChartOr` — Polyfold/Chapter6/SectionOrientation.lean, line 78
- `Polyfold.toChartOr_orChart` — Polyfold/Chapter6/SectionOrientation.lean, line 85
- `Polyfold.toChartOr_trans` — Polyfold/Chapter6/OrientationFunctor.lean, line 263
- `Polyfold.exists_two_orx` — Polyfold/Chapter6/OrientationFunctor.lean, line 257
- `Polyfold.restrictOr` — Polyfold/Chapter6/SectionOrientation.lean, line 124

*What differs.*
- A chosen chart stands for the text's chart-free $\mathrm{Or}^f_x$ (Findings, Chapter 6, item 70).

### V6.56. Transport along paths from local push-forwards

*restated* · dyadic subdivisions

**HWZ (§6.5, the proof of Theorem 6.37, p. 228).** For a path $\varphi$ and $t_0 \in [0, 1]$ one chooses an orientable neighbourhood $U(\varphi(t_0))$ and an open interval $I(t_0)$ on which orientations propagate; using the compactness of $[0, 1]$ and a finite covering, $o_0$ is transported to $o_1$; "by a covering argument" $\varphi_*$ depends only on $[\varphi]$, and the uniqueness of $\Gamma_f$ is called obvious.

**Proved in Lean.** `LocalTransport`: local data (good open sets covering $X_\infty$ and push-forwards along paths in a good set, compatible with concatenation and independent of the good set; `LocalTransport.push_eq_refl`, `LocalTransport.push_eq_push`, `LocalTransport.push_congr`). `LocalTransport.transportN`: the composite of the push-forwards along the $2^N$ dyadic pieces of a path (`vSeg`, `hSeg`, `dSeg`), the same for every $N$ at which every piece lies in a good set (`LocalTransport.IsFine`, `LocalTransport.transportN_eq_of_isFine`); such $N$ exist by the Lebesgue number lemma (`LocalTransport.exists_isLebesgueNumber`). `LocalTransport.transport` is the push-forward on a path in a good set (`LocalTransport.transport_eq_push`), homotopy invariant (`LocalTransport.transport_eq_of_isScHomotopyRel`, on dyadic squares: `LocalTransport.transportN_square`, `equiv_paste_squares`), compatible with concatenation and reparametrization, the identity on constant paths, and the only family with these properties (`LocalTransport.transport_unique`).

- `Polyfold.LocalTransport` — Polyfold/Chapter6/PathTransport.lean, line 93
- `Polyfold.LocalTransport.push_eq_refl` — Polyfold/Chapter6/PathTransport.lean, line 133
- `Polyfold.LocalTransport.push_eq_push` — Polyfold/Chapter6/PathTransport.lean, line 145
- `Polyfold.LocalTransport.push_congr` — Polyfold/Chapter6/PathTransport.lean, line 159
- `Polyfold.LocalTransport.transportN` — Polyfold/Chapter6/PathTransport.lean, line 176
- `Polyfold.LocalTransport.transportN_eq_push` — Polyfold/Chapter6/PathTransport.lean, line 224
- `Polyfold.LocalTransport.IsFine` — Polyfold/Chapter6/PathTransport.lean, line 344
- `Polyfold.LocalTransport.transportN_eq_of_isFine` — Polyfold/Chapter6/PathTransport.lean, line 350
- `Polyfold.LocalTransport.IsLebesgueNumber` — Polyfold/Chapter6/PathTransport.lean, line 292
- `Polyfold.LocalTransport.exists_isLebesgueNumber` — Polyfold/Chapter6/PathTransport.lean, line 326
- `Polyfold.LocalTransport.isFine_of_isLebesgueNumber` — Polyfold/Chapter6/PathTransport.lean, line 368
- `Polyfold.LocalTransport.transport` — Polyfold/Chapter6/PathTransport.lean, line 400
- `Polyfold.LocalTransport.transport_eq_push` — Polyfold/Chapter6/PathTransport.lean, line 428
- `Polyfold.LocalTransport.transport_congr` — Polyfold/Chapter6/PathTransport.lean, line 442
- `Polyfold.LocalTransport.transport_const` — Polyfold/Chapter6/PathTransport.lean, line 436
- `Polyfold.LocalTransport.transport_halves` — Polyfold/Chapter6/PathTransport.lean, line 452
- `Polyfold.LocalTransport.transportN_square` — Polyfold/Chapter6/PathTransport.lean, line 662
- `Polyfold.LocalTransport.exists_isSqLebesgueNumber` — Polyfold/Chapter6/PathTransport.lean, line 612
- `Polyfold.LocalTransport.transport_eq_of_isScHomotopyRel` — Polyfold/Chapter6/PathTransport.lean, line 732
- `Polyfold.LocalTransport.transport_reparam` — Polyfold/Chapter6/PathTransport.lean, line 783
- `Polyfold.LocalTransport.transport_concatPath` — Polyfold/Chapter6/PathTransport.lean, line 795
- `Polyfold.LocalTransport.transport_unique` — Polyfold/Chapter6/PathTransport.lean, line 835
- `Polyfold.equiv_paste_squares` — Polyfold/Chapter6/PathTransport.lean, line 575
- `Polyfold.vSeg` — Polyfold/Chapter6/PathTransport.lean, line 476
- `Polyfold.hSeg` — Polyfold/Chapter6/PathTransport.lean, line 480
- `Polyfold.dSeg` — Polyfold/Chapter6/PathTransport.lean, line 484

*What differs.*
- Dyadic subdivisions of $[0, 1]$ and of $[0, 1]^2$ in place of arbitrary finite coverings (Findings, Chapter 6, item 72).

### V6.57. Theorem 6.37: the functor $\Gamma_f$

*restated* · (∗) on every propagation set · $\mathcal O_f$: types and bijections · unique on morphisms

**HWZ (§6.5, Theorem 6.37 and its proof, p. 228).** For a strong bundle over a tame $X$ and an sc-Fredholm $f$ there is a uniquely determined functor $\Gamma_f : PX \to \mathcal O_f$, $x \mapsto \mathrm{Or}^f_x$, $[\varphi] \mapsto \Gamma_f([\varphi]) : \mathrm{Or}^f_x \to \mathrm{Or}^f_y$, with property (∗): for every sc-smoothly contractible open $U(x)$ on which $f$ has the local propagation property, $\varphi_* = \Gamma_f([\varphi])$ for every sc-smooth path $\varphi$ in $U$.

**Proved in Lean.** `theorem_6_37` ($X$ tame, bump functions, $f$ with tame germ data, $P$ with sc⁺-sections through the smooth fibre points): there is exactly one family of bijections $\Gamma_f([\varphi]) : \mathrm{Or}^f_x \to \mathrm{Or}^f_y$ on the morphisms of $PX$ that takes identities to identities and compositions to composites and has (∗) (`IsStarProperty`, `IsStarPropertyOn`): for every chart $c$, every open $U$ with the local propagation property in $c$ (`IsPropagationNbhd`) and every sc-smooth path $\varphi$ in $U$, $\Gamma_f([\varphi])$ is every push-forward along $\varphi$ in $c$ (`orPush`), read through $\mathrm{Or}^f$ of the chosen charts. `orFunctor`: the functor $PX \to$ Type, $x \mapsto \mathrm{Or}^f_x$ (`orFunctorMap`, `orFunctorMap_id`, `orFunctorMap_comp`); the uniqueness needs (∗) only on a family of such open sets covering $X_\infty$ (`orFunctorMap_unique_of_cover`).

- `Polyfold.IsPropagationNbhd` — Polyfold/Chapter6/OrientationFunctor.lean, line 281
- `Polyfold.orPush` — Polyfold/Chapter6/OrientationFunctor.lean, line 287
- `Polyfold.orPush_eq` — Polyfold/Chapter6/OrientationFunctor.lean, line 306
- `Polyfold.orPush_compat` — Polyfold/Chapter6/OrientationFunctor.lean, line 332
- `Polyfold.orPush_trans` — Polyfold/Chapter6/OrientationFunctor.lean, line 348
- `Polyfold.IsStarPropertyOn` — Polyfold/Chapter6/OrientationFunctor.lean, line 380
- `Polyfold.IsStarProperty` — Polyfold/Chapter6/OrientationFunctor.lean, line 397
- `Polyfold.orLocalTransport` — Polyfold/Chapter6/OrientationFunctor.lean, line 418
- `Polyfold.orLocalTransport_transport_eq` — Polyfold/Chapter6/OrientationFunctor.lean, line 438
- `Polyfold.LocalTransport.restrict` — Polyfold/Chapter6/OrientationFunctor.lean, line 186
- `Polyfold.LocalTransport.transport_apply_eq_of_local` — Polyfold/Chapter6/OrientationFunctor.lean, line 205
- `Polyfold.orFunctorMap` — Polyfold/Chapter6/OrientationFunctor.lean, line 458
- `Polyfold.orFunctorMap_mk` — Polyfold/Chapter6/OrientationFunctor.lean, line 470
- `Polyfold.orFunctorMap_id` — Polyfold/Chapter6/OrientationFunctor.lean, line 477
- `Polyfold.orFunctorMap_comp` — Polyfold/Chapter6/OrientationFunctor.lean, line 482
- `Polyfold.orFunctor` — Polyfold/Chapter6/OrientationFunctor.lean, line 492
- `Polyfold.orFunctorMap_isStarProperty` — Polyfold/Chapter6/OrientationFunctor.lean, line 514
- `Polyfold.orFunctorMap_unique_of_cover` — Polyfold/Chapter6/OrientationFunctor.lean, line 525
- `Polyfold.orFunctorMap_unique` — Polyfold/Chapter6/OrientationFunctor.lean, line 596
- `Polyfold.theorem_6_37` — Polyfold/Chapter6/OrientationFunctor.lean, line 611

*What differs.*
- (∗) is asked for every open set with the local propagation property, not only for sc-smoothly contractible ones (gap G.61); $\mathcal O_f$ is read as types and bijections; "uniquely determined" is read for the maps on morphisms, since on objects there is no choice (Findings, Chapter 6, item 72).
- The hypotheses are the standing ones of Theorem 6.35 and sc⁺-sections through every smooth fibre point, so that every $\mathrm{Or}^f_x$ has two elements; bump functions give them (Findings, Chapter 6, item 72).

### V6.58. Definition 6.38: orientable sections

*restated* · path component via sc-smooth paths

**HWZ (§6.5, Definition 6.38, p. 229).** An sc-Fredholm section $f$ over a tame $X$ is orientable if, for any two smooth points $x$, $y$ in the same path component, $\Gamma_f([\varphi])$ does not depend on the class $[\varphi] : x \to y$.

**Proved in Lean.** `IsOrientableSection`: $\Gamma_f([\varphi]) = \Gamma_f([\psi])$ for any two morphisms $x \to y$ of $PX$ (classes for `scPathSetoid`); `isOrientableSection_iff_exists`: equivalently, there is $y \mapsto o_y$ with $\Gamma_f([\varphi])o_x = o_y$ for every $[\varphi] : x \to y$.

- `Polyfold.scPathSetoid` — Polyfold/Chapter6/OrientationFunctor.lean, line 243
- `Polyfold.IsOrientableSection` — Polyfold/Chapter6/OrientationFunctor.lean, line 629
- `Polyfold.isOrientableSection_iff_exists` — Polyfold/Chapter6/OrientationFunctor.lean, line 719

*What differs.*
- "Smooth points in the same path component" is read as smooth points joined by an sc-smooth path; for points not so joined there is nothing to check (gap G.56; Findings, Chapter 6, items 42, 73).

### V6.59. Definition 6.39 and its equivalence with Definition 6.38

*stronger* · the equivalence proved · $U_\infty$ read as $X_\infty$

**HWZ (§6.5, Definition 6.39, p. 229).** "An equivalent version": $f$ is orientable if there is a map $y \mapsto o_y$, $y \in U_\infty$, $o_y$ an orientation of $\mathrm{DET}(f, y)$, such that every smooth $x$ has an orientable neighbourhood $U(x)$ on which $y \mapsto o_y$ is one of the two continuous orientations.

**Proved in Lean.** `IsOrientableSection'`: a map $y \mapsto o_y$ on $X_\infty$ such that every smooth point has an orientable neighbourhood over which it is a continuous orientation; `isOrientableSection'_iff_exists`: this holds iff there is $y \mapsto o_y$ with $\Gamma_f([\varphi])o_x = o_y$ for all $[\varphi]$; `isOrientableSection_iff`: Definitions 6.38 and 6.39 are equivalent.

- `Polyfold.IsOrientableSection'` — Polyfold/Chapter6/SectionOrientation.lean, line 135
- `Polyfold.isOrientableSection'_iff_exists` — Polyfold/Chapter6/OrientationFunctor.lean, line 731
- `Polyfold.isOrientableSection_iff` — Polyfold/Chapter6/OrientationFunctor.lean, line 742

*What differs.*
- The equivalence, stated without proof, is proved: from 6.39 to 6.38 the transport along a path is computed on dyadic pieces inside orientable neighbourhoods (`LocalTransport.transport_apply_eq_of_local`); from 6.38 to 6.39 a base point is chosen in each class of points joined by sc-smooth paths (Findings, Chapter 6, item 73).
- "$y \in U_\infty$", before any $U$ is introduced, is read as $y \in X_\infty$ (possible misprint) (Findings, Chapter 6, item 74).

### V6.60. Definition 6.40: orientations of sc-Fredholm sections

*restated* · orientable nbhd: the pair of V6.50

**HWZ (§6.5, Definition 6.40, p. 229).** An orientation of $f$ assigns to every smooth $y$ an orientation $o^f_y$ of $\mathrm{DET}(f, y)$ such that, for every smooth $x$ and every orientable neighbourhood $U(x)$, the restriction to $U_\infty$ is one of the two continuous orientations.

**Proved in Lean.** `IsSectionOrientation`: a map $y \mapsto o_y$ on $X_\infty$ whose restriction to every orientable neighbourhood of every smooth point is a continuous orientation; equivalently $\Gamma_f([\varphi])o_x = o_y$ for all $[\varphi] : x \to y$ (`isSectionOrientation_iff`). $f$ has an orientation iff it is orientable (`exists_isSectionOrientation_iff`); two orientations that agree at a point agree on the smooth points joined to it by sc-smooth paths (`IsSectionOrientation.apply_eq_iff`), and there are exactly two on each such class (`IsSectionOrientation.exists_two`).

- `Polyfold.IsSectionOrientation` — Polyfold/Chapter6/SectionOrientation.lean, line 144
- `Polyfold.isSectionOrientation_iff` — Polyfold/Chapter6/OrientationFunctor.lean, line 749
- `Polyfold.exists_isSectionOrientation_iff` — Polyfold/Chapter6/OrientationFunctor.lean, line 760
- `Polyfold.IsSectionOrientation.apply_eq_iff` — Polyfold/Chapter6/OrientationFunctor.lean, line 768
- `Polyfold.IsSectionOrientation.exists_two` — Polyfold/Chapter6/OrientationFunctor.lean, line 781

*What differs.*
- An orientable neighbourhood is the pair $V \subseteq U$ of V6.50 (Findings, Chapter 6, items 54, 75).

### V6.61. Theorem 6.41: the natural orientation of the solution set

*narrower* · orientation along paths of zeros · on $S$ as a manifold: gap G.67 · two charts: gap G.68 · perturbation paragraph: gap G.69

**HWZ (§6.5, Theorem 6.41 and its proof, p. 229; the paragraph after it, pp. 229–230).** Over a tame $X$, for a proper sc-Fredholm section $f$ with $(f, x)$ in general position to $\partial X$ at every zero and an orientation $o^f$ of $f$, the solution set $S = f^{-1}(0)$ is a smooth compact manifold with boundary with corners with a natural orientation. Proof: $T_xS = \ker f'(x)$ is oriented by $o^f_x$ since $f'(x)$ is onto, and the local prolongation of this orientation on $S$ is the Fredholm one. For $f$ not generic, a small perturbation $s$ supported near the zero set orients $S_{f+s}$.

**Proved in Lean.** `theorem_6_41_solutionSet` ($X$ tame, $f$ with tame germ data, `StrongBundle.IsProper`, general position (Definition 5.17) at every zero): $S$ is compact, a smooth submanifold in general position with the induced structure of a tame manifold with boundary with corners (the conclusions of Theorem 5.18; Lemma 4.19 for good position, `MPolyfold.IsGeneralPositionAt.isGoodPositionAt`), and $T_xS = \ker f'(x)$ in a chart (`tangentSpace_solutionSet_eq_linKer`). At a zero, $f'(x)$ (`ChartPoint.linZero`) lies in $\mathrm{Lin}(f, x)$ and is onto (`ChartPoint.linZero_mem_linSet`, `ChartPoint.linZero_surjective`, `ChartPoint.map_ker_linZero`), so $o_x \in \mathrm{Or}^f_x$ gives a ray of $\det f'(x) \cong \lambda(\ker f'(x)) = \lambda(T_xS)$, the tangent orientation (`ChartPoint.tangentOr`, `tangentOrAt`). `theorem_6_41`: moreover, for an orientation $o$ of $f$ (Definition 6.40) and every sc-smooth path $\gamma$ of zeros in an orientable neighbourhood $V \subseteq U$, the kernels $\ker f'(\gamma_q)$ form a continuous family of subspaces (`tangentFamily`, `exists_tangentFamily`), and the tangent orientations of $o$ form an orientation of its line bundle (`isLineOrientation_tangentOr`, `isLineOrientation_tangentOr_of_isSectionOrientation`). The Fredholm side is the push-forward for the datum $S = 0$, $k = 0$ (`isStabKernels_zero`, `stabSign_of_surjective`, `stabRayEquiv_zero`), which along a path of zeros is the continuation between tangent orientations (`IsStabKernels.orRay_eq_tangentOr`, `ChartPoint.stabRayEquiv_eq_tangentOr`, `cont_tangentOr`).

- `Polyfold.theorem_6_41_solutionSet` — Polyfold/Chapter6/SolutionOrientation.lean, line 305
- `Polyfold.MPolyfold.IsGeneralPositionAt.isGoodPositionAt` — Polyfold/Chapter6/SolutionOrientation.lean, line 267
- `Polyfold.tangentSpace_solutionSet_eq_linKer` — Polyfold/Chapter6/SolutionOrientation.lean, line 335
- `Polyfold.ChartPoint.linZero` — Polyfold/Chapter6/SolutionOrientation.lean, line 367
- `Polyfold.ChartPoint.linZero_mem_linSet` — Polyfold/Chapter6/SolutionOrientation.lean, line 377
- `Polyfold.ChartPoint.linZero_surjective` — Polyfold/Chapter6/SolutionOrientation.lean, line 386
- `Polyfold.ChartPoint.map_ker_linZero` — Polyfold/Chapter6/SolutionOrientation.lean, line 397
- `Polyfold.ChartPoint.tangentOr` — Polyfold/Chapter6/SolutionOrientation.lean, line 414
- `Polyfold.tangentOrAt` — Polyfold/Chapter6/SolutionOrientation.lean, line 707
- `Polyfold.stabSign_of_surjective` — Polyfold/Chapter6/SolutionOrientation.lean, line 114
- `Polyfold.stabRayEquiv_zero` — Polyfold/Chapter6/SolutionOrientation.lean, line 200
- `Polyfold.ChartPoint.stabRayEquiv_eq_tangentOr` — Polyfold/Chapter6/SolutionOrientation.lean, line 489
- `Polyfold.IsStabKernels.orRay_eq_tangentOr` — Polyfold/Chapter6/SolutionOrientation.lean, line 521
- `Polyfold.isStabKernels_zero` — Polyfold/Chapter6/SolutionOrientation.lean, line 624
- `Polyfold.SubspaceFamily.congrL` — Polyfold/Chapter6/SolutionOrientation.lean, line 432
- `Polyfold.exists_tangentFamily` — Polyfold/Chapter6/SolutionOrientation.lean, line 563
- `Polyfold.tangentFamily` — Polyfold/Chapter6/SolutionOrientation.lean, line 590
- `Polyfold.tangentFamily_L` — Polyfold/Chapter6/SolutionOrientation.lean, line 600
- `Polyfold.cont_tangentOr` — Polyfold/Chapter6/SolutionOrientation.lean, line 723
- `Polyfold.isLineOrientation_tangentOr` — Polyfold/Chapter6/SolutionOrientation.lean, line 802
- `Polyfold.isLineOrientation_tangentOr_of_isSectionOrientation` — Polyfold/Chapter6/SolutionOrientation.lean, line 865
- `Polyfold.theorem_6_41` — Polyfold/Chapter6/SolutionOrientation.lean, line 892

*What differs.*
- "A natural orientation" is read as the tangent orientations with their continuity along the sc-smooth paths of zeros in a chart, and "the local prolongation of the orientation on $S$ is the Fredholm one" as the identity of continuation and push-forward along such paths; intermediate points are reached by the paths $s \mapsto \gamma(t\kappa(s))$, which stay in $\gamma([0, t])$ (Findings, Chapter 6, item 91).
- Not formalized: an orientation of $S$ as an abstract manifold, of its tangent bundle in the charts of the induced structure (gap G.67), the compatibility of the tangent orientations read in two charts at one zero (gap G.68), and the perturbation paragraph after the theorem, with $S_{f+s}$ and $\mathrm{Lin}(f + s, x) = \mathrm{Lin}(f, x)$ (gap G.69) (Findings, Chapter 6, items 92, 93).
- Tame germ data is the standing hypothesis of Chapter 5; the orientation $o$ exists iff $f$ is orientable (V6.60). "Proper" is the text's hypothesis; the proof uses only the compactness of $S$, which for sc-Fredholm sections is equivalent to it (V5.10), so nothing of the hypothesis is lost (Findings, Chapter 6, item 90).

### V6.62. Remark 6.42: the orientation over $X \times [0, 1]$, at a point

*narrower* · at a point · sign $(-1)^{\dim\operatorname{coker}L}$ · $X \times [0, 1]$ as $\mathbb R \times X$

**HWZ (§6.5, Remark 6.42, p. 230).** For an oriented $(f, o)$ and an sc⁺-section $s$ of $Y \to X \times [0, 1]$, $\hat f(x, t) = f(x) + s(x, t)$ has a natural orientation from $o$ and the standard orientation of $[0, 1]$: for $L = (f - t)'(x)$ oriented by $h = (a_1 \wedge \dots \wedge a_n) \otimes (b_1 \wedge \dots \wedge b_l)^*$, the operator $\tilde L(a, b) = La$ on $T_{(x,t)}(X \times [0, 1])$ is oriented by $\tilde h = (a_1 \wedge \dots \wedge a_n \wedge e) \otimes (b_1 \wedge \dots \wedge b_l)^*$, $e$ the standard orientation of $[0, 1]$, and $\tilde L$ lies in the linearization space of $\hat f$ at $(x, t)$.

**Proved in Lean.** `extOp`: for Fredholm $L$, $\tilde L = L \oplus 0 : E \times \mathbb R \to F$ is Fredholm (`isFredholm_extOp`) with $\ker\tilde L = \ker L \times \mathbb R$ and $\operatorname{coker}\tilde L = \operatorname{coker}L$ (`finrank_ker_extOp`, `extE`, `range_extOp`, `extCoker`). `extDet`: $h \mapsto \tilde h$, $(a_1 \wedge \dots \wedge a_n) \otimes d^* \mapsto ((a_1, 0) \wedge \dots \wedge (a_n, 0) \wedge e) \otimes d^*$ with $e = (0, 1)$, an isomorphism $\det(L) \cong \det(\tilde L)$ (`extDet_wedge_tmul`); in local determinant charts its coordinate is $(-1)^{\dim F/R(P) + \dim\operatorname{coker}L}$ times a continuous nowhere-zero function (`coord_extDet`). `extDetN` $= (-1)^{\dim\operatorname{coker}L}$ `extDet` pulls continuous orientations back along $L \mapsto \tilde L$ (`coord_extDetN`, `isLineOrientation_extPull`, `LineOrientation.extPull`) and agrees with `extDet` for $L$ onto (`extDetN_eq_of_surjective`); `extConjOp`, `extConjDet`, `existsUnique_extConjOr`: the same after the swap of the factors. In charts: for $\hat f = \tilde f + S$, $\tilde f(t, y) = f(y)$, $S$ an sc⁺-section of $\pi^*P \to \mathbb R \times X$, and the product chart point (`ChartPoint.prodPt`, `ChartPoint.prodT`, `ChartPoint.prodK`), $\hat L(\sigma, v) = Lv$ (`ChartPoint.prodLin`) lies in $\mathrm{Lin}(\hat f, (t, x))$ for every $L \in \mathrm{Lin}(f, x)$ (`ChartPoint.prodLin_mem_linSet`, through the $t$-constant lift `constLift`); an orientation $o$ of $\mathrm{DET}(f, x)$ gives exactly one orientation $\hat o$ of $\mathrm{DET}(\hat f, (t, x))$ with $\hat o(\hat L)$ the image of $o(L)$ for **every** $L$ (`ChartPoint.existsUnique_prodOr`, `ChartPoint.prodOr`, `ChartPoint.prodOr_apply`), and $o \mapsto \hat o$ is injective (`ChartPoint.prodOr_injective`).

- `Polyfold.extOp` — Polyfold/Chapter6/ProductOrientation.lean, line 99
- `Polyfold.isFredholm_extOp` — Polyfold/Chapter6/ProductOrientation.lean, line 160
- `Polyfold.finrank_ker_extOp` — Polyfold/Chapter6/ProductOrientation.lean, line 136
- `Polyfold.extE` — Polyfold/Chapter6/ProductOrientation.lean, line 113
- `Polyfold.range_extOp` — Polyfold/Chapter6/ProductOrientation.lean, line 150
- `Polyfold.extCoker` — Polyfold/Chapter6/ProductOrientation.lean, line 197
- `Polyfold.extDet` — Polyfold/Chapter6/ProductOrientation.lean, line 204
- `Polyfold.extDet_wedge_tmul` — Polyfold/Chapter6/ProductOrientation.lean, line 210
- `Polyfold.extDetN` — Polyfold/Chapter6/ProductOrientation.lean, line 225
- `Polyfold.extDetN_eq_of_surjective` — Polyfold/Chapter6/ProductOrientation.lean, line 238
- `Polyfold.coord_extDet` — Polyfold/Chapter6/ProductOrientation.lean, line 420
- `Polyfold.coord_extDetN` — Polyfold/Chapter6/ProductOrientation.lean, line 471
- `Polyfold.isLineOrientation_extPull` — Polyfold/Chapter6/ProductOrientation.lean, line 548
- `Polyfold.LineOrientation.extPull` — Polyfold/Chapter6/ProductOrientation.lean, line 660
- `Polyfold.extConjOp` — Polyfold/Chapter6/ProductOrientation.lean, line 733
- `Polyfold.extConjDet` — Polyfold/Chapter6/ProductOrientation.lean, line 744
- `Polyfold.existsUnique_extConjOr` — Polyfold/Chapter6/ProductOrientation.lean, line 792
- `Polyfold.ChartPoint.prodPt` — Polyfold/Chapter6/ProductOrientation.lean, line 848
- `Polyfold.ChartPoint.mem_prodPt_T_iff` — Polyfold/Chapter6/ProductOrientation.lean, line 862
- `Polyfold.ChartPoint.mem_prodPt_K_iff` — Polyfold/Chapter6/ProductOrientation.lean, line 867
- `Polyfold.ChartPoint.prodT` — Polyfold/Chapter6/ProductOrientation.lean, line 882
- `Polyfold.ChartPoint.prodK` — Polyfold/Chapter6/ProductOrientation.lean, line 907
- `Polyfold.ChartPoint.prodLin` — Polyfold/Chapter6/ProductOrientation.lean, line 923
- `Polyfold.ChartPoint.IsScPlusOp.prodPt` — Polyfold/Chapter6/ProductOrientation.lean, line 941
- `Polyfold.constLift` — Polyfold/Chapter6/ProductOrientation.lean, line 985
- `Polyfold.ChartPoint.prodLin_mem_linSet` — Polyfold/Chapter6/ProductOrientation.lean, line 1052
- `Polyfold.ChartPoint.existsUnique_prodOr` — Polyfold/Chapter6/ProductOrientation.lean, line 1136
- `Polyfold.ChartPoint.prodOr` — Polyfold/Chapter6/ProductOrientation.lean, line 1165
- `Polyfold.ChartPoint.prodOr_apply` — Polyfold/Chapter6/ProductOrientation.lean, line 1174
- `Polyfold.ChartPoint.prodOr_injective` — Polyfold/Chapter6/ProductOrientation.lean, line 1188

*What differs.*
- As we read it, the literal $h \mapsto \tilde h$ is not continuous in $L$ where the parity of $\dim\operatorname{coker}L$ changes, so the orientation of $\mathrm{DET}(\hat f, (x, t))$ it defines could depend on the choice of $L$; the sign $(-1)^{\dim\operatorname{coker}L}$ (the sign of V6.40) is used, which agrees with the text's map when $L$ is onto (Findings, Chapter 6, item 95).
- $X \times [0, 1]$ is read as $\mathbb R \times X$ (decision D2), with the parameter first, so $\tilde L(a, b) = La$ is conjugated by the swap of the factors. Only an orientation of $\mathrm{DET}(f, x)$ at the one point and $\mathrm{Lin}(f, x) \ne \emptyset$ (bump functions, V6.1) are used, not an orientation of $f$ (Findings, Chapter 6, item 96).
- That $(t, y) \mapsto \hat o$ is an orientation of $\hat f$ in the sense of Definition 6.40, built from an orientation of $f$, is not formalized (gap G.66; Findings, Chapter 6, item 97).

### V6.63. §6.7.1: the proof of Lemma 6.5

*restated* · homogeneity in the bases of $A$, $D$

**HWZ (§6.7.1, pp. 234–235).** With complements $(V, W)$, a change of the basis of $V$ by $\sigma$ multiplies both wedges of (91) by $\det(\sigma)$, so has no influence. A change of the bases of $A$ and $D$ multiplies $a \otimes d^*$ by $\det(\tau)/\det(\varepsilon)$, and the vector is said to be independent of the bases iff $\det(\tau) = \det(\varepsilon)$. For two choices of complements, the new basis vectors differ from the old by $q_i \in \alpha(A)$ and $p_i \in \beta(C)$, which leaves the wedges unchanged.

**Proved in Lean.** `FourTermExact.Choice.exists_smul_source_value`: for two choices of (91) the right-hand sides are related as the sources are. A change of the basis of $Z$ multiplies both wedges by its determinant, a change of the bases of $A$ and $D$ multiplies both sides by the same factor, and a change of complements adds to the basis of $Z$ vectors of $\alpha(A)$ and to the $\gamma$-preimages vectors of $\beta(B)$ (`FourTermExact.Choice.wedgeC`), which leaves the wedges unchanged.

- `Polyfold.FourTermExact.Choice.exists_smul_source_value` — Polyfold/Chapter6/ExactSequence.lean, line 284
- `Polyfold.FourTermExact.Choice.wedgeC` — Polyfold/Chapter6/ExactSequence.lean, line 215

*What differs.*
- The step "if and only if $\det(\tau) = \det(\varepsilon)$" is read as the homogeneity of (91) in the bases of $A$ and $D$, both sides scaling by $\det(\sigma)/\det(\varepsilon)$, $\tau$ being the $\sigma$ just introduced (possible misprint). The corrections $p_i$ lie in $\beta(B)$ (written $\beta(C)$) and are combinations of the $\beta$-images, whose names are exchanged with those of the $\gamma$-preimages in the last step (possible misprints) (Findings, Chapter 6, item 1).

### V6.64. §6.7.2: the proof of Proposition 6.12

*restated* · spanning proved directly in $F$

**HWZ (§6.7.2, pp. 235–237).** With $d_i \in R(I - Q)$, bases $a, b$ of $\ker(QT)$ and $a, b, \tilde b$ of $\ker(PT)$, the text computes $\gamma^P_{QT}(\gamma^Q_T(h)) = \alpha^P \otimes (\beta^P)^*$, splits $F/R(P) = \ker\tilde Q \oplus \ker(I - \tilde Q)$, replaces $[QT(\tilde b_i)]$ by $[T(\tilde b_i)]$ in the wedge, and finds the same vector for $\gamma^P_T(h)$.

**Proved in Lean.** `mem_span_append_of_ker`: if $Qg = 0$, then $g$ is a combination of the $d_i$ plus $Tx$ with $x \in \ker(QT)$, so the classes of the $d_i$ and $Tb_j$ span what the text calls $\ker\tilde Q$; the classes $[T\tilde b]$ and $[QT\tilde b]$ in $F/R(P)$ differ by elements of that span, which does not change the wedge. With `gammaProj_wedge_tmul` and `comp_comp_eq_of_projLE` this gives Proposition 6.12 (V6.14).

- `Polyfold.mem_span_append_of_ker` — Polyfold/Chapter6/ProjectionSequence.lean, line 267
- `Polyfold.gammaProj_wedge_tmul` — Polyfold/Chapter6/ProjectionSequence.lean, line 221
- `Polyfold.comp_comp_eq_of_projLE` — Polyfold/Chapter6/ProjectionSequence.lean, line 253

*What differs.*
- The spanning step is proved directly in $F$; the name $\alpha_q$ in the last part is read as $\alpha^P$ (possible misprint) (Findings, Chapter 6, items 6, 7).

## Not formalized

*What the book states and the formalization does not prove, and what it does instead; an entry proved since the first edition of this page keeps its number and is marked “formalized since”*

### G.1. Example 1.2: the weighted Sobolev spaces $H^{m,\delta_m}(\mathbb R \times S^1)$

*not formalized*

**HWZ (§1.1, Example 1.2, pp. 6–7).** With $0 = \delta_0 < \delta_1 < \cdots$, the spaces $E_m = H^{m,\delta_m}(\mathbb R \times S^1)$ of $L^2$ functions whose weak derivatives up to order $m$, weighted by $e^{\delta_m|s|}$, are in $L^2$ form an sc-structure on $L^2(\mathbb R \times S^1)$, "using Sobolev's compact embedding theorem for bounded domains and the assumption that $(\delta_m)$ is strictly increasing".

**Proved in Lean.** **Not formalized.** Mathlib has no weighted Sobolev spaces and no Rellich–Kondrachov theorem; the exposition proves the example in full (Proposition 1.C). The only examples of sc-Banach spaces built here are the constant structure on a finite-dimensional space, and the sums, shifts, sc-subspaces and quotients of sc-Banach spaces (V1.1, V1.4, V1.6). This example, with the shift map of the 2010 paper, is the project's planned step H2.


### G.2. Remark 1.15: partial cones in place of partial quadrants

*not formalized*

**HWZ (§1.1, Remark 1.15, p. 11).** Instead of a partial quadrant $C$ one may take a closed convex partial cone $P$ ($\lambda P \subset P$ for $\lambda \ge 0$) with non-empty interior; for $U$ open in $P$, $\mathrm{sc}^1$ is defined as in Definition 1.14, with the tangent map on $TP = P^1 \oplus E$, again a closed cone with non-empty interior. Many results should carry over, "but one should check carefully which arguments carry over".

**Proved in Lean.** **Not formalized**, as in the exposition, which stays with quadrants. The proofs of §§1.2–1.3 use of the quadrant only the sc-domain property (V1.27: open-in-convex level sets with unique derivatives), so they apply to any $U$ with that property; whether relatively open subsets of partial cones have it is not examined. (Propositions 1.19 and 1.20 under the text's hypothesis, listed here until 2026-10-25, are now proved as stated, V1.18–V1.19.)


### G.3. Definition 1.14: $Df$ need not be norm continuous

*formalized since* · now V1.13 · now V1.34

**HWZ (§1.1, after Definition 1.14, p. 11).** "In general, the map $U_1 \to \mathcal L(E_0, F_0)$, defined by $x \mapsto Df(x)$, will not(!) be continuous, if the space of bounded linear operators is equipped with the operator norm."

**Proved in Lean.** **Formalized since the first edition of this page** (third addendum; V1.13, V1.34), by an example (the text gives none). $X$ is the sc-Banach space of sequences whose level $m$ consists of the $x$ with $(k+1)^m x_k \to 0$, normed by $|x|_m = \sup_k (k+1)^m|x_k|$: every level is a copy of $c_0$, the inclusion $X_{m+1} \to X_m$ is $\mathrm{diag}(1/(k+1))$, compact, and the finitely supported sequences are smooth points dense in every level. On $E = \mathbb R \oplus X$ the map $f(t, x)_k = \cos(kt)x_k$ is $\mathrm{sc}^1$ with $Df(t, x)(\tau, \xi)_k = -k\sin(kt)x_k\tau + \cos(kt)\xi_k$ (the factor $k$ is absorbed by one level). $(\pi/(n+1), 0) \to 0$ in $E_1$, but $\|Df(\pi/(n+1), 0) - Df(0, 0)\| \ge 2$ (test on the unit vector $e_{n+1}$); since the derivative is unique on $E_1$, no derivative family of $f$ is continuous for the operator norm. Not formalized: that $f$ is sc-smooth (it is), and the shift map of the exposition (§6), which needs Example 1.2 (G.1).

- `Polyfold.exists_isSc1_not_continuousOn_deriv` — Polyfold/Chapter1/ScOneNotNormContinuous.lean, line 690
- `Polyfold.ScOneExample.isSc1With` — Polyfold/Chapter1/ScOneNotNormContinuous.lean, line 587
- `Polyfold.ScOneExample.not_continuousAt_D` — Polyfold/Chapter1/ScOneNotNormContinuous.lean, line 648

### G.4. Proposition 2.2: classical smooth retractions have submanifold images

*not formalized*

**HWZ (§2.1, Proposition 2.2, p. 18 (proof §2.6.1, pp. 54–55)).** If $r : U \to U$ is a $C^\infty$ retraction of an open subset of a Banach space $E$, then $O = r(U)$ is a $C^\infty$ submanifold: near each $x \in O$ there are a splitting $E = R \oplus N$ and a diffeomorphism $\psi : V \to W$ with $\psi(O \cap V) = R \cap W$ (the text prints $\psi(0) = x$ for $\psi(x) = 0$).

**Proved in Lean.** **Not formalized.** The proposition is classical and is used only as motivation (the contrast with sc-smooth retractions, whose images can change dimension). The exposition proves it in §8.1 with the inverse function theorem; its Lean version would need Mathlib's inverse function theorem for $C^\infty$ maps between Banach spaces and the splitting by the projection $Dr(0)$. Not attempted.


### G.5. Definition 2.9: sc-smooth bundle retractions and bundle maps

*not formalized*

**HWZ (§2.1, Definition 2.9, p. 22).** A trivial sc-bundle $U \oplus F \to U$; an sc-smooth $R(u, v) = (r(u), \rho(u, v))$, $\rho$ linear in $v$, $R \circ R = R$, is an sc-smooth bundle retraction with bundle retract $B = R(U \oplus F) \to O$; bundle maps $\Phi(u, v) = (a(u), \phi(u, v))$ with \"$p' \circ \Phi = p$\" (read $a \circ p$); the category $\mathcal{BR}$ and the functor $T : \mathcal R \to \mathcal{BR}$.

**Proved in Lean.** **Not formalized as a definition.** The tangent retraction $Tr$ (V2.8) and the strong bundle retractions of §2.5 (V2.54) are the instances the theory uses; both are formalized as sc-smooth retractions of the stated form, with linearity in the fibre where it is needed. The categories $\mathcal R$, $\mathcal{BR}$, $\mathcal{SBR}$ and their functors are not formalized.


### G.6. $X_m$ as an M-polyfold for $m \ge 2$

*not formalized*

**HWZ (§2.2, after Definition 2.14, p. 25).** For every $m$, the charts $(V_m, \varphi, (O_m, C_m, E_m))$ form an atlas on $X_m$.

**Proved in Lean.** **Proved for $m = 1$** (V2.16). For $m \ge 2$ the structure is the iterate $(X^1)^1 \cdots$, whose underlying space is the level of a level. Since the fourth addendum its points are known to be those of $X_m$: $(X^1)_m = X_{m+1}$ and $(X^1)_\infty = X_\infty$ as sets, and an sc-smooth map $X \to Z$ induces an sc-smooth map $X^1 \to Z^1$; that the topology of $(X^1)_m$ is that of $X_{m+1}$ (V2.14), and so that the iterate is $X_m$ with its charts, is not formalized (Findings, Chapter 5, items 142, 146). Theorem 2.16 is proved for every $X_m$ directly (V2.17).

- `Polyfold.MPolyfold.mem_shift_levelSet_iff` — Polyfold/Chapter5/StrongBundleShift.lean, line 304
- `Polyfold.MPolyfold.mem_shift_smoothSet_iff` — Polyfold/Chapter5/StrongBundleShift.lean, line 313
- `Polyfold.MPolyfold.IsScSmoothMap.levelOne` — Polyfold/Chapter5/StrongBundleShift.lean, line 367

### G.7. Definition 2.18: the linear structure of $T_xX$; Proposition 2.21 (3) in $T_aX$

*not formalized*

**HWZ (§2.2, Definition 2.18 and Proposition 2.21 (3), (4), pp. 26–30).** $T_xX$ is a vector space with $\lambda[(x, \varphi, h_1)] + \mu[(x, \varphi, h_2)] = [(x, \varphi, \lambda h_1 + \mu h_2)]$, a Banach space through $T\varphi$, an sc-Banach space at smooth $x$; Proposition 2.21 (3): $T_aA$ has an sc-complement in $T_aX$.

**Proved in Lean.** **Not formalized.** $T_xX$ is a set identified with $T_{\varphi(x)}O$ by $T\varphi$ (V2.19); the vector space, Banach and sc-structures on it are not defined. Proposition 2.21 (3), (4) are proved in a chart (V2.25), which is how the text proves them; their transport to $T_aX$ is not.


### G.8. Proposition 2.19 (2): $p : TX \to X_1$ is open

*not formalized*

**HWZ (§2.2, Proposition 2.19 (2), p. 27).** The projection $p : TX \to X_1$ is an open map.

**Proved in Lean.** **Not formalized** (not used). Continuity of $p$ is V2.20. The exposition's §8.3 proves openness with the $\mathrm{sc}^0$ property of $Tr$.


### G.9. Remark 2.28: $C_xO$ need not be a partial quadrant

*formalized since* · now V2.33

**HWZ (§2.3, Remark 2.28, p. 33).** Naively one might expect $C_xO$ to be a partial quadrant in $T_xO$; \"however, this is in general not the case\".

**Proved in Lean.** **Settled since the first edition of this page, in the negative** (third addendum; V2.33): the claim is false. At every smooth point of every sc-smooth retract, tame or not, $C_xO$ is a partial quadrant in $T_xO$ (with the sc-structure induced from $E$), of dimension $\dim(T_xO/T^R_xO) \le d_C(x)$; the proof reduces it to Flor's theorem on nonnegative idempotent matrices, proved in the needed case. For a non-tame retract only the equality of that dimension with $d_C(x)$ can fail (Theorem 2.31). The text gives no example, and none exists (Findings, Chapter 2, item 50).

- `Polyfold.remark_2_28_isPartialQuadrant` — Polyfold/Chapter2/PartialConeQuadrant.lean, line 655
- `Polyfold.flor_nonnegRange_simplicial` — Polyfold/Chapter2/PartialConeQuadrant.lean, line 375

### G.10. Lemma 2.29: $T^R_xO$ and $C_xO$ through sc-smooth paths; $T_xO = C_xO - C_xO$

*not formalized*

**HWZ (§2.3, Lemma 2.29, pp. 33–35).** For a retract and a smooth $x \in O$: (1) $T^R_xO$ is the closure of the derivatives $\dot\alpha(0)$ of sc-smooth paths $\alpha : (-\varepsilon, \varepsilon) \to O$ through $x$; (2) $C_xO$ the closure of the one-sided derivatives of sc-smooth paths $\alpha : [0, \varepsilon) \to O$; (3) $T_xO = C_xO - C_xO$.

**Proved in Lean.** **Not formalized in the path formulation.** Sc-smooth paths would need the constant sc-structure on an interval as a retract and the density of smooth points of $T^R_xO$ and $C_xO$ (the exposition's Lemma 3.A on all levels). The sign arguments that the proof consists of are formalized (V2.34), and Proposition 2.30 is proved from them, not from the lemma. (3) is not formalized.


### G.11. Theorem 2.31, second statement: equality makes $C_xO$ a partial quadrant

*formalized since* · now V2.33 · now V2.37

**HWZ (§2.3, Theorem 2.31, p. 35 (second statement)).** If $\dim(T_xO/T^R_xO) = d_O(x)$, then $C_xO$ is a partial quadrant in $T_xO$.

**Proved in Lean.** **Formalized since the first edition of this page** (third addendum; V2.33, V2.37), without the hypothesis: $C_xO$ is a partial quadrant in $T_xO$ at every smooth point of every sc-smooth retract, whatever $\dim(T_xO/T^R_xO)$ is, and the quadrant has dimension $\dim(T_xO/T^R_xO)$, which is $d_O(x)$ under the hypothesis. The sc-Banach structure of $T_xO$ and $T^R_xO$ as an sc-subspace, which the exposition supplied on paper, are proved without tameness; the smooth lifts come from the columns given by Flor's theorem (V2.33).

- `Polyfold.remark_2_28_isPartialQuadrant` — Polyfold/Chapter2/PartialConeQuadrant.lean, line 655

### G.12. The extended faces of a partial quadrant, intrinsically

*not formalized*

**HWZ (§2.4, p. 39).** $\{e \in C : d_C(e) = 1\}$ has exactly $k$ connected components $A_i$; each lies in a smallest subspace $f_i$ (an extended face), with a half-space $H_{f_i} \supset C$; $\mathcal F(e) = \{f : e \in f\}$ and $d_C(e) = \#\mathcal F(e)$.

**Proved in Lean.** **Not formalized as stated.** The formalization works with a presentation $T$ of $C$ and takes the coordinate hyperplanes $f_i = \{\lambda_i = 0\}$ as the extended faces (`coordHyper`); that a connected piece of $\{d_C = 1\}$ lies in one $f_i$ is `subset_coordHyper_of_isPreconnected` (V2.45). That $E_x$ does not depend on the presentation is proved (`minimalSubspaceWith_eq`, V2.39); the count of components, the minimality of $f_i$ and the intrinsic description of the extended faces are not formalized.


### G.13. Definition 2.38: $T^R_xX$ and $C_xX$ of an M-polyfold

*not formalized*

**HWZ (§2.4, Definition 2.38, p. 42).** For a smooth $x \in X$, $T^R_xX$ and $C_xX$ are the preimages of $T^R_oO$ and $C_oO$ under $T\psi(x)$ for any chart $\psi$; well defined by Proposition 2.30. For tame $X$, $C_xX$ is a partial quadrant and $d_X(x) = \dim(T_xX/T^R_xX) = d_{C_xX}(0_x)$.

**Proved in Lean.** **Only the local form is formalized**: $T^R_xO$ and $C_xO$ in a chart (V2.32) and their invariance under chart changes (V2.35). The global objects in $T_xX$ are not defined, since $T_xX$ carries no linear structure here (G.7); in a tame chart, $d_X(x) = \dim(T_xO/T^R_xO)$ is V2.42. In a tame chart at a smooth point, $C_oO$ is a partial quadrant in $T_oO$ (V2.42); its transport to $T_xX$ and $d_{C_xX}(0_x) = d_X(x)$ are not formalized.


### G.14. Definition 2.47: strong bundle isomorphisms; the category $\mathcal{SBR}$

*not formalized*

**HWZ (§2.5, Definition 2.47 and after Definition 2.49, pp. 48–51).** A strong bundle isomorphism is an invertible strong bundle map with strong bundle inverse. The category $\mathcal{SBR}$ of local strong bundle retracts and the functors $\mathrm{forget}[i] : \mathcal{SBR} \to \mathcal{BR}$.

**Proved in Lean.** **Not formalized.** Strong bundle maps and retractions are V2.54; the transition maps of strong bundle charts are required to be sc-smooth on $[0]$ and $[1]$ in both directions (V2.57), which is the isomorphism property in the form it is used.


### G.15. Lemma 2.56 and Proposition 2.57: closed locally finite refinements

*not formalized*

**HWZ (§2.6.2, Lemma 2.56 and Proposition 2.57, p. 56).** Lemma 2.56 (Michael): a regular Hausdorff space is paracompact iff every open cover has a closed locally finite refinement. Proposition 2.57: a regular space with a locally finite cover by closed paracompact subspaces is paracompact.

**Proved in Lean.** **Not formalized, because not needed.** The proofs of Theorem 2.16 and Proposition 2.19(3) avoid them (V2.17, V2.20, V2.62). The text applies Proposition 2.57 to $X_m$ and $TX$ without checking that they are regular.


### G.16. Theorem 3.18: parameterized perturbations

*formalized since* · now V3.91 · now V3.92 · now V3.106

**HWZ (§3.1, Theorem 3.18, p. 74).** For a tame strong bundle and an sc-Fredholm section $f$, $s_1, \dots, s_n \in \Gamma^+(P)$: $(r, x) \mapsto f(x) + \sum r_is_i(x)$ is an sc-Fredholm section of $\pi^*(P) \to \mathbb R^n \times X$.

**Proved in Lean.** **Formalized since the first edition of this page** (V3.91, V3.92): $(r, x) \mapsto f(x) + \sum r_is_i(x)$ is an sc-Fredholm section of $\pi^*P$ for any strong bundle (tameness not used), by the text's route: $\tilde f$ is sc-Fredholm in the product chart through the translation charts of $\mathbb R^n$ and the $\mathbb R^n$-extension of the basic germ, $\tilde s$ is sc$^+$, and Theorem 3.15. The linearization at $(0, x)$ after Theorem 3.19 is V3.92; the form for germ data in tame charts is V3.106.

- `Polyfold.theorem_3_18` — Polyfold/Chapter3/ParamPerturbationG.lean, line 141
- `Polyfold.theorem_3_18'` — Polyfold/Chapter3/ParamPerturbationG.lean, line 152
- `Polyfold.StrongBundle.IsScFredholmSection.param` — Polyfold/Chapter3/ParamPerturbationG.lean, line 124
- `Polyfold.linAt_paramSection_zero` — Polyfold/Chapter3/ParamPerturbationG.lean, line 396
- `Polyfold.theorem_3_18_tame` — Polyfold/Chapter3/ParamPerturbationG.lean, line 209

### G.17. Theorem 3.19: implicit function theorem, interior case

*formalized since* · now V3.68 · now V3.95 · now V3.96 · now V3.97 · now V3.99 · now V3.101

**HWZ (§3.1, Theorem 3.19, p. 74).** For $d_X \equiv 0$, $f$ sc-Fredholm, $f(x_0) = 0$: $f'(x_0)$ is sc-Fredholm; if it is onto, the solution set near $x_0$ is a smooth manifold of dimension the index, with $f'(y)$ onto and $\ker f'(y) = T_yS$.

**Proved in Lean.** **Formalized since the first edition of this page.** First (V3.68) under the filler condition at the nearby zeros, which was the added hypothesis of Theorem 3.54 (1) (V3.82) and is now a theorem (V3.102); with the text's hypotheses (V3.95): for $d_X \equiv 0$, an sc-Fredholm section with tame germ data and $(f, x_0)$ in good position in a tame chart (V3.103), an open $U \ni x_0$ in which every zero is a smooth point in good position in a tame chart and $S(f, U)$ is a sub-M-polyfold equivalent to a $d$-dimensional manifold without boundary; with the hypothesis “$f'(x_0)$ surjective” (V3.101); the dimension is the Fredholm index (V3.97), $\ker f'(y) = T_yS$ in the chart (V3.99), and the first clause, “$f'(x_0)$ is sc-Fredholm”, is Proposition 3.52 in sc form, in the chart at $x_0$ and in every chart, with $f'(x_0)$ onto on every level (V3.46, V3.96; third addendum).

- `Polyfold.theorem_3_19` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 209
- `Polyfold.theorem_3_19_linearization` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 186
- `Polyfold.theorem_3_19'` — Polyfold/Chapter3/GlobalIFTNearbyOntoG.lean, line 650
- `Polyfold.theorem_3_19_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 595
- `Polyfold.theorem_3_19_of_surjective` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 615
- `Polyfold.theorem_3_19_linearization_sc` — Polyfold/Chapter3/FredholmGermLinearizationScG.lean, line 339

### G.18. Theorem 3.23 and Corollary 3.24: implicit function theorem, boundary case

*formalized since* · now V3.69 · now V3.70 · now V3.95 · now V3.97

**HWZ (§3.1, Theorem 3.23 and Corollary 3.24, pp. 77–78).** At a zero with surjective linearization whose kernel is in good position to $C_xX$, the local solution set consists of smooth points and is a tame sub-M-polyfold with a unique structure of a manifold with boundary with corners; globally if this holds at every zero.

**Proved in Lean.** **Formalized since the first edition of this page.** Theorem 3.23 (V3.69): the local solution set consists of smooth points and is a tame sub-M-polyfold equivalent to a $d$-dimensional manifold with boundary with corners, when $x$ and the zeros near it are in good position in tame charts (V3.103; or under the filler condition at the nearby zeros, V3.82), and since the second addendum with the text's hypotheses (V3.95), with the dimension as the Fredholm index (V3.97). Corollary 3.24 (V3.70) with the text's hypotheses: good position in a tame chart at every zero gives a sub-M-polyfold with tame induced structure, a manifold with boundary with corners of locally constant dimension.

- `Polyfold.theorem_3_23_of_nearby` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 124
- `Polyfold.theorem_3_23` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 166
- `Polyfold.corollary_3_24` — Polyfold/Chapter3/GlobalIFTTheoremsG.lean, line 257
- `Polyfold.theorem_3_23'` — Polyfold/Chapter3/GlobalIFTNearbyOntoG.lean, line 631
- `Polyfold.theorem_3_23_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 547

### G.19. Remark 3.36: the quantitative solution germ

*not formalized*

**HWZ (§3.3, Remark 3.36, p. 89).** Decreasing sequences $(\varepsilon_i)$, $(\tau_i)$ with: $\delta$ on $\{|a|_0 \le \varepsilon_0\}$ a continuous solution, unique for $|w|_0 \le \tau_0$; $\delta(a) \in W_i$, $|\delta(a)|_i \le \tau_i$ for $|a|_0 \le \varepsilon_i$; $\delta : \{|a|_0 \le \varepsilon_i\} \to W_i$ of class $C^i$.

**Proved in Lean.** **Not formalized in quantitative form.** Its content is Theorem 3.29 (existence, uniqueness in $O(0)$, $\delta_i(a) \in K(i)$; V3.26) and Corollary 3.34 with $m = k = i$ (V3.31), with $\varepsilon_i$ below the radius of $N(2i + 2^i - 1)$.


### G.20. Corollary 3.39: composition with a given conjugation

*formalized since* · now V3.76

**HWZ (§3.4, Corollary 3.39, p. 93).** If $g$ is equivalent by a strong bundle isomorphism $\Phi$ to a basic germ and $s$ is an sc$^+$-germ, there is $\Psi$ with $((\Psi \circ \Phi)_*(g + s))^1$ basic.

**Proved in Lean.** **Formalized since the first edition of this page** (V3.76): for $g$ sc-smooth and conjugated to a basic germ and $s$ sc-smooth into $F^1$ with $s(0) = 0$, $(g + s)^1$ is conjugated to a basic germ on the shifted structures, by the composite of the index raise of the given conjugation and the linear coordinate change of Theorem 3.38.

- `Polyfold.corollary_3_39` — Polyfold/Chapter3/BasicClassComposition.lean, line 590
- `Polyfold.corollary_3_39_isConjugate` — Polyfold/Chapter3/BasicClassComposition.lean, line 779

### G.21. Proposition 3.10, second statement, on levels $m \ge 1$

*formalized since* · now V3.12

**HWZ (§3.1, Proposition 3.10, p. 68).** $Df(a, w) : \mathbb R^n \oplus W_m \to \mathbb R^N \oplus W_m$ is Fredholm of index $n - N$ for $(a, w) \in E_{m+1}$ small in $E_m$, for every $m$.

**Proved in Lean.** **Formalized since the first edition of this page** (third addendum; V3.12): for every $m$ there is $\delta > 0$ such that $Df(x)_m : \mathbb R^n \oplus W_m \to \mathbb R^N \oplus W_m$ is Fredholm of index $n - N$ at every $x \in U_{m+1}$ with $|x|_m < \delta$, by the text's proof on level $m$; the input it needed, Lemma 3.9 on level $m$ with arbitrary $\varepsilon$, is proved as stated (V3.11).

- `Polyfold.proposition_3_10_level` — Polyfold/Chapter3/BasicGermLinearizationLevel.lean, line 236
- `Polyfold.proposition_3_10_full` — Polyfold/Chapter3/BasicGermLinearizationLevel.lean, line 276

### G.22. Proposition 3.52 as an sc-Fredholm operator on $T_xX$

*formalized since* · now V3.46 · now V3.96

**HWZ (§3.6, Proposition 3.52, p. 110).** $Tf(x) : T_xX \to Y_x$ is an sc-Fredholm operator.

**Proved in Lean.** **Formalized since the first edition of this page** (third addendum; V3.46, V3.96), in charts. In the chart of Definition 3.11 centred at the zero, $T_0O = Dr(0)E$ and $K_0 = \rho(0)F$ are sc-subspaces and $Tf(x_0) = Dg(0)|_{T_0O} : T_0O \to K_0$ is sc-Fredholm, of index $n - N$ on every level for every conjugating basic germ; in **every** strong bundle chart around a zero $y$, at the point $z$ over $y$, $\mathrm{Lin}(z) : T_zO \to K_z$ is sc-Fredholm, the levels being transported between charts at smooth points. No tameness is used. $T_xX$ and $Y_x$ themselves carry no linear structure here (G.7), so “an sc-Fredholm operator on $T_xX$” is read in charts.

- `Polyfold.proposition_3_52_sc` — Polyfold/Chapter3/FredholmGermLinearizationScG.lean, line 292
- `Polyfold.StrongBundle.linAt_isScFredholm` — Polyfold/Chapter3/LinearizationChartsScG.lean, line 400

### G.23. Theorem 3.54 (1) with the text's hypotheses: surjectivity of $f'(y)$ at the nearby zeros

*formalized since* · now V3.81 · now V3.82 · now V3.93 · now V3.94

**HWZ (§3.6, Theorem 3.54 (1), pp. 111–114).** (1) At every zero $y$ near $x$ the germ $(f, y)$ is in good position, “from Corollary 3.41 and Lemma 3.55”; (2) the solution set near $x$ is a sub-M-polyfold with the structure of a manifold with boundary with corners.

**Proved in Lean.** **Formalized since the first edition of this page** (V3.93, V3.94): with the text's hypotheses (tame germ data, good position in a tame chart, V3.103), every zero $y$ near $x_0$ is in good position in a tame chart, in particular $f'(y)$ is onto. The text's argument does not give the surjectivity (it gives that of the filled linearization only; the same step is in the book's arXiv version); it is proved by an implicit function theorem at the nearby zero for $g + \mu\rho(r(\cdot))\lambda$, with Theorem 3.30 at the centre for a contraction germ whose regions in $a$ do not depend on $\lambda$ (Findings, Chapter 3, items 180–189). The first form under the filler condition at the nearby zeros (V3.82) is kept; that condition follows from good position (V3.102). (2) is proved from (1) (V3.85, V3.94); the index is locally constant along the solution set (V3.98).

- `Polyfold.theorem_3_54_chart_onto` — Polyfold/Chapter3/GlobalIFTNearbyOntoG.lean, line 60
- `Polyfold.theorem_3_54_one'` — Polyfold/Chapter3/GlobalIFTNearbyOntoG.lean, line 508
- `Polyfold.theorem_3_54'` — Polyfold/Chapter3/GlobalIFTNearbyOntoG.lean, line 615
- `Polyfold.theorem_3_54_one` — Polyfold/Chapter3/GlobalIFTNearbySurjG.lean, line 396

### G.24. Theorem 3.58: the basic germ criterion

*formalized since* · now V3.88 · now V3.89

**HWZ (§3.7, Theorem 3.58, pp. 116–120).** Under (1) $Df(x)$ sc-Fredholm of constant index at smooth points, (2) a splitting $E = B \oplus X$ with a compactness condition, (3) a uniform estimate on $D_2f$: $f - f(0)$ is conjugated near $0$ to a basic germ.

**Proved in Lean.** **Formalized since the first edition of this page**, in the coordinates of the text's proof ($E = \mathbb R^n \oplus X$, $F = \mathbb R^N \oplus Y$; V3.89, with the second half of the proof V3.88): under (1)–(3), $f - f(0)$ is conjugated near $0$ to a basic germ. The reduction of a general sc-splitting to these coordinates is not formalized.

- `Polyfold.theorem_3_58` — Polyfold/Chapter3/BasicGermCriterionIndex.lean, line 417
- `Polyfold.theorem_3_58_of_family` — Polyfold/Chapter3/BasicGermCriterionProof.lean, line 649

### G.25. Lemmas 3.62–3.64: extreme rays

*not formalized*

**HWZ (§3.8.1, Lemmas 3.62–3.64, pp. 121–122).** A closed convex cone in finite dimensions is the closed convex hull of its extreme rays (3.62); a cone with interior is a quadrant iff it has $\dim N$ extreme rays (3.63, from [21]); a generator $a$ of an extreme ray of $N \cap C$ has $\dim N - 1 \le \#\sigma_a$ (3.64).

**Proved in Lean.** **Superseded, not formalized**: the proof of Proposition 3.22 (V3.21) avoids extreme rays (a segment argument and Lemma 3.65; Findings, Chapter 3, item 18).


### G.26. Lemmas 3.66–3.68: the complement $\widetilde N$

*not formalized*

**HWZ (§3.8.1, Lemmas 3.66–3.68, pp. 123–125).** $\widetilde N$ is in good position with good complement $(N \cap W) \oplus N^\perp$ (3.66); $C \cap \widetilde N$ is a closed convex cone whose extreme rays satisfy $\dim\widetilde N - 1 = \#\sigma_a = d_C(a)$ (3.67); either $\widetilde N \cap (\mathbb R^{\Sigma^c} \oplus W) = \{0\}$ or $\widetilde N \subseteq \mathbb R^{\Sigma^c} \oplus W$ with $\dim\widetilde N = 1$, $\Sigma = \emptyset$ (3.68).

**Proved in Lean.** **Superseded, not formalized as stated**: the normal form of Proposition 3.22 (V3.21) treats the three cases $N \cap C = N$, $\Sigma = \emptyset$, $\Sigma \ne \emptyset$ directly; the content of Lemma 3.68's second case is `quadrantNormalForm_of_vanIdx_empty`.


### G.27. Definition 3.71: class $C^k$ on partial quadrants

*not formalized*

**HWZ (§3.8.4, Definition 3.71, p. 135).** $f : U \to \mathbb R^m$ on a relatively open subset of a partial quadrant is $C^1$ if it has one-sided derivatives depending continuously on $x$; $C^k$ if $f$ and $Tf$ are $C^{k-1}$.

**Proved in Lean.** **Not formalized separately**: the theorems of §§3.8.4–3.8.5 use Mathlib's $C^k$ within the set (`ContDiffOn`), which on relatively open subsets of partial quadrants agrees with sc$^1$ = $C^1$ (`isSc1_iff_contDiffOn_of_isRelOpenInQuadrant`, Chapter 1, V1.35).


### G.28. Lemma 3.76: iterated tangent maps

*not formalized*

**HWZ (§3.8.4, Lemma 3.76, p. 139).** Under the assumptions of Proposition 3.73 the iterated tangent maps $T^kf : T^kU \to T^kV$ are smooth homeomorphisms.

**Proved in Lean.** **Superseded, not formalized**: the regularity of $f^{-1}$ is proved by bootstrapping $Dg = [Df]^{-1} \circ g$ (V3.59, V3.62; Findings, Chapter 3, item 28).


### G.29. Lemma 3.70 and Lemma 3.55 in a general presentation of $C$; Theorem 3.27 and $d_X$

*not formalized*

**HWZ (§3.8.1, §3.8.3, Lemmas 3.70, 3.55; §3.2, proof of Theorem 3.27, p. 127).** Lemma 3.55 is stated for any partial quadrant $C \subseteq E$; the proof of Theorem 3.27 uses Lemma 3.70 to get $d_{N \cap C}(v) = d_X(y)$.

**Proved in Lean.** **Lemma 3.70 is formalized in the model $\mathbb R^n \oplus W$**; Lemma 3.55 in the model, in coordinates for functionals cutting out $C$, and, since the first edition of this page, for any presentation of $C$ and $\sigma$ on a relatively open domain (V3.80). The transport of Lemma 3.70 to a general presentation, and hence $d_M = d_X$ on $M$ in Theorem 3.27, is not done (Findings, Chapter 3, item 84).


### G.30. Theorem 3.19: the dimension is the index; $\ker f'(y) = T_yS$; good position for $d_X \equiv 0$

*formalized since* · now V3.97 · now V3.98 · now V3.99 · now V3.100 · now V3.101

**HWZ (§3.1, Theorem 3.19, p. 74).** The solution set near $x_0$ is a manifold whose dimension agrees with the Fredholm index of $f'(x_0)$; at its points $\ker f'(y) = T_yS(f, U)$; and for $d_X(x) = 0$ good position is the surjectivity of $f'(x)$.

**Proved in Lean.** **Formalized since the first edition of this page** (second addendum). The dimension: the dimension $d$ of the solution set near a zero in good position is $\dim\ker f'(y) = \mathrm{ind}\,f'(y)$ at every zero $y$ near it, in every chart (V3.97, with V3.96), also in Theorems 3.23, 3.57, and the index is locally constant along the solution set (V3.98). The kernel: $D\psi$ maps $\ker f'(y)$, read in the chart at $x_0$, onto the tangent space of the solution graph (V3.99); $T_yS$ as a subspace of $T_yX$ is not formalized (Chapter 2 gap G.13). Good position in a tame chart at $d_X(y) = 0$ is surjectivity, for tame germ data (V3.100), so Theorems 3.19 and 3.56 hold with “$f'(x)$ surjective” (V3.101).

- `Polyfold.theorem_3_19_index` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 595
- `Polyfold.theorem_3_54_index_locally_constant` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 508
- `Polyfold.theorem_3_54_ker_eq_tangent` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 708
- `Polyfold.StrongBundle.isGoodPositionGerm_iff_isLinSurjAt` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 358
- `Polyfold.theorem_3_19_of_surjective` — Polyfold/Chapter3/GlobalIFTIndexG.lean, line 615

### G.31. Remark 4.3: “$X^1 \ne X$ is possible”

*formalized since* · now V4.6

**HWZ (§4.1, Remark 4.3, p. 148).** If $X_0 = X_\infty$, then $X_m = X_0$ as sets for all $m$; "however, it is possible that $X^1 \ne X$ as sc-smooth spaces despite the fact that $(X^1)_m = X_{m+1} = X_i$ as sets".

**Proved in Lean.** **Formalized since the first edition of this page** (fourth addendum; V4.6), by an example the text does not give. On the weighted sequence space $X$ of V1.13 ($|x|_m = \sup_k(k+1)^m|x_k|$), $L(t)$ is the projection onto $\cos\theta\,e_{n_k} + \sin\theta\,e_{n_{k+1}}$ ($n_k = 2^k$), the angle $\theta$ turning from $0$ to $\pi/2$ with flat ends while $t$ runs through $[1/(k+2), 1/(k+1)]$, and $L(t) = 0$ for $t \le 0$. The retraction $r(t, z) = (t, L(t)z)$ of $\mathbb R \oplus X$ is sc-smooth by a criterion for parameter families of level operators with one level of loss; its retract $O$ consists of smooth points, and the lift $O \to E_1$ is discontinuous at $0$, so $O$ is not an sc⁺-retract (Proposition 4.8), and the M-polyfold $O$ with its single chart has $X_0 = X_\infty$ and $1_0^1$ not sc-smooth. Why an example needs a retraction that loses a level (one with $C^1$ level maps gives none) is an argument, not formalized (Findings, Chapter 4, items 140–146).

- `Polyfold.remark_4_3_example` — Polyfold/Chapter4/RemarkFourThreeFamily.lean, line 922
- `Polyfold.remark_4_3_retract_example` — Polyfold/Chapter4/RemarkFourThreeFamily.lean, line 856
- `Polyfold.IsLossFamily.isScSmooth` — Polyfold/Chapter4/RemarkFourThreeExample.lean, line 312
- `Polyfold.RemarkFourThree.isLossFamily_fam` — Polyfold/Chapter4/RemarkFourThreeFamily.lean, line 732
- `Polyfold.RemarkFourThree.not_continuousOn_liftOne` — Polyfold/Chapter4/RemarkFourThreeFamily.lean, line 802

### G.32. Lemma 4.10: the section $u \mapsto (1 - p)(u - t(u))$ is sc-Fredholm

*not formalized*

**HWZ (§4.1, Lemma 4.10, pp. 151–153).** The section $u \mapsto (u, \mathbf f(u))$, $\mathbf f(u) = (1 - p)(u - t(u))$, of the local strong bundle $U \triangleleft Y \to U$ is sc-Fredholm.

**Proved in Lean.** **Not formalized, because no longer used**: Proposition 4.9, its only use, is proved directly (V4.20–V4.25). It would need $U \triangleleft Y$ as a strong bundle, $Y$ and $Y \cap F$ as sc-subspaces, the sc-isomorphism $E \cong (T_0O \oplus B) \oplus W$ with $B \subseteq Y_\infty$, and at each smooth point the re-centred strong bundle chart (V4.18), filler and conjugation. The text's proof has a sign slip in $D\mathbf f(u)$, calls $D\mathbf f(u)$ an sc⁺-operator, writes $L(T_0O)$ for $L(Y)$, and omits the interior points of $(T_0O \oplus B) \cap C$ (Findings, item 57).


### G.33. Remark 4.14: the local form near $\{d_X = 0\}$

*not formalized*

**HWZ (§4.2, Remark 4.14, p. 157).** Near points $a \in A$ with $d_X(a) = 0$ the submanifold $A$ is a smooth finite-dimensional manifold in the classical sense.

**Proved in Lean.** **Formalized only globally**: if $d_X = 0$ on all of $A$, $A$ has a corner structure, without tameness of $X$ (V4.32). The local statement, for the open piece $A \cap \{d_X = 0\}$ of an arbitrary $A$, is not formalized (Findings, item 61).

- `Polyfold.MPolyfold.hasCornerStructure_of_degIndex_eq_zero` — Polyfold/Chapter4/Submanifolds.lean, line 1530

### G.34. The open question after Proposition 4.15

*not formalized*

**HWZ (§4.2, Open Question, p. 159).** Is a sub-M-polyfold with $A = A_\infty$ and $\dim T_aA$ finite and locally constant a smooth finite-dimensional submanifold? Is the "T" $\{(x, 0) : |x| < 1\} \cup \{(0, y) : 0 \le y < 1\}$ homeomorphic to a retract $O = O_\infty$? Impossible for sc⁺-retracts.

**Proved in Lean.** **Not formalized** (a question, not a statement). The last sentence, for a retract without boundary, is V4.32 with $A = O$: an sc⁺-retract in $(O, E, E)$ is a manifold; that the "T" is not a topological manifold is not formalized (Findings, item 65).


### G.35. Theorem 4.22 (1): local faces of the chart as global local faces

*not formalized*

**HWZ (§4.2, Theorem 4.22 (1), p. 162).** There are precisely $d = d_X(x)$ local faces $F_1, \dots, F_d$ contained in $U$.

**Proved in Lean.** **Formalized for the chart model only** (V4.50): $d_X(x) = n$, all coordinates vanish at the centre, and $\psi(x)$ lies in exactly $d_X(x)$ faces of the M-polyfold $O$. The identification of these faces with (germs of) global faces of $X$ (Theorem 2.45 in the face-structured case) is not formalized (Findings, items 86, 90). The text's local faces are faces of the neighbourhood $U$ itself (closures in $U$ of the components of $U \cap \{d_X = 1\}$), so (4) is affected as well; the missing step is a local face theorem for small neighbourhoods, believed true for tame $X$ (Findings, Chapter 4, item 130; third addendum).

- `Polyfold.MPolyfold.theorem_4_22` — Polyfold/Chapter4/LocalStructure.lean, line 1541

### G.36. Theorem 4.23: chart independence of stratified regularity

*not formalized*

**HWZ (§4.3, proof of Theorem 4.23, p. 166).** Regular values of the maps $p_\sigma : A \cap F_\sigma^\circ \to \mathbb R^m$, intrinsic to $A$ and its strata.

**Proved in Lean.** **Not formalized.** Stratified regularity is defined in some product chart (V4.53); its independence of the chart is true by the transport argument of V4.39 (the transition maps of product charts are $\mathrm{id} \times \tau$ up to translation) but not formalized. Theorem 4.23 is unaffected: it produces $\Sigma$ (Findings, items 102, 108).

- `Polyfold.IsStratRegularPoint` — Polyfold/Chapter4/Families.lean, line 552

### G.37. Definition 4.25: sc-differential forms and the directed system

*not formalized*

**HWZ (§4.4, Definition 4.25, p. 167).** An sc-differential $k$-form is an sc-smooth $\omega : \oplus^kTX \to \mathbb R$, linear in each argument and skew-symmetric; pull-back along $X^{i+1} \to X^i$ gives a directed system with limit $\Omega^*_\infty(X)$.

**Proved in Lean.** **Not formalized.** It needs $\oplus^kTX$ as an M-polyfold, a linear $T_xX$ (gap G.7) and the M-polyfolds $X^i$ for $i \ge 2$ (gap G.6). The text writes $\Omega^*_\infty$ for both the limit and the sum (Findings, item 124).


### G.38. Proposition 4.26: the Lie bracket of sc-smooth vector fields

*not formalized*

**HWZ (§4.4, Proposition 4.26, p. 167).** For sc-smooth vector fields $A$, $B$ on $X$ the usual formula defines an sc-smooth vector field $[A, B]$ on $X^1$, a section of $T(X^1) \to X^2$ (quoted from another paper).

**Proved in Lean.** **Not formalized** (no proof in the text; needs the tangent bundle of $X^1$ over $X^2$, gap G.6).


### G.39. The exterior derivative, Definition 4.27 and the relative complex

*not formalized*

**HWZ (§4.4, pp. 167–168, Definition 4.27).** $d : \Omega^k(X^{i+1}) \to \Omega^{k+1}(X^i)$ by the usual formula, $d^2 = 0$; $H^*_{sc}(X) = \ker d/\operatorname{im} d$; the relative complex $\Omega^*_\infty(X) \oplus \Omega^{*-1}_\infty(\partial X)$ with $d(\omega, \tau) = (d\omega, j^*\omega - d\tau)$.

**Proved in Lean.** **Not formalized.** The direction of $d$ should presumably be $\Omega^k(X^i) \to \Omega^{k+1}(X^{i+1})$ (the bracket lives one level up); $d \circ d = 0$ and $dj^* = j^*d$ are asserted without proof; forms on $\partial X$, a union of faces, are not defined (Findings, items 120–122).


### G.40. Theorem 4.28: Stokes' theorem

*not formalized*

**HWZ (§4.4, Theorem 4.28, p. 168).** For an oriented compact tame smooth $n$-dimensional submanifold $N$ whose boundary is a union of faces $F$, and an sc-differential $(n - 1)$-form $\omega$, $\int_N d\omega = \sum_F\int_F\omega$.

**Proved in Lean.** **Not formalized** (no proof in the text; integration on manifolds with corners of varying dimension is not in Mathlib). The formula writes $\int_M$ for $\int_N$ (Findings, item 123).


### G.41. Corollary 5.8 beyond the chart level

*formalized since* · now V5.13 · now V5.14

**HWZ (§5.2, Corollary 5.8, p. 173).** $f^i$ is an sc-Fredholm section of $P^i : Y^i \to X^i$ with compact solution set ("it is a priori clear that $f^i$ is sc-Fredholm").

**Proved in Lean.** **Formalized since the first edition of this page, for each fixed $i$** (fourth addendum; V5.13, V5.14). The shifted strong bundle $P^1 : Y^1 \to X^1$ is built (total space $Y_{1,1}$, the index raises of the strong bundle charts as atlas), and $f^1$ is an sc-Fredholm section of it with compact solution set, with condition (3) of the filling on level $1$ proved for the data of Definition 3.11 (by Lemma 3.17 and Proposition 3.52 in sc form; it does not follow from level $0$ alone); $f^2$ on $P^2 = (P^1)^1$ by iteration, and so every fixed $i$. Not formalized: one statement for a family $P^i$ indexed by $i$, the identification of $(X^1)^1$ with $X_2$ as topological spaces (the sets agree; gap G.6), and the tame form of the conclusion (the tameness of the index raises of tame charts) (Findings, Chapter 5, items 140–146).

- `Polyfold.StrongBundle.shift` — Polyfold/Chapter5/StrongBundleShift.lean, line 877
- `Polyfold.IsFillingGerm.germ_shift` — Polyfold/Chapter5/Corollary58.lean, line 245
- `Polyfold.corollary_5_8` — Polyfold/Chapter5/Corollary58.lean, line 546
- `Polyfold.corollary_5_8_two` — Polyfold/Chapter5/Corollary58.lean, line 557

### G.42. The metric $\rho$ on $\Gamma^{+,1}_U(P)$

*formalized since* · now V5.21

**HWZ (§5.3, p. 174).** $\Gamma^{+,1}_U(P)$ "becomes a metric space with respect to the uniform distance $\rho(s, s') = \sup_xN(s(x) - s'(x))$. The metric space $(\Gamma^{+,1}_U(P), \rho)$ is not complete."

**Proved in Lean.** **Formalized since the first edition of this page, with a correction** (fourth addendum; V5.21). $\rho$ is a metric on $\Gamma^{+,1}_U(P)$ for every auxiliary norm ($\rho \le 2$); the density statements $N(s(x) - s'(x)) \le \varepsilon$ of V5.30, V5.39 are $\rho(s, s') \le \varepsilon$. “Not complete” is proved for the trivial bundle $\mathbb R \times \mathbb R \to \mathbb R$ ($N(x, v) = |v|$, $U = \mathbb R$) and is false without a hypothesis: the space is complete for $U = \emptyset$ and over a point with finite-dimensional fibre. Not formalized: a general sufficient condition for non-completeness, and the identification of the metric completion with the sections of Remark 5.12 (V5.22) (Findings, Chapter 5, items 150–153).

- `Polyfold.StrongBundle.allowableMetric` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 184
- `Polyfold.TrivialBundle.not_completeSpace_allowableSections` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 491
- `Polyfold.StrongBundle.completeSpace_allowableSections_empty` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 223
- `Polyfold.TrivialBundle.completeSpace_allowableSections_point` — Polyfold/Chapter5/AllowableSectionsMetric.lean, line 556

### G.43. Remark 5.14

*not formalized*

**HWZ (§5.3, Remark 5.14, p. 175).** In [21] the fibres were separable sc-Hilbert spaces and auxiliary norms had more properties involving weak convergence; neither is needed here, "due to an improved treatment of the compactness".

**Proved in Lean.** **Not formalized** (a comment on [21]). The formalization indeed assumes neither: the fibres are arbitrary and Definition 5.1 is as stated (V5.3, V5.10).


### G.44. Remark 5.16

*not formalized*

**HWZ (§5.3, Remark 5.16, pp. 176–177).** For transversal $f_0$, $f_1$ joined by a sc-Fredholm arc $(t, x) \mapsto f_t(x)$ with compact solution set, a perturbation $s$ vanishing near $t = 0, 1$ makes the arc transversal, and its solution set is a compact cobordism; "the reader will be able to carry out this construction in more detail".

**Proved in Lean.** **Not formalized** (a sketch, left to the reader; it needs the boundary case of Theorem 5.19 on $[0, 1] \times X$).


### G.45. A dense form of Theorem 5.19

*not formalized*

**HWZ (§5.3, Theorem 5.19, p. 180).** "There exists an arbitrarily small section $s \in \Gamma^{+,1}_U(P)$ satisfying $s(x) = 0$ near $\partial X$" with the properties of the theorem.

**Proved in Lean.** **Not formalized in the dense form.** The generic form gives $s_\lambda = \sum\lambda_it_i$ for $\lambda$ off a null set of a small ball, so arbitrarily small as $\lambda \to 0$ (V5.40); density around a given allowable $s'$, as in Theorems 5.13 and 5.18, is not stated (Findings, Chapter 5, item 89).

- `Polyfold.theorem_5_19` — Polyfold/Chapter5/GeneralPosition.lean, line 2119

### G.46. Finding 88: the parametrized section at the boundary zeros

*not formalized*

**HWZ (§5.3, proof of Theorem 5.19, p. 180).** "Then we consider as before the section $(\lambda, x) \mapsto f(x) + \sum\lambda_is_i(x)$, and, for a generic value of $\lambda$ ... the associated section $s_\lambda$ has the desired properties."

**Proved in Lean.** **Checked on paper only.** At a zero $(0, x)$, $x \in \partial X$, where all $s_i$ vanish, $\ker F'(0, x) = \mathbb R^m \times \ker f'(x)$ is in good position to $\mathbb R^m \times C_x$ only if $\ker f'(x) + E_x \supseteq T_xX$, a general position condition that good position does not imply ($\mathbb R(1, 1)$ in $[0, \infty)^2$). So "as before" cannot apply Theorem 3.54 to $F$ there; the formal proof avoids these points (V5.40) (Findings, Chapter 5, item 88).

- `Polyfold.theorem_5_19` — Polyfold/Chapter5/GeneralPosition.lean, line 2119
- `Polyfold.StrongBundle.IsGoodPositionGermTame.congr_nhds` — Polyfold/Chapter3/Chapter5BridgeG.lean, line 77

### G.47. Remark 5.21

*not formalized*

**HWZ (§5.3, Remark 5.21, p. 181).** Instead of $(f|X_i, P|Y_i) = (f_i, P_i)$ one should require that the problems are isomorphic and make this part of the data.

**Proved in Lean.** **Not formalized.** Definition 5.20 takes the restrictions to $t^{-1}(0)$, $t^{-1}(1)$ as the end problems (V5.41) (Findings, Chapter 5, item 100).


### G.48. Theorem 5.22: Morse-type structure

*not formalized*

**HWZ (§5.3, Theorem 5.22, p. 181 (proof pp. 181–186)).** For a generalized compact homotopy with end problems in general position and $\partial X = X_0 \sqcup X_1$, an arbitrarily small $s_0 \in \Gamma^{+,1}_U(P)$ vanishing near $\partial X$ makes $(f + s_0, x)$ in general position at every zero and $t : S_{f+s_0} \to [0, 1]$ a function with only Morse-type critical points.

**Proved in Lean.** **Not formalized.** It needs finite-dimensional Morse theory on manifolds with boundary, the cotangent bundle of the solution set, a parametric Sard theorem and a trivialization $\Phi_\lambda : S \to S_\lambda$ of the family (not "the classical standard implicit function theorem"); its proof also needs $dt(x) \ne 0$ at the critical points of $t|S$, which the statement does not assume (V5.42). Lemmas 5.23, 5.24 are V5.42–V5.44 (Findings, Chapter 5, items 101, 103).

- `Polyfold.lemma_5_23` — Polyfold/Chapter5/Homotopy.lean, line 106
- `Polyfold.lemma_5_24` — Polyfold/Chapter5/Homotopy.lean, line 527
- `Polyfold.ne_zero_of_isCompl_ker` — Polyfold/Chapter5/Homotopy.lean, line 150

### G.49. Theorem 5.27: cobordism between good position perturbations

*not formalized*

**HWZ (§5.3, Theorem 5.27, p. 188).** For a proper homotopy $f_t$ and perturbations $s_0$, $s_1$ putting $f + s_i$ in good position, there is $s(x, t)$ with $s(\cdot, i) = s_i$ such that $f + s$ is in good position at all smooth points; its solution set is a compact manifold with corners meeting $\{i\} \times X$ in $S_0$, $S_1$.

**Proved in Lean.** **Not formalized**: "the proof is left to the reader" (Findings, Chapter 5, item 104).


### G.50. Theorem 5.32: Bonic–Frampton

*not formalized*

**HWZ (§5.4.2, Theorem 5.32, p. 193).** On $L^p$, $\|\cdot\|^p$ is $C^\infty$ for $p$ an even integer, $C^{p-1}$ for $p$ odd, and $C^{[p]}$ for $p$ not an integer.

**Proved in Lean.** **Not formalized** (cited from [9], Theorem 1; deep Banach space geometry, not used on the main line; the statement misses "$p$" in (1), (2)) (Findings, Chapter 5, items 117, 120).


### G.51. The $L^p$ and Sobolev remark

*not formalized*

**HWZ (§5.4.2, pp. 193–194).** The usual norms of $W^{k,p}(\Omega)$ have the differentiability of $\|\cdot\|_{L^p}$; $\beta(\|x\|^p)$ is a bump function of $L^p$; $W^{1,4}(\Omega)$ with $E_m = W^{1+m,4}(\Omega)$ admits sc-smooth bump functions, while for $W^{1,3/2}(\Omega)$ the straightforward one is only sc¹ — "does there exist a sc-smooth bump function on $E$?"

**Proved in Lean.** **Not formalized.** It needs Sobolev spaces with their sc-structures (gap G.1) and Theorem 5.32 (Findings, Chapter 5, item 118).


### G.52. Theorem 5.40: Toruńczyk

*not formalized*

**HWZ (§5.4.2, Theorem 5.40, p. 198).** A Banach space $E$ admits a $C^k$-partition of unity iff there are a set $\Gamma$ and a coordinate-wise $C^k$ homeomorphic embedding of $E$ into $c_0(\Gamma)$.

**Proved in Lean.** **Stated, not proved** (`TorunczykStatement`, V5.59), and not used (cited from [9], Theorem 30) (Findings, Chapter 5, item 117).

- `Polyfold.TorunczykStatement` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 915

### G.53. Theorem 5.43: Godefroy–Troyanski–Whitfield–Zizler

*not formalized*

**HWZ (§5.4.2, Theorem 5.43, p. 198).** If the WCG space $E$ admits a $C^k$-bump function, then it also admits $C^k$-partitions of unity.

**Proved in Lean.** **Stated, not proved** (`GodefroyTroyanskiWhitfieldZizlerStatement`, V5.62; cited from [12] and [9], Theorem 31); it is an explicit hypothesis of Corollary 5.44 (V5.63) (Findings, Chapter 5, items 116, 117).

- `Polyfold.GodefroyTroyanskiWhitfieldZizlerStatement` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 1072
- `Polyfold.corollary_5_44` — Polyfold/Chapter5/PartitionsOfUnity.lean, line 1083

### G.54. Theorem 6.43: the invariant $\Psi_{(f,o)}$

*not formalized*

**HWZ (§6.6, Theorem 6.43, p. 231 (proof pp. 231–233)).** Over a tame $X$ with sc-smooth bump functions, a proper oriented sc-Fredholm section $(f, o)$ defines a linear map $\Psi_{(f,o)} : H^*_{dR}(X, \partial X) \to \mathbb R$ with (1) $\Psi_{(f,o)}([\omega, \tau]) = \int_{S_{f+s}}\omega - \int_{\partial S_{f+s}}\tau$ for every $s$ admissible for $(N, U)$, and (2) $\Psi_{(f_0,o_0)} = \Psi_{(f_1,o_1)}$ for a proper oriented homotopy. For $\partial X = \emptyset$, $\Psi_{(f,o)}([\omega]) = \int_{S_{f+s}}\omega$ on $H^n_{dR}(X)$, $n$ the index (p. 233).

**Proved in Lean.** **Not formalized** (decision D1). It needs the sc-differential forms and their cohomology of §4.4 (gaps G.37–G.40), integration over oriented compact manifolds with boundary with corners and Stokes' theorem, which Mathlib does not have; its proof also uses the homotopy of Remark 5.16 (gap G.44). What the theorem rests on is formalized: the perturbations of Theorem 5.18 (V5.38, V5.39) and the tangent orientations of Theorem 6.41 (V6.61) (Findings, Chapter 6, item 100).

- `Polyfold.theorem_5_18` — Polyfold/Chapter5/GeneralPosition.lean, line 1779
- `Polyfold.theorem_6_41` — Polyfold/Chapter6/SolutionOrientation.lean, line 892

### G.55. §6.6: the sections admissible for $(N, U)$

*not formalized*

**HWZ (§6.6, p. 230).** For a proper oriented $(f, o)$ over a tame $X$ with bump functions and an auxiliary norm $N$, Theorem 5.18 gives an open $U \supseteq S$ such that every sc⁺-section supported in $U$ with $N(s(x)) \le 1$ has a compact $S_{f+s}$; the distinguished ones, with $(f + s, x)$ in general position at every zero, have oriented solution sets and are called admissible for $(N, U)$.

**Proved in Lean.** **Not formalized** as a notion; it is used only in Theorem 6.43 (gap G.54). The facts recalled are formalized: Theorem 5.18 (V5.38, V5.39) and the tangent orientations of the solution set (V6.61); the orientation of $S_{f+s}$ for a perturbed $f$ is gap G.69 (Findings, Chapter 6, item 101).

- `Polyfold.theorem_5_18_dense` — Polyfold/Chapter5/GeneralPosition.lean, line 1968

### G.56. The facts on paths recalled on p. 201

*not formalized*

**HWZ (§6.1, before Proposition 6.2, p. 201).** An M-polyfold is locally path connected, and any two smooth points in the same path component can be joined by an sc⁺-smooth path $\varphi : [0, 1] \to X$.

**Proved in Lean.** **Not formalized** beyond a chart: inside the domain of a chart, nearby smooth points are joined by sc-smooth paths (`exists_nhds_scPath`, V6.49), and "in the same path component" (Definitions 6.27, 6.38) is read as "joined by an sc-smooth path" (V6.58) (Findings, Chapter 6, item 42).

- `Polyfold.exists_nhds_scPath` — Polyfold/Chapter6/ScPaths.lean, line 84

### G.57. The alternative determinant $\lambda(\ker T) \otimes \lambda(\operatorname{coker}(T)^*)$

*not formalized*

**HWZ (§6.3, after Definition 6.7, p. 208).** Some authors use $\det(T) = \lambda(\ker T) \otimes \lambda(\operatorname{coker}(T)^*)$; the two definitions are naturally isomorphic, given a convention identifying $\lambda^*(A)$ and $\lambda(A^*)$.

**Proved in Lean.** **Not formalized**, and not used: the chapter's formal statements use Definition 6.7 (V6.8); the convention $\iota$ of Definition 6.3 is V6.3 (Findings, Chapter 6, item 10).

- `Polyfold.fredholmDet` — Polyfold/Chapter6/FredholmDet.lean, line 133
- `Polyfold.iotaDual` — Polyfold/Chapter6/DetLine.lean, line 601

### G.58. The identification (95) and the maps $V \otimes \lambda(\mathbb R^n) \to V$

*not formalized*

**HWZ (§6.3, after Proposition 6.15, p. 213).** Dual to (94), $\mathbb R \to \lambda(\mathbb R^n)$ maps $1$ to the wedge of the standard basis, with inverse (95) $c_1 \wedge \dots \wedge c_n \mapsto \det([c_1, \dots, c_n])$; this gives identifications $V \otimes \lambda(\mathbb R^n) \to V$ and $V \otimes \lambda^*(\mathbb R^n) \to V$ for every finite-dimensional $V$.

**Proved in Lean.** **Not formalized**, and not used: the formal statements use (94) only (V6.17, V6.18) (Findings, Chapter 6, item 10).

- `Polyfold.stabPsi_dualVec` — Polyfold/Chapter6/Stabilization.lean, line 295

### G.59. Lemma 6.19 in general

*not formalized*

**HWZ (§6.4, Lemma 6.19, p. 216).** For finite-dimensional topological vector bundles $E$, $F$ over $X$, the bundles $\lambda(E)$, $\lambda^*(F)$, $E \oplus F$ and $E \otimes F$ have the structure of topological vector bundles in a natural way (a standard lemma, cited from [29]).

**Proved in Lean.** **Not formalized** in general: Mathlib has no exterior powers or tensor products of vector bundles. The lemma is applied only to trivial bundles, and Proposition 6.20 is proved with explicit frames (V6.22) (Findings, Chapter 6, item 22).

- `Polyfold.LocalDetChart.frame` — Polyfold/Chapter6/LocalDetBundle.lean, line 379
- `Polyfold.proposition_6_20` — Polyfold/Chapter6/LocalDetBundle.lean, line 524

### G.60. $\mathrm{DET}(E, F)$ is not orientable; the classical case

*not formalized*

**HWZ (§6.4, p. 218; the opening of §6.5, p. 219).** The text remarks that $\mathrm{DET}(E, F)$ is known to be non-orientable, though orientable over certain subsets. For a classical Fredholm map $f : U \to F$, the determinant line bundle of the $Df(x)$ is a smooth line bundle over $U$, with precisely two orientations if $U$ is contractible.

**Proved in Lean.** **Not formalized** (remarks, not used). The orientability over convex sets of Fredholm operators, which is what the chapter uses, is Proposition 6.26 (V6.30) (Findings, Chapter 6, item 26).

- `Polyfold.proposition_6_26` — Polyfold/Chapter6/DetBundle.lean, line 356

### G.61. Proposition 6.28 (1): sc-smooth contractibility

*not formalized*

**HWZ (§6.5, Proposition 6.28 (1), p. 220; Theorem 6.35, Definition 6.36, Theorem 6.37).** The neighbourhood $U(x)$ of Proposition 6.28 is sc-smoothly contractible (by $r(ty)$ on $U = r(V')$, $V'$ convex), and Theorem 6.35, Definition 6.36 and property (∗) of Theorem 6.37 ask for sc-smoothly contractible neighbourhoods.

**Proved in Lean.** **Not formalized.** As we read it, the proof does not establish (1) for $U$: it needs $r(V') \subseteq V'$, which is not stated. (1′) is proved instead (two sc-smooth paths in $U$ with the same end points are sc-smoothly homotopic in a larger $W$ with the end points fixed) and is what the proofs use (V6.32, V6.48, V6.50, V6.57) (Findings, Chapter 6, items 45, 53, 54, 72).

- `Polyfold.proposition_6_28` — Polyfold/Chapter6/OrientableNbhd.lean, line 529
- `Polyfold.theorem_6_35` — Polyfold/Chapter6/PropagationWellDefined.lean, line 740

### G.62. Lemma 6.30 as a statement about manifolds

*not formalized*

**HWZ (§6.5, Lemma 6.30, p. 222).** The solution set of $F = 0$ near $(t, \varphi(t), 0)$ is a smooth manifold with boundary with corners, $\pi : S \to [0, 1]$ is a submersion, its fibres $S_t$ are manifolds with boundary with corners, and $L$ is a smooth vector bundle over $[0, 1]$.

**Proved in Lean.** **Not formalized.** The kernels are formalized as a continuous family of subspaces of the model space (V6.34, V6.42), which is all the continuation of orientations needs (Findings, Chapter 6, item 48).

- `Polyfold.exists_subspaceFamily_linKer` — Polyfold/Chapter6/KernelFamily.lean, line 166
- `Polyfold.exists_isStabKernels` — Polyfold/Chapter6/StabKernelsExist.lean, line 88

### G.63. Property (P) of Lemma 6.29 for the slices $F_t$

*not formalized*

**HWZ (§6.5, Lemma 6.29, p. 222).** (P): for every fixed $t \in [0, 1]$, the section $F_t$ is at $(\varphi(t), 0)$ in general position to the boundary of $X \times \mathbb R^k$.

**Proved in Lean.** **Not formalized.** The general position of $F$ at the points $(t, \varphi(t), 0)$, which the text derives from (P) and which Lemmas 6.30, 6.31 use, is proved (V6.33). As we read it, (P) follows, since the tangent vectors of the family of zeros lie in $\ker F'$ and $\mathbb R^n$ has no boundary; this chart computation is not carried out (Findings, Chapter 6, item 47).

- `Polyfold.lemma_6_29` — Polyfold/Chapter6/Lemma629.lean, line 203

### G.64. $\mathrm{Lin}(f, x)$ as sc-Fredholm operators on every level

*not formalized*

**HWZ (§6.1, Definition 6.1, p. 201).** The operators in $\mathrm{Lin}(f, x)$ are sc-Fredholm operators $T_xX \to Y_x$, all with the same Fredholm index.

**Proved in Lean.** **Not formalized** on every level: at a chart point the members are shown Fredholm on level $0$, with the index $\mathrm{ind}(f, x)$ of V3.98, which is what the determinant lines use (V6.1) (Findings, Chapter 6, item 40).

- `Polyfold.ChartPoint.exists_index_linSet` — Polyfold/Chapter6/LinSet.lean, line 388

### G.65. Paths and families on $[0, 1]$; $X \times [0, 1]$ as an M-polyfold

*not formalized*

**HWZ (§6.5, pp. 220–230).** Paths, homotopies and families are sc-smooth maps on $[0, 1]$, $[0, 1]^2$, $[0, 1]^n$, and $X \times [0, 1]$, $[0, 1] \times X \times \mathbb R^k$ are M-polyfolds with boundary (Proposition 6.28, Lemmas 6.29–6.34, Theorem 6.35, Remark 6.42).

**Proved in Lean.** **Not formalized** as stated: they are read on $\mathbb R$, $\mathbb R^2$, $\mathbb R^n$ and $\mathbb R^n \times X$, of which only $[0, 1]$, $[0, 1]^2$, $[0, 1]^n$ matters (decision D2), as for Proposition 6.2 in Chapter 3 (V3.98); a path that does not extend sc-smoothly to $\mathbb R$ is not covered (Findings, Chapter 6, items 71, 102).


### G.66. Remark 6.42 beyond a point

*not formalized*

**HWZ (§6.5, Remark 6.42, p. 230).** $\hat f(x, t) = f(x) + s(x, t)$ on $X \times [0, 1]$ has a natural orientation associated with $o$ and the standard orientation of $[0, 1]$.

**Proved in Lean.** **Not formalized** beyond a point: that $(t, y) \mapsto \hat o$ is an orientation of $\hat f$ in the sense of Definition 6.40 (continuity over the orientable neighbourhoods of $\mathbb R \times X$, independence of the chart of the pull-back bundle), built from an orientation of $f$. At a point the remark is V6.62 (Findings, Chapter 6, item 97).

- `Polyfold.ChartPoint.existsUnique_prodOr` — Polyfold/Chapter6/ProductOrientation.lean, line 1136

### G.67. Theorem 6.41: the orientation of $S$ as a manifold

*not formalized*

**HWZ (§6.5, Theorem 6.41, p. 229).** The solution set $S$ is a smooth compact manifold with boundary with corners possessing a natural orientation.

**Proved in Lean.** **Not formalized** as an orientation of the abstract finite-dimensional manifold $S$ (of its tangent bundle in the charts of the induced structure). What is formalized is the tangent orientation at each zero and its continuity along the sc-smooth paths of zeros in a chart (V6.61) (Findings, Chapter 6, item 92).

- `Polyfold.theorem_6_41` — Polyfold/Chapter6/SolutionOrientation.lean, line 892

### G.68. Theorem 6.41: tangent orientations read in two charts

*not formalized*

**HWZ (§6.5, Theorem 6.41, p. 229).** $T_xS = \ker f'(x)$ is oriented by $o^f_x$, an object the text treats as independent of the chart.

**Proved in Lean.** **Not formalized**: the compatibility of the tangent orientations read in two charts at the same zero. $\mathrm{Or}^f_x$ itself is identified between charts (V6.53–V6.55) (Findings, Chapter 6, item 92).

- `Polyfold.ChartPoint.tangentOr` — Polyfold/Chapter6/SolutionOrientation.lean, line 414
- `Polyfold.ChartPoint.orTransfer` — Polyfold/Chapter6/ChartTransfer.lean, line 1205

### G.69. The paragraph after Theorem 6.41: perturbed solution sets

*not formalized*

**HWZ (§6.5, after Theorem 6.41, pp. 229–230).** If $f$ is not generic, a small perturbation $s$ supported near the zero set gives $S_{f+s}$ a natural orientation coming from $o^f$, since $\det((f + s)'(x))$ is oriented from $\mathrm{DET}(f, x)$ for $x \in S_{f+s}$.

**Proved in Lean.** **Not formalized**: the perturbation, the orientation of $S_{f+s}$ coming from $o^f$, and the identification $\mathrm{Lin}(f + s, x) = \mathrm{Lin}(f, x)$ for an sc⁺-section $s$ that it uses. The perturbations themselves are Theorem 5.18 (V5.38, V5.39) (Findings, Chapter 6, item 93).

- `Polyfold.theorem_5_18` — Polyfold/Chapter5/GeneralPosition.lean, line 1779

