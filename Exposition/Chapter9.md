# Chapter 9. Branched ep⁺-subgroupoids: weighted solution sets, their tangents, orientations and measures (HWZ Part II, Chapter 9, pp. 401–458 (2017 pp. 291–332))

*Hofer–Wysocki–Zehnder, "Polyfold and Fredholm Theory", Part II, Chapter 9 (arXiv 1707.08941, pp. 291–332), rewritten for a
first-year graduate student who has read Chapters 7 and 8 and wants to know what kind of object the solution set of a
perturbed equation with local symmetries is. Every formalized statement is proved; what is not formalized is marked. Where
the Lean formalization found a gap or a shorter route, the text follows the Lean. Statement numbers and printed pages are
those of the book (Springer 2021), with the 2017 text's in parentheses (see `BookConcordance.md`); results new in the 2021
edition are marked as such. Conventions: ep-groupoids, natural representations of the isotropy groups $G_x$, the orbit map
$\pi : X \to |X|$ and the reduced ep-groupoid are those of Chapter 7, the tangent ep-groupoid that of Chapter 8. A
submanifold is a smooth finite-dimensional submanifold of Part I, near each of its points the image of an sc⁺-retraction.
The tangent fibres $T_xX$ carry no linear structure in the project (gap G.7), so the tangent space $T_yM$ of a submanifold
is a set of tangent vectors, and every piece of linear algebra is done in a chart. The findings cited are those of
`Findings.md`, "Chapter 9".*

---

## 0. One picture, two drawings: counting solutions with weights

Perturb an equation on $\mathbb R^2$ so that its solution set is two smooth curves through the origin: the first is the
graph of $\beta_1$, which vanishes for $s \le 0$ and is positive for $s > 0$, and the second is the graph of $\beta_2$,
positive for $s < 0$ and zero for $s \ge 0$. Count every point by the number of curves through it: $\Theta(p) = \#\{i \mid p
\in \mathrm{graph}\,\beta_i\}$. Then $\Theta = 1$ on the two curves except at the origin, where they cross, and $\Theta(0) =
2$. Now draw it differently: the axis, the graph of $\gamma_1 = 0$, and the graph of $\gamma_2 = \beta_1 + \beta_2$,
positive off $0$; each point gets the same count. The two drawings share no curve near the origin, yet they describe one
function $\Theta$. This is Remark 9.1.3 (b) (2017: 9.2 (b)), and it is the whole point of the chapter: in the presence of
symmetries a perturbed solution set cannot in general be made a manifold, only a function to $\mathbb Q^+$ that is *locally*
a weighted sum of indicators of submanifolds, and the local pictures are not unique.

Symmetry is where the rational weights come from. If a group of order $2$ swaps the two curves, a symmetric perturbation
must keep both, and a single "solution" in the orbit space is counted as $\frac12 + \frac12$. A solution set with symmetry
is therefore a functor $\Theta : X \to \mathbb Q^+$ on an ep-groupoid. The chapter gives it what a manifold has, a
dimension, tangent spaces, an orientation, a boundary and integrals with Stokes' theorem, built from the local pictures and
independent of them. Three of its uniqueness claims, as we read them, do not hold as stated, each an instance of the
non-uniqueness of the drawings (§§2, 4, 5).

## 1. Branched ep⁺-subgroupoids (pp. 401–406 (2017 pp. 291–296))

**Remark 9.1.1 (2017: 9.1) (the dimension of a submanifold).** The dimension of $T_mM$ is locally constant on a submanifold
$M$.

*How this is read.* The dimension is that of the chart image of $T_aM$, a linear subspace, and does not depend on the chart.
Local constancy needs level-0 calculus of Part I that the project lacks; it is the hypothesis `HasLocallyConstantDimAt`,
proved on $\mathbb R^m$, where $T_yM$ is the range of the idempotent $Ds(y)$ of a retraction, whose rank is its continuous
trace (Findings, item 2). *Checked by machine (V9.2):* `Polyfold.MPolyfold.HasDimAt`, `Polyfold.MPolyfold.HasDimAt.unique`,
`Polyfold.MPolyfold.IsSmoothSubmanifold.exists_hasDimAt`, `Polyfold.MPolyfold.HasLocallyConstantDimAt`,
`Polyfold.MPolyfold.hasLocallyConstantDimAt_rn`.

**Definition 9.1.2 (2017: 9.1) (branched ep⁺-subgroupoid).** A branched ep⁺-subgroupoid of the ep-groupoid $X$ is a functor
$\Theta : X \to \mathbb Q^+$, that is a function on objects with $\Theta(s(\varphi)) = \Theta(t(\varphi))$, such that
$\mathrm{supp}(\Theta) = \{\Theta > 0\}$ lies in the smooth objects, $|\mathrm{supp}(\Theta)|$ is paracompact, and every $x
\in \mathrm{supp}(\Theta)$ has a *local branching structure*: an open $U(x)$, finitely many submanifolds $M_i \subseteq
U(x)$ through $x$, properly embedded, and weights $\sigma_i > 0$ with $\Theta(y) = \sum_{i : y \in M_i} \sigma_i$ for $y \in
U(x)$. $\Theta$ is $n$-dimensional if at every point of its support some local branching structure has only $n$-dimensional
sheets.

Paracompactness is an instance on the subspace $|\mathrm{supp}(\Theta)|$, and properness of the inclusion $M_i \to U(x)$ is
`IsProperMap`; for an $M_i$ closed in $U(x)$ it is automatic. The 2021 text says the sheets of an $n$-dimensional $\Theta$
"can be taken" $n$-dimensional, and this is the definition used. The zero functor and the indicator of a smooth point of
$\mathbb R^n$ are examples, and so are finite weighted sums of indicators of closed submanifolds of $\mathbb R^n$ (Findings,
items 1, 3). *Checked by machine (V9.1, V9.3):* `Polyfold.EpGroupoid.IsBranchedEpSubgroupoid`,
`Polyfold.EpGroupoid.LocalBranchingStructure`, `Polyfold.EpGroupoid.IsNDimensional`,
`Polyfold.EpGroupoid.isBranchedEpSubgroupoid_indicator`, `Polyfold.EpGroupoid.isBranchedEpSubgroupoid_sum_rn`.

**Remark 9.1.3 (2017: 9.2) (local branching structures are not unique).** The two drawings of §0 are two local branching
structures of one $\Theta$ on $\mathbb R^2$ with no common sheet near the origin.

*Proof.* The sign conditions on $\beta_1$, $\beta_2$ are met by $\beta_1(s) = e(s)$, $\beta_2(s) = e(-s)$ with $e(s) =
\exp(-1/s)$ for $s > 0$ and $0$ otherwise. If the graphs of $0$ and $\gamma_2$ give the same count as those of $\beta_1$ and
$\beta_2$, then on the vertical line over $s$ the points $(s, \beta_1(s))$ and $(s, \beta_2(s))$ are covered with the right
multiplicity only if $\gamma_2(s) = \beta_1(s) + \beta_2(s)$, one of the two summands being $0$; conversely this $\gamma_2$
works. Each of $\beta_1$, $\beta_2$ differs from $0$ and from $\gamma_2$ at points arbitrarily close to $0$, so no sheet of
one structure agrees with a sheet of the other on a neighbourhood of the origin. $\square$

*Checked by machine (V9.4):* `Polyfold.EpGroupoid.remark_9_1_3_b`,
`Polyfold.EpGroupoid.Remark913Hyp.eq_add_of_thetaGraphs_eq`, `Polyfold.EpGroupoid.remark913Hyp_expNegInvGlue`.

**Remark 9.1.4 (2017: 9.3) (paracompactness).** A paracompact subset of $|X|$ is metrizable, and compactness of
$|\mathrm{supp}(\Theta)|$ gives paracompactness. Not formalized (gap G.94; Findings, item 7).

**Lemma 9.1.5 (2017: 9.1) (the orbit support is locally closed).** For a branched ep⁺-subgroupoid $\Theta$,
$|\mathrm{supp}(\Theta)|$ is locally closed in $|X|$.

*Proof.* Since $\Theta$ is a functor, $\mathrm{supp}(\Theta)$ is saturated: $\pi^{-1}(|\mathrm{supp}(\Theta)|) =
\mathrm{supp}(\Theta)$. On the domain $U(x)$ of a local branching structure the support is $\bigcup_i M_i$, a finite union
of sets closed in $U(x)$; so $\mathrm{supp}(\Theta)$ is locally closed in $X$. The orbit map is open (Chapter 7), and the
image of a saturated locally closed set under an open quotient map is locally closed. $\square$

The text's neighbourhood with the properness property is not needed (Findings, item 5). *Checked by machine (V9.5):*
`Polyfold.EpGroupoid.preimage_π_orbitSupp`, `Polyfold.EpGroupoid.isLocallyClosed_supp`, `Polyfold.EpGroupoid.lemma_9_1_5`.

**Definition 9.1.6 (2017: 9.2) (closed and compact).** $\Theta$ is closed, or compact, if $|\mathrm{supp}(\Theta)|$ is
closed, or compact, in $|X|$. *Checked by machine (V9.6):* `Polyfold.EpGroupoid.IsClosedBranched`,
`Polyfold.EpGroupoid.IsCompactBranched`.

**Lemma 9.1.7 (2017: 9.2) (symmetric local branching structures).** At $x \in \mathrm{supp}(\Theta)$ there are local
branching structures, inside every neighbourhood of $x$, on the domain $U$ of a natural representation of $G_x$, with an
action of $G_x$ on the index set such that $g * M_i = M_{g(i)}$ and $\sigma_{g(i)} = \sigma_i$.

*Proof.* Restrict a structure to $U$: the sheets $M_i \cap U$ are submanifolds, closed in $U$, through $x$. Put $J = I
\times G_x$, $M_{(i,g)} = \Phi(g)(M_i \cap U)$ and $\sigma_{(i,g)} = \sigma_i / \#G_x$. Each $\Phi(g)$ is an
sc-diffeomorphism of $U$ fixing $x$, so $M_{(i,g)}$ is a properly embedded submanifold through $x$; the text uses this
without saying so. For $y \in U$, $y \in \Phi(g)(M_i)$ iff $\Phi(g)^{-1}(y) \in M_i$, and $\Theta(\Phi(g)^{-1}(y)) =
\Theta(y)$ since $\Theta$ is a functor, so $\sum_{(i,g) : y \in M_{(i,g)}} \sigma_i / \#G_x = \frac{1}{\#G_x} \sum_g
\Theta(\Phi(g)^{-1} y) = \Theta(y)$. $G_x$ acts on $J$ by left multiplication on the second factor. $\square$

Before the lemma the text restricts a structure to $V(x_0) \subseteq U(x)$; since a local branching structure has $x$ on
every sheet, the restriction is formalized for open $V \ni x$, the case used here (Findings, items 5, 6). *Checked by
machine (V9.7):* `Polyfold.EpGroupoid.LocalBranchingStructure.restrict`,
`Polyfold.EpGroupoid.LocalBranchingStructure.symmetrize`, `Polyfold.EpGroupoid.lemma_9_1_7`.

**Definition 9.1.8 (2017: 9.3) (manifold and orbifold type).** $\Theta$ is of orbifold type if it takes only the values $0$
and $1$, of manifold type if moreover there is at most one morphism between two points of its support. *Checked by machine
(V9.8):* `Polyfold.EpGroupoid.IsOrbifoldType`, `Polyfold.EpGroupoid.IsManifoldType`.

**Proposition 9.1.9 (2017: 9.1) (manifold and orbifold structures).** For $\Theta$ of manifold or orbifold type,
$|\mathrm{supp}(\Theta)|$ carries a natural manifold or orbifold structure (with Remark 9.1.10). Not formalized (gap G.95;
Findings, item 7).

## 2. Splitting by dimension (pp. 407–408 (2017 p. 297))

**Proposition 9.1.11 (2017: 9.2) (the dimensional decomposition).** A branched ep⁺-subgroupoid determines a unique sequence
$\Theta_0, \Theta_1, \ldots$ of branched ep⁺-subgroupoids with $\Theta_k$ $k$-dimensional and $\Theta = \sum_k \Theta_k$,
the sum locally finite.

*The local construction.* Given a local branching structure and a labelling of its sheets by dimension, put $\Theta_k(y) =
\sum_{\dim M_i = k,\ y \in M_i} \sigma_i$ on $U(x)$. The sheets of dimension $k$ form a $k$-dimensional local branching
structure of $\Theta_k$, and $\Theta = \sum_k \Theta_k$ on $U(x)$. For a symmetric structure, $\Phi(g)$ preserves dimension,
so the $\Theta_k$ are $G_x$-invariant. That $\Theta_k$ does not depend on the structure is Proposition 9.1.12.

*The uniqueness, as we read it, does not hold.* On the trivial ep-groupoid of $\mathbb R^2$ let $L$ be the $x$-axis and
$\Theta = 1_L$. Family A: $\Theta_0 = 1_{\{0\}}$, $\Theta_1 = 1_{L \setminus \{0\}}$. Family B: $\Theta_0 = 0$, $\Theta_1 =
1_L$. In family A, $L \setminus \{0\}$ is a $1$-dimensional submanifold properly embedded in the open set $\mathbb R^2
\setminus \{0\}$, all Definition 9.1.2 asks at its points; both families have (1) and (2), and the text's proof constructs
B. A possible repair: each $\Theta_k$ represented near each point by a subfamily of a local branching structure of $\Theta$.
It and the global gluing of the local $\Theta_k$ are not formalized (gap G.96; Findings, item 8). *Checked by machine
(V9.9):* `Polyfold.EpGroupoid.Proposition_9_1_11`, `Polyfold.EpGroupoid.LocalBranchingStructure.eq_sum_dimPart`,
`Polyfold.EpGroupoid.SymmetricBranchingStructure.dimPart_Φ`, `Polyfold.EpGroupoid.not_proposition_9_1_11_rn`.

**Proposition 9.1.12 (new in the 2021 edition) (the local decomposition is intrinsic).** For two local branching structures
of $\Theta$ at $x$ there is an open $G_x$-invariant $V(x)$ on which their dimensional decompositions agree.

For structures of one dimension this is immediate, $\Theta_n = \Theta$ for both. The general case is proved in Appendix
§9.6.1 (§8 below), by descending induction on the dimension; its key step needs the graph representation of §3, which is a
hypothesis on a general M-polyfold and holds on $\mathbb R^m$. So the proposition holds for every ep-groupoid whose object
M-polyfold is $\mathbb R^m$, and in general under that hypothesis (Findings, items 9, 91). *Checked by machine (V9.10):*
`Polyfold.EpGroupoid.Proposition_9_1_12`, `Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_isOfDim`,
`Polyfold.EpGroupoid.proposition_9_1_12_of_hasGraphChartAt`, `Polyfold.EpGroupoid.proposition_9_1_12_rn`.

## 3. Good points and the tangent section (pp. 408–418 (2017 pp. 297–306))

The tangent of $\Theta$ at $x$ should be the weighted sum of the tangent spaces of the sheets through $x$. To make "formal
sum of tangent spaces" precise, $\mathrm{Gr}(x)$ is the group of finitely supported rational functions on subsets of $T_xX$,
and a morphism $\varphi : x \to y$ pushes such a sum forward by its tangent $T\varphi$ (Chapter 7). The objects $(x, a)$, $a
\in \mathrm{Gr}(x)$, over the smooth objects form the category $\mathrm{Gr}(X)$ with the projection $\pi$ to $X^\infty$
(Findings, item 20). *Checked by machine (V9.11, V9.12):* `Polyfold.EpGroupoid.Gr`, `Polyfold.EpGroupoid.grPush_comp`,
`Polyfold.MPolyfold.submanifoldTangent`, `Polyfold.MPolyfold.chartTangent_eq`, `Polyfold.MPolyfold.finrank_chartTangent`.

**Theorem 9.2.1 (2017: 9.1) (the tangent section).** There is a section functor $T_\Theta : X^\infty \to \mathrm{Gr}(X)$
with $T_\Theta(x) = \sum_i \sigma_i T_xM_i$ for every local branching structure at $x \in \mathrm{supp}(\Theta)$,
$T_\Theta(x) = 0$ off the support, and $T_\Theta(\varphi) = (T_\Theta(s(\varphi)), \varphi)$.

Everything rests on one claim, *the independence*: two local branching structures at $x$ give the same formal sum $\sum_i
\sigma_i T_xM_i$. Given it, $T_\Theta(x)$ is that sum, and naturality follows by transporting a structure along the local
sc-diffeomorphism $\hat\varphi$ of $\varphi$, which maps tangent sets by $T\varphi$. The independence is proved through good
points.

**Definition 9.2.2 (2017: 9.4) (good points).** A point $y$ of the support in $U(x)$ is good if near $y$ all sheets through
$y$ coincide; otherwise it is bad.

The text states this for equidimensional $\Theta$; nothing below needs that. *Intrinsic form.* $y$ is good iff $\Theta$ is
constant on $\mathrm{supp}(\Theta)$ near $y$. Indeed, off the closed sheets not through $y$, $\Theta(z) \le \Theta(y)$, with
equality iff $z$ lies on all sheets through $y$ (Findings, item 23). *Checked by machine (V9.15):*
`Polyfold.EpGroupoid.LocalBranchingStructure.IsGoodPoint`, `Polyfold.EpGroupoid.LocalBranchingStructure.isGoodPoint_iff`.

**Lemma 9.2.3 (2017: 9.3) (goodness does not depend on the structure).** If $y$ is good for one local branching structure,
it is good for every structure whose domain contains $y$.

*Proof.* The intrinsic form of goodness does not mention the structure. $\square$

In the text's proof $Q(z) = V(y) \cap W(y)$ is presumably $Q(y)$ (possible misprint). *Checked by machine (V9.16):*
`Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_2_3`.

**Remark 9.2.4 (2017: 9.4).** (a) The good set is well defined; (b) near a good point $y$, $\Theta = \Theta(y) \cdot 1_M$
for a submanifold $M$ properly embedded near $y$. *Checked by machine (V9.17):* `Polyfold.EpGroupoid.remark_9_2_4_a`,
`Polyfold.EpGroupoid.remark_9_2_4_b`.

**Lemma 9.2.5 (2017: 9.4) (goodness along morphisms).** $s(\varphi)$ is good iff $t(\varphi)$ is good.

*Proof.* On a sheet $\mathbf W$ of $s$ around $\varphi$, $\hat\varphi = t \circ (s|\mathbf W)^{-1}$ is an sc-diffeomorphism
between neighbourhoods of $s(\varphi)$ and $t(\varphi)$ with $\Theta \circ \hat\varphi = \Theta$, so "$\Theta$ is constant
on its support near the point" passes from one to the other. $\square$

*Checked by machine (V9.18):* `Polyfold.EpGroupoid.lemma_9_2_5`.

**Definition 9.2.6 (2017: 9.5) (good and bad sets).** The good set and the bad set are the saturated subsets of the support
formed by the good and the bad points, by Lemma 9.2.5; the text refers here to "Remark 9.2.4 (c)", which has only (a) and
(b) (possible misprint; Findings, item 22). *Checked by machine (V9.19):* `Polyfold.EpGroupoid.goodSet`,
`Polyfold.EpGroupoid.badSet`.

**Lemma 9.2.7 (2017: 9.5) (good points are dense).** (1) The good set is open and dense in the support. (2) For an
$n$-dimensional structure at $x$, every sheet contains good points converging to $x$.

*Proof of (1).* Openness is the definition. For density, take an open $W \subseteq U(x)$ meeting the support. Shrink $W$ one
sheet at a time so that $M_U \cap W$ either lies in $M_j$ or misses it: if $M_U \cap W \not\subseteq M_j$, a point of $M_U
\cap W$ off the closed set $M_j$ has a neighbourhood $W' \subseteq W$ missing $M_j$, and the sheets already decided stay
decided. On the final $W$ all sheets through a point of $M_U \cap W$ contain $M_U \cap W$, so they coincide there, and every
point of $W \cap \mathrm{supp}(\Theta)$ is good. $\square$

*Proof of (2).* Apply the same shrinking inside a sheet $M_{i_0}$ near $x$. The point found lies on a family of sheets that
contain $M_{i_0}$ near it; it is good once each of them equals $M_{i_0}$ near it, which is invariance of domain for
submanifolds of equal dimension. That fact of Part I is not formalized; it is the hypothesis `HasDomainInvarianceAt`, which
on $\mathbb R^m$ follows from the inverse function theorem. $\square$

The density in (1) needs neither (2) nor equidimensionality, and (2) holds at every $x$, not only at bad points (Findings,
item 24). *Checked by machine (V9.20, V9.21):* `Polyfold.EpGroupoid.lemma_9_2_7_1_dense`,
`Polyfold.EpGroupoid.isNowhereDense_badSet`, `Polyfold.MPolyfold.HasDomainInvarianceAt`,
`Polyfold.EpGroupoid.lemma_9_2_7_2_rn`.

**Proposition 9.2.8 (2017: 9.3) (approaching a bad point).** At a bad point $x$, the sheets with one tangent space $L =
T_xM_i$ form a class $\Xi$, which splits as $I^1 \sqcup \cdots \sqcup I^p$ with sequences of good points converging to $x$
that lie on $M_i$ exactly for $i \in I^e$.

*How this is read.* The text proves this with Lemmas 9.2.9–9.2.11 (2017: 9.6–9.8), the sheets of the class being graphs over
a cone in $L$, and uses it to count $\sum_{i \in \Xi} \sigma_i$ by values of $\Theta$. The count needs only a *tangent
slice*: a finite set $F$ near $x$ meeting each sheet of the class exactly once and missing all other sheets, so that
$\sum_{i \in \Xi} \sigma_i = \sum_{y \in F} \Theta(y)$. Take a direction $h_0 \in L$ off the finitely many other tangent
spaces and a projection $Q$ onto $L$; for small $t > 0$ the slice is $\{y \mid Q(\varphi y - \varphi x) = t h_0,\ \|\varphi
y - \varphi x - t h_0\| < \varepsilon t\}$. It meets each sheet of the class once because the sheet is a graph over $L$
along the ray $t h_0$, and misses the other sheets because their tangent spaces do not contain $h_0$. The graph property
along rays is the hypothesis `IsGraphChartAt` on a general M-polyfold, proved on $\mathbb R^m$ by the inverse function
theorem; sheets of several dimensions ask one chart for all (`HasGraphChartAt`), and orientations a ball of foot points
(`HasGraphBallAt`) (Findings, item 25). *Checked by machine (V9.22):* `Polyfold.MPolyfold.HasTangentSlicesAt`,
`Polyfold.MPolyfold.IsGraphChartAt`, `Polyfold.MPolyfold.hasTangentSlicesAt_of_hasGraphChartsAt`,
`Polyfold.MPolyfold.hasGraphChartAt_rn`, `Polyfold.MPolyfold.hasTangentSlicesAt_rn`.

*Proof of Theorem 9.2.1.* At a good point the sum is $\Theta(y) \cdot T_yM$ for every structure. For two structures with
sheets of one dimension, group the sheets of both through $x$ by tangent set; for each class $L$ a slice meeting each sheet
of either structure with tangent space $L$ once gives $\sum_{T_xM_i = L} \sigma_i = \sum_{y \in F} \Theta(y) =
\sum_{T_xM'_j = L} \sigma'_j$, so the sums agree. In general split both structures by dimension: their dimensional parts agree near $x$ by
Proposition 9.1.12, so the tangent sums agree dimension by dimension; restricting a structure to where the dimensions of its
sheets are constant uses `HasLocallyConstantDimAt`. Given the independence, the section and its naturality are as above.
$\square$

So Theorem 9.2.1 holds for every branched ep⁺-subgroupoid of an ep-groupoid over $\mathbb R^m$, and in general under the
graph representation and the local constancy of the dimension. In Remark 9.1.3 (b) the two structures give the same tangent
sum $2 \cdot T_0(\mathbb R \times 0)$ at the bad origin, all four graphs being tangent to the axis there. The text writes
"the proposition" (p. 410) for the theorem and closes with "Theorem 9.2.8" (p. 418) (possible misprints; Findings, items 21,
22). *Checked by machine (V9.13, V9.14):* `Polyfold.EpGroupoid.theorem_9_2_1`,
`Polyfold.EpGroupoid.HasIndependentTangentSums`, `Polyfold.EpGroupoid.hasIndependentTangentSums_of_isOfDim`,
`Polyfold.EpGroupoid.hasIndependentTangentSums_of_hasGraphChartAt_of_hasLocallyConstantDimAt`,
`Polyfold.EpGroupoid.hasIndependentTangentSums_rn`.

## 4. The tangent $T\Theta$ and the boundary $\partial\Theta$ (pp. 418–422 (2017 pp. 306–309))

**Definition 9.2.12 (2017: 9.6) (the tangent of $\Theta$).** $T\Theta : TX \to \mathbb Q^+$ is $0$ over the complement of
the support and $T\Theta(h) = \sum_{h \in T_{p(h)}M_i} \sigma_i$ over $U(x)$.

Defined through $T_\Theta(p(h))$, $T\Theta$ needs no choice, agrees with the local formula by the independence of Theorem
9.2.1, and is a nonnegative functor on the tangent ep-groupoid. To be a branched ep⁺-subgroupoid it needs the $TM_i$ to be
smooth submanifolds of $TX$: they are closed sub-M-polyfolds, images of $Ts$, but that $Ts$ is an sc⁺-retraction is not
formalized, also on $\mathbb R^m$ (gap G.99; Findings, item 26). *Checked by machine (V9.23):*
`Polyfold.EpGroupoid.tangentTheta`, `Polyfold.EpGroupoid.tangentTheta_eq`, `Polyfold.EpGroupoid.isFunctorial_tangentTheta`,
`Polyfold.EpGroupoid.TangentBranchingHyp`,
`Polyfold.EpGroupoid.isBranchedEpSubgroupoid_tangentTheta_of_isSmoothSubmanifold`.

**Lemma 9.2.13 (2017: 9.9) (position relative to the boundary).** For $x \in M \cap \partial X$: (1) $d_M(x) = 0$ iff (2)
$T_xM \subseteq T^R_xX$.

*How this is read.* "$T_xM \subseteq T^R_xX$" is the inclusion of the chart image of $T_xM$ in the reduced tangent space
$E_z$ at the chart image $z$, independent of the chart. The text states "(1) $x \in \partial X$ and $d_M(x) = 0$ iff (2)";
as printed, (2) ⇒ (1) does not hold as we read it at interior points (a point of $\mathbb R^n$), so the lemma is read at
points of $M \cap \partial X$, where it is used (Findings, item 41).

*Proof.* (1) ⇒ (2): if $d_M(x) = 0$, $M$ has a chart without boundary near $x$, whose tangent space lies in $E_z$. (2) ⇒
(1): in a chart $M$ is the image of an sc⁺-retraction $s$ near $z$, with $T_zM \subseteq E_z$. The projection $p$ onto
$T_zM$ is injective on $M$ near $z$, by a level-1 contraction (the step "the image is $M$ near $0$", not spelled out in the
text), and by the inverse function theorem for $p \circ s$, $p(\cdot - z)$ is a chart of $M$ onto an open subset of $T_zM
\subseteq E_z$. So $d_M(x) = 0$. $\square$

The complement and the map $F$ of the text are not needed, and the boundary hypothesis is used by neither direction: at
every $x \in M$, $d_M(x) = 0$ iff $T_xM \subseteq T^R_xX$. *Checked by machine (V9.24):* `Polyfold.MPolyfold.lemma_9_2_13`,
`Polyfold.MPolyfold.lemma_9_2_13_two_one`, `Polyfold.ScRetraction.IsScPlus.exists_flat`,
`Polyfold.MPolyfold.subDegIndex_eq_zero_iff`, `Polyfold.MPolyfold.not_lemma_9_2_13_two_one`.

**Remark 9.2.14 (2017: 9.5).** $x \in \partial M$ iff $x \in \partial X$ and $T_xM \not\subseteq T^R_xX$. *Proof.* By Lemma
9.2.13 and $\partial M \subseteq \partial X$. $\square$ *Checked by machine (V9.25):*
`Polyfold.MPolyfold.remark_9_2_14_iff`.

**Proposition 9.2.15 (2017: 9.4) (the boundary weights).** (1) The boundary weight $\sum_{y \in \partial M_i} \sigma_i$ does
not depend on the structure. (2) It vanishes where $d_X(y) = 0$. (3) $\partial\Theta$, the boundary weight on $\partial X$
and $0$ off it, is a functor.

*Proof.* By Remark 9.2.14, $y \in \partial M_i$ iff $y \in \partial X$ and $T_yM_i$ is not in reduced position, so the
boundary weight is the part of $T_\Theta(y)$ on the tangent sets not in reduced position, which does not depend on the
structure by Theorem 9.2.1. If $d_X(y) = 0$ every tangent set is in reduced position. Functoriality is that of $T_\Theta$.
$\square$

(1) and (2) need neither $x \in \mathrm{supp}(\Theta) \cap \partial X$ nor that $\Theta$ be branched (Findings, item 43).
*Checked by machine (V9.26):* `Polyfold.EpGroupoid.boundaryTheta`, `Polyfold.EpGroupoid.proposition_9_2_15_1`,
`Polyfold.EpGroupoid.proposition_9_2_15_2`, `Polyfold.EpGroupoid.proposition_9_2_15_3`.

**Definition 9.2.16 (2017: 9.7) (the boundary of $\Theta$).** $\partial\Theta$ is characterized by (1)
$\mathrm{supp}(\partial\Theta) \subseteq \partial X$ and (2) the local formula at the points of
$\mathrm{supp}(\partial\Theta)$.

*As we read it, (1) and (2) do not characterize $\partial\Theta$ uniquely.* Condition (2) is asked only on the support of
the candidate, so the zero functor satisfies (1) and (2) for every $\Theta$; for $\Theta = 1$ on $[0, \infty)$,
$\partial\Theta(0) = 1 \ne 0$. With (2) asked at the points of $\mathrm{supp}(\Theta)$ and the candidate $0$ off
$\mathrm{supp}(\Theta)$, $\partial\Theta$ is unique. Before the definition the text cites "Proposition 9.2.13" (2017:
"Proposition 9.9"), presumably Proposition 9.2.15 (possible misprint; Findings, items 44, 45). *Checked by machine (V9.27):*
`Polyfold.EpGroupoid.IsBoundaryCharacterized`, `Polyfold.EpGroupoid.isBoundaryCharacterized_zero`,
`Polyfold.not_unique_isBoundaryCharacterized_halfLine`, `Polyfold.EpGroupoid.eq_boundaryTheta`.

**Remark 9.2.17 (2017: 9.6).** $\partial\Theta \le \Theta$, and $\partial\Theta$ is not $\Theta$ restricted to $\partial X$:
the indicator of the corner $0$ of $[0, \infty)$ has $\partial\Theta(0) = 0$, while $\Theta = 1$ on $[0, \infty)$ has
$\partial\Theta(0) = 1$. The remark's "In Section 9.5" refers to §9.3 (possible misprint; Findings, item 46). *Checked by
machine (V9.28):* `Polyfold.EpGroupoid.boundaryTheta_le`, `Polyfold.boundaryTheta_halfLineCorner`,
`Polyfold.EpGroupoid.boundaryTheta_one`.

## 5. Orientations (pp. 422–429 (2017 pp. 309–315))

An orientation of a finite-dimensional vector space is a class of bases. For a tangent set it is a set of frames, lists of
vectors of the set, whose chart images are the positive bases of an orientation of the chart image; a chart change acts
linearly, so this does not depend on the chart, and every tangent set has exactly two orientations.
$\widehat{\mathrm{Gr}}(x)$ is the group of formal sums of oriented tangent sets, and forgetting orientations maps it to
$\mathrm{Gr}(x)$, sending $(T, o) + (T, -o)$ to $2T$ (Findings, item 50). *Checked by machine (V9.29):*
`Polyfold.MPolyfold.IsOrientedAt`, `Polyfold.MPolyfold.exists_two_orientations`, `Polyfold.EpGroupoid.GrHat`,
`Polyfold.EpGroupoid.grForgetFunctor`.

**Definition 9.3.2 (2017: 9.8) (orientation of $\Theta$).** An orientation of $\Theta$ is a functor $\hat T_\Theta :
X^\infty \to \widehat{\mathrm{Gr}}(X)$ lifting $T_\Theta$ that is locally the oriented sum $\sum_i \sigma_i (T_yM_i,
o_i(y))$ of an oriented local branching structure, each $o_i$ a continuous orientation of $M_i$.

The lift of $T_\Theta$ uses the independence of Theorem 9.2.1 (Findings, item 51). *Checked by machine (V9.30):*
`Polyfold.MPolyfold.SubmanifoldOrientation`, `Polyfold.EpGroupoid.OrientedBranchingStructure`,
`Polyfold.EpGroupoid.IsOrientation`, `Polyfold.EpGroupoid.isOrientation_sum_rn`.

**Remark 9.3.3 (2017: 9.8) (many orientations).** The indicator of a point $p$ has the orientations $q \cdot (\{p\}, +) +
(1 - q) \cdot (\{p\}, -)$, $q \in (0,1) \cap \mathbb Q$: the weight $1$ can be split between the two orientations of a
$0$-dimensional tangent set in any way. *Checked by machine (V9.31):* `Polyfold.EpGroupoid.remark_9_3_3`.

**Lemma 9.3.4 (2017: 9.10) (orientations are determined at good points).** Two orientations of an $n$-dimensional $\Theta$
that agree at the good points agree everywhere.

*Without equidimensionality, as we read it, the lemma does not hold.* On $\mathbb R^2$ let $\Theta = 1_{\mathbb R \times
0} + 1_{\{0\}}$. The origin is bad, the good points are the other points of the line, and two orientations that orient the line
alike and the point oppositely agree at all good points and differ at the origin.

*Proof for $n$-dimensional $\Theta$.* At a bad $x$, take the sheets of both structures with one tangent set $L$ at $x$. Over
a ball of foot points in $L$ each of them is a graph (the hypothesis `HasGraphBallAt`), and the good points are dense on it,
by Lemma 9.2.7 (1). The relative orientation of two sheets of the class is the sign of the determinant of their chart
frames, which is locally constant if the frames are continuous on level $1$, the hypothesis `HasContinuousLevelOneOn`. So
the relative orientations at $x$ are those at nearby good points, where the two orientations agree, and the oriented sums at
$x$ agree class by class. $\square$

That good points of the first structure serve the second is the step supplied here; both hypotheses hold on $\mathbb R^m$
(Findings, item 53; gap G.100). *Checked by machine (V9.32):* `Polyfold.EpGroupoid.lemma_9_3_4`,
`Polyfold.EpGroupoid.lemma_9_3_4_of_hasGraphBallAt`, `Polyfold.EpGroupoid.lemma_9_3_4_rn`,
`Polyfold.lemma_9_3_4_mixed_dim_rn`.

**Example 9.3.5 (2017: 9.1) (two orientations of one $\Theta$).** With $\beta^{++}(s) = e(s) + e(-s)$, $\beta^{--} =
-\beta^{++}$, and $\beta^{+-}$, $\beta^{-+}$ obtained by switching between them at $0$, the pairs $G^{++}, G^{--}$ and
$G^{+-}, G^{-+}$ of graphs describe one $\Theta$. Orienting each graph by $\pm(1, \beta')$ gives orientations $\hat T^1$,
$\hat T^2$.

As stated, they coincide at the origin, differ at $(s, \beta^{++}(s))$ for $s > 0$, and no signs on the second pair
reproduce $\hat T^1$ near $0$. Two claims do not hold as we read them: the orientations also coincide for $s < 0$, where
$G^{+-} = G^{++}$ and $G^{-+} = G^{--}$ carry the same orientations; and the four sign choices on the first pair give four
different orientations, none of them $\hat T^2$, so there are at least five with weights $1$, and infinitely many with
fractional weights. A classification of all orientations is not formalized (gap G.101; Findings, item 54). *Checked by
machine (V9.33):* `Polyfold.example_9_3_5`, `Polyfold.example_9_3_5_eq_of_neg`, `Polyfold.orientedLift1_injective`,
`Polyfold.exampleT2_ne_orientedLift1`.

**Definition 9.3.6 (2017: 9.10) (tame $\Theta$).** $\Theta$ is tame if it has local branching structures on domains with the
natural $G_x$-action and the properness property whose sheets have tame induced structures (Part I, Definition 2.5.18). The
consequence that each $M_i$ is a manifold with boundary with corners is not formalized (gap G.102; Findings, item 55).
*Checked by machine (V9.34):* `Polyfold.EpGroupoid.TameBranchingStructure`, `Polyfold.EpGroupoid.IsTameBranched`.

**Lemma 9.3.7 (new in the 2021 edition) (equal tangent spaces, equal degeneracy).** For submanifolds $M_1$, $M_2$ with tame
induced structures, $T_yM_1 = T_yM_2$ implies $d_{M_1}(y) = d_{M_2}(y)$.

*Proof.* For a submanifold with tame induced structure, $d_M(y)$ is the codimension of the reduced part of the chart image
of $T_yM$, a number determined by that linear space and the partial quadrant of the chart of $Y$. Equal tangent spaces give
equal numbers. $\square$

Neither "$Y$ tame" nor "of the same dimension" is used; the text's "$T_0O \cap C = T^R_0O$" is read through the linearity of
the chart image (Findings, item 56). *Checked by machine (V9.35):* `Polyfold.MPolyfold.lemma_9_3_7`,
`Polyfold.MPolyfold.subDegIndex_eq_of_submanifoldTangent_eq`.

**Definition 9.3.8 (2017: 9.9) (boundary orientation).** For oriented $(M, o)$ and $y \in \partial M$ with $d_M(y) = 1$, a
basis $(a_1, \ldots, a_{n-1})$ of $T_y\partial M$ is positive iff $(e, a_1, \ldots, a_{n-1})$ is positive for an outward
$e$.

The convention orients a hyperplane $K \subseteq T_yM$ given $e \notin K$, unchanged by $e \mapsto ce + k$, $c > 0$, $k \in
K$. That $K = T^R_yM$ and the outward side come from the cones $C_yM$ is not formalized: $K$ and $e$ are data (gap G.103;
Findings, item 57). *Checked by machine (V9.36):* `Polyfold.MPolyfold.boundaryFrames`,
`Polyfold.MPolyfold.isOrientedAt_boundaryFrames`, `Polyfold.MPolyfold.boundaryFrames_eq`.

**Proposition 9.3.9 (new in the 2021 edition) (the boundary orientation of $\Theta$).** The oriented sum at $y$ split by the
degeneracy index of the sheets, (9.11), does not depend on the structure, and hence neither does the boundary orientation
(9.12) built from its degree-$1$ part.

*Proof.* By Lemma 9.3.7 tangent sets of sheets of different degree at $y$ never coincide, so two oriented structures with
the same oriented sum at $y$ have the same degree-$\ell$ parts for every $\ell$. Apply the boundary operation, a function of
the oriented tangent set, to the degree-$1$ part. $\square$

*Checked by machine (V9.37):* `Polyfold.EpGroupoid.eq_9_11`, `Polyfold.EpGroupoid.proposition_9_3_9`.

**Definition 9.3.10 (2017: 9.11).** $\hat T_{\partial\Theta}$ is (9.12) on the support and $0$ off it; the continuity of the
boundary orientation along $\partial M$ and its extension to the faces (Figure 9.1) are not formalized (gap G.103; Findings,
item 58). *Checked by machine (V9.38):* `Polyfold.EpGroupoid.boundaryLift`.

## 6. The geometry of branching (pp. 429–436 (2017 pp. 315–322))

Integration needs that, off a null set, sheets either coincide or meet negligibly. §9.4 makes this precise for
finite-dimensional manifolds, formalized for Mathlib manifolds with corners.

**Definition 9.4.1 (2017: 9.12) (relative tangent spaces and essential points).** For $K \subseteq M$ and $z \in K$,
$T^K_zM$ is the span of the limits of $\varphi(z_k)/|\varphi(z_k)|$ for $z_k \to z$ in $K \setminus \{z\}$, in a chart
$\varphi$ centred at $z$; $z$ is essential if it is a limit of points of $K$ at which $T^K M$ is all of $TM$.

In a chart it is the span of Mathlib's tangent cone of the image of $K$, mapped by the derivative under chart changes. For
two crossing lines in $\mathbb R^2$ the essential set is the crossing point. *Checked by machine (V9.39):*
`Polyfold.relTangent`, `Polyfold.relTangent_eq_map`, `Polyfold.essentialSet`, `Polyfold.essentialSet_crossLines`.

**Lemma 9.4.2 (2017: 9.11).** The essential set of $K$ is closed in $K$. *Proof.* It is a closure taken in $K$. $\square$
*Checked by machine (V9.40):* `Polyfold.lemma_9_4_2`.

**Lemma 9.4.3 (2017: 9.12) (Property (T) after shrinking).** Every oriented local branching structure has, on a smaller
domain, Property (T): the orientation relation of two sheets with the same tangent space at a common point is the same at
every common point with the same tangent space. Not formalized: it needs the continuity of the change-of-frame determinant
of two sheets along their intersection (gap G.104; Findings, item 71).

**Lemma 9.4.4 (2017: 9.13) (essential points do not depend on the reference sheet).** A point of $K(i, i') = M_i \cap
M_{i'}$ is essential for $K(i, i') \subseteq M_i$ iff for $K(i, i') \subseteq M_{i'}$.

*As we read it, this needs sheets of one dimension.* $\mathbb R \times 0$ as a subset of the line is essential at every
point, as a subset of $\mathbb R^2$ nowhere. For an $n$-dimensional $\Theta$ the text's argument in a chart applies; for
sheets of an M-polyfold the lemma is a field of the structure `SheetGeometry`, satisfiable by graphs in $\mathbb R^2$ (gap
G.105; Findings, item 72). *Checked by machine (V9.42):* `Polyfold.MPolyfold.SheetGeometry`,
`Polyfold.lemma_9_4_4_mixed_dim`, `Polyfold.graphSheetGeometry`.

**Definition 9.4.5 (2017: 9.13) (measure zero).** $A \subseteq M$ has measure zero if its images in all charts have Lebesgue
measure zero. *Checked by machine (V9.43):* `Polyfold.IsMeasureZero`, `Polyfold.isMeasureZero_iUnion`.

**Lemma 9.4.6 (2017: 9.14) (non-essential points are negligible).** The non-essential points of any $K \subseteq M$ form a
set of measure zero.

*Proof.* At a point where $T^K_zM \ne T_zM$ there is a unit direction $v$ off the span, and the points of $K$ near $z$ lie
outside a cone around $v$. A cone has positive density at its vertex, so $z$ is not a Lebesgue density point of $K$; by
Lebesgue's density theorem such points form a null set. A non-essential point has a neighbourhood in $K$ of such points, by
Lemma 9.4.2. $\square$

(Findings, item 70.) *Checked by machine (V9.44):* `Polyfold.lemma_9_4_6`, `Polyfold.isMeasureZero_setOf_relTangent_ne_top`.

**Definition 9.4.7 (2017: 9.14) ($y$-equivalence).** Sheets $i$, $i'$ through $y$ are $y$-equivalent if they are joined by a
chain of sheets with $y$ essential in each consecutive intersection; equivalent sheets have the same tangent space at $y$,
and $P_y$ is the set of classes. *Checked by machine (V9.45):* `Polyfold.MPolyfold.SheetGeometry.YEquiv`,
`Polyfold.MPolyfold.SheetGeometry.equivalence_yEquiv`.

**Lemma 9.4.8 (2017: 9.15).** The points $y \in M_U$ with $\#P_y \ge 2$ form a null set.

*Proof.* If $y$ lies on $M_i$ and has two classes, the class of $i$ omits some $j$ through $y$, so $y$ is a non-essential
point of $K(i, j)$ inside $M_i$; by Lemma 9.4.6 these points are null in $M_i$. $\square$

The text concludes with $\bigcup_{j, j'} K(j, j')^{ne}$; as we read it, $K(j, j')^{ne}$ is null only in $M_j$ and $M_{j'}$,
and the proof needs $K(i, j)^{ne}$ inside each sheet $M_i$ through $y$ (Findings, item 73). *Checked by machine (V9.46):*
`Polyfold.MPolyfold.SheetGeometry.lemma_9_4_8`, `Polyfold.MPolyfold.SheetGeometry.isNullIn_diff_MStar`.

**Proposition 9.4.9 (2017: 9.5) (the generic form of an oriented structure).** Off a null set, $M_U$ is the disjoint union
of the pieces $M^J_U$ on which $I_y = J$, and on $M^J_U$: $\Theta = \sigma_J$, $T_\Theta = \sigma_J T^J$ and $\hat
T_\Theta = a_J (T^J, o^a_J) + b_J (T^J, o^b_J)$ with $a_J + b_J = \sigma_J$ and $o^a_J = -o^b_J$.

*Proof.* The null set is that of Lemma 9.4.8. On $M^J_U$ all sheets of $J$ are $y$-equivalent, so they have one tangent set
$T^J$. By Property (T) their orientations at $y$ fall into two opposite classes, with weights $a_J$, $b_J$. $\square$

"$o^a_J = -o^b_J$" is read as "$o^a_J \ne o^b_J$ on the same tangent set", which has exactly two orientations (Findings,
item 74). *Checked by machine (V9.47):* `Polyfold.EpGroupoid.proposition_9_4_9`.

**Proposition 9.4.10 (2017: 9.6) (comparing two oriented structures).** Two oriented structures on $U(x)$ with the same
weight sums and the same oriented sums agree off a null set, piece by piece.

*Proof.* Take the union of the two structures, which describes $2\Theta$, and its generic set from Proposition 9.4.9. Cut it
by the finitely many values of $y \mapsto (I_y, I'_y, J_+(y), J'_+(y))$, $J_+$ the positively oriented class; on each piece
both structures have the constant form of Proposition 9.4.9 with the same weights. $\square$

Property (T) is not needed. The two structures of Example 9.3.5 satisfy the hypotheses, and at the origin $G^{++}$ and
$G^{--}$ are tangent but not equivalent (Findings, item 74). *Checked by machine (V9.48):*
`Polyfold.EpGroupoid.proposition_9_4_10`, `Polyfold.example935_hypotheses_9_4_10`, `Polyfold.example935_two_le_numClasses`.

## 7. Measure zero, σ-algebras and isotropy factors (pp. 436–452 (2017 pp. 322–331))

§9.5 integrates sc-differential $n$-forms over an oriented, tame, compact, $n$-dimensional $\Theta$, with $S
= |\mathrm{supp}(\Theta)|$. The forms of §8.2 are not formalized (gaps G.74, G.80); everything that does not involve them is.

**Definition 9.5.1 (2017: 9.15) (sets of measure zero in $S$).** $A \subseteq S$ has measure zero if every $x \in
\mathrm{supp}(\Theta)$ has a local branching structure on a suitable $U(x)$ whose preimages $M_i \cap \pi^{-1}(A)$ have
measure zero in the sheets.

*How this is read.* Measure zero in the sheets of an M-polyfold is not available in the project, so it is a system of null
sets on a class of sheets: a σ-ideal in each sheet, local, induced alike by two sheets of the class on their overlap, a
nonempty sheet not null in itself. "A suitable $U(x)$" is a tame structure, Definition 9.3.6; compactness and orientation
are not used (gap G.106; Findings, item 80). *Checked by machine (V9.49):* `Polyfold.SheetNullSets`,
`Polyfold.MPolyfold.SheetMeasureGeometry`, `Polyfold.EpGroupoid.IsMeasureZeroSupp`, `Polyfold.EpGroupoid.HasTameSheetsIn`.

**Lemma 9.5.2 (2017: 9.16) (independence of the choice).** The notion of measure zero does not depend on the local branching
structures chosen.

*Proof.* Suppose some structure at every point has null preimages of $A$, and let $M'_j$ be a sheet of any structure with
sheets in the class. Near a point $z$ of $M'_j \cap \pi^{-1}(A)$, $M'_j$ lies in the support, which near $z$ is the union of
the finitely many sheets $M_i$ of a structure at $z$ with null preimages. So $M'_j \cap \pi^{-1}(A)$ is covered near each of
its points by finitely many sheets in which it is null; by the transfer property and locality it is null in $M'_j$.
$\square$

The text cites the literature. *The transfer property, as we read it, needs one dimension*: the axis $\mathbb R \times 0$ is
null in the sheet $\mathbb R^2$ and not in itself. So the lemma is proved for sheets of one class, as for the
$n$-dimensional structures of an $n$-dimensional $\Theta$; that all its structures are $n$-dimensional is Proposition 9.1.12
(gaps G.97, G.106; Findings, item 81). *Checked by machine (V9.50):* `Polyfold.EpGroupoid.lemma_9_5_2`,
`Polyfold.EpGroupoid.isSigmaIdeal_isMeasureZeroSupp`, `Polyfold.EpGroupoid.not_isMeasureZeroSupp_orbitSupp`,
`Polyfold.isNull_transfer_mixed_dim`.

**Definition 9.5.3 (2017: 9.16) (the σ-algebra $L(S)$).** $L(S)$ is the smallest σ-algebra on $S$ containing the Borel sets
and the sets of measure zero; the text adds that it is obtained from the Borel sets by adding the sets of measure zero.

*Proof of the remark, read as a completion.* For a σ-ideal $\mathcal N$, the sets $A$ with $A \,\Delta\, B \in \mathcal N$
for some Borel $B$ form a σ-algebra, since $\bigcup_k A_k \,\Delta\, \bigcup_k B_k \subseteq \bigcup_k (A_k \,\Delta\,
B_k)$; it contains the Borel sets and $\mathcal N$, and lies in every σ-algebra containing both. So $K \in L(S)$ iff $K
\,\Delta\, B$ has measure zero for a Borel $B$. $\square$

The form $K = B \cup N$ would need Borel null hulls. On $\mathbb R^2$ with $\Theta = 1$ some member of $L(S)$ is not Borel:
the $2^{\mathfrak c}$ subsets of the null axis are in $L(S)$, and there are only $\mathfrak c$ Borel sets (Findings, item
82). *Checked by machine (V9.51, V9.53):* `Polyfold.EpGroupoid.lebesgueSigma`, `Polyfold.measurableSet_borelNullSigma_iff`,
`Polyfold.EpGroupoid.remark_9_5_3`, `Polyfold.lebesgueSigma_theta935`,
`Polyfold.exists_mem_lebesgueSigma_not_borel_thetaPlane`.

**Theorem 9.5.4 (2017: 9.2) (branched integration).** For oriented, tame, compact, $n$-dimensional $\Theta$ there is a
unique linear map $\omega \mapsto \mu_\omega$ from sc-differential $n$-forms to signed measures on $(S, L(S))$, given on
$|U(x)|$ by $\frac{1}{\#G_x} \sum_i \sigma_i \int_{M_i \cap \pi^{-1}(\cdot)} \omega$; Theorem 9.5.5 (new in the 2021
edition) is the version with $\#G^{\mathrm{eff}}_x$ under LUC. Not formalized, with Definition 9.5.6, (9.21)–(9.22) and the
measure identities of Lemma 9.5.7 and Remark 9.5.8 (gap G.107; Findings, item 85).

Its proof compares local measures on overlaps: the combinatorics is Proposition 9.4.10, the group theory the following
results, of which the isotropy and set parts are proved.

**Lemma 9.5.9 (2017: 9.18) (restrictions, the $G_x$-case).** For $y \in U(x)$ with stabilizer $H \cong G_y$ in $G_x$:
$\#(G_x/H) \cdot \#G_y = \#G_x$; inside any neighbourhood of $y$ there is an open $V$ with $\varphi_g(V) = V$ for $g \in H$
and $\varphi_g(V) \cap V = \emptyset$ otherwise; and for $K \subseteq |M_U \cap V|$ the preimage $M_U \cap \pi^{-1}(K)$ is
the disjoint union, over coset representatives $r$, of $\varphi_r(M_U \cap V \cap \pi^{-1}(K))$.

*Proof.* $H \cong G_y$ by the natural representation, and Lagrange's theorem counts. Separate $y$ from the finitely many
$\varphi_g(y) \ne y$ and make the neighbourhood $H$-invariant. As $\Theta$ is a functor, $\varphi_g$ maps $M_U$ to itself,
so the preimage of $K$ is the union of the translates of its part in $V$, disjoint for different cosets. $\square$

*Checked by machine (V9.54):* `Polyfold.EpGroupoid.NaturalRep.card_quotient_stabilizer_mul_card_isotropy`,
`Polyfold.EpGroupoid.NaturalRep.exists_slice`, `Polyfold.EpGroupoid.NaturalRep.MU_inter_preimage_eq_iUnion_quotient`,
`Polyfold.EpGroupoid.NaturalRep.pairwise_disjoint_image_Φ_out`.

**Lemma 9.5.10 (new in the 2021 edition) (restrictions, the effective case).** $\#T_x \cdot \#G^{\mathrm{eff}}_x = \#G_x$
for the subgroup $T_x$ acting trivially near $x$; under LUC, $T_x$ is the kernel of the representation, lies in $H$, and
corresponds to $T_y$, so that (9.23) $\#(G_x/H) \cdot \#G^{\mathrm{eff}}_y = \#G^{\mathrm{eff}}_x$.

*Proof.* Divide the formula of Lemma 9.5.9 by $\#T_x = \#T_y$. $\square$ *Checked by machine (V9.55):*
`Polyfold.EpGroupoid.NaturalRep.kerΦ_eq_trivialSubgroup`, `Polyfold.EpGroupoid.NaturalRep.card_trivialSubgroup_eq`,
`Polyfold.EpGroupoid.NaturalRep.card_quotient_stabilizer_mul_card_effIsotropy`.

**Lemma 9.5.11 (2017: 9.19) (morphism invariance).** For $\varphi : x \to x'$, $\#G_x = \#G_{x'}$ and
$\#G^{\mathrm{eff}}_x = \#G^{\mathrm{eff}}_{x'}$, by conjugation with $\varphi$; and $|M_U| = |M_{U'}|$ for any map $\hat\varphi$ of $U$ onto $U'$
with $|\hat\varphi(z)| = |z|$. The "change of variables" in the integrals is not stated (Findings, item 84). *Checked by
machine (V9.56):* `Polyfold.EpGroupoid.card_isotropy_eq_of_mor`, `Polyfold.EpGroupoid.card_effIsotropy_eq_of_mor`,
`Polyfold.EpGroupoid.image_π_MU_eq`.

**Proposition 9.5.13 (new in the 2021 edition) (effective and reduced integrals).** (1) For effective $X$ the two integrals
agree; (2) under LUC the effective integral on $X$ is the integral on the reduced ep-groupoid $X_R$. What is proved is the
equality of the normalizing factors: $\#G^{\mathrm{eff}}_x = \#G_x$ for effective $X$, and $\#G^{\mathrm{eff}}_x = \#G^R_x$,
the functors and local branching structures of $X$ and $X_R$ being the same (Findings, item 84). *Checked by machine
(V9.57):* `Polyfold.EpGroupoid.card_effIsotropy_eq_of_isEffective`, `Polyfold.EpGroupoid.card_effIsotropy_eq_reduced`.

**Definition 9.5.14 (2017: 9.17) (the σ-algebra $L(\partial S)$).** With $(n-1)$-dimensional measure zero in the boundaries
$\partial M_i$, a set $K \subseteq \partial S = |\mathrm{supp}(\partial\Theta)|$ has measure zero if its boundary preimages
are null; $L(\partial S)$ is generated by the Borel sets of $\partial S$ and these sets. The notion does not depend on the
structures by the proof of Lemma 9.5.2, which here uses the independence of Theorem 9.2.1 through $\partial\Theta$. Measure
zero face by face, and an example with $\partial S \ne \emptyset$, are not formalized (gap G.108; Findings, item 83).
*Checked by machine (V9.52):* `Polyfold.EpGroupoid.IsMeasureZeroBoundary`,
`Polyfold.EpGroupoid.isMeasureZeroBoundaryAll_of`, `Polyfold.EpGroupoid.lebesgueSigmaBoundary`.

**Theorem 9.5.15 (2017: 9.3) (canonical boundary measures).** $(n-1)$-forms define signed measures on $(\partial S,
L(\partial S))$ by integrals over the $\partial M_i$ with the boundary orientation; Theorem 9.5.16 (new in the 2021 edition)
is the effective version. Not formalized (gap G.109).

**Theorem 9.5.17 (2017: 9.4) (Stokes' theorem).** If $X$ admits sc-smooth partitions of unity,
$\mu^{\partial\Theta}_\omega(\partial S) = \mu^{\Theta}_{d\omega}(S)$ for every $(n-1)$-form $\omega$; Theorem 9.5.18 (new
in the 2021 edition) is the effective version. Not formalized, with Remark 9.5.20 (gap G.110; Findings, item 85). Remarks
9.5.12 and 9.5.19 discuss open questions and have no formal content.

## 8. Appendix: the proof of Proposition 9.1.12 (pp. 452–457, new in the 2021 edition)

The proof compares two structures dimension by dimension from the top. Where the text removes sets "of measure zero" and
moves a point slightly, the formalization uses a covering lemma: a nonempty open piece of a $k$-dimensional submanifold is
not covered by finitely many closed submanifolds of smaller dimension, since $A \cap W \subseteq N$ near $a$ forces $\dim_a
A \le \dim_a N$ (Findings, item 90). *Checked by machine:* `Polyfold.MPolyfold.HasDimAt.le_of_inter_subset`,
`Polyfold.MPolyfold.exists_mem_forall_notMem`.

**Lemma 9.6.1 (the top dimension).** Two local branching structures at $x$ have the same top dimension, which defines
$\dim_\Theta(x)$.

*Proof.* If the first has a $k$-dimensional sheet and the second none of dimension $\ge k$, a point of that sheet off the
sheets of the second (the covering lemma) has $\Theta > 0$ and $\Theta = 0$. $\square$ *Checked by machine (V9.58):*
`Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_1`, `Polyfold.EpGroupoid.localTopDim_eq`.

**Lemma 9.6.2 (the top-dimensional union).** The unions $M^k_U$ of the top-dimensional sheets of two structures agree on the
common domain. *Proof.* A point of $M^k_U$ outside the closed set $M'^k_{U'}$ has nearby points of the same top sheet off
$M'^k_{U'}$ and, by the covering lemma, off the lower-dimensional sheets of the second structure, where $\Theta$ would be
both positive and $0$. $\square$ *Checked by machine (V9.59):* `Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_2`.

**Definition 9.6.3 (top-good points).** $y \in M^k_U$ is top-good if near $y$ all top-dimensional sheets through $y$
coincide. At points top-good for both structures, the top parts $\Theta_k$ agree: near such a point both are $\sigma \cdot
1_M$, and $\sigma$ is $\Theta$ at a point of $M$ off the lower-dimensional sheets. *Checked by machine (V9.60):*
`Polyfold.EpGroupoid.LocalBranchingStructure.IsTopGoodPoint`,
`Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_isTopGoodPoint`.

**Lemma 9.6.4 (top-goodness is intrinsic).** A point top-good for one structure is top-good for the other.

*How this is read.* The text argues "similarly as for good points". This needs that the top weight of the second structure
at $y$ is the $\sigma$ read off $\Theta$, which the text does not show: a priori the second structure could have, through
$y$, several top-dimensional sheets with different tangent spaces. The step is proved from the graph representation by
grouping the top sheets of both structures by tangent space and taking, for each class, one slice for both families that
avoids the lower-dimensional sheets; on $\mathbb R^m$ it holds in all dimensions (Findings, item 91). *Checked by machine
(V9.61):* `Polyfold.MPolyfold.TopMultiplicity`, `Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4`,
`Polyfold.EpGroupoid.LocalBranchingStructure.lemma_9_6_4_of_hasGraphChartAt`, `Polyfold.MPolyfold.topMultiplicity_rn`.

**Proposition 9.6.5 (top-bad points).** At a top-bad $x$, each class of top-dimensional sheets with one tangent space splits
into subfamilies approached by top-good points, and $\Theta_k(x) = \sum$ over classes of the values of $\Theta$ there (p.
457), independently of the structure.

*Proof.* Under the graph representation each class has, inside every neighbourhood of $x$, a finite top slice meeting each
sheet of the class once and missing the other top sheets and the lower-dimensional ones; its $\Theta$-values sum to the
weight of the class. One slice can be chosen for the sheets of both structures, so both class weights are the same sum.
$\square$

The common slice supplies the independence, which the text asserts. In (1) "$I_k = I^1 \sqcup \cdots \sqcup I^p$" reads as
the class $\Xi = I^1 \sqcup \cdots \sqcup I^p$, the points $x^k_e$ on p. 457 are presumably the $x^e_j$, and "This completes
the proof of Proposition 9.6.5" refers to Proposition 9.1.12 (possible misprints; Findings, items 91, 92). *Proof of
Proposition 9.1.12.* With the top parts agreeing near $x$, subtract them from both structures and repeat in lower
dimensions. $\square$ *Checked by machine (V9.62):* `Polyfold.EpGroupoid.LocalBranchingStructure.proposition_9_6_5`,
`Polyfold.EpGroupoid.LocalBranchingStructure.dimPart_topDim_eq_of_hasGraphChartAt`,
`Polyfold.EpGroupoid.LocalBranchingStructure.dimPartsAgreeNear_of_hasGraphChartAt`.

Sections 9.6.2 and 9.6.3 of the appendix discuss open questions on branched ep⁺-subgroupoids and have no formal content.

## 9. Witnesses: the hypotheses can hold

Every hypothesis of the chapter is satisfied by an example, all in Lean (Findings, items 100–102). The hypotheses of §§9.2
and 9.6.1 (graph charts, slices, local constancy of the dimension, invariance of domain, `TopMultiplicity`, level-1
continuity of frames) hold on every ep-groupoid over $\mathbb R^m$, where Proposition 9.1.12, Theorem 9.2.1, Lemmas 9.2.7
(2), 9.3.4 and 9.6.4 and Proposition 9.6.5 hold without hypotheses: `Polyfold.MPolyfold.hasGraphChartAt_rn`,
`Polyfold.MPolyfold.hasLocallyConstantDimAt_rn`, `Polyfold.MPolyfold.hasDomainInvarianceAt_rn`,
`Polyfold.MPolyfold.topMultiplicity_rn`, `Polyfold.hasContinuousLevelOneOn_rn`. `TangentBranchingHyp` holds for the zero
functor (`Polyfold.EpGroupoid.tangentBranchingHyp_zero`). Example 9.3.5 has Property (T), graphs in $\mathbb R^2$ form a
`SheetGeometry` and a `SheetMeasureGeometry`, and every structure on $\mathbb R^n$ restricts to a tame one
(`Polyfold.propertyT_example935B1`, `Polyfold.graphSheetMeasureGeometry`, `Polyfold.hasTameSheetsIn_trivial_rn`). No witness
of Lemma 9.2.13 at a boundary point and none of $L(\partial S)$ with $\partial S \ne \emptyset$ is constructed.

## 10. Summary of what was silently assumed, now made explicit

| Where | HWZ say | What is actually needed |
|---|---|---|
| p. 402, Remark 9.1.1 (2017: 9.1) | $\dim T_mM$ locally constant | a level-0 argument; a hypothesis in general, proved on $\mathbb R^m$ |
| pp. 404–405, Lemma 9.1.7 (2017: 9.2) | $M_{(i,g)} = g * M_i$ | that $\Phi(g)(M_i)$ is a properly embedded submanifold through $x$ |
| pp. 407–408, Prop. 9.1.11 (2017: 9.2) | a unique decomposition | not unique as we read it ($1_L = 1_{\{0\}} + 1_{L \setminus 0}$); a condition tying $\Theta_k$ to the structures |
| p. 412, Lemma 9.2.7 (2) (2017: 9.5 (2)) | the point is "clearly" good | invariance of domain for submanifolds |
| pp. 413–418, Prop. 9.2.8, Lemmas 9.2.9–9.2.11 (2017: 9.3, 9.6–9.8) | graphs over cones; sequences of good points | graphs along rays in one chart for all dimensions; slices count the weights |
| p. 418, Def. 9.2.12 (2017: 9.6) | $T\Theta$ is a branched ep⁺-subgroupoid | $TM_i$ smooth submanifolds of $TX$ (open) |
| p. 419, Lemma 9.2.13 (2017: 9.9) | (2) ⇒ "$x \in \partial X$ and $d_M(x) = 0$" | $x \in \partial X$ as a standing assumption; injectivity of the projection on $M$ |
| p. 421, Def. 9.2.16 (2017: 9.7) | (1), (2) characterize $\partial\Theta$ | (2) on $\mathrm{supp}(\Theta)$ and $0$ off it |
| p. 423, Lemma 9.3.4 (2017: 9.10) | the good points determine the orientation | $n$-dimensional $\Theta$; common good points for both structures |
| p. 425, Example 9.3.5 (2017: 9.1) | "otherwise different", "four possibilities" | they agree for $s < 0$; at least five |
| p. 427, Def. 9.3.8 (2017: 9.9) | $T_y\partial M$, the outward $e$ | data here; their construction from $C_yM$ open |
| p. 431, Lemma 9.4.4 (2017: 9.13) | "left to the reader" | sheets of one dimension |
| p. 432, Lemma 9.4.8 (2017: 9.15) | $\bigcup K(j, j')^{ne}$ | $K(i, j)^{ne}$ inside each $M_i$ |
| p. 435, Prop. 9.4.10 (2017: 9.6) | Property (T) | not needed |
| p. 437, Lemma 9.5.2 (2017: 9.16) | cited, no proof | the transfer of null sets, which needs one dimension |
| p. 438, the remark after Def. 9.5.3 (2017: 9.16) | add the null sets | the completion $K \,\Delta\, B$ null |
| pp. 453–454, Lemmas 9.6.1, 9.6.2 | "measure zero", "move $z$ slightly" | a topological covering lemma |
| p. 455, Lemma 9.6.4 | "similarly as good points" | the top weight of the second structure; a common slice |
| p. 457, the formula for $\Theta_k(x)$ | independent of the structure | one slice for both structures |

**Checked by machine.** The chapter is formalized in Lean 4 against Mathlib in the 25 files of `Polyfold/Chapter9/` imported
by the root module, from `Basic.lean` to `MeasureEffective.lean` (the `WIP_*` files there are not part of it); the
paragraphs "*Checked by machine*" name the declarations. Formalized: all definitions of §§9.1–9.4 and §9.6.1 and those of
§9.5 that do not involve forms; Theorem 9.2.1, Propositions 9.1.12 and 9.6.5 and Lemmas 9.2.7 (2), 9.3.4 and 9.6.4 for every
ep-groupoid over $\mathbb R^m$ and in general under the graph representation; the other lemmas, propositions and remarks of
§§9.1–9.4 and §9.6.1 with formal content, several in stronger forms; Lemma 9.5.2 for structures with sheets of one class;
and the isotropy and set parts of Lemmas 9.5.9–9.5.11 and Proposition 9.5.13. Four uniqueness or independence claims do not
hold as we read them, each with a counterexample in Lean: Proposition 9.1.11, Definition 9.2.16, Lemma 9.3.4 without
equidimensionality, and Lemmas 9.4.4 and 9.5.2 across dimensions; and Lemma 9.2.13 is read at boundary points. Not
formalized: the global part of Proposition 9.1.11, Remark 9.1.4, Proposition 9.1.9, Lemma 9.4.3, the boundary geometry of
Definitions 9.3.8 and 9.3.10, and branched integration, the boundary measures and Stokes' theorem (gaps G.93–G.110). The
machine-checked statements are listed in `Exposition/Verification.md` (V9.1–V9.62), compared with the text in
`Exposition/polyfold-beside-lean.html` and retold in `Exposition/ProofByProof.md`, Part IX. The findings are
`Exposition/Findings.md`, "Chapter 9", items 1–9, 20–26, 40–46, 50–58, 70–74, 80–85, 90–93 and 100–102 (numbered in blocks;
the gaps in the numbering are unused numbers).