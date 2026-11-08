# Chapter 7. Ep-groupoids: local symmetries, orbit spaces and partitions of unity (HWZ Part II, Chapter 7, pp. 287–356 (2017 pp. 225–256))

*Hofer–Wysocki–Zehnder, "Polyfold and Fredholm Theory", Part II, Chapter 7 (arXiv 1707.08941, pp. 225–256),
rewritten for a first-year graduate student who knows manifolds and finite group actions and wants to know how
polyfold theory describes problems with local symmetries. Every formalized statement is proved; what is not formalized
is marked. Where the Lean formalization found a gap or a shorter route, the text follows the Lean. Part II has no 2014
preprint: its statement numbers and printed pages are those of the book (Springer 2021), with the 2017 text's in
parentheses (see `BookConcordance.md`). Results of Part I are cited in the same way, by their 2021 numbers with the
2017 numbers in parentheses; the preprint numbers are in the concordance. Conventions: the objects $X$ and the morphisms $\mathbf X$ of an ep-groupoid carry
M-polyfold structures, and an M-polyfold is Hausdorff and paracompact (Definition 2.3.4 (2017: 2.8)); $|X|$ carries the quotient
topology; "an open neighbourhood $U(x)$ equipped with the natural $G_x$-action" is a chosen datum, a *natural
representation* (§3), never a hypothesis about all such neighbourhoods. The findings cited are those of `Findings.md`,
"Chapter 7".*

---

## 0. Two identical beads on a wire: what is the space of their states?

Two identical beads slide on a straight wire. With labels, a state is a pair $(a,b)\in\mathbb R^2$. Without labels, $(a,b)$ and
$(b,a)$ are the same state, so the space of states is the quotient of $\mathbb R^2$ by the swap, which as a topological space is the
closed half-plane $\{a\le b\}$. As a smooth object the half-plane does not describe the problem. In the coordinates $u = (a+b)/2$,
$v = (b-a)/2$ the swap is $(u,v)\mapsto(u,-v)$ and the quotient map is $(u,v)\mapsto(u,|v|)$. The motion $a(t) = t$, $b(t) = -t$, in which the
beads pass through each other at $t = 0$, is the same motion as the one in which they bounce off each other; upstairs it is
the smooth path $v(t) = -t$, but in the half-plane it is $t\mapsto(0,|t|)$, which has a corner. Likewise the distance $|b-a| = 2|v|$
between the beads is a function of the state, continuous and invariant under the swap, and not smooth on $\mathbb R^2$, although
it is a smooth coordinate of the half-plane. The smooth invariant functions on $\mathbb R^2$ are the smooth functions of $u$ and $v^2$
(a theorem of Whitney on even functions). Neither the topology of the half-plane nor its structure as a manifold with
boundary records which paths and functions are the smooth ones. The pair "$\mathbb R^2$ with the swap" does.

An *ep-groupoid* keeps exactly this pair. Here its objects are the points of $X = \mathbb R^2$, and there is one morphism
$(g,y):y\to g\cdot y$ for every $g\in\{1,\text{swap}\}$ and every $y$, with source $s(g,y) = y$ and target $t(g,y) = g\cdot y$. The *orbit
space* $|X|$ is the half-plane, and the *isotropy group* $G_y$ of a point is its stabilizer, trivial off the diagonal and of
order two on it. An ep-groupoid need not come from a global group action, but near every object it looks like one, the
action of the finite group $G_x$ on a neighbourhood of $x$ (Theorem 7.1.13 (2017: 7.1)). It is the polyfold version of an étale proper Lie
groupoid, and Part II uses it to describe Fredholm problems with local symmetries, as orbifolds describe spaces with
them. Chapter 7 develops the basic theory: the definition (§1), the orbit space and the isotropy groups (§2), the local
model (§3), ep-subgroupoids (§4), the effective case and the reduction of symmetries that act trivially (§5), the
topology of $|X|$ and the index lift (§6), paracompact orbit spaces and proper subsets (§7), and invariant sc-smooth
partitions of unity (§8). §9 records the examples that show the hypotheses can hold, and §10 returns to identical
particles on a line, with two and with three beads.

The formalization changed the text in these places. The natural representation of Theorem 7.1.13 (2017: 7.1) is taken on a
*connected* neighbourhood, which the text chooses on 2017 p. 231 but does not state, and the local path connectedness of
M-polyfolds that provides it is proved (§3). The remark after Definition 7.1.7 (2017: 7.7), that a functor sc-smooth on objects is
sc-smooth on morphisms, does not hold as we read it; it holds for functors continuous on morphisms (§1). The reduced
morphism space $\mathbf X^R$ of Proposition 7.2.10 (2017: 7.9) and Proposition 7.10 (2017; rewritten in 2021 as Theorem 7.2.14) is an M-polyfold under the hypothesis that it is Hausdorff and
paracompact, which the proof does not give as we read it (§5; gap G.71). Proposition 7.1.15 (2017: 7.5) is proved by transporting one
natural representation, without the text's induction (§3). The claim of Proposition 7.3.9 (2017: 7.11) that the lift of a tame
ep-groupoid is tame, for which the text gives no argument, is proved (§6). Steps the text leaves out are supplied: the
uniqueness of natural representations, the conjugation of the subgroups $T_x$, Michael's theorem on unions of closed
paracompact sets, and the support bound that makes the sum in the proof of Theorem 7.5.7 (2017: 7.4) locally finite (§§3, 5–8). The
tangent $T\varphi$ of a morphism is only defined (§1; gap G.70).

## 1. Groupoids and ep-groupoids (pp. 287–292 (2017 pp. 225–229))

**Definition 7.1.1 (2017: 7.1) (groupoid).** A *groupoid* $X = (X,\mathbf X)$ is a small category whose morphisms are all invertible, with
the structure maps $s,t:\mathbf X\to X$ (source and target), $m:\mathbf X\,{}_s{\times}_t\,\mathbf X\to\mathbf X$, $m(\varphi,\psi) = \varphi\circ\psi$, on the composable pairs
$s(\varphi) = t(\psi)$, $u:X\to\mathbf X$, $u(x) = 1_x$, and $\iota:\mathbf X\to\mathbf X$, $\iota(\varphi) = \varphi^{-1}$. $\mathrm{mor}(x,y)$ is the set of morphisms $x\to y$; $x\sim y$ if
$\mathrm{mor}(x,y)\neq\emptyset$; the *orbit space* is $|X| = X/\sim$, with the projection $\pi(x) = |x|$.

*How this is read.* A groupoid is a structure of maps on two types, with the laws of a category required on composable
pairs; the composition is a total function whose values on non-composable pairs are never used. The saturation
$\pi^{-1}(\pi(A))$ of a set of objects, which the chapter uses from Definition 7.1.21 (2017: 7.10) on, is defined here, and a bridge to Mathlib's
groupoids makes "full" and "faithful" Mathlib's notions (Findings, item 1). *Checked by machine (V7.1):*
`Polyfold.GroupoidStr`, `Polyfold.GroupoidStr.OrbitSpace`, `Polyfold.GroupoidStr.π`, `Polyfold.GroupoidStr.π_eq_π_iff`,
`Polyfold.GroupoidStr.saturation`, `Polyfold.GroupoidStr.isSaturated_iff`, `Polyfold.GroupoidStr.instGroupoid`.

**Definition 7.1.2 (2017: 7.2) (isotropy group).** $G_x = \mathrm{mor}(x,x)$, a group under $gh = g\circ h$. Mathlib's vertex group multiplies in the
other order and is identified with the opposite group (Findings, item 2). *Checked by machine (V7.2):*
`Polyfold.GroupoidStr.Isotropy`, `Polyfold.GroupoidStr.isotropyEquivVertexGroup`, `Polyfold.GroupoidStr.isotropyEquivAut`.

**Definition 7.1.3 (2017: 7.3) (ep-groupoid).** An *ep-groupoid* is a groupoid $X$ with M-polyfold structures on $X$ and $\mathbf X$ such that

1. $s$ and $t$ are local sc-diffeomorphisms;
2. $u$ and $\iota$ are sc-smooth;
3. every $x\in X$ has an open neighbourhood $V(x)$ such that $t:s^{-1}(\mathrm{cl}_X V(x))\to X$ is proper;
4. $m$ is sc-smooth on the fibred product $\mathbf X\,{}_s{\times}_t\,\mathbf X$, a sub-M-polyfold of $\mathbf X\times\mathbf X$ since $s$ is a local sc-diffeomorphism.

"e" stands for étale, condition (1), and "p" for proper, condition (3).

*How this is read.* "Proper" is Mathlib's notion for the restriction of $t$ to the subspace $s^{-1}(\mathrm{cl}_X V(x))$. Since $\mathbf X$ is
metrizable (Theorem 2.3.10 (2017: 2.2)), it is equivalent to the form in which the proofs use it: every sequence in $s^{-1}(\mathrm{cl}_X V(x))$ whose
targets converge has a convergent subsequence; equivalently, $s^{-1}(\mathrm{cl}_XV(x))\cap t^{-1}(K)$ is compact for every compact $K$. With
it are proved: properness passes to every smaller open $V'\subseteq V(x)$, which the text uses without comment; a proper
restriction has closed image; and its fibres are finite. Condition (3) asks for one $V(x)$ for each $x$, and it cannot be asked of every
neighbourhood: in the pair groupoid of $\mathbb Z$ (one morphism between any two integers, discrete topologies) the map
$t:s^{-1}(\mathbb Z)\to\mathbb Z$ is not proper (§9; Findings, items 3, 103). For (4) the text cites "Lemma 2.8 in [38]", the paper *A General
Fredholm Theory III* of its bibliography; this is an external citation, and its statement in the book is Part I's
Proposition 2.5.20 (2017: 2.15), which the formalization uses. The proofs use an equivalent *sheet form* of (4): for every local
section $\sigma$ of $s$, the map $\psi\mapsto m(\sigma(t(\psi)),\psi)$ is sc-smooth where it is defined (Findings, item 4). *Checked by machine
(V7.3, V7.4):* `Polyfold.EpGroupoid`, `Polyfold.EpGroupoid.exists_isProperMap`, `Polyfold.EpGroupoid.isScSmoothComp`,
`Polyfold.IsScSmoothCompSheet`, `Polyfold.isScSmoothComp_iff_sheet`, `Polyfold.MPolyfold.isSubMPolyfold_fibredProduct`,
`Polyfold.isProperMap_iff_exists_tendsto_subseq`, `Polyfold.MPolyfold.isProperMap_domRestrict_iff_isCompact_preimage`,
`Polyfold.isProperMap_domRestrict_closure_mono`, `Polyfold.isClosed_image_preimage_of_isProperMap_domRestrict`,
`Polyfold.finite_setOf_of_isProperMap_domRestrict`.

The comparison of (3) with the classical properness of $(s,t):\mathbf X\to X\times X$ (2017 p. 227) has no formal content and is not
formalized.

**Definition 7.1.4 (2017: 7.4) (the map $\hat\varphi$ and the tangent $T\varphi$).** Since $s$ and $t$ are local sc-diffeomorphisms, a morphism $\varphi:x\to y$ has
open neighbourhoods $\mathbf U(\varphi)$, $U(x)$, $U(y)$ for which $s:\mathbf U(\varphi)\to U(x)$ and $t:\mathbf U(\varphi)\to U(y)$ are sc-diffeomorphisms. Then
$\hat\varphi = t\circ(s|\mathbf U(\varphi))^{-1}:U(x)\to U(y)$ is an sc-diffeomorphism with $\hat\varphi(x) = y$, and $T\varphi := T\hat\varphi(x):T_xX\to T_yX$.

Such neighbourhoods are a *sheet* of $s$ at $\varphi$, and $\hat\varphi$ is proved an sc-diffeomorphism. $T\varphi$ is a definition only: that it does
not depend on the sheet, that it is a bounded linear isomorphism on level $0$ for $\varphi$ on level $1$, and an sc-isomorphism for
smooth $\varphi$, needs a linear structure on the tangent spaces $T_xX$, which the project does not have (gap G.7). Nothing in
Chapter 7 uses $T\varphi$; it is deferred to Chapter 8, where the tangent of an ep-groupoid is built (gap G.70). The display of
$\hat\varphi$ reads "$\circ\, U(x)\to U(y)$" with $\circ$ for a colon (possible misprint; the same in Definition 7.1.20 (2017: 7.9)), and the target of $T\varphi$ lacks
its $X$ (possible misprint or extraction artefact) (Findings, items 5, 110). *Checked by machine (V7.5):*
`Polyfold.EpGroupoid.Sheet`, `Polyfold.EpGroupoid.exists_sheet`, `Polyfold.EpGroupoid.hat`,
`Polyfold.EpGroupoid.isScDiffeoOn_hat`, `Polyfold.EpGroupoid.hat_src`, `Polyfold.EpGroupoid.tangentMor`.

**Levels and the degeneracy index (pp. 289–291 (2017 pp. 227–228); Definition 7.1.5 (2017: 7.5)).** A local sc-diffeomorphism preserves the levels and, by
Part I's Proposition 2.4.4 (2017: 2.7), the degeneracy index. So for $\varphi:x\to y$ the points $x$, $\varphi$, $y$ lie on the same levels, and
$d_X(s(\varphi)) = d_{\mathbf X}(\varphi) = d_X(t(\varphi))$. Hence $d_X$ is constant on classes, and Definition 7.1.5 (2017: 7.5) sets $d_{|X|}(|x|) = d_X(x)$. The sets
$|X_k| = \pi(X_k)$ of the filtration $|X| = |X_0|\supset|X_1|\supset\cdots$ are defined; the set $|X_\infty|$ and the identity $|X_\infty| = \bigcap_k|X_k|$, immediate
since the level is constant on classes, are not stated (gap G.72) (Findings, items 6, 112). The text's remark that $X_\infty$ is
dense in every $X_k$ is made without proof; Part I proves it only for sc-Banach spaces, and it is not formalized (gap G.73;
Findings, item 116). *Checked by machine (V7.6,
V7.7):* `Polyfold.EpGroupoid.mem_levelSet_src_iff`, `Polyfold.MPolyfold.IsLocalScDiffeo.degIndex_eq`,
`Polyfold.EpGroupoid.degIndex_src`, `Polyfold.EpGroupoid.degIndex_tgt`, `Polyfold.EpGroupoid.orbitLevel`,
`Polyfold.EpGroupoid.degIndexOrbit`, `Polyfold.EpGroupoid.degIndexOrbit_π`.

**Definition 7.1.6 (2017: 7.6) (tame ep-groupoid).** $X$ is *tame* if the object M-polyfold is tame; then so is $\mathbf X$. "Tame" is the
existence of an equivalent tame atlas (Definition 2.5.7 (2017: 2.19)), and the tame atlas of $\mathbf X$ is transported from $X$ along the local
sc-diffeomorphism $s$. Read as "every chart is tame" the hypothesis could not be satisfied (Findings, items 7, 106).
*Checked by machine (V7.8):* `Polyfold.EpGroupoid.IsTame`, `Polyfold.MPolyfold.IsScDiffeoOn.exists_tame_chart`,
`Polyfold.MPolyfold.IsLocalScDiffeo.isTame`.

**Definition 7.1.7 (2017: 7.7) (the category $\mathcal{EP}$).** The objects of $\mathcal{EP}$ are the ep-groupoids, its morphisms the functors $f:X\to Y$ that
are sc-smooth on objects and on morphisms. A functor commutes with $s$, $t$, $m$ and $u$; that it commutes with $\iota$ follows
(Findings, item 8). *Checked by machine (V7.9):* `Polyfold.GroupoidFunctor`, `Polyfold.GroupoidFunctor.mor_inv`,
`Polyfold.EpFunctor`, `Polyfold.EpFunctor.comp`, `Polyfold.EP`.

> **The remark after Definition 7.1.7 (2017: 7.7) does not hold as we read it.** The text (pp. 290–292 (2017 pp. 228–229)) says that it suffices to ask
> that $f$ be sc-smooth on objects: for $\varphi\in\mathbf X$ and $\psi = f(\varphi)$ choose sheets $\mathbf U(\varphi)$, $\mathbf U(\psi)$ with $f(\mathbf U(\varphi))\subseteq\mathbf U(\psi)$; then
> $f(\gamma) = (s|\mathbf U(\psi))^{-1}(f(s(\gamma)))$ for $\gamma\in\mathbf U(\varphi)$, and the right side is sc-smooth. Choosing $\mathbf U(\varphi)$ with $f(\mathbf U(\varphi))\subseteq\mathbf U(\psi)$ needs $f$
> to be continuous on morphisms, and without that the claim fails. Let $\mathbb Z/3$ act trivially on $\mathbb R$: the ep-groupoid has the
> objects $\mathbb R$, the morphisms $\mathbb Z/3\times\mathbb R$ and $s(g,y) = t(g,y) = y$. Let $f$ be the identity on objects, and on morphisms
> $f(g,y) = (g,y)$ for $y\le0$, $f(g,y) = (g^2,y)$ for $y>0$. Since $g\mapsto g^2$ is an automorphism of $\mathbb Z/3$, $f$ is a functor, and it is
> sc-smooth on objects; but for $g\neq1$, $(g,y)\to(g,0)$ as $y\downarrow0$ while $f(g,y) = (g^2,y)\to(g^2,0)\neq f(g,0)$. So $f$ is not continuous, hence
> not sc-smooth, on morphisms.

For functors continuous on morphisms the argument goes through: with a sheet $\mathbf U(\psi)$ of $s$ at $\psi = f(\varphi)$ and the open
$\mathbf U(\varphi) = f^{-1}(\mathbf U(\psi))$, every $\gamma\in\mathbf U(\varphi)$ has $f(\gamma)\in\mathbf U(\psi)$ and $s(f(\gamma)) = f(s(\gamma))$, so $f(\gamma) = (s|\mathbf U(\psi))^{-1}(f(s(\gamma)))$. A functor
sc-smooth on objects is therefore a morphism of $\mathcal{EP}$ if and only if it is continuous on morphisms (Findings, items 9,
104). *Checked by machine (V7.10):* `Polyfold.EpGroupoid.mor_eq_srcInv_obj_src`,
`Polyfold.EpGroupoid.isScSmoothMap_mor_of_continuous`, `Polyfold.EpGroupoid.isScSmoothMap_mor_iff_continuous`,
`Polyfold.EpFunctor.ofContinuous`, `Polyfold.EpGroupoid.Examples.remark_definition_7_7_counterexample`.

## 2. The orbit space and the isotropy groups (pp. 291–293 (2017 pp. 229–230))

$|X|$ carries the quotient topology: $W\subseteq|X|$ is open if and only if $\pi^{-1}(W)$ is open in $X$.

**Proposition 7.1.8 (2017: 7.1).** $\pi:X\to|X|$ is open.

*Proof.* For $U\subseteq X$ open, $\pi^{-1}(\pi(U))$ consists of the targets of the morphisms with source in $U$, that is, it is $t(s^{-1}(U))$. Since $s$
is continuous and $t$ is a local homeomorphism, hence open, this set is open, and so is $\pi(U)$. $\square$

The text argues point by point with the same sheets (Findings, item 10). *Checked by machine (V7.11):*
`Polyfold.EpGroupoid.proposition_7_1`, `Polyfold.EpGroupoid.proposition_7_1_isOpenQuotientMap`.

**Proposition 7.1.9 (2017: 7.2).** Every point of $|X|$ has a countable basis of open neighbourhoods $W_1\supseteq W_2\supseteq\cdots$.

*Proof.* $X$ is metrizable (Theorem 2.3.10 (2017: 2.2)). The images under $\pi$ of the balls of radius $1/(k+1)$ about $x$ are open by Proposition 7.1.8 (2017: 7.1)
and decreasing; if $W\ni|x|$ is open, $\pi^{-1}(W)$ contains one of the balls, so $W$ contains its image. $\square$

*Checked by machine (V7.12):* `Polyfold.EpGroupoid.proposition_7_2`,
`Polyfold.EpGroupoid.proposition_7_2_firstCountableTopology`.

**Proposition 7.1.10 (2017: 7.3) (the local closure relation).** Every $x\in X$ has an open neighbourhood $U$ such that
$\pi(\mathrm{cl}_XA) = \mathrm{cl}_{|X|}\pi(A)$ for every $A\subseteq U$.

*Proof.* Let $U = V(x)$ be as in (3) of Definition 7.1.3 (2017: 7.3), and $A\subseteq\mathrm{cl}_XU$. The inclusion $\subseteq$ holds by continuity. Conversely,
$\pi^{-1}(\pi(\mathrm{cl}_XA)) = t(s^{-1}(\mathrm{cl}_XA))$, and $s^{-1}(\mathrm{cl}_XA)$ is a closed subset of $s^{-1}(\mathrm{cl}_XU)$, on which $t$ is proper, hence a closed map.
So the saturated set $\pi^{-1}(\pi(\mathrm{cl}_XA))$ is closed, $\pi(\mathrm{cl}_XA)$ is closed in $|X|$, and it contains $\mathrm{cl}_{|X|}\pi(A)$. $\square$

The proof holds for every $U$ with the properness property and every $A\subseteq\mathrm{cl}_XU$, slightly more than the text states; the
text's sequence argument is the same fact (Findings, item 11). *Checked by machine (V7.13):*
`Polyfold.EpGroupoid.proposition_7_3`, `Polyfold.EpGroupoid.proposition_7_3_of_isProperMap`.

**Lemma 7.1.11 (2017: 7.1).** If $t:s^{-1}(\mathrm{cl}_XU(x_0))\to X$ is proper, then for every $x\in X$ only finitely many morphisms $\psi$ have $s(\psi) = x$ and
$t(\psi)\in U(x_0)$.

*Proof.* The inverses of these $\psi$ have target $x$ and source in $U(x_0)$: they lie in the fibre over $x$ of the proper map
$t:s^{-1}(\mathrm{cl}_XU(x_0))\to X$. That fibre is compact, and discrete since $t$ is a local homeomorphism, hence finite. $\square$

The text's proof works with the inverses, $s$ and $t$ exchanged (possible misprint); both forms are proved. In the proof
"$t:V(\psi)\to V(y)$" is meant for $V(x)$, and "$s(\psi)\in s^{-1}(\mathrm{cl}_X(U(x_0)))$" for $\psi\in s^{-1}(\mathrm{cl}_X(U(x_0)))$; statement and proof lack a closing
parenthesis (possible misprints). The openness of $U(x_0)$ and $x_0\in U(x_0)$ are not used (Findings, items 12, 96). *Checked
by machine (V7.14):* `Polyfold.EpGroupoid.lemma_7_1`, `Polyfold.EpGroupoid.lemma_7_1_swap`,
`Polyfold.IsProperMap.finite_preimage_singleton_of_isLocallyInjective`.

**Proposition 7.1.12 (2017: 7.4).** Every isotropy group $G_x$ is finite.

*Proof.* Lemma 7.1.11 (2017: 7.1) with $x_0 = x$ and $U(x_0) = V(x)$ of Definition 7.1.3 (3) (2017: 7.3). $\square$

For $\varphi:x\to y$, conjugation $g\mapsto\varphi\circ g\circ\varphi^{-1}$ is an isomorphism $G_x\to G_y$. The text notes that there is no canonical
identification; precisely, two choices of $\varphi$ give isomorphisms that differ by an inner automorphism of $G_y$ (Findings,
item 13). *Checked by machine (V7.15, V7.16):* `Polyfold.EpGroupoid.proposition_7_4`,
`Polyfold.MPolyfold.finite_isotropy_of_isLocalScDiffeo`, `Polyfold.EpGroupoid.conjIsotropy`,
`Polyfold.EpGroupoid.nonempty_isotropy_mulEquiv`, `Polyfold.EpGroupoid.isotropyConj_eq_isotropyConj_conj`.

## 3. The natural representation (pp. 293–306 (2017 pp. 231–237); Appendix 7.6.1 (2017 7.5.1), pp. 344–346 (2017 pp. 253–254))

**Theorem 7.1.13 (2017: 7.1) (the natural representation of $G_x$).** Let $x\in X$ and let $V$ be an open neighbourhood of $x$. There are an open
connected neighbourhood $U\subseteq V$ of $x$, a homomorphism $\Phi:G_x\to\mathrm{Diff}_{sc}(U)$ and an sc-smooth map $\Gamma:G_x\times U\to\mathbf X$ such that

1. $\Gamma(g,x) = g$;
2. $s(\Gamma(g,y)) = y$ and $t(\Gamma(g,y)) = \Phi(g)(y)$;
3. every morphism $\psi:y\to z$ between points of $U$ is $\Gamma(g,y)$ for exactly one $g\in G_x$.

One writes $g*y = \Phi(g)(y)$; the theorem is restated and proved as Theorem 7.6.1 (2017: 7.5) in Appendix 7.6.1 (2017 7.5.1).

*How this is read.* A natural representation is a datum $(U,\Phi,\Gamma)$. The statement does not say "connected", but the text
chooses "the connected open neighborhood $U(x)$" on p. 293 (2017 p. 231), and connectedness is needed: it is what makes $\Phi$ a
homomorphism. Indeed $y\mapsto\Gamma(gh,y)$ and $y\mapsto\Gamma(g,h*y)\circ\Gamma(h,y)$ are continuous sections of $s$ that agree at $y = x$; two sections of a local
homeomorphism that agree at one point agree on a connected set containing it, and on a disconnected $U$ they may
disagree on another component. $\Phi(g)$ is an sc-diffeomorphism of $U$ with inverse $\Phi(g^{-1})$, and "$\Gamma$ sc-smooth on $G_x\times U$" is
sc-smoothness on each slice $\{g\}\times U$, $G_x\times U$ being a finite disjoint union of copies of $U$ (below) (Findings, items 20,
23).

*Proof (Theorem 7.6.1 (2017: 7.5), Lemmas 7.6.2 and 7.6.3 (2017: 7.8 and 7.9)).* By Proposition 7.1.12 (2017: 7.4), $G_x$ is finite. Choose for every $g\in G_x$ a sheet $N_g\ni g$, the $N_g$
pairwise disjoint, so that $s$ and $t$ map $N_g$ sc-diffeomorphically onto open neighbourhoods of $x$, and put
$U_0 = V\cap\bigcap_gs(N_g)$; write $s_g$, $t_g$ for $s$, $t$ on $N_g\cap s^{-1}(U_0)$.

*Lemma 7.6.2 (2017: 7.8).* There is an open $U_1\subseteq U_0$ of $x$ such that every morphism between points of $U_1$ lies in some $N_g$. Otherwise,
along a countable basis of $x$, there are morphisms $h_k\notin\bigcup_gN_g$ with $s(h_k)\to x$ and $t(h_k)\to x$. For large $k$, $s(h_k)$ lies in a
neighbourhood of $x$ with the properness property, so a subsequence converges, to a morphism $x\to x$, that is, to some
$g\in G_x$; then $h_k\in N_g$ for large $k$, which is excluded.

*Lemma 7.6.3 (2017: 7.9).* There is an open connected $U_2\subseteq U_1$ of $x$ such that $U = \bigcup_gt_g\circ s_g^{-1}(U_2)$ lies in $U_1$ and is invariant under every
$t_g\circ s_g^{-1}$. The key is a composition rule: for $g,h\in G_x$ the morphism $m(s_g^{-1}(t_hs_h^{-1}(y)),s_h^{-1}(y))$ depends continuously on $y$,
by (4) in sheet form, and equals $gh$ at $y = x$, so it lies in $N_{gh}$ for $y$ near $x$ and is $s_{gh}^{-1}(y)$; hence
$t_gs_g^{-1}\circ t_hs_h^{-1} = t_{gh}s_{gh}^{-1}$ near $x$. For $U_2$ small these compositions are defined and $U$ lies in $U_1$; then $U$ is invariant by the
composition rule, and connected because each piece $t_gs_g^{-1}(U_2)$ is connected and contains $x$.

Now put $\Phi(g) = t_gs_g^{-1}|_U$ and $\Gamma(g,y) = s_g^{-1}(y)$. Properties (1) and (2) hold by construction, $\Phi$ is a homomorphism by the
composition rule and the connectedness of $U$, and (3) holds by Lemma 7.6.2 (2017: 7.8): a morphism $\psi:y\to z$ between points of $U$ lies in
some $N_g$, so $\psi = s_g^{-1}(y) = \Gamma(g,y)$, and $g$ is unique because the $N_g$ are disjoint. $\square$

The text does not say that $U_2$ is connected; it can be so chosen because M-polyfolds are locally path connected (below)
(Findings, item 31). The neighbourhood is started at $U_0 = V\cap\bigcap_gs(N_g)$ so that $U\subseteq V$, which the text's proof does not
address, and the contractibility of the $N_g$ that the text asks for is not needed. In the statement of Theorem 7.6.1 (2017: 7.5),
"$\Phi:G_x\to\mathrm{Diff}_{sc}(U)$" is meant for $G_{x_0}$, and Lemma 7.6.2 (2017: 7.8) invokes "the properness assumption of ep-polyfolds" for
ep-groupoids (possible misprints) (Findings, items 29, 30). *Checked by machine (V7.17, V7.62–V7.64):*
`Polyfold.EpGroupoid.NaturalRep`, `Polyfold.EpGroupoid.NaturalRep.isConnected_U`,
`Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_Φ`, `Polyfold.EpGroupoid.NaturalRep.Φ_mul`,
`Polyfold.EpGroupoid.NaturalRep.isScSmoothOn_Γ`, `Polyfold.EpGroupoid.NaturalRep.existsUnique_Γ`,
`Polyfold.EpGroupoid.theorem_7_1`, `Polyfold.EpGroupoid.theorem_7_5`, `Polyfold.EpGroupoid.lemma_7_8`,
`Polyfold.EpGroupoid.lemma_7_9`, `Polyfold.EpGroupoid.NatRepConstruction.Sheets.isConnected_unionHat`,
`Polyfold.EpGroupoid.NatRepConstruction.Sheets.hat_mul`.

**M-polyfolds are locally path connected.** The text uses connected neighbourhoods and open connected components
without comment (2017 pp. 231, 247, 254). An sc-retract $O = r(U)$ is locally path connected: a point $p\in O$ near $o$ is joined to $o$
inside $O$, and inside any given neighbourhood of $o$, by the path $\tau\mapsto r(o+\tau(p-o))$. Hence every M-polyfold, and every open
quotient of one, is locally path connected, open connected sets are path connected, and connected components are open.
This is the first of the two facts of Part I's gap G.56, now formalized (Findings, items 21, 114). *Checked by machine
(V7.18):* `Polyfold.ScRetraction.exists_ball_joinedIn`, `Polyfold.MPolyfold.locallyPathConnectedSpace`,
`Polyfold.MPolyfold.isOpen_connectedComponent`, `Polyfold.MPolyfold.locallyPathConnectedSpace_quotient`,
`Polyfold.eqOn_sections_of_isPreconnected`.

**After Theorem 7.1.13 (2017: 7.1) (pp. 293–297 (2017 pp. 231–233)).** Write $\mathbf U(x)$ for the set of morphisms between points of $U = U(x)$ and $\mathbf U(g) = \Gamma(g,U)$. Then
$\mathbf U(x)$ is the disjoint union of the connected open sets $\mathbf U(g)$, $g\in G_x$, on each of which $s$ and $t$ are sc-diffeomorphisms onto
$U$; and $\mathbf U(x)$ fits into any given open neighbourhood of $G_x$ in $\mathbf X$ (Lemma 7.6.2 (2017: 7.8) for arbitrary open $N_g$, then Theorem 7.1.13 (2017: 7.1)
inside $U_1$). The finite disjoint union $G_x\times U$ is an M-polyfold, the product of $U$ with the discrete M-polyfold on $G_x$. The
*translation groupoid* $G_x\ltimes U$, with objects $U$, morphisms $G_x\times U$, $s(g,y) = y$, $t(g,y) = g*y$ and $(g,h*y)\circ(h,y) = (gh,y)$, is an
ep-groupoid, built from $(\Phi,\Gamma)$ alone, with the properness for every open set. $\Gamma:G_x\ltimes U\to X$ is a functor (because $U$ is
connected), full and faithful by (3), sc-smooth on objects and morphisms, with image the full subcategory on $U$. Finally,
$\hat\Phi(g)(\varphi) = \Gamma(ghg^{-1},g*s(\varphi))$ for $\varphi\in\mathbf U(h)$ defines a homomorphism $\hat\Phi$ from $G_x$ to the sc-diffeomorphisms of $\mathbf U(x)$ with
$\hat\Phi(g)(\mathbf U(h)) = \mathbf U(ghg^{-1})$, $s\circ\hat\Phi(g) = \Phi(g)\circ s$ and $t\circ\hat\Phi(g) = \Phi(g)\circ t$. No possible misprint was found on these pages (Findings,
items 22, 23). *Checked by machine (V7.19–V7.23):* `Polyfold.EpGroupoid.NaturalRep.pairwise_disjoint_image_Γ`,
`Polyfold.EpGroupoid.NaturalRep.iUnion_image_Γ`, `Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_src_image`,
`Polyfold.discretePolyfold`, `Polyfold.isScSmoothMap_prod_discrete_iff`,
`Polyfold.EpGroupoid.NaturalRep.translationEpGroupoid`, `Polyfold.EpGroupoid.NaturalRep.translation_isProperMap`,
`Polyfold.EpGroupoid.NaturalRep.full`, `Polyfold.EpGroupoid.NaturalRep.faithful`,
`Polyfold.EpGroupoid.NaturalRep.epFunctor`, `Polyfold.EpGroupoid.NaturalRep.Φhat`,
`Polyfold.EpGroupoid.NaturalRep.Φhat_mul`, `Polyfold.EpGroupoid.NaturalRep.src_Φhat`,
`Polyfold.EpGroupoid.NaturalRep.tgt_Φhat`.

**Uniqueness and restriction.** Two natural representations at $x$ agree on the connected component of $x$ in $U\cap U'$, since
$\Gamma(g,\cdot)$ and $\Gamma'(g,\cdot)$ are sections of $s$ through $g$; and a natural representation restricts to every $G_x$-invariant connected open
neighbourhood of $x$ in $U$. The text uses both without statement ("$U(x)$ can be chosen arbitrarily small", "adapting
restrictions", pp. 307–311 (2017 pp. 239–241)) (Findings, item 24). *Checked by machine (V7.24):*
`Polyfold.EpGroupoid.NaturalRep.Γ_eqOn`, `Polyfold.EpGroupoid.NaturalRep.Φ_eqOn`,
`Polyfold.EpGroupoid.NaturalRep.restrict`, `Polyfold.EpGroupoid.exists_naturalRep_shrink`.

**Proposition 7.1.15 (2017: 7.5) (finitely many isomorphic objects).** Let $Y$ be a finite set of mutually isomorphic objects and $V$ a
neighbourhood of $Y$. There are pairwise disjoint connected open neighbourhoods $U(y)\subseteq V$ of the $y\in Y$ and a functor $f$
assigning to every morphism $\psi:y\to y'$ between points of $Y$ an sc-diffeomorphism $f(\psi):U(y)\to U(y')$, such that the morphisms
between points of $\bigcup_yU(y)$ split into open sets $\mathbf U(\psi)$ with (1) $f$ on $G_y$ the natural action of $G_y$ on $U(y)$, (2) $s:\mathbf U(\psi)\to U(y)$
and $t:\mathbf U(\psi)\to U(y')$ sc-diffeomorphisms, (3) $f(\psi) = t\circ(s|\mathbf U(\psi))^{-1}$. Definition 7.1.18 (2017: 7.8) calls this datum the natural
representation of the full subcategory on $Y$.

*Proof.* Fix one object $x$ isomorphic to the points of $Y$ (it need not lie in $Y$), a natural representation $(U,\Phi,\Gamma)$ at $x$, and
morphisms $\gamma_y:x\to y$. Transport $U$ along the sheets: $U(y) = \hat\gamma_y(U)$, with $U$ so small that the $U(y)$ are disjoint and lie in $V$.
For $\psi:y\to y'$ the morphism $g = \gamma_{y'}^{-1}\circ\psi\circ\gamma_y$ lies in $G_x$; put $f(\psi) = \hat\gamma_{y'}\circ\Phi(g)\circ\hat\gamma_y^{-1}$, and let $\mathbf U(\psi)$ be the transport of $\mathbf U(g)$.
That $f$ is a functor comes from $\Phi$ being a homomorphism, and (1)–(3) from Theorem 7.1.13 (2017: 7.1). $\square$

The text proceeds by induction on the number of objects, shrinking the neighbourhoods at every step; the transport
needs neither. $V$ is read as a neighbourhood of the set $Y$, and $Y = \emptyset$ is allowed. The text's proof has twelve possible
misprints, one of them possibly an extraction artefact, for instance "Let $k\ge3$" for $k\ge2$ and $\Psi_g$ for $\Phi_g$; none affects the
argument (Findings, items 25, 26). *Checked by machine (V7.25, V7.26):* `Polyfold.EpGroupoid.NaturalRepFinite`,
`Polyfold.EpGroupoid.NaturalRepFinite.F_comp`, `Polyfold.EpGroupoid.NaturalRepFinite.pairwiseDisjoint_U`,
`Polyfold.EpGroupoid.NaturalRepFinite.F_eq`, `Polyfold.EpGroupoid.NatRepFinite.transportRep`,
`Polyfold.EpGroupoid.NatRepFinite.exists_star`, `Polyfold.EpGroupoid.NatRepFinite.emptyNaturalRepFinite`,
`Polyfold.EpGroupoid.proposition_7_5`, `Polyfold.EpGroupoid.proposition_7_5_of_mem_nhdsSet`.

**Proposition 7.1.19 (2017: 7.6).** For a natural representation at $x$, the map $\tau:G_x\backslash U(x)\to\pi(U(x))$, $G_x*y\mapsto|y|$, is a homeomorphism onto the open
set $\pi(U(x))$; the functor $G_x\ltimes U(x)\to X$ is fully faithful and induces this homeomorphism of orbit spaces.

*Proof.* By (2) and (3) of Theorem 7.1.13 (2017: 7.1), $|y| = |z|$ for $y,z\in U(x)$ if and only if $z = g*y$ for some $g$, so $\tau$ is well defined and injective.
It is continuous; and for $Q\subseteq G_x\backslash U(x)$ open, $\tau(Q) = \pi(\sigma^{-1}(Q))$ with $\sigma$ the quotient map, open by Proposition 7.1.8 (2017: 7.1). So $\tau$ is an
open embedding with image $\pi(U(x))$. $\square$

The openness of $\sigma$, which the text uses, is not needed (Findings, item 27). *Checked by machine (V7.27):*
`Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_orbitQuotientMap`, `Polyfold.EpGroupoid.proposition_7_6`,
`Polyfold.EpGroupoid.proposition_7_6_fullyFaithful`.

**Definition 7.1.20 (2017: 7.9) (local uniformizer).** A local uniformizer around $x$ is a fully faithful functor $\Psi_x:G_x\ltimes U(x)\to X$, the
inclusion on objects, that induces a homeomorphism of $G_x\backslash U(x)$ onto the open set $\pi(U(x))$. Every natural representation
gives one, so local uniformizers exist inside every open $V\ni x$; they are injective on objects and on morphisms, as the
text notes, and those built from natural representations are open embeddings on objects and on morphisms. "Embedding"
is derived, not required. The definition writes "$\Psi_x\circ G_x\ltimes U(x)\to X$" with $\circ$ for a colon, and "a a local uniformizer"
(possible misprints) (Findings, item 28). *Checked by machine (V7.28):* `Polyfold.EpGroupoid.LocalUniformizer`,
`Polyfold.EpGroupoid.NaturalRep.toLocalUniformizer`, `Polyfold.EpGroupoid.exists_localUniformizer`,
`Polyfold.EpGroupoid.LocalUniformizer.injective_mor`, `Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_functor_mor`.

## 4. Ep-subgroupoids (pp. 305–308 (2017 pp. 237–239))

**Definition 7.1.21 (2017: 7.10) (ep-subgroupoid).** Let $A\subseteq X$ be saturated, $A = \pi^{-1}(\pi(A))$, and a sub-M-polyfold of $X$. The
*ep-subgroupoid* defined by $A$ is the full subcategory with objects $A$ and morphisms $\mathbf A = \{\varphi\mid s(\varphi),t(\varphi)\in A\}$. Open saturated sets,
and the saturations of open sets, are examples (Findings, items 40, 105).

The text recalls four facts on a sub-M-polyfold $A$ from Part I's Proposition 2.3.19 (2017: 2.6): (1) the inclusion $A\to X$ is sc-smooth and a
homeomorphism onto its image; (2) for a local sc-smooth retraction $r$ onto $A\cap V$, $i^{-1}\circ r$ is sc-smooth; (3) $T_aA$ has an
sc-complement in $T_aX$ at smooth points; (4) $T_aA = Tr(a)T_aX$. Facts (1) and (2) are used. Facts (3) and (4) are not restated,
since tangent spaces carry no linear structure in the project (gap G.7); in a chart they are Part I's
`Polyfold.proposition_2_21_3` and `Polyfold.proposition_2_21_4` (Findings, item 40).

For saturated $A$, $\mathbf A = s^{-1}(A) = t^{-1}(A)$: a morphism with source in $A$ has its target in $A$. So $\mathbf A$ is the preimage of a
sub-M-polyfold under a local sc-diffeomorphism, and a sub-M-polyfold; the text's retraction $\mathbf r = (s|\mathbf U(\varphi))^{-1}\circ r\circ s$ is this
construction. The text adds "$t(\mathbf r(\psi))\in U(a)$, so that $\mathbf r(\psi)\in\mathbf U(a)$"; that need not hold ($t(\mathbf r(\psi))$ lies near $t(\varphi)$, not near $a$)
and is not used, since $\mathbf r(\psi)\in\mathbf A$ follows from $s(\mathbf r(\psi))\in A$ and saturation (possible misprint or extraction artefact)
(Findings, item 41).

**Proposition 7.1.22 (2017: 7.7).** If $A$ is saturated and a sub-M-polyfold of $X$, the full subcategory $(A,\mathbf A)$ with the restricted structure
maps is an ep-groupoid.

*Proof.* (1): the restrictions of the sheets of $s$ and $t$ to $\mathbf A = s^{-1}(A)$ are sc-diffeomorphisms onto open subsets of $A$. (2) and (4):
restrictions of sc-smooth maps are sc-smooth into $A$, because a map sc-smooth into $X$ with values in the sub-M-polyfold $A$ is
sc-smooth into $A$; for (4), the fibred product of $\mathbf A$ includes sc-smoothly into that of $\mathbf X$. (3): for $a\in A$ take $V(a)$ with the
properness property in $X$. A sequence of morphisms with sources in $\mathrm{cl}_A(V(a)\cap A)$ and targets converging in $A$ has a
subsequence converging in $\mathbf X$, to a morphism whose target lies in $A$; by saturation its source lies in $A$, so the limit
lies in $\mathbf A$. Finally $A$ and $\mathbf A$ must be paracompact to be M-polyfolds of the project; as subspaces of the metrizable $X$
and $\mathbf X$ they are metrizable, hence paracompact. $\square$

These steps the text leaves out; any $V(a)$ with the properness property works, the $G_a$-invariance of $U(a)$ is not used, and
the inclusion is a fully faithful functor in $\mathcal{EP}$ (Findings, item 42). *Checked by machine (V7.29–V7.32):*
`Polyfold.EpGroupoid.IsEpSubgroupoid`, `Polyfold.EpGroupoid.isEpSubgroupoid_saturation`,
`Polyfold.EpGroupoid.subObjPolyfold`, `Polyfold.EpGroupoid.morOn_eq_preimage_src`,
`Polyfold.EpGroupoid.isSubMPolyfold_morOn`, `Polyfold.EpGroupoid.exists_isProperMap_fullSub`,
`Polyfold.EpGroupoid.isScSmoothComp_fullSub`, `Polyfold.EpGroupoid.instParacompactSpaceMorOn`,
`Polyfold.EpGroupoid.subEpGroupoid`, `Polyfold.EpGroupoid.proposition_7_7`, `Polyfold.EpGroupoid.subEpFunctor_full`.

## 5. Effective and reduced ep-groupoids (pp. 307–324 (2017 pp. 239–244))

**Definition 7.2.1 (2017: 7.11).** $X$ is *effective* if for every $x$ and every $g\in G_x\setminus\{1_x\}$, every open neighbourhood of $g$ in $\mathbf X$ contains a
morphism $\psi$ with $s(\psi)\neq t(\psi)$. An object $x$ is *regular* if $G_x = \{1_x\}$; $X_{reg}$ is the set of regular objects. If $s(\varphi)$ is regular, so
is $t(\varphi)$, by conjugation (§2), so $X_{reg}$ is saturated (Findings, item 50). For the two beads of §0 the swap moves every point
not on the diagonal, and the ep-groupoid is effective; a finite group acting trivially gives a non-effective one (§9).
*Checked by machine (V7.33):* `Polyfold.EpGroupoid.IsEffective`, `Polyfold.GroupoidStr.IsRegular`,
`Polyfold.GroupoidStr.regularSet`, `Polyfold.EpGroupoid.isRegular_tgt_of_isRegular_src`,
`Polyfold.EpGroupoid.isSaturated_regularSet`.

**Lemma 7.2.2 (2017: 7.2).** $X_{reg}$ is open.

*Proof.* Let $x$ be regular and $(U,\Phi,\Gamma)$ a natural representation at $x$. For $a\in U$, by (3) of Theorem 7.1.13 (2017: 7.1) every morphism $a\to a$ is
$\Gamma(1,a)$, and $\Gamma(1,a) = 1_a$ because $y\mapsto\Gamma(1,y)$ and $y\mapsto1_y$ are sections of $s$ through $1_x$, which agree on the connected $U$. So
$U\subseteq X_{reg}$. $\square$

The step $\Gamma(1,a) = 1_a$ is where the connectedness of $U$ enters (Findings, item 51). *Checked by machine (V7.34):*
`Polyfold.EpGroupoid.NaturalRep.subset_regularSet`, `Polyfold.EpGroupoid.lemma_7_2`.

**Lemma 7.2.3 (2017: 7.3).** $X$ is effective if and only if every $x$ has, inside every open $V\ni x$, a natural representation with $\Phi$
injective.

*Proof.* If $X$ is effective, $\Phi$ is injective for *every* natural representation: if $\Phi(g) = \mathrm{id}$ with $g\neq1$, then $s = t$ on $\mathbf U(g) = \Gamma(g,U)$,
an open neighbourhood of $g$, because $t(\Gamma(g,y)) = g*y = y = s(\Gamma(g,y))$. Conversely, let $g\neq1$ and let $W$ be an open neighbourhood of $g$.
Fix a natural representation $(U_0,\Phi_0,\Gamma_0)$ at $x$; the hypothesis gives an injective one inside the neighbourhood of $x$ on which
$\Gamma_0(g,\cdot)$ stays in $W\cap\mathbf U_0(g)$; by uniqueness the two agree there, and since $\Phi(g)\neq\mathrm{id}$ some $y$ has $g*y\neq y$, so $\psi = \Gamma(g,y)\in W$ has
$s(\psi)\neq t(\psi)$. $\square$

The text's "adapting restrictions" is read through the uniqueness of natural representations (§3), and "injective" as
"trivial kernel" (Findings, item 52). *Checked by machine (V7.35):* `Polyfold.EpGroupoid.NaturalRep.kerΦ`,
`Polyfold.EpGroupoid.NaturalRep.injective_Φ_iff`, `Polyfold.EpGroupoid.isEffective_iff_forall_naturalRep`,
`Polyfold.EpGroupoid.lemma_7_3`.

**Proposition 7.2.4 (2017: 7.8).** If $X$ is effective, $X_{reg}$ is open and dense.

*Proof.* Openness is Lemma 7.2.2 (2017: 7.2). Let $W$ be open and non-empty, and choose $a\in W$ with $\#G_a$ minimal over $W$ (Proposition 7.1.12 (2017: 7.4)). Take a
natural representation at $a$ inside $W$. For $y$ in it, $G_y$ is isomorphic to the stabilizer of $y$ in $G_a$; by minimality the
stabilizer is all of $G_a$, so every $g\in G_a$ fixes every $y$, $\Phi(g) = \mathrm{id}$, and $g = 1$ by Lemma 7.2.3 (2017: 7.3). So $a\in X_{reg}\cap W$. $\square$

The text minimizes over a neighbourhood $U(x_0)$; minimizing over the given open set makes it unnecessary. The converse,
not in the text, holds too: $X$ is effective if and only if $X_{reg}$ is dense (Findings, item 53). *Checked by machine (V7.36):*
`Polyfold.EpGroupoid.NaturalRep.stabilizerEquivIsotropy`, `Polyfold.EpGroupoid.proposition_7_8`,
`Polyfold.EpGroupoid.isEffective_iff_dense_regularSet`.

**The subgroup $T_x$ (2017 p. 241).** $g\in G_x$ *acts trivially* if $\Phi(g) = \mathrm{id}$ for some natural representation at $x$; $T_x$ is the set of
these $g$. The kernel of $\Phi$ depends on $U(x)$: sc-smooth maps are not analytic, and $\Phi(g)$ can be the identity on a small $U(x)$
and not on a larger one. The text chooses $U(x)$ so small that $\ker\Phi = T_x$; what is proved is that there is a neighbourhood $N$ of
$x$ with $\ker\Phi = T_x$ for every natural representation inside $N$. Not in the text: $g\in T_x$ if and only if $s = t$ on a
neighbourhood of $g$ in $\mathbf X$, an intrinsic description; $T_x$ is a normal subgroup of $G_x$; all $T_x$ are trivial if and only if $X$
is effective; and, needed for Definition 7.2.7 (2017: 7.12) but not stated, $\varphi T_x\varphi^{-1} = T_y$ for $\varphi:x\to y$. "$\mathrm{Diff}_{sc}(U(x)$" lacks a
parenthesis (possible misprint or extraction artefact) (Findings, item 54). *Checked by machine (V7.37):*
`Polyfold.EpGroupoid.ActsTrivially`, `Polyfold.EpGroupoid.trivialSubgroup`,
`Polyfold.EpGroupoid.mem_trivialSet_iff_eventually`, `Polyfold.EpGroupoid.exists_naturalRep_kerΦ_eq`,
`Polyfold.EpGroupoid.trivialSubgroup_normal`, `Polyfold.EpGroupoid.isEffective_iff_trivialSubgroup_eq_bot`,
`Polyfold.EpGroupoid.map_isotropyConj_trivialSubgroup`.

**Definition 7.2.7 (2017: 7.12).** $\mathbf X^T = \bigcup_xT_x$ is the *non-effective part*. Morphisms $\varphi$, $\varphi'$ are equivalent, $\varphi\sim\varphi'$, if $s(\varphi) = s(\varphi') = x$ and
$\varphi = \varphi'\circ g$ for some $g\in T_x$; $\mathbf X^R = \mathbf X/\!\sim$ is the set of *reduced morphisms*. $\sim$ is an equivalence relation because $T_x$ is a subgroup,
and $\mathbf X^T$ is the interior of $\{s = t\}$ in $\mathbf X$. The text calls $\mathbf X^R$ "the subset of reduced morphisms"; it is a quotient, as the next
sentence says (possible misprint) (Findings, item 55). *Checked by machine (V7.38):*
`Polyfold.EpGroupoid.nonEffectivePart`, `Polyfold.EpGroupoid.nonEffectivePart_eq_interior`,
`Polyfold.EpGroupoid.reducedSetoid`, `Polyfold.EpGroupoid.ReducedMor`.

**Proposition 7.2.10 (2017: 7.9).** $\mathbf X^R$ has a natural M-polyfold structure, for which the projection $\mathbf X\to\mathbf X^R$ is a local sc-diffeomorphism.

*What the proof gives.* $\mathbf X^R$ carries the quotient topology, and the projection $\varphi\mapsto[\varphi]$ is open. On every sheet of $s$ the
projection is injective, since equivalent morphisms have the same source. A chart $\psi$ of $\mathbf X$ whose domain lies in a sheet of $s$, with $\sigma$ the inverse of $s$ on the sheet, gives the
chart $[\varphi']\mapsto\psi(\sigma(s(\varphi')))$ of $\mathbf X^R$ on the image of its domain, well defined for the same reason. The transition maps $\psi_2\circ\sigma_2\circ s\circ\psi_1^{-1}$ are sc-smooth. All of this holds without hypotheses.

> **$\mathbf X^R$ need not be Hausdorff, as we read it.** An M-polyfold is a Hausdorff paracompact space (Definition 2.3.4 (2017: 2.8)), and
> the proof gives neither property. Checked in Lean (after the round-trip audit): take an sc-smooth splicing $\pi_t$ on $\mathbb R\times E$ with $\pi_t = 0$
> for $t\le0$ and $\pi_t$ of rank one for $t>0$, the retract $O = r(\mathbb R\times E)$, $r(t,e) = (t,\pi_te)$, and $\mathbb Z/2$ acting by $(t,e)\mapsto(t,-e)$. In
> the translation groupoid $\mathbb Z/2\ltimes O$ the generator $g$ acts trivially near $y = (t,0)$ for $t<0$, where $O$ is the line $\{(t,0)\}$, so
> $T_y = \mathbb Z/2$; but every neighbourhood of $(0,0)$ in $O$ contains points $(t,e)$, $t>0$, $e\neq0$, which $g$ moves, so $T_{(0,0)} = 1$. The
> classes of the morphisms $(1,(0,0))$ and $(g,(0,0))$ are then distinct points of $\mathbf X^R$, but every pair of neighbourhoods of them
> contains the classes of $(1,(t,0))$ and $(g,(t,0))$ for small $t<0$, which coincide. In Lean the retract is the one of Part I's
> Remark 4.2.2 (2017: 4.3) example, a point over each $t\le0$ and a line over each $t>0$
> (`Polyfold.EpGroupoid.Examples.exists_not_t2Space_reducedMor`; Findings, item 107).

So Proposition 7.2.10 (2017: 7.9) and Proposition 7.10 (2017; rewritten in 2021 as Theorem 7.2.14) are proved under the hypothesis that $\mathbf X^R$ is Hausdorff and paracompact (gap G.71). The
hypothesis is satisfiable: for effective $X$ the projection $\mathbf X\to\mathbf X^R$ is a homeomorphism, which covers the trivial ep-groupoid
of every M-polyfold, and paracompactness follows from regularity of $\mathbf X^R$ when $\mathbf X$ is second countable. Whether
Hausdorffness of $\mathbf X^R$ with $\mathbf X$ second countable suffices is not settled: a locally metrizable, second countable Hausdorff
space need not be regular (Findings, items 56, 60, 111). The proof has four possible misprints, such as "$(s|\mathbf U(\psi))^{-1}(s(\psi))$" for
$(s|\mathbf U(\psi))^{-1}(s(\psi'))$ and $T_x$ for $T_{s(\varphi)}$ (Findings, item 57).

**Proposition 7.10 (2017) and the reduced ep-groupoid.** With the structure maps induced on $\mathbf X^R$, $X_R = (X,\mathbf X^R)$ is an ep-groupoid, and it
is effective. Its isotropy group at $x$ is $G_x/T_x$, the *effective isotropy group* $G_x^{\mathrm{eff}}$ of Definition 7.2.15 (2017: 7.13).

*Proof.* (1): on a sheet $\mathbf U$, the source and target of $\mathbf X^R$ are $s\circ(p|\mathbf U)^{-1}$ and $t\circ(p|\mathbf U)^{-1}$ for the projection $p:\mathbf X\to\mathbf X^R$. (3), "proved
similarly": the target map of $X$ is that of $X_R$ composed with the continuous surjection $\mathbf X\to\mathbf X^R$, and properness descends. (4) in
sheet form, with a step the text leaves implicit. Effectiveness comes from the intrinsic description of $T_x$: a reduced
morphism near $[g]$ with $s = t$ on a neighbourhood would put $g$ in $T_x$. The kernel of $G_x\to\mathrm{mor}_{X_R}(x,x)$ is $T_x$, and the map is onto.
$\square$

For effective $X$, $X_R\cong X$. Definition 7.2.15 (2017: 7.13) has "For and object" (possible misprint) (Findings, items 58, 59). *Checked by
machine (V7.39–V7.41):* `Polyfold.EpGroupoid.isOpenMap_reducedπ`, `Polyfold.EpGroupoid.reducedChart`,
`Polyfold.EpGroupoid.reducedChart_compatible`, `Polyfold.EpGroupoid.reducedPolyfold`,
`Polyfold.EpGroupoid.proposition_7_9`, `Polyfold.EpGroupoid.t2Space_reducedMor_of_isEffective`,
`Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_isEffective`, `Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_t3`,
`Polyfold.EpGroupoid.reducedEpGroupoid`, `Polyfold.EpGroupoid.exists_isProperMap_reduced`,
`Polyfold.EpGroupoid.isScSmoothCompSheet_reduced`, `Polyfold.EpGroupoid.isEffective_reducedEpGroupoid`,
`Polyfold.EpGroupoid.proposition_7_10`, `Polyfold.EpGroupoid.reductionIso`,
`Polyfold.EpGroupoid.quotientTrivialSubgroupEquiv`, `Polyfold.EpGroupoid.EffIsotropy`,
`Polyfold.EpGroupoid.effIsotropyEquivReduced`.

## 6. The topology of the orbit space and the index lift (pp. 319–328 (2017 pp. 244–248))

**Theorem 7.3.1 (2017: 7.2).** $|X|$ is locally metrizable, regular and Hausdorff; if $|X|$ is paracompact, it is metrizable.

"Locally metrizable" is read: every point has an open neighbourhood that is metrizable in the subspace topology. The
proof is Lemmas 7.3.2–7.3.5 (2017: 7.4–7.7); the metrizability of a paracompact $|X|$ is Smirnov's theorem (a paracompact Hausdorff locally
metrizable space is metrizable), in the form proved for Part I (Findings, item 70). *Checked by machine (V7.42):*
`Polyfold.EpGroupoid.theorem_7_2`, `Polyfold.EpGroupoid.theorem_7_2_metrizable`, `Polyfold.metrizableSpace_of_locally`.

**Lemma 7.3.2 (2017: 7.4).** Every point of $|X|$ has a metrizable open neighbourhood, namely $|U(x)| = \pi(U(x))$ for a natural representation at $x$.

*Proof.* Let $d$ be a metric for $U = U(x)$ (Theorem 2.3.10 (2017: 2.2)) and $\rho(y,y') = \max_{g\in G_x}d(g*y,g*y')$, a $G_x$-invariant metric with the same
topology. On $G_x\backslash U$, $\hat\rho([y],[y']) = \min_h\rho(y,h*y')$ is a metric for the quotient topology; its triangle inequality uses the
invariance of $\rho$. By Proposition 7.1.19 (2017: 7.6), $G_x\backslash U$ is homeomorphic to the open set $|U(x)|$. $\square$

$\hat\rho$ is computed as $\min_h\rho(y,h*y')$, equal to the text's expression by invariance (Findings, item 71). *Checked by machine
(V7.43):* `Polyfold.EpGroupoid.metrizableSpace_orbitRel_quotient_naturalRep`, `Polyfold.EpGroupoid.lemma_7_4_naturalRep`,
`Polyfold.EpGroupoid.lemma_7_4`.

**Lemmas 7.3.3–7.3.5 (2017: 7.5–7.7).** Lemma 7.3.3 (2017: 7.5), the countable neighbourhood bases, is Proposition 7.1.9 (2017: 7.2). Lemma 7.3.5 (2017: 7.7), *$|X|$ is regular*: given
$|x|\in W$ open, choose an open $U\ni x$ with the properness property and $\mathrm{cl}_XU\subseteq\pi^{-1}(W)$, possible since $X$ is metrizable and
properness passes to smaller sets; then $\pi(\mathrm{cl}_XU) = \mathrm{cl}_{|X|}\pi(U)$ by Proposition 7.1.10 (2017: 7.3) is a closed neighbourhood of $|x|$ inside $W$.
Lemma 7.3.4 (2017: 7.6), *$|X|$ is Hausdorff*, then follows: points of $|X|$ are closed, as $\{x\}$ is compact, hence a proper subset, whose image is
closed (Proposition 7.5.10 (1) (2017: 7.14), §7), and a regular space with closed points is Hausdorff. The text proves Lemma 7.3.4 (2017: 7.6)
directly (Findings, item 72). *Checked by machine (V7.44–V7.46):* `Polyfold.EpGroupoid.lemma_7_5`,
`Polyfold.EpGroupoid.t1Space_orbitSpace`, `Polyfold.EpGroupoid.lemma_7_6`, `Polyfold.EpGroupoid.lemma_7_7`.

**Corollary 7.3.6 (2017: 7.1).** If $|X|$ is second countable, it is metrizable. This is Urysohn's theorem. The text adds that a subset of
$|X|$ is again locally metrizable, regular and Hausdorff, so that a paracompact subset is metrizable (Findings, item 73).
*Checked by machine (V7.47, V7.48):* `Polyfold.EpGroupoid.corollary_7_1`,
`Polyfold.EpGroupoid.exists_metrizable_nhds_subtype`, `Polyfold.EpGroupoid.metrizableSpace_of_paracompactSpace_subtype`.

**Definition 7.3.7 (2017: 7.14).** $K\subseteq|X|$ is *component compact* if $K\cap C$ is compact for every connected component $C$ of $|X|$.

**Michael's theorem (Part I, Lemma 2.7.3 (2017: 2.7) and Proposition 2.7.4 (2017: 2.17)).** A regular space is paracompact if and only if every open
cover has a locally finite closed refinement; and a regular space with a locally finite cover by closed paracompact
subspaces is paracompact. Part I left both unformalized, as not needed there (gap G.15); they are now proved, for
regular spaces, without the Hausdorff property that the text assumes. The Lean names carry the preprint numbers, Lemma
2.56 and Proposition 2.57 (Findings, item 75). *Checked by machine (V7.50):* `Polyfold.lemma_2_56`, `Polyfold.michael_tfae`,
`Polyfold.proposition_2_57`, `Polyfold.paracompactSpace_iUnion`, `Polyfold.paracompactSpace_biUnion_of_finite`.

**Corollary 7.3.8 (2017: 7.2).** A component compact $K\subseteq|X|$ has an open neighbourhood $U$ whose closure is paracompact; hence $\mathrm{cl}(U)$ and $U$ are
metrizable.

*Proof.* If $K$ is compact: every point of $K$ has an open neighbourhood with metrizable closure (Lemma 7.3.2 (2017: 7.4) and regularity);
finitely many of them cover $K$; let $U$ be their union. $\mathrm{cl}(U)$ is a finite union of closed metrizable, hence paracompact, sets,
and paracompact by Michael's theorem, which the text does not cite; it is metrizable as a paracompact subset of $|X|$. In
general the text works "in a connected component" of $|X|$. This needs the components to be open, which holds because $|X|$ is
locally connected, an open quotient of a locally path connected space (§3); and a step the text does not give: the
neighbourhoods found in the different components form a locally finite family of closed paracompact sets, whose union is
paracompact by Michael's theorem. $\square$

In the proof, $U$ names both $\bigcup_i\mathrm{cl}\,U(z_i)$ and $\bigcup_iU(z_i)$ (possible misprint) (Findings, item 74). *Checked by machine (V7.49,
V7.51):* `Polyfold.EpGroupoid.IsComponentCompact`, `Polyfold.EpGroupoid.locallyPathConnectedSpace_orbitSpace`,
`Polyfold.EpGroupoid.exists_isOpen_metrizableSpace_closure`, `Polyfold.EpGroupoid.corollary_7_2_of_isCompact`,
`Polyfold.EpGroupoid.corollary_7_2`.

**Proposition 7.3.9 (2017: 7.11) (the index lift).** $X^1 = (X_1,\mathbf X_1)$, with the M-polyfold structures of level $1$ and the restricted structure
maps, is an ep-groupoid; if $X$ is tame, so is $X^1$.

*Proof.* The structure maps preserve level $1$; for $m$ this uses that $t(\varphi\circ\psi) = t(\varphi)$ lies on the level of $\varphi$ (§1). (1): the
level-one lift of a local sc-diffeomorphism is one. (2): Part I's lift of sc-smooth maps. (4): the text's "trivially" uses,
as we read it, $(\mathbf X\,{}_s{\times}_t\,\mathbf X)^1 = \mathbf X^1\,{}_s{\times}_t\,\mathbf X^1$ as M-polyfolds, which is not proved here; the sheet form avoids it. (3): for $x\in X_1$
take $V(x)$ with the properness property in $X$. Let $(\varphi_k)$ be morphisms on level $1$ with sources in the level-one closure of
$V(x)\cap X_1$ and targets converging in $X_1$. Properness in $X$ gives a subsequence converging in $\mathbf X$ to some $\varphi$; for large $k$ the $\varphi_k$
lie in a sheet of $t$ at $\varphi$, on which $t$ is an sc-diffeomorphism, so $\varphi_k = (t|\text{sheet})^{-1}(t(\varphi_k))$ converges on level $1$. $\square$

The text has "$(t(\varphi_k))$ belongs to a compact subset of $X_1$", replaced by "$t(\varphi_k)$ converges in $X_1$", and its step (b) is not
needed; display (7.5) lacks a closing parenthesis (possible misprint) (Findings, items 80, 96).

*Tameness.* The text gives no argument for "if $X$ is tame so is $X^1$". As we read it, the claim needs that the index lift of a
tame retraction is tame, which Part I left open (Chapter 5, item 145). It is proved: for a presentation $E\cong\mathbb R^n\oplus W$ of the
partial quadrant, the shifted presentation of the level-one quadrant has the same $\mathbb R^n$-coordinates, so the degeneracy index
does not change, and the relevant subspace $E_x$ for it is $E_x\cap E_1$; the derivative of the lifted retraction has range
$T_xO\cap E_1$, and an sc-complement $A$ of $T_xO$ gives the sc-complement $A\cap E_1$. With Part I's independence of the presentation,
the level-one charts of tame charts form a tame atlas of $X^1$ (Findings, items 81, 115). *Checked by machine (V7.52):*
`Polyfold.EpGroupoid.liftGroupoidStr`, `Polyfold.MPolyfold.IsLocalScDiffeo.levelOne`,
`Polyfold.EpGroupoid.exists_isProperMap_lift`, `Polyfold.EpGroupoid.isScSmoothCompSheet_lift`,
`Polyfold.EpGroupoid.liftOne`, `Polyfold.MPolyfold.IsTame.levelOne`, `Polyfold.EpGroupoid.isTame_liftOne`,
`Polyfold.EpGroupoid.proposition_7_11`.

## 7. Paracompact orbit spaces and proper subsets (pp. 340–344 (2017 pp. 249–252))

**Definition 7.5.1 (2017: 7.15).** $X$ has a *paracompact orbit space* if (5) $|X|$ is paracompact. Hausdorffness is not required; it holds by
Lemma 7.3.4 (2017: 7.6). The text notes that if $X$ is second countable, (1)–(4) of Definition 7.1.3 (2017: 7.3) imply (5); read with $X$ the object space,
$|X|$ is then second countable ($\pi$ is open), metrizable by Corollary 7.3.6 (2017: 7.1), hence paracompact. The text's sentence "it is presently
not known whether the property (5) is a consequence of the properties (1)–(4)" (p. 340 (2017 p. 249)) states an open question; it is not
formalized and not given a gap, since nothing depends on it. Remark 7.5.2 (2017: 7.1), that [38] required second countability, has
no formal content (Findings, items 82, 113). *Checked by machine (V7.53):* `Polyfold.EpGroupoid.HasParacompactOrbitSpace`,
`Polyfold.EpGroupoid.remark_7_1`, `Polyfold.EpGroupoid.hasParacompactOrbitSpace_of_secondCountableTopology`,
`Polyfold.EpGroupoid.hasParacompactOrbitSpace_iff_metrizableSpace`.

**Proposition 7.5.3 (2017: 7.12).** If $|X|$ is paracompact, so is $|X^1|$.

*Proof.* The text writes $|X_1|$ for the orbit space of $X^1$, treats it as the subset $\pi(X_1)$ of $|X|$, and argues with Lemma 2.7.3 (2017: 2.7) and
Michael's unions. Here $|X^1|$ keeps its own quotient topology, with the continuous injection $|X^1|\to|X|$ onto $\pi(X_1)$. A general
lemma: a space with a continuous map to a paracompact Hausdorff space, under which every point has an open neighbourhood
with metrizable preimage, is metrizable (the local metrics are glued with a partition of unity). $|X|$ is paracompact and,
by Lemma 7.3.4 (2017: 7.6), Hausdorff. Every point of $|X|$ has the neighbourhood $\pi(U(x))$ of a natural representation, and its preimage in
$|X^1|$ is the quotient of $U(x)\cap X_1$, with the level-one topology, by the restricted $G_x$-action, metrizable as in Lemma 7.3.2 (2017: 7.4). So
$|X^1|$ is metrizable, hence paracompact. $\square$

The conclusion is stronger than the text's. $U(x)\cap X_1$ need not be connected in $X^1$, so it is not a natural representation of
$X^1$; only the restricted action is used. The regularity of $|X^1|$ is not needed on this route (Findings, item 83). *Checked
by machine (V7.54):* `Polyfold.EpGroupoid.orbitIncl`, `Polyfold.EpGroupoid.continuous_orbitIncl`,
`Polyfold.EpGroupoid.range_orbitIncl`, `Polyfold.EpGroupoid.NaturalRep.liftMulAction`,
`Polyfold.EpGroupoid.NaturalRep.metrizableSpace_preimage_orbitIncl`, `Polyfold.metrizableSpace_of_pullback`,
`Polyfold.EpGroupoid.proposition_7_12`.

**Definition 7.5.8 (2017: 7.17) (proper subsets).** $Q\subseteq X$ is *proper* if $t:s^{-1}(Q)\to X$ is proper; an open $U$ has the *properness property* if
$\mathrm{cl}_XU$ is proper. So Definition 7.1.3 (3) (2017: 7.3) says that every object has a neighbourhood with the properness property, and every
smaller open neighbourhood has it too. $Q$ is proper if and only if $s^{-1}(Q)\cap t^{-1}(K)$ is compact for every compact $K$; closed subsets of
proper sets, finite unions of proper sets and compact sets are proper (Findings, item 92). *Checked by machine (V7.59):*
`Polyfold.EpGroupoid.IsProperSubset`, `Polyfold.EpGroupoid.HasPropernessProperty`,
`Polyfold.EpGroupoid.HasPropernessProperty.mono`, `Polyfold.EpGroupoid.isProperSubset_iff_isCompact`,
`Polyfold.EpGroupoid.isProperSubset_of_isCompact`.

**Proposition 7.5.9 (2017: 7.13).** Proper subsets of $X$ are closed.

*Proof.* Let $x_k\to x$ with $x_k\in Q$. The units $1_{x_k}$ lie in $s^{-1}(Q)\cap t^{-1}(K)$, $K = \{x\}\cup\{x_k\}$, which is compact, so a
subsequence converges in $s^{-1}(Q)$; its limit $\varphi$ has $t(\varphi) = x = s(\varphi)$, so $x = s(\varphi)\in Q$. $\square$

*Checked by machine (V7.60):* `Polyfold.EpGroupoid.proposition_7_13`, `Polyfold.EpGroupoid.IsProperSubset.isClosed`.

**Proposition 7.5.10 (2017: 7.14).** (1) If $Q$ is proper, $\pi(Q)$ is closed in $|X|$. (2) If $|X|$ is paracompact, $A\subseteq|X|$ is closed if and only if $A = \pi(Q)$ for
a proper $Q$.

*Proof.* (1): $\pi^{-1}(\pi(Q)) = t(s^{-1}(Q))$ is the image of the closed set $s^{-1}(Q)$ under the proper, hence closed, map $t:s^{-1}(Q)\to X$; it is
closed and saturated, so $\pi(Q)$ is closed. (2): one direction is (1). For $A$ closed, choose for every $z\in A$ an object $x_z$ with $|x_z| = z$
and an open $V(x_z)$ with the properness property. The open sets $\pi(V(x_z))$ cover $A$; take a locally finite open refinement $(v_z)$ of
this cover of $A$ with $v_z\subseteq\pi(V(x_z))$, which paracompactness alone provides. Put $P_z = \mathrm{cl}_X(V(x_z))\cap\pi^{-1}(\mathrm{cl}(v_z)\cap A)$, a closed subset of the
proper set $\mathrm{cl}_X(V(x_z))$, hence proper, with $\pi(P_z)\subseteq\mathrm{cl}(v_z)$. The closures of a locally finite family are locally finite, so
$Q = \bigcup_zP_z$ is proper: a compact set has compact image in $|X|$, which meets only finitely many $\mathrm{cl}(v_z)$. And $\pi(Q) = A$, since
every $a\in A$ lies in some $v_z\subseteq\pi(V(x_z))$. $\square$

The text proves (1) with sequences, and for (2) takes a locally finite *closed* refinement from Lemma 2.7.3 (2017: 2.7), which assumes
$|X|$ regular and Hausdorff (true by Theorem 7.3.1 (2017: 7.2)); the route above needs paracompactness only, and any neighbourhood with
the properness property serves for the text's $U(x_z)$. "$\mathrm{cl}_X(U_{x_{z_i}})$" stands for $\mathrm{cl}_X(U(x_{z_i}))$ (possible misprint)
(Findings, item 92). *Checked by machine (V7.61):* `Polyfold.EpGroupoid.isClosed_saturation_of_isProperSubset`,
`Polyfold.EpGroupoid.proposition_7_14_one`, `Polyfold.EpGroupoid.isProperSubset_iUnion_of_locallyFinite`,
`Polyfold.EpGroupoid.exists_hasPropernessProperty_subset`, `Polyfold.EpGroupoid.proposition_7_14_two`.

## 8. Invariant sc-smooth partitions of unity (pp. 341–343 (2017 pp. 250–251); Appendix 7.6.2 (2017 7.5.2), pp. 345–347 (2017 pp. 254–256))

**Theorem 7.5.4 (2017: 7.3).** Let $|X|$ be paracompact. Every open cover of $|X|$ has a subordinate continuous partition of unity, and every
cover of $X$ by saturated open sets $(U_\lambda)$ has a subordinate continuous partition of unity $(\beta_\lambda)$ with (1) every object has a
saturated open neighbourhood meeting only finitely many $\mathrm{supp}\,\beta_\lambda$, and (2) $\beta_\lambda(s(\varphi)) = \beta_\lambda(t(\varphi))$ for every morphism $\varphi$.

*Proof.* $|X|$ is paracompact and, by Lemma 7.3.4 (2017: 7.6), Hausdorff, hence normal, so it has partitions of unity subordinate to every
open cover. For a saturated cover, the sets $\pi(U_\lambda)$ form an open cover of $|X|$; pull back a subordinate partition of unity by $\pi$. $\square$

The text's "due to paracompactness" needs normality, that is, the Hausdorff property, which Definition 7.5.1 (2017: 7.15) does not
require and Lemma 7.3.4 (2017: 7.6) provides (Findings, item 90). *Checked by machine (V7.55):* `Polyfold.EpGroupoid.orbitPullback`,
`Polyfold.EpGroupoid.orbitPullback_isSubordinate`, `Polyfold.EpGroupoid.theorem_7_3`.

**Definition 7.5.5 (2017: 7.16).** $X$ *has sc-smooth partitions of unity* if every cover of $X$ by saturated open sets has a subordinate
sc-smooth partition of unity with (1) and (2) of Theorem 7.5.4 (2017: 7.3). The index types are taken in the universe of $X$, supports
are closed supports, and (2) is $\beta_\lambda(s(\varphi)) = \beta_\lambda(t(\varphi))$. Remark 7.5.6 (2017: 7.2) observes that, apart from sc-Hilbert spaces, sc-smooth
partitions of unity are "a zoo"; it has no formal content, and the sc-Hilbert case is Part I's (Corollary 7.6.6 (2017: 7.3) below)
(Findings, item 91). *Checked by machine (V7.56, V7.57):* `Polyfold.EpGroupoid.HasScPartitionsOfUnity`,
`Polyfold.MPolyfold.IsScSmoothPartitionOfUnity`.

**Theorem 7.5.7 (2017: 7.4)** *(2017 p. 251; restated as Theorem 7.6.4 (2017: 7.6), p. 346 (2017 p. 255)).* If $|X|$ is paracompact and the object M-polyfold admits sc-smooth
partitions of unity, then $X$ has sc-smooth partitions of unity.

The proof (Appendix 7.6.2 (2017 7.5.2)) averages over the local groups. It rests on a lemma.

**Lemma 7.6.5 (2017: 7.10) (invariant majorants).** Let $|X|$ be paracompact and let the object M-polyfold admit sc-smooth partitions of
unity. Let $(V,\Phi,\Gamma)$ be a natural representation at $x$ and $U$ an open $G_x$-invariant set with
$\mathrm{cl}_XU\subseteq V$. If $\beta:X\to[0,1]$ is continuous, supported in $U$ and invariant ($\beta(g*y) = \beta(y)$ on $V$), there is an sc-smooth $f:X\to[0,\infty)$,
invariant on $V$, with $\beta\le f$ and $\mathrm{supp}\,f\subseteq\mathrm{cl}_XU\subseteq V$.

*Proof.* The open sets $U$ and $X\setminus\mathrm{supp}\,\beta$ cover $X$. Let $(\alpha_1,\alpha_2)$ be a subordinate sc-smooth partition of unity of $X$. Then $\alpha_2 = 0$
on $\mathrm{supp}\,\beta$, so $\alpha_1 = 1\ge\beta$ there, and $\alpha_1\ge\beta$ everywhere. Average: $f(y) = |G_x|^{-1}\sum_g\alpha_1(g*y)$ on $V$, and $f = 0$ off $V$. Then $f$ is invariant,
$f\ge\beta$ because $\alpha_1(g*y)\ge\beta(g*y) = \beta(y)$, and $\mathrm{supp}\,f\subseteq\bigcup_gg*\mathrm{cl}_XU = \mathrm{cl}_XU$; it is sc-smooth on $V$ and zero on $X\setminus\mathrm{cl}_XU$, two
open sets covering $X$. $\square$

The text takes a partition of unity of the cover of $V(x)$ by small sets; the hypothesis, however, is that $X$, not $V(x)$, admits
sc-smooth partitions of unity, so the cover is completed by $X\setminus\mathrm{cl}\,U(x)$ and coarsened to two sets. The bound $\mathrm{supp}\,f\subseteq\mathrm{cl}_XU$,
which the proof gives and the proof of Theorem 7.5.7 (2017: 7.4) needs, is added to the statement; $x\in U$ is not used, and neither are the
paracompactness of $|X|$ and the continuity of $\beta$, which are kept (Findings, item 93).
*Checked by machine (V7.66):* `Polyfold.EpGroupoid.lemma_7_10`.

*Proof of Theorem 7.5.7 (2017: 7.4).* Let $(U_\lambda)$ be a saturated open cover of $X$. For every $x$ choose open sets $V(x)\subseteq\mathrm{cl}_XV(x)\subseteq W(x)$ with
(1) $W(x)$ carrying a natural representation and $V(x)$ invariant, (2) $t:s^{-1}(\mathrm{cl}_XV(x))\to X$ proper, (3) $V(x)\subseteq U_\lambda$ for some $\lambda$, and (4)
$(\pi^{-1}(|V(x)|)\setminus V(x))\cap W(x) = \emptyset$. Property (4) is not a further choice: it follows from (1), since a point $y\in W(x)$ with $|y|\in|V(x)|$ is joined
to a point of $V(x)$ by a morphism between points of $W(x)$, so $y = g*v$ with $v\in V(x)$, and $y\in V(x)$ by invariance. The sets $|V(x)|$ cover
$|X|$; take a locally finite refinement $(V'_i)$ with $V'_i\subseteq|V(x_i)|$, open sets $V''_i$ with $\mathrm{cl}(V''_i)\subseteq V'_i$ that still cover $|X|$, and a
continuous partition of unity $(\beta_i)$ subordinate to $(V''_i)$. Put $U''_i = V(x_i)\cap\pi^{-1}(V''_i)$. Lemma 7.6.5 (2017: 7.10) gives an invariant sc-smooth
$f_i\ge\beta_i\circ\pi$ on $V(x_i)$, supported in $\mathrm{cl}_XU''_i$; extended to the saturation of $V(x_i)$ through the morphisms and by $0$ outside, it is a
function $h_i$ on $X$ compatible with morphisms. The sum $h = \sum_ih_i$ is locally finite and positive, and $(h_i/h)$ is the partition of
unity. $\square$

Four points of this proof need more than a reading, and all four stand. (a) Lemma 7.6.5 (2017: 7.10) is applied with $W(x_i)$ in the role of
$V(x)$ and $U''_i$ in the role of $U(x)$, since $\mathrm{cl}\,U''_i\subseteq\mathrm{cl}\,V(x_i)\subseteq W(x_i)$; the text's "approximate $(\beta_i\circ\pi)|V(x_i)$ using Lemma 7.10" reads
as $V(x_i)$ in the role of $V(x)$ (possible misprint). (b) The continuity of the cut-off $(\beta_i\circ\pi)|V(x_i)$, extended by $0$, uses (4). (c)
"The sum of all $h_i$ is locally finite" needs $\mathrm{supp}\,f_i\subseteq\pi^{-1}(\mathrm{cl}\,V'_i)$, which Lemma 7.6.5 (2017: 7.10) as stated does not give and its proof does. (d)
The sc-smoothness of $h_i$ uses that the saturation of the support, a closed subset of the proper set $\mathrm{cl}_XV(x_i)$, is closed
(Proposition 7.5.10 (1) (2017: 7.14)). "We average" needs no second average, the $f_i$ being invariant already. The normalization $(h_i/h)$
and the return from the index set of the refinement to $\Lambda$, which the text leaves implicit, are replaced by Mathlib's bump
coverings, as in Part I's Theorem 5.5.10 (2017: 5.12), with the construction above as the Urysohn-type input. In property (2),
"$t:s^{-1}(\mathrm{cl}_X(V(x))\to X$" lacks a closing parenthesis (possible misprint) (Findings, items 94, 96). *Checked by machine (V7.58,
V7.65, V7.67):* `Polyfold.EpGroupoid.exists_invariant_nhds_of_isOpen`,
`Polyfold.EpGroupoid.mem_of_π_mem_image_of_invariant`, `Polyfold.EpGroupoid.orbitExtension`,
`Polyfold.EpGroupoid.isScSmoothMap_orbitExtension`, `Polyfold.EpGroupoid.exists_isScSmoothMap_orbit_urysohn`,
`Polyfold.admitsScPartitionsOfUnity_of_approx`, `Polyfold.EpGroupoid.theorem_7_4`, `Polyfold.EpGroupoid.theorem_7_6`.

**Corollary 7.6.6 (2017: 7.3).** If $|X|$ is paracompact and the object M-polyfold has an atlas whose local models have Hilbert spaces $E_0$,
every cover of $X$ by saturated open sets has a subordinate sc-smooth partition of unity of $X$.

*Proof.* The atlas gives sc-smooth partitions of unity of the object M-polyfold (Part I, Proposition 5.5.8 (2017: 5.6), Theorem 5.5.10 (2017: 5.12),
Corollary 5.5.17 (2017: 5.2)), and Theorem 7.5.7 (2017: 7.4) applies. $\square$

In Part I that existence rests on the theorem of Godefroy–Troyanski–Whitfield–Zizler (Part I's Theorem 5.5.16 (2017: 5.14)), which the
project takes as an explicit hypothesis (gap G.53); it holds for finite-dimensional spaces. "Hilbert" is read as
$\|v\|^2 = b(v,v)$ for a continuous bilinear $b$, and the atlas is existential, one chart per point; "every compatible chart has a
Hilbert $E_0$" could not be satisfied (Findings, items 95, 106). *Checked by machine (V7.68):*
`Polyfold.EpGroupoid.corollary_7_3`, `Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert`,
`Polyfold.GodefroyTroyanskiWhitfieldZizlerStatement`, `Polyfold.EpGroupoid.corollary_7_3_hypotheses_rn`.

## 9. Witnesses: the hypotheses can hold

A hypothesis that no ep-groupoid satisfies would make a theorem empty. The formalization checks every hypothesis of the
chapter on examples, all in Lean (`Polyfold/Chapter7/NonVacuity.lean` and the files of the definitions; Findings, items
100–106).

- *Action ep-groupoids.* A finite discrete group $K$ acting on an M-polyfold $U$ by sc-smooth maps gives an ep-groupoid with
  morphisms $K\times U$, $s(g,y) = y$, $t(g,y) = g\cdot y$. Its isotropy groups are the stabilizers and its orbit space is $U/K$; a subset is
  proper if and only if it is closed, every open set has the properness property, and the orbit space is paracompact
  when $U$ is second countable. `Polyfold.EpGroupoid.Examples.actionEpGroupoid`,
  `Polyfold.EpGroupoid.Examples.isProperSubset_action_iff`,
  `Polyfold.EpGroupoid.Examples.hasParacompactOrbitSpace_action`.
- *An effective ep-groupoid with non-trivial isotropy.* $\{\pm1\}$ acting on $\mathbb R$ by $y\mapsto\pm y$: effective, with $G_0\cong\mathbb Z/2$, $X_{reg} = \mathbb R\setminus\{0\}$,
  $T_0 = 1$, tame, with paracompact orbit space; so Definition 7.2.1 (2017: 7.11) is not vacuous. This is the $v$-coordinate of the two beads
  of §0. `Polyfold.EpGroupoid.Examples.reflectionEpGroupoid`,
  `Polyfold.EpGroupoid.Examples.isEffective_reflection_nonvacuous`, `Polyfold.EpGroupoid.Examples.isTame_reflection`.
- *A non-effective ep-groupoid.* $\mathbb Z/3$ acting trivially on $\mathbb R$: $G_x\cong\mathbb Z/3$, $T_x = G_x$, not effective, $X_{reg} = \emptyset$. It carries the
  counterexample of §1. `Polyfold.EpGroupoid.Examples.trivialZ3EpGroupoid`,
  `Polyfold.EpGroupoid.Examples.not_isEffective_trivialZ3`.
- *Properness cannot be universal.* The pair groupoid of $\mathbb Z$ is an ep-groupoid, but $t:s^{-1}(\mathrm{cl}\,V)\to X$ is not proper for $V = \mathbb Z$.
  `Polyfold.EpGroupoid.Examples.pairEpGroupoid`, `Polyfold.EpGroupoid.Examples.pair_not_forall_isProperMap`.
- *The trivial ep-groupoid of an M-polyfold* $P$, with only identities: tame for tame $P$, effective, $X_{reg} = X$, every closed set
  proper, $|X|\cong P$, paracompact orbit space, with natural representations and ep-subgroupoids; on $\mathbb R^n$ it satisfies the
  hypotheses of Theorems 7.5.7, 7.6.4 (2017: 7.4, 7.6) and of Corollary 7.6.6 (2017: 7.3). `Polyfold.EpGroupoid.isEffective_trivial`,
  `Polyfold.EpGroupoid.hasParacompactOrbitSpace_trivial`, `Polyfold.EpGroupoid.theorem_7_4_hypotheses_rn`,
  `Polyfold.EpGroupoid.corollary_7_3_hypotheses_rn`.

Every hypothesis that quantifies over charts or neighbourhoods is existential and satisfiable: tameness (a tame atlas),
the Hilbert atlas of Corollary 7.6.6 (2017: 7.3) (one chart per point), properness (one neighbourhood per point), the natural
representation (a datum, which exists inside every neighbourhood); the hypotheses on $\mathbf X^R$ of Proposition 7.2.10 (2017: 7.9) and Proposition 7.10 (2017; rewritten in 2021 as Theorem 7.2.14) are
satisfiable as well (§5). No hypothesis of the form "for all compatible charts" is made in Chapter 7 (Findings, item 106).

## 10. Application: identical particles on a line

The computations below were done by hand; they are not checked in Lean. The ep-groupoids are action ep-groupoids, of
which the general construction is formalized (§9), but the instances for the symmetric groups are not written out.

**The ep-groupoid.** $n$ identical particles on a line: $X = \mathbb R^n$ with the constant sc-structure (a finite-dimensional space is an
M-polyfold, with the identity as retraction, and tame since it has no boundary), and the symmetric group $S_n$ acting by
permuting coordinates, $(\sigma\cdot x)_i = x_{\sigma^{-1}(i)}$, which is linear, hence sc-smooth. The morphisms are $S_n\times\mathbb R^n$, $n!$ copies of $\mathbb R^n$, with
$s(\sigma,x) = x$, $t(\sigma,x) = \sigma\cdot x$ and $(\tau,\sigma\cdot x)\circ(\sigma,x) = (\tau\sigma,x)$.

**Two particles.** In the coordinates $u = (x_1+x_2)/2$, $v = (x_2-x_1)/2$ the swap is $(u,v)\mapsto(u,-v)$: the ep-groupoid is the product of
the trivial ep-groupoid on $\mathbb R$ (in $u$) with the reflection ep-groupoid of §9 (in $v$). $G_x$ is trivial for $v\neq0$ and $\mathbb Z/2$ on the
diagonal; $X_{reg} = \{x_1\neq x_2\}$, two open half-planes, open and dense. The ep-groupoid is effective: a neighbourhood of
$(\text{swap},(u,0))$ contains $(\text{swap},(u,v))$ with $v\neq0$, whose source $(u,v)$ and target $(u,-v)$ differ; so $T_x = 1$, $\mathbf X^R = \mathbf X$ and $X_R\cong X$.
A natural representation at $(u_0,0)$ is any open disc about it, with $\Phi(\text{swap})(u,v) = (u,-v)$ and $\Gamma(g,y) = (g,y)$; at $(u_0,v_0)$ with $v_0\neq0$,
$G = 1$ and a disc of radius less than $|v_0|$ serves, the swap carrying it off itself. With the Euclidean metric $d$, which the swap
preserves, $\rho = d$ in Lemma 7.3.2 (2017: 7.4), and
$$\hat\rho([u,v],[u',v'])^2 = \min\bigl((u-u')^2+(v-v')^2,\ (u-u')^2+(v+v')^2\bigr) = (u-u')^2+(|v|-|v'|)^2 ,$$
so $(u,v)\mapsto(u,|v|)$ is an isometry of $|X|$ onto the half-plane $\mathbb R\times[0,\infty)$. As in §0, the half-plane carries the right metric
and topology, while the smooth structure is kept upstairs: the smooth invariant functions are the smooth functions of $u$ and
$v^2$, and $2|v| = |x_2-x_1|$ is not one of them.

**Three particles.** The isotropy group of $x\in\mathbb R^3$ is the stabilizer of the coordinate pattern: trivial if the three
coordinates are distinct, $\mathbb Z/2$ (the transposition of the two equal ones) if exactly two are equal, $S_3$ if all three are equal;
orders $1$, $2$, $6$, as Proposition 7.1.12 (2017: 7.4) requires, and constant along orbits, as conjugation requires. $X_{reg}$ is the
complement of the three planes $x_i = x_j$, six open chambers, open and dense (Proposition 7.2.4 (2017: 7.8)); $X$ is effective, since $S_3$ acts
faithfully on every open set, so $T_x = 1$. Sorting the coordinates identifies $|X|$ with the closed chamber $C = \{x_1\le x_2\le x_3\}$, the
product of the line $\mathbb R(1,1,1)$ with a wedge of angle $\pi/3$ in the orthogonal plane (the normals $(1,-1,0)$ and $(0,1,-1)$ of the walls
make the angle $2\pi/3$). The edge of the wedge has isotropy $S_3$, the two open faces $\mathbb Z/2$, the interior $1$.

*A natural representation.* At $x = (0,0,1)$, $G_x = \{1,(12)\}$. Let $U$ be the sup-norm ball of radius $r<1/2$ about $x$: it is connected and
invariant under $(12)$. If $y,y'\in U$ and $\sigma\cdot y = y'$, then $|x_i-x_{\sigma^{-1}(i)}|\le|x_i-y'_i|+|y_{\sigma^{-1}(i)}-x_{\sigma^{-1}(i)}|<2r<1$ for every $i$, so $x_{\sigma^{-1}(i)} = x_i$ and
$\sigma\in G_x$: this is (3) of Theorem 7.1.13 (2017: 7.1), with $\Phi((12))$ the exchange of the first two coordinates and $\Gamma(\sigma,y) = (\sigma,y)$.

*Proposition 7.1.15 (2017: 7.5).* $Y = \{(0,0,1),(0,1,0),(1,0,0)\}$ consists of mutually isomorphic objects, each with isotropy of order $2$. Between any
two of them there are exactly two morphisms, so the full subcategory on $Y$ has $3\cdot3\cdot2 = 18$ morphisms. A natural
representation of it is given by the three disjoint sup-norm balls $U(y)$ of radius $r<1/2$, the maps $f(\sigma,y) = \sigma\cdot(-):U(y)\to U(\sigma\cdot y)$
and $\mathbf U(\sigma,y) = \{\sigma\}\times U(y)$; it is the transport of the ball at $(0,0,1)$ along the permutations, as in the proof of §3.

*The metric of Lemma 7.3.2 (2017: 7.4).* For a global action of a finite group by isometries the formula of Lemma 7.3.2 (2017: 7.4) defines a metric on
all of $|X|$. With the sup-norm, $\rho = d$ and $\hat\rho([y],[y']) = \min_\sigma\|y-\sigma\cdot y'\|_\infty$; for sorted $y$, $y'$ the minimum is attained at $\sigma = 1$ (exchanging
two crossed coordinates does not increase the maximum), so $|X|\cong C$ isometrically for the sup-norm. For example, the three
permutations of $(0,1,1)$ are all at sup-distance $1$ from $(0,0,1)$, and $\hat\rho([(0,0,1)],[(0,1,1)]) = 1$.

*The degeneracy index.* $\mathbb R^3$ has no boundary, so $d_X\equiv0$ and $d_{|X|}\equiv0$ by Definition 7.1.5 (2017: 7.5), although $|X|\cong C$ is, as a set, a wedge with
faces and an edge. The faces of the orbit space are not boundary of the ep-groupoid; this is why $d_{|X|}$ is read upstairs.

*Partitions of unity.* $X = \mathbb R^3$ is second countable, so $|X|$ is paracompact (Definition 7.5.1 (2017: 7.15)), and $\mathbb R^3$ has smooth partitions of unity;
Theorem 7.5.7 (2017: 7.4) applies. For a global action it is elementary: for an $S_3$-invariant open cover $(U_\lambda)$ take any subordinate smooth
partition of unity $(\alpha_\lambda)$ of $\mathbb R^3$ and average, $\beta_\lambda(x) = \frac{1}{6}\sum_{\sigma}\alpha_\lambda(\sigma\cdot x)$. Each $\beta_\lambda$ is smooth and invariant, so
$\beta_\lambda(s(\sigma,x)) = \beta_\lambda(t(\sigma,x))$; it is supported in $\bigcup_{\sigma}\sigma(\mathrm{supp}\,\alpha_\lambda)\subseteq U_\lambda$; and $\sum_{\lambda}\beta_\lambda = 1$. This is the averaging of Lemma 7.6.5 (2017: 7.10) done once
and globally; Theorem 7.5.7 (2017: 7.4) is needed when the symmetry is only local.

*Symmetries that move nothing.* Let $S_3\times\mathbb Z/2$ act, the factor $\mathbb Z/2$ trivially. Then $G_x$ is the stabilizer times $\mathbb Z/2$, and $T_x = \{1\}\times\mathbb Z/2$
for every $x$: an element acts trivially near $x$ exactly when its $S_3$-part is $1$. The ep-groupoid is not effective, and $\mathbf X^R$ is
$(S_3\times\mathbb Z/2\times\mathbb R^3)/(\mathbb Z/2)\cong S_3\times\mathbb R^3$, Hausdorff and paracompact, so that $X_R = S_3\ltimes\mathbb R^3$ and $G^{\mathrm{eff}}_x$ is the stabilizer in $S_3$. Here $T_x$ is
the same at every point; in the splicing example of §5 it jumps, and there $\mathbf X^R$ is not Hausdorff (checked by machine;
gap G.71).

## 11. Summary of what was silently assumed, now made explicit

| Where (2017 text) | HWZ say | What is actually needed |
|---|---|---|
| 2017 p. 227, Def. 7.1.3 (3) (2017: 7.3) | every $x$ has $V(x)$ with $t:s^{-1}(\mathrm{cl}_XV(x))\to X$ proper | one $V(x)$ per point; the sequential form; smaller $V$ inherit it; not every $V$ |
| 2017 p. 227, Def. 7.1.3 (4) (2017: 7.3) | "Lemma 2.8 in [38]" | Part I's Proposition 2.5.20 (2017: 2.15) (an external citation); the sheet form |
| p. 289 (2017 p. 227), Def. 7.1.4 (2017: 7.4) | $T\varphi$ an sc-isomorphism; "$\circ\, U(x)\to U(y)$" | only defined (G.7, G.70); a colon (possible misprint) |
| 2017 p. 228 | $\lvert X_\infty\rvert = \bigcap_k\lvert X_k\rvert$ | not stated (G.72) |
| 2017 p. 227 | $X_\infty$ dense in every $X_k$ | not formalized (G.73) |
| p. 290 (2017 p. 228), Def. 7.1.6 (2017: 7.6) | $\mathbf X$ tame | the tame atlas transported along $s$ |
| pp. 290–292 (2017 pp. 228–229), remark after Def. 7.1.7 (2017: 7.7) | sc-smooth on objects suffices | also continuous on morphisms; without it, does not hold as we read it |
| pp. 291–293 (2017 pp. 229–230), Props. 7.1.8, 7.1.10 (2017: 7.1, 7.3) | point by point; sequences | the saturation $t(s^{-1}(U))$; closedness of proper maps, for $A\subseteq\mathrm{cl}\,U$ |
| p. 292 (2017 p. 230), Lemma 7.1.11 (2017: 7.1) | the $\psi$ with $s(\psi) = x$ | the proof treats the inverses (possible misprint); both forms |
| p. 293 (2017 p. 230) | "no canonical identification" | unique up to an inner automorphism of $G_y$ |
| p. 293 (2017 p. 231), Thm. 7.1.13 (2017: 7.1) | an open $U(x)$ | $U(x)$ connected; M-polyfolds locally path connected |
| pp. 297–304 (2017 pp. 233–236), Prop. 7.1.15 (2017: 7.5) | induction with shrinking | transport from one object; twelve possible misprints |
| pp. 304 ff. (2017 pp. 236–237), Prop. 7.1.19 (2017: 7.6) | $\sigma$ open | not needed |
| p. 305 (2017 p. 237), Def. 7.1.20 (2017: 7.9) | "$\Psi_x\circ G_x\ltimes U(x)\to X$", "a a" | $\Psi_x:$ (possible misprints) |
| 2017 pp. 237–238 | the tangent facts (3), (4) | not restated (G.7) |
| 2017 p. 238 | "$t(\mathbf r(\psi))\in U(a)$" | not needed; $\mathbf A = s^{-1}(A)$ |
| pp. 307 ff. (2017 pp. 238–239), Prop. 7.1.22 (2017: 7.7) | "restrictions of sc-smooth maps" | sc-smoothness into $A$; inclusion of fibred products; $A$, $\mathbf A$ paracompact |
| p. 307 (2017 p. 239), Lemma 7.2.2 (2017: 7.2) | — | $\Gamma(1,a) = 1_a$, from $U$ connected |
| pp. 308–309 (2017 pp. 239–240), Lemma 7.2.3 (2017: 7.3) | "adapting restrictions" | the uniqueness of natural representations |
| pp. 309 ff. (2017 pp. 240–241), Prop. 7.2.4 (2017: 7.8) | the minimum over $U(x_0)$ | the minimum over the open set; the converse |
| 2017 p. 241 | "$U(x)$ so small that the kernel is $T_x$" | one $N$ for all natural representations inside it; $\varphi T_x\varphi^{-1} = T_y$ |
| p. 310 (2017 p. 241), Def. 7.2.7 (2017: 7.12) | "the subset $\mathbf X^R$" | a quotient (possible misprint) |
| pp. 313–324 (2017 pp. 242–244), Prop. 7.2.10 (2017: 7.9) and Prop. 7.10 (2017; rewritten in 2021 as Theorem 7.2.14) | $\mathbf X^R$ an M-polyfold | $\mathbf X^R$ Hausdorff and paracompact as hypotheses (G.71); not Hausdorff in general |
| pp. 325 ff. (2017 pp. 245–246), Lemmas 7.3.4, 7.3.5 (2017: 7.6, 7.7) | Lemma 7.3.4 (2017: 7.6) directly | Lemma 7.3.5 (2017: 7.7) first, then closed points |
| p. 326 (2017 p. 247), Cor. 7.3.8 (2017: 7.2) | "work in a connected component" | open components; a locally finite union; Michael's theorem |
| pp. 327–328 (2017 pp. 247–248), Prop. 7.3.9 (2017: 7.11) | "(1), (2) and (4) trivially"; "if $X$ is tame so is $X^1$" | the sheet form; the tameness of index lifts, proved |
| 2017 p. 248, Prop. 7.3.9 (3) (2017: 7.11) | $(t(\varphi_k))$ in a compact subset of $X_1$ | $t(\varphi_k)$ converges in $X_1$ |
| p. 340 (2017 p. 249), Def. 7.5.1 (2017: 7.15) | "$X$ second countable" | the object space |
| pp. 340 ff. (2017 pp. 249–250), Prop. 7.5.3 (2017: 7.12) | Lemma 2.7.3 (2017: 2.7), unions of closed paracompact sets | $\lvert X^1\rvert$ metrizable, along $\lvert X^1\rvert\to\lvert X\rvert$ |
| p. 341 (2017 p. 250), Thm. 7.5.4 (2017: 7.3) | "due to paracompactness" | Hausdorff (Lemma 7.3.4 (2017: 7.6)), for normality |
| pp. 343–344 (2017 pp. 251–252), Prop. 7.5.10 (2) (2017: 7.14) | Lemma 2.7.3 (2017: 2.7) | paracompactness alone |
| p. 346 (2017 p. 255), Lemma 7.6.5 (2017: 7.10) | a partition of unity of $V(x)$ | of $X$, for two sets; $\mathrm{supp}\,f\subseteq\mathrm{cl}_XU(x)$ |
| pp. 346–347 (2017 pp. 255–256), proof of Thm. 7.5.7 (2017: 7.4) | Lemma 7.6.5 (2017: 7.10) with $V(x_i)$; "the sum is locally finite"; $(h_i/h)$ | $W(x_i)$ (possible misprint); the support bound; Mathlib's bump coverings |
| p. 347 (2017 p. 256), Cor. 7.6.6 (2017: 7.3) | Part I, Prop. 5.5.8 (2017: 5.6), Thm. 5.5.10 (2017: 5.12), Cor. 5.5.17 (2017: 5.2) | Part I's Theorem 5.5.16 (2017: 5.14) as a hypothesis (G.53) |

---

**Checked by machine.** The chapter is formalized in Lean 4 against Mathlib in `Polyfold/Chapter7/` (`Groupoid.lean`,
`EpGroupoid.lean`, `ProperMaps.lean`, `LocalDiffeo.lean`, `Basic.lean`, `LocConnected.lean`, `Discrete.lean`,
`NaturalRep.lean`, `NaturalAction.lean`, `NaturalRepFinite.lean`, `Uniformizer.lean`, `SubGroupoid.lean`, `Effective.lean`,
`Reduced.lean`, `OrbitTopology.lean`, `Michael.lean`, `Lift.lean`, `ProperSubsets.lean`, `PartitionsOfUnity.lean`,
`NonVacuity.lean`); the paragraphs "*Checked by machine*" name the declarations. Formalized: every definition of the
chapter (Definitions 7.1.1–7.5.8 (2017: 7.1–7.17); the tangent $T\varphi$ of Definition 7.1.4 (2017: 7.4) as a definition only); Theorems 7.1.13–7.6.4 (2017: 7.1–7.6); Propositions
7.1.8–7.2.4 and 7.3.9–7.5.10 (2017: 7.1–7.8 and 7.11–7.14); Proposition 7.2.10 (2017: 7.9) and Proposition 7.10 (2017) under the hypothesis that $\mathbf X^R$ is Hausdorff and paracompact; Lemmas
7.1.11–7.6.5 (2017: 7.1–7.10); Corollaries 7.3.6–7.6.6 (2017: 7.1–7.3), Corollary 7.6.6 (2017: 7.3) with Part I's Theorem 5.5.16 (2017: 5.14) as a hypothesis; the claims the text makes in
passing on 2017 pp. 227–233, 237–238, 241, 247 and 249; the local path connectedness of M-polyfolds and Michael's theorem (Part I's
gaps G.56, first fact, and G.15); the witnesses of §9. **Theorems 7.1.13–7.6.4 (2017: 7.1–7.6) hold** with the readings above. In a changed
form: Theorem 7.1.13 (2017: 7.1) with $U$ connected; Proposition 7.1.15 (2017: 7.5) by transport; Propositions 7.1.10, 7.5.10 (1) (2017: 7.3, 7.14) and Lemma 7.1.11 (2017: 7.1) through the
closedness and the fibres of proper maps; Proposition 7.5.3 (2017: 7.12) with the stronger conclusion that $|X^1|$ is metrizable;
Proposition 7.5.10 (2) (2017: 7.14) from paracompactness alone; Lemma 7.6.5 (2017: 7.10) with the support bound; the remark after Definition 7.1.7 (2017: 7.7) for
functors continuous on morphisms (without that it does not hold as we read it). Not formalized: the properties of $T\varphi$
(gap G.70); the paracompactness of $\mathbf X^R$ when it is Hausdorff (G.71; Hausdorffness itself fails in general, by the
splicing example, checked by machine); the set $|X_\infty|$ (G.72); the density of $X_\infty$ in $X_k$ (G.73); the tangent facts (3), (4) before Proposition 7.1.22 (2017: 7.7) (G.7); the comparison with classical properness
(2017 p. 227) and the open question of 2017 p. 249, without a gap; Remarks 7.5.2 and 7.5.6 (2017: 7.1 and 7.2), which have no formal content; the
computations of §10, done by hand. The machine-checked statements are listed in `Exposition/Verification.md`
(V7.1–V7.68), compared with the text in `Exposition/polyfold-beside-lean.html` and retold in `Exposition/ProofByProof.md`.
The findings are `Exposition/Findings.md`, "Chapter 7", items 1–115 (numbered in blocks; the gaps in the numbering are
unused numbers).
