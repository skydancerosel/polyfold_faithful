# Chapter 8. Bundles and covering functors: the tangent of an ep-groupoid, strong bundles and proper coverings (HWZ Part II, Chapter 8, pp. 357–400 (2017 pp. 257–289))

*Hofer–Wysocki–Zehnder, "Polyfold and Fredholm Theory", Part II, Chapter 8 (arXiv 1707.08941, pp. 257–289),
rewritten for a first-year graduate student who has read Chapter 7 and wants to know how velocities, bundles and
coverings are described for problems with local symmetries. Every formalized statement is proved; what is not
formalized is marked. Where the Lean formalization found a gap or a shorter route, the text follows the Lean. Part II
has no 2014 preprint: its statement numbers and printed pages are those of the book (Springer 2021), with the 2017
text's in parentheses (see `BookConcordance.md`). Results of Part I are cited in the same way, by their 2021
numbers with the 2017 numbers in parentheses; the preprint numbers are in the concordance. Conventions: ep-groupoids, sc-smooth functors, natural
representations, the index lift $X^1$ and paracompact orbit spaces are those of Chapter 7; $TX$ and $T\mathbf X$ are Part
I's tangent M-polyfolds, whose fibres $T_xX$ carry no linear structure in the project (gap G.7), so that no statement
about the linearity of a tangent map is formalized; a "strong bundle map" between strong bundles over M-polyfolds,
which Part I defines only between local models, is read globally (§6). The findings cited are those of `Findings.md`,
"Chapter 8".*

---

## 0. Identical beads in motion: velocities, forces and a marked bead

Chapter 7 began with two identical beads on a wire. In the coordinates $u = (a+b)/2$, $v = (b-a)/2$ the exchange of the
labels is $(u,v)\mapsto(u,-v)$, and the object that keeps the smooth structure of the problem is not the half-plane of
unlabelled positions but the pair "$\mathbb R^2$ with the swap", an ep-groupoid. Now let the beads move. A state of motion
is a position together with a velocity, $(u,v,\dot u,\dot v)$, and exchanging the labels changes both: the swap acts by
$(u,v,\dot u,\dot v)\mapsto(u,-v,\dot u,-\dot v)$, its derivative acting on the velocity. So the states of motion form an
ep-groupoid again, with the tangent vectors as objects and one morphism $(y,\dot y)\to(g\cdot y,g\cdot\dot y)$ for every
$g\in\{1,\text{swap}\}$. It is the *tangent* of the ep-groupoid of Chapter 7, and its orbit space is the space of states
of motion of the unlabelled beads. Over a point of the diagonal, $v = 0$, the velocities $\dot v$ and $-\dot v$ give the
same state: two beads at the same place with velocities $\dot a$, $\dot b$ are the same as with $\dot b$, $\dot a$. The
states of motion over a collision are the unordered pairs of velocities, not a vector space, and the orbit space of the
tangent is not a vector bundle over the orbit space. Upstairs, in the ep-groupoid, the velocities form vector spaces and
the morphisms act on them; this is what §§1–4 build for every ep-groupoid. Theorem 8.1.1 (2017: 8.1) makes the tangent an
ep-groupoid, Theorem 8.1.11 (2017: 8.2) makes the tangent of an sc-smooth functor an sc-smooth functor, and Theorem 8.1.15 (2017: 8.4) passes the
paracompactness of $|X|$ to $|TX|$.

A force acting on the beads is a vector attached to every configuration, and the swap acts on it too: the force at the
configuration $g\cdot y$ is $g$ applied to the force at $y$. A *strong bundle over an ep-groupoid* (Definition 8.3.1 (2017: 8.4)) is a
bundle over the objects together with such a lift of every morphism to a linear isomorphism of the fibres, compatible
with compositions, and the admissible sections, the *section functors* of Definition 8.3.4 (2017: 8.7), are those compatible with the
lifts. For a pair potential between identical particles the force field is one (§11).

Now take three identical particles on a line, the ep-groupoid $S_3\ltimes\mathbb R^3$ of Chapter 7, §10, and mark one of
them, say with a tag that does not change the physics. A state is now a pair $(i,x)$, a configuration $x$ with the
particle $i$ marked, and permutations act on both entries. Forgetting the mark is a functor to $S_3\ltimes\mathbb R^3$
which is three-to-one on objects and is locally the identity: a *proper covering functor* (Definition 8.5.1 (2017: 8.8)). On orbit
spaces it is not a covering: over a configuration with three distinct positions it has three preimages (the marked
particle is the leftmost, the middle or the rightmost one), over a configuration with two coincident particles two, and
over a triple collision one. The structure theory of §§7–9 explains this. The count that stays constant is the count
upstairs, $\#F^{-1}(x) = 3$ (Proposition 8.6.4 (2017: 8.4)), and it splits over the points of the orbit space by the orbit–stabilizer
theorem, which is the last claim of Lemma 8.6.1 (2017: 8.9). §11 works this out, together with the tangent of the two beads.

Chapter 8 develops: the structure maps of the tangent (§1); the tangent ep-groupoid, Theorem 8.1.1 (2017: 8.1) with Lemmas 8.1.2–8.1.9 (2017: 8.1–8.8)
(§2); Remark 8.1.10 (2017: 8.1), the tangent functor, natural transformations and their tangents (§3); the orbit space of the tangent,
Theorem 8.1.15 (2017: 8.4) (§4); sc-differential forms, Definitions 8.2.1 and 8.2.2 (2017: 8.2 and 8.3), which are not formalized (§5); strong bundles over
ep-groupoids, their functorial picture, strong bundle maps and section functors (§6); proper covering functors and their
local structure, Theorem 8.5.3 (2017: 8.5) (§7); covering functors of finite groupoids, geometric lifts and the local model of a
proper covering functor, Proposition 8.5.7 (2017: 8.3) and Theorem 8.5.8 (2017: 8.6) (§8); proper strong bundle covering functors and the appendix,
which counts the points of the fibres (§9). §10 records the examples that show the hypotheses can hold, and §11 is the
application.

The formalization changed the text in these places. Square (5) of Theorem 8.5.3 (2017: 8.5), as printed with the target map $t$ on its
right arrow, does not hold as we read it; checked in Lean on the identity functor of $\mathbb Z/2\ltimes\mathbb R$, it is
formalized with the source map $s$ on both vertical arrows, together with a companion square with $t$ on both (§7).
Proposition 8.5.7 (2017: 8.3) needs the finite groupoid $D$ to be nonempty, which the text does not state; the hypothesis holds where
the proposition is used, in Theorem 8.5.8 (2017: 8.6) (§8). The degeneracy remark after Definition 8.5.1 (2017: 8.8) uses the product formula for
the degeneracy index, which Part I has for tame M-polyfolds; it is proved for tame $X$, $Y$, and in general as an
inequality (§7). Theorem 8.1.15 (2017: 8.4) is proved by metrizability, as Proposition 7.5.3 (2017: 7.12), not by the text's locally finite cover by
closed paracompact sets, and the conclusion is stronger: $|TX|$ is metrizable (§4). Steps the text asserts without proof
are supplied: the tangents of maps defined only on open sets, which the proofs of §8.1 differentiate (§1); "$Tr$ is a
tame retraction" in Lemma 8.1.9 (2017: 8.8), proved from the definitions (§2); that natural equivalence is an equivalence relation
(§3); the open embedding $G_x\backslash TU(x)\to|TX|$ (§4); the ep-groupoid of the functorial picture of a strong bundle and
the equivalence of Definitions 8.3.2 and 8.3.3 (2017: 8.5 and 8.6) (§6); the "one verifies" of Proposition 8.5.7 (2017: 8.3) and of Theorem 8.5.8 (2017: 8.6) (§8). Lemma
8.1.2 (2017: 8.1) is proved in the sheet form its proof uses; the identification of the tangent of the fibred product with the fibred
product of the tangents is not formalized (gap G.75, §2). Definitions 8.2.1 and 8.2.2 (2017: 8.2 and 8.3) are not formalized (gap G.74, §5).
Strong bundle maps between strong bundles over M-polyfolds, which Part I defines only for local models, enter Definition
8.3.1 (2017: 8.4) and everything after it as a reading (§6). Two restrictions come from the formalization and not from the text: the
tangent of an ep-groupoid in `Type u` lives in `Type (max u 1)`, so that the tangent functor is
`EP.{max u 1} ⥤ EP.{max u 1}` (§3), and Theorem 8.5.8 (2017: 8.6) is stated for ep-groupoids whose objects and morphisms are in
`Type` (§8).

## 1. The tangent data (pp. 357–359 (2017 pp. 257–258))

**The structure maps (8.1)–(8.9).** The tangent of the ep-groupoid $(X,\mathbf X)$ is the pair $T(X,\mathbf X) = (TX,T\mathbf X)$
of tangent M-polyfolds (Part I, Definition 2.3.14 (2017: 2.11)) (8.1). A vector $h\in T_\varphi\mathbf X$ over a morphism $\varphi\in\mathbf X_1$ is viewed
as a morphism $(\varphi,h):Ts(\varphi)(h)\to Tt(\varphi)(h)$ (8.2), so that the source and target maps are $s_T = Ts$ and $t_T = Tt$
(8.3). If $Ts(\psi)(k) = Tt(\varphi)(h)$ (8.4), then $s(\psi) = t(\varphi)$, and
$$(\psi,k)\circ(\varphi,h) = \bigl(\psi\circ\varphi,\ Ts(\psi\circ\varphi)^{-1}(Ts(\varphi)(h))\bigr), \qquad (8.5)$$
or, with the projection $p:T\mathbf X\to\mathbf X^1$, $k\circ h = Ts(p(k)\circ p(h))^{-1}\,Ts(p(h))(h)$ (8.6). The unit of $a\in T_xX$ is
$1_a = (1_x,Ts(1_x)^{-1}a)$ (8.7), (8.8), and the inverse is $\iota_T(\varphi,k) = (\varphi^{-1},T\iota(\varphi)(k))$ (8.9).

*How this is read.* $Ts(\psi\circ\varphi)^{-1}$ makes sense because $s$ is a local sc-diffeomorphism: $Ts$ maps every fibre
$T_\varphi\mathbf X$ bijectively onto $T_{s(\varphi)}X$. Two consequences are used throughout the chapter. *Fibre injectivity*: two
vectors of $T\mathbf X$ with the same base point and the same image under $Ts$ are equal. *Fibre surjectivity*: every vector
of $T_{s(\varphi)}X$ is $Ts(h)$ for some $h$ over $\varphi$. So the composite (8.5) is the unique vector over $p(k)\circ p(h)$ whose
image under $Ts$ is $Ts(h)$. In Lean the composition is a total function, defined by choice, with a junk value off
composable pairs, as Chapter 7's composition; on composable pairs it is the text's. The unit map is $u_T = Tu$ and the
inverse map $\iota_T = T\iota$; that $Tu$ is (8.8) is the first computation of Lemma 8.1.5 (2017: 8.4). (8.5) writes $T_{\varphi\circ\psi}\mathbf X$ for
$T_{\psi\circ\varphi}\mathbf X$ (possible misprint). For $X$ in `Type u`, Part I's tangent M-polyfold lives in `Type (max u 1)`, and so
do $TX$, $T\mathbf X$ and later $|TX|$ (Findings, items 1, 2). *Checked by machine (V8.1):* `Polyfold.EpGroupoid.tSrc`,
`Polyfold.EpGroupoid.tTgt`, `Polyfold.EpGroupoid.tUnit`, `Polyfold.EpGroupoid.tInv`, `Polyfold.EpGroupoid.tBase`,
`Polyfold.EpGroupoid.tComp`, `Polyfold.EpGroupoid.tangent_ext`, `Polyfold.EpGroupoid.exists_tSrc_eq`,
`Polyfold.EpGroupoid.tComp_spec`, `Polyfold.EpGroupoid.tComp_eq`, `Polyfold.EpGroupoid.tUnit_eq`.

**Tangents of maps defined on open sets.** The proofs of §8.1 differentiate maps that are defined only on open sets,
such as the inverse $(s|\mathbf U(\psi))^{-1}$ of the source map on a sheet, and use that $Ts:T\mathbf U(\varphi)\to TU(x)$ is an
sc-diffeomorphism. Part I defines the tangent $Tf$ only of a globally sc-smooth $f$. For an open $U\subseteq X$, $TU$ is read as
the open set $p^{-1}(U)\subseteq TX$, which is the tangent of the open sub-M-polyfold $U$. For a map $f$ sc-smooth on $U$ the
tangent $Tf$ on $p^{-1}(U)$ is built from the charts, as Part I builds $Tf$; it lies over $f$, satisfies the chain rule, is
sc-smooth, and equals Part I's tangent when $f$ is globally sc-smooth. The tangent of an sc-diffeomorphism between open
sets is an sc-diffeomorphism between their tangents, and the tangent of a local sc-diffeomorphism is a local
sc-diffeomorphism, bijective on every fibre and surjective if the map is; this is the "by construction" of Lemma 8.1.7 (2017: 8.6).
Off $p^{-1}(U)$ the tangent takes a junk value, which exists because a nonempty M-polyfold has points on level $1$; the
text needs none of this (Findings, item 3). *Checked by machine (V8.2):* `Polyfold.MPolyfold.tangentPreimage`,
`Polyfold.MPolyfold.isOpen_tangentPreimage`, `Polyfold.MPolyfold.tangentMapOn`, `Polyfold.MPolyfold.tangentMapOn_comp`,
`Polyfold.MPolyfold.tangentMapOn_eq_tangentMap`, `Polyfold.MPolyfold.tangentMapOn_isScSmoothOn`,
`Polyfold.MPolyfold.IsScDiffeoOn.tangent`, `Polyfold.MPolyfold.IsLocalScDiffeo.tangentMap`,
`Polyfold.MPolyfold.IsLocalScDiffeo.bijOn_tangentFiber`, `Polyfold.MPolyfold.IsLocalScDiffeo.surjective_tangentMap`,
`Polyfold.MPolyfold.isScDiffeoOn_tangentMap_subtypeVal`, `Polyfold.MPolyfold.nonempty_tangentSpace`.

## 2. The tangent ep-groupoid (pp. 358–365 (2017 pp. 258–264))

**Theorem 8.1.1 (2017: 8.1) (the tangent ep-groupoid).** $T(X,\mathbf X) = (TX,T\mathbf X)$ with the structure maps (8.3)–(8.9) is an ep-groupoid.
If $(X,\mathbf X)$ is tame, so is $T(X,\mathbf X)$. The projections $p:TX\to X^1$ and $p:T\mathbf X\to\mathbf X^1$ form an sc-smooth functor
$(p,p):T(X,\mathbf X)\to(X,\mathbf X)^1$.

The proof is Lemmas 8.1.2–8.1.9 (2017: 8.1–8.8): the groupoid laws are Lemmas 8.1.3–8.1.6 (2017: 8.2–8.5), the conditions of Definition 7.1.3 (2017: 7.3) are Lemmas 8.1.7 and
8.1.8 (2017: 8.6 and
8.7), and tameness is Lemma 8.1.9 (2017: 8.8). Where the text differentiates identities between maps of $\mathbf X$, the formalization uses
fibre injectivity: the base points are computed in $\mathbf X$, and the values of $Ts$ by Part I's chain rule applied to
$s\circ u = \mathrm{id}$, $s\circ\iota = t$, and the like. The one differentiation that remains is the target in Lemma 8.1.3 (2017: 8.2). The
statements are the text's (Findings, item 4).

**Lemma 8.1.2 (2017: 8.1).** Identifying $T(\mathbf X\,{}_s{\times}_t\,\mathbf X)$ with $T\mathbf X\,{}_{Ts}{\times}_{Tt}\,T\mathbf X$, the composition of $T\mathbf X$ is the tangent
of the multiplication: $(\psi,k)\circ(\varphi,h) = Tm(\psi,\varphi)(k,h)$, where $k = Ts(\psi)^{-1}(Tt(\varphi)(h))$.

*How this is read.* The identification of the tangent of the fibred product with the fibred product of the tangents is
not formalized (gap G.75). The lemma is proved in the form its proof uses. The proof varies $\varphi'$ near $\varphi$ and
puts $\psi' = F(\varphi') = (s|\mathbf U(\psi))^{-1}(t(\varphi'))$, which makes $m(\psi',\varphi')$ a function of $\varphi'$ alone. Let $s:W\to V$
be a sheet of $s$ around $\psi$, with inverse $\sigma$, and $g(\varphi') = m(\sigma(t(\varphi')),\varphi')$ on the open set $t^{-1}(V)$; $g$ is
sc-smooth by Chapter 7's sheet form of Definition 7.1.3 (4) (2017: 7.3).

*Proof.* Let $k$ over $\psi\in W$ and $h$ over $\varphi$ be composable, $Ts(k) = Tt(h)$. The vector $T\sigma(Tt(h))$ lies over
$\sigma(t(\varphi)) = \psi$, and $Ts(T\sigma(Tt(h))) = Tt(h) = Ts(k)$; so $k = T\sigma(Tt(h))$ by fibre injectivity. The vector $Tg(h)$ lies
over $g(\varphi) = \psi\circ\varphi$, and $Ts(Tg(h)) = Ts(h)$ because $s\circ g = s$ on $t^{-1}(V)$. So $Tg(h)$ is the composite (8.5):
$k\circ h = Tg(h)$. $\square$

The proof writes $s|\mathbf U(\varphi\circ\psi)$ for $s|\mathbf U(\psi\circ\varphi)$ (possible misprint) (Findings, items 5, 111). *Checked by
machine (V8.4):* `Polyfold.EpGroupoid.lemma_8_1`, `Polyfold.EpGroupoid.tComp_eq_tangentMapOn`,
`Polyfold.EpGroupoid.tangentMapOn_srcInv_tSrc`, `Polyfold.EpGroupoid.mem_tangentPreimage_tgt`,
`Polyfold.EpGroupoid.isScSmoothCompSheet`.

**Lemma 8.1.3 (2017: 8.2).** $s_T(\Psi\circ\Phi) = s_T(\Phi)$ and $t_T(\Psi\circ\Phi) = t_T(\Psi)$.

*Proof.* The first equality is (8.5). For the second, with the sheet and the map $g$ of Lemma 8.1.2 (2017: 8.1), $t\circ g = t\circ\sigma\circ t$ on
$t^{-1}(V)$, since $t(m(\sigma(t\varphi'),\varphi')) = t(\sigma(t\varphi'))$. By the chain rule, $Tt(k\circ h) = T(t\circ g)(h) = Tt(T\sigma(Tt(h))) = Tt(k)$.
$\square$

This is the text's computation, whose $\alpha\circ s = t\circ(s|\mathbf U(\psi))^{-1}\circ t$ near $\varphi$ is $t\circ g$ here. The proof has "$= =$",
"$:\mathbf U(\psi\circ\varphi)\to U(x)$" without the map $s$, and "$Tt)\varphi)(h)$" (possible misprints) (Findings, item 6). *Checked by
machine (V8.5):* `Polyfold.EpGroupoid.lemma_8_2`, `Polyfold.EpGroupoid.tTgt_tangentMapOn`.

**Lemma 8.1.4 (2017: 8.3).** The composition of $T\mathbf X$ is associative.

*Proof.* For composable $l$, $k$, $h$ over $\sigma$, $\psi$, $\varphi$, Lemma 8.1.3 (2017: 8.2) makes both $l\circ(k\circ h)$ and $(l\circ k)\circ h$ defined. Both lie
over $\sigma\circ\psi\circ\varphi$, and by (8.5) both have the image $Ts(h)$ under $Ts$. By fibre injectivity they are equal. $\square$

The text expands both sides with (8.5) (Findings, item 4). *Checked by machine (V8.6):* `Polyfold.EpGroupoid.lemma_8_3`.

**Lemma 8.1.5 (2017: 8.4).** For $q\in T_xX$, $1_q = (1_x,Ts(1_x)^{-1}q)$ is a morphism $q\to q$ and a two-sided unit.

*Proof.* $1_q = Tu(q)$: the vector $Tu(q)$ lies over $u(x) = 1_x$, and $Ts(Tu(q)) = T(s\circ u)(q) = q$. Likewise $Tt(Tu(q)) = T(t\circ u)(q) = q$,
so $1_q:q\to q$. If $k$ over $\varphi$ has $Ts(k) = q$, then $k\circ1_q$ lies over $\varphi\circ1_x = \varphi$ and $Ts(k\circ1_q) = Ts(1_q) = q = Ts(k)$,
so $k\circ1_q = k$. If $Tt(k) = q$, then $1_q\circ k$ lies over $\varphi$ and $Ts(1_q\circ k) = Ts(k)$, so $1_q\circ k = k$. $\square$

The text obtains $Tt(1_q) = q$ from $t\circ(s|\mathbf U(1_x))^{-1} = \mathrm{id}$ near $x$; the chain rule for $t\circ u = \mathrm{id}$ gives it directly
(Findings, item 6). *Checked by machine (V8.7):* `Polyfold.EpGroupoid.tSrc_tUnit`, `Polyfold.EpGroupoid.tTgt_tUnit`,
`Polyfold.EpGroupoid.tComp_tUnit`, `Polyfold.EpGroupoid.tUnit_tComp`, `Polyfold.EpGroupoid.lemma_8_4`.

**Lemma 8.1.6 (2017: 8.5).** $\iota_T(\varphi,k) = (\varphi^{-1},T\iota(\varphi)(k))$ is a two-sided inverse of $(\varphi,k)$.

*Proof.* From $s\circ\iota = t$ and $t\circ\iota = s$, $Ts(T\iota(k)) = Tt(k)$ and $Tt(T\iota(k)) = Ts(k)$, so $T\iota(k)$ is a morphism
$Tt(k)\to Ts(k)$. The composite $T\iota(k)\circ k$ lies over $\varphi^{-1}\circ\varphi = 1_x$ and its image under $Ts$ is $Ts(k)$; so do those of
$1_{Ts(k)}$ (Lemma 8.1.5 (2017: 8.4)), and the two are equal. The other side is the same. $\square$

*Checked by machine (V8.8):* `Polyfold.EpGroupoid.tSrc_tInv`, `Polyfold.EpGroupoid.tTgt_tInv`,
`Polyfold.EpGroupoid.tComp_tInv`, `Polyfold.EpGroupoid.tInv_tComp`, `Polyfold.EpGroupoid.lemma_8_5`.

**Lemma 8.1.7 (2017: 8.6).** $s_T$ and $t_T$ are surjective local sc-diffeomorphisms, and all structure maps of $(TX,T\mathbf X)$ are
sc-smooth.

*Proof.* $s_T = Ts$ and $t_T = Tt$ are tangents of surjective local sc-diffeomorphisms (§1). $u_T = Tu$ and $\iota_T = T\iota$ are
tangents of sc-smooth maps. For the multiplication, Chapter 7's sheet form of Definition 7.1.3 (4) (2017: 7.3) is proved. A sheet of
$s_T$ around a vector over $\psi$ is $p^{-1}(W)$ for a sheet $W$ of $s$ around $\psi$, with inverse $T\sigma$, and on its domain the map
$\Psi\mapsto T\sigma(t_T\Psi)\circ\Psi$ is $Tg$ by Lemma 8.1.2 (2017: 8.1), sc-smooth by §1. By Chapter 7's equivalence of the sheet form with
condition (4), the multiplication is sc-smooth on $T\mathbf X\,{}_{s_T}{\times}_{t_T}\,T\mathbf X$. $\square$

The text adds that "$m_{T\mathbf X}$ is precisely $Tm$", which uses the identification of Lemma 8.1.2 (2017: 8.1) (gap G.75); the proof above
avoids it (Findings, item 7). *Checked by machine (V8.9):* `Polyfold.EpGroupoid.isLocalScDiffeo_tSrc`,
`Polyfold.EpGroupoid.isLocalScDiffeo_tTgt`, `Polyfold.EpGroupoid.surjective_tSrc`, `Polyfold.EpGroupoid.surjective_tTgt`,
`Polyfold.EpGroupoid.isScSmoothMap_tUnit`, `Polyfold.EpGroupoid.isScSmoothMap_tInv`,
`Polyfold.EpGroupoid.isScSmoothCompSheet_tangent`, `Polyfold.EpGroupoid.isScSmoothComp_tangent`,
`Polyfold.EpGroupoid.lemma_8_6`, `Polyfold.isScSmoothComp_iff_sheet`.

**Lemma 8.1.8 (2017: 8.7).** $(TX,T\mathbf X)$ has the properness property: every $a\in TX$ has an open neighbourhood $V'$ for which
$t_T:s_T^{-1}(\mathrm{cl}\,V')\to TX$ is proper.

*Proof.* Let $x = p(a)\in X_1$, let $V$ be an open neighbourhood of $x$ in $X$ with $t:s^{-1}(\mathrm{cl}_XV)\to X$ proper (Definition 7.1.3
(3) (2017: 7.3)), and put $V' = p^{-1}(V)$. $TX$ and $T\mathbf X$ are metrizable, so properness is Chapter 7's sequential criterion. Let
$(\varphi_k,h_k)$ be vectors with $s_T(\varphi_k,h_k)\in\mathrm{cl}\,V'$ and $t_T(\varphi_k,h_k)\to b$. Then $s(\varphi_k)\in\mathrm{cl}_XV$ and $t(\varphi_k)\to p(b)$, so by
the properness of $X$ a subsequence of $(\varphi_k)$ converges in $\mathbf X$, to some $\varphi$. Let $\mathbf U(\varphi)$ be a sheet of $t$ at $\varphi$. For large
$k$, $\varphi_k\in\mathbf U(\varphi)$, and on $p^{-1}(\mathbf U(\varphi))$ the inverse of $Tt$ is continuous (§1); so $(\varphi_k,h_k) = (Tt|p^{-1}\mathbf U(\varphi))^{-1}(t_T(\varphi_k,h_k))$
converges. $\square$

The text's step "$\varphi_k\to\varphi$ in $\mathbf X^1$" is not needed. The proof writes $t(\varphi_k,h_k) = Ts(\varphi_k)(h_k)$ for $Tt(\varphi_k)(h_k)$
(possible misprint), and accordingly inverts $Ts$ where the formal proof inverts $Tt$, the map whose values converge
(Findings, item 7). *Checked by machine (V8.10):* `Polyfold.EpGroupoid.lemma_8_7`.

**Lemma 8.1.9 (2017: 8.8).** If the ep-groupoid $(X,\mathbf X)$ is tame, so is $(TX,T\mathbf X)$.

The text's proof: if $\phi:U\to O$ is a tame chart of the object M-polyfold onto a tame retract $O = r(U)\subseteq C$, then $Tr$ is a
tame retraction, so $(TX,T\mathbf X)$ has a tame object space and is tame by definition. "$Tr$ is a tame retraction" is asserted
without argument, and Part I does not state it.

*Proof that $Tr$ is tame.* By Part I's Definition 2.5.2 (2017: 2.17), a retraction $r$ onto $O$ in a partial quadrant $C\subseteq E$ is tame if (1)
$d_C(r(a)) = d_C(a)$, and (2) at every smooth point $a\in O$ the tangent space $T_aO = Dr(a)E$ has an sc-complement inside the
subspace $E_a$ that $C$ determines at $a$. Present $TC = C^1\oplus E$ so that its $\mathbb R^n$-coordinates at $(a,b)$ are those of $a$.
Then $d_{TC}(a,b) = d_C(a)$ and $Tr(a,b) = (r(a),Dr(a)b)$, so (1) for $Tr$ is (1) for $r$. For (2) at a smooth point $(a,b)$, let
$A\subseteq E_a$ be the sc-complement of $T_aO$ given by the tameness of $r$, and $A' = (A\cap E_1)\oplus A$. With $L = D(Tr)(a,b)$ three facts
suffice: $L$ is a projection, since $Tr\circ Tr = Tr$; the first row of $L$ is $(Dr(a),0)$, from $\mathrm{pr}_1\circ Tr = r\circ\mathrm{pr}_1$; and
$L(0,l) = (0,Dr(a)l)$, from the affine map $w\mapsto Tr(a,w)$. If $(k,l)\in L(TE)\cap A'$, then $L(k,l) = (k,l)$, so $k = Dr(a)k\in T_aO\cap A = 0$,
and then $l = Dr(a)l\in T_aO\cap A = 0$. For the sum, split $k = c_1+\alpha$ with $c_1\in T_aO$, $\alpha\in A$, on the level of $k$, then
$l-(L(c_1,0))_2 = c_2+\beta$ with $c_2\in T_aO$, $\beta\in A$; then $(k,l) = L(c_1,0)+L(0,c_2)+(\alpha,\beta)$. The same holds on every level. The
second derivative of $r$, which enters $L$, is not needed. Tameness for every presentation of $TC$ follows from this one
presentation by Part I's Lemma 1.3.4 (2017: 1.1), the independence of the degeneracy index of the presentation. $\square$

From tame charts of $X$ the tangent charts of $TX$, modelled on $T(O,C,E)$, form an equivalent tame atlas; the text's "tame
chart" is read as a chart modelled on a tame retract (Findings, item 8). *Checked by machine (V8.11):*
`Polyfold.ScIso.tangentPres`, `Polyfold.degIndex_tangentSet`, `Polyfold.ScRetraction.scDeriv_tangentRetraction_fst`,
`Polyfold.ScRetraction.scDeriv_tangentRetraction_inr`, `Polyfold.ScRetraction.IsTameWith.tangent`,
`Polyfold.ScRetraction.IsTame.tangentRetraction`, `Polyfold.IsTameRetract.tangent`, `Polyfold.MPolyfold.IsTame.tangent`,
`Polyfold.EpGroupoid.lemma_8_8`.

**Proof of Theorem 8.1.1 (2017: 8.1)** *(pp. 363–365 (2017 pp. 263–264)).* Lemmas 8.1.3–8.1.6 (2017: 8.2–8.5) make $(TX,T\mathbf X)$ a groupoid, Lemmas 8.1.7 and 8.1.8 (2017: 8.6 and 8.7) give conditions
(1)–(4) of Definition 7.1.3 (2017: 7.3), and Lemma 8.1.9 (2017: 8.8) gives the tameness. The projection $p$ is sc-smooth into the index lift
$(X,\mathbf X)^1$ of Proposition 7.3.9 (2017: 7.11), and it is compatible with the composition, $p(k\circ h) = p(k)\circ p(h)$ by (8.5), which the text
calls obvious. $\square$

`Polyfold.EpGroupoid.theorem_8_1` records that the ep-groupoid has the M-polyfolds $TX$, $T\mathbf X$ and the text's structure
maps, with the base point and the source of a composite; the tameness sentence is a separate statement (Findings, items
2, 9). *Checked by machine (V8.3):* `Polyfold.EpGroupoid.tangentGroupoidStr`, `Polyfold.EpGroupoid.tangentEpGroupoid`,
`Polyfold.EpGroupoid.tangentProjFunctor`, `Polyfold.EpGroupoid.tBase_tComp`, `Polyfold.EpGroupoid.theorem_8_1`,
`Polyfold.EpGroupoid.theorem_8_1_tame`.

## 3. Remark 8.1.10 (2017: 8.1), the tangent functor and natural transformations (pp. 364–372 (2017 pp. 264–268))

**Remark 8.1.10 (2017: 8.1) (the morphisms of $T\mathbf X$ as pairs).** A morphism $\varphi:x\to y$ in $\mathbf X_1$ has "a well-defined associated linear
isomorphism" $T\varphi$, the tangent of $t\circ(s|\mathbf U(\varphi))^{-1}$ at $x$, and $t_T\circ(s_T|T_\varphi\mathbf X)^{-1} = T\varphi$. The morphisms of $T\mathbf X$ may be
viewed as the pairs $(T\varphi,a)$, $a\in T_{s(\varphi)}X$, composed by $(T\psi,h)\circ(T\varphi,l) = (T(\psi\circ\varphi),l)$, through the map
$G(\varphi,h) = (T\varphi,Ts(h))$, a bijection compatible with the compositions; the right side can be given the M-polyfold
structure that makes $G$ an sc-diffeomorphism, or described by the triples $(a,T\varphi,b)$, $b = T\varphi(a)$.

*How this is read.* $T\varphi$ is Chapter 7's tangent of a morphism (Definition 7.1.4 (2017: 7.4)), $Tt\circ(Ts|T_\varphi\mathbf X)^{-1}$. It is well
defined, with $T\varphi(Ts(h)) = Tt(h)$ for every $h$ over $\varphi$, and it is functorial, $T(\psi\circ\varphi) = T\psi\circ T\varphi$: for $a = Ts(h)$ and $k$ with
$Ts(k) = Tt(h)$, the composite $k\circ h$ lies over $\psi\circ\varphi$ with $Ts(k\circ h) = a$, so $T(\psi\circ\varphi)(a) = Tt(k\circ h) = Tt(k) = T\psi(T\varphi(a))$ by
Lemma 8.1.3 (2017: 8.2). In $G(\varphi,h) = (T\varphi,Ts(h))$ the first entry is read as $T\varphi$ labelled by $\varphi$: as a bare map $G$ need not be
injective, since distinct morphisms can have the same tangent; for $\mathbb Z/3$ acting trivially on $\mathbb R$ (Chapter 7, §9) the
three morphisms at a point all have $T\varphi = \mathrm{id}$ (an example not formalized). With the label, $G$ is a bijection onto the
pairs $(\varphi,a)$ with $\varphi\in\mathbf X_1$ and $a\in T_{s(\varphi)}X$, compatible with the compositions. Not formalized: that $T\varphi$ is a linear
isomorphism, which needs a linear structure on $T_xX$ (gap G.7), and that it is the tangent of $\hat\varphi = t\circ(s|\mathbf U(\varphi))^{-1}$ at
$x$ (gap G.70, which the well-definedness and functoriality above now close in part); and, without a gap since nothing
uses them, the M-polyfold structure transported along $G$ and the triples $(a,T\varphi,b)$. Possible misprints: "$T\varphi:T_xX\to T_yY$"
for $T_yX$, twice on 2017 p. 264, and "the linearization of $t\circ(s|U(\varphi))^{-1}$ at $\varphi$" on 2017 p. 265 for "at $x$", the point where this
map is defined and where 2017 p. 264 takes its tangent (Findings, items 10, 112, 113). *Checked by machine (V8.12):*
`Polyfold.EpGroupoid.tangentMor`, `Polyfold.EpGroupoid.tangentMor_tSrc`, `Polyfold.EpGroupoid.tangentMor_comp`,
`Polyfold.EpGroupoid.remarkG`, `Polyfold.EpGroupoid.remark_8_1`.

**Theorem 8.1.11 (2017: 8.2).** If $(\Phi,\boldsymbol\Phi):(X,\mathbf X)\to(Y,\mathbf Y)$ is an sc-smooth functor between ep-groupoids, its tangent
$(T\Phi,T\boldsymbol\Phi):T(X,\mathbf X)\to T(Y,\mathbf Y)$ is an sc-smooth functor.

*Proof.* Tangents of sc-smooth maps are sc-smooth. From $s\circ\boldsymbol\Phi = \Phi\circ s$ and $t\circ\boldsymbol\Phi = \Phi\circ t$, $T\boldsymbol\Phi$ maps a morphism
$h:Ts(h)\to Tt(h)$ of $T\mathbf X$ to a morphism $T\Phi(Ts(h))\to T\Phi(Tt(h))$ of $T\mathbf Y$. For composable $k$, $h$, both $T\boldsymbol\Phi(k\circ h)$ and
$T\boldsymbol\Phi(k)\circ T\boldsymbol\Phi(h)$ lie over $\boldsymbol\Phi(p(k)\circ p(h))$, and both have the image $T\Phi(Ts(h))$ under $Ts$; they are equal by fibre
injectivity in $T\mathbf Y$. Units: $T\boldsymbol\Phi(Tu(q)) = T(\boldsymbol\Phi\circ u)(q) = T(u\circ\Phi)(q) = Tu(T\Phi(q))$. $\square$

The text differentiates $\boldsymbol\Phi(m(\psi,\varphi)) = m(\boldsymbol\Phi(\psi),\boldsymbol\Phi(\varphi))$ through Lemma 8.1.2 (2017: 8.1) and leaves the units to the reader; both are
proved here (Findings, items 4, 11). *Checked by machine (V8.13):* `Polyfold.EpFunctor.tangent`,
`Polyfold.EpFunctor.theorem_8_2`.

**Theorem 8.1.12 (2017: 8.3) (functoriality of $T$).** $T$ is a functor $\mathcal{EP}\to\mathcal{EP}$, $X\mapsto TX$, $\Phi\mapsto T\Phi$, and $TX$ is tame if $X$
is.

*Proof.* Theorems 8.1.1 and 8.1.11 (2017: 8.1 and 8.2), with Part I's chain rule $T(\Psi\circ\Phi) = T\Psi\circ T\Phi$ and $T\mathrm{id} = \mathrm{id}$; tameness is Lemma 8.1.9 (2017: 8.8).
$\square$

*How this is read.* The tangent of an ep-groupoid in `Type u` lives in `Type (max u 1)`, so the functor is formalized as
an endofunctor `EP.{max u 1} ⥤ EP.{max u 1}` of the category of ep-groupoids in the universe `max u 1` (Lean identifies
`max (max u 1) 1` with `max u 1`); an ep-groupoid in `Type` has its tangent ep-groupoid by Theorem 8.1.1 (2017: 8.1), in `Type 1`. This
restriction comes from the formalization, not from the text (Findings, items 2, 11). *Checked by machine (V8.14):*
`Polyfold.EP.tangent`, `Polyfold.tangentFunctor`, `Polyfold.theorem_8_3`, `Polyfold.theorem_8_3_tame`.

**Definition 8.1.13 (2017: 8.1) (natural transformation, natural equivalence).** For sc-smooth functors $F,G:X\to Y$ between
ep-groupoids, a natural transformation $\tau:F\to G$ is an sc-smooth map $\tau:X\to\mathbf Y$ with $\tau(x):F(x)\to G(x)$ and
$\tau(x')\circ F(h) = G(h)\circ\tau(x)$ for every morphism $h:x\to x'$; $F$ is naturally equivalent to $G$, $F\simeq G$, if one exists.

The definition is read literally (Findings, item 12). *Checked by machine (V8.15):* `Polyfold.EpNatTrans`,
`Polyfold.EpFunctor.NaturallyEquivalent`.

**$\simeq$ is an equivalence relation** *(2017 p. 267, stated without proof).* Reflexivity: $x\mapsto1_{F(x)}$. Symmetry: $x\mapsto\tau(x)^{-1}$,
sc-smooth since $\iota$ is. Transitivity: $x\mapsto\tau'(x)\circ\tau(x)$; its sc-smoothness is the one point that is not groupoid
algebra. Near $x_0$ take a sheet $W\ni\tau'(x_0)$ of $s$ with inverse $\sigma$. For $x$ near $x_0$, $\tau'(x)\in W$ and
$\tau'(x) = \sigma(s(\tau'(x))) = \sigma(G(x)) = \sigma(t(\tau(x)))$, so $\tau'(x)\circ\tau(x) = m(\sigma(t\psi),\psi)$ at $\psi = \tau(x)$: an sc-smooth function of $\psi$ by the
sheet form of Definition 7.1.3 (4) (2017: 7.3), composed with the sc-smooth $\tau$. Whiskering, not in the text, is added (Findings, item
12). *Checked by machine (V8.16):* `Polyfold.EpNatTrans.refl`, `Polyfold.EpNatTrans.symm`, `Polyfold.EpNatTrans.trans`,
`Polyfold.EpNatTrans.isScSmoothMap_comp_app`, `Polyfold.EpFunctor.naturallyEquivalent_equivalence`,
`Polyfold.EpNatTrans.whiskerLeft`, `Polyfold.EpNatTrans.whiskerRight`.

**Proposition 8.1.14 (2017: 8.1).** If $\tau:\Phi\to\Psi$ is a natural transformation between sc-smooth functors $\Phi,\Psi:X\to Y$, then
$T\tau:TX\to T\mathbf Y$ is a natural transformation $T\Phi\to T\Psi$. In particular $\Phi\simeq\Psi$ implies $T\Phi\simeq T\Psi$.

*Proof.* $T\tau$ is sc-smooth. From $s\circ\tau = \Phi$ and $t\circ\tau = \Psi$, $T\tau(a)$ is a morphism $T\Phi(a)\to T\Psi(a)$. Let $h$ be a morphism of
$TX$ over $\alpha$. Both sides of the naturality square, $T\tau(t_Th)\circ T\boldsymbol\Phi(h)$ and $T\boldsymbol\Psi(h)\circ T\tau(s_Th)$, lie over
$\tau(t\alpha)\circ\boldsymbol\Phi(\alpha) = \boldsymbol\Psi(\alpha)\circ\tau(s\alpha)$, and both have the image $T\Phi(Ts(h))$ under $Ts$; by fibre injectivity they are
equal. $\square$

The text differentiates the naturality square at $\alpha_0\in\mathbf X^1$. Possible misprints: "$T\tau(x_0(h))$" for $T\tau(x_0)(h)$ (2017 p. 267), and the lower arrow of the last diagram labelled $T\tau(x_0)h$ for $T\tau(x_0')h'$ (2017 p. 268; possibly an artefact of the
text extraction) (Findings, items 4, 13). *Checked by machine (V8.17):* `Polyfold.EpNatTrans.tangent`,
`Polyfold.proposition_8_1`.

## 4. The orbit space of the tangent (2017 p. 268)

**Theorem 8.1.15 (2017: 8.4).** If the ep-groupoid $X$ has paracompact orbit space $|X|$, then the tangent ep-groupoid $TX$ has
paracompact orbit space $|TX|$.

The text's proof: $|X^1|$ is paracompact (Proposition 7.5.3 (2017: 7.12)). For $z\in|X^1|$ take a representative $x_z\in X_1$ and a
neighbourhood $U(x_z)$ with the natural $G_{x_z}$-action such that $TU(x_z)$, as a bundle over $U(x_z)^1$, is sc-isomorphic to
a local bundle model $TO\to O^1$ with an sc-smooth bundle action of $G_{x_z}$; then $|TU(x_z)|$ and $|U(x_z)^1|$ are metrizable. A
locally finite closed refinement $(A_z)$ of the cover $(|U(x_z)^1|)$ of $|X^1|$ gives closed paracompact sets $\tilde A_z\subseteq|TX|$ that
cover $|TX|$ locally finitely, and $|TX|$, being regular and Hausdorff, is paracompact by Michael's theorem (Part I,
Proposition 2.7.4 (2017: 2.17)).

*Proof (as formalized).* The route is that of Proposition 7.5.3 (2017: 7.12). The projection functor $(p,p)$ of Theorem 8.1.1 (2017: 8.1) induces a
continuous map $|p|:|TX|\to|X^1|$. By Proposition 7.5.3 (2017: 7.12), $|X^1|$ is metrizable, hence paracompact and Hausdorff. Every point of
$|X^1|$ has the open neighbourhood $|U(x)_1| = \pi(U(x)\cap X_1)$, for a natural representation $U(x)$ at a representative $x\in X_1$,
and its preimage under $|p|$ is $|TU(x)| = \pi(TU(x))$, with $TU(x) = p^{-1}(U(x))$; this uses fibre surjectivity, by which a
vector over a point isomorphic to a point of $U(x)_1$ is isomorphic to a vector over $U(x)_1$. The group $G_x$ acts on $TU(x)$
by the tangents $T\Phi(g)$ of the natural action, and $G_x\backslash TU(x)\to|TX|$ is an open embedding onto $|TU(x)|$: the fibres of
$\pi$ on $TU(x)$ are the orbits, because a morphism $k:v\to w$ of $TX$ between vectors over $U(x)$ lies over a morphism
$p(k) = \Gamma(g,s(p(k)))$ (Theorem 7.1.13 (3) (2017: 7.1)), and then $k = T\Gamma(g)(v)$ by fibre injectivity. $TU(x)$ is metrizable as a subspace
of $TX$ (Part I, Proposition 2.3.15 (3) (2017: 2.5)), and $G_x\backslash TU(x)$ by the metric $\hat\rho$ of Lemma 7.3.2 (2017: 7.4). The pull-back form of
Smirnov's theorem used for Proposition 7.5.3 (2017: 7.12) (a space with a continuous map to a paracompact Hausdorff space, under which
every point has an open neighbourhood with metrizable preimage, is metrizable) makes $|TX|$ metrizable, hence
paracompact. $\square$

The conclusion is stronger than the text's: $|TX|$ is metrizable. The step shared with the text is the metrizability of
$|TU(x_z)|$; the regularity of $|TX|$, Michael's theorem and the local bundle model $TO\to O^1$ are not used. The open
embedding $G_x\backslash TU(x)\to|TX|$, the argument of Proposition 7.1.19 (2017: 7.6) for $TX$, is left implicit in the text. The linearity of the
action of $G_x$ on the fibres is not formalized (gap G.7). The metric $\hat\rho$ is set up again in `TangentOrbit.lean` for a
finite group acting by homeomorphisms on a metrizable space, since Chapter 7's versions are private. The statement
writes "parcompact" (possible misprint) (Findings, items 20, 21, 113). *Checked by machine (V8.18):*
`Polyfold.EpGroupoid.tangentOrbitProj`, `Polyfold.EpGroupoid.continuous_tangentOrbitProj`,
`Polyfold.EpGroupoid.NaturalRep.tangentU`, `Polyfold.EpGroupoid.NaturalRep.tΦ`,
`Polyfold.EpGroupoid.NaturalRep.tangentMulAction`, `Polyfold.EpGroupoid.NaturalRep.tΓ`,
`Polyfold.EpGroupoid.NaturalRep.tangent_π_eq_iff`, `Polyfold.EpGroupoid.NaturalRep.isOpenEmbedding_tangentOrbitQuotientMap`,
`Polyfold.EpGroupoid.NaturalRep.image_tangentU_eq_preimage`, `Polyfold.EpGroupoid.NaturalRep.metrizableSpace_image_tangentU`,
`Polyfold.EpGroupoid.metrizableSpace_tangent_orbitSpace`, `Polyfold.EpGroupoid.theorem_8_4`,
`Polyfold.metrizableSpace_of_pullback`.

## 5. Sc-differential forms on ep-groupoids (pp. 368–375 (2017 pp. 268–270))

**Definition 8.2.1 (2017: 8.2).** An sc-differential $k$-form on the ep-groupoid $(X,\mathbf X)$ is an sc-smooth map $\omega:\oplus^kTX\to\mathbb R$ on the
Whitney sum of the tangent of the object M-polyfold, linear in each argument and skew-symmetric, with $(T\varphi)^*\omega_y = \omega_x$
for every morphism $\varphi:x\to y$ in $\mathbf X_1$. $\Omega^k_{ep}(X)$ is the vector space of these forms. A form on $X^i$ is a form on $X^{i+1}$,
and $\Omega^*_{ep,\infty}(X) = \bigl(\bigoplus_i\Omega^*_{ep}(X^i)\bigr)/D$ is the direct limit. The exterior derivative $d[\omega] = [d\omega]$ is
compatible with morphisms: for $f = t\circ(s|\mathbf U(\varphi_0))^{-1}$ near $s(\varphi_0)$, $T\varphi = Tf(x)$, so $f^*\omega = \omega$ and $f^*d\omega = df^*\omega = d\omega$; and
$d\circ d = 0$.

**Definition 8.2.2 (2017: 8.3).** $(\Omega^*_{ep,\infty}(X),d)$ is the sc-de Rham complex of $X$.

*Not formalized* (gap G.74). The two definitions need the Whitney sums $\oplus^kTX$ as M-polyfolds, the linear structure of
the fibres $T_xX$ (gap G.7), linear tangent maps $T\varphi$ (gap G.70), the levels $X^i$ for $i\ge2$ (gap G.6), and the
sc-differential forms, the Lie bracket and the exterior derivative of Part I's §4.4, none of which is formalized either
(gaps G.37–G.39). Nothing else in the chapter uses them. Possible misprints: Definition 8.2.1 (2017: 8.2) writes "$T\varphi:T_xX\to T_yY$" for
$T_yX$ (2017 p. 269), as Remark 8.1.10 (2017: 8.1) does; and in the argument that $d\omega$ is compatible with morphisms (2017 p. 269), "$x = s(\varphi)\in U(x_0)\cap X_1$
and $y = t(\varphi_0)$" has $t(\varphi_0)$ for $t(\varphi)$, the target of the morphism whose tangent follows (Findings, items 110, 114).

## 6. Strong bundles over ep-groupoids (pp. 373–384 (2017 pp. 270–275))

The strong bundles over M-polyfolds are Part I's (§2.6 (2017 §2.5)). A strong bundle $P:W\to X$ has Banach spaces as fibres
$W_x = P^{-1}(x)$ and a double filtration $W_{m,k}$, $0\le k\le m+1$; the M-polyfold $W[0]$ has the levels $W_{m,m}$, and $W[1]$ the
levels $W_{m,m+1}$.

**Strong bundle maps and the pull-back along $s$** *(2017 p. 270).* Definition 8.3.1 (2017: 8.4) asks for "a strong bundle map
$\mu:\mathbf X\,{}_s{\times}_P\,W\to W$ covering the target map". Part I defines strong bundle maps only between local models
(Definition 2.6.1 (2017: 2.22)) and treats the transition maps of a strong bundle atlas in Definition 2.6.4 (2017: 2.25); §8.3 uses the global notion
without defining it. It is read as follows. For strong bundles $P:Y\to X$, $P':Y'\to X'$ and a map $f:X\to X'$, a strong bundle map
$\Phi:Y\to Y'$ covering $f$ satisfies (i) $P'\circ\Phi = f\circ P$; (ii) $\Phi$ is linear on the fibres; (iii) $\Phi:Y[0]\to Y'[0]$ is sc-smooth; (iv)
$\Phi(Y_{0,1})\subseteq Y'_{0,1}$ and $\Phi:Y[1]\to Y'[1]$ is sc-smooth. In the charts, (iii) and (iv) say that the local representatives
are sc-smooth on $[0]$ and on $[1]$, as Definition 2.6.4 (2017: 2.25) asks of transition maps. The preservation of the double
filtration, part of Definition 2.6.1 (2017: 2.22), is not assumed: it follows, and so do the boundedness of the fibre maps and the
sc-smoothness of the base map, $f = P'\circ\Phi\circ0$ with the zero section. A strong bundle isomorphism is a pair of inverse strong
bundle maps. The fibred product $\mathbf X\,{}_s{\times}_P\,W = \{(\psi,w)\mid s(\psi) = P(w)\}$ is Part I's pull-back of $P$ along $s$ (Proposition
2.6.8 (2017: 2.16)), a strong bundle over $\mathbf X$. Added here are its universal property on $[0]$ and on $[1]$, and that over a sheet of $s$
the projection to $W$ is an sc-diffeomorphism, so that this projection is a local sc-diffeomorphism. Strong bundle maps
defined only over open subsets of the base are not formalized; nothing in the chapter needs them (Findings, items 30,
31, 113). *Checked by machine (V8.19):* `Polyfold.StrongBundle.pullback`, `Polyfold.StrongBundle.paracompactSpace_pullback`,
`Polyfold.StrongBundle.pullback_atlas`, `Polyfold.StrongBundle.isScSmoothOn_to_pullback_iff`,
`Polyfold.StrongBundle.isScSmoothMap_pullbackPair`, `Polyfold.StrongBundle.isScDiffeoOn_pullbackProj'`,
`Polyfold.StrongBundle.isLocalScDiffeo_pullbackProj'`, `Polyfold.StrongBundle.IsStrongBundleMap`,
`Polyfold.fiberRestrict`, `Polyfold.StrongBundle.IsStrongBundleMap.fiberMap`,
`Polyfold.StrongBundle.IsStrongBundleMap.isScSmoothMap_base`, `Polyfold.StrongBundle.IsStrongBundleMap.mapsTo_doubleLevel`,
`Polyfold.StrongBundle.IsStrongBundleIso`, `Polyfold.StrongBundle.isStrongBundleMap_pullbackProj'`.

**Definition 8.3.1 (2017: 8.4) (strong bundle over an ep-groupoid).** A strong bundle over the ep-groupoid $X$ is a pair $(P,\mu)$ in
which $P:W\to X$ is a strong bundle over the object M-polyfold and $\mu:\mathbf X\,{}_s{\times}_P\,W\to W$ is a strong bundle map covering $t$, so
that $P(\mu(\psi,w)) = t(\psi)$, with

1. $\mu$ a surjective local sc-diffeomorphism, linear on the fibres;
2. $\mu(1_x,w) = w$ for $w\in W_x$;
3. $\mu(\psi\circ\gamma,w) = \mu(\psi,\mu(\gamma,w))$ whenever $s(\gamma) = P(w)$ and $t(\gamma) = s(\psi)$.

*How this is read.* $\mu$ is a strong bundle map in the sense just described, on Part I's pull-back strong bundle; the
condition $s(\psi) = P(w)$ is carried by the points of the pull-back. Since Part I has strong bundle maps only for local
models, the definition rests on the global reading above. The surjectivity in (1) follows from (2) and is kept, as in
the text (Findings, item 32). *Checked by machine (V8.20):* `Polyfold.EpStrongBundle`, `Polyfold.EpStrongBundle.P_μ`,
`Polyfold.EpGroupoid.unitPair`, `Polyfold.EpStrongBundle.continuous_μ`.

**The fibre maps** *(2017 p. 271).* For $\psi:x\to y$, $\mu(\psi,\cdot):W_x\to W_y$ is a linear isomorphism. It is proved in the stronger form of
a topological linear isomorphism, with inverse $\mu(\psi^{-1},\cdot)$: by (2) and (3), $\mu(\psi^{-1},\mu(\psi,w)) = \mu(\psi^{-1}\circ\psi,w) = \mu(1_x,w) = w$
(Findings, item 32). *Checked by machine (V8.21):* `Polyfold.EpStrongBundle.fiberMor`, `Polyfold.EpStrongBundle.μ_add`,
`Polyfold.EpStrongBundle.μ_smul`, `Polyfold.EpStrongBundle.μ_inv_μ`, `Polyfold.EpStrongBundle.μ_μ_inv`,
`Polyfold.EpStrongBundle.fiberMorEquiv`.

**The functorial picture** *(pp. 375–377 (2017 pp. 271–272)).* With $\mathbf W = \mathbf X\,{}_s{\times}_P\,W$, "we can define the ep-groupoid" $(W,\mathbf W)$:
$s_{\mathbf W}(\psi,w) = w$, $t_{\mathbf W}(\psi,w) = \mu(\psi,w)$, units $(1_x,w)$, inverses $(\psi,w)^{-1} = (\psi^{-1},\mu(\psi,w))$, and $(\psi,w')\circ(\gamma,w) = (\psi\circ\gamma,w)$ for
$w' = \mu(\gamma,w)$. The maps $s_{\mathbf W}$, $t_{\mathbf W}$ cover $s$, $t$, the projections $(P,\pi_1)$ form an sc-smooth functor
$(W,\mathbf W)\to(X,\mathbf X)$, and $|P|:|W|\to|X|$ is continuous and surjective.

*Proof.* The text asserts this without proof. The groupoid laws are (2) and (3) of Definition 8.3.1 (2017: 8.4). Definition 7.1.3 (2017: 7.3): (1)
$s_{\mathbf W}$ is the projection of the pull-back along the local sc-diffeomorphism $s$, hence a local sc-diffeomorphism, and
$t_{\mathbf W} = \mu$ is one by Definition 8.3.1 (1) (2017: 8.4); (2) the units and inverses are sc-smooth by the universal property of the
pull-back; (3) for $w\in W$ take $V = P^{-1}(V(P(w)))$, with $V(P(w))$ as in Definition 7.1.3 (3) (2017: 7.3) for $X$: if $w_k\in\mathrm{cl}\,V$ and
$\mu(\psi_k,w_k)\to w'$, then $s(\psi_k) = P(w_k)\in\mathrm{cl}\,V(P(w))$ and $t(\psi_k) = P(\mu(\psi_k,w_k))\to P(w')$, so a subsequence $\psi_k\to\psi$, and then
$w_k = \mu(\psi_k^{-1},\mu(\psi_k,w_k))\to\mu(\psi^{-1},w')$ by the continuity of $\mu$; (4) holds in the sheet form, through a sheet of $s$ and
condition (4) for $X$. The orbit of $w$ covers that of $P(w)$, since a morphism $\psi$ out of $P(w)$ lifts to $(\psi,w)$; so $|P|$ is
surjective. $\square$

$s_{\mathbf W}$ and $t_{\mathbf W}$ are strong bundle maps covering $s$ and $t$. The composition is total, with a junk value off composable
pairs. Since an `EpGroupoid` has its objects and morphisms in one universe, $W$ lives from here on in the universe of the
objects and morphisms of $X$ (Findings, items 2, 33). *Checked by machine (V8.22):* `Polyfold.EpStrongBundle.morComp`,
`Polyfold.EpStrongBundle.toGroupoidStr`, `Polyfold.EpStrongBundle.exists_isProperMap_tgt`,
`Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr`, `Polyfold.EpStrongBundle.toEpGroupoid`,
`Polyfold.EpStrongBundle.projFunctor`, `Polyfold.EpStrongBundle.isStrongBundleMap_src`,
`Polyfold.EpStrongBundle.isStrongBundleMap_tgt`, `Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor`,
`Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor`.

**Definition 8.3.2 (2017: 8.5) (strong bundle map).** For strong bundles $(P:W\to X,\mu)$ and $(P':W'\to X',\mu')$ over ep-groupoids, a strong
bundle map is a strong bundle map $\Phi:W\to W'$ covering the object map of an sc-smooth functor $\phi:X\to X'$, with
$\Phi(\mu(\gamma,w)) = \mu'(\phi(\gamma),\Phi(w))$ whenever $s(\gamma) = P(w)$.

The definition is read literally, with the global strong bundle maps described above (Findings, item 34). *Checked by
machine (V8.23):* `Polyfold.EpStrongBundle.IsMap`.

**Definition 8.3.3 (2017: 8.6) (strong bundle functor).** A strong bundle functor $\Phi:P\to P'$ is a functor $(W,\mathbf W)\to(W',\mathbf W')$, linear on
the fibres, covering an sc-smooth functor $\phi:X\to X'$, and inducing strong bundle maps $W\to W'$ and $\mathbf W\to\mathbf W'$, with
$P'\circ\Phi = \phi\circ P$.

*How this is read.* "Linear on the fibers", "covers $\phi$" and "induces strong bundle maps" are read together as two strong
bundle map conditions: on objects, for $P$ and $P'$, covering $\phi$ on objects, which contains $P'\circ\Phi = \phi\circ P$; and on morphisms,
for the pull-backs $\mathbf W\to\mathbf X$ and $\mathbf W'\to\mathbf X'$, covering $\phi$ on morphisms (Findings, item 34). *Checked by machine (V8.24):*
`Polyfold.EpStrongBundle.IsStrongBundleFunctor`, `Polyfold.EpStrongBundle.IsStrongBundleFunctor.projFunctor_comp`,
`Polyfold.EpStrongBundle.IsStrongBundleFunctor.mor_val`.

**"These are identical notions"** *(pp. 377–379 (2017 pp. 273–274)).* A strong bundle map $\Phi$ of Definition 8.3.2 (2017: 8.5) lifts to the functor
$\Phi(\gamma,w) = (\phi(\gamma),\Phi(w))$, a strong bundle functor of Definition 8.3.3 (2017: 8.6); conversely the object map of a strong bundle functor
is a strong bundle map of Definition 8.3.2 (2017: 8.5), and the functor is determined by its object map.

*Proof.* The lifted map commutes with sources by construction and with targets by the identity of Definition 8.3.2 (2017: 8.5); it
preserves compositions and units because $\phi$ does. On morphisms it is a map of pull-backs $(\gamma,w)\mapsto(\phi(\gamma),\Phi(w))$, linear on
the fibres, and sc-smooth on $[0]$ and on $[1]$ by the universal property of the pull-back on both levels, which is
proved here for level $[1]$. Conversely, a strong bundle functor commutes with targets, which is the identity of
Definition 8.3.2 (2017: 8.5); and since it commutes with sources and covers $\phi$ on morphisms, it is $(\gamma,w)\mapsto(\phi(\gamma),\Phi(w))$ on morphisms.
$\square$

*Checked by machine (V8.25):* `Polyfold.EpStrongBundle.IsStrongBundleFunctor.isMap`,
`Polyfold.EpStrongBundle.IsMap.liftFunctor`, `Polyfold.EpStrongBundle.IsMap.isStrongBundleFunctor_liftFunctor`,
`Polyfold.EpStrongBundle.IsStrongBundleFunctor.eq_liftFunctor`, `Polyfold.EpStrongBundle.isMap_iff_strongBundleFunctor`,
`Polyfold.StrongBundle.isScSmoothMap_to_pullback_one`, `Polyfold.isLinearMap_fiberRestrict_pullbackMap`.

**Definition 8.3.4 (2017: 8.7) (section functors).** Let $(P:W\to X,\mu)$ be a strong bundle over the ep-groupoid $X$.

1. An sc-smooth section functor is an sc-smooth section $f$ of $P$ with $f(y) = \mu(\varphi,f(x))$ for every morphism $\varphi:x\to y$;
   $\Gamma(P,\mu)$ is "the vector space" of these.
2. An sc$^+$-section functor is an $f\in\Gamma(P,\mu)$ with $f(x)\in W_{0,1}$ for all $x$ that is sc-smooth as a section of $W[1]\to X$;
   $\Gamma^+(P,\mu)\subseteq\Gamma(P,\mu)$ is "the vector subspace" of these.
3. An sc-Fredholm section functor is an $f\in\Gamma(P,\mu)$ that is an sc-Fredholm section of $W\to X$; $\mathrm{Fred}(P,\mu)$ is the
   collection of these.

*How this is read.* (3) uses Part I's Definition 3.1.16 (2017: 3.8) in its germ reading. "Vector space" and "subspace" are read as
closure under Part I's fibrewise zero section, sums and constant multiples; the functorial condition is preserved
because every $\mu(\varphi,\cdot)$ is linear. No module structure on the set of sections is built. The sum of two sc-smooth sections
and the constant multiples of one, which Part I does not state, are proved in the charts (Findings, item 35). *Checked by
machine (V8.26):* `Polyfold.EpStrongBundle.IsScSmoothSectionFunctor`, `Polyfold.EpStrongBundle.IsScPlusSectionFunctor`,
`Polyfold.EpStrongBundle.IsScFredholmSectionFunctor`, `Polyfold.EpStrongBundle.sectionFunctors`,
`Polyfold.EpStrongBundle.plusSectionFunctors`, `Polyfold.EpStrongBundle.fredholmSectionFunctors`,
`Polyfold.EpStrongBundle.fiberZero_mem_sectionFunctors`, `Polyfold.EpStrongBundle.sectionAdd_mem_sectionFunctors`,
`Polyfold.EpStrongBundle.sectionSmul_mem_sectionFunctors`, `Polyfold.EpStrongBundle.plusSectionFunctors_subset`,
`Polyfold.StrongBundle.IsScSmoothSection.sectionAdd_of_isScSmoothSection`,
`Polyfold.StrongBundle.IsScSmoothSection.sectionSmul_const`.

## 7. Proper covering functors and their local structure (pp. 379–388 (2017 pp. 275–279))

**Definition 8.5.1 (2017: 8.8) (proper covering functor).** An sc-smooth functor $F:Y\to X$ between ep-groupoids is a proper covering
functor if

1. $F:Y\to X$ on objects is a surjective local sc-diffeomorphism;
2. every fibre $F^{-1}(x)$ is finite, and there are an open neighbourhood $U(x)$ and mutually disjoint open neighbourhoods
   $U(y)$ of the points $y\in F^{-1}(x)$ such that every $F:U(y)\to U(x)$ is an sc-diffeomorphism and $F^{-1}(U(x)) = \bigcup_{y\in F^{-1}(x)}U(y)$;
3. $L_F:\mathbf Y\to\mathbf X\,{}_s{\times}_F\,Y$, $\varphi\mapsto(F(\varphi),s(\varphi))$, is an sc-diffeomorphism.

*How this is read.* In (2) the inverses $\sigma(y):U(x)\to U(y)$ are part of the data. In (3) $\mathbf X\,{}_s{\times}_F\,Y$ is Part I's
fibred-product sub-M-polyfold of $\mathbf X\times Y$ (Proposition 2.5.20 (2017: 2.15)), as in Definition 7.1.3 (4) (2017: 7.3). Condition (3) says that every
morphism $\varphi$ of $X$ and every $y\in F^{-1}(s(\varphi))$ have exactly one lift, a morphism $\psi$ with $s(\psi) = y$ and $F(\psi) = \varphi$, depending
sc-smoothly on $(\varphi,y)$. This unique lifting is the tool of the rest of the chapter (Findings, item 50). The identity
functor of every ep-groupoid is a proper covering functor (§10). *Checked by machine (V8.27):*
`Polyfold.EpFunctor.IsProperCovering`, `Polyfold.EpFunctor.fibredMap`, `Polyfold.MPolyfold.isSubMPolyfold_fibredProduct`,
`Polyfold.EpFunctor.IsProperCovering.existsUnique_lift`, `Polyfold.EpFunctor.isProperCovering_id`.

**The degeneracy remark** *(pp. 379–385 (2017 pp. 275–276)).* $L_F$ is an sc-diffeomorphism, so $d_{\mathbf Y}(\varphi) = d_{\mathbf X\,{}_s{\times}_F\,Y}(F(\varphi),s(\varphi))$. The
text continues with $d_{\mathbf X\times Y}(\varphi,y) = d_{\mathbf X}(\varphi)+d_Y(y)$ and, $F$ and $s$ being local sc-diffeomorphisms,
$d_{\mathbf X\times Y}(F(\varphi),s(\varphi)) = 2\,d_{\mathbf Y}(\varphi)$, so that $d_{\mathbf X\,{}_s{\times}_F\,Y} = \tfrac12d_{\mathbf X\times Y}$ along the image of $L_F$: "the fibered
product lies in a particular position in the full product".

> **The remark needs $X$ and $Y$ tame, as we read it.** The first equality, and $d_{\mathbf X}(F(\varphi)) = d_{\mathbf Y}(\varphi)$, hold in general,
> by Part I's Proposition 2.4.4 (2017: 2.7): local sc-diffeomorphisms preserve the degeneracy index. The product formula
> $d_{X\times Y} = d_X+d_Y$ is available for tame factors; in general Part I's formalization has only $d_{X\times Y}\le d_X+d_Y$, and Part
> I's Proposition 2.5.20 (2017: 2.15) states its formula $d = \tfrac12d_{X\times Y}$ for the fibred product of tame $X$, $Y$. So the last two
> equalities are proved for tame $X$ and $Y$ (then $\mathbf X$ is tame, $s$ being a local sc-diffeomorphism), and in general
> as the inequality $d_{\mathbf X\times Y}(F(\varphi),s(\varphi))\le2\,d_{\mathbf Y}(\varphi)$. Whether the equality holds without tameness is not settled here
> (Findings, item 51).

*Checked by machine (V8.28):* `Polyfold.EpFunctor.IsProperCovering.degIndex_fibredMap`,
`Polyfold.EpFunctor.IsProperCovering.degIndex_mor`, `Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap_le`,
`Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap`, `Polyfold.MPolyfold.degIndex_prod_le`,
`Polyfold.proposition_2_24`.

**Proposition 8.5.2 (2017: 8.2).** If $F:Y\to X$ and $H:Z\to Y$ are proper covering functors, so is $F\circ H$.

*Proof.* (1): composites of surjective local sc-diffeomorphisms are such, and $(F\circ H)^{-1}(x) = \bigcup_{y\in F^{-1}(x)}H^{-1}(y)$ is finite.
(2), which the text says "follows easily": shrink the neighbourhood $U(x)$ of $F$ to a $U_0$ with $(F|U(y))^{-1}(U_0)\subseteq U'(y)$ for the
evenly covered neighbourhoods $U'(y)$ of $H$, $y\in F^{-1}(x)$, a finite intersection, and cut the neighbourhoods of the points
$z\in H^{-1}(y)$ down accordingly. (3): $L_{F\circ H} = \tilde K\circ L_H$, with $\tilde K:\mathbf Y\,{}_s{\times}_H\,Z\to\mathbf X\,{}_s{\times}_{F\circ H}\,Z$, $(\psi,z)\mapsto(F(\psi),z)$, whose
inverse is $\tilde L(\varphi,z) = (L_F^{-1}(\varphi,H(z)),z)$. $\tilde K$ and $\tilde L$ are maps between sub-M-polyfolds of products; they are
sc-smooth by Part I's Proposition 2.3.19 (2) (2017: 2.6), a map into a sub-M-polyfold being sc-smooth as soon as it is sc-smooth into
the ambient M-polyfold. $\square$

The proof writes "fo" for "for" (2017 p. 276; possible misprint) (Findings, item 52). *Checked by machine (V8.29):*
`Polyfold.EpFunctor.IsProperCovering.evenlyCovered_comp`, `Polyfold.EpFunctor.IsProperCovering.isScDiffeo_fibredMap_comp`,
`Polyfold.EpFunctor.IsProperCovering.proposition_8_2`.

**Theorem 8.5.3 (2017: 8.5) (Proper Covering I).** Let $F:Y\to X$ be a proper covering functor and $x\in X$. For a connected and sufficiently
small open neighbourhood $U(x)$ admitting the natural $G_x$-action $(\Phi,\Gamma)$:

- (0) $F^{-1}(U(x))$ is a disjoint union of connected open neighbourhoods $U(y)$, $y\in F^{-1}(x)$, and every $F:U(y)\to U(x)$ is an
  sc-diffeomorphism;
- (1) $\mathbf U(x) = \Gamma(G_x,U(x)) = \{\varphi\in\mathbf X\mid s(\varphi),t(\varphi)\in U(x)\}$ is the union of connected components $\mathbf U(g)$, $g\in G_x$, and
  $s,t:\mathbf U(g)\to U(x)$ are sc-diffeomorphisms;
- (2) for $y,y'\in F^{-1}(x)$, $\mathbf U(y,y') = \{\psi\in\mathbf Y\mid s(\psi)\in U(y),\ t(\psi)\in U(y')\}$ is the disjoint union of connected open
  neighbourhoods $\mathbf U(\psi_0)$ of the morphisms $\psi_0:y\to y'$, for which (3)–(5) hold;
- (3) $s:\mathbf U(\psi_0)\to U(y)$ and $t:\mathbf U(\psi_0)\to U(y')$ are sc-diffeomorphisms;
- (4) $F:\mathbf U(\psi_0)\to\mathbf U(F(\psi_0))$ is an sc-diffeomorphism;
- (5) the square with top arrow $F:\mathbf U(\psi_0)\to\mathbf U(F(\psi_0))$, left arrow $s:\mathbf U(\psi_0)\to U(s(\psi_0))$, right arrow $t$, and bottom
  arrow $F:U(s(\psi_0))\to U(t(F(\psi_0)))$ is a commutative diagram of sc-diffeomorphisms.

*How this is read.* The data form a *chart* of $F$ at $x$: a natural representation $(U(x),\Phi,\Gamma)$ of Chapter 7, whose $U(x)$
is open and connected, the sets $U(y)$ and $\mathbf U(\psi_0)$, and (0)–(5) as properties. "Disjoint union of connected open
neighbourhoods" means that each set is open, connected and contains its centre, the sets are pairwise disjoint, and
their union is the given set; they are then the connected components. For $\varphi\in\mathbf U(x)$, $\mathbf U(\varphi)$ is the connected component of
$\mathbf U(x)$ containing $\varphi$; by Remark 8.5.4 (2017: 8.2) (a) below, $F(\psi_0)\in G_x\subseteq\mathbf U(x)$, and (1) is Chapter 7's description of $\mathbf U(x)$ by the
sheets $\Gamma(g,U(x))$. "Sc-diffeomorphism" between open sets is Part I's notion, with an inverse. "Sufficiently small" is
proved in two forms: there are charts with $U(x)$ inside every open $V\ni x$, and there is one open $W\ni x$ such that every
natural representation on a connected $U(x)\subseteq W$ belongs to a chart (Findings, item 53).

> **Square (5) as printed does not hold, as we read it.** With the right arrow $t:\mathbf U(F(\psi_0))\to U(t(F(\psi_0)))$ the square
> says $F(s(\psi)) = t(F(\psi))$ for $\psi\in\mathbf U(\psi_0)$. A functor has $F(s(\psi)) = s(F(\psi))$, and $F(\psi) = \Gamma(g,F(s(\psi)))$ with $g = F(\psi_0)$, so
> $t(F(\psi)) = \Phi(g)(F(s(\psi)))$, which differs from $F(s(\psi))$ wherever $\Phi(g)$ moves $F(s(\psi))$. Checked in Lean: the identity
> functor of $\mathbb Z/2\ltimes\mathbb R$, $\mathbb Z/2$ acting by $z\mapsto\pm z$, is a proper covering functor; at $x = 0$, for every chart, the
> sheet $\mathbf U(\psi_0)$ of $\psi_0 = (-1,0)$ contains $\psi = (-1,z)$ with $z\neq0$, and $F(s(\psi)) = z\neq-z = t(F(\psi))$; such charts exist
> (`Polyfold.CoveringExamples.theorem_8_5_five_as_printed`,
> `Polyfold.CoveringExamples.theorem_8_5_five_as_printed_nonvacuous`; Findings, item 54).

So (5) is formalized with $s$ on both vertical arrows: $F(s(\psi)) = s(F(\psi))$ over $F:U(s(\psi_0))\to U(x)$, where the corner
$U(s(F(\psi_0)))$ is $U(x)$ since $s(F(\psi_0)) = t(F(\psi_0)) = x$, the same set as the printed corner. A companion square with $t$ on both
arrows, $F(t(\psi)) = t(F(\psi))$ over $F:U(t(\psi_0))\to U(x)$, is formalized as well. The right arrow $t$ is therefore a possible
misprint for $s$. "Of sc-diffeomorphisms": the left arrows are (3), the top arrow (4), the bottom arrows (0), and the
right arrows $s,t:\mathbf U(F(\psi_0))\to U(x)$ are (1).

*Proof (as formalized).* Let $U'(x)$ and $U'(y)$, $y\in F^{-1}(x)$, be as in Definition 8.5.1 (2) (2017: 8.8), take a natural representation on a
connected $U(x)\subseteq U'(x)$ (Theorem 7.1.13 (2017: 7.1)), and put $U(y) = U'(y)\cap F^{-1}(U(x))$, a copy of $U(x)$ under $F$; this gives (0). For a
morphism $\psi_0:y\to y'$ between points of $F^{-1}(x)$ let $g = F(\psi_0)\in G_x$, and define for $z\in U(y)$
$$\tau(z) = L_F^{-1}\bigl(\Gamma(g,F(z)),z\bigr),$$
the lift at $z$ of the morphism $\Gamma(g,F(z))$ (Definition 8.5.1 (3) (2017: 8.8)); put $\mathbf U(\psi_0) = \tau(U(y))$. $\tau$ is a continuous section of $s$ over
the open set $U(y)$, hence sc-smooth, a continuous section of a local sc-diffeomorphism being locally its local inverse;
so $s:\mathbf U(\psi_0)\to U(y)$ is an sc-diffeomorphism with inverse $\tau$. Next, $F(t(\tau(z))) = t(\Gamma(g,F(z))) = \Phi(g)(F(z))\in U(x)$, so $t\circ\tau$
maps $U(y)$ into $F^{-1}(U(x))$, the disjoint union of the open sets $U(y'')$; $U(y)$ is connected and $t(\tau(y)) = t(\psi_0) = y'$, so
$t\circ\tau$ maps $U(y)$ into $U(y')$, and $t\circ\tau = (F|U(y'))^{-1}\circ\Phi(g)\circ F$ is an sc-diffeomorphism $U(y)\to U(y')$. This is (3). On
$\mathbf U(\psi_0)$, $F = \Gamma(g,\cdot)\circ F\circ s$, a composite of sc-diffeomorphisms onto $\mathbf U(g)$; this is (4), and (5) with $s$ is the
functoriality of $F$. For (2), a morphism $\psi$ from $U(y)$ to $U(y')$ lies over a morphism of $\mathbf U(x)$, so $F(\psi) = \Gamma(g,F(s(\psi)))$ for
exactly one $g\in G_x$ (Theorem 7.1.13 (3) (2017: 7.1)); with $\psi_0$ the lift of $g$ at $y$, both $\psi$ and $\tau(s(\psi))$ lift $F(\psi)$ at $s(\psi)$, so they are
equal. $\square$

The text decomposes the morphisms of $\mathbf Y$ near $F^{-1}(x)$ by sheets $V(\psi)$ and natural representations of the groups $G_y$
in $Y$, in the manner of Proposition 7.1.15 (2017: 7.5), and does not invoke Definition 8.5.1 (3) (2017: 8.8); here (3) does that work, and the
finiteness of $F^{-1}(x)$ and condition (1) of Definition 8.5.1 (2017: 8.8) are not needed. Possible misprints in the proof (2017 p. 278):
"there exists $g\in G_y$ for which $F(\varphi) = \Gamma(g,F(z))$" for $g\in G_x$, $\Gamma$ being the natural representation of $G_x$; "$U(x)$ is a
$G_y$-invariant subset" for $G_x$-invariant; "$F(z') = s(F(\varphi))$" for $t(F(\varphi))$, with $\varphi:z\to z'$; and "admitting admitting". In the
statement, (2) has "morphismsm" (2017 p. 277) (Findings, items 53–55). *Checked by machine (V8.30):*
`Polyfold.EpFunctor.ProperCoveringChart`, `Polyfold.EpFunctor.ProperCoveringChart.comm_src`,
`Polyfold.EpFunctor.ProperCoveringChart.comm_tgt`, `Polyfold.EpFunctor.ProperCoveringLocal.Data`,
`Polyfold.EpFunctor.ProperCoveringLocal.exists_data`, `Polyfold.EpFunctor.ProperCoveringLocal.Data.toChart`,
`Polyfold.EpFunctor.ProperCoveringLocal.isScSmoothOn_of_section`, `Polyfold.EpFunctor.theorem_8_5`,
`Polyfold.EpFunctor.theorem_8_5_of_naturalRep`.

**Remark 8.5.4 (2017: 8.2).** (a) For a morphism $\varphi:y\to y'$ between points of $F^{-1}(x)$, $F(\varphi)$ belongs to $G_x$, since $F$ is a functor. (b) In
Theorem 8.5.3 (2017: 8.5) everything is determined by the choice of the small connected $U(x)$ with the natural $G_x$-action.

*How this is read.* (b) is read as: two charts with the same $U(x)$ have the same $\Phi$ and $\Gamma$ on $U(x)$, because on a connected
$U(x)$ the map $\Gamma(g,\cdot)$ is the continuous section of $s$ through $g$ (Chapter 7's uniqueness of natural representations), the
same sets $U(y)$ and the same sheets $\mathbf U(\psi_0)$, which are connected components of $F^{-1}(U(x))$ and of $\mathbf U(s(\psi_0),t(\psi_0))$. The
remark's comments on the naturality of Theorem 7.1.13's (2017: 7.1) construction and on the main point of the proof have no further
formal content (Findings, item 56). *Checked by machine (V8.31):* `Polyfold.EpFunctor.remark_8_2_a`,
`Polyfold.EpFunctor.isotropyMor`, `Polyfold.EpFunctor.remark_8_2_b`,
`Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_U`,
`Polyfold.EpFunctor.ProperCoveringChart.connectedComponentIn_sheet`.

## 8. Covering functors, geometric lifts and the local model (pp. 387–393 (2017 pp. 279–284))

**Definition 8.5.5 (2017: 8.9) (covering functor, geometric lift).** $\mathrm{Diff}_{sc}$ is the category of M-polyfolds and sc-diffeomorphisms.
Let $D$ and $C$ be categories with finitely many objects and morphisms, all morphisms isomorphisms, and $C$ with a single
object $x$. A covering functor $f:D\to C$ is a functor for which $\mathbf D\to C\,{}_s{\times}_f\,D$, $\psi\mapsto(f(\psi),s(\psi))$, is a bijection. A
geometric lift of $f$ consists of two functors $L_D:D\to\mathrm{Diff}_{sc}$, $L_C:C\to\mathrm{Diff}_{sc}$ and a natural transformation
$\tau:L_D\to L_C\circ f$.

*How this is read.* $C$ is `SingleObj G` for a group $G$, its automorphism group, so $C\,{}_s{\times}_f\,D = G\times D$; $D$ is a Mathlib
groupoid; both are taken in `Type`. The finiteness of $D$, of its hom-sets and of $G$ is not part of the definitions: it is
carried as hypotheses by the results that use it (Proposition 8.5.7 (2017: 8.3), Theorem 8.5.8 (2017: 8.6)). $\mathrm{Diff}_{sc}$ has bundled M-polyfolds of
one universe as objects, and its morphisms are sc-diffeomorphisms with their inverses. $D = \emptyset$ is allowed, as in the
text: the map $\psi\mapsto(f(\psi),s(\psi))$ is then a bijection of empty sets (Findings, item 57). *Checked by machine (V8.32):*
`Polyfold.MPolyfoldCat`, `Polyfold.ScDiffeo`, `Polyfold.coveringMap`, `Polyfold.IsCoveringFunctor`,
`Polyfold.GeometricLift`, `Polyfold.IsCoveringFunctor.existsUnique_lift`, `Polyfold.isCoveringFunctor_of_isEmpty`.

**The discussion after Definition 8.5.5 (2017: 8.9)** *(pp. 388–390 (2017 pp. 280–281)).* Write $U(x) = L_C(x)$ and $U(y) = L_D(y)$. Then $\tau(y):U(y)\to U(x)$ and
$\varphi_{yy'}(\psi) = L_D(\psi):U(y)\to U(y')$ are sc-diffeomorphisms, $\varphi_{yy''}(\psi\circ\gamma) = \varphi_{y'y''}(\psi)\circ\varphi_{yy'}(\gamma)$, the isotropy group $G_y$ acts on
$U(y)$ by $h*z = L_D(h)(z)$ and $G_x$ on $U(x)$ by $g*z = L_C(g)(z)$, and the naturality of $\tau$ makes every $\tau(y)$ equivariant along
$f:G_y\to G_x$, $\tau(y)(h*z) = f(h)*\tau(y)(z)$. All of this is proved as stated. Functoriality is written with Mathlib's $\gamma\gg\psi$ for
the text's $\psi\circ\gamma$, $G_y$ is Mathlib's monoid of endomorphisms of $y$, and the action of $G_x = G$ on $U(x)$ is a left action
through the composition of `SingleObj G` (Findings, item 57). *Checked by machine (V8.33):* `Polyfold.GeometricLift.Ux`,
`Polyfold.GeometricLift.τy`, `Polyfold.GeometricLift.isScDiffeoOn_τy`, `Polyfold.GeometricLift.φ`,
`Polyfold.GeometricLift.φ_comp`, `Polyfold.GeometricLift.smul_def`, `Polyfold.GeometricLift.smul_def'`,
`Polyfold.GeometricLift.τ_equivariant`.

**Disjoint unions of M-polyfolds** *(2017 p. 281).* The proof of Proposition 8.5.7 (2017: 8.3) says that $Y = \bigsqcup_yU(y)$ and
$\mathbf Y = \bigsqcup_{(y,y')}\mathrm{mor}(y,y')\times U(y)$ possess natural M-polyfold structures, without describing them. The structure is the
one whose charts are those of the summands, transported along the inclusions. Charts of different summands have
disjoint domains, and Part I's compatibility of charts then asks for the sc-smoothness of maps between empty retracts,
which holds, so no condition is added. The index type is arbitrary, paracompactness is proved summand by summand, and no
summand needs to be nonempty. Sc-smoothness, local sc-diffeomorphisms, the degeneracy index and tameness are
summand-wise; products distribute over the union, and $G\times U\cong\bigsqcup_GU$ for a discrete $G$ (Findings, item 58). *Checked by
machine (V8.34):* `Polyfold.paracompactSpace_sigma`, `Polyfold.MChart.compatible_of_disjoint`, `Polyfold.MPolyfold.sigma`,
`Polyfold.MPolyfold.isScSmoothMap_sigma_iff`, `Polyfold.MPolyfold.isLocalScDiffeo_sigma_iff`,
`Polyfold.MPolyfold.degIndex_sigma`, `Polyfold.MPolyfold.isTame_sigma_iff`, `Polyfold.isScDiffeoOn_prod_discrete_sigma`.

**Proposition 8.5.7 (2017: 8.3) (geometric lift).** A covering functor $f:D\to C$ with a geometric lift $\tau:L_D\to L_C\circ f$ gives, by a natural
construction, a proper covering functor $F:Y\to X$ between ep-groupoids.

*Proof.* $X = G_x\ltimes U(x)$ is the translation groupoid, with objects $U(x)$, morphisms $G_x\times U(x)$, $s(g,z) = z$ and $t(g,z) = g*z$:
Chapter 7's action ep-groupoid. $Y$ has the objects $\bigsqcup_{y\in D}U(y)$ and the morphisms $\bigsqcup_{(y,y')}\mathrm{mor}(y,y')\times U(y)$, with
$s(\psi,z) = z$, $t(\psi,z) = \varphi_{yy'}(\psi)(z)$, $(\psi,z')\circ(\gamma,z) = (\psi\circ\gamma,z)$ for $z' = \varphi_{yy'}(\gamma)(z)$, $u(z) = (1_y,z)$ and
$\iota(\psi,z) = (\psi^{-1},\varphi_{yy'}(\psi)(z))$. $s$ and $t$ are surjective local sc-diffeomorphisms summand by summand. The text's "one
verifies" is carried out: the composition is sc-smooth in the sheet form, because near $(\psi_0,z_0)$ the summand index of
$\sigma(t\psi)$ is locally constant; and the properness property holds with $V = Y$, because $t$ is proper, finitely many summands
each being mapped homeomorphically onto a summand. $F$ is $\tau(y)$ on $U(y)$ and $F(\psi,z) = (f(\psi),\tau(y)(z))$ on morphisms; it is an
sc-smooth functor by the naturality of $\tau$. Definition 8.5.1 (2017: 8.8): (1) $F$ is a local sc-diffeomorphism, surjective since $D\neq\emptyset$;
(2) holds with $U(x)$ the whole object space of $X$ and, over $w\in U(x)$, one summand around each of the finitely many points
$(y,\tau(y)^{-1}(w))$ of $F^{-1}(w)$; (3) the map (8.16), $(\psi,z)\mapsto((f(\psi),F(z)),z)$, is a bijection by the covering property of $f$, and
its inverse is sc-smooth: near $((g_0,q_0),(y_0,z_0))$ it is $((g_0,q),(y_0,z))\mapsto(\psi_0,z)$, $\psi_0$ the lift of $g_0$ at $y_0$. $\square$

The text deduces that (8.16) is an sc-diffeomorphism from "bijection and local sc-diffeomorphism"; here the inverse is
shown sc-smooth directly. The finiteness of Definition 8.5.5 (2017: 8.9) enters as hypotheses: finitely many morphisms make $t$
proper, finitely many objects make the fibres finite, and a finite $G$ makes $G\ltimes U(x)$ an ep-groupoid. $G$ carries the
discrete topology and is lifted to the universe of $U(x)$, since Chapter 7's translation groupoid takes its group and its
space in one universe; $\mathrm{mor}(y,y')\times U(y)$ is modelled as $\bigsqcup_{\psi:y\to y'}U(y)$; the composition of $Y$ is total, with a junk
value off composable pairs. The proof's "the map $F:X\to Y$" is read as $F:Y\to X$ (possible misprint) (Findings, items 58,
59).

> **$D$ must be nonempty.** Definition 8.5.5 (2017: 8.9) allows $D = \emptyset$, and the empty functor is then a covering functor. Its $Y$
> is empty while $U(x)$ is arbitrary, and $F$ is surjective on objects, as Definition 8.5.1 (1) (2017: 8.8) demands, only if $U(x) = \emptyset$:
> in Lean, $F$ is surjective if and only if $D\neq\emptyset$ or $U(x) = \emptyset$ (`Polyfold.geometricLiftFunctor_surjective_iff`). The
> text does not say so. Proposition 8.5.7 (2017: 8.3) is proved for nonempty $D$, a hypothesis used for the surjectivity only. It
> holds where the proposition is applied, in Theorem 8.5.8 (2017: 8.6), whose $D$ is the full subcategory on $F^{-1}(x)$, nonempty
> because $F$ is surjective (Findings, item 59).

*Checked by machine (V8.35):* `Polyfold.GeometricLift.yObjPolyfold`, `Polyfold.GeometricLift.yMorPolyfold`,
`Polyfold.GeometricLift.isProperMap_yTgt`, `Polyfold.GeometricLift.isScSmoothCompSheet_y`,
`Polyfold.geometricLiftSource`, `Polyfold.geometricLiftTarget`, `Polyfold.geometricLiftFunctor`,
`Polyfold.geometricLiftFunctor_surjective_iff`, `Polyfold.GeometricLift.isScSmoothMap_fibredInv`,
`Polyfold.geometricLiftFunctor_isScDiffeo_fibredMap`, `Polyfold.proposition_8_3`,
`Polyfold.EpGroupoid.Examples.actionEpGroupoid`.

**Theorem 8.5.8 (2017: 8.6) (Proper Covering II).** Let $F:Y\to X$ be a proper covering functor and $x\in X$; let $C$ be the full subcategory
on $x$, with the morphisms $G_x$, and $D$ the full subcategory on the finite set $F^{-1}(x)$. Then $f = F|D:D\to C$ is a covering
functor. For a sufficiently small $U(x)$ as in Theorem 8.5.3 (2017: 8.5) there are a geometric lift $A:K\to L$ of $f$ and fully faithful
open embedding functors $\Phi:L\to X$, $\Psi:K\to Y$, with the image of $\Phi$ the full subcategory on $U(x)$ and the image of $\Psi$ the full
subcategory on $F^{-1}(U(x))$, such that $F\circ\Psi = \Phi\circ A$.

*Proof.* $f$ is a covering functor by the unique lifting of Definition 8.5.1 (3) (2017: 8.8) at the points of $F^{-1}(x)$. Take a chart of
Theorem 8.5.3 (2017: 8.5). The lift: $L_C(x) = U(x)$ and $L_C(g) = \Phi(g)$; $L_D(y) = U(y)$ and, for a morphism $\psi_0:y\to y'$ of $D$,
$L_D(\psi_0) = t\circ(s|\mathbf U(\psi_0))^{-1}$; $\tau(y) = F|U(y)$. The text's "one verifies" is carried out through $F$. On the sheets,
$F(\sigma_\psi(z)) = \Gamma(f(\psi),F(z))$ for $\sigma_\psi = (s|\mathbf U(\psi))^{-1}$, by (1) and (4) of Theorem 8.5.3 (2017: 8.5); hence $\tau(y')\circ L_D(\psi) = \Phi(f(\psi))\circ\tau(y)$, the
naturality of $\tau$, and $L_D$ is a functor because $\Phi$ is a homomorphism and $F$ is injective on each $U(y)$. $A:K\to L$ is the
proper covering functor of Proposition 8.5.7 (2017: 8.3), with $L = G_x\ltimes U(x)$. $\Phi$ is the inclusion on objects and $(g,z)\mapsto\Gamma(g,z)$ on
morphisms; $\Psi$ is the inclusion on objects and $(\psi_0,z)\mapsto(s|\mathbf U(\psi_0))^{-1}(z)$ on morphisms, which preserves compositions and
units by the unique lifting. Both are full, faithful, and injective local sc-diffeomorphisms on objects and on morphisms,
with the stated images, and $F\circ\Psi = \Phi\circ A$. $\square$

*How this is read.* The theorem is stated for ep-groupoids whose objects and morphisms are in `Type`, since Definition
8.5.5 (2017: 8.9) takes $D$ and $G$ in `Type`; this restriction comes from the formalization. "A sufficiently small $U(x)$ as in Theorem
8.5" is any chart of Theorem 8.5.3 (2017: 8.5): charts exist inside every open $V\ni x$, and the conclusion holds for every chart. "A
geometric lift $A:K\to L$" is read as a geometric lift together with the proper covering functor $A$ that Proposition 8.5.7 (2017: 8.3)
associates with it. The morphisms of $D$ are the morphisms $\psi_0$ themselves, so the text's "$\psi:y\to y'\in\mathbf U(\psi_0)$" is read as $\psi = \psi_0$. "Fully
faithful open embedding" is: full and faithful on the underlying groupoids, and an injective local sc-diffeomorphism on
objects and on morphisms; "the image is the full subcategory on $U(x)$" is: the image on objects is $U(x)$, and on
morphisms $\{\varphi\mid s(\varphi),t(\varphi)\in U(x)\}$. The finiteness of $D$ comes from Definition 8.5.1 (2017: 8.8) and Proposition 7.1.12 (2017: 7.4). Possible misprints:
"there exists exists" (2017 p. 283); "$\tau(t):L_D(y)\to L_C\circ f(y)$" for $\tau(y)$, and "$A(\psi,z) = (f(z),F(z))$" for $(f(\psi),F(z))$, as in Proposition
8.5.7's (2017: 8.3) $F(\psi,z) = (f(\psi),\tau(y)(z))$ (2017 p. 284) (Findings, items 2, 60). *Checked by machine (V8.36):* `Polyfold.GroupoidStr.FullOb`,
`Polyfold.EpFunctor.FiberCat`, `Polyfold.EpFunctor.restrictFiber`, `Polyfold.EpFunctor.covering_restrict`,
`Polyfold.EpFunctor.nonempty_fiberCat`, `Polyfold.EpFunctor.IsFullyFaithfulOpenEmbedding`,
`Polyfold.EpFunctor.ProperCoveringChart.geometricLift`, `Polyfold.EpFunctor.ProperCoveringChart.Φ`,
`Polyfold.EpFunctor.ProperCoveringChart.Ψ`, `Polyfold.EpFunctor.ProperCoveringChart.isFullyFaithfulOpenEmbedding_Ψ`,
`Polyfold.EpFunctor.ProperCoveringChart.range_Ψ_mor`, `Polyfold.EpFunctor.ProperCoveringChart.comp_Ψ`,
`Polyfold.EpFunctor.theorem_8_6`.

## 9. Proper strong bundle covering functors and the appendix (pp. 392–400 (2017 pp. 284–289))

**Definition 8.5.9 (2017: 8.10) (proper strong bundle covering functor).** Let $P:W\to Y$ and $Q:V\to X$ be strong bundles over
ep-groupoids, with structure maps $\mu$ and $\tau$. A proper strong bundle covering functor is a strong bundle map $A$, linear on
the fibres, with $Q\circ A = F\circ P$ and

1. $A$ is surjective and a local strong bundle isomorphism covering an sc-smooth proper covering functor $F:Y\to X$;
2. $F^{-1}(x)$ is finite, and there are open neighbourhoods $U(x)$ and mutually disjoint open neighbourhoods $U(y)$,
   $y\in F^{-1}(x)$, with $A:W|U(y)\to V|U(x)$ strong bundle isomorphisms and $F^{-1}(U(x)) = \bigcup_yU(y)$;
3. $\mathbf W\to\mathbf V\,{}_s{\times}_A\,W$, $(\psi,w)\mapsto((F(\psi),A(w)),w)$, is a strong bundle isomorphism covering $L_F:\mathbf Y\to\mathbf X\,{}_s{\times}_F\,Y$, the
   projection being $((\varphi,v),w)\mapsto(\varphi,P(w))$.

*How this is read.* $A$ is taken in the functorial picture, as a strong bundle functor covering $F$ (Definition 8.3.3 (2017: 8.6);
equivalently, its object map is a strong bundle map of Definition 8.3.2 (2017: 8.5)). "A local strong bundle isomorphism" is: every $y$
has open neighbourhoods $U\ni y$ and $U'$ such that $A:W|U\to V|U'$ is a strong bundle isomorphism covering $F:U\to U'$, which means
that $F:U\to U'$ is an sc-diffeomorphism and $A:P^{-1}(U)\to Q^{-1}(U')$ is one on $[0]$ and on $[1]$; the inverse is then linear on
the fibres. The finiteness in (2) is that of Definition 8.5.1 (2) (2017: 8.8) and is not repeated. In (3) the text does not say which
strong bundle structure $\mathbf V\,{}_s{\times}_A\,W\to\mathbf X\,{}_s{\times}_F\,Y$ carries. It is read as the pull-back of $P:W\to Y$ along
$\mathrm{pr}_2:\mathbf X\,{}_s{\times}_F\,Y\to Y$, whose points $((\varphi,y),w)$ with $P(w) = y$ correspond to the text's $((\varphi,v),w)$ with $v = A(w)$; under this
correspondence the projection is the text's. The closing sentence, "all structural statements about proper covering
functors between ep-groupoids lift to the strong bundle situation", is not formalized beyond §8.6.2 (2017 §8.5.2) (Findings, items 70,
113). *Checked by machine (V8.37):* `Polyfold.StrongBundle.IsStrongBundleIsoOn`,
`Polyfold.StrongBundle.IsStrongBundleIsoOn.fiberEquiv`, `Polyfold.EpFunctor.fibredSnd`,
`Polyfold.EpStrongBundle.fibredLift`, `Polyfold.EpStrongBundle.fibredBundleEquiv`,
`Polyfold.EpStrongBundle.pullbackProj_fibredBundleEquiv`, `Polyfold.EpStrongBundle.IsProperStrongBundleCovering`.

**The morphisms over a fibre** *(§8.6.1 (2017 §8.5.1), 2017 p. 286).* For $x\in X$ let $\mathrm{mor}(F^{-1}(x))$ be the set of morphisms between points of
$F^{-1}(x)$. By Definition 8.5.1 (3) (2017: 8.8), $\varphi\mapsto(F(\varphi),s(\varphi))$ is a bijection $\mathrm{mor}(F^{-1}(x))\to G_x\times F^{-1}(x)$, so
$\#\mathrm{mor}(F^{-1}(x)) = \#G_x\cdot\#F^{-1}(x)$. $F^{-1}(x) = \Theta_1\cup\dots\cup\Theta_q$ is the decomposition into isomorphism classes, and points of one
class have isomorphic isotropy groups.

*How this is read.* $\#$ is the cardinality of finite sets: the fibres are finite (Definition 8.5.1 (2) (2017: 8.8)), and so are the
isotropy groups (Proposition 7.1.12 (2017: 7.4)), hence $\mathrm{mor}(F^{-1}(x))$. The classes are indexed by their images in $|Y|$:
$\Theta_c = F^{-1}(x)\cap\pi^{-1}(c)$ for $c\in\pi(F^{-1}(x))\subseteq|Y|$. The statements about $\Theta_c$ hold for every $c$, with $\Theta_c = \emptyset$ off
$\pi(F^{-1}(x))$. With this indexing the correspondence $\Theta_j\leftrightarrow\Theta'_j$ of Lemma 8.6.2 (2017: 8.10) is "the same index" (Findings, item 71).
*Checked by machine (V8.38):* `Polyfold.EpFunctor.fiberClass`, `Polyfold.EpFunctor.fiberIndex`,
`Polyfold.EpFunctor.fiberClasses`, `Polyfold.EpFunctor.nat_card_isotropy_eq_of_mem_fiberClass`,
`Polyfold.EpFunctor.IsProperCovering.morOnFiberEquiv`, `Polyfold.EpFunctor.IsProperCovering.ncard_morOn_fiber`,
`Polyfold.EpFunctor.IsProperCovering.finite_morOn_fiber`.

**Lemma 8.6.1 (2017: 8.9).** For every class $\Theta_j$ and every $y_0\in\Theta_j$,
$$\#G_x\cdot\#\Theta_j = \#\{\psi\in\mathrm{mor}(F^{-1}(x))\mid s(\psi),t(\psi)\in\Theta_j\} = \#G_{y_0}\cdot(\#\Theta_j)^2,\qquad \#G_x = \#G_{y_0}\cdot\#\Theta_j .$$

*Proof.* The set in the middle is $\mathrm{mor}(\Theta_j)$, and the bijection above restricts to a bijection $\mathrm{mor}(\Theta_j)\to G_x\times\Theta_j$
(8.17), since a morphism with source in $\Theta_j$ and target in $F^{-1}(x)$ has its target in $\Theta_j$. Fix morphisms $\psi_y:y_0\to y$,
$y\in\Theta_j$; the maps $\psi\mapsto\psi_{y'}\circ\psi\circ\psi_y^{-1}$ are bijections $G_{y_0}\to\mathrm{mor}(y,y')$, so $\mathrm{mor}(\Theta_j)$ has $\#G_{y_0}\cdot(\#\Theta_j)^2$ elements.
Dividing by $\#\Theta_j\ge1$ gives the last claim. $\square$

(8.17) writes "$\psi\to(F\psi),s(\psi))$", with an unbalanced parenthesis, for $\psi\mapsto(F(\psi),s(\psi))$ (possible misprint) (Findings, item
72). *Checked by machine (V8.39):* `Polyfold.EpFunctor.morOn_fiberClass_eq`,
`Polyfold.EpFunctor.IsProperCovering.morOnClassEquiv`, `Polyfold.EpFunctor.IsProperCovering.lemma_8_9`.

**Lemma 8.6.2 (2017: 8.10).** If $x$ and $x'$ are isomorphic, the isomorphism classes of $F^{-1}(x)$ and of $F^{-1}(x')$ correspond one to one:
there are decompositions $F^{-1}(x) = \bigsqcup_j\Theta_j$ and $F^{-1}(x') = \bigsqcup_j\Theta'_j$ such that, if $y\in F^{-1}(x)$ and $y'\in F^{-1}(x')$ are
isomorphic, there is exactly one $j$ with $y\in\Theta_j$ and $y'\in\Theta'_j$.

*Proof.* Lifting a morphism $x\to x'$ at the points of $F^{-1}(x)$ (Definition 8.5.1 (3) (2017: 8.8)) shows that every point of $F^{-1}(x)$ is
isomorphic to a point of $F^{-1}(x')$, and conversely. So $\pi(F^{-1}(x)) = \pi(F^{-1}(x'))$ in $|Y|$, and with the classes indexed by
$|Y|$ the correspondence is the identity of indices; the index $j$ of the statement is $\pi(y)$, hence unique. $\square$

As a bijection between the sets of classes the correspondence is a separate statement (Findings, items 71, 73). *Checked
by machine (V8.40):* `Polyfold.EpFunctor.IsProperCovering.exists_isomorphic_of_isomorphic`,
`Polyfold.EpFunctor.IsProperCovering.fiberIndex_eq`, `Polyfold.EpFunctor.IsProperCovering.lemma_8_10`,
`Polyfold.EpFunctor.IsProperCovering.lemma_8_10_equiv`.

**Lemma 8.6.3 (2017: 8.11).** If $x$ and $x'$ are isomorphic, then $\#\Theta_j = \#\Theta'_j$ for every $j$, and
$\#F^{-1}(x) = \sum_j\#\Theta_j = \sum_j\#\Theta'_j = \#F^{-1}(x')$.

*Proof.* For isomorphic $y_0\in\Theta_j$ and $y_0'\in\Theta'_j$, $\#G_{y_0} = \#G_{y_0'}$, and $\#G_x = \#G_{x'}$. By the last claim of Lemma 8.6.1 (2017: 8.9),
$\#\Theta_j = \#G_x/\#G_{y_0} = \#G_{x'}/\#G_{y_0'} = \#\Theta'_j$, dividing by $\#G_{y_0}\ge1$. $\square$

Possible misprints: after Lemma 8.6.2 (2017: 8.10) the text writes "Using the third claim of Lemma 8.10" for the third claim of Lemma
8.6.1 (2017: 8.9), Lemma 8.6.2 (2017: 8.10) having no third claim; and Lemma 8.6.3 (2017: 8.11) writes $\sum_{i=1}^q\#\Theta_j$, a sum over $i$ of summands indexed by $j$
(Findings, item 73). *Checked by machine (V8.41):* `Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_sum`,
`Polyfold.EpFunctor.IsProperCovering.lemma_8_11`, `Polyfold.EpFunctor.IsProperCovering.ncard_fiber_eq_of_isomorphic`.

**Proposition 8.6.4 (2017: 8.4).** Let $F:Y\to X$ be a proper covering functor. For every connected component $c$ of $|X|$ there is a
constant $k_c$ with $\#F^{-1}(x) = k_c$ whenever $\pi(x)\in c$. In other words, viewing $\mathbb N$ as an ep-groupoid with only identities,
$x\mapsto\#F^{-1}(x)$ is an sc-smooth functor $X\to\mathbb N$.

*Proof.* $x\mapsto\#F^{-1}(x)$ is locally constant: for $x'\in U(x)$ of Definition 8.5.1 (2) (2017: 8.8), $y\mapsto(F|U(y))^{-1}(x')$ is a bijection
$F^{-1}(x)\to F^{-1}(x')$. By Lemma 8.6.3 (2017: 8.11) it is constant on isomorphism classes, so it descends to $|X|$, where it is locally
constant in the quotient topology ($\pi$ is open, Proposition 7.1.8 (2017: 7.1)), hence constant on connected components. As a functor it
sends a morphism $\varphi$ to the identity of $\#F^{-1}(s(\varphi)) = \#F^{-1}(t(\varphi))$. $\square$

The text argues that "the structure of isomorphism classes" of $F^{-1}(x)$ "stays the same" under perturbation; the proof
uses only the local constancy of the number of points, and the finer claim is not formalized. The text's
$\mathbb N = \{1,2,\dots\}$ is Lean's $\mathbb N$, with $0$, as the trivial ep-groupoid of the discrete M-polyfold; the values are $\ge1$
(Findings, items 74, 113). *Checked by machine (V8.42):* `Polyfold.EpFunctor.IsProperCovering.one_le_ncard_fiber`,
`Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_ncard_fiber`, `Polyfold.EpFunctor.IsProperCovering.fiberCardOrbit`,
`Polyfold.EpFunctor.IsProperCovering.isLocallyConstant_fiberCardOrbit`,
`Polyfold.EpFunctor.IsProperCovering.proposition_8_4`, `Polyfold.EpFunctor.IsProperCovering.fiberCardFunctor`.

**The structure of strong bundle coverings** *(§8.6.2 (2017 §8.5.2), 2017 pp. 288–289).* For a proper strong bundle covering functor $A$
over $F$, on morphisms $A(\varphi,w) = (F(\varphi),A_{s(\varphi)}(w))$, where $A_y:P^{-1}(y)\to Q^{-1}(F(y))$ is the topological linear isomorphism
induced by $A$. From $t(A(\varphi,w)) = A(t(\varphi,w))$,
$$\mu_X(F(\varphi))\circ A_{s(\varphi)} = A_{t(\varphi)}\circ\mu_Y(\varphi),$$
so that, viewing $\mu_Y$ and $\mu_X$ as functors into the category $\mathrm{Ban}$ of Banach spaces and topological linear isomorphisms,
$y\mapsto A_y$ is a natural transformation $\mu_Y\to\mu_X\circ F$.

*How this is read.* The natural transformation is stated as its naturality identity, the fibres $Q^{-1}(F(s(\varphi)))$ and
$Q^{-1}(s(F(\varphi)))$ being identified through their values in $V$; the category $\mathrm{Ban}$ is not formalized. Only the strong
bundle functor part of Definition 8.5.9 (2017: 8.10) enters the identity; condition (1) makes the $A_y$ topological linear isomorphisms
(Findings, item 75). *Checked by machine (V8.43):* `Polyfold.EpStrongBundle.IsProperStrongBundleCovering.mor_val`,
`Polyfold.EpStrongBundle.IsProperStrongBundleCovering.fiberEquiv`, `Polyfold.EpStrongBundle.IsStrongBundleFunctor.μ_comm`,
`Polyfold.EpStrongBundle.section_8_5_2`.

## 10. Witnesses: the hypotheses can hold

A hypothesis that nothing satisfies would make a theorem empty. The formalization checks every hypothesis of the chapter
on examples, all in Lean (`Polyfold/Chapter8/NonVacuity.lean`, `NonVacuityBundle.lean`, and witnesses next to the
statements; Findings, items 100–105).

- *Tame ep-groupoids and their tangents.* The trivial ep-groupoid of $\mathbb R^n$ is tame, and so is its tangent (Lemma 8.1.9 (2017: 8.8),
  Theorems 8.1.1, 8.1.12 (2017: 8.1, 8.3)). The tame $X$, $Y$ of the degeneracy remark are satisfied by the identity of the trivial ep-groupoid
  of $\mathbb R^n$ (not stated as a lemma). `Polyfold.EpGroupoid.isTame_trivial_rn`,
  `Polyfold.EpGroupoid.isTame_tangentEpGroupoid_trivial_rn`.
- *Paracompact orbit spaces.* The trivial ep-groupoid of any M-polyfold has paracompact orbit space, and hence so has its
  tangent (Theorem 8.1.15 (2017: 8.4)). `Polyfold.EpGroupoid.hasParacompactOrbitSpace_trivial`,
  `Polyfold.EpGroupoid.hasParacompactOrbitSpace_tangent_trivial`.
- *Covering functors.* The identity of `SingleObj G` is a covering functor for every group $G$; for nontrivial $G$ the functor
  sending every morphism to $1$ is not; the empty groupoid gives one (Definition 8.5.5 (2017: 8.9)).
  `Polyfold.CoveringExamples.isCoveringFunctor_id`, `Polyfold.CoveringExamples.not_isCoveringFunctor_one`,
  `Polyfold.isCoveringFunctor_of_isEmpty`.
- *A geometric lift, and Proposition 8.5.7 (2017: 8.3) applied.* $\mathbb Z/2 = \mathbb Z^\times$ acting on $\mathbb R$ by $y\mapsto\pm y$ is a geometric lift of the
  identity of `SingleObj ℤˣ`, with $L_D = L_C$ and $\tau = 1$. Proposition 8.5.7 (2017: 8.3) makes it a proper covering functor onto
  $\mathbb Z/2\ltimes\mathbb R$, with non-trivial isotropy at $0$ and nonempty $D$. `Polyfold.CoveringExamples.reflectionLift`,
  `Polyfold.CoveringExamples.isProperCovering_reflectionLift`.
- *Proper covering functors.* The identity functor of every ep-groupoid is a proper covering functor, so Definition 8.5.1 (2017: 8.8),
  Propositions 8.5.2 and 8.6.4 (2017: 8.2 and 8.4), Theorems 8.5.3 and 8.5.8 (2017: 8.5 and 8.6) and Lemmas 8.6.1–8.6.3 (2017: 8.9–8.11) are not vacuous. Theorem 8.5.8 (2017: 8.6) quantifies over all
  charts of Theorem 8.5.3 (2017: 8.5), and charts exist inside every open neighbourhood of $x$. `Polyfold.EpFunctor.isProperCovering_id`,
  `Polyfold.EpFunctor.theorem_8_5`.
- *Square (5) as printed.* On the identity functor of $\mathbb Z/2\ltimes\mathbb R$ (§7).
  `Polyfold.CoveringExamples.theorem_8_5_five_as_printed`,
  `Polyfold.CoveringExamples.theorem_8_5_five_as_printed_nonvacuous`.
- *Strong bundles over ep-groupoids.* Every strong bundle over an M-polyfold is a strong bundle over the trivial
  ep-groupoid of the M-polyfold, with $\mu(z,w) = w$ (Definition 8.3.1 (2017: 8.4)); the identity is a strong bundle map, a strong bundle
  functor and a proper strong bundle covering functor (Definitions 8.3.2, 8.3.3, 8.5.9 (2017: 8.5, 8.6, 8.10), the last on the reading of (3) in §9);
  over the trivial ep-groupoid every section is functorial, so $\Gamma$, $\Gamma^+$ and $\mathrm{Fred}$ are Part I's sc-smooth, sc$^+$- and
  sc-Fredholm sections. A concrete instance in `Type`: Part I's trivial strong bundle $\mathbb R^n\times\mathbb R^k\to\mathbb R^n$ over the trivial
  ep-groupoid of $\mathbb R^n$, whose functorial picture is an ep-groupoid, whose identity is a proper strong bundle covering
  functor, with $0\in\Gamma^+$, and with the graph section $x\mapsto(x,\phi(x))$ of a $C^\infty$ map $\phi:\mathbb R^n\to\mathbb R^k$ in $\Gamma$ and in $\mathrm{Fred}$.
  `Polyfold.EpStrongBundle.trivial`, `Polyfold.EpStrongBundle.isMap_id`,
  `Polyfold.EpStrongBundle.isStrongBundleFunctor_id`, `Polyfold.EpStrongBundle.isProperStrongBundleCovering_id`,
  `Polyfold.EpStrongBundle.isFunctorialSection_trivial`, `Polyfold.TrivialBundle.epBundle`,
  `Polyfold.TrivialBundle.epBundleEpGroupoid`, `Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering`,
  `Polyfold.TrivialBundle.fiberZero_mem_plusSectionFunctors_epBundle`,
  `Polyfold.TrivialBundle.graphSection_mem_fredholmSectionFunctors_epBundle`.

What the witnesses do not exercise: every proper covering functor constructed has one-point fibres $F^{-1}(x)$ (the
identities, and the functor of the reflection lift, whose $D$ has one object). So the even coverings of Definitions 8.5.1
(2) and 8.5.9 (2) (2017: 8.8 and 8.10) are met with one sheet, and the counting of Appendix 8.6 (2017 8.5) only with $q = 1$ and $\#\Theta_1 = 1$. No proper
strong bundle covering functor other than identities is constructed, and $\Gamma^+$ is witnessed by the zero section only.
The marked particle of §11, with three-point fibres, is computed by hand. Every hypothesis that quantifies over charts
or neighbourhoods is existential and satisfiable: tameness (a tame atlas), the paracompact orbit space, and the chart of
Theorem 8.5.3 (2017: 8.5), a datum that exists inside every neighbourhood. No hypothesis of the form "for all compatible charts" is
made in Chapter 8 (Findings, item 105).

## 11. Application: the motion of two beads, a marked particle, and forces

The computations below were done by hand; they are not checked in Lean. The ep-groupoids are action ep-groupoids of
finite groups, of which the general construction is formalized (Chapter 7, §9), but the instances below, the functor
that forgets the mark and the bundle of forces are not written out.

**The motion of two identical beads.** In the coordinate $v = (b-a)/2$ the ep-groupoid of Chapter 7 is $\{\pm1\}$ acting on $\mathbb R$
by $v\mapsto\pm v$ (the coordinate $u$ is untouched, and its tangent is a factor $\mathbb R^2_{(u,\dot u)}$). Its morphisms are $\{\pm1\}\times\mathbb R$, two
copies of $\mathbb R$, and a tangent vector to the morphism $(-1,v)$ is a velocity $\dot v$ at $v$; by (8.3) it is the morphism
$(v,\dot v)\to(-v,-\dot v)$ of the tangent. So the tangent ep-groupoid is $\{\pm1\}$ acting on $\mathbb R^2_{(v,\dot v)}$ by $\pm\mathrm{id}$, the
derivative of the action, and (8.5) is the composition of this action groupoid. The map $q(v,\dot v) = (v+i\dot v)^2 = (v^2-\dot v^2,\,2v\dot v)$
is constant on the orbits and induces a continuous bijection $\mathbb R^2/\pm1\to\mathbb C$, which is proper, hence a homeomorphism. So
the orbit space $|TX|$ is a plane, metrizable as Theorem 8.1.15 (2017: 8.4) says, although $|X| = [0,\infty)$ has a boundary point. The map
$|p|:|TX|\to|X^1| = [0,\infty)$ has a line of velocities as fibre over $|v|>0$, and over $0$ the half-line of the $|\dot v|$, the states
of two beads at the same place. The two motions of Chapter 7, §0, now meet in one curve: the beads passing through each
other, $v(t) = -t$, $\dot v = -1$, and the beads bouncing off each other, $v(t) = |t|$, $\dot v = \mathrm{sign}(t)$, both give
$q = (t^2-1,\,2t)$, a smooth curve in $|TX|\cong\mathbb C$; for unlabelled beads they are the same motion.

**A marked particle among three.** Let $X = S_3\ltimes\mathbb R^3$, three identical particles on a line (Chapter 7, §10), with
$(\sigma\cdot x)_i = x_{\sigma^{-1}(i)}$. Let $Y$ have the objects $\{1,2,3\}\times\mathbb R^3$, where $(i,x)$ is the configuration $x$ with the particle
$i$ marked, and the morphisms $(\sigma,(i,x)):(i,x)\to(\sigma(i),\sigma\cdot x)$: the action ep-groupoid of $S_3$ acting on both factors. Forgetting
the mark, $F(i,x) = x$ and $F(\sigma,(i,x)) = (\sigma,x)$, is a functor. It is a proper covering functor (Definition 8.5.1 (2017: 8.8)): (1) on
objects it is the identity on each of three copies of $\mathbb R^3$; (2) $F^{-1}(x) = \{(1,x),(2,x),(3,x)\}$, evenly covered with
$U(x) = \mathbb R^3$ and $U((i,x)) = \{i\}\times\mathbb R^3$; (3) $L_F(\sigma,(i,x)) = ((\sigma,x),(i,x))$, and the points of $\mathbf X\,{}_s{\times}_F\,Y$ are exactly the pairs
$((\sigma,x),(i,x))$, so $L_F$ is a bijection whose inverse $((\sigma,x),(i,x))\mapsto(\sigma,(i,x))$ is smooth. The morphisms between points of
$F^{-1}(x)$ are the $(\sigma,(i,x))$ with $\sigma\in G_x$; so the $D$ of Theorem 8.5.8 (2017: 8.6) is $G_x$ acting on the labels $\{1,2,3\}$, and $f(\sigma,(i,x)) = \sigma$
is a covering functor: every $\sigma\in G_x$ has exactly one lift at every $(i,x)$. The classes $\Theta_j$ are the orbits of $G_x$ on the
labels, and the isotropy group $G_{(i,x)}$ is the stabilizer of the label $i$ in $G_x$. Writing $i$ for $(i,x)$:

| $x$ | $G_x$ | classes $\Theta_j$ | $G_{y_0}$, $y_0\in\Theta_j$ | $\#G_x = \#G_{y_0}\cdot\#\Theta_j$ | $\#\mathrm{mor}(F^{-1}(x))$ |
|---|---|---|---|---|---|
| $(0,1,2)$ | $1$ | $\{1\}$, $\{2\}$, $\{3\}$ | $1$ | $1 = 1\cdot1$ | $1\cdot3 = 3$ |
| $(0,0,1)$ | $\{1,(12)\}$ | $\{1,2\}$, $\{3\}$ | $1$; $\{1,(12)\}$ | $2 = 1\cdot2$; $2 = 2\cdot1$ | $2\cdot3 = 6$ |
| $(0,0,0)$ | $S_3$ | $\{1,2,3\}$ | $\{1,(23)\}$ for $y_0 = 1$ | $6 = 2\cdot3$ | $6\cdot3 = 18$ |

The last claim of Lemma 8.6.1 (2017: 8.9) is the orbit–stabilizer theorem for $G_x$ acting on the labels. Its middle term counts the
morphisms within a class: $\#G_{y_0}\cdot(\#\Theta_j)^2$ is $1\cdot4 = 4$ and $2\cdot1 = 2$ at $(0,0,1)$, which add up to the $6$ of the table,
and $2\cdot9 = 18$ at $(0,0,0)$. For Lemmas 8.6.2 and 8.6.3 (2017: 8.10 and 8.11) take $x = (0,0,1)$ and $x' = (23)\cdot x = (0,1,0)$, with $G_{x'} = \{1,(13)\}$ and classes
$\{1,3\}$, $\{2\}$. The lifts of $(23):x\to x'$ send $(1,x)\mapsto(1,x')$, $(2,x)\mapsto(3,x')$, $(3,x)\mapsto(2,x')$, so $\Theta_1 = \{1,2\}$ corresponds to
$\Theta'_1 = \{1,3\}$ and $\Theta_2 = \{3\}$ to $\Theta'_2 = \{2\}$, with the same cardinalities $2$ and $1$ and the same total $3$. In the indexing of §9 the
two indices are points of $|Y|$: "the marked particle is one of the coincident pair" and "the marked particle is the lone
one", the same two points for $x$ and for $x'$. Since $|X|$ is connected, Proposition 8.6.4 (2017: 8.4) gives $\#F^{-1}(x) = 3$ for every $x$.

On orbit spaces, every class of $Y$ contains points with the label $3$, whose stabilizer is $\{1,(12)\}$, so
$|Y|\cong\mathbb R^3/\{1,(12)\}$. The map $|Y|\to|X|$ has three preimages over a configuration with distinct positions, two over a double
point and one over a triple collision: these are the numbers $q$ of classes in the table. It is not a covering map; what
is constant is the weighted count $\sum_j\#\Theta_j = \sum_j\#G_x/\#G_{y_j} = 3$, which is why the appendix counts upstairs.

**Forces as a section functor.** Over $X = S_3\ltimes\mathbb R^3$ take the trivial bundle $W = \mathbb R^3\times\mathbb R^3\to\mathbb R^3$, a force $w\in\mathbb R^3$ on the three
particles at every configuration, and $\mu((\sigma,x),(x,w)) = (\sigma\cdot x,\sigma\cdot w)$, permuting the components of the force with the
particles. $\mu$ covers $t$, is linear on the fibres and a local diffeomorphism, $\mu(1_x,\cdot) = \mathrm{id}$, and
$\mu((\tau,\sigma\cdot x)\circ(\sigma,x),w) = (\tau\sigma\cdot x,\tau\sigma\cdot w) = \mu((\tau,\sigma\cdot x),\mu((\sigma,x),w))$: this is Definition 8.3.1 (2017: 8.4), in finite dimensions, where every
level of the bundle is the same. A section functor (Definition 8.3.4 (1) (2017: 8.7)) is a smooth $f:\mathbb R^3\to\mathbb R^3$ with $f(\sigma\cdot x) = \sigma\cdot f(x)$. For a
pair potential $V(x) = \sum_{i<j}\phi(x_i-x_j)$ with $\phi$ smooth and even, $V(\sigma\cdot x) = V(x)$; differentiating, and using that the
permutation matrix $\sigma$ is orthogonal, $\nabla V(\sigma\cdot x) = \sigma\cdot\nabla V(x)$, so the force field $f = -\nabla V$ is a section functor. Its zeros, the
equilibria, form a saturated set: $f(x) = 0$ implies $f(\sigma\cdot x) = \sigma\cdot0 = 0$. An equilibrium of three identical particles is
therefore a point of $|X|$, and the functorial condition is what makes the zero set of a section a subset of the orbit
space.

## 12. Summary of what was silently assumed, now made explicit

| Where (2017 text) | HWZ say | What is actually needed |
|---|---|---|
| 2017 p. 258, (8.5) | $(\psi,k)\circ(\varphi,h)\in T_{\varphi\circ\psi}\mathbf X$ | $T_{\psi\circ\varphi}\mathbf X$ (possible misprint); the composite unique by fibre injectivity of $Ts$ |
| pp. 358–364 (2017 pp. 258–263) | tangents of $(s\vert\mathbf U(\psi))^{-1}$ and $\alpha$; "by construction" | tangents of maps sc-smooth on open sets, built from the charts |
| p. 359 (2017 p. 259), Lemma 8.1.2 (2017: 8.1) | $T(\mathbf X\,{}_s{\times}_t\,\mathbf X) = T\mathbf X\,{}_{Ts}{\times}_{Tt}\,T\mathbf X$, $(\psi,k)\circ(\varphi,h) = Tm(\psi,\varphi)(k,h)$ | the sheet form $k\circ h = Tg(h)$; the identification not formalized (G.75) |
| pp. 361–372 (2017 pp. 260–268), Lemmas 8.1.4–8.1.6 (2017: 8.3–8.5), Thm. 8.1.11 (2017: 8.2), Prop. 8.1.14 (2017: 8.1) | differentiate the identities | fibre injectivity of $Ts$ and the chain rule |
| p. 362 (2017 p. 262), Lemma 8.1.7 (2017: 8.6) | "$m_{T\mathbf X}$ is precisely $Tm$" | condition (4) in the sheet form |
| pp. 363–364 (2017 pp. 262–263), Lemma 8.1.8 (2017: 8.7) | $\varphi_k\to\varphi$ in $\mathbf X^1$; $t(\varphi_k,h_k) = Ts(\varphi_k)(h_k)$ | not needed; $Tt$ (possible misprint) |
| p. 364 (2017 p. 263), Lemma 8.1.9 (2017: 8.8) | "$Tr$ is a tame retraction" | proved from Part I's Definition 2.5.2 (2017: 2.17), for one presentation, and Lemma 1.3.4 (2017: 1.1) |
| pp. 364 ff. (2017 pp. 264–265), Rem. 8.1.10 (2017: 8.1) | $G(\varphi,h) = (T\varphi,Ts(h))$ a bijection; $T\varphi$ linear; "at $\varphi$" | $T\varphi$ labelled by $\varphi$; linearity not formalized (G.7, G.70); at $x$ (possible misprint) |
| p. 365 (2017 p. 265), Thm. 8.1.11 (2017: 8.2) | the units "left to the reader" | proved |
| p. 366 (2017 p. 266), Thm. 8.1.12 (2017: 8.3) | $T:\mathcal{EP}\to\mathcal{EP}$ | `EP.{max u 1} ⥤ EP.{max u 1}` (from the formalization) |
| 2017 p. 267 | $\simeq$ an equivalence relation | the sc-smoothness of $x\mapsto\tau'(x)\circ\tau(x)$, by the sheet form |
| p. 368 (2017 p. 268), Thm. 8.1.15 (2017: 8.4) | a local bundle model $TO\to O^1$; closed paracompact cover, regularity, Prop. 2.7.4 (2017: 2.17) | metrizability along $\lvert p\rvert$; the open embedding $G_x\backslash TU(x)\to\lvert TX\rvert$; "parcompact" (possible misprint) |
| pp. 372–373 (2017 pp. 268–270), Defs. 8.2.1, 8.2.2 (2017: 8.2, 8.3) | sc-differential forms, the sc-de Rham complex | not formalized (G.74) |
| pp. 373–396 (2017 pp. 270–285), §§8.3, 8.5 (2017 §§8.3–8.4) | strong bundle maps between strong bundles | a global reading of Part I's Definition 2.6.1 (2017: 2.22) |
| pp. 375–377 (2017 pp. 271–272) | "we can define the ep-groupoid" $(W,\mathbf W)$ | proved: properness by sequences, (4) in the sheet form |
| pp. 377–379 (2017 pp. 273–274) | "these are identical notions" | proved, with the universal property of the pull-back on $[1]$ |
| pp. 379 ff. (2017 pp. 274–275), Def. 8.3.4 (2017: 8.7) | "the vector space $\Gamma(P,\mu)$" | closure under zero, sums and constant multiples |
| pp. 379–385 (2017 pp. 275–276) | $d_{\mathbf X\times Y} = d_{\mathbf X}+d_Y$ | $X$, $Y$ tame; in general only $\le$ |
| p. 384 (2017 p. 276), Prop. 8.5.2 (2017: 8.2) | (2) "follows easily"; "fo" | shrinking $U(x)$; "for" (possible misprint) |
| p. 385 (2017 p. 277), Thm. 8.5.3 (5) (2017: 8.5) | right arrow $t$, corner $U(t(F(\psi_0)))$ | $s$ on both arrows; as printed it does not hold as we read it |
| pp. 386–388 (2017 pp. 278–279), proof of Thm. 8.5.3 (2017: 8.5) | sheets and natural representations of the $G_y$; "$g\in G_y$"; "$F(z') = s(F(\varphi))$" | Definition 8.5.1 (3) (2017: 8.8); $g\in G_x$, $t(F(\varphi))$ (possible misprints) |
| pp. 386–387 (2017 pp. 277–278), Rem. 8.5.4 (2017: 8.2) (b) | "everything is determined by $U(x)$" | the same $\Phi$, $\Gamma$, $U(y)$, $\mathbf U(\psi_0)$ |
| p. 388 (2017 p. 279), Def. 8.5.5 (2017: 8.9) | $D$, $C$ finite; $D$ may be empty | finiteness as hypotheses; $D\neq\emptyset$ for Prop. 8.5.7 (2017: 8.3) |
| p. 390 (2017 p. 281) | $\bigsqcup_yU(y)$ "possesses a natural M-polyfold structure" | the charts of the summands |
| pp. 390–391 (2017 pp. 281–282), Prop. 8.5.7 (2017: 8.3) | "one verifies"; (8.16) a bijective local sc-diffeomorphism; "$F:X\to Y$" | carried out; the inverse sc-smooth directly; $F:Y\to X$ (possible misprint) |
| pp. 392–393 (2017 pp. 283–284), Thm. 8.5.8 (2017: 8.6) | "a geometric lift $A:K\to L$"; "one verifies"; $A(\psi,z) = (f(z),F(z))$ | the lift with its functor; carried out; $(f(\psi),F(z))$ (possible misprint); ep-groupoids in `Type` |
| p. 394 (2017 p. 285), Def. 8.5.9 (3) (2017: 8.10) | the strong bundle $\mathbf V\,{}_s{\times}_A\,W\to\mathbf X\,{}_s{\times}_F\,Y$ | the pull-back of $P$ along $\mathrm{pr}_2$ |
| 2017 p. 286, (8.17) | "$\psi\to(F\psi),s(\psi))$" | $\psi\mapsto(F(\psi),s(\psi))$ (possible misprint) |
| p. 398 (2017 p. 287) | "the third claim of Lemma 8.10"; $\sum_{i=1}^q\#\Theta_j$ | Lemma 8.6.1 (2017: 8.9); one summation index (possible misprints) |
| p. 399 (2017 p. 288), Prop. 8.6.4 (2017: 8.4) | "the structure of isomorphism classes stays the same"; $\mathbb N = \{1,2,\dots\}$ | the local constancy of $\#F^{-1}(x)$; Lean's $\mathbb N$, values $\ge1$ |
| 2017 pp. 288–289, §8.6.2 (2017 §8.5.2) | a natural transformation of functors into $\mathrm{Ban}$ | its naturality identity |

---

**Checked by machine.** The chapter is formalized in Lean 4 against Mathlib in `Polyfold/Chapter8/` (`Basic.lean`,
`TangentLocal.lean`, `TangentEp.lean`, `TangentTame.lean`, `NatTrans.lean`, `TangentOrbit.lean`, `StrongBundleMap.lean`,
`EpStrongBundle.lean`, `ProperCovering.lean`, `ProperCoveringLocal.lean`, `SigmaPolyfold.lean`, `GeometricLift.lean`,
`NonVacuity.lean`, `NonVacuityBundle.lean`); the paragraphs "*Checked by machine*" name the declarations. Formalized:
every definition of the chapter except Definitions 8.2.1 and 8.2.2 (2017: 8.2 and 8.3) (Definitions 8.1.13 and 8.3.1–8.5.9 (2017: 8.1 and 8.4–8.10)); Theorems 8.1.1–8.5.8 (2017: 8.1–8.6);
Propositions 8.1.14, 8.5.2 and 8.6.4 (2017: 8.1, 8.2 and 8.4), and Proposition 8.5.7 (2017: 8.3) for nonempty $D$; Lemmas 8.1.2–8.6.3 (2017: 8.1–8.11), Lemma 8.1.2 (2017: 8.1) in the sheet form of its
proof; Remark 8.1.10 (2017: 8.1) without its linearity claims, and Remark 8.5.4 (2017: 8.2); the claims the text makes in passing on 2017 pp. 257–258, 267, 270–276, 280–281, 286 and 288–289; the tangents of maps on open sets, global strong bundle maps and disjoint unions of
M-polyfolds, which the text uses without definition; the witnesses of §10. **Theorems 8.1.1–8.5.8 (2017: 8.1–8.6) hold** with the readings
above. In a changed form: Theorem 8.1.12 (2017: 8.3) as a functor `EP.{max u 1} ⥤ EP.{max u 1}`; Theorem 8.1.15 (2017: 8.4) with the stronger
conclusion that $|TX|$ is metrizable, proved by metrizability; Theorem 8.5.3 (2017: 8.5) with square (5) read with $s$ on both vertical
arrows (as printed, with $t$ on the right, it does not hold as we read it, checked in Lean), proved through Definition 8.5.1
(3) (2017: 8.8); Theorem 8.5.8 (2017: 8.6) for ep-groupoids in `Type`; Lemma 8.1.9 (2017: 8.8) with "$Tr$ is a tame retraction" proved from the definitions; the
degeneracy remark for tame $X$, $Y$, and as an inequality in general; Definition 8.3.1 (2017: 8.4) and everything after it with global
strong bundle maps, a reading. Not formalized: Definitions 8.2.1 and 8.2.2 (2017: 8.2 and 8.3) (gap G.74); Lemma 8.1.2 (2017: 8.1) as printed, the
identification $T(\mathbf X\,{}_s{\times}_t\,\mathbf X) = T\mathbf X\,{}_{Ts}{\times}_{Tt}\,T\mathbf X$ with $m_{T\mathbf X} = Tm$ (gap G.75); the linearity of $T_xX$, of $T\varphi$
and of the action of $G_x$ on $TU(x)$ (gaps G.7 and G.70, which is now formalized in part); without a gap, since nothing
depends on them: the M-polyfold structure transported along $G$ in Remark 8.1.10 (2017: 8.1) and the triples $(a,T\varphi,b)$, the local
bundle model $TO\to O^1$ of the text's proof of Theorem 8.1.15 (2017: 8.4), the remarks on naturality in Remark 8.5.4 (2017: 8.2) (b), strong bundle
maps over open subsets of the base, the closing sentence of Definition 8.5.9 (2017: 8.10), the "structure of isomorphism classes"
before Proposition 8.6.4 (2017: 8.4) and the category $\mathrm{Ban}$ of §8.6.2 (2017 §8.5.2); the computations of §11, done by hand. All witnesses of proper
covering functors have one-point fibres. The machine-checked statements are listed in `Exposition/Verification.md`
(V8.1–V8.43), compared with the text in `Exposition/polyfold-beside-lean.html` and retold in `Exposition/ProofByProof.md`.
The findings are `Exposition/Findings.md`, "Chapter 8", items
1–13, 20–21, 30–35, 50–60, 70–75, 100–105 and 110–114 (numbered in blocks; the gaps in the numbering are unused numbers).
