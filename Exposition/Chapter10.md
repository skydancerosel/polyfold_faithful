# Chapter 10. Equivalences and localization: when two ep-groupoids describe the same space (HWZ Part II, Chapter 10, pp. 461–520 (2017 pp. 333–374))

*Hofer–Wysocki–Zehnder, "Polyfold and Fredholm Theory", Part II, Chapter 10 (arXiv 1707.08941, pp. 333–374), rewritten for a
first-year graduate student who has read Chapters 7 and 8 and wants to know why two different ep-groupoids can describe the
same polyfold, and how to make that precise. Every formalized statement is proved; what is not formalized is marked. Where
the Lean formalization found a gap or a shorter route, the text follows the Lean. Statement numbers and printed pages are
those of the book (Springer 2021), with the 2017 text's in parentheses (see `BookConcordance.md`); results new in the 2021
edition are marked as such. Conventions: ep-groupoids, sc-smooth functors, orbit spaces $|X|$, the non-effective part
$\mathbf X^T$, the reduced ep-groupoid and the properties (LUC), (ZHOU), (LR), (SLUC), (SLR) are those of Chapter 7; natural
transformations, the tangent functor and strong bundles over ep-groupoids those of Chapter 8. Compositions are written as in
the text, $g \circ f$; the Lean writes $f ≫ g$. This version covers §§10.1–10.5 and the proofs of Appendix §§10.6.1–10.6.2.
The findings cited are those of `Findings.md`, "Chapter 10".*

---

## 0. One point, many ep-groupoids

Take the integers with exactly one morphism between any two of them: the pair groupoid of $\mathbb Z$. Each object is
isomorphic to every other, in exactly one way, so its orbit space is a single point and no object has a nontrivial symmetry.
It is, for every purpose of polyfold theory, the same as the ep-groupoid with one object and one morphism. Yet the functor
$P$ from the pair groupoid to the point is not an isomorphism of ep-groupoids: it is not injective on objects, and no functor
back is an inverse. What $P$ is, is an *equivalence*: full and faithful (every morphism between images comes from exactly one
morphism), a homeomorphism on orbit spaces, and a local sc-diffeomorphism on objects ($\mathbb Z$ is discrete).

Equivalences arise constantly: covering an ep-groupoid by open sets and taking the disjoint union of the pieces gives a new
ep-groupoid, the refinement, with an equivalence to the old one that is again not injective on objects. A polyfold structure
on a space should therefore not be one ep-groupoid but a class of them up to equivalence, and the maps between polyfolds
should be functors with the equivalences inverted. The chapter does this in five steps: it studies equivalences and what they
preserve (§§1–2), builds the weak fibred product needed to compose "inverted" equivalences (§3), inverts them formally (§4),
repeats the first two steps for strong bundles (§5), and then the inversion (§6). Two steps of the text needed more than a
reading: the two-out-of-three property is argued only on the image of $F$ (§1), and a step of the hard direction of the
characterization of generalized isomorphisms, as we read it, already uses what it proves (§§4, 7).

## 1. Equivalences (pp. 461–467 (2017 pp. 333–339))

**Definition 10.1.1 (2017: 10.1) (equivalence).** An equivalence $F : X \to Y$ is an sc-smooth functor that is full and
faithful, induces a homeomorphism $|F| : |X| \to |Y|$, and is a local sc-diffeomorphism on objects. $E$ is their class.

Full and faithful mean that $\varphi \mapsto F(\varphi)$ maps the morphisms $x \to x'$ bijectively onto the morphisms $F(x)
\to F(x')$. An equivalence is essentially surjective: $|F|$ is onto, so every $y$ is the target of a morphism from some
$F(x)$. The identities are equivalences and composites of equivalences are equivalences (Findings, item 1). *Checked by
machine (V10.1):* `Polyfold.EpFunctor.IsEquivalence`, `Polyfold.EP.equivalences`,
`Polyfold.EpFunctor.IsEquivalence.exists_iso`, `Polyfold.EpFunctor.IsEquivalence.comp`,
`Polyfold.EpGroupoid.Examples.isEquivalence_pairToPoint`.

**Lemma 10.1.2 (2017: 10.1) (equivalences are categorical equivalences, locally diffeomorphic).** An sc-smooth functor is an
equivalence if and only if it is an equivalence of categories and a local sc-diffeomorphism on objects.

*Proof.* For a functor of groupoids, $|F|$ is injective when $F$ is full, since an isomorphism $F(x) \cong F(x')$ lifts to $x
\cong x'$, and surjective exactly when $F$ is essentially surjective; so an equivalence of categories gives a bijection
$|F|$. It is continuous by the universal property of the quotient topology, and open because the orbit maps are open
(Proposition 7.1.8 (2017: 7.1)) and $F$, a local sc-diffeomorphism, is open on objects. Conversely an equivalence is full,
faithful and essentially surjective. $\square$

The pair groupoid of $\mathbb Z$ over the point is an equivalence without a left inverse on objects: equivalences need not be
invertible. *Checked by machine (V10.2):* `Polyfold.EpFunctor.lemma_10_1_2`, `Polyfold.EpFunctor.isEquivalence_iff`,
`Polyfold.GroupoidFunctor.bijective_orbitMap_of_isEquivalence`, `Polyfold.EpFunctor.isOpenMap_orbitMap`,
`Polyfold.EpGroupoid.Examples.not_exists_leftInverse_pairToPoint`.

**Proposition 10.1.3 (2017: 10.1) (refinement along an open covering).** Let $(U_i)_{i \in \iota}$ be an open covering of the
objects of $X$. The pairs $(i, x)$ with $x \in U_i$ and the triples $(i, \varphi, j)$ with $s(\varphi) \in U_i$, $t(\varphi)
\in U_j$, with $s(i, \varphi, j) = (i, s(\varphi))$, $t(i, \varphi, j) = (j, t(\varphi))$ and $(j, \psi, k) \circ (i,
\varphi, j) = (i, \psi \circ \varphi, k)$, form an ep-groupoid $X_{\mathcal U}$, and $(i, x) \mapsto x$, $(i, \varphi, j)
\mapsto \varphi$ is an equivalence $X_{\mathcal U} \to X$.

*How this is read.* The text indexes the covering by its members and writes $(U, x)$; an index type is used, objects and
morphisms are open subsets of $\iota \times X$ and $(\iota \times \iota) \times \mathbf X$ with $\iota$ discrete, and the
object set of $X$ is assumed nonempty, as the open-subset M-polyfold structure of Part I needs. In the formula for the
functor the text prints $(U, \varphi, v)$; we read $(U, \varphi, V)$ (possible misprint) (Findings, item 2).

*Proof.* Source and target are those of $X$ on each sheet, hence local sc-diffeomorphisms, as are unit, inverse and
multiplication. For properness at $(i, x)$ choose a neighbourhood $V_0$ of $x$ with the properness property of $X$ and an
open $V(x) \ni x$ with closure in $U_i \cap V_0$: a sequence (an ultrafilter, in Lean) of morphisms starting in the closure
of $\{i\} \times V(x)$ has convergent images in $X$, and the target index is eventually constant, the sheets being clopen.
The functor is faithful since a morphism $(i, \varphi, j)$ is determined by its ends and $\varphi$, full because $\psi : x
\to x'$ lifts to $(i, \psi, j)$, essentially surjective because the $U_i$ cover; Lemma 10.1.2 applies. $\square$

For the covering $\{x > -1\}$, $\{x < 1\}$ of $\mathbb Z/2 \ltimes \mathbb R$ (with $-1$ acting by $x \mapsto -x$) the
functor is an equivalence that is not injective on objects. *Checked by machine (V10.3):*
`Polyfold.EpGroupoid.OpenCover.epGroupoid`, `Polyfold.EpGroupoid.OpenCover.exists_isProperMap`,
`Polyfold.EpGroupoid.OpenCover.proposition_10_1_3`, `Polyfold.EpGroupoid.Examples.isEquivalence_reflectionCover`,
`Polyfold.EpGroupoid.Examples.not_injective_reflectionCover_obj`.

**Definition 10.1.4 (2017: 10.2) (natural equivalence).** A natural transformation $\tau : F \to G$ between sc-smooth
functors $X \to Y$ is an sc-smooth map $\tau : X \to \mathbf Y$ with $\tau(x) : F(x) \to G(x)$ and $\tau(x') \circ F(\varphi)
= G(\varphi) \circ \tau(x)$ for $\varphi : x \to x'$; $F \simeq G$ if one exists.

This is Definition 8.1.13. $\simeq$ is an equivalence relation, and $F \simeq G$ implies $F \circ \Psi \simeq G \circ \Psi$
and $\Phi \circ F \simeq \Phi \circ G$ (Findings, item 3). *Checked by machine (V10.4):* `Polyfold.definition_10_1_4`,
`Polyfold.EpFunctor.naturallyEquivalent_equivalence`, `Polyfold.EpNatTrans.toNatIso`.

**Proposition 10.1.5 (2017: 10.2) (natural equivalence).** If $F \simeq G$, then $F$ is an equivalence if and only if $G$ is.

The text quotes this from the literature. *Proof.* Since $s \circ \tau = F$ and $s$, $F$ are local sc-diffeomorphisms, so is
$\tau$, and then $G = t \circ \tau$. The underlying functors are naturally isomorphic, so $G$ is an equivalence of categories
with $F$; Lemma 10.1.2. $\square$ (Findings, item 4). *Checked by machine (V10.5):* `Polyfold.EpFunctor.proposition_10_1_5`,
`Polyfold.EpNatTrans.isLocalScDiffeo_app`.

**Proposition 10.1.6 (2017: 10.3) (two out of three).** If $F : X \to Y$ and $\Phi \circ F : X \to Z$ are equivalences and
$\Phi : Y \to Z$ is sc-smooth, then $\Phi$ is an equivalence.

*Proof.* $\Phi$ is an equivalence of categories since $F$ and $\Phi \circ F$ are. At a point $F(x)$, $\Phi$ is a local
sc-diffeomorphism because $\Phi \circ F$ and $F$ are local sc-diffeomorphisms at $x$. The text stops here; a point $y$ need
not be $F(x)$. It receives a morphism $\sigma : F(x) \to y$, and the local sc-diffeomorphism property of a functor passes
along morphisms: near $\sigma$ a local inverse $\tau$ of $s$ gives $\Phi \circ t \circ \tau = t \circ \Phi \circ \tau$ near
$F(x)$, and $t$, $\Phi$ on morphisms and $\tau$ are local sc-diffeomorphisms. Lemma 10.1.2 applies. $\square$

The proof writes $|\Phi| : |X| \to |Y|$ for $|\Phi| : |Y| \to |Z|$ (possible misprint) (Findings, item 5). *Checked by
machine (V10.6):* `Polyfold.EpFunctor.proposition_10_1_6`, `Polyfold.EpFunctor.isLocalScDiffeoAt_obj_tgt`,
`Polyfold.MPolyfold.IsLocalScDiffeoAt.of_comp_right`.

**Theorem 10.1.7 (2017: 10.1) (the tangent of an equivalence).** If $F$ is an equivalence, so is $TF : TX \to TY$.

*Proof.* $TF$ is a local sc-diffeomorphism on objects, as the tangent of one. A tangent morphism is determined by its base
morphism and its source vector, so $TF$ is faithful with $F$. Given a morphism of $TY$ from $TF(x, a)$ to $TF(x', a')$ over
$\psi = F(\varphi)$, lift $\varphi$ to the tangent morphism with source $(x, a)$; its image has the right source, and the
right target because $TF$ is injective on the tangent fibre at $x'$: $TF$ is full. For $(y, b)$ and $\psi : F(x) \to y$, lift
$\psi^{-1}$ with source $(y, b)$; its target lies in $T_{F(x)}Y$, the image of $T_xX$. Lemma 10.1.2. $\square$

Fullness and faithfulness are left to the reader in the text (Findings, item 6). *Checked by machine (V10.7):*
`Polyfold.EpFunctor.theorem_10_1_7`, `Polyfold.EpFunctor.tangent`.

## 2. What equivalences preserve (pp. 467–477 (2017 pp. 339–342))

An equivalence identifies orbit spaces; the question of this section is which finer structure it carries along.

**Remark 10.1.8 (new in the 2021 edition) (orbit-preserving maps need not come from the group).** On a translation groupoid
an sc-smooth map $\beta$ with $|\beta(y)| = |y|$ need not be locally of the form $y \mapsto g * y$; Zhou's example is built
in Appendix §10.6.3 on a weighted Sobolev sc-retract. Not formalized (gap G.112; Findings, item 7).

**Proposition 10.1.9 (new in the 2021 edition) ((LR) under equivalences).** If $F : X \to Y$ is an equivalence, $X$ has the
local regularity property (Definition 7.4.19) if and only if $Y$ has. The proof carries $U(x)$ along $Q = \hat\psi \circ F$
for $\psi : F(x) \to y$; that $Q(U(x))$ has a natural representation, taken for granted, holds by restricting one at $y$. On
p. 469, $\sigma \mapsto \psi \circ \sigma \circ \psi^{-1}$ is printed with target $U(y)$; we read $G_y$ (possible misprint;
Findings, item 16). $\mathcal{EP}_{lreg}$ (p. 461) is not built (gap G.111). *Checked by machine (V10.62):*
`Polyfold.EpFunctor.proposition_10_1_9`, `Polyfold.EpFunctor.TransportChart.exists_naturalRep_push`.

**Proposition 10.1.10 (2017: 10.4) (natural families).** For equivalences $F, G : X \to Y$ with $|F| = |G|$ and $X$ with
(LR), every object has a neighbourhood with an sc-smooth family $\alpha(z) : F(z) \to G(z)$, and $|TF| = |TG|$. (LR) for one
of $X$, $Y$ suffices; the families are in general not natural (§4, Theorem 10.3.19) (Findings, item 16). *Checked by machine
(V10.63):* `Polyfold.EpFunctor.proposition_10_1_10_one`, `Polyfold.EpFunctor.proposition_10_1_10_two`.

**Remark 10.1.11 (2017: 10.1) (the family cannot be prescribed).** On $\mathbb Z/2 \ltimes \mathbb R^2$ with $-1$ acting by
$z \mapsto -z$, $F = \mathrm{id}$ and $G = -\mathrm{id}$ are equivalences with $|F| = |G|$. The family $\alpha(z) = (-1, z)$
is sc-smooth, but no family $\alpha(z) : z \to -z$ with $\alpha(0) = 1_0$ is even continuous at $0$.

*Proof.* For $z \ne 0$ the only morphism $z \to -z$ is $(-1, z)$, which does not tend to $1_0 = (1, 0)$. $\square$ The text
says "not sc-smooth"; continuity already fails, and the example has the family of Proposition 10.1.10 (1) (Findings, item 8).
*Checked by machine (V10.8):* `Polyfold.EpGroupoid.Examples.remark_10_1_11`,
`Polyfold.EpGroupoid.Examples.remark_10_1_11_family`, `Polyfold.EpGroupoid.Examples.remark_10_1_11_scSmooth`.

**Remark 10.1.12 (new in the 2021 edition) (isotropy groups).** For an equivalence $F$ and $\psi : F(x) \to y$, $g \mapsto
\psi \circ F(g) \circ \psi^{-1}$ is an isomorphism $G_x \to G_y$ mapping $T_x$ (acting trivially near $x$) onto $T_y$.

Bijectivity is fullness and faithfulness at $(x, x)$; $g$ acts trivially near $x$ iff $F(g)$ does near $F(x)$, $F$ being a
local sc-diffeomorphism on objects and morphisms; conjugation by $\psi$ carries $T_{F(x)}$ to $T_y$. The text prints $G_x \to
Y_y$; we read $G_x \to G_y$ (possible misprint) (Findings, item 9). *Checked by machine (V10.9):*
`Polyfold.EpFunctor.IsEquivalence.remark_10_1_12`, `Polyfold.EpFunctor.IsEquivalence.bijective_isotropyHom`,
`Polyfold.EpFunctor.isotropyHom_mem_trivialSet_iff`.

**Proposition 10.1.13 (new in the 2021 edition) (the reduced morphism spaces).** For an equivalence $F$, $F_R : \mathbf X^R
\to \mathbf Y^R$, $[\varphi] \mapsto [F(\varphi)]$, is well defined, continuous and open, and $\mathbf X^R$ is Hausdorff if
and only if $\mathbf Y^R$ is.

*Proof.* For a local sc-diffeomorphism on objects, $\mathbf X^T = F^{-1}(\mathbf Y^T) \cap \{s = t\}$ (Remark 10.1.12), so
$F_R$ is well defined; it is continuous, and open since $F$ is open on morphisms and the quotient maps are open. By Theorem
7.2.22, $\mathbf X^R$ is Hausdorff iff $\mathbf X^T$ is closed. If $\mathbf Y^T$ is closed, so is $\mathbf X^T$, a preimage
cut by a closed set. If $\mathbf X^T$ is closed and $\psi \in \mathrm{cl}(\mathbf Y^T)$ at $y$, take $\sigma : F(x) \to y$
and a local inverse $\tau$ of $t$ at $\sigma$; conjugating by $\tau$ moves morphisms of $\mathbf Y^T$ near $\psi$ to
morphisms near $\sigma^{-1} \circ \psi \circ \sigma$ at points $F(x')$, which come from $\mathbf X^T$; so $\sigma^{-1} \circ
\psi \circ \sigma \in F(\mathbf X^T)$ by closedness, and $\psi \in \mathbf Y^T$. $\square$

The text uses sequences; closures do the same job. The first part needs only that $F$ is a local sc-diffeomorphism on objects
(Findings, item 10). *Checked by machine (V10.10):* `Polyfold.EpFunctor.proposition_10_1_13`,
`Polyfold.EpFunctor.nonEffectivePart_eq`, `Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff`,
`Polyfold.EpGroupoid.theorem_7_2_22`.

**Proposition 10.1.14 (2017: 10.5) (the reduced functor).** If $F$ is an equivalence and $\mathbf X^R$, $\mathbf Y^R$ are
Hausdorff, $F_R$, equal to $F$ on objects, is an sc-smooth functor of the reduced ep-groupoids and an equivalence.

By Proposition 10.1.13 one Hausdorff hypothesis implies the other; both are kept, as in the text (Findings, item 11).
*Checked by machine (V10.11):* `Polyfold.EpFunctor.reduced`, `Polyfold.EpFunctor.proposition_10_1_14`.

**Example 10.1.15 (2017: 10.1) (a functor with no reduced map).** Let $\mathbb Z/4$ act on $\mathbb R$ with $1, 3$ acting by
$x \mapsto -x$ and $2$ trivially, and on $\mathbb R^2$ by quarter turns, and let $\Phi$ map everything to the origin. Then
$(2, x)$ acts trivially on $\mathbb R$ but $(2, 0)$ does not on $\mathbb R^2$, so $[(1, x)] = [(3, x)]$ in $\mathbf X^R$
while $[(1, 0)] \ne [(3, 0)]$ in $\mathbf Y^R$: no map of sets $f$ has $f([\varphi]) = [\Phi(\varphi)]$.

This is slightly more than the text's statement, which concerns maps of the reduced ep-groupoids (Findings, item 12).
*Checked by machine (V10.12):* `Polyfold.EpGroupoid.Examples.example_10_1_15`.

**Proposition 10.1.16 (new in the 2021 edition) ((LUC) under equivalences).** If $F : X \to Y$ is an equivalence, $X$ has the
local unique continuation property if and only if $Y$ has.

*Proof.* (LUC) is the closedness of $\mathbf X^T$ (Proposition 7.2.21, part of Theorem 7.2.22), which passes along
equivalences (Proposition 10.1.13). $\square$ The text cites Theorem 7.2.22 here and in Proposition 10.1.13; the citation is
to the theorem on p. 323 (Findings, item 10). *Checked by machine (V10.13):* `Polyfold.EpFunctor.proposition_10_1_16`,
`Polyfold.EpGroupoid.proposition_7_2_21`.

**Proposition 10.1.17 (new in the 2021 edition) ((ZHOU) under equivalences).** If $F$ is an equivalence, $X$ satisfies the
Zhou condition if and only if $Y$ does.

*Proof.* Smooth points correspond. If $Y$ satisfies (ZHOU) and $g \in G_x$ has $Tg = \mathrm{id}$ on $T_xX$, then $T(F(g))
\circ TF = TF \circ Tg$ and $TF$ maps $T_xX$ onto $T_{F(x)}Y$, so $T(F(g)) = \mathrm{id}$, $F(g) \in T_{F(x)}$, and $g \in
T_x$ by Remark 10.1.12. If $X$ does and $k \in G'_y$ has $Tk = \mathrm{id}$, conjugate by $\psi : F(x) \to y$ to $k' \in
G'_{F(x)}$ with $Tk' = \mathrm{id}$, write $k' = F(g)$; $TF$ is injective on $T_xX$, so $Tg = \mathrm{id}$, $g \in T_x$, and
$k \in T_y$. $\square$

The text argues with natural representations instead, and in (b) writes $U(F(y))$ and "$x \in U(x)$" for $U(F(x))$ and $a \in
U(x)$ (possible misprints) (Findings, item 13). *Checked by machine (V10.14):* `Polyfold.EpFunctor.proposition_10_1_17`,
`Polyfold.EpFunctor.tangentMor_mor`.

**Proposition 10.1.18 (new in the 2021 edition) ((SLUC) under equivalences).** If $F$ is an equivalence, $X$ satisfies (SLUC)
if and only if $Y$ does.

*Proof.* The restriction $F^1 : X^1 \to Y^1$ to level 1 is an equivalence, so by induction every $F^i : X^i \to Y^i$ is, and
Proposition 10.1.16 applies at each level. $\square$ The proof cites Proposition 10.1.9 at the last step; we read Proposition
10.1.16 (possible misprint) (Findings, item 14). *Checked by machine (V10.15):* `Polyfold.EP.proposition_10_1_18`,
`Polyfold.EP.exists_isEquivalence_lift`.

**Proposition 10.1.19 (new in the 2021 edition) ((SLR) under equivalences).** If $F$ is an equivalence, $X$ satisfies (SLR)
if and only if $Y$ does.

The same induction reduces it to Proposition 10.1.9 at each level (Findings, items 15, 16). *Checked by machine (V10.16):*
`Polyfold.EP.proposition_10_1_19`, `Polyfold.EP.isSLR_iff_of_isLR_iff`.

## 3. The weak fibred product (pp. 477–483 (2017 pp. 342–347))

To invert an equivalence $G : B \to Y$ and compose it with a functor $\Phi : A \to Y$ one needs a common source mapping to
$A$ and $B$, with $\Phi$ and $G$ agreeing up to a morphism of $Y$.

**Definition 10.2.1 (2017: 10.3) (weak fibred product).** For sc-smooth $F : X \to Y$, $G : Z \to Y$, $X \times_Y Z$ has
objects $(x, \phi, z)$ with $\phi : F(x) \to G(z)$ and morphisms $(h, \phi, k)$ with $\phi : F(s(h)) \to G(s(k))$; $s(h,
\phi, k) = (s(h), \phi, s(k))$, $t(h, \phi, k) = (t(h), G(k) \circ \phi \circ F(h)^{-1}, t(k))$, units $(1_x, \phi, 1_z)$,
inverses $(h^{-1}, G(k) \circ \phi \circ F(h)^{-1}, k^{-1})$ and $(h, \phi', k) \circ (h', \phi, k') = (h \circ h', \phi, k
\circ k')$.

The text writes the inverse as $\iota(h, \psi, k)$ with $\phi$ on the right; we read $\psi = \phi$ (possible misprint). The
groupoid laws come from the conjugation rule $G(k) \circ (G(k') \circ \phi \circ F(h')^{-1}) \circ F(h)^{-1} = G(k \circ k')
\circ \phi \circ F(h \circ h')^{-1}$ (Findings, item 20). *Checked by machine (V10.17):*
`Polyfold.WeakFibredProduct.groupoid`, `Polyfold.WeakFibredProduct.conj`, `Polyfold.WeakFibredProduct.conj_comp`.

**Theorem 10.2.2 (2017: 10.2) (the weak fibred product is an ep-groupoid).** If $F$ is an equivalence and $G$ is sc-smooth,
$X \times_Y Z$ is an ep-groupoid, the projection $\pi_Z$ is an equivalence, $F \circ \pi_X \simeq G \circ \pi_Z$, the
degeneracy index is $d(x, \phi, z) = d_Z(z)$, and $X \times_Y Z$ is tame, or has a paracompact orbit space, when $Z$ is.
Symmetrically if $G$ is an equivalence, with $d = d_X(x)$; if both are, $d_X(x) = d(x, \phi, z) = d_Z(z)$.

*How this is read.* The text gives the objects and morphisms the structures of sub-M-polyfolds of $X \times \mathbf Y \times
Z$ and $\mathbf X \times \mathbf Y \times \mathbf Z$. The formal structure is built in two steps from Part I's fibred
products, $X \,{}_F\!\times_s (\mathbf Y \,{}_t\!\times_G Z)$ and its analogue on morphisms, each a fibred product of an
sc-smooth map with a local sc-diffeomorphism (Proposition 2.5.20). That these structures agree with ones induced directly
from the triple products is not formalized and not needed (gap G.116). The construction uses of $F$ only that it is a local
sc-diffeomorphism on objects; $G$ would do as well (Findings, item 21).

*Proof.* With $F$ a local sc-diffeomorphism on objects, the projections $(x, \phi, z) \mapsto z$ and $(h, \phi, k) \mapsto k$
are local sc-diffeomorphisms ((10.9), (10.10)), and $\pi_Z \circ s = s_Z \circ \pi_{\mathbf Z}$, $\pi_Z \circ t = t_Z \circ
\pi_{\mathbf Z}$ make $s$ and $t$ local sc-diffeomorphisms. Unit, inverse and multiplication have as entries multiplications
of $X$ and $Z$ and projections, so they are sc-smooth. Properness: for $(x, \phi, z)$ take $U \ni x$, $V \ni z$ with the
properness property in $X$ and $Z$; for morphisms $(h_n, \phi_n, k_n)$ starting in the closure of $\{x' \in U, z' \in V\}$
with convergent targets, subsequences of $h_n$ and then $k_n$ converge, and $\phi_n = G(k_n)^{-1} \circ (G(k_n) \circ \phi_n
\circ F(h_n)^{-1}) \circ F(h_n)$ converges by continuity. The text writes "$t : s^{-1}(U) \to X$ proper"; Definition 7.1.3
(3) asks it on $s^{-1}(\mathrm{cl}\,U)$, which is the reading, and no hypothesis on $F$ or $G$ is needed (Findings, item 22).

The natural transformation is $\sigma(x, \phi, z) = \phi$. For $F$ an equivalence, $\pi_Z$ is faithful because a morphism
over $k$ is determined by $F(h)$; full because for $k : z \to z'$ between $(x, \phi, z)$ and $(x', \phi', z')$ the morphism
$\phi'^{-1} \circ G(k) \circ \phi : F(x) \to F(x')$ is $F(h_0)$ and $(h_0, \phi, k)$ lies over $k$; and essentially
surjective because $G(z)$ receives a morphism from some $F(x)$. The text prints the composite as $\phi' \circ G(k) \circ
\phi^{-1}$, which does not compose; we read $\phi'^{-1} \circ G(k) \circ \phi$ (possible misprint). An equivalence preserves
the degeneracy index and pulls back tameness and the paracompactness of the orbit space. $\square$

For $G$ an equivalence the text states only that $\pi_X$ is an equivalence and the degeneracy index; the natural equivalence
and the transfer of tameness and paracompactness are added (Findings, items 23, 24). *Checked by machine (V10.18–V10.20):*
`Polyfold.WeakFibredProduct.Admissible`, `Polyfold.WeakFibredProduct.epGroupoid`,
`Polyfold.WeakFibredProduct.exists_isProperMap`, `Polyfold.WeakFibredProduct.theorem_10_2_2`,
`Polyfold.WeakFibredProduct.theorem_10_2_2_right`, `Polyfold.WeakFibredProduct.theorem_10_2_2_both`,
`Polyfold.WeakFibredProduct.Examples.theorem_10_2_2_pairToPoint`.

**Remark 10.2.3 (2017: 10.2) (two equivalences).** If $F$ and $G$ are both equivalences, both projections of $X \times_Y Z$
are equivalences and $\tau(x, \phi, z) = \phi$ is a natural transformation $F \circ \pi_X \to G \circ \pi_Z$. For
$\mathrm{id}$ and $-\mathrm{id}$ of $\mathbb Z/2 \ltimes \mathbb R^2$ the weak fibred product is a witness. The remark's
closing sentences on smaller models have no formal content (Findings, item 25). *Checked by machine (V10.21):*
`Polyfold.WeakFibredProduct.remark_10_2_3`, `Polyfold.WeakFibredProduct.Examples.remark_10_2_3_negFunctor`.

## 4. Localization at the equivalences (pp. 483–495 (2017 pp. 347–356))

The class $E$ has three properties (p. 483): (E1) isomorphisms of $\mathcal{EP}$ are equivalences, (E2) composites of
equivalences are equivalences, (E3) a functor naturally equivalent to an equivalence is one (Proposition 10.1.5). *Checked by
machine (V10.32):* `Polyfold.EPLocalization.isEquivalence_of_isIso`, `Polyfold.EpFunctor.IsEquivalence.comp`,
`Polyfold.EpFunctor.proposition_10_1_5`.

A map from $X$ to $Y$ "with an equivalence inverted" is a diagram $d : X \xleftarrow{F} A \xrightarrow{\Phi} Y$ with $F$ an
equivalence, to be thought of as $\Phi \circ F^{-1}$. In Lean a diagram contains $A$ as an object of $\mathcal{EP}$, so
diagrams live one universe up, and the classes of diagrams below are sets of that universe (Findings, item 30).

**Definition 10.3.1 (2017: 10.4) (refinement).** $d' : X \xleftarrow{F'} A' \xrightarrow{\Phi'} Y$ is a refinement of $d$ if
there is an equivalence $H : A' \to A$ with $F \circ H \simeq F'$ and $\Phi \circ H \simeq \Phi'$. Examples: $X \xleftarrow{F
\circ H} A' \xrightarrow{\Phi \circ H} Y$ for an equivalence $H$, and $X \xleftarrow{G} A \xrightarrow{\Psi} Y$ with $G
\simeq F$, $\Psi \simeq \Phi$. *Checked by machine (V10.33):* `Polyfold.EPLocalization.Diagram`,
`Polyfold.EPLocalization.Diagram.IsRefinement`, `Polyfold.EPLocalization.Diagram.isRefinement_precomp`,
`Polyfold.EPLocalization.Diagram.isRefinement_of_naturallyEquivalent`.

**Lemma 10.3.2 (2017: 10.3) (refinements compose).** A refinement of a refinement of $d$ is a refinement of $d$, by the
composite of the two equivalences. *Checked by machine (V10.34):* `Polyfold.EPLocalization.Diagram.lemma_10_3_2`.

**Definition 10.3.3 (2017: 10.5) (common refinement).** A common refinement of $(d, d')$ is a diagram refining both. *Checked
by machine (V10.35):* `Polyfold.EPLocalization.Diagram.IsCommonRefinement`.

**Lemma 10.3.4 (2017: 10.4) (transitivity).** If $(d, d')$ and $(d', d'')$ have common refinements, so has $(d, d'')$.

*Proof.* Let $W$ refine $d$ by $H$ and $d'$ by $H'$, and $W'$ refine $d'$ by $K$ and $d''$ by $K'$. $H'$ and $K$ are
equivalences into $A'$, so $W \times_{A'} W'$ is an ep-groupoid with equivalences $\pi_W$, $\pi_{W'}$ (Theorem 10.2.2), and
the diagram (10.11) over it refines $d$ by $H \circ \pi_W$ and $d''$ by $K' \circ \pi_{W'}$; the second uses $H' \circ \pi_W
\simeq K \circ \pi_{W'}$, the natural transformation of the weak fibred product. $\square$ *Checked by machine (V10.36):*
`Polyfold.EPLocalization.Diagram.lemma_10_3_4`.

**Definition 10.3.5 (2017: 10.6) (equivalent diagrams).** Two diagrams are equivalent if they have a common refinement. By
Lemma 10.3.4 this is an equivalence relation, and $[d]$ denotes the class. The diagram $\mathrm{pt} \xleftarrow{P} \mathbb
Z\text{-pair} \xrightarrow{P} \mathrm{pt}$ is equivalent to $\mathrm{pt} \xleftarrow{1} \mathrm{pt} \xrightarrow{1}
\mathrm{pt}$, through the refinement $P$, which is not an isomorphism (Findings, item 31). *Checked by machine (V10.37):*
`Polyfold.EPLocalization.Diagram.Equiv`, `Polyfold.EPLocalization.Diagram.setoid`,
`Polyfold.EPLocalization.Examples.equiv_pairToPoint_id`.

**Lemma 10.3.6 (2017: 10.5) (the orbit map).** If $d'$ refines $d$, $|\Phi| \circ |F|^{-1} = |\Phi'| \circ |F'|^{-1}$.

*Proof.* Naturally equivalent functors induce the same map of orbit spaces, so $|F'| = |F| \circ |H|$ and $|\Phi'| = |\Phi|
\circ |H|$, and $|H|$ cancels. $\square$ *Checked by machine (V10.38):* `Polyfold.EPLocalization.Diagram.lemma_10_3_6`,
`Polyfold.EpFunctor.NaturallyEquivalent.orbitMap_eq`.

**Definition 10.3.7 (2017: 10.7) (the map of a class).** $|[d]| = |\Phi| \circ |F|^{-1} : |X| \to |Y|$, for any
representative; it is continuous, and a homeomorphism if $\Phi$ is an equivalence too (Findings, item 32). *Checked by
machine (V10.39):* `Polyfold.EPLocalization.Diagram.orbitMapQ`, `Polyfold.EPLocalization.Diagram.isHomeomorph_orbitMap`.

**Theorem 10.3.8 (2017: 10.3) (composition of classes).** For $d : X \xleftarrow{F} A \xrightarrow{\Phi} Y$ and $e : Y
\xleftarrow{G} B \xrightarrow{\Psi} Z$, the class of $X \xleftarrow{F \circ \pi_A} A \times_Y B \xrightarrow{\Psi \circ
\pi_B} Z$ depends only on $[d]$ and $[e]$ and defines $[e] \circ [d]$. This composition is associative, with units $[1_X] =
[X \xleftarrow{1} X \xrightarrow{1} X]$.

The weak fibred product is that of $\Phi$ and $G$, an ep-groupoid because $G$ is an equivalence, and $\pi_A$ is an
equivalence. The proof, in Appendix §10.6.1, is retold in §7 (Findings, item 33). *Checked by machine (V10.40):*
`Polyfold.EPLocalization.Diagram.comp`, `Polyfold.EPLocalization.Diagram.theorem_10_3_8`.

**Definition 10.3.9 (2017: 10.8) (generalized maps).** A generalized map $X \to Y$ is a class $[d]$; it is a generalized
isomorphism if some generalized map $g : Y \to X$ has $g \circ [d] = [1_X]$ and $[d] \circ g = [1_Y]$ (Findings, item 34).
*Checked by machine (V10.41):* `Polyfold.EPLocalization.EPLoc.IsGeneralizedIso`,
`Polyfold.EPLocalization.EPLoc.isGeneralizedIso_iff_isIso`.

**Theorem 10.3.10 (2017: 10.4) (generalized isomorphisms).** $[X \xleftarrow{F} A \xrightarrow{\Phi} Y]$ is a generalized
isomorphism if and only if $\Phi$ is an equivalence, and then its inverse is $[Y \xleftarrow{\Phi} A \xrightarrow{F} X]$.

The proof, in Appendix §10.6.2, is retold in §7. *Checked by machine (V10.42):*
`Polyfold.EPLocalization.EPLoc.theorem_10_3_10`, `Polyfold.EPLocalization.EPLoc.inv_homMk`.

**Proposition 10.3.11 (2017: 10.6) (orbit maps compose).** For generalized maps $f$, $g$, $|g \circ f| = |g| \circ |f|$.

*Proof.* An object $(a, \phi, b)$ of $A \times_Y B$ has $\phi : \Phi(a) \to G(b)$, so $|\Phi(a)| = |G(b)|$; hence $|\Psi
\circ \pi_B| \circ |F \circ \pi_A|^{-1} = |\Psi| \circ |G|^{-1} \circ |\Phi| \circ |F|^{-1}$. $\square$ *Checked by machine
(V10.43):* `Polyfold.EPLocalization.EPLoc.proposition_10_3_11`, `Polyfold.EPLocalization.Diagram.orbitMap_comp`.

**Definition 10.3.12 (2017: 10.9) (the category $\mathcal{EP}(E^{-1})$).** Its objects are the ep-groupoids, its morphisms
the generalized maps, composed by Theorem 10.3.8.

In Lean the objects are a copy of those of $\mathcal{EP}$, and $\mathcal{EP}(E^{-1})$ is a large category like $\mathcal{EP}$
(Findings, item 35). *Checked by machine (V10.44):* `Polyfold.EPLocalization.EPLoc`,
`Polyfold.EPLocalization.EPLoc.homMk_eq_homMk_iff`.

**Remark 10.3.13 (new in the 2021 edition) (ep-groupoids as atlases).** An ep-groupoid $X$ can be viewed as an atlas for a
structure on $|X|$. No formal content (Findings, item 37).

**Theorem 10.3.14 (2017: 10.5) (the localization functor).** $i(X) = X$, $i(\Phi) = [X \xleftarrow{1} X \xrightarrow{\Phi}
Y]$ is a functor $\mathcal{EP} \to \mathcal{EP}(E^{-1})$, and for an equivalence $F : X \to Y$, $i(F)$ is invertible with
inverse $[Y \xleftarrow{F} X \xrightarrow{1} X]$.

*Proof.* The composite of $d_\Phi$ and $d_\Psi$ is $X \xleftarrow{\pi_X} X \times_Y Y \xrightarrow{\Psi \circ \pi_Y} Z$
(10.13), and $\Phi \circ \pi_X \simeq \pi_Y$ (Theorem 10.2.2), so (10.13) refines $d_{\Psi \circ \Phi}$ by $\pi_X$. Inverses
come from Theorem 10.3.10 with the legs $1$ and $F$. $\square$

The text says that $d_{\Psi \circ \Phi}$ refines (10.13); with Definition 10.3.1 as stated, where the refining equivalence
goes out of the refinement, the refinement is the other way round, and the equality of classes is the same. Every generalized
map is $i(\Phi) \circ i(F)^{-1}$, and $i$ inverts $E$ in the sense of Mathlib. The pair groupoid of $\mathbb Z$ over the
point is not an isomorphism of $\mathcal{EP}$, but becomes one in $\mathcal{EP}(E^{-1})$. The universal property of the
localization, mentioned on p. 483, is not formalized: it would need that every functor inverting $E$ identifies naturally
equivalent functors, through a cylinder ep-groupoid the project does not have (gap G.117; Findings, item 36). *Checked by
machine (V10.45):* `Polyfold.EPLocalization.EPLoc.theorem_10_3_14`,
`Polyfold.EPLocalization.EPLoc.isInvertedBy_localizationFunctor`, `Polyfold.EPLocalization.EPLoc.homMk_eq`,
`Polyfold.EPLocalization.Examples.isGeneralizedIso_pairToPoint`.

**Theorem 10.3.15 (2017: 10.6) (orbit spaces).** $X \mapsto |X|$, $[d] \mapsto |[d]|$ is a functor $\mathcal{EP}(E^{-1}) \to
\mathrm{TOP}$, by Proposition 10.3.11. *Checked by machine (V10.46):* `Polyfold.EPLocalization.EPLoc.orbitFunctor`,
`Polyfold.EPLocalization.EPLoc.theorem_10_3_15`.

A generalized isomorphism is represented by a diagram whose two legs are equivalences (Theorem 10.3.10), so every property
invariant under equivalences is invariant under generalized isomorphisms.

**Proposition 10.3.16 (new in the 2021 edition) ((LR) under generalized isomorphisms).** If $f : X \to Y$ is a generalized
isomorphism and one side has (LR), so has the other, by Proposition 10.1.9 for the two legs. *Checked by machine (V10.64):*
`Polyfold.EPLocalization.EPLoc.proposition_10_3_16`.

**Proposition 10.3.17 (new in the 2021 edition) ((LUC) under generalized isomorphisms).** If $f : X \to Y$ is a generalized
isomorphism, $X$ has (LUC) if and only if $Y$ has, by Proposition 10.1.16. *Checked by machine (V10.47):*
`Polyfold.EPLocalization.EPLoc.iff_of_isGeneralizedIso`, `Polyfold.EPLocalization.EPLoc.proposition_10_3_17`.

**Remark 10.3.18 (2017: 10.3) (spaces with ep-groupoid charts).** For a space $Z$, call pairs $(X, \beta)$, with $\beta : |X|
\to Z$ a homeomorphism, equivalent if a generalized isomorphism $f : X \to X'$ has $\beta' \circ |f| = \beta$. This is an
equivalence relation, by Proposition 10.3.11.

The metrizability of $Z$ assumed in the text plays no role in the relation. The pair groupoid of $\mathbb Z$ with $|P|$ and
the point with the identity are equivalent pairs. The text adds that $f$ is in general not unique, as the example of Remark
10.5.5 shows (§6; gap G.119, closed; Findings, items 39, 56). *Checked by machine (V10.48):*
`Polyfold.EPLocalization.OrbitChart.Rel`, `Polyfold.EPLocalization.OrbitChart.setoid`,
`Polyfold.EPLocalization.OrbitChart.rel_pairEP_pointEP`.

**Theorem 10.3.19 (2017: 10.7) (uniqueness under (LR)).** If one of $X$, $Y$ has (LR), generalized isomorphisms $f, f' : X
\to Y$ with $|f| = |f'|$ are equal. As we read it, this does not hold: $X = \mathbb Z/3 \times \mathbb R \rightrightarrows
\mathbb R$ with the trivial action has (LR), its orbits being points, and $[X \xleftarrow{1} X \xrightarrow{\mathrm{Inv}}
X]$, $[1_X]$ differ with the same orbit map (§6). The step on p. 494 takes the families $\alpha_a$ of Proposition 10.1.10 (1)
as a natural transformation; here $z \mapsto 1_z$ is one such family, and no natural $1 \to \mathrm{Inv}$ exists. The 2017
Theorem 10.7 lacks (LR) (gap G.120, settled; Findings, items 39, 58). *Checked by machine (V10.65):*
`Polyfold.LocalizationLRCounterexample.not_theorem_10_3_19`,
`Polyfold.LocalizationLRCounterexample.not_naturallyEquivalent_id_inv`.

*With an effective target $Y$ the theorem holds:* the families $\alpha_z$ are then unique and glue, so for $e = f' \circ
f^{-1} = [Y \xleftarrow{F} A \xrightarrow{\Phi} Y]$, $|\Phi| = |F|$ gives $F \simeq \Phi$ and $e = 1_Y$ (Findings, item 17).
*Checked by machine (V10.66):* `Polyfold.EPLocalization.EPLoc.theorem_10_3_19_of_isEffective`.

**Definition 10.3.20 (new in the 2021 edition) ($\mathcal{EP}_{reg}$).** $\mathcal{EP}_{reg}$ and
$\mathcal{EP}_{reg}(E^{-1})$ are the full subcategories on the ep-groupoids with (LR); the point is an object of both.
*Checked by machine (V10.49):* `Polyfold.EPLocalization.EPreg`, `Polyfold.EPLocalization.EPLocReg`,
`Polyfold.EPLocalization.Examples.pointReg`.

**Theorem 10.3.21 (new in the 2021 edition) (invariance under generalized isomorphisms).** For a generalized isomorphism $X
\to Y$, each of (LR), (LUC), (SLR), (SLUC), (ZHOU) holds for $X$ if and only if it holds for $Y$.

The proof, left to the reader in the text, applies Propositions 10.1.9 and 10.1.16–10.1.19 to the two legs (Findings, items
16, 38). *Checked by machine (V10.50):* `Polyfold.EPLocalization.EPLoc.theorem_10_3_21`,
`Polyfold.EPLocalization.EPLoc.theorem_10_3_21_all`.

## 5. Strong bundles and equivalences (pp. 495–504 (2017 pp. 357–364))

A strong bundle $P : W \to X$ over an ep-groupoid comes with an action $\mu$ of the morphisms of $X$ on the fibres (Chapter
8). Its sections that commute with the action, the section functors, are the objects to which Fredholm theory applies; the
question is how they move along equivalences.

**Definition 10.4.1 (2017: 10.10) (strong bundle equivalence).** A strong bundle equivalence $\Phi : (P, \mu) \to (P', \mu')$
is a strong bundle functor covering an equivalence $\phi : X \to X'$ such that (1) $\Phi$ is an equivalence at the levels
$[0]$ and $[1]$, and (2) near every object and every morphism, $\Phi$ is a strong bundle isomorphism covering $\phi$.

*How this is read.* $W[1]$ is not built as an ep-groupoid in the project. At level $[1]$ condition (1) is read as "$|\Phi|$
is a homeomorphism of $|W[1]|$, the quotient of $W_{0,1}$ with its level-1 topology"; fullness and faithfulness at $[1]$ are
those at $[0]$, and the local sc-diffeomorphism property at $[1]$ follows from (2). The fibre maps $W_x \to W'_{\phi(x)}$ are
then linear isomorphisms. Identities, composites and isomorphisms of strong bundles are strong bundle equivalences; so is the
projection $(-\mathrm{id})^*(\mathbb R^n \times \mathbb R^k) \to \mathbb R^n \times \mathbb R^k$, which covers $-\mathrm{id}$
(Findings, item 40). *Checked by machine (V10.22):* `Polyfold.EpStrongBundle.IsStrongBundleEquivalence`,
`Polyfold.EpStrongBundle.IsStrongBundleEquivalence.comp`, `Polyfold.EpStrongBundle.IsStrongBundleEquivalence.fiberEquiv`,
`Polyfold.StrongBundleEquivalenceExamples.isStrongBundleEquivalence_pullbackProj'`.

*Pull-back and push-forward (pp. 496–498).* For a section $f'$ of $P'$, $\Phi^*f'(x) = \Phi_x^{-1}(f'(\phi(x)))$. For a
section functor $f$ of $P$ and $x'$, choose $x$ and $\sigma : \phi(x) \to x'$ and set $\Phi_*f(x') = \mu'(\sigma,
\Phi(f(x)))$. The value does not depend on the choice (10.22): another $y$, $\sigma'$ gives $\sigma'^{-1} \circ \sigma =
\phi(\tau)$ by fullness, $f(y) = \mu(\tau, f(x))$ by functoriality, and $\Phi$ intertwines $\mu$ and $\mu'$. Both are section
functors and $\Phi^*\Phi_* = \mathrm{id}$, $\Phi_*\Phi^* = \mathrm{id}$. In Lean both are defined on all maps, by the zero of
the fibre where needed, with the choice made once (Findings, item 41). *Checked by machine (V10.23):*
`Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback`,
`Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward`,
`Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq`,
`Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_pushforward`.

**Proposition 10.4.2 (2017: 10.7) (pull-backs depend on $|\Phi|$).** If $\Phi$, $\Psi$ are strong bundle equivalences with
$|\Phi| = |\Psi|$, then $\Phi^*f' = \Psi^*f'$ for every section functor $f'$.

*Proof.* $|\Phi| = |\Psi|$ means that each $\Psi(w)$ is $\mu'(\sigma, \Phi(w))$ for some $\sigma$ (10.15). With $w =
\Psi^*f'(x)$, functoriality of $f'$ gives $\mu'(\sigma, \Phi(w)) = f'(\psi(x)) = \mu'(\sigma, \Phi(\Phi^*f'(x)))$, and
$\mu'(\sigma, \cdot)$ and $\Phi_x$ are injective. $\square$ No sc-smoothness is used. The text writes "$f' : W' \to X'$" for
$f' : X' \to W'$ (possible misprint) (Findings, item 42). *Checked by machine (V10.24):*
`Polyfold.EpStrongBundle.proposition_10_4_2`.

**Proposition 10.4.3 (2017: 10.8) (push-forwards depend on $|\Phi|$).** Under the same hypotheses $\Phi_*f = \Psi_*f$ for
every section functor $f$, by (10.15) and (10.22) (Findings, item 43). *Checked by machine (V10.25):*
`Polyfold.EpStrongBundle.proposition_10_4_3`.

**Proposition 10.4.4 (2017: 10.9) (functoriality).** $(\Psi \circ \Phi)^* = \Phi^* \circ \Psi^*$ and $(\Psi \circ \Phi)_* =
\Psi_* \circ \Phi_*$, the first on all sections, the second on all section functors (Findings, item 43). *Checked by machine
(V10.26):* `Polyfold.EpStrongBundle.proposition_10_4_4`.

**Theorem 10.4.5 (2017: 10.8) (section functors correspond).** $\Phi_*$ and $\Phi^*$ are mutually inverse bijections between
the sc-smooth section functors of $(P, \mu)$ and of $(P', \mu')$, depending only on $|\Phi|$, and they preserve
$\mathrm{sc}^+$-section functors and sc-Fredholm section functors.

*Proof of what is checked.* Near $x_0$, $\Phi^*f' = \Phi_U^{-1} \circ f' \circ \phi$ for the local strong bundle isomorphism
$\Phi_U$, which is sc-smooth, and $\mathrm{sc}^+$ with $f'$. The text calls the sc-smoothness of $\Phi_*f$ easily verified.
Near $x'_0$, with a local inverse $\tau$ of $t'$ at the chosen $\sigma_0 : \phi(y_0) \to x'_0$ and a local inverse $g_1$ of
$\phi$ at $y_0$, (10.22) gives $\Phi_*f = \mu' \circ (\tau, \Phi \circ f \circ g_1 \circ s' \circ \tau)$, a composite of
sc-smooth maps; at level $[1]$ the pair maps sc-smoothly into the level $[1]$ of the pull-back bundle, by its universal
property on an open set. $\square$

The sc-Fredholm part is not formalized: it needs the invariance of sc-Fredholm sections under local strong bundle
isomorphisms, of which Part I has only chart-level statements (gap G.121). The text's second display, for $\Gamma^+$, has
$\Phi^* : \Gamma(P', \mu') \to \Gamma(P, \mu)$; we read $\Gamma^+$ (possible misprint) (Findings, item 44). *Checked by
machine (V10.27):* `Polyfold.EpStrongBundle.theorem_10_4_5`,
`Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScSmoothSection_pushforward`,
`Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isScPlusSection_pushforward`.

**Proposition 10.4.6 (new in the 2021 edition) ((LR) for strong bundles).** (LR) of strong bundles is invariant under strong
bundle equivalences (proof left to the reader), and Proposition 10.4.7 (new in the 2021 edition) is the strong bundle version
of Proposition 10.1.10. Not formalized; only the ep-groupoid versions are (§2) (gap G.122; Findings, item 45).

**Definition 10.4.8 (2017: 10.11) (natural transformation of strong bundle functors).** For strong bundle functors $\Phi,
\Psi$ covering $\phi, \psi$, a natural transformation is a family $T(w) : \Phi(w) \to \Psi(w)$ of morphisms of $W'$, natural
in $w$, lying over a natural transformation $\tau : \phi \to \psi$. $T$ carries no smoothness, as in the text. *Checked by
machine (V10.28):* `Polyfold.EpStrongBundle.StrongBundleNatTrans`, `Polyfold.EpStrongBundle.StrongBundleNatEquiv`.

**Remark 10.4.9 (2017: 10.4) (the formula (10.23)).** $T(w) = (\tau(P(w)), \Phi(w))$ and $\Psi(w) = \mu'(\tau(P(w)),
\Phi(w))$; so $T$, and $\Psi$ among strong bundle functors, are determined by $\Phi$ and $\tau$, and $T$ is a strong bundle
map. The second line of (10.23) is printed with $\mu$; we read $\mu'$ (Findings, item 46). *Checked by machine (V10.29):*
`Polyfold.EpStrongBundle.StrongBundleNatTrans.T_eq`, `Polyfold.EpStrongBundle.StrongBundleNatTrans.obj_eq`,
`Polyfold.EpStrongBundle.StrongBundleNatTrans.unique_functor`.

**Definition 10.4.10 (2017: 10.12) (the same, as a strong bundle map).** A natural transformation is a strong bundle map $T :
W \to \mathbf X' \,{}_s\!\times_{P'} W'$ covering a natural transformation $\tau$, satisfying (10.23). For strong bundle
functors the two definitions agree, and naturally equivalent strong bundle functors induce the same map of orbit spaces
(Findings, item 46). *Checked by machine (V10.30):* `Polyfold.EpStrongBundle.IsStrongBundleNatTransMap`,
`Polyfold.EpStrongBundle.IsStrongBundleNatTransMap.toNatTrans`, `Polyfold.EpStrongBundle.StrongBundleNatEquiv.orbitMap_eq`.

**Definition 10.4.11 (2017: 10.13) (the category $\mathcal{SEP}$).** Strong bundles over ep-groupoids and strong bundle
functors form a category; the strong bundle equivalences form a class $F$ with the properties of $E$, mapped into $E$ by
forgetting the bundle. A morphism is the pair $(\phi, \Phi)$, since $\Phi$ determines $\phi$ only on the image of $P$
(Findings, item 47). *Checked by machine (V10.31):* `Polyfold.SEP`, `Polyfold.SEP.equivalences`,
`Polyfold.SEP.toEP_map_mem_equivalences`.

## 6. Localization of strong bundles (pp. 504–508 (2017 pp. 364–367))

For strong bundles $P : W \to X$, $P' : W' \to X'$, §4 is repeated with diagrams $D : W \xleftarrow{\Phi} W''
\xrightarrow{\Psi} W'$, $\Phi$ a strong bundle equivalence, $\Psi$ a strong bundle functor, refinements by strong bundle
equivalences $H$ with $\Phi \circ H \simeq \Phi'$, $\Psi \circ H \simeq \Psi'$, and classes $[D] : W \to W'$, the
*generalized strong bundle maps*. Transitivity (the strong bundle Lemma 10.3.4) needs a weak fibred product of strong
bundles, left to the reader: the pull-back $\pi_Z^*W''$ over $X \times_{X'} X''$, with $\Pi_Z$ an equivalence and $\Phi \circ
\Pi_X \simeq \Psi \circ \Pi_Z$ (the strong bundle Theorem 10.2.2; gap G.123, closed; Findings, items 18, 50). *Checked by
machine (V10.51, V10.68, V10.69):* `Polyfold.SBWeakFibredProduct.theorem_10_2_2`,
`Polyfold.SBLocalization.SDiagram.lemma_10_3_4`.

$[D]$ covers a generalized map $[d]$ of the bases, and $|[D]| = |\Psi| \circ |\Phi|^{-1}$ does not depend on the
representative. On orbit spaces the symbolic diagram (10.24) is the square $|P'| \circ |[D]| = |[d]| \circ |P|$, whose bottom
arrow is printed $|X| \to |X|$ (possible misprint for $|X'|$, in both editions; Findings, item 51). For $|[d]|(|x|) = |x'|$,
morphisms $a : \phi(x'') \to x$, $b : \psi(x'') \to x'$ give $\gamma : G_x \to G'_{x'}$, $\gamma(g) = b \circ \psi(k) \circ
b^{-1}$ where $\phi(k) = a^{-1} \circ g \circ a$ (2017: $a \circ g \circ a^{-1}$), an isomorphism if $\psi$ is an
equivalence; the germs $q$, $Q$ of (10.25) are not formalized (gap G.124; Findings, item 52). *Checked by machine
(V10.52–V10.54):* `Polyfold.SBLocalization.GenSBMap.orbitMap_square`, `Polyfold.EPLocalization.Diagram.isotropyHom`.

**Definition 10.5.1 (2017: 10.14) ($\mathcal{SEP}(F^{-1})$).** Strong bundles and generalized strong bundle maps; composites
live on pull-backs over weak fibred products and, as in Theorem 10.3.8, are well defined, associative and unital (squares
commute strictly by fibrewise injectivity): a category, with a functor from $\mathcal{SEP}$ (gap G.123, closed; Findings,
items 18, 53). *Checked by machine (V10.55, V10.70):* `Polyfold.SBLocalization.SEPLoc.category`.

**Definition 10.5.2 (2017: 10.15) (generalized strong bundle isomorphism).** A class represented with both legs strong bundle
equivalences, such as $[1, P']$ for $P' : (-\mathrm{id})^*W' \to W'$ of §5. *Checked by machine (V10.56):*
`Polyfold.SBLocalization.GenSBMap.IsGeneralizedIso`, `Polyfold.StrongBundleLocalizationExamples.isGeneralizedIso_negDiagram`.

**Remark 10.5.3 (new in the 2021 edition) (Theorem 10.3.10 again).** Its claim is read as: generalized strong bundle
isomorphisms are isomorphisms of $\mathcal{SEP}(F^{-1})$, inverted by the reversed diagram; proved. Of the converse only the
base half ($\psi$ an equivalence) is proved; $\Psi$ would need (C1), (C2) of §7 for strong bundles (gap G.123, open for this
half; Findings, items 19, 53). *Checked by machine (V10.57, V10.71):* `Polyfold.SBLocalization.SEPLoc.theorem_10_3_10`.

**Theorem 10.5.4 (2017: 10.9) (push-forward of sections).** With $[D]_*f = \Psi_*\Phi^*f$ and $[D]^*g = \Phi_*\Psi^*g$ for a
representative of two strong bundle equivalences, $[D]_* : \Gamma(P, \mu) \to \Gamma(P', \mu')$ is a well-defined bijection
with inverse $[D]^*$, also on $\Gamma^+$ and $\mathrm{Fred}$; $|[D]| = |[D']|$ gives $[D]_* = [D']_*$, $[D]^* = [D']^*$.

The text proves independence along a refinement $H$ by Propositions 10.4.2–10.4.4, $\Psi_*\Phi^*f = \Psi_*H_*H^*\Phi^*f =
\Psi'_*\Phi'^*f$; checked as printed. The Lean goes through orbits: a section functor is determined by the orbits of its
values (an isotropy element $\sigma \in G_x$ fixes $f(x)$, $f$ being a functor), and $|(D_*f)(x')| = |[D]|(|f(x)|)$, so $D_*$
depends only on $|D|$. The Fred part rests on that of Theorem 10.4.5 (gap G.125); "isomorphism" is read as a bijection
(Findings, items 54, 55). *Checked by machine (V10.58, V10.59):*
`Polyfold.SBLocalization.SDiagram.pushforward_eq_of_orbitMap_eq`, `Polyfold.SBLocalization.GenSBMap.theorem_10_5_4`.

**Remark 10.5.5 (new in the 2021 edition) (equal orbit maps, different classes).** $|[D]| = |[D']|$ does not in general give
$[D] = [D']$; the text gives no example. On $W = \mathbb R \times \mathbb R^k$ over $\mathbb Z/3 \times \mathbb R
\rightrightarrows \mathbb R$ (trivial action), $\mathrm{Inv}$ over $(g, x) \mapsto (g^{-1}, x)$ is the identity on objects,
so $|[\mathrm{Inv}]| = |[1_W]|$. Relating $g$ and $g'$ when $g = a \circ \phi(k) \circ a^{-1}$, $g' = b \circ \psi(k) \circ
b^{-1}$ gives an invariant of the classes; for $[1_W]$ the generator of $G_0 = \mathbb Z/3$ is related to itself, for
$[\mathrm{Inv}]$ only to its inverse. So already the base classes differ: the non-uniqueness of Remark 10.3.18 (gap G.119,
closed; Findings, item 56). *Checked by machine (V10.60):* `Polyfold.StrongBundleLocalizationExamples.remark_10_5_5`.

**Proposition 10.5.6 (new in the 2021 edition) (local regularity).** If one strong bundle has the local regularity property,
so has the other. Checked for every property invariant under strong bundle equivalences; for local regularity that is
Proposition 10.4.6, not formalized (gaps G.122, G.126); the text's "see Proposition 10.4.7" is read as 10.4.6 (possible
misprint; Findings, item 57). *Checked by machine (V10.61):* `Polyfold.SBLocalization.GenSBMap.iff_of_isGeneralizedIso`.

**Theorem 10.5.7 (2017: 10.10) (uniqueness).** With local regularity on both sides, $|[D]| = |[D']|$ implies $[D] = [D']$. As
we read it, this does not hold: the strong bundle of Remark 10.5.5 has the local regularity property, its orbits being
points, and $[\mathrm{Inv}] \neq [1_W]$ with the same orbit map; nor does the 2017 Theorem 10.10 (gap G.127, settled;
Findings, item 58). *Checked by machine (V10.67):* `Polyfold.LocalizationLRCounterexample.not_theorem_10_5_7`.

## 7. Appendix: the proofs of Theorems 10.3.8 and 10.3.10 (pp. 509–519 (2017 §§10.6.1–10.6.2))

*Proof of Theorem 10.3.8 (Appendix §10.6.1, pp. 509–515).* Let $d'$ refine $d$ by $H$ and $e'$ refine $e$ by $K$, with
natural transformations $\tau_{A'} : \Phi' \to \Phi \circ H$ and $\tau_{B'} : G' \to G \circ K$. Then

$$L(a', \phi, b') = (H(a'), \ \tau_{B'}(b') \circ \phi \circ \tau_{A'}(a')^{-1}, \ K(b'))$$

((10.28), (10.30)) is an sc-smooth functor $A' \times_Y B' \to A \times_Y B$, entry by entry. It is an equivalence: $\pi_A
\circ L = H \circ \pi_{A'}$ holds on the nose, $\pi_A$, $\pi_{A'}$ and $H$ are equivalences, and if $G$ and $G \circ L$ are
equivalences so is $L$ (the two-out-of-three rule on the other side from Proposition 10.1.6). The text instead verifies
directly that $L$ is full, faithful and a local sc-diffeomorphism. Then $(F \circ \pi_A) \circ L = F \circ H \circ \pi_{A'}
\simeq F' \circ \pi_{A'}$ and $(\Psi \circ \pi_B) \circ L \simeq \Psi' \circ \pi_{B'}$, so the composite of $d'$ and $e'$
refines that of $d$ and $e$; with common refinements on both sides the class depends only on the classes. For associativity
the text identifies $(A \times_Y A') \times_Z A''$ and $A \times_Y (A' \times_Z A'')$ as "the same space"; in Lean they are
different types, and the reassociation $((a, \phi, a'), \psi, a'') \mapsto (a, \phi, (a', \psi, a''))$ is a functor, an
equivalence by two out of three, and a refinement with identity natural transformations. For the units, $X \xleftarrow{\pi_X}
X \times_X A \xrightarrow{\Phi \circ \pi_A} Y$ refines $d$ by $\pi_A$, with $F \circ \pi_A \simeq \pi_X$ by $\tau(x, \phi, a)
= \phi$, and similarly on the other side. $\square$

Four places of the appendix are read with a correction (possible misprints): in the naturality of $\tau_{B'}$ the letter
$\tau_A$ appears for $\tau_{B'}$; "$(\Phi \circ \pi_B) \circ L \simeq \Psi' \circ \pi_{B'}$" is read with $\Psi \circ \pi_B$;
the unit law is announced as $[1_X] \circ [d] = [d]$, which in the text's order of composition is $[d] \circ [1_X] = [d]$;
and $\tau(a, \phi, a)$ is read $\tau(x, \phi, a)$ (Findings, item 60). *Checked by machine (V10.40):*
`Polyfold.EPLocalization.wfpMap`, `Polyfold.EPLocalization.isEquivalence_wfpMap`,
`Polyfold.EPLocalization.Diagram.IsRefinement.comp`, `Polyfold.EPLocalization.assocFunctor`,
`Polyfold.EPLocalization.isEquivalence_assocFunctor`, `Polyfold.EPLocalization.Diagram.isRefinement_id_comp`,
`Polyfold.EpFunctor.IsEquivalence.of_comp_left`.

*Proof of Theorem 10.3.10 (Appendix §10.6.2, pp. 515–519).* If $\Phi$ is an equivalence, the composite of $[d]$ and $[Y
\xleftarrow{\Phi} A \xrightarrow{F} X]$ is $X \xleftarrow{F \circ \pi_1} A \times_Y A \xrightarrow{F \circ \pi_2} X$; it is
refined by $X \xleftarrow{F} A \xrightarrow{F} X$ through the diagonal $a \mapsto (a, 1_{\Phi(a)}, a)$, an equivalence since
$\pi_1 \circ \Delta = 1_A$, and that diagram refines $1_X$ by $F$. The other composite is the same with the roles exchanged.

Conversely, let $[Y \xleftarrow{G} B \xrightarrow{\Psi} X]$ be an inverse. A diagram $X \leftarrow C \xrightarrow{\Theta} X$
equivalent to $1_X$ has $\Theta$ an equivalence, by Propositions 10.1.5 and 10.1.6 on a common refinement; so $\Psi \circ
\pi_B$ and $\Phi \circ \pi_{A'}$ are equivalences. (C1) Then $\Phi$ is full, faithful and essentially surjective, as in the
text, which in its injectivity argument writes $A \times_X B$ and $\mathrm{mor}_Y(\Psi(a), \Psi(a'))$ for $A \times_Y B$ and
$\mathrm{mor}_X(\Psi(b), \Psi(b'))$, and in the essential surjectivity "$x$" for "$y$" (possible misprints). (C2) $\Phi$ is a
local sc-diffeomorphism. The text defines $\Gamma(b') = (b', (s|U)^{-1}(b'), \ldots)$, read with $(s|U)^{-1}(\Psi(b'))$
(possible misprint), and then uses that $\Gamma'(b') = (F|W)^{-1} \circ t \circ (s|U)^{-1}(\Psi(b'))$ is a local
sc-diffeomorphism. As we read it this needs $\Psi$ to be a local sc-diffeomorphism, which is the other half of (C2), so the
step does not hold as we read it. The formal argument goes around it. A local inverse $\kappa$ of the equivalence $\Phi \circ
\pi_{A'}$ at $(b, \phi, a)$ gives a local sc-smooth right inverse $\pi_{A'} \circ \kappa$ of $\Phi$ through $a$. $\Phi$ is
injective near $a$: a local section $a' \mapsto (a', \phi(a'), b(a'))$ of the local sc-diffeomorphism $\pi_A : A \times_Y B
\to A$ turns $\Phi(a_1) = \Phi(a_2)$ into an equality for the locally injective $\Psi \circ \pi_B$, $s$ and $G$. An sc-smooth
map that is injective near $a$ and has a local sc-smooth right inverse through $a$ is a local sc-diffeomorphism at $a$. Lemma
10.1.2 concludes. $\square$ (Findings, item 61.) *Checked by machine (V10.42):*
`Polyfold.EPLocalization.Diagram.isRefinement_comp_symm`, `Polyfold.EPLocalization.Diagram.isEquivalence_Φ_of_equiv_id`,
`Polyfold.EPLocalization.isEquivalence_toFunctor_of_comp`, `Polyfold.EPLocalization.isLocalScDiffeo_obj_of_comp`,
`Polyfold.MPolyfold.isLocalScDiffeoAt_of_injOn`.

Appendix §10.6.3 (p. 519), the example behind Remark 10.1.8, is not formalized (gap G.112).

## 8. Witnesses: the hypotheses can hold

Every hypothesis taken is satisfied by an example, and every definition has a witness that is not an identity (Findings, item
70). The nonempty object set of Proposition 10.1.3 and the admissibility of the weak fibred product hold for the covering of
$\mathbb Z/2 \ltimes \mathbb R$ and for every equivalence (`Polyfold.WeakFibredProduct.Admissible.of_isEquivalence_left`);
the effectiveness added to Theorem 10.3.19 holds for the point. The equivalence $\mathbb Z\text{-pair} \to \mathrm{pt}$ is
the witness for equivalences, weak fibred products, equivalent diagrams, generalized isomorphisms that are not isomorphisms
of $\mathcal{EP}$ and equivalent pairs $(X, \beta)$; $\pm\mathrm{id}$ on $\mathbb Z/2 \ltimes \mathbb R^2$ for Remarks
10.1.11 and 10.2.3; the projection $(-\mathrm{id})^*(\mathbb R^n \times \mathbb R^k) \to \mathbb R^n \times \mathbb R^k$ for
strong bundle equivalences, push-forwards, natural equivalences of strong bundle functors and the class $F$ of
$\mathcal{SEP}$ (`Polyfold.StrongBundleEquivalenceExamples.negSEPHom_mem_equivalences`); the point for $\mathcal{EP}_{reg}$;
the same projection for the diagrams of strong bundles, their composites, inverses and push-forwards
(`Polyfold.StrongBundleLocalizationExamples.pushforward_foldDiagram`). §10.5 takes no hypothesis.

## 9. Summary of what was silently assumed, now made explicit

| Where | HWZ say | What is actually needed |
|---|---|---|
| p. 462, Prop. 10.1.3 (2017: 10.1) | the covering $\mathcal U$, $(U, x)$ | an index type; a nonempty object set for the open-subset structure |
| p. 464, Prop. 10.1.5 (2017: 10.2) | quoted from the literature | a five-line proof through Lemma 10.1.2 |
| p. 464, Prop. 10.1.6 (2017: 10.3) | local sc-diffeomorphism at $F(x)$ | the transport to every $y$ along $F(x) \to y$ |
| p. 465, Thm. 10.1.7 (2017: 10.1) | full and faithful "left to the reader" | tangent morphisms determined by base and source vector |
| p. 469, proof of Prop. 10.1.9 | $\sigma \mapsto \psi \circ \sigma \circ \psi^{-1}$ into $U(y)$ | into $G_y$ |
| p. 472, Prop. 10.1.13 | sequences | closures and a conjugation by a local inverse of $t$ |
| p. 476, Prop. 10.1.18 | "Proposition 10.1.9" | Proposition 10.1.16 |
| pp. 478–481, Thm. 10.2.2 (2017: 10.2) | $F$ an equivalence; sub-M-polyfolds of triple products | $F$ or $G$ a local sc-diffeomorphism on objects; iterated fibred products |
| p. 481, Thm. 10.2.2 | $t : s^{-1}(U) \to X$ proper | $t$ proper on $s^{-1}(\mathrm{cl}\,U)$, for any $F$, $G$ |
| p. 482, Thm. 10.2.2 | $\phi' \circ G(k) \circ \phi^{-1}$ | $\phi'^{-1} \circ G(k) \circ \phi$ |
| p. 491, Thm. 10.3.14 (2017: 10.5) | $d_{\Psi \circ \Phi}$ refines (10.13) | (10.13) refines $d_{\Psi \circ \Phi}$ |
| p. 492, Remark 10.3.18 (2017: 10.3) | $Z$ metrizable | not needed for the relation |
| p. 496, Def. 10.4.1 (2017: 10.10) | $\Phi : W[1] \to W'[1]$ an equivalence | a homeomorphism of $|W[1]|$; the rest from (2) |
| p. 498, (10.22) | sc-smoothness "easily verified" | a local formula with local inverses of $t'$ and $\phi$ |
| pp. 497–499, Props. 10.4.2–10.4.4 (2017: 10.7–10.9) | sc-smooth section functors | any section functors |
| p. 504, the classes of §10.5 | "following our earlier construction" | a weak fibred product of strong bundles, built as a pull-back |
| pp. 504–506, (10.24) and $|\mathscr D|$ | $|[d]| : |X| \to |X|$ | $|X| \to |X'|$ |
| p. 506, Remark 10.5.3 | "built into the previous definition" | generalized strong bundle isomorphisms are isomorphisms of $\mathcal{SEP}(F^{-1})$ |
| p. 508, Prop. 10.5.6 | "see Proposition 10.4.7" | Proposition 10.4.6 |
| pp. 512–514, proof of Thm. 10.3.8 | $L$ full, faithful, local sc-diffeo by hand | two out of three with $\pi_A \circ L = H \circ \pi_{A'}$ |
| p. 514, proof of Thm. 10.3.8 | "the same space" | a reassociation functor, an equivalence |
| pp. 518–519, (C2) in the proof of Thm. 10.3.10 | $\Gamma'$ a local sc-diffeomorphism | a local right inverse of $\Phi$ and local injectivity |

**Checked by machine.** The chapter is formalized in Lean 4 against Mathlib in the 23 files of `Polyfold/Chapter10/` imported
by the root module, from `Equivalence.lean` to `StrongBundleLocalizationCategory.lean` (not the `WIP_*` files). Formalized:
all definitions; Lemma 10.1.2, Propositions 10.1.3, 10.1.5, 10.1.6, 10.1.9, 10.1.10, 10.1.13, 10.1.14, 10.1.16–10.1.19,
Theorem 10.1.7, Remarks 10.1.11, 10.1.12, Example 10.1.15, Theorem 10.2.2 and Remark 10.2.3; (E1)–(E3), Lemmas 10.3.2,
10.3.4, 10.3.6, Theorems 10.3.8, 10.3.10, 10.3.14, 10.3.15, Propositions 10.3.11, 10.3.16, 10.3.17, Remark 10.3.18, Theorem
10.3.21, and Theorem 10.3.19 for an effective target, with the proofs of Appendix §§10.6.1–10.6.2; Propositions
10.4.2–10.4.4, Theorem 10.4.5 without its Fred part, and Remark 10.4.9; Remark 10.5.3 in one direction, Theorem 10.5.4
without its Fred part and Remark 10.5.5; several in stronger forms. Proposition 10.5.6 is reduced to Proposition 10.4.6. A
step of (C2) in the proof of Theorem 10.3.10 does not hold as we read it and is replaced; by the example of Remark 10.5.5,
Theorems 10.3.19 and 10.5.7, and the 2017 Theorems 10.7 and 10.10, do not hold as we read them. Not formalized:
$\mathcal{EP}_{lreg}$, Remark 10.1.8 and Appendix §10.6.3, the comparison with the triple-product structures in Theorem
10.2.2, the universal property of the localization, the Fred part of Theorem 10.4.5, Propositions 10.4.6 and 10.4.7, the
converse half of the strong bundle Theorem 10.3.10, $q$ and $Q$, the Fred part of Theorem 10.5.4 and Proposition 10.5.6 (gaps
G.111–G.127; eight are closed or settled since, G.123 but for one half). The statements are V10.1–V10.71 of
`Exposition/Verification.md`, compared in `Exposition/polyfold-beside-lean.html`, retold in `Exposition/ProofByProof.md`;
findings: `Exposition/Findings.md`, "Chapter 10", items 1–25, 30–39, 40–47, 50–59, 60–61, 70.
