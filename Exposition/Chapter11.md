# Chapter 11. Geometry up to equivalence: what survives a change of ep-groupoid (HWZ Part II, Chapter 11, pp. 521–566 (2017 pp. 375–416))

*Hofer–Wysocki–Zehnder, "Polyfold and Fredholm Theory", Part II, Chapter 11 (arXiv 1707.08941, pp. 375–416), rewritten for a
first-year graduate student who has read Chapters 7–10 and wants to know which of the structures built on one ep-groupoid can
be carried to an equivalent one, and why the result does not depend on the choices made. Every formalized statement is
proved; what is not formalized is marked. Where the Lean formalization found a gap or a shorter route, the text follows the
Lean. Statement numbers and printed pages are those of the book (Springer 2021), with the 2017 text's in parentheses (see
`BookConcordance.md`); results new in the 2021 edition are marked as such. Conventions: ep-groupoids, orbit spaces $|X|$, the
degeneracy index and tameness are those of Chapter 7; the tangent functor, strong bundles over ep-groupoids, auxiliary norms
and proper covering functors those of Chapter 8; branched ep⁺-subgroupoids those of Chapter 9; equivalences, the weak fibred
product $X \times_Y Z$, the category $\mathcal{EP}(E^{-1})$ with its generalized maps and generalized isomorphisms, and
generalized strong bundle isomorphisms those of Chapter 10. Compositions are written as in the text, $g \circ f$; the Lean
writes $f ≫ g$. This version covers §§11.1, 11.3, 11.5 and 11.6; §§11.2 and 11.4 are described but not formalized. The
findings cited are those of `Findings.md`, "Chapter 11".*

---

## 0. One point, two ep-groupoids

Let $\mathbb Z/2$ act on $\mathbb R$ by $x \mapsto -x$, and let $X = \mathbb Z/2 \ltimes \mathbb R$ be the translation
groupoid. The function $\Theta_0$ which is $1$ at the object $0$ and $0$ elsewhere is constant along morphisms, since $0$ is
fixed by the action; it is a branched ep⁺-subgroupoid of $X$ in the sense of Chapter 9, with one sheet, the point $\{0\}$, of
weight $1$. Its support in $|X| = [0, \infty)$ is the single point $|0|$.

Now cover $\mathbb R$ by the two open sets $\{x > -1\}$ and $\{x < 1\}$ and take the refinement $X_{\mathcal U}$ of
Proposition 10.1.3: its objects are the pairs $(i, x)$ with $x$ in the $i$-th set, so the object $0$ of $X$ appears twice, as
$(1, 0)$ and $(2, 0)$. The functor $F : X_{\mathcal U} \to X$ forgetting the index is an equivalence, and $X_{\mathcal U}$
describes the same orbifold point. The function $F^*\Theta_0 = \Theta_0 \circ F$ is $1$ at both copies of $0$. It is again a
branched ep⁺-subgroupoid, its support in $|X_{\mathcal U}|$ is again one point, and pushing it forward along $F$ gives back
$\Theta_0$.

Chapter 11 turns this example into a theory. A polyfold is a class of ep-groupoids up to the generalized isomorphisms of
Chapter 10, so a geometric notion on ep-groupoids is a notion on polyfolds only if generalized isomorphisms carry it to the
same kind of object, and in a way that does not depend on the representative. The chapter checks this for the tangent functor
and the degeneracy index (§1), faces (§2), sc-differential forms (§3, not formalized), branched ep⁺-subgroupoids (§4),
integration (§5, not formalized), auxiliary norms and sc⁺-multisections (§6), and proper covering functors (§7). Every
construction has the same shape: along an equivalence $F : X \to Y$, push an object on $X$ to $Y$ by choosing, for each $y$,
some $x$ and a morphism $F(x) \to y$; show the choice does not matter; then define the push-forward along a generalized
isomorphism $[X \xleftarrow{F} A \xrightarrow{\Phi} Y]$ as "pull back along $F$, push forward along $\Phi$", and show that
refining the diagram does not change it. Four places needed more than a reading: the tangent functor's compatibility with
composition (§1), the paracompactness of supports and the restriction of sheets in Theorem 11.3.3 (§4), the uniqueness of
dimensional decompositions on which Theorem 11.3.3 (6) relies (§4), and the boundary operations on which the oriented
boundaries of Theorem 11.3.9 depend (§4).

## 1. The tangent functor and the degeneracy index (pp. 521–523 (2017 pp. 375–377))

**Theorem 11.1.1 (2017: 11.1) (the tangent functor on $\mathcal{EP}(E^{-1})$).** The tangent functor $T : \mathcal{EP} \to
\mathcal{EP}$ induces a functor $T : \mathcal{EP}(E^{-1}) \to \mathcal{EP}(E^{-1})$ by $X \mapsto TX$ and $[X \xleftarrow{F}
A \xrightarrow{\Phi} Y] \mapsto [TX \xleftarrow{TF} TA \xrightarrow{T\Phi} TY]$; it extends $T$ on $\mathcal{EP}$ and maps
generalized isomorphisms to generalized isomorphisms.

*Proof.* $TF$ is an equivalence if $F$ is (Theorem 10.1.7), so the tangent of a diagram is a diagram. A refinement $H : d'
\to d$ comes with natural transformations $F' \to F \circ H$ and $\Phi' \to \Phi \circ H$; their tangents (Proposition
8.1.14) make $TH$ a refinement of $Td$ by $Td'$. So equivalent diagrams have equivalent tangents, and $T$ is defined on
classes. This is the text's argument; it leaves the rest to the reader. The identity diagram is mapped to one refining the
identity of $TX$. For composition, recall that $[e] \circ [d]$ is represented through the weak fibred product $A \times_Y B$
of the right leg $\Phi$ of $d$ and the left leg $G$ of $e$. Given functors $P : C \to A$, $Q : C \to B$ and a natural
transformation $\tau : \Phi \circ P \to G \circ Q$, the map $c \mapsto (P(c), \tau(c), Q(c))$ is a functor $C \to A \times_Y
B$ whose composites with the projections are $P$ and $Q$. Applied to $C = T(A \times_Y B)$, to $T\pi_A$, $T\pi_B$ and the
tangent of the transformation of $A \times_Y B$, it gives a functor $L : T(A \times_Y B) \to TA \times_{TY} TB$. Its
composite with the projection to $TA$ is $T\pi_A$; both $T\pi_A$ and that projection are equivalences, so $L$ is one by two
out of three, and it is a refinement of $Td$ composed with $Te$ by $T(e \circ d)$. Finally $T$ of the class of $i(\Phi) = [X
\xleftarrow{1} X \xrightarrow{\Phi} Y]$ is $i(T\Phi)$. $\square$

The functor is defined on the ep-groupoids of the universe in which Chapter 8's tangent functor takes its values (Findings,
item 1). *Checked by machine (V11.1):* `Polyfold.EPLocalization.EPLoc.theorem_11_1_1`,
`Polyfold.EPLocalization.EPLoc.tangentFunctor`, `Polyfold.EPLocalization.Diagram.IsRefinement.tangent`,
`Polyfold.EPLocalization.Diagram.isRefinement_tangent_comp`, `Polyfold.EPLocalization.wfpLift`,
`Polyfold.EPLocalization.EPLoc.isGeneralizedIso_tangent`.

**Proposition 11.1.2 (2017: 11.1) (the degeneracy index is invariant).** If $f : X \to Y$ is a generalized isomorphism and
$|f|(|x|) = |y|$, then $d_X(x_0) = d_Y(y_0)$ for every $x_0$ with $|x_0| = |x|$ and every $y_0$ with $|y_0| = |y|$. In
particular $d_{|Y|} \circ |f| = d_{|X|}$.

*Proof.* An equivalence is a local sc-diffeomorphism on objects, and local sc-diffeomorphisms preserve the degeneracy index,
so $d_Y(F(x)) = d_X(x)$; and $d_X$ is constant on orbits. A generalized isomorphism has a representative with both legs
equivalences (Theorem 10.3.10), and $|f| = |\Phi| \circ |F|^{-1}$. $\square$

The proof in the text refers to "Proposition 10.3.10" for the representative; the statement meant is Theorem 10.3.10
(possible misprint) (Findings, item 2). *Checked by machine (V11.2):* `Polyfold.EPLocalization.EPLoc.proposition_11_1_2`,
`Polyfold.EpFunctor.IsEquivalence.degIndexOrbit_orbitMap`, `Polyfold.EPLocalization.Diagram.degIndexOrbit_orbitMap`.

## 2. Faces (pp. 523–526 (2017 pp. 377–380))

Chapter 2 defined faces of a tame M-polyfold as closures of components of the set where the degeneracy index is $1$. On an
ep-groupoid the index $d_X$ is constant on orbits, so it descends to $d_{|X|}$ on $|X|$, and faces can be defined downstairs.

**Definition 11.1.3 (2017: 11.1) (faces).** Let $X$ be a tame ep-groupoid. A face of $|X|$ is the closure in $|X|$ of a
connected component of $\{z \in |X| \mid d_{|X|}(z) = 1\}$. For $\theta \subseteq |X|$, $X_\theta$ is the full subcategory on
the objects $x$ with $|x| \in \theta$; a face of $X$ is $X_\theta$ for a face $\theta$ of $|X|$. $X$ is face structured if
every $z \in |X|$ lies in exactly $d_{|X|}(z)$ faces of $|X|$, and weakly face structured if its object M-polyfold is face
structured.

*How this is read.* A face $X_\theta$ is recorded by its object set $\pi^{-1}(\theta)$, which is saturated, together with the
morphisms whose source lies in it (their targets lie in it too). The faces of $|X|$ are then literally Chapter 2's faces for
the index $d_{|X|}$ on the open set $|X|$, and face-structuredness is Chapter 2's condition for $|X|$; this lets every later
statement about faces be a statement about a homeomorphism of orbit spaces preserving an index. The number of faces through
$z$ is counted in $\mathbb N \cup \{\infty\}$, so that "exactly $d_{|X|}(z)$ faces" excludes infinitely many. The ep-groupoid
structure of $X_\theta$ belongs to Proposition 11.1.6 and is not formalized (Findings, item 3). *Checked by machine (V11.3):*
`Polyfold.EpGroupoid.IsOrbitFace`, `Polyfold.EpGroupoid.faceObj`, `Polyfold.EpGroupoid.IsEpFaceStructured`,
`Polyfold.EpGroupoid.IsWeaklyFaceStructured`, `Polyfold.EpGroupoid.isOrbitFace_iff_isFaceIn`,
`Polyfold.EpGroupoid.isEpFaceStructured_iff`.

**Example 11.1.4 (2017: 11.1) (a quadrant with a swap).** On $C = [0, \infty)^2$ the ep-groupoid with only identities is face
structured. With $\mathbb Z/2$ acting by $(a, b) \mapsto (b, a)$, $X = \mathbb Z/2 \ltimes C$ is weakly face structured but
not face structured.

*Proof.* With only identities, $|X| = C$ and the faces are the two coordinate half-axes. With the swap, the object M-polyfold
is still $C$, face structured. In $|X|$ the two open half-axes $\{a = 0 < b\}$ and $\{b = 0 < a\}$ become one, so $\{d_{|X|}
= 1\}$ is connected and $|X|$ has exactly one face, its closure. The corner $|0|$ has $d_{|X|}(|0|) = 2$ but lies in one face
only. $\square$

The text gives no reason for "not face structured"; the one above is the formal proof. The example is proved for $C = [0,
\infty)^2 \oplus W$ with any sc-Banach space $W$ (Findings, item 4). *Checked by machine (V11.4):*
`Polyfold.EpGroupoid.Examples.example_11_1_4`, `Polyfold.EpGroupoid.Examples.swapEpGroupoid`,
`Polyfold.EpGroupoid.Examples.setOf_degIndexOrbit_eq_one_swap`, `Polyfold.EpGroupoid.Examples.not_isEpFaceStructured_swap`.

**Remark 11.1.5 (2017: 11.1) (faces under equivalences).** An equivalence $\Phi : X \to Y$ induces a bijection $\theta
\mapsto |\Phi|(\theta)$ from the faces of $|X|$ to those of $|Y|$, with inverse $\theta' \mapsto |\Phi|^{-1}(\theta')$; on
faces of the ep-groupoids, $\Phi_*(X_\theta) = \mathrm{saturation}(\Phi(X_\theta)) = Y_{|\Phi|(\theta)}$ and
$\Phi^*(Y_{\theta'}) = \Phi^{-1}(Y_{\theta'})$. For a generalized isomorphism $[d] = [X \xleftarrow{\Phi} A
\xrightarrow{\Psi} Y]$ one sets $[d]_* = \Psi_* \circ \Phi^*$ and $[d]^* = \Phi_* \circ \Psi^*$; they are mutually inverse
bijections of faces.

*Proof.* The text quotes [56, Proposition 3.15] for the underlying fact: a homeomorphism $h$ between open sets with $d' \circ
h = d$ maps the faces for $d$ onto the faces for $d'$. Indeed $h$ maps $\{d = 1\}$ homeomorphically onto $\{d' = 1\}$, hence
components to components, and closures to closures. $|\Phi|$ is such a homeomorphism by Proposition 11.1.2, and so is $|[d]|
= |\Psi| \circ |\Phi|^{-1}$; the formulas for $\Phi_*$ and $\Phi^*$ say that the saturation of $\Phi(\pi^{-1}(\theta))$ is
$\pi^{-1}(|\Phi|(\theta))$. $\square$

The first paragraph of the remark, on ordered face structures, has no formal content (Findings, item 5). *Checked by machine
(V11.5):* `Polyfold.EPLocalization.EPLoc.remark_11_1_5`, `Polyfold.TameBoundary.isFaceIn_univ_image`,
`Polyfold.EpFunctor.IsEquivalence.bijOn_faces`, `Polyfold.EpFunctor.saturation_image_faceObj`,
`Polyfold.EPLocalization.EPLoc.faceMap_homMk`, `Polyfold.EPLocalization.EPLoc.bijOn_faceMap`.

**Proposition 11.1.6 (2017: 11.2) (faces of face structured ep-groupoids).** Let $X$ and $Y$ be tame face structured
ep-groupoids and $[d] : X \to Y$ a generalized isomorphism. The text states: the object and morphism sets of a face $F$ of
$X$ are sub-M-polyfolds with tame induced structures, $F$ is a tame face structured ep-groupoid, and the intersection of two
faces is a face of each; $[d]$ induces a bijection $[d]_*$ of faces, and for each face $F$ a generalized isomorphism $[d]_F :
F \to [d]_*F$ (11.1).

*What is proved.* For every generalized isomorphism, with no face structure assumed: $[d]_*$ is a bijection of the faces of
$|X|$ onto those of $|Y|$ with inverse $[d]^*$, $[d]_*(X_\theta) = Y_{|[d]|(\theta)}$, and $|[d]|$ restricts to a
homeomorphism of each face $\theta$ onto $[d]_*\theta$. These are the maps of orbit spaces of the generalized isomorphisms
$[d]_F$.

*What is not.* The structures on a face, which need the restriction of an ep-groupoid to a closed saturated sub-M-polyfold
and the identification of $X_\theta$ with a union of faces of the object M-polyfold; the intersection clause; and the
generalized isomorphisms $[d]_F$ themselves (gap G.128). Whether the intersection clause holds in the generality stated was
left open by the formalization; nothing is claimed either way (Findings, item 6). *Checked by machine (V11.6):*
`Polyfold.EPLocalization.EPLoc.proposition_11_1_6`, `Polyfold.EPLocalization.EPLoc.isOrbitFace_faceMap`,
`Polyfold.EPLocalization.EPLoc.faceComap_faceMap`.

**Remark 11.1.7 (2017: 11.2) (face structure is invariant).** If $f : X \to Y$ is a generalized isomorphism, then $X$ is tame
and face structured if and only if $Y$ is.

*Proof.* Face-structuredness is a property of $(|X|, d_{|X|})$ and is carried by the homeomorphism $|f|$ (Remark 11.1.5).
Tameness along an equivalence $F : X \to Y$: Chapter 10 shows that $X$ is tame if $Y$ is. For the converse take the weak
fibred product $X \times_Y Y$ of $F$ and $1_Y$. Its projection to $X$ is an equivalence, so $X \times_Y Y$ is tame by Chapter
10's direction; its projection to $Y$ is a local sc-diffeomorphism on objects, surjective because $F$ is essentially
surjective, and tameness, a local property, descends along it. $\square$

The forward direction of tameness was not in Chapter 10; the remark needs it (Findings, item 7). *Checked by machine
(V11.7):* `Polyfold.EPLocalization.EPLoc.remark_11_1_7`, `Polyfold.EpFunctor.IsEquivalence.isTame_of_isTame_left`,
`Polyfold.EpFunctor.IsEquivalence.isTame_iff`.

**Proposition 11.1.8 (2017: 11.3) (only $|f|$ matters).** If $f, g : X \to Y$ are generalized isomorphisms of tame face
structured ep-groupoids with $|f| = |g|$, then $f$ and $g$ induce the same bijection of faces, and the same maps $|F| \to
|f_*F|$ on every face.

*Proof.* The bijection is $\theta \mapsto |f|(\theta)$ and the map on a face is the restriction of $|f|$. $\square$

*How this is read.* The text's maps $|F| \to |f_*F|$ are those of the generalized isomorphisms of (11.1), which are not
constructed (G.128); they are read as the restrictions of $|f|$, which is what they are on orbit spaces (Findings, item 8).
*Checked by machine (V11.8):* `Polyfold.EPLocalization.EPLoc.proposition_11_1_8`.

## 3. Differential forms (pp. 526–535 (2017 pp. 380–389)), not formalized

§11.2 carries the sc-differential forms $\Omega^*_{ep,\infty}(X)$ of an ep-groupoid along equivalences and generalized maps.
Theorem 11.2.1 (2017: 11.2) states that $d \circ d = 0$; that a generalized map $f : X \to Y$ has a pull-back $f^*$ commuting
with $d$; that a generalized isomorphism $h$ has a push-forward $h_*$ commuting with $d$ and inverse to $h^*$; and that,
under the local regularity property, $|h| = |k|$ implies $h_* = k_*$ and $h^* = k^*$. The proof follows the pattern of §0.
Lemma 11.2.2 and Definition 11.2.3 (2017: Lemma 11.1, Definition 11.2) push a form along an equivalence $F$:
$(F_*\omega)_y(h_1, \ldots, h_k) = \omega_x(l_1, \ldots, l_k)$ for any $\psi : F(x) \to y$ and $h_j = T\psi(TF(x)l_j)$,
independently of the choices. Lemmas 11.2.4–11.2.6 (2017: 11.2–11.4) give the composition rules, the invariance under natural
equivalence and the invariance under refinement; Definition 11.2.7 (2017: 11.3) defines $[d]^* = F_* \circ G^*$ and $[d]_* =
G_* \circ F^*$; Propositions 11.2.8 and 11.2.9 (2017: 11.4, 11.5) show that, under the local regularity property, only the
orbit map matters, by the local families of Proposition 10.1.10.

None of this is formalized: sc-differential forms on ep-groupoids are not in the project (gaps G.74, G.80), and §11.2 is gap
G.129 (V11.9–V11.13; Findings, item 20). The same pattern for functors $\Theta$, in place of forms, is §4.

## 4. Branched ep⁺-subgroupoids (pp. 535–542 (2017 pp. 389–395))

**Definition 11.3.1 (2017: 11.4) (pull-back and push-forward of functors).** Let $F : X \to Y$ be an equivalence. For a
functor $\Theta' : Y \to \mathbb Q^+$, $F^*\Theta' = \Theta' \circ F$. For a functor $\Theta : X \to \mathbb Q^+$,
$(F_*\Theta)(y) = \Theta(x)$ for any $x$ with a morphism $F(x) \to y$.

*How this is read.* A functor $X \to \mathbb Q^+$ is a map on objects constant along morphisms. Both operations are defined
for every sc-smooth functor and every map on objects: $F_*\Theta(y)$ uses one chosen $x$ and morphism, and is $0$ if there is
none. For an equivalence there always is one, and the next lemma shows that the value does not depend on the choice. The text
writes the push-forward as a map $X' \to \mathbb Q^+$, in both editions; we read $Y \to \mathbb Q^+$ (possible misprint)
(Findings, item 30). *Checked by machine (V11.14):* `Polyfold.EpFunctor.pullbackTheta`,
`Polyfold.EpFunctor.pushforwardTheta`, `Polyfold.EpFunctor.pushforwardTheta_of_not_exists`.

**Lemma 11.3.2 (2017: 11.5) (push-forward along a full functor).** (1) If $F$ is full and $\Theta$ is a functor,
$F_*\Theta(y) = \Theta(x)$ for every $x$ with a morphism $F(x) \to y$, $F_*\Theta$ is a functor and $F^*F_*\Theta = \Theta$.
(2) If $F$ is essentially surjective and $\Theta'$ is a functor, $F_*F^*\Theta' = \Theta'$. (3) Naturally equivalent full
functors have the same push-forwards; naturally equivalent functors have the same pull-backs.

*Proof.* (1) For $\psi : F(x) \to y$ and $\psi' : F(x') \to y$, fullness lifts $\psi^{-1} \circ \psi' : F(x') \to F(x)$ to
some $\sigma : x' \to x$, and $\Theta(x') = \Theta(x)$ because $\Theta$ is a functor. A morphism $y \to y'$ composed with
$\psi$ is a morphism $F(x) \to y'$, so $F_*\Theta$ is constant along morphisms, and $F^*F_*\Theta(x) = \Theta(x)$ with the
choice $1_{F(x)}$. (2) $F_*F^*\Theta'(y) = \Theta'(F(x))$ for $F(x) \cong y$, which is $\Theta'(y)$. (3) If $\tau : F \to G$,
then $\tau(x) : F(x) \to G(x)$ and the two choices are related. $\square$

The text assumes equivalences throughout; the proof uses less, and the formal statements say so. Moreover $(G \circ F)^* =
F^* \circ G^*$ and, for full functors, $(G \circ F)_* = G_* \circ F_*$ (Findings, item 31). *Checked by machine (V11.15):*
`Polyfold.EpFunctor.pushforwardTheta_eq`, `Polyfold.EpFunctor.isFunctorial_pushforwardTheta`,
`Polyfold.EpFunctor.pullbackTheta_pushforwardTheta`, `Polyfold.EpFunctor.pushforwardTheta_pullbackTheta`,
`Polyfold.EpFunctor.pushforwardTheta_eq_of_naturallyEquivalent`, `Polyfold.EpFunctor.pushforwardTheta_comp`.

*Generalized maps (pp. 536–537).* For a diagram $d = [X \xleftarrow{F} A \xrightarrow{\Phi} Y]$ the text sets $d_*\Theta =
\Phi_*F^*\Theta$ and $d^*\Theta' = F_*\Phi^*\Theta'$, and checks that a refinement does not change them. So $f^*$ is defined
for every generalized map and $f_*$ for every generalized isomorphism, computed on any representative ($\Phi$ an equivalence
for $f_*$), and both map functors to functors. The text calls the composition rules "easily verified". They go through one
formula in the weak fibred product $X \times_Y Z$ of $F : X \to Y$ and $G : Z \to Y$: if $F$ is an equivalence,
$(\pi_Z)_*(\pi_X)^*\Theta = G^*F_*\Theta$, since both sides are $\Theta(x)$ at $z$ for any morphism $F(x) \to G(z)$. The
composite of two classes is represented through such a product (Theorem 10.3.8), and the formula gives $(g \circ f)^* = f^*
\circ g^*$ for all generalized maps and $(g \circ f)_* = g_* \circ f_*$, $(f^{-1})_* = f^*$ for generalized isomorphisms.
Nothing uses Theorem 10.3.19, which does not hold as we read it (Chapter 10) (Findings, item 32). *Checked by machine
(V11.16):* `Polyfold.EPLocalization.Diagram.pullTheta_eq_of_isRefinement`, `Polyfold.EPLocalization.EPLoc.pullTheta`,
`Polyfold.EPLocalization.EPLoc.pushTheta`, `Polyfold.WeakFibredProduct.pushforwardTheta_projRight_pullbackTheta`,
`Polyfold.EPLocalization.EPLoc.pullTheta_comp`, `Polyfold.EPLocalization.EPLoc.pushTheta_comp`,
`Polyfold.EPLocalization.EPLoc.pushTheta_inv`.

**Theorem 11.3.3 (2017: 11.3) (branched ep⁺-subgroupoids under generalized isomorphisms).** Let $f : X \to Y$ be a
generalized isomorphism. (1) If $\Theta$ is a branched ep⁺-subgroupoid of $X$, $f_*\Theta$ is one of $Y$. (2) If $\Theta'$ is
a branched ep⁺-subgroupoid of $Y$, $f^*\Theta'$ is one of $X$. $f_*$ and $f^*$ preserve (3) closedness, (4) compactness, (5)
being of orbifold type and of manifold type, and (6) dimensional decompositions: if $\Theta = \sum_k \Theta_k$ with
$\Theta_k$ a $k$-dimensional branched ep⁺-subgroupoid, then $f_*\Theta = \sum_k f_*\Theta_k$ is a dimensional decomposition
of $f_*\Theta$, and likewise for $f^*$.

*Proof.* On a representative with both legs equivalences, $f_* = \Phi_* F^*$ and $f^* = F_*\Phi^*$, so it suffices to treat
an equivalence $F : X \to Y$ and both $F^*$ and $F_*$.

*Step 1, supports.* $|\mathrm{supp}(F^*\Theta')| = |F|^{-1}(|\mathrm{supp}(\Theta')|)$, and $|\mathrm{supp}(F_*\Theta)| =
|F|(|\mathrm{supp}(\Theta)|)$. Since $|F|$ is a homeomorphism, paracompactness, closedness and compactness of the support are
transferred. 2021 Definition 9.1.2 (1) asks for the paracompactness of $|\mathrm{supp}(\Theta)|$; the text's proof does not
mention it, and the formal proof carries it along.

*Step 2, local branching structures.* A local branching structure of $\Theta$ at $x$ is an open $U \ni x$ with finitely many
submanifolds $M_i \subseteq U$ and weights $\sigma_i$ such that $\Theta = \sum_i \sigma_i 1_{M_i}$ on $U$. Given $y$ and
$\psi : F(x) \to y$, the map $\hat\psi \circ F$ (Chapter 10's transport chart: $F$ near $x$ followed by the local
sc-diffeomorphism $\hat\psi$ of $\psi$) is an sc-diffeomorphism from a neighbourhood $W$ of $x$ onto a neighbourhood of $y$,
with $F_*\Theta \circ \hat\psi \circ F = \Theta$ on $W$. It moves the structure at $x$ to one at $y$: the sheets $\hat\psi
F(M_i \cap W)$ with the same weights. The sheets must first be cut down to $W$, a step the text passes over, and they keep
their dimension because the dimension of a submanifold at a point is invariant under sc-diffeomorphisms. For $F^*\Theta'$ the
same with $F$ near $x$ and a structure of $\Theta'$ at $F(x)$. This proves (1) and (2).

*Step 3, type and dimension.* Orbifold type is a property of the local branching structures. For manifold type, two morphisms
$y \to y'$ are compared through the faithfulness of $F$. In that step the text writes $\psi \circ \varphi' \circ \psi^{-1} :
F(x) \to F(x)$ for $\psi : F(x) \to y$ and $\varphi' : y \to y$; we read $\psi^{-1} \circ \varphi' \circ \psi$ (possible
misprint). $n$-dimensionality is preserved by Step 2, and so are dimensional decompositions, since $F_*$ and $F^*$ are
additive. $\square$

*How (6) is read.* The text speaks of "the dimensional decomposition", by the uniqueness part of Proposition 9.1.11. That
uniqueness does not hold as we read it (Chapter 9); so (6) is read as "every dimensional decomposition is mapped to one",
which is what the proof gives (Findings, items 33, 34). The statements take $X$ and $Y$ in one universe. *Checked by machine
(V11.17, V11.18):* `Polyfold.EpGroupoid.LocalBranchingStructure.mapDiffeo`,
`Polyfold.EpFunctor.isBranchedEpSubgroupoid_pushforwardTheta`, `Polyfold.EpFunctor.orbitSupp_pushforwardTheta`,
`Polyfold.EpFunctor.isManifoldType_pushforwardTheta`, `Polyfold.EpFunctor.isDimDecomposition_pushforwardTheta`,
`Polyfold.EPLocalization.EPLoc.theorem_11_3_3_one`, `Polyfold.EPLocalization.EPLoc.theorem_11_3_3_six`,
`Polyfold.EpGroupoid.not_proposition_9_1_11_rn`.

The example of §0 is the witness: $\Theta_0 = 1_{\{0\}}$ on $\mathbb Z/2 \ltimes \mathbb R$, its pull-back along the
refinement, equal to $1$ at two objects, and its push-forward along the generalized isomorphism of the refinement (Findings,
item 35). *Checked by machine (V11.19):* `Polyfold.EpGroupoid.Examples.isBranchedEpSubgroupoid_reflectionTheta`,
`Polyfold.EpGroupoid.Examples.pullbackTheta_reflectionCover_two_points`,
`Polyfold.EpGroupoid.Examples.isGeneralizedIso_reflectionCoverDiagram`.

*The rest of §11.3 (pp. 538–542 (2017 pp. 391–395)): orientations, tangents and boundaries.* Chapter 9 orients a branched
ep⁺-subgroupoid $\Theta$ of $X$ by a section functor $\hat T_\Theta$ of $\hat\pi : \widehat{Gr}(X) \to X_\infty$: at each
smooth object $x$ a finite formal sum, with rational weights, of oriented tangent sets at $x$, natural along morphisms and
represented near each point by the oriented sheets of a local branching structure (Definition 9.3.2). Chapter 9 also takes a
hypothesis that the results below need: the sums $\sum_i \sigma_i T_xM_i$ of Theorem 9.2.1 do not depend on the local
branching structure (`Polyfold.EpGroupoid.HasIndependentTangentSums`). It holds on $\mathbb R^n$ for every $\Theta$
(`Polyfold.EpGroupoid.hasIndependentTangentSums_rn`); here it is assumed for the ep⁺-subgroupoid being moved and proved for
its images.

**Lemma 11.3.4 (2017: 11.6) (section functors along generalized isomorphisms).** Let $\Gamma(\hat\pi_X)$ be the set of
section functors of $\hat\pi_X$, with no continuity required. For an equivalence $F : X \to Y$ set $(F_*h)(y) = T\psi \circ
TF(x)\, h(x)$ for any $x$ and $\psi : F(x) \to y$ (11.8), and $(F^*h')(x) = TF(x)^{-1} h'(F(x))$ (11.9). For a generalized
isomorphism $f$ represented by $X \xleftarrow{F} A \xrightarrow{\Phi} Y$, the maps $f_* = \Phi_* F^*$ and $f^* = F_*\Phi^*$
do not depend on the representative, $(f^{-1})_* = f^*$, and $(g \circ f)_* = g_* \circ f_*$, $(g \circ f)^* = f^* \circ
g^*$.

*Proof.* A linear sc-isomorphism $L : T_xX \to T_yY$ moves an oriented tangent set to its image with the image orientation,
and a formal sum term by term. If $(x', \psi')$ is another choice, fullness of $F$ gives $\gamma : x' \to x$ with $\psi \circ
F(\gamma) = \psi'$, so $T\psi' \circ TF(x') = T\psi \circ TF(x) \circ T\gamma$, and $T\gamma\, h(x') = h(x)$ because $h$ is
natural; the two values agree. The same computation shows that $F_*h$ is natural, and $F^*F_*h = h$, $F_*F^*h' = h'$;
naturally equivalent equivalences give the same maps. On classes one argues as for functors $\Theta$: in the weak fibred
product of two equivalences $(\pi_Z)_*(\pi_X)^*h = G^*F_*h$, which gives the independence of the representative and the
composition laws. $\square$

A section functor is recorded on all objects, $0$ off $X_\infty$; every orientation of Chapter 9 is one. The composition laws
are stated, as in the text, for generalized isomorphisms (Findings, item 40). *Checked by machine (V11.20):*
`Polyfold.EpGroupoid.GrHatSections`, `Polyfold.EpGroupoid.IsOrientation.isGrHatSection`, `Polyfold.EpFunctor.pushSection`,
`Polyfold.EpFunctor.pushSection_eq`, `Polyfold.EpFunctor.pullSection`,
`Polyfold.WeakFibredProduct.pushSection_projRight_pullSection`, `Polyfold.EPLocalization.EPLoc.pushSection_inv`,
`Polyfold.EPLocalization.EPLoc.lemma_11_3_4`.

**Theorem 11.3.5 (2017: 11.4) (orientations under generalized isomorphisms).** Let $f : X \to Y$ be a generalized
isomorphism. If $\hat T_\Theta$ orients $\Theta$, then $f_*\hat T_\Theta$ orients $f_*\Theta$; if $\hat T_{\Theta'}$ orients
$\Theta'$, then $f^*\hat T_{\Theta'}$ orients $f^*\Theta'$.

*Proof.* It suffices to treat an equivalence $F$. Given $y$ and $\psi : F(x) \to y$, the transport chart $Q = \hat\psi \circ
F$ is an sc-diffeomorphism from a neighbourhood of $x$ onto one of $y$, and its tangent map at $u$ is $T\psi_u \circ TF(u)$,
with $\psi_u$ the morphism of $\hat\psi$ at $F(u)$. An oriented local branching structure $(M_i, o_i)$, $(\sigma_i)$
representing $\hat T_\Theta$ near $x$ is moved by $Q$ to $(Q(M_i), Q_*o_i)$ with the same weights, which represents $F_*\hat
T_\Theta$ near $y$ by (11.8). For $F^*$, a structure at $F(x)$ is moved back by a local inverse of $F$. $\square$

Chapter 9 moves submanifolds, tangent sets and orientations by sc-diffeomorphisms of one M-polyfold; the proof needs them
between open subsets of two, and the formal proof supplies this. The independence of the tangent sums is assumed for
$\Theta$, resp. $\Theta'$, and proved for $f_*\Theta$ and $f^*\Theta'$ (Findings, item 41). *Checked by machine (V11.21):*
`Polyfold.EpFunctor.TransportChart.tangentMor_ψ_tangent_obj`, `Polyfold.MPolyfold.SubmanifoldOrientation.mapDiffeo`,
`Polyfold.EpGroupoid.OrientedBranchingStructure.mapDiffeo`, `Polyfold.EpFunctor.isOrientation_pushSection`,
`Polyfold.EpFunctor.isOrientation_pullSection`, `Polyfold.EPLocalization.EPLoc.theorem_11_3_5_push`,
`Polyfold.EPLocalization.EPLoc.theorem_11_3_5_pull`.

**Definition 11.3.6 (2017: 11.5) (oriented branched ep⁺-subgroupoids under generalized isomorphisms).** For an oriented
branched ep⁺-subgroupoid $\hat\Theta = (\Theta, \hat T_\Theta)$ of $X$, one $\hat\Theta'$ of $Y$ and a generalized
isomorphism $f : X \to Y$, $f_*\hat\Theta = (f_*\Theta, f_*\hat T_\Theta)$ and $f^*\hat\Theta' = (f^*\Theta', f^*\hat
T_{\Theta'})$. By (11.10), $(g \circ f)_* = g_* \circ f_*$, $(g \circ f)^* = f^* \circ g^*$, $f^*f_*\hat\Theta = \hat\Theta$
and $f_*f^*\hat\Theta' = \hat\Theta'$.

These are oriented branched ep⁺-subgroupoids by Theorems 11.3.3 and 11.3.5, and (11.10) follows from Lemma 11.3.4 and the
same laws for functors $\Theta$. The structure records the independence of the tangent sums. Of the two inverse laws,
$f^*f_*\hat\Theta = \hat\Theta$ is proved for $\hat T_\Theta$ recorded as $0$ off $X_\infty$, and $f_*f^*\hat\Theta' =
\hat\Theta'$ for its two components (Findings, item 42). *Checked by machine (V11.22):*
`Polyfold.EPLocalization.OrientedBranched`, `Polyfold.EPLocalization.OrientedBranched.push`,
`Polyfold.EPLocalization.OrientedBranched.pull`, `Polyfold.EPLocalization.OrientedBranched.push_comp`,
`Polyfold.EPLocalization.OrientedBranched.pull_comp`, `Polyfold.EPLocalization.OrientedBranched.pull_push`,
`Polyfold.EPLocalization.EPLoc.pushTheta_pullTheta`, `Polyfold.EPLocalization.EPLoc.pushSection_pullSection`.

**Theorem 11.3.7 (2017: 11.5) (tangents under generalized isomorphisms).** Let $f : X \to Y$ be a generalized isomorphism,
with tangent $Tf : TX \to TY$ (Theorem 11.1.1), and let $\Theta$, $\Theta'$ be branched ep⁺-subgroupoids of $X$, $Y$. Then
$(Tf)_*T\Theta = T(f_*\Theta)$ and $(Tf)^*T\Theta' = T(f^*\Theta')$.

*Proof.* The text sketches it and leaves the details to the reader. Near $x$, $T\Theta$ is $\sum_i \sigma_i 1_{T_xM_i}$ for a
local branching structure, independent of the structure by the hypothesis above. For an sc-diffeomorphism $f$ between open
subsets of two M-polyfolds and a submanifold $A$, $T_{f(a)}f(A) = Tf(T_aA)$. So moving a local branching structure by $Q =
\hat\psi \circ F$ moves its tangent sums by $TQ$, and $T(F_*\Theta)(y)$ is $T\Theta(x)$ moved by $T\psi \circ TF(x)$ for
every $\psi : F(x) \to y$. That is $(TF)_*T\Theta$, the push-forward of Definition 11.3.1 along the equivalence $TF$. For a
generalized isomorphism, $Tf = [Td]$ for the chosen representative $d$, and the case of equivalences applies to both legs.
$\square$

The statement assumes the independence of the tangent sums for $\Theta$, resp. $\Theta'$ (Findings, item 43). *Checked by
machine (V11.23):* `Polyfold.MPolyfold.submanifoldTangent_image_of_isScDiffeoOn`,
`Polyfold.EpGroupoid.LocalBranchingStructure.tangentSum_mapDiffeo`, `Polyfold.EpFunctor.tangentValue_pushforwardTheta`,
`Polyfold.EpFunctor.tangentTheta_pushforwardTheta`, `Polyfold.EpFunctor.tangentTheta_pullbackTheta`,
`Polyfold.EPLocalization.EPLoc.hasIndependentTangentSums_pushTheta`, `Polyfold.EPLocalization.EPLoc.tangentFunctor_map_eq`,
`Polyfold.EPLocalization.EPLoc.theorem_11_3_7_push`, `Polyfold.EPLocalization.EPLoc.theorem_11_3_7_pull`.

**Theorem 11.3.8 (2017: 11.6) (boundaries under generalized isomorphisms).** For a generalized isomorphism $f : X \to Y$ and
branched ep⁺-subgroupoids $\Theta$, $\Theta'$ of $X$, $Y$, $f_*(\partial\Theta) = \partial(f_*\Theta)$ and
$f^*(\partial\Theta') = \partial(f^*\Theta')$ (11.11).

*Proof.* $\partial\Theta$ (Definition 9.2.16) is built from the boundaries $\partial M_i$ of the sheets of local branching
structures. The text's sketch notes that $d_M(x)$ is preserved when neighbourhoods are moved; this is read as the invariance
of $\partial M$ (Remark 9.2.14) under sc-diffeomorphisms between open subsets of two M-polyfolds: $f(a) \in \partial f(A)$ if
and only if $a \in \partial A$, through the reduced tangent condition. Then $\partial\Theta$ is moved pointwise by every
chart $\hat\psi \circ F$, and (11.11) follows for equivalences and then for generalized isomorphisms. $\square$

Like the previous statements it assumes the independence of the tangent sums (Findings, item 44). *Checked by machine
(V11.24):* `Polyfold.MPolyfold.isTangentReducedAt_image_iff_of_isScDiffeoOn`,
`Polyfold.MPolyfold.mem_submanifoldBoundary_image_iff_of_isScDiffeoOn`,
`Polyfold.EpGroupoid.boundaryTheta_apply_of_isScDiffeoOn`, `Polyfold.EpFunctor.boundaryTheta_pushforwardTheta`,
`Polyfold.EpFunctor.boundaryTheta_pullbackTheta`, `Polyfold.EPLocalization.EPLoc.theorem_11_3_8_push`,
`Polyfold.EPLocalization.EPLoc.theorem_11_3_8_pull`.

**Theorem 11.3.9 (2017: 11.7) (oriented boundaries under generalized isomorphisms).** For a generalized isomorphism $f : X
\to Y$ and oriented tame branched ep⁺-subgroupoids $\hat\Theta$, $\hat\Theta'$ of $X$, $Y$, $\partial(f_*\hat\Theta) =
f_*(\partial\hat\Theta)$ and $\partial(f^*\hat\Theta') = f^*(\partial\hat\Theta')$.

*What is proved.* The text leaves the proof to the reader. Chapter 9's orientation $\hat T_{\partial\Theta}$ of the boundary
is the boundary lift of $\hat T_\Theta$: the terms at which the sheet has $d_M = 1$ are kept, and each is replaced by its
image under a boundary operation $bd$ on oriented tangent sets. Chapter 9 takes $bd$ as data, since the partial cones of
submanifolds that determine it are not formalized; so the theorem needs the boundary operations on the two sides to
correspond. A linear map $L : T_xX \to T_yY$ *transfers* $bd$ to $bd'$ if it preserves $d_M = 1$ and $bd'(L_*o) = L_*(bd\,
o)$ there; the identity transfers every boundary operation to itself. For a representative $X \xleftarrow{F} A
\xrightarrow{\Phi} Y$ with $\Phi$ an equivalence and boundary operations on $X$, $A$, $Y$ transferred by $TF(a)^{-1}$ and by
$T\psi \circ T\Phi(a)$, both formulae hold, with Theorem 11.3.8 for the underlying $\partial\Theta$. Not formalized: that the
boundary operations of Definition 9.3.8 satisfy this along equivalences, which needs sc-diffeomorphisms between different
M-polyfolds to preserve the tame induced structures, $d_M$ and outward vectors; hence a form of the theorem independent of
the representative (gap G.130; Findings, item 45). *Checked by machine (V11.25):* `Polyfold.MPolyfold.IsBoundaryTransfer`,
`Polyfold.MPolyfold.isBoundaryTransfer_id`, `Polyfold.EpFunctor.pushSection_boundaryLift`,
`Polyfold.EpFunctor.pullSection_boundaryLift`, `Polyfold.EPLocalization.EPLoc.theorem_11_3_9_push`,
`Polyfold.EPLocalization.EPLoc.theorem_11_3_9_pull`.

The hypotheses can hold: the orientation $\hat T^1$ of Example 9.3.5 on $\mathbb R^2$ is a section functor, $(\Theta, \hat
T^1)$ is an oriented branched ep⁺-subgroupoid in the sense of Definition 11.3.6 and is pushed forward along the identity
generalized isomorphism, and the identity transfers the identity boundary operation (Findings, item 46). *Checked by machine
(V11.26):* `Polyfold.EpGroupoid.Examples.exampleT1_mem_grHatSections`, `Polyfold.EpGroupoid.Examples.example935Oriented`,
`Polyfold.EpGroupoid.Examples.example935Oriented_push`, `Polyfold.EpGroupoid.Examples.isBoundaryTransfer_id_rn2`.

## 5. Integration (pp. 542–546 (2017 pp. 396–399)), not formalized

§11.4 shows that integration over branched ep⁺-subgroupoids is a notion on polyfolds. Theorem 11.4.1 (2017: 11.8): for a
generalized isomorphism $f : X \to Y$, an oriented, tame, compact, $n$-dimensional branched ep⁺-subgroupoid $\hat\Theta$ of
$X$ and an $n$-form $\omega$, the canonical measure of Chapter 9 satisfies $|f|_*\mu^{\hat\Theta}_\omega =
\mu^{f_*\hat\Theta}_{f_*\omega}$, and dually for pull-backs; Theorem 11.4.2 (new in the 2021 edition) states the same for the
effective measures under the local unique continuation property. Remark 11.4.3 (2017: 11.3) concludes that pairs $(X, \beta)$
related by a generalized isomorphism compatible with $\beta$ give the same integrals. Theorems 11.4.4 (2017: 11.9) and 11.4.5
(new in the 2021 edition) do the same for the boundary measures.

None of this is formalized. It needs forms (G.74, G.80), branched integration and the boundary measures (G.107–G.109), and
the orientations of §4; §11.4 is gap G.131 (V11.27–V11.29; Findings, item 50).

## 6. Auxiliary norms and multisections (pp. 546–549 (2017 pp. 399–401))

Let $P : W \to X$ and $P' : W' \to X'$ be strong bundles over ep-groupoids, and $[D] = [W \xleftarrow{\Phi} W''
\xrightarrow{\Psi} W']$ a generalized strong bundle isomorphism (Chapter 10), represented with both legs strong bundle
equivalences. An auxiliary norm (Definition 8.3.5) is a function $N$ on the level-$(0,1)$ part $W_{0,1}$ which (1) is a
complete norm on each fibre, (2) forces a sequence $h_k$ with $N(h_k) \to 0$ over a convergent sequence of base points to
converge to the zero section, and (3) is invariant under the morphisms. The objects $W_{0,1}$ with the morphisms of $W$ have
an orbit space $|W[1]|$, and the map $|W[1]| \to |W|$ is injective, since two points of $W_{0,1}$ related by a morphism of
$W$ are related in $W[1]$; a strong bundle equivalence induces a continuous map on it, and $[D]$ the continuous map $|D| =
|\Psi| \circ |\Phi|^{-1}$ on $|W[1]|$, determined by $|D|$ on $|W|$.

**Proposition 11.5.1 (2017: 11.6) (auxiliary norms are carried along).** For an auxiliary norm $N'$ on $W'$, $[D]^*N'(e) =
N'(\Psi(e''))$, for any $e'' \in W''_{0,1}$ with a morphism $\Phi(e'') \to e$, is well defined; it is an auxiliary norm, and
likewise $[D]_*N$. The two are mutually inverse, and $[D]^*N' = [D']^*N'$, $[D]_*N = [D']_*N$ if $|[D]| = |[D']|$.

*What is proved.* Define $[D]^*N'(e) = N'(e')$ for any $e'$ representing $|D|(|e|) \in |W'[1]|$. For invariant $N'$ this does
not depend on $e'$ and equals the text's $N'(\Psi(e''))$ for every admissible $e''$. It is invariant, continuous (the map
induced by $N'$ on $|W'[1]|$, composed with $|D|$ and the quotient map), satisfies (3), is inverse to $[D]_*$, and depends
only on $|[D]|$. Conditions (1) and (2) are not shown: they need the level-$1$ fibre maps of $\mu$ and of a strong bundle
equivalence as linear bijections, and the local homeomorphism property on level $1$ near the zero section (gap G.132).

Before the proposition the text derives $[D] = [D']$ from $|[D]| = |[D']|$ under the local regularity property; that is
Theorem 10.5.7, which does not hold as we read it (Chapter 10). Nothing in §11.5 uses it: the last clause needs only $|[D]| =
|[D']|$ (Findings, item 60). *Checked by machine (V11.30):* `Polyfold.SBLocalization.GenSBMap.proposition_11_5_1`,
`Polyfold.SBLocalization.SDiagram.pullNorm_eq_Ψ`, `Polyfold.SBLocalization.SDiagram.continuous_pullNorm`,
`Polyfold.SBLocalization.SDiagram.pushNorm_pullNorm`, `Polyfold.SBLocalization.SDiagram.pullNorm_eq_of_orbitMap_eq`,
`Polyfold.SBLocalization.SDiagram.oneOrbitMap_eq_of_orbitMap_eq`.

An sc⁺-multisection of $P$ (2021 Definition 13.2.1) is a functor $\Lambda : W \to \mathbb Q^+$ together with local section
structures: near every point, $\Lambda$ is a weighted sum of indicators of the graphs of finitely many sc⁺-sections. Its
pull-back along a strong bundle functor $\Psi$ is $\Psi^*\Lambda = \Lambda \circ \Psi$, and its push-forward along a strong
bundle equivalence $\Phi$ is $\Phi_*\Lambda(w') = \Lambda(w)$ for any $w$ with a morphism $\Phi(w) \to w'$.

**Lemma 11.5.2 (2017: 11.7) (the push-forward is well defined).** For a strong bundle equivalence $\Phi$, $\Phi_*\Lambda$
does not depend on the choices and is an sc⁺-multisection.

*What is proved.* For the functor $\Lambda$: the value does not depend on $w$, $\Phi_*\Lambda$ is a functor, and
$\Phi^*\Phi_*\Lambda = \Lambda$, $\Phi_*\Phi^*\Lambda' = \Lambda'$; the proof is that of Lemma 11.3.2. The local section
structures, and their transport along $\Phi$, are not formalized: 2021 Definition 13.2.1 is not in the project, and the
transport needs a strong bundle form of the transport of Proposition 10.1.9 (gap G.133). *Checked by machine (V11.31):*
`Polyfold.SBLocalization.lemma_11_5_2`, `Polyfold.SBLocalization.pushMult_eq`, `Polyfold.SBLocalization.pullMult_pushMult`.

**Proposition 11.5.3 (2017: 11.7) (multisections under generalized isomorphisms).** $[D]_*\Lambda = \Psi_*\Phi^*\Lambda$ and
$[D]^*\Lambda' = \Phi_*\Psi^*\Lambda'$ do not depend on the representative, are mutually inverse, and, for generalized strong
bundle maps $[D]$, $[D']$ with $|[D]| = |[D']|$, agree.

*Proof (for the functors).* $[D]_*\Lambda(w') = \Lambda(w)$ whenever $|D|(|w|) = |w'|$, so both operations depend only on
$|D|$, and every claim follows. $\square$

The last clause is read for generalized strong bundle isomorphisms, for which $[D]_*$ is defined; the local section
structures are G.133 (Findings, item 61). *Checked by machine (V11.32):*
`Polyfold.SBLocalization.GenSBMap.proposition_11_5_3`, `Polyfold.SBLocalization.SDiagram.pushMult_eq`,
`Polyfold.SBLocalization.SDiagram.pushMult_eq_of_orbitMap_eq`.

## 7. Proper coverings up to equivalence (pp. 549–566 (2017 pp. 401–416))

A proper covering functor $F : Y \to X$ (Definition 8.5.1) is a functor that is a surjective local sc-diffeomorphism on
objects with finite, evenly covered fibres, such that $\alpha : \psi \mapsto (F(\psi), s(\psi))$ is an sc-diffeomorphism from
the morphisms of $Y$ onto the fibred product of the morphisms of $X$ with the objects of $Y$. Such functors are the
ep-groupoid form of finite coverings; §11.6 shows that they too can be taken up to equivalence.

**Lemma 11.6.1 (new in the 2021 edition) (proper coverings on morphisms).** A proper covering functor is a surjective local
sc-diffeomorphism on morphisms.

*Proof.* Since $\alpha$ is bijective, a morphism $\varphi$ of $X$ and an object $y$ over $s(\varphi)$ have a unique lift
$\psi$ with $F(\psi) = \varphi$ and $s(\psi) = y$, and $F(t(\psi)) = t(\varphi)$. Surjectivity on morphisms follows from
surjectivity on objects; the local sc-diffeomorphism property from $\alpha$ and the source map. Lifts with prescribed target
are unique as well, by the inverse. $\square$

*Checked by machine (V11.33):* `Polyfold.EpFunctor.IsProperCovering.lemma_11_6_1`,
`Polyfold.EpFunctor.IsProperCovering.lift`, `Polyfold.EpFunctor.IsProperCovering.existsUnique_lift_tgt` (Findings, item 70).

For an object $x$ of $X$ let $Y_x = F^{-1}(x)$ and $G_x$ the isotropy group. Then $g * y = t(\alpha^{-1}(g, y))$ is an action
of $G_x$ on $Y_x$ ((11.15)).

**Lemma 11.6.2 (2017: 11.8) (the fibre is a translation groupoid).** The full subcategory $Y(x)$ of $Y$ on $Y_x$ is naturally
identified with the translation groupoid $G_x \ltimes Y_x$.

*How this is read.* "Naturally identified" is the functor $Y(x) \to G_x \ltimes Y_x$ which is the identity on objects and
$\alpha$ on morphisms; it is bijective on objects, full and faithful, an isomorphism of categories. The topology of $Y(x)$
plays no part. *Proof.* The action law: $\alpha^{-1}(g_2g_1, y)$ and $\alpha^{-1}(g_2, g_1 * y) \circ \alpha^{-1}(g_1, y)$
have the same image under $\alpha$. In the text's computation of $\alpha(\psi_2 \circ \psi_1)$ the second factor is printed
$(F(\psi_2), s(\psi_1))$; we read $(F(\psi_1), s(\psi_1))$ (possible misprint). Faithfulness and fullness are the injectivity
and surjectivity of $\alpha$ over $Y_x$. $\square$

*Checked by machine (V11.34):* `Polyfold.EpFunctor.IsProperCovering.lemma_11_6_2`,
`Polyfold.EpFunctor.IsProperCovering.instMulActionFiber`, `Polyfold.EpFunctor.IsProperCovering.toTranslation` (Findings, item
71).

**Lemma 11.6.3 (2017: 11.9) (transport of fibres).** A morphism $\varphi : x \to x'$ induces a bijection $B_\varphi : Y_x \to
Y_{x'}$, $B_\varphi(y) = t(\psi)$ for the lift $\psi$ of $(\varphi, y)$, equivariant along $g \mapsto \varphi \circ g \circ
\varphi^{-1}$ ((11.16)), and an isomorphism $G_x \ltimes Y_x \to G_{x'} \ltimes Y_{x'}$.

*Proof.* $B_{\varphi^{-1}}$ is inverse to $B_\varphi$ by uniqueness of lifts; equivariance by uniqueness of lifts of $\varphi
\circ g$. $\square$

*Checked by machine (V11.35):* `Polyfold.EpFunctor.IsProperCovering.lemma_11_6_3`,
`Polyfold.EpFunctor.IsProperCovering.bijective_transportFiber`, `Polyfold.EpFunctor.IsProperCovering.transportFiber_smul`.

**Definition 11.6.4 (2017: 11.6) (functors and equivalences of proper coverings).** (1) An sc-smooth functor $(\Psi, \Phi) :
F \to F'$ between $F : Y \to X$ and $F' : Y' \to X'$ is a pair of sc-smooth functors $\Psi : Y \to Y'$, $\Phi : X \to X'$
with $\Phi \circ F = F' \circ \Psi$. (2) It is an equivalence if $\Psi$ and $\Phi$ are equivalences and $\Psi$ maps each
fibre $Y_x$ bijectively onto $Y'_{\Phi(x)}$.

**Proposition (the fibre condition is automatic).** If $F$ and $F'$ are proper coverings and $\Psi$, $\Phi$ are equivalences,
then $\Psi$ maps each $Y_x$ bijectively onto $Y'_{\Phi(x)}$.

*Proof.* Injectivity: if $\Psi(y_1) = \Psi(y_2)$ with $y_1, y_2 \in Y_x$, fullness of $\Psi$ gives $\eta : y_1 \to y_2$ with
$\Psi(\eta) = 1$. Then $\Phi(F(\eta)) = F'(\Psi(\eta))$ is an identity, so $F(\eta) = 1_x$ by faithfulness of $\Phi$; $\eta$
and $1_{y_1}$ both lift $(1_x, y_1)$, so $\eta = 1_{y_1}$ and $y_2 = y_1$. Surjectivity: for $y'$ over $\Phi(x)$, essential
surjectivity of $\Psi$ gives $y$ and $\eta' : \Psi(y) \to y'$; fullness of $\Phi$ writes $F'(\eta') = \Phi(\varphi)$ with
$\varphi : F(y) \to x$; then $\Psi$ of the lift of $(\varphi, y)$ and $\eta'$ lift the same morphism from the same object, so
they are equal and $\Psi(B_\varphi(y)) = y'$. $\square$

The text's remark after the definition treats the fibre bijection as cutting out a subclass of the functors of (1); within
(2) it comes for free. The functor from the pair groupoid of $\mathbb Z$ to the point, between the identity coverings, is an
equivalence with no inverse functor (Findings, item 72). *Checked by machine (V11.36):* `Polyfold.ProperCoveringHom`,
`Polyfold.ProperCoveringHom.IsEquivalence`, `Polyfold.ProperCoveringHom.isFiberBijective_of_isEquivalence`,
`Polyfold.ProperCoveringHom.isEquivalence_iff`, `Polyfold.CoveringEquivalence.Examples.isEquivalence_pairToPointCovering`.

**Definition 11.6.5 (2017: 11.7) (natural transformations).** A natural transformation $(\zeta, \xi) \to (\zeta', \xi')$ of
functors $F \to F'$ is a pair of natural transformations $\tau_Y : \zeta \to \zeta'$ and $\tau_X : \xi \to \xi'$ with $\tau_X
\circ F = F' \circ \tau_Y$ ((11.20)).

The identity (11.20) is read objectwise, $\tau_X(F(y)) = F'(\tau_Y(y))$; the square after the definition follows. Natural
equivalence, the existence of one, is an equivalence relation compatible with composition on both sides (Findings, item 73).
*Checked by machine (V11.37):* `Polyfold.ProperCoveringHom.NatTrans`, `Polyfold.ProperCoveringHom.NatTrans.naturality_F`,
`Polyfold.ProperCoveringHom.naturallyEquivalent_equivalence`, `Polyfold.ProperCoveringHom.NaturallyEquivalent.comp_left`.

**Theorem 11.6.6 (2017: 11.10) (weak fibred products of proper coverings).** Let $F : Y \to X$, $F' : Y' \to X'$, $F'' : Y''
\to X''$ be proper covering functors, $(\Psi, \Phi) : F \to F'$ an equivalence and $(\zeta, \xi) : F'' \to F'$ an sc-smooth
functor, and let $P = Y \times_{Y'} Y''$, $Q = X \times_{X'} X''$ be the weak fibred products. Then $H(y, \psi', y'') =
(F(y), F'(\psi'), F''(y''))$ on objects and $H(h, \psi', h'') = (F(h), F'(\psi'), F''(h''))$ on morphisms ((11.18), (11.19))
define a functor $H : P \to Q$, and: (1) $H$ is a proper covering functor; (2) $(\pi_{Y''}, \pi_{X''}) : H \to F''$ is an
equivalence; (3) $(\Psi \circ \pi_Y, \Phi \circ \pi_X)$ and $(\zeta \circ \pi_{Y''}, \xi \circ \pi_{X''})$ are naturally
equivalent. If $X''$ is tame, so are $P$ and $Q$; if $(\zeta, \xi)$ is an equivalence, so is $(\pi_Y, \pi_X) : H \to F$.

*Proof.* (A) *Objects.* The text's heading says that $F \times F' \times F''$ maps $X \times_{X'} X''$ onto $Y \times_{Y'}
Y''$; we read $Y \times_{Y'} Y''$ onto $X \times_{X'} X''$ (possible misprint). Given $(x, \varphi', x'')$, lift $x''$ to
$y''$ and $\varphi'$ along $F'$ to a $\psi'$ ending at $\zeta(y'')$; the source of $\psi'$ lies over $\Phi(x)$, so it is
$\Psi(y)$ for some $y \in Y_x$, by the fibre condition. $H$ is a local sc-diffeomorphism on objects by two out of three: the
projections $P \to Y''$ and $Q \to X''$ are local sc-diffeomorphisms because $\Psi$ and $\Phi$ are, $F''$ is one, and
$\pi_{X''} \circ H = F'' \circ \pi_{Y''}$. (B) *The map $\alpha$ of $H$* is an sc-diffeomorphism onto the fibred product, its
inverse built from those of $F$ and $F''$. (C) *Finite fibres, evenly covered.* A fibre of $H$ is determined by its $Y$- and
$Y''$-components (the middle one is then the unique lift), so it is finite. The text argues with sequences; instead, $H$ is
shown to be a proper map on objects, from the properness of $F$ and $F''$ on objects and the continuity of the inverse of the
map $\alpha$ of $F'$, and a proper local sc-diffeomorphism is evenly covered near a point with finite fibre: separate the
points of the fibre by disjoint sheets, and use that a proper map is closed. (D) $\pi_{Y''}$ and $\pi_{X''}$ are equivalences
(Theorem 10.2.2), so the pair is an equivalence of proper coverings by the proposition after Definition 11.6.4. (E)
$\tau_P(y, \psi', y'') = \psi'$ and $\tau_Q(x, \varphi', x'') = \varphi'$ satisfy (11.20). (F) $Y'' \to X''$, $P \to Y''$ and
$Q \to X''$ are surjective local sc-diffeomorphisms on objects, and tameness pulls back along local sc-diffeomorphisms. The
last claim is symmetric. $\square$

Part (1) holds under weaker hypotheses: $\Psi$, $\Phi$ local sc-diffeomorphisms on objects and $\Psi$ onto on fibres
(Findings, item 74). *Checked by machine (V11.38, V11.39):* `Polyfold.ProperCoveringHom.hFunctor`,
`Polyfold.ProperCoveringHom.surjective_hObj`, `Polyfold.ProperCoveringHom.isProperMap_hObj`,
`Polyfold.MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap`, `Polyfold.ProperCoveringHom.isProperCovering_hFunctor_of`,
`Polyfold.ProperCoveringHom.theorem_11_6_6`, `Polyfold.CoveringEquivalence.Examples.theorem_11_6_6_pairToPoint`.

Proper coverings and their functors form a category $\mathcal{PC}$, with the multiplicative class $E_{\mathcal{PC}}$ of
equivalences; by Theorem 11.6.6 (1) the weak fibred product of an equivalence and a functor is again an object of
$\mathcal{PC}$.

**Definition 11.6.7 (2017: 11.8) (diagrams and common refinements).** A diagram $d : F \to F'$ is $F \xleftarrow{\Gamma} A
\xrightarrow{\varepsilon} F'$ with $\Gamma \in E_{\mathcal{PC}}$. A common refinement of $d$ and $d' = (\Gamma',
\varepsilon')$ consists of an object $A''$ and equivalences $H : A'' \to A$, $H' : A'' \to A'$ with $\Gamma \circ H \simeq
\Gamma' \circ H'$ and $\varepsilon \circ H \simeq \varepsilon' \circ H'$.

All proper coverings of $\mathcal{PC}$ are taken in one universe, so that weak fibred products stay in $\mathcal{PC}$
(Findings, item 75). *Checked by machine (V11.40):* `Polyfold.PC`, `Polyfold.PC.equivalences`, `Polyfold.PC.fibred`,
`Polyfold.PC.Diagram.CommonRefinement`, `Polyfold.PC.Examples.diagram`.

**Proposition 11.6.8 (2017: 11.8) (common refinements are transitive).** If $d, d'$ and $d', d''$ have common refinements, so
have $d, d''$.

*Proof.* Let $(H, H')$ refine $d, d'$ through $A''$ and $(K, K')$ refine $d', d''$ through $B''$. The weak fibred product
$A'' \times_{A'} B''$ of $H'$ and $K$ exists in $\mathcal{PC}$ (Theorem 11.6.6), with equivalences $H \circ \pi_{A''}$ and
$K' \circ \pi_{B''}$. Then $\Gamma \circ H \circ \pi_{A''} \simeq \Gamma' \circ H' \circ \pi_{A''} \simeq \Gamma' \circ K
\circ \pi_{B''} \simeq \Gamma'' \circ K' \circ \pi_{B''}$, the middle step by Theorem 11.6.6 (3), and the same chain for the
$\varepsilon$'s. $\square$

The text's chain for the $\varepsilon$'s stops at $\varepsilon' \circ K \circ \pi_{B''}$; the last step uses $\varepsilon'
\circ K \simeq \varepsilon'' \circ K'$ and is added. Together with reflexivity and symmetry, having a common refinement is an
equivalence relation (Findings, item 75). *Checked by machine (V11.41):* `Polyfold.PC.proposition_11_6_8`,
`Polyfold.PC.Diagram.hasCommonRefinement_equivalence`, `Polyfold.PC.Examples.hasCommonRefinement_diagram`.

*The localization (pp. 561–563 (2017 pp. 410–412)).* The text then forms the category $\mathcal{PC}(E^{-1})$ whose morphisms
are the classes of diagrams, composed through weak fibred products, with a functor $I : \mathcal{PC} \to
\mathcal{PC}(E^{-1})$ that inverts equivalences; the well-definedness of the composition is left to the reader. Not
formalized (gap G.134; Findings, item 76).

*Remark 11.6.9 (2017: 11.4), pp. 563–566.* The remark views a strong bundle over an ep-groupoid and a strong bundle map as
functors, recalls Definition 8.5.9 of proper strong bundle coverings, and sketches the category of such coverings with its
equivalences and localization, leaving the details to the reader. Definition 8.5.9 is formalized in Chapter 8
(`Polyfold.EpStrongBundle.IsProperStrongBundleCovering2021`); the category and its localization are not (V11.42; gap G.135;
Findings, item 76).

## 8. Witnesses: the hypotheses can hold

Two hypotheses are taken, both in the rest of §11.3: Chapter 9's independence of the tangent sums of Theorem 9.2.1, assumed
for the branched ep⁺-subgroupoid being moved and proved for its images, which holds on $\mathbb R^n$; and the
boundary-transfer hypothesis of Theorem 11.3.9, which holds along the identity (§4). The statements of §4 and the category
$\mathcal{PC}$ take their ep-groupoids in one universe (Findings, item 80). Every definition has a witness. The quadrant with
the swap is weakly face structured and not face structured (§2). $\Theta_0 = 1_{\{0\}}$ on $\mathbb Z/2 \ltimes \mathbb R$ is
a branched ep⁺-subgroupoid that is pulled back along an equivalence not injective on objects and pushed forward along a
generalized isomorphism (§§0, 4). Example 9.3.5 on $\mathbb R^2$ gives a section functor and an oriented branched
ep⁺-subgroupoid (§4). The constant functions are invariant functions on $W_{0,1}$ and functors on $W$
(`Polyfold.SBLocalization.isOneInvariant_const`, `Polyfold.SBLocalization.isWFunctor_const`) (§6). The functor from the pair
groupoid of $\mathbb Z$ to the point, between identity coverings, is an equivalence of proper coverings, it and the identity
of the point satisfy the hypotheses of Theorem 11.6.6 with a nonempty weak fibred product, and the diagrams $\mathrm{pair}
\leftarrow \mathrm{pair} \to \mathrm{point}$ and $\mathrm{pair} \leftarrow \mathrm{pair} \times_{\mathrm{point}}
\mathrm{pair} \to \mathrm{point}$ have a common refinement (§7).

## 9. Summary of what was silently assumed, now made explicit

| Where | HWZ say | What is actually needed |
|---|---|---|
| pp. 521–522, Thm. 11.1.1 (2017: 11.1) | "the remaining argument" left to the reader | a comparison functor $T(A \times_Y B) \to TA \times_{TY} TB$, an equivalence by two out of three |
| pp. 522–523, Prop. 11.1.2 (2017: 11.1) | "Proposition 10.3.10" | Theorem 10.3.10 |
| p. 523, Ex. 11.1.4 (2017: 11.1) | not face structured, no reason | $\{d_{\lvert X \rvert} = 1\}$ connected, the corner in one face |
| p. 524, Rem. 11.1.5 (2017: 11.1) | quoted from [56] | a homeomorphism preserving the index maps faces to faces |
| p. 525, Rem. 11.1.7 (2017: 11.2) | tame and face structured are invariant | tameness from $X$ to $Y$ along an equivalence, through $X \times_Y Y$ |
| p. 535, Def. 11.3.1 (2017: 11.4) | push-forward $X' \to \mathbb Q^+$ | $Y \to \mathbb Q^+$ |
| p. 536, Lemma 11.3.2 (2017: 11.5) | $F$ an equivalence | $F$ full; essentially surjective for (2) |
| pp. 536–537, generalized maps | compositions "easily verified" | base change in the weak fibred product |
| pp. 537–538, Thm. 11.3.3 (2017: 11.3) | local branching structures moved by $\hat\psi \circ F$ | sheets restricted to its domain; paracompactness of the support carried along |
| p. 538, Thm. 11.3.3 | $\psi \circ \varphi' \circ \psi^{-1}$ | $\psi^{-1} \circ \varphi' \circ \psi$ |
| p. 537, Thm. 11.3.3 (6) | "the" dimensional decomposition | every dimensional decomposition |
| pp. 539–540, Thm. 11.3.5 (2017: 11.4) | oriented structures moved by $\hat\psi \circ F$ | Chapter 9's orientations between two M-polyfolds; the independence of the tangent sums assumed for $\Theta$, proved for $f_*\Theta$, $f^*\Theta'$ |
| p. 541, Thm. 11.3.7 (2017: 11.5) | details left to the reader | $T_{f(a)}f(A) = Tf(T_aA)$ between two M-polyfolds; $Tf = [Td]$ |
| p. 542, Thm. 11.3.8 (2017: 11.6) | $d_M(x)$ preserved | $\partial M$ invariant under sc-diffeomorphisms between two M-polyfolds |
| p. 542, Thm. 11.3.9 (2017: 11.7) | proof left to the reader | boundary operations carried into each other by the tangent maps (assumed; G.130) |
| p. 547, Prop. 11.5.1 (2017: 11.6) | choices of $e''$ and $\Phi(e'') \to e$ | a representative of $\lvert D \rvert(\lvert e \rvert)$ in $\lvert W'[1] \rvert$ |
| p. 549, Prop. 11.5.3 (2017: 11.7) | generalized strong bundle maps with $\lvert [D] \rvert = \lvert [D'] \rvert$ | generalized strong bundle isomorphisms |
| p. 550, (11.15) | $(F(\psi_2), s(\psi_1))$ | $(F(\psi_1), s(\psi_1))$ |
| p. 551, Lemma 11.6.2 (2017: 11.8) | "naturally identified" | an isomorphism of categories, identity on objects |
| p. 553, Def. 11.6.4 (2017: 11.6) | the fibre bijection as a condition | automatic for equivalences of proper coverings |
| p. 556, Thm. 11.6.6 (2017: 11.10), (A) | $X \times_{X'} X''$ onto $Y \times_{Y'} Y''$ | $Y \times_{Y'} Y''$ onto $X \times_{X'} X''$ |
| p. 559, Thm. 11.6.6, (C) | sequences | $H$ a proper map; proper local sc-diffeomorphisms are evenly covered |
| p. 562, Prop. 11.6.8 (2017: 11.8) | the chain for the $\varepsilon$'s | one more step, from $\varepsilon' \circ K \simeq \varepsilon'' \circ K'$ |

**Checked by machine.** The chapter is formalized in Lean 4 against Mathlib in the files `EpEquivalenceGeometry.lean`,
`EpEquivalenceGeometryFaces.lean`, `BranchedEquivalence.lean`, `BranchedEquivalenceLocalization.lean`,
`BranchedEquivalenceTangentSection.lean`, `BranchedEquivalenceTangent.lean`, `BranchedEquivalenceTangentOrientation.lean`,
`StrongBundleUpToEquivalence.lean`, `CoveringEquivalence.lean`, `CoveringEquivalenceTheorem.lean` and
`CoveringEquivalenceDiagram.lean` of `Polyfold/Chapter11/` imported by the root module (not the `WIP_*` files). Formalized:
Theorem 11.1.1, Proposition 11.1.2, Definition 11.1.3, Example 11.1.4, Remarks 11.1.5 and 11.1.7; Proposition 11.1.6 for the
bijection of faces and the homeomorphisms it induces, and Proposition 11.1.8 for those maps; Definition 11.3.1, Lemma 11.3.2,
the push-forward and pull-back along generalized maps and Theorem 11.3.3; Lemma 11.3.4 with (11.8) and (11.9), Theorem
11.3.5, Definition 11.3.6 with (11.10), Theorems 11.3.7 and 11.3.8 under Chapter 9's independence of the tangent sums, and
Theorem 11.3.9 for a representative under the boundary-transfer hypothesis; Proposition 11.5.1 without conditions (1) and (2)
of Definition 8.3.5, Lemma 11.5.2 and Proposition 11.5.3 for the functors underlying sc⁺-multisections; Lemmas 11.6.1–11.6.3,
Definitions 11.6.4, 11.6.5, 11.6.7, Theorem 11.6.6 and Proposition 11.6.8; several in stronger forms. Not formalized: the
ep-groupoid structure of faces, the intersection clause and $[d]_F$ in Proposition 11.1.6, §11.2, §11.4, conditions (1) and
(2) of auxiliary norms in Proposition 11.5.1, the local section structures of sc⁺-multisections, Theorem 11.3.9 independent
of the representative, the localization $\mathcal{PC}(E^{-1})$ and the category of Remark 11.6.9 (gaps G.128–G.135). The
statements are V11.1–V11.42 of `Exposition/Verification.md`, compared in `Exposition/polyfold-beside-lean.html`, retold in
`Exposition/ProofByProof.md`; findings: `Exposition/Findings.md`, "Chapter 11", items 1–8, 20, 30–35, 40–46, 50, 60–61,
70–76, 80.
