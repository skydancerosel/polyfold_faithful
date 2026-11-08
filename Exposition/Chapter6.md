# Chapter 6. Orienting a Fredholm problem: linearizations, determinant lines and orientations (HWZ Part I, Chapter 6, pp. 237–286 (preprint pp. 200–237))

*Hofer–Wysocki–Zehnder, "Polyfold and Fredholm Theory", Part I, Chapter 6 (2014 preprint, arXiv
1407.3185, pp. 200–237), rewritten for a first-year graduate student who wants to know how the solutions of a
Fredholm problem are counted with signs. Every formalized statement is proved; §6.7 (preprint §6.6) and Theorem 6.7.1 (preprint 6.43) are stated and
marked. Where the Lean formalization found a gap or a shorter route, the text follows the Lean. Statement numbers and
pages are those of the book (Springer 2021), with the preprint's in parentheses; each statement also carries its 2017 number
in the form "(book 2017: …)" (see `BookConcordance.md`). Conventions of Chapters 1–5: $P:Y\to X$ a strong bundle over a tame
M-polyfold, $f$ an sc-Fredholm section with tame germ data, $S_f = f^{-1}(0)$, $X_\infty$ the smooth points. A point $x$
is read at a *chart point* $(c,z)$, with $T_zO = Dr(z)E$ for $T_xX$ and $K_z = \rho(z)F$ for $Y_x$; the text's $f-s$ with
$s(x) = f(x)$ is written $f+s$ with $(f+s)(x) = 0$. Paths, homotopies and families are maps on $\mathbb R$, $\mathbb R^2$, $\mathbb R^n$ of which
only $[0,1]$, $[0,1]^2$, $[0,1]^n$ matters (decision D2; gap G.65; Findings, item 102). An orientation of a line is a ray.*

---

## 0. Which equilibria count, and with which sign?

A bead slides without friction on a vertical circular hoop of radius $R$ that spins with angular velocity $\omega$ about its
vertical diameter. In the rotating frame, at the angle $\theta$ from the bottom, the bead has the potential energy
$V = -mgR\cos\theta-\frac12m\omega^2R^2\sin^2\theta$ (gravity and the centrifugal potential), so with $\mu = \omega^2R/g$ its equilibria are the zeros of
$$f_\mu(\theta) = \frac{V'(\theta)}{mgR} = \sin\theta\,(1-\mu\cos\theta),\qquad f_\mu'(\theta) = \cos\theta-\mu\cos2\theta .$$
For $\mu<1$ there are two: the bottom, with $f' = 1-\mu>0$ (stable), and the top, with $f' = -1-\mu<0$. At $\mu = 1$ the bottom
loses its stability, and for $\mu>1$ two new equilibria appear at $\cos\theta = 1/\mu$, with $f' = \mu-1/\mu>0$, while now $f'(0) = 1-\mu<0$.
The number of equilibria jumps from $2$ to $4$; counted with the sign of $f'$ it does not move: $1-1 = 0 = -1-1+1+1$. It is
the Euler characteristic of the circle. The count survives the bifurcation because the sign of $f'$ is an *orientation*:
a zero at which $f'$ is invertible is an oriented point, positive or negative according as $f'$ preserves or reverses
chosen orientations of its source and target.

For a Fredholm operator $T$ between Banach spaces there is no determinant, but there is a *determinant line*
$\det(T) = \lambda(\ker T)\otimes\lambda^*(\operatorname{coker}T)$, a one-dimensional space. When $T$ is invertible it is $\mathbb R\otimes\mathbb R^*$, with a canonical vector,
and where that vector lies relative to a chosen orientation of the line plays the role of $\operatorname{sign}\det$. Classically the
lines form a line bundle over the Fredholm operators, and an orientation is carried along the continuous family of
derivatives $Df(x)$. In polyfold theory the linearizations do not depend continuously on the point (the text's opening,
preprint p. 200), and HWZ need three ideas: replace the one operator by the convex set $\mathrm{Lin}(f,x)$ of its sc$^+$-perturbations
(§1); orient the line bundle $\mathrm{DET}$ over this set (§§2–4); and carry orientations along a path by stabilizing with
finitely many sc$^+$-sections, which turns the linearizations along the path into a continuous family of kernels after all
(§5). The result is a functor on the category of paths and the notion of an oriented sc-Fredholm section (§6); the
solution set of a generic perturbation is then an oriented compact manifold (Theorem 6.6.18 (preprint 6.41)), and integrals over it are
invariants (Theorem 6.7.1 (preprint 6.43), §7).

The formalization changed the text: Lemma 6.10 (preprint; not in the 2021 edition) is proved by another construction (§3); along a family, the isomorphism
of formula (94) is used with the sign $(-1)^{\dim\operatorname{coker}T}$, without which it does not vary continuously as we read it,
and so is the map of Remark 6.6.19 (preprint 6.42) (§§5, 6); Proposition 6.6.3 (1) (preprint 6.28) is replaced by a weaker (1′), and orientable
neighbourhoods by pairs $V\subseteq U$ (§5); the chart-free objects $T_xX$, $Y_x$, $\mathrm{Lin}(f,x)$, $\mathrm{Or}^f_x$ are made in charts and compared
(§§1, 6); the omitted proofs of Lemma 6.6.4 (preprint 6.29), of the "simple computation" of Lemma 6.6.8 (preprint 6.33), of the covering argument of
Theorem 6.6.13 (preprint 6.37) and of the equivalence of Definitions 6.6.14 and 6.6.15 (preprint 6.38 and 6.39) are supplied (§§5, 6); Theorem 6.6.18 (preprint 6.41) is proved in the form
of tangent orientations (§6); §6.7 (preprint §6.6) and Theorem 6.7.1 (preprint 6.43) are not formalized (§7). §9 treats the bead as an sc-Fredholm problem
and computes its determinant lines by hand.

## 1. Linearizations and the index (pp. 237–242 (preprint pp. 200–203))

At a smooth zero $x$ of an sc-smooth section $f$ the linearization $f'(x) = P_x\circ Tf(x):T_xX\to Y_x$ is defined (Chapter 3). At a
smooth point with $f(x)\ne0$ HWZ subtract an sc$^+$-section through $f(x)$: in a strong bundle chart with retraction $R$, the
section $s(y) = R(y,f(x))$ is sc$^+$ because $f(x)$ is a smooth point, and $(f-s)'(x)$ is defined.

*How this is read.* $T_xX$ carries no linear structure in the project; it is read in a chart (gaps G.6, G.7, G.13).
Everything is done at a *chart point* $p = (c,z)$: a strong bundle chart $c$ of the atlas at $x$, with base retract $O = r(V)$
in a partial quadrant $C\subseteq E$ and fibre retractions $\rho(y)$ on $F$, and the image $z\in O$ of $x$. The tangent space is $T_zO = Dr(z)E$,
the fibre is $K_z = \rho(z)F$, and the linearization $(f+s)'(x):T_zO\to K_z$, for $(f+s)(x) = 0$, is the derivative at $z$ of the principal
part of $f+s$ composed with $r$, restricted to $T_zO$, on level $0$. The sc$^+$-sections are global. From §6.3 (preprint §6.2) on the text
assumes sc-smooth partitions of unity (preprint p. 203); what is used of them is sc-smooth bump functions (V5.49): a bump
function equal to $1$ near $x$ and supported in the chart domain turns the chart section $R(y,e)$ into a global sc$^+$-section
through any smooth $e\in Y_x$ (Findings, item 43).

If $s$ and $t$ are sc$^+$-sections with $(f+s)(x) = (f+t)(x) = 0$, then $(f+s)'(x) = (f+t)'(x)+(s-t)'(x)$ and $(s-t)'(x)$ is an sc$^+$-operator,
compact on every level; so one linearization is Fredholm if and only if the other is, with the same index. (The text, preprint p. 201, says that "$(f-s)'(x)$ is a sc-Fredholm operator if and only if $(f-s)'(x)$ is", comparing it with itself where
$(f-t)'(x)$ is meant: a possible misprint (Findings, item 41).)

**Definition 6.2.1 (preprint 6.1)** *(book 2017: Definition 6.1, p. 182).* For an sc-Fredholm section $f$ and a smooth point $x$, read at a
chart point,
$$\mathrm{Lin}(f,x) = \{(f+s)'(x)+a\mid a:T_zO\to K_z\ \text{an sc}^+\text{-operator}\},$$
for an sc$^+$-section $s$ with $(f+s)(x) = 0$; by the remark above it does not depend on $s$. The *index* $\mathrm{ind}(f,x)$ is the Fredholm
index of any member.

**Lemma 6.A.** The members of $\mathrm{Lin}(f,x)$ are Fredholm on level $0$, all of index $\mathrm{ind}(f,x)$; $\mathrm{Lin}(f,x)$ is convex; and it is not
empty when $P$ has sc$^+$-sections through the smooth points of its fibres, in particular when $X$ has sc-smooth bump functions.

*Proof.* An sc-Fredholm section has, at a smooth point, an sc$^+$-section $s$ with $(f+s)(x) = 0$ and $(f+s)'(x)$ Fredholm of index
$\mathrm{ind}(f,x)$ on level $0$ in every chart (Chapter 3, V3.98); adding a compact operator keeps both. Sc$^+$-operators form a linear
space, and $(1-\tau)(L+a)+\tau(L+b) = L+((1-\tau)a+\tau b)$. Nonemptiness needs one section through the smooth point $-f(x)$, which bump
functions give as above. $\square$

The text also calls the members sc-Fredholm on every level; what the determinant lines use is level $0$, and the
statement on every level is not formalized (gap G.64; Findings, item 40). *Checked by machine (V6.1):*
`Polyfold.ChartPoint`, `Polyfold.ChartPoint.T`, `Polyfold.ChartPoint.K`, `Polyfold.ChartPoint.linSet`,
`Polyfold.ChartPoint.mem_linSet_iff`, `Polyfold.ChartPoint.isFredholm_isIndexAt_of_mem_linSet`,
`Polyfold.ChartPoint.fredholmIndex_of_mem_linSet`, `Polyfold.ChartPoint.convex_linSet`,
`Polyfold.ChartPoint.linSet_nonempty`, `Polyfold.MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`.

Before Proposition 6.2.2 (preprint 6.2) the text recalls that an M-polyfold is locally path connected and that two smooth points in one
path component are joined by an sc$^+$-smooth path. Neither is formalized; only the local form inside a chart is (§5), and
"in the same path component" is read throughout as "joined by an sc-smooth path" (gap G.56; Findings, item 42).

**Proposition 6.2.2 (preprint 6.2) (stability of the index)** *(book 2017: Proposition 6.1, p. 183).* Let $X$ be tame and $f$ sc-Fredholm.
If the smooth points $x_0$, $x_1$ are joined by an sc-smooth path $\varphi$, then $\mathrm{ind}(f,x_0) = \mathrm{ind}(f,x_1)$.

*Proof.* It suffices that $t\mapsto\mathrm{ind}(f,\varphi(t))$ is locally constant. The linearizations along $\varphi$ need not vary continuously, so
HWZ pass to a parametrized problem. Fix $t_0$. On $\mathbb R\times X$ (the text's $[0,1]\times X$) take an sc$^+$-section $S$ of the pull-back
of $P$ with $f(\varphi(t))+S(t,\varphi(t)) = 0$ for $t$ near $t_0$ (in a chart, $S(t,y) = -R(y,f(\varphi(t)))$). Let $T_0 = (f+S(t_0,\cdot))'(\varphi(t_0))$. Choose smooth
$e_1,\dots,e_m$ spanning a complement of $R(T_0)$, and smooth $p_1,\dots,p_r$ spanning the image under $T_0$ of a smooth finite-dimensional
subspace with an sc-complement in the reduced tangent space; take sc$^+$-sections $s_i$ with these values at $(t_0,\varphi(t_0))$ and
$$F(\lambda,t,y) = f(y)+S(t,y)+\textstyle\sum_{i=1}^{m+r}\lambda_is_i(t,y).$$
Its linearization at $(0,t_0,\varphi(t_0))$ is onto (the $e_i$), with kernel in good position (the $p_i$). By the implicit function
theorem (Theorem 3.6.8 (preprint 3.54)) the zeros of $F$ near $(0,t_0,\varphi(t_0))$ form a manifold $S_F$ containing $(0,t,\varphi(t))$ for $t$ near $t_0$, with
$T S_F = \ker F'$ and $F'$ onto there. So $\dim T_{(0,t,\varphi(t))}S_F = \mathrm{ind}\,F'(0,t,\varphi(t))$ is locally constant in $t$, and this index is
$\mathrm{ind}(f,\varphi(t))$ plus the number of added parameters. $\square$

The formalization, for $f$ with tame germ data (the reading of tameness of Chapter 3), runs this argument on the
restriction of $P$ to the domain of a chart around $\varphi(t_0)$, where the text's
sections need no cut-off, with the path on $\mathbb R$; the local reading of the index needs no bump functions, the global one
does. *Checked by machine (V3.98, with Chapter 3):* `Polyfold.StrongBundle.IsIndexAt`,
`Polyfold.proposition_6_2_local`, `Polyfold.proposition_6_2`.

## 2. Determinant lines and exact sequences (pp. 241–246 (preprint pp. 203–207))

In this section all spaces are finite-dimensional and real. HWZ fix their conventions with care, since "natural"
isomorphisms of different authors differ by signs (preprint p. 203). $\lambda(E) = \Lambda^{\max}E$ is a line, and $\lambda^*(E)$ is its dual. A change of basis
multiplies the wedge of a basis by its determinant, also in one block of a two-block wedge; and adding to the vectors of
one block vectors from the span of the other block does not change the wedge (expand by multilinearity: every new term
repeats a vector). For $v\ne0$ in a line, $v^*$ is the functional with $v^*(v) = 1$, so $(cv)^* = c^{-1}v^*$. For $\dim E = \dim F$ and $\Phi:E\to F$,
$\lambda(\Phi)(a_1\wedge\dots\wedge a_n) = \Phi a_1\wedge\dots\wedge\Phi a_n$; then $\lambda(\Psi\Phi) = \lambda(\Psi)\lambda(\Phi)$, and $\lambda(\Phi)\ne0$ if and only if $\Phi$ maps a basis to a basis, that is, is
bijective. $\lambda^*(\Phi):\lambda^*(F)\to\lambda^*(E)$ is the dual of $\lambda(\Phi)$. *Checked by machine (V6.2):* `Polyfold.maxPow`,
`Polyfold.maxPowDual`, `Polyfold.wedge_eq_det_smul`, `Polyfold.wedge_append_add_left`,
`Polyfold.wedge_append_add_right`, `Polyfold.dualVec_self`, `Polyfold.maxPowMap_comp`,
`Polyfold.maxPowMap_ne_zero_iff`, `Polyfold.maxPowDualMap`.

**Definition 6.3.1 (preprint 6.3)** *(book 2017: Definition 6.2, p. 185).* For $n = \dim E$, $\iota:\lambda(E^*)\to\lambda^*(E)$ is given by
$$\iota(e_1^*\wedge\dots\wedge e_n^*)(a_1\wedge\dots\wedge a_n) = \det(e_i^*(a_j)),$$
with $\lambda(\{0\}^*) = \mathbb R$ for $n = 0$. The right-hand side is alternating and multilinear in the $a_j$ and in the $e_i^*$, so $\iota$ is a well-defined
linear map of lines. For a basis $e_1,\dots,e_n$ and its dual basis, $\det(e_i^*(e_j)) = 1$, so $\iota(e_1^*\wedge\dots\wedge e_n^*) = (e_1\wedge\dots\wedge e_n)^*$ and $\iota\ne0$. The
text's matrix is the transpose of Mathlib's, with the same determinant. *Checked by machine (V6.3):* `Polyfold.iotaDual`,
`Polyfold.iotaDual_wedge_wedge`, `Polyfold.iotaDual_wedge_dualBasis`, `Polyfold.iotaDual_ne_zero`.

**Proposition 6.3.2 (preprint 6.4)** *(book 2017: Proposition 6.2, p. 185).* For an isomorphism $\Phi:E\to F$, $\lambda^*(\Phi)\circ\iota = \iota\circ\lambda(\Phi^*)$ as maps $\lambda(F^*)\to\lambda^*(E)$.

*Proof.* Take a basis $f_i$ of $F$ and $e_i = \Phi^{-1}f_i$; the dual basis of $E^*$ is $e_i^* = f_i^*\circ\Phi = \Phi^*f_i^*$. Then
$(\lambda^*(\Phi)\iota(f_1^*\wedge\dots\wedge f_n^*))(e_1\wedge\dots\wedge e_n) = (f_1\wedge\dots\wedge f_n)^*(f_1\wedge\dots\wedge f_n) = 1$ and $\iota(\lambda(\Phi^*)(f_1^*\wedge\dots\wedge f_n^*))(e_1\wedge\dots\wedge e_n) = \iota(e_1^*\wedge\dots\wedge e_n^*)(e_1\wedge\dots\wedge e_n) = 1$.
Two linear maps of lines that agree on a nonzero vector are equal. $\square$ *Checked by machine (V6.4):*
`Polyfold.proposition_6_4`.

**Four-term exact sequences.** Let $\mathcal E: 0\to A\xrightarrow{\alpha}B\xrightarrow{\beta}C\xrightarrow{\gamma}D\to0$ be exact, with $n = \dim A$, $m = \dim B$, $l = \dim D$. A *choice* consists of
complements $Z$ of $\alpha(A)$ in $B$ and $V$ of $\beta(B)$ in $C$, bases $a_1,\dots,a_n$ of $A$ and $d_1,\dots,d_l$ of $D$, a basis $b'_1,\dots,b'_{m-n}$ of $Z$, and the
vectors $c_i\in V$ with $\gamma(c_i) = d_i$; put $c'_j = \beta(b'_j)$. Then $\alpha(a),b'$ is a basis of $B = \alpha(A)\oplus Z$; $\beta|_Z$ is an isomorphism onto $\beta(B)$
(its kernel is $Z\cap\alpha(A) = 0$), so the $c'_j$ are a basis of $\beta(B)$; $\gamma|_V$ is an isomorphism onto $D$ (its kernel is $V\cap\beta(B) = 0$, and $\gamma$ is
onto), so the $c_i$ are a basis of $V$, and $c,c'$ is a basis of $C$. HWZ define $\Phi_{\mathcal E}:\lambda(A)\otimes\lambda^*(D)\to\lambda(B)\otimes\lambda^*(C)$ by
$$\Phi_{\mathcal E}\big((a_1\wedge\dots\wedge a_n)\otimes(d_1\wedge\dots\wedge d_l)^*\big) = (\alpha(a_1)\wedge\dots\wedge\alpha(a_n)\wedge b'_1\wedge\dots\wedge b'_{m-n})\otimes(c_1\wedge\dots\wedge c_l\wedge c'_1\wedge\dots\wedge c'_{m-n})^*,\tag{91}$$
with two conventions: the $b'$ come after the $\alpha(a)$, and the $c'$ after the $c$. For one choice, (91) on the one generator
defines a linear map of lines, nonzero, hence an isomorphism. *Checked by machine (V6.5):* `Polyfold.FourTermExact`,
`Polyfold.FourTermExact.Choice`, `Polyfold.FourTermExact.canonicalChoice`, `Polyfold.FourTermExact.phi`,
`Polyfold.FourTermExact.phi_ne_zero`, `Polyfold.FourTermExact.phiEquiv`.

**Lemma 6.3.3 (preprint 6.5)** *(book 2017: Lemma 6.1, p. 187).* $\Phi_{\mathcal E}$ does not depend on the choices: the map defined by (91) for one choice
satisfies (91) for every choice.

The proof is the text's Appendix 6.8.1 (preprint 6.7.1), given in §8. "Does not depend on the choices" is read in this strongest form,
which every later evaluation of $\gamma^P_T$ uses, each with its own choices (Findings, item 1). *Checked by machine (V6.6):*
`Polyfold.FourTermExact.lemma_6_5`.

**Proposition 6.3.5 (preprint 6.6)** *(book 2017: Proposition 6.3, p. 188).* Let $\bar\iota(v\otimes b\otimes\phi) = \phi(v)\,b$ on $\lambda(C)\otimes\lambda(B)\otimes\lambda^*(C)$ and
$\Psi_{\mathcal E}(c\otimes h) = \bar\iota(c\otimes\Phi_{\mathcal E}(h))$, formula (92). In the notation of (91),
$$\Psi_{\mathcal E}\big((c_1\wedge\dots\wedge c_l\wedge c'_1\wedge\dots\wedge c'_{m-n})\otimes(a_1\wedge\dots\wedge a_n)\otimes(d_1\wedge\dots\wedge d_l)^*\big) = \alpha(a_1)\wedge\dots\wedge\alpha(a_n)\wedge b'_1\wedge\dots\wedge b'_{m-n}.$$

*Proof.* With $\mathbf c$ and $\mathbf b$ the two wedges of (91), $\Phi_{\mathcal E}(a\otimes d^*) = \mathbf b\otimes\mathbf c^*$, and $\bar\iota(\mathbf c\otimes\mathbf b\otimes\mathbf c^*) = \mathbf c^*(\mathbf c)\,\mathbf b = \mathbf b$. $\square$

The statement in the text writes the wedge in $C$ as $c'_1\wedge\dots\wedge c'_l\wedge c_1\wedge\dots\wedge c_{m-n}$, exchanging the names of its two blocks; the order
of (91) is meant (possible misprint) (Findings, item 2). *Checked by machine (V6.7):* `Polyfold.contractDual`,
`Polyfold.FourTermExact.psi`, `Polyfold.FourTermExact.proposition_6_6`.

## 3. The determinant of a Fredholm operator (pp. 244–258 (preprint pp. 207–214))

From here $E$, $F$ are real Banach spaces, $T:E\to F$ is bounded and Fredholm, $R(T)$ is its range and $\operatorname{coker}T = F/R(T)$.

**Definition 6.4.1 (preprint 6.7)** *(book 2017: Definition 6.3, p. 189).* $\det(T) = \lambda(\ker T)\otimes\lambda^*(F/R(T))$, a line. Equal operators have identified
determinants, which matters because $PQT$ and $PT$ below are equal operators written differently. The alternative
$\lambda(\ker T)\otimes\lambda(\operatorname{coker}(T)^*)$ mentioned after the definition is not formalized (gap G.57; Findings, item 10).
*Checked by machine (V6.8):* `Polyfold.linDet`, `Polyfold.fredholmDet`, `Polyfold.finrank_fredholmDet`,
`Polyfold.linDetEquivOfEq`.

**Definition 6.4.2 (preprint 6.8)** *(book 2017: Definition 6.4, p. 189).* An orientation of $T$ is an orientation of $\det(T)$: a ray, one of the
two components of $\det(T)\setminus0$. *Checked by machine (V6.9):* `Polyfold.FredholmOrientation`,
`Polyfold.nonempty_fredholmOrientation`, `Polyfold.exists_two_fredholmOrientation`.

**Definition 6.4.3 (preprint 6.9)** *(book 2017: Definition 6.5, p. 189).* A *good left-projection* for $T$ is a bounded projection $P:F\to F$ with
(1) $\dim F/R(P)<\infty$ and (2) $R(PT) = R(P)$. $\Pi_T$ is the set of them, ordered by $P\le Q$ if and only if $P = PQ = QP$.

The facts stated after the definition, with proofs. (a) $P$ is Fredholm of index $0$: $F = R(P)\oplus\ker P$, so $\ker P\cong F/R(P)$. (b) $PT$ is
Fredholm with $\mathrm{ind}(PT) = \mathrm{ind}(P)+\mathrm{ind}(T) = \mathrm{ind}(T)$. (c) $\le$ is a partial order: $P = PP$; if $P\le Q\le P$ then $P = PQ = Q$; if $P\le Q\le R$
then $PR = PQR = PQ = P$ and $RP = RQP = QP = P$. (d) $R(P)\cap R(P')$ has finite codimension, since $F/(R(P)\cap R(P'))$ embeds in
$F/R(P)\times F/R(P')$. (e) $\Pi_T\ne\emptyset$: the projection onto the closed subspace $R(T)$ along a finite-dimensional complement satisfies
$R(PT) = R(T) = R(P)$. The text uses (e) from Proposition 6.4.10 (preprint Lemma 6.11) on without stating it (Findings, item 3). *Checked by machine
(V6.10):* `Polyfold.IsGoodLeftProj`, `Polyfold.goodLeftProjs`, `Polyfold.ProjLE`, `Polyfold.ProjLE.trans`,
`Polyfold.IsGoodLeftProj.fredholmIndex_eq_zero`, `Polyfold.IsGoodLeftProj.fredholmIndex_comp`,
`Polyfold.IsGoodLeftProj.finiteDimensional_quotient_inf`, `Polyfold.exists_isGoodLeftProj`.

**Lemma 6.10 (preprint; not in the 2021 edition)** *(book 2017: dropped; see Remarks 6.2–6.3, p. 190).* For $P,P'\in\Pi_T$ there is $P''\in\Pi_T$ with $P''\le P$ and $P''\le P'$. This
holds for every bounded $T$, Fredholm or not.

> **The text's projection is not below $P$ and $P'$, as we read it.** The proof takes complements $X$, $X'$ of $R(P)\cap R(P')$ in
> $R(P)$, $R(P')$, a complement $Z$ of $X\oplus X'\oplus(R(P)\cap R(P'))$, and $P''$ the projection onto $R(P)\cap R(P')$ along $Z\oplus X\oplus X'$. But $P''P = P''$
> says that $P''$ vanishes on $\ker P$, which nothing arranges. On $\mathbb R^2$ with $T = 1$, let $P$ project onto the $x$-axis along the
> $y$-axis and $P'$ onto the $x$-axis along the diagonal; both lie in $\Pi_T$ and $R(P)\cap R(P')$ is the $x$-axis. A projection $Q$
> onto the $x$-axis with $QP = Q$ and $QP' = Q$ would vanish on the $y$-axis and on the diagonal, hence on $\mathbb R^2$. So no
> projection with range $R(P)\cap R(P')$ lies below both. The 2017 version drops the lemma and remarks that a common lower
> bound need not exist; with the order of Definition 6.4.3 (preprint 6.9) one always exists, with a smaller range, and the preprint's
> route to Lemma 6.5.9 (preprint 6.25) is the one formalized (Findings, item 4).

*Proof.* $\ker P\cong F/R(P)$ and $\ker P'$ are finite-dimensional, so $K = \ker P+\ker P'$ is finite-dimensional, hence closed and
complemented: $F = K\oplus N$ with $N$ closed of finite codimension. $R'' = R(P)\cap R(P')\cap N$ is closed of finite codimension and $R''\cap K = 0$;
choose a finite-dimensional complement $C'$ of the closed subspace $R''\oplus K$ and let $P''$ be the projection onto $R''$ along $C = K\oplus C'$,
bounded since $C$ is closed. For $y\in F$, $y-Py\in\ker P\subseteq C$, so $P''y = P''Py$; and $PP'' = P''$ because $R''\subseteq R(P)$. So $P''\le P$, and likewise
$P''\le P'$. Finally $\dim F/R''<\infty$ and $P''T = P''PT$, so $R(P''T) = P''(R(PT)) = P''(R(P)) = R''$: the inclusion $\subseteq$ is clear, and $\supseteq$ holds because
$P''$ fixes $R''\subseteq R(P)$. $\square$

In the example, $K = \mathbb R^2$ and $P'' = 0$, which is a good left-projection for $T = 1$. *Checked by machine (V6.11):*
`Polyfold.lemma_6_10`, `Polyfold.lemma_6_10_text_reading`.

**Proposition 6.4.10 (preprint Lemma 6.11)** *(book 2017: Proposition 6.4, p. 192).* For $P\in\Pi_T$ the sequence
$$E(T,P):\ 0\to\ker T\xrightarrow{j}\ker(PT)\xrightarrow{\Phi^P_T}F/R(P)\xrightarrow{\pi^P_T}\operatorname{coker}T\to0,$$
with the inclusion $j$, $\Phi^P_T(x) = Tx+R(P)$ and $\pi^P_T(y+R(P)) = (I-P)y+R(T)$, is exact.

*Proof.* $\pi^P_T$ is well defined since $(I-P)$ vanishes on $R(P)$. $j$ is injective and $\Phi^P_Tj = 0$. If $\Phi^P_T(x) = 0$, then $Tx\in R(P)$, so $Tx = PTx = 0$.
For $x\in\ker(PT)$, $\pi^P_T\Phi^P_T(x) = Tx-PTx+R(T) = R(T)$. If $\pi^P_T(y+R(P)) = 0$, say $(I-P)y = Tx$, then $PTx = P(I-P)y = 0$, so $x\in\ker(PT)$ and
$\Phi^P_T(x) = (I-P)y+R(P) = y+R(P)$. Onto: given $f$, choose $x$ with $PTx = Pf$ (by $R(PT) = R(P)$); then $\pi^P_T(f-Tx+R(P)) = f-Pf-Tx+PTx+R(T) = f+R(T)$. $\square$
*Checked by machine (V6.12):* `Polyfold.projSeqPhi`, `Polyfold.projSeqPi`, `Polyfold.lemma_6_11`, `Polyfold.projSeq`.

**The isomorphisms $\gamma^P_T$.** Since $R(PT) = R(P)$, $F/R(P)$ is $\operatorname{coker}(PT)$, and $\Phi_{E(T,P)}$ is an isomorphism $\gamma^P_T:\det(T)\to\det(PT)$, given on
wedges by (91) for any choice (Lemma 6.3.3 (preprint 6.5)). The text's "recalling $R(P) = R(PT)$" is read as this identification (Findings,
item 5). *Checked by machine (V6.13):* `Polyfold.gammaProj`, `Polyfold.gammaProj_tmul`, `Polyfold.gammaProj_wedge_tmul`.

**Proposition 6.4.11 (preprint 6.12)** *(book 2017: Proposition 6.5, p. 193).* If $P\le Q$ in $\Pi_T$, then $QT$ is Fredholm, $P\in\Pi_{QT}$, and
$\gamma^P_{QT}\circ\gamma^Q_T = \gamma^P_T$, up to the identification $\det(PQT) = \det(PT)$ of the equal operators $PQT = PT$.

*Proof.* $QT$ is Fredholm by (b), and $R(P(QT)) = R(PT) = R(P)$ since $PQ = P$. The identity is the computation of the text's Appendix
6.8.2 (preprint 6.7.2), given in §8. $\square$ *Checked by machine (V6.14):* `Polyfold.proposition_6_12`, `Polyfold.IsGoodLeftProj.of_projLE`,
`Polyfold.comp_comp_eq_of_projLE`.

**Corollary 6.4.12 (preprint 6.13)** *(book 2017: Corollary 6.1, p. 193).* If $P\le S$ and $P\le R$ in $\Pi_T$, then $(\gamma^P_{RT})^{-1}\circ\gamma^P_{ST} = \gamma^R_T\circ(\gamma^S_T)^{-1}$; in particular the
left side does not depend on $P$.

*Proof.* By Proposition 6.4.11 (preprint 6.12), $\gamma^P_{RT}\gamma^R_T = \gamma^P_T = \gamma^P_{ST}\gamma^S_T$; solve for $(\gamma^P_{RT})^{-1}\gamma^P_{ST}$. $\square$ *Checked by machine (V6.15):* `Polyfold.corollary_6_13`.

**Stabilization.** For $\varphi:\mathbb R^n\to F$ linear with $T_\varphi(e,r) = Te+\varphi(r)$ onto, consider
$$0\to\ker T\xrightarrow{j}\ker T_\varphi\xrightarrow{\pi}\mathbb R^n\xrightarrow{[\varphi]}F/R(T)\to0,\qquad j(e) = (e,0),\ \pi(e,r) = r,\ [\varphi](r) = \varphi(r)+R(T).$$
$\mathbb R^n$ is written after $E$, in keeping with the conventions of (91), and is oriented by its standard basis.

**Lemma 6.4.14 (preprint 6.14)** *(book 2017: Lemma 6.6, p. 199).* This sequence is exact, and every Fredholm $T$ has a stabilization.

*Proof.* $j$ is injective with $\pi j = 0$; if $\pi(e,r) = r = 0$, then $Te = 0$ and $(e,r) = j(e)$ (the text writes "$j(e) = (0,e)$", a possible misprint
(Findings, item 8)). For $(e,r)\in\ker T_\varphi$, $\varphi(r) = -Te\in R(T)$, so $[\varphi]\pi = 0$; if $[\varphi](r) = 0$, then $\varphi(r) = T(-e)$ for some $e$, and $(e,r)\in\ker T_\varphi$ with
$\pi(e,r) = r$. $[\varphi]$ is onto because $T_\varphi$ is. A stabilization: send the standard basis to representatives of a basis of $\operatorname{coker}T$. $\square$
*Checked by machine (V6.16):* `Polyfold.stabJ`, `Polyfold.stabPi`, `Polyfold.stabClass`, `Polyfold.lemma_6_14`,
`Polyfold.stabSeq`, `Polyfold.exists_surjective_coprod`.

**Formula (94).** $\psi:\lambda^*(\mathbb R^n)\to\lambda^*(\{0\}) = \mathbb R^*$ sends $(e_1\wedge\dots\wedge e_n)^*$, for the standard basis, to $1^*$; for every basis,
$$\psi\big((c_1\wedge\dots\wedge c_n)^*\big) = \det[c_1,\dots,c_n]^{-1}\,1^*,\tag{94}$$
because $c_1\wedge\dots\wedge c_n = \det[c]\,e_1\wedge\dots\wedge e_n$. *Checked by machine (V6.17):* `Polyfold.stdWedge`, `Polyfold.stabPsi`, `Polyfold.stabPsi_dualVec`.

**Proposition 6.4.15 (preprint 6.15)** *(book 2017: Proposition 6.7, p. 199).* $\iota_\varphi = (1\otimes\psi)\circ\Phi_{\mathcal E}:\det(T)\to\lambda(\ker T_\varphi)\otimes\lambda^*(\{0\}) = \det(T_\varphi)$ is an isomorphism.
If $a_1,\dots,a_k$ is a basis of $\ker T$, $\bar c_1,\dots,\bar c_m\in\mathbb R^n$ are such that the $\bar d_i = \varphi(\bar c_i)+R(T)$ form a basis of $F/R(T)$, $h = (a_1\wedge\dots\wedge a_k)\otimes(\bar d_1\wedge\dots\wedge\bar d_m)^*$,
and $\bar b_i = (b_i,r_i)$, $i\le l$, complete the $(a_j,0)$ to a basis of $\ker T_\varphi$, then $r_1,\dots,r_l,\bar c_1,\dots,\bar c_m$ is a basis of $\mathbb R^n$ and
$$\iota_\varphi(h) = \det(\bar c_1,\dots,\bar c_m,r_1,\dots,r_l)^{-1}\,\big((a_1,0)\wedge\dots\wedge(a_k,0)\wedge\bar b_1\wedge\dots\wedge\bar b_l\big)\otimes1^*.$$

*Proof.* $\operatorname{coker}T_\varphi = 0$, so $\det(T_\varphi) = \lambda(\ker T_\varphi)\otimes\lambda^*(\{0\})$. Apply (91) with $A = \ker T$, $B = \ker T_\varphi$, $C = \mathbb R^n$, $D = F/R(T)$: the complement
$Z$ is spanned by the $\bar b_i$, its $\beta$-images are the $r_i = \pi(\bar b_i)$, which form a basis of $\pi(\ker T_\varphi)$, and the $\bar c_i$ span a complement $V$ of it,
being $\gamma$-preimages of a basis of $D$. So $\Phi_{\mathcal E}(h) = ((a,0)\wedge\bar b)\otimes(\bar c\wedge r)^*$, and (94) gives the factor. By exactness
$n = \dim\pi(\ker T_\varphi)+\dim\operatorname{coker}T = l+m$, so $\det(\bar c,r)$ is a square determinant. $\square$

The identity $m+l = n$, which the formula needs, is proved to hold always, and so is the fact that the $r_i$ and $\bar c_j$ form a basis,
which the text notices; the statement calls $\psi$ "$\varphi$" (possible misprint) (Findings, item 9). The identification (95) and the
maps $V\otimes\lambda(\mathbb R^n)\to V$, $V\otimes\lambda^*(\mathbb R^n)\to V$ after the proposition are not formalized; only (94) is used (gap G.58; Findings, item 10).
*Checked by machine (V6.18):* `Polyfold.stabIota`, `Polyfold.stabIota_bijective`, `Polyfold.stab_card_eq`,
`Polyfold.isCompl_range_stabPi_span`, `Polyfold.proposition_6_15`.

**Definition 6.4.16 (preprint 6.16)** *(book 2017: Definition 6.7, p. 200).* $T\oplus S:E\times E'\to F\times F'$ is Fredholm, with $\ker(T\oplus S)\cong\ker T\times\ker S$ and
$\operatorname{coker}(T\oplus S)\cong\operatorname{coker}T\times\operatorname{coker}S$, and $\det(T)\otimes\det(S)\to\det(T\oplus S)$ sends $h\otimes h'$, $h = a\otimes d^*$, $h' = a'\otimes d'^*$, to $(a\wedge a')\otimes(d\wedge d')^*$. A change
of the bases multiplies both sides by the same factor, so the map is well defined; "natural" is read as this formula for
every choice of bases, as in Lemma 6.3.3 (preprint 6.5) (Findings, item 11). *Checked by machine (V6.19):* `Polyfold.kerProdEquiv`,
`Polyfold.cokerProdEquiv`, `Polyfold.isFredholm_prodMap`, `Polyfold.directSumDet`, `Polyfold.definition_6_16`,
`Polyfold.directSumDet_bijective`.

## 4. The determinant bundle (pp. 258–263 (preprint pp. 214–219))

The kernels and cokernels of Fredholm operators jump in dimension, so $\bigcup_S\{S\}\times\det(S)$ has no obvious topology. The
good left-projections fix this: near $T$, the operators $PS$ have kernels of constant dimension and the constant cokernel
$F/R(P)$, and $\gamma^P_S$ carries $\det(S)$ to $\det(PS)$.

**Lemma 6.5.1 (preprint 6.17)** *(book 2017: Lemma 6.7, p. 201).* Let $T$ be bounded, $P\in\Pi_T$ and $Y$ a topological complement of $\ker(PT)$ in $E$. There is
$\varepsilon>0$ such that for $\|S-T\|<\varepsilon$: (1) $P\in\Pi_S$; (2) $PS|_Y:Y\to R(P)$ is a topological isomorphism.

*Proof.* $PT|_Y:Y\to R(P)$ is injective, as $Y\cap\ker(PT) = 0$, and onto, as $PT(E) = PT(Y)$ and $R(PT) = R(P)$; $R(P)$ is closed, so it is a topological
isomorphism by the open mapping theorem. Since $\|PS|_Y-PT|_Y\|\le\|P\|\,\|S-T\|$ and the invertible operators $Y\to R(P)$ form an open set, (2)
holds for small $\varepsilon$. Then $R(PS)\supseteq PS(Y) = R(P)$, and $R(PS)\subseteq R(P)$ always: (1). $\square$

The hypothesis that $T$ is Fredholm is not used; a topological complement is an algebraic complement with a continuous
projection (Findings, item 20). *Checked by machine (V6.20):* `Polyfold.FredholmOp`, `Polyfold.projRestrict`,
`Polyfold.lemma_6_17`.

**Lemma 6.5.2 (preprint 6.18)** *(book 2017: Lemma 6.8, p. 201).* With $E = \ker(PT)\oplus Y$, $e = k+y$, put $y(k,S) = -(PS|_Y)^{-1}PSk$. Then $(k,S)\mapsto y(k,S)$ is
continuous, and $(S,k)\mapsto(S,k+y(k,S))$ maps $\{\|S-T\|<\varepsilon\}\times\ker(PT)$ continuously and bijectively onto $\bigcup_{\|S-T\|<\varepsilon}\{S\}\times\ker(PS)$, with
continuous inverse $(S,k+y)\mapsto(S,k)$, the projection onto $\ker(PT)$ along $Y$.

*Proof.* $PS(k+y) = 0$ if and only if $PSy = -PSk$, that is, $y = y(k,S)$. Inversion of operators is continuous, so $y$ is. The inverse is the
restriction of a continuous projection. $\square$

"Is a trivial vector bundle" is stated as this trivialization with its inverse (Findings, item 21). A *local determinant
chart* is the data $(T,P,Y,\varepsilon)$ of Lemma 6.5.1 (preprint 6.17) with its conclusions. *Checked by machine (V6.21):*
`Polyfold.LocalDetChart`, `Polyfold.LocalDetChart.ySol`, `Polyfold.LocalDetChart.kerMap`,
`Polyfold.LocalDetChart.kerProj`, `Polyfold.LocalDetChart.lemma_6_18`.

**Lemma 6.5.3 (preprint 6.19) and Proposition 6.5.4 (preprint 6.20)** *(book 2017: Lemma 6.9, Proposition 6.8, p. 202).* Lemma 6.5.3 (preprint 6.19) says that exterior powers,
duals, sums and tensor products of finite-dimensional topological vector bundles are topological vector bundles; it is
not formalized in general (gap G.59). It is applied only to trivial bundles, and Proposition 6.5.4 (preprint 6.20) (the local determinant
bundle $\mathrm{DET}(T,P,\varepsilon) = \bigcup_{\|S-T\|<\varepsilon}\{S\}\times\det(PS)$ is a topological line bundle) is proved with explicit frames: for a basis $k_1,\dots,k_n$ of
$\ker(PT)$ and a basis $e_1,\dots,e_l$ of $F/R(P) = F/R(PS)$,
$$\omega(S) = \big(k_1(S)\wedge\dots\wedge k_n(S)\big)\otimes(e_1\wedge\dots\wedge e_l)^*,\qquad k_i(S) = k_i+y(k_i,S),$$
is a nowhere-zero frame (the $k_i(S)$ are a basis of $\ker(PS)$ by Lemma 6.5.2 (preprint 6.18)). For two charts with the same $P$ the two kernel frames
are related by a matrix whose entries are continuous (coordinates along a continuous projection), so the frames differ
by its determinant, a continuous nowhere-zero factor; "in a natural way" is read as this relation (Findings, item 22).
*Checked by machine (V6.22):* `Polyfold.LocalDetChart.kerFrame`, `Polyfold.LocalDetChart.frame`,
`Polyfold.LocalDetChart.frame_ne_zero`, `Polyfold.proposition_6_20`.

**Lemma 6.5.5 (preprint 6.21)** *(book 2017: Lemma 6.10, p. 202).* For $Q\le P$, $\gamma^Q_{PS}$ maps the $P$-frame at $S$ to a continuous nowhere-zero multiple of
the $Q$-frame, on the common ball of any two local determinant charts with the projections $P$ and $Q$.

*Proof.* This is the text's sketch, made explicit. The sequence $E(PS,Q)$ is $0\to\ker(PS)\to\ker(QS)\to F/R(Q)\to F/R(P)\to0$, and its last map
$y+R(Q)\mapsto(I-Q)y+R(P)$ does not depend on $S$; so its kernel, the $\beta$-image, is a fixed subspace, and the complement $V$ and the
$\gamma$-preimages $c_i$ of the constant basis $e$ of $F/R(P)$ may be fixed. Near a point $S_0$ choose, among the continuous frame $k^Q(S)$ of
$\ker(QS)$, vectors $b'_j(S)$ that complement $\ker(PS)$ at $S_0$; they still do nearby, an open condition. Then the right-hand side of (91)
for the $P$-frame is a wedge of continuous vectors, and its coordinate in the $Q$-frame is a quotient of two continuous
nonzero functions. $\square$

The lemma is stated for two charts with different centres and radii, the form Lemma 6.5.9 (preprint 6.25) uses (Findings, item 23).
*Checked by machine (V6.23):* `Polyfold.LocalDetChart.gammaProj_frame_eq`, `Polyfold.lemma_6_21`.

**The bundle $\mathrm{DET}(E,F)$.** Its fibre over a Fredholm $S$ is $\det(S)$. A local determinant chart gives the map
$$\gamma_{(T,P,\varepsilon)}:(S,h)\mapsto\big(S,\ \omega(S)^*(\gamma^P_Sh)\big),$$
the coordinate of $\gamma^P_Sh$ in the frame of Proposition 6.5.4 (preprint 6.20), with model fibre $\mathbb R$; every Fredholm operator is the centre of one ($\Pi_T\ne\emptyset$,
and $\ker(PT)$ is finite-dimensional, so it has a topological complement). The text's $\gamma_{(T,P,\varepsilon)}$ maps into $\mathrm{DET}(T,P,\varepsilon)$ and is read
in the frame (Findings, item 24). *Checked by machine (V6.24):* `Polyfold.DetFiber`, `Polyfold.LocalDetChart.pretriv`,
`Polyfold.LocalDetChart.coord`, `Polyfold.exists_localDetChart`.

**Lemma 6.5.9 (preprint 6.25)** *(book 2017: Lemma 6.11, p. 204).* The transition between two charts is $(S,t)\mapsto(S,g(S)t)$ with $g$ continuous and nowhere zero
on the common ball.

*Proof.* At $S_0$ in the common ball, $P,P'\in\Pi_{S_0}$ (Lemma 6.5.1 (preprint 6.17)), so Lemma 6.10 (preprint; not in the 2021 edition) gives $Q\in\Pi_{S_0}$ with $Q\le P$, $Q\le P'$, and a chart with
projection $Q$ around $S_0$. By Corollary 6.4.12 (preprint 6.13) for the operator $S$, $\gamma^{P'}_S(\gamma^P_S)^{-1} = (\gamma^Q_{P'S})^{-1}\gamma^Q_{PS}$, and by Lemma 6.5.5 (preprint 6.21) both factors are, in frames,
multiplications by continuous nowhere-zero functions near $S_0$. $\square$

This is the text's proof; it is where the common lower bound of Lemma 6.10 (preprint) is needed. *Checked by machine (V6.28):*
`Polyfold.lemma_6_25`, `Polyfold.lemma_6_25_local`.

**Definition 6.5.6 (preprint 6.22), Propositions 6.5.7 and 6.5.8 (preprint 6.23 and 6.24)** *(book 2017: Definition 6.8, Propositions 6.9, 6.10, p. 204).* $\mathcal B$ is the
collection of subsets of $\mathrm{DET}(E,F)$ lying over the ball of some chart whose image under it is open in $\text{ball}\times\mathbb R$.
$\mathcal B$ is a basis of a topology, and with it $\mathrm{DET}(E,F)$ is a topological line bundle trivialized by every $\gamma_{(T,P,\varepsilon)}$.

*Proof.* By Lemma 6.5.9 (preprint 6.25) the charts have continuous transitions with continuous inverses, linear on the fibres, and cover
$\mathrm{DET}(E,F)$: they form a vector prebundle. For $B,B'\in\mathcal B$ and a point of $B\cap B'$, its image under the chart of $B$ is the
intersection of an open set with the preimage of an open set under a transition, hence open; this is the basis
property. The topology generated is the one for which each chart is a homeomorphism onto $\text{ball}\times\mathbb R$, which makes
the charts trivializations. $\square$

$\mathrm{DET}(E,F)$ is built as a Mathlib vector prebundle, whose topology and bundle structure are those of the text.
*Checked by machine (V6.24–V6.27):* `Polyfold.detPrebundle`, `Polyfold.detBasis`, `Polyfold.proposition_6_23`,
`Polyfold.proposition_6_24`.

**Example 6.B (the determinant line over $L(\mathbb R,\mathbb R)$).** Let $E = F = \mathbb R$, so the Fredholm operators are the numbers $a$. Take the chart
centred at $T = 0$: $\Pi_0 = \{0\}$, since $R(P\cdot0) = R(P)$ forces $P = 0$; then $\ker(PS) = \mathbb R$, $Y = 0$, $F/R(P) = \mathbb R$, and the frame is $\omega(S) = 1\otimes1^*$ for all $S$,
with any $\varepsilon$. For $a\ne0$, $\det(a) = \lambda(0)\otimes\lambda^*(0)$ has the canonical vector $h_a = 1\otimes1^*$; $E(a,0)$ is $0\to0\to\mathbb R\xrightarrow{\cdot a}\mathbb R\to0\to0$, and (91)
with $b'_1 = 1$, $c'_1 = a$ gives $\gamma^0_a(h_a) = 1\otimes(a)^* = a^{-1}\,\omega$. At $a = 0$, $\gamma^0_0(1\otimes1^*) = 1\otimes1^* = \omega$. So the coordinate of $h_a$ is $1/a$ for $a\ne0$, and
that of $1\otimes1^*\in\det(0)$ is $1$. The section $a\mapsto a\,h_a$ ($a\ne0$), $0\mapsto1\otimes1^*$ has coordinate $1$: it is a continuous frame, and
$$o^+(a) = [\operatorname{sign}(a)\,h_a]\quad(a\ne0),\qquad o^+(0) = [1\otimes1^*]$$
is a continuous orientation of $\mathrm{DET}(\mathbb R,\mathbb R)$, the other one being $-o^+$. At an invertible $a$, $o^+$ is the canonical orientation for $a>0$ and
its opposite for $a<0$: the orientation records the sign of the determinant, as in §0.

The text ends §6.5 (preprint §6.4) by remarking that $\mathrm{DET}(E,F)$ is not orientable, and opens §6.6 (preprint §6.5) with the classical case (the
determinant bundle of a classical Fredholm section over a contractible $U$); neither is formalized (gap G.60; Findings,
item 26).

## 5. Orientations at a point and their local propagation (pp. 262–273 (preprint pp. 219–227))

From here $X$ is tame with sc-smooth bump functions and $f$ is an sc-Fredholm section with tame germ data (Definition
3.6.4 (preprint 3.51)), the standing hypotheses of Chapter 5. An orientation of a topological line bundle is a choice of rays given near
every point by a continuous nowhere-zero section.

**Lemma 6.C (orientations of line bundles).** Over a preconnected base, two orientations that agree on one fibre agree
everywhere. Over a simply connected, locally path-connected base, every orientation of one fibre extends; so over a
nonempty such base there are exactly two orientations. Nonempty convex subsets of normed spaces are such bases.

*Proof.* The rays of the fibres form a two-sheeted covering, the orientation double cover: over a trivializing open set it
is the product with $\{\pm\}$. An orientation is a continuous section of it. The set where two sections agree is open and
closed, which gives the first claim. For the second, the identity of the base lifts through the covering with a
prescribed value at one point, by the lifting criterion, since the base is simply connected and locally path-connected.
A convex set is contractible by straight lines and its intersections with balls are convex. $\square$

The text gives as reason only "since the base space is contractible" (p. 263 (preprint p. 219)); the theorem needed is the lifting
criterion (Findings, item 25). *Checked by machine (V6.29):* `Polyfold.IsLineOrientation`, `Polyfold.LineOrientation`,
`Polyfold.LineOrientation.eq_of_apply_eq`, `Polyfold.OrCover`, `Polyfold.isCoveringMap_orCover`,
`Polyfold.exists_lineOrientation_apply_eq`, `Polyfold.exists_two_lineOrientation`.

**Proposition 6.6.1 (preprint 6.26)** *(book 2017: Proposition 6.11, p. 205).* Over a nonempty convex set $C$ of Fredholm operators the restriction
$\mathrm{DET}(E,F)|_C$ is a topological line bundle with exactly two orientations; in particular $\mathrm{DET}(f,x) = \bigcup_{L\in\mathrm{Lin}(f,x)}\{L\}\times\det(L)$ has two.

*Proof.* Restrict the trivializations of Proposition 6.5.8 (preprint 6.24) and apply Lemma 6.C; $\mathrm{Lin}(f,x)$ is convex and nonempty (Lemma 6.A). $\square$
*Checked by machine (V6.30):* `Polyfold.fredholmIncl`, `Polyfold.DetOn`, `Polyfold.proposition_6_26`.

**Definition 6.6.2 (preprint 6.27)** *(book 2017: Definition 6.9, p. 205).* An orientation of $(f,x)$ is one of the two orientations of $\mathrm{DET}(f,x)$; $\mathrm{Or}^f_x$
is the set of both. HWZ consider the category $\mathcal O_f$ with objects $\mathrm{Or}^f_x = \{o_x,-o_x\}$ and, for points in one path component, the two
bijections as morphisms. For each $L\in\mathrm{Lin}(f,x)$, $o\mapsto o(L)$ is a bijection of $\mathrm{Or}^f_x$ onto the two orientations of $\det(L)$ (Lemma 6.C:
a value determines the orientation). Between two two-element sets there are exactly two bijections, and one value
determines a bijection. The category $\mathcal O_f$ is read through its objects, with bijections as morphisms (Findings, item 44).
*Checked by machine (V6.31):* `Polyfold.ChartPoint.isFredholm_of_mem_linSet`, `Polyfold.ChartPoint.detLin`,
`Polyfold.ChartPoint.Or`, `Polyfold.ChartPoint.exists_two_or`, `Polyfold.ChartPoint.orEquivRay`,
`Polyfold.nonempty_equiv_of_two`, `Polyfold.equiv_eq_of_apply_eq_of_two`.

**Proposition 6.6.3 (preprint 6.28)** *(book 2017: Proposition 6.12, p. 205).* Every point $x$ has open sets $U\subseteq W$ in the domain of one chart of the atlas with:
(1′) any two sc-smooth paths in $U$ with the same end points are sc-smoothly homotopic in $W$ with the end points fixed;
(2) $\{y\in\mathrm{cl}(U)\mid f(y) = 0\}$ is compact; (3) for every sc-smooth family $\Phi:\mathbb R^n\to X$ with $\Phi([0,1]^n)\subseteq W$ there is an sc$^+$-section $S$ of
$\pi^*P\to\mathbb R^n\times X$ with $(f+S)(q,\Phi(q)) = 0$ for $q$ near $[0,1]^n$, depending on $q\in[0,1]^n$ only through $\Phi(q)$; (4) $\pi^*P$ has sc$^+$-sections
through all smooth fibre points.

The text's (1) is "$U$ is sc-smoothly contractible", and its (3) is stated for paths.

> **(1) is not established for $U$, as we read it.** The proof, in a chart where $O = r(V)$ with $V$ convex, contracts $O$ by
> $r(ty)$: for $y\in O\subseteq V$, $ty\in V$, and $r(1y) = y$, $r(0) = 0$. It then takes a smaller convex $V'$ and $U = r(V')$, and calls $U$ contractible.
> But for $y\in U$ the point $r(ty)$ lies in $O$, and in $U$ only if $r(V')\subseteq V'$, which is not stated. What Theorem 6.6.11 (preprint 6.35) uses is that two
> paths in $U$ with the same end points are homotopic in a larger region where (3) still holds, and that is (1′) (gap G.61;
> Findings, item 45).

*Proof.* Work in a chart $c$ at $x$, with chart map $\varphi$ (in this proof only) and $u_0 = \varphi(x)$. By the local compactness of $f$ (Chapter 5) $x$ has a compact neighbourhood $N$ of its
zeros, and a closed neighbourhood $T\subseteq N$. Take $\delta>0$ with the ball $B_\delta(u_0)$ inside the chart and inside $T$ (read in the chart), and $\delta'\le\delta$
with $C\cap B_{\delta'}(u_0)$ in the domain of $r$ and $r(C\cap B_{\delta'}(u_0))\subseteq B_\delta(u_0)$, by continuity of $r$ at $u_0 = r(u_0)$; let $W$ and $U$ be the points whose images lie in $B_\delta$, $B_{\delta'}$. (1′): for
paths $\gamma_0,\gamma_1$ in $U$ from $x_0$ to $x_1$, the convex combination $(1-\rho(\tau))\varphi(\gamma_0(t))+\rho(\tau)\varphi(\gamma_1(t))$, $\rho$ the smooth transition function, lies
in the convex set $C\cap B_{\delta'}$; so
$$\Phi(\tau,t) = \varphi^{-1}\Big(r\big((1-\rho(\tau))\varphi(\gamma_0(t))+\rho(\tau)\varphi(\gamma_1(t))\big)\Big)$$
lies in $W$, is $\gamma_i$ on the edges, fixes the end points (where the combination is $\varphi(x_i)\in O$, fixed by $r$), and is sc-smooth as a
composite of sc-smooth maps. Since the paths are defined on $\mathbb R$ and only $[0,1]$ is mapped into $U$, the parameter is first
reparametrized by a $C^\infty$ map equal to the identity near $[0,1]$ and keeping both paths in $U$. (2): $\mathrm{cl}(U)\subseteq T\subseteq N$, and the zeros
in $\mathrm{cl}(U)$ form a closed subset of the compact $N$. (3): the text's section is $s(y,t) = R(y,f(\varphi(t)))$ in the chart; here
$S(q,y) = -\beta(y)R(y,f(\Phi(q)))$, read in the chart, with $\beta$ an sc-smooth bump function equal to $1$ near $\mathrm{cl}(W)$ and supported in the chart
domain, which makes $S$ a global sc$^+$-section of $\pi^*P$; at $y = \Phi(q)$, $R(\Phi(q),f(\Phi(q))) = f(\Phi(q))$. (4): $\beta(y)R(y,e_0)$ for a smooth $e_0$. The
paracompactness of $\mathbb R^n\times X$ and of $\pi^*P$, needed for them to be M-polyfold bundles of the project, holds. $\square$

The text works in a chart "assuming $X = U$"; the sections here are global, (3) is stated for families since Theorem 6.6.11 (preprint 6.35)
needs it for homotopies, and the smoothness of $x$ is not used (Findings, item 46). *Checked by machine (V6.32):*
`Polyfold.IsScHomotopyRel`, `Polyfold.exists_contDiff_eq_id_near_Icc_mapsTo`, `Polyfold.exists_nhds_isCompact_zeros`,
`Polyfold.exists_isScPlusSection_pullback_of_family`, `Polyfold.hasScPlusSectionsThrough_pullback_rn_of_bump`,
`Polyfold.proposition_6_28`, `Polyfold.MPolyfold.paracompactSpace_prod`, `Polyfold.paracompactSpace_pullbackSpace`.

**The parametrized section.** For a family $\Phi$ (a path, or a homotopy) and $S$ as in (3), and sc$^+$-sections $s_1,\dots,s_k$ of $\pi^*P$, put
$$F(\lambda,(q,y)) = f(y)+S(q,y)+\textstyle\sum_{i=1}^k\lambda_is_i(q,y)$$
on $\mathbb R^k\times(\mathbb R^n\times X)$, the text's $F(t,y,\lambda) = f(y)-s(y,t)+\sum\lambda_is_i(y,t)$ (preprint p. 221). Then $F(0,(q,\Phi(q))) = 0$ for $q$ near $[0,1]^n$.

**Lemma 6.6.4 (preprint 6.29)** *(book 2017: Lemma 6.12, p. 207).* There are finitely many sc$^+$-sections $s_1,\dots,s_k$ of $\pi^*P$ such that $F$ is in general
position (Definition 5.3.9 (preprint 5.17)) at $(0,(q,\Phi(q)))$ for all $q$ near $[0,1]^n$.

*Proof.* The text gives none ("using the results from the transversality theory"); the one formalized is that of Theorem
5.3.10 (preprint 5.18). At each $q\in[0,1]^n$, finitely many sections whose values at $(q,\Phi(q))$ span a complement of the range of the linearization, and
finitely many more that put its kernel in good position to the boundary, give general position at $(0,(q,\Phi(q)))$; general
position is an open condition along the family, and adding sections keeps it (V6.46). Cover the compact $[0,1]^n$ by finitely
many of these open sets and take all their sections. $\square$

The text states the property (P), that each slice $F_t$ is in general position at $(\varphi(t),0)$, and derives from it the general
position of $F$ at the points $(t,\varphi(t),0)$, which is what Lemmas 6.6.5 and 6.6.6 (preprint 6.30 and 6.31) use; the conclusion is formalized, (P) itself is not
(gap G.63; Findings, item 47). *Checked by machine (V6.33):* `Polyfold.isZeroAt_paramSection_zero`,
`Polyfold.exists_sections_isGeneralPositionGerm_of_isCompact`, `Polyfold.lemma_6_29`.

**Lemma 6.6.5 (preprint 6.30)** *(book 2017: Lemma 6.13, p. 207).* The text: the solution set of $F$ near the points $(t,\varphi(t),0)$ is a manifold with
boundary with corners, $\pi:(t,y,\lambda)\mapsto t$ is a submersion on it, and the tangent spaces $L_t$ of the slices form a smooth vector bundle $L$
over $[0,1]$ with its line bundle $\lambda(L)$. What is formalized is the part used: for a continuous family of zeros in good
position, read in one chart at continuously varying level-$1$ points, the kernels of the linearizations form a
continuous family of subspaces of the model space, of dimension the index; and the derivative of an sc-smooth family of
zeros, read in a chart, lies in the kernel of the linearization. The manifold, the map $\pi$ and the smooth structure of $L$ are
not formalized (gap G.62; Findings, item 48). *Checked by machine (V6.34):*
`Polyfold.StrongBundle.IsSurjLinOfIndex.finrank_linKer`, `Polyfold.exists_local_frame_linKer`,
`Polyfold.exists_subspaceFamily_linKer`, `Polyfold.fderiv_mem_linKer`.

**Continuous families of subspaces.** "Vector bundle" is read as a family $b\mapsto L_b$ of $n$-dimensional subspaces of one normed
space, spanned near every point by a continuous frame. Then $b\mapsto\lambda(L_b)$ is a line bundle with the wedges of frames as
trivializations (two frames differ by a continuous invertible matrix, the wedges by its determinant). Families and
orientations restrict along continuous maps. Over $[0,1]$, by Lemma 6.C, an orientation of $\lambda(L_0)$ extends uniquely, and its
value at $1$ is the *continuation*; over a simply connected, locally path-connected base the continuation along a path
depends only on its end points. The kernels of a norm-continuous family of surjective Fredholm operators over a
connected base form such a family; so do the images of a family under a jointly continuous family of linear maps
injective on its members, with orientations carried along; and so does the cut of a family by the kernel of a fixed
linear map onto on every member (the text's $L_t = TS\cap\{dt = 0\}$). "Varies continuously" is read in the operator norm, and for
maps into a model space as joint continuity. *Checked by machine (V6.35, V6.36, V6.39):* `Polyfold.SubspaceFamily`,
`Polyfold.SubspaceFamily.det`, `Polyfold.SubspaceFamily.transport`, `Polyfold.SubspaceFamily.transport_eq`,
`Polyfold.SubspaceFamily.cont`, `Polyfold.SubspaceFamily.cont_trans`, `Polyfold.SubspaceFamily.cont_eq_transport`,
`Polyfold.exists_subspaceFamily_ker`, `Polyfold.SubspaceFamily.exists_map`,
`Polyfold.SubspaceFamily.isLineOrientation_map`, `Polyfold.SubspaceFamily.exists_inf_ker`.

**The slice kernel.** In the product chart $(\lambda\mapsto\lambda)\times((q\mapsto q)\times\varphi)$ at $(0,(q,z))$ the linearization of $F$ is
$$(\lambda,(\sigma,v))\mapsto D(\hat g_q\circ r)(z)v+\textstyle\sum_i\lambda_i\hat s_i(q,\cdot)(z)+D_q\sigma,\qquad g_q = f+S(q,\cdot),$$
with hats for principal parts and $D_q\sigma$ the derivative of $S$ in the parameter. Cut by $\sigma = 0$, its kernel is the image of $\ker(T\oplus\varphi)$,
where $T = g_q'(x)\in\mathrm{Lin}(f,x)$, $x = \Phi(q)$, and $\varphi(\lambda) = \sum_i\lambda_is_i(q,x)$. The text's $L_t = \ker F_t'(\varphi(t),0)$ is read as this cut of the kernel of the
whole linearization (Findings, item 49). *Checked by machine (V6.37):* `Polyfold.sliceProj`, `Polyfold.sliceIncl`,
`Polyfold.linKer_inf_ker_sliceProj_eq_map`, `Polyfold.mem_linSet_sectionAdd_pullbackSlice`,
`Polyfold.surjective_coprod_of_isLinSurjAt`, `Polyfold.exists_sliceKernel`.

**Lemma 6.6.6 (preprint 6.31)** *(book 2017: Lemma 6.14, p. 209).* With these operators the sequence
$$0\to\ker T\xrightarrow{j}\ker(T\oplus\varphi)\xrightarrow{p}\mathbb R^k\xrightarrow{c}K_z/R(T)\to0,\qquad c(\lambda) = \textstyle\sum_i\lambda_is_i(q,x)+R(T),\tag{96}$$
is exact.

*Proof.* It is the stabilization sequence of $T$ and $\varphi$, exact by Lemma 6.4.14 (preprint 6.14) once $T\oplus\varphi$ is onto. The text has $c$ onto by (P). Here:
$F$ is in general position at $(0,(q,x))$ (Lemma 6.6.4 (preprint 6.29)), so every $y\in K_z$ is $Tv+\varphi(\lambda)+D_q\sigma$. Differentiating $(f+S)(q,\Phi(q)) = 0$ in $q$ gives
$T(D\Phi(q)\sigma)+D_q\sigma = 0$, so $D_q\sigma\in R(T)$: the derivative of the family of zeros absorbs the $\mathbb R^n$-directions, and $y\in R(T)+\varphi(\mathbb R^k)$. $\square$
*Checked by machine (V6.38):* `Polyfold.lemma_6_31`.

**The push-forward of the text** (pp. 265–269 (preprint pp. 223–224)). From (96), $\Phi_{E_t}:\det(T_t)\to\lambda(L_t)\otimes\lambda^*(\mathbb R^k)$, and with (94), $\det(T_t)\cong\lambda(L_t)$. An orientation $o_0$ of
$\mathrm{DET}(f,\varphi(0))$ orients $\det(T_0)$, hence $\lambda(L_0)$; continuation along $L$ orients $\lambda(L_1)$; and $\Phi_{E_1}^{-1}$ orients $\det(T_1)$, hence gives $o_1 = \varphi_*o_0$ in
$\mathrm{DET}(f,\varphi(1))$, the *push-forward orientation*. The proofs of Lemmas 6.6.8, 6.6.10 (preprint 6.33, 6.34) and of Theorem 6.6.11 (preprint 6.35) use that the orientations
carried by $\Phi_{E}$ from $\mathrm{DET}$ to the kernel bundles vary continuously when the operators do.

> **The sign of (94).** As we read it, they do not: $\Phi_{\mathcal E}$ followed by (94) does not vary continuously in the topology of
> $\mathrm{DET}$ where $\dim\operatorname{coker}T$ changes parity, so the orientations it carries along a family need not be continuous (Lemma 6.D,
> Example 6.E). With $\alpha(T) = (-1)^{\dim\operatorname{coker}T}$ they are. The propagation is therefore made with $\alpha(T)\Phi_{\mathcal E}$ at both end points. On each
> operator this carries the text's orientation or its opposite, so for given end-point operators $T_a$, $T_b$ the push-forward
> differs from the text's by $\alpha(T_a)\alpha(T_b)$ (Findings, item 50).

**Lemma 6.D (the stabilization sign).** In a local determinant chart with projection $P$, for $\psi:\mathbb R^k\to F$ with $S\oplus\psi$ onto, the chart
coordinate of $\iota_\psi(x)\in\det(S\oplus\psi)$ is $(-1)^{k\dim F/R(P)+\dim\operatorname{coker}S}D(S,\psi)$ times that of $x\in\det(S)$, with $D$ continuous and nowhere zero near the
centre. Consequently, for a continuous orientation $o$ of $\mathrm{DET}$, a norm-continuous family $T_q$ and a continuous stabilization
$\varphi_q$ with $T_q\oplus\varphi_q$ onto, the rays $\alpha(T_q)\,\iota_{\varphi_q}(o(T_q))$ of $\lambda(\ker(T_q\oplus\varphi_q))$ form an orientation; without $\alpha$ they need not.

*Proof.* $P$ is also a good left-projection for $S\oplus\psi$, and we use it for both operators. Let $l = \dim F/R(P)$, $m = \dim\operatorname{coker}S$, $u$ a basis of $\ker S$,
extended by $w_1,\dots,w_p$ ($p = l-m$) to a basis of $\ker(PS)$, and $g_1,\dots,g_m$ with $(I-P)g_i+R(S) = d_i$ a basis of $\operatorname{coker}S$. By (91),
$\gamma^P_S(u\otimes d^*) = (u\wedge w)\otimes([g]\wedge[Sw])^*$. For $\iota_\psi$ (Proposition 6.4.15 (preprint 6.15)) take $\bar c_i$ with $\psi(\bar c_i)+R(S) = d_i$, say $\psi(\bar c_i) = (I-P)g_i+Sx_i$, and $\bar b_j = (b_j,r_j)$.
For $\gamma^P_{S\oplus\psi}$ extend the basis $(u,0),\bar b$ of $\ker(S\oplus\psi)$ to one of $\ker(P(S\oplus\psi))$ by $(w_j,0)$ and $(-x_i,\bar c_i)$, whose images in $F/R(P)$ are
$[Sw_j]$ and $[(I-P)g_i] = [g_i]$. Then
$$\gamma^P_{S\oplus\psi}\iota_\psi(u\otimes d^*) = \det(\bar c,r)^{-1}\big((u,0)\wedge\bar b\wedge(w,0)\wedge(-x,\bar c)\big)\otimes([Sw]\wedge[g])^*.$$
Read against frames $(k(S),0)\wedge\nu(S)\otimes e^*$ and $k(S)\otimes e^*$, with $\nu_j(S) = (-(PS|_Y)^{-1}P\psi e_j,e_j)$ completing the frame of $\ker(PS)\times0$: moving $(w,0)$ past $\bar b$
costs $(-1)^{p(k-m)}$, the kernel wedge compares with the frame through the $\mathbb R^k$-components, giving $\det(r,\bar c) = (-1)^{m(k-m)}\det(\bar c,r)$, and
exchanging $[Sw]$ and $[g]$ costs $(-1)^{pm}$; the factor comparing $u\wedge w$ with $k(S)$ is common to both coordinates. The total is $(-1)^{pk+m(k-m)} = (-1)^{lk-m^2} = (-1)^{lk+m}$; the actual chart frame of $S\oplus\psi$ differs from the
one used by a continuous nowhere-zero factor, which is $D$. For the consequence: $o(T_q)$ has coordinates of constant sign
near each point, so $\alpha(T_q)\iota_{\varphi_q}(o(T_q))$ has coordinates of sign $(-1)^{lk}\operatorname{sign}D$, locally constant; for onto operators the chart with $P = I$
has the kernel frame of Lemma 6.5.2 (preprint 6.18) as frame, so $\mathrm{DET}$ restricted to them is the kernel line bundle. $\square$

The first exponent $k\dim F/R(P)$ is constant on a chart; the second is not. *Checked by machine (V6.40):* `Polyfold.coord_stabIota`,
`Polyfold.stabD`, `Polyfold.continuousOn_stabD`, `Polyfold.stabD_ne_zero`, `Polyfold.stabSign`,
`Polyfold.isLineOrientation_stabRay`, `Polyfold.not_isLineOrientation_stabRay_uncorrected`.

**Example 6.E (the jump).** In Example 6.B take $\varphi(r) = r$, so $T_a\oplus\varphi:(e,r)\mapsto ae+r$ is onto with kernel spanned by $(1,-a)$, a continuous
family. For $a\ne0$: $\ker T_a = 0$, $\operatorname{coker}T_a = 0$, $\bar b_1 = (1,-a)$, $r_1 = -a$, so $\iota_\varphi(h_a) = (-a)^{-1}(1,-a)\otimes1^*$ and $\iota_\varphi(o^+(a)) = [-(1,-a)]$. For $a = 0$:
$a_1 = 1$, $\bar c_1 = 1$, no $\bar b$, so $\iota_\varphi(1\otimes1^*) = (1,0)\otimes1^*$ and $\iota_\varphi(o^+(0)) = [+(1,0)]$. Against the frame $(1,-a)$ the carried rays are negative for
$a\ne0$ and positive at $a = 0$: they jump. With $\alpha(T_a) = 1$ for $a\ne0$ and $\alpha(0) = -1$ they are $[-(1,-a)]$ for every $a$. (Here $k = l = 1$, and the sign of
Lemma 6.D is $-1$ for $a\ne0$, $+1$ at $a = 0$.) The Lean instance is this family reparametrized, $T_q = q/(1+|q|)$.

**The push-forward with the sign.** At a chart point, $T = (f+S)'(x)\in\mathrm{Lin}(f,x)$ and $\varphi(\lambda) = \sum_i\lambda_i\hat s_i(x)$. A family of *stabilized kernels* over a
parameter space is a continuous family $\Lambda$ of the subspaces $\ker(T_q\oplus\varphi_q)$ of $E_0\times\mathbb R^k$ at points $y(q)$, read in one chart. Its push-forward
$\varphi_*:\mathrm{Or}^f_{x_0}\to\mathrm{Or}^f_{x_1}$ between the end points is
$$o\ \mapsto\ o(T_a)\ \mapsto\ \alpha(T_a)\,\iota_{\varphi_a}(o(T_a))\ \xrightarrow{\ \text{continuation}\ }\ \text{a ray of }\lambda(\Lambda_b)\ \mapsto\ \text{the }o'\text{ with }\alpha(T_b)\,\iota_{\varphi_b}(o'(T_b))\text{ equal to it}.$$
It depends only on the data, is compatible with pull-back and with concatenation, and along a path with continuously
varying data continuation carries the rays read at one parameter to those read at the next. A *push-forward along* an
sc-smooth path $\gamma$ in a chart is one coming from global sc$^+$-sections $S,s_1,\dots,s_k$ of $\pi^*P\to\mathbb R\times X$ with $(f+S)(t,\gamma(t)) = 0$ near $[0,1]$ and a
family of stabilized kernels of their slices along $\gamma$. With the sections of Lemma 6.6.4 (preprint 6.29) the stabilized kernels exist: they are
the tangent spaces of the solution set (Lemma 6.6.5 (preprint 6.30)) cut by $\{dt = 0\}$ and identified with $\ker(T_q\oplus\varphi_q)$ (the slice kernel). So along
every sc-smooth path in a set with property (3) there is a push-forward, and a push-forward along $\gamma$ is the composite of
push-forwards along its two halves. The sections enter pointwise, property (P) is used only to construct a
push-forward, and the continuity in the parameter is that of $\Lambda$. *Checked by machine (V6.41–V6.43):*
`Polyfold.ChartPoint.stabT_mem_linSet`, `Polyfold.ChartPoint.stabPhi`, `Polyfold.IsStabKernels`,
`Polyfold.IsStabKernels.push`, `Polyfold.IsStabKernels.push_congr`, `Polyfold.IsStabKernels.cont_orRay_path`,
`Polyfold.IsStabKernels.push_comp`, `Polyfold.IsStabKernels.push_trans`, `Polyfold.exists_isStabKernels`,
`Polyfold.IsPush`, `Polyfold.IsPush.split`, `Polyfold.exists_isPush`.

**Lemma 6.6.8 (preprint 6.33)** *(book 2017: Lemma 6.15, p. 209).* Appending sc$^+$-sections $\bar s_1,\dots,\bar s_d$ after $s_1,\dots,s_k$ does not change the push-forward.

*Proof.* Let $\varphi'$ be the extended map on $\mathbb R^{k+d}$. Choose $\ell_1,\dots,\ell_d\in\ker(T\oplus\varphi')$ whose last $d$ coordinates are the standard basis. In
Proposition 6.4.15 (preprint 6.15) for $\varphi'$ take the basis $(a,0,0)$, $(\bar b,0)$, $\ell$ of the kernel and the $\bar c_i$ embedded as $(\bar c_i,0)$; the matrix $[(\bar c,0),(r,0),\pi(\ell)]$ is block
triangular with the identity in the last $d$ rows, so its determinant is $\det(\bar c,r)$. Hence
$$\iota_{\varphi'}(h) = (w\mapsto(w,0)\wedge\ell_1\wedge\dots\wedge\ell_d)\big(\iota_\varphi(h)\big),$$
exactly, with no sign, because the appended sections come last; $\alpha(T)$ is the same for both. The map $w\mapsto(w,0)\wedge\ell$ does not depend on the
choice of the $\ell_j$ (two choices differ by vectors of $\ker(T\oplus\varphi)\times0$), and with continuous lifts $\ell_j(q)$ it is a continuous nowhere-zero
map of the kernel line bundles; so it commutes with continuation. $\square$

The text's proof passes through a homotopy $\tilde F(\tau,\cdot)$ and ends with "one verifies by a simple computation"; with the
appended sections last the homotopy is not needed (Findings, item 51). *Checked by machine (V6.45):* `Polyfold.wedgeExt`,
`Polyfold.wedgeExt_congr`, `Polyfold.detEquiv_stabIota_append`, `Polyfold.SubspaceFamily.exists_continuous_lifts`,
`Polyfold.isLineOrientation_wedgeExt`, `Polyfold.propagate_append`, `Polyfold.IsStabKernels.push_append`.

**Lemma 6.6.10 (preprint 6.34)** *(book 2017: Lemma 6.16, p. 211).* For a family of stabilized kernels over the square $[0,1]^2$, with the end points $x_0$,
$x_1$ fixed and the end-point operators varying continuously, the push-forwards along the edges $\tau = 0$ and $\tau = 1$ agree.

*Proof.* Along the edge $t = 0$ the rays $\alpha(T_{\tau,0})\iota(o(T_{\tau,0}))$, for $o\in\mathrm{Or}^f_{x_0}$, form an orientation (Lemma 6.D, $o$ being a continuous
orientation over the convex $\mathrm{Lin}(f,x_0)$), so continuation along that edge carries the ray at $(0,0)$ to the ray at $(1,0)$; likewise along
$t = 1$. Over the square continuation depends only on the end points, so continuation along the edge $\tau = 0$ equals continuation
along the other three edges. Reading the end rays back gives the claim. $\square$

The text's convex homotopy $s^\tau$ is part of the square below; the continuity of the end-point orientations along $\tau$ is that of
Lemma 6.D, with the sign. *Checked by machine (V6.47):* `Polyfold.IsStabKernels.push_square`, `Polyfold.sqEdge`,
`Polyfold.sqPath`.

**Proposition 6.6.7 (preprint 6.32)** *(book 2017: Proposition 6.13, p. 209).* Two push-forwards along the same sc-smooth path in the domain of a chart
agree.

*Proof.* Let the data be $(S^0,s^0_1,\dots,s^0_{k^0})$ and $(S^1,s^1_1,\dots,s^1_{k^1})$. Over the square take $S^\tau = (1-\tau)S^0+\tau S^1$, still zero along the path, the
sections $(1-\tau)\hat s^0_j+\tau\hat s^1_j$ for $j\le k^0+k^1$, with $\hat s^i_j = s^i_j$ for $j\le k^i$ and $0$ otherwise, followed by the sections of Lemma 6.6.4 (preprint 6.29) for the
square. At $\tau = 0$ the sections $s^0$ are the first $k^0$ members of the family and at $\tau = 1$ the sections $s^1$ the first $k^1$, so Lemma 6.6.8 (preprint 6.33)
applies on both edges without reordering; along $t = 0,1$ the operators $(f+S^\tau)'(x_i)$ are affine in $\tau$; and Lemma 6.6.10 (preprint 6.34) compares
the edges. $\square$

"Does not depend on the choices" is read as the agreement of any two data; the text first adds sections to both sides,
then uses Lemma 6.6.10 (preprint 6.34) (Findings, item 52). *Checked by machine (V6.44):* `Polyfold.IsStabKernels.push_eq_of_prefix`,
`Polyfold.isZeroAt_sectionAdd_combo`, `Polyfold.linAt_principal_combo`, `Polyfold.proposition_6_32`.

**Theorem 6.6.11 (preprint 6.35)** *(book 2017: Theorem 6.1, p. 212).* Every smooth point $x$ has an open $U\ni x$ and a chart $c$ such that push-forwards exist
along the sc-smooth paths in $U$ and depend only on their end points.

*Proof.* Take $U\subseteq W$ of Proposition 6.6.3 (preprint 6.28). Push-forwards exist along paths in $U$ ($W$ has property (3)). For paths $\gamma_0,\gamma_1$ in $U$ with the
same end points, (1′) gives a homotopy $\Phi$ in $W$, and (3) a section along it that depends on the parameter only through the
point, so the operators at the fixed end points do not change along $\tau$; with the sections of Lemma 6.6.4 (preprint 6.29) on the square,
Lemma 6.6.10 (preprint 6.34) gives equal push-forwards along the two edges. One more step is needed: $\Phi$ is $\gamma_i$ on the edges only for $t\in[0,1]$,
while a push-forward datum needs $f+S = 0$ near $[0,1]$. So the argument runs through $\gamma_i\circ\kappa$, $\kappa$ the smooth transition function
($\kappa(0) = 0$, $\kappa(1) = 1$, values in $[0,1]$), with three homotopies whose edges are exact for all $t$: $(\sigma,t)\mapsto\gamma_i((1-\sigma)t+\sigma\kappa(t))$ from $\gamma_i$ to $\gamma_i\circ\kappa$,
and $(\tau,t)\mapsto\Phi(\tau,\kappa(t))$ from $\gamma_0\circ\kappa$ to $\gamma_1\circ\kappa$. $\square$

The statement does not introduce $f$, here an sc-Fredholm section with tame germ data, and asks $U$ to be sc-smoothly
contractible, which is not shown (gap G.61); the proof uses (1′) (Findings, item 53). *Checked by machine (V6.48):*
`Polyfold.push_eq_of_homotopy`, `Polyfold.HasLocalPropagation`, `Polyfold.theorem_6_35`.

**Paths in a chart.** For an open $U$ in a chart domain and $x\in U$ there is an open $V\ni x$ in $U$ whose smooth points are pairwise
joined by sc-smooth paths in $U$ (images of segments under $r$). The concatenation of $\gamma_1$ and $\gamma_2$ is $\gamma_1(\kappa(3s))$ for $s\le1/2$ and $\gamma_2(\kappa(3s-2))$
for $s>1/2$; it is constant near $s = 1/2$, hence sc-smooth, with the right end points and halves. Reparametrizing by a $C^\infty$ map keeps
sc-smoothness, and push-forwards compose along concatenations. Paths are joined only locally, inside a chart (gap G.56).
*Checked by machine (V6.49):* `Polyfold.exists_nhds_scPath`, `Polyfold.concatPath`, `Polyfold.isScSmoothMap_concatPath`,
`Polyfold.concatPath_half₁`, `Polyfold.concatPath_half₂`, `Polyfold.isScSmoothMap_reparam`,
`Polyfold.HasLocalPropagation.eq_trans`.

**Definition 6.6.12 (preprint 6.36)** *(book 2017: Definition 6.10, p. 212).* An *orientable neighbourhood* of $(f,x)$ is a pair $V\subseteq U$: $U$ open with the local
propagation property of Theorem 6.6.11 (preprint 6.35) in a chart, and $V\ni x$ open with any two smooth points joined by an sc-smooth path in $U$. A
*continuous orientation* is a choice $y\mapsto o_y\in\mathrm{Or}^f_y$ on $V_\infty$ carried into itself by the push-forwards along paths in $U$. An orientable
neighbourhood has exactly two continuous orientations, and every smooth point has an orientable neighbourhood.

*Proof.* Existence: Theorem 6.6.11 (preprint 6.35) and the paths in a chart. Fix $o_x$ and put $o_y = \gamma_*o_x$ for a path $\gamma$ in $U$ from $x$ to $y\in V_\infty$; by the local
propagation property this does not depend on $\gamma$. For a path $\psi$ in $U$ from $y_1$ to $y_2$, $\psi_*o_{y_1} = \psi_*\gamma_{1*}o_x$ is the push-forward along the concatenation of $\gamma_1$ and $\psi$, a path in $U$ from $x$ to $y_2$, hence $o_{y_2}$. A continuous
orientation is determined by its value at $x$, which is one of two. $\square$

The text's orientable neighbourhood is an open contractible $U$; the pair is used since Proposition 6.6.3 (preprint 6.28) gives (1′) (gap G.61;
Findings, item 54). *Checked by machine (V6.50):* `Polyfold.IsContinuousOrientation`,
`Polyfold.exists_two_isContinuousOrientation`, `Polyfold.IsOrientableNbhd`, `Polyfold.exists_isOrientableNbhd`.

## 6. The orientation functor and oriented sections (pp. 272–276 (preprint pp. 227–230))

**Homotopy classes.** Two sc-smooth paths from $x$ to $y$ are *homotopic* if an sc-smooth $H:\mathbb R^2\to X$ is the one path at $\tau = 0$ and the
other at $\tau = 1$ for $t\in[0,1]$, and fixes the end points for $\tau\in[0,1]$. For a $C^\infty$ map $\theta$ with $\theta(0) = 0$, $\theta(1) = 1$, $\gamma\circ\theta$ is homotopic to $\gamma$ by
$(\sigma,t)\mapsto\gamma((1-\sigma)t+\sigma\theta(t))$, inside every set containing $\gamma([0,1])$ when $\theta([0,1])\subseteq[0,1]$; the concatenation of the two halves of a path is such
a reparametrization. *Checked by machine (V6.51):* `Polyfold.isScHomotopyRel_reparam`, `Polyfold.leftHalf`,
`Polyfold.rightHalf`, `Polyfold.halvesReparam`, `Polyfold.concatPath_halves`.

**The path category $PX$** (pp. 272–274 (preprint pp. 227–228)). Homotopy is an equivalence relation; concatenation is well defined on classes and
associative; the classes of the constant paths are units and the reversed paths $t\mapsto\gamma(1-t)$ give inverses. So the smooth
points with these classes form a category $PX$, indeed a groupoid.

*Proof of transitivity.* The edge conditions hold only for $t\in[0,1]$, so two homotopies $H_1$ (from $\gamma_0$ to $\gamma_1$) and $H_2$ (from $\gamma_1$ to $\gamma_2$)
need not agree at the seam outside $[0,1]$, and the pasted map need not be smooth. Read both through $\kappa$ in $t$: then $H_1(1,\kappa(t)) =
\gamma_1(\kappa(t)) = H_2(0,\kappa(t))$ for all $t$, since $\kappa(t)\in[0,1]$, and with $\kappa$ also in the homotopy variable the pieces are constant near the
seams. Pasting these with the reparametrization homotopies from $\gamma_0$ to $\gamma_0\circ\kappa$ and from $\gamma_2\circ\kappa$ to $\gamma_2$, whose edges are exact, gives a
homotopy from $\gamma_0$ to $\gamma_2$. $\square$

The text defines the composition $[\psi]\ast[\varphi]$ by $\varphi(\beta(s))$ on $[0,1/2]$ and $\psi(\beta(s))$ on $[1/2,1]$, with $\beta([1/2,1]) = [1,2]$; the second piece is
read as $\psi(\beta(s)-1)$ (possible misprint) (Findings, item 55). Transitivity is proved after reparametrizing by $\kappa$, and the
identities, which the text does not name, are the classes of the constant paths (Findings, item 71). Mathlib's
$[\varphi]\gg[\psi]$ is the text's $[\psi]\ast[\varphi]$. *Checked by machine (V6.52):* `Polyfold.ScHomotopic`, `Polyfold.ScHomotopic.trans`,
`Polyfold.isScHomotopyRel_triHomotopy`, `Polyfold.ScPath`, `Polyfold.ScPath.concat`, `Polyfold.ScPath.reverse`,
`Polyfold.ScPath.concat_assoc`, `Polyfold.ScPath.concat_reverse`, `Polyfold.ScPathClass`, `Polyfold.PathCat`,
`Polyfold.PathCat.category`, `Polyfold.PathCat.groupoid`, `Polyfold.PathCat.comp_mk`, `Polyfold.PathCat.id_eq_mk`.

**Comparing charts.** The text treats $T_xX$, $Y_x$, $\mathrm{Lin}(f,x)$ and $\mathrm{Or}^f_x$ as chart-free (preprint p. 219); here they live at chart points and are
identified between charts (Findings, item 70). (a) For isomorphisms $A$, $\Gamma$ with $S'A = \Gamma S$, $A$ maps $\ker S$ onto $\ker S'$ and $\Gamma$ induces
$\operatorname{coker}S\cong\operatorname{coker}S'$, whence $\det(S)\cong\det(S')$ by the wedge formula; this is compatible with composition and with the $\gamma^P$ ($\Gamma P\Gamma^{-1}\in\Pi_{S'}$),
and carries continuous orientations of $\mathrm{DET}$ along. (b) For two chart points $p$, $p'$ at $x$, $A$ is the derivative at $z$ of the base
transition and $\Gamma$ the fibre part of the strong bundle transition, with the cocycle rules; by the chain rule for principal
parts and since conjugates of sc$^+$-operators are sc$^+$, $L\in\mathrm{Lin}_p(f,x)$ if and only if $\Gamma LA^{-1}\in\mathrm{Lin}_{p'}(f,x)$, and the induced bijection
$\mathrm{Or}^f_x(p)\cong\mathrm{Or}^f_x(p')$ satisfies the cocycle rules. (c) The stabilization isomorphism and the sign are natural under conjugation, and
continuation is natural under jointly continuous families of injective linear maps; so a family of stabilized kernels
in one chart is carried by the derivative of the base transition to one in a second chart, with the same sections, and
a push-forward in one chart, conjugated by (b) at the end points, is a push-forward in the other. (d) $\mathrm{Or}^f_x$ is the set of
orientations read in a chart of the atlas at $x$ chosen once and for all; it has two elements and is identified with the
orientations read in any other chart at $x$ by (b), compatibly with composition. *Checked by machine (V6.53–V6.55):*
`Polyfold.conjDet`, `Polyfold.conjDet_trans`, `Polyfold.gammaProj_conjDet`, `Polyfold.LineOrientation.conj`,
`Polyfold.ChartPoint.baseDeriv`, `Polyfold.ChartPoint.fiberMap`, `Polyfold.ChartPoint.mem_linSet_transfer_iff`,
`Polyfold.ChartPoint.orTransfer`, `Polyfold.ChartPoint.orTransfer_trans`, `Polyfold.stabSign_conj`,
`Polyfold.stabRayEquiv_conjDet`, `Polyfold.IsStabKernels.exists_transfer`, `Polyfold.IsPush.transfer`,
`Polyfold.HasLocalPropagation.push_compat`, `Polyfold.orChart`, `Polyfold.Orx`, `Polyfold.toChartOr`,
`Polyfold.toChartOr_trans`, `Polyfold.exists_two_orx`.

**Transport along a path.** Call an open set *good* if it has the local propagation property in some chart (Theorem 6.6.11 (preprint 6.35));
good sets cover $X_\infty$. In a good set the push-forward, read through $\mathrm{Or}^f$ of the chosen charts, does not depend on the good
set or chart, by (c) and Proposition 6.6.7 (preprint 6.32), and is compatible with concatenation. For an sc-smooth path $\gamma$, by the Lebesgue
number lemma there is $N$ such that each of the $2^N$ dyadic pieces $\gamma|_{[j2^{-N},(j+1)2^{-N}]}$ lies in a good set; the *transport* along $\gamma$ is the
composite of the push-forwards along the pieces. It does not depend on $N$: a push-forward along a piece is the composite of
those along its halves. It is homotopy invariant: for a homotopy, the square is cut into $2^N\times2^N$ dyadic squares each mapped
into a good set, where push-forwards depend only on end points, so the two ways around each small square agree; pasting
the squares, the transports along the bottom and top edges agree, the side edges being constant paths, along which the
transport is the identity. It is compatible with concatenation and reparametrization, is the push-forward on a path in a
good set, and is the only family with these properties. The text's "using the compactness of $[0,1]$ and a finite
covering", "by a covering argument" and "it is obvious that $\Gamma_f$ is unique" (p. 274 (preprint p. 228)) are these dyadic subdivisions
(Findings, item 72). *Checked by machine (V6.56):* `Polyfold.LocalTransport`, `Polyfold.LocalTransport.transportN`,
`Polyfold.LocalTransport.transportN_eq_of_isFine`, `Polyfold.LocalTransport.exists_isLebesgueNumber`,
`Polyfold.LocalTransport.transport`, `Polyfold.LocalTransport.transport_eq_push`,
`Polyfold.LocalTransport.transport_const`, `Polyfold.LocalTransport.exists_isSqLebesgueNumber`,
`Polyfold.LocalTransport.transport_eq_of_isScHomotopyRel`, `Polyfold.LocalTransport.transport_concatPath`,
`Polyfold.LocalTransport.transport_unique`, `Polyfold.equiv_paste_squares`.

**Theorem 6.6.13 (preprint 6.37)** *(book 2017: Theorem 6.2, p. 213).* Let $X$ be tame with bump functions, $f$ with tame germ data, and $P$ with
sc$^+$-sections through the smooth fibre points. There is exactly one family of bijections $\Gamma_f([\varphi]):\mathrm{Or}^f_x\to\mathrm{Or}^f_y$ on the morphisms of $PX$
that takes identities to identities and compositions to composites and has property (∗): for every chart $c$, every open $U$
with the local propagation property in $c$ and every sc-smooth path $\varphi$ in $U$, $\Gamma_f([\varphi])$ is every push-forward along $\varphi$ in $c$, read
through $\mathrm{Or}^f$ of the chosen charts. It is a functor $PX\to$ Type, $x\mapsto\mathrm{Or}^f_x$, and uniqueness needs (∗) only on a family of such
open sets covering $X_\infty$.

*Proof.* $\Gamma_f([\varphi])$ is the transport, well defined on classes by homotopy invariance; identities and composites by the
constant paths and concatenation. (∗): for $\varphi$ in such a $U$, the push-forward along $\varphi$ in $U$ is the composite of those along
the dyadic pieces, each of which agrees with the push-forward in a good set by (c) and Proposition 6.6.7 (preprint 6.32). Uniqueness: a
functorial family with (∗) on a cover agrees with the push-forward on every dyadic piece of a fine subdivision, hence
with the transport. $\square$

(∗) is asked for every open set with the local propagation property, not only for sc-smoothly contractible ones (gap
G.61); $\mathcal O_f$ is read as types and bijections, and "uniquely determined" for the maps on morphisms. The sections through the
fibre points make every $\mathrm{Or}^f_x$ two-element; bump functions give them (Findings, item 72). *Checked by machine (V6.57):*
`Polyfold.IsPropagationNbhd`, `Polyfold.orPush`, `Polyfold.orPush_compat`, `Polyfold.IsStarPropertyOn`,
`Polyfold.IsStarProperty`, `Polyfold.orFunctorMap`, `Polyfold.orFunctorMap_id`, `Polyfold.orFunctorMap_comp`,
`Polyfold.orFunctor`, `Polyfold.orFunctorMap_isStarProperty`, `Polyfold.orFunctorMap_unique_of_cover`,
`Polyfold.orFunctorMap_unique`, `Polyfold.theorem_6_37`.

**Definition 6.6.14 (preprint 6.38)** *(book 2017: Definition 6.11, p. 213).* $f$ is *orientable* if, for any two smooth points $x$, $y$ joined by an sc-smooth
path, $\Gamma_f([\varphi])$ does not depend on the morphism $[\varphi]:x\to y$.

**Definition 6.6.15 (preprint 6.39)** *(book 2017: Definition 6.12, p. 213).* $f$ is orientable if there is $y\mapsto o_y\in\mathrm{Or}^f_y$ on $X_\infty$ such that every smooth point has an
orientable neighbourhood $V\subseteq U$ on which it is a continuous orientation.

**Definition 6.6.16 (preprint 6.40)** *(book 2017: Definition 6.13, p. 214).* An *orientation* of $f$ is a map $y\mapsto o_y$ on $X_\infty$ whose restriction to every orientable
neighbourhood of every smooth point is a continuous orientation.

**Proposition 6.F.** Each of the following is equivalent to the next: $f$ is orientable in the sense of Definition 6.6.14 (preprint 6.38); there is
$y\mapsto o_y$ with $\Gamma_f([\varphi])o_x = o_y$ for every $[\varphi]:x\to y$; $f$ is orientable in the sense of Definition 6.6.15 (preprint 6.39). The orientations of Definition 6.6.16 (preprint 6.40) are
exactly the maps with $\Gamma_f([\varphi])o_x = o_y$ for all $[\varphi]$; they exist if and only if $f$ is orientable; two of them that agree at a point agree on
the smooth points joined to it, and there are exactly two on each such class.

*Proof.* Given $o$ preserved by $\Gamma_f$, $\Gamma_f([\varphi])$ sends $o_x\mapsto o_y$ and so $-o_x\mapsto-o_y$, whatever $[\varphi]$: Definition 6.6.14 (preprint 6.38). Conversely, on each class of points joined
by paths fix a base point $x_0$ and $o_{x_0}$ and put $o_y = \Gamma_f([\varphi_y])o_{x_0}$, which does not depend on $\varphi_y$; for $[\psi]:x\to y$, $\Gamma_f([\psi])o_x = \Gamma_f([\psi]\ast[\varphi_x])o_{x_0} = o_y$.
If $o$ is preserved by $\Gamma_f$, its restriction to an orientable neighbourhood is carried into itself by the push-forwards along
paths in $U$, by (∗): a continuous orientation. If $o$ is a continuous orientation on orientable neighbourhoods of all smooth
points, then for a path $\varphi$ from $x$ to $y$, the Lebesgue number lemma for the open cover by the sets $V$ cuts $\varphi$ into pieces each with
end points in some $V$ and image in its $U$; on each piece $\Gamma_f$ is the push-forward, which preserves $o$; so $\Gamma_f([\varphi])o_x = o_y$. The last
claims follow since each $\mathrm{Or}^f_x$ has two elements. $\square$

The text calls Definition 6.6.15 (preprint 6.39) "an equivalent version" without proof (Findings, item 73). It writes "$y\in U_\infty$" before any $U$
is introduced, read as $y\in X_\infty$ (possible misprint) (Findings, item 74), and "smooth points in the same path component" is read
as smooth points joined by an sc-smooth path (gap G.56; Findings, item 73). An orientable neighbourhood is the pair of
Definition 6.6.12 (preprint 6.36) (Findings, item 75). *Checked by machine (V6.58–V6.60):* `Polyfold.scPathSetoid`,
`Polyfold.IsOrientableSection`, `Polyfold.isOrientableSection_iff_exists`, `Polyfold.IsOrientableSection'`,
`Polyfold.isOrientableSection'_iff_exists`, `Polyfold.isOrientableSection_iff`, `Polyfold.IsSectionOrientation`,
`Polyfold.isSectionOrientation_iff`, `Polyfold.exists_isSectionOrientation_iff`,
`Polyfold.IsSectionOrientation.apply_eq_iff`, `Polyfold.IsSectionOrientation.exists_two`.

**Theorem 6.6.18 (preprint 6.41)** *(book 2017: Theorem 6.3, p. 214).* Let $X$ be tame and $f$ a proper sc-Fredholm section, in general position at every
zero, with an orientation $o$. Then $S = f^{-1}(0)$ is a smooth compact manifold with boundary with corners with a natural
orientation.

What is proved. For $f$ with tame germ data: $S$ is compact, a smooth submanifold in general position with the induced
structure of a tame manifold with boundary with corners (the conclusions of Theorem 5.3.10 (preprint 5.18)), and $T_xS = \ker f'(x)$, read in a
chart. At a zero, $f'(x)\in\mathrm{Lin}(f,x)$ (take $s = 0$) and is onto, so $\det f'(x) = \lambda(\ker f'(x))\otimes\lambda^*(0)\cong\lambda(T_xS)$, and $o_x$ gives a ray of $\lambda(T_xS)$, the *tangent
orientation*. For every sc-smooth path $\gamma$ of zeros in an orientable neighbourhood $V\subseteq U$, the kernels $\ker f'(\gamma_q)$ form a continuous
family of subspaces, and the tangent orientations of $o$ form an orientation of its line bundle.

*Proof.* Compactness and the manifold structure are Chapters 4 and 5; "proper" is used only through compactness, which for
sc-Fredholm sections is equivalent to it (V5.10). Along $\gamma$, the datum $S = 0$, $k = 0$ is a push-forward datum: no sections are
needed, the operators $f'(\gamma_q)$ being onto, the stabilized kernels are the kernels $\ker f'(\gamma_q)$, and $\alpha = 1$ on onto operators. So the
push-forward is the continuation between tangent orientations. As $o$ is an orientation of $f$, it maps $o_{\gamma(0)}$ to $o_{\gamma(t)}$ for the
path $s\mapsto\gamma(t\kappa(s))$ from $\gamma(0)$ to $\gamma(t)$, for every $t$; so the tangent orientations along $\gamma$ are the continuation of the one at $\gamma(0)$, an
orientation of the kernel line bundle. $\square$

"A natural orientation" is read as the tangent orientations with their continuity along the sc-smooth paths of zeros in
a chart, and "the local prolongation of the orientation on $S$ is the Fredholm one" as the identity of continuation and
push-forward along such paths (Findings, items 90, 91). Not formalized: an orientation of $S$ as an abstract manifold (gap
G.67) and the compatibility of the tangent orientations read in two charts at one point (gap G.68) (Findings, item 92).
*Checked by machine (V6.61):* `Polyfold.theorem_6_41_solutionSet`, `Polyfold.tangentSpace_solutionSet_eq_linKer`,
`Polyfold.ChartPoint.linZero_mem_linSet`, `Polyfold.ChartPoint.linZero_surjective`, `Polyfold.ChartPoint.tangentOr`,
`Polyfold.stabSign_of_surjective`, `Polyfold.isStabKernels_zero`, `Polyfold.IsStabKernels.orRay_eq_tangentOr`,
`Polyfold.tangentFamily`, `Polyfold.cont_tangentOr`, `Polyfold.isLineOrientation_tangentOr`,
`Polyfold.isLineOrientation_tangentOr_of_isSectionOrientation`, `Polyfold.theorem_6_41`.

The paragraph after the theorem treats a non-generic $f$: a small sc$^+$-perturbation $s$ supported near $S_f$ makes $S_{f+s}$ a manifold,
oriented from $o$ because $\det((f+s)'(x))$ is oriented by $\mathrm{DET}(f,x)$, $\mathrm{Lin}(f+s,x) = \mathrm{Lin}(f,x)$. It is not formalized (gap G.69; Findings,
item 93).

**Remark 6.6.19 (preprint 6.42)** *(book 2017: Remark 6.4, p. 214).* For an oriented $(f,o)$ and an sc$^+$-section $s$ of $Y\to X\times[0,1]$, $\hat f(x,t) = f(x)+s(x,t)$ has a
natural orientation from $o$ and the standard orientation of $[0,1]$: for $L\in\mathrm{Lin}(f,x)$ oriented by $h = (a_1\wedge\dots\wedge a_n)\otimes(b_1\wedge\dots\wedge b_l)^*$, orient
$\tilde L(a,b) = La$ by $\tilde h = (a_1\wedge\dots\wedge a_n\wedge e)\otimes(b_1\wedge\dots\wedge b_l)^*$, $e$ the standard vector of $[0,1]$; $\tilde L$ lies in $\mathrm{Lin}(\hat f,(x,t))$.

For Fredholm $L$, $\tilde L = L\oplus0:E\times\mathbb R\to F$ is Fredholm with $\ker\tilde L = \ker L\times\mathbb R$ and $\operatorname{coker}\tilde L = \operatorname{coker}L$, and $h\mapsto\tilde h$ is an isomorphism
$\det(L)\cong\det(\tilde L)$. But in local determinant charts its coordinate is $(-1)^{\dim F/R(P)+\dim\operatorname{coker}L}$ times a continuous nowhere-zero function.
In Example 6.B, $h_a\mapsto(0,1)\otimes1^*$ has coordinate $-1/a$ in the chart at $0$ of $L(\mathbb R^2,\mathbb R)$, so $o^+(a)$ goes to a negative ray for every $a\ne0$, while at
$a = 0$, $1\otimes1^*\mapsto((1,0)\wedge(0,1))\otimes1^*$ has coordinate $1$. So, as we read it, the literal $h\mapsto\tilde h$ is not continuous in $L$ where the parity of
$\dim\operatorname{coker}L$ changes, and the orientation of $\mathrm{DET}(\hat f,(x,t))$ it defines could depend on the choice of $L$. With the sign of Lemma 6.D,
$(-1)^{\dim\operatorname{coker}L}h\mapsto\tilde h$ has a coordinate continuous up to a sign constant on a chart, pulls continuous orientations back along
$L\mapsto\tilde L$, and agrees with the text's map when $L$ is onto (Findings, item 95).

In charts: $X\times[0,1]$ is read as $\mathbb R\times X$ (decision D2), with the parameter first; $s$ is an sc$^+$-section $S$ of $\pi^*P$ and $\hat f = \tilde f+S$ with
$\tilde f(t,y) = f(y)$. At the product chart point $(t,z)$, where the tangent space is $\mathbb R\times T_zO$ and the fibre $K_z$, the operator $\hat L(\sigma,v) = Lv$
(the text's $\tilde L$ conjugated by the swap of the factors) lies in $\mathrm{Lin}(\hat f,(t,x))$ for every $L\in\mathrm{Lin}(f,x)$, and an orientation $o$ of $\mathrm{DET}(f,x)$
gives exactly one orientation $\hat o$ of $\mathrm{DET}(\hat f,(t,x))$ with $\hat o(\hat L)$ the image of $o(L)$ for every $L$; $o\mapsto\hat o$ is injective. Only the
orientation of $\mathrm{DET}(f,x)$ at the one point is used, and $\mathrm{Lin}(f,x)\ne\emptyset$ (Findings, item 96). That $(t,y)\mapsto\hat o$ is an orientation of
$\hat f$ in the sense of Definition 6.6.16 (preprint 6.40), built from an orientation of $f$, is not formalized (gap G.66; Findings, item 97).
*Checked by machine (V6.62):* `Polyfold.extOp`, `Polyfold.isFredholm_extOp`, `Polyfold.extDet`,
`Polyfold.extDet_wedge_tmul`, `Polyfold.coord_extDet`, `Polyfold.extDetN`, `Polyfold.extDetN_eq_of_surjective`,
`Polyfold.coord_extDetN`, `Polyfold.LineOrientation.extPull`, `Polyfold.extConjDet`, `Polyfold.ChartPoint.prodPt`,
`Polyfold.ChartPoint.prodLin`, `Polyfold.constLift`, `Polyfold.ChartPoint.prodLin_mem_linSet`,
`Polyfold.ChartPoint.existsUnique_prodOr`, `Polyfold.ChartPoint.prodOr_injective`.

## 7. Invariants (pp. 276–279 (preprint pp. 230–233))

This section is stated, not formalized. Let $(f,o)$ be oriented and proper over a tame $X$ with sc-smooth bump functions. For an
auxiliary norm $N$, Theorem 5.3.10 (preprint 5.18) gives an open $U\supseteq S_f$ such that for every sc$^+$-section $s$ supported in $U$ with $N(s(x))\le1$ the set $S_{f+s}$ is
compact, and among them sections for which every $(f+s,x)$, $x\in S_{f+s}$, is in general position; HWZ call these *admissible for
$(N,U)$*, and by §6 their solution sets are oriented compact manifolds with boundary with corners. The notion is not
formalized; what it recalls is Theorem 5.3.10 (preprint 5.18) (V5.38, V5.39) and the orientation of $S_{f+s}$ (Theorem 6.6.18 (preprint 6.41)) (gap G.55; Findings,
item 101). $H^*_{dR}(X,\partial X)$ is the cohomology of $\Omega^*_\infty(X)\oplus\Omega^{*-1}_\infty(\partial X)$ with $d(\omega,\tau) = (d\omega,j^*\omega-d\tau)$, $j:\partial X\to X$ the inclusion (§4.4).

**Theorem 6.7.1 (preprint 6.43)** *(book 2017: Theorem 6.4, p. 215).* Let $P:Y\to X$ be a strong bundle over a tame $X$ with sc-smooth bump functions. A
proper oriented sc-Fredholm section $(f,o)$ determines a linear map $\Psi_{(f,o)}:H^*_{dR}(X,\partial X)\to\mathbb R$ such that (1) for an auxiliary norm $N$ and $s$
admissible for $(N,U)$, $S_{f+s}$ is an oriented compact manifold with boundary with corners and
$$\Psi_{(f,o)}([\omega,\tau]) = \int_{S_{f+s}}\omega-\int_{\partial S_{f+s}}\tau,$$
the integrals being zero when the dimensions of forms and manifolds disagree; (2) for a proper oriented homotopy between
$(f_0,o_0)$ and $(f_1,o_1)$, $\Psi_{(f_0,o_0)} = \Psi_{(f_1,o_1)}$. If $\partial X = \emptyset$, $\Psi_{(f,o)}([\omega]) = \int_{S_{f+s}}\omega$ for $\omega$ of degree the index, and $0$ otherwise.

*The text's proof* (pp. 277–279 (preprint pp. 231–233)). Define $\Psi$ by (1) for one admissible $s_0$; it must be shown independent of $s_0$. For a second
admissible $s_1$, Remark 5.3.8 (preprint 5.16) gives a proper sc$^+$-homotopy $s_t$ such that $F(x,t) = f(x)+s_t(x)$ is in general position on $X\times[0,1]$ along its
solution set $S_F$, a compact manifold with boundary with corners of dimension $n+1$, oriented from $o$ and $[0,1]$ (Remark
6.6.19 (preprint 6.42)). Its boundary is $S_0\cup S_1\cup\tilde S$ with $S_i$ over $X\times\{i\}$ and $\tilde S\subseteq\partial X\times(0,1)$ (the text's Figure 7). Stokes' theorem on $S_F$ for the
closed form pulled back from $\omega$, the identity $j^*\omega = d\tau$ on $\tilde S$, and Stokes' theorem on $\tilde S$, whose boundary is $\partial S_0\cup\partial S_1$, give
$\int_{S_0}\omega-\int_{\partial S_0}\tau = \int_{S_1}\omega-\int_{\partial S_1}\tau$. Part (2) is the same argument for the homotopy.

The text writes the form on $X\times[0,1]$ as $\bar\omega = p_1^*\omega\wedge p_2^*dt$ and its boundary primitive as $p_1^*(d\tau)\wedge p_2^*dt$ (preprint p. 232). As we read it, the
computation needs $p_1^*\omega$ and $p_1^*\tau$ themselves: $p_2^*dt$ restricts to zero on $X\times\{0\}$ and $X\times\{1\}$, and $p_1^*\omega\wedge p_2^*dt$ has degree $n+1$, so its
integrals over the $n$-dimensional pieces of $\partial S_F$ vanish (possible misprint).

**Not formalized.** The theorem, its proof and the case $\partial X = \emptyset$ need the sc-differential forms and their cohomology of
§4.4 (gaps G.37–G.40) and integration over oriented compact manifolds with boundary with corners with Stokes' theorem,
which Mathlib does not have (decision D1; gap G.54; Findings, item 100). What the theorem rests on is formalized: the
perturbations of Theorem 5.3.10 (preprint 5.18) and the tangent orientations of Theorem 6.6.18 (preprint 6.41). The bead of §9 is the simplest instance.

## 8. The appendix: proofs of Lemma 6.3.3 (preprint 6.5) and Proposition 6.4.11 (preprint 6.12) (pp. 279–286 (preprint pp. 234–237))

*Proof of Lemma 6.3.3 (preprint 6.5)* (§6.8.1 (preprint §6.7.1)) *(book 2017: §6.7.1, pp. 218–219)*. Fix the bases $a$ of $A$ and $d$ of $D$; a choice is then $(Z,V,b')$. (i) Replacing $b'$ by
$\sigma b'$ for an automorphism $\sigma$ of $Z$ multiplies $\alpha(a)\wedge b'$ by $\det\sigma$, and $c' = \beta(b')$ by $\det(\beta\sigma\beta^{-1}) = \det\sigma$, so $(c\wedge c')^*$ by $(\det\sigma)^{-1}$: the
right-hand side of (91) is unchanged. (ii) For another complement $Z_1$ of $\alpha(A)$, $b'_j+q_j$ with $q_j\in\alpha(A)$ is a basis of $Z_1$ (projection along $\alpha(A)$);
$\alpha(a)\wedge(b'+q) = \alpha(a)\wedge b'$, adding to one block vectors of the span of the other, and $\beta(b'_j+q_j) = \beta(b'_j)$ since $\beta\alpha = 0$. For another
complement $V_1$ of $\beta(B)$, the $\gamma$-preimages there are $c_i+p_i$ with $\gamma(p_i) = 0$, that is, $p_i\in\beta(B)$, the span of the block $c'$: so $(c+p)\wedge c' = c\wedge c'$. (iii)
Replacing $a$ by $\tau a$ and $d$ by $\varepsilon d$ multiplies $a\otimes d^*$ by $\det\tau/\det\varepsilon$, and the right-hand side by the same factor: $\alpha(a)$ by $\det\tau$, the
$\gamma$-preimages $c$ by $\det\varepsilon$, $(c\wedge c')^*$ by $(\det\varepsilon)^{-1}$. So the linear map defined by one choice satisfies (91) for every choice. $\square$

The text's step "independent of the choices of the basis if and only if $\det(\tau) = \det(\varepsilon)$" is read as the homogeneity (iii), $\tau$ being
the $\sigma$ just introduced; the corrections $p_i$ lie in $\beta(B)$, written $\beta(C)$, and are combinations of the $\beta$-images, whose names are
exchanged with those of the $\gamma$-preimages in the last step (possible misprints) (Findings, item 1). *Checked by machine
(V6.63):* `Polyfold.FourTermExact.Choice.exists_smul_source_value`, `Polyfold.FourTermExact.Choice.wedgeC`.

*Proof of Proposition 6.4.11 (preprint 6.12)* (§6.8.2 (preprint §6.7.2)) *(book 2017: §6.7.2, pp. 219–222)*. Let $P\le Q$ in $\Pi_T$, $h = a\otimes(d+R(T))^*$ with $a$ a basis of $\ker T$ and
representatives $d_i\in\ker Q$ of a basis of $\operatorname{coker}T$: for any $f$, $Qf = QTx$ for some $x$, and $f+R(T) = (I-Q)(f-Tx)+R(T)$. Extend $a$ by $b_1,\dots,b_m$
to a basis of $\ker(QT)$ and further by $\tilde b_1,\dots,\tilde b_k$ to one of $\ker(PT)$. Write $[y]$ for $y+R(P)$.

*$\gamma^Q_T(h)$.* The $\beta$-images are $Tb_j+R(Q)$, and $d_i+R(Q)$ are $\gamma$-preimages, as $(I-Q)d_i = d_i$: $\gamma^Q_T(h) = (a\wedge b)\otimes((d+R(Q))\wedge(Tb+R(Q)))^*$.

*$\gamma^P_{QT}$ of it.* The last map of $E(QT,P)$ is $[y]\mapsto(I-P)y+R(Q)$. Since $Pd_i = PQd_i = 0$ and $PTb_j = PQTb_j = 0$, the classes $[d_i]$, $[Tb_j]$ are
$\gamma$-preimages of $d_i+R(Q)$, $Tb_j+R(Q)$; the $\beta$-images of the $\tilde b$ are $[QT\tilde b]$. So $\gamma^P_{QT}\gamma^Q_T(h) = (a\wedge b\wedge\tilde b)\otimes([d]\wedge[Tb]\wedge[QT\tilde b])^*$.

*$\gamma^P_T(h)$.* Extending $a$ by $b,\tilde b$ to $\ker(PT)$, the $\beta$-images are $[Tb]$, $[T\tilde b]$, and $[d_i]$ are $\gamma$-preimages, $(I-P)d_i = d_i-PQd_i = d_i$. So
$\gamma^P_T(h) = (a\wedge b\wedge\tilde b)\otimes([d]\wedge[Tb]\wedge[T\tilde b])^*$.

*Comparison.* $[T\tilde b]-[QT\tilde b] = [(I-Q)T\tilde b]$, and $(I-Q)T\tilde b\in\ker Q$. If $Qg = 0$, write $g+R(T) = \sum c_id_i+R(T)$, so $g-\sum c_id_i = Tx$ with $QTx = 0$, that is,
$x\in\ker(QT)$ and $Tx = \sum\beta_jTb_j$: $g$ is a combination of the $d_i$ and $Tb_j$. So the third blocks of the two wedges differ by vectors in the span of the first two
blocks, and the wedges agree. $\square$

The text obtains the spanning from the splitting $F/R(P) = \ker\tilde Q\oplus\ker(I-\tilde Q)$ of the induced projection $\tilde Q$; here it is proved directly in $F$
(Findings, item 6). The final wedge, named $\alpha_q$, is read as $\alpha^P$ (possible misprint) (Findings, item 7). *Checked by machine
(V6.64):* `Polyfold.mem_span_append_of_ker`, `Polyfold.gammaProj_wedge_tmul`, `Polyfold.comp_comp_eq_of_projLE`.

## 9. Application: the bead on the hoop as an sc-Fredholm problem

The computations below were done by hand and the numbers checked by a script (sympy and numpy); they are not checked in
Lean.

**The problem.** $X = S^1 = \mathbb R/2\pi\mathbb Z$, with the angle charts and the constant sc-structure $E_m = \mathbb R$: a finite-dimensional manifold is an
M-polyfold with the identity as retraction, tame since it has no boundary, with bump functions. $Y = S^1\times\mathbb R$ with its trivial
strong bundle structure, and $f(\theta) = (\theta,f_\mu(\theta))$. In finite dimensions every linear operator is sc$^+$ (the inclusions $E_{m+1}\to E_m$ are the
identity of $\mathbb R$, which is compact) and every smooth section is sc$^+$; $f$ is sc-Fredholm with tame germ data (the basic germs of
Chapter 3 have $W = 0$), and proper, since $S^1$ is compact (Theorem 5.2.2 (preprint 5.5)). The chart transitions are translations, so the
transfers of §6 are identities. Nothing infinite-dimensional is visible; what is visible is the signs.

**Determinant lines.** $\mathrm{Lin}(f,\theta) = \{f_\mu'(\theta)+a\} = L(\mathbb R,\mathbb R) = \mathbb R$ for every $\theta$, of index $0$, and $\mathrm{DET}(f,\theta)$ is the bundle of Example 6.B, with
the orientations $\pm o^+$.

**An orientation of $f$.** Along a path $\gamma$ take $S(t,y) = -f_\mu(\gamma(t))$, constant in $y$, so $T_t = f_\mu'(\gamma(t))$, and one section $s_1 = 1$, so $\varphi(\lambda) = \lambda$;
$F(\lambda,(t,y)) = f_\mu(y)-f_\mu(\gamma(t))+\lambda$ is in general position everywhere ($\partial_\lambda F = 1$). The stabilized kernels are $\Lambda_t = \mathrm{span}(1,-T_t)$, and by Example 6.E the
sign-normalized ray carried from $o^+$ is $[-(1,-T)]$ for every $T$; continuation along the frame $(1,-T_t)$ keeps it. So every push-forward
maps $o^+$ to $o^+$: $f$ is orientable, and $\theta\mapsto o^+$ is an orientation in the sense of Definition 6.6.16 (preprint 6.40), the other being $-o^+$.

**Tangent orientations.** At a zero with $a = f_\mu'(\theta)\ne0$, $\det(a)\cong\lambda(\ker a) = \lambda(0) = \mathbb R$ sends $h_a$ to $1$ (no added sections, and $\psi$ the identity of
$\lambda^*(\mathbb R^0)$), so $o^+(a) = [\operatorname{sign}(a)h_a]$ orients the point by $\operatorname{sign}f_\mu'(\theta)$ (Theorem 6.6.18 (preprint 6.41)). The count of the oriented $0$-manifold $S_f$ is
$\sum_{f_\mu(\theta) = 0}\operatorname{sign}f_\mu'(\theta)$. For $\mu = 1/2$ the zeros are $0$, $\pi$ with $f' = 1/2$, $-3/2$; for $\mu = 2$ they are $0$, $\pi$, $\pm\pi/3$ with $f' = -1$, $-3$, $3/2$, $3/2$. Both
counts are $0$. With $n = 0$, $\partial X = \emptyset$ and $\omega = 1\in H^0_{dR}(S^1)$, this count is $\Psi_{(f,o)}([1])$ of Theorem 6.7.1 (preprint 6.43), and (2) of that theorem predicts that
it does not change with $\mu$.

**The bifurcation.** The homotopy $F(\theta,\mu) = f_\mu(\theta)$, $\mu\in[1/2,2]$, is $f_{1/2}$ plus the sc$^+$-section $(\mu-1/2)(-\sin\theta\cos\theta)$ (Remark 6.6.19 (preprint 6.42)). At
$(\theta,\mu) = (0,1)$ both $\partial_\theta F = \cos\theta-\mu\cos2\theta$ and $\partial_\mu F = -\sin\theta\cos\theta$ vanish: the zero set there is the line $\theta = 0$ crossed by the curve
$\cos\theta = 1/\mu$ (a pitchfork), not a manifold, so the homotopy is not in general position. This is why §6.7 (preprint §6.6) perturbs (Remark
5.3.8 (preprint 5.16)). With $F_\varepsilon = F+\varepsilon\cos\theta$, $\varepsilon = 1/20$: $\partial_\mu F_\varepsilon = -\sin\theta\cos\theta$ vanishes only at $\theta\in\{0,\pi,\pm\pi/2\}$, where $F_\varepsilon = \varepsilon,-\varepsilon,\pm1\ne0$; so $dF_\varepsilon\ne0$ on the zero set,
which is a compact $1$-manifold over $S^1\times[1/2,2]$ with boundary the zero sets at the two ends. At $\mu = 1/2$ these are $-0.0992$,
$3.1083$, with signs $+,-$; at $\mu = 2$, $-1.0632$, $0.0501$, $1.0298$, $3.1249$, with signs $+,-,+,-$. Both counts are $0$. On the way the number
of zeros changes from $2$ to $4$ at a fold, where $\partial_\theta F_\varepsilon$ changes sign along the curve and a pair of zeros of opposite signs is born: the
perturbation has unfolded the pitchfork.

**The sign of (94), seen on the bead.** Along the constant path at a point $\theta_0$ with $a = f_\mu'(\theta_0)\ne0$, the datum
$S(t,y) = -f_\mu(\theta_0)-ta\sin(y-\theta_0)$, $s_1 = 1$ is a push-forward datum, with $T_t = (1-t)a$ and $T_1 = 0$. Without the sign, $o^+(a)$ is carried to $[-(1,-a)]$, continued
to $[-(1,0)]$, and $(1,0)\otimes1^* = \iota_\varphi(1\otimes1^*)$, so the result is $-o^+$; the datum $S(t,y) = -f_\mu(\theta_0)$ gives $o^+$. So, as we read it, the push-forward
without the sign would depend on the choice of the section, and Proposition 6.6.7 (preprint 6.32) would not hold for it; with the sign
the factor $\alpha(T_1) = -1$ restores $o^+$. This is the factor $\alpha(T_a)\alpha(T_b)$ of §5 (Findings, item 50).

## 10. Summary of what was silently assumed, now made explicit

| Where (preprint) | HWZ say | What is actually needed |
|---|---|---|
| pp. 237–240 (preprint pp. 200–201), Def. 6.2.1 (preprint 6.1) | $T_xX$, $Y_x$; a local section through $f(x)$ | a chart point; global sc$^+$-sections from bump functions |
| preprint p. 201 | "$(f-s)'(x)$ … iff $(f-s)'(x)$" | $(f-t)'(x)$ (possible misprint) |
| preprint p. 201 | M-polyfolds locally path connected; paths in path components | the local form in a chart; "joined by an sc-smooth path" |
| preprint p. 203 | sc-smooth partitions of unity | sc-smooth bump functions |
| p. 246 (preprint p. 207), Prop. 6.3.5 (preprint 6.6) | $c'_1\wedge\dots\wedge c'_l\wedge c_1\wedge\dots\wedge c_{m-n}$ | the order of (91) |
| p. 247 (preprint p. 208), Def. 6.4.3 (preprint 6.9) | — | $\Pi_T\ne\emptyset$ for $T$ Fredholm |
| preprint pp. 208–209, Lemma 6.10 (preprint; not in the 2021 edition) | $P''$ onto $R(P)\cap R(P')$ | $R(P)\cap R(P')\cap N$, along a complement containing $\ker P+\ker P'$ |
| p. 256 (preprint p. 212), Lemma 6.4.14 (preprint 6.14) | $j(e) = (0,e)$ | $(e,0)$ |
| p. 256 (preprint p. 212), (94) | $\Phi_{\mathcal E}$ with $\psi$ | $(-1)^{\dim\operatorname{coker}T}\Phi_{\mathcal E}$ along families |
| p. 257 (preprint p. 213), Prop. 6.4.15 (preprint 6.15) | "$\varphi$"; $m+l = n$ tacit | $\psi$; $m+l = n$ proved |
| p. 258 (preprint p. 214), Lemma 6.5.1 (preprint 6.17) | $T$ Fredholm | not used |
| p. 259 (preprint p. 216), Lemma 6.5.3 (preprint 6.19) | bundle constructions in general | explicit frames |
| pp. 260–261 (preprint pp. 216–217), Lemma 6.5.5 (preprint 6.21) | "trivial", a sketch | the sketch, for two charts |
| p. 263 (preprint p. 219), Prop. 6.6.1 (preprint 6.26) | "contractible" | the lifting criterion for the orientation double cover |
| p. 263 (preprint p. 220), Prop. 6.6.3 (1) (preprint 6.28) | $U = r(V')$ contracted by $r(ty)$ | $r(V')\subseteq V'$; (1′) proved instead |
| preprint p. 221 | "assuming $X = U$" | global sections over $\mathbb R^n\times X$ |
| p. 265 (preprint p. 222), Lemma 6.6.4 (preprint 6.29) | "using the results from the transversality theory" | the proof of Theorem 5.3.10 (preprint 5.18) |
| p. 266 (preprint p. 223), Lemma 6.6.6 (preprint 6.31) | $c$ onto by (P) | general position of $F$ and the derivative of the family of zeros |
| pp. 267–271 (preprint pp. 224–226), Lemmas 6.6.8, 6.6.10 (preprint 6.33, 6.34) | "a simple computation"; "varies continuously" | sections appended last; the sign of (94) |
| pp. 271–273 (preprint pp. 226–227), Thm. 6.6.11 (preprint 6.35) | $f$ not introduced; $U$ contractible | $f$ sc-Fredholm with tame germ data; (1′) and $\gamma_i\circ\kappa$ |
| p. 273 (preprint p. 227), Def. 6.6.12 (preprint 6.36) | an open contractible $U$ | a pair $V\subseteq U$ |
| preprint p. 228 | $\psi(\beta(s))$; homotopy classes form a category | $\psi(\beta(s)-1)$; transitivity after $\kappa$; constant paths as identities |
| p. 273 (preprint p. 228), Thm. 6.6.13 (preprint 6.37) | "a covering argument"; "obvious that $\Gamma_f$ is unique" | dyadic subdivisions; uniqueness from (∗) on a cover |
| p. 273 (preprint p. 228), Thm. 6.6.13 (preprint 6.37) | $\mathrm{Or}^f_x$ chart-free | a chosen chart and the transfer between charts |
| p. 274 (preprint p. 229), Defs. 6.6.14, 6.6.15 (preprint 6.38, 6.39) | "equivalent"; "$y\in U_\infty$" | a proof; $y\in X_\infty$ |
| p. 275 (preprint p. 229), Thm. 6.6.18 (preprint 6.41) | "a natural orientation" | tangent orientations, continuous along paths of zeros |
| p. 276 (preprint p. 230), Rem. 6.6.19 (preprint 6.42) | $h\mapsto\tilde h$ | the sign $(-1)^{\dim\operatorname{coker}L}$ |
| preprint p. 232, Thm. 6.7.1 (preprint 6.43) | $\bar\omega = p_1^*\omega\wedge p_2^*dt$ | $p_1^*\omega$ (possible misprint) |

## 11. The Springer 2021 edition (pp. 247, 253–255, 267–269, 274–275)

The 2021 edition sharpens two statements of §6.4 that the 2017 edition added (they have no preprint counterpart), splits
preprint Lemma 6.33 in two, and adds a topology on the orientation space $O_f$ (Theorem 6.6.17).

**Lemma 6.4.4** *(book 2017: Lemma 6.3, p. 189).* For $T_0$ Fredholm and $P_0\in\Pi_{T_0}$ there is $\varepsilon>0$ such that every $T$ and every
projection $P$ with $\|T-T_0\|<\varepsilon$, $\|P-P_0\|<\varepsilon$ have: $T$ Fredholm, $P\in\Pi_T$, and — new in 2021 —
$$\operatorname{ind}(P\circ T) = \operatorname{ind}(T) = \operatorname{ind}(T_0) = \operatorname{ind}(P_0\circ T_0),$$
the indices of $P\circ T$ and $P_0\circ T_0$ taken as maps $E\to F$ (onto $R(P)$ the index would be $\dim\ker(PT)$). The proof formalized is
not the text's. The *intertwiner*
$$J(P) = PP_0+(1-P)(1-P_0)$$
is continuous in $P$, equals $1$ at $P_0$, and satisfies $J(P)P_0 = PJ(P)$; so for $P$ near $P_0$ it is invertible and $P = JP_0J^{-1}$.
Then $R(P) = JR(P_0)$, and Lemma 6.5.1 (preprint 6.17) for $J^{-1}T$, which is near $T_0$, gives $R(PT) = JR(P_0J^{-1}T) = JR(P_0) = R(P)$. The
index equalities come from the openness of the Fredholm operators of a given index and §3.

*Checked by machine:* `Polyfold.projIntertwiner`, `Polyfold.projIntertwiner_mul`, `Polyfold.lemma_6_4_4_2021`.

**Proposition 6.4.13** *(book 2017: Proposition 6.6, p. 195).* Let $T$ be Fredholm and $P,Q\in\Pi_T$ with $R(P) = R(Q) = H$ (the 2021 text
makes the existence of such projections a hypothesis). The text's maps
$$A_T(e) = e-x(e),\qquad B_T(f+H) = \tilde f+H,$$
with $x(e)\in X$ solving $QTx = QTe$ and $(1-P)f = Tx+\tilde f$, $x\in X$, $\tilde f\in(1-Q)F$, are isomorphisms $\ker(PT)\to\ker(QT)$ and $F/H\to F/H$
that make the diagram of the exact sequences $E(T,P)$ and $E(T,Q)$ of §3 commute. Here $X$ is a common complement of $\ker(PT)$
and $\ker(QT)$, which have the same dimension because $PT$ and $QT$ have the index of $T$ and the same range $H$. Such an $X$ exists
algebraically: if neither space contains the other, pick $a\in K_2\setminus K_1$ and $b\in K_1\setminus K_2$; then $a+b$ lies in neither, and induction
on $\dim(K_1+K_2)-\dim K_1$ applies to $K_i+\mathbb R(a+b)$. The text takes $X$ closed; with a closed $X$ its last sentence, that $A_T$ and $B_T$
depend continuously on $T$, is formalized too (next paragraph; gap G.81, closed).

*Checked by machine:* `Polyfold.exists_isCompl_isCompl_of_finrank_eq`, `Polyfold.proposition_6_4_13_2021`.

**Proposition 6.4.13, the last sentence.** A closed common complement exists: with the algebraic $X_0$ above and a closed
complement $Z$ of the finite-dimensional $K_1+K_2$,
$$X = Z+X_0\cap(K_1+K_2)$$
is closed and complements $K_1$ and $K_2$ topologically. Fix it for $\ker(PT)$, $\ker(QT)$. For $S$ near $T$, $QS|_X : X\to R(Q)$ stays an
isomorphism (Lemma 6.5.1 (preprint 6.17)), and the text's solution $x(e)$ of (6.15) becomes the operator
$$\xi_S = (QS|_X)^{-1}\circ Q,\qquad A_S = 1-\xi_S\circ S,\qquad B_S = (1-P)-S\,\xi_S(1-P),$$
the second on all of $E$, the third lifting $B_S$ to $F$. Inversion being continuous at isomorphisms, $\xi_S$, $A_S$ and $B_S$ are continuous in
$S$ in the operator norm, and jointly with the vector; for every such $S$, $P,Q\in\Pi_S$, $X$ complements $\ker(PS)$ and $\ker(QS)$
topologically, and $A_S$, $B_S$ induce the text's isomorphisms $\ker(PS)\to\ker(QS)$ and $F/H\to F/H$ filling the diagram. We read "depend
continuously" as this continuity of the extensions to $E$ and $F$; the joint continuity is continuity on the kernel bundle
$\bigcup_S\{S\}\times\ker(PS)$ of Remark 6.4.5 (Findings, items 116, 117).

*Checked by machine:* `Polyfold.exists_isClosed_isTopCompl_isTopCompl_of_finrank_eq`, `Polyfold.solveOp`, `Polyfold.kerTransition`,
`Polyfold.cokerTransition`, `Polyfold.continuousAt_solveOp`, `Polyfold.diagram_of_solveOp`, `Polyfold.proposition_6_4_13_continuity_2021`.

**Lemma 6.6.9** *(new in the 2021 edition as a separate lemma; preprint Lemma 6.33, 2017: Lemma 6.15).* Adding sc$^+$-sections
$\sum\mu_j\bar s_j(y,t)$ to a section with property (P) does not change the propagation of orientation. It is the statement of preprint
Lemma 6.33, which §5 calls Lemma 6.6.8. The 2021 Lemma 6.6.8 is the first step of the earlier proof: new parameters $\mu$ that
enter as dummy variables change nothing. Both are §5's identity of push-forwards, Lemma 6.6.8 for $\bar s_j = 0$.

*Checked by machine:* `Polyfold.lemma_6_6_8_2021`, `Polyfold.lemma_6_6_9_2021`.

**Theorem 6.6.17** *(new in the 2021 edition, p. 275).* The orientation space
$$O_f = \{(x,o) : x\in X_\infty,\ o \text{ an orientation of } \mathrm{DET}(f,x)\},\qquad \pi_f(x,o) = x,$$
two points over each $x$, appears in the earlier texts as a set; the 2021 text gives it a topology. With $X_\infty$ in the topology of
Theorem 2.3.10, the theorem asks for the unique Hausdorff topology with (1) $\pi_f$ a local homeomorphism, (2) every $x\in X_\infty$ having an
open $U$ in $X$ over whose smooth part there are exactly two continuous sections, and (3) a continuous section $t\mapsto(\varphi(t),o_t)$ along an
sc-smooth path having $o_t$ equal, for $t$ near $t_0$, to the local propagation of $o_{t_0}$. The proof is left to the reader.

The formalization reads Or$^f_x$ in the chosen chart (§6), paths as sc-smooth maps $\mathbb R\to X$ on $[0,1]$, and "the local propagation" as
the push-forward along the segment of $\varphi$ from $t_0$ to $t$ inside a set with the local propagation property. It calls a family
$y\mapsto o_y$ over an open $U$ a *continuous orientation* if the transport of $\Gamma_f$ carries it along every sc-smooth path in $U$, and
declares $W\subseteq O_f$ open when $\{y\in U_\infty : (y,o_y)\in W\}$ is open for every continuous orientation. The sheets $\{(y,o_y)\}$ are then
open, $\pi_f$ maps each homeomorphically onto $U_\infty$, two sheets through the two points over $x$ are disjoint near $x$, and (1), (3)
and Hausdorffness follow. Uniqueness is stronger than stated: any topology with (1) and (3) is this one, since a continuous local
section agreeing with a sheet at a point agrees with it along every short sc-smooth path from that point (an sc-smooth map
$\mathbb R^n\to X$ is continuous into $X_\infty$, and nearby smooth points are joined by such paths staying close in $X_\infty$).

Property (2) needs more. A continuous section over $U_\infty$ is locally one of the two sheets, so it is $y\mapsto(y,\pm o_y)$ when $U_\infty$ is
connected. The formalization assumes that every smooth point has arbitrarily small open neighbourhoods $U$ with $U_\infty$
connected in $X_\infty$, which holds for $\mathbb R^n$; Part I does not state it (gap G.90). §7.4 uses that $U_\infty$ is connected
for connected open $U$ (gap G.85), which, as we read it, gives the hypothesis, $X$ being locally path connected (Proposition 2.3.7). Existence and uniqueness of a Hausdorff topology with (1) and (3) need no
extra hypothesis. The hypotheses on $X$ and $f$ are those under which $\Gamma_f$ is built (§6). The remarks after the theorem — $\pi_f$ as the
orientation bundle, orientability as a global continuous section, the $\mathbb Z_2$-action and $\det_f$ — are not formalized (gap G.91)
(Findings, items 118–121).

*Checked by machine:* `Polyfold.OrSpace`, `Polyfold.IsOrientationTopology`, `Polyfold.orTopology`, `Polyfold.isLocalHomeomorph_orProj`,
`Polyfold.t2Space_orTopology`, `Polyfold.isPropagationContinuous_orTopology`, `Polyfold.eq_orTopology_of`,
`Polyfold.hasTwoContSections_orTopology`, `Polyfold.MPolyfold.HasConnectedSmoothNbhds`,
`Polyfold.existsUnique_orientationTopology_2021`, `Polyfold.theorem_6_6_17_2021`.

*Other 2021 changes.* Proposition 6.4.15 (preprint 6.15) now states its hypotheses $T$ Fredholm and $T\oplus\varphi$ onto, which §3 already
uses; Proposition 6.6.3 (preprint 6.28) assumes $X$ tame and lets the sections take values in $Y\times[0,1]$, while §5 proves it without
tameness, on the pull-back over $\mathbb R^n\times X$; Lemma 6.6.5 (preprint 6.30) now describes the solution set near $(t,\varphi(t),0)$ in the
points $(t,y,\lambda)$, where the earlier texts write $(t,y,0)$ (possible misprint), and its kernel family in §5 is unaffected.

The findings are `Exposition/Findings.md`, "Chapter 6", items 110–121.

---

**Checked by machine.** The chapter is formalized in Lean 4 against Mathlib in `Polyfold/Chapter6/` (`DetLine.lean`,
`ExactSequence.lean`, `FredholmDet.lean`, `GoodProjections.lean`, `ProjectionSequence.lean`, `Stabilization.lean`,
`DirectSumDet.lean`, `LineBundleOrientation.lean`, `LocalDetBundle.lean`, `DetBundle.lean`, `SubspaceBundle.lean`,
`LinSet.lean`, `Continuation.lean`, `LinOrientation.lean`, `StabilizationContinuity.lean`, `OrientableNbhd.lean`,
`KernelFamily.lean`, `Lemma629.lean`, `ParamKernel.lean`, `AddSections.lean`, `FamilySections.lean`, `Propagation.lean`,
`StabKernelsExist.lean`, `ScPaths.lean`, `PushData.lean`, `PropagationWellDefined.lean`, `ContinuousOrientation.lean`,
`ChartTransfer.lean`, `ScHomotopy.lean`, `PathCategory.lean`, `PathTransport.lean`, `SectionOrientation.lean`,
`PushTransfer.lean`, `OrientationFunctor.lean`, `ProductOrientation.lean`, `SolutionOrientation.lean`); Proposition 6.2.2 (preprint 6.2) is
Chapter 3's (V3.98); the paragraphs "*Checked by machine*" name the declarations. Formalized: every definition of the
chapter (Definitions 6.2.1, 6.3.1, 6.4.1–6.4.3, 6.4.16, 6.5.6, 6.6.2, 6.6.12, 6.6.14–6.6.16 (preprint 6.1, 6.3, 6.7–6.9, 6.16, 6.22, 6.27, 6.36, 6.38–6.40)); Propositions 6.3.2, 6.3.5, 6.4.11, 6.4.15, 6.5.4, 6.5.7,
6.5.8, 6.6.1, 6.6.7 (preprint 6.4, 6.6, 6.12, 6.15, 6.20, 6.23,
6.24, 6.26, 6.32); Lemma 6.3.3, Proposition 6.4.10, Lemma 6.4.14, Lemma 6.5.1, Lemma 6.5.2, Lemma 6.5.5, Lemma 6.5.9, Lemma 6.6.6, Lemma 6.6.8, Lemma 6.6.10 (preprint Lemmas 6.5, 6.11, 6.14, 6.17, 6.18, 6.21, 6.25, 6.31, 6.33, 6.34) and Lemma 6.10 (preprint); Corollary 6.4.12 (preprint 6.13); Theorems 6.6.11 and
6.6.13 (preprint 6.35 and
6.37); the equivalence of Definitions 6.6.14 and 6.6.15 (preprint 6.38 and 6.39); Lemmas 6.A, 6.C, 6.D and Proposition 6.F; Appendix 6.8 (preprint 6.7). **Theorems 6.6.11 and
6.6.13 (preprint 6.35 and
6.37) hold** with the readings above. In a changed form: Lemma 6.10 (preprint) by another construction, for any bounded $T$;
Proposition 6.6.3 (preprint 6.28) with (1′) in place of (1), and orientable neighbourhoods as pairs $V\subseteq U$; formula (94) and Remark 6.6.19 (preprint 6.42)
with the sign $(-1)^{\dim\operatorname{coker}T}$ along families; Lemma 6.6.4 (preprint 6.29) in the form used afterwards; Lemma 6.6.5 (preprint 6.30) as a continuous family of kernels;
Lemma 6.5.3 (preprint 6.19) for trivial bundles only; Theorem 6.6.18 (preprint 6.41) as tangent orientations continuous along the paths of zeros in a
chart; Remark 6.6.19 (preprint 6.42) at a point; $T_xX$, $Y_x$, $\mathrm{Lin}(f,x)$, $\mathrm{Or}^f_x$ in chart points, with the transfer between charts. Not
formalized: Proposition 6.6.3 (1) (preprint 6.28) (gap G.61); the facts on paths of preprint p. 201 (G.56); the members of $\mathrm{Lin}(f,x)$ as sc-Fredholm on
every level (G.64); the alternative determinant (G.57); (95) and the maps after Proposition 6.4.15 (preprint 6.15) (G.58); Lemma 6.5.3 (preprint 6.19) in
general (G.59); the non-orientability of $\mathrm{DET}(E,F)$ and the classical case (G.60); Lemma 6.6.5 (preprint 6.30) as a statement about manifolds
(G.62); property (P) (G.63); paths sc-smooth on $[0,1]$ only (G.65); Remark 6.6.19 (preprint 6.42) beyond a point (G.66); the orientation of $S$ as
an abstract manifold and its chart independence (G.67, G.68); the paragraph after Theorem 6.6.18 (preprint 6.41) (G.69); §6.7 (preprint §6.6) (G.55) and
Theorem 6.7.1 (preprint 6.43) (G.54, decision D1); the example of §9 and the remark on $\bar\omega$ in §7, checked by hand and by a script. The
machine-checked statements are listed in `Exposition/Verification.md` (V6.1–V6.64), compared with the text in
`Exposition/polyfold-beside-lean.html` and retold in `Exposition/ProofByProof.md` (Part VI). The findings are
`Exposition/Findings.md`, "Chapter 6", items 1–102.
